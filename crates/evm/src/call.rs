//! Utilities for dealing with eth_call and adjacent RPC endpoints.

use crate::{Evm, EvmError, InvalidTxError, TransactionEnvMut};
use alloy_primitives::U256;
use revm::{
    context_interface::{
        cfg::gas::CALL_STIPEND,
        result::{HaltReasonTr, ResultAndState},
    },
    Database,
};

/// Default acceptable relative error for gas estimation.
///
/// This matches Geth's gas estimator and allows the search to terminate once the remaining range
/// is less than 1.5% of the current upper bound.
pub const ESTIMATE_GAS_ERROR_RATIO: f64 = 0.015;

/// Insufficient funds error
#[derive(Debug, thiserror::Error)]
#[error("insufficient funds: cost {cost} > balance {balance}")]
pub struct InsufficientFundsError {
    /// Transaction cost
    pub cost: U256,
    /// Account balance
    pub balance: U256,
}

/// Error type for call utilities
#[derive(Debug, thiserror::Error)]
pub enum CallError<E> {
    /// Database error
    #[error(transparent)]
    Database(E),
    /// Insufficient funds error
    #[error(transparent)]
    InsufficientFunds(#[from] InsufficientFundsError),
}

/// Calculates the caller gas allowance.
///
/// `allowance = (account.balance - tx.value) / tx.gas_price`
///
/// Returns an error if the caller has insufficient funds.
/// Caution: This assumes non-zero `env.gas_price`. Otherwise, zero allowance will be returned.
///
/// Note: this takes the mut [Database] trait because the loaded sender can be reused for the
/// following operation like `eth_call`.
pub fn caller_gas_allowance<DB, T>(db: &mut DB, env: &T) -> Result<u64, CallError<DB::Error>>
where
    DB: Database,
    T: revm::context_interface::Transaction,
{
    // Get the caller account.
    let caller = db.basic(env.caller()).map_err(CallError::Database)?;
    // Get the caller balance.
    let balance = caller.map(|acc| acc.balance).unwrap_or_default();
    // Get transaction value.
    let value = env.value();
    // Subtract transferred value from the caller balance. Return error if the caller has
    // insufficient funds.
    let balance =
        balance.checked_sub(env.value()).ok_or(InsufficientFundsError { cost: value, balance })?;

    Ok(balance
        // Calculate the amount of gas the caller can afford with the specified gas price.
        .checked_div(U256::from(env.gas_price()))
        // This will be 0 if gas price is 0. It is fine, because we check it before.
        .unwrap_or_default()
        .saturating_to())
}

/// Estimates the lowest gas limit required for a transaction to succeed.
///
/// The transaction must have already succeeded with its configured gas limit. `gas_used` and
/// `gas_refunded` must come from that successful execution. This performs the Geth-style
/// optimistic probe followed by a binary search using [`ESTIMATE_GAS_ERROR_RATIO`].
///
/// Execution state returned by estimation probes is discarded.
pub fn estimate_gas_limit<E>(
    evm: &mut E,
    tx: E::Tx,
    gas_used: u64,
    gas_refunded: u64,
) -> Result<u64, E::Error>
where
    E: Evm,
    E::Tx: TransactionEnvMut,
{
    estimate_gas_limit_with(tx, gas_used, gas_refunded, ESTIMATE_GAS_ERROR_RATIO, |tx| {
        evm.transact(tx)
    })
}

/// Estimates the lowest gas limit required for a transaction to succeed using `transact`.
///
/// The transaction must have already succeeded with its configured gas limit. `gas_used` and
/// `gas_refunded` must come from that successful execution. An `error_ratio` of zero searches for
/// the exact minimum; otherwise the search terminates once the remaining range relative to the
/// upper bound is below `error_ratio`.
///
/// Each call to `transact` must execute against equivalent initial state and must not commit its
/// returned state. Once the transaction has succeeded at the initial upper bound, any revert or
/// halt from a lower probe is treated as evidence that the probe supplied too little gas. Invalid
/// transaction errors caused by the candidate gas limit update the search range; all other EVM
/// errors are returned unchanged.
pub fn estimate_gas_limit_with<T, H, E>(
    tx: T,
    mut gas_used: u64,
    gas_refunded: u64,
    error_ratio: f64,
    mut transact: impl FnMut(T) -> Result<ResultAndState<H>, E>,
) -> Result<u64, E>
where
    T: TransactionEnvMut,
    H: HaltReasonTr,
    E: EvmError,
{
    let mut highest_gas_limit = tx.gas_limit();
    let mut lowest_gas_limit = gas_used.saturating_sub(1);

    // Transactions commonly succeed with their used gas plus the refund. Account for EIP-150's
    // 63/64 forwarding rule and the call stipend before falling back to binary search.
    let optimistic_gas_limit =
        ((u128::from(gas_used) + u128::from(gas_refunded) + u128::from(CALL_STIPEND)) * 64 / 63)
            .min(u128::from(u64::MAX)) as u64;

    if optimistic_gas_limit < highest_gas_limit {
        if let Some(optimistic_gas_used) = update_estimated_gas_range(
            transact(tx.clone().with_gas_limit(optimistic_gas_limit)),
            optimistic_gas_limit,
            &mut highest_gas_limit,
            &mut lowest_gas_limit,
        )? {
            gas_used = optimistic_gas_used;
        }
    }

    let mut mid_gas_limit =
        gas_used.saturating_mul(3).min(midpoint(highest_gas_limit, lowest_gas_limit));

    while lowest_gas_limit.saturating_add(1) < highest_gas_limit {
        let ratio = (highest_gas_limit - lowest_gas_limit) as f64 / highest_gas_limit as f64;
        if ratio < error_ratio {
            break;
        }

        update_estimated_gas_range(
            transact(tx.clone().with_gas_limit(mid_gas_limit)),
            mid_gas_limit,
            &mut highest_gas_limit,
            &mut lowest_gas_limit,
        )?;

        mid_gas_limit = midpoint(highest_gas_limit, lowest_gas_limit);
    }

    Ok(highest_gas_limit)
}

fn update_estimated_gas_range<H, E>(
    result: Result<ResultAndState<H>, E>,
    gas_limit: u64,
    highest_gas_limit: &mut u64,
    lowest_gas_limit: &mut u64,
) -> Result<Option<u64>, E>
where
    H: HaltReasonTr,
    E: EvmError,
{
    match result {
        Ok(result) => {
            let gas_used = result.result.tx_gas_used();
            if result.result.is_success() {
                *highest_gas_limit = gas_limit;
            } else {
                *lowest_gas_limit = gas_limit;
            }
            Ok(Some(gas_used))
        }
        Err(err) => {
            if err.as_invalid_tx_err().is_some_and(InvalidTxError::is_gas_limit_too_high) {
                *highest_gas_limit = gas_limit;
                Ok(None)
            } else if err.as_invalid_tx_err().is_some_and(InvalidTxError::is_gas_limit_too_low) {
                *lowest_gas_limit = gas_limit;
                Ok(None)
            } else {
                Err(err)
            }
        }
    }
}

const fn midpoint(highest: u64, lowest: u64) -> u64 {
    ((highest as u128 + lowest as u128) / 2) as u64
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::Bytes;
    use core::convert::Infallible;
    use revm::{
        context::{result::ExecutionResult, Transaction, TxEnv},
        context_interface::result::{EVMError, HaltReason, InvalidTransaction, Output, ResultGas},
        state::EvmState,
    };

    type TestError = EVMError<Infallible, InvalidTransaction>;

    fn success(gas_used: u64) -> ResultAndState<HaltReason> {
        ResultAndState::new(
            ExecutionResult::Success {
                reason: revm::context_interface::result::SuccessReason::Stop,
                gas: ResultGas::new_with_state_gas(gas_used, 0, 0, 0),
                logs: Vec::new(),
                output: Output::Call(Bytes::new()),
            },
            EvmState::default(),
        )
    }

    fn revert(gas_used: u64) -> ResultAndState<HaltReason> {
        ResultAndState::new(
            ExecutionResult::Revert {
                gas: ResultGas::new_with_state_gas(gas_used, 0, 0, 0),
                logs: Vec::new(),
                output: Bytes::new(),
            },
            EvmState::default(),
        )
    }

    #[test]
    fn estimates_exact_gas_limit() {
        const REQUIRED_GAS: u64 = 75_000;
        let tx = TxEnv::default().with_gas_limit(1_000_000);

        let estimate = estimate_gas_limit_with(tx, 50_000, 0, 0.0, |tx| {
            Ok::<_, TestError>(if tx.gas_limit() >= REQUIRED_GAS {
                success(50_000)
            } else {
                revert(tx.gas_limit())
            })
        })
        .unwrap();

        assert_eq!(estimate, REQUIRED_GAS);
    }

    #[test]
    fn estimates_with_default_error_ratio() {
        const REQUIRED_GAS: u64 = 75_000;
        let tx = TxEnv::default().with_gas_limit(1_000_000);

        let estimate = estimate_gas_limit_with(tx, 50_000, 0, ESTIMATE_GAS_ERROR_RATIO, |tx| {
            Ok::<_, TestError>(if tx.gas_limit() >= REQUIRED_GAS {
                success(50_000)
            } else {
                revert(tx.gas_limit())
            })
        })
        .unwrap();

        assert!(estimate >= REQUIRED_GAS);
        assert!((estimate - REQUIRED_GAS) as f64 / (estimate as f64) < ESTIMATE_GAS_ERROR_RATIO);
    }

    #[test]
    fn handles_intrinsic_gas_errors() {
        const REQUIRED_GAS: u64 = 75_000;
        let tx = TxEnv::default().with_gas_limit(1_000_000);

        let estimate = estimate_gas_limit_with(tx, 50_000, 0, 0.0, |tx| {
            let gas_limit = tx.gas_limit();
            if gas_limit >= REQUIRED_GAS {
                Ok(success(50_000))
            } else {
                Err(TestError::Transaction(InvalidTransaction::CallGasCostMoreThanGasLimit {
                    initial_gas: REQUIRED_GAS,
                    gas_limit,
                }))
            }
        })
        .unwrap();

        assert_eq!(estimate, REQUIRED_GAS);
    }

    #[test]
    fn propagates_unrelated_evm_errors() {
        let tx = TxEnv::default().with_gas_limit(1_000_000);
        let err = estimate_gas_limit_with(tx, 50_000, 0, 0.0, |_| {
            Err::<ResultAndState<HaltReason>, _>(TestError::Transaction(
                InvalidTransaction::InvalidChainId,
            ))
        })
        .unwrap_err();

        assert!(matches!(err, TestError::Transaction(InvalidTransaction::InvalidChainId)));
    }
}
