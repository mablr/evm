use crate::rpc::{CallFees, CallFeesError};
use alloy_consensus::{error::ValueError, transaction::Recovered, EthereumTxEnvelope, TxEip4844};
use alloy_primitives::{Address, TxKind, U256};
use alloy_rpc_types_eth::{
    request::{TransactionInputError, TransactionRequest},
    Transaction, TransactionInfo,
};
use core::{convert::Infallible, error, error::Error, fmt::Debug};
use revm::{
    context::{BlockEnv, CfgEnv, TxEnv},
    context_interface::{either::Either, Block},
};
use thiserror::Error;

/// Converts `self` into `T`. The opposite of [`FromConsensusTx`].
///
/// Should create an RPC transaction response object based on a consensus transaction, its signer
/// [`Address`] and an additional context [`IntoRpcTx::TxInfo`].
///
/// Avoid implementing [`IntoRpcTx`] and use [`FromConsensusTx`] instead. Implementing it
/// automatically provides an implementation of [`IntoRpcTx`] thanks to the blanket implementation
/// in this crate.
///
/// Prefer using [`IntoRpcTx`] over [`FromConsensusTx`] when specifying trait bounds on a generic
/// function to ensure that types that only implement [`IntoRpcTx`] can be used as well.
pub trait IntoRpcTx<T> {
    /// An additional context, usually [`TransactionInfo`] in a wrapper that carries some
    /// implementation specific extra information.
    type TxInfo;
    /// An associated RPC conversion error.
    type Err: error::Error;

    /// Performs the conversion consuming `self` with `signer` and `tx_info`. See [`IntoRpcTx`]
    /// for details.
    fn into_rpc_tx(self, signer: Address, tx_info: Self::TxInfo) -> Result<T, Self::Err>;
}

impl<ConsensusTx, RpcTx> IntoRpcTx<RpcTx> for ConsensusTx
where
    ConsensusTx: alloy_consensus::Transaction,
    RpcTx: FromConsensusTx<Self>,
    <RpcTx as FromConsensusTx<ConsensusTx>>::Err: Debug,
{
    type TxInfo = RpcTx::TxInfo;
    type Err = <RpcTx as FromConsensusTx<ConsensusTx>>::Err;

    fn into_rpc_tx(self, signer: Address, tx_info: Self::TxInfo) -> Result<RpcTx, Self::Err> {
        RpcTx::from_consensus_tx(self, signer, tx_info)
    }
}

/// Converts `T` into `self`. It is reciprocal of [`IntoRpcTx`].
///
/// Should create an RPC transaction response object based on a consensus transaction, its signer
/// [`Address`] and an additional context [`FromConsensusTx::TxInfo`].
///
/// Prefer implementing [`FromConsensusTx`] over [`IntoRpcTx`] because it automatically provides an
/// implementation of [`IntoRpcTx`] thanks to the blanket implementation in this crate.
///
/// Prefer using [`IntoRpcTx`] over using [`FromConsensusTx`] when specifying trait bounds on a
/// generic function. This way, types that directly implement [`IntoRpcTx`] can be used as arguments
/// as well.
pub trait FromConsensusTx<T>: Sized {
    /// An additional context, usually [`TransactionInfo`] in a wrapper that carries some
    /// implementation specific extra information.
    type TxInfo;
    /// An associated RPC conversion error.
    type Err: error::Error;

    /// Performs the conversion consuming `tx` with `signer` and `tx_info`. See [`FromConsensusTx`]
    /// for details.
    fn from_consensus_tx(tx: T, signer: Address, tx_info: Self::TxInfo) -> Result<Self, Self::Err>;
}

impl<TxIn: alloy_consensus::Transaction, T: alloy_consensus::Transaction + From<TxIn>>
    FromConsensusTx<TxIn> for Transaction<T>
{
    type TxInfo = TransactionInfo;
    type Err = Infallible;

    fn from_consensus_tx(
        tx: TxIn,
        signer: Address,
        tx_info: Self::TxInfo,
    ) -> Result<Self, Self::Err> {
        Ok(Self::from_transaction(Recovered::new_unchecked(tx.into(), signer), tx_info))
    }
}

/// Converts `Tx` into `RpcTx`
///
/// Where:
/// * `Tx` is a transaction from the consensus layer.
/// * `RpcTx` is a transaction response object of the RPC API
///
/// The conversion function is accompanied by `signer`'s address and `tx_info` providing extra
/// context about a transaction in a block.
///
/// The `RpcTxConverter` has two blanket implementations:
/// * `()` assuming `Tx` implements [`IntoRpcTx`].
/// * `Fn(Tx, Address, TxInfo) -> RpcTx` for custom conversion functions.
///
/// One should prefer to implement [`IntoRpcTx`] for `Tx` to get the `RpcTxConverter` implementation
/// for free, thanks to the blanket implementation, unless the conversion requires more context. For
/// example, some configuration parameters or access handles to database, network, etc.
pub trait RpcTxConverter<Tx, RpcTx, TxInfo>: Clone + Debug + Unpin + Send + Sync + 'static {
    /// An associated error that can happen during the conversion.
    type Err;

    /// Performs the conversion of `tx` from `Tx` into `RpcTx`.
    ///
    /// See [`RpcTxConverter`] for more information.
    fn convert_rpc_tx(&self, tx: Tx, signer: Address, tx_info: TxInfo) -> Result<RpcTx, Self::Err>;
}

impl<Tx, RpcTx> RpcTxConverter<Tx, RpcTx, Tx::TxInfo> for ()
where
    Tx: IntoRpcTx<RpcTx>,
{
    type Err = Tx::Err;

    fn convert_rpc_tx(
        &self,
        tx: Tx,
        signer: Address,
        tx_info: Tx::TxInfo,
    ) -> Result<RpcTx, Self::Err> {
        tx.into_rpc_tx(signer, tx_info)
    }
}

impl<Tx, RpcTx, F, TxInfo, E> RpcTxConverter<Tx, RpcTx, TxInfo> for F
where
    F: Fn(Tx, Address, TxInfo) -> Result<RpcTx, E> + Clone + Debug + Unpin + Send + Sync + 'static,
{
    type Err = E;

    fn convert_rpc_tx(&self, tx: Tx, signer: Address, tx_info: TxInfo) -> Result<RpcTx, Self::Err> {
        self(tx, signer, tx_info)
    }
}

/// Converts `TxReq` into `SimTx`.
///
/// Where:
/// * `TxReq` is a transaction request received from an RPC API
/// * `SimTx` is the corresponding consensus layer transaction for execution simulation
///
/// The `SimTxConverter` has two blanket implementations:
/// * `()` assuming `TxReq` implements [`TryIntoSimTx`].
/// * `Fn(TxReq) -> Result<SimTx, E>` for custom conversion functions.
///
/// One should prefer to implement [`TryIntoSimTx`] for `TxReq` to get the `SimTxConverter`
/// implementation for free, thanks to the blanket implementation, unless the conversion requires
/// more context. For example, some configuration parameters or access handles to database, network,
/// etc.
pub trait SimTxConverter<TxReq, SimTx>: Clone + Debug + Unpin + Send + Sync + 'static {
    /// An associated error that can occur during the conversion.
    type Err: Error;

    /// Performs the conversion from `tx_req` into `SimTx`.
    ///
    /// See [`SimTxConverter`] for more information.
    fn convert_sim_tx(&self, tx_req: TxReq) -> Result<SimTx, Self::Err>;
}

impl<TxReq, SimTx> SimTxConverter<TxReq, SimTx> for ()
where
    TxReq: TryIntoSimTx<SimTx> + Debug,
{
    type Err = ValueError<TxReq>;

    fn convert_sim_tx(&self, tx_req: TxReq) -> Result<SimTx, Self::Err> {
        tx_req.try_into_sim_tx()
    }
}

impl<TxReq, SimTx, F, E> SimTxConverter<TxReq, SimTx> for F
where
    TxReq: Debug,
    E: Error,
    F: Fn(TxReq) -> Result<SimTx, E> + Clone + Debug + Unpin + Send + Sync + 'static,
{
    type Err = E;

    fn convert_sim_tx(&self, tx_req: TxReq) -> Result<SimTx, Self::Err> {
        self(tx_req)
    }
}

/// Converts `self` into `T`.
///
/// Should create a fake transaction for simulation using [`TransactionRequest`].
pub trait TryIntoSimTx<T>
where
    Self: Sized,
{
    /// Performs the conversion.
    ///
    /// Should return a signed typed transaction envelope for the [`eth_simulateV1`] endpoint with a
    /// dummy signature or an error if [required fields] are missing.
    ///
    /// [`eth_simulateV1`]: <https://github.com/ethereum/execution-apis/pull/484>
    /// [required fields]: TransactionRequest::buildable_type
    fn try_into_sim_tx(self) -> Result<T, ValueError<Self>>;
}

/// Adds extra context to [`TransactionInfo`].
pub trait TxInfoMapper<T> {
    /// An associated output type that carries [`TransactionInfo`] with some extra context.
    type Out;
    /// An associated error that can occur during the mapping.
    type Err;

    /// Performs the conversion.
    fn try_map(&self, tx: &T, tx_info: TransactionInfo) -> Result<Self::Out, Self::Err>;
}

impl<T> TxInfoMapper<T> for () {
    type Out = TransactionInfo;
    type Err = Infallible;

    fn try_map(&self, _tx: &T, tx_info: TransactionInfo) -> Result<Self::Out, Self::Err> {
        Ok(tx_info)
    }
}

impl TryIntoSimTx<EthereumTxEnvelope<TxEip4844>> for TransactionRequest {
    fn try_into_sim_tx(self) -> Result<EthereumTxEnvelope<TxEip4844>, ValueError<Self>> {
        Self::build_typed_simulate_transaction(self)
    }
}

/// Converts `self` into `T`.
///
/// Should create an executable transaction environment using [`TransactionRequest`].
pub trait TryIntoTxEnv<T, BlockEnv = revm::context::BlockEnv> {
    /// An associated error that can occur during the conversion.
    type Err;

    /// Performs the conversion.
    fn try_into_tx_env<Spec>(
        self,
        cfg_env: &CfgEnv<Spec>,
        block_env: &BlockEnv,
    ) -> Result<T, Self::Err>;
}

/// An Ethereum specific transaction environment error than can occur during conversion from
/// [`TransactionRequest`].
#[derive(Debug, Error)]
pub enum EthTxEnvError {
    /// Error while decoding or validating transaction request fees.
    #[error(transparent)]
    CallFees(#[from] CallFeesError),
    /// Both data and input fields are set and not equal.
    #[error(transparent)]
    Input(#[from] TransactionInputError),
}

impl TryIntoTxEnv<TxEnv> for TransactionRequest {
    type Err = EthTxEnvError;

    fn try_into_tx_env<Spec>(
        self,
        cfg_env: &CfgEnv<Spec>,
        block_env: &BlockEnv,
    ) -> Result<TxEnv, Self::Err> {
        // Ensure that if versioned hashes are set, they're not empty
        if self.blob_versioned_hashes.as_ref().is_some_and(|hashes| hashes.is_empty()) {
            return Err(CallFeesError::BlobTransactionMissingBlobHashes.into());
        }

        let tx_type = self.minimal_tx_type() as u8;

        let Self {
            from,
            to,
            gas_price,
            max_fee_per_gas,
            max_priority_fee_per_gas,
            gas,
            value,
            input,
            nonce,
            access_list,
            chain_id,
            blob_versioned_hashes,
            max_fee_per_blob_gas,
            authorization_list,
            transaction_type: _,
            sidecar: _,
        } = self;

        let CallFees { max_priority_fee_per_gas, gas_price, max_fee_per_blob_gas } =
            CallFees::ensure_fees(
                gas_price.map(U256::from),
                max_fee_per_gas.map(U256::from),
                max_priority_fee_per_gas.map(U256::from),
                U256::from(block_env.basefee),
                blob_versioned_hashes.as_deref(),
                max_fee_per_blob_gas.map(U256::from),
                block_env.blob_gasprice().map(U256::from),
            )?;

        let gas_limit = gas.unwrap_or(
            // Use maximum allowed gas limit. The reason for this
            // is that both Erigon and Geth use pre-configured gas cap even if
            // it's possible to derive the gas limit from the block:
            // <https://github.com/ledgerwatch/erigon/blob/eae2d9a79cb70dbe30b3a6b79c436872e4605458/cmd/rpcdaemon/commands/trace_adhoc.go#L956
            // https://github.com/ledgerwatch/erigon/blob/eae2d9a79cb70dbe30b3a6b79c436872e4605458/eth/ethconfig/config.go#L94>
            block_env.gas_limit,
        );

        let chain_id = chain_id.unwrap_or(cfg_env.chain_id);

        let caller = from.unwrap_or_default();

        let nonce = nonce.unwrap_or_default();

        let env = TxEnv {
            tx_type,
            gas_limit,
            nonce,
            caller,
            gas_price: gas_price.saturating_to(),
            gas_priority_fee: max_priority_fee_per_gas.map(|v| v.saturating_to()),
            kind: to.unwrap_or(TxKind::Create),
            value: value.unwrap_or_default(),
            data: input.try_into_unique_input().map_err(EthTxEnvError::from)?.unwrap_or_default(),
            chain_id: Some(chain_id),
            access_list: access_list.unwrap_or_default(),
            // EIP-4844 fields
            blob_hashes: blob_versioned_hashes.unwrap_or_default(),
            max_fee_per_blob_gas: max_fee_per_blob_gas
                .map(|v| v.saturating_to())
                .unwrap_or_default(),
            // EIP-7702 fields
            authorization_list: authorization_list
                .unwrap_or_default()
                .into_iter()
                .map(Either::Left)
                .collect(),
        };

        Ok(env)
    }
}
