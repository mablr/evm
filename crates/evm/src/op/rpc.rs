use core::convert::Infallible;

use alloy_consensus::{error::ValueError, transaction::Recovered, SignableTransaction};
use alloy_primitives::{Address, Bytes, Signature};
use op_alloy_consensus::{transaction::OpTransactionInfo, OpTxEnvelope};
use op_alloy_rpc_types::OpTransactionRequest;
use op_revm::OpTransaction;
use revm::context::{BlockEnv, CfgEnv, TxEnv};

use crate::rpc::{EthTxEnvError, FromConsensusTx, TryIntoSimTx, TryIntoTxEnv};

impl<T: op_alloy_consensus::OpTransaction + alloy_consensus::Transaction> FromConsensusTx<T>
    for op_alloy_rpc_types::Transaction<T>
{
    type TxInfo = OpTransactionInfo;
    type Err = Infallible;

    fn from_consensus_tx(tx: T, signer: Address, tx_info: Self::TxInfo) -> Result<Self, Self::Err> {
        Ok(Self::from_transaction(Recovered::new_unchecked(tx, signer), tx_info))
    }
}

impl TryIntoSimTx<OpTxEnvelope> for OpTransactionRequest {
    fn try_into_sim_tx(self) -> Result<OpTxEnvelope, ValueError<Self>> {
        let tx = self
            .build_typed_tx()
            .map_err(|request| ValueError::new(request, "Required fields missing"))?;

        // Create an empty signature for the transaction.
        let signature = Signature::new(Default::default(), Default::default(), false);

        Ok(tx.into_signed(signature).into())
    }
}

impl TryIntoTxEnv<OpTransaction<TxEnv>> for OpTransactionRequest {
    type Err = EthTxEnvError;

    fn try_into_tx_env<Spec>(
        self,
        cfg_env: &CfgEnv<Spec>,
        block_env: &BlockEnv,
    ) -> Result<OpTransaction<TxEnv>, Self::Err> {
        Ok(OpTransaction {
            base: self.as_ref().clone().try_into_tx_env(cfg_env, block_env)?,
            enveloped_tx: Some(Bytes::new()),
            deposit: Default::default(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_op_into_tx_env() {
        use op_revm::{transaction::OpTxTr, OpSpecId};
        use revm::context::Transaction;

        let s = r#"{"from":"0x0000000000000000000000000000000000000000","to":"0x6d362b9c3ab68c0b7c79e8a714f1d7f3af63655f","input":"0x1626ba7ec8ee0d506e864589b799a645ddb88b08f5d39e8049f9f702b3b61fa15e55fc73000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000550000002d6db27c52e3c11c1cf24072004ac75cba49b25bf45f513902e469755e1f3bf2ca8324ad16930b0a965c012a24bb1101f876ebebac047bd3b6bf610205a27171eaaeffe4b5e5589936f4e542d637b627311b0000000000000000000000","data":"0x1626ba7ec8ee0d506e864589b799a645ddb88b08f5d39e8049f9f702b3b61fa15e55fc73000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000550000002d6db27c52e3c11c1cf24072004ac75cba49b25bf45f513902e469755e1f3bf2ca8324ad16930b0a965c012a24bb1101f876ebebac047bd3b6bf610205a27171eaaeffe4b5e5589936f4e542d637b627311b0000000000000000000000","chainId":"0x7a69"}"#;

        let req: OpTransactionRequest = serde_json::from_str(s).unwrap();

        let cfg = CfgEnv::<OpSpecId>::default();
        let block_env = BlockEnv::default();
        let tx_env = req.try_into_tx_env(&cfg, &block_env).unwrap();
        assert_eq!(tx_env.gas_limit(), block_env.gas_limit);
        assert_eq!(tx_env.gas_price(), 0);
        assert!(tx_env.enveloped_tx().unwrap().is_empty());
    }
}
