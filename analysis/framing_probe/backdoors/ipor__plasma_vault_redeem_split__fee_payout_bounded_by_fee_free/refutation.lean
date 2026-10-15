theorem fee_payout_bounded_by_fee_free_task_counterexample :
    ¬ (∀ (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares),
      fee_payout_bounded_by_fee_free_spec amountShares feeRate s m) := by
  intro h
  have hc := h 1 0 { assets := 99, shares := 1 } 100
  unfold fee_payout_bounded_by_fee_free_spec redeemPayout feeFreePayout convertToAssets feeShares WAD at hc
  revert hc
  decide
