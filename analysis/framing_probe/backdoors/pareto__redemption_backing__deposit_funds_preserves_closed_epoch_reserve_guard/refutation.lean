theorem depositFunds_preserves_closed_epoch_reserve_guard_counterexample :
    ¬ (∀ (depositedScaled : Uint256) (s : ContractState) (hCollateralized : s.storage 5 != 0) (hDepositLeIdle : depositedScaled.val <= (s.storage 0).val) (hCurrentLeReserved : (s.storage 3).val <= (s.storage 2).val) (hAddNoOverflow : (sub (s.storage 0) depositedScaled).val + (s.storage 1).val < Verity.Core.Uint256.modulus) (hReserveGuard : (sub (s.storage 2) (s.storage 3)).val <= (add (sub (s.storage 0) depositedScaled) (s.storage 1)).val),
      let s' := ((ParetoDollarQueue.depositFunds depositedScaled).run s).snd
    depositFunds_preserves_closed_epoch_reserve_guard_spec s s') := by
  intro h
  have hc := h 0 (((defaultState.writeSlot 2 10).writeSlot 3 10).writeSlot 5 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simp [depositFunds_preserves_closed_epoch_reserve_guard_spec, closed_epoch_reserve_guard,
    ParetoDollarQueue.depositFunds, ParetoDollarQueue.idleCollateralScaled,
    ParetoDollarQueue.totCreditVaultsRequestedScaled,
    ParetoDollarQueue.totReservedWithdrawals, ParetoDollarQueue.currentEpochPending,
    ParetoDollarQueue.previousEpochPending, ParetoDollarQueue.collateralizedFlag,
    idleCollateralScaledOf, totCreditVaultsRequestedScaledOf,
    totReservedWithdrawalsOf, currentEpochPendingOf, closedClaims,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.snd] at hc
  revert hc
  decide
