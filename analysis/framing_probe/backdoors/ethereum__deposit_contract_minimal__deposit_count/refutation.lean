theorem deposit_increments_deposit_count_counterexample :
    ¬ (∀ (depositAmount : Uint256) (s : ContractState) (hCount : s.storage 0 < 4294967295) (hMin : depositAmount >= 1000000000),
      let s' := ((DepositContractMinimal.deposit depositAmount).run s).snd
    deposit_increments_deposit_count_spec s s') := by
  intro h
  have hc := h 32000000000 (defaultState.writeSlot 1 5) (by decide) (by decide)
  simp [deposit_increments_deposit_count_spec, DepositContractMinimal.deposit,
    DepositContractMinimal.depositCount, DepositContractMinimal.fullDepositCount,
    DepositContractMinimal.chainStarted, getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] at hc
  revert hc
  decide
