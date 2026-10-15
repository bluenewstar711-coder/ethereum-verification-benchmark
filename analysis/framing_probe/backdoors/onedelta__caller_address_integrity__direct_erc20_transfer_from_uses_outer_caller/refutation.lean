theorem direct_erc20_transferFrom_uses_outer_caller_counterexample :
    ¬ (∀ (callerAddress : Address) (s : ContractState),
      let s' := ((OneDeltaComposer._transferFrom callerAddress).run s).snd
    erc20_caller_spec {s with sender := callerAddress} s') := by
  intro h
  have hc := h 0 { defaultState with sender := 1 }
  simp [erc20_caller_spec, erc20PullOccurred, erc20PullFrom, outerCallerWord,
    OneDeltaComposer._transferFrom, OneDeltaComposer.erc20TransferFromOccurred,
    OneDeltaComposer.erc20TransferFromWord,
    msgSender, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd] at hc
  revert hc
  decide
