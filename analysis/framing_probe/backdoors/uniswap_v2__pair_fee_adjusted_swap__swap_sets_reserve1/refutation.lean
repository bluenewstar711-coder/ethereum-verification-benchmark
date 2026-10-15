theorem applySwap_sets_reserve1_counterexample :
    ¬ (∀ (balance0 balance1 amount0In amount1In : Uint256) (s : ContractState) (hInput : amount0In != 0 || amount1In != 0) (hFee0 : mul balance0 1000 >= mul amount0In 3) (hFee1 : mul balance1 1000 >= mul amount1In 3) (hK : mul (sub (mul balance0 1000) (mul amount0In 3)) (sub (mul balance1 1000) (mul amount1In 3)) >= mul (mul (s.storage 0) (s.storage 1)) 1000000),
      let s' := ((PairFeeAdjustedSwap.applySwap balance0 balance1 amount0In amount1In).run s).snd
    applySwap_sets_reserve1_spec balance1 s s') := by
  intro h
  have hc := h 1 2 1 0 defaultState (by decide) (by decide) (by decide) (by decide)
  simp [applySwap_sets_reserve1_spec, PairFeeAdjustedSwap.applySwap,
    PairFeeAdjustedSwap.reserve0, PairFeeAdjustedSwap.reserve1,
    getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] at hc
  revert hc
  decide
