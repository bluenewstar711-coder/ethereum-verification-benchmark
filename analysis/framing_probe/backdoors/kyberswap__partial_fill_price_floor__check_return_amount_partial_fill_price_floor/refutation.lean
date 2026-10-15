theorem checkReturnAmount_partial_fill_price_floor_counterexample :
    ¬ (∀ (spentAmount returnAmount amount minReturnAmount flags : Uint256) (s : ContractState) (hPartial : isPartialFill { amount := amount, minReturnAmount := minReturnAmount, flags := flags } = true) (hRun : (MetaAggregationRouterV2._checkReturnAmount spentAmount returnAmount amount minReturnAmount flags).run s = ContractResult.success () s),
      partial_fill_price_floor_spec spentAmount returnAmount
      { amount := amount, minReturnAmount := minReturnAmount, flags := flags }) := by
  intro h
  have hRun : (MetaAggregationRouterV2._checkReturnAmount 0 57896044618658097711785492504343953926634992332820282019728792003956564819968 2 0 1).run defaultState =
      ContractResult.success () defaultState := by
    unfold MetaAggregationRouterV2._checkReturnAmount
    simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
      Verity.require, Verity.Stdlib.Math.mulPanic, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeMul]
  have hov : Verity.Stdlib.Math.safeMul 57896044618658097711785492504343953926634992332820282019728792003956564819968 2 = none := by
    unfold Verity.Stdlib.Math.safeMul
    rw [if_pos (by decide)]
  have hc := h 0 57896044618658097711785492504343953926634992332820282019728792003956564819968 2 0 1 defaultState (by decide) hRun (by decide)
  simp [checkedScaledPriceFloorHolds, hov] at hc
