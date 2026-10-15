theorem transferRemote_preserves_global_solvency_counterexample :
    ¬ (∀ (assets : Uint256) (s : ContractState) (hActive : s.storage 3 = 0) (hAssetsLeBuffer : assets.val <= (s.storage 1).val) (hAssetsLeAsset : assets.val <= (s.storage 0).val),
      let s' := ((TokenGateway.transferRemote assets).run s).snd
    transferRemote_preserves_global_solvency_spec s s') := by
  intro h
  have hc := h 0 (((defaultState.writeSlot 0 10).writeSlot 1 5).writeSlot 2 5)
    (by decide) (by decide) (by decide)
  simp [transferRemote_preserves_global_solvency_spec, global_solvency_spec,
    TokenGateway.transferRemote, TokenGateway.assetBalance, TokenGateway.buffer,
    TokenGateway.assetsLocked, TokenGateway.depreciated,
    assetBalanceOf, bufferOf, assetsLockedOf, depreciatedOf,
    getStorage, setStorage, Verity.require, Verity.bind, Bind.bind,
    Pure.pure, Contract.run, ContractResult.snd] at hc
  revert hc
  decide
