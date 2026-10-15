theorem draw_interval_matches_weights_counterexample :
    ¬ (∀ (ticket : Uint256) (s : ContractState) (hRoot : s.storage 0 != 0) (hInRange : ticket < s.storage 0),
      let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_interval_matches_weights_spec ticket s s') := by
  intro h
  have hc := h 2 (((defaultState.writeSlot 0 10).writeSlot 1 5).writeSlot 3 2) (by decide) (by decide)
  simp [draw_interval_matches_weights_spec, SortitionTrees.draw,
    SortitionTrees.rootSum, SortitionTrees.leftSum, SortitionTrees.leaf0, SortitionTrees.leaf2,
    SortitionTrees.selectedNode,
    getStorage, setStorage, Verity.require, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd] at hc
  revert hc
  decide
