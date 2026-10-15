theorem exact_compliance_task_counterexample :
    ¬ (∀ (currentPps nextPps timePast upperRate : Uint256) (lowerRate : Verity.Core.Int256),
      exactComplianceSpec currentPps nextPps timePast upperRate lowerRate) := by
  intro h
  have hc := h 1 1 1 0 0
  unfold exactComplianceSpec at hc
  rw [if_pos (by decide)] at hc
  have h1 : isCompliant 1 1 1 0 0 = false := by decide
  have h2 : annualizedVariationInsideGuardrails 1 1 1 0 0 := by
    unfold annualizedVariationInsideGuardrails
    decide
  rw [h1] at hc
  exact absurd (hc.mpr h2) (by decide)
