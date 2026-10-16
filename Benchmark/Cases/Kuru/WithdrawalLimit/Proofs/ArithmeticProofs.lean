/-
Kuru V2 full-precision valuation, widths, refill and configuration proofs.
These are proofs of the source-shaped semantic model, not assembly/bytecode
refinement or a deployment attestation.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Specs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Benchmark.Cases.Kuru.WithdrawalLimit

/- Small inversion lemmas keep all executable guards in the proof. -/
private theorem checked_bind_ok {α β : Type} {m : Checked α}
    {f : α → Checked β} {v : β} (h : (m >>= f) = .ok v) :
    ∃ x, m = .ok x ∧ f x = .ok v := by
  cases hm : m with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok x =>
    refine ⟨x, rfl, ?_⟩
    simpa [hm, Bind.bind, Except.bind] using h

private theorem ensure_then_ok {α : Type} {p : Prop} [Decidable p]
    {e : Error} {m : Checked α} {v : α}
    (h : (do ensure p e; m) = .ok v) : p ∧ m = .ok v := by
  by_cases hp : p
  · exact ⟨hp, by simpa [ensure, hp, Bind.bind, Except.bind] using h⟩
  · simp [ensure, hp, Bind.bind, Except.bind] at h

/-- Actual narrowing is modulo; this equality requires the stated range proof. -/
theorem arithmetic_castWord_of_lt {bits v : Nat} (h : v < width bits) :
    castWord bits v = v := by
  change v % width bits = v
  exact Nat.mod_eq_of_lt h

private theorem checkedAdd_success {bits a b v : Nat}
    (h : checkedAdd bits a b = .ok v) : v = a + b ∧ a + b < width bits := by
  unfold checkedAdd at h
  obtain ⟨hwidth, h⟩ := ensure_then_ok h
  have hv : a + b = v := Except.ok.inj h
  exact ⟨hv.symm, hwidth⟩

private theorem checkedSub_success {a b v : Nat}
    (h : checkedSub a b = .ok v) : v = a - b ∧ b ≤ a := by
  unfold checkedSub at h
  obtain ⟨hle, h⟩ := ensure_then_ok h
  have hv : a - b = v := Except.ok.inj h
  exact ⟨hv.symm, hle⟩

private theorem timestamp_success {now t : Nat} (h : timestamp now = .ok t) :
    t = now ∧ now < width 64 := by
  unfold timestamp at h
  obtain ⟨hrange, h⟩ := ensure_then_ok h
  have hpos : 0 < width 64 := by norm_num [width]
  have hlt : now < width 64 := by
    unfold maxWord at hrange
    omega
  have hv : castWord 64 now = t := Except.ok.inj h
  rw [arithmetic_castWord_of_lt hlt] at hv
  exact ⟨hv.symm, hlt⟩

/-- The full mathematical product is used, even when it exceeds uint256. -/
theorem arithmetic_fullMulDiv_success {a b divisor v : Nat} {up : Bool}
    (h : fullMulDiv a b divisor up = .ok v) :
    divisor ≠ 0 ∧ v < width 256 ∧
    v = (if up ∧ a * b % divisor ≠ 0 then a * b / divisor + 1
      else a * b / divisor) := by
  unfold fullMulDiv at h
  obtain ⟨hd, h⟩ := ensure_then_ok h
  obtain ⟨hq, h⟩ := ensure_then_ok h
  by_cases hr : up ∧ a * b % divisor ≠ 0
  · rw [if_pos hr] at h
    obtain ⟨hv, hwidth⟩ := checkedAdd_success h
    exact ⟨hd, by simpa [hv] using hwidth, by simpa [hr] using hv⟩
  · rw [if_neg hr] at h
    have hv : a * b / divisor = v := Except.ok.inj h
    exact ⟨hd, by simpa [← hv] using hq, by simpa [hr] using hv.symm⟩

/-- Exact floor/ceiling inequalities, including zero and exact-division cases. -/
theorem arithmetic_fullMulDiv_rounding {a b divisor v : Nat} {up : Bool}
    (h : fullMulDiv a b divisor up = .ok v) :
    if up then a * b ≤ v * divisor ∧ v * divisor < a * b + divisor
    else v * divisor ≤ a * b ∧ a * b < (v + 1) * divisor := by
  obtain ⟨hd, _, hv⟩ := arithmetic_fullMulDiv_success h
  have hdpos : 0 < divisor := Nat.pos_of_ne_zero hd
  have hdecomp := Nat.div_add_mod' (a * b) divisor
  have hrem := Nat.mod_lt (a * b) hdpos
  cases up with
  | false =>
    simp only [Bool.false_eq_true, false_and, if_false] at hv ⊢
    rw [hv]
    constructor
    · exact Nat.div_mul_le_self (a * b) divisor
    · nlinarith
  | true =>
    simp at hv ⊢
    by_cases hr : a * b % divisor = 0
    · simp [hr] at hv
      rw [hv]
      constructor <;> nlinarith
    · simp [hr] at hv
      rw [hv]
      have hrpos : 0 < a * b % divisor := Nat.pos_of_ne_zero hr
      constructor <;> nlinarith

/-- Complete successful valuation specification, with its actual width guard. -/
theorem arithmetic_value_success (amount quote decimals : Nat) (up : Bool) (v : Nat)
    (h : value amount quote decimals up = .ok v) :
    v ≤ maxWord 192 ∧
    (decimals ≤ 18 → v = amount * quote * 10 ^ (18 - decimals)) ∧
    (decimals > 18 →
      let divisor := 10 ^ (decimals - 18)
      if up then amount * quote ≤ v * divisor ∧ v * divisor < amount * quote + divisor
      else v * divisor ≤ amount * quote ∧ amount * quote < (v + 1) * divisor) := by
  unfold value at h
  obtain ⟨_habi, h⟩ := ensure_then_ok h
  obtain ⟨_hdecimals, h⟩ := ensure_then_ok h
  by_cases hd : decimals ≤ 18
  · rw [if_pos hd] at h
    obtain ⟨hscale, h⟩ := ensure_then_ok h
    obtain ⟨hbound, h⟩ := ensure_then_ok h
    have hv : amount * (quote * 10 ^ (18 - decimals)) = v := Except.ok.inj h
    have hscalePos : 0 < quote * 10 ^ (18 - decimals) := Nat.pos_of_ne_zero hscale
    refine ⟨?_, ?_, ?_⟩
    · rw [← hv]
      exact (Nat.le_div_iff_mul_le hscalePos).mp hbound
    · intro _
      simpa only [Nat.mul_assoc] using hv.symm
    · intro hhigh
      omega
  · rw [if_neg hd] at h
    obtain ⟨result, hresult, h⟩ := checked_bind_ok h
    obtain ⟨hbound, h⟩ := ensure_then_ok h
    have hv : result = v := Except.ok.inj h
    subst result
    refine ⟨hbound, ?_, ?_⟩
    · intro hlow
      exact False.elim (hd hlow)
    · intro _
      exact arithmetic_fullMulDiv_rounding hresult

/-- Deposit dust: all allowed high-decimal inputs, not a finite 77-decimal test. -/
theorem arithmetic_value_dust (amount quote decimals : Nat)
    (hhigh : decimals > 18) (hdec : decimals ≤ 77)
    (_hqpos : quote > 0) (hq : quote < width 128) (ha : amount < width 256)
    (hsmall : amount * quote < 10 ^ (decimals - 18)) :
    value amount quote decimals false = .ok 0 := by
  have hd8 : decimals < width 8 := by
    have hw8 : width 8 = 256 := by norm_num [width]
    omega
  have habi : amount < width 256 ∧ quote < width 128 ∧ decimals < width 8 :=
    ⟨ha, hq, hd8⟩
  have hlow : ¬ decimals ≤ 18 := by omega
  have hdpos : 0 < 10 ^ (decimals - 18) := Nat.pow_pos (by decide)
  have hdne : 10 ^ (decimals - 18) ≠ 0 := Nat.ne_of_gt hdpos
  have hquot : amount * quote / 10 ^ (decimals - 18) = 0 := Nat.div_eq_of_lt hsmall
  have hw256 : 0 < width 256 := by norm_num [width]
  simp [value, ensure, habi, hdec, hlow, fullMulDiv, hdne, hquot, hw256,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The exact bound for initial and newly configured uint128 capacities. -/
theorem arithmetic_capacity_max_bound : maxWord 128 * usdScale < width 192 := by
  norm_num [maxWord, width, usdScale]

/-- Exact largest uint64 elapsed, uint128 rate, and uint192 stored balance. -/
theorem arithmetic_refill_max_bound :
    maxWord 192 + maxWord 64 * maxWord 128 * usdScale < width 256 := by
  norm_num [maxWord, width, usdScale]

theorem arithmetic_capacity_mul_lt {capacity : Nat} (h : capacity < width 128) :
    capacity * usdScale < width 192 := by
  have hc : capacity ≤ maxWord 128 := by
    unfold maxWord
    omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_right usdScale hc) arithmetic_capacity_max_bound

/-- LOW192/HIGH64 representation is recovered without changing the cast model. -/
theorem arithmetic_packedDrip (drip : DripState)
    (ha : drip.available < width 192) (ht : drip.updatedAt < width 64) :
    unpackDrip (packDrip drip) = drip := by
  cases drip with
  | mk available updatedAt =>
    have hpos : 0 < width 192 := by norm_num [width]
    change (⟨(available + updatedAt * width 192) % width 192,
      ((available + updatedAt * width 192) / width 192) % width 64⟩ : DripState) =
      ⟨available, updatedAt⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
      Nat.add_mul_div_right available updatedAt hpos, Nat.div_eq_of_lt ha,
      Nat.zero_add, Nat.mod_eq_of_lt ht]

/-- Cursor + consumed deposit credit remains below D before narrowing. -/
theorem arithmetic_cursor_cast (D cursor used : Nat) (hD : D < width 192)
    (hc : cursor ≤ D) (hu : used ≤ D - cursor) :
    castWord 192 (cursor + used) = cursor + used := by
  apply arithmetic_castWord_of_lt
  omega

/-- Entire unchanged Group 3; no representation or reachability assumption added. -/
theorem valuation_and_widths : ValuationAndWidths := by
  exact ⟨arithmetic_value_success, arithmetic_value_dust, arithmetic_capacity_max_bound,
    arithmetic_refill_max_bound, arithmetic_packedDrip, arithmetic_cursor_cast⟩

/-- Successful availableDrip evaluates the checked OLD configuration exactly. -/
theorem arithmetic_availableDrip_success (s : Persistent) (now A : Nat)
    (h : availableDrip s now = .ok A) :
    A = min (s.drip.available + (now - s.drip.updatedAt) * s.rateUsd18 * usdScale)
      (s.capacityUsd18 * usdScale) := by
  unfold availableDrip at h
  obtain ⟨elapsed, helapsed, h⟩ := checked_bind_ok h
  obtain ⟨heq, _⟩ := checkedSub_success helapsed
  subst elapsed
  obtain ⟨_hrefill, h⟩ := ensure_then_ok h
  obtain ⟨available, havailable, h⟩ := checked_bind_ok h
  obtain ⟨heq, _⟩ := checkedAdd_success havailable
  subst available
  have hA : min (s.drip.available + (now - s.drip.updatedAt) * s.rateUsd18 * usdScale)
      (s.capacityUsd18 * usdScale) = A := Except.ok.inj h
  exact hA.symm

/-- Settlement, clamp, new rate/time, frame, and no instant grant in one theorem. -/
theorem arithmetic_setDripConfig_success (s : Limiter) (now : Nat)
    (caller governance : Key) (capacity rate : Nat) (next : Limiter) (A : Nat)
    (hA : availableDrip s.persistent now = .ok A)
    (h : setDripConfig s now caller governance capacity rate = .ok next) :
    next.persistent.drip.available = min A (capacity * usdScale) ∧
    next.persistent.drip.updatedAt = now ∧ next.persistent.capacityUsd18 = capacity ∧
    next.persistent.rateUsd18 = rate ∧ next.persistent.history = s.persistent.history ∧
    next.persistent.cursor = s.persistent.cursor ∧ next.persistent.drip.available ≤ A := by
  unfold setDripConfig at h
  obtain ⟨_hauth, h⟩ := ensure_then_ok h
  obtain ⟨_hflow, h⟩ := ensure_then_ok h
  obtain ⟨hconfig, h⟩ := ensure_then_ok h
  obtain ⟨t, ht, h⟩ := checked_bind_ok h
  obtain ⟨htime, _⟩ := timestamp_success ht
  subst t
  obtain ⟨oldAvailable, hold, h⟩ := checked_bind_ok h
  rw [hA] at hold
  have hsame : A = oldAvailable := Except.ok.inj hold
  subst oldAvailable
  have hfit : min A (capacity * usdScale) < width 192 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) (arithmetic_capacity_mul_lt hconfig.1)
  have hcast := arithmetic_castWord_of_lt hfit
  have hnext : ({ s with persistent := { s.persistent with
      drip := ⟨castWord 192 (min A (capacity * usdScale)), now⟩,
      capacityUsd18 := capacity, rateUsd18 := rate } } : Limiter) = next := Except.ok.inj h
  rw [← hnext]
  simp [hcast, Nat.min_le_left]

/-- Once flow has started, drip configuration fails before settlement or mutation. -/
theorem arithmetic_setDripConfig_locked (s : Limiter) (now : Nat)
    (caller governance : Key) (capacity rate : Nat)
    (hflow : s.transient.flowStarted = true) (hauth : caller = governance) :
    setDripConfig s now caller governance capacity rate = .error .config := by
  simp [setDripConfig, ensure, hflow, hauth, Bind.bind, Except.bind]

/-- Price-source configuration has the same transaction flow lock. -/
theorem arithmetic_setPriceSource_locked (s : Limiter) (caller governance token source : Key)
    (code : Key → Bool) (hflow : s.transient.flowStarted = true)
    (hauth : caller = governance) :
    setPriceSource s caller governance token source code = .error .config := by
  simp [setPriceSource, ensure, hflow, hauth, Bind.bind, Except.bind]

/-- Entire unchanged Group 6, including both setters' configuration locks. -/
theorem drip_and_configuration : DripAndConfiguration := by
  exact ⟨arithmetic_availableDrip_success, arithmetic_setDripConfig_success,
    arithmetic_setDripConfig_locked, arithmetic_setPriceSource_locked⟩

end Benchmark.Cases.Kuru.WithdrawalLimit
