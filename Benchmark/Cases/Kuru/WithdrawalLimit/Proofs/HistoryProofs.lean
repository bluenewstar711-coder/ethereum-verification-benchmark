/-
Kuru V2 exact history correspondence proof.
The full five-conjunct statement is established on the executable Lean history
model. This is not a mechanized Solidity or bytecode refinement theorem.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Specs
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.SplitIfs

namespace Benchmark.Cases.Kuru.WithdrawalLimit
namespace HistoryProofs

@[simp] private theorem checked_pure {α : Type} (a : α) :
    (pure a : Checked α) = .ok a := rfl
@[simp] private theorem checked_bind_ok {α β : Type} (a : α) (f : α → Checked β) :
    ((Except.ok a : Checked α) >>= f) = f a := rfl
@[simp] private theorem checked_bind_error {α β : Type} (e : Error) (f : α → Checked β) :
    ((Except.error e : Checked α) >>= f) = .error e := rfl
@[simp] private theorem checked_map_ok {α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Checked α) = .ok (f a) := rfl
@[simp] private theorem checked_map_error {α β : Type} (e : Error) (f : α → β) :
    f <$> (Except.error e : Checked α) = .error e := rfl

private theorem width_pos (bits : Nat) : 0 < width bits :=
  Nat.pow_pos (by decide)

private theorem cast_eq {bits n : Nat} (hn : n < width bits) : castWord bits n = n := by
  exact Nat.mod_eq_of_lt hn

private theorem retainedOldest_eq (n : Nat) :
    (if n > ringCapacity then n - ringCapacity + 1 else 1) = retainedOldest n := rfl

theorem oldest_bounds {n : Nat} (hn : 0 < n) :
    1 ≤ retainedOldest n ∧ retainedOldest n ≤ n := by
  unfold retainedOldest ringCapacity window
  split <;> omega

theorem oldest_mono {a b : Nat} (hab : a ≤ b) :
    retainedOldest a ≤ retainedOldest b := by
  unfold retainedOldest ringCapacity window
  split_ifs <;> omega

/-- All logical positions in one retained ring interval have distinct cells. -/
theorem ring_index_injective (sequence other latest : Nat)
    (hs : retainedOldest latest ≤ sequence) (hsl : sequence ≤ latest)
    (ho : retainedOldest latest ≤ other) (hol : other ≤ latest)
    (he : (sequence - 1) % ringCapacity = (other - 1) % ringCapacity) :
    sequence = other := by
  unfold retainedOldest ringCapacity window at *
  split_ifs at hs ho <;> omega

/-- The mathematical list projection is used only in proofs, not by lookup. -/
private def logicalAt (xs : List Checkpoint) (s : Nat) : Checkpoint :=
  (xs[s - 1]?).getD {}

private theorem logical_some {xs : List Checkpoint} {s : Nat}
    (hs : 1 ≤ s) (hl : s ≤ xs.length) :
    xs[s - 1]? = some (logicalAt xs s) := by
  have hi : s - 1 < xs.length := by omega
  simp [logicalAt, List.getElem?_eq_getElem, hi]

private theorem logical_of_some {xs : List Checkpoint} {s : Nat} {cp : Checkpoint}
    (h : xs[s - 1]? = some cp) : logicalAt xs s = cp := by
  simp [logicalAt, h]

private theorem logical_order {xs : List Checkpoint} (hc : chronological xs)
    {i j : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ xs.length) :
    (logicalAt xs i).timestamp < (logicalAt xs j).timestamp ∧
    (logicalAt xs i).cumulative ≤ (logicalAt xs j).cumulative := by
  have hi' : i - 1 < xs.length := by omega
  have hj' : j - 1 < xs.length := by omega
  have hij' : i - 1 < j - 1 := by omega
  have hp := List.pairwise_iff_getElem.mp hc (i - 1) (j - 1) hi' hj' hij'
  simpa [logicalAt, List.getElem?_eq_getElem, hi', hj'] using hp

private theorem logical_gap {xs : List Checkpoint} (hc : chronological xs)
    {i j : Nat} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ xs.length) :
    (logicalAt xs i).timestamp + (j - i) ≤ (logicalAt xs j).timestamp := by
  revert hij hj
  induction j with
  | zero => intro hij hj; omega
  | succ j ih =>
    intro hij hj
    by_cases he : i = j + 1
    · subst i; simp
    · have hij' : i ≤ j := by omega
      have hprev := ih hij' (by omega)
      have hstep := (logical_order hc (by omega : 1 ≤ j) (by omega : j < j + 1) hj).1
      omega

private theorem ring_logical {h : History} {xs : List Checkpoint}
    (hr : RingRepresentation h xs) {s : Nat}
    (ho : retainedOldest h.latestSequence ≤ s) (hl : s ≤ h.latestSequence) :
    checkpointAt h s = logicalAt xs s := by
  exact (logical_of_some (hr.2.2.2.2.2 s ho hl)).symm

private theorem last_logical {xs : List Checkpoint} (hn : 0 < xs.length) :
    lastTimestamp xs = (logicalAt xs xs.length).timestamp ∧
    lastDeposit xs = (logicalAt xs xs.length).cumulative := by
  have hi : xs.length - 1 < xs.length := by omega
  simp [lastTimestamp, lastDeposit, List.getLast?_eq_getElem?,
    logicalAt, List.getElem?_eq_getElem, hi]

private theorem current_logical {h : History} {xs : List Checkpoint}
    (hr : RingRepresentation h xs) (hn : 0 < h.latestSequence) :
    current h = (logicalAt xs h.latestSequence).cumulative := by
  have ho := oldest_bounds hn
  simp [current, Nat.ne_of_gt hn, ring_logical hr ho.2 (Nat.le_refl _)]

private def scanStep (cutoff : Nat) (acc : (Nat × Nat) × Nat) (cp : Checkpoint) :
    (Nat × Nat) × Nat :=
  ((if cp.timestamp ≤ cutoff then (cp.cumulative, acc.2) else acc.1), acc.2 + 1)

/-- A fold lemma with an arbitrary accumulator: a boundary describes the exact
    fold, including its logical sequence, not just the cumulative amount. -/
private theorem scan_partition (xs : List Checkpoint) (cutoff k n : Nat)
    (a : Nat × Nat) (cp : Checkpoint) (hk : k ≤ xs.length)
    (hex : ∀ i q, xs[i]? = some q → i < k → q.timestamp ≤ cutoff)
    (hnew : ∀ i q, xs[i]? = some q → k ≤ i → cutoff < q.timestamp)
    (hcp : 0 < k → xs[k - 1]? = some cp) :
    xs.foldl (scanStep cutoff) (a, n) =
      ((if k = 0 then a else (cp.cumulative, n + k - 1)), n + xs.length) := by
  induction xs generalizing k n a cp with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    simp
  | cons x xs ih =>
    cases k with
    | zero =>
      have hx := hnew 0 x (by simp) (by omega)
      have ht : ∀ i q, xs[i]? = some q → 0 ≤ i → cutoff < q.timestamp := by
        intro i q hq _
        exact hnew (i + 1) q (by simpa using hq) (by omega)
      have hi := ih 0 (n + 1) a cp (by omega) (by omega) ht (by omega)
      simpa [List.foldl_cons, scanStep, Nat.not_le_of_gt hx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
    | succ k =>
      have hx := hex 0 x (by simp) (by omega)
      have he : ∀ i q, xs[i]? = some q → i < k → q.timestamp ≤ cutoff := by
        intro i q hq hik
        exact hex (i + 1) q (by simpa using hq) (by omega)
      have hn : ∀ i q, xs[i]? = some q → k ≤ i → cutoff < q.timestamp := by
        intro i q hq hik
        exact hnew (i + 1) q (by simpa using hq) (by omega)
      have hp : 0 < k → xs[k - 1]? = some cp := by
        intro hpos
        have hh := hcp (by omega)
        have heq : k = (k - 1) + 1 := by omega
        have hh' : (x :: xs)[k]? = some cp := by
          simpa only [Nat.add_sub_cancel] using hh
        rw [heq, List.getElem?_cons_succ] at hh'
        exact hh'
      have hi := ih k (n + 1) (x.cumulative, n) cp (by simpa using hk) he hn hp
      by_cases hz : k = 0
      · subst k
        have heq : x = cp := by simpa using hcp (by omega)
        subst cp
        simpa [List.foldl_cons, scanStep, hx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
      · have ha : n + 1 + k - 1 = n + (k + 1) - 1 := by omega
        simpa [List.foldl_cons, scanStep, hx, hz, ha, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

private theorem reference_boundary {xs : List Checkpoint} {now k : Nat}
    (hc : chronological xs) (ht : window ≤ now)
    (hk : 1 ≤ k) (hl : k ≤ xs.length)
    (he : (logicalAt xs k).timestamp ≤ now - window)
    (hn : k = xs.length ∨ now - window < (logicalAt xs (k + 1)).timestamp) :
    expiredReference xs now = ((logicalAt xs k).cumulative, k) := by
  have hex : ∀ i q, xs[i]? = some q → i < k → q.timestamp ≤ now - window := by
    intro i q hq hik
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hq
    have hq' : logicalAt xs (i + 1) = q := by
      apply logical_of_some
      simpa using hq
    by_cases heq : i + 1 = k
    · simpa [← hq', heq] using he
    · have hp := (logical_order hc (by omega : 1 ≤ i + 1)
          (by omega : i + 1 < k) hl).1
      rw [hq'] at hp
      omega
  have hnew : ∀ i q, xs[i]? = some q → k ≤ i → now - window < q.timestamp := by
    intro i q hq hik
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hq
    have hq' : logicalAt xs (i + 1) = q := by
      apply logical_of_some
      simpa using hq
    rcases hn with hn | hn
    · omega
    · by_cases heq : i = k
      · simpa [← hq', heq] using hn
      · have hp := (logical_order hc (by omega : 1 ≤ k + 1)
            (by omega : k + 1 < i + 1) (by omega)).1
        rw [hq'] at hp
        omega
  have hs := scan_partition xs (now - window) k 1 (0, 0) (logicalAt xs k)
    hl hex hnew (fun _ => logical_some hk hl)
  have hk0 : k ≠ 0 := by omega
  have ha : 1 + k - 1 = k := by omega
  rw [expiredReference, if_neg (Nat.not_lt_of_ge ht)]
  change (xs.foldl (scanStep (now - window)) ((0, 0), 1)).1 = _
  simpa only [if_neg hk0, ha] using congrArg Prod.fst hs

private theorem reference_none {xs : List Checkpoint} {now : Nat}
    (ht : window ≤ now)
    (hn : ∀ s, 1 ≤ s → s ≤ xs.length → now - window < (logicalAt xs s).timestamp) :
    expiredReference xs now = (0, 0) := by
  have hnew : ∀ i q, xs[i]? = some q → 0 ≤ i → now - window < q.timestamp := by
    intro i q hq _
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hq
    have hq' : logicalAt xs (i + 1) = q := by
      apply logical_of_some
      simpa using hq
    simpa [hq'] using hn (i + 1) (by omega) (by omega)
  have hs := scan_partition xs (now - window) 0 1 (0, 0) {}
    (by omega) (by omega) hnew (by omega)
  rw [expiredReference, if_neg (Nat.not_lt_of_ge ht)]
  change (xs.foldl (scanStep (now - window)) ((0, 0), 1)).1 = _
  simpa only [ite_true] using congrArg Prod.fst hs

/-- Binary-search invariant over the *full* ghost list. The executable search
    still consults only retained ring cells. No search fuel or expiry oracle. -/
private theorem upper_partition (h : History) (xs : List Checkpoint) (cutoff low high : Nat)
    (hr : RingRepresentation h xs)
    (hlo : retainedOldest h.latestSequence ≤ low) (hlh : low ≤ high)
    (hhi : high ≤ h.latestSequence + 1)
    (hex : ∀ s, 1 ≤ s → s ≤ xs.length → s < low →
      (logicalAt xs s).timestamp ≤ cutoff)
    (hnew : ∀ s, 1 ≤ s → s ≤ xs.length → high ≤ s →
      cutoff < (logicalAt xs s).timestamp) :
    low ≤ upperBound h cutoff low high ∧ upperBound h cutoff low high ≤ high ∧
    (∀ s, 1 ≤ s → s ≤ xs.length → s < upperBound h cutoff low high →
      (logicalAt xs s).timestamp ≤ cutoff) ∧
    (∀ s, 1 ≤ s → s ≤ xs.length → upperBound h cutoff low high ≤ s →
      cutoff < (logicalAt xs s).timestamp) := by
  by_cases hlt : low < high
  · let middle := (low + high) / 2
    have hmlo : low ≤ middle := by dsimp [middle]; omega
    have hmhi : middle < high := by dsimp [middle]; omega
    have hmold : retainedOldest h.latestSequence ≤ middle := by omega
    have hmlast : middle ≤ h.latestSequence := by omega
    have hmwidth : middle < width 64 := by have := hr.2.1; omega
    have hcast : castWord 64 middle = middle := cast_eq hmwidth
    have hcell := ring_logical hr hmold hmlast
    have hmn : 1 ≤ middle := by
      have : 1 ≤ retainedOldest h.latestSequence := by
        unfold retainedOldest ringCapacity window; split <;> omega
      omega
    by_cases htest : (checkpointAt h (castWord 64 middle)).timestamp ≤ cutoff
    · have heq : upperBound h cutoff low high = upperBound h cutoff (middle + 1) high := by
        rw [upperBound]
        simp only [dif_pos hlt]
        change (if (checkpointAt h (castWord 64 middle)).timestamp ≤ cutoff then _ else _) = _
        rw [if_pos htest]
      rw [heq]
      have hmex : (logicalAt xs middle).timestamp ≤ cutoff := by
        simpa [hcast, hcell] using htest
      have hex' : ∀ s, 1 ≤ s → s ≤ xs.length → s < middle + 1 →
          (logicalAt xs s).timestamp ≤ cutoff := by
        intro s hs hsl hsm
        by_cases hsm' : s < low
        · exact hex s hs hsl hsm'
        · by_cases heq : s = middle
          · simpa [heq] using hmex
          · have hp := (logical_order hr.2.2.2.1 hs (by omega : s < middle)
                (by have := hr.1; omega)).1
            omega
      have hi := upper_partition h xs cutoff (middle + 1) high hr
        (by omega) (by omega) hhi hex' hnew
      exact ⟨by omega, hi.2⟩
    · have heq : upperBound h cutoff low high = upperBound h cutoff low middle := by
        rw [upperBound]
        simp only [dif_pos hlt]
        change (if (checkpointAt h (castWord 64 middle)).timestamp ≤ cutoff then _ else _) = _
        rw [if_neg htest]
      rw [heq]
      have hmfresh : cutoff < (logicalAt xs middle).timestamp := by
        have : ¬ (logicalAt xs middle).timestamp ≤ cutoff := by
          simpa [hcast, hcell] using htest
        omega
      have hnew' : ∀ s, 1 ≤ s → s ≤ xs.length → middle ≤ s →
          cutoff < (logicalAt xs s).timestamp := by
        intro s hs hsl hms
        by_cases heq : s = middle
        · simpa [heq] using hmfresh
        · have hp := (logical_order hr.2.2.2.1 hmn (by omega : middle < s) hsl).1
          omega
      have hi := upper_partition h xs cutoff low middle hr hlo
        (by omega) (by omega) hex hnew'
      exact ⟨hi.1, by omega, hi.2.2⟩
  · have hu : upperBound h cutoff low high = low := by
      rw [upperBound]
      simp only [dif_neg hlt, if_neg hlt]
    rw [hu]
    have heq : high = low := by omega
    exact ⟨Nat.le_refl _, by omega, hex, by simpa [heq] using hnew⟩
termination_by high - low
decreasing_by all_goals (simp_wf; dsimp [middle] at *; omega)

/-- Complete ring lookup, with stale-cache fallthrough and both cache shortcuts. -/
theorem referenceAt_exact (h : History) (xs : List Checkpoint) (now : Nat)
    (hr : RingRepresentation h xs) (ht : lastTimestamp xs ≤ now)
    (_hw : now < width 64) : referenceAt h now = .ok (expiredReference xs now) := by
  have hlen := hr.1
  have hc := hr.2.2.2.1
  by_cases hz : h.latestSequence = 0
  · have hxs : xs = [] := by
      have : xs.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    subst xs
    simp [referenceAt, hz, expiredReference]
  by_cases hearly : now < window
  · simp [referenceAt, hearly, expiredReference]
  have hn : 0 < h.latestSequence := by omega
  have ho := oldest_bounds hn
  have hlast := ring_logical hr ho.2 (Nat.le_refl _)
  have hlasttime : (logicalAt xs h.latestSequence).timestamp ≤ now := by
    have hh := (last_logical (by omega : 0 < xs.length)).1
    rw [← hlen] at hh
    omega
  have htime : window ≤ now := by omega
  have hzero : ¬ (h.latestSequence = 0 ∨ now < window) := by omega
  by_cases hlex : (checkpointAt h h.latestSequence).timestamp ≤ now - window
  · have hb := reference_boundary (k := h.latestSequence) hc htime (by omega) (by omega)
      (by simpa only [hlast] using hlex) (Or.inl (by omega))
    simp only [referenceAt, if_neg hzero, checked_pure, checked_bind_ok,
      if_pos hlex]
    rw [hlast, hb]
  have hold := ring_logical hr (Nat.le_refl _) ho.2
  by_cases hofresh : now - window < (checkpointAt h (retainedOldest h.latestSequence)).timestamp
  · have hone : retainedOldest h.latestSequence = 1 := by
      by_contra hne
      have hover : h.latestSequence > ringCapacity := by
        by_contra hnov
        have : retainedOldest h.latestSequence = 1 := by
          simp [retainedOldest, hnov]
        exact hne this
      have hgap := logical_gap hc ho.1 ho.2 (by omega)
      have hd : h.latestSequence - retainedOldest h.latestSequence = window := by
        rw [retainedOldest, if_pos hover]
        unfold ringCapacity window at *
        omega
      rw [hd, ← hold] at hgap
      omega
    have hall : ∀ s, 1 ≤ s → s ≤ xs.length →
        now - window < (logicalAt xs s).timestamp := by
      intro s hs hsl
      have hf : now - window < (logicalAt xs 1).timestamp := by
        rw [hold, hone] at hofresh
        exact hofresh
      by_cases heq : s = 1
      · simpa [heq] using hf
      · have hp := (logical_order hc (by omega : 1 ≤ 1) (by omega : 1 < s) hsl).1
        omega
    have hb := reference_none htime hall
    simp only [referenceAt, if_neg hzero, checked_pure, checked_bind_ok,
      if_neg hlex, retainedOldest_eq, if_pos hofresh]
    simp [ensure, hone, hb]
  have holdex : (logicalAt xs (retainedOldest h.latestSequence)).timestamp ≤ now - window := by
    rw [← hold]; omega
  have hsearch := upper_partition h xs (now - window)
    (retainedOldest h.latestSequence) (h.latestSequence + 1) hr
    (Nat.le_refl _) (by omega) (Nat.le_refl _)
    (by
      intro s hs hsl hso
      have hp := (logical_order hc hs hso (by omega)).1
      omega)
    (by intro s hs hsl hhigh; omega)
  let r := upperBound h (now - window) (retainedOldest h.latestSequence) (h.latestSequence + 1)
  have hrlo : retainedOldest h.latestSequence ≤ r := hsearch.1
  have hrhi : r ≤ h.latestSequence + 1 := hsearch.2.1
  have hrg : retainedOldest h.latestSequence < r := by
    by_contra hng
    have hf := hsearch.2.2.2 (retainedOldest h.latestSequence) ho.1 (by omega) (by omega)
    omega
  have hkold : retainedOldest h.latestSequence ≤ r - 1 := by omega
  have hklast : r - 1 ≤ h.latestSequence := by omega
  have hkpos : 1 ≤ r - 1 := by omega
  have hkat := ring_logical hr hkold hklast
  have hkcast : castWord 64 (r - 1) = r - 1 := cast_eq (by have := hr.2.1; omega)
  have hbsearch := reference_boundary hc htime hkpos (by omega)
    (hsearch.2.2.1 (r - 1) hkpos (by omega) (by omega))
    (by
      by_cases heq : r - 1 = xs.length
      · exact Or.inl heq
      · apply Or.inr
        have heq' : r - 1 + 1 = r := by omega
        rw [heq']
        exact hsearch.2.2.2 r (by omega) (by omega) (Nat.le_refl _))
  have hfallback :
      ((checkpointAt h (castWord 64 (r - 1))).cumulative, castWord 64 (r - 1)) =
        expiredReference xs now := by
    rw [hkcast, hkat, hbsearch]
  by_cases hcache : h.referenceSequence ≥ retainedOldest h.latestSequence ∧
      h.referenceSequence < h.latestSequence
  · have hca := ring_logical hr hcache.1 (by omega)
    have hcan := ring_logical hr (by omega : retainedOldest h.latestSequence ≤ h.referenceSequence + 1)
      (by omega : h.referenceSequence + 1 ≤ h.latestSequence)
    have hcpos : 1 ≤ h.referenceSequence := by omega
    by_cases hcex : (checkpointAt h h.referenceSequence).timestamp ≤ now - window
    · by_cases hnext : now - window < (checkpointAt h (h.referenceSequence + 1)).timestamp
      · have hb := reference_boundary hc htime hcpos (by omega)
          (by simpa [hca] using hcex) (Or.inr (by simpa [hcan] using hnext))
        simp only [referenceAt, if_neg hzero, checked_pure, checked_bind_ok,
          if_neg hlex, retainedOldest_eq, if_neg hofresh, if_pos hcache,
          if_pos hcex, if_pos hnext]
        rw [hca, hb]
      · by_cases htwo : h.referenceSequence + 1 < h.latestSequence ∧
            now - window < (checkpointAt h (h.referenceSequence + 2)).timestamp
        · have hcan2 := ring_logical hr
            (by omega : retainedOldest h.latestSequence ≤ h.referenceSequence + 2)
            (by omega : h.referenceSequence + 2 ≤ h.latestSequence)
          have hb := reference_boundary hc htime (by omega : 1 ≤ h.referenceSequence + 1)
            (by omega) (by rw [← hcan]; omega)
            (Or.inr (by simpa [hcan2, Nat.add_assoc] using htwo.2))
          simp only [referenceAt, if_neg hzero, checked_pure, checked_bind_ok,
            if_neg hlex, retainedOldest_eq, if_neg hofresh, if_pos hcache,
            if_pos hcex, if_neg hnext, if_pos htwo]
          rw [hcan, hb]
        · simpa [referenceAt, hzero, hlex, retainedOldest_eq, hofresh,
            hcache, hcex, hnext, htwo, r] using congrArg (fun p : Nat × Nat => (Except.ok p : Checked (Nat × Nat))) hfallback
    · simpa [referenceAt, hzero, hlex, retainedOldest_eq, hofresh,
        hcache, hcex, r] using congrArg (fun p : Nat × Nat => (Except.ok p : Checked (Nat × Nat))) hfallback
  · simpa [referenceAt, hzero, hlex, retainedOldest_eq, hofresh,
      hcache, r] using congrArg (fun p : Nat × Nat => (Except.ok p : Checked (Nat × Nat))) hfallback

/-- Appending at the maximum logical sequence fails before any new cell is returned. -/
theorem sequence_overflow (h : History) (v now : Nat)
    (hl : h.latestSequence = maxWord 64)
    (ht : now > (checkpointAt h h.latestSequence).timestamp)
    (hv : v ≤ maxWord 192) (hw : now ≤ maxWord 64) (hm : v ≥ current h) :
    write h v now = .error .arithmetic := by
  have hp : 0 < maxWord 64 := by decide
  have hz : h.latestSequence ≠ 0 := by omega
  have hm' : (checkpointAt h h.latestSequence).cumulative ≤ v := by
    simpa [current, hz] using hm
  have ht' : (checkpointAt h h.latestSequence).timestamp ≤ now := by omega
  have htne : now ≠ (checkpointAt h h.latestSequence).timestamp := by omega
  have hf : ¬ h.latestSequence + 1 < width 64 := by
    have hp' := width_pos 64
    unfold maxWord at hl
    omega
  simp [write, ensure, checkedAdd, hv, hw, hz, hm', ht', htne, hf]

/-- Exact low64/high192 arithmetic roundtrip, with the stated field ranges. -/
theorem checkpoint_roundtrip (cp : Checkpoint)
    (ht : cp.timestamp < width 64) (hc : cp.cumulative < width 192) :
    unpackCheckpoint (packCheckpoint cp) = cp := by
  have hmod : (cp.timestamp + cp.cumulative * width 64) % width 64 = cp.timestamp := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ht]
  have hdiv : (cp.timestamp + cp.cumulative * width 64) / width 64 = cp.cumulative := by
    rw [Nat.add_mul_div_right _ _ (width_pos 64), Nat.div_eq_of_lt ht]
    simp
  cases cp
  simp_all [unpackCheckpoint, packCheckpoint, Nat.mod_eq_of_lt]

private def installed (h : History) (s : Nat) (cp : Checkpoint) : History :=
  { h with
    latestSequence := s
    checkpoints := fun i => if i = (s - 1) % ringCapacity then cp else h.checkpoints i }

private theorem installed_current (h : History) (s : Nat) (cp : Checkpoint)
    (hs : 0 < s) : current (installed h s cp) = cp.cumulative := by
  simp [current, installed, checkpointAt, Nat.ne_of_gt hs]

private theorem latest_select (s latest : Nat) :
    (if s ≠ latest then s else latest) = s := by
  split <;> simp_all

private def nextSequence (h : History) (xs : List Checkpoint) (now : Nat) : Nat :=
  if h.latestSequence = 0 then 1
  else if now = lastTimestamp xs then h.latestSequence else h.latestSequence + 1

/-- Successful writes expose their actual checks, modulo casts and logical
    append/coalesce decision. No extra guard is inserted into the model. -/
private theorem write_shape (h : History) (xs : List Checkpoint) (now v : Nat)
    (next : History) (hr : RingRepresentation h xs) (ht : lastTimestamp xs ≤ now)
    (hm : current h ≤ v) (hw : write h v now = .ok next) :
    now < width 64 ∧ v < width 192 ∧ nextSequence h xs now < width 64 ∧
      next = installed h (nextSequence h xs now) ⟨now, v⟩ := by
  have hv : v ≤ maxWord 192 := by
    by_contra hbad
    simp [write, ensure, hbad] at hw
  have hnow : now ≤ maxWord 64 := by
    by_contra hbad
    simp [write, ensure, hv, hbad] at hw
  have hv' : v < width 192 := by
    have hp := width_pos 192
    unfold maxWord at hv
    omega
  have hnow' : now < width 64 := by
    have hp := width_pos 64
    unfold maxWord at hnow
    omega
  have cv := cast_eq hv'
  have ct := cast_eq hnow'
  by_cases hz : h.latestSequence = 0
  · have hn : nextSequence h xs now = 1 := by simp [nextSequence, hz]
    have hout : installed h 1 ⟨now, v⟩ = next := by
      simpa [write, ensure, hv, hnow, hz, ct, cv, installed, latest_select] using hw
    exact ⟨hnow', hv', by simpa [hn] using (show 1 < width 64 by decide),
      by simpa [hn] using hout.symm⟩
  · have hn : 0 < h.latestSequence := by omega
    have ho := oldest_bounds hn
    have hcp := ring_logical hr ho.2 (Nat.le_refl _)
    have hlast := last_logical (by have := hr.1; omega : 0 < xs.length)
    have htprev : (checkpointAt h h.latestSequence).timestamp = lastTimestamp xs := by
      rw [hcp, hr.1]
      exact hlast.1.symm
    have hmprev : (checkpointAt h h.latestSequence).cumulative ≤ v := by
      simpa [current, hz] using hm
    have htp : (checkpointAt h h.latestSequence).timestamp ≤ now := by omega
    by_cases heq : now = lastTimestamp xs
    · have hn' : nextSequence h xs now = h.latestSequence := by simp [nextSequence, hz, heq]
      have hne : ¬ now ≠ (checkpointAt h h.latestSequence).timestamp := by omega
      have hout : installed h h.latestSequence ⟨now, v⟩ = next := by
        simpa [write, ensure, hv, hnow, hz, hmprev, htp, hne,
          ct, cv, installed, latest_select] using hw
      exact ⟨hnow', hv', by simpa [hn'] using hr.2.1,
        by simpa [hn'] using hout.symm⟩
    · have hne : now ≠ (checkpointAt h h.latestSequence).timestamp := by omega
      by_cases hinc : h.latestSequence + 1 < width 64
      · have hn' : nextSequence h xs now = h.latestSequence + 1 := by
          simp [nextSequence, hz, heq]
        have hout : installed h (h.latestSequence + 1) ⟨now, v⟩ = next := by
          simpa [write, ensure, checkedAdd, hv, hnow, hz, hmprev, htp, hne,
            hinc, ct, cv, installed, latest_select] using hw
        exact ⟨hnow', hv', by simpa [hn'] using hinc,
          by simpa [hn'] using hout.symm⟩
      · simp [write, ensure, checkedAdd, hv, hnow, hz, hmprev, htp, hne, hinc] at hw

private theorem ghostWrite_last (ys : List Checkpoint) (old cp : Checkpoint) :
    ghostWrite (ys ++ [old]) cp =
      if old.timestamp = cp.timestamp then ys ++ [cp] else (ys ++ [old]) ++ [cp] := by
  induction ys with
  | nil => simp [ghostWrite]
  | cons x ys ih =>
    cases ys with
    | nil => split_ifs <;> simp_all [ghostWrite]
    | cons y ys =>
      by_cases heq : old.timestamp = cp.timestamp <;>
        simpa [ghostWrite, List.cons_append, heq] using congrArg (List.cons x) ih

private theorem chronological_append (xs : List Checkpoint) (old cp : Checkpoint)
    (hc : chronological xs) (hl : xs.getLast? = some old)
    (ht : old.timestamp < cp.timestamp) (hv : old.cumulative ≤ cp.cumulative) :
    chronological (xs ++ [cp]) := by
  rcases List.getLast?_eq_some_iff.mp hl with ⟨ys, rfl⟩
  have hp := List.pairwise_append.mp hc
  apply List.pairwise_append.mpr
  refine ⟨hc, by simp, ?_⟩
  intro a ha b hb
  have hb' : b = cp := by simpa using hb
  subst b
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · have hab := hp.2.2 a ha old (by simp)
    exact ⟨by omega, by omega⟩
  · exact ⟨ht, hv⟩

private theorem chronological_replace (ys : List Checkpoint) (old cp : Checkpoint)
    (hc : chronological (ys ++ [old])) (ht : old.timestamp = cp.timestamp)
    (hv : old.cumulative ≤ cp.cumulative) : chronological (ys ++ [cp]) := by
  have hp := List.pairwise_append.mp hc
  apply List.pairwise_append.mpr
  refine ⟨hp.1, by simp, ?_⟩
  intro a ha b hb
  have hb' : b = cp := by simpa using hb
  subst b
  have hab := hp.2.2 a ha old (by simp)
  exact ⟨by omega, by omega⟩

private theorem install_empty (h : History) (cp : Checkpoint)
    (hr : RingRepresentation h []) (ht : cp.timestamp < width 64)
    (hv : cp.cumulative < width 192) : RingRepresentation (installed h 1 cp) [cp] := by
  have hz : h.latestSequence = 0 := by simpa using hr.1
  have href : h.referenceSequence = 0 := by have := hr.2.2.1; omega
  refine ⟨by simp [installed], by change 1 < width 64; decide, by simp [installed, href],
    by simp [chronological], ?_, ?_⟩
  · intro q hq
    have : q = cp := by simpa using hq
    subst q
    exact ⟨ht, hv⟩
  · intro s hs hl
    have hs' : 1 ≤ s := by simpa [installed, retainedOldest, ringCapacity, window] using hs
    have hl' : s ≤ 1 := hl
    have heq : s = 1 := by omega
    subst s
    simp [installed, checkpointAt]

/-- Representation closure on append: every old retained cell except the new
    physical cell is preserved, including when that cell wraps to index zero. -/
private theorem install_append (h : History) (xs : List Checkpoint) (old cp : Checkpoint)
    (hr : RingRepresentation h xs) (hlast : xs.getLast? = some old)
    (ht : old.timestamp < cp.timestamp) (hv : old.cumulative ≤ cp.cumulative)
    (htw : cp.timestamp < width 64) (hvw : cp.cumulative < width 192)
    (hseq : h.latestSequence + 1 < width 64) :
    RingRepresentation (installed h (h.latestSequence + 1) cp) (xs ++ [cp]) := by
  have hlen := hr.1
  have hpos : 0 < h.latestSequence + 1 := by omega
  have hold := oldest_bounds hpos
  refine ⟨by simp [installed, hlen], hseq, ?_,
    chronological_append xs old cp hr.2.2.2.1 hlast ht hv, ?_, ?_⟩
  · have href := hr.2.2.1
    change h.referenceSequence ≤ h.latestSequence + 1
    omega
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hr.2.2.2.2.1 q hq
    · exact ⟨htw, hvw⟩
  · intro s hs hsl
    change retainedOldest (h.latestSequence + 1) ≤ s at hs
    change s ≤ h.latestSequence + 1 at hsl
    by_cases heq : s = h.latestSequence + 1
    · subst s
      have hi : h.latestSequence + 1 - 1 = xs.length := by omega
      simp [installed, checkpointAt, hi, List.getElem?_append]
    · have hsold : retainedOldest h.latestSequence ≤ s :=
        Nat.le_trans (oldest_mono (by omega)) hs
      have hslold : s ≤ h.latestSequence := by omega
      have hneq : (s - 1) % ringCapacity ≠ (h.latestSequence + 1 - 1) % ringCapacity := by
        intro he
        have he' := ring_index_injective s (h.latestSequence + 1) (h.latestSequence + 1)
          hs hsl hold.2 (Nat.le_refl _) he
        exact heq he'
      have hi : s - 1 < xs.length := by omega
      rw [List.getElem?_append_left hi]
      simpa only [installed, checkpointAt, if_neg hneq] using hr.2.2.2.2.2 s hsold hslold

/-- Representation closure on same-second replacement. Logical length and the
    cached sequence do not change; older cumulative values are not rewritten. -/
private theorem install_replace (h : History) (ys : List Checkpoint) (old cp : Checkpoint)
    (hr : RingRepresentation h (ys ++ [old])) (ht : old.timestamp = cp.timestamp)
    (hv : old.cumulative ≤ cp.cumulative)
    (htw : cp.timestamp < width 64) (hvw : cp.cumulative < width 192) :
    RingRepresentation (installed h h.latestSequence cp) (ys ++ [cp]) := by
  have hlen : h.latestSequence = ys.length + 1 := by simpa using hr.1
  have hn : 0 < h.latestSequence := by omega
  have ho := oldest_bounds hn
  refine ⟨by simp [installed, hlen], hr.2.1, hr.2.2.1,
    chronological_replace ys old cp hr.2.2.2.1 ht hv, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hr.2.2.2.2.1 q (by simp [hq])
    · exact ⟨htw, hvw⟩
  · intro s hs hsl
    change retainedOldest h.latestSequence ≤ s at hs
    change s ≤ h.latestSequence at hsl
    by_cases heq : s = h.latestSequence
    · subst s
      have hi : h.latestSequence - 1 = ys.length := by omega
      simp [installed, checkpointAt, hi, List.getElem?_append]
    · have hneq : (s - 1) % ringCapacity ≠ (h.latestSequence - 1) % ringCapacity := by
        intro he
        have he' := ring_index_injective s h.latestSequence h.latestSequence
          hs hsl ho.2 (Nat.le_refl _) he
        exact heq he'
      have hi : s - 1 < ys.length := by omega
      have hcell := hr.2.2.2.2.2 s hs hsl
      rw [List.getElem?_append_left hi] at hcell ⊢
      simpa [installed, checkpointAt, hneq] using hcell

/-- Full successful-write conjunct, not merely preservation of current D. -/
theorem write_preserves (h : History) (xs : List Checkpoint) (now v : Nat) (next : History)
    (hr : RingRepresentation h xs) (ht : lastTimestamp xs ≤ now)
    (hv : v ≥ current h) (hw : write h v now = .ok next) :
    RingRepresentation next (ghostWrite xs ⟨now, v⟩) ∧ current next = v := by
  have hshape := write_shape h xs now v next hr ht hv hw
  rcases hshape with ⟨hnow, hval, hseq, hnext⟩
  cases hlast : xs.getLast? with
  | none =>
    have hxs : xs = [] := List.getLast?_eq_none_iff.mp hlast
    subst xs
    have hz : h.latestSequence = 0 := by simpa using hr.1
    have hn : nextSequence h [] now = 1 := by simp [nextSequence, hz]
    rw [hn] at hnext
    subst next
    exact ⟨by simpa [ghostWrite] using install_empty h ⟨now, v⟩ hr hnow hval,
      installed_current h 1 ⟨now, v⟩ (by omega)⟩
  | some old =>
    obtain ⟨ys, hxs⟩ := List.getLast?_eq_some_iff.mp hlast
    have hlen : h.latestSequence = ys.length + 1 := by simpa [hxs] using hr.1
    have hn : 0 < h.latestSequence := by omega
    have htimestamp : lastTimestamp xs = old.timestamp := by simp [lastTimestamp, hlast]
    have hcurrent : current h = old.cumulative := by
      have htlast := last_logical (by have := hr.1; omega : 0 < xs.length)
      rw [← hr.1] at htlast
      rw [current_logical hr hn, ← htlast.2]
      simp [lastDeposit, hlast]
    have hmon : old.cumulative ≤ v := by omega
    by_cases heq : now = old.timestamp
    · have hsn : nextSequence h xs now = h.latestSequence := by
        simp [nextSequence, Nat.ne_of_gt hn, htimestamp, heq]
      rw [hsn] at hnext
      subst next
      have hghost : ghostWrite xs ⟨now, v⟩ = ys ++ [⟨now, v⟩] := by
        rw [hxs, ghostWrite_last]
        simp [heq]
      rw [hghost]
      exact ⟨install_replace h ys old ⟨now, v⟩ (by simpa [hxs] using hr)
        (by simpa using heq.symm) hmon hnow hval,
        installed_current h h.latestSequence ⟨now, v⟩ hn⟩
    · have hlt : old.timestamp < now := by omega
      have hsn : nextSequence h xs now = h.latestSequence + 1 := by
        simp [nextSequence, Nat.ne_of_gt hn, htimestamp, heq]
      rw [hsn] at hnext hseq
      subst next
      have hghost : ghostWrite xs ⟨now, v⟩ = xs ++ [⟨now, v⟩] := by
        rw [hxs, ghostWrite_last]
        simp [Ne.symm heq]
      rw [hghost]
      exact ⟨install_append h xs old ⟨now, v⟩ hr hlast hlt hmon hnow hval hseq,
        installed_current h (h.latestSequence + 1) ⟨now, v⟩ (by omega)⟩

/-- Current cumulative amount is the last full ghost checkpoint, including empty history. -/
theorem current_eq_lastDeposit (h : History) (xs : List Checkpoint)
    (hr : RingRepresentation h xs) : current h = lastDeposit xs := by
  by_cases hz : h.latestSequence = 0
  · have hxs : xs = [] := List.length_eq_zero_iff.mp (by have := hr.1; omega)
    subst xs
    simp [current, hz, lastDeposit]
  · have hn : 0 < h.latestSequence := by omega
    rw [current_logical hr hn, hr.1]
    exact (last_logical (by have := hr.1; omega)).2.symm

/-- Complete theorem for all five exact-history specification conjuncts. -/
theorem exactHistoryCorrespondence : ExactHistoryCorrespondence := by
  refine ⟨referenceAt_exact, write_preserves, ring_index_injective,
    sequence_overflow, checkpoint_roundtrip⟩

-- Kernel dependency audit is recorded by both bounded gates.
#print axioms exactHistoryCorrespondence
#print axioms current_eq_lastDeposit

end HistoryProofs
end Benchmark.Cases.Kuru.WithdrawalLimit
