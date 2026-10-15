import Benchmark.Cases.Kuru.WithdrawalLimit.HistoryProofs
import Benchmark.Cases.Kuru.WithdrawalLimit.ArithmeticProofs
import Benchmark.Cases.Kuru.WithdrawalLimit.CoreProofs

namespace Benchmark.Cases.Kuru.WithdrawalLimit
namespace LimiterProofs

-- Exact limiter proofs on the semantic model; no source/bytecode refinement.
theorem bind_ok {α β : Type} {m : Checked α} {f : α → Checked β} {v : β}
    (h : (m >>= f) = .ok v) : ∃ x, m = .ok x ∧ f x = .ok v := by
  cases hm : m with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok x => exact ⟨x, rfl, by simpa [hm, Bind.bind, Except.bind] using h⟩

theorem ok_bind {α β : Type} (a : α) (f : α → Checked β) :
    ((.ok a : Checked α) >>= f) = f a := rfl

theorem ensure_true (p : Prop) [Decidable p] (e : Error) (h : p) : ensure p e = .ok () :=
  if_pos h

theorem ensure_ok {α : Type} {p : Prop} [Decidable p] {e : Error}
    {m : Checked α} {v : α} (h : (do ensure p e; m) = .ok v) : p ∧ m = .ok v := by
  by_cases hp : p
  · exact ⟨hp, by simpa [ensure, hp, Bind.bind, Except.bind] using h⟩
  · simp [ensure, hp, Bind.bind, Except.bind] at h

theorem add_ok {bits a b v : Nat} (h : checkedAdd bits a b = .ok v) :
    v = a + b ∧ a + b < width bits := by
  obtain ⟨hb, hv⟩ := ensure_ok (show (do ensure (a+b < width bits) .arithmetic; pure (a+b)) = .ok v from h)
  exact ⟨(Except.ok.inj hv).symm, hb⟩

theorem add_of_lt (bits a b : Nat) (h : a+b < width bits) :
    checkedAdd bits a b = .ok (a+b) := by
  simp only [checkedAdd, ensure, if_pos h, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem sub_ok {a b v : Nat} (h : checkedSub a b = .ok v) :
    v = a - b ∧ b ≤ a := by
  obtain ⟨hb, hv⟩ := ensure_ok (show (do ensure (b ≤ a) .arithmetic; pure (a-b)) = .ok v from h)
  exact ⟨(Except.ok.inj hv).symm, hb⟩

theorem timestamp_ok {now t : Nat} (h : timestamp now = .ok t) :
    t = now ∧ now < width 64 := by
  unfold timestamp at h
  obtain ⟨hb, hv⟩ := ensure_ok h
  have hp : 0 < width 64 := by norm_num [width]
  have ht : now < width 64 := by unfold maxWord at hb; omega
  rw [arithmetic_castWord_of_lt ht] at hv
  exact ⟨(Except.ok.inj hv).symm, ht⟩

theorem timestamp_of_lt {now : Nat} (ht : now < width 64) : timestamp now = .ok now := by
  have hb : now ≤ maxWord 64 := by unfold maxWord; omega
  simp [timestamp, ensure, hb, arithmetic_castWord_of_lt ht]

theorem current_reference (h : History) (reference : Nat) :
    current { h with referenceSequence := reference } = current h := rfl

theorem ring_reference {h : History} {xs : List Checkpoint} {reference : Nat}
    (hr : RingRepresentation h xs) (hb : reference ≤ h.latestSequence) :
    RingRepresentation { h with referenceSequence := reference } xs := by
  exact ⟨hr.1, hr.2.1, hb, hr.2.2.2⟩

private def scanStep (cutoff : Nat) (acc : (Nat × Nat) × Nat) (cp : Checkpoint) :=
  ((if cp.timestamp ≤ cutoff then (cp.cumulative, acc.2) else acc.1), acc.2 + 1)

private theorem fold_bounds (xs : List Checkpoint) (cutoff D : Nat) (acc : (Nat × Nat) × Nat)
    (ha : acc.1.1 ≤ D) (hs : acc.1.2 ≤ acc.2 - 1) (hk : 0 < acc.2)
    (hxs : ∀ cp ∈ xs, cp.cumulative ≤ D) :
    (xs.foldl (scanStep cutoff) acc).1.1 ≤ D ∧
    (xs.foldl (scanStep cutoff) acc).1.2 ≤ acc.2 + xs.length - 1 := by
  induction xs generalizing acc with
  | nil => simpa using And.intro ha hs
  | cons cp xs ih =>
    have hcp := hxs cp (by simp)
    have htail : ∀ q ∈ xs, q.cumulative ≤ D := by intro q hq; exact hxs q (by simp [hq])
    have hval : (scanStep cutoff acc cp).1.1 ≤ D := by
      simp only [scanStep]; split <;> assumption
    have hseq : (scanStep cutoff acc cp).1.2 ≤ (scanStep cutoff acc cp).2 - 1 := by
      simp only [scanStep]; split <;> omega
    have hpos : 0 < (scanStep cutoff acc cp).2 := by simp [scanStep]
    have hi := ih (scanStep cutoff acc cp) hval hseq hpos htail
    have heq : (scanStep cutoff acc cp).2 + xs.length - 1 = acc.2 + (cp :: xs).length - 1 := by
      simp only [scanStep, List.length_cons]; omega
    exact ⟨hi.1, by simpa only [heq, List.foldl_cons] using hi.2⟩

theorem cumulative_le_last {xs : List Checkpoint} (hc : chronological xs) :
    ∀ cp ∈ xs, cp.cumulative ≤ lastDeposit xs := by
  cases hl : xs.getLast? with
  | none => have hx := List.getLast?_eq_none_iff.mp hl; subst xs; simp
  | some old =>
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    have hp := List.pairwise_append.mp hc
    intro cp hcp
    simp only [List.mem_append, List.mem_singleton] at hcp
    rcases hcp with hcp | rfl
    · have ho := hp.2.2 cp hcp old (by simp)
      simpa [lastDeposit] using ho.2
    · simp [lastDeposit]

theorem expired_bounds {h : History} {xs : List Checkpoint} (hr : RingRepresentation h xs)
    (now : Nat) : (expiredReference xs now).1 ≤ current h ∧
      (expiredReference xs now).2 ≤ h.latestSequence := by
  rw [HistoryProofs.current_eq_lastDeposit h xs hr, hr.1]
  unfold expiredReference
  split
  · simp
  · have hb := fold_bounds xs (now-window) (lastDeposit xs) ((0,0),1)
        (by exact Nat.zero_le _) (by decide) (by decide) (cumulative_le_last hr.2.2.2.1)
    change (xs.foldl (scanStep (now-window)) ((0,0),1)).1.1 ≤ lastDeposit xs ∧
      (xs.foldl (scanStep (now-window)) ((0,0),1)).1.2 ≤ xs.length
    exact ⟨hb.1, by simpa only [Prod.snd, Nat.one_add, Nat.succ_sub_one] using hb.2⟩

theorem beginFlow_started (s next : Limiter) (now : Nat)
    (hf : s.transient.flowStarted = true) (h : beginFlow s now = .ok next) : next = s := by
  simpa [beginFlow, hf, Pure.pure, Except.pure] using h.symm

theorem beginFlow_first (h : History) (xs : List Checkpoint) (now : Nat) (s next : Limiter)
    (hr : RingRepresentation h xs) (ht : lastTimestamp xs ≤ now) (hw : now < width 64)
    (hh : s.persistent.history = h) (hf : s.transient.flowStarted = false)
    (hb : beginFlow s now = .ok next) :
    next.transient.expired = (expiredReference xs now).1 ∧ next.transient.flowStarted = true ∧
    next.persistent.history.referenceSequence = (expiredReference xs now).2 := by
  have href := HistoryProofs.referenceAt_exact h xs now hr ht hw
  have heq : (if h.referenceSequence ≠ (expiredReference xs now).2
      then (expiredReference xs now).2 else h.referenceSequence) = (expiredReference xs now).2 := by
    split <;> simp_all
  unfold beginFlow at hb
  simp only [hf, Bool.false_eq_true, ↓reduceIte] at hb
  rw [timestamp_of_lt hw] at hb
  simp only [Bind.bind, Except.bind] at hb
  rw [hh, href] at hb
  simp only [Bind.bind, Except.bind] at hb
  have hv := Except.ok.inj hb
  rw [← hv]
  exact ⟨rfl, rfl, heq⟩

theorem snapshotPrice_success (s : Limiter) (fetch : PriceFetch) (token : Key)
    (quote : Nat) (next : Limiter) (h : snapshotPrice s fetch token = .ok (quote,next)) :
    next.transient.prices token = quote ∧ SamePersistent s next ∧
    next.transient.flowStarted = s.transient.flowStarted ∧ next.transient.expired = s.transient.expired ∧
    (∀ k, k ≠ token → next.transient.prices k = s.transient.prices k) := by
  unfold snapshotPrice at h
  obtain ⟨q, _, h⟩ := bind_ok h
  have hp := Except.ok.inj h
  have hq : q = quote := congrArg Prod.fst hp
  have hn := congrArg Prod.snd hp
  subst q
  simp only [Prod.fst, Prod.snd] at hn
  rw [← hn]
  refine ⟨by simp, rfl, rfl, rfl, ?_⟩
  intro k hk
  simp only [if_neg hk]

theorem price_cached (s : Limiter) (token : Key) (cached : Nat) (fetch : PriceFetch)
    (hc : s.transient.prices token = cached) (hn : cached ≠ 0) :
    price s fetch token = .ok (castWord 128 cached) := by simp [price, hc, hn]

-- Explicit local invariant for snapshot closure, to be derived by WriterProofs.
-- It does not assert reachability or assume any target Group Prop.
def CacheExact (s : Limiter) (xs : List Checkpoint) (now : Nat) : Prop :=
  s.transient.flowStarted = true → s.transient.expired = (expiredReference xs now).1

def FlowTime (s : Limiter) (now : Nat) : Prop :=
  s.transient.flowStarted = true → now < width 64

theorem funding_mono_time {s : Persistent} {xs : List Checkpoint} {now later : Nat}
    (hr : FundingRepresentation s xs now) (ht : now ≤ later) : FundingRepresentation s xs later := by
  rcases hr with ⟨hh, hcur, hS, hD, hcap, hrate, ha, haw, htw, ht0, hlast⟩
  exact ⟨hh,hcur,hS,hD,hcap,hrate,ha,haw,htw,by omega,by omega⟩

theorem availableDrip_total {s : Persistent} {xs : List Checkpoint} {now : Nat}
    (hr : FundingRepresentation s xs now) (ht : now < width 64) :
    availableDrip s now = .ok (min (s.drip.available + (now-s.drip.updatedAt)*s.rateUsd18*usdScale)
      (s.capacityUsd18*usdScale)) := by
  rcases hr with ⟨_,_,_,_,_,hR,_,hA,_,hT,_⟩
  have htmax : now - s.drip.updatedAt ≤ maxWord 64 := by unfold maxWord; omega
  have hrmax : s.rateUsd18 ≤ maxWord 128 := by unfold maxWord; omega
  have hamax : s.drip.available ≤ maxWord 192 := by unfold maxWord; omega
  have hsum : s.drip.available + (now-s.drip.updatedAt)*s.rateUsd18*usdScale < width 256 :=
    lt_of_le_of_lt (Nat.add_le_add hamax
      (Nat.mul_le_mul_right usdScale (Nat.mul_le_mul htmax hrmax))) arithmetic_refill_max_bound
  have href : (now-s.drip.updatedAt)*s.rateUsd18*usdScale < width 256 := by omega
  have hsub : checkedSub now s.drip.updatedAt = .ok (now-s.drip.updatedAt) := by
    simp only [checkedSub, ensure, if_pos hT, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hadd := add_of_lt 256 s.drip.available ((now-s.drip.updatedAt)*s.rateUsd18*usdScale) hsum
  unfold availableDrip
  rw [hsub, ok_bind]
  dsimp only
  rw [ensure_true _ _ href, ok_bind, hadd, ok_bind]
  rfl

theorem initialize_success (now capacity rate : Nat) (next : Limiter)
    (h : initializeLimiter now capacity rate = .ok next) :
    FundingRepresentation next.persistent [] now ∧ next.transient.flowStarted = false ∧
    current next.persistent.history = 0 ∧ next.persistent.cursor = 0 ∧
    next.persistent.history.latestSequence = 0 ∧ next.persistent.drip.available = capacity*usdScale := by
  unfold initializeLimiter at h
  obtain ⟨hc,h0⟩ := ensure_ok h
  obtain ⟨t,ht,h1⟩ := bind_ok h0
  obtain ⟨heq,hw⟩ := timestamp_ok ht
  have hfit := arithmetic_capacity_mul_lt hc.1
  have hn := Except.ok.inj h1
  rw [← hn, heq]
  rw [arithmetic_castWord_of_lt hfit]
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨?_,rfl,by simp [current],by simp [current]; norm_num [width],hc.1,hc.2,
    Nat.le_refl _,hfit,hw,Nat.le_refl _,by simp [lastTimestamp]⟩
  refine ⟨rfl,by norm_num [width],by simp,by simp [chronological],by simp,?_⟩
  intro seq hlo hhi
  simp [retainedOldest, ringCapacity, window] at hlo
  change seq ≤ 0 at hhi
  omega

structure LimiterSafe (s : Limiter) (xs : List Checkpoint) (now : Nat) : Prop where
  funding : FundingRepresentation s.persistent xs now
  cache : CacheExact s xs now
  time : FlowTime s now

theorem safe_initialize (now capacity rate : Nat) (s : Limiter)
    (h : initializeLimiter now capacity rate = .ok s) : LimiterSafe s [] now := by
  have hi := initialize_success now capacity rate s h
  refine ⟨hi.1, ?_, ?_⟩
  · intro ht; simp only [hi.2.1, Bool.false_eq_true] at ht
  · intro ht; simp only [hi.2.1, Bool.false_eq_true] at ht

theorem safe_snapshot (s : Limiter) (xs : List Checkpoint) (now : Nat)
    (fetch : PriceFetch) (token : Key) (quote : Nat) (next : Limiter)
    (hs : LimiterSafe s xs now) (h : snapshotPrice s fetch token = .ok (quote,next)) :
    LimiterSafe next xs now := by
  obtain ⟨_, hp, hf, he, _⟩ := snapshotPrice_success s fetch token quote next h
  refine ⟨?_, ?_, ?_⟩
  · rw [show next.persistent = s.persistent from hp]; exact hs.funding
  · intro hflow
    rw [he]
    exact hs.cache (hf ▸ hflow)
  · intro hflow
    exact hs.time (hf ▸ hflow)

theorem safe_beginFlow (s : Limiter) (xs : List Checkpoint) (now : Nat) (next : Limiter)
    (hs : LimiterSafe s xs now) (h : beginFlow s now = .ok next) : LimiterSafe next xs now := by
  cases hf : s.transient.flowStarted with
  | true => rw [beginFlow_started s next now hf h]; exact hs
  | false =>
    have h0 := h
    unfold beginFlow at h0
    simp only [hf, Bool.false_eq_true, if_false, Bind.bind, Except.bind, Pure.pure, Except.pure] at h0
    obtain ⟨t, ht, h0⟩ := bind_ok h0
    obtain ⟨heqt, hw⟩ := timestamp_ok ht
    have href := HistoryProofs.referenceAt_exact s.persistent.history xs now hs.funding.1 hs.funding.2.2.2.2.2.2.2.2.2.2 hw
    rw [heqt, href] at h0
    dsimp only at h0
    have heq : (if s.persistent.history.referenceSequence ≠ (expiredReference xs now).2
        then (expiredReference xs now).2 else s.persistent.history.referenceSequence) = (expiredReference xs now).2 := by
      split <;> simp_all
    have hv := Except.ok.inj h0
    rw [← hv]
    simp only [heq]
    refine ⟨?_, fun _ => rfl, fun _ => hw⟩
    rcases hs.funding with ⟨hr,hD,hS,hDw,hC,hR,hA,hAw,hTw,hT,hLast⟩
    have hb := expired_bounds hr now
    exact ⟨ring_reference hr hb.2, hD, hS, hDw, hC,hR,hA,hAw,hTw,hT,hLast⟩

theorem safe_approved (s : Limiter) (xs : List Checkpoint) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (next : Limiter) (hs : LimiterSafe s xs now)
    (h : checkApprovedWithdrawal s now fetch caller core token = .ok next) : LimiterSafe next xs now := by
  unfold checkApprovedWithdrawal at h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨started,hstarted,h⟩ := bind_ok h
  obtain ⟨quote,snapped,hp,h⟩ := core_bind_pair_ok h
  rw [← Except.ok.inj h]
  exact safe_snapshot started xs now fetch token quote snapped (safe_beginFlow s xs now started hs hstarted) hp

theorem safe_configureSource (s : Limiter) (xs : List Checkpoint) (now : Nat)
    (caller governance token source : Key) (code : Key → Bool) (next : Limiter)
    (hs : LimiterSafe s xs now)
    (h : setPriceSource s caller governance token source code = .ok next) : LimiterSafe next xs now := by
  unfold setPriceSource at h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨_,h⟩ := ensure_ok h
  rw [← Except.ok.inj h]
  exact ⟨hs.funding, hs.cache, hs.time⟩

theorem safe_configureDrip (s : Limiter) (xs : List Checkpoint) (now capacity rate : Nat)
    (caller governance : Key) (next : Limiter) (hs : LimiterSafe s xs now)
    (h : setDripConfig s now caller governance capacity rate = .ok next) : LimiterSafe next xs now := by
  unfold setDripConfig at h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨hf,h⟩ := ensure_ok h
  obtain ⟨hc,h⟩ := ensure_ok h
  obtain ⟨t,ht,h⟩ := bind_ok h
  obtain ⟨heqt,hw⟩ := timestamp_ok ht
  obtain ⟨A,hA,h⟩ := bind_ok h
  have hfit : min A (capacity*usdScale) < width 192 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) (arithmetic_capacity_mul_lt hc.1)
  rw [← Except.ok.inj h, heqt, arithmetic_castWord_of_lt hfit]
  rcases hs.funding with ⟨hr,hD,hS,hDw,hC,hR,ha,haw,htw,ht0,hLast⟩
  refine ⟨⟨hr,hD,hS,hDw,hc.1,hc.2,Nat.min_le_right _ _,hfit,hw,Nat.le_refl _,hLast⟩, ?_, ?_⟩
  · intro hflow; simp only [hf, Bool.false_eq_true] at hflow
  · intro hflow; simp only [hf, Bool.false_eq_true] at hflow

structure FundingFrame (before after : Limiter) : Prop where
  total : current after.persistent.history = current before.persistent.history
  cursor : after.persistent.cursor = before.persistent.cursor
  drip : after.persistent.drip = before.persistent.drip
  capacity : after.persistent.capacityUsd18 = before.persistent.capacityUsd18
  rate : after.persistent.rateUsd18 = before.persistent.rateUsd18

theorem beginFlow_frame (s next : Limiter) (now : Nat) (h : beginFlow s now = .ok next) :
    FundingFrame s next := by
  unfold beginFlow at h
  split at h
  · rw [← Except.ok.inj h]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨t,_,h⟩ := bind_ok h
    obtain ⟨p,_,h⟩ := bind_ok h
    rcases p with ⟨expired,sequence⟩
    rw [← Except.ok.inj h]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem frame_available {s next : Limiter} (hf : FundingFrame s next) (now : Nat) :
    availableDrip next.persistent now = availableDrip s.persistent now := by
  unfold availableDrip
  rw [hf.drip,hf.capacity,hf.rate]

theorem frame_trans {a b c : Limiter} (hab : FundingFrame a b) (hbc : FundingFrame b c) :
    FundingFrame a c :=
  ⟨hbc.total.trans hab.total,hbc.cursor.trans hab.cursor,hbc.drip.trans hab.drip,
    hbc.capacity.trans hab.capacity,hbc.rate.trans hab.rate⟩

theorem snapshot_frame (s : Limiter) (fetch : PriceFetch) (token : Key) (q : Nat) (next : Limiter)
    (h : snapshotPrice s fetch token = .ok (q,next)) : FundingFrame s next := by
  have hp := (snapshotPrice_success s fetch token q next h).2.1
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rw [show next.persistent = s.persistent from hp]

theorem consumption_frame {a b after : Limiter} {now E : Nat} {f : Funding}
    (hf : FundingFrame a b) (h : OrdinaryConsumption b after now E f) : OrdinaryConsumption a after now E f := by
  unfold OrdinaryConsumption at h ⊢
  simpa only [hf.total,hf.cursor,hf.drip,frame_available hf] using h

theorem sub_of_le (a b : Nat) (h : b ≤ a) : checkedSub a b = .ok (a-b) := by
  simp only [checkedSub,ensure,if_pos h,Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem width192_le256 : width 192 ≤ width 256 := by norm_num [width]

theorem available_at_timestamp (s : Persistent) (now : Nat)
    (ht : s.drip.updatedAt = now) (ha : s.drip.available ≤ s.capacityUsd18*usdScale)
    (hw : s.drip.available < width 256) : availableDrip s now = .ok s.drip.available := by
  unfold availableDrip
  rw [ht,sub_of_le now now (Nat.le_refl _),ok_bind]
  simp only [Nat.sub_self, Nat.zero_mul]
  rw [ensure_true _ _ (by norm_num [width]),ok_bind]
  rw [add_of_lt 256 s.drip.available 0 (by simpa only [Nat.add_zero] using hw),ok_bind]
  simp only [Nat.add_zero,Nat.min_eq_left ha,Pure.pure,Except.pure]

theorem ghost_last (ys : List Checkpoint) (old cp : Checkpoint) :
    ghostWrite (ys ++ [old]) cp =
      if old.timestamp = cp.timestamp then ys ++ [cp] else (ys ++ [old]) ++ [cp] := by
  induction ys with
  | nil => simp [ghostWrite]
  | cons x ys ih =>
    cases ys with
    | nil => split_ifs <;> simp_all [ghostWrite]
    | cons y ys =>
      by_cases heq : old.timestamp = cp.timestamp <;>
        simpa [ghostWrite,List.cons_append,heq] using congrArg (List.cons x) ih

theorem ghost_lastTimestamp (xs : List Checkpoint) (now v : Nat) :
    lastTimestamp (ghostWrite xs ⟨now,v⟩) = now := by
  cases hx : xs.getLast? with
  | none =>
    have hnil := List.getLast?_eq_none_iff.mp hx
    subst xs
    rfl
  | some old =>
    obtain ⟨ys,rfl⟩ := List.getLast?_eq_some_iff.mp hx
    rw [ghost_last]
    split <;> simp [lastTimestamp]

theorem ghost_expired (xs : List Checkpoint) (now v : Nat) :
    (expiredReference (ghostWrite xs ⟨now,v⟩) now).1 = (expiredReference xs now).1 := by
  by_cases hn : now < window
  · simp only [expiredReference,hn,if_true]
  · have hcut : now - window < now := by unfold window at hn ⊢; omega
    cases hx : xs.getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp hx
      subst xs
      simp [ghostWrite,expiredReference,hn,show ¬now ≤ now-window by omega]
    | some old =>
      obtain ⟨ys,rfl⟩ := List.getLast?_eq_some_iff.mp hx
      rw [ghost_last]
      split
      · rename_i heq
        simp only [Checkpoint.mk.injEq] at heq
        simp [expiredReference,hn,List.foldl_append,show ¬now ≤ now-window by omega,heq]
      · simp [expiredReference,hn,List.foldl_append,show ¬now ≤ now-window by omega]

def depositGhost (xs : List Checkpoint) (now D v : Nat) : List Checkpoint :=
  if v ≠ 0 then ghostWrite xs ⟨now,D+v⟩ else xs

theorem deposit_exact (s : Limiter) (xs : List Checkpoint) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (amount decimals vout : Nat) (next : Limiter)
    (hs : LimiterSafe s xs now)
    (h : recordDeposit s now fetch caller core token amount decimals = .ok (vout,next)) :
    LimiterSafe next (depositGhost xs now (current s.persistent.history) vout) now ∧
    current next.persistent.history = current s.persistent.history + vout ∧
    next.persistent.cursor = s.persistent.cursor ∧ next.persistent.drip = s.persistent.drip ∧
    next.transient.flowStarted = true := by
  unfold recordDeposit at h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨started,hstarted,h⟩ := bind_ok h
  obtain ⟨quote,snapped,hp,h⟩ := core_bind_pair_ok h
  have hstartSafe := safe_beginFlow s xs now started hs hstarted
  have hsafe := safe_snapshot started xs now fetch token quote snapped hstartSafe hp
  have hframe := frame_trans (beginFlow_frame s started now hstarted) (snapshot_frame started fetch token quote snapped hp)
  have hflow : snapped.transient.flowStarted = true :=
    (snapshotPrice_success started fetch token quote snapped hp).2.2.1.trans (core_beginFlow_pools s now started hstarted).2
  obtain ⟨v,_,h⟩ := bind_ok h
  obtain ⟨n,hn,h⟩ := bind_ok h
  obtain ⟨hnw,h⟩ := ensure_ok h
  have h0 : ((if v ≠ 0 then write snapped.persistent.history n now else pure snapped.persistent.history) >>=
      fun hist => pure (v, { snapped with persistent := { snapped.persistent with history := hist } })) = .ok (vout,next) := by
    by_cases hv : v ≠ 0 <;>
      simpa [hv,Bind.bind,core_except_bind_assoc,core_except_ok_bind,Pure.pure,Except.pure] using h
  obtain ⟨hist,hh,h⟩ := bind_ok h0
  have hnEq := (add_ok hn).1
  have hnLt : n < width 192 := by
    have hwpos : 0 < width 192 := by norm_num [width]
    unfold maxWord at hnw
    omega
  let ys := depositGhost xs now (current snapped.persistent.history) v
  have hhist : RingRepresentation hist ys ∧ current hist = n := by
    by_cases hv : v ≠ 0
    · rw [if_pos hv] at hh
      simpa only [ys,depositGhost,if_pos hv,hnEq] using
        HistoryProofs.write_preserves snapped.persistent.history xs now n hist hsafe.funding.1
          hsafe.funding.2.2.2.2.2.2.2.2.2.2 (by omega) hh
    · rw [if_neg hv] at hh
      have heq := Except.ok.inj hh
      rw [← heq]
      have hz : v = 0 := by omega
      simpa [ys,depositGhost,hnEq,hz] using
        And.intro hsafe.funding.1 (Eq.refl (current snapped.persistent.history))
  have heq := Except.ok.inj h
  have heqv := congrArg Prod.fst heq
  have heqs := congrArg Prod.snd heq
  simp only [Prod.fst,Prod.snd] at heqv heqs
  rw [← heqs,← heqv]
  have hys : depositGhost xs now (current s.persistent.history) v = ys := by
    simp only [ys,hframe.total]
  rw [hys]
  refine ⟨?_,?_,hframe.cursor,hframe.drip,hflow⟩
  · rcases hsafe.funding with ⟨hr,hD,hS,hDw,hC,hR,hA,hAw,hTw,hT,hLast⟩
    refine ⟨?_,?_,?_⟩
    · refine ⟨hhist.1, HistoryProofs.current_eq_lastDeposit hist ys hhist.1, ?_, ?_,hC,hR,hA,hAw,hTw,hT,?_⟩
      · change snapped.persistent.cursor ≤ current hist
        rw [hhist.2]; omega
      · change current hist < width 192
        rw [hhist.2]; exact hnLt
      · by_cases hv : v ≠ 0
        · simp only [ys,depositGhost,if_pos hv,ghost_lastTimestamp]; omega
        · simpa only [ys,depositGhost,if_neg hv] using hLast
    · intro _
      change snapped.transient.expired = (expiredReference ys now).1
      have he : (expiredReference ys now).1 = (expiredReference xs now).1 := by
        by_cases hv : v ≠ 0
        · simp only [ys,depositGhost,if_pos hv,ghost_expired]
        · simp only [ys,depositGhost,if_neg hv]
      rw [he]
      exact hsafe.cache hflow
    · intro _; exact hsafe.time hflow
  · change current hist = current s.persistent.history + v
    rw [hhist.2,hnEq,hframe.total]

theorem consume_credit (D S E v A : Nat) (hS : S ≤ D) (hE : E ≤ D)
    (hR : v - min v (D-max S E) ≤ A) :
    max S E + min v (D-max S E) ≤ D ∧
    (if min v (D-max S E) ≠ 0 then max S E + min v (D-max S E) else S) ≤ D ∧
    D - max E (if min v (D-max S E) ≠ 0 then max S E + min v (D-max S E) else S) =
      (D-max S E) - min v (D-max S E) ∧
    v ≤ (D-max S E)+A := by
  split_ifs <;> omega

theorem withdrawal_exact (s : Limiter) (xs : List Checkpoint) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (amount decimals : Nat) (fout : Funding) (next : Limiter)
    (hs : LimiterSafe s xs now)
    (h : recordWithdrawal s now fetch caller core token amount decimals = .ok (fout,next)) :
    LimiterSafe next xs now ∧ OrdinaryConsumption s next now (expiredReference xs now).1 fout ∧
    next.transient.flowStarted = true := by
  unfold recordWithdrawal at h
  obtain ⟨_,h⟩ := ensure_ok h
  obtain ⟨started,hstarted,h⟩ := bind_ok h
  obtain ⟨quote,snapped,hp,h⟩ := core_bind_pair_ok h
  have hstartSafe := safe_beginFlow s xs now started hs hstarted
  have hsafe := safe_snapshot started xs now fetch token quote snapped hstartSafe hp
  have hframe := frame_trans (beginFlow_frame s started now hstarted) (snapshot_frame started fetch token quote snapped hp)
  have hflow : snapped.transient.flowStarted = true :=
    (snapshotPrice_success started fetch token quote snapped hp).2.2.1.trans (core_beginFlow_pools s now started hstarted).2
  have htime := hsafe.time hflow
  have hexp := hsafe.cache hflow
  obtain ⟨v,_,h⟩ := bind_ok h
  obtain ⟨credit,hcredit,h⟩ := bind_ok h
  have hcreditEq := (sub_ok hcredit).1
  let cursor := creditCursor snapped.persistent snapped.transient.expired
  let U := min v credit
  let R := v-U
  have h0 : ((if R ≠ 0 then do
      let t ← timestamp now
      let available ← availableDrip snapped.persistent t
      ensure (R ≤ available) .limit
      pure (DripState.mk (castWord 192 (available-R)) t)
      else pure snapped.persistent.drip) >>= fun drip =>
    ((if U ≠ 0 then do
      let sum ← checkedAdd 256 cursor U
      pure (castWord 192 sum)
      else pure snapped.persistent.cursor) >>= fun nextCursor =>
    pure (Funding.mk v cursor credit U R,
      { snapped with persistent := { snapped.persistent with cursor := nextCursor, drip := drip } }))) = .ok (fout,next) := by
    by_cases hr : R ≠ 0 <;> by_cases hu : U ≠ 0
    all_goals
      dsimp only [R,U,cursor] at hr hu ⊢
      simpa [hr,hu,Bind.bind,core_except_bind_assoc,core_except_ok_bind,Pure.pure,Except.pure] using h
  obtain ⟨drip,hdrip,h0⟩ := bind_ok h0
  obtain ⟨nextCursor,hcursor,h0⟩ := bind_ok h0
  let A := min (snapped.persistent.drip.available +
    (now-snapped.persistent.drip.updatedAt)*snapped.persistent.rateUsd18*usdScale)
    (snapped.persistent.capacityUsd18*usdScale)
  have hAvail : availableDrip snapped.persistent now = .ok A := availableDrip_total hsafe.funding htime
  have hAcap : A ≤ snapped.persistent.capacityUsd18*usdScale := Nat.min_le_right _ _
  have hAw : A < width 192 := lt_of_le_of_lt hAcap (arithmetic_capacity_mul_lt hsafe.funding.2.2.2.2.1)
  have hdr : R ≤ A ∧ drip = (if R ≠ 0 then ⟨A-R,now⟩ else snapped.persistent.drip) := by
    by_cases hr : R ≠ 0
    · rw [if_pos hr] at hdrip
      obtain ⟨t,ht,hdrip⟩ := bind_ok hdrip
      obtain ⟨heqt,_⟩ := timestamp_ok ht
      obtain ⟨a,ha,hdrip⟩ := bind_ok hdrip
      rw [heqt] at ha
      have heqa : a = A := Except.ok.inj (ha.symm.trans hAvail)
      obtain ⟨hbound,hdrip⟩ := ensure_ok hdrip
      have hcast : castWord 192 (A-R) = A-R :=
        arithmetic_castWord_of_lt (lt_of_le_of_lt (Nat.sub_le A R) hAw)
      have hd := (Except.ok.inj hdrip).symm
      refine ⟨by omega, ?_⟩
      simpa only [if_pos hr,heqa,heqt,hcast] using hd
    · rw [if_neg hr] at hdrip
      have hz : R = 0 := by omega
      exact ⟨by omega, by simpa only [if_neg hr] using (Except.ok.inj hdrip).symm⟩
  have hcreditShape : credit = current snapped.persistent.history - max snapped.persistent.cursor (expiredReference xs now).1 := by
    simpa only [creditCursor,hexp] using hcreditEq
  have hbounds := consume_credit (current snapped.persistent.history) snapped.persistent.cursor
    (expiredReference xs now).1 v A hsafe.funding.2.2.1 (expired_bounds hsafe.funding.1 now).1
    (by simpa only [R,U,hcreditShape] using hdr.1)
  have hc : nextCursor = (if U ≠ 0 then cursor+U else snapped.persistent.cursor) := by
    by_cases hu : U ≠ 0
    · rw [if_pos hu] at hcursor
      obtain ⟨sum,hsum,hcursor⟩ := bind_ok hcursor
      have heqsum := (add_ok hsum).1
      have hcast : castWord 192 sum = cursor+U := by
        rw [heqsum]
        apply arithmetic_castWord_of_lt
        have hw := hsafe.funding.2.2.2.1
        have hb := hbounds.1
        simpa only [cursor,creditCursor,hexp,U,hcreditShape] using lt_of_le_of_lt hb hw
      simpa only [if_pos hu,hcast] using (Except.ok.inj hcursor).symm
    · rw [if_neg hu] at hcursor
      simpa only [if_neg hu] using (Except.ok.inj hcursor).symm
  have hnewCursor : nextCursor ≤ current snapped.persistent.history := by
    simpa only [hc,cursor,creditCursor,hexp,U,hcreditShape] using hbounds.2.1
  have hnewCredit : current snapped.persistent.history - max (expiredReference xs now).1 nextCursor = credit-U := by
    simpa only [hc,cursor,creditCursor,hexp,U,hcreditShape] using hbounds.2.2.1
  have hdripBounds : drip.available ≤ snapped.persistent.capacityUsd18*usdScale ∧
      drip.available < width 192 ∧ drip.updatedAt < width 64 ∧ drip.updatedAt ≤ now := by
    rw [hdr.2]
    split
    · exact ⟨(Nat.sub_le A R).trans hAcap,lt_of_le_of_lt (Nat.sub_le A R) hAw,htime,Nat.le_refl _⟩
    · exact ⟨hsafe.funding.2.2.2.2.2.2.1,hsafe.funding.2.2.2.2.2.2.2.1,
        hsafe.funding.2.2.2.2.2.2.2.2.1,hsafe.funding.2.2.2.2.2.2.2.2.2.1⟩
  have hafterAvail : availableDrip { snapped.persistent with cursor := nextCursor, drip := drip } now = .ok (A-R) := by
    by_cases hr : R ≠ 0
    · have hdt : drip.updatedAt = now := by rw [hdr.2,if_pos hr]
      have hda : drip.available = A-R := by rw [hdr.2,if_pos hr]
      rw [← hda]
      exact available_at_timestamp _ now hdt hdripBounds.1 (lt_of_lt_of_le hdripBounds.2.1 width192_le256)
    · have hz : R = 0 := by omega
      have hd : drip = snapped.persistent.drip := by rw [hdr.2,if_neg hr]
      simpa only [availableDrip,hd,hz,Nat.sub_zero] using hAvail
  have heq := Except.ok.inj h0
  have hf := congrArg Prod.fst heq
  have hn := congrArg Prod.snd heq
  simp only [Prod.fst,Prod.snd] at hf hn
  rw [← hn,← hf]
  refine ⟨?_,consumption_frame hframe ?_,hflow⟩
  · rcases hsafe.funding with ⟨hh,hD,hS,hDw,hC,hR,hA,hAw,hTw,hT,hLast⟩
    exact ⟨⟨hh,hD,hnewCursor,hDw,hC,hR,hdripBounds.1,hdripBounds.2.1,
      hdripBounds.2.2.1,hdripBounds.2.2.2,hLast⟩,hsafe.cache,hsafe.time⟩
  · have hcs : cursor = max (expiredReference xs now).1 snapped.persistent.cursor := by
      simp only [cursor,creditCursor,hexp,Nat.max_comm]
    have hcr : credit = current snapped.persistent.history - max (expiredReference xs now).1 snapped.persistent.cursor := by
      simpa only [Nat.max_comm] using hcreditShape
    unfold OrdinaryConsumption
    dsimp only
    rw [← hcr,← hcs]
    refine ⟨A,hAvail,rfl,rfl,rfl,rfl,?_,rfl,hc,hdr.2,hnewCredit,hafterAvail⟩
    simpa only [hcreditShape] using hbounds.2.2.2

end LimiterProofs
end Benchmark.Cases.Kuru.WithdrawalLimit
