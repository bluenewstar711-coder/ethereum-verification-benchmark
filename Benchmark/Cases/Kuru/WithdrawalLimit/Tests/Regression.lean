/-
Finite semantic regressions ONLY, not proofs or source-equivalence evidence.
Large ring is a seeded functional layout, NOT an 86401-write reachability proof.
No unbounded batch traversal/decide. The proof modules will not import this file.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Contract

namespace Benchmark.Cases.Kuru.WithdrawalLimit

deriving instance DecidableEq for Except

private def testDeployment : Deployment :=
  { coreAddress := 100, limiterAddress := 200, limiterImmutableCore := 100
    coreImplementationCodeSize := 50, chainId := 1, codePresent := fun _ => true }

private def fixture (token : Key) : Checked World := do
  let d := testDeployment
  let roles : Key → Roles := fun _ => ⟨1, 1, 1⟩
  let w ← freshBoundPair d 100000 0 0 1 1 2 roles
  let w := environmentAction d w (.publish 20 (.ok 1))
  let w ← policyAction d w 1 (.configureSource token 20)
  policyAction d w 1 (.configureToken token true (.ok 18))

private def historyRegressions : Checked (List String) := do
  let h ← write {} 10 0
  let h ← write h 20 0
  let h ← write h 25 1
  ensure (h.latestSequence = 2 ∧ current h = 25) .history
  ensure (referenceAt h 86399 = .ok (0, 0)) .history
  ensure (referenceAt h 86400 = .ok (20, 1)) .history
  ensure (referenceAt h 86401 = .ok (25, 2)) .history
  let h : History := {
    latestSequence := 86404
    checkpoints := fun physical =>
      let logical := if physical + 1 ≥ 4 then physical + 1 else physical + 1 + ringCapacity
      ⟨logical, logical⟩ }
  ensure (referenceAt h 86404 = .ok (4, 4)) .history
  ensure (referenceAt { h with referenceSequence := 3 } 86404 = .ok (4, 4)) .history
  ensure (referenceAt { h with referenceSequence := 4 } 86404 = .ok (4, 4)) .history
  ensure (referenceAt { h with referenceSequence := 4 } 86405 = .ok (5, 5)) .history
  ensure (referenceAt h 172804 = .ok (86404, 86404)) .history
  let overflow : History := { latestSequence := maxWord 64, checkpoints := fun _ => ⟨1, 5⟩ }
  ensure ((write overflow 6 2).toOption.isNone = true) .history
  return ["history_same_second_and_zero", "history_exact_cutoff", "history_wrapped_cold_stale_cache",
    "history_cached_and_single_step", "history_long_idle", "history_checked_sequence_overflow"]

private def valuationRegressions : Checked (List String) := do
  ensure (value 1 1 77 false = .ok 0) .valueOverflow
  ensure (value 1 1 77 true = .ok 1) .valueOverflow
  ensure (value (10 ^ 77) 1 77 true = .ok (10 ^ 18)) .valueOverflow
  ensure (value 1 1 78 true = .error .config) .config
  ensure (value (maxWord 256) (maxWord 128) 18 true = .error .valueOverflow) .valueOverflow
  ensure (fullMulDiv (maxWord 256) (maxWord 128) 1 false = .error .arithmetic) .arithmetic
  return ["valuation_dust_floor_ceil", "valuation_77_decimals", "valuation_guard_and_full_product_overflow"]

private def ordinaryRegressions : Checked (List String) := do
  let d := testDeployment
  let w ← fixture 10
  let w ← deposit d w 1 (.owner 1) 10 20 0 ⟨true, true, 0, 20, []⟩
  let a : OrdinaryArgs := ⟨1, 10, 7, 30⟩
  let w ← withdraw d w 1 a ⟨true, true, 20, 13, []⟩
  ensure (w.limiter.persistent.cursor = 7 ∧ current w.limiter.persistent.history = 20) .limit
  ensure (capacityState w.limiter w.now = .ok (13, 0)) .limit
  let w := endTransaction w
  let w ← withdraw d w 1 ⟨1, 10, 8, 30⟩ ⟨true, true, 13, 5, []⟩
  ensure (capacityState w.limiter w.now = .ok (5, 0)) .limit
  let rejected := withdraw d w 1 ⟨1, 10, 6, 30⟩ ⟨true, true, 5, 0, []⟩
  ensure (rejected.toOption.isNone = true) .limit
  let afterFailure := caughtCall w (fun x => withdraw d x 1 ⟨1, 10, 1, 30⟩ ⟨false, true, 5, 4, []⟩)
  ensure (afterFailure.limiter.persistent.cursor = w.limiter.persistent.cursor) .limit
  ensure (afterFailure.core.balances 1 10 = 5) .balance
  let aborted := executeTransaction d w [
    ⟨.ordinary 1 ⟨1, 10, 2, 30⟩ ⟨true, true, 5, 3, []⟩, false⟩,
    ⟨.abort .transfer, false⟩]
  ensure (aborted.limiter.persistent.cursor = w.limiter.persistent.cursor ∧ aborted.core.balances 1 10 = 5) .limit
  return ["ordinary_exact_consumption", "ordinary_persistent_same_block_transactions",
    "ordinary_unaffordable_rejection", "caught_transfer_failure_rollback", "outer_route_abort_rollback"]

private def approvedRegressions : Checked (List String) := do
  let d := testDeployment
  let w ← fixture 10
  let w ← deposit d w 1 (.owner 1) 10 20 0 ⟨true, true, 0, 20, []⟩
  let w ← policyAction d w 1 (.rotateAuthority 3)
  let q : ApprovedWithdrawal := ⟨1, 10, 30, 5, 0, w.now, 1⟩
  let sig : SignatureAcceptance := { owner := 1, domainProxy := 100, chainId := 1, payload := q, accepted := true }
  let cb : List Callback := [
    { caller := 1, action := .invalidateNonce 1 5 },
    { caller := 1, action := .rotateAuthority 9 },
    { caller := 1, action := .freeze true }]
  let next ← fulfillApprovedWithdrawal d w 3 q sig ⟨true, true, 20, 15, cb⟩
  ensure (next.core.approvedNonces 1 = 5 ∧ next.core.epoch = 2 ∧ next.core.authority = 9 ∧ next.core.frozen = true) .nonce
  ensure (current next.limiter.persistent.history = 20 ∧ next.limiter.persistent.cursor = 0) .limit
  ensure (next.limiter.persistent.drip = w.limiter.persistent.drip) .limit
  ensure ((fulfillApprovedWithdrawal d next 3 q sig ⟨true, true, 15, 10, []⟩).toOption.isNone = true) .nonce
  ensure ((fulfillApprovedWithdrawal d w 3 q { sig with owner := 3 } ⟨true, true, 20, 15, []⟩).toOption.isNone = true) .signature
  let failed := caughtCall w (fun s => fulfillApprovedWithdrawal d s 3 q sig ⟨false, true, 20, 15, cb⟩)
  ensure (failed.core.approvedNonces 1 = 0 ∧ failed.core.epoch = 1 ∧ failed.core.frozen = false) .nonce
  return ["approved_owner_AND_authority", "approved_inclusive_deadline", "approved_callback_monotone_nonce_not_equality",
    "approved_pools_preserved", "approved_replay_rejection", "approved_failure_restores_callback_and_nonce"]

private def nativeAndCacheRegressions : Checked (List String) := do
  let d := testDeployment
  let w ← fixture 0
  let w ← deposit d w 1 (.owner 1) 0 11 11 {}
  let callbacks : List Callback := [
    { caller := 30, action := .receiveNative 5 },
    { caller := 30, action := .nestedGuarded }]
  let next ← withdraw d w 1 ⟨1, 0, 5, 30⟩ { callbacks := callbacks }
  ensure (next.nativeCustody = 11 ∧ next.limiter.persistent.cursor = 5) .limit
  let changed := environmentAction d next (.publish 20 (.error .price))
  ensure (price changed.limiter changed.quotes 0 = .ok 1) .price
  ensure (price (endTransaction changed).limiter changed.quotes 0 = .error .price) .price
  ensure ((policyAction d next 1 (.configureDrip 100 1)).toOption.isNone = true) .config
  return ["native_return_surplus_gross_charge", "persistent_guard_reentry", "cached_quote_survives_invalidation",
    "transaction_end_clears_price", "flow_locks_config"]

private def dripRegressions : Checked (List String) := do
  let l ← initializeLimiter 100 100 1
  let l := { l with persistent := { l.persistent with drip := ⟨0, 100⟩ } }
  ensure (availableDrip l.persistent 120 = .ok (20 * usdScale)) .limit
  let next ← setDripConfig l 120 1 1 200 2
  ensure (next.persistent.drip.available = 20 * usdScale) .limit
  ensure (availableDrip next.persistent 130 = .ok (40 * usdScale)) .limit
  let clamped ← setDripConfig next 130 1 1 30 0
  ensure (clamped.persistent.drip.available = 30 * usdScale) .limit
  ensure (availableDrip clamped.persistent 10000 = .ok (30 * usdScale)) .limit
  return ["drip_old_configuration_settlement", "drip_no_instant_capacity_grant", "drip_new_rate_not_retroactive", "drip_clamp_zero_rate"]

private def revisionRegressions : Checked (List String) := do
  let d := testDeployment
  let w ← fixture 10
  let child := environmentAction d w (.createChild 1)
  ensure (child.core.lastAccountId = 2 ∧ child.core.accounts 2 = ⟨1, 1, 1⟩) .account
  ensure (child.core.subaccountsByRoot 1 = [2] ∧ child.core.rootAccountIdOf 1 = 1) .account
  let child2 := environmentAction d child (.createChild 1)
  ensure (child2.core.accounts 3 = ⟨1, 1, 2⟩ ∧ child2.core.subaccountsByRoot 1 = [2, 3]) .account
  let rooted := environmentAction d child (.ensureRootAccount 9)
  ensure (rooted.core.rootAccountIdOf 9 = 3 ∧ rooted.core.accounts 3 = ⟨9, 3, 0⟩) .account
  ensure (rooted.core.accounts 1 = w.core.accounts 1 ∧ rooted.core.rootAccountIdOf 1 = 1) .account
  ensure (child.core.guardWord = 50 ∧ child.limiter.persistent.cursor = w.limiter.persistent.cursor) .account
  let locked := { w with core := { w.core with guardWord := d.coreAddress.toNat } }
  let rejected := environmentAction d locked (.createChild 1)
  ensure (rejected.core.lastAccountId = w.core.lastAccountId ∧ rejected.core.guardWord = 100) .reentrant
  let overflowing := { w.core with lastAccountId := maxWord 40 }
  ensure ((createSubaccount overflowing 1).toOption.isNone = true) .arithmetic
  let frame : InternalFrame := {
    owner := 9
    grants := w.core.grants
    balances := w.core.balances
    reserves := w.core.reserves
    guarded := true }
  let framed := environmentAction d w (.internalFrame frame)
  ensure (framed.core.owner = 9 ∧ framed.core.guardWord = 50) .reentrant
  let caught := environmentAction d locked (.internalFrame frame)
  ensure (caught.core.owner = 1 ∧ caught.core.guardWord = 100) .reentrant
  let fees ← policyAction d child 1 (.setFeeCollector 9)
  ensure (fees.core.feeCollector = 9 ∧ fees.core.rootAccountIdOf 9 = 3) .account
  ensure (previewCoreWithdrawal w 10 10 = .ok (10, 0, false)) .price
  ensure (previewWithdrawal w.limiter w.now w.quotes 10 10 77 = .ok (1, 0, false)) .price
  let outOfRange ← nextTransaction w (width 64)
  ensure ((ordinaryBatch d [] outOfRange).toOption.isSome = true) .history
  ensure (capacityState outOfRange.limiter outOfRange.now = .error .history) .history
  let validEmpty ← ordinaryBatch d [] w
  ensure (capacityState validEmpty.limiter validEmpty.now = capacityState w.limiter w.now) .history
  return ["child_shared_id_and_metadata", "child_ordered_sequence", "child_then_new_root_id",
    "child_preserves_existing_root_owner", "child_persistent_guard_exit", "child_guarded_callback_rejection",
    "child_checked_uint40_allocation", "guarded_frame_success_sentinel", "guarded_frame_rejected_rollback",
    "fee_collector_registration_after_child", "preview_configured_decimals_not_caller_decimals",
    "empty_batch_out_of_range_observation_failure", "empty_batch_valid_observation_preserved"]

private def modifierRegressions : Checked (List String) := do
  let d := testDeployment
  let w ← fixture 10
  let paused ← policyAction d w 1 (.pause true)
  let f : InternalFrame := {
    owner := 1, grants := w.core.grants, balances := w.core.balances,
    reserves := w.core.reserves, guarded := true, registerRoot := some 9 }
  let projected := environmentAction d paused (.internalFrame f)
  ensure (projected.core.paused = true ∧ projected.core.guardWord = 50 ∧
    projected.core.rootAccountIdOf 9 = 2 ∧ projected.core.lastAccountId = 2) .account
  let active := environmentAction d paused (.internalFrame { f with protocolActive := true })
  ensure (active.core.guardWord = 0 ∧ active.core.lastAccountId = 1) .paused
  let child := environmentAction d paused (.createChild 9)
  ensure (child.core.guardWord = 0 ∧ child.core.lastAccountId = 1) .paused
  ensure ((withdraw d paused 1 ⟨1, 10, 1, 30⟩ {}).toOption.isNone = true) .paused
  let locked := { paused with core := { paused.core with guardWord := 100 } }
  let rejected := environmentAction d locked (.internalFrame f)
  ensure (rejected.core.guardWord = 100 ∧ rejected.core.lastAccountId = 1) .reentrant
  let lockedActive := environmentAction d { locked with core := { locked.core with paused := false } }
    (.internalFrame { f with protocolActive := true })
  ensure (lockedActive.core.guardWord = 100 ∧ lockedActive.core.lastAccountId = 1) .reentrant
  let overflow := { paused with core := { paused.core with lastAccountId := maxWord 40 } }
  let failed := environmentAction d overflow (.internalFrame f)
  ensure (failed.core.guardWord = 0 ∧ failed.core.lastAccountId = maxWord 40 ∧
    failed.core.rootAccountIdOf 9 = 0) .arithmetic
  return ["paused_guard_only_atomic_root_and_exit", "paused_active_frame_rejection",
    "paused_child_and_custody_rejection", "guard_only_callback_sentinel_rejection",
    "active_callback_sentinel_rejection", "guard_only_allocation_failure_atomic_restore"]

def finiteRegressions : Checked (List String) := do
  let h ← historyRegressions
  let v ← valuationRegressions
  let o ← ordinaryRegressions
  let a ← approvedRegressions
  let n ← nativeAndCacheRegressions
  let d ← dripRegressions
  let r ← revisionRegressions
  let m ← modifierRegressions
  return h ++ v ++ o ++ a ++ n ++ d ++ r ++ m

#eval do
  match finiteRegressions with
  | .error e => throw (IO.userError s!"Kuru finite semantic regression failed: {repr e}")
  | .ok names =>
    IO.println s!"Kuru semantic regressions PASS: {names.length} checks"
    for name in names do IO.println s!"PASS {name}"

end Benchmark.Cases.Kuru.WithdrawalLimit
