/-
Source-shaped Kuru V2 WithdrawalLimiter semantics.
Pinned provenance and reproduction instructions are in case.yaml and README.md.

Simplifications/refinement boundaries:
* Verity addresses index total Lean functions instead of hashed physical mappings.
  Solidity scalar/packed uint fields are Nat projections; casts truncate modulo
  width, explicit guards/checked arithmetic are retained. Range safety is a SPEC,
  not assumed by executable transitions.
* External view fetches are supplied as `Checked Nat` from the current source.
  They may revert or return invalid/stale data. Source freshness and economic
  correctness are NOT invented limiter guards. The quoted observation is not a
  proof of the price-provider implementation. Views cannot mutate this state.
* Full-precision mulDiv is mathematical integer quotient/remainder plus its
  actual divisor/result/rounding overflow behavior. Solady implementation
  correspondence is manual, not a proof of its assembly.
* Persistent/transient fields are separate records. Neither `beginFlow` nor
  `record*` resets transient state; only the outer transaction boundary does.
* Events are represented by returned funding observations; gas/log encoding,
  storage hashes, upgrade execution and bytecode refinement are not modeled.
* This is an executable multi-contract semantic model using Verity types and
  rely/guarantee primitives, NOT a `verity_contract` DSL/Yul compilation target.
  No framework incapability is claimed: a DSL bridge would be a separate artifact.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.History
import Verity.Core.Address

namespace Benchmark.Cases.Kuru.WithdrawalLimit

abbrev Key := Verity.Core.Address

def usdScale : Nat := 10 ^ 18

structure DripState where
  available : Nat := 0
  updatedAt : Nat := 0
  deriving DecidableEq, Repr

/-- Solidity DripState packs the available amount LOW192 and time HIGH64. -/
def packDrip (d : DripState) : Nat := d.available + d.updatedAt * width 192

def unpackDrip (word : Nat) : DripState :=
  ⟨word % width 192, (word / width 192) % width 64⟩

structure Persistent where
  history : History := {}
  cursor : Nat := 0
  capacityUsd18 : Nat := 0
  rateUsd18 : Nat := 0
  drip : DripState := {}
  priceSource : Key → Key := fun _ => 0

structure Transient where
  flowStarted : Bool := false
  expired : Nat := 0
  prices : Key → Nat := fun _ => 0

structure Limiter where
  persistent : Persistent := {}
  transient : Transient := {}

abbrev PriceFetch := Key → Checked Nat

def timestamp (now : Nat) : Checked Nat := do
  ensure (now ≤ maxWord 64) .history
  return castWord 64 now

/-- Fresh initialization; no arbitrary inherited history or cursor. -/
def initializeLimiter (now capacity rate : Nat) : Checked Limiter := do
  ensure (capacity < width 128 ∧ rate < width 128) .config
  let t ← timestamp now
  return { persistent := {
    capacityUsd18 := capacity, rateUsd18 := rate,
    drip := ⟨castWord 192 (capacity * usdScale), t⟩ } }

def availableDrip (s : Persistent) (now : Nat) : Checked Nat := do
  let elapsed ← checkedSub now s.drip.updatedAt
  -- Actual checked uint256 expression; no wraparound full-product substitution.
  let refill := elapsed * s.rateUsd18 * usdScale
  ensure (refill < width 256) .arithmetic
  let available ← checkedAdd 256 s.drip.available refill
  return min available (s.capacityUsd18 * usdScale)

def creditCursor (s : Persistent) (expired : Nat) : Nat := max s.cursor expired

def price (s : Limiter) (fetch : PriceFetch) (token : Key) : Checked Nat := do
  let cached := s.transient.prices token
  if cached ≠ 0 then return castWord 128 cached
  let source := s.persistent.priceSource token
  ensure (source ≠ 0) .price
  let quote ← fetch source
  ensure (quote ≠ 0 ∧ quote ≤ maxWord 128) .price
  return castWord 128 quote

def snapshotPrice (s : Limiter) (fetch : PriceFetch) (token : Key) : Checked (Nat × Limiter) := do
  let quote ← price s fetch token
  return (quote, { s with transient := { s.transient with
    prices := fun k => if k = token then quote else s.transient.prices k } })

/-- Preview reads `price`; unlike snapshot, it does not tstore. -/
def beginFlow (s : Limiter) (now : Nat) : Checked Limiter := do
  if s.transient.flowStarted then return s
  let t ← timestamp now
  let (expired, sequence) ← referenceAt s.persistent.history t
  return { s with
    persistent := { s.persistent with history := { s.persistent.history with
      referenceSequence := if s.persistent.history.referenceSequence ≠ sequence
        then sequence else s.persistent.history.referenceSequence } }
    transient := { s.transient with flowStarted := true, expired := expired } }

def fullMulDiv (a b divisor : Nat) (roundUp : Bool) : Checked Nat := do
  ensure (divisor ≠ 0) .arithmetic
  let quotient := a * b / divisor
  ensure (quotient < width 256) .arithmetic
  if roundUp ∧ a * b % divisor ≠ 0 then checkedAdd 256 quotient 1
  else pure quotient

/-- `amount` is ABI uint256 and `decimals` uint8; quote is validated by price. -/
def value (amount quote decimals : Nat) (roundUp : Bool) : Checked Nat := do
  ensure (amount < width 256 ∧ quote < width 128 ∧ decimals < width 8) .config
  ensure (decimals ≤ 77) .config
  if decimals ≤ 18 then
    let scalePrice := quote * 10 ^ (18 - decimals)
    -- EVM/Solidity division by zero fails; normal price paths establish quote>0.
    ensure (scalePrice ≠ 0) .arithmetic
    ensure (amount ≤ maxWord 192 / scalePrice) .valueOverflow
    return amount * scalePrice
  else
    let v ← fullMulDiv amount quote (10 ^ (decimals - 18)) roundUp
    ensure (v ≤ maxWord 192) .valueOverflow
    return v

structure Funding where
  value : Nat
  cursor : Nat
  credit : Nat
  depositUsed : Nat
  dripUsed : Nat
  deriving DecidableEq, Repr

/-- Authorization is explicit here, not assumed by a caller-supplied `onlyCore` flag. -/
def recordDeposit (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (amount decimals : Nat) : Checked (Nat × Limiter) := do
  ensure (caller = core) .unauthorized
  let s ← beginFlow s now
  let (quote, s) ← snapshotPrice s fetch token
  let v ← value amount quote decimals false
  let next ← checkedAdd 256 (current s.persistent.history) v
  ensure (next ≤ maxWord 192) .valueOverflow
  let h ← if v ≠ 0 then write s.persistent.history next now else pure s.persistent.history
  return (v, { s with persistent := { s.persistent with history := h } })

def recordWithdrawal (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) (amount decimals : Nat) : Checked (Funding × Limiter) := do
  ensure (caller = core) .unauthorized
  let s ← beginFlow s now
  let (quote, s) ← snapshotPrice s fetch token
  let v ← value amount quote decimals true
  let cursor := creditCursor s.persistent s.transient.expired
  let credit ← checkedSub (current s.persistent.history) cursor
  let depositUsed := min v credit
  let dripUsed := v - depositUsed
  let drip ← if dripUsed ≠ 0 then do
    let t ← timestamp now
    let available ← availableDrip s.persistent t
    ensure (dripUsed ≤ available) .limit
    pure (DripState.mk (castWord 192 (available - dripUsed)) t)
    else pure s.persistent.drip
  let nextCursor ← if depositUsed ≠ 0 then do
    let sum ← checkedAdd 256 cursor depositUsed
    pure (castWord 192 sum)
    else pure s.persistent.cursor
  return (⟨v, cursor, credit, depositUsed, dripUsed⟩,
    { s with persistent := { s.persistent with cursor := nextCursor, drip := drip } })

def checkApprovedWithdrawal (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (caller core token : Key) : Checked Limiter := do
  ensure (caller = core) .unauthorized
  let s ← beginFlow s now
  let (_, s) ← snapshotPrice s fetch token
  return s

def setDripConfig (s : Limiter) (now : Nat) (caller governance : Key)
    (capacity rate : Nat) : Checked Limiter := do
  ensure (caller = governance) .unauthorized
  ensure (s.transient.flowStarted = false) .config
  ensure (capacity < width 128 ∧ rate < width 128) .config
  let t ← timestamp now
  let available ← availableDrip s.persistent t
  return { s with persistent := { s.persistent with
    drip := ⟨castWord 192 (min available (capacity * usdScale)), t⟩
    capacityUsd18 := capacity, rateUsd18 := rate } }

def setPriceSource (s : Limiter) (caller governance token source : Key)
    (hasCode : Key → Bool) : Checked Limiter := do
  ensure (caller = governance) .unauthorized
  ensure (s.transient.flowStarted = false) .config
  ensure (source = 0 ∨ hasCode source = true) .config
  return { s with persistent := { s.persistent with
    priceSource := fun k => if k = token then source else s.persistent.priceSource k } }

def capacityState (s : Limiter) (now : Nat) : Checked (Nat × Nat) := do
  let expired ← if s.transient.flowStarted then pure s.transient.expired else do
    let (expired, _) ← referenceAt s.persistent.history now
    pure expired
  let credit ← checkedSub (current s.persistent.history) (creditCursor s.persistent expired)
  let t ← timestamp now
  let drip ← availableDrip s.persistent t
  return (credit, drip)

/-- Parameterized read helper; Core wrapper supplies configured decimals. -/
def previewWithdrawal (s : Limiter) (now : Nat) (fetch : PriceFetch)
    (token : Key) (amount decimals : Nat) : Checked (Nat × Nat × Bool) := do
  let quote ← price s fetch token
  let required ← value amount quote decimals true
  let (credit, drip) ← capacityState s now
  let available ← checkedAdd 256 credit drip
  return (required, available, decide (required ≤ available))

end Benchmark.Cases.Kuru.WithdrawalLimit
