import PagingWithDelay.Run.Feasible
import PagingWithDelay.Critical
import PagingWithDelay.Opt

/-!
# Shared definitions of the analysis

Per-entry accounting of the run (fetches, evictions, lengths and budget payments of the moves), and the notions of the charging arguments against a comparator `S` with service times `σ`: chargeable visits (`def:chargeable`), the excess of a miss service, and overdue services.

The comparator is a schedule `S` serving each request `ρ` in `[a_ρ, σ ρ]` (`S.FeasibleBy input σ`), typically in swap form, with cache `cacheAt input S t` at time `t`; it has served `ρ` by `t` if `ServedBy input σ S ρ t`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch criticalEV hole holePayment tripCost)
open PagingWithDelay.Schedule (cacheAt ServedBy)

open Classical

noncomputable section

variable (input : Instance Page)

/-! ### Accounting of the run -/

/-- The fetch `w_p (x_p - δ)` of entry `i` if it is a critical service on `p`, else `0`. -/
def fetchAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => criticalFetch input (snapAt input i).x p
    | _ => 0
  else 0

/-- The weighted eviction `EV(λ)` of entry `i` if it is a critical service, else `0`. -/
def evAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => criticalEV input (snapAt input i).x p
    | _ => 0
  else 0

/-- The length `|λ|` of entry `i` if it is a critical service, else `0`. -/
def lenAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => serviceEnd input (snapAt input i).x p
    | _ => 0
  else 0

/-- The payment `W (1 - δ)` of entry `i` from the budget if it opens a hole, else `0`. -/
def holeAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .openHole e => holePayment input e
    | _ => 0
  else 0

/-- The cost `w_q (x_q - δ)` of entry `i` if it is a round trip on `q`, else `0` (paid from the budget). -/
def tripAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .trip _ π => tripCost input (snapAt input i).x π.page
    | _ => 0
  else 0

/-- `∑_λ fetch(λ)`. -/
def fetchTotal : ℝ := ∑ i ∈ Finset.range (log input).length, fetchAt input i

/-- `∑_λ EV(λ)`. -/
def evTotal : ℝ := ∑ i ∈ Finset.range (log input).length, evAt input i

/-- `∑_λ |λ|`. -/
def lenTotal : ℝ := ∑ i ∈ Finset.range (log input).length, lenAt input i

/-- The total payment for holes. -/
def holeTotal : ℝ := ∑ i ∈ Finset.range (log input).length, holeAt input i

/-- The total cost of round trips. -/
def tripTotal : ℝ := ∑ i ∈ Finset.range (log input).length, tripAt input i

/-! ### Visits -/

/-- The page visited at entry `i`: the page of a critical service or of a round trip. -/
def visitPage (i : ℕ) : Option Page :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => some p
    | .trip _ π => some π.page
    | _ => none
  else none

/-! ### The comparator -/

variable (σ : Request Page → ℝ) (S : Schedule Page)

/-- The comparator's delay cost `∑ d_ρ(σ ρ - a_ρ)` of the requests (by index) pending on page `p` in the loop state `s`. -/
def optDelayOn (s : Snap Page) (p : Page) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin input.requests.length =>
      input.requests[j] ∈ s.pending ∧ input.requests[j].page = p),
    Schedule.delayOf σ input.requests[j]

/-- `def:chargeable` (with "at least `w_p`" in (ii)): entry `i` is a visit of `p` (critical service or round trip) such that, right before it, (i) `p` is not in the comparator's cache and the comparator has served some pending request on `p`, or (ii) the comparator's delay cost for the pending requests on `p` is at least `w_p`. -/
def IsChargeable (i : ℕ) : Prop :=
  ∃ p, visitPage input i = some p ∧
    ((p ∉ cacheAt input S (entryTime input i) ∧
        ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
          ServedBy input σ S ρ (entryTime input i)) ∨
      w p ≤ optDelayOn input σ (snapAt input i) p)

/-- The weight of the page visited at entry `i` if it is chargeable, else `0`. -/
def chargeW (i : ℕ) : ℝ :=
  if IsChargeable input σ S i then
    match visitPage input i with
    | some p => w p
    | none => 0
  else 0

/-- `chargeW i` if entry `i` is a round trip, else `0`: the chargeable weight of round trips. -/
def tripChargeW (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .trip _ _ => chargeW input σ S i
    | _ => 0
  else 0

/-- `w_p` if entry `i` is a miss service on `p`, else `0`. -/
def missW (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => if p ∈ cacheAt input S (entryTime input i) then 0
        else w p
    | _ => 0
  else 0

/-- The levels `e` with `w_p ≤ 2^e ≤ w_max` whose weight is below every weight in the comparator's cache at time `t`. -/
def excessLevels (p : Page) (t : ℝ) : Finset ℤ :=
  (Finset.Icc (level input p) (maxLevel input)).filter
    (fun e => ∀ q ∈ cacheAt input S t, levelWeight e < w q)

/-- The excess `Exc(λ)` of entry `i`: if it is a miss service `λ` on `p`, the sum of `|λ|_W` over the levels `W` with `w_p ≤ W < w_min(OPT)`; else `0`. -/
def excessAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p =>
        if p ∈ cacheAt input S (entryTime input i) then 0
        else ∑ e ∈ excessLevels input S p (entryTime input i),
          levelLen input (snapAt input i).x p e
    | _ => 0
  else 0

/-- The delay at time `t` of the requests pending on `q` in the state `s` that the comparator has already served by `t`. -/
def servedDelay (s : Snap Page) (q : Page) (t : ℝ) : ℝ :=
  ((s.pending.filter fun ρ => decide (ρ.page = q ∧
      ServedBy input σ S ρ t)).map
    fun ρ => ρ.delay (t - ρ.arrival)).sum

/-- Page `q` is *overdue* in the state `s` at time `t`: the pending requests on `q` that the comparator has served have delay more than `w_q`. -/
def PageOverdue (s : Snap Page) (q : Page) (t : ℝ) : Prop :=
  w q < servedDelay input σ S s q t

/-- Entry `i` is an *overdue* critical service: on a page `p` such that some `q` with `w_q ≤ w_p` is overdue right before it. (The paper restricts this to miss services on pages below `w_min(OPT)`; only those have positive excess.) -/
def IsOverdue (i : ℕ) : Prop :=
  ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧
    ∃ q, w q ≤ w p ∧
      PageOverdue input σ S (snapAt input i) q (entryTime input i)

end

end PMD

end PagingWithDelay
