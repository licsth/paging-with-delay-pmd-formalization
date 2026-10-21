import PagingWithDelay.Notation

/-!
# The fractional relaxation

Fractional schedules, their fetch cost (`def:fracfetch`) and delay cost (`def:fracdelay`), and deterministic fractional algorithms. `PMD` is such an algorithm; these definitions belong to the proof, not to the statement of the main theorem.

A fractional state `x : Page → ℝ` gives the *missing mass* of every page: `1 - xᵢ` of page `i` is cached. States lie in `[δ, 1]ⁿ` with total missing mass at least `n - k` (cached mass at most `k`), and a page with `xᵢ = δ` counts as cached.

A fractional schedule is a finite list of waypoints `(time, state)`, traversed in order (`x⁽⁰⁾, …, x⁽ᴺ⁾` in `sec:length`). The state is constant between consecutive waypoint times; waypoints with the same time are traversed at one instant. The requests arriving at time `t` arrive before the waypoints with time `t`.
-/

namespace PagingWithDelay

/-- A waypoint: the fractional schedule is in state `state` at `time`. -/
structure Waypoint (Page : Type*) where
  time : ℝ
  state : Page → ℝ

/-- A fractional schedule: a list of waypoints. -/
abbrev FracSchedule (Page : Type*) := List (Waypoint Page)

namespace FracSchedule

variable {Page : Type*} [Fintype Page]

open scoped InstanceNotation in
/-- The fractional fetch cost `∑ᵥ ∑ᵢ wᵢ (x⁽ᵛ⁾ᵢ - x⁽ᵛ⁺¹⁾ᵢ)⁺` (`def:fracfetch`). -/
noncomputable def fetchCost (input : Instance Page) : FracSchedule Page → ℝ
  | a :: b :: rest =>
      (∑ i, w i * max 0 (a.state i - b.state i)) + fetchCost input (b :: rest)
  | _ => 0

/-- The state right before time `t`: the state of the last waypoint with time `< t`, or of the first waypoint if there is none. -/
noncomputable def stateBefore (X : FracSchedule Page) (t : ℝ) : Page → ℝ :=
  match (X.filter fun w => decide (w.time < t)).getLast? with
  | some w => w.state
  | none => (X.head?.map Waypoint.state).getD fun _ => 1

/-- The time `τ_ρ` at which `ρ` is served: the first time `≥ a_ρ` of a waypoint at which its page has missing mass `δ`. -/
noncomputable def serviceTime (input : Instance Page) (X : FracSchedule Page)
    (ρ : Request Page) : ℝ :=
  sInf {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧ w.time = s}

open scoped InstanceNotation in
/-- The fractional delay cost `∑_ρ α_ρ d_ρ(τ_ρ - a_ρ)` (`def:fracdelay`), where `α_ρ = x_p - δ` for the state `x` right before the arrival of `ρ`. -/
noncomputable def delayCost (input : Instance Page) (X : FracSchedule Page) : ℝ :=
  (input.requests.map fun ρ =>
    (stateBefore X ρ.arrival ρ.page - δ) *
      ρ.delay (serviceTime input X ρ - ρ.arrival)).sum

/-- The cost of a fractional schedule: fractional fetch cost plus fractional delay cost. -/
noncomputable def cost (input : Instance Page) (X : FracSchedule Page) : ℝ :=
  fetchCost input X + delayCost input X

/-- A feasible fractional schedule: chronological waypoints whose states lie in `[δ, 1]ⁿ` with total missing mass at least `n - k`, and every request served at a waypoint at or after its arrival. -/
structure Feasible (input : Instance Page) (X : FracSchedule Page) : Prop where
  chronological : X.Pairwise fun earlier later => earlier.time ≤ later.time
  bounds : ∀ w ∈ X, ∀ i, input.delta ≤ w.state i ∧ w.state i ≤ 1
  mass : ∀ w ∈ X, (Fintype.card Page : ℝ) - input.cacheSize ≤ ∑ i, w.state i
  serves : ∀ ρ ∈ input.requests, ∃ w ∈ X,
    ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta

/-- The waypoints up to time `t`. -/
noncomputable def upTo (X : FracSchedule Page) (t : ℝ) : FracSchedule Page :=
  X.filter fun w => decide (w.time ≤ t)

end FracSchedule

/-- A deterministic fractional algorithm: a fractional schedule for every instance. -/
abbrev FracAlgorithm (Page : Type*) [Fintype Page] := Instance Page → FracSchedule Page

namespace FracAlgorithm

variable {Page : Type*} [Fintype Page]

/-- **Online**: the waypoints up to time `t` depend only on the requests revealed by time `t`. -/
def Online (alg : FracAlgorithm Page) : Prop :=
  ∀ (first second : Instance Page) (t : ℝ), first.upTo t = second.upTo t →
    (alg first).upTo t = (alg second).upTo t

/-- **Feasible**: every instance receives a feasible fractional schedule. -/
def Feasible (alg : FracAlgorithm Page) : Prop :=
  ∀ input : Instance Page, (alg input).Feasible input

end FracAlgorithm

end PagingWithDelay
