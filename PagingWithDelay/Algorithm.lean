import PagingWithDelay.Fractional

/-!
# The algorithm `PMD` (preemptive mirror descent)

Section 3 (`sec:alg`) of `paper/paper.tex` (pseudocode `PreemptiveMirrorDescent`) as an event loop. It keeps the fractional state `x` (missing masses), a budget `B_W` per level `W`, the pending requests, and the claimed delay `c_q` of every page (`claims`).

Notation, for the current pending requests and a time `t`:
* `delay_q(t) = ∑_{ρ pending on q} d_ρ(t - a_ρ)` (`pageDelay`);
* the overshoot `o_q(t) = (delay_q(t) - c_q - w_q)⁺` (`overshoot`);
* `eq:trigger` holds for page `p` at `t` (`TriggerCond`) if `o_p(t) > 0` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_{x→p}| / L`;
* page `p` *becomes critical* at `t` (`Critical`) if `t` is the last moment before `eq:trigger` holds: it holds at times `τ ≥ t` arbitrarily close to `t`;
* the critical service on `p` from `x` follows the mirror descent path `λ(s)ᵢ = min 1 (xᵢ e^{s/wᵢ})` (`i ≠ p`), `λ(s)_p = n - k - ∑_{i ≠ p} λ(s)ᵢ` (`mdPath`), up to its length `|λ| = min {s ≥ 0 : λ(s)_p = δ}` (`serviceEnd`).

The loop, in the idle stage at time `now`:
1. If some page is critical at `now`, the first such page `p` (in the fixed order `Finset.univ.toList`) gets a **critical service** `λ`: every page `q` with `w_q ≤ w_p` raises `c_q` by the same fraction `θ` of its overshoot, `|λ| / L` in total; `x ← λ(|λ|)`; all pending requests on `p` are served and `c_p ← 0`; and `|λ|_W = |I_W ∩ [0, |λ|]|` with `I_W = [L W, 2 L W)` is deposited into `B_W` for every level `W ≥ w_p`. Then the levels `W = w_min, 2 w_min, …, w_max` are examined in increasing order; a **level-`W` preemptive service** runs if `B_W ≥ 4W` and the pages of weight `≤ W` hold cached mass at least `1 - δ`: it opens a hole (every page of weight `≤ W` gives up the same fraction of its cached mass, `1 - δ` in total) and pays `W (1 - δ)` from `B_W`; while `B_W ≥ W`, it performs a round trip (`x_q ← δ`, then back) on the pending page `q` of weight `≤ W` with the earliest deadline `inf {τ ≥ t : delay_q(τ) > w_q}`, serving all pending requests on `q`, resetting `c_q` and paying `w_q (x_q - δ)`; finally it closes the hole.
2. Otherwise the loop advances to the infimum of the times `≥ now` at which `eq:trigger` holds for some page (some page is critical there, and it is later than `now`), unless the next arrival comes no later; then it advances to that arrival time, where its requests arrive. A request on a page with `x_p = δ` is served on arrival.

The loop is a deterministic state machine `next`. Every move records the waypoints of the fractional schedule (`waypoints`): the state after a critical service, after opening a hole, at the bottom of a round trip and after it, and after closing the hole (the states `x⁽ᵛ⁾` of `sec:length`). Ticks and advances record the unchanged state at their time.

**Differences from the paper.**
* *Ties* (several pages critical at once, equal deadlines) are broken by a fixed order of the pages and by the order of the pending requests.
* *Levels* are indexed by exponents: page `p` has level `⌈log₂ w_p⌉` (`log₂ w_p` for power-of-two weights), and `B_W` for `W = 2^e` is `budget e`. Only the levels `w_min ≤ W ≤ w_max` are examined and receive deposits. This is no restriction: no level `W < w_min` receives a deposit, and no level `W ≥ w_max` does either, since at `s = L w_max` every page `i ≠ p` has `λ(s)ᵢ = 1` (`eq:light_evicted_in_band`), so `|λ| ≤ L w_max`.
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

noncomputable section

variable (input : Instance Page)

/-! ### Levels -/

/-- The level `⌈log₂ w⌉` of a page. -/
def level (p : Page) : ℤ := Int.clog 2 (w p)

/-- The lightest level `log₂ w_min`. -/
def minLevel : ℤ := ⨅ p, level input p

/-- The heaviest level `log₂ w_max`. -/
def maxLevel : ℤ := ⨆ p, level input p

/-- The weight `W = 2^e` of level `e`. -/
def levelWeight (e : ℤ) : ℝ := (2 : ℝ) ^ e

/-- The total missing mass `n - k` of a full cache. -/
def restMass : ℝ := (Fintype.card Page : ℝ) - k

/-! ### The critical service -/

/-- The missing mass `x_i(s) = min 1 (x_i e^{s/w_i})` of a page `i ≠ p` at time `s` of the mirror descent path from `x`. -/
def evictCurve (x : Page → ℝ) (i : Page) (s : ℝ) : ℝ :=
  min 1 (x i * Real.exp (s / w i))

/-- The mirror descent path `x(s)` of a critical service on `p` from `x`: the pages `i ≠ p` grow exponentially at rate `1/w_i` up to `1`, and `x_p(s) = n - k - ∑_{i ≠ p} x_i(s)`. -/
def mdPath (x : Page → ℝ) (p : Page) (s : ℝ) : Page → ℝ := fun i =>
  if i = p then restMass input - ∑ j ∈ Finset.univ.erase p, evictCurve input x j s
  else evictCurve input x i s

/-- The end `s^end` of the critical service: the least `s` with `x_p(s) ≤ δ` (equivalently `x_p(s) = δ`, as `x_p(s)` is continuous). -/
def serviceEnd (x : Page → ℝ) (p : Page) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ mdPath input x p s p ≤ δ}

/-- The state `x(s^end)` at the end of the critical service on `p`. -/
def criticalState (x : Page → ℝ) (p : Page) : Page → ℝ :=
  mdPath input x p (serviceEnd input x p)

/-! ### The preemptive service -/

/-- The fraction `θ` by which a level-`W` preemptive service raises the pages of weight `≤ W` when it opens its hole: `θ ∑_{i : w_i ≤ W} (1 - x_i) = 1 - δ`. Capped at `1`, which matters only if these pages hold less than `1 - δ` cached mass, when no hole is opened. -/
def holeFraction (x : Page → ℝ) (e : ℤ) : ℝ :=
  min 1 ((1 - δ) /
    ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i))

/-- The state of a level-`W` preemptive service after it opens its hole: every page `i` of weight `≤ W` gives up the same fraction `θ` (`holeFraction`) of its cached mass, `x_i ← x_i + θ (1 - x_i)`. -/
def hole (x : Page → ℝ) (e : ℤ) : Page → ℝ := fun i =>
  if level input i ≤ e then x i + holeFraction input x e * (1 - x i) else x i

/-- The payment `B_W ← B_W - W (1 - δ)` of a level-`W` preemptive service for creating its hole; it covers refetching the light pages when the hole is closed. -/
def holePayment (e : ℤ) : ℝ := levelWeight e * (1 - δ)

/-- The condition for a level-`W` preemptive service: `B_W ≥ 4W`, and the pages of weight `≤ W` hold cached mass `∑_{i : w_i ≤ W} (1 - x_i) ≥ 1 - δ`. -/
def preemptCondition (x : Page → ℝ) (budget : ℤ → ℝ) (e : ℤ) : Prop :=
  4 * levelWeight e ≤ budget e ∧
    1 - δ ≤ ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)

/-- The cost `w_q (x_q - δ)` of a round trip on `q` from the current state `x` (inside the hole): decrease `x_q` to `δ` and back. -/
def tripCost (x : Page → ℝ) (p : Page) : ℝ :=
  w p * (x p - δ)

/-! ### Initial state and stages -/

/-- Where the event loop is: waiting for the next trigger or arrival (`idle`), about to examine level `e` in the level loop following a critical service (`examine e`), or inside a level-`e` preemptive service whose hole was created from the state `base` (`preempt e base`). -/
inductive Stage (Page : Type*) where
  | idle
  | examine (e : ℤ)
  | preempt (e : ℤ) (base : Page → ℝ)

/-- The page outside `C₀` that holds missing mass `1 - kδ` in the initial state: the first page outside `C₀` in the fixed order `Finset.univ.toList`. -/
def initialPage : Option Page :=
  Finset.univ.toList.find? fun i => decide (i ∉ input.initialCache)

/-- The initial state (Appendix A): missing mass `δ` on the pages of `C₀`, `1 - kδ` on one page outside `C₀` (`initialPage`) and `1` on the others, total `n - k`. -/
def initialState (i : Page) : ℝ :=
  if i ∈ input.initialCache then δ
  else if initialPage input = some i then 1 - k * δ
  else 1

/-- The stage after level `e` has been dealt with. -/
def afterLevel (e : ℤ) : Stage Page :=
  if e < maxLevel input then .examine (e + 1) else .idle

/-! ### Delays, overshoots and the trigger -/

/-- `delay_p(t)`: the total delay at time `t` of the pending requests on `p`. -/
def pageDelay (pending : List (Request Page)) (p : Page) (t : ℝ) : ℝ :=
  ((pending.filter fun ρ => decide (ρ.page = p)).map fun ρ => ρ.delay (t - ρ.arrival)).sum

/-- The overshoot `o_p(t) = (delay_p(t) - c_p - w_p)⁺`. -/
def overshoot (pending : List (Request Page)) (claims : Page → ℝ) (p : Page) (t : ℝ) : ℝ :=
  max 0 (pageDelay pending p t - claims p - w p)

/-- The pages `q` with `w_q ≤ w_p`. -/
def lighter (p : Page) : Finset Page :=
  Finset.univ.filter fun q => w q ≤ w p

/-- The trigger condition `eq:trigger` for page `p` at time `t` in the state `x`: `o_p(t) > 0` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L`. -/
def TriggerCond (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  0 < overshoot input pending claims p t ∧
    serviceEnd input x p / L ≤
      ∑ q ∈ lighter input p, overshoot input pending claims q t

/-- Page `p` becomes critical at time `t`: `t` is the last moment before `eq:trigger` holds, i.e. `eq:trigger` holds at times `τ ≥ t` arbitrarily close to `t`. -/
def Critical (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  ∀ ε > 0, ∃ τ, t ≤ τ ∧ τ < t + ε ∧ TriggerCond input x pending claims τ p

/-- The fraction `θ` of the overshoots claimed by a critical service on `p` at time `t` from the state `x`: `θ ∑_{q : w_q ≤ w_p} o_q(t) = |λ_p(x)| / L`. Capped at `1`, which matters only if `p` is not critical at `t` (otherwise `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L` by continuity). -/
def claimFraction (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : ℝ :=
  min 1 (serviceEnd input x p / L /
    ∑ q ∈ lighter input p, overshoot input pending claims q t)

/-- The claims of a critical service on `p` at time `t` from the state `x`: every page `q` with `w_q ≤ w_p` claims the same fraction `θ` of its overshoot, `c_q ← c_q + θ o_q(t)`, so that `|λ_p(x)| / L` is claimed in total. -/
def claimUpdate (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Page → ℝ := fun q =>
  if q ∈ lighter input p then
    claims q + claimFraction input x pending claims t p * overshoot input pending claims q t
  else claims q

/-! ### Deposits -/

/-- The length `|λ|_W = |I_W ∩ [0, |λ|]|` of the part of the critical service on `p` from `x` in `I_W = [L W, 2 L W)`, for the level `e`, `W = 2^e`. -/
def levelLen (x : Page → ℝ) (p : Page) (e : ℤ) : ℝ :=
  min (2 * L * levelWeight e) (serviceEnd input x p) -
    min (L * levelWeight e) (serviceEnd input x p)

/-- The deposits of a critical service `λ` on `p` from `x`: `B_W ← B_W + |λ|_W` for every level `W` with `w_p ≤ W ≤ w_max`. -/
def deposit (x : Page → ℝ) (p : Page) (budget : ℤ → ℝ) : ℤ → ℝ := fun e =>
  if level input p ≤ e ∧ e ≤ maxLevel input then budget e + levelLen input x p e
  else budget e

/-! ### Round trips -/

/-- The deadline `inf {τ ≥ t : delay_p(τ) > w_p}` of the pending requests on `p` at time `t`. -/
def pageDeadline (pending : List (Request Page)) (t : ℝ) (p : Page) : ℝ :=
  sInf {τ | t ≤ τ ∧ w p < pageDelay pending p τ}

/-- The next round trip of a level-`W` preemptive service at time `t`: the pending request on a page of weight `≤ W` whose page has the earliest deadline (the first such in the pending list). -/
def tripCandidate (pending : List (Request Page)) (t : ℝ) (e : ℤ) : Option (Request Page) :=
  (pending.filter fun ρ => decide (level input ρ.page ≤ e)).argmin
    fun ρ => pageDeadline input pending t ρ.page

/-! ### The event loop -/

/-- The loop state: the current time `now`, the arrival times `upcoming` still to be processed, the fractional state `x` (inside a preemptive service, the state with the hole), the budget `budget e` (`B_W`) of level `e`, the `pending` requests, the used amount `claims q` (`c_q`) of the delay of page `q`, and the `stage` (see `Stage`). -/
structure Snap (Page : Type*) where
  now : ℝ
  upcoming : List ℝ
  x : Page → ℝ
  budget : ℤ → ℝ
  pending : List (Request Page)
  claims : Page → ℝ
  stage : Stage Page

/-- One move of the loop. -/
inductive Move (Page : Type*) where
  /-- Arrivals at time `t`. -/
  | tick (t : ℝ)
  /-- Advance to the time `t` at which some page becomes critical first. -/
  | advance (t : ℝ)
  /-- A critical service on page `p`. -/
  | critical (p : Page)
  /-- Level `e` examined; the condition for its preemptive service fails. -/
  | skip (e : ℤ)
  /-- Level `e` examined; its preemptive service creates the hole and pays `W (1 - δ)`. -/
  | openHole (e : ℤ)
  /-- A round trip on `π.page`, selected by the pending request `π`. -/
  | trip (e : ℤ) (π : Request Page)
  /-- The level-`e` preemptive service closes its hole: no candidate is left (`none`), or the budget is too small for the next round trip, `B_W < W` (`some π`, the candidate that is not served). -/
  | closeHole (e : ℤ) (stop : Option (Request Page))

/-- The distinct arrival times, in increasing order. -/
def arrivalTimes : List ℝ :=
  (input.requests.map Request.arrival).toFinset.sort (· ≤ ·)

/-- The loop state before the first move; `now` is the first arrival time, so times never decrease along the run. -/
def initialSnap : Snap Page where
  now := (arrivalTimes input).headD 0
  upcoming := arrivalTimes input
  x := initialState input
  budget := fun _ => 0
  pending := []
  claims := fun _ => 0
  stage := .idle

/-- The page served by the next critical service at time `s.now`: the first page (in the fixed order `Finset.univ.toList`) that is critical at `s.now`. -/
def triggerPage (s : Snap Page) : Option Page :=
  (Finset.univ.toList).find? fun p => decide (Critical input s.x s.pending s.claims s.now p)

/-- The times `≥ now` at which `eq:trigger` holds for some page, for the current state, pending requests and claims. -/
def triggerTimes (s : Snap Page) : Set ℝ :=
  {t | s.now ≤ t ∧ ∃ p, TriggerCond input s.x s.pending s.claims t p}

/-- One move of `PMD`, or `none` when the run is over. -/
def next (s : Snap Page) : Option (Move Page × Snap Page) :=
  match s.stage with
  | .idle =>
      match triggerPage input s with
      | some p =>
          some (.critical p,
            { s with
              x := criticalState input s.x p
              budget := deposit input s.x p s.budget
              pending := s.pending.filter fun π => decide (π.page ≠ p)
              claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
              stage := .examine (minLevel input) })
      | none =>
          if (triggerTimes input s).Nonempty ∧
              ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a then
            some (.advance (sInf (triggerTimes input s)),
              { s with now := sInf (triggerTimes input s) })
          else
            match s.upcoming with
            | [] => none
            | t :: rest =>
                some (.tick t,
                  { s with
                    now := t
                    upcoming := rest
                    pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
                      fun ρ => decide (s.x ρ.page ≠ δ) })
  | .examine e =>
      if preemptCondition input s.x s.budget e then
        some (.openHole e,
          { s with
            x := hole input s.x e
            budget := Function.update s.budget e (s.budget e - holePayment input e)
            stage := .preempt e s.x })
      else
        some (.skip e, { s with stage := afterLevel input e })
  | .preempt e base =>
      match tripCandidate input s.pending s.now e with
      | none => some (.closeHole e none, { s with x := base, stage := afterLevel input e })
      | some π =>
          if levelWeight e ≤ s.budget e then
            some (.trip e π,
              { s with
                budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
                pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
                claims := Function.update s.claims π.page 0 })
          else
            some (.closeHole e (some π), { s with x := base, stage := afterLevel input e })

/-- The waypoints a move records, given the state before it. -/
def waypoints (pre : Snap Page) : Move Page → List (Waypoint Page)
  | .tick t => [⟨t, pre.x⟩]
  | .advance t => [⟨t, pre.x⟩]
  | .critical p => [⟨pre.now, criticalState input pre.x p⟩]
  | .skip _ => []
  | .openHole e => [⟨pre.now, hole input pre.x e⟩]
  | .trip _ π => [⟨pre.now, Function.update pre.x π.page δ⟩, ⟨pre.now, pre.x⟩]
  | .closeHole _ _ =>
      match pre.stage with
      | .preempt _ base => [⟨pre.now, base⟩]
      | _ => []

/-- A log entry: the state before a move and the move. -/
abbrev Entry (Page : Type*) := Snap Page × Move Page

/-- Run at most `fuel` moves from `s`; returns the log and the final state. -/
def run : ℕ → Snap Page → List (Entry Page) × Snap Page
  | 0, s => ([], s)
  | fuel + 1, s =>
      match next input s with
      | none => ([], s)
      | some (m, s') =>
          let rest := run fuel s'
          ((s, m) :: rest.1, rest.2)

/-- The number of levels `log₂ w_max - log₂ w_min + 1`. -/
def numLevels : ℕ := (maxLevel input - minLevel input + 1).toNat

/-- A bound on the number of moves: every tick consumes an arrival time, every critical service and round trip serves a request, every advance is followed by a critical service, and between two critical services at most two moves per level are made. -/
def fuel : ℕ :=
  (4 * input.requests.length + 1) * (2 * numLevels input + 4) + 1

/-- The log of `PMD` on `input`. -/
def log : List (Entry Page) := (run input (fuel input) (initialSnap input)).1

end

end PMD

/-- **The algorithm `PMD`** (`PreemptiveMirrorDescent`): the fractional schedule recorded by the event loop. -/
noncomputable def preemptiveMirrorDescent {Page : Type*} [Fintype Page] [DecidableEq Page] :
    FracAlgorithm Page :=
  fun input => (PMD.log input).flatMap fun entry => PMD.waypoints input entry.1 entry.2

end PagingWithDelay
