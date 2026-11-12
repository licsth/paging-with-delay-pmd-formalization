import PagingWithDelay.Model

/-!
# Weighted paging with deadlines

As in `Model.lean`, but a request `(p, a, d)` must be served in its window `[a, d]`, and a schedule pays only its fetch cost.
-/

namespace PagingWithDelay

/-- A request for `page`, to be served in `[arrival, deadline]`. -/
structure DeadlineRequest (Page : Type*) where
  page : Page
  arrival : ℝ
  deadline : ℝ
  arrival_le_deadline : arrival ≤ deadline

/-- An instance: as `Instance`, with deadline requests. -/
structure DeadlineInstance (Page : Type*) [Fintype Page] where
  weight : Page → ℝ
  weight_pos : ∀ p, 0 < weight p
  cacheSize : ℕ
  cacheSize_pos : 0 < cacheSize
  cacheSize_lt : cacheSize < Fintype.card Page
  initialCache : Finset Page
  initialCache_card : initialCache.card = cacheSize
  requests : List (DeadlineRequest Page)

namespace DeadlineInstance

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The total weight `∑ᵢ wᵢ` of all pages. -/
noncomputable def totalWeight (input : DeadlineInstance Page) : ℝ :=
  ∑ p, input.weight p

/-- The requests that have arrived by `t`. -/
noncomputable def upTo (input : DeadlineInstance Page) (t : ℝ) : DeadlineInstance Page :=
  { input with requests := input.requests.filter fun ρ => decide (ρ.arrival ≤ t) }

/-- As `Schedule.CachedAt`. -/
def CachedAt (input : DeadlineInstance Page) (S : Schedule Page) (p : Page) (s : ℝ) : Prop :=
  (p ∈ input.initialCache ∧ ∀ step ∈ S.head?, s ≤ step.time) ∨
    ∃ (j : ℕ) (h : j < S.length), S[j].time ≤ s ∧
      (∀ step ∈ S[j + 1]?, s ≤ step.time) ∧ p ∈ S[j].cache

/-- Chronological, at most `k` pages, and every request served in its window. -/
structure Feasible (input : DeadlineInstance Page) (S : Schedule Page) : Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  capacity : ∀ step ∈ S, step.cache.card ≤ input.cacheSize
  serves : ∀ ρ ∈ input.requests, ∃ s, ρ.arrival ≤ s ∧ s ≤ ρ.deadline ∧ input.CachedAt S ρ.page s

/-- The fetch cost of `S`. -/
noncomputable def cost (input : DeadlineInstance Page) (S : Schedule Page) : ℝ :=
  Schedule.costFrom input.weight input.initialCache S

end DeadlineInstance

/-! ## Randomized algorithms (as in `Model.lean`) -/

/-- A distribution on schedules for every instance. -/
abbrev DeadlineAlgorithm (Page : Type*) [Fintype Page] := DeadlineInstance Page → PMF (Schedule Page)

namespace DeadlineAlgorithm

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The steps up to `t` depend only on the requests arrived by `t`. -/
def Online (alg : DeadlineAlgorithm Page) : Prop :=
  ∀ (first second : DeadlineInstance Page) (t : ℝ), first.upTo t = second.upTo t →
    (alg first).map (Schedule.upTo · t) = (alg second).map (Schedule.upTo · t)

/-- Feasible with probability `1`. -/
def Feasible (alg : DeadlineAlgorithm Page) : Prop :=
  ∀ (input : DeadlineInstance Page), ∀ S ∈ (alg input).support, input.Feasible S

/-- The expected cost `E[cost(S)]` of the random schedule `S`. -/
noncomputable def expectedCost (alg : DeadlineAlgorithm Page) (input : DeadlineInstance Page) :
    ENNReal :=
  ∑' S, alg input S * ENNReal.ofReal (input.cost S)

end DeadlineAlgorithm

end PagingWithDelay
