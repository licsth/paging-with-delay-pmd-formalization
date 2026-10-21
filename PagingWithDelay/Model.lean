import PagingWithDelay.Imports

/-!
# Weighted paging with delay

Every definition that the main theorem mentions (the section "Problem definition" of the paper): requests and instances, schedules and their cost, and randomized algorithms.

There are `n` pages (a `Fintype`), page `i` has weight `wᵢ > 0`, and the cache holds `k` pages, `0 < k < n`. A request `(p, a, d)` asks for page `p`; it is revealed at its arrival time `a` together with its delay cost function `d`, and if it is served at time `τ ≥ a`, it costs `d (τ - a)`. Delay cost functions are nondecreasing, continuous and unbounded with `d 0 = 0`. The paper's delay cost functions are defined on `[0, ∞)`; here they are defined on `ℝ` (extend by `0` to negative arguments, which keeps them monotone and continuous), and only nonnegative arguments are ever used. Arrival times may be negative, which does not matter.
-/

namespace PagingWithDelay

/-- A request for `page`, revealed at `arrival` together with its delay cost function `delay`: served at time `τ ≥ arrival`, it costs `delay (τ - arrival)`. -/
structure Request (Page : Type*) where
  page : Page
  arrival : ℝ
  delay : ℝ → ℝ
  delay_mono : Monotone delay
  delay_continuous : Continuous delay
  delay_zero : delay 0 = 0
  delay_unbounded : ∀ M : ℝ, ∃ τ, M ≤ delay τ

/-- An instance: positive page weights, a cache size `0 < k < n`, the initial cache `C₀` of `k` pages and a finite list of requests. The order of the list only breaks ties between simultaneous choices. -/
structure Instance (Page : Type*) [Fintype Page] where
  weight : Page → ℝ
  weight_pos : ∀ p, 0 < weight p
  cacheSize : ℕ
  cacheSize_pos : 0 < cacheSize
  cacheSize_lt : cacheSize < Fintype.card Page
  initialCache : Finset Page
  initialCache_card : initialCache.card = cacheSize
  requests : List (Request Page)

namespace Instance

variable {Page : Type*} [Fintype Page]

/-- The total weight `∑ᵢ wᵢ` of all pages. -/
noncomputable def totalWeight (input : Instance Page) : ℝ :=
  ∑ p, input.weight p

/-- The instance as known at time `t`: the requests that have arrived by `t` (with their delay functions); weights, cache size and initial cache are known from the start. -/
noncomputable def upTo (input : Instance Page) (t : ℝ) : Instance Page :=
  { input with requests := input.requests.filter fun ρ => decide (ρ.arrival ≤ t) }

end Instance

/-! ## Schedules -/

/-- A step of a schedule: at `time`, the cache is replaced by `cache`. -/
structure Step (Page : Type*) where
  time : ℝ
  cache : Finset Page

/-- A schedule: a finite list of steps, starting from the initial cache. Several steps may have the same time: the schedule then goes through several caches at one instant, ending with the cache of the last of these steps. -/
abbrev Schedule (Page : Type*) := List (Step Page)

namespace Schedule

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The fetch cost of `S` starting from the cache `C`: every step pays the weights of the pages it adds to the cache. -/
noncomputable def costFrom (weight : Page → ℝ) : Finset Page → Schedule Page → ℝ
  | _, [] => 0
  | C, step :: rest => (∑ p ∈ step.cache \ C, weight p) + costFrom weight step.cache rest

/-- The fetch cost of `S`, starting from the initial cache. -/
noncomputable def fetchCost (input : Instance Page) (S : Schedule Page) : ℝ :=
  costFrom input.weight input.initialCache S

/-- Page `p` is cached by `S` at time `s`: it is in one of the caches that `S` goes through at time `s`. The initial cache is present until the time of the first step, and the cache of step `j` from its time to the time of step `j + 1` (forever, if `j` is the last step). -/
def CachedAt (input : Instance Page) (S : Schedule Page) (p : Page) (s : ℝ) : Prop :=
  (p ∈ input.initialCache ∧ ∀ step ∈ S.head?, s ≤ step.time) ∨
    ∃ (j : ℕ) (h : j < S.length), S[j].time ≤ s ∧
      (∀ step ∈ S[j + 1]?, s ≤ step.time) ∧ p ∈ S[j].cache

/-- A feasible schedule: steps in chronological order, at most `k` pages cached, and every request served, i.e., its page is cached at some time after its arrival. -/
structure Feasible (input : Instance Page) (S : Schedule Page) : Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  capacity : ∀ step ∈ S, step.cache.card ≤ input.cacheSize
  serves : ∀ ρ ∈ input.requests, ∃ s, ρ.arrival ≤ s ∧ CachedAt input S ρ.page s

/-- The time at which `S` serves the request `ρ`: the first time `τ ≥ a_ρ` at which its page is cached. -/
noncomputable def serviceTime (input : Instance Page) (S : Schedule Page) (ρ : Request Page) : ℝ :=
  sInf {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ}

/-- The cost of `S`: its fetch cost plus the delay cost `∑_ρ d_ρ(τ_ρ - a_ρ)`. -/
noncomputable def cost (input : Instance Page) (S : Schedule Page) : ℝ :=
  fetchCost input S +
    (input.requests.map fun ρ => ρ.delay (serviceTime input S ρ - ρ.arrival)).sum

/-- The steps up to time `t`. -/
noncomputable def upTo (S : Schedule Page) (t : ℝ) : Schedule Page :=
  S.filter fun step => decide (step.time ≤ t)

end Schedule

/-! ## Randomized algorithms

A randomized algorithm turns every instance into a probability distribution on schedules. It is *online* if the distribution of its steps up to any time `t` depends only on the requests revealed by time `t`; then its steps up to `t` can be drawn at time `t`, conditionally on the steps drawn before. Since the delay functions are revealed on arrival, online algorithms are clairvoyant. -/

/-- A randomized algorithm: a distribution on schedules for every instance. -/
abbrev RandAlgorithm (Page : Type*) [Fintype Page] := Instance Page → PMF (Schedule Page)

namespace RandAlgorithm

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- **Online**: the distribution of the steps up to time `t` depends only on the requests revealed by time `t`. -/
def Online (alg : RandAlgorithm Page) : Prop :=
  ∀ (first second : Instance Page) (t : ℝ), first.upTo t = second.upTo t →
    (alg first).map (Schedule.upTo · t) = (alg second).map (Schedule.upTo · t)

/-- **Feasible**: with probability `1`, the schedule is feasible (so every request is served). -/
def Feasible (alg : RandAlgorithm Page) : Prop :=
  ∀ (input : Instance Page), ∀ S ∈ (alg input).support, S.Feasible input

/-- The expected cost `E[cost(S)]` of the random schedule `S`. -/
noncomputable def expectedCost (alg : RandAlgorithm Page) (input : Instance Page) : ENNReal :=
  ∑' S, alg input S * ENNReal.ofReal (S.cost input)

end RandAlgorithm

end PagingWithDelay
