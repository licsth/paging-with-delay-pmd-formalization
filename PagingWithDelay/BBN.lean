import PagingWithDelay.Imports

/-!
# The assumption: online rounding for weighted paging

The only result that this formalization assumes without proof: the online rounding theorem of Bansal, Buchbinder and Naor for weighted paging (*A primal-dual randomized algorithm for weighted paging*, Theorem 4.1), in the form and notation in which the appendix "Rounding" of the paper restates it (with `Q'`, `y'` for the paper's `Q̃`, `ỹ`).

* A *cache state* is a set of `k` pages. `Q`, `Q'` are probability distributions on sets of pages (`PMF (Finset Page)`) that give positive probability only to cache states.
* `𝒫` (`fracCaches k`): the *distributions on pages* `y ∈ [0,1]ⁿ` with `∑ᵢ yᵢ = k`; `yᵢ` is the cached mass of page `i`.
* `Π(Q)` (`marginal Q`): `Π(Q)ᵢ` is the probability that page `i` is in the random cache with distribution `Q`.
* A *transition* from `Q` to `Q'` is a joint distribution `π` of the cache `C` before and the cache `C'` after it, with marginals `Q` and `Q'`. Its expected cost (`transitionCost`) charges `wᵢ/2` for every fetched page `i ∈ C' \ C` and for every evicted page `i ∈ C \ C'`. `cost(Q, Q')` is the minimum of this over all transitions; it is attained (a linear program over a compact set), so `cost(Q, Q') ≤ c` says that some transition costs at most `c`.
* `cost_f(y, y') = ∑ᵢ (wᵢ/2) |yᵢ - y'ᵢ|` (`fracCost`).

Besides the statement of Theorem 4.1, the paper uses (in the proof of the online rounding corollary in the appendix "Rounding", citing the proof of Theorem 4.1) that `𝒟` contains a distribution whose marginals are the indicator vector of the initial cache. The only such distribution on cache states is the one concentrated on the initial cache, so we assume: `𝒟` contains the distribution concentrated on any single cache state.
-/

namespace PagingWithDelay

namespace BBN

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- `𝒫`: the fractional caches `y ∈ [0,1]ⁿ` with total cached mass `∑ᵢ yᵢ = k`. -/
def fracCaches (k : ℕ) : Set (Page → ℝ) :=
  {y | (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = k}

/-- `Q` is a distribution on cache states: every set of pages that it gives positive probability has exactly `k` pages. -/
def OnCacheStates (k : ℕ) (Q : PMF (Finset Page)) : Prop :=
  ∀ C ∈ Q.support, C.card = k

/-- The marginals `Π(Q)ᵢ = Pr_{C ∼ Q}[i ∈ C]`. -/
noncomputable def marginal (Q : PMF (Finset Page)) (i : Page) : ℝ :=
  ∑ C : Finset Page, if i ∈ C then (Q C).toReal else 0

/-- The expected cost of the transition `π` (a joint distribution of the cache `C` before and the cache `C'` after it): `wᵢ/2` for every fetched page `i ∈ C' \ C` and for every evicted page `i ∈ C \ C'`. -/
noncomputable def transitionCost (w : Page → ℝ) (π : PMF (Finset Page × Finset Page)) : ℝ :=
  ∑ CC : Finset Page × Finset Page,
    (π CC).toReal * ((∑ i ∈ CC.2 \ CC.1, w i / 2) + ∑ i ∈ CC.1 \ CC.2, w i / 2)

/-- `cost_f(y, y') = ∑ᵢ (wᵢ/2) |yᵢ - y'ᵢ|`. -/
noncomputable def fracCost (w : Page → ℝ) (y y' : Page → ℝ) : ℝ :=
  ∑ i, w i / 2 * |y i - y' i|

/-- The online rounding theorem of Bansal, Buchbinder and Naor (Theorem 4.1 of their paper, restated in the appendix "Rounding"): for positive weights such that any two distinct weights differ by a factor of at least `2` (in the paper: the distinct weights `ω₁ < ⋯ < ω_K` satisfy `ω_{i+1}/ω_i ≥ 2`), and every cache size `k`, there are a class `𝒟` of distributions on cache states and a map `T : 𝒟 × 𝒫 → 𝒟` such that for all `y, y' ∈ 𝒫` and `Q ∈ 𝒟` with `Π(Q) = y`, the distribution `Q' = T(Q, y')` lies in `𝒟`, has `Π(Q') = y'`, and `cost(Q, Q') ≤ 5 cost_f(y, y')`. Moreover `𝒟` contains the distribution concentrated on any cache state (from the proof). -/
def Statement (Page : Type*) [Fintype Page] [DecidableEq Page] : Prop :=
  ∀ (w : Page → ℝ) (k : ℕ), (∀ i, 0 < w i) → (∀ i j, w i < w j → 2 * w i ≤ w j) →
    ∃ (D : Set (PMF (Finset Page))) (T : PMF (Finset Page) → (Page → ℝ) → PMF (Finset Page)),
      (∀ Q ∈ D, OnCacheStates k Q) ∧
      (∀ C : Finset Page, C.card = k → PMF.pure C ∈ D) ∧
      ∀ Q ∈ D, ∀ y ∈ fracCaches k, ∀ y' ∈ fracCaches k, marginal Q = y →
        T Q y' ∈ D ∧ marginal (T Q y') = y' ∧
          ∃ π : PMF (Finset Page × Finset Page),
            π.map Prod.fst = Q ∧ π.map Prod.snd = T Q y' ∧
              transitionCost w π ≤ 5 * fracCost w y y'

end BBN

/-- **Assumption**: the online rounding theorem of Bansal, Buchbinder and Naor (Theorem 4.1 of their paper) holds. -/
axiom bansalBuchbinderNaor (Page : Type*) [Fintype Page] [DecidableEq Page] :
  BBN.Statement Page

end PagingWithDelay
