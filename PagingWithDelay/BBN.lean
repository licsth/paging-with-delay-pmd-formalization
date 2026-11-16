import PagingWithDelay.BBN.Rounding

/-!
# Online rounding for weighted paging (Bansal–Buchbinder–Naor)

The online rounding theorem of Bansal, Buchbinder and Naor for weighted paging (*A primal-dual randomized algorithm for weighted paging*, Theorem 4.1), in the form in which the appendix "Rounding" of the paper uses it (with `Q'`, `y'` for the paper's `Q̃`, `ỹ`). It is proved in `PagingWithDelay/BBN/`, which formalizes the proof of Bansal, Buchbinder and Naor.

* A *cache state* is a set of `k` pages. `Q`, `Q'` are probability distributions on sets of pages (`PMF (Finset Page)`) that give positive probability only to cache states.
* `𝒫` (`fracCaches k`): the *distributions on pages* `y ∈ [0,1]ⁿ` with `∑ᵢ yᵢ = k`; `yᵢ` is the cached mass of page `i`.
* `Π(Q)` (`marginal Q`): `Π(Q)ᵢ` is the probability that page `i` is in the random cache with distribution `Q`.
* A *transition* from `Q` to `Q'` is a joint distribution `π` of the cache `C` before and the cache `C'` after it, with marginals `Q` and `Q'`. Its expected fetch cost (`fetchCost`) charges `wᵢ` for every fetched page `i ∈ C' \ C`.

The paper states Theorem 4.1 as `cost(Q, Q') ≤ 5 cost_f(y, y')`, where both costs charge `wᵢ/2` per fetched and per evicted page, and its proof of the online rounding corollary only uses the consequence that the expected fetch cost is at most `5 ∑ᵢ wᵢ |y'ᵢ - yᵢ|`. The version proved here bounds the expected fetch cost directly, by `4 ∑ᵢ wᵢ |y'ᵢ - yᵢ|`. As in the paper (which takes this from the proof of Theorem 4.1), `𝒟` contains the distribution concentrated on any cache state.
-/

namespace PagingWithDelay

namespace BBN

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- `Q` is a distribution on cache states: every set of pages that it gives positive probability has exactly `k` pages. -/
def OnCacheStates (k : ℕ) (Q : PMF (Finset Page)) : Prop :=
  ∀ C ∈ Q.support, C.card = k

/-- The expected fetch cost of the transition `π` (a joint distribution of the cache `C` before and the cache `C'` after it): `wᵢ` for every fetched page `i ∈ C' \ C`. -/
noncomputable def fetchCost (w : Page → ℝ) (π : PMF (Finset Page × Finset Page)) : ℝ :=
  ∑ CC : Finset Page × Finset Page, (π CC).toReal * ∑ i ∈ CC.2 \ CC.1, w i

/-- The online rounding theorem of Bansal, Buchbinder and Naor (Theorem 4.1 of their paper, in the form used in the appendix "Rounding"): for positive weights such that any two distinct weights differ by a factor of at least `2`, and every cache size `k`, there are a class `𝒟` of distributions on cache states and a map `T : 𝒟 × 𝒫 → 𝒟` such that for all `y, y' ∈ 𝒫` and `Q ∈ 𝒟` with `Π(Q) = y`, the distribution `Q' = T(Q, y')` lies in `𝒟`, has `Π(Q') = y'`, and some transition from `Q` to `Q'` has expected fetch cost at most `4 ∑ᵢ wᵢ |y'ᵢ - yᵢ|`. Moreover `𝒟` contains the distribution concentrated on any cache state. -/
def Statement (Page : Type*) [Fintype Page] [DecidableEq Page] : Prop :=
  ∀ (w : Page → ℝ) (k : ℕ), (∀ i, 0 < w i) → (∀ i j, w i < w j → 2 * w i ≤ w j) →
    ∃ (D : Set (PMF (Finset Page))) (T : PMF (Finset Page) → (Page → ℝ) → PMF (Finset Page)),
      (∀ Q ∈ D, OnCacheStates k Q) ∧
      (∀ C : Finset Page, C.card = k → PMF.pure C ∈ D) ∧
      ∀ Q ∈ D, ∀ y ∈ fracCaches k, ∀ y' ∈ fracCaches k, marginal Q = y →
        T Q y' ∈ D ∧ marginal (T Q y') = y' ∧
          ∃ π : PMF (Finset Page × Finset Page),
            π.map Prod.fst = Q ∧ π.map Prod.snd = T Q y' ∧
              fetchCost w π ≤ 4 * ∑ i, w i * |y' i - y i|

/-- The indicator vector of a cache state is a fractional cache. -/
lemma indicator_mem_fracCaches {k : ℕ} {C : Finset Page} (hC : C.card = k) :
    indicator C ∈ fracCaches k := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold indicator
    split_ifs <;> norm_num
  · simp [indicator, ← hC]

/-- The joint law of `C ∼ Q` and `C' ∼ K C`. -/
noncomputable def coupling (Q : PMF (Finset Page)) (K : Finset Page → PMF (Finset Page)) :
    PMF (Finset Page × Finset Page) :=
  Q.bind fun C => (K C).map (Prod.mk C)

lemma coupling_apply (Q : PMF (Finset Page)) (K : Finset Page → PMF (Finset Page))
    (C C' : Finset Page) : coupling Q K (C, C') = Q C * K C C' := by
  rw [coupling, PMF.bind_apply, tsum_fintype, Finset.sum_eq_single C]
  · congr 1
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single C']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro b _ hb
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_zero, mul_zero]
    intro c _
    simp [Ne.symm hb]
  · simp

end BBN

open BBN in
/-- **The online rounding theorem of Bansal, Buchbinder and Naor** (Theorem 4.1 of their paper), proved from `bbn_rounding`. -/
theorem bansalBuchbinderNaor (Page : Type*) [Fintype Page] [DecidableEq Page] :
    BBN.Statement Page := by
  intro w k hw hw2
  obtain ⟨T₀, hT₀⟩ := bbn_rounding w hw hw2 k
  refine ⟨{Q | ∃ y ∈ fracCaches k, InClass w y Q}, fun Q y' => Q.bind (T₀ Q (marginal Q) y'),
    ?_, ?_, ?_⟩
  · rintro Q ⟨y, hy, hQ⟩
    exact card_of_inClass w hy hQ
  · intro C hC
    exact ⟨_, indicator_mem_fracCaches hC, inClass_pure w C⟩
  · rintro Q ⟨y₀, -, hQ₀⟩ y hy y' hy' rfl
    have hQ : InClass w (marginal Q) Q := by
      obtain ⟨h1, h2⟩ := hQ₀
      subst h2
      exact ⟨h1, rfl⟩
    obtain ⟨hin, hcost⟩ := hT₀ Q (marginal Q) y' hy hy' hQ
    refine ⟨⟨y', hy', hin⟩, hin.2, coupling Q (T₀ Q (marginal Q) y'), ?_, ?_, ?_⟩
    · simp only [coupling, PMF.map_bind, PMF.map_comp]
      have h : ∀ C, (T₀ Q (marginal Q) y' C).map (Prod.fst ∘ Prod.mk C) = PMF.pure C :=
        fun C => PMF.map_const _ C
      simp only [h, PMF.bind_pure]
    · simp only [coupling, PMF.map_bind, PMF.map_comp]
      exact congrArg _ (funext fun C => PMF.map_id _)
    · refine le_trans (le_of_eq ?_) hcost
      rw [fetchCost, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun C' _ => ?_
      rw [coupling_apply, ENNReal.toReal_mul]

end PagingWithDelay
