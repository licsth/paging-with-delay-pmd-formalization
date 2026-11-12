import PagingWithDelay
import PagingWithDelay.Deadlines.Model
import PagingWithDelay.Deadlines.Simulation

/-!
# Paging with deadlines

Competitive bounds for paging with delay carry over to paging with deadlines, by simulating the delay algorithm in virtual time (`Deadlines/Simulation.lean`).
-/

namespace PagingWithDelay

/-- A competitive online algorithm for paging with delay gives one for paging with deadlines with the same bound. -/
theorem pagingWithDeadlines_of_pagingWithDelay {Page : Type*} [Fintype Page] [DecidableEq Page]
    (α β : ℕ → ℝ)
    (h : ∃ alg : RandAlgorithm Page, alg.Online ∧ alg.Feasible ∧
      ∀ (input : Instance Page) (S : Schedule Page), S.Feasible input →
        alg.expectedCost input ≤
          ENNReal.ofReal (α input.cacheSize * S.cost input + β input.cacheSize * input.totalWeight)) :
    ∃ alg : DeadlineAlgorithm Page, alg.Online ∧ alg.Feasible ∧
      ∀ (input : DeadlineInstance Page) (S : Schedule Page), input.Feasible S →
        alg.expectedCost input ≤
          ENNReal.ofReal (α input.cacheSize * input.cost S + β input.cacheSize * input.totalWeight) := by
  obtain ⟨alg, hon, hfeas, hcost⟩ := h
  exact ⟨Deadlines.simulation alg, Deadlines.simulation_competitive alg hon hfeas α β hcost⟩

/-- An `O(log k)`-competitive online algorithm for weighted paging with deadlines. -/
theorem weightedPagingWithDeadlines_competitive {Page : Type*} [Fintype Page] [DecidableEq Page] :
    ∃ alg : DeadlineAlgorithm Page, alg.Online ∧ alg.Feasible ∧
      ∀ (input : DeadlineInstance Page) (S : Schedule Page), input.Feasible S →
        alg.expectedCost input ≤
          ENNReal.ofReal ((6900 * Real.log input.cacheSize + 17940) * input.cost S +
            (6900 * Real.log input.cacheSize + 19210) * input.totalWeight) :=
  pagingWithDeadlines_of_pagingWithDelay (fun k => 6900 * Real.log k + 17940)
    (fun k => 6900 * Real.log k + 19210) weightedPagingWithDelay_competitive

end PagingWithDelay
