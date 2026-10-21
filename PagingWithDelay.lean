import PagingWithDelay.Model
import PagingWithDelay.BBN
import PagingWithDelay.Randomized

/-!
# Tight weighted paging with delay via mirror descent

A Lean formalization of the main theorem of `paper/paper.tex`. A human reader needs to check only:
* this file: the statement;
* `PagingWithDelay/Model.lean`: the definitions that the statement mentions (requests, instances, schedules and their cost, randomized algorithms);
* `PagingWithDelay/BBN.lean`: the only assumption, the online rounding theorem of Bansal, Buchbinder and Naor (Theorem 4.1 of their paper, restated in the appendix "Rounding" of the paper), stated as an axiom.

Both files import only `PagingWithDelay/Imports.lean`, a list of Mathlib modules. Everything else is proof; `#print axioms weightedPagingWithDelay_competitive` confirms that it uses no assumption besides `bansalBuchbinderNaor` (and the standard axioms `propext`, `Classical.choice`, `Quot.sound`).
-/

namespace PagingWithDelay

/-- **Main theorem** (stated in "Our results" in the introduction of the paper): there exists a clairvoyant randomized online algorithm for weighted paging with delay with competitive ratio `O(log k)`.

Concretely: there is a randomized algorithm `alg` that is
* online: the distribution of its steps up to time `t` depends only on the requests that have arrived by time `t` (clairvoyant: a request's delay cost function is known from its arrival on);
* feasible: with probability `1`, it never holds more than `k` pages and serves every request;

and for every instance and every feasible schedule `S` (in particular an optimal one), with `k` the cache size, `E[cost(alg)] ≤ (6900 ln k + 17940) · cost(S) + (6900 ln k + 19210) · ∑ᵢ wᵢ`.

The expected cost is a sum in `ℝ≥0∞`: every schedule has finite cost, but a distribution on infinitely many schedules can have infinite expected cost, and in `ℝ` such a divergent sum would be `0` by convention. `ENNReal.ofReal` only casts the (nonnegative) right-hand side to `ℝ≥0∞`. -/
theorem weightedPagingWithDelay_competitive {Page : Type*} [Fintype Page] [DecidableEq Page] :
    ∃ alg : RandAlgorithm Page, alg.Online ∧ alg.Feasible ∧
      ∀ (input : Instance Page) (S : Schedule Page), S.Feasible input →
        alg.expectedCost input ≤
          ENNReal.ofReal ((6900 * Real.log input.cacheSize + 17940) * S.cost input +
            (6900 * Real.log input.cacheSize + 19210) * input.totalWeight) :=
  ⟨randomizedPMD, PMD.RandomizedProof.randomizedPMD_online,
    PMD.RandomizedProof.randomizedPMD_feasible, PMD.RandomizedProof.expectedCost_le_log⟩

end PagingWithDelay
