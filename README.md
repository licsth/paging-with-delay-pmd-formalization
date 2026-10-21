# Lean formalization: weighted paging with delay via mirror descent

This repository formalizes, in Lean 4 + Mathlib, the main theorem of the arXiv article _Tight weighted paging with delay via mirror descent_ ([arXiv:2610.24655](https://arxiv.org/abs/2610.24655)): there is an `O(log k)`-competitive randomized online algorithm for weighted paging with delay. The only result that is assumed without proof is the online rounding theorem of Bansal, Buchbinder and Naor.

## The main theorem

`PagingWithDelay.weightedPagingWithDelay_competitive` (in [`PagingWithDelay.lean`](PagingWithDelay.lean)) states: there is a randomized algorithm that is

- **online**: the distribution of its steps up to time `t` depends only on the requests that have arrived by time `t`, and
- **feasible**: with probability `1`, it never holds more than `k` pages and serves every request,

and for every instance and every feasible schedule `S` (in particular an optimal one),

```text
E[cost] ≤ (6900 ln k + 17940) · cost(S) + (6900 ln k + 19210) · ∑ᵢ wᵢ.
```

In Lean:

```lean
theorem weightedPagingWithDelay_competitive {Page : Type*} [Fintype Page] [DecidableEq Page] :
    ∃ alg : RandAlgorithm Page, alg.Online ∧ alg.Feasible ∧
      ∀ (input : Instance Page) (S : Schedule Page), S.Feasible input →
        alg.expectedCost input ≤
          ENNReal.ofReal ((6900 * Real.log input.cacheSize + 17940) * S.cost input +
            (6900 * Real.log input.cacheSize + 19210) * input.totalWeight)
```

The additive term `O(log k) · ∑ᵢ wᵢ` depends only on the weights, not on the requests, so this is a competitive ratio of `O(log k)`.

## How to check it

A reader has to check that the statement says what it should and that the proof uses no hidden assumptions. The Lean kernel checks the rest.

### 1. Read the trusted files (about 220 lines)

- [`PagingWithDelay.lean`](PagingWithDelay.lean): the statement above.
- [`PagingWithDelay/Model.lean`](PagingWithDelay/Model.lean): every definition that the statement mentions: requests and instances, schedules, their feasibility and cost, randomized algorithms, online, feasible and expected cost. It uses no custom notation.
- [`PagingWithDelay/BBN.lean`](PagingWithDelay/BBN.lean): the assumption, the online rounding theorem of Bansal, Buchbinder and Naor (Theorem 4.1 of _A primal-dual randomized algorithm for weighted paging_), stated as an axiom.

`Model.lean` and `BBN.lean` import only [`PagingWithDelay/Imports.lean`](PagingWithDelay/Imports.lean), a list of Mathlib modules. Everything else is proof. This includes the algorithm itself: the theorem asserts that an algorithm _exists_, so its definition does not need to be checked.

### 2. Build the proof

Install Lean via [elan](https://github.com/leanprover/elan); the toolchain (`lean-toolchain`) and Mathlib version (`lake-manifest.json`) are pinned. Then run

```sh
lake exe cache get   # download compiled Mathlib
lake build
```

The build succeeds without errors. The library contains no `sorry`, `native_decide` or `unsafe`.

### 3. Check the axioms

Create a file `Axioms.lean` containing

```lean
import PagingWithDelay
#print axioms PagingWithDelay.weightedPagingWithDelay_competitive
```

and run `lake env lean Axioms.lean`. The output lists `propext`, `Classical.choice` and `Quot.sound` (the standard axioms of Lean and Mathlib) and `PagingWithDelay.bansalBuchbinderNaor` (the assumption), and nothing else.

## Modelling choices

[`Model.lean`](PagingWithDelay/Model.lean) transcribes the paper's problem definition: positive weights, `0 < k < n`, an initial cache of `k` pages, and requests `(p, a, d)` with `d` nondecreasing, continuous and unbounded, `d(0) = 0`. The following modelling decisions are not immediate from the paper's definitions:

- **Schedules** are finite lists of steps `(time, cache)` with at most `k` pages each. A step pays the weights of the pages it adds, and several steps may have the same time. A page is cached at time `s` if it is in some configuration the schedule goes through at `s` (`Schedule.CachedAt`). A request is served at the first such time `s ≥ a_r` and costs `d_r(s - a_r)`.
- **The comparator** is any feasible schedule (which does not have to be online), so the bound holds for an optimal one. It is proved (`Schedule.exists_swapForm`) that there exists a lazy optimal comparator.
- **Online** (`RandAlgorithm.Online`): instances with the same requests of arrival time `≤ t` give the same distribution of the steps up to time `t`. So the algorithm sees a request, including its delay function, at its arrival time. Randomized algorithms are discrete distributions (`PMF`) on schedules, _feasible_ means feasible with probability `1`.
- **The assumption** (`BBN.Statement` in [`BBN.lean`](PagingWithDelay/BBN.lean)) is the online rounding theorem of Bansal, Buchbinder and Naor as stated in the paper's appendix. A transition from `Q` to `Q'` is a joint distribution with marginals `Q` and `Q'` that pays `wᵢ/2` per fetched and per evicted page. "`cost(Q, Q')` is at most `c`" becomes "some transition costs at most `c`". As in the paper, which takes this from BBN's proof, `𝒟` also contains the distribution concentrated on any cache state.

## The proof

The algorithm (`randomizedPMD` in [`PagingWithDelay/Randomized.lean`](PagingWithDelay/Randomized.lean)) rounds the weights up to powers of two, runs the fractional algorithm PMD (preemptive mirror descent, [`PagingWithDelay/Algorithm.lean`](PagingWithDelay/Algorithm.lean)), and rounds its output online with the theorem of Bansal, Buchbinder and Naor. With `L = ln(2k+1)`, the fractional analysis shows that PMD is online and feasible and that its fetch and delay cost satisfy (`PMD.MainProof.fracCost_le`, which does not use the online rounding assumption of Bansal, Buchbinder and Naor):

```text
C_fetch + C_delay ≤ (115 L + 345/2) · cost(S) + (115 L + 387/2) · ∑ᵢ wᵢ.
```

The rounding then gives `E[cost] ≤ (6900 L + 10350) · cost(S) + (6900 L + 11620) · ∑ᵢ wᵢ` (`PMD.RandomizedProof.expectedCost_le`), and the main theorem follows from `L < ln k + 1.1`.
Note that our analysis is not optimized for constants, but for simplicity and clarity. The constants can be improved in multiple places through a more careful analysis.

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) lists, for each result of the paper, the Lean declarations that prove it.

### Differences from the paper

The algorithm follows the paper's description of PMD. The differences, explained in the header of [`Algorithm.lean`](PagingWithDelay/Algorithm.lean), are:

- **Ties** are broken by a fixed order of the pages and of the pending requests.
- **Levels** are only examined between `w_min` and `w_max`; no other level ever receives a deposit.

The proofs follow the paper's proofs, including their estimates, so the explicit constants of the paper's results are the constants in Lean. Where the paper writes `O(·)`, Lean uses the constants that the paper's proof gives.

## AI disclosure

The Lean code and its documentation were written by Claude Opus 5.5.
The authors guided the design and independently verified the correctness of the Lean modelling of randomized weighted paging with delay.
