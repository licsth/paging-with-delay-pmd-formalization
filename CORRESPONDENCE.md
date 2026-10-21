# Correspondence between the paper and the Lean proofs

Every theorem, lemma, proposition, corollary and observation of the paper ([arXiv:2610.24655](https://arxiv.org/abs/2610.24655)), with the Lean declarations that prove it. Results are referred to by their labels in the LaTeX source of the paper, which is available on arXiv. Paths are relative to `PagingWithDelay/`, names are relative to the namespace `PagingWithDelay`.

The comparator `OPT` is an arbitrary feasible schedule `S`. Most bounds use service times `σ` with `S.FeasibleBy input σ` (`S` serves each request `ρ` in `[a_ρ, σ ρ]`), and `S` in swap form (`Schedule.SwapForm`, obtained by `Schedule.exists_swapForm`). Then `OPT` reads `S.fetchCost input + Schedule.totalDelay input σ` and `w(OPT_0)` reads `∑ p ∈ input.initialCache, w p`. Sums over critical services are sums over the log entries: `fetchTotal` is `C_fetch^crit`, `lenTotal` is `∑_ν |λ^(ν)|`, `evTotal` is `∑_ν EV(λ^(ν))` (`Analysis/Defs.lean`).

## Section 1: Introduction

### `thm:main`
* `weightedPagingWithDelay_competitive` (`../PagingWithDelay.lean`): there is an online, feasible randomized algorithm with `E[cost] ≤ (6900 ln k + 17940) · cost(S) + (6900 ln k + 19210) · ∑ wᵢ` for every feasible `S`.
* The algorithm is `randomizedPMD` (`Randomized.lean`): `PMD` on the weights rounded up to powers of two, then rounded online. The bound with `L = ln(2k+1)` is `PMD.RandomizedProof.expectedCost_le`; `PMD.RandomizedProof.expectedCost_le_log` replaces `L` by `ln k + 1.1`.
* Online and feasible: `PMD.RandomizedProof.randomizedPMD_online`, `PMD.RandomizedProof.randomizedPMD_feasible`.

## Section 3: Algorithm definition

### `lem:inv`
* (a) `PMD.Inv` (`Run/Invariant.lean`) is the run invariant: its field `rest` says that the state outside preemptive services lies in `[δ, 1]ⁿ` with total `n - k`, `budget` says `B_W ≥ 0`, and `preempt` describes the state during a preemptive service. It holds initially (`PMD.inv_initial`) and is preserved by every move (`PMD.Inv.step`).
* (a) and (b) for the output: `PMD.preemptiveMirrorDescent_feasible` (`Run/Feasible.lean`): every waypoint lies in `[δ, 1]ⁿ` with total at least `n - k`, the waypoints are chronological, and every request is served.

## Section 4: Reducing to fetch cost of critical service

### `lem:lengthfetch`
* `PMD.CostProof.lenTotal_le_fetchTotal` (`Analysis/Cost.lean`): `∑_ν |λ^(ν)| ≤ 3 C_fetch^crit + 3 ∑ wᵢ`.

### `lem:clock`
* `PMD.serviceEnd_le_three_mul_criticalEV` (`Critical.lean`): `|λ_{x→p}| ≤ 3 EV(λ_{x→p})`.
* Summed over the critical services: `PMD.CostProof.lenTotal_le`.

### `lem:evfetch`
* `PMD.CostProof.evTotal_le` (`Analysis/Cost.lean`): `∑_ν EV(λ^(ν)) ≤ C_fetch^crit + ∑ wᵢ`.

### `prop:preemptfetch`
* `PMD.CostProof.fetchCost_le_lenTotal` (`Analysis/Cost.lean`): `C_fetch ≤ C_fetch^crit + ∑_ν |λ^(ν)|`.
* Its two steps: `PMD.CostProof.fetchCost_le_preempt` (the fetch cost is at most the critical fetches plus the payments for holes and round trips) and `PMD.CostProof.holeTotal_add_tripTotal_le` (the payments are at most `∑_ν |λ^(ν)|`).
* Combined with `lem:lengthfetch`: `PMD.CostProof.fetchCost_le`, `C_fetch ≤ 4 C_fetch^crit + 3 ∑ wᵢ`.
* The converse used in `prop:algdelay`, that the fetch costs of the critical services and round trips are at most `C_fetch`: `PMD.CostProof.fetchTotal_add_tripTotal_le_fetchCost`.

### `obs:monotone`
* `PMD.baseState_mono`, `PMD.baseState_le_x` and `PMD.baseState_le_x_of_mono` (`Run/Basic.lean`), and `PMD.Inv.baseOf_le_next` (`Run/Invariant.lean`).
* Difference: the paper's first sentence is false as stated, since closing a hole lowers `x_p` from its in-hole value. Lean proves it for the base state (the state outside preemptive services), which is what the proofs use. The second sentence (`x_p - δ ≥ α_r` until `r` is served) is used in `PMD.DelayProof.delayCost_le_sum_visitDelay` (`Analysis/AlgDelay/Bridge.lean`).

### `lem:drop`
* `PMD.serviceEnd_le_add_serviceEnd` (`Critical.lean`): `|λ_{x→q}| ≤ |λ_{x→p}| + |λ_{x̃→q}|` for `q ≠ p` with `x_q > δ`.
* Iterated along chains of critical services: `PMD.serviceEnd_le_chainLen_add`.

### `prop:algdelay`
* `PMD.DelayProof.delayCost_le` (`Analysis/AlgDelay.lean`): `C_delay ≤ C_fetch + 5 ∑_ν |λ^(ν)|`. The proof is split over `Analysis/AlgDelay/{Run,Bridge,Visit,Overshoot}.lean`.
* The claims: `PMD.DelayProof.sum_claimAt_le`, `∑ c ≤ ∑_ν |λ^(ν)| / L`. The overshoots: `PMD.DelayProof.sum_overAt_le`, `∑ o ≤ 2 ∑_ν |λ^(ν)| + 2H`, with `eq:prop11_critical_service` and `eq:prop11_preemptive_service` in `PMD.DelayProof.serviceEnd_le_block`.

### `prop:cost`
* `PMD.MainProof.cost_le` (`Main.lean`): `C_fetch + C_delay ≤ 23 C_fetch^crit + 21 ∑ wᵢ`.
* Difference: Lean states the bound in terms of `C_fetch^crit` instead of assuming `C_fetch^crit ≤ ρ OPT + c`; substituting gives the paper's `23ρ` and `c' = 23c + 21 ∑ wᵢ`.

## Section 5: The Bregman potential

The potential `D(OPT‖x)` is `PMD.divergence` (`Critical/Divergence.lean`).

### `obs:evictions`
* `Schedule.sum_evicted_le` (`Opt.lean`): the total weight of the evictions of `S` is at most its fetch cost plus `w(OPT_0)`.

### `lem:optmoves`
* `PMD.divergence_change_cache` (`Critical/Divergence.lean`): one change of the comparator's cache from `O` to `O'` increases `D` by at most `L · w(O \ O') + w(O' \ O)`.
* `PMD.TeleProof.window_divergence_le` (`Analysis/Telescope.lean`): the same for all steps of `S` between two log entries.
* Summed and combined with `obs:evictions` inside `PMD.TeleProof.fetchTotal_le`: the total increase is at most `(L + 1) S.fetchCost + L w(OPT_0)`.

### `prop:phaseD`
* Hit service: `PMD.critical_hit` (`Critical/Divergence.lean`): `ΔD ≤ -fetch(λ)`.
* Miss service: `PMD.TeleProof.critical_miss_len` (`Analysis/Telescope.lean`): `ΔD ≤ 2L w_p + ∑ |λ|_W` over the levels `W` below every weight in the comparator's cache, which is `Exc(ν)` (`PMD.excessAt`).
* Both cases at one log entry: `PMD.TeleProof.entry_divergence_le`, `ΔD ≤ -fetch + (2L + 1) missW + Exc`.

## Section 6: Charging to OPT

### `lem:chargeable`
* `PMD.TeleProof.sum_chargeW_le` (`Analysis/Chargeable.lean`): the weights of the chargeable visits (`PMD.IsChargeable`, `def:chargeable`) sum to at most `S.fetchCost + w(OPT_0) + totalDelay`.
* The comparator side (charging to the last eviction): `Schedule.exists_lastEviction` (`Opt.lean`).

### `lem:miss`
* `PMD.MainProof.sum_missW_le` (`Main.lean`): `∑_{ν ∈ Miss} w_{p^(ν)} ≤ OPT + w(OPT_0)`.
* Its step: `PMD.TeleProof.missW_le_chargeW` (`Analysis/Chargeable.lean`): every miss service is a chargeable visit.

### `prop:tele`
* `PMD.MainProof.fetchTotal_le_excess` (`Main.lean`): `C_fetch^crit ≤ (3L + 2) OPT + Exc + (4L + 2) ∑ wᵢ`.
* The potential argument before applying `lem:miss`: `PMD.TeleProof.fetchTotal_le` (`Analysis/Telescope.lean`), `C_fetch^crit ≤ (L + 1) S.fetchCost + L w(OPT_0) + (L + 1) ∑ wᵢ + (2L + 1) ∑ missW + Exc`.

## Section 7: Bounding the excess

### `lem:timely`
* `PMD.NotOverdueProof.sum_excess_notOverdue_le` (`Analysis/NotOverdue.lean`): the excess of the services that are not overdue (`PMD.IsOverdue`) is at most `L · totalDelay`.

### `obs:servedbefore`
* `PMD.ExcessProof.servedBy_start` (`Analysis/PeriodLevel.lean`): a request on a page outside the comparator's cache of a period that the comparator has served by a time of the period was served by the start of the period.
* The underlying fact about quiet windows: `Schedule.servedBy_of_quiet` (`Opt.lean`).

### `lem:early`
* `PMD.ExcessProof.early_spec` (`Analysis/PeriodLevel.lean`): before a light service of the period, every level-`W` round trip of the period is chargeable, and every level-`W` preemptive service that closes its hole stops with `B_W < W`.

### `lem:periodlevel`
* `PMD.ExcessProof.periodLevel_sum` (`Analysis/PeriodLevel.lean`): `∑ |λ|_W` over the light services of one period and level is at most `4W + (3/2) C_{j,W} + L W`.
* The budget argument: `PMD.ExcessProof.two_pay_le` and `PMD.ExcessProof.budget_lt_of_next_critical` (`Analysis/Money.lean`).

### `lem:lightest`
* `Schedule.sum_stepTimes_le` (`Opt.lean`): if `m τ` is at most the weight of every page in the cache at the step time `τ`, then `∑_τ m τ ≤ S.fetchCost`.

### `prop:excess`
* `PMD.MainProof.excess_le` (`Main.lean`): `Exc ≤ L · OPT + (3/2)(OPT + w(OPT_0)) + (L + 4)(OPT + w(OPT_0))`, the last display of the proof.
* Its parts: `lem:timely`, `PMD.ExcessProof.sum_excess_overdue_le` (`Analysis/Excess.lean`, the overdue services: `≤ (3/2) ∑ (weights of chargeable round trips) + (L + 4) S.fetchCost`), and `lem:chargeable` for the chargeable round trips.

## Section 8: Proof of the main theorem

### Proof of `thm:main`, first display
* `PMD.MainProof.fetchTotal_le` (`Main.lean`): `prop:tele` and `prop:excess` give `C_fetch^crit ≤ (5L + 15/2) OPT + (5L + 15/2) ∑ wᵢ`; with `prop:cost`, `PMD.MainProof.fracCost_le` below.

### `prop:rounding`
* `Rounding.expectedCost_le` (`Rounding/Schedule.lean`): for power-of-two weights, the rounded schedule has expected cost at most `30 C_fetch + 3 C_delay + 5 ∑ wᵢ`.
* Served with probability `1`: `Rounding.feasible_of_mem_support`; online: `Rounding.randomSchedule_upTo`.
* The fractional bound it is applied to: `PMD.MainProof.fracCost_le` (`Main.lean`), `C_fetch + C_delay ≤ (115L + 345/2) cost(S) + (115L + 387/2) ∑ wᵢ`, with `PMD.preemptiveMirrorDescent_online` (`Run/Online.lean`) and `PMD.preemptiveMirrorDescent_feasible`.
* Rounding the weights to powers of two: `Rounded.lean`.

## Appendix A: Rounding

### `thm:bbn`
* `bansalBuchbinderNaor` (`BBN.lean`), an axiom stating `BBN.Statement`. It is the only assumption of the formalization. It also asserts that `𝒟` contains the distribution concentrated on any cache, a fact from the proof of Bansal, Buchbinder and Naor.

### `cor:rounding`
* `Rounding.onlineRounding` (`Rounding/Chain.lean`), from `thm:bbn` via `Rounding.joint_spec`.

### `lem:map`
* `Rounding.zmap` (`Rounding/Map.lean`) is the map `x ↦ z`.
* `Rounding.zmap_mem_fracCaches_le`: `z ∈ [0, 1]ⁿ` and `∑ zᵢ ≤ k`.
* `Rounding.zmap_eq_one`: `zᵢ = 1` if `xᵢ = δ`.
* `Rounding.zmap_sub_le`: `zᵢ` is nonincreasing and `3`-Lipschitz in `xᵢ`.

## Definitions

| paper | Lean |
| --- | --- |
| `sec:problem` (instances, schedules, cost) | `Model.lean` |
| `alg:PMD`, `sec:alg` | `preemptiveMirrorDescent` (`Algorithm.lean`) |
| `def:fracfetch` | `FracSchedule.fetchCost` (`Fractional.lean`) |
| `def:fracdelay` | `FracSchedule.delayCost` (`Fractional.lean`) |
| hit and miss services | `PMD.missW` (`Analysis/Defs.lean`) |
| excess | `PMD.excessAt` (`Analysis/Defs.lean`) |
| `def:chargeable` | `PMD.IsChargeable` (`Analysis/Defs.lean`) |
| overdue pages and services | `PMD.IsOverdue` (`Analysis/Defs.lean`) |
| periods | `Schedule.InPer` (`Opt.lean`) |
| early part, light services | the entries of a period before one of its light services `PMD.ExcessProof.lightServices` (`Analysis/PeriodLevel.lean`) |
