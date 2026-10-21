import PagingWithDelay.Analysis.AlgDelay.Overshoot
import PagingWithDelay.Analysis.Cost

/-!
# `prop:algdelay`: the delay cost of `PMD`

**`prop:algdelay`** (`delayCost_le`): the fractional delay cost of `PMD` is at most `C_fetch + 5 ∑_λ |λ|`.

Proof, following the paper:
* `delayCost_le_sum_visitDelay` (`AlgDelay/Bridge.lean`): every request with positive fractional delay cost is pending until a visit of its page, and its weight `α_ρ` is at most `x_p - δ` right before that visit (`obs:monotone`); so the delay cost is at most `∑_visits (x_p - δ) · delay_p(t)`.
* `visitDelay_le` (`AlgDelay/Visit.lean`): a visit pays at most `c_p + (x_p - δ) w_p + ō_p`, and `(x_p - δ) w_p` is its fetch cost; the fetch costs of all visits are at most `C_fetch` (`CostProof.fetchTotal_add_tripTotal_le_fetchCost`).
* `sum_claimAt_le` (`AlgDelay/Visit.lean`): the used delays `c_p` sum to at most `∑_λ |λ| / L ≤ ∑_λ |λ|`.
* `sum_overAt_le` (`AlgDelay/Overshoot.lean`): the overshoots `ō_p` sum to at most `2 ∑_λ |λ| + 2H`, where `H` is the total payment for holes.
* `H` is paid from the budgets, so `H ≤ ∑_λ |λ|` (`CostProof.holeTotal_add_tripTotal_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

variable {input : Instance Page}

/-- **`prop:algdelay`**: the fractional delay cost of `PMD` is at most its fetch cost plus `5` times the total length of its critical services. -/
theorem delayCost_le (hv : input.Valid) :
    FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) + 5 * lenTotal input := by
  have h1 := delayCost_le_sum_visitDelay hv
  have h2 : ∑ j ∈ Finset.range (log input).length, visitDelay input j ≤
      ∑ j ∈ Finset.range (log input).length,
        (claimAt input j + (fetchAt input j + tripAt input j) + overAt input j) :=
    Finset.sum_le_sum fun j _ => visitDelay_le hv j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
  have h3 := sum_claimAt_le hv
  have h4 := sum_overAt_le hv
  have hfetch := CostProof.fetchTotal_add_tripTotal_le_fetchCost hv
  have hH := CostProof.holeTotal_add_tripTotal_le hv
  have hR := CostProof.tripTotal_nonneg hv
  have hΛ := CostProof.lenTotal_nonneg hv
  have hc : lenTotal input / L ≤ lenTotal input := div_le_self hΛ (Instance.one_le_L hv)
  unfold fetchTotal tripTotal at *
  linarith

end PagingWithDelay.PMD.DelayProof
