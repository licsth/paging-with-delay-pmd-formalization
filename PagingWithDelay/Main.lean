import PagingWithDelay.Run.Online
import PagingWithDelay.Analysis.Cost
import PagingWithDelay.Analysis.Telescope
import PagingWithDelay.Analysis.Chargeable
import PagingWithDelay.Analysis.NotOverdue
import PagingWithDelay.Analysis.Excess
import PagingWithDelay.Analysis.AlgDelay

/-!
# Assembling the bound

As in the paper: `prop:tele` (`fetchTotal_le_excess`, from `TeleProof.fetchTotal_le` and `lem:miss`) and `prop:excess` (`excess_le`, from `lem:timely`, the overdue part and `lem:chargeable`) bound `∑_λ fetch(λ)`; `prop:preemptfetch`, `lem:lengthfetch` (`CostProof`) and `prop:algdelay` bound the cost of the output in terms of `∑_λ fetch(λ)` (`prop:cost`, `cost_le`). Constants are those of the paper's displays; where the paper writes `O(·)`, they are those of its proof.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace MainProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

open Finset Classical

/-- The fetch cost of a schedule is nonnegative. -/
theorem costFrom_nonneg (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) :
    ∀ (C : Finset Page) (S : Schedule Page),
      0 ≤ Schedule.costFrom w C S
  | _, [] => le_rfl
  | C, step :: rest => by
    simp only [Schedule.costFrom]
    exact add_nonneg (sum_nonneg fun p _ => hw p) (costFrom_nonneg w hw _ rest)

open scoped InstanceNotation

/-- A chargeable round trip is a chargeable visit: `tripChargeW ≤ chargeW`. -/
theorem tripChargeW_le_chargeW (hv : input.Valid) {σ : Request Page → ℝ} {S : Schedule Page}
    (i : ℕ) : tripChargeW input σ S i ≤ chargeW input σ S i := by
  by_cases hi : i < (log input).length
  · simp only [tripChargeW, dif_pos hi]
    split
    · exact le_rfl
    · exact TeleProof.chargeW_nonneg hv i
  · simp only [tripChargeW, dif_neg hi]
    exact TeleProof.chargeW_nonneg hv i

/-- **`lem:miss`**: the weights of the miss services sum to at most `OPT + w(OPT₀)`. -/
theorem sum_missW_le (hv : input.Valid) {σ : Request Page → ℝ}
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    ∑ i ∈ range (log input).length, missW input S i ≤
      S.fetchCost input + Schedule.totalDelay input σ + ∑ p ∈ input.initialCache, w p := by
  have h1 : ∑ i ∈ range (log input).length, missW input S i ≤
      ∑ i ∈ range (log input).length, chargeW input σ S i :=
    sum_le_sum fun i _ => TeleProof.missW_le_chargeW hv hσ hF i
  have h2 := TeleProof.sum_chargeW_le hv hσ hSw hF
  linarith

/-- **`prop:excess`**: `Exc ≤ L · OPT + (3/2) (OPT + w(OPT₀)) + (L + 4) (OPT + w(OPT₀))`, the last display of the paper's proof. -/
theorem excess_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    ∑ i ∈ range (log input).length, excessAt input S i ≤
      L * (S.fetchCost input + Schedule.totalDelay input σ) +
        3 / 2 * (S.fetchCost input + Schedule.totalDelay input σ +
          ∑ p ∈ input.initialCache, w p) +
        (L + 4) * (S.fetchCost input + Schedule.totalDelay input σ +
          ∑ p ∈ input.initialCache, w p) := by
  have hL := Instance.one_le_L hv
  -- `lem:timely` and the overdue services
  have hnot := NotOverdueProof.sum_excess_notOverdue_le hv hσ hF
  have hover := ExcessProof.sum_excess_overdue_le hv h2 hσ hSw hF
  have hsplit : ∑ i ∈ range (log input).length, excessAt input S i =
      ∑ i ∈ range (log input).length,
          (if IsOverdue input σ S i then excessAt input S i else 0) +
        ∑ i ∈ range (log input).length,
          (if IsOverdue input σ S i then 0 else excessAt input S i) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by split_ifs <;> ring
  -- `lem:chargeable` for the chargeable round trips
  have htrip : ∑ i ∈ range (log input).length, tripChargeW input σ S i ≤
      ∑ i ∈ range (log input).length, chargeW input σ S i :=
    sum_le_sum fun i _ => tripChargeW_le_chargeW hv i
  have hcharge := TeleProof.sum_chargeW_le hv hσ hSw hF
  have hW0 : 0 ≤ ∑ p ∈ input.initialCache, w p :=
    sum_nonneg fun p _ => (hv.weight_pos p).le
  have hOd := Schedule.totalDelay_nonneg hv hσ
  have hOf : 0 ≤ S.fetchCost input :=
    costFrom_nonneg _ (fun p => (hv.weight_pos p).le) _ _
  nlinarith

/-- **`prop:tele`**: `C_fetch^crit ≤ (3L + 2) OPT + Exc + (4L + 2) ∑ wᵢ`. -/
theorem fetchTotal_le_excess (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    fetchTotal input ≤
      (3 * L + 2) * (S.fetchCost input + Schedule.totalDelay input σ) +
        ∑ i ∈ range (log input).length, excessAt input S i +
        (4 * L + 2) * input.totalWeight := by
  have hL := Instance.one_le_L hv
  have htele := TeleProof.fetchTotal_le hv hσ hSw h2
  have hmiss := sum_missW_le hv hσ hSw hF
  have hW0 : ∑ p ∈ input.initialCache, w p ≤ input.totalWeight :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => (hv.weight_pos p).le
  have hW0' : 0 ≤ ∑ p ∈ input.initialCache, w p :=
    sum_nonneg fun p _ => (hv.weight_pos p).le
  have hOd := Schedule.totalDelay_nonneg hv hσ
  have hOf : 0 ≤ S.fetchCost input :=
    costFrom_nonneg _ (fun p => (hv.weight_pos p).le) _ _
  nlinarith

/-- `prop:tele` + `prop:excess` (first display of the proof of `thm:main`): `C_fetch^crit ≤ (5L + 15/2) OPT + (5L + 15/2) ∑ wᵢ`. -/
theorem fetchTotal_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    {σ : Request Page → ℝ} (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
    (hSw : Schedule.SwapForm input S) (hF : S.FeasibleBy input σ) :
    fetchTotal input ≤
      (5 * L + 15 / 2) * (S.fetchCost input + Schedule.totalDelay input σ) +
        (5 * L + 15 / 2) * input.totalWeight := by
  have hL := Instance.one_le_L hv
  have htele := fetchTotal_le_excess hv h2 hσ hSw hF
  have hexc := excess_le hv h2 hσ hSw hF
  have hW0 : ∑ p ∈ input.initialCache, w p ≤ input.totalWeight :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _ => (hv.weight_pos p).le
  nlinarith

/-- **`prop:cost`**: `C_fetch + C_delay ≤ 23 C_fetch^crit + 21 ∑ wᵢ`, given `prop:algdelay`. -/
theorem cost_le (hv : input.Valid)
    (hdelay : FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) + 5 * lenTotal input) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      23 * fetchTotal input + 21 * input.totalWeight := by
  have hf := CostProof.fetchCost_le_lenTotal hv
  have hlen := CostProof.lenTotal_le_fetchTotal hv
  unfold FracSchedule.cost
  linarith

/-- **The fractional bound.** For power-of-two weights, the cost of `PMD` (fetch cost plus fractional delay cost) is `O(L)` times the cost of any feasible schedule `S` with service times `σ`. -/
theorem cost_le_costWith (input : Instance Page) (h2 : input.PowerOfTwoWeights)
    (S : Schedule Page) (σ : Request Page → ℝ) (hS : S.Feasible input)
    (hστ : S.ServiceTimes input σ) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      (115 * L + 345 / 2) * S.costWith input σ + (115 * L + 387 / 2) * input.totalWeight := by
  have hv := input.valid
  have hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ := fun ρ hρ => (hστ ρ hρ).1
  obtain ⟨S', hF', hSw', hc'⟩ := Schedule.exists_swapForm hv hS hστ
  have hL := Instance.one_le_L hv
  have hT := Instance.totalWeight_nonneg hv
  have hfe := fetchTotal_le hv h2 hσ hSw' hF'
  have hcost : S'.fetchCost input + Schedule.totalDelay input σ ≤ S.costWith input σ := by
    rw [Schedule.costWith_eq]; linarith
  have hfe' : fetchTotal input ≤
      (5 * L + 15 / 2) * S.costWith input σ + (5 * L + 15 / 2) * input.totalWeight := by
    have := mul_le_mul_of_nonneg_left hcost (by linarith : (0 : ℝ) ≤ 5 * L + 15 / 2)
    linarith
  have := cost_le hv (DelayProof.delayCost_le hv)
  nlinarith

/-- **The fractional bound**, against the cost of `S` with its first service times. -/
theorem fracCost_le (input : Instance Page) (h2 : input.PowerOfTwoWeights)
    (S : Schedule Page) (hS : S.Feasible input) :
    FracSchedule.cost input (preemptiveMirrorDescent input) ≤
      (115 * L + 345 / 2) * S.cost input + (115 * L + 387 / 2) * input.totalWeight := by
  rw [Schedule.cost_eq_costWith]
  exact cost_le_costWith input h2 S _ hS (Schedule.serviceTimes_serviceTime hS)

end MainProof

end PMD

end PagingWithDelay
