import PagingWithDelay.Main

/-!
# Arbitrary weights: rounding up to powers of two

The first step of the proof of `thm:main`: rounding every weight up to a power of two (`w ↦ 2^⌈log₂ w⌉ ∈ [w, 2w)`) at most doubles the cost of every schedule and does not decrease it.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open scoped InstanceNotation in
/-- The instance with every weight rounded up to a power of two, `w ↦ 2^⌈log₂ w⌉`. -/
noncomputable def Instance.roundWeights (input : Instance Page) : Instance Page :=
  { input with
    weight := fun p => (2 : ℝ) ^ Int.clog 2 (w p)
    weight_pos := fun p => by positivity }

namespace Schedule

theorem costFrom_mono {w w' : Page → ℝ} (hw : ∀ p, w p ≤ w' p) :
    ∀ (C : Finset Page) (S : Schedule Page), costFrom w C S ≤ costFrom w' C S
  | _, [] => le_rfl
  | C, step :: rest => by
      simp only [costFrom]
      exact add_le_add (Finset.sum_le_sum fun p _ => hw p) (costFrom_mono hw step.cache rest)

theorem costFrom_smul (w : Page → ℝ) (a : ℝ) :
    ∀ (C : Finset Page) (S : Schedule Page),
      costFrom (fun p => a * w p) C S = a * costFrom w C S
  | _, [] => by simp [costFrom]
  | C, step :: rest => by
      simp only [costFrom, costFrom_smul w a step.cache rest, mul_add, Finset.mul_sum]

end Schedule

open scoped InstanceNotation

namespace PMD

namespace RoundedProof

variable {input : Instance Page}

open Finset

theorem roundWeights_powerOfTwo : input.roundWeights.PowerOfTwoWeights :=
  fun p => ⟨Int.clog 2 (w p), rfl⟩

theorem le_roundWeights (p : Page) : w p ≤ input.roundWeights.weight p := by
  have := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) (w p)
  simpa [Instance.roundWeights] using this

theorem roundWeights_le (p : Page) : input.roundWeights.weight p ≤ 2 * w p := by
  have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) (input.weight_pos p)
  simp only [Instance.roundWeights]
  have : (2 : ℝ) ^ Int.clog 2 (w p) =
      2 * (2 : ℝ) ^ (Int.clog 2 (w p) - 1) := by
    rw [← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring_nf
  push_cast at h
  rw [this]; linarith

theorem roundWeights_L : input.roundWeights.L = L := rfl

theorem roundWeights_upTo (t : ℝ) : (input.upTo t).roundWeights = input.roundWeights.upTo t :=
  rfl

theorem totalWeight_roundWeights_le :
    input.roundWeights.totalWeight ≤ 2 * input.totalWeight := by
  unfold Instance.totalWeight
  rw [mul_sum]
  exact sum_le_sum fun p _ => roundWeights_le p

theorem feasible_roundWeights_iff {S : Schedule Page} :
    S.Feasible input.roundWeights ↔ S.Feasible input :=
  ⟨fun h => ⟨h.chronological, h.capacity, h.serves⟩,
    fun h => ⟨h.chronological, h.capacity, h.serves⟩⟩

/-- The cost of a schedule with the original weights is at most its cost with the rounded weights (the delay costs agree). -/
theorem cost_le_cost_roundWeights (S : Schedule Page) :
    S.cost input ≤ S.cost input.roundWeights := by
  unfold Schedule.cost Schedule.fetchCost
  have := Schedule.costFrom_mono (fun p => le_roundWeights (input := input) p)
    input.initialCache S
  exact add_le_add this le_rfl

/-- Rounding the weights at most doubles the cost of a schedule. -/
theorem cost_roundWeights_le (S : Schedule Page) (hS : S.Feasible input) :
    S.cost input.roundWeights ≤ 2 * S.cost input := by
  have hv := input.valid
  have hf : S.fetchCost input.roundWeights ≤ 2 * S.fetchCost input := by
    unfold Schedule.fetchCost
    rw [← Schedule.costFrom_smul]
    exact Schedule.costFrom_mono (fun p => roundWeights_le p) _ _
  have hσ := Schedule.serviceTimes_serviceTime hS
  have hd := Schedule.totalDelay_nonneg hv (fun ρ hρ => (hσ ρ hρ).1)
  have he : S.cost input.roundWeights = S.fetchCost input.roundWeights +
      Schedule.totalDelay input (S.serviceTime input) := rfl
  rw [he, Schedule.cost_eq_costWith, Schedule.costWith_eq]
  linarith

end RoundedProof

end PMD

end PagingWithDelay
