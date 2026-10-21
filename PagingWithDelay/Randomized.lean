import PagingWithDelay.Rounded
import PagingWithDelay.Rounding.Schedule

/-!
# The randomized algorithm (`thm:main`)

The algorithm of `thm:main`: round the weights up to powers of two, run `PMD`, and round its fractional schedule online (`prop:rounding`, `Rounding.randomSchedule`). It is online and feasible with probability `1`; its expected cost is at most `30` times the fractional bound of `PMD` on the rounded weights plus `5 ∑ w̃ᵢ`, giving `E[cost] ≤ (6900 L + 10350) cost(S) + (6900 L + 11620) ∑ wᵢ` for every feasible schedule `S`.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

namespace PMD

namespace RandomizedProof

open Rounding RoundedProof

variable {input : Instance Page}

open scoped InstanceNotation in
/-- The initial state is mapped to the indicator vector of the initial cache. -/
theorem zmap_initialState :
    zmap δ (initialState input) = indicator input.initialCache := by
  have hv := input.valid
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast input.cacheSize_pos
  have hd1 : δ * (2 * k + 1) = 1 := by
    unfold Instance.delta; field_simp
  have hδ1 := Instance.delta_lt_one hv
  funext i
  unfold zmap initialState indicator
  split_ifs with h1 h2
  · -- `x_i = δ`
    rw [div_self (by linarith)]; norm_num
  · -- `x_i = 1 - kδ`: `u_i = kδ / (1 - δ) = 1/2`
    have : (1 - (1 - k * δ)) / (1 - δ) = 1 / 2 := by
      rw [div_eq_iff (by linarith)]; nlinarith
    rw [this]; norm_num
  · simp

/-- The first waypoint of `PMD` maps to the indicator vector of the initial cache. -/
theorem head_zmap (input : Instance Page) :
    ∀ w ∈ (preemptiveMirrorDescent input).head?,
      zmap input.delta w.state = indicator input.initialCache := by
  intro w hw
  rw [output_head input.valid w hw, snapAt_zero input.valid]
  exact zmap_initialState

end RandomizedProof

end PMD

open PMD.RandomizedProof PMD.RoundedProof Rounding in
/-- The randomized algorithm of `thm:main`: `PMD` on the weights rounded up to powers of two, rounded online to integral caches (`prop:rounding`). -/
noncomputable def randomizedPMD : RandAlgorithm Page := fun input =>
  randomSchedule input.roundWeights (preemptiveMirrorDescent input.roundWeights)

namespace PMD

namespace RandomizedProof

open Rounding RoundedProof

theorem randomizedPMD_online : (randomizedPMD : RandAlgorithm Page).Online := by
  intro I1 I2 t h
  have hX := preemptiveMirrorDescent_online _ _ t
    (show I1.roundWeights.upTo t = I2.roundWeights.upTo t by
      rw [← roundWeights_upTo, ← roundWeights_upTo, h])
  have hw : I1.roundWeights = { I2.roundWeights with requests := I1.roundWeights.requests } := by
    have hw : (I1.upTo t).weight = (I2.upTo t).weight := congrArg _ h
    have hk : (I1.upTo t).cacheSize = (I2.upTo t).cacheSize := congrArg _ h
    have hC : (I1.upTo t).initialCache = (I2.upTo t).initialCache := congrArg _ h
    obtain ⟨w, hw', k, hk', hkn, C, hC', r⟩ := I1
    obtain ⟨w', hw'', k', hk'', hkn', C', hC'', r'⟩ := I2
    simp only [Instance.upTo] at hw hk hC
    subst hw hk hC
    rfl
  simp only [randomizedPMD]
  rw [randomSchedule_upTo _ (preemptiveMirrorDescent_feasible _).chronological,
    randomSchedule_upTo _ (preemptiveMirrorDescent_feasible _).chronological, hX]
  -- `randomSchedule` depends on the instance only through its weights, cache size, initial cache and `δ`
  rw [hw]
  rfl

theorem randomizedPMD_feasible : (randomizedPMD : RandAlgorithm Page).Feasible := by
  intro input S hS
  exact feasible_roundWeights_iff.mp
    (feasible_of_mem_support roundWeights_powerOfTwo (preemptiveMirrorDescent_feasible _)
      (head_zmap _) S hS)

/-- The fractional delay cost is nonnegative. -/
theorem delayCost_nonneg {X : FracSchedule Page} (hX : X.Feasible input) :
    0 ≤ X.delayCost input := by
  unfold FracSchedule.delayCost
  apply List.sum_nonneg
  intro c hc
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hc
  apply mul_nonneg
  · have hδ1 := Instance.delta_lt_one input.valid
    unfold FracSchedule.stateBefore
    cases hl : (X.filter fun w => decide (w.time < ρ.arrival)).getLast? with
    | some w =>
      have hmem : w ∈ X := List.mem_of_mem_filter (List.mem_of_getLast? hl)
      simp only
      linarith [(hX.bounds w hmem ρ.page).1]
    | none =>
      cases hX0 : X.head? with
      | none => simp only [Option.map_none, Option.getD_none]; linarith
      | some w =>
        simp only [Option.map_some, Option.getD_some]
        linarith [(hX.bounds w (List.mem_of_mem_head? hX0) ρ.page).1]
  · rw [← ρ.delay_zero]
    apply ρ.delay_mono
    obtain ⟨w, hw, h1, h2⟩ := hX.serves ρ hρ
    have : ρ.arrival ≤ X.serviceTime input ρ := by
      unfold FracSchedule.serviceTime
      apply le_csInf (⟨w.time, w, hw, h1, h2, rfl⟩ :
        {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧ w.time = s}.Nonempty)
      rintro s ⟨w', -, h1', -, rfl⟩
      exact h1'
    linarith

/-- The cost of a feasible schedule is nonnegative. -/
theorem cost_nonneg {S : Schedule Page} (hS : S.Feasible input) : 0 ≤ S.cost input := by
  have := Schedule.serviceTimes_serviceTime hS
  rw [Schedule.cost_eq_costWith, Schedule.costWith_eq]
  have h1 := Schedule.totalDelay_nonneg input.valid fun ρ hρ => (this ρ hρ).1
  have h2 : 0 ≤ S.fetchCost input :=
    MainProof.costFrom_nonneg _ (fun p => (input.weight_pos p).le) _ _
  linarith

open scoped InstanceNotation in
/-- **`thm:main`**, the bound. -/
theorem expectedCost_le (input : Instance Page) (S : Schedule Page) (hS : S.Feasible input) :
    randomizedPMD.expectedCost input ≤
      ENNReal.ofReal ((6900 * L + 10350) * S.cost input +
        (6900 * L + 11620) * input.totalWeight) := by
  set I := input.roundWeights
  set X := preemptiveMirrorDescent I
  have hXf : X.Feasible I := preemptiveMirrorDescent_feasible I
  have hround := Rounding.expectedCost_le (roundWeights_powerOfTwo (input := input)) hXf
    (head_zmap I)
  have hfrac := MainProof.fracCost_le I roundWeights_powerOfTwo S
    (feasible_roundWeights_iff.mpr hS)
  rw [roundWeights_L] at hfrac
  have hc := cost_roundWeights_le S hS
  have hT := totalWeight_roundWeights_le (input := input)
  have hL := Instance.one_le_L input.valid
  have hD := delayCost_nonneg hXf
  have hcost0 := cost_nonneg hS
  calc randomizedPMD.expectedCost input
      = ∑' S', randomSchedule I X S' * ENNReal.ofReal (S'.cost input) := rfl
    _ ≤ ∑' S', randomSchedule I X S' * ENNReal.ofReal (S'.cost I) := by
        gcongr with S'
        exact cost_le_cost_roundWeights S'
    _ ≤ ENNReal.ofReal (30 * X.fetchCost I + 3 * X.delayCost I + 5 * I.totalWeight) := hround
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        unfold FracSchedule.cost at hfrac
        have h1 := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 115 * L + 345 / 2)
        have h2 := mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℝ) ≤ 115 * L + 387 / 2)
        nlinarith

open scoped InstanceNotation in
/-- **`thm:main`** with `ln k` in place of `L = ln (2k+1) ≤ ln k + 1.1` (`Instance.L_le_log_add`): `6900 · 1.1 = 7590`. -/
theorem expectedCost_le_log (input : Instance Page) (S : Schedule Page)
    (hS : S.Feasible input) :
    randomizedPMD.expectedCost input ≤
      ENNReal.ofReal ((6900 * Real.log k + 17940) * S.cost input +
        (6900 * Real.log k + 19210) * input.totalWeight) := by
  refine (expectedCost_le input S hS).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL := Instance.L_le_log_add input.valid
  have hc := cost_nonneg hS
  have hT := Instance.totalWeight_nonneg input.valid
  nlinarith [mul_nonneg (sub_nonneg.2 hL) hc, mul_nonneg (sub_nonneg.2 hL) hT]

end RandomizedProof

end PMD

end PagingWithDelay
