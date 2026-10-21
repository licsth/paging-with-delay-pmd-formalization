import PagingWithDelay.Basic
import PagingWithDelay.Critical.CurveAux

/-!
# The critical service (`sec:alg`)

Properties of the mirror descent path from a rest state `x` on a page `r` with `x r > δ`: it ends in a rest state with `x_r = δ`, the other pages only grow, and its length, fetch cost and interval evictions.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- The fetch `w_r (x_r - δ)` of the critical service on `r` from `x`. -/
noncomputable def criticalFetch (input : Instance Page) (x : Page → ℝ) (r : Page) : ℝ :=
  w r * (x r - δ)

/-- The weighted eviction `EV(φ) = ∑_{i ≠ r} wᵢ (xᵢ(s^end) - xᵢ)` of the critical service. -/
noncomputable def criticalEV (input : Instance Page) (x : Page → ℝ) (r : Page) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i * (criticalState input x r i - x i)

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
  (hr : δ < x r)
include hv hx hr

/-- The set whose infimum is the end of the critical service. -/
theorem serviceEnd_set_aux :
    (0 ≤ L * levelWeight (maxLevel input) ∧
      mdPath input x r (L * levelWeight (maxLevel input)) r ≤ δ) := by
  have hL := L_pos hv
  have hW := levelWeight_pos (maxLevel input)
  refine ⟨by positivity, ?_⟩
  rw [mdPath_self]
  have h1 : ∀ j ∈ Finset.univ.erase r,
      evictCurve input x j (L * levelWeight (maxLevel input)) = 1 := by
    intro j _
    unfold evictCurve
    apply min_eq_left
    have hwj := hv.weight_pos j
    have hle : w j ≤ levelWeight (maxLevel input) :=
      (level_le_iff hv j _).mp (le_maxLevel j)
    have hge : L ≤ L * levelWeight (maxLevel input) / w j := by
      rw [le_div_iff₀ hwj]
      exact mul_le_mul_of_nonneg_left hle hL.le
    calc (1 : ℝ) = δ * Real.exp L := (delta_mul_exp_L hv).symm
      _ ≤ x j * Real.exp (L * levelWeight (maxLevel input) / w j) := by
        apply mul_le_mul (hx.1 j).1 (Real.exp_le_exp.mpr hge) (Real.exp_pos _).le
        linarith [(hx.1 j).1, delta_pos hv]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ, nsmul_eq_mul, mul_one, restMass,
    Nat.cast_sub (card_pos hv)]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  push_cast
  linarith [delta_pos hv]

theorem serviceEnd_set_nonempty :
    {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ}.Nonempty :=
  ⟨_, serviceEnd_set_aux hv hx hr⟩

theorem serviceEnd_set_bdd :
    BddBelow {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ} :=
  ⟨0, fun s hs => hs.1⟩

theorem mdPath_zero : mdPath input x r 0 r = x r := by
  rw [mdPath_self, ← hx.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  rw [Finset.sum_congr rfl fun j _ => evictCurve_zero (input := input) j (hx.1 j).2]
  ring

theorem serviceEnd_nonneg : 0 ≤ serviceEnd input x r :=
  le_csInf (serviceEnd_set_nonempty hv hx hr) fun s hs => hs.1

/-- The critical service ends by path time `L · 2^{maxLevel}`, when all other pages are evicted. -/
theorem serviceEnd_le : serviceEnd input x r ≤ L * levelWeight (maxLevel input) :=
  csInf_le (serviceEnd_set_bdd hv hx hr) (serviceEnd_set_aux hv hx hr)

/-- Before its end, the critical service has `x_r(s) > δ`. -/
theorem delta_lt_mdPath {s : ℝ} (hs0 : 0 ≤ s) (hs : s < serviceEnd input x r) :
    δ < mdPath input x r s r := by
  by_contra h
  push_neg at h
  have := csInf_le (serviceEnd_set_bdd hv hx hr) (show s ∈ {s : ℝ | 0 ≤ s ∧
    mdPath input x r s r ≤ δ} from ⟨hs0, h⟩)
  exact absurd hs (not_lt.mpr this)

theorem mdPath_serviceEnd : mdPath input x r (serviceEnd input x r) r = δ := by
  have hcont := mdPath_self_continuous (input := input) x r
  have hmem : serviceEnd input x r ∈ {s : ℝ | 0 ≤ s ∧ mdPath input x r s r ≤ δ} := by
    apply IsClosed.csInf_mem _ (serviceEnd_set_nonempty hv hx hr) (serviceEnd_set_bdd hv hx hr)
    exact isClosed_Ici.inter (isClosed_Iic.preimage hcont)
  apply le_antisymm hmem.2
  by_contra hlt
  push_neg at hlt
  have h0 := mdPath_zero hv hx hr
  have hpos : 0 < serviceEnd input x r := by
    rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h, h0] at hlt; linarith
    · exact h
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hpos.le hcont.continuousOn
    (show δ ∈ Set.Icc _ _ from ⟨hlt.le, by rw [h0]; exact hr.le⟩)
  rcases eq_or_lt_of_le hc.2 with h | h
  · rw [h] at hfc; linarith
  · have := delta_lt_mdPath hv hx hr hc.1 h
    simp only at hfc
    linarith

theorem criticalState_self : criticalState input x r r = δ :=
  mdPath_serviceEnd hv hx hr

theorem criticalState_of_ne {i : Page} (hi : i ≠ r) :
    criticalState input x r i = evictCurve input x i (serviceEnd input x r) :=
  mdPath_of_ne x r _ hi

theorem le_criticalState {i : Page} (hi : i ≠ r) : x i ≤ criticalState input x r i := by
  rw [criticalState_of_ne hv hx hr hi]
  calc x i = evictCurve input x i 0 := (evictCurve_zero i (hx.1 i).2).symm
    _ ≤ _ := evictCurve_mono hv i (by linarith [(hx.1 i).1, delta_pos hv])
        (serviceEnd_nonneg hv hx hr)

theorem criticalState_isRest : IsRest input (criticalState input x r) := by
  refine ⟨fun i => ?_, ?_⟩
  · rcases eq_or_ne i r with rfl | hi
    · rw [criticalState_self hv hx hr]; exact ⟨le_rfl, (delta_lt_one hv).le⟩
    · refine ⟨(hx.1 i).1.trans (le_criticalState hv hx hr hi), ?_⟩
      rw [criticalState_of_ne hv hx hr hi]; exact evictCurve_le_one _ _ _
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
    have : ∀ j ∈ Finset.univ.erase r, criticalState input x r j =
        evictCurve input x j (serviceEnd input x r) := fun j hj =>
      criticalState_of_ne hv hx hr (Finset.ne_of_mem_erase hj)
    rw [Finset.sum_congr rfl this]
    unfold criticalState
    rw [mdPath_self]
    ring

theorem criticalFetch_lt_weight : criticalFetch input x r < w r := by
  unfold criticalFetch
  have := hv.weight_pos r
  have := (hx.1 r).2
  have := delta_pos hv
  nlinarith

/-- The fetch cost of the critical service is its fetch. -/
theorem critical_fetchCost :
    ∑ i, w i * max 0 (x i - criticalState input x r i) = criticalFetch input x r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), criticalState_self hv hx hr]
  unfold criticalFetch
  rw [max_eq_right (by linarith)]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [max_eq_left (by linarith [le_criticalState hv hx hr (Finset.ne_of_mem_erase hi)]), mul_zero]

/-- `∑ wᵢ xᵢ` changes by `EV - fetch` in a critical service. -/
theorem critical_weightedMass :
    ∑ i, w i * criticalState input x r i =
      ∑ i, w i * x i + criticalEV input x r - criticalFetch input x r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), ← Finset.add_sum_erase _ _ (Finset.mem_univ r),
    criticalState_self hv hx hr]
  unfold criticalFetch criticalEV
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end

end PMD

end PagingWithDelay
