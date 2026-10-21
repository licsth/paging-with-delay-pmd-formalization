import PagingWithDelay.Basic

/-!
# Helpers for the critical service curve
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- Telescoping over an integer interval. -/
theorem sum_Icc_telescope (g : ℤ → ℝ) (l : ℤ) :
    ∀ n : ℕ, ∑ e ∈ Finset.Icc l (l + n), (g (e + 1) - g e) = g (l + n + 1) - g l
  | 0 => by simp
  | n + 1 => by
    have hI : Finset.Icc l (l + ((n + 1 : ℕ) : ℤ)) = insert (l + n + 1) (Finset.Icc l (l + n)) := by
      ext e; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hn : (l + n + 1) ∉ Finset.Icc l (l + n) := by simp
    rw [hI, Finset.sum_insert hn, sum_Icc_telescope g l n]
    push_cast; ring_nf

theorem sum_Icc_telescope' (g : ℤ → ℝ) (l M : ℤ) (h : l ≤ M) :
    ∑ e ∈ Finset.Icc l M, (g (e + 1) - g e) = g (M + 1) - g l := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M = l + n := ⟨(M - l).toNat, by omega⟩
  subst hn
  exact sum_Icc_telescope g l n

theorem evictCurve_continuous (x : Page → ℝ) (i : Page) :
    Continuous (evictCurve input x i) :=
  continuous_const.min (continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const _)))

theorem evictCurve_mono (hv : input.Valid) {x : Page → ℝ} (i : Page) (hxi : 0 ≤ x i) :
    Monotone (evictCurve input x i) := by
  intro a b hab
  unfold evictCurve
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ hxi
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right hab (hv.weight_pos i).le

theorem evictCurve_zero {x : Page → ℝ} (i : Page) (hxi : x i ≤ 1) :
    evictCurve input x i 0 = x i := by
  unfold evictCurve
  simp [hxi]

theorem evictCurve_le_one (x : Page → ℝ) (i : Page) (s : ℝ) : evictCurve input x i s ≤ 1 :=
  min_le_left _ _

theorem mdPath_self (x : Page → ℝ) (r : Page) (s : ℝ) :
    mdPath input x r s r = restMass input - ∑ j ∈ Finset.univ.erase r, evictCurve input x j s := by
  simp [mdPath]

theorem mdPath_of_ne (x : Page → ℝ) (r : Page) (s : ℝ) {i : Page} (hi : i ≠ r) :
    mdPath input x r s i = evictCurve input x i s := by
  simp [mdPath, hi]

theorem mdPath_self_continuous (x : Page → ℝ) (r : Page) :
    Continuous fun s => mdPath input x r s r := by
  simp only [mdPath_self]
  exact continuous_const.sub (continuous_finset_sum _ fun j _ => evictCurve_continuous x j)

end PMD

end PagingWithDelay
