import PagingWithDelay.Critical.Curve

/-!
# Auxiliary facts for `Divergence.lean`

Right derivatives of the eviction curves and a comparison principle for functions with right derivatives.
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

open Set

set_option linter.unusedSectionVars false

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- Page `i` is not yet evicted at path time `u`. -/
abbrev NotEvicted (input : Instance Page) (x : Page → ℝ) (i : Page) (u : ℝ) : Prop :=
  x i * Real.exp (u / w i) < 1

theorem dvEvictCurve_of_notEvicted {x : Page → ℝ} {i : Page} {u : ℝ}
    (h : NotEvicted input x i u) :
    evictCurve input x i u = x i * Real.exp (u / w i) := min_eq_right h.le

theorem dvEvictCurve_of_evicted {x : Page → ℝ} {i : Page} {u : ℝ}
    (h : ¬ NotEvicted input x i u) : evictCurve input x i u = 1 :=
  min_eq_left (not_lt.mp h)

theorem dvEvictCurve_zero {x : Page → ℝ} {i : Page} (h : x i ≤ 1) :
    evictCurve input x i 0 = x i := by
  simp [evictCurve, h]

theorem dvEvictCurve_pos {x : Page → ℝ} {i : Page} (h : 0 < x i) (s : ℝ) :
    0 < evictCurve input x i s :=
  lt_min one_pos (mul_pos h (Real.exp_pos _))

theorem dvEvictCurve_continuous (x : Page → ℝ) (i : Page) :
    Continuous (evictCurve input x i) := by
  unfold evictCurve
  fun_prop

/-- The right derivative of an eviction curve. -/
theorem dvEvictCurve_hasDerivWithinAt {x : Page → ℝ} {i : Page} (hw : 0 < w i)
    (hx : 0 ≤ x i) (u : ℝ) :
    HasDerivWithinAt (evictCurve input x i)
      (if NotEvicted input x i u then evictCurve input x i u / w i else 0)
      (Ici u) u := by
  split_ifs with h
  · have hd : HasDerivAt (fun s => x i * Real.exp (s / w i))
        (x i * Real.exp (u / w i) / w i) u := by
      have := (((hasDerivAt_id u).div_const (w i)).exp).const_mul (x i)
      convert this using 1
      simp only [id]
      ring
    have hc : Continuous fun s => x i * Real.exp (s / w i) := by fun_prop
    have hev : evictCurve input x i =ᶠ[nhds u] fun s => x i * Real.exp (s / w i) := by
      filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with s hs
      exact min_eq_right hs.le
    rw [dvEvictCurve_of_notEvicted h]
    exact (hd.congr_of_eventuallyEq hev).hasDerivWithinAt
  · have h1 : ∀ s ∈ Ici u, evictCurve input x i s = 1 := by
      intro s hs
      apply min_eq_left
      have h' : 1 ≤ x i * Real.exp (u / w i) := not_lt.mp h
      refine h'.trans (mul_le_mul_of_nonneg_left ?_ hx)
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs hw.le)
    exact (hasDerivWithinAt_const u (Ici u) (1 : ℝ)).congr h1 (h1 u self_mem_Ici)

/-- Comparison principle: if `f' ≤ B'` on `[a, b)` (right derivatives), then `f b - f a ≤ B b - B a`. -/
theorem sub_le_sub_of_deriv_right_le {f f' B B' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hf' : ∀ u, HasDerivWithinAt f (f' u) (Ici u) u)
    (hB : Continuous B) (hB' : ∀ u, HasDerivWithinAt B (B' u) (Ici u) u)
    (bound : ∀ u ∈ Ico a b, f' u ≤ B' u) : f b - f a ≤ B b - B a := by
  have := image_le_of_deriv_right_le_deriv_boundary (f := f) (f' := f') (a := a) (b := b)
    hf.continuousOn (fun u _ => hf' u) (B := fun s => B s - B a + f a) (B' := B')
    (by simp) (by fun_prop) (fun u _ => (hB' u).sub_const _ |>.add_const _) bound
    ⟨hab, le_rfl⟩
  linarith

/-- Comparison with a linear function. -/
theorem sub_le_mul_of_deriv_right_le {f f' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hf' : ∀ u, HasDerivWithinAt f (f' u) (Ici u) u)
    (bound : ∀ u ∈ Ico a b, f' u ≤ c) : f b - f a ≤ c * (b - a) := by
  have := sub_le_sub_of_deriv_right_le (B := fun s => c * s) (B' := fun _ => c) hab hf hf'
    (by fun_prop) (fun u => ((hasDerivAt_id u).const_mul c).hasDerivWithinAt.congr_deriv
      (by simp)) bound
  simp only at this
  linarith

theorem dvMin_sub_min_le {a b S : ℝ} (h : b ≤ a) : min a S - min b S ≤ a - b := by
  simp only [min_def]; split_ifs <;> linarith

end PMD

end PagingWithDelay
