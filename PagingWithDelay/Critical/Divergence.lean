import PagingWithDelay.Critical.DivergenceAux

/-!
# The Bregman potential (`sec:bregman`)

`D(O ‖ x) = ∑_{i ∉ O} wᵢ g(xᵢ) + ∑_{i ∈ O} wᵢ xᵢ` with `g(u) = u - 1 - ln u`, its behaviour under moves of the comparator (`lem:optmoves`) and in one critical service (`prop:phaseD`).
-/

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

/-- `g(u) = u - 1 - ln u`. -/
noncomputable def bregG (u : ℝ) : ℝ := u - 1 - Real.log u

/-- The Bregman divergence `D(O ‖ x)`. -/
noncomputable def divergence (input : Instance Page) (O : Finset Page) (x : Page → ℝ) : ℝ :=
  ∑ i, w i * (if i ∈ O then x i else bregG (x i))

theorem bregG_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ bregG u := by
  have := Real.log_le_sub_one_of_pos hu
  unfold bregG; linarith

theorem bregG_le_of_frac (hv : input.Valid) {u : ℝ} (h1 : δ ≤ u) :
    bregG u ≤ L - 1 + u := by
  have hd := delta_pos hv
  have : Real.log δ ≤ Real.log u := Real.log_le_log hd h1
  rw [log_delta hv] at this
  unfold bregG; linarith

theorem divergence_nonneg (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O : Finset Page) : 0 ≤ divergence input O x := by
  unfold divergence
  refine Finset.sum_nonneg fun i _ => mul_nonneg (hv.weight_pos i).le ?_
  have hxi : 0 < x i := lt_of_lt_of_le (delta_pos hv) (hx i).1
  split_ifs
  · exact hxi.le
  · exact bregG_nonneg hxi

theorem divergence_le (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O : Finset Page) : divergence input O x ≤ (L + 1) * input.totalWeight := by
  unfold divergence Instance.totalWeight
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (L + 1)]
  refine mul_le_mul_of_nonneg_left ?_ (hv.weight_pos i).le
  have hL := L_pos hv
  have h1 := (hx i).2
  split_ifs
  · linarith
  · have := bregG_le_of_frac hv (hx i).1
    linarith

/-- `lem:optmoves`, one comparator move: replacing `O` by `O'` changes `D` by at most `L` times the evicted weight plus the fetched weight. -/
theorem divergence_change_cache (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x)
    (O O' : Finset Page) :
    divergence input O' x - divergence input O x ≤
      L * ∑ i ∈ O \ O', w i + ∑ i ∈ O' \ O, w i := by
  unfold divergence
  have e1 : ∀ T : Finset Page, ∑ i ∈ T, w i =
      ∑ i, if i ∈ T then w i else 0 := fun T => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [e1, e1, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw := (hv.weight_pos i).le
  have hL := L_pos hv
  have hxi : 0 < x i := lt_of_lt_of_le (delta_pos hv) (hx i).1
  have hlog : Real.log δ ≤ Real.log (x i) := Real.log_le_log (delta_pos hv) (hx i).1
  have hlog1 : Real.log (x i) ≤ 0 := Real.log_nonpos hxi.le (hx i).2
  rw [log_delta hv] at hlog
  by_cases h : i ∈ O <;> by_cases h' : i ∈ O' <;> simp [h, h', bregG] <;> nlinarith

/-! ### Auxiliary: the critical service part of `D` from the pages `i ≠ r` -/

section CriticalAux

open Set

/-- The contribution of the pages `i ≠ r` to `D(O ‖ x(s))` along the critical service. -/
noncomputable def restPart (input : Instance Page) (O : Finset Page) (x : Page → ℝ) (r : Page)
    (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i *
    (if i ∈ O then evictCurve input x i s else bregG (evictCurve input x i s))

/-- Its right derivative. -/
noncomputable def restDeriv (input : Instance Page) (O : Finset Page) (x : Page → ℝ) (r : Page)
    (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r,
    (if NotEvicted input x i u then evictCurve input x i u - (if i ∈ O then 0 else 1) else 0)

/-- The weighted missing mass of the pages `i ≠ r` along the critical service. -/
noncomputable def evMass (input : Instance Page) (x : Page → ℝ) (r : Page) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, w i * evictCurve input x i s

/-- Its right derivative. -/
noncomputable def evDeriv (input : Instance Page) (x : Page → ℝ) (r : Page) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, (if NotEvicted input x i u then evictCurve input x i u else 0)

theorem continuous_restPart {x : Page → ℝ} (hx0 : ∀ i, 0 < x i) (O : Finset Page) (r : Page) :
    Continuous (restPart input O x r) := by
  unfold restPart
  refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
  have hc := dvEvictCurve_continuous (input := input) x i
  by_cases hi : i ∈ O
  · simp only [hi, ↓reduceIte]; exact hc
  · simp only [hi, ↓reduceIte]
    unfold bregG
    exact (hc.sub continuous_const).sub (hc.log fun s => (dvEvictCurve_pos (hx0 i) s).ne')

theorem continuous_evMass (x : Page → ℝ) (r : Page) : Continuous (evMass input x r) := by
  unfold evMass
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (dvEvictCurve_continuous x i)

theorem hasDerivWithinAt_restPart (hv : input.Valid) {x : Page → ℝ} (hx0 : ∀ i, 0 < x i)
    (O : Finset Page) (r : Page) (u : ℝ) :
    HasDerivWithinAt (restPart input O x r) (restDeriv input O x r u) (Ici u) u := by
  unfold restPart restDeriv
  refine HasDerivWithinAt.fun_sum fun i _ => ?_
  have hw := hv.weight_pos i
  have hd := dvEvictCurve_hasDerivWithinAt (input := input) (x := x) hw (hx0 i).le u
  have hpos := dvEvictCurve_pos (input := input) (hx0 i) u
  by_cases hi : i ∈ O
  · simp only [hi, ↓reduceIte]
    refine (hd.const_mul _).congr_deriv ?_
    split_ifs <;> field_simp <;> simp
  · simp only [hi, ↓reduceIte]
    have h2 : HasDerivWithinAt (fun s => w i * bregG (evictCurve input x i s))
        (w i * ((if NotEvicted input x i u then evictCurve input x i u / w i
          else 0) - (if NotEvicted input x i u then evictCurve input x i u / w i
          else 0) / evictCurve input x i u)) (Ici u) u := by
      unfold bregG
      exact ((hd.sub_const 1).sub (hd.log hpos.ne')).const_mul _
    refine h2.congr_deriv ?_
    split_ifs
    · field_simp
    · simp

theorem hasDerivWithinAt_evMass (hv : input.Valid) {x : Page → ℝ} (hx0 : ∀ i, 0 < x i)
    (r : Page) (u : ℝ) :
    HasDerivWithinAt (evMass input x r) (evDeriv input x r u) (Ici u) u := by
  unfold evMass evDeriv
  refine HasDerivWithinAt.fun_sum fun i _ => ?_
  have hw := hv.weight_pos i
  have hd := dvEvictCurve_hasDerivWithinAt (input := input) (x := x) hw (hx0 i).le u
  refine (hd.const_mul _).congr_deriv ?_
  split_ifs
  · field_simp
  · simp

theorem dvMdPath_self_eq (x : Page → ℝ) (r : Page) (u : ℝ) :
    mdPath input x r u r = restMass input - ∑ j ∈ Finset.univ.erase r, evictCurve input x j u := by
  simp [mdPath]

/-- The key identity `h(u) = [r ∉ O] - x_r(u) - |E(u) ∩ O|`. -/
theorem restDeriv_eq {O : Finset Page} (hO : O.card = k) (x : Page → ℝ) (r : Page)
    (u : ℝ) :
    restDeriv input O x r u = (if r ∈ O then 0 else 1) - mdPath input x r u r -
      ∑ i ∈ Finset.univ.erase r, (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
  have ht : ∀ i, (if NotEvicted input x i u then
      evictCurve input x i u - (if i ∈ O then 0 else 1) else 0) =
      (evictCurve input x i u - (if i ∈ O then 0 else 1)) -
        (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
    intro i
    by_cases h : NotEvicted input x i u
    · simp [h]
    · rw [dvEvictCurve_of_evicted h]
      by_cases hi : i ∈ O <;> simp [h, hi]
  unfold restDeriv
  rw [Finset.sum_congr rfl fun i _ => ht i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    dvMdPath_self_eq]
  have h2 : ∑ i, (if i ∈ O then (0 : ℝ) else 1) = restMass input := by
    have : ∀ i, (if i ∈ O then (0 : ℝ) else 1) = 1 - (if i ∈ O then 1 else 0) := by
      intro i; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
    simp [restMass, hO]
  have h1 := Finset.add_sum_erase Finset.univ (fun i => if i ∈ O then (0 : ℝ) else 1)
    (Finset.mem_univ r)
  simp only at h1
  linarith

theorem divergence_eq_split (O : Finset Page) (y : Page → ℝ) (r : Page) :
    divergence input O y = w r * (if r ∈ O then y r else bregG (y r)) +
      ∑ i ∈ Finset.univ.erase r, w i * (if i ∈ O then y i else bregG (y i)) :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm

theorem divergence_start {x : Page → ℝ} (hx : IsRest input x) (O : Finset Page) (r : Page) :
    divergence input O x = w r * (if r ∈ O then x r else bregG (x r)) +
      restPart input O x r 0 := by
  rw [divergence_eq_split O x r]
  congr 1
  unfold restPart
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dvEvictCurve_zero (hx.1 i).2]

theorem divergence_end (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
    (hr : δ < x r) (O : Finset Page) :
    divergence input O (criticalState input x r) =
      w r * (if r ∈ O then δ else bregG δ) +
      restPart input O x r (serviceEnd input x r) := by
  rw [divergence_eq_split O _ r, criticalState_self hv hx hr]
  congr 1
  unfold restPart
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [criticalState_of_ne hv hx hr (Finset.ne_of_mem_erase hi)]

end CriticalAux

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {r : Page}
  (hr : δ < x r) {O : Finset Page} (hO : O.card = k)
include hv hx hr hO

/-- `prop:phaseD`, hit service. -/
theorem critical_hit (hrO : r ∈ O) :
    divergence input O (criticalState input x r) - divergence input O x ≤ -criticalFetch input x r := by
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_lt_of_le (delta_pos hv) (hx.1 i).1
  have hS0 := serviceEnd_nonneg hv hx hr
  have hD0 := divergence_start hx O r
  have hD1 := divergence_end hv hx hr O
  have hA := sub_le_mul_of_deriv_right_le (c := 0) hS0 (continuous_restPart hx0 O r)
    (hasDerivWithinAt_restPart hv hx0 O r) fun u hu => by
      have hxr := delta_lt_mdPath hv hx hr hu.1 hu.2
      have hd := delta_pos hv
      rw [restDeriv_eq hO, if_pos hrO]
      have : 0 ≤ ∑ i ∈ Finset.univ.erase r,
          (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
      linarith
  rw [hD0, hD1]
  simp only [hrO, ↓reduceIte]
  unfold criticalFetch
  linarith

end

end PMD

end PagingWithDelay
