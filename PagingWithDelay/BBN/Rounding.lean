import PagingWithDelay.BBN.Profile
import PagingWithDelay.BBN.AddRemove
import PagingWithDelay.BBN.Transfer

/-!
# The online rounding theorem (BBN, Theorem 4.1, fetch-cost version)

Assembly: one step of the rounding draws the target profile `m` from the coupling `rhoLaw`
conditioned on the current profile, fixes the marginals page by page (`add_remove`), and then
moves pages within classes until the cache has profile `m` (`transfer`).
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace PagingWithDelay.BBN

namespace Assembly

/-! ### Conditional distributions of a coupling -/

section Cond

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
theorem map_fst_apply (π : PMF (α × β)) (a : α) : π.map Prod.fst a = ∑ b, π (a, b) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The conditional distribution of the second coordinate of `π` given the first is `a`. -/
def condSnd (π : PMF (α × β)) (a : α) : PMF β :=
  if h : π.map Prod.fst a = 0 then π.map Prod.snd else
    PMF.ofFintype (fun b => π (a, b) / π.map Prod.fst a) (by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← map_fst_apply]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _))

theorem bind_condSnd (π : PMF (α × β)) :
    (π.map Prod.fst).bind (fun a => (condSnd π a).map (Prod.mk a)) = π := by
  ext ⟨a, b⟩
  have hrow : ∀ a' b', π (a', b') ≤ π.map Prod.fst a' := fun a' b' => by
    rw [map_fst_apply]
    exact Finset.single_le_sum (f := fun b => π (a', b)) (fun _ _ => zero_le _)
      (Finset.mem_univ b')
  have hmk : ∀ a' (p : PMF β), p.map (Prod.mk a') (a, b) = if a = a' then p b else 0 := by
    intro a' p
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · simp
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [hmk, if_pos rfl]
    unfold condSnd
    split_ifs with h
    · simpa [h] using (le_antisymm (h ▸ hrow a b) (zero_le _)).symm
    · rw [PMF.ofFintype_apply]
      exact ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)
  · intro a' _ ha'
    rw [hmk, if_neg (Ne.symm ha'), mul_zero]
  · simp

end Cond

/-! ### Expectations over finite types -/

section Ex

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The expectation of `f` under `p`. -/
def ex (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

theorem ex_bind (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    ex (p.bind K) f = ex p (fun a => ex (K a) f) := by
  unfold ex
  have h : ∀ b, ((p.bind K) b).toReal = ∑ a, (p a).toReal * (K a b).toReal := by
    intro b
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  simp_rw [h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

theorem ex_pure (a : α) (f : α → ℝ) : ex (PMF.pure a) f = f a := by
  classical
  unfold ex
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [PMF.pure_apply, hb]
  · simp

theorem ex_map (p : PMF α) (g : α → β) (f : β → ℝ) : ex (p.map g) f = ex p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]

theorem ex_congr (p : PMF α) {f g : α → ℝ} (h : ∀ a ∈ p.support, f a = g a) :
    ex p f = ex p g := by
  unfold ex
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).2 ha)]

theorem ex_mono (p : PMF α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : ex p f ≤ ex p g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

theorem ex_add (p : PMF α) (f g : α → ℝ) : ex p (fun a => f a + g a) = ex p f + ex p g := by
  unfold ex
  simp_rw [mul_add, Finset.sum_add_distrib]

theorem ex_mul_left (p : PMF α) (c : ℝ) (f : α → ℝ) : ex p (fun a => c * f a) = c * ex p f := by
  unfold ex
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

theorem ex_sum {ι : Type*} [Fintype ι] (p : PMF α) (f : ι → α → ℝ) :
    ex p (fun a => ∑ v, f v a) = ∑ v, ex p (f v) := by
  unfold ex
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_toReal (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a), h]
  simp

theorem ex_const (p : PMF α) (c : ℝ) : ex p (fun _ => c) = c := by
  unfold ex
  rw [← Finset.sum_mul, sum_toReal, one_mul]

theorem sum_sum_eq (p : PMF α) (K : α → PMF β) (f : α → β → ℝ) :
    ∑ a, ∑ b, (p a).toReal * (K a b).toReal * f a b = ex p (fun a => ex (K a) (f a)) := by
  unfold ex
  simp_rw [Finset.mul_sum, mul_assoc]

theorem ext_of_ex [DecidableEq α] {p q : PMF α}
    (h : ∀ a, ex p (fun z => if z = a then 1 else 0) = ex q (fun z => if z = a then 1 else 0)) :
    p = q := by
  have key : ∀ (r : PMF α) a, ex r (fun z => if z = a then 1 else 0) = (r a).toReal := by
    intro r a
    unfold ex
    simp
  ext a
  have := h a
  rw [key, key] at this
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 this

end Ex

/-! ### One step of the rounding -/

section Step

variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- The weight of the pages of `C'` missing from `C`. -/
def cost (C C' : Finset Page) : ℝ := ∑ i ∈ C' \ C, w i

/-- Draw the cache from `D` and the target profile from `ρ` conditioned on its profile. -/
def mu (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w)) : PMF (Finset Page × Prof w) :=
  D.bind fun C => (condSnd ρ (profile w C)).map (Prod.mk C)

/-- Apply `κ` to the cache, keeping the target profile. -/
def mu2 (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page)) :
    PMF (Finset Page × Prof w) :=
  μ.bind fun x => (κ x).map fun C'' => (C'', x.2)

/-- The step kernel. -/
def kern (ρ : PMF (Prof w × Prof w)) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (C : Finset Page) : PMF (Finset Page) :=
  (condSnd ρ (profile w C)).bind fun m => (κ₁ (C, m)).bind fun C'' => κ₂ (C'', m)

theorem ex_mu (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w))
    (h : Finset Page × Prof w → ℝ) :
    ex (mu w D ρ) h = ex D (fun C => ex (condSnd ρ (profile w C)) (fun m => h (C, m))) := by
  unfold mu
  rw [ex_bind]
  simp_rw [ex_map]

theorem ex_mu2 (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page))
    (h : Finset Page × Prof w → ℝ) :
    ex (mu2 w μ κ) h = ex μ (fun x => ex (κ x) (fun C'' => h (C'', x.2))) := by
  unfold mu2
  rw [ex_bind]
  simp_rw [ex_map]

theorem ex_kern (ρ : PMF (Prof w × Prof w)) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (C : Finset Page) (g : Finset Page → ℝ) :
    ex (kern w ρ κ₁ κ₂ C) g =
      ex (condSnd ρ (profile w C)) (fun m => ex (κ₁ (C, m)) (fun C'' => ex (κ₂ (C'', m)) g)) := by
  unfold kern
  rw [ex_bind]
  simp_rw [ex_bind]

theorem ex_chain (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w))
    (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page)) (g : Finset Page → ℝ) :
    ex D (fun C => ex (kern w ρ κ₁ κ₂ C) g) = ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) g) := by
  rw [ex_mu2, ex_mu]
  simp_rw [ex_kern]

theorem mu_map {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) :
    (mu w D ρ).map (fun x => (profile w x.1, x.2)) = ρ := by
  unfold mu
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have : (fun C => (condSnd ρ (profile w C)).map
      ((fun x : Finset Page × Prof w => (profile w x.1, x.2)) ∘ Prod.mk C)) =
      (fun a => (condSnd ρ a).map (Prod.mk a)) ∘ profile w := by
    funext C
    rfl
  rw [this, ← PMF.bind_map, hD, bind_condSnd]

theorem ex_mu_prof {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) (g : Prof w × Prof w → ℝ) :
    ex (mu w D ρ) (fun x => g (profile w x.1, x.2)) = ex ρ g := by
  conv_rhs => rw [← mu_map w hD]
  rw [ex_map]

theorem mu_snd {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) :
    (mu w D ρ).map Prod.snd = ρ.map Prod.snd := by
  conv_rhs => rw [← mu_map w hD]
  rw [PMF.map_comp]
  rfl

theorem mu2_snd (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page)) :
    (mu2 w μ κ).map Prod.snd = μ.map Prod.snd := by
  unfold mu2
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have : ∀ x : Finset Page × Prof w,
      (κ x).map (Prod.snd ∘ fun C'' => (C'', x.2)) = PMF.pure x.2 := by
    intro x
    exact PMF.map_const (κ x) x.2
  simp_rw [this]
  rfl

theorem marginal_eq_ex (Q : PMF (Finset Page)) (i : Page) :
    marginal Q i = ex Q (fun C => if i ∈ C then 1 else 0) := by
  unfold marginal ex
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases h : i ∈ C <;> simp [h]

theorem margX_eq_ex (μ : PMF (Finset Page × Prof w)) (i : Page) :
    margX μ i = ex μ (fun x => if i ∈ x.1 then 1 else 0) := rfl

theorem margX_mu {D : PMF (Finset Page)} {y : Page → ℝ} (hD : marginal D = y)
    (ρ : PMF (Prof w × Prof w)) (i : Page) : margX (mu w D ρ) i = y i := by
  rw [margX_eq_ex, ex_mu, ← hD, marginal_eq_ex]
  congr 1
  funext C
  exact ex_const (condSnd ρ (profile w C)) (if i ∈ C then 1 else 0)

theorem wclass_pos (hw : ∀ i, 0 < w i) (v : WClass w) : 0 < (v : ℝ) := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.1 v.2
  rw [← hi]
  exact hw i

/-- The classes partition the pages. -/
theorem sum_cls (f : Page → ℝ) :
    ∑ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, f i = ∑ i, w i * f i := by
  have h1 : ∀ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, f i = ∑ i ∈ cls w v, w i * f i := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  simp_rw [h1]
  exact (Finset.sum_coe_sort (Finset.univ.image w) (fun v => ∑ i ∈ cls w v, w i * f i)).trans
    (Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i)) _)

theorem cost_le (C C'' C' : Finset Page) (hw : ∀ i, 0 ≤ w i) :
    cost w C C' ≤ cost w C'' C' + cost w C C'' := by
  unfold cost
  rw [← Finset.sum_union]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hw i
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_union] at hi ⊢
    by_cases h : i ∈ C'' <;> tauto
  · rw [Finset.disjoint_left]
    intro i h1 h2
    exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_sdiff.1 h2).1

theorem max_add_max (a b : ℝ) : max 0 (a - b) + max 0 (b - a) = |b - a| := by
  rcases le_total a b with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring

/-- The hypotheses of `transfer` for the distribution after `add_remove`. -/
theorem mu2_hyps {k : ℕ} {y y' : Page → ℝ} (hy' : y' ∈ fracCaches k) {D : PMF (Finset Page)}
    (hD : InClass w y D) (κ₁ : Finset Page × Prof w → PMF (Finset Page))
    (hκ₁ : ∀ i, ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
      (if i ∈ C' then 1 else 0) = y' i) :
    (∀ i, margX (mu2 w (mu w D (rhoLaw w y y')) κ₁) i = y' i) ∧
    (∀ x ∈ (mu2 w (mu w D (rhoLaw w y y')) κ₁).support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1) ∧
    (∀ v : WClass w, ∑ x, ((mu2 w (mu w D (rhoLaw w y y')) κ₁) x).toReal * ((x.2 v : ℕ) : ℝ) =
      classMass w y' v) := by
  have hDρ : D.map (profile w) = (rhoLaw w y y').map Prod.fst :=
    hD.1.trans (rhoLaw_fst w y y').symm
  have hsnd : (mu2 w (mu w D (rhoLaw w y y')) κ₁).map Prod.snd = profLaw w y' := by
    rw [mu2_snd, mu_snd w hDρ, rhoLaw_snd]
  refine ⟨fun i => ?_, fun x hx v => ?_, fun v => ?_⟩
  · rw [margX_eq_ex, ex_mu2, ← hκ₁ i, sum_sum_eq]
  · have : x.2 ∈ (profLaw w y').support := by
      rw [← hsnd]
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩
    exact profLaw_bounds w hy' this v
  · have h := ex_map (mu2 w (mu w D (rhoLaw w y y')) κ₁) Prod.snd (fun c => ((c v : ℕ) : ℝ))
    rw [hsnd] at h
    exact h.symm.trans (profLaw_mean w hy' v)

end Step

/-! ### The step and its guarantees -/

section Main

variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem step_spec (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) {k : ℕ}
    {y y' : Page → ℝ} (hy : y ∈ fracCaches k) (hy' : y' ∈ fracCaches k) {D : PMF (Finset Page)}
    (hD : InClass w y D) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (hκ₁ : (∀ i, ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
          (if i ∈ C' then 1 else 0) = y' i) ∧
      (∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ i, w i * max 0 (y' i - margX (mu w D (rhoLaw w y y')) i)) ∧
      (∀ v : WClass w,
        ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
            max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C' v : ℕ) : ℝ)) ≤
          ∑ x, (mu w D (rhoLaw w y y') x).toReal *
              max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ i ∈ cls w v, max 0 (margX (mu w D (rhoLaw w y y')) i - y' i)))
    (hκ₂ : (∀ x ∈ (mu2 w (mu w D (rhoLaw w y y')) κ₁).support, ∀ C' ∈ (κ₂ x).support,
          profile w C' = x.2) ∧
      (∀ i, ∑ x, ∑ C', (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal * (κ₂ x C').toReal *
          (if i ∈ C' then 1 else 0) = y' i) ∧
      ∑ x, ∑ C', (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal * (κ₂ x C').toReal *
          ∑ i ∈ C' \ x.1, w i ≤
        ∑ x, (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal *
          ∑ v : WClass w, (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) :
    InClass w y' (D.bind (kern w (rhoLaw w y y') κ₁ κ₂)) ∧
      ∑ C, ∑ C', (D C).toReal * (kern w (rhoLaw w y y') κ₁ κ₂ C C').toReal * ∑ i ∈ C' \ C, w i ≤
        4 * ∑ i, w i * |y' i - y i| := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hρ1 := rhoLaw_fst w y y'
  have hρ2 := rhoLaw_snd w y y'
  have hρ3 := rhoLaw_move w hw hw2 hy hy'
  generalize rhoLaw w y y' = ρ at hρ1 hρ2 hρ3 hκ₁ hκ₂ ⊢
  have hDρ : D.map (profile w) = ρ.map Prod.fst := hD.1.trans hρ1.symm
  have hsnd : (mu2 w (mu w D ρ) κ₁).map Prod.snd = profLaw w y' := by
    rw [mu2_snd, mu_snd w hDρ, hρ2]
  have hmy : ∀ i, margX (mu w D ρ) i = y i := margX_mu w hD.2 ρ
  obtain ⟨hk1, hk2, hk3⟩ := hκ₁
  obtain ⟨hp1, hp2, hp3⟩ := hκ₂
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · classical
    apply ext_of_ex
    intro c
    simp only [ex_map, ex_bind, ex_chain]
    have : ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (fun C' => if profile w C' = c then 1 else 0))
        = ex (mu2 w (mu w D ρ) κ₁) (fun x => if x.2 = c then 1 else 0) := by
      apply ex_congr
      intro x hx
      rw [ex_congr (κ₂ x) (g := fun _ => if x.2 = c then 1 else 0)
        (fun C' hC' => by rw [hp1 x hx C' hC']), ex_const]
    rw [this, ← hsnd, ex_map]
  · funext i
    rw [marginal_eq_ex, ex_bind, ex_chain, ← hp2 i, sum_sum_eq]
  · rw [sum_sum_eq]
    show ex D (fun C => ex (kern w ρ κ₁ κ₂ C) (cost w C)) ≤ _
    have e1 : ex D (fun C => ex (kern w ρ κ₁ κ₂ C) (cost w C)) =
        ex (mu w D ρ) (fun x => ex (κ₁ x) (fun C'' => ex (κ₂ (C'', x.2)) (cost w x.1))) := by
      rw [ex_mu]
      simp_rw [ex_kern]
    have e2 : ex (mu w D ρ) (fun x => ex (κ₁ x) (fun C'' => ex (κ₂ (C'', x.2)) (cost w x.1))) ≤
        ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1)) +
          ex (mu w D ρ) (fun x => ex (κ₁ x) (cost w x.1)) := by
      rw [ex_mu2, ← ex_add]
      refine ex_mono _ fun x => ?_
      rw [← ex_add]
      refine ex_mono _ fun C'' => ?_
      calc ex (κ₂ (C'', x.2)) (cost w x.1)
          ≤ ex (κ₂ (C'', x.2)) (fun C' => cost w C'' C' + cost w x.1 C'') :=
            ex_mono _ fun C' => cost_le w _ _ _ hw0
        _ = ex (κ₂ (C'', x.2)) (cost w C'') + cost w x.1 C'' := by
            rw [ex_add, ex_const]
    have hA : ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1)) ≤
        ∑ v : WClass w, (v : ℝ) *
          (ex (mu w D ρ) (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) +
            ∑ i ∈ cls w v, max 0 (margX (mu w D ρ) i - y' i)) := by
      calc ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1))
          ≤ ex (mu2 w (mu w D ρ) κ₁) (fun x => ∑ v : WClass w,
              (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) := by
            have := hp3
            rw [sum_sum_eq] at this
            exact this
        _ = ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ) (fun x => ex (κ₁ x)
              (fun C'' => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C'' v : ℕ) : ℝ)))) := by
            rw [ex_mu2]
            simp_rw [ex_sum, ex_mul_left]
        _ ≤ _ := by
            refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (wclass_pos w hw v).le
            have := hk3 v
            rw [sum_sum_eq] at this
            exact this
    have hB : ex (mu w D ρ) (fun x => ex (κ₁ x) (cost w x.1)) ≤
        ∑ i, w i * max 0 (y' i - margX (mu w D ρ) i) := by
      have := hk2
      rw [sum_sum_eq] at this
      exact this
    have hmove : ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ)
          (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) ≤
        3 * ∑ i, w i * |y' i - y i| := by
      calc ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ)
            (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)))
          = ∑ v : WClass w, (v : ℝ) * ex ρ
              (fun z => max 0 (((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ))) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [ex_mu_prof w hDρ (fun z => max 0 (((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)))]
        _ ≤ ∑ v : WClass w, (v : ℝ) * ex ρ
              (fun z => |((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)|) := by
            refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (wclass_pos w hw v).le
            exact ex_mono _ fun z => max_le (abs_nonneg _) (le_abs_self _)
        _ = ex ρ (fun z => ∑ v : WClass w, (v : ℝ) * |((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)|) := by
            rw [ex_sum]
            simp_rw [ex_mul_left]
        _ ≤ _ := hρ3
    have hcls : ∑ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, max 0 (margX (mu w D ρ) i - y' i) +
        ∑ i, w i * max 0 (y' i - margX (mu w D ρ) i) = ∑ i, w i * |y' i - y i| := by
      simp_rw [hmy]
      rw [sum_cls, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_add, max_add_max]
    simp_rw [mul_add, Finset.sum_add_distrib] at hA
    have hpos : 0 ≤ ∑ i, w i * |y' i - y i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (abs_nonneg _)
    linarith

/-- The kernel of `add_remove` for `μ = mu w D (rhoLaw w y y')`. -/
def kappa1 (hw0 : ∀ i, 0 ≤ w i) (D : PMF (Finset Page)) (y y' : Page → ℝ)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) : Finset Page × Prof w → PMF (Finset Page) :=
  Classical.choose (add_remove w hw0 y' hy' (mu w D (rhoLaw w y y')))

/-- The kernel of `transfer` for `μ₂ = mu2 w μ (kappa1 …)`. -/
def kappa2 (hw0 : ∀ i, 0 ≤ w i) {k : ℕ} (D : PMF (Finset Page)) (y y' : Page → ℝ)
    (H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D) :
    Finset Page × Prof w → PMF (Finset Page) :=
  Classical.choose (transfer w hw0 y' (mu2 w (mu w D (rhoLaw w y y')) (kappa1 w hw0 D y y' H.2.1.1))
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).1
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.1
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.2)

open Classical in
/-- The rounding map (the identity kernel when the hypotheses fail). -/
def Tmap (hw0 : ∀ i, 0 ≤ w i) (k : ℕ) (D : PMF (Finset Page)) (y y' : Page → ℝ) :
    Finset Page → PMF (Finset Page) :=
  if H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D then
    kern w (rhoLaw w y y') (kappa1 w hw0 D y y' H.2.1.1) (kappa2 w hw0 D y y' H)
  else fun C => PMF.pure C

end Main

end Assembly

end PagingWithDelay.BBN

namespace PagingWithDelay.BBN

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Assembly in
/-- **Online rounding for weighted paging** (Bansal–Buchbinder–Naor, Theorem 4.1, fetch-cost
version with constant `4`). -/
theorem bbn_rounding (w : Page → ℝ) (hw : ∀ i, 0 < w i)
    (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) (k : ℕ) :
    ∃ T : PMF (Finset Page) → (Page → ℝ) → (Page → ℝ) → Finset Page → PMF (Finset Page),
      ∀ D y y', y ∈ fracCaches k → y' ∈ fracCaches k → InClass w y D →
        InClass w y' (D.bind (T D y y')) ∧
        ∑ C, ∑ C', (D C).toReal * (T D y y' C C').toReal * ∑ i ∈ C' \ C, w i ≤
          4 * ∑ i, w i * |y' i - y i| := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  refine ⟨Tmap w hw0 k, fun D y y' hy hy' hD => ?_⟩
  have H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D := ⟨hy, hy', hD⟩
  rw [Tmap, dif_pos H]
  exact step_spec w hw hw2 hy hy' hD _ _
    (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y'))))
    (Classical.choose_spec (transfer w hw0 y'
      (mu2 w (mu w D (rhoLaw w y y')) (kappa1 w hw0 D y y' H.2.1.1))
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).1
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.1
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.2))

theorem inClass_pure (w : Page → ℝ) (C₀ : Finset Page) :
    InClass w (indicator C₀) (PMF.pure C₀) := by
  refine ⟨by rw [PMF.pure_map, profLaw_indicator], ?_⟩
  funext i
  unfold marginal indicator
  rw [Finset.sum_eq_single C₀]
  · simp
  · intro C _ hC
    simp [PMF.pure_apply, hC]
  · simp

theorem card_of_inClass (w : Page → ℝ) {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k)
    {D : PMF (Finset Page)} (hD : InClass w y D) : ∀ C ∈ D.support, C.card = k := by
  intro C hC
  have : profile w C ∈ (profLaw w y).support := by
    rw [← hD.1]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨C, hC, rfl⟩
  exact card_of_profLaw w hy this C rfl

end PagingWithDelay.BBN
