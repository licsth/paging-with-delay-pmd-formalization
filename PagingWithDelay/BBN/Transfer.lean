import PagingWithDelay.BBN.Defs

/-!
# Hole/excess transfers within each weight class (BBN)

Proof of `transfer`. The state is a pair `((C, m), D)` of the initial cache `C`, the target
profile `m`, and the current cache `D`. A *round* for a class `v` moves one page of class `v` from
caches with an excess in `v` to caches with a hole in `v` (product coupling), preserving the
marginals. Each round decreases `∑ᵥ (max excess + max hole)` over the support, so finitely many
rounds reach the target profile.
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace PagingWithDelay.BBN

namespace Transfer

/-! ### Expectations over finite PMFs -/

section Expect

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The expectation of `f` under `p`. -/
def ex (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

lemma toReal_bind (p : PMF α) (k : α → PMF β) (b : β) :
    ((p.bind k) b).toReal = ∑ a, (p a).toReal * (k a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

lemma ex_bind (p : PMF α) (k : α → PMF β) (f : β → ℝ) :
    ex (p.bind k) f = ex p (fun a => ex (k a) f) := by
  unfold ex
  simp_rw [toReal_bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

lemma ex_pure [DecidableEq α] (a : α) (f : α → ℝ) : ex (PMF.pure a) f = f a := by
  simp only [ex, PMF.pure_apply]
  simp [apply_ite ENNReal.toReal, ite_mul]

lemma ex_map (p : PMF α) (h : α → β) (f : β → ℝ) : ex (p.map h) f = ex p (f ∘ h) := by
  classical
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]
  rfl

lemma toReal_ne_zero {p : PMF α} {a : α} : (p a).toReal ≠ 0 ↔ p a ≠ 0 := by
  rw [Ne, ENNReal.toReal_eq_zero_iff]
  simp [PMF.apply_ne_top]

lemma toReal_pos {p : PMF α} {a : α} (h : p a ≠ 0) : 0 < (p a).toReal :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (toReal_ne_zero.2 h))

/-- One step: with probability `r z` move to `g z`, otherwise stay at `b₀`. -/
def stepK {Z : Type*} [Fintype Z] (r : Z → ℝ) (g : Z → β) (b₀ : β) : PMF β :=
  if h : (∀ z, 0 ≤ r z) ∧ ∑ z, r z ≤ 1 then
    (PMF.ofFintype (fun o : Option Z => ENNReal.ofReal (o.elim (1 - ∑ z, r z) r)) (by
      rw [Fintype.sum_option]
      simp only [Option.elim]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => h.1 z),
        ← ENNReal.ofReal_add (by linarith [h.2]) (Finset.sum_nonneg fun z _ => h.1 z)]
      simp)).map (fun o => o.elim b₀ g)
  else PMF.pure b₀

variable {Z : Type*} [Fintype Z]

lemma ex_stepK (r : Z → ℝ) (g : Z → β) (b₀ : β) (h0 : ∀ z, 0 ≤ r z) (h1 : ∑ z, r z ≤ 1)
    (f : β → ℝ) : ex (stepK r g b₀) f = f b₀ + ∑ z, r z * (f (g z) - f b₀) := by
  rw [stepK, dif_pos ⟨h0, h1⟩, ex_map]
  unfold ex
  rw [Fintype.sum_option]
  simp only [PMF.ofFintype_apply, Option.elim, Function.comp]
  rw [ENNReal.toReal_ofReal (by linarith)]
  simp_rw [ENNReal.toReal_ofReal (h0 _)]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma mem_support_stepK (r : Z → ℝ) (g : Z → β) (b₀ : β) (h0 : ∀ z, 0 ≤ r z)
    (h1 : ∑ z, r z ≤ 1) {b : β} (hb : b ∈ (stepK r g b₀).support) :
    (b = b₀ ∧ ∑ z, r z < 1) ∨ ∃ z, r z ≠ 0 ∧ b = g z := by
  rw [stepK, dif_pos ⟨h0, h1⟩, PMF.mem_support_map_iff] at hb
  obtain ⟨o, ho, rfl⟩ := hb
  rw [PMF.mem_support_ofFintype_iff, Ne, ENNReal.ofReal_eq_zero, not_le] at ho
  cases o with
  | none => exact Or.inl ⟨rfl, by simp only [Option.elim] at ho; linarith⟩
  | some z => exact Or.inr ⟨z, ne_of_gt ho, rfl⟩

lemma map_stepK {γ : Type*} (r : Z → ℝ) (g : Z → β) (b₀ : β) (h : β → γ) (c : γ)
    (hg : ∀ z, h (g z) = c) (hb : h b₀ = c) : (stepK r g b₀).map h = PMF.pure c := by
  unfold stepK
  split_ifs
  · rw [PMF.map_comp]
    have : (h ∘ fun o : Option Z => o.elim b₀ g) = Function.const _ c := by
      funext o; cases o <;> simp [hg, hb]
    rw [this, PMF.map_const]
  · rw [PMF.pure_map, hb]

end Expect

/-! ### Conditional distributions (copied from `PagingWithDelay.Rounding`) -/

section Cond

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
lemma map_fst_apply (π : PMF (α × β)) (a : α) : π.map Prod.fst a = ∑ b, π (a, b) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The conditional distribution of the second coordinate given the first. -/
def condSnd (π : PMF (α × β)) (a : α) : PMF β :=
  if h : π.map Prod.fst a = 0 then π.map Prod.snd else
    PMF.ofFintype (fun b => π (a, b) / π.map Prod.fst a) (by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← map_fst_apply]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _))

lemma bind_condSnd (π : PMF (α × β)) :
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

lemma condSnd_ne_zero {π : PMF (α × β)} {a : α} {b : β} (ha : π.map Prod.fst a ≠ 0)
    (hb : condSnd π a b ≠ 0) : π (a, b) ≠ 0 := by
  unfold condSnd at hb
  rw [dif_neg ha, PMF.ofFintype_apply] at hb
  intro h
  rw [h, ENNReal.zero_div] at hb
  exact hb rfl

lemma ex_cond (π : PMF (α × β)) (μ : PMF α) (h : π.map Prod.fst = μ) (f : α × β → ℝ) :
    ∑ a, ∑ b, (μ a).toReal * (condSnd π a b).toReal * f (a, b) = ex π f := by
  have e : ex π f = ex ((π.map Prod.fst).bind (fun a => (condSnd π a).map (Prod.mk a))) f := by
    rw [bind_condSnd]
  rw [e, ex_bind, h]
  simp only [ex_map]
  unfold ex
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Function.comp, mul_assoc]

end Cond

/-! ### States, counts and the round -/

section Round

variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- States: `((initial cache, target profile), current cache)`. -/
abbrev St := (Finset Page × Prof w) × Finset Page

/-- The indicator of a cache. -/
def ind (D : Finset Page) (i : Page) : ℝ := if i ∈ D then 1 else 0

/-- The number of pages of class `v` in the current cache. -/
def cnt (v : WClass w) (z : St w) : ℕ := (z.2 ∩ cls w v).card

/-- The target number of pages of class `v`. -/
def tg (v : WClass w) (z : St w) : ℕ := (z.1.2 v : ℕ)

/-- Some page of class `v` lies in `e` but not in `h`. -/
def Ex (v : WClass w) (h e : St w) : Prop := ∃ p, p ∈ e.2 ∧ p ∉ h.2 ∧ w p = v

open Classical in
/-- The cache of `e` after giving a page of class `v` to `h`. -/
def remC (v : WClass w) (h e : St w) : Finset Page :=
  if hx : Ex w v h e then e.2.erase hx.choose else e.2

open Classical in
/-- The cache of `h` after receiving a page of class `v` from `e`. -/
def addC (v : WClass w) (h e : St w) : Finset Page :=
  if hx : Ex w v h e then insert hx.choose h.2 else h.2

open Classical in
/-- Whether `i` is the page moved from `e` to `h`. -/
def qi (v : WClass w) (h e : St w) (i : Page) : ℝ :=
  if hx : Ex w v h e then (if i = hx.choose then 1 else 0) else 0

lemma mem_cls {p : Page} {u : ℝ} : p ∈ cls w u ↔ w p = u := by simp [cls]

lemma cls_eq {p : Page} {u v : WClass w} (hu : p ∈ cls w u) (hv : w p = v) : u = v :=
  Subtype.ext (((mem_cls w).1 hu).symm.trans hv)

lemma class_nonneg (hw : ∀ i, 0 ≤ w i) (u : WClass w) : 0 ≤ (u : ℝ) := by
  obtain ⟨a, _, ha⟩ := Finset.mem_image.1 u.2
  rw [← ha]; exact hw a

lemma ind_remC (v : WClass w) (h e : St w) (i : Page) :
    ind (remC w v h e) i = ind e.2 i - qi w v h e i := by
  unfold remC qi
  by_cases hx : Ex w v h e
  · rw [dif_pos hx, dif_pos hx]
    by_cases hi : i = hx.choose
    · rw [if_pos hi]; simp [ind, hi, hx.choose_spec.1]
    · rw [if_neg hi]; simp [ind, Finset.mem_erase, hi]
  · rw [dif_neg hx, dif_neg hx]; simp

lemma ind_addC (v : WClass w) (h e : St w) (i : Page) :
    ind (addC w v h e) i = ind h.2 i + qi w v h e i := by
  unfold addC qi
  by_cases hx : Ex w v h e
  · rw [dif_pos hx, dif_pos hx]
    by_cases hi : i = hx.choose
    · rw [if_pos hi]; simp [ind, hi, hx.choose_spec.2.1]
    · rw [if_neg hi]; simp [ind, Finset.mem_insert, hi]
  · rw [dif_neg hx, dif_neg hx]; simp

lemma card_erase_inter (D S : Finset Page) (p : Page) (hp : p ∈ D) :
    ((D.erase p) ∩ S).card + (if p ∈ S then 1 else 0) = (D ∩ S).card := by
  rw [Finset.erase_inter]
  split_ifs with hs
  · have hm : p ∈ D ∩ S := Finset.mem_inter.2 ⟨hp, hs⟩
    rw [Finset.card_erase_of_mem hm]
    have := Finset.card_pos.2 ⟨p, hm⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hs])]; rfl

lemma card_insert_inter (D S : Finset Page) (p : Page) (hp : p ∉ D) :
    ((insert p D) ∩ S).card = (D ∩ S).card + (if p ∈ S then 1 else 0) := by
  split_ifs with hs
  · rw [Finset.insert_inter_of_mem hs, Finset.card_insert_of_notMem (by simp [hp])]
  · rw [Finset.insert_inter_of_notMem hs]; rfl

/-- If `e` has an excess and `h` a hole in class `v`, and both targets are within `1` of `K v`,
some page of class `v` lies in `e` but not in `h`. -/
lemma ex_of (K : WClass w → ℝ) {v : WClass w} {e h : St w} (hbe : K v - 1 < (tg w v e : ℝ))
    (hbh : (tg w v h : ℝ) < K v + 1) (he : tg w v e < cnt w v e) (hh : cnt w v h < tg w v h) :
    Ex w v h e := by
  have h1 : (tg w v e : ℝ) + 1 ≤ cnt w v e := by exact_mod_cast he
  have h2 : (cnt w v h : ℝ) + 1 ≤ tg w v h := by exact_mod_cast hh
  have h3 : cnt w v h < cnt w v e := by
    have : (cnt w v h : ℝ) < cnt w v e := by linarith
    exact_mod_cast this
  by_contra hne
  apply absurd h3
  apply not_lt.2
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_inter] at hp ⊢
  refine ⟨?_, hp.2⟩
  by_contra hq
  exact hne ⟨p, hp.1, hq, (mem_cls w).1 hp.2⟩

variable (ν : PMF (St w)) (v : WClass w)

/-- The probability of an excess in class `v`. -/
def PE : ℝ := ∑ z, if tg w v z < cnt w v z then (ν z).toReal else 0

/-- The probability of a hole in class `v`. -/
def PH : ℝ := ∑ z, if cnt w v z < tg w v z then (ν z).toReal else 0

/-- `max (PE, PH)`. -/
def MM : ℝ := max (PE w ν v) (PH w ν v)

/-- The rate at which `z` is paired with `z₂`. -/
def rr (z z₂ : St w) : ℝ :=
  if (tg w v z < cnt w v z ∧ cnt w v z₂ < tg w v z₂) ∨
      (cnt w v z < tg w v z ∧ tg w v z₂ < cnt w v z₂) then (ν z₂).toReal / MM w ν v else 0

/-- The state of `z` after being paired with `z₂`. -/
def gg (z z₂ : St w) : St w :=
  if tg w v z < cnt w v z then (z.1, remC w v z₂ z) else (z.1, addC w v z z₂)

/-- One round for class `v`. -/
def round : PMF (St w) := ν.bind (fun z => stepK (rr w ν v z) (gg w v z) z)

variable {w ν v}

lemma rr_nonneg (hM : 0 < MM w ν v) (z z₂ : St w) : 0 ≤ rr w ν v z z₂ := by
  unfold rr; split_ifs
  · exact div_nonneg ENNReal.toReal_nonneg hM.le
  · exact le_rfl

lemma sum_rr (z : St w) : ∑ z₂, rr w ν v z z₂ =
    (if tg w v z < cnt w v z then PH w ν v else if cnt w v z < tg w v z then PE w ν v else 0) /
      MM w ν v := by
  unfold rr PE PH
  by_cases h1 : tg w v z < cnt w v z
  · have h2 : ¬ cnt w v z < tg w v z := by omega
    simp only [h1, h2, true_and, false_and, or_false, ↓reduceIte]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z₂ _ => ?_
    split_ifs <;> simp
  · by_cases h2 : cnt w v z < tg w v z
    · simp only [h1, h2, true_and, false_and, false_or, ↓reduceIte]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun z₂ _ => ?_
      split_ifs <;> simp
    · simp [h1, h2]

lemma sum_rr_le (hM : 0 < MM w ν v) (z : St w) : ∑ z₂, rr w ν v z z₂ ≤ 1 := by
  rw [sum_rr]
  apply div_le_one_of_le₀ _ hM.le
  unfold MM
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _
  · exact hM.le

lemma ex_round (hM : 0 < MM w ν v) (f : St w → ℝ) :
    ex (round w ν v) f = ex ν f +
      ∑ z, ∑ z₂, (ν z).toReal * rr w ν v z z₂ * (f (gg w v z z₂) - f z) := by
  rw [round, ex_bind]
  have hK : ∀ z, ex (stepK (rr w ν v z) (gg w v z) z) f =
      f z + ∑ z₂, rr w ν v z z₂ * (f (gg w v z z₂) - f z) := fun z =>
    ex_stepK _ _ _ (rr_nonneg hM z) (sum_rr_le hM z) f
  simp only [hK]
  simp only [ex, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma pair_cancel {Z : Type*} [Fintype Z] (T A : Z → Z → ℝ)
    (h : ∀ z z₂, T z z₂ = A z₂ z - A z z₂) : ∑ z, ∑ z₂, T z z₂ = 0 := by
  simp_rw [h, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp

lemma round_marg (hM : 0 < MM w ν v) (i : Page) :
    ex (round w ν v) (fun z => ind z.2 i) = ex ν (fun z => ind z.2 i) := by
  rw [ex_round hM]
  suffices hs : ∑ z, ∑ z₂, (ν z).toReal * rr w ν v z z₂ *
      (ind (gg w v z z₂).2 i - ind z.2 i) = 0 by rw [hs, add_zero]
  apply pair_cancel _ (fun e h => if tg w v e < cnt w v e ∧ cnt w v h < tg w v h then
    (ν e).toReal * ((ν h).toReal / MM w ν v) * qi w v h e i else 0)
  intro z z₂
  simp only [rr, gg]
  by_cases h1 : tg w v z < cnt w v z <;> by_cases h2 : cnt w v z₂ < tg w v z₂ <;>
    by_cases h3 : cnt w v z < tg w v z <;> by_cases h4 : tg w v z₂ < cnt w v z₂ <;>
    first | omega | (simp only [h1, h2, h3, h4, and_true, and_false,
      or_false, false_or, ↓reduceIte, ind_remC, ind_addC]; ring)

lemma round_map_fst : (round w ν v).map Prod.fst = ν.map Prod.fst := by
  rw [round, PMF.map_bind]
  have : ∀ z, (stepK (rr w ν v z) (gg w v z) z).map Prod.fst = PMF.pure z.1 := fun z =>
    map_stepK _ _ _ _ _ (fun z₂ => by unfold gg; split_ifs <;> rfl) rfl
  simp only [this]
  rfl

end Round


/-! ### Cost, successors and the potential -/

section Main

variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- The weight fetched so far plus the weight of the remaining holes. -/
def F (z : St w) : ℝ :=
  ∑ i ∈ z.2 \ z.1.1, w i + ∑ u : WClass w, (u : ℝ) * max 0 ((tg w u z : ℝ) - cnt w u z)

/-- The weight of the initial holes. -/
def G (x : Finset Page × Prof w) : ℝ :=
  ∑ u : WClass w, (u : ℝ) * max 0 (((x.2 u : ℕ) : ℝ) - ((profile w x.1 u : ℕ) : ℝ))

open Classical in
/-- The support as a finset. -/
def suppF (ν : PMF (St w)) : Finset (St w) := Finset.univ.filter (fun z => ν z ≠ 0)

/-- The largest excess in class `u` over the support. -/
def mS (ν : PMF (St w)) (u : WClass w) : ℕ := (suppF w ν).sup (fun z => cnt w u z - tg w u z)

/-- The largest hole in class `u` over the support. -/
def mD (ν : PMF (St w)) (u : WClass w) : ℕ := (suppF w ν).sup (fun z => tg w u z - cnt w u z)

/-- The potential. -/
def Φ (ν : PMF (St w)) : ℕ := ∑ u, (mS w ν u + mD w ν u)

/-- The invariant of the rounds. -/
def Inv (μ : PMF (Finset Page × Prof w)) (y' : Page → ℝ) (ν : PMF (St w)) : Prop :=
  ν.map Prod.fst = μ ∧ (∀ i, ex ν (fun z => ind z.2 i) = y' i) ∧
    (∀ z, ν z ≠ 0 → F w z ≤ G w z.1)

variable {w}

lemma mem_suppF {ν : PMF (St w)} {z : St w} : z ∈ suppF w ν ↔ ν z ≠ 0 := by simp [suppF]

lemma max_aux {a b : ℝ} (h : b + 1 ≤ a) (u : ℝ) :
    u * max 0 (a - (b + 1)) + u = u * max 0 (a - b) := by
  have h1 : max 0 (a - (b + 1)) = a - (b + 1) := max_eq_right (by linarith)
  have h2 : max 0 (a - b) = a - b := max_eq_right (by linarith)
  rw [h1, h2]; ring

lemma F_rem (hw : ∀ i, 0 ≤ w i) {v : WClass w} {z : St w} {p : Page} (hp : p ∈ z.2)
    (hpv : w p = v) (hex : tg w v z < cnt w v z) : F w (z.1, z.2.erase p) ≤ F w z := by
  unfold F
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hi ⊢
      exact ⟨hi.1.2, hi.2⟩
    · intro i _ _; exact hw i
  · apply Finset.sum_le_sum
    intro u _
    apply mul_le_mul_of_nonneg_left _ (class_nonneg w hw u)
    have hc := card_erase_inter z.2 (cls w u) p hp
    show max 0 ((tg w u z : ℝ) - (((z.2.erase p) ∩ cls w u).card : ℕ)) ≤
      max 0 ((tg w u z : ℝ) - ((z.2 ∩ cls w u).card : ℕ))
    by_cases hu : p ∈ cls w u
    · have huv : u = v := cls_eq w hu hpv
      subst huv
      rw [if_pos hu] at hc
      unfold cnt at hex
      have h1 : tg w u z ≤ ((z.2.erase p) ∩ cls w u).card := by omega
      have h2 : (tg w u z : ℝ) ≤ (((z.2.erase p) ∩ cls w u).card : ℕ) := by exact_mod_cast h1
      exact (max_le le_rfl (by linarith)).trans (le_max_left _ _)
    · rw [if_neg hu, add_zero] at hc
      rw [hc]

lemma F_add (hw : ∀ i, 0 ≤ w i) {v : WClass w} {z : St w} {p : Page} (hp : p ∉ z.2)
    (hpv : w p = v) (hh : cnt w v z < tg w v z) : F w (z.1, insert p z.2) ≤ F w z := by
  unfold F
  have h1 : ∑ i ∈ insert p z.2 \ z.1.1, w i ≤ w p + ∑ i ∈ z.2 \ z.1.1, w i := by
    calc ∑ i ∈ insert p z.2 \ z.1.1, w i ≤ ∑ i ∈ insert p (z.2 \ z.1.1), w i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_sdiff, Finset.mem_insert] at hi ⊢
            tauto
          · intro i _ _; exact hw i
      _ = w p + ∑ i ∈ z.2 \ z.1.1, w i := Finset.sum_insert (by simp [hp])
  have h2 : ∀ u : WClass w, (u : ℝ) * max 0 ((tg w u (z.1, insert p z.2) : ℝ) -
      cnt w u (z.1, insert p z.2)) + (if u = v then (v : ℝ) else 0) ≤
      (u : ℝ) * max 0 ((tg w u z : ℝ) - cnt w u z) := by
    intro u
    have hc := card_insert_inter z.2 (cls w u) p hp
    show (u : ℝ) * max 0 ((tg w u z : ℝ) - (((insert p z.2) ∩ cls w u).card : ℕ)) +
      (if u = v then (v : ℝ) else 0) ≤ (u : ℝ) * max 0 ((tg w u z : ℝ) - ((z.2 ∩ cls w u).card : ℕ))
    by_cases hu : u = v
    · subst hu
      rw [if_pos rfl, hc, if_pos ((mem_cls w).2 hpv)]
      unfold cnt at hh
      have : (((z.2 ∩ cls w u).card : ℕ) : ℝ) + 1 ≤ tg w u z := by exact_mod_cast hh
      push_cast
      exact (max_aux this _).le
    · rw [if_neg hu, hc, if_neg (fun h => hu (cls_eq w h hpv)), add_zero, add_zero]
  have h3 := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (WClass w))) => h2 u)
  rw [Finset.sum_add_distrib] at h3
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h3
  rw [← hpv] at h3
  linarith

lemma succ (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) {z z' : St w} (hz : ν z ≠ 0)
    (hz' : z' ∈ (stepK (rr w ν v z) (gg w v z) z).support) :
    z'.1 = z.1 ∧ F w z' ≤ F w z ∧ (∀ u, u ≠ v → cnt w u z' = cnt w u z) ∧
    ((z' = z ∧ (tg w v z < cnt w v z → PH w ν v < MM w ν v) ∧
        (cnt w v z < tg w v z → PE w ν v < MM w ν v)) ∨
      (tg w v z < cnt w v z ∧ cnt w v z' + 1 = cnt w v z) ∨
      (cnt w v z < tg w v z ∧ cnt w v z' = cnt w v z + 1)) := by
  rcases mem_support_stepK _ _ _ (rr_nonneg hM z) (sum_rr_le hM z) hz' with
    ⟨rfl, hlt⟩ | ⟨z₂, hr, rfl⟩
  · refine ⟨rfl, le_rfl, fun _ _ => rfl, Or.inl ⟨rfl, fun h => ?_, fun h => ?_⟩⟩
    · rw [sum_rr, if_pos h, div_lt_one hM] at hlt; exact hlt
    · rw [sum_rr, if_neg (by omega), if_pos h, div_lt_one hM] at hlt; exact hlt
  · have hc : ((tg w v z < cnt w v z ∧ cnt w v z₂ < tg w v z₂) ∨
        (cnt w v z < tg w v z ∧ tg w v z₂ < cnt w v z₂)) ∧ ν z₂ ≠ 0 := by
      unfold rr at hr
      split_ifs at hr with hc
      · refine ⟨hc, fun h0 => hr ?_⟩
        simp [h0]
      · exact absurd rfl hr
    obtain ⟨hc, hz₂⟩ := hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : Ex w v z₂ z := ex_of w K (hB z hz v).1 (hB z₂ hz₂ v).2 h1 h2
      have hg : gg w v z z₂ = (z.1, z.2.erase hx.choose) := by
        unfold gg remC; rw [if_pos h1, dif_pos hx]
      obtain ⟨hp1, -, hp3⟩ := hx.choose_spec
      rw [hg]
      refine ⟨rfl, F_rem hw hp1 hp3 h1, fun u hu => ?_, Or.inr (Or.inl ⟨h1, ?_⟩)⟩
      · have hc := card_erase_inter z.2 (cls w u) _ hp1
        rw [if_neg (fun h => hu (cls_eq w h hp3)), add_zero] at hc
        exact hc
      · have hc := card_erase_inter z.2 (cls w v) _ hp1
        rw [if_pos ((mem_cls w).2 hp3)] at hc
        exact hc
    · have hx : Ex w v z z₂ := ex_of w K (hB z₂ hz₂ v).1 (hB z hz v).2 h2 h1
      have hg : gg w v z z₂ = (z.1, insert hx.choose z.2) := by
        unfold gg addC; rw [if_neg (show ¬ tg w v z < cnt w v z by omega), dif_pos hx]
      obtain ⟨-, hp2, hp3⟩ := hx.choose_spec
      rw [hg]
      refine ⟨rfl, F_add hw hp2 hp3 h1, fun u hu => ?_, Or.inr (Or.inr ⟨h1, ?_⟩)⟩
      · have hc := card_insert_inter z.2 (cls w u) _ hp2
        rw [if_neg (fun h => hu (cls_eq w h hp3)), add_zero] at hc
        exact hc
      · have hc := card_insert_inter z.2 (cls w v) _ hp2
        rw [if_pos ((mem_cls w).2 hp3)] at hc
        exact hc

lemma round_supp {ν : PMF (St w)} {v : WClass w} {z' : St w} (h : round w ν v z' ≠ 0) :
    ∃ z, ν z ≠ 0 ∧ z' ∈ (stepK (rr w ν v z) (gg w v z) z).support := by
  have : z' ∈ (round w ν v).support := (PMF.mem_support_iff _ _).2 h
  rw [round, PMF.mem_support_bind_iff] at this
  obtain ⟨z, hz, hz'⟩ := this
  exact ⟨z, (PMF.mem_support_iff _ _).1 hz, hz'⟩

lemma succ_facts (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) {z' : St w} (hz' : round w ν v z' ≠ 0) :
    ∃ z, ν z ≠ 0 ∧ F w z' ≤ F w z ∧ z'.1 = z.1 ∧ (∀ u, tg w u z' = tg w u z) ∧
      (∀ u, u ≠ v → cnt w u z' = cnt w u z) ∧
      ((z' = z ∧ (tg w v z < cnt w v z → PH w ν v < MM w ν v) ∧
          (cnt w v z < tg w v z → PE w ν v < MM w ν v)) ∨
        (tg w v z < cnt w v z ∧ cnt w v z' + 1 = cnt w v z) ∨
        (cnt w v z < tg w v z ∧ cnt w v z' = cnt w v z + 1)) := by
  obtain ⟨z, hz, hz''⟩ := round_supp hz'
  obtain ⟨h1, hF, hc, hcase⟩ := succ hw K hB hM hz hz''
  exact ⟨z, hz, hF, h1, fun u => by unfold tg; rw [h1], hc, hcase⟩

lemma Φ_lt (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) (hE : ∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z)
    (hH : ∃ z, ν z ≠ 0 ∧ cnt w v z < tg w v z) : Φ w (round w ν v) < Φ w ν := by
  have hle : ∀ u, mS w (round w ν v) u ≤ mS w ν u ∧ mD w (round w ν v) u ≤ mD w ν u := by
    intro u
    constructor
    · apply Finset.sup_le
      intro z' hz'
      obtain ⟨z, hz, -, -, htg, hcnt, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
      have hle : cnt w u z - tg w u z ≤ mS w ν u :=
        Finset.le_sup (f := fun z => cnt w u z - tg w u z) ((mem_suppF).2 hz)
      show cnt w u z' - tg w u z' ≤ mS w ν u
      rw [htg u]
      by_cases hu : u = v
      · subst hu
        rcases hcase with ⟨rfl, -, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩ <;> omega
      · rw [hcnt u hu]; exact hle
    · apply Finset.sup_le
      intro z' hz'
      obtain ⟨z, hz, -, -, htg, hcnt, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
      have hle : tg w u z - cnt w u z ≤ mD w ν u :=
        Finset.le_sup (f := fun z => tg w u z - cnt w u z) ((mem_suppF).2 hz)
      show tg w u z' - cnt w u z' ≤ mD w ν u
      rw [htg u]
      by_cases hu : u = v
      · subst hu
        rcases hcase with ⟨rfl, -, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩ <;> omega
      · rw [hcnt u hu]; exact hle
  have hlt : mS w (round w ν v) v + mD w (round w ν v) v < mS w ν v + mD w ν v := by
    obtain ⟨z₁, hz₁, he₁⟩ := hE
    obtain ⟨z₂, hz₂, hh₂⟩ := hH
    have hS1 : cnt w v z₁ - tg w v z₁ ≤ mS w ν v :=
      Finset.le_sup (f := fun z => cnt w v z - tg w v z) ((mem_suppF).2 hz₁)
    have hD1 : tg w v z₂ - cnt w v z₂ ≤ mD w ν v :=
      Finset.le_sup (f := fun z => tg w v z - cnt w v z) ((mem_suppF).2 hz₂)
    have h1 := hle v
    rcases le_or_gt (PE w ν v) (PH w ν v) with hP | hP
    · have hMM : MM w ν v = PH w ν v := max_eq_right hP
      have hS : mS w (round w ν v) v ≤ mS w ν v - 1 := by
        apply Finset.sup_le
        intro z' hz'
        obtain ⟨z, hz, -, -, htg, -, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
        have hle : cnt w v z - tg w v z ≤ mS w ν v :=
          Finset.le_sup (f := fun z => cnt w v z - tg w v z) ((mem_suppF).2 hz)
        show cnt w v z' - tg w v z' ≤ mS w ν v - 1
        rw [htg v]
        rcases hcase with ⟨heq, hA, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩
        · rw [heq]
          have : ¬ tg w v z < cnt w v z := fun h => lt_irrefl _ (hMM ▸ hA h)
          omega
        · omega
        · omega
      omega
    · have hMM : MM w ν v = PE w ν v := max_eq_left hP.le
      have hD : mD w (round w ν v) v ≤ mD w ν v - 1 := by
        apply Finset.sup_le
        intro z' hz'
        obtain ⟨z, hz, -, -, htg, -, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
        have hle : tg w v z - cnt w v z ≤ mD w ν v :=
          Finset.le_sup (f := fun z => tg w v z - cnt w v z) ((mem_suppF).2 hz)
        show tg w v z' - cnt w v z' ≤ mD w ν v - 1
        rw [htg v]
        rcases hcase with ⟨heq, -, hA⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩
        · rw [heq]
          have : ¬ cnt w v z < tg w v z := fun h => lt_irrefl _ (hMM ▸ hA h)
          omega
        · omega
        · omega
      omega
  unfold Φ
  apply Finset.sum_lt_sum
  · intro u _; exact add_le_add (hle u).1 (hle u).2
  · exact ⟨v, Finset.mem_univ _, hlt⟩

lemma mean_zero {ν : PMF (St w)} {μ : PMF (Finset Page × Prof w)} {y' : Page → ℝ}
    (hfst : ν.map Prod.fst = μ) (hm : ∀ i, ex ν (fun z => ind z.2 i) = y' i)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v)
    (v : WClass w) : ∑ z, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) = 0 := by
  have hc : ∀ z, (cnt w v z : ℝ) = ∑ p ∈ cls w v, ind z.2 p := by
    intro z
    unfold cnt ind
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have h1 : ∑ z, (ν z).toReal * (cnt w v z : ℝ) = classMass w y' v := by
    simp only [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold classMass
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hm p]; rfl
  have h2 : ∑ z, (ν z).toReal * (tg w v z : ℝ) = classMass w y' v := by
    have := ex_map ν Prod.fst (fun x => ((x.2 v : ℕ) : ℝ))
    rw [hfst] at this
    rw [← hmean v]
    exact this.symm
  simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]

lemma signs {ν : PMF (St w)} {v : WClass w} {z₀ : St w} (hz₀ : ν z₀ ≠ 0)
    (hne : cnt w v z₀ ≠ tg w v z₀) (h0 : ∑ z, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) = 0) :
    (∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z) ∧ (∃ z, ν z ≠ 0 ∧ cnt w v z < tg w v z) := by
  constructor
  · by_contra hcon
    push Not at hcon
    have hnp : ∀ z ∈ Finset.univ, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) ≤ 0 := by
      intro z _
      by_cases hz : ν z = 0
      · simp [hz]
      · apply mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        have : (cnt w v z : ℝ) ≤ tg w v z := by exact_mod_cast hcon z hz
        linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h0 z₀ (Finset.mem_univ _)
    have hlt : cnt w v z₀ < tg w v z₀ := lt_of_le_of_ne (hcon z₀ hz₀) hne
    have h2 : (cnt w v z₀ : ℝ) < tg w v z₀ := by exact_mod_cast hlt
    have := mul_neg_of_pos_of_neg (toReal_pos hz₀) (by linarith : (cnt w v z₀ : ℝ) - tg w v z₀ < 0)
    linarith
  · by_contra hcon
    push Not at hcon
    have hnp : ∀ z ∈ Finset.univ, 0 ≤ (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) := by
      intro z _
      by_cases hz : ν z = 0
      · simp [hz]
      · apply mul_nonneg ENNReal.toReal_nonneg
        have : (tg w v z : ℝ) ≤ cnt w v z := by exact_mod_cast hcon z hz
        linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnp).1 h0 z₀ (Finset.mem_univ _)
    have hlt : tg w v z₀ < cnt w v z₀ := lt_of_le_of_ne (hcon z₀ hz₀) (Ne.symm hne)
    have h2 : (tg w v z₀ : ℝ) < cnt w v z₀ := by exact_mod_cast hlt
    have := mul_pos (toReal_pos hz₀) (by linarith : 0 < (cnt w v z₀ : ℝ) - tg w v z₀)
    linarith

lemma PE_pos {ν : PMF (St w)} {v : WClass w} (hE : ∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z) :
    0 < PE w ν v := by
  obtain ⟨z, hz, h⟩ := hE
  have := Finset.single_le_sum
    (f := fun z => if tg w v z < cnt w v z then (ν z).toReal else 0)
    (fun z _ => by beta_reduce; split_ifs <;> simp) (Finset.mem_univ z)
  simp only [h, ↓reduceIte] at this
  exact lt_of_lt_of_le (toReal_pos hz) this

lemma hB_of {μ : PMF (Finset Page × Prof w)} {y' : Page → ℝ} {ν : PMF (St w)}
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hfst : ν.map Prod.fst = μ) :
    ∀ z, ν z ≠ 0 → ∀ u : WClass w, classMass w y' u - 1 < (tg w u z : ℝ) ∧
      (tg w u z : ℝ) < classMass w y' u + 1 := by
  intro z hz u
  have : z.1 ∈ μ.support := by
    rw [← hfst]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨z, (PMF.mem_support_iff _ _).2 hz, rfl⟩
  exact hbound z.1 this u

lemma round_inv (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {μ : PMF (Finset Page × Prof w)}
    {y' : Page → ℝ} {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) (h : Inv w μ y' ν) : Inv w μ y' (round w ν v) := by
  refine ⟨by rw [round_map_fst, h.1], fun i => by rw [round_marg hM, h.2.1 i], fun z' hz' => ?_⟩
  obtain ⟨z, hz, hF, h1, -⟩ := succ_facts hw K hB hM hz'
  rw [h1]
  exact hF.trans (h.2.2 z hz)

theorem main (hw : ∀ i, 0 ≤ w i) (μ : PMF (Finset Page × Prof w)) (y' : Page → ℝ)
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v) :
    ∀ (n : ℕ) (ν : PMF (St w)), Φ w ν = n → Inv w μ y' ν →
      ∃ ν', Inv w μ y' ν' ∧ ∀ z, ν' z ≠ 0 → ∀ u, cnt w u z = tg w u z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hn hI
  by_cases hdone : ∀ z, ν z ≠ 0 → ∀ u, cnt w u z = tg w u z
  · exact ⟨ν, hI, hdone⟩
  push Not at hdone
  obtain ⟨z₀, hz₀, v, hne⟩ := hdone
  have hB := hB_of hbound hI.1
  obtain ⟨hE, hH⟩ := signs hz₀ hne (mean_zero hI.1 hI.2.1 hmean v)
  have hM : 0 < MM w ν v := lt_of_lt_of_le (PE_pos hE) (le_max_left _ _)
  exact ih _ (hn ▸ Φ_lt hw _ hB hM hE hH) _ rfl (round_inv hw _ hB hM hI)

end Main

end Transfer

open Transfer in
/-- If the target profiles are `⌊K'_v⌋` or `⌈K'_v⌉` with mean `K'_v` (the class mass of the
marginals `y'`), pages can be moved from caches with an excess in a class to caches with a hole
in it until every cache has its target profile; marginals are preserved, and the fetched pages
are exactly the missing ones. -/
theorem transfer {Page : Type*} [Fintype Page] [DecidableEq Page]
    (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) (y' : Page → ℝ)
    (μ : PMF (Finset Page × Prof w)) (hmarg : ∀ i, margX μ i = y' i)
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v) :
    ∃ κ : Finset Page × Prof w → PMF (Finset Page),
      (∀ x ∈ μ.support, ∀ C' ∈ (κ x).support, profile w C' = x.2) ∧
      (∀ i, ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * (if i ∈ C' then 1 else 0) = y' i) ∧
      ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ x, (μ x).toReal *
          ∑ v : WClass w, (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) := by
  classical
  let ν₀ : PMF (St w) := μ.map (fun x => (x, x.1))
  have hI0 : Inv w μ y' ν₀ := by
    refine ⟨?_, fun i => ?_, fun z hz => ?_⟩
    · show (μ.map _).map Prod.fst = μ
      rw [PMF.map_comp]
      exact PMF.map_id μ
    · show ex (μ.map _) _ = _
      rw [ex_map, ← hmarg i]
      rfl
    · obtain ⟨x, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hz)
      apply le_of_eq
      simp [F, G, cnt, tg, profile]
  obtain ⟨ν', ⟨hfst, hm, hF⟩, hfin⟩ := main hw μ y' hbound hmean _ ν₀ rfl hI0
  have hsum := ex_cond ν' μ hfst
  refine ⟨condSnd ν', ?_, ?_, ?_⟩
  · intro x hx C' hC'
    have hne : ν' (x, C') ≠ 0 := condSnd_ne_zero (by rw [hfst]; exact (PMF.mem_support_iff _ _).1 hx)
      ((PMF.mem_support_iff _ _).1 hC')
    funext u
    exact Fin.ext (hfin _ hne u)
  · intro i
    exact (hsum (fun z => ind z.2 i)).trans (hm i)
  · calc _ = ex ν' (fun z => ∑ i ∈ z.2 \ z.1.1, w i) := hsum _
      _ ≤ ex ν' (fun z => G w z.1) := by
        unfold ex
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : ν' z = 0
        · simp [hz]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        refine le_trans ?_ (hF z hz)
        unfold F
        apply le_add_of_nonneg_right
        exact Finset.sum_nonneg fun u _ => mul_nonneg (class_nonneg w hw u) (le_max_left _ _)
      _ = ex μ (G w) := by rw [← hfst, ex_map]; rfl
      _ = _ := rfl

end PagingWithDelay.BBN
