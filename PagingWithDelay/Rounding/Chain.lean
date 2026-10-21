import PagingWithDelay.BBN

/-!
# `cor:rounding`: online rounding of a sequence of fractional caches

From `thm:bbn` (`bansalBuchbinderNaor`): fractional caches `y⁽⁰⁾, …, y⁽ᴺ⁾ ∈ 𝒫` given online, with `y⁽⁰⁾` the indicator vector of the initial cache `C₀`, can be rounded online to random caches `C⁽⁰⁾, …, C⁽ᴺ⁾` of `k` pages with `Pr[i ∈ C⁽ᵛ⁾] = y⁽ᵛ⁾ᵢ`, `C⁽⁰⁾ = C₀`, and expected fetch cost `E[∑_{i ∈ C⁽ᵛ⁺¹⁾ \ C⁽ᵛ⁾} wᵢ] ≤ 5 ∑ᵢ wᵢ |y⁽ᵛ⁺¹⁾ᵢ - y⁽ᵛ⁾ᵢ|`.

`round ys` is the joint distribution of the caches for `ys`. It is online: the first `m` caches depend only on the first `m` fractional caches.
-/

namespace PagingWithDelay

namespace Rounding

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The distribution of the cache `C⁽ᵛ⁾`. -/
noncomputable def cacheLaw (μ : PMF (List (Finset Page))) (ν : ℕ) : PMF (Finset Page) :=
  μ.map fun Cs => Cs.getD ν ∅

/-- The joint distribution of the caches `(C⁽ᵛ⁾, C⁽ᵛ⁺¹⁾)`. -/
noncomputable def stepLaw (μ : PMF (List (Finset Page))) (ν : ℕ) :
    PMF (Finset Page × Finset Page) :=
  μ.map fun Cs => (Cs.getD ν ∅, Cs.getD (ν + 1) ∅)

/-! ### Conditional distributions of a coupling -/

section Cond

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
/-- The first marginal of `π` at `a` is the sum of the row `a`. -/
lemma map_fst_apply (π : PMF (α × β)) (a : α) : π.map Prod.fst a = ∑ b, π (a, b) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The conditional distribution of the second coordinate of `π` given first coordinate `a` (the second marginal if `a` has probability `0`). -/
noncomputable def condSnd (π : PMF (α × β)) (a : α) : PMF β :=
  if h : π.map Prod.fst a = 0 then π.map Prod.snd else
    PMF.ofFintype (fun b => π (a, b) / π.map Prod.fst a) (by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← map_fst_apply]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _))

/-- Drawing `a` from the first marginal of `π` and then the second coordinate from `condSnd π a` gives back `π`. -/
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

/-- An experiment on `π` can draw the first coordinate first and then the second from the conditional distribution. -/
lemma bind_eq_bind_condSnd {γ : Type*} (π : PMF (α × β)) (f : α × β → PMF γ) :
    π.bind f = (π.map Prod.fst).bind fun a => (condSnd π a).bind fun b => f (a, b) := by
  calc π.bind f = ((π.map Prod.fst).bind fun a => (condSnd π a).map (Prod.mk a)).bind f := by
        rw [bind_condSnd]
    _ = _ := by
        rw [PMF.bind_bind]
        congr 1
        funext a
        rw [PMF.bind_map]
        rfl

end Cond

omit [Fintype Page] [DecidableEq Page] in
/-- The image of a distribution under a constant map. -/
lemma map_eq_pure {β γ : Type*} {p : PMF β} {f : β → γ} {c : γ} (h : ∀ b, f b = c) :
    p.map f = PMF.pure c := by
  rw [show f = Function.const β c from funext h]
  exact PMF.map_const _ _

/-! ### The chain of caches

`cpl Q y y'` is the transition (coupling) from the distribution `Q` of the current cache, with fractional cache `y`, to the next fractional cache `y'`; its second marginal is the distribution of the next cache. The caches are drawn one after the other, each from the conditional distribution of the transition given the current cache. -/

section Chain

variable {Y : Type*} (cpl : PMF (Finset Page) → Y → Y → PMF (Finset Page × Finset Page))

/-- The joint distribution of the caches after the current cache `C` (with distribution `Q` and fractional cache `y`), for the further fractional caches `ys`. -/
noncomputable def rest : PMF (Finset Page) → Y → Finset Page → List Y → PMF (List (Finset Page))
  | _, _, _, [] => PMF.pure []
  | Q, y, C, y' :: ys => (condSnd (cpl Q y y') C).bind fun C' =>
      (rest ((cpl Q y y').map Prod.snd) y' C' ys).map (C' :: ·)

/-- The joint distribution of the caches for the fractional caches `y :: ys`, when the first cache has distribution `Q`. -/
noncomputable def joint (Q : PMF (Finset Page)) (y : Y) (ys : List Y) :
    PMF (List (Finset Page)) :=
  Q.bind fun C => (rest cpl Q y C ys).map (C :: ·)

/-- The rounding: the joint distribution of the caches, starting in `C₀`. -/
noncomputable def chainRound (C₀ : Finset Page) : List Y → PMF (List (Finset Page))
  | [] => PMF.pure []
  | y :: ys => joint cpl (PMF.pure C₀) y ys

omit [DecidableEq Page] in
/-- `rest` is online. -/
lemma rest_take (Q : PMF (Finset Page)) (y : Y) (C : Finset Page) (ys : List Y) (m : ℕ) :
    (rest cpl Q y C ys).map (List.take m) = rest cpl Q y C (ys.take m) := by
  induction ys generalizing Q y C m with
  | nil => simp [rest, PMF.pure_map]
  | cons y' ys ih =>
    cases m with
    | zero => exact (map_eq_pure fun _ => rfl).trans (by simp [rest])
    | succ m =>
      simp only [rest, List.take_succ_cons, PMF.map_bind, PMF.map_comp]
      congr 1
      funext C'
      rw [← ih, PMF.map_comp]
      rfl

omit [DecidableEq Page] in
/-- The rounding is online. -/
lemma chainRound_take (C₀ : Finset Page) (ys : List Y) (m : ℕ) :
    (chainRound cpl C₀ ys).map (List.take m) = chainRound cpl C₀ (ys.take m) := by
  cases ys with
  | nil => simp [chainRound, PMF.pure_map]
  | cons y ys =>
    cases m with
    | zero => exact (map_eq_pure fun _ => rfl).trans (by simp [chainRound])
    | succ m =>
      simp only [chainRound, joint, List.take_succ_cons, PMF.map_bind, PMF.map_comp]
      congr 1
      funext C
      rw [← rest_take, PMF.map_comp]
      rfl

omit [DecidableEq Page] in
/-- The caches after the current one: one for each further fractional cache. -/
lemma length_of_mem_rest (Q : PMF (Finset Page)) (y : Y) (C : Finset Page) (ys : List Y) :
    ∀ Cs ∈ (rest cpl Q y C ys).support, Cs.length = ys.length := by
  induction ys generalizing Q y C with
  | nil => simp [rest]
  | cons y' ys ih =>
    intro Cs hCs
    simp only [rest, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hCs
    obtain ⟨C', -, Cs', hCs', rfl⟩ := hCs
    simp [ih _ _ _ Cs' hCs']

/-- One step of the chain: if the transition `π = cpl Q y y'` has first marginal `Q`, the first two caches have joint distribution `π`. -/
lemma joint_cons {Q : PMF (Finset Page)} {y y' : Y} (ys : List Y)
    (h : (cpl Q y y').map Prod.fst = Q) :
    joint cpl Q y (y' :: ys) = (cpl Q y y').bind fun CC =>
      (rest cpl ((cpl Q y y').map Prod.snd) y' CC.2 ys).map (fun Cs => CC.1 :: CC.2 :: Cs) := by
  rw [bind_eq_bind_condSnd, h]
  simp only [joint, rest, PMF.map_bind, PMF.map_comp]
  rfl

omit [DecidableEq Page] in
/-- The distribution of the first cache. -/
lemma cacheLaw_joint_zero (Q : PMF (Finset Page)) (y : Y) (ys : List Y) :
    cacheLaw (joint cpl Q y ys) 0 = Q := by
  simp only [cacheLaw, joint, PMF.map_bind, PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure Q]
  congr 1
  funext C
  exact map_eq_pure fun _ => rfl

/-- The joint distribution of the first two caches is the transition. -/
lemma stepLaw_joint_zero {Q : PMF (Finset Page)} {y y' : Y} (ys : List Y)
    (h : (cpl Q y y').map Prod.fst = Q) :
    stepLaw (joint cpl Q y (y' :: ys)) 0 = cpl Q y y' := by
  rw [joint_cons cpl ys h]
  simp only [stepLaw, PMF.map_bind, PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure (cpl Q y y')]
  congr 1
  funext CC
  exact map_eq_pure fun _ => rfl

/-- Dropping the first cache gives the chain started in the next distribution. -/
lemma joint_tail {Q : PMF (Finset Page)} {y y' : Y} (ys : List Y)
    (h : (cpl Q y y').map Prod.fst = Q) :
    (joint cpl Q y (y' :: ys)).map List.tail =
      joint cpl ((cpl Q y y').map Prod.snd) y' ys := by
  rw [joint_cons cpl ys h, PMF.map_bind]
  simp only [joint, PMF.bind_map, PMF.map_comp]
  rfl

end Chain

omit [Fintype Page] [DecidableEq Page] in
/-- The cache `C⁽ᵛ⁺¹⁾` is the cache `C⁽ᵛ⁾` after dropping the first cache. -/
lemma cacheLaw_succ (μ : PMF (List (Finset Page))) (ν : ℕ) :
    cacheLaw μ (ν + 1) = cacheLaw (μ.map List.tail) ν := by
  simp only [cacheLaw, PMF.map_comp]
  congr 1
  funext Cs
  cases Cs <;> simp

omit [Fintype Page] [DecidableEq Page] in
/-- The same for the pair `(C⁽ᵛ⁺¹⁾, C⁽ᵛ⁺²⁾)`. -/
lemma stepLaw_succ (μ : PMF (List (Finset Page))) (ν : ℕ) :
    stepLaw μ (ν + 1) = stepLaw (μ.map List.tail) ν := by
  simp only [stepLaw, PMF.map_comp]
  congr 1
  funext Cs
  cases Cs <;> simp

/-! ### The laws of the chain -/

/-- The marginals of the distribution concentrated on `C` are the indicator vector of `C`. -/
lemma marginal_pure (C : Finset Page) :
    BBN.marginal (PMF.pure C) = fun i => if i ∈ C then 1 else 0 := by
  funext i
  rw [BBN.marginal, Finset.sum_eq_single C (fun C' _ hC' => by simp [PMF.pure_apply, hC'])
    (by simp)]
  simp

/-- The expected fetch cost of a transition is at most twice its cost. -/
lemma fetchCost_le (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) (π : PMF (Finset Page × Finset Page)) :
    ∑ CC : Finset Page × Finset Page, (π CC).toReal * ∑ i ∈ CC.2 \ CC.1, w i ≤
      2 * BBN.transitionCost w π := by
  rw [BBN.transitionCost, Finset.mul_sum]
  refine Finset.sum_le_sum fun CC _ => ?_
  have ha : 0 ≤ (π CC).toReal := ENNReal.toReal_nonneg
  have hs : 0 ≤ ∑ i ∈ CC.1 \ CC.2, w i / 2 := Finset.sum_nonneg fun i _ => by linarith [hw i]
  rw [← Finset.sum_div]
  nlinarith [mul_nonneg ha hs]

omit [DecidableEq Page] in
/-- `2 cost_f(y, y') = ∑ᵢ wᵢ |y'ᵢ - yᵢ|`. -/
lemma two_mul_fracCost (w y y' : Page → ℝ) :
    2 * BBN.fracCost w y y' = ∑ i, w i * |y' i - y i| := by
  rw [BBN.fracCost, Finset.mul_sum]
  congr 1
  funext i
  rw [abs_sub_comm]
  ring

/-- Along valid fractional caches, every cache distribution of the chain lies in `D` with the given marginals and every transition costs at most `5` times the fractional cost, provided the transitions `cpl` do so (`thm:bbn`). -/
lemma joint_spec (w : Page → ℝ) (k : ℕ) (D : Set (PMF (Finset Page)))
    (cpl : PMF (Finset Page) → (Page → ℝ) → (Page → ℝ) → PMF (Finset Page × Finset Page))
    (hcpl : ∀ Q ∈ D, ∀ y ∈ BBN.fracCaches k, ∀ y' ∈ BBN.fracCaches k, BBN.marginal Q = y →
      (cpl Q y y').map Prod.fst = Q ∧ (cpl Q y y').map Prod.snd ∈ D ∧
        BBN.marginal ((cpl Q y y').map Prod.snd) = y' ∧
        BBN.transitionCost w (cpl Q y y') ≤ 5 * BBN.fracCost w y y')
    (ys : List (Page → ℝ)) :
    ∀ Q ∈ D, ∀ y ∈ BBN.fracCaches k, BBN.marginal Q = y → (∀ y' ∈ ys, y' ∈ BBN.fracCaches k) →
      (∀ ν (hν : ν < (y :: ys).length),
        cacheLaw (joint cpl Q y ys) ν ∈ D ∧
          BBN.marginal (cacheLaw (joint cpl Q y ys) ν) = (y :: ys)[ν]) ∧
      (∀ ν (hν : ν + 1 < (y :: ys).length),
        BBN.transitionCost w (stepLaw (joint cpl Q y ys) ν) ≤
          5 * BBN.fracCost w (y :: ys)[ν] (y :: ys)[ν + 1]) := by
  induction ys with
  | nil =>
    intro Q hQ y hy hm _
    refine ⟨fun ν hν => ?_, fun ν hν => by simp at hν⟩
    obtain rfl : ν = 0 := by simpa using hν
    rw [cacheLaw_joint_zero]
    exact ⟨hQ, hm⟩
  | cons y' ys ih =>
    intro Q hQ y hy hm hys
    obtain ⟨h1, h2, h3, h4⟩ := hcpl Q hQ y hy y' (hys y' List.mem_cons_self) hm
    have ih' := ih _ h2 y' (hys y' List.mem_cons_self) h3
      fun z hz => hys z (List.mem_cons_of_mem _ hz)
    have ht := joint_tail cpl ys h1
    refine ⟨fun ν hν => ?_, fun ν hν => ?_⟩
    · cases ν with
      | zero =>
        rw [cacheLaw_joint_zero]
        exact ⟨hQ, hm⟩
      | succ ν =>
        rw [cacheLaw_succ, ht]
        exact ih'.1 ν (by simpa using hν)
    · cases ν with
      | zero =>
        rw [stepLaw_joint_zero cpl ys h1]
        simpa using h4
      | succ ν =>
        rw [stepLaw_succ, ht]
        exact ih'.2 ν (by simpa using hν)

/-- **`cor:rounding`**. -/
theorem onlineRounding (w : Page → ℝ) (hw_pos : ∀ i, 0 < w i)
    (hw : ∀ i j, w i < w j → 2 * w i ≤ w j) (k : ℕ) (C₀ : Finset Page) (hC₀ : C₀.card = k) :
    ∃ round : List (Page → ℝ) → PMF (List (Finset Page)),
      (∀ ys m, (round ys).map (List.take m) = round (ys.take m)) ∧
      ∀ ys : List (Page → ℝ), (∀ y ∈ ys, y ∈ BBN.fracCaches k) →
        (∀ y ∈ ys.head?, y = fun i => if i ∈ C₀ then 1 else 0) →
        (∀ Cs ∈ (round ys).support,
          Cs.length = ys.length ∧ (∀ C ∈ Cs, C.card = k) ∧ (∀ C ∈ Cs.head?, C = C₀)) ∧
        (∀ ν (hν : ν < ys.length), BBN.marginal (cacheLaw (round ys) ν) = ys[ν]) ∧
        (∀ ν (hν : ν + 1 < ys.length),
          ∑ CC : Finset Page × Finset Page,
              (stepLaw (round ys) ν CC).toReal * ∑ i ∈ CC.2 \ CC.1, w i ≤
            5 * ∑ i, w i * |ys[ν + 1] i - ys[ν] i|) := by
  classical
  obtain ⟨D, T, hD, hpure, hT⟩ := bansalBuchbinderNaor Page w k hw_pos hw
  -- the transition of `thm:bbn` where its hypotheses hold, anything elsewhere
  let cpl : PMF (Finset Page) → (Page → ℝ) → (Page → ℝ) → PMF (Finset Page × Finset Page) :=
    fun Q y y' =>
      if h : Q ∈ D ∧ y ∈ BBN.fracCaches k ∧ y' ∈ BBN.fracCaches k ∧ BBN.marginal Q = y then
        (hT Q h.1 y h.2.1 y' h.2.2.1 h.2.2.2).2.2.choose
      else PMF.pure (∅, ∅)
  have hcpl : ∀ Q ∈ D, ∀ y ∈ BBN.fracCaches k, ∀ y' ∈ BBN.fracCaches k, BBN.marginal Q = y →
      (cpl Q y y').map Prod.fst = Q ∧ (cpl Q y y').map Prod.snd ∈ D ∧
        BBN.marginal ((cpl Q y y').map Prod.snd) = y' ∧
        BBN.transitionCost w (cpl Q y y') ≤ 5 * BBN.fracCost w y y' := by
    intro Q hQ y hy y' hy' hm
    have h : Q ∈ D ∧ y ∈ BBN.fracCaches k ∧ y' ∈ BBN.fracCaches k ∧ BBN.marginal Q = y :=
      ⟨hQ, hy, hy', hm⟩
    obtain ⟨hTD, hTm, -⟩ := hT Q hQ y hy y' hy' hm
    obtain ⟨e1, e2, e3⟩ := (hT Q h.1 y h.2.1 y' h.2.2.1 h.2.2.2).2.2.choose_spec
    simp only [cpl, dif_pos h]
    exact ⟨e1, by rw [e2]; exact hTD, by rw [e2]; exact hTm, e3⟩
  refine ⟨chainRound cpl C₀, chainRound_take cpl C₀, ?_⟩
  intro ys hys hhead
  cases ys with
  | nil => simp [chainRound]
  | cons y ys =>
    have hm : BBN.marginal (PMF.pure C₀) = y := by
      rw [marginal_pure, hhead y rfl]
    obtain ⟨hA, hB⟩ := joint_spec w k D cpl hcpl ys (PMF.pure C₀) (hpure C₀ hC₀) y
      (hys y List.mem_cons_self) hm fun z hz => hys z (List.mem_cons_of_mem _ hz)
    refine ⟨fun Cs hCs => ?_, fun ν hν => (hA ν hν).2, fun ν hν => ?_⟩
    · have hCs' := hCs
      simp only [chainRound, joint, PMF.pure_bind, PMF.mem_support_map_iff] at hCs'
      obtain ⟨Cs', hCs', rfl⟩ := hCs'
      refine ⟨by simp [length_of_mem_rest cpl _ _ _ _ Cs' hCs'], fun C hC => ?_, by simp⟩
      obtain ⟨ν, hν, rfl⟩ := List.mem_iff_getElem.mp hC
      have hlen : ν < (y :: ys).length := by
        simpa [length_of_mem_rest cpl _ _ _ _ Cs' hCs'] using hν
      refine hD _ (hA ν hlen).1 _ ?_
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hCs, by simp [List.getElem?_eq_getElem hν]⟩
    · calc _ ≤ 2 * BBN.transitionCost w (stepLaw (chainRound cpl C₀ (y :: ys)) ν) :=
            fetchCost_le w (fun i => (hw_pos i).le) _
        _ ≤ 2 * (5 * BBN.fracCost w (y :: ys)[ν] (y :: ys)[ν + 1]) := by
            gcongr
            exact hB ν hν
        _ = _ := by rw [mul_left_comm, two_mul_fracCost]

end Rounding

end PagingWithDelay
