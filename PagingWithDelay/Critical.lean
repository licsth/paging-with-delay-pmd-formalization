import PagingWithDelay.Basic
import PagingWithDelay.Critical.Divergence

/-!
# One critical service, deposits and overshoots

Pure facts (no run, no log) about the critical service for a valid instance `input`, and about the deposits and overshoots of `PMD`.

* `serviceEnd_le_add_serviceEnd` (`lem:drop`): after a critical service on `p ≠ q`, the critical service on `q` is shorter by at most `|λ_p(x)|`; `serviceEnd_le_chainLen_add` iterates it along a chain of critical services.
* `serviceEnd_le_three_mul_criticalEV` (`lem:clock`): `|λ| ≤ 3 EV(λ)`.
* `serviceEnd_le_of_light`: if the pages of level `≤ e` hold cached mass at least `1 - δ`, every critical service has length at most `L 2^e`.
* `levelLen` facts: `0 ≤ |λ|_W ≤ L W`, telescoping, `∑_W |λ|_W ≤ |λ|`.
* Overshoots: `o_q ≥ 0` and `delay_q ≤ c_q + w_q + o_q`.

`serviceEnd` and `criticalState` apply to arbitrary `x`; from a rest state with `x_p ≤ δ` the critical service is trivial (length `0`, state unchanged: `serviceEnd_eq_zero_of_le`, `criticalState_eq_of_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  mdPath evictCurve restMass IsRest IsFrac criticalEV evMass evDeriv NotEvicted levelWeight_pos
  levelWeight_succ sum_Icc_telescope' dvMin_sub_min_le)

/-! ### Basic facts about one critical service -/

section Deadline

variable {input : Instance Page}

/-- `|λ_p(x)| ≥ 0`, for every `x`. -/
theorem C.serviceEnd_nonneg' (x : Page → ℝ) (p : Page) : 0 ≤ serviceEnd input x p :=
  Real.sInf_nonneg fun _ hs => hs.1

/-- The critical service on `p` ends no later than any `s ≥ 0` with `x_p(s) ≤ δ`. -/
theorem serviceEnd_le_of_mem {x : Page → ℝ} {p : Page} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : mdPath input x p s p ≤ δ) : serviceEnd input x p ≤ s :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨hs0, hs⟩

theorem mdPath_zero_self' {x : Page → ℝ} (hx : IsRest input x) (p : Page) :
    mdPath input x p 0 p = x p := by
  rw [PagingWithDelay.PMD.mdPath_self, ← hx.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  rw [Finset.sum_congr rfl fun j _ =>
    PagingWithDelay.PMD.evictCurve_zero (input := input) j (hx.1 j).2]
  ring

theorem mdPath_zero' {x : Page → ℝ} (hx : IsRest input x) (p : Page) : mdPath input x p 0 = x := by
  funext i
  by_cases hi : i = p
  · subst hi; exact mdPath_zero_self' hx i
  · rw [PagingWithDelay.PMD.mdPath_of_ne _ _ _ hi,
      PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2]

/-- A critical service on a page with `x_p ≤ δ` has length `0`. -/
theorem serviceEnd_eq_zero_of_le {x : Page → ℝ} (hx : IsRest input x) {p : Page}
    (hp : x p ≤ δ) : serviceEnd input x p = 0 :=
  le_antisymm (serviceEnd_le_of_mem le_rfl (by rw [mdPath_zero_self' hx]; exact hp))
    (C.serviceEnd_nonneg' x p)

/-- A critical service on a page with `x_p ≤ δ` does not change the state. -/
theorem criticalState_eq_of_le {x : Page → ℝ} (hx : IsRest input x) {p : Page}
    (hp : x p ≤ δ) : criticalState input x p = x := by
  unfold criticalState
  rw [serviceEnd_eq_zero_of_le hx hp, mdPath_zero' hx]

section Valid

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
include hv hx

/-- A critical service from a rest state ends in a rest state (also when `x_p ≤ δ`). -/
theorem criticalState_isRest' (p : Page) : IsRest input (criticalState input x p) := by
  by_cases hp : δ < x p
  · exact PagingWithDelay.PMD.criticalState_isRest hv hx hp
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]; exact hx

/-- The other pages do not decrease (also when `x_p ≤ δ`). -/
theorem le_criticalState' {p q : Page} (hqp : q ≠ p) : x q ≤ criticalState input x p q := by
  by_cases hp : δ < x p
  · exact PagingWithDelay.PMD.le_criticalState hv hx hp hqp
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]

theorem delta_lt_criticalState {p q : Page} (hqp : q ≠ p) (hq : δ < x q) :
    δ < criticalState input x p q :=
  hq.trans_le (le_criticalState' hv hx hqp)

/-- The critical service on `p` does not increase `x_p` (it ends at `δ`, or does nothing when `x_p ≤ δ`). -/
theorem criticalState_self_le (p : Page) : criticalState input x p p ≤ x p := by
  by_cases hp : δ < x p
  · rw [PagingWithDelay.PMD.criticalState_self hv hx hp]; exact hp.le
  · rw [criticalState_eq_of_le hx (not_lt.mp hp)]

end Valid

/-- Continuing an eviction curve: if `y_i` is the eviction curve of `i` from `x` at time `a`, then the eviction curve of `i` from `y` at time `s ≥ 0` is the one from `x` at time `a + s` (once at `1`, it stays there). -/
theorem evictCurve_continue {x y : Page → ℝ} {i : Page} {a s : ℝ}
    (hy : y i = evictCurve input x i a) (hs : 0 ≤ s) :
    evictCurve input y i s = evictCurve input x i (a + s) := by
  have he : 1 ≤ Real.exp (s / w i) :=
    Real.one_le_exp (div_nonneg hs (input.weight_pos i).le)
  unfold evictCurve at hy ⊢
  rw [hy, add_div, Real.exp_add, ← mul_assoc]
  rcases le_total 1 (x i * Real.exp (a / w i)) with h | h
  · rw [min_eq_left h, one_mul, min_eq_left he,
      min_eq_left (one_le_mul_of_one_le_of_one_le h he)]
  · rw [min_eq_right h]

/-- The eviction curve is monotone in the start value and in time. -/
theorem evictCurve_le_of_le {x y : Page → ℝ} {i : Page} {s t : ℝ} (hyx : y i ≤ x i)
    (hx0 : 0 ≤ x i) (hst : s ≤ t) : evictCurve input y i s ≤ evictCurve input x i t := by
  unfold evictCurve
  apply min_le_min_left
  calc y i * Real.exp (s / w i) ≤ x i * Real.exp (s / w i) :=
        mul_le_mul_of_nonneg_right hyx (Real.exp_pos _).le
    _ ≤ x i * Real.exp (t / w i) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hst (input.weight_pos i).le)) hx0

/-! ### `lem:drop` -/

section Drop

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
include hv hx

/-- **`lem:drop`**: after the critical service on `p ≠ q` from the rest state `x`, the critical service on `q` is shorter by at most the length of the one on `p`: `|λ_q(x)| ≤ |λ_p(x)| + |λ_q(x̃)|`. No assumption on `x_p` is needed (for `x_p ≤ δ` the service on `p` is trivial).

As in the paper, let `λ = λ_{x→q}`, `λ̃ = λ_{x̃→q}` and `a = |λ_{x→p}|`. For pages `i ∉ {p, q}`, `λ̃` continues the path of the service on `p`: `λ̃(s)_i = λ(s + a)_i`. For `p`, `λ̃(s)_p ≤ λ(s)_p ≤ λ(s + a)_p` as `x̃_p ≤ x_p`. Summing over `i ≠ q` at `s = |λ̃|` gives `λ(|λ̃| + a)_q ≤ λ̃(|λ̃|)_q = δ`, so `|λ| ≤ |λ̃| + a` (`|λ|` is the first time with `λ_q ≤ δ`). -/
theorem serviceEnd_le_add_serviceEnd {p q : Page} (hpq : p ≠ q) (hq : δ < x q) :
    serviceEnd input x q ≤ serviceEnd input x p + serviceEnd input (criticalState input x p) q := by
  set a := serviceEnd input x p with ha_def
  set s := serviceEnd input (criticalState input x p) q with hs_def
  have ha : 0 ≤ a := C.serviceEnd_nonneg' x p
  have hs : 0 ≤ s := C.serviceEnd_nonneg' _ q
  have hy := criticalState_isRest' hv hx p
  have hyq := delta_lt_criticalState hv hx hpq.symm hq
  -- pages `i ∉ {p, q}`: `λ̃(s)_i = λ(s + a)_i`
  have hcont : ∀ i, i ≠ p →
      evictCurve input (criticalState input x p) i s = evictCurve input x i (a + s) := fun i hip =>
    evictCurve_continue (show criticalState input x p i = evictCurve input x i a from
      PagingWithDelay.PMD.mdPath_of_ne x p a hip) hs
  -- page `p`: `λ̃(s)_p ≤ λ(s)_p ≤ λ(s + a)_p`
  have hp : evictCurve input (criticalState input x p) p s ≤ evictCurve input x p (a + s) := by
    have hx0 : 0 ≤ x p := le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 p).1
    calc evictCurve input (criticalState input x p) p s ≤ evictCurve input x p s :=
          evictCurve_le_of_le (criticalState_self_le hv hx p) hx0 le_rfl
      _ ≤ evictCurve input x p (a + s) := evictCurve_le_of_le le_rfl hx0 (by linarith)
  have hsum : ∑ i ∈ Finset.univ.erase q, evictCurve input (criticalState input x p) i s ≤
      ∑ i ∈ Finset.univ.erase q, evictCurve input x i (a + s) :=
    Finset.sum_le_sum fun i _ => by
      by_cases hip : i = p
      · subst hip; exact hp
      · exact (hcont i hip).le
  -- hence `λ(s + a)_q ≤ λ̃(s)_q = δ`
  apply serviceEnd_le_of_mem (add_nonneg ha hs)
  have h1 := PagingWithDelay.PMD.mdPath_serviceEnd hv hy hyq
  rw [PagingWithDelay.PMD.mdPath_self] at h1 ⊢
  linarith

end Drop

/-! ### Chains of critical services -/

variable (input) in
/-- The state after the critical services on the pages of `ps`, in order, from `x`. -/
noncomputable def chainState (x : Page → ℝ) : List Page → Page → ℝ
  | [] => x
  | p :: ps => chainState (criticalState input x p) ps

variable (input) in
/-- The total length of the critical services on the pages of `ps`, in order, from `x`. -/
noncomputable def chainLen (x : Page → ℝ) : List Page → ℝ
  | [] => 0
  | p :: ps => serviceEnd input x p + chainLen (criticalState input x p) ps

@[simp] theorem chainState_nil (x : Page → ℝ) : chainState input x [] = x := rfl

@[simp] theorem chainState_cons (x : Page → ℝ) (p : Page) (ps : List Page) :
    chainState input x (p :: ps) = chainState input (criticalState input x p) ps := rfl

@[simp] theorem chainLen_nil (x : Page → ℝ) : chainLen input x [] = 0 := rfl

@[simp] theorem chainLen_cons (x : Page → ℝ) (p : Page) (ps : List Page) :
    chainLen input x (p :: ps) = serviceEnd input x p + chainLen input (criticalState input x p) ps := rfl

theorem chainLen_nonneg (x : Page → ℝ) : ∀ ps : List Page, 0 ≤ chainLen input x ps
  | [] => le_rfl
  | p :: ps => add_nonneg (C.serviceEnd_nonneg' x p) (chainLen_nonneg _ ps)

theorem chainState_isRest (hv : input.Valid) :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → IsRest input (chainState input x ps)
  | [], _, hx => hx
  | p :: ps, _, hx => chainState_isRest hv ps (criticalState_isRest' hv hx p)

theorem delta_lt_chainState (hv : input.Valid) {q : Page} :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → q ∉ ps → δ < x q →
      δ < chainState input x ps q
  | [], _, _, _, hq => hq
  | p :: ps, _, hx, hqs, hq => by
    simp only [List.mem_cons, not_or] at hqs
    exact delta_lt_chainState hv ps (criticalState_isRest' hv hx p) hqs.2
      (delta_lt_criticalState hv hx hqs.1 hq)

/-- **`lem:drop`, iterated**: after a chain of critical services on pages other than `q`, the critical service on `q` is shorter by at most the total length of the chain. -/
theorem serviceEnd_le_chainLen_add (hv : input.Valid) {q : Page} :
    ∀ (ps : List Page) {x : Page → ℝ}, IsRest input x → q ∉ ps → δ < x q →
      serviceEnd input x q ≤ chainLen input x ps + serviceEnd input (chainState input x ps) q
  | [], _, _, _, _ => by simp
  | p :: ps, x, hx, hqs, hq => by
    simp only [List.mem_cons, not_or] at hqs
    have h1 := serviceEnd_le_add_serviceEnd hv hx (Ne.symm hqs.1) hq
    have h2 := serviceEnd_le_chainLen_add hv ps (criticalState_isRest' hv hx p) hqs.2
      (delta_lt_criticalState hv hx hqs.1 hq)
    simp only [chainLen_cons, chainState_cons]
    linarith

/-! ### `lem:clock` -/

/-- `k δ = k/(2k+1) ≥ 1/3`. -/
theorem one_third_le_cacheSize_mul_delta (hv : input.Valid) :
    1 / 3 ≤ (k : ℝ) * δ := by
  unfold Instance.delta
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

section Clock

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) {p : Page} (hp : δ < x p)
include hv hx hp

/-- Before the end of the critical service the weighted eviction rate is at least `k δ ≥ 1/3`, as at most `n - k - 1` of the pages `i ≠ p` are fully evicted. -/
theorem one_third_le_evDeriv {u : ℝ} (hu0 : 0 ≤ u) (hu : u < serviceEnd input x p) :
    1 / 3 ≤ evDeriv input x p u := by
  set N := (Finset.univ.erase p).filter (fun i => NotEvicted input x i u) with hN
  set M := (Finset.univ.erase p).filter (fun i => ¬ NotEvicted input x i u) with hM
  have hcard : N.card + M.card = (Finset.univ.erase p).card :=
    Finset.card_filter_add_card_filter_not _
  have hcard2 : (Finset.univ.erase p).card + 1 = Fintype.card Page :=
    Finset.card_erase_add_one (Finset.mem_univ p)
  have hge : ∀ i, x i ≤ evictCurve input x i u := fun i => by
    calc x i = evictCurve input x i 0 := (PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2).symm
      _ ≤ _ := PagingWithDelay.PMD.evictCurve_mono hv i
          (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 i).1) hu0
  -- the evicted pages
  have hMsum : (M.card : ℝ) ≤ ∑ j ∈ Finset.univ.erase p, evictCurve input x j u := by
    have h1 : ∑ j ∈ M, evictCurve input x j u = M.card := by
      rw [Finset.sum_congr rfl fun j hj =>
        PagingWithDelay.PMD.dvEvictCurve_of_evicted (Finset.mem_filter.mp hj).2]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ _
    exact le_trans (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 j).1) (hge j)
  have hlt := PagingWithDelay.PMD.delta_lt_mdPath hv hx hp hu0 hu
  rw [PagingWithDelay.PMD.mdPath_self] at hlt
  unfold restMass at hlt
  have hk : (k : ℝ) < N.card + 1 := by
    have hc : ((N.card : ℕ) : ℝ) + M.card + 1 = Fintype.card Page := by
      exact_mod_cast (show N.card + M.card + 1 = Fintype.card Page by omega)
    linarith [PagingWithDelay.PMD.delta_pos hv]
  have hk' : (k : ℝ) ≤ N.card := by
    have : k < N.card + 1 := by exact_mod_cast hk
    exact_mod_cast (show k ≤ N.card by omega)
  have hD : evDeriv input x p u = ∑ j ∈ N, evictCurve input x j u := by
    unfold evDeriv
    rw [hN, Finset.sum_filter]
  have hDge : (N.card : ℝ) * δ ≤ evDeriv input x p u := by
    rw [hD]
    have : ∑ j ∈ N, δ ≤ ∑ j ∈ N, evictCurve input x j u :=
      Finset.sum_le_sum fun j _ => (hx.1 j).1.trans (hge j)
    simpa using this
  have := one_third_le_cacheSize_mul_delta hv
  nlinarith [PagingWithDelay.PMD.delta_pos hv]

/-- `EV(λ) = G(s^end) - G(0)` for `G(s) = ∑_{i ≠ p} wᵢ xᵢ(s)`. -/
theorem criticalEV_eq_evMass :
    criticalEV input x p = evMass input x p (serviceEnd input x p) - evMass input x p 0 := by
  unfold criticalEV evMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PagingWithDelay.PMD.criticalState_of_ne hv hx hp (Finset.ne_of_mem_erase hi),
    PagingWithDelay.PMD.evictCurve_zero i (hx.1 i).2, mul_sub]

/-- **`lem:clock`**: `|λ| ≤ 3 EV(λ)`. -/
theorem serviceEnd_le_three_mul_criticalEV : serviceEnd input x p ≤ 3 * criticalEV input x p := by
  have hx0 : ∀ i, 0 < x i := fun i => (PagingWithDelay.PMD.delta_pos hv).trans_le (hx.1 i).1
  have h := PagingWithDelay.PMD.sub_le_mul_of_deriv_right_le
    (f := fun s => -evMass input x p s) (f' := fun u => -evDeriv input x p u) (c := -(1 / 3))
    (PagingWithDelay.PMD.serviceEnd_nonneg hv hx hp)
    (PagingWithDelay.PMD.continuous_evMass x p).neg
    (fun u => (PagingWithDelay.PMD.hasDerivWithinAt_evMass hv hx0 p u).neg)
    (fun u hu => neg_le_neg (one_third_le_evDeriv hv hx hp hu.1 hu.2))
  rw [criticalEV_eq_evMass hv hx hp]
  simp only at h
  linarith

end Clock

/-! ### Light mass ⇒ short service -/

/-- If the pages of level `≤ e` hold cached mass `∑_{i : wᵢ ≤ 2^e} (1 - xᵢ) ≥ 1 - δ` (the second half of `preemptCondition`), then every critical service from the rest state `x` has length at most `L 2^e`: by then the pages `i ≠ q` of level `≤ e` are fully evicted, having gained at least `x_q - δ`. -/
theorem serviceEnd_le_of_light (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x) (q : Page)
    {e : ℤ} (hcond : 1 - δ ≤
      ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) :
    serviceEnd input x q ≤ L * levelWeight e := by
  have hL := PagingWithDelay.PMD.L_pos hv
  have hW := levelWeight_pos e
  apply serviceEnd_le_of_mem (by positivity)
  rw [PagingWithDelay.PMD.mdPath_self]
  set f : Page → ℝ := fun j => if level input j ≤ e then 1 - x j else 0 with hf
  have hterm : ∀ j, x j + f j ≤ evictCurve input x j (L * levelWeight e) := by
    intro j
    simp only [hf]
    split_ifs with hj
    · have : evictCurve input x j (L * levelWeight e) = 1 := by
        unfold evictCurve
        apply min_eq_left
        have hwj := hv.weight_pos j
        have hle : w j ≤ levelWeight e :=
          (PagingWithDelay.PMD.level_le_iff hv j e).mp hj
        have hge : L ≤ L * levelWeight e / w j := by
          rw [le_div_iff₀ hwj]
          exact mul_le_mul_of_nonneg_left hle hL.le
        calc (1 : ℝ) = δ * Real.exp L :=
              (PagingWithDelay.PMD.delta_mul_exp_L hv).symm
          _ ≤ x j * Real.exp (L * levelWeight e / w j) := by
            apply mul_le_mul (hx.1 j).1 (Real.exp_le_exp.mpr hge) (Real.exp_pos _).le
            linarith [(hx.1 j).1, PagingWithDelay.PMD.delta_pos hv]
      rw [this]; ring_nf; exact le_rfl
    · rw [add_zero]
      calc x j = evictCurve input x j 0 := (PagingWithDelay.PMD.evictCurve_zero j (hx.1 j).2).symm
        _ ≤ _ := PagingWithDelay.PMD.evictCurve_mono hv j
            (le_trans (PagingWithDelay.PMD.delta_pos hv).le (hx.1 j).1) (by positivity)
  have hsum : ∑ j ∈ Finset.univ.erase q, (x j + f j) ≤
      ∑ j ∈ Finset.univ.erase q, evictCurve input x j (L * levelWeight e) :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [Finset.sum_add_distrib] at hsum
  have hx2 := hx.2
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)] at hx2
  have hf2 : ∑ j, f j = ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i) := by
    simp only [hf]; rw [Finset.sum_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q)] at hf2
  have hfq : f q ≤ 1 - x q := by
    simp only [hf]; split_ifs <;> linarith [(hx.1 q).2]
  linarith

/-- `serviceEnd_le_of_light` under the condition of a level-`e` preemptive service. -/
theorem serviceEnd_le_of_preemptCondition (hv : input.Valid) {x : Page → ℝ} (hx : IsRest input x)
    (q : Page) {budget : ℤ → ℝ} {e : ℤ}
    (h : PagingWithDelay.PMD.preemptCondition input x budget e) :
    serviceEnd input x q ≤ L * levelWeight e :=
  serviceEnd_le_of_light hv hx q h.2

end Deadline

/-! ### Deposits: `levelLen` -/

section LevelLen

variable {input : Instance Page}

/-- `L = ln (2k+1) ≥ 0` (no assumptions needed). -/
theorem L_nonneg' (input : Instance Page) : 0 ≤ L :=
  Real.log_nonneg (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)

/-- `|λ|_W = min (L·2W) |λ| - min (L·W) |λ|`, written with `levelWeight (e+1) = 2W`. -/
theorem levelLen_eq_sub (x : Page → ℝ) (p : Page) (e : ℤ) :
    levelLen input x p e = min (L * levelWeight (e + 1)) (serviceEnd input x p) -
      min (L * levelWeight e) (serviceEnd input x p) := by
  unfold levelLen
  rw [levelWeight_succ, show L * (2 * levelWeight e) = 2 * L * levelWeight e by ring]

theorem C.levelLen_nonneg (x : Page → ℝ) (p : Page) (e : ℤ) : 0 ≤ levelLen input x p e := by
  unfold levelLen
  apply sub_nonneg.mpr
  apply min_le_min_right
  have := L_nonneg' input
  have := levelWeight_pos e
  nlinarith

theorem levelLen_le (x : Page → ℝ) (p : Page) (e : ℤ) :
    levelLen input x p e ≤ L * levelWeight e := by
  unfold levelLen
  have := L_nonneg' input
  have := levelWeight_pos e
  have h := dvMin_sub_min_le (a := 2 * L * levelWeight e) (b := L * levelWeight e)
    (S := serviceEnd input x p) (by nlinarith)
  linarith

/-- Telescoping: `∑_{a ≤ e ≤ b} |λ|_{2^e} = min (L 2^{b+1}) |λ| - min (L 2^a) |λ|`. -/
theorem sum_levelLen_Icc (x : Page → ℝ) (p : Page) {a b : ℤ} (hab : a ≤ b) :
    ∑ e ∈ Finset.Icc a b, levelLen input x p e =
      min (L * levelWeight (b + 1)) (serviceEnd input x p) -
        min (L * levelWeight a) (serviceEnd input x p) := by
  simp_rw [levelLen_eq_sub]
  exact sum_Icc_telescope' (fun e => min (L * levelWeight e) (serviceEnd input x p))
    a b hab

/-- The intervals `I_W` are disjoint: `∑_{a ≤ e ≤ b} |λ|_{2^e} ≤ |λ|`. -/
theorem sum_levelLen_Icc_le (x : Page → ℝ) (p : Page) (a b : ℤ) :
    ∑ e ∈ Finset.Icc a b, levelLen input x p e ≤ serviceEnd input x p := by
  rcases lt_or_ge b a with h | h
  · rw [Finset.Icc_eq_empty (not_le.mpr h), Finset.sum_empty]
    exact C.serviceEnd_nonneg' _ _
  rw [sum_levelLen_Icc x p h]
  have h1 := min_le_right (L * levelWeight (b + 1)) (serviceEnd input x p)
  have h2 : 0 ≤ min (L * levelWeight a) (serviceEnd input x p) :=
    le_min (mul_nonneg (L_nonneg' input) (levelWeight_pos a).le) (C.serviceEnd_nonneg' _ _)
  linarith

/-- The total deposit of a critical service is at most its length. -/
theorem sum_levelLen_le (x : Page → ℝ) (p : Page) :
    ∑ e ∈ Finset.Icc (level input p) (maxLevel input), levelLen input x p e ≤
      serviceEnd input x p :=
  sum_levelLen_Icc_le x p _ _

end LevelLen

/-! ### Overshoots -/

section Overshoots

variable (input : Instance Page) (x : Page → ℝ) (pending : List (Request Page))
  (claims : Page → ℝ) (t : ℝ)

theorem C.overshoot_nonneg (q : Page) : 0 ≤ overshoot input pending claims q t :=
  le_max_left _ _

theorem le_overshoot_add (q : Page) :
    pageDelay pending q t ≤ claims q + w q + overshoot input pending claims q t := by
  unfold overshoot
  have := le_max_right 0 (pageDelay pending q t - claims q - w q)
  linarith

theorem C.mem_lighter {p q : Page} : q ∈ lighter input p ↔ w q ≤ w p := by
  simp [lighter]

theorem C.self_mem_lighter (p : Page) : p ∈ lighter input p := (C.mem_lighter input).mpr le_rfl

end Overshoots

end PMD

end PagingWithDelay
