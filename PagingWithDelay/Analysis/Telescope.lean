import PagingWithDelay.Analysis.Defs

/-!
# Telescoping the Bregman potential (`prop:phaseD`, `lem:optmoves`, `prop:tele`)

* `critical_miss_len` (`prop:phaseD`, miss service, with lengths): the growth of `D(O ‖ x)` in a critical service on `r ∉ O` is at most `2 L w_r` plus `∑ |λ|_W` over the levels `w_r ≤ W < w_min(O)`. The rate of the pages `i ≠ r` is at most `1`, and at most `0` once some page of `O` is evicted (path time `≥ L w_q`).
* `fetchTotal_le` (`prop:tele`): the potential before entry `i` is `D(O ‖ x)` with `O` the comparator's cache at that time and `x` the state outside the current preemptive service (`baseState`). Only critical services change `x`; the comparator's steps in `(entryTime i, entryTime (i+1)]` change `O`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace TeleProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch IsRest IsFrac divergence bregG bregG_nonneg restPart restDeriv
  continuous_restPart hasDerivWithinAt_restPart restDeriv_eq divergence_start divergence_end
  sub_le_mul_of_deriv_right_le delta_lt_mdPath serviceEnd_nonneg serviceEnd_le
  levelWeight_level levelWeight_pos levelWeight_succ le_maxLevel delta_mul_exp_L log_delta
  NotEvicted criticalFetch_lt_weight divergence_change_cache divergence_le divergence_nonneg
  critical_hit)
open PagingWithDelay.Schedule (cacheAt evictedAt fetchedAt SwapForm cacheAt_change)

open Finset

/-! ### `prop:phaseD` for a miss service, with lengths -/

section Phase

open scoped InstanceNotation

variable {input : Instance Page} (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
  {x : Page → ℝ} (hx : IsRest input x) {r : Page} (hr : δ < x r)
  {O : Finset Page} (hO : O.card = k)
include hv h2 hx hr hO

/-- `prop:phaseD`, miss service, with the excess measured by lengths: the growth of `D` is at most `2 L w_r` plus `∑ |λ|_W` over the levels `W` with `w_r ≤ W ≤ w_max` below every weight of `O`. -/
theorem critical_miss_len (hrO : r ∉ O) :
    divergence input O (criticalState input x r) - divergence input O x ≤
      2 * L * w r +
        ∑ e ∈ (Finset.Icc (level input r) (maxLevel input)).filter
            (fun e => ∀ q ∈ O, levelWeight e < w q),
          levelLen input x r e := by
  have hbv := hv
  have hr' : δ < x r := hr
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_lt_of_le (Instance.delta_pos hv) (hx.1 i).1
  have hS0 := serviceEnd_nonneg hbv hx hr'
  have hL : 0 < L := Instance.L_pos hv
  have hd := Instance.delta_pos hv
  have hD0 := divergence_start hx O r
  have hD1 := divergence_end hbv hx hr' O
  set S := serviceEnd input x r with hS
  set A := restPart input O x r with hAdef
  have hAc : Continuous A := continuous_restPart hx0 O r
  have hAd := hasDerivWithinAt_restPart hbv hx0 O r
  set P : ℤ → ℝ := fun e => min (L * levelWeight e) S with hP
  have hP0 : ∀ e, 0 ≤ P e := fun e =>
    le_min (mul_nonneg hL.le (levelWeight_pos e).le) hS0
  have hPS : ∀ e, P e ≤ S := fun e => min_le_right _ _
  have hPmono : ∀ e, P e ≤ P (e + 1) := fun e =>
    min_le_min_right _ (mul_le_mul_of_nonneg_left
      (by rw [levelWeight_succ]; linarith [levelWeight_pos e]) hL.le)
  have hsum_nonneg : ∀ u, 0 ≤ ∑ i ∈ Finset.univ.erase r,
      (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := fun u =>
    Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hle1 : ∀ u, 0 ≤ u → u < S → restDeriv input O x r u ≤ 1 := by
    intro u hu0 huS
    have hxr := delta_lt_mdPath hbv hx hr' hu0 huS
    rw [restDeriv_eq hO, if_neg hrO]
    have : (0 : ℝ) < δ := hd
    linarith [hsum_nonneg u]
  have hle0 : ∀ u, 0 ≤ u → u < S → ∀ q ∈ O, L * w q ≤ u →
      restDeriv input O x r u ≤ 0 := by
    intro u hu0 huS q hq hqu
    have hxr := delta_lt_mdPath hbv hx hr' hu0 huS
    have hqr : q ≠ r := fun h => hrO (h ▸ hq)
    have hwq := hv.weight_pos q
    have hev : ¬ NotEvicted input x q u := by
      unfold NotEvicted
      push_neg
      have h1 : L ≤ u / w q := by rw [le_div_iff₀ hwq]; linarith
      have h2 : Real.exp L ≤ Real.exp (u / w q) := Real.exp_le_exp.mpr h1
      have h3 := delta_mul_exp_L hbv
      have h4 : δ * Real.exp L ≤ x q * Real.exp (u / w q) :=
        mul_le_mul (hx.1 q).1 h2 (Real.exp_pos _).le (hx0 q).le
      simpa using (show 1 ≤ x q * Real.exp (u / w q) by linarith)
    have hone : (1 : ℝ) ≤ ∑ i ∈ Finset.univ.erase r,
        (if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0) := by
      have := Finset.single_le_sum
        (f := fun i => if ¬ NotEvicted input x i u ∧ i ∈ O then (1 : ℝ) else 0)
        (fun i _ => by dsimp only; split_ifs <;> norm_num)
        (Finset.mem_erase.mpr ⟨hqr, Finset.mem_univ q⟩)
      dsimp only at this
      rw [if_pos ⟨hev, hq⟩] at this
      exact this
    rw [restDeriv_eq hO, if_neg hrO]
    have : (0 : ℝ) < δ := hd
    linarith
  -- the initial segment `[0, L w_r)`
  have hwr : w r = levelWeight (level input r) :=
    (levelWeight_level hbv h2 r).symm
  have hinit : A (P (level input r)) - A 0 ≤ L * w r := by
    have := sub_le_mul_of_deriv_right_le (c := 1) (hP0 (level input r)) hAc hAd
      fun u hu => hle1 u hu.1 (lt_of_lt_of_le hu.2 (hPS (level input r)))
    have h' : P (level input r) ≤ L * w r := by
      rw [hwr]; exact min_le_left _ _
    linarith
  -- one band `I_W`
  have hband : ∀ e, A (P (e + 1)) - A (P e) ≤
      if (∀ q ∈ O, levelWeight e < w q) then levelLen input x r e else 0 := by
    intro e
    split_ifs with hc
    · have := sub_le_mul_of_deriv_right_le (c := 1) (hPmono e) hAc hAd
        fun u hu => hle1 u ((hP0 e).trans hu.1) (lt_of_lt_of_le hu.2 (hPS (e + 1)))
      rw [levelLen_eq_sub]
      simp only [hP] at this
      linarith
    · push_neg at hc
      obtain ⟨q, hq, hqe⟩ := hc
      have := sub_le_mul_of_deriv_right_le (c := 0) (hPmono e) hAc hAd fun u hu => by
        have huS : u < S := lt_of_lt_of_le hu.2 (hPS (e + 1))
        have hu0 : 0 ≤ u := (hP0 e).trans hu.1
        refine hle0 u hu0 huS q hq ?_
        have h1 : L * levelWeight e ≤ u := by
          rcases min_le_iff.mp hu.1 with h | h
          · exact h
          · exact absurd h (not_le.mpr huS)
        exact le_trans (mul_le_mul_of_nonneg_left hqe hL.le) h1
      linarith
  -- telescoping over the bands
  have htele : ∀ n, level input r ≤ n → A (P n) - A (P (level input r)) ≤
      ∑ e ∈ Finset.Icc (level input r) (n - 1),
        (if (∀ q ∈ O, levelWeight e < w q) then levelLen input x r e else 0) := by
    intro n hn
    induction n, hn using Int.le_induction with
    | base =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    | succ n hn ih =>
      have hins := Finset.insert_Icc_right_eq_Icc_add_one (a := level input r) (b := n - 1)
        (by omega)
      rw [sub_add_cancel] at hins
      rw [add_sub_cancel_right, ← hins, Finset.sum_insert (by simp)]
      have := hband n
      linarith
  have hM := le_maxLevel (input := input) r
  have hend : P (maxLevel input + 1) = S := by
    apply min_eq_right
    refine (serviceEnd_le hbv hx hr').trans (mul_le_mul_of_nonneg_left ?_ hL.le)
    rw [levelWeight_succ]; linarith [levelWeight_pos (maxLevel input)]
  have ht := htele (maxLevel input + 1) (by omega)
  rw [add_sub_cancel_right, hend] at ht
  rw [Finset.sum_filter]
  -- the page `r`
  have hgd : bregG δ = δ - 1 + L := by
    have := log_delta hbv
    unfold bregG; rw [this]; ring
  have hgx := bregG_nonneg (hx0 r)
  have hwr0 := hv.weight_pos r
  have hb1 : w r * bregG δ ≤ L * w r := by
    rw [hgd, mul_comm L]
    exact mul_le_mul_of_nonneg_left (by linarith [Instance.delta_lt_one hv]) hwr0.le
  have hb2 : 0 ≤ w r * bregG (x r) := mul_nonneg hwr0.le hgx
  rw [hD0, hD1]
  simp only [hrO, ↓reduceIte]
  linarith

end Phase

/-! ### One entry and one window -/

section Run

open scoped InstanceNotation

variable {input : Instance Page} (hv : input.Valid) {σ : Request Page → ℝ}
  (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {S : Schedule Page}
  (hSw : SwapForm input S)
include hv hσ hSw

/-- `prop:phaseD` at one entry: the change of the potential at entry `i`. -/
theorem entry_divergence_le (h2 : input.PowerOfTwoWeights) {i : ℕ}
    (hi : i < (log input).length) :
    divergence input (cacheAt input S (entryTime input i))
        (baseState (snapAt input (i + 1))) -
      divergence input (cacheAt input S (entryTime input i))
        (baseState (snapAt input i)) ≤
      -fetchAt input i + (1 + 2 * L) * missW input S i + excessAt input S i := by
  have hbv := hv
  cases hmv : moveAt i hi with
  | critical p =>
    obtain ⟨hidle, -, hsucc⟩ := critical_spec hv hi hmv
    obtain ⟨-, -, hxr, hr, -⟩ := critical_facts hv hi hmv
    have hx0 : (snapAt input i).x = baseState (snapAt input i) :=
      x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
    have hb1 : baseState (snapAt input (i + 1)) =
        criticalState input (snapAt input i).x p := by
      rw [hsucc]; rfl
    have hr' : δ < (snapAt input i).x p := hr
    have hO := Schedule.card_cacheAt hv hSw (entryTime input i)
    have hpf : fetchAt input i = criticalFetch input (snapAt input i).x p := by
      simp only [fetchAt, dif_pos hi, hmv]
    have hmw : missW input S i =
        if p ∈ cacheAt input S (entryTime input i) then 0
        else w p := by
      simp only [missW, dif_pos hi, hmv]
    rw [hb1, ← hx0, hpf, hmw]
    by_cases hrO : p ∈ cacheAt input S (entryTime input i)
    · have hex : excessAt input S i = 0 := by
        simp only [excessAt, dif_pos hi, hmv, if_pos hrO]
      rw [hex, if_pos hrO]
      have := critical_hit hbv hxr hr' hO hrO
      linarith
    · have hex : excessAt input S i =
          ∑ e ∈ excessLevels input S p (entryTime input i),
            levelLen input (snapAt input i).x p e := by
        simp only [excessAt, dif_pos hi, hmv, if_neg hrO]
      rw [hex, if_neg hrO]
      have := critical_miss_len hv h2 hxr hr hO hrO
      have := criticalFetch_lt_weight hbv hxr hr'
      unfold excessLevels
      have hL : 0 ≤ L := L_nonneg' input
      nlinarith
  | _ =>
    rw [baseState_succ_of_not_critical hv hi (by intro π hπ; rw [hmv] at hπ; cases hπ)]
    simp only [fetchAt, excessAt, missW, dif_pos hi, hmv]
    simp

/-- `lem:optmoves` between two entries: the comparator's steps in `(entryTime i, entryTime (i+1)]` change the potential by at most `L` times the evicted plus the fetched weight. -/
theorem window_divergence_le (i : ℕ) :
    divergence input (cacheAt input S (entryTime input (i + 1)))
          (baseState (snapAt input (i + 1))) -
        divergence input (cacheAt input S (entryTime input i))
          (baseState (snapAt input (i + 1))) ≤
      ∑ j ∈ range S.length,
        if ∃ h : j < S.length, entryTime input i < S[j].time ∧
            S[j].time ≤ entryTime input (i + 1) then
          L * ∑ q ∈ evictedAt input S j, w q +
            1 * ∑ p ∈ fetchedAt input S j, w p
        else 0 := by
  have hbv := hv
  have hx := (baseState_isRest hv (i + 1)).1
  have hF : ∀ (C : Finset Page) (p q : Page), p ∉ C → q ∈ C →
      divergence input (insert p (C.erase q)) (baseState (snapAt input (i + 1))) -
          divergence input C (baseState (snapAt input (i + 1))) ≤
        L * w q + 1 * w p := by
    intro C p q hp hq
    have hd := divergence_change_cache hbv hx C (insert p (C.erase q))
    have h1 : C \ insert p (C.erase q) ⊆ {q} := by
      intro a ha
      simp only [mem_sdiff, mem_insert, mem_erase] at ha
      simp only [mem_singleton]
      by_contra hne
      exact ha.2 (Or.inr ⟨hne, ha.1⟩)
    have h2 : insert p (C.erase q) \ C ⊆ {p} := by
      intro a ha
      simp only [mem_sdiff, mem_insert, mem_erase] at ha
      simp only [mem_singleton]
      rcases ha.1 with h | h
      · exact h
      · exact absurd h.2 ha.2
    have s1 : ∑ a ∈ C \ insert p (C.erase q), w a ≤ w q := by
      have := sum_le_sum_of_subset_of_nonneg h1 (fun a _ _ => (hv.weight_pos a).le)
      simpa using this
    have s2 : ∑ a ∈ insert p (C.erase q) \ C, w a ≤ w p := by
      have := sum_le_sum_of_subset_of_nonneg h2 (fun a _ _ => (hv.weight_pos a).le)
      simpa using this
    have := mul_le_mul_of_nonneg_left s1 (L_nonneg' input)
    linarith
  have hmono : entryTime input i ≤ entryTime input (i + 1) := entryTime_mono hv (by omega)
  have := cacheAt_change hv hSw
    (fun O => divergence input O (baseState (snapAt input (i + 1)))) L 1 hF hmono
  rw [sum_filter] at this
  exact this

/-- `prop:tele` (telescoping), against a comparator in swap form: `∑_λ fetch(λ) ≤ (L+1) fetchCost(S) + L w(C₀) + (L+1) ∑ w + (2L+1) ∑ missW + ∑ Exc`. -/
theorem fetchTotal_le (h2 : input.PowerOfTwoWeights) :
    fetchTotal input ≤
      (L + 1) * S.fetchCost input +
        L * ∑ p ∈ input.initialCache, w p +
        (L + 1) * input.totalWeight +
        (2 * L + 1) * ∑ i ∈ Finset.range (log input).length, missW input S i +
        ∑ i ∈ Finset.range (log input).length, excessAt input S i := by
  have hbv := hv
  have hL := L_nonneg' input
  set N := (log input).length with hN
  set D : ℕ → ℝ := fun i =>
    divergence input (cacheAt input S (entryTime input i))
      (baseState (snapAt input i)) with hD
  set D' : ℕ → ℝ := fun i =>
    divergence input (cacheAt input S (entryTime input i))
      (baseState (snapAt input (i + 1))) with hD'
  set g : ℕ → ℝ := fun j =>
    L * ∑ q ∈ evictedAt input S j, w q +
      1 * ∑ p ∈ fetchedAt input S j, w p with hg
  set W0 := ∑ p ∈ input.initialCache, w p with hW0
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    have h1 : 0 ≤ ∑ q ∈ evictedAt input S j, w q :=
      sum_nonneg fun q _ => (hv.weight_pos q).le
    have h2 : 0 ≤ ∑ q ∈ fetchedAt input S j, w q :=
      sum_nonneg fun q _ => (hv.weight_pos q).le
    simp only [hg]
    positivity
  -- the windows are disjoint
  have hdisj : ∑ i ∈ range N, ∑ j ∈ range S.length,
      (if ∃ h : j < S.length, entryTime input i < S[j].time ∧
          S[j].time ≤ entryTime input (i + 1) then g j else 0) ≤
      ∑ j ∈ range S.length, g j := by
    rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((range N).filter fun i => ∃ h : j < S.length,
        entryTime input i < S[j].time ∧ S[j].time ≤ entryTime input (i + 1)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      simp only [mem_filter] at ha hb
      obtain ⟨-, hj, ha1, ha2⟩ := ha
      obtain ⟨-, hj', hb1, hb2⟩ := hb
      by_contra hab
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · have : entryTime input (a + 1) ≤ entryTime input b := entryTime_mono hv (by omega)
        linarith
      · have : entryTime input (b + 1) ≤ entryTime input a := entryTime_mono hv (by omega)
        linarith
    have : ((((range N).filter fun i => ∃ h : j < S.length,
        entryTime input i < S[j].time ∧ S[j].time ≤ entryTime input (i + 1)).card : ℕ) : ℝ)
        ≤ 1 := by exact_mod_cast hcard
    nlinarith [hg0 j]
  have hgsum : ∑ j ∈ range S.length, g j ≤
      L * (S.fetchCost input + W0) + S.fetchCost input := by
    have hev := Schedule.sum_evicted_le hv hSw
    have hfe := Schedule.fetchCost_eq_sum_fetched hv hSw
    simp only [hg, sum_add_distrib, ← mul_sum, one_mul]
    rw [← hfe]
    have := mul_le_mul_of_nonneg_left hev hL
    linarith
  -- telescoping
  have htel : ∑ i ∈ range N, (D (i + 1) - D i) = D N - D 0 := sum_range_sub D N
  have hsplit : ∑ i ∈ range N, (D (i + 1) - D i) =
      ∑ i ∈ range N, (D' i - D i) + ∑ i ∈ range N, (D (i + 1) - D' i) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  have hphase : ∑ i ∈ range N, (D' i - D i) ≤
      ∑ i ∈ range N, (-fetchAt input i + (1 + 2 * L) * missW input S i +
        excessAt input S i) :=
    sum_le_sum fun i hi => entry_divergence_le hv hσ hSw h2 (mem_range.mp hi)
  have hwin : ∑ i ∈ range N, (D (i + 1) - D' i) ≤ ∑ j ∈ range S.length, g j :=
    le_trans (sum_le_sum fun i _ => window_divergence_le hv hσ hSw i) hdisj
  have hphase' : ∑ i ∈ range N, (-fetchAt input i +
      (1 + 2 * L) * missW input S i + excessAt input S i) =
      -fetchTotal input + (1 + 2 * L) * ∑ i ∈ range N, missW input S i +
        ∑ i ∈ range N, excessAt input S i := by
    rw [sum_add_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum]
    rfl
  have hD0 : D 0 ≤ (L + 1) * input.totalWeight :=
    divergence_le hbv (baseState_isRest hv 0).1 _
  have hDN : 0 ≤ D N := divergence_nonneg hbv (baseState_isRest hv N).1 _
  linarith

end Run

end TeleProof

end PMD

end PagingWithDelay
