import PagingWithDelay.Analysis.AlgDelay.Bridge

/-!
# `prop:algdelay`, part 3: the delay of one visit, and the used delay

Consider a visit `j` of page `p` at time `t`, and let `a = startOf j` be the tick or advance that set `t`. No page has triggered since the previous time, so `snapAt a` is the paper's state "right before the steps of `PMD` at time `t`". Let `ō_p = o_p(t)` be the overshoot of `p` in this state (`overAt j`). The visit pays

  `(x_p - δ) · delay_p(t) ≤ c_p + (x_p - δ) w_p + ō_p` (`visitDelay_le`),

where `c_p` is the claim of `p` right before the visit (`claimAt j`) and `(x_p - δ) w_p` is the fetch cost of the visit (`fetchAt j + tripAt j`).

The claims of all visits sum to at most `∑_λ |λ| / L` (`sum_claimAt_le`), by the potential `∑_q c_q`: a critical service increases it by `|λ|/L` minus the claim of its page, which it resets, and a round trip resets the claim of its page.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

variable (input) in
/-- The claim `c_p` of the page `p` visited by entry `j`, right before the visit (`0` if entry `j` is not a visit). -/
def claimAt (j : ℕ) : ℝ :=
  match visitPage input j with
  | some p => (snapAt input j).claims p
  | none => 0

variable (input) in
/-- The overshoot `ō_p = o_p(t)` of the page `p` visited by entry `j` at its time `t`, in the state at the start index of `t` (right before the steps of `PMD` at `t`); `0` if entry `j` is not a visit. -/
def overAt (j : ℕ) : ℝ :=
  match visitPage input j with
  | some p => overshoot input (snapAt input (startOf input j)).pending
      (snapAt input (startOf input j)).claims p (entryTime input j)
  | none => 0

theorem overAt_nonneg (j : ℕ) : 0 ≤ overAt input j := by
  unfold overAt
  split
  · exact overshoot_nonneg _ _ _ _
  · exact le_rfl

theorem overAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    overAt input j = overshoot input (snapAt input (startOf input j)).pending
      (snapAt input (startOf input j)).claims p (entryTime input j) := by
  simp [overAt, hvis]

theorem overAt_of_none {j : ℕ} (hvis : visitPage input j = none) : overAt input j = 0 := by
  simp [overAt, hvis]

section

variable (hv : input.Valid)
include hv

/-- A tick or an advance does not change the delays at its time: an advance does not change the pending list, and the requests arriving at a tick have delay `d(0) = 0`. -/
theorem pageDelay_succ_of_TA {a : ℕ} (h : a < (log input).length)
    (hmove : (∃ t, moveAt a h = .tick t) ∨ (∃ t, moveAt a h = .advance t)) (p : Page) :
    pageDelay (snapAt input (a + 1)).pending p (entryTime input a) =
      pageDelay (snapAt input a).pending p (entryTime input a) := by
  rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [entryTime_tick hv h ht, (tick_spec hv h ht).2.2.2.2]
    dsimp only
    have hself : (snapAt input a).pending.filter
        (fun ρ => decide ((snapAt input a).x ρ.page ≠ δ)) = (snapAt input a).pending :=
      List.filter_eq_self.mpr (fun ρ hρ => by simpa using (ne_of_gt (delta_lt_of_pending hv hρ)))
    rw [List.filter_append, hself]
    unfold pageDelay
    rw [List.filter_append, List.map_append, List.sum_append, add_eq_left]
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hy
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    rw [hρ.1.1.2, sub_self]
    exact hv.delay_zero ρ hρ.1.1.1
  · rw [(advance_spec hv h ht).2.2.2.2.2.2]

/-- **The delay of one visit**: `(x_p - δ) delay_p(t) ≤ c_p + (x_p - δ) w_p + ō_p`. -/
theorem visitDelay_le (j : ℕ) :
    visitDelay input j ≤ claimAt input j + (fetchAt input j + tripAt input j) + overAt input j := by
  cases hvis : visitPage input j with
  | none =>
    rw [visitDelay_of_none hvis, fetchAt_add_tripAt_of_none hvis, overAt_of_none hvis]
    simp [claimAt, hvis]
  | some p =>
    rw [visitDelay_of_visit hvis, fetchAt_add_tripAt_of_visit hvis, overAt_of_visit hvis]
    simp only [claimAt, hvis]
    obtain ⟨hj, -⟩ := visitPage_eq_some_iff.mp hvis
    have ha : startOf input j < j := startOf_lt_of_visit hv hvis
    obtain ⟨han, hmove⟩ := isTA_startOf hv hj
    rw [entryTime_startOf hv hj]
    set a := startOf input j with ha_def
    set t := entryTime input a with ht_def
    have h1 : pageDelay (snapAt input j).pending p t = pageDelay (snapAt input (a + 1)).pending p t :=
      pageDelay_of_between hv (by omega)
        (fun l' h h1 h2 => ⟨(not_tick_of_not_isTA (not_isTA_of_startOf_lt (j := j) (by omega) (by omega))
          h).1, no_visit_between hv hvis (by omega) h2⟩) t
    have h2 := pageDelay_succ_of_TA hv han hmove p
    have h3 : (snapAt input a).claims p ≤ (snapAt input j).claims p :=
      claims_le_of_between hv ha.le (fun l' h1 h2 => no_visit_before hv hvis h1 h2)
    have h4 := le_overshoot_add input (snapAt input a).pending (snapAt input a).claims t p
    have hx1 : (snapAt input j).x p ≤ 1 := ((x_frac hv j).1 p).2
    have hxδ : δ < (snapAt input j).x p := by
      obtain ⟨ρ, hρ, rfl⟩ := visit_pending hv hvis
      exact delta_lt_of_pending hv hρ
    have hc := claims_nonneg hv j p
    have ho := overshoot_nonneg (input := input) (snapAt input a).pending (snapAt input a).claims p t
    set c := (snapAt input j).claims p
    set o := overshoot input (snapAt input a).pending (snapAt input a).claims p t
    set u := (snapAt input j).x p - δ
    have hu0 : 0 ≤ u := by simp only [u]; linarith
    have hu1 : u ≤ 1 := by simp only [u]; linarith [Instance.delta_pos hv]
    calc u * pageDelay (snapAt input j).pending p t ≤ u * (c + w p + o) := by
          apply mul_le_mul_of_nonneg_left _ hu0
          rw [h1, h2]; linarith
      _ = u * c + w p * u + u * o := by ring
      _ ≤ c + w p * u + o := by
          linarith [mul_le_of_le_one_left hc hu1, mul_le_of_le_one_left ho hu1]

/-! ### Used delay -/

/-- One entry: the claim of the visited page plus the potential after the entry is at most the potential before plus `|λ|/L`. -/
theorem claimAt_add_le (i : ℕ) (h : i < (log input).length) :
    claimAt input i + ∑ q, (snapAt input (i + 1)).claims q ≤
      ∑ q, (snapAt input i).claims q + lenAt input i / L := by
  have hL := Instance.L_pos hv
  cases hvis : visitPage input i with
  | none =>
    obtain ⟨h1, h2⟩ := visitPage_eq_none hvis h
    rw [claims_succ_of_not_visit hv h h1 h2]
    simp only [claimAt, hvis, zero_add, le_add_iff_nonneg_right]
    exact div_nonneg (lenAt_nonneg i) hL.le
  | some p =>
    simp only [claimAt, hvis]
    obtain ⟨h', hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
    · rw [(critical_spec hv h hm).2.2, lenAt_of_critical h hm]
      dsimp only
      rw [sum_update_eq (Finset.mem_univ p)]
      have hsum := sum_claimUpdate_of_triggered hv (critical_facts hv h hm).1
      rw [Finset.sum_sub_distrib] at hsum
      have hle := le_claimUpdate hv (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p p
      linarith
    · rw [(trip_spec hv h hm).2.2.2]
      dsimp only
      rw [sum_update_eq (Finset.mem_univ π.page)]
      have := lenAt_nonneg (input := input) i
      have := div_nonneg this hL.le
      linarith

/-- **Used delay**: the claims of all visits sum to at most `∑_λ |λ| / L`. -/
theorem sum_claimAt_le :
    ∑ j ∈ Finset.range (log input).length, claimAt input j ≤ lenTotal input / L := by
  set Φ : ℕ → ℝ := fun i => ∑ q, (snapAt input i).claims q with hΦ
  have key : ∀ i ∈ Finset.range (log input).length,
      claimAt input i ≤ (Φ i - Φ (i + 1)) + lenAt input i / L := by
    intro i hi
    have := claimAt_add_le hv i (Finset.mem_range.mp hi)
    simp only [hΦ]
    linarith
  have h0 : Φ 0 = 0 := by simp [hΦ, snapAt_zero hv, initialSnap]
  have hn : 0 ≤ Φ (log input).length :=
    Finset.sum_nonneg fun q _ => claims_nonneg hv _ q
  calc _ ≤ ∑ i ∈ Finset.range (log input).length, ((Φ i - Φ (i + 1)) + lenAt input i / L) :=
        Finset.sum_le_sum key
    _ = (Φ 0 - Φ (log input).length) + lenTotal input / L := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.sum_div]
        rfl
    _ ≤ lenTotal input / L := by linarith

end

end

end PagingWithDelay.PMD.DelayProof
