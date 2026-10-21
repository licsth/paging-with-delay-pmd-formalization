import PagingWithDelay.Analysis.AlgDelay.Visit

/-!
# `prop:algdelay`, part 4: the overshoots

Fix a time `t`, with start index `a` (the tick or advance that set `t`), and let `F_a` be the entries at time `t` (`startOf l = a`). Let `q` be the heaviest page visited at time `t` with positive overshoot `ō_q`. Every page is visited at most once at time `t`, and `q` has not triggered since the previous time, so (`sum_overshoot_le_of_not_triggered`)

  `∑_{visits at t} ō_p ≤ ∑_{w_{q'} ≤ w_q} o_{q'}(t) ≤ |λ_q(x̄)| / L`,

with `x̄` the state at `a`. By `lem:drop` (along the chain of critical services at time `t`) and, if `q` is visited by a round trip of a level-`W` preemptive service, by its condition (`|λ_q| ≤ L W` from its start state, and `W ≤ 2 W (1 - δ)`),

  `|λ_q(x̄)| ≤ 2 ∑_{l ∈ F_a} |λ_l| + 2 L ∑_{l ∈ F_a} hole_l` (`serviceEnd_le_block`).

As in the paper, in the critical case both the chain and the service on `q` are bounded by `∑_{l ∈ F_a} |λ_l|` separately, and `L ≥ 1` turns `2/L` into `2`. Summing over the times (the `F_a` partition the entries): `∑_visits ō ≤ 2 ∑_λ |λ| + 2 · (total hole payments)` (`sum_overAt_le`).
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
/-- The entries at the time started by entry `a`. -/
def block (a : ℕ) : Finset ℕ :=
  (Finset.range (log input).length).filter fun l => startOf input l = a

section

variable (hv : input.Valid)
include hv

theorem mem_block_of_between {a js l : ℕ} (hjs : js < (log input).length)
    (hja : startOf input js = a) (h1 : a ≤ l) (h2 : l ≤ js) : l ∈ block input a := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  rw [startOf_of_between hv hjs (hja ▸ h1) h2, hja]

/-- **Comparing `|λ_q(x̄)|` with the costs at time `t`**: for a visit `js` of `q` at the time started by `a`, the critical service on `q` from the state at `a` is at most twice the total length of the critical services at time `t` plus `2 L` times the hole payments at time `t`. -/
theorem serviceEnd_le_block {a js : ℕ} {q : Page} (hjs : js < (log input).length)
    (hvis : visitPage input js = some q) (hja : startOf input js = a)
    (hδ : δ < (snapAt input a).x q) :
    serviceEnd input (snapAt input a).x q ≤
      2 * ∑ l ∈ block input a, lenAt input l + 2 * L * ∑ l ∈ block input a, holeAt input l := by
  have has : a < js := hja ▸ startOf_lt_of_visit hv hvis
  obtain ⟨han, hmove⟩ : IsTA input a := hja ▸ isTA_startOf hv hjs
  have hidle : (snapAt input a).stage = .idle := by
    rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact (tick_spec hv han ht).1
    · exact (advance_spec hv han ht).1
  have hxa : (snapAt input a).x = baseState (snapAt input a) :=
    x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
  have hvb := hv
  have hrest : IsRest input (baseState (snapAt input a)) := baseState_isRest hv a
  have hδ' : δ < baseState (snapAt input a) q := by
    rw [← hxa]; exact hδ
  have hL := Instance.L_pos hv
  have hnocrit : ∀ m, m ≤ js → ∀ l (hl : l < (log input).length), a ≤ l → l < m →
      moveAt l hl ≠ .critical q := fun m hm l hl h1 h2 hc =>
    no_visit_before hv hvis (hja ▸ h1) (by omega) (visitPage_of_critical hl hc)
  have hlenF : ∀ m, m ≤ js + 1 →
      ∑ l ∈ Finset.Ico a m, lenAt input l ≤ ∑ l ∈ block input a, lenAt input l := by
    intro m hm
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l hl
      rw [Finset.mem_Ico] at hl
      exact mem_block_of_between hv hjs hja hl.1 (by omega)
    · intro l _ _; exact lenAt_nonneg l
  have hholeF : 0 ≤ ∑ l ∈ block input a, holeAt input l :=
    Finset.sum_nonneg fun l _ => holeAt_nonneg hv l
  have hlenF0 : 0 ≤ ∑ l ∈ block input a, lenAt input l :=
    Finset.sum_nonneg fun l _ => lenAt_nonneg l
  rw [hxa]
  obtain ⟨hjsn, hm | ⟨e, π, hm, hπ⟩⟩ := visitPage_eq_some_iff.mp hvis
  · -- `q` is visited by a critical service: the chain ends with it.
    obtain ⟨ps, hqps, hst, hlen⟩ := exists_chain hv has.le (hnocrit js le_rfl)
    have h1 := serviceEnd_le_chainLen_add hvb ps hrest hqps hδ'
    obtain ⟨hidle', -, -⟩ := critical_spec hv hjsn hm
    have hxjs : (snapAt input js).x = baseState (snapAt input js) :=
      x_eq_baseState hv (by intro e b hb; rw [hidle'] at hb; cases hb)
    rw [← hst, ← hxjs, hlen] at h1
    -- the chain and the service on `q` are each at most the lengths at time `t`
    have h2 := hlenF js (by omega)
    have h3 : lenAt input js ≤ ∑ l ∈ block input a, lenAt input l :=
      Finset.single_le_sum (fun l _ => lenAt_nonneg l)
        (mem_block_of_between hv hjsn hja has.le le_rfl)
    rw [lenAt_of_critical hjsn hm] at h3
    nlinarith
  · -- `q` is visited by a round trip of a level-`e` preemptive service opened at `o`.
    obtain ⟨o, ho, hojs, hmo, htrips⟩ := preempt_start hv hjsn (Or.inl ⟨π, hm⟩)
    have hao : a < o := by
      by_contra hle
      push_neg at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨π', hπ'⟩ := htrips a han hlt has
        rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rw [ht] at hπ' <;> cases hπ'
      · subst heq
        rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩ <;> rw [ht] at hmo <;> cases hmo
    obtain ⟨ps, hqps, hst, hlen⟩ := exists_chain hv hao.le (hnocrit o hojs.le)
    have h1 := serviceEnd_le_chainLen_add hvb ps hrest hqps hδ'
    obtain ⟨hexam, hcond, -⟩ := openHole_spec hv ho hmo
    have hxo : (snapAt input o).x = baseState (snapAt input o) :=
      x_eq_baseState hv (by intro e b hb; rw [hexam] at hb; cases hb)
    have h2 := serviceEnd_le_of_preemptCondition hvb (hxo ▸ baseState_isRest hv o) q hcond
    rw [← hst, ← hxo, hlen] at h1
    have h3 := hlenF o (by omega)
    have hhole : holeAt input o = holePayment input e := holeAt_of_openHole ho hmo
    have hδ3 := Instance.delta_le_third hv
    have hlw : levelWeight e ≤ 2 * holeAt input o := by
      rw [hhole]
      unfold holePayment
      nlinarith [PagingWithDelay.PMD.levelWeight_pos e]
    have hoF : holeAt input o ≤ ∑ l ∈ block input a, holeAt input l :=
      Finset.single_le_sum (fun l _ => holeAt_nonneg hv l)
        (mem_block_of_between hv hjsn hja hao.le hojs.le)
    nlinarith

/-- **The overshoots at one time**: the overshoots of the visits at the time started by `a` are at most `∑_{l ∈ F_a} (2 |λ_l| + 2 hole_l)`. -/
theorem sum_overAt_block_le (a : ℕ) :
    ∑ j ∈ block input a, overAt input j ≤
      ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) := by
  have hL := Instance.L_pos hv
  have hRnn : 0 ≤ ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) :=
    Finset.sum_nonneg fun l _ =>
      add_nonneg (mul_nonneg two_pos.le (lenAt_nonneg l)) (mul_nonneg two_pos.le (holeAt_nonneg hv l))
  set G := (block input a).filter fun j => 0 < overAt input j with hG
  have hFG : ∑ j ∈ block input a, overAt input j = ∑ j ∈ G, overAt input j :=
    (Finset.sum_filter_of_ne fun j _ hne => lt_of_le_of_ne (overAt_nonneg j) (Ne.symm hne)).symm
  rw [hFG]
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · rw [hGe, Finset.sum_empty]; exact hRnn
  obtain ⟨j0, hj0⟩ := hGne
  obtain ⟨p0, hp0⟩ : ∃ p0, visitPage input j0 = some p0 := by
    cases hvis : visitPage input j0 with
    | none =>
      have := (Finset.mem_filter.mp hj0).2
      rw [overAt_of_none hvis] at this
      exact absurd this (lt_irrefl 0)
    | some p => exact ⟨p, rfl⟩
  set pg : ℕ → Page := fun j => (visitPage input j).getD p0 with hpg
  have hGmem : ∀ j ∈ G, j < (log input).length ∧ startOf input j = a ∧
      visitPage input j = some (pg j) ∧ 0 < overAt input j := by
    intro j hj
    obtain ⟨hjF, hpos⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjn, hja⟩ := Finset.mem_filter.mp hjF
    refine ⟨Finset.mem_range.mp hjn, hja, ?_, hpos⟩
    cases hvis : visitPage input j with
    | none => rw [overAt_of_none hvis] at hpos; exact absurd hpos (lt_irrefl 0)
    | some p => simp [hpg, hvis]
  obtain ⟨js, hjs, hmax⟩ :=
    Finset.exists_max_image G (fun j => w (pg j)) ⟨j0, hj0⟩
  obtain ⟨hjsn, hjsa, hjsv, hjspos⟩ := hGmem js hjs
  set q := pg js with hq
  have has : a < js := hjsa ▸ startOf_lt_of_visit hv hjsv
  obtain ⟨han, hmove⟩ : IsTA input a := hjsa ▸ isTA_startOf hv hjsn
  set ta := entryTime input a with hta
  have hoverAt : ∀ j ∈ G, overAt input j =
      overshoot input (snapAt input a).pending (snapAt input a).claims (pg j) ta := by
    intro j hj
    obtain ⟨hjn, hja, hjv, -⟩ := hGmem j hj
    rw [overAt_of_visit hjv, entryTime_startOf hv hjn, hja]
  have hpos : (snapAt input a).claims q + w q <
      pageDelay (snapAt input a).pending q ta :=
    overshoot_pos_iff.mp (by rw [← hoverAt js hjs]; exact hjspos)
  obtain ⟨ρq, hρq, hρqp⟩ : ∃ ρ ∈ (snapAt input a).pending, ρ.page = q := by
    apply exists_pending_of_pageDelay_ne (t := ta)
    have := claims_nonneg hv a q
    have := hv.weight_pos q
    intro h0; rw [h0] at hpos; linarith
  have hδq : δ < (snapAt input a).x q := hρqp ▸ delta_lt_of_pending hv hρq
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, snapAt_zero hv] at hρq; simp [initialSnap] at hρq
    · exact h0
  have hnow : (snapAt input a).now < ta := by
    rcases hmove with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [hta, entryTime_tick hv han ht]
      exact now_lt_upcoming hv han.le ha0 (by rw [(tick_spec hv han ht).2.2.2.1]; simp)
    · rw [hta, (entryTime_advance hv han ht).1]; exact (entryTime_advance hv han ht).2
  have hsum := sum_overshoot_le_of_not_triggered ((inv_snapAt hv a).continuous hv) hnow
    (fun τ h1 h2 => not_triggered_before hv han hmove h1 h2 q) hpos
  have hinj : Set.InjOn pg G := by
    intro j1 hj1 j2 hj2 heq
    obtain ⟨hj1n, hj1a, hj1v, -⟩ := hGmem j1 hj1
    obtain ⟨hj2n, hj2a, hj2v, -⟩ := hGmem j2 hj2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact no_visit_between hv hj2v (by rw [hj2a, ← hj1a]; exact startOf_lt_of_visit hv hj1v)
        hlt (by rw [hj1v, heq])
    · exact no_visit_between hv hj1v (by rw [hj1a, ← hj2a]; exact startOf_lt_of_visit hv hj2v)
        hlt (by rw [hj2v, heq])
  have hle1 : ∑ j ∈ G, overAt input j ≤
      ∑ p ∈ lighter input q, overshoot input (snapAt input a).pending (snapAt input a).claims p ta := by
    rw [Finset.sum_congr rfl hoverAt, ← Finset.sum_image (f := fun p =>
      overshoot input (snapAt input a).pending (snapAt input a).claims p ta) hinj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      exact mem_lighter.mpr (hmax j hj)
    · intro _ _ _; exact overshoot_nonneg _ _ _ _
  have hblock := serviceEnd_le_block hv hjsn hjsv hjsa hδq
  have hdiv : (2 * ∑ l ∈ block input a, lenAt input l +
        2 * L * ∑ l ∈ block input a, holeAt input l) / L =
      ∑ l ∈ block input a, (2 * lenAt input l / L + 2 * holeAt input l) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum]
    field_simp
  calc ∑ j ∈ G, overAt input j ≤ serviceEnd input (snapAt input a).x q / L :=
        hle1.trans hsum
    _ ≤ (2 * ∑ l ∈ block input a, lenAt input l +
          2 * L * ∑ l ∈ block input a, holeAt input l) / L :=
        div_le_div_of_nonneg_right hblock hL.le
    _ = ∑ l ∈ block input a, (2 * lenAt input l / L + 2 * holeAt input l) := hdiv
    _ ≤ _ := Finset.sum_le_sum fun l _ => add_le_add_left
        (div_le_self (mul_nonneg two_pos.le (lenAt_nonneg l)) (Instance.one_le_L hv)) _

/-- **Overshoots**: the overshoots of all visits sum to at most `2 ∑_λ |λ| + 2 · (total hole payments)`. -/
theorem sum_overAt_le :
    ∑ j ∈ Finset.range (log input).length, overAt input j ≤
      2 * lenTotal input + 2 * holeTotal input := by
  have hmaps : ∀ j ∈ Finset.range (log input).length,
      startOf input j ∈ Finset.range (log input).length := fun j hj =>
    Finset.mem_range.mpr (lt_of_le_of_lt (startOf_le j) (Finset.mem_range.mp hj))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ a ∈ Finset.range (log input).length,
        ∑ l ∈ block input a, (2 * lenAt input l + 2 * holeAt input l) :=
        Finset.sum_le_sum fun a _ => sum_overAt_block_le hv a
    _ = ∑ l ∈ Finset.range (log input).length, (2 * lenAt input l + 2 * holeAt input l) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = 2 * lenTotal input + 2 * holeTotal input := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

end

end

end PagingWithDelay.PMD.DelayProof
