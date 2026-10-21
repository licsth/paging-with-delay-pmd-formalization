import PagingWithDelay.Analysis.AlgDelay.Run

/-!
# `prop:algdelay`, part 2: from the fractional delay cost to the visits

The fractional delay cost of `PMD` (`FracSchedule.delayCost`) is a sum over the request list. Every request is either served on arrival (cost `d(0) = 0`) or pending until the visit of its page that serves it. We bound the delay cost by the sum over the visits `j` of the delays of the requests served by `j`, each weighted with the missing mass `x_p - δ` of the page right before the visit (`delayCost_le_sum_visitDelay`):

* `stateBefore_tick`: the state right before the arrival time `a` of a request is the state before the tick at `a`;
* by `obs:monotone`, the weight `α_ρ` of a request is at most `x_p - δ` right before its serving visit;
* multiplicities: the request list may contain equal requests; each occurs in the pending list at its serving visit at least as often as in the request list (`count_requests_le_pending`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay.PMD.DelayProof

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch hole holePayment preemptCondition tripCost IsRest lastState)

open Classical

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

noncomputable section

variable {input : Instance Page}

/-! ### Definitions -/

variable (input) in
/-- The requests served by entry `j`: the pending requests on the page it visits (none if it is not a visit). -/
def servedAt (j : ℕ) : List (Request Page) :=
  match visitPage input j with
  | some p => (snapAt input j).pending.filter fun ρ => decide (ρ.page = p)
  | none => []

variable (input) in
open scoped PagingWithDelay.InstanceNotation in
/-- The delay of `ρ` at the time of entry `j`, weighted with the missing mass `x_p - δ` of its page right before entry `j`. -/
def reqCost (j : ℕ) (ρ : Request Page) : ℝ :=
  ((snapAt input j).x ρ.page - δ) * ρ.delay (entryTime input j - ρ.arrival)

variable (input) in
/-- The weighted delay of the requests served by entry `j`. -/
def visitDelay (j : ℕ) : ℝ := ((servedAt input j).map (reqCost input j)).sum

theorem mem_servedAt {j : ℕ} {ρ : Request Page} (h : ρ ∈ servedAt input j) :
    ρ ∈ (snapAt input j).pending ∧ visitPage input j = some ρ.page := by
  unfold servedAt at h
  split at h
  · rename_i p hp
    simp only [List.mem_filter, decide_eq_true_eq] at h
    exact ⟨h.1, h.2 ▸ hp⟩
  · simp at h

theorem servedAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    servedAt input j = (snapAt input j).pending.filter fun ρ => decide (ρ.page = p) := by
  simp [servedAt, hvis]

theorem servedAt_of_none {j : ℕ} (hvis : visitPage input j = none) : servedAt input j = [] := by
  simp [servedAt, hvis]

open scoped PagingWithDelay.InstanceNotation in
/-- The weighted delay of a visit of `p` is `(x_p - δ) · delay_p(t)`. -/
theorem visitDelay_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    visitDelay input j = ((snapAt input j).x p - δ) *
      pageDelay (snapAt input j).pending p (entryTime input j) := by
  unfold visitDelay pageDelay
  rw [servedAt_of_visit hvis, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ρ hρ
  simp only [List.mem_filter, decide_eq_true_eq] at hρ
  simp [reqCost, hρ.2]

theorem visitDelay_of_none {j : ℕ} (hvis : visitPage input j = none) : visitDelay input j = 0 := by
  simp [visitDelay, servedAt_of_none hvis]

/-! ### The state right before an arrival -/

theorem lastState_eq_getLast : ∀ (y : Page → ℝ) (A : List (Waypoint Page)) (h : A ≠ []),
    lastState y A = (A.getLast h).state
  | _, [], h => absurd rfl h
  | _, [a], _ => rfl
  | y, a :: b :: rest, _ => by
    rw [PagingWithDelay.PMD.lastState_cons, lastState_eq_getLast a.state (b :: rest)
      (List.cons_ne_nil _ _)]
    rfl

section

variable (hv : input.Valid)
include hv

theorem mem_take_flatMap {m : ℕ} {w : Waypoint Page}
    (hw : w ∈ ((log input).take m).flatMap fun e => waypoints input e.1 e.2) :
    ∃ l, l < m ∧ ∃ h : l < (log input).length, w ∈ wpAt input l := by
  rw [List.mem_flatMap] at hw
  obtain ⟨e, he, hwe⟩ := hw
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hl
  have hl1 : l < m := lt_of_lt_of_le hl (min_le_left _ _)
  have hl2 : l < (log input).length := lt_of_lt_of_le hl (min_le_right _ _)
  refine ⟨l, hl1, hl2, ?_⟩
  rw [List.getElem_take, log_getElem l hl2] at hwe
  rw [wpAt_of_lt hl2]
  exact hwe

theorem mem_drop_flatMap {m : ℕ} {w : Waypoint Page}
    (hw : w ∈ ((log input).drop m).flatMap fun e => waypoints input e.1 e.2) :
    ∃ l, m ≤ l ∧ ∃ h : l < (log input).length, w ∈ wpAt input l := by
  rw [List.mem_flatMap] at hw
  obtain ⟨e, he, hwe⟩ := hw
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem he
  rw [List.length_drop] at hl
  have hl2 : m + l < (log input).length := by omega
  refine ⟨m + l, by omega, hl2, ?_⟩
  rw [List.getElem_drop, log_getElem (m + l) hl2] at hwe
  rw [wpAt_of_lt hl2]
  exact hwe

/-- The state right before the arrival time `t` (in the sense of `FracSchedule.stateBefore`) is the state before the tick at `t`. -/
theorem stateBefore_tick {i₀ : ℕ} (h₀ : i₀ < (log input).length) {t : ℝ}
    (ht : moveAt i₀ h₀ = .tick t) :
    FracSchedule.stateBefore (preemptiveMirrorDescent input) t = (snapAt input i₀).x := by
  set W : Entry Page → List (Waypoint Page) := fun e => waypoints input e.1 e.2 with hW
  set A := ((log input).take i₀).flatMap W with hA
  set B := ((log input).drop i₀).flatMap W with hB
  have hXAB : preemptiveMirrorDescent input = A ++ B := by
    rw [output_eq hv, hA, hB, ← List.flatMap_append, List.take_append_drop]
  have hAt : ∀ w ∈ A, w.time < t := by
    intro w hw
    obtain ⟨l, hl, hl', hwl⟩ := mem_take_flatMap hv hw
    rw [(wp_spec hv l hl' w hwl).1]
    exact entryTime_lt_of_tick hv h₀ ht hl
  have hBt : ∀ w ∈ B, ¬ w.time < t := by
    intro w hw
    obtain ⟨l, hl, hl', hwl⟩ := mem_drop_flatMap hv hw
    rw [(wp_spec hv l hl' w hwl).1, not_lt, ← entryTime_tick hv h₀ ht]
    exact entryTime_mono hv hl
  have hfilter : (preemptiveMirrorDescent input).filter (fun w => decide (w.time < t)) = A := by
    rw [hXAB, List.filter_append, List.filter_eq_self.mpr (fun w hw => by simpa using hAt w hw),
      List.filter_eq_nil_iff.mpr (fun w hw => by simpa using hBt w hw), List.append_nil]
  have hlast : lastState (snapAt input 0).x A = (snapAt input i₀).x :=
    (pathFrom_take (fun _ _ => 0) (lastState_wpAt hv) i₀ h₀.le).2
  unfold FracSchedule.stateBefore
  rw [hfilter]
  by_cases hAe : A = []
  · rw [hAe] at hlast ⊢
    simp only [List.getLast?_nil]
    rw [PagingWithDelay.PMD.lastState_nil] at hlast
    rw [← hlast]
    have hmem : (⟨t, (snapAt input i₀).x⟩ : Waypoint Page) ∈ preemptiveMirrorDescent input := by
      rw [mem_output_iff hv]
      exact ⟨i₀, h₀, by rw [wpAt_of_lt h₀, ht]; simp [waypoints]⟩
    cases hhd : (preemptiveMirrorDescent input).head? with
    | none =>
      rw [List.head?_eq_none_iff] at hhd
      rw [hhd] at hmem; simp at hmem
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      exact output_head hv w (by rw [← output_eq hv]; exact hhd)
  · rw [List.getLast?_eq_some_getLast hAe]
    dsimp only
    rw [← lastState_eq_getLast (snapAt input 0).x A hAe, hlast]

/-! ### Multiplicities -/

/-- A request that stays pending does not lose copies. -/
theorem count_pending_succ {l : ℕ} (h : l < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (l + 1)).pending) :
    (snapAt input l).pending.count ρ ≤ (snapAt input (l + 1)).pending.count ρ := by
  rcases hm : moveAt l h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · have heq := (tick_spec hv h hm).2.2.2.2
    rw [heq] at hρ ⊢
    dsimp only at hρ ⊢
    rw [List.count_filter, List.count_append]
    · omega
    · exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [(critical_spec hv h hm).2.2] at hρ ⊢
    dsimp only at hρ ⊢
    rw [List.count_filter]
    exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [(trip_spec hv h hm).2.2.2] at hρ ⊢
    dsimp only at hρ ⊢
    rw [List.count_filter]
    exact (List.mem_filter.mp hρ).2
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]

/-- At the tick of its arrival, a request that becomes pending enters the pending list with all its copies in the request list. -/
theorem count_requests_le_tick {i₀ : ℕ} (h₀ : i₀ < (log input).length) {ρ : Request Page}
    (ht : moveAt i₀ h₀ = .tick ρ.arrival) (hρ : ρ ∈ (snapAt input (i₀ + 1)).pending) :
    input.requests.count ρ ≤ (snapAt input (i₀ + 1)).pending.count ρ := by
  have heq := (tick_spec hv h₀ ht).2.2.2.2
  rw [heq] at hρ ⊢
  dsimp only at hρ ⊢
  rw [List.count_filter, List.count_append, List.count_filter]
  · omega
  · simp
  · exact (List.mem_filter.mp hρ).2

theorem count_requests_le_pending {i₀ j : ℕ} (h₀ : i₀ < (log input).length) {ρ : Request Page}
    (ht : moveAt i₀ h₀ = .tick ρ.arrival) (hij : i₀ < j)
    (hpend : ∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending) :
    input.requests.count ρ ≤ (snapAt input j).pending.count ρ := by
  induction j, hij using Nat.le_induction with
  | base => exact count_requests_le_tick hv h₀ ht (hpend _ (by omega) le_rfl)
  | succ m hm ih =>
    refine (ih fun l h1 h2 => hpend l h1 (by omega)).trans ?_
    by_cases hlt : m < (log input).length
    · exact count_pending_succ hv hlt (hpend _ (by omega) le_rfl)
    · rw [snapAt_of_ge (i := m + 1) (by omega), snapAt_of_ge (i := m) (by omega)]

/-! ### The bridge -/

theorem reqCost_nonneg {j : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input j).pending) :
    0 ≤ reqCost input j ρ := by
  obtain ⟨hreq, harr, -⟩ := pending_spec hv hρ
  have hx := delta_lt_of_pending hv hρ
  have hd : 0 ≤ ρ.delay (entryTime input j - ρ.arrival) := by
    rw [← hv.delay_zero ρ hreq]
    exact hv.delay_mono ρ hreq (by linarith [now_le_entryTime hv j])
  exact mul_nonneg (by linarith) hd

theorem visitDelay_eq_sum_count (j : ℕ) :
    visitDelay input j =
      ∑ ρ ∈ input.requests.toFinset, ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
  unfold visitDelay
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset
  · intro ρ hρ
    rw [List.mem_toFinset] at hρ ⊢
    exact (pending_spec hv (mem_servedAt hρ).1).1
  · intro ρ _ hρ
    rw [List.mem_toFinset] at hρ
    rw [List.count_eq_zero_of_not_mem hρ]
    simp

open scoped PagingWithDelay.InstanceNotation in
/-- The delay cost of one request (counted with its multiplicity) is at most what the visits charge for it. -/
theorem request_le {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    (input.requests.count ρ : ℝ) *
        ((FracSchedule.stateBefore (preemptiveMirrorDescent input) ρ.arrival ρ.page -
            δ) *
          ρ.delay (FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ -
            ρ.arrival)) ≤
      ∑ j ∈ Finset.range (log input).length,
        ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
  obtain ⟨i₀, j, h₀, hj, ht, hij, hpend, hnot, hserv⟩ := serviceTime_spec hv hρ
  have hnonneg : ∀ j' ∈ Finset.range (log input).length,
      0 ≤ ((servedAt input j').count ρ : ℝ) * reqCost input j' ρ := by
    intro j' _
    by_cases hc : (servedAt input j').count ρ = 0
    · simp [hc]
    · have hmem : ρ ∈ servedAt input j' := List.count_pos_iff.mp (Nat.pos_of_ne_zero hc)
      exact mul_nonneg (Nat.cast_nonneg _) (reqCost_nonneg hv (mem_servedAt hmem).1)
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst heq
    rw [hserv, entryTime_tick hv h₀ ht, sub_self, hv.delay_zero ρ hρ, mul_zero, mul_zero]
    exact Finset.sum_nonneg hnonneg
  · have hρj := hpend j hlt le_rfl
    obtain ⟨hvis, -⟩ := pending_removed hv hj hρj hnot
    have hvp : visitPage input j = some ρ.page := by
      rcases hvis with hm | ⟨e, π, hm, hπ⟩
      · exact visitPage_of_critical hj hm
      · rw [← hπ]; exact visitPage_of_trip hj hm
    have hcount : (servedAt input j).count ρ = (snapAt input j).pending.count ρ := by
      rw [servedAt_of_visit hvp, List.count_filter (by simp)]
    have hcR := count_requests_le_pending hv h₀ ht hlt hpend
    have hx : (snapAt input i₀).x ρ.page ≤ (snapAt input j).x ρ.page := by
      rw [x_eq_baseState hv (fun e b hb => by rw [(tick_spec hv h₀ ht).1] at hb; cases hb)]
      apply baseState_le_x_of_mono hv hij
      intro l hl h1 h2 hm
      exact ((pending_succ_of_critical hv hl hm).mp (hpend (l + 1) (by omega) (by omega))).2 rfl
    have hd : 0 ≤ ρ.delay (entryTime input j - ρ.arrival) := by
      rw [← hv.delay_zero ρ hρ]
      apply hv.delay_mono ρ hρ
      have := entryTime_mono hv hij
      rw [entryTime_tick hv h₀ ht] at this
      linarith
    have hF : (FracSchedule.stateBefore (preemptiveMirrorDescent input) ρ.arrival ρ.page -
          δ) *
          ρ.delay (FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ -
            ρ.arrival) ≤ reqCost input j ρ := by
      rw [hserv, stateBefore_tick hv h₀ ht]
      exact mul_le_mul_of_nonneg_right (by linarith) hd
    have hF0 : 0 ≤ reqCost input j ρ := reqCost_nonneg hv hρj
    calc _ ≤ (input.requests.count ρ : ℝ) * reqCost input j ρ :=
          mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _)
      _ ≤ ((servedAt input j).count ρ : ℝ) * reqCost input j ρ := by
          apply mul_le_mul_of_nonneg_right _ hF0
          rw [hcount]; exact_mod_cast hcR
      _ ≤ _ := Finset.single_le_sum hnonneg (Finset.mem_range.mpr hj)

/-- **The bridge**: the fractional delay cost of `PMD` is at most the total weighted delay of the requests served by the visits. -/
theorem delayCost_le_sum_visitDelay :
    FracSchedule.delayCost input (preemptiveMirrorDescent input) ≤
      ∑ j ∈ Finset.range (log input).length, visitDelay input j := by
  unfold FracSchedule.delayCost
  rw [Finset.sum_list_map_count]
  simp only [nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => visitDelay_eq_sum_count hv j, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [List.mem_toFinset] at hρ
  exact request_le hv hρ

end

end

end PagingWithDelay.PMD.DelayProof
