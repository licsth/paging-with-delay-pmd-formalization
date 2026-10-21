import PagingWithDelay.Run.Basic
import PagingWithDelay.Run.Path
import PagingWithDelay.Hole

/-!
# Helper facts about the run

The log as a list of `(snapAt i, moveAt i)`, the output as the concatenation of the entries' waypoints (`wpAt`), its fetch cost as a sum over the entries (`pathFrom_output`, `fetchCost_output`), the first move, the range of examined levels, and fractional states along the run.

The path costs `pathFrom`, `lastState`, `dFetch` are those of `Run/Path.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage IsRest IsFrac
  restMass pathFrom lastState dFetch)

noncomputable section

variable {input : Instance Page}

theorem sum_update_eq {ι : Type*} [DecidableEq ι] {S : Finset ι} {a : ι} (ha : a ∈ S)
    (f : ι → ℝ) (v : ℝ) : ∑ x ∈ S, Function.update f a v x = ∑ x ∈ S, f x - f a + v := by
  rw [Finset.sum_update_of_mem ha, Finset.sum_eq_add_sum_diff_singleton ha f]
  ring

theorem log_getElem (i : ℕ) (h : i < (log input).length) :
    (log input)[i] = (snapAt input i, moveAt i h) := by
  simp [snapAt, h, moveAt]

theorem snapAt_of_ge_len {i : ℕ} (h : (log input).length ≤ i) :
    snapAt input i = snapAt input (log input).length := by
  simp [snapAt, not_lt.2 h]

/-- The waypoints of entry `i` (empty past the end). -/
def wpAt (input : Instance Page) (i : ℕ) : List (Waypoint Page) :=
  if h : i < (log input).length then waypoints input (snapAt input i) (moveAt i h) else []

theorem wpAt_of_lt {i : ℕ} (h : i < (log input).length) :
    wpAt input i = waypoints input (snapAt input i) (moveAt i h) := by
  simp [wpAt, h]

/-- The output of `PMD` is the concatenation of the waypoints of the log entries. -/
theorem output_eq (hv : input.Valid) :
    preemptiveMirrorDescent input = (log input).flatMap fun e => waypoints input e.1 e.2 :=
  rfl

theorem mem_output_iff (hv : input.Valid) {w : Waypoint Page} :
    w ∈ preemptiveMirrorDescent input ↔ ∃ i, ∃ _ : i < (log input).length, w ∈ wpAt input i := by
  simp only [preemptiveMirrorDescent, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hw⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    rw [log_getElem i hi] at hw
    exact ⟨i, hi, by simpa [wpAt, hi] using hw⟩
  · rintro ⟨i, hi, hw⟩
    refine ⟨_, List.getElem_mem hi, ?_⟩
    rw [log_getElem i hi]
    simpa [wpAt, hi] using hw

theorem flatMap_take (m : ℕ) (hm : m ≤ (log input).length) :
    ((log input).take (m + 1)).flatMap (fun e => waypoints input e.1 e.2) =
      ((log input).take m).flatMap (fun e => waypoints input e.1 e.2) ++ wpAt input m := by
  by_cases h : m < (log input).length
  · rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem h, log_getElem m h]
    simp [wpAt, h]
  · have hm' : m = (log input).length := le_antisymm hm (not_lt.1 h)
    subst hm'
    simp [wpAt, List.take_of_length_le (Nat.le_succ _)]

/-- Summing along the chain: if each entry ends in the state before the next, the cost of the output from the initial state is the sum of the entries' costs. -/
theorem pathFrom_take (d : (Page → ℝ) → (Page → ℝ) → ℝ)
    (hlast : ∀ i, i < (log input).length →
      lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x)
    (m : ℕ) (hm : m ≤ (log input).length) :
    pathFrom d (snapAt input 0).x
        (((log input).take m).flatMap (fun e => waypoints input e.1 e.2)) =
      ∑ i ∈ Finset.range m, pathFrom d (snapAt input i).x (wpAt input i) ∧
    lastState (snapAt input 0).x
        (((log input).take m).flatMap (fun e => waypoints input e.1 e.2)) =
      (snapAt input m).x := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [flatMap_take m (by omega), PagingWithDelay.PMD.pathFrom_append,
      PagingWithDelay.PMD.lastState_append, ih2, ih1, Finset.sum_range_succ]
    exact ⟨rfl, hlast m (by omega)⟩

theorem pathFrom_output (d : (Page → ℝ) → (Page → ℝ) → ℝ)
    (hlast : ∀ i, i < (log input).length →
      lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x) :
    pathFrom d (snapAt input 0).x
        ((log input).flatMap (fun e => waypoints input e.1 e.2)) =
      ∑ i ∈ Finset.range (log input).length,
        pathFrom d (snapAt input i).x (wpAt input i) := by
  have := (pathFrom_take d hlast (log input).length le_rfl).1
  rwa [List.take_length] at this

/-- The levels examined or in a preemptive service lie in `[minLevel, maxLevel]`. -/
def StageOK (input : Instance Page) : Stage Page → Prop
  | .idle => True
  | .examine e => minLevel input ≤ e ∧ e ≤ maxLevel input
  | .preempt e _ => minLevel input ≤ e ∧ e ≤ maxLevel input

theorem stageOK_afterLevel {e : ℤ} (he : minLevel input ≤ e ∧ e ≤ maxLevel input) :
    StageOK input (afterLevel input e) := by
  unfold afterLevel
  split_ifs with h
  · exact ⟨by omega, by omega⟩
  · trivial

theorem baseState_of_preempt {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) : baseState (snapAt input i) = b := by
  simp [baseState, hs]

section

variable (hv : input.Valid)
include hv

/-- The first move is a tick (no request is pending initially). -/
theorem first_tick (h : 0 < (log input).length) :
    ∃ t, moveAt 0 h = .tick t := by
  have hn := next_snapAt hv 0 h
  have hinv := inv_snapAt hv 0
  rw [snapAt_zero hv] at hn hinv
  generalize hm : moveAt 0 h = m at hn
  cases m with
  | tick t => exact ⟨t, rfl⟩
  | advance t =>
    obtain ⟨-, -, hadv, -⟩ := next_advance hn
    obtain ⟨τ, -, p, hp⟩ := hadv.1
    obtain ⟨ρ, hρ, -⟩ :=
      exists_pending_of_triggered (triggered_of_triggerCond hp) (hinv.claims p) (hv.weight_pos p)
    simp [initialSnap] at hρ
  | critical p =>
    obtain ⟨-, hp, -⟩ := next_critical hn
    obtain ⟨ρ, hρ, -⟩ := hinv.exists_pending_of_triggerPage hv hp
    simp [initialSnap] at hρ
  | skip e => obtain ⟨hs, -⟩ := next_skip hn; simp [initialSnap] at hs
  | openHole e => obtain ⟨hs, -⟩ := next_openHole hn; simp [initialSnap] at hs
  | trip e π => obtain ⟨⟨b, hs⟩, -⟩ := next_trip hn; simp [initialSnap] at hs
  | closeHole e stop => obtain ⟨b, hs, -⟩ := next_closeHole hn; simp [initialSnap] at hs

/-- The head of the output is the initial state. -/
theorem output_head :
    ∀ a ∈ ((log input).flatMap (fun e => waypoints input e.1 e.2)).head?,
      a.state = (snapAt input 0).x := by
  intro a ha
  rcases hl : log input with _ | ⟨e0, tl⟩
  · simp [hl] at ha
  · have h0 : 0 < (log input).length := by simp [hl]
    obtain ⟨t, ht⟩ := first_tick hv h0
    have he0 : e0 = (snapAt input 0, moveAt 0 h0) := by
      rw [← log_getElem 0 h0]; simp [hl]
    rw [hl, he0, ht] at ha
    simp [waypoints] at ha
    rw [← ha]

/-- Every entry ends in the state before the next one. -/
theorem lastState_wpAt (i : ℕ) (h : i < (log input).length) :
    lastState (snapAt input i).x (wpAt input i) = (snapAt input (i + 1)).x := by
  rw [wpAt_of_lt h]
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · rw [(tick_spec hv h hm).2.2.2.2]; simp [waypoints]
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]; simp [waypoints]
  · rw [(critical_spec hv h hm).2.2]; simp [waypoints]
  · rw [(skip_spec hv h hm).2.2]; simp [waypoints]
  · rw [(openHole_spec hv h hm).2.2]; simp [waypoints]
  · rw [(trip_spec hv h hm).2.2.2]; simp [waypoints]
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    rw [he]; simp [waypoints, hs]

/-- The fetch cost of the output is the sum over the log entries of the fetch costs of their waypoint paths. -/
theorem fetchCost_output :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) =
      ∑ i ∈ Finset.range (log input).length,
        pathFrom (dFetch input) (snapAt input i).x (wpAt input i) := by
  rw [output_eq hv,
    PagingWithDelay.PMD.fetchCost_eq_pathFrom' input (snapAt input 0).x _
      (output_head hv)]
  exact pathFrom_output _ (lastState_wpAt hv)

theorem stageOK (i : ℕ) : StageOK input (snapAt input i).stage := by
  induction i with
  | zero => rw [snapAt_zero hv]; trivial
  | succ i ih =>
    by_cases h : i < (log input).length
    · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
      · rw [(tick_spec hv h hm).2.2.2.2]; exact ih
      · rw [(advance_spec hv h hm).2.2.2.2.2.2]; exact ih
      · rw [(critical_spec hv h hm).2.2]
        exact ⟨le_rfl, PagingWithDelay.PMD.minLevel_le_maxLevel hv⟩
      · obtain ⟨hs, -, he⟩ := skip_spec hv h hm
        rw [he]; rw [hs] at ih; exact stageOK_afterLevel ih
      · obtain ⟨hs, -, he⟩ := openHole_spec hv h hm
        rw [he]; rw [hs] at ih; exact ih
      · rw [(trip_spec hv h hm).2.2.2]; exact ih
      · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
        rw [he]; rw [hs] at ih; exact stageOK_afterLevel ih
    · rw [snapAt_of_ge_len (by omega)]
      rw [snapAt_of_ge_len (by omega)] at ih
      exact ih

/-- Every state of the run is fractional with missing mass at least `n - k`. -/
theorem x_frac (i : ℕ) :
    IsFrac input (snapAt input i).x ∧ restMass input ≤ ∑ j, (snapAt input i).x j := by
  have hvb := hv
  by_cases hs : ∃ e b, (snapAt input i).stage = .preempt e b
  · obtain ⟨e, b, hs⟩ := hs
    obtain ⟨hx, hcond⟩ := x_eq_hole hv hs
    have hb := baseState_isRest hv i
    rw [baseState_of_preempt hs] at hb
    rw [hx]
    refine ⟨PagingWithDelay.PMD.hole_isFrac hvb hb.1 e, ?_⟩
    rw [PagingWithDelay.PMD.sum_hole hvb hb.1 e hcond, hb.2]
    linarith [Instance.delta_lt_one hv]
  · push_neg at hs
    rw [x_eq_baseState hv hs]
    exact ⟨(baseState_isRest hv i).1, (baseState_isRest hv i).2.ge⟩

/-- Every waypoint of entry `i` is at the time of the entry and is a fractional state with missing mass at least `n - k`. -/
theorem wp_spec (i : ℕ) (h : i < (log input).length) :
    ∀ w ∈ wpAt input i, w.time = entryTime input i ∧ IsFrac input w.state ∧
      restMass input ≤ ∑ j, w.state j := by
  intro w hw
  have hfr := x_frac hv
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    exact ⟨(entryTime_tick hv h hm).symm, hfr i⟩
  · simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    exact ⟨(entryTime_advance hv h hm).1.symm, hfr i⟩
  · obtain ⟨-, -, he⟩ := critical_spec hv h hm
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    have hx1 : (snapAt input (i + 1)).x =
        criticalState input (snapAt input i).x p := by rw [he]
    refine ⟨ht.symm, ?_⟩
    dsimp only
    rw [← hx1]; exact hfr (i + 1)
  · simp [wpAt, dif_pos h, hm, waypoints] at hw
  · obtain ⟨-, -, he⟩ := openHole_spec hv h hm
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_singleton] at hw
    subst hw
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    have hx1 : (snapAt input (i + 1)).x = hole input (snapAt input i).x e := by rw [he]
    refine ⟨ht.symm, ?_⟩
    dsimp only
    rw [← hx1]; exact hfr (i + 1)
  · obtain ⟨⟨b, hs⟩, -, -, -⟩ := trip_spec hv h hm
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, waypoints, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · subst hw
      refine ⟨ht.symm, ?_, ?_⟩
      · intro j
        by_cases hj : j = π.page
        · subst hj
          simp only [Function.update_self]
          exact ⟨le_rfl, (Instance.delta_lt_one hv).le⟩
        · simp only [Function.update_of_ne hj]
          exact (hfr i).1 j
      · obtain ⟨hx, hcond⟩ := x_eq_hole hv hs
        have hb := baseState_isRest hv i
        rw [baseState_of_preempt hs] at hb
        have hsum : ∑ j, (snapAt input i).x j = restMass input + (1 - input.delta) := by
          rw [hx, PagingWithDelay.PMD.sum_hole hv hb.1 e hcond, hb.2]
        have hp := ((hfr i).1 π.page).2
        dsimp only
        rw [sum_update_eq (Finset.mem_univ _), hsum]
        linarith
    · subst hw
      exact ⟨ht.symm, hfr i⟩
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    have ht := entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, waypoints, hs, List.mem_singleton] at hw
    subst hw
    have hx1 : (snapAt input (i + 1)).x = b := by rw [he]
    refine ⟨ht.symm, ?_⟩
    dsimp only
    rw [← hx1]; exact hfr (i + 1)

/-- While a request stays pending, no waypoint has its page at `δ`: if `ρ` is pending after entry `i`, every waypoint of entry `i` has `x_p > δ`. Hence a request is served (`FracSchedule.serviceTime`) exactly at the entry that removes it from the pending list (or at its arrival tick, if it never becomes pending). -/
theorem delta_lt_wp_of_pending_succ {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (i + 1)).pending) :
    ∀ w ∈ wpAt input i, input.delta < w.state ρ.page := by
  intro w hw
  have hfr := x_frac hv
  have hnext : input.delta < (snapAt input (i + 1)).x ρ.page := delta_lt_of_pending hv hρ
  rw [wpAt_of_lt h] at hw
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> rw [hm] at hw
  · have he := (tick_spec hv h hm).2.2.2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hρ
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    exact lt_of_le_of_ne ((hfr i).1 ρ.page).1 (Ne.symm hρ.2)
  · have he := (advance_spec hv h hm).2.2.2.2.2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · have he := (critical_spec hv h hm).2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · simp [waypoints] at hw
  · have he := (openHole_spec hv h hm).2.2
    simp only [waypoints, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext
  · have he := (trip_spec hv h hm).2.2.2
    have hρ' := hρ
    rw [he] at hρ'
    simp only [List.mem_filter, decide_eq_true_eq] at hρ'
    have hx : input.delta < (snapAt input i).x ρ.page := delta_lt_of_pending hv hρ'.1
    simp only [waypoints, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw
    · subst hw
      simp only [Function.update_of_ne hρ'.2]
      exact hx
    · subst hw; exact hx
  · obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    simp only [waypoints, hs, List.mem_singleton] at hw
    subst hw
    rw [he] at hnext
    exact hnext

end

end

end PMD

end PagingWithDelay
