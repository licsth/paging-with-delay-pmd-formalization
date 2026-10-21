import PagingWithDelay.Run.Invariant

/-!
# The run of `PMD`: log, snapshots, and their invariants

`snapAt i` is the loop state before log entry `i` (after entry `i - 1`); `snapAt (log.length)` is the final state. This file collects what the analysis uses about the run: the chain of moves, the semantics of each move, the order of times, the invariants (`lem:inv`), pending-list and claims facts, `obs:monotone`, and the structure of preemptive services and level loops.
-/

namespace PagingWithDelay

namespace PMD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage IsRest IsFrac
  restMass)

noncomputable section

variable (input : Instance Page)

/-- The final loop state. -/
def finalSnap : Snap Page := (run input (fuel input) (initialSnap input)).2

/-- The loop state before entry `i` of the log (the final state for `i ≥ log.length`). -/
def snapAt (i : ℕ) : Snap Page :=
  if h : i < (log input).length then ((log input)[i]).1 else finalSnap input

/-- The move of entry `i`. -/
def moveAt {input : Instance Page} (i : ℕ) (h : i < (log input).length) : Move Page :=
  ((log input)[i]).2

/-- The time of entry `i`: the time after its move. -/
def entryTime (i : ℕ) : ℝ := (snapAt input (i + 1)).now

/-- The state outside the current preemptive service: the state the hole was opened from, or the current state. -/
def baseState (s : Snap Page) : Page → ℝ :=
  match s.stage with
  | .preempt _ base => base
  | _ => s.x

variable {input}

theorem snapAt_eq_runSnap (i : ℕ) :
    snapAt input i = runSnap input (fuel input) (initialSnap input) i := rfl

theorem snapAt_of_ge {i : ℕ} (hi : (log input).length ≤ i) :
    snapAt input i = finalSnap input := by
  unfold snapAt; rw [dif_neg (by omega)]

theorem baseState_eq_baseOf (s : Snap Page) : baseState s = baseOf s := rfl

theorem baseState_of_preempt' {s : Snap Page} {e : ℤ} {b : Page → ℝ}
    (hs : s.stage = .preempt e b) : baseState s = b := by
  simp [baseState, hs]

theorem baseState_of_not_preempt {s : Snap Page} (hs : ∀ e b, s.stage ≠ .preempt e b) :
    baseState s = s.x :=
  baseOf_of_not_preempt hs

section

variable (hv : input.Valid)
include hv

/-! ### The chain of moves -/

theorem snapAt_zero : snapAt input 0 = initialSnap input := by
  rw [snapAt_eq_runSnap]; exact runSnap_zero _ _

theorem next_snapAt (i : ℕ) (h : i < (log input).length) :
    next input (snapAt input i) = some (moveAt i h, snapAt input (i + 1)) := by
  rw [snapAt_eq_runSnap, snapAt_eq_runSnap]
  exact next_runSnap _ _ i h

theorem next_final : next input (snapAt input (log input).length) = none := by
  rw [snapAt_of_ge le_rfl]; exact next_run_initial hv

theorem inv_snapAt (i : ℕ) : Inv input (snapAt input i) := by
  induction i with
  | zero => rw [snapAt_zero hv]; exact inv_initial hv
  | succ i ih =>
    by_cases hi : i < (log input).length
    · exact (ih.step hv (next_snapAt hv i hi)).1
    · rw [snapAt_of_ge (by omega)]; rw [snapAt_of_ge (by omega)] at ih; exact ih

theorem started_succ {i : ℕ} (hi : i < (log input).length) :
    Started input (snapAt input (i + 1)) :=
  ((inv_snapAt hv i).step hv (next_snapAt hv i hi)).2.1

theorem started_of_pos {i : ℕ} (hi : i ≤ (log input).length) (h0 : 0 < i) :
    Started input (snapAt input i) := by
  have := started_succ hv (i := i - 1) (by omega)
  rwa [show i - 1 + 1 = i by omega] at this

theorem now_succ (i : ℕ) : (snapAt input i).now ≤ (snapAt input (i + 1)).now := by
  by_cases hi : i < (log input).length
  · exact ((inv_snapAt hv i).next_now hv (next_snapAt hv i hi)).1
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

/-- At the end, all arrival times are processed, nothing is pending, the loop is idle, and `eq:trigger` holds for no page from now on. -/
theorem final_spec :
    (snapAt input (log input).length).upcoming = [] ∧
      (snapAt input (log input).length).pending = [] ∧
      (snapAt input (log input).length).stage = .idle ∧
      triggerTimes input (snapAt input (log input).length) = ∅ := by
  have hn := next_eq_none (next_final hv)
  have hinv := inv_snapAt hv (log input).length
  refine ⟨hn.2.2.2, ?_, hn.1, Set.not_nonempty_iff_eq_empty.mp hn.2.2.1⟩
  rw [List.eq_nil_iff_forall_not_mem]
  intro ρ hρ
  exact hn.2.2.1 (triggerTimes_nonempty_of_valid hv (fun π hπ => (hinv.pend π hπ).1)
    (fun π hπ => (hinv.pend π hπ).2.1) hρ)

/-! ### Times -/

theorem now_mono {i j : ℕ} (hij : i ≤ j) : (snapAt input i).now ≤ (snapAt input j).now := by
  exact monotone_nat_of_le_succ (f := fun i => (snapAt input i).now) (now_succ hv) hij

theorem entryTime_mono {i j : ℕ} (hij : i ≤ j) : entryTime input i ≤ entryTime input j :=
  now_mono hv (by omega)

theorem now_le_entryTime (i : ℕ) : (snapAt input i).now ≤ entryTime input i :=
  now_succ hv i

theorem upcoming_pairwise (i : ℕ) : (snapAt input i).upcoming.Pairwise (· < ·) :=
  (inv_snapAt hv i).upcoming_pairwise

theorem now_le_upcoming (i : ℕ) {a : ℝ} (ha : a ∈ (snapAt input i).upcoming) :
    (snapAt input i).now ≤ a :=
  (inv_snapAt hv i).now_le_upcoming ha

/-- After the first move, all upcoming arrival times are strictly later than now. -/
theorem now_lt_upcoming {i : ℕ} (hi : i ≤ (log input).length) (h0 : 0 < i) {a : ℝ}
    (ha : a ∈ (snapAt input i).upcoming) : (snapAt input i).now < a :=
  started_of_pos hv hi h0 a ha

/-- A tick at `t` precedes all entries at time `t`: every entry before it has time `< t`. -/
theorem entryTime_lt_of_tick {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) {j : ℕ} (hj : j < i) : entryTime input j < t := by
  have hst := started_of_pos hv h.le (by omega)
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  have hn := ((inv_snapAt hv i).next_now hv hnext).2.2.1 t rfl
  have h1 := hn.2.2 hst
  have h2 := now_mono hv (i := j + 1) (j := i) (by omega)
  unfold entryTime
  linarith

theorem entryTime_tick {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) : entryTime input i = t := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact (((inv_snapAt hv i).next_now hv hnext).2.2.1 t rfl).1

theorem entryTime_advance {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .advance t) : entryTime input i = t ∧ (snapAt input i).now < t := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  have := ((inv_snapAt hv i).next_now hv hnext).2.2.2 t rfl
  exact ⟨this.1, this.2.2⟩

/-- Moves other than ticks and advances happen at the current time. -/
theorem entryTime_of_not_tick {i : ℕ} (h : i < (log input).length)
    (hm : ∀ t, moveAt i h ≠ .tick t) (ha : ∀ t, moveAt i h ≠ .advance t) :
    entryTime input i = (snapAt input i).now := by
  exact (((inv_snapAt hv i).next_now hv (next_snapAt hv i h)).2.1 hm ha).1

theorem upcoming_succ_of_not_tick {i : ℕ} (h : i < (log input).length)
    (hm : ∀ t, moveAt i h ≠ .tick t) :
    (snapAt input (i + 1)).upcoming = (snapAt input i).upcoming := by
  by_cases ha : ∃ t, moveAt i h = .advance t
  · obtain ⟨t, ht⟩ := ha
    have hnext := next_snapAt hv i h
    rw [ht] at hnext
    exact (((inv_snapAt hv i).next_now hv hnext).2.2.2 t rfl).2.1
  · push_neg at ha
    exact (((inv_snapAt hv i).next_now hv (next_snapAt hv i h)).2.1 hm ha).2

/-- Every arrival time is ticked. -/
theorem exists_tick_arrival {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ i, ∃ h : i < (log input).length, moveAt i h = .tick ρ.arrival := by
  have key : ∀ n, ρ.arrival ∉ (snapAt input n).upcoming →
      ∃ i, ∃ h : i < (log input).length, moveAt i h = .tick ρ.arrival := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [snapAt_zero hv] at hn
      exact absurd (arrival_mem_arrivalTimes hρ) hn
    | succ n ih =>
      intro hn
      by_cases hmem : ρ.arrival ∈ (snapAt input n).upcoming
      · by_cases hlt : n < (log input).length
        · by_cases htick : ∃ t, moveAt n hlt = .tick t
          · obtain ⟨t, ht⟩ := htick
            have hnext := next_snapAt hv n hlt
            rw [ht] at hnext
            have hup := (((inv_snapAt hv n).next_now hv hnext).2.2.1 t rfl).2.1
            rw [hup] at hmem
            rcases List.mem_cons.mp hmem with h1 | h1
            · exact ⟨n, hlt, by rw [ht, h1]⟩
            · exact absurd h1 hn
          · push_neg at htick
            rw [upcoming_succ_of_not_tick hv hlt htick] at hn
            exact absurd hmem hn
        · rw [snapAt_of_ge (by omega)] at hn hmem
          exact absurd hmem hn
      · exact ih hmem
  apply key (log input).length
  rw [(final_spec hv).1]
  simp

/-- Between two moves, `eq:trigger` holds for no page: at a tick or an advance at entry `i`, it holds for no page (w.r.t. `snapAt i`) at any time in `[now, entryTime i)`. -/
theorem not_triggered_before {i : ℕ} (h : i < (log input).length)
    (hm : (∃ t, moveAt i h = .tick t) ∨ (∃ t, moveAt i h = .advance t)) {τ : ℝ}
    (hτ1 : (snapAt input i).now ≤ τ) (hτ2 : τ < entryTime input i) (p : Page) :
    ¬ TriggerCond input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims τ p := by
  intro hp
  have hmem : τ ∈ triggerTimes input (snapAt input i) := ⟨hτ1, p, hp⟩
  have hle := sInf_triggerTimes_le hmem
  have hnext := next_snapAt hv i h
  rcases hm with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at hnext
    obtain ⟨-, -, hnadv, hup, -⟩ := next_tick hnext
    rw [entryTime_tick hv h ht] at hτ2
    apply hnadv
    refine ⟨⟨τ, hmem⟩, ?_⟩
    rw [hup]
    intro a ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha
    by_contra hc
    push_neg at hc
    linarith
  · rw [ht] at hnext
    obtain ⟨-, -, -, ht', -⟩ := next_advance hnext
    rw [(entryTime_advance hv h ht).1, ht'] at hτ2
    linarith

/-! ### Pending requests -/

/-- Pending requests are requests of the input that have arrived (their arrival time has been ticked). -/
theorem pending_spec {i : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input i).pending) :
    ρ ∈ input.requests ∧ ρ.arrival ≤ (snapAt input i).now ∧
      ρ.arrival ∉ (snapAt input i).upcoming :=
  (inv_snapAt hv i).pend ρ hρ

/-- The key monotonicity: a request pending before entry `j` that had arrived by the time of an earlier entry `i` was already pending after entry `i`. -/
theorem pending_of_later {i j : ℕ} (hij : i < j) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input j).pending) (ha : ρ.arrival ≤ entryTime input i) :
    ρ ∈ (snapAt input (i + 1)).pending := by
  by_contra hnot
  have key : ∀ n, i + 1 ≤ n → ρ ∉ (snapAt input n).pending := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hnot
    | succ n hn ih =>
      intro hmem
      by_cases hlt : n < (log input).length
      · have hnext := next_snapAt hv n hlt
        obtain ⟨hm, -⟩ := next_pending_new hnext hmem ih
        rw [hm] at hnext
        have hN := ((inv_snapAt hv n).next_now hv hnext).2.2.1 _ rfl
        have hst := started_of_pos hv hlt.le (by omega)
        have h1 := hN.2.2 hst
        have h2 := now_mono hv (i := i + 1) (j := n) hn
        unfold entryTime at ha
        linarith
      · rw [snapAt_of_ge (by omega)] at hmem ih
        exact ih hmem
  exact key j (by omega) hρ

/-- A request enters the pending list only at the tick at its arrival time. -/
theorem pending_new {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (h1 : ρ ∈ (snapAt input (i + 1)).pending) (h0 : ρ ∉ (snapAt input i).pending) :
    moveAt i h = .tick ρ.arrival ∧ ρ ∈ input.requests :=
  next_pending_new (next_snapAt hv i h) h1 h0

open scoped InstanceNotation in
/-- Part of `lem:inv`: every pending request is on a page with base missing mass `> δ`. -/
theorem delta_lt_baseState_of_pending {i : ℕ} {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) : δ < baseState (snapAt input i) ρ.page :=
  (inv_snapAt hv i).pend_delta ρ hρ

/-! ### States and budgets (`lem:inv`(a)) -/

theorem baseState_isRest (i : ℕ) : IsRest input (baseState (snapAt input i)) := by
  rw [baseState_eq_baseOf]; exact (inv_snapAt hv i).rest

theorem x_eq_baseState {i : ℕ} (hs : ∀ e b, (snapAt input i).stage ≠ .preempt e b) :
    (snapAt input i).x = baseState (snapAt input i) := by
  rw [baseState_eq_baseOf, baseOf_of_not_preempt hs]

open scoped InstanceNotation in
theorem x_eq_hole {i : ℕ} {e : ℤ} {b : Page → ℝ} (hs : (snapAt input i).stage = .preempt e b) :
    (snapAt input i).x = hole input b e ∧
      1 - δ ≤
        ∑ j ∈ Finset.univ.filter (fun j => level input j ≤ e), (1 - b j) := by
  exact (inv_snapAt hv i).preempt e b hs

/-- The current state is at least the base state (`obs:monotone`: opening a hole only increases missing masses). -/
theorem baseState_le_x (i : ℕ) (q : Page) :
    baseState (snapAt input i) q ≤ (snapAt input i).x q := by
  by_cases hs : ∃ e b, (snapAt input i).stage = .preempt e b
  · obtain ⟨e, b, hs⟩ := hs
    have hb := baseState_isRest hv i
    rw [baseState_of_preempt' hs] at hb ⊢
    rw [(x_eq_hole hv hs).1]
    exact PagingWithDelay.PMD.le_hole hv hb.1 e q
  · push_neg at hs
    rw [x_eq_baseState hv hs]

open scoped InstanceNotation in
/-- Part of `lem:inv`: every pending request is on a page with missing mass `> δ`. -/
theorem delta_lt_of_pending {i : ℕ} {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) : δ < (snapAt input i).x ρ.page :=
  (delta_lt_baseState_of_pending hv hρ).trans_le (baseState_le_x hv i ρ.page)

theorem baseState_succ_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) :
    baseState (snapAt input (i + 1)) = baseState (snapAt input i) := by
  rw [baseState_eq_baseOf, baseState_eq_baseOf]
  exact next_baseOf_of_not_critical (next_snapAt hv i h) hm

/-- `obs:monotone`, one move: the base missing mass of `q` does not decrease, unless the move is a critical service on `q`. -/
theorem baseState_le_succ {i : ℕ} (h : i < (log input).length) {q : Page}
    (hm : moveAt i h ≠ .critical q) :
    baseState (snapAt input i) q ≤ baseState (snapAt input (i + 1)) q :=
  (inv_snapAt hv i).baseOf_le_next hv (next_snapAt hv i h) hm

/-- `obs:monotone`: between two log indices with no critical service on `q` in between, the base missing mass of `q` does not decrease (round trips do not change the base state). -/
theorem baseState_mono {i j : ℕ} (hij : i ≤ j) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), i ≤ l → l < j → moveAt l hl ≠ .critical q) :
    baseState (snapAt input i) q ≤ baseState (snapAt input j) q := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    refine (ih fun l hl h1 h2 => hno l hl h1 (by omega)).trans ?_
    by_cases hlt : j < (log input).length
    · exact baseState_le_succ hv hlt (hno j hlt hj (by omega))
    · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

/-- `obs:monotone` for the current state: between `i` and `j` without a critical service on `q`, the missing mass of `q` at `j` is at least its base missing mass at `i`. -/
theorem baseState_le_x_of_mono {i j : ℕ} (hij : i ≤ j) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), i ≤ l → l < j → moveAt l hl ≠ .critical q) :
    baseState (snapAt input i) q ≤ (snapAt input j).x q :=
  (baseState_mono hv hij hno).trans (baseState_le_x hv j q)

theorem budget_nonneg (i : ℕ) (e : ℤ) : 0 ≤ (snapAt input i).budget e := by
  exact (inv_snapAt hv i).budget e

theorem claims_nonneg (i : ℕ) (q : Page) : 0 ≤ (snapAt input i).claims q :=
  (inv_snapAt hv i).claims q

/-! ### Semantics of the moves -/

open scoped InstanceNotation in
theorem tick_spec {i : ℕ} (h : i < (log input).length) {t : ℝ} (hm : moveAt i h = .tick t) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = none ∧
    ¬ AdvanceCond input (snapAt input i) ∧
    (snapAt input i).upcoming = t :: (snapAt input (i + 1)).upcoming ∧
    (snapAt input (i + 1)) = { snapAt input i with
      now := t
      upcoming := (snapAt input i).upcoming.tail
      pending := ((snapAt input i).pending ++
          input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
        fun ρ => decide ((snapAt input i).x ρ.page ≠ δ) } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨hst, hn, ha, hup, heq⟩ := next_tick hnext
  refine ⟨hst, hn, ha, ?_, heq⟩
  rw [heq]; exact hup

theorem advance_spec {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .advance t) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = none ∧
    AdvanceCond input (snapAt input i) ∧ t = sInf (triggerTimes input (snapAt input i)) ∧
    (∃ p, Critical input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims
      t p) ∧ (snapAt input i).now < t ∧
    (snapAt input (i + 1)) = { snapAt input i with now := t } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨hst, hn, ha, ht, heq⟩ := next_advance hnext
  have hc := (inv_snapAt hv i).continuous hv
  refine ⟨hst, hn, ha, ht, ht ▸ exists_critical_sInf ha.1,
    ht ▸ now_lt_sInf_triggerTimes hc ha.1 hn, heq⟩

theorem critical_spec {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    (snapAt input i).stage = .idle ∧ triggerPage input (snapAt input i) = some p ∧
    (snapAt input (i + 1)) = { snapAt input i with
      x := criticalState input (snapAt input i).x p
      budget := deposit input (snapAt input i).x p (snapAt input i).budget
      pending := (snapAt input i).pending.filter fun π => decide (π.page ≠ p)
      claims := Function.update (claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p) p 0
      stage := .examine (minLevel input) } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_critical hnext

open scoped InstanceNotation in
/-- The facts behind a critical service on `p`: `p` is critical now (closed form of the trigger), has a pending request, and the state is a rest state with `x_p > δ`. -/
theorem critical_facts {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    Triggered input (snapAt input i).x (snapAt input i).pending (snapAt input i).claims
        (snapAt input i).now p ∧
      (∃ ρ ∈ (snapAt input i).pending, ρ.page = p) ∧
      IsRest input (snapAt input i).x ∧ δ < (snapAt input i).x p ∧
      entryTime input i = (snapAt input i).now := by
  obtain ⟨hst, htp, -⟩ := critical_spec hv h hm
  obtain ⟨ρ, hρ, hρp⟩ := (inv_snapAt hv i).exists_pending_of_triggerPage hv htp
  have hx : (snapAt input i).x = baseState (snapAt input i) :=
    x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb)
  refine ⟨triggerPage_triggered ((inv_snapAt hv i).continuous hv) htp, ⟨ρ, hρ, hρp⟩, ?_, hρp ▸ delta_lt_of_pending hv hρ, ?_⟩
  · rw [hx]; exact baseState_isRest hv i
  · exact entryTime_of_not_tick hv h (by rw [hm]; simp) (by rw [hm]; simp)

theorem skip_spec {i : ℕ} (h : i < (log input).length) {e : ℤ} (hm : moveAt i h = .skip e) :
    (snapAt input i).stage = .examine e ∧
    ¬ preemptCondition input (snapAt input i).x (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with stage := afterLevel input e } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_skip hnext

theorem openHole_spec {i : ℕ} (h : i < (log input).length) {e : ℤ}
    (hm : moveAt i h = .openHole e) :
    (snapAt input i).stage = .examine e ∧
    preemptCondition input (snapAt input i).x (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with
      x := hole input (snapAt input i).x e
      budget := Function.update (snapAt input i).budget e
        ((snapAt input i).budget e - holePayment input e)
      stage := .preempt e (snapAt input i).x } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_openHole hnext

theorem trip_spec {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) :
    (∃ b, (snapAt input i).stage = .preempt e b) ∧
    tripCandidate input (snapAt input i).pending (snapAt input i).now e = some π ∧
    levelWeight e ≤ (snapAt input i).budget e ∧
    (snapAt input (i + 1)) = { snapAt input i with
      budget := Function.update (snapAt input i).budget e
        ((snapAt input i).budget e - tripCost input (snapAt input i).x π.page)
      pending := (snapAt input i).pending.filter fun ρ => decide (ρ.page ≠ π.page)
      claims := Function.update (snapAt input i).claims π.page 0 } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  exact next_trip hnext

theorem closeHole_spec {i : ℕ} (h : i < (log input).length) {e : ℤ}
    {stop : Option (Request Page)} (hm : moveAt i h = .closeHole e stop) :
    ∃ b, (snapAt input i).stage = .preempt e b ∧
    (match stop with
      | none => tripCandidate input (snapAt input i).pending (snapAt input i).now e = none
      | some π => tripCandidate input (snapAt input i).pending (snapAt input i).now e = some π ∧
          (snapAt input i).budget e < levelWeight e) ∧
    (snapAt input (i + 1)) = { snapAt input i with x := b, stage := afterLevel input e } := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨b, h1, h2, h3⟩ := next_closeHole hnext
  refine ⟨b, h1, ?_, h3⟩
  cases stop with
  | none => exact h2
  | some π => exact h2

/-- Only visits (critical services and round trips) change the claims. -/
theorem claims_succ_of_not_visit {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π) :
    (snapAt input (i + 1)).claims = (snapAt input i).claims := by
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · rw [(tick_spec hv h hm).2.2.2.2]
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]
  · exact absurd hm (hc p)
  · rw [(skip_spec hv h hm).2.2]
  · rw [(openHole_spec hv h hm).2.2]
  · exact absurd hm (ht e π)
  · obtain ⟨b, -, -, he⟩ := closeHole_spec hv h hm
    rw [he]

/-- Only critical services, round trips and ticks change the pending list (ticks only add requests). -/
theorem pending_succ_of_not_visit {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π)
    (htk : ∀ t, moveAt i h ≠ .tick t) :
    (snapAt input (i + 1)).pending = (snapAt input i).pending := by
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · exact absurd hm (htk t)
  · rw [(advance_spec hv h hm).2.2.2.2.2.2]
  · exact absurd hm (hc p)
  · rw [(skip_spec hv h hm).2.2]
  · rw [(openHole_spec hv h hm).2.2]
  · exact absurd hm (ht e π)
  · obtain ⟨b, -, -, he⟩ := closeHole_spec hv h hm
    rw [he]

/-! ### Serving requests -/

/-- A request leaves the pending list only by a visit of its page (a critical service on it or a round trip to it); the visit records a waypoint at the current time with `x_p = δ`. -/
theorem pending_removed {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending) (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    (moveAt i h = .critical ρ.page ∨ ∃ e π, moveAt i h = .trip e π ∧ π.page = ρ.page) ∧
      ∃ w ∈ waypoints input (snapAt input i) (moveAt i h),
        w.time = (snapAt input i).now ∧ w.state ρ.page = input.delta :=
  (inv_snapAt hv i).removed hv (next_snapAt hv i h) hρ hρ'

/-- A visit serves all pending requests on its page. -/
theorem pending_succ_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) {ρ : Request Page} :
    ρ ∈ (snapAt input (i + 1)).pending ↔ ρ ∈ (snapAt input i).pending ∧ ρ.page ≠ p := by
  rw [(critical_spec hv h hm).2.2]
  simp

theorem pending_succ_of_trip {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) {ρ : Request Page} :
    ρ ∈ (snapAt input (i + 1)).pending ↔ ρ ∈ (snapAt input i).pending ∧ ρ.page ≠ π.page := by
  rw [(trip_spec hv h hm).2.2.2]
  simp

open scoped InstanceNotation in
/-- A request ticked at entry `i` that does not become pending is served on arrival: its page has `x_p = δ` at the tick's waypoint `(t, x)`. -/
theorem served_on_arrival {i : ℕ} (h : i < (log input).length) {t : ℝ}
    (hm : moveAt i h = .tick t) {ρ : Request Page} (hρ : ρ ∈ input.requests)
    (ha : ρ.arrival = t) (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    (snapAt input i).x ρ.page = δ ∧
      (⟨t, (snapAt input i).x⟩ : Waypoint Page) ∈
        waypoints input (snapAt input i) (moveAt i h) := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext ⊢
  exact next_tick_served hnext hρ ha hρ'

/-- A request leaves the pending list (or is served on arrival) at a waypoint at or after its arrival with `x_p = δ`. -/
theorem served_of_removed {i : ℕ} (h : i < (log input).length) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input i).pending ∨
      (∃ t, moveAt i h = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t))
    (hρ' : ρ ∉ (snapAt input (i + 1)).pending) :
    ∃ w ∈ waypoints input (snapAt input i) (moveAt i h),
      ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta := by
  rcases hρ with hρ | ⟨t, ht, hreq, ha⟩
  · obtain ⟨-, w, hw, hwt, hws⟩ := pending_removed hv h hρ hρ'
    exact ⟨w, hw, hwt ▸ (pending_spec hv hρ).2.1, hws⟩
  · obtain ⟨hx, hw⟩ := served_on_arrival hv h ht hreq ha hρ'
    exact ⟨_, hw, ha.le, hx⟩

/-! ### Structure of preemptive services and level loops -/

theorem lt_length_of_stage {l : ℕ} (hl : (snapAt input l).stage ≠ .idle) :
    l < (log input).length := by
  by_contra hge
  rw [snapAt_of_ge (by omega)] at hl
  have := (final_spec hv).2.2.1
  rw [snapAt_of_ge le_rfl] at this
  exact hl this

/-- Every preemptive service closes: an `openHole e` is followed by round trips of level `e` and then by a `closeHole e`. -/
theorem preempt_block {i : ℕ} (h : i < (log input).length) {e : ℤ}
    (hm : moveAt i h = .openHole e) :
    ∃ j, ∃ hj : j < (log input).length, i < j ∧ (∃ stop, moveAt j hj = .closeHole e stop) ∧
      ∀ l (hl : l < (log input).length), i < l → l < j → ∃ π, moveAt l hl = .trip e π := by
  classical
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨-, -, heq⟩ := next_openHole hnext
  have hst1 : (snapAt input (i + 1)).stage = .preempt e (snapAt input i).x := by rw [heq]
  let P : ℕ → Prop := fun l => i < l ∧
    ∀ hl : l < (log input).length, ∀ π, moveAt l hl ≠ .trip e π
  have hP : ∃ l, P l := ⟨(log input).length, h, fun hl => absurd hl (lt_irrefl _)⟩
  have hj : P (Nat.find hP) := Nat.find_spec hP
  have hmin : ∀ l < Nat.find hP, ¬ P l := fun l hl => Nat.find_min hP hl
  have hstage : ∀ l, i + 1 ≤ l → l ≤ Nat.find hP →
      (snapAt input l).stage = .preempt e (snapAt input i).x := by
    intro l hl1
    induction l, hl1 using Nat.le_induction with
    | base => intro _; exact hst1
    | succ l hl ih =>
      intro hl2
      have hnP := hmin l (by omega)
      simp only [P, not_and, not_forall, not_not] at hnP
      obtain ⟨hl', π, hπ⟩ := hnP (by omega)
      have hs := ih (by omega)
      rcases next_of_preempt hs (next_snapAt hv l hl') with ⟨π', -, hst'⟩ | ⟨stop, hm', -⟩
      · exact hst'
      · rw [hπ] at hm'; cases hm'
  have hjst := hstage (Nat.find hP) hj.1 le_rfl
  have hjlt : Nat.find hP < (log input).length :=
    lt_length_of_stage hv (by rw [hjst]; simp)
  refine ⟨Nat.find hP, hjlt, hj.1, ?_, ?_⟩
  · rcases next_of_preempt hjst (next_snapAt hv _ hjlt) with ⟨π, hm', -⟩ | ⟨stop, hm', -⟩
    · exact absurd hm' (hj.2 hjlt π)
    · exact ⟨stop, hm'⟩
  · intro l hl hil hlj
    have hnP := hmin l hlj
    simp only [P, not_and, not_forall, not_not] at hnP
    obtain ⟨hl', π, hπ⟩ := hnP hil
    exact ⟨π, hπ⟩

/-- Every round trip and close belongs to a preemptive service: going back from it, there are only round trips of the same level until its `openHole`. -/
theorem preempt_start {l : ℕ} (hl : l < (log input).length) {e : ℤ}
    (hm : (∃ π, moveAt l hl = .trip e π) ∨ (∃ stop, moveAt l hl = .closeHole e stop)) :
    ∃ i, ∃ hi : i < (log input).length, i < l ∧ moveAt i hi = .openHole e ∧
      ∀ l' (hl' : l' < (log input).length), i < l' → l' < l → ∃ π, moveAt l' hl' = .trip e π := by
  have key : ∀ l b, l ≤ (log input).length → (snapAt input l).stage = .preempt e b →
      ∃ i, ∃ hi : i < (log input).length, i < l ∧ moveAt i hi = .openHole e ∧
        ∀ l' (hl' : l' < (log input).length), i < l' → l' < l →
          ∃ π, moveAt l' hl' = .trip e π := by
    intro l
    induction l with
    | zero =>
      intro b _ hs
      rw [snapAt_zero hv] at hs
      simp [initialSnap] at hs
    | succ l ih =>
      intro b hl hs
      have hlt : l < (log input).length := by omega
      rcases next_to_preempt (next_snapAt hv l hlt) hs with hm | ⟨π, hm, hs'⟩
      · exact ⟨l, hlt, by omega, hm, fun l' _ h1 h2 => by omega⟩
      · obtain ⟨i, hi, hil, hio, htr⟩ := ih b hlt.le hs'
        refine ⟨i, hi, by omega, hio, fun l' hl' h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
        · exact htr l' hl' h1 h3
        · subst h3; exact ⟨π, hm⟩
  obtain ⟨b, hs⟩ : ∃ b, (snapAt input l).stage = .preempt e b := by
    rcases hm with ⟨π, hπ⟩ | ⟨stop, hst⟩
    · exact (trip_spec hv hl hπ).1
    · obtain ⟨b, hb, -⟩ := closeHole_spec hv hl hst
      exact ⟨b, hb⟩
  exact key l b hl.le hs

/-- No tick, advance or critical service happens at an entry whose stage is not idle. -/
theorem not_idle_moves {l : ℕ} (hl : l < (log input).length)
    (hs : (snapAt input l).stage ≠ .idle) :
    (∀ p, moveAt l hl ≠ .critical p) ∧ (∀ t, moveAt l hl ≠ .tick t) ∧
      (∀ t, moveAt l hl ≠ .advance t) := by
  refine ⟨fun p hp => hs (critical_spec hv hl hp).1, fun t ht => hs (tick_spec hv hl ht).1,
    fun t ht => hs (advance_spec hv hl ht).1⟩

/-- After a level-`e` examination at `l`, the level is dealt with at some `j ≥ l` by a `skip e` or a `closeHole e`, without critical services, ticks or advances. -/
theorem level_done {l : ℕ} {e : ℤ} (hl : (snapAt input l).stage = .examine e) :
    ∃ j, ∃ hj : j < (log input).length, l ≤ j ∧
      (moveAt j hj = .skip e ∨ ∃ stop, moveAt j hj = .closeHole e stop) ∧
      (snapAt input (j + 1)).stage = afterLevel input e ∧
      ∀ l' (hl' : l' < (log input).length), l ≤ l' → l' ≤ j →
        (∀ π, moveAt l' hl' ≠ .critical π) ∧ (∀ t, moveAt l' hl' ≠ .tick t) ∧
          (∀ t, moveAt l' hl' ≠ .advance t) := by
  have hlt : l < (log input).length := lt_length_of_stage hv (by rw [hl]; simp)
  rcases next_of_examine hl (next_snapAt hv l hlt) with ⟨hm, hst⟩ | ⟨hm, hst⟩
  · refine ⟨l, hlt, le_rfl, Or.inl hm, hst, fun l' hl' h1 h2 => ?_⟩
    obtain rfl : l' = l := by omega
    have : moveAt l' hl' = .skip e := hm
    rw [this]; simp
  · obtain ⟨j, hj, hlj, ⟨stop, hjm⟩, htr⟩ := preempt_block hv hlt hm
    have hjst : (snapAt input (j + 1)).stage = afterLevel input e := by
      obtain ⟨b, -, -, heq⟩ := closeHole_spec hv hj hjm
      rw [heq]
    refine ⟨j, hj, hlj.le, Or.inr ⟨stop, hjm⟩, hjst, fun l' hl' h1 h2 => ?_⟩
    rcases (show l' = l ∨ (l < l' ∧ l' < j) ∨ l' = j by omega) with h3 | h3 | h3
    · subst h3
      have : moveAt l' hl' = .openHole e := hm
      rw [this]; simp
    · obtain ⟨π, hπ⟩ := htr l' hl' h3.1 h3.2
      rw [hπ]; simp
    · subst h3
      have : moveAt l' hl' = .closeHole e stop := hjm
      rw [this]; simp

/-- The level loop after a critical service examines every level: each level `e` gets a later `skip e` or `closeHole e`, with no critical service, tick or advance in between. -/
theorem levelLoop_examines {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) {e : ℤ} (he₁ : minLevel input ≤ e)
    (he₂ : e ≤ maxLevel input) :
    ∃ j, ∃ hj : j < (log input).length, i < j ∧
      (moveAt j hj = .skip e ∨ ∃ stop, moveAt j hj = .closeHole e stop) ∧
      ∀ l (hl : l < (log input).length), i < l → l ≤ j →
        (∀ π, moveAt l hl ≠ .critical π) ∧ (∀ t, moveAt l hl ≠ .tick t) ∧
          (∀ t, moveAt l hl ≠ .advance t) := by
  have hnext := next_snapAt hv i h
  rw [hm] at hnext
  obtain ⟨-, -, heq⟩ := next_critical hnext
  have hst1 : (snapAt input (i + 1)).stage = .examine (minLevel input) := by rw [heq]
  have key : ∀ e, minLevel input ≤ e → e ≤ maxLevel input →
      ∃ l, i < l ∧ (snapAt input l).stage = .examine e ∧
        ∀ l' (hl' : l' < (log input).length), i < l' → l' < l →
          (∀ π, moveAt l' hl' ≠ .critical π) ∧ (∀ t, moveAt l' hl' ≠ .tick t) ∧
            (∀ t, moveAt l' hl' ≠ .advance t) := by
    intro e he1
    induction e, he1 using Int.le_induction with
    | base => intro _; exact ⟨i + 1, by omega, hst1, fun l' _ h1 h2 => by omega⟩
    | succ e he ih =>
      intro he2
      obtain ⟨l, hil, hl, hq⟩ := ih (by omega)
      obtain ⟨j, hj, hlj, -, hjst, hq'⟩ := level_done hv hl
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [hjst]; simp [afterLevel, show e < maxLevel input by omega]
      · intro l' hl' h1 h2
        by_cases h3 : l' < l
        · exact hq l' hl' h1 h3
        · exact hq' l' hl' (by omega) (by omega)
  obtain ⟨l, hil, hl, hq⟩ := key e he₁ he₂
  obtain ⟨j, hj, hlj, hjm, -, hq'⟩ := level_done hv hl
  refine ⟨j, hj, by omega, hjm, fun l' hl' h1 h2 => ?_⟩
  by_cases h3 : l' < l
  · exact hq l' hl' h1 h3
  · exact hq' l' hl' (by omega) h2

end

end

end PMD

end PagingWithDelay
