import PagingWithDelay.Run.Step
import PagingWithDelay.Critical.Curve
import PagingWithDelay.Basic

/-!
# The run of the loop: generic chain facts, the invariant, and termination

* `runSnap n s i` is the state before entry `i` of `run n s` (the final state once `i` is past the end); consecutive states are related by `next`.
* `Inv` is the invariant of the loop (`lem:inv`) and `Started` says that the current time lies strictly before all upcoming arrival times (true after the first move).
* `measure` strictly decreases along `next`, which gives termination within `fuel` moves.
-/

open scoped PagingWithDelay.InstanceNotation

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

/-! ### Generic facts about `run` -/

/-- The state before entry `i` of `run n s`. -/
def runSnap (n : ℕ) (s : Snap Page) (i : ℕ) : Snap Page :=
  if h : i < (run input n s).1.length then ((run input n s).1[i]).1 else (run input n s).2

variable {input}

theorem run_succ_of_next {n : ℕ} {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) :
    run input (n + 1) s = ((s, m) :: (run input n s').1, (run input n s').2) := by
  simp [run, h]

theorem run_succ_of_none {n : ℕ} {s : Snap Page} (h : next input s = none) :
    run input (n + 1) s = ([], s) := by
  simp [run, h]

theorem runSnap_zero (n : ℕ) (s : Snap Page) : runSnap input n s 0 = s := by
  cases n with
  | zero => simp [runSnap, run]
  | succ n =>
    cases h : next input s with
    | none => simp [runSnap, run_succ_of_none h]
    | some p =>
      obtain ⟨m, s'⟩ := p
      simp [runSnap, run_succ_of_next h]

theorem runSnap_succ_of_next {n : ℕ} {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) (i : ℕ) :
    runSnap input (n + 1) s (i + 1) = runSnap input n s' i := by
  simp [runSnap, run_succ_of_next h]

theorem next_runSnap : ∀ (n : ℕ) (s : Snap Page) (i : ℕ) (hi : i < (run input n s).1.length),
    next input (runSnap input n s i) =
      some (((run input n s).1[i]).2, runSnap input n s (i + 1)) := by
  intro n
  induction n with
  | zero => intro s i hi; simp [run] at hi
  | succ n ih =>
    intro s i hi
    cases h : next input s with
    | none => simp [run_succ_of_none h] at hi
    | some p =>
      obtain ⟨m, s'⟩ := p
      cases i with
      | zero =>
        rw [runSnap_zero, runSnap_succ_of_next h, runSnap_zero, h]
        simp [run_succ_of_next h]
      | succ i =>
        have hi' : i < (run input n s').1.length := by
          simpa [run_succ_of_next h] using hi
        rw [runSnap_succ_of_next h, runSnap_succ_of_next h, ih s' i hi']
        simp [run_succ_of_next h]

theorem next_run_final (μ : Snap Page → ℕ) (P : Snap Page → Prop)
    (hstep : ∀ s m s', P s → next input s = some (m, s') → P s' ∧ μ s' < μ s) :
    ∀ (n : ℕ) (s : Snap Page), P s → μ s < n → next input (run input n s).2 = none := by
  intro n
  induction n with
  | zero => intro s _ h; omega
  | succ n ih =>
    intro s hs hμ
    cases h : next input s with
    | none => simpa [run_succ_of_none h] using h
    | some p =>
      obtain ⟨m, s'⟩ := p
      obtain ⟨hs', hμ'⟩ := hstep s m s' hs h
      rw [run_succ_of_next h]
      exact ih s' hs' (by omega)

/-! ### Arrival times -/

theorem arrivalTimes_pairwise : (arrivalTimes input).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort ((input.requests.map Request.arrival).toFinset) (· ≤ ·)
  have h2 := Finset.sort_nodup ((input.requests.map Request.arrival).toFinset) (· ≤ ·)
  exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2

theorem arrival_mem_arrivalTimes {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ρ.arrival ∈ arrivalTimes input := by
  unfold arrivalTimes
  rw [Finset.mem_sort, List.mem_toFinset]
  exact List.mem_map_of_mem hρ

theorem arrivalTimes_length_le : (arrivalTimes input).length ≤ input.requests.length := by
  unfold arrivalTimes
  rw [Finset.length_sort]
  exact (List.toFinset_card_le _).trans (by simp)

/-! ### The invariant -/

/-- The state outside the current preemptive service (same as `baseState`). -/
def baseOf (s : Snap Page) : Page → ℝ :=
  match s.stage with
  | .preempt _ base => base
  | _ => s.x

theorem baseOf_congr {s s' : Snap Page} (h1 : s'.stage = s.stage) (h2 : s'.x = s.x) :
    baseOf s' = baseOf s := by
  unfold baseOf; rw [h1, h2]

theorem baseOf_of_not_preempt {s : Snap Page} (hs : ∀ e b, s.stage ≠ .preempt e b) :
    baseOf s = s.x := by
  unfold baseOf
  split
  · rename_i e b h; exact absurd h (hs e b)
  · rfl

theorem afterLevel_ne_preempt (e e' : ℤ) (b : Page → ℝ) :
    afterLevel input e ≠ (.preempt e' b : Stage Page) := by
  unfold afterLevel; split_ifs <;> simp

/-- The current time lies strictly before all upcoming arrival times (true after the first move). -/
def Started (input : Instance Page) (s : Snap Page) : Prop :=
  ∀ a ∈ s.upcoming, s.now < a

/-- The invariant of the loop. -/
structure Inv (input : Instance Page) (s : Snap Page) : Prop where
  upc : ∃ pre, arrivalTimes input = pre ++ s.upcoming
  times : s = initialSnap input ∨ Started input s
  pend : ∀ ρ ∈ s.pending, ρ ∈ input.requests ∧ ρ.arrival ≤ s.now ∧ ρ.arrival ∉ s.upcoming
  pend_delta : ∀ ρ ∈ s.pending, δ < baseOf s ρ.page
  rest : IsRest input (baseOf s)
  preempt : ∀ e b, s.stage = .preempt e b → s.x = hole input b e ∧
    1 - δ ≤ ∑ j ∈ Finset.univ.filter (fun j => level input j ≤ e), (1 - b j)
  budget : ∀ e, 0 ≤ s.budget e
  claims : ∀ q, 0 ≤ s.claims q
  claims_pos : ∀ q, 0 < s.claims q → ∃ ρ ∈ s.pending, ρ.page = q

theorem inv_initial (hv : input.Valid) : Inv input (initialSnap input) where
  upc := ⟨[], rfl⟩
  times := Or.inl rfl
  pend := by simp [initialSnap]
  pend_delta := by simp [initialSnap]
  rest := by
    simpa [baseOf, initialSnap] using
      PagingWithDelay.PMD.initialState_isRest hv
  preempt := by simp [initialSnap]
  budget := by simp [initialSnap]
  claims := by simp [initialSnap]
  claims_pos := by simp [initialSnap]

theorem Inv.upcoming_pairwise {s : Snap Page} (hs : Inv input s) :
    s.upcoming.Pairwise (· < ·) := by
  obtain ⟨pre, hpre⟩ := hs.upc
  have hp := (arrivalTimes_pairwise (input := input))
  rw [hpre] at hp
  exact (List.pairwise_append.mp hp).2.1

theorem Inv.now_le_upcoming {s : Snap Page} (hs : Inv input s) {a : ℝ} (ha : a ∈ s.upcoming) :
    s.now ≤ a := by
  rcases hs.times with h0 | h
  · subst h0
    simp only [initialSnap] at ha ⊢
    have hp := (arrivalTimes_pairwise (input := input))
    cases hA : arrivalTimes input with
    | nil => rw [hA] at ha; simp at ha
    | cons a0 rest =>
      rw [hA] at ha hp
      simp only [List.headD_cons]
      rcases List.mem_cons.mp ha with h1 | h1
      · exact h1.ge
      · exact (List.rel_of_pairwise_cons hp h1).le
  · exact (h a ha).le

theorem Inv.initial_or {s : Snap Page} (hs : Inv input s)
    (hnot : s.stage ≠ .idle ∨ s.pending ≠ []) : Started input s := by
  rcases hs.times with h0 | h
  · subst h0; simp [initialSnap] at hnot
  · exact h

theorem Inv.continuous {s : Snap Page} (hv : input.Valid) (hs : Inv input s) :
    ∀ ρ ∈ s.pending, Continuous ρ.delay :=
  fun ρ hρ => hv.delay_continuous ρ (hs.pend ρ hρ).1

theorem countP_mem_cons (l : List (Request Page)) {t : ℝ} {rest : List ℝ} (ht : t ∉ rest) :
    l.countP (fun ρ => decide (ρ.arrival ∈ t :: rest)) =
      l.countP (fun ρ => decide (ρ.arrival ∈ rest)) +
        (l.filter fun ρ => decide (ρ.arrival = t)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.filter_cons, ih]
    by_cases h1 : a.arrival = t
    · have h2 : a.arrival ∉ rest := h1 ▸ ht
      have e1 : decide (a.arrival ∈ t :: rest) = true := by simp [h1]
      have e2 : decide (a.arrival ∈ rest) = false := by simp [h2]
      have e3 : decide (a.arrival = t) = true := by simp [h1]
      rw [e1, e2, e3]
      simp
      omega
    · have e1 : decide (a.arrival ∈ t :: rest) = decide (a.arrival ∈ rest) := by simp [h1]
      have e3 : decide (a.arrival = t) = false := by simp [h1]
      rw [e1, e3]
      simp only [Bool.false_eq_true, if_false]
      split_ifs <;> omega

/-! ### The measure -/

variable (input) in
/-- A rank of the state, decreasing within a level loop and from an idle state where no page triggers to one where some page does. -/
def rank (s : Snap Page) : ℕ :=
  match s.stage with
  | .idle => if (triggerPage input s).isSome then 0 else 1
  | .examine e => 2 * (maxLevel input - e).toNat + 3
  | .preempt e _ => 2 * (maxLevel input - e).toNat + 2

variable (input) in
/-- The termination measure. -/
def measure (s : Snap Page) : ℕ :=
  (s.upcoming.length + s.pending.length +
      input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming))) *
    (2 * numLevels input + 4) + rank input s

theorem rank_idle_le {s : Snap Page} (hs : s.stage = .idle) : rank input s ≤ 1 := by
  unfold rank; rw [hs]; dsimp only; split_ifs <;> omega

theorem rank_of_afterLevel {s : Snap Page} {e : ℤ} (hs : s.stage = afterLevel input e) :
    rank input s ≤ 2 * (maxLevel input - e).toNat + 1 := by
  unfold afterLevel at hs
  split_ifs at hs with h
  · unfold rank; rw [hs]; simp only; omega
  · have := rank_idle_le (input := input) hs; omega

theorem measure_initial_lt : measure input (initialSnap input) < fuel input := by
  have h1 := List.countP_le_length (p := fun ρ => decide (ρ.arrival ∈ arrivalTimes input))
    (l := input.requests)
  have h2 := arrivalTimes_length_le (input := input)
  have h3 : rank input (initialSnap input) ≤ 1 := rank_idle_le rfl
  simp only [measure, initialSnap, fuel, List.length_nil, add_zero] at h3 ⊢
  have h : ((arrivalTimes input).length +
      input.requests.countP (fun ρ => decide (ρ.arrival ∈ arrivalTimes input))) *
      (2 * numLevels input + 4) ≤
      (4 * input.requests.length) * (2 * numLevels input + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : (4 * input.requests.length + 1) * (2 * numLevels input + 4) =
      4 * input.requests.length * (2 * numLevels input + 4) + (2 * numLevels input + 4) := by ring
  omega

/-! ### Preservation -/

section

variable (hv : input.Valid)
include hv

theorem levelLen_nonneg (x : Page → ℝ) (p : Page) (e : ℤ) : 0 ≤ levelLen input x p e := by
  unfold levelLen
  have hL := Instance.L_pos hv
  have hW := PagingWithDelay.PMD.levelWeight_pos e
  have : L * levelWeight e ≤ 2 * L * levelWeight e := by nlinarith
  have := min_le_min_right (serviceEnd input x p) this
  linarith

theorem deposit_nonneg {x : Page → ℝ} {p : Page} {budget : ℤ → ℝ} (hb : ∀ e, 0 ≤ budget e)
    (e : ℤ) : 0 ≤ deposit input x p budget e := by
  unfold deposit
  split_ifs
  · exact add_nonneg (hb e) (levelLen_nonneg hv x p e)
  · exact hb e

/-- A critical service is on a page with a pending request. -/
theorem Inv.exists_pending_of_triggerPage {s : Snap Page} (hs : Inv input s) {p : Page}
    (hp : triggerPage input s = some p) : ∃ ρ ∈ s.pending, ρ.page = p :=
  exists_pending_of_critical (triggerPage_spec hp) (hs.claims p) (hv.weight_pos p)

theorem Inv.step {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) :
    Inv input s' ∧ Started input s' ∧ measure input s' < measure input s := by
  have hK : 2 * (numLevels input) + 4 =
      2 * (maxLevel input - minLevel input).toNat + 6 := by
    have := PagingWithDelay.PMD.minLevel_le_maxLevel hv
    simp only [numLevels]; omega
  have hvb := hv
  cases m with
  | tick t =>
    obtain ⟨hst, hnone, -, hup, rfl⟩ := next_tick h
    obtain ⟨A, hA⟩ := hs.upc
    have hpw := hs.upcoming_pairwise
    rw [hup] at hpw
    have hnow : s.now ≤ t := hs.now_le_upcoming (by rw [hup]; simp)
    have hnd : t ∉ s.upcoming.tail := fun ht => lt_irrefl t (List.rel_of_pairwise_cons hpw ht)
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hkeep : ∀ ρ ∈ s.pending, ρ ∈ ((s.pending ++ input.requests.filter
        fun ρ => decide (ρ.arrival = t)).filter fun ρ => decide (s.x ρ.page ≠ δ)) := by
      intro ρ hρ
      simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
      have := hs.pend_delta ρ hρ
      rw [hbase] at this
      exact ⟨Or.inl hρ, ne_of_gt this⟩
    have hstart : Started input ({ s with
        now := t
        upcoming := s.upcoming.tail
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) } : Snap Page) := by
      intro a ha
      exact List.rel_of_pairwise_cons hpw ha
    refine ⟨⟨⟨A ++ [t], by rw [hA, hup]; simp⟩, Or.inr hstart, ?_, ?_, ?_, ?_, hs.budget,
      hs.claims, ?_⟩, hstart, ?_⟩
    · intro ρ hρ
      dsimp only at hρ
      simp only [List.mem_filter, List.mem_append, decide_eq_true_eq] at hρ
      rcases hρ.1 with hold | hnew
      · obtain ⟨hreq, ha, hnu⟩ := hs.pend ρ hold
        refine ⟨hreq, ha.trans hnow, fun h' => hnu ?_⟩
        rw [hup]; exact List.mem_cons_of_mem _ h'
      · refine ⟨hnew.1, hnew.2.le, ?_⟩
        dsimp only
        rw [hnew.2]; exact hnd
    · intro ρ hρ
      dsimp only at hρ
      simp only [List.mem_filter, decide_eq_true_eq] at hρ
      show δ < baseOf s ρ.page
      rw [hbase]
      have := (hs.rest.1 ρ.page).1
      rw [hbase] at this
      exact lt_of_le_of_ne this (Ne.symm hρ.2)
    · exact hs.rest
    · intro e b hb; simp [hst] at hb
    · intro q hq
      obtain ⟨ρ, hρ, hρq⟩ := hs.claims_pos q hq
      exact ⟨ρ, hkeep ρ hρ, hρq⟩
    · have hr := rank_idle_le (input := input) hst
      have hr' := rank_idle_le (input := input) (s := { s with
        now := t
        upcoming := s.upcoming.tail
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) }) hst
      simp only [measure]
      have hc1 := countP_mem_cons input.requests hnd
      rw [← hup] at hc1
      have hl : s.upcoming.length = s.upcoming.tail.length + 1 := by
        rw [hup]; simp
      have hf := List.length_filter_le (fun ρ : Request Page => decide (s.x ρ.page ≠ δ))
        (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t))
      rw [List.length_append] at hf
      have key : s.upcoming.tail.length +
          ((s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
            fun ρ => decide (s.x ρ.page ≠ δ)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming.tail)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | advance t =>
    obtain ⟨hst, hnone, hadv, ht, rfl⟩ := next_advance h
    have hc := hs.continuous hv
    have hlt : s.now < t := ht ▸ now_lt_sInf_triggerTimes hc hadv.1 hnone
    have hpw := hs.upcoming_pairwise
    have hstart : Started input ({ s with now := t } : Snap Page) := by
      intro a ha
      cases hup : s.upcoming with
      | nil => rw [hup] at ha; simp at ha
      | cons a0 rest =>
        have h0 : t < a0 := by rw [ht]; exact hadv.2 a0 (by rw [hup]; simp)
        dsimp only at ha
        rw [hup] at ha hpw
        rcases List.mem_cons.mp ha with h1 | h1
        · rw [h1]; exact h0
        · exact h0.trans (List.rel_of_pairwise_cons hpw h1)
    have hb : baseOf ({ s with now := t } : Snap Page) = baseOf s := baseOf_congr rfl rfl
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, ?_, hs.preempt, hs.budget, hs.claims,
      hs.claims_pos⟩, hstart, ?_⟩
    · intro ρ hρ
      obtain ⟨h1, h2, h3⟩ := hs.pend ρ hρ
      exact ⟨h1, h2.trans hlt.le, h3⟩
    · rw [hb]; exact hs.pend_delta
    · rw [hb]; exact hs.rest
    · obtain ⟨p, hp⟩ := triggerPage_advance hc hadv.1
      rw [← ht] at hp
      have h1 : rank input s = 1 := by unfold rank; rw [hst, hnone]; rfl
      have h2 : rank input ({ s with now := t } : Snap Page) = 0 := by
        unfold rank; dsimp only; rw [hp, hst]; rfl
      simp only [measure]
      omega
  | critical p =>
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨ρ, hρ, hρp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hstart := hs.initial_or (Or.inr (List.ne_nil_of_mem hρ))
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hρp ▸ hbase ▸ hs.pend_delta ρ hρ
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hstart, ?_⟩
    · intro π hπ
      simp only [List.mem_filter] at hπ
      exact hs.pend π hπ.1
    · intro π hπ
      simp only [List.mem_filter, decide_eq_true_eq] at hπ
      simp only [baseOf]
      exact (hbase ▸ hs.pend_delta π hπ.1).trans_le
        (PagingWithDelay.PMD.le_criticalState hvb hrest hr hπ.2)
    · simpa [baseOf] using PagingWithDelay.PMD.criticalState_isRest hvb hrest hr
    · intro e b hb; simp at hb
    · exact deposit_nonneg hv hs.budget
    · intro q
      by_cases hq : q = p
      · subst hq; simp
      · simp only [Function.update_of_ne hq]
        exact (hs.claims q).trans (le_claimUpdate hv _ _ _ _ _ _)
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; simp at hq
      · simp only [Function.update_of_ne hqp] at hq
        have hmem : ∀ π ∈ s.pending, π.page = q → π ∈ s.pending.filter
            fun π => decide (π.page ≠ p) := by
          intro π hπ hπq
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hπ, hπq ▸ hqp⟩
        rcases lt_or_ge 0 (s.claims q) with h0 | h0
        · obtain ⟨π, hπ, hπq⟩ := hs.claims_pos q h0
          exact ⟨π, hmem π hπ hπq, hπq⟩
        · have hc0 : s.claims q = 0 := le_antisymm h0 (hs.claims q)
          have h1 := claimUpdate_le (input := input) s.x s.pending s.claims s.now p q
          have hov : 0 < overshoot input s.pending s.claims q s.now := by linarith
          have hpd := overshoot_pos_iff.mp hov
          obtain ⟨π, hπ, hπq⟩ := exists_pending_of_pageDelay_ne (p := q) (t := s.now)
            (by linarith [hv.weight_pos q])
          exact ⟨π, hmem π hπ hπq, hπq⟩
    · have hr0 : rank input s ≤ 1 := rank_idle_le hst
      have hr1 : rank input ({ s with
          x := criticalState input s.x p
          budget := deposit input s.x p s.budget
          pending := s.pending.filter fun π => decide (π.page ≠ p)
          claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
          stage := .examine (minLevel input) } : Snap Page) =
          2 * (maxLevel input - minLevel input).toNat + 3 := rfl
      simp only [measure]
      rw [hr1]
      have hlt : (s.pending.filter fun π => decide (π.page ≠ p)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨ρ, hρ, by simp [hρp]⟩
      have key : s.upcoming.length + (s.pending.filter fun π => decide (π.page ≠ p)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | skip e =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hbase' : baseOf ({ s with stage := afterLevel input e } : Snap Page) = s.x :=
      baseOf_of_not_preempt (by simpa using afterLevel_ne_preempt (input := input) e)
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, hs.budget, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · rw [hbase', ← hbase]; exact hs.pend_delta
    · rw [hbase', ← hbase]; exact hs.rest
    · intro e' b hb; exact absurd hb (afterLevel_ne_preempt e e' b)
    · have := rank_of_afterLevel (input := input)
        (s := { s with stage := afterLevel input e }) rfl
      have h1 : rank input s = 2 * (maxLevel input - e).toNat + 3 := by
        unfold rank; rw [hst]
      simp only [measure]
      omega
  | openHole e =>
    obtain ⟨hst, hcond, rfl⟩ := next_openHole h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, ?_, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · have h1 := hs.pend_delta; rw [hbase] at h1; exact h1
    · have h1 := hs.rest; rw [hbase] at h1; exact h1
    · intro e' b hb
      simp only [Stage.preempt.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨rfl, hcond.2⟩
    · intro e'
      by_cases he : e' = e
      · subst he
        simp only [Function.update_self]
        have h1 : holePayment input e' = levelWeight e' * (1 - δ) := rfl
        have h2 := PagingWithDelay.PMD.levelWeight_pos e'
        have h3 := Instance.delta_pos hv
        have h4 := hcond.1
        nlinarith
      · simp [Function.update_of_ne he, hs.budget e']
    · have h1 : rank input s = 2 * (maxLevel input - e).toNat + 3 := by
        unfold rank; rw [hst]
      have h2 : rank input ({ s with
          x := hole input s.x e
          budget := Function.update s.budget e (s.budget e - holePayment input e)
          stage := .preempt e s.x } : Snap Page) = 2 * (maxLevel input - e).toNat + 2 := rfl
      simp only [measure]
      omega
  | trip e π =>
    obtain ⟨⟨b, hst⟩, hπ, hcost, rfl⟩ := next_trip h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hπmem : π ∈ s.pending := by
      have := List.argmin_mem hπ
      exact (List.mem_filter.mp this).1
    refine ⟨⟨hs.upc, Or.inr hstart, ?_, ?_, hs.rest, hs.preempt, ?_, ?_, ?_⟩, hstart, ?_⟩
    · intro ρ hρ
      exact hs.pend ρ (List.mem_filter.mp hρ).1
    · intro ρ hρ
      exact hs.pend_delta ρ (List.mem_filter.mp hρ).1
    · -- the round trip costs `w_q (x_q - δ) ≤ w_q ≤ W ≤ B_W`
      have htrip : tripCost input s.x π.page ≤ levelWeight e := by
        have hlev : level input π.page ≤ e := by
          simpa using (List.mem_filter.mp (List.argmin_mem hπ)).2
        have hrest : IsRest input b := by
          have := hs.rest; simpa [baseOf, hst] using this
        have h1 := PagingWithDelay.PMD.hole_le_one hvb hrest.1 e π.page
        have hd := Instance.delta_pos hv
        have hw := hv.weight_pos π.page
        have hW := (PagingWithDelay.PMD.level_le_iff hvb π.page e).1 hlev
        unfold tripCost
        rw [(hs.preempt e b hst).1]
        nlinarith
      intro e'
      by_cases he : e' = e
      · subst he; simp; linarith
      · simp [Function.update_of_ne he, hs.budget e']
    · intro q
      by_cases hq : q = π.page
      · subst hq; simp
      · simp only [Function.update_of_ne hq]; exact hs.claims q
    · intro q hq
      by_cases hqp : q = π.page
      · subst hqp; simp at hq
      · simp only [Function.update_of_ne hqp] at hq
        obtain ⟨ρ, hρ, hρq⟩ := hs.claims_pos q hq
        refine ⟨ρ, ?_, hρq⟩
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨hρ, hρq ▸ hqp⟩
    · have h1 : rank input s = 2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; rw [hst]
      have h2 : rank input ({ s with
          budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
          pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
          claims := Function.update s.claims π.page 0 } : Snap Page) =
          2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; simp only; rw [hst]
      simp only [measure]
      rw [h1, h2]
      have hlt : (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨π, hπmem, by simp⟩
      have key : s.upcoming.length + (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) + 1 ≤
          s.upcoming.length + s.pending.length +
          input.requests.countP (fun ρ => decide (ρ.arrival ∈ s.upcoming)) := by omega
      have := Nat.mul_le_mul_right (2 * numLevels input + 4) key
      rw [add_mul] at this
      omega
  | closeHole e stop =>
    obtain ⟨b, hst, -, rfl⟩ := next_closeHole h
    have hstart := hs.initial_or (Or.inl (by simp [hst]))
    have hbase : baseOf s = b := by simp [baseOf, hst]
    have hbase' : baseOf ({ s with x := b, stage := afterLevel input e } : Snap Page) = b :=
      baseOf_of_not_preempt (by simpa using afterLevel_ne_preempt (input := input) e)
    refine ⟨⟨hs.upc, Or.inr hstart, hs.pend, ?_, ?_, ?_, hs.budget, hs.claims, hs.claims_pos⟩,
      hstart, ?_⟩
    · rw [hbase', ← hbase]; exact hs.pend_delta
    · rw [hbase', ← hbase]; exact hs.rest
    · intro e' b' hb; exact absurd hb (afterLevel_ne_preempt e e' b')
    · have := rank_of_afterLevel (input := input)
        (s := { s with x := b, stage := afterLevel input e }) rfl
      have h1 : rank input s = 2 * (maxLevel input - e).toNat + 2 := by
        unfold rank; rw [hst]
      simp only [measure]
      omega

end

/-! ### Consequences of one move -/

theorem Inv.next_now (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) :
    s.now ≤ s'.now ∧
      ((∀ t, m ≠ .tick t) → (∀ t, m ≠ .advance t) →
        s'.now = s.now ∧ s'.upcoming = s.upcoming) ∧
      (∀ t, m = .tick t → s'.now = t ∧ s.upcoming = t :: s'.upcoming ∧
        (Started input s → s.now < t)) ∧
      (∀ t, m = .advance t → s'.now = t ∧ s'.upcoming = s.upcoming ∧ s.now < t) := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, hup, rfl⟩ := next_tick h
    have hnow : s.now ≤ t := hs.now_le_upcoming (by rw [hup]; simp)
    refine ⟨hnow, fun ht' => absurd rfl (ht' t), ?_, fun _ h => by cases h⟩
    rintro t' ⟨⟩
    exact ⟨rfl, hup, fun hst => hst t (by rw [hup]; simp)⟩
  | advance t =>
    obtain ⟨-, hnone, hadv, ht, rfl⟩ := next_advance h
    have hlt : s.now < t := ht ▸ now_lt_sInf_triggerTimes (hs.continuous hv) hadv.1 hnone
    refine ⟨hlt.le, fun _ ha => absurd rfl (ha t), fun _ h => (by cases h), ?_⟩
    rintro t' ⟨⟩
    exact ⟨rfl, rfl, hlt⟩
  | critical ρ =>
    obtain ⟨-, -, rfl⟩ := next_critical h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ h => (by cases h), fun _ h => by cases h⟩

/-- A request enters the pending list only at the tick at its arrival time. -/
theorem next_pending_new {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) {ρ : Request Page}
    (h' : ρ ∈ s'.pending) (hnot : ρ ∉ s.pending) :
    m = .tick ρ.arrival ∧ ρ ∈ input.requests := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_tick h
    simp only [List.mem_filter, List.mem_append, decide_eq_true_eq] at h'
    rcases h'.1 with h1 | h1
    · exact absurd h1 hnot
    · exact ⟨by rw [h1.2], h1.1⟩
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    exact absurd h' hnot
  | critical ρ' =>
    obtain ⟨-, -, rfl⟩ := next_critical h
    exact absurd (List.mem_filter.mp h').1 hnot
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact absurd h' hnot
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact absurd h' hnot
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    exact absurd (List.mem_filter.mp h').1 hnot
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact absurd h' hnot

theorem next_baseOf_of_not_critical {s s' : Snap Page} {m : Move Page}
    (h : next input s = some (m, s')) (hm : ∀ p, m ≠ .critical p) :
    baseOf s' = baseOf s := by
  cases m with
  | tick t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_tick h
    rfl
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    rfl
  | critical p => exact absurd rfl (hm p)
  | skip e =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    rw [baseOf_of_not_preempt (s := s) (by simp [hst])]
    apply baseOf_of_not_preempt
    intro e' b; exact afterLevel_ne_preempt e e' b
  | openHole e =>
    obtain ⟨hst, -, rfl⟩ := next_openHole h
    rw [baseOf_of_not_preempt (s := s) (by simp [hst])]
    rfl
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    rfl
  | closeHole e stop =>
    obtain ⟨b, hst, -, rfl⟩ := next_closeHole h
    have : baseOf s = b := by simp [baseOf, hst]
    rw [this]
    apply baseOf_of_not_preempt
    intro e' b'; exact afterLevel_ne_preempt e e' b'

/-- `obs:monotone`, one move: the base state of a page `q` does not decrease unless the move is a critical service on `q`. -/
theorem Inv.baseOf_le_next (hv : input.Valid) {s s' : Snap Page} {m : Move Page}
    (hs : Inv input s) (h : next input s = some (m, s')) {q : Page} (hm : m ≠ .critical q) :
    baseOf s q ≤ baseOf s' q := by
  by_cases hc : ∃ p, m = .critical p
  · obtain ⟨p, rfl⟩ := hc
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨ρ, hρ, hρp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hρp ▸ hbase ▸ hs.pend_delta ρ hρ
    have hqp : q ≠ p := fun h => hm (h ▸ rfl)
    rw [hbase]
    simp only [baseOf]
    exact PagingWithDelay.PMD.le_criticalState hv hrest hr hqp
  · push_neg at hc
    rw [next_baseOf_of_not_critical h hc]

theorem next_of_preempt {s s' : Snap Page} {m : Move Page} {e : ℤ} {b : Page → ℝ}
    (hs : s.stage = .preempt e b) (h : next input s = some (m, s')) :
    (∃ π, m = .trip e π ∧ s'.stage = .preempt e b) ∨
      (∃ stop, m = .closeHole e stop ∧ s'.stage = afterLevel input e) := by
  cases m with
  | tick t => obtain ⟨hst, -⟩ := next_tick h; simp [hst] at hs
  | advance t => obtain ⟨hst, -⟩ := next_advance h; simp [hst] at hs
  | critical ρ => obtain ⟨hst, -⟩ := next_critical h; simp [hst] at hs
  | skip e => obtain ⟨hst, -⟩ := next_skip h; simp [hst] at hs
  | openHole e => obtain ⟨hst, -⟩ := next_openHole h; simp [hst] at hs
  | trip e' π =>
    obtain ⟨⟨b', hst⟩, -, -, rfl⟩ := next_trip h
    rw [hst] at hs
    simp only [Stage.preempt.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inl ⟨π, rfl, hst⟩
  | closeHole e' stop =>
    obtain ⟨b', hst, -, rfl⟩ := next_closeHole h
    rw [hst] at hs
    simp only [Stage.preempt.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact Or.inr ⟨stop, rfl, rfl⟩

theorem next_of_examine {s s' : Snap Page} {m : Move Page} {e : ℤ}
    (hs : s.stage = .examine e) (h : next input s = some (m, s')) :
    (m = .skip e ∧ s'.stage = afterLevel input e) ∨
      (m = .openHole e ∧ s'.stage = .preempt e s.x) := by
  cases m with
  | tick t => obtain ⟨hst, -⟩ := next_tick h; simp [hst] at hs
  | advance t => obtain ⟨hst, -⟩ := next_advance h; simp [hst] at hs
  | critical ρ => obtain ⟨hst, -⟩ := next_critical h; simp [hst] at hs
  | skip e' =>
    obtain ⟨hst, -, rfl⟩ := next_skip h
    rw [hst] at hs; simp only [Stage.examine.injEq] at hs; subst hs
    exact Or.inl ⟨rfl, rfl⟩
  | openHole e' =>
    obtain ⟨hst, -, rfl⟩ := next_openHole h
    rw [hst] at hs; simp only [Stage.examine.injEq] at hs; subst hs
    exact Or.inr ⟨rfl, rfl⟩
  | trip e' π => obtain ⟨⟨b', hst⟩, -⟩ := next_trip h; simp [hst] at hs
  | closeHole e' stop => obtain ⟨b', hst, -⟩ := next_closeHole h; simp [hst] at hs

theorem next_to_preempt {s s' : Snap Page} {m : Move Page} {e : ℤ} {b : Page → ℝ}
    (h : next input s = some (m, s')) (hs' : s'.stage = .preempt e b) :
    m = .openHole e ∨ (∃ π, m = .trip e π ∧ s.stage = .preempt e b) := by
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_tick h
    simp only at hs'; rw [hst] at hs'; simp at hs'
  | advance t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_advance h
    simp only at hs'; rw [hst] at hs'; simp at hs'
  | critical ρ => obtain ⟨-, -, rfl⟩ := next_critical h; simp at hs'
  | skip e' => obtain ⟨-, -, rfl⟩ := next_skip h; exact absurd hs' (afterLevel_ne_preempt e' e b)
  | openHole e' =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    simp only [Stage.preempt.injEq] at hs'
    rw [hs'.1]; exact Or.inl rfl
  | trip e' π =>
    obtain ⟨⟨b', hst⟩, -, -, rfl⟩ := next_trip h
    simp only at hs'
    rw [hst] at hs' ⊢
    simp only [Stage.preempt.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    exact Or.inr ⟨π, rfl, rfl⟩
  | closeHole e' stop =>
    obtain ⟨b', -, -, rfl⟩ := next_closeHole h
    exact absurd hs' (afterLevel_ne_preempt e' e b)

/-- A request leaves the pending list only by a visit of its page (a critical service on it or a round trip to it), which records a waypoint at the current time with `x_p = δ`. -/
theorem Inv.removed (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (h : next input s = some (m, s')) {ρ : Request Page} (hρ : ρ ∈ s.pending)
    (hρ' : ρ ∉ s'.pending) :
    (m = .critical ρ.page ∨ ∃ e π, m = .trip e π ∧ π.page = ρ.page) ∧
      ∃ v ∈ waypoints input s m, v.time = s.now ∧ v.state ρ.page = δ := by
  have hvb := hv
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, rfl⟩ := next_tick h
    exfalso; apply hρ'
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have := hs.pend_delta ρ hρ
    rw [hbase] at this
    simp only [List.mem_filter, List.mem_append, decide_eq_true_eq]
    exact ⟨Or.inl hρ, ne_of_gt this⟩
  | advance t =>
    obtain ⟨-, -, -, -, rfl⟩ := next_advance h
    exact absurd hρ hρ'
  | critical p =>
    obtain ⟨hst, htp, rfl⟩ := next_critical h
    obtain ⟨π, hπ, hπp⟩ := hs.exists_pending_of_triggerPage hv htp
    have hbase : baseOf s = s.x := baseOf_of_not_preempt (by simp [hst])
    have hrest : IsRest input s.x := hbase ▸ hs.rest
    have hr : δ < s.x p := hπp ▸ hbase ▸ hs.pend_delta π hπ
    simp only [List.mem_filter, decide_eq_true_eq, not_and, not_not] at hρ'
    have hpage := hρ' hρ
    refine ⟨Or.inl (by rw [hpage]), ⟨s.now, criticalState input s.x p⟩,
      by simp [waypoints], rfl, ?_⟩
    simp only
    rw [hpage]
    exact PagingWithDelay.PMD.criticalState_self hvb hrest hr
  | skip e =>
    obtain ⟨-, -, rfl⟩ := next_skip h
    exact absurd hρ hρ'
  | openHole e =>
    obtain ⟨-, -, rfl⟩ := next_openHole h
    exact absurd hρ hρ'
  | trip e π =>
    obtain ⟨-, -, -, rfl⟩ := next_trip h
    simp only [List.mem_filter, decide_eq_true_eq, not_and, not_not] at hρ'
    have hpage := hρ' hρ
    refine ⟨Or.inr ⟨e, π, rfl, hpage.symm⟩, ⟨s.now, Function.update s.x π.page δ⟩,
      by simp [waypoints], rfl, ?_⟩
    simp only
    rw [hpage]
    simp
  | closeHole e stop =>
    obtain ⟨b, -, -, rfl⟩ := next_closeHole h
    exact absurd hρ hρ'

/-- A request arriving at a tick that does not become pending is served on arrival: `x_p = δ` in the tick's waypoint. -/
theorem next_tick_served {s s' : Snap Page} {t : ℝ} (h : next input s = some (.tick t, s'))
    {ρ : Request Page} (hρ : ρ ∈ input.requests) (ha : ρ.arrival = t) (hρ' : ρ ∉ s'.pending) :
    s.x ρ.page = δ ∧ (⟨t, s.x⟩ : Waypoint Page) ∈
      waypoints input s (.tick t) := by
  obtain ⟨-, -, -, -, rfl⟩ := next_tick h
  simp only [List.mem_filter, List.mem_append, decide_eq_true_eq, not_and, not_not] at hρ'
  exact ⟨hρ' (Or.inr ⟨hρ, ha⟩), by simp [waypoints]⟩

section

variable (hv : input.Valid)
include hv

/-- The run from the initial state ends within `fuel` moves. -/
theorem next_run_initial :
    next input (run input (fuel input) (initialSnap input)).2 = none :=
  next_run_final (measure input) (Inv input)
    (fun _ _ _ hs h => ⟨(hs.step hv h).1, (hs.step hv h).2.2⟩)
    (fuel input) (initialSnap input) (inv_initial hv) measure_initial_lt

end

end

end PMD

end PagingWithDelay
