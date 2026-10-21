import PagingWithDelay.Algorithm
import PagingWithDelay.Basic
import PagingWithDelay.Run.SortedTimes

/-!
# `PMD` for paging with delay is online

A self-contained simulation argument (with the facts about sorted lists of times of `Run/SortedTimes.lean`).

* **Termination.** The measure `meas` strictly decreases along a run: ticks consume an arrival time, critical services and round trips remove a pending request (`eq:trigger` forces `o_p > 0`, hence a pending request on `p`, as `c_p ≥ 0`), the level loop decreases the rank of the stage, and an `advance` is always followed by a critical service (with finitely many pages, some page is critical at the infimum of the trigger times). The initial measure is below `fuel`, so the run stops before fuel runs out and the output does not depend on the amount of fuel (`run_indep`).
* **Simulation.** Two runs on instances that agree up to time `t` make the same moves while `now ≤ t`; once one would move past `t` (an advance to a trigger time `> t`, or a tick at an arrival `> t`), both record only waypoints after `t`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage)

noncomputable section

namespace OnlineProof

/-! ### Instances with the same weights, cache size and initial cache -/

/-- Two instances with the same weights, cache size and initial cache. -/
def Same (I1 I2 : Instance Page) : Prop :=
  I1.weight = I2.weight ∧ I1.cacheSize = I2.cacheSize ∧ I1.initialCache = I2.initialCache

variable {I1 I2 : Instance Page}

theorem Same.eq (h : Same I1 I2) : I1 = { I2 with requests := I1.requests } := by
  obtain ⟨w, hw, k, hk, hkn, C, hC, r⟩ := I1
  obtain ⟨w', hw', k', hk', hkn', C', hC', r'⟩ := I2
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem Same.criticalState (h : Same I1 I2) :
    (criticalState I1 : (Page → ℝ) → Page → Page → ℝ) = criticalState I2 := by rw [h.eq]; rfl
theorem Same.minLevel (h : Same I1 I2) : minLevel I1 = minLevel I2 := by rw [h.eq]; rfl
theorem Same.hole (h : Same I1 I2) : (hole I1 : (Page → ℝ) → ℤ → Page → ℝ) = hole I2 := by
  rw [h.eq]; rfl
theorem Same.holePayment (h : Same I1 I2) : (holePayment I1 : ℤ → ℝ) = holePayment I2 := by
  rw [h.eq]; rfl
theorem Same.preemptCondition (h : Same I1 I2) :
    (preemptCondition I1 : (Page → ℝ) → (ℤ → ℝ) → ℤ → Prop) = preemptCondition I2 := by
  rw [h.eq]; rfl
theorem Same.afterLevel (h : Same I1 I2) : (afterLevel I1 : ℤ → Stage Page) = afterLevel I2 := by
  rw [h.eq]; rfl
theorem Same.tripCost (h : Same I1 I2) : (tripCost I1 : (Page → ℝ) → Page → ℝ) = tripCost I2 := by
  rw [h.eq]; rfl
theorem Same.initialState (h : Same I1 I2) : (initialState I1 : Page → ℝ) = initialState I2 := by
  rw [h.eq]; rfl
theorem Same.delta (h : Same I1 I2) : I1.delta = I2.delta := by rw [h.eq]; rfl
theorem Same.triggerPage (h : Same I1 I2) :
    (triggerPage I1 : Snap Page → Option Page) = triggerPage I2 := by rw [h.eq]; rfl
theorem Same.triggerTimes (h : Same I1 I2) :
    (triggerTimes I1 : Snap Page → Set ℝ) = triggerTimes I2 := by rw [h.eq]; rfl
theorem Same.claimUpdate (h : Same I1 I2) :
    (claimUpdate I1 : (Page → ℝ) → List (Request Page) → (Page → ℝ) → ℝ → Page → Page → ℝ) =
      claimUpdate I2 := by rw [h.eq]; rfl
theorem Same.deposit (h : Same I1 I2) :
    (deposit I1 : (Page → ℝ) → Page → (ℤ → ℝ) → ℤ → ℝ) = deposit I2 := by rw [h.eq]; rfl
theorem Same.tripCandidate (h : Same I1 I2) :
    (tripCandidate I1 : List (Request Page) → ℝ → ℤ → Option (Request Page)) =
      tripCandidate I2 := by rw [h.eq]; rfl

/-! ### The moves of `next` -/

section Moves

variable (input : Instance Page) {s : Snap Page}

theorem next_critical {q : Page} (hst : s.stage = .idle) (htp : triggerPage input s = some q) :
    next input s = some (.critical q,
      { s with
        x := criticalState input s.x q
        budget := deposit input s.x q s.budget
        pending := s.pending.filter fun π => decide (π.page ≠ q)
        claims := Function.update (claimUpdate input s.x s.pending s.claims s.now q) q 0
        stage := .examine (minLevel input) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, htp]

theorem next_advance (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : (triggerTimes input s).Nonempty ∧ ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a) :
    next input s = some (.advance (sInf (triggerTimes input s)),
      { s with now := sInf (triggerTimes input s) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, htp]
  rw [if_pos hc]

open scoped InstanceNotation in
theorem next_tick {a : ℝ} {r : List ℝ} (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a))
    (hup : s.upcoming = a :: r) :
    next input s = some (.tick a,
      { s with
        now := a
        upcoming := r
        pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a)).filter
          fun ρ => decide (s.x ρ.page ≠ δ) }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst hup
  subst hst hup
  simp only [next, htp]
  rw [if_neg hc]

theorem next_none (hst : s.stage = .idle) (htp : triggerPage input s = none)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a))
    (hup : s.upcoming = []) :
    next input s = none := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst hup
  subst hst hup
  simp only [next, htp]
  rw [if_neg hc]

theorem next_openHole {e : ℤ} (hst : s.stage = .examine e)
    (hpc : preemptCondition input s.x s.budget e) :
    next input s = some (.openHole e,
      { s with
        x := hole input s.x e
        budget := Function.update s.budget e (s.budget e - holePayment input e)
        stage := .preempt e s.x }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, if_pos hpc]

theorem next_skip {e : ℤ} (hst : s.stage = .examine e)
    (hpc : ¬ preemptCondition input s.x s.budget e) :
    next input s = some (.skip e, { s with stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, if_neg hpc]

theorem next_closeNone {e : ℤ} {base : Page → ℝ} (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = none) :
    next input s = some (.closeHole e none,
      { s with x := base, stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, htc]

theorem next_trip {e : ℤ} {base : Page → ℝ} {π : Request Page} (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = some π)
    (hcost : levelWeight e ≤ s.budget e) :
    next input s = some (.trip e π,
      { s with
        budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
        pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
        claims := Function.update s.claims π.page 0 }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, htc, if_pos hcost]

theorem next_closeSome {e : ℤ} {base : Page → ℝ} {π : Request Page}
    (hst : s.stage = .preempt e base)
    (htc : tripCandidate input s.pending s.now e = some π)
    (hcost : ¬ levelWeight e ≤ s.budget e) :
    next input s = some (.closeHole e (some π),
      { s with x := base, stage := afterLevel input e }) := by
  obtain ⟨now, up, x, b, p, c, st⟩ := s
  dsimp only at hst
  subst hst
  simp only [next, htc, if_neg hcost]

end Moves

/-! ### The trigger -/

section Trigger

variable (input : Instance Page)

theorem critical_of_triggerPage {s : Snap Page} {q : Page} (h : triggerPage input s = some q) :
    Critical input s.x s.pending s.claims s.now q := by
  have := List.find?_some h
  simpa using this

theorem pageDelay_eq_zero (L : List (Request Page)) (q : Page) (τ : ℝ)
    (h : ∀ ρ ∈ L, ρ.page ≠ q) : pageDelay L q τ = 0 := by
  have : L.filter (fun ρ => decide (ρ.page = q)) = [] :=
    List.filter_eq_nil_iff.mpr fun ρ hρ => by simpa using h ρ hρ
  simp [pageDelay, this]

/-- `eq:trigger` needs a pending request on the page (claims are nonnegative). -/
theorem exists_pending_of_triggerCond (hv : input.Valid) {x : Page → ℝ} {L : List (Request Page)}
    {c : Page → ℝ} {τ : ℝ} {q : Page} (hc : ∀ q, 0 ≤ c q) (h : TriggerCond input x L c τ q) :
    ∃ ρ ∈ L, ρ.page = q := by
  by_contra hne
  push_neg at hne
  have h1 := h.1
  unfold overshoot at h1
  rw [pageDelay_eq_zero L q τ hne] at h1
  have := hv.weight_pos q
  have := hc q
  exact absurd h1 (not_lt.mpr (max_le le_rfl (by linarith)))

/-- A critical page has a pending request. -/
theorem exists_pending_of_critical (hv : input.Valid) {x : Page → ℝ} {L : List (Request Page)}
    {c : Page → ℝ} {τ : ℝ} {q : Page} (hc : ∀ q, 0 ≤ c q) (h : Critical input x L c τ q) :
    ∃ ρ ∈ L, ρ.page = q := by
  obtain ⟨τ', -, -, h'⟩ := h 1 one_pos
  exact exists_pending_of_triggerCond input hv hc h'

theorem not_triggerCond_nil (hv : input.Valid) {x : Page → ℝ} {c : Page → ℝ} {τ : ℝ} {q : Page}
    (hc : ∀ q, 0 ≤ c q) : ¬ TriggerCond input x [] c τ q := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := exists_pending_of_triggerCond input hv hc h
  simp at hρ

theorem not_critical_nil (hv : input.Valid) {x : Page → ℝ} {c : Page → ℝ} {τ : ℝ} {q : Page}
    (hc : ∀ q, 0 ≤ c q) : ¬ Critical input x [] c τ q := by
  intro h
  obtain ⟨ρ, hρ, -⟩ := exists_pending_of_critical input hv hc h
  simp at hρ

/-- Some page is critical at the infimum of the trigger times: with finitely many pages, `eq:trigger` holds for one of them at times arbitrarily close after the infimum. -/
theorem exists_critical_sInf {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    ∃ p, Critical input s.x s.pending s.claims (sInf (triggerTimes input s)) p := by
  have hbdd : BddBelow (triggerTimes input s) := ⟨s.now, fun _ ht => ht.1⟩
  by_contra hno
  push_neg at hno
  have hno' : ∀ p, ∃ ε > 0, ∀ τ, sInf (triggerTimes input s) ≤ τ →
      τ < sInf (triggerTimes input s) + ε → ¬ TriggerCond input s.x s.pending s.claims τ p := by
    intro p
    have := hno p
    unfold Critical at this
    push_neg at this
    exact this
  choose ε hε hε' using hno'
  obtain ⟨t0, -, p0, -⟩ := id hne
  set δ := Finset.univ.inf' ⟨p0, Finset.mem_univ p0⟩ ε with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun p _ => hε p
  obtain ⟨t, htT, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (triggerTimes input s)) hδ)
  obtain ⟨p, hp⟩ := htT.2
  have hle : δ ≤ ε p := Finset.inf'_le ε (Finset.mem_univ p)
  exact hε' p t (csInf_le hbdd htT) (by linarith) hp

/-- After an advance, some page is critical. -/
theorem triggerPage_advance (hv : input.Valid) (s : Snap Page)
    (hs : ∀ ρ ∈ s.pending, ρ ∈ input.requests) (hne : (triggerTimes input s).Nonempty) :
    triggerPage input { s with now := sInf (triggerTimes input s) } ≠ none := by
  obtain ⟨p, hp⟩ := exists_critical_sInf input hne
  unfold triggerPage
  rw [Ne, List.find?_eq_none]
  push_neg
  exact ⟨p, Finset.mem_toList.mpr (Finset.mem_univ _), by simpa using hp⟩

theorem triggerPage_nil (hv : input.Valid) {s : Snap Page} (hc : ∀ q, 0 ≤ s.claims q)
    (h : s.pending = []) : triggerPage input s = none := by
  unfold triggerPage
  rw [List.find?_eq_none]
  intro q _
  rw [h]
  simpa using not_critical_nil input hv hc

theorem triggerTimes_nil (hv : input.Valid) {s : Snap Page} (hc : ∀ q, 0 ≤ s.claims q)
    (h : s.pending = []) : triggerTimes input s = ∅ := by
  ext τ
  simp only [triggerTimes, h, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_exists]
  intro _ q
  exact not_triggerCond_nil input hv hc

theorem now_le_sInf (s : Snap Page) (hne : (triggerTimes input s).Nonempty) :
    s.now ≤ sInf (triggerTimes input s) :=
  le_csInf hne fun _ h => h.1

end Trigger

/-! ### Claims stay nonnegative -/

theorem update_zero_nonneg {f : Page → ℝ} (hf : ∀ q, 0 ≤ f q) (a : Page) :
    ∀ q, 0 ≤ Function.update f a 0 q := by
  intro q
  rw [Function.update_apply]
  split_ifs
  exacts [le_rfl, hf q]

theorem claimUpdate_nonneg (input : Instance Page) (hv : input.Valid) (x : Page → ℝ)
    (L : List (Request Page)) {c : Page → ℝ} (hc : ∀ q, 0 ≤ c q) (τ : ℝ) (p : Page) :
    ∀ q, 0 ≤ claimUpdate input x L c τ p q := by
  intro q
  unfold claimUpdate
  split_ifs
  · have hθ : 0 ≤ claimFraction input x L c τ p :=
      le_min zero_le_one (div_nonneg (div_nonneg (Real.sInf_nonneg fun _ h => h.1)
        (Instance.L_pos hv).le) (Finset.sum_nonneg fun q _ => le_max_left _ _))
    have ho : 0 ≤ overshoot input L c q τ := le_max_left _ _
    nlinarith [hc q]
  · exact hc q

/-! ### Invariants of a single run -/

section Single

variable (input : Instance Page)

/-- The run invariant: times are sorted from `now` on, upcoming times are distinct, pending requests are requests of the instance, claims are nonnegative. -/
structure Inv (s : Snap Page) : Prop where
  sorted : (s.now :: s.upcoming).Pairwise (· ≤ ·)
  nodup : s.upcoming.Nodup
  pending : ∀ ρ ∈ s.pending, ρ ∈ input.requests
  claims : ∀ q, 0 ≤ s.claims q

/-- The weight of one unit of `load`. -/
def K : ℕ := 2 * numLevels input + 4

/-- A rank of the state, decreasing along the level loop; in the idle stage it is `0` iff some page triggers now. -/
def rank (s : Snap Page) : ℕ :=
  match s.stage with
  | .idle => if triggerPage input s = none then 1 else 0
  | .examine e => 2 * (maxLevel input - e).toNat + 3
  | .preempt e _ => 2 * (maxLevel input - e).toNat + 2

/-- Arrival times still to come, requests still to arrive, pending requests. -/
def load (s : Snap Page) : ℕ :=
  s.upcoming.length + (input.requests.filter fun ρ => decide (ρ.arrival ∈ s.upcoming)).length +
    s.pending.length

/-- The termination measure. -/
def meas (s : Snap Page) : ℕ := load input s * K input + rank input s

theorem rank_idle {s : Snap Page} (h : s.stage = .idle) :
    rank input s = if triggerPage input s = none then 1 else 0 := by
  unfold rank; rw [h]

theorem rank_examine {s : Snap Page} {e : ℤ} (h : s.stage = .examine e) :
    rank input s = 2 * (maxLevel input - e).toNat + 3 := by
  unfold rank; rw [h]

theorem rank_preempt {s : Snap Page} {e : ℤ} {b : Page → ℝ} (h : s.stage = .preempt e b) :
    rank input s = 2 * (maxLevel input - e).toNat + 2 := by
  unfold rank; rw [h]

theorem rank_idle_le {s : Snap Page} (h : s.stage = .idle) : rank input s ≤ 1 := by
  rw [rank_idle input h]; split_ifs <;> omega

theorem rank_afterLevel {s : Snap Page} {e : ℤ} (h : s.stage = afterLevel input e) :
    rank input s < 2 * (maxLevel input - e).toNat + 2 := by
  unfold afterLevel at h
  split_ifs at h with he
  · rw [rank_examine input h]; omega
  · have := rank_idle_le input h; omega

theorem rank_minLevel_lt {s : Snap Page} (h : s.stage = .examine (minLevel input)) :
    rank input s < K input := by
  rw [rank_examine input h]
  unfold K numLevels
  omega

theorem count_split (R : List (Request Page)) (t : ℝ) (rest : List ℝ) (ht : t ∉ rest) :
    (R.filter fun ρ => decide (ρ.arrival ∈ t :: rest)).length =
      (R.filter fun ρ => decide (ρ.arrival = t)).length +
        (R.filter fun ρ => decide (ρ.arrival ∈ rest)).length := by
  induction R with
  | nil => simp
  | cons ρ R ih =>
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> (try simp only [List.length_cons]) <;>
      first | omega | (exfalso; simp only [decide_eq_true_eq, List.mem_cons] at *; grind)

theorem next_step (hv : input.Valid) {s s' : Snap Page} {m : Move Page} (hs : Inv input s)
    (hn : next input s = some (m, s')) :
    Inv input s' ∧ s.now ≤ s'.now ∧ (∀ w ∈ waypoints input s m, s.now ≤ w.time ∧ w.time ≤ s'.now) ∧
      meas input s' < meas input s := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  have K4 : 4 ≤ K input := by unfold K; omega
  cases hst : s.stage with
  | idle =>
    cases htp : triggerPage input s with
    | some q =>
      rw [next_critical input hst htp] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      obtain ⟨ρ, hρ, hρq⟩ := exists_pending_of_critical input hv hs4 (critical_of_triggerPage input htp)
      have hlt : (s.pending.filter fun π => decide (π.page ≠ q)).length < s.pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨ρ, hρ, by simp [hρq]⟩
      refine ⟨⟨hs1, hs2, fun π h => hs3 π (List.mem_filter.mp h).1,
        update_zero_nonneg (claimUpdate_nonneg input hv _ _ hs4 _ _) _⟩, le_rfl, ?_, ?_⟩
      · simp [waypoints]
      · have hr := rank_minLevel_lt input (s := { s with
          x := criticalState input s.x q
          budget := deposit input s.x q s.budget
          pending := s.pending.filter fun π => decide (π.page ≠ q)
          claims := Function.update (claimUpdate input s.x s.pending s.claims s.now q) q 0
          stage := .examine (minLevel input) }) rfl
        have h0 : rank input s = 0 := by rw [rank_idle input hst, htp]; simp
        unfold meas load
        dsimp only at hr ⊢
        rw [h0]
        nlinarith
    | none =>
      have h1 : rank input s = 1 := by rw [rank_idle input hst, htp]; simp
      by_cases hc : (triggerTimes input s).Nonempty ∧
          ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a
      · rw [next_advance input hst htp hc] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        have hle := now_le_sInf input s hc.1
        refine ⟨⟨?_, hs2, hs3, hs4⟩, hle, by simp [waypoints, hle], ?_⟩
        · dsimp only
          refine List.Pairwise.cons ?_ (List.Pairwise.of_cons hs1)
          intro b hb
          cases hup : s.upcoming with
          | nil => rw [hup] at hb; simp at hb
          | cons a r =>
            rw [hup] at hb hs1
            have ha := hc.2 a (by simp [hup])
            rcases List.mem_cons.mp hb with rfl | hb
            · exact ha.le
            · exact ha.le.trans ((List.pairwise_cons.mp (List.Pairwise.of_cons hs1)).1 b hb)
        · have h0 : rank input { s with now := sInf (triggerTimes input s) } = 0 := by
            rw [rank_idle input (s := { s with now := sInf (triggerTimes input s) }) hst]
            simp [triggerPage_advance input hv s hs3 hc.1]
          unfold meas load
          dsimp only
          rw [h0, h1]
          omega
      · cases hup : s.upcoming with
        | nil => rw [next_none input hst htp hc hup] at hn; cases hn
        | cons a r =>
          rw [next_tick input hst htp hc hup] at hn
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
          rw [hup] at hs1 hs2
          have ha : a ∉ r := (List.nodup_cons.mp hs2).1
          have hnowa : s.now ≤ a := (List.pairwise_cons.mp hs1).1 a (by simp)
          refine ⟨⟨(List.pairwise_cons.mp hs1).2, (List.nodup_cons.mp hs2).2, ?_, hs4⟩,
            hnowa, ?_, ?_⟩
          · intro π hπ
            rcases List.mem_append.mp (List.mem_filter.mp hπ).1 with h | h
            · exact hs3 π h
            · exact (List.mem_filter.mp h).1
          · simp only [waypoints, List.mem_singleton]
            rintro w rfl
            exact ⟨hnowa, le_rfl⟩
          · have hr := rank_idle_le input (s := { s with
              now := a
              upcoming := r
              pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a)).filter
                fun ρ => decide (s.x ρ.page ≠ input.delta) }) hst
            unfold meas load
            dsimp only at hr ⊢
            rw [hup, h1, count_split _ _ _ ha]
            have := List.length_filter_le (fun ρ => decide (s.x ρ.page ≠ input.delta))
              (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = a))
            rw [List.length_append] at this
            simp only [List.length_cons]
            nlinarith
  | examine e =>
    by_cases hpc : preemptCondition input s.x s.budget e
    · rw [next_openHole input hst hpc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, by simp [waypoints], ?_⟩
      unfold meas load
      dsimp only
      rw [rank_examine input hst, rank_preempt input (s := { s with
        x := hole input s.x e
        budget := Function.update s.budget e (s.budget e - holePayment input e)
        stage := .preempt e s.x }) rfl]
      omega
    · rw [next_skip input hst hpc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, by simp [waypoints], ?_⟩
      have := rank_afterLevel input (s := { s with stage := afterLevel input e }) rfl
      unfold meas load
      dsimp only at this ⊢
      rw [rank_examine input hst]
      omega
  | preempt e b =>
    cases htc : tripCandidate input s.pending s.now e with
    | none =>
      rw [next_closeNone input hst htc] at hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, ?_, ?_⟩
      · simp [waypoints, hst]
      · have := rank_afterLevel input (s := { s with x := b, stage := afterLevel input e }) rfl
        unfold meas load
        dsimp only at this ⊢
        rw [rank_preempt input hst]
        omega
    | some π =>
      have hmem : π ∈ s.pending := (List.mem_filter.mp (List.argmin_mem htc)).1
      by_cases hcost : levelWeight e ≤ s.budget e
      · rw [next_trip input hst htc hcost] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        have hlt : (s.pending.filter fun ρ => decide (ρ.page ≠ π.page)).length <
            s.pending.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨π, hmem, by simp⟩
        refine ⟨⟨hs1, hs2, fun ρ h => hs3 ρ (List.mem_filter.mp h).1,
          update_zero_nonneg hs4 _⟩, le_rfl, ?_, ?_⟩
        · simp [waypoints]
        · unfold meas load
          dsimp only
          rw [rank_preempt input hst, rank_preempt input (s := { s with
            budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
            pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
            claims := Function.update s.claims π.page 0 }) hst]
          nlinarith
      · rw [next_closeSome input hst htc hcost] at hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
        refine ⟨⟨hs1, hs2, hs3, hs4⟩, le_rfl, ?_, ?_⟩
        · simp [waypoints, hst]
        · have := rank_afterLevel input (s := { s with x := b, stage := afterLevel input e }) rfl
          unfold meas load
          dsimp only at this ⊢
          rw [rank_preempt input hst]
          omega

theorem run_indep (hv : input.Valid) : ∀ (n m : ℕ) (s : Snap Page), Inv input s → meas input s < n →
    meas input s < m → run input n s = run input m s := by
  intro n
  induction n with
  | zero => intro m s _ h; omega
  | succ n ih =>
    intro m s hs hn hm
    cases m with
    | zero => omega
    | succ m =>
      simp only [run]
      cases hnx : next input s with
      | none => rfl
      | some pr =>
        obtain ⟨mv, s'⟩ := pr
        obtain ⟨hi, -, -, hme⟩ := next_step input hv hs hnx
        dsimp only
        rw [ih m s' hi (by omega) (by omega)]

/-- The waypoints of a log up to time `t`. -/
def F (t : ℝ) (L : List (Entry Page)) : List (Waypoint Page) :=
  (L.flatMap fun e => waypoints input e.1 e.2).filter fun w => decide (w.time ≤ t)

theorem F_nil (t : ℝ) : F input t ([] : List (Entry Page)) = [] := by simp [F]

theorem F_cons (t : ℝ) (e : Entry Page) (L : List (Entry Page)) :
    F input t (e :: L) = (waypoints input e.1 e.2).filter (fun w => decide (w.time ≤ t)) ++ F input t L := by
  simp [F, List.filter_append]

theorem later (hv : input.Valid) (t : ℝ) :
    ∀ (n : ℕ) (s : Snap Page), Inv input s → t < s.now → F input t (run input n s).1 = [] := by
  intro n
  induction n with
  | zero => intro s _ _; simp [run, F_nil]
  | succ n ih =>
    intro s hs ht
    simp only [run]
    cases hnx : next input s with
    | none => simp [F_nil]
    | some pr =>
      obtain ⟨mv, s'⟩ := pr
      obtain ⟨hi, hle, hw, -⟩ := next_step input hv hs hnx
      dsimp only
      rw [F_cons, ih s' hi (lt_of_lt_of_le ht hle), List.append_nil, List.filter_eq_nil_iff]
      intro w hmem
      have := (hw w hmem).1
      simp only [decide_eq_true_eq, not_le]
      linarith

/-- The run stops, or its next move records only waypoints after `t` and moves `now` past `t`. -/
def Stop (t : ℝ) (s : Snap Page) : Prop :=
  next input s = none ∨
    ∃ m s', next input s = some (m, s') ∧ t < s'.now ∧ ∀ w ∈ waypoints input s m, t < w.time

theorem stop_nil (hv : input.Valid) (t : ℝ) {s : Snap Page} (hs : Inv input s) (h : Stop input t s)
    (n : ℕ) : F input t (run input n s).1 = [] := by
  cases n with
  | zero => simp [run, F_nil]
  | succ n =>
    rcases h with h | ⟨m, s', h, ht, hw⟩
    · simp [run, h, F_nil]
    · simp only [run, h]
      obtain ⟨hi, -, -, -⟩ := next_step input hv hs h
      rw [F_cons, later input hv t n s' hi ht, List.append_nil, List.filter_eq_nil_iff]
      intro w hwm
      simpa using hw w hwm

/-- In the idle stage with no page triggering now, if neither a trigger time nor an arrival time `≤ t` is ahead, the next move happens after `t`. -/
theorem stop_idle (t : ℝ) {s : Snap Page} (hst : s.stage = .idle)
    (htp : triggerPage input s = none) (hup : ∀ a ∈ s.upcoming.head?, t < a)
    (hc : ¬ ((triggerTimes input s).Nonempty ∧ sInf (triggerTimes input s) ≤ t)) : Stop input t s := by
  by_cases hc' : (triggerTimes input s).Nonempty ∧
      ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a
  · right
    have hlt : t < sInf (triggerTimes input s) := by
      by_contra h
      exact hc ⟨hc'.1, not_lt.mp h⟩
    exact ⟨_, _, next_advance input hst htp hc', hlt, by simp [waypoints, hlt]⟩
  · cases hu : s.upcoming with
    | nil => left; exact next_none input hst htp hc' hu
    | cons a r =>
      right
      have ha : t < a := hup a (by simp [hu])
      refine ⟨_, _, next_tick input hst htp hc' hu, ha, ?_⟩
      simp [waypoints, ha]

theorem inv_initial : Inv input (initialSnap input) := by
  have hp : (arrivalTimes input).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hn : (arrivalTimes input).Nodup := Finset.sort_nodup _ _
  refine ⟨?_, hn, by simp [initialSnap], fun _ => le_rfl⟩
  unfold initialSnap
  dsimp only
  generalize arrivalTimes input = l at *
  cases l with
  | nil => simp
  | cons a l =>
    refine List.Pairwise.cons ?_ hp
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_rfl
    · exact (List.pairwise_cons.mp hp).1 b hb

theorem length_arrivalTimes : (arrivalTimes input).length ≤ input.requests.length := by
  unfold arrivalTimes
  rw [Finset.length_sort]
  exact (List.toFinset_card_le _).trans (by simp)

/-- The only property of `fuel` used: it is at least `(2 |requests| + 1) · K`. -/
theorem fuel_ge : (2 * input.requests.length + 1) * K input ≤ fuel input := by
  unfold fuel K
  have := Nat.mul_le_mul_right (2 * numLevels input + 4)
    (show 2 * input.requests.length + 1 ≤ 4 * input.requests.length + 1 by omega)
  omega

theorem meas_initial : meas input (initialSnap input) < fuel input := by
  have hl : load input (initialSnap input) ≤ 2 * input.requests.length := by
    have h1 := length_arrivalTimes input
    have h2 := List.length_filter_le
      (fun ρ : Request Page => decide (ρ.arrival ∈ arrivalTimes input)) input.requests
    unfold load initialSnap
    dsimp only
    simp only [List.length_nil, add_zero]
    omega
  have hr : rank input (initialSnap input) ≤ 1 := rank_idle_le input rfl
  have hf := fuel_ge input
  have K4 : 4 ≤ K input := by unfold K; omega
  have := Nat.mul_le_mul_right (K input) hl
  unfold meas
  nlinarith

end Single

/-! ### Two runs -/

/-- Related snapshots of the runs on two instances that agree up to time `t`. -/
structure Rel (I1 I2 : Instance Page) (t : ℝ) (s1 s2 : Snap Page) : Prop where
  x : s1.x = s2.x
  budget : s1.budget = s2.budget
  pending : s1.pending = s2.pending
  claims : s1.claims = s2.claims
  stage : s1.stage = s2.stage
  up : s1.upcoming.filter (fun a => decide (a ≤ t)) = s2.upcoming.filter (fun a => decide (a ≤ t))
  inv1 : Inv I1 s1
  inv2 : Inv I2 s2
  now : (s1.now = s2.now ∧ s1.now ≤ t) ∨ (s1.pending = [] ∧ s1.stage = .idle)

variable (t : ℝ)

theorem step_sim (hv1 : I1.Valid) (hv2 : I2.Valid) (hS : Same I1 I2)
    (hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a))
    {s1 s2 : Snap Page} (hR : Rel I1 I2 t s1 s2) :
    (Stop I1 t s1 ∧ Stop I2 t s2) ∨
      ∃ m s1' s2', next I1 s1 = some (m, s1') ∧ next I2 s2 = some (m, s2') ∧
        waypoints I1 s1 m = waypoints I2 s2 m ∧ Rel I1 I2 t s1' s2' := by
  obtain ⟨hx, hb, hp, hc, hst, hup, hi1, hi2, hnow⟩ := hR
  cases hst1 : s1.stage with
  | idle =>
    have hst2 : s2.stage = .idle := hst ▸ hst1
    have hsame : (s1.now = s2.now ∧ s1.now ≤ t) ∨ (s1.pending = [] ∧ s2.pending = []) := by
      rcases hnow with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hp ▸ h⟩
    have htp : triggerPage I2 s2 = triggerPage I1 s1 := by
      rcases hsame with ⟨hn, -⟩ | ⟨h1, h2⟩
      · rw [← hS.triggerPage]; simp only [triggerPage, hx, hp, hc, hn]
      · rw [triggerPage_nil I1 hv1 hi1.claims h1, triggerPage_nil I2 hv2 hi2.claims h2]
    have htt : triggerTimes I2 s2 = triggerTimes I1 s1 := by
      rcases hsame with ⟨hn, -⟩ | ⟨h1, h2⟩
      · rw [← hS.triggerTimes]; simp only [triggerTimes, hx, hp, hc, hn]
      · rw [triggerTimes_nil I1 hv1 hi1.claims h1, triggerTimes_nil I2 hv2 hi2.claims h2]
    cases htp1 : triggerPage I1 s1 with
    | some q =>
      have hn : s1.now = s2.now ∧ s1.now ≤ t := by
        rcases hsame with h | ⟨h1, -⟩
        · exact h
        · rw [triggerPage_nil I1 hv1 hi1.claims h1] at htp1; cases htp1
      right
      have e1 := next_critical I1 hst1 htp1
      have e2 := next_critical I2 hst2 (htp.trans htp1)
      refine ⟨_, _, _, e1, e2, ?_, ⟨?_, ?_, ?_, ?_, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hS.criticalState, hx, hn.1]
      · dsimp only; rw [hS.criticalState, hx]
      · dsimp only; rw [hS.deposit, hx, hb]
      · dsimp only; rw [hp]
      · dsimp only; rw [hS.claimUpdate, hx, hp, hc, hn.1]
      · dsimp only; rw [hS.minLevel]
    | none =>
      have htp2 : triggerPage I2 s2 = none := htp.trans htp1
      rcases PagingWithDelay.PMD.OnlineProof.heads t (List.Pairwise.of_cons hi1.sorted)
          (List.Pairwise.of_cons hi2.sorted) hup with
        ⟨h1, h2⟩ | ⟨a, r1, r2, ha, hu1, hu2, hr⟩
      · by_cases hT : (triggerTimes I1 s1).Nonempty ∧ sInf (triggerTimes I1 s1) ≤ t
        · right
          have c1 : (triggerTimes I1 s1).Nonempty ∧
              ∀ a ∈ s1.upcoming.head?, sInf (triggerTimes I1 s1) < a :=
            ⟨hT.1, fun a h => lt_of_le_of_lt hT.2 (h1 a h)⟩
          have c2 : (triggerTimes I2 s2).Nonempty ∧
              ∀ a ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < a := by
            rw [htt]; exact ⟨hT.1, fun a h => lt_of_le_of_lt hT.2 (h2 a h)⟩
          have e1 := next_advance I1 hst1 htp1 c1
          have e2 := next_advance I2 hst2 htp2 c2
          have i2 := (next_step I2 hv2 hi2 e2).1
          rw [htt] at e2 i2
          refine ⟨_, _, _, e1, e2, by simp only [waypoints, hx], ⟨hx, hb, hp, hc, hst, hup,
            (next_step I1 hv1 hi1 e1).1, i2, Or.inl ⟨rfl, hT.2⟩⟩⟩
        · left
          exact ⟨stop_idle I1 t hst1 htp1 h1 hT, stop_idle I2 t hst2 htp2 h2 (htt ▸ hT)⟩
      · right
        by_cases hT : (triggerTimes I1 s1).Nonempty ∧
            ∀ b ∈ s1.upcoming.head?, sInf (triggerTimes I1 s1) < b
        · have c2 : (triggerTimes I2 s2).Nonempty ∧
              ∀ b ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < b := by
            rw [htt, hu2]; rw [hu1] at hT; exact hT
          have hlt : sInf (triggerTimes I1 s1) < a := hT.2 a (by simp [hu1])
          have e1 := next_advance I1 hst1 htp1 hT
          have e2 := next_advance I2 hst2 htp2 c2
          have i2 := (next_step I2 hv2 hi2 e2).1
          rw [htt] at e2 i2
          refine ⟨_, _, _, e1, e2, by simp only [waypoints, hx], ⟨hx, hb, hp, hc, hst, hup,
            (next_step I1 hv1 hi1 e1).1, i2, Or.inl ⟨rfl, hlt.le.trans ha⟩⟩⟩
        · have c2 : ¬ ((triggerTimes I2 s2).Nonempty ∧
              ∀ b ∈ s2.upcoming.head?, sInf (triggerTimes I2 s2) < b) := by
            rw [htt, hu2]; rw [hu1] at hT; exact hT
          have e1 := next_tick I1 hst1 htp1 hT hu1
          have e2 := next_tick I2 hst2 htp2 c2 hu2
          refine ⟨_, _, _, e1, e2, ?_, ⟨hx, hb, ?_, hc, hst, hr,
            (next_step I1 hv1 hi1 e1).1, (next_step I2 hv2 hi2 e2).1, Or.inl ⟨rfl, ha⟩⟩⟩
          · simp only [waypoints, hx]
          · dsimp only; rw [hp, hreq a ha, hx, hS.delta]
  | examine e =>
    have hst2 : s2.stage = .examine e := hst ▸ hst1
    have hn : s1.now = s2.now ∧ s1.now ≤ t := by
      rcases hnow with h | ⟨-, h⟩
      · exact h
      · rw [hst1] at h; cases h
    right
    by_cases hpc : preemptCondition I1 s1.x s1.budget e
    · have hpc2 : preemptCondition I2 s2.x s2.budget e := by
        rw [← hS.preemptCondition, ← hx, ← hb]; exact hpc
      have e1 := next_openHole I1 hst1 hpc
      have e2 := next_openHole I2 hst2 hpc2
      refine ⟨_, _, _, e1, e2, ?_, ⟨?_, ?_, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hS.hole, hx, hn.1]
      · dsimp only; rw [hS.hole, hx]
      · dsimp only; rw [hS.holePayment, hb]
      · dsimp only; rw [hx]
    · have hpc2 : ¬ preemptCondition I2 s2.x s2.budget e := by
        rw [← hS.preemptCondition, ← hx, ← hb]; exact hpc
      have e1 := next_skip I1 hst1 hpc
      have e2 := next_skip I2 hst2 hpc2
      refine ⟨_, _, _, e1, e2, rfl, ⟨hx, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      dsimp only; rw [hS.afterLevel]
  | preempt e b =>
    have hst2 : s2.stage = .preempt e b := hst ▸ hst1
    have hn : s1.now = s2.now ∧ s1.now ≤ t := by
      rcases hnow with h | ⟨-, h⟩
      · exact h
      · rw [hst1] at h; cases h
    right
    have htc : tripCandidate I2 s2.pending s2.now e = tripCandidate I1 s1.pending s1.now e := by
      rw [← hS.tripCandidate, hp, hn.1]
    cases htc1 : tripCandidate I1 s1.pending s1.now e with
    | none =>
      have e1 := next_closeNone I1 hst1 htc1
      have e2 := next_closeNone I2 hst2 (htc.trans htc1)
      refine ⟨_, _, _, e1, e2, ?_, ⟨rfl, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
        (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
      · simp only [waypoints, hst1, hst2, hn.1]
      · dsimp only; rw [hS.afterLevel]
    | some π =>
      by_cases hcost : levelWeight e ≤ s1.budget e
      · have hcost2 : levelWeight e ≤ s2.budget e := by
          rw [← hb]; exact hcost
        have e1 := next_trip I1 hst1 htc1 hcost
        have e2 := next_trip I2 hst2 (htc.trans htc1) hcost2
        refine ⟨_, _, _, e1, e2, ?_, ⟨hx, ?_, ?_, ?_, hst, hup, (next_step I1 hv1 hi1 e1).1,
          (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
        · simp only [waypoints, hS.delta, hx, hn.1]
        · dsimp only; rw [hS.tripCost, hx, hb]
        · dsimp only; rw [hp]
        · dsimp only; rw [hc]
      · have hcost2 : ¬ levelWeight e ≤ s2.budget e := by
          rw [← hb]; exact hcost
        have e1 := next_closeSome I1 hst1 htc1 hcost
        have e2 := next_closeSome I2 hst2 (htc.trans htc1) hcost2
        refine ⟨_, _, _, e1, e2, ?_, ⟨rfl, hb, hp, hc, ?_, hup, (next_step I1 hv1 hi1 e1).1,
          (next_step I2 hv2 hi2 e2).1, Or.inl hn⟩⟩
        · simp only [waypoints, hst1, hst2, hn.1]
        · dsimp only; rw [hS.afterLevel]

theorem sim (hv1 : I1.Valid) (hv2 : I2.Valid) (hS : Same I1 I2)
    (hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a)) :
    ∀ (n : ℕ) (s1 s2 : Snap Page), Rel I1 I2 t s1 s2 →
      F I1 t (run I1 n s1).1 = F I2 t (run I2 n s2).1 := by
  intro n
  induction n with
  | zero => intro s1 s2 _; simp [run, F_nil]
  | succ n ih =>
    intro s1 s2 hR
    rcases step_sim t hv1 hv2 hS hreq hR with ⟨h1, h2⟩ | ⟨m, s1', s2', e1, e2, hw, hR'⟩
    · rw [stop_nil I1 hv1 t hR.inv1 h1, stop_nil I2 hv2 t hR.inv2 h2]
    · simp only [run, e1, e2]
      rw [F_cons, F_cons, ih s1' s2' hR']
      simp only [hw]

theorem mem_arrivalTimes (input : Instance Page) {a : ℝ} (ha : a ≤ t) :
    a ∈ arrivalTimes input ↔
      ∃ ρ ∈ input.requests.filter (fun ρ => decide (ρ.arrival ≤ t)), ρ.arrival = a := by
  simp only [arrivalTimes, Finset.mem_sort, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, ⟨hρ, ha⟩, rfl⟩
  · rintro ⟨ρ, ⟨hρ, -⟩, h⟩
    exact ⟨ρ, hρ, h⟩

theorem arrivalTimes_filter
    (hf : (I1.requests.filter fun ρ => decide (ρ.arrival ≤ t)) =
      I2.requests.filter fun ρ => decide (ρ.arrival ≤ t)) :
    (arrivalTimes I1).filter (fun a => decide (a ≤ t)) =
      (arrivalTimes I2).filter (fun a => decide (a ≤ t)) := by
  have p1 : (arrivalTimes I1).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have p2 : (arrivalTimes I2).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have n1 : (arrivalTimes I1).Nodup := Finset.sort_nodup _ _
  have n2 : (arrivalTimes I2).Nodup := Finset.sort_nodup _ _
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (p1.filter _) (p2.filter _)
  · rw [List.perm_ext_iff_of_nodup (n1.filter _) (n2.filter _)]
    intro a
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨(mem_arrivalTimes t I2 ha).mpr (hf ▸ (mem_arrivalTimes t I1 ha).mp h), ha⟩
    · rintro ⟨h, ha⟩
      exact ⟨(mem_arrivalTimes t I1 ha).mpr (hf ▸ (mem_arrivalTimes t I2 ha).mp h), ha⟩

end OnlineProof

end

open OnlineProof in
/-- **`PMD` is online**: the waypoints up to time `t` depend only on the requests that have arrived by `t`. -/
theorem preemptiveMirrorDescent_online : (preemptiveMirrorDescent : FracAlgorithm Page).Online := by
  intro I1 I2 t h
  have hv1 := I1.valid
  have hv2 := I2.valid
  have hw : (I1.upTo t).weight = (I2.upTo t).weight := congrArg _ h
  have hk : (I1.upTo t).cacheSize = (I2.upTo t).cacheSize := congrArg _ h
  have hC : (I1.upTo t).initialCache = (I2.upTo t).initialCache := congrArg _ h
  have hS : Same I1 I2 := ⟨hw, hk, hC⟩
  have hf : (I1.requests.filter fun ρ => decide (ρ.arrival ≤ t)) =
      I2.requests.filter fun ρ => decide (ρ.arrival ≤ t) := congrArg Instance.requests h
  have hreq : ∀ a ≤ t, (I1.requests.filter fun ρ => decide (ρ.arrival = a)) =
      I2.requests.filter fun ρ => decide (ρ.arrival = a) := by
    intro a ha
    have key : ∀ R : List (Request Page), (R.filter fun ρ => decide (ρ.arrival = a)) =
        (R.filter fun ρ => decide (ρ.arrival ≤ t)).filter fun ρ => decide (ρ.arrival = a) := by
      intro R
      rw [List.filter_filter]
      congr 1
      funext ρ
      by_cases hρ : ρ.arrival = a
      · simp [hρ, ha]
      · simp [hρ]
    rw [key, hf, ← key]
  have hR : Rel I1 I2 t (initialSnap I1) (initialSnap I2) :=
    ⟨by show initialState I1 = initialState I2; rw [hS.initialState], rfl, rfl, rfl, rfl,
      arrivalTimes_filter t hf, inv_initial I1, inv_initial I2, Or.inr ⟨rfl, rfl⟩⟩
  have e1 := run_indep I1 hv1 (fuel I1) (max (fuel I1) (fuel I2)) (initialSnap I1)
    (inv_initial I1) (meas_initial I1) (lt_of_lt_of_le (meas_initial I1) (le_max_left _ _))
  have e2 := run_indep I2 hv2 (fuel I2) (max (fuel I1) (fuel I2)) (initialSnap I2)
    (inv_initial I2) (meas_initial I2) (lt_of_lt_of_le (meas_initial I2) (le_max_right _ _))
  have := sim t hv1 hv2 hS hreq (max (fuel I1) (fuel I2)) _ _ hR
  simp only [F] at this
  simp only [preemptiveMirrorDescent, FracSchedule.upTo, log, e1, e2]
  exact this

end PMD

end PagingWithDelay
