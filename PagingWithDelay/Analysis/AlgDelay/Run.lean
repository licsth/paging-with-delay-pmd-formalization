import PagingWithDelay.Analysis.Defs

/-!
# `prop:algdelay`, part 1: facts about the run

Facts about the log of `PMD` used by the proof of `prop:algdelay` (`PagingWithDelay/Analysis/AlgDelay.lean`):

* `startOf j`: the *start index* of the time of entry `j`, the last tick or advance at or before `j`. All entries from `startOf j` to `j` have the same time.
* Visits (`visitPage`): a visit has a pending request on its page, and no request on its page is pending after it; no page is visited twice at one time.
* Between the start of a time and a visit of `p`, the delay of `p` does not change and the claim of `p` does not decrease.
* `exists_chain`: between two log indices, the base state changes only by critical services, so it is the end of a chain (`chainState`) of them, whose length (`chainLen`) is the sum of the `lenAt` of the entries.
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

/-! ### Chains of critical services -/

theorem chainState_append_single (I : Instance Page) (x : Page → ℝ)
    (ps : List Page) (p : Page) :
    chainState I x (ps ++ [p]) = criticalState I (chainState I x ps) p := by
  induction ps generalizing x with
  | nil => rfl
  | cons a ps ih => simp [ih]

theorem chainLen_append_single (I : Instance Page) (x : Page → ℝ)
    (ps : List Page) (p : Page) :
    chainLen I x (ps ++ [p]) = chainLen I x ps + serviceEnd I (chainState I x ps) p := by
  induction ps generalizing x with
  | nil => simp
  | cons a ps ih => simp [ih]; ring

/-! ### The accounting of single entries -/

theorem lenAt_of_critical {l : ℕ} (h : l < (log input).length) {p : Page}
    (hm : moveAt l h = .critical p) :
    lenAt input l = serviceEnd input (snapAt input l).x p := by
  simp [lenAt, h, hm]

theorem lenAt_of_not_critical {l : ℕ}
    (hm : ∀ (h : l < (log input).length) p, moveAt l h ≠ .critical p) : lenAt input l = 0 := by
  unfold lenAt
  split_ifs with h
  · rcases hc : moveAt l h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp
    exact absurd hc (hm h p)
  · rfl

theorem lenAt_nonneg (l : ℕ) : 0 ≤ lenAt input l := by
  unfold lenAt
  split_ifs with h
  · split
    · exact serviceEnd_nonneg' _ _
    all_goals exact le_rfl
  · exact le_rfl

theorem holeAt_of_openHole {l : ℕ} (h : l < (log input).length) {e : ℤ}
    (hm : moveAt l h = .openHole e) : holeAt input l = holePayment input e := by
  simp [holeAt, h, hm]

theorem holeAt_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ holeAt input l := by
  unfold holeAt
  split_ifs with h
  · split
    · unfold holePayment
      have := Instance.delta_lt_one hv
      apply mul_nonneg (PagingWithDelay.PMD.levelWeight_pos _).le
      linarith
    all_goals exact le_rfl
  · exact le_rfl

/-! ### Visits -/

theorem visitPage_eq_some_iff {j : ℕ} {p : Page} :
    visitPage input j = some p ↔ ∃ h : j < (log input).length,
      moveAt j h = .critical p ∨ ∃ e π, moveAt j h = .trip e π ∧ π.page = p := by
  unfold visitPage
  split_ifs with h
  · rcases hm : moveAt j h with t | t | p' | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp [h, hm, eq_comm]
  · simp [h]

theorem visitPage_of_critical {j : ℕ} (h : j < (log input).length) {p : Page}
    (hm : moveAt j h = .critical p) : visitPage input j = some p :=
  visitPage_eq_some_iff.mpr ⟨h, Or.inl hm⟩

theorem visitPage_of_trip {j : ℕ} (h : j < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt j h = .trip e π) : visitPage input j = some π.page :=
  visitPage_eq_some_iff.mpr ⟨h, Or.inr ⟨e, π, hm, rfl⟩⟩

theorem visitPage_eq_none {j : ℕ} (hn : visitPage input j = none) (h : j < (log input).length) :
    (∀ p, moveAt j h ≠ .critical p) ∧ (∀ e π, moveAt j h ≠ .trip e π) := by
  refine ⟨fun p hp => ?_, fun e π hp => ?_⟩
  · rw [visitPage_of_critical h hp] at hn; cases hn
  · rw [visitPage_of_trip h hp] at hn; cases hn

/-- The fetch cost `w_p (x_p - δ)` of a visit of `p` is its `fetchAt` (critical service) or its `tripAt` (round trip). -/
theorem fetchAt_add_tripAt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    fetchAt input j + tripAt input j = w p * ((snapAt input j).x p - δ) := by
  obtain ⟨h, hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
  · simp [fetchAt, tripAt, h, hm, PagingWithDelay.PMD.criticalFetch]
  · simp [fetchAt, tripAt, h, hm, tripCost]

theorem fetchAt_add_tripAt_of_none {j : ℕ} (hn : visitPage input j = none) :
    fetchAt input j + tripAt input j = 0 := by
  unfold fetchAt tripAt
  split_ifs with h
  · obtain ⟨h1, h2⟩ := visitPage_eq_none hn h
    rcases hm : moveAt j h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩ <;> simp
    · exact absurd hm (h1 p)
    · exact absurd hm (h2 e π)
  · simp

section

variable (hv : input.Valid)
include hv

/-- A visit of `p` has a pending request on `p`. -/
theorem visit_pending {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    ∃ ρ ∈ (snapAt input j).pending, ρ.page = p := by
  obtain ⟨h, hm | ⟨e, π, hm, hπ⟩⟩ := visitPage_eq_some_iff.mp hvis
  · exact (critical_facts hv h hm).2.1
  · obtain ⟨-, hc, -⟩ := trip_spec hv h hm
    unfold tripCandidate at hc
    have := List.argmin_mem hc
    exact ⟨π, (List.mem_filter.mp this).1, hπ⟩

/-- After a visit of `p`, no request on `p` is pending. -/
theorem no_pending_after_visit {l : ℕ} {p : Page} (hvis : visitPage input l = some p)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input (l + 1)).pending) : ρ.page ≠ p := by
  obtain ⟨h, hm | ⟨e, π, hm, rfl⟩⟩ := visitPage_eq_some_iff.mp hvis
  · exact ((pending_succ_of_critical hv h hm).mp hρ).2
  · exact ((pending_succ_of_trip hv h hm).mp hρ).2

/-- Without ticks, the pending list only shrinks. -/
theorem pending_of_no_tick {l m : ℕ} (hlm : l ≤ m)
    (hno : ∀ l' (h : l' < (log input).length), l ≤ l' → l' < m → ∀ t, moveAt l' h ≠ .tick t)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input m).pending) : ρ ∈ (snapAt input l).pending := by
  induction m, hlm using Nat.le_induction generalizing ρ with
  | base => exact hρ
  | succ m hm ih =>
    apply ih (fun l' h h1 h2 => hno l' h h1 (by omega))
    by_contra hnot
    by_cases hlt : m < (log input).length
    · exact hno m hlt hm (by omega) _ (pending_new hv hlt hρ hnot).1
    · rw [snapAt_of_ge (by omega)] at hρ
      rw [snapAt_of_ge (by omega)] at hnot
      exact hnot hρ

end

/-! ### Start indices -/

variable (input) in
/-- Entry `a` is a tick or an advance: the entries after it (until the next one) happen at its time. -/
def IsTA (a : ℕ) : Prop :=
  ∃ h : a < (log input).length, (∃ t, moveAt a h = .tick t) ∨ (∃ t, moveAt a h = .advance t)


variable (input) in
/-- The *start index* of the time of entry `j`: the last tick or advance at or before `j`. (Well defined, since entry `0` is a tick.) -/
def startOf (j : ℕ) : ℕ := Nat.findGreatest (IsTA input) j

theorem startOf_le (j : ℕ) : startOf input j ≤ j := Nat.findGreatest_le j

theorem not_isTA_of_startOf_lt {j l : ℕ} (h1 : startOf input j < l) (h2 : l ≤ j) :
    ¬ IsTA input l :=
  Nat.findGreatest_is_greatest h1 h2

theorem startOf_eq_of {a j : ℕ} (ha : IsTA input a) (haj : a ≤ j)
    (hno : ∀ l, a < l → l ≤ j → ¬ IsTA input l) : startOf input j = a :=
  Nat.findGreatest_eq_iff.mpr ⟨haj, fun _ => ha, fun n h1 h2 => hno n h1 h2⟩

theorem not_tick_of_not_isTA {l : ℕ} (hl : ¬ IsTA input l) (h : l < (log input).length) :
    (∀ t, moveAt l h ≠ .tick t) ∧ (∀ t, moveAt l h ≠ .advance t) :=
  ⟨fun t ht => hl ⟨h, Or.inl ⟨t, ht⟩⟩, fun t ht => hl ⟨h, Or.inr ⟨t, ht⟩⟩⟩

theorem not_isTA_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    ¬ IsTA input j := by
  rintro ⟨h, ⟨t, ht⟩ | ⟨t, ht⟩⟩ <;>
  · obtain ⟨h', hm | ⟨e, π, hm, -⟩⟩ := visitPage_eq_some_iff.mp hvis
    · rw [ht] at hm; cases hm
    · rw [ht] at hm; cases hm

section

variable (hv : input.Valid)
include hv

theorem isTA_startOf {j : ℕ} (hj : j < (log input).length) : IsTA input (startOf input j) := by
  have h0 : 0 < (log input).length := by omega
  obtain ⟨t, ht⟩ := first_tick hv h0
  exact Nat.findGreatest_spec (Nat.zero_le j) ⟨h0, Or.inl ⟨t, ht⟩⟩

theorem startOf_of_between {j l : ℕ} (hj : j < (log input).length) (h1 : startOf input j ≤ l)
    (h2 : l ≤ j) : startOf input l = startOf input j :=
  startOf_eq_of (isTA_startOf hv hj) h1 (fun l' h1' h2' => not_isTA_of_startOf_lt h1' (by omega))

theorem startOf_lt_of_visit {j : ℕ} {p : Page} (hvis : visitPage input j = some p) :
    startOf input j < j := by
  obtain ⟨h, -⟩ := visitPage_eq_some_iff.mp hvis
  rcases lt_or_eq_of_le (startOf_le (input := input) j) with hlt | heq
  · exact hlt
  · exact absurd (heq ▸ isTA_startOf hv h) (not_isTA_of_visit hvis)

/-- All entries from the start index of `j` to `j` have the time of `j`. -/
theorem entryTime_startOf {j : ℕ} (hj : j < (log input).length) :
    entryTime input j = entryTime input (startOf input j) := by
  have key : ∀ l, startOf input j ≤ l → l ≤ j → entryTime input l = entryTime input (startOf input j) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => intro _; rfl
    | succ l hl ih =>
      intro hlj
      have hlt : l + 1 < (log input).length := by omega
      obtain ⟨h1, h2⟩ := not_tick_of_not_isTA (not_isTA_of_startOf_lt (by omega) hlj) hlt
      rw [entryTime_of_not_tick hv hlt h1 h2, ← ih (by omega)]
      rfl
  exact key j (startOf_le j) le_rfl

/-- No page is visited twice at one time: between the start index of a visit of `p` and the visit, `p` is not visited. -/
theorem no_visit_between {j l : ℕ} {p : Page} (hvis : visitPage input j = some p)
    (h1 : startOf input j < l) (h2 : l < j) : visitPage input l ≠ some p := by
  intro hl
  obtain ⟨ρ, hρ, hρp⟩ := visit_pending hv hvis
  have hsub := pending_of_no_tick hv (l := l + 1) (m := j) (by omega)
    (fun l' h h1' h2' t ht => not_isTA_of_startOf_lt (j := j) (by omega) (by omega)
      ⟨h, Or.inl ⟨t, ht⟩⟩) hρ
  exact no_pending_after_visit hv hl hsub hρp

/-- No visit of `p` in `[startOf j, j)` for a visit `j` of `p`. -/
theorem no_visit_before {j l : ℕ} {p : Page} (hvis : visitPage input j = some p)
    (h1 : startOf input j ≤ l) (h2 : l < j) : visitPage input l ≠ some p := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact no_visit_between hv hvis h1 h2
  · intro hl
    have hlt : l < (log input).length := (visitPage_eq_some_iff.mp hl).1
    have := isTA_startOf hv (visitPage_eq_some_iff.mp hvis).1
    rw [h1] at this
    exact not_isTA_of_visit hl this

/-! ### Delays and claims between visits -/

/-- A move that is not a tick and not a visit of `p` does not change the delay of `p`. -/
theorem pageDelay_succ {l : ℕ} (h : l < (log input).length) (htk : ∀ t, moveAt l h ≠ .tick t)
    {p : Page} (hp : visitPage input l ≠ some p) (t : ℝ) :
    pageDelay (snapAt input (l + 1)).pending p t = pageDelay (snapAt input l).pending p t := by
  rcases hm : moveAt l h with t' | t' | p' | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · exact absurd hm (htk t')
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · have hp' : p ≠ p' := fun hpp => hp (hpp ▸ visitPage_of_critical h hm)
    rw [(critical_spec hv h hm).2.2]
    exact pageDelay_filter_ne _ hp' t
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]
  · have hp' : p ≠ π.page := fun hpp => hp (hpp ▸ visitPage_of_trip h hm)
    rw [(trip_spec hv h hm).2.2.2]
    exact pageDelay_filter_ne _ hp' t
  · rw [pending_succ_of_not_visit hv h (by simp [hm]) (by simp [hm]) (by simp [hm])]

theorem pageDelay_of_between {l m : ℕ} (hlm : l ≤ m) {p : Page}
    (hno : ∀ l' (h : l' < (log input).length), l ≤ l' → l' < m →
      (∀ t, moveAt l' h ≠ .tick t) ∧ visitPage input l' ≠ some p) (t : ℝ) :
    pageDelay (snapAt input m).pending p t = pageDelay (snapAt input l).pending p t := by
  induction m, hlm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [← ih (fun l' h h1 h2 => hno l' h h1 (by omega))]
    by_cases hlt : m < (log input).length
    · obtain ⟨h1, h2⟩ := hno m hlt hm (by omega)
      exact pageDelay_succ hv hlt h1 h2 t
    · rw [snapAt_of_ge (by omega), snapAt_of_ge (i := m) (by omega)]

/-- A move that is not a visit of `p` does not decrease the claim of `p`. -/
theorem claims_le_succ {l : ℕ} {p : Page} (hp : visitPage input l ≠ some p) :
    (snapAt input l).claims p ≤ (snapAt input (l + 1)).claims p := by
  by_cases h : l < (log input).length
  · by_cases hvis : (∃ p', moveAt l h = .critical p') ∨ (∃ e π, moveAt l h = .trip e π)
    · rcases hvis with ⟨p', hm⟩ | ⟨e, π, hm⟩
      · have hp' : p ≠ p' := fun hpp => hp (hpp ▸ visitPage_of_critical h hm)
        rw [(critical_spec hv h hm).2.2]
        dsimp only
        rw [Function.update_of_ne hp']
        exact le_claimUpdate hv _ _ _ _ _ _
      · have hp' : p ≠ π.page := fun hpp => hp (hpp ▸ visitPage_of_trip h hm)
        rw [(trip_spec hv h hm).2.2.2]
        dsimp only
        rw [Function.update_of_ne hp']
    · push_neg at hvis
      rw [claims_succ_of_not_visit hv h hvis.1 hvis.2]
  · rw [snapAt_of_ge (i := l + 1) (by omega), snapAt_of_ge (i := l) (by omega)]

theorem claims_le_of_between {l m : ℕ} (hlm : l ≤ m) {p : Page}
    (hno : ∀ l', l ≤ l' → l' < m → visitPage input l' ≠ some p) :
    (snapAt input l).claims p ≤ (snapAt input m).claims p := by
  induction m, hlm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    exact (ih fun l' h1 h2 => hno l' h1 (by omega)).trans (claims_le_succ hv (hno m hm (by omega)))

/-! ### Chains of critical services along the run -/

/-- Between `a` and `m`, the base state changes only by critical services: it is the end of their chain, of total length `∑_{a ≤ l < m} lenAt l`. -/
theorem exists_chain {a m : ℕ} (ham : a ≤ m) {q : Page}
    (hno : ∀ l (hl : l < (log input).length), a ≤ l → l < m → moveAt l hl ≠ .critical q) :
    ∃ ps : List Page, q ∉ ps ∧
      baseState (snapAt input m) = chainState input (baseState (snapAt input a)) ps ∧
      chainLen input (baseState (snapAt input a)) ps = ∑ l ∈ Finset.Ico a m, lenAt input l := by
  induction m, ham using Nat.le_induction with
  | base => exact ⟨[], by simp, rfl, by simp⟩
  | succ m hm ih =>
    obtain ⟨ps, hq, hst, hlen⟩ := ih fun l hl h1 h2 => hno l hl h1 (by omega)
    rw [Finset.sum_Ico_succ_top hm]
    by_cases hlt : m < (log input).length
    · by_cases hc : ∃ p, moveAt m hlt = .critical p
      · obtain ⟨p, hp⟩ := hc
        have hpq : p ≠ q := fun h => hno m hlt hm (by omega) (h ▸ hp)
        obtain ⟨hidle, -, heq⟩ := critical_spec hv hlt hp
        have hxm : (snapAt input m).x = baseState (snapAt input m) :=
          x_eq_baseState hv (by intro e b hb; rw [hidle] at hb; cases hb)
        have hb1 : baseState (snapAt input (m + 1)) = criticalState input (snapAt input m).x p := by
          rw [baseState_of_not_preempt (by rw [heq]; intro e b hb; cases hb), heq]
        refine ⟨ps ++ [p], ?_, ?_, ?_⟩
        · simp [hq, hpq.symm]
        · rw [hb1, chainState_append_single, hxm, hst]
        · rw [chainLen_append_single, hlen, lenAt_of_critical hlt hp, hxm, hst]
      · push_neg at hc
        refine ⟨ps, hq, ?_, ?_⟩
        · rw [baseState_succ_of_not_critical hv hlt hc, hst]
        · rw [lenAt_of_not_critical (fun h p => hc p), add_zero, hlen]
    · refine ⟨ps, hq, ?_, ?_⟩
      · rw [snapAt_of_ge (by omega), ← snapAt_of_ge (i := m) (by omega), hst]
      · rw [lenAt_of_not_critical (fun h p => absurd h hlt), add_zero, hlen]

end

end

end PagingWithDelay.PMD.DelayProof
