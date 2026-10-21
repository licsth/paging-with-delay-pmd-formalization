import PagingWithDelay.Trigger
import PagingWithDelay.Hole

/-!
# One move of the loop

Characterization of `next` by its move.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost initialState afterLevel Stage)

noncomputable section

variable {input : Instance Page}

/-- The condition under which an idle loop advances to the infimum of the trigger times. -/
def AdvanceCond (input : Instance Page) (s : Snap Page) : Prop :=
  (triggerTimes input s).Nonempty ∧ ∀ a ∈ s.upcoming.head?, sInf (triggerTimes input s) < a

theorem next_tick {s s' : Snap Page} {t : ℝ} (h : next input s = some (.tick t, s')) :
    s.stage = .idle ∧ triggerPage input s = none ∧ ¬ AdvanceCond input s ∧
    s.upcoming = t :: s.upcoming.tail ∧
    s' = { s with
      now := t
      upcoming := s.upcoming.tail
      pending := (s.pending ++ input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
        fun ρ => decide (s.x ρ.page ≠ δ) } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      · simp at h
      · split at h
        · simp at h
        · rename_i t' rest
          simp only [Option.some.injEq, Prod.mk.injEq, Move.tick.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, hf, hc, rfl, rfl⟩
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_advance {s s' : Snap Page} {t : ℝ} (h : next input s = some (.advance t, s')) :
    s.stage = .idle ∧ triggerPage input s = none ∧ AdvanceCond input s ∧
    t = sInf (triggerTimes input s) ∧
    s' = { s with now := t } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.advance.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hf, hc, rfl, rfl⟩
      · split at h
        · simp at h
        · simp at h
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_critical {s s' : Snap Page} {p : Page}
    (h : next input s = some (.critical p, s')) :
    s.stage = .idle ∧ triggerPage input s = some p ∧
    s' = { s with
      x := criticalState input s.x p
      budget := deposit input s.x p s.budget
      pending := s.pending.filter fun π => decide (π.page ≠ p)
      claims := Function.update (claimUpdate input s.x s.pending s.claims s.now p) p 0
      stage := .examine (minLevel input) } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · rename_i p' hf
      simp only [Option.some.injEq, Prod.mk.injEq, Move.critical.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hf, rfl⟩
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_skip {s s' : Snap Page} {e : ℤ} (h : next input s = some (.skip e, s')) :
    s.stage = .examine e ∧ ¬ preemptCondition input s.x s.budget e ∧
    s' = { s with stage := afterLevel input e } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h with hb
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq, Move.skip.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hb, rfl⟩
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_openHole {s s' : Snap Page} {e : ℤ} (h : next input s = some (.openHole e, s')) :
    s.stage = .examine e ∧ preemptCondition input s.x s.budget e ∧
    s' = { s with
      x := hole input s.x e
      budget := Function.update s.budget e (s.budget e - holePayment input e)
      stage := .preempt e s.x } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq, Prod.mk.injEq, Move.openHole.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hb, rfl⟩
    · simp at h
  | preempt e b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h <;> simp at h

theorem next_trip {s s' : Snap Page} {e : ℤ} {π : Request Page}
    (h : next input s = some (.trip e π, s')) :
    (∃ b, s.stage = .preempt e b) ∧
    tripCandidate input s.pending s.now e = some π ∧
    levelWeight e ≤ s.budget e ∧
    s' = { s with
      budget := Function.update s.budget e (s.budget e - tripCost input s.x π.page)
      pending := s.pending.filter fun ρ => decide (ρ.page ≠ π.page)
      claims := Function.update s.claims π.page 0 } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i π' hπ
      split_ifs at h with hcost
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.trip.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨⟨b, rfl⟩, hπ, hcost, rfl⟩
      · simp at h

theorem next_closeHole {s s' : Snap Page} {e : ℤ} {stop : Option (Request Page)}
    (h : next input s = some (.closeHole e stop, s')) :
    ∃ b, s.stage = .preempt e b ∧
    (match stop with
      | none => tripCandidate input s.pending s.now e = none
      | some π => tripCandidate input s.pending s.now e = some π ∧
          s.budget e < levelWeight e) ∧
    s' = { s with x := b, stage := afterLevel input e } := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h <;> simp at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · rename_i hπ
      simp only [Option.some.injEq, Prod.mk.injEq, Move.closeHole.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨b, rfl, hπ, rfl⟩
    · rename_i π' hπ
      split_ifs at h with hcost
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq, Move.closeHole.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨b, rfl, ⟨hπ, lt_of_not_ge hcost⟩, rfl⟩

/-- `next` is `none` exactly at an idle state where no page triggers, no trigger time is left, and no arrival time is left. -/
theorem next_eq_none {s : Snap Page} (h : next input s = none) :
    s.stage = .idle ∧ triggerPage input s = none ∧ ¬ (triggerTimes input s).Nonempty ∧
      s.upcoming = [] := by
  rcases s with ⟨now, up, x, budget, pend, claims, stage⟩
  cases stage with
  | idle =>
    simp only [next] at h
    split at h
    · simp at h
    · rename_i hf
      split_ifs at h with hc
      cases up with
      | nil =>
        refine ⟨rfl, hf, ?_, rfl⟩
        intro hne
        apply hc
        refine ⟨hne, ?_⟩
        simp
      | cons t rest => simp at h
  | examine e' =>
    simp only [next] at h
    split_ifs at h
  | preempt e' b =>
    simp only [next] at h
    split at h
    · simp at h
    · split_ifs at h

end

end PMD

end PagingWithDelay
