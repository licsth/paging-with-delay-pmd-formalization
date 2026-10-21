import PagingWithDelay.Run.Basic
import PagingWithDelay.Run.Steps

/-!
# `PMD` is feasible (`lem:inv`)

Every waypoint is a fractional state with missing mass at least `n - k`, the waypoints are chronological, and every request is served: on arrival (`x_p = δ` at the tick), or later by a visit of its page, which records a waypoint with `x_p = δ`. At the end nothing is pending, since a pending request would eventually trigger (`lem:inv`(b)).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- A property that holds at `a` and fails at `b ≥ a` is lost at some step in between. -/
theorem exists_drop (P : ℕ → Prop) {a b : ℕ} (ha : P a) (hb : ¬ P b) (hab : a ≤ b) :
    ∃ j, a ≤ j ∧ j < b ∧ P j ∧ ¬ P (j + 1) := by
  induction b with
  | zero => exact absurd (by rwa [Nat.le_zero.1 hab] at ha) hb
  | succ b ih =>
    by_cases hP : P b
    · refine ⟨b, ?_, by omega, hP, hb⟩
      rcases Nat.lt_or_ge b a with h | h
      · exact absurd (by rwa [show a = b + 1 by omega] at ha) hb
      · exact h
    · have hab' : a ≤ b := by
        rcases Nat.lt_or_ge b a with h | h
        · exact absurd (by rwa [show a = b + 1 by omega] at ha) hb
        · exact h
      obtain ⟨j, h1, h2, h3, h4⟩ := ih hP hab'
      exact ⟨j, h1, by omega, h3, h4⟩

section

variable {input : Instance Page} (hv : input.Valid)
include hv

/-- Every request is served by some log entry `j`: a waypoint of `j` at or after the arrival has `x_p = δ` (the tick of its arrival, or the visit that removes it from the pending list). -/
theorem exists_serving_entry {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ j, ∃ hj : j < (log input).length, ∃ w ∈ wpAt input j,
      ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta := by
  obtain ⟨i0, h0, ht⟩ := exists_tick_arrival hv hρ
  have key : ∃ j, ∃ hj : j < (log input).length,
      (ρ ∈ (snapAt input j).pending ∨
        (∃ t, moveAt j hj = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t)) ∧
      ρ ∉ (snapAt input (j + 1)).pending := by
    by_cases hin : ρ ∈ (snapAt input (i0 + 1)).pending
    · have hfin : ρ ∉ (snapAt input (log input).length).pending := by
        rw [(final_spec hv).2.1]; simp
      obtain ⟨j, -, hj2, hPj, hPj1⟩ :=
        exists_drop (fun m => ρ ∈ (snapAt input m).pending) hin hfin (by omega)
      exact ⟨j, hj2, Or.inl hPj, hPj1⟩
    · exact ⟨i0, h0, Or.inr ⟨_, ht, hρ, rfl⟩, hin⟩
  obtain ⟨j, hj, hr1, hr2⟩ := key
  obtain ⟨w, hw, hw'⟩ := served_of_removed hv hj hr1 hr2
  exact ⟨j, hj, w, by rw [wpAt_of_lt hj]; exact hw, hw'⟩

/-- **When a request is served.** Let `i₀` be the tick of the arrival of `ρ`. Then there is an entry `j ≥ i₀` such that `ρ` is pending before every entry `l` with `i₀ < l ≤ j` and not after `j`, and the service time of `ρ` is `entryTime j`. If `j = i₀`, `ρ` is served on arrival (`x_p = δ` at the tick); otherwise entry `j` is a visit of its page (`pending_removed`). -/
theorem serviceTime_spec {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ i₀ j, ∃ h₀ : i₀ < (log input).length, ∃ hj : j < (log input).length,
      moveAt i₀ h₀ = .tick ρ.arrival ∧ i₀ ≤ j ∧
      (∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending) ∧
      ρ ∉ (snapAt input (j + 1)).pending ∧
      FracSchedule.serviceTime input (preemptiveMirrorDescent input) ρ = entryTime input j := by
  classical
  obtain ⟨i₀, h₀, ht⟩ := exists_tick_arrival hv hρ
  let Q : ℕ → Prop := fun m => i₀ ≤ m ∧ ρ ∉ (snapAt input (m + 1)).pending
  have hQ : ∃ m, Q m := by
    refine ⟨(log input).length - 1, by omega, ?_⟩
    rw [show (log input).length - 1 + 1 = (log input).length by omega, (final_spec hv).2.1]
    simp
  obtain ⟨j, hjQ, hjmin⟩ : ∃ j, Q j ∧ ∀ m < j, ¬ Q m :=
    ⟨Nat.find hQ, Nat.find_spec hQ, fun m hm => Nat.find_min hQ hm⟩
  have hjlt : j < (log input).length := by
    by_contra hge
    apply hjmin ((log input).length - 1) (by omega)
    refine ⟨by omega, ?_⟩
    rw [show (log input).length - 1 + 1 = (log input).length by omega, (final_spec hv).2.1]
    simp
  have hpend : ∀ l, i₀ < l → l ≤ j → ρ ∈ (snapAt input l).pending := by
    intro l h1 h2
    have := hjmin (l - 1) (by omega)
    simp only [Q, not_and, not_not] at this
    have h := this (by omega)
    rwa [show l - 1 + 1 = l by omega] at h
  refine ⟨i₀, j, h₀, hjlt, ht, hjQ.1, hpend, hjQ.2, ?_⟩
  have hr1 : ρ ∈ (snapAt input j).pending ∨
      (∃ t, moveAt j hjlt = .tick t ∧ ρ ∈ input.requests ∧ ρ.arrival = t) := by
    rcases eq_or_lt_of_le hjQ.1 with h | h
    · right
      subst h
      exact ⟨_, ht, hρ, rfl⟩
    · exact Or.inl (hpend j h le_rfl)
  obtain ⟨w, hw, hwa, hws⟩ := served_of_removed hv hjlt hr1 hjQ.2
  have hwt : w.time = entryTime input j :=
    (wp_spec hv j hjlt w (by rw [wpAt_of_lt hjlt]; exact hw)).1
  unfold FracSchedule.serviceTime
  apply IsLeast.csInf_eq
  refine ⟨⟨w, (mem_output_iff hv).mpr ⟨j, hjlt, by rw [wpAt_of_lt hjlt]; exact hw⟩, hwa, hws,
    hwt⟩, ?_⟩
  rintro s ⟨w', hw', hwa', hws', rfl⟩
  obtain ⟨i, hi, hwi⟩ := (mem_output_iff hv).mp hw'
  have hwt' : w'.time = entryTime input i := (wp_spec hv i hi w' hwi).1
  rw [hwt']
  by_cases hji : j ≤ i
  · exact entryTime_mono hv hji
  · exfalso
    by_cases hii : i < i₀
    · have := entryTime_lt_of_tick hv h₀ ht hii
      rw [hwt'] at hwa'
      linarith
    · have hp := hpend (i + 1) (by omega) (by omega)
      have := delta_lt_wp_of_pending_succ hv hi hp w' hwi
      rw [hws'] at this
      exact lt_irrefl _ this

end

theorem preemptiveMirrorDescent_feasible :
    (preemptiveMirrorDescent : FracAlgorithm Page).Feasible := by
  intro input
  have hv := input.valid
  constructor
  · show List.Pairwise _ ((log input).flatMap _)
    rw [List.pairwise_flatMap]
    constructor
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [log_getElem i hi]
      have hs := wp_spec hv i hi
      simp only [wpAt, dif_pos hi] at hs
      apply List.pairwise_of_forall_mem_list
      intro a ha b hb
      rw [(hs a ha).1, (hs b hb).1]
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [log_getElem i hi, log_getElem j hj]
      intro a ha b hb
      have hsi := wp_spec hv i hi
      have hsj := wp_spec hv j hj
      simp only [wpAt, dif_pos hi, dif_pos hj] at hsi hsj
      rw [(hsi a ha).1, (hsj b hb).1]
      exact entryTime_mono hv hij.le
  · intro w hw
    obtain ⟨i, hi, hw⟩ := (mem_output_iff hv).mp hw
    exact (wp_spec hv i hi w hw).2.1
  · intro w hw
    obtain ⟨i, hi, hw⟩ := (mem_output_iff hv).mp hw
    exact (wp_spec hv i hi w hw).2.2
  · intro ρ hρ
    obtain ⟨j, hj, w, hw, hw'⟩ := exists_serving_entry hv hρ
    exact ⟨w, (mem_output_iff hv).mpr ⟨j, hj, hw⟩, hw'⟩

end PMD

end PagingWithDelay
