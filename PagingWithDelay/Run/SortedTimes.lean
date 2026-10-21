import PagingWithDelay.Algorithm

/-!
# Lists of times filtered up to a time

Two facts about sorted lists of times and their prefixes up to `t`, used to show that `PMD` is online (`PagingWithDelay/Run/Online.lean`).
-/

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OnlineProof

theorem filter_le_nil (t b : ℝ) (r : List ℝ) (h : (b :: r).Pairwise (· ≤ ·)) (hb : t < b) :
    (b :: r).filter (fun a => decide (a ≤ t)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha
  have : b ≤ a := by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (List.pairwise_cons.mp h).1 a ha
  simp only [decide_eq_true_eq, not_le]
  linarith

theorem heads (t : ℝ) {u1 u2 : List ℝ} (h1 : u1.Pairwise (· ≤ ·)) (h2 : u2.Pairwise (· ≤ ·))
    (hf : u1.filter (fun a => decide (a ≤ t)) = u2.filter (fun a => decide (a ≤ t))) :
    ((∀ a ∈ u1.head?, t < a) ∧ (∀ a ∈ u2.head?, t < a)) ∨
      ∃ a r1 r2, a ≤ t ∧ u1 = a :: r1 ∧ u2 = a :: r2 ∧
        r1.filter (fun a => decide (a ≤ t)) = r2.filter (fun a => decide (a ≤ t)) := by
  cases u1 with
  | nil =>
    cases u2 with
    | nil => left; simp
    | cons b r2 =>
      left
      refine ⟨by simp, ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      by_contra hb
      push_neg at hb
      simp [hb] at hf
  | cons a r1 =>
    cases u2 with
    | nil =>
      left
      refine ⟨?_, by simp⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      by_contra ha
      push_neg at ha
      simp [ha] at hf
    | cons b r2 =>
      by_cases ha : a ≤ t
      · by_cases hb : b ≤ t
        · right
          simp only [List.filter_cons, ha, hb, decide_true, if_true, List.cons.injEq] at hf
          obtain ⟨rfl, hr⟩ := hf
          exact ⟨a, r1, r2, ha, rfl, rfl, hr⟩
        · exfalso
          rw [filter_le_nil t b r2 h2 (lt_of_not_ge hb)] at hf
          simp [ha] at hf
      · by_cases hb : b ≤ t
        · exfalso
          rw [filter_le_nil t a r1 h1 (lt_of_not_ge ha)] at hf
          simp [hb] at hf
        · left
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
          exact ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩

end OnlineProof

end

end PMD

end PagingWithDelay
