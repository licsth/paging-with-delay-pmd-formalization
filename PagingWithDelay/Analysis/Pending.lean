import PagingWithDelay.Analysis.Defs

/-!
# Pending requests as a sub-multiset of the requests

Every request value occurs in the pending list at most as often as among the requests (a tick adds all requests with a fresh arrival time, which no pending request has). Hence sums over the pending list are bounded by index sums over the requests whose value is pending.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace PendingProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

open Classical

/-- Every request value is pending at most as often as it occurs in the requests. -/
theorem pending_count_le (hv : input.Valid) (i : ℕ) (ρ : Request Page) :
    (snapAt input i).pending.count ρ ≤ input.requests.count ρ := by
  induction i with
  | zero => rw [snapAt_zero hv]; simp [initialSnap]
  | succ i ih =>
    by_cases hi : i < (log input).length
    · rcases hm : moveAt i hi with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
      · obtain ⟨-, -, -, hup, heq⟩ := tick_spec hv hi hm
        rw [heq]
        refine (List.filter_sublist.count_le _).trans ?_
        rw [List.count_append]
        by_cases ha : ρ.arrival = t
        · have h0 : (snapAt input i).pending.count ρ = 0 := by
            rw [List.count_eq_zero]
            intro hρ
            exact (pending_spec hv hρ).2.2 (by rw [hup, ha]; simp)
          rw [h0, zero_add]
          exact List.filter_sublist.count_le _
        · have h0 : (input.requests.filter fun ρ => decide (ρ.arrival = t)).count ρ = 0 := by
            rw [List.count_eq_zero]
            intro hρ
            exact ha (by simpa using (List.mem_filter.mp hρ).2)
          rw [h0, add_zero]
          exact ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [(critical_spec hv hi hm).2.2]
        exact (List.filter_sublist.count_le _).trans ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
      · rw [(trip_spec hv hi hm).2.2.2]
        exact (List.filter_sublist.count_le _).trans ih
      · rw [pending_succ_of_not_visit hv hi (by rw [hm]; simp) (by rw [hm]; simp)
          (by rw [hm]; simp)]
        exact ih
    · rw [snapAt_of_ge (by omega)]
      rw [snapAt_of_ge (by omega)] at ih
      exact ih

/-- A sum of nonnegative terms over the pending requests satisfying `P` is at most the sum over the indices of the requests whose value is pending and satisfies `P`. -/
theorem sum_pending_le (hv : input.Valid) (i : ℕ) (P : Request Page → Prop)
    (f : Request Page → ℝ) (hf : ∀ ρ ∈ input.requests, 0 ≤ f ρ) :
    (((snapAt input i).pending.filter fun ρ => decide (P ρ)).map f).sum ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ P input.requests[k]),
        f input.requests[k] := by
  set L := (snapAt input i).pending.filter fun ρ => decide (P ρ) with hL
  set R := input.requests with hR
  set g : Request Page → ℝ := fun ρ => if ρ ∈ (snapAt input i).pending ∧ P ρ then f ρ else 0
    with hg
  have hrhs : ∑ k ∈ Finset.univ.filter (fun k : Fin R.length =>
      R[k] ∈ (snapAt input i).pending ∧ P R[k]), f R[k] = (R.map g).sum := by
    rw [Finset.sum_filter]
    exact Fin.sum_univ_fun_getElem R g
  rw [hrhs, Finset.sum_list_map_count, Finset.sum_list_map_count]
  have hmemL : ∀ ρ, ρ ∈ L ↔ ρ ∈ (snapAt input i).pending ∧ P ρ := by
    intro ρ; rw [hL, List.mem_filter, decide_eq_true_iff]
  have hsub : L.toFinset ⊆ R.toFinset := by
    intro ρ hρ
    rw [List.mem_toFinset, hmemL] at hρ
    rw [List.mem_toFinset]
    exact (pending_spec hv hρ.1).1
  calc ∑ ρ ∈ L.toFinset, L.count ρ • f ρ ≤ ∑ ρ ∈ L.toFinset, R.count ρ • g ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [List.mem_toFinset] at hρ
        have hρ' := (hmemL ρ).mp hρ
        have hgρ : g ρ = f ρ := by rw [hg]; simp [hρ']
        rw [hgρ, nsmul_eq_mul, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hf ρ (pending_spec hv hρ'.1).1)
        exact_mod_cast (List.filter_sublist.count_le _).trans (pending_count_le hv i ρ)
    _ = ∑ ρ ∈ R.toFinset, R.count ρ • g ρ := by
        apply Finset.sum_subset hsub
        intro ρ _ hρ
        rw [List.mem_toFinset, hmemL] at hρ
        rw [hg]; simp [hρ]

/-- The delay of the pending requests on `p` at a time `t ≥` their arrivals is at most the index sum of their delays. -/
theorem pageDelay_le_sum (hv : input.Valid) (i : ℕ) (p : Page) (t : ℝ)
    (ht : ∀ ρ ∈ (snapAt input i).pending, ρ.arrival ≤ t) :
    pageDelay (snapAt input i).pending p t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = p),
        input.requests[k].delay (t - input.requests[k].arrival) := by
  set f : Request Page → ℝ := fun ρ => if ρ.arrival ≤ t then ρ.delay (t - ρ.arrival) else 0
    with hfdef
  have hf : ∀ ρ ∈ input.requests, 0 ≤ f ρ := by
    intro ρ hρ
    rw [hfdef]
    dsimp only
    split_ifs with h
    · rw [← hv.delay_zero ρ hρ]
      exact hv.delay_mono ρ hρ (by linarith)
    · exact le_rfl
  have key := sum_pending_le hv i (fun ρ => ρ.page = p) f hf
  have hl : pageDelay (snapAt input i).pending p t =
      (((snapAt input i).pending.filter fun ρ => decide (ρ.page = p)).map f).sum := by
    unfold pageDelay
    congr 1
    apply List.map_congr_left
    intro ρ hρ
    rw [hfdef]
    simp only
    rw [if_pos (ht ρ (List.mem_filter.mp hρ).1)]
  have hfil : ((snapAt input i).pending.filter fun ρ => decide (ρ.page = p)) =
      (snapAt input i).pending.filter fun ρ => @decide (ρ.page = p) (Classical.propDecidable _) :=
    List.filter_congr (fun ρ _ => decide_eq_decide.mpr Iff.rfl)
  rw [hl, hfil]
  refine key.trans (le_of_eq ?_)
  refine Finset.sum_congr (by ext k; simp only [Finset.mem_filter]) ?_
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [hfdef]
  simp only
  rw [if_pos (ht _ hk.2.1)]

end PendingProof

end PMD

end PagingWithDelay
