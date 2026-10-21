import PagingWithDelay.Analysis.Pending

/-!
# Services that are not overdue (`lem:timely`)

The excess of the critical services that are not overdue is at most `L` times the comparator's delay cost: `∑_{λ not overdue} Exc(λ) ≤ L · ∑_ρ d_ρ(σ ρ - a_ρ)`.

* A critical service `λ` on `p` claims `claimAt i q = c_q' - c_q ≥ 0` from every page `q` (`claimUpdate`), in total `|λ|/L` since `p` triggers; and `Exc(λ) ≤ |λ|`. So `Exc(λ) ≤ L ∑_q claimAt i q` (`excessAt_le`).
* Fix a page `q`. Every entry `i` that is not overdue and claims a positive amount from `q` has `q` pending, so `q` is visited at some entry `≥ i`; let `nextVisit i q` be the first one, and group the claims from `q` by `(q, nextVisit i q)`. Let `m` be the last entry of a group. Within the group no visit of `q` resets `c_q`, so the claims telescope to at most `c_q + claimAt m q ≤ delay_q(t_m) - w_q` right before `m` (a positive claim is at most the overshoot `delay_q - c_q - w_q`). As `m` is not overdue and `w_q ≤ w_{p_m}`, the pending requests on `q` served by the comparator have delay at most `w_q`; every other one costs the comparator at least its current delay. So the group is paid by the comparator's delay cost of the requests pending on `q` right before `m` (`group_le`).
* These request sets are pairwise disjoint: a request pending on `q` before `m(q, j)` and before `m(q, j')` with `j < j'` would still be pending after the visit `j` of `q` (`group_disjoint`).

**Remark on the paper.** The paper's argument goes through as stated. Our `IsOverdue` is not restricted to miss services on pages below `w_min(OPT)`, which the argument does not need. The telescoping only uses the claims between the first and the last grouped entry, not that `c_q` is reset to `0` at the previous visit.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace NotOverdueProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd)
open PagingWithDelay.Schedule (cacheAt ServedBy)

open Classical

noncomputable section

variable (input : Instance Page)

/-- The amount entry `i` claims from page `q`: if it is a critical service on `p`, the increase `claimUpdate … q - c_q` of `c_q`; else `0`. -/
def claimAt (i : ℕ) (q : Page) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q - (snapAt input i).claims q
    | _ => 0
  else 0

/-- The first visit of `q` at or after entry `i` (`0` if there is none). -/
def nextVisit (i : ℕ) (q : Page) : ℕ :=
  if h : ∃ j, i ≤ j ∧ visitPage input j = some q then Nat.find h else 0

variable {input}

/-! ### Claims -/

theorem claimAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (q : Page) :
    claimAt input i q = claimUpdate input (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q - (snapAt input i).claims q := by
  simp only [claimAt, dif_pos h, hm]

theorem claimAt_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) (q : Page) : claimAt input i q = 0 := by
  unfold claimAt
  rw [dif_pos h]
  split
  · next p hp => exact absurd hp (hm p)
  · rfl

theorem claimAt_of_ge {i : ℕ} (h : (log input).length ≤ i) (q : Page) :
    claimAt input i q = 0 := by
  unfold claimAt
  rw [dif_neg (by omega)]

theorem visitPage_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) : visitPage input i = some p := by
  simp only [visitPage, dif_pos h, hm]

theorem visitPage_of_trip {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) : visitPage input i = some π.page := by
  simp only [visitPage, dif_pos h, hm]

theorem visitPage_of_other {i : ℕ} (h : i < (log input).length)
    (hc : ∀ p, moveAt i h ≠ .critical p) (ht : ∀ e π, moveAt i h ≠ .trip e π) :
    visitPage input i = none := by
  unfold visitPage
  rw [dif_pos h]
  split
  · next p hp => exact absurd hp (hc p)
  · next e π hp => exact absurd hp (ht e π)
  · rfl

theorem lt_of_visitPage {i : ℕ} {q : Page} (hq : visitPage input i = some q) :
    i < (log input).length := by
  by_contra hge
  unfold visitPage at hq
  rw [dif_neg hge] at hq
  cases hq

section

variable (hv : input.Valid)
include hv

theorem claimAt_nonneg (i : ℕ) (q : Page) : 0 ≤ claimAt input i q := by
  by_cases h : i < (log input).length
  · by_cases hc : ∃ p, moveAt i h = .critical p
    · obtain ⟨p, hm⟩ := hc
      rw [claimAt_of_critical h hm]
      linarith [le_claimUpdate hv (snapAt input i).x (snapAt input i).pending
        (snapAt input i).claims (snapAt input i).now p q]
    · push_neg at hc
      rw [claimAt_of_not_critical h hc]
  · rw [claimAt_of_ge (by omega)]

open scoped InstanceNotation in
/-- A critical service claims `|λ|/L` in total. -/
theorem sum_claimAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) :
    ∑ q, claimAt input i q = serviceEnd input (snapAt input i).x p / L := by
  simp_rw [claimAt_of_critical h hm]
  exact sum_claimUpdate_of_triggered hv (critical_facts hv h hm).1

open scoped InstanceNotation in
/-- `|λ| = L · ∑_q claimAt i q`. -/
theorem lenAt_eq (i : ℕ) : lenAt input i = L * ∑ q, claimAt input i q := by
  by_cases h : i < (log input).length
  · by_cases hc : ∃ p, moveAt i h = .critical p
    · obtain ⟨p, hm⟩ := hc
      rw [sum_claimAt_of_critical hv h hm, mul_div_cancel₀ _ (Instance.L_pos hv).ne']
      simp only [lenAt, dif_pos h, hm]
    · push_neg at hc
      simp_rw [claimAt_of_not_critical h hc]
      simp only [Finset.sum_const_zero, mul_zero]
      unfold lenAt
      rw [dif_pos h]
      split
      · next p hp => exact absurd hp (hc p)
      · rfl
  · simp_rw [claimAt_of_ge (show (log input).length ≤ i by omega)]
    simp only [Finset.sum_const_zero, mul_zero]
    unfold lenAt
    rw [dif_neg h]

/-- `Exc(λ) ≤ |λ|`. -/
theorem excessAt_le_lenAt (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) :
    excessAt input S i ≤ lenAt input i := by
  unfold excessAt lenAt
  by_cases h : i < (log input).length
  · rw [dif_pos h, dif_pos h]
    split
    · next p hp =>
      split_ifs
      · exact serviceEnd_nonneg' (input := input) _ _
      · refine le_trans ?_ (sum_levelLen_Icc_le (snapAt input i).x p (level input p)
          (maxLevel input))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun e _ _ => levelLen_nonneg hv _ _ _
    · exact le_rfl
  · rw [dif_neg h, dif_neg h]

open scoped InstanceNotation in
/-- `Exc(λ) ≤ L ∑_q claimAt i q`. -/
theorem excessAt_le (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) :
    excessAt input S i ≤ L * ∑ q, claimAt input i q :=
  (lenAt_eq hv i) ▸ excessAt_le_lenAt hv σ S i

/-- Off visits of `q`, `c_q` changes exactly by the claim from `q`. -/
theorem claims_succ {i : ℕ} {q : Page} (hq : visitPage input i ≠ some q) :
    (snapAt input (i + 1)).claims q = (snapAt input i).claims q + claimAt input i q := by
  by_cases h : i < (log input).length
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · have hpq : q ≠ p := by
        rintro rfl; exact hq (visitPage_of_critical h hm)
      rw [(critical_spec hv h hm).2.2, claimAt_of_critical h hm]
      simp only [Function.update_of_ne hpq]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
    · have hpq : q ≠ π.page := by
        intro he; exact hq (he ▸ visitPage_of_trip h hm)
      rw [(trip_spec hv h hm).2.2.2, claimAt_of_not_critical h (by rw [hm]; simp)]
      simp only [Function.update_of_ne hpq]
      ring
    · rw [claims_succ_of_not_visit hv h (by rw [hm]; simp) (by rw [hm]; simp),
        claimAt_of_not_critical h (by rw [hm]; simp)]
      ring
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega), claimAt_of_ge (by omega)]
    ring

/-- Telescoping of `c_q` over entries without a visit of `q`. -/
theorem claims_telescope {a b : ℕ} (hab : a ≤ b) {q : Page}
    (hno : ∀ l, a ≤ l → l < b → visitPage input l ≠ some q) :
    (snapAt input b).claims q =
      (snapAt input a).claims q + ∑ l ∈ Finset.Ico a b, claimAt input l q := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [claims_succ hv (hno b hab (by omega)), ih fun l h1 h2 => hno l h1 (by omega),
      Finset.sum_Ico_succ_top hab]
    ring

/-- A visit of `q` serves all pending requests on `q`. -/
theorem not_pending_succ_of_visit {j : ℕ} {q : Page} (hj : visitPage input j = some q)
    {ρ : Request Page} (hρ : ρ ∈ (snapAt input (j + 1)).pending) : ρ.page ≠ q := by
  have h := lt_of_visitPage hj
  by_cases hc : ∃ p, moveAt j h = .critical p
  · obtain ⟨p, hm⟩ := hc
    rw [visitPage_of_critical h hm] at hj
    cases hj
    exact ((pending_succ_of_critical hv h hm).1 hρ).2
  by_cases ht : ∃ e π, moveAt j h = .trip e π
  · obtain ⟨e, π, hm⟩ := ht
    rw [visitPage_of_trip h hm] at hj
    cases hj
    exact ((pending_succ_of_trip hv h hm).1 hρ).2
  push_neg at hc ht
  rw [visitPage_of_other h hc ht] at hj
  cases hj

/-- A pending request on `q` is eventually removed by a visit of `q`. -/
theorem exists_visit {i : ℕ} {ρ : Request Page} (hρ : ρ ∈ (snapAt input i).pending) :
    ∃ j, i ≤ j ∧ visitPage input j = some ρ.page := by
  have hi : i ≤ (log input).length := by
    by_contra hgt
    rw [snapAt_of_ge (by omega), ← snapAt_of_ge (input := input) le_rfl,
      (final_spec hv).2.1] at hρ
    simp at hρ
  have hfin : ρ ∉ (snapAt input (log input).length).pending := by
    rw [(final_spec hv).2.1]; simp
  obtain ⟨j, hj1, hj2, hPj, hPj1⟩ :=
    exists_drop (fun m => ρ ∈ (snapAt input m).pending) hρ hfin hi
  refine ⟨j, hj1, ?_⟩
  rcases (pending_removed hv hj2 hPj hPj1).1 with hm | ⟨e, π, hm, hπ⟩
  · exact visitPage_of_critical hj2 hm
  · rw [← hπ]; exact visitPage_of_trip hj2 hm

theorem nextVisit_spec {i : ℕ} {q : Page} (hex : ∃ j, i ≤ j ∧ visitPage input j = some q) :
    i ≤ nextVisit input i q ∧ visitPage input (nextVisit input i q) = some q ∧
      ∀ l, i ≤ l → l < nextVisit input i q → visitPage input l ≠ some q := by
  unfold nextVisit
  rw [dif_pos hex]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun l h1 h2 h3 => ?_⟩
  exact Nat.find_min hex h2 ⟨h1, h3⟩

open scoped InstanceNotation in
/-- The facts behind a positive claim from `q`: entry `i` is a critical service on a page `p` with `w_q ≤ w_p`, `q` has a pending request, and `c_q + claimAt i q` is at most `delay_q - w_q`. -/
theorem claim_pos_facts {i : ℕ} {q : Page} (hpos : 0 < claimAt input i q) :
    ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧
      w q ≤ w p ∧
      (∃ ρ ∈ (snapAt input i).pending, ρ.page = q) ∧
      (snapAt input i).claims q + claimAt input i q ≤
        pageDelay (snapAt input i).pending q (snapAt input i).now - w q := by
  have h : i < (log input).length := by
    by_contra hge; rw [claimAt_of_ge (by omega)] at hpos; exact lt_irrefl 0 hpos
  have hc : ∃ p, moveAt i h = .critical p := by
    by_contra hno; push_neg at hno
    rw [claimAt_of_not_critical h hno] at hpos; exact lt_irrefl 0 hpos
  obtain ⟨p, hm⟩ := hc
  set s := snapAt input i
  have hcl := claimAt_of_critical h hm q
  have hle := claimUpdate_le (input := input) s.x s.pending s.claims s.now p q
  have hlight : w q ≤ w p := by
    by_contra hn
    have := claimUpdate_of_not_lighter (input := input) s.x s.pending s.claims s.now
      (p := p) (q := q) (by rw [mem_lighter]; exact hn)
    rw [this, sub_self] at hcl
    rw [hcl] at hpos; exact lt_irrefl 0 hpos
  have hov : 0 < overshoot input s.pending s.claims q s.now := by linarith
  have hlt := overshoot_pos_iff.1 hov
  have hcq := claims_nonneg hv i q
  have hw := hv.weight_pos q
  refine ⟨h, p, hm, hlight, ?_, ?_⟩
  · exact exists_pending_of_pageDelay_ne (t := s.now) (by intro h0; linarith)
  · have hov' : overshoot input s.pending s.claims q s.now =
        pageDelay s.pending q s.now - s.claims q - w q := by
      unfold overshoot; exact max_eq_right (by linarith)
    linarith

end

/-! ### Grouping the claims against the comparator -/

/-- Splitting the page delay into the requests satisfying `P` and the others. -/
theorem pageDelay_split (l : List (Request Page)) (q : Page) (t : ℝ) (P : Request Page → Prop) :
    pageDelay l q t =
      ((l.filter fun ρ => decide (ρ.page = q ∧ P ρ)).map fun ρ => ρ.delay (t - ρ.arrival)).sum +
      ((l.filter fun ρ => decide (ρ.page = q ∧ ¬ P ρ)).map fun ρ => ρ.delay (t - ρ.arrival)).sum := by
  unfold pageDelay
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hq : a.page = q <;> by_cases hP : P a <;>
      simp [hq, hP, ih] <;> ring

variable (input) (σ : Request Page → ℝ) (S : Schedule Page)

/-- The entries that are not overdue and claim a positive amount from `q`. -/
def claimSet (q : Page) : Finset ℕ :=
  (Finset.range (log input).length).filter fun i =>
    ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q

/-- The entries of `claimSet q` whose next visit of `q` is entry `j`. -/
def groupSet (q : Page) (j : ℕ) : Finset ℕ :=
  (claimSet input σ S q).filter fun i => nextVisit input i q = j

/-- The last entry of the group `(q, j)`. -/
def lastOf (q : Page) (j : ℕ) : ℕ := (groupSet input σ S q j).sup id

/-- The requests (by index) that pay for the group `(q, j)`: those pending on `q` right before its last entry. -/
def groupReq (q : Page) (j : ℕ) : Finset (Fin input.requests.length) :=
  Finset.univ.filter fun k => (groupSet input σ S q j).Nonempty ∧
    input.requests[k] ∈ (snapAt input (lastOf input σ S q j)).pending ∧
    input.requests[k].page = q

variable {input σ S}

section Comparator

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hF : S.FeasibleBy input σ)
include hv

theorem mem_claimSet_facts {q : Page} {i : ℕ} (hi : i ∈ claimSet input σ S q) :
    i < (log input).length ∧ ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q ∧
      ∃ j, i ≤ j ∧ visitPage input j = some q := by
  simp only [claimSet, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨-, -, -, -, ⟨ρ, hρ, hρq⟩, -⟩ := claim_pos_facts hv hi.2.2
  obtain ⟨j, hj1, hj2⟩ := exists_visit hv hρ
  exact ⟨hi.1, hi.2.1, hi.2.2, j, hj1, hρq ▸ hj2⟩

theorem mem_groupSet_facts {q : Page} {j i : ℕ} (hi : i ∈ groupSet input σ S q j) :
    i < (log input).length ∧ ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q ∧
      i ≤ j ∧ visitPage input j = some q ∧
      ∀ l, i ≤ l → l < j → visitPage input l ≠ some q := by
  simp only [groupSet, Finset.mem_filter] at hi
  obtain ⟨h1, h2, h3, hex⟩ := mem_claimSet_facts hv hi.1
  obtain ⟨n1, n2, n3⟩ := nextVisit_spec hv hex
  rw [hi.2] at n1 n2 n3
  exact ⟨h1, h2, h3, n1, n2, n3⟩

theorem lastOf_mem {q : Page} {j : ℕ} (hne : (groupSet input σ S q j).Nonempty) :
    lastOf input σ S q j ∈ groupSet input σ S q j := by
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  unfold lastOf; rw [heq]; exact hm

theorem le_lastOf {q : Page} {j i : ℕ} (hi : i ∈ groupSet input σ S q j) :
    i ≤ lastOf input σ S q j :=
  Finset.le_sup (f := id) hi

/-- The request sets of distinct groups of the same page are disjoint. -/
theorem group_disjoint {q : Page} {j j' : ℕ} (hjj : j < j') {ρ : Request Page}
    (hne : (groupSet input σ S q j).Nonempty) (hne' : (groupSet input σ S q j').Nonempty)
    (hρ : ρ ∈ (snapAt input (lastOf input σ S q j)).pending)
    (hρ' : ρ ∈ (snapAt input (lastOf input σ S q j')).pending) (hρq : ρ.page = q) : False := by
  set m := lastOf input σ S q j
  set m' := lastOf input σ S q j'
  obtain ⟨-, -, -, hmj, hvj, -⟩ := mem_groupSet_facts hv (lastOf_mem hv hne)
  obtain ⟨-, -, -, hmj', -, hno'⟩ := mem_groupSet_facts hv (lastOf_mem hv hne')
  have hjm' : j < m' := by
    by_contra hle
    exact hno' j (by omega) hjj hvj
  have harr : ρ.arrival ≤ entryTime input j := by
    have h1 := (pending_spec hv hρ).2.1
    have h2 := now_mono hv (input := input) (show m ≤ j + 1 by omega)
    unfold entryTime
    linarith
  have hpend := pending_of_later hv hjm' hρ' harr
  exact not_pending_succ_of_visit hv hvj hpend hρq

include hσ hF

/-- The claims of a group are paid by the comparator's delay cost of its requests. -/
theorem group_le (q : Page) (j : ℕ) :
    ∑ i ∈ groupSet input σ S q j, claimAt input i q ≤
      Schedule.delayCostOn input σ (groupReq input σ S q j) := by
  by_cases hne : (groupSet input σ S q j).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact Schedule.delayCostOn_nonneg hv hσ _
  set A := groupSet input σ S q j with hA
  set m := lastOf input σ S q j with hm_def
  have hmA : m ∈ A := lastOf_mem hv hne
  set i0 := A.min' hne with hi0_def
  have hi0A : i0 ∈ A := Finset.min'_mem A hne
  obtain ⟨hmlen, hmov, hmpos, hmj, -, -⟩ := mem_groupSet_facts hv hmA
  obtain ⟨-, -, -, -, -, hi0no⟩ := mem_groupSet_facts hv hi0A
  have hi0m : i0 ≤ m := le_lastOf hv hi0A
  -- the claims of the group telescope
  have hsub : A ⊆ Finset.Ico i0 (m + 1) := by
    intro i hi
    have h1 : i0 ≤ i := Finset.min'_le A i hi
    have h2 : i ≤ m := le_lastOf hv hi
    simp only [Finset.mem_Ico]; omega
  have hstep1 : ∑ i ∈ A, claimAt input i q ≤ ∑ i ∈ Finset.Ico i0 (m + 1), claimAt input i q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => claimAt_nonneg hv i q
  rw [Finset.sum_Ico_succ_top hi0m] at hstep1
  have htel := claims_telescope hv hi0m (q := q) fun l h1 h2 => hi0no l h1 (by omega)
  have hc0 := claims_nonneg hv i0 q
  obtain ⟨_hml, p, hmp, hlight, -, hbound⟩ := claim_pos_facts hv hmpos
  -- the comparator
  have ht : entryTime input m = (snapAt input m).now := (critical_facts hv hmlen hmp).2.2.2.2
  set t := (snapAt input m).now with ht_def
  set s := snapAt input m with hs_def
  have hserved : servedDelay input σ S s q t ≤ input.weight q := by
    by_contra hlt
    push_neg at hlt
    exact hmov ⟨hmlen, p, hmp, q, hlight, by unfold PageOverdue; rw [ht]; exact hlt⟩
  have hsplit := pageDelay_split s.pending q t
    (fun ρ => ServedBy input σ S ρ t)
  have hsd : servedDelay input σ S s q t =
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
        ServedBy input σ S ρ t)).map
          fun ρ => ρ.delay (t - ρ.arrival)).sum := rfl
  have hun1 :
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => ρ.delay (t - ρ.arrival)).sum ≤
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => Schedule.delayOf σ ρ).sum := by
    apply List.sum_le_sum
    intro ρ hρ
    simp only [List.mem_filter, decide_eq_true_eq] at hρ
    exact Schedule.delay_le_of_not_servedBy hF hv (pending_spec hv hρ.1).1 hρ.2.2
  have hun2 := PendingProof.sum_pending_le hv m
    (fun ρ => ρ.page = q ∧ ¬ ServedBy input σ S ρ t)
    (Schedule.delayOf σ) (fun ρ hρ => Schedule.delayOf_nonneg hv hσ hρ)
  have hun12 :
      ((s.pending.filter fun ρ => decide (ρ.page = q ∧
          ¬ ServedBy input σ S ρ t)).map
        fun ρ => ρ.delay (t - ρ.arrival)).sum ≤
      Schedule.delayCostOn input σ (groupReq input σ S q j) := by
    refine hun1.trans (le_trans (le_of_eq ?_) (hun2.trans ?_))
    · congr 2
      exact List.filter_congr fun ρ _ => decide_eq_decide.mpr Iff.rfl
    · unfold Schedule.delayCostOn
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_filter] at hk
        unfold groupReq
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hne, hk.2.1, hk.2.2.1⟩
      · intro k _ _
        exact Schedule.delayOf_getElem_nonneg hv hσ k
  rw [← hsd] at hsplit
  linarith

/-- The claims of the entries that are not overdue total at most the comparator's delay cost. -/
theorem sum_claim_notOverdue_le :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) ≤
      Schedule.totalDelay input σ := by
  set N := Finset.range (log input).length
  have h1 : ∀ i, (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) =
      ∑ q, (if ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q then claimAt input i q else 0) := by
    intro i
    split_ifs with ho
    · symm; apply Finset.sum_eq_zero; intro q _; rw [if_neg (by tauto)]
    · apply Finset.sum_congr rfl; intro q _
      by_cases hp : 0 < claimAt input i q
      · rw [if_pos ⟨ho, hp⟩]
      · rw [if_neg (by tauto)]
        exact le_antisymm (not_lt.1 hp) (claimAt_nonneg hv i q)
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ q, ∑ i ∈ N,
      (if ¬ IsOverdue input σ S i ∧ 0 < claimAt input i q then claimAt input i q else 0) =
      ∑ j ∈ N, ∑ i ∈ groupSet input σ S q j, claimAt input i q := by
    intro q
    rw [← Finset.sum_filter]
    symm
    exact Finset.sum_fiberwise_of_maps_to (s := claimSet input σ S q) (t := N)
      (g := fun i => nextVisit input i q)
      (fun i hi => by
        obtain ⟨-, -, -, -, hv', -⟩ := mem_groupSet_facts hv
          (Finset.mem_filter.2 ⟨hi, rfl⟩ : i ∈ groupSet input σ S q (nextVisit input i q))
        exact Finset.mem_range.2 (lt_of_visitPage hv'))
      _
  simp_rw [h2]
  rw [← Finset.sum_product (s := (Finset.univ : Finset Page)) (t := N)
    (f := fun g => ∑ i ∈ groupSet input σ S g.1 g.2, claimAt input i g.1)]
  refine Schedule.sum_le_totalDelay hv hσ (Finset.univ ×ˢ N)
    (fun g => groupReq input σ S g.1 g.2) ?_
    (fun g => ∑ i ∈ groupSet input σ S g.1 g.2, claimAt input i g.1)
    (fun g _ => group_le hv hσ hF g.1 g.2)
  rintro ⟨q, j⟩ - ⟨q', j'⟩ - hne
  rw [Function.onFun, Finset.disjoint_left]
  intro k hk hk'
  simp only [groupReq, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  obtain ⟨hA, hk1, hk2⟩ := hk
  obtain ⟨hA', hk1', hk2'⟩ := hk'
  have hqq : q = q' := hk2.symm.trans hk2'
  subst hqq
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  rcases lt_or_gt_of_ne hjj with h | h
  · exact group_disjoint hv h hA hA' hk1 hk1' hk2
  · exact group_disjoint hv h hA' hA hk1' hk1 hk2

open scoped InstanceNotation in
/-- **`lem:timely`**: the excess of the critical services that are not overdue is at most `L` times the comparator's delay cost. -/
theorem sum_excess_notOverdue_le :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else excessAt input S i) ≤
      L * Schedule.totalDelay input σ := by
  calc ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else excessAt input S i)
      ≤ ∑ i ∈ Finset.range (log input).length,
        L * (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · simp
        · exact excessAt_le hv σ S i
    _ = L * ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then 0 else ∑ q, claimAt input i q) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ L * Schedule.totalDelay input σ :=
        mul_le_mul_of_nonneg_left (sum_claim_notOverdue_le hv hσ hF) (Instance.L_pos hv).le

end Comparator

end

end NotOverdueProof

end PMD

end PagingWithDelay
