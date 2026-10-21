import PagingWithDelay.Analysis.Pending

/-!
# Chargeable visits (`lem:miss`, `lem:chargeable`)

* `missW_le_chargeW` (`lem:miss`): every miss service is chargeable. By the trigger, the pending requests on its page `p` have delay at least `w_p`; either the comparator has served one of them (and `p`, not cached, was evicted since: (i)), or none is served yet, so each has comparator delay cost at least its current delay (ii).
* `sum_chargeW_le` (`lem:chargeable`): the chargeable visits weigh at most `fetchCost(S) + w(C₀) + ∑_ρ d_ρ(σ ρ - a_ρ)`. Visits with (i) are charged to the comparator's last eviction of their page (distinct for distinct visits); visits with (ii) to the comparator's delay cost of their pending requests (disjoint for distinct visits).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PagingWithDelay

namespace PMD

namespace TeleProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState)
open PagingWithDelay.Schedule (cacheAt evictedAt fetchedAt SwapForm ServedBy IsLastEviction)

open Finset Classical

variable {input : Instance Page} {σ : Request Page → ℝ} {S : Schedule Page}

/-! ### Elementary facts -/

theorem visitPage_lt {i : ℕ} {p : Page} (h : visitPage input i = some p) :
    i < (log input).length := by
  by_contra hi
  simp [visitPage, dif_neg hi] at h

open scoped InstanceNotation in
theorem chargeW_of_chargeable {i : ℕ} {p : Page} (hc : IsChargeable input σ S i)
    (hp : visitPage input i = some p) : chargeW input σ S i = w p := by
  unfold chargeW
  rw [if_pos hc, hp]

theorem chargeW_of_not_chargeable {i : ℕ} (hc : ¬ IsChargeable input σ S i) :
    chargeW input σ S i = 0 := by
  unfold chargeW
  rw [if_neg hc]

theorem chargeW_nonneg (hv : input.Valid) (i : ℕ) : 0 ≤ chargeW input σ S i := by
  unfold chargeW
  split_ifs
  · split
    · exact (hv.weight_pos _).le
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_nonneg (hv : input.Valid) (i : ℕ) : 0 ≤ tripChargeW input σ S i := by
  unfold tripChargeW
  split_ifs with hi
  · split
    · exact chargeW_nonneg hv i
    · exact le_rfl
  · exact le_rfl

/-- A visit of `p` serves all pending requests on `p`. -/
theorem not_pending_of_visit (hv : input.Valid) {i : ℕ} {p : Page}
    (hp : visitPage input i = some p) {ρ : Request Page}
    (hρ : ρ ∈ (snapAt input (i + 1)).pending) : ρ.page ≠ p := by
  have hi := visitPage_lt hp
  unfold visitPage at hp
  rw [dif_pos hi] at hp
  revert hp
  cases hmv : moveAt i hi with
  | critical q =>
    intro hp
    cases hp
    exact ((pending_succ_of_critical hv hi hmv).1 hρ).2
  | trip e π =>
    intro hp
    cases hp
    exact ((pending_succ_of_trip hv hi hmv).1 hρ).2
  | _ => intro hp; cases hp

/-- A request pending at a visit of its page is not pending at any later entry. -/
theorem not_pending_after_visit (hv : input.Valid) {i i' : ℕ} (hii' : i < i') {p : Page}
    (hp : visitPage input i = some p) {ρ : Request Page}
    (ha : ρ.arrival ≤ entryTime input i) (hρ' : ρ ∈ (snapAt input i').pending) :
    ρ.page ≠ p :=
  not_pending_of_visit hv hp (pending_of_later hv hii' hρ' ha)

/-- In swap form, a step evicts at most one page. -/
theorem evicted_unique' {I : Instance Page} (hS : SwapForm I S) {j : ℕ}
    (hj : j < S.length) {p q : Page} (hp : p ∈ evictedAt I S j) (hq : q ∈ evictedAt I S j) :
    p = q := by
  obtain ⟨a, b, ha, hb, hcache⟩ := hS.swap j hj
  have hsucc : Schedule.cacheBeforeStep I S (j + 1) = S[j].cache := by
    simp [Schedule.cacheBeforeStep, List.getElem?_eq_getElem hj]
  unfold evictedAt at hp hq
  rw [hsucc, hcache] at hp hq
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hp hq
  have h1 : p = b := by by_contra hne; exact hp.2.2 hne hp.1
  have h2 : q = b := by by_contra hne; exact hq.2.2 hne hq.1
  rw [h1, h2]

/-! ### `lem:miss` -/

/-- `lem:miss`: a miss service is chargeable, so `missW ≤ chargeW`. -/
theorem missW_le_chargeW (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (hF : S.FeasibleBy input σ) (i : ℕ) :
    missW input S i ≤ chargeW input σ S i := by
  by_cases hi : i < (log input).length
  swap
  · have : missW input S i = 0 := by simp only [missW, dif_neg hi]
    rw [this]; exact chargeW_nonneg hv i
  cases hmv : moveAt i hi with
  | critical p =>
    have hmw : missW input S i =
        if p ∈ cacheAt input S (entryTime input i) then 0
        else input.weight p := by
      simp only [missW, dif_pos hi, hmv]
    rw [hmw]
    split_ifs with hrO
    · exact chargeW_nonneg hv i
    have hvp : visitPage input i = some p := by simp only [visitPage, dif_pos hi, hmv]
    refine le_of_eq (chargeW_of_chargeable ⟨p, hvp, ?_⟩ hvp).symm
    by_cases hserved : ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
        ServedBy input σ S ρ (entryTime input i)
    · exact Or.inl ⟨hrO, hserved⟩
    right
    push_neg at hserved
    obtain ⟨htrig, -, -, -, hti⟩ := critical_facts hv hi hmv
    have h1 : (snapAt input i).claims p + input.weight p ≤
        pageDelay (snapAt input i).pending p (snapAt input i).now := htrig.1
    have h0 := claims_nonneg hv i p
    have h2 := PendingProof.pageDelay_le_sum hv i p (snapAt input i).now
      (fun ρ hρ => (pending_spec hv hρ).2.1)
    have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin input.requests.length =>
          input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = p),
        input.requests[k].delay ((snapAt input i).now - input.requests[k].arrival) ≤
        optDelayOn input σ (snapAt input i) p := by
      unfold optDelayOn
      refine sum_le_sum fun k hk => ?_
      rw [mem_filter] at hk
      have hn := hserved _ hk.2.1 hk.2.2
      rw [hti] at hn
      exact Schedule.delay_le_of_not_servedBy' hF hv k hn
    linarith
  | _ =>
    have : missW input S i = 0 := by simp only [missW, dif_pos hi, hmv]
    rw [this]; exact chargeW_nonneg hv i

/-! ### `lem:chargeable` -/

/-- Condition (i) of `def:chargeable` at entry `i`. -/
def CondI (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page) (i : ℕ) : Prop :=
  ∃ p, visitPage input i = some p ∧
    p ∉ cacheAt input S (entryTime input i) ∧
    ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
      ServedBy input σ S ρ (entryTime input i)

section Charge

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hSw : SwapForm input S)
  (hF : S.FeasibleBy input σ)
include hv hσ hSw hF

open scoped InstanceNotation in
/-- The visits with (i) weigh at most the comparator's evicted weight. -/
theorem sum_condI_le :
    ∑ i ∈ (range (log input).length).filter (CondI input σ S), chargeW input σ S i ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p := by
  set A := (range (log input).length).filter (CondI input σ S) with hA
  have H : ∀ i ∈ A, ∃ j, ∃ p, visitPage input i = some p ∧
      chargeW input σ S i = w p ∧
      IsLastEviction input S p (entryTime input i) j ∧
      ∃ ρ ∈ (snapAt input i).pending, ρ.page = p ∧
        ∃ hj : j < S.length, ρ.arrival ≤ S[j].time := by
    intro i hi
    obtain ⟨-, p, hvp, hrO, ρ, hρ, hρp, hsv⟩ := mem_filter.1 hi
    have hcw := chargeW_of_chargeable (Or.inl ⟨hrO, ρ, hρ, hρp, hsv⟩ |> fun h => ⟨p, hvp, h⟩) hvp
    subst hρp
    obtain ⟨j, hj, hj'⟩ := Schedule.exists_lastEviction hv hSw hF hsv hrO
    exact ⟨j, ρ.page, hvp, hcw, hj, ρ, hρ, rfl, hj'⟩
  choose! jOf hjOf using H
  set F : ℕ → ℝ := fun j => ∑ p ∈ evictedAt input S j, w p
    with hFdef
  have hF0 : ∀ j, 0 ≤ F j := fun j => sum_nonneg fun p _ => (hv.weight_pos p).le
  have h1 : ∑ i ∈ A, chargeW input σ S i ≤ ∑ i ∈ A, F (jOf i) := by
    apply sum_le_sum
    intro i hi
    obtain ⟨p, -, hcw, ⟨-, -, hev, -⟩, -⟩ := hjOf i hi
    rw [hcw]
    exact single_le_sum (f := fun p => w p) (fun p _ => (hv.weight_pos p).le) hev
  have hinj_lt : ∀ i ∈ A, ∀ i' ∈ A, i < i' → jOf i ≠ jOf i' := by
    intro i hi i' hi' hlt heq
    obtain ⟨p, hvp, -, ⟨hj, ht, hev, -⟩, -⟩ := hjOf i hi
    obtain ⟨p', -, -, ⟨-, -, hev', -⟩, ρ', hρ', hρp', hj', ha'⟩ := hjOf i' hi'
    rw [← heq] at hev'
    have ha'' : ρ'.arrival ≤ S[jOf i].time := by simpa [heq] using ha'
    have hpage : p' = p := evicted_unique' hSw hj hev' hev
    exact not_pending_after_visit hv hlt hvp (ha''.trans ht) hρ' (hρp'.trans hpage)
  have hinj : Set.InjOn jOf A := by
    intro i hi i' hi' heq
    rcases lt_trichotomy i i' with hlt | hlt | hlt
    · exact absurd heq (hinj_lt i hi i' hi' hlt)
    · exact hlt
    · exact absurd heq.symm (hinj_lt i' hi' i hi hlt)
  have h2 : ∑ i ∈ A, F (jOf i) = ∑ j ∈ A.image jOf, F j := (sum_image hinj).symm
  have h3 : ∑ j ∈ A.image jOf, F j ≤ ∑ j ∈ range S.length, F j := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hj
      obtain ⟨-, -, -, ⟨hj, -⟩, -⟩ := hjOf i hi
      exact mem_range.2 hj
    · intro j _ _
      exact hF0 j
  have h4 := Schedule.sum_evicted_le hv hSw
  calc ∑ i ∈ A, chargeW input σ S i ≤ ∑ i ∈ A, F (jOf i) := h1
    _ = ∑ j ∈ A.image jOf, F j := h2
    _ ≤ ∑ j ∈ range S.length, F j := h3
    _ ≤ _ := h4

/-- The chargeable visits without (i) (which satisfy (ii)) weigh at most the comparator's delay cost. -/
theorem sum_not_condI_le :
    ∑ i ∈ (range (log input).length).filter (fun i => ¬ CondI input σ S i),
        chargeW input σ S i ≤ Schedule.totalDelay input σ := by
  set R := (range (log input).length).filter (fun i => ¬ CondI input σ S i) with hR
  set C := R.filter (IsChargeable input σ S) with hC
  have hRC : ∑ i ∈ R, chargeW input σ S i = ∑ i ∈ C, chargeW input σ S i := by
    refine (sum_filter_of_ne (s := R) (p := IsChargeable input σ S) fun i _ hne => ?_).symm
    by_contra hc
    exact hne (chargeW_of_not_chargeable hc)
  have H : ∀ i ∈ C, ∃ p, visitPage input i = some p ∧
      input.weight p ≤ optDelayOn input σ (snapAt input i) p := by
    intro i hi
    obtain ⟨hiR, hc⟩ := mem_filter.1 hi
    obtain ⟨-, hnI⟩ := mem_filter.1 hiR
    obtain ⟨p, hvp, hAB⟩ := hc
    exact ⟨p, hvp, hAB.resolve_left fun hA => hnI ⟨p, hvp, hA⟩⟩
  have : Nonempty Page := Fintype.card_pos_iff.mp (by have := hv.cacheSize_lt; omega)
  choose! pOf hpOf using H
  set I : ℕ → Finset (Fin input.requests.length) := fun i =>
    Finset.univ.filter (fun k : Fin input.requests.length =>
      input.requests[k] ∈ (snapAt input i).pending ∧ input.requests[k].page = pOf i) with hI
  have hdisj : (C : Set ℕ).PairwiseDisjoint I := by
    have key : ∀ i ∈ C, ∀ i' ∈ C, i < i' → Disjoint (I i) (I i') := by
      intro i hi i' hi' hlt
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [hI, mem_filter, mem_univ, true_and] at hk hk'
      have ha : input.requests[k].arrival ≤ entryTime input i :=
        (pending_spec hv hk.1).2.1.trans (now_le_entryTime hv i)
      exact not_pending_after_visit hv hlt (hpOf i hi).1 ha hk'.1 hk.2
    intro i hi i' hi' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key i hi i' hi' hlt
    · exact (key i' hi' i hi hlt).symm
  rw [hRC]
  refine Schedule.sum_le_totalDelay hv hσ C I hdisj (fun i => chargeW input σ S i) ?_
  intro i hi
  obtain ⟨hvp, hle⟩ := hpOf i hi
  dsimp only
  rw [chargeW_of_chargeable (mem_filter.1 hi).2 hvp]
  exact hle

open scoped InstanceNotation in
/-- `lem:chargeable`: the chargeable visits weigh at most `fetchCost(S) + w(C₀) + ∑_ρ d_ρ(σ ρ - a_ρ)`. -/
theorem sum_chargeW_le :
    ∑ i ∈ range (log input).length, chargeW input σ S i ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p +
        Schedule.totalDelay input σ := by
  rw [← sum_filter_add_sum_filter_not (range (log input).length) (CondI input σ S)]
  have := sum_condI_le hv hσ hSw hF
  have := sum_not_condI_le hv hσ hSw hF
  linarith

end Charge

end TeleProof

end PMD

end PagingWithDelay
