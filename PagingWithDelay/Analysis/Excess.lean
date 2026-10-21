import PagingWithDelay.Analysis.PeriodLevel

/-!
# The excess of overdue services (`prop:excess`, overdue part)

The excess of an overdue miss service `λ` on `p` in the period of `τ` is the sum of its deposits `|λ|_W` over the levels `w_p ≤ W < w_min(O_j)`, at each of which `λ` is a light service. Regrouping by periods and levels, `lem:periodlevel` bounds each group by `(L + 4) W + (3/2) C_{j,W}`; the chargeable round trips of distinct groups are distinct entries, and `∑_j ∑_{W < w_min(O_j)} W ≤ ∑_j w_min(O_j)` is at most the comparator's fetch cost (`lem:lightest`).

No overdue service with positive excess happens before the comparator's first step: its overdue page `q` (with `w_q ≤ w_p ≤ W < w_min(C₀)`) has a pending request served by the comparator while only `C₀` was cached, but `q ∉ C₀`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

namespace ExcessProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight levelWeight_pos minLevel_le)
open PagingWithDelay.Schedule (cacheAt ServedBy stepTimes)
open PagingWithDelay.Schedule (InPer)

open Classical

noncomputable section

/-- The levels whose weight is below every weight cached at `τ`. -/
def lightLevels (input : Instance Page) (S : Schedule Page) (τ : ℝ) :
    Finset ℤ :=
  (Finset.Icc (minLevel input) (maxLevel input)).filter
    (fun e => ∀ q ∈ cacheAt input S τ, levelWeight e < w q)

/-- Distinct powers of two below `2^b` sum to less than `2^b`. -/
theorem sum_levelWeight_lt (s : Finset ℤ) :
    ∀ b : ℤ, (∀ e ∈ s, e < b) → ∑ e ∈ s, levelWeight e < levelWeight b := by
  induction s using Finset.induction_on_max with
  | h0 => intro b _; simpa using levelWeight_pos b
  | step a s ha ih =>
    intro b hb
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have h1 := ih a ha
    have hab : a + 1 ≤ b := hb a (Finset.mem_insert_self a s)
    have h2 : levelWeight (a + 1) ≤ levelWeight b := by
      unfold levelWeight
      exact zpow_le_zpow_right₀ (by norm_num) hab
    rw [PagingWithDelay.PMD.levelWeight_succ] at h2
    linarith

theorem lt_of_levelWeight_lt {e b : ℤ} (h : levelWeight e < levelWeight b) : e < b := by
  by_contra hcon
  push_neg at hcon
  have : levelWeight b ≤ levelWeight e := by
    unfold levelWeight
    exact zpow_le_zpow_right₀ (by norm_num) hcon
  linarith

variable {input : Instance Page} {σ : Request Page → ℝ} {S : Schedule Page}

theorem isLightService_iff {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    IsLightService input e i ↔ level input p ≤ e := by
  constructor
  · rintro ⟨h', p', hm', hle⟩
    have := hm.symm.trans hm'
    cases this
    exact hle
  · intro hle
    exact ⟨h, p, hm, hle⟩

/-- The chargeable level-`e` round trips of the periods and levels are distinct entries: their total weight is at most `∑_l tripChargeW l`. -/
theorem sum_periodTrips_le (hv : input.Valid) :
    ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
        ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l ≤
      ∑ l ∈ Finset.range (log input).length, tripChargeW input σ S l := by
  set N := (log input).length
  set f := fun l => tripChargeW input σ S l with hf
  set cond : ℝ → ℤ → ℕ → Prop := fun τ e l =>
    (∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) ∧
      InPer S τ (entryTime input l) with hcond
  have hrw : ∀ τ e, ∑ l ∈ periodTrips input S τ e, f l =
      ∑ l ∈ Finset.range N, if cond τ e l then f l else 0 := by
    intro τ e
    unfold periodTrips
    rw [Finset.sum_filter]
  simp only [hrw]
  -- swap the sums over the levels and the entries
  have hsw : ∀ τ, ∑ e ∈ lightLevels input S τ, ∑ l ∈ Finset.range N,
      (if cond τ e l then f l else 0) =
      ∑ l ∈ Finset.range N, ∑ e ∈ lightLevels input S τ,
        (if cond τ e l then f l else 0) := fun τ => Finset.sum_comm
  simp only [hsw]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro l _
  by_cases hex : ∃ τ₀ ∈ stepTimes S, ∃ e₀ ∈ lightLevels input S τ₀, cond τ₀ e₀ l
  · obtain ⟨τ₀, hτ₀, e₀, he₀, hc₀⟩ := hex
    rw [Finset.sum_eq_single τ₀]
    · rw [Finset.sum_eq_single e₀]
      · rw [if_pos hc₀]
      · intro e _ hne
        rw [if_neg]
        rintro ⟨⟨h, π, hm⟩, -⟩
        obtain ⟨⟨h', π', hm'⟩, -⟩ := hc₀
        have := hm.symm.trans hm'
        cases this
        exact hne rfl
      · intro h; exact absurd he₀ h
    · intro τ _ hne
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg]
      rintro ⟨-, hper⟩
      exact hne (hper.unique hc₀.2)
    · intro h; exact absurd hτ₀ h
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · exact tripChargeW_nonneg hv l
    · intro τ hτ
      apply Finset.sum_eq_zero
      intro e he
      rw [if_neg (hex τ hτ e he)]

/-- **`prop:excess`, overdue part**: the excess of the overdue services is at most `(3/2) ∑ C_{j,W}` plus `(L + 4)` times the comparator's fetch cost, where `∑ C_{j,W}` is at most the total weight of the chargeable round trips. -/
theorem sum_excess_overdue_le (hv : input.Valid) (h2 : input.PowerOfTwoWeights)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (hSw : Schedule.SwapForm input S)
    (hF : S.FeasibleBy input σ) :
    ∑ i ∈ Finset.range (log input).length,
        (if IsOverdue input σ S i then excessAt input S i else 0) ≤
      3 / 2 * ∑ i ∈ Finset.range (log input).length, tripChargeW input σ S i +
        (L + 4) * S.fetchCost input := by
  set N := (log input).length with hN
  set R : ℕ → ℝ := fun i => ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
      (if i ∈ lightServices input σ S τ e then levelLenAt input i e else 0) with hRdef
  have hRnn : ∀ i, 0 ≤ R i := by
    intro i
    apply Finset.sum_nonneg; intro τ _
    apply Finset.sum_nonneg; intro e _
    split_ifs
    · exact levelLenAt_nonneg i e
    · exact le_rfl
  -- Step A: each excess is the sum of its terms over its period and its levels
  have hA : ∀ i ∈ Finset.range N,
      (if IsOverdue input σ S i then excessAt input S i else 0) ≤ R i := by
    intro i hi
    have hi' : i < N := Finset.mem_range.1 hi
    split_ifs with hov
    swap
    · exact hRnn i
    have hov' := hov
    obtain ⟨h, p, hm, q, hwq, hovq⟩ := hov'
    unfold excessAt
    rw [dif_pos hi', hm]
    simp only
    split_ifs with hmem
    · exact hRnn i
    by_cases hex : ∃ τ, InPer S τ (entryTime input i)
    · obtain ⟨τ₀, hτ₀⟩ := hex
      have hcache := Schedule.InPer.cacheAt_eq hv hSw hτ₀
      calc ∑ e ∈ excessLevels input S p (entryTime input i),
            levelLen input (snapAt input i).x p e
          = ∑ e ∈ lightLevels input S τ₀,
              (if i ∈ lightServices input σ S τ₀ e then levelLenAt input i e else 0) := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext e
              simp only [excessLevels, lightLevels, lightServices, Finset.mem_filter,
                Finset.mem_Icc, Finset.mem_range, hcache, isLightService_iff hi' hm]
              constructor
              · rintro ⟨⟨h1, h2⟩, h3⟩
                exact ⟨⟨⟨(minLevel_le p).trans h1, h2⟩, h3⟩, hi', h1, hov, hτ₀⟩
              · rintro ⟨⟨⟨-, h2⟩, h3⟩, -, h1, -⟩
                exact ⟨⟨h1, h2⟩, h3⟩
            · intro e _
              rw [levelLenAt_of_critical hi' hm]
        _ ≤ R i := Finset.single_le_sum (f := fun τ => ∑ e ∈ lightLevels input S τ,
              (if i ∈ lightServices input σ S τ e then levelLenAt input i e else 0))
            (fun τ _ => by
              apply Finset.sum_nonneg; intro e _
              split_ifs
              · exact levelLenAt_nonneg i e
              · exact le_rfl) hτ₀.1
    · -- no step before the service: then it has no excess levels
      push_neg at hex
      have hall : ∀ step ∈ S, entryTime input i < step.time := by
        intro s hs
        by_contra hle
        push_neg at hle
        obtain ⟨τ, hτ⟩ := Schedule.InPer.exists_of_step ⟨s, hs, hle⟩
        exact hex τ hτ
      have hC0 := Schedule.cacheAt_of_lt hv hSw hall
      have hempty : excessLevels input S p (entryTime input i) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        simp only [excessLevels, Finset.mem_filter, Finset.mem_Icc] at he
        obtain ⟨⟨hle, -⟩, hlt⟩ := he
        obtain ⟨r, -, hrq, hrs⟩ := exists_served_of_overdue hv hovq
        obtain ⟨s, -, -, hst, hcase⟩ := hrs
        rcases hcase with ⟨hC, -⟩ | ⟨j, hj, hjt, -, -⟩
        · have hq : q ∈ cacheAt input S (entryTime input i) := by
            rw [hC0]; rw [← hrq]; exact hC
          have h1 := hlt q hq
          have h2 := (level_le_iff' hv p e).1 hle
          linarith
        · have := hall _ (List.getElem_mem hj)
          linarith
      rw [hempty, Finset.sum_empty]
      exact hRnn i
  -- Step B: regroup by periods and levels
  have hB : ∑ i ∈ Finset.range N, R i =
      ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
        ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e := by
    simp only [hRdef]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro τ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2
      (by unfold lightServices; exact Finset.filter_subset _ _)]
  -- Step C: `lem:periodlevel` for every period and level
  have hC : ∀ τ ∈ stepTimes S, ∀ e ∈ lightLevels input S τ,
      ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e ≤
        (L + 4) * levelWeight e +
          3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l := by
    intro τ _ e he
    simp only [lightLevels, Finset.mem_filter, Finset.mem_Icc] at he
    have := periodLevel_sum hv hσ hSw hF he.2 he.1.2
    linarith
  -- Step E: `lem:lightest`
  have hE : ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ, levelWeight e ≤
      S.fetchCost input := by
    apply Schedule.sum_stepTimes_le hv hSw hF
    intro τ _ q hq
    have hlw := PagingWithDelay.PMD.levelWeight_level hv
      h2 q
    rw [← hlw]
    apply le_of_lt
    apply sum_levelWeight_lt
    intro e he
    simp only [lightLevels, Finset.mem_filter] at he
    exact lt_of_levelWeight_lt ((he.2 q hq).trans_eq hlw.symm)
  -- Step F: the chargeable round trips
  have hFt := sum_periodTrips_le (σ := σ) (S := S) hv
  -- combine
  have hk1 : 0 ≤ L + 4 := by have := L_nonneg' input; linarith
  have hk2 : (0 : ℝ) ≤ 3 / 2 := by norm_num
  calc ∑ i ∈ Finset.range N, (if IsOverdue input σ S i then excessAt input S i else 0)
      ≤ ∑ i ∈ Finset.range N, R i := Finset.sum_le_sum hA
    _ = ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
          ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e := hB
    _ ≤ ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
          ((L + 4) * levelWeight e +
            3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l) :=
        Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun e he => hC τ hτ e he
    _ = (L + 4) * ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ, levelWeight e +
          3 / 2 * ∑ τ ∈ stepTimes S, ∑ e ∈ lightLevels input S τ,
            ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hE hk1
        have := mul_le_mul_of_nonneg_left hFt hk2
        linarith

end

end ExcessProof

end PMD

end PagingWithDelay
