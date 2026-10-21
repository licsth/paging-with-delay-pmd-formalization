import PagingWithDelay.Algorithm

/-!
# Basic facts: the standing assumptions, constants, levels, fractional states

`Instance.Valid` collects the assumptions that `Instance` and `Request` carry as fields (`Instance.valid`); the internal lemmas take it as a hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

namespace Instance

variable (input) in
/-- All weights are (integer) powers of two. -/
def PowerOfTwoWeights : Prop :=
  ∀ p, ∃ e : ℤ, w p = 2 ^ e

variable (input) in
/-- The standing assumptions on an instance: positive weights, `0 < k < n`, an initial cache of `k` pages, and delay cost functions that are nondecreasing, continuous and unbounded with `d 0 = 0`. -/
structure Valid : Prop where
  weight_pos : ∀ p, 0 < w p
  cacheSize_pos : 0 < k
  cacheSize_lt : k < Fintype.card Page
  initialCache_card : input.initialCache.card = k
  delay_mono : ∀ ρ ∈ input.requests, Monotone ρ.delay
  delay_continuous : ∀ ρ ∈ input.requests, Continuous ρ.delay
  delay_zero : ∀ ρ ∈ input.requests, ρ.delay 0 = 0
  delay_unbounded : ∀ ρ ∈ input.requests, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ

variable (input) in
/-- Every instance satisfies the standing assumptions. -/
theorem valid : input.Valid where
  weight_pos := input.weight_pos
  cacheSize_pos := input.cacheSize_pos
  cacheSize_lt := input.cacheSize_lt
  initialCache_card := input.initialCache_card
  delay_mono ρ _ := ρ.delay_mono
  delay_continuous ρ _ := ρ.delay_continuous
  delay_zero ρ _ := ρ.delay_zero
  delay_unbounded ρ _ := ρ.delay_unbounded

theorem delta_pos (hv : input.Valid) : 0 < δ := by
  unfold delta; positivity

theorem delta_lt_one (hv : input.Valid) : δ < 1 := by
  unfold delta
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_lt_one (by positivity)]; linarith

theorem L_pos (hv : input.Valid) : 0 < L := by
  unfold Instance.L
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  apply Real.log_pos; linarith

/-- `L = ln (2k+1) ≥ ln 3 ≥ 1`. -/
theorem one_le_L (hv : input.Valid) : 1 ≤ L := by
  unfold Instance.L
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have h3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- `δ ≤ 1/3`. -/
theorem delta_le_third (hv : input.Valid) : δ ≤ 1 / 3 := by
  unfold delta
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `L = ln (2k+1) ≤ ln (3k) = ln k + ln 3 < ln k + 1.1`. -/
theorem L_le_log_add (hv : input.Valid) : L ≤ Real.log k + 11 / 10 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have h3 : Real.log 3 < 11 / 10 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num),
      show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.exp_add]
    calc (3 : ℝ) < 2.7182818283 * (1 + 1 / 10 + (1 / 10) ^ 2 / 2) := by norm_num
      _ ≤ Real.exp 1 * Real.exp (1 / 10) :=
        mul_le_mul Real.exp_one_gt_d9.le (Real.quadratic_le_exp_of_nonneg (by norm_num))
          (by norm_num) (Real.exp_pos 1).le
  have h : Real.log (2 * k + 1) ≤ Real.log (3 * k) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  unfold Instance.L
  linarith

theorem totalWeight_nonneg (hv : input.Valid) : 0 ≤ input.totalWeight :=
  Finset.sum_nonneg fun p _ => (hv.weight_pos p).le

end Instance

namespace PMD


/-- A fractional state: all missing masses in `[δ, 1]`. -/
def IsFrac (input : Instance Page) (x : Page → ℝ) : Prop :=
  ∀ i, δ ≤ x i ∧ x i ≤ 1

/-- A rest state: a fractional state with total missing mass exactly `n - k`. -/
def IsRest (input : Instance Page) (x : Page → ℝ) : Prop :=
  IsFrac input x ∧ ∑ i, x i = restMass input

theorem delta_pos (hv : input.Valid) : 0 < δ := by
  unfold Instance.delta; positivity

theorem delta_lt_one (hv : input.Valid) : δ < 1 := by
  unfold Instance.delta
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  rw [div_lt_one (by positivity)]; linarith

theorem L_pos (hv : input.Valid) : 0 < L := by
  unfold Instance.L
  have : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  apply Real.log_pos; linarith

theorem log_delta (hv : input.Valid) : Real.log δ = -L := by
  unfold Instance.delta Instance.L
  rw [one_div, Real.log_inv]

theorem delta_mul_exp_L (hv : input.Valid) : δ * Real.exp L = 1 := by
  unfold Instance.delta Instance.L
  rw [Real.exp_log (by positivity)]
  field_simp

theorem levelWeight_pos (e : ℤ) : 0 < levelWeight e := by
  unfold levelWeight; positivity

theorem levelWeight_succ (e : ℤ) : levelWeight (e + 1) = 2 * levelWeight e := by
  unfold levelWeight
  rw [zpow_add₀ (by norm_num), zpow_one, mul_comm]

/-- A page has level `≤ e` iff its weight is at most `2^e`. -/
theorem level_le_iff (hv : input.Valid) (p : Page) (e : ℤ) :
    level input p ≤ e ↔ w p ≤ levelWeight e := by
  unfold level levelWeight
  have := Int.le_zpow_iff_clog_le (b := 2) (by norm_num) (x := e) (hv.weight_pos p)
  push_cast at this
  exact this.symm

theorem levelWeight_level (hv : input.Valid) (h2 : input.PowerOfTwoWeights) (p : Page) :
    levelWeight (level input p) = w p := by
  obtain ⟨e, he⟩ := h2 p
  unfold levelWeight level
  rw [he]
  have := Int.clog_zpow (R := ℝ) (b := 2) (by norm_num) e
  push_cast at this
  rw [this]

theorem minLevel_le (p : Page) : minLevel input ≤ level input p :=
  ciInf_le (Set.finite_range _).bddBelow p

theorem le_maxLevel (p : Page) : level input p ≤ maxLevel input :=
  le_ciSup (Set.finite_range _).bddAbove p

theorem card_pos (hv : input.Valid) : 0 < Fintype.card Page :=
  lt_of_le_of_lt (Nat.zero_le _) hv.cacheSize_lt

theorem nonempty_page (hv : input.Valid) : Nonempty Page :=
  Fintype.card_pos_iff.mp (card_pos hv)

theorem minLevel_le_maxLevel (hv : input.Valid) : minLevel input ≤ maxLevel input := by
  obtain ⟨p⟩ := nonempty_page hv
  exact (minLevel_le p).trans (le_maxLevel p)

/-- The initial page exists and lies outside `C₀`. -/
theorem initialPage_spec (hv : input.Valid) :
    ∃ p₀, initialPage input = some p₀ ∧ p₀ ∉ input.initialCache := by
  have hex : ∃ i, i ∉ input.initialCache := by
    by_contra h
    push_neg at h
    have : Finset.univ ⊆ input.initialCache := fun i _ => h i
    have := Finset.card_le_card this
    rw [Finset.card_univ, hv.initialCache_card] at this
    exact absurd hv.cacheSize_lt (not_lt.2 this)
  obtain ⟨i, hi⟩ := hex
  cases h : initialPage input with
  | none =>
      exfalso
      unfold initialPage at h
      have := List.find?_eq_none.1 h i (Finset.mem_toList.2 (Finset.mem_univ i))
      simp [hi] at this
  | some p₀ =>
      refine ⟨p₀, rfl, ?_⟩
      unfold initialPage at h
      simpa using List.find?_some h

theorem initialState_isRest (hv : input.Valid) : IsRest input (initialState input) := by
  obtain ⟨p₀, hp₀, hp₀C⟩ := initialPage_spec hv
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hv.cacheSize_pos
  have hd := delta_pos hv
  have hd1 : δ * (2 * k + 1) = 1 := by
    unfold Instance.delta; field_simp
  have heq : initialState input = fun i =>
      (if i ∈ input.initialCache then δ else 1) -
        (if i = p₀ then k * δ else 0) := by
    funext i
    unfold initialState
    rw [hp₀]
    by_cases hi : i = p₀
    · subst hi; simp [hp₀C]
    · have : ¬ some p₀ = some i := fun h => hi (Option.some_injective _ h).symm
      split_ifs <;> simp_all
  refine ⟨fun i => ?_, ?_⟩
  · rw [heq]
    by_cases hi : i = p₀
    · subst hi; simp only [hp₀C, if_false, if_true]; constructor <;> nlinarith
    · simp only [hi, if_false, sub_zero]
      split_ifs
      · exact ⟨le_rfl, (delta_lt_one hv).le⟩
      · exact ⟨(delta_lt_one hv).le, le_rfl⟩
  · rw [heq, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ p₀, if_pos (Finset.mem_univ _)]
    have hc : (Finset.univ.filter (fun i => i ∈ input.initialCache)) = input.initialCache := by
      ext; simp
    have hc2 : (Finset.univ.filter (fun i => i ∉ input.initialCache)).card
        = Fintype.card Page - k := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hc,
        hv.initialCache_card, Finset.card_univ]
    rw [hc, hv.initialCache_card, hc2, nsmul_eq_mul, nsmul_eq_mul,
      Nat.cast_sub hv.cacheSize_lt.le]
    unfold restMass
    ring

end PMD

end PagingWithDelay
