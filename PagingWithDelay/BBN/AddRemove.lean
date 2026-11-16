import PagingWithDelay.BBN.Defs

/-!
# Fixing the marginals page by page

Each page `i` independently stays/leaves (if cached) or enters/stays out (if not cached), with
probabilities chosen so that its marginal becomes `y' i`. The kernel is a product of Bernoullis.
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace PagingWithDelay.BBN.AddRemove

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- Sum over all sets of a product of per-element choices. -/
theorem sum_prod_ite (f g : Page → ℝ) :
    ∑ C : Finset Page, ∏ i, (if i ∈ C then f i else g i) = ∏ i, (f i + g i) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun C _ => ?_
  have := Finset.prod_piecewise (Finset.univ : Finset Page) C f g
  simp only [Finset.piecewise, Finset.univ_inter] at this
  rw [this, Finset.compl_eq_univ_sdiff]

/-- The probability of `C` under independent inclusions with probabilities `t`. -/
def prodW (t : Page → ℝ) (C : Finset Page) : ℝ := ∏ i, (if i ∈ C then t i else 1 - t i)

theorem prodW_nonneg {t : Page → ℝ} (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (C : Finset Page) :
    0 ≤ prodW t C :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith [ht i]

theorem sum_prodW (t : Page → ℝ) : ∑ C, prodW t C = 1 := by
  unfold prodW; rw [sum_prod_ite]; simp

theorem sum_prodW_mem (t : Page → ℝ) (j : Page) :
    ∑ C, prodW t C * (if j ∈ C then 1 else 0) = t j := by
  have h : ∀ C : Finset Page, prodW t C * (if j ∈ C then 1 else 0) =
      ∏ i, (if i ∈ C then t i else (if i = j then 0 else 1 - t i)) := by
    intro C
    unfold prodW
    by_cases hj : j ∈ C
    · rw [if_pos hj, mul_one]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ C
      · simp [hi]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [hi, this]
    · rw [if_neg hj, mul_zero, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  simp_rw [h]
  rw [sum_prod_ite]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem sum_prodW_affine (t : Page → ℝ) (j : Page) (c d : ℝ) :
    ∑ C, prodW t C * (c + d * (if j ∈ C then 1 else 0)) = c + d * t j := by
  have h : ∀ C, prodW t C * (c + d * (if j ∈ C then 1 else 0)) =
      c * prodW t C + d * (prodW t C * (if j ∈ C then 1 else 0)) := fun C => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_prodW, sum_prodW_mem, mul_one]

theorem sum_prodW_lin (t : Page → ℝ) (s : Finset Page) (c d : Page → ℝ) :
    ∑ C, prodW t C * ∑ i ∈ s, (c i + d i * (if i ∈ C then 1 else 0)) =
      ∑ i ∈ s, (c i + d i * t i) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_prodW_affine t i (c i) (d i)

/-- The product kernel as a `PMF`. -/
def prodPMF (t : Page → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : PMF (Finset Page) :=
  PMF.ofFintype (fun C => ENNReal.ofReal (prodW t C)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun C _ => prodW_nonneg ht C), sum_prodW,
      ENNReal.ofReal_one])

theorem prodPMF_toReal (t : Page → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (C : Finset Page) :
    (prodPMF t ht C).toReal = prodW t C := by
  simp [prodPMF, ENNReal.toReal_ofReal (prodW_nonneg ht C)]

theorem pmf_sum_toReal {α : Type*} [Fintype α] (μ : PMF α) : ∑ x, (μ x).toReal = 1 := by
  have h := PMF.tsum_coe μ
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x), h, ENNReal.toReal_one]

variable {w : Page → ℝ}

theorem margX_nonneg (μ : PMF (Finset Page × Prof w)) (i : Page) : 0 ≤ margX μ i :=
  Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem margX_le_one (μ : PMF (Finset Page × Prof w)) (i : Page) : margX μ i ≤ 1 := by
  rw [← pmf_sum_toReal μ]
  refine Finset.sum_le_sum fun x _ => ?_
  have := (μ x).toReal_nonneg
  split_ifs <;> nlinarith

theorem sum_ite_mem (μ : PMF (Finset Page × Prof w)) (i : Page) (c d : ℝ) :
    ∑ x, (μ x).toReal * (if i ∈ x.1 then c else d) = c * margX μ i + d * (1 - margX μ i) := by
  have h : ∀ x : Finset Page × Prof w, (μ x).toReal * (if i ∈ x.1 then c else d) =
      c * ((μ x).toReal * (if i ∈ x.1 then 1 else 0)) + d * (μ x).toReal -
        d * ((μ x).toReal * (if i ∈ x.1 then 1 else 0)) := by
    intro x; split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, pmf_sum_toReal]
  unfold margX; ring

/-- Probability of adding a missing page. -/
def addP (y y' : Page → ℝ) (i : Page) : ℝ := max 0 (y' i - y i) / (1 - y i)

/-- Probability of removing a cached page. -/
def remP (y y' : Page → ℝ) (i : Page) : ℝ := max 0 (y i - y' i) / y i

theorem addP_mul {y y' : Page → ℝ} (_hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : addP y y' i * (1 - y i) = max 0 (y' i - y i) := by
  unfold addP
  by_cases h : 1 - y i = 0
  · rw [h, mul_zero]; have := hy' i; rw [eq_comm, max_eq_left]; linarith
  · field_simp

theorem remP_mul {y y' : Page → ℝ} (_hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : remP y y' i * y i = max 0 (y i - y' i) := by
  unfold remP
  by_cases h : y i = 0
  · rw [h, mul_zero]; have := hy' i; rw [eq_comm, max_eq_left]; linarith
  · field_simp

theorem addP_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : 0 ≤ addP y y' i ∧ addP y y' i ≤ 1 := by
  have h1 := hy i; have h2 := hy' i
  unfold addP
  refine ⟨div_nonneg (le_max_left _ _) (by linarith), div_le_one_of_le₀ ?_ (by linarith)⟩
  exact max_le (by linarith) (by linarith)

theorem remP_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : 0 ≤ remP y y' i ∧ remP y y' i ≤ 1 := by
  have h1 := hy i; have h2 := hy' i
  unfold remP
  refine ⟨div_nonneg (le_max_left _ _) h1.1, div_le_one_of_le₀ ?_ h1.1⟩
  exact max_le h1.1 (by linarith)

/-- The inclusion probability of page `i` after the step, given the old cache `C`. -/
def incl (y y' : Page → ℝ) (C : Finset Page) (i : Page) : ℝ :=
  if i ∈ C then 1 - remP y y' i else addP y y' i

theorem incl_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) (C : Finset Page) (i : Page) :
    0 ≤ incl y y' C i ∧ incl y y' C i ≤ 1 := by
  unfold incl
  have := addP_mem hy hy' i; have := remP_mem hy hy' i
  split_ifs <;> constructor <;> linarith

/-- Pointwise shortfall bound. -/
theorem shortfall_le (m : ℝ) (s C C' : Finset Page) :
    max 0 (m - ((C' ∩ s).card : ℝ)) ≤ max 0 (m - ((C ∩ s).card : ℝ)) +
      ∑ i ∈ s, (if i ∈ C then 1 - (if i ∈ C' then 1 else 0) else 0) := by
  have hsum : ∑ i ∈ s, (if i ∈ C then 1 - (if i ∈ C' then (1 : ℝ) else 0) else 0) =
      ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i ∈ C <;> by_cases h2 : i ∈ C' <;> simp [h1, h2]
  have hcard : (C ∩ s).card ≤ (C' ∩ s).card + (s.filter (fun i => i ∈ C ∧ i ∉ C')).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    rw [Finset.mem_inter] at hi
    by_cases h : i ∈ C'
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h, hi.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hi.2, hi.1, h⟩)
  rw [hsum]
  have : ((C ∩ s).card : ℝ) ≤ ((C' ∩ s).card : ℝ) +
      ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := Nat.cast_nonneg _
  refine max_le (by positivity) ?_
  linarith [le_max_right 0 (m - ((C ∩ s).card : ℝ))]

end PagingWithDelay.BBN.AddRemove

namespace PagingWithDelay.BBN

open AddRemove

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

theorem add_remove (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) (y' : Page → ℝ)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) (μ : PMF (Finset Page × Prof w)) :
    ∃ κ : Finset Page × Prof w → PMF (Finset Page),
      (∀ i, ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * (if i ∈ C' then 1 else 0) = y' i) ∧
      (∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ i, w i * max 0 (y' i - margX μ i)) ∧
      (∀ v : WClass w,
        ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal *
            max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C' v : ℕ) : ℝ)) ≤
          ∑ x, (μ x).toReal * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ i ∈ cls w v, max 0 (margX μ i - y' i)) := by
  set y := margX μ with hydef
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i => ⟨margX_nonneg μ i, margX_le_one μ i⟩
  have ht := incl_mem hy hy'
  refine ⟨fun x => prodPMF (incl y y' x.1) (ht x.1), ?_, ?_, ?_⟩
  · -- marginals
    intro i
    simp_rw [prodPMF_toReal, mul_assoc, ← Finset.mul_sum, sum_prodW_mem]
    unfold incl
    rw [sum_ite_mem]
    have h1 := addP_mul hy hy' i; have h2 := remP_mul hy hy' i
    rw [← hydef]
    have : max 0 (y' i - y i) - max 0 (y i - y' i) = y' i - y i := by
      rcases le_total (y' i) (y i) with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    nlinarith
  · -- fetch cost
    apply le_of_eq
    have hpt : ∀ (x : Finset Page × Prof w) (C' : Finset Page), ∑ i ∈ C' \ x.1, w i =
        ∑ i, (if i ∈ x.1 then 0 else w i) * (if i ∈ C' then 1 else 0) := by
      intro x C'
      rw [show (∑ i, (if i ∈ x.1 then 0 else w i) * (if i ∈ C' then (1 : ℝ) else 0)) =
          ∑ i, (if i ∈ C' \ x.1 then w i else 0) from Finset.sum_congr rfl fun i _ => by
            by_cases h1 : i ∈ x.1 <;> by_cases h2 : i ∈ C' <;> simp [h1, h2],
        Finset.sum_ite_mem, Finset.univ_inter]
    have hx : ∀ x : Finset Page × Prof w,
        ∑ C', (μ x).toReal * (prodPMF (incl y y' x.1) (ht x.1) C').toReal * ∑ i ∈ C' \ x.1, w i =
          ∑ i, (μ x).toReal * (if i ∈ x.1 then 0 else w i * addP y y' i) := by
      intro x
      simp_rw [hpt, prodPMF_toReal, mul_assoc, ← Finset.mul_sum]
      have := sum_prodW_lin (incl y y' x.1) Finset.univ (fun _ => 0)
        (fun i => if i ∈ x.1 then 0 else w i)
      simp only [zero_add] at this
      rw [this]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold incl; split_ifs <;> simp
    simp_rw [hx]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_ite_mem, ← hydef, zero_mul, zero_add, mul_assoc, addP_mul hy hy']
  · intro v
    calc _ ≤ ∑ x, ∑ C', (μ x).toReal * (prodPMF (incl y y' x.1) (ht x.1) C').toReal *
            (max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
              ∑ i ∈ cls w v, ((if i ∈ x.1 then 1 else 0) +
                (if i ∈ x.1 then -1 else 0) * (if i ∈ C' then 1 else 0))) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun C' _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := shortfall_le ((x.2 v : ℕ) : ℝ) (cls w v) x.1 C'
          have he : ∀ i, (if i ∈ x.1 then 1 - (if i ∈ C' then (1 : ℝ) else 0) else 0) =
              (if i ∈ x.1 then 1 else 0) + (if i ∈ x.1 then -1 else 0) *
                (if i ∈ C' then 1 else 0) := fun i => by split_ifs <;> ring
          simp_rw [he] at h
          exact h
      _ = ∑ x, (μ x).toReal * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ x, ∑ i ∈ cls w v, (μ x).toReal * (if i ∈ x.1 then remP y y' i else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp_rw [prodPMF_toReal, mul_assoc, ← Finset.mul_sum]
          rw [← mul_add]
          congr 1
          rw [Finset.sum_congr rfl (fun C _ => mul_add _ _ _), Finset.sum_add_distrib,
            ← Finset.sum_mul, sum_prodW, one_mul, sum_prodW_lin]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold incl; split_ifs <;> ring
      _ = _ := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sum_ite_mem, ← hydef, zero_mul, add_zero, remP_mul hy hy']

end PagingWithDelay.BBN
