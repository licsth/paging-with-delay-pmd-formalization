import PagingWithDelay.Basic

/-!
# The hole of a preemptive service

The hole raises only pages of weight `≤ 2^e`, each by the same fraction of its cached mass, stays below `1`, and — if these pages hold cached mass at least `1 - δ` — raises by exactly `1 - δ`, so its closing cost is at most `(1 - δ) 2^e`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page] {input : Instance Page}

variable (input) in
/-- The closing cost `∑ᵢ wᵢ (x^hole_i - x_i)`: the fetch cost of closing the hole opened from `x`, at most the payment `W (1 - δ)` (`closingCost_le`). -/
noncomputable def closingCost (x : Page → ℝ) (e : ℤ) : ℝ :=
  ∑ i, w i * (hole input x e i - x i)

/-! ### The hole -/

section

variable (hv : input.Valid) {x : Page → ℝ} (hx : IsFrac input x) (e : ℤ)
include hv hx

/-- The cached mass `∑_{i : w_i ≤ W} (1 - x_i)` of the pages a level-`W` hole raises is nonnegative. -/
theorem lightMass_nonneg :
    0 ≤ ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i) :=
  Finset.sum_nonneg fun i _ => by linarith [(hx i).2]

theorem holeFraction_nonneg : 0 ≤ holeFraction input x e :=
  le_min zero_le_one
    (div_nonneg (by linarith [delta_lt_one hv]) (lightMass_nonneg hv hx e))

theorem holeFraction_le_one : holeFraction input x e ≤ 1 := min_le_left _ _

theorem hole_bounds : (∀ i, x i ≤ hole input x e i) ∧ (∀ i, hole input x e i ≤ 1) := by
  have h0 := holeFraction_nonneg hv hx e
  have h1 := holeFraction_le_one hv hx e
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> unfold hole <;> split_ifs
  · nlinarith [(hx i).2]
  · exact le_rfl
  · nlinarith [(hx i).2]
  · exact (hx i).2

theorem le_hole (i : Page) : x i ≤ hole input x e i := (hole_bounds hv hx e).1 i

theorem hole_le_one (i : Page) : hole input x e i ≤ 1 := (hole_bounds hv hx e).2 i

theorem hole_isFrac : IsFrac input (hole input x e) := fun i =>
  ⟨(hx i).1.trans (le_hole hv hx e i), hole_le_one hv hx e i⟩

theorem hole_eq_of_lt_level {i : Page} (hi : e < level input i) : hole input x e i = x i :=
  if_neg (by omega)

/-- The hole raises the pages of weight `≤ W` by `min (1 - δ) (∑_{i : w_i ≤ W} (1 - x_i))` in total. -/
theorem hole_sum :
    ∑ i, hole input x e i = ∑ i, x i +
      min (1 - δ) (∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) := by
  set S := ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)
  have hS : 0 ≤ S := lightMass_nonneg hv hx e
  have hδ : 0 < 1 - δ := by linarith [delta_lt_one hv]
  have hraise : ∑ i, (hole input x e i - x i) = holeFraction input x e * S := by
    rw [Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by unfold hole; split_ifs <;> ring
  have hθ : holeFraction input x e * S = min (1 - δ) S := by
    rcases hS.eq_or_lt with h | h
    · rw [← h, mul_zero, min_eq_right hδ.le]
    · unfold holeFraction
      rw [min_mul_of_nonneg _ _ hS, one_mul, div_mul_cancel₀ _ h.ne', min_comm]
  linarith [Finset.sum_sub_distrib (s := Finset.univ) (f := hole input x e) (g := x)]

theorem closingCost_le : closingCost input x e ≤ (1 - δ) * levelWeight e := by
  have h1 : closingCost input x e ≤ ∑ i, levelWeight e * (hole input x e i - x i) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : level input i ≤ e
    · apply mul_le_mul_of_nonneg_right ((level_le_iff hv i e).mp hi)
      linarith [le_hole hv hx e i]
    · rw [hole_eq_of_lt_level hv hx e (by omega)]; simp
  have h2 : ∑ i, (hole input x e i - x i) ≤ 1 - δ := by
    rw [Finset.sum_sub_distrib, hole_sum hv hx e]
    linarith [min_le_left (1 - δ)
      (∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i))]
  rw [← Finset.mul_sum] at h1
  nlinarith [levelWeight_pos e]

/-- Opening the hole fetches nothing. -/
theorem hole_fetch_open :
    ∑ i, w i * max 0 (x i - hole input x e i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [max_eq_left (by linarith [le_hole hv hx e i]), mul_zero]

/-- Closing the hole fetches exactly the closing cost. -/
theorem hole_fetch_close :
    ∑ i, w i * max 0 (hole input x e i - x i) = closingCost input x e := by
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_right (by linarith [le_hole hv hx e i])]

/-- Under the second preemptive service condition the hole has total size exactly `1 - δ`. -/
theorem sum_hole (hcond : 1 - δ ≤
      ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e), (1 - x i)) :
    ∑ i, hole input x e i = ∑ i, x i + (1 - δ) := by
  rw [hole_sum hv hx e, min_eq_left hcond]

end

end PMD

end PagingWithDelay
