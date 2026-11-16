import PagingWithDelay.Imports
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Online rounding for weighted paging (Bansal–Buchbinder–Naor): definitions

The proof of the online rounding theorem of Bansal, Buchbinder and Naor (*A primal-dual randomized
algorithm for weighted paging*, Theorem 4.1) in `PagingWithDelay/BBN/`. This is a formalization of
their proof, not new mathematics.

## The class `𝒟(y)` (BBN, proof of Theorem 4.1)

Pages are grouped into *weight classes* `v` (the distinct values of `w`). For a fractional cache `y`
let `S_≤(v) = ∑_{w q ≤ v} y q` and `S_<(v) = ∑_{w q < v} y q`. For `α ∈ [0,1)` the cache `C(α)` of
BBN holds `n_v(α) = ⌈S_≤(v) - α⌉ - ⌈S_<(v) - α⌉` pages of class `v` (the number of points of
`α + ℤ` in the class interval `[S_<(v), S_≤(v))`). We only remember the *law* of this profile:
`D ∈ 𝒟(y)` iff the class profile of a cache drawn from `D` has the law of `n(α)` for uniform `α`,
and the marginals of `D` are `y`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators

namespace PagingWithDelay.BBN

section Pages

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- `𝒫`: fractional caches `y ∈ [0,1]ⁿ` with total mass `k`. -/
def fracCaches (k : ℕ) : Set (Page → ℝ) :=
  {y | (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = k}

/-- The indicator vector of a set of pages. -/
def indicator (C : Finset Page) (i : Page) : ℝ := if i ∈ C then 1 else 0

/-- `Π(Q)`: the marginals `Pr_{C ∼ Q}[i ∈ C]`. -/
def marginal (Q : PMF (Finset Page)) (i : Page) : ℝ :=
  ∑ C : Finset Page, if i ∈ C then (Q C).toReal else 0

/-- The weight classes: the distinct values of `w`. -/
abbrev WClass (w : Page → ℝ) := {v : ℝ // v ∈ Finset.univ.image w}

/-- A class profile: a number of pages for each weight class (at most the number of pages). -/
abbrev Prof (w : Page → ℝ) := WClass w → Fin (Fintype.card Page + 1)

/-- The pages of weight `v`. -/
def cls (w : Page → ℝ) (v : ℝ) : Finset Page := Finset.univ.filter (fun q => w q = v)

/-- The mass of `y` on the class of weight `v`. -/
def classMass (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ cls w v, y q

/-- The class profile of a cache: the number of its pages in each weight class. -/
def profile (w : Page → ℝ) (C : Finset Page) : Prof w := fun v =>
  ⟨(C ∩ cls w v).card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩

/-- `S_≤(v)`: the mass of `y` on pages of weight at most `v`. -/
def massLE (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ Finset.univ.filter (fun q => w q ≤ v), y q

/-- `S_<(v)`: the mass of `y` on pages of weight less than `v`. -/
def massLT (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ Finset.univ.filter (fun q => w q < v), y q

/-- BBN's profile at `α`: `n_v(α) = ⌈S_≤(v) - α⌉ - ⌈S_<(v) - α⌉` (truncated to `[0, #pages]`,
which never bites for fractional caches and `α ∈ [0,1)`). -/
def slots (w y : Page → ℝ) (α : ℝ) : Prof w := fun v =>
  ⟨min (⌈massLE w y v - α⌉ - ⌈massLT w y v - α⌉).toNat (Fintype.card Page), by omega⟩

end Pages

/-- The uniform distribution on `[0,1)`. -/
def unif : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

section Laws

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

theorem measurable_slots (w y : Page → ℝ) : Measurable (slots w y) := by
  refine measurable_pi_lambda _ fun v => ?_
  have h1 : Measurable fun α : ℝ => ⌈massLE w y v - α⌉ :=
    Int.measurable_ceil.comp (measurable_const.sub measurable_id)
  have h2 : Measurable fun α : ℝ => ⌈massLT w y v - α⌉ :=
    Int.measurable_ceil.comp (measurable_const.sub measurable_id)
  exact (Measurable.of_discrete (f := fun z : ℤ × ℤ =>
    (⟨min (z.1 - z.2).toNat (Fintype.card Page), by omega⟩ : Fin (Fintype.card Page + 1)))).comp
    (h1.prodMk h2)

instance (w y : Page → ℝ) : IsProbabilityMeasure (unif.map (slots w y)) :=
  Measure.isProbabilityMeasure_map (measurable_slots w y).aemeasurable

instance (w y y' : Page → ℝ) :
    IsProbabilityMeasure (unif.map (fun α => (slots w y α, slots w y' α))) :=
  Measure.isProbabilityMeasure_map ((measurable_slots w y).prodMk (measurable_slots w y')).aemeasurable

/-- The law of BBN's profile `n(α)` for uniform `α ∈ [0,1)`. -/
def profLaw (w y : Page → ℝ) : PMF (Prof w) := (unif.map (slots w y)).toPMF

/-- The coupling of the profiles for `y` and `y'` through the same `α`. -/
def rhoLaw (w y y' : Page → ℝ) : PMF (Prof w × Prof w) :=
  (unif.map (fun α => (slots w y α, slots w y' α))).toPMF

/-- `𝒟(y)`: the profile of the cache has the law of BBN's `n(α)`, and the marginals are `y`. -/
def InClass (w y : Page → ℝ) (D : PMF (Finset Page)) : Prop :=
  D.map (profile w) = profLaw w y ∧ marginal D = y

/-- The marginals of the cache coordinate of a distribution on (cache, target profile) pairs. -/
def margX {w : Page → ℝ} (μ : PMF (Finset Page × Prof w)) (i : Page) : ℝ :=
  ∑ x, (μ x).toReal * (if i ∈ x.1 then 1 else 0)

end Laws

end PagingWithDelay.BBN
