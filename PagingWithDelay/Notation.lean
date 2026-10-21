import PagingWithDelay.Model

/-!
# Notation of the paper

`open scoped PagingWithDelay.InstanceNotation` lets a section write the parameters of the instance named `input` as in the paper: `w i` for the weight `wᵢ`, `k` for the cache size, `δ` and `L`. The notation is unhygienic: it refers to whatever variable is called `input` at the use site. While it is open, `w`, `k`, `δ` and `L` cannot be variable names.
-/

namespace PagingWithDelay

/-- `L = ln (2k+1)`, the logarithm of the paper (`L ≤ ln k + 1.1`, `Instance.L_le_log_add`). -/
noncomputable def Instance.L {Page : Type*} [Fintype Page] (input : Instance Page) : ℝ :=
  Real.log (2 * input.cacheSize + 1)

/-- The threshold `δ = 1/(2k+1)`: a page with missing mass `δ` counts as cached. -/
noncomputable def Instance.delta {Page : Type*} [Fintype Page] (input : Instance Page) : ℝ :=
  1 / (2 * input.cacheSize + 1)

namespace InstanceNotation

set_option hygiene false

/-- The weight `wᵢ` of page `i`. -/
scoped notation "w" => input.weight
/-- The cache size `k`. -/
scoped notation "k" => input.cacheSize
/-- The threshold `δ = 1/(2k+1)`. -/
scoped notation "δ" => input.delta
/-- The logarithm `L = ln (2k+1)`. -/
scoped notation "L" => input.L

end InstanceNotation

end PagingWithDelay
