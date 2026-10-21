import PagingWithDelay.BBN

set_option linter.unusedSectionVars false

/-!
# The rounding map (`lem:map`) and the lazy fractional caches

The fractional states `x ∈ [δ, 1]ⁿ` of `PMD` (missing masses, `∑ᵢ xᵢ ≥ n - k`, `δ = 1/(2k+1)`) are turned into fractional caches for `cor:rounding`:
* `zmap δ x`: `zᵢ = max 0 (2 uᵢ - 1)` with `uᵢ = (1 - xᵢ)/(1 - δ)` (`lem:map`), a cached mass in `[0,1]` with `zᵢ = 1` if `xᵢ = δ`, total `≤ k`;
* `lazySeq k zs`: the lazy fractional caches `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾` of total mass exactly `k`; `y⁽⁰⁾ = z⁽⁰⁾`, and `y⁽ᵛ⁺¹⁾ = lazyStep k y⁽ᵛ⁾ z⁽ᵛ⁺¹⁾` raises each `yᵢ` to `max yᵢ z'ᵢ`, then lowers the excess over `z'` by a common fraction until the total is `k`.
-/

namespace PagingWithDelay

namespace Rounding

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The rounding map of `lem:map`: `zᵢ = max 0 (2 (1 - xᵢ)/(1 - δ) - 1)`. -/
noncomputable def zmap (δ : ℝ) (x : Page → ℝ) : Page → ℝ :=
  fun i => max 0 (2 * ((1 - x i) / (1 - δ)) - 1)

/-- One lazy step: raise `y` to `max y z`, then lower the excess `max y z - z` by a common fraction so that the total is `k`. -/
noncomputable def lazyStep (k : ℕ) (y z : Page → ℝ) : Page → ℝ :=
  fun i => z i + ((k - ∑ j, z j) / ∑ j, (max (y j) (z j) - z j)) * (max (y i) (z i) - z i)

/-- The lazy sequence: `y⁽⁰⁾ = z⁽⁰⁾`, `y⁽ᵛ⁺¹⁾ = lazyStep k y⁽ᵛ⁾ z⁽ᵛ⁺¹⁾`. -/
noncomputable def lazySeq (k : ℕ) : List (Page → ℝ) → List (Page → ℝ)
  | [] => []
  | z :: zs => z :: lazyFrom k z zs
where
  /-- The lazy caches after `y` for the targets `zs`. -/
  lazyFrom (k : ℕ) (y : Page → ℝ) : List (Page → ℝ) → List (Page → ℝ)
    | [] => []
    | z :: zs => lazyStep k y z :: lazyFrom k (lazyStep k y z) zs

/-! ## `lem:map` -/

variable {k : ℕ} {δ : ℝ}

/-- With `δ = 1/(2k+1)` and `k ≥ 1`: `0 < δ`, `1 - δ ≥ 2/3` and `k = (k + 1/2)(1 - δ)`. -/
lemma delta_facts (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) :
    0 < δ ∧ 2 / 3 ≤ 1 - δ ∧ (k : ℝ) = (k + 1 / 2) * (1 - δ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * k + 1 := by linarith
  subst hδ
  refine ⟨by positivity, ?_, ?_⟩
  · rw [le_sub_iff_add_le, div_add_div _ _ (by norm_num) hpos.ne', div_le_one (by positivity)]
    nlinarith
  · field_simp
    ring

/-- Unfolding `zmap`. -/
lemma zmap_apply (x : Page → ℝ) (i : Page) :
    zmap δ x i = max 0 (2 * ((1 - x i) / (1 - δ)) - 1) := rfl

theorem zmap_mem_fracCaches_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ}
    (hx : ∀ i, δ ≤ x i ∧ x i ≤ 1) (hmass : (Fintype.card Page : ℝ) - k ≤ ∑ i, x i) :
    (∀ i, 0 ≤ zmap δ x i ∧ zmap δ x i ≤ 1) ∧ ∑ i, zmap δ x i ≤ k := by
  obtain ⟨hδ0, hδ1, hkδ⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  set u : Page → ℝ := fun i => (1 - x i) / (1 - δ) with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => div_nonneg (by linarith [(hx i).2]) hc.le
  have hu1 : ∀ i, u i ≤ 1 := fun i => (div_le_one hc).2 (by linarith [(hx i).1])
  have hz : ∀ i, zmap δ x i = max 0 (2 * u i - 1) := fun i => rfl
  refine ⟨fun i => ⟨by rw [hz]; exact le_max_left _ _, by
    rw [hz]; exact max_le (by norm_num) (by linarith [hu1 i])⟩, ?_⟩
  -- `∑ u ≤ k + 1/2`
  have hsumu : ∑ i, u i ≤ k + 1 / 2 := by
    have : ∑ i, u i = (Fintype.card Page - ∑ i, x i) / (1 - δ) := by
      simp only [hu, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [this, div_le_iff₀ hc]
    linarith
  -- only the pages in `A = {i | uᵢ > 1/2}` contribute
  set A := Finset.univ.filter (fun i => 1 / 2 < u i) with hA
  have hsumA : ∑ i, zmap δ x i = ∑ i ∈ A, (2 * u i - 1) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz]
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  have h1 : ∑ i ∈ A, (2 * u i - 1) ≤ A.card := by
    rw [← mul_one (A.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => by linarith [hu1 i]
  have h2 : ∑ i ∈ A, (2 * u i - 1) ≤ 2 * (k + 1 / 2) - A.card := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ∑ i ∈ A, u i ≤ ∑ i, u i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hu0 i
    linarith
  rw [hsumA]
  rcases le_or_gt A.card k with h | h
  · exact h1.trans (by exact_mod_cast h)
  · have : (k : ℝ) + 1 ≤ A.card := by exact_mod_cast h
    linarith

theorem zmap_eq_one (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ} {i : Page}
    (hi : x i = δ) : zmap δ x i = 1 := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  rw [zmap_apply, hi, div_self (by linarith)]
  norm_num

/-- `1 - zᵢ ≤ 3 (xᵢ - δ)`: the probability that page `i` is not cached. -/
theorem one_sub_zmap_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) {x : Page → ℝ} {i : Page}
    (hi : δ ≤ x i) : 1 - zmap δ x i ≤ 3 * (x i - δ) := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  have : 1 - (2 * ((1 - x i) / (1 - δ)) - 1) ≤ 3 * (x i - δ) := by
    have e : 1 - (2 * ((1 - x i) / (1 - δ)) - 1) = 2 * (x i - δ) / (1 - δ) := by
      field_simp
      ring
    rw [e, div_le_iff₀ hc]
    nlinarith
  linarith [le_max_right 0 (2 * ((1 - x i) / (1 - δ)) - 1), zmap_apply (δ := δ) x i]

/-- `z` is nonincreasing and `3`-Lipschitz in each coordinate: `(z(x')ᵢ - z(x)ᵢ)⁺ ≤ 3 (xᵢ - x'ᵢ)⁺`. -/
theorem zmap_sub_le (hk : 0 < k) (hδ : δ = 1 / (2 * k + 1)) (x x' : Page → ℝ) (i : Page) :
    max 0 (zmap δ x' i - zmap δ x i) ≤ 3 * max 0 (x i - x' i) := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk hδ
  have hc : 0 < 1 - δ := by linarith
  set a := 2 * ((1 - x i) / (1 - δ)) - 1
  set a' := 2 * ((1 - x' i) / (1 - δ)) - 1
  have e : a' - a = 2 * (x i - x' i) / (1 - δ) := by
    simp only [a, a']
    field_simp
    ring
  have hle : max 0 a' - max 0 a ≤ max 0 (a' - a) := by
    simpa using max_sub_max_le_max 0 a' 0 a
  have hd : max 0 (a' - a) ≤ 3 * max 0 (x i - x' i) := by
    apply max_le (by positivity)
    rw [e, div_le_iff₀ hc]
    rcases le_total 0 (x i - x' i) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  exact max_le (by positivity) (hle.trans hd)

/-! ## The lazy sequence -/

/-- One lazy step keeps the invariant: for `y ∈ 𝒫` and `z ∈ [0,1]ⁿ` with `∑ z ≤ k`, `y' = lazyStep k y z` satisfies `z ≤ y' ≤ max y z` and `y' ∈ 𝒫`. -/
theorem lazyStep_spec {y z : Page → ℝ} (hy : y ∈ BBN.fracCaches k)
    (hz : (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k) :
    (∀ i, z i ≤ lazyStep k y z i ∧ lazyStep k y z i ≤ max (y i) (z i)) ∧
      lazyStep k y z ∈ BBN.fracCaches k := by
  obtain ⟨hy01, hysum⟩ := hy
  obtain ⟨hz01, hzsum⟩ := hz
  set S := ∑ j, (max (y j) (z j) - z j) with hS
  have hd : ∀ j, 0 ≤ max (y j) (z j) - z j := fun j => by linarith [le_max_right (y j) (z j)]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hd j
  have hDS : (k : ℝ) - ∑ j, z j ≤ S := by
    have : ∑ j, y j ≤ ∑ j, max (y j) (z j) := Finset.sum_le_sum fun j _ => le_max_left _ _
    rw [hS, Finset.sum_sub_distrib]
    linarith
  set θ := ((k : ℝ) - ∑ j, z j) / S with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hS0
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ hDS hS0
  have hy' : ∀ i, lazyStep k y z i = z i + θ * (max (y i) (z i) - z i) := fun i => rfl
  have hbd : ∀ i, z i ≤ lazyStep k y z i ∧ lazyStep k y z i ≤ max (y i) (z i) := fun i => by
    rw [hy']
    constructor
    · nlinarith [hd i]
    · nlinarith [hd i]
  refine ⟨hbd, fun i => ⟨(hz01 i).1.trans (hbd i).1,
    (hbd i).2.trans (max_le (hy01 i).2 (hz01 i).2)⟩, ?_⟩
  simp only [hy', Finset.sum_add_distrib, ← Finset.mul_sum]
  rcases hS0.lt_or_eq with h | h
  · rw [hθ, div_mul_cancel₀ _ h.ne']
    ring
  · rw [← hS, ← h, mul_zero, add_zero]
    linarith

/-- The lazy sequence as a scan: `lazySeq k (z :: zs) = scanl (lazyStep k) z zs`. -/
theorem lazySeq_cons (z : Page → ℝ) (zs : List (Page → ℝ)) :
    lazySeq k (z :: zs) = List.scanl (lazyStep k) z zs := by
  suffices h : ∀ (y : Page → ℝ) (zs : List (Page → ℝ)),
      y :: lazySeq.lazyFrom k y zs = List.scanl (lazyStep k) y zs from h z zs
  intro y zs
  induction zs generalizing y with
  | nil => simp [lazySeq.lazyFrom]
  | cons z zs ih => simp [lazySeq.lazyFrom, ih, List.scanl_cons]

theorem length_lazySeq (zs : List (Page → ℝ)) : (lazySeq k zs).length = zs.length := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq_cons]

/-- The lazy sequence is computed online. -/
theorem lazySeq_take (zs : List (Page → ℝ)) (m : ℕ) :
    (lazySeq k zs).take m = lazySeq k (zs.take m) := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs =>
    cases m with
    | zero => simp [lazySeq]
    | succ m => simp [lazySeq_cons, List.take_scanl]

theorem head?_lazySeq (zs : List (Page → ℝ)) : (lazySeq k zs).head? = zs.head? := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq]

/-- The recursion of the lazy sequence by index (with default `0` out of range). -/
theorem getD_lazySeq_succ {zs : List (Page → ℝ)} {ν : ℕ} (hν : ν + 1 < zs.length) :
    (lazySeq k zs).getD (ν + 1) 0 = lazyStep k ((lazySeq k zs).getD ν 0) (zs.getD (ν + 1) 0) := by
  cases zs with
  | nil => simp at hν
  | cons z zs =>
    simp only [List.length_cons] at hν
    rw [lazySeq_cons, List.getD_eq_getElem _ _ (by simpa using hν),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_succ_scanl]
    have : ν < zs.length := by omega
    simp [this]

theorem getD_lazySeq_zero (zs : List (Page → ℝ)) : (lazySeq k zs).getD 0 0 = zs.getD 0 0 := by
  cases zs with
  | nil => simp [lazySeq]
  | cons z zs => simp [lazySeq]

/-- The invariant of the lazy sequence, by index: `y⁽ᵛ⁾ ∈ 𝒫` and `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾`. -/
theorem getD_lazySeq_spec {zs : List (Page → ℝ)}
    (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) (ν : ℕ) (hν : ν < zs.length) :
    (lazySeq k zs).getD ν 0 ∈ BBN.fracCaches k ∧
      ∀ i, zs.getD ν 0 i ≤ (lazySeq k zs).getD ν 0 i := by
  have hzν : ∀ ν (hν : ν < zs.length), (∀ i, 0 ≤ zs.getD ν 0 i ∧ zs.getD ν 0 i ≤ 1) ∧
      ∑ i, zs.getD ν 0 i ≤ k := fun ν hν => by
    rw [List.getD_eq_getElem _ _ hν]; exact hz _ (List.getElem_mem hν)
  induction ν with
  | zero =>
    rw [getD_lazySeq_zero]
    refine ⟨⟨(hzν 0 hν).1, ?_⟩, fun i => le_rfl⟩
    cases zs with
    | nil => simp at hν
    | cons z zs => simpa using h0 z (by simp)
  | succ ν ih =>
    rw [getD_lazySeq_succ hν]
    obtain ⟨h1, h2⟩ := lazyStep_spec (ih (by omega)).1 (hzν _ hν)
    exact ⟨h2, fun i => (h1 i).1⟩

/-- The lazy caches dominate the targets: `y⁽ᵛ⁾ ≥ z⁽ᵛ⁾`. -/
theorem le_lazySeq {zs : List (Page → ℝ)} (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) (ν : ℕ) (hν : ν < (lazySeq k zs).length) (i : Page) :
    (zs[ν]'(by simpa [length_lazySeq] using hν)) i ≤ (lazySeq k zs)[ν] i := by
  have hν' : ν < zs.length := by simpa [length_lazySeq] using hν
  have := (getD_lazySeq_spec hz h0 ν hν').2 i
  rwa [List.getD_eq_getElem _ _ hν, List.getD_eq_getElem _ _ hν'] at this

theorem lazySeq_mem {zs : List (Page → ℝ)} (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) : ∀ y ∈ lazySeq k zs, y ∈ BBN.fracCaches k := by
  intro y hy
  obtain ⟨ν, hν, rfl⟩ := List.getElem_of_mem hy
  have hν' : ν < zs.length := by simpa [length_lazySeq] using hν
  have := (getD_lazySeq_spec hz h0 ν hν').1
  rwa [List.getD_eq_getElem _ _ hν] at this

/-- `|a| = 2 a⁺ - a`. -/
lemma abs_eq_two_mul_max_sub (a : ℝ) : |a| = 2 * max 0 a - a := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_right h]; ring
  · rw [abs_of_nonpos h, max_eq_left h]; ring

/-- Per page: the total movement of a sequence `a` in `[0,1]` whose increments are bounded by the positive increments of `b` is at most `2 ∑ (Δb)⁺ + 1`. -/
lemma sum_abs_sub_le (a b : ℕ → ℝ) (N : ℕ) (ha : ∀ ν, 0 ≤ a ν ∧ a ν ≤ 1)
    (hab : ∀ ν < N, a (ν + 1) - a ν ≤ max 0 (b (ν + 1) - b ν)) :
    ∑ ν ∈ Finset.range N, |a (ν + 1) - a ν| ≤
      2 * ∑ ν ∈ Finset.range N, max 0 (b (ν + 1) - b ν) + 1 := by
  simp only [abs_eq_two_mul_max_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (f := a)]
  have : ∑ ν ∈ Finset.range N, max 0 (a (ν + 1) - a ν) ≤
      ∑ ν ∈ Finset.range N, max 0 (b (ν + 1) - b ν) :=
    Finset.sum_le_sum fun ν hν =>
      max_le (le_max_left _ _) (hab ν (Finset.mem_range.1 hν))
  linarith [(ha N).1, (ha 0).2]

/-- The movement cost of the lazy caches: `∑ᵥ ∑ᵢ wᵢ |y⁽ᵛ⁺¹⁾ᵢ - y⁽ᵛ⁾ᵢ| ≤ 2 ∑ᵥ ∑ᵢ wᵢ (z⁽ᵛ⁺¹⁾ᵢ - z⁽ᵛ⁾ᵢ)⁺ + ∑ᵢ wᵢ`. -/
theorem sum_movement_lazySeq_le (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) {zs : List (Page → ℝ)}
    (hz : ∀ z ∈ zs, (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ k)
    (h0 : ∀ z ∈ zs.head?, ∑ i, z i = k) :
    ∑ ν ∈ Finset.range (zs.length - 1),
        ∑ i, w i * |(lazySeq k zs).getD (ν + 1) 0 i - (lazySeq k zs).getD ν 0 i| ≤
      2 * ∑ ν ∈ Finset.range (zs.length - 1),
          ∑ i, w i * max 0 (zs.getD (ν + 1) 0 i - zs.getD ν 0 i) + ∑ i, w i := by
  set Y := fun ν => (lazySeq k zs).getD ν 0 with hY
  set Z := fun ν => zs.getD ν 0 with hZ
  -- every `y⁽ᵛ⁾` lies in `[0,1]ⁿ` (the default `0` too)
  have hY01 : ∀ ν i, 0 ≤ Y ν i ∧ Y ν i ≤ 1 := fun ν i => by
    rcases lt_or_ge ν zs.length with h | h
    · exact (getD_lazySeq_spec hz h0 ν h).1.1 i
    · have h' : (lazySeq k zs).length ≤ ν := by rwa [length_lazySeq]
      simp only [hY]
      rw [List.getD_eq_default _ _ h']
      simp
  -- `y⁽ᵛ⁺¹⁾ᵢ - y⁽ᵛ⁾ᵢ ≤ (z⁽ᵛ⁺¹⁾ᵢ - z⁽ᵛ⁾ᵢ)⁺`
  have hstep : ∀ i, ∀ ν < zs.length - 1,
      Y (ν + 1) i - Y ν i ≤ max 0 (Z (ν + 1) i - Z ν i) := fun i ν hν => by
    have hν1 : ν + 1 < zs.length := by omega
    obtain ⟨hYν, hZY⟩ := getD_lazySeq_spec hz h0 ν (by omega)
    have hZ1 : (∀ i, 0 ≤ Z (ν + 1) i ∧ Z (ν + 1) i ≤ 1) ∧ ∑ i, Z (ν + 1) i ≤ k := by
      simp only [hZ, List.getD_eq_getElem _ _ hν1]; exact hz _ (List.getElem_mem hν1)
    have h := ((lazyStep_spec hYν hZ1).1 i).2
    simp only [hY] at h ⊢
    rw [getD_lazySeq_succ hν1]
    have := hZY i
    simp only [hZ] at hZ1 ⊢
    rcases le_total (Y ν i) (Z (ν + 1) i) with h' | h'
    · simp only [hY, hZ] at h'
      rw [max_eq_right h'] at h
      exact le_max_of_le_right (by linarith)
    · simp only [hY, hZ] at h'
      rw [max_eq_left h'] at h
      exact le_max_of_le_left (by linarith)
  calc ∑ ν ∈ Finset.range (zs.length - 1), ∑ i, w i * |Y (ν + 1) i - Y ν i|
      = ∑ i, w i * ∑ ν ∈ Finset.range (zs.length - 1), |Y (ν + 1) i - Y ν i| := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ i, w i * (2 * ∑ ν ∈ Finset.range (zs.length - 1), max 0 (Z (ν + 1) i - Z ν i) + 1) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (sum_abs_sub_le (fun ν => Y ν i) (fun ν => Z ν i) _ (hY01 · i) (hstep i)) (hw i)
    _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i _ => by ring

end Rounding

end PagingWithDelay
