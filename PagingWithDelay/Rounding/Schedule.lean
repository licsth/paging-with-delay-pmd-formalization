import PagingWithDelay.Opt
import PagingWithDelay.Rounding.Chain
import PagingWithDelay.Rounding.Map

/-!
# `prop:rounding`: from a fractional schedule to a random integral schedule

A feasible fractional schedule `X` with states `x⁽⁰⁾, …, x⁽ᴺ⁾` at times `t⁽⁰⁾ ≤ … ≤ t⁽ᴺ⁾` is rounded as in Appendix A: the states are mapped to cached masses `z⁽ᵛ⁾ = zmap δ x⁽ᵛ⁾` (`lem:map`), made lazy (`y⁽ᵛ⁾ = lazySeq k z`), and rounded online by `cor:rounding` to random caches `C⁽ᵛ⁾`, to which the integral schedule moves at time `t⁽ᵛ⁾`. For power-of-two weights, if the first state maps to the indicator vector of the initial cache, the schedule is feasible with probability `1` and has expected cost at most `30 C_fetch + 3 C_delay + 5 ∑ wᵢ`. The rounding is online: the steps up to time `t` depend only on the waypoints up to time `t`.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

namespace Rounding

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- The indicator vector of a set of pages. -/
def indicator (C : Finset Page) : Page → ℝ := fun i => if i ∈ C then 1 else 0

open scoped InstanceNotation in
/-- Power-of-two weights differ by a factor of at least `2` if they differ. -/
theorem two_mul_le_of_powerOfTwo {input : Instance Page} (h2 : input.PowerOfTwoWeights)
    (i j : Page) (h : w i < w j) : 2 * w i ≤ w j := by
  obtain ⟨a, ha⟩ := h2 i
  obtain ⟨b, hb⟩ := h2 j
  rw [ha, hb] at h ⊢
  have hab : a < b := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h
  calc 2 * (2 : ℝ) ^ a = 2 ^ (a + 1) := by rw [zpow_add_one₀ two_ne_zero, mul_comm]
    _ ≤ 2 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)

open Classical in
open scoped InstanceNotation in
/-- The rounding of `cor:rounding` for the weights, cache size and initial cache of `input` (a trivial function unless the weights are powers of two). -/
noncomputable def roundFor (input : Instance Page) :
    List (Page → ℝ) → PMF (List (Finset Page)) :=
  if h2 : input.PowerOfTwoWeights then
    Classical.choose (onlineRounding w input.weight_pos
      (two_mul_le_of_powerOfTwo h2) k input.initialCache input.initialCache_card)
  else fun _ => PMF.pure []

/-- The lazy fractional caches `y⁽ᵛ⁾` of the states of `X`. -/
noncomputable def lazyCaches (input : Instance Page) (X : FracSchedule Page) :
    List (Page → ℝ) :=
  lazySeq input.cacheSize (X.map fun w => zmap input.delta w.state)

/-- The integral schedule that moves to the cache `C⁽ᵛ⁾` at the time of the `ν`-th waypoint. -/
def toSchedule (X : FracSchedule Page) (Cs : List (Finset Page)) : Schedule Page :=
  List.zipWith (fun w C => ⟨w.time, C⟩) X Cs

/-- The random integral schedule rounded from `X`. -/
noncomputable def randomSchedule (input : Instance Page) (X : FracSchedule Page) :
    PMF (Schedule Page) :=
  (roundFor input (lazyCaches input X)).map (toSchedule X)

/-! ### Chronological lists -/

section Lists

variable {α : Type*} {R : α → α → Prop} {P : α → Bool}

/-- In a list ordered by `R`, filtering by a predicate inherited by earlier elements keeps a prefix. -/
theorem filter_eq_take (hP : ∀ x y, R x y → P y → P x) {l : List α} (hl : l.Pairwise R) :
    l.filter P = l.take (l.filter P).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : P x
    · rw [List.filter_cons_of_pos hx, List.length_cons, List.take_succ_cons, ← ih hl.2]
    · have : l.filter P = [] :=
        List.filter_eq_nil_iff.2 fun y hy hPy => hx (hP x y (hl.1 y hy) hPy)
      rw [List.filter_cons_of_neg hx, this]
      rfl

/-- The same by index: the predicate holds exactly at the indices below the length of the filtered list. -/
theorem getElem_iff_lt_length_filter (hP : ∀ x y, R x y → P y → P x) {l : List α}
    (hl : l.Pairwise R) (j : ℕ) (hj : j < l.length) : P l[j] ↔ j < (l.filter P).length := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hx : P x
    · rw [List.filter_cons_of_pos hx, List.length_cons]
      cases j with
      | zero => simp [hx]
      | succ j => simpa using ih hl.2 j (by simpa using hj)
    · have : l.filter P = [] :=
        List.filter_eq_nil_iff.2 fun y hy hPy => hx (hP x y (hl.1 y hy) hPy)
      rw [List.filter_cons_of_neg hx, this]
      cases j with
      | zero => simpa using hx
      | succ j =>
        simp only [List.getElem_cons_succ, List.length_nil, Nat.not_lt_zero, iff_false]
        exact List.filter_eq_nil_iff.1 this _ (List.getElem_mem _)

end Lists

/-! ### The integral schedule of a sequence of caches -/

theorem toSchedule_cons (w : Waypoint Page) (X : FracSchedule Page) (C : Finset Page)
    (Cs : List (Finset Page)) : toSchedule (w :: X) (C :: Cs) = ⟨w.time, C⟩ :: toSchedule X Cs :=
  rfl

theorem length_toSchedule (X : FracSchedule Page) (Cs : List (Finset Page)) :
    (toSchedule X Cs).length = min X.length Cs.length := by
  simp [toSchedule]

theorem getElem_toSchedule {X : FracSchedule Page} {Cs : List (Finset Page)} {j : ℕ}
    (hj : j < (toSchedule X Cs).length) :
    (toSchedule X Cs)[j] = ⟨(X[j]'(by rw [length_toSchedule] at hj; omega)).time,
      Cs[j]'(by rw [length_toSchedule] at hj; omega)⟩ := by
  simp [toSchedule]

/-- The steps of `toSchedule X Cs` are chronological if the waypoints are. -/
theorem toSchedule_chronological {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (Cs : List (Finset Page)) :
    (toSchedule X Cs).Pairwise fun earlier later => earlier.time ≤ later.time := by
  rw [List.pairwise_iff_getElem] at hX ⊢
  intro i j hi hj hij
  rw [getElem_toSchedule, getElem_toSchedule]
  exact hX i j _ _ hij

/-- The steps up to time `t` are those of the waypoints up to time `t`. -/
theorem toSchedule_upTo {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (Cs : List (Finset Page))
    (t : ℝ) :
    Schedule.upTo (toSchedule X Cs) t = toSchedule (X.upTo t) (Cs.take (X.upTo t).length) := by
  induction X generalizing Cs with
  | nil => simp [toSchedule, Schedule.upTo, FracSchedule.upTo]
  | cons w X ih =>
    rw [List.pairwise_cons] at hX
    cases Cs with
    | nil => simp [toSchedule, Schedule.upTo]
    | cons C Cs =>
      have ih' := ih hX.2 Cs
      simp only [Schedule.upTo, FracSchedule.upTo] at ih' ⊢
      rw [toSchedule_cons]
      by_cases hw : w.time ≤ t
      · rw [List.filter_cons_of_pos (by simpa using hw), List.filter_cons_of_pos (by simpa using hw),
          List.length_cons, List.take_succ_cons, toSchedule_cons, ih']
      · have h1 : X.filter (fun w => decide (w.time ≤ t)) = [] :=
          List.filter_eq_nil_iff.2 fun v hv h => hw ((hX.1 v hv).trans (by simpa using h))
        rw [List.filter_cons_of_neg (by simpa using hw), List.filter_cons_of_neg (by simpa using hw),
          ih', h1]
        rfl

/-- The fetch cost of `toSchedule X Cs` starting from `C`. -/
theorem costFrom_toSchedule (w : Page → ℝ) : ∀ (X : FracSchedule Page) (Cs : List (Finset Page))
    (C : Finset Page), Cs.length ≤ X.length →
    Schedule.costFrom w C (toSchedule X Cs) = ∑ i ∈ Cs.getD 0 ∅ \ C, w i +
      ∑ ν ∈ Finset.range (Cs.length - 1), ∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, w i
  | _, [], C, _ => by simp [toSchedule, Schedule.costFrom]
  | [], _ :: _, _, h => by simp at h
  | x :: X, C' :: Cs, C, h => by
      rw [toSchedule_cons, Schedule.costFrom,
        costFrom_toSchedule w X Cs C' (by simpa using h)]
      rcases Cs with _ | ⟨C'', Cs⟩
      · simp
      · simp only [List.length_cons, Nat.add_sub_cancel, Finset.sum_range_succ' _ (Cs.length)]
        simp
        ring

/-- The cache of step `ν` is present at every time `s` from the time of waypoint `ν` to the time of the next waypoint. -/
theorem cachedAt_toSchedule {input : Instance Page} {X : FracSchedule Page}
    {Cs : List (Finset Page)} (hlen : Cs.length = X.length) {ν : ℕ} (hν : ν < X.length) {s : ℝ}
    (h1 : X[ν].time ≤ s) (h2 : ∀ h : ν + 1 < X.length, s ≤ X[ν + 1].time) {p : Page}
    (hp : p ∈ Cs[ν]'(hlen ▸ hν)) : Schedule.CachedAt input (toSchedule X Cs) p s := by
  have hS : ν < (toSchedule X Cs).length := by rw [length_toSchedule]; omega
  refine Or.inr ⟨ν, hS, ?_, ?_, ?_⟩
  · rw [getElem_toSchedule]; exact h1
  · intro step hstep
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hstep
    rw [getElem_toSchedule]
    exact h2 (by rw [length_toSchedule] at h; omega)
  · rw [getElem_toSchedule]; exact hp

/-- The initial cache is present until the time of the first waypoint. -/
theorem cachedAt_toSchedule_initial {input : Instance Page} {X : FracSchedule Page}
    {Cs : List (Finset Page)} (hlen : Cs.length = X.length)
    (h0 : ∀ C ∈ Cs.head?, C = input.initialCache) (hpos : 0 < X.length) {s : ℝ}
    (hs : s ≤ X[0].time) {p : Page} (hp : p ∈ Cs[0]'(hlen ▸ hpos)) :
    Schedule.CachedAt input (toSchedule X Cs) p s := by
  obtain ⟨w, X', rfl⟩ := List.exists_cons_of_length_pos hpos
  obtain ⟨C, Cs', rfl⟩ := List.exists_cons_of_length_pos (hlen ▸ hpos)
  refine Or.inl ⟨?_, ?_⟩
  · rw [← h0 C rfl]; simpa using hp
  · intro step hstep
    simp only [toSchedule_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hstep
    subst hstep
    simpa using hs

/-! ### The state right before a time -/

/-- The index of the waypoint giving the state right before time `t`: the last waypoint with time `< t`, or the first one if there is none. -/
noncomputable def beforeIdx (X : FracSchedule Page) (t : ℝ) : ℕ :=
  (X.filter fun w => decide (w.time < t)).length - 1

theorem beforeIdx_lt {X : FracSchedule Page} (hpos : 0 < X.length) (t : ℝ) :
    beforeIdx X t < X.length := by
  have := List.length_filter_le (fun w : Waypoint Page => decide (w.time < t)) X
  unfold beforeIdx
  omega

/-- Waypoints with time `< t` come first. -/
theorem lt_iff_lt_length_filter {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (t : ℝ) (j : ℕ)
    (hj : j < X.length) : X[j].time < t ↔ j < (X.filter fun w => decide (w.time < t)).length := by
  rw [← getElem_iff_lt_length_filter (P := fun w : Waypoint Page => decide (w.time < t))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hX j hj]
  simp

theorem stateBefore_eq {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (hpos : 0 < X.length)
    (t : ℝ) : X.stateBefore t = (X[beforeIdx X t]'(beforeIdx_lt hpos t)).state := by
  have hfilt := filter_eq_take (P := fun w : Waypoint Page => decide (w.time < t))
    (fun x y (hxy : x.time ≤ y.time) h => by simp only [decide_eq_true_eq] at h ⊢; linarith) hX
  have hn := List.length_filter_le (fun w : Waypoint Page => decide (w.time < t)) X
  have hb : beforeIdx X t = (X.filter fun w => decide (w.time < t)).length - 1 := rfl
  unfold FracSchedule.stateBefore
  conv_lhs => rw [hfilt, List.getLast?_take]
  split_ifs with h0
  · obtain ⟨w, X', rfl⟩ := List.exists_cons_of_length_pos hpos
    simp only [hb, h0]
    simp
  · rw [List.getElem?_eq_getElem (by omega : _ - 1 < X.length)]
    simp only [hb, Option.some_or]

/-- If the page of `ρ` is in the cache right before its arrival, it is cached at its arrival. -/
theorem cachedAt_arrival {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) {Cs : List (Finset Page)}
    (hlen : Cs.length = X.length) (h0 : ∀ C ∈ Cs.head?, C = input.initialCache)
    (hpos : 0 < X.length) {p : Page} {t : ℝ} (hp : p ∈ Cs.getD (beforeIdx X t) ∅) :
    Schedule.CachedAt input (toSchedule X Cs) p t := by
  have hiff := lt_iff_lt_length_filter hX t
  have hb := beforeIdx_lt hpos t
  rw [List.getD_eq_getElem _ _ (by omega)] at hp
  obtain hn | hn := Nat.eq_zero_or_pos (List.length (X.filter fun w : Waypoint Page => decide (w.time < t)))
  · have hb0 : beforeIdx X t = 0 := by simp only [beforeIdx, hn]
    simp only [hb0] at hp
    exact cachedAt_toSchedule_initial hlen h0 hpos (not_lt.1 fun h => by
      have := (hiff 0 hpos).1 h; omega) hp
  · refine cachedAt_toSchedule hlen hb ((hiff _ hb).2 (by unfold beforeIdx; omega)).le
      (fun h => not_lt.1 fun h' => ?_) hp
    have := (hiff _ h).1 h'
    unfold beforeIdx at this
    omega

/-! ### Laws of finite random caches -/

omit [DecidableEq Page] in
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (Q : PMF α) : ∑ a, (Q a).toReal = 1 := by
  have h := PMF.tsum_coe Q
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top Q a), h, ENNReal.toReal_one]

/-- The probability that page `i` is not cached. -/
theorem sum_not_mem_eq (Q : PMF (Finset Page)) (i : Page) :
    ∑ C : Finset Page, (if i ∈ C then 0 else (Q C).toReal) = 1 - BBN.marginal Q i := by
  rw [BBN.marginal, ← sum_toReal_eq_one Q, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs <;> ring

/-- A page with marginal `1` is in every cache of the support. -/
theorem mem_of_marginal_eq_one {Q : PMF (Finset Page)} {i : Page} (h : BBN.marginal Q i = 1)
    {C : Finset Page} (hC : C ∈ Q.support) : i ∈ C := by
  by_contra hi
  have hs := sum_not_mem_eq Q i
  rw [h, sub_self] at hs
  have hle : (if i ∈ C then 0 else (Q C).toReal) ≤
      ∑ C' : Finset Page, (if i ∈ C' then 0 else (Q C').toReal) :=
    Finset.single_le_sum (f := fun C' => if i ∈ C' then 0 else (Q C').toReal)
      (fun C' _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ C)
  rw [hs, if_neg hi] at hle
  have h0 : (Q C).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h0 | htop
  · exact (PMF.mem_support_iff _ _).1 hC h0
  · exact PMF.apply_ne_top _ _ htop

omit [Fintype Page] [DecidableEq Page] in
/-- Expectation under an image distribution. -/
theorem tsum_map_mul {α β : Type*} (μ : PMF α) (f : α → β) (g : β → ENNReal) :
    ∑' b, μ.map f b * g b = ∑' a, μ a * g (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  simp_rw [ite_mul, zero_mul]
  simp

omit [Fintype Page] [DecidableEq Page] in
/-- The expectation of a nonnegative function of a finite random variable `f`, as a real sum over the law of `f`. -/
theorem tsum_mul_ofReal_eq {α β : Type*} [Fintype β] (μ : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∑' a, μ a * ENNReal.ofReal (g (f a)) = ENNReal.ofReal (∑ b, (μ.map f b).toReal * g b) := by
  rw [← tsum_map_mul μ f (fun b => ENNReal.ofReal (g b)), tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg ENNReal.toReal_nonneg (hg b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

omit [Fintype Page] [DecidableEq Page] in
/-- Linearity of expectation for a list sum. -/
theorem tsum_mul_list_sum {α ι : Type*} (μ : α → ENNReal) (l : List ι) (g : ι → α → ENNReal) :
    ∑' a, μ a * (l.map fun i => g i a).sum = (l.map fun i => ∑' a, μ a * g i a).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

omit [Fintype Page] [DecidableEq Page] in
theorem ofReal_list_sum {ι : Type*} (l : List ι) (f : ι → ℝ) (hf : ∀ i ∈ l, 0 ≤ f i) :
    ENNReal.ofReal (l.map f).sum = (l.map fun i => ENNReal.ofReal (f i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hf a List.mem_cons_self) (List.sum_nonneg fun x hx => ?_),
      ih fun i hi => hf i (List.mem_cons_of_mem _ hi)]
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact hf j (List.mem_cons_of_mem _ hj)

/-! ### The rounding -/

open scoped InstanceNotation in
theorem roundFor_eq {input : Instance Page} (h2 : input.PowerOfTwoWeights) :
    roundFor input = Classical.choose (onlineRounding w input.weight_pos
      (two_mul_le_of_powerOfTwo h2) k input.initialCache input.initialCache_card) := by
  rw [roundFor, dif_pos h2]

open scoped InstanceNotation in
/-- The rounding is online (for all weights). -/
theorem roundFor_take (input : Instance Page) (ys : List (Page → ℝ)) (m : ℕ) :
    (roundFor input ys).map (List.take m) = roundFor input (ys.take m) := by
  by_cases h2 : input.PowerOfTwoWeights
  · rw [roundFor_eq h2]
    exact (Classical.choose_spec (onlineRounding w input.weight_pos
      (two_mul_le_of_powerOfTwo h2) k input.initialCache
      input.initialCache_card)).1 ys m
  · simp [roundFor, dif_neg h2, PMF.pure_map]

theorem lazyCaches_take (input : Instance Page) (X : FracSchedule Page) (m : ℕ) :
    lazyCaches input (X.take m) = (lazyCaches input X).take m := by
  rw [lazyCaches, lazyCaches, lazySeq_take, List.map_take]

theorem sum_indicator (C : Finset Page) : ∑ i, indicator C i = C.card := by
  simp [indicator]

/-- The cached masses `z⁽ᵛ⁾ = zmap δ x⁽ᵛ⁾` of the states of `X`. -/
theorem zs_spec {input : Instance Page} {X : FracSchedule Page} (hX : X.Feasible input) :
    ∀ z ∈ X.map (fun w => zmap input.delta w.state),
      (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ input.cacheSize := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
  exact zmap_mem_fracCaches_le input.cacheSize_pos rfl (hX.bounds w hw) (hX.mass w hw)

theorem zs_head {input : Instance Page} {X : FracSchedule Page}
    (h0 : ∀ w ∈ X.head?, zmap input.delta w.state = indicator input.initialCache) :
    ∀ z ∈ (X.map fun w => zmap input.delta w.state).head?, ∑ i, z i = input.cacheSize := by
  intro z hz
  simp only [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [h0 w hw, sum_indicator, input.initialCache_card]

/-- The properties of the cache sequences in the support of the rounding used by the analysis. -/
structure Rounded (input : Instance Page) (X : FracSchedule Page) (Cs : List (Finset Page)) :
    Prop where
  length_eq : Cs.length = X.length
  card_eq : ∀ C ∈ Cs, C.card = input.cacheSize
  head_eq : ∀ C ∈ Cs.head?, C = input.initialCache
  mem : ∀ ν (hν : ν < X.length) (hν' : ν < Cs.length) (p : Page),
    X[ν].state p = input.delta → p ∈ Cs[ν]

/-- The specification of the rounding of the lazy caches of a feasible `X`. -/
theorem roundFor_spec {input : Instance Page} (h2 : input.PowerOfTwoWeights)
    {X : FracSchedule Page} (hX : X.Feasible input)
    (h0 : ∀ w ∈ X.head?, zmap input.delta w.state = indicator input.initialCache) :
    (lazyCaches input X).length = X.length ∧
    (∀ Cs ∈ (roundFor input (lazyCaches input X)).support, Rounded input X Cs) ∧
    (∀ ν (hν : ν < (lazyCaches input X).length),
      BBN.marginal (cacheLaw (roundFor input (lazyCaches input X)) ν) = (lazyCaches input X)[ν]) ∧
    (∀ ν (hν : ν + 1 < (lazyCaches input X).length),
      ∑ CC : Finset Page × Finset Page,
          (stepLaw (roundFor input (lazyCaches input X)) ν CC).toReal *
            ∑ i ∈ CC.2 \ CC.1, input.weight i ≤
        5 * ∑ i, input.weight i *
          |(lazyCaches input X)[ν + 1] i - (lazyCaches input X)[ν] i|) := by
  have hz := zs_spec hX
  have hz0 := zs_head h0
  have hys : ∀ y ∈ lazyCaches input X, y ∈ BBN.fracCaches input.cacheSize := lazySeq_mem hz hz0
  have hhead : ∀ y ∈ (lazyCaches input X).head?,
      y = fun i => if i ∈ input.initialCache then 1 else 0 := by
    intro y hy
    simp only [lazyCaches, head?_lazySeq, List.head?_map, Option.mem_def,
      Option.map_eq_some_iff] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact h0 w hw
  have hlenX : (lazyCaches input X).length = X.length := by simp [lazyCaches, length_lazySeq]
  have hspec := Classical.choose_spec (onlineRounding input.weight input.weight_pos
    (two_mul_le_of_powerOfTwo h2) input.cacheSize input.initialCache input.initialCache_card)
  rw [← roundFor_eq h2] at hspec
  obtain ⟨hsupp, hmarg, hstep⟩ := hspec.2 _ hys hhead
  refine ⟨hlenX, fun Cs hCs => ?_, hmarg, hstep⟩
  obtain ⟨hlen, hcard, hC0⟩ := hsupp Cs hCs
  refine ⟨hlen.trans hlenX, hcard, hC0, fun ν hν hν' p hp => ?_⟩
  have hyν : ν < (lazyCaches input X).length := hlenX ▸ hν
  -- the cached mass of `p` in `y⁽ᵛ⁾` is `1`
  have h1 : (lazyCaches input X)[ν] p = 1 := by
    have hle := le_lazySeq hz hz0 ν hyν p
    have hz1 : zmap input.delta X[ν].state p = 1 := zmap_eq_one input.cacheSize_pos rfl hp
    have hy1 := ((hys _ (List.getElem_mem hyν)).1 p).2
    simp only [List.getElem_map] at hle
    rw [hz1] at hle
    exact le_antisymm hy1 hle
  have hm : BBN.marginal (cacheLaw (roundFor input (lazyCaches input X)) ν) p = 1 := by
    rw [hmarg ν hyν, h1]
  have hmem := mem_of_marginal_eq_one hm
    ((PMF.mem_support_map_iff _ _ _).2 ⟨Cs, hCs, rfl⟩)
  rwa [List.getD_eq_getElem _ _ hν'] at hmem

/-! ### Fetch costs -/

open scoped InstanceNotation in
/-- The fetch cost of the rounded schedule. -/
theorem fetchCost_toSchedule {input : Instance Page} {X : FracSchedule Page}
    {Cs : List (Finset Page)} (hR : Rounded input X Cs) :
    Schedule.fetchCost input (toSchedule X Cs) =
      ∑ ν ∈ Finset.range (X.length - 1),
        ∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, w i := by
  rw [Schedule.fetchCost, costFrom_toSchedule _ _ _ _ hR.length_eq.le, hR.length_eq]
  have : Cs.getD 0 ∅ \ input.initialCache = ∅ := by
    rcases Cs with _ | ⟨C, Cs⟩
    · simp
    · simp [hR.head_eq C rfl]
  rw [this, Finset.sum_empty, zero_add]

omit [DecidableEq Page] in
open scoped InstanceNotation in
/-- The fractional fetch cost by index. -/
theorem fracFetchCost_eq (input : Instance Page) (X : FracSchedule Page) :
    X.fetchCost input = ∑ ν ∈ Finset.range (X.length - 1), ∑ i, w i *
      max 0 ((X.map Waypoint.state).getD ν 0 i - (X.map Waypoint.state).getD (ν + 1) 0 i) := by
  induction X with
  | nil => simp [FracSchedule.fetchCost]
  | cons a X ih =>
    cases X with
    | nil => simp [FracSchedule.fetchCost]
    | cons b rest =>
      rw [FracSchedule.fetchCost, ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ' _ (rest.length)]
      simp
      ring

/-! ### Delay costs -/

/-- The fractional service time is attained at a waypoint. -/
theorem exists_fracServiceTime {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Feasible input) {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ∃ ν, ∃ hν : ν < X.length, ρ.arrival ≤ X[ν].time ∧ X[ν].state ρ.page = input.delta ∧
      X[ν].time = X.serviceTime input ρ := by
  have hne : {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧
      w.time = s}.Nonempty := by
    obtain ⟨w, hw, h1, h2⟩ := hX.serves ρ hρ
    exact ⟨w.time, w, hw, h1, h2, rfl⟩
  have hfin : {s | ∃ w ∈ X, ρ.arrival ≤ w.time ∧ w.state ρ.page = input.delta ∧
      w.time = s}.Finite :=
    (X.map Waypoint.time).finite_toSet.subset fun s ⟨w, hw, _, _, hs⟩ =>
      List.mem_map.2 ⟨w, hw, hs⟩
  obtain ⟨w, hw, h1, h2, h3⟩ := hne.csInf_mem hfin
  obtain ⟨ν, hν, rfl⟩ := List.getElem_of_mem hw
  exact ⟨ν, hν, h1, h2, h3⟩

/-- The bound `d_ρ(τ_ρ - a_ρ) · 1[p_ρ ∉ C]` on the delay cost of `ρ` in the rounded schedule, given the cache `C` right before its arrival. -/
noncomputable def delayBound (input : Instance Page) (X : FracSchedule Page) (ρ : Request Page)
    (C : Finset Page) : ℝ :=
  ρ.delay (X.serviceTime input ρ - ρ.arrival) * if ρ.page ∈ C then 0 else 1

theorem delayBound_nonneg {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Feasible input) {ρ : Request Page} (hρ : ρ ∈ input.requests) (C : Finset Page) :
    0 ≤ delayBound input X ρ C := by
  obtain ⟨ν, hν, h1, -, h3⟩ := exists_fracServiceTime hX hρ
  have : 0 ≤ ρ.delay (X.serviceTime input ρ - ρ.arrival) := by
    rw [← ρ.delay_zero]; exact ρ.delay_mono (by linarith)
  unfold delayBound
  split_ifs <;> simp [this]

/-- The delay cost of `ρ` in the rounded schedule: `0` if its page is in the cache right before its arrival, and at most `d_ρ(τ_ρ - a_ρ)` in any case. -/
theorem delay_le_delayBound {input : Instance Page} {X : FracSchedule Page}
    (hX : X.Feasible input) {Cs : List (Finset Page)} (hR : Rounded input X Cs)
    {ρ : Request Page} (hρ : ρ ∈ input.requests) :
    ρ.delay (Schedule.serviceTime input (toSchedule X Cs) ρ - ρ.arrival) ≤
      delayBound input X ρ (Cs.getD (beforeIdx X ρ.arrival) ∅) := by
  obtain ⟨ν, hν, h1, h2, h3⟩ := exists_fracServiceTime hX hρ
  have hcached : Schedule.CachedAt input (toSchedule X Cs) ρ.page X[ν].time :=
    cachedAt_toSchedule hR.length_eq hν le_rfl
      (fun h => List.pairwise_iff_getElem.1 hX.chronological ν (ν + 1) hν h (by omega))
      (hR.mem ν hν _ _ h2)
  have hlo := Schedule.arrival_le_serviceTime ⟨_, h1, hcached⟩
  have hhi := Schedule.serviceTime_le h1 hcached
  unfold delayBound
  split_ifs with hp
  · have hca := cachedAt_arrival (input := input) hX.chronological hR.length_eq hR.head_eq
      (by omega) hp
    have heq := le_antisymm (Schedule.serviceTime_le le_rfl hca) hlo
    rw [heq, sub_self, ρ.delay_zero, mul_zero]
  · rw [mul_one]
    exact ρ.delay_mono (by linarith)

theorem getD_zs {δ : ℝ} {X : FracSchedule Page} {j : ℕ} (hj : j < X.length) :
    (X.map fun w => zmap δ w.state).getD j 0 = zmap δ ((X.map Waypoint.state).getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-! ### `prop:rounding` -/

/-- The rounding is online. -/
theorem randomSchedule_upTo (input : Instance Page) {X : FracSchedule Page}
    (hX : X.Pairwise fun earlier later => earlier.time ≤ later.time) (t : ℝ) :
    (randomSchedule input X).map (Schedule.upTo · t) = randomSchedule input (X.upTo t) := by
  have hXt : X.upTo t = X.take (X.upTo t).length :=
    filter_eq_take (fun x y (hxy : x.time ≤ y.time) h => by
      simp only [decide_eq_true_eq] at h ⊢; linarith) hX
  have hlazy : lazyCaches input (X.upTo t) = (lazyCaches input X).take (X.upTo t).length := by
    conv_lhs => rw [hXt]
    rw [lazyCaches_take]
  rw [randomSchedule, randomSchedule, hlazy, ← roundFor_take, PMF.map_comp, PMF.map_comp]
  congr 1
  funext Cs
  exact toSchedule_upTo hX Cs t

/-- With probability `1`, the rounded schedule is feasible. -/
theorem feasible_of_mem_support {input : Instance Page} (h2 : input.PowerOfTwoWeights)
    {X : FracSchedule Page} (hX : X.Feasible input)
    (h0 : ∀ w ∈ X.head?, zmap input.delta w.state = indicator input.initialCache) :
    ∀ S ∈ (randomSchedule input X).support, S.Feasible input := by
  obtain ⟨-, hR, -, -⟩ := roundFor_spec h2 hX h0
  intro S hS
  rw [randomSchedule] at hS
  obtain ⟨Cs, hCs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hS
  have hRC := hR Cs hCs
  refine ⟨toSchedule_chronological hX.chronological Cs, fun step hstep => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hstep
    rw [getElem_toSchedule]
    exact (hRC.card_eq _ (List.getElem_mem _)).le
  · obtain ⟨ν, hν, ha, hδ, -⟩ := exists_fracServiceTime hX hρ
    exact ⟨_, ha, cachedAt_toSchedule hRC.length_eq hν le_rfl
      (fun h => List.pairwise_iff_getElem.1 hX.chronological ν (ν + 1) hν h (by omega))
      (hRC.mem ν hν _ _ hδ)⟩

/-- **`prop:rounding`**: the expected cost of the rounded schedule. -/
theorem expectedCost_le {input : Instance Page} (h2 : input.PowerOfTwoWeights)
    {X : FracSchedule Page} (hX : X.Feasible input)
    (h0 : ∀ w ∈ X.head?, zmap input.delta w.state = indicator input.initialCache) :
    ∑' S, randomSchedule input X S * ENNReal.ofReal (S.cost input) ≤
      ENNReal.ofReal (30 * X.fetchCost input + 3 * X.delayCost input + 5 * input.totalWeight) := by
  obtain ⟨hlenX, hR, hmarg, hstep⟩ := roundFor_spec h2 hX h0
  set ys := lazyCaches input X with hys
  set μ := roundFor input ys with hμ
  have hw : ∀ i, 0 ≤ input.weight i := fun i => (input.weight_pos i).le
  -- the cost of a rounded schedule
  have hpt : ∀ Cs ∈ μ.support, ENNReal.ofReal ((toSchedule X Cs).cost input) ≤
      ∑ ν ∈ Finset.range (X.length - 1),
          ENNReal.ofReal (∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, input.weight i) +
        (input.requests.map fun ρ =>
          ENNReal.ofReal (delayBound input X ρ (Cs.getD (beforeIdx X ρ.arrival) ∅))).sum := by
    intro Cs hCs
    have hRC := hR Cs hCs
    rw [Schedule.cost, fetchCost_toSchedule hRC,
      ← ENNReal.ofReal_sum_of_nonneg fun ν _ => Finset.sum_nonneg fun i _ => hw i,
      ← ofReal_list_sum _ _ fun ρ hρ => delayBound_nonneg hX hρ _]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
    exact add_le_add le_rfl (List.sum_le_sum fun ρ hρ => delay_le_delayBound hX hRC hρ)
  -- the expected fetch cost
  have hfetch : ∑ ν ∈ Finset.range (X.length - 1), ENNReal.ofReal
      (∑ CC : Finset Page × Finset Page,
        (stepLaw μ ν CC).toReal * ∑ i ∈ CC.2 \ CC.1, input.weight i) ≤
      ENNReal.ofReal (30 * X.fetchCost input + 5 * input.totalWeight) := by
    have hmove : ∑ ν ∈ Finset.range (X.length - 1),
          ∑ i, input.weight i * |ys.getD (ν + 1) 0 i - ys.getD ν 0 i| ≤
        2 * ∑ ν ∈ Finset.range (X.length - 1), ∑ i, input.weight i *
          max 0 ((X.map fun w => zmap input.delta w.state).getD (ν + 1) 0 i -
            (X.map fun w => zmap input.delta w.state).getD ν 0 i) + ∑ i, input.weight i := by
      have := sum_movement_lazySeq_le input.weight hw (zs_spec hX) (zs_head h0)
      rw [List.length_map] at this
      exact this
    have hzx : ∑ ν ∈ Finset.range (X.length - 1), ∑ i, input.weight i *
          max 0 ((X.map fun w => zmap input.delta w.state).getD (ν + 1) 0 i -
            (X.map fun w => zmap input.delta w.state).getD ν 0 i) ≤ 3 * X.fetchCost input := by
      rw [fracFetchCost_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun ν hν => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hν' : ν + 1 < X.length := by rw [Finset.mem_range] at hν; omega
      rw [getD_zs hν', getD_zs (by omega : ν < X.length)]
      have := zmap_sub_le (δ := input.delta) input.cacheSize_pos rfl ((X.map Waypoint.state).getD ν 0)
        ((X.map Waypoint.state).getD (ν + 1) 0) i
      nlinarith [mul_le_mul_of_nonneg_left this (hw i)]
    calc _ ≤ ∑ ν ∈ Finset.range (X.length - 1), ENNReal.ofReal
          (5 * ∑ i, input.weight i * |ys.getD (ν + 1) 0 i - ys.getD ν 0 i|) := by
          refine Finset.sum_le_sum fun ν hν => ENNReal.ofReal_le_ofReal ?_
          have hν' : ν + 1 < ys.length := by rw [Finset.mem_range] at hν; omega
          rw [List.getD_eq_getElem _ _ hν', List.getD_eq_getElem _ _ (by omega)]
          exact hstep ν hν'
      _ = ENNReal.ofReal (5 * ∑ ν ∈ Finset.range (X.length - 1),
          ∑ i, input.weight i * |ys.getD (ν + 1) 0 i - ys.getD ν 0 i|) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun ν _ =>
            mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (abs_nonneg _))]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Instance.totalWeight]
          linarith
  -- the expected delay cost
  have hper : ∀ ρ ∈ input.requests,
      ∑ C, (cacheLaw μ (beforeIdx X ρ.arrival) C).toReal * delayBound input X ρ C ≤
        3 * ((X.stateBefore ρ.arrival ρ.page - input.delta) *
          ρ.delay (X.serviceTime input ρ - ρ.arrival)) := by
    intro ρ hρ
    obtain ⟨ν, hν, ha, -, hτ⟩ := exists_fracServiceTime hX hρ
    have hpos : 0 < X.length := by omega
    have hmX : beforeIdx X ρ.arrival < X.length := beforeIdx_lt hpos _
    have hmy : beforeIdx X ρ.arrival < ys.length := hlenX ▸ hmX
    have hd : 0 ≤ ρ.delay (X.serviceTime input ρ - ρ.arrival) := by
      rw [← ρ.delay_zero]; exact ρ.delay_mono (by linarith)
    have e : ∑ C, (cacheLaw μ (beforeIdx X ρ.arrival) C).toReal * delayBound input X ρ C =
        ρ.delay (X.serviceTime input ρ - ρ.arrival) * (1 - ys[beforeIdx X ρ.arrival] ρ.page) := by
      rw [← hmarg _ hmy, ← sum_not_mem_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      unfold delayBound
      split_ifs <;> ring
    rw [e, stateBefore_eq hX.chronological hpos]
    have hle : zmap input.delta (X[beforeIdx X ρ.arrival]'hmX).state ρ.page ≤
        ys[beforeIdx X ρ.arrival] ρ.page := by
      have := le_lazySeq (zs_spec hX) (zs_head h0) _ hmy ρ.page
      rw [List.getElem_map] at this
      exact this
    have hz := one_sub_zmap_le (δ := input.delta) input.cacheSize_pos rfl
      (hX.bounds _ (List.getElem_mem hmX) ρ.page).1
    nlinarith [mul_le_mul_of_nonneg_left hle hd, mul_le_mul_of_nonneg_left hz hd]
  have hper0 : ∀ ρ ∈ input.requests,
      0 ≤ ∑ C, (cacheLaw μ (beforeIdx X ρ.arrival) C).toReal * delayBound input X ρ C :=
    fun ρ hρ => Finset.sum_nonneg fun C _ =>
      mul_nonneg ENNReal.toReal_nonneg (delayBound_nonneg hX hρ C)
  have hdelay : (input.requests.map fun ρ => ENNReal.ofReal
      (∑ C, (cacheLaw μ (beforeIdx X ρ.arrival) C).toReal * delayBound input X ρ C)).sum ≤
      ENNReal.ofReal (3 * X.delayCost input) := by
    calc _ ≤ (input.requests.map fun ρ => ENNReal.ofReal
          (3 * ((X.stateBefore ρ.arrival ρ.page - input.delta) *
            ρ.delay (X.serviceTime input ρ - ρ.arrival)))).sum :=
          List.sum_le_sum fun ρ hρ => ENNReal.ofReal_le_ofReal (hper ρ hρ)
      _ = ENNReal.ofReal (input.requests.map fun ρ =>
          3 * ((X.stateBefore ρ.arrival ρ.page - input.delta) *
            ρ.delay (X.serviceTime input ρ - ρ.arrival))).sum :=
          (ofReal_list_sum _ _ fun ρ hρ => (hper0 ρ hρ).trans (hper ρ hρ)).symm
      _ = ENNReal.ofReal (3 * X.delayCost input) := by
          rw [List.sum_map_mul_left]
          rfl
  have hfrac0 : 0 ≤ X.fetchCost input := by
    rw [fracFetchCost_eq]
    exact Finset.sum_nonneg fun ν _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (le_max_left _ _)
  have hdel0 : 0 ≤ 3 * X.delayCost input := by
    rw [FracSchedule.delayCost, ← List.sum_map_mul_left]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
      exact (hper0 ρ hρ).trans (hper ρ hρ)
  calc ∑' S, randomSchedule input X S * ENNReal.ofReal (S.cost input)
      = ∑' Cs, μ Cs * ENNReal.ofReal ((toSchedule X Cs).cost input) := by
        rw [randomSchedule]
        exact tsum_map_mul _ _ _
    _ ≤ ∑' Cs, μ Cs * (∑ ν ∈ Finset.range (X.length - 1),
          ENNReal.ofReal (∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, input.weight i) +
        (input.requests.map fun ρ =>
          ENNReal.ofReal (delayBound input X ρ (Cs.getD (beforeIdx X ρ.arrival) ∅))).sum) :=
        ENNReal.tsum_le_tsum fun Cs => by
          by_cases hCs : Cs ∈ μ.support
          · gcongr
            exact hpt Cs hCs
          · rw [PMF.mem_support_iff, not_not] at hCs
            simp [hCs]
    _ = ∑ ν ∈ Finset.range (X.length - 1), ENNReal.ofReal
          (∑ CC : Finset Page × Finset Page,
            (stepLaw μ ν CC).toReal * ∑ i ∈ CC.2 \ CC.1, input.weight i) +
        (input.requests.map fun ρ => ENNReal.ofReal
          (∑ C, (cacheLaw μ (beforeIdx X ρ.arrival) C).toReal * delayBound input X ρ C)).sum := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
        congr 1
        · calc _ = ∑' Cs, ∑ ν ∈ Finset.range (X.length - 1), μ Cs *
                ENNReal.ofReal (∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, input.weight i) :=
                tsum_congr fun Cs => Finset.mul_sum _ _ _
            _ = ∑ ν ∈ Finset.range (X.length - 1), ∑' Cs, μ Cs *
                ENNReal.ofReal (∑ i ∈ Cs.getD (ν + 1) ∅ \ Cs.getD ν ∅, input.weight i) :=
                Summable.tsum_finsetSum fun _ _ => ENNReal.summable
            _ = _ := Finset.sum_congr rfl fun ν _ =>
                tsum_mul_ofReal_eq μ (fun Cs => (Cs.getD ν ∅, Cs.getD (ν + 1) ∅))
                  (fun CC => ∑ i ∈ CC.2 \ CC.1, input.weight i)
                  fun CC => Finset.sum_nonneg fun i _ => hw i
        · rw [tsum_mul_list_sum]
          exact congrArg List.sum (List.map_congr_left fun ρ hρ =>
            tsum_mul_ofReal_eq μ (fun Cs => Cs.getD (beforeIdx X ρ.arrival) ∅)
              (delayBound input X ρ) (delayBound_nonneg hX hρ))
    _ ≤ ENNReal.ofReal (30 * X.fetchCost input + 5 * input.totalWeight) +
        ENNReal.ofReal (3 * X.delayCost input) := add_le_add hfetch hdelay
    _ = _ := by
        rw [← ENNReal.ofReal_add (by
          have := Instance.totalWeight_nonneg (input.valid); positivity) hdel0]
        congr 1
        ring

end Rounding

end PagingWithDelay
