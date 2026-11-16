import PagingWithDelay.BBN.Defs

/-! BBN's class profiles `n(α)` and their coupling. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option linter.unusedSectionVars false

namespace PagingWithDelay.BBN.Profile
open PagingWithDelay.BBN

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-! ### Generic measure glue -/

theorem sum_toPMF {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (g : ℝ → β) (hg : Measurable g) [IsProbabilityMeasure (unif.map g)] (f : β → ℝ) :
    ∑ b, ((unif.map g).toPMF b).toReal * f b = ∫ α, f (g α) ∂unif := by
  rw [← integral_map hg.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    integral_fintype _ Integrable.of_finite]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Measure.toPMF_apply, smul_eq_mul, measureReal_def]

theorem exists_of_mem_support {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (g : ℝ → β) (hg : Measurable g)
    [IsProbabilityMeasure (unif.map g)] {b : β} (hb : b ∈ ((unif.map g).toPMF).support) :
    ∃ α ∈ Set.Ico (0 : ℝ) 1, g α = b := by
  rw [PMF.mem_support_iff, Measure.toPMF_apply, Measure.map_apply hg (measurableSet_singleton b),
    unif, Measure.restrict_apply (hg (measurableSet_singleton b))] at hb
  by_contra h
  apply hb
  have : g ⁻¹' {b} ∩ Set.Ico 0 1 = ∅ := by
    ext α
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2
    exact h ⟨α, h2, h1⟩
  rw [this, measure_empty]

theorem map_toPMF {β γ : Type*} [Fintype β] [Fintype γ] [MeasurableSpace β]
    [MeasurableSingletonClass β] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (g : ℝ → β) (hg : Measurable g) [IsProbabilityMeasure (unif.map g)] (f : β → γ)
    (h : ℝ → γ) [IsProbabilityMeasure (unif.map h)] (hfg : ∀ α, f (g α) = h α) :
    ((unif.map g).toPMF).map f = (unif.map h).toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ (hf := measurable_of_finite f), Measure.toPMF_toMeasure,
    Measure.toPMF_toMeasure, Measure.map_map (measurable_of_finite f) hg]
  congr 1
  funext α
  exact hfg α


/-! ### Ceilings of `x - α` for uniform `α` -/

theorem ae_Ico : ∀ᵐ α ∂unif, α ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico

theorem ceil_sub_eq (x α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ⌈x - α⌉ = ⌊x⌋ + if α < Int.fract x then 1 else 0 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hf : Int.fract x = x - ⌊x⌋ := rfl
  obtain ⟨h0, h1'⟩ := hα
  split_ifs with h
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

theorem ceil_ae (x : ℝ) : (fun α : ℝ => ((⌈x - α⌉ : ℤ) : ℝ)) =ᵐ[unif]
    fun α => (⌊x⌋ : ℝ) + (Set.Iio (Int.fract x)).indicator (fun _ => (1 : ℝ)) α := by
  filter_upwards [ae_Ico] with α hα
  rw [ceil_sub_eq x α hα, Set.indicator_apply]
  by_cases h : α < Int.fract x <;> simp [h]

theorem integrable_ceil (x : ℝ) : Integrable (fun α : ℝ => ((⌈x - α⌉ : ℤ) : ℝ)) unif :=
  ((integrable_const _).add ((integrable_const (1 : ℝ)).indicator measurableSet_Iio)).congr
    (ceil_ae x).symm

theorem integral_ceil (x : ℝ) : ∫ α, ((⌈x - α⌉ : ℤ) : ℝ) ∂unif = x := by
  rw [integral_congr_ae (ceil_ae x), integral_add (integrable_const _)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio), integral_const,
    integral_indicator_const _ measurableSet_Iio]
  have hI : Set.Iio (Int.fract x) ∩ Set.Ico 0 1 = Set.Ico 0 (Int.fract x) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    have := Int.fract_lt_one x
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [probReal_univ, one_smul, smul_eq_mul, mul_one, measureReal_def, unif,
    Measure.restrict_apply measurableSet_Iio, hI, Real.volume_Ico, sub_zero,
    ENNReal.toReal_ofReal (Int.fract_nonneg x)]
  exact Int.floor_add_fract x

theorem integral_abs_ceil_sub (x x' : ℝ) :
    ∫ α, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| ∂unif = |x' - x| := by
  rcases le_total x x' with h | h
  · have hp : ∀ α : ℝ, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| =
        ((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ) := fun α => by
      apply abs_of_nonneg
      have : ⌈x - α⌉ ≤ ⌈x' - α⌉ := Int.ceil_mono (by linarith)
      have : ((⌈x - α⌉ : ℤ) : ℝ) ≤ ((⌈x' - α⌉ : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    simp_rw [hp]
    rw [integral_sub (integrable_ceil _) (integrable_ceil _), integral_ceil, integral_ceil,
      abs_of_nonneg (by linarith)]
  · have hp : ∀ α : ℝ, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| =
        ((⌈x - α⌉ : ℤ) : ℝ) - ((⌈x' - α⌉ : ℤ) : ℝ) := fun α => by
      rw [abs_sub_comm]
      apply abs_of_nonneg
      have : ⌈x' - α⌉ ≤ ⌈x - α⌉ := Int.ceil_mono (by linarith)
      have : ((⌈x' - α⌉ : ℤ) : ℝ) ≤ ((⌈x - α⌉ : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    simp_rw [hp]
    rw [integral_sub (integrable_ceil _) (integrable_ceil _), integral_ceil, integral_ceil,
      abs_sub_comm, abs_of_nonneg (by linarith)]

theorem ceil_sub_bounds (a b α : ℝ) :
    a - b - 1 < (((⌈a - α⌉ - ⌈b - α⌉ : ℤ)) : ℝ) ∧ (((⌈a - α⌉ - ⌈b - α⌉ : ℤ)) : ℝ) < a - b + 1 := by
  have h1 := Int.le_ceil (a - α)
  have h2 := Int.ceil_lt_add_one (a - α)
  have h3 := Int.le_ceil (b - α)
  have h4 := Int.ceil_lt_add_one (b - α)
  push_cast
  constructor <;> linarith

/-! ### Class masses -/

variable (w : Page → ℝ)

/-- The raw count `n_v(α)` (without truncation). -/
def rawN (y : Page → ℝ) (α v : ℝ) : ℤ := ⌈massLE w y v - α⌉ - ⌈massLT w y v - α⌉

theorem massLE_sub_massLT (y : Page → ℝ) (v : ℝ) :
    massLE w y v - massLT w y v = classMass w y v := by
  unfold massLE massLT classMass cls
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases lt_trichotomy (w q) v with h | h | h
  · simp [h, h.le, h.ne]
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']

theorem classMass_nonneg {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (v : ℝ) :
    0 ≤ classMass w y v := Finset.sum_nonneg fun i _ => (h01 i).1

theorem classMass_le {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (v : ℝ) :
    classMass w y v ≤ Fintype.card Page := by
  calc classMass w y v ≤ ∑ q ∈ cls w v, (1 : ℝ) := Finset.sum_le_sum fun i _ => (h01 i).2
    _ = (cls w v).card := by simp
    _ ≤ Fintype.card Page := by exact_mod_cast Finset.card_le_univ _

theorem slots_cast {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (α : ℝ) (v : WClass w) :
    (((slots w y α v : ℕ)) : ℝ) = ((rawN w y α v : ℤ) : ℝ) := by
  have hb := ceil_sub_bounds (massLE w y v) (massLT w y v) α
  rw [massLE_sub_massLT] at hb
  have hm0 := classMass_nonneg w h01 v
  have hmN := classMass_le w h01 v
  have hn0 : 0 ≤ rawN w y α v := by
    have : (-1 : ℝ) < ((rawN w y α v : ℤ) : ℝ) := by unfold rawN; linarith [hb.1]
    have : (-1 : ℤ) < rawN w y α v := by exact_mod_cast this
    omega
  have hnN : rawN w y α v ≤ Fintype.card Page := by
    have : ((rawN w y α v : ℤ) : ℝ) < (Fintype.card Page : ℝ) + 1 := by unfold rawN; linarith [hb.2]
    have : rawN w y α v < (Fintype.card Page : ℤ) + 1 := by exact_mod_cast this
    omega
  have e : ((slots w y α v : ℕ)) = (rawN w y α v).toNat := by
    simp only [slots]
    unfold rawN at hnN hn0 ⊢
    omega
  rw [e]
  have := Int.toNat_of_nonneg hn0
  exact_mod_cast this

/-! ### Telescoping over classes -/

theorem tele (y : Page → ℝ) (α : ℝ) (s : Finset ℝ) :
    (∀ v ∈ Finset.univ.image w, ∀ u ∈ s, v ≤ u → v ∈ s) →
    ∑ v ∈ s, rawN w y α v =
      ⌈(∑ q ∈ Finset.univ.filter (fun q => w q ∈ s), y q) - α⌉ - ⌈(0 : ℝ) - α⌉ := by
  induction s using Finset.induction_on_max with
  | h0 => intro _; simp
  | step a s hlt ih =>
    intro hdc
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdc' : ∀ v ∈ Finset.univ.image w, ∀ u ∈ s, v ≤ u → v ∈ s := by
      intro v hv u hu hvu
      rcases Finset.mem_insert.mp (hdc v hv u (Finset.mem_insert_of_mem hu) hvu) with h | h
      · subst h; exact absurd hvu (not_le.mpr (hlt u hu))
      · exact h
    rw [Finset.sum_insert ha, ih hdc']
    have hT : ∀ q, w q ∈ Finset.univ.image w := fun q => Finset.mem_image_of_mem w (Finset.mem_univ q)
    have e1 : massLE w y a = ∑ q ∈ Finset.univ.filter (fun q => w q ∈ insert a s), y q := by
      unfold massLE
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h']; exact Finset.mem_insert_self a s
        · exact hdc (w q) (hT q) a (Finset.mem_insert_self a s) h
      · intro h
        rcases Finset.mem_insert.mp h with h' | h'
        · exact h'.le
        · exact (hlt _ h').le
    have e2 : massLT w y a = ∑ q ∈ Finset.univ.filter (fun q => w q ∈ s), y q := by
      unfold massLT
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases Finset.mem_insert.mp (hdc (w q) (hT q) a (Finset.mem_insert_self a s) h.le)
          with h' | h'
        · exact absurd h' h.ne
        · exact h'
      · exact hlt _
    unfold rawN
    rw [e1, e2]
    ring

theorem sum_rawN {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) : ∑ v : WClass w, rawN w y α v = k := by
  rw [Finset.sum_coe_sort (Finset.univ.image w) (fun v => rawN w y α v)]
  rw [tele w y α _ (fun v hv _ _ _ => hv)]
  have hf : Finset.univ.filter (fun q => w q ∈ Finset.univ.image w) = Finset.univ :=
    Finset.filter_true_of_mem fun q _ => Finset.mem_image_of_mem w (Finset.mem_univ q)
  rw [hf, hy.2]
  obtain ⟨h0, h1⟩ := hα
  have c1 : ⌈(k : ℝ) - α⌉ = k := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have c2 : ⌈(0 : ℝ) - α⌉ = 0 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  rw [c1, c2, sub_zero]

theorem card_eq_sum_cls (C : Finset Page) :
    C.card = ∑ v : WClass w, (C ∩ cls w v).card := by
  rw [Finset.sum_coe_sort (Finset.univ.image w) (fun v => (C ∩ cls w v).card),
    Finset.card_eq_sum_card_fiberwise (f := w) (t := Finset.univ.image w)
      (fun q _ => Finset.mem_image_of_mem w (Finset.mem_univ q))]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext q
  simp [cls]

/-! ### The weighted movement bound -/

theorem geo (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) (s : Finset ℝ) :
    ∀ u ∈ Finset.univ.image w, (Finset.univ.image w).filter (· < u) = s → ∑ v ∈ s, v ≤ u := by
  induction s using Finset.induction_on_max with
  | h0 =>
    intro u hu _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    simpa using (hw i).le
  | step a s hlt ih =>
    intro u hu hs
    have haT : a ∈ Finset.univ.image w ∧ a < u := by
      have : a ∈ insert a s := Finset.mem_insert_self a s
      rw [← hs] at this
      exact Finset.mem_filter.mp this
    have h2a : 2 * a ≤ u := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haT.1
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
      exact hw2 i j haT.2
    have hs' : (Finset.univ.image w).filter (· < a) = s := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hvT, hva⟩
        have : v ∈ (Finset.univ.image w).filter (· < u) :=
          Finset.mem_filter.mpr ⟨hvT, hva.trans haT.2⟩
        rw [hs] at this
        rcases Finset.mem_insert.mp this with h | h
        · exact absurd h hva.ne
        · exact h
      · intro hv
        have : v ∈ insert a s := Finset.mem_insert_of_mem hv
        rw [← hs] at this
        exact ⟨(Finset.mem_filter.mp this).1, hlt v hv⟩
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.sum_insert ha]
    have := ih a haT.1 hs'
    linarith

theorem exch_lt (T : Finset ℝ) (d : Page → ℝ) :
    ∑ v ∈ T, v * ∑ i ∈ Finset.univ.filter (fun i => v < w i), d i =
      ∑ i, d i * ∑ v ∈ T.filter (fun v => v < w i), v := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

theorem exch_le (T : Finset ℝ) (d : Page → ℝ) :
    ∑ v ∈ T, v * ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), d i =
      ∑ i, d i * ∑ v ∈ T.filter (fun v => v ≤ w i), v := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

theorem abs_massLE_sub {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) (v : ℝ) :
    |massLE w y' v - massLE w y v| ≤
      ∑ i ∈ Finset.univ.filter (fun i => v < w i), |y' i - y i| := by
  have hd : ∑ i, (y' i - y i) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => w i ≤ v)
    (fun i => y' i - y i)
  rw [hd] at hsplit
  have e : massLE w y' v - massLE w y v =
      -∑ i ∈ Finset.univ.filter (fun i => ¬ w i ≤ v), (y' i - y i) := by
    unfold massLE; rw [← Finset.sum_sub_distrib]; linarith
  rw [e, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.filter_congr (fun i _ => not_le)]

theorem abs_massLT_sub {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) (v : ℝ) :
    |massLT w y' v - massLT w y v| ≤
      ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), |y' i - y i| := by
  have hd : ∑ i, (y' i - y i) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => w i < v)
    (fun i => y' i - y i)
  rw [hd] at hsplit
  have e : massLT w y' v - massLT w y v =
      -∑ i ∈ Finset.univ.filter (fun i => ¬ w i < v), (y' i - y i) := by
    unfold massLT; rw [← Finset.sum_sub_distrib]; linarith
  rw [e, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.filter_congr (fun i _ => not_lt)]

theorem comb (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j)
    {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) :
    ∑ v : WClass w, (v : ℝ) * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|) ≤
      3 * ∑ i, w i * |y' i - y i| := by
  set T := Finset.univ.image w with hT
  rw [Finset.sum_coe_sort T (fun v => v * (|massLE w y' v - massLE w y v| +
    |massLT w y' v - massLT w y v|))]
  calc ∑ v ∈ T, v * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|)
      ≤ ∑ v ∈ T, v * (∑ i ∈ Finset.univ.filter (fun i => v < w i), |y' i - y i| +
          ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), |y' i - y i|) := by
        refine Finset.sum_le_sum fun v hv => ?_
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        exact mul_le_mul_of_nonneg_left
          (add_le_add (abs_massLE_sub w hs _) (abs_massLT_sub w hs _)) (hw j).le
    _ = ∑ i, |y' i - y i| * (∑ v ∈ T.filter (fun v => v < w i), v +
          ∑ v ∈ T.filter (fun v => v ≤ w i), v) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [exch_lt, exch_le]
    _ ≤ ∑ i, |y' i - y i| * (3 * w i) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hwi : w i ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ i)
        have g := geo w hw hw2 _ (w i) hwi rfl
        have hins : T.filter (fun v => v ≤ w i) = insert (w i) (T.filter (fun v => v < w i)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            rcases eq_or_lt_of_le h2 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h1, h⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨hwi, le_rfl⟩
            · exact ⟨h1, h2.le⟩
        rw [hins, Finset.sum_insert (by simp)]
        linarith
    _ = 3 * ∑ i, w i * |y' i - y i| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Integral cache -/

theorem indicator_mem01 (C₀ : Finset Page) : ∀ i, 0 ≤ indicator C₀ i ∧ indicator C₀ i ≤ 1 := by
  intro i; unfold indicator; split_ifs <;> norm_num

theorem sum_indicator (C₀ s : Finset Page) :
    ∑ q ∈ s, indicator C₀ q = ((s ∩ C₀).card : ℝ) := by
  simp [indicator]

theorem ceil_nat_sub (m : ℕ) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) : ⌈(m : ℝ) - α⌉ = m := by
  obtain ⟨h0, h1⟩ := hα
  rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

end PagingWithDelay.BBN.Profile

namespace PagingWithDelay.BBN
variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem rhoLaw_fst (y y' : Page → ℝ) : (rhoLaw w y y').map Prod.fst = profLaw w y :=
  Profile.map_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y')) _ _ fun _ => rfl

theorem rhoLaw_snd (y y' : Page → ℝ) : (rhoLaw w y y').map Prod.snd = profLaw w y' :=
  Profile.map_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y')) _ _ fun _ => rfl

end PagingWithDelay.BBN

namespace PagingWithDelay.BBN
variable {Page : Type*} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem profLaw_bounds {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {c : Prof w}
    (hc : c ∈ (profLaw w y).support) (v : WClass w) :
    classMass w y v - 1 < ((c v : ℕ) : ℝ) ∧ ((c v : ℕ) : ℝ) < classMass w y v + 1 := by
  obtain ⟨α, -, rfl⟩ := Profile.exists_of_mem_support _ (measurable_slots w y) hc
  rw [Profile.slots_cast w hy.1, ← Profile.massLE_sub_massLT]
  exact Profile.ceil_sub_bounds _ _ _

theorem card_of_profLaw {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {c : Prof w}
    (hc : c ∈ (profLaw w y).support) (C : Finset Page) (hC : profile w C = c) : C.card = k := by
  obtain ⟨α, hα, rfl⟩ := Profile.exists_of_mem_support _ (measurable_slots w y) hc
  have h : (C.card : ℝ) = k := by
    rw [Profile.card_eq_sum_cls w C]
    push_cast
    have : ∀ v : WClass w, (((C ∩ cls w v).card : ℕ) : ℝ) = ((Profile.rawN w y α v : ℤ) : ℝ) := by
      intro v
      rw [← Profile.slots_cast w hy.1 α v, ← hC]
      rfl
    simp_rw [this]
    exact_mod_cast Profile.sum_rawN w hy hα
  exact_mod_cast h

theorem profLaw_mean {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) (v : WClass w) :
    ∑ c, (profLaw w y c).toReal * ((c v : ℕ) : ℝ) = classMass w y v := by
  unfold profLaw
  rw [Profile.sum_toPMF _ (measurable_slots w y) (fun c => ((c v : ℕ) : ℝ))]
  simp_rw [Profile.slots_cast w hy.1, Profile.rawN]
  push_cast
  rw [integral_sub (Profile.integrable_ceil _) (Profile.integrable_ceil _), Profile.integral_ceil,
    Profile.integral_ceil, Profile.massLE_sub_massLT]

theorem rhoLaw_move (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) {k : ℕ}
    {y y' : Page → ℝ} (hy : y ∈ fracCaches k) (hy' : y' ∈ fracCaches k) :
    ∑ x, (rhoLaw w y y' x).toReal *
        ∑ v : WClass w, (v : ℝ) * |((x.2 v : ℕ) : ℝ) - ((x.1 v : ℕ) : ℝ)| ≤
      3 * ∑ i, w i * |y' i - y i| := by
  unfold rhoLaw
  rw [Profile.sum_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y'))
    (fun x => ∑ v : WClass w, (v : ℝ) * |((x.2 v : ℕ) : ℝ) - ((x.1 v : ℕ) : ℝ)|)]
  simp_rw [Profile.slots_cast w hy.1, Profile.slots_cast w hy'.1, Profile.rawN]
  push_cast
  have ic := Profile.integrable_ceil
  have hpos : ∀ v : WClass w, 0 ≤ (v : ℝ) := fun v => by
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp v.2
    rw [← h]; exact (hw j).le
  calc ∫ α, ∑ v : WClass w, (v : ℝ) *
        |((⌈massLE w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          (((⌈massLE w y v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y v - α⌉ : ℤ) : ℝ))| ∂unif
      ≤ ∫ α, ∑ v : WClass w, (v : ℝ) *
        (|((⌈massLE w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLE w y v - α⌉ : ℤ) : ℝ)| +
          |((⌈massLT w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y v - α⌉ : ℤ) : ℝ)|) ∂unif := by
        refine integral_mono
          (integrable_finset_sum _ fun v _ =>
            (((ic _).sub (ic _)).sub ((ic _).sub (ic _))).abs.const_mul _)
          (integrable_finset_sum _ fun v _ =>
            (((ic _).sub (ic _)).abs.add ((ic _).sub (ic _)).abs).const_mul _) fun α => ?_
        refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (hpos v)
        rw [abs_le]
        constructor <;> linarith [le_abs_self (((⌈massLE w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLE w y v - α⌉ : ℤ) : ℝ)), neg_abs_le (((⌈massLE w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLE w y v - α⌉ : ℤ) : ℝ)), le_abs_self (((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLT w y v - α⌉ : ℤ) : ℝ)), neg_abs_le (((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLT w y v - α⌉ : ℤ) : ℝ))]
    _ = ∑ v : WClass w, (v : ℝ) * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|) := by
        rw [integral_finset_sum]
        · refine Finset.sum_congr rfl fun v _ => ?_
          rw [integral_const_mul, integral_add, Profile.integral_abs_ceil_sub,
            Profile.integral_abs_ceil_sub]
          · exact ((ic _).sub (ic _)).abs
          · exact ((ic _).sub (ic _)).abs
        · intro v _
          exact (((ic _).sub (ic _)).abs.add ((ic _).sub (ic _)).abs).const_mul _
    _ ≤ 3 * ∑ i, w i * |y' i - y i| := Profile.comb w hw hw2 (by rw [hy.2, hy'.2])

theorem profLaw_indicator (C₀ : Finset Page) :
    profLaw w (indicator C₀) = PMF.pure (profile w C₀) := by
  unfold profLaw
  apply PMF.toMeasure_injective
  have hae : slots w (indicator C₀) =ᵐ[unif] fun _ => profile w C₀ := by
    filter_upwards [Profile.ae_Ico] with α hα
    funext v
    apply Fin.ext
    have h := Profile.slots_cast w (Profile.indicator_mem01 C₀) α v
    have hm := Profile.massLE_sub_massLT w (indicator C₀) v
    unfold Profile.rawN at h
    unfold massLE at h hm
    unfold massLT at h hm
    unfold classMass at hm
    rw [Profile.sum_indicator, Profile.sum_indicator] at h hm
    rw [Profile.sum_indicator] at hm
    rw [Profile.ceil_nat_sub _ hα, Profile.ceil_nat_sub _ hα] at h
    push_cast at h
    rw [hm, Finset.inter_comm] at h
    exact_mod_cast h
  rw [Measure.toPMF_toMeasure, PMF.toMeasure_pure, Measure.map_congr hae, Measure.map_const,
    measure_univ, one_smul]

end PagingWithDelay.BBN
