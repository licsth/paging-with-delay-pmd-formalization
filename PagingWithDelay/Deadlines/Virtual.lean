import PagingWithDelay.Deadlines.Model

/-!
# Virtual time and the virtual instance

Request `r` gets a gap of length `ε_r = 3^(-N)` behind the virtual time of its deadline, where `N` is the number of requests arrived by `a_r`; the gaps of later requests sum to at most `ε_r / 2` (`fsum_after_le`). Its virtual delay is `0` up to the virtual time of its deadline and rises to `2 ∑ᵢ wᵢ` inside its gap (the ramp). `realTime` maps virtual time back (`gc`).
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

namespace Deadlines

variable {Page : Type*}

/-! ## Generic facts about lists -/

theorem sum_filter_split {α : Type*} (l : List α) (f : α → ℝ) (p q : α → Bool) :
    ((l.filter p).map f).sum =
      ((l.filter fun a => p a && q a).map f).sum + ((l.filter fun a => p a && !q a).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq, ih] <;> ring

theorem length_filter_split {α : Type*} (l : List α) (p q : α → Bool) :
    (l.filter p).length =
      (l.filter fun a => p a && q a).length + (l.filter fun a => p a && !q a).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq, ih] <;> omega

/-- `∑_{x ∈ M} 3^{-#{y ∈ M : y ≤ x}} ≤ (1 - 3^{-|M|}) / 2`. -/
theorem geom_sum_le : ∀ (n : ℕ) (M : List ℝ), M.length = n →
    (M.map fun x => (1 / 3 : ℝ) ^ (M.filter fun y => decide (y ≤ x)).length).sum ≤
      (1 - (1 / 3 : ℝ) ^ n) / 2 := by
  intro n
  induction n with
  | zero =>
    intro M hM
    rw [List.length_eq_zero_iff.1 hM]
    simp
  | succ n ih =>
    intro M hM
    have hne : M ≠ [] := by rintro rfl; simp at hM
    obtain ⟨m, hm, hmax⟩ : ∃ m ∈ M, ∀ x ∈ M, x ≤ m := by
      obtain ⟨m, hm, h⟩ := M.toFinset.exists_max_image id (List.toFinset_nonempty_iff M |>.2 hne)
      exact ⟨m, List.mem_toFinset.1 hm, fun x hx => h x (List.mem_toFinset.2 hx)⟩
    have hlen : (M.erase m).length = n := by
      rw [List.length_erase_of_mem hm, hM]; rfl
    rw [((List.perm_cons_erase hm).map _).sum_eq, List.map_cons, List.sum_cons]
    have h1 : (M.filter fun y => decide (y ≤ m)).length = n + 1 := by
      rw [List.filter_eq_self.2 (fun x hx => by simpa using hmax x hx), hM]
    have h2 : ((M.erase m).map fun x =>
          (1 / 3 : ℝ) ^ (M.filter fun y => decide (y ≤ x)).length).sum ≤
        ((M.erase m).map fun x =>
          (1 / 3 : ℝ) ^ ((M.erase m).filter fun y => decide (y ≤ x)).length).sum := by
      apply List.sum_le_sum
      intro x _
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        ((List.erase_sublist.filter _).length_le)
    have h3 := ih (M.erase m) hlen
    rw [h1]
    have h4 : (1 / 3 : ℝ) ^ (n + 1) = (1 / 3) ^ n / 3 := by rw [pow_succ]; ring
    rw [h4]
    linarith

/-- In a list of reals, there is a point `t' ∈ (t, t + δ]` with no element in `(t, t')`. -/
theorem exists_gap (L : List ℝ) (t δ : ℝ) (hδ : 0 < δ) :
    ∃ t', t < t' ∧ t' ≤ t + δ ∧ ∀ x ∈ L, t < x → t' ≤ x := by
  induction L with
  | nil => exact ⟨t + δ, by linarith, le_rfl, by simp⟩
  | cons x L ih =>
    obtain ⟨t', h1, h2, h3⟩ := ih
    by_cases hx : t < x
    · refine ⟨min t' x, lt_min h1 hx, (min_le_left _ _).trans h2, ?_⟩
      intro y hy hty
      rcases List.mem_cons.1 hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h3 y hy hty)
    · refine ⟨t', h1, h2, ?_⟩
      intro y hy hty
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hty hx
      · exact h3 y hy hty

/-! ## Virtual time -/

section VirtualTime

variable (R : List (DeadlineRequest Page))

/-- The number of requests that have arrived by time `x` (with multiplicity). -/
noncomputable def count (x : ℝ) : ℕ := (R.filter fun r => decide (r.arrival ≤ x)).length

/-- The length `ε_r = 3^(-N)` of the gap of `r`, where `N` is the number of requests arrived by `a_r`. -/
noncomputable def eps (r : DeadlineRequest Page) : ℝ := (1 / 3 : ℝ) ^ count R r.arrival

/-- The total gap length of the requests satisfying `p`. -/
noncomputable def fsum (p : DeadlineRequest Page → Bool) : ℝ := ((R.filter p).map (eps R)).sum

/-- The total gap length of the deadlines before `t`. -/
noncomputable def shift (t : ℝ) : ℝ := fsum R fun r => decide (r.deadline < t)

/-- The total gap length of the deadlines up to `t`. -/
noncomputable def shiftR (t : ℝ) : ℝ := fsum R fun r => decide (r.deadline ≤ t)

/-- The virtual time of the events (arrivals and deadlines) at real time `t`. -/
noncomputable def vtime (t : ℝ) : ℝ := t + shift R t

/-- The virtual time at the end of the gaps of the deadlines at real time `t`. -/
noncomputable def vtimeR (t : ℝ) : ℝ := t + shiftR R t

/-- The gaps of the deadlines in `[a_r, d_r)` that are known at the arrival of `r`. -/
noncomputable def known (r : DeadlineRequest Page) : ℝ :=
  fsum R fun r' => decide (r'.arrival ≤ r.arrival ∧ r.arrival ≤ r'.deadline ∧ r'.deadline < r.deadline)

/-- The start of the ramp of `r`, relative to its virtual arrival. -/
noncomputable def start (r : DeadlineRequest Page) : ℝ :=
  r.deadline - r.arrival + known R r + eps R r / 2

/-- The end of the ramp of `r`, in virtual time. -/
noncomputable def rampEnd (r : DeadlineRequest Page) : ℝ :=
  vtime R r.arrival + start R r + eps R r / 2

/-- The real time of the virtual time `v`. -/
noncomputable def realTime (v : ℝ) : ℝ := sSup {t | vtime R t ≤ v}

variable {R}

theorem eps_pos (r : DeadlineRequest Page) : 0 < eps R r := by
  unfold eps; positivity

theorem fsum_nonneg (p : DeadlineRequest Page → Bool) : 0 ≤ fsum R p :=
  List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨r, -, rfl⟩; exact (eps_pos r).le)

theorem fsum_congr {p q : DeadlineRequest Page → Bool} (h : ∀ r ∈ R, p r = q r) :
    fsum R p = fsum R q := by
  unfold fsum; rw [List.filter_congr h]

theorem fsum_mono {p q : DeadlineRequest Page → Bool} (h : ∀ r ∈ R, p r = true → q r = true) :
    fsum R p ≤ fsum R q := by
  unfold fsum
  have : R.filter p = (R.filter q).filter p := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r hr
    cases hp : p r <;> simp [hp, h r hr]
  rw [this]
  exact ((List.filter_sublist).map _).sum_le_sum
    (by simp only [List.mem_map]; rintro _ ⟨r, -, rfl⟩; exact (eps_pos r).le)

theorem fsum_split (p q : DeadlineRequest Page → Bool) :
    fsum R p = fsum R (fun r => p r && q r) + fsum R (fun r => p r && !q r) :=
  sum_filter_split R (eps R) p q

theorem eps_le_fsum {p : DeadlineRequest Page → Bool} {r : DeadlineRequest Page} (hr : r ∈ R)
    (hp : p r = true) : eps R r ≤ fsum R p :=
  List.single_le_sum (by simp only [List.mem_map]; rintro _ ⟨r, -, rfl⟩; exact (eps_pos r).le) _
    (List.mem_map_of_mem (List.mem_filter.2 ⟨hr, hp⟩))

/-- The gaps of the requests arriving after `a` sum to at most `3^(-count a) / 2`. -/
theorem fsum_after_le (a : ℝ) :
    fsum R (fun r => decide (a < r.arrival)) ≤ (1 / 3 : ℝ) ^ count R a / 2 := by
  set M := R.filter fun r => decide (a < r.arrival) with hM
  have hc : ∀ r ∈ M, count R r.arrival =
      count R a + (M.filter fun r' => decide (r'.arrival ≤ r.arrival)).length := by
    intro r hr
    have har : a < r.arrival := by simpa [hM] using (List.mem_filter.1 hr).2
    unfold count
    rw [length_filter_split R _ (fun r' => decide (r'.arrival ≤ a))]
    congr 1
    · congr 1
      apply List.filter_congr
      intro r' _
      by_cases h : r'.arrival ≤ a
      · simp [h, h.trans har.le]
      · simp [h]
    · rw [hM, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro r' _
      by_cases h : r'.arrival ≤ a <;> simp [h, not_le.1]
  have hsum : fsum R (fun r => decide (a < r.arrival)) =
      (1 / 3 : ℝ) ^ count R a *
        (M.map fun r => (1 / 3 : ℝ) ^ (M.filter fun r' => decide (r'.arrival ≤ r.arrival)).length).sum := by
    rw [← List.sum_map_mul_left]
    unfold fsum
    rw [← hM]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [eps, hc r hr, pow_add]
  have hgeom := geom_sum_le _ (M.map DeadlineRequest.arrival) rfl
  have hgeom' : (M.map fun r =>
      (1 / 3 : ℝ) ^ (M.filter fun r' => decide (r'.arrival ≤ r.arrival)).length).sum ≤ 1 / 2 := by
    have : (M.map fun r =>
        (1 / 3 : ℝ) ^ (M.filter fun r' => decide (r'.arrival ≤ r.arrival)).length) =
        ((M.map DeadlineRequest.arrival).map fun x =>
          (1 / 3 : ℝ) ^ ((M.map DeadlineRequest.arrival).filter fun y => decide (y ≤ x)).length) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      simp only [Function.comp, List.filter_map, List.length_map]
      rfl
    rw [this]
    have : 0 ≤ (1 / 3 : ℝ) ^ (M.map DeadlineRequest.arrival).length := by positivity
    linarith
  rw [hsum]
  have : 0 ≤ (1 / 3 : ℝ) ^ count R a := by positivity
  nlinarith

theorem shift_nonneg (t : ℝ) : 0 ≤ shift R t := fsum_nonneg _

theorem shift_le_total (t : ℝ) : shift R t ≤ fsum R fun _ => true :=
  fsum_mono fun _ _ _ => rfl

theorem shift_le_shiftR (t : ℝ) : shift R t ≤ shiftR R t :=
  fsum_mono fun r _ h => by simp only [decide_eq_true_eq] at h ⊢; exact h.le

theorem shift_mono {t t' : ℝ} (h : t ≤ t') : shift R t ≤ shift R t' :=
  fsum_mono fun r _ hr => by simp only [decide_eq_true_eq] at hr ⊢; linarith

theorem shiftR_mono {t t' : ℝ} (h : t ≤ t') : shiftR R t ≤ shiftR R t' :=
  fsum_mono fun r _ hr => by simp only [decide_eq_true_eq] at hr ⊢; linarith

theorem shiftR_le_shift {t t' : ℝ} (h : t < t') : shiftR R t ≤ shift R t' :=
  fsum_mono fun r _ hr => by simp only [decide_eq_true_eq] at hr ⊢; linarith

theorem vtime_mono : Monotone (vtime R) := fun _ _ h => add_le_add h (shift_mono h)

theorem vtimeR_mono : Monotone (vtimeR R) := fun _ _ h => add_le_add h (shiftR_mono h)

theorem vtime_le_vtimeR (t : ℝ) : vtime R t ≤ vtimeR R t :=
  add_le_add le_rfl (shift_le_shiftR t)

theorem vtimeR_lt_vtime {t t' : ℝ} (h : t < t') : vtimeR R t < vtime R t' := by
  unfold vtimeR vtime; linarith [shiftR_le_shift (R := R) h]

/-- An event at real time `a` happens by virtual time `vtimeR R t` iff `a ≤ t`. -/
theorem vtime_le_vtimeR_iff {a t : ℝ} : vtime R a ≤ vtimeR R t ↔ a ≤ t := by
  constructor
  · intro h
    by_contra hlt
    exact absurd h (not_le.2 (vtimeR_lt_vtime (not_le.1 hlt)))
  · intro h
    exact (vtime_le_vtimeR a).trans (vtimeR_mono h)

/-- The ramp of `r` starts after the virtual time of its deadline. -/
theorem vtime_deadline_le {r : DeadlineRequest Page} :
    vtime R r.deadline ≤ vtime R r.arrival + start R r := by
  have had := r.arrival_le_deadline
  -- `shift d = shift a + (gaps in [a, d))`, split by arrival before or after `a`.
  have h1 := fsum_split (R := R) (fun r' => decide (r'.deadline < r.deadline))
    (fun r' => decide (r'.deadline < r.arrival))
  have h2 : fsum R (fun r' => decide (r'.deadline < r.deadline) && decide (r'.deadline < r.arrival)) =
      shift R r.arrival := by
    unfold shift
    apply fsum_congr
    intro r' _
    by_cases h : r'.deadline < r.arrival
    · simp [h, h.trans_le had]
    · simp [h]
  have h3 := fsum_split (R := R)
    (fun r' => decide (r'.deadline < r.deadline) && !decide (r'.deadline < r.arrival))
    (fun r' => decide (r'.arrival ≤ r.arrival))
  have h4 : fsum R (fun r' => (decide (r'.deadline < r.deadline) &&
      !decide (r'.deadline < r.arrival)) && decide (r'.arrival ≤ r.arrival)) ≤ known R r := by
    apply fsum_mono
    intro r' _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_lt] at h ⊢
    exact ⟨h.2, h.1.2, h.1.1⟩
  have h5 : fsum R (fun r' => (decide (r'.deadline < r.deadline) &&
      !decide (r'.deadline < r.arrival)) && !decide (r'.arrival ≤ r.arrival)) ≤
      fsum R (fun r' => decide (r.arrival < r'.arrival)) := by
    apply fsum_mono
    intro r' _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_le] at h ⊢
    exact h.2
  have h6 := fsum_after_le (R := R) r.arrival
  unfold vtime start
  unfold shift at h2 ⊢
  unfold eps
  linarith

/-- The ramp of `r` ends within the gaps at its deadline. -/
theorem rampEnd_le {r : DeadlineRequest Page} (hr : r ∈ R) : rampEnd R r ≤ vtimeR R r.deadline := by
  have had := r.arrival_le_deadline
  have h1 := fsum_split (R := R) (fun r' => decide (r'.deadline ≤ r.deadline))
    (fun r' => decide (r'.deadline < r.arrival))
  have h2 : fsum R (fun r' => decide (r'.deadline ≤ r.deadline) && decide (r'.deadline < r.arrival)) =
      shift R r.arrival := by
    unfold shift
    apply fsum_congr
    intro r' _
    by_cases h : r'.deadline < r.arrival
    · simp [h, h.le.trans had]
    · simp [h]
  have h3 := fsum_split (R := R)
    (fun r' => decide (r'.deadline ≤ r.deadline) && !decide (r'.deadline < r.arrival))
    (fun r' => decide (r'.deadline < r.deadline))
  have h4 : known R r ≤ fsum R (fun r' => (decide (r'.deadline ≤ r.deadline) &&
      !decide (r'.deadline < r.arrival)) && decide (r'.deadline < r.deadline)) := by
    apply fsum_mono
    intro r' _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_lt] at h ⊢
    exact ⟨⟨h.2.2.le, h.2.1⟩, h.2.2⟩
  have h5 : eps R r ≤ fsum R (fun r' => (decide (r'.deadline ≤ r.deadline) &&
      !decide (r'.deadline < r.arrival)) && !decide (r'.deadline < r.deadline)) := by
    apply eps_le_fsum hr
    simp [had]
  unfold rampEnd vtime vtimeR start
  unfold shift at h2 ⊢
  unfold shiftR
  linarith

theorem shift_eq_shiftR_of_gap {t t' : ℝ} (htt' : t < t')
    (hgap : ∀ r ∈ R, t < r.deadline → t' ≤ r.deadline) : shift R t' = shiftR R t := by
  unfold shift shiftR
  apply fsum_congr
  intro r hr
  by_cases h : r.deadline ≤ t
  · simp [h, h.trans_lt htt']
  · have := hgap r hr (not_le.1 h)
    simp [h, this]

/-- `realTime R` is the lower adjoint of `vtimeR R`. -/
theorem gc (R : List (DeadlineRequest Page)) : GaloisConnection (realTime R) (vtimeR R) := by
  intro v t
  have hbdd : BddAbove {t | vtime R t ≤ v} :=
    ⟨v, fun t' ht' => le_trans (le_add_of_nonneg_right (shift_nonneg t')) ht'⟩
  have hne : ({t | vtime R t ≤ v} : Set ℝ).Nonempty := by
    refine ⟨v - fsum R (fun _ => true), ?_⟩
    show vtime R _ ≤ v
    unfold vtime
    linarith [shift_le_total (R := R) (v - fsum R (fun _ => true))]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨t', ht', ht'δ, hgap⟩ :=
      exists_gap (R.map DeadlineRequest.deadline) t (v - vtimeR R t) (by linarith)
    have hs : shift R t' = shiftR R t :=
      shift_eq_shiftR_of_gap ht' fun r hr hd => hgap _ (List.mem_map_of_mem hr) hd
    have hmem : t' ∈ {t | vtime R t ≤ v} := by
      show t' + shift R t' ≤ v
      unfold vtimeR at ht'δ
      linarith
    have := le_csSup hbdd hmem
    unfold realTime at h
    linarith
  · intro h
    apply csSup_le hne
    intro t' ht'
    by_contra hlt
    have := vtimeR_lt_vtime (R := R) (not_le.1 hlt)
    have ht'' : vtime R t' ≤ v := ht'
    linarith

theorem realTime_mono : Monotone (realTime R) := (gc R).monotone_l

theorem realTime_le_iff {v t : ℝ} : realTime R v ≤ t ↔ v ≤ vtimeR R t := gc R v t

theorem le_realTime {a v : ℝ} (h : vtime R a ≤ v) : a ≤ realTime R v := by
  by_contra hlt
  have h1 : v ≤ vtimeR R (realTime R v) := realTime_le_iff.1 le_rfl
  have h2 := vtimeR_lt_vtime (R := R) (not_le.1 hlt)
  linarith

theorem start_nonneg (r : DeadlineRequest Page) : 0 ≤ start R r := by
  unfold start known
  have := r.arrival_le_deadline
  have := fsum_nonneg (R := R)
    (fun r' => decide (r'.arrival ≤ r.arrival ∧ r.arrival ≤ r'.deadline ∧ r'.deadline < r.deadline))
  have := eps_pos (R := R) r
  linarith

/-! ### Agreement with the requests arrived by `t` -/

section UpTo

variable {t : ℝ}


theorem count_upTo {x : ℝ} (hx : x ≤ t) : count (R.filter fun r => decide (r.arrival ≤ t)) x = count R x := by
  unfold count
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro r _
  by_cases h : r.arrival ≤ x
  · simp [h, h.trans hx]
  · simp [h]

theorem eps_upTo {r : DeadlineRequest Page} (hr : r.arrival ≤ t) : eps (R.filter fun r => decide (r.arrival ≤ t)) r = eps R r := by
  unfold eps; rw [count_upTo hr]

theorem fsum_upTo {p : DeadlineRequest Page → Bool} (h : ∀ r ∈ R, p r = true → r.arrival ≤ t) :
    fsum (R.filter fun r => decide (r.arrival ≤ t)) p = fsum R p := by
  unfold fsum
  rw [List.filter_filter]
  have : (R.filter fun r => p r && decide (r.arrival ≤ t)) = R.filter p :=
    List.filter_congr fun r hr => by cases hp : p r <;> simp [hp, h r hr]
  rw [this]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact eps_upTo (h r (List.mem_filter.1 hr).1 (List.mem_filter.1 hr).2)

theorem shift_upTo {x : ℝ} (hx : x ≤ t) : shift (R.filter fun r => decide (r.arrival ≤ t)) x = shift R x :=
  fsum_upTo fun r _ h => by
    simp only [decide_eq_true_eq] at h; linarith [r.arrival_le_deadline]

theorem shiftR_upTo {x : ℝ} (hx : x ≤ t) : shiftR (R.filter fun r => decide (r.arrival ≤ t)) x = shiftR R x :=
  fsum_upTo fun r _ h => by
    simp only [decide_eq_true_eq] at h; linarith [r.arrival_le_deadline]

theorem vtime_upTo {x : ℝ} (hx : x ≤ t) : vtime (R.filter fun r => decide (r.arrival ≤ t)) x = vtime R x := by
  unfold vtime; rw [shift_upTo hx]

theorem vtimeR_upTo {x : ℝ} (hx : x ≤ t) : vtimeR (R.filter fun r => decide (r.arrival ≤ t)) x = vtimeR R x := by
  unfold vtimeR; rw [shiftR_upTo hx]

theorem known_upTo {r : DeadlineRequest Page} (hr : r.arrival ≤ t) : known (R.filter fun r => decide (r.arrival ≤ t)) r = known R r :=
  fsum_upTo fun r' _ h => by
    simp only [decide_eq_true_eq] at h; linarith [h.1]

theorem start_upTo {r : DeadlineRequest Page} (hr : r.arrival ≤ t) : start (R.filter fun r => decide (r.arrival ≤ t)) r = start R r := by
  unfold start; rw [known_upTo hr, eps_upTo hr]

theorem rampEnd_upTo {r : DeadlineRequest Page} (hr : r.arrival ≤ t) :
    rampEnd (R.filter fun r => decide (r.arrival ≤ t)) r = rampEnd R r := by
  unfold rampEnd; rw [vtime_upTo hr, start_upTo hr, eps_upTo hr]

theorem realTime_upTo {v : ℝ} (hv : v ≤ vtimeR R t) : realTime (R.filter fun r => decide (r.arrival ≤ t)) v = realTime R v := by
  have key : ∀ s, realTime (R.filter fun r => decide (r.arrival ≤ t)) v ≤ s ↔ realTime R v ≤ s := by
    intro s
    rw [realTime_le_iff, realTime_le_iff]
    rcases le_or_gt s t with hs | hs
    · rw [vtimeR_upTo hs]
    · have h1 : v ≤ vtimeR R s := hv.trans (vtimeR_mono hs.le)
      have h2 : v ≤ vtimeR (R.filter fun r => decide (r.arrival ≤ t)) s := by
        have := vtimeR_mono (R := (R.filter fun r => decide (r.arrival ≤ t))) hs.le
        rw [vtimeR_upTo le_rfl] at this
        exact hv.trans this
      exact ⟨fun _ => h1, fun _ => h2⟩
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

end UpTo

end VirtualTime

/-! ## The virtual instance -/

section Instance

variable [Fintype Page]

theorem totalWeight_pos (I : DeadlineInstance Page) : 0 < I.totalWeight := by
  have : Nonempty Page := Fintype.card_pos_iff.1 (lt_of_le_of_lt (Nat.zero_le _) I.cacheSize_lt)
  exact Finset.sum_pos (fun p _ => I.weight_pos p) Finset.univ_nonempty

/-- The slope of the ramp. -/
noncomputable def slope (I : DeadlineInstance Page) (r : DeadlineRequest Page) : ℝ :=
  4 * I.totalWeight / eps I.requests r

theorem slope_pos (I : DeadlineInstance Page) (r : DeadlineRequest Page) : 0 < slope I r :=
  div_pos (by linarith [totalWeight_pos I]) (eps_pos r)

/-- The virtual delay request of `r`. -/
noncomputable def virtualRequest (I : DeadlineInstance Page) (r : DeadlineRequest Page) :
    Request Page where
  page := r.page
  arrival := vtime I.requests r.arrival
  delay x := slope I r * max 0 (x - start I.requests r)
  delay_mono x y hxy :=
    mul_le_mul_of_nonneg_left (max_le_max le_rfl (by linarith)) (slope_pos I r).le
  delay_continuous := by fun_prop
  delay_zero := by
    rw [max_eq_left (by linarith [start_nonneg (R := I.requests) r]), mul_zero]
  delay_unbounded M := by
    refine ⟨start I.requests r + max M 0 / slope I r, ?_⟩
    have hs := slope_pos I r
    rw [add_sub_cancel_left, max_eq_right (div_nonneg (le_max_right _ _) hs.le),
      mul_div_cancel₀ _ hs.ne']
    exact le_max_left _ _

/-- The virtual delay instance. -/
noncomputable def virtualInstance (I : DeadlineInstance Page) : Instance Page where
  weight := I.weight
  weight_pos := I.weight_pos
  cacheSize := I.cacheSize
  cacheSize_pos := I.cacheSize_pos
  cacheSize_lt := I.cacheSize_lt
  initialCache := I.initialCache
  initialCache_card := I.initialCache_card
  requests := I.requests.map (virtualRequest I)

theorem virtualRequest_delay_rampEnd (I : DeadlineInstance Page) (r : DeadlineRequest Page) :
    (virtualRequest I r).delay (rampEnd I.requests r - (virtualRequest I r).arrival) =
      2 * I.totalWeight := by
  show slope I r * max 0 (rampEnd I.requests r - vtime I.requests r.arrival - start I.requests r) = _
  have he := eps_pos (R := I.requests) r
  have : rampEnd I.requests r - vtime I.requests r.arrival - start I.requests r =
      eps I.requests r / 2 := by unfold rampEnd; ring
  rw [this, max_eq_right (by linarith), slope]
  field_simp
  ring

theorem virtualRequest_delay_nonneg (I : DeadlineInstance Page) (r : DeadlineRequest Page)
    (x : ℝ) : 0 ≤ (virtualRequest I r).delay x :=
  mul_nonneg (slope_pos I r).le (le_max_left _ _)

theorem virtualRequest_delay_eq_zero (I : DeadlineInstance Page) (r : DeadlineRequest Page)
    {x : ℝ} (hx : x ≤ start I.requests r) : (virtualRequest I r).delay x = 0 := by
  show slope I r * max 0 (x - start I.requests r) = 0
  rw [max_eq_left (by linarith), mul_zero]

theorem request_ext {ρ ρ' : Request Page} (h1 : ρ.page = ρ'.page) (h2 : ρ.arrival = ρ'.arrival)
    (h3 : ρ.delay = ρ'.delay) : ρ = ρ' := by
  cases ρ; cases ρ'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem upTo_requests (I : DeadlineInstance Page) (t : ℝ) :
    (I.upTo t).requests = I.requests.filter fun r => decide (r.arrival ≤ t) := rfl

theorem virtualRequest_upTo (I : DeadlineInstance Page) {t : ℝ} {r : DeadlineRequest Page}
    (hr : r.arrival ≤ t) : virtualRequest (I.upTo t) r = virtualRequest I r := by
  apply request_ext
  · rfl
  · show vtime (I.upTo t).requests r.arrival = vtime I.requests r.arrival
    rw [upTo_requests, vtime_upTo hr]
  · show (fun x => slope (I.upTo t) r * max 0 (x - start (I.upTo t).requests r)) =
      fun x => slope I r * max 0 (x - start I.requests r)
    have h1 : slope (I.upTo t) r = slope I r := by
      unfold slope; rw [upTo_requests, eps_upTo hr]; rfl
    rw [h1, upTo_requests, start_upTo hr]

/-- The virtual instance is online. -/
theorem virtualInstance_upTo (I : DeadlineInstance Page) (t : ℝ) :
    (virtualInstance I).upTo (vtimeR (I.upTo t).requests t) = virtualInstance (I.upTo t) := by
  have hv : vtimeR (I.upTo t).requests t = vtimeR I.requests t := by
    rw [upTo_requests, vtimeR_upTo le_rfl]
  rw [hv]
  unfold Instance.upTo virtualInstance
  congr 1
  rw [List.filter_map, upTo_requests]
  have : (I.requests.filter ((fun ρ : Request Page => decide (ρ.arrival ≤ vtimeR I.requests t)) ∘
      virtualRequest I)) = I.requests.filter fun r => decide (r.arrival ≤ t) := by
    apply List.filter_congr
    intro r _
    simp only [Function.comp, virtualRequest]
    exact decide_eq_decide.2 vtime_le_vtimeR_iff
  rw [this]
  apply List.map_congr_left
  intro r hr
  exact (virtualRequest_upTo I (by simpa using (List.mem_filter.1 hr).2)).symm

end Instance

end Deadlines

end PagingWithDelay
