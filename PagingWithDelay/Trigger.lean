import PagingWithDelay.Basic
import PagingWithDelay.Critical.Curve

/-!
# The trigger: delays, overshoots, trigger times, and claims

* `pageDelay pending p` and the overshoots are continuous in `t` when the delay functions of the pending requests are. Hence a page critical at `t` satisfies the closed form `Triggered` of the trigger at `t`: `delay_p(t) ≥ c_p + w_p` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)|/L`. The analysis only uses `Triggered`.
* Some page is critical at the infimum of `triggerTimes s` (finitely many pages), so an advance is followed by a critical service; if no page is critical now, the infimum is strictly later.
* A pending request with an unbounded monotone delay function makes `triggerTimes s` nonempty.
* Facts about `triggerPage`.
* The claims update `claimUpdate`: only the pages `q` with `w_q ≤ w_p` change, each `c_q` by the same fraction `θ ≤ 1` of `o_q`; the total increase is `min (|λ_p(x)|/L) (∑_{q : w_q ≤ w_p} o_q)`, which is `|λ_p(x)|/L` when `p` satisfies `Triggered`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (serviceEnd)

noncomputable section

variable {input : Instance Page}

/-! ### Page delays -/

@[simp] theorem pageDelay_nil (p : Page) (t : ℝ) :
    pageDelay ([] : List (Request Page)) p t = 0 := by
  simp [pageDelay]

theorem continuous_pageDelay {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (p : Page) :
    Continuous (pageDelay pending p) := by
  unfold pageDelay
  refine continuous_list_sum (f := fun (ρ : Request Page) (t : ℝ) => ρ.delay (t - ρ.arrival)) _ ?_
  intro ρ hρ
  exact (hc ρ (List.mem_filter.mp hρ).1).comp (continuous_id.sub continuous_const)

theorem continuous_overshoot {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (p : Page) :
    Continuous (overshoot input pending claims p) := by
  unfold overshoot
  exact continuous_const.max
    (((continuous_pageDelay hc p).sub continuous_const).sub continuous_const)

theorem continuous_sum_overshoot {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (S : Finset Page) :
    Continuous (fun t => ∑ q ∈ S, overshoot input pending claims q t) :=
  continuous_finset_sum _ fun q _ => continuous_overshoot hc claims q

theorem overshoot_nonneg (pending : List (Request Page)) (claims : Page → ℝ) (p : Page)
    (t : ℝ) : 0 ≤ overshoot input pending claims p t :=
  le_max_left _ _

theorem overshoot_pos_iff {pending : List (Request Page)} {claims : Page → ℝ} {p : Page}
    {t : ℝ} :
    0 < overshoot input pending claims p t ↔ claims p + w p < pageDelay pending p t := by
  unfold overshoot
  constructor
  · intro h
    rcases le_total 0 (pageDelay pending p t - claims p - w p) with h1 | h1
    · rw [max_eq_right h1] at h; linarith
    · rw [max_eq_left h1] at h; exact absurd h (lt_irrefl 0)
  · intro h
    exact lt_max_of_lt_right (by linarith)

theorem le_overshoot (pending : List (Request Page)) (claims : Page → ℝ) (p : Page) (t : ℝ) :
    pageDelay pending p t - claims p - w p ≤ overshoot input pending claims p t :=
  le_max_right _ _

/-- A nonzero page delay needs a pending request on the page. -/
theorem exists_pending_of_pageDelay_ne {pending : List (Request Page)} {p : Page} {t : ℝ}
    (h : pageDelay pending p t ≠ 0) : ∃ ρ ∈ pending, ρ.page = p := by
  by_contra hno
  push_neg at hno
  apply h
  unfold pageDelay
  rw [List.filter_eq_nil_iff.mpr (by intro ρ hρ; simpa using hno ρ hρ)]
  simp

/-- The delay of one pending request on `p` is at most the page delay. -/
theorem delay_le_pageDelay {pending : List (Request Page)} {t : ℝ}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ pending, ρ.delay 0 = 0)
    (harr : ∀ ρ ∈ pending, ρ.arrival ≤ t) {ρ : Request Page} (hρ : ρ ∈ pending) :
    ρ.delay (t - ρ.arrival) ≤ pageDelay pending ρ.page t := by
  unfold pageDelay
  apply List.single_le_sum
  · intro v hv
    simp only [List.mem_map, List.mem_filter] at hv
    obtain ⟨π, ⟨hπ, -⟩, rfl⟩ := hv
    rw [← hzero π hπ]
    exact hmono π hπ (by linarith [harr π hπ])
  · exact List.mem_map.mpr ⟨ρ, List.mem_filter.mpr ⟨hρ, by simp⟩, rfl⟩

theorem pageDelay_mono {pending : List (Request Page)} (hmono : ∀ ρ ∈ pending, Monotone ρ.delay)
    (p : Page) : Monotone (pageDelay pending p) := by
  intro a b hab
  unfold pageDelay
  apply List.sum_le_sum
  intro ρ hρ
  exact hmono ρ (List.mem_filter.mp hρ).1 (by linarith)

/-- The page delay only depends on the pending requests on the page. -/
theorem pageDelay_filter_ne (pending : List (Request Page)) {p q : Page} (hpq : q ≠ p) (t : ℝ) :
    pageDelay (pending.filter fun π => decide (π.page ≠ p)) q t = pageDelay pending q t := by
  unfold pageDelay
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro ρ _
  by_cases h : ρ.page = q
  · subst h; simp [hpq]
  · simp [h]

/-! ### Triggering -/

variable (input) in
/-- The closed form of the trigger at `t`: `delay_p(t) ≥ c_p + w_p` and `∑_{q : w_q ≤ w_p} o_q(t) ≥ |λ_p(x)| / L`. It holds whenever `eq:trigger` holds (`triggered_of_triggerCond`) and, by continuity, whenever `p` is critical at `t` (`triggered_of_critical`). -/
def Triggered (x : Page → ℝ) (pending : List (Request Page)) (claims : Page → ℝ) (t : ℝ)
    (p : Page) : Prop :=
  claims p + w p ≤ pageDelay pending p t ∧
    serviceEnd input x p / L ≤
      ∑ q ∈ lighter input p, overshoot input pending claims q t

theorem triggered_iff {x : Page → ℝ} {pending : List (Request Page)} {claims : Page → ℝ}
    {t : ℝ} {p : Page} :
    Triggered input x pending claims t p ↔
      claims p + w p ≤ pageDelay pending p t ∧
        serviceEnd input x p / L ≤
          ∑ q ∈ lighter input p, overshoot input pending claims q t := Iff.rfl

theorem triggerCond_iff {x : Page → ℝ} {pending : List (Request Page)} {claims : Page → ℝ}
    {t : ℝ} {p : Page} :
    TriggerCond input x pending claims t p ↔
      claims p + w p < pageDelay pending p t ∧
        serviceEnd input x p / L ≤
          ∑ q ∈ lighter input p, overshoot input pending claims q t := by
  rw [TriggerCond, overshoot_pos_iff]

theorem triggered_of_triggerCond {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : TriggerCond input x pending claims t p) :
    Triggered input x pending claims t p :=
  ⟨(triggerCond_iff.mp h).1.le, h.2⟩

theorem mem_lighter {p q : Page} : q ∈ lighter input p ↔ w q ≤ w p := by
  simp [lighter]

theorem self_mem_lighter (p : Page) : p ∈ lighter input p := mem_lighter.mpr le_rfl

/-- A triggered page has a pending request (claims are nonnegative and weights positive). -/
theorem exists_pending_of_triggered {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : Triggered input x pending claims t p)
    (hc : 0 ≤ claims p) (hw : 0 < w p) : ∃ ρ ∈ pending, ρ.page = p := by
  apply exists_pending_of_pageDelay_ne (t := t)
  have := h.1
  intro h0
  linarith

/-- A critical page has a pending request: `eq:trigger` holds at some time, so its page delay is positive. -/
theorem exists_pending_of_critical {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} {t : ℝ} {p : Page} (h : Critical input x pending claims t p)
    (hc : 0 ≤ claims p) (hw : 0 < w p) : ∃ ρ ∈ pending, ρ.page = p := by
  obtain ⟨τ, -, -, hτ⟩ := h 1 one_pos
  exact exists_pending_of_triggered (triggered_of_triggerCond hτ) hc hw

theorem isClosed_triggered {x : Page → ℝ} {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) (claims : Page → ℝ) (p : Page) :
    IsClosed {t | Triggered input x pending claims t p} := by
  simp only [triggered_iff, Set.setOf_and]
  exact (isClosed_le continuous_const (continuous_pageDelay hc p)).inter
    (isClosed_le continuous_const (continuous_sum_overshoot hc claims _))

/-- A page that is critical at `t` satisfies the closed form of the trigger at `t`: `t` is a limit of times at which `eq:trigger` holds. -/
theorem triggered_of_critical {x : Page → ℝ} {pending : List (Request Page)}
    (hc : ∀ ρ ∈ pending, Continuous ρ.delay) {claims : Page → ℝ} {t : ℝ} {p : Page}
    (h : Critical input x pending claims t p) : Triggered input x pending claims t p := by
  have hsub : {τ | TriggerCond input x pending claims τ p} ⊆
      {τ | Triggered input x pending claims τ p} := fun τ hτ => triggered_of_triggerCond hτ
  have hcl : t ∈ closure {τ | TriggerCond input x pending claims τ p} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨τ, h1, h2, h3⟩ := h ε hε
    refine ⟨τ, h3, ?_⟩
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  exact closure_minimal hsub (isClosed_triggered hc claims p) hcl

theorem triggerTimes_bddBelow (s : Snap Page) : BddBelow (triggerTimes input s) :=
  ⟨s.now, fun _ ht => ht.1⟩

theorem now_le_sInf_triggerTimes {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    s.now ≤ sInf (triggerTimes input s) :=
  le_csInf hne fun _ ht => ht.1

theorem sInf_triggerTimes_le {s : Snap Page} {t : ℝ} (ht : t ∈ triggerTimes input s) :
    sInf (triggerTimes input s) ≤ t :=
  csInf_le (triggerTimes_bddBelow s) ht

/-- Some page is critical at the infimum of the trigger times: as there are finitely many pages, `eq:trigger` holds for one of them arbitrarily soon after the infimum. -/
theorem exists_critical_sInf {s : Snap Page} (hne : (triggerTimes input s).Nonempty) :
    ∃ p, Critical input s.x s.pending s.claims (sInf (triggerTimes input s)) p := by
  by_contra hno
  push_neg at hno
  have hno' : ∀ p, ∃ ε > 0, ∀ τ, sInf (triggerTimes input s) ≤ τ →
      τ < sInf (triggerTimes input s) + ε →
        ¬ TriggerCond input s.x s.pending s.claims τ p := by
    intro p
    have := hno p
    unfold Critical at this
    push_neg at this
    exact this
  choose ε hε hε' using hno'
  obtain ⟨t0, -, p0, -⟩ := id hne
  set η := Finset.univ.inf' ⟨p0, Finset.mem_univ p0⟩ ε with hηdef
  have hη : 0 < η := (Finset.lt_inf'_iff _).2 fun p _ => hε p
  obtain ⟨t, htT, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (triggerTimes input s)) hη)
  obtain ⟨p, hp⟩ := htT.2
  have hle : η ≤ ε p := Finset.inf'_le ε (Finset.mem_univ p)
  exact hε' p t (sInf_triggerTimes_le htT) (by linarith) hp

theorem triggerPage_spec {s : Snap Page} {p : Page} (h : triggerPage input s = some p) :
    Critical input s.x s.pending s.claims s.now p := by
  have := List.find?_some h
  simpa using this

/-- The page of the next critical service satisfies the closed form of the trigger now. -/
theorem triggerPage_triggered {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    {p : Page} (h : triggerPage input s = some p) :
    Triggered input s.x s.pending s.claims s.now p :=
  triggered_of_critical hc (triggerPage_spec h)

theorem triggerPage_eq_none_iff {s : Snap Page} :
    triggerPage input s = none ↔ ∀ p, ¬ Critical input s.x s.pending s.claims s.now p := by
  unfold triggerPage
  rw [List.find?_eq_none]
  constructor
  · intro h p hp
    exact h p (by simp) (by simpa using hp)
  · intro h p _ hp
    exact h p (by simpa using hp)

theorem triggerPage_eq_some_of_critical {s : Snap Page} {p : Page}
    (h : Critical input s.x s.pending s.claims s.now p) : ∃ q, triggerPage input s = some q := by
  cases hq : triggerPage input s with
  | none => exact absurd h (triggerPage_eq_none_iff.mp hq p)
  | some q => exact ⟨q, rfl⟩

/-- Without a page critical now, the infimum of the trigger times is strictly later. -/
theorem now_lt_sInf_triggerTimes {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    (hne : (triggerTimes input s).Nonempty) (hnone : triggerPage input s = none) :
    s.now < sInf (triggerTimes input s) := by
  rcases eq_or_lt_of_le (now_le_sInf_triggerTimes hne) with h | h
  · obtain ⟨p, hp⟩ := exists_critical_sInf hne
    rw [← h] at hp
    exact absurd hp (triggerPage_eq_none_iff.mp hnone p)
  · exact h

/-- After advancing to the infimum of the trigger times, some page is critical. -/
theorem triggerPage_advance {s : Snap Page} (hc : ∀ ρ ∈ s.pending, Continuous ρ.delay)
    (hne : (triggerTimes input s).Nonempty) :
    ∃ p, triggerPage input { s with now := sInf (triggerTimes input s) } = some p := by
  obtain ⟨p, hp⟩ := exists_critical_sInf hne
  exact triggerPage_eq_some_of_critical (s := { s with now := sInf (triggerTimes input s) }) hp

/-- A pending request with an unbounded monotone delay function eventually makes `eq:trigger` hold for its page. -/
theorem triggerTimes_nonempty {s : Snap Page}
    (hmono : ∀ ρ ∈ s.pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ s.pending, ρ.delay 0 = 0)
    (hunb : ∀ ρ ∈ s.pending, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ)
    (harr : ∀ ρ ∈ s.pending, ρ.arrival ≤ s.now) {ρ : Request Page} (hρ : ρ ∈ s.pending) :
    (triggerTimes input s).Nonempty := by
  set p := ρ.page
  set thr := serviceEnd input s.x p / L
  obtain ⟨τ, hτ⟩ := hunb ρ hρ (s.claims p + w p + |thr| + 1)
  set t := max s.now (ρ.arrival + τ)
  have harr' : ∀ π ∈ s.pending, π.arrival ≤ t := fun π hπ => (harr π hπ).trans (le_max_left _ _)
  have h1 : ρ.delay τ ≤ ρ.delay (t - ρ.arrival) :=
    hmono ρ hρ (by have := le_max_right s.now (ρ.arrival + τ); linarith)
  have h2 := delay_le_pageDelay hmono hzero harr' hρ
  refine ⟨t, le_max_left _ _, p, triggerCond_iff.mpr ⟨?_, ?_⟩⟩
  · linarith [abs_nonneg thr]
  · calc thr ≤ |thr| := le_abs_self _
      _ ≤ pageDelay s.pending p t - s.claims p - w p := by linarith
      _ ≤ overshoot input s.pending s.claims p t := le_overshoot _ _ _ _
      _ ≤ _ := Finset.single_le_sum (f := fun q => overshoot input s.pending s.claims q t)
          (fun q _ => overshoot_nonneg _ _ _ _) (self_mem_lighter (input := input) p)

/-- The same, for the pending requests of a valid instance. -/
theorem triggerTimes_nonempty_of_valid (hv : input.Valid) {s : Snap Page}
    (hreq : ∀ ρ ∈ s.pending, ρ ∈ input.requests) (harr : ∀ ρ ∈ s.pending, ρ.arrival ≤ s.now)
    {ρ : Request Page} (hρ : ρ ∈ s.pending) : (triggerTimes input s).Nonempty :=
  triggerTimes_nonempty (fun π hπ => hv.delay_mono π (hreq π hπ))
    (fun π hπ => hv.delay_zero π (hreq π hπ)) (fun π hπ => hv.delay_unbounded π (hreq π hπ))
    harr hρ

/-- If `eq:trigger` does not hold for page `p` at any time in `[a, t)` (with `a < t`) and `p` has positive overshoot at `t`, then at `t` the overshoots of the lighter pages are at most `|λ_p(x)|/L`. -/
theorem sum_overshoot_le_of_not_triggered {x : Page → ℝ} {pending : List (Request Page)}
    {claims : Page → ℝ} (hc : ∀ ρ ∈ pending, Continuous ρ.delay) {a t : ℝ} (hat : a < t)
    {p : Page} (hno : ∀ τ, a ≤ τ → τ < t → ¬ TriggerCond input x pending claims τ p)
    (hpos : claims p + w p < pageDelay pending p t) :
    ∑ q ∈ lighter input p, overshoot input pending claims q t ≤
      serviceEnd input x p / L := by
  by_contra hlt
  push_neg at hlt
  set U := {τ | claims p + w p < pageDelay pending p τ} ∩
    {τ | serviceEnd input x p / L <
      ∑ q ∈ lighter input p, overshoot input pending claims q τ}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (continuous_pageDelay hc p)).inter
      (isOpen_lt continuous_const (continuous_sum_overshoot hc claims _))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t ⟨hpos, hlt⟩
  set τ := max a (t - ε / 2)
  have hτ1 : a ≤ τ := le_max_left _ _
  have hτ2 : τ < t := max_lt hat (by linarith)
  have hτ3 : τ ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    have := le_max_right a (t - ε / 2)
    linarith
  have hτU := hball hτ3
  exact hno τ hτ1 hτ2 (triggerCond_iff.mpr ⟨hτU.1, hτU.2.le⟩)

/-! ### Claims -/

/-! ### The claims of a critical service -/

theorem serviceEnd_nonneg' (x : Page → ℝ) (p : Page) : 0 ≤ serviceEnd input x p :=
  Real.sInf_nonneg fun _ hs => hs.1

theorem claimRem_nonneg (hv : input.Valid) (x : Page → ℝ) (p : Page) :
    0 ≤ serviceEnd input x p / L :=
  div_nonneg (serviceEnd_nonneg' x p) (Instance.L_pos hv).le

theorem claimFraction_nonneg (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    0 ≤ claimFraction input x pending claims t p :=
  le_min zero_le_one (div_nonneg (claimRem_nonneg hv x p)
    (Finset.sum_nonneg fun q _ => overshoot_nonneg _ _ _ _))

theorem claimFraction_le_one (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    claimFraction input x pending claims t p ≤ 1 :=
  min_le_left _ _

theorem le_claimUpdate (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p q : Page) :
    claims q ≤ claimUpdate input x pending claims t p q := by
  unfold claimUpdate
  split_ifs
  · nlinarith [claimFraction_nonneg hv x pending claims t p, overshoot_nonneg (input := input) pending claims q t]
  · exact le_rfl

theorem claimUpdate_le (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p q : Page) :
    claimUpdate input x pending claims t p q ≤ claims q + overshoot input pending claims q t := by
  unfold claimUpdate
  split_ifs
  · nlinarith [claimFraction_le_one (input := input) x pending claims t p,
      overshoot_nonneg (input := input) pending claims q t]
  · linarith [overshoot_nonneg (input := input) pending claims q t]

/-- Only the pages `q` with `w_q ≤ w_p` give claims. -/
theorem claimUpdate_of_not_lighter (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) {p q : Page} (hq : q ∉ lighter input p) :
    claimUpdate input x pending claims t p q = claims q :=
  if_neg hq

/-- The total claim of a critical service on `p`: `min (|λ_p(x)|/L) (∑_{q : w_q ≤ w_p} o_q)`. -/
theorem sum_claimUpdate (hv : input.Valid) (x : Page → ℝ) (pending : List (Request Page))
    (claims : Page → ℝ) (t : ℝ) (p : Page) :
    ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      min (serviceEnd input x p / L)
        (∑ q ∈ lighter input p, overshoot input pending claims q t) := by
  set S := ∑ q ∈ lighter input p, overshoot input pending claims q t
  have hS : 0 ≤ S := Finset.sum_nonneg fun q _ => overshoot_nonneg _ _ _ _
  have hsum : ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      claimFraction input x pending claims t p * S := by
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ (lighter input p))
      (fun q _ hq => by rw [claimUpdate_of_not_lighter x pending claims t hq, sub_self])]
    exact Finset.sum_congr rfl fun q hq => by simp [claimUpdate, hq]
  rw [hsum]
  rcases hS.eq_or_lt with h | h
  · rw [← h, mul_zero, min_eq_right (claimRem_nonneg hv x p)]
  · unfold claimFraction
    rw [min_mul_of_nonneg _ _ hS, one_mul, div_mul_cancel₀ _ h.ne', min_comm]

/-- When `p` triggers, the claims of the critical service total exactly `|λ_p(x)|/L`. -/
theorem sum_claimUpdate_of_triggered (hv : input.Valid) {x : Page → ℝ}
    {pending : List (Request Page)} {claims : Page → ℝ} {t : ℝ} {p : Page}
    (h : Triggered input x pending claims t p) :
    ∑ q, (claimUpdate input x pending claims t p q - claims q) =
      serviceEnd input x p / L := by
  rw [sum_claimUpdate hv, min_eq_left h.2]

end

end PMD

end PagingWithDelay
