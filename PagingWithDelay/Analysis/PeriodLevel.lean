import PagingWithDelay.Analysis.Money
import PagingWithDelay.Analysis.Pending

/-!
# The early part, one period and one level (`lem:early`, `lem:periodlevel`)

Fix a step time `τ` of the comparator (the start `t_j` of period `j`) and a level `e` whose weight `W = 2^e` is below every weight in the comparator's cache `O_j`. The *light services* `λ^(1), …, λ^(m)` are the overdue critical services of the period on pages of level `≤ e` (`lightServices`). The *early part* consists of the entries of the period before `λ^(m)`.

`lem:early` (`early_spec`): at `λ^(m)` (time `t_m`) some page `q` with `w_q ≤ w_{p_m} ≤ W` is overdue, so the comparator has served some pending request `r` on `q` by `t_m`. As `q` is not cached in the period, `r` was served by `τ`, so `a_r ≤ τ` and `r` is pending at every level-`e` preemptive service of the early part. Hence these never run out of candidates and stop for lack of budget (`B_W < W`). The pending requests on `q` have delay `> w_q` at `t_m`, so the deadline of `q`, and thus of every page chosen for a round trip, is at most `t_m`. A round trip on `p` is then chargeable: either the comparator has served a pending request on `p` (so `p` is not cached), or it has served none by `t_m` and pays at least their delay at `t_m`, which is at least `w_p`.

`lem:periodlevel` (`periodLevel_sum`): the deposits `|λ^(ℓ)|_W` of the light services of one period and one level are at most `4W + (3/2) C_{j,W} + L W`, where `C_{j,W}` is the total weight of the chargeable level-`e` round trips of the period.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

namespace ExcessProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  hole holePayment preemptCondition tripCost afterLevel Stage IsRest IsFrac levelWeight_pos
  minLevel_le)
open PagingWithDelay.Schedule (cacheAt ServedBy stepTimes)
open PagingWithDelay.Schedule (InPer)

open Classical

noncomputable section

/-! ### Definitions -/

variable (input : Instance Page)

/-- The length `|λ|_W` in level `e` of the critical service at entry `i` (else `0`). -/
def levelLenAt (i : ℕ) (e : ℤ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .critical p => levelLen input (snapAt input i).x p e
    | _ => 0
  else 0

/-- Entry `i` is a critical service on a page of level `≤ e`. -/
def IsLightService (e : ℤ) (i : ℕ) : Prop :=
  ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧ level input p ≤ e

variable (σ : Request Page → ℝ) (S : Schedule Page)

/-- The *light services* of the period of `τ` and the level `e`: the overdue critical services of the period on pages of level `≤ e`. -/
def lightServices (τ : ℝ) (e : ℤ) : Finset ℕ :=
  (Finset.range (log input).length).filter
    (fun i => IsLightService input e i ∧ IsOverdue input σ S i ∧ InPer S τ (entryTime input i))

/-- The level-`e` round trips of the period of `τ`. -/
def periodTrips (τ : ℝ) (e : ℤ) : Finset ℕ :=
  (Finset.range (log input).length).filter
    (fun l => (∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) ∧
      InPer S τ (entryTime input l))

variable {input σ S}

/-! ### Small facts -/

theorem levelLenAt_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    levelLenAt input i e = levelLen input (snapAt input i).x p e := by
  unfold levelLenAt
  rw [dif_pos h, hm]

theorem levelLenAt_nonneg (i : ℕ) (e : ℤ) : 0 ≤ levelLenAt input i e := by
  unfold levelLenAt
  split_ifs with h
  · split
    · exact C.levelLen_nonneg _ _ _
    · exact le_rfl
  · exact le_rfl

theorem levelLenAt_le (i : ℕ) (e : ℤ) : levelLenAt input i e ≤ L * levelWeight e := by
  have hL := L_nonneg' input
  have hW := levelWeight_pos e
  unfold levelLenAt
  split_ifs with h
  · split
    · exact levelLen_le _ _ _
    · positivity
  · positivity

theorem visitPage_of_trip {l : ℕ} (h : l < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt l h = .trip e π) : visitPage input l = some π.page := by
  unfold visitPage
  rw [dif_pos h, hm]

theorem chargeW_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ chargeW input σ S l := by
  unfold chargeW
  split_ifs
  · split
    · exact (hv.weight_pos _).le
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_nonneg (hv : input.Valid) (l : ℕ) : 0 ≤ tripChargeW input σ S l := by
  unfold tripChargeW
  split_ifs with h
  · split
    · exact chargeW_nonneg hv l
    · exact le_rfl
  · exact le_rfl

theorem tripChargeW_of_chargeable {l : ℕ} (h : l < (log input).length) {e : ℤ}
    {π : Request Page} (hm : moveAt l h = .trip e π) (hc : IsChargeable input σ S l) :
    tripChargeW input σ S l = w π.page := by
  unfold tripChargeW chargeW
  rw [dif_pos h, hm]
  simp only
  rw [if_pos hc, visitPage_of_trip h hm]

theorem tripWL_eq_zero {l : ℕ} {e : ℤ}
    (hno : ¬ ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π) :
    tripWL input e l = 0 := by
  unfold tripWL
  split_ifs with h
  · generalize hmv : moveAt l h = m
    cases m with
    | trip e' π =>
      simp only
      split_ifs with he
      · subst he; exact absurd ⟨h, π, hmv⟩ hno
      · rfl
    | _ => rfl
  · rfl

theorem tripWL_of_trip {l : ℕ} (h : l < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt l h = .trip e π) : tripWL input e l = w π.page := by
  unfold tripWL
  rw [dif_pos h, hm]
  simp

theorem servedBy_mono {ρ : Request Page} {t t' : ℝ} (htt' : t ≤ t')
    (h : ServedBy input σ S ρ t) :
    ServedBy input σ S ρ t' := by
  obtain ⟨s, h1, h2, h3, h4⟩ := h
  exact ⟨s, h1, h2, h3.trans htt', h4⟩

/-- An overdue page has a pending request that the comparator has served. -/
theorem exists_served_of_overdue (hv : input.Valid) {s : Snap Page} {q : Page} {t : ℝ}
    (h : PageOverdue input σ S s q t) :
    ∃ r ∈ s.pending, r.page = q ∧ ServedBy input σ S r t := by
  by_contra hcon
  push_neg at hcon
  have hnil : (s.pending.filter fun ρ => decide (ρ.page = q ∧
      ServedBy input σ S ρ t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp only [decide_eq_true_eq, not_and]
    exact hcon r hr
  unfold PageOverdue servedDelay at h
  rw [hnil] at h
  simp at h
  linarith [hv.weight_pos q]

/-! ### Deadlines of pages -/

theorem pageDeadline_le {pending : List (Request Page)} {t T : ℝ} {p : Page} (htT : t ≤ T)
    (h : w p < pageDelay pending p T) : pageDeadline input pending t p ≤ T :=
  csInf_le ⟨t, fun x hx => hx.1⟩ ⟨htT, h⟩

/-- If the deadline of `p` is at most `T`, the delay of the pending requests on `p` at `T` is at least `w_p` (the delays are continuous). -/
theorem weight_le_pageDelay {pending : List (Request Page)} {t T : ℝ} {p : Page}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hcont : ∀ ρ ∈ pending, Continuous ρ.delay)
    (hne : ∃ x, t ≤ x ∧ w p < pageDelay pending p x)
    (h : pageDeadline input pending t p ≤ T) : w p ≤ pageDelay pending p T := by
  set A := {x | t ≤ x ∧ w p < pageDelay pending p x} with hA
  have hB : IsClosed {x | w p ≤ pageDelay pending p x} :=
    isClosed_le continuous_const (continuous_pageDelay hcont p)
  have hAB : A ⊆ {x | w p ≤ pageDelay pending p x} := fun x hx => hx.2.le
  have hmem := closure_minimal hAB hB (csInf_mem_closure hne ⟨t, fun x hx => hx.1⟩)
  exact hmem.trans (pageDelay_mono hmono p h)

/-- A page with a pending request has a deadline: the delay of its pending requests eventually exceeds `w_p`. -/
theorem exists_pageDelay_gt {pending : List (Request Page)} {t : ℝ} {p : Page}
    (hmono : ∀ ρ ∈ pending, Monotone ρ.delay) (hzero : ∀ ρ ∈ pending, ρ.delay 0 = 0)
    (hunb : ∀ ρ ∈ pending, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ)
    (harr : ∀ ρ ∈ pending, ρ.arrival ≤ t) {π : Request Page} (hπ : π ∈ pending)
    (hπp : π.page = p) : ∃ x, t ≤ x ∧ w p < pageDelay pending p x := by
  obtain ⟨τ₀, hτ₀⟩ := hunb π hπ (w p + 1)
  refine ⟨max t (τ₀ + π.arrival), le_max_left _ _, ?_⟩
  have h1 := delay_le_pageDelay hmono hzero
    (fun ρ hρ => (harr ρ hρ).trans (le_max_left t (τ₀ + π.arrival))) hπ
  rw [hπp] at h1
  have h2 : π.delay τ₀ ≤ π.delay (max t (τ₀ + π.arrival) - π.arrival) :=
    hmono π hπ (by linarith [le_max_right t (τ₀ + π.arrival)])
  linarith

/-! ### The pending list shrinks, apart from new arrivals -/

section Pending

variable (hv : input.Valid)
include hv

/-- One move: the pending requests satisfying `P` (which have arrived by `T`) form a sublist of the earlier ones, unless the move is a tick at a time `≤ T`. -/
theorem pending_filter_sublist_succ {m : ℕ} (T : ℝ) (P : Request Page → Bool)
    (hP : ∀ ρ, P ρ = true → ρ.arrival ≤ T)
    (htick : ∀ (hm : m < (log input).length) t, moveAt m hm = .tick t → T < t) :
    ((snapAt input (m + 1)).pending.filter P).Sublist ((snapAt input m).pending.filter P) := by
  by_cases hm : m < (log input).length
  · generalize hmv : moveAt m hm = mv
    cases mv with
    | tick t =>
      obtain ⟨-, -, -, -, hs⟩ := tick_spec hv hm hmv
      rw [hs]
      simp only
      rw [List.filter_append, List.filter_append]
      have hnil : ((input.requests.filter fun ρ => decide (ρ.arrival = t)).filter
          (fun ρ => decide ((snapAt input m).x ρ.page ≠ δ))).filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro ρ hρ hPρ
        simp only [List.mem_filter, decide_eq_true_eq] at hρ
        have := hP ρ hPρ
        have := htick hm t hmv
        linarith [hρ.1.2]
      rw [hnil, List.append_nil]
      exact List.filter_sublist.filter P
    | critical p =>
      obtain ⟨-, -, hs⟩ := critical_spec hv hm hmv
      rw [hs]
      exact List.filter_sublist.filter P
    | trip e π =>
      obtain ⟨-, -, -, hs⟩ := trip_spec hv hm hmv
      rw [hs]
      exact List.filter_sublist.filter P
    | _ =>
      rw [pending_succ_of_not_visit hv hm (by intro p h; rw [hmv] at h; cases h)
        (by intro e π h; rw [hmv] at h; cases h) (by intro t h; rw [hmv] at h; cases h)]
  · rw [snapAt_of_ge (by omega), snapAt_of_ge (by omega)]

theorem pending_filter_sublist {l j : ℕ} (hlj : l ≤ j) (T : ℝ) (P : Request Page → Bool)
    (hP : ∀ ρ, P ρ = true → ρ.arrival ≤ T)
    (htick : ∀ m (hm : m < (log input).length), l ≤ m → m < j → ∀ t,
      moveAt m hm = .tick t → T < t) :
    ((snapAt input j).pending.filter P).Sublist ((snapAt input l).pending.filter P) := by
  induction j, hlj using Nat.le_induction with
  | base => exact List.Sublist.refl _
  | succ n hn ih =>
    exact (pending_filter_sublist_succ hv T P hP (fun hm t h => htick n hm hn (by omega) t h)).trans
      (ih (fun m hm h1 h2 t h => htick m hm h1 (by omega) t h))

/-- Ticks after entry `l > 0` happen after the time `(snapAt l).now`. -/
theorem lt_of_tick_after {l m : ℕ} (hl0 : 0 < l) (hlm : l ≤ m) (hm : m < (log input).length)
    {t : ℝ} (hmt : moveAt m hm = .tick t) : (snapAt input l).now < t := by
  have := entryTime_lt_of_tick hv hm hmt (j := l - 1) (by omega)
  unfold entryTime at this
  rwa [Nat.sub_add_cancel hl0] at this

end Pending

/-! ### `lem:early` -/

section Early

variable (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
  (hSw : Schedule.SwapForm input S)
  (hF : S.FeasibleBy input σ)
  {τ : ℝ} {e : ℤ}
  (hW : ∀ q ∈ cacheAt input S τ, levelWeight e < w q)

section Comparator

include hv hW in
theorem not_mem_cacheAt {p : Page} (hp : level input p ≤ e) :
    p ∉ cacheAt input S τ :=
  fun hmem => absurd (hW p hmem) (not_lt.2 ((level_le_iff' hv p e).1 hp))

include hSw in
/-- `obs:servedbefore`: a request on a page not cached in the period of `τ` that the comparator has served by a time `T` of the period was served by `τ`. -/
theorem servedBy_start {T : ℝ} (hper : InPer S τ T) {ρ : Request Page}
    (hp : ρ.page ∉ cacheAt input S τ)
    (hs : ServedBy input σ S ρ T) :
    ServedBy input σ S ρ τ := by
  have hc := hSw.chronological
  obtain ⟨s, h1, h2, h3, h4⟩ := hs
  by_cases hsτ : s ≤ τ
  · exact ⟨s, h1, h2, hsτ, h4⟩
  exfalso
  have hτs : τ < s := not_le.1 hsτ
  obtain ⟨st, hst, hstτ⟩ := Schedule.mem_stepTimes.1 hper.1
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hst
  rcases h4 with ⟨-, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
  · have := Schedule.head_le hc hh hi
    linarith
  · have hjτ : S[j].time ≤ τ := by
      by_contra hcon
      exact hper.2.2 _ (List.getElem_mem hj) ⟨not_le.1 hcon, ha.trans h3⟩
    apply hp
    rw [Schedule.cacheAt_eq_of_last hc hj hjτ
      (fun st hst => lt_of_lt_of_le hτs (hb st hst))]
    exact hpj

end Comparator

include hv hσ hSw hF hW

/-- `lem:early`: let `i'` be a light service of the period of `τ` and level `e`, and `l < i'` an entry of the period. If `l` is a level-`e` round trip, it is chargeable; if `l` closes a level-`e` hole, the preemptive service stopped for lack of budget, ending with `B_W < W`. -/
theorem early_spec {l i' : ℕ} (hl : l < (log input).length)
    (hper : InPer S τ (entryTime input l)) (hi' : i' ∈ lightServices input σ S τ e)
    (hli' : l < i') :
    (∀ π, moveAt l hl = .trip e π → IsChargeable input σ S l) ∧
    (∀ stop, moveAt l hl = .closeHole e stop →
      stop ≠ none ∧ (snapAt input (l + 1)).budget e < levelWeight e) := by
  have hvb := hv
  -- the light service `i'` and its overdue page `q`
  simp only [lightServices, Finset.mem_filter, Finset.mem_range] at hi'
  obtain ⟨-, ⟨h', p', hm', hle'⟩, ⟨h'', p'', hm'', q, hwq, hov⟩, hper'⟩ := hi'
  have hpp : p'' = p' := by
    have := hm''.symm.trans hm'
    cases this; rfl
  subst hpp
  have hlq : level input q ≤ e :=
    (level_le_iff' hv q e).2 (hwq.trans ((level_le_iff' hv p'' e).1 hle'))
  have hqc := not_mem_cacheAt hv hW hlq
  set t' := entryTime input i' with ht'
  have ht'now : t' = (snapAt input i').now := (critical_facts hv h' hm').2.2.2.2
  obtain ⟨r, hr, hrq, hrs⟩ := exists_served_of_overdue hv hov
  -- the requests on `q` served by `t'` were served by `τ`, so they arrived by `τ`
  have hservedτ : ∀ ρ : Request Page, ρ.page = q →
      ServedBy input σ S ρ t' → ρ.arrival ≤ τ := by
    intro ρ hρq hρs
    have hρc : ρ.page ∉ cacheAt input S τ := hρq ▸ hqc
    obtain ⟨s, h1, -, h3, -⟩ := servedBy_start hSw hper' hρc hρs
    exact h1.trans h3
  -- the facts at entry `l`, which is inside a level-`e` preemptive service
  have hcommon : ∀ b, (snapAt input l).stage = .preempt e b →
      0 < l ∧ entryTime input l = (snapAt input l).now ∧ r ∈ (snapAt input l).pending := by
    intro b hst
    have hl0 : 0 < l := by
      rcases Nat.eq_zero_or_pos l with rfl | h
      · rw [snapAt_zero hv] at hst; simp [initialSnap] at hst
      · exact h
    obtain ⟨-, hlt⟩ := entryTime_of_preempt hv hst
    refine ⟨hl0, hlt, ?_⟩
    have := pending_of_later hv (show l - 1 < i' by omega) hr
      ((hservedτ r hrq hrs).trans (by
        unfold entryTime; rw [Nat.sub_add_cancel hl0, ← hlt]; exact hper.2.1))
    rwa [Nat.sub_add_cancel hl0] at this
  have hrl : level input r.page ≤ e := hrq ▸ hlq
  constructor
  · intro π hm
    obtain ⟨⟨b, hst⟩, hcand, -, -⟩ := trip_spec hv hl hm
    obtain ⟨hl0, hlt, hrP⟩ := hcommon b hst
    set P := (snapAt input l).pending with hPdef
    set t := (snapAt input l).now with htdef
    have htt' : t ≤ t' := by rw [← hlt]; exact entryTime_mono hv hli'.le
    -- facts on the pending requests at `l`
    have hPreq : ∀ ρ ∈ P, ρ ∈ input.requests := fun ρ hρ => (pending_spec hv hρ).1
    have hParr : ∀ ρ ∈ P, ρ.arrival ≤ t := fun ρ hρ => (pending_spec hv hρ).2.1
    have hmono : ∀ ρ ∈ P, Monotone ρ.delay := fun ρ hρ => hv.delay_mono ρ (hPreq ρ hρ)
    have hzero : ∀ ρ ∈ P, ρ.delay 0 = 0 := fun ρ hρ => hv.delay_zero ρ (hPreq ρ hρ)
    have hcont : ∀ ρ ∈ P, Continuous ρ.delay := fun ρ hρ => hv.delay_continuous ρ (hPreq ρ hρ)
    have hunb : ∀ ρ ∈ P, ∀ M : ℝ, ∃ τ, M ≤ ρ.delay τ :=
      fun ρ hρ => hv.delay_unbounded ρ (hPreq ρ hρ)
    -- the delay at `t'` of the pending requests on `q` exceeds `w_q`
    have hqdelay : w q < pageDelay P q t' := by
      have hov' : w q < servedDelay input σ S (snapAt input i') q t' := hov
      refine hov'.trans_le ?_
      unfold servedDelay pageDelay
      set Q : Request Page → Bool := fun ρ => decide (ρ.page = q ∧ ρ.arrival ≤ τ) with hQ
      have hs1 : ((snapAt input i').pending.filter fun ρ => decide (ρ.page = q ∧
          ServedBy input σ S ρ t')).Sublist
          ((snapAt input i').pending.filter Q) := by
        apply List.monotone_filter_right
        intro ρ hρ
        simp only [decide_eq_true_eq, hQ] at hρ ⊢
        exact ⟨hρ.1, hservedτ ρ hρ.1 hρ.2⟩
      have hs2 : ((snapAt input i').pending.filter Q).Sublist (P.filter Q) := by
        apply pending_filter_sublist hv hli'.le τ Q
        · intro ρ hρ; simp only [decide_eq_true_eq, hQ] at hρ; exact hρ.2
        · intro m hm h1 h2 t₀ hmt
          exact lt_of_le_of_lt (le_of_le_of_eq hper.2.1 hlt)
            (lt_of_tick_after hv hl0 h1 hm hmt)
      have hs3 : (P.filter Q).Sublist (P.filter fun ρ => decide (ρ.page = q)) := by
        apply List.monotone_filter_right
        intro ρ hρ
        simp only [decide_eq_true_eq, hQ] at hρ ⊢
        exact hρ.1
      apply List.Sublist.sum_le_sum (((hs1.trans hs2).trans hs3).map _)
      intro a ha
      simp only [List.mem_map, List.mem_filter] at ha
      obtain ⟨ρ, ⟨hρ, -⟩, rfl⟩ := ha
      rw [← hzero ρ hρ]
      exact hmono ρ hρ (by linarith [hParr ρ hρ])
    have hdq : pageDeadline input P t q ≤ t' := pageDeadline_le htt' hqdelay
    -- the trip is chosen over `r`, so the deadline of its page is at most `t'`
    obtain ⟨hπ, hπle, hπd⟩ := tripCandidate_spec hcand
    have hdπ : pageDeadline input P t π.page ≤ t' :=
      (hπd r hrP hrl).trans (by rw [hrq]; exact hdq)
    have hwπ : w π.page ≤ pageDelay P π.page t' :=
      weight_le_pageDelay hmono hcont
        (exists_pageDelay_gt hmono hzero hunb hParr hπ rfl) hdπ
    have hπc : π.page ∉ cacheAt input S (entryTime input l) := by
      rw [Schedule.InPer.cacheAt_eq hv hSw hper]; exact not_mem_cacheAt hv hW hπle
    refine ⟨π.page, visitPage_of_trip hl hm, ?_⟩
    by_cases hserved : ∃ ρ ∈ P, ρ.page = π.page ∧
        ServedBy input σ S ρ (entryTime input l)
    · exact Or.inl ⟨hπc, hserved⟩
    · right
      push_neg at hserved
      -- no pending request on `π.page` is served by `t'`
      have hns : ∀ ρ ∈ P, ρ.page = π.page →
          ¬ ServedBy input σ S ρ t' := by
        intro ρ hρ hρp hs
        have hρc : ρ.page ∉ cacheAt input S τ :=
          hρp ▸ not_mem_cacheAt hv hW hπle
        exact hserved ρ hρ hρp (servedBy_mono hper.2.1 (servedBy_start hSw hper' hρc hs))
      refine hwπ.trans ((PendingProof.pageDelay_le_sum hv l π.page t'
        (fun ρ hρ => (hParr ρ hρ).trans htt')).trans ?_)
      unfold optDelayOn
      apply Finset.sum_le_sum
      intro j hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Schedule.delay_le_of_not_servedBy' hF hv j (hns _ hk.1 hk.2)
  · intro stop hm
    obtain ⟨b, hst, hstop, hs⟩ := closeHole_spec hv hl hm
    obtain ⟨-, -, hrP⟩ := hcommon b hst
    cases stop with
    | none => exact absurd hstop (tripCandidate_ne_none hrP hrl)
    | some π =>
      rw [hs]
      exact ⟨Option.some_ne_none π, hstop.2⟩

omit hσ hSw hF hW in
theorem stage_idle_of_mem {i : ℕ} (hi : i ∈ lightServices input σ S τ e) :
    ∃ h : i < (log input).length, ∃ p, moveAt i h = .critical p ∧ level input p ≤ e ∧
      (snapAt input i).stage = .idle ∧ InPer S τ (entryTime input i) := by
  simp only [lightServices, Finset.mem_filter] at hi
  obtain ⟨-, ⟨h, p, hm, hle⟩, -, hper⟩ := hi
  exact ⟨h, p, hm, hle, (critical_spec hv h hm).1, hper⟩

/-- `lem:periodlevel`: the deposits of the light services of one period and one level are at most `4W + (3/2) C_{j,W} + L W`, where `C_{j,W}` is the total weight of the chargeable level-`e` round trips of the period. The deposit of `λ^(m)` is at most `L W`; those of `λ^(1), …, λ^(m-1)` are at most the payments from `B_W` between `λ^(1)` and `λ^(m)` plus the budget left at `λ^(m)`. -/
theorem periodLevel_sum (he : e ≤ maxLevel input) :
    ∑ i ∈ lightServices input σ S τ e, levelLenAt input i e ≤
      4 * levelWeight e + 3 / 2 * ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l +
        L * levelWeight e := by
  set Φ := lightServices input σ S τ e with hΦ
  set T := ∑ l ∈ periodTrips input S τ e, tripChargeW input σ S l with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun l _ => tripChargeW_nonneg hv l
  have hW0 := levelWeight_pos e
  have hL := L_nonneg' input
  have hR0 : 0 ≤ 4 * levelWeight e + 3 / 2 * T := by positivity
  rcases Φ.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty]; nlinarith
  -- the last light service `λ^(m)`; its term is at most `L W`
  set i₁ := Φ.max' hne with hi₁def
  have hi₁ : i₁ ∈ Φ := Finset.max'_mem _ _
  rw [← Finset.add_sum_erase Φ _ hi₁]
  have hfirst : levelLenAt input i₁ e ≤ L * levelWeight e := levelLenAt_le _ _
  suffices hrest : ∑ i ∈ Φ.erase i₁, levelLenAt input i e ≤
      4 * levelWeight e + 3 / 2 * T by linarith
  rcases (Φ.erase i₁).eq_empty_or_nonempty with hemp' | hne'
  · rw [hemp', Finset.sum_empty]; exact hR0
  -- the first light service `λ^(1)`
  set i₀ := (Φ.erase i₁).min' hne' with hi₀def
  have hi₀ : i₀ ∈ Φ.erase i₁ := Finset.min'_mem _ _
  have hlt_of : ∀ x ∈ Φ.erase i₁, x < i₁ := fun x hx =>
    lt_of_le_of_ne (Finset.le_max' Φ x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hi₀lt := hlt_of i₀ hi₀
  obtain ⟨h₁, p₁, hm₁, -, hst₁, hper₁⟩ := stage_idle_of_mem hv hi₁
  obtain ⟨h₀, p₀, hm₀, hle₀, hst₀, hper₀⟩ :=
    stage_idle_of_mem hv (Finset.mem_of_mem_erase hi₀)
  -- the entries from `λ^(1)` up to `λ^(m)` lie in the early part
  have hperl : ∀ l, i₀ ≤ l → l ≤ i₁ → InPer S τ (entryTime input l) := fun l h1 h2 =>
    hper₁.of_le (hper₀.2.1.trans (entryTime_mono hv h1)) (entryTime_mono hv h2)
  have hearly : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      (∀ π, moveAt l hl = .trip e π → IsChargeable input σ S l) ∧
      (∀ stop, moveAt l hl = .closeHole e stop →
        stop ≠ none ∧ (snapAt input (l + 1)).budget e < levelWeight e) :=
    fun l hl h1 h2 => early_spec hv hσ hSw hF hW hl (hperl l h1 h2.le) hi₁ h2
  have hno : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      moveAt l hl ≠ .closeHole e none := fun l hl h1 h2 hmv =>
    ((hearly l hl h1 h2).2 none hmv).1 rfl
  -- the last critical service of level `≤ e` before `λ^(m)`
  set Cr := (Finset.Ico i₀ i₁).filter (fun l => IsLightService input e l) with hCr
  have hCrne : Cr.Nonempty := ⟨i₀, Finset.mem_filter.2
    ⟨Finset.mem_Ico.2 ⟨le_rfl, hi₀lt⟩, ⟨h₀, p₀, hm₀, hle₀⟩⟩⟩
  set a := Cr.max' hCrne with hadef
  have ha : a ∈ Cr := Finset.max'_mem _ _
  obtain ⟨haI, ⟨ha', pa, hma, hlea⟩⟩ := Finset.mem_filter.1 ha
  obtain ⟨hi₀a, hai₁⟩ := Finset.mem_Ico.1 haI
  -- the budget of level `e` between `λ^(1)` and `λ^(m)`
  have hpay := two_pay_le hv hi₀lt.le h₁.le hst₀ hst₁ hno
  have hdep := sum_dep_le hv (e := e) hi₀lt.le h₁.le
  have hmid : ∀ l (hl : l < (log input).length), a < l → l < i₁ →
      ∀ p', moveAt l hl = .critical p' → e < level input p' := by
    intro l hl h1 h2 p' hm
    by_contra hcon
    push_neg at hcon
    have hlC : l ∈ Cr := Finset.mem_filter.2
      ⟨Finset.mem_Ico.2 ⟨by omega, h2⟩, ⟨hl, p', hm, hcon⟩⟩
    have : l ≤ a := Finset.le_max' Cr l hlC
    omega
  -- the budget left at the end of the early part is below `4W`
  have hbal := budget_lt_of_next_critical hv he hai₁ h₁ ha' hma hlea ⟨p₁, hm₁⟩ hmid
    (fun l hl h1 h2 => hno l hl (by omega) h2)
  -- deposits of the light services before `λ^(m)`
  have hdepΦ : ∑ i ∈ Φ.erase i₁, levelLenAt input i e ≤
      ∑ l ∈ Finset.Ico i₀ i₁, dep input e l := by
    calc ∑ i ∈ Φ.erase i₁, levelLenAt input i e
        = ∑ i ∈ Φ.erase i₁, dep input e i := by
          apply Finset.sum_congr rfl
          intro i hi
          obtain ⟨h, p, hm, hle, -, -⟩ :=
            stage_idle_of_mem hv (Finset.mem_of_mem_erase hi)
          rw [levelLenAt_of_critical h hm, dep_of_critical hv h hm hle he]
      _ ≤ ∑ l ∈ Finset.Ico i₀ i₁, dep input e l := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_Ico.2 ⟨Finset.min'_le _ _ hx, hlt_of x hx⟩
          · intro x _ _; exact dep_nonneg hv e x
  -- the level-`e` round trips there are chargeable (`lem:early`)
  have htrip : ∑ l ∈ Finset.Ico i₀ i₁, tripWL input e l ≤ T := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico i₀ i₁)
      (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π)]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun l => ¬ _) _)
      (fun l hl => tripWL_eq_zero (Finset.mem_filter.1 hl).2), add_zero]
    calc ∑ l ∈ (Finset.Ico i₀ i₁).filter
          (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π),
          tripWL input e l
        = ∑ l ∈ (Finset.Ico i₀ i₁).filter
          (fun l => ∃ h : l < (log input).length, ∃ π, moveAt l h = .trip e π),
          tripChargeW input σ S l := by
          apply Finset.sum_congr rfl
          intro l hl
          obtain ⟨hlI, h, π, hm⟩ := Finset.mem_filter.1 hl
          obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hlI
          rw [tripWL_of_trip h hm,
            tripChargeW_of_chargeable h hm ((hearly l h h1 h2).1 π hm)]
      _ ≤ T := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro l hl
            obtain ⟨hlI, h, π, hm⟩ := Finset.mem_filter.1 hl
            obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hlI
            simp only [periodTrips, Finset.mem_filter, Finset.mem_range]
            exact ⟨h, ⟨h, π, hm⟩, hperl l h1 h2.le⟩
          · intro l _ _; exact tripChargeW_nonneg hv l
  linarith

end Early

end

end ExcessProof

end PMD

end PagingWithDelay
