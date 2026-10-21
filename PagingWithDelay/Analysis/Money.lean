import PagingWithDelay.Analysis.Defs

/-!
# The budget of one level (the budget argument of `lem:periodlevel`)

For a level `e`, we compare the payments from the budget `B_W` between two log entries with the total weight of the level-`e` round trips there. If no level-`e` preemptive service runs out of candidates, each starts with `B_W ≥ 4W`, pays at most `W` for its hole and ends with `B_W < W`, so it pays less than `3/2` times the weights of its round trips (`two_pay_le`). The deposits `|λ|_W` (`levelLen`) are at most the payments plus the final budget (`sum_dep_le`). After a critical service on a page of level `≤ e`, `B_W` is below `4W` at the next such critical service (`budget_lt_of_next_critical`).
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

noncomputable section

/-! ### The round-trip candidate -/

section Candidate

variable {input : Instance Page}

theorem tripCandidate_spec {pending : List (Request Page)} {t : ℝ} {e : ℤ}
    {π : Request Page} (h : tripCandidate input pending t e = some π) :
    π ∈ pending ∧ level input π.page ≤ e ∧
      ∀ ρ ∈ pending, level input ρ.page ≤ e →
        pageDeadline input pending t π.page ≤ pageDeadline input pending t ρ.page := by
  unfold tripCandidate at h
  have hm := List.argmin_mem h
  simp only [List.mem_filter, decide_eq_true_eq] at hm
  refine ⟨hm.1, hm.2, fun ρ hρ hl => ?_⟩
  have hmem : ρ ∈ pending.filter (fun ρ => decide (level input ρ.page ≤ e)) := by
    simpa [List.mem_filter] using ⟨hρ, hl⟩
  exact List.le_of_mem_argmin (f := fun ρ : Request Page => pageDeadline input pending t ρ.page)
    hmem h

theorem tripCandidate_ne_none {pending : List (Request Page)} {t : ℝ} {e : ℤ}
    {ρ : Request Page} (hρ : ρ ∈ pending) (hl : level input ρ.page ≤ e) :
    tripCandidate input pending t e ≠ none := by
  unfold tripCandidate
  rw [Ne, List.argmin_eq_none]
  intro h
  have : ρ ∈ pending.filter (fun ρ => decide (level input ρ.page ≤ e)) := by
    simpa [List.mem_filter] using ⟨hρ, hl⟩
  rw [h] at this
  simp at this

end Candidate

/-! ### Small run facts -/

section RunFacts

variable {input : Instance Page} (hv : input.Valid)
include hv

theorem level_le_iff' (p : Page) (e : ℤ) :
    level input p ≤ e ↔ w p ≤ levelWeight e :=
  PagingWithDelay.PMD.level_le_iff hv p e

theorem preempt_state {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) :
    (snapAt input i).x = hole input b e ∧ IsRest input b := by
  refine ⟨(x_eq_hole hv hs).1, ?_⟩
  have := baseState_isRest hv i
  unfold baseState at this
  rw [hs] at this
  exact this

theorem tripCost_nonneg_le {i : ℕ} {e : ℤ} {b : Page → ℝ}
    (hs : (snapAt input i).stage = .preempt e b) (p : Page) :
    0 ≤ tripCost input (snapAt input i).x p ∧
      tripCost input (snapAt input i).x p ≤ w p := by
  have hvb := hv
  obtain ⟨hx, hb⟩ := preempt_state hv hs
  have h1 := PagingWithDelay.PMD.hole_le_one hvb hb.1 e p
  have h2 := PagingWithDelay.PMD.le_hole hvb hb.1 e p
  have h3 := (hb.1 p).1
  have hw := hv.weight_pos p
  have hd := Instance.delta_pos hv
  unfold tripCost
  rw [hx]
  constructor
  · exact mul_nonneg hw.le (by linarith)
  · nlinarith

theorem not_idle_of_preempt {l : ℕ} {e : ℤ} {b : Page → ℝ}
    (hst : (snapAt input l).stage = .preempt e b) : (snapAt input l).stage ≠ .idle := by
  rw [hst]; simp

/-- Moves inside a preemptive service happen at the current time. -/
theorem entryTime_of_preempt {l : ℕ} {e : ℤ} {b : Page → ℝ}
    (hst : (snapAt input l).stage = .preempt e b) :
    ∃ hl : l < (log input).length, entryTime input l = (snapAt input l).now := by
  have hl := lt_length_of_stage hv (not_idle_of_preempt hv hst)
  obtain ⟨-, h1, h2⟩ := not_idle_moves hv hl (not_idle_of_preempt hv hst)
  exact ⟨hl, entryTime_of_not_tick hv hl h1 h2⟩

/-- Only critical services increase budgets. -/
theorem budget_succ_le_of_not_critical {i : ℕ} (h : i < (log input).length)
    (hm : ∀ p, moveAt i h ≠ .critical p) (e : ℤ) :
    (snapAt input (i + 1)).budget e ≤ (snapAt input i).budget e := by
  generalize hmv : moveAt i h = m at hm
  cases m with
  | tick t =>
    rw [(tick_spec hv h hmv).2.2.2.2]
  | advance t =>
    rw [(advance_spec hv h hmv).2.2.2.2.2.2]
  | critical p => exact absurd rfl (hm p)
  | skip e' =>
    rw [(skip_spec hv h hmv).2.2]
  | openHole e' =>
    obtain ⟨hst, -, hs⟩ := openHole_spec hv h hmv
    rw [hs]
    simp only
    by_cases he : e = e'
    · subst he
      rw [Function.update_self]
      have : 0 ≤ holePayment input e :=
        mul_nonneg (levelWeight_pos e).le (by simp; linarith [Instance.delta_lt_one hv])
      linarith
    · rw [Function.update_of_ne he]
  | trip e' π =>
    obtain ⟨⟨b, hst⟩, -, -, hs⟩ := trip_spec hv h hmv
    rw [hs]
    simp only
    by_cases he : e = e'
    · subst he
      rw [Function.update_self]
      linarith [(tripCost_nonneg_le hv hst π.page).1]
    · rw [Function.update_of_ne he]
  | closeHole e' stop =>
    obtain ⟨b, -, -, hs⟩ := closeHole_spec hv h hmv
    rw [hs]

theorem budget_succ_of_critical {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    (snapAt input (i + 1)).budget e =
      if level input p ≤ e ∧ e ≤ maxLevel input then
        (snapAt input i).budget e + levelLen input (snapAt input i).x p e
      else (snapAt input i).budget e := by
  rw [(critical_spec hv h hm).2.2]
  rfl

theorem budget_succ_critical_ge {i : ℕ} (h : i < (log input).length) {p : Page}
    (hm : moveAt i h = .critical p) (e : ℤ) :
    (snapAt input i).budget e ≤ (snapAt input (i + 1)).budget e := by
  rw [budget_succ_of_critical hv h hm]
  split_ifs
  · linarith [C.levelLen_nonneg (input := input) (snapAt input i).x p e]
  · exact le_rfl

end RunFacts

/-! ### Payments, deposits and the slack of a preemptive service -/

variable (input : Instance Page)

/-- The payment from `B_e` at entry `l` (the decrease of `B_e`, except at critical services). -/
def pay (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .critical _ => 0
    | _ => (snapAt input l).budget e - (snapAt input (l + 1)).budget e
  else 0

/-- The deposit into `B_e` at entry `l` (the increase of `B_e` at critical services). -/
def dep (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .critical _ => (snapAt input (l + 1)).budget e - (snapAt input l).budget e
    | _ => 0
  else 0

/-- The weight of the page of a level-`e` round trip at entry `l` (else `0`). -/
def tripWL (e : ℤ) (l : ℕ) : ℝ :=
  if h : l < (log input).length then
    match moveAt l h with
    | .trip e' π => if e' = e then w π.page else 0
    | _ => 0
  else 0

/-- The slack of the preemptive service invariant: inside a level-`e` preemptive service, `B_e - 2^e`. -/
def slack (e : ℤ) (s : Snap Page) : ℝ :=
  match s.stage with
  | .preempt e' _ => if e' = e then s.budget e - levelWeight e else 0
  | _ => 0

variable {input}

theorem slack_of_not_preempt {s : Snap Page} {e : ℤ} (h : ∀ b, s.stage ≠ .preempt e b) :
    slack e s = 0 := by
  unfold slack
  rcases hs : s.stage with _ | e' | ⟨e', b⟩
  · rfl
  · rfl
  · simp only
    split_ifs with he
    · subst he; exact absurd hs (h b)
    · rfl

theorem slack_preempt {s : Snap Page} {e : ℤ} {b : Page → ℝ} (h : s.stage = .preempt e b) :
    slack e s = s.budget e - levelWeight e := by
  unfold slack
  rw [h]
  simp

theorem afterLevel_ne_preempt (e e' : ℤ) (b : Page → ℝ) :
    afterLevel input e ≠ .preempt e' b := by
  unfold afterLevel
  split_ifs <;> simp

/-- Telescoping inequality. -/
theorem sum_Ico_le_telescope (g u : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ l, a ≤ l → l < b → g l ≤ u (l + 1) - u l) :
    ∑ l ∈ Finset.Ico a b, g l ≤ u b - u a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have h1 := ih (fun l h1 h2 => h l h1 (by omega))
    have h2 := h n hn (by omega)
    linarith

theorem antitone_of_step (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ l, a ≤ l → l < b → f (l + 1) ≤ f l) : f b ≤ f a := by
  have := sum_Ico_le_telescope (fun _ => (0 : ℝ)) (fun l => - f l) hab
    (fun l h1 h2 => by have := h l h1 h2; simp; linarith)
  simp at this
  linarith

section

variable (hv : input.Valid)
include hv

theorem budget_step (e : ℤ) {l : ℕ} (hl : l < (log input).length) :
    dep input e l - pay input e l =
      (snapAt input (l + 1)).budget e - (snapAt input l).budget e := by
  unfold dep pay
  rw [dif_pos hl, dif_pos hl]
  cases moveAt l hl <;> simp

theorem dep_nonneg (e : ℤ) (l : ℕ) : 0 ≤ dep input e l := by
  unfold dep
  split_ifs with hl
  · generalize hmv : moveAt l hl = m
    cases m with
    | critical p =>
      simp only
      linarith [budget_succ_critical_ge hv hl hmv e]
    | _ => simp
  · exact le_rfl

theorem dep_of_critical {e : ℤ} {l : ℕ} (hl : l < (log input).length) {p : Page}
    (hm : moveAt l hl = .critical p) (hle : level input p ≤ e)
    (he : e ≤ maxLevel input) :
    dep input e l = levelLen input (snapAt input l).x p e := by
  unfold dep
  rw [dif_pos hl, hm]
  simp only
  rw [budget_succ_of_critical hv hl hm e, if_pos ⟨hle, he⟩]
  ring

/-- One step of the preemptive service invariant. -/
theorem slack_step (e : ℤ) {l : ℕ} (hl : l < (log input).length)
    (hno : moveAt l hl ≠ .closeHole e none) :
    slack e (snapAt input l) + (2 * pay input e l - 3 * tripWL input e l) ≤
      slack e (snapAt input (l + 1)) := by
  have hpay : ∀ m, moveAt l hl = m → pay input e l = (match m with
      | .critical _ => 0
      | _ => (snapAt input l).budget e - (snapAt input (l + 1)).budget e) := by
    intro m hm; unfold pay; rw [dif_pos hl, hm]
  have htw : ∀ m, moveAt l hl = m → tripWL input e l = (match m with
      | .trip e' π => if e' = e then w π.page else 0
      | _ => 0) := by
    intro m hm; unfold tripWL; rw [dif_pos hl, hm]
  generalize hmv : moveAt l hl = m at hno
  have hp := hpay m hmv
  have ht := htw m hmv
  cases m with
  | tick t =>
    obtain ⟨hst, -, -, -, hs⟩ := tick_spec hv hl hmv
    simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; simp [hst])]
    simp only at hp
    rw [hp, ht]; simp
  | advance t =>
    obtain ⟨hst, -, -, -, -, -, hs⟩ := advance_spec hv hl hmv
    simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; simp [hst])]
    simp only at hp
    rw [hp, ht]; simp
  | critical p =>
    obtain ⟨hst, -, hs⟩ := critical_spec hv hl hmv
    simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs, slack_of_not_preempt (by intro b; simp)]
    rw [hp, ht]; simp
  | skip e' =>
    obtain ⟨hst, -, hs⟩ := skip_spec hv hl hmv
    simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    rw [slack_of_not_preempt (by intro b; exact afterLevel_ne_preempt _ _ _)]
    simp only at hp
    rw [hp, ht]; simp
  | openHole e' =>
    obtain ⟨hst, hcond, hs⟩ := openHole_spec hv hl hmv
    simp only at hp ht
    rw [slack_of_not_preempt (by intro b; rw [hst]; simp)]
    rw [hs] at hp ⊢
    simp only at hp
    rw [ht]
    by_cases he : e' = e
    · subst he
      rw [slack_preempt (by rfl)]
      simp only [Function.update_self] at hp ⊢
      have h1 : holePayment input e' ≤ (1 - δ) * levelWeight e' := by
        unfold holePayment; rw [mul_comm]
      have h2 := hcond.1
      have hd := Instance.delta_pos hv
      have hW := levelWeight_pos e'
      have h3 : (1 - δ) * levelWeight e' ≤ levelWeight e' := by nlinarith
      rw [hp]
      linarith
    · rw [slack_of_not_preempt (by intro b hb; simp at hb; exact he hb.1)]
      simp only [Function.update_of_ne (Ne.symm he)] at hp
      rw [hp]; simp
  | trip e' π =>
    obtain ⟨⟨b, hst⟩, hcand, hle, hs⟩ := trip_spec hv hl hmv
    simp only at hp ht
    rw [hs] at hp ⊢
    simp only at hp
    by_cases he : e' = e
    · subst he
      rw [slack_preempt hst, slack_preempt (by simpa using hst)]
      simp only [Function.update_self, if_pos] at hp ht ⊢
      have := (tripCost_nonneg_le hv hst π.page).2
      rw [hp, ht]
      linarith
    · rw [slack_of_not_preempt (by intro b' hb'; rw [hst] at hb'; simp at hb'; exact he hb'.1)]
      rw [slack_of_not_preempt (by intro b' hb'; simp [hst] at hb'; exact he hb'.1)]
      simp only [Function.update_of_ne (Ne.symm he), if_neg he] at hp ht
      rw [hp, ht]; simp
  | closeHole e' stop =>
    obtain ⟨b, hst, hstop, hs⟩ := closeHole_spec hv hl hmv
    simp only at hp ht
    have h0 : slack e (snapAt input (l + 1)) = 0 :=
      slack_of_not_preempt (by intro b'; rw [hs]; exact afterLevel_ne_preempt _ _ _)
    rw [h0]
    rw [hs] at hp
    simp only at hp
    rw [hp, ht]
    by_cases he : e' = e
    · subst he
      rw [slack_preempt hst]
      cases stop with
      | none => exact absurd rfl hno
      | some π =>
        simp; linarith [hstop.2]
    · rw [slack_of_not_preempt (by intro b' hb'; rw [hst] at hb'; simp at hb'; exact he hb'.1)]
      simp

/-- `lem:periodlevel`, the payments: between two idle entries, if no level-`e` preemptive service runs out of candidates, the payments from `B_e` are at most `3/2` times the weights of the level-`e` round trips. -/
theorem two_pay_le {e : ℤ} {i₀ i₁ : ℕ} (h01 : i₀ ≤ i₁) (h1 : i₁ ≤ (log input).length)
    (hst₀ : (snapAt input i₀).stage = .idle) (hst₁ : (snapAt input i₁).stage = .idle)
    (hno : ∀ l (hl : l < (log input).length), i₀ ≤ l → l < i₁ →
      moveAt l hl ≠ .closeHole e none) :
    2 * ∑ l ∈ Finset.Ico i₀ i₁, pay input e l ≤
      3 * ∑ l ∈ Finset.Ico i₀ i₁, tripWL input e l := by
  have := sum_Ico_le_telescope (fun l => 2 * pay input e l - 3 * tripWL input e l)
    (fun l => slack e (snapAt input l)) h01 (fun l hl1 hl2 => by
      have hl : l < (log input).length := by omega
      have := slack_step hv e hl (hno l hl hl1 hl2)
      simp only; linarith)
  simp only at this
  rw [slack_of_not_preempt (by intro b; rw [hst₁]; simp),
    slack_of_not_preempt (by intro b; rw [hst₀]; simp)] at this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  linarith

/-- The deposits between two entries are at most the payments plus the final budget. -/
theorem sum_dep_le {e : ℤ} {i₀ i₁ : ℕ} (h01 : i₀ ≤ i₁) (h1 : i₁ ≤ (log input).length) :
    ∑ l ∈ Finset.Ico i₀ i₁, dep input e l ≤
      (snapAt input i₁).budget e + ∑ l ∈ Finset.Ico i₀ i₁, pay input e l := by
  have := sum_Ico_le_telescope (fun l => dep input e l - pay input e l)
    (fun l => (snapAt input l).budget e) h01 (fun l hl1 hl2 => by
      simp only
      rw [budget_step hv e (by omega : l < (log input).length)])
  simp only at this
  rw [Finset.sum_sub_distrib] at this
  have := budget_nonneg hv i₀ e
  linarith

/-- `lem:periodlevel`, the leftover budget: after a critical service on a page of level `≤ e`, the budget of level `e` is below `4 · 2^e` at the next such critical service (if no level-`e` preemptive service in between runs out of candidates). -/
theorem budget_lt_of_next_critical {e : ℤ} (he : e ≤ maxLevel input) {a b : ℕ}
    (hab : a < b) (hb : b < (log input).length) (ha : a < (log input).length) {p : Page}
    (hma : moveAt a ha = .critical p) (hp : level input p ≤ e)
    (hbp : ∃ p', moveAt b hb = .critical p')
    (hmid : ∀ l (hl : l < (log input).length), a < l → l < b →
      ∀ p', moveAt l hl = .critical p' → e < level input p')
    (hno : ∀ l (hl : l < (log input).length), a ≤ l → l < b →
      moveAt l hl ≠ .closeHole e none) :
    (snapAt input b).budget e < 4 * levelWeight e := by
  obtain ⟨j, hj, haj, hmj, hbet⟩ :=
    levelLoop_examines hv ha hma ((minLevel_le p).trans hp) he
  have hjb : j < b := by
    by_contra hcon
    obtain ⟨p', hp'⟩ := hbp
    exact (hbet b hb hab (by omega)).1 p' hp'
  have hW := levelWeight_pos e
  -- the budget right after the examination of level `e`
  have hj1 : (snapAt input (j + 1)).budget e < 4 * levelWeight e := by
    rcases hmj with hmj | ⟨stop, hmj⟩
    · obtain ⟨hst, hncond, hs⟩ := skip_spec hv hj hmj
      rw [hs]
      simp only
      -- the hole condition holds, so the budget condition fails
      obtain ⟨-, -, hxa, hra, -⟩ := critical_facts hv ha hma
      have hbase : ∀ l, a + 1 ≤ l → l ≤ j →
          baseState (snapAt input l) = baseState (snapAt input (a + 1)) := by
        intro l h1 h2
        induction l, h1 using Nat.le_induction with
        | base => rfl
        | succ n hn ih =>
          rw [← ih (by omega)]
          exact baseState_succ_of_not_critical hv (by omega)
            (hbet n (by omega) (by omega) (by omega)).1
      have hxj : (snapAt input j).x = criticalState input (snapAt input a).x p := by
        rw [x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb),
          hbase j (by omega) le_rfl]
        have hs1 := (critical_spec hv ha hma).2.2
        have : (snapAt input (a + 1)).stage = .examine (minLevel input) := by rw [hs1]
        rw [← x_eq_baseState hv (by intro e b hb; rw [this] at hb; cases hb), hs1]
      have hrest := baseState_isRest hv j
      rw [← x_eq_baseState hv (by intro e b hb; rw [hst] at hb; cases hb)] at hrest
      have hcond : 1 - δ ≤
          ∑ i ∈ Finset.univ.filter (fun i => level input i ≤ e),
            (1 - (snapAt input j).x i) := by
        have hmem : p ∈ Finset.univ.filter (fun i => level input i ≤ e) := by simp [hp]
        have := Finset.single_le_sum (f := fun i => 1 - (snapAt input j).x i)
          (fun i _ => by have := (hrest.1 i).2; linarith) hmem
        simp only at this
        rw [hxj, PagingWithDelay.PMD.criticalState_self hv hxa
          (by simpa using hra)] at this
        rw [hxj]
        exact this
      unfold preemptCondition at hncond
      push_neg at hncond
      by_contra hcon
      push_neg at hcon
      exact absurd hcond (not_le.2 (hncond hcon))
    · obtain ⟨bb, hst, hstop, hs⟩ := closeHole_spec hv hj hmj
      rw [hs]
      simp only
      cases stop with
      | none => exact absurd hmj (hno j hj (by omega) hjb)
      | some π =>
        linarith [hstop.2]
  -- afterwards it does not increase until `b`
  have hmono := antitone_of_step (fun l => (snapAt input l).budget e) (show j + 1 ≤ b by omega)
    (fun l h1 h2 => by
      have hl : l < (log input).length := by omega
      simp only
      generalize hmv : moveAt l hl = m
      cases m with
      | critical p' =>
        rw [budget_succ_of_critical hv hl hmv e,
          if_neg (fun h => absurd h.1 (not_le.2 (hmid l hl (by omega) h2 p' hmv)))]
      | _ => exact budget_succ_le_of_not_critical hv hl (by intro p' h; rw [hmv] at h; cases h) e)
  simp only at hmono
  linarith

end

end

end ExcessProof

end PMD

end PagingWithDelay
