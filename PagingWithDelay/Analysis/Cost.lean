import PagingWithDelay.Analysis.Defs

/-!
# The fetch cost of `PMD` (`prop:preemptfetch`, `lem:lengthfetch`)

The fetch cost of `PMD`, in terms of the critical services of the log.

* A critical service `λ` deposits `|λ|_W` into `B_W` for `w_p ≤ W ≤ w_max`, in total at most `|λ|` (`sum_levelLen_le`); the budgets start at `0` and stay nonnegative, so the payments for holes and round trips are at most `∑_λ |λ|` (`holeTotal_add_tripTotal_le`).
* `|λ| ≤ 3 EV(λ)` (`lem:clock`), so `∑_λ |λ| ≤ 3 ∑_λ EV(λ)` (`lenTotal_le`).
* `∑_λ EV(λ) ≤ ∑_λ fetch(λ) + ∑ wᵢ` (`lem:evfetch`), by telescoping `∑ᵢ wᵢ xᵢ` of the base state (`evTotal_le`); with the previous item this is `lem:lengthfetch` (`lenTotal_le_fetchTotal`).
* A critical service fetches `fetch(λ)`, a round trip its cost, closing a hole at most its payment `W (1 - δ)`; nothing else fetches (`fetchCost_le_preempt`; with the budget bound this is `prop:preemptfetch`, `fetchCost_le_lenTotal`).

Hence the fetch cost is at most `4 ∑_λ fetch(λ) + 3 ∑ wᵢ` (`fetchCost_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PagingWithDelay

namespace PMD

namespace CostProof

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open PagingWithDelay.PMD (level minLevel maxLevel levelWeight serviceEnd criticalState
  criticalFetch criticalEV hole holePayment preemptCondition tripCost afterLevel Stage IsRest
  IsFrac pathFrom lastState dFetch closingCost pathFrom_cons pathFrom_nil dFetch_self)

noncomputable section

variable (input : Instance Page)

/-! ### Helpers: per-entry contributions -/

/-- The closing cost of the hole opened by entry `i`, if it opens one. -/
def openAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .openHole e => closingCost input (snapAt input i).x e
    | _ => 0
  else 0

/-- The closing cost of the currently open hole (`0` outside a preemptive service). -/
def pendingClose (s : Snap Page) : ℝ :=
  match s.stage with
  | .preempt e b => closingCost input b e
  | _ => 0

/-- The closing cost of the hole closed by entry `i`, if it closes one. -/
def closeAt (i : ℕ) : ℝ :=
  if h : i < (log input).length then
    match moveAt i h with
    | .closeHole _ _ => pendingClose input (snapAt input i)
    | _ => 0
  else 0

open scoped InstanceNotation in
/-- The weighted mass `∑ⱼ wⱼ xⱼ` of the base state. -/
def baseMass (s : Snap Page) : ℝ := ∑ j, w j * baseState s j

/-- The total budget of all levels. -/
def totalBudget (s : Snap Page) : ℝ :=
  ∑ e ∈ Finset.Icc (minLevel input) (maxLevel input), s.budget e

variable {input}

theorem pendingClose_afterLevel (s : Snap Page) (e : ℤ) :
    pendingClose input { s with stage := afterLevel input e } = 0 := by
  unfold pendingClose afterLevel
  split_ifs <;> rfl

theorem sum_update_single (w : Page → ℝ) (x : Page → ℝ) (p : Page) (v : ℝ)
    (g : ℝ → ℝ → ℝ) (hg : ∀ a, g a a = 0) :
    ∑ j, w j * g (Function.update x p v j) (x j) = w p * g v (x p) := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj, hg]
  · simp

section

variable (hv : input.Valid)
include hv

theorem isRest_x_of_not_preempt {i : ℕ}
    (hs : ∀ e b, (snapAt input i).stage ≠ .preempt e b) :
    IsRest input (snapAt input i).x := by
  rw [x_eq_baseState hv hs]; exact baseState_isRest hv i

theorem trip_mem_pending {i : ℕ} (h : i < (log input).length) {e : ℤ} {π : Request Page}
    (hm : moveAt i h = .trip e π) : π ∈ (snapAt input i).pending := by
  obtain ⟨-, hcand, -⟩ := trip_spec hv h hm
  exact (List.mem_filter.1 (List.argmin_mem hcand)).1

open scoped InstanceNotation in
/-- Everything an entry contributes. -/
theorem entry_spec (i : ℕ) (h : i < (log input).length) :
    pathFrom (dFetch input) (snapAt input i).x (wpAt input i) =
      fetchAt input i + tripAt input i + closeAt input i ∧
    pendingClose input (snapAt input (i + 1)) - pendingClose input (snapAt input i) =
      openAt input i - closeAt input i ∧
    totalBudget input (snapAt input (i + 1)) - totalBudget input (snapAt input i) ≤
      lenAt input i - holeAt input i - tripAt input i ∧
    baseMass input (snapAt input (i + 1)) - baseMass input (snapAt input i) =
      evAt input i - fetchAt input i := by
  have hvb := hv
  have hok := stageOK hv i
  have hbase : ∀ (hnp : ∀ p, moveAt i h ≠ .critical p),
      baseMass input (snapAt input (i + 1)) - baseMass input (snapAt input i) = 0 := by
    intro hnp; simp [baseMass, baseState_succ_of_not_critical hv h hnp]
  rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
  · -- tick
    have he := (tick_spec hv h hm).2.2.2.2
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil,
      dFetch_self, totalBudget, pendingClose]
    all_goals try first | rfl | ring1 | simp
  · -- advance
    have he := (advance_spec hv h hm).2.2.2.2.2.2
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil,
      dFetch_self, totalBudget, pendingClose]
    all_goals try first | rfl | ring1 | simp
  · -- critical service
    obtain ⟨hs, -, he⟩ := critical_spec hv h hm
    obtain ⟨-, -, hx, hr, -⟩ := critical_facts hv h hm
    have hb0 : baseState (snapAt input i) = (snapAt input i).x := by simp [baseState, hs]
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    rw [he]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [pathFrom_cons, pathFrom_nil, dFetch]
      rw [PagingWithDelay.PMD.critical_fetchCost hvb hx hr]; ring
    · simp [pendingClose, hs]
    · simp only [totalBudget]
      rw [← Finset.sum_sub_distrib]
      have hsum : ∑ e ∈ Finset.Icc (minLevel input) (maxLevel input),
          (deposit input (snapAt input i).x p (snapAt input i).budget e -
            (snapAt input i).budget e) =
          ∑ e ∈ Finset.Icc (level input p) (maxLevel input),
            levelLen input (snapAt input i).x p e := by
        have hsub : Finset.Icc (level input p) (maxLevel input) ⊆
            Finset.Icc (minLevel input) (maxLevel input) :=
          Finset.Icc_subset_Icc (PagingWithDelay.PMD.minLevel_le p) le_rfl
        rw [← Finset.sum_subset hsub]
        · apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_Icc] at he
          simp [deposit, he]
        · intro e _ he
          rw [Finset.mem_Icc] at he
          simp only [deposit]
          rw [if_neg (by tauto)]; ring
      rw [hsum]
      have := sum_levelLen_le (input := input) (snapAt input i).x p
      linarith
    · simp only [baseMass, hb0]
      simp only [baseState]
      have hw := PagingWithDelay.PMD.critical_weightedMass hvb hx hr
      rw [hw]; ring
  · -- skip
    obtain ⟨hs, -, he⟩ := skip_spec hv h hm
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); (try rw [pendingClose_afterLevel]); simp only [pathFrom_nil,
      totalBudget, pendingClose, hs]
    all_goals try first | rfl | ring1 | simp
  · -- openHole
    obtain ⟨hs, -, he⟩ := openHole_spec hv h hm
    have hx : IsRest input (snapAt input i).x :=
      isRest_x_of_not_preempt hv (by rw [hs]; simp)
    have hb := hbase (by rw [hm]; simp)
    rw [hs] at hok
    have hmem : e ∈ Finset.Icc (minLevel input) (maxLevel input) :=
      Finset.mem_Icc.2 hok
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, dFetch,
      pendingClose, hs, totalBudget, PagingWithDelay.PMD.hole_fetch_open hvb hx.1]
    all_goals try first | rfl | ring1 | (rw [sum_update_eq hmem]; linarith)
  · -- trip
    obtain ⟨⟨b, hs⟩, hcand, -, he⟩ := trip_spec hv h hm
    have hπ := trip_mem_pending hv h hm
    have hr : δ < (snapAt input i).x π.page := delta_lt_of_pending hv hπ
    have hb := hbase (by rw [hm]; simp)
    rw [hs] at hok
    have hmem : e ∈ Finset.Icc (minLevel input) (maxLevel input) :=
      Finset.mem_Icc.2 hok
    have h3 : dFetch input (snapAt input i).x
        (Function.update (snapAt input i).x π.page δ) =
        tripCost input (snapAt input i).x π.page := by
      unfold dFetch tripCost
      rw [sum_update_single _ _ _ _ (fun a b => max 0 (b - a)) (by simp)]
      rw [max_eq_right (by simpa using hr.le)]
    have h4 : dFetch input (Function.update (snapAt input i).x π.page δ)
        (snapAt input i).x = 0 := by
      unfold dFetch
      rw [sum_update_single _ _ _ _ (fun a b => max 0 (a - b)) (by simp)]
      rw [max_eq_left (by linarith)]; ring
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, h3, h4,
      pendingClose, hs, totalBudget]
    all_goals try first | rfl | ring1 | (rw [sum_update_eq hmem]; linarith)
  · -- closeHole
    obtain ⟨b, hs, -, he⟩ := closeHole_spec hv h hm
    obtain ⟨hx, -⟩ := x_eq_hole hv hs
    have hbr : IsRest input b := by
      have := baseState_isRest hv i; rwa [baseState_of_preempt hs] at this
    have hb := hbase (by rw [hm]; simp)
    simp only [wpAt, dif_pos h, hm, fetchAt, evAt, lenAt, holeAt, tripAt, openAt, closeAt,
      waypoints, hs]
    refine ⟨?_, ?_, ?_, by linarith⟩
    all_goals (try rw [he]); simp only [pathFrom_cons, pathFrom_nil, dFetch, hx,
      pendingClose, hs, totalBudget, PagingWithDelay.PMD.hole_fetch_close hvb hbr.1]
    all_goals try first | rfl | ring1 | (unfold afterLevel; split_ifs <;> rfl) | simp

/-! ### Nonnegativity -/

theorem fetchAt_nonneg (i : ℕ) : 0 ≤ fetchAt input i := by
  unfold fetchAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨-, -, -, hr, -⟩ := critical_facts hv h hm
    unfold criticalFetch
    exact mul_nonneg (hv.weight_pos p).le (by linarith)
  · exact le_rfl

theorem lenAt_nonneg (i : ℕ) : 0 ≤ lenAt input i := by
  unfold lenAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    exact C.serviceEnd_nonneg' _ _
  · exact le_rfl

/-- `lem:clock` for every entry: `|λ| ≤ 3 EV(λ)`. -/
theorem lenAt_le (i : ℕ) : lenAt input i ≤ 3 * evAt input i := by
  unfold lenAt evAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨-, -, hx, hr, -⟩ := critical_facts hv h hm
    exact serviceEnd_le_three_mul_criticalEV hv hx hr
  · simp

theorem holeAt_nonneg (i : ℕ) : 0 ≤ holeAt input i := by
  unfold holeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    unfold holePayment
    exact mul_nonneg (PagingWithDelay.PMD.levelWeight_pos e).le
      (by linarith [Instance.delta_lt_one hv])
  · exact le_rfl

open scoped InstanceNotation in
theorem tripAt_nonneg (i : ℕ) : 0 ≤ tripAt input i := by
  unfold tripAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    have hr : δ < (snapAt input i).x π.page :=
      delta_lt_of_pending hv (trip_mem_pending hv h hm)
    unfold tripCost
    exact mul_nonneg (hv.weight_pos _).le (by linarith)
  · exact le_rfl

theorem closeAt_nonneg (i : ℕ) : 0 ≤ closeAt input i := by
  unfold closeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨b, hs, -, -⟩ := closeHole_spec hv h hm
    have hbr : IsRest input b := by
      have := baseState_isRest hv i; rwa [baseState_of_preempt hs] at this
    simp only [pendingClose, hs, PagingWithDelay.PMD.closingCost]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hv.weight_pos j).le
      (by linarith [PagingWithDelay.PMD.le_hole hv hbr.1 e j])
  · exact le_rfl

theorem fetchTotal_nonneg : 0 ≤ fetchTotal input :=
  Finset.sum_nonneg fun i _ => fetchAt_nonneg hv i

theorem lenTotal_nonneg : 0 ≤ lenTotal input :=
  Finset.sum_nonneg fun i _ => lenAt_nonneg hv i

theorem holeTotal_nonneg : 0 ≤ holeTotal input :=
  Finset.sum_nonneg fun i _ => holeAt_nonneg hv i

theorem tripTotal_nonneg : 0 ≤ tripTotal input :=
  Finset.sum_nonneg fun i _ => tripAt_nonneg hv i

/-! ### Payments, deposits and lengths -/

/-- A hole costs at most its payment `W (1 - δ)` to close. -/
theorem openAt_le_holeAt (i : ℕ) : openAt input i ≤ holeAt input i := by
  unfold openAt holeAt
  split_ifs with h
  · rcases hm : moveAt i h with t | t | p | e | e | ⟨e, π⟩ | ⟨e, stop⟩
    all_goals try simp
    obtain ⟨hs, -, -⟩ := openHole_spec hv h hm
    have hx : IsRest input (snapAt input i).x :=
      isRest_x_of_not_preempt hv (by rw [hs]; simp)
    have := PagingWithDelay.PMD.closingCost_le hv hx.1 e
    simp only [holePayment]
    linarith
  · exact le_rfl

theorem sum_open_eq_close :
    ∑ i ∈ Finset.range (log input).length, openAt input i =
      ∑ i ∈ Finset.range (log input).length, closeAt input i := by
  have h := Finset.sum_range_sub (fun i => pendingClose input (snapAt input i))
    (log input).length
  rw [Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.1),
    Finset.sum_sub_distrib] at h
  simp only [pendingClose, (final_spec hv).2.2.1, snapAt_zero hv, initialSnap] at h
  linarith

/-- The budget payments (for holes and round trips) are at most the deposits, hence at most the lengths of the critical services. -/
theorem holeTotal_add_tripTotal_le : holeTotal input + tripTotal input ≤ lenTotal input := by
  have h := Finset.sum_range_sub (fun i => totalBudget input (snapAt input i))
    (log input).length
  have hle := Finset.sum_le_sum
    (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.2.1)
  rw [h, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hle
  have hN : 0 ≤ totalBudget input (snapAt input (log input).length) :=
    Finset.sum_nonneg fun e _ => budget_nonneg hv _ e
  have h0 : totalBudget input (snapAt input 0) = 0 := by
    simp [totalBudget, snapAt_zero hv, initialSnap]
  unfold holeTotal tripTotal lenTotal
  linarith

/-- `lem:clock`, summed: `∑_λ |λ| ≤ 3 ∑_λ EV(λ)`. -/
theorem lenTotal_le : lenTotal input ≤ 3 * evTotal input := by
  unfold lenTotal evTotal
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => lenAt_le hv i

/-- **`lem:evfetch`**: `∑_λ EV(λ) ≤ ∑_λ fetch(λ) + ∑ wᵢ`, by telescoping `∑ᵢ wᵢ xᵢ` of the base state. -/
theorem evTotal_le : evTotal input ≤ fetchTotal input + input.totalWeight := by
  have h := Finset.sum_range_sub (fun i => baseMass input (snapAt input i))
    (log input).length
  rw [Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).2.2.2),
    Finset.sum_sub_distrib] at h
  have hN : baseMass input (snapAt input (log input).length) ≤ input.totalWeight := by
    unfold baseMass Instance.totalWeight
    apply Finset.sum_le_sum
    intro j _
    have := ((baseState_isRest hv (log input).length).1 j).2
    have := hv.weight_pos j
    nlinarith
  have h0 : 0 ≤ baseMass input (snapAt input 0) := by
    unfold baseMass
    apply Finset.sum_nonneg
    intro j _
    have := ((baseState_isRest hv 0).1 j).1
    have := hv.weight_pos j
    have := Instance.delta_pos hv
    nlinarith
  unfold evTotal fetchTotal
  linarith

/-- **`lem:lengthfetch`**: `∑_λ |λ| ≤ 3 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem lenTotal_le_fetchTotal : lenTotal input ≤ 3 * fetchTotal input + 3 * input.totalWeight := by
  have h2 := lenTotal_le hv
  have h3 := evTotal_le hv
  linarith

/-- The payments from the budgets are at most `3 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem holeTotal_add_tripTotal_le' :
    holeTotal input + tripTotal input ≤ 3 * fetchTotal input + 3 * input.totalWeight := by
  have h1 := holeTotal_add_tripTotal_le hv
  have h2 := lenTotal_le_fetchTotal hv
  linarith

/-! ### The fetch cost and the length of the output -/

/-- The fetch cost of `PMD` is at most the fetches of the critical services plus the payments for holes and round trips. -/
theorem fetchCost_le_preempt :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      fetchTotal input + holeTotal input + tripTotal input := by
  have hsum := sum_open_eq_close hv
  have hpay := Finset.sum_le_sum fun i (_ : i ∈ Finset.range (log input).length) =>
    openAt_le_holeAt hv i
  rw [fetchCost_output hv,
    Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).1)]
  simp only [Finset.sum_add_distrib]
  unfold fetchTotal holeTotal tripTotal
  linarith

/-- The fetch cost of `PMD` is at least the fetches of the critical services plus the costs of the round trips, i.e. of all visits (used in `prop:algdelay`). -/
theorem fetchTotal_add_tripTotal_le_fetchCost :
    fetchTotal input + tripTotal input ≤
      FracSchedule.fetchCost input (preemptiveMirrorDescent input) := by
  have hclose := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (log input).length) =>
    closeAt_nonneg hv i
  rw [fetchCost_output hv,
    Finset.sum_congr rfl (fun i hi => (entry_spec hv i (Finset.mem_range.1 hi)).1)]
  simp only [Finset.sum_add_distrib]
  unfold fetchTotal tripTotal
  linarith

/-- **`prop:preemptfetch`**: the fetch cost of `PMD` is at most `∑_λ fetch(λ) + ∑_λ |λ|`. -/
theorem fetchCost_le_lenTotal :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      fetchTotal input + lenTotal input := by
  have h0 := fetchCost_le_preempt hv
  have h1 := holeTotal_add_tripTotal_le hv
  linarith

/-- **`prop:preemptfetch` + `lem:lengthfetch`**: the fetch cost of `PMD` is at most `4 ∑_λ fetch(λ) + 3 ∑ wᵢ`. -/
theorem fetchCost_le :
    FracSchedule.fetchCost input (preemptiveMirrorDescent input) ≤
      4 * fetchTotal input + 3 * input.totalWeight := by
  have h0 := fetchCost_le_preempt hv
  have h1 := holeTotal_add_tripTotal_le' hv
  linarith

end

end

end CostProof

end PMD

end PagingWithDelay
