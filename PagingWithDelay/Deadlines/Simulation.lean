import PagingWithDelay.Deadlines.Virtual
import PagingWithDelay.Deadlines.Detour
import PagingWithDelay.Rounding.Schedule

/-!
# The simulation

`simulation alg` runs `alg` on the virtual instance and follows its schedule in real time; a request not served by the end of its ramp (which costs `2 ∑ᵢ wᵢ` delay) gets a detour at its deadline.
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

namespace Deadlines

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

/-- `S'` serves `r` in `[vtime a_r, rampEnd r]`. -/
def Served (C₀ : Finset Page) (R : List (DeadlineRequest Page)) (S' : Schedule Page)
    (r : DeadlineRequest Page) : Prop :=
  ∃ x, vtime R r.arrival ≤ x ∧ x ≤ rampEnd R r ∧ Holds r.page x C₀ S'

/-- The requests that the virtual schedule `S'` does not serve by the end of their ramps. -/
noncomputable def unserved (I : DeadlineInstance Page) (S' : Schedule Page) :
    List (DeadlineRequest Page) :=
  I.requests.filter fun r =>
    @decide (¬ Served I.initialCache I.requests S' r) (Classical.propDecidable _)

/-- `S'` in real time, with detours for the unserved requests. -/
noncomputable def simulate (I : DeadlineInstance Page) (S' : Schedule Page) : Schedule Page :=
  detours I.initialCache (retime (realTime I.requests) S') (unserved I S')

/-- The deadline algorithm that simulates the delay algorithm `alg` in virtual time. -/
noncomputable def simulation (alg : RandAlgorithm Page) : DeadlineAlgorithm Page :=
  fun I => (alg (virtualInstance I)).map (simulate I)

variable {I : DeadlineInstance Page}

theorem mem_unserved {S' : Schedule Page} {r : DeadlineRequest Page} :
    r ∈ unserved I S' ↔ r ∈ I.requests ∧ ¬ Served I.initialCache I.requests S' r := by
  unfold unserved
  rw [List.mem_filter]
  exact and_congr_right fun _ =>
    ⟨@of_decide_eq_true _ (Classical.propDecidable _), @decide_eq_true _ (Classical.propDecidable _)⟩

theorem chrono_simulate {S' : Schedule Page} (hS' : Chrono S') : Chrono (simulate I S') :=
  chrono_detours (chrono_retime realTime_mono hS') _

/-! ## Feasibility and cost -/

/-- The simulated schedule of a feasible virtual schedule is feasible. -/
theorem simulate_feasible {S' : Schedule Page} (hF : S'.Feasible (virtualInstance I)) :
    I.Feasible (simulate I S') where
  chronological := chrono_simulate hF.chronological
  capacity := capacity_detours I.cacheSize_pos I.initialCache_card.le
    (capacity_retime hF.capacity) _
  serves r hr := by
    have hb := chrono_retime (realTime_mono (R := I.requests)) hF.chronological
    by_cases hs : Served I.initialCache I.requests S' r
    · obtain ⟨x, hx1, hx2, hH⟩ := hs
      refine ⟨realTime I.requests x, le_realTime hx1,
        realTime_le_iff.2 (hx2.trans (rampEnd_le hr)), ?_⟩
      rw [deadlineCachedAt_iff, idxCached_iff_holds (chrono_simulate hF.chronological)]
      exact holds_detours hb _ (holds_retime realTime_mono hH)
    · refine ⟨r.deadline, r.arrival_le_deadline, le_rfl, ?_⟩
      rw [deadlineCachedAt_iff, idxCached_iff_holds (chrono_simulate hF.chronological)]
      exact holds_detours_mem hb (mem_unserved.2 ⟨hr, hs⟩)

/-- An unserved request pays delay `2 ∑ᵢ wᵢ`. -/
theorem delay_of_not_served {S' : Schedule Page} (hF : S'.Feasible (virtualInstance I))
    {r : DeadlineRequest Page} (hr : r ∈ I.requests)
    (hns : ¬ Served I.initialCache I.requests S' r) :
    2 * I.totalWeight ≤ (virtualRequest I r).delay
      (S'.serviceTime (virtualInstance I) (virtualRequest I r) - (virtualRequest I r).arrival) := by
  obtain ⟨τ, hτ1, hτ2⟩ := hF.serves (virtualRequest I r) (List.mem_map_of_mem hr)
  have hst : rampEnd I.requests r ≤ S'.serviceTime (virtualInstance I) (virtualRequest I r) := by
    unfold Schedule.serviceTime
    refine le_csInf ⟨τ, hτ1, hτ2⟩ ?_
    rintro y ⟨hy1, hy2⟩
    by_contra hlt
    apply hns
    refine ⟨y, hy1, (not_le.1 hlt).le, ?_⟩
    rwa [cachedAt_iff, idxCached_iff_holds hF.chronological] at hy2
  rw [← virtualRequest_delay_rampEnd I r]
  exact (virtualRequest I r).delay_mono (by linarith)

/-- The simulated schedule costs at most as much as the virtual schedule. -/
theorem simulate_cost {S' : Schedule Page} (hF : S'.Feasible (virtualInstance I)) :
    I.cost (simulate I S') ≤ S'.cost (virtualInstance I) := by
  have hw : ∀ p, 0 ≤ I.weight p := fun p => (I.weight_pos p).le
  have h1 := cost_detours I.weight hw (C₀ := I.initialCache)
    (chrono_retime (realTime_mono (R := I.requests)) hF.chronological) (unserved I S')
  rw [costFrom_retime] at h1
  set g : DeadlineRequest Page → ℝ := fun r => (virtualRequest I r).delay
    (S'.serviceTime (virtualInstance I) (virtualRequest I r) - (virtualRequest I r).arrival)
  have hmap : ((virtualInstance I).requests.map fun ρ =>
      ρ.delay (S'.serviceTime (virtualInstance I) ρ - ρ.arrival)) = I.requests.map g := by
    simp only [virtualInstance, List.map_map]
    rfl
  have h2 : ((unserved I S').length : ℝ) * (2 * I.totalWeight) ≤ (I.requests.map g).sum := by
    calc ((unserved I S').length : ℝ) * (2 * I.totalWeight)
        = ((unserved I S').map fun _ => 2 * I.totalWeight).sum := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ ≤ ((unserved I S').map g).sum := by
          apply List.sum_le_sum
          intro r hr
          obtain ⟨hr, hns⟩ := mem_unserved.1 hr
          exact delay_of_not_served hF hr hns
      _ ≤ (I.requests.map g).sum :=
          (List.filter_sublist.map g).sum_le_sum (by
            simp only [List.mem_map]
            rintro _ ⟨r, -, rfl⟩
            exact virtualRequest_delay_nonneg I r _)
  unfold DeadlineInstance.cost simulate
  unfold Schedule.cost Schedule.fetchCost
  rw [hmap]
  have : (∑ q, I.weight q) = I.totalWeight := rfl
  rw [this] at h1
  exact h1.trans (by
    show Schedule.costFrom I.weight I.initialCache S' + _ ≤
      Schedule.costFrom I.weight I.initialCache S' + _
    linarith)

/-! ## The comparator -/

/-- A feasible deadline schedule, moved to virtual time, is feasible for the virtual instance. -/
theorem opt_feasible {S : Schedule Page} (hS : I.Feasible S) :
    (retime (vtime I.requests) S).Feasible (virtualInstance I) where
  chronological := chrono_retime vtime_mono hS.chronological
  capacity := capacity_retime hS.capacity
  serves ρ hρ := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hρ
    obtain ⟨s, hs1, -, hs3⟩ := hS.serves r hr
    refine ⟨vtime I.requests s, vtime_mono hs1, ?_⟩
    rw [cachedAt_iff, idxCached_iff_holds (chrono_retime vtime_mono hS.chronological)]
    rw [deadlineCachedAt_iff, idxCached_iff_holds hS.chronological] at hs3
    exact holds_retime vtime_mono hs3

/-- A feasible deadline schedule, in virtual time, pays no delay. -/
theorem opt_cost {S : Schedule Page} (hS : I.Feasible S) :
    (retime (vtime I.requests) S).cost (virtualInstance I) = I.cost S := by
  unfold Schedule.cost Schedule.fetchCost DeadlineInstance.cost
  rw [List.sum_eq_zero, add_zero]
  · exact costFrom_retime _ _ _ _
  intro x hx
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hρ
  obtain ⟨s, hs1, hs2, hs3⟩ := hS.serves r hr
  apply virtualRequest_delay_eq_zero
  have hc : Schedule.CachedAt (virtualInstance I) (retime (vtime I.requests) S) r.page
      (vtime I.requests s) := by
    rw [cachedAt_iff, idxCached_iff_holds (chrono_retime vtime_mono hS.chronological)]
    rw [deadlineCachedAt_iff, idxCached_iff_holds hS.chronological] at hs3
    exact holds_retime vtime_mono hs3
  have h1 := Schedule.serviceTime_le (ρ := virtualRequest I r) (vtime_mono hs1) hc
  have h2 := vtime_deadline_le (R := I.requests) (r := r)
  have h3 := vtime_mono (R := I.requests) hs2
  show _ - vtime I.requests r.arrival ≤ start I.requests r
  linarith

/-! ## Online -/

/-- Up to `t`, the simulated schedule depends only on `I.upTo t` and `S'.upTo (vtimeR t)`. -/
theorem simulate_upTo {S' : Schedule Page} (hS' : Chrono S') (t : ℝ) :
    (simulate I S').upTo t =
      (simulate (I.upTo t) (S'.upTo (vtimeR (I.upTo t).requests t))).upTo t := by
  set R := I.requests
  set v := vtimeR (I.upTo t).requests t
  have hv : v = vtimeR R t := by simp only [v, upTo_requests, vtimeR_upTo le_rfl, R]
  unfold simulate
  rw [upTo_detours, upTo_detours]
  have hbase : (retime (realTime R) S').upTo t =
      (retime (realTime (I.upTo t).requests) (S'.upTo v)).upTo t := by
    have hA : (retime (realTime R) S').upTo t = retime (realTime R) (S'.upTo v) := by
      unfold retime Schedule.upTo
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro st _
      simp only [Function.comp]
      rw [hv]
      exact decide_eq_decide.2 realTime_le_iff
    have hB : (retime (realTime (I.upTo t).requests) (S'.upTo v)).upTo t =
        retime (realTime R) (S'.upTo v) := by
      have hagree : ∀ st ∈ S'.upTo v, realTime (I.upTo t).requests st.time = realTime R st.time := by
        intro st hst
        have : st.time ≤ v := by simpa using (List.mem_filter.1 hst).2
        rw [upTo_requests]
        exact realTime_upTo (hv ▸ this)
      unfold Schedule.upTo
      rw [List.filter_eq_self.2]
      · unfold retime
        apply List.map_congr_left
        intro st hst
        rw [hagree st hst]
      · intro st hst
        obtain ⟨st', hst', rfl⟩ := List.mem_map.1 hst
        have : st'.time ≤ v := by simpa using (List.mem_filter.1 hst').2
        simp only [decide_eq_true_eq]
        exact realTime_le_iff.2 this
    rw [hA, hB]
  have hlist : (unserved I S').filter (fun r => decide (r.deadline ≤ t)) =
      (unserved (I.upTo t) (S'.upTo v)).filter (fun r => decide (r.deadline ≤ t)) := by
    unfold unserved
    rw [List.filter_filter, List.filter_filter, upTo_requests, List.filter_filter]
    apply List.filter_congr
    intro r hrR
    by_cases hD : r.deadline ≤ t
    · have ha : r.arrival ≤ t := r.arrival_le_deadline.trans hD
      have hserv : Served (I.upTo t).initialCache (I.requests.filter fun r => decide (r.arrival ≤ t)) (S'.upTo v) r ↔
          Served I.initialCache R S' r := by
        unfold Served
        rw [vtime_upTo ha, rampEnd_upTo ha]
        apply exists_congr
        intro x
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, (holds_upTo hS' (h2.trans ((rampEnd_le hrR).trans
            (hv ▸ vtimeR_mono hD)))).1 h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, (holds_upTo hS' (h2.trans ((rampEnd_le hrR).trans
            (hv ▸ vtimeR_mono hD)))).2 h3⟩
      simp only [hD, ha, decide_true, Bool.true_and, Bool.and_true]
      exact decide_eq_decide.2 (not_congr hserv.symm)
    · simp [hD]
  rw [hbase, hlist]
  rfl

theorem pmf_map_congr {α β : Type*} (p : PMF α) {f g : α → β} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  ext b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(PMF.apply_eq_zero_iff p a).2 ha]
    simp

theorem simulation_online (alg : RandAlgorithm Page) (hon : alg.Online) (hfeas : alg.Feasible) :
    (simulation alg).Online := by
  have key : ∀ (K : DeadlineInstance Page) (t : ℝ),
      ((simulation alg) K).map (Schedule.upTo · t) =
        ((alg (virtualInstance K)).map (Schedule.upTo · (vtimeR (K.upTo t).requests t))).map
          (fun S'' => (simulate (K.upTo t) S'').upTo t) := by
    intro K t
    simp only [simulation, PMF.map_comp]
    apply pmf_map_congr
    intro S' hS'
    exact simulate_upTo (hfeas _ S' hS').chronological t
  intro I J t h
  rw [key I t, key J t, h]
  congr 1
  apply hon
  have h1 := virtualInstance_upTo I t
  have h2 := virtualInstance_upTo J t
  rw [h] at h1
  rw [h1, h2]

theorem simulation_feasible (alg : RandAlgorithm Page) (hfeas : alg.Feasible) :
    (simulation alg).Feasible := by
  intro I S hS
  rw [simulation, PMF.support_map] at hS
  obtain ⟨S', hS', rfl⟩ := hS
  exact simulate_feasible (hfeas _ S' hS')

theorem simulation_expectedCost (alg : RandAlgorithm Page) (hfeas : alg.Feasible)
    (I : DeadlineInstance Page) :
    (simulation alg).expectedCost I ≤ alg.expectedCost (virtualInstance I) := by
  unfold DeadlineAlgorithm.expectedCost RandAlgorithm.expectedCost simulation
  rw [Rounding.tsum_map_mul]
  refine ENNReal.tsum_le_tsum fun S' => ?_
  by_cases h : S' ∈ (alg (virtualInstance I)).support
  · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (simulate_cost (hfeas _ S' h))) _
  · rw [(PMF.apply_eq_zero_iff _ _).2 h, zero_mul, zero_mul]

/-- **The reduction**: a competitive online algorithm for paging with delay gives one for paging with deadlines with the same bound. -/
theorem simulation_competitive (alg : RandAlgorithm Page) (hon : alg.Online)
    (hfeas : alg.Feasible) (α β : ℕ → ℝ)
    (hcost : ∀ (input : Instance Page) (S : Schedule Page), S.Feasible input →
      alg.expectedCost input ≤
        ENNReal.ofReal (α input.cacheSize * S.cost input + β input.cacheSize * input.totalWeight)) :
    (simulation alg).Online ∧ (simulation alg).Feasible ∧
      ∀ (input : DeadlineInstance Page) (S : Schedule Page), input.Feasible S →
        (simulation alg).expectedCost input ≤
          ENNReal.ofReal (α input.cacheSize * input.cost S +
            β input.cacheSize * input.totalWeight) := by
  refine ⟨simulation_online alg hon hfeas, simulation_feasible alg hfeas, ?_⟩
  intro I S hS
  calc (simulation alg).expectedCost I ≤ alg.expectedCost (virtualInstance I) :=
        simulation_expectedCost alg hfeas I
    _ ≤ _ := hcost _ _ (opt_feasible hS)
    _ = _ := by rw [opt_cost hS]; rfl

end Deadlines

end PagingWithDelay
