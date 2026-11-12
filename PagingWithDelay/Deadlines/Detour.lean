import PagingWithDelay.Opt
import PagingWithDelay.Deadlines.Model

/-!
# Retiming schedules and inserting detours

`Holds` is a recursive form of `CachedAt` for chronological schedules (`idxCached_iff_holds`).
-/

set_option linter.unusedSectionVars false

namespace PagingWithDelay

namespace Deadlines

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

open Schedule.NF (lastCache Present idx_of_present present_of_idx costFrom_append)

/-- The steps of `S` are in chronological order. -/
def Chrono (S : Schedule Page) : Prop := S.Pairwise fun a b => a.time ≤ b.time

/-- Page `p` is cached at time `s` by the schedule `S` started from the cache `C` (for chronological `S`). -/
def Holds (p : Page) (s : ℝ) : Finset Page → Schedule Page → Prop
  | C, [] => p ∈ C
  | C, st :: rest => (s ≤ st.time ∧ p ∈ C) ∨ (st.time ≤ s ∧ Holds p s st.cache rest)

/-- `CachedAt` (of `Model.lean` and of `Deadlines/Model.lean`) with the initial cache `C₀`. -/
def IdxCached (C₀ : Finset Page) (S : Schedule Page) (p : Page) (s : ℝ) : Prop :=
  (p ∈ C₀ ∧ ∀ step ∈ S.head?, s ≤ step.time) ∨
    ∃ (j : ℕ) (h : j < S.length), S[j].time ≤ s ∧
      (∀ step ∈ S[j + 1]?, s ≤ step.time) ∧ p ∈ S[j].cache

theorem cachedAt_iff (input : Instance Page) (S : Schedule Page) (p : Page) (s : ℝ) :
    Schedule.CachedAt input S p s ↔ IdxCached input.initialCache S p s := Iff.rfl

theorem deadlineCachedAt_iff (input : DeadlineInstance Page) (S : Schedule Page) (p : Page)
    (s : ℝ) : input.CachedAt S p s ↔ IdxCached input.initialCache S p s := Iff.rfl

theorem holds_iff_present {p : Page} {s : ℝ} (C : Finset Page) (l : Schedule Page) :
    Holds p s C l ↔ ∃ X, Present s C l X ∧ p ∈ X := by
  induction l generalizing C with
  | nil => simp [Holds, Present]
  | cons st rest ih =>
    simp only [Holds, Present, ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, X, h2, h3⟩)
      · exact ⟨C, Or.inl ⟨h1, rfl⟩, h2⟩
      · exact ⟨X, Or.inr ⟨h1, h2⟩, h3⟩
    · rintro ⟨X, (⟨h1, rfl⟩ | ⟨h1, h2⟩), h3⟩
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h1, X, h2, h3⟩

theorem idxCached_iff_holds {C₀ : Finset Page} {S : Schedule Page} {p : Page} {s : ℝ}
    (hS : Chrono S) : IdxCached C₀ S p s ↔ Holds p s C₀ S := by
  rw [holds_iff_present]
  constructor
  · rintro (⟨hp, hh⟩ | ⟨j, hj, h1, h2, hp⟩)
    · exact ⟨C₀, present_of_idx C₀ S C₀ hS (Or.inl ⟨rfl, hh⟩), hp⟩
    · exact ⟨S[j].cache, present_of_idx C₀ S _ hS (Or.inr ⟨j, hj, h1, h2, rfl⟩), hp⟩
  · rintro ⟨X, hX, hp⟩
    rcases idx_of_present C₀ S X hX with ⟨rfl, hh⟩ | ⟨j, hj, h1, h2, rfl⟩
    · exact Or.inl ⟨hp, hh⟩
    · exact Or.inr ⟨j, hj, h1, h2, hp⟩

/-- If all steps of `B` come after `s`, a page cached at `s` is in the starting cache. -/
theorem mem_of_holds_of_lt {q : Page} {s : ℝ} {C : Finset Page} {B : Schedule Page}
    (hB : ∀ y ∈ B, s < y.time) (h : Holds q s C B) : q ∈ C := by
  cases B with
  | nil => exact h
  | cons y B =>
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · linarith [hB y List.mem_cons_self]

/-! ## Retiming -/

/-- Move every step from time `s` to time `f s`. -/
def retime (f : ℝ → ℝ) (S : Schedule Page) : Schedule Page :=
  S.map fun st => ⟨f st.time, st.cache⟩

theorem chrono_retime {f : ℝ → ℝ} (hf : Monotone f) {S : Schedule Page} (hS : Chrono S) :
    Chrono (retime f S) := by
  unfold Chrono retime
  rw [List.pairwise_map]
  exact hS.imp fun h => hf h

theorem holds_retime {f : ℝ → ℝ} (hf : Monotone f) {p : Page} {s : ℝ} {C : Finset Page}
    {S : Schedule Page} (h : Holds p s C S) : Holds p (f s) C (retime f S) := by
  induction S generalizing C with
  | nil => exact h
  | cons st rest ih =>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hf h1, h2⟩
    · exact Or.inr ⟨hf h1, ih h2⟩

theorem costFrom_retime (w : Page → ℝ) (f : ℝ → ℝ) (C : Finset Page) (S : Schedule Page) :
    Schedule.costFrom w C (retime f S) = Schedule.costFrom w C S := by
  induction S generalizing C with
  | nil => rfl
  | cons st rest ih => simp only [retime, List.map_cons, Schedule.costFrom] at ih ⊢; rw [ih]

theorem capacity_retime {k : ℕ} {f : ℝ → ℝ} {S : Schedule Page}
    (hS : ∀ st ∈ S, st.cache.card ≤ k) : ∀ st ∈ retime f S, st.cache.card ≤ k := by
  intro st hst
  obtain ⟨st', h1, rfl⟩ := List.mem_map.1 hst
  exact hS st' h1

/-! ## Truncation -/

theorem chrono_upTo {S : Schedule Page} (hS : Chrono S) (t : ℝ) : Chrono (S.upTo t) :=
  hS.sublist List.filter_sublist

theorem holds_upTo {S : Schedule Page} (hS : Chrono S) {p : Page} {x v : ℝ} (hx : x ≤ v)
    {C : Finset Page} : Holds p x C (S.upTo v) ↔ Holds p x C S := by
  induction S generalizing C with
  | nil => rfl
  | cons st rest ih =>
    rw [Chrono, List.pairwise_cons] at hS
    by_cases hst : st.time ≤ v
    · have : Schedule.upTo (st :: rest) v = st :: Schedule.upTo rest v := by
        simp [Schedule.upTo, hst]
      rw [this]
      simp only [Holds, ih hS.2]
    · have hnil : Schedule.upTo (st :: rest) v = [] := by
        rw [Schedule.upTo, List.filter_eq_nil_iff]
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · simpa using hst
        · have := hS.1 a ha
          simp only [decide_eq_true_eq]
          linarith
      rw [hnil]
      simp only [Holds]
      constructor
      · intro h; exact Or.inl ⟨by linarith, h⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h
        · linarith

/-! ## Detours -/

/-- At time `d`, fetch `p` and go back to the previous cache. -/
noncomputable def detour (C₀ : Finset Page) (S : Schedule Page) (d : ℝ) (p : Page) :
    Schedule Page :=
  S.upTo d ++ ⟨d, {p}⟩ :: ⟨d, lastCache C₀ (S.upTo d)⟩ :: S.filter fun st => decide (d < st.time)

theorem chrono_split {S : Schedule Page} (hS : Chrono S) (d : ℝ) :
    S.upTo d ++ S.filter (fun st => decide (d < st.time)) = S := by
  induction S with
  | nil => rfl
  | cons st rest ih =>
    rw [Chrono, List.pairwise_cons] at hS
    by_cases hst : st.time ≤ d
    · simp [Schedule.upTo, hst, not_lt.2 hst] at ih ⊢
      exact ih hS.2
    · have h1 : Schedule.upTo (st :: rest) d = [] := by
        rw [Schedule.upTo, List.filter_eq_nil_iff]
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · simpa using hst
        · have := hS.1 a ha
          simp only [decide_eq_true_eq]
          linarith
      have h2 : (st :: rest).filter (fun st => decide (d < st.time)) = st :: rest := by
        rw [List.filter_eq_self]
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · simpa using hst
        · have := hS.1 a ha
          simp only [decide_eq_true_eq]
          linarith
      rw [h1, h2]; rfl

theorem holds_insert {q : Page} {s d : ℝ} (X : Finset Page) (A B : Schedule Page)
    (C : Finset Page) (hA : ∀ x ∈ A, x.time ≤ d) (hB : ∀ y ∈ B, d ≤ y.time)
    (h : Holds q s C (A ++ B)) :
    Holds q s C (A ++ ⟨d, X⟩ :: ⟨d, lastCache C A⟩ :: B) := by
  induction A generalizing C with
  | nil =>
    simp only [List.nil_append, lastCache] at h ⊢
    rcases le_or_gt d s with hds | hsd
    · exact Or.inr ⟨hds, Or.inr ⟨hds, h⟩⟩
    · exact Or.inl ⟨hsd.le, mem_of_holds_of_lt (fun y hy => lt_of_lt_of_le hsd (hB y hy)) h⟩
  | cons a A ih =>
    simp only [List.cons_append] at h ⊢
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, ih a.cache (fun x hx => hA x (List.mem_cons_of_mem _ hx)) h2⟩

/-- A detour keeps every page cached that the schedule caches. -/
theorem holds_detour {S : Schedule Page} (hS : Chrono S) {C₀ : Finset Page} {q p : Page}
    {s d : ℝ} (h : Holds q s C₀ S) : Holds q s C₀ (detour C₀ S d p) := by
  rw [← chrono_split hS d] at h
  exact holds_insert _ _ _ _ (fun x hx => by simpa using (List.mem_filter.1 hx).2)
    (fun y hy => (by simpa using (List.mem_filter.1 hy).2 : d < y.time).le) h

/-- A detour to `p` at time `d` caches `p` at time `d`. -/
theorem holds_detour_self (C₀ : Finset Page) (S : Schedule Page) (d : ℝ) (p : Page) :
    Holds p d C₀ (detour C₀ S d p) := by
  have key : ∀ (A : Schedule Page) (C Y : Finset Page) (B : Schedule Page),
      (∀ x ∈ A, x.time ≤ d) → Holds p d C (A ++ ⟨d, {p}⟩ :: ⟨d, Y⟩ :: B) := by
    intro A
    induction A with
    | nil =>
      intro C Y B _
      exact Or.inr ⟨le_rfl, Or.inl ⟨le_rfl, Finset.mem_singleton_self p⟩⟩
    | cons a A ih =>
      intro C Y B hA
      exact Or.inr ⟨hA a List.mem_cons_self,
        ih a.cache Y B fun x hx => hA x (List.mem_cons_of_mem _ hx)⟩
  exact key _ _ _ _ fun x hx => by simpa using (List.mem_filter.1 hx).2

theorem chrono_detour {S : Schedule Page} (hS : Chrono S) (C₀ : Finset Page) (d : ℝ) (p : Page) :
    Chrono (detour C₀ S d p) := by
  unfold Chrono detour
  have hF : ∀ y ∈ S.filter (fun st => decide (d < st.time)), d < y.time :=
    fun y hy => by simpa using (List.mem_filter.1 hy).2
  have hU : ∀ x ∈ S.upTo d, x.time ≤ d := fun x hx => by simpa using (List.mem_filter.1 hx).2
  rw [List.pairwise_append]
  refine ⟨hS.sublist List.filter_sublist, ?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_cons]
    refine ⟨?_, ?_, hS.sublist List.filter_sublist⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_rfl
      · exact (hF y hy).le
    · intro y hy; exact (hF y hy).le
  · intro x hx y hy
    have := hU x hx
    rcases List.mem_cons.1 hy with rfl | hy
    · exact this
    rcases List.mem_cons.1 hy with rfl | hy
    · exact this
    · linarith [hF y hy]

theorem lastCache_card_le {k : ℕ} (C : Finset Page) (l : Schedule Page) (hC : C.card ≤ k)
    (hl : ∀ x ∈ l, x.cache.card ≤ k) : (lastCache C l).card ≤ k := by
  induction l generalizing C with
  | nil => exact hC
  | cons st rest ih =>
    exact ih st.cache (hl st List.mem_cons_self) (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem capacity_detour {k : ℕ} (hk : 0 < k) {C₀ : Finset Page} (hC₀ : C₀.card ≤ k)
    {S : Schedule Page} (hS : ∀ st ∈ S, st.cache.card ≤ k) (d : ℝ) (p : Page) :
    ∀ st ∈ detour C₀ S d p, st.cache.card ≤ k := by
  have hU : ∀ x ∈ S.upTo d, x.cache.card ≤ k := fun x hx => hS x (List.mem_filter.1 hx).1
  intro st hst
  simp only [detour, List.mem_append, List.mem_cons] at hst
  rcases hst with h | rfl | rfl | h
  · exact hU st h
  · simpa using hk
  · exact lastCache_card_le _ _ hC₀ hU
  · exact hS st (List.mem_filter.1 h).1

theorem cost_detour (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) {S : Schedule Page} (hS : Chrono S)
    (C₀ : Finset Page) (d : ℝ) (p : Page) :
    Schedule.costFrom w C₀ (detour C₀ S d p) ≤ Schedule.costFrom w C₀ S + 2 * ∑ q, w q := by
  conv_rhs => rw [← chrono_split hS d]
  unfold detour
  rw [costFrom_append, costFrom_append]
  simp only [Schedule.costFrom]
  have h1 : ∑ q ∈ {p} \ lastCache C₀ (S.upTo d), w q ≤ ∑ q, w q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => hw q
  have h2 : ∑ q ∈ lastCache C₀ (S.upTo d) \ {p}, w q ≤ ∑ q, w q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => hw q
  linarith

theorem upTo_detour (C₀ : Finset Page) (S : Schedule Page) (d : ℝ) (p : Page) (t : ℝ) :
    (detour C₀ S d p).upTo t = if d ≤ t then detour C₀ (S.upTo t) d p else S.upTo t := by
  split_ifs with hdt
  · have hA : (S.upTo t).upTo d = S.upTo d := by
      unfold Schedule.upTo
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases h : x.time ≤ d
      · simp [h, h.trans hdt]
      · simp [h]
    have hA' : (S.upTo d).upTo t = S.upTo d := by
      unfold Schedule.upTo
      rw [List.filter_eq_self]
      intro x hx
      have := (List.mem_filter.1 hx).2
      simp only [decide_eq_true_eq] at this ⊢
      linarith
    have hB : (S.filter fun st => decide (d < st.time)).filter (fun st => decide (st.time ≤ t)) =
        (S.upTo t).filter fun st => decide (d < st.time) := by
      unfold Schedule.upTo
      simp only [List.filter_filter, Bool.and_comm]
    unfold detour
    rw [hA]
    conv_lhs => rw [Schedule.upTo, List.filter_append]
    rw [← Schedule.upTo, hA', List.filter_cons_of_pos (by simpa using hdt),
      List.filter_cons_of_pos (by simpa using hdt), hB]
  · have hA : (S.upTo d).upTo t = S.upTo t := by
      unfold Schedule.upTo
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases h : x.time ≤ t
      · simp [h, h.trans (not_le.1 hdt).le]
      · simp [h]
    have hB : (S.filter fun st => decide (d < st.time)).filter (fun st => decide (st.time ≤ t)) =
        [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := (List.mem_filter.1 hx).2
      simp only [decide_eq_true_eq] at this ⊢
      linarith [not_le.1 hdt]
    unfold detour
    conv_lhs => rw [Schedule.upTo, List.filter_append]
    rw [← Schedule.upTo, hA, List.filter_cons_of_neg (by simpa using hdt),
      List.filter_cons_of_neg (by simpa using hdt), hB, List.append_nil]

/-! ## Detours for a list of requests -/

/-- Insert the detours to the pages of the requests in `L`, each at its deadline. -/
noncomputable def detours (C₀ : Finset Page) (base : Schedule Page)
    (L : List (DeadlineRequest Page)) : Schedule Page :=
  L.foldr (fun r S => detour C₀ S r.deadline r.page) base

theorem chrono_detours {C₀ : Finset Page} {base : Schedule Page} (hb : Chrono base)
    (L : List (DeadlineRequest Page)) : Chrono (detours C₀ base L) := by
  induction L with
  | nil => exact hb
  | cons r L ih => exact chrono_detour ih _ _ _

theorem holds_detours {C₀ : Finset Page} {base : Schedule Page} (hb : Chrono base)
    (L : List (DeadlineRequest Page)) {q : Page} {s : ℝ} (h : Holds q s C₀ base) :
    Holds q s C₀ (detours C₀ base L) := by
  induction L with
  | nil => exact h
  | cons r L ih => exact holds_detour (chrono_detours hb L) ih

theorem holds_detours_mem {C₀ : Finset Page} {base : Schedule Page} (hb : Chrono base)
    {L : List (DeadlineRequest Page)} {r : DeadlineRequest Page} (hr : r ∈ L) :
    Holds r.page r.deadline C₀ (detours C₀ base L) := by
  induction L with
  | nil => simp at hr
  | cons r' L ih =>
    rcases List.mem_cons.1 hr with rfl | hr
    · exact holds_detour_self _ _ _ _
    · exact holds_detour (chrono_detours hb L) (ih hr)

theorem capacity_detours {k : ℕ} (hk : 0 < k) {C₀ : Finset Page} (hC₀ : C₀.card ≤ k)
    {base : Schedule Page} (hb : ∀ st ∈ base, st.cache.card ≤ k)
    (L : List (DeadlineRequest Page)) : ∀ st ∈ detours C₀ base L, st.cache.card ≤ k := by
  induction L with
  | nil => exact hb
  | cons r L ih => exact capacity_detour hk hC₀ ih _ _

theorem cost_detours (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) {C₀ : Finset Page}
    {base : Schedule Page} (hb : Chrono base) (L : List (DeadlineRequest Page)) :
    Schedule.costFrom w C₀ (detours C₀ base L) ≤
      Schedule.costFrom w C₀ base + L.length * (2 * ∑ q, w q) := by
  induction L with
  | nil => simp [detours]
  | cons r L ih =>
    have := cost_detour w hw (chrono_detours (C₀ := C₀) hb L) C₀ r.deadline r.page
    simp only [detours, List.foldr_cons, List.length_cons, Nat.cast_succ] at this ih ⊢
    linarith

theorem upTo_detours (C₀ : Finset Page) (base : Schedule Page) (L : List (DeadlineRequest Page))
    (t : ℝ) : (detours C₀ base L).upTo t =
      detours C₀ (base.upTo t) (L.filter fun r => decide (r.deadline ≤ t)) := by
  induction L with
  | nil => rfl
  | cons r L ih =>
    simp only [detours, List.foldr_cons] at ih ⊢
    rw [upTo_detour, ih]
    split_ifs with h
    · rw [List.filter_cons_of_pos (by simpa using h), List.foldr_cons]
    · rw [List.filter_cons_of_neg (by simpa using h)]

end Deadlines

end PagingWithDelay
