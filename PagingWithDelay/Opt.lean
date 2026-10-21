import PagingWithDelay.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The comparator (the lazy optimum of `sec:problem`)

The analysis compares against an arbitrary feasible schedule `S` with service times `σ`, which serves every request `ρ` in the window `[a_ρ, σ ρ]` (`FeasibleBy`). This file collects the facts about `S` that the analysis uses:
* the lazy optimum in swap form (`exists_swapForm`): `S` can be replaced, with the same windows and no larger fetch cost, by a schedule in which every step evicts one page and fetches another;
* its cache at a time (`cacheAt`), its evictions (`obs:evictions`), the lightest weights (`lem:lightest`), quiet windows, the last eviction of a page (the comparator side of `lem:miss` and `lem:chargeable`), and its periods;
* delay costs of groups of requests: `delayCostOn input σ I` is the delay cost of the requests with index in `I` (index sets, since requests may be duplicated in the list); pairwise disjoint groups sum to at most the total delay cost `totalDelay input σ`.
-/

namespace PagingWithDelay

variable {Page : Type*} [Fintype Page] [DecidableEq Page]

namespace Schedule

/-- `σ` assigns service times: the page of every request `ρ` is cached by `S` at time `σ ρ ≥ a_ρ`. The analysis holds for every such `σ`; the first service times are one choice (`serviceTimes_serviceTime`). -/
def ServiceTimes (input : Instance Page) (S : Schedule Page) (σ : Request Page → ℝ) : Prop :=
  ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ ∧ CachedAt input S ρ.page (σ ρ)

/-- The cost of `S` with service times `σ`: its fetch cost plus the delay cost `∑_ρ d_ρ(σ ρ - a_ρ)`. -/
noncomputable def costWith (input : Instance Page) (S : Schedule Page)
    (σ : Request Page → ℝ) : ℝ :=
  fetchCost input S + (input.requests.map fun ρ => ρ.delay (σ ρ - ρ.arrival)).sum

theorem cost_eq_costWith (input : Instance Page) (S : Schedule Page) :
    S.cost input = S.costWith input (S.serviceTime input) := rfl

/-- The times at which a page is cached form a closed set. -/
theorem isClosed_cachedAt (input : Instance Page) (S : Schedule Page) (p : Page) :
    IsClosed {s | CachedAt input S p s} := by
  have hopt : ∀ o : Option (Step Page), IsClosed {s : ℝ | ∀ step ∈ o, s ≤ step.time} := by
    intro o
    cases o with
    | none => simp
    | some st => simpa using isClosed_Iic (a := st.time)
  have h : {s | CachedAt input S p s} =
      ({s | p ∈ input.initialCache} ∩ {s | ∀ step ∈ S.head?, s ≤ step.time}) ∪
        ⋃ j : Fin S.length, ({s | S[j].time ≤ s} ∩ {s | ∀ step ∈ S[(j : ℕ) + 1]?, s ≤ step.time} ∩
          {s | p ∈ S[j].cache}) := by
    ext s
    simp only [CachedAt, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro (h | ⟨j, hj, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨j, hj⟩, ⟨h1, h2⟩, h3⟩
    · rintro (h | ⟨j, ⟨h1, h2⟩, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, j.2, h1, h2, h3⟩
  rw [h]
  refine IsClosed.union ((isClosed_const).inter (hopt _)) (isClosed_iUnion_of_finite fun j => ?_)
  exact ((isClosed_Ici).inter (hopt _)).inter isClosed_const

/-- The first service times of a feasible schedule are service times: the infimum is attained. -/
theorem serviceTimes_serviceTime {input : Instance Page} {S : Schedule Page}
    (hF : S.Feasible input) : S.ServiceTimes input (S.serviceTime input) := by
  intro ρ hρ
  have hne : {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ}.Nonempty := hF.serves ρ hρ
  have hcl : IsClosed {τ | ρ.arrival ≤ τ ∧ CachedAt input S ρ.page τ} :=
    (isClosed_Ici (a := ρ.arrival)).inter (isClosed_cachedAt input S ρ.page)
  exact hcl.csInf_mem hne ⟨ρ.arrival, fun _ h => h.1⟩

/-- A request is served no later than any time after its arrival at which its page is cached. -/
theorem serviceTime_le {input : Instance Page} {S : Schedule Page} {ρ : Request Page} {s : ℝ}
    (hs : ρ.arrival ≤ s) (hc : CachedAt input S ρ.page s) : S.serviceTime input ρ ≤ s :=
  csInf_le ⟨ρ.arrival, fun _ h => h.1⟩ ⟨hs, hc⟩

/-- A request is served after its arrival (if it is served at all). -/
theorem arrival_le_serviceTime {input : Instance Page} {S : Schedule Page} {ρ : Request Page}
    (hne : ∃ s, ρ.arrival ≤ s ∧ CachedAt input S ρ.page s) :
    ρ.arrival ≤ S.serviceTime input ρ :=
  le_csInf hne fun _ h => h.1

variable {input : Instance Page} {σ : Request Page → ℝ}

theorem ServiceTimes.arrival_le {S : Schedule Page} (hσ : S.ServiceTimes input σ) :
    ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ := fun ρ hρ => (hσ ρ hρ).1

/-! ## Serving within the windows `[a_ρ, σ ρ]` -/

/-- `S` is feasible and serves every request `ρ` in the window `[a_ρ, σ ρ]`: its page is cached at some time `s` with `a_ρ ≤ s ≤ σ ρ`. -/
structure FeasibleBy (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page) :
    Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  capacity : ∀ step ∈ S, step.cache.card ≤ input.cacheSize
  serves : ∀ ρ ∈ input.requests, ∃ s, ρ.arrival ≤ s ∧ s ≤ σ ρ ∧ CachedAt input S ρ.page s

/-- `S` has served `ρ` by time `t`: its page is cached at some time `s` with `a_ρ ≤ s ≤ σ ρ` and `s ≤ t`. -/
def ServedBy (input : Instance Page) (σ : Request Page → ℝ) (S : Schedule Page)
    (ρ : Request Page) (t : ℝ) : Prop :=
  ∃ s, ρ.arrival ≤ s ∧ s ≤ σ ρ ∧ s ≤ t ∧ CachedAt input S ρ.page s

/-- A feasible schedule with service times `σ` serves every request in its window `[a_ρ, σ ρ]`. -/
theorem Feasible.feasibleBy {S : Schedule Page} (hF : S.Feasible input)
    (hσ : S.ServiceTimes input σ) : S.FeasibleBy input σ where
  chronological := hF.chronological
  capacity := hF.capacity
  serves ρ hρ := ⟨σ ρ, (hσ ρ hρ).1, le_rfl, (hσ ρ hρ).2⟩

/-! ## The swap normal form: the construction -/

/-!
Given a feasible schedule `S`, we build `S'` along the steps of `S`, keeping a cache `C'` of exactly `k` pages that contains the current cache of `S`. At a step of `S` to the cache `C_new`, for each `p ∈ C_new \ C'` we evict some page of `C' \ C_new` and fetch `p` (a swap step at the same time). The facts are proved for recursive notions (`lastCache`, `Present`, `SwapFrom`) and then translated to the index-based ones.
-/

namespace NF

/-- The cache after the steps of `l`, starting from `C`. -/
def lastCache : Finset Page → Schedule Page → Finset Page
  | C, [] => C
  | _, st :: rest => lastCache st.cache rest

/-- `X` is a cache present at time `s` in the schedule `l` started from `C`. -/
def Present (s : ℝ) : Finset Page → Schedule Page → Finset Page → Prop
  | C, [], X => X = C
  | C, st :: rest, X => (s ≤ st.time ∧ X = C) ∨ (st.time ≤ s ∧ Present s st.cache rest X)

/-- Every step of `l` (started from `C`) is a swap. -/
def SwapFrom : Finset Page → Schedule Page → Prop
  | _, [] => True
  | C, st :: rest =>
      (∃ p q, p ∉ C ∧ q ∈ C ∧ st.cache = insert p (C.erase q)) ∧ SwapFrom st.cache rest

/-- One round: fetch the pages of `ps` one by one into `C`, each time evicting a page of `C \ Cnew`. -/
noncomputable def roundL (t : ℝ) (Cnew : Finset Page) : Finset Page → List Page → Schedule Page
  | _, [] => []
  | C, p :: ps =>
    if h : p ∉ C ∧ (C \ Cnew).Nonempty then
      ⟨t, insert p (C.erase h.2.choose)⟩ :: roundL t Cnew (insert p (C.erase h.2.choose)) ps
    else roundL t Cnew C ps

/-- The round for the step `st` of `S`, from the cache `C` of `S'`. -/
noncomputable def round (st : Step Page) (C : Finset Page) : Schedule Page :=
  roundL st.time st.cache C (st.cache \ C).toList

/-- The swap-form schedule. -/
noncomputable def build : Finset Page → Schedule Page → Schedule Page
  | _, [] => []
  | C, st :: rest => round st C ++ build (lastCache C (round st C)) rest

/-! ### Generic facts -/

theorem costFrom_append (w : Page → ℝ) (C : Finset Page) (l₁ l₂ : Schedule Page) :
    costFrom w C (l₁ ++ l₂) = costFrom w C l₁ + costFrom w (lastCache C l₁) l₂ := by
  induction l₁ generalizing C with
  | nil => simp [costFrom, lastCache]
  | cons st rest ih => simp only [List.cons_append, costFrom, lastCache, ih]; ring

theorem swapFrom_append (C : Finset Page) (l₁ l₂ : Schedule Page) :
    SwapFrom C (l₁ ++ l₂) ↔ SwapFrom C l₁ ∧ SwapFrom (lastCache C l₁) l₂ := by
  induction l₁ generalizing C with
  | nil => simp [SwapFrom, lastCache]
  | cons st rest ih => simp only [List.cons_append, SwapFrom, lastCache, ih, and_assoc]

theorem lastCache_card (n : ℕ) (C : Finset Page) (l : Schedule Page) (hC : C.card = n)
    (hl : ∀ x ∈ l, x.cache.card = n) : (lastCache C l).card = n := by
  induction l generalizing C with
  | nil => exact hC
  | cons st rest ih =>
    exact ih st.cache (hl st (by simp)) (fun x hx => hl x (by simp [hx]))

theorem present_self {s : ℝ} (C : Finset Page) (l : Schedule Page)
    (h : ∀ st ∈ l, s ≤ st.time) : Present s C l C := by
  cases l with
  | nil => rfl
  | cons st rest => exact Or.inl ⟨h st (by simp), rfl⟩

theorem present_append {s : ℝ} (C : Finset Page) (l₁ l₂ : Schedule Page) (X : Finset Page)
    (h₁ : ∀ st ∈ l₁, st.time ≤ s) (h : Present s (lastCache C l₁) l₂ X) :
    Present s C (l₁ ++ l₂) X := by
  induction l₁ generalizing C with
  | nil => exact h
  | cons st rest ih =>
    exact Or.inr ⟨h₁ st (by simp), ih st.cache (fun x hx => h₁ x (by simp [hx])) h⟩

theorem idx_of_present {s : ℝ} (C : Finset Page) (l : Schedule Page) (X : Finset Page)
    (h : Present s C l X) :
    (X = C ∧ ∀ st ∈ l.head?, s ≤ st.time) ∨
      ∃ (j : ℕ) (hj : j < l.length), l[j].time ≤ s ∧ (∀ st ∈ l[j + 1]?, s ≤ st.time) ∧
        X = l[j].cache := by
  induction l generalizing C with
  | nil => left; exact ⟨h, by simp⟩
  | cons st rest ih =>
    rcases h with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · left; exact ⟨rfl, by simpa using h1⟩
    · rcases ih st.cache h2 with ⟨rfl, h3⟩ | ⟨j, hj, h3, h4, rfl⟩
      · right
        refine ⟨0, by simp, h1, ?_, rfl⟩
        intro x hx
        apply h3
        cases rest with
        | nil => simp at hx
        | cons y ys => simpa using hx
      · right
        exact ⟨j + 1, by simp; omega, by simpa using h3, by simpa using h4, by simp⟩

theorem present_of_idx {s : ℝ} (C : Finset Page) (l : Schedule Page) (X : Finset Page)
    (hc : l.Pairwise fun a b => a.time ≤ b.time)
    (h : (X = C ∧ ∀ st ∈ l.head?, s ≤ st.time) ∨
      ∃ (j : ℕ) (hj : j < l.length), l[j].time ≤ s ∧ (∀ st ∈ l[j + 1]?, s ≤ st.time) ∧
        X = l[j].cache) :
    Present s C l X := by
  induction l generalizing C with
  | nil =>
    rcases h with ⟨rfl, -⟩ | ⟨j, hj, -⟩
    · rfl
    · simp at hj
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    rcases h with ⟨rfl, h1⟩ | ⟨j, hj, h1, h2, rfl⟩
    · exact Or.inl ⟨h1 st rfl, rfl⟩
    · cases j with
      | zero =>
        refine Or.inr ⟨by simpa using h1, ih st.cache hc.2 (Or.inl ⟨by simp, ?_⟩)⟩
        intro x hx
        apply h2
        cases rest with
        | nil => simp at hx
        | cons y ys => simpa using hx
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        refine Or.inr ⟨?_, ih st.cache hc.2
          (Or.inr ⟨j, hj', by simpa using h1, by simpa using h2, by simp⟩)⟩
        exact le_trans (hc.1 _ (List.getElem_mem hj')) (by simpa using h1)

theorem pairwise_of_const (t : ℝ) (l : Schedule Page) (h : ∀ x ∈ l, x.time = t) :
    l.Pairwise fun a b => a.time ≤ b.time := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih fun y hy => h y (by simp [hy])⟩
    rw [h x (by simp), h y (by simp [hy])]

theorem swap_card {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    (insert p (C.erase q)).card = C.card := by
  have hp' : p ∉ C.erase q := fun h => hp (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hp', Finset.card_erase_of_mem hq]
  have : 0 < C.card := Finset.card_pos.2 ⟨q, hq⟩
  omega

/-! ### Rounds -/

section Round

variable (t : ℝ) (Cnew : Finset Page)

theorem roundL_time (C : Finset Page) (ps : List Page) :
    ∀ x ∈ roundL t Cnew C ps, x.time = t := by
  induction ps generalizing C with
  | nil => simp [roundL]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact ih _ x hx
    · exact ih C

theorem roundL_card (C : Finset Page) (ps : List Page) :
    ∀ x ∈ roundL t Cnew C ps, x.cache.card = C.card := by
  induction ps generalizing C with
  | nil => simp [roundL]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · have hq := (Finset.mem_sdiff.1 h.2.choose_spec).1
      have hc := swap_card h.1 hq
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc
      · rw [ih _ x hx, hc]
    · exact ih C

theorem roundL_swap (C : Finset Page) (ps : List Page) :
    SwapFrom C (roundL t Cnew C ps) := by
  induction ps generalizing C with
  | nil => simp [roundL, SwapFrom]
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · exact ⟨⟨p, _, h.1, (Finset.mem_sdiff.1 h.2.choose_spec).1, rfl⟩, ih _⟩
    · exact ih C

theorem roundL_last (C : Finset Page) (ps : List Page) (hk : Cnew.card ≤ C.card)
    (hsub : ∀ x ∈ Cnew, x ∈ C ∨ x ∈ ps) :
    Cnew ⊆ lastCache C (roundL t Cnew C ps) := by
  induction ps generalizing C with
  | nil =>
    intro x hx
    rcases hsub x hx with h | h
    · exact h
    · simp at h
  | cons p ps ih =>
    simp only [roundL]
    split_ifs with h
    · have hq := Finset.mem_sdiff.1 h.2.choose_spec
      apply ih
      · rw [swap_card h.1 hq.1]; exact hk
      · intro x hx
        rcases hsub x hx with hxC | hxp
        · left
          apply Finset.mem_insert_of_mem
          refine Finset.mem_erase.2 ⟨?_, hxC⟩
          rintro rfl; exact hq.2 hx
        · rcases List.mem_cons.1 hxp with rfl | hxp
          · left; exact Finset.mem_insert_self _ _
          · right; exact hxp
    · apply ih C hk
      intro x hx
      rcases hsub x hx with hxC | hxp
      · left; exact hxC
      · rcases List.mem_cons.1 hxp with rfl | hxp
        · left
          by_cases hpC : x ∈ C
          · exact hpC
          · exfalso
            have hne : ¬ (C \ Cnew).Nonempty := fun hn => h ⟨hpC, hn⟩
            rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
            have := Finset.eq_of_subset_of_card_le hne hk
            exact hpC (this ▸ hx)
        · right; exact hxp

theorem roundL_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (Cold : Finset Page)
    (C : Finset Page) (ps : List Page) (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∈ Cnew)
    (hinv : Cold ∩ Cnew ⊆ C) :
    costFrom w C (roundL t Cnew C ps) ≤ ∑ p ∈ ps.toFinset \ Cold, w p := by
  induction ps generalizing C with
  | nil => simp [roundL, costFrom]
  | cons p ps ih =>
    rw [List.nodup_cons] at hnd
    have hpN : p ∈ Cnew := hps p (by simp)
    have hps' : ∀ x ∈ ps, x ∈ Cnew := fun x hx => hps x (by simp [hx])
    have hsub : ps.toFinset \ Cold ⊆ (p :: ps).toFinset \ Cold :=
      Finset.sdiff_subset_sdiff (by intro x; simp; tauto) (Finset.Subset.refl _)
    simp only [roundL]
    split_ifs with h
    · have hq := Finset.mem_sdiff.1 h.2.choose_spec
      simp only [costFrom]
      have hpCold : p ∉ Cold := fun hc => h.1 (hinv (Finset.mem_inter.2 ⟨hc, hpN⟩))
      have h1 : ∑ x ∈ insert p (C.erase h.2.choose) \ C, w x ≤ w p := by
        calc ∑ x ∈ insert p (C.erase h.2.choose) \ C, w x ≤ ∑ x ∈ {p}, w x := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                rw [Finset.mem_sdiff, Finset.mem_insert] at hx
                rcases hx with ⟨rfl | hx, hxC⟩
                · simp
                · exact absurd (Finset.mem_of_mem_erase hx) hxC
              · intro x _ _; exact hw x
          _ = w p := by simp
      have h2 := ih (insert p (C.erase h.2.choose)) hnd.2 hps' (by
        intro x hx
        apply Finset.mem_insert_of_mem
        refine Finset.mem_erase.2 ⟨?_, hinv hx⟩
        rintro rfl; exact hq.2 (Finset.mem_inter.1 hx).2)
      have h3 : (p :: ps).toFinset \ Cold = insert p (ps.toFinset \ Cold) := by
        rw [List.toFinset_cons, Finset.insert_sdiff_of_notMem _ hpCold]
      rw [h3, Finset.sum_insert (by simp [hnd.1])]
      linarith
    · exact le_trans (ih C hnd.2 hps' hinv)
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x))

end Round

theorem round_time (st : Step Page) (C : Finset Page) : ∀ x ∈ round st C, x.time = st.time :=
  roundL_time _ _ _ _

theorem round_card (st : Step Page) (C : Finset Page) :
    ∀ x ∈ round st C, x.cache.card = C.card :=
  roundL_card _ _ _ _

theorem round_last (st : Step Page) (C : Finset Page) (hk : st.cache.card ≤ C.card) :
    st.cache ⊆ lastCache C (round st C) := by
  apply roundL_last _ _ _ _ hk
  intro x hx
  by_cases hxC : x ∈ C
  · left; exact hxC
  · right; simp [hx, hxC]

theorem round_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (Cold C : Finset Page) (st : Step Page)
    (hsub : Cold ⊆ C) : costFrom w C (round st C) ≤ ∑ p ∈ st.cache \ Cold, w p := by
  refine le_trans (roundL_cost _ _ w hw Cold C _ (Finset.nodup_toList _) ?_ ?_) ?_
  · intro p hp; exact (Finset.mem_sdiff.1 (Finset.mem_toList.1 hp)).1
  · exact fun x hx => hsub (Finset.mem_inter.1 hx).1
  · rw [Finset.toList_toFinset]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _)
    · intro x _ _; exact hw x

/-! ### The whole construction -/

theorem build_time (C : Finset Page) (S : Schedule Page) :
    ∀ x ∈ build C S, ∃ y ∈ S, x.time = y.time := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ⟨st, by simp, round_time st C x hx⟩
    · obtain ⟨y, hy, e⟩ := ih _ x hx
      exact ⟨y, by simp [hy], e⟩

theorem build_chrono (C : Finset Page) (S : Schedule Page)
    (hc : S.Pairwise fun a b => a.time ≤ b.time) :
    (build C S).Pairwise fun a b => a.time ≤ b.time := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    simp only [build]
    rw [List.pairwise_append]
    refine ⟨pairwise_of_const st.time _ (round_time st C), ih _ hc.2, ?_⟩
    intro a ha b hb
    obtain ⟨y, hy, e⟩ := build_time _ rest b hb
    rw [round_time st C a ha, e]
    exact hc.1 y hy

theorem build_card (k : ℕ) (C : Finset Page) (S : Schedule Page) (hC : C.card = k)
    (hcap : ∀ st ∈ S, st.cache.card ≤ k) : ∀ x ∈ build C S, x.cache.card = k := by
  induction S generalizing C with
  | nil => simp [build]
  | cons st rest ih =>
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [round_card st C x hx, hC]
    · refine ih _ ?_ (fun y hy => hcap y (by simp [hy])) x hx
      exact lastCache_card k C _ hC (fun y hy => by rw [round_card st C y hy, hC])

theorem build_swap (C : Finset Page) (S : Schedule Page) : SwapFrom C (build C S) := by
  induction S generalizing C with
  | nil => simp [build, SwapFrom]
  | cons st rest ih =>
    simp only [build]
    rw [swapFrom_append]
    exact ⟨roundL_swap _ _ _ _, ih _⟩

theorem build_cost (w : Page → ℝ) (hw : ∀ p, 0 ≤ w p) (k : ℕ) (C C' : Finset Page)
    (S : Schedule Page) (hsub : C ⊆ C') (hC : C'.card = k)
    (hcap : ∀ st ∈ S, st.cache.card ≤ k) :
    costFrom w C' (build C' S) ≤ costFrom w C S := by
  induction S generalizing C C' with
  | nil => simp [build, costFrom]
  | cons st rest ih =>
    simp only [build, costFrom]
    rw [costFrom_append]
    have h1 := round_cost w hw C C' st hsub
    have h2 := ih st.cache (lastCache C' (round st C'))
      (round_last st C' (by rw [hC]; exact hcap st (by simp)))
      (lastCache_card k C' _ hC (fun y hy => by rw [round_card st C' y hy, hC]))
      (fun y hy => hcap y (by simp [hy]))
    linarith

theorem build_present {s : ℝ} (k : ℕ) (C C' : Finset Page) (S : Schedule Page)
    (hsub : C ⊆ C') (hC : C'.card = k) (hcap : ∀ st ∈ S, st.cache.card ≤ k)
    (hc : S.Pairwise fun a b => a.time ≤ b.time) (X : Finset Page) (hX : Present s C S X) :
    ∃ Y, X ⊆ Y ∧ Present s C' (build C' S) Y := by
  induction S generalizing C C' with
  | nil => exact ⟨C', by rw [show X = C from hX]; exact hsub, rfl⟩
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    simp only [build]
    rcases hX with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · refine ⟨C', hsub, present_self _ _ ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [round_time st C' x hx]; exact h1
      · obtain ⟨y, hy, e⟩ := build_time _ rest x hx
        rw [e]; exact le_trans h1 (hc.1 y hy)
    · obtain ⟨Y, hXY, hY⟩ := ih st.cache (lastCache C' (round st C'))
        (round_last st C' (by rw [hC]; exact hcap st (by simp)))
        (lastCache_card k C' _ hC (fun y hy => by rw [round_card st C' y hy, hC]))
        (fun y hy => hcap y (by simp [hy])) hc.2 h2
      refine ⟨Y, hXY, present_append _ _ _ _ ?_ hY⟩
      intro x hx; rw [round_time st C' x hx]; exact h1

open scoped PagingWithDelay.InstanceNotation in
/-- The swap normal form, stated with the recursive notion `SwapFrom`. -/
theorem exists_swapFrom {input : Instance Page} (hv : input.Valid) {σ : Request Page → ℝ}
    {S : Schedule Page} (hS : S.FeasibleBy input σ) :
    ∃ S' : Schedule Page, S'.FeasibleBy input σ ∧ SwapFrom input.initialCache S' ∧
      S'.fetchCost input ≤ S.fetchCost input := by
  refine ⟨build input.initialCache S, ⟨build_chrono _ _ hS.chronological, ?_, ?_⟩,
    build_swap _ _, ?_⟩
  · intro st hst
    rw [build_card k _ S hv.initialCache_card hS.capacity st hst]
  · intro ρ hρ
    obtain ⟨s, h1, h2, h3⟩ := hS.serves ρ hρ
    have key : ∃ X, ρ.page ∈ X ∧ Present s input.initialCache S X := by
      rcases h3 with ⟨hp, h⟩ | ⟨j, hj, ha, hb, hp⟩
      · exact ⟨_, hp, present_of_idx _ _ _ hS.chronological (Or.inl ⟨rfl, h⟩)⟩
      · exact ⟨_, hp, present_of_idx _ _ _ hS.chronological (Or.inr ⟨j, hj, ha, hb, rfl⟩)⟩
    obtain ⟨X, hpX, hX⟩ := key
    obtain ⟨Y, hXY, hY⟩ := build_present k _ _ S (subset_refl _)
      hv.initialCache_card hS.capacity hS.chronological X hX
    refine ⟨s, h1, h2, ?_⟩
    rcases idx_of_present _ _ _ hY with ⟨rfl, h⟩ | ⟨j, hj, ha, hb, rfl⟩
    · exact Or.inl ⟨hXY hpX, h⟩
    · exact Or.inr ⟨j, hj, ha, hb, hXY hpX⟩
  · exact build_cost w (fun p => (hv.weight_pos p).le) k _ _ S
      (subset_refl _) hv.initialCache_card hS.capacity

end NF

/-! ## Caches, evictions and the lazy optimum -/

/-- The cache before step `j` (for `j ≤ length`, the cache after the first `j` steps). -/
def cacheBeforeStep (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  match j with
  | 0 => input.initialCache
  | j + 1 => (S[j]?.map Step.cache).getD input.initialCache

/-- The cache after all steps with time `≤ t` (for a chronological schedule). -/
noncomputable def cacheAt (input : Instance Page) (S : Schedule Page) (t : ℝ) : Finset Page :=
  cacheBeforeStep input S (S.filter fun step => decide (step.time ≤ t)).length

/-- Swap normal form: chronological, and every step evicts exactly one cached page and fetches exactly one page not cached. -/
structure SwapForm (input : Instance Page) (S : Schedule Page) : Prop where
  chronological : S.Pairwise fun earlier later => earlier.time ≤ later.time
  swap : ∀ (j : ℕ) (h : j < S.length), ∃ p q,
    p ∉ cacheBeforeStep input S j ∧ q ∈ cacheBeforeStep input S j ∧
      S[j].cache = insert p ((cacheBeforeStep input S j).erase q)

/-- The pages fetched at step `j`. -/
def fetchedAt (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  cacheBeforeStep input S (j + 1) \ cacheBeforeStep input S j

/-- The pages evicted at step `j`. -/
def evictedAt (input : Instance Page) (S : Schedule Page) (j : ℕ) : Finset Page :=
  cacheBeforeStep input S j \ cacheBeforeStep input S (j + 1)

/-- The distinct times of the steps. -/
noncomputable def stepTimes (S : Schedule Page) : Finset ℝ :=
  (S.map PagingWithDelay.Step.time).toFinset

/-! ### Helpers -/

/-- The cache before step `j`, from an arbitrary start cache `C`. -/
def cbs (C : Finset Page) (S : Schedule Page) : ℕ → Finset Page
  | 0 => C
  | j + 1 => (S[j]?.map Step.cache).getD C

theorem cacheBeforeStep_eq_cbs (S : Schedule Page) (j : ℕ) :
    cacheBeforeStep input S j = cbs input.initialCache S j := by
  cases j <;> rfl

theorem cbs_succ_of_lt (C : Finset Page) {S : Schedule Page} {j : ℕ} (h : j < S.length) :
    cbs C S (j + 1) = S[j].cache := by
  simp [cbs, List.getElem?_eq_getElem h]

theorem cbs_succ_of_le (C : Finset Page) {S : Schedule Page} {j : ℕ} (h : S.length ≤ j) :
    cbs C S (j + 1) = C := by
  simp [cbs, List.getElem?_eq_none h]

theorem cbs_cons (C : Finset Page) (st : Step Page) (rest : Schedule Page) {j : ℕ}
    (h : j ≤ rest.length) : cbs C (st :: rest) (j + 1) = cbs st.cache rest j := by
  cases j with
  | zero => simp [cbs]
  | succ j =>
    rw [cbs_succ_of_lt _ (by simp; omega), cbs_succ_of_lt _ (by omega)]
    simp

theorem cacheBeforeStep_succ_of_lt {S : Schedule Page} {j : ℕ} (h : j < S.length) :
    cacheBeforeStep input S (j + 1) = S[j].cache := by
  rw [cacheBeforeStep_eq_cbs, cbs_succ_of_lt _ h]

theorem cacheBeforeStep_succ_of_le {S : Schedule Page} {j : ℕ} (h : S.length ≤ j) :
    cacheBeforeStep input S (j + 1) = input.initialCache := by
  rw [cacheBeforeStep_eq_cbs, cbs_succ_of_le _ h]

theorem costFrom_eq_sum (w : Page → ℝ) (C : Finset Page) (S : Schedule Page) :
    costFrom w C S = ∑ j ∈ Finset.range S.length, ∑ p ∈ cbs C S (j + 1) \ cbs C S j, w p := by
  induction S generalizing C with
  | nil => simp [costFrom]
  | cons st rest ih =>
    rw [List.length_cons, Finset.sum_range_succ', costFrom, ih st.cache]
    have h0 : cbs C (st :: rest) (0 + 1) = st.cache := by simp [cbs]
    rw [h0, show cbs C (st :: rest) 0 = C from rfl, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [cbs_cons _ _ _ (by omega), cbs_cons _ _ _ (by omega)]

open scoped PagingWithDelay.InstanceNotation

theorem swapFrom_idx (C : Finset Page) (S : Schedule Page) (h : NF.SwapFrom C S) :
    ∀ (j : ℕ) (hj : j < S.length), ∃ p q, p ∉ cbs C S j ∧ q ∈ cbs C S j ∧
      S[j].cache = insert p ((cbs C S j).erase q) := by
  induction S generalizing C with
  | nil => intro j hj; simp at hj
  | cons st rest ih =>
    intro j hj
    cases j with
    | zero => exact h.1
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      rw [cbs_cons _ _ _ hj'.le]
      simpa using ih st.cache h.2 j hj'

/-- The number of steps with time `≤ t`. -/
noncomputable def numLE (S : Schedule Page) (t : ℝ) : ℕ :=
  (S.filter fun step => decide (step.time ≤ t)).length

theorem cacheAt_def (S : Schedule Page) (t : ℝ) :
    cacheAt input S t = cacheBeforeStep input S (numLE S t) := rfl

theorem numLE_le_length (S : Schedule Page) (t : ℝ) : numLE S t ≤ S.length :=
  List.length_filter_le _ _

theorem time_mono {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {i j : ℕ} (hij : i ≤ j) (hj : j < S.length) :
    S[i].time ≤ S[j].time := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.1 hc i j (by omega) hj hlt

theorem lt_numLE_iff {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} {i : ℕ} (hi : i < S.length) : i < numLE S t ↔ S[i].time ≤ t := by
  induction S generalizing i with
  | nil => simp at hi
  | cons st rest ih =>
    rw [List.pairwise_cons] at hc
    unfold numLE
    rw [List.filter_cons]
    by_cases hst : st.time ≤ t
    · simp only [hst, decide_true, if_true, List.length_cons]
      cases i with
      | zero => simpa using hst
      | succ i =>
        have hi' : i < rest.length := by simpa using hi
        have := ih hc.2 hi'
        unfold numLE at this
        simp only [List.getElem_cons_succ]
        exact Nat.succ_lt_succ_iff.trans this
    · simp only [hst, decide_false, Bool.false_eq_true, if_false]
      have hnil : rest.filter (fun step => decide (step.time ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := hc.1 a ha
        simp only [decide_eq_true_eq]
        linarith [not_le.1 hst]
      rw [hnil]
      simp only [List.length_nil, Nat.not_lt_zero, false_iff, not_le]
      cases i with
      | zero => simpa using not_le.1 hst
      | succ i =>
        have hi' : i < rest.length := by simpa using hi
        simp only [List.getElem_cons_succ]
        exact lt_of_lt_of_le (not_le.1 hst) (hc.1 _ (List.getElem_mem hi'))

theorem head_le {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time) {s : ℝ}
    (h : ∀ st ∈ S.head?, s ≤ st.time) {i : ℕ} (hi : i < S.length) : s ≤ S[i].time := by
  cases S with
  | nil => simp at hi
  | cons x xs =>
    have h0 : s ≤ x.time := h x rfl
    exact le_trans h0 (time_mono hc (Nat.zero_le i) hi)

theorem cacheAt_eq_initial {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} (h : ∀ st ∈ S.head?, t < st.time) : cacheAt input S t = input.initialCache := by
  rw [cacheAt_def]
  have : numLE S t = 0 := by
    by_contra hne
    have hpos : 0 < numLE S t := Nat.pos_of_ne_zero hne
    have h0 : 0 < S.length := lt_of_lt_of_le hpos (numLE_le_length S t)
    have h1 := (lt_numLE_iff hc h0).1 hpos
    cases S with
    | nil => simp at h0
    | cons x xs => exact absurd h1 (not_le.2 (h x rfl))
  rw [this]; rfl

theorem cacheAt_eq_of_last {S : Schedule Page} (hc : S.Pairwise fun a b => a.time ≤ b.time)
    {t : ℝ} {j : ℕ} (hj : j < S.length) (h1 : S[j].time ≤ t)
    (h2 : ∀ st ∈ S[j + 1]?, t < st.time) : cacheAt input S t = S[j].cache := by
  rw [cacheAt_def]
  have hn : numLE S t = j + 1 := by
    have ha := (lt_numLE_iff hc hj).2 h1
    have hb : numLE S t ≤ j + 1 := by
      by_contra hne
      push_neg at hne
      have hl : j + 1 < S.length := lt_of_lt_of_le hne (numLE_le_length S t)
      have := (lt_numLE_iff hc hl).1 hne
      exact absurd this (not_le.2 (h2 _ (List.getElem?_eq_getElem hl)))
    omega
  rw [hn, cacheBeforeStep_succ_of_lt hj]

theorem exists_last_evict {S : Schedule Page} {p : Page} {a b : ℕ} (hab : a ≤ b)
    (hp : p ∈ cacheBeforeStep input S a) (hp' : p ∉ cacheBeforeStep input S b) :
    ∃ i, a ≤ i ∧ i < b ∧ p ∈ evictedAt input S i ∧
      ∀ i', i < i' → i' < b → p ∉ evictedAt input S i' := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hp hp'
  | succ b hab ih =>
    by_cases hb : p ∈ cacheBeforeStep input S b
    · exact ⟨b, hab, by omega, Finset.mem_sdiff.2 ⟨hb, hp'⟩, fun i' h1 h2 => by omega⟩
    · obtain ⟨i, h1, h2, h3, h4⟩ := ih hb
      refine ⟨i, h1, by omega, h3, fun i' hi1 hi2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
      · exact h4 i' hi1 hi2
      · exact fun hmem => hb (Finset.mem_sdiff.1 hmem).1

theorem swap_sdiff_left {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    C \ insert p (C.erase q) = {q} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hne
    exact hn (Or.inr ⟨hne, hx⟩)
  · rintro rfl
    refine ⟨hq, fun h => h.elim (fun e => hp (e ▸ hq)) (fun h => h.1 rfl)⟩

theorem swap_sdiff_right {C : Finset Page} {p q : Page} (hp : p ∉ C) (hq : q ∈ C) :
    insert p (C.erase q) \ C = {p} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | ⟨-, hx⟩, hn⟩
    · exact hx
    · exact absurd hx hn
  · rintro rfl
    exact ⟨Or.inl rfl, hp⟩

theorem SwapForm.step {S : Schedule Page} (hS : SwapForm input S) {j : ℕ} (hj : j < S.length) :
    ∃ p q, p ∉ cacheBeforeStep input S j ∧ q ∈ cacheBeforeStep input S j ∧
      cacheBeforeStep input S (j + 1) = insert p ((cacheBeforeStep input S j).erase q) ∧
      fetchedAt input S j = {p} ∧ evictedAt input S j = {q} := by
  obtain ⟨p, q, hp, hq, he⟩ := hS.swap j hj
  have he' : cacheBeforeStep input S (j + 1) = insert p ((cacheBeforeStep input S j).erase q) := by
    rw [cacheBeforeStep_succ_of_lt hj, he]
  refine ⟨p, q, hp, hq, he', ?_, ?_⟩
  · unfold fetchedAt; rw [he', swap_sdiff_right hp hq]
  · unfold evictedAt; rw [he', swap_sdiff_left hp hq]

/-- The lazy optimum of `sec:problem`, in the stronger swap form: a feasible schedule with service times `σ` can be replaced by a swap-form schedule that serves every request `ρ` by `σ ρ`, at no larger fetch cost. -/
theorem exists_swapForm (hv : input.Valid) {S : Schedule Page} (hF : S.Feasible input)
    (hσ : S.ServiceTimes input σ) :
    ∃ S' : Schedule Page, S'.FeasibleBy input σ ∧ SwapForm input S' ∧
      S'.fetchCost input ≤ S.fetchCost input := by
  obtain ⟨S', hF', hsw, hc⟩ := NF.exists_swapFrom hv (hF.feasibleBy hσ)
  refine ⟨S', hF', ⟨hF'.chronological, fun j hj => ?_⟩, hc⟩
  simp only [cacheBeforeStep_eq_cbs]
  exact swapFrom_idx _ _ hsw j hj

section SwapForm

variable (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
include hv hS

theorem card_cacheBeforeStep (j : ℕ) : (cacheBeforeStep input S j).card = k := by
  induction j with
  | zero => exact hv.initialCache_card
  | succ j ih =>
    by_cases hj : j < S.length
    · obtain ⟨p, q, hp, hq, he, -, -⟩ := hS.step hj
      rw [he, NF.swap_card hp hq, ih]
    · rw [cacheBeforeStep_succ_of_le (not_lt.1 hj)]; exact hv.initialCache_card

/-- In swap form, the cache always holds exactly `k` pages. -/
theorem card_cacheAt (t : ℝ) : (cacheAt input S t).card = k := by
  exact card_cacheBeforeStep hv hS _

/-- The fetch cost is the total weight of the pages fetched at the steps. -/
theorem fetchCost_eq_sum_fetched :
    S.fetchCost input = ∑ j ∈ Finset.range S.length, ∑ p ∈ fetchedAt input S j, w p := by
  unfold fetchCost fetchedAt
  simp only [cacheBeforeStep_eq_cbs]
  exact costFrom_eq_sum _ _ _

/-- `obs:evictions`: the total weight of evictions is at most the fetch cost plus `w(C₀)`. -/
theorem sum_evicted_le :
    ∑ j ∈ Finset.range S.length, ∑ p ∈ evictedAt input S j, w p ≤
      S.fetchCost input + ∑ p ∈ input.initialCache, w p := by
  have hw : ∀ p, 0 ≤ w p := fun p => (hv.weight_pos p).le
  rw [fetchCost_eq_sum_fetched hv hS]
  have key : ∀ j, ∑ p ∈ evictedAt input S j, w p =
      ∑ p ∈ fetchedAt input S j, w p +
        (∑ p ∈ cacheBeforeStep input S j, w p -
          ∑ p ∈ cacheBeforeStep input S (j + 1), w p) := by
    intro j
    unfold evictedAt fetchedAt
    have := Finset.sum_sdiff_sub_sum_sdiff (s₁ := cacheBeforeStep input S (j + 1))
      (s₂ := cacheBeforeStep input S j) (f := w)
    linarith
  simp only [key, Finset.sum_add_distrib]
  have htel := Finset.sum_range_sub'
    (fun j => ∑ p ∈ cacheBeforeStep input S j, w p) S.length
  beta_reduce at htel
  have h0 : cacheBeforeStep input S 0 = input.initialCache := rfl
  rw [h0] at htel
  have : 0 ≤ ∑ p ∈ cacheBeforeStep input S S.length, w p :=
    Finset.sum_nonneg (fun p _ => hw p)
  linarith

/-- Between two times, a function of the cache changes by at most the sum of its changes at the steps in between. -/
theorem cacheAt_change (F : Finset Page → ℝ) (α β : ℝ)
    (hF : ∀ C p q, p ∉ C → q ∈ C →
      F (insert p (C.erase q)) - F C ≤ α * w q + β * w p)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    F (cacheAt input S t₂) - F (cacheAt input S t₁) ≤
      ∑ j ∈ (Finset.range S.length).filter
          (fun j => ∃ h : j < S.length, t₁ < S[j].time ∧ S[j].time ≤ t₂),
        (α * ∑ q ∈ evictedAt input S j, w q +
          β * ∑ p ∈ fetchedAt input S j, w p) := by
  have hc := hS.chronological
  have hlen := numLE_le_length S t₂
  have h12 : numLE S t₁ ≤ numLE S t₂ := by
    by_contra h
    push_neg at h
    have hl : numLE S t₂ < S.length := lt_of_lt_of_le h (numLE_le_length S t₁)
    have := (lt_numLE_iff hc hl).1 h
    exact absurd ((lt_numLE_iff hc hl).2 (le_trans this ht)) (lt_irrefl _)
  have hset : (Finset.range S.length).filter
      (fun j => ∃ h : j < S.length, t₁ < S[j].time ∧ S[j].time ≤ t₂) =
      Finset.Ico (numLE S t₁) (numLE S t₂) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hj, hj', h1, h2⟩
      exact ⟨not_lt.1 (fun h => absurd ((lt_numLE_iff hc hj).1 h) (not_le.2 h1)),
        (lt_numLE_iff hc hj).2 h2⟩
    · rintro ⟨h1, h2⟩
      have hj : j < S.length := by omega
      exact ⟨hj, hj, not_le.1 (fun h => absurd ((lt_numLE_iff hc hj).2 h) (by omega)),
        (lt_numLE_iff hc hj).1 h2⟩
  have htel := Finset.sum_Ico_sub (fun j => F (cacheBeforeStep input S j)) h12
  beta_reduce at htel
  rw [hset, cacheAt_def, cacheAt_def, ← htel]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨p, q, hp, hq, he, hfe, hev⟩ := hS.step (show j < S.length by omega)
  rw [hfe, hev, he, Finset.sum_singleton, Finset.sum_singleton]
  exact hF _ p q hp hq

/-- Before the first step, the cache is the initial cache. -/
theorem cacheAt_of_lt {t : ℝ} (ht : ∀ step ∈ S, t < step.time) :
    cacheAt input S t = input.initialCache := by
  rw [cacheAt_def]
  have : numLE S t = 0 := by
    unfold numLE
    have hnil : S.filter (fun step => decide (step.time ≤ t)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simpa using ht a ha
    rw [hnil]; rfl
  rw [this]; rfl

/-- If no step happens in `(t₁, t₂]`, the cache is the same at `t₁` and `t₂`. -/
theorem cacheAt_eq_of_quiet {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hq : ∀ step ∈ S, ¬ (t₁ < step.time ∧ step.time ≤ t₂)) :
    cacheAt input S t₁ = cacheAt input S t₂ := by
  have hfil : S.filter (fun step => decide (step.time ≤ t₁)) =
      S.filter (fun step => decide (step.time ≤ t₂)) := by
    apply List.filter_congr
    intro x hx
    simp only [decide_eq_decide]
    constructor
    · intro h; linarith
    · intro h; by_contra h'; exact hq x hx ⟨not_le.1 h', h⟩
  unfold cacheAt
  rw [hfil]

end SwapForm


/-! ## Quiet windows, last evictions and lightest weights -/

section

variable (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
  (hF : S.FeasibleBy input σ)
include hv hS hF

/-- A quiet window. If the page of `ρ` is not cached at `t ≤ σ ρ` and no step happens in `(t, σ ρ]`, then `S` has served `ρ` by `t`; in particular `a_ρ ≤ t`. -/
theorem servedBy_of_quiet {ρ : Request Page} (hρ : ρ ∈ input.requests) {t : ℝ}
    (ht : t ≤ σ ρ) (hq : ∀ step ∈ S, ¬ (t < step.time ∧ step.time ≤ σ ρ))
    (hp : ρ.page ∉ cacheAt input S t) : ServedBy input σ S ρ t := by
  have hc := hS.chronological
  obtain ⟨s, h1, h2, h3⟩ := hF.serves ρ hρ
  by_cases hst : s ≤ t
  · exact ⟨s, h1, h2, hst, h3⟩
  · exfalso
    have hst' : t < s := not_le.1 hst
    apply hp
    rcases h3 with ⟨hpC, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
    · rw [cacheAt_eq_initial hc (fun st hst => lt_of_lt_of_le hst' (hh st hst))]
      exact hpC
    · have hjt : S[j].time ≤ t := by
        by_contra hcon
        exact hq _ (List.getElem_mem hj) ⟨not_le.1 hcon, le_trans ha h2⟩
      rw [cacheAt_eq_of_last hc hj hjt (fun st hst => lt_of_lt_of_le hst' (hb st hst))]
      exact hpj

/-- The last eviction of `p` at a step with time `≤ t`. -/
def IsLastEviction (input : Instance Page) (S : Schedule Page) (p : Page) (t : ℝ) (j : ℕ) :
    Prop :=
  ∃ h : j < S.length, S[j].time ≤ t ∧ p ∈ evictedAt input S j ∧
    ∀ j' (h' : j' < S.length), j < j' → S[j'].time ≤ t → p ∉ evictedAt input S j'

/-- Charging to the last eviction (`lem:chargeable`). If `S` has served a request `π` on `p` by `t` but `p` is not cached at `t`, then `S` has evicted `p` at a step with time `≤ t`, and the last such eviction is at a time `≥ a_π`. -/
theorem exists_lastEviction {π : Request Page} {t : ℝ} (hπ : ServedBy input σ S π t)
    (hp : π.page ∉ cacheAt input S t) :
    ∃ j, IsLastEviction input S π.page t j ∧
      ∃ h : j < S.length, π.arrival ≤ S[j].time := by
  have hc := hS.chronological
  obtain ⟨s, h1, h2, h3, h4⟩ := hπ
  have hn := numLE_le_length S t
  rw [cacheAt_def] at hp
  rcases h4 with ⟨hpC, hh⟩ | ⟨j, hj, ha, hb, hpj⟩
  · obtain ⟨i, -, hi2, hi3, hi4⟩ :=
      exists_last_evict (input := input) (S := S) (a := 0) (Nat.zero_le _) hpC hp
    have hilen : i < S.length := by omega
    refine ⟨i, ⟨hilen, (lt_numLE_iff hc hilen).1 hi2, hi3, ?_⟩, hilen, ?_⟩
    · intro j' hj' hij ht'
      exact hi4 j' hij ((lt_numLE_iff hc hj').2 ht')
    · exact le_trans h1 (head_le hc hh hilen)
  · have hjn : j < numLE S t := (lt_numLE_iff hc hj).2 (le_trans ha h3)
    have hmem : π.page ∈ cacheBeforeStep input S (j + 1) := by
      rw [cacheBeforeStep_succ_of_lt hj]; exact hpj
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_last_evict (by omega) hmem hp
    have hilen : i < S.length := by omega
    refine ⟨i, ⟨hilen, (lt_numLE_iff hc hilen).1 hi2, hi3, ?_⟩, hilen, ?_⟩
    · intro j' hj' hij ht'
      exact hi4 j' hij ((lt_numLE_iff hc hj').2 ht')
    · have hj1 : j + 1 < S.length := by omega
      have := hb _ (List.getElem?_eq_getElem hj1)
      exact le_trans h1 (le_trans this (time_mono hc hi1 hilen))

/-- `lem:lightest` (lightest weights). If `m τ` is at most the weight of every page cached at the step time `τ`, then `∑_τ m τ` is at most the fetch cost of `S`. -/
theorem sum_stepTimes_le (m : ℝ → ℝ)
    (hm : ∀ τ ∈ stepTimes S, ∀ q ∈ cacheAt input S τ, m τ ≤ w q) :
    ∑ τ ∈ stepTimes S, m τ ≤ S.fetchCost input := by
  have hc := hS.chronological
  have hw : ∀ p, 0 ≤ w p := fun p => (hv.weight_pos p).le
  set g : ℝ → ℕ := fun τ => numLE S τ - 1 with hg
  have hA : ∀ τ ∈ stepTimes S, ∃ h : g τ < S.length, S[g τ].time = τ ∧ g τ + 1 = numLE S τ := by
    intro τ hτ
    unfold stepTimes at hτ
    rw [List.mem_toFinset, List.mem_map] at hτ
    obtain ⟨st, hst, rfl⟩ := hτ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hst
    have hin := (lt_numLE_iff hc hi (t := S[i].time)).2 le_rfl
    have hn := numLE_le_length S S[i].time
    have hgl : g S[i].time < S.length := by simp only [hg]; omega
    refine ⟨hgl, ?_, by simp only [hg]; omega⟩
    apply le_antisymm
    · exact (lt_numLE_iff hc hgl).1 (by simp only [hg]; omega)
    · exact time_mono hc (by simp only [hg]; omega) hgl
  have hinj : Set.InjOn g (stepTimes S : Set ℝ) := by
    intro τ hτ τ' hτ' heq
    obtain ⟨h1, e1, -⟩ := hA τ hτ
    obtain ⟨h2, e2, -⟩ := hA τ' hτ'
    rw [← e1, ← e2]
    simp only [heq]
  have hB : ∀ τ ∈ stepTimes S, m τ ≤ ∑ p ∈ fetchedAt input S (g τ), w p := by
    intro τ hτ
    obtain ⟨h1, e1, e2⟩ := hA τ hτ
    obtain ⟨p, q, hp, hq, he, hfe, hev⟩ := hS.step h1
    rw [hfe, Finset.sum_singleton]
    apply hm τ hτ
    rw [cacheAt_def, ← e2, he]
    exact Finset.mem_insert_self _ _
  rw [fetchCost_eq_sum_fetched hv hS]
  calc ∑ τ ∈ stepTimes S, m τ
      ≤ ∑ τ ∈ stepTimes S, ∑ p ∈ fetchedAt input S (g τ), w p :=
        Finset.sum_le_sum hB
    _ = ∑ j ∈ (stepTimes S).image g, ∑ p ∈ fetchedAt input S j, w p :=
        (Finset.sum_image (f := fun j => ∑ p ∈ fetchedAt input S j, w p) hinj).symm
    _ ≤ ∑ j ∈ Finset.range S.length, ∑ p ∈ fetchedAt input S j, w p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hj
          obtain ⟨h1, -, -⟩ := hA τ hτ
          exact Finset.mem_range.2 h1
        · intro j _ _
          exact Finset.sum_nonneg (fun p _ => hw p)

end


/-! ## Periods

A time `t` lies in the period of the step time `τ` if `τ` is the last step time `≤ t`. Every time after the first step lies in exactly one period, and the comparator's cache is constant on a period. -/

/-- `t` lies in the period starting at the step time `τ`. -/
def InPer (S : Schedule Page) (τ t : ℝ) : Prop :=
  τ ∈ stepTimes S ∧ τ ≤ t ∧ ∀ step ∈ S, ¬ (τ < step.time ∧ step.time ≤ t)

theorem mem_stepTimes {S : Schedule Page} {τ : ℝ} :
    τ ∈ stepTimes S ↔ ∃ step ∈ S, step.time = τ := by
  unfold stepTimes
  simp

theorem InPer.unique {S : Schedule Page} {τ τ' t : ℝ} (h : InPer S τ t) (h' : InPer S τ' t) :
    τ = τ' := by
  obtain ⟨hτ, hτt, hq⟩ := h
  obtain ⟨hτ', hτ't, hq'⟩ := h'
  obtain ⟨s, hs, rfl⟩ := mem_stepTimes.1 hτ
  obtain ⟨s', hs', rfl⟩ := mem_stepTimes.1 hτ'
  rcases lt_trichotomy s.time s'.time with hlt | heq | hgt
  · exact absurd ⟨hlt, hτ't⟩ (hq s' hs')
  · exact heq
  · exact absurd ⟨hgt, hτt⟩ (hq' s hs)

theorem InPer.exists_of_step {S : Schedule Page} {t : ℝ} (h : ∃ step ∈ S, step.time ≤ t) :
    ∃ τ, InPer S τ t := by
  have hne : ((stepTimes S).filter (· ≤ t)).Nonempty := by
    obtain ⟨s, hs, hst⟩ := h
    exact ⟨s.time, Finset.mem_filter.2 ⟨mem_stepTimes.2 ⟨s, hs, rfl⟩, hst⟩⟩
  have hm := Finset.max'_mem _ hne
  rw [Finset.mem_filter] at hm
  refine ⟨_, hm.1, hm.2, fun s hs ⟨h1, h2⟩ => ?_⟩
  have : s.time ∈ (stepTimes S).filter (· ≤ t) :=
    Finset.mem_filter.2 ⟨mem_stepTimes.2 ⟨s, hs, rfl⟩, h2⟩
  exact absurd (Finset.le_max' _ _ this) (not_le.2 h1)

theorem InPer.of_le {S : Schedule Page} {τ t₁ t₂ : ℝ} (h : InPer S τ t₂) (h₁ : τ ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) : InPer S τ t₁ :=
  ⟨h.1, h₁, fun s hs ⟨a, b⟩ => h.2.2 s hs ⟨a, b.trans h₁₂⟩⟩

theorem InPer.cacheAt_eq (hv : input.Valid) {S : Schedule Page} (hS : SwapForm input S)
    {τ t : ℝ} (h : InPer S τ t) : cacheAt input S t = cacheAt input S τ :=
  (cacheAt_eq_of_quiet hv hS h.2.1 h.2.2).symm


/-! ## Delay costs of groups of requests -/

/-- The delay cost `d_ρ(σ ρ - a_ρ)` of request `ρ`. -/
noncomputable def delayOf (σ : Request Page → ℝ) (ρ : Request Page) : ℝ :=
  ρ.delay (σ ρ - ρ.arrival)

/-- The delay cost of the requests with index in `I`. -/
noncomputable def delayCostOn (input : Instance Page) (σ : Request Page → ℝ)
    (I : Finset (Fin input.requests.length)) : ℝ :=
  ∑ i ∈ I, delayOf σ input.requests[i]

/-- The total delay cost `∑_ρ d_ρ(σ ρ - a_ρ)`. -/
noncomputable def totalDelay (input : Instance Page) (σ : Request Page → ℝ) : ℝ :=
  (input.requests.map fun ρ => ρ.delay (σ ρ - ρ.arrival)).sum

theorem costWith_eq (S : Schedule Page) :
    S.costWith input σ = S.fetchCost input + totalDelay input σ := rfl

theorem totalDelay_eq_delayCostOn_univ :
    totalDelay input σ = delayCostOn input σ Finset.univ := by
  unfold totalDelay delayCostOn delayOf
  exact (Fin.sum_univ_fun_getElem input.requests (fun ρ => ρ.delay (σ ρ - ρ.arrival))).symm

theorem delayOf_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    {ρ : Request Page} (hρ : ρ ∈ input.requests) : 0 ≤ delayOf σ ρ := by
  unfold delayOf
  rw [← hv.delay_zero ρ hρ]
  exact hv.delay_mono ρ hρ (by linarith [hσ ρ hρ])

theorem delayOf_getElem_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (i : Fin input.requests.length) : 0 ≤ delayOf σ input.requests[i] :=
  delayOf_nonneg hv hσ (List.getElem_mem _)

theorem delayCostOn_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    (I : Finset (Fin input.requests.length)) : 0 ≤ delayCostOn input σ I :=
  Finset.sum_nonneg fun i _ => delayOf_getElem_nonneg hv hσ i

theorem totalDelay_nonneg (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) :
    0 ≤ totalDelay input σ := by
  rw [totalDelay_eq_delayCostOn_univ]; exact delayCostOn_nonneg hv hσ _

theorem delayCostOn_mono (hv : input.Valid) (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ)
    {I J : Finset (Fin input.requests.length)} (h : I ⊆ J) :
    delayCostOn input σ I ≤ delayCostOn input σ J :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => delayOf_getElem_nonneg hv hσ i

theorem delayCostOn_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) (I : Finset (Fin input.requests.length)) :
    delayCostOn input σ I ≤ totalDelay input σ := by
  rw [totalDelay_eq_delayCostOn_univ]
  exact delayCostOn_mono hv hσ (Finset.subset_univ I)

/-- The delay costs of pairwise disjoint groups of requests (as index sets) sum to at most the total delay cost. -/
theorem sum_delayCostOn_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {ι : Type*} (G : Finset ι)
    (I : ι → Finset (Fin input.requests.length)) (hdisj : (G : Set ι).PairwiseDisjoint I) :
    ∑ g ∈ G, delayCostOn input σ (I g) ≤ totalDelay input σ := by
  classical
  unfold delayCostOn
  rw [← Finset.sum_biUnion hdisj]
  exact delayCostOn_le_totalDelay hv hσ _

/-- The form used by the charging arguments: if pairwise disjoint groups `g` of requests have delay cost at least `X g`, then `∑_g X g ≤ ∑_ρ d_ρ(σ ρ - a_ρ)`. -/
theorem sum_le_totalDelay (hv : input.Valid)
    (hσ : ∀ ρ ∈ input.requests, ρ.arrival ≤ σ ρ) {ι : Type*} (G : Finset ι)
    (I : ι → Finset (Fin input.requests.length)) (hdisj : (G : Set ι).PairwiseDisjoint I)
    (X : ι → ℝ) (hX : ∀ g ∈ G, X g ≤ delayCostOn input σ (I g)) :
    ∑ g ∈ G, X g ≤ totalDelay input σ :=
  (Finset.sum_le_sum hX).trans (sum_delayCostOn_le_totalDelay hv hσ G I hdisj)

/-! ## Delay lower bounds from not being served -/

section Served

variable {S : Schedule Page} (hF : S.FeasibleBy input σ)
include hF

/-- If `S` (serving every request `ρ` by `σ ρ`) has not served `ρ` by `t`, then `t < σ ρ`. -/
theorem lt_of_not_servedBy {ρ : Request Page} (hρ : ρ ∈ input.requests) {t : ℝ}
    (hn : ¬ ServedBy input σ S ρ t) : t < σ ρ := by
  by_contra hle
  push_neg at hle
  obtain ⟨s, h1, h2, h3⟩ := hF.serves ρ hρ
  exact hn ⟨s, h1, h2, le_trans h2 hle, h3⟩

/-- If `S` has not served `ρ` by `t`, the delay cost of `ρ` is at least `d_ρ(t - a_ρ)`. -/
theorem delay_le_of_not_servedBy (hv : input.Valid) {ρ : Request Page}
    (hρ : ρ ∈ input.requests) {t : ℝ}
    (hn : ¬ ServedBy input σ S ρ t) :
    ρ.delay (t - ρ.arrival) ≤ delayOf σ ρ :=
  hv.delay_mono ρ hρ (by linarith [lt_of_not_servedBy hF hρ hn])

/-- Index form of `delay_le_of_not_servedBy`. -/
theorem delay_le_of_not_servedBy' (hv : input.Valid) (i : Fin input.requests.length) {t : ℝ}
    (hn : ¬ ServedBy input σ S input.requests[i] t) :
    input.requests[i].delay (t - input.requests[i].arrival) ≤ delayOf σ input.requests[i] :=
  delay_le_of_not_servedBy hF hv (List.getElem_mem _) hn

end Served

end Schedule

end PagingWithDelay
