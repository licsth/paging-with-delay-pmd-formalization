import PagingWithDelay.Fractional

/-!
# Costs of concatenated paths

`pathFrom d y W` is the cost of the polygonal path from the state `y` through the waypoints of `W`, where `d a b` is the cost of the segment from `a` to `b`. It is additive under concatenation; the fractional fetch cost of a schedule is an instance.
-/

set_option linter.unusedSectionVars false

open scoped PagingWithDelay.InstanceNotation

namespace PagingWithDelay

namespace PMD

variable {Page : Type*} [Fintype Page]

/-- The segment cost of the fetch cost. -/
noncomputable def dFetch (input : Instance Page) (a b : Page → ℝ) : ℝ :=
  ∑ i, w i * max 0 (a i - b i)

theorem dFetch_self (input : Instance Page) (a : Page → ℝ) : dFetch input a a = 0 := by
  simp [dFetch]

/-- The cost of the path from `y` through the waypoints. -/
noncomputable def pathFrom (d : (Page → ℝ) → (Page → ℝ) → ℝ) :
    (Page → ℝ) → List (Waypoint Page) → ℝ
  | _, [] => 0
  | y, a :: rest => d y a.state + pathFrom d a.state rest

/-- The state at the end of the path from `y` through the waypoints. -/
def lastState : (Page → ℝ) → List (Waypoint Page) → Page → ℝ
  | y, [] => y
  | _, a :: rest => lastState a.state rest

@[simp] theorem pathFrom_nil (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ) :
    pathFrom d y [] = 0 := rfl

@[simp] theorem pathFrom_cons (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ)
    (a : Waypoint Page) (rest : List (Waypoint Page)) :
    pathFrom d y (a :: rest) = d y a.state + pathFrom d a.state rest := rfl

@[simp] theorem lastState_nil (y : Page → ℝ) : lastState y ([] : List (Waypoint Page)) = y := rfl

@[simp] theorem lastState_cons (y : Page → ℝ) (a : Waypoint Page) (rest : List (Waypoint Page)) :
    lastState y (a :: rest) = lastState a.state rest := rfl

theorem pathFrom_append (d : (Page → ℝ) → (Page → ℝ) → ℝ) (y : Page → ℝ)
    (A B : List (Waypoint Page)) :
    pathFrom d y (A ++ B) = pathFrom d y A + pathFrom d (lastState y A) B := by
  induction A generalizing y with
  | nil => simp
  | cons a A ih => simp [ih]; ring

theorem lastState_append (y : Page → ℝ) (A B : List (Waypoint Page)) :
    lastState y (A ++ B) = lastState (lastState y A) B := by
  induction A generalizing y with
  | nil => simp
  | cons a A ih => simp [ih]

theorem fetchCost_eq_pathFrom (input : Instance Page) (a : Waypoint Page)
    (rest : List (Waypoint Page)) :
    FracSchedule.fetchCost input (a :: rest) = pathFrom (dFetch input) a.state rest := by
  induction rest generalizing a with
  | nil => simp [FracSchedule.fetchCost]
  | cons b rest ih => simp [FracSchedule.fetchCost, ih, dFetch]

theorem fetchCost_eq_pathFrom' (input : Instance Page) (y : Page → ℝ) (W : List (Waypoint Page))
    (hW : ∀ a ∈ W.head?, a.state = y) :
    FracSchedule.fetchCost input W = pathFrom (dFetch input) y W := by
  cases W with
  | nil => simp [FracSchedule.fetchCost]
  | cons a rest =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hW
    rw [fetchCost_eq_pathFrom, pathFrom_cons, hW, dFetch_self, zero_add]

end PMD

end PagingWithDelay
