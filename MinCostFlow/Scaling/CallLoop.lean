module

public import MinCostFlow.Scaling.Circulation

/-!
# Explicit loops with circulation-call traces

The mathematical models of the Appendix C scaling loops record every solver
instance and count the other integer operations supplied by their bodies. This
file gives the finite sequential loop and its accounting lemmas. The counter
adds one operation per iteration for loop control. These counts are separate
from the word-RAM costs that implement each integer operation.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- A computation's returned data, explicit solver-call list, and other work. -/
structure CallResult (α : Type) where
  value : α
  calls : List Circulation
  work : ℕ

namespace CallResult

/-- Return data with no solver call or arithmetic work. -/
def pure {α : Type} (a : α) : CallResult α := ⟨a, [], 0⟩

/-- Invoke the integral circulation solver once and record its input instance. -/
def solve (solver : (I : Circulation) → Fin I.m → ℤ) (I : Circulation) :
    CallResult (Fin I.m → ℤ) := ⟨solver I, [I], 0⟩

/-- Run computations in order and concatenate their call lists. -/
def bind {α β : Type} (r : CallResult α) (next : α → CallResult β) : CallResult β :=
  let s := next r.value
  ⟨s.value, r.calls ++ s.calls, r.work + s.work⟩

/-- Charge an explicitly counted block of other integer operations. -/
def charge {α : Type} (r : CallResult α) (work : ℕ) : CallResult α :=
  { r with work := r.work + work }

/-- Perform exactly `rounds` iterations, passing the state between iterations. -/
def forRounds {α : Type} (step : α → CallResult α) : ℕ → α → CallResult α
  | 0, a => pure a
  | rounds + 1, a => (forRounds step rounds a).bind (fun b => (step b).charge 1)

/-- A finite loop makes at most the per-iteration bound times its length calls. -/
theorem forRounds_calls {α : Type} (step : α → CallResult α) (K : ℕ)
    (hstep : ∀ a, (step a).calls.length ≤ K) (rounds : ℕ) (a : α) :
    (forRounds step rounds a).calls.length ≤ rounds * K := by
  induction rounds with
  | zero => simp [forRounds, pure]
  | succ rounds ih =>
    simp only [forRounds, bind, charge, List.length_append]
    have hs := hstep (forRounds step rounds a).value
    calc
      (forRounds step rounds a).calls.length +
          (step (forRounds step rounds a).value).calls.length ≤ rounds * K + K :=
        Nat.add_le_add ih hs
      _ = (rounds + 1) * K := by rw [Nat.add_mul, Nat.one_mul]

/-- Every recorded instance inherits any instance bound satisfied by each body. -/
theorem forRounds_instances {α : Type} (step : α → CallResult α)
    (P : Circulation → Prop) (hstep : ∀ a, ∀ I ∈ (step a).calls, P I)
    (rounds : ℕ) (a : α) : ∀ I ∈ (forRounds step rounds a).calls, P I := by
  induction rounds with
  | zero => simp [forRounds, pure]
  | succ rounds ih =>
    intro I hI
    rcases List.mem_append.mp hI with h | h
    · exact ih I h
    · exact hstep _ I h

/-- Other work is bounded by the body's bound plus one control operation for
each iteration. The theorem concerns this explicit model's counter. -/
theorem forRounds_work {α : Type} (step : α → CallResult α) (B : ℕ)
    (hstep : ∀ a, (step a).work ≤ B) (rounds : ℕ) (a : α) :
    (forRounds step rounds a).work ≤ rounds * (B + 1) := by
  induction rounds with
  | zero => simp [forRounds, pure]
  | succ rounds ih =>
    simp only [forRounds, bind, charge]
    have hs := hstep (forRounds step rounds a).value
    calc
      (forRounds step rounds a).work + ((step (forRounds step rounds a).value).work + 1)
          ≤ rounds * (B + 1) + (B + 1) :=
        Nat.add_le_add ih (Nat.add_le_add_right hs 1)
      _ = (rounds + 1) * (B + 1) := by rw [Nat.add_mul, Nat.one_mul]

/-- A state invariant preserved by each body holds at the end of the finite loop. -/
theorem forRounds_invariant {α : Type} (step : α → CallResult α)
    (P : α → Prop) (hstep : ∀ a, P a → P (step a).value)
    (rounds : ℕ) (a : α) (ha : P a) : P (forRounds step rounds a).value := by
  induction rounds with
  | zero => exact ha
  | succ rounds ih => exact hstep _ ih

/-- Instance bounds may use an invariant of the states reached by the loop. -/
theorem forRounds_instances_of_invariant {α : Type} (step : α → CallResult α)
    (P : α → Prop) (hstep : ∀ a, P a → P (step a).value)
    (Q : Circulation → Prop) (hbody : ∀ a, P a → ∀ I ∈ (step a).calls, Q I)
    (rounds : ℕ) (a : α) (ha : P a) : ∀ I ∈ (forRounds step rounds a).calls, Q I := by
  induction rounds with
  | zero => simp [forRounds, pure]
  | succ rounds ih =>
    intro I hI
    rcases List.mem_append.mp hI with h | h
    · exact ih I h
    · exact hbody _ (forRounds_invariant step P hstep rounds a ha) I h

/-- The loop accounting assumptions have a concrete simultaneous example:
calling one fixed instance per iteration has one call and zero body overhead. -/
theorem solve_example (solver : (I : Circulation) → Fin I.m → ℤ)
    (I : Circulation) :
    (solve solver I).calls.length = 1 ∧ (solve solver I).work = 0 ∧
      ∀ J ∈ (solve solver I).calls, J.m = I.m := by
  refine ⟨rfl, rfl, ?_⟩
  intro J hJ
  have he : J = I := List.mem_singleton.mp hJ
  exact congrArg Circulation.m he

end CallResult
end MinCostFlow.Scaling
