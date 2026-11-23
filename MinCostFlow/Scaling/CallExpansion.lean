module

public import MinCostFlow.Scaling.CallLoop

/-!
# Substituting counted solver procedures

The proof of Lemma C.1 of Chen et al., arXiv:2203.00671v2, composes cost and
capacity scaling. Replacing one solver call by a counted procedure expands its
trace and adds its other-work counter. This file proves the corresponding
bounds and shows that sequential loops respect this substitution when their
bodies compute the same states.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CallResult

/-- Expand every recorded solver call by the trace and work of the procedure
used to implement that call. The outer returned data is unchanged. -/
def expand {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ)) (r : CallResult α) : CallResult α :=
  ⟨r.value, r.calls.flatMap (fun I => (inner I).calls),
    r.work + (r.calls.map (fun I => (inner I).work)).sum⟩

private theorem sum_map_le (xs : List Circulation) (f : Circulation → ℕ) (B : ℕ)
    (h : ∀ I ∈ xs, f I ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons I xs ih =>
    have hh := h I List.mem_cons_self
    have ht : ∀ J ∈ xs, f J ≤ B := fun J hJ => h J (List.mem_cons_of_mem _ hJ)
    have hi := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A uniform inner-call bound multiplies the length of the outer call trace. -/
theorem expand_calls {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ)) (r : CallResult α) (K : ℕ)
    (h : ∀ I ∈ r.calls, (inner I).calls.length ≤ K) :
    (expand inner r).calls.length ≤ r.calls.length * K := by
  change (r.calls.flatMap (fun I => (inner I).calls)).length ≤ _
  rw [List.length_flatMap]
  exact sum_map_le r.calls (fun I => (inner I).calls.length) K h

/-- Every inner solver instance inherits its proved property after expansion. -/
theorem expand_instances {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ)) (r : CallResult α)
    (P : Circulation → Prop)
    (h : ∀ I ∈ r.calls, ∀ J ∈ (inner I).calls, P J) :
    ∀ J ∈ (expand inner r).calls, P J := by
  intro J hJ
  obtain ⟨I, hI, hJ⟩ := List.mem_flatMap.mp hJ
  exact h I hI J hJ

/-- A uniform bound on inner work is paid once per outer call. -/
theorem expand_work {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ)) (r : CallResult α) (B : ℕ)
    (h : ∀ I ∈ r.calls, (inner I).work ≤ B) :
    (expand inner r).work ≤ r.work + r.calls.length * B :=
  Nat.add_le_add_left (sum_map_le r.calls (fun I => (inner I).work) B h) r.work

/-- Bodies returning the same state give identical state sequences. -/
theorem forRounds_value_eq {α : Type} (measured plain : α → CallResult α)
    (hvalue : ∀ a, (measured a).value = (plain a).value) (t : ℕ) (a : α) :
    (forRounds measured t a).value = (forRounds plain t a).value := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (measured (forRounds measured t a).value).value =
      (plain (forRounds plain t a).value).value
    rw [ih, hvalue]

/-- Expanding body call traces commutes with the explicit sequential loop. -/
theorem forRounds_calls_expand {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ))
    (measured plain : α → CallResult α)
    (hvalue : ∀ a, (measured a).value = (plain a).value)
    (hcalls : ∀ a, (measured a).calls = (expand inner (plain a)).calls)
    (t : ℕ) (a : α) :
    (forRounds measured t a).calls = (expand inner (forRounds plain t a)).calls := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (forRounds measured t a).calls ++
      (measured (forRounds measured t a).value).calls =
      ((forRounds plain t a).calls ++ (plain (forRounds plain t a).value).calls).flatMap _
    rw [ih, forRounds_value_eq measured plain hvalue, hcalls, List.flatMap_append]
    rfl

/-- Expanding body work counters commutes with the explicit sequential loop. -/
theorem forRounds_work_expand {α : Type}
    (inner : (I : Circulation) → CallResult (Fin I.m → ℤ))
    (measured plain : α → CallResult α)
    (hvalue : ∀ a, (measured a).value = (plain a).value)
    (hwork : ∀ a, (measured a).work = (expand inner (plain a)).work)
    (t : ℕ) (a : α) :
    (forRounds measured t a).work = (expand inner (forRounds plain t a)).work := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (forRounds measured t a).work +
      ((measured (forRounds measured t a).value).work + 1) =
      (forRounds plain t a).work + ((plain (forRounds plain t a).value).work + 1) +
        (((forRounds plain t a).calls ++ (plain (forRounds plain t a).value).calls).map _).sum
    rw [ih, forRounds_value_eq measured plain hvalue, hwork]
    simp only [expand, List.map_append, List.sum_append]
    omega

end MinCostFlow.Scaling.CallResult
