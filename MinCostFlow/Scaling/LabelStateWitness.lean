module

public import MinCostFlow.Scaling.LabelStateLayout

/-!
# Stored label states with arbitrary pending lists

An immutable list can be allocated above the state arrays while leaving
those arrays zero. Writing its pointer and length into the state header
then represents any pending list with zero labels, false visited flags,
and empty outgoing lists. This gives concrete nonempty traversal states
without a reachability or algorithm-correctness hypothesis.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every pending edge list has a concrete stored label state and fresh
zero tail, with the other state fields in their zero/empty form. -/
theorem exists_labelStatePendingAt_at (J : Circulation) (base : ℕ) (es : List (Fin J.m)) :
    ∃ mem bound, labelNodes J.n base ≤ bound ∧ ZeroFrom mem bound ∧
      LabelStateAt mem base bound
        { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := es :
          Circulation.LabelState J } := by
  let lo := labelNodes J.n base
  have hlo : base+3 ≤ lo := by dsimp [lo, labelNodes]; omega
  obtain ⟨mem, bound, ptr, hbound, _, hat, hprefix, hzero⟩ := exists_indexListAt_above lo es
  let mem' := Function.update (Function.update mem base ptr) (base+1) es.length
  have hframe : ∀ x, lo ≤ x → x < bound → mem' x = mem x := by
    intro x hx _
    dsimp only [mem']
    rw [Function.update_of_ne (by omega : x ≠ base+1), Function.update_of_ne (by omega : x ≠ base)]
  have harray : ∀ x, base+2 ≤ x → x < lo → mem' x = 0 := by
    intro x hx hxlo
    dsimp only [mem']
    rw [Function.update_of_ne (by omega : x ≠ base+1), Function.update_of_ne (by omega : x ≠ base)]
    exact hprefix x hxlo
  refine ⟨mem', bound, hbound, ?_, ptr, ?_, hat.of_agree hframe, ?_, ?_, ?_⟩
  · intro x hx
    dsimp only [mem']
    rw [Function.update_of_ne (by omega : x ≠ base+1), Function.update_of_ne (by omega : x ≠ base)]
    exact hzero x hx
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl
    · simp only [mem', Nat.add_zero, Function.update_of_ne (by omega : base ≠ base+1),
        Function.update_self, List.getElem_cons_zero]
    · simp only [mem', Function.update_self, List.getElem_cons_succ, List.getElem_cons_zero]
  · intro v i hi
    have hv := v.isLt
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl <;>
      rw [harray _ (by dsimp [labelLabels]; omega) (by dsimp [lo, labelLabels, labelNodes]; omega)] <;> rfl
  · intro v
    have hv := v.isLt
    exact harray _ (by dsimp [labelSeen]; omega) (by dsimp [lo, labelSeen, labelNodes]; omega)
  · intro v
    refine ⟨0, ?_, .nil⟩
    intro i hi
    have hv := v.isLt
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl <;>
      rw [harray _ (by dsimp [labelHeads]; omega) (by dsimp [lo, labelHeads, labelNodes]; omega)] <;> rfl

/-- The zero-base specialization represents arbitrary pending lists in
canonical state memory with a fresh zero tail. -/
theorem exists_labelStatePendingAt (J : Circulation) (es : List (Fin J.m)) :
    ∃ mem bound, labelNodes J.n 0 ≤ bound ∧ ZeroFrom mem bound ∧
      LabelStateAt mem 0 bound
        { labels := fun _ => 0, seen := fun _ => false, outgoing := fun _ => [], pending := es :
          Circulation.LabelState J } := exists_labelStatePendingAt_at J 0 es

end MinCostFlow.Scaling.Machine
