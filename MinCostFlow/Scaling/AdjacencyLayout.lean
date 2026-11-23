module

public import MinCostFlow.Scaling.IndexListLayout
public import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Basic
import WordRAM.Memory

/-!
# Stored adjacency heads and lengths

The label and cycle traversals index outgoing edge lists by vertex. Each
vertex has two words: its immutable-list pointer and its length. The list
nodes lie after the entire vertex table. Updating one vertex therefore
preserves every other head, and changing head cells leaves existing list
nodes intact. This file proves these layout update and frame rules.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A pointer and list length per vertex, with all list nodes in `[lo,bound)`. -/
def AdjacencyAt {n m : ℕ} (mem : ℕ → ℕ) (heads lo bound : ℕ)
    (out : Fin n → List (Fin m)) : Prop :=
  ∀ v, ∃ ptr, ListAt mem (heads+2*v.val) [ptr, (out v).length] ∧
    IndexListAt mem lo bound ptr (out v)

/-- Updating one head and supplying its represented list changes exactly
that vertex's adjacency value. Node cells and all other heads are preserved. -/
theorem AdjacencyAt.update {n m : ℕ} {mem mem' : ℕ → ℕ} {heads lo bound bound' : ℕ}
    {out : Fin n → List (Fin m)} (hat : AdjacencyAt mem heads lo bound out)
    (v : Fin n) (es : List (Fin m)) (ptr : ℕ)
    (hend : heads+2*n ≤ lo) (hbound : bound ≤ bound')
    (hhead : ListAt mem' (heads+2*v.val) [ptr, es.length])
    (hlist : IndexListAt mem' lo bound' ptr es)
    (hnodeFrame : ∀ x, lo ≤ x → x < bound → mem' x = mem x)
    (hheadFrame : ∀ x < lo, x ≠ heads+2*v.val → x ≠ heads+2*v.val+1 → mem' x = mem x) :
    AdjacencyAt mem' heads lo bound' (Function.update out v es) := by
  intro u
  by_cases huv : u = v
  · subst u
    simpa only [Function.update_self] using (show ∃ p,
      ListAt mem' (heads+2*v.val) [p, es.length] ∧ IndexListAt mem' lo bound' p es from
      ⟨ptr, hhead, hlist⟩)
  · rw [Function.update_of_ne huv]
    obtain ⟨p, hstored, hnodes⟩ := hat u
    refine ⟨p, ?_, (hnodes.of_agree hnodeFrame).mono le_rfl hbound⟩
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    have hu := u.isLt
    have hv := v.isLt
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rw [hheadFrame _ (by rcases hi' with rfl | rfl <;> omega)
      (by rcases hi' with rfl | rfl <;> omega) (by rcases hi' with rfl | rfl <;> omega)]
    exact hstored i hi

/-- A frame below the old storage bound preserves the whole adjacency table,
while the allowed node range may grow with new allocations. -/
theorem AdjacencyAt.of_agree_below {n m : ℕ} {mem mem' : ℕ → ℕ}
    {heads lo bound bound' : ℕ} {out : Fin n → List (Fin m)}
    (hat : AdjacencyAt mem heads lo bound out) (hend : heads+2*n ≤ bound)
    (hbound : bound ≤ bound') (hframe : ∀ x < bound, mem' x = mem x) :
    AdjacencyAt mem' heads lo bound' out := by
  intro v
  obtain ⟨ptr, hstored, hnodes⟩ := hat v
  refine ⟨ptr, hstored.of_agree_below (h₀ := bound) ?_ hframe,
    (hnodes.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound⟩
  change heads+2*v.val+2 ≤ bound
  have hv := v.isLt
  omega

/-- Preserving head cells and immutable node cells preserves the adjacency
layout independently of writes to other tables in the same memory. -/
theorem AdjacencyAt.of_agree {n m : ℕ} {mem mem' : ℕ → ℕ}
    {heads lo bound bound' : ℕ} {out : Fin n → List (Fin m)}
    (hat : AdjacencyAt mem heads lo bound out) (hbound : bound ≤ bound')
    (hheads : ∀ x, heads ≤ x → x < heads+2*n → mem' x = mem x)
    (hnodes : ∀ x, lo ≤ x → x < bound → mem' x = mem x) :
    AdjacencyAt mem' heads lo bound' out := by
  intro v
  obtain ⟨ptr, hstored, hlist⟩ := hat v
  refine ⟨ptr, ?_, (hlist.of_agree hnodes).mono le_rfl hbound⟩
  intro i hi
  have hv := v.isLt
  have hi' : i < 2 := hi
  exact (hheads _ (by omega) (by omega)).trans (hstored i hi)

/-- Zero memory initializes every vertex's pointer and length to zero. -/
theorem adjacencyAt_empty {n m : ℕ} {mem : ℕ → ℕ} {heads lo bound : ℕ}
    (hzero : ZeroFrom mem heads) :
    AdjacencyAt mem heads lo bound (fun _ : Fin n => ([] : List (Fin m))) := by
  intro v
  refine ⟨0, ?_, .nil⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
  rcases hi' with rfl | rfl <;> rw [hzero _ (by omega)] <;> rfl

/-- The initial empty adjacency table, separated node range, positive heap,
and zero tail hold together for all graph dimensions. -/
theorem exists_emptyAdjacencyAt (n m : ℕ) :
    ∃ mem lo, 0 < lo ∧ 2*n ≤ lo ∧
      AdjacencyAt mem 0 lo lo (fun _ : Fin n => ([] : List (Fin m))) ∧ ZeroFrom mem lo := by
  exact ⟨fun _ => 0, 2*n+1, by omega, by omega,
    adjacencyAt_empty (fun _ _ => rfl), fun _ _ => rfl⟩

end MinCostFlow.Scaling.Machine
