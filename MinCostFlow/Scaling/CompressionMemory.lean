module

public import MinCostFlow.Scaling.SolverInputLayout
public import MinCostFlow.Scaling.VertexCompression
import Mathlib.Tactic.FinCases

/-!
# Memory correctness of endpoint relabeling

Compression copies a circulation, remaps its tail and head cells, and replaces
its vertex-count header. This file proves that those operations produce
exactly the solver encoding of `Circulation.compress`. The frame conditions
show that remapping leaves capacities, signs, and cost magnitudes unchanged.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Copying records, remapping both endpoint tables, and updating the header
produces the solver layout of the model's compressed graph. -/
theorem compressed_solverWords_at (J : Circulation) (a : ℕ)
    (mem0 mem1 mem2 : ℕ → ℕ) (hcopy : ListAt mem0 a J.solverWords)
    (htail : ∀ e : Fin J.m, mem1 (a + 2 + 5 * e.val) =
      J.endpointLabels.table (J.tail e) - 1)
    (hframe1 : ∀ x, (∀ e : Fin J.m, x ≠ a + 2 + 5 * e.val) → mem1 x = mem0 x)
    (hhead : ∀ e : Fin J.m, mem2 (a + 3 + 5 * e.val) =
      J.endpointLabels.table (J.head e) - 1)
    (hframe2 : ∀ x, (∀ e : Fin J.m, x ≠ a + 3 + 5 * e.val) → mem2 x = mem1 x) :
    ListAt (Function.update mem2 a J.endpointLabels.count) a J.compress.solverWords := by
  have hsource := (solverWords_at_iff J mem0 a).mp hcopy
  apply (solverWords_at_iff J.compress _ a).mpr
  refine ⟨by rw [Function.update_self], ?_, ?_⟩
  · rw [Function.update_of_ne (by omega : a + 1 ≠ a)]
    have h2 := hframe2 (a + 1) (fun e => by omega)
    have h1 := hframe1 (a + 1) (fun e => by omega)
    exact h2.trans (h1.trans hsource.2.1)
  · intro e j
    have headdr : a + (2 + 5 * e.val + j.val) ≠ a := by omega
    rw [Function.update_of_ne headdr]
    fin_cases j
    · have h2 := hframe2 (a + 2 + 5 * e.val) (fun k => by omega)
      have hh := h2.trans (htail e)
      simpa only [Circulation.solverEdgeWords, Circulation.compress, Circulation.encodeVertex,
        List.getD_cons_zero, Nat.add_zero, Nat.add_assoc] using hh
    · have hh := hhead e
      have haddr : a + (2 + 5 * e.val + 1) = a + 3 + 5 * e.val := by omega
      rw [haddr]
      simpa only [Circulation.solverEdgeWords, Circulation.compress, Circulation.encodeVertex,
        List.getD_cons_succ, List.getD_cons_zero] using hh
    · have h2 := hframe2 (a + (2 + 5 * e.val + 2)) (fun k => by omega)
      have h1 := hframe1 (a + (2 + 5 * e.val + 2)) (fun k => by omega)
      have hh := h2.trans (h1.trans (hsource.2.2 e ⟨2, by decide⟩))
      simpa only [Circulation.solverEdgeWords, Circulation.compress,
        List.getD_cons_succ, List.getD_cons_zero] using hh
    · have h2 := hframe2 (a + (2 + 5 * e.val + 3)) (fun k => by omega)
      have h1 := hframe1 (a + (2 + 5 * e.val + 3)) (fun k => by omega)
      have hh := h2.trans (h1.trans (hsource.2.2 e ⟨3, by decide⟩))
      simpa only [Circulation.solverEdgeWords, Circulation.compress,
        List.getD_cons_succ, List.getD_cons_zero] using hh
    · have h2 := hframe2 (a + (2 + 5 * e.val + 4)) (fun k => by omega)
      have h1 := hframe1 (a + (2 + 5 * e.val + 4)) (fun k => by omega)
      have hh := h2.trans (h1.trans (hsource.2.2 e ⟨4, by decide⟩))
      simpa only [Circulation.solverEdgeWords, Circulation.compress,
        List.getD_cons_succ, List.getD_cons_zero] using hh

end MinCostFlow.Scaling.Machine
