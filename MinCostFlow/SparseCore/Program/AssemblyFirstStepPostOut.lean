module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4

import Mathlib.Tactic

/-!
# The split lists of Phase 3 at the end of the step (`AssemblyFirstStepPostOut`)

The post of the step (`AsmFsPostRaw`) asks for the input record of the output step
(`OutStepInAt`) in the final memory, below the final heap pointer and outside the output graph
and the final tour. Phase 4 writes the leaving and the entering edges. The split lists are those
that Phase 3 wrote (`OutSplitListsAt`), below the end of Phase 3 and outside the cells that
Phase 3 avoided. Phase 4 keeps these cells, and the final avoided cells below the end of Phase 3
are among those that Phase 3 avoided.

`outSplitListsAt_transfer` moves the split lists to a new memory that agrees on the cells below
`top` outside `avoid`, to a larger top and to a set `avoid'` that, below `top`, lies in `avoid`.
The split lists read only such cells: each record has five cells outside `avoid`, and each list
of ends has its cells outside `avoid`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

public section

/-- **The split lists in a new memory.** If `mem'` agrees with `mem` below `top` outside
`avoid` (`hag`), the set `avoid'` lies in `avoid` below `top` (`hav`) and `top ≤ top'`, then the
split lists at `a` stay in place. By induction on the splits. A record lies below `top`
outside `avoid`, so its five cells agree, and so do the cells of its list of ends. -/
theorem outSplitListsAt_transfer {mem mem' : ℕ → ℕ} {top top' : ℕ} {avoid avoid' : ℕ → Prop}
    {keep E₀ : Finset ℕ}
    (hag : ∀ x, x < top → ¬ avoid x → mem' x = mem x)
    (hav : ∀ x, x < top → avoid' x → avoid x) (htop : top ≤ top') :
    ∀ (P : List Update) (Ys : List (List End)) (a : ℕ) (G : MGraph),
      OutSplitListsAt mem top avoid keep E₀ a G P Ys →
      OutSplitListsAt mem' top' avoid' keep E₀ a G P Ys := by
  intro P
  induction P with
  | nil =>
    intro Ys a G h
    cases Ys with
    | nil => exact h
    | cons Y Ys => exact False.elim h
  | cons u P ih =>
    intro Ys a G h
    cases Ys with
    | nil => cases u <;> exact False.elim h
    | cons Y Ys =>
      cases u with
      | insert e x y => exact False.elim h
      | delete e => exact False.elim h
      | split v v' St Sh =>
        simp only [OutSplitListsAt] at h ⊢
        obtain ⟨h0, h5, hfree, hv, hv', h2, hE, hlen, hfree2, hnd, hE₀, hkeep, hrest⟩ := h
        have hk : ∀ i < 5, mem' (a + i) = mem (a + i) :=
          fun i hi => hag _ (by omega) (hfree i hi)
        have hk2 : ∀ i < 1 + Y.length, mem' (mem (a + 3) + i) = mem (mem (a + 3) + i) :=
          fun i hi => hag _ (by omega) (hfree2 i hi)
        have e0 : mem' a = mem a := by simpa using hk 0 (by norm_num)
        have e1 := hk 1 (by norm_num)
        have e2 := hk 2 (by norm_num)
        have e3 := hk 3 (by norm_num)
        have e4 := hk 4 (by norm_num)
        have hl0 : mem' (mem (a + 3)) = mem (mem (a + 3)) := by
          simpa using hk2 0 (by omega)
        refine ⟨h0, by omega, fun i hi ha => hfree i hi (hav _ (by omega) ha),
          by rw [e0]; exact hv, by rw [e1]; exact hv', by rw [e2]; exact h2, ?_,
          by rw [e3]; omega, fun i hi ha => ?_, hnd, hE₀, fun x hx => by rw [e2]; exact hkeep x hx,
          by rw [e4]; exact ih Ys _ _ hrest⟩
        · rw [e3]
          refine ⟨by rw [hl0]; exact hE.1, fun i hi => ?_⟩
          have hc := hk2 (1 + i) (by omega)
          rw [← Nat.add_assoc] at hc
          rw [hc]
          exact hE.2 i hi
        · rw [e3] at ha
          exact hfree2 i hi (hav _ (by omega) ha)

end

end MinCostFlow.SparseCore.Program
