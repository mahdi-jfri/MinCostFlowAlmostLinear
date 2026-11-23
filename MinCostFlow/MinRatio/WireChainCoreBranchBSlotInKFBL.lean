module

public import MinCostFlow.MinRatio.WireChainCoreBranchBDoneKFBL

/-!
# The slot words that Sync 2a reads (`WireChainCoreBranchBSlotInKFBL`)

Sync 2a of Branch B reads, for each finished level `j`, the pointer and the length of the list
`fDel j` from the words `2` and `3` of the select slot of the level. `branchBSlot_of_done` gives
the premise `hSlot` of `wireBranchBSuffixKFBL_runs` from the finished slots of the exit
(`BranchBDoneSlots`): the slot holds the lists (`LevelDiffListsAt`), and the list lies below the
heap pointer `hi` (`SelOutGoodAt`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program SparseCore.Program

/-- The premise `hSlot` of `wireBranchBSuffixKFBL_runs` at the heap pointer `hi` of the finished
slots, with `fPtr j` the word `2` of the slot of level `j`. The slots end below `hi`
(`hSlotEnd`). -/
theorem branchBSlot_of_done {w P d lo hi selBase n : ℕ} {Lmax : ℕ → ℕ}
    {foot : ℕ → ℕ → Prop} {mem : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E' : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem n D G U E' vals)
    (hSlotEnd : selBase + 1 + 12 * n ≤ hi) :
    ∀ j < n, mem (selBase + 1 + 12 * j + 2) = mem (selBase + 1 + 12 * j + 2) ∧
      mem (selBase + 1 + 12 * j + 3) = (D j).fDel.length ∧
      ListAt mem (mem (selBase + 1 + 12 * j + 2)) (D j).fDel ∧
      mem (selBase + 1 + 12 * j + 2) + (D j).fDel.length ≤ hi ∧
      selBase + 1 + 12 * j + 3 < hi := by
  intro j hj
  obtain ⟨hL, _, hF, _⟩ := h j hj
  exact ⟨rfl, hL.2.2.1, hL.2.2.2.1, hF.2.1, by omega⟩

end MinCostFlow.MinRatio
