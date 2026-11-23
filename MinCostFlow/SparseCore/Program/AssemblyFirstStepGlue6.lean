module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue5
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepModel

import Mathlib.Tactic

/-!
# The bounds of Phase 3 of the first step (`AssemblyFirstStepGlue6`)

Phase 3 asks for bounds of three kinds. This file proves them.

* The names in the model are below the caps: the new roots, the edges of the old and the new core
  graph, and the deleted edges (`asmFirstStep_phase3_model`). They come from the facts of the
  old and the new state (`AsmBrModelFacts`). A deleted edge is an edge of the graph or an edge
  that the batch inserts first (`batchDeletes_lt_of_valid`), so it is below the edge cap too.
* The caps fit in a word (`asmFirstStep_cap_words`): the caps are below `(M + N + 2) ^ capExp`
  and a word holds `(M + N + 2) ^ e` when `3 capExp ≤ e` (`capPow_lt_of_word`).
* The bundle table lies below the heap pointer, and so do its slot blocks
  (`bunTable_place_of_foot`), since its fixed part and each block are cells of its foot.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **A deleted edge is below the edge cap.** In a valid batch whose inserted edges are below
`eCap`, on a graph whose edges are below `eCap`, every deleted edge is below `eCap`: it is an edge
of the graph at the time of the deletion, which is an edge of the first graph or an inserted
edge. -/
theorem delete_lt_of_valid {vCap eCap : ℕ} : ∀ (U : List Update) (G : MGraph), G.BatchIsValid U →
    BatchWithinCaps vCap eCap U → (∀ e ∈ G.E, e < eCap) → ∀ e, Update.delete e ∈ U → e < eCap
  | [], _, _, _, _, _, h => nomatch h
  | u :: rest, G, ⟨hu, hrest⟩, hCap, hGE, e, he => by
    have hE' : ∀ e ∈ (G.applyUpdate u).E, e < eCap := by
      cases u with
      | insert ei _ _ =>
        intro e' he'
        simp only [MGraph.applyUpdate, Finset.mem_insert] at he'
        rcases he' with rfl | he'
        · exact hCap _ List.mem_cons_self
        · exact hGE e' he'
      | delete _ =>
        intro e' he'
        simp only [MGraph.applyUpdate, Finset.mem_erase] at he'
        exact hGE e' he'.2
      | split _ _ _ _ => exact hGE
    rcases List.mem_cons.mp he with heq | hmem
    · subst heq
      exact hGE e hu
    · exact delete_lt_of_valid rest _ hrest (fun x hx => hCap x (List.mem_cons_of_mem _ hx)) hE'
        e hmem

/-- The edges in `batchDeletes U` are below the edge cap (`delete_lt_of_valid`). -/
theorem batchDeletes_lt_of_valid {vCap eCap : ℕ} {U : List Update} {G : MGraph}
    (hU : G.BatchIsValid U) (hCaps : BatchWithinCaps vCap eCap U) (hGE : ∀ e ∈ G.E, e < eCap) :
    ∀ e ∈ batchDeletes U, e < eCap := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff U e).mp he
  exact delete_lt_of_valid U G hU hCaps hGE e hu

/-- **The model bounds of Phase 3.** From the facts of the old and the new state: P7's readiness
(`asmBr_outStepReady`), the new roots below `vCap` (`asmBr_newRoots_lt`), the edges of the old and
the new core graph below `eCap` (a core graph has a subset of the edges of its graph), and the
deleted edges below `eCap` (`batchDeletes_lt_of_valid`). -/
theorem asmFirstStep_phase3_model {depth : ℕ} {impl : SparsifyImpl} {vCap eCap : ℕ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {delEdges : List ℕ}
    (hold : AsmBrModelFacts impl vCap eCap tr ord)
    (hnew : AsmBrModelFacts impl vCap eCap (stepBundleTree sp tr U ord ord').state ord')
    (hBU : tr.cs.G.BatchIsValid U) (hord : OrderedBatch tr.cs.G U ord ord')
    (hCaps : BatchWithinCaps vCap eCap U) (hDel : delEdges.toFinset = batchDeletes U) :
    OutStepReady sp tr U ord ord' ∧
    (∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap) ∧
    (∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, e < eCap) ∧
    (∀ e ∈ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E, e < eCap) ∧
    (∀ e ∈ delEdges, e < eCap) := by
  have hGE : ∀ e ∈ tr.cs.G.E, e < eCap := hold.2.2.2.2.2.2.2.2.1
  have hGE' : ∀ e ∈ (compLSFBatch tr.cs U).G.E, e < eCap := hnew.2.2.2.2.2.2.2.2.1
  refine ⟨asmBr_outStepReady sp hold hnew hBU hord, asmBr_newRoots_lt sp hnew,
    fun e he => hGE e (Finset.sdiff_subset he), fun e he => hGE' e (Finset.sdiff_subset he),
    fun e he => ?_⟩
  have he' : e ∈ batchDeletes U := by
    rw [← hDel]
    exact List.mem_toFinset.mpr he
  exact batchDeletes_lt_of_valid hBU hCaps hGE e he'

/-- A power of a number below `(M + N + 2) ^ capExp` fits in a word that holds
`(M + N + 2) ^ e`, when the power times `capExp` is at most `e`. -/
theorem capPow_lt_of_word {w M N L e capExp j c : ℕ}
    (hW : (M + N + 2) ^ e * (L + 1) < 2 ^ w) (hcap : c ≤ (M + N + 2) ^ capExp)
    (hj : j * capExp ≤ e) : c ^ j < 2 ^ w :=
  calc c ^ j ≤ ((M + N + 2) ^ capExp) ^ j := Nat.pow_le_pow_left hcap j
    _ = (M + N + 2) ^ (capExp * j) := (pow_mul _ _ _).symm
    _ ≤ (M + N + 2) ^ e := Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_comm]; exact hj)
    _ ≤ (M + N + 2) ^ e * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ < 2 ^ w := hW

/-- **The caps fit in a word.** When `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`, the slot cap is at
most `2 (vCap + eCap + 2) ^ 2`, and a word holds `(M + N + 2) ^ e` with `3 capExp ≤ e`, the words
of Phase 3 and the caps of Phase 2 are below `2 ^ w` (`capPow_lt_of_word` with the powers `2`
and `3`). -/
theorem asmFirstStep_cap_words {w M N L e capExp vCap eCap slotCap : ℕ}
    (hW : (M + N + 2) ^ e * (L + 1) < 2 ^ w) (hcap : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp)
    (hj : 3 * capExp ≤ e) (hsl : slotCap ≤ 2 * (vCap + eCap + 2) ^ 2) :
    (vCap + eCap + 2) ^ 2 < 2 ^ w ∧ vCap * (2 * eCap) < 2 ^ w ∧ 4 * eCap < 2 ^ w ∧
      vCap < 2 ^ w ∧ slotCap < 2 ^ w := by
  have h2 := capPow_lt_of_word hW hcap (by omega : 2 * capExp ≤ e)
  have h3 := capPow_lt_of_word hW hcap hj
  have hsq : (vCap + eCap + 2) ^ 2 = (vCap + eCap + 2) * (vCap + eCap + 2) := by ring
  have hcu : (vCap + eCap + 2) ^ 3 = (vCap + eCap + 2) ^ 2 * (vCap + eCap + 2) := by ring
  have hA : vCap * (2 * eCap) ≤ (vCap + eCap + 2) ^ 2 := by rw [hsq]; nlinarith
  have hB : 4 * eCap ≤ (vCap + eCap + 2) ^ 2 := by rw [hsq]; nlinarith
  have hC : vCap ≤ (vCap + eCap + 2) ^ 2 := by rw [hsq]; nlinarith
  have hD : 2 * (vCap + eCap + 2) ^ 2 ≤ (vCap + eCap + 2) ^ 3 := by
    rw [hcu]; nlinarith [Nat.zero_le ((vCap + eCap + 2) ^ 2)]
  exact ⟨h2, by omega, by omega, by omega, by omega⟩

/-- **The bundle table lies below `h`.** Its fixed part and each of its slot blocks are cells of
its foot and are not empty, so when the foot lies below `h < 2 ^ w`, the fixed part ends at most
at `h` and each block ends below `2 ^ w`. -/
theorem bunTable_place_of_foot {slotCap vCap eCap k bunH h w : ℕ} {m : BundleTableMeta slotCap}
    (hf : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot bunH m a → a < h)
    (hw : h < 2 ^ w) :
    bunH + bundleTableFixedSize slotCap eCap ≤ h ∧
    ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w := by
  refine ⟨?_, fun js q c hq => ?_⟩
  · have := hf (bunH + bundleTableFixedSize slotCap eCap - 1)
      (Or.inl ⟨by unfold bundleTableFixedSize; omega, by unfold bundleTableFixedSize; omega⟩)
    unfold bundleTableFixedSize at this ⊢
    omega
  · have := hf (q + bundleSlotBlockSize c - 1)
      (Or.inr ⟨js, q, c, hq, by unfold bundleSlotBlockSize; omega,
        by unfold bundleSlotBlockSize; omega⟩)
    unfold bundleSlotBlockSize at this ⊢
    omega

end

end MinCostFlow.SparseCore.Program
