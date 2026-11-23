module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Proof
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase5Facts
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriverCells

import Mathlib.Tactic

/-!
# Phase 1 of the first step, from the branch (`AssemblyFirstStepGlue1`)

The first step of a branch (the step of Section 6 of the paper) starts with Phase 1, the scan of
the batch (`asmFirstScanBatch_runs`). The driver (`asmFirstStepMainStmt`) calls it on the graph
of the read record, the component map and the component table of the side record, the batch and
the caps, at the heap pointer `h + 6`. This file proves that the premises of the scan hold when
the branch is in its representation (`asmBrFullRep`), as `AsmBrCoreStepAt.runs` gives it.

* `cells_apart`: two blocks of cells with no common cell lie one after the other, when neither is
  empty. The representation keeps its parts apart cell by cell; the scan asks the blocks apart as
  intervals (`ScanGeom`).
* `asmFirstStep_scanGeom`: the geometry of the scan. The graph, the component map and the
  component table are cells of the branch, so they lie below `h` and apart from one another, and
  the batch is apart from them since it is an input outside the cells of the branch.
* `asmFirstStep_phase1_runs`: the run of the scan, with its post, for the start map
  `v ↦ mem (cmpH + v)` and the active flags of the components of the side.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **Blocks apart.** Two blocks `[a, a + n)` and `[c, c + m)` with no common cell lie one after
the other, when neither is empty. If they overlapped, the larger of the two starts would be a
common cell. -/
theorem cells_apart {a n c m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : ∀ i < n, ∀ j < m, a + i ≠ c + j) : a + n ≤ c ∨ c + m ≤ a := by
  by_contra hc
  rcases le_total a c with hac | hca
  · exact h (c - a) (by omega) 0 hm (by omega)
  · exact h 0 hn (a - c) (by omega) (by omega)

/-- A block of cells that is not empty, and lies apart from another one cell by cell, lies apart
from it as an interval, or the other block is empty. -/
theorem cells_apart_or {a n c m : ℕ}
    (h : ∀ i < n, ∀ j < m, a + i ≠ c + j) : n = 0 ∨ m = 0 ∨ a + n ≤ c ∨ c + m ≤ a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inr (Or.inl hm)
  exact Or.inr (Or.inr (cells_apart hn hm h))

variable {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
  {impl : SparsifyImpl} {w P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}

/-- **The geometry of the scan**, from the representation of the branch at `b`. The graph of the
read record, the component map and the component table are cells of the branch: the graph is a
block of the read data, the map and the table are blocks of the maps of the side. So they lie
below `h`, and they are apart, since the parts of the branch are apart and the blocks of the maps
are apart (`AsmSdMapsAt`). The batch is an input outside the cells of the branch, so it is apart
from the three. -/
theorem asmFirstStep_scanGeom {b batch words h : ℕ} {a : AsmBranchAbs depth}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {mem : ℕ → ℕ}
    (hR : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b a x mem)
    (hwords : 0 < words)
    (hBin : InputAt w mem ((asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot
      b x) batch words h)
    (hfoot : ∀ a', (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot b x a' →
      a' < h)
    (hw16 : 16 ≤ 2 ^ w)
    (hsp : h + 6 + asmFirstScanBatchSpace x.vCap x.eCap words < 2 ^ w) :
    ScanGeom w x.yRead.q.g x.xRest.cmpH x.xRest.ctH x.xRest.comps.length batch words x.vCap
      x.eCap (h + 6) := by
  obtain ⟨hRep, hV5, -⟩ := hR
  have hD : ∀ i j, i ≠ j → ∀ a', asmSdMapPart x.xRest i a' → ¬ asmSdMapPart x.xRest j a' := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSide, -⟩ := hRep
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, -⟩ := hSide
    exact hMaps.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDisj⟩ := hRep
  -- the three blocks are cells of the branch
  have hG : ∀ i < dynGraphSize x.vCap x.eCap,
      (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot b x
        (x.yRead.q.g + i) := fun i hi =>
    ⟨1, by decide, Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega⟩)))))))⟩
  have hGp : ∀ i < dynGraphSize x.vCap x.eCap,
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 1 (x.yRead.q.g + i) :=
    fun i hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega⟩)))))))
  have hCp : ∀ v < x.vCap,
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 5 (x.xRest.cmpH + v) :=
    fun v hv => ⟨3, by decide, Or.inr ⟨0, by omega, by rw [hV5]; omega⟩⟩
  have hTp : ∀ c < 3 * x.xRest.comps.length,
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 5 (x.xRest.ctH + c) :=
    fun c hc => ⟨3, by decide, Or.inr ⟨2, by omega, by omega⟩⟩
  have hfoot5 : ∀ a', asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 5 a' →
      a' < h := fun a' ha' => hfoot a' ⟨5, by decide, ha'⟩
  have hdG : 0 < dynGraphSize x.vCap x.eCap := by unfold dynGraphSize; omega
  -- the bounds below `h`
  have hg_le : x.yRead.q.g + dynGraphSize x.vCap x.eCap ≤ h := by
    have := hfoot _ (hG _ (Nat.sub_lt hdG Nat.one_pos)); omega
  have hcmp : x.vCap = 0 ∨ x.xRest.cmpH + x.vCap ≤ h := by
    rcases Nat.eq_zero_or_pos x.vCap with h0 | hpos
    · exact Or.inl h0
    · right; have := hfoot5 _ (hCp _ (Nat.sub_lt hpos Nat.one_pos)); omega
  have hct : x.xRest.comps.length = 0 ∨ x.xRest.ctH + 3 * x.xRest.comps.length ≤ h := by
    rcases Nat.eq_zero_or_pos x.xRest.comps.length with h0 | hpos
    · exact Or.inl h0
    · right; have := hfoot5 _ (hTp _ (show 3 * x.xRest.comps.length - 1 < _ by omega)); omega
  -- the blocks apart
  have hgc : ∀ i < dynGraphSize x.vCap x.eCap, ∀ j < x.vCap,
      x.yRead.q.g + i ≠ x.xRest.cmpH + j := fun i hi j hj heq =>
    hDisj 1 (by decide) 5 (by decide) (by decide) _ (hGp i hi) (heq ▸ hCp j hj)
  have hgt : ∀ i < dynGraphSize x.vCap x.eCap, ∀ j < 3 * x.xRest.comps.length,
      x.yRead.q.g + i ≠ x.xRest.ctH + j := fun i hi j hj heq =>
    hDisj 1 (by decide) 5 (by decide) (by decide) _ (hGp i hi) (heq ▸ hTp j hj)
  have hbc : ∀ i < words, ∀ j < x.vCap, batch + i ≠ x.xRest.cmpH + j := fun i hi j hj heq =>
    (hBin.2 i hi).2 (heq ▸ ⟨5, by decide, hCp j hj⟩)
  have hbt : ∀ i < words, ∀ j < 3 * x.xRest.comps.length, batch + i ≠ x.xRest.ctH + j :=
    fun i hi j hj heq => (hBin.2 i hi).2 (heq ▸ ⟨5, by decide, hTp j hj⟩)
  have hct' : ∀ i < x.vCap, ∀ j < 3 * x.xRest.comps.length,
      x.xRest.cmpH + i ≠ x.xRest.ctH + j := by
    intro i hi j hj heq
    exact hD 0 2 (by decide) (x.xRest.cmpH + i)
      (show asmSdMapPart x.xRest 0 (x.xRest.cmpH + i) from ⟨by omega, by rw [hV5]; omega⟩)
      (show asmSdMapPart x.xRest 2 (x.xRest.cmpH + i) from ⟨by omega, by omega⟩)
  have hgc' := cells_apart_or hgc
  have hgt' := cells_apart_or hgt
  have hbc' := cells_apart_or hbc
  have hbt' := cells_apart_or hbt
  have hct'' := cells_apart_or hct'
  have hbat := hBin.1
  exact ⟨hw16, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, hsp⟩

/-- **Phase 1 from the branch.** When the branch at `b` is in its representation, the batch `U`
is valid with names below the caps and sits outside the cells of the branch, the cells of the
branch lie below `h`, and the memory is zero from `h`, the scan of Phase 1 runs at `h + 6`. It
starts from the component map `v ↦ mem (cmpH + v)` and the active flags of the components of the
side. The premises of `asmFirstScanBatch_runs` come from the side record: the LSF invariant, the
cross edges of the inactive components, the list of the components and the maps
(`asmSdMaps_cmp_ok`, `asmSdMaps_cmp_lt`); the graph comes from the read record
(`asmFirstStep_cells_of_rep`), and the geometry from `asmFirstStep_scanGeom`. -/
theorem asmFirstStep_phase1_runs {p : Program} {ω : ℕ → Bool} {b batch words h pos : ℕ}
    {a : AsmBranchAbs depth}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {U : List Update}
    {mem : ℕ → ℕ}
    (hR : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b a x mem)
    (hU : a.tr.cs.G.BatchIsValid U) (hCaps : BatchWithinCaps x.vCap x.eCap U)
    (hBat : BatchAt mem batch a.tr.cs.G U words)
    (hBin : InputAt w mem ((asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot
      b x) batch words h)
    (hfoot : ∀ a', (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot b x a' →
      a' < h)
    (hw16 : 16 ≤ 2 ^ w) (hz : ZeroFrom mem h)
    (hsp : h + 6 + asmFirstScanBatchSpace x.vCap x.eCap words < 2 ^ w) :
    let st0 : ScanBatchState :=
      { cmpMap := fun v => mem (x.xRest.cmpH + v)
        actFlag := fun c => if hc : c < x.xRest.comps.length then
          decide (x.xRest.comps[c] ∈ a.tr.activeComps) else false
        insFlag := fun _ => false
        delFlag := fun _ => false
        origVert := fun _ => 0
        newComps := []
        delEdges := []
        insEdges := [] }
    let sbF := scanBatchFold a.tr.cs.G st0 U
    ∃ st' cost,
      Runs w p ω asmFirstScanBatchStmt
        (startState [x.yRead.q.g, x.xRest.cmpH, x.xRest.ctH, batch, words, x.vCap, x.eCap, h + 6]
          mem pos)
        (.returned (h + 6 + asmFirstScanBatchSpace x.vCap x.eCap words)) st' cost ∧
      st'.mem (h + 6) = sbF.newComps.length ∧
      st'.mem (h + 7) = sbF.delEdges.length ∧
      ScanMemAt mem st'.mem x.xRest.cmpH x.xRest.ctH x.xRest.comps.length x.vCap x.eCap words
        (h + 6) sbF ∧
      cost ≤ 245 * words + 120 := by
  intro st0 sbF
  have hcells := asmFirstStep_cells_of_rep hR
  have hGeo := asmFirstStep_scanGeom hR hBat.1 hBin hfoot hw16 hsp
  obtain ⟨hRep, -⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSide, -⟩ := hRep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, hM⟩ := hSide
  obtain ⟨-, -, -, -, -, -, hLSF, -, -, -, -, -, -, -, -, -, -, -, -, -, hCross, -⟩ := hM
  obtain ⟨C_lsst, ℓ₀, hI, -⟩ := hLSF
  have hMaps' := hMaps
  obtain ⟨-, -, -, -, hCnd, hCiff, -, -, hCt, -⟩ := hMaps'
  obtain ⟨st', cost, hrun, h0, h1, -, hM', hc⟩ :=
    asmFirstScanBatch_runs (p := p) (ω := ω) (pos := pos) (cmpMap₀ := fun v => mem (x.xRest.cmpH + v))
      hI hU hCaps hCnd hCiff (fun v _ => rfl) (asmSdMaps_cmp_lt hI hMaps)
      (asmSdMaps_cmp_ok hMaps) (fun c hc => (hCt c hc).1) hCross hcells.2.2.2.2.2.2.2.2.1 hBat
      hGeo (hz.mono (by omega))
  exact ⟨st', cost, hrun, h0, h1, hM', hc⟩

end

end MinCostFlow.SparseCore.Program
