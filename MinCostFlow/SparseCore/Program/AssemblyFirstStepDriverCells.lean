module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFull

import Mathlib.Tactic

/-!
# The cells that the driver of the first step reads (`AssemblyFirstStepDriverCells`)

The driver of the first step (`asmFirstStepMainStmt`, the step of a branch in Section 6 of the
paper) starts by reading words of the branch record and of the side record. Its run
(`asmFirstStepMain_run_of`) asks what these words are. This file reads them off the
representation of the branch (`asmBrFullRep`), which `AsmBrCoreStepAt.runs` gives.

* `asmFirstStep_cells_of_rep`: the words of the branch record (the side record, the tour, the
  caps, the read record, the embedding and the output graph), the graph `tr.cs.G` at cell `6` of
  the read record, the output graph `tr.S_cur`, and the words of the side record (the bundle
  table, the spanner table, the slot count, the slot cap, the component map and the component
  table).
* `asmFirstStep_bounds_of_foot`: the branch record, the read record, the side record and the
  output graph lie below `h` when the cells of the branch do.
* `asmBrModelFacts_of_rep`: the model facts `AsmBrModelFacts` of the old state. The step asks them
  of the new state only, but Phase 3 needs them of the old one too (`asmBr_outStepReady`). The
  side model of the branch holds all of them but the validity of `S_cur` and the bounds on the
  names, which the read view gives (`ReadView.Inv`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.MinRatio
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The cells that the driver reads**, from the representation of the branch at `b`. The
offsets are those of the branch record (`ASM_BR_*`) and of the side record (`ASM_SD_*`). -/
theorem asmFirstStep_cells_of_rep {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {b : ℕ} {a : AsmBranchAbs depth}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {mem : ℕ → ℕ}
    (hR : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b a x mem) :
    mem (b + 4) = x.restH ∧ mem (b + 3) = x.tourH ∧ mem (b + 5) = x.vCap ∧
    mem (b + 6) = x.eCap ∧ mem b = x.readH ∧ mem (b + 1) = x.embH ∧ mem (b + 2) = x.outH ∧
    mem (x.readH + 6) = x.yRead.q.g ∧ DynGraphAt mem x.yRead.q.g x.vCap x.eCap a.tr.cs.G ∧
    mem x.outH = x.gOut ∧ DynGraphAt mem x.gOut x.vCap x.eCap a.tr.S_cur ∧
    mem x.restH = x.xRest.bunH ∧ mem (x.restH + 1) = x.xRest.spanH ∧
    mem (x.restH + 3) = x.xRest.slots.length ∧ mem (x.restH + 4) = x.xRest.slotCap ∧
    mem (x.restH + 12) = x.xRest.cmpH ∧ mem (x.restH + 14) = x.xRest.ctH := by
  obtain ⟨hRep, -⟩ := hR
  obtain ⟨hRd, hEmb, hOut, hTour, hRest, hV, hE, -, -, hG, -, -, -, hRead, -, -, -, hOutG, -, -,
    hSide, -⟩ := hRep
  obtain ⟨hview, -, -, hRec, -⟩ := hRead
  obtain ⟨-, -, -, -, -, -, hg6, -, -, -, -, -, -, -, -, hDG⟩ := hRec
  obtain ⟨hOH, -, hDGS⟩ := hOutG
  obtain ⟨hBun, hSpan, -, hNS, hSC, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, -⟩ := hSide
  obtain ⟨hCmp, -, hCt, -⟩ := hMaps
  rw [hview, hG] at hDG
  exact ⟨hRest, hTour, hV, hE, hRd, hEmb, hOut, hg6, hDG, hOH, hDGS, hBun, hSpan, hNS, hSC,
    hCmp, hCt⟩

/-- **The records lie below `h`.** If every cell of the branch at `b` is below `h`, then so are
the branch record, the read record, the side record and the output graph. -/
theorem asmFirstStep_bounds_of_foot {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {b h : ℕ} {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ}
    (hfoot : ∀ a, (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).foot b x a →
      a < h) :
    b + ASM_BR_SIZE ≤ h ∧ x.readH + readFullWords ≤ h ∧ x.restH + ASM_SD_SIZE ≤ h ∧
      x.gOut + dynGraphSize x.vCap x.eCap ≤ h := by
  have hB : b + ASM_BR_SIZE - 1 < h :=
    hfoot _ ⟨0, by decide, by unfold ASM_BR_SIZE; omega, by unfold ASM_BR_SIZE; omega⟩
  have hRd : x.readH + readFullWords - 1 < h :=
    hfoot _ ⟨1, by decide, Or.inl ⟨by unfold readFullWords; omega, by unfold readFullWords; omega⟩⟩
  have hS : x.restH + ASM_SD_SIZE - 1 < h :=
    hfoot _ ⟨5, by decide, ⟨0, by decide, by unfold ASM_SD_SIZE; omega,
      by unfold ASM_SD_SIZE; omega⟩⟩
  have hO : x.gOut + dynGraphSize x.vCap x.eCap - 1 < h :=
    hfoot _ ⟨3, by decide, Or.inr ⟨by unfold dynGraphSize; omega,
      by unfold dynGraphSize; omega⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ASM_BR_SIZE at hB ⊢; omega
  · unfold readFullWords at hRd ⊢; omega
  · unfold ASM_SD_SIZE at hS ⊢; omega
  · unfold dynGraphSize at hO ⊢; omega

/-- **The model facts of the old state**, from the representation of the branch. The side
model gives `1 ≤ k`, the LSF invariant with the rotation, `RestartScurModelInv`,
`BunDisjointInv`, the spanner constant, and the spanner parameters at `mMax`, which is `m₀`. The
read view holds `tr.cs.G` and `S_cur`, and its invariant gives the validity of `S_cur` and the
bounds on the names by the caps. -/
theorem asmBrModelFacts_of_rep {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {b : ℕ} {a : AsmBranchAbs depth}
    {x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ} {mem : ℕ → ℕ}
    (hR : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).rep b a x mem) :
    AsmBrModelFacts impl x.vCap x.eCap a.tr a.ord := by
  obtain ⟨hRep, -⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, hG, -, hS, hInv, -, -, -, -, -, -, -, hSide, -⟩ := hRep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hM⟩ := hSide
  obtain ⟨-, -, -, hScur, -, hk, hLSF, hPar, hConst, -, -, hDisj, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hmMax, -, -⟩ := hM
  obtain ⟨-, hV, hE, -, -, -, -, -, -, -, -, -, hSval, -, hSE, -⟩ := hInv
  rw [hG] at hV hE
  rw [hS] at hSval hSE
  rw [hmMax] at hPar
  exact ⟨hk, hLSF, hScur, hDisj, hSval, hPar, hConst, hV, hE, hSE⟩

end

end MinCostFlow.SparseCore.Program
