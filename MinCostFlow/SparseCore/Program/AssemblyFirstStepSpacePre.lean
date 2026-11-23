module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue3
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceTotal
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriverCells
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepTop

import Mathlib.Tactic

/-!
# The room of Phases 1, 2 and 3 (`AssemblyFirstStepSpacePre`)

Before the step, the room `h + space X < 2 ^ w` of `AsmFsPre` holds at the space
`asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`. The space of each prefix of the phases is at most
that space (the lemmas of `AssemblyFirstStepSpaceTotal.lean`), so the room of each prefix is below
`2 ^ w`. This file proves the three room premises `hSp1`, `hSp2` and `hSp3` of the pieces
(`asmFirstStep_hSp1_std`, `asmFirstStep_hSp2_std`, `asmFirstStep_hSp3_std`).

The prefix lemmas need two facts on the scan of the batch, which hold before the step
(`asmFirstStep_newComps_room`):
* the new components are at most `2 |U|` (so at most `words`), and the deleted edges are at most
  `|U|`;
* the old slots and the buckets of the new components fit in `slotCap`. The side model counts the
  active buckets of all components below the caps, and the old slots are the active pairs.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **The scan before the step**: the old slots and the buckets of the new components fit in
`slotCap`, the new components are at most `2 |U|`, and the deleted edges at most `|U|`. -/
theorem asmFirstStep_newComps_room {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ}
    {Ψ : BundleTreeState depth → ℕ} {restH : ℕ} {tr : BundleTreeState depth}
    {ord : ℕ → List End} {U : List Update}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {mem : ℕ → ℕ}
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH ⟨tr, ord, y.vCap5, y.eCap5⟩ y mem)
    (hU : tr.cs.G.BatchIsValid U) :
    let sbF := scanBatchFold tr.cs.G (asmFirstScanStart mem y.cmpH y.comps tr.activeComps) U
    y.slots.length + newCompsBucketSum tr y.comps sbF.newComps ≤ y.slotCap ∧
      sbF.newComps.length ≤ 2 * U.length ∧ sbF.delEdges.length ≤ U.length := by
  intro sbF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps, hMod⟩ := hSide
  have hMaps' := hMaps
  obtain ⟨-, -, -, -, hCnd, hCiff, -⟩ := hMaps'
  obtain ⟨hSlotMap0, -, -, hScurInv, -, -, ⟨C_lsst, ℓ₀, hI, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    ⟨hTotCap, -⟩, -, hCross, -⟩ := hMod
  obtain ⟨hnd, hok, -, hlen, -, hdlen⟩ :=
    asmFirstStep_newComps_ok (cmpMap₀ := fun v => mem (y.cmpH + v)) hI hU hCnd hCiff
      (asmSdMaps_cmp_ok hMaps) hCross
  refine ⟨?_, hlen, hdlen⟩
  have hcard : y.slots.length = (activePairs tr).card := by
    rw [← List.toFinset_card_of_nodup hSlotMap0.1, ← hSlotMap0.image_eq,
      Finset.card_image_of_injOn fun q₁ hq₁ q₂ hq₂ heq => hSlotMap0.2.2.2.1 q₁ hq₁ q₂ hq₂ heq]
  have hle : y.slots.length + newCompsBucketSum tr y.comps sbF.newComps ≤
      min (min y.slotCap y.cap) y.slotsCap := by
    rw [hcard]
    exact (activeBuckets_disj_sum_le tr y.comps hCnd hCiff hScurInv.1 sbF.newComps hnd
      fun q hq => by
        obtain ⟨hc, hnot, _⟩ := hok q hq
        exact ⟨hc, by rwa [getElem!_pos y.comps q.1 hc]⟩).trans hTotCap
  exact le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))

end

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **The room of Phase 1** (`hSp1` of the pieces). -/
theorem asmFirstStep_hSp1_std {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ} :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words < 2 ^ w := by
  intro A hA
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  unfold AsmFsPre AsmFsPreRaw at hA
  dsimp only at hA ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hroom, -⟩ := hA
  have hle := asmFirstPhase1Space_le_std c₀ impl.cw capExp C_sp M N k x.vCap x.eCap L depth words
    editWords
  omega

/-- **The facts of the prefix lemmas, before the step**: the rep of the branch, the graph below
`eCap`, and the scan (`asmFirstStep_newComps_room`). The new components are at most `words`, the
buckets of the new components fit in `slotCap`, and the deleted edges are at most `words`. -/
theorem asmFirstStep_prefix_facts {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {space : ℕ → ℕ}
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A) :
    let sbF := scanBatchFold A.tr.cs.G
      (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U
    (∀ e ∈ A.tr.cs.G.E, e < A.x.eCap) ∧ sbF.newComps.length ≤ A.words ∧
      newCompsBucketSum A.tr A.x.xRest.comps sbF.newComps ≤ A.x.xRest.slotCap ∧
      sbF.delEdges.length ≤ A.words := by
  intro sbF
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  dsimp only [sbF] at hA ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -, hBat, hU, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, hGE, -⟩ := asmBrModelFacts_of_rep hR
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he hGE
  subst hv he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSide, -⟩ := hRA
  obtain ⟨hsl, hlen, hdlen⟩ := asmFirstStep_newComps_room hSide hU
  dsimp only at hsl hlen hdlen hGE ⊢
  exact ⟨hGE, by omega, by omega, by omega⟩

/-- **The room of Phases 1 and 2** (`hSp2` of the pieces), for the root query of space `1`. -/
theorem asmFirstStep_hSp2_std {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        newActTotalSpace tourBundleSpec 1 impl w A.x.xRest A.tr A.ord
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).newComps < 2 ^ w := by
  intro A hA
  obtain ⟨hGE, hNC, hSum, -⟩ := asmFirstStep_prefix_facts A hA
  have hle := asmFirstPhase12Space_le_std (c₀ := c₀) (k := A.k) (editWords := A.editWords) hC hγ
    hA.2.2.2.2.2.2.2.2.2.1 hA.1 hA.2.1 hGE hNC hSum
  have hroom := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  omega

/-- **The room of Phases 1 to 3** (`hSp3` of the pieces), for the root query of space `1`. -/
theorem asmFirstStep_hSp3_std {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        newActTotalSpace tourBundleSpec 1 impl w A.x.xRest A.tr A.ord
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).newComps +
        asmFirstPhase3Space A.x.xRest.slotCap A.x.vCap A.x.eCap A.words A.editWords
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).delEdges.length < 2 ^ w := by
  intro A hA
  obtain ⟨hGE, hNC, hSum, hDel⟩ := asmFirstStep_prefix_facts A hA
  have hle := asmFirstPhase123Space_le_std (c₀ := c₀) (k := A.k) (editWords := A.editWords) hC hγ
    hA.2.2.2.2.2.2.2.2.2.1 hA.1 hA.2.1 hGE hNC hSum hDel
  have hroom := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  omega

end

end MinCostFlow.SparseCore.Program
