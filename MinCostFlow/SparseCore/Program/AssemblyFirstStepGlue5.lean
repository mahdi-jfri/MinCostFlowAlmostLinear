module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue4
public import MinCostFlow.SparseCore.Program.AssemblyReemb
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase4Facts

import Mathlib.Tactic

/-!
# The inputs of Phase 3 of the first step (`AssemblyFirstStepGlue5`)

Phase 3 reads the batch, the order edits and the split entries, which the step gets as inputs,
and the list of the deleted edges, which the scan of Phase 1 writes. Phases 1 and 2 must keep
these cells. This file proves that they do.

* `asmFirstStep_phase2_keep`: Phase 2 keeps every cell below its heap pointer that is not a cell
  of the side record or of the tour before the step. Its post lists the cells that it may change:
  the bundle table, the spanners, the slot count, two cells of the table row of each new
  component, and the new slots of the slot list. All of them are cells of the side.
* `asmFirstStep_keep12`: so Phases 1 and 2 together keep every cell below `h` outside the side
  and the tour.
* `asmFirstStep_phase3_inputs`: the batch, the edits and the split entries are inputs outside the
  cells of the branch, so they are kept; the deleted edges lie in the block of the scan, which
  Phase 2 does not touch.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

public section

/-- **What Phase 2 keeps.** The frame of Phase 2 (`asmFirstNewAct_runs`) keeps a cell below its
heap pointer `h₂` unless it is a cell of the bundle table, of the spanners or of the tour, the slot
count, a cell of the table row of a new component, or a new slot of the slot list. When the new
components have indices in range and the new slots fit in the slot list, all these cells but
those of the tour are cells of the side record. -/
theorem asmFirstStep_phase2_keep {TR : ℕ → ℕ → DSRep AsmTourAbs} {depth : ℕ}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {restH tourH h₂ nSlots1 : ℕ} {newComps : List (ℕ × ℕ)}
    {mem₁ mem₂ : ℕ → ℕ}
    (hNC : ∀ q ∈ newComps, q.1 < y.comps.length) (hsl : nSlots1 ≤ y.slotsCap)
    (hfr : ∀ a < h₂,
        ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a →
        ¬ bucketFoot y.spanH y.xSpan a →
        ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a →
        a ≠ restH + ASM_SD_NSLOTS →
        (∀ k (_hk : k < newComps.length), ¬ (y.ctH + 3 * (newComps.getD k (0, 0)).1 + 1 ≤ a ∧
          a < y.ctH + 3 * (newComps.getD k (0, 0)).1 + 3)) →
        ¬ (y.slotsPtr + y.slots.length ≤ a ∧ a < y.slotsPtr + nSlots1) →
        mem₂ a = mem₁ a) :
    ∀ a < h₂, ¬ asmSdFoot restH y a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a →
      mem₂ a = mem₁ a := by
  intro a ha hs ht
  have h3 : ASM_SD_NSLOTS = 3 := rfl
  have h16 : ASM_SD_SIZE = 16 := rfl
  refine hfr a ha (fun hb => hs ⟨1, by decide, hb⟩) (fun hb => hs ⟨2, by decide, hb⟩) ht
    (fun he => hs ⟨0, by decide, show restH ≤ a ∧ a < restH + ASM_SD_SIZE by omega⟩)
    (fun k hk hin => ?_) (fun hin => hs ⟨3, by decide, Or.inl ⟨by omega, by omega⟩⟩)
  have hq : (newComps.getD k (0, 0)).1 < y.comps.length := by
    rw [List.getD_eq_getElem _ _ hk]
    exact hNC _ (List.getElem_mem hk)
  exact hs ⟨3, by decide, Or.inr ⟨2, by omega, by omega⟩⟩

/-- **Phases 1 and 2 keep the cells outside the side and the tour.** Let the scan of Phase 1 at
`h + 6` take `mem` to `mem₁` (`ScanMemAt`) and Phase 2 keep the cells below `h₂` outside the side
and the tour (`asmFirstStep_phase2_keep`). The component map and the active flags that the scan
writes are cells of the side. So every cell below `h` outside the side and the tour has the same
value in `mem₂` as in `mem`, when `h ≤ h₂`. -/
theorem asmFirstStep_keep12 {T : DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {y : AsmBrSide B5 depth} {tx₀ : T.τ} {restH tourH words h h₂ : ℕ}
    {mem mem₁ mem₂ : ℕ → ℕ} {sb : ScanBatchState}
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb)
    (hK2 : ∀ a < h₂, ¬ asmSdFoot restH y a → ¬ T.foot tourH tx₀ a → mem₂ a = mem₁ a)
    (hh : h ≤ h₂) :
    ∀ a < h, ¬ asmSdFoot restH y a → ¬ T.foot tourH tx₀ a → mem₂ a = mem a := by
  intro a ha hs ht
  rw [hK2 a (by omega) hs ht]
  exact asmFirstStep_scan_frame hM a (by omega)
    (fun v hv he => hs ⟨3, by decide, Or.inr ⟨0, by omega, by omega⟩⟩)
    (fun c hc he => hs ⟨3, by decide, Or.inr ⟨2, by omega, by omega⟩⟩)

/-- **The inputs of Phase 3 after Phases 1 and 2.** Let Phases 1 and 2 keep the cells below `h`
outside the side and the tour (`asmFirstStep_keep12`), and let Phase 2 keep the cells of the
block of the scan, which lie at `h` or above and below its heap pointer `h₂`. Then the batch, the
order edits and the split entries, which are inputs outside the side and the tour, are still in
place, and so is the list of the deleted edges that the scan wrote at
`h + 9 + 2 eCap + vCap + 4 words`. -/
theorem asmFirstStep_phase3_inputs {T : DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {y : AsmBrSide B5 depth} {tx₀ : T.τ} {restH tourH batch words edits editWords spPtr h h₂ : ℕ}
    {mem mem₁ mem₂ : ℕ → ℕ} {sb : ScanBatchState} {G : MGraph} {U : List Update}
    {ed : List OrdEdit} {L : List CompSplitEntry}
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb)
    (hK : ∀ a < h, ¬ asmSdFoot restH y a → ¬ T.foot tourH tx₀ a → mem₂ a = mem a)
    (hK2 : ∀ a, h ≤ a → a < h₂ → mem₂ a = mem₁ a)
    (hh₂ : h + 6 + asmFirstScanBatchSpace y.vCap5 y.eCap5 words ≤ h₂)
    (hdlen : sb.delEdges.length ≤ words)
    (hB : SmallBatchAt mem batch G U words) (hE : OrdEditsAt mem edits ed editWords)
    (hS : SplitEntriesAt mem spPtr L)
    (hBo : ∀ i < words, ¬ asmSdFoot restH y (batch + i) ∧ ¬ T.foot tourH tx₀ (batch + i))
    (hBl : batch + words ≤ h)
    (hEo : ∀ i < editWords, ¬ asmSdFoot restH y (edits + i) ∧ ¬ T.foot tourH tx₀ (edits + i))
    (hEl : edits + editWords ≤ h)
    (hSo : ∀ i < splitEntriesWords L,
      ¬ asmSdFoot restH y (spPtr + i) ∧ ¬ T.foot tourH tx₀ (spPtr + i))
    (hSl : spPtr + splitEntriesWords L ≤ h) :
    SmallBatchAt mem₂ batch G U words ∧ OrdEditsAt mem₂ edits ed editWords ∧
      SplitEntriesAt mem₂ spPtr L ∧
      ListAt mem₂ (h + 9 + 2 * y.eCap5 + y.vCap5 + 4 * words) sb.delEdges := by
  have hOut : ∀ p n, (∀ i < n, ¬ asmSdFoot restH y (p + i) ∧ ¬ T.foot tourH tx₀ (p + i)) →
      p + n ≤ h → ∀ a, p ≤ a → a < p + n → mem₂ a = mem a := by
    intro p n hpn hle a h1 h2
    obtain ⟨hs, ht⟩ := hpn (a - p) (by omega)
    rw [Nat.add_sub_cancel' h1] at hs ht
    exact hK a (by omega) hs ht
  refine ⟨smallBatchAt_of_agree hB (hOut _ _ hBo hBl), ordEditsAt_of_agree hE (hOut _ _ hEo hEl),
    splitEntriesAt_of_agree hS (hOut _ _ hSo hSl), ?_⟩
  have hD := hM.2.2.2.2.2.2.1
  have hb : scanDelEdgesBase (h + 6) y.vCap5 y.eCap5 words =
      h + 9 + 2 * y.eCap5 + y.vCap5 + 4 * words := by
    unfold scanDelEdgesBase; omega
  rw [hb] at hD
  refine listAt_of_agree hD fun a ha1 ha2 => hK2 a (by omega) ?_
  unfold asmFirstScanBatchSpace at hh₂
  omega

end

end MinCostFlow.SparseCore.Program
