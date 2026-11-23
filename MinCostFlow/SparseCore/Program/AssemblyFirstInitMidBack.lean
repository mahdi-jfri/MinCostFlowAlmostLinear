module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMid
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBack
import MinCostFlow.MinRatio.GraphRead
import Mathlib.Tactic

/-!
# From the middle of the build to its back (`AssemblyFirstInitMidBack`)

The back of the build (`asmFirstInitBack_runs`) starts from `AsmFiBackIn`. Here we
build `AsmFiBackIn` from the end of the front (`AsmFiFrontOut`) and the end of the middle
(`AsmFiMidOut`). Most fields are bookkeeping on the layout of the heap:

`h < tourH < o₁ ≤ sH ≤ slotsPtr`, `slotsPtr + |D| ≤ r20 ≤ r25 ≤ tblEnd ≤ r26 ≤ r29`.

The graph `G` and P4's export lie below `h`. The front keeps the memory below `h`, and the middle
keeps the memory below `r20` outside the cells of the tour, which start at `tourH`. So both are
still in place. The slot list sits in `[slotsPtr, slotsPtr + |D|)`, which the middle also keeps.
The new tour lies in `[tourH, o₁)` and in `[tblEnd, r26)`, so it misses the graph, the slot list
and the spanners (which start at `r26`).

The model facts of the back (`hScurInv`, `hScurVal`, `hBD`, `hSE`, `hspanMatch`, `hGE`) and its room
in the word size are hypotheses here. The whole build supplies them at the init state.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-- **The input of the back from the front and the middle.** The registers come from the start
state through the front (`regs_in`) and the middle (`regs_lo`). The graph, the export and the
record word of the tour lie below `h`, the slot list below `r20` and above `o₁`, so the front and
the middle keep them. The rest is the layout of the heap and the fields of `AsmFiMidOut`. -/
theorem asmFiBackIn_of_mid {depth w j graph expPtr expEnd L capExp M N vCap eCap h k P o₁ tourH
    cmpH ctH sH tblEnd : ℕ} {impl : SparsifyImpl} {tr : BundleTreeState depth}
    {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ} {st st₁ st₂ : State}
    {xTour xT' : (tourAsmRep vCap eCap).τ} {comps : List (Finset ℕ)} {S D : List ℕ}
    {memC : ℕ → ℕ} {B : ℕ} {specs assigns : List (ℕ × ℕ)} {rList : List ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ st.mem st.regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hM : AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps B D specs
      assigns st₁ tourH o₁ rList S5 m5 tblEnd xT' x6 st₂)
    (r1 : st.regs 1 = j) (r2 : st.regs 2 = graph) (r4 : st.regs 4 = expPtr)
    (r10 : st.regs 10 = vCap) (r11 : st.regs 11 = eCap) (r14 : st.regs 14 = h)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ h)
    (hExp : CompBranchExportAt w st.mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h) (hcsG : tr.cs.G = G) (hVlt : ∀ v ∈ G.V, v < vCap)
    (hElt : ∀ e ∈ G.E, e < eCap) (hRot : HasRotOrder tr ord)
    (hScurInv : RestartScurModelInv tr) (hScurVal : tr.S_cur.IsValid) (hBD : BunDisjointInv tr)
    (hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E)
    (hspanMatch : ∀ q ∈ activePairs tr, ∃ (hs : slotOfD comps B D q < eCap) (d : DSHist),
      spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range D.length) ⟨slotOfD comps B D q, hs⟩ = some d ∧
      d.state (asmFiSP impl w M depth k eCap) = tr.dyn q)
    (hGE : ∀ q ∈ activePairs tr, (tr.dyn q).G.E = (tr.bun q).edges)
    (hw16 : 16 ≤ 2 ^ w) (hjW : j < 2 ^ w)
    (hroom : st₂.regs 29 + asmFiBackSpace (asmFiSP impl w M depth k eCap)
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range D.length)) (List.range D.length) vCap eCap tr.S_cur < 2 ^ w) :
    AsmFiBackIn (asmFiSP impl w M depth k eCap) eCap eCap tr ord G j graph expPtr expEnd L capExp
      M N vCap eCap h tourH xT' (sH + 2 + eCap + 5 * G.m) (st₂.regs 26) (st₂.regs 29)
      (List.range D.length) (slotOfD comps B D)
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range D.length)) x6 st₂ := by
  -- the layout of the heap
  have hr1 : ∀ i < 15, st₂.regs i = st.regs i := fun i hi =>
    (hM.regs_lo i (by omega)).trans (hF.regs_in i hi)
  have e20 : st₂.regs 20 = st₁.regs 20 := hM.regs_lo 20 (by omega)
  have hDm : D.length ≤ G.m := hF.slots.D_len.trans hF.slots.S_len
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hsH : o₁ + 16 ≤ sH := by
    rw [hF.sH_eq, hF.ctH_eq, hF.cmpH_eq]; omega
  have h20 := hF.r20
  have hT1 := hF.tourH_lo
  have hT2 := hF.tourH_hi
  have h25 := hM.r25
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h29 := hM.r29_lo
  have hsz : ASM_BR_TOUR < ASM_BR_SIZE := by simp only [ASM_BR_TOUR, ASM_BR_SIZE]; omega
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  -- the memory below `h` and the slot list are kept
  have hlow : ∀ a < h, st₂.mem a = st.mem a := fun a ha => by
    rw [hM.keep a (by rw [h20]; omega) (Or.inl (by omega)), hF.low a ha]
  have hslots : ∀ i < D.length, st₂.mem (sH + 2 + eCap + 5 * G.m + i) = i := fun i hi => by
    rw [hM.keep _ (by rw [h20]; omega) (Or.inr (by omega))]
    exact hF.slots.slots i hi
  -- the cells of the new tour
  have hTf : ∀ a, (tourAsmRep vCap eCap).foot tourH xT' a →
      (tourH ≤ a ∧ a < o₁) ∨ (tblEnd ≤ a ∧ a < st₂.regs 26) := hM.tour_foot
  refine
    { r1 := by rw [hr1 1 (by omega), r1]
      r2 := by rw [hr1 2 (by omega), r2]
      r4 := by rw [hr1 4 (by omega), r4]
      r10 := by rw [hr1 10 (by omega), r10]
      r11 := by rw [hr1 11 (by omega), r11]
      r14 := by rw [hr1 14 (by omega), r14]
      r23 := by rw [hM.regs_lo 23 (by omega), hF.r23]
      r24 := by rw [hM.regs_lo 24 (by omega), hF.r24, List.length_range]
      r26 := rfl
      r29 := rfl
      rec_tour := by
        rw [hM.keep _ (by rw [h20]; omega) (Or.inl (by omega))]
        exact hF.rec_tour
      rec_tour_lt := by omega
      hG := MinCostFlow.MinRatio.dynGraphAt_of_copy hG fun i hi => hlow _ (by omega)
      hG_le := by omega
      hExp := compBranchExportAt_congr (fun a _ ha => (hlow a (by omega)).symm) hExp
      hExp_le := by omega
      hlist := fun i hi => by
        rw [List.length_range] at hi
        rw [List.getElem_range]
        exact hslots i hi
      hlist_le := by rw [List.length_range]; omega
      hS6 := hM.span_rep
      hfoot6 := fun a ha => (hM.span_foot a ha).2
      hspan_le := by omega
      htour_rep := hM.tour_rep
      htour_foot := fun a ha => by rcases hTf a ha with h0 | h0 <;> omega
      htour_disj_G := fun a _ ha hT => by rcases hTf a hT with h0 | h0 <;> omega
      htour_disj_span := fun a ha hT => by
        have := (hM.span_foot a ha).1
        rcases hTf a hT with h0 | h0 <;> omega
      htour_disj_slots := fun a ha ha' hT => by
        rw [List.length_range] at ha'
        rcases hTf a hT with h0 | h0 <;> omega
      hz := hM.zero
      hcsG := hcsG
      hVlt := hVlt
      hElt := hElt
      hRot := hRot
      hScurInv := hScurInv
      hScurVal := hScurVal
      hBD := hBD
      hSE := hSE
      hMap := hM.slot_map
      hspanMatch := hspanMatch
      hGE := hGE
      hw16 := hw16
      hjW := hjW
      hSPe := le_refl _
      hroom := hroom }

end MinCostFlow.SparseCore.Program
