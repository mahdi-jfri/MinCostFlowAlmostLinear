module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSdMaps
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitRec
import Mathlib.Tactic

/-!
# The bundle side at the end of the build (`AssemblyFirstInitSideRep`)

At the end of the build, the bundle side `asmFiSide` sits at `o₁` (register `15`). Its four parts
lie in four intervals that do not meet:

`[o₁, o₁ + 16)` (the record), `[o₁ + 16, r20)` (the slot list and the maps),
`[r25, tblEnd)` (P5's table), `[r26, r29)` (P6's spanners),

and `r20 ≤ r25 ≤ tblEnd ≤ r26`. The record stores write the record. The back and the record stores
keep every other cell in `[o₁ + 16, r29)` outside the tour. So P5's table and P6's spanners keep
their memory form (both are local), and the slot list and the maps keep theirs
(`asmFiSide_maps`). `asmFiSide_rep` proves `AsmBrSideAt` from these facts and the model
(`asmFiSide_model`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

set_option maxHeartbeats 2000000 in
/-- **The memory form of the bundle side at the end of the build.** From the front, the middle,
the record of the side at `o₁` in the final memory `memF` (written by the record stores from the
registers `regs₄`, which are those at the end of the middle), and the final memory equal to the
memory after the middle on `[o₁ + 16, r29)` outside the tour, the side `asmFiSide` meets
`AsmBrSideAt`, given its model. -/
theorem asmFiSide_rep {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ}
    {Ψ : BundleTreeState depth → ℕ} {expEnd M N k P vCap eCap h o₁ tourH cmpH ctH sH expPtr
      tblEnd walkPot lgFac : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph}
    {ℓ₀ : ℕ → ℝ} {mem regs regs₄ mem₃ memF : ℕ → ℕ} {st₁ st₂ : State}
    {xTour xT' : (tourAsmRep vCap eCap).τ} {comps : List (Finset ℕ)} {S D : List ℕ}
    {memC : ℕ → ℕ} {C_lsst : ℝ} {ℓ : ℕ → ℝ} {specs assigns : List (ℕ × ℕ)} {rList : List ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hM : AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
      (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D specs assigns st₁ tourH o₁ rList S5 m5
      tblEnd xT' x6 st₂)
    (hR : AsmFiRecOut regs₄ mem₃ h o₁ memF) (hregs : ∀ i < 30, regs₄ i = st₂.regs i)
    (r6 : regs 6 = M) (r11 : regs 11 = eCap) (r12 : regs 12 = depth)
    (hkeep : ∀ a, o₁ + 16 ≤ a → a < st₂.regs 29 →
      ¬ (tourAsmRep vCap eCap).foot tourH xT' a → memF a = st₂.mem a)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hcsG : tr.cs.G = G) (hG₀ : tr.cs.G₀ = G) (hI : CompLSFInv C_lsst ℓ tr.cs)
    (hAC : tr.activeComps = largeComps k G) (hGval : G.IsValid)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hbktM : ∀ e ∈ G.E, bucketOf (tr.cs.lsf.wstr e * ℓ₀ e) = tr.origBucket e)
    (hcode : ∀ e ∈ G.E,
      bucketCode (tr.origBucket e) < asmFirstInitKeyBase P (mem (expPtr + 6)) L)
    (hact : ∀ q, q ∈ activePairs tr ↔ q.1 ∈ largeComps k G ∧
      ∃ e ∈ G.E, e ∉ tr.cs.lsf.F.F.E ∧ G.tail e ∈ q.1 ∧ tr.origBucket e = q.2)
    (hBw : asmFirstInitKeyBase P (mem (expPtr + 6)) L < 2 ^ w)
    (hw29 : st₂.regs 29 < 2 ^ w) (hMw : M < 2 ^ w) (hdw : depth < 2 ^ w)
    (hspV : 2 * eCap + bundleSplitBudget k M + 1 < 2 ^ w)
    (hModel : AsmBrSideModel impl w depth L capExp limbMul Ψ ⟨tr, ord, vCap, eCap⟩
      (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
        D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16)
        ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
        (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) walkPot lgFac)) :
    AsmBrSideAt scProgB5 impl w depth L capExp limbMul Ψ o₁ ⟨tr, ord, vCap, eCap⟩
      (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
        D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16)
        ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
        (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) walkPot lgFac) memF := by
  set B := asmFirstInitKeyBase P (mem (expPtr + 6)) L with hB
  -- the layout
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hDm : D.length ≤ G.m := hF.slots.D_len.trans hF.slots.S_len
  have hcmpE := hF.cmpH_eq
  have hctE := hF.ctH_eq
  have hsHE := hF.sH_eq
  have h20 := hF.r20
  have e20 : st₂.regs 20 = sH + slotListSpace eCap G.m := (hM.regs_lo 20 (by omega)).trans h20
  have h25 := hM.r25
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h29 := hM.r29_lo
  have hT2 := hF.tourH_hi
  have hTf : ∀ a, (tourAsmRep vCap eCap).foot tourH xT' a →
      (tourH ≤ a ∧ a < o₁) ∨ (tblEnd ≤ a ∧ a < st₂.regs 26) := hM.tour_foot
  -- registers at the record stores
  have q : ∀ i < 15, regs₄ i = regs i := fun i hi =>
    ((hregs i (by omega)).trans (hM.regs_lo i (by omega))).trans (hF.regs_in i hi)
  have q' : ∀ i, 15 ≤ i → i < 25 → regs₄ i = st₁.regs i := fun i h1 h2 =>
    (hregs i (by omega)).trans (hM.regs_lo i h2)
  -- the final memory keeps the slot list and the maps
  have hag : ∀ a, o₁ + 16 ≤ a → a < sH + slotListSpace eCap G.m → memF a = st₁.mem a := by
    intro a h1 h2
    rw [hkeep a h1 (by omega) fun hT => by rcases hTf a hT with h0 | h0 <;> omega]
    exact hM.keep a (by omega) (Or.inr (by omega))
  have hmaps := asmFiSide_maps (M := M) (bunH := st₂.regs 25) (spanH := st₂.regs 26)
    (S5 := S5) (m5 := m5) (x6 := x6) (walkPot := walkPot) (lgFac := lgFac) (mem' := memF) hF hExp hcsG hG₀ hI hAC
    hGval hVlt hElt hbktM hcode hact
    (by rw [hR.cmp, q' 16 (by omega) (by omega), hF.r16])
    (by rw [hR.bkt])
    (by rw [hR.ct, q' 18 (by omega) (by omega), hF.r18])
    (by rw [hR.ncomp, q' 17 (by omega) (by omega), hF.r17]) hag hBw
    (by rw [← e20]; omega)
  -- the cells of the maps lie in `[o₁ + 16, r20)`
  have hcellR : ∀ a, asmSdMapCell (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6
      (sH + 2 + eCap + 5 * G.m) D.length G.m (slotOfD comps B D) cmpH (o₁ + 16) ctH comps
      (fun c => st₁.mem (ctH + 3 * c + 1)) (fun c => cslList D B c) walkPot lgFac) a →
      o₁ + 16 ≤ a ∧ a < sH + 2 + eCap + 5 * G.m := by
    rintro a ⟨i, hi⟩
    have hvm : vCap ≤ 5 * vCap := by omega
    rcases i with _ | _ | _ | c <;> simp only [asmSdMapPart, asmFiSide] at hi
    · omega
    · omega
    · omega
    · obtain ⟨hc, h1, h2⟩ := hi
      obtain ⟨j, hj, -, ha⟩ := asmFi_csl_cell hF.slots hc h1 h2
      omega
  -- the bundle table and the spanners keep their memory form
  have hbun := (bunTableHeadroomRep_local eCap vCap eCap k (st₂.regs 25) S5 m5 st₂.mem memF
    fun a ha => by
      have := hM.bun_foot a ha
      exact (hkeep a (by omega) (by omega) fun hT => by
        rcases hTf a hT with h0 | h0 <;> omega).symm).1 hM.bun_rep
  have hspan := (bucketSpannerRep_local (asmFiSP impl w M depth k eCap) eCap (st₂.regs 26)
    (spanAfter (fun _ => none) (asmFirstInitSlotGraph S5) (List.range D.length)) x6 st₂.mem memF
    fun a ha => by
      have := hM.span_foot a ha
      exact (hkeep a (by omega) (by omega) fun hT => by
        rcases hTf a hT with h0 | h0 <;> omega).symm).1 hM.span_rep
  -- the slot list
  have hlist : ListAt memF (sH + 2 + eCap + 5 * G.m) (List.range D.length) := by
    intro i hi
    rw [List.length_range] at hi
    rw [List.getElem_range, hag _ (by omega) (by omega)]
    exact hF.slots.slots i hi
  -- the words of the record
  have v23 : regs₄ 23 = sH + 2 + eCap + 5 * G.m := (q' 23 (by omega) (by omega)).trans hF.r23
  have v24 : regs₄ 24 = D.length := (q' 24 (by omega) (by omega)).trans hF.r24
  have v25 : regs₄ 25 = st₂.regs 25 := hregs 25 (by omega)
  have v26 : regs₄ 26 = st₂.regs 26 := hregs 26 (by omega)
  have v27 : regs₄ 27 = bundleSplitBudget k M := (hregs 27 (by omega)).trans hM.r27
  have v28 : regs₄ 28 = 2 * eCap + bundleSplitBudget k M + 1 := (hregs 28 (by omega)).trans hM.r28
  have v6 : regs₄ 6 = M := (q 6 (by omega)).trans r6
  have v11 : regs₄ 11 = eCap := (q 11 (by omega)).trans r11
  have v12 : regs₄ 12 = depth := (q 12 (by omega)).trans r12
  have v16 : regs₄ 16 = cmpH := (q' 16 (by omega) (by omega)).trans hF.r16
  have v17 : regs₄ 17 = comps.length := (q' 17 (by omega) (by omega)).trans hF.r17
  have v18 : regs₄ 18 = ctH := (q' 18 (by omega) (by omega)).trans hF.r18
  have hbspl : bundleSplitBudget k M < 2 ^ w := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbun, hspan, hlist,
    by simp only [asmFiSide, List.length_range]; exact hDm, ?_, hmaps, hModel⟩
  · exact hR.bun.trans v25
  · exact hR.span.trans v26
  · exact hR.slots.trans v23
  · exact (hR.nslots.trans v24).trans (List.length_range).symm
  · exact hR.slotCap.trans v11
  · exact hR.eCap5.trans v11
  · exact hR.cap.trans v11
  · exact hR.spl.trans v12
  · exact hR.split.trans v27
  · exact hR.spv.trans v28
  · exact hR.spe.trans v11
  · exact hR.mmax.trans v6
  · intro i hi
    simp only [ASM_SD_SIZE] at hi
    have hrec := hR
    rcases hrec with ⟨-, -, -, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
      w15, -⟩
    have hDsl := hF.slots.D_len
    have hSsl := hF.slots.S_len
    clear hmaps hModel hbun hspan hlist hcellR hag hF hM hR hExp hI hact hcode hbktM hkeep hTf
      hregs q q'
    have hcm : cmpH ≤ ctH := by rw [hctE]; omega
    have hcs : ctH + 3 * comps.length ≤ sH := by rw [hsHE]
    have ho : o₁ + 16 ≤ cmpH := by rw [hcmpE]; omega
    clear hcmpE hctE hsHE
    simp only [ASM_SD_BUN, ASM_SD_SPAN, ASM_SD_SLOTS, ASM_SD_NSLOTS, ASM_SD_SLOTCAP, ASM_SD_ECAP5,
      ASM_SD_CAP, ASM_SD_SPL, add_zero] at w0 w1 w2 w3 w4 w5 w6 w7
    simp only [ASM_SD_SPLIT, ASM_SD_SPV, ASM_SD_SPE, ASM_SD_MMAX, ASM_SD_CMP, ASM_SD_BKT, ASM_SD_CT,
      ASM_SD_NCOMP] at w8 w9 w10 w11 w12 w13 w14 w15
    interval_cases i
    · rw [add_zero, w0, v25]; omega
    · rw [w1, v26]; omega
    · rw [w2, v23]; omega
    · rw [w3, v24]; omega
    · rw [w4, v11]; omega
    · rw [w5, v11]; omega
    · rw [w6, v11]; omega
    · rw [w7, v12]; omega
    · rw [w8, v27]; omega
    · rw [w9, v28]; omega
    · rw [w10, v11]; omega
    · rw [w11, v6]; omega
    · rw [w12, v16]; omega
    · rw [w13]; omega
    · rw [w14, v18]; omega
    · rw [w15, v17]; omega
  · intro i hi j hj hij a hia hja
    clear hmaps hModel hbun hspan hlist hag hExp hI hact hcode hbktM hkeep hR hregs q q'
    have hp : ∀ i < 4, asmSdPart o₁ (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26)
        x6 (sH + 2 + eCap + 5 * G.m) D.length G.m (slotOfD comps B D) cmpH (o₁ + 16) ctH comps
        (fun c => st₁.mem (ctH + 3 * c + 1)) (fun c => cslList D B c) walkPot lgFac) i a →
        (i = 0 ∧ o₁ ≤ a ∧ a < o₁ + 16) ∨ (i = 3 ∧ o₁ + 16 ≤ a ∧ a < st₂.regs 20) ∨
        (i = 1 ∧ st₂.regs 25 ≤ a ∧ a < tblEnd) ∨ (i = 2 ∧ st₂.regs 26 ≤ a ∧ a < st₂.regs 29) := by
      intro i hi ha
      rcases i with _ | _ | _ | _ | i
      · simp only [asmSdPart, ASM_SD_SIZE] at ha
        omega
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hM.bun_foot a ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hM.span_foot a ha⟩))
      · simp only [asmSdPart] at ha
        rcases ha with ha | ha
        · simp only [asmFiSide] at ha
          omega
        · have := hcellR a ha
          omega
      · omega
    rcases hp i hi hia with h0 | h0 | h0 | h0 <;> rcases hp j hj hja with h1 | h1 | h1 | h1 <;>
      omega

end MinCostFlow.SparseCore.Program
