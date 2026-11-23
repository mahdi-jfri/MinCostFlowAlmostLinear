module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitChain
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSideRep
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuild
import Mathlib.Tactic

/-!
# The post of the build (`AssemblyFirstInitPost`)

The run of the body of the build (`asmFirstInitBody_runs`) leaves four outputs: the front, the
middle, the back and the record stores. Here we turn them into the post of
`AsmFirstInitBuildAt.runs`, except the space and the cost.

The branch that the build leaves is `asmFiConc`: the embedding table at `h32`, the output graph
with handle `h30 + 5` and memory form at `h30 + 7`, the tour at `tourH` with the marks of the
back, and the bundle side `asmFiSide` at `o₁`. The readout data are not built here (part `1`), so
their fields are zero.

**The record words.** The record stores write `EMB`, `OUT` and `REST`. The front writes `TOUR`,
`VCAP`, `ECAP`, `TCAP` and `LW`, and the middle, the back and the record stores keep them, since
they lie below the tour and outside the record of the bundle side.

**The memory forms.** The record stores write only the record of the branch and the record of the
bundle side. So the embedding table, the output graph and the tour keep their memory form (all
three are local). The bundle side has its memory form by `asmFiSide_rep`.

**The six parts.** They lie in `[h, h33)`, in these cells:
the record in `[h, h + 16)`, the tour in `[tourH, o₁) ∪ [tblEnd, r26)`, the bundle side in
`[o₁, r20) ∪ [r25, tblEnd) ∪ [r26, r29)` (`asmFiSide_foot`), the output graph in `[h30, h31)` and
the embedding table in `[h32, h33)`. The heap pointers grow in this order:
`h + 16 < tourH < o₁ < r20 ≤ r25 ≤ tblEnd ≤ r26 ≤ r29 ≤ h30 < h31 ≤ h32 < h33`. So the parts do not
meet.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The branch that the build leaves.** The caps, the embedding table at `embH`, the output
graph with handle `h30 + 5` at `h30 + 7`, the tour, and the bundle side `y` at `o₁`. The readout
data are built later, so their handle and value are zero. -/
noncomputable def asmFiConc {depth : ℕ} (vCap eCap tCap Lw embH h30 tourH o₁ : ℕ)
    (yEmb : EmbConc) (sTour : OutTourAbs) (xTour : (tourAsmRep vCap eCap).τ)
    (y : AsmBrSide scProgB5 depth) : AsmBrConc tourAsmRep (AsmBrSide scProgB5 depth) where
  vCap := vCap
  eCap := eCap
  tCap := tCap
  L_w := Lw
  readH := 0
  yRead := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩, 0, 0, Read.emptyView⟩
  embH := embH
  yEmb := yEmb
  outH := h30 + 5
  gOut := h30 + 7
  tourH := tourH
  sTour := sTour
  xTour := xTour
  restH := o₁
  xRest := y

/-- **The cells of the bundle side** that the build leaves: the record and the maps in
`[o₁, r20)`, P5's table in `[r25, tblEnd)`, and P6's spanners in `[r26, r29)`. -/
theorem asmFiSide_foot {impl : SparsifyImpl} {w depth M k P vCap eCap h o₁ tourH cmpH ctH sH
      expPtr tblEnd walkPot lgFac L : ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {G : MGraph} {ℓ₀ : ℕ → ℝ} {mem regs : ℕ → ℕ} {st₁ st₂ : State}
    {xTour xT' : (tourAsmRep vCap eCap).τ} {comps : List (Finset ℕ)} {S D : List ℕ}
    {memC : ℕ → ℕ} {specs assigns : List (ℕ × ℕ)} {rList : List ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hM : AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
      (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D specs assigns st₁ tourH o₁ rList S5 m5
      tblEnd xT' x6 st₂) {a : ℕ}
    (ha : asmSdFoot o₁ (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6
      (sH + 2 + eCap + 5 * G.m) D.length G.m
      (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16) ctH comps
      (fun c => st₁.mem (ctH + 3 * c + 1))
      (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) walkPot lgFac) a) :
    (o₁ ≤ a ∧ a < st₂.regs 20) ∨ (st₂.regs 25 ≤ a ∧ a < tblEnd) ∨
      (st₂.regs 26 ≤ a ∧ a < st₂.regs 29) := by
  set B := asmFirstInitKeyBase P (mem (expPtr + 6)) L with hB
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hDm : D.length ≤ G.m := hF.slots.D_len.trans hF.slots.S_len
  have hcmpE := hF.cmpH_eq
  have hctE := hF.ctH_eq
  have hsHE := hF.sH_eq
  have e20 : st₂.regs 20 = sH + slotListSpace eCap G.m :=
    (hM.regs_lo 20 (by omega)).trans hF.r20
  have h25 := hM.r25
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h29 := hM.r29_lo
  obtain ⟨i, hi, hia⟩ := ha
  rcases i with _ | _ | _ | _ | i
  · simp only [asmSdPart, ASM_SD_SIZE] at hia
    left
    omega
  · exact Or.inr (Or.inl (hM.bun_foot a hia))
  · exact Or.inr (Or.inr (hM.span_foot a hia))
  · left
    simp only [asmSdPart] at hia
    rcases hia with hia | ⟨j, hj⟩
    · simp only [asmFiSide] at hia
      omega
    · have hvm : vCap ≤ 5 * vCap := by omega
      rcases j with _ | _ | _ | c <;> simp only [asmSdMapPart, asmFiSide] at hj
      · omega
      · omega
      · omega
      · obtain ⟨hc, h1, h2⟩ := hj
        obtain ⟨j, hj, -, ha⟩ := asmFi_csl_cell hF.slots hc h1 h2
        omega
  · omega

set_option maxHeartbeats 4000000 in
/-- **The post of the build**, from the four outputs of the body (`asmFirstInitBody_runs`) and the
model of the bundle side, except the space and the cost. The branch is `asmFiConc` with the side
`asmFiSide`; the record words, the memory forms, the cells of the six parts in `[h, h33)`, their
apartness, the zero memory from `h33` and the memory below `h` are as `AsmFirstInitBuildAt.runs`
asks. -/
theorem asmFirstInit_post {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ}
    {expEnd M N k P vCap eCap h o₁ tourH cmpH ctH sH expPtr tblEnd h30 h31 h32 h33 : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    {mem regs : ℕ → ℕ} {st₁ st₂ st₃ st₄ : State}
    {xTour xT' xT'' : (tourAsmRep vCap eCap).τ} {comps : List (Finset ℕ)} {S D : List ℕ}
    {memC : ℕ → ℕ} {C_lsst : ℝ} {ℓ : ℕ → ℝ} {specs assigns : List (ℕ × ℕ)} {rList : List ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap} {sTour' : OutTourAbs} {yEmb : EmbConc}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hM : AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
      (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D specs assigns st₁ tourH o₁ rList S5 m5
      tblEnd xT' x6 st₂)
    (hB : AsmFiBackOut (asmFiSP impl w M depth k eCap) tr ord vCap eCap tourH (st₂.regs 29) xT'
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range D.length)) (List.range D.length) st₂.mem st₂.regs h30 h31 h32 h33 sTour'
      xT'' yEmb st₃)
    (hR : AsmFiRecOut st₃.regs st₃.mem h o₁ st₄.mem)
    (r6 : regs 6 = M) (r11 : regs 11 = eCap) (r12 : regs 12 = depth)
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
    (hw33 : h33 < 2 ^ w) (hMw : M < 2 ^ w) (hdw : depth < 2 ^ w)
    (hspV : 2 * eCap + bundleSplitBudget k M + 1 < 2 ^ w)
    (hModel : AsmBrSideModel impl w depth L capExp limbMul walkPot ⟨tr, ord, vCap, eCap⟩
      (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
        D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16)
        ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
        (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) (walkPot tr)
        (bundleLogFactor M N))) :
    let X := asmBrSideRep scProgB5 impl w depth L capExp limbMul walkPot
    let x := asmFiConc vCap eCap (mem (expPtr + 7)) (mem (expPtr + 6)) h32 h30 tourH o₁ yEmb
      sTour' xT''
      (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
        D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16)
        ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
        (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) (walkPot tr)
        (bundleLogFactor M N))
    st₄.mem (h + ASM_BR_EMB) = x.embH ∧ st₄.mem (h + ASM_BR_OUT) = x.outH ∧
    st₄.mem (h + ASM_BR_TOUR) = x.tourH ∧ st₄.mem (h + ASM_BR_REST) = x.restH ∧
    st₄.mem (h + ASM_BR_VCAP) = x.vCap ∧ st₄.mem (h + ASM_BR_ECAP) = x.eCap ∧
    st₄.mem (h + ASM_BR_TCAP) = x.tCap ∧ st₄.mem (h + ASM_BR_LW) = x.L_w ∧
    x.vCap = vCap ∧ x.eCap = eCap ∧ x.tCap = mem (expPtr + 7) ∧ x.L_w = mem (expPtr + 6) ∧
    (embRep x.eCap).rep x.embH x.yEmb.view x.yEmb st₄.mem ∧
    (coreGraph tr.cs.G tr.cs.lsf).E ⊆ x.yEmb.view.dom ∧
    (∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, x.yEmb.view.emb e = tr.emb e) ∧
    (outGraphRep x.vCap x.eCap).rep x.outH tr.S_cur x.gOut st₄.mem ∧
    (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ x.vCap x.eCap).rep x.tourH x.sTour x.xTour
      st₄.mem ∧
    OutMarksOf x.sTour (outCoreOrder tr ord) tr.S_cur.E ∧
    X.rep x.restH ⟨tr, ord, vCap, eCap⟩ x.xRest st₄.mem ∧
    x.xRest.vCap5 = vCap ∧ x.xRest.eCap5 = eCap ∧
    x.xRest.slotCap ≤ 2 * (vCap + eCap + 2) ^ 2 ∧
    (∀ i < 6, i ≠ 1 → ∀ a, asmBrPart X h x i a → h ≤ a ∧ a < h33) ∧
    (∀ i < 6, ∀ i' < 6, i ≠ 1 → i' ≠ 1 → i ≠ i' → ∀ a, asmBrPart X h x i a →
      ¬ asmBrPart X h x i' a) ∧
    h + ASM_BR_SIZE ≤ h33 ∧
    ZeroFrom st₄.mem h33 ∧
    (∀ a < h, st₄.mem a = mem a) := by
  intro X x
  -- the layout
  have hT1 := hF.tourH_lo
  have hT2 := hF.tourH_hi
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hcmpE := hF.cmpH_eq
  have hctE := hF.ctH_eq
  have hsHE := hF.sH_eq
  have e20 : st₂.regs 20 = sH + slotListSpace eCap G.m :=
    (hM.regs_lo 20 (by omega)).trans hF.r20
  have e20' : st₁.regs 20 = sH + slotListSpace eCap G.m := hF.r20
  have h25 := hM.r25
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h29 := hM.r29_lo
  have h30e := hB.h30_eq
  have h31l := hB.h31_lo
  have h32e := hB.h32_eq
  have h33l := hB.h33_lo
  simp only [ASM_BR_SIZE] at hT1
  have hTf : ∀ a, (tourAsmRep vCap eCap).foot tourH xT' a →
      (tourH ≤ a ∧ a < o₁) ∨ (tblEnd ≤ a ∧ a < st₂.regs 26) := hM.tour_foot
  -- the record stores keep every cell outside the two records
  have hfr : ∀ a, (h + 16 ≤ a ∧ a < o₁) ∨ o₁ + 16 ≤ a ∨ a < h → st₄.mem a = st₃.mem a := by
    intro a ha
    exact hR.frame a (by simp only [ASM_BR_EMB]; omega) (by simp only [ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_REST]; omega) (by simp only [ASM_SD_SIZE]; omega)
  -- below the tour, the memory at the end is that after the front
  have hkeep1 : ∀ a, a < tourH → a ≠ h + ASM_BR_EMB → a ≠ h + ASM_BR_OUT →
      a ≠ h + ASM_BR_REST → st₄.mem a = st₁.mem a := by
    intro a ha h1 h2 h3
    rw [hR.frame a h1 h2 h3 (Or.inl (by omega)),
      hB.low a (by omega) fun hT => by rcases hTf a hT with h0 | h0 <;> omega]
    exact hM.keep a (by omega) (Or.inl ha)
  -- the six parts
  have hloc : ∀ i < 6, i ≠ 1 → ∀ a, asmBrPart X h x i a →
      (i = 0 ∧ h ≤ a ∧ a < h + 16) ∨ (i = 2 ∧ h32 ≤ a ∧ a < h33) ∨
      (i = 3 ∧ h30 ≤ a ∧ a < h31) ∨
      (i = 4 ∧ ((tourH ≤ a ∧ a < o₁) ∨ (tblEnd ≤ a ∧ a < st₂.regs 26))) ∨
      (i = 5 ∧ ((o₁ ≤ a ∧ a < st₂.regs 20) ∨ (st₂.regs 25 ≤ a ∧ a < tblEnd) ∨
        (st₂.regs 26 ≤ a ∧ a < st₂.regs 29))) := by
    intro i hi hi1 a ha
    rcases i with _ | _ | _ | _ | _ | _ | i
    · have ha' : h ≤ a ∧ a < h + ASM_BR_SIZE := ha
      simp only [ASM_BR_SIZE] at ha'
      exact Or.inl ⟨rfl, ha'⟩
    · exact absurd rfl hi1
    · exact Or.inr (Or.inl ⟨rfl, hB.emb_foot a ha⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hB.out_foot a ha⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hTf a (hB.tour_foot a ha)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, asmFiSide_foot (walkPot := walkPot tr)
        (lgFac := bundleLogFactor M N) hF hM ha⟩)))
    · omega
  -- the memory forms after the record stores
  have hEm := (embRep_local eCap h32 yEmb.view yEmb st₃.mem st₄.mem fun c hc =>
    (hfr c (by have := hB.emb_foot c hc; omega)).symm).1 hB.emb_rep
  have hOut := (outGraphRep_local vCap eCap (h30 + 5) tr.S_cur (h30 + 7) st₃.mem st₄.mem
    fun c hc => (hfr c (by have := hB.out_foot c hc; omega)).symm).1 hB.out_rep
  have hTour := (asmBrTourView_keep tourAsmRep_local ⟨tr, ord, vCap, eCap⟩ (s := sTour')
    (fun c hc => (hfr c (by rcases hTf c (hB.tour_foot c hc) with h0 | h0 <;> omega)).symm)).1
    hB.tour_rep
  have hSide := asmFiSide_rep hF hM hR (fun i hi => hB.regs_in i hi) r6 r11 r12
    (fun a h1 h2 h3 => (hfr a (Or.inr (Or.inl h1))).trans (hB.low a h2 h3)) hExp hcsG hG₀ hI
    hAC hGval hVlt hElt hbktM hcode hact hBw (by omega) hMw hdw hspV hModel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, hEm, hB.emb_dom, hB.emb_eq, hOut,
    hTour, hB.tour_marks, hSide, rfl, rfl, ?_, ?_, ?_, by simp only [ASM_BR_SIZE]; omega, ?_, ?_⟩
  · exact hR.emb.trans hB.r32
  · exact hR.out.trans (by rw [hB.r30]; rfl)
  · rw [hkeep1 _ (by simp only [ASM_BR_TOUR]; omega)
      (by simp only [ASM_BR_TOUR, ASM_BR_EMB]; omega)
      (by simp only [ASM_BR_TOUR, ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_TOUR, ASM_BR_REST]; omega)]
    exact hF.rec_tour
  · exact hR.rest
  · rw [hkeep1 _ (by simp only [ASM_BR_VCAP]; omega)
      (by simp only [ASM_BR_VCAP, ASM_BR_EMB]; omega)
      (by simp only [ASM_BR_VCAP, ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_VCAP, ASM_BR_REST]; omega)]
    exact hF.rec_vCap
  · rw [hkeep1 _ (by simp only [ASM_BR_ECAP]; omega)
      (by simp only [ASM_BR_ECAP, ASM_BR_EMB]; omega)
      (by simp only [ASM_BR_ECAP, ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_ECAP, ASM_BR_REST]; omega)]
    exact hF.rec_eCap
  · rw [hkeep1 _ (by simp only [ASM_BR_TCAP]; omega)
      (by simp only [ASM_BR_TCAP, ASM_BR_EMB]; omega)
      (by simp only [ASM_BR_TCAP, ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_TCAP, ASM_BR_REST]; omega)]
    exact hF.rec_tCap
  · rw [hkeep1 _ (by simp only [ASM_BR_LW]; omega)
      (by simp only [ASM_BR_LW, ASM_BR_EMB]; omega)
      (by simp only [ASM_BR_LW, ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_LW, ASM_BR_REST]; omega)]
    exact hF.rec_Lw
  · show eCap ≤ 2 * (vCap + eCap + 2) ^ 2
    nlinarith
  · intro i hi hi1 a ha
    rcases hloc i hi hi1 a ha with h0 | h0 | h0 | h0 | h0 <;> omega
  · intro i hi i' hi' hi1 hi1' hne a ha ha'
    rcases hloc i hi hi1 a ha with h0 | h0 | h0 | h0 | h0 <;>
      rcases hloc i' hi' hi1' a ha' with h1 | h1 | h1 | h1 | h1 <;> omega
  · intro a ha
    rw [hfr a (Or.inr (Or.inl (by omega)))]
    exact hB.zero a ha
  · intro a ha
    rw [hkeep1 a (by omega) (by simp only [ASM_BR_EMB]; omega) (by simp only [ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_REST]; omega)]
    exact hF.low a ha

end MinCostFlow.SparseCore.Program
