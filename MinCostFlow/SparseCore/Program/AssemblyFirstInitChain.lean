module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMidBack
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitRec
import Mathlib.Tactic

/-!
# The run of the whole body of the build (`AssemblyFirstInitChain`)

The body of the build (`asmFirstInitBuildBody`) is the front, the middle, the back, the record
stores and the return of register `33`. Here we chain the four runs:
`asmFirstInitFront_runs`, `asmFirstInitMid_runs`, `asmFirstInitBack_runs_of_module` (through
`asmFiBackIn_of_mid`) and `asmFirstInitRec_runs`. The result `asmFirstInitBody_runs` gives the
four outputs (`AsmFiFrontOut`, `AsmFiMidOut`, `AsmFiBackOut`, `AsmFiRecOut`) and the cost: the
sum of the four bounds, with the potential of the tour passed from each part to the next.

The model state `tr` is general here. Its facts are hypotheses, as in the middle and the back.
The space is a hypothesis too: the front, the middle and the back fit below `2 ^ w` for every table
of P5 with at most `eCap` slots whose graphs meet `SpanGraphOK` (`hspB`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

set_option maxHeartbeats 4000000 in
/-- **The run of the body of the build**, from the start state of the build. -/
theorem asmFirstInitBody_runs {depth w bT b bSort bSpan bExport fExpM capExp M N vCap eCap
    expPtr expEnd h k L P cOrdPtr cWords graph lengths j cfH pos : ℕ} {impl : SparsifyImpl}
    {p : Program} {RL : ReadLib} {fCFRoot bRead bComp fExpD bBack : ℕ} (F : AsmFirstInitProcs)
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    -- the procedures of the front
    (hfT : p.procs[F.fTour]? = some (tourBranchInitStmt (tourInit bT)))
    (hpBk : p.HasAt F.fBkt (bucketTableModule F.fBkt))
    (hpC : p.HasAt F.fComp (compMapModule F.fComp))
    (hpS : p.HasAt F.fSlot (slotListModule F.fSlot))
    -- the procedures of the middle
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hfR : p.procs[F.fRoots]? = some (rootsListBody bSort))
    (hpT : HasTourProcs p bT)
    (hpB : p.HasAt b (bundleProcs b (tourOp bT 4) (tourOp bT 12) (tourOp bT 10)))
    (hfB : p.procs[F.fBun]? =
      some (asmFirstInitBunBody (b + bundleIdxTableInit) (b + bundleIdxInitSlots)))
    (hfS : p.procs[F.fSpan]? = some (asmFirstInitSpanBody fExpM (bSpan + bsIdxOp0 + 0)))
    (hfE : p.procs[fExpM]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hpSp : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    -- the procedures of the back
    (hfRT : F.fRootTbl = bBack) (hfS0 : F.fS0 = bBack + 1)
    (hfM : F.fMark = bBack + 7) (hfEm : F.fEmb = bBack + 9)
    (hRL : RL.Has p) (hpRead : p.HasAt bRead (readBranchProcs RL fCFRoot bRead))
    (hpComp : p.HasAt bComp (compMapModule bComp))
    (hfExpD : p.procs[fExpD]? = some asmFirstExportDynGraphStmt)
    (hpBack : p.HasAt bBack (asmFirstInitBackModule RL bRead bSpan bT bComp fExpD bBack))
    -- the model
    {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    (hcsG : tr.cs.G = G) (hGval : G.IsValid) (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap) (hk1 : 1 ≤ k)
    (hsub : ∀ e ∈ tr.cs.lsf.F.F.E, e ∈ tr.cs.G.E)
    (hbktM : ∀ e ∈ G.E, bucketOf (tr.cs.lsf.wstr e * ℓ₀ e) = tr.origBucket e)
    (hact : ∀ q, q ∈ activePairs tr ↔ q.1 ∈ largeComps k G ∧
      ∃ e ∈ G.E, e ∉ tr.cs.lsf.F.F.E ∧ G.tail e ∈ q.1 ∧ tr.origBucket e = q.2)
    (hbun : ∀ q, tr.bun q = initBundleFor tr.cs ord
      (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket q.1 q.2) k)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hokM : ∀ q ∈ activePairs tr, SpanGraphOK (asmFiSP impl w M depth k eCap) (tr.initBunG q))
    (hdyn : ∀ q, tr.dyn q = DSHist.state (asmFiSP impl w M depth k eCap) ⟨tr.initBunG q, []⟩)
    (hScurInv : RestartScurModelInv tr) (hScurVal : tr.S_cur.IsValid) (hBD : BunDisjointInv tr)
    (hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E)
    (hGE : ∀ q ∈ activePairs tr, (tr.dyn q).G.E = (tr.bun q).edges)
    -- the memory at the start
    (hOrdAt : OrdListAt mem cOrdPtr ord cWords) (hOrdLe : cOrdPtr + cWords ≤ h)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h)
    (hGat : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ h)
    (hlen : BranchLengthsAt mem lengths eCap L P h G ℓ₀) (hz : ZeroFrom mem h)
    -- the words
    (hw10 : 10 ≤ w) (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hBw : asmFirstInitKeyBase P (mem (expPtr + 6)) L < 2 ^ w)
    (hkw : vCap * asmFirstInitKeyBase P (mem (expPtr + 6)) L < 2 ^ w)
    (hMw : 56 * M + k < 2 ^ w) (hdw : depth < 2 ^ w) (hjW : j < 2 ^ w)
    (hspB : ∀ (S5 : Fin eCap → Option BundleState) (n : ℕ), n ≤ eCap →
      (∀ s ∈ List.range n,
        SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) →
      h + asmFiFrontSpace vCap eCap (mem (expPtr + 6)) L +
        asmFiMidSpace (asmFiSP impl w M depth k eCap) vCap eCap +
        asmFiBackSpace (asmFiSP impl w M depth k eCap)
          (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
            (List.range n)) (List.range n) vCap eCap tr.S_cur < 2 ^ w) :
    ∃ o₁ tourH xTour cmpH ctH sH comps S D memC st₁,
      AsmFiFrontOut w depth tr ord G ℓ₀ mem
        (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
          mem pos).regs expPtr k L P vCap eCap h o₁ tourH xTour cmpH ctH sH comps S D memC st₁ ∧
    ∃ rList S5 m5 tblEnd xT' x6 st₂,
      AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
        (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D
        (slotSpecsL memC cmpH (o₁ + 16) (asmFirstInitKeyBase P (mem (expPtr + 6)) L) G S D)
        (slotAssignsL memC cmpH (o₁ + 16) (asmFirstInitKeyBase P (mem (expPtr + 6)) L) G S D)
        st₁ tourH o₁ rList S5 m5 tblEnd xT' x6 st₂ ∧
    ∃ h30 h31 h32 h33 sTour' xT'' yEmb st₃,
      AsmFiBackOut (asmFiSP impl w M depth k eCap) tr ord vCap eCap tourH (st₂.regs 29) xT'
        (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
          (List.range D.length)) (List.range D.length) st₂.mem st₂.regs h30 h31 h32 h33 sTour'
        xT'' yEmb st₃ ∧
    ∃ st₄ c,
      st₄.regs = st₃.regs ∧ AsmFiRecOut st₃.regs st₃.mem h o₁ st₄.mem ∧
      Runs w p ω (asmFirstInitBuildBody F)
        (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
          mem pos) (.returned h33) st₄ c ∧
      c + (bunTableHeadroomRep eCap vCap eCap k).phi (st₂.regs 25) m5 st₂.mem +
          specPhi (asmFiSP impl w M depth k eCap)
            (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
              (List.range D.length)) +
          (tourAsmRep vCap eCap).phi tourH xT'' st₃.mem ≤
        (tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
          bucketTableCost (mem (expPtr + 6)) L G.m + compMapCost G.n G.m +
          slotListCost G.m (components G).card (mem (mem (expPtr + 1) + 2)) + 200) +
        (rootsListCost rList.length +
          bundleInitSlotsCost tourBundleSpec eCap D.length S.length (outCoreOrder tr ord) rList +
          bunPhiMul * (2 * S.length) +
          ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum +
          ((List.range D.length).map fun s =>
            spanActivateCost (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)).sum +
          200 * D.length + 600) +
        (rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
          (840 * (rebuildSize (asmFiSP impl w M depth k eCap)
            (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
              (List.range D.length)) (List.range D.length) + D.length + 1) +
            130 * tr.cs.lsf.F.R.card + 200) +
          (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
            tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
          (30 * G.m + embRefreshMul * (embRefreshSizeAt (asmFiSP impl w M depth k eCap)
            (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
              (List.range D.length)) (List.range D.length) + D.length + 1) + 80) + 100) +
        130 := by
  set st₀ := startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth,
    lengths, h] mem pos with hst₀
  have hw16 : 16 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw10)
  -- the front
  obtain ⟨hfDle, hfe, hfeL⟩ := asmFi_forestEdges_of_export hExp hExpLe hsub
  have hcode := asmFi_code_lt hExp hcsG hlen
  have hsp0 := hspB (fun _ => none) 0 (Nat.zero_le _) (by simp)
  have hspF : h + asmFiFrontSpace vCap eCap (mem (expPtr + 6)) L < 2 ^ w := by omega
  have hcodeM : ∀ e ∈ G.E, bucketCode (tr.origBucket e) <
      asmFirstInitKeyBase P (mem (expPtr + 6)) L := fun e he => hbktM e he ▸ hcode e he
  obtain ⟨o₁, tourH, xTour, cmpH, ctH, sH, comps, S, D, memC, st₁, c₁, hrun₁, hF, hc₁⟩ :=
    asmFirstInitFront_runs (st := st₀) (tr := tr) (ord := ord) (ℓ₀ := ℓ₀) (cWords := cWords)
      (expEnd := expEnd) (capExp := capExp) (M := M) (N := N) (graph := graph)
      (cOrdPtr := cOrdPtr) (expPtr := expPtr) (k := k) (L := L) (P := P) (vCap := vCap)
      (eCap := eCap) (lengths := lengths) (h := h) F ω hpT hfT hw10 hpBk hpC hpS
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcsG hGval hRot hVlt hElt hw hOrdAt hOrdLe hExp
      hExpLe hGat hGle hlen hfDle (by rw [← hcsG]; exact hfe) hfeL hcode hz hspF hBw hkw
  replace hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem st₀.regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁ := hF
  refine ⟨o₁, tourH, xTour, cmpH, ctH, sH, comps, S, D, memC, st₁, hF, ?_⟩
  -- the middle
  have hDm : D.length ≤ G.m := hF.slots.D_len.trans hF.slots.S_len
  have hGm : G.m ≤ eCap := card_le_of_lt_cap hElt
  have hr20 := hF.r20_le
  obtain ⟨rList, S5, m5, tblEnd, xT', x6, st₂, c₂, hrun₂, hM, hc₂⟩ :=
    asmFirstInitMid_runs (impl := impl) (M := M) (N := N) (capExp := capExp) (expEnd := expEnd)
      (expPtr := expPtr) (k := k) (vCap := vCap) (eCap := eCap) (depth := depth) (h := h)
      F ω hpSort hfR hpT hpB hfB hfS hfE hpExport hpSp hF rfl rfl rfl rfl rfl rfl rfl hw10 hcsG
      hGval hRot hVlt hElt hk1 hExp hExpLe hbktM hcodeM hact hbun hG hokM hMw hdw
      (by rw [hF.r20]; omega)
  refine ⟨rList, S5, m5, tblEnd, xT', x6, st₂, hM, ?_⟩
  -- the back
  have hspan := asmFirstInit_spanMatch (asmFiSP impl w M depth k eCap) (tr := tr) hM.slot_map hM.bun_match hG hdyn
  have hsp2 := hspB S5 D.length (by omega) hM.span_ok
  have h29 := hM.r29_hi
  have hIn := asmFiBackIn_of_mid (j := j) (graph := graph) (expEnd := expEnd) (N := N)
    (capExp := capExp) (h := h) (expPtr := expPtr) (st := st₀) hF hM rfl rfl rfl rfl rfl rfl hGat hGle hExp hExpLe hcsG hVlt hElt hRot
    hScurInv hScurVal hBD hSE (fun q hq => by
      obtain ⟨hs, d, hd, hst, -⟩ := hspan q hq
      exact ⟨hs, d, hd, hst⟩) hGE hw16 hjW (by rw [hF.r20] at h29; omega)
  obtain ⟨h30, h31, h32, h33, sTour', xT'', yEmb, st₃, c₃, hrun₃, hB, hc₃⟩ :=
    asmFirstInitBack_runs_of_module (P := asmFiSP impl w M depth k eCap) (slotCap := eCap)
      (cap := eCap) (tr := tr) (st := st₂) (p := p) (RL := RL) (bSpan := bSpan) (bTour := bT)
      (fExp := fExpD) (bBack := bBack) F ω hfRT hfS0 hfM hfEm hRL hpRead hpComp hpT hfExpD hpSp
      hpBack hIn
  refine ⟨h30, h31, h32, h33, sTour', xT'', yEmb, st₃, hB, ?_⟩
  -- the record stores
  have e14 : st₃.regs 14 = h := by
    rw [hB.regs_in 14 (by omega), hM.regs_lo 14 (by omega), hF.regs_in 14 (by omega)]; rfl
  have e15 : st₃.regs 15 = o₁ := by
    rw [hB.regs_in 15 (by omega), hM.regs_lo 15 (by omega), hF.r15]
  have hT1 := hF.tourH_lo
  have hT2 := hF.tourH_hi
  have hspace := hB.h33_space
  have h30lo : h30 + 7 ≤ h33 := by have := hB.h31_lo; have := hB.h32_eq; have := hB.h33_lo; omega
  have hrl := hM.r29_lo
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h25 := hM.r25
  have hroom := hIn.hroom
  have e20 : st₁.regs 20 = sH + slotListSpace eCap G.m := hF.r20
  have hsH : o₁ + 16 ≤ sH := by rw [hF.sH_eq, hF.ctH_eq, hF.cmpH_eq]; omega
  have hh33 : h33 < 2 ^ w := by omega
  have ho29 : o₁ + 16 ≤ st₂.regs 29 := by omega
  have h29' : st₂.regs 29 ≤ h33 := by have := hB.h30_eq; omega
  simp only [ASM_BR_SIZE] at hT1
  obtain ⟨st₄, c₄, hrun₄, hregs₄, hc₄, hR⟩ := asmFirstInitRec_runs (w := w) (p := p) (ω := ω) e14 e15
    (by simp only [ASM_BR_SIZE]; omega) (by simp only [ASM_SD_SIZE]; omega)
    (by rw [hB.r30]; exact lt_of_le_of_lt (by omega : h30 + 5 ≤ h33) hh33)
  have hret : Runs w p ω (.ret (.reg 33)) st₄ (.returned h33) st₄ 2 :=
    runs_ret_iff.mpr ⟨h33, by rw [Expr.eval_reg_of_eq]; rw [hregs₄, hB.r33], rfl, rfl, rfl⟩
  have hrun := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrun₁, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrun₂,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrun₃, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrun₄, hret,
      rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st₄, _, hregs₄, hR, hrun, ?_⟩
  simp only [hst₀, startState] at hc₁
  simp only [List.length_range] at hc₃
  clear * - hc₁ hc₂ hc₃ hc₄
  omega

end MinCostFlow.SparseCore.Program
