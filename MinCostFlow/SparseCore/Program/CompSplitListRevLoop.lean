module

public import MinCostFlow.SparseCore.Program.CompSplitListBranchBase
import MinCostFlow.SparseCore.CompLSFBridge
import WordRAM.Tactic

/-!
# Per-Branch Reverse Union-Find Loop (`CompSplitListRevLoop`)

Defines and verifies `compRevLoopStmt` / `compRevLoop_runs`: iterates `idx = t - 1` down to `0`
over the sorted released forest-edge list `D_sorted` in `dBuf`, reads `(ru, rv)` via
`compEdgeEndRootsProc`, runs two `compUFInitFindProc` calls and one `compUFPairUnionProc`
(`doUnion = 1`) call, writes `[1, D_sorted[idx], kept, fresh]` at
`spBufJ + 4 * (spCnt + hasInp + idx)` matching `releasesSplitEntries`, and advances `RevUFInv`
from `(S1 j).RF.F` up to `forestAfterInput (S j).RF.F u`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Reverse Union-Find loop over sorted released edges `dBuf[r20 - 1]` down to `dBuf[0]`. -/
def compRevLoopStmt (bEndRoots bUFInitFind bUFPairUnion : ℕ) : Stmt :=
  .loop (.bin .lt (.const 0) (.reg 20))
    (.assign 20 (.bin .sub (.reg 20) (.const 1)) ;;
     .assign 21 (.load (.bin .add (.reg 15) (.reg 20))) ;;
     .call 23 bEndRoots [.reg 0, .reg 1, .reg 21, .reg 17] ;;
     .assign 22 (.load (.reg 17)) ;;
     .assign 23 (.load (.bin .add (.reg 17) (.const 1))) ;;
     .call 25 bUFInitFind [.reg 12, .reg 13, .reg 22] ;;
     .call 26 bUFInitFind [.reg 12, .reg 13, .reg 23] ;;
     .assign 27 (.bin .add (.reg 10)
       (.bin .mul (.const 4) (.bin .add (.bin .add (.reg 24) (.reg 19)) (.reg 20)))) ;;
     .call 23 bUFPairUnion
       [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 1, .reg 21, .const 1])

lemma compRevLoopStmt_noRand (a b c : ℕ) : (compRevLoopStmt a b c).NoRand := by
  simp [compRevLoopStmt, Stmt.NoRand]

/-! ## 1. Pure helpers -/

/-- `CompLSFRepDirty` depends only on memory inside `[b, x.endAddr)`. -/
lemma compLSFRepDirty_of_agree {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {touched : List ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hrep : CompLSFRepDirty W k b S x touched mem₁)
    (hag : ∀ a, b ≤ a → a < x.endAddr → mem₂ a = mem₁ a) :
    CompLSFRepDirty W k b S x touched mem₂ := by
  obtain ⟨hk, h1, h2, h3, h4, h5, h6, h7, h8, hTE, hhdr, hBr, hm0, hT,
    hComp, hEf, hVC, hEC, hCI, hGh, hTM, hOne, hWins, hDisj⟩ := hrep
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hStatAg : ∀ a, b ≤ a → a < b + compStaticSize x.vCap x.eCap x.L_w → mem₂ a = mem₁ a :=
    fun a ha1 ha2 => hag a ha1 (by omega)
  have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
  refine ⟨hk, h1, h2, h3, h4, h5, h6, h7, h8, hTE, ?_, hBr, hm0, hT,
    ?_, hEf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDisj⟩
  · have hh : ∀ off < compHdrSize, mem₂ (b + off) = mem₁ (b + off) := fun off hoff =>
      hStatAg (b + off) (by omega) (by dsimp only [compStaticSize, compGhostSize, compHdrSize] at *; omega)
    rcases hhdr with ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23⟩
    exact ⟨(hh _ (by decide)).trans p0, (hh _ (by decide)).trans p1, (hh _ (by decide)).trans p2,
      (hh _ (by decide)).trans p3, (hh _ (by decide)).trans p4, (hh _ (by decide)).trans p5,
      (hh _ (by decide)).trans p6, (hh _ (by decide)).trans p7, (hh _ (by decide)).trans p8,
      (hh _ (by decide)).trans p9, (hh _ (by decide)).trans p10, (hh _ (by decide)).trans p11,
      (hh _ (by decide)).trans p12, (hh _ (by decide)).trans p13, (hh _ (by decide)).trans p14,
      (hh _ (by decide)).trans p15, (hh _ (by decide)).trans p16, (hh _ (by decide)).trans p17,
      (hh _ (by decide)).trans p18, (hh _ (by decide)).trans p19, (hh _ (by decide)).trans p20,
      (hh _ (by decide)).trans p21, (hh _ (by decide)).trans p22, (hh _ (by decide)).trans p23⟩
  · intro c; obtain ⟨a1, a2, a3, a4⟩ := hComp c
    refine ⟨(hStatAg _ (by dsimp [compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans a1,
      (hStatAg _ (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans a2,
      (hStatAg _ (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans a3,
      fun hm => by
        obtain ⟨ec, he1, he2, he3⟩ := a4 hm
        exact ⟨ec, he1, (hStatAg _ (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
          (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans he2, he3⟩⟩
  · intro c v hv
    have hvlt : v < x.vCap := hT.hVlt v (by rw [← (hBr.choose_spec ⟨0, hk⟩).1.hV_eq]; exact Finset.mem_biUnion.mpr ⟨_, hT.compOf_mem c, hv⟩)
    exact (hStatAg _ (by dsimp [compVCompBase, compHdrSize]; omega)
      (by dsimp [compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hVC c v hv)
  · intro e he; have helt : e < x.eCap := hT.hElt e he
    exact ⟨(hStatAg _ (by dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hEC e he).1,
      (hStatAg _ (by dsimp [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hEC e he).2⟩
  · intro e he
    exact ⟨(hStatAg _ (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hCI e he).1,
      (hStatAg _ (by dsimp [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
        (by dsimp [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hCI e he).2⟩
  · set gPtr := compGhostBase b x.vCap x.eCap
    have hgIn : ∀ off < compGhostSize x.vCap x.eCap, mem₂ (gPtr + off) = mem₁ (gPtr + off) :=
      fun off hoff => hStatAg (gPtr + off)
        (by dsimp [gPtr, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base,
          compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
          compVCompBase, compHdrSize]; omega)
        (by dsimp [gPtr, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
          compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compStaticSize, compHdrSize] at hoff ⊢; omega)
    refine ⟨fun v hv => ?_, fun e he hcr => ?_⟩
    · obtain ⟨g1, g2, g3, g4⟩ := hGh.1 v hv
      refine ⟨g1.of_agree (hgIn v (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := g1.2.1 e he
            simpa [ghostTPrevBase, Nat.add_assoc] using hgIn (4 * x.vCap + e) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := g1.2.1 e he
            simpa [ghostTNextBase, Nat.add_assoc] using hgIn (4 * x.vCap + x.eCap + e) (by dsimp [compGhostSize]; omega)),
        by have h := hgIn (x.vCap + v) (by dsimp [compGhostSize]; omega)
           simpa [ghostTCntBase, Nat.add_assoc] using h.trans (by simpa [ghostTCntBase, Nat.add_assoc] using g2),
        g3.of_agree
          (by simpa [ghostHHeadBase, Nat.add_assoc] using hgIn (2 * x.vCap + v) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := g3.2.1 e he
            simpa [ghostHPrevBase, Nat.add_assoc] using hgIn (4 * x.vCap + 3 * x.eCap + e) (by dsimp [compGhostSize]; omega))
          (fun e he => by
            have helt := g3.2.1 e he
            simpa [ghostHNextBase, Nat.add_assoc] using hgIn (4 * x.vCap + 4 * x.eCap + e) (by dsimp [compGhostSize]; omega)),
        by have h := hgIn (3 * x.vCap + v) (by dsimp [compGhostSize]; omega)
           simpa [ghostHCntBase, Nat.add_assoc] using h.trans (by simpa [ghostHCntBase, Nat.add_assoc] using g4)⟩
    · have helt := hT.hElt e he
      exact ⟨by have h := hgIn (4 * x.vCap + 2 * x.eCap + e) (by dsimp [compGhostSize]; omega)
                simpa [ghostTVertBase, Nat.add_assoc] using h.trans (by simpa [ghostTVertBase, Nat.add_assoc] using (hGh.2 e he hcr).1),
        by have h := hgIn (4 * x.vCap + 5 * x.eCap + e) (by dsimp [compGhostSize]; omega)
           simpa [ghostHVertBase, Nat.add_assoc] using h.trans (by simpa [ghostHVertBase, Nat.add_assoc] using (hGh.2 e he hcr).2)⟩
  · intro c hc
    exact (hStatAg _ (by dsimp [compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compGhostSize]; omega)
      (by dsimp [compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hTM c hc)
  · exact ⟨(hStatAg _ (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compGhostSize]; omega)
      (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans hOne.1,
      fun i hi1 hi2 => (hStatAg _ (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compGhostSize]; omega)
        (by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize]; omega)).trans (hOne.2 i hi1 hi2)⟩
  · intro ec j; obtain ⟨hm, hwr, hv, he, hl, hge, hle⟩ := hWins ec j
    have hidx_lt : ec.1 * k + j.1 < x.m0Total * k := by
      calc ec.1 * k + j.1 < ec.1 * k + k := Nat.add_lt_add_left j.2 _
        _ = (ec.1 + 1) * k := by ring
        _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
    have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
    refine ⟨(hag _ (by dsimp [compHandlesBase, compStaticSize]; omega)
        (by dsimp [compTablesEnd] at hTE; omega)).trans hm,
      (lsfRep_local W.h _ _ _ mem₁ mem₂ fun a ha =>
        (hag a (le_trans hb_le_te (le_trans hge ha.1)) (lt_of_lt_of_le ha.2 hle)).symm).1 hwr,
      hv, he, hl, hge, hle⟩

lemma ufInitOne_preserves_active {isOld : ℕ → Bool} {U : RevUFState} {r a : ℕ}
    (ha : 1 ≤ U.sz a) :
    (ufInitOne isOld U r).sz a = U.sz a ∧ (ufInitOne isOld U r).par a = U.par a := by
  by_cases h0 : U.sz r = 0
  · have hne : a ≠ r := fun h => by rw [h] at ha; omega
    simp [ufInitOne, h0, Function.update_of_ne hne]
  · simp [ufInitOne, h0]

private lemma foldl_eraseForestEdge_take_succ (F : MGraph) (D : List ℕ) {i : ℕ} (hi : i < D.length) :
    (D.take (i + 1)).foldl eraseForestEdge F =
      eraseForestEdge ((D.take i).foldl eraseForestEdge F) D[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma foldl_eraseForestEdge_props (F : MGraph) (L : List ℕ) :
    (L.foldl eraseForestEdge F).V = F.V ∧
    (L.foldl eraseForestEdge F).E = F.E \ L.toFinset ∧
    (L.foldl eraseForestEdge F).tail = F.tail ∧
    (L.foldl eraseForestEdge F).head = F.head := by
  induction L generalizing F with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (eraseForestEdge F x)
    refine ⟨h1, ?_, h3, h4⟩
    rw [h2]; ext e; simp only [Finset.mem_sdiff, Finset.mem_erase,
      List.toFinset_cons, Finset.mem_insert, not_or]; tauto

private lemma revUFInv_of_same_graph {F₁ F₂ : MGraph} {RF' : RootedForest} {R_old : Finset ℕ}
    {U : RevUFState}
    (hV : F₁.V = F₂.V) (hE : F₁.E = F₂.E)
    (hEnd : ∀ e ∈ F₁.E, F₁.tail e = F₂.tail e ∧ F₁.head e = F₂.head e)
    (hU : RevUFInv F₁ RF' R_old U) : RevUFInv F₂ RF' R_old U := by
  have hConn : ∀ u v, F₁.Connected u v ↔ F₂.Connected u v := fun u v => by
    have hdir : ∀ (A B : MGraph), A.E = B.E →
        (∀ e ∈ A.E, A.tail e = B.tail e ∧ A.head e = B.head e) →
        ∀ {x y P}, A.IsWalk x y P → B.IsWalk x y P := by
      intro A B hEB hEndB x y P hP
      induction hP with
      | nil z => exact .nil z
      | @cons _ _ z _ he hs _ ih =>
        have h1 := hEndB z.1 he
        have hsrc : B.src z = A.src z := by rcases z with ⟨e, _ | _⟩ <;> simp [MGraph.src, h1.1, h1.2]
        have hdst : B.dst z = A.dst z := by rcases z with ⟨e, _ | _⟩ <;> simp [MGraph.dst, h1.1, h1.2]
        exact .cons (hEB ▸ he) (hsrc.trans hs) (hdst ▸ ih)
    exact ⟨fun ⟨P, hP⟩ => ⟨P, hdir F₁ F₂ hE hEnd hP⟩,
      fun ⟨P, hP⟩ => ⟨P, hdir F₂ F₁ hE.symm (fun e he =>
        ⟨(hEnd e (hE ▸ he)).1.symm, (hEnd e (hE ▸ he)).2.symm⟩) hP⟩⟩
  have hComp : ∀ x, compOf F₁ x = compOf F₂ x := fun x => by
    ext y; simp only [compOf, Finset.mem_filter, hV, hConn]
  refine ⟨hU.hNotR, fun r hr hz => by rw [← hComp r]; exact hU.hUntouched r hr hz, hU.hSzLe,
    fun r hr ha =>
      let ⟨h1, h2, h3, h4⟩ := hU.hActivePar r hr ha
      ⟨h1, h2, (hConn _ _).mp h3, h4⟩,
    fun r hr ha hp => by have := hU.hRootMeta r hr ha hp; rwa [hComp r] at this,
    fun r₁ hr₁ r₂ hr₂ ha₁ hp₁ ha₂ hp₂ hc =>
      hU.hRootUnique r₁ hr₁ r₂ hr₂ ha₁ hp₁ ha₂ hp₂ ((hConn r₁ r₂).mpr hc)⟩

/-! ## 2. Verification of `compRevLoopStmt` -/

set_option maxHeartbeats 1200000 in
/-- Verification of `compRevLoopStmt`: given `D_sorted = (F_mid.E \ (S1 j).RF.F.E).sort (· ≤ ·)`
at `dBuf`, runs the Reverse Union-Find loop from `idx = t - 1` down to `0`, writing all `t`
entries of `releasesSplitEntries (S1 j).RF.R (inputMid (S j) u) D_sorted` at
`spBufJ + 4 * (spCnt + hasInp + idx)`, advancing `RevUFInv` to `F_mid`, and keeping
`act.length ≤ 2 * t`. -/
theorem compRevLoop_runs {W : LSFWindowImpl} {w k b bEndRoots bUFInitFind bUFPairUnion
    spBufJ ufBase dBuf tmp2 spCnt hasInp : ℕ}
    {S : CompLSFFamily k} {x1 : CompLSFMeta k} {touched1 : List ℕ} {u : Update}
    {D_sorted : List ℕ} {R_old : Finset ℕ} {isNew : ℕ → Bool}
    {p : Program} {ω : ℕ → Bool} {st : State} (j : Fin k)
    (hpEndRoots : p.procs[bEndRoots]? = some compEdgeEndRootsProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep0 : ∃ ℓ₀, CompLSFInv W.C_lsst ℓ₀ (S j))
    (hu_val : (S j).G.UpdateIsValid u)
    (hrep1 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 st.mem)
    (hend_le_sp : x1.endAddr ≤ spBufJ)
    (hsp_le_uf : spBufJ + 4 * (spCnt + hasInp + D_sorted.length) ≤ ufBase)
    (huf_le_d : ufBase + ufScratchSize x1.vCap ≤ dBuf)
    (hd_le_tmp : dBuf + D_sorted.length ≤ tmp2)
    (htmp_w : tmp2 + 2 < 2 ^ w)
    (hD_eq : D_sorted = ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).sort (· ≤ ·))
    (hD_at : ListAt st.mem dBuf D_sorted)
    (hR_old_sub : R_old ⊆ (compLSFStepSingle (S j) u).RF.R)
    (hR_old_sep : ∀ r ∈ R_old, ∀ s ∈ R_old, (forestAfterInput (S j).RF.F u).Connected r s → r = s)
    (hL0_R : (inputMid (S j) u).F.R =
      canonRoots (forestAfterInput (S j).RF.F u) R_old (compLSFStepSingle (S j) u).RF.R)
    (hisNew : ∀ r ∈ (compLSFStepSingle (S j) u).RF.R, isNew r = false ↔ r ∈ R_old)
    (hMem0 : RevUFMemAt st.mem ufBase x1.vCap isNew RevUFState.zero [])
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = j.1) (hr10 : st.regs 10 = spBufJ)
    (hr12 : st.regs 12 = ufBase) (hr13 : st.regs 13 = x1.vCap)
    (hr15 : st.regs 15 = dBuf) (hr17 : st.regs 17 = tmp2)
    (hr19 : st.regs 19 = hasInp) (hr20 : st.regs 20 = D_sorted.length) (hr24 : st.regs 24 = spCnt) :
    let F_mid := forestAfterInput (S j).RF.F u
    let RF' := (compLSFStepSingle (S j) u).RF
    let rels := releasesSplitEntries RF'.R (inputMid (S j) u) D_sorted
    ∃ st' c U_end act_end,
      Runs w p ω (compRevLoopStmt bEndRoots bUFInitFind bUFPairUnion) st .normal st' c ∧
      (∀ r < 20, st'.regs r = st.regs r) ∧
      st'.regs 24 = spCnt ∧
      RevUFInv F_mid RF' R_old U_end ∧
      RevUFMemAt st'.mem ufBase x1.vCap isNew U_end act_end ∧
      act_end.length ≤ 2 * D_sorted.length ∧
      (∀ idx (hidx : idx < D_sorted.length),
        let e := rels[idx]'(by rw [releasesSplitEntries_length]; exact hidx)
        st'.mem (spBufJ + 4 * (spCnt + hasInp + idx)) = (if e.isRelease then 1 else 0) ∧
        st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 1) = e.edge ∧
        st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 2) = e.kept ∧
        st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 3) = e.fresh) ∧
      (∀ a,
        (a < spBufJ + 4 * (spCnt + hasInp) ∨ spBufJ + 4 * (spCnt + hasInp + D_sorted.length) ≤ a) →
        (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) →
        (a < tmp2 ∨ tmp2 + 2 ≤ a) → st'.mem a = st.mem a) ∧
      c ≤ D_sorted.length * (40 * Nat.log 2 (2 * D_sorted.length + 2) + 820) + 10 := by
  classical
  intro F_mid RF' rels
  obtain ⟨ℓ₀, hIj⟩ := hrep0
  set cs1 := compLSFStepSingle (S j) u
  have hI1 : CompLSFInv W.C_lsst ℓ₀ cs1 := compLSFBatch_inv (U := [u]) hIj ⟨hu_val, trivial⟩
  have hRF' : RF'.IsRootedSpanningForestOf cs1.G := compLSF_RF_isRSF hI1
  have hF_mid_subG : cs1.G.IsSubgraph F_mid := by
    have hV0 : (S j).RF.F.V = (S j).G.V := (compLSF_RF_isRSF hIj).2.1
    cases u with
    | insert e a b =>
      refine ⟨by simpa [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput] using hV0.le,
        fun f hf => Finset.mem_insert_of_mem (compLSF_F_edge_orig hIj hf).1, fun f hf => ?_⟩
      have ho := compLSF_F_edge_orig hIj hf
      have hne : f ≠ e := fun h => hu_val.1 (h ▸ ho.1)
      simp [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput, hne, ho.2.2.2.1, ho.2.2.2.2]
    | delete e =>
      refine ⟨by simpa [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput, eraseForestEdge] using hV0.le,
        fun f hf => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hf).1,
          (compLSF_F_edge_orig hIj (Finset.mem_erase.mp hf).2).1⟩, fun f hf => ?_⟩
      have ho := compLSF_F_edge_orig hIj (Finset.mem_erase.mp hf).2
      exact ⟨ho.2.2.2.1, ho.2.2.2.2⟩
    | split v v' At Ah =>
      refine ⟨by simp [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput, hV0],
        fun f hf => (compLSF_F_edge_orig hIj hf).1, fun f hf => ?_⟩
      have ho := compLSF_F_edge_orig hIj hf
      simp only [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput, ho.2.2.2.1, ho.2.2.2.2, and_self]
  have hF_mid_V : F_mid.V = cs1.G.V := by
    have hV0 := (compLSF_RF_isRSF hIj).2.1
    cases u <;> simp [cs1, compLSFStepSingle, MGraph.applyUpdate, F_mid, forestAfterInput, eraseForestEdge, hV0]
  have hF_mid_for : F_mid.IsForest := by
    have hF0 := (compLSF_RF_isRSF hIj).1
    cases u with
    | insert _ _ _ => exact hF0
    | delete e => exact isForest_eraseEdge hF0 e
    | split v v' At Ah =>
      have hv_not : v' ∉ (S j).RF.F.V := by rw [(compLSF_RF_isRSF hIj).2.1]; exact hu_val.2.1
      have hv_in : v ∈ (S j).RF.F.V := by rw [(compLSF_RF_isRSF hIj).2.1]; exact hu_val.1
      refine ⟨fun e he => ?_, fun P ⟨hne, hnd, x, hwalk⟩ => ?_⟩
      · have h0 := hF0.1 e he
        simp only [F_mid, forestAfterInput, MGraph.applyUpdate, Finset.mem_insert]
        exact ⟨by split_ifs <;> [exact Or.inl rfl; exact Or.inr h0.1],
               by split_ifs <;> [exact Or.inl rfl; exact Or.inr h0.2]⟩
      · let proj : ℕ → ℕ := fun u => if u = v' then v else u
        have hlift : ∀ {a b : ℕ} {Q : List (ℕ × Bool)},
            ((S j).RF.F.applyUpdate (.split v v' At Ah)).IsWalk a b Q → (S j).RF.F.IsWalk (proj a) (proj b) Q := by
          intro a b Q hQ
          induction hQ with
          | nil z => exact .nil (proj z)
          | @cons a b z rest he hs _ ih =>
            have htne : (S j).RF.F.tail z.1 ≠ v' := fun h => hv_not (h ▸ (hF0.1 z.1 he).1)
            have hhne : (S j).RF.F.head z.1 ≠ v' := fun h => hv_not (h ▸ (hF0.1 z.1 he).2)
            have hsrc : (S j).RF.F.src z = proj a := by
              rw [← hs]; rcases z with ⟨e, _ | _⟩ <;>
                simp only [MGraph.src, MGraph.applyUpdate, proj] at htne hhne ⊢ <;> split_ifs with h1 h2 <;> simp_all
            have hdst : (S j).RF.F.dst z = proj (((S j).RF.F.applyUpdate (.split v v' At Ah)).dst z) := by
              rcases z with ⟨e, _ | _⟩ <;>
                simp only [MGraph.dst, MGraph.applyUpdate, proj] at htne hhne ⊢ <;> split_ifs with h1 h2 <;> simp_all
            exact .cons he hsrc (hdst ▸ ih)
        exact hF0.2 P ⟨hne, hnd, proj x, hlift hwalk⟩
  have hF_mid_subRF' : F_mid.IsSubgraph RF'.F := by
    have hEsub : RF'.F.E ⊆ F_mid.E := by
      have hdec := (compLSFBatch_decremental (U := [u]) hIj ⟨hu_val, trivial⟩).1
      cases u with
      | insert _ _ _ => exact hdec
      | delete e =>
        intro f hf
        have hne : f ≠ e := fun h => by
          have hfG := (compLSF_F_edge_orig hI1 hf).1
          rw [h] at hfG; simp [cs1, compLSFStepSingle, MGraph.applyUpdate] at hfG
        exact Finset.mem_erase.mpr ⟨hne, hdec hf⟩
      | split _ _ _ _ => exact hdec
    refine ⟨hRF'.2.1.trans hF_mid_V.symm ▸ Finset.Subset.rfl, hEsub, fun f hf => ?_⟩
    have ho1 := compLSF_F_edge_orig hI1 hf
    have hsub := hF_mid_subG.2.2 f (hEsub hf)
    exact ⟨ho1.2.2.2.1.trans hsub.1.symm, ho1.2.2.2.2.trans hsub.2.symm⟩
  have hD_nd : D_sorted.Nodup := by rw [hD_eq]; exact Finset.sort_nodup _ _
  have hD_mem : ∀ e, e ∈ D_sorted ↔ e ∈ F_mid.E ∧ e ∉ RF'.F.E := fun e => by
    rw [hD_eq, Finset.mem_sort, Finset.mem_sdiff]
  have hrep1_orig := hrep1
  obtain ⟨hk, _, _, _, _, _, _, _, _, hTE1, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
  obtain ⟨_, hG0_j, hG_j, _, hCr_j, _, hCompG_j⟩ := hBr1 j
  have hR_lt : ∀ r ∈ RF'.R, r < x1.vCap := fun r hr => hT1.hVlt r (hG_j ▸ hRF'.2.2.1 hr)
  have hT1_j : CompEdgeTrack x1.numComps x1.vCap x1.eCap x1.compOf x1.edgeC1 x1.edgeC2
      x1.gtVert x1.ghVert x1.gtList x1.ghList cs1 := by
    refine ⟨⟨hT1.hBij.1, fun C => by rw [hG0_j]; exact hT1.hBij.2 C⟩,
      fun v hv => hT1.hVlt v (hG_j ▸ hv), fun e he => hT1.hElt e (hG_j ▸ he),
      fun e he => ?_, hT1.hGT, hT1.hGH⟩
    obtain ⟨c1, c2, h1, h2, h3, h4, h5, h6, h7⟩ := hT1.hEdge e (hG_j ▸ he)
    exact ⟨c1, c2, h1, h2, by rw [hCompG_j, hG_j]; exact h3, by rw [hCompG_j, hG_j]; exact h4,
      fun c => by rw [hCompG_j]; exact h5 c, by rw [hCr_j]; exact h6,
      fun heq => by rw [hCompG_j, hG_j]; exact h7 heq⟩
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hL0F : (inputMid (S j) u).F.F = F_mid := by
    cases u with
    | insert _ _ _ => rfl
    | delete e =>
      by_cases he : e ∈ (S j).RF.F.E
      · simp [inputMid, F_mid, forestAfterInput, he]
      · simp only [inputMid, F_mid, forestAfterInput, he, ↓reduceIte, eraseForestEdge, Finset.erase_eq_of_notMem he]
        rfl
    | split _ _ _ _ => rfl
  have hloop : ∀ i (hi : i ≤ D_sorted.length) (s : State) (U : RevUFState) (act : List ℕ),
      (∀ r < 20, s.regs r = st.regs r) → s.regs 20 = i → s.regs 24 = spCnt →
      RevUFInv ((D_sorted.take i).foldl eraseForestEdge F_mid) RF' R_old U →
      RevUFMemAt s.mem ufBase x1.vCap isNew U act →
      act.length ≤ 2 * (D_sorted.length - i) →
      (∀ idx (hidx1 : i ≤ idx) (hidx2 : idx < D_sorted.length),
        let e := rels[idx]'(by rw [releasesSplitEntries_length]; exact hidx2)
        s.mem (spBufJ + 4 * (spCnt + hasInp + idx)) = (if e.isRelease then 1 else 0) ∧
        s.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 1) = e.edge ∧
        s.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 2) = e.kept ∧
        s.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 3) = e.fresh) →
      (∀ a,
        (a < spBufJ + 4 * (spCnt + hasInp + i) ∨ spBufJ + 4 * (spCnt + hasInp + D_sorted.length) ≤ a) →
        (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) →
        (a < tmp2 ∨ tmp2 + 2 ≤ a) → s.mem a = st.mem a) →
      ∃ st' c U_end act_end,
        Runs w p ω (compRevLoopStmt bEndRoots bUFInitFind bUFPairUnion) s .normal st' c ∧
        (∀ r < 20, st'.regs r = st.regs r) ∧ st'.regs 24 = spCnt ∧
        RevUFInv F_mid RF' R_old U_end ∧
        RevUFMemAt st'.mem ufBase x1.vCap isNew U_end act_end ∧
        act_end.length ≤ 2 * D_sorted.length ∧
        (∀ idx (hidx : idx < D_sorted.length),
          let e := rels[idx]'(by rw [releasesSplitEntries_length]; exact hidx)
          st'.mem (spBufJ + 4 * (spCnt + hasInp + idx)) = (if e.isRelease then 1 else 0) ∧
          st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 1) = e.edge ∧
          st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 2) = e.kept ∧
          st'.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 3) = e.fresh) ∧
        (∀ a,
          (a < spBufJ + 4 * (spCnt + hasInp) ∨ spBufJ + 4 * (spCnt + hasInp + D_sorted.length) ≤ a) →
          (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) →
          (a < tmp2 ∨ tmp2 + 2 ≤ a) → st'.mem a = st.mem a) ∧
        c ≤ i * (40 * Nat.log 2 (2 * D_sorted.length + 2) + 820) + 4 := by
    intro i
    induction i with
    | zero =>
      intro hi s U act hr_o hr20s hr24s hU hMem hact hdone hfr
      simp only [List.take_zero, List.foldl_nil, Nat.add_zero] at hU hfr
      exact ⟨s, 4, U, act, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr20s, hw0'], rfl, rfl, by simp [Expr.size]⟩),
        hr_o, hr24s, hU, hMem, by omega, fun idx hidx => hdone idx (Nat.zero_le _) hidx, hfr, by omega⟩
    | succ idx ih =>
      intro hi s U act hr_o hr20s hr24s hU hMem hact hdone hfr
      have hidx_lt : idx < D_sorted.length := by omega
      set d := D_sorted[idx]
      have hd_mid : d ∈ F_mid.E ∧ d ∉ RF'.F.E := (hD_mem d).mp (List.getElem_mem hidx_lt)
      set F_idx := (D_sorted.take idx).foldl eraseForestEdge F_mid
      set F_idx1 := (D_sorted.take (idx + 1)).foldl eraseForestEdge F_mid
      have hF_step : F_idx1 = eraseForestEdge F_idx d := foldl_eraseForestEdge_take_succ F_mid D_sorted hidx_lt
      have hFidx_p := foldl_eraseForestEdge_props F_mid (D_sorted.take idx)
      have hFidx1_p := foldl_eraseForestEdge_props F_mid (D_sorted.take (idx + 1))
      have hd_not_take : d ∉ D_sorted.take idx := fun hm => by
        obtain ⟨q, hq, hqd⟩ := List.getElem_of_mem hm
        have hqlt : q < idx := by rw [List.length_take] at hq; omega
        rw [List.getElem_take] at hqd
        have hEq := List.nodup_iff_injective_getElem.mp hD_nd
          (a₁ := ⟨q, by omega⟩) (a₂ := ⟨idx, hidx_lt⟩) hqd
        simp at hEq; omega
      have hd_Fidx : d ∈ F_idx.E := by
        rw [hFidx_p.2.1]; exact Finset.mem_sdiff.mpr ⟨hd_mid.1, List.mem_toFinset.not.mpr hd_not_take⟩
      have hFidx_subMid : F_mid.IsSubgraph F_idx :=
        ⟨hFidx_p.1 ▸ Finset.Subset.rfl, hFidx_p.2.1 ▸ Finset.sdiff_subset,
         fun f _ => ⟨congrFun hFidx_p.2.2.1 f, congrFun hFidx_p.2.2.2 f⟩⟩
      have hFidx_for : F_idx.IsForest := by
        have hfold_for : ∀ (L : List ℕ) (K : MGraph), K.IsForest → (L.foldl eraseForestEdge K).IsForest := by
          intro L; induction L with
          | nil => intro K hK; exact hK
          | cons e rest ihL => intro K hK; exact ihL _ (isForest_eraseEdge hK e)
        exact hfold_for (D_sorted.take idx) F_mid hF_mid_for
      have hFidx_V : F_idx.V = cs1.G.V := hFidx_p.1.trans hF_mid_V
      have hFidx_G : cs1.G.IsSubgraph F_idx :=
        ⟨hFidx_subMid.1.trans hF_mid_subG.1, hFidx_subMid.2.1.trans hF_mid_subG.2.1,
         fun f hf => ⟨(hFidx_subMid.2.2 f hf).1.trans (hF_mid_subG.2.2 f (hFidx_subMid.2.1 hf)).1,
           (hFidx_subMid.2.2 f hf).2.trans (hF_mid_subG.2.2 f (hFidx_subMid.2.1 hf)).2⟩⟩
      have hFidx1_subRF' : F_idx1.IsSubgraph RF'.F := by
        refine ⟨hRF'.2.1.trans (hFidx1_p.1.trans hF_mid_V).symm ▸ Finset.Subset.rfl, fun f hf => ?_, fun f hf => ?_⟩
        · rw [hFidx1_p.2.1]
          refine Finset.mem_sdiff.mpr ⟨hF_mid_subRF'.2.1 hf, fun hm => ?_⟩
          have hfD := List.mem_of_mem_take (List.mem_toFinset.mp hm)
          exact ((hD_mem f).mp hfD).2 hf
        · rw [hFidx1_p.2.2.1, hFidx1_p.2.2.2]; exact hF_mid_subRF'.2.2 f hf
      have hSep_idx : ∀ r ∈ R_old, ∀ s ∈ R_old, F_idx.Connected r s → r = s :=
        fun r hr s hs hc => hR_old_sep r hr s hs (connected_of_subgraph hFidx_subMid hc)
      have hrep1_s : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 s.mem :=
        compLSFRepDirty_of_agree hrep1_orig fun a _ ha2 =>
          hfr a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      have hs_d : s.mem (dBuf + idx) = d := by
        rw [hfr (dBuf + idx) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
        exact hD_at idx hidx_lt
      obtain ⟨cF, hc1, hm1, hdC, htC, hhC⟩ :=
        compReleased_edge_in_comp hIj hu_val hT1_j (Finset.mem_sdiff.mpr hd_mid)
      have hdG0 : d ∈ (compLSFStepSingle (S ⟨0, hrep1_orig.1⟩) u).G.E := hG_j ▸ (hF_mid_subG.2.1 hd_mid.1)
      have hm1_0 : 1 ≤ (compGraph (compLSFStepSingle (S ⟨0, hrep1_orig.1⟩) u).G₀ (x1.compOf cF)).m := hG0_j ▸ hm1
      let a1 : State := { s with regs := Function.update s.regs 20 idx }
      let a2 : State := { a1 with regs := Function.update a1.regs 21 d }
      have ha1 : Runs w p ω (.assign 20 (.bin .sub (.reg 20) (.const 1))) s .normal a1 4 :=
        runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, BinOp.eval, hr20s, hw1, show idx < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 15) (.reg 20)))) a1 .normal a2 5 :=
        runs_assign_iff.mpr ⟨d, Expr.eval_load_of_eq (by
          simp [a1, Expr.eval, BinOp.eval, hr_o 15 (by omega), hr15, show dBuf + idx < 2 ^ w by omega])
          hs_d, rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨sER, cER, hrunER, hER0, hER1, hERfr, hcER⟩ :=
        compEdgeEndRoots_runs (p := p) (pos := a2.pos) (ω := ω) j cF hw16 hrep1_s
          (by omega) htmp_w hdG0 hc1 hm1_0 hdC
      set ru := RF'.root (F_idx.tail d)
      set rv := RF'.root (F_idx.head d)
      have hER0' : sER.mem tmp2 = ru := by rwa [← htC, ← hFidx_p.2.2.1] at hER0
      have hER1' : sER.mem (tmp2 + 1) = rv := by rwa [← hhC, ← hFidx_p.2.2.2] at hER1
      let a3 : State := { a2 with regs := Function.update a2.regs 23 0, mem := sER.mem, pos := sER.pos }
      have ha3 : Runs w p ω (.call 23 bEndRoots [.reg 0, .reg 1, .reg 21, .reg 17]) a2 .normal a3 (cER + 5) :=
        runs_call_iff.mpr ⟨[b, j.1, d, tmp2], _, .returned 0, sER, cER,
          by simp [evalArgs, Expr.eval, a2, a1, hr_o 0 (by omega), hr0, hr_o 1 (by omega), hr1,
            hr_o 17 (by omega), hr17], hpEndRoots, hrunER, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      let a4 : State := { a3 with regs := Function.update a3.regs 22 ru }
      let a5 : State := { a4 with regs := Function.update a4.regs 23 rv }
      have ha4 : Runs w p ω (.assign 22 (.load (.reg 17))) a3 .normal a4 3 :=
        runs_assign_iff.mpr ⟨ru, Expr.eval_load_of_eq (by
          simp [a3, a2, a1, Expr.eval, hr_o 17 (by omega), hr17]) hER0', rfl, rfl, by simp [Expr.size]⟩
      have ha5 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 17) (.const 1)))) a4 .normal a5 5 :=
        runs_assign_iff.mpr ⟨rv, Expr.eval_load_of_eq (by
          simp [a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 17 (by omega), hr17, hw1, show tmp2 + 1 < 2 ^ w by omega])
          hER1', rfl, rfl, by simp [Expr.size]⟩
      have hMem_a5 : RevUFMemAt a5.mem ufBase x1.vCap isNew U act :=
        revUFMemAt_of_agree hMem fun a _ ha2 => hERfr a (Or.inl (by omega))
      have hRF'V : ∀ r ∈ RF'.R, r ∈ F_idx1.V := fun r hr => by
        rw [hFidx1_p.1, hF_mid_V]; exact hRF'.2.2.1 hr
      have hru_R : ru ∈ RF'.R := (rootedForest_root_spec hRF' (hFidx_V ▸ (hFidx_for.1 d hd_Fidx).1)).1
      have hrv_R : rv ∈ RF'.R := (rootedForest_root_spec hRF' (hFidx_V ▸ (hFidx_for.1 d hd_Fidx).2)).1
      obtain ⟨ra, sF1, cF1, hrunF1, hU1, hMem1, hraR, hraAct, hraPar, hraConn, hfrF1, hcF1⟩ :=
        compUFInitFind_runs (p := p) (pos := a5.pos) (ω := ω) hw16 (by omega) hR_lt hR_old_sub
          hRF'V hisNew hU hMem_a5 hru_R
      set U1 := ufInitOne (fun z => !isNew z) U ru
      set act1 := if U.sz ru = 0 then act ++ [ru] else act
      let a6 : State := { a5 with regs := Function.update a5.regs 25 ra, mem := sF1.mem, pos := sF1.pos }
      have ha6 : Runs w p ω (.call 25 bUFInitFind [.reg 12, .reg 13, .reg 22]) a5 .normal a6 (cF1 + 4) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, ru], _, .returned ra, sF1, cF1,
          by simp [evalArgs, Expr.eval, a5, a4, a3, a2, a1, hr_o 12 (by omega), hr12, hr_o 13 (by omega), hr13],
          hpInitFind, hrunF1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      obtain ⟨rb, sF2, cF2, hrunF2, hU2, hMem2, hrbR, hrbAct, hrbPar, hrbConn, hfrF2, hcF2⟩ :=
        compUFInitFind_runs (p := p) (pos := a6.pos) (ω := ω) hw16 (by omega) hR_lt hR_old_sub
          hRF'V hisNew hU1 hMem1 hrv_R
      set U2 := ufInitOne (fun z => !isNew z) U1 rv
      set act2 := if U1.sz rv = 0 then act1 ++ [rv] else act1
      let a7 : State := { a6 with regs := Function.update a6.regs 26 rb, mem := sF2.mem, pos := sF2.pos }
      have ha7 : Runs w p ω (.call 26 bUFInitFind [.reg 12, .reg 13, .reg 23]) a6 .normal a7 (cF2 + 4) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, rv], _, .returned rb, sF2, cF2,
          by simp [evalArgs, Expr.eval, a6, a5, a4, a3, a2, a1, hr_o 12 (by omega), hr12, hr_o 13 (by omega), hr13],
          hpInitFind, hrunF2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have ⟨hraAct2, hraPar2⟩ := ufInitOne_preserves_active (isOld := fun z => !isNew z) (r := rv) hraAct
      rw [hF_step] at hU2 hraConn hrbConn hFidx1_subRF'
      obtain ⟨hne_ab, hpair_eq, hU3⟩ :=
        revUFInv_union_edge hFidx_for hFidx_V hFidx_G hd_Fidx hFidx1_subRF' hRF' hR_old_sub hSep_idx
          hU2 hraR (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar) hraConn hrbR hrbAct hrbPar hrbConn
      set outSlot := spBufJ + 4 * (spCnt + hasInp + idx)
      let a8 : State := { a7 with regs := Function.update a7.regs 27 outSlot }
      have ha8 : Runs w p ω (.assign 27 (.bin .add (.reg 10)
          (.bin .mul (.const 4) (.bin .add (.bin .add (.reg 24) (.reg 19)) (.reg 20))))) a7 .normal a8 10 :=
        runs_assign_iff.mpr ⟨outSlot, by
          have h1 : spCnt + hasInp < 2 ^ w := by omega
          have h2 : spCnt + hasInp + idx < 2 ^ w := by omega
          have h3 : 4 * (spCnt + hasInp + idx) < 2 ^ w := by omega
          have h4 : outSlot < 2 ^ w := by omega
          simp [a7, a6, a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 10 (by omega), hr10,
            hr24s, hr_o 19 (by omega), hr19, hw4, h1, h2, h3, h4, outSlot],
          rfl, rfl, by simp [Expr.size]⟩
      have hoA_w : U2.oldR ra < 2 ^ w := by
        have hmo := (hU2.hRootMeta ra hraR (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar)).2.2
        rw [hmo]; split_ifs with hne
        · have := hR_lt _ (hR_old_sub (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2)
          dsimp only [ufScratchSize] at huf_le_d; omega
        · omega
      have hoB_w : U2.oldR rb < 2 ^ w := by
        have hmo := (hU2.hRootMeta rb hrbR hrbAct hrbPar).2.2
        rw [hmo]; split_ifs with hne
        · have := hR_lt _ (hR_old_sub (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2)
          dsimp only [ufScratchSize] at huf_le_d; omega
        · omega
      have hsz_sum_w : U2.sz ra + U2.sz rb < 2 ^ w := by
        have h1 : U2.sz ra ≤ act2.length :=
          hMem2.sz_le_act (r := ra) (hR_lt ra hraR) (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar)
        have h2 : U2.sz rb ≤ act2.length := hMem2.sz_le_act (r := rb) (hR_lt rb hrbR) hrbAct hrbPar
        have h3 : act2.length ≤ x1.vCap := hMem2.act_len_le
        dsimp only [ufScratchSize] at huf_le_d; omega
      have hd_w : d < 2 ^ w := by
        have := hT1.hElt d hdG0
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostSize, compHdrSize] at hTE1
        omega
      obtain ⟨sPU, cPU, hrunPU, hPU0, hPU1, hPU2, hPU3, hMem3, hfrPU, hcPU⟩ :=
        compUFPairUnion_runs (outSlot := outSlot) (p := p) (pos := a8.pos) (ω := ω) hw16 (by omega)
          (by omega) (Or.inl (by omega)) hw1 hd_w hw1 (hR_lt ra hraR) (hR_lt rb hrbR) hoA_w hoB_w hMem2
          (fun _ => ⟨hne_ab, hraAct2.symm ▸ hraAct, hrbAct, hraPar2.symm ▸ hraPar, hrbPar, hsz_sum_w⟩)
      simp only [one_ne_zero, ↓reduceIte] at hMem3
      let a9 : State := { a8 with regs := Function.update a8.regs 23 0, mem := sPU.mem, pos := sPU.pos }
      have ha9 : Runs w p ω (.call 23 bUFPairUnion
          [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 1, .reg 21, .const 1]) a8 .normal a9 (cPU + 9) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, ra, rb, outSlot, 1, d, 1], _, .returned 0, sPU, cPU,
          by simp [evalArgs, Expr.eval, a8, a7, a6, a5, a4, a3, a2, a1, hr_o 12 (by omega), hr12,
            hr_o 13 (by omega), hr13, hw1], hpPairUnion, hrunPU, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have hact1_le : act1.length ≤ act.length + 1 := by dsimp [act1]; split_ifs <;> simp
      have hact2_le : act2.length ≤ 2 * (D_sorted.length - idx) := by
        have h2 : act2.length ≤ act1.length + 1 := by dsimp [act2]; split_ifs <;> simp
        omega
      have hrel_idx := releasesSplitEntries_getElem hF_mid_for hF_mid_V hF_mid_subG hF_mid_subRF'
        hRF' hR_old_sub hR_old_sep hL0F hL0_R hD_nd (fun e he => (hD_mem e).mp he) idx hidx_lt
      have hstep_fr : ∀ a, (a < outSlot ∨ outSlot + 4 ≤ a) →
          (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) →
          (a < tmp2 ∨ tmp2 + 2 ≤ a) → a9.mem a = s.mem a := fun a ha1 ha2 ha3 => by
        have hpu := hfrPU a ha1 (by rcases ha2 with h | h; exact Or.inr (Or.inl h); dsimp [ufScratchSize] at h; exact Or.inr (Or.inr (by omega)))
        exact hpu.trans ((hfrF2 a ha2).trans ((hfrF1 a ha2).trans (hERfr a ha3)))
      have t8 := runs_seq_iff.mpr (Or.inr ⟨a8, 10, cPU + 9, ha8, ha9, rfl⟩)
      have t7 := runs_seq_iff.mpr (Or.inr ⟨a7, cF2 + 4, _, ha7, t8, rfl⟩)
      have t6 := runs_seq_iff.mpr (Or.inr ⟨a6, cF1 + 4, _, ha6, t7, rfl⟩)
      have t5 := runs_seq_iff.mpr (Or.inr ⟨a5, 5, _, ha5, t6, rfl⟩)
      have t4 := runs_seq_iff.mpr (Or.inr ⟨a4, 3, _, ha4, t5, rfl⟩)
      have t3 := runs_seq_iff.mpr (Or.inr ⟨a3, cER + 5, _, ha3, t4, rfl⟩)
      have t2 := runs_seq_iff.mpr (Or.inr ⟨a2, 5, _, ha2, t3, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨a1, 4, _, ha1, t2, rfl⟩)
      obtain ⟨st', cRest, U_end, act_end, hrest, hr'_o, hr'_24, hU_end, hMem_end, hact_end, hdone', hfr', hcRest⟩ :=
        ih (by omega) a9 (ufUnion U2 ra rb) act2
          (fun r hr => by simp [a9, a8, a7, a6, a5, a4, a3, a2, a1, show r ≠ 20 by omega,
            show r ≠ 21 by omega, show r ≠ 22 by omega, show r ≠ 23 by omega, show r ≠ 25 by omega,
            show r ≠ 26 by omega, show r ≠ 27 by omega, hr_o r hr])
          (by simp [a9, a8, a7, a6, a5, a4, a3, a2, a1])
          (by simp [a9, a8, a7, a6, a5, a4, a3, a2, a1, hr24s])
          hU3 hMem3 hact2_le
          (fun q hq1 hq2 => by
            by_cases hqe : q = idx
            · subst hqe
              have hrel_e : rels[q]'(by rw [releasesSplitEntries_length]; exact hq2) =
                  ⟨true, d, (ufPair U2 ra rb).1, (ufPair U2 ra rb).2⟩ := by
                rw [hrel_idx, hpair_eq]
              simp only [hrel_e, ↓reduceIte]
              exact ⟨hPU0, hPU1, hPU2, hPU3⟩
            · have hqgt : idx + 1 ≤ q := by omega
              have hq_fr : ∀ off < 4, a9.mem (spBufJ + 4 * (spCnt + hasInp + q) + off) =
                  s.mem (spBufJ + 4 * (spCnt + hasInp + q) + off) := fun off hoff =>
                hstep_fr _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
              have hdq := hdone q hqgt hq2
              have h0 := hq_fr 0 (by omega); simp only [Nat.add_zero] at h0
              exact ⟨h0.trans hdq.1, (hq_fr 1 (by omega)).trans hdq.2.1,
                (hq_fr 2 (by omega)).trans hdq.2.2.1, (hq_fr 3 (by omega)).trans hdq.2.2.2⟩)
          (fun a ha1 ha2 ha3 => (hstep_fr a (by omega) ha2 ha3).trans (hfr a (by omega) ha2 ha3))
      have hfull : Runs w p ω (compRevLoopStmt bEndRoots bUFInitFind bUFPairUnion) s .normal st' _ :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, a9, _, cRest,
          by simp [Expr.eval, BinOp.eval, hr20s, hw0, hw0'], by decide, hbody, hrest, by simp [Expr.size]; rfl⟩))
      have hlog1 : Nat.log 2 act1.length ≤ Nat.log 2 (2 * D_sorted.length + 2) :=
        Nat.log_mono_right (by omega)
      have hlog2 : Nat.log 2 act2.length ≤ Nat.log 2 (2 * D_sorted.length + 2) :=
        Nat.log_mono_right (by omega)
      have hmul_step : (idx + 1) * (40 * Nat.log 2 (2 * D_sorted.length + 2) + 820) =
          idx * (40 * Nat.log 2 (2 * D_sorted.length + 2) + 820) +
          (40 * Nat.log 2 (2 * D_sorted.length + 2) + 820) := by ring
      exact ⟨st', _, U_end, act_end, hfull, hr'_o, hr'_24, hU_end, hMem_end, hact_end, hdone', hfr', by omega⟩
  have hFend_p := foldl_eraseForestEdge_props F_mid D_sorted
  have hFend_V : (D_sorted.foldl eraseForestEdge F_mid).V = RF'.F.V := hFend_p.1.trans (hF_mid_V.trans hRF'.2.1.symm)
  have hFend_E : (D_sorted.foldl eraseForestEdge F_mid).E = RF'.F.E := by
    rw [hFend_p.2.1]; ext e; simp only [Finset.mem_sdiff, List.mem_toFinset, hD_mem]; constructor
    · rintro ⟨hm, hn⟩; exact Classical.byContradiction fun h => hn ⟨hm, h⟩
    · intro he; exact ⟨hF_mid_subRF'.2.1 he, fun h => h.2 he⟩
  have hU0 : RevUFInv ((D_sorted.take D_sorted.length).foldl eraseForestEdge F_mid) RF' R_old RevUFState.zero := by
    rw [List.take_length]
    exact revUFInv_of_same_graph hFend_V.symm hFend_E.symm
      (fun e he => ⟨(hF_mid_subRF'.2.2 e he).1.trans (congrFun hFend_p.2.2.1.symm e),
        (hF_mid_subRF'.2.2 e he).2.trans (congrFun hFend_p.2.2.2.symm e)⟩) (revUFInv_zero hRF')
  obtain ⟨st', c, U_end, act_end, hr, hr_o, hr_24, hU_end, hMem_end, hact_end, hdone, hfr, hc⟩ :=
    hloop D_sorted.length le_rfl st RevUFState.zero [] (fun _ _ => rfl) hr20 hr24
      hU0 hMem0 (by simp) (fun _ h1 h2 => by omega) (fun _ _ _ _ => rfl)
  exact ⟨st', c, U_end, act_end, hr, hr_o, hr_24, hU_end, hMem_end, hact_end, hdone, hfr,
    le_trans hc (Nat.add_le_add_left (by decide) _)⟩

end

end MinCostFlow.SparseCore.Program
