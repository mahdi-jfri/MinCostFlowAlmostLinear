module

public import MinCostFlow.MinRatio.SelectUpdateFPhiLen
public import MinCostFlow.MinRatio.WireShiftDeepSelectLoop
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Non-rebuilt prefix `F`, `φ`, and `len` update loop (`SelectUpdateFPhiLenLoop`)

Verifies `selectUpdateFPhiLenLoopBody` (`SelectUpdateFPhiLen.lean`), calling
`selectUpdateFPhiLenLevelBody` across non-rebuilt interior levels `cur .. limit - 1`
(`limit = min firstReb d ≤ d`). Because no sparse-core readout `op 4` is called, every address
`< scratch` outside `[B.base, B.endAddr)` — in particular all of `Rrep.foot` and every stretch
table and list of `UpdateCoreSelectOutAt` — is preserved across all iterations.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

private lemma regBlk_in_blocks_fl {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d)
    (h : B.regBlk j a) : B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  unfold SelectBlocksLoc.regBlk at h; omega

private lemma lenPtr_prev_le_fPtr_fl {B : SelectBlocksLoc} {j : ℕ} (hj : 0 < j) :
    B.lenPtr (j - 1) + B.eCap * B.Lk ≤ B.fPtr j := by
  have h1 : B.lenPtr (j - 1) + B.eCap * B.Lk ≤ B.fPtr (j - 1) + B.levelSize := by
    unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; omega
  have h2 : B.fPtr (j - 1) + B.levelSize = B.fPtr j := by
    unfold SelectBlocksLoc.fPtr
    cases j with | zero => omega | succ k => simp [Nat.succ_mul]; omega
  omega

private lemma selOutTable_bound_off_blk {w sb selOutBase scratch lo hi stAddr stLw : ℕ}
    {foot : ℕ → Prop} {mem : ℕ → ℕ} {E : Finset ℕ}
    (hloLtHi : lo < hi) (hsbLeLo : sb ≤ lo) (hHiLeOut : hi ≤ selOutBase)
    (hFootDisj : ∀ a, sb ≤ a → a < hi → ¬ foot a)
    (hTab : SelOutTableAt w foot selOutBase scratch mem stAddr stLw E)
    (hPos : ∀ e ∈ E, 0 < stLw) :
    ∀ e ∈ E, mem stAddr + e * stLw + stLw ≤ scratch ∧
      (mem stAddr + e * stLw + stLw ≤ lo ∨ hi ≤ mem stAddr + e * stLw) := by
  intro e he
  obtain ⟨hEnd, hWords⟩ := hTab.2 e he
  refine ⟨hEnd, interval_disj_region (hPos e he) hloLtHi fun x hx1 hx2 ⟨h1, h2⟩ => ?_⟩
  have ht : x - (mem stAddr + e * stLw) < stLw := by omega
  have hxEq : mem stAddr + e * stLw + (x - (mem stAddr + e * stLw)) = x := by omega
  rcases hWords (x - (mem stAddr + e * stLw)) ht with hf | ⟨hge, _⟩
  · rw [hxEq] at hf; exact hFootDisj x (by omega) hx2 hf
  · omega

private lemma fixVal_congr_fl {m1 m2 : ℕ → ℕ} {a h L P : ℕ}
    (hag : ∀ t < L, m1 (a + t) = m2 (a + t)) :
    Num.fixVal m1 a h L P = Num.fixVal m2 a h L P := by
  unfold Num.fixVal Num.intVal Num.signedVal
  rw [Num.unsignedVal_congr hag]

private lemma selOutTable_agree {w selOutBase scratch stAddr stLw : ℕ}
    {foot : ℕ → Prop} {m1 m2 : ℕ → ℕ} {E : Finset ℕ}
    (hTab : SelOutTableAt w foot selOutBase scratch m1 stAddr stLw E)
    (hFootAg : ∀ a, foot a → m2 a = m1 a)
    (hOutAg : ∀ a, selOutBase ≤ a → a < scratch → m2 a = m1 a) :
    ∀ e ∈ E, ∀ t < stLw, m2 (m1 stAddr + e * stLw + t) = m1 (m1 stAddr + e * stLw + t) := by
  intro e he t ht
  rcases (hTab.2 e he).2 t ht with hf | ⟨h1, h2⟩
  · exact hFootAg _ hf
  · exact hOutAg _ h1 h2

set_option maxHeartbeats 1200000 in
theorem selectUpdateFPhiLenLoop_runs
    {w L P m V psi k epsExp drainUnit vCap eCap sb metaBase pLast selOutBase
      cur limit scratch pos : ℕ}
    {self lvlProc dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill coreLenEdge : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {root : ℕ} {oldCh : ChainState cfg.T cfg.P} {modelPre : Alg2State cfg}
    {tok' : SolverToken cfg L Rcore} {loc : SelectHeapLoc} {B : SelectBlocksLoc}
    {D : SelBlocksData} {levelU : ℕ → List Update} {diffLists : ℕ → LevelDiffLists}
    {uWords stLw : ℕ → ℕ} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hLkW : L < 2 ^ w)
    (hcurLe : cur ≤ limit) (hlimLe : limit ≤ cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' mem)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hEndLeOut : B.endAddr ≤ selOutBase)
    (hOutLeSc : selOutBase + 1 + 12 * limit ≤ scratch)
    (hcaps : SolverLevelCapsInv P V vCap eCap modelPre tok' mem)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok' mem) pLast))
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hPrevOk : 0 < cur →
      D.E (cur - 1) = (modelPre.chain.G (cur - 1)).E ∧
      D.len (cur - 1) = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ cur)
    (hGSubPrev : ∀ j, cur ≤ j → j < limit → 0 < j →
      (modelPre.chain.G j).E ⊆ (modelPre.chain.G (j - 1)).E)
    (hSlotOut : ∀ j, cur ≤ j → j < limit →
      let slot := selOutBase + 1 + 12 * j
      let L' := diffLists j
      let stDesc := mem (slot + 8)
      let uPtr := mem (slot + 10)
      let foot := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok'
      LevelDiffListsAt mem slot L' ∧
      mem (slot + 9) = stLw j ∧ stLw j < 2 ^ w ∧
      mem (slot + 11) = uWords j ∧
      SelOutWordsAt foot selOutBase scratch (mem (slot + 0)) L'.uG.length ∧
      SelOutWordsAt foot selOutBase scratch (mem (slot + 2)) L'.fDel.length ∧
      SelOutWordsAt foot selOutBase scratch (mem (slot + 4)) L'.uS.length ∧
      SelOutWordsAt foot selOutBase scratch (mem (slot + 6)) L'.reemb.length ∧
      BatchAt mem uPtr (oldCh.G j) (levelU j) (uWords j) ∧
      BatchWithinCaps vCap eCap (levelU j) ∧
      (∀ t < uWords j, mem (uPtr + t) < 2 ^ w) ∧
      SelOutWordsAt foot selOutBase scratch uPtr (uWords j) ∧
      SelOutWordsAt foot selOutBase scratch stDesc 2 ∧
      StretchValuesAt mem stDesc 4 (stLw j) P (modelPre.chain.G j).E
        (modelPre.chain.toTreeChain.activeLSF j).wstr ∧
      SelOutTableAt w foot selOutBase scratch mem stDesc (stLw j) (modelPre.chain.G j).E ∧
      SelOutTableAt w foot selOutBase scratch mem (stDesc + 1) (stLw j) (modelPre.chain.G j).E)
    (hModel : ∀ j, cur ≤ j → j < limit →
      D.V j = (oldCh.G j).V ∧
      modelPre.chain.G j = (oldCh.G j).applyBatch (levelU j) ∧
      (oldCh.G j).BatchIsValid (levelU j) ∧
      (oldCh.G j).IsSubgraph (D.F j) ∧ (D.F j).V = (oldCh.G j).V ∧
      (modelPre.chain.G j).IsSubgraph (modelPre.chain.toTreeChain.activeLSF j).F.F ∧
      (modelPre.chain.toTreeChain.activeLSF j).F.F.V = (modelPre.chain.G j).V ∧
      (modelPre.chain.toTreeChain.activeLSF j).F.F.E ⊆ (D.F j).E ∧
      (∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E, Update.delete e ∉ levelU j) ∧
      (diffLists j).fDel.toFinset = (D.F j).E \ (modelPre.chain.toTreeChain.activeLSF j).F.F.E ∧
      ((∀ e ∈ (diffLists j).uG, e < eCap) ∧ (∀ e ∈ (diffLists j).fDel, e < eCap)) ∧
      (∀ e ∈ (modelPre.chain.G j).E, e ∉ (diffLists j).uG →
        e ∈ D.E j ∧ modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e = D.len j e) ∧
      (∀ e ∈ (modelPre.chain.G j).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ P = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e))
    (hpLoop : p.procs[self]? = some (selectUpdateFPhiLenLoopBody self lvlProc))
    (hpLvl : p.procs[lvlProc]? =
      some (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill))
    (hDgBatch : ∀ j, cur ≤ j → j < limit →
      MeetsContract w p dgApplyBatch
        (dgApplyBatchContract w vCap eCap (oldCh.G j) (D.F j) (levelU j) (uWords j)))
    (hDelList : ∀ j, cur ≤ j → j < limit →
      MeetsContract w p delEdgeList
        (dgDeleteEdgeListContract w vCap eCap ((levelU j).foldl (dgBatchTarget 0) (D.F j))
          (diffLists j).fDel))
    (hSplits : ∀ j, cur ≤ j → j < limit →
      MeetsContract w p batchCopySplits
        (selBatchCopySplitsContract w vCap P (oldCh.G j) (levelU j) (uWords j) (D.φ j)))
    (hFilterPres : ∀ j, cur ≤ j → j < limit →
      MeetsContract w p filterPres (selFilterPresentContract w (diffLists j).uG))
    (hpCoreLen : p.procs[coreLenFill]? = some (selCoreLenFillBody coreLenEdge))
    (hCoreLenEdge : MeetsContract w p coreLenEdge (selCoreLenEdgeContract w P))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateFPhiLenLoopSpace diffLists stLw cur limit L < 2 ^ w) :
    let C' := modelPre.chain.toTreeChain
    ∃ scOut cost out,
      Runs w p ω (selectUpdateFPhiLenLoopBody self lvlProc)
        (startState [metaBase, cur, limit, solverLevelMetaAddr tok'.table cfg.P.d,
          selOutBase, cfg.P.d, L, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateFPhiLenLoopSpace diffLists stLw cur limit L ∧
      SelBlocksDataAt out.mem B P
        { D with
          F := fun j => if cur ≤ j ∧ j < limit then (C'.activeLSF j).F.F else D.F j
          V := fun j => if cur ≤ j ∧ j < limit then (C'.G j).V else D.V j
          φ := fun j => if cur ≤ j ∧ j < limit then splitPot (D.φ j) (batchSplits (levelU j)) else D.φ j
          E := fun j => if cur ≤ j ∧ j < limit then (C'.G j).E else D.E j
          len := fun j => if cur ≤ j ∧ j < limit then C'.chainLen modelPre.chain.ℓ (j + 1) else D.len j } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) → out.mem a = mem a) ∧
      cost ≤ selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw cur limit L := by
  intro C'
  set Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hsbLeBase : sb ≤ B.base := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
    omega
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hsbLtEnd : sb < B.endAddr := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    omega
  have hMetaEnd : metaBase + selectLevelMetaSize B.d ≤ B.base := by have := hreg.2.2.2.1; omega
  have hOwn := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCapsM := solverLevelCapsInv_iff_metaCaps.mp hcaps
  have hInd : ∀ n cur' sc pos' (D' : SelBlocksData) (mCur : ℕ → ℕ),
      limit - cur' = n → cur ≤ cur' → cur' ≤ limit → scratch ≤ sc →
      (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) → mCur a = mem a) →
      SelBlocksDataAt mCur B P D' pLast →
      (0 < cur' → D'.E (cur' - 1) = (modelPre.chain.G (cur' - 1)).E ∧
        D'.len (cur' - 1) = C'.chainLen modelPre.chain.ℓ cur') →
      (∀ j, cur' ≤ j → j < limit →
        D'.V j = D.V j ∧ D'.F j = D.F j ∧ D'.φ j = D.φ j ∧
        D'.E j = D.E j ∧ D'.len j = D.len j) →
      ZeroFrom mCur sc →
      sc + selectUpdateFPhiLenLoopSpace diffLists stLw cur' limit L < 2 ^ w →
      ∃ scOut cost out,
        Runs w p ω (selectUpdateFPhiLenLoopBody self lvlProc)
          (startState [metaBase, cur', limit, solverLevelMetaAddr tok'.table cfg.P.d,
            selOutBase, cfg.P.d, L, sc] mCur pos')
          (.returned scOut) out cost ∧
        sc ≤ scOut ∧
        scOut ≤ sc + selectUpdateFPhiLenLoopSpace diffLists stLw cur' limit L ∧
        SelBlocksDataAt out.mem B P
          { D' with
            F := fun j => if cur' ≤ j ∧ j < limit then (C'.activeLSF j).F.F else D'.F j
            V := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).V else D'.V j
            φ := fun j => if cur' ≤ j ∧ j < limit then splitPot (D'.φ j) (batchSplits (levelU j)) else D'.φ j
            E := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).E else D'.E j
            len := fun j => if cur' ≤ j ∧ j < limit then C'.chainLen modelPre.chain.ℓ (j + 1) else D'.len j } pLast ∧
        ZeroFrom out.mem scOut ∧
        (∀ a < sc, ¬ (B.base ≤ a ∧ a < B.endAddr) → out.mem a = mCur a) ∧
        cost ≤ selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw cur' limit L := by
    intro n
    induction n with
    | zero =>
      intro cur' sc pos' D' mCur hsub _ hcurLe' _ _ hblk0 _ _ hz0 _
      have hcurEq : cur' = limit := by omega
      have hSp0 : selectUpdateFPhiLenLoopSpace diffLists stLw cur' limit L = 0 := by
        unfold selectUpdateFPhiLenLoopSpace; rw [hcurEq, Finset.Ico_self, Finset.sum_empty]
      have hNo : ∀ j, ¬ (cur' ≤ j ∧ j < limit) := fun j h => by omega
      have hDEq : ({ D' with
            F := fun j => if cur' ≤ j ∧ j < limit then (C'.activeLSF j).F.F else D'.F j
            V := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).V else D'.V j
            φ := fun j => if cur' ≤ j ∧ j < limit then splitPot (D'.φ j) (batchSplits (levelU j)) else D'.φ j
            E := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).E else D'.E j
            len := fun j => if cur' ≤ j ∧ j < limit then C'.chainLen modelPre.chain.ℓ (j + 1) else D'.len j } : SelBlocksData) = D' := by
        cases D'; simp [hNo]
      let s0 := startState [metaBase, cur', limit, solverLevelMetaAddr tok'.table cfg.P.d,
        selOutBase, cfg.P.d, L, sc] mCur pos'
      have hRun : Runs w p ω (selectUpdateFPhiLenLoopBody self lvlProc) s0 (.returned sc) s0 6 := by
        unfold selectUpdateFPhiLenLoopBody
        refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hcurEq], ?_,
          by simp [Expr.size]⟩
        exact runs_ret_iff.mpr ⟨sc, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
      refine ⟨sc, 6, s0, hRun, le_refl _, by omega, hDEq.symm ▸ hblk0, hz0, fun _ _ _ => rfl, ?_⟩
      unfold selectUpdateFPhiLenLoopCost; omega
    | succ n ih =>
      intro cur' sc pos' D' mCur hsub hGeCur hcurLe' hScGe hAg0 hblk0 hPrevOk0 hDEqD hz0 hroom0
      have hcurLt : cur' < limit := by omega
      have hcurD : cur' < cfg.P.d := lt_of_lt_of_le hcurLt hlimLe
      have hcurB : cur' < B.d := by omega
      have hFootAg : ∀ a, Rrep.foot root tok' a → mCur a = mem a := fun a ha =>
        hAg0 a (hFootSc a ha) fun hb => hFootDisj a (by omega) hb.2 ha
      have hOutAg : ∀ a, selOutBase ≤ a → a < scratch → mCur a = mem a := fun a h1 h2 =>
        hAg0 a h2 (by omega)
      have hMC := hCapsM.2.2.2.2.2 cur' hcurD
      have hSlotCur := hSlotOut cur' hGeCur hcurLt
      dsimp only at hSlotCur
      obtain ⟨hDiffC, hStLwEq, hStLwW, hUWEq, hUGW, hFDelW, hUSW, hReembW, hBatchC, hCapsUC,
        hUWordsLt, hUPtrW, hStDescW, hStretchC, hNumTab, hDenTab⟩ := hSlotCur
      have hModC := hModel cur' hGeCur hcurLt
      have hDC := hDEqD cur' le_rfl hcurLt
      set slotCur := selOutBase + 1 + 12 * cur'
      set prevLen := if cur' = 0 then mem (solverLevelMetaAddr tok'.table cfg.P.d) else B.lenPtr (cur' - 1)
      have hBlkLeEnd : B.fPtr cur' + B.levelSize ≤ B.endAddr := by
        have := B.blk_le_last (Nat.le_of_lt hcurB)
        unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
      have hBaseLeF : B.base ≤ B.fPtr cur' := by unfold SelectBlocksLoc.fPtr; omega
      have hBlkPos : B.fPtr cur' < B.fPtr cur' + B.levelSize := by
        unfold SelectBlocksLoc.levelSize dynGraphSize; omega
      have hGLe : solverLevelG tok' mem cur' + dynGraphSize vCap eCap ≤ scratch := by
        have h1 : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
        have hlast := hFootSc (solverLevelG tok' mem cur' + dynGraphSize vCap eCap - 1)
          (Or.inl (hOwn _ (by
            have htg := hMC.2.2.2.2 (solverLevelG tok' mem cur' + dynGraphSize vCap eCap - 1)
              (by unfold solverLevelG; omega) (by unfold solverLevelG; omega)
            split_ifs at htg <;> omega)))
        omega
      have hGOffBlk : solverLevelG tok' mem cur' + dynGraphSize B.vCap B.eCap ≤ B.fPtr cur' ∨
          B.fPtr cur' + B.levelSize ≤ solverLevelG tok' mem cur' := by
        rw [hBv, hBe]
        have hD := interval_disj_region (a := solverLevelG tok' mem cur')
          (len := dynGraphSize vCap eCap) (by unfold dynGraphSize; omega) hsbLtEnd
          (fun x hx1 hx2 ⟨h1, h2⟩ => hFootDisj x hx1 hx2 (Or.inl (hOwn _ (by
            have htg := hMC.2.2.2.2 x (by unfold solverLevelG at h1; exact h1)
              (by unfold solverLevelG at h2; exact h2)
            split_ifs at htg <;> omega))))
        exact hD.imp (by omega) (by omega)
      have hGCur : DynGraphAt mCur (solverLevelG tok' mem cur') B.vCap B.eCap (modelPre.chain.G cur') := by
        rw [hBv, hBe]
        exact hMC.1.of_agree fun a h1 h2 => hFootAg a (Or.inl (hOwn a (by
          have htg := hMC.2.2.2.2 a h1 h2; split_ifs at htg <;> omega)))
      have htabCur : SelectMetaTableAt mCur (selectMlocOf B metaBase (solverLevelG tok' mem) pLast) :=
        htab.of_agree fun a h1 h2 => by
          dsimp only [selectMlocOf] at h1 h2
          exact hAg0 a (by omega) (by omega)
      have hSlotAg : ∀ t < 12, mCur (slotCur + t) = mem (slotCur + t) := fun t ht =>
        hOutAg _ (by dsimp only [slotCur]; omega) (by dsimp only [slotCur]; omega)
      have hDiffCur : LevelDiffListsAt mCur slotCur (diffLists cur') :=
        ⟨(hSlotAg 1 (by omega)).trans hDiffC.1,
         fun i hi => by
           rw [hSlotAg 0 (by omega)]
           exact (hOutAg _ (by have := hUGW.1; omega) (by have := hUGW.2.1; omega)).trans (hDiffC.2.1 i hi),
         (hSlotAg 3 (by omega)).trans hDiffC.2.2.1,
         fun i hi => by
           rw [hSlotAg 2 (by omega)]
           exact (hOutAg _ (by have := hFDelW.1; omega) (by have := hFDelW.2.1; omega)).trans (hDiffC.2.2.2.1 i hi),
         (hSlotAg 5 (by omega)).trans hDiffC.2.2.2.2.1,
         fun i hi => by
           rw [hSlotAg 4 (by omega)]
           exact (hOutAg _ (by have := hUSW.1; omega) (by have := hUSW.2.1; omega)).trans (hDiffC.2.2.2.2.2.1 i hi),
         (hSlotAg 7 (by omega)).trans hDiffC.2.2.2.2.2.2.1,
         fun i hi => by
           rw [hSlotAg 6 (by omega)]
           exact (hOutAg _ (by have := hReembW.1; omega) (by have := hReembW.2.1; omega)).trans (hDiffC.2.2.2.2.2.2.2 i hi)⟩
      have hStDescAg : mCur (mem (slotCur + 8)) = mem (mem (slotCur + 8)) ∧
          mCur (mem (slotCur + 8) + 1) = mem (mem (slotCur + 8) + 1) :=
        ⟨hOutAg _ hStDescW.1 (by have := hStDescW.2.1; omega),
         hOutAg _ (by have := hStDescW.1; omega) (by have := hStDescW.2.1; omega)⟩
      have hStLwPos : ∀ e ∈ (modelPre.chain.G cur').E, 0 < stLw cur' := by
        intro e he
        by_contra h0
        have hEq0 : stLw cur' = 0 := by omega
        have hpos := (hStretchC e he).2.2.1
        rw [hEq0] at hpos
        simp [Num.fixVal, Num.intVal, Num.signedVal, Num.unsignedVal, Num.capacity] at hpos
      have hNumBnd := selOutTable_bound_off_blk hBlkPos (by omega) (by omega)
        (fun a ha1 ha2 => hFootDisj a ha1 (by omega)) hNumTab hStLwPos
      have hDenBnd := selOutTable_bound_off_blk hBlkPos (by omega) (by omega)
        (fun a ha1 ha2 => hFootDisj a ha1 (by omega)) hDenTab hStLwPos
      have hStretchCur : StretchValuesAt mCur (mem (slotCur + 8)) 4 (stLw cur') P
          (modelPre.chain.G cur').E (C'.activeLSF cur').wstr := by
        intro e he
        have hnumA := selOutTable_agree hNumTab hFootAg hOutAg e he
        have hdenA := selOutTable_agree hDenTab hFootAg hOutAg e he
        have hS := hStretchC e he
        rw [hStDescAg.1, hStDescAg.2]
        refine ⟨fun t ht => by rw [hnumA t ht]; exact hS.1 t ht,
          fun t ht => by rw [hdenA t ht]; exact hS.2.1 t ht,
          by rw [fixVal_congr_fl hdenA]; exact hS.2.2.1,
          by rw [fixVal_congr_fl hnumA, fixVal_congr_fl hdenA]; exact hS.2.2.2⟩
      have hPrevProps :
          prevLen + B.eCap * B.Lk ≤ sc ∧
          (prevLen + B.eCap * B.Lk ≤ B.fPtr cur' ∨ B.fPtr cur' + B.levelSize ≤ prevLen) ∧
          EdgeValuesAt mCur prevLen 4 B.Lk P (modelPre.chain.G cur').E
            (C'.chainLen modelPre.chain.ℓ cur') := by
        by_cases hcz : cur' = 0
        · subst hcz
          dsimp only [prevLen]; simp only [↓reduceIte]
          have hOwn0 : Rrep.foot root tok' (mem (solverLevelMetaAddr tok'.table cfg.P.d)) :=
            Or.inl (by simpa using hMC.2.2.1)
          have hTag0 : ∀ a, mem (solverLevelMetaAddr tok'.table cfg.P.d) ≤ a →
              a < mem (solverLevelMetaAddr tok'.table cfg.P.d) + eCap * L →
              Rrep.foot root tok' a := fun a h1 h2 =>
            Or.inl (hOwn a (by have := hMC.2.2.2.1 a (by simpa using h1) (by simpa using h2); omega))
          have hLe : mem (solverLevelMetaAddr tok'.table cfg.P.d) + B.eCap * B.Lk ≤ sc := by
            rw [hBe, hBLk]
            by_cases hpos : 0 < eCap * L
            · have := hFootSc (mem (solverLevelMetaAddr tok'.table cfg.P.d) + eCap * L - 1)
                (hTag0 _ (by omega) (by omega))
              omega
            · have := hFootSc _ hOwn0; omega
          have hOff : mem (solverLevelMetaAddr tok'.table cfg.P.d) + B.eCap * B.Lk ≤ B.fPtr 0 ∨
              B.fPtr 0 + B.levelSize ≤ mem (solverLevelMetaAddr tok'.table cfg.P.d) := by
            rw [hBe, hBLk]
            by_cases hpos : 0 < eCap * L
            · exact interval_disj_region hpos hBlkPos fun x hx1 hx2 ⟨h1, h2⟩ =>
                hFootDisj x (by omega) (by omega) (hTag0 x h1 h2)
            · have hnot : ¬ (B.fPtr 0 ≤ mem (solverLevelMetaAddr tok'.table cfg.P.d) ∧
                  mem (solverLevelMetaAddr tok'.table cfg.P.d) < B.fPtr 0 + B.levelSize) := fun h =>
                hFootDisj _ (by omega) (by omega) hOwn0
              omega
          have hEV : EdgeValuesAt mCur (mem (solverLevelMetaAddr tok'.table cfg.P.d)) 4 B.Lk P
              (modelPre.chain.G 0).E (C'.chainLen modelPre.chain.ℓ 0) := by
            rw [hBLk]
            have h0 : EdgeValuesAt mem (mem (solverLevelMetaAddr tok'.table cfg.P.d)) 4 L P
                (modelPre.chain.G 0).E (C'.chainLen modelPre.chain.ℓ 0) := by
              simpa [C'] using hMC.2.1
            intro e he
            have heCap : e < eCap := hMC.1.2.2.1 e he
            have heMul : e * L + L ≤ eCap * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCap)
              rwa [Nat.succ_mul] at this
            have hag : ∀ t < L, mCur (mem (solverLevelMetaAddr tok'.table cfg.P.d) + e * L + t) =
                mem (mem (solverLevelMetaAddr tok'.table cfg.P.d) + e * L + t) := fun t ht =>
              hFootAg _ (hTag0 _ (by omega) (by omega))
            exact ⟨fun t ht => by rw [hag t ht]; exact (h0 e he).1 t ht,
              by rw [fixVal_congr_fl hag]; exact (h0 e he).2⟩
          exact ⟨hLe, hOff, hEV⟩
        · have hpos : 0 < cur' := by omega
          dsimp only [prevLen]; simp only [hcz, ↓reduceIte]
          have hPrevLeF := lenPtr_prev_le_fPtr_fl (B := B) hpos
          obtain ⟨hEP, hLenP⟩ := hPrevOk0 hpos
          have hSub := hGSubPrev cur' hGeCur hcurLt hpos
          have hEV : EdgeValuesAt mCur (B.lenPtr (cur' - 1)) 4 B.Lk P
              (modelPre.chain.G cur').E (C'.chainLen modelPre.chain.ℓ cur') := by
            have hpart := (hblk0.2.2.1 (cur' - 1) (by omega)).2
            unfold coreLenPrec at hpart
            rw [ite_eq_left (show cur' - 1 < B.d by omega)] at hpart
            intro e he
            have heP : e ∈ D'.E (cur' - 1) := hEP ▸ hSub he
            have h := hpart e heP
            rwa [hLenP] at h
          exact ⟨by omega, Or.inl hPrevLeF, hEV⟩
      -- Space split for `Ico cur' limit`
      have hIco : Finset.Ico cur' limit = insert cur' (Finset.Ico (cur' + 1) limit) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hNotMem : cur' ∉ Finset.Ico (cur' + 1) limit := by simp
      have hSpSplit : selectUpdateFPhiLenLoopSpace diffLists stLw cur' limit L =
          selectUpdateFPhiLenSpace (diffLists cur').uG.length L (stLw cur') +
          selectUpdateFPhiLenLoopSpace diffLists stLw (cur' + 1) limit L := by
        unfold selectUpdateFPhiLenLoopSpace
        rw [hIco, Finset.sum_insert hNotMem]
      have hCostSplit : selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw cur' limit L =
          selectUpdateFPhiLenCost (uWords cur') (levelU cur').length (diffLists cur').uG.length
            (diffLists cur').fDel.length L (stLw cur') + 70 +
          selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw (cur' + 1) limit L := by
        unfold selectUpdateFPhiLenLoopCost
        rw [hIco, Finset.sum_insert hNotMem]; omega
      -- Run `selectUpdateFPhiLenLevel_runs` at `cur'`
      have hLenStep : ∀ e, (C'.activeLSF cur').wstr e * C'.chainLen modelPre.chain.ℓ cur' e =
          C'.chainLen modelPre.chain.ℓ (cur' + 1) e := fun _ => rfl
      obtain ⟨sc1, c1, st1, hr1, hsc1Lo, hsc1Hi, hblk1, hz1, hfr1, hc1⟩ :=
        selectUpdateFPhiLenLevel_runs (ω := ω) (j := cur') (pLast := pLast) (prevLen := prevLen)
          (slot := slotCur) (uPtr := mem (slotCur + 10)) (uWords := uWords cur')
          (stDesc := mem (slotCur + 8)) (stLw := stLw cur') (scratch := sc) (pos := pos')
          (oldG := oldCh.G cur') (newG := modelPre.chain.G cur')
          (newF := (C'.activeLSF cur').F.F)
          (wstr := (C'.activeLSF cur').wstr) (prevVal := C'.chainLen modelPre.chain.ℓ cur')
          (solverG := solverLevelG tok' mem) (U := levelU cur') (L := diffLists cur')
          hw16 (by omega) hcurB hStLwW htabCur hblk0
          (by omega) (by omega) hGCur (by rw [hBv, hBe]; omega) hGOffBlk hDiffCur
          ⟨hSlotAg 8 (by omega), (hSlotAg 9 (by omega)).trans hStLwEq, hSlotAg 10 (by omega)⟩
          (by dsimp only [slotCur]; omega)
          (by rw [hSlotAg 0 (by omega)]; have := hUGW.2.1; omega)
          (by rw [hSlotAg 0 (by omega)]; right; have := hUGW.1; omega)
          (by rw [hSlotAg 2 (by omega)]; have := hFDelW.2.1; omega)
          (by rw [hSlotAg 2 (by omega)]; right; have := hFDelW.1; omega)
          (hBatchC.of_agree fun t ht => hOutAg _ (by have := hUPtrW.1; omega) (by have := hUPtrW.2.1; omega))
          (fun t ht => by rw [hOutAg _ (by have := hUPtrW.1; omega) (by have := hUPtrW.2.1; omega)]; exact hUWordsLt t ht)
          (by have := hUPtrW.2.1; omega)
          (Or.inr (by have := hUPtrW.1; omega))
          (by have := hStDescW.2.1; omega)
          ⟨by rw [hStDescAg.1]; exact hNumTab.1, by rw [hStDescAg.2]; exact hDenTab.1⟩
          hStretchCur
          (fun e he => by rw [hStDescAg.1]; exact ⟨by have := (hNumBnd e he).1; omega, (hNumBnd e he).2⟩)
          (fun e he => by rw [hStDescAg.2]; exact ⟨by have := (hDenBnd e he).1; omega, (hDenBnd e he).2⟩)
          hPrevProps.1 hPrevProps.2.1 hPrevProps.2.2
          (hDC.1.trans hModC.1) hModC.2.1 hModC.2.2.1 (by rw [hBv, hBe]; exact hCapsUC)
          (hDC.2.1 ▸ hModC.2.2.2.1) (hDC.2.1 ▸ hModC.2.2.2.2.1)
          hModC.2.2.2.2.2.1 hModC.2.2.2.2.2.2.1 (hDC.2.1 ▸ hModC.2.2.2.2.2.2.2.1)
          hModC.2.2.2.2.2.2.2.2.1 (hDC.2.1 ▸ hModC.2.2.2.2.2.2.2.2.2.1)
          (by rw [hBe]; exact hModC.2.2.2.2.2.2.2.2.2.2.1)
          (fun e he hnot => by
            rw [hDC.2.2.2.1, hDC.2.2.2.2, hLenStep]
            exact hModC.2.2.2.2.2.2.2.2.2.2.2.1 e he hnot)
          (fun e he => by rw [hBLk, hLenStep]; exact hModC.2.2.2.2.2.2.2.2.2.2.2.2 e he)
          (by rw [hBv, hBe, hDC.2.1]; exact hDgBatch cur' hGeCur hcurLt)
          (by rw [hBv, hBe, hDC.2.1]; exact hDelList cur' hGeCur hcurLt)
          (by rw [hBv, hDC.2.2.1]; exact hSplits cur' hGeCur hcurLt)
          (hFilterPres cur' hGeCur hcurLt) hpCoreLen hCoreLenEdge hz0
          (by rw [hBLk]; omega)
      -- Recursive call on `cur' + 1`
      set D1 : SelBlocksData :=
        { D' with
          F := Function.update D'.F cur' (C'.activeLSF cur').F.F
          V := Function.update D'.V cur' (modelPre.chain.G cur').V
          φ := Function.update D'.φ cur' (splitPot (D'.φ cur') (batchSplits (levelU cur')))
          E := Function.update D'.E cur' (modelPre.chain.G cur').E
          len := Function.update D'.len cur' (C'.chainLen modelPre.chain.ℓ (cur' + 1)) }
      have hblk1' : SelBlocksDataAt st1.mem B P D1 pLast := by
        convert hblk1 using 2; funext e; rfl
      have hAg1 : ∀ a < sc, ¬ (B.base ≤ a ∧ a < B.endAddr) → st1.mem a = mCur a := fun a ha hnot =>
        hfr1 a ha fun hrb => hnot (regBlk_in_blocks_fl (Nat.le_of_lt hcurB) hrb)
      obtain ⟨sc2, c2, st2, hr2, hsc2Lo, hsc2Hi, hblk2, hz2, hfr2, hc2⟩ :=
        ih (cur' + 1) sc1 st1.pos D1 st1.mem (by omega) (by omega) (by omega) (by omega)
          (fun a ha hnot => (hAg1 a (by omega) hnot).trans (hAg0 a ha hnot))
          hblk1'
          (fun _ => by simp [D1])
          (fun j hj1 hj2 => by
            have hne : j ≠ cur' := by omega
            have hd := hDEqD j (by omega) hj2
            simp [D1, hne, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2])
          hz1 (by rw [hBLk] at hsc1Hi; omega)
      -- Combine `D1` updates with `cur' + 1 .. limit - 1`
      have hDFinal :
          ({ D1 with
            F := fun j => if cur' + 1 ≤ j ∧ j < limit then (C'.activeLSF j).F.F else D1.F j
            V := fun j => if cur' + 1 ≤ j ∧ j < limit then (C'.G j).V else D1.V j
            φ := fun j => if cur' + 1 ≤ j ∧ j < limit then splitPot (D1.φ j) (batchSplits (levelU j)) else D1.φ j
            E := fun j => if cur' + 1 ≤ j ∧ j < limit then (C'.G j).E else D1.E j
            len := fun j => if cur' + 1 ≤ j ∧ j < limit then C'.chainLen modelPre.chain.ℓ (j + 1) else D1.len j } : SelBlocksData) =
          { D' with
            F := fun j => if cur' ≤ j ∧ j < limit then (C'.activeLSF j).F.F else D'.F j
            V := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).V else D'.V j
            φ := fun j => if cur' ≤ j ∧ j < limit then splitPot (D'.φ j) (batchSplits (levelU j)) else D'.φ j
            E := fun j => if cur' ≤ j ∧ j < limit then (C'.G j).E else D'.E j
            len := fun j => if cur' ≤ j ∧ j < limit then C'.chainLen modelPre.chain.ℓ (j + 1) else D'.len j } := by
        cases D'; simp only [D1, SelBlocksData.mk.injEq, and_true]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          (funext j; by_cases hEq : j = cur'
           · subst hEq; simp [hcurLt, C', ChainState.toTreeChain]
           · by_cases hR : cur' + 1 ≤ j ∧ j < limit
             · have hR' : cur' ≤ j ∧ j < limit := ⟨by omega, hR.2⟩
               simp [hR, hR', hEq]
             · have hR' : ¬ (cur' ≤ j ∧ j < limit) := by omega
               simp [hR', Function.update_of_ne hEq]
               intro h1 h2; omega)
      -- Stitch the loop step: cond + assign 8 + cond(assign 9) + call lvl + call self + ret
      let s0 := startState [metaBase, cur', limit, solverLevelMetaAddr tok'.table cfg.P.d,
        selOutBase, cfg.P.d, L, sc] mCur pos'
      let rg8 := Function.update s0.regs 8 slotCur
      let rg9 := Function.update rg8 9 prevLen
      let rg10 := Function.update rg9 10 sc1
      let rg11 := Function.update rg10 11 sc2
      have rSlot : Runs w p ω
          (.assign 8 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 1))))
          s0 .normal ⟨mCur, rg8, pos'⟩ 8 :=
        runs_assign_iff.mpr ⟨slotCur, by
          simp [Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega,
            show 12 < 2 ^ w by omega, show selOutBase + 1 < 2 ^ w by omega,
            show 12 * cur' < 2 ^ w by omega, show slotCur < 2 ^ w by dsimp only [slotCur]; omega,
            slotCur], rfl, rfl, by simp [Expr.size]⟩
      have hPrevRun : ∃ cP,
          Runs w p ω
            (.cond (.reg 1)
              (.assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const smTableOff))
                (.bin .mul (.const 4) (.bin .add (.reg 5) (.const 1))))
                (.bin .sub (.reg 1) (.const 1)))))
              (.assign 9 (.load (.reg 3))))
            ⟨mCur, rg8, pos'⟩ .normal ⟨mCur, rg9, pos'⟩ cP ∧ cP ≤ 18 := by
        by_cases hcz : cur' = 0
        · have hLMA : solverLevelMetaAddr tok'.table cfg.P.d < scratch :=
            hFootSc _ (Or.inl (hOwn _ (by
              have := hCapsM.2.2.2.2.1 0 (by omega); rw [Nat.add_zero] at this; omega)))
          have hLMAg : mCur (solverLevelMetaAddr tok'.table cfg.P.d) = prevLen := by
            dsimp only [prevLen]; simp only [hcz, ↓reduceIte]
            exact hFootAg _ (Or.inl (hOwn _ (by
              have := hCapsM.2.2.2.2.1 0 (by omega); rw [Nat.add_zero] at this; omega)))
          have rElse : Runs w p ω (.assign 9 (.load (.reg 3)))
              ⟨mCur, rg8, pos'⟩ .normal ⟨mCur, rg9, pos'⟩ 3 :=
            runs_assign_iff.mpr ⟨prevLen, by
              simp [Expr.eval, rg8, s0, startState, hLMAg,
                show prevLen < 2 ^ w by have := hPrevProps.1; omega], rfl, rfl, by simp [Expr.size]⟩
          exact ⟨_, runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, rg8, s0, startState, hcz], rElse, rfl⟩,
            by simp [Expr.size]⟩
        · have hrowP := htabCur.2.2 (cur' - 1) (by dsimp only [selectMlocOf]; omega)
          have hlenP : mCur (smEntryAddr metaBase B.d 4 (cur' - 1)) = prevLen := by
            dsimp only [prevLen]; simp only [hcz, ↓reduceIte]
            simpa [selectMlocOf] using hrowP.2.2.2.2.1
          have hMetaSz : metaBase + (2 + 8 * (B.d + 1)) ≤ B.base := by
            unfold selectLevelMetaSize at hMetaEnd; exact hMetaEnd
          have hEntLt : smEntryAddr metaBase B.d 4 (cur' - 1) < 2 ^ w := by
            unfold smEntryAddr smTableOff; omega
          have rThen : Runs w p ω
              (.assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const smTableOff))
                (.bin .mul (.const 4) (.bin .add (.reg 5) (.const 1))))
                (.bin .sub (.reg 1) (.const 1)))))
              ⟨mCur, rg8, pos'⟩ .normal ⟨mCur, rg9, pos'⟩ 15 :=
            runs_assign_iff.mpr ⟨prevLen, by
              simp [Expr.eval, BinOp.eval, rg8, s0, startState, hBd.symm,
                show smTableOff < 2 ^ w by unfold smTableOff; omega,
                show metaBase + smTableOff < 2 ^ w by unfold smTableOff; omega,
                show 1 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
                show B.d + 1 < 2 ^ w by omega,
                show 4 * (B.d + 1) < 2 ^ w by omega,
                show metaBase + smTableOff + 4 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
                show cur' - 1 < 2 ^ w by omega,
                show metaBase + smTableOff + 4 * (B.d + 1) + (cur' - 1) =
                  smEntryAddr metaBase B.d 4 (cur' - 1) by unfold smEntryAddr; omega,
                hEntLt, hlenP, show prevLen < 2 ^ w by have := hPrevProps.1; omega],
              rfl, rfl, by simp [Expr.size]⟩
          exact ⟨_, runs_cond_iff.mpr ⟨cur', _, by simp [Expr.eval, rg8, s0, startState, show cur' < 2 ^ w by omega],
            by rw [ite_eq_right hcz]; exact rThen, rfl⟩, by simp [Expr.size]⟩
      obtain ⟨cP, rPrev, hcP⟩ := hPrevRun
      have rCallLvl : Runs w p ω (.call 10 lvlProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 6, .reg 7])
          ⟨mCur, rg9, pos'⟩ .normal ⟨st1.mem, rg10, st1.pos⟩ (c1 + 7) :=
        runs_call_iff.mpr ⟨[metaBase, cur', slotCur, prevLen, L, sc], _, .returned sc1, st1, c1,
          by simp [evalArgs, Expr.eval, rg9, rg8, s0, startState], hpLvl,
          by simpa [hBLk] using hr1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have rCallSelf : Runs w p ω
          (.call 11 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5,
            .reg 6, .reg 10])
          ⟨st1.mem, rg10, st1.pos⟩ .normal ⟨st2.mem, rg11, st2.pos⟩ (c2 + 11) :=
        runs_call_iff.mpr ⟨[metaBase, cur' + 1, limit, solverLevelMetaAddr tok'.table cfg.P.d,
            selOutBase, cfg.P.d, L, sc1], _, .returned sc2, st2, c2,
          by simp [evalArgs, Expr.eval, BinOp.eval, rg10, rg9, rg8, s0, startState,
            show 1 < 2 ^ w by omega, show cur' + 1 < 2 ^ w by omega],
          hpLoop, hr2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have rRet : Runs w p ω (.ret (.reg 11)) ⟨st2.mem, rg11, st2.pos⟩ (.returned sc2)
          ⟨st2.mem, rg11, st2.pos⟩ 2 :=
        runs_ret_iff.mpr ⟨sc2, by simp [Expr.eval, rg11], rfl, rfl, by simp [Expr.size]⟩
      have rBody := runs_seq_iff.mpr (Or.inr ⟨_, _, _, rSlot,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rPrev,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallLvl,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallSelf, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have rStep : Runs w p ω (selectUpdateFPhiLenLoopBody self lvlProc) s0
          (.returned sc2) ⟨st2.mem, rg11, st2.pos⟩ (c1 + c2 + cP + 36) := by
        unfold selectUpdateFPhiLenLoopBody
        exact runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, s0, startState, hcurLt, show 1 < 2 ^ w by omega],
          by simpa using rBody, by simp [Expr.size]; omega⟩
      refine ⟨sc2, _, ⟨st2.mem, rg11, st2.pos⟩, rStep, by omega,
        by rw [hSpSplit]; rw [hBLk] at hsc1Hi; omega,
        hDFinal ▸ hblk2, hz2,
        fun a ha hnot => (hfr2 a (by omega) hnot).trans (hAg1 a ha hnot), ?_⟩
      rw [hCostSplit]; rw [hBLk] at hc1; omega
  exact hInd (limit - cur) cur scratch pos D mem rfl le_rfl hcurLe le_rfl (fun _ _ _ => rfl)
    hblk hPrevOk (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) hz hroom

end MinCostFlow.MinRatio
