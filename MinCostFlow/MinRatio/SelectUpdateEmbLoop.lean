module

public import MinCostFlow.MinRatio.SelectUpdateEmb
public import MinCostFlow.MinRatio.WireShiftDeepSelectLoop
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Non-rebuilt prefix embedding update loop (`SelectUpdateEmbLoop`)

Verifies `selectUpdateEmbLoopBody` (`SelectUpdateEmb.lean`), calling `selectUpdateEmbLevelBody`
for non-rebuilt interior levels `cur .. limit - 1` (`limit = min firstReb d ≤ d`), updating
`D.coreE j` and `D.emb j` in `SelBlocksDataAt` while preserving `solverStateRep`,
`SolverLevelCapsInv`, `SelectMetaTableAt`, `SelectHeapAt`, and `SelOutWordsAt` for the remaining
slots and lists (`uG`, `fDel`, `reemb`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

private lemma regEmb_in_blocks {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d) (h : B.regEmb j a) :
    B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have h4 := B.blkEnd_eq j
  have h5 : B.fPtr j ≤ B.embPtr j := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
  unfold SelectBlocksLoc.regEmb at h
  omega

private lemma selectMlocOf_congr_emb {B : SelectBlocksLoc} {metaBase pLast : ℕ}
    {g₁ g₂ : ℕ → ℕ} (h : ∀ j < B.d, g₁ j = g₂ j) :
    selectMlocOf B metaBase g₁ pLast = selectMlocOf B metaBase g₂ pLast := by
  unfold selectMlocOf; congr 1
  · funext j; by_cases hj : j < B.d <;> simp [hj]; exact h j hj
  · funext j; by_cases hj : j < B.d <;> by_cases hj1 : j + 1 < B.d <;>
      simp [hj, hj1] <;> exact h (j + 1) hj1

set_option maxHeartbeats 1200000 in
theorem selectUpdateEmbLoop_runs
    {w L P m V psi k epsExp drainUnit depth capExp vCap eCap sb metaBase pLast
      heapSize selOutBase cur limit scratch pos : ℕ}
    {self embLvlProc embUpdateFromList : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {modelPre : Alg2State cfg} {tok' : SolverToken cfg L Rcore}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {D : SelBlocksData}
    {diffLists : ℕ → LevelDiffLists} {mem : ℕ → ℕ}
    (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hSlotW : B.slot < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hcurLe : cur ≤ limit) (hlimLe : limit ≤ cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' mem)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hEndLeOut : B.endAddr ≤ selOutBase)
    (hOutWords : SelOutWordsAt
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
      selOutBase scratch selOutBase (1 + 12 * limit))
    (hcaps : SolverLevelCapsInv P V vCap eCap modelPre tok' mem)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok' mem) pLast))
    (hHeap : SelectHeapAt mem loc 4 heapSize)
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hFMatch : ∀ j, cur ≤ j → j < limit →
      D.F j = (modelPre.chain.toTreeChain.activeLSF j).F.F)
    (hScIn : ∀ j, cur ≤ j → j < limit →
      SparseCoreOrdInput cfg.T cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
        (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
        (modelPre.chain.updCount j))
    (hBrLt : ∀ j, cur ≤ j → j < limit → modelPre.chain.bran j < cfg.P.k)
    (hSlotOut : ∀ j, cur ≤ j → j < limit →
      let slot := selOutBase + 1 + 12 * j
      let L' := diffLists j
      LevelDiffListsAt mem slot L' ∧
      SelOutWordsAt (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
        selOutBase scratch (mem (slot + 0)) L'.uG.length ∧
      SelOutWordsAt (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
        selOutBase scratch (mem (slot + 2)) L'.fDel.length ∧
      SelOutWordsAt (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
        selOutBase scratch (mem (slot + 4)) L'.uS.length ∧
      SelOutWordsAt (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
        selOutBase scratch (mem (slot + 6)) L'.reemb.length)
    (hModel : ∀ j, cur ≤ j → j < limit →
      ((∀ e ∈ (diffLists j).uG, e < eCap) ∧ (∀ e ∈ (diffLists j).fDel, e < eCap) ∧
        (∀ e ∈ (diffLists j).uS, e < eCap) ∧ (∀ e ∈ (diffLists j).reemb, e < eCap)) ∧
      (∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ B.slot) ∧
      (∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
        e ∉ (diffLists j).uG → e ∉ (diffLists j).fDel → e ∉ (diffLists j).uS →
        e ∉ (diffLists j).reemb →
        e ∈ D.coreE j ∧ modelPre.chain.toTreeChain.activeEmb j e = D.emb j e))
    (hpLoop : p.procs[self]? = some (selectUpdateEmbLoopBody self embLvlProc))
    (hpEmbLvl : p.procs[embLvlProc]? = some (selectUpdateEmbLevelBody (op 4) embUpdateFromList))
    (hFootAt : ∀ j, cur ≤ j → j < limit →
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hEmbUpd : ∀ j, cur ≤ j → j < limit → ∀ L' : List ℕ,
      MeetsContract w p embUpdateFromList
        (selEmbUpdateFromListContract w vCap eCap (modelPre.chain.G j)
          (modelPre.chain.toTreeChain.activeLSF j).F.F L'
          (modelPre.chain.toTreeChain.activeEmb j)))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateEmbLoopSpace diffLists cur limit < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let C' := modelPre.chain.toTreeChain
    ∃ scOut cost out tok2,
      Runs w p ω (selectUpdateEmbLoopBody self embLvlProc)
        (startState [metaBase, cur, limit, tok'.handle + 18, selOutBase, cfg.P.d, B.slot, scratch]
          mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateEmbLoopSpace diffLists cur limit ∧
      Rrep.rep root modelPre tok2 out.mem ∧
      tok2.table = tok'.table ∧ tok2.handle = tok'.handle ∧
      tok2.levelsEnd = tok'.levelsEnd ∧ tok2.intCap = tok'.intCap ∧
      tok2.rootECap = tok'.rootECap ∧
      tok2.tree = tok'.tree ∧ tok2.trees = tok'.trees ∧ tok2.edgeRecords = tok'.edgeRecords ∧
      tok2.termHandle = tok'.termHandle ∧ tok2.termTok = tok'.termTok ∧
      tok2.vcLast = tok'.vcLast ∧ tok2.ecLast = tok'.ecLast ∧
      (∀ a, Rrep.foot root tok2 a → Rrep.foot root tok' a ∨ (scratch ≤ a ∧ a < scOut)) ∧
      (∀ a, tok'.owned a → tok2.owned a) ∧
      (∀ a < scratch, tok2.tag a = tok'.tag a) ∧
      (∀ a, tok'.tag a ≠ 0 → tok2.tag a = tok'.tag a) ∧
      SolverLevelCapsInv P V vCap eCap modelPre tok2 out.mem ∧
      SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tok2 out.mem) pLast) ∧
      SelectHeapAt out.mem loc 4 heapSize ∧
      SelBlocksDataAt out.mem B P
        { D with
          coreE := fun j => if cur ≤ j ∧ j < limit then (C'.activeCore j).E else D.coreE j
          emb := fun j => if cur ≤ j ∧ j < limit then C'.activeEmb j else D.emb j } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) →
        ¬ (∃ j, cur ≤ j ∧ j < limit ∧ Rcore.foot (tok'.coreHandle j) (tok'.coreTok j) a) →
        out.mem a = mem a) ∧
      cost + Rrep.phi root tok2 out.mem ≤
        selectUpdateEmbLoopCost Psc.readout diffLists cur limit B.slot +
          Rrep.phi root tok' mem := by
  intro Rrep C'
  have hInd : ∀ n cur sc pos (tok : SolverToken cfg L Rcore) (D : SelBlocksData) (mCur : ℕ → ℕ),
      limit - cur = n → cur ≤ limit →
      Rrep.rep root modelPre tok mCur →
      (∀ a, Rrep.foot root tok a → a < sc) →
      (∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok a) →
      SelOutWordsAt (Rrep.foot root tok) selOutBase sc selOutBase (1 + 12 * limit) →
      SolverLevelCapsInv P V vCap eCap modelPre tok mCur →
      SelectMetaTableAt mCur (selectMlocOf B metaBase (solverLevelG tok mCur) pLast) →
      SelectHeapAt mCur loc 4 heapSize →
      SelBlocksDataAt mCur B P D pLast →
      (∀ j, cur ≤ j → j < limit → D.F j = (C'.activeLSF j).F.F) →
      (∀ j, cur ≤ j → j < limit →
        SparseCoreOrdInput cfg.T cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
          (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
          (modelPre.chain.updCount j)) →
      (∀ j, cur ≤ j → j < limit → modelPre.chain.bran j < cfg.P.k) →
      (∀ j, cur ≤ j → j < limit →
        let slot := selOutBase + 1 + 12 * j
        let L' := diffLists j
        LevelDiffListsAt mCur slot L' ∧
        SelOutWordsAt (Rrep.foot root tok) selOutBase sc (mCur (slot + 0)) L'.uG.length ∧
        SelOutWordsAt (Rrep.foot root tok) selOutBase sc (mCur (slot + 2)) L'.fDel.length ∧
        SelOutWordsAt (Rrep.foot root tok) selOutBase sc (mCur (slot + 4)) L'.uS.length ∧
        SelOutWordsAt (Rrep.foot root tok) selOutBase sc (mCur (slot + 6)) L'.reemb.length) →
      (∀ j, cur ≤ j → j < limit →
        ((∀ e ∈ (diffLists j).uG, e < eCap) ∧ (∀ e ∈ (diffLists j).fDel, e < eCap) ∧
          (∀ e ∈ (diffLists j).uS, e < eCap) ∧ (∀ e ∈ (diffLists j).reemb, e < eCap)) ∧
        (∀ e ∈ (C'.activeCore j).E, (mWalkEncode (C'.activeEmb j e)).length ≤ B.slot) ∧
        (∀ e ∈ (C'.activeCore j).E,
          e ∉ (diffLists j).uG → e ∉ (diffLists j).fDel → e ∉ (diffLists j).uS →
          e ∉ (diffLists j).reemb →
          e ∈ D.coreE j ∧ C'.activeEmb j e = D.emb j e)) →
      (∀ j, cur ≤ j → j < limit →
        SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
          (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op) →
      (∀ j, cur ≤ j → j < limit → ∀ L' : List ℕ,
        MeetsContract w p embUpdateFromList
          (selEmbUpdateFromListContract w vCap eCap (modelPre.chain.G j) (C'.activeLSF j).F.F L' (C'.activeEmb j))) →
      ZeroFrom mCur sc →
      sc + selectUpdateEmbLoopSpace diffLists cur limit < 2 ^ w →
      ∃ scOut cost out tok2,
        Runs w p ω (selectUpdateEmbLoopBody self embLvlProc)
          (startState [metaBase, cur, limit, tok.handle + 18, selOutBase, cfg.P.d, B.slot, sc]
            mCur pos)
          (.returned scOut) out cost ∧
        sc ≤ scOut ∧
        scOut ≤ sc + selectUpdateEmbLoopSpace diffLists cur limit ∧
        Rrep.rep root modelPre tok2 out.mem ∧
        tok2.table = tok.table ∧ tok2.handle = tok.handle ∧
        tok2.levelsEnd = tok.levelsEnd ∧ tok2.intCap = tok.intCap ∧
        tok2.rootECap = tok.rootECap ∧
        tok2.tree = tok.tree ∧ tok2.trees = tok.trees ∧ tok2.edgeRecords = tok.edgeRecords ∧
        tok2.termHandle = tok.termHandle ∧ tok2.termTok = tok.termTok ∧
        tok2.vcLast = tok.vcLast ∧ tok2.ecLast = tok.ecLast ∧
        (∀ a, Rrep.foot root tok2 a → Rrep.foot root tok a ∨ (sc ≤ a ∧ a < scOut)) ∧
        (∀ a, tok.owned a → tok2.owned a) ∧
        (∀ a < sc, tok2.tag a = tok.tag a) ∧
        (∀ a, tok.tag a ≠ 0 → tok2.tag a = tok.tag a) ∧
        SolverLevelCapsInv P V vCap eCap modelPre tok2 out.mem ∧
        SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tok2 out.mem) pLast) ∧
        SelectHeapAt out.mem loc 4 heapSize ∧
        SelBlocksDataAt out.mem B P
          { D with
            coreE := fun j => if cur ≤ j ∧ j < limit then (C'.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < limit then C'.activeEmb j else D.emb j } pLast ∧
        ZeroFrom out.mem scOut ∧
        (∀ a < sc, ¬ (B.base ≤ a ∧ a < B.endAddr) →
          ¬ (∃ j, cur ≤ j ∧ j < limit ∧ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
          out.mem a = mCur a) ∧
        cost + Rrep.phi root tok2 out.mem ≤
          selectUpdateEmbLoopCost Psc.readout diffLists cur limit B.slot +
            Rrep.phi root tok mCur := by
    intro n
    induction n with
    | zero =>
      intro cur sc pos tok D mCur hsub hcurLe hrep0 _ _ _ hcaps0 htab0 hHeap0 hblk0
        _ _ _ _ _ _ _ hz0 _
      have hcurEq : cur = limit := by omega
      have hSp0 : selectUpdateEmbLoopSpace diffLists cur limit = 0 := by
        unfold selectUpdateEmbLoopSpace; rw [hcurEq, Finset.Ico_self, Finset.sum_empty]
      have hNo : ∀ j, ¬ (cur ≤ j ∧ j < limit) := fun j h => by omega
      have hDEq : ({ D with
            coreE := fun j => if cur ≤ j ∧ j < limit then (C'.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < limit then C'.activeEmb j else D.emb j } : SelBlocksData) = D := by
        cases D; simp [hNo]
      let s0 := startState [metaBase, cur, limit, tok.handle + 18, selOutBase, cfg.P.d, B.slot, sc]
        mCur pos
      have hRun : Runs w p ω (selectUpdateEmbLoopBody self embLvlProc) s0 (.returned sc) s0 6 := by
        unfold selectUpdateEmbLoopBody
        refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hcurEq], ?_,
          by simp [Expr.size]⟩
        exact runs_ret_iff.mpr ⟨sc, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
      refine ⟨sc, 6, s0, tok, hRun, le_refl _, by omega, hrep0,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ ha => Or.inl ha, fun _ ha => ha, fun _ _ => rfl, fun _ _ => rfl, hcaps0, htab0, hHeap0,
        hDEq.symm ▸ hblk0, hz0, fun _ _ _ _ => rfl, ?_⟩
      simp only [s0, startState]; unfold selectUpdateEmbLoopCost; omega
    | succ n ih =>
      intro cur sc pos tok D mCur hsub hcurLe hrep0 hFootSc0 hFootDisj0 hOutW0 hcaps0 htab0
        hHeap0 hblk0 hFM0 hScIn0 hBrLt0 hSlotOut0 hModel0 hFootAt0 hEmb0 hz0 hroom0
      have hcurLt : cur < limit := by omega
      have hcurD : cur < cfg.P.d := lt_of_lt_of_le hcurLt hlimLe
      have hcurB : cur < B.d := by omega
      have hsbLeBase : sb ≤ B.base := by
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
        omega
      have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
      have hsbLtEnd : sb < B.endAddr := by
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
        omega
      have hEndSc0 : B.endAddr ≤ sc := by have := hOutW0.2.1; omega
      have hMetaLe0 : metaBase + selectLevelMetaSize B.d ≤ sc := by have := hreg.2.2.2.1; omega
      have htags := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨hOwn, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, t21⟩ := htags
      have hMC := (solverLevelCapsInv_iff_metaCaps.mp hcaps0).2.2.2.2.2 cur hcurD
      have hCoreCur := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cur hcurD
      set slotCur := selOutBase + 1 + 12 * cur
      set hnd := tok.coreHandle cur
      set br := modelPre.chain.bran cur
      have hSlotCur := hSlotOut0 cur le_rfl hcurLt
      dsimp only at hSlotCur
      obtain ⟨hDiffC, hUGW, hFDelW, hUSW, hReembW⟩ := hSlotCur
      obtain ⟨hListCaps, hEmbSlot, hEmbUnch⟩ := hModel0 cur le_rfl hcurLt
      have hBlkLeEnd : B.fPtr cur + B.levelSize ≤ B.endAddr := by
        have := B.blk_le_last (Nat.le_of_lt hcurB)
        unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
      have hBaseLeF : B.base ≤ B.fPtr cur := by unfold SelectBlocksLoc.fPtr; omega
      have hGLe : solverLevelG tok mCur cur + dynGraphSize vCap eCap ≤ sc := by
        have h1 : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
        have hlast := hFootSc0 (solverLevelG tok mCur cur + dynGraphSize vCap eCap - 1)
          (Or.inl (hOwn _ (by
            have htg := hMC.2.2.2.2 (solverLevelG tok mCur cur + dynGraphSize vCap eCap - 1)
              (by unfold solverLevelG; omega) (by unfold solverLevelG; omega)
            split_ifs at htg <;> omega)))
        omega
      have hGOffBlk : solverLevelG tok mCur cur + dynGraphSize B.vCap B.eCap ≤ B.fPtr cur ∨
          B.fPtr cur + B.levelSize ≤ solverLevelG tok mCur cur := by
        rw [hBv, hBe]
        have hD := interval_disj_region (a := solverLevelG tok mCur cur) (len := dynGraphSize vCap eCap)
          (by unfold dynGraphSize; omega) hsbLtEnd (fun x hx1 hx2 ⟨h1, h2⟩ =>
            hFootDisj0 x hx1 hx2 (Or.inl (hOwn _ (by
              have htg := hMC.2.2.2.2 x (by unfold solverLevelG at h1; exact h1)
                (by unfold solverLevelG at h2; exact h2)
              split_ifs at htg <;> omega))))
        exact hD.imp (by omega) (by omega)
      have hDisjG : ∀ a, solverLevelG tok mCur cur ≤ a →
          a < solverLevelG tok mCur cur + dynGraphSize B.vCap B.eCap →
          ¬ Rcore.foot hnd (tok.coreTok cur) a := by
        rw [hBv, hBe]
        intro a h1 h2 hc
        have ht1 := hMC.2.2.2.2 a (by unfold solverLevelG at h1; exact h1)
          (by unfold solverLevelG at h2; exact h2)
        have ht2 := t21 cur hcurD a hc
        split_ifs at ht1 <;> omega
      have hDisjLists :
          (∀ a, mCur (slotCur + 0) ≤ a → a < mCur (slotCur + 0) + (diffLists cur).uG.length →
            ¬ Rcore.foot hnd (tok.coreTok cur) a) ∧
          (∀ a, mCur (slotCur + 2) ≤ a → a < mCur (slotCur + 2) + (diffLists cur).fDel.length →
            ¬ Rcore.foot hnd (tok.coreTok cur) a) ∧
          (∀ a, mCur (slotCur + 4) ≤ a → a < mCur (slotCur + 4) + (diffLists cur).uS.length →
            ¬ Rcore.foot hnd (tok.coreTok cur) a) ∧
          (∀ a, mCur (slotCur + 6) ≤ a → a < mCur (slotCur + 6) + (diffLists cur).reemb.length →
            ¬ Rcore.foot hnd (tok.coreTok cur) a) :=
        ⟨fun a h1 h2 hc => hUGW.2.2 (a - mCur (slotCur + 0)) (by omega)
            (by rw [Nat.add_sub_of_le h1]; exact Or.inr (Or.inr ⟨cur, hcurD, hc⟩)),
         fun a h1 h2 hc => hFDelW.2.2 (a - mCur (slotCur + 2)) (by omega)
            (by rw [Nat.add_sub_of_le h1]; exact Or.inr (Or.inr ⟨cur, hcurD, hc⟩)),
         fun a h1 h2 hc => hUSW.2.2 (a - mCur (slotCur + 4)) (by omega)
            (by rw [Nat.add_sub_of_le h1]; exact Or.inr (Or.inr ⟨cur, hcurD, hc⟩)),
         fun a h1 h2 hc => hReembW.2.2 (a - mCur (slotCur + 6)) (by omega)
            (by rw [Nat.add_sub_of_le h1]; exact Or.inr (Or.inr ⟨cur, hcurD, hc⟩))⟩
      have hActLSF : C'.activeLSF cur = cfg.T.lsfs (modelPre.chain.scState cur) br := by
        simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hcurD, br]
      have hActCore : C'.activeCore cur =
          coreGraph (modelPre.chain.G cur) (cfg.T.lsfs (modelPre.chain.scState cur) br) := by
        rw [TreeChain.activeCore, hActLSF]; rfl
      have hActEmb : C'.activeEmb cur = cfg.T.emb (modelPre.chain.scState cur) br := by
        simp [C', TreeChain.activeEmb, ChainState.toTreeChain, hcurD, br]
      have hSpSplit : selectUpdateEmbLoopSpace diffLists cur limit =
          selectUpdateEmbSpace (diffLists cur).uG.length (diffLists cur).fDel.length
            (diffLists cur).uS.length (diffLists cur).reemb.length +
          selectUpdateEmbLoopSpace diffLists (cur + 1) limit := by
        unfold selectUpdateEmbLoopSpace; rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]
      have hCostSplit : selectUpdateEmbLoopCost Psc.readout diffLists cur limit B.slot =
          (selectUpdateEmbCost Psc.readout (diffLists cur).uG.length (diffLists cur).fDel.length
            (diffLists cur).uS.length (diffLists cur).reemb.length B.slot + 70) +
          selectUpdateEmbLoopCost Psc.readout diffLists (cur + 1) limit B.slot := by
        unfold selectUpdateEmbLoopCost; rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]; omega
      have hHndW : hnd < 2 ^ w :=
        lt_of_lt_of_le (hFootSc0 _ (Or.inl (hcaps0.1.2.1 cur hcurD))) (by omega)
      -- Step 1: call `selectUpdateEmbLevelBody` at level `cur`
      obtain ⟨sc1, c1, st1, y1, hr1, hsc1Lo, hsc1Hi, hCoreRep1, hblk1, hz1, hCoreFoot1, hFr1, hc1⟩ :=
        selectUpdateEmbLevel_runs (fmt := fmt) (j := cur) (pLast := pLast)
          (handle := hnd) (branch := br) (slot := slotCur) (scratch := sc) (pos := pos)
          (B := B) (metaBase := metaBase) (solverG := solverLevelG tok mCur) (D := D)
          (a := chainLevelOrdAbs modelPre.chain cur) (x := tok.coreTok cur)
          (L := diffLists cur) (mem := mCur)
          hlocalCore hw16 hSlotW hcurB (hBrLt0 cur le_rfl hcurLt) hkW hHndW
          htab0 (hfmtP ▸ hblk0) hMetaLe0 hEndSc0
          (hBv ▸ hBe ▸ hMC.1) (hBv ▸ hBe ▸ hGLe) hGOffBlk
          (by dsimp only [chainLevelOrdAbs]; rw [← hActLSF]; exact hFM0 cur le_rfl hcurLt)
          hCoreCur.2.2 (hScIn0 cur le_rfl hcurLt)
          (fun a ha => hFootSc0 a (Or.inr (Or.inr ⟨cur, hcurD, ha⟩)))
          (fun a h1 h2 hc => hFootDisj0 a (by omega) h2 (Or.inr (Or.inr ⟨cur, hcurD, hc⟩)))
          hDisjG hDisjLists (hBv ▸ hBe ▸ hBLk ▸ hFootAt0 cur le_rfl hcurLt)
          hDiffC (by have := hOutW0.2.1; dsimp only [slotCur]; omega)
          hUGW.2.1 (Or.inr (le_trans hBlkLeEnd (le_trans hEndLeOut hUGW.1)))
          hFDelW.2.1 (Or.inr (le_trans hBlkLeEnd (le_trans hEndLeOut hFDelW.1)))
          hUSW.2.1 (Or.inr (le_trans hBlkLeEnd (le_trans hEndLeOut hUSW.1)))
          hReembW.2.1 (Or.inr (le_trans hBlkLeEnd (le_trans hEndLeOut hReembW.1)))
          (hBe ▸ hListCaps)
          (fun e he => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            rw [← hActEmb]; exact hEmbSlot e (hActCore.symm ▸ he))
          (fun e he hu hf hus hr => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            rw [← hActEmb]; exact hEmbUnch e (hActCore.symm ▸ he) hu hf hus hr)
          (fun L' => by
            dsimp only [chainLevelOrdAbs]
            rw [hBv, hBe, ← hActLSF, ← hActEmb]
            exact hEmb0 cur le_rfl hcurLt L')
          hz0 (by omega)
      -- Update solver token via `memM`
      have hFr1OffCore : ∀ a < sc, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          (a < sb ∨ B.endAddr ≤ a) → st1.mem a = mCur a := fun a ha hnc hoff =>
        hFr1 a ha hnc fun hre => by have := regEmb_in_blocks (Nat.le_of_lt hcurB) hre; omega
      have hFr1Foot : ∀ a < sc, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          Rrep.foot root tok a → st1.mem a = mCur a := fun a ha hnc hf =>
        hFr1OffCore a ha hnc (by
          by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
          exact hFootDisj0 a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) hf)
      let tok1 : SolverToken cfg L Rcore :=
        { tok with
          coreTok := Function.update tok.coreTok cur y1
          owned := fun a => tok.owned a ∨ (sc ≤ a ∧ a < sc1)
          tag := fun a => if sc ≤ a ∧ a < sc1 then 21 + cur else tok.tag a }
      let memM : ℕ → ℕ := fun a => if sb ≤ a ∧ a < B.endAddr then mCur a else st1.mem a
      have hFrM : ∀ a < sc, ¬ Rcore.foot hnd (tok.coreTok cur) a → memM a = mCur a :=
        fun a ha hnc => by
          dsimp only [memM]; split_ifs with hrg
          · rfl
          · exact hFr1OffCore a ha hnc (by
              by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
              exact hrg ⟨Nat.le_of_not_lt h1, Nat.lt_of_not_le h2⟩)
      have hY1DisjReg : ∀ a, Rcore.foot hnd y1 a → ¬ (sb ≤ a ∧ a < B.endAddr) := fun a ha hrg => by
        rcases hCoreFoot1 a ha with hold | hnew
        · exact hFootDisj0 a hrg.1 hrg.2 (Or.inr (Or.inr ⟨cur, hcurD, hold⟩))
        · omega
      have hrepY1M : Rcore.rep hnd (chainLevelOrdAbs modelPre.chain cur) y1 memM :=
        (hlocalCore hnd (chainLevelOrdAbs modelPre.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).1 hCoreRep1
      obtain ⟨hrep1M, hfoot1, hphi1M⟩ :=
        solverStateRep_update_coreTok hlocalCore hcurD hrep0 hFootSc0 hFrM hrepY1M hCoreFoot1
      have hFoot1Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok1 a := fun a h1 h2 hf1 => by
        rcases hfoot1 a hf1 with hf0 | hnew
        · exact hFootDisj0 a h1 h2 hf0
        · omega
      have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
      have hrep1 : Rrep.rep root modelPre tok1 st1.mem :=
        (hRrepLoc root modelPre tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).1 hrep1M
      have hphi1Eq : Rrep.phi root tok1 st1.mem = Rrep.phi root tok1 memM :=
        ((hRrepLoc root modelPre tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).2).symm
      have hphiY1Eq : Rcore.phi hnd y1 memM = Rcore.phi hnd y1 st1.mem :=
        ((hlocalCore hnd (chainLevelOrdAbs modelPre.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).2).symm
      have hcaps1 : SolverLevelCapsInv P V vCap eCap modelPre tok1 st1.mem := by
        refine hcaps0.preserve rfl (fun j hj => Or.inl (hcaps0.1.2.1 j hj)) (fun a ha => ?_)
          (fun j hj => Or.inl (SolverLevelMetaAt.atCaps hcaps0.1 hcaps0.2 j hj).2.2.1)
          rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
        have hne0 : tok.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have hlt := hFootSc0 a (Or.inl (hOwn a hne0))
        have hnc : ¬ Rcore.foot hnd (tok.coreTok cur) a := fun hc => by
          have := t21 cur hcurD a hc; rcases ha with h | h | h | h <;> omega
        exact ⟨by dsimp only [tok1]; rw [ite_eq_right (by omega)],
          hFr1Foot a hlt hnc (Or.inl (hOwn a hne0))⟩
      have hMlocEq1 : selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast =
          selectMlocOf B metaBase (solverLevelG tok mCur) pLast :=
        selectMlocOf_congr_emb fun j hj => by
          rw [hBd] at hj
          have htag := hcaps0.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
          rw [← Nat.add_assoc] at htag
          have hlt := hFootSc0 _ (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
            (by omega)))
          have hnc : ¬ Rcore.foot hnd (tok.coreTok cur)
              (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := fun hc => by
            have := t21 cur hcurD _ hc; omega
          exact hFr1Foot _ hlt hnc (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
            (by omega)))
      have hLocLeBase : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
      have htab1 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast) := by
        rw [hMlocEq1]
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        exact htab0.of_agree fun a ha1 ha2 => hFr1 a (by simp only [selectMlocOf] at ha2; omega)
          (fun hc => hFootDisj0 a (by simp only [selectMlocOf] at ha1; omega)
            (by simp only [selectMlocOf] at ha2; omega) (Or.inr (Or.inr ⟨cur, hcurD, hc⟩)))
          (fun hre => by
            have := regEmb_in_blocks (Nat.le_of_lt hcurB) hre
            simp only [selectMlocOf] at ha2; omega)
      have hHeap1 : SelectHeapAt st1.mem loc 4 heapSize :=
        hHeap0.of_agree fun a ha1 ha2 => by
          have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
          exact hFr1 a (by omega)
            (fun hc => hFootDisj0 a (by omega) (by omega) (Or.inr (Or.inr ⟨cur, hcurD, hc⟩)))
            (fun hre => by have := regEmb_in_blocks (Nat.le_of_lt hcurB) hre; omega)
      let D1 : SelBlocksData :=
        { D with
          coreE := Function.update D.coreE cur (C'.activeCore cur).E
          emb := Function.update D.emb cur (C'.activeEmb cur) }
      have hblk1' : SelBlocksDataAt st1.mem B P D1 pLast := by
        rw [hfmtP] at hblk1
        dsimp only [chainLevelOrdAbs] at hblk1
        dsimp only [D1]; rw [hActCore, hActEmb]; exact hblk1
      have hWordsKeep : ∀ a len, SelOutWordsAt (Rrep.foot root tok) selOutBase sc a len →
          (∀ t < len, st1.mem (a + t) = mCur (a + t)) ∧
          SelOutWordsAt (Rrep.foot root tok1) selOutBase sc1 a len := fun a len ha =>
        ⟨fun t ht => hFr1OffCore (a + t) (by have := ha.2.1; omega)
          (fun hc => ha.2.2 t ht (Or.inr (Or.inr ⟨cur, hcurD, hc⟩)))
          (Or.inr (by have := ha.1; omega)),
         ⟨ha.1, le_trans ha.2.1 hsc1Lo, fun t ht hf1 => by
           rcases hfoot1 (a + t) hf1 with hf0 | hnew
           · exact ha.2.2 t ht hf0
           · have := ha.2.1; omega⟩⟩
      obtain ⟨hOutAg1, hOutW1⟩ := hWordsKeep selOutBase (1 + 12 * limit) hOutW0
      -- Recursive call on `cur + 1`
      obtain ⟨scOut, cRec, out, tok2, hrRec, hscOutLo, hscOutHi, hrepOut, htabOutEq, hhndOutEq,
          hlevOutEq, hintOutEq, hrecOutEq, htreeOutEq, htreesOutEq, hedgOutEq,
          hthOutEq, httOutEq, hvcOutEq, hecOutEq,
          hftOut, hOwnOut, hTagLtOut, hTagOut, hcapsOut, htabOut, hHeapOut, hblkOut, hzOut, hfrOut, hcRec⟩ :=
        ih (cur + 1) sc1 st1.pos tok1 D1 st1.mem (by omega) (by omega) hrep1
          (fun a ha => by rcases hfoot1 a ha with h0 | hnew; exact lt_of_lt_of_le (hFootSc0 a h0) hsc1Lo; exact hnew.2)
          hFoot1Disj hOutW1 hcaps1 htab1 hHeap1 hblk1'
          (fun j hj1 hj2 => hFM0 j (by omega) hj2)
          (fun j hj1 hj2 => hScIn0 j (by omega) hj2)
          (fun j hj1 hj2 => hBrLt0 j (by omega) hj2)
          (fun j hj1 hj2 => by
            obtain ⟨hD, hU, hF, hS, hR⟩ := hSlotOut0 j (by omega) hj2
            have hSAg : ∀ t < 12, st1.mem (selOutBase + 1 + 12 * j + t) =
                mCur (selOutBase + 1 + 12 * j + t) := fun t ht => by
              have h := hOutAg1 (1 + 12 * j + t) (by omega)
              rwa [← Nat.add_assoc, ← Nat.add_assoc] at h
            obtain ⟨hUAg, hUW1⟩ := hWordsKeep _ _ hU
            obtain ⟨hFAg, hFW1⟩ := hWordsKeep _ _ hF
            obtain ⟨hSAgL, hSW1⟩ := hWordsKeep _ _ hS
            obtain ⟨hRAg, hRW1⟩ := hWordsKeep _ _ hR
            refine ⟨⟨(hSAg 1 (by omega)).trans hD.1,
              fun i hi => by rw [hSAg 0 (by omega)]; exact (hUAg i hi).trans (hD.2.1 i hi),
              (hSAg 3 (by omega)).trans hD.2.2.1,
              fun i hi => by rw [hSAg 2 (by omega)]; exact (hFAg i hi).trans (hD.2.2.2.1 i hi),
              (hSAg 5 (by omega)).trans hD.2.2.2.2.1,
              fun i hi => by rw [hSAg 4 (by omega)]; exact (hSAgL i hi).trans (hD.2.2.2.2.2.1 i hi),
              (hSAg 7 (by omega)).trans hD.2.2.2.2.2.2.1,
              fun i hi => by rw [hSAg 6 (by omega)]; exact (hRAg i hi).trans (hD.2.2.2.2.2.2.2 i hi)⟩,
              by rw [hSAg 0 (by omega)]; exact hUW1,
              by rw [hSAg 2 (by omega)]; exact hFW1,
              by rw [hSAg 4 (by omega)]; exact hSW1,
              by rw [hSAg 6 (by omega)]; exact hRW1⟩)
          (fun j hj1 hj2 => by
            obtain ⟨hc, hs, hu⟩ := hModel0 j (by omega) hj2
            refine ⟨hc, hs, fun e he h1 h2 h3 h4 => ?_⟩
            dsimp only [D1]; simp only [Function.update_of_ne (show j ≠ cur by omega)]
            exact hu e he h1 h2 h3 h4)
          (fun j hj1 hj2 => hFootAt0 j (by omega) hj2)
          (fun j hj1 hj2 => hEmb0 j (by omega) hj2)
          hz1 (by omega)
      -- Stitch current step + recursive call into `selectUpdateEmbLoopBody`
      let s0 := startState [metaBase, cur, limit, tok.handle + 18, selOutBase, cfg.P.d, B.slot, sc]
        mCur pos
      have hHndCurLt : tok.handle + 18 + cur < sc :=
        hFootSc0 _ (Or.inl (hOwn _ (by rw [hT4 cur (by omega)]; decide)))
      have hBrCurLt : tok.handle + 18 + (cfg.P.d + 1) + cur < sc := by
        have h := hT4 ((cfg.P.d + 1) + cur) (by omega)
        rw [← Nat.add_assoc] at h
        exact hFootSc0 _ (Or.inl (hOwn _ (by rw [h]; decide)))
      let rg8 := Function.update s0.regs 8 slotCur
      let rg9 := Function.update rg8 9 hnd
      let rg10 := Function.update rg9 10 br
      let rg11 := Function.update rg10 11 sc1
      let rg12 := Function.update rg11 12 scOut
      have h1 : Runs w p ω
          (.assign 8 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 1))))
          s0 .normal ⟨mCur, rg8, pos⟩ 8 :=
        runs_assign_iff.mpr ⟨slotCur, by
          simp [Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega,
            show 12 < 2 ^ w by omega, show selOutBase + 1 < 2 ^ w by have := hOutW0.2.1; omega,
            show 12 * cur < 2 ^ w by have := hOutW0.2.1; omega,
            show slotCur < 2 ^ w by have := hOutW0.2.1; dsimp only [slotCur]; omega, slotCur],
          rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 3) (.reg 1))))
          ⟨mCur, rg8, pos⟩ .normal ⟨mCur, rg9, pos⟩ 5 :=
        runs_assign_iff.mpr ⟨hnd, by
          simp [Expr.eval, BinOp.eval, rg8, s0, startState, hnd, hCoreCur.1,
            show tok.handle + 18 + cur < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω
          (.assign 10 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 5) (.const 1))) (.reg 1))))
          ⟨mCur, rg9, pos⟩ .normal ⟨mCur, rg10, pos⟩ 9 :=
        runs_assign_iff.mpr ⟨br, by
          simp [Expr.eval, BinOp.eval, rg9, rg8, s0, startState, show 1 < 2 ^ w by omega,
            show cfg.P.d + 1 < 2 ^ w by omega,
            show tok.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega,
            show tok.handle + 18 + (cfg.P.d + 1) + cur < 2 ^ w by omega,
            br, hCoreCur.2.1],
          rfl, rfl, by simp [Expr.size]⟩
      have h4 : Runs w p ω
          (.call 11 embLvlProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 10, .reg 6, .reg 7])
          ⟨mCur, rg10, pos⟩ .normal ⟨st1.mem, rg11, st1.pos⟩ (c1 + 8) :=
        runs_call_iff.mpr ⟨[metaBase, cur, slotCur, hnd, br, B.slot, sc], _, .returned sc1, st1, c1,
          by simp [evalArgs, Expr.eval, rg10, rg9, rg8, s0, startState],
          hpEmbLvl, hr1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have h5 : Runs w p ω
          (.call 12 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5,
            .reg 6, .reg 11])
          ⟨st1.mem, rg11, st1.pos⟩ .normal ⟨out.mem, rg12, out.pos⟩ (cRec + 11) :=
        runs_call_iff.mpr ⟨[metaBase, cur + 1, limit, tok1.handle + 18, selOutBase, cfg.P.d,
          B.slot, sc1], _, .returned scOut, out, cRec,
          by simp [evalArgs, Expr.eval, BinOp.eval, rg11, rg10, rg9, rg8, s0, startState,
            show 1 < 2 ^ w by omega, show cur + 1 < 2 ^ w by omega, tok1],
          hpLoop, hrRec, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have h6 : Runs w p ω (.ret (.reg 12))
          ⟨out.mem, rg12, out.pos⟩ (.returned scOut) ⟨out.mem, rg12, out.pos⟩ 2 :=
        runs_ret_iff.mpr ⟨scOut, by simp [Expr.eval, rg12], rfl, rfl, rfl⟩
      have hRunFull : Runs w p ω (selectUpdateEmbLoopBody self embLvlProc) s0 (.returned scOut)
            ⟨out.mem, rg12, out.pos⟩ (c1 + cRec + 52) := by
        unfold selectUpdateEmbLoopBody
        refine runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, s0, startState, hcurLt, show 1 < 2 ^ w by omega],
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h2,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h3,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, h4,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, h5, h6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          by simp [Expr.size]; omega⟩
      have hDEqFinal :
          ({ D1 with
              coreE := fun j => if cur + 1 ≤ j ∧ j < limit then (C'.activeCore j).E else D1.coreE j
              emb := fun j => if cur + 1 ≤ j ∧ j < limit then C'.activeEmb j else D1.emb j } :
            SelBlocksData) =
          { D with
              coreE := fun j => if cur ≤ j ∧ j < limit then (C'.activeCore j).E else D.coreE j
              emb := fun j => if cur ≤ j ∧ j < limit then C'.activeEmb j else D.emb j } := by
        cases D
        simp only [D1, SelBlocksData.mk.injEq, true_and, and_true]
        constructor <;> (funext j; by_cases hjeq : j = cur
                         · subst hjeq; simp [hcurLt]
                         · by_cases hjr : cur + 1 ≤ j ∧ j < limit
                           · simp [hjr, show cur ≤ j ∧ j < limit by omega]
                           · simp [show ¬ (cur ≤ j ∧ j < limit) by omega, Function.update_of_ne hjeq]
                             intro h1 h2; omega)
      refine ⟨scOut, _, ⟨out.mem, rg12, out.pos⟩, tok2, hRunFull, by omega, by omega,
        hrepOut, htabOutEq, hhndOutEq, hlevOutEq, hintOutEq, hrecOutEq, htreeOutEq, htreesOutEq,
        hedgOutEq, hthOutEq, httOutEq, hvcOutEq, hecOutEq,
        fun a ha => by
          rcases hftOut a ha with h1 | h2
          · rcases hfoot1 a h1 with h0 | hnew
            · exact Or.inl h0
            · exact Or.inr ⟨hnew.1, lt_of_lt_of_le hnew.2 hscOutLo⟩
          · exact Or.inr ⟨le_trans hsc1Lo h2.1, h2.2⟩,
        fun a ha => hOwnOut a (Or.inl ha),
        fun a ha => (hTagLtOut a (lt_of_lt_of_le ha hsc1Lo)).trans (by dsimp only [tok1]; rw [ite_eq_right (by omega)]),
        fun a ha => (hTagOut a (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc0 a (Or.inl (hOwn a ha)); omega)]; exact ha)).trans
          (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc0 a (Or.inl (hOwn a ha)); omega)]),
        hcapsOut, htabOut, hHeapOut, hDEqFinal ▸ hblkOut, hzOut,
        fun a ha hnb hnc => by
          have hnc1 : ¬ (∃ j, cur + 1 ≤ j ∧ j < limit ∧ Rcore.foot (tok1.coreHandle j) (tok1.coreTok j) a) := by
            rintro ⟨j, hj1, hj2, hfj⟩
            dsimp only [tok1] at hfj
            rw [Function.update_of_ne (by omega)] at hfj
            exact hnc ⟨j, by omega, hj2, hfj⟩
          exact (hfrOut a (lt_of_lt_of_le ha hsc1Lo) hnb hnc1).trans
            (hFr1 a ha (fun hc => hnc ⟨cur, le_rfl, hcurLt, hc⟩)
              (fun hre => hnb (regEmb_in_blocks (Nat.le_of_lt hcurB) hre))), ?_⟩
      change c1 + Rcore.phi hnd y1 st1.mem ≤
        selectUpdateEmbCost Psc.readout (diffLists cur).uG.length (diffLists cur).fDel.length
          (diffLists cur).uS.length (diffLists cur).reemb.length B.slot + Rcore.phi hnd (tok.coreTok cur) mCur at hc1
      simp only [Expr.size, argsSize]
      dsimp only [Rrep, hnd, tok1] at hphi1M hphi1Eq hphiY1Eq hcRec hc1 ⊢
      rw [hCostSplit]; omega
  exact hInd (limit - cur) cur scratch pos tok' D mem rfl hcurLe hrep hFootSc hFootDisj hOutWords
    hcaps htab hHeap hblk hFMatch hScIn hBrLt hSlotOut hModel hFootAt hEmbUpd hz hroom

end MinCostFlow.MinRatio
