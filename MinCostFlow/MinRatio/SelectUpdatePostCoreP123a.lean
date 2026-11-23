module

public import MinCostFlow.MinRatio.SelectUpdatePostCoreAux
public import MinCostFlow.MinRatio.SelectUpdateModel
public import MinCostFlow.MinRatio.WireSelectTouchedWstr
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Post-core select-update prefix phases 1–3a (`SelectUpdatePostCoreP123a`)

Verifies Phases 1, 2, 3a-1, and 3a-2 of `selectUpdatePostCoreBody`:
1. `selTableWriteBody` — refresh the select metadata table for `modelPre`.
2. `selUpdateG0Body` — refresh level-0 gradients `B.g0Ptr` from `(slots, edgeRecords, treeHeap)`.
3. `selectUpdateFPhiLenLoopBody` — update `F`, `φ`, and `coreLen` on non-rebuilt levels `0 .. lim - 1`.
4. `selectUpdateEmbLoopBody` — update embeddings on non-rebuilt levels `0 .. lim - 1`.

Split from `SelectUpdatePostCore.lean` to keep both modules concise and fast to compile.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Bundle Chain Chain.Ordered IPM.Machine Num DynSpanner.Program SparseCore SparseCore.Program

lemma coreBatchTouchedEdges_eq_batchTouchedEdges :
    ∀ U : List Update, coreBatchTouchedEdges U = batchTouchedEdges U
  | [] => rfl
  | .insert _ _ _ :: rest => congrArg _ (coreBatchTouchedEdges_eq_batchTouchedEdges rest)
  | .delete _ :: rest => congrArg _ (coreBatchTouchedEdges_eq_batchTouchedEdges rest)
  | .split _ _ _ _ :: rest => coreBatchTouchedEdges_eq_batchTouchedEdges rest

lemma selOutWordsAt_bump_hi {foot : ℕ → Prop} {lo hi hi' a n : ℕ}
    (h : SelOutWordsAt foot lo hi a n) (hle : hi ≤ hi') :
    SelOutWordsAt foot lo hi' a n :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2⟩

lemma selOutTableAt_bump_hi {w lo hi hi' a Lw : ℕ} {foot : ℕ → Prop}
    {mem : ℕ → ℕ} {E : Finset ℕ}
    (h : SelOutTableAt w foot lo hi mem a Lw E) (hle : hi ≤ hi') :
    SelOutTableAt w foot lo hi' mem a Lw E :=
  ⟨h.1, fun e he => ⟨le_trans (h.2 e he).1 hle,
    fun t ht => ((h.2 e he).2 t ht).elim Or.inl (fun h2 => Or.inr ⟨h2.1, lt_of_lt_of_le h2.2 hle⟩)⟩⟩

lemma selOutTableAt_congr_mem {w lo hi a Lw : ℕ} {foot : ℕ → Prop}
    {m1 m2 : ℕ → ℕ} {E : Finset ℕ}
    (h : SelOutTableAt w foot lo hi m1 a Lw E) (hm : m2 a = m1 a) :
    SelOutTableAt w foot lo hi m2 a Lw E :=
  ⟨hm ▸ h.1, fun e he => by rw [hm]; exact h.2 e he⟩

set_option maxHeartbeats 1600000 in
/-- Verification of Phases 1, 2, 3a-1, and 3a-2 of `selectUpdatePostCoreBody`. Returns the
intermediate states, token `tok3`, `Runs` witnesses, block data `D3`, and non-core frame needed
by `selectUpdatePostCore_runs` (`SelectUpdatePostCore.lean`). -/
theorem selectUpdatePostCore_prefix_runs
    {w L P m V psi k epsExp drainUnit depth capExp vCap eCap pLast sb metaBase
      selOutBase scratch pos : ℕ}
    {tableWriteProc g0Proc copyOne filterPres
      fPhiLenLoopProc fPhiLenLvlProc dgApplyBatch delEdgeList batchCopySplits coreLenFill coreLenEdge
      embLoopProc embLvlProc embUpdateFromList : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G₀ G₀' : MGraph}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root firstReb : ℕ} {model modelPre : Alg2State cfg}
    {tok' : SolverToken cfg L Rcore} {sg : SelectGhost} {B : SelectBlocksLoc}
    {levelU levelUS : ℕ → List Update} {diffLists : ℕ → LevelDiffLists} {memCore : ℕ → ℕ}
    (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hLpos : 0 < L) (hLkW : L < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) (hSlotW : B.slot < 2 ^ w) (hdPos : 0 < cfg.P.d)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' memCore)
    (hcaps : SolverLevelCapsInv P V vCap eCap modelPre tok' memCore)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hEndLeOut : B.endAddr ≤ selOutBase)
    (hreg : SelectRegion sb sg.loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hBlkOld : SelectBlocksAt memCore B P model.chain.toTreeChain model.chain.g model.chain.ℓ
      sg.φ pLast)
    (hHeapOld : SelectHeapAt memCore sg.loc 4 sg.size)
    (hModOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hModNew : SelectModelInv modelPre G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hLink : UpdateCoreLevelLink model.chain modelPre.chain firstReb levelU levelUS)
    (hOutAt : UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore |>.foot root tok')
      memCore selOutBase scratch firstReb model.chain modelPre.chain levelU levelUS diffLists)
    (hStLwW : ∀ j < min firstReb cfg.P.d, memCore (selOutBase + 1 + 12 * j + 9) < 2 ^ w)
    (hgEqNew : ∀ e ∈ (modelPre.chain.G 0).E, modelPre.chain.g e = modelPre.extg (modelPre.intToExt e))
    (hgFitNew : ∀ e ∈ (modelPre.chain.G 0).E, ∀ z : ℤ,
      (z : ℝ) / (2 : ℝ) ^ P = modelPre.chain.g e → Num.Fits 4 L z ∧ Num.Fits 4 L (-z))
    (hBranchA : firstReb = 0 → (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m)
    (hgSurv : 0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
      modelPre.chain.g e = model.chain.g e)
    (hPrefModel : ∀ j < min firstReb cfg.P.d,
      let C := model.chain.toTreeChain
      let C' := modelPre.chain.toTreeChain
      (∀ e ∈ (C'.activeLSF j).F.F.E, Update.delete e ∉ levelU j) ∧
      (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E ∧
      (∀ e ∈ (diffLists j).uS, e < eCap) ∧
      (∀ e ∈ (diffLists j).reemb, e < eCap) ∧
      (∀ e ∈ (C'.G j).E, e ∉ (diffLists j).uG →
        e ∈ (C.G j).E ∧ C'.chainLen modelPre.chain.ℓ (j + 1) e = C.chainLen model.chain.ℓ (j + 1) e) ∧
      (∀ e ∈ (C'.activeCore j).E,
        e ∉ (diffLists j).uG → e ∉ (diffLists j).fDel → e ∉ (diffLists j).uS →
        e ∉ (diffLists j).reemb →
        e ∈ (C.activeCore j).E ∧ C'.activeEmb j e = C.activeEmb j e) ∧
      SparseCoreOrdInput cfg.T cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
        (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
        (modelPre.chain.updCount j) ∧
      modelPre.chain.bran j < cfg.P.k)
    (hLenFitAll : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e)
    (hEmbSlot : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
      (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ B.slot)
    (hTableWrite : MeetsContract w p tableWriteProc
      (selTableWriteContract w B metaBase (solverLevelMetaAddr tok'.table cfg.P.d) pLast))
    (hpG0 : p.procs[g0Proc]? = some (selUpdateG0Body copyOne filterPres))
    (hCopyOne : ∀ val : ℤ, MeetsContract w p copyOne (selCopyG0OneContract w eCap val))
    (hFilterPres : ∀ L' : List ℕ, MeetsContract w p filterPres (selFilterPresentContract w L'))
    (hpFPLLoop : p.procs[fPhiLenLoopProc]? = some (selectUpdateFPhiLenLoopBody fPhiLenLoopProc fPhiLenLvlProc))
    (hpFPLLvl : p.procs[fPhiLenLvlProc]? =
      some (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill))
    (hDgBatch : ∀ j < min firstReb cfg.P.d,
      MeetsContract w p dgApplyBatch
        (dgApplyBatchContract w vCap eCap (model.chain.G j)
          (model.chain.toTreeChain.activeLSF j).F.F (levelU j) (memCore (selOutBase + 1 + 12 * j + 11))))
    (hDelList : ∀ j < min firstReb cfg.P.d,
      MeetsContract w p delEdgeList
        (dgDeleteEdgeListContract w vCap eCap
          ((levelU j).foldl (dgBatchTarget 0) (model.chain.toTreeChain.activeLSF j).F.F)
          (diffLists j).fDel))
    (hSplits : ∀ j < min firstReb cfg.P.d,
      MeetsContract w p batchCopySplits
        (selBatchCopySplitsContract w vCap P (model.chain.G j) (levelU j)
          (memCore (selOutBase + 1 + 12 * j + 11)) (sg.φ j)))
    (hpCoreLen : p.procs[coreLenFill]? = some (selCoreLenFillBody coreLenEdge))
    (hCoreLenEdge : MeetsContract w p coreLenEdge (selCoreLenEdgeContract w P))
    (hpEmbLoop : p.procs[embLoopProc]? = some (selectUpdateEmbLoopBody embLoopProc embLvlProc))
    (hpEmbLvl : p.procs[embLvlProc]? = some (selectUpdateEmbLevelBody (op 4) embUpdateFromList))
    (hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hEmbUpd : ∀ j < min firstReb cfg.P.d, ∀ L' : List ℕ,
      MeetsContract w p embUpdateFromList
        (selEmbUpdateFromListContract w vCap eCap (modelPre.chain.G j)
          (modelPre.chain.toTreeChain.activeLSF j).F.F L'
          (modelPre.chain.toTreeChain.activeEmb j)))
    (hz : ZeroFrom memCore scratch)
    (hroom :
      let stLw := fun j => memCore (selOutBase + 1 + 12 * j + 9)
      let lim := min firstReb cfg.P.d
      scratch + selUpdateG0Space firstReb (diffLists 0).uG.length +
        selectUpdateFPhiLenLoopSpace diffLists stLw 0 lim L +
        selectUpdateEmbLoopSpace diffLists 0 lim < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let C := model.chain.toTreeChain
    let C' := modelPre.chain.toTreeChain
    let d := cfg.P.d
    let lim := min firstReb d
    let stLw := fun j => memCore (selOutBase + 1 + 12 * j + 9)
    let uWords := fun j => memCore (selOutBase + 1 + 12 * j + 11)
    let D3 : SelBlocksData :=
      { SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ with
        E0 := (modelPre.chain.G 0).E
        g := modelPre.chain.g
        F := fun j => if 0 ≤ j ∧ j < lim then (C'.activeLSF j).F.F else (C.activeLSF j).F.F
        V := fun j => if 0 ≤ j ∧ j < lim then (C'.G j).V else (C.G j).V
        φ := fun j => if 0 ≤ j ∧ j < lim then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
        E := fun j => if 0 ≤ j ∧ j < lim then (C'.G j).E else (C.G j).E
        len := fun j => if 0 ≤ j ∧ j < lim then C'.chainLen modelPre.chain.ℓ (j + 1)
          else C.chainLen model.chain.ℓ (j + 1)
        coreE := fun j => if 0 ≤ j ∧ j < lim then (C'.activeCore j).E else (C.activeCore j).E
        emb := fun j => if 0 ≤ j ∧ j < lim then C'.activeEmb j else C.activeEmb j }
    ∃ bTW oTW stTW st1 st2 st3 sc1 sc2 sc3 cTW cG0 cFPL cEmb tok3,
      p.procs[tableWriteProc]? = some bTW ∧
      Runs w p ω bTW
        (startState [metaBase, B.base, d, vCap, eCap, L, B.slot,
          solverLevelMetaAddr tok'.table d, pLast] memCore pos) oTW stTW cTW ∧
      Runs w p ω (selUpdateG0Body copyOne filterPres)
        (startState [firstReb, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
          solverLevelG tok' memCore 0, vCap, selOutBase + 1, L, scratch] stTW.mem stTW.pos)
        (.returned sc1) st1 cG0 ∧
      Runs w p ω (selectUpdateFPhiLenLoopBody fPhiLenLoopProc fPhiLenLvlProc)
        (startState [metaBase, 0, lim, solverLevelMetaAddr tok'.table d, selOutBase, d, L, sc1]
          st1.mem st1.pos) (.returned sc2) st2 cFPL ∧
      Runs w p ω (selectUpdateEmbLoopBody embLoopProc embLvlProc)
        (startState [metaBase, 0, lim, tok'.handle + 18, selOutBase, d, B.slot, sc2]
          st2.mem st2.pos) (.returned sc3) st3 cEmb ∧
      scratch ≤ sc1 ∧ sc1 ≤ sc2 ∧ sc2 ≤ sc3 ∧
      sc3 ≤ scratch + selUpdateG0Space firstReb (diffLists 0).uG.length +
        selectUpdateFPhiLenLoopSpace diffLists stLw 0 lim L +
        selectUpdateEmbLoopSpace diffLists 0 lim ∧
      Rrep.rep root modelPre tok3 st3.mem ∧
      tok3.table = tok'.table ∧ tok3.handle = tok'.handle ∧
      tok3.levelsEnd = tok'.levelsEnd ∧ tok3.intCap = tok'.intCap ∧
      tok3.rootECap = tok'.rootECap ∧
      tok3.tree = tok'.tree ∧ tok3.trees = tok'.trees ∧ tok3.edgeRecords = tok'.edgeRecords ∧
      tok3.termHandle = tok'.termHandle ∧ tok3.termTok = tok'.termTok ∧
      tok3.vcLast = tok'.vcLast ∧ tok3.ecLast = tok'.ecLast ∧
      (∀ a, Rrep.foot root tok3 a → Rrep.foot root tok' a ∨ (scratch ≤ a ∧ a < sc3)) ∧
      (∀ a, tok'.owned a → tok3.owned a) ∧
      (∀ a < scratch, tok3.tag a = tok'.tag a) ∧
      (∀ a, tok'.tag a ≠ 0 → tok3.tag a = tok'.tag a) ∧
      SolverLevelCapsInv P V vCap eCap modelPre tok3 st3.mem ∧
      SelectMetaTableAt st3.mem (selectMlocOf B metaBase (solverLevelG tok3 st3.mem) pLast) ∧
      SelectHeapAt st3.mem sg.loc 4 sg.size ∧
      SelBlocksDataAt st3.mem B P D3 pLast ∧
      ZeroFrom st3.mem sc3 ∧
      (∀ a < scratch, ¬ (metaBase ≤ a ∧ a < B.endAddr) →
        (∀ j < d, tok'.tag a ≠ 21 + j) → st3.mem a = memCore a) ∧
      cTW ≤ 240 * d + 840 ∧
      cG0 ≤ selUpdateG0Cost firstReb (modelPre.chain.G 0).m (diffLists 0).uG.length L ∧
      cFPL ≤ selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw 0 lim L ∧
      cEmb + Rrep.phi root tok3 st3.mem ≤
        selectUpdateEmbLoopCost Psc.readout diffLists 0 lim B.slot + Rrep.phi root tok' memCore := by
  intro Rrep C C' d lim stLw uWords D3
  let loc := sg.loc
  have hsbEq : sb = loc.hb := hreg.1.symm
  have hLocEndLeMeta : loc.endAddr ≤ metaBase := le_of_eq (hreg.2.1.symm.trans hreg.2.2.1.symm)
  have hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base := hreg.2.2.2.1.symm
  have hMetaSz : metaBase + (2 + 8 * (B.d + 1)) = B.base := by
    unfold selectLevelMetaSize at hMetaEnd; exact hMetaEnd
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hLocHbLtEnd : loc.hb < loc.endAddr := by
    rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
  have hsbLeMeta : sb ≤ metaBase := by omega
  have hsbLeBase : sb ≤ B.base := by omega
  have hsbLtEnd : sb < B.endAddr := by omega
  have hOutLeSc : selOutBase + 1 + 12 * lim ≤ scratch := by
    have := hOutAt.2.1.2.1; dsimp only [lim, d]; omega
  have hEndSc : B.endAddr ≤ scratch := by omega
  have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hTags0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn0 := hTags0.1
  have hLvlMetaEnd : solverLevelMetaAddr tok'.table d + 2 * d + 1 < scratch := by
    have htg := hcaps.1.1.2.2.2
    have hlt := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    unfold solverSelectBlocksAddr solverSelectHeapAddr at hlt
    exact hlt
  have hLvlMetaDisj :
      solverLevelMetaAddr tok'.table d + 2 * B.d ≤ metaBase ∨
      metaBase + selectLevelMetaSize B.d ≤ solverLevelMetaAddr tok'.table d := by
    have hD := interval_disj_region (a := solverLevelMetaAddr tok'.table d) (len := 2 * d)
      (by omega) hsbLtEnd fun x hx1 hx2 ⟨h1, h2⟩ => by
      have htg := hcaps.1.2.2.2.2.1 (x - solverLevelMetaAddr tok'.table d) (by omega)
      have heq : solverLevelMetaAddr tok'.table d + (x - solverLevelMetaAddr tok'.table d) = x := by omega
      rw [heq] at htg
      exact hFootDisj x hx1 hx2 (Or.inl (hOwn0 x (by rw [htg]; omega)))
    rcases hD with hL | hR
    · left; omega
    · right; omega
  -- Phase 1: `selTableWriteBody`
  obtain ⟨bTW, hbTW, oTW, stTW, cTW, hrTW, hpTW, hcTW⟩ :=
    hTableWrite [metaBase, B.base, B.d, B.vCap, B.eCap, B.Lk, B.slot,
      solverLevelMetaAddr tok'.table d, pLast] memCore pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> try omega
          · have : B.vCap ≤ B.endAddr := by
              rw [B.endAddr_eq]; unfold selectBlocksSize dynGraphSize; omega
            omega
          · have : B.eCap ≤ B.endAddr := by
              rw [B.endAddr_eq]; unfold selectBlocksSize dynGraphSize; omega
            omega)
      ⟨rfl, hw16, by omega, by omega, by dsimp only [d] at hLvlMetaEnd ⊢; omega, hLvlMetaDisj⟩
  obtain ⟨_, hTab1Raw, hFrTW⟩ := hpTW
  have hTWOffMeta : ∀ a, (a < metaBase ∨ B.base ≤ a) → stTW.mem a = memCore a := fun a ha =>
    hFrTW a (by omega)
  have hTWFootAg : ∀ a, Rrep.foot root tok' a → stTW.mem a = memCore a := fun a ha =>
    hTWOffMeta a (by by_contra h; exact hFootDisj a (by omega) (by omega) ha)
  have hRep1 : Rrep.rep root modelPre tok' stTW.mem :=
    (hRrepLoc root modelPre tok' memCore stTW.mem fun a ha => (hTWFootAg a ha).symm).1 hrep
  have hPhi1 : Rrep.phi root tok' stTW.mem = Rrep.phi root tok' memCore :=
    ((hRrepLoc root modelPre tok' memCore stTW.mem fun a ha => (hTWFootAg a ha).symm).2).symm
  have hCaps1 : SolverLevelCapsInv P V vCap eCap modelPre tok' stTW.mem :=
    hcaps.preserve rfl (fun j hj => hcaps.1.2.1 j hj)
      (fun a ha => by
        have hne : tok'.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        exact ⟨rfl, hTWFootAg a (Or.inl (hOwn0 a hne))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hGPtrEqTW : ∀ j < d, solverLevelG tok' stTW.mem j = solverLevelG tok' memCore j := fun j hj => by
    have htg := hcaps.1.2.2.2.2.1 (d + j) (by omega)
    rw [← Nat.add_assoc] at htg
    exact hTWFootAg _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
  have hTab1 : SelectMetaTableAt stTW.mem (selectMlocOf B metaBase (solverLevelG tok' stTW.mem) pLast) := by
    have heq : selTableOf B metaBase (solverLevelMetaAddr tok'.table d) pLast memCore =
        selectMlocOf B metaBase (solverLevelG tok' stTW.mem) pLast := by
      unfold selTableOf selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]
        rw [hBd]; exact (hGPtrEqTW j (by omega)).symm
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]
        rw [hBd]; exact (hGPtrEqTW (j + 1) (by omega)).symm
    rwa [← heq]
  have hBlk1 : SelBlocksDataAt stTW.mem B P (SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ) pLast :=
    (selectBlocksAt_iff_data.mp hBlkOld).of_agree fun a ha1 _ => hTWOffMeta a (Or.inr ha1)
  have hZ1 : ZeroFrom stTW.mem scratch := fun a ha => (hTWOffMeta a (Or.inr (by omega))).trans (hz a ha)
  -- Phase 2: `selUpdateG0Body`
  have hG0At1 := SolverLevelMetaAt.atCaps hCaps1.1 hCaps1.2 0 hdPos
  have hG0Sc1 : solverLevelG tok' stTW.mem 0 + dynGraphSize vCap eCap ≤ scratch := by
    have hDGP : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have htg := hG0At1.2.2.2.2 (solverLevelG tok' stTW.mem 0 + dynGraphSize vCap eCap - 1)
      (by unfold solverLevelG; omega) (by unfold solverLevelG; omega)
    have hne : tok'.tag (solverLevelG tok' stTW.mem 0 + dynGraphSize vCap eCap - 1) ≠ 0 := by
      split_ifs at htg <;> omega
    have := hFootSc _ (Or.inl (hOwn0 _ hne)); omega
  have hG0OffB1 : solverLevelG tok' stTW.mem 0 + dynGraphSize vCap eCap ≤ B.g0Ptr ∨
      B.g0Ptr + B.eCap * L ≤ solverLevelG tok' stTW.mem 0 := by
    have hDGP : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have hD := interval_disj_region (a := solverLevelG tok' stTW.mem 0) (len := dynGraphSize vCap eCap)
      hDGP hsbLtEnd fun x hx1 hx2 hx => by
      have htg := hG0At1.2.2.2.2 x (by unfold solverLevelG at hx; exact hx.1)
        (by unfold solverLevelG at hx; exact hx.2)
      have hne : tok'.tag x ≠ 0 := by split_ifs at htg <;> omega
      exact hFootDisj x hx1 hx2 (Or.inl (hOwn0 x hne))
    have hBEndEq : B.g0Ptr + B.eCap * L = B.endAddr := by rw [← hBLk]; rfl
    have hBaseLeG0 : B.base ≤ B.g0Ptr := by
      have := B.blk_le_last (le_refl B.d)
      have : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
      unfold SelectBlocksLoc.g0Ptr; omega
    rcases hD with hL | hR <;> [left; right] <;> omega
  obtain ⟨sc1, cG0, st1, hrG0, hsc1Eq, hBlk2, hZ2, hFrG0, hcG0⟩ :=
    selUpdateG0_runs (D := SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ)
      (uG := (diffLists 0).uG) hw16 hLpos hBLk hBv hRep1 hFootSc
      (fun a h1 h2 => hFootDisj a (by
        have := B.blk_le_last (le_refl B.d)
        have : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
        unfold SelectBlocksLoc.g0Ptr at h1; omega) (by rw [← hBLk] at h2; exact h2))
      (hBe.symm ▸ hG0At1.1) (hBe.symm ▸ hG0Sc1) (hBe.symm ▸ hG0OffB1) hEndSc hBlk1 hgEqNew hgFitNew hBranchA
      (fun hFRNe => by
        have h0Lt : 0 < lim := by omega
        have hS0 := hOutAt.2.2 0 h0Lt
        have hNR0 := hLink.2.2.2.1 (by omega)
        have hAgOut : ∀ a, selOutBase ≤ a → a < scratch → stTW.mem a = memCore a :=
          fun a h1 _ => hTWOffMeta a (Or.inr (by omega))
        have hPtr0Eq : stTW.mem (selOutBase + 1) = memCore (selOutBase + 1) :=
          hAgOut _ (by omega) (by omega)
        have hLen0Eq : stTW.mem (selOutBase + 1 + 1) = (diffLists 0).uG.length := by
          rw [hAgOut _ (by omega) (by omega)]
          simpa using hS0.1.1
        have hUGW0 := hS0.2.2.2.2.2.2.1
        simp only [Nat.mul_zero, Nat.add_zero] at hUGW0
        have hUGAt1 : ListAt stTW.mem (stTW.mem (selOutBase + 1)) (diffLists 0).uG := fun t ht => by
          rw [hPtr0Eq, hAgOut _ (by have := hUGW0.1; omega)
            (by have := hUGW0.2.1; omega)]
          simpa using hS0.1.2.1 t ht
        have hUGCap0 : ∀ e ∈ (diffLists 0).uG, e < B.eCap := by
          rw [hBe, hS0.2.1]
          exact mem_coreBatchTouchedEdges_lt_eCap (hNR0.2.2.1 0 (Nat.zero_le _)).2
            (fun e he => hBe ▸ hBlkOld.2.1 0 (Nat.zero_le _) e he)
            hS0.2.2.2.2.2.2.2.2.2.2.2.1
        have hBEndEq : B.g0Ptr + B.eCap * L = B.endAddr := by rw [← hBLk]; rfl
        refine ⟨by omega, hLen0Eq, hUGAt1, by rw [hPtr0Eq]; exact hUGW0.2.1,
          Or.inr (by rw [hPtr0Eq, hBEndEq]; have := hUGW0.1; omega), hUGCap0,
          fun e heNew hNotU => ?_⟩
        have heOld : e ∈ (model.chain.G 0).E := by
          by_contra hNotOld
          have hmem : e ∈ batchTouchedEdges (levelU 0) :=
            mem_batchTouchedEdges_of_symmDiff (G := model.chain.G 0) (U := levelU 0)
              (by rw [← (hNR0.2.2.1 0 (Nat.zero_le _)).1]
                  exact ⟨fun _ => hNotOld, fun _ => heNew⟩)
          rw [← coreBatchTouchedEdges_eq_batchTouchedEdges, ← hS0.2.1] at hmem
          exact hNotU hmem
        exact ⟨heOld, hgSurv (by omega) e heNew heOld⟩)
      (hBe.symm ▸ hCopyOne) (hFilterPres (diffLists 0).uG) hZ1 (by omega)
  have hSt1OffB : ∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) → st1.mem a = stTW.mem a :=
    fun a ha hnb => hFrG0 a ha fun hg0 => hnb ⟨by
      have := B.blk_le_last (le_refl B.d)
      have : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
      unfold SelectBlocksLoc.regG0 SelectBlocksLoc.g0Ptr at hg0; omega,
      by unfold SelectBlocksLoc.regG0 at hg0; exact hg0.2⟩
  have hSt1FootAg : ∀ a, Rrep.foot root tok' a → st1.mem a = stTW.mem a := fun a ha =>
    hSt1OffB a (hFootSc a ha) fun hb => hFootDisj a (by omega) hb.2 ha
  have hRep2 : Rrep.rep root modelPre tok' st1.mem :=
    (hRrepLoc root modelPre tok' stTW.mem st1.mem fun a ha => (hSt1FootAg a ha).symm).1 hRep1
  have hPhi2 : Rrep.phi root tok' st1.mem = Rrep.phi root tok' stTW.mem :=
    ((hRrepLoc root modelPre tok' stTW.mem st1.mem fun a ha => (hSt1FootAg a ha).symm).2).symm
  have hCaps2 : SolverLevelCapsInv P V vCap eCap modelPre tok' st1.mem :=
    hCaps1.preserve rfl (fun j hj => hCaps1.1.2.1 j hj)
      (fun a ha => by
        have hne : tok'.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        exact ⟨rfl, hSt1FootAg a (Or.inl (hOwn0 a hne))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCaps1.1 hCaps1.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hTab2 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok' st1.mem) pLast) := by
    have hGEq : ∀ j < d, solverLevelG tok' st1.mem j = solverLevelG tok' stTW.mem j := fun j hj => by
      have htg := hCaps1.1.2.2.2.2.1 (d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact hSt1FootAg _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    have hM : selectMlocOf B metaBase (solverLevelG tok' st1.mem) pLast =
        selectMlocOf B metaBase (solverLevelG tok' stTW.mem) pLast := by
      unfold selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hGEq j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hGEq (j + 1) (by omega)
    rw [hM]
    exact hTab1.of_agree fun a _ h2 => hSt1OffB a (by dsimp only [selectMlocOf] at h2; omega)
      (by dsimp only [selectMlocOf] at h2; omega)
  have hSt1OutAg : ∀ a, selOutBase ≤ a → a < scratch → st1.mem a = memCore a := fun a h1 h2 =>
    (hSt1OffB a h2 (by omega)).trans (hTWOffMeta a (Or.inr (by omega)))
  -- Phase 3a-1: `selectUpdateFPhiLenLoopBody` over `0 .. lim - 1`
  obtain ⟨sc2, cFPL, st2, hrFPL, hsc2Lo, hsc2Hi, hBlk3, hZ3, hFrFPL, hcFPL⟩ :=
    selectUpdateFPhiLenLoop_runs (oldCh := model.chain) (levelU := levelU) (diffLists := diffLists)
      (uWords := uWords) (stLw := stLw)
      hw16 hLkW (Nat.zero_le lim) (Nat.min_le_right _ _) hreg hBd hBv hBe hBLk
      hRep2 (fun a ha => lt_of_lt_of_le (hFootSc a ha) (by omega)) hFootDisj hEndLeOut
      (by dsimp only [lim, d] at hOutLeSc ⊢; omega)
      hCaps2 hTab2 hBlk2 (fun h => absurd h (Nat.not_lt_zero _))
      (fun j _ hj hjPos => C'.G_E_subset_of_le hModNew.1 (by omega)
        (show j ≤ C'.d by dsimp only [C', ChainState.toTreeChain, lim, d] at hj ⊢; omega))
      (fun j _ hj => by
        have hS := hOutAt.2.2 j hj
        set sl := selOutBase + 1 + 12 * j
        have hslW : ∀ t < 12, st1.mem (sl + t) = memCore (sl + t) := fun t ht =>
          hSt1OutAg (sl + t) (by omega) (by omega)
        have hOutW : ∀ a n, SelOutWordsAt (Rrep.foot root tok') selOutBase scratch a n →
            (∀ t < n, st1.mem (a + t) = memCore (a + t)) ∧
            SelOutWordsAt (Rrep.foot root tok') selOutBase sc1 a n := fun a n hw =>
          ⟨fun t ht => hSt1OutAg (a + t) (by have := hw.1; omega) (by have := hw.2.1; omega),
           selOutWordsAt_bump_hi hw (by omega)⟩
        have hW0 := hOutW _ _ hS.2.2.2.2.2.2.1
        have hW2 := hOutW _ _ hS.2.2.2.2.2.2.2.1
        have hW4 := hOutW _ _ hS.2.2.2.2.2.2.2.2.1
        have hW6 := hOutW _ _ hS.2.2.2.2.2.2.2.2.2.1
        have hWU := hOutW _ _ hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hWSt := hOutW _ _ hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hDL1 : LevelDiffListsAt st1.mem sl (diffLists j) :=
          ⟨(hslW 1 (by omega)).trans hS.1.1,
           fun t ht => by rw [hslW 0 (by omega)]; exact (hW0.1 t ht).trans (hS.1.2.1 t ht),
           (hslW 3 (by omega)).trans hS.1.2.2.1,
           fun t ht => by rw [hslW 2 (by omega)]; exact (hW2.1 t ht).trans (hS.1.2.2.2.1 t ht),
           (hslW 5 (by omega)).trans hS.1.2.2.2.2.1,
           fun t ht => by rw [hslW 4 (by omega)]; exact (hW4.1 t ht).trans (hS.1.2.2.2.2.2.1 t ht),
           ⟨(hslW 7 (by omega)).trans hS.1.2.2.2.2.2.2.1,
            fun t ht => by rw [hslW 6 (by omega)]; exact (hW6.1 t ht).trans (hS.1.2.2.2.2.2.2.2 t ht)⟩⟩
        have hStDescEq : st1.mem (sl + 8) = memCore (sl + 8) := hslW 8 (by omega)
        have hUPtrEq : st1.mem (sl + 10) = memCore (sl + 10) := hslW 10 (by omega)
        have hT0 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hT1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hStVal1 : StretchValuesAt st1.mem (st1.mem (sl + 8)) 4 (stLw j) P
            (modelPre.chain.G j).E (C'.activeLSF j).wstr := by
          rw [hStDescEq]
          have hAct : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
            simp [C', TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d by omega]
          rw [hAct]
          have hSv := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hAgT : ∀ a, (Rrep.foot root tok' a ∨ (selOutBase ≤ a ∧ a < scratch)) →
              st1.mem a = memCore a := fun a ha =>
            ha.elim (fun hf => (hSt1FootAg a hf).trans (hTWFootAg a hf)) (fun ho => hSt1OutAg a ho.1 ho.2)
          have hb0 : st1.mem (memCore (sl + 8)) = memCore (memCore (sl + 8)) := hWSt.1 0 (by omega)
          have hb1 : st1.mem (memCore (sl + 8) + 1) = memCore (memCore (sl + 8) + 1) := hWSt.1 1 (by omega)
          intro e he
          obtain ⟨hv0, hv1, hne0, hdiv⟩ := hSv e he
          have hag0 : ∀ t < stLw j,
              st1.mem (st1.mem (memCore (sl + 8)) + e * stLw j + t) =
                memCore (memCore (memCore (sl + 8)) + e * stLw j + t) := fun t ht => by
            rw [hb0]; exact hAgT _ ((hT0.2 e he).2 t ht)
          have hag1 : ∀ t < stLw j,
              st1.mem (st1.mem (memCore (sl + 8) + 1) + e * stLw j + t) =
                memCore (memCore (memCore (sl + 8) + 1) + e * stLw j + t) := fun t ht => by
            rw [hb1]; exact hAgT _ ((hT1.2 e he).2 t ht)
          refine ⟨fun t ht => (hag0 t ht) ▸ hv0 t ht, fun t ht => (hag1 t ht) ▸ hv1 t ht,
            by unfold Num.fixVal at hne0 ⊢; rw [Num.intVal_congr hag1]; exact hne0,
            by unfold Num.fixVal at hdiv ⊢; rw [Num.intVal_congr hag0, Num.intVal_congr hag1]; exact hdiv⟩
        refine ⟨hDL1, hslW 9 (by omega), hStLwW j hj, hslW 11 (by omega),
          by rw [hslW 0 (by omega)]; exact hW0.2,
          by rw [hslW 2 (by omega)]; exact hW2.2,
          by rw [hslW 4 (by omega)]; exact hW4.2,
          by rw [hslW 6 (by omega)]; exact hW6.2,
          by rw [hUPtrEq]; exact hS.2.2.2.2.2.2.2.2.2.2.1.1.of_agree fun t ht => hWU.1 t ht,
          hS.2.2.2.2.2.2.2.2.2.2.2.1,
          fun t ht => by rw [hUPtrEq, hWU.1 t ht]; exact hS.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht,
          by rw [hUPtrEq]; exact hWU.2,
          by rw [hStDescEq]; exact hWSt.2,
          hStVal1,
          by rw [hStDescEq]; exact selOutTableAt_bump_hi (selOutTableAt_congr_mem hT0 (hWSt.1 0 (by omega))) (by omega),
          by rw [hStDescEq]; exact selOutTableAt_bump_hi (selOutTableAt_congr_mem hT1 (hWSt.1 1 (by omega))) (by omega)⟩)
      (fun j _ hj => by
        have hjD : j < cfg.P.d := by dsimp only [lim, d] at hj; omega
        have hS := hOutAt.2.2 j hj
        have hPM := hPrefModel j hj
        have hNR := hLink.2.2.2.1 (by dsimp only [lim, d] at hj; omega)
        have hGB := hNR.2.2.1 j (by dsimp only [lim, d] at hj; omega)
        have hOldSF := ((hModOld.1.2.2.2.2.1 j hjD).2.1 (model.chain.bran j)
          (hModOld.1.2.2.2.2.1 j hjD).1).1.2.1
        have hNewSF := ((hModNew.1.2.2.2.2.1 j hjD).2.1 (modelPre.chain.bran j)
          (hModNew.1.2.2.2.2.1 j hjD).1).1.2.1
        have hActOld : C.activeLSF j = cfg.T.lsfs (model.chain.scState j) (model.chain.bran j) := by
          simp [C, TreeChain.activeLSF, ChainState.toTreeChain, hjD]
        have hActNew : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
          simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hjD]
        have hDF : (SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ).F j =
            (C.activeLSF j).F.F := rfl
        refine ⟨rfl, hGB.1, hGB.2,
          by change (model.chain.G j).IsSubgraph ((C.activeLSF j).F.F); rw [hActOld]; exact hOldSF.2.2.2.2,
          by change (C.activeLSF j).F.F.V = (model.chain.G j).V; rw [hActOld]; exact hOldSF.2.1,
          by rw [hActNew]; exact hNewSF.2.2.2.2,
          by rw [hActNew]; exact hNewSF.2.1,
          hPM.2.1, hPM.1,
          by change (diffLists j).fDel.toFinset = (C.activeLSF j).F.F.E \ (C'.activeLSF j).F.F.E
             rw [hActOld, hActNew]; exact hS.2.2.2.1,
          ⟨by rw [hS.2.1]
              exact mem_coreBatchTouchedEdges_lt_eCap hGB.2
                (fun e he => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) e he) hS.2.2.2.2.2.2.2.2.2.2.2.1,
           mem_fDel_lt_eCap (hActOld.symm ▸ hActNew.symm ▸ hS.2.2.2.1)
             (hActOld.symm ▸ hOldSF.2.2.2.2.2.1) (fun e he => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) e he)⟩,
          hPM.2.2.2.2.1, hLenFitAll j hjD⟩)
      hpFPLLoop hpFPLLvl (fun j _ hj => hDgBatch j hj) (fun j _ hj => hDelList j hj)
      (fun j _ hj => hSplits j hj) (fun j _ hj => hFilterPres (diffLists j).uG)
      hpCoreLen hCoreLenEdge hZ2 (by dsimp only [lim, d, stLw] at hroom ⊢; omega)
  have hSt2FootAg : ∀ a, Rrep.foot root tok' a → st2.mem a = st1.mem a := fun a ha =>
    hFrFPL a (lt_of_lt_of_le (hFootSc a ha) (by omega)) fun hb => hFootDisj a (by omega) hb.2 ha
  have hRep3 : Rrep.rep root modelPre tok' st2.mem :=
    (hRrepLoc root modelPre tok' st1.mem st2.mem fun a ha => (hSt2FootAg a ha).symm).1 hRep2
  have hPhi3 : Rrep.phi root tok' st2.mem = Rrep.phi root tok' st1.mem :=
    ((hRrepLoc root modelPre tok' st1.mem st2.mem fun a ha => (hSt2FootAg a ha).symm).2).symm
  have hCaps3 : SolverLevelCapsInv P V vCap eCap modelPre tok' st2.mem :=
    hCaps2.preserve rfl (fun j hj => hCaps2.1.2.1 j hj)
      (fun a ha => by
        have hne : tok'.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        exact ⟨rfl, hSt2FootAg a (Or.inl (hOwn0 a hne))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCaps2.1 hCaps2.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hTab3 : SelectMetaTableAt st2.mem (selectMlocOf B metaBase (solverLevelG tok' st2.mem) pLast) := by
    have hGEq : ∀ j < d, solverLevelG tok' st2.mem j = solverLevelG tok' st1.mem j := fun j hj => by
      have htg := hCaps2.1.2.2.2.2.1 (d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact hSt2FootAg _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    have hM : selectMlocOf B metaBase (solverLevelG tok' st2.mem) pLast =
        selectMlocOf B metaBase (solverLevelG tok' st1.mem) pLast := by
      unfold selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hGEq j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hGEq (j + 1) (by omega)
    rw [hM]
    exact hTab2.of_agree fun a _ h2 => hFrFPL a (by dsimp only [selectMlocOf] at h2; omega)
      (by dsimp only [selectMlocOf] at h2; omega)
  have hSt2OffB : ∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) → st2.mem a = stTW.mem a :=
    fun a ha hnb => (hFrFPL a (by omega) hnb).trans (hSt1OffB a ha hnb)
  have hSt2OutAg : ∀ a, selOutBase ≤ a → a < scratch → st2.mem a = memCore a := fun a h1 h2 =>
    (hSt2OffB a h2 (by omega)).trans (hTWOffMeta a (Or.inr (by omega)))
  have hHeap2 : SelectHeapAt st2.mem loc 4 sg.size :=
    hHeapOld.of_agree fun a h1 h2 => by
      dsimp only [loc] at h1 h2 hLocEndLeMeta hLocHbLtEnd
      exact (hSt2OffB a (by omega) (by omega)).trans (hTWOffMeta a (Or.inl (by omega)))
  -- Phase 3a-2: `selectUpdateEmbLoopBody` over `0 .. lim - 1`
  obtain ⟨sc3, cEmb, st3, tok3, hrEmb, hsc3Lo, hsc3Hi, hRep4,
      htab3Eq, hhnd3Eq, hlev3Eq, hint3Eq, hrec3Eq, htree3Eq, htrees3Eq, hedg3Eq, hth3Eq, htt3Eq,
      hvc3Eq, hec3Eq, hft3, hown3, htag3Lt, htag3Ne, hCaps4, hTab4, hHeap3, hBlk4, hZ4, hFrEmb, hcEmb⟩ :=
    selectUpdateEmbLoop_runs (diffLists := diffLists)
      hfmtP hlocalCore hw16 hSlotW hkW (Nat.zero_le lim) (Nat.min_le_right _ _) hreg hBd hBv hBe hBLk
      hRep3 (fun a ha => lt_of_lt_of_le (hFootSc a ha) (by omega)) hFootDisj hEndLeOut
      (selOutWordsAt_bump_hi hOutAt.2.1 (by omega)) hCaps3 hTab3 hHeap2 hBlk3
      (fun j _ hj => by simp [hj])
      (fun j _ hj => (hPrefModel j hj).2.2.2.2.2.2.1)
      (fun j _ hj => (hPrefModel j hj).2.2.2.2.2.2.2)
      (fun j _ hj => by
        have hS := hOutAt.2.2 j hj
        set sl := selOutBase + 1 + 12 * j
        have hslW : ∀ t < 8, st2.mem (sl + t) = memCore (sl + t) := fun t ht =>
          hSt2OutAg (sl + t) (by omega) (by omega)
        have hOutW : ∀ a n, SelOutWordsAt (Rrep.foot root tok') selOutBase scratch a n →
            (∀ t < n, st2.mem (a + t) = memCore (a + t)) ∧
            SelOutWordsAt (Rrep.foot root tok') selOutBase sc2 a n := fun a n hw =>
          ⟨fun t ht => hSt2OutAg (a + t) (by have := hw.1; omega) (by have := hw.2.1; omega),
           selOutWordsAt_bump_hi hw (by omega)⟩
        have hW0 := hOutW _ _ hS.2.2.2.2.2.2.1
        have hW2 := hOutW _ _ hS.2.2.2.2.2.2.2.1
        have hW4 := hOutW _ _ hS.2.2.2.2.2.2.2.2.1
        have hW6 := hOutW _ _ hS.2.2.2.2.2.2.2.2.2.1
        have hDL2 : LevelDiffListsAt st2.mem sl (diffLists j) :=
          ⟨(hslW 1 (by omega)).trans hS.1.1,
           fun t ht => by rw [hslW 0 (by omega)]; exact (hW0.1 t ht).trans (hS.1.2.1 t ht),
           (hslW 3 (by omega)).trans hS.1.2.2.1,
           fun t ht => by rw [hslW 2 (by omega)]; exact (hW2.1 t ht).trans (hS.1.2.2.2.1 t ht),
           (hslW 5 (by omega)).trans hS.1.2.2.2.2.1,
           fun t ht => by rw [hslW 4 (by omega)]; exact (hW4.1 t ht).trans (hS.1.2.2.2.2.2.1 t ht),
           ⟨(hslW 7 (by omega)).trans hS.1.2.2.2.2.2.2.1,
            fun t ht => by rw [hslW 6 (by omega)]; exact (hW6.1 t ht).trans (hS.1.2.2.2.2.2.2.2 t ht)⟩⟩
        exact ⟨hDL2, by rw [hslW 0 (by omega)]; exact hW0.2, by rw [hslW 2 (by omega)]; exact hW2.2,
          by rw [hslW 4 (by omega)]; exact hW4.2, by rw [hslW 6 (by omega)]; exact hW6.2⟩)
      (fun j _ hj => by
        have hjD : j < cfg.P.d := by dsimp only [lim, d] at hj; omega
        have hS := hOutAt.2.2 j hj
        have hPM := hPrefModel j hj
        have hNR := hLink.2.2.2.1 (by dsimp only [lim, d] at hj; omega)
        have hOldSF := ((hModOld.1.2.2.2.2.1 j hjD).2.1 (model.chain.bran j)
          (hModOld.1.2.2.2.2.1 j hjD).1).1.2.1
        have hActOld : C.activeLSF j = cfg.T.lsfs (model.chain.scState j) (model.chain.bran j) := by
          simp [C, TreeChain.activeLSF, ChainState.toTreeChain, hjD]
        have hActNew : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
          simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hjD]
        exact ⟨⟨by rw [hS.2.1]
                   exact mem_coreBatchTouchedEdges_lt_eCap (hNR.2.2.1 j (by dsimp only [lim, d] at hj; omega)).2
                     (fun e he => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) e he) hS.2.2.2.2.2.2.2.2.2.2.2.1,
            mem_fDel_lt_eCap (hActOld.symm ▸ hActNew.symm ▸ hS.2.2.2.1)
              (hActOld.symm ▸ hOldSF.2.2.2.2.2.1) (fun e he => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) e he),
            hPM.2.2.1, hPM.2.2.2.1⟩,
          hEmbSlot j hjD, hPM.2.2.2.2.2.1⟩)
      hpEmbLoop hpEmbLvl (fun j _ hj => hFootAt j (by omega)) (fun j _ hj => hEmbUpd j hj) hZ3
      (by dsimp only [lim, d, stLw] at hroom hsc2Hi ⊢; omega)
  have hNonCore3 : ∀ a < scratch, ¬ (metaBase ≤ a ∧ a < B.endAddr) →
      (∀ j < d, tok'.tag a ≠ 21 + j) → st3.mem a = memCore a := fun a ha hnm hnc => by
    have hnb : ¬ (B.base ≤ a ∧ a < B.endAddr) := fun h => hnm ⟨by omega, h.2⟩
    have hncCore0 : ¬ (∃ j, 0 ≤ j ∧ j < lim ∧ Rcore.foot (tok'.coreHandle j) (tok'.coreTok j) a) :=
      fun ⟨j, _, hj, hf⟩ => hnc j (by omega) (hTags0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j (by omega) a hf)
    have hOffM : a < metaBase ∨ B.base ≤ a := by omega
    exact (hFrEmb a (by omega) hnb hncCore0).trans ((hSt2OffB a ha hnb).trans (hTWOffMeta a hOffM))
  simp only [selTableWriteContract, hBd] at hcTW
  refine ⟨bTW, oTW, stTW, st1, st2, st3, sc1, sc2, sc3, cTW, cG0, cFPL, cEmb, tok3,
    hbTW, by simpa only [hBd, hBv, hBe, hBLk] using hrTW,
    by rw [← hGPtrEqTW 0 hdPos]; exact hrG0, hrFPL, hrEmb,
    by omega, hsc2Lo, hsc3Lo, by omega,
    hRep4, htab3Eq, hhnd3Eq, hlev3Eq, hint3Eq, hrec3Eq, htree3Eq, htrees3Eq, hedg3Eq, hth3Eq, htt3Eq,
    hvc3Eq, hec3Eq,
    fun a ha => (hft3 a ha).elim Or.inl (fun hn => Or.inr ⟨by omega, hn.2⟩),
    hown3, fun a ha => htag3Lt a (by omega), htag3Ne, hCaps4, hTab4, hHeap3, hBlk4, hZ4,
    hNonCore3, hcTW, hcG0, hcFPL, by rw [hPhi3, hPhi2, hPhi1] at hcEmb; exact hcEmb⟩

end MinCostFlow.MinRatio
