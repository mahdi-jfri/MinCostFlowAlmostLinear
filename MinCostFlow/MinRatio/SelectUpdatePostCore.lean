module

public import MinCostFlow.MinRatio.SelectUpdatePostCoreP123a
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Post-core select-region and select-heap update (`SelectUpdatePostCore`)

Verifies `selectUpdatePostCoreBody` (`SelectUpdatePostCoreAux.lean`), composing Phases 1–3a
(`selectUpdatePostCore_prefix_runs`, `SelectUpdatePostCoreP123a.lean`) with Phase 3b
(`selectUpdateSuffixBlocks_runs`) and Phase 4 (`selectUpdateHeapPhase_runs`).

The theorem `selectUpdatePostCore_runs` is completely independent of tree/off-tree numeric budgets
(`B, R`) and preserves `tok.tree`, `tok.trees`, `tok.edgeRecords`, and every non-core cell below
`scratch` outside `[sb, B.endAddr)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Bundle Chain Chain.Ordered IPM.Machine Num DynSpanner.Program SparseCore SparseCore.Program

private lemma selectMetaDisjoint_of_solver_region_pc {B : SelectBlocksLoc}
    {loc : SelectHeapLoc} {sb metaBase pLast sc d vCap eCap L : ℕ} {gPtr : ℕ → ℕ}
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (_hBLk : B.Lk = L)
    (hEndSc : B.endAddr ≤ sc)
    (hGEnd : ∀ j < d, gPtr j + dynGraphSize vCap eCap ≤ sc ∧
      (gPtr j + dynGraphSize vCap eCap ≤ sb ∨ B.endAddr ≤ gPtr j)) :
    SelectMetaDisjoint (selectMlocOf B metaBase gPtr pLast) loc sc := by
  have hsb : sb = loc.hb := hreg.1.symm
  have hLocEnd : loc.endAddr ≤ metaBase := le_of_eq (hreg.2.1.symm.trans hreg.2.2.1.symm)
  have hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base := hreg.2.2.2.1.symm
  have hBaseEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hLastEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap = B.g0Ptr := rfl
  have hG0End : B.g0Ptr + B.eCap * B.Lk = B.endAddr := rfl
  have hBaseLast : B.base ≤ B.lastGPtr := by
    have := B.blk_le_last (Nat.zero_le _); unfold SelectBlocksLoc.fPtr at this; omega
  have hBlkBnd : ∀ j ≤ B.d,
      B.base ≤ B.fPtr j ∧
      B.fPtr j + dynGraphSize B.vCap B.eCap ≤ B.lastGPtr ∧
      B.phiPtr j + B.vCap * B.Lk ≤ B.lastGPtr ∧
      B.lenPtr j + B.eCap * B.Lk ≤ B.lastGPtr ∧
      B.embPtr j + B.eCap ≤ B.lastGPtr := fun j hj => by
    have hbl := B.blk_le_last hj
    have hbf : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
    unfold SelectBlocksLoc.levelSize at hbl
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
    have : 0 ≤ B.eCap * B.slot := Nat.zero_le _
    exact ⟨hbf, by omega, by omega, by omega, by omega⟩
  refine ⟨hreg.2.2.2.2.2.1.symm, by simp only [selectMlocOf]; omega,
    Or.inr (by simp only [selectMlocOf]; exact hLocEnd), fun j hj => ?_, ?_⟩
  · have hjb := hBlkBnd j hj
    dsimp only [selectMlocOf]
    refine ⟨?_, ?_, by omega, Or.inr (by omega), fun hjlt => ?_⟩
    · by_cases hlt : j < B.d
      · simp only [hlt, ↓reduceIte]; rw [hBv, hBe]; exact (hGEnd j (by omega)).1
      · simp only [hlt, ↓reduceIte]; omega
    · by_cases hlt : j < B.d
      · simp only [hlt, ↓reduceIte]; rw [hBv, hBe]
        rcases (hGEnd j (by omega)).2 with h1 | h2 <;> [left; right] <;> omega
      · simp only [hlt, ↓reduceIte]; right; omega
    · by_cases hlt1 : j + 1 < B.d
      · simp only [hlt1, ↓reduceIte]; rw [hBv, hBe]
        refine ⟨(hGEnd (j + 1) (by omega)).1, ?_⟩
        rcases (hGEnd (j + 1) (by omega)).2 with h1 | h2 <;> [left; right] <;> omega
      · have hjltB : j < B.d := hjlt
        simp only [hlt1, hjltB, ↓reduceIte]; exact ⟨by omega, Or.inr (by omega)⟩
  · refine ⟨by simp only [selectMlocOf]; omega, fun j hj => ?_⟩
    have hjb := hBlkBnd j hj
    simp only [selectMlocOf]
    exact ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 1600000 in
/-- End-to-end verification of `selectUpdatePostCoreBody`: updates the entire select region
(metadata table, level-0 gradients, non-rebuilt `F`/`φ`/`len`/`emb`, rebuilt suffix blocks and
potentials, and the select heap) for `modelPre`, restoring `SelectRegionAt`, `SolverSelectBlocksInv`,
`SolverSelectInv`, `Rrep.rep`, `SolverLevelCapsInv`, and exact non-core frame. -/
theorem selectUpdatePostCore_runs
    {w L P m V psi k epsExp drainUnit depth capExp vCap eCap pLast sb metaBase
      selOutBase scratch pos evalSpace evalCost : ℕ}
    {tableWriteProc g0Proc copyOne filterPres
      fPhiLenLoopProc fPhiLenLvlProc dgApplyBatch delEdgeList batchCopySplits coreLenFill coreLenEdge
      embLoopProc embLvlProc embUpdateFromList
      sufBlocksProc initIntLoop fillIntProc dgCopyProc filterAbs embCopyProc fillLast phiLoop phiFillProc
      heapPhaseProc heapPrefLoop updLvlProc rebSufProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G G₀ G₀' : MGraph}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {reembFn : ToolReembFn cfg.T} {pot : cfg.T.State → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root firstReb : ℕ} {model modelPre : Alg2State cfg}
    {tok' : SolverToken cfg L Rcore} {sg : SelectGhost} {B : SelectBlocksLoc}
    {solverGOld : ℕ → ℕ} {levelU levelUS : ℕ → List Update} {diffLists : ℕ → LevelDiffLists}
    {ins : ℕ → ℕ → Prop} {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop} {memCore : ℕ → ℕ}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLpos : 0 < L) (hLkW : L < 2 ^ w)
    (hpLastW : pLast < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) (hSlotW : B.slot < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (heCapPos : 0 < eCap) (heCapLeHeap : eCap ≤ sg.loc.cap)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' memCore)
    (hcaps : SolverLevelCapsInv P V vCap eCap modelPre tok' memCore)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hEndLeOut : B.endAddr ≤ selOutBase)
    (hreg : SelectRegion sb sg.loc B metaBase)
    (hcap : sg.loc.cap = selectHeapCap cfg G m)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hOwnEq : sg.owned = fun a => sb ≤ a ∧ a < B.endAddr)
    (hhbAt : memCore (solverSelectHeapAddr tok'.table cfg.P.d) = sb)
    (hBlkAt : memCore (solverSelectBlocksAddr tok'.table cfg.P.d) = B.base)
    (hTabOld : SelectMetaTableAt memCore (selectMlocOf B metaBase solverGOld pLast))
    (hBlkOld : SelectBlocksAt memCore B P model.chain.toTreeChain model.chain.g model.chain.ℓ
      sg.φ pLast)
    (hMatchOld : SelectHeapMatchesChain memCore sg.loc 4 P model.chain.toTreeChain
      model.chain.g model.chain.ℓ sg.size)
    (hPotOld : SelectPotInv model.chain.toTreeChain model.chain.g sg.φ)
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
    (hℓSurv : 0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
      modelPre.chain.ℓ e = model.chain.ℓ e)
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
      modelPre.chain.bran j < cfg.P.k ∧
      LevelDiffCovers C C' j ins (diffLists j))
    (hWstr : ∀ j, j < firstReb → j ≤ cfg.P.d →
      ∀ f ∈ (modelPre.chain.G j).E, f ∈ (model.chain.G j).E → ¬ ins j f →
        (modelPre.chain.toTreeChain.activeLSF j).wstr f =
          (model.chain.toTreeChain.activeLSF j).wstr f)
    (hInsFwd : ∀ j, j + 1 < firstReb → j < cfg.P.d →
      ∀ f ∈ (modelPre.chain.G (j + 1)).E, f ∈ (model.chain.G (j + 1)).E →
        ins j f → ins (j + 1) f)
    (hEP :
      let φS := fun j =>
        if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
      0 < firstReb → EndPotAgree model.chain.toTreeChain modelPre.chain.toTreeChain sg.φ φS (firstReb - 1))
    (hPotPref :
      let φS := fun j =>
        if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
      ∀ j < firstReb, j ≤ cfg.P.d →
        SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φS j)
    (hPhiBdPref :
      let φS := fun j =>
        if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
      ∀ j < firstReb, j ≤ cfg.P.d → PhiBd φS j)
    (hNoRebLast : firstReb = cfg.P.d + 1 →
      modelPre.chain.G cfg.P.d = model.chain.G cfg.P.d ∧
      modelPre.chain.toTreeChain.activeLSF cfg.P.d = model.chain.toTreeChain.activeLSF cfg.P.d ∧
      (∀ e ∈ (modelPre.chain.G cfg.P.d).E,
        modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e =
          model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e) ∧
      (∀ f ∈ (modelPre.chain.G cfg.P.d).E, ¬ ins cfg.P.d f))
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (modelPre.chain.G j).V, v < vCap)
    (hEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E, e < eCap)
    (hLenFitAll : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e)
    (hLenFitLast : firstReb ≤ cfg.P.d → ∀ e ∈ (modelPre.chain.G cfg.P.d).E,
      ∀ prevM : ℕ → ℕ,
        EdgeValuesAt prevM (B.lenPtr (cfg.P.d - 1)) 4 L P (modelPre.chain.G cfg.P.d).E
          (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ cfg.P.d) →
        Num.Fits 4 L (Num.intVal prevM (B.lenPtr (cfg.P.d - 1) + e * L) 4 L * (2 : ℤ) ^ pLast) ∧
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
            modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e)
    (hEmbSlot : ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
      (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ B.slot)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ k) →
      (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
          (modelPre.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ j)
            ((modelPre.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hPhiFit : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ' k) →
      (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P modelPre.chain.toTreeChain modelPre.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (modelPre.chain.toTreeChain.activeLSF j).F.F
        (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ' j))
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
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenFill (selCoreLenFillContract w P eCap eL))
    (hpEmbLoop : p.procs[embLoopProc]? = some (selectUpdateEmbLoopBody embLoopProc embLvlProc))
    (hpEmbLvl : p.procs[embLvlProc]? = some (selectUpdateEmbLevelBody (op 4) embUpdateFromList))
    (hEmbUpd : ∀ j < min firstReb cfg.P.d, ∀ L' : List ℕ,
      MeetsContract w p embUpdateFromList
        (selEmbUpdateFromListContract w vCap eCap (modelPre.chain.G j)
          (modelPre.chain.toTreeChain.activeLSF j).F.F L'
          (modelPre.chain.toTreeChain.activeEmb j)))
    (hpSufBlocks : p.procs[sufBlocksProc]? =
      some (selectUpdateSuffixBlocksBody initIntLoop (op 3) fillLast phiLoop))
    (hpInitInt : p.procs[initIntLoop]? = some (selectInitInteriorLoopBody initIntLoop fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenFill filterAbs embCopyProc))
    (hpFillLast : p.procs[fillLast]? = some (selectFillLastLevelBody dgCopyProc coreLenFill))
    (hpPhiLoop : p.procs[phiLoop]? = some (selectPhiLoopBody phiLoop phiFillProc))
    (hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ vcF ecF (Fold Fnew : MGraph),
      MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcF ecF Fold Fnew))
    (hFilterAbs : ∀ eL : List ℕ, MeetsContract w p filterAbs (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j, firstReb ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p embCopyProc
        (selEmbCopyContract w eL (modelPre.chain.toTreeChain.activeEmb j)))
    (hPhiFill : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p phiFillProc
        (selectPhiFillContract w 4 P (selectMlocOf B metaBase solverG pLast)
          modelPre.chain.toTreeChain G₀' modelPre.chain.g modelPre.chain.ℓ
          σ' σ'_mwu γ'_ℓ γ'_c φ))
    (hpHeapPhase : p.procs[heapPhaseProc]? = some (selectUpdateHeapPhaseBody heapPrefLoop rebSufProc))
    (hpHeapPref : p.procs[heapPrefLoop]? = some (selectUpdateHeapPrefixLoopBody heapPrefLoop updLvlProc))
    (hUpdLvl : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ), ∀ j < min firstReb cfg.P.d,
      MeetsContract w p updLvlProc
        (selectUpdateLevelNoRoomContract w 4 P sg.loc (selectMlocOf B metaBase solverG pLast)
          modelPre.chain.toTreeChain modelPre.chain.g modelPre.chain.ℓ φ
          (fun k => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (k + 1))
          (diffLists j) evalSpace evalCost))
    (hRebSuf : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p rebSufProc
        (selectRebuildSuffixNoRoomContract w 4 P sg.loc (selectMlocOf B metaBase solverG pLast)
          modelPre.chain.toTreeChain G₀' modelPre.chain.g modelPre.chain.ℓ
          σ' σ'_mwu γ'_ℓ γ'_c φ
          (fun k => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (k + 1))
          evalSpace evalCost))
    (hz : ZeroFrom memCore scratch)
    (hroom :
      let stLw := fun j => memCore (selOutBase + 1 + 12 * j + 9)
      scratch + selectUpdatePostCoreRawSpace memCore sg.loc modelPre.chain diffLists stLw
        firstReb L capExp evalSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let stLw := fun j => memCore (selOutBase + 1 + 12 * j + 9)
    let uWords := fun j => memCore (selOutBase + 1 + 12 * j + 11)
    ∃ scOut cost out tokFinal sg',
      Runs w p ω
        (selectUpdatePostCoreBody tableWriteProc g0Proc fPhiLenLoopProc embLoopProc
          sufBlocksProc heapPhaseProc)
        (startState [root, selOutBase, scratch] memCore pos) (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdatePostCoreRawSpace memCore sg.loc modelPre.chain diffLists stLw
        firstReb L capExp evalSpace ∧
      Rrep.rep root modelPre tokFinal out.mem ∧
      tokFinal.table = tok'.table ∧ tokFinal.handle = tok'.handle ∧
      tokFinal.levelsEnd = tok'.levelsEnd ∧ tokFinal.intCap = tok'.intCap ∧
      tokFinal.rootECap = tok'.rootECap ∧
      tokFinal.tree = tok'.tree ∧ tokFinal.trees = tok'.trees ∧
      tokFinal.edgeRecords = tok'.edgeRecords ∧
      tokFinal.termHandle = tok'.termHandle ∧ tokFinal.termTok = tok'.termTok ∧
      tokFinal.vcLast = tok'.vcLast ∧ tokFinal.ecLast = tok'.ecLast ∧
      (∀ a, Rrep.foot root tokFinal a → Rrep.foot root tok' a ∨ (scratch ≤ a ∧ a < scOut)) ∧
      (∀ a, tok'.owned a → tokFinal.owned a) ∧
      (∀ a < scratch, tokFinal.tag a = tok'.tag a) ∧
      (∀ a, tok'.tag a ≠ 0 → tokFinal.tag a = tok'.tag a) ∧
      SolverLevelCapsInv P V vCap eCap modelPre tokFinal out.mem ∧
      sg'.loc = sg.loc ∧ sg'.owned = sg.owned ∧
      sg'.reembPot = chainReembPot pot modelPre.chain ∧
      SelectRegionAt G P m vCap eCap pLast sb metaBase B modelPre tokFinal sg' out.mem ∧
      SolverSelectBlocksInv G L P m vCap eCap pLast B modelPre (Rrep.foot root tokFinal) tokFinal
        sg' out.mem ∧
      SolverSelectInv G L P m 4 2 tokFinal.table modelPre (Rrep.foot root tokFinal)
        (LevelMetaFoot tokFinal) sg' out.mem ∧
      (∀ j ≤ cfg.P.d, PhiBd sg'.φ j) ∧
      (∀ a, sg'.owned a → ¬ Rrep.foot root tokFinal a) ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ (sb ≤ a ∧ a < B.endAddr) →
        (∀ j < cfg.P.d, tok'.tag a ≠ 21 + j) → out.mem a = memCore a) ∧
      cost + Rrep.phi root tokFinal out.mem ≤
        selectUpdatePostCoreRawCost memCore sg.loc model.chain modelPre.chain levelU diffLists
          uWords stLw Psc.readout firstReb L capExp B.slot evalCost +
          Rrep.phi root tok' memCore := by
  intro Rrep stLw uWords
  let d := cfg.P.d
  let lim := min firstReb d
  let C := model.chain.toTreeChain
  let C' := modelPre.chain.toTreeChain
  let loc := sg.loc
  have hFR : firstReb ≤ d + 1 := hLink.1
  have hsbEq : sb = loc.hb := hreg.1.symm
  have hLocEndLeMeta : loc.endAddr ≤ metaBase := le_of_eq (hreg.2.1.symm.trans hreg.2.2.1.symm)
  have hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base := hreg.2.2.2.1.symm
  have hMetaSz : metaBase + (2 + 8 * (B.d + 1)) = B.base := by
    unfold selectLevelMetaSize at hMetaEnd; exact hMetaEnd
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hLocHbLtEnd : loc.hb < loc.endAddr := by
    rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
  have hsbLtEnd : sb < B.endAddr := by omega
  have hOutLeSc : selOutBase + 1 + 12 * lim ≤ scratch := by
    have := hOutAt.2.1.2.1; dsimp only [lim, d]; omega
  have hEndSc : B.endAddr ≤ scratch := by omega
  have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hTags0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn0 := hTags0.1
  -- Phases 1, 2, 3a-1, 3a-2
  obtain ⟨bTW, oTW, stTW, st1, st2, st3, sc1, sc2, sc3, cTW, cG0, cFPL, cEmb, tok3,
      hbTW, hrTW, hrG0, hrFPL, hrEmb, hsc1Lo, hsc2Lo, hsc3Lo, hsc3Hi, hRep4,
      htab3Eq, hhnd3Eq, hlev3Eq, hint3Eq, hrec3Eq, htree3Eq, htrees3Eq, hedg3Eq, hth3Eq, htt3Eq,
      hvc3Eq, hec3Eq, hft3, hown3, htag3Lt, htag3Ne, hCaps4, hTab4, hHeap3, hBlk4, hZ4,
      hNonCore3, hcTW, hcG0, hcFPL, hcEmb⟩ :=
    selectUpdatePostCore_prefix_runs hfmtP hlocalCore hw16 hLpos hLkW hpLastW hkW hSlotW hdPos
      hrep hcaps hFootSc hFootDisj hEndLeOut hreg hBd hBv hBe hBLk hBlkOld hMatchOld.1
      hModOld hModNew hLink hOutAt hStLwW hgEqNew hgFitNew hBranchA hgSurv
      (fun j hj => by
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, _⟩ := hPrefModel j hj
        exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩)
      hLenFitAll hEmbSlot hTableWrite hpG0 hCopyOne hFilterPres hpFPLLoop hpFPLLvl
      hDgBatch hDelList hSplits hpCoreLen hCoreLenEdge hpEmbLoop hpEmbLvl hFootAt hEmbUpd hz
      (by dsimp only [selectUpdatePostCoreRawSpace, stLw] at hroom ⊢; omega)
  have hFoot3Sc : ∀ a, Rrep.foot root tok3 a → a < sc3 := fun a ha =>
    (hft3 a ha).elim (fun h0 => lt_of_lt_of_le (hFootSc a h0) (by omega)) (fun hn => hn.2)
  have hFoot3Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok3 a := fun a h1 h2 ha =>
    (hft3 a ha).elim (hFootDisj a h1 h2) (fun hn => by omega)
  have hFVNew : ∀ j ≤ d, ∀ v ∈ (C'.activeLSF j).F.F.V, v < vCap := fun j hj v hv => by
    apply hVcap j hj
    by_cases hlt : j < cfg.P.d
    · have hVeq := ((hModNew.1.2.2.2.2.1 j hlt).2.1 (modelPre.chain.bran j)
        (hModNew.1.2.2.2.2.1 j hlt).1).1.2.1.2.1
      have hAct : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
        simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hlt]
      rw [hAct] at hv; exact hVeq ▸ hv
    · have hjd : j = cfg.P.d := by dsimp only [d] at hj; omega
      subst hjd
      have hVeq := (hModNew.1.2.2.2.2.2.2.1 modelPre.chain.lastBran hModNew.1.2.2.2.2.2.1).2.1.2.1
      have hAct : C'.activeLSF cfg.P.d = modelPre.chain.lastLSFs modelPre.chain.lastBran := by
        simp [C', TreeChain.activeLSF, ChainState.toTreeChain]
      rw [hAct] at hv; exact hVeq ▸ hv
  have hFENew : ∀ j ≤ d, ∀ e ∈ (C'.activeLSF j).F.F.E, e < eCap := fun j hj e he => by
    apply hEcap j hj
    by_cases hlt : j < cfg.P.d
    · have hSub := ((hModNew.1.2.2.2.2.1 j hlt).2.1 (modelPre.chain.bran j)
        (hModNew.1.2.2.2.2.1 j hlt).1).1.2.1.2.2.2.2.2.1
      have hAct : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
        simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hlt]
      rw [hAct] at he; exact hSub he
    · have hjd : j = cfg.P.d := by dsimp only [d] at hj; omega
      subst hjd
      have hSub := (hModNew.1.2.2.2.2.2.2.1 modelPre.chain.lastBran hModNew.1.2.2.2.2.2.1).2.1.2.2.2.2.2.1
      have hAct : C'.activeLSF cfg.P.d = modelPre.chain.lastLSFs modelPre.chain.lastBran := by
        simp [C', TreeChain.activeLSF, ChainState.toTreeChain]
      rw [hAct] at he; exact hSub he
  -- Phase 3b: `selectUpdateSuffixBlocksBody`
  obtain ⟨sc4, cSuf, st4, tok4, φ', hrSuf, hsc4Lo, hsc4Hi, hRep5,
      htab4Eq, hhnd4Eq, hlev4Eq, hint4Eq, hrec4Eq, htree4Eq, htrees4Eq, hedg4Eq, hth4Eq, htt4Eq,
      hvc4Eq, hec4Eq, hft4, hown4, htag4Lt, htag4Ne, hCaps5, hTab5, hHeap4, hBlocks5,
      hφKeep, hPot5, hPhiBd5, hZ5, hFrSuf, hcSuf⟩ :=
    selectUpdateSuffixBlocks_runs (PhiBd := PhiBd)
      hfmt4 hfmtP hlocalCore hw16 hw10 hLkW hSlotW hkW hpLastW hdPos hFR
      hreg hBd hBv hBe hBLk hRep4 hFoot3Sc hFoot3Disj (by omega) hCaps4 hModNew hTab4 hHeap3 hBlk4
      ⟨rfl, rfl⟩
      (fun j hj => by
        have hj' : 0 ≤ j ∧ j < min firstReb cfg.P.d := ⟨Nat.zero_le _, hj⟩
        simp [hj', ChainState.toTreeChain])
      (fun hFREq => by
        obtain ⟨hG, hF, hL, _⟩ := hNoRebLast hFREq
        have hnot : ¬ (0 ≤ cfg.P.d ∧ cfg.P.d < min firstReb cfg.P.d) := by omega
        simp only [hnot, ↓reduceIte, SelBlocksData.ofChain, hBd]
        exact ⟨hG.symm, by rw [hF], by change (model.chain.G cfg.P.d).V = _; rw [hG],
          by change (model.chain.G cfg.P.d).E = _; rw [hG], fun e he => (hL e he).symm⟩)
      (fun j hj1 hj2 => by
        have h := hPotPref j hj1 hj2
        have hEqφ : (fun k => if 0 ≤ k ∧ k < min firstReb cfg.P.d then splitPot (sg.φ k) (batchSplits (levelU k)) else sg.φ k) =
            (fun k => if k < min firstReb cfg.P.d then splitPot (sg.φ k) (batchSplits (levelU k)) else sg.φ k) := by
          funext k; simp
        rwa [hEqφ])
      (fun j hj1 hj2 => by
        have h := hPhiBdPref j hj1 hj2
        have hEqφ : (fun k => if 0 ≤ k ∧ k < min firstReb cfg.P.d then splitPot (sg.φ k) (batchSplits (levelU k)) else sg.φ k) =
            (fun k => if k < min firstReb cfg.P.d then splitPot (sg.φ k) (batchSplits (levelU k)) else sg.φ k) := by
          funext k; simp
        rwa [hEqφ])
      hPhiBdStep hVcap hEcap hFVNew hFENew
      (fun j _ hj => hLenFitAll j hj) hLenFitLast (fun j _ hj => hEmbSlot j hj) hPhiFit
      hpInitInt hpFillInt hpFillLast hpPhiLoop hFootAt
      (fun _ _ _ vcF ecF => hDgCopy vcF ecF _ _) (hDgCopy vCap eCap _ _)
      (hDgCopy tok3.vcLast tok3.ecLast _ _) hCoreLen hFilterAbs hEmbCopy
      (hPhiFill (solverLevelG tok3 st3.mem)) hZ4
      (by unfold selectUpdatePostCoreRawSpace at hroom; dsimp only [stLw, lim, d] at hroom hsc3Hi ⊢; omega)
  have hNonCore4 : ∀ a < scratch, ¬ (sb ≤ a ∧ a < B.endAddr) →
      (∀ j < d, tok'.tag a ≠ 21 + j) → st4.mem a = memCore a := fun a ha hnsb hnc => by
    have hnb : ¬ (B.base ≤ a ∧ a < B.endAddr) := fun h => hnsb ⟨by omega, h.2⟩
    have hnm : ¬ (metaBase ≤ a ∧ a < B.endAddr) := fun h => hnsb ⟨by omega, h.2⟩
    have hnc3 : ∀ j < d, tok3.tag a ≠ 21 + j := fun j hj => by
      rw [htag3Lt a ha]; exact hnc j hj
    exact (hFrSuf a (by omega) hnb hnc3).trans (hNonCore3 a ha hnm hnc)
  have hHeapAg4 : ∀ a, loc.hb ≤ a → a < loc.endAddr → st4.mem a = memCore a := fun a h1 h2 => by
    have hnb : ¬ (B.base ≤ a ∧ a < B.endAddr) := by omega
    have hnf0 : ¬ Rrep.foot root tok' a := hFootDisj a (by omega) (by omega)
    have htag0 : tok'.tag a = 0 := by by_contra hne; exact hnf0 (Or.inl (hOwn0 a hne))
    have hnc3 : ∀ j < d, tok3.tag a ≠ 21 + j := fun j _ => by
      rw [htag3Lt a (by omega), htag0]; omega
    exact (hFrSuf a (by omega) hnb hnc3).trans
      (hNonCore3 a (by omega) (by omega) (fun j _ => by rw [htag0]; omega))
  have hMatchOld4 : SelectHeapMatchesChain st4.mem loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hMatchOld.of_agree hHeapAg4
  have hFoot4Sc : ∀ a, Rrep.foot root tok4 a → a < sc4 := fun a ha =>
    (hft4 a ha).elim (fun h3 => lt_of_lt_of_le (hFoot3Sc a h3) hsc4Lo) (fun hn => hn.2)
  have hFoot4Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok4 a := fun a h1 h2 ha =>
    (hft4 a ha).elim (hFoot3Disj a h1 h2) (fun hn => by omega)
  have hGEnd4 : ∀ j < d,
      solverLevelG tok4 st4.mem j + dynGraphSize vCap eCap ≤ sc4 ∧
      (solverLevelG tok4 st4.mem j + dynGraphSize vCap eCap ≤ sb ∨
        B.endAddr ≤ solverLevelG tok4 st4.mem j) := by
    intro j hj
    have hAt := SolverLevelMetaAt.atCaps hCaps5.1 hCaps5.2 j hj
    have hOwn4 := hRep5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hDGP : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have hSc : solverLevelG tok4 st4.mem j + dynGraphSize vCap eCap ≤ sc4 := by
      have htg := hAt.2.2.2.2 (solverLevelG tok4 st4.mem j + dynGraphSize vCap eCap - 1)
        (by unfold solverLevelG; omega) (by unfold solverLevelG; omega)
      have hne : tok4.tag (solverLevelG tok4 st4.mem j + dynGraphSize vCap eCap - 1) ≠ 0 := by
        split_ifs at htg <;> omega
      have := hFoot4Sc _ (Or.inl (hOwn4 _ hne)); omega
    have hD := interval_disj_region (a := solverLevelG tok4 st4.mem j) (len := dynGraphSize vCap eCap)
      hDGP hsbLtEnd fun x hx1 hx2 hx => by
      have htg := hAt.2.2.2.2 x (by unfold solverLevelG at hx; exact hx.1)
        (by unfold solverLevelG at hx; exact hx.2)
      have hne : tok4.tag x ≠ 0 := by split_ifs at htg <;> omega
      exact hFoot4Disj x hx1 hx2 (Or.inl (hOwn4 x hne))
    exact ⟨hSc, hD⟩
  set mloc4 := selectMlocOf B metaBase (solverLevelG tok4 st4.mem) pLast
  have hMeta4 : SelectLevelMetaAt st4.mem mloc4 4 P C' modelPre.chain.g modelPre.chain.ℓ φ'
      (fun j => C'.chainLen modelPre.chain.ℓ (j + 1)) :=
    selectLevelMetaAt_of_solver hBd hBv hBe hTab5 hBlocks5 hCaps5 hModNew hPot5
  have hDisj4 : SelectMetaDisjoint mloc4 loc sc4 :=
    selectMetaDisjoint_of_solver_region_pc hreg hBd hBv hBe hBLk (by omega) hGEnd4
  have hMetaFr4 : ∀ m', (∀ a < sc4, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = st4.mem a) →
      SelectLevelMetaAt m' mloc4 4 P C' modelPre.chain.g modelPre.chain.ℓ φ'
        (fun j => C'.chainLen modelPre.chain.ℓ (j + 1)) := by
    intro m' hm'
    have hFoot4Ag : ∀ a, Rrep.foot root tok4 a → m' a = st4.mem a := fun a ha =>
      hm' a (hFoot4Sc a ha) (by by_contra h; exact hFoot4Disj a (by omega) (by omega) ha)
    have hOwn4 := hRep5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hCaps' : SolverLevelCapsInv P V vCap eCap modelPre tok4 m' :=
      hCaps5.preserve rfl (fun j hj => hCaps5.1.2.1 j hj)
        (fun a ha => by
          have hne : tok4.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
          exact ⟨rfl, hFoot4Ag a (Or.inl (hOwn4 a hne))⟩)
        (fun j hj => (SolverLevelMetaAt.atCaps hCaps5.1 hCaps5.2 j hj).2.2.1)
        rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have hGEq : ∀ j < d, solverLevelG tok4 m' j = solverLevelG tok4 st4.mem j := fun j hj => by
      have htg := hCaps5.1.2.2.2.2.1 (d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact hFoot4Ag _ (Or.inl (hOwn4 _ (by rw [htg]; omega)))
    have hMlocEq : selectMlocOf B metaBase (solverLevelG tok4 m') pLast = mloc4 := by
      unfold mloc4 selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hGEq j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hGEq (j + 1) (by omega)
    have hTab' : SelectMetaTableAt m' mloc4 :=
      hTab5.of_agree fun a h1 h2 => hm' a (by dsimp only [mloc4, selectMlocOf] at h2; omega)
        (Or.inr (by dsimp only [mloc4, selectMlocOf] at h1; omega))
    have hBlk' : SelectBlocksAt m' B P C' modelPre.chain.g modelPre.chain.ℓ φ' pLast :=
      selectBlocksAt_iff_data.mpr ((selectBlocksAt_iff_data.mp hBlocks5).of_agree fun a h1 h2 =>
        hm' a (by omega) (Or.inr (by omega)))
    rw [← hMlocEq] at hTab' ⊢
    exact selectLevelMetaAt_of_solver hBd hBv hBe hTab' hBlk' hCaps' hModNew hPot5
  have hHeapCong := selectUpdateHeapPhase_congr_mem (C' := modelPre.chain) (diffLists := diffLists)
    (firstReb := firstReb) (evalSpace := evalSpace) (evalCost := evalCost) hHeapAg4
  have hSt4OutAg : ∀ a, selOutBase ≤ a → a < scratch → ¬ Rrep.foot root tok' a →
      st4.mem a = memCore a := fun a h1 h2 hnf => by
    have htag0 : tok'.tag a = 0 := by by_contra hne; exact hnf (Or.inl (hOwn0 a hne))
    exact hNonCore4 a h2 (by omega) (fun j _ => by rw [htag0]; omega)
  -- Phase 4: `selectUpdateHeapPhaseBody`
  obtain ⟨sc5, cHeap, st5, sizeOut, hrHeap, hsc5Lo, hsc5Hi, hMatch5, _, hZ6, hFrHeap, hcHeap⟩ :=
    selectUpdateHeapPhase_runs (C := C) (C' := C') (ins := ins) (diffLists := diffLists)
      (selOutBase := selOutBase)
      hw16 (by simpa only [mloc4, selectMlocOf] using hpLastW) hFR rfl
      (hreg.2.2.2.2.1.trans hBd) hreg.2.2.2.2.2.1.symm
      (by dsimp only [loc, d, lim, C', ChainState.toTreeChain] at *; omega)
      (by dsimp only [loc, d, lim, C', ChainState.toTreeChain] at *; omega)
      hModOld.1 hModOld.2.1 hModNew.1 hModNew.2.1 hPotOld hPot5
      (fun hpos j hj => by
        have h1 := hEP hpos j hj
        have hφEq : φ' j = (if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j) := by
          have hk := hφKeep j (by omega)
          simpa only [show 0 ≤ j ∧ j < min firstReb cfg.P.d ↔ j < min firstReb cfg.P.d by omega] using hk
        rwa [hφEq])
      hWstr hInsFwd hℓSurv hgSurv
      (fun j hj => (hPrefModel j hj).2.2.2.2.2.2.2.2)
      (fun hFREq => by
        obtain ⟨hG, hF, _, hNI⟩ := hNoRebLast hFREq
        exact ⟨hG, hF, hNI⟩)
      (fun j hj => by
        have hjLim : j < lim := hj
        have hjD : j < cfg.P.d := by dsimp only [lim, d] at hjLim; omega
        have hS := hOutAt.2.2 j hj
        have hPM := hPrefModel j hj
        have hNR := hLink.2.2.2.1 (by dsimp only [lim, d] at hjLim; omega)
        set sl := selOutBase + 1 + 12 * j
        have hslW : ∀ t < 8, st4.mem (sl + t) = memCore (sl + t) := fun t ht =>
          hSt4OutAg (sl + t) (by omega) (by dsimp only [lim, d] at hjLim hOutLeSc; omega)
            (by rw [show sl + t = selOutBase + (1 + 12 * j + t) by omega]
                exact hOutAt.2.1.2.2 (1 + 12 * j + t) (by dsimp only [lim, d] at hjLim; omega))
        have hOutW : ∀ a n, SelOutWordsAt (Rrep.foot root tok') selOutBase scratch a n →
            (∀ t < n, st4.mem (a + t) = memCore (a + t)) := fun a n hw t ht =>
          hSt4OutAg (a + t) (by have := hw.1; omega) (by have := hw.2.1; omega) (hw.2.2 t ht)
        have hW0 := hOutW _ _ hS.2.2.2.2.2.2.1
        have hW2 := hOutW _ _ hS.2.2.2.2.2.2.2.1
        have hW4 := hOutW _ _ hS.2.2.2.2.2.2.2.2.1
        have hW6 := hOutW _ _ hS.2.2.2.2.2.2.2.2.2.1
        have hDL4 : LevelDiffListsAt st4.mem sl (diffLists j) :=
          ⟨(hslW 1 (by omega)).trans hS.1.1,
           fun t ht => by rw [hslW 0 (by omega)]; exact (hW0 t ht).trans (hS.1.2.1 t ht),
           (hslW 3 (by omega)).trans hS.1.2.2.1,
           fun t ht => by rw [hslW 2 (by omega)]; exact (hW2 t ht).trans (hS.1.2.2.2.1 t ht),
           (hslW 5 (by omega)).trans hS.1.2.2.2.2.1,
           fun t ht => by rw [hslW 4 (by omega)]; exact (hW4 t ht).trans (hS.1.2.2.2.2.2.1 t ht),
           ⟨(hslW 7 (by omega)).trans hS.1.2.2.2.2.2.2.1,
            fun t ht => by rw [hslW 6 (by omega)]; exact (hW6 t ht).trans (hS.1.2.2.2.2.2.2.2 t ht)⟩⟩
        have hDisjDL : LevelDiffListsDisjoint st4.mem sl (diffLists j) loc sc4 :=
          ⟨by dsimp only [lim, d] at hjLim hOutLeSc; omega, Or.inr (by dsimp only [loc] at *; omega),
           by rw [hslW 0 (by omega)]; have := hS.2.2.2.2.2.2.1.2.1; omega,
           Or.inr (by rw [hslW 0 (by omega)]; have := hS.2.2.2.2.2.2.1.1; dsimp only [loc] at *; omega),
           by rw [hslW 2 (by omega)]; have := hS.2.2.2.2.2.2.2.1.2.1; omega,
           Or.inr (by rw [hslW 2 (by omega)]; have := hS.2.2.2.2.2.2.2.1.1; dsimp only [loc] at *; omega),
           by rw [hslW 4 (by omega)]; have := hS.2.2.2.2.2.2.2.2.1.2.1; omega,
           Or.inr (by rw [hslW 4 (by omega)]; have := hS.2.2.2.2.2.2.2.2.1.1; dsimp only [loc] at *; omega),
           by rw [hslW 6 (by omega)]; have := hS.2.2.2.2.2.2.2.2.2.1.2.1; omega,
           Or.inr (by rw [hslW 6 (by omega)]; have := hS.2.2.2.2.2.2.2.2.2.1.1; dsimp only [loc] at *; omega)⟩
        have hAllCap : ∀ e ∈ (diffLists j).allTouched, e < loc.cap ∧ e < mloc4.eCap j := by
          intro e he
          have heECap : e < eCap := by
            unfold LevelDiffLists.allTouched at he
            simp only [List.mem_append] at he
            rcases he with ((h1 | h2) | h3) | h4
            · rw [hS.2.1] at h1
              exact mem_coreBatchTouchedEdges_lt_eCap (hNR.2.2.1 j (by dsimp only [lim, d] at hjLim; omega)).2
                (fun x hx => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) x hx) hS.2.2.2.2.2.2.2.2.2.2.2.1 e h1
            · have hOldSubF := ((hModOld.1.2.2.2.2.1 j hjD).2.1 (model.chain.bran j)
                (hModOld.1.2.2.2.2.1 j hjD).1).1.2.1
              have hActOld : C.activeLSF j = cfg.T.lsfs (model.chain.scState j) (model.chain.bran j) := by
                simp [C, TreeChain.activeLSF, ChainState.toTreeChain, hjD]
              have hActNew : C'.activeLSF j = cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
                simp [C', TreeChain.activeLSF, ChainState.toTreeChain, hjD]
              exact mem_fDel_lt_eCap (hActOld.symm ▸ hActNew.symm ▸ hS.2.2.2.1)
                (hActOld.symm ▸ hOldSubF.2.2.2.2.2.1) (fun x hx => hBe ▸ hBlkOld.2.1 j (by rw [hBd]; omega) x hx) e h2
            · exact hPM.2.2.1 e h3
            · exact hPM.2.2.2.1 e h4
          exact ⟨lt_of_lt_of_le heECap heCapLeHeap, by simp only [mloc4, selectMlocOf, hBe]; exact heECap⟩
        exact ⟨hDL4, hDisjDL, hAllCap⟩)
      (fun j _ hj e he => lt_of_lt_of_le (hEcap j hj e he) heCapLeHeap)
      hMatchOld4 hMeta4 hDisj4 hMetaFr4 hpHeapPref
      (fun j hj => hUpdLvl (solverLevelG tok4 st4.mem) φ' j hj)
      (hRebSuf (solverLevelG tok4 st4.mem) φ') hZ5
      (by rw [hHeapCong.1]; dsimp only [selectUpdatePostCoreRawSpace, stLw, lim, d, loc] at hroom hsc3Hi hsc4Hi ⊢; omega)
  -- Final post-state transfer across Phase 4
  have hFoot4Ag5 : ∀ a, Rrep.foot root tok4 a → st5.mem a = st4.mem a := fun a ha =>
    hFrHeap a (hFoot4Sc a ha) (by by_contra h; dsimp only [loc] at *; exact hFoot4Disj a (by omega) (by omega) ha)
  have hRep6 : Rrep.rep root modelPre tok4 st5.mem :=
    (hRrepLoc root modelPre tok4 st4.mem st5.mem fun a ha => (hFoot4Ag5 a ha).symm).1 hRep5
  have hPhi6 : Rrep.phi root tok4 st5.mem = Rrep.phi root tok4 st4.mem :=
    ((hRrepLoc root modelPre tok4 st4.mem st5.mem fun a ha => (hFoot4Ag5 a ha).symm).2).symm
  have hOwn4 := hRep5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCaps6 : SolverLevelCapsInv P V vCap eCap modelPre tok4 st5.mem :=
    hCaps5.preserve rfl (fun j hj => hCaps5.1.2.1 j hj)
      (fun a ha => by
        have hne : tok4.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        exact ⟨rfl, hFoot4Ag5 a (Or.inl (hOwn4 a hne))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCaps5.1 hCaps5.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hTab6 : SelectMetaTableAt st5.mem (selectMlocOf B metaBase (solverLevelG tok4 st5.mem) pLast) := by
    have hGEq : ∀ j < d, solverLevelG tok4 st5.mem j = solverLevelG tok4 st4.mem j := fun j hj => by
      have htg := hCaps5.1.2.2.2.2.1 (d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact hFoot4Ag5 _ (Or.inl (hOwn4 _ (by rw [htg]; omega)))
    have hM : selectMlocOf B metaBase (solverLevelG tok4 st5.mem) pLast = mloc4 := by
      unfold mloc4 selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hGEq j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hGEq (j + 1) (by omega)
    rw [hM]
    exact hTab5.of_agree fun a h1 h2 => hFrHeap a (by dsimp only [mloc4, selectMlocOf] at h2; omega)
      (Or.inr (by dsimp only [mloc4, selectMlocOf, loc] at h1 hLocEndLeMeta ⊢; omega))
  have hBlocks6 : SelectBlocksAt st5.mem B P C' modelPre.chain.g modelPre.chain.ℓ φ' pLast :=
    selectBlocksAt_iff_data.mpr ((selectBlocksAt_iff_data.mp hBlocks5).of_agree fun a h1 h2 =>
      hFrHeap a (by omega) (Or.inr (by dsimp only [loc] at hLocEndLeMeta ⊢; omega)))
  have hNonCore5 : ∀ a < scratch, ¬ (sb ≤ a ∧ a < B.endAddr) →
      (∀ j < d, tok'.tag a ≠ 21 + j) → st5.mem a = memCore a := fun a ha hnsb hnc =>
    (hFrHeap a (by omega) (by dsimp only [loc] at hsbEq hLocEndLeMeta ⊢; omega)).trans (hNonCore4 a ha hnsb hnc)
  have hhbAt5 : st5.mem (solverSelectHeapAddr tok4.table d) = sb := by
    rw [htab4Eq, htab3Eq]
    have htg := hcaps.1.1.2.2.1
    have hlt := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    have hOff : ¬ (sb ≤ solverSelectHeapAddr tok'.table d ∧ solverSelectHeapAddr tok'.table d < B.endAddr) :=
      fun h => hFootDisj _ h.1 h.2 (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    exact (hNonCore5 _ hlt hOff (fun j hj => by rw [htg]; dsimp only [d] at hj ⊢; omega)).trans hhbAt
  have hBlkAt5 : st5.mem (solverSelectBlocksAddr tok4.table d) = B.base := by
    rw [htab4Eq, htab3Eq]
    have htg := hcaps.1.1.2.2.2
    have hlt := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    have hOff : ¬ (sb ≤ solverSelectBlocksAddr tok'.table d ∧ solverSelectBlocksAddr tok'.table d < B.endAddr) :=
      fun h => hFootDisj _ h.1 h.2 (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    exact (hNonCore5 _ hlt hOff (fun j hj => by rw [htg]; dsimp only [d] at hj ⊢; omega)).trans hBlkAt
  -- Stitch the 6 sub-calls into `selectUpdatePostCoreBody`
  have hRootW : root + 10 < 2 ^ w := by
    have htg := hTags0.2.1 10 (by omega)
    have := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; decide))); omega
  have hHndW : tok'.handle + 18 + 2 * (d + 1) < 2 ^ w := by
    have htg := hTags0.2.2.2.2.1 (2 * (d + 1) - 1) (by dsimp only [d]; omega)
    have := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; decide))); dsimp only [d] at *; omega
  have hTabW : tok'.table + 4 * d + 3 < 2 ^ w := by
    have htg := hcaps.1.1.2.2.2
    have := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
    unfold solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr at this
    dsimp only [d] at *; omega
  have hSlotDiv := slot_div_formula (B := B) (hBe.symm ▸ heCapPos)
  have hF1Lt : B.fPtr 1 < 2 ^ w := by
    have := B.blk_le_last (show 1 ≤ B.d by omega)
    have : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
    omega
  have hEmb0LeF1 : B.embPtr 0 + eCap ≤ B.fPtr 1 := by
    have h1 : B.fPtr 1 = B.fPtr 0 + B.levelSize := by unfold SelectBlocksLoc.fPtr; simp
    unfold SelectBlocksLoc.levelSize at h1
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
    rw [← hBe]; omega
  have hLMAddr : solverLevelMetaAddr tok'.table d = tok'.table + 2 * d + 2 := by
    unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; dsimp only [d]; omega
  have hSHAddr : solverSelectHeapAddr tok'.table d = tok'.table + 4 * d + 2 := by
    unfold solverSelectHeapAddr; rw [hLMAddr]; omega
  have hSBAddr : solverSelectBlocksAddr tok'.table d = tok'.table + 4 * d + 3 := by
    unfold solverSelectBlocksAddr; rw [hSHAddr]
  obtain ⟨outF, cBody, hrBody, hOutMem, hcBody⟩ :=
    selectUpdatePostCoreBody_stitch
      (handle := tok'.handle) (table := tok'.table) (slots := tok'.slots)
      (edgeRecords := tok'.edgeRecords) (treeHeap := tok'.treeHeap) (d := d)
      (sb := sb) (blkBase := B.base) (metaBase := metaBase) (L := L)
      (vCap := vCap) (eCap := eCap) (pLast := pLast)
      (emb0 := B.embPtr 0) (f1 := B.fPtr 1) (slot := B.slot)
      (g0Ptr := B.g0Ptr) (G0Ptr := solverLevelG tok' memCore 0)
      (termHandle := tok'.termHandle) (termBran := modelPre.chain.lastBran)
      (firstReb := firstReb)
      hw16 hdPos heCapPos hRootW (by omega) hHndW hTabW (by omega) (by omega) (by omega)
      hEmb0LeF1 hF1Lt hSlotW (by rw [← hBe]; exact hSlotDiv)
      (by simpa using hrep.1 0 (by simp))
      (by simpa using hrep.1 1 (by simp))
      (by simpa using hrep.1 6 (by simp))
      (by simpa using hrep.1 10 (by simp))
      (by simpa using hrep.2.1 0 (by simp))
      (by simpa using hrep.2.2.2.1 2 (by simp))
      (by rw [← hSHAddr]; exact hhbAt)
      (by rw [← hSBAddr]; exact hBlkAt)
      (by have := hMatchOld.1.1 13 (by simp); simpa [hsbEq, hreg.2.2.1] using this)
      (by have := hMatchOld.1.1 3 (by simp); simpa [hsbEq, hreg.2.2.2.2.2.1, hBLk] using this)
      (by simpa [selectMlocOf, smEntryAddr, smTableOff, hBd, hBv] using (hTabOld.2.2 0 (Nat.zero_le _)).2.1)
      (by simpa [selectMlocOf, smEntryAddr, smTableOff, hBd, hBe] using (hTabOld.2.2 0 (Nat.zero_le _)).2.2.1)
      (by simpa [selectMlocOf, smEntryAddr, smTableOff, hBd] using (hTabOld.2.2 B.d le_rfl).2.2.2.2.2.2.2)
      (by simpa [selectMlocOf, smEntryAddr, smTableOff, hBd] using (hTabOld.2.2 0 (Nat.zero_le _)).2.2.2.2.2.1)
      (by simpa [selectMlocOf, smEntryAddr, smTableOff, hBd] using
            (hTabOld.2.2 1 (by dsimp only [selectMlocOf]; omega)).2.2.2.2.2.2.1)
      (by simpa [selectMlocOf, smG0Off] using hTabOld.1)
      (by unfold solverLevelG; rw [hLMAddr]; rfl)
      (by exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (by exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hOutAt.1
      hbTW (by rw [← hLMAddr]; exact hrTW)
      hpG0 hrG0
      hpFPLLoop (by rw [← hLMAddr]; exact hrFPL)
      hpEmbLoop hrEmb
      hpSufBlocks (by rw [← hLMAddr]; simpa only [hhnd3Eq, htab3Eq, hth3Eq] using hrSuf)
      hpHeapPhase (by simpa only [hsbEq, mloc4, selectMlocOf, C', ChainState.toTreeChain] using hrHeap)
  -- Assemble final `SelectGhost` and invariants
  let sg' : SelectGhost :=
    { loc := loc
      size := sizeOut
      φ := φ'
      owned := sg.owned
      mloc := selectMlocOf B metaBase (solverLevelG tok4 st5.mem) pLast
      coreLen := fun j => C'.chainLen modelPre.chain.ℓ (j + 1)
      reembPot := chainReembPot pot modelPre.chain }
  have hRegAt' : SelectRegionAt G P m vCap eCap pLast sb metaBase B modelPre tok4 sg' outF.mem := by
    rw [hOutMem]
    exact ⟨hreg, hcap, hBd, hBv, hBe, hBLk, hOwnEq, hhbAt5, hBlkAt5, rfl, hTab6, hBlocks6,
      hMatch5, hPot5, rfl, ⟨G₀', σ', σ'_mwu, γ'_ℓ, γ'_c, hModNew⟩⟩
  have hBlkInv' : SolverSelectBlocksInv G L P m vCap eCap pLast B modelPre
      (Rrep.foot root tok4) tok4 sg' outF.mem :=
    hRegAt'.to_solverSelectBlocksInv hFoot4Disj
  have hSelInv' : SolverSelectInv G L P m 4 2 tok4.table modelPre
      (Rrep.foot root tok4) (LevelMetaFoot tok4) sg' outF.mem :=
    hBlkInv'.toSolverSelectInv (hOutMem ▸ hCaps6)
  refine ⟨sc5, cBody, outF, tok4, sg', hrBody, by omega,
    by rw [hHeapCong.1] at hsc5Hi; dsimp only [selectUpdatePostCoreRawSpace, stLw, lim, d, loc] at hsc3Hi hsc4Hi hsc5Hi ⊢; omega,
    hOutMem ▸ hRep6, htab4Eq.trans htab3Eq, hhnd4Eq.trans hhnd3Eq, hlev4Eq.trans hlev3Eq,
    hint4Eq.trans hint3Eq, hrec4Eq.trans hrec3Eq, htree4Eq.trans htree3Eq,
    htrees4Eq.trans htrees3Eq, hedg4Eq.trans hedg3Eq, hth4Eq.trans hth3Eq, htt4Eq.trans htt3Eq,
    hvc4Eq.trans hvc3Eq, hec4Eq.trans hec3Eq,
    fun a ha => by
      rcases hft4 a ha with h3 | h4
      · rcases hft3 a h3 with h0 | h3'
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩,
    fun a ha => hown4 a (hown3 a ha),
    fun a ha => (htag4Lt a (by omega)).trans (htag3Lt a ha),
    fun a ha => (htag4Ne a (by rw [htag3Ne a ha]; exact ha)).trans (htag3Ne a ha),
    hOutMem ▸ hCaps6, rfl, rfl, rfl, hRegAt', hBlkInv', hSelInv', hPhiBd5,
    fun a ha => by rw [hOwnEq] at ha; exact hFoot4Disj a ha.1 ha.2,
    hOutMem ▸ hZ6, fun a ha hnsb hnc => hOutMem ▸ hNonCore5 a ha hnsb hnc, ?_⟩
  have hSufCostEq :
      selectUpdateSuffixBlocksCost
        (fun j => if 0 ≤ j ∧ j < min firstReb cfg.P.d then (modelPre.chain.toTreeChain.activeLSF j).F.F
          else (model.chain.toTreeChain.activeLSF j).F.F)
        (model.chain.G cfg.P.d) modelPre.chain Psc.readout firstReb L capExp B.slot =
      selectUpdateSuffixBlocksCost (fun j => (model.chain.toTreeChain.activeLSF j).F.F)
        (model.chain.G cfg.P.d) modelPre.chain Psc.readout firstReb L capExp B.slot :=
    selectUpdateSuffixBlocksCost_congr fun j hj _ => by
      simp [show ¬ j < firstReb by omega]
  rw [hOutMem, hPhi6, hHeapCong.2] at *
  dsimp only [SelBlocksData.ofChain] at hcSuf
  rw [hBd] at hcSuf
  change cSuf + _ ≤ selectUpdateSuffixBlocksCost
      (fun j => if 0 ≤ j ∧ j < min firstReb cfg.P.d then (modelPre.chain.toTreeChain.activeLSF j).F.F
        else (model.chain.toTreeChain.activeLSF j).F.F)
      (model.chain.G cfg.P.d) modelPre.chain Psc.readout firstReb L capExp B.slot + _ at hcSuf
  rw [hSufCostEq] at hcSuf
  unfold selectUpdatePostCoreRawCost
  dsimp only [Rrep, C, C', d, lim, stLw, uWords, loc] at hcEmb hcSuf hcFPL hcG0 hcTW hcHeap ⊢
  omega

end MinCostFlow.MinRatio
