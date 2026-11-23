module

public import MinCostFlow.MinRatio.SelectLevelDRebuild
public import MinCostFlow.MinRatio.SelectRebuildNoRoom
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.SolverSelectPreserve
import WordRAM.Tactic

/-!
# Terminal shift preserving the select region and select heap (`WireShiftTermSelect`)

Wraps `shiftTermChainProc` (`ShiftTermChainSyncSpecWExt`) with level-`d` select-block refill
(`selectRebuildLevelDBlocksBody`, `SelectLevelDRebuild.lean`) and level-`d` select-heap rebuild
(`selectRebuildLevelBody`, `WireSelectUpdateLevel.lean`):

* `termSelectSpace` and `termSelectFixed`: exact space (`PolyNat`) and fixed step-cost (`m^{o(1)}`)
  overhead of the level-`d` select rebuild in `ShiftTerm`.
* `shiftTermSelectBody`: deterministic Word-RAM wrapper `[root, heap] → nextHeap`.
* `shiftTermSelectBody_runs`: preserves `solverStateRep`, `SolverLevelCapsInv`,
  `SolverSelectBlocksInv`, and `SolverSelectInv` (`solverStateRepSel`) across
  `alg2LoopShiftStep cfg model (Fin.last cfg.P.d)`, with `Δ chainReembPot = 0` and cost
  `termFixed + termSelectFixed + toolMul · Δ totalRuntime + treeMul · Δ totalTreeUpdates`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program
open SparseCore.Program LastLevelProgram

/-! ## 1. Exact select-rebuild space and cost bounds for `ShiftTerm` -/

/-- Exact extra scratch space required by `ShiftTerm` to rebuild level `d`'s select block
and select-heap keys, parameterized by `(d, nD, mD, cap, L, evalSpace)` where
`(G_d).n ≤ nD` and `(G_d).m ≤ mD`. -/
def termSelectSpace (d nD mD cap L evalSpace : ℕ) : ℕ :=
  levelDBlocksSpace d nD mD mD L +
    selectRebuildLevelSpace mD mD cap L evalSpace

/-- Exact extra fixed step cost required by `ShiftTerm` to rebuild level `d`'s select block
and select-heap keys, parameterized by `(d, nD, mD, cap, L, evalCost)`. -/
def termSelectFixed (d nD mD cap L evalCost : ℕ) : ℕ :=
  levelDBlocksCost d nD mD nD mD mD L +
    selectRebuildLevelCost mD mD cap L evalCost + 120

/-! ## 2. Deterministic terminal-shift wrapper with select maintenance -/

/-- Deterministic Word-RAM terminal shift `[root, heap] → nextHeap`: runs `shiftTermChainProc`,
loads `(hb, metaBase, L, d)` at run time from the solver root directory and `table + 4 * d + 2`,
rebuilds level `d`'s select block (`F_d`, `φ_d`, `len_d`) via `rebuildLevelDProc`, and rebuilds
level `d`'s select-heap keys via `rebuildHeapLvlProc`. -/
def shiftTermSelectBody (shiftTermChainProc rebuildLevelDProc rebuildHeapLvlProc : ℕ) : Stmt :=
  .assign 2 (.reg 0) ;;
  .call 3 shiftTermChainProc [.reg 0, .reg 1] ;;
  .assign 4 (.load (.reg 2)) ;;
  .assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.const 5))) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.const 11))) ;;
  .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 7))) (.const 2))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.const shMetaOff))) ;;
  .call 10 rebuildLevelDProc [.reg 2, .reg 9, .reg 6, .reg 3] ;;
  .call 11 rebuildHeapLvlProc [.reg 8, .reg 9, .reg 7, .reg 10] ;;
  .ret (.reg 11)

theorem shiftTermSelectBody_noRand (shiftTermChainProc rebuildLevelDProc rebuildHeapLvlProc : ℕ) :
    (shiftTermSelectBody shiftTermChainProc rebuildLevelDProc rebuildHeapLvlProc).NoRand := by
  simp [shiftTermSelectBody, Stmt.NoRand]

/-! ## 3. Helper lemmas for candidate count, monotonicity, and heap preservation -/

/-- Under `SelectHeapMatchesChain`, the number of heap candidates at level `lvl` is at most
`(C.G lvl).E.card`. -/
theorem levelCandCount_le_card_G {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size lvl : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hlvl : lvl ≤ C.d)
    (hm : SelectHeapMatchesChain mem loc h P C g ℓ size) :
    levelCandCount mem loc lvl ≤ (C.G lvl).E.card := by
  have hok := selectHeapLevelOk_of_matchesChain hH hm (i := lvl) hlvl
  unfold levelCandCount
  refine Finset.card_le_card fun e he => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at he
  have hcand := hok.1 e he.1 he.2.1 he.2.2
  have hsub : (C.activeCore lvl).E ⊆ (C.G lvl).E := by
    unfold TreeChain.activeCore coreGraph
    exact Finset.sdiff_subset
  exact hsub (Finset.mem_sdiff.mp hcand).1

/-- Monotonicity of `levelDBlocksSpace` in `(nF, mF, mG)`. -/
theorem levelDBlocksSpace_mono {d n₁ n₂ m₁ m₂ g₁ g₂ L : ℕ}
    (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) (hg : g₁ ≤ g₂) :
    levelDBlocksSpace d n₁ m₁ g₁ L ≤ levelDBlocksSpace d n₂ m₂ g₂ L := by
  unfold levelDBlocksSpace selectPhiFillSpace
  have h1 : 3 * m₁ ≤ 3 * m₂ := Nat.mul_le_mul_left 3 hm
  have h2 : 2 * n₁ ≤ 2 * n₂ := Nat.mul_le_mul_left 2 hn
  have h3 : n₁ * phiFillEdgeStepSpace d L ≤ n₂ * phiFillEdgeStepSpace d L :=
    Nat.mul_le_mul_right _ hn
  have h4 : g₁ * selCoreLenEdgeSpace L L ≤ g₂ * selCoreLenEdgeSpace L L :=
    Nat.mul_le_mul_right _ hg
  omega

/-- Monotonicity of `levelDBlocksCost` in `(nOld, mOld, nNew, mNew, mG)`. -/
theorem levelDBlocksCost_mono {d no₁ no₂ mo₁ mo₂ nn₁ nn₂ mn₁ mn₂ g₁ g₂ L : ℕ}
    (hno : no₁ ≤ no₂) (hmo : mo₁ ≤ mo₂) (hnn : nn₁ ≤ nn₂) (hmn : mn₁ ≤ mn₂) (hg : g₁ ≤ g₂) :
    levelDBlocksCost d no₁ mo₁ nn₁ mn₁ g₁ L ≤ levelDBlocksCost d no₂ mo₂ nn₂ mn₂ g₂ L := by
  unfold levelDBlocksCost dgRefillFromDynGraphCost dgRefillFromListsCost dgPackEdgeTriplesCost
    selectPhiFillCost
  have h1 := Nat.mul_le_mul_right (d * (130 * L + 240) + 125 * L + 900) hnn
  have h2 := Nat.mul_le_mul_right (selCoreLenEdgeCost L L + 40) hg
  omega

/-- Monotonicity of `selectRebuildLevelSpace` in `(oldCand, mNew)`. -/
theorem selectRebuildLevelSpace_mono {o₁ o₂ m₁ m₂ cap L evalSpace : ℕ}
    (ho : o₁ ≤ o₂) (hm : m₁ ≤ m₂) :
    selectRebuildLevelSpace o₁ m₁ cap L evalSpace ≤
      selectRebuildLevelSpace o₂ m₂ cap L evalSpace := by
  unfold selectRebuildLevelSpace heapClearLevelSpace selectProcessListSpace
  have h1 := Nat.mul_le_mul_right (heapRebalanceSpace cap L) ho
  have h2 := Nat.mul_le_mul_right (selectProcessEdgeSpace cap L evalSpace) hm
  omega

/-- Monotonicity of `selectRebuildLevelCost` in `(oldCand, mNew)`. -/
theorem selectRebuildLevelCost_mono {o₁ o₂ m₁ m₂ cap L evalCost : ℕ}
    (ho : o₁ ≤ o₂) (hm : m₁ ≤ m₂) :
    selectRebuildLevelCost o₁ m₁ cap L evalCost ≤
      selectRebuildLevelCost o₂ m₂ cap L evalCost := by
  unfold selectRebuildLevelCost heapClearLevelCost selectProcessListCost
  have h1 := Nat.mul_le_mul_right (heapDeleteCost cap L + 60) ho
  have h2 := Nat.mul_le_mul_right (selectProcessEdgeCost cap L evalCost + 40) hm
  omega

/-- Rebuilding level `d` of the select heap when `C` and `C'` agree on all levels `< d`
(and on `g`, `ℓ`) preserves `SelectHeapMatchesChain`. -/
theorem selectRebuildLevelD_preserves_matchesChain
    {w h P size : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {g g' ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost scratch ret : ℕ} {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hdEq : C'.d = C.d) (hd' : loc.d = C'.d)
    (hG : ∀ j < C.d, C'.G j = C.G j)
    (hLSF : ∀ j < C.d, C'.activeLSF j = C.activeLSF j)
    (hS : ∀ j < C.d, C'.activeS j = C.activeS j)
    (hEmb : ∀ j < C.d, C'.activeEmb j = C.activeEmb j)
    (hg : ∀ e, g' e = g e) (hℓ : ∀ e, ℓ' e = ℓ e)
    (hMatchOld : SelectHeapMatchesChain mem loc h P C g ℓ size)
    (hPost : (selectRebuildLevelContract w h P loc mloc C' g' ℓ' φ coreLen
      evalSpace evalCost).post [loc.hb, mloc.metaBase, C'.d, scratch] mem ret mem') :
    ∃ size', SelectHeapMatchesChain mem' loc h P C' g' ℓ' size' := by
  obtain ⟨_, _, ⟨size', hat', _⟩, _, _, hokD, hpres⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hokD hpres
  refine ⟨size', selectHeapMatchesChain_of_levelOk hH' hat' hd' fun i hi => ?_⟩
  by_cases hilt : i < C'.d
  · have hiltC : i < C.d := hdEq ▸ hilt
    have hOldOk := selectHeapLevelOk_of_matchesChain hH hMatchOld (i := i) (Nat.le_of_lt hiltC)
    have hcandDisj : ∀ e ∈ (C'.activeCore i).E \ (C'.activeS i).E,
        e ∉ (C'.activeCore C'.d).E \ (C'.activeS C'.d).E := fun e he hed => by
      have hEq := C'.level_unique_of_mem_activeCore_diff hH' hi le_rfl he hed; omega
    refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
    · by_cases hinD : e ∈ (C'.activeCore C'.d).E \ (C'.activeS C'.d).E
      · have hlD := (hokD.2 e hinD).2.2.1; omega
      · by_cases h0eq : mem (loc.posPtr + e) = 0 ∨ mem (loc.lvlPtr + e) = C'.d
        · exact (hnz ((hpres e heCap hinD).1 h0eq)).elim
        · push Not at h0eq
          have hlEq := ((hpres e heCap hinD).2 h0eq.1 h0eq.2).2.1
          have hOld := hOldOk.1 e heCap h0eq.1 (hlEq.symm.trans hl)
          exact (selectHeap_prefix_preserved (i₀ := C.d) hG hLSF hS hEmb hg hℓ hiltC e).1.mpr hOld
    · have hPref := selectHeap_prefix_preserved (i₀ := C.d) hG hLSF hS hEmb hg hℓ hiltC e
      have hOld : e ∈ (C.activeCore i).E \ (C.activeS i).E := hPref.1.mp he
      obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldOk.2 e hOld
      obtain ⟨hwi, hwl⟩ := hPref.2 hOld
      obtain ⟨k1, k2, k3, k4⟩ := (hpres e heCap (hcandDisj e he)).2 hnz0 (by omega)
      exact ⟨heCap, k1, k2.trans hl0, by rw [k3, k4, hwi, hwl]; exact hrep0⟩
  · have hiEq : i = C'.d := by omega
    subst hiEq; exact hokD

/-- A terminal shift does not change any interior tool state `scState j` (`j < d`), so
`chainReembPot pot` is unchanged. -/
theorem termShift_chainReembPot_eq {cfg : Alg2Config} (pot : cfg.T.State → ℕ)
    (model : Alg2State cfg) :
    chainReembPot pot (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain =
      chainReembPot pot model.chain := by
  unfold chainReembPot
  refine Finset.sum_congr rfl fun j hj => ?_
  have hEq : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.scState j =
      model.chain.scState j := by
    simp [alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  rw [hEq]

/-! ## 4. Main verification theorem for `shiftTermSelectBody` -/

set_option maxHeartbeats 1200000 in
/-- **Terminal shift with select-region and select-heap rebuild:**
`shiftTermSelectBody` advances the terminal branch, syncs the path tree, rebuilds level `d`'s
select block (`B.fPtr d`, `B.phiPtr d`, `B.lenPtr d`) and select-heap keys, and preserves
`solverStateRep`, `SolverLevelCapsInv`, `SolverSelectBlocksInv`, and `SolverSelectInv`
(`solverStateRepSel`) with `Δ chainReembPot = 0`. -/
theorem shiftTermSelectBody_runs
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap vCap eCap pLast
      termSpace termFixed toolMul treeMul nD mD evalSpace evalCost
      shiftTermChainProc rebuildLevelDProc refillDGProc phiFillProc coreLenFillProc coreLenEdgeProc
      rebuildHeapLvlProc root heap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {ω : ℕ → Bool} {B : SelectBlocksLoc} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {sg : SelectGhost} {mem0 mem : ℕ → ℕ}
    {B_num R_num : ℤ} {G₀' : MGraph} {σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hCoreLocal : Rcore.Local)
    (hTermSpec : ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      lastTreeCap cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul)
    (hpRebuildD : p.procs[rebuildLevelDProc]? =
      some (selectRebuildLevelDBlocksBody refillDGProc phiFillProc coreLenFillProc))
    (hpFill : p.procs[coreLenFillProc]? = some (selCoreLenFillBody coreLenEdgeProc))
    (hEdge : MeetsContract w p coreLenEdgeProc (selCoreLenEdgeContract w P))
    (hRefill :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      let oldF := (model.chain.lastLSFs model.chain.lastBran).F.F
      let newF := (model'.chain.lastLSFs model'.chain.lastBran).F.F
      ∀ vcLast ecLast,
        MeetsContract w p refillDGProc
          (dgRefillFromDynGraphContract w B.vCap B.eCap vcLast ecLast oldF newF))
    (hPhiFill :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      let mloc := selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) pLast
      MeetsContract w p phiFillProc
        (selectPhiFillContract w 4 P mloc model'.chain.toTreeChain G₀' model'.chain.g
          model'.chain.ℓ σ' σ'_mwu γ'_ℓ γ'_c sg.φ))
    (hRebHeap :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      let mloc := selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) pLast
      ∀ φ' : ℕ → ℕ → ℝ,
        MeetsContract w p rebuildHeapLvlProc
          (selectRebuildLevelNoRoomContract w 4 P sg.loc mloc model'.chain.toTreeChain
            model'.chain.g model'.chain.ℓ φ'
            (fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
            evalSpace evalCost))
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hpLastW : pLast < 2 ^ w) (hLW : L < 2 ^ w)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hCaps0 : SolverLevelCapsInv P V vCap eCap model tok mem0)
    (hSel0 : SolverSelectBlocksInv G L P m vCap eCap pLast B model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok) tok sg mem0)
    (hMemEq : ∀ a, tok.tag a ≠ 5 → mem a = mem0 a)
    (hSched' : SolverScheduleAt mem tok.levelsEnd (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)))
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B_num R_num)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B_num)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B_num)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit model)
    (hBranLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hLastBranLt : model.chain.lastBran < model.chain.lastK)
    (hLastKW : model.chain.lastK < 2 ^ w)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B_num + R_num) < (Num.capacity 4 L : ℤ))
    (hNewForest : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.toTreeChain.chainTree.IsForest)
    (hOldSub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hNewSub : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.toTreeChain.chainTree.E ⊆
      (model.chain.G 0).E)
    (hDisjPref : Disjoint
      ((Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
      ((model.chain.lastLSFs model.chain.lastBran).F.F.E ∪
        (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E))
    (hLastCap : (model.chain.lastLSFs model.chain.lastBran).F.F.m +
      (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.m ≤ lastTreeCap)
    (hMod' : SelectModelInv (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)) G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hGdSize : (model.chain.G cfg.P.d).n ≤ nD ∧ (model.chain.G cfg.P.d).m ≤ mD)
    (hGdCapHeap : ∀ e ∈ (model.chain.G cfg.P.d).E, e < sg.loc.cap)
    (hFitsE :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      ∀ e ∈ (model'.chain.lastLSFs model'.chain.lastBran).F.F.E,
        PotGradEvalFits 4 L P model'.chain.toTreeChain model'.chain.g sg.φ cfg.P.d e)
    (hFitsW :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      ForestWalkFits 4 L P (model'.chain.lastLSFs model'.chain.lastBran).F.F
        (potGrad model'.chain.toTreeChain model'.chain.g sg.φ cfg.P.d))
    (hLenFits :
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      ∀ e ∈ (model'.chain.G cfg.P.d).E,
        let prev := model'.chain.toTreeChain.chainLen model'.chain.ℓ cfg.P.d e
        let cur := model'.chain.toTreeChain.chainLen model'.chain.ℓ (cfg.P.d + 1) e
        (∃ qp : ℤ, Num.Fits 4 L (qp * (2 : ℤ) ^ pLast) ∧ (qp : ℝ) / (2 : ℝ) ^ P = prev) ∧
        (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ (P + pLast) = cur))
    (hBelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        sg.owned a → a < heap)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + (termSpace + termSelectSpace cfg.P.d nD mD sg.loc.cap L evalSpace) < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    ∃ nextHeap cost out tok' sg',
      Runs w p ω (shiftTermSelectBody shiftTermChainProc rebuildLevelDProc rebuildHeapLvlProc)
        (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧
      nextHeap ≤ heap + (termSpace + termSelectSpace cfg.P.d nD mD sg.loc.cap L evalSpace) ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
      tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
      Rrep.rep root model' tok' out.mem ∧
      SolverLevelCapsInv P V vCap eCap model' tok' out.mem ∧
      (SolverLevelLayoutAt vCap eCap tok mem0 → SolverLevelLayoutAt vCap eCap tok' out.mem) ∧
      SolverSelectBlocksInv G L P m vCap eCap pLast B model' (Rrep.foot root tok') tok' sg' out.mem ∧
      SolverSelectInv G L P m 4 2 tok'.table model' (Rrep.foot root tok') (LevelMetaFoot tok')
        sg' out.mem ∧
      sg'.owned = sg.owned ∧ sg'.reembPot = sg.reembPot ∧
      (∀ j < cfg.P.d, sg'.φ j = sg.φ j) ∧
      (let F' := (model'.chain.lastLSFs model'.chain.lastBran).F.F
       ∀ v ∈ F'.V, ∃ r ∈ F'.V, F'.Connected v r ∧
        sg'.φ cfg.P.d v = walkInner (potGrad model'.chain.toTreeChain model'.chain.g sg.φ cfg.P.d)
          (F'.forestPath v r)) ∧
      PathTreeNumericInv tok'.tree tok'.trees B_num R_num ∧
      OffTreeRecInv model' L out.mem tok'.edgeRecords B_num ∧
      OffTreeRecBound model' L out.mem tok'.edgeRecords B_num ∧
      ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → ¬ sg.owned a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
      cost + Rrep.phi root tok' out.mem ≤
        (termFixed + termSelectFixed cfg.P.d nD mD sg.loc.cap L evalCost) +
          toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
          treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
          Rrep.phi root tok mem0 := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  set d := cfg.P.d
  set model' := alg2LoopShiftStep cfg model (Fin.last d)
  set C := model.chain.toTreeChain
  set C' := model'.chain.toTreeChain
  obtain ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown, hoff, hhbAddr, hblkAddr, hmloc, hclen,
    htab0, hblocks0, hpot0, hmatch0, hmod0⟩ := hSel0
  obtain ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod0'⟩ := hmod0
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  have hEndPos : sg.loc.hb < B.endAddr := by
    have : 0 < selectHeapSize sg.loc.cap sg.loc.d sg.loc.Lk := by
      unfold selectHeapSize shHdrSize; omega
    rw [sg.loc.endAddr_eq] at hlo2; omega
  have hBEnd : B.endAddr ≤ heap := by
    have := hBelow (B.endAddr - 1) (Or.inr (by rw [hown]; exact ⟨by omega, by omega⟩)); omega
  -- Step 1: run `shiftTermChainProc`
  obtain ⟨bTerm, hbTerm, hTermRun⟩ := hTermSpec
  obtain ⟨heap1, c1, out1, tok', hRun1, h1Lo, h1Hi, hLevEq, hCapEq, hRep1, hPres1,
    hNum1, hOff1, hOffBd1, hz1, hFr1, hFoot1, hCost1⟩ :=
    hTermRun root heap pos ω mem0 mem model tok B_num R_num hRep0 hMemEq hSched'
      hNum0 hOffInv0 hOffBd0 hCapFacts hBranLt hLastBranLt hLastKW hLogW hCapT hNewForest
      hOldSub hNewSub hDisjPref hLastCap (fun a ha => hBelow a (Or.inl ha)) hz (by omega)
  -- `model'` agrees with `model` on all levels `< d`, `G d`, `g`, `ℓ`
  have hChEq : model'.chain = (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain cfg.P.d).1 := rfl
  have hBd' : B.d = d := hBd
  have hChG : ∀ j, model'.chain.G j = model.chain.G j := fun j => by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChSc : ∀ j < d, model'.chain.scState j = model.chain.scState j := fun j _ => by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChBr : ∀ j < d, model'.chain.bran j = model.chain.bran j := fun j _ => by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChG_vec : model'.chain.g = model.chain.g := by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChL_vec : model'.chain.ℓ = model.chain.ℓ := by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChLastK : model'.chain.lastK = model.chain.lastK := by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hChLastBran : model'.chain.lastBran = (model.chain.lastBran + 1) % model.chain.lastK := by
    rw [hChEq]; simp [Chain.Ordered.algorithm1_shift]
  have hBran'Lt : model'.chain.lastBran < model'.chain.lastK := by
    rw [hChLastBran, hChLastK]; exact Nat.mod_lt _ (by omega)
  have hC'LSF_lt : ∀ j < d, C'.activeLSF j = C.activeLSF j := fun j hj => by
    have hj' : j < cfg.P.d := hj
    simp only [C, C', TreeChain.activeLSF, ChainState.toTreeChain, hj', ↓reduceIte,
      hChSc j hj, hChBr j hj]
  have hC'S_lt : ∀ j < d, C'.activeS j = C.activeS j := fun j hj => by
    have hj' : j < cfg.P.d := hj
    simp only [C, C', TreeChain.activeS, ChainState.toTreeChain, hj', ↓reduceIte,
      hChSc j hj, hChBr j hj]
  have hC'Emb_lt : ∀ j < d, C'.activeEmb j = C.activeEmb j := fun j hj => by
    have hj' : j < cfg.P.d := hj
    simp only [C, C', TreeChain.activeEmb, ChainState.toTreeChain, hj', ↓reduceIte,
      hChSc j hj, hChBr j hj]
  have hC'Core_lt : ∀ j < d, C'.activeCore j = C.activeCore j := fun j hj => by
    unfold TreeChain.activeCore
    rw [hC'LSF_lt j hj]
    change coreGraph (model'.chain.G j) _ = coreGraph (model.chain.G j) _
    rw [hChG j]
  have hC'Len_le : ∀ j ≤ d, C'.chainLen model'.chain.ℓ j = C.chainLen model.chain.ℓ j := by
    intro j
    induction j with
    | zero => intro _; simpa [TreeChain.chainLen] using hChL_vec
    | succ j ih =>
      intro hj
      simp only [TreeChain.chainLen]
      rw [ih (by omega), hC'LSF_lt j (by omega)]
  -- `SolverLevelCapsInv` after `shiftTermChainProc`
  have hCaps1 : SolverLevelCapsInv P V vCap eCap model' tok' out1.mem :=
    hPres1.to_capsInv hCaps0
      (by rw [hChEq]; simp [Chain.Ordered.algorithm1_shift])
      (fun _ _ => by rw [hChEq]; simp [Chain.Ordered.algorithm1_shift])
      (fun j _ => hChG j) hChSc hChBr hChL_vec
  -- Region arithmetic helpers
  have hlo3' : sg.loc.metaPtr + selectLevelMetaSize d ≤ B.base := by
    rw [← hBd']; exact le_of_eq hlo3
  have hBlkD_le : B.fPtr d + B.levelSize ≤ B.lastGPtr := B.blk_le_last (hBd.symm ▸ le_rfl)
  have hBase_le_fD : B.base ≤ B.fPtr d := by unfold SelectBlocksLoc.fPtr; omega
  have hFD_le_embD : B.fPtr d ≤ B.embPtr d := by
    have := B.embPtr_eq d; omega
  have hEmbD_le_end : B.embPtr d ≤ B.endAddr := by
    have h1 := B.blkEnd_eq d; have h2 := B.embPtr_eq d
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  -- Select region `[hb, B.endAddr)` was completely untouched by `shiftTermChainProc`
  have hagSel1 : ∀ a, sg.loc.hb ≤ a → a < B.endAddr → out1.mem a = mem0 a := fun a h1 h2 => by
    have ho : sg.owned a := by rw [hown]; exact ⟨h1, h2⟩
    have hnf : ¬ Rrep.foot root tok a := hoff a ho
    have htag5 : tok.tag a ≠ 5 := fun ht5 => hnf (Or.inl (hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a (by omega)))
    exact (hFr1 a (hBelow a (Or.inr ho)) hnf).trans (hMemEq a htag5)
  have hoff1 : ∀ a, sg.loc.hb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok' a := fun a h1 h2 hf' => by
    rcases hFoot1 a hf' with hf | ⟨hge, _⟩
    · exact hoff a (by rw [hown]; exact ⟨h1, h2⟩) hf
    · omega
  have hBelow1 : ∀ a, Rrep.foot root tok' a ∨ (sg.loc.hb ≤ a ∧ a < B.endAddr) → a < heap1 := by
    rintro a (hf' | ⟨h1, h2⟩)
    · rcases hFoot1 a hf' with hf | ⟨_, hlt⟩
      · exact lt_of_lt_of_le (hBelow a (Or.inl hf)) h1Lo
      · exact hlt
    · exact lt_of_lt_of_le (hBelow a (Or.inr (by rw [hown]; exact ⟨h1, h2⟩))) h1Lo
  -- `solverLevelG` and `mloc` are preserved across `shiftTermChainProc`
  have hG1eq : ∀ j < d, solverLevelG tok' out1.mem j = solverLevelG tok mem0 j := fun j hj => by
    unfold solverLevelG
    rw [hPres1.1]
    have htag : tok.tag (solverLevelMetaAddr tok.table d + d + j) = 22 + d := by
      have := hCaps0.1.2.2.2.2.1 (d + j) (by omega); simpa [Nat.add_assoc] using this
    exact (hPres1.metaEq _ (Or.inr (Or.inr (Or.inl htag)))).2
  have hmloc1Eq : selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast = sg.mloc := by
    rw [hmloc]; unfold selectMlocOf
    congr 1
    · funext j; split_ifs with h
      · exact hG1eq j (by rw [← hBd']; exact h)
      · rfl
    · funext j; split_ifs with h1 h2
      · exact hG1eq (j + 1) (by rw [← hBd']; exact h1)
      · rfl
      · rfl
  have htab1 : SelectMetaTableAt out1.mem (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast) := by
    rw [hmloc1Eq]
    exact htab0.of_agree fun a h1 h2 => hagSel1 a
      (by rw [hmloc] at h1; simp only [selectMlocOf] at h1; omega)
      (by rw [hmloc] at h2; simp only [selectMlocOf] at h2; omega)
  have hD1 : SelBlocksDataAt out1.mem B P
      (SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ) pLast :=
    (selectBlocksAt_iff_data.mp hblocks0).of_agree fun a h1 h2 => hagSel1 a (by omega) h2
  have hMatch1 : SelectHeapMatchesChain out1.mem sg.loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hmatch0.of_agree fun a h1 h2 => hagSel1 a h1 (by omega)
  -- Readout facts from `hRep1` and `hPres1` for the intermediate register loads
  have hRootDir1 := hRep1.1
  have hDetHdr1 := hRep1.2.1
  have hInitPar1 := hRep1.2.2.2.1
  have hTags1 := hRep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hRoot0_1 : out1.mem root = tok'.handle := by simpa using hRootDir1 0 (by simp)
  have hRoot1_1 : out1.mem (root + 1) = tok'.table := by simpa using hRootDir1 1 (by simp)
  have hHd5_1 : out1.mem (tok'.handle + 5) = L := by simpa using hDetHdr1 5 (by simp)
  have hHd11_1 : out1.mem (tok'.handle + 11) = d := by
    have := hInitPar1 2 (by simp); simpa [Nat.add_assoc] using this
  have hHbAddr1 : out1.mem (tok'.table + 4 * d + 2) = sg.loc.hb := by
    rw [← solverSelectHeapAddr_eq_four_two, hPres1.1]
    exact (hPres1.metaEq _ (Or.inr (Or.inl hCaps0.1.1.2.2.1))).2.trans hhbAddr
  have hBlkAddr1 : out1.mem (solverSelectBlocksAddr tok'.table d) = B.base := by
    rw [hPres1.1]
    exact (hPres1.metaEq _ (Or.inr (Or.inl hCaps0.1.1.2.2.2))).2.trans hblkAddr
  have hMetaPtr1 : out1.mem (sg.loc.hb + shMetaOff) = sg.loc.metaPtr := by
    have hh := hMatch1.1.1 13 (by simp)
    simpa [shMetaOff] using hh
  -- Size bounds on `oldF`, `newF`, `G_d` against `(nD, mD)`
  set oldF := (model.chain.lastLSFs model.chain.lastBran).F.F
  set newF := (model'.chain.lastLSFs model'.chain.lastBran).F.F
  have hOldFSub := C.forestsAreSubgraphs_of_holds hmod0'.1 d le_rfl
  have hNewFSub := C'.forestsAreSubgraphs_of_holds hMod'.1 d le_rfl
  have hC_actD : (C.activeLSF d).F.F = oldF := by
    have : C.activeLSF d = model.chain.lastLSFs model.chain.lastBran := by
      simp [C, TreeChain.activeLSF, ChainState.toTreeChain, d]
    rw [this]
  have hC'_actD : (C'.activeLSF d).F.F = newF := by
    have : C'.activeLSF d = model'.chain.lastLSFs model'.chain.lastBran := by
      simp [C', TreeChain.activeLSF, ChainState.toTreeChain, d]
    rw [this]
  rw [hC_actD] at hOldFSub; rw [hC'_actD] at hNewFSub
  have hOldFLe : oldF.n ≤ nD ∧ oldF.m ≤ mD :=
    ⟨(Finset.card_le_card hOldFSub.1).trans hGdSize.1,
      (Finset.card_le_card hOldFSub.2.1).trans hGdSize.2⟩
  have hNewFLe : newF.n ≤ nD ∧ newF.m ≤ mD :=
    ⟨(Finset.card_le_card hNewFSub.1).trans (by rw [show C'.G d = model.chain.G d from hChG d]; exact hGdSize.1),
      (Finset.card_le_card hNewFSub.2.1).trans (by rw [show C'.G d = model.chain.G d from hChG d]; exact hGdSize.2)⟩
  have hSpDLe : levelDBlocksSpace d newF.n newF.m (model'.chain.G d).m L ≤
      levelDBlocksSpace d nD mD mD L :=
    levelDBlocksSpace_mono hNewFLe.1 hNewFLe.2 (by rw [hChG d]; exact hGdSize.2)
  have hCostDLe : levelDBlocksCost d oldF.n oldF.m newF.n newF.m (model'.chain.G d).m L ≤
      levelDBlocksCost d nD mD nD mD mD L :=
    levelDBlocksCost_mono hOldFLe.1 hOldFLe.2 hNewFLe.1 hNewFLe.2 (by rw [hChG d]; exact hGdSize.2)
  -- Step 2: run `selectRebuildLevelDBlocksBody`
  have hRun2 := selectRebuildLevelDBlocks_runs (w := w) (L := L) (P := P) (m := m) (V := V)
    (psi := psi) (k := k) (epsExp := epsExp) (drainUnit := drainUnit)
    (vCap := vCap) (eCap := eCap) (pLast := pLast) (root := root) (scratch := heap1)
    (pos := out1.pos) (refillDGProc := refillDGProc) (phiFillProc := phiFillProc)
    (coreLenFillProc := coreLenFillProc) (coreLenEdgeProc := coreLenEdgeProc)
    (cfg := cfg) (Rcore := Rcore) (p := p) (ω := ω) (B := B) (loc := sg.loc) (model := model')
    (tok := tok') (mem := out1.mem)
    (D := SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ)
    (G₀ := G₀') (σ := σ') (σ_mwu := σ'_mwu) (γ_ℓ := γ'_ℓ) (γ_c := γ'_c)
    hpFill hEdge (by simp only [SelBlocksData.ofChain]; rw [hC_actD]; exact hRefill tok'.vcLast tok'.ecLast)
    (by rw [hmloc1Eq, hmloc]; exact hPhiFill)
    hw16 hw10 hBd hBv hBe hBLk hreg hRep1 hCaps1 htab1 hD1
    ⟨fun j hj => ⟨by simp only [SelBlocksData.ofChain]; exact (hChG j).symm ▸ rfl,
        by simp only [SelBlocksData.ofChain]; exact (hChG j).symm ▸ rfl,
        by simp only [SelBlocksData.ofChain]; rw [hC'LSF_lt j hj],
        by simp only [SelBlocksData.ofChain]; exact (hC'Len_le (j + 1) (by omega)).symm,
        by simp only [SelBlocksData.ofChain]; rw [hC'Core_lt j hj],
        by simp only [SelBlocksData.ofChain]; rw [hC'Emb_lt j hj]⟩,
      by simp only [SelBlocksData.ofChain, hBd]; exact (hChG d).symm,
      by simp only [SelBlocksData.ofChain]; exact (hChG 0).symm ▸ rfl,
      by simp only [SelBlocksData.ofChain]; exact hChG_vec.symm⟩
    (fun j hj => by
      have hp := hpot0 j (by change j ≤ d; omega)
      unfold SelectPotInvAt at hp ⊢
      dsimp only [SelBlocksData.ofChain]
      have hpg : potGrad C' model'.chain.g sg.φ j = potGrad C model.chain.g sg.φ j := by
        funext e
        rw [potGrad_eq_sum, potGrad_eq_sum, hChG_vec]
        congr 1
        refine Finset.sum_congr rfl fun t ht => ?_
        have htd : t < d := by have := Finset.mem_range.mp ht; omega
        simp only [C, C', ChainState.toTreeChain]
        rw [hChG t]
      rw [hpg, hC'LSF_lt j hj]; exact hp)
    hMod'.1 hBran'Lt
    ⟨by rw [hChG d]; exact hblocks0.1 d (hBd.symm ▸ le_rfl),
      by rw [hChG d]; exact hblocks0.2.1 d (hBd.symm ▸ le_rfl)⟩
    hFitsE hFitsW hLenFits hoff1 hBelow1 hpLastW hLW hz1
    (by change heap1 + levelDBlocksSpace d newF.n newF.m (model'.chain.G d).m L < 2 ^ w
        have := hSpDLe; unfold termSelectSpace at hRoom; omega)
  obtain ⟨heap2, c2, out2, φd', hRunD, h2Lo, h2Hi, hc2, htab2, hblk2, hpot2, hFillD, hz2, hFr2⟩ := hRun2
  have hRoom' : heap + (termSpace + (levelDBlocksSpace d nD mD mD L +
      selectRebuildLevelSpace mD mD sg.loc.cap L evalSpace)) < 2 ^ w := hRoom
  have h2Hi' : heap2 ≤ heap1 + levelDBlocksSpace d nD mD mD L :=
    (show heap2 ≤ heap1 + levelDBlocksSpace d newF.n newF.m (model'.chain.G d).m L from h2Hi).trans
      (Nat.add_le_add_left hSpDLe _)
  have hc2' : c2 ≤ levelDBlocksCost d nD mD nD mD mD L := by
    have h := hc2
    change c2 ≤ levelDBlocksCost d (C.activeLSF d).F.F.n (C.activeLSF d).F.F.m
      newF.n newF.m (model'.chain.G d).m L at h
    rw [hC_actD] at h
    exact h.trans hCostDLe
  have hFr2' : ∀ a < heap1, (a < B.fPtr d ∨ B.embPtr d ≤ a) → out2.mem a = out1.mem a := hFr2
  -- Frame facts after Step 2: solver foot, heap block, and `table` are untouched (`B.fPtr d ≥ B.base ≥ loc.endAddr`)
  have hFD_ge_end : sg.loc.endAddr ≤ B.fPtr d := by omega
  have hAgFoot2 : ∀ a, Rrep.foot root tok' a → out2.mem a = out1.mem a := fun a ha =>
    hFr2' a (hBelow1 a (Or.inl ha)) (by
      by_contra hc; push Not at hc
      exact hoff1 a (by omega) (by omega) ha)
  have hRep2 : Rrep.rep root model' tok' out2.mem :=
    (solverStateRep_local cfg L P m V psi k epsExp drainUnit hCoreLocal root model' tok'
      out1.mem out2.mem (fun a ha => (hAgFoot2 a ha).symm)).1 hRep1
  have hPhiEq2 : Rrep.phi root tok' out2.mem = Rrep.phi root tok' out1.mem :=
    (solverStateRep_local cfg L P m V psi k epsExp drainUnit hCoreLocal root model' tok'
      out1.mem out2.mem (fun a ha => (hAgFoot2 a ha).symm)).2.symm
  have hCaps2 : SolverLevelCapsInv P V vCap eCap model' tok' out2.mem :=
    hCaps1.preserve rfl hCaps1.1.2.1
      (fun a ha => ⟨rfl, hAgFoot2 a (LevelMetaFoot.mem_foot hRep1 ha)⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCaps1.1 hCaps1.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hMatch2 : SelectHeapMatchesChain out2.mem sg.loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hMatch1.of_agree fun a h1 h2 => hFr2' a (by omega) (Or.inl (by omega))
  have hG2eq : ∀ j < d, solverLevelG tok' out2.mem j = solverLevelG tok' out1.mem j := fun j hj => by
    unfold solverLevelG
    have htag : tok'.tag (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
      have := hCaps1.1.2.2.2.2.1 (cfg.P.d + j) (by omega); simpa [Nat.add_assoc] using this
    exact hAgFoot2 _ (LevelMetaFoot.mem_foot hRep1 (Or.inr (Or.inr (Or.inl htag))))
  have hmloc2Eq : selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out2.mem) pLast =
      selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast := by
    unfold selectMlocOf
    congr 1
    · funext j; split_ifs with h
      · exact hG2eq j (by rw [← hBd']; exact h)
      · rfl
    · funext j; split_ifs with h1 h2
      · exact hG2eq (j + 1) (by rw [← hBd']; exact h1)
      · rfl
      · rfl
  have hMeta2 : SelectLevelMetaAt out2.mem (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast)
      4 P C' model'.chain.g model'.chain.ℓ (Function.update sg.φ d φd')
      (fun j => C'.chainLen model'.chain.ℓ (j + 1)) := by
    rw [← hmloc2Eq]
    exact selectLevelMetaAt_of_solver hBd hBv hBe (hmloc2Eq.symm ▸ htab2) hblk2 hCaps2 hMod' hpot2
  have hDisj2 : SelectMetaDisjoint (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast)
      sg.loc heap2 := by
    rw [← hmloc2Eq]
    exact selectMetaDisjoint_of_solver_region hBd hBv hBe hreg hCaps2
      (fun a ha => LevelMetaFoot.mem_foot hRep2 ha) hoff1
      (fun a ha => lt_of_lt_of_le (hBelow1 a ha) h2Lo)
  have hCandLe : levelCandCount out2.mem sg.loc d ≤ mD :=
    (levelCandCount_le_card_G hmod0'.1 le_rfl hMatch2).trans hGdSize.2
  have hSpHeapLe : selectRebuildLevelSpace (levelCandCount out2.mem sg.loc d) (C'.G d).E.card
      sg.loc.cap sg.loc.Lk evalSpace ≤ selectRebuildLevelSpace mD mD sg.loc.cap L evalSpace := by
    rw [hreg.2.2.2.2.2.1, hBLk]
    exact selectRebuildLevelSpace_mono hCandLe (by change (model'.chain.G d).m ≤ mD; rw [hChG d]; exact hGdSize.2)
  have hCostHeapLe : selectRebuildLevelCost (levelCandCount out2.mem sg.loc d) (C'.G d).E.card
      sg.loc.cap sg.loc.Lk evalCost ≤ selectRebuildLevelCost mD mD sg.loc.cap L evalCost := by
    rw [hreg.2.2.2.2.2.1, hBLk]
    exact selectRebuildLevelCost_mono hCandLe (by change (model'.chain.G d).m ≤ mD; rw [hChG d]; exact hGdSize.2)
  -- Step 3: combine all calls in `shiftTermSelectBody`
  have hTableLt1 : tok'.table + 4 * d + 2 < heap1 := by
    rw [← solverSelectHeapAddr_eq_four_two]
    exact hBelow1 _ (Or.inl (LevelMetaFoot.mem_foot hRep1 (Or.inr (Or.inl hCaps1.1.1.2.2.1))))
  have hRootLt1 : root + 1 < heap1 :=
    hBelow1 _ (Or.inl (Or.inl (hTags1.1 _ (by rw [hTags1.2.1 1 (by omega)]; decide))))
  have hHdLt1 : tok'.handle + 11 < heap1 :=
    hBelow1 _ (Or.inl (Or.inl (hTags1.1 _ (by rw [hTags1.2.2.1 11 (by omega)]; decide))))
  have hHbMetaLt1 : sg.loc.hb + shMetaOff < heap1 := by
    have : shMetaOff < selectHeapSize sg.loc.cap sg.loc.d sg.loc.Lk := by
      unfold shMetaOff selectHeapSize shHdrSize; omega
    have hEnd := sg.loc.endAddr_eq
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw13 : shMetaOff < 2 ^ w := by unfold shMetaOff; omega
  have hMetaFr2 : ∀ m', (∀ a < heap2, (a < sg.loc.hb ∨ sg.loc.endAddr ≤ a) → m' a = out2.mem a) →
      SelectLevelMetaAt m' (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast)
        4 P C' model'.chain.g model'.chain.ℓ (Function.update sg.φ d φd')
        (fun j => C'.chainLen model'.chain.ℓ (j + 1)) := fun m' hm' => by
    have hAgFootM : ∀ a, Rrep.foot root tok' a → m' a = out2.mem a := fun a ha =>
      hm' a (lt_of_lt_of_le (hBelow1 a (Or.inl ha)) h2Lo) (by
        by_contra hc; push Not at hc
        exact hoff1 a (by omega) (by omega) ha)
    have hCapsM : SolverLevelCapsInv P V vCap eCap model' tok' m' :=
      hCaps2.preserve rfl hCaps2.1.2.1
        (fun a ha => ⟨rfl, hAgFootM a (LevelMetaFoot.mem_foot hRep2 ha)⟩)
        (fun j hj => (SolverLevelMetaAt.atCaps hCaps2.1 hCaps2.2 j hj).2.2.1)
        rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have htabM : SelectMetaTableAt m' (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast) :=
      htab2.of_agree fun a h1 h2 => by
        simp only [selectMlocOf, hBd'] at h1 h2
        exact hm' a (by omega) (Or.inr (by omega))
    have hblkM : SelectBlocksAt m' B P C' model'.chain.g model'.chain.ℓ (Function.update sg.φ d φd') pLast :=
      hblk2.of_agree fun a h1 h2 => hm' a (by omega) (Or.inr (by omega))
    have hGMeq : ∀ j < d, solverLevelG tok' m' j = solverLevelG tok' out1.mem j := fun j hj => by
      have htag : tok'.tag (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
        have := hCaps2.1.2.2.2.2.1 (cfg.P.d + j) (by omega); simpa [Nat.add_assoc] using this
      exact (hAgFootM _ (LevelMetaFoot.mem_foot hRep2 (Or.inr (Or.inr (Or.inl htag))))).trans (hG2eq j hj)
    have hmlocM : selectMlocOf B sg.loc.metaPtr (solverLevelG tok' m') pLast =
        selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast := by
      unfold selectMlocOf; congr 1
      · funext j; split_ifs with h
        · exact hGMeq j (by rw [← hBd']; exact h)
        · rfl
      · funext j; split_ifs with h1 h2
        · exact hGMeq (j + 1) (by rw [← hBd']; exact h1)
        · rfl
        · rfl
    rw [← hmlocM]
    exact selectLevelMetaAt_of_solver hBd hBv hBe (hmlocM.symm ▸ htabM) hblkM hCapsM hMod' hpot2
  have hRebH1 : MeetsContract w p rebuildHeapLvlProc
      (selectRebuildLevelNoRoomContract w 4 P sg.loc
        (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast) C'
        model'.chain.g model'.chain.ℓ (Function.update sg.φ d φd')
        (fun j => C'.chainLen model'.chain.ℓ (j + 1)) evalSpace evalCost) := by
    rw [hmloc1Eq, hmloc]
    exact hRebHeap (Function.update sg.φ d φd')
  have hRunFull : ∃ o stFin cost,
      Runs w p ω (shiftTermSelectBody shiftTermChainProc rebuildLevelDProc rebuildHeapLvlProc)
        (startState [root, heap] mem pos) o stFin cost ∧
      (∃ nextHeap sg',
        o = .returned nextHeap ∧
        heap ≤ nextHeap ∧ heap1 ≤ nextHeap ∧
        nextHeap ≤ heap + (termSpace + termSelectSpace d nD mD sg.loc.cap L evalSpace) ∧
        Rrep.rep root model' tok' stFin.mem ∧
        SolverLevelCapsInv P V vCap eCap model' tok' stFin.mem ∧
        (SolverLevelLayoutAt vCap eCap tok mem0 → SolverLevelLayoutAt vCap eCap tok' stFin.mem) ∧
        SolverSelectBlocksInv G L P m vCap eCap pLast B model' (Rrep.foot root tok') tok' sg' stFin.mem ∧
        sg'.owned = sg.owned ∧ sg'.reembPot = sg.reembPot ∧ (∀ j < d, sg'.φ j = sg.φ j) ∧
        (∀ v ∈ newF.V, ∃ r ∈ newF.V, newF.Connected v r ∧ sg'.φ d v = walkInner (potGrad C' model'.chain.g sg.φ d) (newF.forestPath v r)) ∧
        OffTreeRecInv model' L stFin.mem tok'.edgeRecords B_num ∧ OffTreeRecBound model' L stFin.mem tok'.edgeRecords B_num ∧
        ZeroFrom stFin.mem nextHeap ∧ (∀ a < heap, ¬ Rrep.foot root tok a → ¬ sg.owned a → stFin.mem a = mem a) ∧
        Rrep.phi root tok' stFin.mem = Rrep.phi root tok' out1.mem) ∧
      cost ≤ c1 + c2 + selectRebuildLevelCost (levelCandCount out2.mem sg.loc d) (C'.G d).E.card
        sg.loc.cap sg.loc.Lk evalCost + 120 := by
    apply runs_start_le
    unfold shiftTermSelectBody
    refine runs_seq_assign_le (v := root) (by eval_expr) ?_
    refine runs_seq_rec_call hbTerm (vs := [root, heap]) (by eval_expr) (by wram_words) hRun1 ?_
    refine runs_seq_assign_le (v := tok'.handle) (by eval_expr) ?_
    refine runs_seq_assign_le (v := tok'.table) (by eval_expr) ?_
    refine runs_seq_assign_le (v := L) (by eval_expr) ?_
    refine runs_seq_assign_le (v := d) (by eval_expr) ?_
    refine runs_seq_assign_le (v := sg.loc.hb) (by eval_expr) ?_
    refine runs_seq_assign_le (v := sg.loc.metaPtr) (by eval_expr) ?_
    refine runs_seq_rec_call hpRebuildD (vs := [root, sg.loc.metaPtr, L, heap1])
      (by eval_expr) (by wram_words) hRunD ?_
    refine runs_seq_call_flat hRebH1 (vs := [sg.loc.hb, sg.loc.metaPtr, d, heap2])
      (by eval_expr) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl | rfl | rfl) <;> omega)
      ⟨d, heap2, sg.size, rfl, hw16, hpLastW, by omega, hreg.2.2.2.2.1.trans hBd,
        by simp [selectMlocOf, hreg.2.2.2.2.2.1], le_rfl,
        by intro e he; exact hGdCapHeap e (by change e ∈ (model'.chain.G d).E at he; rwa [hChG d] at he),
        hMatch2.1, hMeta2, hDisj2, hMetaFr2, hz2,
        by have := hSpHeapLe; unfold termSelectSpace at hRoom; omega⟩ ?_
    intro nextHeap mem3 pos3 hp3
    have hPost3 := hp3
    dsimp only [selectRebuildLevelNoRoomContract, selectRebuildLevelContract] at hp3
    obtain ⟨h3Lo, h3Hi, ⟨sz3, hat3, _⟩, ⟨_, hFr3⟩, hz3, _, _⟩ := hp3
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h3Lo h3Hi hFr3
    obtain ⟨sz3', hMatch3⟩ := selectRebuildLevelD_preserves_matchesChain (w := w) (evalCost := evalCost)
      hmod0'.1 hMod'.1 rfl (hreg.2.2.2.2.1.trans hBd)
      (fun j _ => hChG j) hC'LSF_lt hC'S_lt hC'Emb_lt
      (fun e => congrFun hChG_vec e) (fun e => congrFun hChL_vec e) hMatch2 hPost3
    refine WordRAM.runs_ret_le (v := nextHeap) (by eval_expr) ?_ ?_
    · have hAgFoot3 : ∀ a, Rrep.foot root tok' a → mem3 a = out2.mem a := fun a ha =>
        hFr3 a (lt_of_lt_of_le (hBelow1 a (Or.inl ha)) h2Lo) (by
          by_contra hc; push Not at hc
          exact hoff1 a (by omega) (by omega) ha)
      have hAgFoot31 : ∀ a, Rrep.foot root tok' a → mem3 a = out1.mem a := fun a ha =>
        (hAgFoot3 a ha).trans (hAgFoot2 a ha)
      have hRep3 : Rrep.rep root model' tok' mem3 :=
        (solverStateRep_local cfg L P m V psi k epsExp drainUnit hCoreLocal root model' tok'
          out1.mem mem3 (fun a ha => (hAgFoot31 a ha).symm)).1 hRep1
      have hPhiEq3 : Rrep.phi root tok' mem3 = Rrep.phi root tok' out1.mem :=
        (solverStateRep_local cfg L P m V psi k epsExp drainUnit hCoreLocal root model' tok'
          out1.mem mem3 (fun a ha => (hAgFoot31 a ha).symm)).2.symm
      have hCaps3 : SolverLevelCapsInv P V vCap eCap model' tok' mem3 :=
        hCaps2.preserve rfl hCaps2.1.2.1
          (fun a ha => ⟨rfl, hAgFoot3 a (LevelMetaFoot.mem_foot hRep2 ha)⟩)
          (fun j hj => (SolverLevelMetaAt.atCaps hCaps2.1 hCaps2.2 j hj).2.2.1)
          rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
      have hOff3 : OffTreeRecInv model' L mem3 tok'.edgeRecords B_num :=
        offTreeRecInv_of_agree hRep1 hOff1 fun a ha =>
          hAgFoot31 a (Or.inl (hTags1.1 a (by rcases ha with h | h <;> rw [h] <;> decide)))
      have hOffBd3 : OffTreeRecBound model' L mem3 tok'.edgeRecords B_num :=
        offTreeRecBound_of_agree hRep1 hOffBd1 fun a ha =>
          hAgFoot31 a (Or.inl (hTags1.1 a (by rcases ha with h | h <;> rw [h] <;> decide)))
      have hG3eq : ∀ j < d, solverLevelG tok' mem3 j = solverLevelG tok' out1.mem j := fun j hj => by
        have htag : tok'.tag (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
          have := hCaps1.1.2.2.2.2.1 (cfg.P.d + j) (by omega); simpa [Nat.add_assoc] using this
        exact hAgFoot31 _ (LevelMetaFoot.mem_foot hRep1 (Or.inr (Or.inr (Or.inl htag))))
      have hmloc3Eq : selectMlocOf B sg.loc.metaPtr (solverLevelG tok' mem3) pLast =
          selectMlocOf B sg.loc.metaPtr (solverLevelG tok' out1.mem) pLast := by
        unfold selectMlocOf; congr 1
        · funext j; split_ifs with h
          · exact hG3eq j (by rw [← hBd']; exact h)
          · rfl
        · funext j; split_ifs with h1 h2
          · exact hG3eq (j + 1) (by rw [← hBd']; exact h1)
          · rfl
          · rfl
      have htab3 : SelectMetaTableAt mem3 (selectMlocOf B sg.loc.metaPtr (solverLevelG tok' mem3) pLast) := by
        rw [hmloc3Eq]
        exact htab2.of_agree fun a h1 h2 => by
          simp only [selectMlocOf, hBd'] at h1 h2
          exact hFr3 a (by omega) (Or.inr (by omega))
      have hblk3 : SelectBlocksAt mem3 B P C' model'.chain.g model'.chain.ℓ
          (Function.update sg.φ d φd') pLast :=
        hblk2.of_agree fun a h1 h2 => hFr3 a (by omega) (Or.inr (by omega))
      let sg' : SelectGhost :=
        { sg with
          mloc := selectMlocOf B sg.loc.metaPtr (solverLevelG tok' mem3) pLast
          size := sz3'
          φ := Function.update sg.φ d φd'
          coreLen := fun j => C'.chainLen model'.chain.ℓ (j + 1) }
      have hSel3 : SolverSelectBlocksInv G L P m vCap eCap pLast B model' (Rrep.foot root tok')
          tok' sg' mem3 :=
        ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown,
          fun a ha => hoff1 a (by rw [hown] at ha; exact ha.1) (by rw [hown] at ha; exact ha.2),
          (hAgFoot31 _ (LevelMetaFoot.mem_foot hRep1 (Or.inr (Or.inl hCaps1.1.1.2.2.1)))).trans
            (by rw [solverSelectHeapAddr_eq_four_two]; exact hHbAddr1),
          (hAgFoot31 _ (LevelMetaFoot.mem_foot hRep1 (Or.inr (Or.inl hCaps1.1.1.2.2.2)))).trans hBlkAddr1,
          rfl, rfl, htab3, hblk3, hpot2, hMatch3, G₀', σ', σ'_mwu, γ'_ℓ, γ'_c, hMod'⟩
      refine ⟨nextHeap, sg', rfl, by omega, by omega,
        by have := hSpDLe; have := hSpHeapLe; unfold termSelectSpace; omega,
        hRep3, hCaps3, fun hL => hPres1.to_levelLayout_of_foot hCaps0.1 hRep1 hAgFoot31 hL, hSel3, rfl, rfl, fun j hj => Function.update_of_ne (by omega) _ _,
        by simpa [sg', Function.update_self, SelBlocksData.ofChain] using hFillD,
        hOff3, hOffBd3, hz3, fun a ha hnf hno => ?_, hPhiEq3⟩
      have hNotOwn : a < sg.loc.hb ∨ B.endAddr ≤ a := by
        rw [hown] at hno; omega
      have hFr3a : mem3 a = out2.mem a := hFr3 a (by omega) (by omega)
      have hFr2a : out2.mem a = out1.mem a := hFr2' a (by omega) (by omega)
      exact hFr3a.trans (hFr2a.trans (hFr1 a ha hnf))
    · simp only [selectRebuildLevelNoRoomContract, selectRebuildLevelContract,
        List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]; omega
  obtain ⟨o, stFin, cost, hRun, ⟨nextHeap, sg', rfl, hLo, h1LeN, hHi, hRep', hCaps', hLay', hSel', hOwn',
    hReemb', hPhiLt', hPhiD', hOff', hOffBd', hz', hFr', hPhiEq'⟩, hCost⟩ := hRunFull
  refine ⟨nextHeap, cost, stFin, tok', sg', hRun, hLo, hHi, hLevEq, hCapEq, hPres1.tableEq,
    hPres1.rootECapEq, hRep', hCaps', hLay', hSel', hSel'.toSolverSelectInv hCaps', hOwn', hReemb',
    hPhiLt', hPhiD', hNum1, hOff', hOffBd', hz', hFr',
    fun a ha => (hFoot1 a ha).imp id (fun ⟨h1, h2⟩ => ⟨h1, by omega⟩), ?_⟩
  change cost + Rrep.phi root tok' stFin.mem ≤
    termFixed + termSelectFixed d nD mD sg.loc.cap L evalCost +
      toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
      treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
      Rrep.phi root tok mem0
  rw [hPhiEq']
  unfold termSelectFixed
  have h1 : c1 + Rrep.phi root tok' out1.mem ≤
      termFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        Rrep.phi root tok mem0 := hCost1
  have h2 := hc2'; have h3 := hCostHeapLe
  omega

end MinCostFlow.MinRatio
