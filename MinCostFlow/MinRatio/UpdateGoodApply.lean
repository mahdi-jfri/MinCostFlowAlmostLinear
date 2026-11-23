module

public import MinCostFlow.MinRatio.UpdateGoodNormOut
public import MinCostFlow.MinRatio.UpdateGoodApplyPaths
public import MinCostFlow.MinRatio.UpdateGoodApplyOffTree
public import MinCostFlow.MinRatio.PathFlowUpdate
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
import WordRAM.Tactic

/-!
# Complete good-cycle output and flow application for `Update`

Combines `updateGoodNormOutBody` (rounded multiplier, `2L`-limb actual normalization,
`AnswerAt` header, and `PathTag` setup), `updateGoodApplyPathsBody` (tree-path `PathApply`
loop), and `updateGoodApplyOffTreeBody` (grouped explicit off-tree route update and
`offReadyList` push) into `updateGoodApplyBody`, and proves `updateGoodApplyBody_runs`
re-establishing `solverStateRep` and `PathTreeNumericInv` on the post-flow-routing
`Alg2State`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Total heap space above `workHeap` reserved by `updateGoodApplyBody`. -/
@[expose] def goodApplySpace (L pathsLen edgesLen : ℕ) : ℕ :=
  Num.fixedDivideSpace L + 8 * L + pathsLen * pathApplySpace L + explicitRouteSpace L edgesLen

/-- Fixed deterministic good-cycle application procedure taking
`[root, eta, magPtr, edgesBase, edgesLen, pathsBase, pathsLen, outHeap, workHeap]`. -/
@[expose] def updateGoodApplyBody (goodNormOut applyPaths applyOffTree : ℕ) : Stmt :=
  .assign 9 (.load (.reg 0)) ;;
  .assign 10 (.load (.bin .add (.reg 9) (.const 5))) ;;
  .assign 11 (.load (.bin .add (.reg 9) (.const 8))) ;;
  .call 12 goodNormOut [.reg 1, .reg 2, .reg 10, .reg 11, .reg 7, .reg 8] ;;
  .assign 13 (.bin .sub (.reg 12) (.bin .mul (.const 2) (.reg 10))) ;;
  .assign 14 (.bin .sub (.reg 12) (.bin .mul (.const 9) (.reg 10))) ;;
  .call 15 applyPaths [.reg 0, .reg 5, .reg 6, .reg 13, .reg 12] ;;
  .call 16 applyOffTree [.reg 0, .reg 3, .reg 4, .reg 14, .reg 10, .reg 15] ;;
  .ret (.reg 16)

theorem updateGoodApplyBody_noRand (goodNormOut applyPaths applyOffTree : ℕ) :
    (updateGoodApplyBody goodNormOut applyPaths applyOffTree).NoRand := by
  simp [updateGoodApplyBody, Stmt.NoRand]

private theorem listAt_congr_ga {mem mem' : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) :
    ListAt mem' base xs := fun j hj => (hag j hj).trans (h j hj)

/-- Re-establish `solverStateRep` after `updateGoodApplyBody` updates the path tree,
off-tree edge records, and `offReadyList`. -/
theorem solverStateRep_after_goodApply {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root workHeap h1 h2 cnt' : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} {s' : PathTreeState} {trees' : List AuxTree} {depth' : ℕ → ℕ}
    {treeTok' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {inc : ℕ → ℝ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < workHeap)
    (hworkLe : workHeap ≤ h1) (_hh12 : h1 ≤ h2)
    (hm11 : mem' (root + 11) = cnt')
    (hrootOther : ∀ j < 16, j ≠ 11 → mem' (root + j) = mem (root + j))
    (hoff' : OffReadyInv mem' cnt' tok.offReadyList tok.inOffReady tok.intCap)
    (hsn : s'.n = model.extG.n)
    (hlct' : LctInvWith pathPayload s' trees' tok.free depth')
    (htrep' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap s' treeTok' mem')
    (hftTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap treeTok' a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (h1 ≤ a ∧ a < h2))
    (hfrOther : ∀ a < workHeap, tok.tag a ≠ 0 → tok.tag a ≠ 1 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
      tok.tag a ≠ 16 → tok.tag a ≠ 18 → mem' a = mem a)
    (hacc' : SolverEdgeAccountsAt
      { model with
        flow := fun e => model.flow e + inc e
        detectAccum := fun e => model.detectAccum e + |inc e| }
      L P mem' tok.slots tok.names tok.slotThresholds tok.edgeThresholds tok.edgeRecords
      tok.inOffReady tok.intCap s' trees')
    (hns' : TreeEditNamedSlots s' trees' model.chain.toTreeChain.chainTree
      (fun f => mem' (tok.slots + f)) (fun k => mem' (tok.names + k)))
    (hgl' : SolverEdgeOrientInv L P model mem' tok.slots tok.edgeRecords s' trees') :
    let model' : Alg2State cfg :=
      { model with
        flow := fun e => model.flow e + inc e
        detectAccum := fun e => model.detectAccum e + |inc e| }
    let tok' : SolverToken cfg L Rcore :=
      { tok with
        offReadyCount := cnt'
        tree := s'
        trees := trees'
        depth := depth'
        treeTok := treeTok'
        owned := fun a => tok.owned a ∨ (h1 ≤ a ∧ a < h2)
        tag := fun a => if h1 ≤ a ∧ a < h2 then 16 else tok.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model' tok' mem' ∧
    (∀ i < cfg.P.d, Rcore.phi (tok'.coreHandle i) (tok'.coreTok i) mem' =
      Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem) := by
  dsimp only
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, _, htn, _, _, hedgeAcc, hcores, htermH, htermBr, htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hltOut {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < workHeap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hv14 : v ≠ 14)
      (hv15 : v ≠ 15) (hv16 : v ≠ 16) (hv18 : v ≠ 18) : mem' a = mem a :=
    hfrOther a (hltOut ht hv0) (fun h => hv0 (ht.symm.trans h)) (fun h => hv1 (ht.symm.trans h))
      (fun h => hv14 (ht.symm.trans h)) (fun h => hv15 (ht.symm.trans h))
      (fun h => hv16 (ht.symm.trans h)) (fun h => hv18 (ht.symm.trans h))
  have htagKeep {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) :
      (if h1 ≤ a ∧ a < h2 then 16 else tok.tag a) = v := by
    have := hltOut ht hv0
    rw [ite_eq_right (by omega), ht]
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ)
      (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) : mem a = mem' a :=
    (hagT (t21 i hi a ha) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a) : mem a = mem' a :=
    (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  refine ⟨⟨?_,
    listAt_congr_ga hdetect (fun j hj => hagT (t2 j (by simp [List.length] at hj; omega))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    listAt_congr_ga hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hagT (t2 (5 + j) (by simp [List.length] at hj; omega))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    listAt_congr_ga hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact hagT (t2 (9 + j) (by simp [List.length] at hj; omega))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hfreshInv,
    ⟨(hagT t6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfreshTab.1,
      fun e he => (hagT (t7 e he) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hfreshTab.2.1 e he),
      fun e he => (hagT (t8 e he) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hagT (t5 i.val (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsched.2.2.2.2⟩,
    hoff', hsn, hlct', htrep', hacc',
    fun i hi => by
      obtain ⟨hh, hbr, hcr⟩ := hcores i hi
      exact ⟨(hagT (t4 i (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh,
        by
          have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
          rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbr,
        (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem mem' (hcore_ag i hi)).1 hcr⟩,
    (hagT (t4 cfg.P.d (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans htermBr,
    (htermLocal tok.termHandle _ tok.termTok mem mem' hterm_ag).1 htermRep,
    ⟨fun j hj => (hagT (t3 j hj) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hwire.1 j hj),
     hwire.2.1.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
     hwire.2.2.1, hns', hgl'⟩,
    ?_⟩,
    fun i hi => (hlocalCore (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok.coreTok i) mem mem' (hcore_ag i hi)).2.symm⟩
  · intro j hj
    have hj16 : j < 16 := by simpa [List.length] using hj
    by_cases h11 : j = 11
    · subst h11; simpa using hm11
    · rw [hrootOther j hj16 h11]
      have h0 := hrootDir j hj
      interval_cases j <;> first | exact False.elim (h11 rfl) | simpa using h0
  · refine ⟨fun a ha => by
        dsimp only at ha
        by_cases hr : h1 ≤ a ∧ a < h2
        · exact Or.inr hr
        · rw [ite_eq_right hr] at ha; exact Or.inl (hOwn a ha),
      fun j hj => htagKeep (t1 j hj) (by decide), fun j hj => htagKeep (t2 j hj) (by decide),
      fun j hj => htagKeep (t3 j hj) (by decide), fun j hj => htagKeep (t4 j hj) (by decide),
      fun j hj => htagKeep (t5 j hj) (by decide), htagKeep t6 (by decide),
      fun j hj => htagKeep (t7 j hj) (by decide), fun j hj => htagKeep (t8 j hj) (by decide),
      fun j hj => htagKeep (t9 j hj) (by decide),
      fun j hj => htagKeep (t10 j (by dsimp only at hj; omega)) (by decide),
      fun j hj => htagKeep (t11 j (by dsimp only at hj; omega)) (by decide),
      fun j hj => htagKeep (t12 j hj) (by decide), fun j hj => htagKeep (t13 j hj) (by decide),
      fun j hj => htagKeep (t14 j hj) (by decide), fun j hj => htagKeep (t15 j hj) (by decide),
      fun a ha => by
        dsimp only
        rcases hftTree a ha with h0 | hr
        · exact htagKeep (t16 a h0) (by decide)
        · rw [ite_eq_left hr],
      fun e he => ⟨fun j hj => by
          rw [hagT (t12 _ (hedgeAcc.1 e he).1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact htagKeep ((t1718 e he).1 j hj) (by decide),
        fun hnot j hj => by
          rw [hagT (t13 _ (hedgeAcc.1 e he).1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact htagKeep ((t1718 e he).2 hnot j hj) (by decide)⟩,
      fun a ha => htagKeep (t19 a ha) (by decide),
      fun a h1 h2 => htagKeep (t20 a h1 h2) (by decide),
      fun i hi a ha => htagKeep (t21 i hi a ha) (by omega)⟩

/-- End-to-end execution of `updateGoodApplyBody`: writes the good-cycle output header at
`outHeap`, applies flow and detector updates across `paths` (in the path tree) and `edges`
(in off-tree records + `offReadyList`), and re-establishes `solverStateRep` and
`PathTreeNumericInv`. -/
theorem updateGoodApplyBody_runs
    {w L P m V psi k epsExp drainUnit initTree goodNormOut applyPaths applyOffTree
      pathNorm copyWords pathFlowTag explicitRouteUpdate offTreePush isNeg
      root eta magPtr edgesBase pathsBase outHeap workHeap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {request magnitude : ℤ} {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    {address : ℕ → ℕ} {old : ℕ → PathEdgeValue} {inc : ℕ → ℝ} {B R : ℤ}
    (hfmt4 : fmt.limbBits = 4)
    (hGoodNorm : p.procs[goodNormOut]? = some (updateGoodNormOutBody pathNorm copyWords pathFlowTag))
    (hApplyPaths : p.procs[applyPaths]? = some (updateGoodApplyPathsBody (opTree 2)))
    (hApplyOff : p.procs[applyOffTree]? = some (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush))
    (hNorm : MeetsContract w p pathNorm (pathNormalizationContract w 4 request magnitude))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hTag : MeetsContract w p pathFlowTag (pathFlowTagContract w 4 (pathMultiplier P request magnitude)))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hRoute : ∀ dst,
      (workHeap + Num.fixedDivideSpace L - L) + L ≤ dst →
      dst + edges.length + 2 < 2 ^ w →
      (∀ e ∈ edges.map Prod.fst, e < 2 ^ w) →
      (∀ e ∈ edges.map Prod.fst, address e + 2 + 4 * L ≤ min edgesBase (min dst (workHeap + Num.fixedDivideSpace L - L))) →
      MeetsContract w p explicitRouteUpdate
        (explicitEdgeRouteUpdateContract w 4 L edgesBase tok.edgeRecords dst
          (workHeap + Num.fixedDivideSpace L - L) edges address old (pathMultiplier P request magnitude)))
    (hPush : p.procs[offTreePush]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < workHeap ∧ (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a))
    (hP4 : 4 ∣ P) (hPW : P < 2 ^ w) (hw13 : 13 < 2 ^ w) (hLW : L < 2 ^ w)
    (hcapPos : 0 < tok.intCap) (h2nW : 2 * tok.tree.n + 1 < 2 ^ w)
    (hlogW : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * L)
    (hmagPos : 0 < magnitude)
    (hstep : (2 : ℝ) * ((magnitude : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ))
    (hetaEnd : eta + L ≤ workHeap) (hmagEnd : magPtr + L ≤ workHeap)
    (hedgesEnd : edgesBase + 2 * edges.length ≤ workHeap)
    (hpathsEnd : pathsBase + 2 * paths.length ≤ workHeap)
    (houtEnd : outHeap + 1 + 2 * L ≤ workHeap)
    (htEdges : ∀ x < 2 * edges.length, tok.tag (edgesBase + x) = 0 ∧
      (edgesBase + x < outHeap ∨ outHeap + 1 + 2 * L ≤ edgesBase + x))
    (htPaths : ∀ x < 2 * paths.length, tok.tag (pathsBase + x) = 0 ∧
      (pathsBase + x < outHeap ∨ outHeap + 1 + 2 * L ≤ pathsBase + x))
    (hetaAt : PathIntAt mem eta 4 L request)
    (hmagAt : PathIntAt mem magPtr 4 L magnitude)
    (hedgesAt : ExplicitEdgesAt mem edgesBase edges)
    (hpathsAt : PathEndpointsAt mem pathsBase paths)
    (hfitMult : Num.Fits 4 L (pathMultiplier P request magnitude))
    (hfitAbs : Num.Fits 4 L |pathMultiplier P request magnitude|)
    (hconn : ∀ q ∈ paths, q.1 < tok.tree.n ∧ q.2 < tok.tree.n ∧
      pathTreeConnected tok.tree (q.1 + 1) (q.2 + 1))
    (haddr : ∀ ei ∈ edges.map Prod.fst, ei < tok.intCap ∧
      mem (tok.edgeRecords + ei) = address ei ∧
      PathEdgeAt mem (address ei) 4 L (some (old ei)) ∧
      (∀ x < 2 + 4 * L, tok.tag (address ei + x) = 18) ∧
      address ei + 2 + 4 * L ≤ edgesBase)
    (hcapTree : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) *
      ((B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow (pathMultiplier P request magnitude))) +
        (R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow (pathMultiplier P request magnitude)))) <
      (Num.capacity 4 L : ℤ))
    (hz : ZeroFrom mem workHeap)
    (hroom : workHeap + goodApplySpace L paths.length edges.length + 2 < 2 ^ w)
    (haccBridge : ∀ (mem' : ℕ → ℕ) (trees' : List AuxTree) (depth' : ℕ → ℕ),
      let s' := applyPathsFold tok.tree (PathTag.ofFlow (pathMultiplier P request magnitude)) paths
      LctInvWith pathPayload s' trees' tok.free depth' →
      (∀ ei ∈ edges.map Prod.fst,
        PathEdgeAt mem' (address ei) 4 L (some (updatedOffTreeVal edges old (pathMultiplier P request magnitude) ei)) ∧
        (0 ≤ (updatedOffTreeVal edges old (pathMultiplier P request magnitude) ei).detector →
          mem' (tok.inOffReady + ei) = 1)) →
      (∀ a < workHeap, (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a) →
        (∀ ei ∈ edges.map Prod.fst, a < address ei + 2 + 2 * L ∨ address ei + 2 + 4 * L ≤ a) →
        tok.tag a ≠ 1 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → mem' a = mem a) →
      (∀ j < tok.intCap, mem (tok.inOffReady + j) = 1 → mem' (tok.inOffReady + j) = 1) →
      (∀ j < tok.intCap, j ∉ edges.map Prod.fst → mem' (tok.inOffReady + j) = mem (tok.inOffReady + j)) →
      SolverEdgeAccountsAt
        { model with
          flow := fun e => model.flow e + inc e
          detectAccum := fun e => model.detectAccum e + |inc e| }
        L P mem' tok.slots tok.names tok.slotThresholds tok.edgeThresholds tok.edgeRecords
        tok.inOffReady tok.intCap s' trees' ∧
      TreeEditNamedSlots s' trees' model.chain.toTreeChain.chainTree
        (fun f => mem' (tok.slots + f)) (fun k => mem' (tok.names + k)) ∧
      SolverEdgeOrientInv L P model mem' tok.slots tok.edgeRecords s' trees') :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let mult := pathMultiplier P request magnitude
    let req := (request : ℝ) / (2 : ℝ) ^ P
    let inner := ((-magnitude : ℤ) : ℝ) / (2 : ℝ) ^ P
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * inner)
    let model' : Alg2State cfg :=
      { model with
        flow := fun e => model.flow e + inc e
        detectAccum := fun e => model.detectAccum e + |inc e| }
    ∃ ret cost out tok',
      Runs w p ω (updateGoodApplyBody goodNormOut applyPaths applyOffTree)
        (startState [root, eta, magPtr, edgesBase, edges.length, pathsBase, paths.length, outHeap, workHeap] mem pos)
        (.returned ret) out cost ∧
      out.mem outHeap = 1 ∧
      ScalarAt out.mem (outHeap + 1) 4 (2 * L) (2 * P) actual ∧
      NormalizationWithin req actual ∧
      Rrep.rep root model' tok' out.mem ∧
      PreservesLevelMeta tok tok' mem out.mem ∧
      tok'.intCap = tok.intCap ∧
      PathTreeNumericInv tok'.tree tok'.trees
        (B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult))
        (R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult)) ∧
      ZeroFrom out.mem ret ∧ workHeap ≤ ret ∧
      ret ≤ workHeap + goodApplySpace L paths.length edges.length ∧
      (∀ a < workHeap, (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a) → ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < ret)) ∧
      cost + Rrep.phi root tok' out.mem ≤
        2852 * L ^ 2 + 3109 * L +
        paths.length * (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 45) +
        edges.length * (136 * edges.length + 152 * L ^ 2 + 561 * L + drainUnit + 960) + 1200 +
        Rrep.phi root tok mem ∧
      tok'.edgeRecords = tok.edgeRecords ∧
      (∀ j < tok.intCap, out.mem (tok.edgeRecords + j) = mem (tok.edgeRecords + j)) := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let mult := pathMultiplier P request magnitude
  let tag := PathTag.ofFlow mult
  let h1 := workHeap + Num.fixedDivideSpace L + 8 * L
  let tagPtr := workHeap + Num.fixedDivideSpace L + 6 * L
  let multPtr := workHeap + Num.fixedDivideSpace L - L
  have hrep0 := hrep
  obtain ⟨hrootDir, _, hnumH, _, _, _, _, _, _, hoffReady0, htn, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, _, _, _, _, _, _, t13, t14, t15, t16, _⟩ := htags
  have hltWork {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) :
      a < workHeap ∧ (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a) :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hdivSp : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
  have hworkW : workHeap < 2 ^ w := by dsimp only [goodApplySpace] at hroom; omega
  have houtW : outHeap < 2 ^ w := by omega
  have hhandleW : tok.handle < 2 ^ w := lt_trans (hltWork (t2 0 (by omega)) (by decide)).1 hworkW
  have hh5W : tok.handle + 5 < 2 ^ w := lt_trans (hltWork (t2 5 (by omega)) (by decide)).1 hworkW
  have hh8W : tok.handle + 8 < 2 ^ w := lt_trans (hltWork (t2 8 (by omega)) (by decide)).1 hworkW
  have hm0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hmL : mem (tok.handle + 5) = L := by simpa using hnumH 0 (by simp)
  have hmP : mem (tok.handle + 8) = P := by
    have h3 := hnumH 3 (by simp)
    simpa [show tok.handle + 5 + 3 = tok.handle + 8 by omega] using h3
  let s0 := startState [root, eta, magPtr, edgesBase, edges.length, pathsBase, paths.length, outHeap, workHeap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 9 tok.handle }
  let s2 : State := { s1 with regs := Function.update s1.regs 10 L }
  let s3 : State := { s2 with regs := Function.update s2.regs 11 P }
  have r1 : Runs w p ω (.assign 9 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s0, startState, hm0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 5)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s1, s0, startState, show 5 < 2 ^ w by omega, hh5W, hmL], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 9) (.const 8)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨P, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 8 < 2 ^ w by omega, hh8W, hmP], rfl, rfl, rfl⟩
  -- Phase 1: `goodNormOut`
  obtain ⟨cN, stN, hrN, hcN, hout1N, houtScN, hnormWithin, hmultAtN, htagAtN, hzN, hfrN⟩ :=
    updateGoodNormOutBody_runs (w := w) (ω := ω) (pos := s3.pos) hNorm hCopy hTag hP4 hPW
      (by omega) hmagPos hstep (by omega) (by omega) houtEnd hetaAt hmagAt hfitMult hfitAbs hz
      (by dsimp only [goodApplySpace] at hroom; omega)
  let s4 : State := { regs := Function.update s3.regs 12 h1, mem := stN.mem, pos := stN.pos }
  have r4 : Runs w p ω (.call 12 goodNormOut [.reg 1, .reg 2, .reg 10, .reg 11, .reg 7, .reg 8])
      s3 .normal s4 (cN + 7) :=
    runs_call_iff.mpr ⟨[eta, magPtr, L, P, outHeap, workHeap],
      updateGoodNormOutBody pathNorm copyWords pathFlowTag, .returned h1, stN, cN,
      by simp [evalArgs, Expr.eval, s3, s2, s1, s0, startState], hGoodNorm, hrN, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have h1W : h1 < 2 ^ w := by dsimp only [h1, goodApplySpace] at hroom ⊢; omega
  have h9LW : 9 * L < 2 ^ w := by
    have : L ≤ Num.fixedDivideSpace L := hdivSp; dsimp only [goodApplySpace] at hroom; omega
  let s5 : State := { s4 with regs := Function.update s4.regs 13 tagPtr }
  let s6 : State := { s5 with regs := Function.update s5.regs 14 multPtr }
  have r5 : Runs w p ω (.assign 13 (.bin .sub (.reg 12) (.bin .mul (.const 2) (.reg 10)))) s4 .normal s5 6 :=
    runs_assign_iff.mpr ⟨tagPtr, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, show 2 < 2 ^ w by omega, show 2 * L < 2 ^ w by omega,
        show h1 - 2 * L = tagPtr by dsimp only [h1, tagPtr]; omega,
        show tagPtr < 2 ^ w by dsimp only [tagPtr, goodApplySpace] at hroom ⊢; omega], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 14 (.bin .sub (.reg 12) (.bin .mul (.const 9) (.reg 10)))) s5 .normal s6 6 :=
    runs_assign_iff.mpr ⟨multPtr, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, show 9 < 2 ^ w by omega, h9LW,
        show h1 - 9 * L = multPtr by dsimp only [h1, multPtr]; omega,
        show multPtr < 2 ^ w by dsimp only [multPtr, goodApplySpace] at hroom ⊢; omega], rfl, rfl, rfl⟩
  -- Transfer `solverStateRep` to `s6.mem = stN.mem`
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hagFootN (a : ℕ) (ha : Rrep.foot root tok a) : mem a = s6.mem a :=
    (hfrN a (hbelow a ha).1 (hbelow a ha).2).symm
  have hrepN : Rrep.rep root model tok s6.mem := (hlocR root model tok mem s6.mem hagFootN).1 hrep0
  have hphiN : Rrep.phi root tok s6.mem = Rrep.phi root tok mem := ((hlocR root model tok mem s6.mem hagFootN).2).symm
  have htreePhiN : Rtree.phi tok.treeHeap tok.treeTok s6.mem = Rtree.phi tok.treeHeap tok.treeTok mem :=
    ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap tok.tree tok.treeTok mem s6.mem
      (fun a ha => hagFootN a (Or.inr (Or.inl ha)))).2.symm
  have hpathsAtN : PathEndpointsAt s6.mem pathsBase paths := fun j hj => by
    have h1j := hfrN (pathsBase + 2 * j) (by omega) (htPaths _ (by omega)).2
    have h2j := hfrN (pathsBase + 2 * j + 1) (by omega)
      (by rw [show pathsBase + 2 * j + 1 = pathsBase + (2 * j + 1) by omega]; exact (htPaths _ (by omega)).2)
    exact ⟨h1j.trans (hpathsAt j hj).1, h2j.trans (hpathsAt j hj).2⟩
  -- Phase 2: `applyPaths`
  obtain ⟨h2, cP, stP, trees', depth', treeTok', hrP, hh2Lo, hh2Hi, hW', hnum', htrepP, hzP, hfrP, hftP, hcP⟩ :=
    updateGoodApplyPathsBody_runs (w := w) (ω := ω) (pos := s6.pos) hfmt4 hTreeImpl hrepN hnum
      (fun a ha => lt_of_lt_of_le (hbelow a ha).1 (by omega))
      (by omega) (by omega)
      (fun a ha => ⟨by
          by_contra h; push Not at h
          have h16 := t16 a ha
          have h0 := (htPaths (a - pathsBase) (by omega)).1
          rw [show pathsBase + (a - pathsBase) = a by omega] at h0; omega,
        Or.inl (lt_of_lt_of_le (hbelow a (Or.inr (Or.inl ha))).1 (by omega))⟩)
      hpathsAtN htagAtN hconn hzN (by omega) h2nW hlogW hcapTree
      (by dsimp only [goodApplySpace] at hroom; omega)
  let s7 : State := { regs := Function.update s6.regs 15 h2, mem := stP.mem, pos := stP.pos }
  have r7 : Runs w p ω (.call 15 applyPaths [.reg 0, .reg 5, .reg 6, .reg 13, .reg 12])
      s6 .normal s7 (cP + 6) :=
    runs_call_iff.mpr ⟨[root, pathsBase, paths.length, tagPtr, h1],
      updateGoodApplyPathsBody (opTree 2), .returned h2, stP, cP,
      by simp [evalArgs, Expr.eval, s6, s5, s4, s3, s2, s1, s0, startState], hApplyPaths, hrP, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  -- Transfer non-tree regions to `s7.mem = stP.mem`
  let s' := applyPathsFold tok.tree tag paths
  have hsn' : s'.n = model.extG.n := by
    have hfn : ∀ (ps : List (ℕ × ℕ)) (t : PathTreeState), (applyPathsFold t tag ps).n = t.n := by
      intro ps; induction ps with
      | nil => intro t; rfl
      | cons _ rest ih => intro t; exact ih _
    exact (hfn paths tok.tree).trans htn
  have hfrP_below (a : ℕ) (ha : a < workHeap) (hdisj : a < outHeap ∨ outHeap + 1 + 2 * L ≤ a)
      (h16 : tok.tag a ≠ 16) : s7.mem a = mem a :=
    (hfrP a (lt_of_lt_of_le ha (by omega)) (fun ht => h16 (t16 a ht))).trans
      (hfrN a ha hdisj)
  have hedgesAtP : ExplicitEdgesAt s7.mem edgesBase edges := hedgesAt.congr fun x hx1 hx2 => by
    have htx := htEdges (x - edgesBase) (by omega)
    rw [show edgesBase + (x - edgesBase) = x by omega] at htx
    exact (hfrP x (by omega) (fun ht => by have h16 := t16 x ht; omega)).trans
      (hfrN x (by omega) htx.2)
  have hmultAtP : PathIntAt s7.mem multPtr 4 L mult :=
    hmultAtN.congr (fun i hi => hfrP (multPtr + i) (by dsimp only [multPtr]; omega)
      (fun ht => by have := (hbelow (multPtr + i) (Or.inr (Or.inl ht))).1; dsimp only [multPtr] at this; omega))
  -- Phase 3: `applyOffTree` at `s7.mem = stP.mem` using tag map `tagP` (tagging `[h1, h2)` as `16`)
  let tagP : ℕ → ℕ := fun a => if h1 ≤ a ∧ a < h2 then 16 else tok.tag a
  have htagP_keep {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : tagP a = v := by
    have := (hltWork ht hv).1; dsimp only [tagP]; rw [ite_eq_right (by dsimp only [h1]; omega), ht]
  have hltH2 {a v : ℕ} (ht : tagP a = v) (hv : v ≠ 0) : a < h2 := by
    dsimp only [tagP] at ht
    by_cases hr : h1 ≤ a ∧ a < h2
    · exact hr.2
    · rw [ite_eq_right hr] at ht; exact lt_of_lt_of_le (hltWork ht hv).1 (by omega)
  have hrootDirP : SolverRootDirAt s7.mem root tok.handle tok.table tok.levelsEnd tok.forward
      tok.inverse tok.freshCounter tok.slots tok.names tok.slotThresholds tok.edgeThresholds
      tok.edgeRecords tok.offReadyCount tok.offReadyList tok.inOffReady tok.rootGraph tok.intCap :=
    listAt_congr_ga hrootDir fun j hj =>
      have hw := hltWork (t1 j (by simpa [List.length] using hj)) (by decide)
      hfrP_below (root + j) hw.1 hw.2 (by rw [t1 j (by simpa [List.length] using hj)]; decide)
  have hoffP : OffReadyInv s7.mem tok.offReadyCount tok.offReadyList tok.inOffReady tok.intCap := by
    obtain ⟨hA, hB, hC, hD, hE⟩ := hoffReady0
    have hol (j : ℕ) (hj : j < tok.intCap) : s7.mem (tok.offReadyList + j) = mem (tok.offReadyList + j) :=
      have hw := hltWork (t14 j hj) (by decide)
      hfrP_below _ hw.1 hw.2 (by rw [t14 j hj]; decide)
    have hio (j : ℕ) (hj : j < tok.intCap) : s7.mem (tok.inOffReady + j) = mem (tok.inOffReady + j) :=
      have hw := hltWork (t15 j hj) (by decide)
      hfrP_below _ hw.1 hw.2 (by rw [t15 j hj]; decide)
    refine ⟨hA, fun j hj => by rw [hol j (lt_of_lt_of_le hj hA), hio _ (hB j hj).1]; exact hB j hj,
      fun j₁ hj₁ j₂ hj₂ hne => by
        rw [hol j₁ (lt_of_lt_of_le hj₁ hA), hol j₂ (lt_of_lt_of_le hj₂ hA)]; exact hC j₁ hj₁ j₂ hj₂ hne,
      fun j hj => by rw [hio j hj]; exact hD j hj,
      fun j hj h1' => by
        rw [hio j hj] at h1'
        obtain ⟨x, hx, hxe⟩ := hE j hj h1'
        exact ⟨x, hx, (hol x (lt_of_lt_of_le hx hA)).trans hxe⟩⟩
  have haddrP : ∀ ei ∈ edges.map Prod.fst, ei < tok.intCap ∧
      s7.mem (tok.edgeRecords + ei) = address ei ∧
      PathEdgeAt s7.mem (address ei) 4 L (some (old ei)) ∧
      (∀ x < 2 + 4 * L, tagP (address ei + x) = 18) := fun ei hei => by
    obtain ⟨h1e, h2e, h3e, h4e, _⟩ := haddr ei hei
    have hw13' := hltWork (t13 ei h1e) (by decide)
    refine ⟨h1e, (hfrP_below _ hw13'.1 hw13'.2 (by rw [t13 ei h1e]; decide)).trans h2e,
      h3e.congr (fun a ha1 ha2 => by
        have ht18a : tok.tag a = 18 := by rw [show a = address ei + (a - address ei) by omega]; exact h4e _ (by omega)
        have hw18 := hltWork ht18a (by decide)
        exact hfrP_below a hw18.1 hw18.2 (by rw [ht18a]; decide)),
      fun x hx => htagP_keep (h4e x hx) (by decide)⟩
  have hRouteH2 : MeetsContract w p explicitRouteUpdate
      (explicitEdgeRouteUpdateContract w 4 L edgesBase tok.edgeRecords h2 multPtr edges address old mult) :=
    hRoute h2 (by
        have hdivL : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
        omega)
      (by dsimp only [goodApplySpace, explicitRouteSpace] at hroom; omega)
      (fun ei hei => by
        obtain ⟨h1e, _⟩ := haddr ei hei
        have := (hltWork (t13 ei h1e) (by decide)).1; omega)
      (fun ei hei => by
        obtain ⟨_, _, _, h4e, hbe⟩ := haddr ei hei
        have hlast := (hltWork (h4e (2 + 4 * L - 1) (by omega)) (by decide)).1
        have hdivL : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
        omega)
  obtain ⟨h3, cO, stO, cnt', hrO, hh3Lo, hh3Hi, hcntLo, hcntHi, hm11', hoff', hupdOff, hzO,
      hfrO_no18, hfrO_out, hrootOtherO, hioMonoO, hioPresO, hcO⟩ :=
    updateGoodApplyOffTreeBody_runs (w := w) (ω := ω) (pos := s7.pos) (drainUnit := drainUnit)
      tagP hRouteH2 hPush hIsNeg hrootDirP hoffP hltH2
      (fun j hj => htagP_keep (t1 j hj) (by decide))
      (fun j hj => htagP_keep (t13 j hj) (by decide))
      (fun j hj => htagP_keep (t14 j hj) (by decide))
      (fun j hj => htagP_keep (t15 j hj) (by decide))
      (by omega) (by omega)
      (fun x hx => by
        dsimp only [tagP]
        rw [ite_eq_right (by dsimp only [h1]; omega), (htEdges x hx).1])
      hedgesAtP hmultAtP haddrP hzP hcapPos hw13 hLW
      (by dsimp only [goodApplySpace] at hroom; omega)
  let out : State := { regs := Function.update s7.regs 16 h3, mem := stO.mem, pos := stO.pos }
  have r8 : Runs w p ω (.call 16 applyOffTree [.reg 0, .reg 3, .reg 4, .reg 14, .reg 10, .reg 15])
      s7 .normal out (cO + 7) :=
    runs_call_iff.mpr ⟨[root, edgesBase, edges.length, multPtr, L, h2],
      updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush, .returned h3, stO, cO,
      by simp [evalArgs, Expr.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState], hApplyOff, hrO, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have r9 : Runs w p ω (.ret (.reg 16)) out (.returned h3) out 2 :=
    runs_ret_iff.mpr ⟨h3, by simp [Expr.eval, out], rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (updateGoodApplyBody goodNormOut applyPaths applyOffTree) s0 (.returned h3) out
      (3 + (5 + (5 + ((cN + 7) + (6 + (6 + ((cP + 6) + ((cO + 7) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, cN + 7, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 6, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, cP + 6, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨out, cO + 7, 2, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Verify outputs at `outHeap` survive Phases 2 & 3 (tagged 0)
  have houtTag0 (a : ℕ) (ha1 : outHeap ≤ a) (ha2 : a < outHeap + 1 + 2 * L) :
      tok.tag a = 0 ∧ tagP a = 0 := by
    have h0 : tok.tag a = 0 := by
      by_contra hnz; have := (hltWork rfl hnz).2; omega
    exact ⟨h0, by dsimp only [tagP]; rw [ite_eq_right (by dsimp only [h1]; omega), h0]⟩
  have houtPres (a : ℕ) (ha1 : outHeap ≤ a) (ha2 : a < outHeap + 1 + 2 * L) :
      out.mem a = stN.mem a := by
    have ⟨h0, h0P⟩ := houtTag0 a ha1 ha2
    have h1o := hfrO_no18 a (by omega)
      (by rw [h0P]; decide) (by rw [h0P]; decide) (by rw [h0P]; decide) (by rw [h0P]; decide)
    have h2p := hfrP a (by omega) (fun ht => by have := t16 a ht; omega)
    exact h1o.trans h2p
  have hout1 : out.mem outHeap = 1 := (houtPres outHeap le_rfl (by omega)).trans hout1N
  have houtScalar : ScalarAt out.mem (outHeap + 1) 4 (2 * L) (2 * P)
      (-(((mult : ℝ) / (2 : ℝ) ^ P) * (((-magnitude : ℤ) : ℝ) / (2 : ℝ) ^ P))) := by
    have hag : ∀ i < 2 * L, out.mem (outHeap + 1 + i) = stN.mem (outHeap + 1 + i) :=
      fun i hi => houtPres (outHeap + 1 + i) (by omega) (by omega)
    refine ⟨fun i hi => by rw [hag i hi]; exact houtScN.1 i hi, ?_⟩
    rw [Num.fixVal, Num.intVal, Num.unsignedVal_congr (fun i hi => hag i hi)]
    exact houtScN.2
  -- Transfer `Rtree.rep` and `Rtree.phi` across Phase 3 (all `Rtree.foot` cells have `tagP = 16`)
  have htree_agO (a : ℕ) (ha : Rtree.foot tok.treeHeap treeTok' a) : s7.mem a = out.mem a := by
    have h16P : tagP a = 16 := by
      rcases hftP a ha with h0 | hr
      · exact htagP_keep (t16 a h0) (by decide)
      · dsimp only [tagP]; rw [ite_eq_left hr]
    exact (hfrO_no18 a (hltH2 h16P (by decide))
      (by rw [h16P]; decide) (by rw [h16P]; decide) (by rw [h16P]; decide) (by rw [h16P]; decide)).symm
  have htrepO : Rtree.rep tok.treeHeap s' treeTok' out.mem :=
    ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap s' treeTok' s7.mem out.mem htree_agO).1 htrepP
  have htreePhiO : Rtree.phi tok.treeHeap treeTok' out.mem = Rtree.phi tok.treeHeap treeTok' s7.mem :=
    ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap s' treeTok' s7.mem out.mem htree_agO).2.symm
  -- Frame facts for `solverStateRep_after_goodApply` and `haccBridge`
  have hfrOut_noOff (a : ℕ) (ha : a < workHeap) (hdisj : a < outHeap ∨ outHeap + 1 + 2 * L ≤ a)
      (hnotOff : ∀ ei ∈ edges.map Prod.fst, a < address ei + 2 + 2 * L ∨ address ei + 2 + 4 * L ≤ a)
      (h1t : tok.tag a ≠ 1) (h14t : tok.tag a ≠ 14) (h15t : tok.tag a ≠ 15) (h16t : tok.tag a ≠ 16) :
      out.mem a = mem a := by
    have htp : tagP a = tok.tag a := by dsimp only [tagP]; rw [ite_eq_right (by dsimp only [h1]; omega)]
    exact (hfrO_out a (by omega) hnotOff (by rw [htp]; exact h1t)
      (by rw [htp]; exact h14t) (by rw [htp]; exact h15t)).trans (hfrP_below a ha hdisj h16t)
  have hfrOther (a : ℕ) (ha : a < workHeap) (hdisj : a < outHeap ∨ outHeap + 1 + 2 * L ≤ a)
      (h1t : tok.tag a ≠ 1) (h14t : tok.tag a ≠ 14) (h15t : tok.tag a ≠ 15)
      (h16t : tok.tag a ≠ 16) (h18t : tok.tag a ≠ 18) : out.mem a = mem a := by
    have htp : tagP a = tok.tag a := by dsimp only [tagP]; rw [ite_eq_right (by dsimp only [h1]; omega)]
    exact (hfrO_no18 a (by omega) (by rw [htp]; exact h1t)
      (by rw [htp]; exact h14t) (by rw [htp]; exact h15t) (by rw [htp]; exact h18t)).trans
      (hfrP_below a ha hdisj h16t)
  obtain ⟨hacc', hns', hgl'⟩ := haccBridge out.mem trees' depth' hW' hupdOff hfrOut_noOff (fun j hj h1j =>
    have hw15 := hltWork (t15 j hj) (by decide)
    hioMonoO j hj ((hfrP_below _ hw15.1 hw15.2 (by rw [t15 j hj]; decide)).trans h1j))
    (fun j hj hnot =>
      have hw15 := hltWork (t15 j hj) (by decide)
      (hioPresO j hj hnot).trans (hfrP_below _ hw15.1 hw15.2 (by rw [t15 j hj]; decide)))
  obtain ⟨hrepFinal, hcorePhiFinal⟩ := solverStateRep_after_goodApply hlocalCore hrep0
    (fun a ha => (hbelow a ha).1) (by omega) hh2Lo hm11'
    (fun j hj hne11 =>
      have hw1 := hltWork (t1 j hj) (by decide)
      (hrootOtherO j hj hne11).trans (hfrP_below _ hw1.1 hw1.2 (by rw [t1 j hj]; decide)))
    hoff' hsn' hW' htrepO hftP
    (fun a ha h0t => hfrOther a ha (hbelow a (Or.inl (hOwn a h0t))).2) hacc' hns' hgl'
  have hPresMeta : PreservesLevelMeta tok
      { tok with
        offReadyCount := cnt'
        tree := s'
        trees := trees'
        depth := depth'
        treeTok := treeTok'
        owned := fun a => tok.owned a ∨ (h1 ≤ a ∧ a < h2)
        tag := fun a => if h1 ≤ a ∧ a < h2 then 16 else tok.tag a } mem out.mem := by
    refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, fun a ht => ?_⟩
    have hne : tok.tag a ≠ 0 ∧ tok.tag a ≠ 1 ∧ tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧
        tok.tag a ≠ 16 ∧ tok.tag a ≠ 18 := by
      rcases ht with h | h | h | h <;> rw [h] <;> exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hbw := hbelow a (Or.inl (hOwn a hne.1))
    exact ⟨by dsimp only; rw [ite_eq_right (by dsimp only [h1]; omega)],
      hfrOther a hbw.1 hbw.2 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2⟩
  -- Assemble final result
  refine ⟨h3, _, out, _, hrFull, hout1, houtScalar, hnormWithin, hrepFinal, hPresMeta, rfl, hnum', hzO,
    by omega, by dsimp only [goodApplySpace]; omega,
    ?_, ?_, ?_, rfl, fun j hj => ?_⟩
  rotate_right
  · have hw13 := hltWork (t13 j hj) (by decide)
    exact hfrOther _ hw13.1 hw13.2 (by rw [t13 j hj]; decide) (by rw [t13 j hj]; decide)
      (by rw [t13 j hj]; decide) (by rw [t13 j hj]; decide) (by rw [t13 j hj]; decide)
  · intro a ha hdisj hnf
    have hnotTag (v : ℕ) (hv : v ≠ 0) : tok.tag a ≠ v := fun ht => hnf (Or.inl (hOwn a (ht ▸ hv)))
    exact hfrOther a ha hdisj (hnotTag 1 (by decide)) (hnotTag 14 (by decide))
      (hnotTag 15 (by decide)) (hnotTag 16 (by decide)) (hnotTag 18 (by decide))
  · intro a ha
    rcases ha with (hown | htree | hcore)
    · rcases hown with h0 | ⟨ha1, ha2⟩
      · exact Or.inl (Or.inl h0)
      · exact Or.inr ⟨by omega, lt_of_lt_of_le ha2 (by omega)⟩
    · rcases hftP a htree with h0 | ⟨ha1, ha2⟩
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inr ⟨by omega, lt_of_lt_of_le ha2 (by omega)⟩
    · exact Or.inl (Or.inr (Or.inr hcore))
  · -- Amortized cost telescoping
    have hcoresSum : (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) out.mem) =
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) :=
      Finset.sum_congr rfl fun i _ => hcorePhiFinal i.val i.isLt
    change _ + (Rtree.phi tok.treeHeap treeTok' out.mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) out.mem) +
      cnt' * drainUnit) ≤
      2852 * L ^ 2 + 3109 * L +
      paths.length * (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 45) +
      edges.length * (136 * edges.length + 152 * L ^ 2 + 561 * L + drainUnit + 960) + 1200 +
      (Rtree.phi tok.treeHeap tok.treeTok mem +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) +
        tok.offReadyCount * drainUnit)
    rw [hcoresSum, htreePhiO]
    have hcP' : cP + Rtree.phi tok.treeHeap treeTok' s7.mem ≤
        paths.length * (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 45) + 30 +
        Rtree.phi tok.treeHeap tok.treeTok mem := by
      rw [← htreePhiN, ← htn]; exact hcP
    omega

end MinCostFlow.MinRatio
