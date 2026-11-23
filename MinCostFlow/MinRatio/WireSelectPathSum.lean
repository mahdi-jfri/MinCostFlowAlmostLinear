module

public import MinCostFlow.MinRatio.WireSelectRawProofs
public import MinCostFlow.MinRatio.UpdateGoodApply
public import MinCostFlow.MinRatio.PathApplyAccounting
public import MinCostFlow.MinRatio.PathNumericHistory
public import MinCostFlow.LinkCut.PathProg.Vals
import MinCostFlow.LinkCut.PathProg.WrapQuery
import MinCostFlow.LSF.Walks

/-!
# Link-cut `PathSummary` solver bridge (`lctPathSummary_model_step`, `solverStateRep_update_treeSummary`)

Connects `lctPathSummary pathPayload tok.tree (vid u) (vid v)` and machine operation `opTree 3`
(`pathTreeMachineContract`) to `solverStateRep`:
1. `lctPathSummary_model_step`: proves that `lctPathSummary` preserves `LctInvWith`,
   `PathTreeNumericInv`, `TreeEditNamedSlots`, `SolverEdgeAccountsAt`, and `SolverEdgeOrientInv`,
   and that its returned `sum.length` satisfies
   `(sum.length : ℝ) / 2^P = walkLength (fun ei => model.extℓ (model.intToExt ei)) (F.forestPath u v)`
   and `|sum.length| ≤ model.extG.n * B`.
2. `solverStateRep_update_treeSummary`: lifts one `opTree 3` run through
   `solverStateRep_after_goodApply` (with zero flow increment) to preserve `solverStateRep`,
   `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`, and `SelectHeapMatchesChain`,
   telescoping `Rrep.phi` against `pathTreeBudget`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LinkCut.PathProg LinkCut.PathTree

/-! ## 1. Pure length summary helpers -/

private theorem listSummary_length_eq_sum (ps : List (ℕ × Option PathEdgeValue)) :
    (pathPayload.listSummary ps).length =
      (ps.filterMap (fun p => p.2.map PathEdgeValue.length)).sum := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨k, v⟩
    rw [LctPayload.listSummary_cons]
    cases v with
    | none =>
      simpa [pathPayload, PathSummary.single, PathSummary.combine, PathSummary.empty] using ih
    | some val =>
      simpa [pathPayload, PathSummary.single, PathSummary.combine] using congrArg (val.length + ·) ih

private theorem walkVertices_length_eq (F : MGraph) (u : ℕ) (W : List (ℕ × Bool)) :
    (F.walkVertices u W).length = W.length + 1 := by
  induction W generalizing u with
  | nil => rfl
  | cons x rest _ => simp [MGraph.walkVertices]

private theorem forestPath_length_lt {F : MGraph} {n u v : ℕ}
    (hF : F.IsForest) (hV : ∀ e ∈ F.E, F.tail e < n ∧ F.head e < n)
    (hu : u < n) (hconn : F.Connected u v) :
    (F.forestPath u v).length < n := by
  have hpath := LSF.forestPath_isPath hF hconn
  have hnd : (F.walkVertices u (F.forestPath u v)).Nodup := hpath.2
  have hsub : (F.walkVertices u (F.forestPath u v)).toFinset ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range]
    rw [List.mem_toFinset] at hx
    simp only [MGraph.walkVertices, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨e, he, rfl⟩
    · exact hu
    · have heE := MGraph.isWalk_edges_mem hpath.1 e he
      cases he2 : e.2 <;> simp [MGraph.dst, he2, (hV e.1 heE).1, (hV e.1 heE).2]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range, List.toFinset_card_of_nodup hnd, walkVertices_length_eq] at hcard
  omega

private theorem mem_forestPairs_unique_val {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} (hnd : (trees.flatMap AuxTree.toList).Nodup)
    {k : ℕ} {v₁ v₂ : Option PathEdgeValue}
    (h1 : (k, v₁) ∈ forestPairs pathPayload s trees)
    (h2 : (k, v₂) ∈ forestPairs pathPayload s trees) :
    v₁ = v₂ := by
  have hndFst : ((forestPairs pathPayload s trees).map Prod.fst).Nodup :=
    (forestPairs_fst_perm s trees).nodup_iff.mpr hnd
  have hinj := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst hndFst)).mp hndFst
  exact (Prod.mk.inj (hinj (k, v₁) h1 (k, v₂) h2 rfl)).2

private theorem lctPathSummary_fst_eq_cost (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1 = (lctPathSummaryCost pathPayload s u v).1 := rfl

private theorem lctPathSummary_snd_eq_cost (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).2 = (lctPathSummaryCost pathPayload s u v).2.1 := rfl

private theorem lctPathSummary_fst_eq_expose (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1 = lctExpose pathPayload (lctReroot pathPayload s u) v := rfl

private theorem lctExpose_eq_cost (s : PathTreeState) (v : ℕ) :
    lctExpose pathPayload s v = (lctExposeCost pathPayload s v).1 := rfl

private theorem abs_list_sum_le {xs : List ℤ} {B : ℤ}
    (hb : ∀ z ∈ xs, |z| ≤ B) :
    |xs.sum| ≤ (xs.length : ℤ) * B := by
  induction xs with
  | nil => simp
  | cons z rest ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := hb z List.mem_cons_self
    have h2 := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    calc |z + rest.sum| ≤ |z| + |rest.sum| := abs_add_le z rest.sum
      _ ≤ B + (rest.length : ℤ) * B := add_le_add h1 h2
      _ = ((rest.length : ℤ) + 1) * B := by ring

/-! ## 2. Pure model step for `lctPathSummary` -/

/-- Pure `lctPathSummary` step on `tok.tree`: preserves `LctInvWith`, `PathTreeNumericInv`,
`TreeEditNamedSlots`, `SolverEdgeAccountsAt`, and `SolverEdgeOrientInv`, and proves that
`sum.length` equals the scaled `walkLength` of `F.forestPath u v` and is bounded in magnitude
by `model.extG.n * B`. -/
theorem lctPathSummary_model_step {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root u v : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} {B R : ℤ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hu : u < model.extG.n) (hv : v < model.extG.n)
    (hconn : model.chain.toTreeChain.chainTree.Connected u v) :
    let F := model.chain.toTreeChain.chainTree
    let res := lctPathSummary pathPayload tok.tree (vid u) (vid v)
    let s' := res.1
    let sum := res.2
    pathTreeConnected tok.tree (vid u) (vid v) ∧
    ∃ trees' depth',
      LctInvWith pathPayload s' trees' tok.free depth' ∧
      PathTreeNumericInv s' trees' B R ∧
      TreeEditNamedSlots s' trees' F (fun ei => mem (tok.slots + ei)) (fun sl => mem (tok.names + sl)) ∧
      SolverEdgeAccountsAt model L P mem tok.slots tok.names tok.slotThresholds
        tok.edgeThresholds tok.edgeRecords tok.inOffReady tok.intCap s' trees' ∧
      SolverEdgeOrientInv L P model mem tok.slots tok.edgeRecords s' trees' ∧
      (sum.length : ℝ) / (2 : ℝ) ^ P =
        walkLength (fun ei => model.extℓ (model.intToExt ei)) (F.forestPath u v) ∧
      |sum.length| ≤ (model.extG.n : ℤ) * B := by
  dsimp only
  set F := model.chain.toTreeChain.chainTree
  set slot := fun ei => mem (tok.slots + ei)
  set name := fun sl => mem (tok.names + sl)
  obtain ⟨_, _, _, _, hFresh, _, _, hIntB, _, _, htn, hlct, htreeRep, hedgeAcc, _, _, _, _, hWire, _⟩ := hrep
  obtain ⟨_, _, ⟨hF, hFEnds⟩, hns, hori⟩ := hWire
  have hVals : ValsOnEdges tok.tree := htreeRep.2.2.vals
  have hV : ∀ e ∈ F.E, F.tail e < tok.tree.n ∧ F.head e < tok.tree.n ∧ F.tail e ≠ F.head e := by
    intro e he; rw [htn]; exact (hFEnds e he).2
  have huN : u < tok.tree.n := htn.symm ▸ hu
  have hvN : v < tok.tree.n := htn.symm ▸ hv
  have hptConn : pathTreeConnected tok.tree (vid u) (vid v) :=
    treeEditNamedSlots_connected hlct hns (fun e he => ⟨(hV e he).1, (hV e he).2.1⟩) huN hvN hconn
  refine ⟨hptConn, ?_⟩
  have hsubEq : subRoot (inducedSubPar pathPayload tok.tree.splay tok.trees)
      (tok.trees.flatMap AuxTree.toList).length (vid u) =
      subRoot (inducedSubPar pathPayload tok.tree.splay tok.trees)
      (tok.trees.flatMap AuxTree.toList).length (vid v) :=
    (pathTreeConnected_iff_induced_roots hlct huN hvN).mp hptConn
  obtain ⟨tu, htu, huIn⟩ := List.mem_flatMap.mp (hlct.verticesActive u huN)
  obtain ⟨tv, htv, hvIn⟩ := List.mem_flatMap.mp (hlct.verticesActive v hvN)
  have huv : isVertex tok.tree.n (vid u) := vid_isVertex huN
  have hvv : isVertex tok.tree.n (vid v) := vid_isVertex hvN
  -- Step A: `lctReroot` + `lctExpose` = `lctPathSummary`
  set s' := (lctPathSummary pathPayload tok.tree (vid u) (vid v)).1 with hs'_def
  set sum := (lctPathSummary pathPayload tok.tree (vid u) (vid v)).2 with hsum_def
  have hs'n : s'.n = tok.tree.n := lctPathSummary_n tok.tree (vid u) (vid v)
  obtain ⟨trees1, trees', tL, depth', htExpMem, hlct', hactPerm', _, _, _, _, hpar'u, _, _,
      hsumEq, hperm1, hfpPerm', hreachExp, hoffOut, honIn, hconnIff', _, _⟩ :=
    lctPathSummary_spec pathPayload_laws hlct htu huIn huv htv hvIn hsubEq
  rw [← lctPathSummary_fst_eq_cost] at hlct' hpar'u hsumEq hfpPerm' hreachExp hoffOut honIn hconnIff'
  rw [← lctPathSummary_snd_eq_cost] at hsumEq
  rw [← hs'_def] at hlct' hpar'u hsumEq hfpPerm' hreachExp hoffOut honIn hconnIff'
  rw [← hsum_def] at hsumEq
  -- `PathTreeNumericInv` preserved on `(s', trees')`
  obtain ⟨tsNum, dNum, hWNum, hnumNum⟩ := pathTreeNumericInv_summary hlct hnum htu huIn huv hvv
  change LctInvWith pathPayload s' tsNum tok.free dNum at hWNum
  change PathTreeNumericInv s' tsNum B R at hnumNum
  -- Step B: Reroot preserves `TreeEditNamedSlots` and orientation/accounts; Expose preserves them too
  set st1 := lctReroot pathPayload tok.tree (vid u) with hst1_def
  have hst1n : st1.n = tok.tree.n := LinkCut.Gen.lctReroot_n pathPayload tok.tree (vid u)
  obtain ⟨trees1R, _, depth1R, _, hlct1R, hact1R, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    lctReroot_spec pathPayload_laws hlct htu huIn huv
  have hst1Eq : (lctRerootCost pathPayload tok.tree (vid u)).1 = st1 := rfl
  rw [hst1Eq] at hlct1R
  obtain ⟨hns1, hor1⟩ := reroot_preserves_named_orient hlct hns hV huN (hst1_def ▸ hlct1R)
  rw [← hst1_def] at hns1 hor1
  have hv1R : vid v ∈ trees1R.flatMap AuxTree.toList :=
    hact1R.mem_iff.mpr (hlct.verticesActive v hvN)
  obtain ⟨tv1R, htv1R, hv1RIn⟩ := List.mem_flatMap.mp hv1R
  obtain ⟨trees2E, _, _, hlct2E, hact2E, hpar2E, hfp2E, _⟩ :=
    lctExpose_spec pathPayload_laws hlct1R htv1R hv1RIn
  rw [← lctExpose_eq_cost] at hlct2E hpar2E hfp2E
  have hs'Eq : s' = lctExpose pathPayload st1 (vid v) := lctPathSummary_fst_eq_expose tok.tree (vid u) (vid v)
  have hVals' : ValsOnEdges s' := by
    rw [hs'Eq]
    exact vals_expose hlct1R (hst1_def ▸ vals_reroot hlct hVals huv) hv1R
  have hlct2E' : LctInvWith pathPayload s' trees2E tok.free depth1R := by
    rw [hs'Eq]; exact hlct2E
  have hpar2E' : ∀ z, inducedSubPar pathPayload s'.splay trees2E z =
      inducedSubPar pathPayload st1.splay trees1R z := fun z => by
    rw [hs'Eq]; exact hpar2E z
  have hfp2E' : (forestPairs pathPayload s'.splay trees2E).Perm
      (forestPairs pathPayload st1.splay trees1R) := by
    rw [hs'Eq]; exact hfp2E
  -- Freeze `s'`, `sum`, `st1` so `whnf` never unfolds `lctPathSummary`
  clear hs'_def hsum_def hst1_def hst1Eq hs'Eq
  clear_value s' sum st1
  have hfpNumEq := treeEdit_account_witness_agreement hWNum hlct'
  have hactNumEq := (treeEdit_witness_agreement hWNum hlct').1
  have hnum' : PathTreeNumericInv s' trees' B R := by
    obtain ⟨hB, hR, hRoutes, hAccNum, hInact⟩ := hnumNum
    refine ⟨hB, hR, ?_, fun i val hm => hAccNum i val (hfpNumEq.symm.mem_iff.mp hm),
      fun i hi hnot => hInact i hi (fun hm => hnot (hactNumEq.mem_iff.mp hm))⟩
    intro t ht x hx
    have htNum : t ∈ tsNum := lct_tree_mem_of_same_pointers hWNum hlct' rfl
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ht
    exact hRoutes t htNum x hx
  obtain ⟨hactE', hparE'⟩ := treeEdit_witness_agreement hlct2E' hlct'
  have hfpE' := treeEdit_account_witness_agreement hlct2E' hlct'
  have hparFinal : ∀ z, inducedSubPar pathPayload s'.splay trees' z =
      inducedSubPar pathPayload st1.splay trees1R z := fun z =>
    (congrFun hparE'.symm z).trans (hpar2E' z)
  have hact1'_perm : (trees'.flatMap AuxTree.toList).Perm (trees1R.flatMap AuxTree.toList) :=
    hactE'.symm.trans hact2E
  have hfp1'_perm : (forestPairs pathPayload s'.splay trees').Perm
      (forestPairs pathPayload st1.splay trees1R) :=
    hfpE'.symm.trans hfp2E'
  have hs'st1N : s'.n = st1.n := hs'n.trans hst1n.symm
  have hns' : TreeEditNamedSlots s' trees' F slot name := by
    refine ⟨fun e he => ?_, fun k hk hks => hns1.inverse k (hact1'_perm.mem_iff.mp hk) (hs'st1N ▸ hks), fun e he => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := hns1.forward e he
      exact ⟨hact1'_perm.mem_iff.mpr a1, hs'st1N.symm ▸ a2, a3⟩
    · have he1 := hns1.endpoints e he
      simpa only [hparFinal] using he1
  -- Per-edge account preservation for every `e ∈ model.extG.E`
  have hTreeEdgeKeep : ∀ e ∈ model.extG.E, model.extToInt e ∈ F.E →
      ∀ val : PathEdgeValue,
        (slot (model.extToInt e), some val) ∈ forestPairs pathPayload tok.tree.splay tok.trees →
        ∃ val' : PathEdgeValue,
          (slot (model.extToInt e), some val') ∈ forestPairs pathPayload s'.splay trees' ∧
          val'.originalFlow = val.originalFlow ∧
          val'.originalGradient = val.originalGradient ∧
          val'.length = val.length ∧
          val'.detector = val.detector ∧
          (val'.forward = true →
            inducedSubPar pathPayload s'.splay trees' (vid (F.head (model.extToInt e))) = slot (model.extToInt e) ∧
            inducedSubPar pathPayload s'.splay trees' (slot (model.extToInt e)) = vid (F.tail (model.extToInt e))) ∧
          (val'.forward = false →
            inducedSubPar pathPayload s'.splay trees' (vid (F.tail (model.extToInt e))) = slot (model.extToInt e) ∧
            inducedSubPar pathPayload s'.splay trees' (slot (model.extToInt e)) = vid (F.head (model.extToInt e))) := by
    intro e he hT val hp
    have hoE := hori e he
    dsimp only at hoE
    rw [ite_eq_left hT] at hoE
    obtain ⟨_, _, hft, hff⟩ := hoE val hp
    obtain ⟨val', hp1, hfl, hgr, hln, hdt, hft1, hff1⟩ := hor1 (model.extToInt e) hT val hp ⟨hft, hff⟩
    exact ⟨val', hfp1'_perm.symm.mem_iff.mp hp1, hfl, hgr, hln, hdt,
      fun h => by simpa only [hparFinal] using hft1 h,
      fun h => by simpa only [hparFinal] using hff1 h⟩
  have hAcc' : SolverEdgeAccountsAt model L P mem tok.slots tok.names tok.slotThresholds
      tok.edgeThresholds tok.edgeRecords tok.inOffReady tok.intCap s' trees' := by
    refine ⟨fun e he => ?_, fun sl val hsl hfp => ?_⟩
    · obtain ⟨hei, hthr, hbr⟩ := hedgeAcc.1 e he
      refine ⟨hei, hthr, ?_⟩
      by_cases hT : model.extToInt e ∈ F.E
      · rw [ite_eq_left hT] at hbr ⊢
        obtain ⟨a1, a2, a3, a4, val, acc, hp, hfl, hacc, hdet⟩ := hbr
        obtain ⟨val', hp', hfl', _, _, hdet', _, _⟩ := hTreeEdgeKeep e he hT val hp
        exact ⟨a1, hs'n.symm ▸ a2, a3, a4, val', acc, hp', hfl'.symm ▸ hfl, hacc, hdet'.symm ▸ hdet⟩
      · rw [ite_eq_right hT] at hbr ⊢; exact hbr
    · have hslAct : sl ∈ trees'.flatMap AuxTree.toList :=
        (forestPairs_fst_perm s'.splay trees').mem_iff.mp (List.mem_map.mpr ⟨(sl, some val), hfp, rfl⟩)
      obtain ⟨hMemF, hSlEq⟩ := hns'.inverse sl hslAct hsl
      have hG0 : name sl ∈ (model.chain.G 0).E := hFsub hMemF
      obtain ⟨hFwd, hExt⟩ := hFresh.hRight (name sl) hG0
      exact ⟨(hFEnds (name sl) hMemF).1, hMemF, hSlEq, hExt, hFwd⟩
  have hOri' : SolverEdgeOrientInv L P model mem tok.slots tok.edgeRecords s' trees' := by
    intro e he
    dsimp only [SolverEdgeOrientInv]
    by_cases hT : model.extToInt e ∈ F.E
    · rw [ite_eq_left hT]
      intro val' hp'
      have hbr := (hedgeAcc.1 e he).2.2
      rw [ite_eq_left hT] at hbr
      obtain ⟨_, _, _, _, val0, _, hp0, _, _, _⟩ := hbr
      obtain ⟨val1, hp1, _, hgr1, hln1, _, hft1, hff1⟩ := hTreeEdgeKeep e he hT val0 hp0
      have heq : some val' = some val1 := mem_forestPairs_unique_val hlct'.activeNodup hp' hp1
      have hvEq : val' = val1 := Option.some.inj heq
      subst hvEq
      have ho0 := hori e he
      dsimp only [SolverEdgeOrientInv] at ho0
      rw [ite_eq_left hT] at ho0
      obtain ⟨hgr0, hln0, _, _⟩ := ho0 val0 hp0
      exact ⟨hgr1.symm ▸ hgr0, hln1.symm ▸ hln0, hft1, hff1⟩
    · rw [ite_eq_right hT]
      have ho0 := hori e he
      dsimp only [SolverEdgeOrientInv] at ho0
      rw [ite_eq_right hT] at ho0
      exact ho0
  -- Step C: Exact length identity and magnitude bound for `sum.length`
  set t_exp := AuxTree.node (vid v) tL AuxTree.leaf
  set onPath := SplayState.evalPairs pathPayload s'.splay t_exp false pathPayload.idTag
  set offPath := forestPairs pathPayload s'.splay (trees'.erase t_exp)
  have hreachUV : reaches (inducedSubPar pathPayload s'.splay trees')
      (trees'.flatMap AuxTree.toList).length (vid u) (vid v) = true := by
    have hsu : subRoot (inducedSubPar pathPayload s'.splay trees')
        (trees'.flatMap AuxTree.toList).length (vid u) = vid u :=
      subRoot_eq_self_of_zero hlct' (hlct'.verticesActive u (hs'n.symm ▸ huN)) hpar'u
    have hEq' : subRoot (inducedSubPar pathPayload s'.splay trees')
        (trees'.flatMap AuxTree.toList).length (vid u) =
        subRoot (inducedSubPar pathPayload s'.splay trees')
        (trees'.flatMap AuxTree.toList).length (vid v) :=
      (hconnIff' (vid u) (hlct.verticesActive u huN) (vid v) (hlct.verticesActive v hvN)).mpr hsubEq
    rw [hsu] at hEq'
    exact (subRoot_eq_iff_reaches_zero hlct' (hlct'.verticesActive v (hs'n.symm ▸ hvN)) hpar'u).mp hEq'.symm
  have hWalkIff := (parentWalk_forestPath hlct' hns' hF (hs'n.symm ▸ hV) (hs'n.symm ▸ huN) (hs'n.symm ▸ hvN) hpar'u hreachUV).1
  have hOnNd : (onPath.map Prod.fst).Nodup := by
    have hAllNd : ((forestPairs pathPayload s'.splay trees').map Prod.fst).Nodup :=
      (forestPairs_fst_perm s'.splay trees').nodup_iff.mpr hlct'.activeNodup
    have hAppNd : ((onPath ++ offPath).map Prod.fst).Nodup :=
      (hfpPerm'.map Prod.fst).nodup_iff.mp hAllNd
    rw [List.map_append] at hAppNd
    exact hAppNd.of_append_left
  -- Characterize `onPath.filterMap (fun p => p.2.map ...)` via bijection with `walkEdges (F.forestPath u v)`
  set Wp := F.forestPath u v
  set Eset := walkEdges Wp
  have hPathWp := LSF.forestPath_isPath hF hconn
  have hEsetSub : ∀ e ∈ Eset, e ∈ F.E := fun e he => by
    unfold Eset walkEdges at he
    rw [List.mem_toFinset] at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact MGraph.isWalk_edges_mem hPathWp.1 x hx
  -- For every `e ∈ Eset`, there is a unique `(slot e, some val_e) ∈ onPath`
  have hEdgeInOn : ∀ e ∈ Eset, ∃ val : PathEdgeValue,
      (slot e, some val) ∈ onPath ∧
      (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt e) ∧
      |val.length| ≤ B := by
    intro e he
    have heF : e ∈ F.E := hEsetSub e he
    have hreachE : reaches (inducedSubPar pathPayload s'.splay trees')
        (trees'.flatMap AuxTree.toList).length (slot e) (vid v) = true :=
      (hWalkIff e heF).mpr he
    have hSlotInExp : slot e ∈ t_exp.toList := (hreachExp (slot e)).mpr hreachE
    have hG0e : e ∈ (model.chain.G 0).E := hFsub heF
    obtain ⟨heFwd, heExt⟩ := hFresh.hRight e hG0e
    have hbr := (hAcc'.1 (model.intToExt e) heExt).2.2
    rw [heFwd, ite_eq_left heF] at hbr
    obtain ⟨_, _, _, _, val, _, hp, _, _, _⟩ := hbr
    have hpApp : (slot e, some val) ∈ onPath ++ offPath := hfpPerm'.mem_iff.mp hp
    have hNotOff : (slot e, some val) ∉ offPath := fun h => hoffOut _ h hSlotInExp
    have hpOn : (slot e, some val) ∈ onPath := (List.mem_append.mp hpApp).resolve_right hNotOff
    have hoE := hOri' (model.intToExt e) heExt
    dsimp only [SolverEdgeOrientInv] at hoE
    rw [heFwd, ite_eq_left heF] at hoE
    exact ⟨val, hpOn, (hoE val hp).2.1, (hnum'.2.2.2.1 (slot e) val hp).2.1⟩
  -- Conversely, every `(k, some val) ∈ onPath` has `isEdgeSlot s'.n k`, `name k ∈ Eset`, and `slot (name k) = k`
  have hOnInEdge : ∀ k val, (k, some val) ∈ onPath →
      name k ∈ Eset ∧ slot (name k) = k := by
    intro k val hp
    have hFp : (k, some val) ∈ forestPairs pathPayload s'.splay trees' :=
      hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ hp)
    have hAct : k ∈ trees'.flatMap AuxTree.toList :=
      (forestPairs_fst_perm s'.splay trees').mem_iff.mp (List.mem_map.mpr ⟨(k, some val), hFp, rfl⟩)
    have hNotV : ¬ isVertex s'.n k := fun hvK => by
      have hNone := pairsVE_of_vals hVals' trees' (k, some val) hFp hvK
      simp at hNone
    have hSlot : isEdgeSlot s'.n k :=
      (isNode_iff_vertex_or_edge.mp (hlct'.activeValid k hAct)).resolve_left hNotV
    obtain ⟨hMemF, hSlEq⟩ := hns'.inverse k hAct hSlot
    have hInExp : k ∈ t_exp.toList := honIn _ hp
    have hReach : reaches (inducedSubPar pathPayload s'.splay trees')
        (trees'.flatMap AuxTree.toList).length k (vid v) = true :=
      (hreachExp k).mp hInExp
    rw [← hSlEq] at hReach
    exact ⟨(hWalkIff (name k) hMemF).mp hReach, hSlEq⟩
  -- Express `sum.length` as a `Finset.sum` over `Eset`
  have hSumLen : (sum.length : ℝ) / (2 : ℝ) ^ P =
      walkLength (fun ei => model.extℓ (model.intToExt ei)) Wp ∧
      |sum.length| ≤ (model.extG.n : ℤ) * B := by
    classical
    let somePairs := onPath.filter (fun p => p.2.isSome)
    let fLen : ℕ × Option PathEdgeValue → ℤ := fun p => match p.2 with | some val => val.length | none => 0
    have hFilterSum : (onPath.filterMap (fun p => p.2.map PathEdgeValue.length)).sum =
        (somePairs.map fLen).sum := by
      dsimp only [somePairs, fLen]
      clear * -
      induction onPath with
      | nil => rfl
      | cons p rest ih =>
        rcases p with ⟨k, v⟩
        cases v <;> simp [ih]
    have hSumEq : sum.length = (somePairs.map fLen).sum := by
      rw [hsumEq, listSummary_length_eq_sum, hFilterSum]
    have hSomeNd : somePairs.Nodup :=
      (List.Nodup.of_map Prod.fst hOnNd).filter _
    have hOnInj : ∀ p₁ ∈ somePairs, ∀ p₂ ∈ somePairs, name p₁.1 = name p₂.1 → p₁ = p₂ := by
      intro ⟨k₁, v₁⟩ h1 ⟨k₂, v₂⟩ h2 hne
      obtain ⟨h1On, h1Some⟩ := List.mem_filter.mp h1
      obtain ⟨h2On, h2Some⟩ := List.mem_filter.mp h2
      obtain ⟨val₁, rfl⟩ := Option.isSome_iff_exists.mp h1Some
      obtain ⟨val₂, rfl⟩ := Option.isSome_iff_exists.mp h2Some
      have hs1 := (hOnInEdge k₁ val₁ h1On).2
      have hs2 := (hOnInEdge k₂ val₂ h2On).2
      have hkEq : k₁ = k₂ := by rw [← hs1, hne, hs2]
      subst hkEq
      have hFp1 := hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ h1On)
      have hFp2 := hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ h2On)
      have hvEq := mem_forestPairs_unique_val hlct'.activeNodup hFp1 hFp2
      rw [hvEq]
    have hBijSum : ∀ (g : ℕ × Option PathEdgeValue → ℝ) (h : ℕ → ℝ),
        (∀ p ∈ somePairs, g p = h (name p.1)) →
        (somePairs.map g).sum = ∑ e ∈ Eset, h e := by
      intro g h hgh
      rw [← List.sum_toFinset _ hSomeNd]
      refine Finset.sum_nbij (fun p => name p.1) ?_ ?_ ?_ ?_
      · intro ⟨k, v⟩ hp
        rw [List.mem_toFinset] at hp
        obtain ⟨hOn, hSome⟩ := List.mem_filter.mp hp
        obtain ⟨val, rfl⟩ := Option.isSome_iff_exists.mp hSome
        exact (hOnInEdge k val hOn).1
      · intro p₁ h1 p₂ h2 hEq
        exact hOnInj p₁ (List.mem_toFinset.mp h1) p₂ (List.mem_toFinset.mp h2) hEq
      · intro e he
        obtain ⟨val, hpOn, _, _⟩ := hEdgeInOn e he
        refine ⟨(slot e, some val), List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpOn, rfl⟩), ?_⟩
        exact (hns'.forward e (hEsetSub e he)).2.2
      · intro p hp
        exact hgh p (List.mem_toFinset.mp hp)
    have hCastDiv : (sum.length : ℝ) / (2 : ℝ) ^ P =
        (somePairs.map (fun p => (fLen p : ℝ) / (2 : ℝ) ^ P)).sum := by
      rw [hSumEq]
      have hAux : ∀ xs : List (ℕ × Option PathEdgeValue),
          ((xs.map fLen).sum : ℝ) / (2 : ℝ) ^ P =
            (xs.map (fun p => (fLen p : ℝ) / (2 : ℝ) ^ P)).sum := fun xs => by
        induction xs with
        | nil => simp
        | cons p rest ih => rw [List.map_cons, List.sum_cons, Int.cast_add, add_div, ih, List.map_cons, List.sum_cons]
      exact hAux somePairs
    constructor
    · rw [hCastDiv, LSF.walkLength_eq_sum_of_isPath _ hPathWp]
      refine hBijSum _ _ fun ⟨k, v⟩ hp => ?_
      obtain ⟨hOn, hSome⟩ := List.mem_filter.mp hp
      obtain ⟨val, rfl⟩ := Option.isSome_iff_exists.mp hSome
      obtain ⟨heIn, hSlEq⟩ := hOnInEdge k val hOn
      obtain ⟨val', hpOn', hLen', _⟩ := hEdgeInOn (name k) heIn
      rw [hSlEq] at hpOn'
      have hFp1 := hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ hOn)
      have hFp2 := hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ hpOn')
      have hvEq := mem_forestPairs_unique_val hlct'.activeNodup hFp1 hFp2
      have hvalEq : val = val' := Option.some.inj hvEq
      subst hvalEq
      exact hLen'
    · rw [hSumEq]
      have hB0 : 0 ≤ B := hnum'.1
      have hEach : ∀ z ∈ somePairs.map fLen, |z| ≤ B := by
        intro z hz
        obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp hz
        obtain ⟨hOn, hSome⟩ := List.mem_filter.mp hp
        obtain ⟨val, rfl⟩ := Option.isSome_iff_exists.mp hSome
        have hFp := hfpPerm'.symm.mem_iff.mp (List.mem_append_left _ hOn)
        exact (hnum'.2.2.2.1 k val hFp).2.1
      have hAbs := abs_list_sum_le hEach
      rw [List.length_map] at hAbs
      have hCardEq : somePairs.length = Eset.card := by
        rw [← List.toFinset_card_of_nodup hSomeNd]
        refine Finset.card_bij (fun p _ => name p.1) ?_ ?_ ?_
        · intro ⟨k, v⟩ hp
          obtain ⟨hOn, hSome⟩ := List.mem_filter.mp (List.mem_toFinset.mp hp)
          obtain ⟨val, rfl⟩ := Option.isSome_iff_exists.mp hSome
          exact (hOnInEdge k val hOn).1
        · intro p₁ h1 p₂ h2 hEq
          exact hOnInj p₁ (List.mem_toFinset.mp h1) p₂ (List.mem_toFinset.mp h2) hEq
        · intro e he
          obtain ⟨val, hpOn, _, _⟩ := hEdgeInOn e he
          exact ⟨(slot e, some val), List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpOn, rfl⟩),
            (hns'.forward e (hEsetSub e he)).2.2⟩
      have hCardLe : Eset.card ≤ model.extG.n := by
        have hLt := forestPath_length_lt hF (fun e he => ⟨(hFEnds e he).2.1, (hFEnds e he).2.2.1⟩) hu hconn
        have hLt' : Wp.length < model.extG.n := hLt
        have hCardWp : Eset.card = Wp.length := by
          unfold Eset walkEdges
          rw [List.toFinset_card_of_nodup (LSF.isPath_nodup_edges hPathWp), List.length_map]
        omega
      calc |(somePairs.map fLen).sum| ≤ (somePairs.length : ℤ) * B := hAbs
        _ = (Eset.card : ℤ) * B := by rw [hCardEq]
        _ ≤ (model.extG.n : ℤ) * B := mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hCardLe) hB0
  exact ⟨trees', depth', hlct', hnum', hns', hAcc', hOri', hSumLen.1, hSumLen.2⟩

/-! ## 3. Machine `opTree 3` (`PathSummary`) step on `solverStateRep` -/

/-- Executes one `opTree 3` (`PathSummary`) call on `[tok.treeHeap, vid u, vid v, work]`,
updating `tok` via `solverStateRep_after_goodApply` (zero flow increment) and returning the
guarded next scratch pointer `workNext = max ret (work + 2 * L)`. -/
theorem solverStateRep_update_treeSummary
    {w L P m V psi k epsExp drainUnit initTree root descBase work u v size : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R : ℤ}
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hMatch : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (hlocDisj : ∀ a, loc.hb ≤ a → a < loc.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < work)
    (hdescWork : descBase ≤ work)
    (htag18 : ∀ a, tok.tag a = 18 → a < descBase)
    (hz : ZeroFrom mem work)
    (hroom : work + (20 * LinkCut.PathProg.treeLimbs L + 100) < 2 ^ w)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w)
    (htreeHW : tok.treeHeap < 2 ^ w)
    (hu : u < model.extG.n) (hv : v < model.extG.n)
    (hconn : model.chain.toTreeChain.chainTree.Connected u v) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let sum := (lctPathSummary pathPayload tok.tree (vid u) (vid v)).2
    ∃ (bTree : Stmt) (oTree : Outcome) (stTree : State) (cTree : ℕ) (tok' : SolverToken cfg L Rcore),
      p.procs[opTree 3]? = some bTree ∧
      Runs w p ω bTree (startState [tok.treeHeap, u + 1, v + 1, work] mem pos) oTree stTree cTree ∧
      work ≤ oTree.value ∧
      oTree.value ≤ work + (20 * LinkCut.PathProg.treeLimbs L + 100) ∧
      PathIntAt stTree.mem (work + L) 4 L sum.length ∧
      (sum.length : ℝ) / (2 : ℝ) ^ P =
        walkLength (fun ei => model.extℓ (model.intToExt ei))
          (model.chain.toTreeChain.chainTree.forestPath u v) ∧
      |sum.length| ≤ (model.extG.n : ℤ) * B ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
      tok'.handle = tok.handle ∧ tok'.treeHeap = tok.treeHeap ∧
      (∀ a, tok'.tag a = 18 → a < descBase) ∧
      Rrep.rep root model tok' stTree.mem ∧
      PreservesLevelMeta tok tok' mem stTree.mem ∧
      SelectHeapMatchesChain stTree.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      OffTreeRecInv model L stTree.mem tok'.edgeRecords B ∧
      OffTreeRecBound model L stTree.mem tok'.edgeRecords B ∧
      ZeroFrom stTree.mem (max oTree.value (work + 2 * L)) ∧
      max oTree.value (work + 2 * L) ≤ work + (20 * LinkCut.PathProg.treeLimbs L + 100) ∧
      (∀ a < work, ¬ Rrep.foot root tok a → stTree.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a) ∧
      cTree + Rrep.phi root tok' stTree.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + Rrep.phi root tok mem := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, _, _, _, _, _, _, hoffR, htn, hlct, htreeRep, hedgeAcc, _, _, _, _, hWire, htags⟩ := hrep
  have hvidU : u + 1 = vid u := rfl
  have hvidV : v + 1 = vid v := rfl
  obtain ⟨hptConn, trees', depth', hlct', hnum', hns', hAcc', hOri', hLenEq, hLenBd⟩ :=
    lctPathSummary_model_step hrep0 hnum hFsub hu hv hconn
  have hfits0 : pathTreeFits fmt.limbBits L tok.tree := by
    rw [hfmt4]; exact hnum.fits hlct (by rw [htn]; exact hcapT)
  have hfits1 : pathTreeFits fmt.limbBits L (lctPathSummary pathPayload tok.tree (vid u) (vid v)).1 := by
    rw [hfmt4]; exact hnum'.fits hlct' (by rw [lctPathSummary_n, htn]; exact hcapT)
  have hTreePre : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
      3 tok.tree [tok.treeHeap, vid u, vid v, work] mem :=
    ⟨⟨tok.trees, tok.free, tok.depth, hlct⟩, hfits0, htn ▸ h2nW,
      by rw [hfmt4, htn]; exact hlogW,
      tok.treeHeap, vid u, vid v, work, rfl,
      by unfold isVertex vid; omega, by unfold isVertex vid; omega, hptConn, hfits1⟩
  have hTreeFoot : ∀ a, Rtree.foot tok.treeHeap tok.treeTok a → a < work :=
    fun a ha => hbelow a (Or.inr (Or.inl ha))
  obtain ⟨bTree, hbTree, oTree, stTree, cTree, hrTree, sNext, treeTok', hrepTree', hpostTree,
      hRespTree, hcostTree⟩ :=
    hTreeImpl.2.2 3 tok.treeHeap tok.tree tok.treeTok [tok.treeHeap, vid u, vid v, work]
      mem pos ω (by intro v' hv'; simp [vid] at hv'; rcases hv' with rfl | rfl | rfl | rfl <;> omega)
      rfl htreeRep hTreePre hTreeFoot
      (by simpa [heapArg] using hz)
      (by simp only [pathTreeMachineContract, LinkCut.PathProg.pathAlloc, show (3 : ℕ) ≠ 7 by decide, ↓reduceIte,
            heapArg, List.getLastD_cons, List.getLastD_nil]; exact hroom)
  simp only [pathTreeMachineContract, LinkCut.PathProg.pathAlloc, show (3 : ℕ) ≠ 7 by decide, ↓reduceIte,
    heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero, List.getD_cons_succ] at hpostTree hRespTree hcostTree
  obtain ⟨hsNextEq, hSumAt⟩ := hpostTree
  have hsNextN : sNext.n = tok.tree.n := by rw [hsNextEq]; exact lctPathSummary_n tok.tree (vid u) (vid v)
  rw [← hsNextEq] at hlct' hnum' hns' hAcc' hOri'
  clear hsNextEq
  obtain ⟨hRetLo, hRetHi, hzRet, hFrTree, hFtTree⟩ := hRespTree
  have h2LleAlloc : 2 * L ≤ 20 * LinkCut.PathProg.treeLimbs L + 100 := by
    unfold LinkCut.PathProg.treeLimbs; omega
  set workN := max oTree.value (work + 2 * L)
  have hWorkNLe : workN ≤ work + (20 * LinkCut.PathProg.treeLimbs L + 100) := by omega
  have hzWorkN : ZeroFrom stTree.mem workN := fun a ha => hzRet a (by omega)
  have hFrOther : ∀ a < work, tok.tag a ≠ 0 → tok.tag a ≠ 16 → stTree.mem a = mem a := fun a ha h0 h16 =>
    hFrTree a ha fun hf => h16 (htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hf)
  have hOwnLt (a : ℕ) (h0 : tok.tag a ≠ 0) : a < work :=
    hbelow a (Or.inl (htags.1 a h0))
  have hTagEq {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv16 : v ≠ 16) : stTree.mem a = mem a :=
    hFrOther a (hOwnLt a (ht ▸ hv0)) (ht ▸ hv0) (ht ▸ hv16)
  -- Re-establish `solverStateRep` via `solverStateRep_after_goodApply` with `inc := fun _ => 0`
  have hModEq :
      ({ model with
        flow := fun e => model.flow e + (0 : ℝ)
        detectAccum := fun e => model.detectAccum e + |(0 : ℝ)| } : Alg2State cfg) = model := by
    cases model; simp
  have hAcc'Mem : SolverEdgeAccountsAt model L P stTree.mem tok.slots tok.names tok.slotThresholds
      tok.edgeThresholds tok.edgeRecords tok.inOffReady tok.intCap sNext trees' := by
    obtain ⟨_, _, _, _, _, _, _, _, _, t9, t10, t11, t12, t13, _, t15, _, t1718, _, _, _⟩ := htags
    refine ⟨fun e he => ?_, fun sl val hsl hfp => ?_⟩
    · obtain ⟨hei, hthr, hbr⟩ := hAcc'.1 e he
      refine ⟨hei, ?_, ?_⟩
      · rw [hTagEq (t12 _ hei) (by decide) (by decide)]
        exact hthr.congr fun j hj => hTagEq ((t1718 e he).1 j hj) (by decide) (by decide)
      · by_cases hT : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
        · rw [ite_eq_left hT] at hbr ⊢
          obtain ⟨a1, a2, a3, a4, val, acc, hp, hfl, hacc, hdet⟩ := hbr
          have hslLt : mem (tok.slots + model.extToInt e) < 2 * tok.tree.n := hsNextN ▸ a2.2
          dsimp only
          rw [hTagEq (t9 _ hei) (by decide) (by decide), hTagEq (t10 _ hslLt) (by decide) (by decide),
            hTagEq (t11 _ hslLt) (by decide) (by decide), hTagEq (t12 _ hei) (by decide) (by decide)]
          exact ⟨a1, a2, a3, a4, val, acc, hp, hfl, hacc, hdet⟩
        · rw [ite_eq_right hT] at hbr ⊢
          obtain ⟨a1, val, acc, hpa, hfl, hacc, hdet, h0⟩ := hbr
          refine ⟨(hTagEq (t9 _ hei) (by decide) (by decide)).trans a1, val, acc, ?_, hfl, hacc, hdet,
            fun hd => (hTagEq (t15 _ hei) (by decide) (by decide)).trans (h0 hd)⟩
          rw [hTagEq (t13 _ hei) (by decide) (by decide)]
          exact hpa.congr fun x hx1 hx2 => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]
            exact hTagEq ((t1718 e he).2 hT _ (by omega)) (by decide) (by decide)
    · have hslLt : sl < 2 * tok.tree.n := hsNextN ▸ hsl.2
      obtain ⟨a1, a2, a3, a4, a5⟩ := hAcc'.2 sl val hsl hfp
      dsimp only
      rw [hTagEq (t10 sl hslLt) (by decide) (by decide), hTagEq (t9 _ a1) (by decide) (by decide)]
      exact ⟨a1, a2, a3, a4, a5⟩
  have hNs'Mem : TreeEditNamedSlots sNext trees' model.chain.toTreeChain.chainTree
      (fun ei => stTree.mem (tok.slots + ei)) (fun sl => stTree.mem (tok.names + sl)) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, t9, t10, _⟩ := htags
    have hFEnds := hWire.2.2.1.2
    refine ⟨fun ei hei => ?_, fun sl hsl hls => ?_, fun ei hei => ?_⟩
    · obtain ⟨b1, b2, b3⟩ := hns'.forward ei hei
      rw [hTagEq (t9 ei (hFEnds ei hei).1) (by decide) (by decide),
        hTagEq (t10 _ (hsNextN ▸ b2.2)) (by decide) (by decide)]
      exact ⟨b1, b2, b3⟩
    · obtain ⟨b1, b2⟩ := hns'.inverse sl hsl hls
      rw [hTagEq (t10 sl (hsNextN ▸ hls.2)) (by decide) (by decide),
        hTagEq (t9 _ (hFEnds _ b1).1) (by decide) (by decide)]
      exact ⟨b1, b2⟩
    · rw [hTagEq (t9 ei (hFEnds ei hei).1) (by decide) (by decide)]
      exact hns'.endpoints ei hei
  have hOri'Mem : SolverEdgeOrientInv L P model stTree.mem tok.slots tok.edgeRecords sNext trees' := by
    obtain ⟨_, _, _, _, _, _, _, _, _, t9, _, _, _, t13, _, _, _, t1718, _⟩ := htags
    intro e he
    have ho := hOri' e he
    have hei := (hedgeAcc.1 e he).1
    dsimp only [SolverEdgeOrientInv] at ho ⊢
    by_cases hT : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
    · rw [ite_eq_left hT] at ho ⊢
      rw [hTagEq (t9 _ hei) (by decide) (by decide)]; exact ho
    · rw [ite_eq_right hT] at ho ⊢
      intro val hpa
      rw [hTagEq (t13 _ hei) (by decide) (by decide)] at hpa
      exact ho val (hpa.congr fun x hx1 hx2 => by
        have hx : x = mem (tok.edgeRecords + model.extToInt e) +
            (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
        rw [hx]
        exact (hTagEq ((t1718 e he).2 hT _ (by omega)) (by decide) (by decide)).symm)
  have hOff'Mem : OffReadyInv stTree.mem tok.offReadyCount tok.offReadyList tok.inOffReady tok.intCap := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, t14, t15, _⟩ := htags
    obtain ⟨o1, o2, o3, o4, o5⟩ := hoffR
    refine ⟨o1, fun j hj => ?_, fun j1 h1 j2 h2 hne => ?_, fun e he => ?_, fun e he h1 => ?_⟩
    · rw [hTagEq (t14 j (by omega)) (by decide) (by decide)]
      obtain ⟨a, b⟩ := o2 j hj
      exact ⟨a, (hTagEq (t15 _ a) (by decide) (by decide)).trans b⟩
    · rw [hTagEq (t14 j1 (by omega)) (by decide) (by decide),
        hTagEq (t14 j2 (by omega)) (by decide) (by decide)]
      exact o3 j1 h1 j2 h2 hne
    · rw [hTagEq (t15 e he) (by decide) (by decide)]; exact o4 e he
    · rw [hTagEq (t15 e he) (by decide) (by decide)] at h1
      obtain ⟨j, hj, hje⟩ := o5 e he h1
      exact ⟨j, hj, (hTagEq (t14 j (by omega)) (by decide) (by decide)).trans hje⟩
  have hFtSame : ∀ a, Rtree.foot tok.treeHeap treeTok' a → Rtree.foot tok.treeHeap tok.treeTok a := by
    intro a ha
    dsimp only [Rtree, LinkCut.PathProg.pathRep] at ha ⊢
    rw [hrepTree'.1, hsNextN, ← htreeRep.1] at ha
    exact ha
  have hGood := solverStateRep_after_goodApply (inc := fun _ => 0) hlocalCore
    (workHeap := work) (h1 := work) (h2 := work) (cnt' := tok.offReadyCount)
    hrep0 hbelow le_rfl le_rfl
    ((hTagEq (htags.2.1 11 (by decide)) (by decide) (by decide)).trans (by simpa using hrootDir 11 (by simp)))
    (fun j hj _ => hTagEq (htags.2.1 j hj) (by decide) (by decide))
    hOff'Mem (hsNextN.trans htn) hlct' hrepTree'
    (fun a ha => Or.inl (hFtSame a ha))
    (fun a ha h0 _ _ _ h16 _ => hFrOther a ha h0 h16)
    (hModEq.symm ▸ hAcc'Mem) hNs'Mem hOri'Mem
  rw [hModEq] at hGood
  set tok' : SolverToken cfg L Rcore :=
    { tok with
      tree := sNext
      trees := trees'
      depth := depth'
      treeTok := treeTok'
      owned := fun a => tok.owned a ∨ (work ≤ a ∧ a < work)
      tag := fun a => if work ≤ a ∧ a < work then 16 else tok.tag a }
  have hphiEq : Rrep.phi root tok' stTree.mem + Rtree.phi tok.treeHeap tok.treeTok mem =
      Rrep.phi root tok mem + Rtree.phi tok.treeHeap treeTok' stTree.mem := by
    dsimp only [Rrep, solverStateRep]
    have hCoreSum : (∑ j : Fin cfg.P.d, Rcore.phi (tok'.coreHandle j.val) (tok'.coreTok j.val) stTree.mem) =
        (∑ j : Fin cfg.P.d, Rcore.phi (tok.coreHandle j.val) (tok.coreTok j.val) mem) :=
      Finset.sum_congr rfl fun j _ => hGood.2 j.val j.isLt
    rw [hCoreSum]
    dsimp only [tok', Rtree]; omega
  have hMatch' : SelectHeapMatchesChain stTree.mem loc 4 P model.chain.toTreeChain
      model.chain.g model.chain.ℓ size :=
    hMatch.of_agree fun a ha1 ha2 =>
      hFrTree a (by omega) fun hf => hlocDisj a ha1 ha2 (Or.inr (Or.inl hf))
  have hOffInv' : OffTreeRecInv model L stTree.mem tok'.edgeRecords B := by
    show OffTreeRecInv model L stTree.mem tok.edgeRecords B
    exact offTreeRecInv_of_agree hrep0 hoff fun a ha =>
      hFrOther a (hOwnLt a (by rcases ha with h | h <;> rw [h] <;> decide))
        (by rcases ha with h | h <;> rw [h] <;> decide)
        (by rcases ha with h | h <;> rw [h] <;> decide)
  have hOffBd' : OffTreeRecBound model L stTree.mem tok'.edgeRecords B := by
    show OffTreeRecBound model L stTree.mem tok.edgeRecords B
    exact offTreeRecBound_of_agree hrep0 hBd fun a ha =>
      hFrOther a (hOwnLt a (by rcases ha with h | h <;> rw [h] <;> decide))
        (by rcases ha with h | h <;> rw [h] <;> decide)
        (by rcases ha with h | h <;> rw [h] <;> decide)
  have hPresMeta : PreservesLevelMeta tok tok' mem stTree.mem :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, fun a ht => by
      have hge : 20 ≤ tok.tag a := by rcases ht with h | h | h | h <;> omega
      exact ⟨by dsimp only [tok']; rw [ite_eq_right (by omega)],
        hFrOther a (hOwnLt a (by omega)) (by omega) (by omega)⟩⟩
  refine ⟨bTree, oTree, stTree, cTree, tok', hbTree, by rw [hvidU, hvidV]; exact hrTree, hRetLo, hRetHi,
    by rw [hfmt4] at hSumAt; exact hSumAt.2.1, hLenEq, hLenBd,
    rfl, rfl, rfl, rfl, ?_, hGood.1, hPresMeta, hMatch', hnum', hOffInv', hOffBd',
    hzWorkN, hWorkNLe,
    fun a ha hnf => hFrTree a ha fun hf => hnf (Or.inr (Or.inl hf)),
    fun a ha => ?_, by rw [htn] at hcostTree; dsimp only [Rrep, Rtree] at hphiEq ⊢; omega⟩
  · intro a h18
    dsimp only [tok'] at h18
    split_ifs at h18 with hr
    · omega
    · exact htag18 a h18
  · rcases ha with (hO | ⟨h1, h2⟩) | hT | hC
    · exact Or.inl hO
    · omega
    · exact Or.inr (Or.inl (hFtSame a hT))
    · exact Or.inr (Or.inr hC)

end MinCostFlow.MinRatio

