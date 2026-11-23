module

public import MinCostFlow.MinRatio.WireChainCoreAlgebra
public import MinCostFlow.MinRatio.WireChainCoreBranchBRuntimeKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSizesKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSplitKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopRunKFBL
public import MinCostFlow.MinRatio.OrdBatchEdits
import Mathlib.Tactic

/-!
# Pure model and arithmetic helpers for the Branch B cost proof (`WireChainCoreBranchBCostProofModel`)

Provides the model-level and pure natural-number lemmas needed to prove the `costLe` field of
`BranchBCostFieldsKFBL` from `BranchBRunKFBL`:

* `ordEditsEnc_batchToOrdEdits_le`: an edge-only batch `U` translates to order edits of encoding
  size at most `2 * U.length`, giving `editWords ≤ 10 * U.length + 1`.
* `list_length_le_batchEnc` and `mGraph_m_le_applyBatch_add_length`: each update has encoding size
  at least `1` and deletes at most `1` edge, giving `(G i₀).m ≤ (G' i₀).m + bW i₀` in Case 1.
* `ordUpdateLoop_treeUpdates_decomp` and `branchB_treeUpdates_ge_fDel_add_symmDiff`: tracking
  `Chain.Ordered.updateLoop` across the plain levels `[0, i₀)` and the exit shows that
  `∑_{j < i₀} (D j).fDel.length + (oldE \ newE).card + (newE \ oldE).card` is at most
  `modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates` in all three exit cases.
* `branchB_stepCost_le_noRebuild`: relates `branchBStepCostKFBL + 4` to
  `updateCoreNoRebuildStepCost + 30` plus the per-level `20 * fDel.length + 20 * reemb.length`.
* `branchB_cost_case1_arith`, `branchB_cost_case2_arith`, `branchB_cost_case3_arith`: standalone
  natural-number cost assembly lemmas for the three exit cases.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore.Program

/-! ### 1. Batch and edit size bounds -/

/-- Every edge-only update translates to order edits of total encoding size at most `2`. -/
theorem ordEditsEnc_batchToOrdEdits_le (U : List Update) (hEdge : ∀ u ∈ U, IsEdgeUpdate u) :
    ordEditsEnc (batchToOrdEdits U) ≤ 2 * U.length := by
  induction U with
  | nil => simp [batchToOrdEdits, ordEditsEnc]
  | cons u rest ih =>
    have hu := hEdge u List.mem_cons_self
    have hr := ih (fun v hv => hEdge v (List.mem_cons_of_mem u hv))
    simp only [batchToOrdEdits, List.flatMap_cons, ordEditsEnc, List.map_append, List.sum_append,
      List.length_cons] at hr ⊢
    cases u with
    | insert e x y =>
      simp only [edgeUpdateToOrdEdits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        OrdEdit.enc]
      omega
    | delete e =>
      simp only [edgeUpdateToOrdEdits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        OrdEdit.enc]
      omega
    | split _ _ _ _ => exact hu.elim

/-- Every update has encoding size at least `1`, so `U.length ≤ G.batchEnc U`. -/
theorem list_length_le_batchEnc : ∀ (G : MGraph) (U : List Update), U.length ≤ G.batchEnc U
  | _, [] => le_rfl
  | G, u :: rest => by
    have h1 : 1 ≤ G.updateEnc u := by
      cases u <;> simp [MGraph.updateEnc]
    have h2 := list_length_le_batchEnc (G.applyUpdate u) rest
    simp only [List.length_cons, MGraph.batchEnc]
    omega

/-- Applying a batch of `U.length` updates deletes at most `U.length` edges. -/
theorem mGraph_m_le_applyBatch_add_length :
    ∀ (G : MGraph) (U : List Update), G.m ≤ (G.applyBatch U).m + U.length
  | _, [] => by simp [MGraph.applyBatch]
  | G, u :: rest => by
    have hstep : G.m ≤ (G.applyUpdate u).m + 1 := by
      cases u with
      | insert e x y =>
        simp only [MGraph.m, MGraph.applyUpdate]
        have := Finset.card_le_card (Finset.subset_insert e G.E)
        omega
      | delete e =>
        simp only [MGraph.m, MGraph.applyUpdate]
        by_cases he : e ∈ G.E
        · rw [Finset.card_erase_of_mem he]
          have hpos : 1 ≤ G.E.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        · rw [Finset.erase_eq_of_notMem he]
          omega
      | split _ _ _ _ =>
        simp only [MGraph.m, MGraph.applyUpdate]
        omega
    have hrest := mGraph_m_le_applyBatch_add_length (G.applyUpdate u) rest
    simp only [MGraph.applyBatch, List.foldl_cons, List.length_cons] at hrest ⊢
    omega

/-! ### 2. Tree-update decomposition of `Chain.Ordered.updateLoop` -/

/-- Exact `totalTreeUpdates` equality for `algorithm1_rebuild` at `idx < P.d`. -/
private theorem algorithm1_rebuild_totalTreeUpdates_eq (T : SparseCoreRestartTool)
    (L : LastLevelTool) (P : ChainParams) (st : ChainState T P) {idx : ℕ} (hidx : idx < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P st idx Gnew extraEnc).1
    st.totalTreeUpdates +
      (diffTreeChanges st.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length ≤
      next.totalTreeUpdates := by
  intro next
  have hSub := rebuild_totalTreeUpdates_sub T L P st hidx Gnew extraEnc
  set G0 := fun j => if j = idx then Gnew else st.G j
  set res := Chain.Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - idx) idx G0
    st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
  obtain ⟨hEDpre, hEDzero, _⟩ := ordRebuildSuffix_extra T L P st.lvlM st.N₀ st.ℓ st.g
    (P.d - idx) idx (by omega) G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates
    st.curFwd
  have hDec : ∀ m, next.curDecUpdates m = res.2.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hidx, ↓reduceDIte, res, G0]
  have hSplitRange : Finset.range P.d = Finset.range idx ∪ Finset.Ico idx P.d := by
    ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hDisjRange : Disjoint (Finset.range idx) (Finset.Ico idx P.d) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  have hOldS : (Finset.range P.d).sum (fun j => st.curDecUpdates j) =
      (Finset.range idx).sum (fun j => st.curDecUpdates j) +
      (Finset.Ico idx P.d).sum (fun j => st.curDecUpdates j) := by
    rw [hSplitRange, Finset.sum_union hDisjRange]
  have hNewS : (Finset.range P.d).sum (fun j => next.curDecUpdates j) =
      (Finset.range idx).sum (fun j => st.curDecUpdates j) := by
    rw [hSplitRange, Finset.sum_union hDisjRange]
    have h1 : (Finset.range idx).sum (fun j => next.curDecUpdates j) =
        (Finset.range idx).sum (fun j => st.curDecUpdates j) :=
      Finset.sum_congr rfl fun j hj => by rw [hDec j, (hEDpre j (Finset.mem_range.mp hj)).2]
    have h2 : (Finset.Ico idx P.d).sum (fun j => next.curDecUpdates j) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj; rw [hDec j, (hEDzero j h1 (by omega)).2]
    rw [h1, h2, add_zero]
  have hCl : next.closedTreeUpdates = st.closedTreeUpdates +
      (Finset.Ico idx P.d).sum (fun j => st.curDecUpdates j) + st.curLastTreeUpdates +
      (diffTreeChanges st.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hidx, ↓reduceDIte]; rfl
  unfold ChainState.totalTreeUpdates
  rw [hCl, hOldS, hNewS]
  omega

/-- Decomposition of `Chain.Ordered.updateLoop` into its plain steps `[idx, i₀)` and its exit at
`i₀`, tracking `rebuildCount`, active LSFs, and `totalTreeUpdates`. -/
theorem ordUpdateLoop_treeUpdates_decomp (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      idx + rem = P.d →
      let X := (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
      ∃ (i₀ : ℕ) (chStop : ChainState T P),
        idx ≤ i₀ ∧ i₀ ≤ P.d ∧
        (∀ j < i₀, X.rebuildCount j = st.rebuildCount j) ∧
        (i₀ < P.d → X.rebuildCount i₀ = st.rebuildCount i₀ + 1) ∧
        (∀ j < idx, chStop.scState j = st.scState j ∧ chStop.bran j = st.bran j ∧
          X.scState j = st.scState j ∧ X.bran j = st.bran j) ∧
        (∀ j, idx ≤ j → j < i₀ →
          chStop.scState j = X.scState j ∧ chStop.bran j = X.bran j ∧ X.bran j = st.bran j) ∧
        (∀ j, i₀ ≤ j → j < P.d → chStop.scState j = st.scState j ∧ chStop.bran j = st.bran j) ∧
        chStop.lastLSFs = st.lastLSFs ∧ chStop.lastBran = st.lastBran ∧
        st.totalTreeUpdates +
          (Finset.Ico idx i₀).sum (fun j =>
            ((T.lsfs (st.scState j) (st.bran j)).F.F.E \
              (T.lsfs (X.scState j) (X.bran j)).F.F.E).card) ≤
          chStop.totalTreeUpdates ∧
        (i₀ < P.d →
          chStop.totalTreeUpdates +
            (diffTreeChanges chStop.toTreeChain.chainTree.E X.toTreeChain.chainTree.E).length ≤
            X.totalTreeUpdates) ∧
        (i₀ = P.d →
          chStop.totalTreeUpdates +
            (diffTreeChanges (st.lastLSFs st.lastBran).F.F.E
              (X.lastLSFs X.lastBran).F.F.E).length ≤
            X.totalTreeUpdates)
  | 0, idx, st, curG, curU, _, hsum => by
    have hidx : idx = P.d := by omega
    subst hidx
    intro X
    refine ⟨P.d, st, le_rfl, le_rfl, ?_, fun h => absurd h (by omega), ?_,
      fun _ h1 h2 => absurd h2 (by omega), fun _ h1 h2 => absurd h2 (by omega), rfl, rfl,
      by simp, fun h => absurd h (by omega), ?_⟩
    · intro j _
      by_cases hU : curU = [] <;> simp [X, Chain.Ordered.updateLoop, hU]
    · intro j _
      by_cases hU : curU = [] <;> simp [X, Chain.Ordered.updateLoop, hU]
    · intro _
      by_cases hU : curU = []
      · have hX : X = { st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' } :=
          by simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte]
        rw [hX, diffTreeChanges_length_eq]; simp [ChainState.totalTreeUpdates]
      · have hX : X = { st with
            G := fun j => if j = P.d then curG else st.G j
            lastK := (L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).1
            lastLSFs := (L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).2
            lastBran := 0, ℓ := ℓ', g := g', curLastRebuilds := st.curLastRebuilds + 1
            curLastCost := st.curLastCost + L.cost curG
            curLastTreeUpdates := st.curLastTreeUpdates +
              (diffTreeChanges (st.lastLSFs st.lastBran).F.F.E
                ((L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).2 0).F.F.E).length } :=
          by simp only [X, Chain.Ordered.updateLoop, hU, ↓reduceIte]
        rw [hX]
        unfold ChainState.totalTreeUpdates
        dsimp only
        omega
  | rem + 1, idx, st, curG, curU, curEncStep, hsum => by
    have hidxLt : idx < P.d := by omega
    intro X
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · let stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hX : X = (Chain.Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncStep).1 := by
        simp only [X, Chain.Ordered.updateLoop, hOver, ↓reduceIte, stLG]
      have hEx := ordAlgorithm1_rebuild_exact T L P stLG hidxLt (rebuildStartGraph idx curG) curEncStep
      have hSub := algorithm1_rebuild_totalTreeUpdates_eq T L P stLG hidxLt (rebuildStartGraph idx curG) curEncStep
      have hStTot : stLG.totalTreeUpdates = st.totalTreeUpdates := rfl
      have hStE : stLG.toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := by
        ext e; simp only [stLG, TreeChain.chainTree, TreeChain.chainTreeEdges,
          ChainState.toTreeChain, TreeChain.activeLSF]; rfl
      refine ⟨idx, st, le_rfl, hidxLt.le, ?_, ?_, ?_, fun _ h1 h2 => absurd h2 (by omega),
        fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl, by simp, ?_, fun h => absurd h (by omega)⟩
      · intro j hj
        rw [hX]; exact (hEx.1 j hj).2.2.2.2
      · intro _
        rw [hX, hEx.2.2.2.2.2.1 idx]; simp [stLG]
      · intro j hj
        rw [hX]
        have hp := hEx.1 j hj
        exact ⟨rfl, rfl, hp.2.1, hp.2.2.1⟩
      · intro _
        dsimp only at hSub
        rw [hStTot, hStE, ← hX] at hSub
        exact hSub
    · set Cpartial : TreeChain := { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      set upd := T.updateOrd (st.scState idx) curU (Cpartial.chainLen ℓ' idx) (Cpartial.chainGrad g' idx)
        (chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)
      set fiLen := (diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
        (T.lsfs upd.1 (st.bran idx)).F.F.E).length
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then upd.1 else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j => if j = idx + 1 then st.recUpdates (idx + 1) + (upd.2 (st.bran idx)).length else st.recUpdates j
          curFwd := fun j => if j = idx then st.curFwd idx + (upd.2 (st.bran idx)).length else st.curFwd j
          curEnc := fun j => if j = idx then st.curEnc idx + curEncStep
            else if j = idx + 1 then st.curEnc (idx + 1) + (st.G (idx + 1)).batchEnc (upd.2 (st.bran idx))
            else st.curEnc j
          curDecUpdates := fun j => if j = idx then st.curDecUpdates idx + fiLen else st.curDecUpdates j }
      have hX : X = (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) stNext
          (T.S upd.1 (st.bran idx)) (upd.2 (st.bran idx)) 0).1 := by
        simp only [X, Chain.Ordered.updateLoop, hOver, ↓reduceIte, Cpartial, upd, fiLen, stNext]
      have hStepTot : stNext.totalTreeUpdates = st.totalTreeUpdates + fiLen := by
        unfold ChainState.totalTreeUpdates
        have hmem : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidxLt
        have hSum : (Finset.range P.d).sum (fun j => stNext.curDecUpdates j) =
            (Finset.range P.d).sum (fun j => st.curDecUpdates j) + fiLen := by
          rw [← Finset.add_sum_erase _ _ hmem,
            ← Finset.add_sum_erase _ (fun j => st.curDecUpdates j) hmem]
          have hEq : ((Finset.range P.d).erase idx).sum (fun j => stNext.curDecUpdates j) =
              ((Finset.range P.d).erase idx).sum (fun j => st.curDecUpdates j) :=
            Finset.sum_congr rfl fun j hj => by
              have hne := (Finset.mem_erase.mp hj).1; simp [stNext, hne]
          rw [hEq]; simp [stNext]; omega
        dsimp only [stNext] at hSum ⊢
        omega
      obtain ⟨i₀, chStop, hi1, hi2, hrcPre, hrcAt, hLtIdx1, hMid, hGeI0, hLastL, hLastB,
        hSumRest, hExitLt, hExitEq⟩ :=
        ordUpdateLoop_treeUpdates_decomp T L TP P N₀ ℓ' g' rem (idx + 1) stNext
          (T.S upd.1 (st.bran idx)) (upd.2 (st.bran idx)) 0 (by omega)
      rw [← hX] at hrcPre hrcAt hLtIdx1 hMid hSumRest hExitLt hExitEq
      have hAtIdx := hLtIdx1 idx (Nat.lt_succ_self idx)
      have hScIdx : X.scState idx = upd.1 := by simpa [stNext] using hAtIdx.2.2.1
      have hBrIdx : X.bran idx = st.bran idx := by simpa [stNext] using hAtIdx.2.2.2
      have hChScIdx : chStop.scState idx = upd.1 := by simpa [stNext] using hAtIdx.1
      have hChBrIdx : chStop.bran idx = st.bran idx := by simpa [stNext] using hAtIdx.2.1
      refine ⟨i₀, chStop, by omega, hi2, hrcPre, hrcAt, ?_, ?_, ?_, hLastL, hLastB, ?_,
        hExitLt, hExitEq⟩
      · intro j hj
        have h := hLtIdx1 j (by omega)
        have hne : j ≠ idx := by omega
        simpa [stNext, hne] using h
      · intro j hj1 hj2
        by_cases hje : j = idx
        · subst hje; exact ⟨by rw [hChScIdx, hScIdx], by rw [hChBrIdx, hBrIdx], hBrIdx⟩
        · exact hMid j (by omega) hj2
      · intro j hj1 hj2
        have h := hGeI0 j hj1 hj2
        have hne : j ≠ idx := by omega
        simpa [stNext, hne] using h
      · have hIco : (Finset.Ico idx i₀).sum (fun j =>
            ((T.lsfs (st.scState j) (st.bran j)).F.F.E \
              (T.lsfs (X.scState j) (X.bran j)).F.F.E).card) =
            ((T.lsfs (st.scState idx) (st.bran idx)).F.F.E \
              (T.lsfs (X.scState idx) (X.bran idx)).F.F.E).card +
            (Finset.Ico (idx + 1) i₀).sum (fun j =>
              ((T.lsfs (stNext.scState j) (stNext.bran j)).F.F.E \
                (T.lsfs (X.scState j) (X.bran j)).F.F.E).card) := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : idx < i₀)]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j ≠ idx := by have := (Finset.mem_Ico.mp hj).1; omega
          simp [stNext, hne]
        have hCardLe : ((T.lsfs (st.scState idx) (st.bran idx)).F.F.E \
            (T.lsfs (X.scState idx) (X.bran idx)).F.F.E).card ≤ fiLen := by
          rw [hScIdx, hBrIdx]
          simp only [fiLen, diffTreeChanges_length_eq]
          omega
        rw [hIco]
        omega

/-- For any two finsets `oldE`, `newE` disjoint from `Fp`, the symmetric difference of
`Fp ∪ oldE` and `Fp ∪ newE` has size `(oldE \ newE).card + (newE \ oldE).card`. -/
private theorem diffTreeChanges_union_disjoint (Fp oldE newE : Finset ℕ)
    (hOld : ∀ e ∈ Fp, e ∉ oldE) (hNew : ∀ e ∈ Fp, e ∉ newE) :
    (diffTreeChanges (Fp ∪ oldE) (Fp ∪ newE)).length =
      (oldE \ newE).card + (newE \ oldE).card := by
  rw [diffTreeChanges_length_eq]
  have h1 : (Fp ∪ oldE) \ (Fp ∪ newE) = oldE \ newE := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    constructor
    · rintro ⟨(hf | ho), hnf, hnn⟩
      · exact absurd hf hnf
      · exact ⟨ho, hnn⟩
    · rintro ⟨ho, hnn⟩
      exact ⟨Or.inr ho, fun hf => hOld e hf ho, hnn⟩
  have h2 : (Fp ∪ newE) \ (Fp ∪ oldE) = newE \ oldE := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    constructor
    · rintro ⟨(hf | hn), hnf, hno⟩
      · exact absurd hf hnf
      · exact ⟨hn, hno⟩
    · rintro ⟨hn, hno⟩
      exact ⟨Or.inr hn, fun hf => hNew e hf hn, hno⟩
  rw [h1, h2]

/-- In all three Branch B exit cases, the sum of non-rebuilt forest deletions `T` plus the suffix
symmetric difference `(oldE \ newE).card + (newE \ oldE).card` is bounded by
`X.totalTreeUpdates - st0.totalTreeUpdates`. -/
theorem branchB_treeUpdates_ge_fDel_add_symmDiff
    {T : SparseCoreRestartTool} {L : LastLevelTool} {TP : SparseCoreParams} {P : ChainParams}
    {N₀ : ℕ} {ℓ' g' : ℕ → ℝ} {st0 X : ChainState T P} {G1 : MGraph} {Uint : List Update}
    {enc0 i₀ fr : ℕ} {fDel : ℕ → List ℕ}
    (hX : X = (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' P.d 0 st0 G1 Uint enc0).1)
    (hiLe : i₀ ≤ P.d)
    (hCase : (i₀ < P.d ∧ fr = i₀ ∧
        (∀ j < i₀, X.rebuildCount j = st0.rebuildCount j) ∧
        X.rebuildCount i₀ = st0.rebuildCount i₀ + 1) ∨
      (i₀ = P.d ∧ (fr = P.d ∨ fr = P.d + 1) ∧
        ∀ j < P.d, X.rebuildCount j = st0.rebuildCount j))
    (hfDel : ∀ j < i₀, (fDel j).Nodup ∧
      (fDel j).toFinset = (T.lsfs (st0.scState j) (st0.bran j)).F.F.E \
        (T.lsfs (X.scState j) (X.bran j)).F.F.E)
    (hSplit :
      let Fp := (Finset.range fr).biUnion fun j => (X.toTreeChain.activeLSF j).F.F.E
      let oldE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests st0 fr else [])
      let newE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests X fr else [])
      (∀ e ∈ Fp, e ∉ oldE) ∧ (∀ e ∈ Fp, e ∉ newE) ∧ Fp ∪ newE = X.toTreeChain.chainTree.E) :
    let oldE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests st0 fr else [])
    let newE := graphListEdgeUnion (if fr ≤ P.d then chainSuffixForests X fr else [])
    (Finset.range i₀).sum (fun j => (fDel j).length) +
      ((oldE \ newE).card + (newE \ oldE).card) ≤
      X.totalTreeUpdates - st0.totalTreeUpdates := by
  intro oldE newE
  obtain ⟨j₀, chStop, _, hjLe, hrcPre, hrcAt, _, hMid, hGe, hLastL, hLastB,
    hSumPre, hExitLt, hExitEq⟩ :=
    ordUpdateLoop_treeUpdates_decomp T L TP P N₀ ℓ' g' P.d 0 st0 G1 Uint enc0 (Nat.zero_add P.d)
  rw [← hX] at hrcPre hrcAt hMid hSumPre hExitLt hExitEq
  -- Identify `j₀ = i₀` via `rebuildCount`
  have hjEq : j₀ = i₀ := by
    rcases hCase with ⟨hiLt, _, hPre, hAt⟩ | ⟨hiEq, _, hAll⟩
    · by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := hrcAt (by omega)
        have h2 := hPre j₀ hlt
        omega
      · have h1 := hrcPre i₀ hgt
        omega
    · subst hiEq
      by_contra hne
      have h1 := hrcAt (by omega)
      have h2 := hAll j₀ (by omega)
      omega
  subst j₀
  -- Identify the prefix sum with `∑ j < i₀, (fDel j).length`
  have hPrefEq : (Finset.range i₀).sum (fun j => (fDel j).length) =
      (Finset.Ico 0 i₀).sum (fun j =>
        ((T.lsfs (st0.scState j) (st0.bran j)).F.F.E \
          (T.lsfs (X.scState j) (X.bran j)).F.F.E).card) := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjLt : j < i₀ := (Finset.mem_Ico.mp hj).2
    obtain ⟨hNd, hSet⟩ := hfDel j hjLt
    rw [← List.toFinset_card_of_nodup hNd, hSet]
  rw [← hPrefEq] at hSumPre
  rcases hCase with ⟨hiLt, hfrEq, _, _⟩ | ⟨rfl, hfrCase, _⟩
  · -- Case 1: interior rebuild at `fr = i₀ < P.d`
    subst hfrEq
    set Fp := (Finset.range fr).biUnion fun j => (X.toTreeChain.activeLSF j).F.F.E
    have hChStopE : chStop.toTreeChain.chainTree.E = Fp ∪ oldE := by
      ext e
      rw [mem_chainTree_iff, Finset.mem_union, Finset.mem_biUnion, mem_suffixUnion_iff]
      constructor
      · rintro ⟨j, hj, he⟩
        by_cases hlt : j < fr
        · refine Or.inl ⟨j, Finset.mem_range.mpr hlt, ?_⟩
          have ⟨hsc, hbr, _⟩ := hMid j (Nat.zero_le j) hlt
          simpa [ChainState.toTreeChain, TreeChain.activeLSF, show j < P.d by omega, hsc, hbr] using he
        · refine Or.inr ⟨j, by omega, hj, ?_⟩
          by_cases hjd : j < P.d
          · have ⟨hsc, hbr⟩ := hGe j (by omega) hjd
            simpa [ChainState.toTreeChain, TreeChain.activeLSF, hjd, hsc, hbr] using he
          · have hjeq : j = P.d := by omega
            subst hjeq
            simpa [ChainState.toTreeChain, TreeChain.activeLSF, hLastL, hLastB] using he
      · rintro (⟨j, hj, he⟩ | ⟨j, hj1, hj2, he⟩)
        · have hlt := Finset.mem_range.mp hj
          have ⟨hsc, hbr, _⟩ := hMid j (Nat.zero_le j) hlt
          refine ⟨j, by omega, ?_⟩
          simpa [ChainState.toTreeChain, TreeChain.activeLSF, show j < P.d by omega, hsc, hbr] using he
        · refine ⟨j, hj2, ?_⟩
          by_cases hjd : j < P.d
          · have ⟨hsc, hbr⟩ := hGe j hj1 hjd
            simpa [ChainState.toTreeChain, TreeChain.activeLSF, hjd, hsc, hbr] using he
          · have hjeq : j = P.d := by omega
            subst hjeq
            simpa [ChainState.toTreeChain, TreeChain.activeLSF, hLastL, hLastB] using he
    have hDiff := hExitLt hiLt
    rw [hChStopE, ← hSplit.2.2, diffTreeChanges_union_disjoint Fp oldE newE hSplit.1 hSplit.2.1] at hDiff
    omega
  · -- Cases 2 and 3: `i₀ = P.d`
    have hDiff := hExitEq rfl
    rcases hfrCase with rfl | rfl
    · -- Case 2: `fr = P.d`
      have hOldE : oldE = (st0.lastLSFs st0.lastBran).F.F.E := by
        ext e; rw [mem_suffixUnion_iff]
        constructor
        · rintro ⟨j, h1, h2, he⟩
          have hj : j = P.d := by omega
          subst hj; simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he
        · intro he
          exact ⟨P.d, le_rfl, le_rfl, by simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he⟩
      have hNewE : newE = (X.lastLSFs X.lastBran).F.F.E := by
        ext e; rw [mem_suffixUnion_iff]
        constructor
        · rintro ⟨j, h1, h2, he⟩
          have hj : j = P.d := by omega
          subst hj; simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he
        · intro he
          exact ⟨P.d, le_rfl, le_rfl, by simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he⟩
      rw [hOldE, hNewE, ← diffTreeChanges_length_eq]
      omega
    · -- Case 3: `fr = P.d + 1`
      have hOldE : oldE = ∅ := by
        simp [oldE, graphListEdgeUnion]
      have hNewE : newE = ∅ := by
        simp [newE, graphListEdgeUnion]
      rw [hOldE, hNewE]
      simp only [Finset.sdiff_self, Finset.card_empty, add_zero]
      omega

/-! ### 3. Pure `ℕ` cost arithmetic helpers -/

/-- Compares `branchBStepCostKFBL + 4` to `updateCoreNoRebuildStepCost + 30` plus the per-level
copy costs `20 * fDelLen + 20 * reembLen`. -/
theorem branchB_stepCost_le_noRebuild (L capExp : ℕ) (Psc : SparseCoreOrdParams)
    (k M N bW eW Δc nU fDelLen reembLen : ℕ) :
    branchBStepCostKFBL L capExp Psc k M N bW eW Δc nU fDelLen reembLen + 4 ≤
      (updateCoreNoRebuildStepCost L capExp Psc k M N bW eW nU Δc + 30) +
        20 * fDelLen + 20 * reembLen := by
  unfold branchBStepCostKFBL updateCoreNoRebuildStepCost
  dsimp only
  omega

/-- Pure `ℕ` assembly for Case 1 (interior rebuild at `0 < i₀ < d`, `fr = i₀`). -/
theorem branchB_cost_case1_arith
    {cost c0 cP cF cL cX cS u d i₀ L du syncE refOne bW0 bWE bWi0 stepSum T Rsum Δon S
      ro mulTerm lvlSum lastTerm phiTreeEnd phiTree1 phiTree0 phiCoreEnd phiCoreE phiCore0
      offEnd off1 off0 treeMul rhs : ℕ}
    (hCost : cost ≤ c0 + cP + cF + cL + cX + cS + 12)
    (hc0 : c0 ≤ 210)
    (hcP : cP + (phiTree1 + off1 * du) ≤
      35 + 2 * (50 * u + 45) + (u * (syncE + 2) + 90 * u + 230) +
        ((u * (refOne + 120) + 71 * L + 210) + (u * (17 * L + 70) + 80)) + 4 +
        (phiTree0 + off0 * du))
    (hcF : cF ≤ 20 * bW0 + 60) (hbW0 : bW0 ≤ 4 * u + 1)
    (hcL : cL + phiCoreE ≤ stepSum + 20 * T + 20 * Rsum + 32 + phiCore0)
    (hcX : cX + phiCoreEnd ≤
      2 * ((d - i₀) * (ro + 48)) + 670 * bWE + mulTerm + lvlSum + lastTerm +
        ro + 15 * (d - i₀) + 413 + phiCoreE)
    (hbWE : bWE ≤ bWi0)
    (hcS : cS + (phiTreeEnd + offEnd * du) ≤
      T * (syncE + 2) + 40 * T + 64 * i₀ + 175 + Δon * (syncE + 2) + 155 * S +
        210 * (d + 1 - i₀) + 350 + (160 * u + 60 + u * du) + 20 + (phiTree1 + off1 * du))
    (hiLe : i₀ ≤ d)
    (hTotal :
      (134 * u + 65) + u * (syncE + 2) + (u * (refOne + 120) + 71 * L + 220) +
        (670 * (4 * u + 1) + 30) + (u * (17 * L + 70) + 80) + stepSum +
        (130 * u + u * du + 100) + 100 * d + 1000 +
        670 * bWi0 + mulTerm + 2 * ro + 200 + lvlSum + lastTerm +
        2 * d * (ro + 68) + (230 * (d + 1) + 85 * S + 260) + 70 * S + 300 ≤ rhs)
    (hTreeMul : syncE + 62 ≤ treeMul)
    {Δtu : ℕ} (hTU : T + Δon ≤ Δtu) :
    cost + (phiTreeEnd + phiCoreEnd + offEnd * du) ≤
      rhs + treeMul * Δtu + 40 * Rsum + (phiTree0 + phiCore0 + off0 * du) := by
  have hro : 2 * ((d - i₀) * (ro + 48)) + 15 * (d - i₀) + 210 * (d + 1 - i₀) ≤
      2 * d * (ro + 68) + 230 * (d + 1) := by
    have h1 : (d - i₀) * (ro + 48) ≤ d * (ro + 48) := Nat.mul_le_mul_right _ (Nat.sub_le d i₀)
    have h2 : 2 * (d * (ro + 48)) = 2 * d * ro + 96 * d := by ring
    have h3 : 2 * d * (ro + 68) = 2 * d * ro + 136 * d := by ring
    omega
  have hTree : 20 * T + T * (syncE + 2) + 40 * T + Δon * (syncE + 2) ≤ treeMul * Δtu := by
    have h1 : 20 * T + T * (syncE + 2) + 40 * T = T * (syncE + 62) := by ring
    have h2 : Δon * (syncE + 2) ≤ Δon * (syncE + 62) := Nat.mul_le_mul_left _ (by omega)
    have h3 : T * (syncE + 62) + Δon * (syncE + 62) = (syncE + 62) * (T + Δon) := by ring
    exact (by omega : 20 * T + T * (syncE + 2) + 40 * T + Δon * (syncE + 2) ≤
      (syncE + 62) * (T + Δon)).trans (Nat.mul_le_mul hTreeMul hTU)
  have h670 : 670 * bWE ≤ 670 * bWi0 := Nat.mul_le_mul_left 670 hbWE
  have h64 : 64 * i₀ ≤ 100 * d := by omega
  omega

/-- Pure `ℕ` assembly for Case 2 (non-empty terminal exit at `i₀ = d`, `fr = d`). -/
theorem branchB_cost_case2_arith
    {cost c0 cP cF cL cX cS u d L du syncE refOne bW0 stepSum T Rsum Δon S
      ro copyG lenTerm mulTerm lastTerm phiTreeEnd phiTree1 phiTree0 phiCoreEnd phiCoreE phiCore0
      offEnd off1 off0 treeMul rhs : ℕ}
    (hCost : cost ≤ c0 + cP + cF + cL + cX + cS + 12)
    (hc0 : c0 ≤ 210)
    (hcP : cP + (phiTree1 + off1 * du) ≤
      35 + 2 * (50 * u + 45) + (u * (syncE + 2) + 90 * u + 230) +
        ((u * (refOne + 120) + 71 * L + 210) + (u * (17 * L + 70) + 80)) + 4 +
        (phiTree0 + off0 * du))
    (hcF : cF ≤ 20 * bW0 + 60) (hbW0 : bW0 ≤ 4 * u + 1)
    (hcL : cL + phiCoreE ≤ stepSum + 20 * T + 20 * Rsum + 32 + phiCore0)
    (hcX : cX + phiCoreEnd ≤
      3 * ro + copyG + lenTerm + mulTerm + lastTerm + 360 + 36 + phiCoreE)
    (hcS : cS + (phiTreeEnd + offEnd * du) ≤
      T * (syncE + 2) + 40 * T + 64 * d + 175 + Δon * (syncE + 2) + 155 * S +
        210 * (d + 1 - d) + 350 + (160 * u + 60 + u * du) + 20 + (phiTree1 + off1 * du))
    (hTotal :
      (134 * u + 65) + u * (syncE + 2) + (u * (refOne + 120) + 71 * L + 220) +
        (670 * (4 * u + 1) + 30) + (u * (17 * L + 70) + 80) + stepSum +
        (130 * u + u * du + 100) + 100 * d + 1000 +
        3 * ro + copyG + lenTerm + mulTerm + lastTerm +
        (230 * 2 + 85 * S + 260) + 70 * S + 400 ≤ rhs)
    (hTreeMul : syncE + 62 ≤ treeMul)
    {Δtu : ℕ} (hTU : T + Δon ≤ Δtu) :
    cost + (phiTreeEnd + phiCoreEnd + offEnd * du) ≤
      rhs + treeMul * Δtu + 40 * Rsum + (phiTree0 + phiCore0 + off0 * du) := by
  have hTree : 20 * T + T * (syncE + 2) + 40 * T + Δon * (syncE + 2) ≤ treeMul * Δtu := by
    have h1 : 20 * T + T * (syncE + 2) + 40 * T = T * (syncE + 62) := by ring
    have h2 : Δon * (syncE + 2) ≤ Δon * (syncE + 62) := Nat.mul_le_mul_left _ (by omega)
    have h3 : T * (syncE + 62) + Δon * (syncE + 62) = (syncE + 62) * (T + Δon) := by ring
    exact (by omega : 20 * T + T * (syncE + 2) + 40 * T + Δon * (syncE + 2) ≤
      (syncE + 62) * (T + Δon)).trans (Nat.mul_le_mul hTreeMul hTU)
  omega

/-- Pure `ℕ` assembly for Case 3 (empty terminal exit at `i₀ = d`, `fr = d + 1`). -/
theorem branchB_cost_case3_arith
    {cost c0 cP cF cL cX cS u d L du syncE refOne bW0 stepSum T Rsum
      phiTreeEnd phiTree1 phiTree0 phiCoreEnd phiCoreE phiCore0
      offEnd off1 off0 treeMul rhs : ℕ}
    (hCost : cost ≤ c0 + cP + cF + cL + cX + cS + 12)
    (hc0 : c0 ≤ 210)
    (hcP : cP + (phiTree1 + off1 * du) ≤
      35 + 2 * (50 * u + 45) + (u * (syncE + 2) + 90 * u + 230) +
        ((u * (refOne + 120) + 71 * L + 210) + (u * (17 * L + 70) + 80)) + 4 +
        (phiTree0 + off0 * du))
    (hcF : cF ≤ 20 * bW0 + 60) (hbW0 : bW0 ≤ 4 * u + 1)
    (hcL : cL + phiCoreE ≤ stepSum + 20 * T + 20 * Rsum + 32 + phiCore0)
    (hcX : cX ≤ 44) (hPhiCore : phiCoreEnd = phiCoreE)
    (hcS : cS + (phiTreeEnd + offEnd * du) ≤
      T * (syncE + 2) + 40 * T + 64 * d + 175 + 0 * (syncE + 2) + 155 * 0 +
        210 * (d + 1 - (d + 1)) + 350 + (160 * u + 60 + u * du) + 20 + (phiTree1 + off1 * du))
    (hTotal :
      (134 * u + 65) + u * (syncE + 2) + (u * (refOne + 120) + 71 * L + 220) +
        (670 * (4 * u + 1) + 30) + (u * (17 * L + 70) + 80) + stepSum +
        (130 * u + u * du + 100) + 100 * d + 1000 + 600 ≤ rhs)
    (hTreeMul : syncE + 62 ≤ treeMul)
    {Δtu : ℕ} (hTU : T ≤ Δtu) :
    cost + (phiTreeEnd + phiCoreEnd + offEnd * du) ≤
      rhs + treeMul * Δtu + 40 * Rsum + (phiTree0 + phiCore0 + off0 * du) := by
  have hTree : 20 * T + T * (syncE + 2) + 40 * T ≤ treeMul * Δtu := by
    have h1 : 20 * T + T * (syncE + 2) + 40 * T = (syncE + 62) * T := by ring
    rw [h1]
    exact Nat.mul_le_mul hTreeMul hTU
  omega

end MinCostFlow.MinRatio
