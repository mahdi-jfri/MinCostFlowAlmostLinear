module

public import MinCostFlow.MinRatio.WireChainAlgebra
public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.Chain.Ordered.RenameFacts
public import MinCostFlow.IPM.Machine.MinRatioContract
import WordRAM.Tactic

/-!
# Algebraic lemmas for ordered chain update (`WireChainCoreAlgebra`)

Provides the pure model-level lemmas used to verify `ordChainUpdateCoreBody`:
1. `ToolUpdateOrdEqOnE` and `sparseCoreBundleRestartTool_updateOrdEqOnE`: `updateOrd` of
   `sparseCoreBundleRestartTool` is independent of the length/gradient arguments.
2. Finset symmetric-difference bounds for `diffTreeChanges` (`diffTreeChanges_triangle`,
   `diffTreeChanges_union_right_le`, `diffTreeChanges_union_left_le`).
3. Step-by-step `totalRuntime` and `totalTreeUpdates` accounting for `Chain.Ordered.updateLoop`
   and `Chain.Ordered.algorithm1_update`, including the unconditional bound
   `(diffTreeChanges st.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length ≤
     next.totalTreeUpdates - st.totalTreeUpdates`.
4. `RefreshBatch` + `translateBatch` edge-correspondence lemmas characterizing unchanged vs.
   replaced edges and uniqueness of old-ID deletions in `U_int`.
5. `filterActiveEdits` and `treeEditDiff_filterActive`: restricting `TreeEditDifference oldE newE`
   to `midE = oldE ∩ G'.E` when `newE ⊆ G'.E` and `oldE \ midE` have already been cut.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.IPM.Machine

/-! ### 1. Length/gradient independence of `T.updateOrd` -/

/-- `T.updateOrd` depends only on the state, batch, and output order (independent of the length and
gradient arguments). Holds definitionally for `sparseCoreBundleRestartTool`. -/
@[expose] def ToolUpdateOrdEqOnE (T : SparseCoreRestartTool) : Prop :=
  ∀ (st : T.State) (U : List Update) (len len' grad grad' : ℕ → ℝ) (ord : ℕ → List End),
    T.updateOrd st U len grad ord = T.updateOrd st U len' grad' ord

theorem sparseCoreBundleRestartTool_updateOrdEqOnE
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut) :
    ToolUpdateOrdEqOnE (sparseCoreBundleRestartTool oracle C_lsst L sparsify) :=
  fun _ _ _ _ _ _ _ => rfl

/-! ### 2. `diffTreeChanges` symmetric-difference bounds -/

theorem diffTreeChanges_length_eq (E₁ E₂ : Finset ℕ) :
    (diffTreeChanges E₁ E₂).length = (E₁ \ E₂).card + (E₂ \ E₁).card := by
  simp [diffTreeChanges]

theorem diffTreeChanges_triangle (E₁ E₂ E₃ : Finset ℕ) :
    (diffTreeChanges E₁ E₃).length ≤
      (diffTreeChanges E₁ E₂).length + (diffTreeChanges E₂ E₃).length := by
  rw [diffTreeChanges_length_eq, diffTreeChanges_length_eq, diffTreeChanges_length_eq]
  have h1 : E₁ \ E₃ ⊆ (E₁ \ E₂) ∪ (E₂ \ E₃) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    by_cases h2 : x ∈ E₂
    · exact Or.inr ⟨h2, hx.2⟩
    · exact Or.inl ⟨hx.1, h2⟩
  have h2 : E₃ \ E₁ ⊆ (E₃ \ E₂) ∪ (E₂ \ E₁) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
    by_cases hm : x ∈ E₂
    · exact Or.inr ⟨hm, hx.2⟩
    · exact Or.inl ⟨hx.1, hm⟩
  have hc1 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  have hc2 := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
  omega

theorem diffTreeChanges_union_right_le (A B C : Finset ℕ) :
    (diffTreeChanges (A ∪ C) (B ∪ C)).length ≤ (diffTreeChanges A B).length := by
  rw [diffTreeChanges_length_eq, diffTreeChanges_length_eq]
  have h1 : (A ∪ C) \ (B ∪ C) ⊆ A \ B := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
    exact ⟨hx.1.resolve_right hx.2.2, hx.2.1⟩
  have h2 : (B ∪ C) \ (A ∪ C) ⊆ B \ A := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
    exact ⟨hx.1.resolve_right hx.2.2, hx.2.1⟩
  have hc1 := Finset.card_le_card h1
  have hc2 := Finset.card_le_card h2
  omega

theorem diffTreeChanges_union_left_le (C A B : Finset ℕ) :
    (diffTreeChanges (C ∪ A) (C ∪ B)).length ≤ (diffTreeChanges A B).length := by
  rw [Finset.union_comm C A, Finset.union_comm C B]
  exact diffTreeChanges_union_right_le A B C

/-! ### 3. `updateLoop` / `algorithm1_update` runtime and tree-update accounting -/

private theorem chainTree_E_split_at {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) {j : ℕ} (hj : j < P.d + 1) :
    st.toTreeChain.chainTree.E =
      ((Finset.range (P.d + 1)).erase j).biUnion (fun r => (st.toTreeChain.activeLSF r).F.F.E) ∪
        (st.toTreeChain.activeLSF j).F.F.E := by
  ext e
  simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨r, hr, he⟩
    by_cases h : r = j
    · subst h; exact Or.inr he
    · exact Or.inl ⟨r, ⟨h, hr⟩, he⟩
  · rintro (⟨r, ⟨_, hr⟩, he⟩ | he)
    · exact ⟨r, hr, he⟩
    · exact ⟨j, hj, he⟩

/-- Changing only `scState idx` (`idx < P.d`) changes `chainTree.E` by at most
`diffTreeChanges (old active LSF at idx) (new active LSF at idx)`. -/
theorem diffTreeChanges_update_scState_le {T : SparseCoreRestartTool} {P : ChainParams}
    (st st' : ChainState T P) {idx : ℕ} (hidx : idx < P.d)
    (hSc : ∀ r < P.d, r ≠ idx → st'.scState r = st.scState r)
    (hBr : ∀ r < P.d, st'.bran r = st.bran r)
    (hLast : st'.lastLSFs = st.lastLSFs ∧ st'.lastBran = st.lastBran) :
    (diffTreeChanges st.toTreeChain.chainTree.E st'.toTreeChain.chainTree.E).length ≤
      (diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
        (T.lsfs (st'.scState idx) (st.bran idx)).F.F.E).length := by
  rw [chainTree_E_split_at st (j := idx) (by omega), chainTree_E_split_at st' (j := idx) (by omega)]
  have hOther :
      ((Finset.range (P.d + 1)).erase idx).biUnion (fun r => (st'.toTreeChain.activeLSF r).F.F.E) =
      ((Finset.range (P.d + 1)).erase idx).biUnion (fun r => (st.toTreeChain.activeLSF r).F.F.E) := by
    refine Finset.biUnion_congr rfl (fun r hr => ?_)
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hr
    have hlt' := Finset.mem_range.mp hlt
    by_cases hrd : r < P.d
    · simp only [ChainState.toTreeChain, TreeChain.activeLSF, hrd, ↓reduceIte, hSc r hrd hne, hBr r hrd]
    · simp only [ChainState.toTreeChain, TreeChain.activeLSF, hrd, ↓reduceIte, hLast.1, hLast.2]
  rw [hOther]
  have hA1 : (st.toTreeChain.activeLSF idx).F.F.E = (T.lsfs (st.scState idx) (st.bran idx)).F.F.E := by
    simp [ChainState.toTreeChain, TreeChain.activeLSF, hidx]
  have hA2 : (st'.toTreeChain.activeLSF idx).F.F.E = (T.lsfs (st'.scState idx) (st.bran idx)).F.F.E := by
    simp [ChainState.toTreeChain, TreeChain.activeLSF, hidx, hBr idx hidx]
  rw [hA1, hA2]
  exact diffTreeChanges_union_left_le _ _ _

/-- Changing only `(lastLSFs, lastBran)` changes `chainTree.E` by at most
`diffTreeChanges oldLast newLast`. -/
theorem diffTreeChanges_update_last_le {T : SparseCoreRestartTool} {P : ChainParams}
    (st st' : ChainState T P)
    (hSc : ∀ r < P.d, st'.scState r = st.scState r)
    (hBr : ∀ r < P.d, st'.bran r = st.bran r) :
    (diffTreeChanges st.toTreeChain.chainTree.E st'.toTreeChain.chainTree.E).length ≤
      (diffTreeChanges (st.lastLSFs st.lastBran).F.F.E (st'.lastLSFs st'.lastBran).F.F.E).length := by
  rw [chainTree_E_split_at st (Nat.lt_succ_self P.d), chainTree_E_split_at st' (Nat.lt_succ_self P.d)]
  have hOther :
      ((Finset.range (P.d + 1)).erase P.d).biUnion (fun r => (st'.toTreeChain.activeLSF r).F.F.E) =
      ((Finset.range (P.d + 1)).erase P.d).biUnion (fun r => (st.toTreeChain.activeLSF r).F.F.E) := by
    refine Finset.biUnion_congr rfl (fun r hr => ?_)
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hr
    have hrd : r < P.d := by have := Finset.mem_range.mp hlt; omega
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hrd, ↓reduceIte, hSc r hrd, hBr r hrd]
  rw [hOther]
  have hA1 : (st.toTreeChain.activeLSF P.d).F.F.E = (st.lastLSFs st.lastBran).F.F.E := by
    simp [ChainState.toTreeChain, TreeChain.activeLSF]
  have hA2 : (st'.toTreeChain.activeLSF P.d).F.F.E = (st'.lastLSFs st'.lastBran).F.F.E := by
    simp [ChainState.toTreeChain, TreeChain.activeLSF]
  rw [hA1, hA2]
  exact diffTreeChanges_union_left_le _ _ _

/-- `updateLoop` monotonically increases `totalTreeUpdates` and its `totalTreeUpdates` rise
dominates `(diffTreeChanges oldChainTree.E newChainTree.E).length`. -/
theorem ordUpdateLoop_treeUpdates_bound (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      idx + rem = P.d →
      let st' := (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
      st.totalTreeUpdates ≤ st'.totalTreeUpdates ∧
      (diffTreeChanges st.toTreeChain.chainTree.E st'.toTreeChain.chainTree.E).length ≤
        st'.totalTreeUpdates - st.totalTreeUpdates
  | 0, idx, st, curG, curU, _, _ => by
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs with hU
    · refine ⟨le_rfl, ?_⟩
      have hE : ({ st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' } :
          ChainState T P).toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := by
        ext e; simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain,
          TreeChain.activeLSF]; rfl
      rw [hE, diffTreeChanges_length_eq]; simp
    · let st' : ChainState T P :=
        { st with
          G := fun j => if j = P.d then curG else st.G j
          lastK := (L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).1
          lastLSFs := (L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).2
          lastBran := 0, ℓ := ℓ', g := g', curLastRebuilds := st.curLastRebuilds + 1
          curLastCost := st.curLastCost + L.cost curG
          curLastTreeUpdates := st.curLastTreeUpdates +
            (diffTreeChanges (st.lastLSFs st.lastBran).F.F.E
              ((L.build curG ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }.chainLen ℓ' P.d)).2 0).F.F.E).length }
      have hTot : st'.totalTreeUpdates = st.totalTreeUpdates +
          (diffTreeChanges (st.lastLSFs st.lastBran).F.F.E (st'.lastLSFs st'.lastBran).F.F.E).length := by
        unfold ChainState.totalTreeUpdates; dsimp only [st']; omega
      have hle := diffTreeChanges_update_last_le st st' (fun _ _ => rfl) (fun _ _ => rfl)
      change st.totalTreeUpdates ≤ st'.totalTreeUpdates ∧
        (diffTreeChanges st.toTreeChain.chainTree.E st'.toTreeChain.chainTree.E).length ≤
          st'.totalTreeUpdates - st.totalTreeUpdates
      omega
  | rem + 1, idx, st, curG, curU, curEncStep, hsum => by
    dsimp only [Chain.Ordered.updateLoop]
    have hidxLt : idx < P.d := by omega
    split_ifs with hOver
    · let stWithLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hSub := rebuild_totalTreeUpdates_sub T L P stWithLG hidxLt (rebuildStartGraph idx curG) curEncStep
      have hStTot : stWithLG.totalTreeUpdates = st.totalTreeUpdates := rfl
      have hStE : stWithLG.toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := by
        ext e; simp only [stWithLG, TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain,
          TreeChain.activeLSF]; rfl
      have hMono : stWithLG.totalTreeUpdates ≤
          (Chain.Ordered.algorithm1_rebuild T L P stWithLG idx (rebuildStartGraph idx curG) curEncStep).1.totalTreeUpdates := by
        set next := (Chain.Ordered.algorithm1_rebuild T L P stWithLG idx (rebuildStartGraph idx curG) curEncStep).1
        set G0 := fun j => if j = idx then rebuildStartGraph idx curG else stWithLG.G j
        set res := Chain.Ordered.rebuildSuffix T L P stWithLG.lvlM stWithLG.N₀ stWithLG.ℓ stWithLG.g
          (P.d - idx) idx G0 stWithLG.scState stWithLG.bran stWithLG.updCount stWithLG.curEnc
          stWithLG.curDecUpdates stWithLG.curFwd
        obtain ⟨hEDpre, hEDzero, _⟩ := ordRebuildSuffix_extra T L P stWithLG.lvlM stWithLG.N₀
          stWithLG.ℓ stWithLG.g (P.d - idx) idx (by omega) G0 stWithLG.scState stWithLG.bran
          stWithLG.updCount stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
        have hDec : ∀ m, next.curDecUpdates m = res.2.2.2.2.2.1 m := fun m => by
          simp only [next, Chain.Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte, res, G0]
        have hOldS : (Finset.range P.d).sum (fun j => stWithLG.curDecUpdates j) =
            (Finset.range idx).sum (fun j => stWithLG.curDecUpdates j) +
            (Finset.Ico idx P.d).sum (fun j => stWithLG.curDecUpdates j) := by
          rw [← Finset.sum_union]
          · congr 1; ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
          · rw [Finset.disjoint_left]; intro x h1 h2
            simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
        have hNewS : (Finset.range P.d).sum (fun j => next.curDecUpdates j) =
            (Finset.range idx).sum (fun j => stWithLG.curDecUpdates j) := by
          rw [show Finset.range P.d = Finset.range idx ∪ Finset.Ico idx P.d by
            ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega,
            Finset.sum_union (by rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; omega)]
          have h1 : (Finset.range idx).sum (fun j => next.curDecUpdates j) =
              (Finset.range idx).sum (fun j => stWithLG.curDecUpdates j) :=
            Finset.sum_congr rfl (fun j hj => by rw [hDec j, (hEDpre j (Finset.mem_range.mp hj)).2])
          have h2 : (Finset.Ico idx P.d).sum (fun j => next.curDecUpdates j) = 0 :=
            Finset.sum_eq_zero (fun j hj => by
              obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj; rw [hDec j, (hEDzero j h1 (by omega)).2])
          rw [h1, h2, add_zero]
        have hCl : next.closedTreeUpdates = stWithLG.closedTreeUpdates +
            (Finset.Ico idx P.d).sum (fun j => stWithLG.curDecUpdates j) + stWithLG.curLastTreeUpdates +
            (diffTreeChanges stWithLG.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
          simp only [next, Chain.Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]; rfl
        unfold ChainState.totalTreeUpdates
        rw [hCl, hOldS, hNewS]
        omega
      dsimp only at hSub hMono
      rw [hStTot, hStE] at hSub
      rw [hStTot] at hMono
      exact ⟨hMono, by dsimp only [stWithLG] at hSub ⊢; omega⟩
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
      have hStepTot : stNext.totalTreeUpdates = st.totalTreeUpdates + fiLen := by
        unfold ChainState.totalTreeUpdates
        have hSum : (Finset.range P.d).sum (fun j => stNext.curDecUpdates j) =
            (Finset.range P.d).sum (fun j => st.curDecUpdates j) + fiLen := by
          have hmem : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidxLt
          rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ (fun j => st.curDecUpdates j) hmem]
          have hEq : ((Finset.range P.d).erase idx).sum (fun j => stNext.curDecUpdates j) =
              ((Finset.range P.d).erase idx).sum (fun j => st.curDecUpdates j) :=
            Finset.sum_congr rfl (fun j hj => by
              have hne := (Finset.mem_erase.mp hj).1; simp [stNext, hne])
          rw [hEq]; simp [stNext]; omega
        dsimp only [stNext] at hSum ⊢
        omega
      have hStepDiff : (diffTreeChanges st.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E).length ≤ fiLen := by
        have h1 := diffTreeChanges_update_scState_le st stNext hidxLt
          (fun r _ hne => by simp [stNext, hne]) (fun _ _ => rfl) ⟨rfl, rfl⟩
        simpa [stNext, fiLen] using h1
      set res := Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) stNext
        (T.S upd.1 (st.bran idx)) (upd.2 (st.bran idx)) 0
      obtain ⟨hMonoRest, hDiffRest⟩ := ordUpdateLoop_treeUpdates_bound T L TP P N₀ ℓ' g'
        rem (idx + 1) stNext (T.S upd.1 (st.bran idx)) (upd.2 (st.bran idx)) 0 (by omega)
      have hTri := diffTreeChanges_triangle st.toTreeChain.chainTree.E
        stNext.toTreeChain.chainTree.E res.1.toTreeChain.chainTree.E
      change st.totalTreeUpdates ≤ res.1.totalTreeUpdates ∧
        (diffTreeChanges st.toTreeChain.chainTree.E res.1.toTreeChain.chainTree.E).length ≤
          res.1.totalTreeUpdates - st.totalTreeUpdates
      dsimp only [res] at hMonoRest hDiffRest hTri ⊢
      omega

/-- For `algorithm1_update`, `totalTreeUpdates` never falls and its rise dominates
`(diffTreeChanges oldChainTree.E newChainTree.E).length`. -/
theorem ordAlgorithm1_update_treeUpdates_bound (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) :
    let next := (Chain.Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    st.totalTreeUpdates ≤ next.totalTreeUpdates ∧
    (diffTreeChanges st.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length ≤
      next.totalTreeUpdates - st.totalTreeUpdates := by
  dsimp only [Chain.Ordered.algorithm1_update]
  exact ordUpdateLoop_treeUpdates_bound T L TP P N₀ ℓ' g' P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (Nat.zero_add P.d)

/-- Step-level `totalRuntime` equality for one non-rebuild iteration of `updateLoop` at `idx < P.d`. -/
theorem updateLoop_step_totalRuntime_eq {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) {idx : ℕ} (hidx : idx < P.d)
    (curG : MGraph) (sc' : T.State) (curU nextU : List Update)
    (curEncStep nextEnc fiLen : ℕ)
    (hCostLe : T.cost (st.scState idx) ≤ T.cost sc') :
    let stNext : ChainState T P :=
      { st with
        G := fun j => if j = idx then curG else st.G j
        scState := fun j => if j = idx then sc' else st.scState j
        updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
        recUpdates := fun j => if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
        curFwd := fun j => if j = idx then st.curFwd idx + nextU.length else st.curFwd j
        curEnc := fun j => if j = idx then st.curEnc idx + curEncStep
          else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
          else st.curEnc j
        curDecUpdates := fun j => if j = idx then st.curDecUpdates idx + fiLen else st.curDecUpdates j }
    stNext.totalRuntime = st.totalRuntime + (T.cost sc' - T.cost (st.scState idx)) + curEncStep +
      (if idx + 1 < P.d then nextEnc else 0) := by
  dsimp only
  unfold ChainState.totalRuntime
  have hmemIdx : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidx
  have hSum :
      (Finset.range P.d).sum (fun j =>
        T.cost (if j = idx then sc' else st.scState j) +
        (if j = idx then st.curEnc idx + curEncStep
         else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc else st.curEnc j)) =
      (Finset.range P.d).sum (fun j => T.cost (st.scState j) + st.curEnc j) +
        (T.cost sc' - T.cost (st.scState idx)) + curEncStep +
        (if idx + 1 < P.d then nextEnc else 0) := by
    rw [← Finset.add_sum_erase _ _ hmemIdx, ← Finset.add_sum_erase _ (fun j => T.cost (st.scState j) + st.curEnc j) hmemIdx]
    simp only [↓reduceIte]
    by_cases h1 : idx + 1 < P.d
    · have hmem1 : idx + 1 ∈ (Finset.range P.d).erase idx :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr h1⟩
      rw [← Finset.add_sum_erase _ _ hmem1,
        ← Finset.add_sum_erase _ (fun j => T.cost (st.scState j) + st.curEnc j) hmem1]
      have hRest :
          (((Finset.range P.d).erase idx).erase (idx + 1)).sum (fun j =>
            T.cost (if j = idx then sc' else st.scState j) +
            (if j = idx then st.curEnc idx + curEncStep
             else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc else st.curEnc j)) =
          (((Finset.range P.d).erase idx).erase (idx + 1)).sum (fun j => T.cost (st.scState j) + st.curEnc j) :=
        Finset.sum_congr rfl (fun j hj => by
          have hne1 := (Finset.mem_erase.mp hj).1
          have hne0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          simp [hne0, hne1])
      rw [hRest, ite_eq_left h1]
      simp only [show idx + 1 ≠ idx by omega, ↓reduceIte]
      omega
    · have hRest :
          ((Finset.range P.d).erase idx).sum (fun j =>
            T.cost (if j = idx then sc' else st.scState j) +
            (if j = idx then st.curEnc idx + curEncStep
             else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc else st.curEnc j)) =
          ((Finset.range P.d).erase idx).sum (fun j => T.cost (st.scState j) + st.curEnc j) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne0, hlt⟩ := Finset.mem_erase.mp hj
          have hlt' := Finset.mem_range.mp hlt
          have hne1 : j ≠ idx + 1 := by omega
          simp [hne0, hne1])
      rw [hRest, ite_eq_right h1]
      omega
  dsimp only
  omega

/-- Monotonicity of `totalRuntime` across `algorithm1_rebuild` (`i₀ < P.d`). -/
theorem algorithm1_rebuild_totalRuntime_le (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    chain.totalRuntime ≤ (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1.totalRuntime := by
  set next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
  set G0 := fun j => if j = i₀ then Gnew else chain.G j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
    G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨_, hSBpre, _⟩ := ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ
    chain.g (P.d - i₀) i₀ (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc
    chain.curDecUpdates chain.curFwd
  obtain ⟨hEDpre, hEDzero, _⟩ := ordRebuildSuffix_extra T L P chain.lvlM chain.N₀ chain.ℓ
    chain.g (P.d - i₀) i₀ (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc
    chain.curDecUpdates chain.curFwd
  have hSc : ∀ m, next.scState m = res.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hEnc : ∀ m, next.curEnc m = res.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hSplit (f : ℕ → ℕ) : (Finset.range P.d).sum f = (Finset.range i₀).sum f + (Finset.Ico i₀ P.d).sum f := by
    rw [← Finset.sum_union]
    · congr 1; ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    · rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; omega
  have hNewPre : (Finset.range i₀).sum (fun j => T.cost (next.scState j) + next.curEnc j) =
      (Finset.range i₀).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) :=
    Finset.sum_congr rfl (fun j hj => by
      have hlt := Finset.mem_range.mp hj
      rw [hSc j, hEnc j, (hSBpre j hlt).1, (hEDpre j hlt).1])
  have hCl : next.closedRuntime = chain.closedRuntime +
      (Finset.Ico i₀ P.d).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
      chain.curLastCost + extraEnc := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  unfold ChainState.totalRuntime
  rw [hCl, hSplit (fun j => T.cost (chain.scState j) + chain.curEnc j),
    hSplit (fun j => T.cost (next.scState j) + next.curEnc j), hNewPre]
  omega

/-- Exact `algorithm1_rebuild` characterization (`i₀ < P.d`) analogous to `ordAlgorithm1_shift_exact`. -/
theorem ordAlgorithm1_rebuild_exact (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
    (∀ m < i₀, next.G m = chain.G m ∧ next.scState m = chain.scState m ∧
      next.bran m = chain.bran m ∧ next.updCount m = chain.updCount m ∧
      next.rebuildCount m = chain.rebuildCount m) ∧
    next.G i₀ = Gnew ∧
    (∀ j, i₀ ≤ j → j < P.d →
      next.scState j = T.initOrd P.k (chain.lvlM j) chain.N₀ (next.G j)
        (next.toTreeChain.chainLen chain.ℓ j) (next.toTreeChain.chainGrad chain.g j)
        (next.levelOrd j) ∧
      next.G (j + 1) = T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0) ∧
    (next.lastK, next.lastLSFs) = L.build (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) ∧
    next.lastBran = 0 ∧
    (∀ j, next.rebuildCount j = if j = i₀ then chain.rebuildCount i₀ + 1 else chain.rebuildCount j) ∧
    next.ℓ = chain.ℓ ∧ next.g = chain.g ∧ next.lvlM = chain.lvlM ∧ next.N₀ = chain.N₀ ∧
    next.shiftCount = chain.shiftCount := by
  dsimp only
  set G0 := fun j => if j = i₀ then Gnew else chain.G j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
    G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  set next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
  have hG : ∀ m, next.G m = res.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hSc : ∀ m, next.scState m = res.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hBr : ∀ m, next.bran m = res.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hUpd : ∀ m, next.updCount m = res.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hReb : ∀ j, next.rebuildCount j = if j = i₀ then chain.rebuildCount i₀ + 1 else chain.rebuildCount j :=
    fun j => by simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  obtain ⟨hGpre, hSBpre, hCore⟩ := ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀
    chain.ℓ chain.g (P.d - i₀) i₀ (by omega) G0 chain.scState chain.bran chain.updCount
    chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨_, _, hLast⟩ := ordRebuildSuffix_extra T L P chain.lvlM chain.N₀ chain.ℓ chain.g
    (P.d - i₀) i₀ (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc
    chain.curDecUpdates chain.curFwd
  have hadd : i₀ + (P.d - i₀) = P.d := by omega
  have hLenCongr : ∀ (C₁ C₂ : TreeChain) (k : ℕ),
      (∀ m < k, C₁.activeLSF m = C₂.activeLSF m) → C₁.chainLen chain.ℓ k = C₂.chainLen chain.ℓ k := by
    intro C₁ C₂ k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro h; simp only [TreeChain.chainLen]
      rw [h k (Nat.lt_succ_self k), ih (fun m hm => h m (Nat.lt_succ_of_lt hm))]
  have hGradCongr : ∀ (C₁ C₂ : TreeChain) (k : ℕ),
      (∀ m < k, C₁.G m = C₂.G m) → (∀ m < k, C₁.activeLSF m = C₂.activeLSF m) →
      C₁.chainGrad chain.g k = C₂.chainGrad chain.g k := by
    intro C₁ C₂ k; induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro hGm hLm; simp only [TreeChain.chainGrad]
      rw [hGm k (Nat.lt_succ_self k), hLm k (Nat.lt_succ_self k),
        ih (fun m hm => hGm m (Nat.lt_succ_of_lt hm)) (fun m hm => hLm m (Nat.lt_succ_of_lt hm))]
  refine ⟨fun m hm => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hReb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG m, hGpre m (le_of_lt hm)]; simp [G0, show m ≠ i₀ by omega]
  · rw [hSc m, (hSBpre m hm).1]
  · rw [hBr m, (hSBpre m hm).2.1]
  · rw [hUpd m, (hSBpre m hm).2.2]
  · rw [hReb m]; simp [show m ≠ i₀ by omega]
  · rw [hG i₀, hGpre i₀ le_rfl]; simp [G0]
  · intro j hj1 hj2
    obtain ⟨hscj, hGj1, hbrj, hupj⟩ := hCore j hj1 (by omega)
    have hlen := hLenCongr
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 j, ⟨res.1 j, ∅⟩, fun _ => 1⟩, lastBran := 0 } : TreeChain)
      next.toTreeChain j (fun m hm => by
        simp [ChainState.toTreeChain, TreeChain.activeLSF, show m < P.d by omega, hSc m, hBr m])
    have hgrad := hGradCongr
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 j, ⟨res.1 j, ∅⟩, fun _ => 1⟩, lastBran := 0 } : TreeChain)
      next.toTreeChain j (fun m _ => (hG m).symm) (fun m hm => by
        simp [ChainState.toTreeChain, TreeChain.activeLSF, show m < P.d by omega, hSc m, hBr m])
    have hord : Chain.Ordered.chainLevelOrd T res.1 res.2.1 res.2.2.1 j = next.levelOrd j := by
      unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
      split_ifs
      · rw [hG 0]
      · rw [hSc (j - 1), hBr (j - 1)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [res] at hlen hgrad hord
      rw [hSc j, hscj, hlen, hgrad, hord, ← hG j]
    · rw [hG (j + 1), hGj1, hSc j]
    · rw [hBr j, hbrj]
    · rw [hUpd j, hupj]
  · have hpair : (next.lastK, next.lastLSFs) = res.2.2.2.2.2.2.2.1 := by
      simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
    rw [hpair, hLast.1, hadd, ← hG P.d]
    congr 1
    exact hLenCongr _ next.toTreeChain P.d (fun m hm => by
      simp [ChainState.toTreeChain, TreeChain.activeLSF, hm, hSc m, hBr m, res])
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]

end MinCostFlow.MinRatio
