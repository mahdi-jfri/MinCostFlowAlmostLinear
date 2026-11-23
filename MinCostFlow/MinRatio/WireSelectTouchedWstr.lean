module

public import MinCostFlow.MinRatio.WireSelectUpdateSplit
public import MinCostFlow.MinRatio.WireSelectUpdate
public import MinCostFlow.MinRatio.WireReembFacts
public import MinCostFlow.SparseCore.ReembFactsDeleted

import MinCostFlow.SparseCore.CanonCoreValid
import MinCostFlow.Chain.Ordered.UpdateProofs

/-!
# Touched-edge coverage and non-reinserted `wstr` preservation across `Update` (`WireSelectTouchedWstr`)

Proves the model side of the re-insertion (`D_reins`) correction for `sparseCoreProgTool` on
reached solver states (`ShiftLoopChainInv`, `OrdSolverReachedInv` / `alg2PreLoopState`):

1. **Batch touched-edge extraction (`batchTouchedEdges`):**
   * Collects every edge ID inserted or deleted by a batch `U : List Update`
     (`mem_batchTouchedEdges_iff`), with length `≤ U.length` (`batchTouchedEdges_length_le`).
   * Covers every symmetric-difference edge (`mem_batchTouchedEdges_of_symmDiff`) and every
     `D_reins` re-insertion emitted by `buildUSOrd` (`mem_batchTouchedEdges_buildUSOrd_reins`).
2. **Weakened `hWstr` and downward non-insertion cascade on non-rebuilt levels:**
   * `progTool_nonRebuilt_wstr_eq_of_not_inserts`: on every non-rebuilt level `j ≤ i` of
     `NonRebuiltBatches`, every surviving edge `f ∈ (st'.G j).E ∩ (st.G j).E` that is NOT inserted
     by `U j` preserves its stretch estimate `(st'.toTreeChain.activeLSF j).wstr f =
     (st.toTreeChain.activeLSF j).wstr f`.
   * `progTool_nonRebuilt_not_inserts_of_top`: if a surviving edge `f ∈ (st'.G k).E ∩ (st.G k).E`
     is not inserted by `U k`, then `f` is not inserted by `U j` for ANY `j ≤ k` (because any
     insertion of a surviving edge at level `m < k` must first delete it in `U m`, which forces
     `buildUSOrd` at level `m` to exclude `f` from `keepSet` and re-insert `f` in `U (m + 1)`).
   * `progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts`: combines the cascade with `hℓEq` at
     level `0` to preserve `(activeLSF j).wstr f` for all `j ≤ k` and `chainLen ℓ (k + 1) f`.
3. **Strong touched-list coverage (`uG`, `fDel`, `uS`, `reemb`) and reached-state wrappers:**
   * `progTool_nonRebuilt_touched_covers`: at every non-rebuilt level `j ≤ i`, the touched lists
     cover every edge deleted or inserted by `U j` (re-insertions included), every edge deleted from
     `F_j`, and every edge deleted or inserted by the output batch `U_S` of level `j`
     (re-insertions included); under `SparseCoreOrdInput` + `OrderedBatch` at level `j`, they also
     satisfy `ReembCovers` and `LevelDiffCovers`.
   * `progTool_shiftLoop_update_touched_wstr` and `progTool_reachedInv_preLoop_touched_wstr`:
     direct instantiations on `ShiftLoopChainInv` (`Ordered.algorithm1_update`) and
     `OrdSolverReachedInv` (`alg2PreLoopState`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.IPM.Machine

/-! ## 1. Batch touched-edge list and valid-batch re-insertion helper -/

/-- Edge IDs touched (inserted or deleted) by a batch `U`, in batch order. -/
def batchTouchedEdges : List Update → List ℕ
  | [] => []
  | .insert e _ _ :: rest => e :: batchTouchedEdges rest
  | .delete e :: rest => e :: batchTouchedEdges rest
  | .split _ _ _ _ :: rest => batchTouchedEdges rest

theorem batchTouchedEdges_length_le : ∀ U : List Update, (batchTouchedEdges U).length ≤ U.length
  | [] => le_rfl
  | .insert _ _ _ :: rest => Nat.succ_le_succ (batchTouchedEdges_length_le rest)
  | .delete _ :: rest => Nat.succ_le_succ (batchTouchedEdges_length_le rest)
  | .split _ _ _ _ :: rest => Nat.le_succ_of_le (batchTouchedEdges_length_le rest)

theorem mem_batchTouchedEdges_iff :
    ∀ (U : List Update) (e : ℕ),
      e ∈ batchTouchedEdges U ↔ ∃ u ∈ U, u.Inserts e ∨ u = .delete e
  | [], e => by simp [batchTouchedEdges]
  | .insert e₀ a b :: rest, e => by
    simp only [batchTouchedEdges, List.mem_cons, mem_batchTouchedEdges_iff rest e]
    constructor
    · rintro (rfl | ⟨u, hu, h⟩)
      · exact ⟨.insert e a b, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, rfl | hu, h⟩
      · rcases h with hIns | hDel
        · left; exact hIns.symm
        · cases hDel
      · exact Or.inr ⟨u, hu, h⟩
  | .delete e₀ :: rest, e => by
    simp only [batchTouchedEdges, List.mem_cons, mem_batchTouchedEdges_iff rest e]
    constructor
    · rintro (rfl | ⟨u, hu, h⟩)
      · exact ⟨.delete e, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, rfl | hu, h⟩
      · rcases h with hIns | hDel
        · simp [Update.Inserts] at hIns
        · left; cases hDel; rfl
      · exact Or.inr ⟨u, hu, h⟩
  | .split v v' St Sh :: rest, e => by
    simp only [batchTouchedEdges, List.mem_cons, mem_batchTouchedEdges_iff rest e]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, rfl | hu, h⟩
      · rcases h with hIns | hDel
        · simp [Update.Inserts] at hIns
        · cases hDel
      · exact ⟨u, hu, h⟩

theorem mem_batchTouchedEdges_of_inserts {U : List Update} {u : Update} {e : ℕ}
    (hu : u ∈ U) (hIns : u.Inserts e) : e ∈ batchTouchedEdges U :=
  (mem_batchTouchedEdges_iff U e).mpr ⟨u, hu, Or.inl hIns⟩

theorem mem_batchTouchedEdges_of_delete {U : List Update} {e : ℕ}
    (hDel : Update.delete e ∈ U) : e ∈ batchTouchedEdges U :=
  (mem_batchTouchedEdges_iff U e).mpr ⟨.delete e, hDel, Or.inr rfl⟩

/-- Every edge whose membership changes across `G.applyBatch U` lies in `batchTouchedEdges U`. -/
theorem mem_batchTouchedEdges_of_symmDiff :
    ∀ {G : MGraph} {U : List Update} {e : ℕ},
      (e ∈ (G.applyBatch U).E ↔ e ∉ G.E) → e ∈ batchTouchedEdges U
  | G, [], e, h => by
    simp only [MGraph.applyBatch, List.foldl_nil] at h
    exact absurd (Iff.rfl : e ∈ G.E ↔ e ∈ G.E) (by tauto)
  | G, u :: rest, e, h => by
    by_cases htouch : u.Inserts e ∨ u = .delete e
    · exact (mem_batchTouchedEdges_iff (u :: rest) e).mpr ⟨u, List.mem_cons_self, htouch⟩
    · have hE_eq : e ∈ (G.applyUpdate u).E ↔ e ∈ G.E := by
        cases u with
        | insert e₀ a b =>
          have hne : e ≠ e₀ := fun heq => htouch (Or.inl (by simpa [Update.Inserts] using heq.symm))
          simp [MGraph.applyUpdate, hne]
        | delete e₀ =>
          have hne : e ≠ e₀ := fun heq => htouch (Or.inr (by subst heq; rfl))
          simp [MGraph.applyUpdate, hne]
        | split v v' St Sh => rfl
      have hrest : e ∈ ((G.applyUpdate u).applyBatch rest).E ↔ e ∉ (G.applyUpdate u).E := by
        simpa [MGraph.applyBatch, List.foldl_cons, hE_eq] using h
      have hmem := mem_batchTouchedEdges_of_symmDiff hrest
      obtain ⟨u', hu', h'⟩ := (mem_batchTouchedEdges_iff rest e).mp hmem
      exact (mem_batchTouchedEdges_iff (u :: rest) e).mpr ⟨u', List.mem_cons_of_mem _ hu', h'⟩

/-- In any valid batch `U` on `G`, if an edge `e ∈ G.E` is inserted by `U`, then `U` must also
delete `e` (`e ∈ batchDeletes U`). -/
theorem mem_batchDeletes_of_inserts_of_mem_E {G : MGraph} {U : List Update} {e : ℕ}
    (hBV : G.BatchIsValid U) (heG : e ∈ G.E) (hins : ∃ u ∈ U, u.Inserts e) :
    e ∈ batchDeletes U :=
  mem_batchDeletes_of_inserts_in_G hBV heG hins

/-- Any edge in `targetE` excluded from `keepSet` (in particular, any `D_reins` re-insertion or
any edge deleted by `U`) is explicitly inserted by `buildUSOrd` and therefore lies in
`batchTouchedEdges (buildUSOrd ...)`. -/
theorem buildUSOrd_inserts_of_not_keep (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) {e : ℕ}
    (heT : e ∈ targetE) (hnotKeep : e ∉ ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins) :
    ∃ u ∈ buildUSOrd UC U cs_new S_prev targetE D_reins, u.Inserts e := by
  unfold buildUSOrd
  refine ⟨Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e)),
    ?_, rfl⟩
  refine List.mem_append_right _ ?_
  exact List.mem_map.mpr ⟨e, (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨heT, hnotKeep⟩),
    rfl⟩

/-- Every `D_reins` re-insertion in `targetE` (and every `D_reins` edge in `S_prev.E`) lies in
`batchTouchedEdges (buildUSOrd ...)`. -/
theorem mem_batchTouchedEdges_buildUSOrd_reins (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) {e : ℕ} (heR : e ∈ D_reins)
    (hMem : e ∈ S_prev.E ∨ e ∈ targetE) :
    e ∈ batchTouchedEdges (buildUSOrd UC U cs_new S_prev targetE D_reins) := by
  have hnotKeep : e ∉ ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins :=
    fun h => (Finset.mem_sdiff.mp h).2 heR
  rcases hMem with heS | heT
  · apply mem_batchTouchedEdges_of_delete
    unfold buildUSOrd
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    exact List.mem_map.mpr ⟨e, (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨heS, hnotKeep⟩),
      rfl⟩
  · obtain ⟨u, hu, hIns⟩ := buildUSOrd_inserts_of_not_keep UC U cs_new S_prev targetE D_reins
      heT hnotKeep
    exact mem_batchTouchedEdges_of_inserts hu hIns

/-! ## 2. Weakened `hWstr` and downward non-insertion cascade on `NonRebuiltBatches` -/

/-- **Weakened `hWstr` on a non-rebuilt prefix of `sparseCoreProgTool`:**
At every non-rebuilt level `j ≤ i`, any surviving edge `f ∈ (st'.G j).E ∩ (st.G j).E` that is NOT
inserted by `U j` preserves its stretch estimate `(st'.toTreeChain.activeLSF j).wstr f =
(st.toTreeChain.activeLSF j).wstr f`. -/
theorem progTool_nonRebuilt_wstr_eq_of_not_inserts {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {P : ChainParams}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i) :
    ∀ j ≤ i, ∀ f ∈ (st'.G j).E, f ∈ (st.G j).E →
      (∀ u ∈ U j, ¬ u.Inserts f) →
      (st'.toTreeChain.activeLSF j).wstr f = (st.toTreeChain.activeLSF j).wstr f := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨hi_d, _, _, hStep, hLast⟩ := hNR
  intro j hj f _ _ hNoIns
  by_cases hjd : j < P.d
  · obtain ⟨hbr, ℓj, gj, ordj, hsc', _⟩ := hStep j hj hjd
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte, hbr]
    by_cases hne : (st.scState j).isNonempty = true
    · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hne (U j) ℓj gj ordj
      have hne' : (st'.scState j).isNonempty = true := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      have hL_old : T.lsfs (st.scState j) (st.bran j) = ((st.scState j).trees (st.bran j)).cs.lsf := by
        change (if (st.scState j).isNonempty then _ else _) = _; simp [hne]
      have hL_new : T.lsfs (st'.scState j) (st.bran j) =
          (compLSFBatch ((st.scState j).trees (st.bran j)).cs (U j)).lsf := by
        change (if (st'.scState j).isNonempty then _ else _) = _
        rw [ite_eq_left hne', hsc']
        change ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).1.trees (st.bran j)).cs.lsf = _
        rw [hup]; rfl
      rw [hL_old, hL_new]
      exact compLSFBatch_wstr_of_not_inserts _ (U j) hNoIns
    · have hf : (st.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
      have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hf (U j) ℓj gj ordj
      have hne' : (st'.scState j).isNonempty = false := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
      change (if (st'.scState j).isNonempty then _ else emptyLSF).wstr f =
        (if (st.scState j).isNonempty then _ else emptyLSF).wstr f
      simp [hne', hf]
  · have hjeq : j = P.d := by omega
    have hieq : i = P.d := by omega
    obtain ⟨_, hLSF, hBran⟩ := hLast hieq
    subst hjeq
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte, hLSF, hBran]

/-- **Downward non-insertion cascade on a non-rebuilt prefix:**
If a surviving edge `f ∈ (st'.G k).E ∩ (st.G k).E` is NOT inserted by `U k`, then `f` is NOT
inserted by `U j` at ANY lower level `j ≤ k`.
Indeed, if `U m` (`m < k`) inserted `f`, validity of `U m` on `st.G m` would force
`f ∈ batchDeletes (U m)`, which excludes `f` from `keepSet` in `buildUSOrd` at level `m` and
forces `U (m + 1)` to re-insert `f`. -/
theorem progTool_nonRebuilt_not_inserts_of_top {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i) :
    ∀ k ≤ i, ∀ f ∈ (st'.G k).E, f ∈ (st.G k).E →
      (∀ u ∈ U k, ¬ u.Inserts f) →
      ∀ j ≤ k, ∀ u ∈ U j, ¬ u.Inserts f := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨hi_d, _, hGB, hStep, _⟩ := hNR
  -- One step down: from `m + 1` to `m`.
  have hDown : ∀ m, m + 1 ≤ i → ∀ f ∈ (st'.G (m + 1)).E, f ∈ (st.G (m + 1)).E →
      (∀ u ∈ U (m + 1), ¬ u.Inserts f) → ∀ u ∈ U m, ¬ u.Inserts f := by
    intro m hm1 f hf' hf hNoIns1 u hu hIns
    have hm : m ≤ i := Nat.le_of_succ_le hm1
    have hmd : m < P.d := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm1 hi_d)
    have hfGm : f ∈ (st.G m).E :=
      (Finset.mem_sdiff.mp (st.toTreeChain.G_succ_E_subset hH hmd hf)).1
    have hfDel : f ∈ batchDeletes (U m) :=
      mem_batchDeletes_of_inserts_of_mem_E (hGB m hm).2 hfGm ⟨u, hu, hIns⟩
    obtain ⟨hbr, ℓm, gm, ordm, hsc', hU1⟩ := hStep m hm hmd
    have hUm1 : U (m + 1) = (T.updateOrd (st.scState m) (U m) ℓm gm ordm).2 (st.bran m) := hU1 hm1
    by_cases hne : (st.scState m).isNonempty = true
    · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState m) hne (U m) ℓm gm ordm
      have hne' : (st'.scState m).isNonempty = true := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      let tr := (st.scState m).trees (st.bran m)
      let info := stepBundleTree (fun _ => canonicalSparsify impl) tr (U m) (st.scState m).ord ordm
      have hGk' : st'.G (m + 1) = T.S (st'.scState m) (st'.bran m) := by
        have := (hH'.2.2.2.2.1 m hmd).2.2.2
        simpa [ChainState.toTreeChain] using this
      have hS'_eq : st'.G (m + 1) = info.state.S_cur := by
        rw [hGk', hbr, progTool_S_of_nonempty _ hne', hsc']
        change ((T.updateOrd (st.scState m) (U m) ℓm gm ordm).1.trees (st.bran m)).S_cur = _
        rw [hup]
      have hUS_eq : U (m + 1) = info.U_S := by rw [hUm1, hup]
      have hfS' : f ∈ info.state.S_cur.E := hS'_eq ▸ hf'
      -- By `buildUSOrd_applyBatch_E_eq`, `info.state.S_cur.E = targetE`.
      let targetE' : Finset ℕ :=
        ((info.state.activeComps.biUnion fun C =>
            (tr.activeBuckets C).biUnion fun b => (info.state.dyn (C, b)).H.E) ∪
          (info.state.activeComps.biUnion fun C =>
            ((info.state.cs.compSt C).G.E \ (info.state.cs.compSt C).RF.F.E) \
              (info.state.activeComps.biUnion fun C' =>
                (tr.activeBuckets C').biUnion fun b => (info.state.bun (C', b)).edges))) ∪
          info.state.cs.crossEdges
      have hEeq := buildUSOrd_applyBatch_E_eq (canonCoreBatch tr.cs (U m)) (U m)
        (compLSFBatch tr.cs (U m)) tr.S_cur targetE' info.D_total
      have hfTgt : f ∈ targetE' := by
        simpa only [info, stepBundleTree, coreBatchOf_eq] using hEeq ▸ hfS'
      have hnotKeep : f ∉ ((tr.S_cur.E ∩ targetE') \ batchDeletes (U m)) \ info.D_total :=
        fun hk => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).2 hfDel
      obtain ⟨u1, hu1, hIns1⟩ := buildUSOrd_inserts_of_not_keep (canonCoreBatch tr.cs (U m)) (U m)
        (compLSFBatch tr.cs (U m)) tr.S_cur targetE' info.D_total hfTgt hnotKeep
      have hu1' : u1 ∈ U (m + 1) := by
        rw [hUS_eq]; simpa only [targetE', info, stepBundleTree, coreBatchOf_eq] using hu1
      exact hNoIns1 u1 hu1' hIns1
    · -- If `st.scState m` is empty, `st.G (m + 1) = emptyGraph`, contradicting `f ∈ (st.G (m + 1)).E`.
      have hEmpty : st.G (m + 1) = emptyGraph := by
        rw [hInv.hGSucc m hmd]
        change (if (st.scState m).isNonempty then _ else emptyGraph) = emptyGraph
        simp [hne]
      rw [hEmpty] at hf
      simp [emptyGraph] at hf
  intro k
  induction k with
  | zero =>
    intro _ f _ _ hNo0 j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    exact hNo0
  | succ m ih =>
    intro hm1 f hf' hf hNo1 j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact hNo1
    · have hmd : m < P.d := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm1 hi_d)
      have hfGm : f ∈ (st.G m).E :=
        (Finset.mem_sdiff.mp (st.toTreeChain.G_succ_E_subset hH hmd hf)).1
      have hfGm' : f ∈ (st'.G m).E :=
        (Finset.mem_sdiff.mp (st'.toTreeChain.G_succ_E_subset hH' hmd hf')).1
      have hNoM : ∀ u ∈ U m, ¬ u.Inserts f := hDown m hm1 f hf' hf hNo1
      exact ih (Nat.le_of_succ_le hm1) f hfGm' hfGm hNoM j (Nat.le_of_lt_succ hlt)

/-- Combining `progTool_nonRebuilt_not_inserts_of_top` and `progTool_nonRebuilt_wstr_eq_of_not_inserts`:
if a surviving edge `f ∈ (st'.G k).E ∩ (st.G k).E` is not inserted by `U k`, then it keeps its
`wstr` at EVERY level `j ≤ k` AND keeps `chainLen ℓ (k + 1) f` (given `hℓEq` at level `0`). -/
theorem progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth : ℕ} {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams}
    {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓh' ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓh' σ' σ'_mwu γ'_ℓ γ'_c)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i)
    (hℓEq : ∀ f ∈ (st'.G 0).E, f ∈ (st.G 0).E → ℓ' f = ℓ f) :
    ∀ k ≤ i, ∀ f ∈ (st'.G k).E, f ∈ (st.G k).E →
      (∀ u ∈ U k, ¬ u.Inserts f) →
      (∀ j ≤ k, (st'.toTreeChain.activeLSF j).wstr f = (st.toTreeChain.activeLSF j).wstr f) ∧
      st'.toTreeChain.chainLen ℓ' (k + 1) f = st.toTreeChain.chainLen ℓ (k + 1) f := by
  intro k hk f hf' hf hNoK
  have hNoAll := progTool_nonRebuilt_not_inserts_of_top hInv hH hH' hNR k hk f hf' hf hNoK
  have hWstr := progTool_nonRebuilt_wstr_eq_of_not_inserts hNR
  have hMem : ∀ j ≤ k, f ∈ (st'.G j).E ∧ f ∈ (st.G j).E := fun j hj => by
    have hk_d : k ≤ P.d := le_trans hk hNR.1
    exact ⟨st'.toTreeChain.G_E_subset_of_le hH' hj hk_d hf',
      st.toTreeChain.G_E_subset_of_le hH hj hk_d hf⟩
  have hWAll : ∀ j ≤ k, (st'.toTreeChain.activeLSF j).wstr f = (st.toTreeChain.activeLSF j).wstr f :=
    fun j hj => hWstr j (le_trans hj hk) f (hMem j hj).1 (hMem j hj).2 (hNoAll j hj)
  refine ⟨hWAll, ?_⟩
  have hCL : ∀ m ≤ k + 1, st'.toTreeChain.chainLen ℓ' m f = st.toTreeChain.chainLen ℓ m f := by
    intro m
    induction m with
    | zero =>
      intro _
      exact hℓEq f (hMem 0 (Nat.zero_le k)).1 (hMem 0 (Nat.zero_le k)).2
    | succ r ih =>
      intro hr
      have hrk : r ≤ k := Nat.le_of_succ_le_succ hr
      change (st'.toTreeChain.activeLSF r).wstr f * st'.toTreeChain.chainLen ℓ' r f =
        (st.toTreeChain.activeLSF r).wstr f * st.toTreeChain.chainLen ℓ r f
      rw [hWAll r hrk, ih (Nat.le_of_lt hr)]
  exact hCL (k + 1) le_rfl

/-! ## 3. Touched-list coverage on a non-rebuilt prefix -/

/-- **Touched-list coverage on a non-rebuilt prefix of `sparseCoreProgTool`:**
At every non-rebuilt level `j ≤ i`:
* `uG := batchTouchedEdges (U j)` covers EVERY edge inserted or deleted by `U j` (including
  `D_reins` re-insertions), hence every symmetric-difference edge of `G_j`, with `uG.length ≤ (U j).length`;
* `fDel` covers every edge deleted from `(activeLSF j).F.F` (and no edge is added to `F_j`);
* when `j < P.d`, `uS := batchTouchedEdges (U_out j)` covers EVERY edge inserted or deleted by the
  output batch `U_out j` of level `j` (including `D_reins` re-insertions), hence every
  symmetric-difference edge of `activeS j`, with `uS.length ≤ (U_out j).length`;
* when `j = P.d` (`i = P.d`), `U P.d = []` and `activeS P.d` is unchanged. -/
theorem progTool_nonRebuilt_touched_covers {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i) :
    ∀ j ≤ i,
      let uG := batchTouchedEdges (U j)
      let fDel := ((st.toTreeChain.activeLSF j).F.F.E \
        (st'.toTreeChain.activeLSF j).F.F.E).sort (· ≤ ·)
      uG.length ≤ (U j).length ∧
      (∀ e, (∃ u ∈ U j, u.Inserts e ∨ u = .delete e) → e ∈ uG) ∧
      (∀ e, (e ∈ (st'.G j).E ↔ e ∉ (st.G j).E) → e ∈ uG) ∧
      (∀ e, e ∈ (st.toTreeChain.activeLSF j).F.F.E → e ∉ (st'.toTreeChain.activeLSF j).F.F.E →
        e ∈ fDel) ∧
      (∀ e, e ∈ (st'.toTreeChain.activeLSF j).F.F.E → e ∉ (st.toTreeChain.activeLSF j).F.F.E →
        e ∈ uG) ∧
      (j < P.d →
        ∃ ℓj gj ordj,
          let T := sparseCoreProgTool lsfInit C_lsst depth impl
          let Uout := (T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j)
          let uS := batchTouchedEdges Uout
          st'.scState j = (T.updateOrd (st.scState j) (U j) ℓj gj ordj).1 ∧
          (j + 1 ≤ i → U (j + 1) = Uout) ∧
          uS.length ≤ Uout.length ∧
          (∀ e, (∃ u ∈ Uout, u.Inserts e ∨ u = .delete e) → e ∈ uS) ∧
          (∀ e, (e ∈ (st'.toTreeChain.activeS j).E ↔ e ∉ (st.toTreeChain.activeS j).E) → e ∈ uS)) ∧
      (j = P.d → ∀ e, (e ∈ (st'.toTreeChain.activeS j).E ↔ e ∉ (st.toTreeChain.activeS j).E) →
        False) := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  have hFsub := progTool_nonRebuilt_forest_subset hInv hInit hNR
  obtain ⟨hi_d, _, hGB, hStep, hLast⟩ := hNR
  intro j hj
  dsimp only
  refine ⟨batchTouchedEdges_length_le (U j),
    fun e h => (mem_batchTouchedEdges_iff (U j) e).mpr h,
    fun e h => mem_batchTouchedEdges_of_symmDiff ((hGB j hj).1 ▸ h),
    fun e h1 h2 => (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨h1, h2⟩),
    fun e h1 h2 => absurd (hFsub j hj h1) h2,
    fun hjd => ?_,
    fun hjeq e hxor => ?_⟩
  · -- `j < P.d`: output batch `Uout` on `activeS j`
    obtain ⟨hbr, ℓj, gj, ordj, hsc', hU1⟩ := hStep j hj hjd
    refine ⟨ℓj, gj, ordj, hsc', hU1, batchTouchedEdges_length_le _,
      fun e h => (mem_batchTouchedEdges_iff _ e).mpr h, fun e hxor => ?_⟩
    have hSeq : st'.toTreeChain.activeS j =
        (st.toTreeChain.activeS j).applyBatch
          ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j)) := by
      simp only [TreeChain.activeS, ChainState.toTreeChain, hjd, ↓reduceIte, hbr, hsc']
      exact progTool_S_updateOrd (st.scState j) (U j) ℓj gj ordj (st.bran j)
    exact mem_batchTouchedEdges_of_symmDiff (hSeq ▸ hxor)
  · -- `j = P.d`: `activeS P.d = emptyGraph` on both `st` and `st'`
    subst hjeq
    simp [TreeChain.activeS, ChainState.toTreeChain] at hxor

/-- Full `LevelDiffCovers` (including `ReembCovers`) at a non-rebuilt level `j ≤ i` (`j < P.d`)
when `SparseCoreOrdInput` and `OrderedBatch` hold at level `j`. -/
theorem progTool_nonRebuilt_levelDiffCovers {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i j : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i)
    (hj : j ≤ i) (hjd : j < P.d) (hdepth : 1 ≤ depth)
    {M N n : ℕ} {ord : ℕ → List End}
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) P.k M N
      (st.scState j) (st.G j) ord n)
    (hOrdB : ∀ ℓj gj ordj,
      st'.scState j = ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState j)
        (U j) ℓj gj ordj).1 →
      OrderedBatch (st.G j) (U j) ord ordj) :
    ∃ (lists : LevelDiffLists),
      lists.uG = batchTouchedEdges (U j) ∧
      (∀ e, (∃ u ∈ U j, u.Inserts e ∨ u = .delete e) → e ∈ lists.uG) ∧
      LevelDiffCovers st.toTreeChain st'.toTreeChain j (fun k e => ∃ u ∈ U k, u.Inserts e) lists := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  obtain ⟨_, huG_all, huG_sym, hfDel, hfIns, hOut, _⟩ :=
    progTool_nonRebuilt_touched_covers hInv hInit hNR j hj
  obtain ⟨ℓj, gj, ordj, hsc', _, _, _, huS_sym⟩ := hOut hjd
  have hbr : st'.bran j = st.bran j := (hNR.2.2.2.1 j hj hjd).1
  have huG_cov : ∀ e, ((e ∈ (st'.toTreeChain.G j).E ↔ e ∉ (st.toTreeChain.G j).E) ∨
      (∃ u ∈ U j, u.Inserts e)) → e ∈ batchTouchedEdges (U j) := fun e h =>
    h.elim (huG_sym e) (fun ⟨u, hu, hi⟩ => huG_all e ⟨u, hu, Or.inl hi⟩)
  by_cases hne : (st.scState j).isNonempty = true
  · let lists : LevelDiffLists :=
      { uG := batchTouchedEdges (U j)
        fDel := ((st.toTreeChain.activeLSF j).F.F.E \
          (st'.toTreeChain.activeLSF j).F.F.E).sort (· ≤ ·)
        uS := batchTouchedEdges ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j))
        reemb := progReemb lsfInit C_lsst depth impl (st.scState j) (U j) ordj (st.bran j) }
    have hReemb : ReembCovers st.toTreeChain st'.toTreeChain j lists.reemb :=
      reembCovers_of_progTool_of_input hjd hjd hbr (Nat.lt_of_lt_of_le Nat.zero_lt_one P.hk)
        hdepth (st.scState j) hinp hne (U j) ℓj gj ordj (hNR.2.2.1 j hj).2 (hOrdB ℓj gj ordj hsc')
        (hInit (st.bran j) (hInv.hBran j hjd)) (hNR.2.2.1 j hj).1
        (by simp [ChainState.toTreeChain, hsc'])
        (by simp [ChainState.toTreeChain, hsc'])
        rfl
        (by simp [ChainState.toTreeChain, hsc'])
    refine ⟨lists, rfl, huG_all, huG_cov, hfDel, hfIns, huS_sym, hReemb, ?_⟩
    intro e heOld heNew ⟨x, hxEmb, hins⟩
    refine hReemb e heOld heNew ?_
    have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hne (U j) ℓj gj ordj
    have hne' : (st'.scState j).isNonempty = true := by
      rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
    have htree' : (st'.scState j).trees (st'.bran j) =
        (stepBundleTree (fun _ => canonicalSparsify impl) ((st.scState j).trees (st.bran j))
          (U j) (st.scState j).ord ordj).state := by
      rw [hbr, hsc']; change ((T.updateOrd _ _ _ _ _).1.trees (st.bran j)) = _; rw [hup]
    have heOff : e ∉ ((st.scState j).trees (st.bran j)).S_cur.E := by
      have h1 := (Finset.mem_sdiff.mp heOld).2
      simpa [TreeChain.activeS, ChainState.toTreeChain, hjd, hne, sparseCoreProgTool,
        sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
        sparseCoreBundleToolWith] using h1
    have heOff' : e ∉ (stepBundleTree (fun _ => canonicalSparsify impl)
        ((st.scState j).trees (st.bran j)) (U j) (st.scState j).ord ordj).state.S_cur.E := by
      have h1 := (Finset.mem_sdiff.mp heNew).2
      rw [← htree']
      simpa [TreeChain.activeS, ChainState.toTreeChain, hjd, hne', sparseCoreProgTool,
        sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
        sparseCoreBundleToolWith] using h1
    have hxTr : x ∈ ((st.scState j).trees (st.bran j)).emb e := by
      simpa [TreeChain.activeEmb, ChainState.toTreeChain, hjd, hne, sparseCoreProgTool,
        sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
        sparseCoreBundleToolWith] using hxEmb
    have hneEmb := progTool_emb_ne_of_inserts lsfInit C_lsst depth hdepth impl
      (Nat.lt_of_lt_of_le Nat.zero_lt_one P.hk) (st.scState j) (st.G j) ord hinp hne (U j) ordj
      (hNR.2.2.1 j hj).2 (hOrdB ℓj gj ordj hsc') (hInit (st.bran j) (hInv.hBran j hjd))
      heOff heOff' hxTr hins
    simpa [TreeChain.activeEmb, ChainState.toTreeChain, hjd, hne, hne', htree', sparseCoreProgTool,
      sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
      sparseCoreBundleToolWith] using hneEmb
  · have hf : (st.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hf (U j) ℓj gj ordj
    have hne' : (st'.scState j).isNonempty = false := by
      rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
    let lists : LevelDiffLists :=
      { uG := batchTouchedEdges (U j)
        fDel := ((st.toTreeChain.activeLSF j).F.F.E \
          (st'.toTreeChain.activeLSF j).F.F.E).sort (· ≤ ·)
        uS := batchTouchedEdges ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j))
        reemb := [] }
    refine ⟨lists, rfl, huG_all, huG_cov, hfDel, hfIns, huS_sym, ?_, ?_⟩
    · intro e _ _ hEmbNe
      exfalso; apply hEmbNe
      simp only [TreeChain.activeEmb, ChainState.toTreeChain, hjd, ↓reduceIte]
      change (if (st'.scState j).isNonempty then _ else fun _ => []) e =
        (if (st.scState j).isNonempty then _ else fun _ => []) e
      simp [hne', hf]
    · intro e _ _ ⟨x, hxEmb, _⟩
      simp only [TreeChain.activeEmb, ChainState.toTreeChain, hjd, ↓reduceIte] at hxEmb
      change x ∈ (if (st.scState j).isNonempty then _ else fun _ => []) e at hxEmb
      simp [hf] at hxEmb

/-! ## 4. Forms for `ShiftLoopChainInv` and `OrdSolverReachedInv` -/

/-- **Touched-edge coverage and non-reinserted `wstr` preservation on `ShiftLoopChainInv` after
`Ordered.algorithm1_update`.**
Either level `0` (or the sole level when `P.d = 0 ∧ U₀ ≠ []`) is rebuilt, or on the exact
non-rebuilt prefix `0, …, i` with per-level batches `U` (`U 0 = U₀`):
1. at every `j ≤ i`, `batchTouchedEdges (U j)` covers every edge deleted or inserted by `U j`
   (re-insertions included) with length `≤ (U j).length`, `diffTreeChanges` covers `F_j \ F'_j`,
   and for `j < P.d`, `batchTouchedEdges (U_out j)` covers every edge deleted or inserted by
   level `j`'s output batch (re-insertions included) and every symmetric-difference edge of `S_j`;
2. at every `j ≤ i`, every surviving edge `f ∈ (st'.G j).E ∩ (st.G j).E` not inserted by `U j`
   keeps `(st'.toTreeChain.activeLSF j).wstr f = (st.toTreeChain.activeLSF j).wstr f` — and in
   fact is not inserted by `U m` for any `m ≤ j`, so it keeps `wstr` at all levels `m ≤ j` and
   keeps `chainLen ℓ' (j + 1) f` (when `hℓEq` holds at level `0`). -/
theorem progTool_shiftLoop_update_touched_wstr {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b)
    {st : ChainState cfg.T cfg.P} (hShift : ShiftLoopChainInv cfg st)
    (U₀ : List Update) (g' ℓ' : ℕ → ℝ)
    (hBatch₀ : (st.G 0).BatchIsValid U₀) (hNR₀ : NoBatchReinsert (st.G 0) U₀)
    (hEdge : ∀ u ∈ U₀, IsEdgeUpdate u)
    (hG0'Valid : ((st.G 0).applyBatch U₀).IsValid)
    (hG0'm : ((st.G 0).applyBatch U₀).m ≤ cfg.P.M₀)
    (hG0'n : ((st.G 0).applyBatch U₀).n ≤ cfg.N₀)
    (hℓ'R : LenInRange (max 0 cfg.Ψ) ((st.G 0).applyBatch U₀) ℓ')
    (hℓ'Stable : ∀ e ∈ ((st.G 0).applyBatch U₀).E, e ∈ (st.G 0).E →
      (∀ u ∈ U₀, ¬ u.Inserts e) → ℓ' e = st.ℓ e) :
    let st' := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st U₀ g' ℓ').1
    (firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = some 0 ∨
      (cfg.P.d = 0 ∧ U₀ ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      i ≤ cfg.P.d ∧ U 0 = U₀ ∧
      ((firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = some (i + 1) ∧ i < cfg.P.d) ∨
        (firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = none ∧
          (i = cfg.P.d ∨ (i + 1 = cfg.P.d ∧ U cfg.P.d ≠ [])))) ∧
      (∀ j ≤ i,
        (batchTouchedEdges (U j)).length ≤ (U j).length ∧
        (∀ e, (∃ u ∈ U j, u.Inserts e ∨ u = .delete e) → e ∈ batchTouchedEdges (U j)) ∧
        (∀ e, (e ∈ (st'.G j).E ↔ e ∉ (st.G j).E) → e ∈ batchTouchedEdges (U j)) ∧
        (∀ e, e ∈ (st.toTreeChain.activeLSF j).F.F.E → e ∉ (st'.toTreeChain.activeLSF j).F.F.E →
          e ∈ ((st.toTreeChain.activeLSF j).F.F.E \
            (st'.toTreeChain.activeLSF j).F.F.E).sort (· ≤ ·)) ∧
        (∀ e, e ∈ (st'.toTreeChain.activeLSF j).F.F.E → e ∉ (st.toTreeChain.activeLSF j).F.F.E →
          e ∈ batchTouchedEdges (U j)) ∧
        (j < cfg.P.d →
          ∃ ℓj gj ordj,
            let Uout := (cfg.T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j)
            st'.scState j = (cfg.T.updateOrd (st.scState j) (U j) ℓj gj ordj).1 ∧
            (j + 1 ≤ i → U (j + 1) = Uout) ∧
            (batchTouchedEdges Uout).length ≤ Uout.length ∧
            (∀ e, (∃ u ∈ Uout, u.Inserts e ∨ u = .delete e) → e ∈ batchTouchedEdges Uout) ∧
            (∀ e, (e ∈ (st'.toTreeChain.activeS j).E ↔ e ∉ (st.toTreeChain.activeS j).E) →
              e ∈ batchTouchedEdges Uout))) ∧
      (∀ j ≤ i, ∀ f ∈ (st'.G j).E, f ∈ (st.G j).E →
        (∀ u ∈ U j, ¬ u.Inserts f) →
        (∀ m ≤ j, ∀ u ∈ U m, ¬ u.Inserts f) ∧
        (∀ m ≤ j, (st'.toTreeChain.activeLSF m).wstr f = (st.toTreeChain.activeLSF m).wstr f) ∧
        st'.toTreeChain.chainLen ℓ' (j + 1) f = st.toTreeChain.chainLen st.ℓ (j + 1) f) := by
  rcases cfg with ⟨T, L, TP, LP, P, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT hV hInit hShift hBatch₀ hNR₀ hEdge hG0'Valid hG0'm hG0'n hℓ'R hℓ'Stable ⊢
  subst hT
  obtain ⟨hInv, ⟨overflow, hBud⟩, _, _⟩ := hShift
  have hUpd := update_preserves_with_noHidden (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U₀ g' ℓ'
    hBatch₀ hNR₀ hEdge hG0'Valid hG0'm hG0'n hℓ'R hℓ'Stable
  dsimp only at hUpd
  have hH := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH' := (hUpd.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  rcases progTool_algorithm1_update_nonRebuiltBatches hInv hH hH' hInit hBatch₀ hNR₀ with
    hAllReb | ⟨i, U, hU0, hCase, hNR⟩
  · exact Or.inl hAllReb
  · right
    have hℓEq0 : ∀ f ∈ ((Ordered.algorithm1_update (sparseCoreProgTool lsfInit C_lsst depth impl)
        L TP P N₀ st U₀ g' ℓ').1.G 0).E, f ∈ (st.G 0).E → ℓ' f = st.ℓ f := by
      intro f hf' hf
      have hG0eq : (Ordered.algorithm1_update (sparseCoreProgTool lsfInit C_lsst depth impl)
          L TP P N₀ st U₀ g' ℓ').1.G 0 = (st.G 0).applyBatch U₀ := by
        rw [(hNR.2.2.1 0 (Nat.zero_le i)).1, hU0]
      exact hℓ'Stable f (hG0eq ▸ hf') hf (hNR₀ f hf)
    have hTouched := progTool_nonRebuilt_touched_covers hInv hInit hNR
    have hNoTop := progTool_nonRebuilt_not_inserts_of_top hInv hH hH' hNR
    have hWCL := progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts hInv hH hH' hNR hℓEq0
    refine ⟨i, U, hNR.1, hU0, hCase, fun j hj => ?_, fun j hj f hf' hf hNoJ => ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hTouched j hj
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    · exact ⟨hNoTop j hj f hf' hf hNoJ, (hWCL j hj f hf' hf hNoJ).1, (hWCL j hj f hf' hf hNoJ).2⟩

/-- **Touched-edge coverage and non-reinserted `wstr` preservation on `OrdSolverReachedInv` and
`alg2PreLoopState`:**
For any reached solver state `model` (`OrdSolverReachedInv`) with `sparseCoreProgTool`,
`ValidOrdNoHidden`, and `IsValidLSFInitFor`, and any `RefreshBatch` meeting `hagree`,
`translateBatch` discharges all level-`0` batch and length-stability preconditions, yielding both
strong touched-list coverage (including `D_reins` re-insertions) and non-reinserted `wstr` /
`chainLen` preservation on the non-rebuilt prefix of `pre := alg2PreLoopState cfg model U_ext g_ext l_ext`. -/
theorem progTool_reachedInv_preLoop_touched_wstr {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b)
    (hm : G.m ≤ cfg.P.M₀) (hn : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (h : OrdSolverReachedInv κ G P model tok)
    {U_ext : List Update} {g_ext l_ext : ℕ → ℝ}
    (hU : RefreshBatch G U_ext) (hl : ∀ e ∈ G.E, 0 < l_ext e)
    (hlR : ∀ e ∈ G.E, |Real.log (l_ext e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U_ext, ¬ u.Inserts e) →
      g_ext e = model.extg e ∧ l_ext e = model.extℓ e) :
    let tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U_ext
    let pre := alg2PreLoopState cfg model U_ext g_ext l_ext
    (firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = some 0 ∨
      (cfg.P.d = 0 ∧ tb.2.2.2.2 ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      i ≤ cfg.P.d ∧ U 0 = tb.2.2.2.2 ∧
      ((firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = some (i + 1) ∧
          i < cfg.P.d) ∨
        (firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = none ∧
          (i = cfg.P.d ∨ (i + 1 = cfg.P.d ∧ U cfg.P.d ≠ [])))) ∧
      (∀ j ≤ i,
        (batchTouchedEdges (U j)).length ≤ (U j).length ∧
        (∀ e, (∃ u ∈ U j, u.Inserts e ∨ u = .delete e) → e ∈ batchTouchedEdges (U j)) ∧
        (∀ e, (e ∈ (pre.chain.G j).E ↔ e ∉ (model.chain.G j).E) → e ∈ batchTouchedEdges (U j)) ∧
        (∀ e, e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E →
          e ∉ (pre.chain.toTreeChain.activeLSF j).F.F.E →
          e ∈ ((model.chain.toTreeChain.activeLSF j).F.F.E \
            (pre.chain.toTreeChain.activeLSF j).F.F.E).sort (· ≤ ·)) ∧
        (∀ e, e ∈ (pre.chain.toTreeChain.activeLSF j).F.F.E →
          e ∉ (model.chain.toTreeChain.activeLSF j).F.F.E →
          e ∈ batchTouchedEdges (U j)) ∧
        (j < cfg.P.d →
          ∃ ℓj gj ordj,
            let Uout := (cfg.T.updateOrd (model.chain.scState j) (U j) ℓj gj ordj).2
              (model.chain.bran j)
            pre.chain.scState j = (cfg.T.updateOrd (model.chain.scState j) (U j) ℓj gj ordj).1 ∧
            (j + 1 ≤ i → U (j + 1) = Uout) ∧
            (batchTouchedEdges Uout).length ≤ Uout.length ∧
            (∀ e, (∃ u ∈ Uout, u.Inserts e ∨ u = .delete e) → e ∈ batchTouchedEdges Uout) ∧
            (∀ e, (e ∈ (pre.chain.toTreeChain.activeS j).E ↔
              e ∉ (model.chain.toTreeChain.activeS j).E) → e ∈ batchTouchedEdges Uout))) ∧
      (∀ j ≤ i, ∀ f ∈ (pre.chain.G j).E, f ∈ (model.chain.G j).E →
        (∀ u ∈ U j, ¬ u.Inserts f) →
        (∀ m ≤ j, ∀ u ∈ U m, ¬ u.Inserts f) ∧
        (∀ m ≤ j, (pre.chain.toTreeChain.activeLSF m).wstr f =
          (model.chain.toTreeChain.activeLSF m).wstr f) ∧
        pre.chain.toTreeChain.chainLen (fun e' => l_ext (tb.2.2.1 e')) (j + 1) f =
          model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1) f) := by
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := h.2.1
  have hUncond := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hm) (fun t ht => by rw [hGD t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  rcases hUncond with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, _, _, _, _, _, _, _⟩
  have hGT : D.G T_step = G := hGD T_step le_rfl
  have hExtG_G : model.extG = G := hExtG.trans hGT
  have hGValid : G.IsValid := hGT ▸ (hHist.2.1 T_step le_rfl).1
  have hBatch_ext : model.extG.BatchIsValid U_ext := hExtG_G.symm ▸ hU.1
  set tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U_ext
  have hTB := translateBatch_preserves U_ext model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hBatch_ext
  dsimp only at hTB
  rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hExtEq : tb.1 = G := by rw [hExtG', hExtG_G]; exact hU.2.1
  have hEdgeU : ∀ u ∈ U_ext, IsEdgeUpdate u := fun u hu => by
    have hns := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd hns id
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt model.nextFresh U_ext hEdgeU
  have hG0'Valid : ((model.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    hFresh'.isValid_iff.mpr (hExtEq ▸ hGValid)
  have hG0'm : ((model.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hm
  have hG0'n : ((model.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hn
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((model.chain.G 0).applyBatch tb.2.2.2.2)
      (fun e' => l_ext (tb.2.2.1 e')) := by
    intro e' he'
    have heExt : tb.2.2.1 e' ∈ G.E := hExtEq ▸ (hFresh'.hRight e' he').2
    have hpos := hl _ heExt
    have hlog := hlR _ heExt
    have hmax : |Real.log (l_ext (tb.2.2.1 e'))| ≤ max 0 cfg.Ψ := le_trans hlog (le_max_right _ _)
    rw [abs_le] at hmax
    dsimp only
    exact ⟨by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.1,
      by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.2⟩
  have hSurvExt : ∀ e' ∈ ((model.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (model.chain.G 0).E →
      tb.2.2.1 e' = model.intToExt e' ∧
      model.intToExt e' ∈ G.E ∧
      (∀ u ∈ U_ext, ¬ u.Inserts (model.intToExt e')) := by
    intro e' he' he0
    have hlt : e' < model.nextFresh := hFresh.hLtFresh e' he0
    have hi2e_eq : tb.2.2.1 e' = model.intToExt e' := hi2e_old e' hlt
    have heExt : model.intToExt e' ∈ G.E := by
      rw [← hExtEq, ← hi2e_eq]; exact (hFresh'.hRight e' he').2
    refine ⟨hi2e_eq, heExt, fun u hu hIns => ?_⟩
    have hge := hYesInsExt (model.intToExt e') (hExtEq ▸ heExt) ⟨u, hu, hIns⟩
    have he2i'_eq : tb.2.1 (model.intToExt e') = e' := by
      rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
    exact absurd (lt_of_lt_of_le hlt (le_trans hge (le_of_eq he2i'_eq))) (lt_irrefl _)
  have hℓ_intStable : ∀ e' ∈ ((model.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (model.chain.G 0).E →
      (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') →
      (fun e' => l_ext (tb.2.2.1 e')) e' = model.chain.ℓ e' := by
    intro e' he' he0 _
    obtain ⟨hi2e_eq, heExt, hNoIns⟩ := hSurvExt e' he' he0
    dsimp only
    rw [hi2e_eq, (hagree _ heExt hNoIns).2, hChℓ]
  have hConn0 : ∀ u ∈ (model.chain.G 0).V, ∀ v ∈ (model.chain.G 0).V,
      (model.chain.G 0).Connected u v := by
    have hWalk : ∀ {a b : ℕ} {P : List (ℕ × Bool)}, model.extG.IsWalk a b P →
        (model.chain.G 0).Connected a b := by
      intro a b P hW
      induction hW with
      | nil u => exact ⟨[], .nil u⟩
      | @cons u v x P hx hsrc _ ih =>
        obtain ⟨P', hP'⟩ := ih
        have heInt : model.extToInt x.1 ∈ (model.chain.G 0).E :=
          hFresh.hE ▸ Finset.mem_image_of_mem _ hx
        have htail := hFresh.hTail x.1 hx
        have hhead := hFresh.hHead x.1 hx
        have hsrc' : (model.chain.G 0).src (model.extToInt x.1, x.2) = u := by
          by_cases hb : x.2 = true <;> simpa [MGraph.src, hb, htail, hhead] using hsrc
        have hdst' : (model.chain.G 0).dst (model.extToInt x.1, x.2) = model.extG.dst x := by
          by_cases hb : x.2 = true <;> simp [MGraph.dst, hb, htail, hhead]
        exact ⟨(model.extToInt x.1, x.2) :: P', .cons heInt hsrc' (hdst'.symm ▸ hP')⟩
    intro u hu v hv
    have huE : u ∈ G.V := hExtG_G ▸ hFresh.hV ▸ hu
    have hvE : v ∈ G.V := hExtG_G ▸ hFresh.hV ▸ hv
    obtain ⟨P, hP⟩ := hConn u huE v hvE
    exact hWalk (hExtG_G.symm ▸ hP)
  have hℓ0R : LenInRange (max 0 cfg.Ψ) (model.chain.G 0) model.chain.ℓ := by
    intro e' he0
    have heExt : model.intToExt e' ∈ (D.G T_step).E := hExtG ▸ (hFresh.hRight e' he0).2
    have hpos := (hHist.2.1 T_step le_rfl).2 _ heExt
    have hlog := hLenD T_step le_rfl _ heExt
    have hmax : |Real.log (D.ℓ T_step (model.intToExt e'))| ≤ max 0 cfg.Ψ :=
      le_trans hlog (le_max_right _ _)
    rw [abs_le] at hmax
    have hEqℓ : model.chain.ℓ e' = D.ℓ T_step (model.intToExt e') := by
      rw [hChℓ]; exact (hExtLG _ (hExtG ▸ heExt)).1
    rw [hEqℓ]
    exact ⟨by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.1,
      by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.2⟩
  have hShift : ShiftLoopChainInv cfg model.chain := ⟨hInv, ⟨_, hBud⟩, hℓ0R, hConn0⟩
  exact progTool_shiftLoop_update_touched_wstr hT hV hInit hShift tb.2.2.2.2
    (fun e' => g_ext (tb.2.2.1 e')) (fun e' => l_ext (tb.2.2.1 e'))
    hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable

end MinCostFlow.MinRatio
