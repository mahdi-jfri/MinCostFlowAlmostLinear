module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.Chain.BundleRestartMach
public import MinCostFlow.SparseCore.Program.ContractOrder
import Mathlib.Tactic

/-!
# Monotonicity of chain runtime and tree updates, and sparse-core init size bound

Proves:
- `ToolCostMono`: monotonicity of a sparse-core restart tool's cumulative cost, discharged for
  `sparseCoreBundleRestartToolMachWith` in `sparseCoreBundleRestartToolMachWith_costMono`.
- Monotonicity of `ChainState.totalRuntime` (under `ToolCostMono`) and `ChainState.totalTreeUpdates`
  (unconditional) across `algorithm1_rebuild`, `updateLoop`, `algorithm1_update`, `algorithm1_shift`,
  and `algorithm2_loopWith`.
- `ordWordsOn_eq_of_isRotationOrder` and `sparseCoreInitExtra_le_toolCost`: on a valid connected
  nonempty graph with rotation order `ord`, the extra input-reading size `G.n + G.m + ordWords + 1`
  of `sparseCoreOrdMachineContract.initCost` is at most `6` times `tool.cost (tool.initOrd …)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Chain.Ordered SparseCore SparseCore.Program Bundle DynSpanner

/-! ## 1. Monotonicity of `totalRuntime` and `totalTreeUpdates` -/

/-- Monotonicity of a sparse-core restart tool's cumulative cost under updates and restarts. -/
@[expose] def ToolCostMono (T : SparseCoreRestartTool) : Prop :=
  (∀ st U ℓ g ord, T.cost st ≤ T.cost (T.updateOrd st U ℓ g ord).1) ∧
  (∀ st j, T.cost st ≤ T.cost (T.restart st j))

/-- The concrete machine-cost bundle restart tool satisfies `ToolCostMono`. -/
theorem sparseCoreBundleRestartToolMachWith_costMono
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    ToolCostMono (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst) := by
  let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
  refine ⟨fun (st : SparseCoreBundleState L) U ℓ g ord => ?_, fun (st : SparseCoreBundleState L) j => ?_⟩
  · change (if st.isNonempty = true then ∑ x ∈ Finset.range st.k, (st.trees x).machCost else 0) ≤ _
    by_cases hne : st.isNonempty = true
    · rw [ite_eq_left hne]
      have hupd : (T.updateOrd st U ℓ g ord).1 =
          ⟨st.isNonempty, st.k, ord,
            fun x => (stepBundleTree sparsify (st.trees x) U st.ord ord).state⟩ := by
        change (updateBundleCore sparsify st U ord).1 = _
        rw [updateBundleCore_of_nonempty hne]
      change _ ≤ if (T.updateOrd st U ℓ g ord).1.isNonempty = true then
          ∑ x ∈ Finset.range (T.updateOrd st U ℓ g ord).1.k,
            ((T.updateOrd st U ℓ g ord).1.trees x).machCost
        else 0
      rw [hupd, ite_eq_left hne]
      refine Finset.sum_le_sum fun x _ => ?_
      change (st.trees x).machCost ≤ (stepBundleTree sparsify (st.trees x) U st.ord ord).state.machCost
      rw [stepBundleTree_machCost]
      exact Nat.le_add_right _ _
    · rw [ite_eq_right hne]
      exact Nat.zero_le _
  · change (if st.isNonempty = true then ∑ x ∈ Finset.range st.k, (st.trees x).machCost else 0) ≤ _
    by_cases hne : st.isNonempty = true
    · rw [ite_eq_left hne]
      have hR : T.restart st j =
          { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
            trees := Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) } := by
        change (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j = _
        rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
      change _ ≤ if (T.restart st j).isNonempty = true then
          ∑ x ∈ Finset.range (T.restart st j).k, ((T.restart st j).trees x).machCost
        else 0
      rw [hR, ite_eq_left hne]
      refine Finset.sum_le_sum fun x _ => ?_
      have hfold := foldl_bundleRestartWith_machCost lsfInit C_lsst L sparsify [j] st hne x
      have hEq : ([j].foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees x =
          (Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) x) := by
        change ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j).trees x = _
        rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
      rw [hEq] at hfold
      rw [hfold]
      exact Nat.le_add_right _ _
    · rw [ite_eq_right hne]
      exact Nat.zero_le _

private theorem rebuildSuffix_scState_lt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      k < idx →
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.1 k = sc k ∧
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.2.1 k =
        cEnc k ∧
      (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.2.2.1 k =
        cDec k
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k, hk => by
    dsimp only [Ordered.rebuildSuffix]
    obtain ⟨h1, h2, h3⟩ := rebuildSuffix_scState_lt T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1)
      _ _ _ _ _ _ _ k (Nat.lt_succ_of_lt hk)
    refine ⟨h1.trans (by simp [Nat.ne_of_lt hk]),
      h2.trans (by simp [Nat.ne_of_lt hk]),
      h3.trans (by simp [Nat.ne_of_lt hk])⟩

private theorem sum_range_split {f : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.range b, f i =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.Ico a b, f i := by
  have hdisj : Disjoint (Finset.range a) (Finset.Ico a b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have := Finset.mem_range.mp hx1
    have := (Finset.mem_Ico.mp hx2).1
    omega
  have hunion : Finset.range a ∪ Finset.Ico a b = Finset.range b := by
    ext x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdisj, hunion]

theorem algorithm1_rebuild_totalRuntime_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph) (extraEnc : ℕ) :
    st.totalRuntime ≤ (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.totalRuntime := by
  unfold Ordered.algorithm1_rebuild ChainState.totalRuntime
  split_ifs with hi
  · dsimp only
    let G0 := fun j => if j = i₀ then Gnew else st.G j
    rw [sum_range_split (Nat.le_of_lt hi)]
    have hlow : ∑ j ∈ Finset.range i₀, (T.cost (st.scState j) + st.curEnc j) ≤
        ∑ j ∈ Finset.range P.d,
          (T.cost ((Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
            st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.1 j) +
           (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
            st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.2.2.2.1 j) := by
      rw [sum_range_split (Nat.le_of_lt hi)]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
      have hlt := Finset.mem_range.mp hj
      obtain ⟨h1, h2, _⟩ := rebuildSuffix_scState_lt T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd j hlt
      rw [h1, h2]
    calc st.closedRuntime +
          ((∑ i ∈ Finset.range i₀, (T.cost (st.scState i) + st.curEnc i)) +
            ∑ i ∈ Finset.Ico i₀ P.d, (T.cost (st.scState i) + st.curEnc i)) + st.curLastCost
        = (st.closedRuntime + ∑ i ∈ Finset.Ico i₀ P.d, (T.cost (st.scState i) + st.curEnc i) +
            st.curLastCost) + ∑ i ∈ Finset.range i₀, (T.cost (st.scState i) + st.curEnc i) := by
          omega
      _ ≤ (st.closedRuntime + ∑ i ∈ Finset.Ico i₀ P.d, (T.cost (st.scState i) + st.curEnc i) +
            st.curLastCost + extraEnc) +
          (∑ j ∈ Finset.range P.d,
            (T.cost ((Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
              st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.1 j) +
             (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
              st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.2.2.2.1 j)) +
          (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
            st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.2.2.2.2.2.2.2 := by
          refine le_trans (Nat.add_le_add (Nat.le_add_right _ _) hlow) (Nat.le_add_right _ _)
  · dsimp only; omega

theorem algorithm1_rebuild_totalTreeUpdates_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph) (extraEnc : ℕ) :
    st.totalTreeUpdates ≤ (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.totalTreeUpdates := by
  unfold Ordered.algorithm1_rebuild ChainState.totalTreeUpdates
  split_ifs with hi
  · dsimp only
    let G0 := fun j => if j = i₀ then Gnew else st.G j
    rw [sum_range_split (Nat.le_of_lt hi)]
    have hlow : ∑ j ∈ Finset.range i₀, st.curDecUpdates j ≤
        ∑ j ∈ Finset.range P.d,
          (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ G0
            st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd).2.2.2.2.2.1 j := by
      rw [sum_range_split (Nat.le_of_lt hi)]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
      have hlt := Finset.mem_range.mp hj
      obtain ⟨_, _, h3⟩ := rebuildSuffix_scState_lt T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd j hlt
      rw [h3]
    calc st.closedTreeUpdates +
          ((∑ i ∈ Finset.range i₀, st.curDecUpdates i) +
            ∑ i ∈ Finset.Ico i₀ P.d, st.curDecUpdates i) + st.curLastTreeUpdates
        = (st.closedTreeUpdates + ∑ i ∈ Finset.Ico i₀ P.d, st.curDecUpdates i +
            st.curLastTreeUpdates) + ∑ i ∈ Finset.range i₀, st.curDecUpdates i := by
          omega
      _ ≤ _ := by
          refine le_trans (Nat.add_le_add (Nat.le_add_right _ _) hlow) (Nat.le_add_right _ _)
  · dsimp only; omega

theorem updateLoop_totalRuntime_mono {T : SparseCoreRestartTool} (hM : ToolCostMono T)
    (L : LastLevelTool) (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      st.totalRuntime ≤ (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1.totalRuntime
  | 0, _, st, curG, curU, _ => by
    unfold Ordered.updateLoop
    split_ifs <;> simp only [ChainState.totalRuntime] <;> omega
  | rem + 1, idx, st, curG, curU, curEncStep => by
    unfold Ordered.updateLoop
    split_ifs with hthr
    · exact algorithm1_rebuild_totalRuntime_mono T L P
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
        idx (rebuildStartGraph idx curG) curEncStep
    · dsimp only
      refine le_trans ?_ (updateLoop_totalRuntime_mono hM L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0)
      unfold ChainState.totalRuntime
      dsimp only
      refine Nat.add_le_add_right (Nat.add_le_add_left (Finset.sum_le_sum fun i _ => ?_) _) _
      by_cases h1 : i = idx
      · subst h1; simp only [↓reduceIte]
        exact Nat.add_le_add (hM.1 (st.scState i) curU _ _ _) (Nat.le_add_right _ _)
      · by_cases h2 : i = idx + 1
        · subst h2; simp only [h1, ↓reduceIte]
          exact Nat.add_le_add_left (Nat.le_add_right _ _) _
        · simp only [h1, h2, ↓reduceIte]; exact le_rfl

theorem updateLoop_totalTreeUpdates_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      st.totalTreeUpdates ≤
        (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1.totalTreeUpdates
  | 0, _, st, curG, curU, _ => by
    unfold Ordered.updateLoop
    split_ifs <;> simp only [ChainState.totalTreeUpdates] <;> omega
  | rem + 1, idx, st, curG, curU, curEncStep => by
    unfold Ordered.updateLoop
    split_ifs with hthr
    · exact algorithm1_rebuild_totalTreeUpdates_mono T L P
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
        idx (rebuildStartGraph idx curG) curEncStep
    · dsimp only
      refine le_trans ?_ (updateLoop_totalTreeUpdates_mono T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0)
      unfold ChainState.totalTreeUpdates
      dsimp only
      refine Nat.add_le_add_right (Nat.add_le_add_left (Finset.sum_le_sum fun i _ => ?_) _) _
      split_ifs with h1
      · subst h1; exact Nat.le_add_right _ _
      · exact le_rfl

theorem algorithm1_update_totalRuntime_mono {T : SparseCoreRestartTool} (hM : ToolCostMono T)
    (L : LastLevelTool) (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ) :
    st.totalRuntime ≤ (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1.totalRuntime := by
  unfold Ordered.algorithm1_update
  exact updateLoop_totalRuntime_mono hM L TP P N₀ ℓ' g' P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U)

theorem algorithm1_update_totalTreeUpdates_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (st : ChainState T P) (U : List Update) (g' ℓ' : ℕ → ℝ) :
    st.totalTreeUpdates ≤ (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1.totalTreeUpdates := by
  unfold Ordered.algorithm1_update
  exact updateLoop_totalTreeUpdates_mono T L TP P N₀ ℓ' g' P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U)

theorem algorithm1_shift_totalRuntime_mono {T : SparseCoreRestartTool} (hM : ToolCostMono T)
    (L : LastLevelTool) (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) :
    st.totalRuntime ≤ (Ordered.algorithm1_shift T L P st i₀).1.totalRuntime := by
  unfold Ordered.algorithm1_shift ChainState.totalRuntime
  split_ifs with hi
  · dsimp only
    let newBran := (st.bran i₀ + 1) % P.k
    let sc_i0 := T.restart (st.scState i₀) newBran
    let G0 := fun j => if j = i₀ + 1 then T.S sc_i0 newBran else st.G j
    let sc0 := fun j => if j = i₀ then sc_i0 else st.scState j
    let bran0 := fun j => if j = i₀ then newBran else st.bran j
    let cDec0 := fun j => if j = i₀ then 0 else st.curDecUpdates j
    let cEnc0 := fun j => if j = i₀ + 1 then 0 else st.curEnc j
    rw [sum_range_split (Nat.succ_le_of_lt hi)]
    have hlow : ∑ j ∈ Finset.range (i₀ + 1), (T.cost (st.scState j) + st.curEnc j) ≤
        ∑ j ∈ Finset.range P.d,
          (T.cost ((Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
            G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd).2.1 j) +
           (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
            G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd).2.2.2.2.1 j) := by
      rw [sum_range_split (Nat.succ_le_of_lt hi)]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine Finset.sum_le_sum fun j hj => ?_
      have hlt := Finset.mem_range.mp hj
      obtain ⟨h1, h2, _⟩ := rebuildSuffix_scState_lt T L P st.lvlM st.N₀ st.ℓ st.g
        (P.d - (i₀ + 1)) (i₀ + 1) G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd j hlt
      rw [h1, h2]
      dsimp only [sc0, cEnc0, sc_i0, newBran]
      have hne1 : j ≠ i₀ + 1 := by omega
      simp only [hne1, ↓reduceIte]
      by_cases hji : j = i₀
      · subst hji; simp only [↓reduceIte]
        have := hM.2 (st.scState j) ((st.bran j + 1) % P.k)
        omega
      · simp only [hji, ↓reduceIte]; exact le_rfl
    calc st.closedRuntime +
          ((∑ i ∈ Finset.range (i₀ + 1), (T.cost (st.scState i) + st.curEnc i)) +
            ∑ i ∈ Finset.Ico (i₀ + 1) P.d, (T.cost (st.scState i) + st.curEnc i)) + st.curLastCost
        = (st.closedRuntime + ∑ i ∈ Finset.Ico (i₀ + 1) P.d, (T.cost (st.scState i) + st.curEnc i) +
            st.curLastCost) + ∑ i ∈ Finset.range (i₀ + 1), (T.cost (st.scState i) + st.curEnc i) := by
          omega
      _ ≤ _ := le_trans (Nat.add_le_add_left hlow _) (Nat.le_add_right _ _)
  · dsimp only; exact le_rfl

theorem algorithm1_shift_totalTreeUpdates_mono (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) :
    st.totalTreeUpdates ≤ (Ordered.algorithm1_shift T L P st i₀).1.totalTreeUpdates := by
  unfold Ordered.algorithm1_shift ChainState.totalTreeUpdates
  split_ifs with hi
  · dsimp only
    let newBran := (st.bran i₀ + 1) % P.k
    let sc_i0 := T.restart (st.scState i₀) newBran
    let G0 := fun j => if j = i₀ + 1 then T.S sc_i0 newBran else st.G j
    let sc0 := fun j => if j = i₀ then sc_i0 else st.scState j
    let bran0 := fun j => if j = i₀ then newBran else st.bran j
    let cDec0 := fun j => if j = i₀ then 0 else st.curDecUpdates j
    let cEnc0 := fun j => if j = i₀ + 1 then 0 else st.curEnc j
    rw [sum_range_split (Nat.le_of_lt hi)]
    have hlow : ∑ j ∈ Finset.range i₀, st.curDecUpdates j ≤
        ∑ j ∈ Finset.range P.d,
          (Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
            G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd).2.2.2.2.2.1 j := by
      rw [sum_range_split (Nat.le_of_lt hi)]
      refine le_trans ?_ (Nat.le_add_right _ _)
      refine le_of_eq (Finset.sum_congr rfl fun j hj => ?_)
      have hlt := Finset.mem_range.mp hj
      obtain ⟨_, _, h3⟩ := rebuildSuffix_scState_lt T L P st.lvlM st.N₀ st.ℓ st.g
        (P.d - (i₀ + 1)) (i₀ + 1) G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd j (by omega)
      rw [h3]
      dsimp only [cDec0]
      rw [ite_eq_right (by omega)]
    calc st.closedTreeUpdates +
          ((∑ i ∈ Finset.range i₀, st.curDecUpdates i) +
            ∑ i ∈ Finset.Ico i₀ P.d, st.curDecUpdates i) + st.curLastTreeUpdates
        = (st.closedTreeUpdates + ∑ i ∈ Finset.Ico i₀ P.d, st.curDecUpdates i +
            st.curLastTreeUpdates) + ∑ i ∈ Finset.range i₀, st.curDecUpdates i := by
          omega
      _ ≤ _ := le_trans (Nat.add_le_add (Nat.le_add_right _ _) hlow) (Nat.le_add_right _ _)
  · dsimp only; omega

theorem algorithm2_loopWith_mono {cfg : Alg2Config} (hM : ToolCostMono cfg.T)
    (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P)
    (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    ch.totalRuntime ≤ res.1.totalRuntime ∧
    ch.totalTreeUpdates ≤ res.1.totalTreeUpdates ∧
    res.1.rebuildCount = ch.rebuildCount := by
  suffices h : ∀ N ch branD passes lctOps,
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ N →
      let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      ch.totalRuntime ≤ res.1.totalRuntime ∧
      ch.totalTreeUpdates ≤ res.1.totalTreeUpdates ∧
      res.1.rebuildCount = ch.rebuildCount from
    h _ ch branD passes lctOps le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ch branD passes lctOps hN
    dsimp only
    rw [Ordered.algorithm2_loopWith]
    dsimp only
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
    · rw [dite_eq_left hGood]; exact ⟨le_rfl, le_rfl, rfl⟩
    · rw [dite_eq_right hGood]
      split
      · exact ⟨le_rfl, le_rfl, rfl⟩
      · rename_i i _
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left hCap]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          obtain ⟨h1, h2, h3⟩ := ih (N - 1) (by omega)
            (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _ (by omega)
          have hrcShift : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.rebuildCount =
              ch.rebuildCount := by
            unfold Ordered.algorithm1_shift; dsimp only; split_ifs <;> rfl
          exact ⟨(algorithm1_shift_totalRuntime_mono hM cfg.L cfg.P ch i.val).trans h1,
            (algorithm1_shift_totalTreeUpdates_mono cfg.T cfg.L cfg.P ch i.val).trans h2,
            h3.trans hrcShift⟩
        · rw [dite_eq_right hCap]; exact ⟨le_rfl, le_rfl, rfl⟩

/-- `algorithm2_loopWith` never decreases `totalTreeUpdates` (unconditionally, without
`ToolCostMono`). -/
theorem algorithm2_loopWith_totalTreeUpdates_mono (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P)
    (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    ch.totalTreeUpdates ≤
      (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1.totalTreeUpdates := by
  suffices h : ∀ N ch branD passes lctOps,
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ N →
      ch.totalTreeUpdates ≤
        (Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1.totalTreeUpdates from
    h _ ch branD passes lctOps le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ch branD passes lctOps hN
    rw [Ordered.algorithm2_loopWith]
    dsimp only
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
    · rw [dite_eq_left hGood]
    · rw [dite_eq_right hGood]
      split
      · exact le_rfl
      · rename_i i _
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left hCap]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          exact (algorithm1_shift_totalTreeUpdates_mono cfg.T cfg.L cfg.P ch i.val).trans
            (ih (N - 1) (by omega) (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 _ _ _ (by omega))
        · rw [dite_eq_right hCap]

/-! ## 2. Extra init size bound for `sparseCoreOrdMachineContract` -/

/-- The word length of a rotation order written on `G.V` is `2 * G.n + 2 * G.m + 1`. -/
theorem ordWordsOn_eq_of_isRotationOrder {G : MGraph} {ord : ℕ → List End}
    (hG : G.IsValid) (hrot : IsRotationOrder G ord) :
    ordWordsOn G.V ord = 2 * G.n + 2 * G.m + 1 := by
  classical
  obtain ⟨ρ, hρ⟩ := hrot
  rw [← hρ]
  unfold ordWordsOn
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hlen : ∑ v ∈ G.V, (ρ.order v).length = 2 * G.m := by
    have hcard : ∀ v ∈ G.V, (ρ.order v).length =
        ((G.E ×ˢ (Finset.univ : Finset Bool)).filter fun x => G.src x = v).card := by
      intro v _
      rw [← List.toFinset_card_of_nodup (ρ.nodup v)]
      congr 1
      ext ⟨e, side⟩
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, ρ.mem_order]
    rw [Finset.sum_congr rfl hcard]
    have hmaps : ∀ x ∈ G.E ×ˢ (Finset.univ : Finset Bool), G.src x ∈ G.V := by
      intro ⟨e, side⟩ hx
      have he : e ∈ G.E := (Finset.mem_product.mp hx).1
      cases side
      · exact (hG e he).2
      · exact (hG e he).1
    rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_true_of_mem hmaps,
      Finset.card_product, Finset.card_univ, Fintype.card_bool]
    unfold MGraph.m; ring
  rw [hlen]
  unfold MGraph.n; ring

/-- On a valid connected nonempty graph with `0 < k`, the extra input-reading size
`G.n + G.m + ordWords + 1` of `sparseCoreOrdMachineContract.initCost` is at most `6` times the
machine tool cost of `sparseCoreBundleRestartToolMachWith.initOrd`. -/
theorem sparseCoreInitExtra_le_toolCost
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {k M N ordWords : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End}
    (hk : 0 < k) (hG : G.IsValid) (hne : G.V.Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hord : ordWords ≤ 2 * G.n + 2 * G.m + 1) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    G.n + G.m + ordWords + 1 ≤ 6 * T.cost (T.initOrd k M N G ℓ g ord) := by
  intro T
  have hn : G.n ≤ G.m + 1 := Chain.connected_n_le_m_add_one hG hconn
  have hcost : G.m + 1 ≤ T.cost (T.initOrd k M N G ℓ g ord) := by
    change G.m + 1 ≤ if (initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G ℓ ord).isNonempty = true
      then ∑ j ∈ Finset.range k, (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost
      else 0
    have hneB : (initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G ℓ ord).isNonempty = true := by
      simp [initBundleCoreWithParams, hne]
    rw [ite_eq_left hneB]
    have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
    have hsingle : (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord 0).machCost ≤
        ∑ j ∈ Finset.range k, (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost :=
      Finset.single_le_sum
        (f := fun j => (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G ℓ ord j).machCost)
        (fun _ _ => Nat.zero_le _) h0
    refine le_trans ?_ hsingle
    unfold initBundleTreeWithParams bundleLogFactor
    dsimp only
    have hlog1 : 1 ≤ (Nat.log 2 (M + N + 2) + 1) ^ 2 := by
      have : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
      nlinarith
    have hmul : G.m + 1 ≤ (G.m + 1) * (Nat.log 2 (M + N + 2) + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by omega)
    refine le_trans hmul (Nat.mul_le_mul_right _ ?_)
    omega
  omega


end MinCostFlow.MinRatio
