module

public import MinCostFlow.MinRatio.WireReembPotChain
public import MinCostFlow.MinRatio.WireSelectActiveS

import MinCostFlow.SparseCore.Program.AssemblyModel
import MinCostFlow.Chain.BundleRestartMach
import MinCostFlow.DynSpanner.Walks

/-!
# Bounding the forwarded batch at the last level by tool cost (`WireSelectFwdCost`)

Bounds the forwarded output batch `U_{S, j}` (and in particular `U_{S, d - 1}` entering the last
level `d` at an `Update`) directly by the single-step growth of the tool cost of `sparseCoreProgTool`
with constant `1`, with no amortization or potential needed:

* In `stepBundleTree`, `tr.S_cur.batchEnc info.U_S` enters `machStep` directly, multiplied by
  `bundleLogFactor tr.m₀ tr.n₀ ≥ 1`, so `info.U_S.length ≤ tr.S_cur.batchEnc info.U_S ≤
  info.state.machCost - tr.machCost`.
* Summing over branches `j < st.k` gives, for `T = sparseCoreProgTool lsfInit C_lsst depth impl`
  and any branch `b < st.k`:
  - `progTool_updateOrd_cost_mono`: `T.cost st ≤ T.cost (T.updateOrd st U ℓ g ord').1`.
  - `progTool_updateOrd_batchEnc_le_cost_sub`:
    `(T.S st b).batchEnc ((T.updateOrd st U ℓ g ord').2 b) ≤ T.cost st' - T.cost st`.
  - `progTool_updateOrd_fwd_length_le_cost_sub`:
    `((T.updateOrd st U ℓ g ord').2 b).length ≤ T.cost st' - T.cost st`.
* On every chain meeting `ChainInv`, `ShiftLoopChainInv`, or `OrdSolverReachedInv`, every level
  `idx < P.d` satisfies `ch.bran idx < (scState idx).k` (`progTool_chainInv_bran_lt_k`,
  `progTool_shiftLoop_bran_lt_k`, `progTool_reachedInv_bran_lt_k`).
* Plugging into `updateLoop_level_step` and `selectUpdateLevel_paid_step` (`WireReembPotChain.lean`)
  bounds both `nextU.length` and `(ch.G (idx + 1)).batchEnc nextU` at `idx = d - 1` by
  `Δ T.cost ≤ Δ totalRuntime`, eliminating the leftover `if idx + 1 < P.d then 0 else nextU.length`
  term in `selectUpdateLevel_paid_step_progTool`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-! ## 1. Per-branch and tool-level bounds -/

private theorem one_le_bundleLogFactor_aux (M N : ℕ) : 1 ≤ bundleLogFactor M N := by
  unfold bundleLogFactor
  exact Nat.one_le_pow 2 _ (Nat.succ_pos _)

/-- `stepBundleTree` never decreases `machCost`. -/
theorem stepBundleTree_machCost_mono {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    tr.machCost ≤ (stepBundleTree sparsify tr U ord ord').state.machCost :=
  Nat.le_add_right _ _

/-- The Lemma 2.1 encoding size of `info.U_S` on `tr.S_cur` is at most the single-step growth of
`machCost` (constant `1`). -/
theorem stepBundleTree_batchEnc_le_machCost_sub {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify tr U ord ord'
    tr.S_cur.batchEnc info.U_S ≤ info.state.machCost - tr.machCost := by
  intro info
  have hmc := stepBundleTree_machCost sparsify tr U ord ord'
  have hlog : 1 ≤ bundleLogFactor tr.m₀ tr.n₀ := one_le_bundleLogFactor_aux tr.m₀ tr.n₀
  have h1 : tr.S_cur.batchEnc info.U_S ≤
      U.length +
      (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        (tr.dyn (C, b)).G.batchEnc (info.U_B (C, b))) +
      tr.S_cur.batchEnc info.U_S +
      (info.state.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
        spanBatchChargeWith tr.spanConst tr.spanParams L ((tr.initBunG (C, b)).n + tr.splitBound)
          (tr.initBunG (C, b)) (tr.dyn (C, b)).G (info.U_B (C, b))) +
      lsfBatchSize tr.cs U +
      info.newlyActive.sum fun C => tr.lazyMachInitCost C := by
    omega
  have h2 := le_trans h1 (Nat.le_mul_of_pos_right _ hlog)
  dsimp only [info] at h2 ⊢
  omega

/-- The length of `info.U_S` is at most the single-step growth of `machCost` (constant `1`). -/
theorem stepBundleTree_US_length_le_machCost_sub {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify tr U ord ord'
    info.U_S.length ≤ info.state.machCost - tr.machCost :=
  le_trans (MinCostFlow.DynSpanner.length_le_batchEnc tr.S_cur _)
    (stepBundleTree_batchEnc_le_machCost_sub sparsify tr U ord ord')

private theorem machTool_updateOrd_cost_mono {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    T.cost st ≤ T.cost (T.updateOrd st U ℓ g ord').1 := by
  intro T
  by_cases hne : st.isNonempty = true
  · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst st hne U ℓ g ord'
    have hne' : (T.updateOrd st U ℓ g ord').1.isNonempty = true := by rw [hup]; exact hne
    have hc : T.cost st = (Finset.range st.k).sum fun j => (st.trees j).machCost := by
      change (if st.isNonempty then _ else 0) = _; simp [hne]
    have hc' : T.cost (T.updateOrd st U ℓ g ord').1 =
        (Finset.range st.k).sum fun j =>
          (stepBundleTree sparsify (st.trees j) U st.ord ord').state.machCost := by
      change (if (T.updateOrd st U ℓ g ord').1.isNonempty then _ else 0) = _
      simp only [hne', ↓reduceIte]
      rw [hup]
    rw [hc, hc']
    exact Finset.sum_le_sum fun j _ => stepBundleTree_machCost_mono sparsify (st.trees j) U st.ord ord'
  · have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hne
    have hc : T.cost st = 0 := by change (if st.isNonempty then _ else 0) = 0; simp [hf]
    rw [hc]; exact Nat.zero_le _

private theorem machTool_updateOrd_batchEnc_le_cost_sub {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    {b : ℕ} (hb : b < st.k) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    (T.S st b).batchEnc ((T.updateOrd st U ℓ g ord').2 b) ≤
      T.cost (T.updateOrd st U ℓ g ord').1 - T.cost st := by
  intro T
  by_cases hne : st.isNonempty = true
  · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst st hne U ℓ g ord'
    have hne' : (T.updateOrd st U ℓ g ord').1.isNonempty = true := by rw [hup]; exact hne
    have hS : T.S st b = (st.trees b).S_cur := by
      change (if st.isNonempty then _ else _) = _; simp [hne]
    have hU : (T.updateOrd st U ℓ g ord').2 b =
        (stepBundleTree sparsify (st.trees b) U st.ord ord').U_S := by rw [hup]
    have hc : T.cost st = (Finset.range st.k).sum fun j => (st.trees j).machCost := by
      change (if st.isNonempty then _ else 0) = _; simp [hne]
    have hc' : T.cost (T.updateOrd st U ℓ g ord').1 =
        (Finset.range st.k).sum fun j =>
          (stepBundleTree sparsify (st.trees j) U st.ord ord').state.machCost := by
      change (if (T.updateOrd st U ℓ g ord').1.isNonempty then _ else 0) = _
      simp only [hne', ↓reduceIte]
      rw [hup]
    have hbm : b ∈ Finset.range st.k := Finset.mem_range.mpr hb
    have hrest : ((Finset.range st.k).erase b).sum (fun j => (st.trees j).machCost) ≤
        ((Finset.range st.k).erase b).sum
          (fun j => (stepBundleTree sparsify (st.trees j) U st.ord ord').state.machCost) :=
      Finset.sum_le_sum fun j _ => stepBundleTree_machCost_mono sparsify (st.trees j) U st.ord ord'
    have hsplit1 := (Finset.add_sum_erase (Finset.range st.k)
      (fun j => (st.trees j).machCost) hbm).symm
    have hsplit2 := (Finset.add_sum_erase (Finset.range st.k)
      (fun j => (stepBundleTree sparsify (st.trees j) U st.ord ord').state.machCost) hbm).symm
    have hsingle := stepBundleTree_batchEnc_le_machCost_sub sparsify (st.trees b) U st.ord ord'
    have hmono := stepBundleTree_machCost_mono sparsify (st.trees b) U st.ord ord'
    rw [hS, hU, hc, hc', hsplit1, hsplit2]
    omega
  · have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst st hf U ℓ g ord'
    have hU : (T.updateOrd st U ℓ g ord').2 b = [] := by rw [hup]
    rw [hU]; simp [MGraph.batchEnc]

/-- Updating `sparseCoreProgTool` never decreases `T.cost`. -/
theorem progTool_updateOrd_cost_mono {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} (st : SparseCoreBundleState depth) (U : List Update)
    (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    T.cost st ≤ T.cost (T.updateOrd st U ℓ g ord').1 :=
  machTool_updateOrd_cost_mono (lsfInit := lsfInit) (C_lsst := C_lsst)
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    st U ℓ g ord'

/-- For every branch `b < st.k` of `sparseCoreProgTool`, the encoding size of the forwarded batch
`(T.updateOrd st U ℓ g ord').2 b` on `T.S st b` is at most `T.cost st' - T.cost st` (constant `1`). -/
theorem progTool_updateOrd_batchEnc_le_cost_sub {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} (st : SparseCoreBundleState depth) (U : List Update)
    (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) {b : ℕ} (hb : b < st.k) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    (T.S st b).batchEnc ((T.updateOrd st U ℓ g ord').2 b) ≤
      T.cost (T.updateOrd st U ℓ g ord').1 - T.cost st :=
  machTool_updateOrd_batchEnc_le_cost_sub (lsfInit := lsfInit) (C_lsst := C_lsst)
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    st U ℓ g ord' hb

/-- For every branch `b < st.k` of `sparseCoreProgTool`, the length of the forwarded batch
`(T.updateOrd st U ℓ g ord').2 b` is at most `T.cost st' - T.cost st` (constant `1`). -/
theorem progTool_updateOrd_fwd_length_le_cost_sub {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} (st : SparseCoreBundleState depth) (U : List Update)
    (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) {b : ℕ} (hb : b < st.k) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    ((T.updateOrd st U ℓ g ord').2 b).length ≤
      T.cost (T.updateOrd st U ℓ g ord').1 - T.cost st :=
  le_trans (MinCostFlow.DynSpanner.length_le_batchEnc _ _)
    (progTool_updateOrd_batchEnc_le_cost_sub st U ℓ g ord' hb)

/-! ## 2. `st.k = P.k` on reached chain states -/

private theorem machTool_restart_k_eq {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (j : ℕ) :
    ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).restart st j).k =
      st.k := by
  have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify st j
  change ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st j).k = st.k
  rw [hR]
  split_ifs <;> rfl

private theorem machTool_foldl_restart_k_eq {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State)
    (rs : List ℕ) :
    (SparseCoreBundleState.k (L := L)
      (rs.foldl (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).restart st)) =
      SparseCoreBundleState.k (L := L) st := by
  induction rs generalizing st with
  | nil => rfl
  | cons j rest ih =>
    exact (ih _).trans (machTool_restart_k_eq sparsify params spanConst st j)

private theorem machTool_runOrdAfterRestarts_k_eq {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    ∀ t, SparseCoreBundleState.k (L := L)
        ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
          k M N D ord restarts t) = k
  | 0 => by
    refine (machTool_foldl_restart_k_eq sparsify params spanConst _ _).trans ?_
    rfl
  | t + 1 => by
    refine (machTool_foldl_restart_k_eq sparsify params spanConst _ _).trans ?_
    set prev : SparseCoreBundleState L :=
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).runOrdAfterRestarts
        k M N D ord restarts t
    have ih := machTool_runOrdAfterRestarts_k_eq (lsfInit := lsfInit) (C_lsst := C_lsst) (L := L)
      sparsify params spanConst k M N D ord restarts t
    change ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).updateOrd
      prev (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1)) (ord (t + 1))).1.k = k
    by_cases hne : prev.isNonempty = true
    · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst prev hne]
      exact ih
    · have hf : prev.isNonempty = false := Bool.eq_false_iff.mpr hne
      rw [asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst prev hf]
      exact ih

/-- Along any `runOrdAfterRestarts k M N ...` of `sparseCoreProgTool`, `st.k = k`. -/
theorem progTool_runOrdAfterRestarts_k_eq {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (restarts : ℕ → List ℕ) (t : ℕ) :
    ((sparseCoreProgTool lsfInit C_lsst depth impl).runOrdAfterRestarts k M N D ord restarts t).k = k :=
  machTool_runOrdAfterRestarts_k_eq (lsfInit := lsfInit) (C_lsst := C_lsst)
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    k M N D ord restarts t

/-- On any chain meeting `Ordered.ChainInv` for `sparseCoreProgTool`, every level `i < P.d` has
`(ch.scState i).k = P.k` and `ch.bran i < (ch.scState i).k`. -/
theorem progTool_chainInv_bran_lt_k {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {ch : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ ch)
    {i : ℕ} (hi : i < P.d) :
    (ch.scState i).k = P.k ∧ ch.bran i < (ch.scState i).k := by
  obtain ⟨H⟩ := hInv.hHist i hi
  have hk : (ch.scState i).k = P.k := by
    rw [H.hRun]
    exact progTool_runOrdAfterRestarts_k_eq P.k (levelM TP P i) N₀ H.D H.ord H.restarts H.len
  exact ⟨hk, hk.symm ▸ hInv.hBran i hi⟩

/-- On a chain meeting `ShiftLoopChainInv` with tool `sparseCoreProgTool`, every level `i < cfg.P.d`
satisfies `ch.bran i < (hT ▸ ch.scState i).k`. -/
theorem progTool_shiftLoop_bran_lt_k {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    {ch : ChainState cfg.T cfg.P} (h : ShiftLoopChainInv cfg ch)
    {i : ℕ} (hi : i < cfg.P.d) :
    ch.bran i <
      SparseCoreBundleState.k (L := depth)
        (hT ▸ ch.scState i : (sparseCoreProgTool lsfInit C_lsst depth impl).State) := by
  rcases cfg with ⟨T, L, TP, LP, P, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT
  subst hT
  exact (progTool_chainInv_bran_lt_k h.1 hi).2

/-- On a solver state meeting `OrdSolverReachedInv` with `ValidOrdNoHidden` and tool
`sparseCoreProgTool`, every level `i < cfg.P.d` satisfies
`model.chain.bran i < (hT ▸ model.chain.scState i).k`. -/
theorem progTool_reachedInv_bran_lt_k {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden) (hm : G.m ≤ cfg.P.M₀) (hn : G.n ≤ cfg.N₀)
    (h : OrdSolverReachedInv κ G P model tok)
    {i : ℕ} (hi : i < cfg.P.d) :
    model.chain.bran i <
      SparseCoreBundleState.k (L := depth)
        (hT ▸ model.chain.scState i : (sparseCoreProgTool lsfInit C_lsst depth impl).State) := by
  obtain ⟨D, η, op, T_step, hHist, hEdge, hLen, hG, hEq⟩ := h.2.1
  have hUncond := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdge hLen
    (fun t ht => by rw [hG t ht]; exact hm) (fun t ht => by rw [hG t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  have hInv := hUncond.1
  rcases cfg with ⟨T, Ltool, TP, LP, Pch, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT
  subst hT
  exact (progTool_chainInv_bran_lt_k hInv hi).2

/-! ## 3. Last-level forwarded batch in `updateLoop` and `selectUpdateLevel_paid_step` -/

/-- **Forwarded batch at any non-rebuilt level `idx < P.d` (including `idx = P.d - 1`).**
For `T = sparseCoreProgTool`, when `stNext` is the next state of `updateLoop_level_step` at level
`idx < P.d`, both the length and the Lemma 2.1 encoding size of the forwarded batch `nextU` are
bounded (with constant `1`) by the growth of the tool cost of level `idx`, and hence by
`stNext.totalRuntime - st.totalRuntime`. -/
theorem progTool_updateLoop_fwd_le_runtime_sub {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {P : ChainParams}
    {st stNext : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {idx : ℕ} {curU : List Update} {ℓi gi : ℕ → ℝ} {ord' : ℕ → List End} {e : ℕ}
    (hbr : st.bran idx < (st.scState idx).k)
    (hGsucc : st.G (idx + 1) = (sparseCoreProgTool lsfInit C_lsst depth impl).S
      (st.scState idx) (st.bran idx))
    (hRt :
      let T := sparseCoreProgTool lsfInit C_lsst depth impl
      let res := T.updateOrd (st.scState idx) curU ℓi gi ord'
      let nextU := res.2 (st.bran idx)
      stNext.totalRuntime + T.cost (st.scState idx) =
        st.totalRuntime + T.cost res.1 + e +
          (if idx + 1 < P.d then (st.G (idx + 1)).batchEnc nextU else 0)) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let res := T.updateOrd (st.scState idx) curU ℓi gi ord'
    let nextU := res.2 (st.bran idx)
    nextU.length ≤ (st.G (idx + 1)).batchEnc nextU ∧
    (st.G (idx + 1)).batchEnc nextU ≤ T.cost res.1 - T.cost (st.scState idx) ∧
    T.cost res.1 - T.cost (st.scState idx) ≤ stNext.totalRuntime - st.totalRuntime := by
  dsimp only at hRt ⊢
  have h1 := MinCostFlow.DynSpanner.length_le_batchEnc (st.G (idx + 1))
    (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').2
      (st.bran idx))
  have h2 : (st.G (idx + 1)).batchEnc
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').2
        (st.bran idx)) ≤
      (sparseCoreProgTool lsfInit C_lsst depth impl).cost
        ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').1 -
      (sparseCoreProgTool lsfInit C_lsst depth impl).cost (st.scState idx) := by
    rw [hGsucc]
    exact progTool_updateOrd_batchEnc_le_cost_sub (st.scState idx) curU ℓi gi ord' hbr
  have hmono := progTool_updateOrd_cost_mono (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    (st.scState idx) curU ℓi gi ord'
  dsimp only at hmono
  have h3 : (sparseCoreProgTool lsfInit C_lsst depth impl).cost
        ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').1 -
      (sparseCoreProgTool lsfInit C_lsst depth impl).cost (st.scState idx) ≤
      stNext.totalRuntime - st.totalRuntime := by
    split_ifs at hRt <;> omega
  exact ⟨h1, h2, h3⟩

/-- **`selectUpdateLevel_paid_step` for `sparseCoreProgTool`, with the last-level forwarded batch
absorbed into `Δ totalRuntime`.** Eliminates the explicit `if idx + 1 < P.d then 0 else nextU.length`
term of `selectUpdateLevel_paid_step` (`WireReembPotChain.lean`) by raising the `totalRuntime`
multiplier from `K * (c + 1)` to `K * (c + 2)`. -/
theorem selectUpdateLevel_paid_step_progTool {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {P : ChainParams}
    {st stNext : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {idx : ℕ} {curU : List Update} {ℓi gi : ℕ → ℝ} {ord' : ℕ → List End} {e fiLen : ℕ}
    (hidx : idx < P.d) (hbr : st.bran idx < (st.scState idx).k)
    (hsc : ∀ j, stNext.scState j =
      if j = idx then ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').1
      else st.scState j)
    (hRt :
      let T := sparseCoreProgTool lsfInit C_lsst depth impl
      let res := T.updateOrd (st.scState idx) curU ℓi gi ord'
      let nextU := res.2 (st.bran idx)
      stNext.totalRuntime + T.cost (st.scState idx) =
        st.totalRuntime + T.cost res.1 + e +
          (if idx + 1 < P.d then (st.G (idx + 1)).batchEnc nextU else 0))
    (hTu : stNext.totalTreeUpdates = st.totalTreeUpdates + fiLen)
    {L : LevelDiffLists} {cap Lk evalCost K c : ℕ}
    (hK : selectProcessEdgeCost cap Lk evalCost + 40 ≤ K)
    (hre :
      let T := sparseCoreProgTool lsfInit C_lsst depth impl
      let sc' := (T.updateOrd (st.scState idx) curU ℓi gi ord').1
      ReembCostBound L.reemb (T.cost sc' - T.cost (st.scState idx)) c
        (progReembPot (st.scState idx)) (progReembPot sc'))
    (hlen :
      let T := sparseCoreProgTool lsfInit C_lsst depth impl
      let nextU := (T.updateOrd (st.scState idx) curU ℓi gi ord').2 (st.bran idx)
      L.uG.length + L.fDel.length + L.uS.length ≤ curU.length + nextU.length + fiLen) :
    selectUpdateLevelCost L cap Lk evalCost + K * chainReembPot progReembPot stNext ≤
      140 + K * c + K * curU.length +
        K * (c + 2) * (stNext.totalRuntime - st.totalRuntime) +
        K * (stNext.totalTreeUpdates - st.totalTreeUpdates) +
        K * chainReembPot progReembPot st := by
  dsimp only at hRt hre hlen
  have hmono := progTool_updateOrd_cost_mono (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    (st.scState idx) curU ℓi gi ord'
  dsimp only at hmono
  have hbase := selectUpdateLevel_paid_step progReembPot hsc hidx hRt hTu hmono hK hre hlen
  have hfwd_len := progTool_updateOrd_fwd_length_le_cost_sub (lsfInit := lsfInit) (C_lsst := C_lsst)
    (impl := impl) (st.scState idx) curU ℓi gi ord' hbr
  dsimp only at hfwd_len
  have hcost_le_rt : (sparseCoreProgTool lsfInit C_lsst depth impl).cost
        ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').1 -
      (sparseCoreProgTool lsfInit C_lsst depth impl).cost (st.scState idx) ≤
      stNext.totalRuntime - st.totalRuntime := by
    split_ifs at hRt <;> omega
  have hlast_le :
      (if idx + 1 < P.d then 0
        else (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState idx) curU ℓi gi ord').2
          (st.bran idx)).length) ≤
        stNext.totalRuntime - st.totalRuntime := by
    split_ifs
    · exact Nat.zero_le _
    · exact le_trans hfwd_len hcost_le_rt
  have hKlast := Nat.mul_le_mul_left K hlast_le
  have hmul : K * (c + 2) * (stNext.totalRuntime - st.totalRuntime) =
      K * (c + 1) * (stNext.totalRuntime - st.totalRuntime) +
      K * (stNext.totalRuntime - st.totalRuntime) := by ring
  omega

end MinCostFlow.MinRatio
