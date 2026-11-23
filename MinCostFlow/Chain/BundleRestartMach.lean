module

public import MinCostFlow.Chain.BundleRestart
import MinCostFlow.Chain.BundleRestartCost
import MinCostFlow.Chain.LevelConnected
import MinCostFlow.DynSpanner.Walks
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bundle restart tool with the machine cost

The sparse-core machine contract (`SparseCore/Program/Contract.lean`) charges each operation a
constant times the rise of the tool's `cost`. The field `cost` of `BundleTreeState` does not pay
for the machine: it counts each update once, while the order store and the tours spend one search
tree step (a logarithm) per update, the bundle and output batches are written with their moved
sets, the LSF works on fixed-point numbers of several limbs, and the bucket dynamic spanners charge
the explicit Theorem 8.2 bounds (`spanInitBound` and `spanBatchChargeWith`) multiplied by the
spanner constant `spanConst`. The field `machCost` pays for all of these (`BundleTreeCore.lean`).

This file defines `sparseCoreBundleRestartToolMachWith` (for any LSF initializer `lsfInit`,
sparsifier parameters `params : ℕ → SparsifyParams`, and spanner constant `spanConst : ℕ`) and its
specialization `sparseCoreBundleRestartToolMach` at `initLSFOnline oracle C_lsst`
(`toolMachWith_initLSFOnline`, by `rfl`), and proves the structural facts used by the cost bounds:

* `BundleNonMachEq` / `SparseCoreBundleNonMachEq`: the runs of `sparseCoreBundleRestartToolMachWith`
  and `sparseCoreBundleRestartToolWith` agree on every non-machine field (`cs`, `activeComps`,
  `activeBuckets`, `bun`, `initBunG`, `dyn`, `S_cur`, `cost`, and output batches `U_S`), so `lsfs`,
  `S`, `emb`, `rot`, `coreInstanceOrdFrom`, `coreCOrdFrom`, and `coreWOrdFrom` coincide;
* every branch keeps the size bounds `M`, `N`, the spanner parameters `params M`, the spanner
  constant `spanConst`, and `lazyMachInitCost` (`runOrdAfterRestartsMachWith_params`);
* restarts add `singleBundleRestartMachCost` (`foldl_bundleRestartWith_machCost`,
  `bundleRestartToolMachWith_restart_cost_eq`);
* size bounds: `DynSpanner.batchEnc_le_update_cost`, `lsfInitSize G₀ ≤ 4 m`,
  `lsfBatchSize cs U ≤ 4 |U|`, and `bundleLogFactor M N ≤ 16 log² (M + N + 2)`.
-/

@[expose] public section

namespace MinCostFlow.DynSpanner

private lemma step_G_cost_ge {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (step st u sparsify).state.G = st.G.applyUpdate u ∧
      st.G.updateEnc u ≤ (step st u sparsify).cost := by
  unfold step
  dsimp only
  have hmul : st.G.updateEnc u ≤ (L + 1) * st.G.updateEnc u := Nat.le_mul_of_pos_left _ (by omega)
  split
  · exact ⟨rfl, by dsimp only; omega⟩
  · exact ⟨rfl, by dsimp only; omega⟩

private lemma updateGo_cost_ge {L : ℕ} (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    ∀ (us : List Update) (cur : DynSpannerState L) (uhAcc : List Update) (dAcc : Finset ℕ)
      (cAcc : ℕ), cAcc + cur.G.batchEnc us ≤ (updateGo sparsify cur us uhAcc dAcc cAcc).cost
  | [], cur, uhAcc, dAcc, cAcc => by simp [updateGo, MGraph.batchEnc]
  | u :: rest, cur, uhAcc, dAcc, cAcc => by
    obtain ⟨hG, hc⟩ := step_G_cost_ge cur u sparsify
    have ih := updateGo_cost_ge sparsify rest (step cur u sparsify).state
      (uhAcc ++ (step cur u sparsify).UH) (dAcc ∪ (step cur u sparsify).D)
      (cAcc + (step cur u sparsify).cost)
    rw [hG] at ih
    simp only [updateGo, MGraph.batchEnc]
    omega

/-- A batch update of the dynamic spanner costs at least the encoding size of its batch: each
step charges `(L + 1)` times the encoding of its update (Algorithm 6). -/
theorem batchEnc_le_update_cost {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    st.G.batchEnc U ≤ (update st U sparsify).cost := by
  have h := updateGo_cost_ge sparsify U st [] ∅ 0
  simpa [update] using h

end MinCostFlow.DynSpanner

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF

/-- The log factor is at most `16 log² (M + N + 2)`: `⌊log₂ x⌋ ≤ log x / log 2 ≤ 2 log x`, and
`1 ≤ 2 log x` for `x ≥ 2`, since `log 2 ≥ 1 / 2`. -/
theorem bundleLogFactor_le (M N : ℕ) :
    (bundleLogFactor M N : ℝ) ≤ 16 * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ 2 := by
  have hx2 : (2 : ℝ) ≤ (M : ℝ) + (N : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N]
  have hcast : (((M + N + 2 : ℕ) : ℝ)) = (M : ℝ) + (N : ℝ) + 2 := by push_cast; ring
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have hlogx : Real.log 2 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) hx2
  have hnl : (Nat.log 2 (M + N + 2) : ℝ) ≤ Real.logb 2 ((M : ℝ) + (N : ℝ) + 2) := by
    have := Real.natLog_le_logb (M + N + 2) 2
    rw [hcast] at this
    exact_mod_cast this
  have hlogb : Real.logb 2 ((M : ℝ) + (N : ℝ) + 2) ≤ 2 * Real.log ((M : ℝ) + (N : ℝ) + 2) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h1 : ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) ≤ 4 * Real.log ((M : ℝ) + (N : ℝ) + 2) := by
    push_cast
    linarith
  have h0 : (0 : ℝ) ≤ ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold bundleLogFactor
  have hsq := pow_le_pow_left₀ h0 h1 2
  push_cast at hsq ⊢
  nlinarith

/-- The LSF initializations have total size at most `4 m`: a component `C` with an edge is
connected, so `n_C ≤ m_C + 1 ≤ 2 m_C`, and the `m_C` sum to `m`. -/
theorem lsfInitSize_le {G₀ : MGraph} (hG₀ : G₀.IsValid) : lsfInitSize G₀ ≤ 4 * G₀.m := by
  classical
  unfold lsfInitSize
  calc ((components G₀).filter fun C => 1 ≤ (compGraph G₀ C).m).sum
        (fun C => (compGraph G₀ C).m + (compGraph G₀ C).n + 1)
      ≤ ((components G₀).filter fun C => 1 ≤ (compGraph G₀ C).m).sum
        (fun C => 4 * (compGraph G₀ C).m) := by
        refine Finset.sum_le_sum fun C hC => ?_
        obtain ⟨hCc, hm⟩ := Finset.mem_filter.mp hC
        have hn := MinCostFlow.Chain.connected_n_le_m_add_one (compGraph_isValid hG₀ hCc)
          (compGraph_connected hG₀ hCc)
        omega
    _ ≤ (components G₀).sum (fun C => 4 * (compGraph G₀ C).m) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 4 * G₀.m := by rw [← Finset.mul_sum, components_sum_m G₀ hG₀]

/-- The LSF batches of a step have total size at most `6 |U|`: the projected batches have total
length at most `4 |U|` (`sum_projCompBatchG_length_le`), and at most `2 |U|` components are
touched (`touchedCompsBatch_card_le`). -/
theorem lsfBatchSize_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    lsfBatchSize cs U ≤ 6 * U.length := by
  classical
  unfold lsfBatchSize
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 : (touchedCompsBatch cs U).sum (fun C => (projCompBatchG cs.G (cs.compSt C).G U).length) ≤
      (components cs.G₀).sum (fun C => (projCompBatchG cs.G (cs.compSt C).G U).length) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 := sum_projCompBatchG_length_le U hI hU
  have h3 := touchedCompsBatch_card_le hI hU
  omega

end MinCostFlow.SparseCore

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## Tool definitions -/

/-- `sparseCoreBundleRestartToolWith` with the machine cost and explicit spanner-charge
parameters `params` and `spanConst`: the cost of a nonempty state is the sum of `machCost` over its
branches. All non-machine fields agree with `sparseCoreBundleRestartToolWith`. -/
noncomputable def sparseCoreBundleRestartToolMachWith
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    SparseCoreRestartTool :=
  { sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify with
    init := fun k M N G₀ ℓ₀ _g₀ =>
      initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ (sortedEnds G₀)
    initOrd := fun k M N G₀ ℓ₀ _g₀ ord =>
      initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord
    cost := fun st => if st.isNonempty then (Finset.range st.k).sum fun j => (st.trees j).machCost
      else 0 }

/-- `sparseCoreBundleRestartTool` with the machine cost and explicit spanner-charge parameters
`params` and `spanConst`. -/
noncomputable def sparseCoreBundleRestartToolMach
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    SparseCoreRestartTool :=
  sparseCoreBundleRestartToolMachWith (initLSFOnline oracle C_lsst) C_lsst L sparsify params
    spanConst

/-- Specializing `sparseCoreBundleRestartToolMachWith` to `initLSFOnline` recovers
`sparseCoreBundleRestartToolMach` definitionally. -/
theorem toolMachWith_initLSFOnline
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    sparseCoreBundleRestartToolMachWith (initLSFOnline oracle C_lsst) C_lsst L sparsify params
        spanConst =
      sparseCoreBundleRestartToolMach oracle C_lsst L sparsify params spanConst :=
  rfl

lemma sparseCoreBundleRestartToolMachWith_cost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).cost st =
      if st.isNonempty = true then ∑ j ∈ Finset.range st.k, (st.trees j).machCost else 0 := rfl

lemma sparseCoreBundleRestartToolMach_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) :
    (sparseCoreBundleRestartToolMach oracle C_lsst L sparsify params spanConst).cost st =
      if st.isNonempty = true then ∑ j ∈ Finset.range st.k, (st.trees j).machCost else 0 := rfl

lemma sparseCoreBundleRestartToolMachWith_restart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).restart =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart := rfl

lemma sparseCoreBundleRestartToolMach_restart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    (sparseCoreBundleRestartToolMach oracle C_lsst L sparsify params spanConst).restart =
      (sparseCoreBundleRestartTool oracle C_lsst L sparsify).restart := rfl

/-! ## Agreement on all non-machine fields -/

/-- Two `BundleTreeState`s agree on every field except the machine-cost accounting fields
(`spanParams`, `spanConst`, `lazyMachInitCost`, `machCost`). -/
structure BundleNonMachEq {L : ℕ} (a b : BundleTreeState L) : Prop where
  k : a.k = b.k
  m₀ : a.m₀ = b.m₀
  n₀ : a.n₀ = b.n₀
  splitBound : a.splitBound = b.splitBound
  cs : a.cs = b.cs
  activeComps : a.activeComps = b.activeComps
  origBucket : a.origBucket = b.origBucket
  activeBuckets : a.activeBuckets = b.activeBuckets
  bun : a.bun = b.bun
  initBunG : a.initBunG = b.initBunG
  dyn : a.dyn = b.dyn
  S_cur : a.S_cur = b.S_cur
  lazyInitCost : a.lazyInitCost = b.lazyInitCost
  cost : a.cost = b.cost

/-- Two `SparseCoreBundleState`s agree on `isNonempty`, `k`, `ord`, and every branch's non-machine
fields. -/
structure SparseCoreBundleNonMachEq {L : ℕ} (a b : SparseCoreBundleState L) : Prop where
  isNonempty : a.isNonempty = b.isNonempty
  k : a.k = b.k
  ord : a.ord = b.ord
  trees : ∀ j, BundleNonMachEq (a.trees j) (b.trees j)

lemma BundleNonMachEq.init (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    BundleNonMachEq
      (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j)
      (initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma BundleNonMachEq.step {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {a b : BundleTreeState L} (h : BundleNonMachEq a b) (U : List Update)
    (ord ord' : ℕ → List End) :
    let ia := stepBundleTree sparsify a U ord ord'
    let ib := stepBundleTree sparsify b U ord ord'
    BundleNonMachEq ia.state ib.state ∧
      ia.U_B = ib.U_B ∧ ia.U_S = ib.U_S ∧ ia.stepOut = ib.stepOut ∧
      ia.newlyActive = ib.newlyActive := by
  cases a; cases b
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  subst h8; subst h9; subst h10; subst h11; subst h12; subst h13; subst h14
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl⟩

lemma BundleNonMachEq.restart {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {a b : BundleTreeState L} (h : BundleNonMachEq a b) (ord : ℕ → List End) :
    BundleNonMachEq (restartBundleTree L sparsify a ord) (restartBundleTree L sparsify b ord) := by
  cases a; cases b
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  subst h8; subst h9; subst h10; subst h11; subst h12; subst h13; subst h14
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma BundleNonMachEq.emb_eq {L : ℕ} {a b : BundleTreeState L} (h : BundleNonMachEq a b) :
    a.emb = b.emb := by
  funext e
  unfold BundleTreeState.emb
  rw [h.S_cur, h.activeComps, h.activeBuckets, h.bun, h.dyn]

lemma BundleNonMachEq.outOrder_eq {L : ℕ} {a b : BundleTreeState L} (h : BundleNonMachEq a b)
    (ord : ℕ → List End) : a.outOrder ord = b.outOrder ord := by
  cases a; cases b
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  dsimp only at h5 h12
  subst h5; subst h12
  rfl

lemma SparseCoreBundleNonMachEq.init (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) :
    SparseCoreBundleNonMachEq
      (initBundleCoreWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord)
      (initBundleCoreWith lsfInit L sparsify k M N G₀ ℓ₀ ord) :=
  ⟨rfl, rfl, rfl, fun j => BundleNonMachEq.init lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j⟩

lemma SparseCoreBundleNonMachEq.update {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b)
    (U : List Update) (ord' : ℕ → List End) :
    SparseCoreBundleNonMachEq (updateBundleCore sparsify a U ord').1
        (updateBundleCore sparsify b U ord').1 ∧
      (updateBundleCore sparsify a U ord').2 = (updateBundleCore sparsify b U ord').2 := by
  unfold updateBundleCore
  rw [h.isNonempty]
  by_cases hne : b.isNonempty = true
  · simp only [hne, ↓reduceIte]
    refine ⟨⟨rfl, h.k, rfl, fun j => ?_⟩, funext fun j => ?_⟩
    · rw [h.ord]; exact (BundleNonMachEq.step sparsify (h.trees j) U b.ord ord').1
    · rw [h.ord]; exact (BundleNonMachEq.step sparsify (h.trees j) U b.ord ord').2.2.1
  · simp only [hne]
    exact ⟨h, rfl⟩

lemma SparseCoreBundleNonMachEq.restart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b) (j : ℕ) :
    SparseCoreBundleNonMachEq
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart a j)
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart b j) := by
  rw [sparseCoreBundleRestartTool_restart_eq, sparseCoreBundleRestartTool_restart_eq, h.isNonempty]
  by_cases hne : b.isNonempty = true
  · simp only [hne, ↓reduceIte]
    refine ⟨rfl, h.k, h.ord, fun i => ?_⟩
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, h.ord]
      exact BundleNonMachEq.restart sparsify (h.trees i) b.ord
    · simp only [Function.update_of_ne hij]
      exact h.trees i
  · simp only [hne]
    exact h

lemma SparseCoreBundleNonMachEq.foldl_restart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (xs : List ℕ) :
    ∀ {a b : SparseCoreBundleState L}, SparseCoreBundleNonMachEq a b →
      SparseCoreBundleNonMachEq
        (xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart a)
        (xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart b) := by
  induction xs with
  | nil => intro _ _ h; exact h
  | cons x xs ih =>
    intro a b h
    exact ih (SparseCoreBundleNonMachEq.restart lsfInit C_lsst L sparsify h x)

lemma SparseCoreBundleNonMachEq.lsfs_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b) (j : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).lsfs a j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs b j := by
  change (if a.isNonempty then (a.trees j).cs.lsf else emptyLSF) =
    (if b.isNonempty then (b.trees j).cs.lsf else emptyLSF)
  rw [h.isNonempty, (h.trees j).cs]

lemma SparseCoreBundleNonMachEq.S_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b) (j : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).S a j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).S b j := by
  change (if a.isNonempty then (a.trees j).S_cur else emptyGraph) =
    (if b.isNonempty then (b.trees j).S_cur else emptyGraph)
  rw [h.isNonempty, (h.trees j).S_cur]

lemma SparseCoreBundleNonMachEq.emb_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b) (j : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).emb a j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).emb b j := by
  change (if a.isNonempty then (a.trees j).emb else fun _ => []) =
    (if b.isNonempty then (b.trees j).emb else fun _ => [])
  rw [h.isNonempty, (h.trees j).emb_eq]

lemma SparseCoreBundleNonMachEq.rot_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {a b : SparseCoreBundleState L} (h : SparseCoreBundleNonMachEq a b) (j : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).rot a j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).rot b j := by
  change (if a.isNonempty then (a.trees j).outOrder a.ord else fun _ => []) =
    (if b.isNonempty then (b.trees j).outOrder b.ord else fun _ => [])
  rw [h.isNonempty, h.ord, (h.trees j).outOrder_eq]

/-- Along any run, `sparseCoreBundleRestartToolMachWith` and `sparseCoreBundleRestartToolWith`
agree on all non-machine state fields and produce the exact same output batches `U_S`. -/
lemma sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) (t : ℕ) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    SparseCoreBundleNonMachEq
        (Tm.runOrdAfterUpdate k M N D ord restarts t).1
        (Tb.runOrdAfterUpdate k M N D ord restarts t).1 ∧
      (Tm.runOrdAfterUpdate k M N D ord restarts t).2 =
        (Tb.runOrdAfterUpdate k M N D ord restarts t).2 ∧
      SparseCoreBundleNonMachEq
        (Tm.runOrdAfterRestarts k M N D ord restarts t)
        (Tb.runOrdAfterRestarts k M N D ord restarts t) := by
  intro Tm Tb
  induction t with
  | zero =>
    have h0 := SparseCoreBundleNonMachEq.init lsfInit L sparsify params spanConst k M N
      (D.G 0) (D.ℓ 0) (ord 0)
    refine ⟨h0, rfl, ?_⟩
    exact SparseCoreBundleNonMachEq.foldl_restart lsfInit C_lsst L sparsify (restarts 0) h0
  | succ s ih =>
    obtain ⟨_, _, hpost⟩ := ih
    have hstep := SparseCoreBundleNonMachEq.update sparsify hpost (D.U (s + 1)) (ord (s + 1))
    have hpre : SparseCoreBundleNonMachEq
        (Tm.runOrdAfterUpdate k M N D ord restarts (s + 1)).1
        (Tb.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 := by
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ, SparseCoreRestartTool.runOrdAfterUpdate_succ]
      exact hstep.1
    have hU : (Tm.runOrdAfterUpdate k M N D ord restarts (s + 1)).2 =
        (Tb.runOrdAfterUpdate k M N D ord restarts (s + 1)).2 := by
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ, SparseCoreRestartTool.runOrdAfterUpdate_succ]
      exact hstep.2
    refine ⟨hpre, hU, ?_⟩
    exact SparseCoreBundleNonMachEq.foldl_restart lsfInit C_lsst L sparsify (restarts (s + 1)) hpre

lemma sparseCoreBundleRestartToolMachWith_coreInstanceOrdFrom_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).coreInstanceOrdFrom k M N D ord restarts =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).coreInstanceOrdFrom
        k M N D ord restarts := by
  funext s₀ j
  unfold SparseCoreRestartTool.coreInstanceOrdFrom
  have hG : ∀ δ,
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).S
        ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
          spanConst).runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).S
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
          k M N D ord restarts (s₀ + δ)) j := fun δ =>
    SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j
  have hU : ∀ δ,
      ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).2 j =
      ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate
        k M N D ord restarts (s₀ + δ)).2 j := fun δ =>
    congrFun (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
      spanConst k M N D ord restarts (s₀ + δ)).2.1 j
  have hL : ∀ δ,
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).lsfs
        ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
          spanConst).runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
          k M N D ord restarts (s₀ + δ)) j := fun δ =>
    SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j
  congr 1
  · funext δ; exact hG δ
  · funext δ; exact hU δ
  · funext δ e; rw [hL δ]
  · funext δ; rw [hL δ]

lemma sparseCoreBundleRestartToolMachWith_coreCOrdFrom_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).coreCOrdFrom k M N D ord restarts =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).coreCOrdFrom
        k M N D ord restarts := by
  funext c s₀ j δ e
  unfold SparseCoreRestartTool.coreCOrdFrom
  rw [SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j,
    SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j]

lemma sparseCoreBundleRestartToolMachWith_coreWOrdFrom_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).coreWOrdFrom k M N D ord restarts =
      (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).coreWOrdFrom
        k M N D ord restarts := by
  funext w s₀ j δ e
  unfold SparseCoreRestartTool.coreWOrdFrom
  rw [SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j,
    SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst
      (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify params
        spanConst k M N D ord restarts (s₀ + δ)).2.2 j]

/-! ## Parameter preservation along runs -/

/-- Restarts keep `m₀`, `n₀`, `spanParams`, `spanConst`, and `lazyMachInitCost` on every branch. -/
lemma foldl_bundleRestartWith_machParams
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (M N : ℕ) (P_sp : SparsifyParams) (c_sp : ℕ)
    (lazyM : ℕ → Finset ℕ → ℕ) (xs : List ℕ) :
    ∀ (st : SparseCoreBundleState L),
      (∀ j, (st.trees j).m₀ = M ∧ (st.trees j).n₀ = N ∧
        (st.trees j).spanParams = P_sp ∧ (st.trees j).spanConst = c_sp ∧
        (st.trees j).lazyMachInitCost = lazyM j) →
      ∀ j,
        let tr := (xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j
        tr.m₀ = M ∧ tr.n₀ = N ∧ tr.spanParams = P_sp ∧ tr.spanConst = c_sp ∧
          tr.lazyMachInitCost = lazyM j := by
  induction xs with
  | nil => intro st h j; exact h j
  | cons x xs ih =>
    intro st h
    refine ih _ fun j => ?_
    rw [sparseCoreBundleRestartTool_restart_eq]
    by_cases hne : st.isNonempty = true
    · simp only [hne, ↓reduceIte]
      by_cases hjx : j = x
      · subst hjx; simp only [Function.update_self]; exact h j
      · simp only [Function.update_of_ne hjx]; exact h j
    · simp only [hne]; exact h j

/-- Every branch of every stage of a `sparseCoreBundleRestartToolMachWith` run keeps the size
bounds `M` and `N`, the spanner parameters `params M`, the spanner constant `spanConst`, and
`lazyMachInitCost`. -/
lemma runOrdAfterRestartsMachWith_params
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let st₀ := fun j =>
      initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0) (ord 0) j
    ∀ t j,
      let pre := (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j
      let post := (T.runOrdAfterRestarts k M N D ord restarts t).trees j
      (pre.m₀ = M ∧ pre.n₀ = N ∧ pre.spanParams = params M ∧ pre.spanConst = spanConst ∧
        pre.lazyMachInitCost = (st₀ j).lazyMachInitCost) ∧
      (post.m₀ = M ∧ post.n₀ = N ∧ post.spanParams = params M ∧ post.spanConst = spanConst ∧
        post.lazyMachInitCost = (st₀ j).lazyMachInitCost) := by
  intro T st₀ t
  have hpost : ∀ s,
      (∀ j, ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).m₀ = M ∧
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).n₀ = N ∧
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).spanParams = params M ∧
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).spanConst = spanConst ∧
        ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).lazyMachInitCost =
          (st₀ j).lazyMachInitCost) →
      ∀ j, ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).m₀ = M ∧
        ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).n₀ = N ∧
        ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).spanParams = params M ∧
        ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).spanConst = spanConst ∧
        ((T.runOrdAfterRestarts k M N D ord restarts s).trees j).lazyMachInitCost =
          (st₀ j).lazyMachInitCost := fun s h =>
    foldl_bundleRestartWith_machParams lsfInit C_lsst L sparsify M N (params M) spanConst
      (fun j => (st₀ j).lazyMachInitCost) (restarts s) _ h
  have hpre : ∀ s, ∀ j,
      ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).m₀ = M ∧
      ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).n₀ = N ∧
      ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).spanParams = params M ∧
      ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).spanConst = spanConst ∧
      ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j).lazyMachInitCost =
        (st₀ j).lazyMachInitCost := by
    intro s
    induction s with
    | zero => intro j; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | succ s ih =>
      intro j
      have hp := hpost s ih j
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ]
      by_cases hne : (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true
      · have hU : T.updateOrd (T.runOrdAfterRestarts k M N D ord restarts s) (D.U (s + 1))
            (D.ℓ (s + 1)) (D.g (s + 1)) (ord (s + 1)) =
            ({ T.runOrdAfterRestarts k M N D ord restarts s with
              ord := ord (s + 1),
              trees := fun i => (stepBundleTree sparsify
                ((T.runOrdAfterRestarts k M N D ord restarts s).trees i) (D.U (s + 1))
                (T.runOrdAfterRestarts k M N D ord restarts s).ord (ord (s + 1))).state },
             fun i => (stepBundleTree sparsify
                ((T.runOrdAfterRestarts k M N D ord restarts s).trees i) (D.U (s + 1))
                (T.runOrdAfterRestarts k M N D ord restarts s).ord (ord (s + 1))).U_S) :=
          updateBundleCore_of_nonempty hne (D.U (s + 1)) (ord (s + 1))
        rw [hU]
        exact hp
      · have hU : T.updateOrd (T.runOrdAfterRestarts k M N D ord restarts s) (D.U (s + 1))
            (D.ℓ (s + 1)) (D.g (s + 1)) (ord (s + 1)) =
            (T.runOrdAfterRestarts k M N D ord restarts s, fun _ => []) := by
          change updateBundleCore sparsify _ _ _ = _
          simp only [updateBundleCore, hne]
          rfl
        rw [hU]
        exact hp
  intro j
  exact ⟨hpre t j, hpost t (hpre t) j⟩

/-! ## Restart machine-cost lemmas -/

/-- `singleBundleRestartMachCost` is invariant under `restartBundleTree` at the same order. -/
lemma singleBundleRestartMachCost_restartBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    singleBundleRestartMachCost L sparsify (restartBundleTree L sparsify tr ord) ord =
      singleBundleRestartMachCost L sparsify tr ord := by
  classical
  unfold singleBundleRestartMachCost
  have hsum : ∀ (S : Finset (Finset ℕ)) (B : Finset ℕ → Finset ℤ)
      (P_sp : SparsifyParams) (c_sp sp : ℕ),
      S.sum (fun C => (B C).sum fun b =>
        let Hb := normGraph (restartBucketBundle (restartBundleTree L sparsify tr ord) ord C b).graph
        c_sp * spanInitBound P_sp L sp Hb) =
      S.sum (fun C => (B C).sum fun b =>
        let Hb := normGraph (restartBucketBundle tr ord C b).graph
        c_sp * spanInitBound P_sp L sp Hb) := fun S B P_sp c_sp sp =>
    Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun b _ => by
      rw [restartBucketBundle_restartBundleTree]
  exact congrArg (fun x => (tr.cs.G.m + 1 + x) * bundleLogFactor tr.m₀ tr.n₀)
    (hsum tr.activeComps tr.activeBuckets tr.spanParams tr.spanConst tr.splitBound)

/-- Any prefix of restarts at the same step leaves `singleBundleRestartMachCost` of every branch
`j` unchanged. -/
lemma foldl_bundleRestartWith_singleMachCost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (hne : st.isNonempty = true) (j : ℕ) :
    singleBundleRestartMachCost L sparsify
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j)
      st.ord =
      singleBundleRestartMachCost L sparsify (st.trees j) st.ord := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    have hR : T.restart st x =
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees x (restartBundleTree L sparsify (st.trees x) st.ord) } := by
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
    have hne' : (T.restart st x).isNonempty = true := by rw [hR]; exact hne
    have hord' : (T.restart st x).ord = st.ord := by rw [hR]
    change singleBundleRestartMachCost L sparsify
      ((xs.foldl T.restart (T.restart st x)).trees j) st.ord = _
    rw [← hord', ih (T.restart st x) hne', hord', hR]
    dsimp only
    by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact singleBundleRestartMachCost_restartBundleTree sparsify (st.trees j) st.ord
    · simp only [Function.update_of_ne hjx]

/-- Restarting a nonempty state along `xs` adds `singleBundleRestartMachCost` to the machine
cost of branch `j` once per occurrence of `j` in `xs` (for any `lsfInit`). -/
lemma foldl_bundleRestartWith_machCost
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (xs : List ℕ) :
    ∀ (st : SparseCoreBundleState L), st.isNonempty = true → ∀ j,
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees
          j).machCost =
        (st.trees j).machCost + xs.count j * singleBundleRestartMachCost L sparsify (st.trees j)
          st.ord := by
  induction xs with
  | nil => intro st _ j; simp only [List.count_nil, zero_mul, add_zero]; rfl
  | cons x xs ih =>
    intro st hne j
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    have hR : T.restart st x =
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees x (restartBundleTree L sparsify (st.trees x) st.ord) } := by
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
    have hne' : (T.restart st x).isNonempty = true := by rw [hR]; exact hne
    change ((xs.foldl T.restart (T.restart st x)).trees j).machCost = _
    rw [ih _ hne' j, hR]
    dsimp only
    by_cases hjx : j = x
    · subst hjx
      have hsrc := singleBundleRestartMachCost_restartBundleTree sparsify (st.trees j) st.ord
      simp only [Function.update_self, hsrc, List.count_cons_self]
      change (st.trees j).machCost + singleBundleRestartMachCost L sparsify (st.trees j) st.ord +
        _ = _
      ring
    · simp only [Function.update_of_ne hjx]
      rw [List.count_cons_of_ne (Ne.symm hjx)]

/-- Restarting a nonempty state along `xs` adds `singleBundleRestartMachCost` to the machine
cost of branch `j` once per occurrence of `j` in `xs`. -/
lemma foldl_bundleRestart_machCost
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (xs : List ℕ) :
    ∀ (st : SparseCoreBundleState L), st.isNonempty = true → ∀ j,
      ((xs.foldl (sparseCoreBundleRestartTool oracle C_lsst L sparsify).restart st).trees
          j).machCost =
        (st.trees j).machCost + xs.count j * singleBundleRestartMachCost L sparsify (st.trees j)
          st.ord :=
  foldl_bundleRestartWith_machCost (initLSFOnline oracle C_lsst) C_lsst L sparsify xs

/-- Restarting branch `j < st.k` of a nonempty state adds `singleBundleRestartMachCost` to the
machine cost of the tool (for any `lsfInit`). -/
lemma bundleRestartToolMachWith_restart_cost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (j : ℕ) (hne : st.isNonempty = true) (hj : j < st.k) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    T.cost (T.restart st j) =
      T.cost st + singleBundleRestartMachCost L sparsify (st.trees j) st.ord := by
  intro T
  have hmem : j ∈ Finset.range st.k := Finset.mem_range.mpr hj
  have hsum : ∀ f : ℕ → BundleTreeState L,
      ∑ x ∈ Finset.range st.k,
          (Function.update f j (restartBundleTree L sparsify (f j) st.ord) x).machCost =
        ∑ x ∈ Finset.range st.k, (f x).machCost +
          singleBundleRestartMachCost L sparsify (f j) st.ord := by
    intro f
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ (fun x => (f x).machCost) hmem,
      Function.update_self]
    have hrest : ∑ x ∈ (Finset.range st.k).erase j,
        (Function.update f j (restartBundleTree L sparsify (f j) st.ord) x).machCost =
        ∑ x ∈ (Finset.range st.k).erase j, (f x).machCost :=
      Finset.sum_congr rfl fun x hx => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [hrest]
    change (f j).machCost + singleBundleRestartMachCost L sparsify (f j) st.ord + _ = _
    omega
  have hR : T.restart st j =
      { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
        trees := Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) } := by
    dsimp only [T]
    rw [sparseCoreBundleRestartToolMachWith_restart, sparseCoreBundleRestartTool_restart_eq,
      ite_eq_left hne]
  dsimp only [T] at hR ⊢
  rw [hR, sparseCoreBundleRestartToolMachWith_cost_eq, sparseCoreBundleRestartToolMachWith_cost_eq]
  simp only [hne, ↓reduceIte]
  exact hsum st.trees

/-- Restarting branch `j < st.k` of a nonempty state adds `singleBundleRestartMachCost` to the
machine cost of the tool. -/
lemma bundleRestartToolMach_restart_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (st : SparseCoreBundleState L) (j : ℕ) (hne : st.isNonempty = true) (hj : j < st.k) :
    let T := sparseCoreBundleRestartToolMach oracle C_lsst L sparsify params spanConst
    T.cost (T.restart st j) =
      T.cost st + singleBundleRestartMachCost L sparsify (st.trees j) st.ord :=
  bundleRestartToolMachWith_restart_cost_eq (initLSFOnline oracle C_lsst) C_lsst L sparsify
    params spanConst st j hne hj

end MinCostFlow.Chain

end
