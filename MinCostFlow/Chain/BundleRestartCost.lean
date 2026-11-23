module

public import MinCostFlow.Chain.BundleRestartSpec
public import MinCostFlow.SparseCore.BundleCostEnv
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cost of One Restart of `sparseCoreBundleRestartTool`

Bounds the work `singleBundleRestartCost` of restarting one branch `j` of
`sparseCoreBundleRestartTool` (paper Lemma 5.17, pages 23–24).
Because a restart re-bundles only the surviving initially-admitted edges of each active bucket on
the current tours, the total bucket edge count stays at most `(D.G 0).m ≤ M`, every rebuilt bundle
graph is valid with `n ≤ 2 m`, and the current graph has at most `2 M` edges. Applying Theorem 8.2
with no update batches, `bundleInitBuckets_cost_sum_le`, and `bundleRestartCost_le_params` yields
the cost clause of item 3 of `IsSpecOrdRestart` without any input degree bound or `hComp_bound`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

lemma restartBundleTree_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    (restartBundleTree L sparsify tr ord).cost =
      tr.cost + singleBundleRestartCost L sparsify tr ord :=
  rfl

/-- `singleBundleRestartCost` is invariant under `restartBundleTree` at the same order `ord`,
because `restartBucketBundle` is idempotent on `restartBundleTree`. -/
lemma singleBundleRestartCost_restartBundleTree {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (ord : ℕ → List End) :
    singleBundleRestartCost L sparsify (restartBundleTree L sparsify tr ord) ord =
      singleBundleRestartCost L sparsify tr ord := by
  classical
  unfold singleBundleRestartCost
  have hsum : ∀ (S : Finset (Finset ℕ)) (B : Finset ℕ → Finset ℤ) (sp m₀ : ℕ),
      S.sum (fun C => (B C).sum fun b =>
        let Hb := normGraph (restartBucketBundle (restartBundleTree L sparsify tr ord) ord C b).graph
        (DynSpanner.init Hb L (phaseBase (Hb.n + sp) L) (sparsify m₀)).cost) =
      S.sum (fun C => (B C).sum fun b =>
        let Hb := normGraph (restartBucketBundle tr ord C b).graph
        (DynSpanner.init Hb L (phaseBase (Hb.n + sp) L) (sparsify m₀)).cost) := fun S B sp m₀ =>
    Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun b _ => by
      rw [restartBucketBundle_restartBundleTree]
  exact congrArg (tr.cs.G.m + 1 + ·) (hsum tr.activeComps tr.activeBuckets tr.splitBound tr.m₀)

/-- Any prefix of restarts at the same step leaves `singleBundleRestartCost` of every branch `j`
unchanged. -/
lemma foldl_bundleRestart_singleCost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreBundleState L) (hne : st.isNonempty = true) (j : ℕ) :
    singleBundleRestartCost L sparsify
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j) st.ord =
      singleBundleRestartCost L sparsify (st.trees j) st.ord := by
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
    change singleBundleRestartCost L sparsify
      ((xs.foldl T.restart (T.restart st x)).trees j) st.ord = _
    rw [← hord', ih (T.restart st x) hne', hord', hR]
    dsimp only
    by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact singleBundleRestartCost_restartBundleTree sparsify (st.trees j) st.ord
    · simp only [Function.update_of_ne hjx]

/-- Restarting branch `j < st.k` of a nonempty state adds `singleBundleRestartCost` to the total
cost. -/
lemma bundleRestartTool_restart_cost_eq
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreBundleState L) (j : ℕ) (hne : st.isNonempty = true) (hj : j < st.k) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    T.cost (T.restart st j) = T.cost st + singleBundleRestartCost L sparsify (st.trees j) st.ord := by
  intro T
  have hmem : j ∈ Finset.range st.k := Finset.mem_range.mpr hj
  have hsum : ∀ f : ℕ → BundleTreeState L,
      ∑ x ∈ Finset.range st.k,
          (Function.update f j (restartBundleTree L sparsify (f j) st.ord) x).cost =
        ∑ x ∈ Finset.range st.k, (f x).cost + singleBundleRestartCost L sparsify (f j) st.ord := by
    intro f
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ (fun x => (f x).cost) hmem,
      Function.update_self, restartBundleTree_cost]
    have hrest : ∑ x ∈ (Finset.range st.k).erase j,
        (Function.update f j (restartBundleTree L sparsify (f j) st.ord) x).cost =
        ∑ x ∈ (Finset.range st.k).erase j, (f x).cost :=
      Finset.sum_congr rfl fun x hx => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [hrest]
    omega
  have hR : T.restart st j =
      { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
        trees := Function.update st.trees j (restartBundleTree L sparsify (st.trees j) st.ord) } := by
    dsimp only [T]
    rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
  dsimp only [T] at hR ⊢
  rw [hR, sparseCoreBundleRestartTool_cost_eq, sparseCoreBundleRestartTool_cost_eq]
  simp only [hne, ↓reduceIte]
  exact hsum st.trees

/-- Bound on `singleBundleRestartCost` at step `r ≤ τ` for `(pre r).trees j` at `(M, N)` without
any input degree bound or `hComp_bound`. -/
lemma singleBundleRestartCost_pre_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (r j : ℕ) (hj : j < k) (hr : r ≤ τ) :
    let T_tool := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let tr := (T_tool.runOrdAfterUpdate k M N D ord restarts r).1.trees j
    let P := bundleCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
    let T := ((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) * logMN ^ (p_max + 1)
    (singleBundleRestartCost E.L sparsify tr (ord r) : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T ∧
    (singleBundleRestartCost E.L sparsify tr (ord r) : ℝ) + 12600 * (7 : ℝ) ^ p_max * T ≤ P.c_T * T ∧
    (singleBundleRestartCost E.L sparsify tr (ord r) : ℝ) +
      12600 * (7 : ℝ) ^ p_max * (((k : ℝ) + 1) * T) ≤ P.c_T * (((k : ℝ) + 1) * T) := by
  classical
  intro T_tool tr P p_max logMN T
  have hk1 : 1 ≤ k := hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hBun := runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify
    k M N τ hk1 D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j (hHyps.hInit j hj) r hr
  set st₀ := initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
  set actB := st₀.activeBuckets
  have hk_tr : tr.k = k := hBun.1
  have hm0_tr : tr.m₀ = M := hBun.2.1
  have hAB : tr.activeBuckets = actB := hBun.2.2.2.2.1
  have hI_r : CompLSFInv E.C_lsst (D.ℓ 0) tr.cs := hBun.2.2.2.2.2.2.2.1
  have hcsG : tr.cs.G = D.G r := hBun.2.2.2.2.2.2.2.2.1
  have hact : tr.activeComps ⊆ components (D.G 0) := hBun.2.2.2.2.2.2.2.2.2.1.2
  have hm_cur : tr.cs.G.m ≤ 2 * M := by
    rw [hcsG]
    have h1 := dyn_G_m_le hD r hr
    have h2 := (updateThreshold_le_div_k_at hk hN_pos hThresh r hr).2
    omega
  obtain ⟨hcard0, hm0_sum, _, _⟩ := initBundleTreeWith_buckets_sum_le lsfInit E.L sparsify
    (M := M) (N := N) hk1 (G₀ := D.G 0) (D.ℓ 0) (ord 0) j
  have hE_sub0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (restartBucketBundle tr (ord r) C b).edges ⊆ (st₀.bun (C, b)).edges := by
    intro C hC b
    have hsub1 : (restartBucketBundle tr (ord r) C b).edges ⊆ (tr.bun (C, b)).edges :=
      initBundleFor_edges_subset tr.cs (ord r) (tr.bun (C, b)).edges tr.k
    have hsub2 : (tr.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := by
      rw [((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]
      exact Finset.sdiff_subset
    exact hsub1.trans hsub2
  have hm_sum : (components (D.G 0)).sum
      (fun C => (actB C).sum fun b => (restartBucketBundle tr (ord r) C b).graph.m) ≤ M := by
    refine le_trans (le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) hm0_sum) hM
    exact Finset.card_le_card (hE_sub0 C hC b)
  obtain ⟨ρ_r, hρ_r⟩ := orderedUpTo_rot_at hOrd hr hcsG
  have hC_val : (coreGraph tr.cs.G tr.cs.lsf).IsValid := by
    intro e he
    have hth := hI_r.hG_val e (Finset.mem_sdiff.mp he).1
    exact ⟨(root_mem_R (compLSF_RF_isRSF hI_r) hth.1).1,
      (root_mem_R (compLSF_RF_isRSF hI_r) hth.2).1⟩
  have hHb_sp : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (restartBucketBundle tr (ord r) C b).graph.IsValid ∧
      (restartBucketBundle tr (ord r) C b).graph.n ≤
        2 * (restartBucketBundle tr (ord r) C b).graph.m := by
    intro C hC b
    have hR := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
    have hEcore : (tr.bun (C, b)).edges ⊆ (coreGraph tr.cs.G tr.cs.lsf).E :=
      (hR.1 ρ_r hI_r.hG_val (compLSF_RF_isRSF hI_r) hρ_r).1
    dsimp only [restartBucketBundle]
    rw [hk_tr]
    have h2m := initBundleFor_n_le_two_m tr.cs (ord r) hEcore hk
    rw [initBundleFor_eq hI_r hρ_r]
    have hpart := initBundleState_inv
      (coreRotation (L := tr.cs.lsf) ρ_r hI_r.hG_val (compLSF_RF_isRSF hI_r))
      hC_val hEcore hk
    exact ⟨BundleState.graph_isValid hpart, by rw [← initBundleFor_eq hI_r hρ_r]; exact h2m⟩
  have h82 : ∀ C ∈ components (D.G 0), ∀ b ∈ actB C,
      let Hb := normGraph (restartBucketBundle tr (ord r) C b).graph
      let initB := DynSpanner.init Hb E.L (phaseBase (Hb.n + tr.splitBound) E.L) (sparsify tr.m₀)
      (initB.state.H.m : ℝ) ≤
        (E.P_fn M).K_s * (Hb.n : ℝ) * (E.P_fn M).γ_ℓ *
          (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ (E.P_fn M).p_s ∧
      (initB.cost : ℝ) ≤
        (E.P_fn M).K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * (E.P_fn M).γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ (E.P_fn M).p_t +
          (Hb.n : ℝ) + (Hb.m : ℝ) + (initB.state.H.m : ℝ) +
          (Hb.m : ℝ) * (E.P_fn M).γ_ℓ + (E.L : ℝ) + 1 := by
    intro C hC b hb' Hb initB
    have hm_b : Hb.m ≤ M := by
      calc Hb.m ≤ (actB C).sum (fun b' => (restartBucketBundle tr (ord r) C b').graph.m) :=
            Finset.single_le_sum (f := fun b' => (restartBucketBundle tr (ord r) C b').graph.m)
              (fun _ _ => Nat.zero_le _) hb'
        _ ≤ (components (D.G 0)).sum
              (fun C' => (actB C').sum fun b' => (restartBucketBundle tr (ord r) C' b').graph.m) :=
            Finset.single_le_sum
              (f := fun C' => (actB C').sum fun b' => (restartBucketBundle tr (ord r) C' b').graph.m)
              (fun _ _ => Nat.zero_le _) hC
        _ ≤ M := hm_sum
    have hSp : SparsifySpec M (E.P_fn M) (sparsify tr.m₀) := by rw [hm0_tr]; exact hHyps.hSp
    have hthm := DynSpanner.theorem_8_2 (Us := []) (splitBound := tr.splitBound)
      (normGraph_isValid (hHb_sp C hC b).1) E.hL hm_b hSp trivial (by simp) (by simp [batchSplitCount])
    exact ⟨hthm.1, hthm.2.1⟩
  have hbuck := bundleInitBuckets_cost_sum_le (L := E.L) (P_b := E.P_fn M) (m₀ := M) (G₀ := D.G 0)
    tr.activeComps hact actB (fun C b => normGraph (restartBucketBundle tr (ord r) C b).graph)
    (fun C b => DynSpanner.init (normGraph (restartBucketBundle tr (ord r) C b).graph) E.L
      (phaseBase ((normGraph (restartBucketBundle tr (ord r) C b).graph).n + tr.splitBound) E.L)
      (sparsify tr.m₀))
    (le_trans hcard0 hM) hm_sum (fun C hC b _ => (hHb_sp C hC b).2) h82
  have hbuck' : ((tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      (DynSpanner.init (normGraph (restartBucketBundle tr (ord r) C b).graph) E.L
        (phaseBase ((normGraph (restartBucketBundle tr (ord r) C b).graph).n + tr.splitBound) E.L)
        (sparsify tr.m₀)).cost : ℕ) : ℝ) ≤
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * bundleLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        bundleLambda (E.P_fn M) M) * (M : ℝ) := by
    rw [hAB]; push_cast; exact hbuck
  have hres := bundleRestartCost_le_params E M N tr.cs.G.m _ hN_pos hm_cur hbuck'
  exact ⟨hres.1, hres.2.1, hres.2.2 k⟩

/-- The cost part of item 3 of `SparseCoreRestartTool.IsSpecOrdRestart` for
`sparseCoreBundleRestartTool`: each restart adds at most
`c_T * (M + 1) * γ_r(M) * log^{p_T}(M + N + 2)` to the cost. -/
theorem bundleRestart_restartCost_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro T P pre r hr p j' hpref st'
  have hValP := bundleCoreParams_valid E
  have hγrM : 1 ≤ P.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hcT_nn : 0 ≤ P.c_T := hValP.2.2.2.2.2.2.2.2.2
  have hlogMN_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
  have hRHS_nn : 0 ≤ P.c_T * ((M : ℝ) + 1) * P.γ_r M *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T :=
    mul_nonneg (mul_nonneg (mul_nonneg hcT_nn (by positivity)) (by linarith))
      (pow_nonneg hlogMN_nn _)
  have hf_p := foldl_bundleRestart_props lsfInit E.C_lsst E.L sparsify (pre r) p
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
      ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
    have hj' : j' < k := hrest r hr j' (hpref.subset (by simp))
    have hne_pre : (pre r).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts r).1.trans
        (decide_eq_true hV₀)
    have hk_pre : (pre r).k = k :=
      (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts r).2.2.1
    have hord_pre : (pre r).ord = ord r :=
      ((runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts r).2.2.2.2 hV₀).1
    have hne_st' : st'.isNonempty = true := hf_p.1.trans hne_pre
    have hk_st' : st'.k = k := hf_p.2.1.trans hk_pre
    have hord_st' : st'.ord = ord r := hf_p.2.2.1.trans hord_pre
    have hrc_eq := bundleRestartTool_restart_cost_eq lsfInit E.C_lsst E.L sparsify st' j' hne_st'
      (hk_st'.symm ▸ hj')
    have hsc_eq : singleBundleRestartCost E.L sparsify (st'.trees j') st'.ord =
        singleBundleRestartCost E.L sparsify ((pre r).trees j') (ord r) := by
      rw [hord_st', ← hord_pre]
      exact foldl_bundleRestart_singleCost_eq lsfInit E.C_lsst E.L sparsify p (pre r) hne_pre j'
    have hsrc := singleBundleRestartCost_pre_le E lsfInit sparsify k M N τ D ord restarts
      hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps r j' hj' hr
    dsimp only at hsrc
    have hT_le : (singleBundleRestartCost E.L sparsify ((pre r).trees j') (ord r) : ℝ) ≤
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
      have hrb : 0 ≤ bundleRecBase E M :=
        le_trans (by linarith [bundleRecEnv_ge_four E M]) (le_max_left _ _)
      have hcm : 0 ≤ bundleCostMult E M := by linarith [bundleCostMult_ge_one E M]
      have hTbase_nn : 0 ≤ ((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1) := by positivity
      have hp_nn : 0 ≤ 12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by positivity
      have hEq : P.c_T * ((M : ℝ) + 1) * P.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T =
          P.c_T * (((M : ℝ) + 1) * (bundleRecBase E M * bundleCostMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
        dsimp only [P, bundleCoreParams]; ring
      linarith [hsrc.2.1, hEq]
    dsimp only at hrc_eq
    rw [hrc_eq, hsc_eq, Nat.cast_add]
    linarith
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit E.C_lsst E.L sparsify k M N D ord restarts hV₀
    have hst'_hem : st'.isNonempty = false := hf_p.1.trans (hrunE r).1
    have hres_eq : T.restart st' j' = st' := by
      change (if st'.isNonempty = true then _ else st') = st'
      simp only [hst'_hem, Bool.false_eq_true, ↓reduceIte]
    rw [hres_eq]
    linarith

/-- Items 1 to 6 of `SparseCoreRestartTool.IsSpecOrdRestart` for `sparseCoreBundleRestartToolWith`,
with item 3 in full. Item 7 (total cumulative cost) is proved in `BundleRestartFull.lean`. -/
theorem bundleRestart_spec_noTotalCost (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (post t) j) (T.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
      (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (T.coreCOrdFrom k M N D ord restarts c s₀ j)
          (T.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j)) := by
  intro T P pre U_S post
  have h := bundleRestart_spec_noCost E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hHyps
  have hc := bundleRestart_restartCost_le E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hWeak hOrd hM hN hrest hThresh hHyps
  refine ⟨h.1, h.2.1, fun r hr p j' hpref => ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have h3 := h.2.2.1 r hr p j' hpref
  exact ⟨h3.1, h3.2.1, h3.2.2, hc r hr p j' hpref⟩

end MinCostFlow.Chain

end
