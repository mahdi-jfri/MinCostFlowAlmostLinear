module

public import MinCostFlow.Chain.SparseCoreRestartSpec
public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.SparseCoreCostEnv
import MinCostFlow.SparseCore.SparseCoreCostEnvNoComp
import MinCostFlow.Chain.SparseCoreRestartEpoch
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SparseCoreMetrics
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cost of one restart of `sparseCoreRestartTool`

A restart of branch `j` re-initializes the Theorem 8.2 structure of every active bucket on the
current bucket graph, and rebuilds `S_cur`. This file bounds that work at `(M, N)` without
`hThresh₀`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- The work of one call of `restartTreeCore` on the branch state `tr`: reading the current graph,
and one Theorem 8.2 initialization per active bucket. -/
noncomputable def singleRestartCost (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (tr : TreeCoreState L) : ℕ :=
  tr.cs.G.m + 1 + tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
    (DynSpanner.init (restartBucketGraph tr C b) L
      (phaseBase ((restartBucketGraph tr C b).n + tr.splitBound) L) (sparsify tr.m₀)).cost

lemma restartTreeCore_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (tr : TreeCoreState L) :
    (restartTreeCore L sparsify tr).cost = tr.cost + singleRestartCost L sparsify tr :=
  rfl

/-- A restart of a branch `j < k` of a nonempty state adds exactly `singleRestartCost` to the
total cost. -/
lemma sRT_restart_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (j : ℕ) (hne : st.isNonempty = true) (hj : j < st.k) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    T.cost (T.restart st j) = T.cost st + singleRestartCost L sparsify (st.trees j) := by
  intro T
  have hmem : j ∈ Finset.range st.k := Finset.mem_range.mpr hj
  have hsum : ∀ f : ℕ → TreeCoreState L,
      ∑ x ∈ Finset.range st.k,
          (Function.update f j (restartTreeCore L sparsify (f j)) x).cost =
        ∑ x ∈ Finset.range st.k, (f x).cost + singleRestartCost L sparsify (f j) := by
    intro f
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ (fun x => (f x).cost) hmem,
      Function.update_self, restartTreeCore_cost]
    have hrest : ∑ x ∈ (Finset.range st.k).erase j,
        (Function.update f j (restartTreeCore L sparsify (f j)) x).cost =
        ∑ x ∈ (Finset.range st.k).erase j, (f x).cost :=
      Finset.sum_congr rfl fun x hx => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [hrest]
    omega
  change (if (T.restart st j).isNonempty = true then
      ∑ x ∈ Finset.range (T.restart st j).k, ((T.restart st j).trees x).cost else 0) =
    (if st.isNonempty = true then ∑ x ∈ Finset.range st.k, (st.trees x).cost else 0) + _
  have hR : T.restart st j =
      { st with trees := Function.update st.trees j (restartTreeCore L sparsify (st.trees j)) } := by
    change (if st.isNonempty then _ else st) = _
    simp only [hne, ↓reduceIte]
  rw [hR]
  simp only [hne, ↓reduceIte]
  exact hsum st.trees

/-- The work of one restart of branch `j` at a step `r ≤ τ`, on any branch state with the same
base fields as the unrestarted run at `(M, N)`, is at most `(4 + 3·7^p) T` with
`T = (M + 1) γ_r(M) log^{p+1}(M + N + 2)`, and adding the dynamic-update allowance
`12600·7^p T` stays below `c_T T`. -/
lemma singleRestartCost_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (r j : ℕ) (hr : r ≤ τ) (hj : j < k) (tr : TreeCoreState E.L)
    (hbase : TreeBaseFieldsEq tr (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j r).1) :
    let P := sparseCoreParams E
    let p_max := max E.p_s_hi E.p_t_hi
    let logMN := Real.log ((M : ℝ) + (N : ℝ) + 2)
    let T := ((M : ℝ) + 1) * (recBase E M * costMult E M) * logMN ^ (p_max + 1)
    (singleRestartCost E.L sparsify tr : ℝ) ≤ (4 + 3 * (7 : ℝ) ^ p_max) * T ∧
    (singleRestartCost E.L sparsify tr : ℝ) + 12600 * (7 : ℝ) ^ p_max * T ≤ P.c_T * T := by
  intro P p_max logMN T
  have hk1 : 1 ≤ k := hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
  have hb := hBase r hr
  set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j with hcs₀
  set actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
    (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e)) with hactB
  have hm0 : tr.m₀ = M := hbase.m₀.trans hb.1
  have hOB : tr.origBucket = fun e => bucketOf (coreLen cs₀.lsf (safeLen (D.G 0) (D.ℓ 0)) e) :=
    hbase.origBucket.trans hb.2.2.2.2.1
  have hAB : tr.activeBuckets = actB := hbase.activeBuckets.trans hb.2.2.2.2.2.1
  have hcsG : tr.cs.G = D.G r := by rw [hbase.cs]; exact hb.2.2.2.2.2.2.2.2.2.1
  have hact : tr.activeComps ⊆ components (D.G 0) := by
    rw [hbase.activeComps]; exact hb.2.2.2.2.2.2.2.2.2.2.1.2
  have hTI : ∀ C ∈ components (D.G 0),
      TildeInv (cs₀.compSt C) (tr.cs.compSt C) (tr.ts C) ∧
      (tr.ts C).C.E ⊆ (initTildeState (cs₀.compSt C)).C.E := fun C hC => by
    rw [hbase.cs, hbase.ts]
    exact ⟨(hb.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.1, (hb.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1⟩
  -- The current graph has at most `2 M` edges, since `(D.G 0).m ≤ M` and at most `M` updates arrive.
  have hm_cur : tr.cs.G.m ≤ 2 * M := by
    rw [hcsG]
    have h1 := dyn_G_m_le hD r hr
    have h2 := (updateThreshold_le_div_k_at hk hN_pos hThresh r hr).2
    omega
  -- The bucket graphs of the restart have at most `M` edges in total.
  obtain ⟨hcard0, hm0_sum, _⟩ := all_buckets_sum_le oracle hHyps.hLSST hk1 hG₀ hV₀ hℓ₀ j
  have hm_sum : (components (D.G 0)).sum
      (fun C => (actB C).sum fun b => (restartBucketGraph tr C b).m) ≤ M := by
    refine le_trans (le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) hm0_sum) hM
    have hE_sub : (restartBucketGraph tr C b).E ⊆ (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).E := by
      intro e he
      have hts_sub := (hTI C hC).2
      change e ∈ (tr.ts C).C.E.filter (fun e => tr.origBucket e = b) at he
      rw [hOB, Finset.mem_filter] at he
      beta_reduce at he
      change e ∈ (initTildeState (cs₀.compSt C)).C.E.filter
        (fun e => bucketOf (coreLen (cs₀.compSt C).lsf (D.ℓ 0) e) = b)
      rw [Finset.mem_filter]
      refine ⟨hts_sub he.1, ?_⟩
      rw [← initCompLSF_origBucket_congr oracle hHyps.hLSST hG₀ hV₀ hℓ₀ hk1 j hC e (hts_sub he.1),
        ← initCompLSF_safeLen_origBucket_eq oracle E.C_lsst hk1 hG₀ hV₀ hℓ₀ hC hHyps.hLSST
          (hts_sub he.1)]
      exact he.2
    exact Finset.card_le_card hE_sub
  have hHb_sp : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (restartBucketGraph tr C b).IsValid ∧ (restartBucketGraph tr C b).n ≤
        2 * (restartBucketGraph tr C b).m := fun C hC b => by
    have h := activeSubgraph_rawBucket_spec (hTI C hC).1.hC_val tr.origBucket b
    exact ⟨h.1, h.2.2.2.1⟩
  -- Theorem 8.2 with no batch bounds the size and the cost of each initialization.
  have h82 : ∀ C ∈ components (D.G 0), ∀ b ∈ actB C,
      let Hb := restartBucketGraph tr C b
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
      calc Hb.m ≤ (actB C).sum (fun b' => (restartBucketGraph tr C b').m) :=
            Finset.single_le_sum (f := fun b' => (restartBucketGraph tr C b').m)
              (fun _ _ => Nat.zero_le _) hb'
        _ ≤ (components (D.G 0)).sum
              (fun C' => (actB C').sum fun b' => (restartBucketGraph tr C' b').m) :=
            Finset.single_le_sum
              (f := fun C' => (actB C').sum fun b' => (restartBucketGraph tr C' b').m)
              (fun _ _ => Nat.zero_le _) hC
        _ ≤ M := hm_sum
    have hSp : SparsifySpec M (E.P_fn M) (sparsify tr.m₀) := by
      rw [hm0]; exact hHyps.hSp
    have hthm := DynSpanner.theorem_8_2 (Us := []) (splitBound := tr.splitBound)
      (hHb_sp C hC b).1 E.hL hm_b hSp trivial (by simp) (by simp [batchSplitCount])
    exact ⟨hthm.1, hthm.2.1⟩
  have hbuck := initBuckets_cost_sum_le (L := E.L) (P_b := E.P_fn M) (m₀ := M) (G₀ := D.G 0)
    tr.activeComps hact actB (fun C b => restartBucketGraph tr C b)
    (fun C b => DynSpanner.init (restartBucketGraph tr C b) E.L
      (phaseBase ((restartBucketGraph tr C b).n + tr.splitBound) E.L) (sparsify tr.m₀))
    (le_trans hcard0 hM) hm_sum (fun C hC b _ => (hHb_sp C hC b).2) h82
  have hbuck' : ((tr.activeComps.sum fun C => (tr.activeBuckets C).sum fun b =>
      (DynSpanner.init (restartBucketGraph tr C b) E.L
        (phaseBase ((restartBucketGraph tr C b).n + tr.splitBound) E.L)
        (sparsify tr.m₀)).cost : ℕ) : ℝ) ≤
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * coreLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        coreLambda (E.P_fn M) M) * (M : ℝ) := by
    rw [hAB]; push_cast; exact hbuck
  exact restartCost_le_params_noComp E M N (D.G 0).maxDeg tr.cs.G.m _ hN_pos hm_cur
    (by exact_mod_cast hHyps.hDeg_bound.1) hbuck'

/-- The cost part of item 3 of `SparseCoreRestartTool.IsSpecRestart` for `sparseCoreRestartTool`:
each restart adds at most `c_T (M + 1) γ_r(M) log^{p_T}(M + N + 2)` to the cost. -/
theorem sparseCoreRestart_restartCost_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro T P pre r hr p j' hpref st'
  have hValP := sparseCoreParams_valid E
  have hγrM : 1 ≤ P.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hcT_nn : 0 ≤ P.c_T := hValP.2.2.2.2.2.2.2.2.2
  have hlogMN_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
  have hRHS_nn : 0 ≤ P.c_T * ((M : ℝ) + 1) * P.γ_r M *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T :=
    mul_nonneg (mul_nonneg (mul_nonneg hcT_nn (by positivity)) (by linarith))
      (pow_nonneg hlogMN_nn _)
  have hf_p := foldl_restart_props oracle E.C_lsst E.L sparsify (pre r) p
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
      ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
    have hj' : j' < k := hrest r hr j' (hpref.subset (by simp))
    have hne_pre : (pre r).isNonempty = true :=
      (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts r).1.trans
        (decide_eq_true hV₀)
    have hk_pre : (pre r).k = k :=
      (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts r).2.2.1
    have hne_st' : st'.isNonempty = true := hf_p.1.trans hne_pre
    have hk_st' : st'.k = k := hf_p.2.1.trans hk_pre
    have hBase_pre :=
      (runAfterRestarts_base_proj oracle E.C_lsst E.L sparsify k M N D restarts hV₀ j' r).1
    have hBase_st' : TreeBaseFieldsEq (st'.trees j')
        (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j' r).1 :=
      (hf_p.2.2.2.1 j').trans hBase_pre
    have hrc_eq := sRT_restart_cost_eq oracle E.C_lsst E.L sparsify st' j' hne_st'
      (hk_st'.symm ▸ hj')
    have hsrc := singleRestartCost_le_noComp E oracle sparsify k M N τ D hk hG₀ hV₀ hℓ₀ hD
      hM hN hThresh hHyps r j' hr hj' (st'.trees j') hBase_st'
    dsimp only at hsrc
    have hT_le : (singleRestartCost E.L sparsify (st'.trees j') : ℝ) ≤
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
      have hrb_ge : recEnv E M ≤ recBase E M := le_max_left _ _
      have hrb : 0 ≤ recBase E M := by linarith [recEnv_ge_four E M]
      have hcm : 0 ≤ costMult E M := by linarith [costMult_ge_one E M]
      have hTbase_nn : 0 ≤ ((M : ℝ) + 1) * (recBase E M * costMult E M) *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1) := by positivity
      have hp_nn : 0 ≤ 12600 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi *
          (((M : ℝ) + 1) * (recBase E M * costMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by positivity
      have hEq : P.c_T * ((M : ℝ) + 1) * P.γ_r M *
          (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T =
          P.c_T * (((M : ℝ) + 1) * (recBase E M * costMult E M) *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ (max E.p_s_hi E.p_t_hi + 1)) := by
        dsimp only [P, sparseCoreParams]; ring
      linarith [hsrc.2, hEq]
    dsimp only at hrc_eq
    rw [hrc_eq, Nat.cast_add]
    linarith
  · have hrunE := runAfterRestarts_empty_case oracle E.C_lsst E.L sparsify k M N D restarts hV₀
    have hst'_hem : st'.isNonempty = false := hf_p.1.trans (hrunE r).1
    have hres_eq : T.restart st' j' = st' := by
      change (if st'.isNonempty then _ else st') = st'
      simp only [hst'_hem, Bool.false_eq_true, ↓reduceIte]
    rw [hres_eq]
    linarith

/-- Items 1 to 5 of `SparseCoreRestartTool.IsSpecRestart` for `sparseCoreRestartTool`, with item 3
in full. Only item 6, the bound on the total cost, is left out. -/
theorem sparseCoreRestart_spec_noTotalCost_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
    let post := fun t => T.runAfterRestarts k M N D restarts t
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
      (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
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
        WeakHiddenStable (T.coreInstanceFrom k M N D restarts s₀ j) (t - s₀) Ψ'
          (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j)) := by
  intro T P pre U_S post
  have h := sparseCoreRestart_spec_noCost_noComp E oracle sparsify k τ M N D restarts Ψ c w
    hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps
  have hc := sparseCoreRestart_restartCost_le_noComp E oracle sparsify k τ M N D restarts Ψ c w
    hk hG₀ hD hWeak hM hN hrest hThresh hHyps
  refine ⟨h.1, h.2.1, fun r hr p j' hpref => ?_, h.2.2.2.1, h.2.2.2.2⟩
  have h3 := h.2.2.1 r hr p j' hpref
  exact ⟨h3.1, h3.2.1, h3.2.2, hc r hr p j' hpref⟩

end MinCostFlow.Chain

end
