module

public import MinCostFlow.Chain.SparseCoreRestartEpochCost
import MinCostFlow.Chain.SparseCoreRestartAux
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreEpochCost
import MinCostFlow.SparseCore.SparseCoreCostEnvNoComp
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SparseCoreBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The total cost of one branch of `sparseCoreRestartTool`

Bounds the cost of branch `j` after step `τ` of a run with restarts at `(M, N)` without
`hComp_bound` or `hThresh₀` (`branch_cost_restart_le_noComp`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- Active-vertex initialization, lazy initialization and component-batch parts of the cost of
`treeRunSeq` at `(M, N)` (without `hComp_bound` or `hThresh₀`). -/
theorem treeRunSeq_init_uc_le_active
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (_hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound) :
    let m₀ := (D.G 0).m
    let n_eff := min N (M + 1)
    let Δ₀ := (D.G 0).maxDeg
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda P_b M
    let ucBound := 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ)
    ((m₀ : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) ∧
    (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
        fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).U_C C).length : ℝ)) ≤ ucBound := by
  classical
  intro m₀ n_eff Δ₀ q_τ Λ ucBound
  set cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
  set ts₀ := fun C => initTildeState (cs₀.compSt C)
  let actB : Finset ℕ → Finset ℤ := fun C =>
    (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components (D.G 0),
      (cs₀.compSt C).G = compGraph (D.G 0) C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hCov₀ : ∀ C ∈ components (D.G 0),
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2
  have hHb : ∀ C ∈ components (D.G 0), ∀ b : ℤ, _ := fun C hC b =>
    initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, _, hT82_cum⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  obtain ⟨hAct_card_sum, hm_sum, _⟩ := all_buckets_sum_le oracle hLSST hk hG₀ hV₀ hℓ₀ j
  have hInit_sum :
      ((m₀ : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) := by
    have hlazy0 : (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost =
        fun C => (actB C).sum fun b =>
          (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
            (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
              (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
                Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L) (sparsify M)).cost :=
      (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.1
    rw [hlazy0]
    push_cast
    have hsum := initBuckets_cost_sum_le (L := L) (P_b := P_b) (m₀ := M) (G₀ := D.G 0)
      (treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps
      (hStage_all τ le_rfl).2.2.2.2.1 actB
      (fun C b => initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
      (fun C b => DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
        (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
          (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
            Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L) (sparsify M))
      (le_trans hAct_card_sum hM) (le_trans hm_sum hM)
      (fun C hC b _ => (hHb C hC b).2.2.2.2.1)
      (fun C hC b _ => ⟨(hT82_cum C hC b τ le_rfl).1, (hT82_cum C hC b τ le_rfl).2.1⟩)
    have hm₀M : (m₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith [hsum, hm₀M]
  have hUC_sum :
      (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
        fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).U_C C).length : ℝ)) ≤ ucBound := by
    have h1 :
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℝ))) ≤
        ∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C =>
          (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℝ) := by
      refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun _ _ _ => Nat.cast_nonneg _)
      exact (hStage_all (s + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hs))).2.2.2.2.1
    have h2 := epoch_U_C_sum_le_min oracle C_lsst L sparsify hLSST k M N τ hk D
      hG₀ hV₀ hℓ₀ hD hN hThresh j 0 τ (by omega)
      (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).1)
      (fun r _ => by rw [Nat.zero_add]) (fun r _ => by rw [Nat.zero_add])
    dsimp only at h2
    have hIcc : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
    have huc_mono : coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) Δ₀ ≤ coreUCRatio n_eff Δ₀ :=
      coreUCRatio_mono (min_le_min hN (Nat.add_le_add_right hM 1)) Δ₀
    calc _ ≤ (components (D.G 0)).sum (fun C => ∑ r ∈ Finset.range τ,
              (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                (D.U (r + 1))).U_C C).length : ℝ)) := by
            rw [← Finset.sum_comm]; exact h1
      _ = (components (D.G 0)).sum (fun C => ∑ r ∈ Finset.range τ,
              (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                (D.U (0 + r + 1))).U_C C).length : ℝ)) :=
            Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]
      _ ≤ 2 * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) Δ₀ *
            ((∑ s ∈ Finset.Icc (0 + 1) (0 + τ), (D.U s).length : ℕ) : ℝ) := h2
      _ ≤ ucBound := by
            rw [hIcc]
            exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  exact ⟨hInit_sum, hUC_sum⟩

/-- The cost of branch `j` after step `τ`, split into its parts: the initialization and lazy
initializations, the input batches, the component batches (these three as in `treeRunSeq`), the
batch sizes and Theorem 8.2 work of the run with restarts, and the restart work. -/
lemma branch_cost_decomp
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let post := fun t => T.runAfterRestarts k M N D restarts t
    let base := fun t => (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
    let infoR := fun s => stepTreeCoreAux sparsify ((post s).trees j) (D.U (s + 1))
    ((post τ).trees j).cost =
      (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
        ((base τ).activeComps.sum (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost) +
        ∑ s ∈ Finset.range τ, (D.U (s + 1)).length +
        ∑ s ∈ Finset.range τ, ((base (s + 1)).activeComps.sum fun C =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_C C).length) +
        ∑ s ∈ Finset.range τ, ((infoR s).U_S.length +
          ((infoR s).state.activeComps.sum fun C =>
            (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost)) +
        ∑ r ∈ Finset.range (τ + 1),
          (restarts r).count j * singleRestartCost L sparsify (base r) := by
  intro T post base infoR
  have hEq := branch_cost_eq oracle C_lsst L sparsify k M N D restarts hV₀ j τ
  have hCE := treeRunSeq_cost_eq oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hN hThresh j τ le_rfl
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j
  have hdyn : ∀ s ∈ Finset.range τ,
      ((base (s + 1)).activeComps.sum fun C =>
        ((initTildeState ((initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j).compSt C)).C.E.image
          (fun e => bucketOf (coreLen (initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j).lsf
            (D.ℓ 0) e))).sum fun b =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost) =
      ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).state.activeComps.sum fun C =>
        ((base s).activeBuckets C).sum fun b =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost) := by
    intro s hs
    have hAB := (hBase s (by have := Finset.mem_range.mp hs; omega)).2.2.2.2.2.1
    change _ = ((base (s + 1)).activeComps.sum fun C =>
        ((base s).activeBuckets C).sum fun b =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost)
    rw [hAB]
  have hsumO : ∑ s ∈ Finset.range τ,
      ((D.U (s + 1)).length +
        ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
          ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length) +
        (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2.length +
        ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
          ((initTildeState ((initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j).compSt C)).C.E.image
            (fun e => bucketOf (coreLen (initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j).lsf
              (D.ℓ 0) e))).sum fun b =>
            ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
              (D.U (s + 1))).stepOut (C, b)).cost)) =
      ∑ s ∈ Finset.range τ, (D.U (s + 1)).length +
        ∑ s ∈ Finset.range τ, ((base (s + 1)).activeComps.sum fun C =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_C C).length) +
        ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_S.length +
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).state.activeComps.sum fun C =>
            ((base s).activeBuckets C).sum fun b =>
              ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have h := hdyn s hs
    change _ = _ + _ + ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_S.length + _)
    change (D.U (s + 1)).length + _ + (stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_S.length +
      _ = _
    rw [h]
    ring
  rw [hsumO] at hCE
  have hEq' : ((post τ).trees j).cost +
      ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_S.length +
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).state.activeComps.sum fun C =>
            ((base s).activeBuckets C).sum fun b =>
              ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost)) =
      (base τ).cost +
        ∑ s ∈ Finset.range τ, ((infoR s).U_S.length +
          ((infoR s).state.activeComps.sum fun C =>
            (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost)) +
        ∑ r ∈ Finset.range (τ + 1),
          (restarts r).count j * singleRestartCost L sparsify (base r) := hEq
  have hCE' : (base τ).cost = (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
      ((base τ).activeComps.sum (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost) +
      (∑ s ∈ Finset.range τ, (D.U (s + 1)).length +
        ∑ s ∈ Finset.range τ, ((base (s + 1)).activeComps.sum fun C =>
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_C C).length) +
        ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).U_S.length +
          ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).state.activeComps.sum fun C =>
            ((base s).activeBuckets C).sum fun b =>
              ((stepTreeCoreAux sparsify (base s) (D.U (s + 1))).stepOut (C, b)).cost))) := hCE
  omega

/-- The cost of branch `j` after the last step `τ` of a run with restarts at `(M, N)` (without
`hComp_bound` or `hThresh₀`). -/
theorem branch_cost_restart_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) (j : ℕ) (hj : j < k) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    (((T.runAfterRestarts k M N D restarts τ).trees j).cost : ℝ) ≤
      (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        (P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  intro T P
  have hk1 : 1 ≤ k := hk
  have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
  have hqτ_le_M : (Finset.Icc 1 τ).sum (fun s => (D.U s).length) ≤ M :=
    (updateThreshold_le_div_k_at hk hN_pos hThresh τ le_rfl).2
  have hne : ∀ s, (T.runAfterRestarts k M N D restarts s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  set p_max := max E.p_s_hi E.p_t_hi with hp_max
  set logMN := Real.log ((M : ℝ) + (N : ℝ) + 2) with hlogMN
  set γ' := recBase E M * costMult E M with hγ'
  set T_b := ((M : ℝ) + 1) * γ' * logMN ^ (p_max + 1) with hT_b
  set q_τ := (Finset.Icc 1 τ).sum fun s => (D.U s).length with hq_τ
  set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
  set dC := (components (D.G 0)).sup fun C => (initTildeState (cs₀.compSt C)).C.maxDeg
  set n_eff := min N (M + 1) with hn_eff
  set n_act := (activeSubgraph (D.G 0)).n with hn_act
  obtain ⟨hbase, _, hfin, hTb_nn, hγ'_nn, hlogMN_ge1⟩ := cost_env_baseline_parts_noComp E M N
    n_act (D.G 0).maxDeg dC q_τ hN_pos
    (le_trans (activeSubgraph_n_le_two_m hG₀) (Nat.mul_le_mul_left 2 hM)) hqτ_le_M
    (le_trans (maxDeg_le_two_m (D.G 0)) (Nat.mul_le_mul_left 2 hM))
    (by exact_mod_cast hHyps.hDeg_bound.1)
    (by exact_mod_cast hHyps.hDeg_bound.2 j hj)
  have hG_eq : P.c_T * ((M : ℝ) + 1) * P.γ_r M * logMN ^ P.p_T = P.c_T * T_b := by
    simp only [hT_b, hγ', P, sparseCoreParams, hp_max]; ring
  rw [hG_eq]
  have hG_fin : ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max + 37800 * (7 : ℝ) ^ p_max) * T_b ≤
      P.c_T * T_b := by
    have h := hfin; rw [hG_eq] at h; exact h
  have h7_ge1 : (1 : ℝ) ≤ (7 : ℝ) ^ p_max := one_le_pow₀ (by norm_num)
  have hcT_rest : (4 + 3 * (7 : ℝ) ^ p_max) + 12600 * (7 : ℝ) ^ p_max ≤ P.c_T := by
    simp only [P, sparseCoreParams, hp_max]
    linarith only [h7_ge1, E.hc_n]
  have hlog_nn : 0 ≤ logMN := by linarith
  have hdec := branch_cost_decomp oracle E.C_lsst E.L sparsify hHyps.hLSST k M N τ hk1 D restarts
    hG₀ hV₀ hℓ₀ hD hN hThresh j
  dsimp only at hdec
  obtain ⟨hInit, hUC⟩ := treeRunSeq_init_uc_le_active oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify
    hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps.hSp j hj (E.B_fn M) (hHyps.hB_bound j hj)
  have hDU : ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) = (q_τ : ℝ) := by
    rw [Nat.cast_sum, sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ, hq_τ,
      Nat.cast_sum]
  have hUS_eq : ∀ s, (stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
      (D.U (s + 1))).U_S = (T.runAfterUpdate k M N D restarts (s + 1)).2 j := fun s => by
    rw [T.runAfterUpdate_succ]
    dsimp only [T]
    rw [sRT_update_of_nonempty (hne s)]
  have hUS_part := epoch_partition_sum_le restarts j τ
    (fun s => (((T.runAfterUpdate k M N D restarts s).2 j).length : ℝ))
    (fun s => ((D.U s).length : ℝ)) 0
    (coreRecoursePerQ E.L (E.P_fn M) M n_eff (D.G 0).maxDeg (E.B_fn M)) le_rfl
    (fun s₀ t hst htτ hs₀ hNoRest => by
      rw [zero_add]
      exact epoch_US_restart_le_noComp E oracle sparsify k M N τ D restarts hk hG₀ hV₀ hℓ₀ hD hM hN
        hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest) τ le_rfl
  have hUS_sum : ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify
      ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1))).U_S.length : ℝ) ≤
      coreRecoursePerQ E.L (E.P_fn M) M n_eff (D.G 0).maxDeg (E.B_fn M) * (q_τ : ℝ) := by
    have h1 : ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify
        ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1))).U_S.length : ℝ) =
        ∑ s ∈ Finset.Icc 1 τ, (((T.runAfterUpdate k M N D restarts s).2 j).length : ℝ) := by
      rw [← sum_range_eq_sum_Icc_succ (fun s => (((T.runAfterUpdate k M N D restarts s).2 j).length : ℝ))]
      exact Finset.sum_congr rfl fun s _ => by rw [hUS_eq s]
    rw [h1]
    have hq : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) = (q_τ : ℝ) := by
      rw [hq_τ, Nat.cast_sum]
    rw [hq, mul_zero, zero_add] at hUS_part
    exact hUS_part
  set dynF : ℕ → ℝ := fun s =>
    ((((stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts (s - 1)).trees j)
        (D.U (s - 1 + 1))).state.activeComps.sum fun C =>
      (((T.runAfterRestarts k M N D restarts (s - 1)).trees j).activeBuckets C).sum fun b =>
        ((stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts (s - 1)).trees j)
          (D.U (s - 1 + 1))).stepOut (C, b)).cost : ℕ) : ℝ)) with hdynF
  have hB_nn : 0 ≤ 25200 * (7 : ℝ) ^ p_max * (γ' * logMN ^ (p_max + 1)) := by positivity
  have hA_nn : 0 ≤ 12600 * (7 : ℝ) ^ p_max * T_b := by positivity
  have hDyn_part := epoch_partition_sum_le restarts j τ dynF (fun s => ((D.U s).length : ℝ))
    (12600 * (7 : ℝ) ^ p_max * T_b) (25200 * (7 : ℝ) ^ p_max * (γ' * logMN ^ (p_max + 1)))
    hA_nn
    (fun s₀ t hst htτ hs₀ hNoRest => epoch_dyn_cost_restart_le_T_noComp E oracle sparsify k M N τ D
      restarts hk hG₀ hV₀ hℓ₀ hD hM hN hThresh hHyps s₀ t j hj hst htτ hs₀ hNoRest) τ le_rfl
  have hDyn_eq : ∑ s ∈ Finset.range τ, (((stepTreeCoreAux sparsify
      ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1))).state.activeComps.sum fun C =>
        (((T.runAfterRestarts k M N D restarts s).trees j).activeBuckets C).sum fun b =>
          ((stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
            (D.U (s + 1))).stepOut (C, b)).cost : ℕ) : ℝ) =
      ∑ s ∈ Finset.Icc 1 τ, dynF s := by
    rw [← sum_range_eq_sum_Icc_succ dynF]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hdynF, Nat.add_sub_cancel]
  have hRest : ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
      singleRestartCost E.L sparsify (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j r).1 : ℕ) : ℝ) ≤
      (∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) *
        ((4 + 3 * (7 : ℝ) ^ p_max) * T_b) := by
    rw [Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hrc := singleRestartCost_le_noComp E oracle sparsify k M N τ D hk hG₀ hV₀ hℓ₀ hD hM hN
      hThresh hHyps r j hr_le hj (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j r).1
      (TreeBaseFieldsEq.refl _)
    dsimp only at hrc
    push_cast
    exact mul_le_mul_of_nonneg_left hrc.1 (Nat.cast_nonneg _)
  have hCount : ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0) ≤
      ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun r _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (f := fun r => ((restarts r).count j : ℝ))
        (fun x hx => by simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢; omega)
        (fun _ _ _ => Nat.cast_nonneg _))
    split_ifs with hmem
    · exact_mod_cast List.count_pos_iff.mpr hmem
    · exact Nat.cast_nonneg _
  have hq_m1 : (q_τ : ℝ) ≤ (M : ℝ) + 1 := by
    have : (q_τ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqτ_le_M
    linarith
  have hBq : 25200 * (7 : ℝ) ^ p_max * (γ' * logMN ^ (p_max + 1)) * (q_τ : ℝ) ≤
      25200 * (7 : ℝ) ^ p_max * T_b := by
    have h1 := mul_le_mul_of_nonneg_left hq_m1 hB_nn
    have h2 : 25200 * (7 : ℝ) ^ p_max * (γ' * logMN ^ (p_max + 1)) * ((M : ℝ) + 1) =
        25200 * (7 : ℝ) ^ p_max * T_b := by rw [hT_b]; ring
    linarith
  have hq_eq : ∑ s ∈ Finset.Icc 1 τ, ((D.U s).length : ℝ) = (q_τ : ℝ) := by
    rw [hq_τ, Nat.cast_sum]
  rw [hq_eq] at hDyn_part
  set Rc := ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) with hRc
  set Nc := ∑ r ∈ Finset.Icc 1 (τ - 1), (if j ∈ restarts r then (1 : ℝ) else 0)
  have hRc_nn : 0 ≤ Rc := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hNA := mul_le_mul_of_nonneg_right hCount hA_nn
  have hRest_tot : Rc * ((4 + 3 * (7 : ℝ) ^ p_max + 12600 * (7 : ℝ) ^ p_max) * T_b) ≤
      Rc * (P.c_T * T_b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcT_rest hTb_nn) hRc_nn
  have hrec_nn : 0 ≤ coreRecoursePerQ E.L (E.P_fn M) M n_eff (D.G 0).maxDeg (E.B_fn M) *
      (q_τ : ℝ) :=
    le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hUS_sum
  have hbase' : (M : ℝ) + (n_act : ℝ) + 1 +
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * coreLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        coreLambda (E.P_fn M) M) * (M : ℝ) +
      (q_τ : ℝ) + 2 * coreUCRatio n_eff (D.G 0).maxDeg * (q_τ : ℝ) +
      coreRecoursePerQ E.L (E.P_fn M) M n_eff (D.G 0).maxDeg (E.B_fn M) * (q_τ : ℝ) ≤
      ((7 + E.c_n) + 3 * (7 : ℝ) ^ p_max) * T_b := hbase
  have hInit' : ((D.G 0).m : ℝ) + (n_act : ℝ) + 1 +
      (((treeRunSeq oracle E.C_lsst E.L sparsify k M N D j τ).1.activeComps.sum
        (initTreeCore oracle E.C_lsst E.L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) ≤
      (M : ℝ) + (n_act : ℝ) + 1 +
      ((E.L : ℝ) + 1 + (E.P_fn M).K_t * (2 + (E.P_fn M).γ_ℓ ^ 2) * coreLambda (E.P_fn M) M +
        3 + (E.P_fn M).γ_ℓ + 2 * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        coreLambda (E.P_fn M) M) * (M : ℝ) := hInit
  have hUC' : ∑ s ∈ Finset.range τ,
      ((((treeRunSeq oracle E.C_lsst E.L sparsify k M N D j (s + 1)).1.activeComps.sum
        fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j s).1
          (D.U (s + 1))).U_C C).length : ℕ) : ℝ)) ≤
      2 * coreUCRatio n_eff (D.G 0).maxDeg * (q_τ : ℝ) := by
    have h := hUC
    rw [hq_τ]
    push_cast at h ⊢
    exact h
  have hDyn_part' : ∑ s ∈ Finset.Icc 1 τ, dynF s ≤
      (1 + Nc) * (12600 * (7 : ℝ) ^ p_max * T_b) +
        25200 * (7 : ℝ) ^ p_max * (γ' * logMN ^ (p_max + 1)) * (q_τ : ℝ) := hDyn_part
  have hcostR : (((T.runAfterRestarts k M N D restarts τ).trees j).cost : ℝ) =
      ((D.G 0).m : ℝ) + (n_act : ℝ) + 1 +
        (((treeRunSeq oracle E.C_lsst E.L sparsify k M N D j τ).1.activeComps.sum
          (initTreeCore oracle E.C_lsst E.L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) +
        ((∑ s ∈ Finset.range τ, (D.U (s + 1)).length : ℕ) : ℝ) +
        (∑ s ∈ Finset.range τ, (((treeRunSeq oracle E.C_lsst E.L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℕ) : ℝ)) +
        ∑ s ∈ Finset.range τ, ((stepTreeCoreAux sparsify
          ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1))).U_S.length : ℝ) +
        ∑ s ∈ Finset.range τ, (((stepTreeCoreAux sparsify
          ((T.runAfterRestarts k M N D restarts s).trees j) (D.U (s + 1))).state.activeComps.sum fun C =>
            (((T.runAfterRestarts k M N D restarts s).trees j).activeBuckets C).sum fun b =>
              ((stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
                (D.U (s + 1))).stepOut (C, b)).cost : ℕ) : ℝ) +
        ((∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
          singleRestartCost E.L sparsify (treeRunSeq oracle E.C_lsst E.L sparsify k M N D j r).1 : ℕ) : ℝ) := by
    rw [hdec]
    push_cast
    rw [Finset.sum_add_distrib]
    ring
  rw [hcostR, hDU, hDyn_eq]
  linarith only [hInit', hUC', hUS_sum, hDyn_part', hRest, hbase', hG_fin, hNA, hRest_tot, hBq,
    hrec_nn]

end MinCostFlow.Chain

end
