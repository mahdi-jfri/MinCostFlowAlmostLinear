module

public import MinCostFlow.SparseCore.ReembFactsCostBase

import MinCostFlow.Chain.BundleRestartCost
import MinCostFlow.SparseCore.BundleEpochCost

/-!
# Model cost at most machine cost on reached states of the sparse core (`ReembFactsCost`)

Proves `sparseCoreOrdInput_cost_le_machCost`: on every state `s` reached under
`SparseCoreOrdInput` for `sparseCoreBundleRestartToolMachWith` (with `0 < k`, `1 ≤ L`,
`1 ≤ spanConst`, and `SparsifySpec M (params M) (sparsify M)`), every branch `j` satisfying
`IsValidLSFInitFor lsfInit C_lsst k j` satisfies `(s.trees j).cost ≤ (s.trees j).machCost`.

For a nonempty initial graph, compares `bundle_branch_cost_decomp` against
`bundleWith_branch_machCost_eq` term by term using `dynSpanner_init_cost_le_spanInitBound`,
`DynSpanner.length_le_batchEnc`, and `run_dyn_cost_le_charge`. For an empty initial graph, the
state stays at initialization where `cost = 1 ≤ 2 ≤ machCost`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.LSF
open MinCostFlow.SparseCore.Program

private lemma runOrdAfterRestartsMachWith_of_empty
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hEmpty : ¬ (D.G 0).V.Nonempty) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    ∀ t, Tm.runOrdAfterRestarts k M N D ord restarts t =
      Tm.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0) := by
  intro Tm
  have hne0 : (Tm.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0)).isNonempty = false := by
    change decide (D.G 0).V.Nonempty = false
    exact decide_eq_false hEmpty
  have hfold : ∀ (xs : List ℕ) (st : SparseCoreBundleState L), st.isNonempty = false →
      xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st = st := by
    intro xs
    induction xs with
    | nil => intro _ _; rfl
    | cons x xs ih =>
      intro st hf
      have hr : (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st x = st := by
        rw [sparseCoreBundleRestartTool_restart_eq]
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        rfl
      dsimp only [List.foldl]
      rw [hr]
      exact ih st hf
  intro t
  induction t with
  | zero =>
    rw [SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate]
    exact hfold (restarts 0) _ hne0
  | succ s ih =>
    rw [SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate_succ, ih]
    have hu : (Tm.updateOrd (Tm.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0))
        (D.U (s + 1)) (D.ℓ (s + 1)) (D.g (s + 1)) (ord (s + 1))).1 =
        Tm.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0) := by
      dsimp only [Tm]
      rw [asm_updateOrd_of_empty _ _ _ _ _ _ _ hne0]
    rw [hu]
    exact hfold (restarts (s + 1)) _ hne0

/-- **Model cost is at most machine cost on every reached state.** For every state `s` reached under
`SparseCoreOrdInput` for `sparseCoreBundleRestartToolMachWith` (with `0 < k`, `1 ≤ L`,
`1 ≤ spanConst`, and `SparsifySpec M (params M) (sparsify M)`), every branch `j` satisfying
`IsValidLSFInitFor lsfInit C_lsst k j` satisfies `(s.trees j).cost ≤ (s.trees j).machCost`. -/
theorem sparseCoreOrdInput_cost_le_machCost
    {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hL : 1 ≤ L) (hConst : 1 ≤ spanConst)
    (hSp : SparsifySpec M (params M) (sparsify M))
    (hinp : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    (SparseCoreBundleState.trees (L := L) s j).cost ≤
      (SparseCoreBundleState.trees (L := L) s j).machCost := by
  classical
  let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
  let Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  obtain ⟨τ, D, ordSeq, restarts, hG₀, hM, hN, hℓ₀, hD, hOrd, _, _, hsum, hThr, hrun⟩ :=
    sparseCoreOrdInput_exists_run Tm hinp
  have hlog_ge1 : 1 ≤ bundleLogFactor M N := by
    unfold bundleLogFactor
    have h1 : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.le_add_left 1 _
    exact Nat.one_le_pow 2 _ h1
  by_cases hV₀ : (D.G 0).V.Nonempty
  · set post_m := fun t => Tm.runOrdAfterRestarts k M N D ordSeq restarts t
    set pre_b := fun t => (Tb.runOrdAfterUpdate k M N D ordSeq restarts t).1
    set post_b := fun t => Tb.runOrdAfterRestarts k M N D ordSeq restarts t
    set st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ordSeq 0) j
    set base := fun t => (bundleRunSeqWith lsfInit L sparsify k M N D ordSeq j t).1
    set infoB := fun r =>
      stepBundleTree sparsify ((post_b r).trees j) (D.U (r + 1)) (ordSeq r) (ordSeq (r + 1))
    have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
      sparsify params spanConst k M N D ordSeq restarts τ).2.2
    have hcost_eq : (SparseCoreBundleState.trees (L := L) s j).cost = ((post_b τ).trees j).cost := by
      rw [← hrun]; exact (hNM.trees j).cost
    have hmach_eq : (SparseCoreBundleState.trees (L := L) s j).machCost =
        ((post_m τ).trees j).machCost := by
      rw [← hrun]
    rw [hcost_eq, hmach_eq,
      bundle_branch_cost_decomp lsfInit C_lsst L sparsify k M N D ordSeq restarts hV₀ j τ,
      bundleWith_branch_machCost_eq lsfInit C_lsst L sparsify params spanConst k M N D ordSeq
        restarts hV₀ j τ]
    refine le_trans ?_ (Nat.le_mul_of_pos_left _ hlog_ge1)
    have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
      k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
    have ht1 : (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 ≤
        3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2 := by omega
    have ht2 : (base τ).activeComps.sum st₀.lazyInitCost ≤
        ((post_b τ).trees j).activeComps.sum (fun C => (st₀.activeBuckets C).sum fun b =>
          spanConst * spanInitBound (params M) L (bundleSplitBudget k M)
            (normGraph (st₀.bun (C, b)).graph)) := by
      have hact_eq : (base τ).activeComps = ((post_b τ).trees j).activeComps :=
        ((runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ordSeq restarts
          hV₀ j τ).2.activeComps).symm
      rw [hact_eq]
      have hact_sub : ((post_b τ).trees j).activeComps ⊆ components (D.G 0) := by
        have hbf : BundleBaseFieldsEq ((post_b τ).trees j) ((pre_b τ).trees j) :=
          (foldl_bundleRestart_props lsfInit C_lsst L sparsify (pre_b τ) (restarts τ)).2.2.2.2.1 j
        rw [hbf.activeComps]
        exact (hBun τ le_rfl).2.2.2.2.2.2.2.2.2.1.2
      have hBun0 := hBun 0 (Nat.zero_le τ)
      have hI₀ : CompLSFInv C_lsst (D.ℓ 0) st₀.cs := hBun0.2.2.2.2.2.2.2.1
      obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
      refine Finset.sum_le_sum fun C hC => ?_
      have hC0 : C ∈ components (D.G 0) := hact_sub hC
      refine Finset.sum_le_sum fun b _ => ?_
      have hR0 := ((hBun0.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).1
      have hPart := hR0.1 ρ₀ hI₀.hG_val (compLSF_RF_isRSF hI₀) hρ₀
      have hVal : (normGraph (st₀.bun (C, b)).graph).IsValid :=
        normGraph_isValid (BundleState.graph_isValid hPart)
      have hm_le : (normGraph (st₀.bun (C, b)).graph).m ≤ M := by
        rw [normGraph_m]
        exact le_trans (Finset.card_le_card (hPart.1.trans Finset.sdiff_subset)) hM
      exact le_trans (dynSpanner_init_cost_le_spanInitBound hVal hL hm_le hSp)
        (Nat.le_mul_of_pos_left _ hConst)
    have ht4 : (∑ r ∈ Finset.range τ, ((infoB r).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b => ((infoB r).U_B (C, b)).length)) ≤
        ∑ r ∈ Finset.range τ, ((infoB r).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b =>
            (((post_b r).trees j).dyn (C, b)).G.batchEnc ((infoB r).U_B (C, b))) :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun C _ => Finset.sum_le_sum fun b _ =>
        DynSpanner.length_le_batchEnc _ _
    have ht5 : (∑ r ∈ Finset.range τ, (infoB r).U_S.length) ≤
        ∑ r ∈ Finset.range τ, ((post_b r).trees j).S_cur.batchEnc (infoB r).U_S :=
      Finset.sum_le_sum fun r _ => DynSpanner.length_le_batchEnc _ _
    have ht6 : (∑ r ∈ Finset.range τ, ((infoB r).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b => ((infoB r).stepOut (C, b)).cost)) ≤
        ∑ r ∈ Finset.range τ, ((infoB r).state.activeComps.sum fun C =>
          (st₀.activeBuckets C).sum fun b =>
            spanBatchChargeWith spanConst (params M) L
              ((((post_b r).trees j).initBunG (C, b)).n + bundleSplitBudget k M)
              (((post_b r).trees j).initBunG (C, b))
              (((post_b r).trees j).dyn (C, b)).G ((infoB r).U_B (C, b))) :=
      run_dyn_cost_le_charge lsfInit C_lsst L hL sparsify (params M) spanConst hConst
        k M N τ hk D ordSeq restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd (hsum.symm ▸ hThr) j hInit
        τ le_rfl
    have ht7 : (∑ r ∈ Finset.range (τ + 1),
          (restarts r).count j * singleBundleRestartCost L sparsify ((pre_b r).trees j) (ordSeq r)) ≤
        ∑ r ∈ Finset.range (τ + 1), (restarts r).count j *
          (((pre_b r).trees j).cs.G.m + 1 +
            ((pre_b r).trees j).activeComps.sum fun C => (st₀.activeBuckets C).sum fun b =>
              spanConst * spanInitBound (params M) L (bundleSplitBudget k M)
                (normGraph (restartBucketBundle ((pre_b r).trees j) (ordSeq r) C b).graph)) := by
      refine Finset.sum_le_sum fun r hr => Nat.mul_le_mul_left _ ?_
      have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hBr := hBun r hr_le
      set trr := (pre_b r).trees j
      have hAB_r : trr.activeBuckets = st₀.activeBuckets := hBr.2.2.2.2.1
      have hSB_r : trr.splitBound = bundleSplitBudget k M := hBr.2.2.1
      have hm0_r : trr.m₀ = M := hBr.2.1
      have hk_r : trr.k = k := hBr.1
      have hI_r : CompLSFInv C_lsst (D.ℓ 0) trr.cs := hBr.2.2.2.2.2.2.2.1
      have hG_r : trr.cs.G = D.G r := hBr.2.2.2.2.2.2.2.2.1
      have hact_r : trr.activeComps ⊆ components (D.G 0) := hBr.2.2.2.2.2.2.2.2.2.1.2
      obtain ⟨ρ_r, hρ_r⟩ := orderedUpTo_rot_at hOrd hr_le hG_r
      have hC_val : (coreGraph trr.cs.G trr.cs.lsf).IsValid := by
        intro e he
        have hth := hI_r.hG_val e (Finset.mem_sdiff.mp he).1
        exact ⟨(root_mem_R (compLSF_RF_isRSF hI_r) hth.1).1,
          (root_mem_R (compLSF_RF_isRSF hI_r) hth.2).1⟩
      unfold singleBundleRestartCost
      rw [hAB_r, hSB_r, hm0_r]
      refine Nat.add_le_add_left (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) _
      have hC0 : C ∈ components (D.G 0) := hact_r hC
      have hR := ((hBr.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).1
      have hEcore : (trr.bun (C, b)).edges ⊆ (coreGraph trr.cs.G trr.cs.lsf).E :=
        (hR.1 ρ_r hI_r.hG_val (compLSF_RF_isRSF hI_r) hρ_r).1
      have hHb_val : (normGraph (restartBucketBundle trr (ordSeq r) C b).graph).IsValid := by
        apply normGraph_isValid
        dsimp only [restartBucketBundle]
        rw [hk_r, initBundleFor_eq hI_r hρ_r]
        exact BundleState.graph_isValid
          (initBundleState_inv
            (coreRotation (L := trr.cs.lsf) ρ_r hI_r.hG_val (compLSF_RF_isRSF hI_r))
            hC_val hEcore hk)
      have hHb_m : (normGraph (restartBucketBundle trr (ordSeq r) C b).graph).m ≤ M := by
        rw [normGraph_m]
        have hsub1 : (restartBucketBundle trr (ordSeq r) C b).edges ⊆ (trr.bun (C, b)).edges :=
          initBundleFor_edges_sub trr.cs (ordSeq r) (trr.bun (C, b)).edges trr.k
        have hsub2 : (trr.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := by
          rw [((hBr.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).2.2.1]; exact Finset.sdiff_subset
        have hsub3 : (st₀.bun (C, b)).edges ⊆ (D.G 0).E := by
          have hB0 := hBun 0 (Nat.zero_le τ)
          have hI₀ : CompLSFInv C_lsst (D.ℓ 0) st₀.cs := hB0.2.2.2.2.2.2.2.1
          obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
          have hP0 := ((hB0.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).1.1 ρ₀ hI₀.hG_val
            (compLSF_RF_isRSF hI₀) hρ₀
          exact hP0.1.trans Finset.sdiff_subset
        exact le_trans (Finset.card_le_card ((hsub1.trans hsub2).trans hsub3)) hM
      exact le_trans (dynSpanner_init_cost_le_spanInitBound hHb_val hL hHb_m hSp)
        (Nat.le_mul_of_pos_left _ hConst)
    exact Nat.add_le_add
      (Nat.add_le_add
        (le_trans
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add (le_trans ht1 (Nat.le_add_right _ _)) ht2)
                (le_refl (∑ r ∈ Finset.range τ, (D.U (r + 1)).length)))
              ht4)
            ht5)
          (Nat.le_add_right _ _))
        ht6)
      ht7
  · have hs_eq : s = Tm.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ordSeq 0) :=
      hrun.symm.trans (runOrdAfterRestartsMachWith_of_empty lsfInit C_lsst L sparsify params
        spanConst k M N D ordSeq restarts hV₀ τ)
    have hE_empty : (D.G 0).E = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      exact hV₀ ⟨(D.G 0).tail e, (hG₀ e he).1⟩
    have hm0 : (D.G 0).m = 0 := by simp [MGraph.m, hE_empty]
    have hlarge_empty : largeComps k (D.G 0) = ∅ := by
      ext C
      simp only [largeComps, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hC hge
      have hle : (compGraph (D.G 0) C).m ≤ (D.G 0).m :=
        Finset.card_le_card (Finset.filter_subset _ _)
      omega
    have htr_eq : SparseCoreBundleState.trees (L := L) s j =
        initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0)
          (ordSeq 0) j := by
      rw [hs_eq]; rfl
    rw [htr_eq]
    have hcost0 : (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0)
        (D.ℓ 0) (ordSeq 0) j).cost = (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
        (largeComps k (D.G 0)).sum _ := rfl
    have hmach0 := initBundleTreeWithParams_machCost lsfInit L sparsify params spanConst
      k M N (D.G 0) (D.ℓ 0) (ordSeq 0) j
    dsimp only at hmach0
    rw [hcost0, hmach0, hlarge_empty, Finset.sum_empty]
    have hinner : (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 + 0 ≤
        3 * (D.G 0).m + 3 * (activeSubgraph (D.G 0)).n + 2 +
          lsfInitSize (D.G 0) * bundleLogFactor M N ^ 2 +
          (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0)
            (ordSeq 0) j).activeComps.sum
          (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N (D.G 0) (D.ℓ 0)
            (ordSeq 0) j).lazyMachInitCost := by omega
    exact le_trans hinner (Nat.le_mul_of_pos_right _ hlog_ge1)

end MinCostFlow.SparseCore
