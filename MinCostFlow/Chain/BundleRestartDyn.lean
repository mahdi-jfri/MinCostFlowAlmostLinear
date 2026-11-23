module

public import MinCostFlow.Chain.BundleRestartBun
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.BundleEpochCost
import MinCostFlow.SparseCore.BundleInitCount
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bucket Spanner Dynamics Between Restarts

Publicly re-exports `BundleRestartBun` (`runOrdAfterRestarts_bun_inv`, `foldl_bundleRestart_*`)
and proves `epochBundleSeq_dyn_spec`: over any non-restarted suffix `[s₀, t]` of branch `j`, each
bucket starts with `Hb C b := ((st 0).bun (C, b)).graph` (`IsValid`, `m ≤ G₀.m`, `n ≤ 2 m`,
`maxDeg ≤ k`, `k * vertices.card ≤ k * R_C.card + 2 * edges.card`) and receives valid batches of
deletions and splits matching `DynSpanner.runBatchState` and `DynSpanner.runBatchStepOut`, with
local split and deletion bounds from `bundleCompStep_stage` (without needing `hThresh`).

Also proves `epochBundleSeq_Hb_m_sum_le`, `epochBundleSeq_deletes_sum_le`, and
`epochBundleSeq_batchSplitCount_le_splitB` (under `hThresh`) for the epoch Theorem 8.2, recourse,
and cost bounds.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-- Any bucket batch list over a non-restarted suffix `[s₀, t]` is `Hb.BatchIsValid` and
consists strictly of deletions and splits, matching `DynSpanner.runBatchState` and
`DynSpanner.runBatchStepOut` from `Hb C b := ((st 0).bun (C, b)).graph` without `hThresh`. -/
theorem epochBundleSeq_dyn_spec
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (_hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀_rest : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let G₀ := D.G 0
    let splitB := bundleSplitBudget k M
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let Hb := fun C b => ((st 0).bun (C, b)).graph
    let Us_ep : Finset ℕ → ℤ → List (List Update) := fun C b =>
      (List.range (t - s₀)).map fun r =>
        (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
    ∀ C ∈ components G₀, ∀ b : ℤ,
      (Hb C b).IsValid ∧ (Hb C b).m ≤ G₀.m ∧ (Hb C b).n ≤ 2 * (Hb C b).m ∧
      (Hb C b).maxDeg ≤ k ∧
      k * ((st 0).bun (C, b)).vertices.card ≤
        k * ((st 0).cs.compSt C).R.card + 2 * ((st 0).bun (C, b)).edges.card ∧
      (Hb C b).BatchIsValid (Us_ep C b).flatten ∧
      (∀ op ∈ (Us_ep C b).flatten, isDelOrSplit op) ∧
      batchSplitCount (Us_ep C b).flatten ≤
        2 * (((st (t - s₀)).cs.compSt C).R \ ((st 0).cs.compSt C).R).card ∧
      (st 0).dyn (C, b) = (DynSpanner.init (normGraph (Hb C b)) L (phaseBase ((Hb C b).n + splitB) L)
        (sparsify M)).state ∧
      (∀ δ ≤ t - s₀,
        (st δ).dyn (C, b) = DynSpanner.runBatchState (L := L) (normGraph (Hb C b))
          (phaseBase ((Hb C b).n + splitB) L) (sparsify M) (Us_ep C b) δ ∧
        GraphEq ((st δ).dyn (C, b)).G ((st δ).bun (C, b)).graph ∧
        ((st δ).dyn (C, b)).G.IsValid ∧
        ((st δ).dyn (C, b)).G.IsSubgraph ((st δ).dyn (C, b)).H ∧
        ((st δ).bun (C, b)).vertices.card ≤
          ((st 0).bun (C, b)).vertices.card +
            2 * (((st δ).cs.compSt C).R \ ((st 0).cs.compSt C).R).card) ∧
      (∀ δ < t - s₀,
        let info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1))
          (ord (s₀ + δ)) (ord (s₀ + δ + 1))
        info.stepOut (C, b) =
          DynSpanner.runBatchStepOut (L := L) (normGraph (Hb C b)) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) δ ∧
        ((st δ).dyn (C, b)).G.BatchIsValid (info.U_B (C, b)) ∧
        (∀ op ∈ info.U_B (C, b), isDelOrSplit op) ∧
        batchSplitCount (info.U_B (C, b)) ≤
          2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card ∧
        (info.U_B (C, b)).countP deleteTag ≤
          (((st δ).bun (C, b)).edges ∩ batchDeletes (D.U (s₀ + δ + 1))).card ∧
        ((st δ).bun (C, b)).edges \ ((st (δ + 1)).bun (C, b)).edges ⊆
          batchDeletes (D.U (s₀ + δ + 1)) ∧
        Disjoint ((st (δ + 1)).bun (C, b)).edges (batchDeletes (D.U (s₀ + δ + 1)))) := by
  classical
  intro G₀ splitB st Hb Us_ep C hC b
  let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  obtain ⟨_, hSt_step⟩ := epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  obtain ⟨hEp_lt, _, hEp_fin⟩ := epochBundleSeq_eq_post lsfInit C_lsst L sparsify
    k M N D ord restarts s₀ t j hst
  have hne_pre : ∀ s, (T.runOrdAfterUpdate k M N D ord restarts s).1.isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).1.trans
      (decide_eq_true hV₀)
  have hSt0_eq : st 0 = (T.runOrdAfterRestarts k M N D ord restarts s₀).trees j := by
    have hSt0_ne : ¬ (s₀ = t ∧ s₀ < t) := fun h => absurd h.1 (ne_of_lt h.2)
    dsimp only [st, epochBundleSeq, T]
    rw [Nat.add_zero]
    simp only [hSt0_ne, ↓reduceIte]
  have hbf_s0 : BundleBaseFieldsEq
      ((T.runOrdAfterRestarts k M N D ord restarts s₀).trees j)
      ((T.runOrdAfterUpdate k M N D ord restarts s₀).1.trees j) :=
    (foldl_bundleRestart_props lsfInit C_lsst L sparsify
      (T.runOrdAfterUpdate k M N D ord restarts s₀).1 (restarts s₀)).2.2.2.2.1 j
  have hBun_s0 := hBun s₀ (le_trans hst htτ)
  have hReady_ep : ∀ δ ≤ t - s₀,
      (st δ).k = k ∧ (st δ).m₀ = M ∧ (st δ).splitBound = splitB ∧
      CompLSFInv C_lsst (D.ℓ 0) (st δ).cs ∧ (st δ).cs.G = D.G (s₀ + δ) ∧
      (st δ).cs.G₀ = G₀ ∧
      BundleCompReady (st δ).cs C ((st δ).bun (C, b)) k (ord (s₀ + δ)) ∧
      ((st δ).bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
      GraphEq ((st δ).dyn (C, b)).G ((st δ).bun (C, b)).graph := by
    intro δ hδ
    have hBδ := hBun (s₀ + δ) (by omega)
    have hbf_δ : BundleBaseFieldsEq
        ((T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j)
        ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1.trees j) :=
      (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1 (restarts (s₀ + δ))).2.2.2.2.1 j
    by_cases hlt : δ < t - s₀
    · have heq : st δ = (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j := hEp_lt δ hlt
      have hG₀_eq : (st δ).cs.G₀ = G₀ := by
        rw [heq, hbf_δ.cs, hBδ.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
      refine ⟨heq ▸ hbf_δ.k.trans hBδ.1, heq ▸ hbf_δ.m₀.trans hBδ.2.1,
        heq ▸ hbf_δ.splitBound.trans hBδ.2.2.1,
        heq ▸ hbf_δ.cs.symm ▸ hBδ.2.2.2.2.2.2.2.1,
        by rw [heq, hbf_δ.cs, hBδ.2.2.2.2.2.2.2.2.1], hG₀_eq,
        by rw [heq]; exact ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1,
        by rw [heq, ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1,
            ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]; exact Finset.sdiff_subset,
        by rw [heq]; exact ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.2.2⟩
    · have hδeq : δ = t - s₀ := by omega
      subst hδeq
      by_cases hst_lt : s₀ < t
      · have heq : st (t - s₀) = (T.runOrdAfterUpdate k M N D ord restarts t).1.trees j :=
          hEp_fin hst_lt
        have hst_eq : s₀ + (t - s₀) = t := by omega
        rw [hst_eq] at hBδ ⊢
        have hG₀_eq : (st (t - s₀)).cs.G₀ = G₀ := by
          rw [heq, hBδ.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
        refine ⟨heq ▸ hBδ.1, heq ▸ hBδ.2.1, heq ▸ hBδ.2.2.1,
          heq ▸ hBδ.2.2.2.2.2.2.2.1, by rw [heq, hBδ.2.2.2.2.2.2.2.2.1], hG₀_eq,
          by rw [heq]; exact ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1,
          by rw [heq, ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]; exact Finset.sdiff_subset,
          by rw [heq]; exact ((hBδ.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.2.1⟩
      · have heq0 : t - s₀ = 0 := by omega
        rw [heq0, Nat.add_zero] at hBδ ⊢
        have hG₀_eq : (st 0).cs.G₀ = G₀ := by
          rw [hSt0_eq, hbf_s0.cs, hBun_s0.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
        refine ⟨hSt0_eq ▸ hbf_s0.k.trans hBun_s0.1, hSt0_eq ▸ hbf_s0.m₀.trans hBun_s0.2.1,
          hSt0_eq ▸ hbf_s0.splitBound.trans hBun_s0.2.2.1,
          hSt0_eq ▸ hbf_s0.cs.symm ▸ hBun_s0.2.2.2.2.2.2.2.1,
          by rw [hSt0_eq, hbf_s0.cs, hBun_s0.2.2.2.2.2.2.2.2.1], hG₀_eq,
          by rw [hSt0_eq]; exact ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.1,
          by rw [hSt0_eq, ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1,
              ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]; exact Finset.sdiff_subset,
          by rw [hSt0_eq]; exact ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.2.2⟩
  -- Initial bundle graph properties at δ = 0
  have hR0 := hReady_ep 0 (Nat.zero_le _)
  rw [Nat.add_zero] at hR0
  obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (le_trans hst htτ) hR0.2.2.2.2.1
  have hPart0 := hR0.2.2.2.2.2.2.1.1 ρ₀ hR0.2.2.2.1.hG_val (compLSF_RF_isRSF hR0.2.2.2.1) hρ₀
  have hHb_val : (Hb C b).IsValid := BundleState.graph_isValid hPart0
  have hHb_deg : (Hb C b).maxDeg ≤ k := BundleState.maxDeg_le hPart0
  have hHb_m : (Hb C b).m ≤ G₀.m := by
    have h1 : ((st 0).bun (C, b)).edges.card ≤ (st₀.bun (C, b)).edges.card :=
      Finset.card_le_card hR0.2.2.2.2.2.2.2.1
    have h2 : (st₀.bun (C, b)).edges ⊆ G₀.E :=
      (initBundleFor_edges_subset _ _ _ _).trans
        ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
    exact le_trans h1 (Finset.card_le_card h2)
  have hHb_mM : (Hb C b).m ≤ M := le_trans hHb_m hM
  -- Show (st 0).bun (C, b) is a fresh `initBundleFor` (either restarted or initial)
  -- and (st 0).dyn (C, b) is `DynSpanner.init (Hb C b) ...`
  have hInit_bun_dyn :
      (Hb C b).n ≤ 2 * (Hb C b).m ∧
      k * ((st 0).bun (C, b)).vertices.card ≤
        k * ((st 0).cs.compSt C).R.card + 2 * ((st 0).bun (C, b)).edges.card ∧
      (st 0).dyn (C, b) = (DynSpanner.init (normGraph (Hb C b)) L (phaseBase ((Hb C b).n + splitB) L)
        (sparsify M)).state := by
    have hInitFor_bnds : ∀ (cs' : CompLSFState) (ord' : ℕ → List End) (E : Finset ℕ),
        CompLSFInv C_lsst (D.ℓ 0) cs' → cs'.G₀ = G₀ →
        (∃ ρ' : Rotation cs'.G, ρ'.order = ord') →
        E ⊆ (coreGraph cs'.G cs'.lsf).E →
        E ⊆ (cs'.compSt C).G.E →
        (∀ e ∈ E, e ∉ cs'.crossEdges) →
        (initBundleFor cs' ord' E k).graph.n ≤ 2 * (initBundleFor cs' ord' E k).graph.m ∧
        k * (initBundleFor cs' ord' E k).vertices.card ≤
          k * (cs'.compSt C).R.card + 2 * (initBundleFor cs' ord' E k).edges.card := by
      intro cs' ord' E hI' hG₀' ⟨ρ', hρ'⟩ hEcore hEC hX
      refine ⟨initBundleFor_n_le_two_m cs' ord' hEcore hk, ?_⟩
      rw [initBundleFor_eq hI' hρ']
      refine initBundleState_vertex_bound_at _ hEcore hk _ ?_
      intro x hx
      obtain ⟨e, side⟩ := x
      have heC := hEC hx
      have hends := hI'.hNonCross_ends C (hG₀'.symm ▸ hC) e heC (hX e hx)
      have hval := (hI'.hCompLSF C (hG₀'.symm ▸ hC)).1.hG_val e heC
      rw [coreGraph_src]
      apply compLSF_root_mem_R hI' (hG₀'.symm ▸ hC)
      cases side
      · change cs'.G.head e ∈ _; rw [← hends.2]; exact hval.2
      · change cs'.G.tail e ∈ _; rw [← hends.1]; exact hval.1
    by_cases hC_act : C ∈ (st 0).activeComps
    · have hC_act_pre : C ∈ ((T.runOrdAfterUpdate k M N D ord restarts s₀).1.trees j).activeComps := by
        rw [hSt0_eq, hbf_s0.activeComps] at hC_act; exact hC_act
      have hact_case : j ∈ restarts s₀ ∨ (s₀ = 0 ∧ j ∉ restarts 0) := by
        rcases hs₀_rest with rfl | hj_r
        · by_cases hj0 : j ∈ restarts 0
          · exact Or.inl hj0
          · exact Or.inr ⟨rfl, hj0⟩
        · exact Or.inl hj_r
      rcases hact_case with hj_r | ⟨rfl, hj0⟩
      · set preS0 := (T.runOrdAfterUpdate k M N D ord restarts s₀).1
        have ha : ((T.runOrdAfterRestarts k M N D ord restarts s₀).trees j).bun (C, b) =
              restartBucketBundle (preS0.trees j) preS0.ord C b ∧
            ((T.runOrdAfterRestarts k M N D ord restarts s₀).trees j).dyn (C, b) =
              (DynSpanner.init (normGraph (restartBucketBundle (preS0.trees j) preS0.ord C b).graph) L
                (phaseBase ((restartBucketBundle (preS0.trees j) preS0.ord C b).graph.n +
                  (preS0.trees j).splitBound) L) (sparsify (preS0.trees j).m₀)).state :=
          foldl_bundleRestart_active lsfInit C_lsst L sparsify (restarts s₀)
            preS0 j (C := C) (b := b) (hne_pre s₀) hC_act_pre hj_r
        have hbun0 : (st 0).bun (C, b) =
            initBundleFor (preS0.trees j).cs (ord s₀) ((preS0.trees j).bun (C, b)).edges k := by
          rw [hSt0_eq, ha.1]
          dsimp only [restartBucketBundle]
          rw [((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s₀).2.2.2.2 hV₀).1,
            hBun_s0.1]
        have hcs0 : (st 0).cs = (preS0.trees j).cs := by
          rw [hSt0_eq, hbf_s0.cs]
        have hdyn0 : (st 0).dyn (C, b) = (DynSpanner.init (normGraph (Hb C b)) L
            (phaseBase ((Hb C b).n + splitB) L) (sparsify M)).state := by
          dsimp only [Hb]
          rw [hSt0_eq, ha.2, ha.1, hBun_s0.2.2.1, hBun_s0.2.1]
        have hPreR := ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).1
        have hPreD := ((hBun_s0.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.1
        obtain ⟨ρ_pre, hρ_pre⟩ := orderedUpTo_rot_at hOrd (le_trans hst htτ)
          hBun_s0.2.2.2.2.2.2.2.2.1
        have hI_pre := hBun_s0.2.2.2.2.2.2.2.1
        have hEcore := (hPreR.1 ρ_pre hI_pre.hG_val (compLSF_RF_isRSF hI_pre) hρ_pre).1
        have hbnds := hInitFor_bnds _ (ord s₀) _ hI_pre
          (by rw [hBun_s0.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl) ⟨ρ_pre, hρ_pre⟩
          hEcore hPreR.2.2 (fun e he hc => Finset.disjoint_left.mp hPreD he (hI_pre.hCross_sub hc))
        rw [hcs0]
        dsimp only [Hb]
        rw [hbun0]
        exact ⟨hbnds.1, hbnds.2, by rw [← hbun0]; exact hdyn0⟩
      · have hni := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
          (T.runOrdAfterUpdate k M N D ord restarts 0).1 (restarts 0)).2.2.2.2.2 j hj0
        have hst0_is : st 0 = st₀ := hSt0_eq.trans hni
        have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
        have hE0C : bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b ⊆
            (st₀.cs.compSt C).G.E := by
          have hR_0 := ((hBun 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.1
          obtain ⟨ρ0', hρ0'⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
          have hEqE := initBundleFor_edges hI₀ hρ0'
            (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b) k
          exact hEqE ▸ hR_0.2.2
        obtain ⟨ρ0', hρ0'⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
        have hbnds := hInitFor_bnds st₀.cs (ord 0)
          (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b)
          hI₀ rfl ⟨ρ0', hρ0'⟩ (Finset.filter_subset _ _) hE0C
          (fun _ _ hc => Finset.notMem_empty _ hc)
        dsimp only [Hb]
        rw [hst0_is]
        exact ⟨hbnds.1, hbnds.2, rfl⟩
    · have hna_pre : C ∉ ((T.runOrdAfterUpdate k M N D ord restarts s₀).1.trees j).activeComps := by
        rw [hSt0_eq, hbf_s0.activeComps] at hC_act; exact hC_act
      have hunt := hBun_s0.2.2.2.2.2.2.2.2.2.2.1 C hC hna_pre
      have hbun_st0 : (st 0).bun (C, b) = st₀.bun (C, b) := hSt0_eq ▸ (hunt.2 b).2.2.1
      have hdyn_st0 : (st 0).dyn (C, b) = st₀.dyn (C, b) := hSt0_eq ▸ (hunt.2 b).2.2.2
      have hcsC_st0 : ((st 0).cs.compSt C) = st₀.cs.compSt C := by
        rw [hSt0_eq, hbf_s0.cs]; exact hunt.1
      have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
      obtain ⟨ρ0', hρ0'⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (G := st₀.cs.G) rfl
      have hE0C : bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b ⊆
          (st₀.cs.compSt C).G.E := by
        have hR_0 := ((hBun 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.1
        have hEqE := initBundleFor_edges hI₀ hρ0'
          (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b) k
        exact hEqE ▸ hR_0.2.2
      have hbnds := hInitFor_bnds st₀.cs (ord 0)
        (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b)
        hI₀ rfl ⟨ρ0', hρ0'⟩ (Finset.filter_subset _ _) hE0C
        (fun _ _ hc => Finset.notMem_empty _ hc)
      dsimp only [Hb]
      rw [hbun_st0, hdyn_st0, hcsC_st0]
      exact ⟨hbnds.1, hbnds.2, rfl⟩
  -- Per-step bundleCompStep_stage facts on the epoch
  have hStepEp : ∀ δ < t - s₀,
      let info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1))
        (ord (s₀ + δ)) (ord (s₀ + δ + 1))
      ((st δ).bun (C, b)).graph.BatchIsValid (info.U_B (C, b)) ∧
      ((st (δ + 1)).bun (C, b)).graph = ((st δ).bun (C, b)).graph.applyBatch (info.U_B (C, b)) ∧
      (∀ op ∈ info.U_B (C, b), isDelOrSplit op) ∧
      batchSplitCount (info.U_B (C, b)) ≤
        2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card ∧
      (info.U_B (C, b)).countP deleteTag ≤
        (((st δ).bun (C, b)).edges ∩ batchDeletes (D.U (s₀ + δ + 1))).card ∧
      ((st (δ + 1)).bun (C, b)).vertices.card =
        ((st δ).bun (C, b)).vertices.card + batchSplitCount (info.U_B (C, b)) ∧
      ((st (δ + 1)).bun (C, b)).edges =
        ((st δ).bun (C, b)).edges \ batchDeletes (D.U (s₀ + δ + 1)) ∧
      ((st δ).cs.compSt C).R ⊆ ((st (δ + 1)).cs.compSt C).R := by
    intro δ hδ info
    have hRδ := hReady_ep δ (Nat.le_of_lt hδ)
    have hDt := hD (s₀ + δ + 1) (Nat.succ_pos _) (by omega)
    simp only [Nat.add_sub_cancel] at hDt
    have hBV : (st δ).cs.G.BatchIsValid (D.U (s₀ + δ + 1)) := by rw [hRδ.2.2.2.2.1]; exact hDt.1
    obtain ⟨ρδ, σδ, hρδ, hσδ, hrotδ⟩ := orderedUpTo_rot_step hOrd (by omega : s₀ + δ < τ) hRδ.2.2.2.2.1
    have hstg := bundleCompStep_stage hRδ.2.2.2.1 hBV hρδ hσδ hrotδ
      (hRδ.2.2.2.2.2.1.symm ▸ hC) hRδ.2.2.2.2.2.2.1
    have hst1 : st (δ + 1) = (stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1))
        (ord (s₀ + δ)) (ord (s₀ + δ + 1))).state := (hSt_step δ hδ).1
    have hUB_eq : info.U_B (C, b) =
        (bundleCompStep (st δ).cs ((st δ).bun (C, b)) k (ord (s₀ + δ)) (ord (s₀ + δ + 1))
          (D.U (s₀ + δ + 1))).1 := by
      change (bundleCompStep (st δ).cs ((st δ).bun (C, b)) (st δ).k _ _ _).1 = _; rw [hRδ.1]
    have hbun_eq : (st (δ + 1)).bun (C, b) =
        (bundleCompStep (st δ).cs ((st δ).bun (C, b)) k (ord (s₀ + δ)) (ord (s₀ + δ + 1))
          (D.U (s₀ + δ + 1))).2 := by
      rw [hst1]; change (bundleCompStep (st δ).cs ((st δ).bun (C, b)) (st δ).k _ _ _).2 = _; rw [hRδ.1]
    have hcs_eq : (st (δ + 1)).cs = compLSFBatch (st δ).cs (D.U (s₀ + δ + 1)) := by
      rw [hst1]; rfl
    have hRsub := (compLSFBatch_compSt hRδ.2.2.2.1 hBV (hRδ.2.2.2.2.2.1.symm ▸ hC)).2.2.2.1
    rw [hUB_eq, hbun_eq, hcs_eq]
    exact ⟨hstg.2.2.1, hstg.2.2.2.1, hstg.2.2.2.2.1, hstg.2.2.2.2.2.1,
      hstg.2.2.2.2.2.2.1, hstg.2.2.2.2.2.2.2.1, hstg.2.1, hRsub⟩
  -- Prefix induction for DynSpanner.runBatchState and vertex/split counts
  have hPref : ∀ d ≤ t - s₀,
      let pref := ((Us_ep C b).take d).flatten
      (Hb C b).BatchIsValid pref ∧
      (∀ op ∈ pref, isDelOrSplit op) ∧
      ((st d).dyn (C, b)).G = (normGraph (Hb C b)).applyBatch pref ∧
      (st d).dyn (C, b) = DynSpanner.runBatchState (L := L) (normGraph (Hb C b))
        (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take d) d ∧
      ((st d).dyn (C, b)).G.IsValid ∧
      ((st d).dyn (C, b)).G.IsSubgraph ((st d).dyn (C, b)).H ∧
      ((st 0).cs.compSt C).R ⊆ ((st d).cs.compSt C).R ∧
      batchSplitCount pref ≤ 2 * (((st d).cs.compSt C).R \ ((st 0).cs.compSt C).R).card ∧
      ((st d).bun (C, b)).vertices.card ≤
        ((st 0).bun (C, b)).vertices.card +
          2 * (((st d).cs.compSt C).R \ ((st 0).cs.compSt C).R).card := by
    intro d
    induction d with
    | zero =>
      intro _
      have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hinv0 := (DynSpanner.runInv_all (normGraph_isValid hHb_val) hL hq1 hHb_mM hSp (us := [])
        (by trivial) (fun _ h => by simp at h) 0 le_rfl).1
      have hG0_eq : ((st 0).dyn (C, b)).G = normGraph (Hb C b) := by
        rw [hInit_bun_dyn.2.2]; exact hinv0.G_eq
      refine ⟨trivial, fun _ h => by simp at h, hG0_eq, hInit_bun_dyn.2.2,
        hG0_eq.symm ▸ normGraph_isValid hHb_val, hInit_bun_dyn.2.2.symm ▸ hinv0.H_sub,
        Finset.Subset.rfl, by simp [batchSplitCount], by simp⟩
    | succ δ ih =>
      intro hδ1
      have hδ_lt : δ < t - s₀ := hδ1
      obtain ⟨hBV_p, hds_p, hApp_p, hRun_p, _, _, hR0_p, hsc_p, hv_p⟩ := ih (Nat.le_of_lt hδ_lt)
      set info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))
      have hRδ := hReady_ep δ (Nat.le_of_lt hδ_lt)
      have hSδ := hStepEp δ hδ_lt
      have hget : (Us_ep C b)[δ]? = some (info.U_B (C, b)) := by
        dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hδ_lt]; rfl
      have htake : ((Us_ep C b).take (δ + 1)).flatten =
          ((Us_ep C b).take δ).flatten ++ info.U_B (C, b) := by
        rw [take_succ_of_getElem? hget, List.flatten_append]; simp
      have hBV_s1 : (Hb C b).BatchIsValid ((Us_ep C b).take (δ + 1)).flatten := by
        rw [htake, SparseCore.batchIsValid_append]
        refine ⟨hBV_p, ?_⟩
        have hge : GraphEq ((Hb C b).applyBatch ((Us_ep C b).take δ).flatten)
            ((st δ).bun (C, b)).graph :=
          graphEq_trans (graphEq_applyBatch (graphEq_symm (normGraph_graphEq _)) _)
            (hApp_p ▸ hRδ.2.2.2.2.2.2.2.2)
        exact (graphEq_batchIsValid hge _).mpr hSδ.1
      have hBV_s1_n : (normGraph (Hb C b)).BatchIsValid ((Us_ep C b).take (δ + 1)).flatten :=
        (graphEq_batchIsValid (normGraph_graphEq _) _).mpr hBV_s1
      have hds_s1 : ∀ op ∈ ((Us_ep C b).take (δ + 1)).flatten, isDelOrSplit op := fun op hop => by
        rw [htake, List.mem_append] at hop
        exact hop.elim (hds_p op) (hSδ.2.2.1 op)
      have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hTrace := DynSpanner.batchTrace_spec (normGraph_isValid hHb_val) hL hq1 hHb_mM hSp hBV_s1_n hds_s1
      have hUs_take_len : ((Us_ep C b).take (δ + 1)).length = δ + 1 :=
        List.length_take_of_le (by simp [Us_ep]; exact hδ1)
      have htr1 := hTrace.1 (δ + 1) hUs_take_len.symm.le
      have hget_take : ((Us_ep C b).take (δ + 1))[δ]? = some (info.U_B (C, b)) := by
        rw [List.getElem?_take]; simp [hget]
      have hrun_eq_δ : DynSpanner.runBatchState (L := L) (normGraph (Hb C b))
          (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take δ) δ =
          DynSpanner.runBatchState (L := L) (normGraph (Hb C b))
            (phaseBase ((Hb C b).n + splitB) L) (sparsify M) ((Us_ep C b).take (δ + 1)) δ := by
        rw [bundleRunBatchState_take_eq _ _ _ ((Us_ep C b).take (δ + 1)) δ δ le_rfl]
        simp [List.take_take]
      have hstep_st : (st (δ + 1)).dyn (C, b) =
          (DynSpanner.update ((st δ).dyn (C, b)) (info.U_B (C, b)) (sparsify M)).state := by
        have hstep_eq : (st (δ + 1)).dyn (C, b) = info.state.dyn (C, b) :=
          congrFun (congrArg BundleTreeState.dyn (hSt_step δ hδ_lt).1) (C, b)
        rw [hstep_eq]
        change (DynSpanner.update ((st δ).dyn (C, b)) (info.U_B (C, b)) (sparsify (st δ).m₀)).state = _
        rw [hRδ.2.1]
      have hrun_s1 : (st (δ + 1)).dyn (C, b) =
          DynSpanner.runBatchState (L := L) (normGraph (Hb C b)) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) ((Us_ep C b).take (δ + 1)) (δ + 1) := by
        rw [hstep_st, hRun_p, hrun_eq_δ]
        dsimp only [DynSpanner.runBatchState]
        rw [hget_take]
      have hTake_all_len : ((Us_ep C b).take (δ + 1)).flatten.length =
          batchPrefixLen ((Us_ep C b).take (δ + 1)) (δ + 1) := by
        simp [batchPrefixLen, List.take_of_length_le hUs_take_len.le]
      have hinv1 := (DynSpanner.runInv_all (normGraph_isValid hHb_val) hL hq1 hHb_mM hSp hBV_s1_n hds_s1
        ((Us_ep C b).take (δ + 1)).flatten.length le_rfl).1
      have hst_runState : (st (δ + 1)).dyn (C, b) =
          DynSpanner.runState (normGraph (Hb C b)) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) ((Us_ep C b).take (δ + 1)).flatten
            ((Us_ep C b).take (δ + 1)).flatten.length := by
        rw [hrun_s1, htr1.1, hTake_all_len]
      have hG_app1 : ((st (δ + 1)).dyn (C, b)).G =
          (normGraph (Hb C b)).applyBatch ((Us_ep C b).take (δ + 1)).flatten := by
        rw [hst_runState, hinv1.G_eq, List.take_length]
      have hR_step := hSδ.2.2.2.2.2.2.2
      have htel : (((st (δ + 1)).cs.compSt C).R \ ((st 0).cs.compSt C).R).card =
          (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card +
          (((st δ).cs.compSt C).R \ ((st 0).cs.compSt C).R).card := by
        rw [Finset.card_sdiff_of_subset (hR0_p.trans hR_step),
          Finset.card_sdiff_of_subset hR_step, Finset.card_sdiff_of_subset hR0_p]
        have c1 := Finset.card_le_card hR0_p
        have c2 := Finset.card_le_card hR_step
        omega
      refine ⟨hBV_s1, hds_s1, hG_app1, hrun_s1, ?_, ?_, hR0_p.trans hR_step, ?_, ?_⟩
      · rw [hG_app1]; exact applyBatch_isValid (normGraph_isValid hHb_val) hBV_s1_n
      · rw [hst_runState, hinv1.G_eq, List.take_length]
        have := hinv1.H_sub; rwa [List.take_length] at this
      · rw [htake, SparseCore.batchSplitCount_append]
        have h1 : batchSplitCount (info.U_B (C, b)) ≤
            2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card := hSδ.2.2.2.1
        omega
      · have h1 : batchSplitCount (info.U_B (C, b)) ≤
            2 * (((st (δ + 1)).cs.compSt C).R \ ((st δ).cs.compSt C).R).card := hSδ.2.2.2.1
        have h2 : ((st (δ + 1)).bun (C, b)).vertices.card =
            ((st δ).bun (C, b)).vertices.card + batchSplitCount (info.U_B (C, b)) := hSδ.2.2.2.2.2.1
        omega
  have hUs_len : (Us_ep C b).length = t - s₀ := by simp [Us_ep]
  have hTake_all : (Us_ep C b).take (t - s₀) = Us_ep C b := List.take_of_length_le hUs_len.le
  obtain ⟨hBV_fin, hds_fin, _, _, _, _, _, hsc_fin, _⟩ := hPref (t - s₀) le_rfl
  rw [hTake_all] at hBV_fin hds_fin hsc_fin
  refine ⟨hHb_val, hHb_m, hInit_bun_dyn.1, hHb_deg, hInit_bun_dyn.2.1, hBV_fin, hds_fin, hsc_fin,
    hInit_bun_dyn.2.2, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨_, _, _, hRun_d, hGval_d, hHsub_d, _, _, hv_d⟩ := hPref δ hδ
    rw [← bundleRunBatchState_take_eq _ _ _ (Us_ep C b) δ δ le_rfl] at hRun_d
    exact ⟨hRun_d, (hReady_ep δ hδ).2.2.2.2.2.2.2.2, hGval_d, hHsub_d, hv_d⟩
  · intro δ hδ
    obtain ⟨_, _, _, hRun_d, _, _, _, _, _⟩ := hPref δ (Nat.le_of_lt hδ)
    have hRδ := hReady_ep δ (Nat.le_of_lt hδ)
    have hSδ := hStepEp δ hδ
    have hget : (Us_ep C b)[δ]? = some
        ((stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))).U_B (C, b)) := by
      dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hδ]; rfl
    rw [← bundleRunBatchState_take_eq _ _ _ (Us_ep C b) δ δ le_rfl] at hRun_d
    refine ⟨?_, (graphEq_batchIsValid hRδ.2.2.2.2.2.2.2.2 _).mpr hSδ.1, hSδ.2.2.1, hSδ.2.2.2.1,
      hSδ.2.2.2.2.1, ?_, ?_⟩
    · dsimp only [DynSpanner.runBatchStepOut]
      rw [hget, ← hRun_d]
      change DynSpanner.update ((st δ).dyn (C, b)) _ (sparsify (st δ).m₀) = _
      rw [hRδ.2.1]
      rfl
    · rw [hSδ.2.2.2.2.2.2.1]
      intro e he
      obtain ⟨heB, hnot⟩ := Finset.mem_sdiff.mp he
      by_contra hnd
      exact hnot (Finset.mem_sdiff.mpr ⟨heB, hnd⟩)
    · rw [hSδ.2.2.2.2.2.2.1]
      exact Finset.sdiff_disjoint

/-! ## Sum bounds over an epoch (bucket edges, deletions, and split budget) -/

/-- The sum of initial bucket edge counts at the start of any epoch is at most `G₀.m`. -/
lemma epochBundleSeq_Hb_m_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    (components (D.G 0)).sum (fun C => (st₀.activeBuckets C).sum fun b =>
      ((st 0).bun (C, b)).graph.m) ≤ (D.G 0).m := by
  intro st₀ st
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit s₀ (le_trans hst htτ)
  have hSt0_eq : st 0 = (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify |>.runOrdAfterRestarts
      k M N D ord restarts s₀).trees j := by
    have hSt0_ne : ¬ (s₀ = t ∧ s₀ < t) := fun h => absurd h.1 (ne_of_lt h.2)
    dsimp only [st, epochBundleSeq]
    rw [Nat.add_zero]
    simp only [hSt0_ne, ↓reduceIte]
  have hinit := (initBundleTreeWith_buckets_sum_le lsfInit L sparsify (M := M) (N := N) hk
    (G₀ := D.G 0) (D.ℓ 0) (ord 0) j).2.1
  refine le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => ?_) hinit
  have hsub : ((st 0).bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := by
    rw [hSt0_eq, ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1,
      ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]
    exact Finset.sdiff_subset
  exact Finset.card_le_card hsub

/-- Across all components and active buckets, the total number of deletions in bundle batches at
any step of an epoch is at most the input batch length. -/
lemma epochBundleSeq_deletes_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N) (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀_rest : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ < t - s₀) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let info := stepBundleTree sparsify (st δ) (D.U (s₀ + δ + 1)) (ord (s₀ + δ)) (ord (s₀ + δ + 1))
    ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (info.U_B (C, b)).countP deleteTag) ≤ (D.U (s₀ + δ + 1)).length := by
  classical
  intro st₀ st info
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀_rest hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit (s₀ + δ) (by omega)
  have hEp_lt : st δ = (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify |>.runOrdAfterRestarts
      k M N D ord restarts (s₀ + δ)).trees j :=
    (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j hst).1 δ hδ
  have hDisj0 := (initBundleTreeWith_buckets_sum_le lsfInit L sparsify (M := M) (N := N) hk
    (G₀ := D.G 0) (D.ℓ 0) (ord 0) j).2.2.2
  have hsub_st0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st δ).bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges := fun C hC b => by
    rw [hEp_lt, ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1,
      ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.1]
    exact Finset.sdiff_subset
  let S : Finset ℕ → ℤ → Finset ℕ := fun C b =>
    ((st δ).bun (C, b)).edges ∩ batchDeletes (D.U (s₀ + δ + 1))
  have hdisj_b : ∀ C ∈ components (D.G 0),
      Set.PairwiseDisjoint (↑(st₀.activeBuckets C) : Set ℤ) (fun b => S C b) := by
    intro C hC b₁ _ b₂ _ hne
    exact Disjoint.mono (Finset.inter_subset_left.trans (hsub_st0 C hC b₁))
      (Finset.inter_subset_left.trans (hsub_st0 C hC b₂))
      (hDisj0 C hC C hC b₁ b₂ (fun h => hne (Prod.mk.inj h).2))
  have hdisj_C : Set.PairwiseDisjoint (↑(components (D.G 0)) : Set (Finset ℕ))
      (fun C => (st₀.activeBuckets C).biUnion (fun b => S C b)) := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨b₁, _, hb₁⟩ := Finset.mem_biUnion.mp he₁
    obtain ⟨b₂, _, hb₂⟩ := Finset.mem_biUnion.mp he₂
    exact Finset.disjoint_left.mp
      (hDisj0 C₁ hC₁ C₂ hC₂ b₁ b₂ (fun h => hne (Prod.mk.inj h).1))
      (hsub_st0 C₁ hC₁ b₁ (Finset.mem_inter.mp hb₁).1)
      (hsub_st0 C₂ hC₂ b₂ (Finset.mem_inter.mp hb₂).1)
  calc ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
        (info.U_B (C, b)).countP deleteTag)
      ≤ (components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b => (S C b).card :=
        Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ =>
          ((hDyn C hC b).2.2.2.2.2.2.2.2.2.2 δ hδ).2.2.2.2.1
    _ = (components (D.G 0)).sum fun C => ((st₀.activeBuckets C).biUnion fun b => S C b).card :=
        Finset.sum_congr rfl fun C hC => (Finset.card_biUnion (hdisj_b C hC)).symm
    _ = ((components (D.G 0)).biUnion fun C => (st₀.activeBuckets C).biUnion fun b => S C b).card :=
        (Finset.card_biUnion hdisj_C).symm
    _ ≤ (batchDeletes (D.U (s₀ + δ + 1))).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ =>
          Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right)
    _ ≤ (D.U (s₀ + δ + 1)).length := batchDeletes_card_le _

/-- Under `hThresh`, the total number of splits received by any bucket spanner over any
non-restarted suffix `[s₀, t]` is at most `bundleSplitBudget k M`. -/
lemma epochBundleSeq_batchSplitCount_le_splitB
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N) (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀_rest : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {C : Finset ℕ} (hC : C ∈ components (D.G 0)) (b : ℤ) :
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let Us_ep : List (List Update) :=
      (List.range (t - s₀)).map fun r =>
        (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
    batchSplitCount Us_ep.flatten ≤ bundleSplitBudget k M := by
  intro st Us_ep
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀_rest hNoRest C hC b
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  set cs₀ := (initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).cs
  have hcs_r : ∀ r,
      (bundleRunSeqWith lsfInit L sparsify k M N D ord j r).1.cs =
        compLSFBatch cs₀ (dynBatches D r).flatten := fun r => by
    induction r with
    | zero => rfl
    | succ m ih =>
      rw [bundleRunSeqWith_cs, ih, dynBatches_succ, List.flatten_append, compLSFBatch_append,
        List.flatten_cons, List.flatten_nil, List.append_nil]
  have hR_le : ∀ r ≤ τ,
      ((((bundleRunSeqWith lsfInit L sparsify k M N D ord j r).1.cs.compSt C).R \
        (cs₀.compSt C).R).card : ℝ) ≤
      56 * ((∑ s ∈ Finset.Icc 1 r, (D.U s).length : ℕ) : ℝ) *
        (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by
    intro r
    induction r with
    | zero => intro _; dsimp only [bundleRunSeqWith, cs₀]; simp
    | succ m ih =>
      intro hm_le
      have hm_lt : m < τ := hm_le
      have hBm := hBun m hm_lt.le
      have hbase_m := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
        hV₀ j m).1
      have hI_m : CompLSFInv C_lsst (D.ℓ 0)
          (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs :=
        hbase_m.cs ▸ hBm.2.2.2.2.2.2.2.1
      have hG_m : (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.G = D.G m := by
        rw [← hbase_m.cs, hBm.2.2.2.2.2.2.2.2.1]
      have hG₀_m : (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.G₀ = D.G 0 := by
        rw [hcs_r m, compLSFBatch_G₀]; rfl
      have hDt := hD (m + 1) (Nat.succ_pos m) hm_le
      simp only [Nat.add_sub_cancel] at hDt
      have hBV : (bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.G.BatchIsValid
          (D.U (m + 1)) := by rw [hG_m]; exact hDt.1
      have hgrow := compLSFBatch_compSt_R_card_le hI_m hBV (hG₀_m ▸ hC)
      rw [hG₀_m, ← bundleRunSeqWith_cs] at hgrow
      have hS0 : (cs₀.compSt C).R ⊆
          ((bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.compSt C).R := by
        rw [← hbase_m.cs]; exact (hBm.2.2.2.2.2.2.2.2.2.2.2 C hC).1.hR_sub
      have hss : ((bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.compSt C).R ⊆
          ((bundleRunSeqWith lsfInit L sparsify k M N D ord j (m + 1)).1.cs.compSt C).R :=
        (compLSFBatch_compSt hI_m hBV (hG₀_m ▸ hC)).2.2.2.1
      have hdiff : ((((bundleRunSeqWith lsfInit L sparsify k M N D ord j (m + 1)).1.cs.compSt C).R \
            (cs₀.compSt C).R).card : ℝ) ≤
          ((((bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.compSt C).R \
            (cs₀.compSt C).R).card : ℝ) +
          ((((bundleRunSeqWith lsfInit L sparsify k M N D ord j (m + 1)).1.cs.compSt C).R.card : ℝ) -
            (((bundleRunSeqWith lsfInit L sparsify k M N D ord j m).1.cs.compSt C).R.card : ℝ)) := by
        have c1 := Finset.card_le_card hS0
        have c2 := Finset.card_le_card hss
        rw [Finset.card_sdiff_of_subset hS0, Finset.card_sdiff_of_subset (hS0.trans hss),
          Nat.cast_sub c1, Nat.cast_sub (c1.trans c2)]
        linarith
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp [Finset.mem_Icc]; omega
      rw [hIcc, Finset.sum_insert (by simp), Nat.cast_add]
      have hring : 56 * (((D.U (m + 1)).length : ℝ) +
          ((∑ x ∈ Finset.Icc 1 m, (D.U x).length : ℕ) : ℝ)) *
            (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 =
          56 * ((D.U (m + 1)).length : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 +
          56 * ((∑ x ∈ Finset.Icc 1 m, (D.U x).length : ℕ) : ℝ) *
            (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by ring
      have ih' := ih hm_lt.le
      linarith [hgrow, ih', hdiff, hring]
  have hRsub0 : (cs₀.compSt C).R ⊆ ((st 0).cs.compSt C).R := by
    have h0 := hSt_base 0 (Nat.zero_le _)
    have hB0 := hBun s₀ (le_trans hst htτ)
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
      hV₀ j s₀).1.cs
    dsimp only [st]
    rw [h0.cs, Nat.add_zero, ← hbp]
    exact (hB0.2.2.2.2.2.2.2.2.2.2.2 C hC).1.hR_sub
  have hRdiff_le : (((st (t - s₀)).cs.compSt C).R \ ((st 0).cs.compSt C).R).card ≤
      (((bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs.compSt C).R \
        (cs₀.compSt C).R).card := by
    have ht_eq := (hSt_base (t - s₀) le_rfl).cs
    rw [show s₀ + (t - s₀) = t by omega] at ht_eq
    dsimp only [st]
    rw [ht_eq]
    exact Finset.card_le_card (Finset.sdiff_subset_sdiff Finset.Subset.rfl hRsub0)
  have hlogN_pos : (0 : ℝ) < Real.log ((N : ℝ) + 2) := by linarith [half_lt_log_add_two N]
  have hlog_sq_le : (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith [half_lt_log_add_two (D.G 0).n])
      (Real.log_le_log (by positivity)
        (by linarith [show ((D.G 0).n : ℝ) ≤ (N : ℝ) from by exact_mod_cast hN])) 2
  have hlog2_pos : (0 : ℝ) < (Real.log ((N : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlogN_pos
  have hq_sub : ∑ s ∈ Finset.Icc 1 t, (D.U s).length ≤ ∑ s ∈ Finset.Icc 1 τ, (D.U s).length :=
    Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl htτ)
  have hR_bound : ((((bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs.compSt C).R \
      (cs₀.compSt C).R).card : ℝ) ≤ 56 * (M : ℝ) / (k : ℝ) := by
    have hr' := le_trans (hR_le t htτ) (mul_le_mul_of_nonneg_left hlog_sq_le (by positivity))
    have hq_r : ((∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N :=
      le_trans (by exact_mod_cast hq_sub) hThresh
    have h2 := mul_le_mul_of_nonneg_right (show 56 * ((∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) ≤
      56 * SparseCoreTool.updateThreshold k M N by linarith) hlog2_pos.le
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have heq : 56 * SparseCoreTool.updateThreshold k M N * (Real.log ((N : ℝ) + 2)) ^ 2 =
        56 * (M : ℝ) / (k : ℝ) := by
      rw [SparseCoreTool.updateThreshold]; field_simp [hlog2_pos.ne', hk_pos.ne']
    exact le_trans hr' (heq ▸ h2)
  have hceil : (((bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs.compSt C).R \
      (cs₀.compSt C).R).card ≤ Nat.ceil (56 * (M : ℝ) / (k : ℝ)) := by
    exact_mod_cast le_trans hR_bound (Nat.le_ceil _)
  have hsc : batchSplitCount Us_ep.flatten ≤
      2 * (((st (t - s₀)).cs.compSt C).R \ ((st 0).cs.compSt C).R).card :=
    hDyn.2.2.2.2.2.2.2.1
  unfold bundleSplitBudget
  omega

end MinCostFlow.Chain

end
