module

public import MinCostFlow.SparseCore.BundleRunInvBase

import MinCostFlow.SparseCore.BundleStage
import MinCostFlow.SparseCore.BundleInitCount
import Mathlib.Tactic.Positivity

/-!
# The run invariant of a branch on bundle graphs

`bundleRunSeq_inv` is the analogue of `treeRunSeq_inv` for `bundleRunSeq`. Along the run, the
sparsified core keeps its form (the spanners of the active bundle graphs, the extra edges of the
active components and the cross edges), each step moves it by the output batch, the number of
active components that are not large grows by at most two per update, and the spanner of every
bundle graph meets the bounds of Theorem 8.2 (page 26).

The proof follows the old one. The bundle stage of the run (`bundleRunSeq_stage_inv_stmt`) gives the
states of the LSF, the active components, the bundles and the spanner runs at every stage. The
bundle graph of each component and bucket is valid, has at most `M` edges, and receives only
deletions and splits, at most `bundleSplitBudget k M` splits in all, so Theorem 8.2 applies to its
spanner (`bundleBucket_theorem_8_2`). The form of the core follows by induction from
`stepBundleTree_stage_step`, and the length of each output batch from `stepBundleTree_US_len`.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- The run invariant of one branch on bundle graphs (the analogue of `treeRunSeq_inv`). -/
theorem bundleRunSeq_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) :
    let G₀ := D.G 0
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let st₀ := (run 0).1
    let actB : Finset ℕ → Finset ℤ := st₀.activeBuckets
    let splitB := bundleSplitBudget k M
    (∀ t ≤ τ,
      let st := (run t).1
      st.S_cur.IsValid ∧
      st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => st.extraEdges C) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur ∧
      st.activeComps ⊆ components G₀ ∧
      largeComps k G₀ ⊆ st.activeComps ∧
      (st.activeComps \ largeComps k G₀).card ≤ 2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        let Hb₀ := (st₀.bun (C, b)).graph
        let nMax_b := Hb₀.n + splitB
        let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
        (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
        Embedding.IsEmbedding (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
        (Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        Embedding.vcong (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            (Hb₀.maxDeg : ℝ))) ∧
    (∀ t, 1 ≤ t → t ≤ τ →
      let stPrev := (run (t - 1)).1
      let stCur := (run t).1
      let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j (t - 1)
      stPrev.S_cur.BatchIsValid info.U_S ∧
      stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
      (D.U t = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_B (C, b)) (sparsify M) ∧
        (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
        (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
        (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
        (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
        (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
          eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG))) ∧
      (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
        e ∉ info.D_total ∧ ∀ u ∈ D.U t, ¬ u.Inserts e) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U t).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, (stPrev.dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
        (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
        7 * (D.U t).length +
        2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        2 * info.D_total.card) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ, ∀ t ≤ τ,
      let Hb₀ := normGraph (st₀.bun (C, b)).graph
      let nMax_b := Hb₀.n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let initB := DynSpanner.init Hb₀ L (phaseBase nMax_b L) (sparsify M)
      let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
      let res_b : ℕ → StepOut L := fun s =>
        DynSpanner.runBatchStepOut (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s
      let batchTot_b : ℝ := ((Us_b.take t).flatten.length : ℝ)
      let encTot_b : ℝ := ∑ s ∈ Finset.range t,
        ((DynSpanner.runBatchState (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s).G.batchEnc
          ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) : ℝ)
      ((initB.state.H.m : ℝ) ≤ P_b.K_s * (Hb₀.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log ((Hb₀.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s) ∧
      ((initB.cost : ℝ) ≤ P_b.K_t * (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_t +
          (Hb₀.n : ℝ) + (Hb₀.m : ℝ) + (initB.state.H.m : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) ∧
      (∑ s ∈ Finset.range t, ((res_b s).UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
          Λ_s_b * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).cost : ℝ) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b * ((Hb₀.maxDeg : ℝ) + 1) *
          Λ_b * encTot_b)) := by
  classical
  intro G₀ run st₀ actB splitB
  have _ := hj
  have hstage := bundleRunSeq_stage_inv_stmt oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀
    hD hN hThresh ord hOrd j
  obtain ⟨hBase, hStep, hFlat⟩ := hstage
  have hrun0 : run 0 = (initBundleTree oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) (ord 0) j, []) :=
    rfl
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) st₀.cs := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hcs₀_G₀ : st₀.cs.G₀ = G₀ := rfl
  have hCov₀ : ∀ C ∈ components G₀,
      (st₀.cs.compSt C).W_init.biUnion (inducedEdges (st₀.cs.compSt C).RF.F) =
        (st₀.cs.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.2
  have hG₀_t : ∀ t ≤ τ, (run t).1.cs.G₀ = G₀ := fun t ht => by
    rw [(hBase t ht).2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  -- The bundle partition at every stage.
  have hPart : ∀ t ≤ τ, ∀ C ∈ components G₀, ∀ b : ℤ, ∀ e ∈ ((run t).1.bun (C, b)).edges,
      e ∈ (run t).1.cs.G.E \ (run t).1.cs.RF.F.E ∧
        (run t).1.cs.RF.root ((run t).1.cs.G.tail e) ∈ ((run t).1.cs.compSt C).R := by
    intro t ht C hC b e he
    obtain ⟨-, -, -, -, -, -, -, hI_t, hG_t, -, -, hC_t⟩ := hBase t ht
    obtain ⟨ρ, hρ⟩ := orderedUpTo_rot_at hOrd ht hG_t
    obtain ⟨hP, -, hpar, -⟩ := (hC_t C hC).2 b
    have hPt := hP ρ hI_t.hG_val (compLSF_RF_isRSF hI_t) hρ
    refine ⟨hPt.1 he, ?_⟩
    have hx : ((e, true) : End) ∈ edgeEnds ((run t).1.bun (C, b)).edges :=
      (mem_edgeEnds _ _).mpr he
    obtain ⟨hbv, hbp⟩ := hPt.2.2.1 _ hx
    have h := hpar _ hbv
    rw [hbp] at h
    exact h
  -- The initial bundle graphs.
  have hHbV : ∀ C ∈ components G₀, ∀ b : ℤ, (normGraph (st₀.bun (C, b)).graph).IsValid := fun C hC b => by
    obtain ⟨-, -, -, -, hV, -⟩ := ((hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
    exact hV
  have hHbm : ∀ C ∈ components G₀, ∀ b : ℤ, (normGraph (st₀.bun (C, b)).graph).m ≤ M := fun C hC b => by
    have hsub : (st₀.bun (C, b)).edges ⊆ G₀.E := fun e he =>
      (Finset.mem_sdiff.mp (hPart 0 (Nat.zero_le τ) C hC b e he).1).1
    exact (Finset.card_le_card hsub).trans hM
  have hlen_Us : ∀ C b, (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b).length = τ :=
    fun C b => by simp [bundleBatchList, bundleBatchListWith]
  have hT82 := fun C (hC : C ∈ components G₀) (b : ℤ) =>
    bundleBucket_theorem_8_2 (P_b := P_b) (splitB := splitB) (hHbV C hC b) hL (hHbm C hC b) hSp
      (hlen_Us C b) ((graphEq_batchIsValid (normGraph_graphEq _) _).mpr (hFlat C hC b).1)
      (hFlat C hC b).2.1 (hFlat C hC b).2.2.1
  -- Facts of the bundle stage at each stage.
  have hAB : ∀ t ≤ τ, (run t).1.activeBuckets = actB := fun t ht => (hBase t ht).2.2.2.2.1
  have hI : ∀ t ≤ τ, CompLSFInv C_lsst (D.ℓ 0) (run t).1.cs := fun t ht =>
    (hBase t ht).2.2.2.2.2.2.2.1
  have hAct : ∀ t ≤ τ, largeComps k G₀ ⊆ (run t).1.activeComps ∧
      (run t).1.activeComps ⊆ components G₀ := fun t ht => (hBase t ht).2.2.2.2.2.2.2.2.2.1
  have hUnt : ∀ t ≤ τ, ∀ C ∈ components G₀, C ∉ (run t).1.activeComps →
      (run t).1.cs.compSt C = st₀.cs.compSt C ∧ ∀ b : ℤ, (run t).1.bun (C, b) = st₀.bun (C, b) ∧
        (run t).1.dyn (C, b) = st₀.dyn (C, b) := fun t ht => (hBase t ht).2.2.2.2.2.2.2.2.2.2.1
  have hCt := fun t (ht : t ≤ τ) => (hBase t ht).2.2.2.2.2.2.2.2.2.2.2
  have hdynG : ∀ t ≤ τ, ∀ C ∈ components G₀, ∀ b : ℤ,
      GraphEq ((run t).1.dyn (C, b)).G ((run t).1.bun (C, b)).graph := fun t ht C hC b =>
    ((hCt t ht C hC).2 b).2.2.2.1
  have hdynrun : ∀ t ≤ τ, ∀ C ∈ components G₀, ∀ b : ℤ,
      (run t).1.dyn (C, b) = DynSpanner.runBatchState (normGraph (st₀.bun (C, b)).graph)
        (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)
        (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) t := fun t ht C hC b =>
    ((hCt t ht C hC).2 b).2.2.2.2.2
  have hStageDyn : ∀ t ≤ τ, ∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := (st₀.bun (C, b)).graph
      let nMax_b := Hb₀.n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let st := (run t).1
      (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
      ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
        (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
      ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
      Embedding.IsEmbedding (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
      (Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
          (Hb₀.maxDeg : ℝ) := by
    intro t ht C hC b
    dsimp only
    rw [hdynrun t ht C hC b]
    simpa only [normGraph_n, normGraph_m, normGraph_maxDeg] using (hT82 C hC b).2.2.1 t ht
  -- On an empty batch the bundle batches are empty and the bundles keep their edges.
  have hNil : ∀ s (hs : s < τ), D.U (s + 1) = [] → ∀ C ∈ components G₀, ∀ b : ℤ,
      (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b) = [] ∧
        ((run (s + 1)).1.bun (C, b)).edges = ((run s).1.bun (C, b)).edges := by
    intro s hs hUnil C hC b
    obtain ⟨-, hGeq, hds, hsc, -⟩ := (hStep s hs).2.2.2.2 C hC b
    have hcs : (run (s + 1)).1.cs = (run s).1.cs := by
      change compLSFBatch (run s).1.cs (D.U (s + 1)) = _
      rw [hUnil]; rfl
    have hdel := (hStep s hs).2.2.1 b
    rw [hUnil] at hdel
    have hdelC := (Finset.single_le_sum (f := fun C =>
      ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).countP deleteTag)
      (fun _ _ => Nat.zero_le _) hC).trans hdel
    have hsc' := hsc
    change _ ≤ 2 * (((run (s + 1)).1.cs.compSt C).R \ ((run s).1.cs.compSt C).R).card at hsc'
    rw [hcs, Finset.sdiff_self, Finset.card_empty] at hsc'
    have hnil := eq_nil_of_delOrSplit hds (by omega) (by simpa using hdelC)
    refine ⟨hnil, ?_⟩
    have h1 := (hdynG (s + 1) hs C hC b).2.1
    have h0 := (hdynG s hs.le C hC b).2.1
    change ((run (s + 1)).1.dyn (C, b)).G =
      ((run s).1.dyn (C, b)).G.applyBatch
        ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) at hGeq
    rw [hnil] at hGeq
    have hE := congrArg MGraph.E hGeq
    change ((run (s + 1)).1.dyn (C, b)).G.E = ((run s).1.dyn (C, b)).G.E at hE
    rw [h1, h0] at hE
    exact hE
  -- The rotations of the input along the run.
  have hRot := fun s (hs : s < τ) =>
    orderedUpTo_rot_step hOrd hs ((hBase s hs.le).2.2.2.2.2.2.2.2.1)
  choose ρs σs hρs hσs hrots using hRot
  have hSL := fun s (hs : s < τ) hVal hV hE hSub =>
    stepBundleTree_stage_step sparsify hI₀ hcs₀_G₀ hCov₀ (run s).1 (D.U (s + 1))
      (ord s) (ord (s + 1)) actB (hAB s hs.le) (hG₀_t s hs.le) (hI s hs.le) (hAct s hs.le).2
      (fun C hC => ((hCt s hs.le) C hC).1) (hStep s hs).1 (ρs s hs) (σs s hs) (hρs s hs)
      (hσs s hs) (hrots s hs) hVal hV hE hSub
      (fun C hC b _ => (hStageDyn (s + 1) hs C hC b).1.2.1)
      (fun C hC b _ => by
        change ((run (s + 1)).1.dyn (C, b)).G.E ⊆ ((run (s + 1)).1.bun (C, b)).edges
        rw [(hdynG (s + 1) hs C hC b).2.1]; exact Finset.Subset.rfl)
      (fun C hC b _ => hPart (s + 1) hs C hC b)
      (fun hUnil C hC b _ => hNil s hs hUnil C hC b)
      (fun hUnil C hC b => by
        change DynSpanner.update ((run s).1.dyn (C, b))
          ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b))
          (sparsify (run s).1.m₀) = _
        rw [(hNil s hs hUnil C hC b).1, update_nil])
  -- The form of the sparsified core along the run.
  have hS_stage : ∀ t ≤ τ,
      let st := (run t).1
      st.S_cur.IsValid ∧
      st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => st.extraEdges C) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur := by
    intro t
    induction t with
    | zero =>
      intro _
      dsimp only
      obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (rfl : G₀ = D.G 0)
      have hRF₀ := compLSF_RF_isRSF hI₀
      set E₀ := st₀.activeComps.biUnion fun C => (actB C).biUnion fun b => (st₀.dyn (C, b)).H.E
      have hS₀ : st₀.S_cur = MGraph.mk st₀.cs.RF.R E₀ (coreGraph G₀ st₀.cs.lsf).tail
          (coreGraph G₀ st₀.cs.lsf).head := rfl
      have hSub_E : E₀ ⊆ st₀.cs.G.E \ st₀.cs.RF.F.E := by
        intro e he
        simp only [E₀, Finset.mem_biUnion] at he
        obtain ⟨C, hCA, b, _, heb⟩ := he
        have hC : C ∈ components G₀ := largeComps_sub hCA
        have heG := (hStageDyn 0 (Nat.zero_le τ) C hC b).1.2.1 heb
        rw [(hdynG 0 (Nat.zero_le τ) C hC b).2.1] at heG
        exact (hPart 0 (Nat.zero_le τ) C hC b e heG).1
      have hEx : (st₀.activeComps.biUnion fun C => st₀.extraEdges C) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rw [Finset.mem_biUnion] at he
        obtain ⟨C, hCA, heC⟩ := he
        have h0 := initBundleTree_extraEdges oracle L sparsify hLSST M N hk hG₀ hV₀ hℓ₀ j hρ₀
          (largeComps_sub hCA)
        change e ∈ (initBundleTree oracle C_lsst L sparsify k M N G₀ (D.ℓ 0) (ord 0) j).extraEdges C
          at heC
        rw [h0] at heC
        exact Finset.notMem_empty e heC
      have hX : st₀.cs.crossEdges = ∅ := rfl
      refine ⟨?_, rfl, ?_, ?_⟩
      · rw [hS₀]
        intro e he
        have heG := (Finset.mem_sdiff.mp (hSub_E he)).1
        have hth := hI₀.hG_val e heG
        exact ⟨(rootedForest_root_spec hRF₀ hth.1).1, (rootedForest_root_spec hRF₀ hth.2).1⟩
      · rw [hEx, hX, Finset.union_empty, Finset.union_empty]
        rfl
      · rw [hS₀]
        exact ⟨Finset.Subset.rfl, hSub_E, fun e _ => ⟨rfl, rfl⟩⟩
    | succ s ih =>
      intro hs_le
      obtain ⟨hVal_s, hV_s, hE_s, hSub_s⟩ := ih (Nat.le_of_succ_le hs_le)
      have hsp := hSL s hs_le hVal_s hV_s hE_s hSub_s
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1⟩
  -- The spanner step of each bundle graph.
  have hStepB : ∀ s (hs : s < τ), ∀ C ∈ components G₀, ∀ b : ℤ,
      let stPrev := (run s).1
      let stCur := (run (s + 1)).1
      let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j s
      info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_B (C, b)) (sparsify M) ∧
      (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
      (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
      (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
      (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
      (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
        eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
        eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG)) := by
    intro s hs C hC b
    dsimp only
    have hm₀ : (run s).1.m₀ = M := (hBase s hs.le).2.1
    have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs
    have hs82 := (hT82 C hC b).2.2.2.1 s hs _ hget
    have hres_eq : DynSpanner.runBatchStepOut (normGraph (st₀.bun (C, b)).graph)
        (phaseBase ((normGraph (st₀.bun (C, b)).graph).n + splitB) L) (sparsify M)
        (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) s =
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b) := by
      unfold DynSpanner.runBatchStepOut
      rw [hget]
      change DynSpanner.update
        (DynSpanner.runBatchState (normGraph (st₀.bun (C, b)).graph)
          (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)
          (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) s) _ _ = _
      rw [← hdynrun s hs.le C hC b]
      change _ = DynSpanner.update ((run s).1.dyn (C, b))
        ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b))
        (sparsify (run s).1.m₀)
      rw [hm₀]
    dsimp only at hs82
    rw [hres_eq] at hs82
    refine ⟨by
        change DynSpanner.update _ _ (sparsify (run s).1.m₀) = _
        rw [hm₀]
        rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hdynrun s hs.le C hC b]; exact hs82.2.2.1
    · rw [hdynrun s hs.le C hC b, hdynrun (s + 1) hs C hC b]; exact hs82.2.2.2.1
    · rw [hdynrun (s + 1) hs C hC b]; exact hs82.2.2.2.2.1
    · intro eG heG eH heH hnD
      rw [hdynrun (s + 1) hs C hC b] at heG heH
      rw [hdynrun s hs.le C hC b]
      exact hs82.2.2.2.2.2 eG heG eH heH hnD
  -- The number of active components that are not large.
  have hAct_diff_card : ∀ t ≤ τ, ((run t).1.activeComps \ largeComps k G₀).card ≤
      2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) := by
    intro t
    induction t with
    | zero =>
      intro _
      change (largeComps k G₀ \ largeComps k G₀).card ≤ _
      rw [Finset.sdiff_self, Finset.card_empty]
      exact Nat.zero_le _
    | succ s ih =>
      intro hs_le
      have hss := (hStep s hs_le).2.1
      have ih' := ih (Nat.le_of_succ_le hs_le)
      have hsub : (run (s + 1)).1.activeComps \ largeComps k G₀ ⊆
          ((run s).1.activeComps \ largeComps k G₀) ∪
            (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive := by
        intro C hC
        rw [Finset.mem_sdiff] at hC
        rw [hss.2.2.1, Finset.mem_union] at hC
        rw [Finset.mem_union]
        rcases hC with ⟨h1 | h2, hNL⟩
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨h1, hNL⟩)
        · exact Or.inr h2
      have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
        ext x; simp [Finset.mem_Icc]; omega
      calc ((run (s + 1)).1.activeComps \ largeComps k G₀).card
          ≤ (((run s).1.activeComps \ largeComps k G₀) ∪
              (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive).card :=
            Finset.card_le_card hsub
        _ ≤ ((run s).1.activeComps \ largeComps k G₀).card +
              (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive.card :=
            Finset.card_union_le _ _
        _ ≤ 2 * (Finset.Icc 1 s).sum (fun i => (D.U i).length) + 2 * (D.U (s + 1)).length :=
            Nat.add_le_add ih' hss.2.2.2
        _ = 2 * (Finset.Icc 1 (s + 1)).sum (fun i => (D.U i).length) := by
            rw [hIcc, Finset.sum_insert (by simp)]; omega
  -- Small components have small initial bundle graphs.
  have hSmall : ∀ C ∈ components G₀, C ∉ largeComps k G₀ → ∀ b : ℤ,
      (st₀.bun (C, b)).vertices.card ≤ 11 :=
    (initBundleTree_vertex_sum_le_stmt oracle C_lsst L sparsify hLSST k M N hk G₀ hG₀ hV₀ (D.ℓ 0) hℓ₀
      (ord 0) j ((components G₀).sum fun C => (actB C).card)
      (fun C hC => Finset.single_le_sum (f := fun C => (actB C).card)
        (fun _ _ => Nat.zero_le _) hC)).2.1
  refine ⟨fun t ht => ?_, fun t ht1 htτ => ?_, fun C hC b t ht => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hS_stage t ht
    refine ⟨h1, h2, h3, h4, (hAct t ht).2, (hAct t ht).1, hAct_diff_card t ht,
      fun C hC b => hStageDyn t ht C hC b⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    simp only [Nat.add_sub_cancel]
    have hs : s < τ := htτ
    obtain ⟨hVal_s, hV_s, hE_s, hSub_s⟩ := hS_stage s hs.le
    have hsp := hSL s hs hVal_s hV_s hE_s hSub_s
    have hss := (hStep s hs).2.1
    have hNew_sub : (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive ⊆
        components G₀ \ largeComps k G₀ := by
      intro C hC
      have hC1 : C ∈ (run (s + 1)).1.activeComps := by
        rw [hss.2.2.1]; exact Finset.mem_union_right _ hC
      have hna : C ∉ (run s).1.activeComps := by
        rw [hss.1, Finset.mem_sdiff] at hC; exact hC.2
      exact Finset.mem_sdiff.mpr ⟨(hAct (s + 1) hs).2 hC1, fun hL => hna ((hAct s hs.le).1 hL)⟩
    have hNew_n : ∀ C ∈ (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive,
        ∀ b : ℤ, ((run s).1.dyn (C, b)).G.n ≤ 11 := by
      intro C hC b
      have hC_comp := (Finset.mem_sdiff.mp (hNew_sub hC)).1
      have hNL := (Finset.mem_sdiff.mp (hNew_sub hC)).2
      have hna : C ∉ (run s).1.activeComps := by
        rw [hss.1, Finset.mem_sdiff] at hC; exact hC.2
      rw [((hUnt s hs.le C hC_comp hna).2 b).2, graphEq_n (hdynG 0 (Nat.zero_le τ) C hC_comp b)]
      exact hSmall C hC_comp hNL b
    have hUntEx : ∀ C ∈ components G₀, C ∉ (run s).1.activeComps → (run s).1.extraEdges C = ∅ := by
      intro C hC hna
      obtain ⟨hcsC, hbunC⟩ := hUnt s hs.le C hC hna
      obtain ⟨ρ₀, hρ₀⟩ := orderedUpTo_rot_at hOrd (Nat.zero_le τ) (rfl : G₀ = D.G 0)
      have h0 := initBundleTree_extraEdges oracle L sparsify hLSST M N hk hG₀ hV₀ hℓ₀ j hρ₀ hC
      have heq : (run s).1.extraEdges C = st₀.extraEdges C := by
        unfold BundleTreeState.extraEdges
        rw [hcsC, hAB s hs.le]
        congr 1
        exact Finset.biUnion_congr rfl fun b _ => by rw [(hbunC b).1]
      rw [heq]
      exact h0
    have hLen := stepBundleTree_US_len sparsify (run s).1 (D.U (s + 1)) (ord s) (ord (s + 1)) actB
      (hAB s hs.le) (hG₀_t s hs.le) (hI s hs.le) (hAct s hs.le).2 hUntEx (hStep s hs).1 hE_s
      hsp.2.2.1 hsp.2.2.2.2.2.2.2.2
      (fun C hC' b _ => (hStepB s hs C ((hAct (s + 1) hs).2 hC') b).2.2.2.1)
      (fun C hC b _ => by
        obtain ⟨-, hGeq, hds, -, hdel⟩ := (hStep s hs).2.2.2.2 C hC b
        refine ⟨?_, hdel⟩
        change ((run (s + 1)).1.bun (C, b)).edges ⊆ ((run s).1.bun (C, b)).edges
        have h1 := (hdynG (s + 1) hs C hC b).2.1
        have h0 := (hdynG s hs.le C hC b).2.1
        change ((run (s + 1)).1.dyn (C, b)).G = ((run s).1.dyn (C, b)).G.applyBatch
          ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) at hGeq
        have hE := congrArg MGraph.E hGeq
        rw [h1] at hE
        change ((run (s + 1)).1.bun (C, b)).edges = _ at hE
        rw [hE]
        exact (applyBatch_E_subset_of_delOrSplit _ _ hds).trans (by rw [h0]; exact Finset.Subset.rfl))
    exact ⟨hsp.2.2.2.2.1, hsp.2.2.2.2.2.1, hsp.2.2.2.2.2.2.1, hStepB s hs, hsp.2.2.2.2.2.2.2.1,
      hNew_sub, hss.2.2.2, hNew_n, hLen⟩
  · have hm0 := (hT82 C hC b).1
    have h0 := (hT82 C hC b).2.1
    have hc := (hT82 C hC b).2.2.2.2 t ht
    refine ⟨hm0, h0, hc.1, hc.2.1, ?_⟩
    refine le_trans hc.2.2 ?_
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · refine Finset.sum_le_sum fun s hs => ?_
      have hs_lt : s < τ := lt_of_lt_of_le (Finset.mem_range.mp hs) ht
      have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs_lt
      rw [hget]
    · have hK_t := P_b.hK_t
      have hK_s := P_b.hK_s
      have hγc := P_b.hγ_c
      have hγl := P_b.hγ_ℓ
      have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      have hnm_ge : (1 : ℝ) ≤ ((st₀.bun (C, b)).graph.n + splitB : ℕ) +
          ((st₀.bun (C, b)).graph.m : ℝ) + 2 := by linarith
      have hΛ_nn : 0 ≤ (1 + Real.log (((st₀.bun (C, b)).graph.n + splitB : ℕ) +
          ((st₀.bun (C, b)).graph.m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t :=
        pow_nonneg (by linarith [Real.log_nonneg hnm_ge]) _
      positivity

end MinCostFlow.SparseCore
