module

public import MinCostFlow.SparseCore.BundleSpannerSize
public import MinCostFlow.SparseCore.BundleRunInv
import MinCostFlow.SparseCore.BundleStage
import MinCostFlow.SparseCore.SparseCoreRunBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sparsified core theorem on bundle graphs (`bundleRunSeq_isSparsifiedCoreGraph`)

Proves the six clauses of `IsSparsifiedCoreGraph` for `bundleRunSeq` across all stages `t ≤ τ`
(paper Lemma 5.17, pages 23–24):
1. Subgraph `(coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur`.
2. Embedding `st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur` via `BundleState.parent`
   and `BundleState.project_edge`.
3. Length approximation `approx2` along every embedded walk.
4. Embedding length bound `≤ coreE82Len L P_b`.
5. Edge congestion bound `≤ 1 + coreE82Cong L P_b * k` (using the bundle degree cap `≤ k`,
   free of any input graph degree).
6. Sparsity bound `st.S_cur.E.card ≤ bundleSizeFactor L P_b M B_bound * M / k`.

Uses `bundleRunSeq_inv`, `bundleRunSeq_stage_inv_stmt`, and `bundleCompStep_edges_eq`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-- **Sparsified core metrics for `bundleRunSeq`** (paper Definition 5.7 and Lemma 5.17, pages 19
and 23–24). The congestion factor uses the bundle cap `k` in place of any graph degree, and the size
factor `bundleSizeFactor` is free of degrees. -/
theorem bundleRunSeq_isSparsifiedCoreGraph
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) :
    let G₀ := D.G 0
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let actB : Finset ℕ → Finset ℤ := (run 0).1.activeBuckets
    ∀ t ≤ τ,
      let st := (run t).1
      (coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur ∧
      st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur ∧
      (∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
        approx2 (coreLen st.cs.lsf (D.ℓ t) e) (coreLen st.cs.lsf (D.ℓ t) e')) ∧
      (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
      st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b * (k : ℝ) ∧
      (∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
        (st.S_cur.E.card : ℝ) ≤ bundleSizeFactor L P_b M B_bound * (M : ℝ) / (k : ℝ)) := by
  classical
  intro G₀ run actB t ht st
  have hℓ₀ : ∀ e ∈ G₀.E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ (D.ℓ 0) e := fun e he => by
    rw [safeLen_eq_of_mem (D.ℓ 0) he]; exact hℓ₀ e he
  let st₀ := (run 0).1
  let cs₀ := st₀.cs
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hCompG : ∀ C' ∈ components G₀, (cs₀.compSt C').G = compGraph G₀ C' :=
    fun C' hC' => (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC').2.1
  obtain ⟨hStageBase, hStageStep, hStageFlat⟩ :=
    bundleRunSeq_stage_inv_stmt oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨hRunStage, _, _⟩ :=
    bundleRunSeq_inv
      oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj
  have hbt := hStageBase t ht
  have hrt := hRunStage t ht
  have hActB_t : st.activeBuckets = actB := hbt.2.2.2.2.1
  have hcs_t : st.cs = compLSFBatch cs₀ (dynBatches D t).flatten := hbt.2.2.2.2.2.2.1
  have hI_t : CompLSFInv C_lsst (D.ℓ 0) st.cs := hbt.2.2.2.2.2.2.2.1
  have hG_t : st.cs.G = D.G t := hbt.2.2.2.2.2.2.2.2.1
  have hcs_G₀ : st.cs.G₀ = G₀ := by rw [hcs_t, compLSFBatch_G₀]; rfl
  have hLarge_sub : largeComps k G₀ ⊆ st.activeComps := hbt.2.2.2.2.2.2.2.2.2.1.1
  have hAct_sub : st.activeComps ⊆ components G₀ := hbt.2.2.2.2.2.2.2.2.2.1.2
  have hUnt := hbt.2.2.2.2.2.2.2.2.2.2.1
  have hC_stage := hbt.2.2.2.2.2.2.2.2.2.2.2
  have hS_V : st.S_cur.V = st.cs.RF.R := hrt.2.1
  have hS_E : st.S_cur.E =
      (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
        (st.activeComps.biUnion fun C => st.extraEdges C) ∪
        st.cs.crossEdges := hrt.2.2.1
  have hS_sub : (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur := hrt.2.2.2.1
  have hSmallAct : (st.activeComps \ largeComps k G₀).card ≤
      2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) := hrt.2.2.2.2.2.2.1
  have hDynSp := hrt.2.2.2.2.2.2.2
  obtain ⟨ρ_all, hρ_ord, hρ_batch⟩ := hOrd
  have hBunSpec : ∀ C ∈ components G₀, ∀ b : ℤ,
      (st.bun (C, b)).edges =
        (st₀.bun (C, b)).edges \ (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)) ∧
      Disjoint (st.bun (C, b)).edges st.cs.insertedGlobal := by
    intro C hC b
    exact bundleRunSeq_bun_edges_spec oracle C_lsst L sparsify ⟨ρ_all, hρ_ord, hρ_batch⟩ j hC b
      (fun hR _ _ => bundleCompStep_edges_eq hR)
      (fun s hs =>
        have hbs := hStageBase s hs
        have hCs := hbs.2.2.2.2.2.2.2.2.2.2.2 C hC
        ⟨hbs.1, hbs.2.2.2.2.2.2.2.1, hbs.2.2.2.2.2.2.2.2.1, (hCs.2 b).1, (hCs.2 b).2.2.1⟩)
      (fun s hs => (hStageStep s hs).1) t ht
  have hBun_edge_props : ∀ C ∈ components G₀, ∀ b : ℤ, ∀ e ∈ (st.bun (C, b)).edges,
      e ∈ compEdgeSet G₀ C ∧ e ∈ G₀.E ∧ st₀.origBucket e = b ∧
        e ∉ st.cs.insertedGlobal ∧ e ∉ st.cs.crossEdges := by
    intro C hC b e he
    have he0 : e ∈ (st₀.bun (C, b)).edges := ((hC_stage C hC).2 b).2.1 he
    have hsub0 : (st₀.bun (C, b)).edges ⊆
        bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b :=
      initBundleFor_edges_subset _ _ _ _
    have hbc := bucketCoreEdges_props hI₀ rfl hCompG st₀.origBucket hC b (hsub0 he0)
    have heG0 : e ∈ G₀.E := (Finset.mem_filter.mp hbc.1).1
    have hni : e ∉ st.cs.insertedGlobal := Finset.disjoint_left.mp (hBunSpec C hC b).2 he
    have hnc : e ∉ st.cs.crossEdges := fun hc => hni (hI_t.hCross_sub hc)
    exact ⟨hbc.1, heG0, hbc.2.2.2.2, hni, hnc⟩
  have hPart_t : ∀ C ∈ components G₀, ∀ b : ℤ,
      (st.bun (C, b)).IsPartition
        (coreRotation (L := st.cs.lsf) (hG_t.symm ▸ ρ_all t) hI_t.hG_val (compLSF_RF_isRSF hI_t)) k :=
    fun C hC b => ((hC_stage C hC).2 b).1 (hG_t.symm ▸ ρ_all t) hI_t.hG_val (compLSF_RF_isRSF hI_t)
      ((rotation_cast_order hG_t.symm (ρ_all t)).trans (hρ_ord t ht))
  -- Clause 1: Subgraph
  have hSub : (coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur := by
    rw [← hG_t]; exact hS_sub
  -- Clause 2: Embedding
  have hEmb : st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur := by
    refine ⟨?_, fun e he => ?_⟩
    · change st.cs.RF.R ⊆ st.S_cur.V
      rw [hS_V]
    · by_cases heS : e ∈ st.S_cur.E
      · have hemb : st.emb e = [(e, true)] := by unfold BundleTreeState.emb; simp [heS]
        rw [hemb]
        have hEnd := hSub.2.2 e heS
        exact MGraph.IsWalk.cons heS (by simp [MGraph.src, hEnd.1])
          (by simpa [MGraph.dst, hEnd.2] using MGraph.IsWalk.nil _)
      · by_cases hp : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
            e ∈ (st.bun p).edges
        · set p := hp.choose
          have hpA : p.1 ∈ st.activeComps := hp.choose_spec.1
          have hpC : p.1 ∈ components G₀ := hAct_sub hpA
          have hpb : p.2 ∈ actB p.1 := hActB_t ▸ hp.choose_spec.2.1
          have hep : e ∈ (st.bun p).edges := hp.choose_spec.2.2
          have hemb : st.emb e = piTotal (st.dyn p) e := by
            unfold BundleTreeState.emb; simp [heS, hp, p]
          rw [hemb]
          have hGeq_p : GraphEq (st.dyn p).G (st.bun p).graph := ((hC_stage p.1 hpC).2 p.2).2.2.2.1
          have hSp_p := hDynSp p.1 hpC p.2
          have heGp : e ∈ (st.dyn p).G.E := by rw [hGeq_p.2.1]; exact hep
          have hw_p : (st.dyn p).H.IsWalk ((st.dyn p).G.tail e) ((st.dyn p).G.head e)
              (piTotal (st.dyn p) e) := hSp_p.2.2.2.1.2 e heGp
          have hPart_p := hPart_t p.1 hpC p.2
          have hw_lift := isWalk_map (st.bun p).parent (fun e' he' => by
            have he'G : e' ∈ (st.dyn p).G.E := hSp_p.1.2.1 he'
            have he'B : e' ∈ (st.bun p).edges := by rwa [hGeq_p.2.1] at he'G
            have he'S : e' ∈ st.S_cur.E := by
              rw [hS_E]
              exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_biUnion.mpr ⟨p.1, hpA, Finset.mem_biUnion.mpr ⟨p.2, hpb, he'⟩⟩))
            have hProj' := BundleState.project_edge hPart_p he'B
            have hSubH' := hSp_p.1.2.2 e' he'
            have hSubS' := hS_sub.2.2 e' he'S
            have hEnds' := hGeq_p.2.2 e' he'G
            have htail : (st.bun p).parent ((st.dyn p).H.tail e') = st.S_cur.tail e' := by
              rw [hSubH'.1, hEnds'.1, hProj'.2.1, hSubS'.1]
            have hhead : (st.bun p).parent ((st.dyn p).H.head e') = st.S_cur.head e' := by
              rw [hSubH'.2, hEnds'.2, hProj'.2.2, hSubS'.2]
            exact ⟨he'S, htail, hhead⟩) hw_p
          have hProj := BundleState.project_edge hPart_p hep
          have hEnds := hGeq_p.2.2 e heGp
          have htail_e : (st.bun p).parent ((st.dyn p).G.tail e) =
              (coreGraph (D.G t) st.cs.lsf).tail e := by
            rw [hEnds.1, hProj.2.1, hG_t]
          have hhead_e : (st.bun p).parent ((st.dyn p).G.head e) =
              (coreGraph (D.G t) st.cs.lsf).head e := by
            rw [hEnds.2, hProj.2.2, hG_t]
          rwa [htail_e, hhead_e] at hw_lift
        · have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
          rw [hemb]
          have he_nc : e ∉ st.cs.crossEdges := fun hc => heS (by
            rw [hS_E]; exact Finset.mem_union_right _ hc)
          have he_G : e ∈ st.cs.G.E := by rw [hG_t]; exact (Finset.mem_sdiff.mp he).1
          obtain ⟨C, hC_G0, heC⟩ := hI_t.hEdge_cover e he_G he_nc
          have hC : C ∈ components G₀ := hcs_G₀ ▸ hC_G0
          have hna : C ∉ st.activeComps := by
            intro hCA
            have hnF : e ∉ (st.cs.compSt C).RF.F.E := fun heF =>
              (Finset.mem_sdiff.mp he).2 (Finset.mem_biUnion.mpr ⟨C, hC_G0, heF⟩)
            have hnB : e ∉ (st.activeBuckets C).biUnion (fun b => (st.bun (C, b)).edges) := by
              intro hm
              rw [Finset.mem_biUnion] at hm
              rcases hm with ⟨b, hb, heb⟩
              exact hp ⟨(C, b), hCA, hb, heb⟩
            exact heS (by
              rw [hS_E]
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨C, hCA,
                  Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heC, hnF⟩, hnB⟩⟩)))
          have hNL : C ∉ largeComps k G₀ := fun hL' => hna (hLarge_sub hL')
          have hcs_u := (hUnt C hC hna).1
          have hlt : 4 * (compGraph G₀ C).m < k := by
            by_contra hge
            push Not at hge
            have hm1 : 1 ≤ (compGraph G₀ C).m := by
              have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge; omega
            exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
          have hsm := initLSF_small_props hLSST hG₀ hℓs hk hC hlt j
          have he_ends := hI_t.hNonCross_ends C hC_G0 e heC he_nc
          have heC₀ : e ∈ (compGraph G₀ C).E := by rw [← hCompG C hC, ← hcs_u]; exact heC
          have hroot₀ := hsm.2.2.2 e heC₀
          have hCI_C := (hI_t.hCompLSF C hC_G0).1
          have htV := (hCI_C.hG_val e heC).1
          have hhV := (hCI_C.hG_val e heC).2
          have hrt : st.cs.RF.root (st.cs.G.tail e) = st.cs.RF.root (st.cs.G.head e) := by
            rw [← he_ends.1, ← he_ends.2, compLSF_RF_root_eq hI_t hC_G0 htV,
              compLSF_RF_root_eq hI_t hC_G0 hhV, hcs_u, hCompG C hC]
            exact hroot₀
          have hth_eq : (coreGraph (D.G t) st.cs.lsf).tail e =
              (coreGraph (D.G t) st.cs.lsf).head e := by
            dsimp only [coreGraph]; rw [← hG_t]; exact hrt
          rw [hth_eq]
          exact MGraph.IsWalk.nil _
  -- Clause 3: approx2
  have hApprox : ∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ t) e) (coreLen st.cs.lsf (D.ℓ t) e') := by
    intro e he e' he'
    have hwstr_ge1 : ∀ x ∈ (D.G t).E, 1 ≤ st.cs.lsf.wstr x := by
      intro x hx
      have hℓt : ∀ y ∈ st.cs.G.E, 0 < D.ℓ t y := hG_t ▸ hℓ t ht
      have hℓo : ∀ y ∈ st.cs.G₀.E, y ∈ st.cs.G.E → y ∉ st.cs.insertedGlobal →
          D.ℓ t y = D.ℓ 0 y := by
        intro y _ hy hni
        rw [hG_t] at hy
        rw [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at hni
        exact length_eq_init_of_not_batchesInserted hD hLen t ht y hy hni
      have hH := hI_t.to_Holds hℓt hℓo
      have hHw : st.cs.RF.stretch (D.G t) (D.ℓ t) x ≤ st.cs.lsf.wstr x := by
        have htmp := (hH.2.2.2 x (hG_t.symm ▸ hx)).1
        change st.cs.RF.stretch st.cs.G (D.ℓ t) x ≤ st.cs.lsf.wstr x at htmp
        rwa [hG_t] at htmp
      exact (one_le_stretch (hG_t ▸ (compLSF_RF_isRSF hI_t).2.2.2.2)
        (fun y hy => le_of_lt (hℓ t ht y hy)) hx).trans hHw
    have hcore_pos : ∀ x ∈ (D.G t).E, 0 < coreLen st.cs.lsf (D.ℓ t) x :=
      fun x hx => mul_pos (lt_of_lt_of_le zero_lt_one (hwstr_ge1 x hx)) (hℓ t ht x hx)
    by_cases heS : e ∈ st.S_cur.E
    · have hemb : st.emb e = [(e, true)] := by unfold BundleTreeState.emb; simp [heS]
      rw [hemb, walkEdges] at he'
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.mem_singleton] at he'
      rw [he']
      have hp := hcore_pos e (Finset.mem_sdiff.mp he).1
      exact ⟨hp, hp, by linarith, by linarith⟩
    · by_cases hp : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
          e ∈ (st.bun p).edges
      · set p := hp.choose
        have hpC : p.1 ∈ components G₀ := hAct_sub hp.choose_spec.1
        have hep : e ∈ (st.bun p).edges := hp.choose_spec.2.2
        have hemb : st.emb e = piTotal (st.dyn p) e := by
          unfold BundleTreeState.emb; simp [heS, hp, p]
        rw [hemb] at he'
        have hGeq_p : GraphEq (st.dyn p).G (st.bun p).graph := ((hC_stage p.1 hpC).2 p.2).2.2.2.1
        have hSp_p := hDynSp p.1 hpC p.2
        have heGp : e ∈ (st.dyn p).G.E := by rw [hGeq_p.2.1]; exact hep
        have he'_H : e' ∈ (st.dyn p).H.E := walkEdges_subset_of_isWalk (hSp_p.2.2.2.1.2 e heGp) he'
        have he'_B : e' ∈ (st.bun p).edges := by
          change e' ∈ (st.bun p).graph.E; rw [← hGeq_p.2.1]; exact hSp_p.1.2.1 he'_H
        obtain ⟨_, heG0, hb_e, he_niG, _⟩ := hBun_edge_props p.1 hpC p.2 e hep
        obtain ⟨_, he'G0, hb_e', he'_niG, _⟩ := hBun_edge_props p.1 hpC p.2 e' he'_B
        have he_ni : e ∉ batchesInserted (dynBatches D t) := by
          rwa [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he_niG
        have he'_ni : e' ∉ batchesInserted (dynBatches D t) := by
          rwa [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he'_niG
        have he_Dt : e ∈ (D.G t).E := (Finset.mem_sdiff.mp he).1
        have he'_Dt : e' ∈ (D.G t).E := by
          have h1 : e' ∈ (coreGraph st.cs.G st.cs.lsf).E := (hPart_t p.1 hpC p.2).1 he'_B
          rw [hG_t] at h1
          exact (Finset.mem_sdiff.mp h1).1
        have hℓ_e : D.ℓ t e = D.ℓ 0 e :=
          length_eq_init_of_not_batchesInserted hD hLen t ht e he_Dt he_ni
        have hℓ_e' : D.ℓ t e' = D.ℓ 0 e' :=
          length_eq_init_of_not_batchesInserted hD hLen t ht e' he'_Dt he'_ni
        have hw_e : st.cs.lsf.wstr e = cs₀.lsf.wstr e := by
          change st.cs.wstrGlobal e = cs₀.wstrGlobal e
          rw [hcs_t]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D t).flatten
            (by rw [← hcs_t, hG_t]; exact he_Dt) (by rwa [← hcs_t])
        have hw_e' : st.cs.lsf.wstr e' = cs₀.lsf.wstr e' := by
          change st.cs.wstrGlobal e' = cs₀.wstrGlobal e'
          rw [hcs_t]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D t).flatten
            (by rw [← hcs_t, hG_t]; exact he'_Dt) (by rwa [← hcs_t])
        have hlen_e : coreLen st.cs.lsf (D.ℓ t) e = coreLen cs₀.lsf (D.ℓ 0) e := by
          unfold coreLen; rw [hw_e, hℓ_e]
        have hlen_e' : coreLen st.cs.lsf (D.ℓ t) e' = coreLen cs₀.lsf (D.ℓ 0) e' := by
          unfold coreLen; rw [hw_e', hℓ_e']
        have hbk_eq : bucketOf (coreLen cs₀.lsf (D.ℓ 0) e) = bucketOf (coreLen cs₀.lsf (D.ℓ 0) e') := by
          have h1 : st₀.origBucket e = bucketOf (coreLen cs₀.lsf (D.ℓ 0) e) := by
            change bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e) = _
            rw [coreLen, coreLen, safeLen_eq_of_mem (D.ℓ 0) heG0]
          have h2 : st₀.origBucket e' = bucketOf (coreLen cs₀.lsf (D.ℓ 0) e') := by
            change bucketOf (coreLen cs₀.lsf (safeLen G₀ (D.ℓ 0)) e') = _
            rw [coreLen, coreLen, safeLen_eq_of_mem (D.ℓ 0) he'G0]
          rw [← h1, ← h2, hb_e, hb_e']
        rw [hlen_e, hlen_e']
        exact approx2_of_bucketOf_eq (hlen_e ▸ hcore_pos e he_Dt)
          (hlen_e' ▸ hcore_pos e' he'_Dt) hbk_eq
      · have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
        rw [hemb, walkEdges] at he'
        simp at he'
  -- Clause 4: Embedding length
  have hLenEmb : (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b := by
    have h1 : (1 : ℝ) ≤ coreE82Len L P_b := by
      unfold coreE82Len
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
      have hγ := one_le_pow₀ P_b.hγ_ℓ (n := L + 1)
      nlinarith
    have hnat : ∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ((st.emb e).length : ℝ) ≤ coreE82Len L P_b := by
      intro e _
      by_cases heS : e ∈ st.S_cur.E
      · have hemb : st.emb e = [(e, true)] := by unfold BundleTreeState.emb; simp [heS]
        rw [hemb]; simpa using h1
      · by_cases hp : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
            e ∈ (st.bun p).edges
        · set p := hp.choose
          have hpC : p.1 ∈ components G₀ := hAct_sub hp.choose_spec.1
          have hemb : st.emb e = piTotal (st.dyn p) e := by
            unfold BundleTreeState.emb; simp [heS, hp, p]
          rw [hemb]
          have hGeq_p : GraphEq (st.dyn p).G (st.bun p).graph := ((hC_stage p.1 hpC).2 p.2).2.2.2.1
          have heGp : e ∈ (st.dyn p).G.E := by rw [hGeq_p.2.1]; exact hp.choose_spec.2.2
          have hle_sup : (piTotal (st.dyn p) e).length ≤
              Embedding.length (piTotal (st.dyn p)) (st.dyn p).G :=
            Finset.le_sup (f := fun x => (piTotal (st.dyn p) x).length) heGp
          exact le_trans (by exact_mod_cast hle_sup) (hDynSp p.1 hpC p.2).2.2.2.2.1
        · have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
          rw [hemb]; simp only [List.length_nil, Nat.cast_zero]; linarith
    by_cases hne : (coreGraph (D.G t) st.cs.lsf).E.Nonempty
    · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup _ hne (fun e => (st.emb e).length)
      change (((coreGraph (D.G t) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [heq]; exact hnat e he
    · change (((coreGraph (D.G t) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sup_empty, bot_eq_zero', Nat.cast_zero]
      linarith
  -- Clause 5: Edge congestion ≤ 1 + coreE82Cong L P_b * k
  have hCong : st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b * (k : ℝ) := by
    have hE82_nn : 0 ≤ coreE82Cong L P_b := by
      unfold coreE82Cong; have := P_b.hγ_ℓ; have := P_b.hγ_c; positivity
    have hAt : ∀ e' ∈ st.S_cur.E,
        st.emb.econgAt (coreGraph (D.G t) st.cs.lsf) (fun _ => 1) (fun _ => 1) e' ≤
          1 + coreE82Cong L P_b * (k : ℝ) := by
      intro e' he'
      unfold Embedding.econgAt
      rw [div_one]
      have hS_filt : ∀ e, e ∈ (coreGraph (D.G t) st.cs.lsf).E →
          e' ∈ walkEdges (st.emb e) →
          e = e' ∨ ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ actB p.1 ∧
            e ∈ (st.bun p).edges ∧ e' ∈ walkEdges (piTotal (st.dyn p) e) := by
        intro e _ hw
        by_cases heS : e ∈ st.S_cur.E
        · left
          have hemb : st.emb e = [(e, true)] := by unfold BundleTreeState.emb; simp [heS]
          rw [hemb] at hw
          simp only [walkEdges, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
            insert_empty_eq, Finset.mem_singleton] at hw
          exact hw.symm
        · by_cases hp : ∃ p : Finset ℕ × ℤ, p.1 ∈ st.activeComps ∧ p.2 ∈ st.activeBuckets p.1 ∧
              e ∈ (st.bun p).edges
          · right
            have hemb : st.emb e = piTotal (st.dyn hp.choose) e := by
              unfold BundleTreeState.emb; simp [heS, hp]
            exact ⟨hp.choose, hp.choose_spec.1, hActB_t ▸ hp.choose_spec.2.1,
              hp.choose_spec.2.2, hemb ▸ hw⟩
          · exfalso
            have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
            rw [hemb, walkEdges] at hw
            simp at hw
      rw [hS_E] at he'
      rcases Finset.mem_union.mp he' with he'12 | he'X
      · rcases Finset.mem_union.mp he'12 with he'B | he'Ex
        · rw [Finset.mem_biUnion] at he'B
          rcases he'B with ⟨C, hCA, he'BC⟩
          rw [Finset.mem_biUnion] at he'BC
          rcases he'BC with ⟨b, _, he'H⟩
          have hC : C ∈ components G₀ := hAct_sub hCA
          have hGeq_Cb : GraphEq (st.dyn (C, b)).G (st.bun (C, b)).graph := ((hC_stage C hC).2 b).2.2.2.1
          have hSp_Cb := hDynSp C hC b
          have he'G : e' ∈ (st.dyn (C, b)).G.E := hSp_Cb.1.2.1 he'H
          have he'Bun : e' ∈ (st.bun (C, b)).edges := by rwa [hGeq_Cb.2.1] at he'G
          obtain ⟨he'CE, _, hb_e', _, _⟩ := hBun_edge_props C hC b e' he'Bun
          have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)) ⊆
              insert e' ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e))) := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, _, heB', hw⟩
            · exact Finset.mem_insert_self _ _
            · have hC' : C' ∈ components G₀ := hAct_sub hC'A
              have hGeq' : GraphEq (st.dyn (C', b')).G (st.bun (C', b')).graph :=
                ((hC_stage C' hC').2 b').2.2.2.1
              have hSp' := hDynSp C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hGeq'.2.1]; exact heB'
              have he'_H' : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hSp'.2.2.2.1.2 e he_G') hw
              have he'_Bun' : e' ∈ (st.bun (C', b')).edges := by
                change e' ∈ (st.bun (C', b')).graph.E; rw [← hGeq'.2.1]; exact hSp'.1.2.1 he'_H'
              obtain ⟨he'_CE', _, hb'_e', _, _⟩ := hBun_edge_props C' hC' b' e' he'_Bun'
              have hC_eq : C' = C := by
                by_contra hne
                exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC' hC hne)
                  he'_CE' he'CE
              subst hC_eq
              have hb_eq : b' = b := hb'_e'.symm.trans hb_e'
              subst hb_eq
              exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he_G', hw⟩)
          have hsum_le : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤
              1 + (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)),
                (1 : ℝ)) := by
            calc (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter _, (1 : ℝ))
                ≤ ∑ _e ∈ insert e' ((st.dyn (C, b)).G.E.filter
                    (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e))), (1 : ℝ) :=
                    Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
              _ ≤ 1 + ∑ _e ∈ (st.dyn (C, b)).G.E.filter _, (1 : ℝ) := by
                  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
                  have hcard := Finset.card_insert_le e'
                    ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)))
                  exact_mod_cast (show _ ≤ 1 + _ from by omega)
          have hvc : (∑ _e ∈ (st.dyn (C, b)).G.E.filter
                (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)), (1 : ℝ)) ≤
              (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := by
            have hea := econgAt_le_vcongAt_tail hSp_Cb.2.2.2.1 he'H
            unfold Embedding.econgAt at hea
            rw [div_one] at hea
            have hvt : (st.dyn (C, b)).H.tail e' ∈ (st.dyn (C, b)).H.V := by
              rw [(hSp_Cb.1.2.2 e' he'H).1]
              exact hSp_Cb.2.2.2.1.1 (((hC_stage C hC).2 b).2.2.2.2.1 e' he'G).1
            have hv_sup : (piTotal (st.dyn (C, b))).vcongAt (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1)
                ((st.dyn (C, b)).H.tail e') ≤
                (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := by
              dsimp only [Embedding.vcong]
              split_ifs with hne
              · exact Finset.le_sup' _ hvt
              · exact absurd ⟨_, hvt⟩ hne
            exact le_trans hea hv_sup
          have hdeg_k : ((st₀.bun (C, b)).graph.maxDeg : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (hStageFlat C hC b).2.2.2
          have hvc_k : (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
              coreE82Cong L P_b * (k : ℝ) :=
            le_trans hSp_Cb.2.2.2.2.2 (mul_le_mul_of_nonneg_left hdeg_k hE82_nn)
          linarith
        · have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)) ⊆ {e'} := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, hb'A, heB', hw⟩
            · exact Finset.mem_singleton_self _
            · exfalso
              have hC' : C' ∈ components G₀ := hAct_sub hC'A
              have hGeq' : GraphEq (st.dyn (C', b')).G (st.bun (C', b')).graph :=
                ((hC_stage C' hC').2 b').2.2.2.1
              have hSp' := hDynSp C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hGeq'.2.1]; exact heB'
              have he'H : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hSp'.2.2.2.1.2 e he_G') hw
              have he'Bun' : e' ∈ (st.bun (C', b')).edges := by
                change e' ∈ (st.bun (C', b')).graph.E; rw [← hGeq'.2.1]; exact hSp'.1.2.1 he'H
              obtain ⟨he'_CE', _, _, he'_niG, _⟩ := hBun_edge_props C' hC' b' e' he'Bun'
              rw [Finset.mem_biUnion] at he'Ex
              rcases he'Ex with ⟨C, hCA, he'ExC⟩
              have hC : C ∈ components G₀ := hAct_sub hCA
              have he'G_C : e' ∈ (st.cs.compSt C).G.E :=
                (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he'ExC).1).1
              have he'_niC : e' ∉ (st.cs.compSt C).insertedEdges := fun hm =>
                he'_niG (hI_t.hCompIns_sub C (hcs_G₀ ▸ hC) hm)
              have he'_CE : e' ∈ compEdgeSet G₀ C := by
                have hs := ((hI_t.hCompLSF C (hcs_G₀ ▸ hC)).1.hsurv_edge e' he'G_C he'_niC).1
                rwa [(hI_t.hCompLSF C (hcs_G₀ ▸ hC)).2.1, hcs_G₀] at hs
              have hEq : C = C' := by
                by_contra hne
                exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC hC' hne)
                  he'_CE he'_CE'
              subst hEq
              exact (Finset.mem_sdiff.mp he'ExC).2
                (Finset.mem_biUnion.mpr ⟨b', hActB_t.symm ▸ hb'A, he'Bun'⟩)
          have hsum_le1 : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
            calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
              _ = 1 := by simp
          have hk_nn : 0 ≤ coreE82Cong L P_b * (k : ℝ) := mul_nonneg hE82_nn (Nat.cast_nonneg _)
          linarith
      · have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)) ⊆ {e'} := by
          intro e he
          rw [Finset.mem_filter] at he
          rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, _, heB', hw⟩
          · exact Finset.mem_singleton_self _
          · exfalso
            have hC' : C' ∈ components G₀ := hAct_sub hC'A
            have hGeq' : GraphEq (st.dyn (C', b')).G (st.bun (C', b')).graph :=
              ((hC_stage C' hC').2 b').2.2.2.1
            have hSp' := hDynSp C' hC' b'
            have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hGeq'.2.1]; exact heB'
            have he'H : e' ∈ (st.dyn (C', b')).H.E :=
              walkEdges_subset_of_isWalk (hSp'.2.2.2.1.2 e he_G') hw
            have he'Bun' : e' ∈ (st.bun (C', b')).edges := by
              change e' ∈ (st.bun (C', b')).graph.E; rw [← hGeq'.2.1]; exact hSp'.1.2.1 he'H
            exact (hBun_edge_props C' hC' b' e' he'Bun').2.2.2.1 (hI_t.hCross_sub he'X)
        have hsum_le1 : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
          calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
            _ = 1 := by simp
        have hk_nn : 0 ≤ coreE82Cong L P_b * (k : ℝ) := mul_nonneg hE82_nn (Nat.cast_nonneg _)
        linarith
    unfold Embedding.econg
    split_ifs with hE
    · exact (Finset.sup'_le_iff _ _).mpr hAt
    · positivity
  -- Clause 6: Sparsity bound
  have hCard : ∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
      (st.S_cur.E.card : ℝ) ≤ bundleSizeFactor L P_b M B_bound * (M : ℝ) / (k : ℝ) := by
    intro B_bound hB_bound
    have hGn_bnds : ∀ C ∈ components G₀, ∀ b : ℤ,
        (st.dyn (C, b)).G.n ≤ bundleNMax M ∧
        (st.dyn (C, b)).G.n ≤
          (st₀.bun (C, b)).vertices.card + 2 * ((st.cs.compSt C).R \ (cs₀.compSt C).R).card := by
      intro C hC b
      exact bundleRunSeq_dyn_Gn_bounds oracle C_lsst L sparsify hk hM ord j hC b
        (fun s hs =>
          have hbs := hStageBase s hs
          ⟨hbs.2.2.2.2.2.2.2.1, ((hbs.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1⟩)
        (fun s hs =>
          have hss := hStageStep s hs
          have hsb := hss.2.2.2.2 C hC b
          ⟨hss.1, hsb.1, hsb.2.1, hsb.2.2.1, hsb.2.2.2.1⟩)
        (by
          have hfl := hStageFlat C hC b
          exact ⟨hfl.1, hfl.2.1, hfl.2.2.1⟩) t ht
    exact bundleRunSeq_S_cur_card_le oracle C_lsst L P_b sparsify hLSST hk hG₀ hV₀ hℓ₀ hD hM hN
      hThresh ⟨ρ_all, hρ_ord, hρ_batch⟩ j ht hActB_t hI_t hAct_sub hS_E hSmallAct
      (fun C hC b => (hBunSpec C hC b).1) hGn_bnds (fun C hC b => (hDynSp C hC b).2.1) hB_bound
  exact ⟨hSub, hEmb, hApprox, hLenEmb, hCong, hCard⟩

end

end MinCostFlow.SparseCore
