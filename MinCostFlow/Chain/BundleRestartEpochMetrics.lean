module

public import MinCostFlow.Chain.BundleRestartEpochSize
import MinCostFlow.SparseCore.BundleSpannerMetricsAux
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.SplitSpannerBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Post-Restart Sparsified-Core Metrics for `sparseCoreBundleRestartTool`

Proves `epochBundleSeq_isSparsifiedCoreGraph`: at every stage `δ ≤ t - s₀` of a non-restarted
epoch `[s₀, t]` of `sparseCoreBundleRestartTool`, the branch state `st δ` satisfies all six
clauses of `IsSparsifiedCoreGraph` (subgraph, embedding, `approx2`, embedding length
`≤ coreE82Len L P_b`, edge congestion `≤ 1 + coreE82Cong L P_b * k`, and edge count
`≤ bundleSizeFactor L P_b M B_bound * M / k`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 2. All six clauses of `IsSparsifiedCoreGraph` at any stage of an epoch -/

/-- All six sparsified-core metrics for `epochBundleSeq` at any stage `δ ≤ t - s₀` of an epoch
`[s₀, t]` (paper Definition 5.7, page 19). -/
theorem epochBundleSeq_isSparsifiedCoreGraph
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e) (hLen : LengthsStable D τ)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r)
    {δ : ℕ} (hδ : δ ≤ t - s₀) :
    let G₀ := D.G 0
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
    let actB := st₀.activeBuckets
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j δ
    (coreGraph (D.G (s₀ + δ)) st.cs.lsf).IsSubgraph st.S_cur ∧
    st.emb.IsEmbedding (coreGraph (D.G (s₀ + δ)) st.cs.lsf) st.S_cur ∧
    (∀ e ∈ (coreGraph (D.G (s₀ + δ)) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ (s₀ + δ)) e) (coreLen st.cs.lsf (D.ℓ (s₀ + δ)) e')) ∧
    (st.emb.length (coreGraph (D.G (s₀ + δ)) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
    st.emb.econg (coreGraph (D.G (s₀ + δ)) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b * (k : ℝ) ∧
    (∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
      (st.S_cur.E.card : ℝ) ≤ bundleSizeFactor L P_b M B_bound * (M : ℝ) / (k : ℝ)) := by
  classical
  intro G₀ st₀ actB st
  have hℓ₀ : ∀ e ∈ G₀.E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ (D.ℓ 0) e := fun e he => by
    rw [safeLen_eq_of_mem (D.ℓ 0) he]; exact hℓ₀ e he
  let cs₀ := st₀.cs
  let r := s₀ + δ
  have hr_le : r ≤ τ := by omega
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCompG : ∀ C' ∈ components G₀, (cs₀.compSt C').G = compGraph G₀ C' :=
    fun C' hC' => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC').2.1
  have hInv := epochBundleSeq_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSt_base := (epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest).1 δ hδ
  have hbp_r := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
    hV₀ j r).1
  have hBr := hBun r hr_le
  have hActB_t : st.activeBuckets = actB := by
    rw [hSt_base.activeBuckets, ← hbp_r.activeBuckets]; exact hBr.2.2.2.2.1
  have hcs_t : st.cs = compLSFBatch cs₀ (dynBatches D r).flatten := by
    rw [hSt_base.cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.1
  have hI_t : CompLSFInv C_lsst (D.ℓ 0) st.cs := by
    rw [hSt_base.cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.2.1
  have hG_t : st.cs.G = D.G r := by
    rw [hSt_base.cs, ← hbp_r.cs]; exact hBr.2.2.2.2.2.2.2.2.1
  have hcs_G₀ : st.cs.G₀ = G₀ := by rw [hcs_t, compLSFBatch_G₀]; rfl
  have hLarge_sub : largeComps k G₀ ⊆ st.activeComps := by
    rw [hSt_base.activeComps, ← hbp_r.activeComps]; exact hBr.2.2.2.2.2.2.2.2.2.1.1
  have hAct_sub : st.activeComps ⊆ components G₀ := (hInv.2.2.1 δ hδ).2.1
  have hUnt : ∀ C ∈ components G₀, C ∉ st.activeComps → st.cs.compSt C = cs₀.compSt C := by
    intro C hC hna
    rw [hSt_base.activeComps, ← hbp_r.activeComps] at hna
    rw [hSt_base.cs, ← hbp_r.cs]
    exact (hBr.2.2.2.2.2.2.2.2.2.2.1 C hC hna).1
  have hS_V_E_sub : st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => st.extraEdges C) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur := by
    dsimp only [st, epochBundleSeq]
    split_ifs with hcond
    · exact (hSc t htτ).1.2
    · exact (hSc r hr_le).2.2
  obtain ⟨hS_V, hS_E, hS_sub⟩ := hS_V_E_sub
  have hDynSp := (hInv.2.2.1 δ hδ).2.2
  have ⟨ρ_all, hρ_ord, _⟩ := hOrd
  have hBun_meta : ∀ C ∈ components G₀, ∀ b : ℤ,
      (st.bun (C, b)).IsPartition
        (coreRotation (L := st.cs.lsf) (hG_t.symm ▸ ρ_all r) hI_t.hG_val (compLSF_RF_isRSF hI_t)) k ∧
      (st.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
      Disjoint (st.bun (C, b)).edges st.cs.insertedGlobal := by
    intro C hC b
    have hρ_cast : (hG_t.symm ▸ ρ_all r : Rotation st.cs.G).order = ord r :=
      (rotation_cast_order hG_t.symm (ρ_all r)).trans (hρ_ord r hr_le)
    have hReady : BundleCompReady st.cs C (st.bun (C, b)) k (ord r) ∧
        (st.bun (C, b)).edges ⊆ (st₀.bun (C, b)).edges ∧
        Disjoint (st.bun (C, b)).edges st.cs.insertedGlobal := by
      dsimp only [st, epochBundleSeq]
      split_ifs with hcond
      · have hBt := hBun t htτ
        have hrt : r = t := hcond.1
        rw [hrt]
        have hc := (hBt.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
        exact ⟨hc.1, hc.2.2.1 ▸ Finset.sdiff_subset, hc.2.2.2.2.1⟩
      · have hc := (hBr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
        have hbf := (foldl_bundleRestart_props lsfInit C_lsst L sparsify
          ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate k M N D ord
            restarts r).1 (restarts r)).2.2.2.2.1 j
        have hcs_eq : (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts
            k M N D ord restarts (s₀ + δ)).trees j).cs =
            (((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterUpdate k M N D ord
              restarts r).1.trees j).cs := hbf.cs
        refine ⟨hc.2.1, ?_, ?_⟩
        · rw [hc.2.2.2.1, hc.2.2.1]; exact Finset.sdiff_subset
        · rw [hc.2.2.2.1, hcs_eq]; exact hc.2.2.2.2.1
    exact ⟨hReady.1.1 (hG_t.symm ▸ ρ_all r) hI_t.hG_val (compLSF_RF_isRSF hI_t) hρ_cast,
      hReady.2.1, hReady.2.2⟩
  have hBun_edge_props : ∀ C ∈ components G₀, ∀ b : ℤ, ∀ e ∈ (st.bun (C, b)).edges,
      e ∈ compEdgeSet G₀ C ∧ e ∈ G₀.E ∧ st₀.origBucket e = b ∧
        e ∉ st.cs.insertedGlobal ∧ e ∉ st.cs.crossEdges := by
    intro C hC b e he
    have he0 : e ∈ (st₀.bun (C, b)).edges := (hBun_meta C hC b).2.1 he
    have hsub0 : (st₀.bun (C, b)).edges ⊆
        bucketCoreEdges (coreGraph G₀ cs₀.lsf) st₀.origBucket C b :=
      initBundleFor_edges_subset _ _ _ _
    have hbc := bucketCoreEdges_props hI₀ rfl hCompG st₀.origBucket hC b (hsub0 he0)
    have heG0 : e ∈ G₀.E := (Finset.mem_filter.mp hbc.1).1
    have hni : e ∉ st.cs.insertedGlobal := Finset.disjoint_left.mp (hBun_meta C hC b).2.2 he
    have hnc : e ∉ st.cs.crossEdges := fun hc => hni (hI_t.hCross_sub hc)
    exact ⟨hbc.1, heG0, hbc.2.2.2.2, hni, hnc⟩
  -- Clause 1: Subgraph
  have hSub : (coreGraph (D.G r) st.cs.lsf).IsSubgraph st.S_cur := by rw [← hG_t]; exact hS_sub
  -- Clause 2: Embedding
  have hEmb : st.emb.IsEmbedding (coreGraph (D.G r) st.cs.lsf) st.S_cur := by
    refine ⟨?_, fun e he => ?_⟩
    · change st.cs.RF.R ⊆ st.S_cur.V; rw [hS_V]
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
          have hSp_p := hDynSp p.1 hpC p.2
          have hGeq_p : GraphEq (st.dyn p).G (st.bun p).graph := hSp_p.1
          have heGp : e ∈ (st.dyn p).G.E := by rw [hGeq_p.2.1]; exact hep
          have hw_p : (st.dyn p).H.IsWalk ((st.dyn p).G.tail e) ((st.dyn p).G.head e)
              (piTotal (st.dyn p) e) := hSp_p.2.2.2.2.2.2.1.2 e heGp
          have hPart_p := (hBun_meta p.1 hpC p.2).1
          have hw_lift := isWalk_map (st.bun p).parent (fun e' he' => by
            have he'G : e' ∈ (st.dyn p).G.E := hSp_p.2.2.2.1.2.1 he'
            have he'B : e' ∈ (st.bun p).edges := by rwa [hGeq_p.2.1] at he'G
            have he'S : e' ∈ st.S_cur.E := by
              rw [hS_E]
              exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_biUnion.mpr ⟨p.1, hpA, Finset.mem_biUnion.mpr ⟨p.2, hpb, he'⟩⟩))
            have hProj' := BundleState.project_edge hPart_p he'B
            have hSubH' := hSp_p.2.2.2.1.2.2 e' he'
            have hSubS' := hS_sub.2.2 e' he'S
            have htail : (st.bun p).parent ((st.dyn p).H.tail e') = st.S_cur.tail e' := by
              rw [hSubH'.1, (hGeq_p.2.2 e' he'G).1, hProj'.2.1, hSubS'.1]
            have hhead : (st.bun p).parent ((st.dyn p).H.head e') = st.S_cur.head e' := by
              rw [hSubH'.2, (hGeq_p.2.2 e' he'G).2, hProj'.2.2, hSubS'.2]
            exact ⟨he'S, htail, hhead⟩) hw_p
          have hProj := BundleState.project_edge hPart_p hep
          have htail_e : (st.bun p).parent ((st.dyn p).G.tail e) =
              (coreGraph (D.G r) st.cs.lsf).tail e := by rw [(hGeq_p.2.2 e heGp).1, hProj.2.1, hG_t]
          have hhead_e : (st.bun p).parent ((st.dyn p).G.head e) =
              (coreGraph (D.G r) st.cs.lsf).head e := by rw [(hGeq_p.2.2 e heGp).2, hProj.2.2, hG_t]
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
              intro hm; rw [Finset.mem_biUnion] at hm
              rcases hm with ⟨b, hb, heb⟩; exact hp ⟨(C, b), hCA, hb, heb⟩
            exact heS (by
              rw [hS_E]
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨C, hCA,
                  Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heC, hnF⟩, hnB⟩⟩)))
          have hNL : C ∉ largeComps k G₀ := fun hL' => hna (hLarge_sub hL')
          have hcs_u := hUnt C hC hna
          have hlt : 4 * (compGraph G₀ C).m < k := by
            by_contra hge
            push Not at hge
            have hm1 : 1 ≤ (compGraph G₀ C).m := by
              have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge; omega
            exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
          have hsm := initLSF_small_props_with hInit hG₀ hℓs hk hC hlt
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
          have hth_eq : (coreGraph (D.G r) st.cs.lsf).tail e =
              (coreGraph (D.G r) st.cs.lsf).head e := by
            dsimp only [coreGraph]; rw [← hG_t]; exact hrt
          rw [hth_eq]; exact MGraph.IsWalk.nil _
  -- Clause 3: approx2
  have hApprox : ∀ e ∈ (coreGraph (D.G r) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ r) e) (coreLen st.cs.lsf (D.ℓ r) e') := by
    intro e he e' he'
    have hwstr_ge1 : ∀ x ∈ (D.G r).E, 1 ≤ st.cs.lsf.wstr x := by
      intro x hx
      have hℓr : ∀ y ∈ st.cs.G.E, 0 < D.ℓ r y := hG_t ▸ hℓ r hr_le
      have hℓo : ∀ y ∈ st.cs.G₀.E, y ∈ st.cs.G.E → y ∉ st.cs.insertedGlobal →
          D.ℓ r y = D.ℓ 0 y := by
        intro y _ hy hni
        rw [hG_t] at hy
        rw [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at hni
        exact length_eq_init_of_not_batchesInserted hD hLen r hr_le y hy hni
      have hH := hI_t.to_Holds hℓr hℓo
      have hHw : st.cs.RF.stretch (D.G r) (D.ℓ r) x ≤ st.cs.lsf.wstr x := by
        have htmp := (hH.2.2.2 x (hG_t.symm ▸ hx)).1
        change st.cs.RF.stretch st.cs.G (D.ℓ r) x ≤ st.cs.lsf.wstr x at htmp
        rwa [hG_t] at htmp
      exact (one_le_stretch (hG_t ▸ (compLSF_RF_isRSF hI_t).2.2.2.2)
        (fun y hy => le_of_lt (hℓ r hr_le y hy)) hx).trans hHw
    have hcore_pos : ∀ x ∈ (D.G r).E, 0 < coreLen st.cs.lsf (D.ℓ r) x :=
      fun x hx => mul_pos (lt_of_lt_of_le zero_lt_one (hwstr_ge1 x hx)) (hℓ r hr_le x hx)
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
        have hSp_p := hDynSp p.1 hpC p.2
        have hGeq_p : GraphEq (st.dyn p).G (st.bun p).graph := hSp_p.1
        have heGp : e ∈ (st.dyn p).G.E := by rw [hGeq_p.2.1]; exact hep
        have he'_H : e' ∈ (st.dyn p).H.E :=
          walkEdges_subset_of_isWalk (hSp_p.2.2.2.2.2.2.1.2 e heGp) he'
        have he'_B : e' ∈ (st.bun p).edges := by
          change e' ∈ (st.bun p).graph.E; rw [← hGeq_p.2.1]; exact hSp_p.2.2.2.1.2.1 he'_H
        obtain ⟨_, heG0, hb_e, he_niG, _⟩ := hBun_edge_props p.1 hpC p.2 e hep
        obtain ⟨_, he'G0, hb_e', he'_niG, _⟩ := hBun_edge_props p.1 hpC p.2 e' he'_B
        have he_ni : e ∉ batchesInserted (dynBatches D r) := by
          rwa [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he_niG
        have he'_ni : e' ∉ batchesInserted (dynBatches D r) := by
          rwa [hcs_t, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he'_niG
        have he_Dr : e ∈ (D.G r).E := (Finset.mem_sdiff.mp he).1
        have he'_Dr : e' ∈ (D.G r).E := by
          have h1 : e' ∈ (coreGraph st.cs.G st.cs.lsf).E := (hBun_meta p.1 hpC p.2).1.1 he'_B
          rw [hG_t] at h1; exact (Finset.mem_sdiff.mp h1).1
        have hℓ_e : D.ℓ r e = D.ℓ 0 e :=
          length_eq_init_of_not_batchesInserted hD hLen r hr_le e he_Dr he_ni
        have hℓ_e' : D.ℓ r e' = D.ℓ 0 e' :=
          length_eq_init_of_not_batchesInserted hD hLen r hr_le e' he'_Dr he'_ni
        have hw_e : st.cs.lsf.wstr e = cs₀.lsf.wstr e := by
          change st.cs.wstrGlobal e = cs₀.wstrGlobal e
          rw [hcs_t]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D r).flatten
            (by rw [← hcs_t, hG_t]; exact he_Dr) (by rwa [← hcs_t])
        have hw_e' : st.cs.lsf.wstr e' = cs₀.lsf.wstr e' := by
          change st.cs.wstrGlobal e' = cs₀.wstrGlobal e'
          rw [hcs_t]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D r).flatten
            (by rw [← hcs_t, hG_t]; exact he'_Dr) (by rwa [← hcs_t])
        have hlen_e : coreLen st.cs.lsf (D.ℓ r) e = coreLen cs₀.lsf (D.ℓ 0) e := by
          unfold coreLen; rw [hw_e, hℓ_e]
        have hlen_e' : coreLen st.cs.lsf (D.ℓ r) e' = coreLen cs₀.lsf (D.ℓ 0) e' := by
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
        exact approx2_of_bucketOf_eq (hlen_e ▸ hcore_pos e he_Dr)
          (hlen_e' ▸ hcore_pos e' he'_Dr) hbk_eq
      · have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
        rw [hemb, walkEdges] at he'; simp at he'
  -- Clause 4: Embedding length
  have hLenEmb : (st.emb.length (coreGraph (D.G r) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b := by
    have h1 : (1 : ℝ) ≤ coreE82Len L P_b := by
      unfold coreE82Len
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
      have hγ := one_le_pow₀ P_b.hγ_ℓ (n := L + 1)
      nlinarith
    have hnat : ∀ e ∈ (coreGraph (D.G r) st.cs.lsf).E, ((st.emb e).length : ℝ) ≤ coreE82Len L P_b := by
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
          have hSp_p := hDynSp p.1 hpC p.2
          have heGp : e ∈ (st.dyn p).G.E := by rw [hSp_p.1.2.1]; exact hp.choose_spec.2.2
          have hle_sup : (piTotal (st.dyn p) e).length ≤
              Embedding.length (piTotal (st.dyn p)) (st.dyn p).G :=
            Finset.le_sup (f := fun x => (piTotal (st.dyn p) x).length) heGp
          exact le_trans (by exact_mod_cast hle_sup) hSp_p.2.2.2.2.2.2.2.1
        · have hemb : st.emb e = [] := by unfold BundleTreeState.emb; simp [heS, hp]
          rw [hemb]; simp only [List.length_nil, Nat.cast_zero]; linarith
    by_cases hne : (coreGraph (D.G r) st.cs.lsf).E.Nonempty
    · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup _ hne (fun e => (st.emb e).length)
      change (((coreGraph (D.G r) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [heq]; exact hnat e he
    · change (((coreGraph (D.G r) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sup_empty, bot_eq_zero', Nat.cast_zero]; linarith
  -- Clause 5: Edge congestion ≤ 1 + coreE82Cong L P_b * k
  have hCong : st.emb.econg (coreGraph (D.G r) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b * (k : ℝ) := by
    have hE82_nn : 0 ≤ coreE82Cong L P_b := by
      unfold coreE82Cong; have := P_b.hγ_ℓ; have := P_b.hγ_c; positivity
    have hAt : ∀ e' ∈ st.S_cur.E,
        st.emb.econgAt (coreGraph (D.G r) st.cs.lsf) (fun _ => 1) (fun _ => 1) e' ≤
          1 + coreE82Cong L P_b * (k : ℝ) := by
      intro e' he'
      unfold Embedding.econgAt; rw [div_one]
      have hS_filt : ∀ e, e ∈ (coreGraph (D.G r) st.cs.lsf).E →
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
            rw [hemb, walkEdges] at hw; simp at hw
      rw [hS_E] at he'
      rcases Finset.mem_union.mp he' with he'12 | he'X
      · rcases Finset.mem_union.mp he'12 with he'B | he'Ex
        · rw [Finset.mem_biUnion] at he'B; rcases he'B with ⟨C, hCA, he'BC⟩
          rw [Finset.mem_biUnion] at he'BC; rcases he'BC with ⟨b, _, he'H⟩
          have hC : C ∈ components G₀ := hAct_sub hCA
          have hSp_Cb := hDynSp C hC b
          have hGeq_Cb : GraphEq (st.dyn (C, b)).G (st.bun (C, b)).graph := hSp_Cb.1
          have he'G : e' ∈ (st.dyn (C, b)).G.E := hSp_Cb.2.2.2.1.2.1 he'H
          have he'Bun : e' ∈ (st.bun (C, b)).edges := by rwa [hGeq_Cb.2.1] at he'G
          obtain ⟨he'CE, _, hb_e', _, _⟩ := hBun_edge_props C hC b e' he'Bun
          have hfilt_sub : (coreGraph (D.G r) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)) ⊆
              insert e' ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e))) := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, _, heB', hw⟩
            · exact Finset.mem_insert_self _ _
            · have hC' : C' ∈ components G₀ := hAct_sub hC'A
              have hSp' := hDynSp C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hSp'.1.2.1]; exact heB'
              have he'_H' : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hSp'.2.2.2.2.2.2.1.2 e he_G') hw
              have he'_Bun' : e' ∈ (st.bun (C', b')).edges := by
                change e' ∈ (st.bun (C', b')).graph.E; rw [← hSp'.1.2.1]; exact hSp'.2.2.2.1.2.1 he'_H'
              obtain ⟨he'_CE', _, hb'_e', _, _⟩ := hBun_edge_props C' hC' b' e' he'_Bun'
              have hC_eq : C' = C := by
                by_contra hne
                exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC' hC hne)
                  he'_CE' he'CE
              subst hC_eq
              have hb_eq : b' = b := hb'_e'.symm.trans hb_e'
              subst hb_eq
              exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he_G', hw⟩)
          have hsum_le : (∑ _e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤
              1 + (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)),
                (1 : ℝ)) := by
            calc (∑ _e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter _, (1 : ℝ))
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
            have hea := econgAt_le_vcongAt_tail hSp_Cb.2.2.2.2.2.2.1 he'H
            unfold Embedding.econgAt at hea; rw [div_one] at hea
            have hvt : (st.dyn (C, b)).H.tail e' ∈ (st.dyn (C, b)).H.V := by
              rw [(hSp_Cb.2.2.2.1.2.2 e' he'H).1]
              exact hSp_Cb.2.2.2.2.2.2.1.1 (hSp_Cb.2.1 e' he'G).1
            have hv_sup : (piTotal (st.dyn (C, b))).vcongAt (st.dyn (C, b)).G (st.dyn (C, b)).H
                  (fun _ => 1) ((st.dyn (C, b)).H.tail e') ≤
                (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := by
              dsimp only [Embedding.vcong]; split_ifs with hne
              · exact Finset.le_sup' _ hvt
              · exact absurd ⟨_, hvt⟩ hne
            exact le_trans hea hv_sup
          linarith [hSp_Cb.2.2.2.2.2.2.2.2]
        · have hfilt_sub : (coreGraph (D.G r) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)) ⊆ {e'} := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, hb'A, heB', hw⟩
            · exact Finset.mem_singleton_self _
            · exfalso
              have hC' : C' ∈ components G₀ := hAct_sub hC'A
              have hSp' := hDynSp C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hSp'.1.2.1]; exact heB'
              have he'H : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hSp'.2.2.2.2.2.2.1.2 e he_G') hw
              have he'Bun' : e' ∈ (st.bun (C', b')).edges := by
                change e' ∈ (st.bun (C', b')).graph.E; rw [← hSp'.1.2.1]; exact hSp'.2.2.2.1.2.1 he'H
              obtain ⟨he'_CE', _, _, he'_niG, _⟩ := hBun_edge_props C' hC' b' e' he'Bun'
              rw [Finset.mem_biUnion] at he'Ex; rcases he'Ex with ⟨C, hCA, he'ExC⟩
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
          have hsum_le1 : (∑ _e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
            calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
              _ = 1 := by simp
          have hk_nn : 0 ≤ coreE82Cong L P_b * (k : ℝ) := mul_nonneg hE82_nn (Nat.cast_nonneg _)
          linarith
      · have hfilt_sub : (coreGraph (D.G r) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)) ⊆ {e'} := by
          intro e he
          rw [Finset.mem_filter] at he
          rcases hS_filt e he.1 he.2 with rfl | ⟨⟨C', b'⟩, hC'A, _, heB', hw⟩
          · exact Finset.mem_singleton_self _
          · exfalso
            have hC' : C' ∈ components G₀ := hAct_sub hC'A
            have hSp' := hDynSp C' hC' b'
            have he_G' : e ∈ (st.dyn (C', b')).G.E := by rw [hSp'.1.2.1]; exact heB'
            have he'H : e' ∈ (st.dyn (C', b')).H.E :=
              walkEdges_subset_of_isWalk (hSp'.2.2.2.2.2.2.1.2 e he_G') hw
            have he'Bun' : e' ∈ (st.bun (C', b')).edges := by
              change e' ∈ (st.bun (C', b')).graph.E; rw [← hSp'.1.2.1]; exact hSp'.2.2.2.1.2.1 he'H
            exact (hBun_edge_props C' hC' b' e' he'Bun').2.2.2.2 he'X
        have hsum_le1 : (∑ _e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
          calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
            _ = 1 := by simp
        have hk_nn : 0 ≤ coreE82Cong L P_b * (k : ℝ) := mul_nonneg hE82_nn (Nat.cast_nonneg _)
        linarith
    dsimp only [Embedding.econg]
    split_ifs with hne
    · exact Finset.sup'_le hne _ hAt
    · have hk_nn : 0 ≤ coreE82Cong L P_b * (k : ℝ) := mul_nonneg hE82_nn (Nat.cast_nonneg _)
      linarith
  -- Clause 6: Sparsity
  refine ⟨hSub, hEmb, hApprox, hLenEmb, hCong, fun B_bound hB_bound => ?_⟩
  exact epochBundleSeq_S_cur_card_le lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
    hδ hB_bound

end MinCostFlow.Chain

end
