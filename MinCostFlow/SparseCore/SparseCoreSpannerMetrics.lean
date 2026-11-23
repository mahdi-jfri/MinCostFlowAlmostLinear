module

public import MinCostFlow.SparseCore.SparseCoreRunBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Core-graph spanner theorem for `sparseCoreTool` (`treeRunSeq_isSparsifiedCoreGraph`)

Proves `IsSparsifiedCoreGraph` (`IsSubgraph`, `IsEmbedding` via component-wise `qToR`, `approx2`,
length, congestion, and unconditional sparsity on `st.S_cur.E.card`) across `t = 0..τ`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 3. Core-graph spanner theorem (`treeRunSeq_isSparsifiedCoreGraph`) -/

/-- State-level core-graph spanner theorem for any `st : TreeCoreState L` at step `t ≤ τ`
whose `cs`, `ts`, `activeComps`, and `origBucket` match `treeRunSeq` and whose `dyn (C, b)` buckets
satisfy the `Theorem 8.2` epoch invariants (`H.m`, `IsEmbedding`, `length`, `vcong`). Used by
both `treeRunSeq_isSparsifiedCoreGraph` and restartable `sparseCoreRestartTool`. -/
theorem treeCoreState_isSparsifiedCoreGraph
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
    (j : ℕ) (hj : j < k) (t : ℕ) (ht : t ≤ τ) (st : TreeCoreState L) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
    let stOrig := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
    st.origBucket = (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) →
    st.cs = stOrig.cs →
    st.ts = stOrig.ts →
    st.activeComps = stOrig.activeComps →
    st.S_cur.V = st.cs.RF.R →
    st.S_cur.E =
      (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
        (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)) ∪
        st.cs.crossEdges →
    (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur →
    (∀ C ∈ components G₀, ∀ b : ℤ,
      (st.dyn (C, b)).G.IsValid ∧
      (st.ts C).C.IsSubgraph (st.dyn (C, b)).G ∧
      (st.dyn (C, b)).G.E = (st.ts C).C.E.filter (fun e => origB e = b) ∧
      (st.dyn (C, b)).G.n ≤ coreNMax M) →
    (∀ C ∈ components G₀, ∀ b : ℤ,
      (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
      ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
        coreLambdaS P_b M ∧
      (piTotal (st.dyn (C, b))).IsEmbedding (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
      ((piTotal (st.dyn (C, b))).length (st.dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b ∧
      (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
        coreE82Cong L P_b * ((ts₀ C).C.maxDeg : ℝ) ∧
      (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
        coreE82Cong L P_b * (2 * (M : ℝ))) →
    (coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur ∧
    st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur ∧
    (∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ t) e) (coreLen st.cs.lsf (D.ℓ t) e')) ∧
    (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
    st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b *
        (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) ∧
    st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b * (2 * (M : ℝ)) ∧
    (∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
      (st.S_cur.E.card : ℝ) ≤ ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
        (B_bound : ℝ) * (2 * (G₀.maxDeg : ℝ) + 190) + 115) *
        (M : ℝ) / (k : ℝ)) := by
  classical
  intro G₀ ℓ₀ cs₀ ts₀ origB actB stOrig horig_st hcs_st hts_st hact_st hSV_st hSE_st
    hSsub_st hDynG_st hDynSp_st
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e := hℓ 0 (Nat.zero_le τ)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    simpa [safeLen, he] using hℓ₀ e he
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2
  have hT₀ : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (cs₀.compSt C) (ts₀ C) :=
    fun C hC => initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨hSmall, hStage_all, _, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hbt := hBase t ht
  have hst := hStage_all t ht
  have hGeq : st.cs.G = D.G t := hcs_st ▸ hbt.2.2.2.2.2.2.2.2.2.1
  have hI_t : CompLSFInv C_lsst ℓ₀ st.cs := hcs_st ▸ hbt.2.2.2.2.2.2.2.2.1
  have hcs_G₀ : st.cs.G₀ = G₀ := by rw [hcs_st, hbt.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
  have hAct_sub : st.activeComps ⊆ components G₀ := hact_st ▸ hbt.2.2.2.2.2.2.2.2.2.2.1.2
  have hLarge_sub : largeComps k G₀ ⊆ st.activeComps := hact_st ▸ hbt.2.2.2.2.2.2.2.2.2.2.1.1
  have hUnt : ∀ C ∈ components G₀, C ∉ st.activeComps →
      st.cs.compSt C = cs₀.compSt C ∧ st.ts C = ts₀ C := fun C hC hna => by
    rw [hcs_st, hts_st]
    exact hbt.2.2.2.2.2.2.2.2.2.2.2.1 C hC (hact_st ▸ hna)
  have hC_props : ∀ C ∈ components G₀,
      LSFDerivedFrom (cs₀.compSt C) (st.cs.compSt C) ∧
      TildeInv (cs₀.compSt C) (st.cs.compSt C) (st.ts C) ∧
      (st.ts C).C.E ⊆ (ts₀ C).C.E ∧
      Disjoint (st.ts C).C.E (st.cs.compSt C).insertedEdges ∧
      ∀ b : ℤ,
        (st.dyn (C, b)).G.IsValid ∧
        (st.ts C).C.IsSubgraph (st.dyn (C, b)).G ∧
        (st.dyn (C, b)).G.E = (st.ts C).C.E.filter (fun e => origB e = b) ∧
        True := fun C hC => by
    have hp := hbt.2.2.2.2.2.2.2.2.2.2.2.2 C hC
    refine ⟨?_, ?_, ?_, ?_, fun b => ⟨(hDynG_st C hC b).1, (hDynG_st C hC b).2.1, (hDynG_st C hC b).2.2.1, True.intro⟩⟩
    · rw [hcs_st]; exact hp.1
    · rw [hcs_st, hts_st]; exact hp.2.1
    · rw [hts_st]; exact hp.2.2.1
    · rw [hcs_st, hts_st]; exact hp.2.2.2.1
  have hC_compEdge : ∀ C ∈ components G₀, ∀ x ∈ (st.ts C).C.E,
      x ∈ compEdgeSet G₀ C ∧ x ∈ (st.cs.compSt C).G.E ∧ x ∉ (st.cs.compSt C).insertedEdges ∧
        x ∉ st.cs.insertedGlobal ∧ x ∉ st.cs.crossEdges := by
    intro C hC x hx
    have hx₀ : x ∈ (ts₀ C).C.E := (hC_props C hC).2.2.1 hx
    have hxC₀ : x ∈ (cs₀.compSt C).G.E := (Finset.mem_sdiff.mp ((hT₀ C hC).hCE_sub hx₀)).1
    have hx_ce : x ∈ compEdgeSet G₀ C := by rwa [(hS₀C_spec C hC).1] at hxC₀
    have hxC : x ∈ (st.cs.compSt C).G.E :=
      (Finset.mem_sdiff.mp ((hC_props C hC).2.1.hCE_sub hx)).1
    have hx_niC : x ∉ (st.cs.compSt C).insertedEdges :=
      Finset.disjoint_left.mp (hC_props C hC).2.2.2.1 hx
    have hx_niG : x ∉ st.cs.insertedGlobal := fun hm =>
      hx_niC (hI_t.hCE_ins C (hcs_G₀ ▸ hC) x hxC hm)
    have hx_nc : x ∉ st.cs.crossEdges :=
      hI_t.hNonIns_notCross C (hcs_G₀ ▸ hC) x hxC hx_niC
    exact ⟨hx_ce, hxC, hx_niC, hx_niG, hx_nc⟩
  have hSub : (coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur := by
    rw [← hGeq]; exact hSsub_st
  have hEmb : st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur := by
    refine ⟨?_, fun e he => ?_⟩
    · change st.cs.RF.R ⊆ st.S_cur.V
      rw [hSV_st]
    · by_cases heS : e ∈ st.S_cur.E
      · have hemb : st.emb e = [(e, true)] := by
          dsimp only [TreeCoreState.emb]; split_ifs; rfl
        rw [hemb]
        have hEnd := hSub.2.2 e heS
        exact MGraph.IsWalk.cons heS (by simp [MGraph.src, hEnd.1])
          (by simpa [MGraph.dst, hEnd.2] using MGraph.IsWalk.nil _)
      · by_cases hCex : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E
        · set C := hCex.choose
          have hCA : C ∈ st.activeComps := hCex.choose_spec.1
          have hC : C ∈ components G₀ := hAct_sub hCA
          have heC : e ∈ (st.ts C).C.E := hCex.choose_spec.2
          have hemb : st.emb e = piTotal (st.dyn (C, origB e)) e := by
            have he0 : e ∈ G₀.E :=
              (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
                ((hT₀ C hC).hCE_sub ((hC_props C hC).2.2.1 heC)))).1
            dsimp only [TreeCoreState.emb]
            split_ifs
            · rw [horig_st]; simp [origB, coreLen, safeLen, he0]; rfl
          rw [hemb]
          set b := origB e
          have hb_act : b ∈ actB C := Finset.mem_image_of_mem origB ((hC_props C hC).2.2.1 heC)
          have hb_dyn := (hC_props C hC).2.2.2.2 b
          have hb_sp := hDynSp_st C hC b
          have heG_b : e ∈ (st.dyn (C, b)).G.E := by
            rw [hb_dyn.2.2.1]; exact Finset.mem_filter.mpr ⟨heC, rfl⟩
          have hw_b : (st.dyn (C, b)).H.IsWalk ((st.dyn (C, b)).G.tail e)
              ((st.dyn (C, b)).G.head e) (piTotal (st.dyn (C, b)) e) := hb_sp.2.2.1.2 e heG_b
          have hT_C := (hC_props C hC).2.1
          have hCI_C := (hI_t.hCompLSF C (hcs_G₀ ▸ hC)).1
          have hw_lifted := isWalk_map (qToR (st.cs.compSt C) (st.ts C)) (fun e' he' => by
            have he'G : e' ∈ (st.dyn (C, b)).G.E := hb_sp.1.2.1 he'
            have he'C : e' ∈ (st.ts C).C.E := hb_dyn.2.1.2.1 he'G
            have he'S : e' ∈ st.S_cur.E := by
              rw [hSE_st]
              exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_biUnion.mpr ⟨C, hCA, Finset.mem_biUnion.mpr ⟨b, hb_act, he'⟩⟩))
            obtain ⟨_, he'G_C, _, _, he'_nc⟩ := hC_compEdge C hC e' he'C
            have he'St := hCI_C.hG_val e' he'G_C
            have hEnds' := hT_C.hEnds e' he'C
            have hEndsG' := hI_t.hNonCross_ends C (hcs_G₀ ▸ hC) e' he'G_C he'_nc
            have hSubH' := hb_sp.1.2.2 e' he'
            have hSubC' := hb_dyn.2.1.2.2 e' he'G
            have hSubS' := hSub.2.2 e' he'S
            have htail : qToR (st.cs.compSt C) (st.ts C) ((st.dyn (C, b)).H.tail e') =
                st.S_cur.tail e' := by
              rw [hSubH'.1, hSubC'.1, hEnds'.1, qToR_eq_root hT_C he'St.1,
                ← compLSF_RF_root_eq hI_t (hcs_G₀ ▸ hC) he'St.1, hEndsG'.1, hSubS'.1]
              dsimp only [coreGraph]; rw [hGeq]; rfl
            have hhead : qToR (st.cs.compSt C) (st.ts C) ((st.dyn (C, b)).H.head e') =
                st.S_cur.head e' := by
              rw [hSubH'.2, hSubC'.2, hEnds'.2, qToR_eq_root hT_C he'St.2,
                ← compLSF_RF_root_eq hI_t (hcs_G₀ ▸ hC) he'St.2, hEndsG'.2, hSubS'.2]
              dsimp only [coreGraph]; rw [hGeq]; rfl
            exact ⟨he'S, htail, hhead⟩) hw_b
          obtain ⟨_, heG_C, _, _, he_nc⟩ := hC_compEdge C hC e heC
          have heSt := hCI_C.hG_val e heG_C
          have hEnds := hT_C.hEnds e heC
          have hEndsG := hI_t.hNonCross_ends C (hcs_G₀ ▸ hC) e heG_C he_nc
          have hSubC := hb_dyn.2.1.2.2 e heG_b
          have htail_e : qToR (st.cs.compSt C) (st.ts C) ((st.dyn (C, b)).G.tail e) =
              (coreGraph (D.G t) st.cs.lsf).tail e := by
            rw [hSubC.1, hEnds.1, qToR_eq_root hT_C heSt.1,
              ← compLSF_RF_root_eq hI_t (hcs_G₀ ▸ hC) heSt.1, hEndsG.1]
            dsimp only [coreGraph]; rw [hGeq]; rfl
          have hhead_e : qToR (st.cs.compSt C) (st.ts C) ((st.dyn (C, b)).G.head e) =
              (coreGraph (D.G t) st.cs.lsf).head e := by
            rw [hSubC.2, hEnds.2, qToR_eq_root hT_C heSt.2,
              ← compLSF_RF_root_eq hI_t (hcs_G₀ ▸ hC) heSt.2, hEndsG.2]
            dsimp only [coreGraph]; rw [hGeq]; rfl
          rwa [htail_e, hhead_e] at hw_lifted
        · have hemb : st.emb e = [] := by
            dsimp only [TreeCoreState.emb]; split_ifs; rfl
          rw [hemb]
          have he_nc : e ∉ st.cs.crossEdges := fun hc => heS (by
            rw [hSE_st]; exact Finset.mem_union_right _ hc)
          have he_G : e ∈ st.cs.G.E := by rw [hGeq]; exact (Finset.mem_sdiff.mp he).1
          obtain ⟨C, hC_G0, heC⟩ := hI_t.hEdge_cover e he_G he_nc
          have hC : C ∈ components G₀ := hcs_G₀ ▸ hC_G0
          have hna : C ∉ st.activeComps := by
            intro hCA
            have hnF : e ∉ (st.cs.compSt C).RF.F.E := fun heF =>
              (Finset.mem_sdiff.mp he).2
                (Finset.mem_biUnion.mpr ⟨C, hC_G0, heF⟩)
            have hnC : e ∉ (st.ts C).C.E := fun heT => hCex ⟨C, hCA, heT⟩
            exact heS (by
              rw [hSE_st]
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨C, hCA,
                  Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heC, hnF⟩, hnC⟩⟩)))
          have hNL : C ∉ largeComps k G₀ := fun hL => hna (hLarge_sub hL)
          have hcs_u := (hUnt C hC hna).1
          have hlt : 4 * (compGraph G₀ C).m < k := by
            by_contra hge
            push Not at hge
            have hm1 : 1 ≤ (compGraph G₀ C).m := by
              have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge; omega
            exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
          have hsm := initLSF_small_props hLSST hG₀ hℓs hk hC hlt j
          have he_ends := hI_t.hNonCross_ends C hC_G0 e heC he_nc
          have heC₀ : e ∈ (compGraph G₀ C).E := by
            rw [← (hS₀C_spec C hC).1, ← hcs_u]; exact heC
          have hroot₀ := hsm.2.2.2 e heC₀
          have hCI_C := (hI_t.hCompLSF C hC_G0).1
          have htV := (hCI_C.hG_val e heC).1
          have hhV := (hCI_C.hG_val e heC).2
          have hrt : st.cs.RF.root (st.cs.G.tail e) = st.cs.RF.root (st.cs.G.head e) := by
            rw [← he_ends.1, ← he_ends.2, compLSF_RF_root_eq hI_t hC_G0 htV,
              compLSF_RF_root_eq hI_t hC_G0 hhV, hcs_u, (hS₀C_spec C hC).1]
            exact hroot₀
          have hth_eq : (coreGraph (D.G t) st.cs.lsf).tail e =
              (coreGraph (D.G t) st.cs.lsf).head e := by
            dsimp only [coreGraph]; rw [← hGeq]; exact hrt
          rw [hth_eq]
          exact MGraph.IsWalk.nil _
  have hApprox : ∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ t) e) (coreLen st.cs.lsf (D.ℓ t) e') := by
    intro e he e' he'
    have hwstr_ge1 : ∀ x ∈ (D.G t).E, 1 ≤ st.cs.lsf.wstr x := by
      intro x hx
      have hℓt : ∀ y ∈ st.cs.G.E, 0 < D.ℓ t y := hGeq ▸ hℓ t ht
      have hℓo : ∀ y ∈ st.cs.G₀.E, y ∈ st.cs.G.E → y ∉ st.cs.insertedGlobal →
          D.ℓ t y = (D.ℓ 0) y := by
        intro y _ hy hni
        rw [hGeq] at hy
        rw [hcs_st, hbt.2.2.2.2.2.2.2.1, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at hni
        exact length_eq_init_of_not_batchesInserted hD hLen t ht y hy hni
      have hH := hI_t.to_Holds hℓt hℓo
      have hHw : st.cs.RF.stretch (D.G t) (D.ℓ t) x ≤ st.cs.lsf.wstr x := by
        have htmp := (hH.2.2.2 x (hGeq.symm ▸ hx)).1
        change st.cs.RF.stretch st.cs.G (D.ℓ t) x ≤ st.cs.lsf.wstr x at htmp
        rwa [hGeq] at htmp
      exact (one_le_stretch (hGeq ▸ (compLSF_RF_isRSF hI_t).2.2.2.2) (fun y hy => le_of_lt (hℓ t ht y hy)) hx).trans hHw
    have hcore_pos : ∀ x ∈ (D.G t).E, 0 < coreLen st.cs.lsf (D.ℓ t) x := by
      intro x hx; exact mul_pos (lt_of_lt_of_le zero_lt_one (hwstr_ge1 x hx)) (hℓ t ht x hx)
    by_cases heS : e ∈ st.S_cur.E
    · have hemb : st.emb e = [(e, true)] := by
        dsimp only [TreeCoreState.emb]; split_ifs; rfl
      rw [hemb, walkEdges] at he'
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.mem_singleton] at he'
      rw [he']
      have hp := hcore_pos e (Finset.mem_sdiff.mp he).1
      exact ⟨hp, hp, by linarith, by linarith⟩
    · by_cases hCex : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E
      · set C := hCex.choose
        have hC : C ∈ components G₀ := hAct_sub hCex.choose_spec.1
        have heC : e ∈ (st.ts C).C.E := hCex.choose_spec.2
        have hemb : st.emb e = piTotal (st.dyn (C, origB e)) e := by
          have he0 : e ∈ G₀.E :=
            (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
              ((hT₀ C hC).hCE_sub ((hC_props C hC).2.2.1 heC)))).1
          dsimp only [TreeCoreState.emb]; split_ifs
          rw [horig_st]; simp [origB, coreLen, safeLen, he0]; rfl
        rw [hemb] at he'
        set b := origB e
        have hb_dyn := (hC_props C hC).2.2.2.2 b
        have hb_sp := hDynSp_st C hC b
        have heG_b : e ∈ (st.dyn (C, b)).G.E := by
          rw [hb_dyn.2.2.1]; exact Finset.mem_filter.mpr ⟨heC, rfl⟩
        have he'_H : e' ∈ (st.dyn (C, b)).H.E :=
          walkEdges_subset_of_isWalk (hb_sp.2.2.1.2 e heG_b) he'
        have he'_G : e' ∈ (st.dyn (C, b)).G.E := hb_sp.1.2.1 he'_H
        have he'_C : e' ∈ (st.ts C).C.E := hb_dyn.2.1.2.1 he'_G
        have hb_e' : origB e' = b := by
          rw [hb_dyn.2.2.1, Finset.mem_filter] at he'_G; exact he'_G.2
        obtain ⟨_, heG_C, _, he_niG, _⟩ := hC_compEdge C hC e heC
        obtain ⟨_, he'G_C, _, he'_niG, _⟩ := hC_compEdge C hC e' he'_C
        have he_ni : e ∉ batchesInserted (dynBatches D t) := by
          rwa [hcs_st, hbt.2.2.2.2.2.2.2.1, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he_niG
        have he'_ni : e' ∉ batchesInserted (dynBatches D t) := by
          rwa [hcs_st, hbt.2.2.2.2.2.2.2.1, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten] at he'_niG
        have he_Dt : e ∈ (D.G t).E := (Finset.mem_sdiff.mp he).1
        have he'_Dt : e' ∈ (D.G t).E := hGeq ▸ (hI_t.hCE_sub C (hcs_G₀ ▸ hC) he'G_C)
        have hℓ_e : D.ℓ t e = D.ℓ 0 e :=
          length_eq_init_of_not_batchesInserted hD hLen t ht e he_Dt he_ni
        have hℓ_e' : D.ℓ t e' = D.ℓ 0 e' :=
          length_eq_init_of_not_batchesInserted hD hLen t ht e' he'_Dt he'_ni
        have hw_e : st.cs.lsf.wstr e = cs₀.lsf.wstr e := by
          change st.cs.wstrGlobal e = cs₀.wstrGlobal e
          rw [hcs_st, hbt.2.2.2.2.2.2.2.1]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D t).flatten
            (by rw [← hbt.2.2.2.2.2.2.2.1, hbt.2.2.2.2.2.2.2.2.2.1]; exact he_Dt)
            (by rw [← hbt.2.2.2.2.2.2.2.1, ← hcs_st]; exact he_niG)
        have hw_e' : st.cs.lsf.wstr e' = cs₀.lsf.wstr e' := by
          change st.cs.wstrGlobal e' = cs₀.wstrGlobal e'
          rw [hcs_st, hbt.2.2.2.2.2.2.2.1]
          exact compLSFBatch_wstr_eq_init_of_not_inserted cs₀ rfl (dynBatches D t).flatten
            (by rw [← hbt.2.2.2.2.2.2.2.1, hbt.2.2.2.2.2.2.2.2.2.1]; exact he'_Dt)
            (by rw [← hbt.2.2.2.2.2.2.2.1, ← hcs_st]; exact he'_niG)
        have hlen_e : coreLen st.cs.lsf (D.ℓ t) e = coreLen cs₀.lsf (D.ℓ 0) e := by
          unfold coreLen; rw [hw_e, hℓ_e]
        have hlen_e' : coreLen st.cs.lsf (D.ℓ t) e' = coreLen cs₀.lsf (D.ℓ 0) e' := by
          unfold coreLen; rw [hw_e', hℓ_e']
        rw [hlen_e, hlen_e']
        exact approx2_of_bucketOf_eq (hlen_e ▸ hcore_pos e he_Dt)
          (hlen_e' ▸ hcore_pos e' he'_Dt) (by change origB e = origB e'; rw [hb_e'])
      · have hemb : st.emb e = [] := by
          dsimp only [TreeCoreState.emb]; split_ifs; rfl
        rw [hemb, walkEdges] at he'
        simp at he'
  have hLenEmb : (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b := by
    have h1 : (1 : ℝ) ≤ coreE82Len L P_b := by
      unfold coreE82Len
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
      have hγ := one_le_pow₀ P_b.hγ_ℓ (n := L + 1)
      nlinarith
    have hnat : ∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ((st.emb e).length : ℝ) ≤ coreE82Len L P_b := by
      intro e _
      by_cases heS : e ∈ st.S_cur.E
      · have hemb : st.emb e = [(e, true)] := by
          dsimp only [TreeCoreState.emb]; split_ifs; rfl
        rw [hemb]; simpa using h1
      · by_cases hCex : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E
        · set C := hCex.choose
          have hC : C ∈ components G₀ := hAct_sub hCex.choose_spec.1
          have heC : e ∈ (st.ts C).C.E := hCex.choose_spec.2
          have hemb : st.emb e = piTotal (st.dyn (C, origB e)) e := by
            have he0 : e ∈ G₀.E :=
              (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
                ((hT₀ C hC).hCE_sub ((hC_props C hC).2.2.1 heC)))).1
            dsimp only [TreeCoreState.emb]; split_ifs
            rw [horig_st]; simp [origB, coreLen, safeLen, he0]; rfl
          rw [hemb]
          set b := origB e
          have heG_b : e ∈ (st.dyn (C, b)).G.E := by
            rw [((hC_props C hC).2.2.2.2 b).2.2.1]; exact Finset.mem_filter.mpr ⟨heC, rfl⟩
          have hle_sup : (piTotal (st.dyn (C, b)) e).length ≤
              Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G :=
            Finset.le_sup (f := fun x => (piTotal (st.dyn (C, b)) x).length) heG_b
          exact le_trans (by exact_mod_cast hle_sup) (hDynSp_st C hC b).2.2.2.1
        · have hemb : st.emb e = [] := by
            dsimp only [TreeCoreState.emb]; split_ifs; rfl
          rw [hemb]; simp only [List.length_nil, Nat.cast_zero]; linarith
    by_cases hne : (coreGraph (D.G t) st.cs.lsf).E.Nonempty
    · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup _ hne (fun e => (st.emb e).length)
      change (((coreGraph (D.G t) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [heq]
      exact hnat e he
    · change (((coreGraph (D.G t) st.cs.lsf).E.sup fun e => (st.emb e).length : ℕ) : ℝ) ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sup_empty, bot_eq_zero', Nat.cast_zero]
      linarith
  have hCongBase :
      st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b *
          (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) ∧
      st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b * (2 * (M : ℝ)) := by
    have hE82_nn : 0 ≤ coreE82Cong L P_b := by
      unfold coreE82Cong; have := P_b.hγ_ℓ; have := P_b.hγ_c; positivity
    have hAt : ∀ e' ∈ st.S_cur.E,
        st.emb.econgAt (coreGraph (D.G t) st.cs.lsf) (fun _ => 1) (fun _ => 1) e' ≤
          1 + coreE82Cong L P_b *
            (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) ∧
        st.emb.econgAt (coreGraph (D.G t) st.cs.lsf) (fun _ => 1) (fun _ => 1) e' ≤
          1 + coreE82Cong L P_b * (2 * (M : ℝ)) := by
      intro e' he'
      unfold Embedding.econgAt
      rw [div_one]
      have hS_filt : ∀ e, e ∈ (coreGraph (D.G t) st.cs.lsf).E →
          e' ∈ walkEdges (st.emb e) →
          e = e' ∨ ∃ C ∈ st.activeComps, e ∉ st.S_cur.E ∧ e ∈ (st.ts C).C.E ∧
            e' ∈ walkEdges (piTotal (st.dyn (C, origB e)) e) := by
        intro e _ hw
        by_cases heS : e ∈ st.S_cur.E
        · left
          have hemb : st.emb e = [(e, true)] := by
            dsimp only [TreeCoreState.emb]; split_ifs; rfl
          rw [hemb] at hw
          simp only [walkEdges, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
            insert_empty_eq, Finset.mem_singleton] at hw
          exact hw.symm
        · by_cases hCex : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E
          · right
            have hemb : st.emb e = piTotal (st.dyn (hCex.choose, origB e)) e := by
              have hC := hAct_sub hCex.choose_spec.1
              have he0 : e ∈ G₀.E :=
                (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
                  ((hT₀ _ hC).hCE_sub ((hC_props _ hC).2.2.1 hCex.choose_spec.2)))).1
              dsimp only [TreeCoreState.emb]; split_ifs
              rw [horig_st]; simp [origB, coreLen, safeLen, he0]
            exact ⟨hCex.choose, hCex.choose_spec.1, heS, hCex.choose_spec.2, hemb ▸ hw⟩
          · exfalso
            have hemb : st.emb e = [] := by
              dsimp only [TreeCoreState.emb]; split_ifs; rfl
            rw [hemb, walkEdges] at hw
            simp at hw
      rw [hSE_st] at he'
      rcases Finset.mem_union.mp he' with he'12 | he'X
      · rcases Finset.mem_union.mp he'12 with he'B | he'Ex
        · rw [Finset.mem_biUnion] at he'B
          rcases he'B with ⟨C, hCA, he'BC⟩
          rw [Finset.mem_biUnion] at he'BC
          rcases he'BC with ⟨b, _, he'H⟩
          have hC : C ∈ components G₀ := hAct_sub hCA
          have hb_dyn := (hC_props C hC).2.2.2.2 b
          have hb_sp := hDynSp_st C hC b
          have he'G : e' ∈ (st.dyn (C, b)).G.E := hb_sp.1.2.1 he'H
          have he'C : e' ∈ (st.ts C).C.E := hb_dyn.2.1.2.1 he'G
          have he'CE : e' ∈ compEdgeSet G₀ C := (hC_compEdge C hC e' he'C).1
          have hb_e' : origB e' = b := by
            rw [hb_dyn.2.2.1, Finset.mem_filter] at he'G; exact he'G.2
          have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)) ⊆
              insert e' ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e))) := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨C', hC'A, _, heC', hw⟩
            · exact Finset.mem_insert_self _ _
            · have hC' : C' ∈ components G₀ := hAct_sub hC'A
              set b' := origB e
              have hb'_dyn := (hC_props C' hC').2.2.2.2 b'
              have hb'_sp := hDynSp_st C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by
                rw [hb'_dyn.2.2.1]; exact Finset.mem_filter.mpr ⟨heC', rfl⟩
              have he'_H' : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hb'_sp.2.2.1.2 e he_G') hw
              have he'_G' : e' ∈ (st.dyn (C', b')).G.E := hb'_sp.1.2.1 he'_H'
              have he'_C' : e' ∈ (st.ts C').C.E := hb'_dyn.2.1.2.1 he'_G'
              have he'_CE' : e' ∈ compEdgeSet G₀ C' := (hC_compEdge C' hC' e' he'_C').1
              have hC_eq : C' = C := by
                by_contra hne
                exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC' hC hne) he'_CE' he'CE
              subst hC_eq
              have hb'_eq : b' = b := by
                rw [hb'_dyn.2.2.1, Finset.mem_filter] at he'_G'
                exact he'_G'.2.symm.trans hb_e'
              subst hb'_eq
              exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he_G', hw⟩)
          have hsum_le : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤
              1 + (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)),
                (1 : ℝ)) := by
            calc (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter _, (1 : ℝ))
                ≤ ∑ _e ∈ insert e' ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e))),
                    (1 : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
              _ ≤ 1 + ∑ _e ∈ (st.dyn (C, b)).G.E.filter _, (1 : ℝ) := by
                  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
                  have hcard := Finset.card_insert_le e'
                    ((st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)))
                  exact_mod_cast (show _ ≤ 1 + _ from by omega)
          have hvc : (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)), (1 : ℝ)) ≤
              (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := by
            have hea := econgAt_le_vcongAt_tail hb_sp.2.2.1 he'H
            unfold Embedding.econgAt at hea
            rw [div_one] at hea
            have hv_sup : (piTotal (st.dyn (C, b))).vcongAt (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1)
                ((st.dyn (C, b)).H.tail e') ≤
                (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := by
              have hvt : (st.dyn (C, b)).H.tail e' ∈ (st.dyn (C, b)).H.V := by
                rw [(hb_sp.1.2.2 e' he'H).1]
                exact hb_sp.2.2.1.1 (hb_dyn.1 e' he'G).1
              dsimp only [Embedding.vcong]
              split_ifs with hne
              · exact Finset.le_sup' _ hvt
              · exact absurd ⟨_, hvt⟩ hne
            exact le_trans hea hv_sup
          have hvc1 : (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)), (1 : ℝ)) ≤
              coreE82Cong L P_b *
                (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) :=
            calc _ ≤ (piTotal (st.dyn (C, b))).vcong (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) := hvc
              _ ≤ coreE82Cong L P_b * ((ts₀ C).C.maxDeg : ℝ) := hb_sp.2.2.2.2.1
              _ ≤ coreE82Cong L P_b *
                    (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) := by
                  gcongr
                  exact Finset.le_sup (f := fun C => (tildeC0Base (cs₀.compSt C)).maxDeg) hC
          have hvc2 : (∑ _e ∈ (st.dyn (C, b)).G.E.filter (fun e => e' ∈ walkEdges (piTotal (st.dyn (C, b)) e)), (1 : ℝ)) ≤
              coreE82Cong L P_b * (2 * (M : ℝ)) :=
            le_trans hvc hb_sp.2.2.2.2.2
          exact ⟨by linarith, by linarith⟩
        · have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)) ⊆
              {e'} := by
            intro e he
            rw [Finset.mem_filter] at he
            rcases hS_filt e he.1 he.2 with rfl | ⟨C', hC'A, _, heC', hw⟩
            · exact Finset.mem_singleton_self _
            · exfalso
              have hC' : C' ∈ components G₀ := hAct_sub hC'A
              set b' := origB e
              have hb'_dyn := (hC_props C' hC').2.2.2.2 b'
              have hb'_sp := hDynSp_st C' hC' b'
              have he_G' : e ∈ (st.dyn (C', b')).G.E := by
                rw [hb'_dyn.2.2.1]; exact Finset.mem_filter.mpr ⟨heC', rfl⟩
              have he'H : e' ∈ (st.dyn (C', b')).H.E :=
                walkEdges_subset_of_isWalk (hb'_sp.2.2.1.2 e he_G') hw
              have he'C' : e' ∈ (st.ts C').C.E := hb'_dyn.2.1.2.1 (hb'_sp.1.2.1 he'H)
              obtain ⟨he'_CE', _, _, he'_niG, _⟩ := hC_compEdge C' hC' e' he'C'
              rw [Finset.mem_biUnion] at he'Ex
              rcases he'Ex with ⟨C, hCA, he'ExC⟩
              have hC : C ∈ components G₀ := hAct_sub hCA
              have he'G_C : e' ∈ (st.cs.compSt C).G.E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he'ExC).1).1
              have he'_niC : e' ∉ (st.cs.compSt C).insertedEdges := fun hm =>
                he'_niG (hI_t.hCompIns_sub C (hcs_G₀ ▸ hC) hm)
              have he'_CE : e' ∈ compEdgeSet G₀ C := by
                have hs := ((hI_t.hCompLSF C (hcs_G₀ ▸ hC)).1.hsurv_edge e' he'G_C he'_niC).1
                rwa [(hI_t.hCompLSF C (hcs_G₀ ▸ hC)).2.1, hcs_G₀] at hs
              have hEq : C = C' := by
                by_contra hne
                exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC hC' hne) he'_CE he'_CE'
              subst hEq
              exact (Finset.mem_sdiff.mp he'ExC).2 he'C'
          have hsum_le1 : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
              (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
            calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
              _ = 1 := by simp
          have hdeg_nn1 : 0 ≤ coreE82Cong L P_b *
              (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) :=
            mul_nonneg hE82_nn (Nat.cast_nonneg _)
          have hdeg_nn2 : 0 ≤ coreE82Cong L P_b * (2 * (M : ℝ)) :=
            mul_nonneg hE82_nn (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          exact ⟨le_trans hsum_le1 (by linarith), le_trans hsum_le1 (by linarith)⟩
      · have hfilt_sub : (coreGraph (D.G t) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)) ⊆
            {e'} := by
          intro e he
          rw [Finset.mem_filter] at he
          rcases hS_filt e he.1 he.2 with rfl | ⟨C', hC'A, _, heC', hw⟩
          · exact Finset.mem_singleton_self _
          · exfalso
            have hC' : C' ∈ components G₀ := hAct_sub hC'A
            set b' := origB e
            have hb'_dyn := (hC_props C' hC').2.2.2.2 b'
            have hb'_sp := hDynSp_st C' hC' b'
            have he_G' : e ∈ (st.dyn (C', b')).G.E := by
              rw [hb'_dyn.2.2.1]; exact Finset.mem_filter.mpr ⟨heC', rfl⟩
            have he'H : e' ∈ (st.dyn (C', b')).H.E :=
              walkEdges_subset_of_isWalk (hb'_sp.2.2.1.2 e he_G') hw
            have he'C' : e' ∈ (st.ts C').C.E := hb'_dyn.2.1.2.1 (hb'_sp.1.2.1 he'H)
            exact (hC_compEdge C' hC' e' he'C').2.2.2.1 (hI_t.hCross_sub he'X)
        have hsum_le1 : (∑ _e ∈ (coreGraph (D.G t) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)), (1 : ℝ)) ≤ 1 := by
          calc _ ≤ ∑ _e ∈ ({e'} : Finset ℕ), (1 : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub (fun _ _ _ => zero_le_one)
            _ = 1 := by simp
        have hdeg_nn1 : 0 ≤ coreE82Cong L P_b *
            (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) :=
          mul_nonneg hE82_nn (Nat.cast_nonneg _)
        have hdeg_nn2 : 0 ≤ coreE82Cong L P_b * (2 * (M : ℝ)) :=
          mul_nonneg hE82_nn (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        exact ⟨le_trans hsum_le1 (by linarith), le_trans hsum_le1 (by linarith)⟩
    unfold Embedding.econg
    split_ifs with hE
    · refine ⟨(Finset.sup'_le_iff _ _).mpr fun e' he' => (hAt e' he').1,
        (Finset.sup'_le_iff _ _).mpr fun e' he' => (hAt e' he').2⟩
    · exact ⟨by positivity, by positivity⟩
  have hCard : ∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
      (st.S_cur.E.card : ℝ) ≤ ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
        (B_bound : ℝ) * (2 * (G₀.maxDeg : ℝ) + 190) + 115) *
        (M : ℝ) / (k : ℝ) := by
    intro B_bound hB_bound
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hN_pos : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
    have hq_sub : Finset.Icc 1 t ⊆ Finset.Icc 1 τ := fun s hs => by
      simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 ht⟩
    have hq_t_le_div : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        (M : ℝ) / (k : ℝ) :=
      le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hq_sub)
        (q_sum_le_M_div_k hk hN_pos hThresh)
    have hR_diff := compLSF_R_diff_le oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j t ht
    have hR_cs : st.cs.RF.R \ cs₀.RF.R =
        (compLSFBatch cs₀ (dynBatches D t).flatten).RF.R \ cs₀.RF.R := by
      rw [hcs_st, hbt.2.2.2.2.2.2.2.1]
    have hR_le : ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
      rw [hR_cs]; exact hR_diff.2.2
    obtain ⟨hEx_le, hV_diff, hV_mono⟩ := extraSet_and_tildeV_run_le oracle C_lsst L sparsify hLSST
      k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j t ht
    have hEx_le' : (components G₀).sum (fun C => (extraSet (st.cs.compSt C) (st.ts C)).card) ≤
        2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) + (st.cs.RF.R \ cs₀.RF.R).card := by
      rw [hcs_st, hts_st]; exact hEx_le
    have hV_diff' : (components G₀).sum (fun C => (st.ts C).C.V.card - (ts₀ C).C.V.card) ≤
        2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) * (G₀.maxDeg + 1) +
          (st.cs.RF.R \ cs₀.RF.R).card := by
      rw [hcs_st, hts_st]; exact hV_diff
    have hV_mono' : ∀ C ∈ components G₀, (ts₀ C).C.V.card ≤ (st.ts C).C.V.card := fun C hC => by
      rw [hts_st]; exact hV_mono C hC
    have hCross_le : (st.cs.crossEdges.card : ℝ) ≤ (M : ℝ) / (k : ℝ) := by
      have hc := compLSF_crossEdges_run_le oracle C_lsst L sparsify k M N D j t
      rw [← hcs_st] at hc
      exact le_trans (by exact_mod_cast hc) hq_t_le_div
    have hEx_card : ((st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card : ℝ) ≤
        114 * (M : ℝ) / (k : ℝ) := by
      have hsub1 : (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card ≤
          (components G₀).sum fun C => (extraSet (st.cs.compSt C) (st.ts C)).card :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum_of_subset hAct_sub)
      have hR1 : ((st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card : ℝ) ≤
          2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) +
            ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) := by
        exact_mod_cast le_trans hsub1 hEx_le'
      calc ((st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card : ℝ)
          ≤ 2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) +
              ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) := hR1
        _ ≤ 2 * ((M : ℝ) / (k : ℝ)) + 112 * (M : ℝ) / (k : ℝ) := by linarith
        _ = 114 * (M : ℝ) / (k : ℝ) := by ring
    have hDyn_Hm : ∀ C ∈ components G₀, ∀ b ∈ actB C,
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.ts C).C.V.card : ℝ) *
          P_b.γ_ℓ * coreLambdaS P_b M := by
      intro C hC b _
      have hsp_b := hDynSp_st C hC b
      have hG_sub := (hC_props C hC).2.2.2.2 b
      have hn_le_V : ((st.dyn (C, b)).G.n : ℝ) ≤ ((st.ts C).C.V.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hG_sub.2.1.1
      have hcoeff_nn : 0 ≤ (L + 1 : ℝ) * P_b.K_s := by
        have := P_b.hK_s; positivity
      have hpost_nn : 0 ≤ P_b.γ_ℓ * coreLambdaS P_b M := by
        have := P_b.hγ_ℓ; have := coreLambdaS_ge_one P_b M; positivity
      calc ((st.dyn (C, b)).H.m : ℝ)
          ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ * coreLambdaS P_b M :=
              hsp_b.2.1
        _ = ((L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ)) * (P_b.γ_ℓ * coreLambdaS P_b M) := by ring
        _ ≤ ((L + 1 : ℝ) * P_b.K_s * ((st.ts C).C.V.card : ℝ)) * (P_b.γ_ℓ * coreLambdaS P_b M) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_le_V hcoeff_nn) hpost_nn
        _ = _ := by ring
    have hts_sum : (st.activeComps.sum fun C => ((st.ts C).C.V.card : ℝ)) ≤
        (2 * (G₀.maxDeg : ℝ) + 190) * (M : ℝ) / (k : ℝ) := by
      have hts_le_each : ∀ C ∈ components G₀,
          ((st.ts C).C.V.card : ℝ) = ((ts₀ C).C.V.card : ℝ) +
            (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ) := fun C hC => by
        have hm := hV_mono' C hC
        have : (ts₀ C).C.V.card + ((st.ts C).C.V.card - (ts₀ C).C.V.card) = (st.ts C).C.V.card :=
          Nat.add_sub_of_le hm
        exact_mod_cast this.symm
      have hsplit_act : st.activeComps ⊆ largeComps k G₀ ∪ (st.activeComps \ largeComps k G₀) := by
        intro C hC
        by_cases hL_c : C ∈ largeComps k G₀
        · exact Finset.mem_union_left _ hL_c
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hC, hL_c⟩)
      have hL_sum : ((largeComps k G₀).sum fun C => ((ts₀ C).C.V.card : ℝ)) ≤
          54 * (M : ℝ) / (k : ℝ) := by
        calc (largeComps k G₀).sum (fun C => ((ts₀ C).C.V.card : ℝ))
            ≤ (largeComps k G₀).sum (fun C => 54 * ((compGraph G₀ C).m : ℝ) / (k : ℝ)) :=
                Finset.sum_le_sum fun C hC =>
                  initLSF_large_tildeV_le hLSST hG₀ hℓs hk hC j
          _ = 54 * (((largeComps k G₀).sum fun C => (compGraph G₀ C).m : ℕ) : ℝ) / (k : ℝ) := by
                push_cast [Finset.mul_sum, Finset.sum_div]; ring
          _ ≤ 54 * (M : ℝ) / (k : ℝ) := by
                have hm_sub : (largeComps k G₀).sum (fun C => (compGraph G₀ C).m) ≤ M :=
                  le_trans (le_trans (Finset.sum_le_sum_of_subset largeComps_sub) (components_sum_m G₀ hG₀).le) hM
                have hk_nn : (0 : ℝ) < (k : ℝ) := hk_pos
                have hm_r : (((largeComps k G₀).sum fun C => (compGraph G₀ C).m : ℕ) : ℝ) ≤ M := by
                  exact_mod_cast hm_sub
                gcongr
      have hS_sum : ((st.activeComps \ largeComps k G₀).sum fun C => ((ts₀ C).C.V.card : ℝ)) ≤
          22 * (M : ℝ) / (k : ℝ) := by
        have hSmall_11 : ∀ C ∈ st.activeComps \ largeComps k G₀, ((ts₀ C).C.V.card : ℝ) ≤ 11 := by
          intro C hC
          rcases Finset.mem_sdiff.mp hC with ⟨hCA, hNL⟩
          exact_mod_cast hSmall C (hAct_sub hCA) hNL
        have hCard_act := hact_st ▸ hst.2.2.2.2.2.2.1
        calc (st.activeComps \ largeComps k G₀).sum (fun C => ((ts₀ C).C.V.card : ℝ))
            ≤ (st.activeComps \ largeComps k G₀).sum (fun _ => (11 : ℝ)) := Finset.sum_le_sum hSmall_11
          _ = 11 * ((st.activeComps \ largeComps k G₀).card : ℝ) := by
                simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
          _ ≤ 11 * (2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
                have hc : ((st.activeComps \ largeComps k G₀).card : ℝ) ≤
                    2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
                  exact_mod_cast hCard_act
                linarith
          _ ≤ 11 * (2 * ((M : ℝ) / (k : ℝ))) := by linarith
          _ = 22 * (M : ℝ) / (k : ℝ) := by ring
      have hDiff_sum : ((components G₀).sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) ≤
          (2 * (G₀.maxDeg : ℝ) + 114) * (M : ℝ) / (k : ℝ) := by
        have hR1 : ((components G₀).sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) ≤
            2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) * ((G₀.maxDeg : ℝ) + 1) +
              ((st.cs.RF.R \ cs₀.RF.R).card : ℝ) := by
          exact_mod_cast hV_diff'
        have hΔ_nn : (0 : ℝ) ≤ (G₀.maxDeg : ℝ) + 1 := by positivity
        have hmul_q := mul_le_mul_of_nonneg_right hq_t_le_div hΔ_nn
        calc ((components G₀).sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ))
            ≤ 2 * ((M : ℝ) / (k : ℝ)) * ((G₀.maxDeg : ℝ) + 1) + 112 * (M : ℝ) / (k : ℝ) := by linarith
          _ = (2 * (G₀.maxDeg : ℝ) + 114) * (M : ℝ) / (k : ℝ) := by ring
      calc (st.activeComps.sum fun C => ((st.ts C).C.V.card : ℝ))
          = st.activeComps.sum (fun C => ((ts₀ C).C.V.card : ℝ) +
              (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) :=
              Finset.sum_congr rfl fun C hC => hts_le_each C (hAct_sub hC)
        _ = (st.activeComps.sum fun C => ((ts₀ C).C.V.card : ℝ)) +
              (st.activeComps.sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) :=
              Finset.sum_add_distrib
        _ ≤ ((largeComps k G₀ ∪ (st.activeComps \ largeComps k G₀)).sum fun C => ((ts₀ C).C.V.card : ℝ)) +
              ((components G₀).sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) := by
              refine add_le_add ?_ ?_
              · exact Finset.sum_le_sum_of_subset_of_nonneg hsplit_act (fun _ _ _ => Nat.cast_nonneg _)
              · exact Finset.sum_le_sum_of_subset_of_nonneg hAct_sub (fun _ _ _ => Nat.cast_nonneg _)
        _ = ((largeComps k G₀).sum fun C => ((ts₀ C).C.V.card : ℝ)) +
              ((st.activeComps \ largeComps k G₀).sum fun C => ((ts₀ C).C.V.card : ℝ)) +
              ((components G₀).sum fun C => (((st.ts C).C.V.card - (ts₀ C).C.V.card : ℕ) : ℝ)) := by
              rw [Finset.sum_union (Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 h1)]
        _ ≤ 54 * (M : ℝ) / (k : ℝ) + 22 * (M : ℝ) / (k : ℝ) +
              (2 * (G₀.maxDeg : ℝ) + 114) * (M : ℝ) / (k : ℝ) := by
              linarith
        _ = (2 * (G₀.maxDeg : ℝ) + 190) * (M : ℝ) / (k : ℝ) := by ring
    have hDyn_sum : ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) ≤
        ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (B_bound : ℝ) *
          (2 * (G₀.maxDeg : ℝ) + 190)) * (M : ℝ) / (k : ℝ) := by
      set C0 := (L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M
      have hC0_nn : 0 ≤ C0 := by
        have := P_b.hK_s; have := P_b.hγ_ℓ; have := coreLambdaS_ge_one P_b M; positivity
      have hcard_le : (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card ≤
          st.activeComps.sum fun C => (actB C).sum fun b => (st.dyn (C, b)).H.m :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
      have hR1 : ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) ≤
          st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).H.m : ℝ) := by
        exact_mod_cast hcard_le
      have hR2 : (st.activeComps.sum fun C => (actB C).sum fun b => ((st.dyn (C, b)).H.m : ℝ)) ≤
          st.activeComps.sum fun C => (B_bound : ℝ) * (C0 * ((st.ts C).C.V.card : ℝ)) := by
        refine Finset.sum_le_sum fun C hCA => ?_
        have hC := hAct_sub hCA
        calc (actB C).sum (fun b => ((st.dyn (C, b)).H.m : ℝ))
            ≤ (actB C).sum (fun _ => C0 * ((st.ts C).C.V.card : ℝ)) :=
                Finset.sum_le_sum fun b hb => by
                  have := hDyn_Hm C hC b hb
                  dsimp only [C0]; linarith
          _ = ((actB C).card : ℝ) * (C0 * ((st.ts C).C.V.card : ℝ)) := by
                simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (B_bound : ℝ) * (C0 * ((st.ts C).C.V.card : ℝ)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C hC)
                  (mul_nonneg hC0_nn (Nat.cast_nonneg _))
      have hR3 : (st.activeComps.sum fun C => (B_bound : ℝ) * (C0 * ((st.ts C).C.V.card : ℝ))) =
          (C0 * (B_bound : ℝ)) * (st.activeComps.sum fun C => ((st.ts C).C.V.card : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => by ring
      have hCB_nn : 0 ≤ C0 * (B_bound : ℝ) := mul_nonneg hC0_nn (Nat.cast_nonneg _)
      calc ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ)
          ≤ (C0 * (B_bound : ℝ)) * (st.activeComps.sum fun C => ((st.ts C).C.V.card : ℝ)) :=
              le_trans hR1 (le_trans hR2 (le_of_eq hR3))
        _ ≤ (C0 * (B_bound : ℝ)) * ((2 * (G₀.maxDeg : ℝ) + 190) * (M : ℝ) / (k : ℝ)) :=
              mul_le_mul_of_nonneg_left hts_sum hCB_nn
        _ = (C0 * (B_bound : ℝ) * (2 * (G₀.maxDeg : ℝ) + 190)) * (M : ℝ) / (k : ℝ) := by ring
    have hS_union : st.S_cur.E.card ≤
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card +
        (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card +
        st.cs.crossEdges.card := by
      rw [hSE_st]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h1 : (st.S_cur.E.card : ℝ) ≤
        ((st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E).card : ℝ) +
        ((st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)).card : ℝ) +
        (st.cs.crossEdges.card : ℝ) := by exact_mod_cast hS_union
    calc (st.S_cur.E.card : ℝ)
        ≤ ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (B_bound : ℝ) *
            (2 * (G₀.maxDeg : ℝ) + 190)) * (M : ℝ) / (k : ℝ) +
          114 * (M : ℝ) / (k : ℝ) + (M : ℝ) / (k : ℝ) := by linarith
      _ = ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (B_bound : ℝ) *
            (2 * (G₀.maxDeg : ℝ) + 190) + 115) * (M : ℝ) / (k : ℝ) := by ring
  refine ⟨hSub, hEmb, hApprox, hLenEmb, hCongBase.1, hCongBase.2, hCard⟩

theorem treeRunSeq_isSparsifiedCoreGraph
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
    (j : ℕ) (hj : j < k) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
    ∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      (coreGraph (D.G t) st.cs.lsf).IsSubgraph st.S_cur ∧
      st.emb.IsEmbedding (coreGraph (D.G t) st.cs.lsf) st.S_cur ∧
      (∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
        approx2 (coreLen st.cs.lsf (D.ℓ t) e) (coreLen st.cs.lsf (D.ℓ t) e')) ∧
      (st.emb.length (coreGraph (D.G t) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b ∧
      st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b *
          (((components G₀).sup fun C => (tildeC0Base (cs₀.compSt C)).maxDeg : ℕ) : ℝ) ∧
      st.emb.econg (coreGraph (D.G t) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
        1 + coreE82Cong L P_b * (2 * (M : ℝ)) ∧
      (∀ B_bound : ℕ, (∀ C ∈ components G₀, (actB C).card ≤ B_bound) →
        (st.S_cur.E.card : ℝ) ≤ ((L + 1 : ℝ) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
          (B_bound : ℝ) * (2 * (G₀.maxDeg : ℝ) + 190) + 115) *
          (M : ℝ) / (k : ℝ)) := by
  intro G₀ ℓ₀ cs₀ ts₀ origB actB t ht
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e := hℓ 0 (Nat.zero_le τ)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    simpa [safeLen, he] using hℓ₀ e he
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hHb := fun C hC b => initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hS₀C_spec C hC).2 b
  obtain ⟨hBase, hStep, hFlat⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, _, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hbt := hBase t ht
  have hst := hStage_all t ht
  have hGn_le_nMax : ∀ C ∈ components G₀, ∀ b : ℤ,
      ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n ≤ coreNMax M := by
    intro C hC b
    have hfb := hFlat C hC b
    have hPref : ∀ s ≤ τ,
        let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
        let pref := (Us_b.take s).flatten
        (initBucketGraph (cs₀.compSt C) ℓ₀ b).BatchIsValid pref ∧
        (initBucketGraph (cs₀.compSt C) ℓ₀ b).applyBatch pref =
          ((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.dyn (C, b)).G := by
      intro s
      induction s with
      | zero => intro _; exact ⟨trivial, rfl⟩
      | succ s ih =>
        intro hs_le
        have hs_lt : s < τ := hs_le
        obtain ⟨hBV_p, hG_p⟩ := ih (Nat.le_of_succ_le hs_le)
        have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_lt
        have htake : ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take (s + 1)).flatten =
            ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take s).flatten ++
              (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                (D.U (s + 1))).U_b (C, b) := by
          rw [take_succ_of_getElem? hget, List.flatten_append]; simp
        have hBV_step := ((hStep s hs_lt).2.2.2 C hC).2.2.2.2 b |>.1
        have hG_step := ((hStep s hs_lt).2.2.2 C hC).2.2.2.2 b |>.2.1
        refine ⟨?_, ?_⟩
        · rw [htake, batchIsValid_append]; exact ⟨hBV_p, hG_p ▸ hBV_step⟩
        · rw [htake, applyBatch_append, hG_p, ← hG_step]
    have hcat : ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten ++
        ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).drop t).flatten =
        (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have hds_pref : ∀ op ∈ ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten,
        isDelOrSplit op := fun op hop => hfb.2.1 op (by rw [← hcat, List.mem_append]; exact Or.inl hop)
    have hsc_pref : batchSplitCount ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten ≤
        batchSplitCount (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).flatten := by
      rw [← hcat, batchSplitCount_append]; omega
    have hv : ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n ≤
        (initBucketGraph (cs₀.compSt C) ℓ₀ b).n +
          batchSplitCount ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten := by
      unfold MGraph.n; rw [← (hPref t ht).2]
      exact (applyBatch_V_card_eq_of_isDelOrSplit (hPref t ht).1 hds_pref).le
    have hHb_n : (initBucketGraph (cs₀.compSt C) ℓ₀ b).n ≤ 2 * M := by
      have hm2 := (hHb C hC b).2.2.2.2.2.2.2.1
      have h3 : (cs₀.compSt C).G.m ≤ M := le_trans (by rw [(hS₀C_spec C hC).1]; exact compGraph_m_le) hM
      exact le_trans (hHb C hC b).2.2.2.2.1 (Nat.mul_le_mul_left 2 (le_trans hm2 h3))
    have hSplitB := splitB_le_coreSplitMax_at hk (le_trans (Finset.card_pos.mpr hV₀) hN) hM
    have hfb_sc : batchSplitCount (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).flatten ≤
        Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
          Nat.ceil (56 * (M : ℝ) / (k : ℝ)) := hfb.2.2
    have hsb1 : batchSplitCount ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten ≤
        coreSplitMax M := le_trans hsc_pref (le_trans hfb_sc hSplitB)
    unfold coreNMax
    omega
  refine treeCoreState_isSparsifiedCoreGraph oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D
    hG₀ hV₀ hD hℓ hLen hM hN hThresh hSp j hj t ht _ hbt.2.2.2.2.1 rfl rfl rfl
    hst.2.1 hst.2.2.1 hst.2.2.2.1 (fun C hC b => ?_) (fun C hC b => ?_)
  · have hb_dyn := (hbt.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b
    exact ⟨hb_dyn.1, hb_dyn.2.1, hb_dyn.2.2.1, hGn_le_nMax C hC b⟩
  · have hsp_b := hst.2.2.2.2.2.2.2 C hC b
    have hHb_m : (initBucketGraph (cs₀.compSt C) ℓ₀ b).m ≤ M := by
      have hm2 : (initBucketGraph (cs₀.compSt C) ℓ₀ b).m ≤ (cs₀.compSt C).G.m :=
        (hHb C hC b).2.2.2.2.2.2.2.1
      have h3 : (cs₀.compSt C).G.m ≤ M := le_trans (by rw [(hS₀C_spec C hC).1]; exact compGraph_m_le) hM
      exact le_trans hm2 h3
    have hGn_le : (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n : ℝ) ≤
        (coreNMax M : ℝ) := by
      exact_mod_cast hGn_le_nMax C hC b
    have hlam_le : (1 + Real.log ((((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n : ℝ) +
          ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) + 2)) ^ P_b.p_s ≤ coreLambdaS P_b M := by
      have harg1 : (1 : ℝ) ≤ (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n : ℝ) +
          ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n),
          Nat.cast_nonneg (α := ℝ) (initBucketGraph (cs₀.compSt C) ℓ₀ b).m]
      have hlog_nn : 0 ≤ 1 + Real.log ((((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n : ℝ) +
          ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) + 2) := by linarith [Real.log_nonneg harg1]
      have h2m : ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hHb_m
      unfold coreLambdaS
      exact pow_le_pow_left₀ hlog_nn (add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))) _
    have hpre_nn : 0 ≤ (L + 1 : ℝ) * P_b.K_s *
        (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ := by
      have := P_b.hK_s; have := P_b.hγ_ℓ; positivity
    have hE82_nn : 0 ≤ coreE82Cong L P_b := by
      unfold coreE82Cong; have := P_b.hγ_ℓ; have := P_b.hγ_c; positivity
    have hdeg1 : (initBucketGraph (cs₀.compSt C) ℓ₀ b).maxDeg ≤ (tildeC0Base (cs₀.compSt C)).maxDeg :=
      (hHb C hC b).2.2.2.2.2.2.2.2
    have hdeg2 : (initBucketGraph (cs₀.compSt C) ℓ₀ b).maxDeg ≤ 2 * M := by
      have := maxDeg_le_two_m (initBucketGraph (cs₀.compSt C) ℓ₀ b); omega
    refine ⟨hsp_b.1, le_trans hsp_b.2.1 (mul_le_mul_of_nonneg_left hlam_le hpre_nn),
      hsp_b.2.2.2.1, hsp_b.2.2.2.2.1, ?_, ?_⟩
    · exact le_trans hsp_b.2.2.2.2.2
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg1) hE82_nn)
    · exact le_trans hsp_b.2.2.2.2.2
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg2) hE82_nn)

end

end MinCostFlow.SparseCore
