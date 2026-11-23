module

public import MinCostFlow.DynSpanner.Invariant

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rebuild step specifications (Theorem 8.1 calls in Algorithm 6)

This file establishes the exact invariants proved at each sparsification call of Algorithm 6:
* `initCore_spec`: validity, subgraph/embedding invariants, `length` (`lenBound γ_ℓ 0`),
  `vcong` (`vcongBound γ_c γ_ℓ G.maxDeg 0`), `H₀.m` sparsity, and operation-count bound for
  `initCore` (replacing [chen2022maximum] Theorem 5.3 with Theorem 8.1).
* `projWalk_spec`: validity of the projected multigraph `J`, auxiliary host `H_aux`, and
  projection embedding `embJH`; bounds on `|E_aff|`, `J.m`, `J.n`, `J.maxDeg`, `vcong(embJH)`, and
  `length(embJH)`; and validity, length (`lenBound γ_ℓ (i + 1)`), and vertex congestion
  (`vcongBound` step) of the updated level spanner `H_j` and embedding `π_{≤ j}`.
-/

namespace MinCostFlow.DynSpanner

section RebuildSpecs

@[expose] public section

/-- Specification of `initCore` (replacing [chen2022maximum] Theorem 5.3 with Theorem 8.1). -/
theorem initCore_spec {mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hSpec : SparsifySpec mMax P sparsify)
    {G : MGraph} (hVG : G.IsValid) (hGm : G.m ≤ mMax) :
    let core := initCore G sparsify
    let H₀ := core.1
    let Pi₀ := core.2.1
    let c := core.2.2
    H₀.IsValid ∧
    G.IsSubgraph H₀ ∧
    H₀.V = G.V ∧
    Embedding.IsEmbedding Pi₀ G H₀ ∧
    (Embedding.length Pi₀ G : ℝ) ≤ lenBound P.γ_ℓ 0 ∧
    Embedding.vcong Pi₀ G H₀ (fun _ => 1) ≤ vcongBound P.γ_c P.γ_ℓ G.maxDeg 0 ∧
    (H₀.m : ℝ) ≤ P.K_s * ((activeSubgraph G).n : ℝ) * P.γ_ℓ *
      (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_s ∧
    (c : ℝ) ≤ P.K_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_t +
      (G.n : ℝ) + (G.m : ℝ) + (H₀.m : ℝ) + (G.m : ℝ) * lenBound P.γ_ℓ 0 := by
  intro core H₀ Pi₀ c
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  by_cases hE : G.E.Nonempty
  · set Gact := activeSubgraph G
    set out := sparsify Gact Gact idEmb
    have hV_act : Gact.IsValid := activeSubgraph_isValid hVG
    have hm_act : Gact.m ≤ mMax := hGm
    have hEmb_act : Embedding.IsEmbedding idEmb Gact Gact := idEmb_isEmbedding Gact
    have hLen1 : Gact.E.Nonempty → 1 ≤ Embedding.length idEmb Gact := fun h => by
      rw [idEmb_length_eq_one h]
    obtain ⟨hSubJ, hEmbJ, hVcongJ, hLenJ, hSpars, hCost⟩ :=
      hSpec Gact Gact idEmb hV_act hV_act hm_act hLen1 hEmb_act
    have hVJtilde : out.Jtilde.IsValid := fun e he => by
      obtain ⟨ht, hh⟩ := hSubJ.2.2 e he
      obtain ⟨htG, hhG⟩ := hV_act e (hSubJ.2.1 he)
      -- `out.emb.IsEmbedding Gact out.Jtilde` gives `Gact.V ⊆ out.Jtilde.V`, so the ends of `e`
      -- lie in `out.Jtilde.V`.
      exact ⟨hEmbJ.1 (ht ▸ htG), hEmbJ.1 (hh ▸ hhG)⟩
    have hCoreEq : H₀ = { V := G.V, E := out.Jtilde.E, tail := G.tail, head := G.head } ∧
        Pi₀ = (fun e => shortcutWalk G (G.tail e) (out.emb e)) ∧
        c = out.cost + G.n + G.m + out.Jtilde.E.card + ∑ e ∈ G.E, (out.emb e).length := by
      simp only [core, H₀, Pi₀, c, initCore, hE, ↓reduceDIte]
      exact ⟨rfl, rfl, rfl⟩
    rcases hCoreEq with ⟨hHeq, hPieq, hceq⟩
    have hH_sub_J : H₀.IsSubgraph out.Jtilde := by
      rw [hHeq]
      refine ⟨Finset.Subset.trans hSubJ.1 (Finset.filter_subset _ _), Finset.Subset.rfl,
        fun e he => hSubJ.2.2 e he⟩
    have hSub_G_H : G.IsSubgraph H₀ := by
      rw [hHeq]
      exact ⟨Finset.Subset.rfl, hSubJ.2.1, fun _ _ => ⟨rfl, rfl⟩⟩
    have hH_valid : H₀.IsValid := by
      intro e he
      obtain ⟨ht, hh⟩ := hVG e (hSub_G_H.2.1 he)
      rw [hHeq]
      exact ⟨ht, hh⟩
    have hH_tail : H₀.tail = G.tail := by rw [hHeq]
    have hH_head : H₀.head = G.head := by rw [hHeq]
    have hEmb_out : Embedding.IsEmbedding out.emb G H₀ := by
      refine ⟨by rw [hHeq], fun e he => ?_⟩
      exact IsWalk.of_isSubgraph hH_sub_J (hEmbJ.2 e he)
    have hEmb_GH : Embedding.IsEmbedding Pi₀ G H₀ := by
      rw [hPieq]
      exact ⟨hEmb_out.1, fun e he => shortcutWalk_isWalk hH_tail hH_head (hEmb_out.2 e he)⟩
    have hLen1' : Embedding.length idEmb Gact = 1 := idEmb_length_eq_one hE
    have hLen_out : (Embedding.length out.emb G : ℝ) ≤ lenBound P.γ_ℓ 0 := by
      have hlen_act : Embedding.length out.emb Gact =
          Embedding.length (Embedding.comp idEmb out.emb) Gact := by
        rw [idEmb_comp]
      have hlen_G : Embedding.length out.emb G = Embedding.length out.emb Gact := rfl
      rw [hlen_G, hlen_act]
      have hle : (Embedding.length (Embedding.comp idEmb out.emb) Gact : ℝ) ≤ P.γ_ℓ * 1 := by
        simpa [hLen1'] using hLenJ
      simpa [lenBound] using hle
    have hLen_Pi0 : (Embedding.length Pi₀ G : ℝ) ≤ lenBound P.γ_ℓ 0 := by
      have hlen_sc : Embedding.length Pi₀ G ≤ Embedding.length out.emb G := by
        rw [hPieq]
        unfold Embedding.length
        rw [Finset.sup_le_iff]
        intro e he
        exact le_trans (shortcutWalk_length_le G (out.emb e) (G.tail e))
          (Finset.le_sup (f := fun e => (out.emb e).length) he)
      exact le_trans (Nat.cast_le.mpr hlen_sc) hLen_out
    have hVcong_out : Embedding.vcong out.emb G H₀ (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G.maxDeg 0 := by
      unfold Embedding.vcong
      split_ifs with hVne
      · rw [Finset.sup'_le_iff]
        intro v _hv
        unfold Embedding.vcongAt
        by_cases hv_act : v ∈ Gact.V
        · have hflt : (G.E.filter fun e => v ∈ H₀.walkVertices (G.tail e) (out.emb e)) ⊆
              (Gact.E.filter fun e => v ∈ Gact.walkVertices (Gact.tail e) (out.emb e)) := by
            intro e he
            rw [Finset.mem_filter] at he ⊢
            refine ⟨he.1, ?_⟩
            have hw1 : H₀.walkVertices (Gact.tail e) (out.emb e) =
                out.Jtilde.walkVertices (Gact.tail e) (out.emb e) :=
              walkVertices_of_isSubgraph hH_sub_J (hEmbJ.2 e he.1)
            have hw2 : Gact.walkVertices (Gact.tail e) (out.emb e) =
                out.Jtilde.walkVertices (Gact.tail e) (out.emb e) :=
              walkVertices_of_isSubgraph hSubJ (hEmbJ.2 e he.1)
            have he2 : v ∈ H₀.walkVertices (G.tail e) (out.emb e) := he.2
            change v ∈ H₀.walkVertices (Gact.tail e) (out.emb e) at he2
            rw [hw1, ← hw2] at he2
            exact he2
          have hv1 : ((G.E.filter fun e => v ∈ H₀.walkVertices (G.tail e) (out.emb e)).card : ℝ) ≤
              Embedding.vcongAt (Embedding.comp idEmb out.emb) Gact Gact (fun _ => 1) v := by
            rw [idEmb_comp]
            unfold Embedding.vcongAt
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_le]
            exact Finset.card_le_card hflt
          have hv2 : Embedding.vcongAt (Embedding.comp idEmb out.emb) Gact Gact (fun _ => 1) v ≤
              Embedding.vcong (Embedding.comp idEmb out.emb) Gact Gact (fun _ => 1) := by
            unfold Embedding.vcong
            have hactNe : Gact.V.Nonempty := ⟨v, hv_act⟩
            simp only [hactNe, ↓reduceDIte]
            exact Finset.le_sup'
              (f := Embedding.vcongAt (Embedding.comp idEmb out.emb) Gact Gact (fun _ => 1)) hv_act
          have hv3 : Embedding.vcong (Embedding.comp idEmb out.emb) Gact Gact (fun _ => 1) ≤
              P.γ_c * 1 * ((G.maxDeg : ℝ) + (G.maxDeg : ℝ)) := by
            have hvc_id : Embedding.vcong idEmb Gact Gact (fun _ => 1) ≤ (G.maxDeg : ℝ) :=
              le_trans (idEmb_vcong_le Gact) (Nat.cast_le.mpr (activeSubgraph_maxDeg_le G))
            have hmd : (Gact.maxDeg : ℝ) ≤ (G.maxDeg : ℝ) :=
              Nat.cast_le.mpr (activeSubgraph_maxDeg_le G)
            rw [hLen1'] at hVcongJ
            push_cast at hVcongJ
            have hmul : P.γ_c * 1 * (Embedding.vcong idEmb Gact Gact (fun _ => 1) + (Gact.maxDeg : ℝ)) ≤
                P.γ_c * 1 * ((G.maxDeg : ℝ) + (G.maxDeg : ℝ)) :=
              mul_le_mul_of_nonneg_left (add_le_add hvc_id hmd) (mul_nonneg hγc (by norm_num))
            exact le_trans hVcongJ hmul
          have htwo : P.γ_c * 1 * ((G.maxDeg : ℝ) + (G.maxDeg : ℝ)) =
              2 * P.γ_c * (G.maxDeg : ℝ) := by ring
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact le_trans (le_trans (le_trans hv1 hv2) (htwo ▸ hv3))
            (vcongBound_zero hγc G.maxDeg)
        · have hzero : (G.E.filter fun e => v ∈ H₀.walkVertices (G.tail e) (out.emb e)) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro e he
            rw [Finset.mem_filter] at he
            have hw1 : H₀.walkVertices (Gact.tail e) (out.emb e) =
                out.Jtilde.walkVertices (Gact.tail e) (out.emb e) :=
              walkVertices_of_isSubgraph hH_sub_J (hEmbJ.2 e he.1)
            have he2' : v ∈ H₀.walkVertices (Gact.tail e) (out.emb e) := he.2
            have he2 : v ∈ out.Jtilde.walkVertices (Gact.tail e) (out.emb e) := hw1 ▸ he2'
            have htailV : Gact.tail e ∈ out.Jtilde.V := hEmbJ.1 (hV_act e he.1).1
            have hvJ : v ∈ out.Jtilde.V :=
              IsWalk.walkVertices_mem_V hVJtilde (hEmbJ.2 e he.1) htailV v he2
            exact hv_act (hSubJ.1 hvJ)
          simp only [hzero, Finset.sum_empty]
          exact vcongBound_nonneg hγc hγl G.maxDeg 0
      · exact vcongBound_nonneg hγc hγl G.maxDeg 0
    have hVcong_Pi0 : Embedding.vcong Pi₀ G H₀ (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G.maxDeg 0 := by
      have hvc_le : Embedding.vcong Pi₀ G H₀ (fun _ => 1) ≤
          Embedding.vcong out.emb G H₀ (fun _ => 1) := by
        rw [hPieq]
        refine vcong_le_of_map Finset.Subset.rfl id (fun _ hz => hz) fun z _ e _ hz => ?_
        rw [walkVertices_congr_ends hH_tail hH_head] at hz ⊢
        exact shortcutWalk_walkVertices_subset G (out.emb e) (G.tail e) z hz
      exact le_trans hvc_le hVcong_out
    have hHm : H₀.m = out.Jtilde.m := by rw [hHeq]; rfl
    have hWalkCost : ((∑ e ∈ G.E, (out.emb e).length : ℕ) : ℝ) ≤ (G.m : ℝ) * lenBound P.γ_ℓ 0 := by
      have hsum : ∑ e ∈ G.E, (out.emb e).length ≤ ∑ _ ∈ G.E, Embedding.length out.emb G :=
        Finset.sum_le_sum fun e he => Finset.le_sup (f := fun e => (out.emb e).length) he
      have hsum' : ∑ e ∈ G.E, (out.emb e).length ≤ G.m * Embedding.length out.emb G := by
        simpa [MGraph.m] using hsum
      have hcast : ((∑ e ∈ G.E, (out.emb e).length : ℕ) : ℝ) ≤
          (G.m : ℝ) * (Embedding.length out.emb G : ℝ) := by
        exact_mod_cast hsum'
      exact le_trans hcast (mul_le_mul_of_nonneg_left hLen_out (Nat.cast_nonneg _))
    have hCost' : (c : ℝ) ≤ P.K_t * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_t +
        (G.n : ℝ) + (G.m : ℝ) + (H₀.m : ℝ) + (G.m : ℝ) * lenBound P.γ_ℓ 0 := by
      rw [hceq]
      have hGact_m : Gact.m = G.m := rfl
      rw [hLen1', hGact_m] at hCost
      push_cast at hCost ⊢
      have hHm' : (out.Jtilde.E.card : ℝ) = (H₀.m : ℝ) := by rw [hHm]; rfl
      push_cast at hWalkCost
      linarith [hCost, hWalkCost, hHm']
    refine ⟨hH_valid, hSub_G_H, by rw [hHeq], hEmb_GH, hLen_Pi0, hVcong_Pi0, ?_, hCost'⟩
    rw [hHm]
    exact hSpars
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    have hnot : ¬ G.E.Nonempty := by simp [hE]
    have hCoreEq : H₀ = emptyGraphOn G ∧ Pi₀ = idEmb ∧ c = G.n := by
      simp [core, H₀, Pi₀, c, initCore, hnot]
    rcases hCoreEq with ⟨hHeq, hPieq, hceq⟩
    have hH_valid : H₀.IsValid := by rw [hHeq]; intro e he; simp [emptyGraphOn] at he
    have hSub_G_H : G.IsSubgraph H₀ := by
      rw [hHeq]
      exact ⟨Finset.Subset.rfl, Finset.empty_subset _, fun _ he => by simp [emptyGraphOn] at he⟩
    have hEmb_GH : Embedding.IsEmbedding Pi₀ G H₀ := by
      rw [hHeq, hPieq]
      exact ⟨Finset.Subset.rfl, fun e he => by simp [hE] at he⟩
    have hLen_Pi0 : (Embedding.length Pi₀ G : ℝ) ≤ lenBound P.γ_ℓ 0 := by
      simp [hPieq, Embedding.length, hE, lenBound_nonneg hγl]
    have hVcong_Pi0 : Embedding.vcong Pi₀ G H₀ (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G.maxDeg 0 := by
      have hzero : Embedding.vcong Pi₀ G H₀ (fun _ => 1) = 0 := by
        unfold Embedding.vcong
        split_ifs with hVne
        · apply le_antisymm
          · rw [Finset.sup'_le_iff]; intro v _; simp [Embedding.vcongAt, hE]
          · obtain ⟨v, hv⟩ := hVne
            exact le_trans (vcongAt_nonneg Pi₀ G H₀ v)
              (Finset.le_sup' (f := Embedding.vcongAt Pi₀ G H₀ (fun _ => 1)) hv)
        · rfl
      rw [hzero]
      exact vcongBound_nonneg hγc hγl G.maxDeg 0
    have hHm0 : H₀.m = 0 := by simp [hHeq, emptyGraphOn, MGraph.m]
    have hlog1 : 1 ≤ 1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2) := by
      have harg : (1 : ℝ) ≤ ((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2 := by
        linarith [show (0 : ℝ) ≤ (activeSubgraph G).n by positivity,
          show (0 : ℝ) ≤ G.m by positivity]
      linarith [Real.log_nonneg harg]
    have hnonneg1 : 0 ≤ P.K_s * ((activeSubgraph G).n : ℝ) * P.γ_ℓ *
        (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_s :=
      mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl)
        (pow_nonneg (by linarith) _)
    have hnonneg2 : 0 ≤ P.K_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_t :=
      mul_nonneg (mul_nonneg P.hK_t (by positivity)) (pow_nonneg (by linarith) _)
    have hHV : H₀.V = G.V := by rw [hHeq]; rfl
    refine ⟨hH_valid, hSub_G_H, hHV, hEmb_GH, hLen_Pi0, hVcong_Pi0, ?_, ?_⟩
    · rw [hHm0, Nat.cast_zero]; exact hnonneg1
    · rw [hceq, hHm0]
      have hGm0 : G.m = 0 := by simp [MGraph.m, hE]
      simp only [hGm0, CharP.cast_eq_zero, add_zero, zero_mul] at hnonneg2 ⊢
      linarith

/-- Every walk returned by `initCore` visits distinct vertices. -/
theorem initCore_nodup (G : MGraph) (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    ∀ e ∈ G.E, ((initCore G sparsify).1.walkVertices (G.tail e)
      ((initCore G sparsify).2.1 e)).Nodup := by
  intro e he
  have hE : G.E.Nonempty := ⟨e, he⟩
  simp only [initCore, hE, ↓reduceDIte]
  rw [walkVertices_congr_ends (G := G)
    (H := ⟨G.V, (sparsify (activeSubgraph G) (activeSubgraph G) idEmb).Jtilde.E, G.tail, G.head⟩)
    rfl rfl]
  exact shortcutWalk_nodup G _ _

/-- Specification of one rebuild step (`0 < j`) from `G_r` to `G' = G_r.applyBatch delta`
with touched set `S_prev` containing `allTouched G_r delta`. -/
theorem projWalk_spec {mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hSpec : SparsifySpec mMax P sparsify)
    {G_r H_lt_r H_lt : MGraph} {delta : List Update} {pi_r piLt_mid : Embedding}
    {S_prev : Finset ℕ} {i : ℕ} {V_prev V_next : ℝ}
    (hVG_r : G_r.IsValid) (hBV_d : G_r.BatchIsValid delta)
    (hds_d : ∀ u ∈ delta, isDelOrSplit u) (hGm_r : G_r.m ≤ mMax)
    (hSub_lt_r : G_r.IsSubgraph H_lt_r)
    (hEmb_lt_r : Embedding.IsEmbedding pi_r G_r H_lt_r)
    (hLen_r : (Embedding.length pi_r G_r : ℝ) ≤ lenBound P.γ_ℓ i)
    (hVcong_r : Embedding.vcong pi_r G_r H_lt_r (fun _ => 1) ≤ V_prev) (hVprev_nn : 0 ≤ V_prev)
    (hVstep : V_prev + P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) ≤ V_next)
    (hHLtV : H_lt.V = (G_r.applyBatch delta).V)
    (hHLtE : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E)
    (hHLt_tail : H_lt.tail = (G_r.applyBatch delta).tail)
    (hHLt_head : H_lt.head = (G_r.applyBatch delta).head)
    (hSub_lt : (G_r.applyBatch delta).IsSubgraph H_lt)
    (hTouch : allTouched G_r delta ⊆ S_prev)
    (hpi_eq : ∀ e ∈ (G_r.applyBatch delta).E, piLt_mid e = pi_r e) :
    let G' := G_r.applyBatch delta
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let H_aux := buildAuxHost G' H_lt E_aff
    let embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    let out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
    let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    let embMid : Embedding := Embedding.comp embJH outEmb
    let H_j : MGraph := { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
    let Pi_j : Embedding := reembedWalk G' H_lt piLt_mid embMid S_prev
    let H_new_lt : MGraph := { V := G'.V, E := H_lt.E ∪ H_j.E, tail := G'.tail, head := G'.head }
    let pi_new : Embedding := fun e => if e ∈ E_aff then Pi_j e else piLt_mid e
    (E_aff.card : ℝ) ≤ (S_prev.card : ℝ) * V_prev ∧
    J.m = E_aff.card ∧
    J.n ≤ 2 * E_aff.card ∧
    out.Jtilde.E ⊆ E_aff ∧
    G'.IsSubgraph H_j ∧
    H_j.IsValid ∧
    G'.IsSubgraph H_new_lt ∧
    H_new_lt.V = G'.V ∧
    H_new_lt.IsValid ∧
    Embedding.IsEmbedding pi_new G' H_new_lt ∧
    (Embedding.length pi_new G' : ℝ) ≤ lenBound P.γ_ℓ (i + 1) ∧
    Embedding.vcong pi_new G' H_new_lt (fun _ => 1) ≤ V_next ∧
    (E_aff.Nonempty →
      (Embedding.length embJH J : ℝ) ≤ lenBound P.γ_ℓ i + 1 ∧
      (out.Jtilde.m : ℝ) ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
      (out.cost : ℝ) ≤ P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ i + 1)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t) ∧
    (∀ e ∈ out.Jtilde.E, ∀ x ∈ embJH e, x.1 ∈ H_lt.E ∨ x.1 = e) ∧
    (E_aff = ∅ → out.cost = 0 ∧ out.Jtilde.E = ∅) ∧
    outEmb.IsEmbedding J out.Jtilde ∧
    (H_aux.IsValid ∧ J.IsValid ∧ J.m ≤ mMax ∧ embJH.IsEmbedding J H_aux ∧
      (Embedding.length embMid J : ℝ) ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ)) := by
  intro G' E_aff J H_aux embJH out outEmb embMid H_j Pi_j H_new_lt pi_new
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hInvG := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
  rcases hInvG with ⟨hVG', hEG'_sub, hVG_sub, _hdeg_le, hAncMem, hAncEq, hAncEnds⟩
  have hVH_lt_r : H_lt_r.IsValid := fun e he => by
    obtain ⟨ht, hh⟩ := hSub_lt_r.2.2 e he
    obtain ⟨htG, hhG⟩ := hVG_r e (hSub_lt_r.2.1 he)
    exact ⟨hEmb_lt_r.1 (ht ▸ htG), hEmb_lt_r.1 (hh ▸ hhG)⟩
  have hEnds_lt : ∀ e ∈ H_lt_r.E, H_lt.tail e = G'.tail e ∧ H_lt.head e = G'.head e :=
    fun _ _ => ⟨congrFun hHLt_tail _, congrFun hHLt_head _⟩
  have h_sub_aux : H_aux.IsSubgraph H_lt :=
    ⟨by rw [hHLtV]; exact Finset.Subset.rfl, Finset.subset_union_left,
      fun _ _ => ⟨congrFun hHLt_tail _, congrFun hHLt_head _⟩⟩
  have h_aff_hits : ∀ e ∈ E_aff,
      (∃ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ S_prev) ∧
      (∃ z ∈ H_lt.walkVertices (G'.head e) (walkRev (pi_r e)), z ∈ S_prev) := by
    intro e he
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
    have hhit : ∃ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ S_prev := by
      simpa [E_aff, affectedEdges, decide_eq_true_eq, hpi_eq e heG'] using (Finset.mem_filter.mp he).2
    have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
    have hwEdges : ∀ x ∈ pi_r e, x.1 ∈ H_lt_r.E := IsWalk.mem_edge hw_r
    have hwEdgesRev : ∀ x ∈ walkRev (pi_r e), x.1 ∈ H_lt_r.E :=
      IsWalk.mem_edge (isWalk_walkRev hw_r)
    obtain ⟨htV, hhV⟩ := hVG' e heG'
    obtain ⟨hanc_t, hanc_h⟩ := hAncEnds e (hEG'_sub heG')
    have hV_w : ∀ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ G'.V :=
      walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hwEdges htV
    have hV_wr : ∀ z ∈ H_lt.walkVertices (G'.head e) (walkRev (pi_r e)), z ∈ G'.V :=
      walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hwEdgesRev hhV
    have h1 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hTouch
      hwEdges htV hanc_t hV_w).mp hhit
    have h2 : ∃ z₀ ∈ H_lt_r.walkVertices (G_r.head e) (walkRev (pi_r e)), z₀ ∈ S_prev := by
      obtain ⟨z₀, hz₀, hz₀S⟩ := h1
      exact ⟨z₀, (mem_walkVertices_walkRev hw_r z₀).mpr hz₀, hz₀S⟩
    have h3 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hTouch
      hwEdgesRev hhV hanc_h hV_wr).mpr h2
    exact ⟨hhit, h3⟩
  have hAff_card : (E_aff.card : ℝ) ≤ (S_prev.card : ℝ) * V_prev := by
    have hsub_u : E_aff ⊆ (S_prev ∩ G_r.V).biUnion
        fun v => G_r.E.filter fun e => v ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e) := by
      intro e he
      have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
      have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
      have hwEdges : ∀ x ∈ pi_r e, x.1 ∈ H_lt_r.E := IsWalk.mem_edge hw_r
      obtain ⟨htV, _⟩ := hVG' e heG'
      obtain ⟨hanc_t, _⟩ := hAncEnds e (hEG'_sub heG')
      have hV_w : ∀ z ∈ H_lt.walkVertices (G'.tail e) (pi_r e), z ∈ G'.V :=
        walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hwEdges htV
      have hhit := (h_aff_hits e he).1
      obtain ⟨z₀, hz₀, hz₀S⟩ :=
        (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt hTouch
          hwEdges htV hanc_t hV_w).mp hhit
      have htail_lt : G_r.tail e ∈ H_lt_r.V := hEmb_lt_r.1 (hVG_r e (hEG'_sub heG')).1
      have hz₀V : z₀ ∈ G_r.V := hSub_lt_r.1 (IsWalk.walkVertices_mem_V hVH_lt_r hw_r htail_lt z₀ hz₀)
      rw [Finset.mem_biUnion]
      exact ⟨z₀, Finset.mem_inter.mpr ⟨hz₀S, hz₀V⟩, Finset.mem_filter.mpr ⟨hEG'_sub heG', hz₀⟩⟩
    have hcard_le : E_aff.card ≤ ∑ v ∈ S_prev ∩ G_r.V,
        (G_r.E.filter fun e => v ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e)).card :=
      le_trans (Finset.card_le_card hsub_u) Finset.card_biUnion_le
    have hcard_real : (E_aff.card : ℝ) ≤ ∑ v ∈ S_prev ∩ G_r.V,
        Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) v := by
      have hc : (E_aff.card : ℝ) ≤ ((∑ v ∈ S_prev ∩ G_r.V,
          (G_r.E.filter fun e => v ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e)).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard_le
      push_cast at hc
      simpa [Embedding.vcongAt] using hc
    have hv_le : ∀ v ∈ S_prev ∩ G_r.V, Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) v ≤ V_prev := by
      intro v hv
      have hv_lt : v ∈ H_lt_r.V := hEmb_lt_r.1 (Finset.mem_inter.mp hv).2
      have hv_vc : Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) v ≤
          Embedding.vcong pi_r G_r H_lt_r (fun _ => 1) := by
        unfold Embedding.vcong
        have hltNe : H_lt_r.V.Nonempty := ⟨v, hv_lt⟩
        simp only [hltNe, ↓reduceDIte]
        exact Finset.le_sup' (f := Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1)) hv_lt
      exact le_trans hv_vc hVcong_r
    have hsum_le : ∑ v ∈ S_prev ∩ G_r.V, Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) v ≤
        ((S_prev ∩ G_r.V).card : ℝ) * V_prev := by
      calc ∑ v ∈ S_prev ∩ G_r.V, Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) v
          ≤ ∑ _ ∈ S_prev ∩ G_r.V, V_prev := Finset.sum_le_sum hv_le
        _ = ((S_prev ∩ G_r.V).card : ℝ) * V_prev := by simp
    have hS_le : ((S_prev ∩ G_r.V).card : ℝ) * V_prev ≤ (S_prev.card : ℝ) * V_prev :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
        hVprev_nn
    exact le_trans (le_trans hcard_real hsum_le) hS_le
  have hJm : J.m = E_aff.card := rfl
  have hJn : J.n ≤ 2 * E_aff.card := by
    calc J.n ≤ ∑ e ∈ E_aff, ({(proj G' H_lt piLt_mid S_prev e).1,
            (proj G' H_lt piLt_mid S_prev e).2} : Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ E_aff, 2 := Finset.sum_le_sum fun _ _ => Finset.card_insert_le _ _
      _ = 2 * E_aff.card := by simp [mul_comm]
  have hV_aux : H_aux.IsValid := by
    intro e he
    simp only [H_aux, buildAuxHost] at he ⊢
    rcases Finset.mem_union.mp he with he1 | he2
    · exact hVG' e (hSub_lt.2.1 he1)
    · exact hVG' e ((Finset.mem_filter.mp he2).1)
  have hJ_valid : J.IsValid := by
    intro e he
    simp only [J, buildProjGraph] at he ⊢
    constructor <;> exact Finset.mem_biUnion.mpr ⟨e, he, by simp⟩
  have hPref_props : ∀ e ∈ E_aff,
      let p₁ := (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2
      let q₂ := (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2
      (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).1 ∈ S_prev ∧
      (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).1 ∈ G'.V ∧
      H_lt.IsWalk (G'.tail e) (J.tail e) p₁ ∧
      p₁ <+: pi_r e ∧
      (∀ z ∈ H_lt.walkVertices (G'.tail e) p₁,
        batchAnc delta z ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e)) ∧
      (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).1 ∈ S_prev ∧
      (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).1 ∈ G'.V ∧
      H_lt.IsWalk (G'.head e) (J.head e) q₂ ∧
      q₂ <+: walkRev (pi_r e) ∧
      (∀ z ∈ H_lt.walkVertices (G'.head e) q₂,
        batchAnc delta z ∈ H_lt_r.walkVertices (G_r.head e) (walkRev (pi_r e))) := by
    intro e he
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
    have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
    obtain ⟨ht0_V, hh0_V⟩ := hVG_r e (hEG'_sub heG')
    obtain ⟨ht_V, hh_V⟩ := hVG' e heG'
    obtain ⟨hanc_t, hanc_h⟩ := hAncEnds e (hEG'_sub heG')
    obtain ⟨hhit1, hhit2⟩ := h_aff_hits e he
    have hp1 := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt
      hTouch (pi_r e) (G_r.tail e) (G_r.head e) (G'.tail e) ht0_V hh0_V hw_r ht_V hanc_t).2 hhit1
    have hq2 := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt
      hTouch (walkRev (pi_r e)) (G_r.head e) (G_r.tail e) (G'.head e)
      hh0_V ht0_V (isWalk_walkRev hw_r) hh_V hanc_h).2 hhit2
    dsimp only at hp1 hq2
    have hJt : J.tail e = (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).1 := by
      simp [J, buildProjGraph, proj, hpi_eq e heG']
    have hJh : J.head e = (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).1 := by
      simp [J, buildProjGraph, proj, hpi_eq e heG']
    refine ⟨hp1.1, hp1.2.1, hJt ▸ hp1.2.2.1, hp1.2.2.2.1, hp1.2.2.2.2.1,
      hq2.1, hq2.2.1, hJh ▸ hq2.2.2.1, hq2.2.2.2.1, hq2.2.2.2.2.1⟩
  have hEmbJH : Embedding.IsEmbedding embJH J H_aux := by
    refine ⟨?_, fun e he => ?_⟩
    · intro v hv
      simp only [J, buildProjGraph, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with ⟨e, he, rfl | rfl⟩
      · simpa [H_aux, buildAuxHost, proj, hpi_eq e (Finset.mem_filter.mp he).1] using
          (hPref_props e he).2.1
      · simpa [H_aux, buildAuxHost, proj, hpi_eq e (Finset.mem_filter.mp he).1] using
          (hPref_props e he).2.2.2.2.2.2.1
    · have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
      have hp := hPref_props e he
      set p₁ := (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2
      set q₂ := (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2
      have hwalk1 : H_aux.IsWalk (J.tail e) (G'.tail e) (walkRev p₁) :=
        IsWalk.of_isSubgraph h_sub_aux (isWalk_walkRev hp.2.2.1)
      have heAux : e ∈ H_aux.E := Finset.mem_union_right _ he
      have hwalk_e : H_aux.IsWalk (G'.tail e) (G'.head e) [(e, true)] :=
        .cons heAux rfl (.nil _)
      have hwalk2 : H_aux.IsWalk (G'.head e) (J.head e) q₂ :=
        IsWalk.of_isSubgraph h_sub_aux hp.2.2.2.2.2.2.2.1
      have hfull := IsWalk.append (IsWalk.append hwalk1 hwalk_e) hwalk2
      simpa [embJH, projWalk, hpi_eq e heG', p₁, q₂, List.append_assoc] using hfull
  have hEmbJH_len : (Embedding.length embJH J : ℝ) ≤ lenBound P.γ_ℓ i + 1 := by
    have hsup : Embedding.length embJH J ≤ Embedding.length pi_r G_r + 1 := by
      unfold Embedding.length
      rw [Finset.sup_le_iff]
      intro e he
      have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
      have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
      obtain ⟨ht0_V, hh0_V⟩ := hVG_r e (hEG'_sub heG')
      obtain ⟨ht_V, hh_V⟩ := hVG' e heG'
      obtain ⟨hanc_t, hanc_h⟩ := hAncEnds e (hEG'_sub heG')
      obtain ⟨hhit1, hhit2⟩ := h_aff_hits e he
      have hadd := prefixWalk_length_add_le hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE
        hEnds_lt hTouch ht0_V hh0_V hw_r ht_V hh_V hanc_t hanc_h hhit1 hhit2
      have hpi_le : (pi_r e).length ≤ Embedding.length pi_r G_r :=
        Finset.le_sup (f := fun e => (pi_r e).length) (hEG'_sub heG')
      have hlen_e : (embJH e).length =
          (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2.length + 1 +
          (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2.length := by
        simp only [embJH, projWalk, hpi_eq e heG', List.length_append, List.length_cons,
          List.length_nil, length_walkRev]
      have hadd' : (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2.length +
          (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2.length ≤
          (pi_r e).length := hadd
      rw [hlen_e]
      exact le_trans (by omega : _ ≤ (pi_r e).length + 1) (Nat.add_le_add_right hpi_le 1)
    have hc : (Embedding.length embJH J : ℝ) ≤ (Embedding.length pi_r G_r : ℝ) + 1 := by
      exact_mod_cast hsup
    linarith [hLen_r]
  have hEmbJH_anc : ∀ e ∈ E_aff, ∀ z,
      z ∈ H_aux.walkVertices (J.tail e) (embJH e) →
      batchAnc delta z ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e) := by
    intro e he z hz
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
    have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
    have hp := hPref_props e he
    set p₁ := (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2
    set q₂ := (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2
    have hwalk1 : H_aux.IsWalk (J.tail e) (G'.tail e) (walkRev p₁) :=
      IsWalk.of_isSubgraph h_sub_aux (isWalk_walkRev hp.2.2.1)
    have hwalk_e : H_aux.IsWalk (G'.tail e) (G'.head e) [(e, true)] :=
      .cons (Finset.mem_union_right _ he) rfl (.nil _)
    have hwalk2 : H_aux.IsWalk (G'.head e) (J.head e) q₂ :=
      IsWalk.of_isSubgraph h_sub_aux hp.2.2.2.2.2.2.2.1
    have heq_w : embJH e = walkRev p₁ ++ ([(e, true)] ++ q₂) := by
      simp [embJH, projWalk, hpi_eq e heG', p₁, q₂, List.append_assoc]
    rw [heq_w] at hz
    have hsplit1 := (IsWalk.mem_walkVertices_append (_w := 0) hwalk1 z).mp hz
    rcases hsplit1 with hz1 | hz_rest
    · have hw1_lt := walkVertices_of_isSubgraph h_sub_aux (isWalk_walkRev hp.2.2.1)
      rw [hw1_lt] at hz1
      have hz1' := (mem_walkVertices_walkRev hp.2.2.1 z).mp hz1
      exact hp.2.2.2.2.1 z hz1'
    · have hsplit2 := (IsWalk.mem_walkVertices_append (_w := 0) hwalk_e z).mp hz_rest
      rcases hsplit2 with hz_e | hz2
      · simp only [MGraph.walkVertices, MGraph.dst, H_aux, buildAuxHost, ↓reduceIte,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz_e
        obtain ⟨hanc_t, hanc_h⟩ := hAncEnds e (hEG'_sub heG')
        rcases hz_e with rfl | rfl
        · rw [hanc_t]; exact mem_walkVertices_start _ _ _
        · rw [hanc_h]; exact IsWalk.end_mem_walkVertices hw_r
      · have hw2_lt := walkVertices_of_isSubgraph h_sub_aux hp.2.2.2.2.2.2.2.1
        rw [hw2_lt] at hz2
        have hz2' := hp.2.2.2.2.2.2.2.2.2 z hz2
        exact (mem_walkVertices_walkRev hw_r (batchAnc delta z)).mp hz2'
  have hEmbJH_vcong : Embedding.vcong embJH J H_aux (fun _ => 1) ≤ V_prev := by
    unfold Embedding.vcong
    split_ifs with hVne
    · rw [Finset.sup'_le_iff]
      intro z hz
      have hzG' : z ∈ G'.V := hz
      have hz0 : batchAnc delta z ∈ G_r.V := hAncMem z hzG'
      have hflt : (J.E.filter fun e => z ∈ H_aux.walkVertices (J.tail e) (embJH e)) ⊆
          (G_r.E.filter fun e => batchAnc delta z ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e)) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨hEG'_sub (Finset.mem_filter.mp he.1).1, hEmbJH_anc e he.1 z he.2⟩
      have hv1 : Embedding.vcongAt embJH J H_aux (fun _ => 1) z ≤
          Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) (batchAnc delta z) := by
        unfold Embedding.vcongAt
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_le]
        exact Finset.card_le_card hflt
      have hv2 : Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) (batchAnc delta z) ≤
          Embedding.vcong pi_r G_r H_lt_r (fun _ => 1) := by
        unfold Embedding.vcong
        have hz_lt : batchAnc delta z ∈ H_lt_r.V := hEmb_lt_r.1 hz0
        have hltNe : H_lt_r.V.Nonempty := ⟨_, hz_lt⟩
        simp only [hltNe, ↓reduceDIte]
        exact Finset.le_sup' (f := Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1)) hz_lt
      exact le_trans (le_trans hv1 hv2) hVcong_r
    · exact hVprev_nn
  have hJ_maxDeg : (J.maxDeg : ℝ) ≤ 2 * V_prev := by
    unfold MGraph.maxDeg
    by_cases hJV : J.V.Nonempty
    · rw [← Finset.sup'_eq_sup hJV]
      obtain ⟨z, hz, hsup⟩ := J.V.exists_mem_eq_sup' hJV J.deg
      rw [hsup]
      have hvc : (J.deg z : ℝ) ≤ 2 * Embedding.vcongAt embJH J H_aux (fun _ => 1) z := by
        have ht_sub : (J.E.filter fun e => J.tail e = z) ⊆
            (J.E.filter fun e => z ∈ H_aux.walkVertices (J.tail e) (embJH e)) := by
          intro e he
          rw [Finset.mem_filter] at he ⊢
          refine ⟨he.1, ?_⟩
          rw [← he.2]
          exact mem_walkVertices_start _ _ _
        have hh_sub : (J.E.filter fun e => J.head e = z) ⊆
            (J.E.filter fun e => z ∈ H_aux.walkVertices (J.tail e) (embJH e)) := by
          intro e he
          rw [Finset.mem_filter] at he ⊢
          refine ⟨he.1, ?_⟩
          rw [← he.2]
          exact IsWalk.end_mem_walkVertices (hEmbJH.2 e he.1)
        have hcard : J.deg z ≤ 2 *
            (J.E.filter fun e => z ∈ H_aux.walkVertices (J.tail e) (embJH e)).card := by
          unfold MGraph.deg
          have h1 := Finset.card_le_card ht_sub
          have h2 := Finset.card_le_card hh_sub
          omega
        unfold Embedding.vcongAt
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hcard
      have hzAux : z ∈ H_aux.V := hEmbJH.1 hz
      have hvc_le : Embedding.vcongAt embJH J H_aux (fun _ => 1) z ≤
          Embedding.vcong embJH J H_aux (fun _ => 1) := by
        unfold Embedding.vcong
        have hauxNe : H_aux.V.Nonempty := ⟨z, hzAux⟩
        simp only [hauxNe, ↓reduceDIte]
        exact Finset.le_sup' (f := Embedding.vcongAt embJH J H_aux (fun _ => 1)) hzAux
      exact le_trans hvc (mul_le_mul_of_nonneg_left (le_trans hvc_le hEmbJH_vcong) (by norm_num))
    · rw [Finset.not_nonempty_iff_eq_empty] at hJV
      simp [hJV]
      linarith
  have hJm_max : J.m ≤ mMax := by
    have hEaff_sub : E_aff ⊆ G'.E := Finset.filter_subset _ _
    exact le_trans (Finset.card_le_card (Finset.Subset.trans hEaff_sub hEG'_sub)) hGm_r
  have hJtilde_sub : J.IsSubgraph out.Jtilde ∧
      Embedding.IsEmbedding outEmb J out.Jtilde ∧
      Embedding.vcong embMid J H_aux (fun _ => 1) ≤
        P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) ∧
      ((Embedding.length embMid J : ℝ) ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ)) ∧
      (E_aff.Nonempty →
        (out.Jtilde.m : ℝ) ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
        (out.cost : ℝ) ≤ P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ i + 1)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t) ∧
      (E_aff = ∅ → out.cost = 0 ∧ out.Jtilde.E = ∅) := by
    by_cases hEne : E_aff.Nonempty
    · have hLen1_J : J.E.Nonempty → 1 ≤ Embedding.length embJH J := fun _ => by
        obtain ⟨e, he⟩ := hEne
        have hge : 1 ≤ (embJH e).length := by
          simp only [embJH, projWalk, List.length_append, List.length_cons, List.length_nil]
          omega
        exact le_trans hge (Finset.le_sup (f := fun e => (embJH e).length) he)
      obtain ⟨hSubJ, hEmbOut, hVcMid, hLenMid, hSparsOut, hCostOut⟩ :=
        hSpec H_aux J embJH hV_aux hJ_valid hJm_max hLen1_J hEmbJH
      have hout_eq : out = sparsify H_aux J embJH := by simp [out, hEne]
      have hEmbOut' : Embedding.IsEmbedding outEmb J out.Jtilde := by
        refine ⟨by rw [hout_eq]; exact hEmbOut.1, fun e he => ?_⟩
        simpa [outEmb, hout_eq] using
          shortcutWalk_isWalk (G := (sparsify H_aux J embJH).Jtilde)
            (H := (sparsify H_aux J embJH).Jtilde) rfl rfl (hEmbOut.2 e he)
      have hVcMid_sc : Embedding.vcong embMid J H_aux (fun _ => 1) ≤
          Embedding.vcong (Embedding.comp embJH (sparsify H_aux J embJH).emb) J H_aux (fun _ => 1) := by
        refine comp_vcong_le_of_sublist fun e _ => ?_
        simp only [outEmb, hout_eq]
        exact shortcutWalk_sublist _ _ _
      have hLenMid_sc : Embedding.length embMid J ≤
          Embedding.length (Embedding.comp embJH (sparsify H_aux J embJH).emb) J := by
        refine comp_length_le_of_sublist fun e _ => ?_
        simp only [outEmb, hout_eq]
        exact shortcutWalk_sublist _ _ _
      have hVc_le : Embedding.vcong embMid J H_aux (fun _ => 1) ≤
          P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) := by
        have h1 : P.γ_c * (Embedding.length embJH J : ℝ) *
            (Embedding.vcong embJH J H_aux (fun _ => 1) + (J.maxDeg : ℝ)) ≤
            P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) := by
          have ha : P.γ_c * (Embedding.length embJH J : ℝ) ≤ P.γ_c * (lenBound P.γ_ℓ i + 1) :=
            mul_le_mul_of_nonneg_left hEmbJH_len hγc
          have hb : Embedding.vcong embJH J H_aux (fun _ => 1) + (J.maxDeg : ℝ) ≤
              V_prev + 2 * V_prev :=
            add_le_add hEmbJH_vcong hJ_maxDeg
          have hlnn : 0 ≤ lenBound P.γ_ℓ i + 1 := by
            linarith [lenBound_nonneg hγl i]
          have hvn : 0 ≤ Embedding.vcong embJH J H_aux (fun _ => 1) + (J.maxDeg : ℝ) :=
            add_nonneg (vcong_nonneg embJH J H_aux) (Nat.cast_nonneg _)
          exact mul_le_mul ha hb hvn (mul_nonneg hγc hlnn)
        exact le_trans hVcMid_sc (le_trans hVcMid h1)
      have hCost_le : (out.cost : ℝ) ≤ P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 *
          (lenBound P.γ_ℓ i + 1)) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t := by
        have hlog_nn : 0 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t := by
          have h1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
            linarith [show (0 : ℝ) ≤ J.n by positivity, show (0 : ℝ) ≤ J.m by positivity]
          exact pow_nonneg (by linarith [Real.log_nonneg h1]) _
        have hm1 : (J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (Embedding.length embJH J : ℝ) ≤
            (J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ i + 1) := by
          have hmul : (J.m : ℝ) * P.γ_ℓ ^ 2 * (Embedding.length embJH J : ℝ) ≤
              (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ i + 1) :=
            mul_le_mul_of_nonneg_left hEmbJH_len (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          linarith
        have hm2 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm1 P.hK_t) hlog_nn
        simpa [hout_eq] using le_trans hCostOut hm2
      have hLenMid' : (Embedding.length embMid J : ℝ) ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ) :=
        le_trans (Nat.cast_le.mpr hLenMid_sc) hLenMid
      refine ⟨hout_eq ▸ hSubJ, hEmbOut', hVc_le, hLenMid',
        fun _ => ⟨by simpa [hout_eq] using hSparsOut, hCost_le⟩,
        fun he => absurd hEne (by simp [he])⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      have hnot : ¬ E_aff.Nonempty := by simp [hEne]
      have hout_eq : out = ⟨J, idEmb, 0⟩ := by simp [out, hnot]
      have hJE : J.E = ∅ := hEne
      have hSubJ : J.IsSubgraph out.Jtilde := by
        rw [hout_eq]; exact ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩
      have hEmbOut : Embedding.IsEmbedding outEmb J out.Jtilde := by
        rw [hout_eq]
        exact ⟨Finset.Subset.rfl, fun e he => absurd he (by simp [J, hJE])⟩
      have hVc_zero : Embedding.vcong embMid J H_aux (fun _ => 1) = 0 := by
        unfold Embedding.vcong
        split_ifs with hVne
        · apply le_antisymm
          · rw [Finset.sup'_le_iff]; intro v _; simp [Embedding.vcongAt, J, hJE]
          · obtain ⟨v, hv⟩ := hVne
            exact le_trans (vcongAt_nonneg embMid J H_aux v)
              (Finset.le_sup' (f := Embedding.vcongAt embMid J H_aux (fun _ => 1)) hv)
        · rfl
      have hLen0 : Embedding.length embMid J = 0 := by simp [Embedding.length, J, hJE]
      have hlnn : 0 ≤ lenBound P.γ_ℓ i + 1 := by linarith [lenBound_nonneg hγl i]
      have hEmb_len0 : 0 ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ) :=
        mul_nonneg hγl (Nat.cast_nonneg _)
      have hVc_rhs : 0 ≤ P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) :=
        mul_nonneg (mul_nonneg hγc hlnn) (by linarith)
      refine ⟨hSubJ, hEmbOut, hVc_zero ▸ hVc_rhs, ?_,
        fun h => absurd h (by simp [hEne]), fun _ => by simp [hout_eq, J, hJE]⟩
      rw [hLen0]; simpa using hEmb_len0
  rcases hJtilde_sub with ⟨hSubJtilde, hEmbOut, hVcMid_le, hLenMid_le, hNonempty_bnd, hEmpty_bnd⟩
  have hOut_sub_aff : out.Jtilde.E ⊆ E_aff := hSubJtilde.2.1
  have hOut_sub_G' : out.Jtilde.E ⊆ G'.E := Finset.Subset.trans hOut_sub_aff (Finset.filter_subset _ _)
  have hSub_Hj : G'.IsSubgraph H_j := ⟨Finset.Subset.rfl, hOut_sub_G', fun _ _ => ⟨rfl, rfl⟩⟩
  have hHj_valid : H_j.IsValid := fun e he => hVG' e (hOut_sub_G' he)
  have hHnew_sub : G'.IsSubgraph H_new_lt :=
    ⟨Finset.Subset.rfl, Finset.union_subset hSub_lt.2.1 hOut_sub_G', fun _ _ => ⟨rfl, rfl⟩⟩
  have hHnew_V : H_new_lt.V = G'.V := rfl
  have hHnew_valid : H_new_lt.IsValid := fun e he => hVG' e (hHnew_sub.2.1 he)
  have hHlt_sub_Hnew : H_new_lt.IsSubgraph H_lt :=
    ⟨by rw [hHLtV], Finset.subset_union_left, fun _ _ => ⟨congrFun hHLt_tail _, congrFun hHLt_head _⟩⟩
  have hAux_sub_Hnew : H_aux.IsSubgraph H_new_lt :=
    ⟨Finset.Subset.rfl, Finset.union_subset Finset.subset_union_left
      (Finset.Subset.trans hOut_sub_aff Finset.subset_union_right),
      fun _ _ => ⟨rfl, rfl⟩⟩
  have hJH_edges : ∀ e ∈ out.Jtilde.E, ∀ x ∈ embJH e, x.1 ∈ H_lt.E ∨ x.1 = e := by
    intro e he x hx
    have heAff : e ∈ E_aff := hOut_sub_aff he
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp heAff).1
    have hp := hPref_props e heAff
    simp only [embJH, projWalk, hpi_eq e heG', List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx1 | hx_mid) | hx2
    · left
      have hx1' : x.1 ∈ walkEdges (walkRev (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2) := by
        rw [mem_walkEdges_iff]
        exact ⟨x, hx1, rfl⟩
      rw [walkEdges_walkRev, mem_walkEdges_iff] at hx1'
      obtain ⟨y, hy, hyfst⟩ := hx1'
      exact hyfst ▸ IsWalk.mem_edge hp.2.2.1 y hy
    · right; rw [hx_mid]
    · left; exact IsWalk.mem_edge hp.2.2.2.2.2.2.2.1 x hx2
  have hEmbJH_Hnew : Embedding.IsEmbedding embJH out.Jtilde H_new_lt := by
    refine ⟨Finset.Subset.trans hSubJtilde.1 hEmbJH.1, fun e he => ?_⟩
    have heAff : e ∈ E_aff := hOut_sub_aff he
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp heAff).1
    have hp := hPref_props e heAff
    obtain ⟨hJt_eq, hJh_eq⟩ := hSubJtilde.2.2 e he
    rw [hJt_eq, hJh_eq]
    have h1 : H_new_lt.IsWalk (J.tail e) (G'.tail e)
        (walkRev (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2) :=
      IsWalk.of_isSubgraph hHlt_sub_Hnew (isWalk_walkRev hp.2.2.1)
    have h2 : H_new_lt.IsWalk (G'.tail e) (G'.head e) [(e, true)] :=
      .cons (Finset.mem_union_right _ he) rfl (.nil _)
    have h3 : H_new_lt.IsWalk (G'.head e) (J.head e)
        (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2 :=
      IsWalk.of_isSubgraph hHlt_sub_Hnew hp.2.2.2.2.2.2.2.1
    simpa [embJH, projWalk, hpi_eq e heG', List.append_assoc] using
      IsWalk.append (IsWalk.append h1 h2) h3
  have hEmbMid_Hnew : Embedding.IsEmbedding embMid J H_new_lt :=
    comp_isEmbedding hEmbOut hEmbJH_Hnew
  have hPi_new_emb : Embedding.IsEmbedding pi_new G' H_new_lt := by
    refine ⟨le_rfl, fun e heG' => ?_⟩
    by_cases heAff : e ∈ E_aff
    · have hp := hPref_props e heAff
      have heJ : e ∈ J.E := heAff
      have h1 : H_new_lt.IsWalk (G'.tail e) (J.tail e)
          (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2 :=
        IsWalk.of_isSubgraph hHlt_sub_Hnew hp.2.2.1
      have h2 : H_new_lt.IsWalk (J.tail e) (J.head e) (embMid e) := hEmbMid_Hnew.2 e heJ
      have h3 : H_new_lt.IsWalk (J.head e) (G'.head e)
          (walkRev (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2) :=
        IsWalk.of_isSubgraph hHlt_sub_Hnew (isWalk_walkRev hp.2.2.2.2.2.2.2.1)
      have hfull := IsWalk.append (IsWalk.append h1 h2) h3
      simpa [pi_new, heAff, Pi_j, reembedWalk, hpi_eq e heG', List.append_assoc] using hfull
    · have hdisj : Disjoint (H_lt.walkVertices (G'.tail e) (pi_r e)).toFinset S_prev := by
        rw [Finset.disjoint_left]
        intro z hz
        simp only [List.mem_toFinset] at hz
        intro hzS
        apply heAff
        refine Finset.mem_filter.mpr ⟨heG', ?_⟩
        simp only [decide_eq_true_eq, hpi_eq e heG']
        exact ⟨z, hz, hzS⟩
      have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
      obtain ⟨ht0_V, hh0_V⟩ := hVG_r e (hEG'_sub heG')
      obtain ⟨ht_V, _⟩ := hVG' e heG'
      obtain ⟨hanc_t, _⟩ := hAncEnds e (hEG'_sub heG')
      have hSurv := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt
        hTouch (pi_r e) (G_r.tail e) (G_r.head e) (G'.tail e) ht0_V hh0_V hw_r ht_V hanc_t).1 hdisj
      have hwalk_lt : H_lt.IsWalk (G'.tail e) (G'.head e) (pi_r e) := by
        have hz_end : G_r.head e ∈ H_lt.walkVertices (G'.tail e) (pi_r e) :=
          IsWalk.end_mem_walkVertices hSurv.2.1
        have hnotS : G_r.head e ∉ S_prev := fun hmem =>
          (Finset.disjoint_left.mp hdisj) (List.mem_toFinset.mpr hz_end) hmem
        have hnt := not_mem_allTouched_invariants delta G_r hVG_r hBV_d hds_d (G_r.head e)
          fun h => hnotS (hTouch h)
        have hfix : G'.head e = G_r.head e :=
          ((hnt.2.2 e (hEG'_sub heG')).2 rfl).2
        rw [hfix]
        exact hSurv.2.1
      have hwalk_new := IsWalk.of_isSubgraph hHlt_sub_Hnew hwalk_lt
      simpa [pi_new, heAff, hpi_eq e heG'] using hwalk_new
  have hPi_new_len : (Embedding.length pi_new G' : ℝ) ≤ lenBound P.γ_ℓ (i + 1) := by
    have h1 : Embedding.length pi_new G' = G'.E.sup fun e => (pi_new e).length := rfl
    by_cases hGE : G'.E.Nonempty
    · obtain ⟨e, heG', hsup⟩ := G'.E.exists_mem_eq_sup' hGE fun e => (pi_new e).length
      rw [h1, ← Finset.sup'_eq_sup hGE, hsup]
      by_cases heAff : e ∈ E_aff
      · have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
        obtain ⟨ht0_V, hh0_V⟩ := hVG_r e (hEG'_sub heG')
        obtain ⟨ht_V, hh_V⟩ := hVG' e heG'
        obtain ⟨hanc_t, hanc_h⟩ := hAncEnds e (hEG'_sub heG')
        obtain ⟨hhit1, hhit2⟩ := h_aff_hits e heAff
        have hadd := prefixWalk_length_add_le hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE
          hEnds_lt hTouch ht0_V hh0_V hw_r ht_V hh_V hanc_t hanc_h hhit1 hhit2
        have hpi_le : ((pi_r e).length : ℝ) ≤ lenBound P.γ_ℓ i := by
          have hle : (pi_r e).length ≤ Embedding.length pi_r G_r :=
            Finset.le_sup (f := fun e => (pi_r e).length) (hEG'_sub heG')
          exact le_trans (Nat.cast_le.mpr hle) hLen_r
        have hmid_le : ((embMid e).length : ℝ) ≤ P.γ_ℓ * (lenBound P.γ_ℓ i + 1) := by
          have hle : (embMid e).length ≤ Embedding.length embMid J :=
            Finset.le_sup (f := fun e => (embMid e).length) heAff
          have hm1 : ((embMid e).length : ℝ) ≤ P.γ_ℓ * (Embedding.length embJH J : ℝ) :=
            le_trans (Nat.cast_le.mpr hle) hLenMid_le
          have hm2 : P.γ_ℓ * (Embedding.length embJH J : ℝ) ≤ P.γ_ℓ * (lenBound P.γ_ℓ i + 1) :=
            mul_le_mul_of_nonneg_left hEmbJH_len hγl
          exact le_trans hm1 hm2
        have hlen_e : ((pi_new e).length : ℝ) =
            ((prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2.length : ℝ) +
            ((embMid e).length : ℝ) +
            ((prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2.length : ℝ) := by
          simp only [pi_new, heAff, ↓reduceIte, Pi_j, reembedWalk, hpi_eq e heG',
            List.length_append, length_walkRev]
          push_cast; ring
        have hadd_r : ((prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2.length : ℝ) +
            ((prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2.length : ℝ) ≤
            ((pi_r e).length : ℝ) := by exact_mod_cast hadd
        exact le_trans (by linarith) (lenBound_step P.hγ_ℓ i)
      · have heq : pi_new e = pi_r e := by simp [pi_new, heAff, hpi_eq e heG']
        have hle : (pi_r e).length ≤ Embedding.length pi_r G_r :=
          Finset.le_sup (f := fun e => (pi_r e).length) (hEG'_sub heG')
        rw [heq]
        exact le_trans (le_trans (Nat.cast_le.mpr hle) hLen_r) (lenBound_mono P.hγ_ℓ (Nat.le_succ i))
    · rw [Finset.not_nonempty_iff_eq_empty] at hGE
      simp [Embedding.length, hGE, lenBound_nonneg hγl]
  have hPi_new_vcong : Embedding.vcong pi_new G' H_new_lt (fun _ => 1) ≤ V_next := by
    have hVnext_nn : 0 ≤ V_next := by
      have hlnn : 0 ≤ lenBound P.γ_ℓ i + 1 := by linarith [lenBound_nonneg hγl i]
      have hterm : 0 ≤ P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) :=
        mul_nonneg (mul_nonneg hγc hlnn) (by linarith)
      linarith
    unfold Embedding.vcong
    split_ifs with hVne
    · rw [Finset.sup'_le_iff]
      intro z hz
      have hzG' : z ∈ G'.V := hz
      have hz0 : batchAnc delta z ∈ G_r.V := hAncMem z hzG'
      set F := G'.E.filter fun e => z ∈ H_new_lt.walkVertices (G'.tail e) (pi_new e)
      set F_orig := G_r.E.filter fun e =>
        batchAnc delta z ∈ H_lt_r.walkVertices (G_r.tail e) (pi_r e)
      set F_mid := E_aff.filter fun e =>
        z ∈ H_aux.walkVertices (J.tail e) (embMid e)
      have hF_sub : F ⊆ F_orig ∪ F_mid := by
        intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨heG', hz_w⟩ := he
        rw [Finset.mem_union]
        by_cases heAff : e ∈ E_aff
        · have hp := hPref_props e heAff
          have h1 : H_new_lt.IsWalk (G'.tail e) (J.tail e)
              (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2 :=
            IsWalk.of_isSubgraph hHlt_sub_Hnew hp.2.2.1
          have h2 : H_new_lt.IsWalk (J.tail e) (J.head e) (embMid e) := hEmbMid_Hnew.2 e heAff
          have hz_eq : pi_new e =
              (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2 ++ (embMid e ++
              walkRev (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2) := by
            simp [pi_new, heAff, Pi_j, reembedWalk, hpi_eq e heG', List.append_assoc]
          rw [hz_eq] at hz_w
          rcases (IsWalk.mem_walkVertices_append (_w := 0) h1 z).mp hz_w with hz_p1 | hz_rest
          · left
            have hw1_eq := walkVertices_of_isSubgraph hHlt_sub_Hnew hp.2.2.1
            have hz_lt : z ∈ H_lt.walkVertices (G'.tail e)
                (prefixWalk H_lt (G'.tail e) (pi_r e) S_prev).2 := hw1_eq.symm ▸ hz_p1
            exact Finset.mem_filter.mpr ⟨hEG'_sub heG', hp.2.2.2.2.1 z hz_lt⟩
          · rcases (IsWalk.mem_walkVertices_append (_w := 0) h2 z).mp hz_rest with hz_mid | hz_p2
            · right
              have hm_aux := walkVertices_of_isSubgraph hAux_sub_Hnew h2
              exact Finset.mem_filter.mpr ⟨heAff, hm_aux.symm ▸ hz_mid⟩
            · left
              have hw3_lt : H_lt.IsWalk (J.head e) (G'.head e)
                  (walkRev (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2) :=
                isWalk_walkRev hp.2.2.2.2.2.2.2.1
              have hw3_eq := walkVertices_of_isSubgraph hHlt_sub_Hnew hw3_lt
              have hz_lt : z ∈ H_lt.walkVertices (J.head e)
                  (walkRev (prefixWalk H_lt (G'.head e) (walkRev (pi_r e)) S_prev).2) :=
                hw3_eq.symm ▸ hz_p2
              have hz_q2 := (mem_walkVertices_walkRev hp.2.2.2.2.2.2.2.1 z).mp hz_lt
              have hanc_rev := hp.2.2.2.2.2.2.2.2.2 z hz_q2
              have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
              exact Finset.mem_filter.mpr
                ⟨hEG'_sub heG', (mem_walkVertices_walkRev hw_r (batchAnc delta z)).mp hanc_rev⟩
        · left
          have hdisj : Disjoint (H_lt.walkVertices (G'.tail e) (pi_r e)).toFinset S_prev := by
            rw [Finset.disjoint_left]
            intro v hv hvS
            apply heAff
            refine Finset.mem_filter.mpr ⟨heG', ?_⟩
            simp only [decide_eq_true_eq, hpi_eq e heG']
            exact ⟨v, List.mem_toFinset.mp hv, hvS⟩
          have hw_r := hEmb_lt_r.2 e (hEG'_sub heG')
          obtain ⟨ht0_V, hh0_V⟩ := hVG_r e (hEG'_sub heG')
          obtain ⟨ht_V, _⟩ := hVG' e heG'
          obtain ⟨hanc_t, _⟩ := hAncEnds e (hEG'_sub heG')
          have hSurv := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt hHLtV hHLtE hEnds_lt
            hTouch (pi_r e) (G_r.tail e) (G_r.head e) (G'.tail e) ht0_V hh0_V hw_r ht_V hanc_t).1 hdisj
          have heq_w : pi_new e = pi_r e := by simp [pi_new, heAff, hpi_eq e heG']
          have hw_eq := walkVertices_of_isSubgraph hHlt_sub_Hnew hSurv.2.1
          have hz_lt : z ∈ H_lt.walkVertices (G'.tail e) (pi_r e) := by
            rw [heq_w] at hz_w
            exact hw_eq.symm ▸ hz_w
          have hz_notS : z ∉ S_prev := fun h =>
            (Finset.disjoint_left.mp hdisj) (List.mem_toFinset.mpr hz_lt) h
          have hnt := not_mem_allTouched_invariants delta G_r hVG_r hBV_d hds_d z
            fun h => hz_notS (hTouch h)
          rw [hSurv.2.2] at hz_lt
          refine Finset.mem_filter.mpr ⟨hEG'_sub heG', ?_⟩
          rwa [hnt.2.1 (hnt.1 hzG')]
      have hcard_le : (F.card : ℝ) ≤ (F_orig.card : ℝ) + (F_mid.card : ℝ) := by
        exact_mod_cast le_trans (Finset.card_le_card hF_sub) (Finset.card_union_le _ _)
      have hForig_le : (F_orig.card : ℝ) ≤ V_prev := by
        have h1 : (F_orig.card : ℝ) =
            Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) (batchAnc delta z) := by
          simp [F_orig, Embedding.vcongAt]
        have hz_lt : batchAnc delta z ∈ H_lt_r.V := hEmb_lt_r.1 hz0
        have h2 : Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1) (batchAnc delta z) ≤
            Embedding.vcong pi_r G_r H_lt_r (fun _ => 1) := by
          unfold Embedding.vcong
          have hltNe : H_lt_r.V.Nonempty := ⟨_, hz_lt⟩
          simp only [hltNe, ↓reduceDIte]
          exact Finset.le_sup' (f := Embedding.vcongAt pi_r G_r H_lt_r (fun _ => 1)) hz_lt
        exact le_trans (h1 ▸ h2) hVcong_r
      have hFmid_le : (F_mid.card : ℝ) ≤
          P.γ_c * (lenBound P.γ_ℓ i + 1) * (V_prev + 2 * V_prev) := by
        have h1 : (F_mid.card : ℝ) = Embedding.vcongAt embMid J H_aux (fun _ => 1) z := by
          simp [F_mid, J, buildProjGraph, Embedding.vcongAt]
        have hzAux : z ∈ H_aux.V := hzG'
        have h2 : Embedding.vcongAt embMid J H_aux (fun _ => 1) z ≤
            Embedding.vcong embMid J H_aux (fun _ => 1) := by
          unfold Embedding.vcong
          have hauxNe : H_aux.V.Nonempty := ⟨z, hzAux⟩
          simp only [hauxNe, ↓reduceDIte]
          exact Finset.le_sup' (f := Embedding.vcongAt embMid J H_aux (fun _ => 1)) hzAux
        exact le_trans (h1 ▸ h2) hVcMid_le
      have hvc_z : Embedding.vcongAt pi_new G' H_new_lt (fun _ => 1) z = (F.card : ℝ) := by
        simp [F, Embedding.vcongAt]
      rw [hvc_z]
      exact le_trans hcard_le (le_trans (add_le_add hForig_le hFmid_le) hVstep)
    · exact hVnext_nn
  exact ⟨hAff_card, hJm, hJn, hOut_sub_aff, hSub_Hj, hHj_valid, hHnew_sub, hHnew_V, hHnew_valid,
    hPi_new_emb, hPi_new_len, hPi_new_vcong,
    fun hEne => ⟨hEmbJH_len, (hNonempty_bnd hEne).1, (hNonempty_bnd hEne).2⟩,
    hJH_edges, hEmpty_bnd, hEmbOut,
    hV_aux, hJ_valid, hJm_max, hEmbJH, hLenMid_le⟩

end

end RebuildSpecs

end MinCostFlow.DynSpanner
