module

public import MinCostFlow.SparseCore.CompLSFBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Forest validity, `LSF.Holds`, touched components, and MWU bridge for `CompLSF`

Builds on `CompLSFBounds.lean` to prove:
1. `compLSFBatch` invariance (`compLSFBatch_inv`, `compLSFBatch_compSt`, `compLSFBatch_projValid`),
2. Forest and rooted spanning forest structure (`compLSF_T_isForest`, `compLSF_RF_isRSF`,
   `compLSF_RF_root_eq`),
3. `CompLSFInv.to_Holds` (`cs.lsf.Holds cs.G ℓ (6272 * max 1 C_lsst * cs.k * log^6(G₀.n + 2))`),
4. `sum_projCompBatchG_length_le`, `touchedCompsBatch` (`≤ 2 * U.length`),
   `compLSF_connected_R_card_le`, and `compLSF_mwu_bound` via `lemma_5_5_online`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

@[expose] public section

/-! ## 1. Batch corollaries and forest structure -/

lemma compLSFBatch_append (cs : CompLSFState) (U₁ U₂ : List Update) :
    compLSFBatch cs (U₁ ++ U₂) = compLSFBatch (compLSFBatch cs U₁) U₂ :=
  List.foldl_append

lemma compLSFBatch_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    CompLSFInv C_lsst ℓ₀ (compLSFBatch cs U) :=
  (compLSFBatch_step_props U hI hU).1

lemma compLSFBatch_compSt {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    (compLSFBatch cs U).compSt C =
      applyLSFBatch (cs.compSt C) (projCompBatchG cs.G (cs.compSt C).G U) ∧
    ((compLSFBatch cs U).compSt C).G =
      (cs.compSt C).G.applyBatch (projCompBatchG cs.G (cs.compSt C).G U) ∧
    (cs.compSt C).G.BatchIsValid (projCompBatchG cs.G (cs.compSt C).G U) ∧
    (cs.compSt C).R ⊆ ((compLSFBatch cs U).compSt C).R ∧
    ((compLSFBatch cs U).compSt C).RF.F.E ⊆ (cs.compSt C).RF.F.E :=
  (compLSFBatch_step_props U hI hU).2.2.1 C hC

lemma compLSFBatch_decremental {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    (compLSFBatch cs U).RF.F.E ⊆ cs.RF.F.E ∧ cs.RF.R ⊆ (compLSFBatch cs U).RF.R :=
  ⟨(compLSFBatch_step_props U hI hU).2.2.2.1, (compLSFBatch_step_props U hI hU).2.2.2.2⟩

/-- On a connected initial graph `S.G₀`, the spanning tree `S.T₀` (and hence `S.T_cur`) has no
bridge edges: every edge of `S.T_cur.E` belongs to `S.G₀.E`. -/
lemma lsfInv_T_E_subset_G₀_of_connected {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S)
    (hConn : ∀ u ∈ S.G₀.V, ∀ v ∈ S.G₀.V, S.G₀.Connected u v) :
    S.T_cur.E ⊆ S.G₀.E := by
  intro f hf
  have hfT : f ∈ S.T₀.E := hI.hT_cur_E ▸ hf
  have hT := hI.hT₀
  have hf_ends := hT.isForest.1 f hfT
  obtain ⟨c, p, hcV, hpV, hcr, hp, hpe⟩ :
      ∃ c p, c ∈ S.T₀.V ∧ p ∈ S.T₀.V ∧ c ≠ S.r₀ ∧ parent S.T₀ S.r₀ c = p ∧
        parentEdge S.T₀ S.r₀ c = f := by
    rcases edge_parent_orientation hT hfT with ⟨hp, hpe, hne⟩ | ⟨hp, hpe, hne⟩
    · exact ⟨S.T₀.tail f, S.T₀.head f, hf_ends.1, hf_ends.2, hne, hp, hpe⟩
    · exact ⟨S.T₀.head f, S.T₀.tail f, hf_ends.2, hf_ends.1, hne, hp, hpe⟩
  have hc_sub : c ∈ subtree S.T₀ S.r₀ c := mem_subtree_iff.mpr ⟨hcV, isAncestor_refl _ _ _⟩
  have hp_nsub : p ∉ subtree S.T₀ S.r₀ c := by
    intro hmem
    have hanc : IsAncestor S.T₀ S.r₀ c p := (mem_subtree_iff.mp hmem).2
    have hle := isAncestor_depth_le hT hpV hanc
    have hdp := depth_parent hT hcV hcr
    rw [hp] at hdp
    omega
  obtain ⟨P, hP⟩ := hConn c (hI.hTV ▸ hcV) p (hI.hTV ▸ hpV)
  obtain ⟨e, heE, hsplit⟩ := comp_walk_exit hP hc_sub hp_nsub
  have htV : S.G₀.tail e ∈ S.T₀.V := hI.hTV.symm ▸ (hI.hG₀_val e heE).1
  have hhV : S.G₀.head e ∈ S.T₀.V := hI.hTV.symm ▸ (hI.hG₀_val e heE).2
  have hdiff : ¬ (IsAncestor S.T₀ S.r₀ c (S.G₀.tail e) ↔ IsAncestor S.T₀ S.r₀ c (S.G₀.head e)) := by
    rcases hsplit with ⟨htS, hhNS⟩ | ⟨hhS, htNS⟩
    · intro hiff
      exact hhNS (mem_subtree_iff.mpr ⟨hhV, hiff.mp (mem_subtree_iff.mp htS).2⟩)
    · intro hiff
      exact htNS (mem_subtree_iff.mpr ⟨htV, hiff.mpr (mem_subtree_iff.mp hhS).2⟩)
  have hf_path : f ∈ walkEdges (S.T₀.forestPath (S.G₀.tail e) (S.G₀.head e)) := by
    rw [← hpe]
    exact (parentEdge_mem_walkEdges_iff hT hcV hcr htV hhV).mpr hdiff
  exact hI.hTp₀ e heE hf_path

/-- On any `CompLSFInv` state, every component tree edge lies in `compEdgeSet cs.G₀ C`, so
`encTEdge` is the identity on every tree edge (no bridge edge names occur). -/
lemma compLSF_encTEdge_eq_self {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    {f : ℕ} (hf : f ∈ (cs.compSt C).T_cur.E) :
    f ∈ compEdgeSet cs.G₀ C ∧ encTEdge cs.G₀ C f = f := by
  have hCI := (hI.hCompLSF C hC).1
  have hG₀C : (cs.compSt C).G₀ = compGraph cs.G₀ C := (hI.hCompLSF C hC).2.1
  have hConn : ∀ u ∈ (cs.compSt C).G₀.V, ∀ v ∈ (cs.compSt C).G₀.V,
      (cs.compSt C).G₀.Connected u v := by
    rw [hG₀C]
    exact compGraph_connected hI.hG₀_val hC
  have hfC : f ∈ compEdgeSet cs.G₀ C := by
    have := lsfInv_T_E_subset_G₀_of_connected hCI hConn hf
    rwa [hG₀C] at this
  exact ⟨hfC, encTEdge_eq_self hfC⟩

private lemma compLSF_T_edge_comp {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.T.E) :
    ∃ C ∈ components cs.G₀, e ∈ (cs.compSt C).T₀.E ∧ e ∈ (cs.compSt C).G.E ∧
      e ∉ (cs.compSt C).insertedEdges ∧
      (cs.compSt C).G.tail e = cs.G.tail e ∧ (cs.compSt C).G.head e = cs.G.head e := by
  have he' : e ∈ ((components cs.G₀).biUnion fun C =>
      (cs.compSt C).T_cur.E.image (encTEdge cs.G₀ C)) ∩ (cs.G.E \ cs.insertedGlobal) := he
  rw [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_sdiff] at he'
  rcases he' with ⟨⟨C, hC, hf_im⟩, heG, hni⟩
  rcases Finset.mem_image.mp hf_im with ⟨f, hfT, henc⟩
  have hself := compLSF_encTEdge_eq_self hI hC hfT
  rw [hself.2] at henc
  subst henc
  obtain ⟨C', hC', heC', hniC', _⟩ := hI.hWstr_surv f heG hni
  have hCI' := (hI.hCompLSF C' hC').1
  have hfC' : f ∈ compEdgeSet cs.G₀ C' := by
    have h0 := (hCI'.hsurv_edge f heC' hniC').1
    rwa [(hI.hCompLSF C' hC').2.1] at h0
  have hCC' : C' = C := by
    by_contra hne
    exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint cs.G₀ hC' hC hne) hfC' hself.1
  subst hCC'
  have hnc := hI.hNonIns_notCross C' hC' f heC' hniC'
  have hends := hI.hNonCross_ends C' hC' f heC' hnc
  exact ⟨C', hC', (hI.hCompLSF C' hC').1.hT_cur_E ▸ hfT, heC', hniC', hends.1, hends.2⟩

private lemma compLSF_T_walk_stay {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, u ∈ (cs.compSt C).G.V → cs.T.IsWalk u v P →
      v ∈ (cs.compSt C).G.V ∧
      (cs.compSt C).T₀.IsWalk ((cs.compSt C).origVert u) ((cs.compSt C).origVert v) P
  | u, _, _, hu, .nil _ => ⟨hu, .nil _⟩
  | u, v, x :: rest, hu, .cons hxE hxSrc hrest => by
    obtain ⟨C₁, hC₁, hxT₀, hxG, hxni, hxt, hxh⟩ := compLSF_T_edge_comp hI hxE
    have hCI₁ := (hI.hCompLSF C₁ hC₁).1
    have hx_ends := hCI₁.hG_val x.1 hxG
    have hsrc_mem : cs.T.src x ∈ (cs.compSt C₁).G.V := by
      unfold MGraph.src
      change (if x.2 = true then cs.G.tail x.1 else cs.G.head x.1) ∈ _
      rw [← hxt, ← hxh]
      split_ifs <;> [exact hx_ends.1; exact hx_ends.2]
    have hdst_mem : cs.T.dst x ∈ (cs.compSt C₁).G.V := by
      unfold MGraph.dst
      change (if x.2 = true then cs.G.head x.1 else cs.G.tail x.1) ∈ _
      rw [← hxt, ← hxh]
      split_ifs <;> [exact hx_ends.2; exact hx_ends.1]
    have hCC₁ : C₁ = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C hC hne) (hxSrc ▸ hsrc_mem) hu
    subst hCC₁
    have hih := compLSF_T_walk_stay hI hC₁ hdst_mem hrest
    have horig := hCI₁.horig_G_nins x.1 hxG hxni
    have hxG₀ : x.1 ∈ (cs.compSt C₁).G₀.E := (hCI₁.hsurv_edge x.1 hxG hxni).1
    have hTG₀ := hCI₁.hTG₀ x.1 hxT₀ hxG₀
    have hsrc_proj : (cs.compSt C₁).T₀.src x = (cs.compSt C₁).origVert u := by
      rw [← hxSrc]
      unfold MGraph.src
      change (if x.2 = true then (cs.compSt C₁).T₀.tail x.1 else (cs.compSt C₁).T₀.head x.1) =
        (cs.compSt C₁).origVert (if x.2 = true then cs.G.tail x.1 else cs.G.head x.1)
      rw [← hxt, ← hxh]
      split_ifs <;> [exact (horig.1.trans hTG₀.1.symm).symm; exact (horig.2.trans hTG₀.2.symm).symm]
    have hdst_proj : (cs.compSt C₁).T₀.dst x = (cs.compSt C₁).origVert (cs.T.dst x) := by
      unfold MGraph.dst
      change (if x.2 = true then (cs.compSt C₁).T₀.head x.1 else (cs.compSt C₁).T₀.tail x.1) =
        (cs.compSt C₁).origVert (if x.2 = true then cs.G.head x.1 else cs.G.tail x.1)
      rw [← hxt, ← hxh]
      split_ifs <;> [exact (horig.2.trans hTG₀.2.symm).symm; exact (horig.1.trans hTG₀.1.symm).symm]
    exact ⟨hih.1, .cons hxT₀ hsrc_proj (hdst_proj.symm ▸ hih.2)⟩

lemma compLSF_T_isForest {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.T.IsForest := by
  refine ⟨?_, ?_⟩
  · intro e he
    have heG : e ∈ cs.G.E := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1
    exact hI.hG_val e heG
  · rintro P ⟨hne, hnodup, u, huw⟩
    rcases List.exists_cons_of_ne_nil hne with ⟨x, rest, rfl⟩
    cases huw with
    | cons hxE hxSrc hrest =>
      have huV : u ∈ cs.G.V := by
        have heG : x.1 ∈ cs.G.E := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxE).2).1
        have hval : cs.T.src x ∈ cs.G.V := by
          unfold MGraph.src
          change (if x.2 = true then cs.G.tail x.1 else cs.G.head x.1) ∈ cs.G.V
          split_ifs <;> [exact (hI.hG_val x.1 heG).1; exact (hI.hG_val x.1 heG).2]
        exact hxSrc ▸ hval
      rw [← hI.hV_eq, Finset.mem_biUnion] at huV
      rcases huV with ⟨C, hC, huC⟩
      have hw := compLSF_T_walk_stay hI hC huC (.cons hxE hxSrc hrest)
      exact (hI.hCompLSF C hC).1.hT₀.isForest.2 (x :: rest) ⟨hne, hnodup, _, hw.2⟩

lemma lsfInv_to_RF_sub_T {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) :
    S.T.IsSubgraph S.RF.F := by
  let ℓ_tmp : ℕ → ℝ := fun e => if e ∈ S.G₀.E ∧ e ∉ S.insertedEdges then ℓ₀ e else 1
  have hℓ_pos : ∀ e ∈ S.G.E, 0 < ℓ_tmp e := fun e _ => by
    dsimp only [ℓ_tmp]; split_ifs with h; exact hI.hℓ₀ e h.1; exact zero_lt_one
  have hℓ_orig : ∀ e ∈ S.G₀.E, e ∈ S.G.E → e ∉ S.insertedEdges → ℓ_tmp e = ℓ₀ e :=
    fun e he₀ _ hni => by simp [ℓ_tmp, he₀, hni]
  exact (hI.to_Holds hℓ_pos hℓ_orig).2.2.1

private lemma lsfInv_RF_edge_not_inserted {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) {e : ℕ} (heF : e ∈ S.RF.F.E) :
    e ∉ S.insertedEdges := by
  intro heI
  have hRS := lsfInv_to_RS hI
  have hw := hI.hins_wstr e heI
  have hFG := hRS.2.2.2.2.2.2 e heF
  have htV : S.RF.F.tail e ∈ S.G.V := hRS.2.1 ▸ (hRS.1.1 e heF).1
  have hu : S.RF.F.tail e ∈ S.RF.R ∧ S.RF.F.Connected (S.RF.F.tail e) (S.RF.F.tail e) :=
    ⟨hFG.1 ▸ hw.2.1, connected_refl _ _⟩
  have hv : S.RF.F.head e ∈ S.RF.R ∧ S.RF.F.Connected (S.RF.F.tail e) (S.RF.F.head e) :=
    ⟨hFG.2 ▸ hw.2.2, ⟨[(e, true)], .cons heF rfl (.nil _)⟩⟩
  obtain ⟨r, _, huniq⟩ := hRS.2.2.2.1 _ htV
  have hth : S.RF.F.tail e = S.RF.F.head e := (huniq _ hu).trans (huniq _ hv).symm
  exact hRS.1.2 [(e, true)] ⟨by simp, by simp, S.RF.F.tail e,
    .cons heF rfl (by simpa [MGraph.dst, hth] using MGraph.IsWalk.nil (S.RF.F.tail e))⟩

lemma compLSF_RF_sub_T {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.T.IsSubgraph cs.RF.F := by
  refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  intro e he
  change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) at he
  rw [Finset.mem_biUnion] at he
  rcases he with ⟨C, hC, heC⟩
  have hCI := (hI.hCompLSF C hC).1
  have he_comp := hI.hF_sub_compE C hC heC
  have he_T := (lsfInv_to_RF_sub_T hCI).2.1 heC
  have he_CG := (lsfInv_to_RS hCI).2.2.2.2.2.1 heC
  have he_G := hI.hCE_sub C hC he_CG
  have hniC := lsfInv_RF_edge_not_inserted hCI heC
  have hniG : e ∉ cs.insertedGlobal := fun hm => hniC (hI.hCE_ins C hC e he_CG hm)
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_image.mpr ⟨e, he_T, encTEdge_eq_self he_comp⟩⟩,
     Finset.mem_sdiff.mpr ⟨he_G, hniG⟩⟩

lemma compLSF_RF_sub_comp {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    cs.RF.F.IsSubgraph (cs.compSt C).RF.F := by
  have hCI := (hI.hCompLSF C hC).1
  have hRS := lsfInv_to_RS hCI
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hRS.2.1] at hx
    change x ∈ cs.G.V
    rw [← hI.hV_eq]
    exact Finset.mem_biUnion.mpr ⟨C, hC, hx⟩
  · intro e he
    exact Finset.mem_biUnion.mpr ⟨C, hC, he⟩
  · intro e he
    have he_G := hRS.2.2.2.2.2.1 he
    have hni := lsfInv_RF_edge_not_inserted hCI he
    have hnc := hI.hNonIns_notCross C hC e he_G hni
    have hends := hI.hNonCross_ends C hC e he_G hnc
    have hGF := hRS.2.2.2.2.2.2 e he
    exact ⟨hGF.1.trans hends.1, hGF.2.trans hends.2⟩

private lemma compLSF_RF_walk_stay {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, u ∈ (cs.compSt C).G.V → cs.RF.F.IsWalk u v P →
      v ∈ (cs.compSt C).G.V ∧ (cs.compSt C).RF.F.IsWalk u v P
  | u, _, _, hu, .nil _ => ⟨hu, .nil u⟩
  | u, v, x :: rest, hu, .cons hxE hxSrc hrest => by
    have hxE' : x.1 ∈ cs.RF.F.E := hxE
    change x.1 ∈ (components cs.G₀).biUnion (fun C₁ => (cs.compSt C₁).RF.F.E) at hxE'
    rw [Finset.mem_biUnion] at hxE'
    rcases hxE' with ⟨C₁, hC₁, hxC₁⟩
    have hCI₁ := (hI.hCompLSF C₁ hC₁).1
    have hRS₁ := lsfInv_to_RS hCI₁
    have hx_sub := compLSF_RF_sub_comp hI hC₁
    have hx_ends := hRS₁.1.1 x.1 hxC₁
    have hsrc_V : cs.RF.F.src x ∈ (cs.compSt C₁).G.V := by
      unfold MGraph.src
      rw [← (hx_sub.2.2 x.1 hxC₁).1, ← (hx_sub.2.2 x.1 hxC₁).2, ← hRS₁.2.1]
      split_ifs
      · exact hx_ends.1
      · exact hx_ends.2
    have hdst_V : cs.RF.F.dst x ∈ (cs.compSt C₁).G.V := by
      unfold MGraph.dst
      rw [← (hx_sub.2.2 x.1 hxC₁).1, ← (hx_sub.2.2 x.1 hxC₁).2, ← hRS₁.2.1]
      split_ifs
      · exact hx_ends.2
      · exact hx_ends.1
    have hCC₁ : C₁ = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C hC hne) (hxSrc ▸ hsrc_V) hu
    subst hCC₁
    have hih := compLSF_RF_walk_stay hI hC₁ hdst_V hrest
    have hsrc' : (cs.compSt C₁).RF.F.src x = u := by
      rw [← hxSrc]
      unfold MGraph.src
      rw [(hx_sub.2.2 x.1 hxC₁).1, (hx_sub.2.2 x.1 hxC₁).2]
    have hdst' : (cs.compSt C₁).RF.F.dst x = cs.RF.F.dst x := by
      unfold MGraph.dst
      rw [(hx_sub.2.2 x.1 hxC₁).1, (hx_sub.2.2 x.1 hxC₁).2]
    exact ⟨hih.1, .cons hxC₁ hsrc' (hdst'.symm ▸ hih.2)⟩

private lemma walk_of_isSubgraph {G H : MGraph} (hsub : G.IsSubgraph H) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → G.IsWalk u v P
  | u, _, _, .nil _ => .nil u
  | u, v, x :: rest, .cons hxE hxSrc hrest =>
    have he := hsub.2.2 x.1 hxE
    have hsrc : G.src x = H.src x := by unfold MGraph.src; rw [he.1, he.2]
    have hdst : G.dst x = H.dst x := by unfold MGraph.dst; rw [he.1, he.2]
    .cons (hsub.2.1 hxE) (hsrc.trans hxSrc) (hdst ▸ walk_of_isSubgraph hsub hrest)

lemma compLSF_RF_isRSF {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.RF.IsRootedSpanningForestOf cs.G := by
  have hsubT := compLSF_RF_sub_T hI
  have hT_for := compLSF_T_isForest hI
  have hG_sub_RF : cs.G.IsSubgraph cs.RF.F := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    intro e he
    change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) at he
    rw [Finset.mem_biUnion] at he
    rcases he with ⟨C, hC, heC⟩
    exact hI.hCE_sub C hC ((lsfInv_to_RS (hI.hCompLSF C hC).1).2.2.2.2.2.1 heC)
  have hRF_val : cs.RF.F.IsValid := fun e he => by
    have hGe := hI.hG_val e (hG_sub_RF.2.1 he)
    exact hGe
  have hRF_for : cs.RF.F.IsForest := isForest_subgraph hT_for hsubT hRF_val
  have hR_sub : cs.RF.R ⊆ cs.G.V := by
    intro r hr
    change r ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).R) at hr
    rw [Finset.mem_biUnion] at hr
    rcases hr with ⟨C, hC, hrC⟩
    rw [← hI.hV_eq]
    exact Finset.mem_biUnion.mpr ⟨C, hC, lsfInv_R_sub_V (hI.hCompLSF C hC).1 hrC⟩
  refine ⟨hRF_for, rfl, hR_sub, ?_, hG_sub_RF⟩
  intro v hv
  rw [← hI.hV_eq, Finset.mem_biUnion] at hv
  rcases hv with ⟨C, hC, hvC⟩
  have hCI := (hI.hCompLSF C hC).1
  have hRS := lsfInv_to_RS hCI
  obtain ⟨r, ⟨hrR, ⟨P, hP⟩⟩, huniq⟩ := hRS.2.2.2.1 v hvC
  refine ⟨r, ⟨Finset.mem_biUnion.mpr ⟨C, hC, hrR⟩, ⟨P, ?_⟩⟩, ?_⟩
  · exact walk_of_isSubgraph (compLSF_RF_sub_comp hI hC) hP
  · rintro r' ⟨hr'R, ⟨Q, hQ⟩⟩
    change r' ∈ (components cs.G₀).biUnion (fun C₁ => (cs.compSt C₁).R) at hr'R
    rw [Finset.mem_biUnion] at hr'R
    rcases hr'R with ⟨C₁, hC₁, hr'C₁⟩
    have hw := compLSF_RF_walk_stay hI hC hvC hQ
    have hr'_V : r' ∈ (cs.compSt C₁).G.V := lsfInv_R_sub_V (hI.hCompLSF C₁ hC₁).1 hr'C₁
    have hCC₁ : C₁ = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁ C hC hne) hr'_V hw.1
    subst hCC₁
    exact huniq r' ⟨hr'C₁, ⟨Q, hw.2⟩⟩

lemma compLSF_RF_root_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    {v : ℕ} (hv : v ∈ (cs.compSt C).G.V) :
    cs.RF.root v = (cs.compSt C).RF.root v := by
  have hRS := compLSF_RF_isRSF hI
  have hRS_C := lsfInv_to_RS (hI.hCompLSF C hC).1
  have hvG : v ∈ cs.G.V := hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C, hC, hv⟩
  have hspec := rootedForest_root_spec hRS_C hv
  obtain ⟨P, hP⟩ := hspec.2
  have hconn : cs.RF.F.Connected v ((cs.compSt C).RF.root v) :=
    ⟨P, walk_of_isSubgraph (compLSF_RF_sub_comp hI hC) hP⟩
  exact rootedForest_root_eq_of_mem hRS hvG
    (Finset.mem_biUnion.mpr ⟨C, hC, hspec.1⟩) hconn

/-! ## 2. `LSF.Holds`, touched components, root bound, and MWU bound -/

private lemma log_three_ge_one : (1 : ℝ) ≤ Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

private lemma forestPath_eq_nil_of_not_connected {F : MGraph} {u v : ℕ}
    (hnc : ¬ F.Connected u v) : F.forestPath u v = [] := by
  dsimp only [MGraph.forestPath]
  split_ifs with h
  · exact absurd ⟨h.choose, h.choose_spec.1⟩ hnc
  · rfl

lemma CompLSFInv.to_Holds {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ cs.G.E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ cs.G₀.E, e ∈ cs.G.E → e ∉ cs.insertedGlobal → ℓ e = ℓ₀ e) :
    cs.lsf.Holds cs.G ℓ (6272 * max 1 C_lsst * (cs.k : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 6) := by
  have hT_for := compLSF_T_isForest hI
  have hRS := compLSF_RF_isRSF hI
  have hsub_TF := compLSF_RF_sub_T hI
  refine ⟨hT_for, hRS, hsub_TF, fun e he => ?_⟩
  have hk_real : (1 : ℝ) ≤ (cs.k : ℝ) := by exact_mod_cast hI.hk
  have hn₀_pos : 1 ≤ cs.G₀.n := Finset.card_pos.mpr hI.hV₀
  have hlog3 : (1 : ℝ) ≤ Real.log ((cs.G₀.n : ℝ) + 2) := by
    refine le_trans log_three_ge_one (Real.log_le_log (by norm_num) ?_)
    have : (1 : ℝ) ≤ cs.G₀.n := by exact_mod_cast hn₀_pos
    linarith
  have hlog6 : (1 : ℝ) ≤ (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 6 := by
    have : 0 ≤ Real.log ((cs.G₀.n : ℝ) + 2) := by positivity
    exact one_le_pow₀ hlog3
  have hmax : (1 : ℝ) ≤ max 1 C_lsst := le_max_left _ _
  have hσ_ge1 : (1 : ℝ) ≤ 6272 * max 1 C_lsst * (cs.k : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 6 := by
    nlinarith [mul_le_mul (mul_le_mul hmax hk_real (by norm_num) (by positivity)) hlog6 (by norm_num) (by positivity)]
  by_cases heI : e ∈ cs.insertedGlobal
  · obtain ⟨hw1, ⟨C₁, hC₁, htR⟩, ⟨C₂, hC₂, hhR⟩⟩ := hI.hIns_wstr_R e heI
    have htR' : cs.G.tail e ∈ cs.RF.R := Finset.mem_biUnion.mpr ⟨C₁, hC₁, htR⟩
    have hhR' : cs.G.head e ∈ cs.RF.R := Finset.mem_biUnion.mpr ⟨C₂, hC₂, hhR⟩
    have hrt := rootedForest_root_self hRS htR'
    have hrh := rootedForest_root_self hRS hhR'
    have hstr : cs.RF.stretch cs.G ℓ e = 1 := by
      dsimp only [RootedForest.stretch]
      rw [hrt, hrh]
      split_ifs with heq
      · rw [heq]; simp [forestPath_self hRS.1, walkLength]
      · simp [forestPath_self hRS.1, walkLength]
    change cs.RF.stretch cs.G ℓ e ≤ cs.wstrGlobal e ∧ cs.wstrGlobal e ≤ _
    rw [hstr, hw1]
    exact ⟨le_rfl, hσ_ge1⟩
  · obtain ⟨C, hC, heC, hniC, hwC⟩ := hI.hWstr_surv e he heI
    have hCI := (hI.hCompLSF C hC).1
    have hRS_C := lsfInv_to_RS hCI
    have hnc := hI.hNonIns_notCross C hC e heC hniC
    have hends := hI.hNonCross_ends C hC e heC hnc
    have hℓ_C : ∀ f ∈ (cs.compSt C).G.E, 0 < ℓ f := fun f hf => hℓ f (hI.hCE_sub C hC hf)
    have hℓ_orig_C : ∀ f ∈ (cs.compSt C).G₀.E, f ∈ (cs.compSt C).G.E →
        f ∉ (cs.compSt C).insertedEdges → ℓ f = ℓ₀ f := by
      intro f hf₀ hfC hfni
      have hf₀' : f ∈ cs.G₀.E :=
        Finset.filter_subset _ _ ((hI.hCompLSF C hC).2.1 ▸ hf₀)
      have hfg : f ∈ cs.G.E := hI.hCE_sub C hC hfC
      have hfniG : f ∉ cs.insertedGlobal := fun hm => hfni (hI.hCE_ins C hC f hfC hm)
      exact hℓ_orig f hf₀' hfg hfniG
    have hHC := hCI.to_Holds hℓ_C hℓ_orig_C
    have hHCe := hHC.2.2.2 e heC
    have huC : (cs.compSt C).G.tail e ∈ (cs.compSt C).G.V := (hCI.hG_val e heC).1
    have hvC : (cs.compSt C).G.head e ∈ (cs.compSt C).G.V := (hCI.hG_val e heC).2
    have hrt : cs.RF.root (cs.G.tail e) = (cs.compSt C).RF.root ((cs.compSt C).G.tail e) := by
      rw [← hends.1]; exact compLSF_RF_root_eq hI hC huC
    have hrh : cs.RF.root (cs.G.head e) = (cs.compSt C).RF.root ((cs.compSt C).G.head e) := by
      rw [← hends.2]; exact compLSF_RF_root_eq hI hC hvC
    have hsubC := compLSF_RF_sub_comp hI hC
    have hstr_eq : cs.RF.stretch cs.G ℓ e = (cs.compSt C).RF.stretch (cs.compSt C).G ℓ e := by
      dsimp only [RootedForest.stretch]
      rw [hrt, hrh, ← hends.1, ← hends.2]
      set u := (cs.compSt C).G.tail e
      set v := (cs.compSt C).G.head e
      split_ifs with hrt_eq
      · by_cases hconn : (cs.compSt C).RF.F.Connected u v
        · rw [forestPath_subgraph hRS.1 hsubC hconn]
        · have hconn_g : ¬ cs.RF.F.Connected u v := by
            intro hc
            rcases hc with ⟨P, hP⟩
            exact hconn ⟨P, (compLSF_RF_walk_stay hI hC huC hP).2⟩
          rw [forestPath_eq_nil_of_not_connected hconn, forestPath_eq_nil_of_not_connected hconn_g]
      · have hconn_u := (rootedForest_root_spec hRS_C huC).2
        have hconn_v := (rootedForest_root_spec hRS_C hvC).2
        rw [forestPath_subgraph hRS.1 hsubC hconn_u,
          forestPath_subgraph hRS.1 hsubC hconn_v]
    have hGC_ne : (compGraph cs.G₀ C).V.Nonempty := compGraph_nonempty hC
    have hnC_pos : 1 ≤ (compGraph cs.G₀ C).n := Finset.card_pos.mpr hGC_ne
    have hnC_le : (compGraph cs.G₀ C).n ≤ cs.G₀.n := compGraph_n_le hC
    have hlogC : Real.log (((cs.compSt C).G₀.n : ℝ) + 2) ≤ Real.log ((cs.G₀.n : ℝ) + 2) := by
      rw [(hI.hCompLSF C hC).2.1]
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph cs.G₀ C).n : ℝ) ≤ cs.G₀.n := by exact_mod_cast hnC_le
      linarith
    have hlogC_nn : 0 ≤ Real.log (((cs.compSt C).G₀.n : ℝ) + 2) := by
      rw [(hI.hCompLSF C hC).2.1]
      linarith [half_lt_log_add_two (compGraph cs.G₀ C).n]
    have hpowC : (Real.log (((cs.compSt C).G₀.n : ℝ) + 2)) ^ 6 ≤
        (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 6 := pow_le_pow_left₀ hlogC_nn hlogC 6
    have hk_eq := (hI.hCompLSF C hC).2.2
    have hw_bound : (cs.compSt C).wstr e ≤
        6272 * max 1 C_lsst * (cs.k : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 6 := by
      have h2 : (cs.compSt C).wstr e ≤
          6272 * max 1 C_lsst * (cs.compSt C).k * (Real.log (((cs.compSt C).G₀.n : ℝ) + 2)) ^ 6 :=
        hHCe.2
      rw [hk_eq] at h2
      have hc_nn : 0 ≤ 6272 * max 1 C_lsst * (cs.k : ℝ) := by positivity
      exact le_trans h2 (mul_le_mul_of_nonneg_left hpowC hc_nn)
    change cs.RF.stretch cs.G ℓ e ≤ cs.wstrGlobal e ∧ cs.wstrGlobal e ≤ _
    rw [hstr_eq, hwC]
    exact ⟨hHCe.1, hw_bound⟩

/-- Components touched by single global update `u`. -/
noncomputable def touchedComps (cs : CompLSFState) (u : Update) : Finset (Finset ℕ) :=
  open Classical in (components cs.G₀).filter fun C =>
    projCompUpdateG cs.G (cs.compSt C).G u ≠ []

/-- Sum of projected lengths of `u` over all components is at most `4`. -/
lemma sum_projCompUpdateG_length_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (u : Update) :
    ((components cs.G₀).sum fun C => (projCompUpdateG cs.G (cs.compSt C).G u).length) ≤ 4 := by
  classical
  cases u with
  | delete e =>
    calc (components cs.G₀).sum (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.delete e)).length)
        = ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).sum (fun _ => 1) := by
          rw [← Finset.sum_filter_add_sum_filter_not (components cs.G₀) (fun C => e ∈ (cs.compSt C).G.E)]
          have h1 : ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).sum
              (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.delete e)).length) =
              ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).sum (fun _ => 1) :=
            Finset.sum_congr rfl fun C hC => by
              simp [projCompUpdateG, (Finset.mem_filter.mp hC).2]
          have h2 : ((components cs.G₀).filter fun C => e ∉ (cs.compSt C).G.E).sum
              (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.delete e)).length) = 0 :=
            Finset.sum_eq_zero fun C hC => by
              simp [projCompUpdateG, (Finset.mem_filter.mp hC).2]
          omega
      _ = ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).card := by simp
      _ ≤ 4 := le_trans (hI.hEdge_atMostTwo e) (by omega)
  | insert e a b =>
    let Sa := (components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V
    let Sb := (components cs.G₀).filter fun C => b ∈ (cs.compSt C).G.V
    have hcard : ∀ (P : Finset ℕ → Prop) [DecidablePred P] (S : Finset (Finset ℕ)),
        (∀ C₁ ∈ components cs.G₀, ∀ C₂ ∈ components cs.G₀, C₁ ≠ C₂ → ¬(P C₁ ∧ P C₂)) →
        ((components cs.G₀).filter P).card ≤ 1 := fun P _ _ hdisj =>
      Finset.card_le_one.mpr fun C₁ h₁ C₂ h₂ => by
        by_contra hne
        have hm₁ := Finset.mem_filter.mp h₁
        have hm₂ := Finset.mem_filter.mp h₂
        exact hdisj C₁ hm₁.1 C₂ hm₂.1 hne ⟨hm₁.2, hm₂.2⟩
    have ha_le : Sa.card ≤ 1 := hcard (fun C => a ∈ (cs.compSt C).G.V) Sa
      (fun C₁ h₁ C₂ h₂ hne ⟨hA, hB⟩ => Finset.disjoint_left.mp (hI.hV_disj C₁ h₁ C₂ h₂ hne) hA hB)
    have hb_le : Sb.card ≤ 1 := hcard (fun C => b ∈ (cs.compSt C).G.V) Sb
      (fun C₁ h₁ C₂ h₂ hne ⟨hA, hB⟩ => Finset.disjoint_left.mp (hI.hV_disj C₁ h₁ C₂ h₂ hne) hA hB)
    have hsum : ∀ C ∈ components cs.G₀,
        (projCompUpdateG cs.G (cs.compSt C).G (.insert e a b)).length ≤
          2 * (if a ∈ (cs.compSt C).G.V then 1 else 0) + 2 * (if b ∈ (cs.compSt C).G.V then 1 else 0) :=
      fun C _ => by
        dsimp only [projCompUpdateG]
        by_cases ha : a ∈ (cs.compSt C).G.V <;> by_cases hb : b ∈ (cs.compSt C).G.V <;>
          simp [ha, hb]
    calc (components cs.G₀).sum (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.insert e a b)).length)
        ≤ (components cs.G₀).sum (fun C =>
            2 * (if a ∈ (cs.compSt C).G.V then 1 else 0) + 2 * (if b ∈ (cs.compSt C).G.V then 1 else 0)) :=
          Finset.sum_le_sum hsum
      _ = 2 * Sa.card + 2 * Sb.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp [Sa, Sb]
      _ ≤ 4 := by omega
  | split v v' St Sh =>
    have hcard : ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card ≤ 1 :=
      Finset.card_le_one.mpr fun C₁ h₁ C₂ h₂ => by
        by_contra hne
        have hm₁ := Finset.mem_filter.mp h₁
        have hm₂ := Finset.mem_filter.mp h₂
        exact Finset.disjoint_left.mp (hI.hV_disj C₁ hm₁.1 C₂ hm₂.1 hne) hm₁.2 hm₂.2
    calc (components cs.G₀).sum (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.split v v' St Sh)).length)
        = ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).sum (fun _ => 1) := by
          rw [← Finset.sum_filter_add_sum_filter_not (components cs.G₀) (fun C => v ∈ (cs.compSt C).G.V)]
          have h1 : ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).sum
              (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.split v v' St Sh)).length) =
              ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).sum (fun _ => 1) :=
            Finset.sum_congr rfl fun C hC => by simp [projCompUpdateG, (Finset.mem_filter.mp hC).2]
          have h2 : ((components cs.G₀).filter fun C => v ∉ (cs.compSt C).G.V).sum
              (fun C => (projCompUpdateG cs.G (cs.compSt C).G (.split v v' St Sh)).length) = 0 :=
            Finset.sum_eq_zero fun C hC => by simp [projCompUpdateG, (Finset.mem_filter.mp hC).2]
          omega
      _ = ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card := by simp
      _ ≤ 4 := le_trans hcard (by omega)

lemma sum_projCompBatchG_length_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {cs : CompLSFState},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ((components cs.G₀).sum fun C => (projCompBatchG cs.G (cs.compSt C).G U).length) ≤ 4 * U.length
  | [], cs, _, _ => by simp [projCompBatchG]
  | u :: rest, cs, hI, ⟨hu, hrest⟩ => by
    have h1 := compLSFInv_step hI hu
    set cs1 := compLSFStepSingle cs u
    have ih := sum_projCompBatchG_length_le rest h1 hrest
    have hG₁ : cs1.G₀ = cs.G₀ := rfl
    have hsum1 := sum_projCompUpdateG_length_le hI u
    have hlen : ∀ C ∈ components cs.G₀,
        (projCompBatchG cs.G (cs.compSt C).G (u :: rest)).length =
          (projCompUpdateG cs.G (cs.compSt C).G u).length +
            (projCompBatchG cs1.G (cs1.compSt C).G rest).length := by
      intro C hC
      have hBV1 := projCompUpdateG_valid hI hu hC
      have hG1C := applyLSFBatch_G_of_valid (hI.hCompLSF C hC).1 hBV1
      dsimp only [projCompBatchG]
      rw [List.length_append, show (cs.G.applyUpdate u) = cs1.G from rfl,
        show (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) = (cs1.compSt C).G
          from hG1C.symm]
    calc (components cs.G₀).sum (fun C => (projCompBatchG cs.G (cs.compSt C).G (u :: rest)).length)
        = (components cs.G₀).sum (fun C => (projCompUpdateG cs.G (cs.compSt C).G u).length) +
            (components cs1.G₀).sum (fun C => (projCompBatchG cs1.G (cs1.compSt C).G rest).length) := by
          rw [← hG₁, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl hlen
      _ ≤ 4 + 4 * rest.length := Nat.add_le_add hsum1 ih
      _ = 4 * (u :: rest).length := by simp [Nat.mul_succ]; omega

/-- Components touched by global batch `U`. -/
noncomputable def touchedCompsBatch (cs : CompLSFState) (U : List Update) : Finset (Finset ℕ) :=
  open Classical in (components cs.G₀).filter fun C =>
    projCompBatchG cs.G (cs.compSt C).G U ≠ []

lemma touchedComps_card_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (u : Update) :
    (touchedComps cs u).card ≤ 2 := by
  classical
  have hAtMostOneV : ∀ (v : ℕ), ((components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V).card ≤ 1 := by
    intro v
    rw [Finset.card_le_one]
    intro C₁ h1 C₂ h2
    by_contra hne
    exact Finset.disjoint_left.mp
      (hI.hV_disj C₁ (Finset.mem_filter.mp h1).1 C₂ (Finset.mem_filter.mp h2).1 hne)
      (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  cases u with
  | delete e =>
    have hs : touchedComps cs (.delete e) ⊆
        (components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E := by
      intro C hC
      obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
      refine Finset.mem_filter.mpr ⟨hCm, ?_⟩
      by_contra hnot; simp [projCompUpdateG, hnot] at hne
    exact le_trans (Finset.card_le_card hs) (hI.hEdge_atMostTwo e)
  | insert e a b =>
    have hs : touchedComps cs (.insert e a b) ⊆
        ((components cs.G₀).filter fun C => a ∈ (cs.compSt C).G.V) ∪
        ((components cs.G₀).filter fun C => b ∈ (cs.compSt C).G.V) := by
      intro C hC
      obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
      simp only [projCompUpdateG] at hne
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases ha : a ∈ (cs.compSt C).G.V
      · exact Or.inl ⟨hCm, ha⟩
      · by_cases hb : b ∈ (cs.compSt C).G.V
        · exact Or.inr ⟨hCm, hb⟩
        · simp [ha, hb] at hne
    have := le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
    have ha := hAtMostOneV a; have hb := hAtMostOneV b; omega
  | split v v' St Sh =>
    have hs : touchedComps cs (.split v v' St Sh) ⊆
        (components cs.G₀).filter fun C => v ∈ (cs.compSt C).G.V := by
      intro C hC
      obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
      refine Finset.mem_filter.mpr ⟨hCm, ?_⟩
      by_contra hnot; simp [projCompUpdateG, hnot] at hne
    exact le_trans (Finset.card_le_card hs) (by have := hAtMostOneV v; omega)

lemma touchedCompsBatch_card_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {cs : CompLSFState} {U : List Update},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      (touchedCompsBatch cs U).card ≤ 2 * U.length
  | cs, [], _, _ => by
    have hemp : touchedCompsBatch cs [] = ∅ := by
      ext C; simp [touchedCompsBatch, projCompBatchG]
    rw [hemp]; simp
  | cs, u :: rest, hI, ⟨hu, hrest⟩ => by
    classical
    have h1 := compLSFInv_step hI hu
    set cs1 := compLSFStepSingle cs u
    have hsub : touchedCompsBatch cs (u :: rest) ⊆ touchedComps cs u ∪ touchedCompsBatch cs1 rest := by
      intro C hC
      obtain ⟨hCm, hne⟩ := Finset.mem_filter.mp hC
      have hG1 := applyLSFBatch_G_of_valid (hI.hCompLSF C hCm).1 (projCompUpdateG_valid hI hu hCm)
      dsimp only [projCompBatchG] at hne
      rw [show cs.G.applyUpdate u = cs1.G from rfl,
        show (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) = (cs1.compSt C).G
          from hG1.symm] at hne
      simp only [Finset.mem_union, touchedComps, touchedCompsBatch, Finset.mem_filter]
      rw [ne_eq, List.append_eq_nil_iff, not_and_or] at hne
      exact hne.elim (fun h => Or.inl ⟨hCm, h⟩) (fun h => Or.inr ⟨hCm, h⟩)
    have hc1 := touchedComps_card_le hI u
    have hc2 := touchedCompsBatch_card_le h1 hrest
    have hu_le := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    simp only [List.length_cons]
    omega

/-- Single-update root-set growth in one component `C`: `0` if `C` is untouched, and at most
`56 * log²(n_C + 2)` if `C` is touched (even for a cross-insert `[.insert e a a, .delete e]`,
whose `.delete e` step adds zero roots). -/
lemma compLSF_compSt_R_step_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    (((compLSFStepSingle cs u).compSt C).R.card : ℝ) ≤ ((cs.compSt C).R.card : ℝ) +
      if C ∈ touchedComps cs u then 56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 else 0 := by
  classical
  have hCI := (hI.hCompLSF C hC).1
  have hG0C := (hI.hCompLSF C hC).2.1
  by_cases ht : C ∈ touchedComps cs u
  · rw [ite_eq_left ht]
    change ((applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u)).R.card : ℝ) ≤ _
    cases u with
    | delete e =>
      dsimp only [projCompUpdateG]
      split_ifs with he
      · have hB := (applyLSFUpdate_inv_with (u := .delete e) hCI he).2.2.2.2.2.2.2.2.2.2
        simpa [applyLSFBatch, hG0C] using hB
      · have hnn : (0 : ℝ) ≤ 56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 := by positivity
        simp only [applyLSFBatch, List.foldl_nil]; linarith
    | insert e a b =>
      dsimp only [projCompUpdateG]
      have hne : e ∉ (cs.compSt C).G.E := fun h => hu.1 (hI.hCE_sub C hC h)
      split_ifs with h1 h2 h3
      · have hB := (applyLSFUpdate_inv_with (u := .insert e a b) hCI ⟨hne, h1.1, h1.2⟩).2.2.2.2.2.2.2.2.2.2
        simpa [applyLSFBatch, hG0C] using hB
      · rw [(applyLSFBatch_insert_delete_selfLoop hCI hne h2).2.2.2.2.2.2]
        have hB := (applyLSFUpdate_inv_with (u := .insert e a a) hCI ⟨hne, h2, h2⟩).2.2.2.2.2.2.2.2.2.2
        simpa [hG0C] using hB
      · rw [(applyLSFBatch_insert_delete_selfLoop hCI hne h3).2.2.2.2.2.2]
        have hB := (applyLSFUpdate_inv_with (u := .insert e b b) hCI ⟨hne, h3, h3⟩).2.2.2.2.2.2.2.2.2.2
        simpa [hG0C] using hB
      · have hnn : (0 : ℝ) ≤ 56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 := by positivity
        simp only [applyLSFBatch, List.foldl_nil]; linarith
    | split v v' St Sh =>
      have hBV := projCompUpdateG_valid hI hu hC
      dsimp only [projCompUpdateG] at hBV ⊢
      split_ifs at hBV ⊢ with hv
      · have hB := (applyLSFUpdate_inv_with hCI hBV.1).2.2.2.2.2.2.2.2.2.2
        simpa [applyLSFBatch, hG0C] using hB
      · have hnn : (0 : ℝ) ≤ 56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 := by positivity
        simp only [applyLSFBatch, List.foldl_nil]; linarith
  · rw [ite_eq_right ht]
    have hnil : projCompUpdateG cs.G (cs.compSt C).G u = [] := by
      by_contra hne; exact ht (Finset.mem_filter.mpr ⟨hC, hne⟩)
    change ((applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u)).R.card : ℝ) ≤ _
    rw [hnil]; simp [applyLSFBatch]

/-- Batch root-set growth in one component `C`: at most `56 * U.length * log²(n_C + 2)`. -/
lemma compLSFBatch_compSt_R_le_compN {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {cs : CompLSFState} {U : List Update},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ∀ {C : Finset ℕ}, C ∈ components cs.G₀ →
      (((compLSFBatch cs U).compSt C).R.card : ℝ) ≤ ((cs.compSt C).R.card : ℝ) +
        56 * (U.length : ℝ) * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2
  | cs, [], _, _, C, _ => by simp [compLSFBatch]
  | cs, u :: rest, hI, ⟨hu, hrest⟩, C, hC => by
    have h1 := compLSF_compSt_R_step_le hI hu hC
    have hI1 := compLSFInv_step hI hu
    have ih := compLSFBatch_compSt_R_le_compN hI1 hrest hC
    change (((compLSFBatch (compLSFStepSingle cs u) rest).compSt C).R.card : ℝ) ≤
      (((compLSFStepSingle cs u).compSt C).R.card : ℝ) +
        56 * (rest.length : ℝ) * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 at ih
    have hnn : (0 : ℝ) ≤ 56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 := by positivity
    have hstep1 : (((compLSFStepSingle cs u).compSt C).R.card : ℝ) ≤ ((cs.compSt C).R.card : ℝ) +
        56 * (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 := by
      split_ifs at h1 <;> linarith
    change (((compLSFBatch (compLSFStepSingle cs u) rest).compSt C).R.card : ℝ) ≤ _
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

lemma compLSFBatch_untouched {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) (hnt : C ∉ touchedCompsBatch cs U) :
    projCompBatchG cs.G (cs.compSt C).G U = [] ∧ (compLSFBatch cs U).compSt C = cs.compSt C := by
  have hnil : projCompBatchG cs.G (cs.compSt C).G U = [] := by
    by_contra hne
    exact hnt (Finset.mem_filter.mpr ⟨hC, hne⟩)
  have hcs := (compLSFBatch_compSt hI hU hC).1
  rw [hnil, applyLSFBatch] at hcs
  exact ⟨hnil, hcs⟩

lemma compLSF_R_sum_le_min {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ {cs : CompLSFState} {U : List Update},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      ((compLSFBatch cs U).RF.R.card : ℝ) ≤ (cs.RF.R.card : ℝ) +
        56 * ((2 * U.length : ℕ) : ℝ) *
          (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2
  | cs, [], _, _ => by simp [compLSFBatch]
  | cs, u :: rest, hI, ⟨hu, hrest⟩ => by
    classical
    have hdisj_R : ∀ (st : CompLSFState), CompLSFInv C_lsst ℓ₀ st →
        (st.RF.R.card : ℝ) = (((components st.G₀).sum fun C => (st.compSt C).R.card : ℕ) : ℝ) := by
      intro st hIst
      congr 1
      change ((components st.G₀).biUnion fun C => (st.compSt C).R).card = _
      rw [Finset.card_biUnion]
      intro C₁ hC₁ C₂ hC₂ hne
      exact (hIst.hV_disj C₁ hC₁ C₂ hC₂ hne).mono
        (lsfInv_R_sub_V (hIst.hCompLSF C₁ hC₁).1) (lsfInv_R_sub_V (hIst.hCompLSF C₂ hC₂).1)
    have hI1 := compLSFInv_step hI hu
    set cs1 := compLSFStepSingle cs u
    have hstep_R : (cs1.RF.R.card : ℝ) ≤ (cs.RF.R.card : ℝ) +
        56 * (2 : ℝ) * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
      rw [hdisj_R cs1 hI1, hdisj_R cs hI]
      have hG01 : cs1.G₀ = cs.G₀ := rfl
      rw [hG01]
      have hC_le : ∀ C ∈ components cs.G₀,
          ((cs1.compSt C).R.card : ℝ) ≤ ((cs.compSt C).R.card : ℝ) +
            if C ∈ touchedComps cs u then
              56 * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2
            else 0 := fun C hC => by
        have hstepC := compLSF_compSt_R_step_le hI hu hC
        split_ifs at hstepC ⊢
        · have hnC_le : (compGraph cs.G₀ C).n ≤ min cs.G₀.n (cs.G₀.m + 1) :=
            compGraph_n_le_min hI.hG₀_val hC
          have hlogC : Real.log (((compGraph cs.G₀ C).n : ℝ) + 2) ≤
              Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2) := by
            refine Real.log_le_log (by positivity) ?_
            have : ((compGraph cs.G₀ C).n : ℝ) ≤ ((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) := by
              exact_mod_cast hnC_le
            linarith
          have hlogC_nn : 0 ≤ Real.log (((compGraph cs.G₀ C).n : ℝ) + 2) := by
            linarith [half_lt_log_add_two (compGraph cs.G₀ C).n]
          have hsq := pow_le_pow_left₀ hlogC_nn hlogC 2
          linarith
        · exact hstepC
      have hsum : (((components cs.G₀).sum fun C => (cs1.compSt C).R.card : ℕ) : ℝ) ≤
          (components cs.G₀).sum (fun C => ((cs.compSt C).R.card : ℝ) +
            if C ∈ touchedComps cs u then
              56 * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2
            else 0) := by
        rw [Nat.cast_sum]; exact Finset.sum_le_sum hC_le
      rw [Finset.sum_add_distrib] at hsum
      have hpush : ((components cs.G₀).sum fun C => ((cs.compSt C).R.card : ℝ)) =
          (((components cs.G₀).sum fun C => (cs.compSt C).R.card : ℕ) : ℝ) := by push_cast; rfl
      have ht_sum : ((components cs.G₀).sum fun C =>
            if C ∈ touchedComps cs u then
              56 * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2
            else 0) =
          ((touchedComps cs u).card : ℝ) *
            (56 * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2) := by
        rw [← Finset.sum_filter]
        have hfeq : (components cs.G₀).filter (fun C => C ∈ touchedComps cs u) = touchedComps cs u :=
          Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
        rw [hfeq, Finset.sum_const, nsmul_eq_mul]
      have htc_real : ((touchedComps cs u).card : ℝ) ≤ 2 := by exact_mod_cast touchedComps_card_le hI u
      have hlog2_nn : 0 ≤ 56 * (Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by positivity
      rw [hpush, ht_sum] at hsum
      nlinarith
    have ih := compLSF_R_sum_le_min hI1 hrest
    have hG01 : cs1.G₀ = cs.G₀ := rfl
    change ((compLSFBatch cs1 rest).RF.R.card : ℝ) ≤ _
    rw [hG01] at ih
    have hlen : ((2 * (u :: rest).length : ℕ) : ℝ) = 2 + ((2 * rest.length : ℕ) : ℝ) := by
      simp only [List.length_cons]; push_cast; ring
    rw [hlen]
    linarith

lemma compLSF_R_sum_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    ((compLSFBatch cs U).RF.R.card : ℝ) ≤ (cs.RF.R.card : ℝ) +
      56 * ((2 * U.length : ℕ) : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
  have hmin := compLSF_R_sum_le_min hI hU
  have hlog_nn : 0 ≤ Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2) := by
    linarith [half_lt_log_add_two (min cs.G₀.n (cs.G₀.m + 1))]
  have hlog_le : Real.log (((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) + 2) ≤
      Real.log ((cs.G₀.n : ℝ) + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have : ((min cs.G₀.n (cs.G₀.m + 1) : ℕ) : ℝ) ≤ cs.G₀.n := by exact_mod_cast min_le_left _ _
    linarith
  have hsq := pow_le_pow_left₀ hlog_nn hlog_le 2
  have hc : 0 ≤ 56 * ((2 * U.length : ℕ) : ℝ) := by positivity
  exact le_trans hmin (by linarith [mul_le_mul_of_nonneg_left hsq hc])

lemma compLSF_connected_R_card_le_with {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hconn : ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k)
    {U : List Update} (hU : G₀.BatchIsValid U) :
    let cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j
    let cs := compLSFBatch cs₀ U
    (cs.RF.R.card : ℝ) ≤ 1 + 4 * (G₀.m : ℝ) / (k : ℝ) +
      112 * (U.length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
  intro cs₀ cs
  have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hr := compLSF_R_sum_le hI₀ hU
  have hcc := connected_components_eq hG₀ hV₀ hconn
  have hR₀ : (cs₀.RF.R.card : ℝ) ≤ 1 + 4 * (G₀.m : ℝ) / (k : ℝ) := by
    set ℓs := safeLen G₀ ℓ₀
    have hℓs : ∀ e ∈ G₀.E, 0 < ℓs e := fun e he => by
      rw [show ℓs e = ℓ₀ e from safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hr_set : cs₀.RF.R = (lsfInit G₀ ℓs k j).R := by
      change (components G₀).biUnion (fun C => (cs₀.compSt C).R) = _
      rw [hcc.1]
      simp only [Finset.singleton_biUnion]
      change (lsfInit (compGraph G₀ G₀.V) ℓs k j).R = _
      rw [hcc.2]
    rw [hr_set]
    have hR := (hInit G₀ ℓs hG₀ hV₀ hℓs hk).2.2.2.2.2.2.2.1
    split_ifs at hR
    exact hR
  have hcs₀_G₀ : cs₀.G₀.n = G₀.n := rfl
  have h2U : ((2 * U.length : ℕ) : ℝ) = 2 * (U.length : ℝ) := by push_cast; ring
  change (cs.RF.R.card : ℝ) ≤ (cs₀.RF.R.card : ℝ) +
    56 * ((2 * U.length : ℕ) : ℝ) * (Real.log ((cs₀.G₀.n : ℝ) + 2)) ^ 2 at hr
  rw [h2U, hcs₀_G₀] at hr
  linarith

lemma compLSF_connected_R_card_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hconn : ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    {U : List Update} (hU : G₀.BatchIsValid U) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let cs := compLSFBatch cs₀ U
    (cs.RF.R.card : ℝ) ≤ 1 + 4 * (G₀.m : ℝ) / (k : ℝ) +
      112 * (U.length : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 :=
  compLSF_connected_R_card_le_with (initLSFOnline_isValidLSFInitFor hLSST k j) hG₀ hV₀ hconn hℓ₀ hk hU

theorem compLSF_mwu_bound
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (k : ℕ) (hk : 1 ≤ k) (U : List Update) (hU : G₀.BatchIsValid U) :
    let K := 26 * mwuK0 C_lsst + 128
    let cs := fun j => compLSFBatch (initCompLSF oracle C_lsst G₀ ℓ₀ k j) U
    ∀ e ∈ (G₀.applyBatch U).E,
      ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) := by
  intro K cs e he
  classical
  have hI0 := fun j => compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hsp0 := fun j => compLSFBatch_step_props U (hI0 j) hU
  have he_0 : e ∈ (cs 0).G.E := by rwa [compLSFBatch_G]
  have hK₀ : 0 < mwuK0 C_lsst := mwuK0_pos C_lsst
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hn₀_pos : 1 ≤ G₀.n := Finset.card_pos.mpr hV₀
  have hlog3 : (1 : ℝ) ≤ Real.log ((G₀.n : ℝ) + 2) := by
    refine le_trans log_three_ge_one (Real.log_le_log (by norm_num) ?_)
    have : (1 : ℝ) ≤ G₀.n := by exact_mod_cast hn₀_pos
    linarith
  have hlog6 : (1 : ℝ) ≤ (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := one_le_pow₀ hlog3
  have hlogm : (1 / 2 : ℝ) < Real.log ((G₀.m : ℝ) + 2) := half_lt_log_add_two G₀.m
  by_cases heI : e ∈ (cs 0).insertedGlobal
  · have heIj : ∀ j, e ∈ (cs j).insertedGlobal := fun j => by
      have h0 : (cs 0).insertedGlobal = U.foldl updateInserted ∅ :=
        compLSFBatch_insertedGlobal _ U
      have hj : (cs j).insertedGlobal = U.foldl updateInserted ∅ :=
        compLSFBatch_insertedGlobal _ U
      rwa [hj, ← h0]
    have hw1 : ∀ j ∈ Finset.range k, (cs j).wstrGlobal e = 1 := fun j _ =>
      ((hsp0 j).1.hIns_wstr_R e (heIj j)).1
    have hsum1 : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e = 1 := by
      calc ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e
          = ∑ _ ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) :=
            Finset.sum_congr rfl fun j hj => by rw [hw1 j hj, mul_one]
        _ = (k : ℝ) * ((1 : ℝ) / (k : ℝ)) := by simp
        _ = 1 := mul_one_div_cancel hk_pos.ne'
    rw [hsum1]
    have hK_ge : 128 ≤ K := by dsimp [K]; linarith
    have hK_log6 : 128 ≤ K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := by nlinarith
    nlinarith
  · obtain ⟨C, hC_G0, heC0, hniC0, _⟩ := (hsp0 0).1.hWstr_surv e he_0 heI
    have hC : C ∈ components G₀ := by
      rwa [compLSFBatch_G₀ (initCompLSF oracle C_lsst G₀ ℓ₀ k 0) U] at hC_G0
    have hCG₀ : e ∈ (compGraph G₀ C).E := by
      have hs := ((hsp0 0).1.hCompLSF C hC_G0).1.hsurv_edge e heC0 hniC0 |>.1
      rwa [((hsp0 0).1.hCompLSF C hC_G0).2.1, compLSFBatch_G₀] at hs
    set U_C := projCompBatchG G₀ (compGraph G₀ C) U
    have hGC_val := compGraph_isValid hG₀ hC
    have hGC_ne := compGraph_nonempty hC
    set ℓs := safeLen G₀ ℓ₀
    have hℓC : ∀ f ∈ (compGraph G₀ C).E, 0 < ℓs f := fun f hf => by
      have hfG : f ∈ G₀.E := Finset.filter_subset _ _ hf
      rw [show ℓs f = ℓ₀ f from safeLen_eq_of_mem ℓ₀ hfG]
      exact hℓ₀ f hfG
    have hw_eq : ∀ j, (cs j).wstrGlobal e =
        (applyLSFBatches (initLSFOnline oracle C_lsst (compGraph G₀ C) ℓs k j) [U_C]).wstr e := by
      intro j
      have heIj : e ∉ (cs j).insertedGlobal := by
        have h0 : (cs 0).insertedGlobal = U.foldl updateInserted ∅ :=
          compLSFBatch_insertedGlobal _ U
        have hj : (cs j).insertedGlobal = U.foldl updateInserted ∅ :=
          compLSFBatch_insertedGlobal _ U
        rwa [hj, ← h0]
      have he_j : e ∈ (cs j).G.E := by rwa [compLSFBatch_G]
      obtain ⟨Cj, hCj_G0, heCj, hniCj, hwCj⟩ := (hsp0 j).1.hWstr_surv e he_j heIj
      have hCj : Cj ∈ components G₀ := by
        rwa [compLSFBatch_G₀ (initCompLSF oracle C_lsst G₀ ℓ₀ k j) U] at hCj_G0
      have heGCj : e ∈ compEdgeSet G₀ Cj := by
        have hs := ((hsp0 j).1.hCompLSF Cj hCj_G0).1.hsurv_edge e heCj hniCj |>.1
        rwa [((hsp0 j).1.hCompLSF Cj hCj_G0).2.1, compLSFBatch_G₀] at hs
      have hCeq : Cj = C := by
        by_contra hne
        exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hCj hC hne) heGCj hCG₀
      subst hCeq
      have hcomp := (compLSFBatch_compSt (hI0 j) hU hC).1
      rw [hwCj, hcomp]
      rfl
    have hBU_C : (compGraph G₀ C).BatchIsValid U_C :=
      (compLSFBatch_compSt (hI0 0) hU hC).2.2.1
    have he_UC : e ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E := by
      rw [List.foldl_cons, List.foldl_nil]
      have hGeq := (compLSFBatch_compSt (hI0 0) hU hC).2.1
      change e ∈ ((cs 0).compSt C).G.E at heC0
      rw [hGeq] at heC0
      exact heC0
    let ℓ_C : ℕ → ℝ := fun f =>
      if f ∈ (compGraph G₀ C).E ∧ f ∉ batchesInserted [U_C] then ℓs f else 1
    have hℓ_pos : ∀ f ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E, 0 < ℓ_C f :=
      fun f _ => by dsimp only [ℓ_C]; split_ifs with hf; exact hℓC f hf.1; exact zero_lt_one
    have hℓ_orig : ∀ f ∈ (compGraph G₀ C).E, f ∈ ([U_C].foldl MGraph.applyBatch (compGraph G₀ C)).E →
        f ∉ batchesInserted [U_C] → ℓ_C f = ℓs f :=
      fun f hf _ hni => by simp [ℓ_C, hf, hni]
    have hmwu := (lemma_5_5_online oracle C_lsst hLSST (compGraph G₀ C) hGC_val hGC_ne
      ℓs hℓC k hk [U_C] ⟨hBU_C, trivial⟩ ℓ_C hℓ_pos hℓ_orig).2 e he_UC
    have hnC_le : (compGraph G₀ C).n ≤ G₀.n := compGraph_n_le hC
    have hmC_le : (compGraph G₀ C).m ≤ G₀.m := compGraph_m_le
    have hlogC : Real.log (((compGraph G₀ C).n : ℝ) + 2) ≤ Real.log ((G₀.n : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph G₀ C).n : ℝ) ≤ G₀.n := by exact_mod_cast hnC_le
      linarith
    have hlogC_nn : 0 ≤ Real.log (((compGraph G₀ C).n : ℝ) + 2) := by
      linarith [half_lt_log_add_two (compGraph G₀ C).n]
    have hlogCm : Real.log (((compGraph G₀ C).m : ℝ) + 2) ≤ Real.log ((G₀.m : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph G₀ C).m : ℝ) ≤ G₀.m := by exact_mod_cast hmC_le
      linarith
    have hlogCm_nn : 0 ≤ Real.log (((compGraph G₀ C).m : ℝ) + 2) := by
      linarith [half_lt_log_add_two (compGraph G₀ C).m]
    have hK_nn : 0 ≤ K := by dsimp [K]; positivity
    have hpow6 := pow_le_pow_left₀ hlogC_nn hlogC 6
    have hmono : K * (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 6 *
          Real.log (((compGraph G₀ C).m : ℝ) + 2) ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow6 hK_nn) hlogCm hlogCm_nn (by positivity)
    calc ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs j).wstrGlobal e
        = ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) *
            (applyLSFBatches (initLSFOnline oracle C_lsst (compGraph G₀ C) ℓs k j) [U_C]).wstr e :=
          Finset.sum_congr rfl fun j _ => by rw [hw_eq j]
      _ ≤ K * (Real.log (((compGraph G₀ C).n : ℝ) + 2)) ^ 6 *
            Real.log (((compGraph G₀ C).m : ℝ) + 2) := hmwu
      _ ≤ K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.m : ℝ) + 2) := hmono

end

end MinCostFlow.SparseCore
