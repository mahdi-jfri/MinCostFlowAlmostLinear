module

public import MinCostFlow.ExpanderDecomp.OuterProgRecLabels
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `OuterRecSpec` Combination and Witness `RemoveFake` Lemmas (`OuterProgRecCombine`)

Proves the pure `OuterRecSpec` base, cut-combination, and witness-combination lemmas together with
the pre- and post-`RemoveFake` bridges (`outerWitness_pre_removeFake`, `outerWitness_post_removeFake`).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 7. Public `OuterRecSpec` Combination and Arbitrary-`RemoveFake` Lemmas -/

/-- Base-case `OuterRecSpec` for `H.edges.length ≤ QOut cfg M r`. -/
lemma progRecSpec_base {cfg : ParamConfig} {M r : ℕ} {G : Graph} {H : CompactSubgraph}
    (hRep : H.Represents G H.vertSet) (hQ : H.edges.length ≤ QOut cfg M r) :
    OuterRecSpec cfg M r G H
      { parts := H.componentsOf
        depth := if H.edges.length = 0 then 0 else 1
        edgeSum := H.edges.length
        witnessEdgeSum := 0 } := by
  have hQ1 : 1 ≤ QOut cfg M r := by unfold QOut; omega
  obtain ⟨_, hne_sub, hpw, hunion, hexp, _⟩ := H.componentsOf_spec hRep hQ1 hQ
  dsimp only [OuterRecSpec]
  refine ⟨hne_sub, hpw, hunion, hexp, ?_, ?_, 0, 0, 0, ?_, by simp, by omega, by omega, by omega⟩
  · intro hd
    by_cases h0 : H.edges.length = 0
    · simp [h0] at hd
    · simp [h0]; omega
  · by_cases h0 : H.edges.length = 0
    · simp [h0]
    · simp [h0]
  · have hc0 := crossingCount_components_eq_zero hRep hQ1 hQ; omega

/-- Cut-branch `OuterRecSpec` combination lemma. -/
lemma progRecSpec_cut_combine {cfg : ParamConfig} {M r : ℕ} {G : Graph}
    {H act₁ act₂ : CompactSubgraph} {S : Finset ℕ} {iso₁ iso₂ : List ℕ} {o₁ o₂ : OuterRecOut}
    (hRep : H.Represents G H.vertSet) (hSX : S ⊆ H.vertSet) (he_pos : 1 ≤ H.edges.length)
    (hiso1_nd : iso₁.Nodup) (hdisj1 : Disjoint iso₁.toFinset act₁.vertSet)
    (hunion1 : iso₁.toFinset ∪ act₁.vertSet = S)
    (hact1_rep : act₁.Represents G act₁.vertSet) (he1_in : act₁.edges = G.inside S)
    (hiso2_nd : iso₂.Nodup) (hdisj2 : Disjoint iso₂.toFinset act₂.vertSet)
    (hunion2 : iso₂.toFinset ∪ act₂.vertSet = H.vertSet \ S)
    (hact2_rep : act₂.Represents G act₂.vertSet) (he2_in : act₂.edges = G.inside (H.vertSet \ S))
    (h32 : bOut cfg M * G.cutIn H.vertSet S ≤
      cfg.kappa * min (G.volIn H.vertSet S) (G.volIn H.vertSet (H.vertSet \ S)))
    (hsh1 : 16 * DOut cfg M r * act₁.edges.length ≤ (16 * DOut cfg M r - 1) * H.edges.length)
    (hsh2 : 16 * DOut cfg M r * act₂.edges.length ≤ (16 * DOut cfg M r - 1) * H.edges.length)
    (ho₁ : OuterRecSpec cfg M r G act₁ o₁) (ho₂ : OuterRecSpec cfg M r G act₂ o₂) :
    OuterRecSpec cfg M r G H
      { parts :=
          ((iso₁.map fun v => ({v} : Finset ℕ)) ++ o₁.parts) ++
            ((iso₂.map fun v => ({v} : Finset ℕ)) ++ o₂.parts)
        depth := 1 + max o₁.depth o₂.depth
        edgeSum := H.edges.length + o₁.edgeSum + o₂.edgeSum
        witnessEdgeSum := o₁.witnessEdgeSum + o₂.witnessEdgeSum } := by
  obtain ⟨hp1_ne, hp1_pw, hp1_u, hp1_exp, hd1, hes1, cC1, cW1, wR1, hcr1, hpot1, hwR1, hw15_1, hw16_1⟩ := ho₁
  obtain ⟨hp2_ne, hp2_pw, hp2_u, hp2_exp, hd2, hes2, cC2, cW2, wR2, hcr2, hpot2, hwR2, hw15_2, hw16_2⟩ := ho₂
  obtain ⟨hi1_ne, hi1_pw, hi1_u, hi1_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg M r : ℝ)) hiso1_nd
  obtain ⟨hi2_ne, hi2_pw, hi2_u, hi2_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg M r : ℝ)) hiso2_nd
  have hiso1_sub : iso₁.toFinset ⊆ S := by rw [← hunion1]; exact Finset.subset_union_left
  have hact1_sub : act₁.vertSet ⊆ S := by rw [← hunion1]; exact Finset.subset_union_right
  have hiso2_sub : iso₂.toFinset ⊆ H.vertSet \ S := by rw [← hunion2]; exact Finset.subset_union_left
  have hact2_sub : act₂.vertSet ⊆ H.vertSet \ S := by rw [← hunion2]; exact Finset.subset_union_right
  have hdisjST : Disjoint S (H.vertSet \ S) := disjoint_sdiff_self_right
  let l1 := (iso₁.map fun v => ({v} : Finset ℕ)) ++ o₁.parts
  let l2 := (iso₂.map fun v => ({v} : Finset ℕ)) ++ o₂.parts
  have hu1 : l1.toFinset.biUnion id = S := by rw [biUnion_append, hi1_u, hp1_u]; exact hunion1
  have hu2 : l2.toFinset.biUnion id = H.vertSet \ S := by rw [biUnion_append, hi2_u, hp2_u]; exact hunion2
  have hpw1 : l1.Pairwise Disjoint :=
    pairwise_disjoint_append hi1_pw hp1_pw (by rw [hi1_u, hp1_u]; exact hdisj1)
  have hpw2 : l2.Pairwise Disjoint :=
    pairwise_disjoint_append hi2_pw hp2_pw (by rw [hi2_u, hp2_u]; exact hdisj2)
  have hpw_all : (l1 ++ l2).Pairwise Disjoint :=
    pairwise_disjoint_append hpw1 hpw2 (by rw [hu1, hu2]; exact hdisjST)
  have hunion_all : (l1 ++ l2).toFinset.biUnion id = H.vertSet := by
    rw [biUnion_append, hu1, hu2]; exact Finset.union_sdiff_of_subset hSX
  have hne_all : ∀ P ∈ l1 ++ l2, P.Nonempty ∧ P ⊆ H.vertSet := by
    intro P hP; simp only [l1, l2, List.mem_append] at hP
    rcases hP with (h | h) | (h | h)
    · exact ⟨(hi1_ne P h).1, (hi1_ne P h).2.trans (hiso1_sub.trans hSX)⟩
    · exact ⟨(hp1_ne P h).1, (hp1_ne P h).2.trans (hact1_sub.trans hSX)⟩
    · exact ⟨(hi2_ne P h).1, (hi2_ne P h).2.trans (hiso2_sub.trans Finset.sdiff_subset)⟩
    · exact ⟨(hp2_ne P h).1, (hp2_ne P h).2.trans (hact2_sub.trans Finset.sdiff_subset)⟩
  have hexp_all : ∀ P ∈ l1 ++ l2, G.IsConductanceExpanderOn P (1 / (QOut cfg M r : ℝ)) := by
    intro P hP; simp only [l1, l2, List.mem_append] at hP
    rcases hP with (h | h) | (h | h)
    · exact hi1_exp P h
    · exact hp1_exp P h
    · exact hi2_exp P h
    · exact hp2_exp P h
  have hdepth_all : 1 ≤ 1 + max o₁.depth o₂.depth →
      (16 * DOut cfg M r) ^ (1 + max o₁.depth o₂.depth - 1) ≤
      (16 * DOut cfg M r - 1) ^ (1 + max o₁.depth o₂.depth - 1) * H.edges.length := by
    intro _; rw [Nat.add_sub_cancel_left]
    rcases le_total o₁.depth o₂.depth with hm | hm
    · rw [max_eq_right hm]; exact pow_le_of_step hsh2 he_pos hd2
    · rw [max_eq_left hm]; exact pow_le_of_step hsh1 he_pos hd1
  have he_eq : (G.inside H.vertSet).length = H.edges.length := congrArg List.length hRep.2.2.symm
  have he1_eq : act₁.edges.length = (G.inside S).length := congrArg List.length he1_in
  have he2_eq : act₂.edges.length = (G.inside (H.vertSet \ S)).length := congrArg List.length he2_in
  have hsplit := inside_length_split G hSX
  have hesum_all : H.edges.length + o₁.edgeSum + o₂.edgeSum ≤
      (1 + max o₁.depth o₂.depth) * H.edges.length := by
    set m := max o₁.depth o₂.depth
    have h1 : o₁.edgeSum ≤ m * act₁.edges.length := le_trans hes1 (Nat.mul_le_mul_right _ (le_max_left _ _))
    have h2 : o₂.edgeSum ≤ m * act₂.edges.length := le_trans hes2 (Nat.mul_le_mul_right _ (le_max_right _ _))
    calc H.edges.length + o₁.edgeSum + o₂.edgeSum
        ≤ H.edges.length + m * act₁.edges.length + m * act₂.edges.length := by omega
      _ = H.edges.length + m * (act₁.edges.length + act₂.edges.length) := by ring
      _ ≤ H.edges.length + m * H.edges.length := Nat.add_le_add_left (Nat.mul_le_mul_left m (by omega)) _
      _ = (1 + m) * H.edges.length := by ring
  dsimp only [OuterRecSpec]
  refine ⟨hne_all, hpw_all, hunion_all, hexp_all, hdepth_all, hesum_all,
    G.cutIn H.vertSet S + cC1 + cC2, cW1 + cW2, wR1 + wR2, ?_, ?_, by omega, by omega, ?_⟩
  · have hcr_split := crossingCount_split_cut G hSX
      (parts := l1 ++ l2) (p₁ := o₁.parts) (p₂ := o₂.parts)
      (fun P hP => by simp [l1, hP]) (fun P hP => by simp [l2, hP])
    have hins1 : G.inside S = G.inside act₁.vertSet := he1_in.symm.trans hact1_rep.2.2
    have hins2 : G.inside (H.vertSet \ S) = G.inside act₂.vertSet := he2_in.symm.trans hact2_rep.2.2
    rw [crossingCount_congr_inside hins1, crossingCount_congr_inside hins2] at hcr_split
    dsimp only [l1, l2] at hcr_split
    omega
  · have hstep := cutPotential_step G hSX (b := bOut cfg M) (κ := cfg.kappa) h32
    rw [he_eq, ← he1_eq, ← he2_eq] at hstep
    have hdist : bOut cfg M * (G.cutIn H.vertSet S + cC1 + cC2) =
        bOut cfg M * G.cutIn H.vertSet S + bOut cfg M * cC1 + bOut cfg M * cC2 := by ring
    omega
  · have hdist : 16 * bOut cfg M * (cW1 + cW2) =
        16 * bOut cfg M * cW1 + 16 * bOut cfg M * cW2 := by ring
    omega

/-- Witness-branch `OuterRecSpec` combination lemma (works for ANY `R` returned by
`removeFakeContract`). -/
lemma progRecSpec_witness_combine {cfg : ParamConfig} {M r : ℕ} {G : Graph}
    {H actRest : CompactSubgraph} {R : Finset ℕ} {isoRest : List ℕ} {oRest : OuterRecOut}
    (hRep : H.Represents G H.vertSet) (hRX : R ⊆ H.vertSet) (hRne : R.Nonempty)
    (he_pos : 1 ≤ H.edges.length)
    (hRcond : G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)))
    (hiso_nd : isoRest.Nodup) (hdisjR_iso : Disjoint isoRest.toFinset actRest.vertSet)
    (hunionR : isoRest.toFinset ∪ actRest.vertSet = H.vertSet \ R)
    (hactR_rep : actRest.Represents G actRest.vertSet)
    (heR_in : actRest.edges = G.inside (H.vertSet \ R))
    (hshR : 16 * DOut cfg M r * actRest.edges.length ≤ (16 * DOut cfg M r - 1) * H.edges.length)
    (hltR : actRest.edges.length < H.edges.length)
    (hretR : 15 * H.edges.length ≤ 16 * (G.inside R).length)
    (hcutR : 16 * bOut cfg M * G.cutIn H.vertSet R ≤ H.edges.length)
    (hoR : OuterRecSpec cfg M r G actRest oRest) :
    OuterRecSpec cfg M r G H
      { parts := [R] ++ ((isoRest.map fun v => ({v} : Finset ℕ)) ++ oRest.parts)
        depth := 1 + oRest.depth
        edgeSum := H.edges.length + oRest.edgeSum
        witnessEdgeSum := H.edges.length + oRest.witnessEdgeSum } := by
  obtain ⟨hpR_ne, hpR_pw, hpR_u, hpR_exp, hdR, hesR, cCR, cWR, wRR, hcrR, hpotR, hwRR, hw15R, hw16R⟩ := hoR
  obtain ⟨hiR_ne, hiR_pw, hiR_u, hiR_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg M r : ℝ)) hiso_nd
  have hisoR_sub : isoRest.toFinset ⊆ H.vertSet \ R := by rw [← hunionR]; exact Finset.subset_union_left
  have hactR_sub : actRest.vertSet ⊆ H.vertSet \ R := by rw [← hunionR]; exact Finset.subset_union_right
  have hdisjR : Disjoint R (H.vertSet \ R) := disjoint_sdiff_self_right
  let lRest := (isoRest.map fun v => ({v} : Finset ℕ)) ++ oRest.parts
  have hRbi : ([R] : List (Finset ℕ)).toFinset.biUnion id = R := by ext v; simp
  have huRest : lRest.toFinset.biUnion id = H.vertSet \ R := by rw [biUnion_append, hiR_u, hpR_u]; exact hunionR
  have hpwRest : lRest.Pairwise Disjoint :=
    pairwise_disjoint_append hiR_pw hpR_pw (by rw [hiR_u, hpR_u]; exact hdisjR_iso)
  have hpw_all : ([R] ++ lRest).Pairwise Disjoint :=
    pairwise_disjoint_append (List.pairwise_singleton _ _) hpwRest (by rw [hRbi, huRest]; exact hdisjR)
  have hunion_all : ([R] ++ lRest).toFinset.biUnion id = H.vertSet := by
    rw [biUnion_append, hRbi, huRest]; exact Finset.union_sdiff_of_subset hRX
  have hne_all : ∀ P ∈ [R] ++ lRest, P.Nonempty ∧ P ⊆ H.vertSet := by
    intro P hP; simp only [lRest, List.mem_append, List.mem_singleton] at hP
    rcases hP with rfl | h | h
    · exact ⟨hRne, hRX⟩
    · exact ⟨(hiR_ne P h).1, (hiR_ne P h).2.trans (hisoR_sub.trans Finset.sdiff_subset)⟩
    · exact ⟨(hpR_ne P h).1, (hpR_ne P h).2.trans (hactR_sub.trans Finset.sdiff_subset)⟩
  have hexp_all : ∀ P ∈ [R] ++ lRest, G.IsConductanceExpanderOn P (1 / (QOut cfg M r : ℝ)) := by
    intro P hP; simp only [lRest, List.mem_append, List.mem_singleton] at hP
    rcases hP with rfl | h | h
    · exact hRcond
    · exact hiR_exp P h
    · exact hpR_exp P h
  have hdepth_all : 1 ≤ 1 + oRest.depth →
      (16 * DOut cfg M r) ^ (1 + oRest.depth - 1) ≤
      (16 * DOut cfg M r - 1) ^ (1 + oRest.depth - 1) * H.edges.length := by
    intro _; rw [Nat.add_sub_cancel_left]; exact pow_le_of_step hshR he_pos hdR
  have hesum_all : H.edges.length + oRest.edgeSum ≤ (1 + oRest.depth) * H.edges.length := by
    calc H.edges.length + oRest.edgeSum
        ≤ H.edges.length + oRest.depth * actRest.edges.length := Nat.add_le_add_left hesR _
      _ ≤ H.edges.length + oRest.depth * H.edges.length :=
          Nat.add_le_add_left (Nat.mul_le_mul_left oRest.depth (le_of_lt hltR)) _
      _ = (1 + oRest.depth) * H.edges.length := by ring
  have he_eq : (G.inside H.vertSet).length = H.edges.length := congrArg List.length hRep.2.2.symm
  have heR_eq : actRest.edges.length = (G.inside (H.vertSet \ R)).length := congrArg List.length heR_in
  have hsplit := inside_length_split G hRX
  dsimp only [OuterRecSpec]
  refine ⟨hne_all, hpw_all, hunion_all, hexp_all, hdepth_all, hesum_all,
    cCR, G.cutIn H.vertSet R + cWR, (G.inside R).length + wRR, ?_, ?_, by omega, by omega, ?_⟩
  · have hcr_split := crossingCount_split_witness G (X := H.vertSet) (R := R)
      (parts := [R] ++ lRest) (pRest := oRest.parts) (by simp) (fun P hP => by simp [lRest, hP])
    have hinsR : G.inside (H.vertSet \ R) = G.inside actRest.vertSet := heR_in.symm.trans hactR_rep.2.2
    rw [crossingCount_congr_inside hinsR] at hcr_split
    dsimp only [lRest] at hcr_split
    omega
  · exact le_trans hpotR (Nat.mul_le_mul_left _ (cutPotential_mono (le_of_lt hltR)))
  · have hdist : 16 * bOut cfg M * (G.cutIn H.vertSet R + cWR) =
        16 * bOut cfg M * G.cutIn H.vertSet R + 16 * bOut cfg M * cWR := by ring
    omega

/-- Pre-`RemoveFake` conductance and minimum-degree bridge on `Graph.mk G.n (G.inside X ++ F')`:
matches the exact precondition of `ProgRemoveFake.removeFakeContract` on `H = G.inside X` and
`F = contractEdges G X F_out`. -/
lemma outerWitness_pre_removeFake {cfg : ParamConfig} {M r : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} {X : Finset ℕ} (hXdeg : ∀ v ∈ X, 1 ≤ G.degIn X v)
    {W_out F_out : List (ℕ × ℕ)}
    (hW_exp : (Graph.mk (2 * (G.inside X).length) W_out).IsExpansionExpanderOn
      (Finset.range (2 * (G.inside X).length)) (1 / (2 * (PParam cfg M r : ℝ))))
    (hF_valid : ∀ ed ∈ F_out, ed.1 < 2 * (G.inside X).length ∧ ed.2 < 2 * (G.inside X).length)
    (hF_deg : ∀ v < 2 * (G.inside X).length,
      (Graph.mk (2 * (G.inside X).length) F_out).deg v ≤ tParam M)
    {emb : ℕ → List ℕ}
    (hemb : IsEmbeddingOn ⟨2 * (G.inside X).length, W_out⟩
      ⟨2 * (G.inside X).length, (portGraph cloud G X).edges ++ F_out⟩
      (Finset.range (2 * (G.inside X).length)) emb)
    (hcong : ∀ i < (Graph.mk (2 * (G.inside X).length) ((portGraph cloud G X).edges ++ F_out)).m,
      congestion ⟨2 * (G.inside X).length, W_out⟩ emb i ≤ tParam M * ROut cfg M) :
    let F' := contractEdges G X F_out
    let K := Graph.mk G.n (G.inside X ++ F')
    K.IsConductanceExpanderOn X (((1 : ℕ) : ℝ) / (Lambda cfg M r : ℝ)) ∧
    (∀ v ∈ X, 1 ≤ K.degIn X v) := by
  intro F' K
  have hηpos : 0 < tParam M * ROut cfg M := Nat.mul_pos (one_le_tParam M) (one_le_ROut cfg M)
  have hβ0 : (0 : ℝ) ≤ 1 / (2 * (PParam cfg M r : ℝ)) := by positivity
  have hKcond_raw := isConductanceExpanderOn_contractedGraph_of_embedding hcloud hF_valid hF_deg
    hηpos hemb hcong hβ0 hW_exp
  have hLam_eq : (1 / (2 * (PParam cfg M r : ℝ))) /
      (((tParam M * ROut cfg M : ℕ) : ℝ) * ((tParam M + 1 : ℕ) : ℝ)) =
      (((1 : ℕ) : ℝ) / (Lambda cfg M r : ℝ)) := by
    have hPpos : (0 : ℝ) < (PParam cfg M r : ℝ) := by exact_mod_cast one_le_PParam cfg M r
    have htpos : (0 : ℝ) < (tParam M : ℝ) := by exact_mod_cast one_le_tParam M
    have hRpos : (0 : ℝ) < (ROut cfg M : ℝ) := by exact_mod_cast one_le_ROut cfg M
    have h1 : (Lambda cfg M r : ℝ) = (2 : ℝ) * (PParam cfg M r : ℝ) * (tParam M : ℝ) *
        (ROut cfg M : ℝ) * ((tParam M : ℝ) + 1) := by
      unfold Lambda; push_cast; ring
    rw [h1]; push_cast; field_simp
  rw [hLam_eq] at hKcond_raw
  have hins_eq : K.inside X = (contractedGraph G X F_out).inside X := by
    unfold K contractedGraph Graph.inside
    simp only [List.filter_append]
    congr 1
    exact List.filter_eq_self.mpr fun ed hed => by
      have h12 := (mem_inside_iff.mp hed).2; simp [h12.1, h12.2]
  have hcut_eq : ∀ S, K.cutIn X S = (contractedGraph G X F_out).cutIn X S := fun S => by
    unfold Graph.cutIn; rw [hins_eq]
  have hdeg_eq : ∀ v, K.degIn X v = (contractedGraph G X F_out).degIn X v := fun v => by
    unfold Graph.degIn; rw [hins_eq]
  have hvol_eq : ∀ S, K.volIn X S = (contractedGraph G X F_out).volIn X S := fun S => by
    unfold Graph.volIn; apply Finset.sum_congr rfl; intro v _; exact hdeg_eq v
  refine ⟨?_, ?_⟩
  · intro S hS hne hneX
    rw [hcut_eq S, hvol_eq S, hvol_eq (X \ S)]
    exact hKcond_raw S hS hne hneX
  · intro v hv
    rw [hdeg_eq v]
    have h1 := hXdeg v hv
    have h2 : G.degIn X v ≤ (contractedGraph G X F_out).degIn X v := by
      unfold contractedGraph
      rw [degIn_eq_sum_map, degIn_eq_sum_map]
      unfold Graph.inside; dsimp only
      rw [List.filter_append, List.map_append, List.sum_append]; omega
    omega

/-- Post-`RemoveFake` conductance and volume-budget bridge for ANY subset `R ⊆ X` meeting the
postcondition of `ProgRemoveFake.removeFakeContract`. -/
lemma outerWitness_post_removeFake {cfg : ParamConfig} {M r : ℕ}
    (hA60 : 60 ≤ cfg.A)
    {G : Graph} {X R : Finset ℕ} (hRX : R ⊆ X)
    (he_pos : 1 ≤ (G.inside X).length)
    {F' : List (ℕ × ℕ)} (hF'len : F'.length ≤ tParam M * ((G.inside X).length / DOut cfg M r))
    (hRcond : (Graph.mk G.n (G.inside X)).IsConductanceExpanderOn R
      ((((1 : ℕ) : ℝ) / (Lambda cfg M r : ℝ)) / 9))
    (hRvol : ((Graph.mk G.n (G.inside X ++ F')).volIn X (X \ R) : ℝ) ≤
      60 / (((1 : ℕ) : ℝ) / (Lambda cfg M r : ℝ)) * (F'.length : ℝ)) :
    R.Nonempty ∧
    G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)) ∧
    16 * bOut cfg M * G.volIn X (X \ R) ≤ (G.inside X).length := by
  set e := (G.inside X).length
  set z := e / DOut cfg M r
  set Λ := Lambda cfg M r
  have hins_R : (Graph.mk G.n (G.inside X)).inside R = G.inside R := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro ed _
    by_cases h1 : ed.1 ∈ R <;> by_cases h2 : ed.2 ∈ R
    · simp [h1, h2, hRX h1, hRX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hdeg_R : ∀ v, G.degIn R v = (Graph.mk G.n (G.inside X)).degIn R v := fun v => by
    unfold Graph.degIn; rw [hins_R]
  have hRcond_G : G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)) := by
    have hRcond_G1 : G.IsConductanceExpanderOn R ((1 : ℝ) / (Λ : ℝ) / 9) := by
      intro S hS hne hneR
      have hcut : G.cutIn R S = (Graph.mk G.n (G.inside X)).cutIn R S := by
        unfold Graph.cutIn; rw [hins_R]
      have hv1 : G.volIn R S = (Graph.mk G.n (G.inside X)).volIn R S := by
        unfold Graph.volIn; apply Finset.sum_congr rfl; intro v _; exact hdeg_R v
      have hv2 : G.volIn R (R \ S) = (Graph.mk G.n (G.inside X)).volIn R (R \ S) := by
        unfold Graph.volIn; apply Finset.sum_congr rfl; intro v _; exact hdeg_R v
      rw [hcut, hv1, hv2]
      simpa using hRcond S hS hne hneR
    apply isConductanceExpanderOn_mono _ hRcond_G1
    have h12 : 12 * Λ ≤ QOut cfg M r := twelve_mul_Lambda_le_QOut cfg M r
    have h9 : (9 * Λ : ℝ) ≤ (QOut cfg M r : ℝ) := by exact_mod_cast (by omega : 9 * Λ ≤ QOut cfg M r)
    have h9pos : (0 : ℝ) < 9 * (Λ : ℝ) := by have := one_le_Lambda cfg M r; positivity
    have hrew : (1 : ℝ) / (Λ : ℝ) / 9 = 1 / (9 * (Λ : ℝ)) := by ring
    rw [hrew]
    exact one_div_le_one_div_of_le h9pos h9
  have hvol_le_K : G.volIn X (X \ R) ≤ (Graph.mk G.n (G.inside X ++ F')).volIn X (X \ R) := by
    rw [volIn_eq_sum_map, volIn_eq_sum_map]
    have hins_sub : (Graph.mk G.n (G.inside X ++ F')).inside X =
        G.inside X ++ F'.filter fun ed => decide (ed.1 ∈ X) && decide (ed.2 ∈ X) := by
      unfold Graph.inside; simp only [List.filter_append]
      congr 1
      exact List.filter_eq_self.mpr fun ed hed => by
        have h12 := (mem_inside_iff.mp hed).2; simp [h12.1, h12.2]
    rw [hins_sub, List.map_append, List.sum_append]; omega
  have hΛ1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hvol_nat : G.volIn X (X \ R) ≤ cfg.A * tParam M * z * Λ := by
    have hvol_r : (G.volIn X (X \ R) : ℝ) ≤
        ((Graph.mk G.n (G.inside X ++ F')).volIn X (X \ R) : ℝ) := by exact_mod_cast hvol_le_K
    have h1 : (G.volIn X (X \ R) : ℝ) ≤ (60 / (1 / (Λ : ℝ))) * (F'.length : ℝ) :=
      le_trans hvol_r (by simpa using hRvol)
    have h2 : (60 : ℝ) / (1 / (Λ : ℝ)) = 60 * (Λ : ℝ) := by field_simp
    rw [h2] at h1
    have h3 : (G.volIn X (X \ R) : ℝ) ≤ ((60 * Λ * F'.length : ℕ) : ℝ) := by
      push_cast; linarith
    have h4 : G.volIn X (X \ R) ≤ 60 * Λ * F'.length := by exact_mod_cast h3
    calc G.volIn X (X \ R) ≤ 60 * Λ * F'.length := h4
      _ ≤ cfg.A * Λ * (tParam M * z) := Nat.mul_le_mul (Nat.mul_le_mul_right Λ hA60) hF'len
      _ = cfg.A * tParam M * z * Λ := by ring
  have h35 : 16 * bOut cfg M * G.volIn X (X \ R) ≤ e := by
    calc 16 * bOut cfg M * G.volIn X (X \ R)
        ≤ 16 * bOut cfg M * (cfg.A * tParam M * z * Λ) := Nat.mul_le_mul_left _ hvol_nat
      _ = DOut cfg M r * z := by dsimp only [Λ]; unfold DOut; ring
      _ ≤ e := Nat.mul_div_le e (DOut cfg M r)
  have hRne : R.Nonempty := by
    have hret := (edge_shrink_witness G hRX (one_le_bOut cfg M) (one_le_DOut cfg M r) he_pos h35).2.2.2.1
    have hR_pos : 0 < (G.inside R).length := by omega
    obtain ⟨ed, hed⟩ := List.exists_mem_of_length_pos hR_pos
    exact ⟨ed.1, (mem_inside_iff.mp hed).2.1⟩
  exact ⟨hRne, hRcond_G, h35⟩


end MinCostFlow.ExpanderDecomp
