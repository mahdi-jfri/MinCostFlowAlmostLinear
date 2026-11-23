module

public import MinCostFlow.ExpanderDecomp.OuterGame
public import MinCostFlow.ExpanderDecomp.OuterSubgraph
public import MinCostFlow.ExpanderDecomp.OuterBudgets
public import MinCostFlow.ExpanderDecomp.ParamsBounds
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The outer expander decomposition algorithm and its correctness

This file defines the recursive outer expander decomposition algorithm as a model
recuring on the current edge count `H.edges.length`, and proves all correctness guarantees of
the decomposition:

* `OuterRecOut`, `outerDecompAux`: single recursive function on `H.edges.length` returning the
  finalized parts together with the recursion depth, total edge-count sum, and witness edge-count
  sum.
* `outerDecompRec`, `outerDecompDepth`, `outerDecompEdgeSum`, `outerDecompWitnessEdgeSum`,
  `outerDecompParts`, `outerDecompLabels`: projections and top-level label array.
* `outerDecompAux_spec`: strong induction on `H.edges.length` proving all these guarantees.
* `outerDecompLabels_spec`: proves `IsExpanderDecomposition G (1 / cfg.E) (phiOut cfg G.m r)` for
  general `cfg` and `r`, together with the depth bound `HDepth` and edge-sum bounds.
* `outerDecompLabels_default_spec`: target theorem for `cfg = ParamConfig.default` (`E = 200`) and
  `r = rOf G.m` when `G.m ≥ thresholdB1 envelopeCr`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Bundled output of one recursive call of the outer expander decomposition on a stripped compact
subgraph `H`: the finalized parts together with tree depth, total edge sum, and witness edge sum. -/
structure OuterRecOut where
  /-- Finalized vertex subsets partitioning `H.vertSet`. -/
  parts : List (Finset ℕ)
  /-- Height of the recursion subtree (`0` if `e = 0`, `1` at a nonempty base case). -/
  depth : ℕ
  /-- Sum of `H'.edges.length` over all nodes `H'` in the subtree. -/
  edgeSum : ℕ
  /-- Sum of `H'.edges.length` over all witness-outcome nodes in the subtree. -/
  witnessEdgeSum : ℕ

/-- The recursive outer expander decomposition on an already-stripped compact subgraph `H`,
recuring on the current edge count `H.edges.length`. -/
noncomputable def outerDecompAux (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (H : CompactSubgraph) : OuterRecOut :=
  if _hQ : H.edges.length ≤ QOut cfg M r then
    { parts := H.componentsOf
      depth := if H.edges.length = 0 then 0 else 1
      edgeSum := H.edges.length
      witnessEdgeSum := 0 }
  else
    match outerGame cfg M r cloud core route G H.vertSet with
    | .cut U =>
      let S := roundPortCut G H.vertSet U
      let (iso₁, act₁) := (H.restrict S).stripIsolated
      let (iso₂, act₂) := (H.restrict (H.vertSet \ S)).stripIsolated
      let isoParts :=
        (iso₁.map fun v => ({v} : Finset ℕ)) ++ (iso₂.map fun v => ({v} : Finset ℕ))
      let o₁ := if _h1 : act₁.edges.length < H.edges.length then
          outerDecompAux cfg M r cloud core route G act₁
        else ⟨[], 0, 0, 0⟩
      let o₂ := if _h2 : act₂.edges.length < H.edges.length then
          outerDecompAux cfg M r cloud core route G act₂
        else ⟨[], 0, 0, 0⟩
      { parts := isoParts ++ o₁.parts ++ o₂.parts
        depth := 1 + max o₁.depth o₂.depth
        edgeSum := H.edges.length + o₁.edgeSum + o₂.edgeSum
        witnessEdgeSum := o₁.witnessEdgeSum + o₂.witnessEdgeSum }
    | .witness _ F_out =>
      let F' := contractEdges G H.vertSet F_out
      let R := removeFake G.n G.edges F' H.vertSet (1 / (Lambda cfg M r : ℝ))
      let (isoRest, actRest) := (H.restrict (H.vertSet \ R)).stripIsolated
      let isoParts := isoRest.map fun v => ({v} : Finset ℕ)
      let rPart := if R.Nonempty then [R] else []
      let oRest := if _hr : actRest.edges.length < H.edges.length then
          outerDecompAux cfg M r cloud core route G actRest
        else ⟨[], 0, 0, 0⟩
      { parts := rPart ++ isoParts ++ oRest.parts
        depth := 1 + oRest.depth
        edgeSum := H.edges.length + oRest.edgeSum
        witnessEdgeSum := H.edges.length + oRest.witnessEdgeSum }
termination_by H.edges.length

/-- Finalized parts produced by the recursive outer decomposition on `H`. -/
noncomputable def outerDecompRec (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (H : CompactSubgraph) : List (Finset ℕ) :=
  (outerDecompAux cfg M r cloud core route G H).parts

/-- Recursion depth of `outerDecompRec` rooted at `H`. -/
noncomputable def outerDecompDepth (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (H : CompactSubgraph) : ℕ :=
  (outerDecompAux cfg M r cloud core route G H).depth

/-- Sum of `H'.edges.length` over all nodes `H'` in the recursion tree rooted at `H`. -/
noncomputable def outerDecompEdgeSum (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (H : CompactSubgraph) : ℕ :=
  (outerDecompAux cfg M r cloud core route G H).edgeSum

/-- Sum of `H'.edges.length` over all witness nodes in the recursion tree rooted at `H`. -/
noncomputable def outerDecompWitnessEdgeSum (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) (H : CompactSubgraph) : ℕ :=
  (outerDecompAux cfg M r cloud core route G H).witnessEdgeSum

/-- The full list of finalized parts produced by the outer algorithm on `G`: strip root isolated
vertices once, then run `outerDecompRec` on the active subgraph. -/
noncomputable def outerDecompParts (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) : List (Finset ℕ) :=
  let (iso₀, act₀) := (CompactSubgraph.ofGraph G).stripIsolated
  (iso₀.map fun v => ({v} : Finset ℕ)) ++ outerDecompRec cfg M r cloud core route G act₀

/-- The length-`G.n` label array produced by the outer algorithm on `G`. -/
noncomputable def outerDecompLabels (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph) (core : ℕ → Graph → CoreResult) (route : RouterFn)
    (G : Graph) : List ℕ :=
  labelsOfParts G.n (outerDecompParts cfg M r cloud core route G)

/-- The invariant satisfied by `o : OuterRecOut` on a subgraph `H` representing `G[H.vertSet]`. -/
def OuterRecSpec (cfg : ParamConfig) (M r : ℕ) (G : Graph) (H : CompactSubgraph)
    (o : OuterRecOut) : Prop :=
  (∀ P ∈ o.parts, P.Nonempty ∧ P ⊆ H.vertSet) ∧
    o.parts.Pairwise Disjoint ∧
    o.parts.toFinset.biUnion id = H.vertSet ∧
    (∀ P ∈ o.parts, G.IsConductanceExpanderOn P (1 / (QOut cfg M r : ℝ))) ∧
    (1 ≤ o.depth →
      (16 * DOut cfg M r) ^ (o.depth - 1) ≤ (16 * DOut cfg M r - 1) ^ (o.depth - 1) * H.edges.length) ∧
    o.edgeSum ≤ o.depth * H.edges.length ∧
    ∃ cCut cWit wRet : ℕ,
      crossingCount G H.vertSet o.parts ≤ cCut + cWit ∧
      bOut cfg M * cCut ≤ 2 * cfg.kappa * cutPotential H.edges.length ∧
      wRet ≤ H.edges.length ∧
      15 * o.witnessEdgeSum ≤ 16 * wRet ∧
      16 * bOut cfg M * cWit ≤ o.witnessEdgeSum

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Factored base, cut, and witness combination lemmas -/

private theorem outerRecSpec_base {cfg : ParamConfig} {M r : ℕ} {G : Graph} {H : CompactSubgraph}
    (hRep : H.Represents G H.vertSet) (hQ : H.edges.length ≤ QOut cfg M r) :
    OuterRecSpec cfg M r G H
      { parts := H.componentsOf
        depth := if H.edges.length = 0 then 0 else 1
        edgeSum := H.edges.length
        witnessEdgeSum := 0 } := by
  have hQ1 : 1 ≤ QOut cfg M r := by unfold QOut; omega
  obtain ⟨_, hne_sub, hpw, hunion, hexp, _⟩ := H.componentsOf_spec hRep hQ1 hQ
  dsimp only [OuterRecSpec]
  refine ⟨hne_sub, hpw, hunion, hexp, ?_, ?_, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hd
    by_cases h0 : H.edges.length = 0
    · simp [h0] at hd
    · simp [h0]; omega
  · by_cases h0 : H.edges.length = 0
    · simp [h0]
    · simp [h0]
  · have hc0 := crossingCount_components_eq_zero hRep hQ1 hQ
    omega
  · simp
  · omega
  · omega
  · omega

private theorem outerRecSpec_cut_combine {cfg : ParamConfig} {M r : ℕ} {G : Graph}
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
          ((iso₁.map fun v => ({v} : Finset ℕ)) ++ (iso₂.map fun v => ({v} : Finset ℕ))) ++
            o₁.parts ++ o₂.parts
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
  let lIso1 := iso₁.map fun v => ({v} : Finset ℕ)
  let lIso2 := iso₂.map fun v => ({v} : Finset ℕ)
  have hpw_iso : (lIso1 ++ lIso2).Pairwise Disjoint :=
    pairwise_disjoint_append hi1_pw hi2_pw (by rw [hi1_u, hi2_u]; exact hdisjST.mono hiso1_sub hiso2_sub)
  have hpw_1 : ((lIso1 ++ lIso2) ++ o₁.parts).Pairwise Disjoint :=
    pairwise_disjoint_append hpw_iso hp1_pw (by
      rw [biUnion_append, hi1_u, hi2_u, hp1_u, Finset.disjoint_union_left]
      exact ⟨hdisj1, hdisjST.symm.mono hiso2_sub hact1_sub⟩)
  have hpw_all : (((lIso1 ++ lIso2) ++ o₁.parts) ++ o₂.parts).Pairwise Disjoint :=
    pairwise_disjoint_append hpw_1 hp2_pw (by
      rw [biUnion_append, biUnion_append, hi1_u, hi2_u, hp1_u, hp2_u,
        Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨hdisjST.mono hiso1_sub hact2_sub, hdisj2⟩, hdisjST.mono hact1_sub hact2_sub⟩)
  have hunion_all : (((lIso1 ++ lIso2) ++ o₁.parts) ++ o₂.parts).toFinset.biUnion id = H.vertSet := by
    rw [biUnion_append, biUnion_append, biUnion_append, hi1_u, hi2_u, hp1_u, hp2_u]
    calc (iso₁.toFinset ∪ iso₂.toFinset) ∪ act₁.vertSet ∪ act₂.vertSet
        = (iso₁.toFinset ∪ act₁.vertSet) ∪ (iso₂.toFinset ∪ act₂.vertSet) := by
          ext v; simp only [Finset.mem_union]; tauto
      _ = S ∪ (H.vertSet \ S) := by rw [hunion1, hunion2]
      _ = H.vertSet := Finset.union_sdiff_of_subset hSX
  have hne_all : ∀ P ∈ ((lIso1 ++ lIso2) ++ o₁.parts) ++ o₂.parts, P.Nonempty ∧ P ⊆ H.vertSet := by
    intro P hP
    simp only [List.mem_append] at hP
    rcases hP with ((h | h) | h) | h
    · exact ⟨(hi1_ne P h).1, (hi1_ne P h).2.trans (hiso1_sub.trans hSX)⟩
    · exact ⟨(hi2_ne P h).1, (hi2_ne P h).2.trans (hiso2_sub.trans Finset.sdiff_subset)⟩
    · exact ⟨(hp1_ne P h).1, (hp1_ne P h).2.trans (hact1_sub.trans hSX)⟩
    · exact ⟨(hp2_ne P h).1, (hp2_ne P h).2.trans (hact2_sub.trans Finset.sdiff_subset)⟩
  have hexp_all : ∀ P ∈ ((lIso1 ++ lIso2) ++ o₁.parts) ++ o₂.parts,
      G.IsConductanceExpanderOn P (1 / (QOut cfg M r : ℝ)) := by
    intro P hP
    simp only [List.mem_append] at hP
    rcases hP with ((h | h) | h) | h
    · exact hi1_exp P h
    · exact hi2_exp P h
    · exact hp1_exp P h
    · exact hp2_exp P h
  have hdepth_all : 1 ≤ 1 + max o₁.depth o₂.depth →
      (16 * DOut cfg M r) ^ (1 + max o₁.depth o₂.depth - 1) ≤
      (16 * DOut cfg M r - 1) ^ (1 + max o₁.depth o₂.depth - 1) * H.edges.length := by
    intro _
    rw [Nat.add_sub_cancel_left]
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
    have h1 : o₁.edgeSum ≤ m * act₁.edges.length :=
      le_trans hes1 (Nat.mul_le_mul_right _ (le_max_left _ _))
    have h2 : o₂.edgeSum ≤ m * act₂.edges.length :=
      le_trans hes2 (Nat.mul_le_mul_right _ (le_max_right _ _))
    calc H.edges.length + o₁.edgeSum + o₂.edgeSum
        ≤ H.edges.length + m * act₁.edges.length + m * act₂.edges.length := by omega
      _ = H.edges.length + m * (act₁.edges.length + act₂.edges.length) := by ring
      _ ≤ H.edges.length + m * H.edges.length :=
          Nat.add_le_add_left (Nat.mul_le_mul_left m (by omega)) _
      _ = (1 + m) * H.edges.length := by ring
  dsimp only [OuterRecSpec]
  refine ⟨hne_all, hpw_all, hunion_all, hexp_all, hdepth_all, hesum_all,
    G.cutIn H.vertSet S + cC1 + cC2, cW1 + cW2, wR1 + wR2, ?_, ?_, ?_, ?_, ?_⟩
  · have hcr_split := crossingCount_split_cut G hSX
      (parts := ((lIso1 ++ lIso2) ++ o₁.parts) ++ o₂.parts) (p₁ := o₁.parts) (p₂ := o₂.parts)
      (fun P hP => by simp [hP]) (fun P hP => by simp [hP])
    have hins1 : G.inside S = G.inside act₁.vertSet := he1_in.symm.trans hact1_rep.2.2
    have hins2 : G.inside (H.vertSet \ S) = G.inside act₂.vertSet := he2_in.symm.trans hact2_rep.2.2
    rw [crossingCount_congr_inside hins1, crossingCount_congr_inside hins2] at hcr_split
    dsimp only [lIso1, lIso2] at hcr_split
    omega
  · have hstep := cutPotential_step G hSX (b := bOut cfg M) (κ := cfg.kappa) h32
    rw [he_eq, ← he1_eq, ← he2_eq] at hstep
    have hdist : bOut cfg M * (G.cutIn H.vertSet S + cC1 + cC2) =
        bOut cfg M * G.cutIn H.vertSet S + bOut cfg M * cC1 + bOut cfg M * cC2 := by ring
    omega
  · omega
  · omega
  · have hdist : 16 * bOut cfg M * (cW1 + cW2) =
        16 * bOut cfg M * cW1 + 16 * bOut cfg M * cW2 := by ring
    omega

private theorem outerRecSpec_witness_combine {cfg : ParamConfig} {M r : ℕ} {G : Graph}
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
      { parts := ([R] ++ (isoRest.map fun v => ({v} : Finset ℕ))) ++ oRest.parts
        depth := 1 + oRest.depth
        edgeSum := H.edges.length + oRest.edgeSum
        witnessEdgeSum := H.edges.length + oRest.witnessEdgeSum } := by
  obtain ⟨hpR_ne, hpR_pw, hpR_u, hpR_exp, hdR, hesR, cCR, cWR, wRR, hcrR, hpotR, hwRR, hw15R, hw16R⟩ := hoR
  obtain ⟨hiR_ne, hiR_pw, hiR_u, hiR_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg M r : ℝ)) hiso_nd
  have hisoR_sub : isoRest.toFinset ⊆ H.vertSet \ R := by rw [← hunionR]; exact Finset.subset_union_left
  have hactR_sub : actRest.vertSet ⊆ H.vertSet \ R := by rw [← hunionR]; exact Finset.subset_union_right
  have hdisjR : Disjoint R (H.vertSet \ R) := disjoint_sdiff_self_right
  let lIso := isoRest.map fun v => ({v} : Finset ℕ)
  have hRbi : ([R] : List (Finset ℕ)).toFinset.biUnion id = R := by ext v; simp
  have hpw_1 : ([R] ++ lIso).Pairwise Disjoint :=
    pairwise_disjoint_append (List.pairwise_singleton _ _) hiR_pw (by
      rw [hRbi, hiR_u]; exact hdisjR.mono_right hisoR_sub)
  have hpw_all : (([R] ++ lIso) ++ oRest.parts).Pairwise Disjoint :=
    pairwise_disjoint_append hpw_1 hpR_pw (by
      rw [biUnion_append, hRbi, hiR_u, hpR_u, Finset.disjoint_union_left]
      exact ⟨hdisjR.mono_right hactR_sub, hdisjR_iso⟩)
  have hunion_all : (([R] ++ lIso) ++ oRest.parts).toFinset.biUnion id = H.vertSet := by
    rw [biUnion_append, biUnion_append, hRbi, hiR_u, hpR_u]
    calc R ∪ isoRest.toFinset ∪ actRest.vertSet
        = R ∪ (isoRest.toFinset ∪ actRest.vertSet) := Finset.union_assoc _ _ _
      _ = R ∪ (H.vertSet \ R) := by rw [hunionR]
      _ = H.vertSet := Finset.union_sdiff_of_subset hRX
  have hne_all : ∀ P ∈ ([R] ++ lIso) ++ oRest.parts, P.Nonempty ∧ P ⊆ H.vertSet := by
    intro P hP
    simp only [List.mem_append, List.mem_singleton] at hP
    rcases hP with (rfl | h) | h
    · exact ⟨hRne, hRX⟩
    · exact ⟨(hiR_ne P h).1, (hiR_ne P h).2.trans (hisoR_sub.trans Finset.sdiff_subset)⟩
    · exact ⟨(hpR_ne P h).1, (hpR_ne P h).2.trans (hactR_sub.trans Finset.sdiff_subset)⟩
  have hexp_all : ∀ P ∈ ([R] ++ lIso) ++ oRest.parts,
      G.IsConductanceExpanderOn P (1 / (QOut cfg M r : ℝ)) := by
    intro P hP
    simp only [List.mem_append, List.mem_singleton] at hP
    rcases hP with (rfl | h) | h
    · exact hRcond
    · exact hiR_exp P h
    · exact hpR_exp P h
  have hdepth_all : 1 ≤ 1 + oRest.depth →
      (16 * DOut cfg M r) ^ (1 + oRest.depth - 1) ≤
      (16 * DOut cfg M r - 1) ^ (1 + oRest.depth - 1) * H.edges.length := by
    intro _
    rw [Nat.add_sub_cancel_left]
    exact pow_le_of_step hshR he_pos hdR
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
    cCR, G.cutIn H.vertSet R + cWR, (G.inside R).length + wRR, ?_, ?_, ?_, ?_, ?_⟩
  · have hcr_split := crossingCount_split_witness G (X := H.vertSet) (R := R)
      (parts := ([R] ++ lIso) ++ oRest.parts) (pRest := oRest.parts)
      (by simp) (fun P hP => by simp [hP])
    have hinsR : G.inside (H.vertSet \ R) = G.inside actRest.vertSet := heR_in.symm.trans hactR_rep.2.2
    rw [crossingCount_congr_inside hinsR] at hcr_split
    dsimp only [lIso] at hcr_split
    omega
  · exact le_trans hpotR (Nat.mul_le_mul_left _ (cutPotential_mono (le_of_lt hltR)))
  · omega
  · omega
  · have hdist : 16 * bOut cfg M * (G.cutIn H.vertSet R + cWR) =
        16 * bOut cfg M * G.cutIn H.vertSet R + 16 * bOut cfg M * cWR := by ring
    omega

/-! ### Main strong induction on `outerDecompAux` -/

/-- Unified correctness, budget, depth, and edge-sum invariant of `outerDecompAux`, proved by
strong induction on `H.edges.length`. -/
theorem outerDecompAux_spec {cfg : ParamConfig} {M r : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α) (hA60 : 60 ≤ cfg.A)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    (hcore : IsCorePlayer cfg M r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} (hv : G.IsValid)
    (h2M_pow : 2 * M ≤ (NOf M r) ^ r) (h2M_L : 2 * M < 2 ^ LParam M) :
    ∀ (eBound : ℕ) (H : CompactSubgraph),
      H.edges.length ≤ eBound →
      H.Represents G H.vertSet →
      H.vertSet ⊆ G.verts →
      H.edges.length ≤ M →
      (∀ v ∈ H.vertSet, 1 ≤ G.degIn H.vertSet v) →
      OuterRecSpec cfg M r G H (outerDecompAux cfg M r cloud core route G H) := by
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hb1 : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have hb_a0 : 2 * cfg.a₀ ≤ bOut cfg M := two_mul_a0_le_bOut cfg M
  intro eBound
  induction eBound with
  | zero =>
    intro H heB hRep _ _ _
    rw [outerDecompAux.eq_def]
    have hQ : H.edges.length ≤ QOut cfg M r := by omega
    simp only [hQ, ↓reduceDIte]
    exact outerRecSpec_base hRep hQ
  | succ n ih =>
    intro H heB hRep hXV heM hXdeg
    rw [outerDecompAux.eq_def]
    by_cases hQ : H.edges.length ≤ QOut cfg M r
    · simp only [hQ, ↓reduceDIte]
      exact outerRecSpec_base hRep hQ
    · simp only [hQ, ↓reduceDIte]
      have hQlt : QOut cfg M r < H.edges.length := by omega
      have he_eq : (G.inside H.vertSet).length = H.edges.length :=
        congrArg List.length hRep.2.2.symm
      have he_pos : 1 ≤ (G.inside H.vertSet).length := by unfold QOut at hQlt; omega
      have h2D_lt : 2 * DOut cfg M r < (G.inside H.vertSet).length := by unfold QOut at hQlt; omega
      have h2e_pow : 2 * (G.inside H.vertSet).length ≤ (NOf M r) ^ r := by omega
      have h2e_L : 2 * (G.inside H.vertSet).length < 2 ^ LParam M := by omega
      have hgame := outerGame_spec hcloud hcore hroute he_pos h2e_pow h2e_L
      cases hres : outerGame cfg M r cloud core route G H.vertSet with
      | cut U =>
        dsimp only
        rw [hres] at hgame
        obtain ⟨hUV, hUsparse, hUz1, hUz2⟩ := hgame
        let S := roundPortCut G H.vertSet U
        obtain ⟨hSX, _, _, hUret1, hUret2, _, h32⟩ := lemma_8 hcloud cfg.ha₀ hα hb_a0 hUV hUsparse
        change S ⊆ H.vertSet at hSX
        change U.card ≤ 2 * G.volIn H.vertSet S at hUret1
        change ((portGraph cloud G H.vertSet).verts \ U).card ≤
          2 * G.volIn H.vertSet (H.vertSet \ S) at hUret2
        change bOut cfg M * G.cutIn H.vertSet S ≤
          cfg.kappa * min (G.volIn H.vertSet S) (G.volIn H.vertSet (H.vertSet \ S)) at h32
        obtain ⟨hsh1, hsh2, hlt1_in, hlt2_in⟩ := edge_shrink_cut G hSX hD1 h2D_lt
          (by omega) (by omega) hUret1 hUret2
        have hrep1 := CompactSubgraph.restrict_represents hRep hSX
        have hrep2 := CompactSubgraph.restrict_represents hRep
          (Finset.sdiff_subset (s := H.vertSet) (t := S))
        have hst1 := CompactSubgraph.stripIsolated_spec hrep1
        have hst2 := CompactSubgraph.stripIsolated_spec hrep2
        let act₁ := (H.restrict S).stripIsolated.2
        let act₂ := (H.restrict (H.vertSet \ S)).stripIsolated.2
        have he1_in : act₁.edges = G.inside S := hst1.2.2.2.2.2.1.trans hrep1.2.2
        have he2_in : act₂.edges = G.inside (H.vertSet \ S) := hst2.2.2.2.2.2.1.trans hrep2.2.2
        have he1_eq : act₁.edges.length = (G.inside S).length := congrArg List.length he1_in
        have he2_eq : act₂.edges.length = (G.inside (H.vertSet \ S)).length :=
          congrArg List.length he2_in
        have hlt1 : act₁.edges.length < H.edges.length := by omega
        have hlt2 : act₂.edges.length < H.edges.length := by omega
        have ho1 : (if _h1 : act₁.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G act₁ :=
          dite_eq_left_of_eq_true (eq_true hlt1)
        have ho2 : (if _h2 : act₂.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G act₂ :=
          dite_eq_left_of_eq_true (eq_true hlt2)
        have hact1_sub : act₁.vertSet ⊆ S := by rw [← hst1.2.2.1]; exact Finset.subset_union_right
        have hact2_sub : act₂.vertSet ⊆ H.vertSet \ S := by
          rw [← hst2.2.2.1]; exact Finset.subset_union_right
        have ih1 := ih act₁ (by omega) hst1.2.2.2.2.1 ((hact1_sub.trans hSX).trans hXV) (by omega)
          hst1.2.2.2.2.2.2.1
        have ih2 := ih act₂ (by omega) hst2.2.2.2.2.1
          ((hact2_sub.trans Finset.sdiff_subset).trans hXV) (by omega) hst2.2.2.2.2.2.2.1
        have hsh1' : 16 * DOut cfg M r * act₁.edges.length ≤
            (16 * DOut cfg M r - 1) * H.edges.length := by
          rw [he1_eq, ← he_eq]; exact hsh1
        have hsh2' : 16 * DOut cfg M r * act₂.edges.length ≤
            (16 * DOut cfg M r - 1) * H.edges.length := by
          rw [he2_eq, ← he_eq]; exact hsh2
        have hcomb := outerRecSpec_cut_combine (act₁ := act₁) (act₂ := act₂) (S := S)
          hRep hSX (by omega) hst1.1 hst1.2.1 hst1.2.2.1
          hst1.2.2.2.2.1 he1_in hst2.1 hst2.2.1 hst2.2.2.1 hst2.2.2.2.2.1 he2_in h32
          hsh1' hsh2' ih1 ih2
        change OuterRecSpec cfg M r G H
          { parts := (((H.restrict S).stripIsolated.1.map fun v => ({v} : Finset ℕ)) ++
              ((H.restrict (H.vertSet \ S)).stripIsolated.1.map fun v => ({v} : Finset ℕ))) ++
              (if _h1 : act₁.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).parts ++
              (if _h2 : act₂.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).parts
            depth := 1 + max
              (if _h1 : act₁.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).depth
              (if _h2 : act₂.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).depth
            edgeSum := H.edges.length +
              (if _h1 : act₁.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).edgeSum +
              (if _h2 : act₂.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).edgeSum
            witnessEdgeSum :=
              (if _h1 : act₁.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).witnessEdgeSum +
              (if _h2 : act₂.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).witnessEdgeSum }
        rw [ho1, ho2]
        exact hcomb
      | witness W_out F_out =>
        dsimp only
        rw [hres] at hgame
        obtain ⟨hW_exp, hF_valid, hF_len, hF_deg, emb, hemb, hcong⟩ := hgame
        let F' := contractEdges G H.vertSet F_out
        let R := removeFake G.n G.edges F' H.vertSet (1 / (Lambda cfg M r : ℝ))
        obtain ⟨hRX, hRne, hRcond, _, h35⟩ := outerWitness_removeFake hcloud hA60 hv hXV hXdeg
          he_pos hW_exp hF_valid hF_len hF_deg hemb hcong
        change R ⊆ H.vertSet at hRX
        change R.Nonempty at hRne
        change G.IsConductanceExpanderOn R (1 / (QOut cfg M r : ℝ)) at hRcond
        change 16 * bOut cfg M * G.volIn H.vertSet (H.vertSet \ R) ≤
          (G.inside H.vertSet).length at h35
        obtain ⟨_, hshR, hltR_in, hretR, hcutR⟩ :=
          edge_shrink_witness G hRX hb1 hD1 he_pos h35
        have hrepR := CompactSubgraph.restrict_represents hRep
          (Finset.sdiff_subset (s := H.vertSet) (t := R))
        have hstR := CompactSubgraph.stripIsolated_spec hrepR
        let actRest := (H.restrict (H.vertSet \ R)).stripIsolated.2
        have heR_in : actRest.edges = G.inside (H.vertSet \ R) := hstR.2.2.2.2.2.1.trans hrepR.2.2
        have heR_eq : actRest.edges.length = (G.inside (H.vertSet \ R)).length :=
          congrArg List.length heR_in
        have hltR : actRest.edges.length < H.edges.length := by omega
        have hoR : (if _hr : actRest.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G actRest :=
          dite_eq_left_of_eq_true (eq_true hltR)
        have hrP : (if R.Nonempty then [R] else []) = [R] :=
          ite_eq_left_iff.mpr fun h => absurd hRne h
        have hactR_sub : actRest.vertSet ⊆ H.vertSet \ R := by
          rw [← hstR.2.2.1]; exact Finset.subset_union_right
        have ihR := ih actRest (by omega) hstR.2.2.2.2.1
          ((hactR_sub.trans Finset.sdiff_subset).trans hXV) (by omega) hstR.2.2.2.2.2.2.1
        have hshR' : 16 * DOut cfg M r * actRest.edges.length ≤
            (16 * DOut cfg M r - 1) * H.edges.length := by
          rw [heR_eq, ← he_eq]; exact hshR
        have hretR' : 15 * H.edges.length ≤ 16 * (G.inside R).length := by
          rw [← he_eq]; exact hretR
        have hcutR' : 16 * bOut cfg M * G.cutIn H.vertSet R ≤ H.edges.length := by
          rw [← he_eq]; exact hcutR
        have hcomb := outerRecSpec_witness_combine (actRest := actRest) (R := R)
          hRep hRX hRne (by omega) hRcond hstR.1 hstR.2.1
          hstR.2.2.1 hstR.2.2.2.2.1 heR_in hshR' hltR hretR' hcutR' ihR
        change OuterRecSpec cfg M r G H
          { parts := (if R.Nonempty then [R] else []) ++
              ((H.restrict (H.vertSet \ R)).stripIsolated.1.map fun v => ({v} : Finset ℕ)) ++
              (if _hr : actRest.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).parts
            depth := 1 +
              (if _hr : actRest.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).depth
            edgeSum := H.edges.length +
              (if _hr : actRest.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).edgeSum
            witnessEdgeSum := H.edges.length +
              (if _hr : actRest.edges.length < H.edges.length then
                outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).witnessEdgeSum }
        rw [hoR, hrP]
        exact hcomb

/-! ### Top-level correctness, depth, edge-sum, and target theorems -/

/-- **Complete correctness for general `cfg` and `r`**: for any valid graph `G` with
`M = G.m`, `1 ≤ r ≤ ell M`, `1 / cfg.a₀ ≤ α`, and `60 ≤ cfg.A`:
1. `outerDecompLabels` satisfies `IsExpanderDecomposition G (1 / cfg.E) (phiOut cfg M r)`;
2. the recursion depth is at most `HDepth cfg M r`;
3. the sum of edge counts over all recursion nodes is at most `HDepth cfg M r * M`;
4. the sum of edge counts over all witness nodes satisfies `15 * wSum ≤ 16 * M`. -/
theorem outerDecompLabels_spec {cfg : ParamConfig} {r : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α) (hA60 : 60 ≤ cfg.A)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {G : Graph} (hv : G.IsValid)
    (hr1 : 1 ≤ r) (hrl : r ≤ ell G.m)
    (hcore : IsCorePlayer cfg G.m r core coreCost)
    (hroute : IsMatchingPlayer route routeCost) :
    let act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
    IsExpanderDecomposition G (1 / (cfg.E : ℝ)) (phiOut cfg G.m r)
        (outerDecompLabels cfg G.m r cloud core route G) ∧
      outerDecompDepth cfg G.m r cloud core route G act₀ ≤ HDepth cfg G.m r ∧
      outerDecompEdgeSum cfg G.m r cloud core route G act₀ ≤ HDepth cfg G.m r * G.m ∧
      15 * outerDecompWitnessEdgeSum cfg G.m r cloud core route G act₀ ≤ 16 * G.m := by
  have h2M_pow : 2 * G.m ≤ (NOf G.m r) ^ r := by
    have := two_mul_add_two_le_NOf_pow G.m hr1; omega
  have h2M_L : 2 * G.m < 2 ^ LParam G.m := by
    have h1 := two_mul_add_two_le_NOf_pow G.m hr1
    have h2 := NOf_pow_add_two_le_two_pow_L G.m hr1 hrl
    omega
  have hrep0 := CompactSubgraph.ofGraph_represents hv
  have hst0 := CompactSubgraph.stripIsolated_spec hrep0
  let iso₀ := (CompactSubgraph.ofGraph G).stripIsolated.1
  let act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
  have he0_eq : act₀.edges.length = G.m := by
    have h1 : act₀.edges = (CompactSubgraph.ofGraph G).edges := hst0.2.2.2.2.2.1
    rw [h1]; rfl
  have hact0_sub : act₀.vertSet ⊆ G.verts := by
    rw [← hst0.2.2.1]; exact Finset.subset_union_right
  have hrec := outerDecompAux_spec hcloud hα hA60 hcore hroute hv h2M_pow h2M_L
    G.m act₀ (by omega) hst0.2.2.2.2.1 hact0_sub (by omega) hst0.2.2.2.2.2.2.1
  obtain ⟨hp_ne, hp_pw, hp_u, hp_exp, hd_pow, hes, cCut, cWit, wRet, hcr, hpot, hwRet, hw15, hw16⟩ := hrec
  obtain ⟨hi_ne, hi_pw, hi_u, hi_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg G.m r : ℝ)) hst0.1
  let lIso := iso₀.map fun v => ({v} : Finset ℕ)
  let pAct := outerDecompRec cfg G.m r cloud core route G act₀
  let parts := lIso ++ pAct
  have hi_u' : lIso.toFinset.biUnion id = iso₀.toFinset := hi_u
  have hp_u' : pAct.toFinset.biUnion id = act₀.vertSet := hp_u
  have hne_all : ∀ P ∈ parts, P.Nonempty := by
    intro P hP
    rcases List.mem_append.mp hP with h | h
    · exact (hi_ne P h).1
    · exact (hp_ne P h).1
  have hpw_all : parts.Pairwise Disjoint :=
    pairwise_disjoint_append hi_pw hp_pw (by rw [hi_u', hp_u']; exact hst0.2.1)
  have hunion_all : parts.toFinset.biUnion id = G.verts := by
    rw [biUnion_append, hi_u', hp_u']
    exact hst0.2.2.1
  have hexp_all : ∀ P ∈ parts, G.IsConductanceExpanderOn P (phiOut cfg G.m r) := by
    intro P hP
    unfold phiOut
    rcases List.mem_append.mp hP with h | h
    · exact hi_exp P h
    · exact hp_exp P h
  obtain ⟨hlen_lbl, hpartsOf, _⟩ := labelsOfParts_spec (G := G) hne_all hpw_all hunion_all
  have hK2 : 2 ≤ 16 * DOut cfg G.m r := by have := one_le_DOut cfg G.m r; omega
  have hdepth_le : outerDecompDepth cfg G.m r cloud core route G act₀ ≤ HDepth cfg G.m r := by
    have h1 : (outerDecompAux cfg G.m r cloud core route G act₀).depth ≤
        16 * DOut cfg G.m r * (ell G.m + 1) :=
      depth_le_of_pow hK2 (by omega : act₀.edges.length ≤ G.m) hd_pow
    change (outerDecompAux cfg G.m r cloud core route G act₀).depth ≤ HDepth cfg G.m r
    unfold HDepth; omega
  have hesum_le : outerDecompEdgeSum cfg G.m r cloud core route G act₀ ≤ HDepth cfg G.m r * G.m := by
    calc outerDecompEdgeSum cfg G.m r cloud core route G act₀
        ≤ outerDecompDepth cfg G.m r cloud core route G act₀ * act₀.edges.length := hes
      _ ≤ HDepth cfg G.m r * G.m := Nat.mul_le_mul hdepth_le (by omega)
  have hwsum_le : 15 * outerDecompWitnessEdgeSum cfg G.m r cloud core route G act₀ ≤ 16 * G.m := by
    change 15 * (outerDecompAux cfg G.m r cloud core route G act₀).witnessEdgeSum ≤ 16 * G.m
    omega
  have hcut_36 : 8 * cfg.E * cCut ≤ G.m := by
    have h1 : bOut cfg G.m * cCut ≤ 2 * cfg.kappa * (G.m * (ell G.m + 1)) := by
      calc bOut cfg G.m * cCut ≤ 2 * cfg.kappa * cutPotential act₀.edges.length := hpot
        _ = 2 * cfg.kappa * cutPotential G.m := by rw [he0_eq]
        _ ≤ 2 * cfg.kappa * (G.m * (ell G.m + 1)) :=
            Nat.mul_le_mul_left _ (cutPotential_le_mul_ell G.m)
    have hden := cut_budget_denom cfg G.m
    have hmul : bOut cfg G.m * (8 * cfg.E * cCut) ≤ bOut cfg G.m * G.m := by
      calc bOut cfg G.m * (8 * cfg.E * cCut)
          = 8 * cfg.E * (bOut cfg G.m * cCut) := by ring
        _ ≤ 8 * cfg.E * (2 * cfg.kappa * (G.m * (ell G.m + 1))) := Nat.mul_le_mul_left _ h1
        _ = (16 * cfg.kappa * (ell G.m + 1) * cfg.E) * G.m := by ring
        _ ≤ bOut cfg G.m * G.m := Nat.mul_le_mul_right G.m hden
    exact Nat.le_of_mul_le_mul_left hmul (one_le_bOut cfg G.m)
  have hcut_37 : 15 * bOut cfg G.m * cWit ≤ G.m := by
    have h16 : 16 * (15 * bOut cfg G.m * cWit) ≤ 16 * G.m := by
      calc 16 * (15 * bOut cfg G.m * cWit)
          = 15 * (16 * bOut cfg G.m * cWit) := by ring
        _ ≤ 15 * outerDecompWitnessEdgeSum cfg G.m r cloud core route G act₀ :=
            Nat.mul_le_mul_left 15 hw16
        _ ≤ 16 * G.m := hwsum_le
    exact Nat.le_of_mul_le_mul_left h16 (by decide)
  have hcomb : cfg.E * (cCut + cWit) ≤ G.m :=
    combined_cut_budget (E_le_bOut cfg G.m) hcut_36 hcut_37
  have hcross_lbl :
      (G.edges.filter fun ed =>
        decide ((labelsOfParts G.n parts).getD ed.1 0 ≠ (labelsOfParts G.n parts).getD ed.2 0)).length ≤
      cCut + cWit := by
    have hins_act : G.inside act₀.vertSet = G.edges :=
      hst0.2.2.2.2.1.2.2.symm.trans hst0.2.2.2.2.2.1
    have hle : (G.edges.filter fun ed =>
        decide ((labelsOfParts G.n parts).getD ed.1 0 ≠ (labelsOfParts G.n parts).getD ed.2 0)).length ≤
        crossingCount G act₀.vertSet pAct := by
      unfold crossingCount
      rw [hins_act]
      apply length_filter_le_of_imp
      intro ed hed hne_lbl
      rw [decide_eq_true_iff] at hne_lbl ⊢
      have hv_e := hv ed hed
      have hno := (filter_diff_labelsOfParts_eq hne_all hpw_all hunion_all
        (Finset.mem_range.mpr hv_e.1) (Finset.mem_range.mpr hv_e.2)).mp hne_lbl
      intro P hP
      exact hno P (List.mem_append_right lIso hP)
    exact le_trans hle hcr
  have hsum_cut_nat : cfg.E * ∑ X ∈ partsOf G (labelsOfParts G.n parts), G.cut X ≤
      G.vol G.verts := by
    rw [sum_cut_partsOf hv, vol_verts_of_isValid hv]
    have hmul : cfg.E * (2 * (G.edges.filter fun ed =>
        decide ((labelsOfParts G.n parts).getD ed.1 0 ≠
          (labelsOfParts G.n parts).getD ed.2 0)).length) ≤
        2 * (cfg.E * (cCut + cWit)) := by
      calc cfg.E * (2 * (G.edges.filter fun ed =>
            decide ((labelsOfParts G.n parts).getD ed.1 0 ≠
              (labelsOfParts G.n parts).getD ed.2 0)).length)
          = 2 * (cfg.E * (G.edges.filter fun ed =>
            decide ((labelsOfParts G.n parts).getD ed.1 0 ≠
              (labelsOfParts G.n parts).getD ed.2 0)).length) := by ring
        _ ≤ 2 * (cfg.E * (cCut + cWit)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left cfg.E hcross_lbl)
    omega
  have hsum_cut_real : (∑ X ∈ partsOf G (labelsOfParts G.n parts), (G.cut X : ℝ)) ≤
      1 / (cfg.E : ℝ) * (G.vol G.verts : ℝ) := by
    have hEpos : (0 : ℝ) < (cfg.E : ℝ) := by exact_mod_cast cfg.hE
    have hnat_r : (cfg.E : ℝ) * (∑ X ∈ partsOf G (labelsOfParts G.n parts), (G.cut X : ℝ)) ≤
        (G.vol G.verts : ℝ) := by
      have : ((cfg.E * ∑ X ∈ partsOf G (labelsOfParts G.n parts), G.cut X : ℕ) : ℝ) ≤
          (G.vol G.verts : ℝ) := by exact_mod_cast hsum_cut_nat
      simpa [Nat.cast_sum] using this
    rw [one_div_mul_eq_div, le_div_iff₀ hEpos]
    linarith
  refine ⟨⟨hlen_lbl, ?_, hsum_cut_real⟩, hdepth_le, hesum_le, hwsum_le⟩
  intro X hX
  change X ∈ partsOf G (labelsOfParts G.n parts) at hX
  rw [hpartsOf, List.mem_toFinset] at hX
  exact hexp_all X hX

/-- **Target decomposition theorem**: for a valid loopless graph `G` with
`G.m ≥ thresholdB1 envelopeCr`, `cfg = ParamConfig.default` (`E = 200`, `a₀ = 12`, `a = 15`),
cloud expanders of expansion `≥ 1 / 12` (such as `ExplicitExpander.explicitGraph`), a core player,
and a matching player, the labels `outerDecompLabels` satisfy
`IsExpanderDecomposition G (1 / 200) (phiOut cfg G.m (rOf G.m))`. -/
theorem outerDecompLabels_default_spec
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / 12 ≤ α)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {G : Graph} (hv : G.IsValid) (_hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m)
    (hcore : IsCorePlayer ParamConfig.default G.m (rOf G.m) core coreCost)
    (hroute : IsMatchingPlayer route routeCost) :
    IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m))
      (outerDecompLabels ParamConfig.default G.m (rOf G.m) cloud core route G) := by
  have hm4 : 4 ≤ G.m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hr1 : 1 ≤ rOf G.m := one_le_rOf (by omega)
  have hrl : rOf G.m ≤ ell G.m := rOf_le_ell G.m
  have h := (outerDecompLabels_spec (cfg := ParamConfig.default) (r := rOf G.m)
    hcloud (by simpa [ParamConfig.default] using hα) (by decide : 60 ≤ ParamConfig.default.A)
    hv hr1 hrl hcore hroute).1
  simpa [ParamConfig.default] using h

end MinCostFlow.ExpanderDecomp
