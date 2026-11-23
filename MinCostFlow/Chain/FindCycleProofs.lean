module

public import MinCostFlow.Chain.Algorithm1UpdateProofs
public import MinCostFlow.Chain.CycleLemmas
import MinCostFlow.Chain.WalkFlow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# FindCycle Quality and Level Graph Size Bounds (Lemma 5.11 Helpers)

Split from `MinCostFlow.Chain.Lemma5_11`: `FindCycle` quality, heap keys,
`lemma_A_2_wlen`, `findCycle_spec`, and `level_graph_size_bounds`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section FindCycleProofs

private lemma fundChainCycle_walkLength_pos (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    (hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e) {e : ℕ} (he : e ∈ G.E \ C.chainTree.E) :
    0 < walkLength ℓ (C.fundChainCycle e) := by
  have hℓ : ∀ f ∈ G.E, 0 ≤ ℓ f := fun f hf => le_of_lt (hℓ_pos f hf)
  have he0 : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
  have hlvl := C.mem_activeCore_diff_edgeLevel hH he0
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hlvl.1 hlvl.2
  have hIter := C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hlvl.1 hlvl.2
  have hneSp : C.sparsifierCycle (C.edgeLevel e) e ≠ [] := by simp [TreeChain.sparsifierCycle]
  have hNonT := C.iterLift_walkFlow_nonTree hH hSub (C.edgeLevel e) hlvl.1
    hneSp hClosed e (Finset.mem_sdiff.mp he).2
  have hFlowE : walkFlow (C.fundChainCycle e) e = 1 := by
    change walkFlow (C.fundChainCycleAt (C.edgeLevel e) e) e = 1
    rw [← hIter, hNonT]
    have hsub := C.sparsifierCycle_revEmb_edges_subset hH hlvl.1 (Finset.mem_sdiff.mp hlvl.2).1
    have hnot : e ∉ walkEdges (walkRev (C.activeEmb (C.edgeLevel e) e)) := fun hm =>
      (Finset.mem_sdiff.mp hlvl.2).2 (hsub hm)
    simp [TreeChain.sparsifierCycle, walkFlow_cons, walkFlow_eq_zero_of_not_mem hnot]
  have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hlvl.1 hlvl.2
  have hSubG : walkEdges (C.fundChainCycle e) ⊆ G.E :=
    hH.1 ▸ fun f hf => mem_E_of_mem_walkEdges hFundWalk hf
  rw [walkLength_eq_sum_of_subset hSubG]
  have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  refine Finset.sum_pos' (fun f hf => mul_nonneg (hℓ f hf) (abs_nonneg _)) ?_
  exact ⟨e, heG, by rw [hFlowE, abs_one, mul_one]; exact hℓ_pos e heG⟩

/-- For every off-tree edge `e ∈ E(G) \ E(T^𝒢)`, the length overestimate `C.wlen ℓ e` is
strictly positive when `ℓ > 0` on `G`. -/
lemma wlen_pos_of_mem_sdiff (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    (hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e) {e : ℕ} (he : e ∈ G.E \ C.chainTree.E) :
    0 < C.wlen ℓ e :=
  lt_of_lt_of_le (fundChainCycle_walkLength_pos C hH hSub hSpan hℓ_pos he)
    (C.lemma_7_13 hH hSub hSpan hℓ_pos he)

/-- By repaired `lemma_7_12` and `lemma_7_13`, the Word-RAM heap key `heapCycleRatio C g ℓ e` is at
most `exactCycleRatio C g ℓ e` for every off-tree edge `e ∈ E(G) \ E(T^𝒢)`. -/
lemma heapCycleRatio_le_exactCycleRatio (C : TreeChain) {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    (hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e) {e : ℕ} (he : e ∈ G.E \ C.chainTree.E) :
    heapCycleRatio C g ℓ e ≤ exactCycleRatio C g ℓ e := by
  have he0 : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
  have hlvl := C.mem_activeCore_diff_edgeLevel hH he0
  have hGrad : walkInner (C.chainGrad g (C.edgeLevel e + 1)) (C.sparsifierCycle (C.edgeLevel e) e) =
      walkInner g (C.fundChainCycle e) :=
    C.lemma_7_12 hH hSpan hlvl.1 hlvl.2
  have hLenPos := fundChainCycle_walkLength_pos C hH hSub hSpan hℓ_pos he
  have hLenLe := C.lemma_7_13 hH hSub hSpan hℓ_pos he
  unfold heapCycleRatio exactCycleRatio
  dsimp only
  rw [hGrad]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hLenPos hLenLe

/-- Version of Lemma A.2 (Appendix A.3, page 48; Lemma 5.11 proof, page 24) using `heapCycleRatio`
in the supremum, justifying the Word-RAM heap implementation of `FindCycle`. -/
theorem lemma_A_2_wlen (C : TreeChain) {G : MGraph} {ℓ g c w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) (hEmbSurv : C.EmbedsSurviving)
    (hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e) (hvp : IsValidPair G ℓ c w)
    (hne : (G.E \ C.chainTree.E).Nonempty) :
    (1 / (σ + 1)) * (|G.inner g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
      (G.E \ C.chainTree.E).sup' hne (heapCycleRatio C g ℓ) := by
  have hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e := fun e he => le_of_lt (hℓ_pos e he)
  set S := G.E \ C.chainTree.E
  set Wtot := ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)
  set M := S.sup' hne (heapCycleRatio C g ℓ)
  have hσ_pos : 0 < σ + 1 := by
    obtain ⟨e₀, he₀⟩ := hne
    have he₀G := (Finset.mem_sdiff.mp he₀).1
    have hL0 := C.activeLSF_holds hH (Nat.zero_le C.d)
    have h1 := one_le_stretch (hSub 0 (Nat.zero_le C.d)) (by simpa [hH.1] using hℓ) (hH.1 ▸ he₀G)
    have h2 := (hL0.2.2.2 e₀ (hH.1 ▸ he₀G)).1
    have h3 := (hL0.2.2.2 e₀ (hH.1 ▸ he₀G)).2
    have hcl0 : C.chainLen ℓ 0 = ℓ := by simp [TreeChain.chainLen]
    rw [hcl0] at h2
    linarith
  have hGradEq : ∀ e ∈ S, |walkInner g (C.fundChainCycle e)| =
      |walkInner (C.chainGrad g (C.edgeLevel e + 1)) (C.sparsifierCycle (C.edgeLevel e) e)| := by
    intro e he
    have he0 : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
    have hlvl := C.mem_activeCore_diff_edgeLevel hH he0
    rw [C.lemma_7_12 hH hSpan hlvl.1 hlvl.2]; rfl
  have hWlenPos : ∀ e ∈ S, 0 < C.wlen ℓ e := fun e he => wlen_pos_of_mem_sdiff C hH hSub hSpan hℓ_pos he
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨e₀, he₀⟩ := hne
    exact le_trans (div_nonneg (abs_nonneg _) (le_of_lt (hWlenPos e₀ he₀)))
      (Finset.le_sup' (f := heapCycleRatio C g ℓ) he₀)
  have hW_nonneg : 0 ≤ Wtot :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _
  by_cases hW0 : Wtot = 0
  · have hc0 : ∀ e ∈ G.E, c e = 0 := by
      intro e he
      have hw0_sum : (C.G 0).norm1 (C.chainW w 0) = 0 := by
        have hmem : 0 ∈ Finset.range (C.d + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
        have hle := Finset.single_le_sum (f := fun i => (C.G i).norm1 (C.chainW w i))
          (fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _) hmem
        have hge : 0 ≤ (C.G 0).norm1 (C.chainW w 0) := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      have he0 : e ∈ (C.G 0).E := hH.1.symm ▸ he
      have hwe0 : |C.chainW w 0 e| = 0 := by
        unfold MGraph.norm1 at hw0_sum
        have hle := Finset.single_le_sum (f := fun f => |C.chainW w 0 f|)
          (fun _ _ => abs_nonneg _) he0
        have hge : 0 ≤ |C.chainW w 0 e| := abs_nonneg _
        linarith
      have hw_e : w e = 0 := by simpa [TreeChain.chainW] using hwe0
      have hmul : |ℓ e * c e| = 0 := le_antisymm (hw_e ▸ hvp.2 e he) (abs_nonneg _)
      rcases mul_eq_zero.mp (abs_eq_zero.mp hmul) with hℓ0 | hc_e
      · exact absurd hℓ0 (ne_of_gt (hℓ_pos e he))
      · exact hc_e
    have hInner0 : G.inner g c = 0 := Finset.sum_eq_zero fun e he => by rw [hc0 e he, mul_zero]
    rw [hInner0, abs_zero, zero_div, mul_zero]
    exact hM_nonneg
  · have hW_pos : 0 < Wtot := lt_of_le_of_ne hW_nonneg (Ne.symm hW0)
    have hDecomp : G.inner g c =
        ∑ e ∈ S, C.chainC c (C.edgeLevel e) e * walkInner g (C.fundChainCycle e) := by
      unfold MGraph.inner
      have hcong : ∑ e₀ ∈ G.E, g e₀ * c e₀ =
          ∑ e₀ ∈ G.E, ∑ e ∈ S, g e₀ * (C.chainC c (C.edgeLevel e) e * walkFlow (C.fundChainCycle e) e₀) := by
        refine Finset.sum_congr rfl fun e₀ he₀ => ?_
        rw [C.lemma_7_15 hH hSub hSpan hEmbSurv hvp.1 e₀ he₀, Finset.mul_sum]
      rw [hcong, Finset.sum_comm]
      refine Finset.sum_congr rfl fun e he => ?_
      have he0 : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
      have hlvl := C.mem_activeCore_diff_edgeLevel hH he0
      have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hlvl.1 hlvl.2
      have hSubG : walkEdges (C.fundChainCycle e) ⊆ G.E :=
        hH.1 ▸ fun f hf => mem_E_of_mem_walkEdges hFundWalk hf
      rw [walkInner_eq_sum_of_subset hSubG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₀ _ => by ring
    have hNum : |G.inner g c| ≤ M * ((σ + 1) * Wtot) := by
      calc
        |G.inner g c|
            = |∑ e ∈ S, C.chainC c (C.edgeLevel e) e * walkInner g (C.fundChainCycle e)| :=
          congrArg abs hDecomp
        _ ≤ ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * |walkInner g (C.fundChainCycle e)| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact Finset.sum_le_sum fun e _ => (abs_mul _ _).le
        _ ≤ ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * (M * C.wlen ℓ e) := by
          refine Finset.sum_le_sum fun e he => ?_
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hdiv := Finset.le_sup' (f := heapCycleRatio C g ℓ) he
          unfold heapCycleRatio at hdiv
          dsimp only at hdiv
          rw [← hGradEq e he] at hdiv
          exact (div_le_iff₀ (hWlenPos e he)).mp hdiv
        _ = M * ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * C.wlen ℓ e := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ M * ((σ + 1) * Wtot) := by
          refine mul_le_mul_of_nonneg_left ?_ hM_nonneg
          have hEqLevels : ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * C.wlen ℓ e =
              ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
                |C.chainC c i e| * C.wlenAt ℓ i e := by
            change ∑ e ∈ G.E \ C.chainTree.E, _ = _
            rw [← hH.1]
            exact C.sum_offTree_eq_sum_levels hH hSub fun i e => |C.chainC c i e| * C.wlenAt ℓ i e
          rw [hEqLevels]
          exact C.lemma_A_2_sum_bound hH hSub hℓ hvp
    have hStep1 : |G.inner g c| / Wtot ≤ M * (σ + 1) :=
      (div_le_iff₀ hW_pos).mpr (by linarith [hNum])
    rw [one_div, inv_mul_le_iff₀ hσ_pos]
    linarith [hStep1]

private lemma walkEdges_stitchAux_sdiff_subset (G F : MGraph) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      walkEdges (TreeChain.stitchAux G F target x xs) \ F.E ⊆ walkEdges (x :: xs) := by
  intro xs
  induction xs with
  | nil =>
    intro x f hf
    simp only [TreeChain.stitchAux, walkEdges_append, Finset.mem_sdiff, Finset.mem_union] at hf
    rcases hf.1 with hx | hfp
    · exact hx
    · exact absurd (forestPath_edges_subset (G.dst x) target hfp) hf.2
  | cons y ys ih =>
    intro x f hf
    simp only [TreeChain.stitchAux, List.append_assoc, walkEdges_append, Finset.mem_sdiff,
      Finset.mem_union] at hf
    rcases hf.1 with hx | hfp | htail
    · simp only [walkEdges, List.mem_toFinset, List.mem_map, List.mem_cons] at hx ⊢
      rcases hx with ⟨z, rfl | hz, rfl⟩
      · exact ⟨z, Or.inl rfl, rfl⟩
      · cases hz
    · exact absurd (forestPath_edges_subset (G.dst x) (G.src y) hfp) hf.2
    · have hf' : f ∈ walkEdges (TreeChain.stitchAux G F target y ys) \ F.E :=
        Finset.mem_sdiff.mpr ⟨htail, hf.2⟩
      have hsub := ih y hf'
      simp only [walkEdges, List.mem_toFinset, List.mem_map, List.mem_cons] at hsub ⊢
      rcases hsub with ⟨z, hz, rfl⟩
      exact ⟨z, Or.inr hz, rfl⟩

private lemma walkEdges_stitchCycle_sdiff_card_le (G F : MGraph) (W : List (ℕ × Bool)) :
    (walkEdges (TreeChain.stitchCycle G F W) \ F.E).card ≤ W.length := by
  cases W with
  | nil => simp [TreeChain.stitchCycle, walkEdges]
  | cons x xs =>
    have hsub := walkEdges_stitchAux_sdiff_subset G F (G.src x) xs x
    refine le_trans (Finset.card_le_card hsub) ?_
    unfold walkEdges
    exact le_trans (List.toFinset_card_le _) (by simp)

/-- **Algorithm 1 `FindCycle` specification from tree-chain invariants**: if `st.toTreeChain`
satisfies `Holds`, `LastLevelSpans`, and `EmbedsSurviving` with `1 ≤ γ_ℓ`, then
`algorithm1_findCycle st` outputs a circulation `Δ` achieving the Lemma A.2 ratio bound and
represented by at most `1 + γ_ℓ` off-tree edges. -/
theorem findCycle_spec_of_holds {T : SparseCoreRestartTool} {P : ChainParams} (st : ChainState T P)
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hγ1 : 1 ≤ γ_ℓ)
    (hℓPos : ∀ e ∈ (st.G 0).E, 0 < st.ℓ e)
    (hH : st.toTreeChain.Holds (st.G 0) st.ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : st.toTreeChain.LastLevelSpans)
    (hEmbSurv : st.toTreeChain.EmbedsSurviving)
    {c w : ℕ → ℝ} (hvp : IsValidPair (st.G 0) st.ℓ c w) :
    let C := st.toTreeChain
    let (Δ, walk, optEdge) := algorithm1_findCycle st
    (st.G 0).IsCirculation Δ ∧
    (st.G 0).inner st.g Δ ≤ 0 ∧
    ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + γ_ℓ ∧
    (optEdge = none → Δ = 0 ∧ walk = [] ∧ (st.G 0).inner st.g c = 0) ∧
    (∀ e, optEdge = some e →
      e ∈ (st.G 0).E \ C.chainTree.E ∧
      0 < (st.G 0).lnorm st.ℓ Δ ∧
      (1 / (σ + 1)) *
          (|(st.G 0).inner st.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
        |(st.G 0).inner st.g Δ| / (st.G 0).lnorm st.ℓ Δ) := by
  have hSub := (st.toTreeChain).forestsAreSubgraphs_of_holds hH
  set C := st.toTreeChain
  set S := (st.G 0).E \ C.chainTree.E
  dsimp only [algorithm1_findCycle]
  by_cases hne : S.Nonempty
  · have hne' : ((st.G 0).E \ st.toTreeChain.chainTree.E).Nonempty := hne
    simp only [hne', ↓reduceDIte]
    set eBest := leastArgmax S (heapCycleRatio C st.g st.ℓ) hne
    have heBestSpec := leastArgmax_spec S (heapCycleRatio C st.g st.ℓ) hne
    have heBest : eBest ∈ S := heBestSpec.1
    set rawWalk := C.fundChainCycle eBest
    have heBest0 : eBest ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ heBest
    have hlvl := C.mem_activeCore_diff_edgeLevel hH heBest0
    have hRawClosed : (st.G 0).IsWalk ((st.G 0).tail eBest) ((st.G 0).tail eBest) rawWalk :=
      C.fundChainCycleAt_isClosedWalk hH hSub hSpan hlvl.1 hlvl.2
    have hLenPosRaw : 0 < walkLength st.ℓ rawWalk :=
      fundChainCycle_walkLength_pos C hH hSub hSpan hℓPos heBest
    have hCardRaw : ((walkEdges rawWalk \ C.chainTree.E).card : ℝ) ≤ 1 + γ_ℓ := by
      have hcardNat : (walkEdges rawWalk \ C.chainTree.E).card ≤
          (C.sparsifierCycle (C.edgeLevel eBest) eBest).length :=
        walkEdges_stitchCycle_sdiff_card_le (C.G 0) C.chainTree
          (C.sparsifierCycle (C.edgeLevel eBest) eBest)
      have hspLen : (C.sparsifierCycle (C.edgeLevel eBest) eBest).length =
          1 + (C.activeEmb (C.edgeLevel eBest) eBest).length := by
        simp [TreeChain.sparsifierCycle, walkRev, Nat.add_comm]
      have hEmbLen : ((C.activeEmb (C.edgeLevel eBest) eBest).length : ℝ) ≤ γ_ℓ := by
        by_cases hlt : C.edgeLevel eBest < C.d
        · have hSp := C.activeS_isSparsified hH hlt
          have heCore := (Finset.mem_sdiff.mp hlvl.2).1
          have hle : (C.activeEmb (C.edgeLevel eBest) eBest).length ≤
              (C.activeEmb (C.edgeLevel eBest)).length (C.activeCore (C.edgeLevel eBest)) := by
            unfold Embedding.length
            exact Finset.le_sup (f := fun e => (C.activeEmb (C.edgeLevel eBest) e).length) heCore
          have hle_real : ((C.activeEmb (C.edgeLevel eBest) eBest).length : ℝ) ≤ γ_ℓ :=
            le_trans (Nat.cast_le.mpr hle) hSp.2.2.2.1
          exact hle_real
        · have hieq : C.edgeLevel eBest = C.d := Nat.le_antisymm hlvl.1 (Nat.le_of_not_lt hlt)
          have hnil : C.activeEmb (C.edgeLevel eBest) eBest = [] := by
            rw [hieq]; simp [TreeChain.activeEmb]
          rw [hnil, List.length_nil, Nat.cast_zero]
          exact le_trans zero_le_one hγ1
      have hcard_real : ((walkEdges rawWalk \ C.chainTree.E).card : ℝ) ≤
          1 + ((C.activeEmb (C.edgeLevel eBest) eBest).length : ℝ) := by
        exact_mod_cast (hspLen ▸ hcardNat)
      linarith
    have hA2 := lemma_A_2_wlen C (g := st.g) hH hSub hSpan hEmbSurv hℓPos hvp hne
    have hSupLe : S.sup' hne (heapCycleRatio C st.g st.ℓ) ≤ heapCycleRatio C st.g st.ℓ eBest :=
      Finset.sup'_le hne _ fun e he => heBestSpec.2 e he
    have hKeyLeExact : heapCycleRatio C st.g st.ℓ eBest ≤ exactCycleRatio C st.g st.ℓ eBest :=
      heapCycleRatio_le_exactCycleRatio C hH hSub hSpan hℓPos heBest
    have hRatioBound :
        (1 / (σ + 1)) *
            (|(st.G 0).inner st.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
          exactCycleRatio C st.g st.ℓ eBest :=
      le_trans hA2 (le_trans hSupLe hKeyLeExact)
    by_cases hneg : walkInner st.g rawWalk ≤ 0
    · simp only [hneg, ↓reduceIte]
      have hSubG : walkEdges rawWalk ⊆ (st.G 0).E := fun f hf => mem_E_of_mem_walkEdges hRawClosed hf
      have hIn : (st.G 0).inner st.g (walkFlow rawWalk) = walkInner st.g rawWalk :=
        (walkInner_eq_sum_of_subset hSubG).symm
      have hLn : (st.G 0).lnorm st.ℓ (walkFlow rawWalk) = walkLength st.ℓ rawWalk :=
        (walkLength_eq_sum_of_subset hSubG).symm
      refine ⟨isCirculation_walkFlow_of_closed hRawClosed, hIn ▸ hneg, hCardRaw,
        (fun h => by cases h), fun e he => ?_⟩
      cases he
      rw [hIn, hLn]
      exact ⟨heBest, hLenPosRaw, hRatioBound⟩
    · simp only [hneg, ↓reduceIte]
      have hRevClosed : (st.G 0).IsWalk ((st.G 0).tail eBest) ((st.G 0).tail eBest) (walkRev rawWalk) :=
        MGraph.isWalk_walkRev hRawClosed
      have hSubG : walkEdges (walkRev rawWalk) ⊆ (st.G 0).E :=
        fun f hf => mem_E_of_mem_walkEdges hRevClosed hf
      have hIn : (st.G 0).inner st.g (walkFlow (walkRev rawWalk)) = walkInner st.g (walkRev rawWalk) :=
        (walkInner_eq_sum_of_subset hSubG).symm
      have hLn : (st.G 0).lnorm st.ℓ (walkFlow (walkRev rawWalk)) = walkLength st.ℓ (walkRev rawWalk) :=
        (walkLength_eq_sum_of_subset hSubG).symm
      have hCardRev : ((walkEdges (walkRev rawWalk) \ C.chainTree.E).card : ℝ) ≤ 1 + γ_ℓ := by
        rwa [walkEdges_walkRev]
      refine ⟨isCirculation_walkFlow_of_closed hRevClosed, ?_, hCardRev,
        (fun h => by cases h), fun e he => ?_⟩
      · rw [hIn, walkInner_walkRev]; linarith
      · cases he
        rw [hIn, hLn, walkInner_walkRev, abs_neg, walkLength_walkRev]
        exact ⟨heBest, hLenPosRaw, hRatioBound⟩
  · rw [dite_eq_right_iff.mpr (fun h => absurd h hne)]
    refine ⟨fun v _ => by simp [MGraph.demand], by simp [MGraph.inner], ?_, fun _ => ⟨rfl, rfl, ?_⟩,
      fun e h => nomatch h⟩
    · simp only [walkEdges, List.map_nil, List.toFinset_nil, Finset.empty_sdiff, Finset.card_empty,
        Nat.cast_zero]
      have h1 : 1 ≤ γ_ℓ := hγ1
      linarith
    · have hSubF : (st.G 0).E ⊆ C.chainTree.E := by
        intro e he
        by_contra hnot
        exact hne ⟨e, Finset.mem_sdiff.mpr ⟨he, hnot⟩⟩
      have hSubG : (st.G 0).IsSubgraph C.chainTree := C.chainTree_isSubgraph hH hSub
      have hEqE : C.chainTree.E = (st.G 0).E := Finset.Subset.antisymm hSubG.2.1 hSubF
      have hCircTree : C.chainTree.IsCirculation c := by
        intro v hv
        have hEqDem : C.chainTree.demand c v = (st.G 0).demand c v := by
          unfold MGraph.demand
          rw [hEqE]
          refine Finset.sum_congr rfl fun e he => ?_
          have hEnd := hSubG.2.2 e (hEqE ▸ he)
          simp only [MGraph.b, hEnd.1, hEnd.2]
        rw [hEqDem]
        exact hvp.1 v (hSubG.1 hv)
      have hc0 := MGraph.isCirculation_eq_zero_of_isForest (C.chainTree_isForest hH hSub) hCircTree
      unfold MGraph.inner
      exact Finset.sum_eq_zero fun e he => by rw [hc0 e (hSubF he), mul_zero]

/-- **Algorithm 1 `FindCycle` specification (Lemma 5.11, pages 20, 24)**:
for any state `st` satisfying `ChainInv`, `ToolMWU`, and `ToolEmbedsSurviving`, and any valid pair
`(c, w)` for `(st.G 0, st.ℓ)`, `algorithm1_findCycle st` returns `(Δ, walk, optEdge)` such that:
1. `Δ` is a circulation on `st.G 0` with `(st.G 0).inner st.g Δ ≤ 0` and
   `|(st.G 0).inner st.g Δ| = |walkInner st.g walk|` and `(st.G 0).lnorm st.ℓ Δ = walkLength st.ℓ walk`;
2. `walk` is a closed walk in `st.G 0` whose non-`T^𝒢` edges have cardinality at most `1 + TP.γ_ℓ (P.M₀ ^ 2)`
   (in fact `walk` is a `stitchCycle (st.G 0) C.chainTree` over a list of length at most `1 + TP.γ_ℓ (P.M₀ ^ 2)`);
3. if off-tree edges exist, `(st.G 0).lnorm st.ℓ Δ > 0` and the ratio `|⟨g, Δ⟩| / ‖ℓ ∘ Δ‖₁` is at
   least `(1 / (σ_tot + 1)) * |⟨g, c⟩| / ∑_{i=0}^d ‖w^{G_i}‖₁`; otherwise `Δ = 0` and
   `|(st.G 0).inner st.g c| = 0`. -/
theorem findCycle_spec_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hMWU : T.ToolMWURestartNoHidden σ_mwu)
    (hEmb : T.ToolEmbedsSurvivingRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {c w : ℕ → ℝ} (hvp : IsValidPair (st.G 0) st.ℓ c w) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let C := st.toTreeChain
    let (Δ, walk, optEdge) := algorithm1_findCycle st
    (st.G 0).IsCirculation Δ ∧
    (st.G 0).inner st.g Δ ≤ 0 ∧
    ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
    (optEdge = none → Δ = 0 ∧ walk = [] ∧ (st.G 0).inner st.g c = 0) ∧
    (∀ e, optEdge = some e →
      e ∈ (st.G 0).E \ C.chainTree.E ∧
      0 < (st.G 0).lnorm st.ℓ Δ ∧
      (1 / (σ_tot + 1)) *
          (|(st.G 0).inner st.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
        |(st.G 0).inner st.g Δ| / (st.G 0).lnorm st.ℓ Δ) := by
  have hTree := hInv.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP hT hMWU hEmb hγM₀ hγk
  exact findCycle_spec_of_holds st (hTP.2.2.1 (P.M₀ ^ 2)) hInv.hℓPos hTree.1 hTree.2.1 hTree.2.2 hvp

theorem findCycle_spec (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hMWU : T.ToolMWURestart σ_mwu)
    (hEmb : T.ToolEmbedsSurvivingRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {c w : ℕ → ℝ} (hvp : IsValidPair (st.G 0) st.ℓ c w) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let C := st.toTreeChain
    let (Δ, walk, optEdge) := algorithm1_findCycle st
    (st.G 0).IsCirculation Δ ∧
    (st.G 0).inner st.g Δ ≤ 0 ∧
    ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
    (optEdge = none → Δ = 0 ∧ walk = [] ∧ (st.G 0).inner st.g c = 0) ∧
    (∀ e, optEdge = some e →
      e ∈ (st.G 0).E \ C.chainTree.E ∧
      0 < (st.G 0).lnorm st.ℓ Δ ∧
      (1 / (σ_tot + 1)) *
          (|(st.G 0).inner st.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
        |(st.G 0).inner st.g Δ| / (st.G 0).lnorm st.ℓ Δ) :=
  findCycle_spec_noHidden T L TP LP P hσ_mwu_mono hTP hLP
    (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT) hMWU.toNoHidden hEmb.toNoHidden
    hγM₀ hγk hInv hvp

end FindCycleProofs

section LevelGraphSizes

/-- Non-isolated vertices of a multigraph `G`: vertices incident to at least one edge in `G.E`. -/
def nonIsolatedV (G : MGraph) : Finset ℕ :=
  open Classical in
  G.V.filter fun v => ∃ e ∈ G.E, G.tail e = v ∨ G.head e = v

lemma nonIsolatedV_card_le (G : MGraph) : (nonIsolatedV G).card ≤ 2 * G.m := by
  classical
  have hsub : nonIsolatedV G ⊆ G.E.image G.tail ∪ G.E.image G.head := by
    intro v hv
    rw [nonIsolatedV, Finset.mem_filter] at hv
    rcases hv.2 with ⟨e, he, hth | hth⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hth⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hth⟩)
  have h1 : (nonIsolatedV G).card ≤ (G.E.image G.tail ∪ G.E.image G.head).card :=
    Finset.card_le_card hsub
  have h2 : (G.E.image G.tail ∪ G.E.image G.head).card ≤
      (G.E.image G.tail).card + (G.E.image G.head).card := Finset.card_union_le _ _
  have h3 : (G.E.image G.tail).card ≤ G.E.card := Finset.card_image_le
  have h4 : (G.E.image G.head).card ≤ G.E.card := Finset.card_image_le
  unfold MGraph.m
  omega

/-- **Level graph size bounds (Lemma 5.11 proof, page 24)**: at every state satisfying `ChainInv`:
1. `|(st.G i).E| ≤ levelM TP P i` for all `i ≤ P.d`;
2. the non-isolated vertex count of `st.G i` is at most `2 * levelM TP P i`;
3. for `0 < i ≤ P.d`, if level `i - 1`'s `LevelHistory` base graph `H.D.G 0` is connected, then
   `|(st.G i).V| ≤ c_R * (2 * P.M₀ * γ_ℓ^i / k^i + 3)`. -/
theorem level_graph_size_bounds_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i ≤ P.d, ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
    (∀ i ≤ P.d, ((nonIsolatedV (st.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
    (∀ i, 0 < i → i ≤ P.d →
      ∀ H : LevelHistory T TP P N₀ st (i - 1),
        (∀ u ∈ (H.D.G 0).V, ∀ v ∈ (H.D.G 0).V, (H.D.G 0).Connected u v) →
        ((st.G i).n : ℝ) ≤ TP.c_R * (2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3)) := by
  have hLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  refine ⟨fun i hi => (hLev i hi).2.2.1, fun i hi => ?_, fun i hi0 hi H hConn => ?_⟩
  · have hni : ((nonIsolatedV (st.G i)).card : ℝ) ≤ 2 * ((st.G i).m : ℝ) := by
      exact_mod_cast nonIsolatedV_card_le (st.G i)
    linarith [(hLev i hi).2.2.1]
  · have hi_prev_lt : i - 1 < P.d := by omega
    have hi_prev_le : i - 1 ≤ P.d := Nat.le_of_lt hi_prev_lt
    have hSp := (hLev (i - 1) hi_prev_le).2.2.2.2 hi_prev_lt (st.bran (i - 1))
      (hInv.hBran (i - 1) hi_prev_lt)
    have hVsubR : (st.G i).V ⊆ (T.lsfs (st.scState (i - 1)) (st.bran (i - 1))).F.R := by
      have hGsucc := hInv.hGSucc (i - 1) hi_prev_lt
      rw [show i - 1 + 1 = i by omega] at hGsucc
      rw [hGsucc]
      exact hSp.2.1.1
    have hn_le_R : ((st.G i).n : ℝ) ≤ ((T.lsfs (st.scState (i - 1)) (st.bran (i - 1))).F.R.card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hVsubR
    have hSpec := hT P.k H.len (levelM TP P (i - 1)) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh)
    have hR := (hSpec.1 H.len (le_refl _) (st.bran (i - 1)) (hInv.hBran (i - 1) hi_prev_lt)).2.2 hConn
    dsimp only at hR
    rw [← H.hRun] at hR
    have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
    have hlog_pos : 0 < Real.log ((N₀ : ℝ) + 2) := log_add_two_pos _ (Nat.cast_nonneg _)
    have hsq_pos : 0 < (Real.log ((N₀ : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlog_pos
    have hUpdLog : (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
        (Real.log ((N₀ : ℝ) + 2)) ^ 2 ≤ (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) := by
      have hT' : (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) ≤
          (levelM TP P (i - 1) : ℝ) / ((P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 2) := by
        rw [H.hUpd]
        exact H.hThresh
      have h1 := mul_le_mul_of_nonneg_right hT' hsq_pos.le
      calc
        (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
            (Real.log ((N₀ : ℝ) + 2)) ^ 2
            ≤ (levelM TP P (i - 1) : ℝ) / ((P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 2) *
                (Real.log ((N₀ : ℝ) + 2)) ^ 2 := h1
        _ = (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) := by
          field_simp [hk_pos.ne', hsq_pos.ne']
    have hm0_lt := levelM_lt_add_one hTP P (i - 1)
    have hm0_div_k : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) ≤
        (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 1 := by
      have hdiv : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) ≤
          ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) + 1) / (P.k : ℝ) :=
        div_le_div_of_nonneg_right hm0_lt.le hk_pos.le
      have hk_pow : (P.k : ℝ) ^ i = (P.k : ℝ) ^ (i - 1) * (P.k : ℝ) := by
        rw [← pow_succ, show i - 1 + 1 = i by omega]
      have hγ_pow : (TP.γ_ℓ (P.M₀ ^ 2)) ^ i = (TP.γ_ℓ (P.M₀ ^ 2)) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (i - 1) := by
        rw [← pow_succ', show i - 1 + 1 = i by omega]
      have hpow_eq : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) =
          (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i := by
        rw [div_pow, hk_pow, hγ_pow]
        field_simp [hk_pos.ne']
      have hinvk : (1 : ℝ) / (P.k : ℝ) ≤ 1 := by
        rw [div_le_one hk_pos]
        exact_mod_cast P.hk
      linarith [add_div ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1)) 1 (P.k : ℝ)]
    have hcR : 0 ≤ TP.c_R := hTP.2.2.2.2.2.2.2.2.1
    refine le_trans hn_le_R (le_trans hR ?_)
    have hinner : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) +
          (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
            (Real.log ((N₀ : ℝ) + 2)) ^ 2 + 1 ≤
        2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3 := by
      have hdbl :
          (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i +
            (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i =
          2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i := by ring
      linarith [hm0_div_k, hUpdLog, hdbl]
    exact mul_le_mul_of_nonneg_left hinner hcR

theorem level_graph_size_bounds (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestart TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i ≤ P.d, ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
    (∀ i ≤ P.d, ((nonIsolatedV (st.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
    (∀ i, 0 < i → i ≤ P.d →
      ∀ H : LevelHistory T TP P N₀ st (i - 1),
        (∀ u ∈ (H.D.G 0).V, ∀ v ∈ (H.D.G 0).V, (H.D.G 0).Connected u v) →
        ((st.G i).n : ℝ) ≤ TP.c_R * (2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3)) :=
  level_graph_size_bounds_noHidden T L TP LP P hTP (SparseCoreRestartTool.IsSpecRestart.toNoHidden hT)
    hγM₀ hγk hInv

end LevelGraphSizes

end MinCostFlow.Chain
