module

public import MinCostFlow.LSF.Tools
public import MinCostFlow.LSF.Components
public import MinCostFlow.LSF.Congestion
public import MinCostFlow.LSF.LemmaB7
public import MinCostFlow.Basic.Dynamic
public import MinCostFlow.Basic.LSF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Model of the Dynamic Low-Stretch Forest (Lemma 5.4, Appendix A.1)

This file formalizes the data structures and update procedure of Lemma 5.4 (page 17) and its
proof in Appendix A.1 (page 48), adapting `[chen2022maximum, Lemma 6.5]` (`[chen2022maximum]`,
Appendix B.3, lines 194–238):

* Weighted copy multigraph `G_v` (`weightedCopyGraph`) with `⌈m v_e / ‖v‖₁⌉` copies of each edge
  `e ∈ E(G)` and safe length function `safeLen`.
* Projection `projectTree` of a spanning tree `T_raw` computed on `G_v` back onto `G₀` so that
  non-bridge edges of `T_raw` keep their original edge names in `G₀.E`.
* Auxiliary tree `T_H = hldAuxTree T₀ r₀`, congestion ordering `π = congOrder T₀ G_v ℓ_v`, level
  sets `B_i = levelRoots T₀ r₀ i`, and raw stretch overestimates `(B.3)` `levelStretchBound` capped
  at `1` on high-stretch edges whose endpoints are added to `R₀`.
* Tree decomposition `𝒲^T` from `lemma_B_7` with uniform weights `1` and parameter
  `k * (hldDepthBound n + 1)`, refined by connected components of `F₀` (`refineDecomp`).
* Dynamic state `LSFState` and update transition `applyLSFUpdate` supporting `.insert`, `.delete`,
  and `.split` (Appendix A.1: creating an isolated vertex `v'` in `T` and adding `v'` and
  `v^{↑ T_H}` to the root set `R`).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Weighted copy multigraph `G_v` -/

/-- Modulus strictly above all edge identifiers of `G`, used to name copies `e + M * j` without
collision while keeping copy `0` equal to `e`. -/
def copyMod (G : MGraph) : ℕ :=
  G.E.sup id + 1

/-- Identifier of copy `j` of edge `e`. When `j = 0`, this equals `e`. -/
def copyId (M e j : ℕ) : ℕ :=
  e + M * j

/-- Original edge of `G` corresponding to copy identifier `e'`. -/
def origEdge (M e' : ℕ) : ℕ :=
  e' % M

lemma copyMod_pos (G : MGraph) : 0 < copyMod G :=
  Nat.succ_pos _

lemma lt_copyMod {G : MGraph} {e : ℕ} (he : e ∈ G.E) : e < copyMod G :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) he)

lemma origEdge_copyId {G : MGraph} {e j : ℕ} (he : e ∈ G.E) :
    origEdge (copyMod G) (copyId (copyMod G) e j) = e := by
  unfold origEdge copyId
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_copyMod he)]

lemma copyId_inj {G : MGraph} {e₁ e₂ j₁ j₂ : ℕ} (he₁ : e₁ ∈ G.E) (he₂ : e₂ ∈ G.E)
    (hEq : copyId (copyMod G) e₁ j₁ = copyId (copyMod G) e₂ j₂) :
    e₁ = e₂ ∧ j₁ = j₂ := by
  have he_eq : e₁ = e₂ := by
    have h1 := congrArg (origEdge (copyMod G)) hEq
    rwa [origEdge_copyId he₁, origEdge_copyId he₂] at h1
  refine ⟨he_eq, ?_⟩
  subst he_eq
  unfold copyId at hEq
  have hj : copyMod G * j₁ = copyMod G * j₂ := by omega
  exact Nat.eq_of_mul_eq_mul_left (copyMod_pos G) hj

/-- Edge multiplicity `⌈m v_e / ‖v‖₁⌉` in `G_v` (`[chen2022maximum, Appendix B.3]`). -/
noncomputable def edgeMult (G : MGraph) (v : ℕ → ℝ) (e : ℕ) : ℕ :=
  Nat.ceil ((G.E.card : ℝ) * v e / G.norm1 v)

/-- The unweighted multigraph `G_v` obtained from `G` by replacing each edge `e ∈ G.E` with
`⌈m v_e / ‖v‖₁⌉` parallel copies (`[chen2022maximum, Appendix B.3]`). When `G.E = ∅`, this
returns `G`. -/
noncomputable def weightedCopyGraph (G : MGraph) (v : ℕ → ℝ) : MGraph :=
  if G.E.Nonempty then
    let M := copyMod G
    { V := G.V
      E := G.E.biUnion (fun e => (Finset.range (edgeMult G v e)).image (copyId M e))
      tail := fun e' => G.tail (origEdge M e')
      head := fun e' => G.head (origEdge M e') }
  else
    G

/-- Copy lengths on `G_v`: every copy of `e` inherits length `ℓ e`. -/
def weightedCopyLen (G : MGraph) (ℓ : ℕ → ℝ) (e' : ℕ) : ℝ :=
  ℓ (origEdge (copyMod G) e')

/-- Safe lengths agreeing with `ℓ` on `G.E` and `0` elsewhere, used so bridge edges outside
`G.E` never receive unconstrained caller lengths. -/
noncomputable def safeLen (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  open Classical in
  if e ∈ G.E then ℓ e else 0

lemma safeLen_eq_of_mem {G : MGraph} (ℓ : ℕ → ℝ) {e : ℕ} (he : e ∈ G.E) :
    safeLen G ℓ e = ℓ e := by
  unfold safeLen
  exact ite_eq_left_iff.mpr (fun h => absurd he h)

lemma safeLen_nonneg {G : MGraph} {ℓ : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (e : ℕ) :
    0 ≤ safeLen G ℓ e := by
  unfold safeLen
  split_ifs with he
  · exact le_of_lt (hℓ e he)
  · exact le_rfl

lemma edgeMult_pos {G : MGraph} (hE : G.E.Nonempty) {v : ℕ → ℝ}
    (hv : ∀ e ∈ G.E, 0 < v e) {e : ℕ} (he : e ∈ G.E) :
    1 ≤ edgeMult G v e := by
  unfold edgeMult
  have hm : (0 : ℝ) < (G.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
  have hnorm : 0 < G.norm1 v := by
    unfold MGraph.norm1
    refine Finset.sum_pos (fun f hf => abs_pos.mpr (ne_of_gt (hv f hf))) hE
  have hpos : 0 < (G.E.card : ℝ) * v e / G.norm1 v := div_pos (mul_pos hm (hv e he)) hnorm
  exact Nat.ceil_pos.mpr hpos

lemma norm1_eq_sum_pos {G : MGraph} {v : ℕ → ℝ} (hv : ∀ e ∈ G.E, 0 < v e) :
    G.norm1 v = ∑ e ∈ G.E, v e := by
  unfold MGraph.norm1
  refine Finset.sum_congr rfl (fun e he => abs_of_pos (hv e he))

lemma weightedCopyGraph_V (G : MGraph) (v : ℕ → ℝ) :
    (weightedCopyGraph G v).V = G.V := by
  unfold weightedCopyGraph
  split_ifs <;> rfl

lemma mem_weightedCopyGraph_E_iff {G : MGraph} (hE : G.E.Nonempty) {v : ℕ → ℝ} {e' : ℕ} :
    e' ∈ (weightedCopyGraph G v).E ↔
      ∃ e ∈ G.E, ∃ j < edgeMult G v e, copyId (copyMod G) e j = e' := by
  unfold weightedCopyGraph
  rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]

lemma weightedCopyGraph_isValid {G : MGraph} (hG : G.IsValid) (v : ℕ → ℝ) :
    (weightedCopyGraph G v).IsValid := by
  by_cases hE : G.E.Nonempty
  · intro e' he'
    rw [mem_weightedCopyGraph_E_iff hE] at he'
    obtain ⟨e, heG, j, _, rfl⟩ := he'
    rw [weightedCopyGraph_V]
    unfold weightedCopyGraph
    rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
    dsimp only
    rw [origEdge_copyId heG]
    exact hG e heG
  · unfold weightedCopyGraph
    rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
    exact hG

lemma weightedCopyGraph_tail_copyId {G : MGraph} (hE : G.E.Nonempty) {v : ℕ → ℝ}
    {e j : ℕ} (he : e ∈ G.E) :
    (weightedCopyGraph G v).tail (copyId (copyMod G) e j) = G.tail e := by
  unfold weightedCopyGraph
  rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
  exact congrArg G.tail (origEdge_copyId he)

lemma weightedCopyGraph_head_copyId {G : MGraph} (hE : G.E.Nonempty) {v : ℕ → ℝ}
    {e j : ℕ} (he : e ∈ G.E) :
    (weightedCopyGraph G v).head (copyId (copyMod G) e j) = G.head e := by
  unfold weightedCopyGraph
  rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
  exact congrArg G.head (origEdge_copyId he)

lemma weightedCopyGraph_origEdge_mem {G : MGraph} (hE : G.E.Nonempty) {v : ℕ → ℝ}
    {e' : ℕ} (he' : e' ∈ (weightedCopyGraph G v).E) :
    origEdge (copyMod G) e' ∈ G.E ∧
      (weightedCopyGraph G v).tail e' = G.tail (origEdge (copyMod G) e') ∧
      (weightedCopyGraph G v).head e' = G.head (origEdge (copyMod G) e') := by
  rw [mem_weightedCopyGraph_E_iff hE] at he'
  obtain ⟨e, he, _, _, rfl⟩ := he'
  rw [origEdge_copyId he]
  exact ⟨he, weightedCopyGraph_tail_copyId hE he, weightedCopyGraph_head_copyId hE he⟩

lemma weightedCopyLen_pos {G : MGraph} (hE : G.E.Nonempty) {ℓ v : ℕ → ℝ}
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) {e' : ℕ} (he' : e' ∈ (weightedCopyGraph G v).E) :
    0 < weightedCopyLen G ℓ e' := by
  unfold weightedCopyLen
  exact hℓ _ (weightedCopyGraph_origEdge_mem hE he').1

lemma weightedCopyGraph_subgraph {G : MGraph} {v : ℕ → ℝ} (hv : ∀ e ∈ G.E, 0 < v e) :
    G.V ⊆ (weightedCopyGraph G v).V ∧ G.E ⊆ (weightedCopyGraph G v).E ∧
      ∀ e ∈ G.E, G.tail e = (weightedCopyGraph G v).tail e ∧
        G.head e = (weightedCopyGraph G v).head e := by
  by_cases hE : G.E.Nonempty
  · refine ⟨(weightedCopyGraph_V G v).symm.subset, ?_, ?_⟩
    · intro e he
      rw [mem_weightedCopyGraph_E_iff hE]
      refine ⟨e, he, 0, edgeMult_pos hE hv he, ?_⟩
      simp [copyId]
    · intro e he
      have h0 : copyId (copyMod G) e 0 = e := by simp [copyId]
      rw [← h0, weightedCopyGraph_tail_copyId hE he, weightedCopyGraph_head_copyId hE he]
      exact ⟨rfl, rfl⟩
  · unfold weightedCopyGraph
    rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩

lemma weightedCopyGraph_sum_eq {G : MGraph} (hE : G.E.Nonempty) (v : ℕ → ℝ) (F : ℕ → ℝ) :
    ∑ e' ∈ (weightedCopyGraph G v).E, F (origEdge (copyMod G) e') =
      ∑ e ∈ G.E, (edgeMult G v e : ℝ) * F e := by
  classical
  unfold weightedCopyGraph
  rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
  dsimp only
  have hdisj : Set.PairwiseDisjoint (↑G.E : Set ℕ)
      (fun e => (Finset.range (edgeMult G v e)).image (copyId (copyMod G) e)) := by
    intro e₁ he₁ e₂ he₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e' h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨j₁, _, rfl⟩ := h1
    obtain ⟨j₂, _, hEq⟩ := h2
    exact hne (copyId_inj he₂ he₁ hEq).1.symm
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hinj : Set.InjOn (copyId (copyMod G) e) ↑(Finset.range (edgeMult G v e)) :=
    fun j₁ _ j₂ _ hEq => (copyId_inj he he hEq).2
  rw [Finset.sum_image hinj]
  have hconst : ∑ j ∈ Finset.range (edgeMult G v e), F (origEdge (copyMod G) (copyId (copyMod G) e j)) =
      ∑ _j ∈ Finset.range (edgeMult G v e), F e :=
    Finset.sum_congr rfl (fun j _ => congrArg F (origEdge_copyId he))
  rw [hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma weightedCopyGraph_card_le {G : MGraph} {v : ℕ → ℝ} (hv : ∀ e ∈ G.E, 0 < v e) :
    ((weightedCopyGraph G v).E.card : ℝ) ≤ 2 * (G.E.card : ℝ) := by
  by_cases hE : G.E.Nonempty
  · have hsum_one := weightedCopyGraph_sum_eq hE v (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at hsum_one
    have hnorm : 0 < G.norm1 v := by
      unfold MGraph.norm1
      exact Finset.sum_pos (fun f hf => abs_pos.mpr (ne_of_gt (hv f hf))) hE
    have hceil : ∀ e ∈ G.E, (edgeMult G v e : ℝ) ≤ (G.E.card : ℝ) * v e / G.norm1 v + 1 := by
      intro e he
      unfold edgeMult
      exact le_of_lt (Nat.ceil_lt_add_one
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hv e he))) (le_of_lt hnorm)))
    have hle := Finset.sum_le_sum hceil
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hle
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum] at hle
    rw [← norm1_eq_sum_pos hv, mul_assoc (G.E.card : ℝ),
      mul_inv_cancel₀ (ne_of_gt hnorm), mul_one] at hle
    linarith
  · unfold weightedCopyGraph
    rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
    linarith [show (0 : ℝ) ≤ (G.E.card : ℝ) by positivity]

/-! ## Edge-relabeling projection of `T_raw` back onto `G₀` -/

/-- Relabeling map on `T_raw.E` sending copies of `G₀.E` to their original edge identifier in
`G₀.E` and shifting any bridge edges outside `G_v.E` strictly above all identifiers in `G₀.E`. -/
noncomputable def projectEdge (G₀ : MGraph) (v : ℕ → ℝ) (f : ℕ) : ℕ :=
  open Classical in
  if f ∈ (weightedCopyGraph G₀ v).E then origEdge (copyMod G₀) f else f + copyMod G₀

/-- Tree obtained from `T_raw` by projecting edges in `T_raw.E ∩ G_v.E` to their original edge
identifiers in `G₀.E`. -/
noncomputable def projectTree (G₀ : MGraph) (v : ℕ → ℝ) (T_raw : MGraph) : MGraph :=
  open Classical in
  if G₀.E.Nonempty then
    let M := copyMod G₀
    { V := T_raw.V
      E := T_raw.E.image (projectEdge G₀ v)
      tail := fun f' => if f' ∈ G₀.E then G₀.tail f' else T_raw.tail (f' - M)
      head := fun f' => if f' ∈ G₀.E then G₀.head f' else T_raw.head (f' - M) }
  else
    T_raw

private lemma projectTree_edge_corresp {G₀ T_raw : MGraph} {v : ℕ → ℝ}
    (hE : G₀.E.Nonempty) (hT_forest : T_raw.IsForest)
    (hTG_edges : ∀ f ∈ T_raw.E, f ∈ (weightedCopyGraph G₀ v).E →
      T_raw.tail f = (weightedCopyGraph G₀ v).tail f ∧
        T_raw.head f = (weightedCopyGraph G₀ v).head f) :
    let T₀ := projectTree G₀ v T_raw
    (∀ f₁ ∈ T_raw.E, ∀ f₂ ∈ T_raw.E, projectEdge G₀ v f₁ = projectEdge G₀ v f₂ → f₁ = f₂) ∧
    (∀ f ∈ T_raw.E, projectEdge G₀ v f ∈ T₀.E ∧
      T₀.tail (projectEdge G₀ v f) = T_raw.tail f ∧
      T₀.head (projectEdge G₀ v f) = T_raw.head f) ∧
    (∀ f' ∈ T₀.E, f' ∈ G₀.E → T₀.tail f' = G₀.tail f' ∧ T₀.head f' = G₀.head f') := by
  classical
  dsimp only
  have hinj : ∀ f₁ ∈ T_raw.E, ∀ f₂ ∈ T_raw.E,
      projectEdge G₀ v f₁ = projectEdge G₀ v f₂ → f₁ = f₂ := by
    intro f₁ hf₁ f₂ hf₂ hEq
    unfold projectEdge at hEq
    by_cases h1 : f₁ ∈ (weightedCopyGraph G₀ v).E <;> by_cases h2 : f₂ ∈ (weightedCopyGraph G₀ v).E
    · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), ite_eq_left_iff.mpr (fun h => absurd h2 h)] at hEq
      by_contra hne
      have h1e := weightedCopyGraph_origEdge_mem hE h1
      have h2e := weightedCopyGraph_origEdge_mem hE h2
      have ht1 := hTG_edges f₁ hf₁ h1
      have ht2 := hTG_edges f₂ hf₂ h2
      have hsame_t : T_raw.tail f₁ = T_raw.tail f₂ := by
        rw [ht1.1, h1e.2.1, hEq, ← h2e.2.1, ← ht2.1]
      have hsame_h : T_raw.head f₁ = T_raw.head f₂ := by
        rw [ht1.2, h1e.2.2, hEq, ← h2e.2.2, ← ht2.2]
      have hwalk : T_raw.IsWalk (T_raw.tail f₁) (T_raw.tail f₁) [(f₁, true), (f₂, false)] :=
        .cons (x := (f₁, true)) hf₁ rfl
          (.cons (x := (f₂, false)) hf₂ hsame_h.symm (hsame_t.symm ▸ .nil (T_raw.tail f₂)))
      have hcyc : T_raw.IsCycle [(f₁, true), (f₂, false)] := by
        refine ⟨by simp, ?_, T_raw.tail f₁, hwalk⟩
        simp [hne]
      exact hT_forest.2 _ hcyc
    · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), ite_eq_right_iff.mpr (fun h => absurd h h2)] at hEq
      have hlt := lt_copyMod (weightedCopyGraph_origEdge_mem hE h1).1
      omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_left_iff.mpr (fun h => absurd h2 h)] at hEq
      have hlt := lt_copyMod (weightedCopyGraph_origEdge_mem hE h2).1
      omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2)] at hEq
      omega
  have hmap : ∀ f ∈ T_raw.E, projectEdge G₀ v f ∈ (projectTree G₀ v T_raw).E ∧
      (projectTree G₀ v T_raw).tail (projectEdge G₀ v f) = T_raw.tail f ∧
      (projectTree G₀ v T_raw).head (projectEdge G₀ v f) = T_raw.head f := by
    intro f hf
    unfold projectTree
    rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
    dsimp only
    refine ⟨Finset.mem_image_of_mem _ hf, ?_⟩
    unfold projectEdge
    by_cases hfv : f ∈ (weightedCopyGraph G₀ v).E
    · rw [ite_eq_left_iff.mpr (fun h => absurd hfv h)]
      have hmem := weightedCopyGraph_origEdge_mem hE hfv
      simp only [hmem.1, ↓reduceIte]
      have ht := hTG_edges f hf hfv
      exact ⟨(ht.1.trans hmem.2.1).symm, (ht.2.trans hmem.2.2).symm⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hfv)]
      have hnot : f + copyMod G₀ ∉ G₀.E := fun h => by
        have hlt := lt_copyMod h; omega
      simp only [hnot, ↓reduceIte, Nat.add_sub_cancel]
      exact ⟨trivial, trivial⟩
  have hG : ∀ f' ∈ (projectTree G₀ v T_raw).E, f' ∈ G₀.E →
      (projectTree G₀ v T_raw).tail f' = G₀.tail f' ∧
        (projectTree G₀ v T_raw).head f' = G₀.head f' := by
    intro f' _ hf'G
    unfold projectTree
    rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
    dsimp only
    simp only [hf'G, ↓reduceIte]
    exact ⟨trivial, trivial⟩
  exact ⟨hinj, hmap, hG⟩

private lemma projectTree_isWalk_map {G₀ T_raw : MGraph} {v : ℕ → ℝ}
    (hE : G₀.E.Nonempty) (hT_forest : T_raw.IsForest)
    (hTG_edges : ∀ f ∈ T_raw.E, f ∈ (weightedCopyGraph G₀ v).E →
      T_raw.tail f = (weightedCopyGraph G₀ v).tail f ∧
        T_raw.head f = (weightedCopyGraph G₀ v).head f) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, T_raw.IsWalk a b P →
      (projectTree G₀ v T_raw).IsWalk a b (P.map (fun x => (projectEdge G₀ v x.1, x.2))) ∧
        (projectTree G₀ v T_raw).walkVertices a (P.map (fun x => (projectEdge G₀ v x.1, x.2))) =
          T_raw.walkVertices a P := by
  have ⟨_, hmap, _⟩ := projectTree_edge_corresp hE hT_forest hTG_edges
  intro a b P hW
  induction hW with
  | nil u => exact ⟨.nil u, rfl⟩
  | @cons u w x xs hxE hsrc _ ih =>
    have hm := hmap x.1 hxE
    have hsrc' : (projectTree G₀ v T_raw).src (projectEdge G₀ v x.1, x.2) = u := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.src] at hsrc ⊢
      · rw [hm.2.2]; exact hsrc
      · rw [hm.2.1]; exact hsrc
    have hdst' : (projectTree G₀ v T_raw).dst (projectEdge G₀ v x.1, x.2) = T_raw.dst x := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst]
      · exact hm.2.1
      · exact hm.2.2
    refine ⟨.cons hm.1 hsrc' (hdst'.symm ▸ ih.1), ?_⟩
    rw [List.map_cons, MGraph.walkVertices, MGraph.walkVertices, List.map_cons, hdst']
    congr 1
    simpa [MGraph.walkVertices] using ih.2

private lemma projectTree_isWalk_unmap {G₀ T_raw : MGraph} {v : ℕ → ℝ}
    (hE : G₀.E.Nonempty) (hT_forest : T_raw.IsForest)
    (hTG_edges : ∀ f ∈ T_raw.E, f ∈ (weightedCopyGraph G₀ v).E →
      T_raw.tail f = (weightedCopyGraph G₀ v).tail f ∧
        T_raw.head f = (weightedCopyGraph G₀ v).head f) :
    ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, (projectTree G₀ v T_raw).IsWalk a b Q →
      ∃ P : List (ℕ × Bool), T_raw.IsWalk a b P ∧
        Q = P.map (fun x => (projectEdge G₀ v x.1, x.2)) := by
  have ⟨_, hmap, _⟩ := projectTree_edge_corresp hE hT_forest hTG_edges
  intro a b Q hW
  induction hW with
  | nil u => exact ⟨[], .nil u, rfl⟩
  | @cons u w y ys hyE hsrc _ ih =>
    have hyE' : y.1 ∈ (projectTree G₀ v T_raw).E := hyE
    unfold projectTree at hyE'
    rw [ite_eq_left_iff.mpr (fun h => absurd hE h)] at hyE'
    obtain ⟨f, hfT, hfEq⟩ := Finset.mem_image.mp hyE'
    have hm := hmap f hfT
    have hsrc' : T_raw.src (f, y.2) = u := by
      rcases y with ⟨f', b⟩
      cases b <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢ <;>
        dsimp only at hfEq
      · rw [← hfEq, hm.2.2] at hsrc; exact hsrc
      · rw [← hfEq, hm.2.1] at hsrc; exact hsrc
    have hdst' : T_raw.dst (f, y.2) = (projectTree G₀ v T_raw).dst y := by
      rcases y with ⟨f', b⟩
      cases b <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] <;>
        dsimp only at hfEq
      · rw [← hfEq, hm.2.1]
      · rw [← hfEq, hm.2.2]
    obtain ⟨P, hWP, hQ⟩ := ih
    refine ⟨(f, y.2) :: P, .cons hfT hsrc' (hdst'.symm ▸ hWP), ?_⟩
    rw [List.map_cons, hQ]
    congr 1
    ext <;> simp [hfEq]

lemma projectTree_isLSST {G₀ T_raw : MGraph} {v ℓ : ℕ → ℝ} {γ : ℝ}
    (hG₀ : G₀.IsValid) (_hℓ : ∀ e ∈ G₀.E, 0 < ℓ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    (hlsst : IsLSST (weightedCopyGraph G₀ v) (weightedCopyLen G₀ ℓ) (fun _ => 1) γ T_raw) :
    let T₀ := projectTree G₀ v T_raw
    T₀.IsSpanningTreeOn G₀.V ∧
    (∀ f ∈ T₀.E, f ∈ G₀.E → T₀.tail f = G₀.tail f ∧ T₀.head f = G₀.head f) ∧
    (∀ e ∈ G₀.E, walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) ⊆ G₀.E) ∧
    (∀ e' ∈ (weightedCopyGraph G₀ v).E,
      walkEdges (T₀.forestPath ((weightedCopyGraph G₀ v).tail e')
        ((weightedCopyGraph G₀ v).head e')) ⊆ (weightedCopyGraph G₀ v).E) ∧
    (∀ e' ∈ (weightedCopyGraph G₀ v).E,
      treeStretch (weightedCopyGraph G₀ v) T₀ (weightedCopyLen G₀ ℓ) e' =
        treeStretch (weightedCopyGraph G₀ v) T_raw (weightedCopyLen G₀ ℓ) e') ∧
    ∑ e' ∈ (weightedCopyGraph G₀ v).E,
      treeStretch (weightedCopyGraph G₀ v) T₀ (weightedCopyLen G₀ ℓ) e' ≤
        γ * ((weightedCopyGraph G₀ v).E.card : ℝ) := by
  classical
  by_cases hE : G₀.E.Nonempty
  · have hGV : (weightedCopyGraph G₀ v).V = G₀.V := weightedCopyGraph_V G₀ v
    have hsubG := weightedCopyGraph_subgraph hv
    have hst_raw := hlsst.1
    have hTG_raw := hlsst.2.1
    have hpaths_raw := hlsst.2.2.1
    have hsum_raw := hlsst.2.2.2
    have hnorm1_one : (weightedCopyGraph G₀ v).norm1 (fun _ => (1 : ℝ)) =
        ((weightedCopyGraph G₀ v).E.card : ℝ) := by
      unfold MGraph.norm1
      simp only [abs_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hnorm1_one] at hsum_raw
    have ⟨hinj, hmap, hG⟩ := projectTree_edge_corresp hE hst_raw.1 hTG_raw
    let T₀ := projectTree G₀ v T_raw
    have hT₀_V : T₀.V = G₀.V := by
      dsimp only [T₀, projectTree]
      rw [ite_eq_left_iff.mpr (fun h => absurd hE h)]
      exact hGV ▸ hst_raw.2.1
    have hT₀_valid : T₀.IsValid := by
      intro f' hf'
      dsimp only [T₀] at hf'
      have hf'' := hf'
      unfold projectTree at hf''
      rw [ite_eq_left_iff.mpr (fun h => absurd hE h)] at hf''
      obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hf''
      have hm := hmap f hfT
      have huv := hst_raw.1.1 f hfT
      rw [hm.2.1, hm.2.2, hT₀_V, ← hGV, ← hst_raw.2.1]
      exact huv
    have hT₀_nocyc : ∀ Q, ¬ T₀.IsCycle Q := by
      rintro Q ⟨hQne, hQnd, u, hWQ⟩
      obtain ⟨P, hWP, rfl⟩ := projectTree_isWalk_unmap hE hst_raw.1 hTG_raw hWQ
      have hPne : P ≠ [] := fun h => hQne (by simp [h])
      have hPnd : (P.map Prod.fst).Nodup := by
        have hEq_map : (P.map (fun x => (projectEdge G₀ v x.1, x.2))).map Prod.fst =
            (P.map Prod.fst).map (projectEdge G₀ v) := by
          simp [List.map_map, Function.comp_def]
        rw [hEq_map] at hQnd
        exact List.Nodup.of_map (projectEdge G₀ v) hQnd
      exact hst_raw.1.2 P ⟨hPne, hPnd, u, hWP⟩
    have hT₀_st : T₀.IsSpanningTreeOn G₀.V := by
      refine ⟨⟨hT₀_valid, hT₀_nocyc⟩, hT₀_V, fun u hu w hw => ?_⟩
      obtain ⟨P, hWP⟩ := hst_raw.2.2 u (hGV ▸ hu) w (hGV ▸ hw)
      exact ⟨_, (projectTree_isWalk_map hE hst_raw.1 hTG_raw hWP).1⟩
    have hfp_map : ∀ {u w : ℕ}, u ∈ G₀.V → w ∈ G₀.V →
        T₀.forestPath u w = (T_raw.forestPath u w).map (fun x => (projectEdge G₀ v x.1, x.2)) := by
      intro u w hu hw
      have hP := forestPath_isPath hst_raw.1 (hst_raw.2.2 u (hGV ▸ hu) w (hGV ▸ hw))
      have hm := projectTree_isWalk_map hE hst_raw.1 hTG_raw hP.1
      have hQ_path : T₀.IsPath u w ((T_raw.forestPath u w).map (fun x => (projectEdge G₀ v x.1, x.2))) :=
        ⟨hm.1, hm.2 ▸ hP.2⟩
      exact forestPath_eq_of_isPath hT₀_st.1 hQ_path
    have hstretch_eq : ∀ e' ∈ (weightedCopyGraph G₀ v).E,
        treeStretch (weightedCopyGraph G₀ v) T₀ (weightedCopyLen G₀ ℓ) e' =
          treeStretch (weightedCopyGraph G₀ v) T_raw (weightedCopyLen G₀ ℓ) e' := by
      intro e' he'
      have huw := weightedCopyGraph_isValid hG₀ v e' he'
      rw [weightedCopyGraph_V] at huw
      have hP_raw := forestPath_isPath hst_raw.1
        (hst_raw.2.2 ((weightedCopyGraph G₀ v).tail e') (hGV ▸ huw.1)
          ((weightedCopyGraph G₀ v).head e') (hGV ▸ huw.2))
      have hP_T₀ := forestPath_isPath hT₀_st.1 (hT₀_st.2.2 _ huw.1 _ huw.2)
      unfold treeStretch
      rw [walkLength_eq_sum_of_isPath _ hP_T₀, walkLength_eq_sum_of_isPath _ hP_raw,
        hfp_map huw.1 huw.2]
      have hWE_img : walkEdges ((T_raw.forestPath ((weightedCopyGraph G₀ v).tail e')
            ((weightedCopyGraph G₀ v).head e')).map (fun x => (projectEdge G₀ v x.1, x.2))) =
          (walkEdges (T_raw.forestPath ((weightedCopyGraph G₀ v).tail e')
            ((weightedCopyGraph G₀ v).head e'))).image (projectEdge G₀ v) := by
        apply Finset.ext
        intro z
        simp only [walkEdges, List.map_map, Function.comp_def, List.mem_toFinset, List.mem_map,
          Finset.mem_image]
        exact ⟨fun ⟨a, ha, hz⟩ => ⟨a.1, ⟨a, ha, rfl⟩, hz⟩,
          fun ⟨f, ⟨a, ha, hfa⟩, hz⟩ => ⟨a, ha, hfa ▸ hz⟩⟩
      rw [hWE_img, Finset.sum_image]
      · congr 2
        refine Finset.sum_congr rfl (fun f hf => ?_)
        have hfGv : f ∈ (weightedCopyGraph G₀ v).E := hpaths_raw e' he' f hf
        unfold projectEdge
        rw [ite_eq_left_iff.mpr (fun h => absurd hfGv h)]
        unfold weightedCopyLen origEdge
        rw [Nat.mod_mod]
      · intro f₁ hf₁ f₂ hf₂ hEq
        have hf₁T : f₁ ∈ T_raw.E := by
          rw [Finset.mem_coe, walkEdges, List.mem_toFinset, List.mem_map] at hf₁
          obtain ⟨x, hx, rfl⟩ := hf₁
          exact IsWalk_edges_mem hP_raw.1 hx
        have hf₂T : f₂ ∈ T_raw.E := by
          rw [Finset.mem_coe, walkEdges, List.mem_toFinset, List.mem_map] at hf₂
          obtain ⟨x, hx, rfl⟩ := hf₂
          exact IsWalk_edges_mem hP_raw.1 hx
        exact hinj f₁ hf₁T f₂ hf₂T hEq
    refine ⟨hT₀_st, hG, ?_, ?_, hstretch_eq, ?_⟩
    · intro e he
      have huv := hG₀ e he
      rw [hfp_map huv.1 huv.2]
      intro f' hf'
      rw [walkEdges, List.map_map, List.mem_toFinset, List.mem_map] at hf'
      obtain ⟨x, hx, rfl⟩ := hf'
      have hev := hsubG.2.1 he
      have htail_eq := (hsubG.2.2 e he).1
      have hhead_eq := (hsubG.2.2 e he).2
      have hxGv : x.1 ∈ (weightedCopyGraph G₀ v).E :=
        hpaths_raw e hev x.1 (by
          rw [← htail_eq, ← hhead_eq]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))
      change projectEdge G₀ v x.1 ∈ G₀.E
      unfold projectEdge
      rw [ite_eq_left_iff.mpr (fun h => absurd hxGv h)]
      exact (weightedCopyGraph_origEdge_mem hE hxGv).1
    · intro e' he'
      have huw := weightedCopyGraph_isValid hG₀ v e' he'
      rw [weightedCopyGraph_V] at huw
      rw [hfp_map huw.1 huw.2]
      intro f' hf'
      rw [walkEdges, List.map_map, List.mem_toFinset, List.mem_map] at hf'
      obtain ⟨x, hx, rfl⟩ := hf'
      have hxGv : x.1 ∈ (weightedCopyGraph G₀ v).E :=
        hpaths_raw e' he' x.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))
      change projectEdge G₀ v x.1 ∈ (weightedCopyGraph G₀ v).E
      unfold projectEdge
      rw [ite_eq_left_iff.mpr (fun h => absurd hxGv h)]
      exact hsubG.2.1 (weightedCopyGraph_origEdge_mem hE hxGv).1
    · have hsum_eq : ∑ e' ∈ (weightedCopyGraph G₀ v).E,
          treeStretch (weightedCopyGraph G₀ v) T₀ (weightedCopyLen G₀ ℓ) e' =
        ∑ e' ∈ (weightedCopyGraph G₀ v).E,
          treeStretch (weightedCopyGraph G₀ v) T_raw (weightedCopyLen G₀ ℓ) e' :=
        Finset.sum_congr rfl hstretch_eq
      rw [hsum_eq]
      simpa only [one_mul] using hsum_raw
  · have hGV : (weightedCopyGraph G₀ v).E = ∅ := by
      unfold weightedCopyGraph
      rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
      exact Finset.not_nonempty_iff_eq_empty.mp hE
    have hT₀ : projectTree G₀ v T_raw = T_raw := by
      unfold projectTree
      rw [ite_eq_right_iff.mpr (fun h => absurd h hE)]
    have hG₀E : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT₀]; exact (weightedCopyGraph_V G₀ v) ▸ hlsst.1
    · rw [hT₀]; intro f _ hfG; rw [hG₀E] at hfG; exact absurd hfG (Finset.notMem_empty _)
    · intro e he; rw [hG₀E] at he; exact absurd he (Finset.notMem_empty _)
    · intro e' he'; rw [hGV] at he'; exact absurd he' (Finset.notMem_empty _)
    · intro e' he'; rw [hGV] at he'; exact absurd he' (Finset.notMem_empty _)
    · rw [hGV, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero]

/-! ## Parameters, threshold, decomposition, and dynamic LSF state -/

/-- Upper bound `(⌊log₂ n⌋ + 1)(⌊log₂ n⌋ + 2)` on the height of `hldAuxTree T r`
(`lemma_B_9`). -/
def hldDepthBound (n : ℕ) : ℕ :=
  (Nat.log 2 n + 1) * (Nat.log 2 n + 2)

/-- Stretch overestimate threshold `max 1 (8 · (D + 1)² · max 1 C_lsst · log²(n + 2) · k)`
used to add both endpoints of high-stretch edges to `R₀` so all edges satisfy `wstr_e ≤ O(k log⁶ n)`
(`lemma_5_4` item 2). -/
noncomputable def wstrThresh (C_lsst : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  max 1 (8 * ((hldDepthBound n + 1 : ℝ) ^ 2) * max 1 C_lsst * (Real.log ((n : ℝ) + 2)) ^ 2 * k)

/-- An arbitrarily chosen vertex of `G` when `G.V` is nonempty. -/
noncomputable def pickRoot (G : MGraph) : ℕ :=
  open Classical in
  if h : G.V.Nonempty then h.choose else 0

lemma pickRoot_mem {G : MGraph} (hV : G.V.Nonempty) : pickRoot G ∈ G.V := by
  unfold pickRoot
  rw [dite_eq_left_of_eq_true (eq_true hV)]
  exact hV.choose_spec

/-- One representative vertex in `G.V` from each connected component of `G`, choosing `r₀` in the
component of `r₀`. When `G` is connected and `r₀ ∈ G.V`, `compReps G r₀ = {r₀}`. -/
noncomputable def compReps (G : MGraph) (r₀ : ℕ) : Finset ℕ :=
  open Classical in
  (components G).image (fun C =>
    if r₀ ∈ C then r₀ else if h : C.Nonempty then Classical.choose h else r₀)

/-- Tree decomposition `𝒲^T` from `lemma_B_7` with uniform edge weights `1` and parameter
`k * (hldDepthBound G₀.n + 1)` when `2 ≤ G₀.V.card` (else `∅`). -/
noncomputable def pickDecomp (G₀ T₀ : MGraph) (r₀ : ℕ) (k : ℝ) : Finset (Finset ℕ) :=
  open Classical in
  if h : G₀.IsValid ∧ IsRootedTree T₀ r₀ ∧ T₀.V = G₀.V ∧ 2 ≤ G₀.V.card ∧ 0 < k then
    (lemma_B_7 h.1 h.2.1 h.2.2.1 h.2.2.2.1 (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (k * ((hldDepthBound G₀.n + 1 : ℕ) : ℝ))
      (mul_pos h.2.2.2.2 (by exact_mod_cast Nat.succ_pos _))).choose
  else
    ∅

/-- Refinement of `𝒲^T` by the connected components of `F₀`, retaining pieces with at least one
edge of `F₀` (`[chen2022maximum, Appendix B.3]`). -/
noncomputable def refineDecomp (W_T : Finset (Finset ℕ)) (F₀ : MGraph) : Finset (Finset ℕ) :=
  open Classical in
  ((W_T ×ˢ components F₀).image (fun p => p.1 ∩ p.2)).filter
    (fun W => (inducedEdges F₀ W).Nonempty)

/-- State maintained by the dynamic low-stretch forest algorithm of Lemma 5.4 and Appendix A.1. -/
structure LSFState where
  /-- Initial graph `G^(0)`. -/
  G₀ : MGraph
  /-- Current dynamic graph `G^(t)`. -/
  G : MGraph
  /-- Initial edge weights `v`. -/
  v : ℕ → ℝ
  /-- Component reduction parameter `k`. -/
  k : ℝ
  /-- Static initial spanning tree `T₀` on `G₀.V`. -/
  T₀ : MGraph
  /-- Current ambient forest `T` obtained from `T₀` by applying `.split` updates. -/
  T_cur : MGraph
  /-- Map sending each vertex of `G.V` to its initial ancestor vertex in `G₀.V`. -/
  origVert : ℕ → ℕ
  /-- Root `r₀ ∈ G₀.V` of `T₀`. -/
  r₀ : ℕ
  /-- Congestion-sorted edge order `π` on `T₀`. -/
  π : ℕ → ℕ
  /-- Initial root seed `R₀ ⊆ G₀.V` before upward closure in `T_H`. -/
  R₀_init : Finset ℕ
  /-- Current root seed `R_base ⊆ G₀.V` before upward closure in `T_H`. -/
  R₀_base : Finset ℕ
  /-- Vertices created by `.split` operations (`u^NEW` in Appendix A.1). -/
  isolatedVerts : Finset ℕ
  /-- Edges currently in `G` that were introduced by `.insert` updates. -/
  insertedEdges : Finset ℕ
  /-- Maintained stretch overestimates `wstr_e`. -/
  wstr : ℕ → ℝ
  /-- Initial decomposition `𝒲` of `F₀`. -/
  W_init : Finset (Finset ℕ)
  /-- Number of updates applied so far. -/
  numUpdates : ℕ

namespace LSFState

/-- Auxiliary HLD tree `T_H` on `(T₀, r₀)`. -/
noncomputable def TH (S : LSFState) : MGraph :=
  hldAuxTree S.T₀ S.r₀

/-- Roots inside `G₀.V`: upward closure of `R₀_base` in `T_H`. -/
noncomputable def R_orig (S : LSFState) : Finset ℕ :=
  upClosure S.TH S.r₀ S.R₀_base

/-- Full root set `R = R_orig ∪ isolatedVerts`. -/
noncomputable def R (S : LSFState) : Finset ℕ :=
  S.R_orig ∪ S.isolatedVerts

/-- Current ambient forest `T` obtained from `T₀` by applying `.split` updates so that
`F ⊆ T` remains a subgraph of `G`. -/
def T (S : LSFState) : MGraph := S.T_cur

/-- Current rooted spanning forest `F` with edge set `F_{T₀}(R_orig, π).E`, endpoints from
`T_cur`, and root set `R`. -/
noncomputable def RF (S : LSFState) : RootedForest :=
  { F := { V := S.T_cur.V
           E := (forestGivenRoots S.T₀ S.r₀ S.R_orig S.π).E
           tail := S.T_cur.tail
           head := S.T_cur.head }
    R := S.R }

/-- Exposed `LSF` triple `(T, F, wstr)`. -/
noncomputable def lsf (S : LSFState) : LSF :=
  ⟨S.T, S.RF, S.wstr⟩

end LSFState

/-- Initialize the dynamic low-stretch forest state for `(G₀, ℓ₀, v, k)` using the static LSST
oracle `oracle` (`HasLSSTSpec oracle C_lsst`). -/
noncomputable def initLSF (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ) : LSFState :=
  open Classical in
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T_raw := if G₀.E.Nonempty then oracle G_v ℓ_v (fun _ => 1) else oracle G₀ (fun _ => 1) (fun _ => 1)
  let T₀ := projectTree G₀ v T_raw
  let r₀ := pickRoot G₀
  let π :=
    if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  let rawWstr := fun e => levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e
  let thresh := wstrThresh C_lsst G₀.n k
  let E_high := G₀.E.filter (fun e => thresh ≤ rawWstr e)
  let W_T := pickDecomp G₀ T₀ r₀ k
  let R₀_init := compReps G₀ r₀ ∪ boundary W_T ∪ E_high.biUnion (fun e => {G₀.tail e, G₀.head e})
  let wstr := fun e => if e ∈ G₀.E then (if thresh ≤ rawWstr e then (1 : ℝ) else rawWstr e) else 1
  let R_orig_init := upClosure (hldAuxTree T₀ r₀) r₀ R₀_init
  let F₀ := forestGivenRoots T₀ r₀ R_orig_init π
  { G₀ := G₀
    G := G₀
    v := v
    k := k
    T₀ := T₀
    T_cur := T₀
    origVert := id
    r₀ := r₀
    π := π
    R₀_init := R₀_init
    R₀_base := R₀_init
    isolatedVerts := ∅
    insertedEdges := ∅
    wstr := wstr
    W_init := refineDecomp W_T F₀
    numUpdates := 0 }

/-- Apply one dynamic graph update to `LSFState` (Appendix A.1, adapted to keep `F ⊆ G` across
vertex splits):
* `.insert e a b`: adds `a^{↑ T_H}` and `b^{↑ T_H}` to `R` (for ends in `T₀.V`) and sets
  `wstr e = 1`.
* `.delete e`: adds both ends `(origVert _)^{↑ T_H}` of `e` in `T₀.V` to `R`.
* `.split v v' St Sh`: splits `v` along `(St, Sh)` in both `G` and `T`, adds `v'` as a new root,
  and adds `(origVert v)^{↑ T_H}` to `R`. -/
noncomputable def applyLSFUpdate (S : LSFState) : Update → LSFState
  | .insert e a b =>
    let addRoots := ({a, b} : Finset ℕ).filter (fun x => x ∈ S.T₀.V)
    { S with
      G := S.G.applyUpdate (.insert e a b)
      R₀_base := S.R₀_base ∪ addRoots
      insertedEdges := insert e S.insertedEdges
      wstr := Function.update S.wstr e 1
      numUpdates := S.numUpdates + 1 }
  | .delete e =>
    let addRoots := ({S.origVert (S.G.tail e), S.origVert (S.G.head e)} : Finset ℕ).filter
      (fun x => x ∈ S.T₀.V)
    { S with
      G := S.G.applyUpdate (.delete e)
      R₀_base := S.R₀_base ∪ addRoots
      insertedEdges := S.insertedEdges.erase e
      numUpdates := S.numUpdates + 1 }
  | .split v v' St Sh =>
    let vOrig := S.origVert v
    { S with
      G := S.G.applyUpdate (.split v v' St Sh)
      T_cur := S.T_cur.applyUpdate (.split v v' St Sh)
      R₀_base := open Classical in if vOrig ∈ S.T₀.V then insert vOrig S.R₀_base else S.R₀_base
      isolatedVerts := insert v' S.isolatedVerts
      origVert := Function.update S.origVert v' vOrig
      numUpdates := S.numUpdates + 1 }

/-- Apply a batch of updates in order to `LSFState`. -/
noncomputable def applyLSFBatch (S : LSFState) (U : List Update) : LSFState :=
  U.foldl applyLSFUpdate S

/-- Apply a sequence of update batches in order to `LSFState`. -/
noncomputable def applyLSFBatches (S : LSFState) (Us : List (List Update)) : LSFState :=
  Us.foldl applyLSFBatch S

end MinCostFlow.LSF
