module

public import MinCostFlow.Chain.TreeChain
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fundamental chain cycles and good-cycle extraction (Appendix A.3; [chen2022maximum] Section 7.2)

This file formalizes Appendix A.3 (pages 48–49) and the corresponding static definitions and
lemmas from [chen2022maximum] (arXiv:2203.00671v2, Section 7.2; note that the paper cites these
using earlier draft numbers: "Lemma 7.14" is v2 Lemma 7.13 and "Lemma 7.17" is v2 Lemma 7.16):

* `TreeChain.edgeLevel` (Definition A.1; [chen2022maximum] Definition 7.10): the unique level
  `i ≤ d` where a non-tree edge `e ∈ E(G) \ E(T^𝒢)` drops out of `𝒮(G_i, F_i)`.
* `TreeChain.sparsifierCycle` (`a(e)`), `TreeChain.fundChainCycle` (`a^G(e^G)`), and
  `TreeChain.wlen` ([chen2022maximum] Definition 7.11).
* `TreeChain.liftWalk` ([chen2022maximum] Definition 7.14): lifting a cycle from `𝒞(G_i, F_i)`
  into `G_i`.
* `lemma_7_12`: gradient preservation under lifting when each tree `T_i` connects the endpoints
  of edges in `G_i`, together with `lemma_7_12_counterexample` showing it fails after vertex
  splits create isolated vertices in `T_i`.
* `lemma_7_13`: length overestimate `⟨ℓ, |a^G(e^G)|⟩ ≤ wlen_{e^G}` under
  `SelfLoopFreeEmbeddings` (including empty path embeddings for self-loops), together with
  `lemma_7_13_lift_counterexample` showing the general cycle-lifting step in [chen2022maximum]
  fails when a lifted cycle contains multiple self-loops in `𝒞(G_i, F_i)`.
* `lemma_7_15` ([chen2022maximum] Lemma 7.15): decomposition of any circulation `c` into
  fundamental chain cycles using `EmbedsSurviving`.
* `lemma_A_2` (Appendix A.3 Lemma A.2, page 48; [chen2022maximum] Lemma 7.16): existence of a
  fundamental chain cycle achieving ratio at least `(1 / (σ + 1)) * |⟨g, c⟩| / ∑_i ‖w^{G_i}‖₁`
  with `⟨ℓ, |a^G(e^G)|⟩` in the denominator.
-/

@[expose] public section

namespace MinCostFlow.Chain

section WalkHelpers

lemma mem_E_of_mem_walkEdges {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) {e : ℕ} (he : e ∈ walkEdges P) : e ∈ G.E := by
  rw [walkEdges, List.mem_toFinset, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  exact MGraph.isWalk_edges_mem hP x hx

lemma walkInner_eq_inner_of_subset {G : MGraph} {x : ℕ → ℝ} {P : List (ℕ × Bool)}
    (hsub : walkEdges P ⊆ G.E) :
    walkInner x P = G.inner x (walkFlow P) := by
  rw [walkInner_eq_sum_of_subset hsub]
  rfl

lemma walkLength_eq_lnorm_of_subset {G : MGraph} {ℓ : ℕ → ℝ} {P : List (ℕ × Bool)}
    (hsub : walkEdges P ⊆ G.E) :
    walkLength ℓ P = G.lnorm ℓ (walkFlow P) := by
  rw [walkLength_eq_sum_of_subset hsub]
  rfl

lemma walkInner_eq_of_walkFlow_eq (x : ℕ → ℝ) {P Q : List (ℕ × Bool)}
    (h : ∀ e, walkFlow P e = walkFlow Q e) :
    walkInner x P = walkInner x Q := by
  rw [walkInner_eq_sum_of_subset (Finset.subset_union_left (s₁ := walkEdges P) (s₂ := walkEdges Q)),
    walkInner_eq_sum_of_subset (Finset.subset_union_right (s₁ := walkEdges P) (s₂ := walkEdges Q))]
  refine Finset.sum_congr rfl fun e _ => by rw [h e]

lemma walkLength_eq_of_walkFlow_eq (ℓ : ℕ → ℝ) {P Q : List (ℕ × Bool)}
    (h : ∀ e, walkFlow P e = walkFlow Q e) :
    walkLength ℓ P = walkLength ℓ Q := by
  rw [walkLength_eq_sum_of_subset (Finset.subset_union_left (s₁ := walkEdges P) (s₂ := walkEdges Q)),
    walkLength_eq_sum_of_subset (Finset.subset_union_right (s₁ := walkEdges P) (s₂ := walkEdges Q))]
  refine Finset.sum_congr rfl fun e _ => by rw [h e]

lemma walkInner_cons (x : ℕ → ℝ) (y : ℕ × Bool) (P : List (ℕ × Bool)) :
    walkInner x (y :: P) = walkInner x [y] + walkInner x P := by
  simpa using walkInner_append x [y] P

lemma walkFlow_forestPath_mem_E {F : MGraph} {u v e : ℕ}
    (he : walkFlow (F.forestPath u v) e ≠ 0) : e ∈ F.E := by
  have hm := mem_walkEdges_of_walkFlow_ne_zero he
  by_cases hc : F.Connected u v
  · exact mem_E_of_mem_walkEdges (MGraph.isWalk_forestPath hc) hm
  · have hemp : F.forestPath u v = [] := by
      classical
      unfold MGraph.forestPath
      rw [dite_eq_right_iff]
      intro ⟨P, hP⟩; exact absurd ⟨P, hP.1⟩ hc
    rw [hemp, walkFlow_nil] at he
    exact absurd rfl he

lemma forestPath_edges_subset {F : MGraph} (u v : ℕ) :
    walkEdges (F.forestPath u v) ⊆ F.E := by
  intro e he
  by_cases hc : F.Connected u v
  · exact mem_E_of_mem_walkEdges (MGraph.isWalk_forestPath hc) he
  · have hemp : F.forestPath u v = [] := by
      classical
      unfold MGraph.forestPath
      rw [dite_eq_right_iff]
      intro ⟨P, hP⟩; exact absurd ⟨P, hP.1⟩ hc
    simp [hemp, walkEdges] at he

lemma forestPath_self_eq_nil {F : MGraph} (hF : F.IsForest) (u : ℕ) :
    F.forestPath u u = [] := by
  have hp := MGraph.isPath_forestPath (MGraph.connected_refl F u)
  have hnd := MGraph.isPath_edges_nodup hp
  cases h : F.forestPath u u with
  | nil => rfl
  | cons x xs =>
    exfalso
    rw [h] at hp hnd
    exact hF.2 (x :: xs) ⟨List.cons_ne_nil x xs, hnd, u, hp.1⟩

/-- Every edge traversed by a path is non-self-loop (`tail ≠ head`). -/
lemma no_selfLoop_of_isPath {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsPath u v P → ∀ x ∈ P, G.tail x.1 ≠ G.head x.1 := by
  intro u v P hP
  rcases hP with ⟨hW, hnd⟩
  induction hW with
  | nil _ => intro _ hx; cases hx
  | @cons u v y Q he hsrc _ ih =>
    intro x hx
    have hnd_cons : (u :: G.walkVertices (G.dst y) Q).Nodup := by
      simpa [MGraph.walkVertices] using hnd
    have hnotin : u ∉ G.walkVertices (G.dst y) Q := (List.nodup_cons.mp hnd_cons).1
    have htail : (G.walkVertices (G.dst y) Q).Nodup := (List.nodup_cons.mp hnd_cons).2
    rcases List.mem_cons.mp hx with rfl | hxQ
    · intro heq
      have hsd : G.src x = G.dst x := by cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, heq]
      rw [← hsrc, hsd] at hnotin
      exact hnotin (by simp [MGraph.walkVertices])
    · exact ih htail x hxQ

end WalkHelpers

namespace TreeChain

section EdgeLevels

variable (C : TreeChain)

private lemma activeS_last_E : (C.activeS C.d).E = ∅ := by
  simp [activeS]

/-- The unique level `i ≤ d` at which `e ∈ (activeCore i).E \ (activeS i).E`
(Definition A.1, page 48; [chen2022maximum] Definition 7.10). -/
noncomputable def edgeLevel (e : ℕ) : ℕ :=
  open Classical in
  if h : ∃ i, i ≤ C.d ∧ e ∈ (C.activeCore i).E \ (C.activeS i).E then Nat.find h else 0

lemma exists_edgeLevel_of_mem_sdiff {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {e : ℕ} (he0 : e ∈ (C.G 0).E) (heNotT : e ∉ C.chainTree.E) :
    ∃ i, i ≤ C.d ∧ e ∈ (C.activeCore i).E \ (C.activeS i).E := by
  have hnotF : ∀ i ≤ C.d, e ∉ (C.activeLSF i).F.F.E := by
    intro i hi hmem
    apply heNotT
    simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨i, Nat.lt_succ_of_le hi, hmem⟩
  have hstep : ∀ k ≤ C.d,
      (∀ j < k, e ∉ (C.activeCore j).E \ (C.activeS j).E) → e ∈ (C.G k).E := by
    intro k
    induction k with
    | zero => intro _ _; exact he0
    | succ m ih =>
      intro hm hprev
      have heGm : e ∈ (C.G m).E := ih (Nat.le_of_lt hm) fun j hj => hprev j (Nat.lt_succ_of_lt hj)
      have heCore : e ∈ (C.activeCore m).E := Finset.mem_sdiff.mpr ⟨heGm, hnotF m (Nat.le_of_lt hm)⟩
      have heNotDiff := hprev m (Nat.lt_succ_self m)
      have heSm : e ∈ (C.activeS m).E := by
        by_contra hnot
        exact heNotDiff (Finset.mem_sdiff.mpr ⟨heCore, hnot⟩)
      rw [← C.activeS_eq_G_succ hH hm]
      exact heSm
  by_cases hex : ∃ j < C.d, e ∈ (C.activeCore j).E \ (C.activeS j).E
  · obtain ⟨j, hj, hej⟩ := hex
    exact ⟨j, Nat.le_of_lt hj, hej⟩
  · push Not at hex
    have heGd := hstep C.d (le_refl C.d) hex
    have heCoreD : e ∈ (C.activeCore C.d).E := Finset.mem_sdiff.mpr ⟨heGd, hnotF C.d (le_refl C.d)⟩
    refine ⟨C.d, le_refl C.d, Finset.mem_sdiff.mpr ⟨heCoreD, ?_⟩⟩
    rw [C.activeS_last_E]
    exact Finset.notMem_empty e

lemma mem_sdiff_of_mem_activeCore_diff {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    e ∈ (C.G 0).E \ C.chainTree.E := by
  have heCore : e ∈ (C.activeCore i).E := (Finset.mem_sdiff.mp he).1
  have heNotS : e ∉ (C.activeS i).E := (Finset.mem_sdiff.mp he).2
  have heGi : e ∈ (C.G i).E := (Finset.mem_sdiff.mp heCore).1
  have heNotFi : e ∉ (C.activeLSF i).F.F.E := (Finset.mem_sdiff.mp heCore).2
  refine Finset.mem_sdiff.mpr ⟨C.G_E_subset_of_le hH (Nat.zero_le i) hi heGi, ?_⟩
  intro heTree
  simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range] at heTree
  obtain ⟨m, hm_lt, hm_mem⟩ := heTree
  have hm : m ≤ C.d := Nat.lt_succ_iff.mp hm_lt
  rcases lt_trichotomy m i with hlt | rfl | hgt
  · have heGm1 : e ∈ (C.G (m + 1)).E := C.G_E_subset_of_le hH hlt hi heGi
    have hnot := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH (by omega) heGm1)).2
    exact hnot hm_mem
  · exact heNotFi hm_mem
  · have hi_lt : i < C.d := by omega
    have heGm : e ∈ (C.G m).E := (hSub m hm).2.1 hm_mem
    have heGi1 : e ∈ (C.G (i + 1)).E := C.G_E_subset_of_le hH hgt hm heGm
    rw [← C.activeS_eq_G_succ hH hi_lt] at heGi1
    exact heNotS heGi1

lemma level_unique_of_mem_activeCore_diff {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i j e : ℕ} (hi : i ≤ C.d) (hj : j ≤ C.d)
    (hei : e ∈ (C.activeCore i).E \ (C.activeS i).E)
    (hej : e ∈ (C.activeCore j).E \ (C.activeS j).E) : i = j := by
  by_contra hne
  wlog hij : i < j generalizing i j
  · exact this hj hi hej hei (Ne.symm hne) (by omega)
  have hi_lt : i < C.d := by omega
  have heGj : e ∈ (C.G j).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hej).1).1
  have heGi1 : e ∈ (C.G (i + 1)).E := C.G_E_subset_of_le hH hij hj heGj
  rw [← C.activeS_eq_G_succ hH hi_lt] at heGi1
  exact (Finset.mem_sdiff.mp hei).2 heGi1

lemma edgeLevel_eq_of_mem {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i e : ℕ} (hi : i ≤ C.d)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    C.edgeLevel e = i := by
  classical
  have hex : ∃ j, j ≤ C.d ∧ e ∈ (C.activeCore j).E \ (C.activeS j).E := ⟨i, hi, he⟩
  have heq : C.edgeLevel e = Nat.find hex := by
    unfold edgeLevel
    split_ifs
    rfl
  rw [heq]
  have hspec := Nat.find_spec hex
  exact C.level_unique_of_mem_activeCore_diff hH hspec.1 hi hspec.2 he

lemma mem_activeCore_diff_edgeLevel {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {e : ℕ} (he : e ∈ (C.G 0).E \ C.chainTree.E) :
    C.edgeLevel e ≤ C.d ∧ e ∈ (C.activeCore (C.edgeLevel e)).E \ (C.activeS (C.edgeLevel e)).E := by
  classical
  have hmem := Finset.mem_sdiff.mp he
  have hex := C.exists_edgeLevel_of_mem_sdiff hH hmem.1 hmem.2
  have heq : C.edgeLevel e = Nat.find hex := by
    unfold edgeLevel
    split_ifs
    rfl
  rw [heq]
  exact Nat.find_spec hex

lemma sdiff_chainTree_eq_biUnion_level {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    (C.G 0).E \ C.chainTree.E =
      (Finset.range (C.d + 1)).biUnion fun i => (C.activeCore i).E \ (C.activeS i).E := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro he
    have hmem := Finset.mem_sdiff.mp he
    exact C.exists_edgeLevel_of_mem_sdiff hH hmem.1 hmem.2
  · rintro ⟨i, hi, hei⟩
    exact C.mem_sdiff_of_mem_activeCore_diff hH hSub hi hei

lemma sum_offTree_eq_sum_levels {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (f : ℕ → ℕ → ℝ) :
    (∑ e ∈ (C.G 0).E \ C.chainTree.E, f (C.edgeLevel e) e) =
      ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, f i e := by
  rw [C.sdiff_chainTree_eq_biUnion_level hH hSub, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_congr rfl fun e he => ?_
    rw [C.edgeLevel_eq_of_mem hH (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) he]
  · intro i hi j hj hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hei hej
    exact hij (C.level_unique_of_mem_activeCore_diff hH
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hei hej)

end EdgeLevels

section CyclesAndLifting

variable (C : TreeChain)

/-- The sparsifier cycle `a(e) = (e, true) ⊕ rev(Π_i(e))` of an edge `e` in
`(C.activeCore i).E \ (C.activeS i).E` (Definition A.1, page 48; [chen2022maximum] Def. 7.10). -/
def sparsifierCycle (i e : ℕ) : List (ℕ × Bool) :=
  (e, true) :: walkRev (C.activeEmb i e)

/-- The length overestimate `wlen_{e^G}` computed by occurrence count along
`a(e) = (e, true) ⊕ rev(Π_i(e))` ([chen2022maximum] Definition 7.11; agrees with
`⟨ℓ^{𝒞(G_i, F_i)}, |a(e)|⟩` on simple paths and matches `passSparseCoreW` and the
key evaluator on general dynamic-spanner walks). -/
noncomputable def wlenAt (ℓ : ℕ → ℝ) (i e : ℕ) : ℝ :=
  ((C.sparsifierCycle i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum

/-- The length overestimate `wlen_{e^G}` for an off-tree edge `e` at level `edgeLevel e`. -/
noncomputable def wlen (ℓ : ℕ → ℝ) (e : ℕ) : ℝ :=
  C.wlenAt ℓ (C.edgeLevel e) e

noncomputable def stitchAux (G F : MGraph) (target : ℕ) :
    ℕ × Bool → List (ℕ × Bool) → List (ℕ × Bool)
  | x, [] => [x] ++ F.forestPath (G.dst x) target
  | x, y :: xs => [x] ++ F.forestPath (G.dst x) (G.src y) ++ stitchAux G F target y xs

/-- Splicing `F`-paths between consecutive edges (and from the last edge back to the start vertex)
to turn a list of edges into a closed walk in `G`. -/
noncomputable def stitchCycle (G F : MGraph) : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | x :: xs => stitchAux G F (G.src x) x xs

/-- Lifting a closed walk `W` from `𝒞(G_m, F_m)` into `G_m`
([chen2022maximum] Definition 7.14). -/
noncomputable def liftWalk (m : ℕ) (W : List (ℕ × Bool)) : List (ℕ × Bool) :=
  stitchCycle (C.G m) (C.activeLSF m).F.F W

/-- Fundamental chain cycle `a^G(e^G)` associated to an edge `e` at level `i`
(Definition A.1, page 48). -/
noncomputable def fundChainCycleAt (i e : ℕ) : List (ℕ × Bool) :=
  stitchCycle (C.G 0) C.chainTree (C.sparsifierCycle i e)

/-- The fundamental chain cycle `a^G(e^G)` for `e ∈ E(G) \ E(T^𝒢)`
(Definition A.1, page 48; [chen2022maximum] Definition 7.10). -/
noncomputable def fundChainCycle (e : ℕ) : List (ℕ × Bool) :=
  C.fundChainCycleAt (C.edgeLevel e) e

def AdjConn (G F : MGraph) (target : ℕ) : ℕ × Bool → List (ℕ × Bool) → Prop
  | x, [] => F.Connected (G.dst x) target
  | x, y :: xs => F.Connected (G.dst x) (G.src y) ∧ AdjConn G F target y xs

private lemma adjConn_of_closedWalk_aux {G H F : MGraph} {target r₀ : ℕ}
    (hconn : ∀ a b : ℕ × Bool, a.1 ∈ H.E → b.1 ∈ H.E → H.dst a = H.src b →
      F.Connected (G.dst a) (G.src b))
    (hclose : ∀ z : ℕ × Bool, z.1 ∈ H.E → H.dst z = r₀ → F.Connected (G.dst z) target) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      x.1 ∈ H.E → H.IsWalk (H.dst x) r₀ xs → AdjConn G F target x xs
  | [], x, hxE, hW => by
    cases hW
    exact hclose x hxE rfl
  | y :: ys, x, hxE, hW => by
    cases hW with
    | cons hyE hys hrest =>
      exact ⟨hconn x y hxE hyE hys.symm, adjConn_of_closedWalk_aux hconn hclose ys y hyE hrest⟩

lemma adjConn_of_closedWalk {G H F : MGraph} {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)}
    {r₀ : ℕ} (hW : H.IsWalk r₀ r₀ (x₀ :: xs))
    (hconn : ∀ a b : ℕ × Bool, a.1 ∈ H.E → b.1 ∈ H.E → H.dst a = H.src b →
      F.Connected (G.dst a) (G.src b)) :
    AdjConn G F (G.src x₀) x₀ xs := by
  cases hW with
  | cons hx₀E hsrc hrest =>
    have hclose : ∀ z : ℕ × Bool, z.1 ∈ H.E → H.dst z = r₀ → F.Connected (G.dst z) (G.src x₀) := by
      intro z hzE hdst
      exact hconn z x₀ hzE hx₀E (hdst.trans hsrc.symm)
    exact adjConn_of_closedWalk_aux hconn hclose xs x₀ hx₀E hrest

private lemma stitchAux_ne_nil (G F : MGraph) (target : ℕ) (x : ℕ × Bool) (xs : List (ℕ × Bool)) :
    stitchAux G F target x xs ≠ [] := by
  cases xs <;> simp [stitchAux]

private lemma stitchAux_isWalk {G F : MGraph} (hGF : G.IsSubgraph F) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      x.1 ∈ G.E → (∀ y ∈ xs, y.1 ∈ G.E) → AdjConn G F target x xs →
      G.IsWalk (G.src x) target (stitchAux G F target x xs)
  | [], x, hxE, _, hadj => by
    have hFP : G.IsWalk (G.dst x) target (F.forestPath (G.dst x) target) :=
      MGraph.isWalk_of_isSubgraph hGF (MGraph.isWalk_forestPath hadj)
    simpa [stitchAux] using .cons hxE rfl hFP
  | y :: ys, x, hxE, hxsE, hadj => by
    have hyE : y.1 ∈ G.E := hxsE y (by simp)
    have hysE : ∀ z ∈ ys, z.1 ∈ G.E := fun z hz => hxsE z (by simp [hz])
    have hFP : G.IsWalk (G.dst x) (G.src y) (F.forestPath (G.dst x) (G.src y)) :=
      MGraph.isWalk_of_isSubgraph hGF (MGraph.isWalk_forestPath hadj.1)
    have htail := stitchAux_isWalk hGF target ys y hyE hysE hadj.2
    have hmid := MGraph.isWalk_append (.cons hxE rfl hFP) htail
    simpa [stitchAux, List.append_assoc] using hmid

private noncomputable def stitchTreeFlowAux (G F : MGraph) (target : ℕ) :
    ℕ × Bool → List (ℕ × Bool) → ℕ → ℝ
  | x, [] => walkFlow (F.forestPath (G.dst x) target)
  | x, y :: xs => fun e =>
      walkFlow (F.forestPath (G.dst x) (G.src y)) e + stitchTreeFlowAux G F target y xs e

private lemma walkFlow_stitchAux (G F : MGraph) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool) (e : ℕ),
      walkFlow (stitchAux G F target x xs) e =
        walkFlow (x :: xs) e + stitchTreeFlowAux G F target x xs e
  | [], x, e => by
    simp [stitchAux, stitchTreeFlowAux, walkFlow_cons, walkFlow_nil]
  | y :: ys, x, e => by
    have ih := walkFlow_stitchAux G F target ys y e
    simp only [stitchAux, stitchTreeFlowAux, List.append_assoc]
    rw [walkFlow_append, walkFlow_append, ih, walkFlow_cons, walkFlow_cons]
    simp only [walkFlow_cons, walkFlow_nil, add_zero]
    ring

private lemma stitchTreeFlowAux_eq_zero_of_not_mem {G F : MGraph} (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool) {e : ℕ}, e ∉ F.E →
      stitchTreeFlowAux G F target x xs e = 0
  | [], x, _, he => by
    by_contra hne
    exact he (walkFlow_forestPath_mem_E hne)
  | y :: ys, x, e, he => by
    have h1 : walkFlow (F.forestPath (G.dst x) (G.src y)) e = 0 := by
      by_contra hne
      exact he (walkFlow_forestPath_mem_E hne)
    have h2 := stitchTreeFlowAux_eq_zero_of_not_mem (G := G) target ys y he
    simp [stitchTreeFlowAux, h1, h2]

lemma sparsifierCycle_isClosedWalk {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    (C.activeCore i).IsWalk ((C.activeCore i).tail e) ((C.activeCore i).tail e)
      (C.sparsifierCycle i e) := by
  have heCore : e ∈ (C.activeCore i).E := (Finset.mem_sdiff.mp he).1
  by_cases hi_lt : i < C.d
  · have hSp := C.activeS_isSparsified hH hi_lt
    have hEmb : (C.activeS i).IsWalk ((C.activeCore i).tail e) ((C.activeCore i).head e)
        (C.activeEmb i e) := hSp.2.1.2 e heCore
    have hCoreEmb := MGraph.isWalk_of_isSubgraph hSp.1 hEmb
    exact .cons heCore rfl (by simpa [activeCore, MGraph.dst] using MGraph.isWalk_walkRev hCoreEmb)
  · have hieq : i = C.d := by omega
    subst hieq
    have heGd : e ∈ (C.G C.d).E := (Finset.mem_sdiff.mp heCore).1
    have hEnds := C.G_isValid hH C.d (le_refl C.d) e heGd
    have hGdConn : (C.G C.d).Connected ((C.G C.d).tail e) ((C.G C.d).head e) :=
      ⟨[(e, true)], .cons heGd rfl (by simp [MGraph.dst]; exact .nil _)⟩
    have hFConn := hSpan ((C.G C.d).tail e) hEnds.1 ((C.G C.d).head e) hEnds.2 hGdConn
    have hRF := (C.activeLSF_holds hH (le_refl C.d)).2.1
    have hreq : (C.activeLSF C.d).F.root ((C.G C.d).tail e) =
        (C.activeLSF C.d).F.root ((C.G C.d).head e) :=
      root_eq_of_connected hRF hEnds.1 hEnds.2 hFConn
    have htail_head : (C.activeCore C.d).tail e = (C.activeCore C.d).head e := hreq
    refine .cons heCore rfl ?_
    simp only [activeEmb, lt_irrefl, ↓reduceIte, walkRev, List.map_nil, List.reverse_nil,
      MGraph.dst, ← htail_head]
    exact .nil _

lemma sparsifierCycle_revEmb_edges_subset {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i e : ℕ} (hi : i ≤ C.d)
    (heCore : e ∈ (C.activeCore i).E) :
    walkEdges (walkRev (C.activeEmb i e)) ⊆ (C.activeS i).E := by
  rw [walkEdges_walkRev]
  by_cases hi_lt : i < C.d
  · have hSp := C.activeS_isSparsified hH hi_lt
    intro f hf
    exact mem_E_of_mem_walkEdges (hSp.2.1.2 e heCore) hf
  · have hieq : i = C.d := by omega
    subst hieq
    simp [activeEmb, walkEdges]

lemma fundChainCycleAt_isClosedWalk {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    (C.G 0).IsWalk ((C.G 0).tail e) ((C.G 0).tail e) (C.fundChainCycleAt i e) := by
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hSubTree := C.chainTree_isSubgraph hH hSub
  have hconn : ∀ a b : ℕ × Bool, a.1 ∈ (C.activeCore i).E → b.1 ∈ (C.activeCore i).E →
      (C.activeCore i).dst a = (C.activeCore i).src b →
      C.chainTree.Connected ((C.G 0).dst a) ((C.G 0).src b) := by
    intro a b haE hbE heq
    have haGi : a.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp haE).1
    have hbGi : b.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp hbE).1
    have haG0 : a.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi haGi
    have hbG0 : b.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi hbGi
    have hEndsA := C.G_isValid hH 0 (Nat.zero_le C.d) a.1 haG0
    have hEndsB := C.G_isValid hH 0 (Nat.zero_le C.d) b.1 hbG0
    have haV0 : (C.G 0).dst a ∈ (C.G 0).V := by cases ha2 : a.2 <;> simp [MGraph.dst, ha2, hEndsA.1, hEndsA.2]
    have hbV0 : (C.G 0).src b ∈ (C.G 0).V := by cases hb2 : b.2 <;> simp [MGraph.src, hb2, hEndsB.1, hEndsB.2]
    have hproj_eq : C.proj (i + 1) ((C.G 0).dst a) = C.proj (i + 1) ((C.G 0).src b) := by
      change (C.activeLSF i).F.root (C.proj i ((C.G 0).dst a)) =
        (C.activeLSF i).F.root (C.proj i ((C.G 0).src b))
      rw [← C.G_dst_eq_proj hH hi haGi, ← C.G_src_eq_proj hH hi hbGi]
      have hdst : (C.activeCore i).dst a = (C.activeLSF i).F.root ((C.G i).dst a) := by
        cases ha2 : a.2 <;> simp [MGraph.dst, activeCore, coreGraph, ha2]
      have hsrc : (C.activeCore i).src b = (C.activeLSF i).F.root ((C.G i).src b) := by
        cases hb2 : b.2 <;> simp [MGraph.src, activeCore, coreGraph, hb2]
      rw [← hdst, ← hsrc]
      exact heq
    exact C.connected_chainTree_of_proj_eq hH hSub (i + 1) (Nat.succ_le_succ hi) _ haV0 _ hbV0 hproj_eq
  have hadj := adjConn_of_closedWalk (G := C.G 0) (F := C.chainTree) hClosed hconn
  have he0 : e ∈ (C.G 0).E :=
    C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hxs : ∀ y ∈ walkRev (C.activeEmb i e), y.1 ∈ (C.G 0).E := by
    intro y hy
    have hyCore : y.1 ∈ (C.activeCore i).E :=
      MGraph.isWalk_edges_mem (by cases hClosed with | cons _ _ h => exact h) y hy
    exact C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp hyCore).1
  simpa [fundChainCycleAt, stitchCycle, sparsifierCycle, MGraph.src] using
    stitchAux_isWalk hSubTree ((C.G 0).src (e, true)) (walkRev (C.activeEmb i e)) (e, true) he0 hxs hadj

lemma liftWalk_isClosedWalk {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {m r₀ : ℕ} (hm : m ≤ C.d) {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)}
    (hW : (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs)) :
    (C.G m).IsWalk ((C.G m).src x₀) ((C.G m).src x₀) (C.liftWalk m (x₀ :: xs)) ∧
      C.liftWalk m (x₀ :: xs) ≠ [] := by
  have hRF := (C.activeLSF_holds hH hm).2.1
  have hconn : ∀ a b : ℕ × Bool, a.1 ∈ (C.activeCore m).E → b.1 ∈ (C.activeCore m).E →
      (C.activeCore m).dst a = (C.activeCore m).src b →
      (C.activeLSF m).F.F.Connected ((C.G m).dst a) ((C.G m).src b) := by
    intro a b haE hbE heq
    have haGm : a.1 ∈ (C.G m).E := (Finset.mem_sdiff.mp haE).1
    have hbGm : b.1 ∈ (C.G m).E := (Finset.mem_sdiff.mp hbE).1
    have hEndsA := C.G_isValid hH m hm a.1 haGm
    have hEndsB := C.G_isValid hH m hm b.1 hbGm
    have haV : (C.G m).dst a ∈ (C.G m).V := by cases ha2 : a.2 <;> simp [MGraph.dst, ha2, hEndsA.1, hEndsA.2]
    have hbV : (C.G m).src b ∈ (C.G m).V := by cases hb2 : b.2 <;> simp [MGraph.src, hb2, hEndsB.1, hEndsB.2]
    have hreq : (C.activeLSF m).F.root ((C.G m).dst a) = (C.activeLSF m).F.root ((C.G m).src b) := by
      have hdst : (C.activeCore m).dst a = (C.activeLSF m).F.root ((C.G m).dst a) := by
        cases ha2 : a.2 <;> simp [MGraph.dst, activeCore, coreGraph, ha2]
      have hsrc : (C.activeCore m).src b = (C.activeLSF m).F.root ((C.G m).src b) := by
        cases hb2 : b.2 <;> simp [MGraph.src, activeCore, coreGraph, hb2]
      rw [← hdst, ← hsrc]
      exact heq
    exact connected_of_root_eq hRF haV hbV hreq
  have hadj := adjConn_of_closedWalk (G := C.G m) (F := (C.activeLSF m).F.F) hW hconn
  have hx₀Gm : x₀.1 ∈ (C.G m).E := by
    cases hW with | cons hx _ _ => exact (Finset.mem_sdiff.mp hx).1
  have hxsGm : ∀ y ∈ xs, y.1 ∈ (C.G m).E := by
    intro y hy
    have hyCore : y.1 ∈ (C.activeCore m).E :=
      MGraph.isWalk_edges_mem (by cases hW with | cons _ _ h => exact h) y hy
    exact (Finset.mem_sdiff.mp hyCore).1
  refine ⟨?_, ?_⟩
  · unfold liftWalk stitchCycle; dsimp only
    exact stitchAux_isWalk (hSub m hm) ((C.G m).src x₀) xs x₀ hx₀Gm hxsGm hadj
  · unfold liftWalk stitchCycle; dsimp only
    exact stitchAux_ne_nil (C.G m) (C.activeLSF m).F.F ((C.G m).src x₀) x₀ xs

noncomputable def edgeDetourFlow (G : MGraph) (RF : RootedForest) (e : ℕ) : ℕ → ℝ :=
  if RF.root (G.tail e) = RF.root (G.head e) then
    walkFlow (RF.F.forestPath (G.head e) (G.tail e))
  else
    walkFlow (RF.F.forestPath (G.head e) (RF.root (G.head e))) +
      walkFlow (RF.F.forestPath (RF.root (G.tail e)) (G.tail e))

noncomputable def coreDetourFlow (m : ℕ) (w : ℕ → ℝ) (f : ℕ) : ℝ :=
  ∑ e ∈ (C.activeCore m).E, w e * edgeDetourFlow (C.G m) (C.activeLSF m).F e f

/-- Pure-circulation one-step lift of a circulation `w` on `𝒞(G_m, F_m)` to `G_m`. -/
noncomputable def liftFlow (m : ℕ) (w : ℕ → ℝ) : ℕ → ℝ :=
  (fun f => if f ∈ (C.activeCore m).E then w f else 0) + C.coreDetourFlow m w

lemma edgeDetourFlow_mem_E {G : MGraph} {RF : RootedForest} {e f : ℕ}
    (hf : edgeDetourFlow G RF e f ≠ 0) : f ∈ RF.F.E := by
  unfold edgeDetourFlow at hf
  split_ifs at hf
  · exact walkFlow_forestPath_mem_E hf
  · by_contra hnot
    have h1 : walkFlow (RF.F.forestPath (G.head e) (RF.root (G.head e))) f = 0 := by
      by_contra hne; exact hnot (walkFlow_forestPath_mem_E hne)
    have h2 : walkFlow (RF.F.forestPath (RF.root (G.tail e)) (G.tail e)) f = 0 := by
      by_contra hne; exact hnot (walkFlow_forestPath_mem_E hne)
    change walkFlow _ f + walkFlow _ f ≠ 0 at hf
    exact hf (by simp [h1, h2])

lemma coreDetourFlow_eq_zero_of_not_mem {m : ℕ} (w : ℕ → ℝ) {f : ℕ}
    (hf : f ∉ (C.activeLSF m).F.F.E) :
    C.coreDetourFlow m w f = 0 := by
  unfold coreDetourFlow
  refine Finset.sum_eq_zero fun e _ => ?_
  have h0 : edgeDetourFlow (C.G m) (C.activeLSF m).F e f = 0 := by
    by_contra hne
    exact hf (edgeDetourFlow_mem_E hne)
  rw [h0, mul_zero]

lemma isCirculation_of_isSubgraph {H G : MGraph} (hHG : H.IsSubgraph G)
    (hG : G.IsValid) {f : ℕ → ℝ} (hf : G.IsCirculation f) (hsupp : ∀ e, e ∉ G.E → f e = 0) :
    H.IsCirculation f := by
  intro v _
  unfold MGraph.demand
  rw [← Finset.sum_subset hHG.2.1 (fun e _ heG => by rw [hsupp e heG, mul_zero])]
  have hcong : ∑ e ∈ G.E, H.b e v * f e = ∑ e ∈ G.E, G.b e v * f e := by
    refine Finset.sum_congr rfl fun e he => ?_
    have hEnd := hHG.2.2 e he
    simp [MGraph.b, hEnd.1, hEnd.2]
  rw [hcong]
  by_cases hv : v ∈ G.V
  · exact hf v hv
  · refine Finset.sum_eq_zero fun e he => ?_
    have hEnds := hG e he
    have hne1 : v ≠ G.tail e := fun h => hv (h ▸ hEnds.1)
    have hne2 : v ≠ G.head e := fun h => hv (h ▸ hEnds.2)
    rw [MGraph.b_eq_zero_of_ne G hne1 hne2, zero_mul]

lemma isCirculation_subgraph_of_supp {G F : MGraph} (hSub : G.IsSubgraph F)
    {f : ℕ → ℝ} (hf : G.IsCirculation f) (hsupp : ∀ e, e ∉ F.E → f e = 0) :
    F.IsCirculation f := by
  intro v hv
  have hvG : v ∈ G.V := hSub.1 hv
  have hdem := hf v hvG
  unfold MGraph.demand at hdem ⊢
  rw [← Finset.sum_subset hSub.2.1 (fun e _ heF => by rw [hsupp e heF, mul_zero])] at hdem
  have hcong : ∑ e ∈ F.E, F.b e v * f e = ∑ e ∈ F.E, G.b e v * f e := by
    refine Finset.sum_congr rfl fun e he => ?_
    have hEnd := hSub.2.2 e he
    simp [MGraph.b, hEnd.1, hEnd.2]
  rw [hcong]
  exact hdem

private lemma demand_edgeDetourFlow {G : MGraph} {L : LSF}
    (hRF : L.F.IsRootedSpanningForestOf G) (hSub : G.IsSubgraph L.F.F)
    (hG : G.IsValid) {e : ℕ} (he : e ∈ (coreGraph G L).E) (v : ℕ) :
    G.demand (edgeDetourFlow G L.F e) v = -G.b e v + (coreGraph G L).b e v := by
  have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  have hEnds := hG e heG
  have hu := root_mem_R hRF hEnds.1
  have hv := root_mem_R hRF hEnds.2
  unfold edgeDetourFlow
  split_ifs with hroot
  · have hconn : L.F.F.Connected (G.head e) (G.tail e) :=
      connected_of_root_eq hRF hEnds.2 hEnds.1 hroot.symm
    have hw := demand_walkFlow (MGraph.isWalk_of_isSubgraph hSub (MGraph.isWalk_forestPath hconn)) v
    have hself : (coreGraph G L).b e v = 0 := MGraph.b_self _ hroot v
    rw [hw, hself, add_zero]
    simp [MGraph.b]
  · have hW1 := MGraph.isWalk_of_isSubgraph hSub (MGraph.isWalk_forestPath hv.2)
    have hW2 := MGraph.isWalk_of_isSubgraph hSub (MGraph.isWalk_forestPath (MGraph.connected_symm hu.2))
    have h1 := demand_walkFlow hW1 v
    have h2 := demand_walkFlow hW2 v
    rw [MGraph.demand_add, h1, h2]
    simp only [MGraph.b, coreGraph]
    by_cases h1 : v = G.head e <;> by_cases h2 : v = G.tail e <;>
      by_cases h3 : v = L.F.root (G.head e) <;> by_cases h4 : v = L.F.root (G.tail e) <;>
      simp [h1, h2, h3, h4] <;> ring

lemma demand_coreDetourFlow {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {m : ℕ} (hm : m ≤ C.d) {w : ℕ → ℝ} (hw : (C.activeCore m).IsCirculation w) (v : ℕ) :
    (C.G m).demand (C.coreDetourFlow m w) v =
      -(C.G m).demand (fun f => if f ∈ (C.activeCore m).E then w f else 0) v := by
  have hGm := C.G_isValid hH m hm
  have hRF := (C.activeLSF_holds hH hm).2.1
  have hSubm := hSub m hm
  have hlin : (C.G m).demand (C.coreDetourFlow m w) v =
      ∑ e ∈ (C.activeCore m).E, w e * (C.G m).demand (edgeDetourFlow (C.G m) (C.activeLSF m).F e) v := by
    unfold MGraph.demand coreDetourFlow
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => by ring
  rw [hlin]
  have hsplit : ∑ e ∈ (C.activeCore m).E,
      w e * (C.G m).demand (edgeDetourFlow (C.G m) (C.activeLSF m).F e) v =
      ∑ e ∈ (C.activeCore m).E, (-(C.G m).b e v * w e + (C.activeCore m).b e v * w e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [demand_edgeDetourFlow hRF hSubm hGm he v]
    change w e * (-(C.G m).b e v + (C.activeCore m).b e v) = _
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have hfirst : ∑ e ∈ (C.activeCore m).E, -(C.G m).b e v * w e =
      -(C.G m).demand (fun f => if f ∈ (C.activeCore m).E then w f else 0) v := by
    unfold MGraph.demand
    rw [← Finset.sum_neg_distrib]
    have hcong : ∑ e ∈ (C.activeCore m).E, -(C.G m).b e v * w e =
        ∑ e ∈ (C.activeCore m).E, -((C.G m).b e v * if e ∈ (C.activeCore m).E then w e else 0) :=
      Finset.sum_congr rfl fun e he => by simp only [he, ↓reduceIte]; ring
    rw [hcong]
    exact Finset.sum_subset (Finset.sdiff_subset : (C.activeCore m).E ⊆ (C.G m).E)
      fun e _ heNot => by simp [heNot]
  have hsecond : ∑ e ∈ (C.activeCore m).E, (C.activeCore m).b e v * w e = 0 := by
    by_cases hvR : v ∈ (C.activeLSF m).F.R
    · exact hw v hvR
    · refine Finset.sum_eq_zero fun e he => ?_
      have heGm : e ∈ (C.G m).E := (Finset.mem_sdiff.mp he).1
      have hEnds := hGm e heGm
      have hne1 : v ≠ (C.activeCore m).tail e := fun h =>
        hvR (h ▸ (root_mem_R hRF hEnds.1).1)
      have hne2 : v ≠ (C.activeCore m).head e := fun h =>
        hvR (h ▸ (root_mem_R hRF hEnds.2).1)
      rw [MGraph.b_eq_zero_of_ne _ hne1 hne2, zero_mul]
  rw [hfirst, hsecond, add_zero]

lemma isCirculation_liftFlow {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {m : ℕ} (hm : m ≤ C.d) {w : ℕ → ℝ} (hw : (C.activeCore m).IsCirculation w) :
    (C.G m).IsCirculation (C.liftFlow m w) := by
  intro v _
  change (C.G m).demand ((fun f => if f ∈ (C.activeCore m).E then w f else 0) + C.coreDetourFlow m w) v = 0
  rw [MGraph.demand_add, demand_coreDetourFlow C hH hSub hm hw v]
  ring

lemma liftFlow_eq_of_not_mem_F {m : ℕ} (w : ℕ → ℝ) {f : ℕ} (hf : f ∉ (C.activeLSF m).F.F.E) :
    C.liftFlow m w f = if f ∈ (C.activeCore m).E then w f else 0 := by
  change (if f ∈ (C.activeCore m).E then w f else 0) + C.coreDetourFlow m w f = _
  rw [C.coreDetourFlow_eq_zero_of_not_mem w hf, add_zero]

lemma liftFlow_eq_zero_of_not_mem_G {m : ℕ} (hSub : (C.G m).IsSubgraph (C.activeLSF m).F.F)
    (w : ℕ → ℝ) {f : ℕ} (hf : f ∉ (C.G m).E) :
    C.liftFlow m w f = 0 := by
  have hfCore : f ∉ (C.activeCore m).E := fun h => hf (Finset.mem_sdiff.mp h).1
  have hfF : f ∉ (C.activeLSF m).F.F.E := fun h => hf (hSub.2.1 h)
  rw [C.liftFlow_eq_of_not_mem_F w hfF]
  simp [hfCore]

lemma walkFlow_liftWalk_eq_liftFlow {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {m r₀ : ℕ} (hm : m ≤ C.d) {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)}
    (hW : (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs)) :
    ∀ f, walkFlow (C.liftWalk m (x₀ :: xs)) f = C.liftFlow m (walkFlow (x₀ :: xs)) f := by
  have hLift := C.liftWalk_isClosedWalk hH hSub hm hW
  have hc1 : (C.G m).IsCirculation (walkFlow (C.liftWalk m (x₀ :: xs))) :=
    isCirculation_walkFlow_of_closed hLift.1
  have hwCore : (C.activeCore m).IsCirculation (walkFlow (x₀ :: xs)) :=
    isCirculation_walkFlow_of_closed hW
  have hc2 : (C.G m).IsCirculation (C.liftFlow m (walkFlow (x₀ :: xs))) :=
    C.isCirculation_liftFlow hH hSub hm hwCore
  have hOut : ∀ f, f ∉ (C.activeLSF m).F.F.E →
      walkFlow (C.liftWalk m (x₀ :: xs)) f = C.liftFlow m (walkFlow (x₀ :: xs)) f := by
    intro f hfF
    have hst : walkFlow (C.liftWalk m (x₀ :: xs)) f = walkFlow (x₀ :: xs) f := by
      simpa [liftWalk, stitchCycle, walkFlow_stitchAux] using
        congrArg (walkFlow (x₀ :: xs) f + ·)
          (stitchTreeFlowAux_eq_zero_of_not_mem (G := C.G m) (C.G m |>.src x₀) xs x₀ hfF)
    rw [hst, C.liftFlow_eq_of_not_mem_F _ hfF]
    by_cases hfCore : f ∈ (C.activeCore m).E
    · simp [hfCore]
    · have hfW : f ∉ walkEdges (x₀ :: xs) := fun hmem =>
        hfCore (mem_E_of_mem_walkEdges hW hmem)
      simp [hfCore, walkFlow_eq_zero_of_not_mem hfW]
  let d : ℕ → ℝ := fun f => walkFlow (C.liftWalk m (x₀ :: xs)) f - C.liftFlow m (walkFlow (x₀ :: xs)) f
  have hdCircG : (C.G m).IsCirculation d := MGraph.isCirculation_sub hc1 hc2
  have hdsupp : ∀ f, f ∉ (C.activeLSF m).F.F.E → d f = 0 := fun f hfF =>
    sub_eq_zero.mpr (hOut f hfF)
  have hdCircF : (C.activeLSF m).F.F.IsCirculation d :=
    isCirculation_subgraph_of_supp (hSub m hm) hdCircG hdsupp
  have hdZero : ∀ f ∈ (C.activeLSF m).F.F.E, d f = 0 :=
    MGraph.isCirculation_eq_zero_of_isForest (C.activeLSF_holds hH hm).2.1.1 hdCircF
  intro f
  by_cases hfF : f ∈ (C.activeLSF m).F.F.E
  · exact sub_eq_zero.mp (hdZero f hfF)
  · exact hOut f hfF

end CyclesAndLifting

/-- Iteratively lifting a closed walk from level `m` (`m ≤ d`) down through `m - 1, …, 0`
to `G_0` ([chen2022maximum] Lemma 7.12 / 7.13). -/
noncomputable def iterLift (C : TreeChain) : ℕ → List (ℕ × Bool) → List (ℕ × Bool)
  | 0, W => C.liftWalk 0 W
  | m + 1, W => C.iterLift m (C.liftWalk (m + 1) W)

/-- Iterated pure-circulation lifting of a circulation from level `m` down to `G_0`. -/
noncomputable def iterLiftFlow (C : TreeChain) : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, w => C.liftFlow 0 w
  | m + 1, w => C.iterLiftFlow m (C.liftFlow (m + 1) w)

section IterLiftLemmas

variable (C : TreeChain)

lemma iterLift_isClosedWalk {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    ∀ m ≤ C.d, ∀ {r₀ : ℕ} {W : List (ℕ × Bool)}, W ≠ [] → (C.activeCore m).IsWalk r₀ r₀ W →
      ∃ u₀, (C.G 0).IsWalk u₀ u₀ (C.iterLift m W) ∧ C.iterLift m W ≠ [] := by
  intro m
  induction m with
  | zero =>
    intro hm r₀ W hne hW
    cases W with
    | nil => exact absurd rfl hne
    | cons x₀ xs =>
      have h := C.liftWalk_isClosedWalk hH hSub hm hW
      exact ⟨(C.G 0).src x₀, h.1, h.2⟩
  | succ k ih =>
    intro hk r₀ W hne hW
    cases W with
    | nil => exact absurd rfl hne
    | cons x₀ xs =>
      have hLift := C.liftWalk_isClosedWalk hH hSub hk hW
      have hSubCore := C.G_succ_isSubgraph_core hH hk
      have hWalkCore := MGraph.isWalk_of_isSubgraph hSubCore hLift.1
      exact ih (Nat.le_of_lt hk) hLift.2 hWalkCore

lemma iterLift_walkFlow_nonTree {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    ∀ m ≤ C.d, ∀ {r₀ : ℕ} {W : List (ℕ × Bool)}, W ≠ [] → (C.activeCore m).IsWalk r₀ r₀ W →
      ∀ e₀, e₀ ∉ C.chainTree.E → walkFlow (C.iterLift m W) e₀ = walkFlow W e₀ := by
  intro m
  induction m with
  | zero =>
    intro hm r₀ W hne hW e₀ heNotT
    cases W with
    | nil => exact absurd rfl hne
    | cons x₀ xs =>
      have hne0 : e₀ ∉ (C.activeLSF 0).F.F.E := by
        intro hmem; apply heNotT
        simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
        exact ⟨0, Nat.succ_pos _, hmem⟩
      rw [iterLift, C.walkFlow_liftWalk_eq_liftFlow hH hSub hm hW, C.liftFlow_eq_of_not_mem_F _ hne0]
      by_cases hCore : e₀ ∈ (C.activeCore 0).E
      · simp [hCore]
      · have hWnot : e₀ ∉ walkEdges (x₀ :: xs) := fun h => hCore (mem_E_of_mem_walkEdges hW h)
        simp [hCore, walkFlow_eq_zero_of_not_mem hWnot]
  | succ k ih =>
    intro hk r₀ W hne hW e₀ heNotT
    cases W with
    | nil => exact absurd rfl hne
    | cons x₀ xs =>
      have hLift := C.liftWalk_isClosedWalk hH hSub hk hW
      have hSubCore := C.G_succ_isSubgraph_core hH hk
      have hWalkCore := MGraph.isWalk_of_isSubgraph hSubCore hLift.1
      rw [iterLift, ih (Nat.le_of_lt hk) hLift.2 hWalkCore e₀ heNotT]
      have hneF : e₀ ∉ (C.activeLSF (k + 1)).F.F.E := by
        intro hmem; apply heNotT
        simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
        exact ⟨k + 1, Nat.lt_succ_of_le hk, hmem⟩
      rw [C.walkFlow_liftWalk_eq_liftFlow hH hSub hk hW, C.liftFlow_eq_of_not_mem_F _ hneF]
      by_cases hCore : e₀ ∈ (C.activeCore (k + 1)).E
      · simp [hCore]
      · have hWnot : e₀ ∉ walkEdges (x₀ :: xs) := fun h => hCore (mem_E_of_mem_walkEdges hW h)
        simp [hCore, walkFlow_eq_zero_of_not_mem hWnot]

lemma iterLift_fundChainCycleAt_walkFlow_eq {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    ∀ e₀, walkFlow (C.iterLift i (C.sparsifierCycle i e)) e₀ =
      walkFlow (C.fundChainCycleAt i e) e₀ := by
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hne : C.sparsifierCycle i e ≠ [] := List.cons_ne_nil _ _
  obtain ⟨u₀, hIterWalk, _⟩ := C.iterLift_isClosedWalk hH hSub i hi hne hClosed
  have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hi he
  have hc1 := isCirculation_walkFlow_of_closed hIterWalk
  have hc2 := isCirculation_walkFlow_of_closed hFundWalk
  have hNonTree : ∀ e₀, e₀ ∉ C.chainTree.E →
      walkFlow (C.iterLift i (C.sparsifierCycle i e)) e₀ = walkFlow (C.fundChainCycleAt i e) e₀ := by
    intro e₀ heNotT
    rw [C.iterLift_walkFlow_nonTree hH hSub i hi hne hClosed e₀ heNotT]
    unfold fundChainCycleAt stitchCycle sparsifierCycle
    rw [walkFlow_stitchAux, stitchTreeFlowAux_eq_zero_of_not_mem _ _ _ heNotT, add_zero]
  let d : ℕ → ℝ := fun e₀ =>
    walkFlow (C.iterLift i (C.sparsifierCycle i e)) e₀ - walkFlow (C.fundChainCycleAt i e) e₀
  have hdCircF : C.chainTree.IsCirculation d :=
    isCirculation_subgraph_of_supp (C.chainTree_isSubgraph hH hSub) (MGraph.isCirculation_sub hc1 hc2)
      fun e₀ heNotT => sub_eq_zero.mpr (hNonTree e₀ heNotT)
  have hdZero := MGraph.isCirculation_eq_zero_of_isForest (C.chainTree_isForest hH hSub) hdCircF
  intro e₀
  by_cases heT : e₀ ∈ C.chainTree.E
  · exact sub_eq_zero.mp (hdZero e₀ heT)
  · exact hNonTree e₀ heT

end IterLiftLemmas

end TreeChain

end MinCostFlow.Chain
