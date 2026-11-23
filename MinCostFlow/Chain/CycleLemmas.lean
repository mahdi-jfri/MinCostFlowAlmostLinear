module

public import MinCostFlow.Chain.Cycles
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cycle properties and good-cycle extraction (`lemma_7_12`, `lemma_7_13`, `lemma_7_15`, `lemma_A_2`)

This file proves the four main static theorems on fundamental chain cycles in a `TreeChain`
from [chen2022maximum] (arXiv:2203.00671v2, Section 7.2) and Appendix A.3 (pages 48–49):

* `lemma_7_12`: unconditional gradient correctness (`⟨g^{𝒞(G_i, F_i)}, a(e)⟩ = ⟨g, a^G(e^G)⟩`)
  using the component-root-potential repaired `coreGrad`, plus `chainGrad_eq_chainGradPaper_of_treesConnectEdges`
  showing agreement with Definition 5.6 when `TreesConnectEdges` holds (the paper's unshifted
  definition can fail when vertex splits disconnect `T_i`).
* `lemma_7_13`: length overestimates `⟨ℓ, |a^G(e^G)|⟩ ≤ wlen_{e^G}` (the paper's "Lemma 7.14"),
  proved unconditionally for flow norms via `liftFlow`.
* `lemma_7_15`: decomposition of any circulation `c` on `G` into fundamental chain cycles using
  `EmbedsSurviving`.
* `lemma_A_2` (Appendix A.3 Lemma A.2, page 48; [chen2022maximum] Lemma 7.16, the paper's
  "Lemma 7.17"): existence of a fundamental chain cycle achieving ratio at least
  `(1 / (σ + 1)) * |⟨g, c⟩| / ∑_{i=0}^d ‖w^{G_i}‖₁`, using `⟨ℓ, |a^G(e^G)|⟩` in the
  denominator via `lemma_7_13`.
-/

@[expose] public section

namespace MinCostFlow.Chain

namespace TreeChain

variable (C : TreeChain)

section Lemma712

/-- For Definition 5.6: at every level `i ≤ d`, the underlying forest `T_i` connects the endpoints
of every edge in `G_i`. This holds without vertex splits, and can fail when vertex splits add
isolated vertices to `T_i` (see `lemma_7_12_counterexample`). Under this condition, the repaired
`chainGrad` agrees with the paper's `chainGradPaper`. -/
def TreesConnectEdges : Prop :=
  ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, (C.activeLSF i).T.Connected ((C.G i).tail e) ((C.G i).head e)

lemma chainGrad_eq_chainGradPaper_of_treesConnectEdges {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hTrees : C.TreesConnectEdges)
    (hTSub : ∀ m ≤ C.d, (C.activeLSF m).T.E ⊆ (C.G m).E) :
    ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, C.chainGrad g i e = C.chainGradPaper g i e := by
  intro i
  induction i with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro hm e he
    have hm_lt : m < C.d := hm
    have hm_le : m ≤ C.d := Nat.le_of_lt hm_lt
    have heGm : e ∈ (C.G m).E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hm_lt he)).1
    have hprev : C.chainGrad g m e = C.chainGradPaper g m e := ih hm_le e heGm
    have hL := C.activeLSF_holds hH hm_le
    change coreGrad (C.G m) (C.activeLSF m) (C.chainGrad g m) e =
      coreGradPaper (C.G m) (C.activeLSF m) (C.chainGradPaper g m) e
    rw [coreGrad_eq_coreGradPaper_of_connected hL.1 _ (hTrees m hm_le e heGm)]
    unfold coreGradPaper
    rw [hprev]
    congr 1
    rw [walkInner_eq_sum_of_subset (forestPath_edges_subset ((C.G m).head e) ((C.G m).tail e)),
      walkInner_eq_sum_of_subset (forestPath_edges_subset ((C.G m).head e) ((C.G m).tail e))]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfGm : f ∈ (C.G m).E := hTSub m hm_le hf
    rw [ih hm_le f hfGm]

lemma chainGrad_succ_eq_chainGradPaper_of_treesConnectEdges {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hTrees : C.TreesConnectEdges)
    (hTSub : ∀ m ≤ C.d, (C.activeLSF m).T.E ⊆ (C.G m).E) :
    ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, C.chainGrad g (i + 1) e = C.chainGradPaper g (i + 1) e := by
  intro i hi e he
  have hL := C.activeLSF_holds hH hi
  have hbase := C.chainGrad_eq_chainGradPaper_of_treesConnectEdges hH hTrees hTSub (g := g) i hi
  change coreGrad (C.G i) (C.activeLSF i) (C.chainGrad g i) e =
    coreGradPaper (C.G i) (C.activeLSF i) (C.chainGradPaper g i) e
  rw [coreGrad_eq_coreGradPaper_of_connected hL.1 _ (hTrees i hi e he)]
  unfold coreGradPaper
  rw [hbase e he]
  congr 1
  rw [walkInner_eq_sum_of_subset (forestPath_edges_subset ((C.G i).head e) ((C.G i).tail e)),
    walkInner_eq_sum_of_subset (forestPath_edges_subset ((C.G i).head e) ((C.G i).tail e))]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hfGm : f ∈ (C.G i).E := hTSub i hi hf
  rw [hbase f hfGm]

private lemma walkInner_coreGrad_eq (G : MGraph) (L : LSF) (g : ℕ → ℝ) :
    ∀ (W : List (ℕ × Bool)),
      walkInner (coreGrad G L g) W =
        walkInner g W +
          (W.map fun x => treeRootPot L.T g (G.dst x) - treeRootPot L.T g (G.src x)).sum
  | [] => by simp [walkInner_nil]
  | x :: xs => by
    have ih := walkInner_coreGrad_eq G L g xs
    rw [walkInner_cons, walkInner_cons g x xs, ih]
    have hsingle : walkInner (coreGrad G L g) [x] =
        walkInner g [x] + (treeRootPot L.T g (G.dst x) - treeRootPot L.T g (G.src x)) := by
      cases hx2 : x.2 <;>
        simp [walkInner_singleton, hx2, coreGrad, MGraph.dst, MGraph.src] <;> ring
    rw [hsingle]
    simp only [List.map_cons, List.sum_cons]
    ring

private lemma walkInner_forestPath_F_eq_sub_treeRootPot (L : LSF) (hT : L.T.IsForest)
    (hTF : L.T.IsSubgraph L.F.F) (g : ℕ → ℝ) {a b : ℕ} (hab : L.F.F.Connected a b) :
    walkInner g (MGraph.forestPath L.F.F a b) =
      treeRootPot L.T g a - treeRootPot L.T g b := by
  have habT : L.T.Connected a b := MGraph.connected_of_isSubgraph hTF hab
  have hWalkT : L.T.IsWalk a b (MGraph.forestPath L.F.F a b) :=
    MGraph.isWalk_of_isSubgraph hTF (MGraph.isWalk_forestPath hab)
  have hflow : ∀ f, walkFlow (MGraph.forestPath L.F.F a b) f =
      walkFlow (MGraph.forestPath L.T a b) f := fun f =>
    walkFlow_eq_of_isForest hT hWalkT (MGraph.isWalk_forestPath habT) f
  rw [walkInner_eq_of_walkFlow_eq g hflow]
  exact walkInner_forestPath_eq_sub_treeRootPot hT habT g

private lemma walkInner_stitchAux (G : MGraph) (L : LSF) (hT : L.T.IsForest)
    (hTF : L.T.IsSubgraph L.F.F) (g : ℕ → ℝ) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      AdjConn G L.F.F target x xs →
      walkInner g (stitchAux G L.F.F target x xs) =
        walkInner g (x :: xs) +
          ((x :: xs).map fun y => treeRootPot L.T g (G.dst y) - treeRootPot L.T g (G.src y)).sum +
          treeRootPot L.T g (G.src x) - treeRootPot L.T g target
  | [], x, hadj => by
    simp only [stitchAux, walkInner_append, walkInner_forestPath_F_eq_sub_treeRootPot L hT hTF g hadj,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  | y :: ys, x, hadj => by
    have ih := walkInner_stitchAux G L hT hTF g target ys y hadj.2
    simp only [stitchAux, List.append_assoc, walkInner_append]
    rw [walkInner_forestPath_F_eq_sub_treeRootPot L hT hTF g hadj.1, ih]
    rw [walkInner_cons g x (y :: ys)]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- One-step gradient correctness ([chen2022maximum] Lemma 7.12): lifting a closed walk `W`
from `𝒞(G_m, F_m)` into `G_m` preserves its inner product with `g`, unconditionally with the
repaired `coreGrad`. -/
lemma lemma_7_12_step {G : MGraph} {ℓ g : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {m r₀ : ℕ} (hm : m ≤ C.d) {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)}
    (hW : (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs)) :
    walkInner (coreGrad (C.G m) (C.activeLSF m) g) (x₀ :: xs) =
      walkInner g (C.liftWalk m (x₀ :: xs)) := by
  have hLm := C.activeLSF_holds hH hm
  have hT_forest := hLm.1
  have hTF := hLm.2.2.1
  have hRF := hLm.2.1
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
  have hst := walkInner_stitchAux (C.G m) (C.activeLSF m) hT_forest hTF g ((C.G m).src x₀) xs x₀ hadj
  have hcg := walkInner_coreGrad_eq (C.G m) (C.activeLSF m) g (x₀ :: xs)
  change _ = walkInner g (stitchAux (C.G m) (C.activeLSF m).F.F ((C.G m).src x₀) x₀ xs)
  rw [hst, hcg]
  ring

/-- Lemma 7.12 ([chen2022maximum] v2 Lemma 7.12): gradient correctness for fundamental chain
cycles `⟨g^{𝒞(G_i, F_i)}, a(e)⟩ = ⟨g, a^G(e^G)⟩`, proved unconditionally using the repaired
component-root-potential `coreGrad` (no `TreesConnectEdges` needed). -/
theorem lemma_7_12 {G : MGraph} {ℓ g : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) =
      walkInner g (C.fundChainCycleAt i e) := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hiter : ∀ m ≤ C.d, ∀ {r₀ : ℕ} {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)},
      (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs) →
      walkInner (C.chainGrad g (m + 1)) (x₀ :: xs) = walkInner g (C.iterLift m (x₀ :: xs)) := by
    intro m
    induction m with
    | zero =>
      intro hm r₀ x₀ xs hW
      exact C.lemma_7_12_step hH hm hW
    | succ k ih =>
      intro hk r₀ x₀ xs hW
      change walkInner (coreGrad (C.G (k + 1)) (C.activeLSF (k + 1)) (C.chainGrad g (k + 1))) (x₀ :: xs) = _
      rw [C.lemma_7_12_step hH hk hW]
      have hLift := C.liftWalk_isClosedWalk hH hSub hk hW
      have hWalkCore := MGraph.isWalk_of_isSubgraph (C.G_succ_isSubgraph_core hH hk) hLift.1
      cases hList : C.liftWalk (k + 1) (x₀ :: xs) with
      | nil => exact absurd hList hLift.2
      | cons y₀ ys =>
        rw [hList] at hWalkCore
        simpa [iterLift, hList] using ih (Nat.le_of_lt hk) hWalkCore
  rw [← walkInner_eq_of_walkFlow_eq g (C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hi he)]
  exact hiter i hi hClosed

end Lemma712

section Lemma713

lemma chainLen_pos {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) :
    ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, 0 < C.chainLen ℓ i e := by
  intro i
  induction i with
  | zero =>
    intro _ e he
    rw [hH.1] at he
    exact hℓ e he
  | succ k ih =>
    intro hk e he
    have heGk : e ∈ (C.G k).E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hk he)).1
    have hℓk := ih (Nat.le_of_lt hk)
    have hpos_k : 0 < C.chainLen ℓ k e := hℓk e heGk
    have hnonneg_k : ∀ f ∈ (C.G k).E, 0 ≤ C.chainLen ℓ k f := fun f hf => le_of_lt (hℓk f hf)
    have h1 : 1 ≤ (C.activeLSF k).wstr e :=
      le_trans (one_le_stretch (hSub k (Nat.le_of_lt hk)) hnonneg_k heGk)
        ((C.activeLSF_holds hH (Nat.le_of_lt hk)).2.2.2 e heGk).1
    change 0 < (C.activeLSF k).wstr e * C.chainLen ℓ k e
    exact mul_pos (lt_of_lt_of_le zero_lt_one h1) hpos_k

private lemma lnorm_edgeDetourFlow_le {G : MGraph} {L : LSF} {ℓ' : ℕ → ℝ} {σ : ℝ}
    (hG : G.IsValid) (hL : L.Holds G ℓ' σ) (hSub : G.IsSubgraph L.F.F)
    (hℓ' : ∀ e ∈ G.E, 0 < ℓ' e) {e : ℕ} (he : e ∈ (coreGraph G L).E) :
    ∑ f ∈ L.F.F.E, ℓ' f * |edgeDetourFlow G L.F e f| ≤ (L.wstr e - 1) * ℓ' e := by
  have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  have hEnds := hG e heG
  have hRF := hL.2.1
  have hℓ'e : 0 < ℓ' e := hℓ' e heG
  have hstr := (hL.2.2.2 e heG).1
  unfold RootedForest.stretch at hstr
  dsimp only at hstr
  unfold edgeDetourFlow
  split_ifs with hroot
  · simp only [hroot, ↓reduceIte] at hstr
    have hfp : walkLength ℓ' (L.F.F.forestPath (G.head e) (G.tail e)) =
        walkLength ℓ' (L.F.F.forestPath (G.tail e) (G.head e)) :=
      walkLength_forestPath_symm hRF.1
        (connected_of_root_eq hRF hEnds.1 hEnds.2 hroot) ℓ'
    have hsum : ∑ f ∈ L.F.F.E, ℓ' f * |walkFlow (L.F.F.forestPath (G.head e) (G.tail e)) f| =
        walkLength ℓ' (L.F.F.forestPath (G.head e) (G.tail e)) :=
      (walkLength_eq_sum_of_subset (forestPath_edges_subset _ _)).symm
    rw [hsum, hfp]
    have hdiv : walkLength ℓ' (L.F.F.forestPath (G.tail e) (G.head e)) / ℓ' e ≤ L.wstr e - 1 := by
      linarith
    exact (div_le_iff₀ hℓ'e).mp hdiv
  · simp only [hroot, ↓reduceIte] at hstr
    have htri : ∑ f ∈ L.F.F.E,
        ℓ' f * |walkFlow (L.F.F.forestPath (G.head e) (L.F.root (G.head e))) f +
          walkFlow (L.F.F.forestPath (L.F.root (G.tail e)) (G.tail e)) f| ≤
        walkLength ℓ' (L.F.F.forestPath (G.head e) (L.F.root (G.head e))) +
          walkLength ℓ' (L.F.F.forestPath (L.F.root (G.tail e)) (G.tail e)) := by
      rw [walkLength_eq_sum_of_subset (forestPath_edges_subset (G.head e) (L.F.root (G.head e))),
        walkLength_eq_sum_of_subset (forestPath_edges_subset (L.F.root (G.tail e)) (G.tail e)),
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun f hfF => ?_
      have hℓ'f : 0 ≤ ℓ' f := le_of_lt (hℓ' f (hSub.2.1 hfF))
      calc
        ℓ' f * |walkFlow _ f + walkFlow _ f| ≤ ℓ' f * (|walkFlow _ f| + |walkFlow _ f|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hℓ'f
        _ = ℓ' f * |walkFlow _ f| + ℓ' f * |walkFlow _ f| := mul_add _ _ _
    have hsym := walkLength_forestPath_symm hRF.1 (root_mem_R hRF hEnds.1).2 ℓ'
    have hdiv : (walkLength ℓ' (L.F.F.forestPath (G.tail e) (L.F.root (G.tail e))) +
        walkLength ℓ' (L.F.F.forestPath (G.head e) (L.F.root (G.head e)))) / ℓ' e ≤ L.wstr e - 1 := by
      linarith
    have hle := (div_le_iff₀ hℓ'e).mp hdiv
    dsimp only [Pi.add_apply]
    linarith [htri, hsym]

/-- One-step length bound ([chen2022maximum] Lemma 7.13): for any circulation `w` on
`𝒞(G_m, F_m)`, its flow-lifted circulation `liftFlow m w` in `G_m` satisfies
`⟨ℓ', |liftFlow m w|⟩ ≤ ⟨coreLen L_m ℓ', |w|⟩`. -/
lemma lemma_7_13_step {G : MGraph} {ℓ ℓ' : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {m : ℕ} (hm : m ≤ C.d)
    (hL' : (C.activeLSF m).Holds (C.G m) ℓ' σ) (hℓ' : ∀ e ∈ (C.G m).E, 0 < ℓ' e)
    (w : ℕ → ℝ) :
    (C.G m).lnorm ℓ' (C.liftFlow m w) ≤
      (C.activeCore m).lnorm (coreLen (C.activeLSF m) ℓ') w := by
  have hGm := C.G_isValid hH m hm
  have hSubm := hSub m hm
  have hdisj : Disjoint (C.activeCore m).E (C.activeLSF m).F.F.E := disjoint_sdiff_self_left
  have hunion : (C.activeCore m).E ∪ (C.activeLSF m).F.F.E = (C.G m).E :=
    Finset.sdiff_union_of_subset hSubm.2.1
  unfold MGraph.lnorm
  rw [← hunion, Finset.sum_union hdisj]
  have hfirst : ∑ f ∈ (C.activeCore m).E, ℓ' f * |C.liftFlow m w f| =
      ∑ e ∈ (C.activeCore m).E, ℓ' e * |w e| := by
    refine Finset.sum_congr rfl fun e he => ?_
    have heNotF : e ∉ (C.activeLSF m).F.F.E := (Finset.mem_sdiff.mp he).2
    rw [C.liftFlow_eq_of_not_mem_F w heNotF]
    simp only [he, ↓reduceIte]
  have hsecond : ∑ f ∈ (C.activeLSF m).F.F.E, ℓ' f * |C.liftFlow m w f| ≤
      ∑ e ∈ (C.activeCore m).E, |w e| * ((C.activeLSF m).wstr e - 1) * ℓ' e := by
    have hpt : ∀ f ∈ (C.activeLSF m).F.F.E,
        ℓ' f * |C.liftFlow m w f| ≤
          ∑ e ∈ (C.activeCore m).E, ℓ' f * (|w e| * |edgeDetourFlow (C.G m) (C.activeLSF m).F e f|) := by
      intro f hfF
      have hfNotCore : f ∉ (C.activeCore m).E := fun h => (Finset.mem_sdiff.mp h).2 hfF
      have heq : C.liftFlow m w f = ∑ e ∈ (C.activeCore m).E, w e * edgeDetourFlow (C.G m) (C.activeLSF m).F e f := by
        change (if f ∈ (C.activeCore m).E then w f else 0) + C.coreDetourFlow m w f = _
        simp [hfNotCore, coreDetourFlow]
      rw [heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hℓ' f (hSubm.2.1 hfF)))
      calc
        |∑ e ∈ (C.activeCore m).E, w e * edgeDetourFlow (C.G m) (C.activeLSF m).F e f|
            ≤ ∑ e ∈ (C.activeCore m).E, |w e * edgeDetourFlow (C.G m) (C.activeLSF m).F e f| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e ∈ (C.activeCore m).E, |w e| * |edgeDetourFlow (C.G m) (C.activeLSF m).F e f| := by
          refine Finset.sum_congr rfl fun e _ => abs_mul _ _
    calc
      ∑ f ∈ (C.activeLSF m).F.F.E, ℓ' f * |C.liftFlow m w f|
          ≤ ∑ f ∈ (C.activeLSF m).F.F.E, ∑ e ∈ (C.activeCore m).E,
              ℓ' f * (|w e| * |edgeDetourFlow (C.G m) (C.activeLSF m).F e f|) :=
        Finset.sum_le_sum hpt
      _ = ∑ e ∈ (C.activeCore m).E, ∑ f ∈ (C.activeLSF m).F.F.E,
              |w e| * (ℓ' f * |edgeDetourFlow (C.G m) (C.activeLSF m).F e f|) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => by ring
      _ ≤ ∑ e ∈ (C.activeCore m).E, |w e| * ((C.activeLSF m).wstr e - 1) * ℓ' e := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [← Finset.mul_sum, mul_assoc]
        exact mul_le_mul_of_nonneg_left (lnorm_edgeDetourFlow_le hGm hL' hSubm hℓ' he) (abs_nonneg _)
  calc
    (∑ f ∈ (C.activeCore m).E, ℓ' f * |C.liftFlow m w f|) +
        ∑ f ∈ (C.activeLSF m).F.F.E, ℓ' f * |C.liftFlow m w f|
        ≤ (∑ e ∈ (C.activeCore m).E, ℓ' e * |w e|) +
            ∑ e ∈ (C.activeCore m).E, |w e| * ((C.activeLSF m).wstr e - 1) * ℓ' e :=
      add_le_add (le_of_eq hfirst) hsecond
    _ = ∑ e ∈ (C.activeCore m).E, coreLen (C.activeLSF m) ℓ' e * |w e| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      unfold coreLen; ring

private lemma sum_map_eq_sum_walkCount (L : ℕ → ℝ) :
    ∀ (W : List (ℕ × Bool)) {S : Finset ℕ}, walkEdges W ⊆ S →
      (W.map fun x => L x.1).sum = ∑ f ∈ S, L f * walkCount W f
  | [], S, _ => by simp [walkCount]
  | x :: xs, S, hsub => by
    have hxS : x.1 ∈ S := hsub (by simp [walkEdges])
    have hxsSub : walkEdges xs ⊆ S := fun f hf => hsub (by simp [walkEdges] at hf ⊢; exact Or.inr hf)
    have ih := sum_map_eq_sum_walkCount L xs hxsSub
    have hstep : ∀ f, walkCount (x :: xs) f = (if x.1 = f then (1 : ℝ) else 0) + walkCount xs f := fun f => by
      by_cases h : x.1 = f <;> simp [walkCount, List.countP_cons, h] <;> ring
    simp only [List.map_cons, List.sum_cons, ih, hstep, mul_add, Finset.sum_add_distrib]
    have hsingle : (∑ f ∈ S, L f * if x.1 = f then (1 : ℝ) else 0) = L x.1 := by
      rw [Finset.sum_eq_single x.1]
      · simp
      · intro f _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd hxS hnot
    rw [hsingle]

/-- Lemma 7.13 ([chen2022maximum] v2 Lemma 7.13; paper's "Lemma 7.14"): for any edge `e`
at level `i ≤ d`, `⟨ℓ, |a^G(e^G)|⟩ ≤ wlen_{e^G}`. -/
theorem lemma_7_13_at {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e)
    {i e : ℕ} (hi : i ≤ C.d) (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    walkLength ℓ (C.fundChainCycleAt i e) ≤ C.wlenAt ℓ i e := by
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hiter_lnorm : ∀ m ≤ C.d, ∀ {r₀ : ℕ} {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)},
      (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs) →
      (C.G 0).lnorm ℓ (walkFlow (C.iterLift m (x₀ :: xs))) ≤
        (C.activeCore m).lnorm (C.chainLen ℓ (m + 1)) (walkFlow (x₀ :: xs)) := by
    intro m
    induction m with
    | zero =>
      intro hm r₀ x₀ xs hW
      have hℓ0 : ∀ f ∈ (C.G 0).E, 0 < C.chainLen ℓ 0 f := C.chainLen_pos hH hSub hℓ 0 hm
      have hStep := C.lemma_7_13_step hH hSub hm (C.activeLSF_holds hH hm) hℓ0 (walkFlow (x₀ :: xs))
      have hFlow := C.walkFlow_liftWalk_eq_liftFlow hH hSub hm hW
      have hLiftEq : ∀ f, walkFlow (C.iterLift 0 (x₀ :: xs)) f = C.liftFlow 0 (walkFlow (x₀ :: xs)) f :=
        fun f => hFlow f
      calc
        (C.G 0).lnorm ℓ (walkFlow (C.iterLift 0 (x₀ :: xs)))
            = (C.G 0).lnorm (C.chainLen ℓ 0) (C.liftFlow 0 (walkFlow (x₀ :: xs))) := by
          unfold MGraph.lnorm
          refine Finset.sum_congr rfl fun f _ => by rw [chainLen, hLiftEq f]
        _ ≤ (C.activeCore 0).lnorm (C.chainLen ℓ 1) (walkFlow (x₀ :: xs)) := hStep
    | succ k ih =>
      intro hk r₀ x₀ xs hW
      have hLift := C.liftWalk_isClosedWalk hH hSub hk hW
      have hSubCore := C.G_succ_isSubgraph_core hH hk
      have hWalkCore := MGraph.isWalk_of_isSubgraph hSubCore hLift.1
      have hFlow := C.walkFlow_liftWalk_eq_liftFlow hH hSub hk hW
      have hIH : (C.G 0).lnorm ℓ (walkFlow (C.iterLift (k + 1) (x₀ :: xs))) ≤
          (C.activeCore k).lnorm (C.chainLen ℓ (k + 1)) (walkFlow (C.liftWalk (k + 1) (x₀ :: xs))) := by
        cases hList : C.liftWalk (k + 1) (x₀ :: xs) with
        | nil => exact absurd hList hLift.2
        | cons y₀ ys =>
          have hWalkCore' : (C.activeCore k).IsWalk _ _ (y₀ :: ys) := hList ▸ hWalkCore
          simpa [iterLift, hList] using ih (Nat.le_of_lt hk) hWalkCore'
      have hLnormEq : (C.activeCore k).lnorm (C.chainLen ℓ (k + 1)) (walkFlow (C.liftWalk (k + 1) (x₀ :: xs))) =
          (C.G (k + 1)).lnorm (C.chainLen ℓ (k + 1)) (C.liftFlow (k + 1) (walkFlow (x₀ :: xs))) := by
        unfold MGraph.lnorm
        rw [← Finset.sum_subset hSubCore.2.1]
        · refine Finset.sum_congr rfl fun f _ => by rw [hFlow f]
        · intro f _ hfNot
          have hw0 : walkFlow (C.liftWalk (k + 1) (x₀ :: xs)) f = 0 :=
            walkFlow_eq_zero_of_not_mem fun hmem => hfNot (mem_E_of_mem_walkEdges hLift.1 hmem)
          simp [hw0]
      have hℓk1 := C.chainLen_pos hH hSub hℓ (k + 1) hk
      have hStep := C.lemma_7_13_step hH hSub hk (C.activeLSF_holds hH hk) hℓk1 (walkFlow (x₀ :: xs))
      exact le_trans hIH (hLnormEq ▸ hStep)
  have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hi he
  have hSubFund : walkEdges (C.fundChainCycleAt i e) ⊆ (C.G 0).E :=
    fun f hf => mem_E_of_mem_walkEdges hFundWalk hf
  have hSubSpars : walkEdges (C.sparsifierCycle i e) ⊆ (C.activeCore i).E :=
    fun f hf => mem_E_of_mem_walkEdges hClosed hf
  have hℓi1 : ∀ f ∈ (C.activeCore i).E, 0 ≤ C.chainLen ℓ (i + 1) f := by
    intro f hf
    have hfG : f ∈ (C.G i).E := (Finset.mem_sdiff.mp hf).1
    have hℓi := C.chainLen_pos hH hSub hℓ i hi f hfG
    have hLi := C.activeLSF_holds hH hi
    have hwstr := le_trans zero_le_one (le_trans (one_le_stretch (hSub i hi)
      (fun g hg => le_of_lt (C.chainLen_pos hH hSub hℓ i hi g hg)) hfG) (hLi.2.2.2 f hfG).1)
    exact mul_nonneg hwstr (le_of_lt hℓi)
  calc
    walkLength ℓ (C.fundChainCycleAt i e)
        = (C.G 0).lnorm ℓ (walkFlow (C.fundChainCycleAt i e)) :=
      walkLength_eq_lnorm_of_subset hSubFund
    _ = (C.G 0).lnorm ℓ (walkFlow (C.iterLift i (C.sparsifierCycle i e))) := by
      unfold MGraph.lnorm
      refine Finset.sum_congr rfl fun f _ => by
        rw [C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hi he f]
    _ ≤ (C.activeCore i).lnorm (C.chainLen ℓ (i + 1)) (walkFlow (C.sparsifierCycle i e)) :=
      hiter_lnorm i hi hClosed
    _ = walkLength (C.chainLen ℓ (i + 1)) (C.sparsifierCycle i e) :=
      (walkLength_eq_lnorm_of_subset hSubSpars).symm
    _ ≤ C.wlenAt ℓ i e := by
      unfold walkLength wlenAt
      rw [sum_map_eq_sum_walkCount (C.chainLen ℓ (i + 1)) (C.sparsifierCycle i e) Finset.Subset.rfl]
      refine Finset.sum_le_sum fun f hf =>
        mul_le_mul_of_nonneg_left (abs_walkFlow_le_walkCount _ f) (hℓi1 f (hSubSpars hf))

/-- Lemma 7.13 ([chen2022maximum] v2 Lemma 7.13; paper's "Lemma 7.14") indexed by off-tree edge
`e ∈ E(G) \ E(T^𝒢)`. -/
theorem lemma_7_13 {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) (hSpan : C.LastLevelSpans)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) {e : ℕ} (he : e ∈ G.E \ C.chainTree.E) :
    walkLength ℓ (C.fundChainCycle e) ≤ C.wlen ℓ e := by
  have he' : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
  have hlvl := C.mem_activeCore_diff_edgeLevel hH he'
  exact C.lemma_7_13_at hH hSub hSpan hℓ hlvl.1 hlvl.2

end Lemma713

section Lemma715AndA2

/-- Lemma 7.15 ([chen2022maximum] v2 Lemma 7.15): any circulation `c` on `G` decomposes into
a linear combination of the fundamental chain cycles `a^G(e^G)` indexed by level `i ≤ d`. -/
theorem lemma_7_15_levels {G : MGraph} {ℓ c : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) (hEmbSurv : C.EmbedsSurviving)
    (hCirc : G.IsCirculation c) :
    ∀ e₀ ∈ G.E,
      c e₀ = ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀ := by
  let y : ℕ → ℝ := fun e₀ =>
    ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
      C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀
  have hNonTree : ∀ e₀ ∈ (C.G 0).E \ C.chainTree.E, c e₀ = y e₀ := by
    intro e₀ he₀
    have hlvl := C.mem_activeCore_diff_edgeLevel hH he₀
    set k := C.edgeLevel e₀
    have hk_le : k ≤ C.d := hlvl.1
    have he₀Core : e₀ ∈ (C.activeCore k).E := (Finset.mem_sdiff.mp hlvl.2).1
    have he₀NotSk : e₀ ∉ (C.activeS k).E := (Finset.mem_sdiff.mp hlvl.2).2
    have he₀NotT : e₀ ∉ C.chainTree.E := (Finset.mem_sdiff.mp he₀).2
    have hFundFlow : ∀ i ≤ C.d, ∀ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        walkFlow (C.fundChainCycleAt i e) e₀ =
          if i = k then (if e = e₀ then (1 : ℝ) else 0)
          else if i < k then -walkFlow (C.activeEmb i e) e₀ else 0 := by
      intro i hi e he
      have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
      have hneSp : C.sparsifierCycle i e ≠ [] := by simp [sparsifierCycle]
      have hIter := C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hi he e₀
      have hNonT := C.iterLift_walkFlow_nonTree hH hSub i hi hneSp hClosed e₀ he₀NotT
      have hsp : walkFlow (C.fundChainCycleAt i e) e₀ =
          (if e = e₀ then (1 : ℝ) else 0) - walkFlow (C.activeEmb i e) e₀ := by
        rw [← hIter, hNonT]
        simp [sparsifierCycle, walkFlow_cons, walkFlow_walkRev]
        ring
      rw [hsp]
      rcases lt_trichotomy i k with hlt | rfl | hgt
      · have he₀Gk : e₀ ∈ (C.G k).E := (Finset.mem_sdiff.mp he₀Core).1
        have hi_d : i < C.d := Nat.lt_of_lt_of_le hlt hk_le
        have he₀Si : e₀ ∈ (C.activeS i).E := by
          rw [C.activeS_eq_G_succ hH hi_d]
          exact C.G_E_subset_of_le hH hlt hk_le he₀Gk
        have hne : e ≠ e₀ := fun heq => (Finset.mem_sdiff.mp he).2 (heq ▸ he₀Si)
        simp [hlt, Nat.ne_of_lt hlt, hne]
      · have hnotEmb : e₀ ∉ walkEdges (C.activeEmb k e) := by
          intro hmem
          have hsub : walkEdges (C.activeEmb k e) ⊆ (C.activeS k).E := by
            rw [← walkEdges_walkRev]
            exact C.sparsifierCycle_revEmb_edges_subset hH hk_le (Finset.mem_sdiff.mp he).1
          exact he₀NotSk (hsub hmem)
        simp [walkFlow_eq_zero_of_not_mem hnotEmb]
      · have hgt' : ¬ i = k ∧ ¬ i < k := ⟨by omega, by omega⟩
        have hklt : k < C.d := by omega
        have heGi : e ∈ (C.G i).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
        have heSk : e ∈ (C.activeS k).E := by
          rw [C.activeS_eq_G_succ hH hklt]
          exact C.G_E_subset_of_le hH hgt hi heGi
        have hne : e ≠ e₀ := fun heq => he₀NotSk (heq ▸ heSk)
        have hnotEmb : e₀ ∉ walkEdges (C.activeEmb i e) := by
          intro hmem
          have hsub := C.sparsifierCycle_revEmb_edges_subset hH hi (Finset.mem_sdiff.mp he).1
          rw [walkEdges_walkRev] at hsub
          have hfSi : e₀ ∈ (C.activeS i).E := hsub hmem
          by_cases hi_lt : i < C.d
          · rw [C.activeS_eq_G_succ hH hi_lt] at hfSi
            have hfSk : e₀ ∈ (C.activeS k).E := by
              rw [C.activeS_eq_G_succ hH hklt]
              exact C.G_E_subset_of_le hH (by omega) (by omega) hfSi
            exact he₀NotSk hfSk
          · have hid : i = C.d := by omega
            simp only [hid, activeS, lt_irrefl, ↓reduceIte] at hfSi
            exact Finset.notMem_empty e₀ hfSi
        simp [hgt'.1, hgt'.2, hne, walkFlow_eq_zero_of_not_mem hnotEmb]
    have htele : ∀ i < k,
        C.chainC c (i + 1) e₀ - C.chainC c i e₀ =
          ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, C.chainC c i e * walkFlow (C.activeEmb i e) e₀ := by
      intro i hi_lt
      have hi_d : i < C.d := by omega
      have he₀Gk : e₀ ∈ (C.G k).E := (Finset.mem_sdiff.mp he₀Core).1
      have he₀Gi1 : e₀ ∈ (C.G (i + 1)).E := C.G_E_subset_of_le hH hi_lt hk_le he₀Gk
      change passSparseCoreC (C.activeCore i) (C.activeEmb i) (passCoreC (C.chainC c i)) e₀ -
        C.chainC c i e₀ = _
      unfold passSparseCoreC passCoreC
      have hSsub : (C.activeS i).E ⊆ (C.activeCore i).E := (C.activeS_isSparsified hH hi_d).1.2.1
      rw [← Finset.sum_sdiff hSsub]
      have hSurv : ∑ e ∈ (C.activeS i).E, C.chainC c i e * walkFlow (C.activeEmb i e) e₀ =
          C.chainC c i e₀ := by
        have hEqG : (C.activeS i).E = (C.G (i + 1)).E := by rw [C.activeS_eq_G_succ hH hi_d]
        rw [hEqG, Finset.sum_eq_single e₀]
        · rw [hEmbSurv i hi_d e₀ he₀Gi1]
          simp [walkFlow_cons, walkFlow_nil]
        · intro e heGi1 hne
          rw [hEmbSurv i hi_d e heGi1]
          simp [walkFlow_cons, walkFlow_nil, hne]
        · intro hnot; exact absurd he₀Gi1 hnot
      rw [hSurv]
      ring
    have hsum_range : (∑ i ∈ Finset.range (C.d + 1),
        ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀) =
        ∑ i ∈ Finset.range (k + 1),
          ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀ := by
      have hR : Finset.range (k + 1) ⊆ Finset.range (C.d + 1) := fun x hx =>
        Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hk_le))
      rw [← Finset.sum_subset hR]
      intro i hi hnot
      have hik : k < i := by simp only [Finset.mem_range] at hi hnot; omega
      refine Finset.sum_eq_zero fun e he => ?_
      rw [hFundFlow i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) e he]
      simp [show ¬ i = k by omega, show ¬ i < k by omega]
    have hsplit : ∑ i ∈ Finset.range (k + 1),
        ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀ =
        C.chainC c k e₀ - ∑ i ∈ Finset.range k, (C.chainC c (i + 1) e₀ - C.chainC c i e₀) := by
      rw [Finset.sum_range_succ]
      have hkEq : ∑ e ∈ (C.activeCore k).E \ (C.activeS k).E,
          C.chainC c k e * walkFlow (C.fundChainCycleAt k e) e₀ = C.chainC c k e₀ := by
        rw [Finset.sum_eq_single e₀]
        · rw [hFundFlow k hk_le e₀ hlvl.2]; simp
        · intro e he hne
          rw [hFundFlow k hk_le e he]; simp [hne]
        · intro hnot; exact absurd hlvl.2 hnot
      have hltEq : ∑ i ∈ Finset.range k,
          ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
            C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀ =
          -∑ i ∈ Finset.range k, (C.chainC c (i + 1) e₀ - C.chainC c i e₀) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i < k := Finset.mem_range.mp hi
        rw [htele i hik, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [hFundFlow i (by omega) e he]
        simp only [show i ≠ k by omega, ↓reduceIte, hik]
        ring
      rw [hkEq, hltEq]
      ring
    have hteleSum : ∑ i ∈ Finset.range k, (C.chainC c (i + 1) e₀ - C.chainC c i e₀) =
        C.chainC c k e₀ - C.chainC c 0 e₀ := Finset.sum_range_sub (fun i => C.chainC c i e₀) k
    change c e₀ = _
    dsimp only [y]
    rw [hsum_range, hsplit, hteleSum, chainC]
    ring
  have hyCirc : (C.G 0).IsCirculation y := by
    intro v hv
    have hlin : (C.G 0).demand y v =
        ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
          C.chainC c i e * (C.G 0).demand (walkFlow (C.fundChainCycleAt i e)) v := by
      unfold MGraph.demand
      simp_rw [y, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun e₀ _ => by ring
    rw [hlin]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun e he => ?_
    have hClosed := C.fundChainCycleAt_isClosedWalk hH hSub hSpan
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) he
    rw [isCirculation_walkFlow_of_closed hClosed v hv, mul_zero]
  have hcG0 : (C.G 0).IsCirculation c := hH.1.symm ▸ hCirc
  let d : ℕ → ℝ := fun e₀ => if e₀ ∈ (C.G 0).E then c e₀ - y e₀ else 0
  have hdCircG0 : (C.G 0).IsCirculation d := by
    intro v hv
    have hdem := MGraph.isCirculation_sub hcG0 hyCirc v hv
    unfold MGraph.demand
    rw [← hdem]
    refine Finset.sum_congr rfl fun e₀ he₀ => ?_
    simp [d, he₀]
  have hdCircF : C.chainTree.IsCirculation d :=
    isCirculation_subgraph_of_supp (C.chainTree_isSubgraph hH hSub) hdCircG0
      fun e₀ heNotT => by
        by_cases heG0 : e₀ ∈ (C.G 0).E
        · simp [d, heG0, hNonTree e₀ (Finset.mem_sdiff.mpr ⟨heG0, heNotT⟩)]
        · simp [d, heG0]
  have hdZero := MGraph.isCirculation_eq_zero_of_isForest (C.chainTree_isForest hH hSub) hdCircF
  intro e₀ he₀
  have he₀G0 : e₀ ∈ (C.G 0).E := hH.1.symm ▸ he₀
  by_cases heT : e₀ ∈ C.chainTree.E
  · have hz := hdZero e₀ heT
    simp only [d, he₀G0, ↓reduceIte] at hz
    exact sub_eq_zero.mp hz
  · exact hNonTree e₀ (Finset.mem_sdiff.mpr ⟨he₀G0, heT⟩)

/-- Lemma 7.15 ([chen2022maximum] v2 Lemma 7.15) indexed by off-tree edges `E(G) \ E(T^𝒢)`. -/
theorem lemma_7_15 {G : MGraph} {ℓ c : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) (hEmbSurv : C.EmbedsSurviving)
    (hCirc : G.IsCirculation c) :
    ∀ e₀ ∈ G.E,
      c e₀ = ∑ e ∈ G.E \ C.chainTree.E,
        C.chainC c (C.edgeLevel e) e * walkFlow (C.fundChainCycle e) e₀ := by
  intro e₀ he₀
  rw [C.lemma_7_15_levels hH hSub hSpan hEmbSurv hCirc e₀ he₀, ← hH.1]
  refine (C.sum_offTree_eq_sum_levels hH hSub fun i e =>
    C.chainC c i e * walkFlow (C.fundChainCycleAt i e) e₀).symm

/-- Weight sum bound in the proof of [chen2022maximum] v2 Lemma 7.16 (Appendix A.3 Lemma A.2):
`∑_{e ∈ E(G) \ E(T^𝒢)} |c^{G_{lvl(e)}}_e| * wlen_e ≤ (σ + 1) * ∑_{i=0}^d ‖w^{G_i}‖₁`. -/
lemma lemma_A_2_sum_bound {G : MGraph} {ℓ c w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hvp : IsValidPair G ℓ c w) :
    (∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        |C.chainC c i e| * C.wlenAt ℓ i e) ≤
      (σ + 1) * ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i) := by
  have hVP := C.chain_isValidPair hH hSub hℓ hvp
  have hwNonneg : ∀ i ≤ C.d, ∀ e ∈ (C.G i).E, 0 ≤ C.chainW w i e := by
    intro i hi e he
    exact le_trans (abs_nonneg _) ((hVP i hi).1.2 e he)
  have hLevel : ∀ i ≤ C.d,
      (∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, |C.chainC c i e| * C.wlenAt ℓ i e) ≤
        σ * (C.G i).norm1 (C.chainW w i) +
          if i < C.d then (C.G (i + 1)).norm1 (C.chainW w (i + 1)) else 0 := by
    intro i hi
    have hVPi := (hVP i hi).1
    have hℓi := (hVP i hi).2
    have hLi := C.activeLSF_holds hH hi
    have hSplit : ∀ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        C.wlenAt ℓ i e =
          C.chainLen ℓ (i + 1) e + ((C.activeEmb i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum := by
      intro e _
      unfold wlenAt sparsifierCycle
      simp [walkRev, List.map_reverse, List.map_map, Function.comp_def, List.sum_reverse]
    have hFirstTerm : (∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        |C.chainC c i e| * C.chainLen ℓ (i + 1) e) ≤ σ * (C.G i).norm1 (C.chainW w i) := by
      calc
        ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, |C.chainC c i e| * C.chainLen ℓ (i + 1) e
            ≤ ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, σ * C.chainW w i e := by
          refine Finset.sum_le_sum fun e he => ?_
          have heGi : e ∈ (C.G i).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
          have hwstr_le : (C.activeLSF i).wstr e ≤ σ := (hLi.2.2.2 e heGi).2
          have hwstr_nonneg : 0 ≤ (C.activeLSF i).wstr e :=
            le_trans zero_le_one (le_trans (one_le_stretch (hSub i hi) hℓi heGi)
              (hLi.2.2.2 e heGi).1)
          have hℓi_e : 0 ≤ C.chainLen ℓ i e := hℓi e heGi
          have hProd : C.chainLen ℓ i e * |C.chainC c i e| ≤ C.chainW w i e := by
            rw [← abs_of_nonneg hℓi_e, ← abs_mul]
            exact hVPi.2 e heGi
          calc
            |C.chainC c i e| * ((C.activeLSF i).wstr e * C.chainLen ℓ i e)
                = (C.activeLSF i).wstr e * (C.chainLen ℓ i e * |C.chainC c i e|) := by ring
            _ ≤ (C.activeLSF i).wstr e * C.chainW w i e :=
              mul_le_mul_of_nonneg_left hProd hwstr_nonneg
            _ ≤ σ * C.chainW w i e :=
              mul_le_mul_of_nonneg_right hwstr_le (hwNonneg i hi e heGi)
        _ ≤ ∑ e ∈ (C.G i).E, σ * C.chainW w i e := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset) ?_
          intro e heG _
          have hσ0 : 0 ≤ σ := by
            have := (hLi.2.2.2 e heG).2
            have := le_trans (one_le_stretch (hSub i hi) hℓi heG) (hLi.2.2.2 e heG).1
            linarith
          exact mul_nonneg hσ0 (hwNonneg i hi e heG)
        _ = σ * (C.G i).norm1 (C.chainW w i) := by
          rw [← Finset.mul_sum]
          refine congrArg (σ * ·) (Finset.sum_congr rfl fun e he => ?_)
          exact (abs_of_nonneg (hwNonneg i hi e he)).symm
    have hSecondTerm : (∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        |C.chainC c i e| * ((C.activeEmb i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum) ≤
        if i < C.d then (C.G (i + 1)).norm1 (C.chainW w (i + 1)) else 0 := by
      split_ifs with hi_lt
      · have hSp := C.activeS_isSparsified hH hi_lt
        have hEqG : C.activeS i = C.G (i + 1) := C.activeS_eq_G_succ hH hi_lt
        have hper : ∀ e ∈ (C.activeCore i).E \ (C.activeS i).E,
            |C.chainC c i e| * ((C.activeEmb i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum ≤
              ∑ f ∈ (C.activeS i).E, 2 * passCoreW (C.activeLSF i) (C.chainW w i) e *
                walkCount (C.activeEmb i e) f := by
          intro e he
          have heCore := (Finset.mem_sdiff.mp he).1
          have heGi : e ∈ (C.G i).E := (Finset.mem_sdiff.mp heCore).1
          have hSubEmb : walkEdges (C.activeEmb i e) ⊆ (C.activeS i).E := by
            have := C.sparsifierCycle_revEmb_edges_subset hH hi heCore
            rwa [walkEdges_walkRev] at this
          rw [sum_map_eq_sum_walkCount (C.chainLen ℓ (i + 1)) (C.activeEmb i e) hSubEmb, Finset.mul_sum]
          refine Finset.sum_le_sum fun f _ => ?_
          by_cases hf : f ∈ walkEdges (C.activeEmb i e)
          · have hApp := hSp.2.2.1 e heCore f hf
            have hfLen : C.chainLen ℓ (i + 1) f ≤ 2 * C.chainLen ℓ (i + 1) e := by
              change coreLen (C.activeLSF i) (C.chainLen ℓ i) f ≤
                2 * coreLen (C.activeLSF i) (C.chainLen ℓ i) e
              linarith [hApp.2.2.1]
            have hwstr_nonneg : 0 ≤ (C.activeLSF i).wstr e :=
              le_trans zero_le_one (le_trans (one_le_stretch (hSub i hi) hℓi heGi)
                (hLi.2.2.2 e heGi).1)
            have hProd : C.chainLen ℓ i e * |C.chainC c i e| ≤ C.chainW w i e := by
              rw [← abs_of_nonneg (hℓi e heGi), ← abs_mul]
              exact hVPi.2 e heGi
            have hbound : C.chainLen ℓ (i + 1) f * |C.chainC c i e| ≤
                2 * passCoreW (C.activeLSF i) (C.chainW w i) e := by
              calc
                C.chainLen ℓ (i + 1) f * |C.chainC c i e|
                    ≤ (2 * C.chainLen ℓ (i + 1) e) * |C.chainC c i e| :=
                  mul_le_mul_of_nonneg_right hfLen (abs_nonneg _)
                _ = 2 * ((C.activeLSF i).wstr e * (C.chainLen ℓ i e * |C.chainC c i e|)) := by
                  change 2 * ((C.activeLSF i).wstr e * C.chainLen ℓ i e) * _ = _
                  ring
                _ ≤ 2 * ((C.activeLSF i).wstr e * C.chainW w i e) := by
                  refine mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hProd hwstr_nonneg) (by norm_num)
            calc
              |C.chainC c i e| * (C.chainLen ℓ (i + 1) f * walkCount (C.activeEmb i e) f)
                  = (C.chainLen ℓ (i + 1) f * |C.chainC c i e|) * walkCount (C.activeEmb i e) f := by ring
              _ ≤ 2 * passCoreW (C.activeLSF i) (C.chainW w i) e * walkCount (C.activeEmb i e) f :=
                mul_le_mul_of_nonneg_right hbound (walkCount_nonneg _ _)
          · simp [walkCount_eq_zero_of_not_mem hf]
        calc
          ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
              |C.chainC c i e| * ((C.activeEmb i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum
              ≤ ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, ∑ f ∈ (C.activeS i).E,
                  2 * passCoreW (C.activeLSF i) (C.chainW w i) e * walkCount (C.activeEmb i e) f :=
            Finset.sum_le_sum hper
          _ ≤ ∑ e ∈ (C.activeCore i).E, ∑ f ∈ (C.activeS i).E,
                  2 * passCoreW (C.activeLSF i) (C.chainW w i) e * walkCount (C.activeEmb i e) f := by
            refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun e he _ => ?_
            have heGi : e ∈ (C.G i).E := (Finset.mem_sdiff.mp he).1
            have hwstr_nonneg : 0 ≤ (C.activeLSF i).wstr e :=
              le_trans zero_le_one (le_trans (one_le_stretch (hSub i hi) hℓi heGi)
                (hLi.2.2.2 e heGi).1)
            refine Finset.sum_nonneg fun f _ => mul_nonneg (mul_nonneg (by norm_num)
              (mul_nonneg hwstr_nonneg (hwNonneg i hi e heGi))) (walkCount_nonneg _ _)
          _ = ∑ f ∈ (C.G (i + 1)).E, C.chainW w (i + 1) f := by
            rw [Finset.sum_comm, hEqG]
            refine Finset.sum_congr rfl fun f _ => ?_
            change ∑ e ∈ (C.activeCore i).E, _ =
              passSparseCoreW (C.activeCore i) (C.activeEmb i) (passCoreW (C.activeLSF i) (C.chainW w i)) f
            unfold passSparseCoreW
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => by ring
          _ = (C.G (i + 1)).norm1 (C.chainW w (i + 1)) := by
            unfold MGraph.norm1
            refine Finset.sum_congr rfl fun f hf => ?_
            exact (abs_of_nonneg (hwNonneg (i + 1) hi_lt f hf)).symm
      · have hid : i = C.d := by omega
        subst hid
        simp [activeEmb]
    calc
      ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, |C.chainC c i e| * C.wlenAt ℓ i e
          = (∑ e ∈ (C.activeCore i).E \ (C.activeS i).E, |C.chainC c i e| * C.chainLen ℓ (i + 1) e) +
              ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
                |C.chainC c i e| * ((C.activeEmb i e).map fun x => C.chainLen ℓ (i + 1) x.1).sum := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e he => by rw [hSplit e he, mul_add]
      _ ≤ σ * (C.G i).norm1 (C.chainW w i) +
            if i < C.d then (C.G (i + 1)).norm1 (C.chainW w (i + 1)) else 0 :=
        add_le_add hFirstTerm hSecondTerm
  have hSumLevel := Finset.sum_le_sum fun i hi => hLevel i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hSumLevel
  have hShift : (∑ i ∈ Finset.range (C.d + 1),
      if i < C.d then (C.G (i + 1)).norm1 (C.chainW w (i + 1)) else 0) ≤
      ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i) := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, ↓reduceIte, add_zero]
    have hcongr : (∑ i ∈ Finset.range C.d,
        if i < C.d then (C.G (i + 1)).norm1 (C.chainW w (i + 1)) else 0) =
        ∑ i ∈ Finset.range C.d, (C.G (i + 1)).norm1 (C.chainW w (i + 1)) :=
      Finset.sum_congr rfl fun i hi => by simp only [Finset.mem_range.mp hi, ↓reduceIte]
    rw [hcongr, Finset.sum_range_succ']
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  calc
    ∑ i ∈ Finset.range (C.d + 1), ∑ e ∈ (C.activeCore i).E \ (C.activeS i).E,
        |C.chainC c i e| * C.wlenAt ℓ i e
        ≤ σ * (∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) +
            ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i) := by linarith
    _ = (σ + 1) * ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i) := by ring

/-- Appendix A.3 Lemma A.2 (page 48; [chen2022maximum] v2 Lemma 7.16, paper's "Lemma 7.17"):
when `E(G) \ E(T^𝒢)` is nonempty and `ℓ > 0` on `G`, there exists a fundamental chain cycle
whose ratio against `g` and `ℓ` is at least `(1 / (σ + 1)) * |⟨g, c⟩| / ∑_{i=0}^d ‖w^{G_i}‖₁`. -/
theorem lemma_A_2 {G : MGraph} {ℓ g c w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) (hEmbSurv : C.EmbedsSurviving)
    (hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e)
    (hvp : IsValidPair G ℓ c w)
    (hne : (G.E \ C.chainTree.E).Nonempty) :
    (1 / (σ + 1)) * (|G.inner g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
      (G.E \ C.chainTree.E).sup' hne fun e =>
        |walkInner g (C.fundChainCycle e)| / walkLength ℓ (C.fundChainCycle e) := by
  have hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e := fun e he => le_of_lt (hℓ_pos e he)
  set S := G.E \ C.chainTree.E
  set Wtot := ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)
  set M := S.sup' hne fun e => |walkInner g (C.fundChainCycle e)| / walkLength ℓ (C.fundChainCycle e)
  have hσ_pos : 0 < σ + 1 := by
    obtain ⟨e₀, he₀⟩ := hne
    have he₀G := (Finset.mem_sdiff.mp he₀).1
    have hL0 := C.activeLSF_holds hH (Nat.zero_le C.d)
    have h1 := one_le_stretch (hSub 0 (Nat.zero_le C.d)) (by simpa [hH.1] using hℓ) (hH.1 ▸ he₀G)
    change 1 ≤ (C.activeLSF 0).F.stretch (C.G 0) (C.chainLen ℓ 0) e₀ at h1
    have h2 := (hL0.2.2.2 e₀ (hH.1 ▸ he₀G)).1
    have h3 := (hL0.2.2.2 e₀ (hH.1 ▸ he₀G)).2
    linarith
  have hW_nonneg : 0 ≤ Wtot :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _
  have hLenPos : ∀ e ∈ S, 0 < walkLength ℓ (C.fundChainCycle e) := by
    intro e he
    have he0 : e ∈ (C.G 0).E \ C.chainTree.E := hH.1 ▸ he
    have hlvl := C.mem_activeCore_diff_edgeLevel hH he0
    have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hlvl.1 hlvl.2
    have hIter := C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hlvl.1 hlvl.2
    have hneSp : C.sparsifierCycle (C.edgeLevel e) e ≠ [] := by simp [sparsifierCycle]
    have hNonT := C.iterLift_walkFlow_nonTree hH hSub (C.edgeLevel e) hlvl.1
      hneSp hClosed e (Finset.mem_sdiff.mp he).2
    have hFlowE : walkFlow (C.fundChainCycle e) e = 1 := by
      change walkFlow (C.fundChainCycleAt (C.edgeLevel e) e) e = 1
      rw [← hIter, hNonT]
      have hsub := C.sparsifierCycle_revEmb_edges_subset hH hlvl.1 (Finset.mem_sdiff.mp hlvl.2).1
      have hnot : e ∉ walkEdges (walkRev (C.activeEmb (C.edgeLevel e) e)) := fun hm =>
        (Finset.mem_sdiff.mp hlvl.2).2 (hsub hm)
      simp [sparsifierCycle, walkFlow_cons, walkFlow_eq_zero_of_not_mem hnot]
    have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hlvl.1 hlvl.2
    have hSubG : walkEdges (C.fundChainCycle e) ⊆ G.E :=
      hH.1 ▸ fun f hf => mem_E_of_mem_walkEdges hFundWalk hf
    rw [walkLength_eq_sum_of_subset hSubG]
    have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
    refine Finset.sum_pos' (fun f hf => mul_nonneg (hℓ f hf) (abs_nonneg _)) ?_
    exact ⟨e, heG, by rw [hFlowE, abs_one, mul_one]; exact hℓ_pos e heG⟩
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨e₀, he₀⟩ := hne
    exact le_trans (div_nonneg (abs_nonneg _) (le_of_lt (hLenPos e₀ he₀)))
      (Finset.le_sup' (f := fun e => |walkInner g (C.fundChainCycle e)| / walkLength ℓ (C.fundChainCycle e)) he₀)
  by_cases hW0 : Wtot = 0
  · have hc0 : ∀ e ∈ G.E, c e = 0 := by
      intro e he
      have hw0_sum : (C.G 0).norm1 (C.chainW w 0) = 0 := by
        have hmem : 0 ∈ Finset.range (C.d + 1) := Finset.mem_range.mpr (Nat.succ_pos _)
        have hle := Finset.single_le_sum (f := fun i => (C.G i).norm1 (C.chainW w i))
          (fun i _ => Finset.sum_nonneg fun e _ => abs_nonneg _) hmem
        have hge : 0 ≤ (C.G 0).norm1 (C.chainW w 0) :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      have he0 : e ∈ (C.G 0).E := hH.1.symm ▸ he
      have hwe0 : |C.chainW w 0 e| = 0 := by
        unfold MGraph.norm1 at hw0_sum
        have hle := Finset.single_le_sum (f := fun f => |C.chainW w 0 f|)
          (fun _ _ => abs_nonneg _) he0
        have hge : 0 ≤ |C.chainW w 0 e| := abs_nonneg _
        linarith
      have hw_e : w e = 0 := by simpa [chainW] using hwe0
      have hmul : |ℓ e * c e| = 0 := le_antisymm (hw_e ▸ hvp.2 e he) (abs_nonneg _)
      rcases mul_eq_zero.mp (abs_eq_zero.mp hmul) with hℓ0 | hc_e
      · exact absurd hℓ0 (ne_of_gt (hℓ_pos e he))
      · exact hc_e
    have hInner0 : G.inner g c = 0 :=
      Finset.sum_eq_zero fun e he => by rw [hc0 e he, mul_zero]
    rw [hInner0, abs_zero, zero_div, mul_zero]
    exact hM_nonneg
  · have hW_pos : 0 < Wtot := lt_of_le_of_ne hW_nonneg (Ne.symm hW0)
    have hNum : |G.inner g c| ≤ M * ((σ + 1) * Wtot) := by
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
      calc
        |G.inner g c|
            = |∑ e ∈ S, C.chainC c (C.edgeLevel e) e * walkInner g (C.fundChainCycle e)| :=
          congrArg abs hDecomp
        _ ≤ ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e * walkInner g (C.fundChainCycle e)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * |walkInner g (C.fundChainCycle e)| :=
          Finset.sum_congr rfl fun e _ => abs_mul _ _
        _ ≤ ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * (M * walkLength ℓ (C.fundChainCycle e)) := by
          refine Finset.sum_le_sum fun e he => ?_
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hdiv := Finset.le_sup' (f := fun e => |walkInner g (C.fundChainCycle e)| /
            walkLength ℓ (C.fundChainCycle e)) he
          exact (div_le_iff₀ (hLenPos e he)).mp hdiv
        _ = M * ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * walkLength ℓ (C.fundChainCycle e) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
        _ ≤ M * ∑ e ∈ S, |C.chainC c (C.edgeLevel e) e| * C.wlen ℓ e := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => ?_) hM_nonneg
          exact mul_le_mul_of_nonneg_left (C.lemma_7_13 hH hSub hSpan hℓ_pos he) (abs_nonneg _)
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
    have hStep1 : |G.inner g c| / Wtot ≤ M * (σ + 1) := by
      rw [div_le_iff₀ hW_pos]
      linarith [hNum]
    have hStep2 : (1 / (σ + 1)) * (|G.inner g c| / Wtot) ≤ M := by
      rw [one_div, inv_mul_le_iff₀ hσ_pos]
      linarith [hStep1]
    exact hStep2

end Lemma715AndA2

end TreeChain

end MinCostFlow.Chain
