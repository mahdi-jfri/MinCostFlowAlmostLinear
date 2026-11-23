module

public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Basic.Hidden
public import MinCostFlow.Basic.LSF
public import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Core graphs and sparsified core graphs (Sections 5.3–5.4)

This file formalizes Definitions 5.6, 5.7, 5.12, 5.15 and Lemmas 5.13, 5.16 (pages 18–23),
corresponding to Lemmas 7.4 and 7.7 in [chen2022maximum] (arXiv:2203.00671v2):

* `coreGraph G L` (Definition 5.6): the contracted graph `G / F` on the roots `L.F.R` with edge set
  `G.E \ L.F.F.E`, lengths `coreLen L ℓ e = L.wstr e * ℓ e`, and gradients
  `coreGrad G L g e = g e + φ(head e) - φ(tail e)` where `φ(x) = ⟨g, p(T[x, compRoot T x])⟩`
  (agreeing with the paper's `coreGradPaper G L g e = g e + ⟨g, p(T[head e, tail e])⟩` whenever
  `T` connects `tail e` and `head e`, and repairing [chen2022maximum] v2 Lemma 7.12 when vertex
  splits disconnect `T`).
* `IsSparsifiedCoreGraph` (Definition 5.7): a subgraph `S ⊆ 𝒞(G, F)` with embedding `emb`
  preserving edge lengths up to a factor of `2`, with bounded length, congestion, and sparsity.
* `passCoreC`, `passCoreW` (Definition 5.12) and `lemma_5_13` (Lemma 5.13): passing a valid pair
  `(c, w)` down to `𝒞(G, F)`.
* `passSparseCoreC`, `passSparseCoreW` (Definition 5.15) and `lemma_5_16` (Lemma 5.16): passing a
  valid pair down to `𝒮(G, F)`. Note that the lower bound `‖w^{𝒞}‖₁ ≤ ‖w^{𝒮}‖₁` claimed in
  Lemma 5.16 fails when `𝒞(G, F)` contains self-loops whose path embedding in `𝒮(G, F)` is empty
  (as assumed in Appendix A.3); we prove `lemma_5_16_lower_of_loopless` under a looplessness
  condition and exhibit the counterexample `lemma_5_16_lower_counterexample`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section RootHelpers

lemma root_mem_R {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {v : ℕ} (hv : v ∈ G.V) : RF.root v ∈ RF.R ∧ RF.F.Connected v (RF.root v) := by
  classical
  obtain ⟨r, ⟨hrR, hrConn⟩, _⟩ := hRF.2.2.2.1 v hv
  have hex : ∃ r', r' ∈ RF.R ∧ RF.F.Connected v r' := ⟨r, hrR, hrConn⟩
  simpa [RootedForest.root, hex] using Classical.choose_spec hex

lemma root_eq_of_mem_R {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {r : ℕ} (hr : r ∈ RF.R) : RF.root r = r := by
  have hrV : r ∈ G.V := hRF.2.2.1 hr
  obtain ⟨r₀, _, huniq⟩ := hRF.2.2.2.1 r hrV
  have h1 := root_mem_R hRF hrV
  have h2 : r ∈ RF.R ∧ RF.F.Connected r r := ⟨hr, MGraph.connected_refl RF.F r⟩
  exact (huniq (RF.root r) h1).trans (huniq r h2).symm

lemma root_eq_of_connected {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V) (hconn : RF.F.Connected u v) :
    RF.root u = RF.root v := by
  obtain ⟨r₀, _, huniq⟩ := hRF.2.2.2.1 u hu
  have h1 := root_mem_R hRF hu
  have h2 := root_mem_R hRF hv
  have h2' : RF.root v ∈ RF.R ∧ RF.F.Connected u (RF.root v) :=
    ⟨h2.1, MGraph.connected_trans hconn h2.2⟩
  exact (huniq (RF.root u) h1).trans (huniq (RF.root v) h2').symm

lemma connected_of_root_eq {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V) (heq : RF.root u = RF.root v) :
    RF.F.Connected u v := by
  have h1 := (root_mem_R hRF hu).2
  have h2 := (root_mem_R hRF hv).2
  rw [← heq] at h2
  exact MGraph.connected_trans h1 (MGraph.connected_symm h2)

lemma root_eq_of_edge_mem_F {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    (hSub : G.IsSubgraph RF.F) {e : ℕ} (heF : e ∈ RF.F.E) :
    RF.root (G.tail e) = RF.root (G.head e) := by
  have heV := hRF.1.1 e heF
  have htV : RF.F.tail e ∈ G.V := hRF.2.1 ▸ heV.1
  have hhV : RF.F.head e ∈ G.V := hRF.2.1 ▸ heV.2
  have hEnd := hSub.2.2 e heF
  have hconn : RF.F.Connected (RF.F.tail e) (RF.F.head e) :=
    ⟨[(e, true)], .cons heF rfl (by simp [MGraph.dst]; exact .nil _)⟩
  rw [← hEnd.1, ← hEnd.2]
  exact root_eq_of_connected hRF htV hhV hconn

end RootHelpers

section CoreGraphDefs

/-- The core graph `𝒞(G, F)` (Definition 5.6, page 18): obtained from `G` by contracting each
connected component of `L.F` to its root. Vertex names are the roots `L.F.R` and edge names are
kept from `G.E \ L.F.F.E`. -/
noncomputable def coreGraph (G : MGraph) (L : LSF) : MGraph where
  V := L.F.R
  E := G.E \ L.F.F.E
  tail := fun e => L.F.root (G.tail e)
  head := fun e => L.F.root (G.head e)

/-- The length function `ℓ^{𝒞(G, F)}_ê := wstr_e * ℓ_e` on `𝒞(G, F)` (Definition 5.6, page 18). -/
def coreLen (L : LSF) (ℓ : ℕ → ℝ) : ℕ → ℝ :=
  fun e => L.wstr e * ℓ e

/-- Canonical component root in `T`: the least vertex connected to `v` in `T`. -/
noncomputable def compRoot (T : MGraph) (v : ℕ) : ℕ :=
  open Classical in
  Nat.find (⟨v, ⟨[], MGraph.IsWalk.nil v⟩⟩ : ∃ r, T.Connected v r)

lemma connected_compRoot (T : MGraph) (v : ℕ) : T.Connected v (compRoot T v) := by
  classical
  unfold compRoot
  exact Nat.find_spec (⟨v, ⟨[], MGraph.IsWalk.nil v⟩⟩ : ∃ r, T.Connected v r)

lemma compRoot_eq_of_connected {T : MGraph} {u v : ℕ} (h : T.Connected u v) :
    compRoot T u = compRoot T v := by
  classical
  have hiff : ∀ r, T.Connected u r ↔ T.Connected v r := fun r =>
    ⟨fun hur => MGraph.connected_trans (MGraph.connected_symm h) hur,
     fun hvr => MGraph.connected_trans h hvr⟩
  unfold compRoot
  exact le_antisymm
    (Nat.find_min' _ ((hiff _).mpr (Nat.find_spec ⟨v, MGraph.connected_refl T v⟩)))
    (Nat.find_min' _ ((hiff _).mp (Nat.find_spec ⟨u, MGraph.connected_refl T u⟩)))

/-- Component-root potential `φ(v) = ⟨g, p(T[v, compRoot T v])⟩` in `T`. -/
noncomputable def treeRootPot (T : MGraph) (g : ℕ → ℝ) (v : ℕ) : ℝ :=
  walkInner g (MGraph.forestPath T v (compRoot T v))

/-- The paper's original gradient formula `g^{𝒞(G, F)}_ê := g_e + ⟨g, p(T[v, u])⟩` (Definition 5.6,
page 18), where `e = (u, v)`, defaulting to `g_e` when `u` and `v` are not connected in `L.T`.
This fails [chen2022maximum] v2 Lemma 7.12 once vertex splits introduce isolated vertices in `T`
(`lemma_7_12_counterexample`). -/
noncomputable def coreGradPaper (G : MGraph) (L : LSF) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun e => g e + walkInner g (MGraph.forestPath L.T (G.head e) (G.tail e))

/-- Repaired core-graph gradient `g^{𝒞(G, F)}_ê := g_e + φ(v) - φ(u)` on `𝒞(G, F)` (repairing
Definition 5.6, page 18), where `e = (u, v)` and `φ(x) = ⟨g, p(T[x, compRoot T x])⟩`.
Whenever `L.T` is a forest connecting `u` and `v`, this equals `coreGradPaper G L g e`. -/
noncomputable def coreGrad (G : MGraph) (L : LSF) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun e => g e + treeRootPot L.T g (G.head e) - treeRootPot L.T g (G.tail e)

lemma walkInner_forestPath_eq_sub_treeRootPot {T : MGraph} (hT : T.IsForest)
    {u v : ℕ} (huv : T.Connected u v) (g : ℕ → ℝ) :
    walkInner g (MGraph.forestPath T u v) = treeRootPot T g u - treeRootPot T g v := by
  let r := compRoot T u
  have hr_eq : compRoot T v = r := (compRoot_eq_of_connected huv).symm
  have hur : T.Connected u r := connected_compRoot T u
  have hvr : T.Connected v r := hr_eq ▸ connected_compRoot T v
  have hrv : T.Connected r v := MGraph.connected_symm hvr
  have hflow : ∀ f, walkFlow (MGraph.forestPath T u v) f =
      walkFlow (MGraph.forestPath T u r) f - walkFlow (MGraph.forestPath T v r) f := by
    intro f
    have h1 := walkFlow_forestPath_add hT hur hrv f
    have h2 := walkFlow_forestPath_walkRev hT hvr f
    linarith
  let S : Finset ℕ :=
    walkEdges (MGraph.forestPath T u v) ∪
      (walkEdges (MGraph.forestPath T u r) ∪ walkEdges (MGraph.forestPath T v r))
  rw [walkInner_eq_sum_of_subset Finset.subset_union_left]
  change _ = walkInner g (MGraph.forestPath T u r) - walkInner g (MGraph.forestPath T v (compRoot T v))
  rw [hr_eq]
  rw [walkInner_eq_sum_of_subset (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right),
    walkInner_eq_sum_of_subset (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hflow f, mul_sub]

lemma coreGrad_eq_coreGradPaper_of_connected {G : MGraph} {L : LSF} (hT : L.T.IsForest)
    (g : ℕ → ℝ) {e : ℕ} (hconn : L.T.Connected (G.tail e) (G.head e)) :
    coreGrad G L g e = coreGradPaper G L g e := by
  unfold coreGrad coreGradPaper
  rw [walkInner_forestPath_eq_sub_treeRootPot hT (MGraph.connected_symm hconn) g]
  ring

lemma coreGraph_isValid {G : MGraph} {L : LSF} (hG : G.IsValid)
    (hRF : L.F.IsRootedSpanningForestOf G) : (coreGraph G L).IsValid := by
  intro e he
  have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  have hEnds := hG e heG
  exact ⟨(root_mem_R hRF hEnds.1).1, (root_mem_R hRF hEnds.2).1⟩

/-- `a ≈_2 b` (Section 2, page 5): `0 < a`, `0 < b`, `(1 / 2) * b ≤ a`, and `a ≤ 2 * b`. -/
def approx2 (a b : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ (1 / 2 : ℝ) * b ≤ a ∧ a ≤ 2 * b

/-- Structural clauses (items 1–2 and length/congestion bounds, without edge-count cap) of a
`(γ_ℓ, γ_c)`-sparsified core graph (Definition 5.7, pages 18–19). -/
def IsSparsifiedCoreGraphNoSize (G : MGraph) (L : LSF) (ℓ : ℕ → ℝ) (k γ_ℓ γ_c : ℝ)
    (S : MGraph) (emb : Embedding) : Prop :=
  (coreGraph G L).IsSubgraph S ∧
  emb.IsEmbedding (coreGraph G L) S ∧
  (∀ e ∈ (coreGraph G L).E, ∀ e' ∈ walkEdges (emb e),
    approx2 (coreLen L ℓ e) (coreLen L ℓ e')) ∧
  (emb.length (coreGraph G L) : ℝ) ≤ γ_ℓ ∧
  emb.econg (coreGraph G L) S (fun _ => 1) (fun _ => 1) ≤ k * γ_c

/-- `(γ_ℓ, γ_c)`-sparsified core graph with embedding and edge-count budget `m_cap`
(Definition 5.7 / Lemma 5.17, pages 18–19, 23): a subgraph `S ⊆ 𝒞(G, F)` and an embedding
`emb : 𝒞(G, F) → S` with length-`2` approximation along embedded paths, `length(emb) ≤ γ_ℓ`,
unweighted `econg(emb) ≤ k * γ_c`, and `|E(S)| ≤ m_cap * γ_ℓ / k`.
In Lemma 5.17 (`jtree.tex`, lines 193, 399), `m_cap` is the budget parameter `M` (not the
current edge count `G.m`). -/
def IsSparsifiedCoreGraphAt (G : MGraph) (L : LSF) (ℓ : ℕ → ℝ) (k γ_ℓ γ_c : ℝ)
    (m_cap : ℕ) (S : MGraph) (emb : Embedding) : Prop :=
  (coreGraph G L).IsSubgraph S ∧
  emb.IsEmbedding (coreGraph G L) S ∧
  (∀ e ∈ (coreGraph G L).E, ∀ e' ∈ walkEdges (emb e),
    approx2 (coreLen L ℓ e) (coreLen L ℓ e')) ∧
  (emb.length (coreGraph G L) : ℝ) ≤ γ_ℓ ∧
  emb.econg (coreGraph G L) S (fun _ => 1) (fun _ => 1) ≤ k * γ_c ∧
  (S.E.card : ℝ) ≤ (m_cap : ℝ) * γ_ℓ / k

lemma IsSparsifiedCoreGraphAt.toNoSize {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c : ℝ}
    {m_cap : ℕ} {S : MGraph} {emb : Embedding}
    (h : IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ γ_c m_cap S emb) :
    IsSparsifiedCoreGraphNoSize G L ℓ k γ_ℓ γ_c S emb :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- `(γ_ℓ, γ_c)`-sparsified core graph with embedding at `m_cap = G.m`
(Definition 5.7, pages 18–19): special case `IsSparsifiedCoreGraphAt ... G.m`. -/
abbrev IsSparsifiedCoreGraph (G : MGraph) (L : LSF) (ℓ : ℕ → ℝ) (k γ_ℓ γ_c : ℝ)
    (S : MGraph) (emb : Embedding) : Prop :=
  IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ γ_c G.m S emb

end CoreGraphDefs

section PassCore

/-- Passing circulation `c` from `G` to `𝒞(G, F)` (Definition 5.12, page 22): since edge names
are preserved, `c^{𝒞(G, F)}_ê := c_e`. -/
def passCoreC (c : ℕ → ℝ) : ℕ → ℝ :=
  c

/-- Passing length upper bounds `w` from `G` to `𝒞(G, F)` (Definition 5.12, page 22):
`w^{𝒞(G, F)}_ê := wstr_e * w_e`. -/
def passCoreW (L : LSF) (w : ℕ → ℝ) : ℕ → ℝ :=
  fun e => L.wstr e * w e

/-- Passing a valid pair `(c, w)` from `G` to `𝒞(G, F)` (Definition 5.12, page 22). -/
def passCore (L : LSF) (c w : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (passCoreC c, passCoreW L w)

lemma one_le_stretch {RF : RootedForest} {G : MGraph} {ℓ : ℕ → ℝ}
    (hSub : G.IsSubgraph RF.F)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) {e : ℕ} (he : e ∈ G.E) :
    1 ≤ RF.stretch G ℓ e := by
  classical
  unfold RootedForest.stretch
  have hlen_nonneg : ∀ (u v : ℕ), 0 ≤ walkLength ℓ (MGraph.forestPath RF.F u v) := by
    intro u v
    by_cases hconn : ∃ P, RF.F.IsPath u v P
    · refine walkLength_nonneg fun e' he' => hℓ e' ?_
      rw [walkEdges, List.mem_toFinset, List.mem_map] at he'
      obtain ⟨x, hx, rfl⟩ := he'
      have hW := (MGraph.isPath_forestPath ⟨hconn.choose, hconn.choose_spec.1⟩).1
      exact hSub.2.1 (MGraph.isWalk_edges_mem hW x hx)
    · have hempty : MGraph.forestPath RF.F u v = [] := by
        unfold MGraph.forestPath
        rw [dite_eq_right_iff]
        intro h; exact absurd h hconn
      simp [hempty, walkLength_nil]
  have hℓe : 0 ≤ ℓ e := hℓ e he
  dsimp only
  split_ifs with hroot
  · exact le_add_of_nonneg_right (div_nonneg (hlen_nonneg _ _) hℓe)
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg (hlen_nonneg _ _) (hlen_nonneg _ _)) hℓe)

/-- Lemma 5.13 (page 22; [chen2022maximum, Lemma 7.4]): if `(c, w)` is a valid pair on `G` with
lengths `ℓ`, and `L` satisfies `L.Holds G ℓ σ` with `F ⊆ G` and `ℓ ≥ 0` on `G`, then
`(passCoreC c, passCoreW L w)` is a valid pair on `coreGraph G L` with lengths `coreLen L ℓ`, and
`‖w^{𝒞(G, F)}‖₁ ≤ ∑_{e ∈ E(G)} wstr_e * w_e`. -/
theorem lemma_5_13 {G : MGraph} {L : LSF} {ℓ c w : ℕ → ℝ} {σ : ℝ}
    (hG : G.IsValid) (hL : L.Holds G ℓ σ) (hSub : G.IsSubgraph L.F.F)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hvp : IsValidPair G ℓ c w) :
    IsValidPair (coreGraph G L) (coreLen L ℓ) (passCoreC c) (passCoreW L w) ∧
      (coreGraph G L).norm1 (passCoreW L w) ≤ ∑ e ∈ G.E, L.wstr e * w e := by
  have hRF : L.F.IsRootedSpanningForestOf G := hL.2.1
  have hwstr_nonneg : ∀ e ∈ G.E, 0 ≤ L.wstr e := by
    intro e he
    have h1 := one_le_stretch hSub hℓ he
    have h2 := (hL.2.2.2 e he).1
    linarith
  have hw_nonneg : ∀ e ∈ G.E, 0 ≤ w e := by
    intro e he
    exact le_trans (abs_nonneg _) (hvp.2 e he)
  have hcirc : (coreGraph G L).IsCirculation (passCoreC c) := by
    intro r hr
    unfold MGraph.demand passCoreC
    have hC_E : (coreGraph G L).E = G.E \ L.F.F.E := rfl
    rw [hC_E]
    have hzero_F : ∀ e ∈ G.E, e ∈ L.F.F.E → (coreGraph G L).b e r * c e = 0 := by
      intro e _ heF
      have hroot_eq : L.F.root (G.tail e) = L.F.root (G.head e) :=
        root_eq_of_edge_mem_F hRF hSub heF
      have hb0 : (coreGraph G L).b e r = 0 := MGraph.b_self (coreGraph G L) hroot_eq r
      rw [hb0, zero_mul]
    have hsum_GE :
        ∑ e ∈ G.E \ L.F.F.E, (coreGraph G L).b e r * c e =
          ∑ e ∈ G.E, (coreGraph G L).b e r * c e := by
      have hunion := Finset.sum_union (Finset.disjoint_sdiff_inter G.E L.F.F.E)
        (f := fun e => (coreGraph G L).b e r * c e)
      rw [Finset.sdiff_union_inter] at hunion
      have hinter0 : ∑ e ∈ G.E ∩ L.F.F.E, (coreGraph G L).b e r * c e = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_inter] at he
        exact hzero_F e he.1 he.2
      linarith
    rw [hsum_GE]
    let compR := G.V.filter (fun v => L.F.root v = r)
    have hb_sum : ∀ e ∈ G.E,
        (coreGraph G L).b e r * c e = ∑ v ∈ compR, G.b e v * c e := by
      intro e he
      have hEnds := hG e he
      have htail_eq :
          (if r = L.F.root (G.tail e) then (1 : ℝ) else 0) =
            ∑ v ∈ compR, if v = G.tail e then 1 else 0 := by
        by_cases hrt : L.F.root (G.tail e) = r
        · have hmem : G.tail e ∈ compR := Finset.mem_filter.mpr ⟨hEnds.1, hrt⟩
          rw [ite_eq_left_iff.mpr (fun h => absurd hrt.symm h), Finset.sum_eq_single (G.tail e)]
          · simp
          · intro v _ hne; simp [hne]
          · intro hnot; exact absurd hmem hnot
        · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hrt), Finset.sum_eq_zero]
          intro v hv
          have hvroot : L.F.root v = r := (Finset.mem_filter.mp hv).2
          have hne : v ≠ G.tail e := fun h => hrt (h ▸ hvroot)
          simp [hne]
      have hhead_eq :
          (if r = L.F.root (G.head e) then (1 : ℝ) else 0) =
            ∑ v ∈ compR, if v = G.head e then 1 else 0 := by
        by_cases hrh : L.F.root (G.head e) = r
        · have hmem : G.head e ∈ compR := Finset.mem_filter.mpr ⟨hEnds.2, hrh⟩
          rw [ite_eq_left_iff.mpr (fun h => absurd hrh.symm h), Finset.sum_eq_single (G.head e)]
          · simp
          · intro v _ hne; simp [hne]
          · intro hnot; exact absurd hmem hnot
        · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hrh), Finset.sum_eq_zero]
          intro v hv
          have hvroot : L.F.root v = r := (Finset.mem_filter.mp hv).2
          have hne : v ≠ G.head e := fun h => hrh (h ▸ hvroot)
          simp [hne]
      change ((if r = L.F.root (G.tail e) then (1 : ℝ) else 0) -
          (if r = L.F.root (G.head e) then (1 : ℝ) else 0)) * c e =
        ∑ v ∈ compR, ((if v = G.tail e then 1 else 0) - (if v = G.head e then 1 else 0)) * c e
      rw [htail_eq, hhead_eq, ← Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_congr rfl hb_sum, Finset.sum_comm]
    refine Finset.sum_eq_zero fun v hv => ?_
    exact hvp.1 v (Finset.mem_filter.mp hv).1
  have hvalid : ∀ e ∈ (coreGraph G L).E,
      |coreLen L ℓ e * passCoreC c e| ≤ passCoreW L w e := by
    intro e he
    have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
    have hwstr0 := hwstr_nonneg e heG
    unfold coreLen passCoreC passCoreW
    calc
      |L.wstr e * ℓ e * c e| = |L.wstr e * (ℓ e * c e)| := by ring_nf
      _ = |L.wstr e| * |ℓ e * c e| := abs_mul _ _
      _ = L.wstr e * |ℓ e * c e| := by rw [abs_of_nonneg hwstr0]
      _ ≤ L.wstr e * w e := mul_le_mul_of_nonneg_left (hvp.2 e heG) hwstr0
  refine ⟨⟨hcirc, hvalid⟩, ?_⟩
  unfold MGraph.norm1 passCoreW
  have hC_E : (coreGraph G L).E = G.E \ L.F.F.E := rfl
  rw [hC_E]
  calc
    ∑ e ∈ G.E \ L.F.F.E, |L.wstr e * w e|
        = ∑ e ∈ G.E \ L.F.F.E, L.wstr e * w e := by
          refine Finset.sum_congr rfl fun e he => ?_
          have heG := (Finset.mem_sdiff.mp he).1
          exact abs_of_nonneg (mul_nonneg (hwstr_nonneg e heG) (hw_nonneg e heG))
    _ ≤ ∑ e ∈ G.E, L.wstr e * w e := by
          refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
          intro e he _
          exact mul_nonneg (hwstr_nonneg e he) (hw_nonneg e he)

end PassCore

section PassSparseCore

/-- Passing circulation `c^{𝒞}` from `𝒞(G, F)` to `𝒮(G, F)` along `emb` (Definition 5.15,
pages 22–23): `c^{𝒮} = ∑_{ê ∈ E(𝒞)} c^{𝒞}_{ê} p(Π_{𝒞 → 𝒮}(ê))`. -/
noncomputable def passSparseCoreC (C : MGraph) (emb : Embedding) (cC : ℕ → ℝ) : ℕ → ℝ :=
  fun e' => ∑ e ∈ C.E, cC e * walkFlow (emb e) e'

/-- Passing length upper bounds `w^{𝒞}` from `𝒞(G, F)` to `𝒮(G, F)` along `emb`
(Definition 5.15, pages 22–23; `D40` occurrence-count version aligned with page 24, line 451):
`w^{𝒮} = 2 ∑_{ê ∈ E(𝒞)} w^{𝒞}_{ê} walkCount(Π_{𝒞 → 𝒮}(ê), e')`.
When `emb` maps every edge to a simple (edge-nodup) path, this agrees with the signed-flow
formula `2 ∑_{ê ∈ E(𝒞)} w^{𝒞}_{ê} |p(Π_{𝒞 → 𝒮}(ê))|` (see `passSparseCoreW_eq_walkFlow_of_nodup`). -/
noncomputable def passSparseCoreW (C : MGraph) (emb : Embedding) (wC : ℕ → ℝ) : ℕ → ℝ :=
  fun e' => 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e'

lemma passSparseCoreW_eq_walkFlow_of_nodup {C : MGraph} {emb : Embedding} {wC : ℕ → ℝ}
    (hnd : ∀ e ∈ C.E, ((emb e).map Prod.fst).Nodup) (e' : ℕ) :
    passSparseCoreW C emb wC e' = 2 * ∑ e ∈ C.E, wC e * |walkFlow (emb e) e'| := by
  unfold passSparseCoreW
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun e he => ?_)
  rw [walkCount_eq_abs_walkFlow_of_nodup (hnd e he)]

/-- Passing a valid pair `(c^{𝒞}, w^{𝒞})` from `𝒞(G, F)` to `𝒮(G, F)` along `emb`
(Definition 5.15, pages 22–23). -/
noncomputable def passSparseCore (C : MGraph) (emb : Embedding) (cC wC : ℕ → ℝ) :
    (ℕ → ℝ) × (ℕ → ℝ) :=
  (passSparseCoreC C emb cC, passSparseCoreW C emb wC)

/-- Lemma 5.16 (page 23; [chen2022maximum, Lemma 7.7]): if `(cC, wC)` is a valid pair on
`𝒞(G, F)` with lengths `coreLen L ℓ`, and `(S, emb)` is a `(γ_ℓ, γ_c)`-sparsified core graph,
then `(passSparseCoreC 𝒞 emb cC, passSparseCoreW 𝒞 emb wC)` is a valid pair on `S` with lengths
`coreLen L ℓ`, and `‖w^{𝒮}‖₁ ≤ 2 * γ_ℓ * ‖w^{𝒞}‖₁`.

Note: the printed lower bound `‖w^{𝒞}‖₁ ≤ ‖w^{𝒮}‖₁` fails when `𝒞` has self-loops with empty
embedding in `𝒮` (see `lemma_5_16_lower_of_loopless` and `lemma_5_16_lower_counterexample`). -/
theorem lemma_5_16_noSize {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c : ℝ}
    {S : MGraph} {emb : Embedding} {cC wC : ℕ → ℝ}
    (hS : IsSparsifiedCoreGraphNoSize G L ℓ k γ_ℓ γ_c S emb)
    (hvp : IsValidPair (coreGraph G L) (coreLen L ℓ) cC wC) :
    IsValidPair S (coreLen L ℓ)
        (passSparseCoreC (coreGraph G L) emb cC)
        (passSparseCoreW (coreGraph G L) emb wC) ∧
      S.norm1 (passSparseCoreW (coreGraph G L) emb wC) ≤
        2 * γ_ℓ * (coreGraph G L).norm1 wC := by
  let C := coreGraph G L
  rcases hS with ⟨hSub, hEmb, hApprox, hLen, _⟩
  have hwC_nonneg : ∀ e ∈ C.E, 0 ≤ wC e := fun e he => le_trans (abs_nonneg _) (hvp.2 e he)
  have hcirc : S.IsCirculation (passSparseCoreC C emb cC) := by
    intro v hv
    unfold MGraph.demand passSparseCoreC
    have hmul : ∀ e' ∈ S.E,
        S.b e' v * ∑ e ∈ C.E, cC e * walkFlow (emb e) e' =
          ∑ e ∈ C.E, cC e * (S.b e' v * walkFlow (emb e) e') := by
      intro e' _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [Finset.sum_congr rfl hmul, Finset.sum_comm]
    have hdem : ∀ e ∈ C.E,
        ∑ e' ∈ S.E, cC e * (S.b e' v * walkFlow (emb e) e') = cC e * C.b e v := by
      intro e he
      rw [← Finset.mul_sum]
      congr 1
      have hw := hEmb.2 e he
      change S.demand (walkFlow (emb e)) v = C.b e v
      rw [demand_walkFlow hw v]
      rfl
    rw [Finset.sum_congr rfl hdem]
    have hvC : v ∈ C.V := hSub.1 hv
    have hc := hvp.1 v hvC
    simp only [MGraph.demand] at hc
    calc
      ∑ e ∈ C.E, cC e * C.b e v = ∑ e ∈ C.E, C.b e v * cC e := by
        refine Finset.sum_congr rfl fun e _ => mul_comm _ _
      _ = 0 := hc
  have hvalid : ∀ e' ∈ S.E,
      |coreLen L ℓ e' * passSparseCoreC C emb cC e'| ≤ passSparseCoreW C emb wC e' := by
    intro e' he'
    unfold passSparseCoreC passSparseCoreW
    rw [Finset.mul_sum]
    calc
      |∑ e ∈ C.E, coreLen L ℓ e' * (cC e * walkFlow (emb e) e')|
          ≤ ∑ e ∈ C.E, |coreLen L ℓ e' * (cC e * walkFlow (emb e) e')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ C.E, 2 * wC e * walkCount (emb e) e' := by
          refine Finset.sum_le_sum fun e he => ?_
          by_cases hwf : walkFlow (emb e) e' = 0
          · have h0 : 0 ≤ 2 * wC e * walkCount (emb e) e' :=
              mul_nonneg (mul_nonneg (by norm_num) (hwC_nonneg e he)) (walkCount_nonneg _ _)
            simpa [hwf] using h0
          · have he'mem : e' ∈ walkEdges (emb e) := mem_walkEdges_of_walkFlow_ne_zero hwf
            have hap := hApprox e he e' he'mem
            have hℓ'_pos : 0 < coreLen L ℓ e' := hap.2.1
            have hℓ'_le : coreLen L ℓ e' ≤ 2 * coreLen L ℓ e := by linarith [hap.2.2.1]
            have hℓ_nonneg : 0 ≤ coreLen L ℓ e := hap.1.le
            have hw2 : 0 ≤ 2 * wC e := mul_nonneg (by norm_num) (hwC_nonneg e he)
            calc
              |coreLen L ℓ e' * (cC e * walkFlow (emb e) e')|
                  = coreLen L ℓ e' * |cC e| * |walkFlow (emb e) e'| := by
                    rw [abs_mul, abs_mul, abs_of_pos hℓ'_pos, mul_assoc]
              _ ≤ (2 * coreLen L ℓ e) * |cC e| * |walkFlow (emb e) e'| := by
                    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
                    exact mul_le_mul_of_nonneg_right hℓ'_le (abs_nonneg _)
              _ = 2 * |coreLen L ℓ e * cC e| * |walkFlow (emb e) e'| := by
                    rw [abs_mul, abs_of_nonneg hℓ_nonneg]
                    ring
              _ ≤ 2 * wC e * |walkFlow (emb e) e'| := by
                    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
                    exact mul_le_mul_of_nonneg_left (hvp.2 e he) (by norm_num)
              _ ≤ 2 * wC e * walkCount (emb e) e' :=
                    mul_le_mul_of_nonneg_left (abs_walkFlow_le_walkCount (emb e) e') hw2
      _ = 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
  refine ⟨⟨hcirc, hvalid⟩, ?_⟩
  unfold MGraph.norm1 passSparseCoreW
  have hnonneg_S : ∀ e' ∈ S.E, 0 ≤ 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := by
    intro e' _
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (hwC_nonneg e he) (walkCount_nonneg _ _)
  calc
    ∑ e' ∈ S.E, |(2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e')|
        = ∑ e' ∈ S.E, 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := by
          refine Finset.sum_congr rfl fun e' he' => abs_of_nonneg (hnonneg_S e' he')
    _ = 2 * ∑ e ∈ C.E, wC e * ∑ e' ∈ S.E, walkCount (emb e) e' := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
    _ ≤ 2 * ∑ e ∈ C.E, wC e * γ_ℓ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum fun e he => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hwC_nonneg e he)
          have h1 : ∑ e' ∈ S.E, walkCount (emb e) e' ≤ ((emb e).length : ℝ) :=
            sum_walkCount_le_length S.E (emb e)
          have h2 : (emb e).length ≤ emb.length C :=
            Finset.le_sup (f := fun e => (emb e).length) he
          have h3 : ((emb e).length : ℝ) ≤ γ_ℓ := le_trans (by exact_mod_cast h2) hLen
          exact le_trans h1 h3
    _ = 2 * γ_ℓ * ∑ e ∈ C.E, |wC e| := by
          rw [← Finset.sum_mul]
          have habs : ∑ e ∈ C.E, wC e = ∑ e ∈ C.E, |wC e| := by
            refine Finset.sum_congr rfl fun e he => (abs_of_nonneg (hwC_nonneg e he)).symm
          rw [habs]
          ring

/-- Lemma 5.16 (page 23) for `IsSparsifiedCoreGraphAt` (including `IsSparsifiedCoreGraph`). -/
theorem lemma_5_16 {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c : ℝ} {m_cap : ℕ}
    {S : MGraph} {emb : Embedding} {cC wC : ℕ → ℝ}
    (hS : IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ γ_c m_cap S emb)
    (hvp : IsValidPair (coreGraph G L) (coreLen L ℓ) cC wC) :
    IsValidPair S (coreLen L ℓ)
        (passSparseCoreC (coreGraph G L) emb cC)
        (passSparseCoreW (coreGraph G L) emb wC) ∧
      S.norm1 (passSparseCoreW (coreGraph G L) emb wC) ≤
        2 * γ_ℓ * (coreGraph G L).norm1 wC :=
  lemma_5_16_noSize hS.toNoSize hvp

/-- Conditional lower bound in Lemma 5.16 (page 23): when `𝒞(G, F)` has no self-loops (every
edge has distinct endpoints), `‖w^{𝒞}‖₁ ≤ ‖w^{𝒮}‖₁` holds (in fact `2 * ‖w^{𝒞}‖₁ ≤ ‖w^{𝒮}‖₁`). -/
theorem lemma_5_16_lower_of_loopless_noSize {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c : ℝ}
    {S : MGraph} {emb : Embedding} {cC wC : ℕ → ℝ}
    (hS : IsSparsifiedCoreGraphNoSize G L ℓ k γ_ℓ γ_c S emb)
    (hvp : IsValidPair (coreGraph G L) (coreLen L ℓ) cC wC)
    (hnoLoop : ∀ e ∈ (coreGraph G L).E, (coreGraph G L).tail e ≠ (coreGraph G L).head e) :
    (coreGraph G L).norm1 wC ≤ S.norm1 (passSparseCoreW (coreGraph G L) emb wC) := by
  let C := coreGraph G L
  rcases hS with ⟨_, hEmb, _, _, _⟩
  have hwC_nonneg : ∀ e ∈ C.E, 0 ≤ wC e := fun e he => le_trans (abs_nonneg _) (hvp.2 e he)
  have hge1 : ∀ e ∈ C.E, 1 ≤ ∑ e' ∈ S.E, |walkFlow (emb e) e'| := by
    intro e he
    have hdem := demand_walkFlow (hEmb.2 e he) (C.tail e)
    have hne := hnoLoop e he
    simp only [C, hne, ↓reduceIte, sub_zero] at hdem
    have h1 : (1 : ℝ) = |S.demand (walkFlow (emb e)) (C.tail e)| := by rw [hdem]; norm_num
    rw [h1]
    unfold MGraph.demand
    calc
      |∑ e' ∈ S.E, S.b e' (C.tail e) * walkFlow (emb e) e'|
          ≤ ∑ e' ∈ S.E, |S.b e' (C.tail e) * walkFlow (emb e) e'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e' ∈ S.E, |walkFlow (emb e) e'| := by
          refine Finset.sum_le_sum fun e' _ => ?_
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (S.abs_b_le_one e' (C.tail e))
  have hge1_cnt : ∀ e ∈ C.E, 1 ≤ ∑ e' ∈ S.E, walkCount (emb e) e' := fun e he =>
    le_trans (hge1 e he) (Finset.sum_le_sum fun e' _ => abs_walkFlow_le_walkCount (emb e) e')
  have hnonneg_S : ∀ e' ∈ S.E, 0 ≤ 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := by
    intro e' _
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (hwC_nonneg e he) (walkCount_nonneg _ _)
  unfold MGraph.norm1 passSparseCoreW
  calc
    ∑ e ∈ C.E, |wC e| = ∑ e ∈ C.E, wC e :=
      Finset.sum_congr rfl fun e he => abs_of_nonneg (hwC_nonneg e he)
    _ ≤ 2 * ∑ e ∈ C.E, wC e := by
        have hs : 0 ≤ ∑ e ∈ C.E, wC e := Finset.sum_nonneg fun e he => hwC_nonneg e he
        linarith
    _ ≤ 2 * ∑ e ∈ C.E, wC e * ∑ e' ∈ S.E, walkCount (emb e) e' := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum fun e he => ?_
        exact le_mul_of_one_le_right (hwC_nonneg e he) (hge1_cnt e he)
    _ = ∑ e' ∈ S.E, 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := by
        rw [Finset.mul_sum]
        have hinner : ∀ e ∈ C.E,
            2 * (wC e * ∑ e' ∈ S.E, walkCount (emb e) e') =
              ∑ e' ∈ S.E, 2 * (wC e * walkCount (emb e) e') := by
          intro e _
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ e' ∈ S.E, |(2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e')| := by
        refine Finset.sum_congr rfl fun e' he' => (abs_of_nonneg (hnonneg_S e' he')).symm

/-- Conditional lower bound in Lemma 5.16 (page 23) for `IsSparsifiedCoreGraphAt` (including
`IsSparsifiedCoreGraph`). -/
theorem lemma_5_16_lower_of_loopless {G : MGraph} {L : LSF} {ℓ : ℕ → ℝ} {k γ_ℓ γ_c : ℝ}
    {m_cap : ℕ} {S : MGraph} {emb : Embedding} {cC wC : ℕ → ℝ}
    (hS : IsSparsifiedCoreGraphAt G L ℓ k γ_ℓ γ_c m_cap S emb)
    (hvp : IsValidPair (coreGraph G L) (coreLen L ℓ) cC wC)
    (hnoLoop : ∀ e ∈ (coreGraph G L).E, (coreGraph G L).tail e ≠ (coreGraph G L).head e) :
    (coreGraph G L).norm1 wC ≤ S.norm1 (passSparseCoreW (coreGraph G L) emb wC) :=
  lemma_5_16_lower_of_loopless_noSize hS.toNoSize hvp hnoLoop

/-- Counterexample showing that the lower bound `‖w^{𝒞(G, F)}‖₁ ≤ ‖w^{𝒮(G, F)}‖₁` of Lemma 5.16
(page 23; [chen2022maximum, Lemma 7.7]) fails even when `G` is loopless, whenever `𝒞(G, F)` has a
self-loop with empty path embedding in `𝒮(G, F)` (as assumed in Appendix A.3). -/
theorem lemma_5_16_lower_counterexample :
    ∃ (G : MGraph) (L : LSF) (ℓ cC wC : ℕ → ℝ) (S : MGraph) (emb : Embedding),
      G.IsValid ∧ (∀ e ∈ G.E, G.tail e ≠ G.head e) ∧ L.Holds G ℓ 2 ∧ G.IsSubgraph L.F.F ∧
      IsSparsifiedCoreGraph G L ℓ 1 1 1 S emb ∧
      IsValidPair (coreGraph G L) (coreLen L ℓ) cC wC ∧
      S.norm1 (passSparseCoreW (coreGraph G L) emb wC) < (coreGraph G L).norm1 wC := by
  let G : MGraph := ⟨{0, 1}, {0, 1}, fun _ => 0, fun _ => 1⟩
  let T : MGraph := ⟨{0, 1}, {0}, fun _ => 0, fun _ => 1⟩
  let RF : RootedForest := ⟨T, {0}⟩
  let L : LSF := ⟨T, RF, fun _ => 2⟩
  let ℓ : ℕ → ℝ := fun _ => 1
  let cC : ℕ → ℝ := fun _ => 1
  let wC : ℕ → ℝ := fun _ => 2
  let C := coreGraph G L
  let S : MGraph := ⟨{0}, ∅, C.tail, C.head⟩
  let emb : Embedding := fun _ => []
  have hG : G.IsValid := by
    intro e he
    simp only [G, Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with rfl | rfl <;> simp
  have hloopless : ∀ e ∈ G.E, G.tail e ≠ G.head e := by
    intro e _; simp [G]
  have hT_forest : T.IsForest := by
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [T, Finset.mem_singleton] at he
      subst he; simp [T]
    · intro P hP
      rcases hP with ⟨hPne, hPnd, u, hu⟩
      cases hPeq : P with
      | nil => exact hPne hPeq
      | cons x xs =>
        rw [hPeq] at hu hPnd
        cases hu with
        | cons he hx hrest =>
          have hxe : x.1 = 0 := by simpa [T] using he
          cases xs with
          | nil =>
            have hdst : T.dst x = u := by cases hrest; rfl
            rw [← hx] at hdst
            cases hx2 : x.2 <;> simp [T, MGraph.src, MGraph.dst, hx2] at hdst
          | cons y ys =>
            have hye : y.1 = 0 := by
              have hmem := MGraph.isWalk_edges_mem hrest y (by simp)
              simpa [T] using hmem
            simp [hxe, hye] at hPnd
  have hSub : G.IsSubgraph L.F.F := by
    refine ⟨by simp [L, RF, T, G], by simp [L, RF, T, G], ?_⟩
    intro e he
    simp [L, RF, T, G]
  have hRF : RF.IsRootedSpanningForestOf G := by
    refine ⟨hT_forest, rfl, by simp [RF, G], ?_, hSub⟩
    intro v hv
    refine ⟨0, ⟨by simp [RF], ?_⟩, ?_⟩
    · simp only [G, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact MGraph.connected_refl T 0
      · exact ⟨[(0, false)], .cons (by simp [RF, T]) (by simp [RF, T, MGraph.src])
          (by simp [RF, T, MGraph.dst]; exact .nil 0)⟩
    · rintro r ⟨hr, _⟩
      simpa [RF] using hr
  have hr0 : RF.root 0 = 0 := root_eq_of_mem_R hRF (by simp [RF])
  have hr1 : RF.root 1 = 0 := by
    have h1V : (1 : ℕ) ∈ G.V := by simp [G]
    exact (root_mem_R hRF h1V).1 |> fun h => by simpa [RF] using h
  have hL : L.Holds G ℓ 2 := by
    refine ⟨hT_forest, hRF, ⟨by simp [L, RF], by simp [L, RF], fun e _ => ⟨rfl, rfl⟩⟩, ?_⟩
    intro e _
    refine ⟨?_, by simp [L]⟩
    unfold RootedForest.stretch
    have htail : G.tail e = 0 := rfl
    have hhead : G.head e = 1 := rfl
    change (if RF.root (G.tail e) = RF.root (G.head e) then
        1 + walkLength ℓ (T.forestPath (G.tail e) (G.head e)) / ℓ e
      else 1 + (walkLength ℓ (T.forestPath (G.tail e) (RF.root (G.tail e))) +
        walkLength ℓ (T.forestPath (G.head e) (RF.root (G.head e)))) / ℓ e) ≤ L.wstr e
    simp only [htail, hhead, hr0, hr1, ↓reduceIte]
    have hconn01 : T.Connected 0 1 :=
      ⟨[(0, true)], .cons (by simp [T]) (by simp [T, MGraph.src])
        (by simp [T, MGraph.dst]; exact .nil 1)⟩
    have hpath := MGraph.isPath_forestPath hconn01
    have hlen_le : (MGraph.forestPath T 0 1).length ≤ 1 := by
      have hnd := MGraph.isPath_edges_nodup hpath
      have hsub : ((MGraph.forestPath T 0 1).map Prod.fst).toFinset ⊆ {0} := by
        intro a ha
        rw [List.mem_toFinset, List.mem_map] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        have hxE := MGraph.isWalk_edges_mem hpath.1 x hx
        simpa [T] using hxE
      have hc := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hnd, List.length_map] at hc
      simpa using hc
    have hwl_le : walkLength ℓ (MGraph.forestPath T 0 1) ≤ 1 := by
      have h1 : walkLength ℓ (MGraph.forestPath T 0 1) =
          ∑ e' ∈ walkEdges (MGraph.forestPath T 0 1), |walkFlow (MGraph.forestPath T 0 1) e'| := by
        unfold walkLength
        refine Finset.sum_congr rfl fun e' _ => by simp [ℓ]
      rw [h1]
      have h2 := sum_abs_walkFlow_le_length (walkEdges (MGraph.forestPath T 0 1)) (MGraph.forestPath T 0 1)
      exact le_trans h2 (by exact_mod_cast hlen_le)
    have hℓe : ℓ e = 1 := rfl
    rw [hℓe, div_one]
    have hwstr2 : L.wstr e = 2 := rfl
    rw [hwstr2]
    linarith
  have hC_E : C.E = {1} := by
    ext e
    simp only [C, coreGraph, L, RF, T, G, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hS : IsSparsifiedCoreGraph G L ℓ 1 1 1 S emb := by
    refine ⟨⟨by simp [S, coreGraph, L, RF], by simp [S], fun e he => by simp [S] at he⟩,
      ⟨by simp [S, coreGraph, L, RF], ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro e he
      have hce : C.tail e = 0 ∧ C.head e = 0 := by
        simp [C, coreGraph, G, L, hr0, hr1]
      rw [hce.1, hce.2]
      exact .nil 0
    · intro e _ e' he'
      simp [emb, walkEdges] at he'
    · simp [Embedding.length, emb]
    · simp [Embedding.econg, S]
    · simp [S]
  have hvp : IsValidPair C (coreLen L ℓ) cC wC := by
    refine ⟨?_, ?_⟩
    · intro v _
      unfold MGraph.demand
      rw [hC_E, Finset.sum_singleton]
      have hself : C.tail 1 = C.head 1 := by simp [C, coreGraph, G, L, hr0, hr1]
      rw [MGraph.b_self C hself v, zero_mul]
    · intro e _
      norm_num [coreLen, L, ℓ, cC, wC]
  refine ⟨G, L, ℓ, cC, wC, S, emb, hG, hloopless, hL, hSub, hS, hvp, ?_⟩
  have hSnorm : S.norm1 (passSparseCoreW C emb wC) = 0 := by simp [MGraph.norm1, S]
  have hCnorm : C.norm1 wC = 2 := by
    unfold MGraph.norm1
    rw [hC_E, Finset.sum_singleton]
    norm_num [wC]
  rw [hSnorm, hCnorm]
  norm_num

end PassSparseCore

end MinCostFlow.Chain
