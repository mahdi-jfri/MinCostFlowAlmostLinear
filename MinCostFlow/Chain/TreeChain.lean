module

public import MinCostFlow.Chain.CoreGraph
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shifted tree chains and induced spanning trees (Section 5.4)

This file formalizes Definition 5.8 (pages 19–20):

* `TreeChain`: a static `d`-level shifted tree chain `{G_0, …, G_d}` with `k` LSFs, shift index
  `bran_i < k`, and `(γ_ℓ, γ_c)`-sparsified core graphs and embeddings at each level `i < d`, and
  `lastK` LSFs at the final level `d`.
* `TreeChain.Holds`: the conditions of Definition 5.8 (including the MWU average-stretch bound from
  Lemma 5.5).
* `TreeChain.ForestsAreSubgraphs`, `TreeChain.LastLevelSpans`, `TreeChain.EmbedsSurviving`: the
  additional structural conditions (`F_i ⊆ G_i`, `F_d` spanning each component of `G_d`, and
  `Π_i(e) = [(e, true)]` for `e ∈ E(G_{i+1})`) needed for `T^𝒢` to be a spanning tree of `G` and
  for cycle lifting/decomposition in Appendix A.3.
* `TreeChain.chainTree`: the tree `T^𝒢 = ⋃_{i=0}^d F^{G_i}_{bran_i}`, proved to be a subgraph and
  a forest (`chainTree_isForest`) whenever `ForestsAreSubgraphs` holds, and a spanning tree of `G`
  (`chainTree_isSpanningTreeOn`) when `LastLevelSpans` and connectivity of `G` also hold.
-/

@[expose] public section

namespace MinCostFlow.Chain

/-- A static `d`-level shifted tree chain (Definition 5.8, pages 19–20). -/
structure TreeChain where
  /-- Number of recursion levels `d`. -/
  d : ℕ
  /-- Reduction factor `k` at levels `0 ≤ i < d`. -/
  k : ℕ
  /-- Graphs `G_0, …, G_d` in the chain. -/
  G : ℕ → MGraph
  /-- At each level `i < d`, the collection of `k` LSFs `{lsfs i j}_{j=0}^{k-1}`. -/
  lsfs : ℕ → ℕ → LSF
  /-- Shift index `bran i < k` at each level `i < d`. -/
  bran : ℕ → ℕ
  /-- Sparsified core graphs `𝒮(G_i, F_j)` for `i < d`, `j < k`. -/
  S : ℕ → ℕ → MGraph
  /-- Sparsified core graph embeddings `Π_{𝒞(G_i, F_j) → 𝒮(G_i, F_j)}` for `i < d`, `j < k`. -/
  emb : ℕ → ℕ → Embedding
  /-- Number of LSFs at the final level `d`. -/
  lastK : ℕ
  /-- LSFs at the final level `d`. -/
  lastLSFs : ℕ → LSF
  /-- Active index at the final level `d`. -/
  lastBran : ℕ

namespace TreeChain

/-- The active LSF `F^{G_i}_{bran_i}` at level `i ≤ d`. -/
def activeLSF (C : TreeChain) (i : ℕ) : LSF :=
  if i < C.d then C.lsfs i (C.bran i) else C.lastLSFs C.lastBran

/-- The active core graph `𝒞(G_i, F^{G_i}_{bran_i})` at level `i ≤ d`. -/
noncomputable def activeCore (C : TreeChain) (i : ℕ) : MGraph :=
  coreGraph (C.G i) (C.activeLSF i)

/-- The active sparsified core graph at level `i ≤ d`. For `i < d` this is `S i (bran i)`;
for `i = d` this is the edgeless subgraph of `activeCore d` (Definition A.1). -/
noncomputable def activeS (C : TreeChain) (i : ℕ) : MGraph :=
  if i < C.d then C.S i (C.bran i)
  else
    { V := (C.activeCore C.d).V
      E := ∅
      tail := (C.activeCore C.d).tail
      head := (C.activeCore C.d).head }

/-- The active spanner embedding at level `i ≤ d`. For `i < d` this is `emb i (bran i)`;
for `i = d` every edge maps to `[]` (Definition A.1). -/
def activeEmb (C : TreeChain) (i : ℕ) : Embedding :=
  if i < C.d then C.emb i (C.bran i) else fun _ => []

/-- Recursive edge lengths `ℓ^{G_i}` along the chain (Definition 5.6 / 5.7). -/
def chainLen (C : TreeChain) (ℓ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => ℓ
  | i + 1 => coreLen (C.activeLSF i) (C.chainLen ℓ i)

/-- Recursive edge gradients `g^{G_i}` along the chain (repaired Definition 5.6 / 5.7). -/
noncomputable def chainGrad (C : TreeChain) (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => g
  | i + 1 => coreGrad (C.G i) (C.activeLSF i) (C.chainGrad g i)

/-- The paper's original recursive edge gradients `g^{G_i}` along the chain using
`coreGradPaper`, which fails Lemma 7.12 after vertex splits (`lemma_7_12_counterexample`). -/
noncomputable def chainGradPaper (C : TreeChain) (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => g
  | i + 1 => coreGradPaper (C.G i) (C.activeLSF i) (C.chainGradPaper g i)

/-- Recursive circulations `c^{G_i}` passed down the chain (Definitions 5.12, 5.15). -/
noncomputable def chainC (C : TreeChain) (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => c
  | i + 1 => passSparseCoreC (C.activeCore i) (C.activeEmb i) (passCoreC (C.chainC c i))

/-- Recursive upper bounds `w^{G_i}` passed down the chain (Definitions 5.12, 5.15). -/
noncomputable def chainW (C : TreeChain) (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => w
  | i + 1 =>
    passSparseCoreW (C.activeCore i) (C.activeEmb i)
      (passCoreW (C.activeLSF i) (C.chainW w i))

/-- Iterated root projection from `V(G_0)` to `V(G_i)`. -/
noncomputable def proj (C : TreeChain) : ℕ → ℕ → ℕ
  | 0, v => v
  | i + 1, v => (C.activeLSF i).F.root (C.proj i v)

variable (C : TreeChain)

/-- The static conditions of Definition 5.8 (pages 19–20):
* `G_0 = G` is valid, `k > 0`, `lastK > 0`, and `bran_i < k`, `lastBran < lastK`;
* at each level `i < d`, the `k` triples satisfy `LSF.Holds` (with parameter `σ`), the uniform MWU
  average-stretch bound `σ_mwu` (Lemma 5.5), and have `(γ_ℓ, γ_c)`-sparsified core graphs
  `S i j` with embeddings `emb i j`, with `G_{i+1} = S i (bran i)`;
* at level `d`, the `lastK` triples satisfy `LSF.Holds` (with parameter `σ`) and the MWU bound. -/
def Holds (G : MGraph) (ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ) : Prop :=
  C.G 0 = G ∧
  G.IsValid ∧
  0 < C.k ∧
  0 < C.lastK ∧
  (∀ i < C.d,
    C.bran i < C.k ∧
    (∀ j < C.k,
      (C.lsfs i j).Holds (C.G i) (C.chainLen ℓ i) σ ∧
      IsSparsifiedCoreGraphNoSize (C.G i) (C.lsfs i j) (C.chainLen ℓ i) (C.k : ℝ) γ_ℓ γ_c
        (C.S i j) (C.emb i j)) ∧
    (∀ e ∈ (C.G i).E,
      (∑ j ∈ Finset.range C.k, (C.lsfs i j).wstr e) / (C.k : ℝ) ≤ σ_mwu) ∧
    C.G (i + 1) = C.S i (C.bran i)) ∧
  C.lastBran < C.lastK ∧
  (∀ j < C.lastK, (C.lastLSFs j).Holds (C.G C.d) (C.chainLen ℓ C.d) σ) ∧
  (∀ e ∈ (C.G C.d).E,
    (∑ j ∈ Finset.range C.lastK, (C.lastLSFs j).wstr e) / (C.lastK : ℝ) ≤ σ_mwu)

/-- Each active rooted forest `F^{G_i}_{bran_i}` is a subgraph of `G_i`. (This is not implied by
`LSF.Holds`, which only requires `F_i ⊆ T_i`, so we state it explicitly.) -/
def ForestsAreSubgraphs : Prop :=
  ∀ i ≤ C.d, (C.G i).IsSubgraph (C.activeLSF i).F.F

/-- At the final level `d`, the active forest `F_d` spans each connected component of `G_d`
(for example when `F_d` is a single spanning tree of a connected `G_d`). -/
def LastLevelSpans : Prop :=
  ∀ u ∈ (C.G C.d).V, ∀ v ∈ (C.G C.d).V,
    (C.G C.d).Connected u v → (C.activeLSF C.d).F.F.Connected u v

/-- Each spanner embedding `Π_i` (`i < d`) maps surviving edges `e ∈ E(G_{i+1})` to the
single-edge walk `[(e, true)]` (used in [chen2022maximum, Lemma 7.15]). -/
def EmbedsSurviving : Prop :=
  ∀ i < C.d, ∀ e ∈ (C.G (i + 1)).E, C.activeEmb i e = [(e, true)]

/-- The edges of the tree `T^𝒢`: the union of edges of `F^{G_0}_{bran_0}, …, F^{G_d}_{bran_d}`. -/
def chainTreeEdges : Finset ℕ :=
  (Finset.range (C.d + 1)).biUnion fun i => (C.activeLSF i).F.F.E

/-- The spanning tree `T^𝒢` corresponding to the tree chain `𝒢` (Definition 5.8, page 20):
its vertex set is `V(G_0)`, its edge set is `⋃_{i=0}^d E(F^{G_i}_{bran_i})`, and its edge
endpoints are those in `G_0`. -/
def chainTree : MGraph where
  V := (C.G 0).V
  E := C.chainTreeEdges
  tail := (C.G 0).tail
  head := (C.G 0).head

section BasicChainLemmas

lemma activeLSF_holds {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i ≤ C.d) :
    (C.activeLSF i).Holds (C.G i) (C.chainLen ℓ i) σ := by
  unfold activeLSF
  split_ifs with hlt
  · have h := hH.2.2.2.2.1 i hlt
    exact (h.2.1 (C.bran i) h.1).1
  · have hieq : i = C.d := by omega
    subst hieq
    have hlast := hH.2.2.2.2.2
    exact hlast.2.1 C.lastBran hlast.1

/-- `ForestsAreSubgraphs` follows from `TreeChain.Holds`, because `IsRootedSpanningForestOf G`
includes `G.IsSubgraph F`. -/
lemma forestsAreSubgraphs_of_holds {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) : C.ForestsAreSubgraphs :=
  fun _ hi => (C.activeLSF_holds hH hi).2.1.2.2.2.2

lemma activeS_eq_G_succ {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    C.activeS i = C.G (i + 1) := by
  simp only [activeS, hi, ↓reduceIte]
  exact (hH.2.2.2.2.1 i hi).2.2.2.symm

lemma activeS_isSparsified {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    IsSparsifiedCoreGraphNoSize (C.G i) (C.activeLSF i) (C.chainLen ℓ i) (C.k : ℝ) γ_ℓ γ_c
      (C.activeS i) (C.activeEmb i) := by
  have h := hH.2.2.2.2.1 i hi
  simpa only [activeLSF, activeS, activeEmb, hi, ↓reduceIte] using (h.2.1 (C.bran i) h.1).2

lemma G_isValid {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) : ∀ i ≤ C.d, (C.G i).IsValid := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hH.1]
    exact hH.2.1
  | succ j ih =>
    intro hj
    have hjlt : j < C.d := hj
    have hjvalid := ih (Nat.le_of_lt hjlt)
    have hcore := coreGraph_isValid hjvalid (C.activeLSF_holds hH (Nat.le_of_lt hjlt)).2.1
    have hSp := C.activeS_isSparsified hH hjlt
    have hSub : (C.activeCore j).IsSubgraph (C.G (j + 1)) := by
      rw [← C.activeS_eq_G_succ hH hjlt]
      exact hSp.1
    intro e he
    have hEnds := hSub.2.2 e he
    have hcEnds := hcore e (hSub.2.1 he)
    rw [hEnds.1, hEnds.2]
    -- `hcore` shows ends lie in `(C.activeCore j).V`, and `activeS.V = (activeCore j).V`
    have hV : (C.activeCore j).V ⊆ (C.G (j + 1)).V := by
      rw [← C.activeS_eq_G_succ hH hjlt]
      exact hSp.2.1.1
    exact ⟨hV hcEnds.1, hV hcEnds.2⟩

lemma G_succ_V_eq {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    (C.G (i + 1)).V = (C.activeLSF i).F.R := by
  have hSp := C.activeS_isSparsified hH hi
  rw [← C.activeS_eq_G_succ hH hi]
  exact Finset.Subset.antisymm hSp.1.1 hSp.2.1.1

lemma G_succ_V_subset {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    (C.G (i + 1)).V ⊆ (C.G i).V := by
  rw [C.G_succ_V_eq hH hi]
  exact (C.activeLSF_holds hH (Nat.le_of_lt hi)).2.1.2.2.1

lemma G_V_subset_of_le {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.d) :
    (C.G j).V ⊆ (C.G i).V := by
  induction j with
  | zero =>
    have h0 : i = 0 := by omega
    subst h0; exact Finset.Subset.refl _
  | succ k ih =>
    by_cases hle : i ≤ k
    · exact Finset.Subset.trans (C.G_succ_V_subset hH hj) (ih hle (Nat.le_of_lt hj))
    · have heq : i = k + 1 := by omega
      subst heq; exact Finset.Subset.refl _

lemma G_succ_isSubgraph_core {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    (C.activeCore i).IsSubgraph (C.G (i + 1)) := by
  rw [← C.activeS_eq_G_succ hH hi]
  exact (C.activeS_isSparsified hH hi).1

lemma G_succ_E_subset {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i < C.d) :
    (C.G (i + 1)).E ⊆ (C.G i).E \ (C.activeLSF i).F.F.E :=
  (C.G_succ_isSubgraph_core hH hi).2.1

lemma G_E_subset_of_le {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.d) :
    (C.G j).E ⊆ (C.G i).E := by
  induction j with
  | zero =>
    have h0 : i = 0 := by omega
    subst h0; exact Finset.Subset.refl _
  | succ k ih =>
    by_cases hle : i ≤ k
    · exact Finset.Subset.trans (Finset.Subset.trans (C.G_succ_E_subset hH hj) Finset.sdiff_subset)
        (ih hle (Nat.le_of_lt hj))
    · have heq : i = k + 1 := by omega
      subst heq; exact Finset.Subset.refl _

lemma proj_mem_G_V {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) :
    ∀ i ≤ C.d, ∀ v ∈ (C.G 0).V, C.proj i v ∈ (C.G i).V := by
  intro i hi v hv
  induction i with
  | zero => exact hv
  | succ k ih =>
    have hk : k < C.d := hi
    have hmem := ih (Nat.le_of_lt hk)
    rw [C.G_succ_V_eq hH hk]
    exact (root_mem_R (C.activeLSF_holds hH (Nat.le_of_lt hk)).2.1 hmem).1

lemma proj_eq_self_of_mem_G_V {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) :
    ∀ i ≤ C.d, ∀ v ∈ (C.G i).V, C.proj i v = v := by
  intro i
  induction i with
  | zero => intro _ _ _; rfl
  | succ k ih =>
    intro hk v hv
    have hklt : k < C.d := hk
    have hvGk : v ∈ (C.G k).V := C.G_succ_V_subset hH hklt hv
    have hvR : v ∈ (C.activeLSF k).F.R := (C.G_succ_V_eq hH hklt) ▸ hv
    have hprojk := ih (Nat.le_of_lt hklt) v hvGk
    simp only [proj, hprojk]
    exact root_eq_of_mem_R (C.activeLSF_holds hH (Nat.le_of_lt hklt)).2.1 hvR

lemma G_ends_eq_proj {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) :
    ∀ i ≤ C.d, ∀ e ∈ (C.G i).E,
      (C.G i).tail e = C.proj i ((C.G 0).tail e) ∧
      (C.G i).head e = C.proj i ((C.G 0).head e) := by
  intro i
  induction i with
  | zero => intro _ _ _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro hk e he
    have hklt : k < C.d := hk
    have hSub := C.G_succ_isSubgraph_core hH hklt
    have heCore : e ∈ (C.activeCore k).E := hSub.2.1 he
    have heGk : e ∈ (C.G k).E := (Finset.mem_sdiff.mp heCore).1
    have hEnd := hSub.2.2 e he
    have hIH := ih (Nat.le_of_lt hklt) e heGk
    simp only [proj, ← hIH.1, ← hIH.2]
    exact hEnd

lemma G_src_eq_proj {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i ≤ C.d)
    {x : ℕ × Bool} (hx : x.1 ∈ (C.G i).E) :
    (C.G i).src x = C.proj i ((C.G 0).src x) := by
  have hEnds := C.G_ends_eq_proj hH i hi x.1 hx
  cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnds.1, hEnds.2]

lemma G_dst_eq_proj {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i : ℕ} (hi : i ≤ C.d)
    {x : ℕ × Bool} (hx : x.1 ∈ (C.G i).E) :
    (C.G i).dst x = C.proj i ((C.G 0).dst x) := by
  have hEnds := C.G_ends_eq_proj hH i hi x.1 hx
  cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnds.1, hEnds.2]

lemma activeLSF_E_subset_G_zero {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {i : ℕ} (hi : i ≤ C.d) :
    (C.activeLSF i).F.F.E ⊆ (C.G 0).E :=
  Finset.Subset.trans (hSub i hi).2.1 (C.G_E_subset_of_le hH (Nat.zero_le i) hi)

lemma activeLSF_E_disjoint {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {i j : ℕ} (hij : i < j) (hj : j ≤ C.d) :
    Disjoint (C.activeLSF i).F.F.E (C.activeLSF j).F.F.E := by
  rw [Finset.disjoint_left]
  intro e hei hej
  have heGj : e ∈ (C.G j).E := (hSub j hj).2.1 hej
  have heGi1 : e ∈ (C.G (i + 1)).E := C.G_E_subset_of_le hH hij hj heGj
  have hnot : e ∉ (C.activeLSF i).F.F.E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH (by omega) heGi1)).2
  exact hnot hei

end BasicChainLemmas

section TreeChainTree

private def tailTreeEdges (C : TreeChain) (i : ℕ) : Finset ℕ :=
  (Finset.Ico i (C.d + 1)).biUnion fun m => (C.activeLSF m).F.F.E

private def tailTree (C : TreeChain) (i : ℕ) : MGraph where
  V := (C.G i).V
  E := tailTreeEdges C i
  tail := (C.G i).tail
  head := (C.G i).head

private lemma tailTreeEdges_subset_G_E {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {i : ℕ} (_hi : i ≤ C.d) :
    tailTreeEdges C i ⊆ (C.G i).E := by
  intro e he
  simp only [tailTreeEdges, Finset.mem_biUnion, Finset.mem_Ico] at he
  obtain ⟨m, ⟨him, hm⟩, hem⟩ := he
  have hm_le : m ≤ C.d := Nat.lt_succ_iff.mp hm
  exact C.G_E_subset_of_le hH him hm_le ((hSub m hm_le).2.1 hem)

private lemma tailTree_zero_eq_chainTree : tailTree C 0 = C.chainTree := by
  simp only [tailTree, chainTree, tailTreeEdges, chainTreeEdges, Nat.Ico_zero_eq_range]

private lemma filter_walk_tailTree {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {i : ℕ} (hi : i < C.d) :
    ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, (tailTree C i).IsWalk a b Q →
      (tailTree C (i + 1)).IsWalk ((C.activeLSF i).F.root a) ((C.activeLSF i).F.root b)
        (Q.filter fun x => decide (x.1 ∈ tailTreeEdges C (i + 1))) := by
  intro a b Q hQ
  induction hQ with
  | nil z => exact .nil ((C.activeLSF i).F.root z)
  | @cons a b x Q he hsrc _ ih =>
    simp only [List.filter_cons]
    have heTail : x.1 ∈ tailTreeEdges C i := he
    by_cases heNext : x.1 ∈ tailTreeEdges C (i + 1)
    · simp only [heNext, decide_true, ↓reduceIte]
      have heGi1 : x.1 ∈ (C.G (i + 1)).E :=
        tailTreeEdges_subset_G_E C hH hSub (Nat.succ_le_of_lt hi) heNext
      have hCoreSub := C.G_succ_isSubgraph_core hH hi
      have hEnd := hCoreSub.2.2 x.1 heGi1
      have hsrc' : (tailTree C (i + 1)).src x = (C.activeLSF i).F.root a := by
        have hs : (C.G i).src x = a := hsrc
        cases hx2 : x.2 <;>
          simp [tailTree, MGraph.src, activeCore, coreGraph, hx2, hEnd.1, hEnd.2] at hs ⊢ <;>
          rw [hs]
      have hdst' : (tailTree C (i + 1)).dst x = (C.activeLSF i).F.root ((tailTree C i).dst x) := by
        cases hx2 : x.2 <;>
          simp [tailTree, MGraph.dst, activeCore, coreGraph, hx2, hEnd.1, hEnd.2]
      exact .cons heNext hsrc' (hdst' ▸ ih)
    · simp only [heNext, decide_false, Bool.false_eq_true, ↓reduceIte]
      have heFi : x.1 ∈ (C.activeLSF i).F.F.E := by
        simp only [tailTreeEdges, Finset.mem_biUnion, Finset.mem_Ico] at heTail heNext
        obtain ⟨m, ⟨him, hm⟩, hem⟩ := heTail
        by_cases hm_eq : m = i
        · exact hm_eq ▸ hem
        · exfalso
          exact heNext ⟨m, ⟨by omega, hm⟩, hem⟩
      have hRF := (C.activeLSF_holds hH (Nat.le_of_lt hi)).2.1
      have hSubFi := hSub i (Nat.le_of_lt hi)
      have hroot_eq := root_eq_of_edge_mem_F hRF hSubFi heFi
      have hsd : (C.activeLSF i).F.root a = (C.activeLSF i).F.root ((tailTree C i).dst x) := by
        have hs : (C.G i).src x = a := hsrc
        cases hx2 : x.2
        · simp only [tailTree, MGraph.src, MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte] at hs ⊢
          rw [← hs]
          exact hroot_eq.symm
        · simp only [tailTree, MGraph.src, MGraph.dst, hx2, ↓reduceIte] at hs ⊢
          rw [← hs]
          exact hroot_eq
      rw [hsd]
      exact ih

private lemma no_cycle_tailTree {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    ∀ k ≤ C.d + 1, ∀ P, ¬ (tailTree C (C.d + 1 - k)).IsCycle P := by
  intro k
  induction k with
  | zero =>
    intro _ P hP
    rcases hP with ⟨hPne, _, u, hu⟩
    cases P with
    | nil => exact hPne rfl
    | cons x _ =>
      cases hu with
      | cons he _ _ =>
        simp [tailTree, tailTreeEdges] at he
  | succ k ih =>
    intro hk P hP
    let i := C.d + 1 - (k + 1)
    change (tailTree C i).IsCycle P at hP
    have hi_le : i ≤ C.d := by omega
    rcases hP with ⟨hPne, hPnd, u, hu⟩
    by_cases hHasNext : ∃ x ∈ P, x.1 ∈ tailTreeEdges C (i + 1)
    · have hi_lt : i < C.d := by
        by_contra hnot
        have hieq : i = C.d := by omega
        obtain ⟨x, _, hx⟩ := hHasNext
        rw [hieq] at hx
        simp [tailTreeEdges] at hx
      let P' := P.filter fun x => decide (x.1 ∈ tailTreeEdges C (i + 1))
      have hP'ne : P' ≠ [] := by
        obtain ⟨x, hxP, hxNext⟩ := hHasNext
        intro hnil
        have hmem : x ∈ P' := List.mem_filter.mpr ⟨hxP, decide_eq_true hxNext⟩
        rw [hnil] at hmem
        cases hmem
      have hP'nd : (P'.map Prod.fst).Nodup :=
        (List.Sublist.map Prod.fst (List.filter_sublist)).nodup hPnd
      have hP'w := filter_walk_tailTree C hH hSub hi_lt hu
      have hidx : C.d + 1 - k = i + 1 := by omega
      change (tailTree C (i + 1)).IsWalk ((C.activeLSF i).F.root u) ((C.activeLSF i).F.root u) P' at hP'w
      rw [← hidx] at hP'w
      exact ih (Nat.le_of_succ_le hk) P' ⟨hP'ne, hP'nd, (C.activeLSF i).F.root u, hP'w⟩
    · push Not at hHasNext
      have hFi_walk : ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, (tailTree C i).IsWalk a b Q →
          (∀ x ∈ Q, x.1 ∉ tailTreeEdges C (i + 1)) →
          (C.activeLSF i).F.F.IsWalk a b Q := by
        intro a b Q hQ hQnot
        induction hQ with
        | nil z => exact .nil z
        | @cons a b x Q he hsrc _ ihQ =>
          have hxNot := hQnot x (by simp)
          have heFi : x.1 ∈ (C.activeLSF i).F.F.E := by
            have heTail : x.1 ∈ tailTreeEdges C i := he
            simp only [tailTreeEdges, Finset.mem_biUnion, Finset.mem_Ico] at heTail hxNot
            obtain ⟨m, ⟨him, hm⟩, hem⟩ := heTail
            by_cases hm_eq : m = i
            · exact hm_eq ▸ hem
            · exact absurd ⟨m, ⟨by omega, hm⟩, hem⟩ hxNot
          have hSubFi := hSub i hi_le
          have hEnd := hSubFi.2.2 x.1 heFi
          have hsrcF : (C.activeLSF i).F.F.src x = a := by
            have hs : (C.G i).src x = a := hsrc
            cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnd.1, hEnd.2] at hs ⊢ <;> exact hs
          have hdstF : (C.activeLSF i).F.F.dst x = (tailTree C i).dst x := by
            cases hx2 : x.2 <;> simp [tailTree, MGraph.dst, hx2, hEnd.1, hEnd.2]
          exact .cons heFi hsrcF (hdstF ▸ ihQ (fun y hy => hQnot y (by simp [hy])))
      have hFi_forest := (C.activeLSF_holds hH hi_le).2.1.1
      exact hFi_forest.2 P ⟨hPne, hPnd, u, hFi_walk hu hHasNext⟩

/-- `G_0` has `T^𝒢` as a subgraph whenever `ForestsAreSubgraphs` holds. -/
theorem chainTree_isSubgraph {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    (C.G 0).IsSubgraph C.chainTree := by
  refine ⟨Finset.Subset.refl _, ?_, fun e _ => ⟨rfl, rfl⟩⟩
  intro e he
  simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range] at he
  obtain ⟨i, hi, hei⟩ := he
  exact C.activeLSF_E_subset_G_zero hH hSub (Nat.lt_succ_iff.mp hi) hei

/-- `T^𝒢` is a forest whenever `Holds` and `ForestsAreSubgraphs` hold. -/
theorem chainTree_isForest {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    C.chainTree.IsForest := by
  refine ⟨?_, ?_⟩
  · intro e he
    have hSG := C.chainTree_isSubgraph hH hSub
    have hV0 := C.G_isValid hH 0 (Nat.zero_le C.d) e (hSG.2.1 he)
    exact ⟨hV0.1, hV0.2⟩
  · have hno := no_cycle_tailTree C hH hSub (C.d + 1) (le_refl _)
    simp only [Nat.sub_self, tailTree_zero_eq_chainTree] at hno
    exact hno

private lemma connected_chainTree_of_activeLSF_walk {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) {i : ℕ}
    (hIH : ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V, C.proj i u = C.proj i v → C.chainTree.Connected u v)
    (hi : i ≤ C.d) :
    ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, (C.activeLSF i).F.F.IsWalk a b Q →
      ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V,
        C.proj i u = a → C.proj i v = b → C.chainTree.Connected u v := by
  intro a b Q hQ
  induction hQ with
  | nil z =>
    intro u hu v hv hua hvb
    exact hIH u hu v hv (hua.trans hvb.symm)
  | @cons a b x Q he hsrc _ ihQ =>
    intro u hu v hv hua hvb
    have heGi : x.1 ∈ (C.G i).E := (hSub i hi).2.1 he
    have heG0 : x.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi heGi
    have heEnds0 := C.G_isValid hH 0 (Nat.zero_le C.d) x.1 heG0
    have hux : (C.G 0).src x ∈ (C.G 0).V := by
      cases hx2 : x.2 <;> simp [MGraph.src, hx2, heEnds0.1, heEnds0.2]
    have hvx : (C.G 0).dst x ∈ (C.G 0).V := by
      cases hx2 : x.2 <;> simp [MGraph.dst, hx2, heEnds0.1, heEnds0.2]
    have heTree : x.1 ∈ C.chainTree.E := by
      simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
      exact ⟨i, Nat.lt_succ_of_le hi, he⟩
    have hstep : C.chainTree.Connected ((C.G 0).src x) ((C.G 0).dst x) :=
      ⟨[x], .cons heTree rfl (by simp [chainTree, MGraph.dst]; exact .nil _)⟩
    have hEnd := (hSub i hi).2.2 x.1 he
    have hproj_ux : C.proj i ((C.G 0).src x) = a := by
      rw [← C.G_src_eq_proj hH hi heGi, ← hsrc]
      cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnd.1, hEnd.2]
    have hproj_vx : C.proj i ((C.G 0).dst x) = (C.activeLSF i).F.F.dst x := by
      rw [← C.G_dst_eq_proj hH hi heGi]
      cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnd.1, hEnd.2]
    have h1 := hIH u hu ((C.G 0).src x) hux (hua.trans hproj_ux.symm)
    have h2 := ihQ ((C.G 0).dst x) hvx v hv hproj_vx hvb
    exact MGraph.connected_trans h1 (MGraph.connected_trans hstep h2)

/-- Vertices of `G_0` with the same `i`-level projection (`i ≤ d + 1`) are connected in `T^𝒢`. -/
theorem connected_chainTree_of_proj_eq {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs) :
    ∀ i ≤ C.d + 1, ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V,
      C.proj i u = C.proj i v → C.chainTree.Connected u v := by
  intro i
  induction i with
  | zero =>
    intro _ u _ v _ heq
    rw [show u = v from heq]
    exact MGraph.connected_refl C.chainTree v
  | succ k ih =>
    intro hk u hu v hv heq
    have hk_le : k ≤ C.d := Nat.le_of_succ_le_succ hk
    have hIH := ih (Nat.le_of_lt hk)
    have huGk : C.proj k u ∈ (C.G k).V := C.proj_mem_G_V hH k hk_le u hu
    have hvGk : C.proj k v ∈ (C.G k).V := C.proj_mem_G_V hH k hk_le v hv
    have hRF := (C.activeLSF_holds hH hk_le).2.1
    change (C.activeLSF k).F.root (C.proj k u) = (C.activeLSF k).F.root (C.proj k v) at heq
    have hconn := connected_of_root_eq hRF huGk hvGk heq
    obtain ⟨Q, hQ⟩ := hconn
    exact connected_chainTree_of_activeLSF_walk C hH hSub hIH hk_le hQ u hu v hv rfl rfl

private lemma connected_chainTree_of_G_level {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) :
    ∀ k ≤ C.d, ∀ a ∈ (C.G (C.d - k)).V, ∀ b ∈ (C.G (C.d - k)).V,
      (C.G (C.d - k)).Connected a b → C.chainTree.Connected a b := by
  intro k
  induction k with
  | zero =>
    intro _ a ha b hb hconn
    simp only [Nat.sub_zero] at ha hb hconn ⊢
    have hFconn := hSpan a ha b hb hconn
    obtain ⟨Q, hQ⟩ := hFconn
    have hproj := C.connected_chainTree_of_proj_eq hH hSub C.d (Nat.le_succ C.d)
    have ha0 := C.G_V_subset_of_le hH (Nat.zero_le C.d) (le_refl C.d) ha
    have hb0 := C.G_V_subset_of_le hH (Nat.zero_le C.d) (le_refl C.d) hb
    have hpa := C.proj_eq_self_of_mem_G_V hH C.d (le_refl C.d) a ha
    have hpb := C.proj_eq_self_of_mem_G_V hH C.d (le_refl C.d) b hb
    exact connected_chainTree_of_activeLSF_walk C hH hSub hproj (le_refl C.d) hQ a ha0 b hb0 hpa hpb
  | succ k ih =>
    intro hk a ha b hb hconn
    let i := C.d - (k + 1)
    change a ∈ (C.G i).V at ha
    change b ∈ (C.G i).V at hb
    change (C.G i).Connected a b at hconn
    have hi_lt : i < C.d := by omega
    have hidx : C.d - k = i + 1 := by omega
    have ih' : ∀ x ∈ (C.G (i + 1)).V, ∀ y ∈ (C.G (i + 1)).V,
        (C.G (i + 1)).Connected x y → C.chainTree.Connected x y := by
      simpa only [hidx] using ih (Nat.le_of_succ_le hk)
    obtain ⟨Q, hQ⟩ := hconn
    have hproj_step : ∀ {x y : ℕ}, (C.G i).IsWalk x y Q →
        x ∈ (C.G i).V → C.chainTree.Connected x y := by
      intro x y hW hxV
      clear a ha b hb hQ
      induction hW with
      | nil z => exact MGraph.connected_refl C.chainTree z
      | @cons x y z Q he hsrc _ ihW =>
        have hvalid := C.G_isValid hH i (Nat.le_of_lt hi_lt) z.1 he
        have hdstV : (C.G i).dst z ∈ (C.G i).V := by
          cases hz2 : z.2 <;> simp [MGraph.dst, hz2, hvalid.1, hvalid.2]
        have htail_conn := ihW hdstV
        have hstep_conn : C.chainTree.Connected x ((C.G i).dst z) := by
          have hx_is : x = (C.G i).src z := hsrc.symm
          rw [hx_is]
          by_cases heF : z.1 ∈ (C.activeLSF i).F.F.E
          · have heG0 : z.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) (Nat.le_of_lt hi_lt) he
            have heTree : z.1 ∈ C.chainTree.E := by
              simp only [chainTree, chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
              exact ⟨i, by omega, heF⟩
            have hEnds0 := C.G_isValid hH 0 (Nat.zero_le C.d) z.1 heG0
            have hsrc0V : (C.G 0).src z ∈ (C.G 0).V := by
              cases hz2 : z.2 <;> simp [MGraph.src, hz2, hEnds0.1, hEnds0.2]
            have hdst0V : (C.G 0).dst z ∈ (C.G 0).V := by
              cases hz2 : z.2 <;> simp [MGraph.dst, hz2, hEnds0.1, hEnds0.2]
            have hx0V : (C.G i).src z ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le i) (Nat.le_of_lt hi_lt) (hsrc.symm ▸ hxV)
            have hy0V : (C.G i).dst z ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le i) (Nat.le_of_lt hi_lt) hdstV
            have hp1 : C.proj i ((C.G i).src z) = C.proj i ((C.G 0).src z) := by
              rw [C.proj_eq_self_of_mem_G_V hH i (Nat.le_of_lt hi_lt) _ (hsrc.symm ▸ hxV)]
              exact C.G_src_eq_proj hH (Nat.le_of_lt hi_lt) he
            have hp2 : C.proj i ((C.G 0).dst z) = C.proj i ((C.G i).dst z) := by
              rw [C.proj_eq_self_of_mem_G_V hH i (Nat.le_of_lt hi_lt) _ hdstV]
              exact (C.G_dst_eq_proj hH (Nat.le_of_lt hi_lt) he).symm
            have hproj_fn := C.connected_chainTree_of_proj_eq hH hSub i (Nat.le_succ_of_le (Nat.le_of_lt hi_lt))
            have hleft := hproj_fn ((C.G i).src z) hx0V ((C.G 0).src z) hsrc0V hp1
            have hmid : C.chainTree.Connected ((C.G 0).src z) ((C.G 0).dst z) :=
              ⟨[z], .cons heTree rfl (by simp [chainTree, MGraph.dst]; exact .nil _)⟩
            have hright := hproj_fn ((C.G 0).dst z) hdst0V ((C.G i).dst z) hy0V hp2
            exact MGraph.connected_trans hleft (MGraph.connected_trans hmid hright)
          · have heCore : z.1 ∈ (C.activeCore i).E := Finset.mem_sdiff.mpr ⟨he, heF⟩
            have hSp := C.activeS_isSparsified hH hi_lt
            have hWemb := hSp.2.1.2 z.1 heCore
            rw [C.activeS_eq_G_succ hH hi_lt] at hWemb
            have hG1conn : (C.G (i + 1)).Connected ((C.activeLSF i).F.root ((C.G i).src z))
                ((C.activeLSF i).F.root ((C.G i).dst z)) := by
              cases hz2 : z.2
              · simp only [MGraph.src, MGraph.dst, hz2, Bool.false_eq_true, ↓reduceIte]
                exact ⟨walkRev (C.activeEmb i z.1), MGraph.isWalk_walkRev hWemb⟩
              · simp only [MGraph.src, MGraph.dst, hz2, ↓reduceIte]
                exact ⟨C.activeEmb i z.1, hWemb⟩
            have hr1V : (C.activeLSF i).F.root ((C.G i).src z) ∈ (C.G (i + 1)).V := by
              rw [C.G_succ_V_eq hH hi_lt]
              exact (root_mem_R (C.activeLSF_holds hH (Nat.le_of_lt hi_lt)).2.1 (hsrc.symm ▸ hxV)).1
            have hr2V : (C.activeLSF i).F.root ((C.G i).dst z) ∈ (C.G (i + 1)).V := by
              rw [C.G_succ_V_eq hH hi_lt]
              exact (root_mem_R (C.activeLSF_holds hH (Nat.le_of_lt hi_lt)).2.1 hdstV).1
            have hmid := ih' _ hr1V _ hr2V hG1conn
            have hsrc0V : (C.G i).src z ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le i) (Nat.le_of_lt hi_lt) (hsrc.symm ▸ hxV)
            have hdst0V : (C.G i).dst z ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le i) (Nat.le_of_lt hi_lt) hdstV
            have hr1_0V : (C.activeLSF i).F.root ((C.G i).src z) ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le (i + 1)) (Nat.succ_le_of_lt hi_lt) hr1V
            have hr2_0V : (C.activeLSF i).F.root ((C.G i).dst z) ∈ (C.G 0).V :=
              C.G_V_subset_of_le hH (Nat.zero_le (i + 1)) (Nat.succ_le_of_lt hi_lt) hr2V
            have hp1 : C.proj (i + 1) ((C.G i).src z) =
                C.proj (i + 1) ((C.activeLSF i).F.root ((C.G i).src z)) := by
              rw [C.proj_eq_self_of_mem_G_V hH (i + 1) (Nat.succ_le_of_lt hi_lt) _ hr1V]
              change (C.activeLSF i).F.root (C.proj i ((C.G i).src z)) = _
              rw [C.proj_eq_self_of_mem_G_V hH i (Nat.le_of_lt hi_lt) _ (hsrc.symm ▸ hxV)]
            have hp2 : C.proj (i + 1) ((C.activeLSF i).F.root ((C.G i).dst z)) =
                C.proj (i + 1) ((C.G i).dst z) := by
              rw [C.proj_eq_self_of_mem_G_V hH (i + 1) (Nat.succ_le_of_lt hi_lt) _ hr2V]
              change _ = (C.activeLSF i).F.root (C.proj i ((C.G i).dst z))
              rw [C.proj_eq_self_of_mem_G_V hH i (Nat.le_of_lt hi_lt) _ hdstV]
            have hproj_fn := C.connected_chainTree_of_proj_eq hH hSub (i + 1) (by omega)
            have hleft := hproj_fn ((C.G i).src z) hsrc0V _ hr1_0V hp1
            have hright := hproj_fn _ hr2_0V ((C.G i).dst z) hdst0V hp2
            exact MGraph.connected_trans hleft (MGraph.connected_trans hmid hright)
        exact MGraph.connected_trans hstep_conn htail_conn
    exact hproj_step hQ ha

/-- Any two vertices connected in `G_0` are connected in `T^𝒢` when `Holds`,
`ForestsAreSubgraphs`, and `LastLevelSpans` hold. -/
theorem chainTree_connected_of_connected {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans) {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V)
    (hconn : G.Connected u v) : C.chainTree.Connected u v := by
  have h := connected_chainTree_of_G_level C hH hSub hSpan C.d (le_refl C.d)
  simp only [Nat.sub_self, hH.1] at h
  exact h u hu v hv hconn

/-- When `G` is connected, `T^𝒢` is a spanning tree of `G` under `Holds`, `ForestsAreSubgraphs`,
and `LastLevelSpans`. -/
theorem chainTree_isSpanningTreeOn {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hSpan : C.LastLevelSpans)
    (hGconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    C.chainTree.IsSpanningTreeOn G.V := by
  refine ⟨C.chainTree_isForest hH hSub, ?_, ?_⟩
  · simp [chainTree, hH.1]
  · intro u hu v hv
    exact C.chainTree_connected_of_connected hH hSub hSpan hu hv (hGconn u hu v hv)

/-- At level `d`, having at most one root suffices for `LastLevelSpans` (e.g. when `F_d` is a
spanning tree of a connected `G_d`). -/
lemma lastLevelSpans_of_card_root_le_one {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hcard : (C.activeLSF C.d).F.R.card ≤ 1) : C.LastLevelSpans := by
  intro u hu v hv _
  have hRF := (C.activeLSF_holds hH (le_refl C.d)).2.1
  have hru := root_mem_R hRF hu
  have hrv := root_mem_R hRF hv
  have hreq : (C.activeLSF C.d).F.root u = (C.activeLSF C.d).F.root v :=
    Finset.card_le_one.mp hcard _ hru.1 _ hrv.1
  exact connected_of_root_eq hRF hu hv hreq

end TreeChainTree

section PassingDownChain

/-- Passing a valid pair `(c, w)` down a `TreeChain` preserves validity at every level `i ≤ d` and
nonnegativity of `chainLen`. -/
theorem chain_isValidPair {G : MGraph} {ℓ c w : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    (hℓ : ∀ e ∈ G.E, 0 ≤ ℓ e) (hvp : IsValidPair G ℓ c w) :
    ∀ i ≤ C.d,
      IsValidPair (C.G i) (C.chainLen ℓ i) (C.chainC c i) (C.chainW w i) ∧
      (∀ e ∈ (C.G i).E, 0 ≤ C.chainLen ℓ i e) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [chainLen, chainC, chainW, hH.1] using ⟨hvp, hℓ⟩
  | succ k ih =>
    intro hk
    have hk_lt : k < C.d := hk
    obtain ⟨hvp_k, hℓ_k⟩ := ih (Nat.le_of_lt hk_lt)
    have hGkValid := C.G_isValid hH k (Nat.le_of_lt hk_lt)
    have hLk := C.activeLSF_holds hH (Nat.le_of_lt hk_lt)
    have hSubk := hSub k (Nat.le_of_lt hk_lt)
    have hCore := lemma_5_13 hGkValid hLk hSubk hℓ_k hvp_k
    have hSp := C.activeS_isSparsified hH hk_lt
    have hSparse := lemma_5_16_noSize hSp hCore.1
    have hEq := C.activeS_eq_G_succ hH hk_lt
    have hvp_next : IsValidPair (C.G (k + 1)) (C.chainLen ℓ (k + 1))
        (C.chainC c (k + 1)) (C.chainW w (k + 1)) := by
      simpa only [chainLen, chainC, chainW, activeCore, hEq] using hSparse.1
    refine ⟨hvp_next, ?_⟩
    intro e he
    have heGk : e ∈ (C.G k).E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hk_lt he)).1
    have hwstr0 : 0 ≤ (C.activeLSF k).wstr e := by
      have h1 := one_le_stretch hSubk hℓ_k heGk
      have h2 := (hLk.2.2.2 e heGk).1
      linarith
    exact mul_nonneg hwstr0 (hℓ_k e heGk)

end PassingDownChain

private theorem isForest_singleton_edge (V : Finset ℕ) (e₀ a b : ℕ)
    (ha : a ∈ V) (hb : b ∈ V) (hne : a ≠ b) :
    (MGraph.mk V {e₀} (fun _ => a) (fun _ => b)).IsForest := by
  let F : MGraph := ⟨V, {e₀}, fun _ => a, fun _ => b⟩
  refine ⟨fun e he => ?_, fun P hP => ?_⟩
  · have : e = e₀ := by simpa [F] using he
    subst this; exact ⟨ha, hb⟩
  · rcases hP with ⟨hPne, hPnd, u, hu⟩
    cases hPeq : P with
    | nil => exact hPne hPeq
    | cons x xs =>
      rw [hPeq] at hu hPnd
      cases hu with
      | cons he hx hrest =>
        have hxe : x.1 = e₀ := by simpa [F] using he
        cases xs with
        | nil =>
          have hdst : F.dst x = u := by cases hrest; rfl
          rw [← hx] at hdst
          cases hx2 : x.2 <;> simp [F, MGraph.src, MGraph.dst, hx2] at hdst <;>
            exact absurd hdst (by first | exact hne | exact hne.symm)
        | cons y ys =>
          have hye : y.1 = e₀ := by simpa [F] using MGraph.isWalk_edges_mem hrest y (by simp)
          simp [hxe, hye] at hPnd

private theorem walkLength_singleton_edge_le (V : Finset ℕ) (e₀ a b : ℕ)
    (w : ℝ) (hw : 0 ≤ w) (ℓ' : ℕ → ℝ) (hℓ : ℓ' e₀ ≤ w) (hℓ0 : 0 ≤ ℓ' e₀) (u v : ℕ) :
    walkLength ℓ' (MGraph.forestPath (MGraph.mk V {e₀} (fun _ => a) (fun _ => b)) u v) ≤ w := by
  let F : MGraph := ⟨V, {e₀}, fun _ => a, fun _ => b⟩
  by_cases huv : F.Connected u v
  · have hp := MGraph.isPath_forestPath huv
    have hnd := MGraph.isPath_edges_nodup hp
    have hsub : ((MGraph.forestPath F u v).map Prod.fst).toFinset ⊆ {e₀} := by
      intro c hc
      rw [List.mem_toFinset, List.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      simpa [F] using MGraph.isWalk_edges_mem hp.1 x hx
    have hc := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, List.length_map] at hc
    have h1 : walkLength ℓ' (MGraph.forestPath F u v) =
        ℓ' e₀ * ∑ e' ∈ walkEdges (MGraph.forestPath F u v), |walkFlow (MGraph.forestPath F u v) e'| := by
      unfold walkLength
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e' he' => ?_
      have heeq : e' ∈ ({e₀} : Finset ℕ) := hsub (by simpa [walkEdges] using he')
      rw [Finset.mem_singleton.mp heeq]
    rw [h1]
    have hsum := sum_abs_walkFlow_le_length (walkEdges (MGraph.forestPath F u v)) (MGraph.forestPath F u v)
    have hlen : ((MGraph.forestPath F u v).length : ℝ) ≤ 1 := by simpa using hc
    calc
      ℓ' e₀ * ∑ e' ∈ walkEdges (MGraph.forestPath F u v), |walkFlow (MGraph.forestPath F u v) e'|
          ≤ ℓ' e₀ * 1 := mul_le_mul_of_nonneg_left (le_trans hsum hlen) hℓ0
      _ ≤ w := by simpa using hℓ
  · have hemp : MGraph.forestPath F u v = [] := by
      classical
      unfold MGraph.forestPath
      rw [dite_eq_right_iff]
      intro ⟨P, hP⟩; exact absurd ⟨P, hP.1⟩ huv
    change walkLength ℓ' (F.forestPath u v) ≤ w
    rw [hemp, walkLength_nil]
    exact hw

/-- Existence witness showing that `Holds`, `ForestsAreSubgraphs`, `LastLevelSpans`,
`EmbedsSurviving`, and connectivity of `G` can all hold simultaneously on a concrete `1`-level
chain over a triangle graph. -/
theorem treeChain_exists_example :
    ∃ (C : TreeChain) (G : MGraph) (ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ),
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      C.ForestsAreSubgraphs ∧
      C.LastLevelSpans ∧
      C.EmbedsSurviving ∧
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) ∧
      C.chainTree.IsSpanningTreeOn G.V := by
  let G : MGraph :=
    ⟨{0, 1, 2}, {0, 1, 2},
      fun e => if e = 0 then 0 else if e = 1 then 1 else 0,
      fun e => if e = 0 then 1 else if e = 1 then 2 else 2⟩
  let F0 : MGraph :=
    ⟨{0, 1, 2}, {0}, fun _ => 0, fun _ => 1⟩
  let RF0 : RootedForest := ⟨F0, {0, 2}⟩
  let L0 : LSF := ⟨F0, RF0, fun _ => 4⟩
  let S0 : MGraph := ⟨{0, 2}, {1, 2}, fun _ => 0, fun _ => 2⟩
  let emb0 : Embedding := fun e => [(e, true)]
  let F1 : MGraph := ⟨{0, 2}, {1}, fun _ => 0, fun _ => 2⟩
  let RF1 : RootedForest := ⟨F1, {0}⟩
  let L1 : LSF := ⟨F1, RF1, fun _ => 4⟩
  let ℓ : ℕ → ℝ := fun _ => 1
  let C : TreeChain :=
    { d := 1
      k := 1
      G := fun i => if i = 0 then G else S0
      lsfs := fun _ _ => L0
      bran := fun _ => 0
      S := fun _ _ => S0
      emb := fun _ _ => emb0
      lastK := 1
      lastLSFs := fun _ => L1
      lastBran := 0 }
  have hG : G.IsValid := by
    intro e he
    simp only [G, Finset.mem_insert, Finset.mem_singleton] at he ⊢
    rcases he with rfl | rfl | rfl <;> simp
  have hF0_forest : F0.IsForest :=
    isForest_singleton_edge {0, 1, 2} 0 0 1 (by simp) (by simp) (by decide)
  have hstep01 : ∀ {a b : ℕ} {Q : List (ℕ × Bool)},
      F0.IsWalk a b Q → (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) := by
    intro a b Q hW ha
    induction hW with
    | nil _ => exact ha
    | @cons a b z Q he _ _ ih =>
      have hdst : F0.dst z = 0 ∨ F0.dst z = 1 := by
        cases hz2 : z.2 <;> simp [F0, MGraph.dst, hz2]
      exact ih hdst
  have hRF0 : RF0.IsRootedSpanningForestOf G := by
    refine ⟨hF0_forest, rfl, by simp [RF0, G], ?_, ?_⟩
    swap
    · refine ⟨by simp [RF0, F0, G], by simp [RF0, F0, G], fun e he => ?_⟩
      have : e = 0 := by simpa [RF0, F0] using he
      subst this; simp [RF0, F0, G]
    intro v hv
    simp only [G, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · refine ⟨0, ⟨by simp [RF0], MGraph.connected_refl F0 0⟩, ?_⟩
      rintro r ⟨hr, hconn⟩
      simp only [RF0, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨P, hP⟩ := hconn
        have hres := hstep01 hP (Or.inl rfl)
        omega
    · refine ⟨0, ⟨by simp [RF0], ⟨[(0, false)], .cons (by simp [RF0, F0]) (by simp [RF0, F0, MGraph.src])
          (by simp [RF0, F0, MGraph.dst]; exact .nil 0)⟩⟩, ?_⟩
      rintro r ⟨hr, hconn⟩
      simp only [RF0, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨P, hP⟩ := hconn
        have hres := hstep01 hP (Or.inr rfl)
        omega
    · refine ⟨2, ⟨by simp [RF0], MGraph.connected_refl F0 2⟩, ?_⟩
      rintro r ⟨hr, hconn⟩
      simp only [RF0, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exfalso
        obtain ⟨P, hP⟩ := hconn
        cases hP with
        | @cons a b x Q he hsrc _ =>
          cases hx2 : x.2 <;> simp [RF0, F0, MGraph.src, hx2] at hsrc
      · rfl
  have hr0_0 : RF0.root 0 = 0 := root_eq_of_mem_R hRF0 (by simp [RF0])
  have hr0_2 : RF0.root 2 = 2 := root_eq_of_mem_R hRF0 (by simp [RF0])
  have hr0_1 : RF0.root 1 = 0 := by
    have hconn : F0.Connected 1 0 :=
      ⟨[(0, false)], .cons (by simp [F0]) (by simp [F0, MGraph.src])
        (by simp [F0, MGraph.dst]; exact .nil 0)⟩
    exact (root_eq_of_connected hRF0 (by simp [G]) (by simp [G]) hconn).trans hr0_0
  have hSub0 : G.IsSubgraph F0 := by
    refine ⟨by simp [F0, G], by simp [F0, G], fun e he => ?_⟩
    have : e = 0 := by simpa [F0] using he
    subst this; simp [F0, G]
  have hL0 : L0.Holds G ℓ 4 := by
    refine ⟨hF0_forest, hRF0, ⟨by simp [L0, RF0], by simp [L0, RF0], fun e _ => ⟨rfl, rfl⟩⟩, ?_⟩
    intro e _
    refine ⟨?_, by simp [L0]⟩
    have hfp : ∀ u v : ℕ, walkLength ℓ (MGraph.forestPath F0 u v) ≤ 1 :=
      walkLength_singleton_edge_le {0, 1, 2} 0 0 1 1 (by norm_num) ℓ (by norm_num [ℓ]) (by norm_num [ℓ])
    unfold RootedForest.stretch
    change (if RF0.root (G.tail e) = RF0.root (G.head e) then
        1 + walkLength ℓ (F0.forestPath (G.tail e) (G.head e)) / ℓ e
      else 1 + (walkLength ℓ (F0.forestPath (G.tail e) (RF0.root (G.tail e))) +
        walkLength ℓ (F0.forestPath (G.head e) (RF0.root (G.head e)))) / ℓ e) ≤ 4
    have hℓe : ℓ e = 1 := rfl
    rw [hℓe, div_one, div_one]
    split_ifs
    · linarith [hfp (G.tail e) (G.head e)]
    · linarith [hfp (G.tail e) (RF0.root (G.tail e)), hfp (G.head e) (RF0.root (G.head e))]
  have hF1_forest : F1.IsForest :=
    isForest_singleton_edge {0, 2} 1 0 2 (by simp) (by simp) (by decide)
  have hRF1 : RF1.IsRootedSpanningForestOf S0 := by
    refine ⟨hF1_forest, rfl, by simp [RF1, S0], ?_, ?_⟩
    swap
    · refine ⟨by simp [RF1, F1, S0], by simp [RF1, F1, S0], fun e he => ?_⟩
      have : e = 1 := by simpa [RF1, F1] using he
      subst this; simp [RF1, F1, S0]
    intro v hv
    refine ⟨0, ⟨by simp [RF1], ?_⟩, ?_⟩
    · simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact MGraph.connected_refl F1 0
      · exact ⟨[(1, false)], .cons (by simp [RF1, F1]) (by simp [RF1, F1, MGraph.src])
          (by simp [RF1, F1, MGraph.dst]; exact .nil 0)⟩
    · rintro r ⟨hr, _⟩
      simpa [RF1] using hr
  have hr1_0 : RF1.root 0 = 0 := root_eq_of_mem_R hRF1 (by simp [RF1])
  have hr1_2 : RF1.root 2 = 0 := by
    have h2V : (2 : ℕ) ∈ S0.V := by simp [S0]
    simpa [RF1] using (root_mem_R hRF1 h2V).1
  have hL1 : L1.Holds S0 (C.chainLen ℓ 1) 4 := by
    refine ⟨hF1_forest, hRF1, ⟨by simp [L1, RF1], by simp [L1, RF1], fun e _ => ⟨rfl, rfl⟩⟩, ?_⟩
    intro e _
    refine ⟨?_, by simp [L1]⟩
    have hlen4 : ∀ e' : ℕ, C.chainLen ℓ 1 e' = 4 := by
      intro e'
      simp [chainLen, activeLSF, coreLen, C, L0, ℓ]
    have hfp : ∀ u v : ℕ, walkLength (C.chainLen ℓ 1) (MGraph.forestPath F1 u v) ≤ 4 :=
      walkLength_singleton_edge_le {0, 2} 1 0 2 4 (by norm_num) (C.chainLen ℓ 1)
        (by rw [hlen4 1]) (by rw [hlen4 1]; norm_num)
    unfold RootedForest.stretch
    change (if RF1.root (S0.tail e) = RF1.root (S0.head e) then
        1 + walkLength (C.chainLen ℓ 1) (F1.forestPath (S0.tail e) (S0.head e)) / C.chainLen ℓ 1 e
      else 1 + (walkLength (C.chainLen ℓ 1) (F1.forestPath (S0.tail e) (RF1.root (S0.tail e))) +
        walkLength (C.chainLen ℓ 1) (F1.forestPath (S0.head e) (RF1.root (S0.head e)))) /
          C.chainLen ℓ 1 e) ≤ 4
    have htail : S0.tail e = 0 := rfl
    have hhead : S0.head e = 2 := rfl
    simp only [htail, hhead, hr1_0, hr1_2, ↓reduceIte, hlen4 e]
    linarith [hfp 0 2]
  have hCore0_E : (coreGraph G L0).E = {1, 2} := by
    ext e
    simp only [coreGraph, L0, RF0, F0, G, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hS0_isSp : IsSparsifiedCoreGraph G L0 ℓ 1 1 1 S0 emb0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simp [S0, coreGraph, L0, RF0], by rw [hCore0_E], fun e he => ?_⟩
      simp only [S0, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · simp [coreGraph, G, L0, hr0_1, hr0_2, S0]
      · simp [coreGraph, G, L0, hr0_0, hr0_2, S0]
    · refine ⟨by simp [S0, coreGraph, L0, RF0], fun e he => ?_⟩
      rw [hCore0_E] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · refine .cons (by simp [S0]) ?_ ?_
        · simp [coreGraph, G, L0, hr0_1, S0, MGraph.src]
        · simp [S0, MGraph.dst, coreGraph, G, L0, hr0_2]; exact .nil 2
      · refine .cons (by simp [S0]) ?_ ?_
        · simp [coreGraph, G, L0, hr0_0, S0, MGraph.src]
        · simp [S0, MGraph.dst, coreGraph, G, L0, hr0_2]; exact .nil 2
    · intro e _ e' he'
      have heq : e' = e := by simpa [emb0, walkEdges] using he'
      subst heq
      norm_num [approx2, coreLen, L0, ℓ]
    · have hlen_le : emb0.length (coreGraph G L0) ≤ 1 := by
        unfold Embedding.length
        refine Finset.sup_le fun e _ => ?_
        simp [emb0]
      exact_mod_cast hlen_le
    · unfold Embedding.econg
      by_cases hne : S0.E.Nonempty
      · simp only [hne, ↓reduceDIte]
        refine Finset.sup'_le _ _ fun e' _ => ?_
        unfold Embedding.econgAt
        rw [hCore0_E, div_one]
        have hsub : (Finset.filter (fun e => e' ∈ walkEdges (emb0 e)) {1, 2}) ⊆ {e'} := by
          intro a ha
          simp only [Finset.mem_filter, walkEdges, emb0, List.map_cons, List.map_nil,
            List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at ha ⊢
          exact ha.2.symm
        have hc : (Finset.filter (fun e => e' ∈ walkEdges (emb0 e)) {1, 2}).card ≤ 1 :=
          le_trans (Finset.card_le_card hsub) (by simp)
        simpa using (show ((Finset.filter (fun e => e' ∈ walkEdges (emb0 e)) {1, 2}).card : ℝ) ≤ 1 by
          exact_mod_cast hc)
      · simp only [hne, ↓reduceDIte]
        norm_num
    · have hc : S0.E.card ≤ 2 := by simp [S0]
      have hm : G.m = 3 := by simp [G, MGraph.m]
      rw [hm]
      norm_num
      exact_mod_cast (by omega : S0.E.card ≤ 3)
  have hH : C.Holds G ℓ 4 4 1 1 := by
    refine ⟨rfl, hG, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by simpa [C] using hi
      subst hi0
      refine ⟨by norm_num [C], fun j _ => ⟨?_, ?_⟩, ?_, rfl⟩
      · simpa [C, chainLen] using hL0
      · simpa [C, chainLen] using hS0_isSp.toNoSize
      · intro e _
        norm_num [C, L0]
    · intro j _
      simpa [C] using hL1
    · intro e _
      norm_num [C, L1]
  have hSub : C.ForestsAreSubgraphs := by
    intro i hi
    have hcases : i = 0 ∨ i = 1 := by simp [C] at hi; omega
    rcases hcases with rfl | rfl
    · simpa [C, activeLSF, L0] using hSub0
    · refine ⟨by simp [C, activeLSF, L1, RF1, F1, S0], by simp [C, activeLSF, L1, RF1, F1, S0],
        fun e he => ?_⟩
      have he1 : e = 1 := by simpa [C, activeLSF, L1, RF1, F1] using he
      subst he1
      simp [C, activeLSF, L1, RF1, F1, S0]
  have hSpan : C.LastLevelSpans :=
    C.lastLevelSpans_of_card_root_le_one hH (by simp [C, activeLSF, L1, RF1])
  have hEmbSurv : C.EmbedsSurviving := by
    intro i hi e _
    have hi0 : i = 0 := by simpa [C] using hi
    subst hi0
    rfl
  have hGconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v := by
    have h01 : G.Connected 0 1 :=
      ⟨[(0, true)], .cons (by simp [G]) (by simp [G, MGraph.src]) (by simp [G, MGraph.dst]; exact .nil 1)⟩
    have h02 : G.Connected 0 2 :=
      ⟨[(2, true)], .cons (by simp [G]) (by simp [G, MGraph.src]) (by simp [G, MGraph.dst]; exact .nil 2)⟩
    have h12 := MGraph.connected_trans (MGraph.connected_symm h01) h02
    intro u hu v hv
    simp only [G, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact MGraph.connected_refl G 0
    · exact h01
    · exact h02
    · exact MGraph.connected_symm h01
    · exact MGraph.connected_refl G 1
    · exact h12
    · exact MGraph.connected_symm h02
    · exact MGraph.connected_symm h12
    · exact MGraph.connected_refl G 2
  exact ⟨C, G, ℓ, 4, 4, 1, 1, hH, hSub, hSpan, hEmbSurv, hGconn,
    C.chainTree_isSpanningTreeOn hH hSub hSpan hGconn⟩

end TreeChain

end MinCostFlow.Chain
