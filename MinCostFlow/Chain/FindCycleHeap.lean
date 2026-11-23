module

public import MinCostFlow.Chain.FindCycleProofs
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heap-key properties for `algorithm1_findCycle` (`jtree.tex`, pages 21 and 24)

This file proves the structural properties of the own-level candidate key
`heapCycleRatio C g ℓ e = |⟨g^{𝒞(G_i, F_i)}, a(e)⟩| / wlen_{e^G}` (`i = C.edgeLevel e`) that
underlie the paper's heap-based implementation of `FindCycle` (`jtree.tex`, lines 331 and 494–518):

1. `heapCycleRatio_eq_at`: at level `i ≤ d`, `heapCycleRatio C g ℓ e` for
   `e ∈ (C.activeCore i).E \ (C.activeS i).E` evaluates directly at level `i`.
2. `walkInner_fundChainCycle_nonpos_iff`: the sign of `⟨g, a^G(e^G)⟩` (used to orient the cycle
   returned by `algorithm1_findCycle`) equals the sign of the heap numerator
   `⟨g^{𝒞(G_i, F_i)}, a(e)⟩`.
3. `walkInner_chainGrad_congr_G0` and `heapCycleRatio_congr_g_G0`: `heapCycleRatio` depends on `g`
   only on live edges `(C.G 0).E` (changing `g` on deleted edges of `T_0 \ G_0` does not change any
   key).
4. `potGrad`, `potGrad_eq_sum`, `walkInner_potGrad_eq_chainGrad`, and `potGrad_treeRootPot_of_agree`:
   replacing `treeRootPot L_j.T (chainGrad g j)` with any static per-level potential `φ j` matching
   the active forest paths `(C.activeLSF j).F.F` (in particular, the frozen initialization potential
   `treeRootPot L_j.T gInit_j` when `gInit_j` agrees with `potGrad` on surviving forest edges) gives
   the exact same heap numerator for every candidate cycle.
5. `heapCycleRatio_congr_prefix`: a `Shift(i₀)` or `Rebuild(i₀)` leaves every key at levels `i < i₀`
   unchanged.
6. `heapCycleRatio_eq_of_unchanged_emb`: across a non-rebuilding update on levels `0..i`
   (decremental active forests `F'_j ⊆ F_j`, immutable stretches `wstr_j`, unchanged `g`, `ℓ`, and
   `G_0`-endpoints on surviving edges), any surviving candidate `e` at level `i` whose embedding
   `activeEmb i e` did not change keeps the exact same `heapCycleRatio`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section BasicKeyLemmas

/-- At level `i ≤ C.d`, `heapCycleRatio` for `e ∈ (C.activeCore i).E \ (C.activeS i).E` evaluates
directly at level `i`. -/
lemma heapCycleRatio_eq_at (C : TreeChain) {G : MGraph} {ℓ g : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {i e : ℕ} (hi : i ≤ C.d)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    heapCycleRatio C g ℓ e =
      |walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e)| / C.wlenAt ℓ i e := by
  have hlvl : C.edgeLevel e = i := C.edgeLevel_eq_of_mem hH hi he
  unfold heapCycleRatio TreeChain.wlen
  rw [hlvl]

/-- The orientation test `walkInner g (C.fundChainCycle e) ≤ 0` of `algorithm1_findCycle` agrees
with the sign of the own-level heap numerator `walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e)`. -/
lemma walkInner_fundChainCycle_nonpos_iff (C : TreeChain) {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    {e : ℕ} (he : e ∈ (C.G 0).E \ C.chainTree.E) :
    walkInner g (C.fundChainCycle e) ≤ 0 ↔
      walkInner (C.chainGrad g (C.edgeLevel e + 1)) (C.sparsifierCycle (C.edgeLevel e) e) ≤ 0 := by
  have hlvl := C.mem_activeCore_diff_edgeLevel hH he
  rw [C.lemma_7_12 hH hSpan hlvl.1 hlvl.2]
  rfl

/-- Changing `g` outside the live edge set `(C.G 0).E` (for instance, on deleted edges of a static
tree `T_0 \ G_0`) does not change the core-graph numerator of any candidate cycle. -/
theorem walkInner_chainGrad_congr_G0 (C : TreeChain) {G : MGraph} {ℓ g₁ g₂ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hg : ∀ f ∈ (C.G 0).E, g₁ f = g₂ f) {i e : ℕ} (hi : i ≤ C.d)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    walkInner (C.chainGrad g₁ (i + 1)) (C.sparsifierCycle i e) =
      walkInner (C.chainGrad g₂ (i + 1)) (C.sparsifierCycle i e) := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  rw [C.lemma_7_12 hH hSpan hi he, C.lemma_7_12 hH hSpan hi he]
  have hWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hi he
  unfold walkInner
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [hg f (mem_E_of_mem_walkEdges hWalk hf)]

/-- Changing `g` outside `(C.G 0).E` leaves `heapCycleRatio` unchanged for every off-tree edge. -/
theorem heapCycleRatio_congr_g_G0 (C : TreeChain) {G : MGraph} {ℓ g₁ g₂ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hg : ∀ f ∈ (C.G 0).E, g₁ f = g₂ f) {e : ℕ} (he : e ∈ (C.G 0).E \ C.chainTree.E) :
    heapCycleRatio C g₁ ℓ e = heapCycleRatio C g₂ ℓ e := by
  have hlvl := C.mem_activeCore_diff_edgeLevel hH he
  unfold heapCycleRatio
  dsimp only
  rw [walkInner_chainGrad_congr_G0 C hH hSpan hg hlvl.1 hlvl.2]

end BasicKeyLemmas

section FrozenPotentials

/-- Core gradients defined from an arbitrary family of per-level vertex potentials `φ`:
`potGrad C g φ 0 e = g e` and `potGrad C g φ (i + 1) e = potGrad C g φ i e + φ i (head_i e) - φ i (tail_i e)`. -/
def potGrad (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, e => g e
  | i + 1, e => potGrad C g φ i e + φ i ((C.G i).head e) - φ i ((C.G i).tail e)

/-- Closed form of `potGrad` as `g e` plus the sum of endpoint potential differences over levels
`0, …, i - 1`. -/
lemma potGrad_eq_sum (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (i e : ℕ) :
    potGrad C g φ i e =
      g e + ∑ j ∈ Finset.range i, (φ j ((C.G j).head e) - φ j ((C.G j).tail e)) := by
  induction i with
  | zero => simp [potGrad]
  | succ m ih =>
    rw [potGrad, ih, Finset.sum_range_succ]
    ring

private lemma walkInner_potGrad_step_eq (G : MGraph) (g φ : ℕ → ℝ) :
    ∀ (W : List (ℕ × Bool)),
      walkInner (fun e => g e + φ (G.head e) - φ (G.tail e)) W =
        walkInner g W + (W.map fun x => φ (G.dst x) - φ (G.src x)).sum
  | [] => by simp [walkInner_nil]
  | x :: xs => by
    have ih := walkInner_potGrad_step_eq G g φ xs
    rw [walkInner_cons, walkInner_cons g x xs, ih]
    have hsingle : walkInner (fun e => g e + φ (G.head e) - φ (G.tail e)) [x] =
        walkInner g [x] + (φ (G.dst x) - φ (G.src x)) := by
      cases hx2 : x.2 <;>
        simp [walkInner_singleton, hx2, MGraph.dst, MGraph.src] <;> ring
    rw [hsingle]
    simp only [List.map_cons, List.sum_cons]
    ring

private lemma walkInner_stitchAux_pot (G F : MGraph) (g φ : ℕ → ℝ) (target : ℕ)
    (hPot : ∀ a b, F.Connected a b → walkInner g (F.forestPath a b) = φ a - φ b) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      TreeChain.AdjConn G F target x xs →
      walkInner g (TreeChain.stitchAux G F target x xs) =
        walkInner g (x :: xs) +
          ((x :: xs).map fun y => φ (G.dst y) - φ (G.src y)).sum +
          φ (G.src x) - φ target
  | [], x, hadj => by
    simp only [TreeChain.stitchAux, walkInner_append, hPot _ _ hadj,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  | y :: ys, x, hadj => by
    have ih := walkInner_stitchAux_pot G F g φ target hPot ys y hadj.2
    simp only [TreeChain.stitchAux, List.append_assoc, walkInner_append]
    rw [hPot _ _ hadj.1, ih, walkInner_cons g x (y :: ys)]
    simp only [List.map_cons, List.sum_cons]
    ring

private lemma walkInner_potGrad_oneStep (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {m r₀ : ℕ} (hm : m ≤ C.d) {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)}
    (hW : (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs))
    (g φ : ℕ → ℝ)
    (hPot : ∀ a b, (C.activeLSF m).F.F.Connected a b →
      walkInner g ((C.activeLSF m).F.F.forestPath a b) = φ a - φ b) :
    walkInner (fun e => g e + φ ((C.G m).head e) - φ ((C.G m).tail e)) (x₀ :: xs) =
      walkInner g (C.liftWalk m (x₀ :: xs)) := by
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
        cases ha2 : a.2 <;> simp [MGraph.dst, TreeChain.activeCore, coreGraph, ha2]
      have hsrc : (C.activeCore m).src b = (C.activeLSF m).F.root ((C.G m).src b) := by
        cases hb2 : b.2 <;> simp [MGraph.src, TreeChain.activeCore, coreGraph, hb2]
      rw [← hdst, ← hsrc]
      exact heq
    exact connected_of_root_eq hRF haV hbV hreq
  have hadj := TreeChain.adjConn_of_closedWalk (G := C.G m) (F := (C.activeLSF m).F.F) hW hconn
  have hst := walkInner_stitchAux_pot (C.G m) (C.activeLSF m).F.F g φ ((C.G m).src x₀) hPot xs x₀ hadj
  have hcg := walkInner_potGrad_step_eq (C.G m) g φ (x₀ :: xs)
  change _ = walkInner g (TreeChain.stitchAux (C.G m) (C.activeLSF m).F.F ((C.G m).src x₀) x₀ xs)
  rw [hst, hcg]
  ring

/-- Any family of per-level vertex potentials `φ` matching `walkInner (potGrad C g φ j)` along
paths in the active forest `(C.activeLSF j).F.F` (for `j ≤ i`) yields the exact same cycle gradient
sum as `C.chainGrad g (i + 1)` on every candidate cycle at level `i`. -/
theorem walkInner_potGrad_eq_chainGrad (C : TreeChain) {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (φ : ℕ → ℕ → ℝ) {i e : ℕ} (hi : i ≤ C.d)
    (hPot : ∀ j ≤ i, ∀ a b, (C.activeLSF j).F.F.Connected a b →
      walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath a b) = φ j a - φ j b)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    walkInner (potGrad C g φ (i + 1)) (C.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hiter : ∀ m ≤ i, ∀ {r₀ : ℕ} {x₀ : ℕ × Bool} {xs : List (ℕ × Bool)},
      (C.activeCore m).IsWalk r₀ r₀ (x₀ :: xs) →
      walkInner (potGrad C g φ (m + 1)) (x₀ :: xs) = walkInner g (C.iterLift m (x₀ :: xs)) := by
    intro m
    induction m with
    | zero =>
      intro hm r₀ x₀ xs hW
      exact walkInner_potGrad_oneStep C hH (le_trans hm hi) hW g (φ 0) (hPot 0 hm)
    | succ k ih =>
      intro hk r₀ x₀ xs hW
      have hk_d : k + 1 ≤ C.d := le_trans hk hi
      have h1 := walkInner_potGrad_oneStep C hH hk_d hW (potGrad C g φ (k + 1)) (φ (k + 1))
        (hPot (k + 1) hk)
      have hLift := C.liftWalk_isClosedWalk hH hSub hk_d hW
      have hWalkCore := MGraph.isWalk_of_isSubgraph (C.G_succ_isSubgraph_core hH hk_d) hLift.1
      cases hList : C.liftWalk (k + 1) (x₀ :: xs) with
      | nil => exact absurd hList hLift.2
      | cons y₀ ys =>
        rw [hList] at hWalkCore h1
        change walkInner (fun e => potGrad C g φ (k + 1) e + φ (k + 1) ((C.G (k + 1)).head e) -
          φ (k + 1) ((C.G (k + 1)).tail e)) (x₀ :: xs) = _
        rw [h1]
        simpa [TreeChain.iterLift, hList] using ih (Nat.le_of_lt hk) hWalkCore
  rw [C.lemma_7_12 hH hSpan hi he,
    ← walkInner_eq_of_walkFlow_eq g (C.iterLift_fundChainCycleAt_walkFlow_eq hH hSub hSpan hi he)]
  exact hiter i (le_refl i) hClosed

/-- A static initialization potential `φ j v = treeRootPot (C.activeLSF j).T gInit_j v` satisfies the
forest-potential hypothesis of `walkInner_potGrad_eq_chainGrad` whenever `gInit_j` agrees with
`potGrad C g φ j` on the surviving active forest edges `(C.activeLSF j).F.F.E`. -/
lemma potGrad_treeRootPot_of_agree (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    {j : ℕ} (hj : j ≤ C.d) {gCur gInit : ℕ → ℝ}
    (hAgree : ∀ f ∈ (C.activeLSF j).F.F.E, gCur f = gInit f)
    {a b : ℕ} (hab : (C.activeLSF j).F.F.Connected a b) :
    walkInner gCur ((C.activeLSF j).F.F.forestPath a b) =
      treeRootPot (C.activeLSF j).T gInit a - treeRootPot (C.activeLSF j).T gInit b := by
  have hLj := C.activeLSF_holds hH hj
  have hT := hLj.1
  have hTF := hLj.2.2.1
  have hAgreePath : walkInner gCur ((C.activeLSF j).F.F.forestPath a b) =
      walkInner gInit ((C.activeLSF j).F.F.forestPath a b) := by
    unfold walkInner
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [hAgree f (forestPath_edges_subset a b hf)]
  rw [hAgreePath]
  have habT : (C.activeLSF j).T.Connected a b := MGraph.connected_of_isSubgraph hTF hab
  have hWalkT : (C.activeLSF j).T.IsWalk a b ((C.activeLSF j).F.F.forestPath a b) :=
    MGraph.isWalk_of_isSubgraph hTF (MGraph.isWalk_forestPath hab)
  have hflow : ∀ f, walkFlow ((C.activeLSF j).F.F.forestPath a b) f =
      walkFlow ((C.activeLSF j).T.forestPath a b) f := fun f =>
    walkFlow_eq_of_isForest hT hWalkT (MGraph.isWalk_forestPath habT) f
  rw [walkInner_eq_of_walkFlow_eq gInit hflow]
  exact walkInner_forestPath_eq_sub_treeRootPot hT habT gInit

end FrozenPotentials

section PrefixAndUpdateInvariance

/-- **Prefix independence (`Shift(i₀)` / `Rebuild(i₀)`)**: if two valid tree chains agree on
`G`, `activeLSF`, `activeS`, and `activeEmb` at levels `0..i`, then they have the exact same
candidates and `heapCycleRatio` keys at level `i`. -/
theorem heapCycleRatio_congr_prefix (C C' : TreeChain) {G G' : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ σ' σ'_mwu γ'_ℓ γ'_c)
    {i : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (hG : ∀ j ≤ i, C'.G j = C.G j)
    (hL : ∀ j ≤ i, C'.activeLSF j = C.activeLSF j)
    (hS : C'.activeS i = C.activeS i)
    (hEmb : C'.activeEmb i = C.activeEmb i)
    {e : ℕ} (he : e ∈ (C.activeCore i).E \ (C.activeS i).E) :
    e ∈ (C'.activeCore i).E \ (C'.activeS i).E ∧
      heapCycleRatio C' g ℓ e = heapCycleRatio C g ℓ e := by
  have hCoreEq : C'.activeCore i = C.activeCore i := by
    unfold TreeChain.activeCore
    rw [hG i (le_refl i), hL i (le_refl i)]
  have he' : e ∈ (C'.activeCore i).E \ (C'.activeS i).E := by
    rwa [hCoreEq, hS]
  refine ⟨he', ?_⟩
  rw [heapCycleRatio_eq_at C' hH' hi' he', heapCycleRatio_eq_at C hH hi he]
  have hSp : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle
    rw [hEmb]
  have hLen : C'.chainLen ℓ (i + 1) = C.chainLen ℓ (i + 1) :=
    chainLen_congr_lt ℓ (i + 1)
      (fun j hj => hG j (Nat.lt_succ_iff.mp hj))
      (fun j hj => hL j (Nat.lt_succ_iff.mp hj))
  have hGrad : C'.chainGrad g (i + 1) = C.chainGrad g (i + 1) :=
    chainGrad_congr_lt g (i + 1)
      (fun j hj => hG j (Nat.lt_succ_iff.mp hj))
      (fun j hj => hL j (Nat.lt_succ_iff.mp hj))
  unfold TreeChain.wlenAt
  rw [hSp, hLen, hGrad]

/-- Subgraph of `C.chainTree` containing only the active forest edges of levels `0..i`. -/
def prefixTree (C : TreeChain) (i : ℕ) : MGraph where
  V := (C.G 0).V
  E := (Finset.range (i + 1)).biUnion fun j => (C.activeLSF j).F.F.E
  tail := (C.G 0).tail
  head := (C.G 0).head

private lemma prefixTree_isSubgraph_chainTree (C : TreeChain) {i : ℕ} (hi : i ≤ C.d) :
    C.chainTree.IsSubgraph (prefixTree C i) := by
  refine ⟨Finset.Subset.refl _, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  intro e he
  simp only [prefixTree, TreeChain.chainTree, TreeChain.chainTreeEdges,
    Finset.mem_biUnion, Finset.mem_range] at he ⊢
  obtain ⟨j, hj, hej⟩ := he
  exact ⟨j, by omega, hej⟩

private lemma connected_prefixTree_of_activeLSF_walk (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {lim k : ℕ} (hk : k ≤ lim) (hlim : lim ≤ C.d)
    (hIH : ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V, C.proj k u = C.proj k v → (prefixTree C lim).Connected u v) :
    ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, (C.activeLSF k).F.F.IsWalk a b Q →
      ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V,
        C.proj k u = a → C.proj k v = b → (prefixTree C lim).Connected u v := by
  intro a b Q hQ
  have hk_d : k ≤ C.d := le_trans hk hlim
  induction hQ with
  | nil z =>
    intro u hu v hv hua hvb
    exact hIH u hu v hv (hua.trans hvb.symm)
  | @cons a b x Q he hsrc _ ihQ =>
    intro u hu v hv hua hvb
    have heGk : x.1 ∈ (C.G k).E := (hSub k hk_d).2.1 he
    have heG0 : x.1 ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le k) hk_d heGk
    have heEnds0 := C.G_isValid hH 0 (Nat.zero_le C.d) x.1 heG0
    have hux : (C.G 0).src x ∈ (C.G 0).V := by
      cases hx2 : x.2 <;> simp [MGraph.src, hx2, heEnds0.1, heEnds0.2]
    have hvx : (C.G 0).dst x ∈ (C.G 0).V := by
      cases hx2 : x.2 <;> simp [MGraph.dst, hx2, heEnds0.1, heEnds0.2]
    have heTree : x.1 ∈ (prefixTree C lim).E := by
      simp only [prefixTree, Finset.mem_biUnion, Finset.mem_range]
      exact ⟨k, Nat.lt_succ_of_le hk, he⟩
    have hstep : (prefixTree C lim).Connected ((C.G 0).src x) ((C.G 0).dst x) :=
      ⟨[x], .cons heTree rfl (by simp [prefixTree, MGraph.dst]; exact .nil _)⟩
    have hEnd := (hSub k hk_d).2.2 x.1 he
    have hproj_ux : C.proj k ((C.G 0).src x) = a := by
      rw [← C.G_src_eq_proj hH hk_d heGk, ← hsrc]
      cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnd.1, hEnd.2]
    have hproj_vx : C.proj k ((C.G 0).dst x) = (C.activeLSF k).F.F.dst x := by
      rw [← C.G_dst_eq_proj hH hk_d heGk]
      cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnd.1, hEnd.2]
    have h1 := hIH u hu ((C.G 0).src x) hux (hua.trans hproj_ux.symm)
    have h2 := ihQ ((C.G 0).dst x) hvx v hv hproj_vx hvb
    exact MGraph.connected_trans h1 (MGraph.connected_trans hstep h2)

private lemma connected_prefixTree_of_proj_eq (C : TreeChain) {G : MGraph} {ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSub : C.ForestsAreSubgraphs)
    {lim : ℕ} (hlim : lim ≤ C.d) :
    ∀ k ≤ lim + 1, ∀ u ∈ (C.G 0).V, ∀ v ∈ (C.G 0).V,
      C.proj k u = C.proj k v → (prefixTree C lim).Connected u v := by
  intro k
  induction k with
  | zero =>
    intro _ u _ v _ heq
    rw [show u = v from heq]
    exact MGraph.connected_refl _ v
  | succ m ih =>
    intro hm u hu v hv heq
    have hm_le : m ≤ lim := Nat.le_of_succ_le_succ hm
    have hm_d : m ≤ C.d := le_trans hm_le hlim
    have hIH := ih (Nat.le_of_lt hm)
    have huGm : C.proj m u ∈ (C.G m).V := C.proj_mem_G_V hH m hm_d u hu
    have hvGm : C.proj m v ∈ (C.G m).V := C.proj_mem_G_V hH m hm_d v hv
    have hRF := (C.activeLSF_holds hH hm_d).2.1
    change (C.activeLSF m).F.root (C.proj m u) = (C.activeLSF m).F.root (C.proj m v) at heq
    obtain ⟨Q, hQ⟩ := connected_of_root_eq hRF huGm hvGm heq
    exact connected_prefixTree_of_activeLSF_walk C hH hSub hm_le hlim hIH hQ u hu v hv rfl rfl

private lemma walkFlow_stitchAux_congr {G₁ G₂ F₁ F₂ : MGraph} (hF₁ : F₁.IsForest)
    (hF₂ : F₂.IsForest) (target : ℕ)
    (hEnds : ∀ x : ℕ × Bool, x.1 ∈ G₁.E → x.1 ∈ G₂.E → G₁.src x = G₂.src x ∧ G₁.dst x = G₂.dst x)
    (hPath : ∀ u v, F₁.Connected u v → F₂.Connected u v →
      ∀ f, walkFlow (F₁.forestPath u v) f = walkFlow (F₂.forestPath u v) f) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      x.1 ∈ G₁.E → x.1 ∈ G₂.E → (∀ y ∈ xs, y.1 ∈ G₁.E ∧ y.1 ∈ G₂.E) →
      TreeChain.AdjConn G₁ F₁ target x xs → TreeChain.AdjConn G₂ F₂ target x xs →
      ∀ f, walkFlow (TreeChain.stitchAux G₁ F₁ target x xs) f =
        walkFlow (TreeChain.stitchAux G₂ F₂ target x xs) f
  | [], x, hx1, hx2, _, hadj1, hadj2, f => by
    have hdst : G₁.dst x = G₂.dst x := (hEnds x hx1 hx2).2
    dsimp only [TreeChain.AdjConn] at hadj1 hadj2
    simp only [TreeChain.stitchAux, walkFlow_append]
    rw [hdst] at hadj1 ⊢
    rw [hPath (G₂.dst x) target hadj1 hadj2 f]
  | y :: ys, x, hx1, hx2, hxs, hadj1, hadj2, f => by
    have hy := hxs y List.mem_cons_self
    have hys : ∀ z ∈ ys, z.1 ∈ G₁.E ∧ z.1 ∈ G₂.E := fun z hz => hxs z (List.mem_cons_of_mem y hz)
    have hdst : G₁.dst x = G₂.dst x := (hEnds x hx1 hx2).2
    have hsrc : G₁.src y = G₂.src y := (hEnds y hy.1 hy.2).1
    have ih := walkFlow_stitchAux_congr hF₁ hF₂ target hEnds hPath ys y hy.1 hy.2 hys hadj1.2 hadj2.2 f
    simp only [TreeChain.stitchAux, List.append_assoc, walkFlow_append]
    have hconn1 : F₁.Connected (G₂.dst x) (G₂.src y) := by rw [← hdst, ← hsrc]; exact hadj1.1
    rw [hdst, hsrc, hPath (G₂.dst x) (G₂.src y) hconn1 hadj2.1 f, ih]

/-- **Key invariance under non-rebuilding updates**: across an update in which levels `0..i` do not
rebuild or shift (active forests `F'_j ⊆ F_j` are decremental, stretches `wstr_j` are immutable on
surviving edges, and `g`, `ℓ`, and `G_0`-endpoints are unchanged on surviving edges), any candidate
`e` that remains in `(activeCore i).E \ (activeS i).E` with the same embedding `activeEmb i e`
keeps the exact same `heapCycleRatio`. -/
theorem heapCycleRatio_eq_of_unchanged_emb (C C' : TreeChain)
    {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hSpan' : C'.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (hEnds0 : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E →
      (C'.G 0).tail f = (C.G 0).tail f ∧ (C'.G 0).head f = (C.G 0).head f)
    (hFDec : ∀ j ≤ i, (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E)
    (hWstr : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E)
    (he' : e ∈ (C'.activeCore i).E \ (C'.activeS i).E)
    (hEmb : C'.activeEmb i e = C.activeEmb i e) :
    heapCycleRatio C' g' ℓ' e = heapCycleRatio C g ℓ e := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hSub' := C'.forestsAreSubgraphs_of_holds hH'
  rw [heapCycleRatio_eq_at C' hH' hi' he', heapCycleRatio_eq_at C hH hi he]
  have hSpEq : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle
    rw [hEmb]
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hClosed' := C'.sparsifierCycle_isClosedWalk hH' hSpan' hi' he'
  -- Step 1: Denominators `wlenAt` agree because `chainLen` agrees on every edge of `sparsifierCycle i e`.
  have hChainLenEq : ∀ k ≤ i + 1, ∀ f ∈ (C'.G (k - 1)).E, f ∈ (C.G (k - 1)).E →
      k = 0 ∨ (f ∈ (C'.G (k - 1)).E ∧ f ∈ (C.G (k - 1)).E) →
      C'.chainLen ℓ' k f = C.chainLen ℓ k f := by
    intro k
    induction k with
    | zero =>
      intro _ f hf' hf _
      exact hℓEq f hf' hf
    | succ m ih =>
      intro hm f hf' hf _
      have hm_i : m ≤ i := Nat.le_of_succ_le_succ hm
      have hm_d : m ≤ C.d := le_trans hm_i hi
      have hm_d' : m ≤ C'.d := le_trans hm_i hi'
      simp only [Nat.add_sub_cancel] at hf' hf
      have hprev : C'.chainLen ℓ' m f = C.chainLen ℓ m f := by
        cases m with
        | zero => exact hℓEq f hf' hf
        | succ m' =>
          have hf1' : f ∈ (C'.G m').E := (Finset.mem_sdiff.mp (C'.G_succ_E_subset hH' hm_d' hf')).1
          have hf1 : f ∈ (C.G m').E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hm_d hf)).1
          exact ih (Nat.le_of_lt hm) f hf1' hf1 (Or.inr ⟨hf1', hf1⟩)
      change (C'.activeLSF m).wstr f * C'.chainLen ℓ' m f =
        (C.activeLSF m).wstr f * C.chainLen ℓ m f
      rw [hWstr m hm_i f hf' hf, hprev]
  have hWlenEq : C'.wlenAt ℓ' i e = C.wlenAt ℓ i e := by
    unfold TreeChain.wlenAt
    rw [hSpEq]
    apply congrArg List.sum
    refine List.map_congr_left fun x hx => ?_
    have hf : x.1 ∈ walkEdges (C.sparsifierCycle i e) := by
      unfold walkEdges; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hfCore : x.1 ∈ (C.activeCore i).E := mem_E_of_mem_walkEdges hClosed hf
    have hfCore' : x.1 ∈ (C'.activeCore i).E := mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hf)
    have hfGi : x.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp hfCore).1
    have hfGi' : x.1 ∈ (C'.G i).E := (Finset.mem_sdiff.mp hfCore').1
    exact hChainLenEq (i + 1) (le_refl _) x.1 hfGi' hfGi (Or.inr ⟨hfGi', hfGi⟩)
  -- Step 2: Numerators agree because `fundChainCycleAt i e` has the exact same `walkFlow` in `G_0`.
  have hPrefSubC : ∀ {u v : ℕ} {P : List (ℕ × Bool)},
      (prefixTree C' i).IsWalk u v P → C.chainTree.IsWalk u v P := by
    intro u v P hP
    induction hP with
    | nil z => exact .nil z
    | @cons u v x Q hx hsrc _ ih =>
      have hx' : x.1 ∈ (prefixTree C' i).E := hx
      simp only [prefixTree, Finset.mem_biUnion, Finset.mem_range] at hx'
      obtain ⟨j, hj, hxj⟩ := hx'
      have hj_i : j ≤ i := Nat.lt_succ_iff.mp hj
      have hxjC : x.1 ∈ (C.activeLSF j).F.F.E := hFDec j hj_i hxj
      have hxTreeC : x.1 ∈ C.chainTree.E := by
        simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
        exact ⟨j, by omega, hxjC⟩
      have hxG0' : x.1 ∈ (C'.G 0).E := C'.activeLSF_E_subset_G_zero hH' hSub' (le_trans hj_i hi') hxj
      have hxG0 : x.1 ∈ (C.G 0).E := C.activeLSF_E_subset_G_zero hH hSub (le_trans hj_i hi) hxjC
      have hEnd := hEnds0 x.1 hxG0' hxG0
      have hsrcC : C.chainTree.src x = u := by
        rw [← hsrc]
        cases hx2 : x.2 <;> simp [TreeChain.chainTree, prefixTree, MGraph.src, hx2, hEnd.1, hEnd.2]
      have hdstC : C.chainTree.dst x = (prefixTree C' i).dst x := by
        cases hx2 : x.2 <;> simp [TreeChain.chainTree, prefixTree, MGraph.dst, hx2, hEnd.1, hEnd.2]
      exact .cons hxTreeC hsrcC (hdstC ▸ ih)
  have hPrefConn : ∀ a b : ℕ × Bool, a.1 ∈ (C'.activeCore i).E → b.1 ∈ (C'.activeCore i).E →
      (C'.activeCore i).dst a = (C'.activeCore i).src b →
      (prefixTree C' i).Connected ((C'.G 0).dst a) ((C'.G 0).src b) := by
    intro a b haE hbE heq
    have haGi : a.1 ∈ (C'.G i).E := (Finset.mem_sdiff.mp haE).1
    have hbGi : b.1 ∈ (C'.G i).E := (Finset.mem_sdiff.mp hbE).1
    have haG0 : a.1 ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' haGi
    have hbG0 : b.1 ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' hbGi
    have hEndsA := C'.G_isValid hH' 0 (Nat.zero_le C'.d) a.1 haG0
    have hEndsB := C'.G_isValid hH' 0 (Nat.zero_le C'.d) b.1 hbG0
    have haV0 : (C'.G 0).dst a ∈ (C'.G 0).V := by cases ha2 : a.2 <;> simp [MGraph.dst, ha2, hEndsA.1, hEndsA.2]
    have hbV0 : (C'.G 0).src b ∈ (C'.G 0).V := by cases hb2 : b.2 <;> simp [MGraph.src, hb2, hEndsB.1, hEndsB.2]
    have hproj_eq : C'.proj (i + 1) ((C'.G 0).dst a) = C'.proj (i + 1) ((C'.G 0).src b) := by
      change (C'.activeLSF i).F.root (C'.proj i ((C'.G 0).dst a)) =
        (C'.activeLSF i).F.root (C'.proj i ((C'.G 0).src b))
      rw [← C'.G_dst_eq_proj hH' hi' haGi, ← C'.G_src_eq_proj hH' hi' hbGi]
      have hdst : (C'.activeCore i).dst a = (C'.activeLSF i).F.root ((C'.G i).dst a) := by
        cases ha2 : a.2 <;> simp [MGraph.dst, TreeChain.activeCore, coreGraph, ha2]
      have hsrc : (C'.activeCore i).src b = (C'.activeLSF i).F.root ((C'.G i).src b) := by
        cases hb2 : b.2 <;> simp [MGraph.src, TreeChain.activeCore, coreGraph, hb2]
      rw [← hdst, ← hsrc]
      exact heq
    exact connected_prefixTree_of_proj_eq C' hH' hSub' hi' (i + 1) (le_refl _) _ haV0 _ hbV0 hproj_eq
  have hAdjPref : TreeChain.AdjConn (C'.G 0) (prefixTree C' i) ((C'.G 0).src (e, true)) (e, true)
      (walkRev (C'.activeEmb i e)) :=
    TreeChain.adjConn_of_closedWalk (G := C'.G 0) (F := prefixTree C' i) hClosed' hPrefConn
  have hSubPref : C'.chainTree.IsSubgraph (prefixTree C' i) :=
    prefixTree_isSubgraph_chainTree C' hi'
  have hForC' := C'.chainTree_isForest hH' hSub'
  have hForC := C.chainTree_isForest hH hSub
  have hForPref : (prefixTree C' i).IsForest := by
    refine ⟨fun f hf => hForC'.1 f (hSubPref.2.1 hf), fun P hP => ?_⟩
    rcases hP with ⟨hne, hnd, u, hu⟩
    exact hForC'.2 P ⟨hne, hnd, u, MGraph.isWalk_of_isSubgraph hSubPref hu⟩
  have hPathFlow : ∀ u v, (prefixTree C' i).Connected u v →
      (∀ f, walkFlow (C'.chainTree.forestPath u v) f = walkFlow ((prefixTree C' i).forestPath u v) f) ∧
      (∀ f, walkFlow (C.chainTree.forestPath u v) f = walkFlow ((prefixTree C' i).forestPath u v) f) := by
    intro u v hconn
    have hW := MGraph.isWalk_forestPath hconn
    have hWC' := MGraph.isWalk_of_isSubgraph hSubPref hW
    have hWC := hPrefSubC hW
    refine ⟨fun f => walkFlow_eq_of_isForest hForC' (MGraph.isWalk_forestPath ⟨_, hWC'⟩) hWC' f,
            fun f => walkFlow_eq_of_isForest hForC (MGraph.isWalk_forestPath ⟨_, hWC⟩) hWC f⟩
  -- Compare `C'.fundChainCycleAt i e` and `C.fundChainCycleAt i e` via `prefixTree C' i`
  have hAdjC' : TreeChain.AdjConn (C'.G 0) C'.chainTree ((C'.G 0).src (e, true)) (e, true)
      (walkRev (C'.activeEmb i e)) := by
    have hLiftAdj : ∀ {G0 F1 F2 : MGraph} {t : ℕ} {x : ℕ × Bool} {xs : List (ℕ × Bool)},
        (∀ u v, F1.Connected u v → F2.Connected u v) →
        TreeChain.AdjConn G0 F1 t x xs → TreeChain.AdjConn G0 F2 t x xs := by
      intro G0 F1 F2 t x xs hImp
      induction xs generalizing x with
      | nil => intro h; exact hImp _ _ h
      | cons y ys ih => intro h; exact ⟨hImp _ _ h.1, ih h.2⟩
    exact hLiftAdj (fun _ _ hc => MGraph.connected_of_isSubgraph hSubPref hc) hAdjPref
  have hAdjC : TreeChain.AdjConn (C.G 0) C.chainTree ((C'.G 0).src (e, true)) (e, true)
      (walkRev (C'.activeEmb i e)) := by
    have hLiftAdj2 : ∀ {x : ℕ × Bool} {xs : List (ℕ × Bool)},
        x.1 ∈ (C'.G 0).E → x.1 ∈ (C.G 0).E →
        (∀ y ∈ xs, y.1 ∈ (C'.G 0).E ∧ y.1 ∈ (C.G 0).E) →
        TreeChain.AdjConn (C'.G 0) (prefixTree C' i) ((C'.G 0).src (e, true)) x xs →
        TreeChain.AdjConn (C.G 0) C.chainTree ((C'.G 0).src (e, true)) x xs := by
      intro x xs
      induction xs generalizing x with
      | nil =>
        intro hx' hx _ hadj
        have hEnd := hEnds0 x.1 hx' hx
        have hdst : (C.G 0).dst x = (C'.G 0).dst x := by
          cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnd.1, hEnd.2]
        dsimp only [TreeChain.AdjConn] at hadj ⊢
        rw [hdst]
        obtain ⟨P, hP⟩ := hadj
        exact ⟨P, hPrefSubC hP⟩
      | cons y ys ih =>
        intro hx' hx hxs hadj
        have hy := hxs y List.mem_cons_self
        have hEndX := hEnds0 x.1 hx' hx
        have hEndY := hEnds0 y.1 hy.1 hy.2
        have hdst : (C.G 0).dst x = (C'.G 0).dst x := by
          cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEndX.1, hEndX.2]
        have hsrc : (C.G 0).src y = (C'.G 0).src y := by
          cases hy2 : y.2 <;> simp [MGraph.src, hy2, hEndY.1, hEndY.2]
        dsimp only [TreeChain.AdjConn] at hadj ⊢
        refine ⟨?_, ih hy.1 hy.2 (fun z hz => hxs z (List.mem_cons_of_mem y hz)) hadj.2⟩
        rw [hdst, hsrc]
        obtain ⟨P, hP⟩ := hadj.1
        exact ⟨P, hPrefSubC hP⟩
    have heG0' : e ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he').1).1
    have heG0 : e ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
    have hxsE : ∀ y ∈ walkRev (C'.activeEmb i e), y.1 ∈ (C'.G 0).E ∧ y.1 ∈ (C.G 0).E := by
      intro y hy
      have hyCore' : y.1 ∈ (C'.activeCore i).E :=
        MGraph.isWalk_edges_mem (by cases hClosed' with | cons _ _ h => exact h) y hy
      have hyCore : y.1 ∈ (C.activeCore i).E :=
        MGraph.isWalk_edges_mem (by cases hClosed with | cons _ _ h => exact h) y (by rw [← hEmb]; exact hy)
      exact ⟨C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' (Finset.mem_sdiff.mp hyCore').1,
             C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp hyCore).1⟩
    exact hLiftAdj2 heG0' heG0 hxsE hAdjPref
  have heG0' : e ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he').1).1
  have heG0 : e ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hxsE : ∀ y ∈ walkRev (C'.activeEmb i e), y.1 ∈ (C'.G 0).E ∧ y.1 ∈ (C.G 0).E := by
    intro y hy
    have hyCore' : y.1 ∈ (C'.activeCore i).E :=
      MGraph.isWalk_edges_mem (by cases hClosed' with | cons _ _ h => exact h) y hy
    have hyCore : y.1 ∈ (C.activeCore i).E :=
      MGraph.isWalk_edges_mem (by cases hClosed with | cons _ _ h => exact h) y (by rw [← hEmb]; exact hy)
    exact ⟨C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' (Finset.mem_sdiff.mp hyCore').1,
           C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp hyCore).1⟩
  have hSrcE : (C'.G 0).src (e, true) = (C.G 0).src (e, true) := (hEnds0 e heG0' heG0).1
  have hEndsPair : ∀ x : ℕ × Bool, x.1 ∈ (C'.G 0).E → x.1 ∈ (C.G 0).E →
      (C'.G 0).src x = (C.G 0).src x ∧ (C'.G 0).dst x = (C.G 0).dst x := by
    intro x hx' hx
    have hE := hEnds0 x.1 hx' hx
    cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, hE.1, hE.2]
  have hFlow1 : ∀ f, walkFlow (C'.fundChainCycleAt i e) f =
      walkFlow (TreeChain.stitchAux (C'.G 0) (prefixTree C' i) ((C'.G 0).src (e, true))
        (e, true) (walkRev (C'.activeEmb i e))) f := by
    intro f
    change walkFlow (TreeChain.stitchAux (C'.G 0) C'.chainTree ((C'.G 0).src (e, true))
      (e, true) (walkRev (C'.activeEmb i e))) f = _
    exact walkFlow_stitchAux_congr hForC' hForPref ((C'.G 0).src (e, true))
      (fun _ _ _ => ⟨rfl, rfl⟩)
      (fun u v _ hconn f => (hPathFlow u v hconn).1 f)
      (walkRev (C'.activeEmb i e)) (e, true) heG0' heG0'
      (fun y hy => ⟨(hxsE y hy).1, (hxsE y hy).1⟩) hAdjC' hAdjPref f
  have hFlow2 : ∀ f, walkFlow (TreeChain.stitchAux (C'.G 0) (prefixTree C' i) ((C'.G 0).src (e, true))
        (e, true) (walkRev (C'.activeEmb i e))) f =
      walkFlow (C.fundChainCycleAt i e) f := by
    intro f
    have hEqC : C.fundChainCycleAt i e =
        TreeChain.stitchAux (C.G 0) C.chainTree ((C'.G 0).src (e, true))
          (e, true) (walkRev (C'.activeEmb i e)) := by
      unfold TreeChain.fundChainCycleAt TreeChain.stitchCycle TreeChain.sparsifierCycle
      rw [hSrcE, hEmb]
    rw [hEqC]
    exact walkFlow_stitchAux_congr hForPref hForC ((C'.G 0).src (e, true))
      hEndsPair (fun u v hconn _ f => ((hPathFlow u v hconn).2 f).symm)
      (walkRev (C'.activeEmb i e)) (e, true) heG0' heG0 hxsE hAdjPref hAdjC f
  have hFlowEq : ∀ f, walkFlow (C'.fundChainCycleAt i e) f = walkFlow (C.fundChainCycleAt i e) f :=
    fun f => (hFlow1 f).trans (hFlow2 f)
  have hGradEq : walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) := by
    rw [C'.lemma_7_12 hH' hSpan' hi' he', C.lemma_7_12 hH hSpan hi he]
    have hFundWalk' := C'.fundChainCycleAt_isClosedWalk hH' hSub' hSpan' hi' he'
    have hFundWalk := C.fundChainCycleAt_isClosedWalk hH hSub hSpan hi he
    have hSub'0 : walkEdges (C'.fundChainCycleAt i e) ⊆ (C'.G 0).E :=
      fun f hf => mem_E_of_mem_walkEdges hFundWalk' hf
    have hSub0 : walkEdges (C.fundChainCycleAt i e) ⊆ (C.G 0).E :=
      fun f hf => mem_E_of_mem_walkEdges hFundWalk hf
    rw [walkInner_eq_sum_of_subset (Finset.subset_union_left
          (s₁ := walkEdges (C'.fundChainCycleAt i e)) (s₂ := walkEdges (C.fundChainCycleAt i e))),
        walkInner_eq_sum_of_subset (Finset.subset_union_right
          (s₁ := walkEdges (C'.fundChainCycleAt i e)) (s₂ := walkEdges (C.fundChainCycleAt i e)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hFlowEq f]
    by_cases h0 : walkFlow (C.fundChainCycleAt i e) f = 0
    · simp [h0]
    · have hfC : f ∈ walkEdges (C.fundChainCycleAt i e) := mem_walkEdges_of_walkFlow_ne_zero h0
      have hfC' : f ∈ walkEdges (C'.fundChainCycleAt i e) :=
        mem_walkEdges_of_walkFlow_ne_zero (by rw [hFlowEq f]; exact h0)
      rw [hgEq f (hSub'0 hfC') (hSub0 hfC)]
  rw [hGradEq, hWlenEq]

end PrefixAndUpdateInvariance

end MinCostFlow.Chain
