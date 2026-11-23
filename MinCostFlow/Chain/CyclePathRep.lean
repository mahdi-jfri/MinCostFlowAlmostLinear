module

public import MinCostFlow.Chain.Algorithm2Uncond
public import MinCostFlow.Chain.UpdatePreLoopHelpers
public import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith

/-!
# Spanning-Tree Path and Off-Tree Edge Representation for `FindCycle` (Theorem 5.1)

This file formalizes the spanning-tree path + explicit off-tree edge cycle representation
clause of **Theorem 5.1** (`jtree.tex` lines 17–19, page 15):

1. **`Alg2State.extTree`**: the spanning forest (and spanning tree when `extG` is connected)
   `T ⊆ st.extG` obtained by pulling `st.chain.toTreeChain.chainTree` back through
   `FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh`.
   We prove `extTree_isSubgraph`, `extTree_isForest`, `extTree_connected_of_connected`, and
   `extTree_isSpanningTreeOn`.
2. **`cycleSegments` & `findCycle_tree_path_rep`**: for any `ChainState` with `ChainInv` and
   `FreshInv`, every returned circulation `Δ = liftEdgeFn extG extToInt (algorithm1_findCycle ch).1`
   decomposes explicitly as:
   * a list `offTreeEdges : List (ℕ × Bool)` of length `≤ Nat.ceil (TP.γ_ℓ (P.M₀ ^ 2)) + 1`, all lying
     in `extG.E \ T.E`, and
   * a list `treePaths : List (ℕ × ℕ)` of length `≤ 2 * (Nat.ceil (TP.γ_ℓ (P.M₀ ^ 2)) + 1)`, all
     connected in `T`,
   such that `Δ e = (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
   (treePaths.map (fun p => walkFlow (T.forestPath p.1 p.2) e)).sum` for every `e : ℕ`.
3. **`alg2_update_optDir_cycle_rep`**: packages the exact tree + `(offTreeEdges, treePaths)`
   representation at every successful `Update` step of `algorithm2_ds`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section ExtTree

/-- The maintained spanning forest `T ⊆ st.extG` induced by `st.chain.toTreeChain.chainTree`
across the `FreshInv` edge-ID bijection (`jtree.tex` page 15). -/
def Alg2State.extTree {cfg : Alg2Config} (st : Alg2State cfg) : MGraph where
  V := st.extG.V
  E := st.extG.E.filter (fun e => st.extToInt e ∈ st.chain.toTreeChain.chainTree.E)
  tail := st.extG.tail
  head := st.extG.head

/-- Helper mapping walk edges through an edge-ID map `f`. -/
def mapWalk (f : ℕ → ℕ) (P : List (ℕ × Bool)) : List (ℕ × Bool) :=
  P.map fun x => (f x.1, x.2)

private lemma mapWalk_src {G₁ G₂ : MGraph} {f : ℕ → ℕ} (ht : ∀ x : ℕ × Bool, x.1 ∈ G₁.E → G₂.tail (f x.1) = G₁.tail x.1)
    (hh : ∀ x : ℕ × Bool, x.1 ∈ G₁.E → G₂.head (f x.1) = G₁.head x.1)
    {x : ℕ × Bool} (hx : x.1 ∈ G₁.E) :
    G₂.src (f x.1, x.2) = G₁.src x ∧ G₂.dst (f x.1, x.2) = G₁.dst x := by
  cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, ht x hx, hh x hx]

private lemma isWalk_mapWalk {G₁ G₂ : MGraph} {f : ℕ → ℕ}
    (hfE : ∀ e ∈ G₁.E, f e ∈ G₂.E)
    (ht : ∀ e ∈ G₁.E, G₂.tail (f e) = G₁.tail e)
    (hh : ∀ e ∈ G₁.E, G₂.head (f e) = G₁.head e) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G₁.IsWalk u v P → G₂.IsWalk u v (mapWalk f P)
  | u, _, [], .nil _ => .nil u
  | u, v, x :: xs, .cons hx hsrc hrest => by
    have hs := mapWalk_src (G₁ := G₁) (G₂ := G₂) (fun y hy => ht y.1 hy) (fun y hy => hh y.1 hy) hx
    refine .cons (hfE x.1 hx) (hs.1.trans hsrc) ?_
    rw [hs.2]
    exact isWalk_mapWalk hfE ht hh hrest

lemma extTree_isSubgraph {cfg : Alg2Config} (st : Alg2State cfg) :
    st.extG.IsSubgraph st.extTree :=
  ⟨Finset.Subset.refl _, Finset.filter_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩

lemma extTree_isForest {cfg : Alg2Config} (st : Alg2State cfg)
    (hExtValid : st.extG.IsValid)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hForestInt : st.chain.toTreeChain.chainTree.IsForest) :
    st.extTree.IsForest := by
  refine ⟨fun e he => hExtValid e (Finset.filter_subset _ _ he), fun P hP => ?_⟩
  rcases hP with ⟨hPne, hPnd, u, hW⟩
  have hMapW : st.chain.toTreeChain.chainTree.IsWalk u u (mapWalk st.extToInt P) := by
    refine isWalk_mapWalk (G₁ := st.extTree) (G₂ := st.chain.toTreeChain.chainTree) ?_ ?_ ?_ hW
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he
      have heG : e ∈ st.extG.E := (Finset.mem_filter.mp he).1
      change (st.chain.G 0).tail (st.extToInt e) = st.extG.tail e
      exact hFresh.hTail e heG
    · intro e he
      have heG : e ∈ st.extG.E := (Finset.mem_filter.mp he).1
      change (st.chain.G 0).head (st.extToInt e) = st.extG.head e
      exact hFresh.hHead e heG
  have hne' : mapWalk st.extToInt P ≠ [] := by
    simpa [mapWalk] using hPne
  have hEdgesExt : ∀ x ∈ P, x.1 ∈ st.extG.E := fun x hx =>
    (Finset.mem_filter.mp (MGraph.isWalk_edges_mem hW x hx)).1
  have hnd' : ((mapWalk st.extToInt P).map Prod.fst).Nodup := by
    rw [show (mapWalk st.extToInt P).map Prod.fst = (P.map Prod.fst).map st.extToInt by
      dsimp only [mapWalk]; simp [List.map_map, Function.comp_def]]
    refine List.Nodup.map_on ?_ hPnd
    intro a ha b hb heq
    rcases List.mem_map.mp ha with ⟨xa, hxa, rfl⟩
    rcases List.mem_map.mp hb with ⟨xb, hxb, rfl⟩
    have haG : xa.1 ∈ st.extG.E := hEdgesExt xa hxa
    have hbG : xb.1 ∈ st.extG.E := hEdgesExt xb hxb
    have h0 := congrArg st.intToExt heq
    rwa [hFresh.hLeft xa.1 haG, hFresh.hLeft xb.1 hbG] at h0
  exact hForestInt.2 (mapWalk st.extToInt P) ⟨hne', hnd', u, hMapW⟩

lemma extTree_connected_of_connected {cfg : Alg2Config} (st : Alg2State cfg)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : st.chain.toTreeChain.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSub : st.chain.toTreeChain.ForestsAreSubgraphs)
    (hSpan : st.chain.toTreeChain.LastLevelSpans)
    {u v : ℕ} (hu : u ∈ st.extG.V) (hv : v ∈ st.extG.V)
    (hconn : st.extG.Connected u v) :
    st.extTree.Connected u v := by
  have hG0eq : st.chain.toTreeChain.G 0 = G := hH.1
  have hC0 : st.chain.toTreeChain.G 0 = st.chain.G 0 := rfl
  have hGeq : G = st.chain.G 0 := hG0eq.symm.trans hC0
  have huG : u ∈ G.V := by rw [hGeq, ← hFresh.hV]; exact hu
  have hvG : v ∈ G.V := by rw [hGeq, ← hFresh.hV]; exact hv
  have hconn0 : G.Connected u v := by
    obtain ⟨Q, hQ⟩ := hconn
    refine ⟨mapWalk st.extToInt Q, ?_⟩
    rw [hGeq]
    exact isWalk_mapWalk
      (fun e he => by rw [hFresh.hE]; exact Finset.mem_image_of_mem _ he)
      hFresh.hTail hFresh.hHead hQ
  have hTreeConn := st.chain.toTreeChain.chainTree_connected_of_connected hH hSub hSpan huG hvG hconn0
  obtain ⟨Qtree, hQtree⟩ := hTreeConn
  have hSubTree : (st.chain.G 0).IsSubgraph st.chain.toTreeChain.chainTree :=
    st.chain.toTreeChain.chainTree_isSubgraph hH hSub
  refine ⟨mapWalk st.intToExt Qtree, ?_⟩
  refine isWalk_mapWalk (G₁ := st.chain.toTreeChain.chainTree) (G₂ := st.extTree) ?_ ?_ ?_ hQtree
  · intro e' he'
    have he0 : e' ∈ (st.chain.G 0).E := hSubTree.2.1 he'
    obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
    refine Finset.mem_filter.mpr ⟨heExt, ?_⟩
    rw [heq]; exact he'
  · intro e' he'
    have he0 : e' ∈ (st.chain.G 0).E := hSubTree.2.1 he'
    obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
    have hT0 := hFresh.hTail (st.intToExt e') heExt
    have hEnd := hSubTree.2.2 e' he'
    rw [heq] at hT0
    change st.extG.tail (st.intToExt e') = st.chain.toTreeChain.chainTree.tail e'
    rw [hEnd.1]
    exact hT0.symm
  · intro e' he'
    have he0 : e' ∈ (st.chain.G 0).E := hSubTree.2.1 he'
    obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
    have hH0 := hFresh.hHead (st.intToExt e') heExt
    have hEnd := hSubTree.2.2 e' he'
    rw [heq] at hH0
    change st.extG.head (st.intToExt e') = st.chain.toTreeChain.chainTree.head e'
    rw [hEnd.2]
    exact hH0.symm

lemma extTree_isSpanningTreeOn {cfg : Alg2Config} (st : Alg2State cfg)
    (hExtValid : st.extG.IsValid)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : st.chain.toTreeChain.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSub : st.chain.toTreeChain.ForestsAreSubgraphs)
    (hSpan : st.chain.toTreeChain.LastLevelSpans)
    (hConn : ∀ u ∈ st.extG.V, ∀ v ∈ st.extG.V, st.extG.Connected u v) :
    st.extTree.IsSpanningTreeOn st.extG.V := by
  refine ⟨extTree_isForest st hExtValid hFresh (st.chain.toTreeChain.chainTree_isForest hH hSub), rfl, ?_⟩
  intro u hu v hv
  exact extTree_connected_of_connected st hFresh hH hSub hSpan hu hv (hConn u hu v hv)

end ExtTree

section CycleSegments

/-- Decompose a `stitchAux` list into its explicit steps `xs` and tree-path endpoint pairs. -/
def cycleSegmentsAux (G : MGraph) (target : ℕ) :
    ℕ × Bool → List (ℕ × Bool) → List (ℕ × Bool) × List (ℕ × ℕ)
  | x, [] => ([x], [(G.dst x, target)])
  | x, y :: xs =>
    let (es, ps) := cycleSegmentsAux G target y xs
    (x :: es, (G.dst x, G.src y) :: ps)

/-- Decompose a `stitchCycle G F W` walk into its explicit edges `W` and `F`-path endpoints. -/
def cycleSegments (G : MGraph) : List (ℕ × Bool) → List (ℕ × Bool) × List (ℕ × ℕ)
  | [] => ([], [])
  | x :: xs => cycleSegmentsAux G (G.src x) x xs

private lemma cycleSegmentsAux_lengths (G : MGraph) (target : ℕ) (x : ℕ × Bool)
    (xs : List (ℕ × Bool)) :
    (cycleSegmentsAux G target x xs).1 = x :: xs ∧
    (cycleSegmentsAux G target x xs).2.length = (x :: xs).length := by
  induction xs generalizing x with
  | nil => simp [cycleSegmentsAux]
  | cons y ys ih =>
    have h := ih y
    dsimp only [cycleSegmentsAux]
    simp only [h.1, List.length_cons, h.2, and_self]

lemma cycleSegments_eq (G : MGraph) (W : List (ℕ × Bool)) :
    (cycleSegments G W).1 = W ∧ (cycleSegments G W).2.length = W.length := by
  cases W with
  | nil => simp [cycleSegments]
  | cons x xs => exact cycleSegmentsAux_lengths G (G.src x) x xs

private lemma cycleSegmentsAux_conn (G F : MGraph) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      TreeChain.AdjConn G F target x xs →
      ∀ p ∈ (cycleSegmentsAux G target x xs).2, F.Connected p.1 p.2
  | [], x, hadj, p, hp => by
    simp only [cycleSegmentsAux, List.mem_singleton] at hp
    subst hp
    exact hadj
  | y :: ys, x, hadj, p, hp => by
    simp only [cycleSegmentsAux, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact hadj.1
    · exact cycleSegmentsAux_conn G F target ys y hadj.2 p hp'

private lemma walkFlow_stitchAux_segments (G F : MGraph) (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool) (e : ℕ),
      walkFlow (TreeChain.stitchAux G F target x xs) e =
        ((x :: xs).map (fun y => walkFlow [y] e)).sum +
        ((cycleSegmentsAux G target x xs).2.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum
  | [], x, e => by
    simp only [TreeChain.stitchAux, cycleSegmentsAux, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, walkFlow_append]
  | y :: ys, x, e => by
    have ih := walkFlow_stitchAux_segments G F target ys y e
    dsimp only [TreeChain.stitchAux, cycleSegmentsAux]
    rw [List.append_assoc, walkFlow_append, walkFlow_append, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma walkFlow_stitchCycle_segments (G F : MGraph) (W : List (ℕ × Bool)) (e : ℕ) :
    walkFlow (TreeChain.stitchCycle G F W) e =
      ((cycleSegments G W).1.map (fun y => walkFlow [y] e)).sum +
      ((cycleSegments G W).2.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum := by
  cases W with
  | nil => simp [TreeChain.stitchCycle, cycleSegments, walkFlow_nil]
  | cons x xs =>
    dsimp only [cycleSegments]
    rw [(cycleSegmentsAux_lengths G (G.src x) x xs).1]
    exact walkFlow_stitchAux_segments G F (G.src x) xs x e

private lemma walkFlow_mapWalk_intToExt {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hFresh : FreshInv extG intG e2i i2e nf) :
    ∀ (P : List (ℕ × Bool)),
      (∀ x ∈ P, x.1 ∈ intG.E) →
      ∀ e : ℕ, walkFlow (mapWalk i2e P) e = liftEdgeFn extG e2i (walkFlow P) e
  | [], _, e => by simp [mapWalk, walkFlow_nil, liftEdgeFn]
  | x :: xs, hE, e => by
    have hxE : x.1 ∈ intG.E := hE x (by simp)
    have hxsE : ∀ y ∈ xs, y.1 ∈ intG.E := fun y hy => hE y (by simp [hy])
    have ih := walkFlow_mapWalk_intToExt hFresh xs hxsE e
    dsimp only [mapWalk] at ih ⊢
    rw [List.map_cons, walkFlow_cons, ih]
    obtain ⟨hRight, heExt⟩ := hFresh.hRight x.1 hxE
    by_cases he : e ∈ extG.E
    · simp only [liftEdgeFn, he, ↓reduceIte] at ⊢
      have hiff : i2e x.1 = e ↔ x.1 = e2i e := by
        constructor
        · intro h; rw [← h, hRight]
        · intro h; rw [h, hFresh.hLeft e he]
      by_cases h1 : i2e x.1 = e
      · have h2 : x.1 = e2i e := hiff.mp h1
        rw [walkFlow_cons]
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
      · have h2 : x.1 ≠ e2i e := fun h => h1 (hiff.mpr h)
        rw [walkFlow_cons]
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
    · simp only [liftEdgeFn, he, ↓reduceIte, add_zero]
      have hne : i2e x.1 ≠ e := fun h => he (h ▸ heExt)
      simp [hne]

private lemma walkFlow_forestPath_extTree_eq {cfg : Alg2Config} (st : Alg2State cfg)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hTreeSub : (st.chain.G 0).IsSubgraph st.chain.toTreeChain.chainTree)
    (hTreeForest : st.chain.toTreeChain.chainTree.IsForest)
    (hExtValid : st.extG.IsValid)
    {u v : ℕ} (hconn : st.chain.toTreeChain.chainTree.Connected u v) (e : ℕ) :
    st.extTree.Connected u v ∧
    walkFlow (st.extTree.forestPath u v) e =
      liftEdgeFn st.extG st.extToInt (walkFlow (st.chain.toTreeChain.chainTree.forestPath u v)) e := by
  have hP := MGraph.isWalk_forestPath hconn
  have hMapW : st.extTree.IsWalk u v (mapWalk st.intToExt (st.chain.toTreeChain.chainTree.forestPath u v)) := by
    refine isWalk_mapWalk (G₁ := st.chain.toTreeChain.chainTree) (G₂ := st.extTree) ?_ ?_ ?_ hP
    · intro e' he'
      have he0 : e' ∈ (st.chain.G 0).E := hTreeSub.2.1 he'
      obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
      refine Finset.mem_filter.mpr ⟨heExt, ?_⟩
      rwa [heq]
    · intro e' he'
      have he0 : e' ∈ (st.chain.G 0).E := hTreeSub.2.1 he'
      obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
      have hT0 := hFresh.hTail (st.intToExt e') heExt
      have hEnd := hTreeSub.2.2 e' he'
      rw [heq] at hT0
      change st.extG.tail (st.intToExt e') = st.chain.toTreeChain.chainTree.tail e'
      rw [hEnd.1]
      exact hT0.symm
    · intro e' he'
      have he0 : e' ∈ (st.chain.G 0).E := hTreeSub.2.1 he'
      obtain ⟨heq, heExt⟩ := hFresh.hRight e' he0
      have hH0 := hFresh.hHead (st.intToExt e') heExt
      have hEnd := hTreeSub.2.2 e' he'
      rw [heq] at hH0
      change st.extG.head (st.intToExt e') = st.chain.toTreeChain.chainTree.head e'
      rw [hEnd.2]
      exact hH0.symm
  have hExtConn : st.extTree.Connected u v := ⟨_, hMapW⟩
  refine ⟨hExtConn, ?_⟩
  have hExtFor : st.extTree.IsForest := extTree_isForest st hExtValid hFresh hTreeForest
  rw [walkFlow_eq_of_isForest hExtFor (MGraph.isWalk_forestPath hExtConn) hMapW e]
  refine walkFlow_mapWalk_intToExt hFresh _ (fun x hx => ?_) e
  exact hTreeSub.2.1 (MGraph.isWalk_edges_mem hP x hx)

private def flipEdge : ℕ × Bool → ℕ × Bool := fun x => (x.1, !x.2)

private lemma walkFlow_flipEdge_list (xs : List (ℕ × Bool)) (e : ℕ) :
    ((xs.map (fun x => (x.1, !x.2))).map (fun x => walkFlow [x] e)).sum =
      -(xs.map (fun x => walkFlow [x] e)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have h1 : walkFlow [(x.1, !x.2)] e = -walkFlow [x] e := by
      cases hx : x.2 <;> simp [walkFlow, hx] <;> split_ifs <;> ring
    linarith

private lemma walkFlow_neg_forestPath_list (F : MGraph) (hF : F.IsForest)
    (ps : List (ℕ × ℕ)) (hconn : ∀ p ∈ ps, F.Connected p.1 p.2) (e : ℕ) :
    ((ps.map Prod.swap).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
      -(ps.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := walkFlow_forestPath_walkRev hF (hconn p (by simp)) e
    have h2 := ih (fun q hq => hconn q (by simp [hq]))
    simp only [Prod.swap]
    linarith

private lemma split_filter_sum {α : Type _} (L : List α) (p : α → Bool) (f : α → ℝ) :
    (L.map f).sum =
      ((L.filter (fun x => !(p x))).map f).sum + ((L.filter p).map f).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    cases hx : p x <;> simp [hx, ih] <;> ring

/-- **Algorithm 1 `FindCycle` tree-path + off-tree-edge decomposition (`jtree.tex` lines 17–19)**:
under `ChainInv` + `FreshInv`, `Δ = liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1`
decomposes into `offTreeEdges` (`length ≤ ⌈γ_ℓ(M₀²)⌉ + 1`) outside `st.extTree.E` and
`treePaths` (`length ≤ 2 * (⌈γ_ℓ(M₀²)⌉ + 1)`) of `st.extTree`-connected endpoint pairs. -/
theorem findCycle_tree_path_rep {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    (st : Alg2State cfg)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh) :
    let Δ := liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1
    ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
      offTreeEdges.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 ∧
      (∀ x ∈ offTreeEdges, x.1 ∈ st.extG.E \ st.extTree.E) ∧
      treePaths.length ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1) ∧
      (∀ p ∈ treePaths, st.extTree.Connected p.1 p.2) ∧
      ∀ e : ℕ, Δ e =
        (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
        (treePaths.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e)).sum := by
  classical
  have hExtValid : st.extG.IsValid := hFresh.isValid_iff.mp hInv.hG0Valid
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hT hV.hMWU hV.hEmb hV.hγM₀ hV.hγk
  set C := st.chain.toTreeChain
  have hH := hTH.1
  have hSpan := hTH.2.1
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hTreeSub : (st.chain.G 0).IsSubgraph C.chainTree := C.chainTree_isSubgraph hH hSub
  have hTreeFor : C.chainTree.IsForest := C.chainTree_isForest hH hSub
  have hExtFor : st.extTree.IsForest := extTree_isForest st hExtValid hFresh hTreeFor
  dsimp only [algorithm1_findCycle]
  set S := (st.chain.G 0).E \ C.chainTree.E
  by_cases hne : S.Nonempty
  · rw [dite_eq_left_of_eq_true (eq_true hne)]
    set eBest := leastArgmax S (heapCycleRatio C st.chain.g st.chain.ℓ) hne
    have heBestSpec := leastArgmax_spec S (heapCycleRatio C st.chain.g st.chain.ℓ) hne
    have heBest : eBest ∈ S := heBestSpec.1
    have hlvl := C.mem_activeCore_diff_edgeLevel hH heBest
    set i := C.edgeLevel eBest
    have hi : i ≤ C.d := hlvl.1
    set W := C.sparsifierCycle i eBest
    set rawWalk := C.fundChainCycle eBest
    have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi hlvl.2
    have hWlen : W.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 := by
      have hspLen : W.length = 1 + (C.activeEmb i eBest).length := by
        simp [W, TreeChain.sparsifierCycle, walkRev, Nat.add_comm]
      have hEmbLen : ((C.activeEmb i eBest).length : ℝ) ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
        by_cases hlt : i < C.d
        · have hSp := C.activeS_isSparsified hH hlt
          have heCore := (Finset.mem_sdiff.mp hlvl.2).1
          have hle : (C.activeEmb i eBest).length ≤ (C.activeEmb i).length (C.activeCore i) :=
            Finset.le_sup (f := fun e => (C.activeEmb i e).length) heCore
          exact le_trans (Nat.cast_le.mpr hle) hSp.2.2.2.1
        · have hieq : i = C.d := Nat.le_antisymm hi (Nat.le_of_not_lt hlt)
          have hnil : C.activeEmb i eBest = [] := by simp [i, hieq, TreeChain.activeEmb]
          rw [hnil, List.length_nil, Nat.cast_zero]
          exact le_trans zero_le_one (hV.hTP.2.2.1 (cfg.P.M₀ ^ 2))
      have hceil : (C.activeEmb i eBest).length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) := by
        exact_mod_cast le_trans hEmbLen (Nat.le_ceil _)
      omega
    have hWE : ∀ y ∈ W, y.1 ∈ (st.chain.G 0).E := fun y hy => by
      have hyCore : y.1 ∈ (C.activeCore i).E := MGraph.isWalk_edges_mem hClosed y hy
      exact C.G_E_subset_of_le hH (Nat.zero_le i) hi (Finset.mem_sdiff.mp hyCore).1
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
          cases ha2 : a.2 <;> simp [MGraph.dst, TreeChain.activeCore, coreGraph, ha2]
        have hsrc : (C.activeCore i).src b = (C.activeLSF i).F.root ((C.G i).src b) := by
          cases hb2 : b.2 <;> simp [MGraph.src, TreeChain.activeCore, coreGraph, hb2]
        rw [← hdst, ← hsrc]
        exact heq
      exact C.connected_chainTree_of_proj_eq hH hSub (i + 1) (Nat.succ_le_succ hi) _ haV0 _ hbV0 hproj_eq
    have hPsConn : ∀ p ∈ (cycleSegments (C.G 0) W).2, C.chainTree.Connected p.1 p.2 := by
      cases hW : W with
      | nil => simp [W, TreeChain.sparsifierCycle] at hW
      | cons x₀ xs =>
        have hC' : (C.activeCore i).IsWalk ((C.activeCore i).tail eBest) ((C.activeCore i).tail eBest) (x₀ :: xs) :=
          hW ▸ hClosed
        have hadj := TreeChain.adjConn_of_closedWalk (G := C.G 0) (F := C.chainTree) hC' hconn
        exact cycleSegmentsAux_conn (C.G 0) C.chainTree ((C.G 0).src x₀) xs x₀ hadj
    let segs := cycleSegments (C.G 0) W
    have hSeg1 : segs.1 = W := (cycleSegments_eq (C.G 0) W).1
    have hSeg2_len : segs.2.length = W.length := (cycleSegments_eq (C.G 0) W).2
    let W_orient : List (ℕ × Bool) :=
      if walkInner st.chain.g rawWalk ≤ 0 then segs.1 else segs.1.map (fun x => (x.1, !x.2))
    let ps_orient : List (ℕ × ℕ) :=
      if walkInner st.chain.g rawWalk ≤ 0 then segs.2 else segs.2.map Prod.swap
    have hW_orient_E : ∀ x ∈ W_orient, x.1 ∈ (st.chain.G 0).E := by
      intro x hx
      dsimp only [W_orient] at hx
      split_ifs at hx
      · exact hWE x (hSeg1 ▸ hx)
      · rw [List.mem_map] at hx
        rcases hx with ⟨y, hy, rfl⟩
        exact hWE y (hSeg1 ▸ hy)
    have hps_conn : ∀ p ∈ ps_orient, C.chainTree.Connected p.1 p.2 := by
      intro p hp
      dsimp only [ps_orient] at hp
      split_ifs at hp
      · exact hPsConn p hp
      · rw [List.mem_map] at hp
        rcases hp with ⟨q, hq, rfl⟩
        exact MGraph.connected_symm (hPsConn q hq)
    let W_ext : List (ℕ × Bool) := mapWalk st.intToExt W_orient
    let offTreeEdges := W_ext.filter (fun x => !(decide (x.1 ∈ st.extTree.E)))
    let treeEdgePaths := (W_ext.filter (fun x => decide (x.1 ∈ st.extTree.E))).map
      (fun x => (st.extG.src x, st.extG.dst x))
    let treePaths := treeEdgePaths ++ ps_orient
    refine ⟨offTreeEdges, treePaths, ?_, ?_, ?_, ?_, ?_⟩
    · have hlen1 : offTreeEdges.length ≤ W_ext.length := List.length_filter_le _ _
      have hlen2 : W_ext.length = W_orient.length := List.length_map _
      have hlen3 : W_orient.length = W.length := by
        dsimp only [W_orient]
        split_ifs <;> simp [hSeg1]
      omega
    · intro x hx
      rw [List.mem_filter] at hx
      have hxW : x ∈ W_ext := hx.1
      have hnot : x.1 ∉ st.extTree.E := by simpa using hx.2
      dsimp only [W_ext, mapWalk] at hxW
      rw [List.mem_map] at hxW
      rcases hxW with ⟨y, hy, rfl⟩
      exact Finset.mem_sdiff.mpr ⟨(hFresh.hRight y.1 (hW_orient_E y hy)).2, hnot⟩
    · have hlen1 : treeEdgePaths.length ≤ W_ext.length := by
        rw [List.length_map]; exact List.length_filter_le _ _
      have hlen2 : W_ext.length = W.length := by
        dsimp only [W_ext, mapWalk, W_orient]
        split_ifs <;> simp [hSeg1]
      have hlen3 : ps_orient.length = W.length := by
        dsimp only [ps_orient]
        split_ifs <;> simp [hSeg2_len]
      rw [List.length_append]
      omega
    · intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · rw [List.mem_map] at hp
        rcases hp with ⟨x, hx, rfl⟩
        rw [List.mem_filter] at hx
        have hxTree : x.1 ∈ st.extTree.E := by simpa using hx.2
        refine ⟨[x], .cons hxTree rfl ?_⟩
        simp [Alg2State.extTree]
        exact .nil _
      · exact (walkFlow_forestPath_extTree_eq st hFresh hTreeSub hTreeFor hExtValid
          (hps_conn p hp) 0).1
    · intro e
      have hFlowInt : ∀ e' : ℕ, (if walkInner st.chain.g rawWalk ≤ 0 then walkFlow rawWalk
            else walkFlow (walkRev rawWalk)) e' =
          ((W_orient.map (fun y => walkFlow [y] e')).sum +
            (ps_orient.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) e')).sum) := by
        intro e'
        have hRaw : walkFlow rawWalk e' =
            ((segs.1.map (fun y => walkFlow [y] e')).sum +
              (segs.2.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) e')).sum) := by
          simpa [rawWalk, TreeChain.fundChainCycle, TreeChain.fundChainCycleAt] using
            walkFlow_stitchCycle_segments (C.G 0) C.chainTree W e'
        by_cases hneg : walkInner st.chain.g rawWalk ≤ 0
        · simp only [hneg, ↓reduceIte, W_orient, ps_orient]
          exact hRaw
        · simp only [hneg, ↓reduceIte, W_orient, ps_orient]
          rw [walkFlow_walkRev, hRaw, walkFlow_flipEdge_list,
            walkFlow_neg_forestPath_list C.chainTree hTreeFor segs.2 hPsConn]
          ring
      have hOr_eq : (if walkInner st.chain.g rawWalk ≤ 0 then walkFlow rawWalk
            else walkFlow (walkRev rawWalk)) =
          walkFlow (if walkInner st.chain.g rawWalk ≤ 0 then rawWalk else walkRev rawWalk) := by
        split_ifs <;> rfl
      rw [← hOr_eq]
      dsimp only [liftEdgeFn]
      by_cases he : e ∈ st.extG.E
      · simp only [he, ↓reduceIte]
        rw [hFlowInt (st.extToInt e)]
        have hWsum :
            liftEdgeFn st.extG st.extToInt (fun e' => (W_orient.map (fun y => walkFlow [y] e')).sum) e =
              (W_ext.map (fun x => walkFlow [x] e)).sum := by
          have hl : ∀ L : List (ℕ × Bool), (∀ y ∈ L, y.1 ∈ (st.chain.G 0).E) →
              (mapWalk st.intToExt L |>.map (fun x => walkFlow [x] e)).sum =
              liftEdgeFn st.extG st.extToInt (fun e' => (L.map (fun y => walkFlow [y] e')).sum) e := by
            intro L hL
            induction L with
            | nil => simp [mapWalk, liftEdgeFn]
            | cons y ys ihL =>
              have hy0 := hL y (by simp)
              have ih' := ihL fun z hz => hL z (by simp [hz])
              have h1 := walkFlow_mapWalk_intToExt hFresh [y] (fun z hz => by simp at hz; subst hz; exact hy0) e
              dsimp only [mapWalk] at h1 ih' ⊢
              simp only [List.map_cons, List.map_nil, List.sum_cons, liftEdgeFn, he, ↓reduceIte] at h1 ih' ⊢
              rw [h1, ih']
          exact (hl W_orient hW_orient_E).symm
        have hPsum :
            liftEdgeFn st.extG st.extToInt
                (fun e' => (ps_orient.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) e')).sum) e =
              (ps_orient.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e)).sum := by
          have hPgen : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, C.chainTree.Connected p.1 p.2) →
              liftEdgeFn st.extG st.extToInt
                (fun e' => (L.map (fun p => walkFlow (C.chainTree.forestPath p.1 p.2) e')).sum) e =
              (L.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e)).sum := by
            intro L hL
            induction L with
            | nil => simp [liftEdgeFn]
            | cons p ps ihP =>
              have hp0 := hL p (by simp)
              have ih' := ihP fun q hq => hL q (by simp [hq])
              have hfp := (walkFlow_forestPath_extTree_eq st hFresh hTreeSub hTreeFor hExtValid hp0 e).2
              simp only [List.map_cons, List.sum_cons, liftEdgeFn, he, ↓reduceIte] at hfp ih' ⊢
              rw [hfp, ih']
          exact hPgen ps_orient hps_conn
        have hSplit := split_filter_sum W_ext (fun x => decide (x.1 ∈ st.extTree.E))
          (fun x => walkFlow [x] e)
        have hTreeSwap :
            ((W_ext.filter (fun x => decide (x.1 ∈ st.extTree.E))).map (fun x => walkFlow [x] e)).sum =
              (treeEdgePaths.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e)).sum := by
          dsimp only [treeEdgePaths]
          rw [List.map_map]
          congr 1
          refine List.map_congr_left fun x hx => ?_
          have hxTree : x.1 ∈ st.extTree.E := by simpa using (List.mem_filter.mp hx).2
          have hW1 : st.extTree.IsWalk (st.extG.src x) (st.extG.dst x) [x] :=
            .cons hxTree rfl (by simp [Alg2State.extTree]; exact .nil _)
          have hC1 : st.extTree.Connected (st.extG.src x) (st.extG.dst x) := ⟨[x], hW1⟩
          exact walkFlow_eq_of_isForest hExtFor hW1 (MGraph.isWalk_forestPath hC1) e
        dsimp only [liftEdgeFn] at hWsum hPsum
        simp only [he, ↓reduceIte] at hWsum hPsum
        have hTreeMap : treePaths.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e) =
            treeEdgePaths.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e) ++
            ps_orient.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e) :=
          List.map_append
        rw [hWsum, hSplit, hTreeSwap, hPsum, hTreeMap, List.sum_append]
        dsimp only [offTreeEdges]
        ring
      · simp only [he, ↓reduceIte]
        have hOff0 : ∀ x ∈ offTreeEdges, walkFlow [x] e = 0 := fun x hx => by
          rw [List.mem_filter] at hx
          have hxW := hx.1
          dsimp only [W_ext, mapWalk] at hxW
          rw [List.mem_map] at hxW
          rcases hxW with ⟨y, hy, rfl⟩
          have hxE : st.intToExt y.1 ∈ st.extG.E := (hFresh.hRight y.1 (hW_orient_E y hy)).2
          have hne : st.intToExt y.1 ≠ e := fun h => he (h ▸ hxE)
          simp [walkFlow_cons, walkFlow_nil, hne]
        have hTree0 : ∀ p ∈ treePaths, walkFlow (st.extTree.forestPath p.1 p.2) e = 0 := fun p hp => by
          by_contra hnz
          have hmem := mem_walkEdges_of_walkFlow_ne_zero hnz
          have hpConn : st.extTree.Connected p.1 p.2 := by
            rw [List.mem_append] at hp
            rcases hp with hp | hp
            · rw [List.mem_map] at hp
              rcases hp with ⟨x, hx, rfl⟩
              have hxT : x.1 ∈ st.extTree.E := by simpa using (List.mem_filter.mp hx).2
              exact ⟨[x], .cons hxT rfl (by simp [Alg2State.extTree]; exact .nil _)⟩
            · exact (walkFlow_forestPath_extTree_eq st hFresh hTreeSub hTreeFor hExtValid
                (hps_conn p hp) e).1
          have heTree : e ∈ st.extTree.E :=
            mem_E_of_mem_walkEdges (MGraph.isWalk_forestPath hpConn) hmem
          exact he ((extTree_isSubgraph st).2.1 heTree)
        have hS1 : (offTreeEdges.map (fun x => walkFlow [x] e)).sum = 0 :=
          List.sum_eq_zero fun v hv => by
            rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩; exact hOff0 x hx
        have hS2 : (treePaths.map (fun p => walkFlow (st.extTree.forestPath p.1 p.2) e)).sum = 0 :=
          List.sum_eq_zero fun v hv => by
            rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩; exact hTree0 p hp
        rw [hS1, hS2, add_zero]
  · rw [dite_eq_right_of_eq_false (eq_false hne)]
    refine ⟨[], [], Nat.zero_le _, by simp, Nat.zero_le _, by simp, fun e => ?_⟩
    simp [liftEdgeFn]

end CycleSegments

section Algorithm2CycleRep

private lemma alg2_loopWith_some_eq {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ) (overflow : ℝ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow →
      (∀ i : Fin (cfg.P.d + 1),
        (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val) →
      branD < cfg.P.k →
      FreshInv extG (ch.G 0) e2i i2e nf →
      ∀ Δ,
        (algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).2.2.2.2 = some Δ →
        let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
        Δ = liftEdgeFn extG e2i (algorithm1_findCycle res.1).1 ∧
        ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ res.1 ∧
        FreshInv extG (res.1.G 0) e2i i2e nf := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps overflow hB hInv hBud hSh hBD hFresh Δ hSome
    have hLoop := algorithm2_loopWith_preserves hV κ extG e2i i2e nf g' ℓ' ch branD passes lctOps overflow
      hInv hBud hSh hBD hFresh
    rw [algorithm2_loopWith.eq_1] at hSome ⊢
    dsimp only at hSome ⊢
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤
        -(κ * cfg.α)
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      exact ⟨(Option.some.inj hSome).symm, hInv, hFresh⟩
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none =>
        rw [hElig] at hSome
        dsimp only at hSome
        simp at hSome
      | some i =>
        rw [hElig] at hSome
        dsimp only at hSome ⊢
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          omega
        · rw [dite_eq_right_of_eq_false (eq_false hCap)] at hSome
          simp at hSome
  | succ B ihB =>
    intro ch branD passes lctOps overflow hB hInv hBud hSh hBD hFresh Δ hSome
    rw [algorithm2_loopWith.eq_1] at hSome ⊢
    dsimp only at hSome ⊢
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤
        -(κ * cfg.α)
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      exact ⟨(Option.some.inj hSome).symm, hInv, hFresh⟩
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none =>
        rw [hElig] at hSome
        dsimp only at hSome
        simp at hSome
      | some i =>
        rw [hElig] at hSome
        dsimp only at hSome ⊢
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)] at hSome ⊢
          have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          have hShP := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
            hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hBud i.val (Nat.le_of_lt_succ i.isLt)
          dsimp only at hShP
          rcases hShP with ⟨hInv', hBud', hG0', _, _, hShCount', _, _, _⟩
          have hShBound' : ∀ j : Fin (cfg.P.d + 1),
              ((algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.shiftCount j.val : ℝ) ≤
                gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                  (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.rebuildCount j.val := by
            intro j
            have hShReb : (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.rebuildCount = ch.rebuildCount := by
              dsimp only [algorithm1_shift]; split_ifs <;> rfl
            rw [hShReb, congrFun hShCount' j.val]
            by_cases hji : j.val = i.val
            · simp [hji, hCap]
            · simp [hji]; exact hSh j
          let curB := if i.val < cfg.P.d then ch.bran i.val else branD
          let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
          let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
            if i < j then 0
            else if j = i then (if (curB + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j
          let lctOps' := lctOps + 2 * ((walkEdges (algorithm1_findCycle ch).2.1 \ ch.toTreeChain.chainTree.E).card + 1)
          have hBranD' : branD' < cfg.P.k := by
            dsimp only [branD']
            split_ifs
            · exact cfg.P.hk
            · exact Nat.mod_lt _ cfg.P.hk
          have hFresh' : FreshInv extG ((algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.G 0) e2i i2e nf :=
            hG0'.symm ▸ hFresh
          exact ihB (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 branD' passes' lctOps' overflow (by omega)
            hInv' hBud' hShBound' hBranD' hFresh' Δ hSome
        · rw [dite_eq_right_of_eq_false (eq_false hCap)] at hSome
          simp at hSome

private lemma algorithm2_updateWith_spec_fields (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
    let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let lp := algorithm2_loopWith cfg κ tb.1 tb.2.1 g' ℓ' ch1 bp1.1 bp1.2 (st.lctUpdateOps + U_ext.length)
    let res := algorithm2_updateWith cfg κ st U_ext g' ℓ' η
    res.2 = lp.2.2.2.2 ∧
    res.1.chain = lp.1 ∧
    res.1.extG = tb.1 ∧
    res.1.extToInt = tb.2.1 ∧
    res.1.intToExt = tb.2.2.1 ∧
    res.1.nextFresh = tb.2.2.2.1 := by
  dsimp only [algorithm2_updateWith]
  split <;> exact ⟨by symm; assumption, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 5.1 cycle-representation theorem for `algorithm2_dsWith cfg κ`**: at every successful
`Update` step `t + 1 ≤ T` (`minRatioFailOptDir = some Δ`), the state `stNext` after step `t + 1`
maintains a spanning forest `T_tree := stNext.extTree ⊆ D.G (t + 1)` (preserving connectivity of
`D.G (t + 1)`, hence a spanning tree whenever `D.G (t + 1)` is connected) together with
`offTreeEdges` (`≤ ⌈TP.γ_ℓ (M₀²)⌉ + 1`) and `treePaths` (`≤ 2 * (⌈TP.γ_ℓ (M₀²)⌉ + 1)`) summing to `Δ`. -/
theorem alg2_update_optDir_cycle_rep_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t, t + 1 ≤ T → isUpdate (t + 1) = true → ∀ Δ,
      minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = some Δ →
      let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
      let T_tree := stNext.extTree
      (D.G (t + 1)).IsSubgraph T_tree ∧
      T_tree.IsForest ∧
      (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
        (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
      ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
        T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
      ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
        offTreeEdges.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 ∧
        (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
        treePaths.length ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1) ∧
        (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
        ∀ e : ℕ, Δ e =
          (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
          (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum := by
  have hUncond := algorithm2_uncond_preserves_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound
  have hExtLG := alg2UncondInv_extℓ_extg_with (cfg := cfg) (η := η) κ hHist
  intro t ht1 hupd Δ hSome
  have ht_le : t ≤ T := Nat.le_of_succ_le ht1
  have hUI := hUncond.1 t ht_le
  rcases hUI with ⟨hInv, hBud, _, _, hFresh, hExtG, _, hChℓ, _, _, _, hShB, hBranD, _, _⟩
  obtain ⟨hExtℓ, _⟩ := hExtLG t ht_le
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
  have hBatch := hHist.1 (t + 1) (Nat.succ_pos t) ht1
  simp only [Nat.add_sub_cancel] at hBatch
  have htb := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh (hExtG ▸ hBatch.1)
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  rcases htb with ⟨htbExt, htbFresh, htbBatch, htbNR, htbLen, htbNf, htbInsN, htbOld, htbNotIns, htbIns⟩
  have hExtG' : tb.1 = D.G (t + 1) := by rw [htbExt, hExtG, hBatch.2]
  have hExtValid : (D.G (t + 1)).IsValid := (hHist.2.1 (t + 1) ht1).1
  have hU_valid_int : ((st.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    htbFresh.isValid_iff.mpr (hExtG'.symm ▸ hExtValid)
  have hU_m : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [htbFresh.m_eq, hExtG']; exact hmBound (t + 1) ht1
  have hU_n : ((st.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [htbFresh.n_eq, hExtG']; exact hnBound (t + 1) ht1
  have hChℓ_D : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e') := by
    rw [hChℓ]; ext e'; rw [hExtℓ]
  have hℓ'_pos : ∀ e ∈ (D.G (t + 1)).E, 0 < D.ℓ (t + 1) e := (hHist.2.1 (t + 1) ht1).2
  have hℓ'_stable : ∀ e ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, e ∈ (st.chain.G 0).E →
      (∀ u ∈ tb.2.2.2.2, ¬ u.Inserts e) →
      D.ℓ (t + 1) (tb.2.2.1 e) = st.chain.ℓ e := by
    intro e he1 he0 hnoU
    obtain ⟨heq, heExt⟩ := htbFresh.hRight e he1
    have hD_no : ∀ u ∈ D.U (t + 1), ¬ u.Inserts (tb.2.2.1 e) := by
      intro u hu huIns
      have he_old : e < st.nextFresh := hFresh.hLtFresh e he0
      have hge := htbIns (tb.2.2.1 e) (hExtG' ▸ heExt) ⟨u, hu, huIns⟩
      rw [heq] at hge
      omega
    have hNotBet : D.NotInsertedBetween (tb.2.2.1 e) t (t + 1) := fun s hs1 hs2 u hu huIns => by
      have hst : s = t + 1 := by omega
      subst hst
      exact hD_no u hu huIns
    have hℓ_eq := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 (tb.2.2.1 e)
      (hExtG' ▸ heExt) hNotBet).2
    simp only [Nat.add_sub_cancel] at hℓ_eq
    rw [hℓ_eq, hChℓ_D]
    congr 1
    exact htbOld e (hFresh.hLtFresh e he0)
  have hℓ'_pos_int : ∀ e ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E,
      0 < D.ℓ (t + 1) (tb.2.2.1 e) := by
    intro e he
    exact hℓ'_pos _ (hExtG' ▸ (htbFresh.hRight e he).2)
  have hUpd := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud
    tb.2.2.2.2 (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
    htbBatch htbNR hU_valid_int hU_m hU_n hℓ'_pos_int hℓ'_stable
  set updRes := algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
    (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
  set ch1 := updRes.1
  have hG01 : ch1.G 0 = (st.chain.G 0).applyBatch tb.2.2.2.2 :=
    (update_G0_ℓ _ _ _ _ _ _ _ _ _).1
  have hFresh1 : FreshInv tb.1 (ch1.G 0) tb.2.1 tb.2.2.1 tb.2.2.2.1 := hG01 ▸ htbFresh
  set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  have hBranD1 : bp1.1 < cfg.P.k := by
    dsimp only [bp1]
    cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    · exact hBranD
    · exact cfg.P.hk
  have hShB1 : ∀ j : Fin (cfg.P.d + 1),
      (ch1.shiftCount j.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1.rebuildCount j.val := by
    intro j
    have hEq := hUpd.2.2.2.1 j.val
    have hRebLe : ∀ i, st.chain.rebuildCount i ≤ ch1.rebuildCount i := hUpd.2.2.2.2.1
    have hMono := gameShiftBound_mono_reb (P := cfg.P) (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) hRebLe j.val
    exact le_trans (hEq ▸ hShB j) hMono
  have hSpecF := algorithm2_updateWith_spec_fields cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))
  have hOptEq : minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t =
      (algorithm2_loopWith cfg κ tb.1 tb.2.1 (D.g (t + 1)) (D.ℓ (t + 1)) ch1 bp1.1 bp1.2
        (st.lctUpdateOps + (D.U (t + 1)).length)).2.2.2.2 :=
    hSpecF.1
  rw [hOptEq] at hSome
  have hLoopSome := alg2_loopWith_some_eq κ hV tb.1 tb.2.1 tb.2.2.1 tb.2.2.2.1 (D.g (t + 1)) (D.ℓ (t + 1))
    (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1)
    ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
    (st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2)
    le_rfl hUpd.1 hUpd.2.1 hShB1 hBranD1 hFresh1 Δ hSome
  rcases hLoopSome with ⟨hΔeq, hInvEnd, hFreshEnd⟩
  have hStStep : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
      (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1 := by
    rw [minRatioFailState.eq_2]
    simp only [hupd, ↓reduceIte]
    rfl
  set stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
  have hSt_extG : stNext.extG = D.G (t + 1) := by
    rw [hStStep, hSpecF.2.2.1, hExtG']
  have hInvNext : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ stNext.chain := by
    rw [hStStep, hSpecF.2.1]; exact hInvEnd
  have hFreshNext : FreshInv stNext.extG (stNext.chain.G 0) stNext.extToInt stNext.intToExt stNext.nextFresh := by
    rw [hStStep, hSpecF.2.1, hSpecF.2.2.1, hSpecF.2.2.2.1, hSpecF.2.2.2.2.1, hSpecF.2.2.2.2.2]
    exact hFreshEnd
  have hTHNext := hInvNext.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hT hV.hMWU hV.hEmb hV.hγM₀ hV.hγk
  have hSubNext := stNext.chain.toTreeChain.forestsAreSubgraphs_of_holds hTHNext.1
  have hRep := findCycle_tree_path_rep hV stNext hInvNext hFreshNext
  have hΔNext : Δ = liftEdgeFn stNext.extG stNext.extToInt (algorithm1_findCycle stNext.chain).1 := by
    rw [hStStep, hSpecF.2.1, hSpecF.2.2.1, hSpecF.2.2.2.1]; exact hΔeq
  rw [← hΔNext] at hRep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hSt_extG]; exact extTree_isSubgraph stNext
  · exact extTree_isForest stNext (hSt_extG ▸ hExtValid) hFreshNext
      (stNext.chain.toTreeChain.chainTree_isForest hTHNext.1 hSubNext)
  · intro u hu v hv hconn
    rw [← hSt_extG] at hu hv hconn
    exact extTree_connected_of_connected stNext hFreshNext hTHNext.1 hSubNext hTHNext.2.1 hu hv hconn
  · intro hConn
    rw [← hSt_extG] at hConn ⊢
    exact extTree_isSpanningTreeOn stNext (hSt_extG ▸ hExtValid) hFreshNext hTHNext.1 hSubNext hTHNext.2.1 hConn
  · rcases hRep with ⟨offTreeEdges, treePaths, h1, h2, h3, h4, h5⟩
    exact ⟨offTreeEdges, treePaths, h1, fun x hx => hSt_extG ▸ h2 x hx, h3, h4, h5⟩

/-- **Theorem 5.1 cycle-representation theorem for `algorithm2_ds`**: at every successful
`Update` step `t + 1 ≤ T` (`minRatioFailOptDir = some Δ`), the state `stNext` after step `t + 1`
maintains a spanning forest `T_tree := stNext.extTree ⊆ D.G (t + 1)` together with
`offTreeEdges` and `treePaths` summing to `Δ`. -/
theorem alg2_update_optDir_cycle_rep {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t, t + 1 ≤ T → isUpdate (t + 1) = true → ∀ Δ,
      minRatioFailOptDir (algorithm2_ds cfg) D η isUpdate t = some Δ →
      let stNext := minRatioFailState (algorithm2_ds cfg) D η isUpdate (t + 1)
      let T_tree := stNext.extTree
      (D.G (t + 1)).IsSubgraph T_tree ∧
      T_tree.IsForest ∧
      (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
        (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
      ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
        T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
      ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
        offTreeEdges.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 ∧
        (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
        treePaths.length ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1) ∧
        (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
        ∀ e : ℕ, Δ e =
          (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
          (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum :=
  alg2_update_optDir_cycle_rep_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hmBound hnBound

end Algorithm2CycleRep

end MinCostFlow.Chain
