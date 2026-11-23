module

public import MinCostFlow.Chain.Ordered.UpdateTraceHelpers
public import MinCostFlow.Chain.CyclePathRep
public import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith

/-!
# Spanning-Tree Path and Off-Tree Edge Representation for Ordered `FindCycle`

Proves `findCycle_tree_path_rep` for ordered `ChainInv` (`MinCostFlow.Chain.Ordered`),
reusing `Alg2State.extTree`, `extTree_*`, `mapWalk`, `cycleSegments`, and
`walkFlow_stitchCycle_segments` from `MinCostFlow/Chain/CyclePathRep.lean`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

private lemma mapWalk_src {G₁ G₂ : MGraph} {f : ℕ → ℕ}
    (ht : ∀ x : ℕ × Bool, x.1 ∈ G₁.E → G₂.tail (f x.1) = G₁.tail x.1)
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
under ordered `ChainInv` + `FreshInv`, `Δ = liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1`
decomposes into `offTreeEdges` (`length ≤ ⌈γ_ℓ(M₀²)⌉ + 1`) outside `st.extTree.E` and
`treePaths` (`length ≤ 2 * (⌈γ_ℓ(M₀²)⌉ + 1)`) of `st.extTree`-connected endpoint pairs. -/
theorem findCycle_tree_path_rep {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
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
  have hTH := ChainInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk hInv
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

end MinCostFlow.Chain.Ordered
