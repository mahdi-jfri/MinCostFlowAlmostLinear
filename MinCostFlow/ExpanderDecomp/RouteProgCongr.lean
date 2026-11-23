module

public import MinCostFlow.ExpanderDecomp.RouteBatch
import Mathlib.Tactic.Linarith

/-!
# Neighbor-Only Congruence Lemmas for `RouteOrCut` Subroutines

Proves that `bfsLayers`, `growBall`, and `batchBallLoop` depend only on the neighbor list
`(adj u).map Prod.fst` (ignoring host edge indices), and identifies the neighbors of
`adjOf ⟨G.n, G.inside V⟩ X v` with the `V`-filtered neighbors of `adjOf G X v` for `V ⊆ X`.
This lets the Word-RAM ball-growing pass construct a neighbor-only residual CSR directly from
the compact local CSR of `G[X]` in `O(|X| + e_X + 1)` time.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

lemma bfsScanAdj_congr_fst (V : Finset ℕ) (nextDist : ℕ)
    {l1 l2 : List (ℕ × ℕ)} (hfst : l1.map Prod.fst = l2.map Prod.fst)
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    bfsScanAdj V nextDist l1 nxt vis dist = bfsScanAdj V nextDist l2 nxt vis dist := by
  induction l1 generalizing l2 nxt vis dist with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hfst
  | cons p1 rest1 ih =>
    cases l2 with
    | nil => simp at hfst
    | cons p2 rest2 =>
      rcases p1 with ⟨w1, e1⟩
      rcases p2 with ⟨w2, e2⟩
      simp only [List.map_cons, List.cons.injEq] at hfst
      rcases hfst with ⟨rfl, hrest⟩
      simp only [bfsScanAdj]
      split_ifs
      · rw [ih hrest]
      · rw [ih hrest]

lemma bfsExpandFrontier_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (nextDist : ℕ) (frontier : List ℕ) (hfr : ∀ u ∈ frontier, u ∈ V)
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    bfsExpandFrontier adj1 V nextDist frontier nxt vis dist =
      bfsExpandFrontier adj2 V nextDist frontier nxt vis dist := by
  induction frontier generalizing nxt vis dist with
  | nil => rfl
  | cons u rest ih =>
    simp only [bfsExpandFrontier]
    have huV : u ∈ V := hfr u List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ V := fun x hx => hfr x (List.mem_cons_of_mem _ hx)
    rw [bfsScanAdj_congr_fst V nextDist (hadj u huV) nxt vis dist]
    set r1 := bfsScanAdj V nextDist (adj2 u) nxt vis dist
    rw [ih hrest r1.1 r1.2.1 r1.2.2.1]

private lemma bfsScanAdj_mem_V {V : Finset ℕ} {nextDist : ℕ} {l : List (ℕ × ℕ)}
    {nxt : List ℕ} {vis : Finset ℕ} {dist : ℕ → Option ℕ}
    (hnxt : ∀ u ∈ nxt, u ∈ V) :
    ∀ u ∈ (bfsScanAdj V nextDist l nxt vis dist).1, u ∈ V := by
  induction l generalizing nxt vis dist with
  | nil => exact hnxt
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [bfsScanAdj]
    split_ifs with h
    · exact ih (fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact h.1
        · exact hnxt u hu')
    · exact ih hnxt

private lemma bfsExpandFrontier_mem_V {adj : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    {nextDist : ℕ} {frontier nxt : List ℕ} {vis : Finset ℕ} {dist : ℕ → Option ℕ}
    (hnxt : ∀ u ∈ nxt, u ∈ V) :
    ∀ u ∈ (bfsExpandFrontier adj V nextDist frontier nxt vis dist).1, u ∈ V := by
  induction frontier generalizing nxt vis dist with
  | nil => exact hnxt
  | cons u rest ih =>
    simp only [bfsExpandFrontier]
    exact ih (bfsScanAdj_mem_V hnxt)

lemma bfsLoop_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V stopSet : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (rem curDist : ℕ) (frontier : List ℕ) (hfr : ∀ u ∈ frontier, u ∈ V)
    (revLayers : List (List ℕ)) (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost : ℕ) :
    bfsLoop adj1 V stopSet rem curDist frontier revLayers vis dist cost =
      bfsLoop adj2 V stopSet rem curDist frontier revLayers vis dist cost := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero => rfl
  | succ rem ih =>
    simp only [bfsLoop]
    rw [bfsExpandFrontier_congr_fst hadj (curDist + 1) frontier hfr [] vis dist]
    set r := bfsExpandFrontier adj2 V (curDist + 1) frontier [] vis dist
    have hrV : ∀ u ∈ r.1, u ∈ V := bfsExpandFrontier_mem_V (fun _ h => by cases h)
    split_ifs
    · rfl
    · rfl
    · exact ih (curDist + 1) r.1 hrV (r.1 :: revLayers) r.2.1 r.2.2.1 _

lemma bfsLayers_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ) :
    bfsLayers adj1 V S maxDist stopSet = bfsLayers adj2 V S maxDist stopSet := by
  unfold bfsLayers
  dsimp only
  split_ifs
  · rfl
  · rfl
  · apply bfsLoop_congr_fst hadj
    intro u hu
    rw [Finset.mem_sort] at hu
    exact (Finset.mem_inter.mp hu).2

lemma countIncidence_congr_fst (V cur : Finset ℕ) (u : ℕ)
    {l1 l2 : List (ℕ × ℕ)} (hfst : l1.map Prod.fst = l2.map Prod.fst) :
    countIncidence V cur u l1 = countIncidence V cur u l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hfst
  | cons p1 rest1 ih =>
    cases l2 with
    | nil => simp at hfst
    | cons p2 rest2 =>
      rcases p1 with ⟨w1, e1⟩
      rcases p2 with ⟨w2, e2⟩
      simp only [List.map_cons, List.cons.injEq] at hfst
      rcases hfst with ⟨rfl, hrest⟩
      simp only [countIncidence, ih hrest]

lemma addLayerToBall_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (L : List ℕ) (hL : ∀ u ∈ L, u ∈ V) (cur : Finset ℕ) (bd cost : ℕ) :
    addLayerToBall adj1 V L cur bd cost = addLayerToBall adj2 V L cur bd cost := by
  induction L generalizing cur bd cost with
  | nil => rfl
  | cons u rest ih =>
    simp only [addLayerToBall]
    rw [countIncidence_congr_fst V cur u (hadj u (hL u List.mem_cons_self))]
    exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ _ _

lemma scanBallLayers_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (b : ℕ) (layers : List (List ℕ)) (hL : ∀ L ∈ layers, ∀ u ∈ L, u ∈ V)
    (cur : Finset ℕ) (bd cost : ℕ) :
    scanBallLayers adj1 V b layers cur bd cost = scanBallLayers adj2 V b layers cur bd cost := by
  induction layers generalizing cur bd cost with
  | nil => rfl
  | cons L rest ih =>
    simp only [scanBallLayers]
    rw [addLayerToBall_congr_fst hadj L (hL L List.mem_cons_self) cur bd cost]
    split_ifs
    · rfl
    · exact ih (fun L' hL' => hL L' (List.mem_cons_of_mem _ hL')) _ _ _

private lemma bfsLoop_layers_mem_V {adj : ℕ → List (ℕ × ℕ)} {V stopSet : Finset ℕ}
    {rem curDist : ℕ} {frontier : List ℕ} {revLayers : List (List ℕ)}
    {vis : Finset ℕ} {dist : ℕ → Option ℕ} {cost : ℕ}
    (hrev : ∀ L ∈ revLayers, ∀ u ∈ L, u ∈ V) :
    ∀ L ∈ (bfsLoop adj V stopSet rem curDist frontier revLayers vis dist cost).layers,
      ∀ u ∈ L, u ∈ V := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero =>
    intro L hL u hu
    simp only [bfsLoop, List.mem_reverse] at hL
    exact hrev L hL u hu
  | succ rem ih =>
    simp only [bfsLoop]
    set r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
    have hrV : ∀ u ∈ r.1, u ∈ V := bfsExpandFrontier_mem_V (fun _ h => by cases h)
    split_ifs
    · intro L hL u hu
      simp only [List.mem_reverse] at hL
      exact hrev L hL u hu
    · intro L hL u hu
      simp only [List.mem_reverse, List.mem_cons] at hL
      rcases hL with rfl | hL'
      · exact hrV u hu
      · exact hrev L hL' u hu
    · apply ih
      intro L hL u hu
      rcases List.mem_cons.mp hL with rfl | hL'
      · exact hrV u hu
      · exact hrev L hL' u hu

private lemma bfsLayers_layers_mem_V (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ)
    (maxDist : ℕ) (stopSet : Finset ℕ) :
    ∀ L ∈ (bfsLayers adj V S maxDist stopSet).layers, ∀ u ∈ L, u ∈ V := by
  unfold bfsLayers
  dsimp only
  have hinit : ∀ u ∈ (S ∩ V).sort (· ≤ ·), u ∈ V := by
    intro u hu
    rw [Finset.mem_sort] at hu
    exact (Finset.mem_inter.mp hu).2
  split_ifs
  · intro L hL; cases hL
  · intro L hL u hu
    simp only [List.mem_singleton] at hL
    subst hL
    exact hinit u hu
  · apply bfsLoop_layers_mem_V
    intro L hL u hu
    simp only [List.mem_singleton] at hL
    subst hL
    exact hinit u hu

lemma growBall_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {V : Finset ℕ}
    (hadj : ∀ u ∈ V, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (S T : Finset ℕ) (b h L : ℕ) :
    growBall adj1 V S T b h L = growBall adj2 V S T b h L := by
  unfold growBall
  dsimp only
  rw [bfsLayers_congr_fst hadj S (h * L) ∅, bfsLayers_congr_fst hadj T (h * L) ∅]
  set bfsS := bfsLayers adj2 V S (h * L) ∅
  set bfsT := bfsLayers adj2 V T (h * L) ∅
  set bfs := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
  have hmem : ∀ L' ∈ bfs.layers, ∀ u ∈ L', u ∈ V := by
    dsimp only [bfs]
    split_ifs
    · exact bfsLayers_layers_mem_V adj2 V S (h * L) ∅
    · exact bfsLayers_layers_mem_V adj2 V T (h * L) ∅
  rw [scanBallLayers_congr_fst hadj b bfs.layers hmem ∅ 0 (bfsS.cost + bfsT.cost + 1)]

lemma batchBallLoop_congr_fst {adj1 adj2 : ℕ → List (ℕ × ℕ)} {X : Finset ℕ}
    (hadj : ∀ u ∈ X, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst)
    (b h L : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (U Vlive : Finset ℕ)
    (hVlive : Vlive ⊆ X) (cost : ℕ) :
    batchBallLoop adj1 X b h L pairs U Vlive cost =
      batchBallLoop adj2 X b h L pairs U Vlive cost := by
  induction pairs generalizing U Vlive cost with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨A', B'⟩
    simp only [batchBallLoop]
    split_ifs
    · rfl
    · exact ih U Vlive hVlive (cost + 1)
    · have hadjV : ∀ u ∈ Vlive, (adj1 u).map Prod.fst = (adj2 u).map Prod.fst :=
        fun u hu => hadj u (hVlive hu)
      rw [growBall_congr_fst hadjV (A' ∩ Vlive) (B' ∩ Vlive) b h L]
      exact ih _ _ (Finset.sdiff_subset.trans hVlive) _

/-- Residual adjacency neighbors: for `V ⊆ X`, `(adjOf ⟨G.n, G.inside V⟩ X v).map Prod.fst`
equals the `V`-filtered neighbor list of `adjOf G X v` when `v ∈ V`, and `[]` otherwise. -/
lemma adjOf_inside_map_fst (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X) (v : ℕ) :
    (adjOf ⟨G.n, G.inside V⟩ X v).map Prod.fst =
      if v ∈ V then ((adjOf G X v).filter fun p => decide (p.1 ∈ V)).map Prod.fst else [] := by
  have hgen : ∀ (es : List (ℕ × ℕ)) (r1 r2 : ℕ),
      ((((((es.filter fun e => insideB V e).zipIdx r1).map Prod.swap).filter
        fun ie => insideB X ie.2).flatMap fun ie =>
          (if ie.2.1 = v then [(ie.2.2, ie.1)] else []) ++
          (if ie.2.2 = v then [(ie.2.1, ie.1)] else []))).map Prod.fst =
      if v ∈ V then
        ((((((es.zipIdx r2).map Prod.swap).filter fun ie => insideB X ie.2).flatMap fun ie =>
          (if ie.2.1 = v then [(ie.2.2, ie.1)] else []) ++
          (if ie.2.2 = v then [(ie.2.1, ie.1)] else []))).filter fun p => decide (p.1 ∈ V)).map
          Prod.fst
      else [] := by
    intro es
    induction es with
    | nil =>
      intro r1 r2
      split_ifs <;> simp
    | cons e rest ih =>
      intro r1 r2
      rcases e with ⟨a, b⟩
      by_cases hVab : insideB V (a, b) = true
      · have hVab' : a ∈ V ∧ b ∈ V := by
          unfold insideB at hVab
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hVab
          exact hVab
        have hXab : insideB X (a, b) = true := by
          unfold insideB
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hVX hVab'.1, hVX hVab'.2⟩
        simp only [List.filter_cons, hVab, ↓reduceIte, List.zipIdx_cons, List.map_cons,
          Prod.swap_prod_mk, hXab, List.flatMap_cons, List.map_append, List.filter_append]
        by_cases hvV : v ∈ V
        · simp only [hvV, ↓reduceIte] at ih ⊢
          rw [ih (r1 + 1) (r2 + 1)]
          by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb, hVab'.1, hVab'.2, hvV]
        · simp only [hvV, ↓reduceIte] at ih ⊢
          have hna : a ≠ v := fun h => hvV (h ▸ hVab'.1)
          have hnb : b ≠ v := fun h => hvV (h ▸ hVab'.2)
          simp only [hna, hnb, ↓reduceIte]
          exact ih (r1 + 1) (r2 + 1)
      · have hVab_f : insideB V (a, b) = false := Bool.eq_false_iff.mpr hVab
        have hnotV : ¬ (a ∈ V ∧ b ∈ V) := by
          intro h
          apply hVab
          unfold insideB
          simp [h.1, h.2]
        simp only [List.filter_cons, hVab_f, Bool.false_eq_true, ↓reduceIte, List.zipIdx_cons,
          List.map_cons, Prod.swap_prod_mk]
        by_cases hXab : insideB X (a, b) = true
        · simp only [hXab, ↓reduceIte, List.flatMap_cons, List.filter_append, List.map_append]
          by_cases hvV : v ∈ V
          · simp only [hvV, ↓reduceIte] at ih ⊢
            rw [ih r1 (r2 + 1)]
            by_cases ha : a = v <;> by_cases hb : b = v
            · exact absurd ⟨ha.symm ▸ hvV, hb.symm ▸ hvV⟩ hnotV
            · have hbn : b ∉ V := fun hbV => hnotV ⟨ha.symm ▸ hvV, hbV⟩
              simp [ha, hb, hbn]
            · have han : a ∉ V := fun haV => hnotV ⟨haV, hb.symm ▸ hvV⟩
              simp [ha, hb, han]
            · simp [ha, hb]
          · simp only [hvV, ↓reduceIte] at ih ⊢
            exact ih r1 (r2 + 1)
        · have hXab_f : insideB X (a, b) = false := Bool.eq_false_iff.mpr hXab
          simp only [hXab_f, Bool.false_eq_true, ↓reduceIte]
          exact ih r1 (r2 + 1)
  unfold adjOf insideEdgesIdx Graph.inside
  exact hgen G.edges 0 0

end MinCostFlow.ExpanderDecomp
