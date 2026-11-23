module

public import MinCostFlow.ExpanderDecomp.RouteGraph
public import Mathlib.Data.Finset.Sort
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith

/-!
# Local multi-source layered BFS for `RouteOrCut`

This file defines a computable, local multi-source BFS (`bfsLayers`) on an induced subgraph
`G[V]` (`V ⊆ X`), scanning only the local adjacency lists `adjOf G X` of discovered vertices.
It is shared by both components of the router `routeOrCut`:

* `ShortPathBlock`: finds the exact shortest-path distance `j ≤ d` from `S ∩ V`
  to `T ∩ V` and the exact BFS distance map `dist` up to layer `j` (stopping as soon as a
  layer hits `T`).
* `growBall`: grows BFS layers from `S` and `T` up to radius `h * L`, stopping
  early whenever the frontier becomes empty (so a reachable component finishes with zero
  boundary and never loops `h * L` times).

The exact operation count `BFSResult.cost` is bounded by `3 * |V| + ∑_{u ∈ V} (adj u).length + 2`,
and hence by `3 * |X| + 2 * (G.inside X).length + 2`, independent of `maxDist`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Result of a local multi-source layered BFS in `G[V]`. -/
structure BFSResult where
  /-- Discovered layers `L_0, L_1, ..., L_k` in forward order. -/
  layers : List (List ℕ)
  /-- All visited vertices (`⋃ L_r`). -/
  visited : Finset ℕ
  /-- Distance map: `some r` on `L_r`, `none` outside `visited`. -/
  dist : ℕ → Option ℕ
  /-- Index of the last populated layer (`0` when empty). -/
  maxReached : ℕ
  /-- `true` iff BFS stopped upon reaching `stopSet`. -/
  hitStop : Bool
  /-- `true` iff BFS stopped because the frontier became empty. -/
  exhausted : Bool
  /-- Exact operation count of the BFS run. -/
  cost : ℕ

/-- Scan one adjacency list, discovering unvisited neighbors in `V` at distance `nextDist`. -/
def bfsScanAdj (V : Finset ℕ) (nextDist : ℕ) :
    List (ℕ × ℕ) → List ℕ → Finset ℕ → (ℕ → Option ℕ) →
    List ℕ × Finset ℕ × (ℕ → Option ℕ) × ℕ
  | [], nxt, vis, dist => (nxt, vis, dist, 0)
  | (w, _) :: rest, nxt, vis, dist =>
    if w ∈ V ∧ w ∉ vis then
      let r := bfsScanAdj V nextDist rest (w :: nxt) (insert w vis)
        (Function.update dist w (some nextDist))
      (r.1, r.2.1, r.2.2.1, r.2.2.2 + 1)
    else
      let r := bfsScanAdj V nextDist rest nxt vis dist
      (r.1, r.2.1, r.2.2.1, r.2.2.2 + 1)

/-- Expand an entire BFS frontier layer `frontier`, producing the next layer at `nextDist`. -/
def bfsExpandFrontier (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ) :
    List ℕ → List ℕ → Finset ℕ → (ℕ → Option ℕ) →
    List ℕ × Finset ℕ × (ℕ → Option ℕ) × ℕ
  | [], nxt, vis, dist => (nxt, vis, dist, 0)
  | u :: rest, nxt, vis, dist =>
    let r1 := bfsScanAdj V nextDist (adj u) nxt vis dist
    let r2 := bfsExpandFrontier adj V nextDist rest r1.1 r1.2.1 r1.2.2.1
    (r2.1, r2.2.1, r2.2.2.1, r1.2.2.2 + r2.2.2.2 + 1)

/-- Main BFS layer loop, expanding up to `rem` additional layers. -/
def bfsLoop (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ) :
    ℕ → ℕ → List ℕ → List (List ℕ) → Finset ℕ → (ℕ → Option ℕ) → ℕ → BFSResult
  | 0, curDist, _frontier, revLayers, vis, dist, cost =>
    { layers := revLayers.reverse, visited := vis, dist := dist,
      maxReached := curDist, hitStop := false, exhausted := false, cost := cost }
  | rem + 1, curDist, frontier, revLayers, vis, dist, cost =>
    let r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
    let nxt := r.1
    let vis' := r.2.1
    let dist' := r.2.2.1
    let cost1 := cost + r.2.2.2 + 1
    if nxt.isEmpty then
      { layers := revLayers.reverse, visited := vis', dist := dist',
        maxReached := curDist, hitStop := false, exhausted := true, cost := cost1 }
    else
      let hit := nxt.any fun v => decide (v ∈ stopSet)
      let cost2 := cost1 + nxt.length
      if hit then
        { layers := (nxt :: revLayers).reverse, visited := vis', dist := dist',
          maxReached := curDist + 1, hitStop := true, exhausted := false, cost := cost2 }
      else
        bfsLoop adj V stopSet rem (curDist + 1) nxt (nxt :: revLayers) vis' dist' cost2

/-- Multi-source layered BFS from `S ∩ V` in `G[V]` up to distance `maxDist`, stopping early if a
layer intersects `stopSet` or becomes empty. -/
def bfsLayers (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ) (maxDist : ℕ)
    (stopSet : Finset ℕ) : BFSResult :=
  let S0 := S ∩ V
  let initLayer := S0.sort (· ≤ ·)
  if initLayer.isEmpty then
    { layers := [], visited := ∅, dist := fun _ => none,
      maxReached := 0, hitStop := false, exhausted := true, cost := 1 }
  else
    let initDist : ℕ → Option ℕ := fun v => if v ∈ S0 then some 0 else none
    let hit0 := initLayer.any fun v => decide (v ∈ stopSet)
    let cost0 := initLayer.length + initLayer.length + 1
    if hit0 then
      { layers := [initLayer], visited := S0, dist := initDist,
        maxReached := 0, hitStop := true, exhausted := false, cost := cost0 }
    else
      bfsLoop adj V stopSet maxDist 0 initLayer [initLayer] S0 initDist cost0

/-- Union of the first `j + 1` layers `L_0, ..., L_j`. -/
def ballPrefix (layers : List (List ℕ)) (j : ℕ) : Finset ℕ :=
  (layers.take (j + 1)).foldr (fun L acc => L.toFinset ∪ acc) ∅

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Properties of `bfsScanAdj` -/

private lemma bfsScanAdj_spec (V : Finset ℕ) (nextDist : ℕ) (l : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hvisV : vis ⊆ V) (hnxt_nd : nxt.Nodup) (hnxt_sub : ∀ x ∈ nxt, x ∈ vis)
    (hdist_vis : ∀ x ∈ vis, dist x ≠ none)
    (hdist_none : ∀ x, x ∉ vis → dist x = none)
    (hdist_nxt : ∀ x ∈ nxt, dist x = some nextDist) :
    let r := bfsScanAdj V nextDist l nxt vis dist
    r.2.2.2 = l.length ∧
    vis ⊆ r.2.1 ∧ r.2.1 ⊆ V ∧
    r.1.Nodup ∧
    (∀ x, x ∈ r.1 ↔ x ∈ nxt ∨ (x ∈ r.2.1 ∧ x ∉ vis)) ∧
    (∀ x ∈ vis, r.2.2.1 x = dist x) ∧
    (∀ x ∈ r.2.1, x ∉ vis → r.2.2.1 x = some nextDist) ∧
    (∀ x, x ∉ r.2.1 → r.2.2.1 x = none) ∧
    (∀ x ∈ r.2.1, x ∉ vis → ∃ e, (x, e) ∈ l) ∧
    (∀ w e, (w, e) ∈ l → w ∈ V → w ∈ r.2.1) := by
  induction l generalizing nxt vis dist with
  | nil =>
    refine ⟨rfl, Finset.Subset.refl _, hvisV, hnxt_nd, ?_, ?_, ?_, hdist_none, ?_, ?_⟩
    · intro x; tauto
    · intro _ _; rfl
    · intro x hx1 hx2; exact absurd hx1 hx2
    · intro x hx1 hx2; exact absurd hx1 hx2
    · intro _ _ h; cases h
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [bfsScanAdj]
    split_ifs with hcond
    · rcases hcond with ⟨hwV, hwVis⟩
      have hvis1V : insert w vis ⊆ V := Finset.insert_subset_iff.mpr ⟨hwV, hvisV⟩
      have hwNxt : w ∉ nxt := fun h => hwVis (hnxt_sub w h)
      have hnxt1_nd : (w :: nxt).Nodup := List.nodup_cons.mpr ⟨hwNxt, hnxt_nd⟩
      have hnxt1_sub : ∀ x ∈ w :: nxt, x ∈ insert w vis := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hnxt_sub x hx)
      have hdist1_vis : ∀ x ∈ insert w vis, Function.update dist w (some nextDist) x ≠ none := by
        intro x hx
        by_cases hxw : x = w
        · subst hxw; simp
        · simp only [Function.update_of_ne hxw]
          exact hdist_vis x (Finset.mem_of_mem_insert_of_ne hx hxw)
      have hdist1_none : ∀ x, x ∉ insert w vis →
          Function.update dist w (some nextDist) x = none := by
        intro x hx
        have hxw : x ≠ w := fun h => hx (h ▸ Finset.mem_insert_self _ _)
        simp only [Function.update_of_ne hxw]
        exact hdist_none x (fun h => hx (Finset.mem_insert_of_mem h))
      have hdist1_nxt : ∀ x ∈ w :: nxt, Function.update dist w (some nextDist) x = some nextDist := by
        intro x hx
        by_cases hxw : x = w
        · subst hxw; simp
        · simp only [Function.update_of_ne hxw]
          rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd rfl hxw
          · exact hdist_nxt x hx
      have hrec := ih (w :: nxt) (insert w vis) (Function.update dist w (some nextDist))
        hvis1V hnxt1_nd hnxt1_sub hdist1_vis hdist1_none hdist1_nxt
      rcases hrec with ⟨hlen, hsub1, hsubV, hnd, hmem, hEqVis, hEqNew, hNone, hFromL, hCov⟩
      refine ⟨by simp [hlen], le_trans (Finset.subset_insert w vis) hsub1, hsubV, hnd, ?_, ?_, ?_,
        hNone, ?_, ?_⟩
      · intro x
        rw [hmem x]
        by_cases hxw : x = w
        · subst hxw
          simp [hwVis, hsub1 (Finset.mem_insert_self _ _)]
        · simp only [List.mem_cons, hxw, false_or, Finset.mem_insert]
      · intro x hx
        have hxw : x ≠ w := fun h => hwVis (h ▸ hx)
        rw [hEqVis x (Finset.mem_insert_of_mem hx), Function.update_of_ne hxw]
      · intro x hx1 hx2
        by_cases hxw : x = w
        · subst hxw
          rw [hEqVis x (Finset.mem_insert_self _ _)]
          simp
        · exact hEqNew x hx1 (by simp [hxw, hx2])
      · intro x hx1 hx2
        by_cases hxw : x = w
        · subst hxw; exact ⟨e, List.mem_cons_self⟩
        · obtain ⟨e', he'⟩ := hFromL x hx1 (by simp [hxw, hx2])
          exact ⟨e', List.mem_cons_of_mem _ he'⟩
      · intro w' e' hmem' hw'V
        rcases List.mem_cons.mp hmem' with hEq | hmem'
        · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
          exact hsub1 (Finset.mem_insert_self _ _)
        · exact hCov w' e' hmem' hw'V
    · have hrec := ih nxt vis dist hvisV hnxt_nd hnxt_sub hdist_vis hdist_none hdist_nxt
      rcases hrec with ⟨hlen, hsub1, hsubV, hnd, hmem, hEqVis, hEqNew, hNone, hFromL, hCov⟩
      refine ⟨by simp [hlen], hsub1, hsubV, hnd, hmem, hEqVis, hEqNew, hNone, ?_, ?_⟩
      · intro x hx1 hx2
        obtain ⟨e', he'⟩ := hFromL x hx1 hx2
        exact ⟨e', List.mem_cons_of_mem _ he'⟩
      · intro w' e' hmem' hw'V
        rcases List.mem_cons.mp hmem' with hEq | hmem'
        · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
          have hwVis : w' ∈ vis := by
            by_contra hnot
            exact hcond ⟨hw'V, hnot⟩
          exact hsub1 hwVis
        · exact hCov w' e' hmem' hw'V

/-! ### Properties of `bfsExpandFrontier` -/

theorem bfsExpandFrontier_spec (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (frontier nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ)
    (hvisV : vis ⊆ V) (hnxt_nd : nxt.Nodup) (hnxt_sub : ∀ x ∈ nxt, x ∈ vis)
    (hdist_vis : ∀ x ∈ vis, dist x ≠ none)
    (hdist_none : ∀ x, x ∉ vis → dist x = none)
    (hdist_nxt : ∀ x ∈ nxt, dist x = some nextDist) :
    let r := bfsExpandFrontier adj V nextDist frontier nxt vis dist
    r.2.2.2 = frontier.length + (frontier.map fun u => (adj u).length).sum ∧
    vis ⊆ r.2.1 ∧ r.2.1 ⊆ V ∧
    r.1.Nodup ∧
    (∀ x, x ∈ r.1 ↔ x ∈ nxt ∨ (x ∈ r.2.1 ∧ x ∉ vis)) ∧
    (∀ x ∈ vis, r.2.2.1 x = dist x) ∧
    (∀ x ∈ r.2.1, x ∉ vis → r.2.2.1 x = some nextDist) ∧
    (∀ x, x ∉ r.2.1 → r.2.2.1 x = none) ∧
    (∀ x ∈ r.2.1, x ∉ vis → ∃ u ∈ frontier, ∃ e, (x, e) ∈ adj u) ∧
    (∀ u ∈ frontier, ∀ w e, (w, e) ∈ adj u → w ∈ V → w ∈ r.2.1) := by
  induction frontier generalizing nxt vis dist with
  | nil =>
    refine ⟨rfl, Finset.Subset.refl _, hvisV, hnxt_nd, ?_, ?_, ?_, hdist_none, ?_, ?_⟩
    · intro x; tauto
    · intro _ _; rfl
    · intro x hx1 hx2; exact absurd hx1 hx2
    · intro x hx1 hx2; exact absurd hx1 hx2
    · intro _ h; cases h
  | cons u rest ih =>
    simp only [bfsExpandFrontier]
    have h1 := bfsScanAdj_spec V nextDist (adj u) nxt vis dist
      hvisV hnxt_nd hnxt_sub hdist_vis hdist_none hdist_nxt
    rcases h1 with ⟨hc1, hsub1, hvis1V, hnd1, hmem1, hEq1, hNew1, hNone1, hFrom1, hCov1⟩
    set r1 := bfsScanAdj V nextDist (adj u) nxt vis dist
    have hnxt1_sub : ∀ x ∈ r1.1, x ∈ r1.2.1 := by
      intro x hx
      rcases (hmem1 x).mp hx with hx | ⟨hx, _⟩
      · exact hsub1 (hnxt_sub x hx)
      · exact hx
    have hdist1_vis : ∀ x ∈ r1.2.1, r1.2.2.1 x ≠ none := by
      intro x hx
      by_cases hxv : x ∈ vis
      · rw [hEq1 x hxv]; exact hdist_vis x hxv
      · rw [hNew1 x hx hxv]; simp
    have hdist1_nxt : ∀ x ∈ r1.1, r1.2.2.1 x = some nextDist := by
      intro x hx
      rcases (hmem1 x).mp hx with hx | ⟨hx1, hx2⟩
      · rw [hEq1 x (hnxt_sub x hx)]; exact hdist_nxt x hx
      · exact hNew1 x hx1 hx2
    have h2 := ih r1.1 r1.2.1 r1.2.2.1 hvis1V hnd1 hnxt1_sub hdist1_vis hNone1 hdist1_nxt
    rcases h2 with ⟨hc2, hsub2, hvis2V, hnd2, hmem2, hEq2, hNew2, hNone2, hFrom2, hCov2⟩
    refine ⟨?_, le_trans hsub1 hsub2, hvis2V, hnd2, ?_, ?_, ?_, hNone2, ?_, ?_⟩
    · simp only [List.length_cons, List.map_cons, List.sum_cons, hc1, hc2]
      omega
    · intro x
      rw [hmem2 x, hmem1 x]
      constructor
      · rintro ((hx | ⟨hx1, hx2⟩) | ⟨hx1, hx2⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨hsub2 hx1, hx2⟩
        · exact Or.inr ⟨hx1, fun h => hx2 (hsub1 h)⟩
      · rintro (hx | ⟨hx1, hx2⟩)
        · exact Or.inl (Or.inl hx)
        · by_cases h1 : x ∈ r1.2.1
          · exact Or.inl (Or.inr ⟨h1, hx2⟩)
          · exact Or.inr ⟨hx1, h1⟩
    · intro x hx
      rw [hEq2 x (hsub1 hx), hEq1 x hx]
    · intro x hx1 hx2
      by_cases h1 : x ∈ r1.2.1
      · rw [hEq2 x h1, hNew1 x h1 hx2]
      · exact hNew2 x hx1 h1
    · intro x hx1 hx2
      by_cases h1 : x ∈ r1.2.1
      · obtain ⟨e, he⟩ := hFrom1 x h1 hx2
        exact ⟨u, List.mem_cons_self, e, he⟩
      · obtain ⟨u', hu', e, he⟩ := hFrom2 x hx1 h1
        exact ⟨u', List.mem_cons_of_mem _ hu', e, he⟩
    · intro u' hu' w e he hwV
      rcases List.mem_cons.mp hu' with rfl | hu'
      · exact hsub2 (hCov1 w e he hwV)
      · exact hCov2 u' hu' w e he hwV


private lemma bfsLoop_layers_nonempty (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ) :
    ∀ (rem curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
      (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost : ℕ),
      (∀ L ∈ revLayers, L ≠ []) →
      ∀ L ∈ (bfsLoop adj V stopSet rem curDist frontier revLayers vis dist cost).layers, L ≠ []
  | 0, _, _, _, _, _, _, hne, L, hL => hne L (List.mem_reverse.mp hL)
  | rem + 1, curDist, frontier, revLayers, vis, dist, cost, hne, L, hL => by
    simp only [bfsLoop] at hL
    set r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist with hr_def
    by_cases hempty : r.1.isEmpty = true
    · simp only [hempty, ↓reduceIte] at hL
      exact hne L (List.mem_reverse.mp hL)
    · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hL
      have hr1_ne : r.1 ≠ [] := fun h => hempty (List.isEmpty_iff.mpr h)
      have hne' : ∀ M ∈ r.1 :: revLayers, M ≠ [] := by
        intro M hM
        rcases List.mem_cons.mp hM with rfl | hM
        · exact hr1_ne
        · exact hne M hM
      by_cases hhit : (r.1.any fun v => decide (v ∈ stopSet)) = true
      · simp only [hhit, ↓reduceIte] at hL
        exact hne' L (List.mem_reverse.mp hL)
      · simp only [hhit, Bool.false_eq_true, ↓reduceIte] at hL
        exact bfsLoop_layers_nonempty adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers)
          r.2.1 r.2.2.1 (cost + r.2.2.2 + 1 + r.1.length) hne' L hL

/-- Every layer returned by `bfsLayers` is nonempty. -/
theorem bfsLayers_layers_nonempty (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ)
    (maxDist : ℕ) (stopSet : Finset ℕ) :
    ∀ L ∈ (bfsLayers adj V S maxDist stopSet).layers, L ≠ [] := by
  unfold bfsLayers
  dsimp only
  set S0 := S ∩ V
  set initLayer := S0.sort (· ≤ ·)
  by_cases hempty : initLayer.isEmpty = true
  · simp only [hempty, ↓reduceIte]; simp
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
    have hne : initLayer ≠ [] := fun h => hempty (List.isEmpty_iff.mpr h)
    by_cases hhit : (initLayer.any fun v => decide (v ∈ stopSet)) = true
    · simp only [hhit, ↓reduceIte]
      intro L hL
      rw [List.mem_singleton] at hL
      exact hL ▸ hne
    · simp only [hhit, Bool.false_eq_true, ↓reduceIte]
      exact bfsLoop_layers_nonempty adj V stopSet maxDist 0 initLayer [initLayer] S0
        (fun v => if v ∈ S0 then some 0 else none) (initLayer.length + initLayer.length + 1)
        (fun L hL => by rw [List.mem_singleton] at hL; exact hL ▸ hne)

end MinCostFlow.ExpanderDecomp
