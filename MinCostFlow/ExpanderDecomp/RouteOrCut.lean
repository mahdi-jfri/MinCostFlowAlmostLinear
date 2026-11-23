module

public import MinCostFlow.ExpanderDecomp.RouteBatch
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Repeated batches and the router `RouteOrCut`

This file assembles the full static multi-pair matching player `routeOrCut` and its explicit
operation count `routeOrCutCost`:

* Empty or already-satisfied demands (`totalDemand pairs ≤ z`) return immediately with empty
  matchings and zero cost.
* Otherwise, `routeBatches` runs up to `R = H_batch * L` batches of `runBatch` on the original
  host `G[X]` with the remaining unmatched demands, accumulating per-pair matchings and walks
  while stopping early if `totalDemand ≤ z` or if a batch returns a sparse cut `U`.
* Each successful batch shrinks total demand by a factor `≤ 1 - 1/H_batch`. By the integer
  inequality `2 * (H_batch - 1)^H_batch < H_batch^H_batch` (`two_mul_pred_pow_lt_pow`),
  after `R = H_batch * L` successful batches `2^L * D_final ≤ D_0 < 2^L`, so `D_final = 0 ≤ z`.
* Each batch routes vertex-disjoint (hence edge-disjoint) simple paths of length `≤ d`, so
  across at most `R` batches every host edge has congestion at most `R`.

Main results:
* `routeOrCut`, `routeOrCutCost`: the router model and its step count.
* `routeOrCut_spec`: router correctness (both outcomes, matching `RouteSpec` and `Embedding.lean`).
* `routeOrCutCost_le`: the step-count bound `routeOrCutCost ≤ 20 * k * (|X| + e_X + 1) * (d + 1) * R`.
* `routeR_le` (in `RouteGraph.lean`): the congestion bound `R ≤ 528 Δ² b² L²`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Explicit constant in the router step-count bound. -/
def routeCostConst : ℕ := 20

/-- Build the `RouteResult.matched` output from accumulated per-pair routed walks. -/
def mkMatchedResult (acc : List (List ((ℕ × ℕ) × List ℕ))) : RouteResult :=
  RouteResult.matched (acc.map fun ps => ps.map Prod.fst)
    (fun j => (acc.flatten.getD j ((0, 0), [])).2)

/-- Repeated batches loop: runs up to `rem` batches, stopping early once
`totalDemand curPairs ≤ z` or a batch returns a sparse cut. Returns `(result, totalCost)`. -/
def routeBatches (G : Graph) (X : Finset ℕ) (Δ b L z : ℕ) :
    ℕ → List (Finset ℕ × Finset ℕ) → List (List ((ℕ × ℕ) × List ℕ)) → ℕ →
    RouteResult × ℕ
  | 0, _curPairs, acc, cost =>
    (mkMatchedResult acc, cost)
  | rem + 1, curPairs, acc, cost =>
    if totalDemand curPairs ≤ z then
      (mkMatchedResult acc, cost)
    else
      let br := runBatch G X Δ b L curPairs
      match br.outcome with
      | BatchOutcome.cut U => (RouteResult.cut U, cost + br.cost)
      | BatchOutcome.matched batchPaths remPairs =>
        routeBatches G X Δ b L z rem remPairs
          (List.zipWith (· ++ ·) acc batchPaths) (cost + br.cost)

/-- Raw execution of `RouteOrCut`, returning `(outcome, cost)`. Empty or already-satisfied
demands (`totalDemand pairs ≤ z`) return immediately with cost `0`. -/
def routeOrCutRaw (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) : RouteResult × ℕ :=
  if totalDemand pairs ≤ z then
    (RouteResult.matched (List.replicate pairs.length []) (fun _ => []), 0)
  else
    routeBatches G X Δ b L z (routeR Δ b L) pairs (List.replicate pairs.length []) 0

/-- **`RouteOrCut`**: deterministic static multi-pair matching player on `(G, X)`. -/
def routeOrCut (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) : RouteResult :=
  (routeOrCutRaw G X pairs Δ L b z).1

/-- Explicit operation count of `routeOrCut`, tracking all local BFS, DFS, ball-growing,
and batch operations. -/
def routeOrCutCost (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) : ℕ :=
  (routeOrCutRaw G X pairs Δ L b z).2

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-! ### Edge usage and congestion helpers -/

/-- Number of routed walks in `ps` that traverse host edge `e`. -/
private def edgeUses (ps : List ((ℕ × ℕ) × List ℕ)) (e : ℕ) : ℕ :=
  (ps.filter fun q => decide (e ∈ q.2)).length

private lemma edgeUses_append (ps qs : List ((ℕ × ℕ) × List ℕ)) (e : ℕ) :
    edgeUses (ps ++ qs) e = edgeUses ps e + edgeUses qs e := by
  unfold edgeUses
  rw [List.filter_append, List.length_append]

private lemma edgeUses_zipWith_flatten
    (acc batch : List (List ((ℕ × ℕ) × List ℕ))) (hlen : acc.length = batch.length) (e : ℕ) :
    edgeUses (List.zipWith (· ++ ·) acc batch).flatten e =
      edgeUses acc.flatten e + edgeUses batch.flatten e := by
  induction acc generalizing batch with
  | nil =>
    cases batch with
    | nil => simp [edgeUses]
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    cases batch with
    | nil => simp at hlen
    | cons b brest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, List.flatten_cons, edgeUses_append, ih brest hlen]
      omega

private lemma edgeUses_le_one_of_walkVerts_pairwise {G : Graph}
    {ps : List ((ℕ × ℕ) × List ℕ)}
    (hwalk : ∀ p ∈ ps, IsEdgeWalk G.edges p.1.1 p.1.2 p.2)
    (hdisj : ps.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset)
    (e : ℕ) :
    edgeUses ps e ≤ 1 := by
  unfold edgeUses
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.pairwise_cons] at hdisj
    rw [List.filter_cons]
    by_cases he : e ∈ p.2
    · simp only [he, decide_true, ↓reduceIte, List.length_cons]
      have hzero : (rest.filter fun q => decide (e ∈ q.2)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq
        simp only [decide_eq_true_eq]
        have hdisj_verts : ∀ w, w ∈ walkVerts G.edges p.1.1 p.2 → w ∉ walkVerts G.edges q.1.1 q.2 := by
          intro w hw1 hw2
          exact Finset.disjoint_left.mp (hdisj.1 q hq)
            (List.mem_toFinset.mpr hw1) (List.mem_toFinset.mpr hw2)
        exact (hwalk p List.mem_cons_self).edge_disjoint_of_walkVerts_disjoint
          (hwalk q (List.mem_cons_of_mem _ hq)) hdisj_verts e he
      rw [hzero]
      simp
    · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun q hq => hwalk q (List.mem_cons_of_mem _ hq)) hdisj.2

private lemma map_flatten_fst (acc : List (List ((ℕ × ℕ) × List ℕ))) :
    (acc.map fun ps => ps.map Prod.fst).flatten = acc.flatten.map Prod.fst := by
  induction acc with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.flatten_cons, List.map_append, ih]

private lemma congestion_mkMatchedResult (G : Graph) (acc : List (List ((ℕ × ℕ) × List ℕ))) (e : ℕ) :
    congestion (Graph.mk G.n (acc.map fun ps => ps.map Prod.fst).flatten)
      (fun j => (acc.flatten.getD j ((0, 0), [])).2) e =
    edgeUses acc.flatten e := by
  unfold congestion edgeUses Graph.m
  rw [map_flatten_fst, List.length_map]
  rw [length_filter_eq_card_range _ _ ((0, 0), [])]
  simp only [decide_eq_true_eq]

private lemma isEmbeddingOn_mkMatchedResult (G : Graph) (X : Finset ℕ)
    (acc : List (List ((ℕ × ℕ) × List ℕ)))
    (hwalks : ∀ p ∈ acc.flatten, IsEdgeWalkIn G X p.1.1 p.1.2 p.2) :
    IsEmbeddingOn (Graph.mk G.n (acc.map fun ps => ps.map Prod.fst).flatten) G X
      (fun j => (acc.flatten.getD j ((0, 0), [])).2) := by
  intro j hj _
  unfold Graph.m at hj
  rw [map_flatten_fst, List.length_map] at hj
  have hmem : acc.flatten.getD j ((0, 0), []) ∈ acc.flatten := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hedge : edgeAt (acc.map fun ps => ps.map Prod.fst).flatten j =
      (acc.flatten.getD j ((0, 0), [])).1 := by
    unfold edgeAt
    rw [map_flatten_fst]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
      List.getD_eq_getElem _ _ hj, List.getElem_map]
  rw [hedge]
  exact hwalks _ hmem

private lemma zipWith_deficit_eq_totalDemand
    (origPairs curPairs : List (Finset ℕ × Finset ℕ))
    (acc : List (List ((ℕ × ℕ) × List ℕ)))
    (hlen1 : curPairs.length = origPairs.length)
    (hlen2 : acc.length = origPairs.length)
    (hcard : ∀ i (hi : i < origPairs.length),
      (curPairs.getD i (∅, ∅)).1.card + (acc.getD i []).length = (origPairs[i]'hi).1.card) :
    (List.zipWith (fun p M => p.1.card - M.length) origPairs
      (acc.map fun ps => ps.map Prod.fst)).sum =
    totalDemand curPairs := by
  induction origPairs generalizing curPairs acc with
  | nil =>
    cases curPairs with
    | nil =>
      cases acc with
      | nil => simp [totalDemand]
      | cons _ _ => simp at hlen2
    | cons _ _ => simp at hlen1
  | cons p prest ih =>
    cases curPairs with
    | nil => simp at hlen1
    | cons c crest =>
      cases acc with
      | nil => simp at hlen2
      | cons a arest =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen1 hlen2
        have h0 := hcard 0 (Nat.zero_lt_succ _)
        simp only [List.getD_cons_zero, List.getElem_cons_zero] at h0
        have hrest := ih crest arest hlen1 hlen2 (fun i hi => by
          have hi' := hcard (i + 1) (Nat.succ_lt_succ hi)
          simpa only [List.getD_cons_succ, List.getElem_cons_succ] using hi')
        simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, List.length_map,
          totalDemand] at hrest ⊢
        omega

/-! ### Invariant and specification of `routeBatches` -/

/-- State invariant maintained across batches of `routeBatches`. -/
private structure BatchLoopInv (G : Graph) (X : Finset ℕ)
    (origPairs : List (Finset ℕ × Finset ℕ)) (d : ℕ)
    (t : ℕ) (curPairs : List (Finset ℕ × Finset ℕ))
    (acc : List (List ((ℕ × ℕ) × List ℕ))) : Prop where
  len_cur : curPairs.length = origPairs.length
  len_acc : acc.length = origPairs.length
  valid_cur : RouteTerminalPairs X curPairs
  walks_ok : ∀ p ∈ acc.flatten, p.2.length ≤ d ∧ IsEdgeWalkIn G X p.1.1 p.1.2 p.2
  cong_le : ∀ e, edgeUses acc.flatten e ≤ t
  per_pair : ∀ i (hi : i < origPairs.length),
    let (A, B) := origPairs[i]'hi
    let (Ac, Bc) := curPairs.getD i (∅, ∅)
    let ps := acc.getD i []
    (∀ q ∈ ps, q.1.1 ∈ A ∧ q.1.2 ∈ B) ∧
    (ps.map fun q => q.1.1).Nodup ∧
    (ps.map fun q => q.1.2).Nodup ∧
    Ac = A \ (ps.map fun q => q.1.1).toFinset ∧
    Bc = B \ (ps.map fun q => q.1.2).toFinset ∧
    Ac.card + ps.length = A.card

private lemma mkMatchedResult_spec (G : Graph) (X : Finset ℕ)
    (origPairs : List (Finset ℕ × Finset ℕ)) (Δ L b z t : ℕ)
    (curPairs : List (Finset ℕ × Finset ℕ)) (acc : List (List ((ℕ × ℕ) × List ℕ)))
    (hinv : BatchLoopInv G X origPairs (routeD Δ b L) t curPairs acc)
    (ht_le : t ≤ routeR Δ b L)
    (hdef : totalDemand curPairs ≤ z) :
    RouteSpec G X origPairs Δ L b z (mkMatchedResult acc) := by
  unfold mkMatchedResult RouteSpec RouteMatchedSpec
  dsimp only
  refine ⟨by simp [hinv.len_acc], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi_spec := hinv.per_pair i hi
    have hlen_acc := hinv.len_acc
    have hi_acc : i < acc.length := by omega
    have hgetM : (acc.map fun ps => ps.map Prod.fst).getD i [] = (acc.getD i []).map Prod.fst := by
      rw [List.getD_eq_getElem _ _ (by simp [hi_acc]), List.getD_eq_getElem _ _ hi_acc,
        List.getElem_map]
    rw [hgetM]
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rw [List.mem_map] at he
      obtain ⟨q, hq, rfl⟩ := he
      exact hi_spec.1 q hq
    · rw [List.map_map]; exact hi_spec.2.1
    · rw [List.map_map]; exact hi_spec.2.2.1
  · rw [zipWith_deficit_eq_totalDemand origPairs curPairs acc hinv.len_cur hinv.len_acc
      (fun i hi => (hinv.per_pair i hi).2.2.2.2.2)]
    exact hdef
  · exact isEmbeddingOn_mkMatchedResult G X acc (fun p hp => (hinv.walks_ok p hp).2)
  · intro j hj
    rw [map_flatten_fst, List.length_map] at hj
    have hmem : acc.flatten.getD j ((0, 0), []) ∈ acc.flatten := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact (hinv.walks_ok _ hmem).1
  · intro e _
    rw [congestion_mkMatchedResult]
    exact le_trans (hinv.cong_le e) ht_le

private lemma demand_zero_after_R_batches {H L D0 D : ℕ} (hH : 2 ≤ H) (_hL : 1 ≤ L)
    (hD0 : D0 < 2 ^ L) (hdecay : H ^ (H * L) * D ≤ (H - 1) ^ (H * L) * D0) :
    D = 0 := by
  have hbin : 2 * (H - 1) ^ H < H ^ H := two_mul_pred_pow_lt_pow hH
  have hpowL : 2 ^ L * (H - 1) ^ (H * L) ≤ H ^ (H * L) := by
    calc
      2 ^ L * (H - 1) ^ (H * L) = 2 ^ L * ((H - 1) ^ H) ^ L := by rw [Nat.pow_mul]
      _ = (2 * (H - 1) ^ H) ^ L := (Nat.mul_pow 2 ((H - 1) ^ H) L).symm
      _ ≤ (H ^ H) ^ L := Nat.pow_le_pow_left (Nat.le_of_lt hbin) L
      _ = H ^ (H * L) := (Nat.pow_mul H H L).symm
  have hchain : H ^ (H * L) * (2 ^ L * D) ≤ H ^ (H * L) * D0 := by
    calc
      H ^ (H * L) * (2 ^ L * D) = 2 ^ L * (H ^ (H * L) * D) := by ring
      _ ≤ 2 ^ L * ((H - 1) ^ (H * L) * D0) := Nat.mul_le_mul_left (2 ^ L) hdecay
      _ = (2 ^ L * (H - 1) ^ (H * L)) * D0 := by ring
      _ ≤ H ^ (H * L) * D0 := Nat.mul_le_mul_right D0 hpowL
  have hpos : 0 < H ^ (H * L) := Nat.pow_pos (by omega)
  have h2LD : 2 ^ L * D ≤ D0 := Nat.le_of_mul_le_mul_left hchain hpos
  have hlt : 2 ^ L * D < 2 ^ L * 1 := by omega
  have hD_lt : D < 1 := Nat.lt_of_mul_lt_mul_left hlt
  omega

private theorem routeBatches_spec (G : Graph) {X : Finset ℕ}
    (origPairs : List (Finset ℕ × Finset ℕ)) (horig : RouteTerminalPairs X origPairs)
    {Δ L b z : ℕ} (hΔ : 1 ≤ Δ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L)
    (rem t : ℕ) (ht_rem : t + rem = routeR Δ b L)
    (curPairs : List (Finset ℕ × Finset ℕ)) (acc : List (List ((ℕ × ℕ) × List ℕ)))
    (cost : ℕ)
    (hinv : BatchLoopInv G X origPairs (routeD Δ b L) t curPairs acc)
    (hdecay : (routeHBatch Δ b L) ^ t * totalDemand curPairs ≤
      (routeHBatch Δ b L - 1) ^ t * totalDemand origPairs) :
    let res := routeBatches G X Δ b L z rem curPairs acc cost
    RouteSpec G X origPairs Δ L b z res.1 ∧
    res.2 ≤ cost + rem * (routeCostConst * origPairs.length *
      (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) := by
  induction rem generalizing t curPairs acc cost with
  | zero =>
    simp only [routeBatches, Nat.zero_mul, Nat.add_zero]
    have ht_eq : t = routeR Δ b L := by omega
    subst ht_eq
    have hD0_lt : totalDemand origPairs < 2 ^ L := by
      have h2D := two_mul_totalDemand_le horig
      omega
    have hD_zero : totalDemand curPairs = 0 :=
      demand_zero_after_R_batches (routeHBatch_ge_two hΔ (by omega)) hL hD0_lt hdecay
    exact ⟨mkMatchedResult_spec G X origPairs Δ L b z (routeR Δ b L) curPairs acc hinv
      (le_refl _) (by omega), le_refl _⟩
  | succ rem ih =>
    simp only [routeBatches]
    by_cases hdone : totalDemand curPairs ≤ z
    · simp only [eq_true hdone, ↓reduceIte]
      exact ⟨mkMatchedResult_spec G X origPairs Δ L b z t curPairs acc hinv (by omega) hdone,
        Nat.le_add_right _ _⟩
    · simp only [eq_false hdone, ↓reduceIte]
      have hdem_pos : 1 ≤ totalDemand curPairs := by omega
      have hbatch := runBatch_spec G hΔ hb hL hdeg hcard curPairs hinv.valid_cur hdem_pos
      set br := runBatch G X Δ b L curPairs with hbr_def
      rcases hbatch with ⟨hmatched, hcut, hbr_cost⟩
      have hbr_cost' : br.cost ≤ routeCostConst * origPairs.length *
          (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1) := by
        unfold routeCostConst
        rw [← hinv.len_cur]
        exact hbr_cost
      cases hout : br.outcome with
      | cut U =>
        dsimp only
        obtain ⟨hUX, hUcut, hU1, hU2⟩ := hcut U hout
        have hz1 : z + 1 ≤ 2 * U.card := by omega
        have hz2 : z + 1 ≤ 2 * (X \ U).card := by omega
        refine ⟨⟨hUX, hUcut, hz1, hz2⟩, ?_⟩
        have hmul : (rem + 1) * (routeCostConst * origPairs.length *
            (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) =
            rem * (routeCostConst * origPairs.length *
              (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) +
            routeCostConst * origPairs.length *
              (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1) := by ring
        omega
      | matched batchPaths remPairs =>
        dsimp only
        obtain ⟨hb_len1, hb_len2, hb_walks, hb_disj, hb_idx, hb_valid, _, hb_prog⟩ :=
          hmatched batchPaths remPairs hout
        set acc' := List.zipWith (· ++ ·) acc batchPaths
        have hlen_acc_batch : acc.length = batchPaths.length := by
          rw [hinv.len_acc, hb_len1, hinv.len_cur]
        have hacc'_len : acc'.length = origPairs.length := by
          simp [acc', hinv.len_acc, hb_len1, hinv.len_cur]
        have hlen_acc0 := hinv.len_acc
        have hlen_cur0 := hinv.len_cur
        have hacc'_walks : ∀ p ∈ acc'.flatten,
            p.2.length ≤ routeD Δ b L ∧ IsEdgeWalkIn G X p.1.1 p.1.2 p.2 := by
          intro p hp
          rw [List.mem_flatten] at hp
          obtain ⟨L_i, hLi, hpL⟩ := hp
          rw [List.mem_iff_getElem] at hLi
          obtain ⟨i, hi, rfl⟩ := hLi
          have hi_orig : i < origPairs.length := by omega
          have hi_acc : i < acc.length := by omega
          have hi_bp : i < batchPaths.length := by omega
          have hget : acc'[i]'hi = acc[i]'hi_acc ++ batchPaths[i]'hi_bp :=
            List.getElem_zipWith
          rw [hget, List.mem_append] at hpL
          rcases hpL with hp1 | hp2
          · exact hinv.walks_ok p (List.mem_flatten.mpr ⟨acc[i]'hi_acc, List.getElem_mem hi_acc, hp1⟩)
          · have hpb := hb_walks p (List.mem_flatten.mpr ⟨batchPaths[i]'hi_bp, List.getElem_mem hi_bp, hp2⟩)
            exact ⟨hpb.1, hpb.2.1⟩
        have hacc'_cong : ∀ e, edgeUses acc'.flatten e ≤ t + 1 := by
          intro e
          rw [edgeUses_zipWith_flatten acc batchPaths hlen_acc_batch e]
          have h1 := hinv.cong_le e
          have h2 : edgeUses batchPaths.flatten e ≤ 1 :=
            edgeUses_le_one_of_walkVerts_pairwise (fun p hp => (hb_walks p hp).2.1.1) hb_disj e
          omega
        have hacc'_pair : ∀ i (hi : i < origPairs.length),
            let (A, B) := origPairs[i]'hi
            let (Ac, Bc) := remPairs.getD i (∅, ∅)
            let ps := acc'.getD i []
            (∀ q ∈ ps, q.1.1 ∈ A ∧ q.1.2 ∈ B) ∧
            (ps.map fun q => q.1.1).Nodup ∧
            (ps.map fun q => q.1.2).Nodup ∧
            Ac = A \ (ps.map fun q => q.1.1).toFinset ∧
            Bc = B \ (ps.map fun q => q.1.2).toFinset ∧
            Ac.card + ps.length = A.card := by
          intro i hi
          have hi_cur : i < curPairs.length := by omega
          have hi_acc : i < acc.length := by omega
          have hi_bp : i < batchPaths.length := by omega
          have hi_acc' : i < acc'.length := by omega
          have hprev := hinv.per_pair i hi
          have hstep := hb_idx i hi_cur
          have hcur_getD : curPairs.getD i (∅, ∅) = curPairs[i]'hi_cur :=
            List.getD_eq_getElem _ _ hi_cur
          rw [hcur_getD] at hprev
          have hacc'_getD : acc'.getD i [] = acc.getD i [] ++ batchPaths.getD i [] := by
            rw [List.getD_eq_getElem _ _ hi_acc', List.getD_eq_getElem _ _ hi_acc,
              List.getD_eq_getElem _ _ hi_bp, List.getElem_zipWith]
          dsimp only at hprev hstep ⊢
          rw [hacc'_getD]
          set A := (origPairs[i]'hi).1
          set B := (origPairs[i]'hi).2
          set Ac := (curPairs[i]'hi_cur).1
          set Bc := (curPairs[i]'hi_cur).2
          set Ar := (remPairs.getD i (∅, ∅)).1
          set Br := (remPairs.getD i (∅, ∅)).2
          set ps0 := acc.getD i []
          set ps1 := batchPaths.getD i []
          have hAc_eq : Ac = A \ (ps0.map fun q => q.1.1).toFinset := hprev.2.2.2.1
          have hBc_eq : Bc = B \ (ps0.map fun q => q.1.2).toFinset := hprev.2.2.2.2.1
          have hAr_eq : Ar = Ac \ (ps1.map fun q => q.1.1).toFinset := hstep.2.2.2.1
          have hBr_eq : Br = Bc \ (ps1.map fun q => q.1.2).toFinset := hstep.2.2.2.2.1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with hq0 | hq1
            · exact hprev.1 q hq0
            · have hq1A : q.1.1 ∈ Ac := (hstep.1 q hq1).1
              have hq1B : q.1.2 ∈ Bc := (hstep.1 q hq1).2.1
              rw [hAc_eq] at hq1A
              rw [hBc_eq] at hq1B
              exact ⟨Finset.sdiff_subset hq1A, Finset.sdiff_subset hq1B⟩
          · rw [List.map_append, List.nodup_append]
            refine ⟨hprev.2.1, hstep.2.1, fun x hx0 y hy1 hEq => ?_⟩
            subst hEq
            rw [List.mem_map] at hy1
            obtain ⟨q, hq1, rfl⟩ := hy1
            have hqA : q.1.1 ∈ Ac := (hstep.1 q hq1).1
            rw [hAc_eq, Finset.mem_sdiff] at hqA
            exact hqA.2 (List.mem_toFinset.mpr hx0)
          · rw [List.map_append, List.nodup_append]
            refine ⟨hprev.2.2.1, hstep.2.2.1, fun x hx0 y hy1 hEq => ?_⟩
            subst hEq
            rw [List.mem_map] at hy1
            obtain ⟨q, hq1, rfl⟩ := hy1
            have hqB : q.1.2 ∈ Bc := (hstep.1 q hq1).2.1
            rw [hBc_eq, Finset.mem_sdiff] at hqB
            exact hqB.2 (List.mem_toFinset.mpr hx0)
          · rw [hAr_eq, hAc_eq, List.map_append, List.toFinset_append]
            ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
          · rw [hBr_eq, hBc_eq, List.map_append, List.toFinset_append]
            ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
          · have h1 : Ac.card + ps0.length = A.card := hprev.2.2.2.2.2
            have h2 : Ar.card + ps1.length = Ac.card := hstep.2.2.2.2.2.1
            simp only [List.length_append]
            omega
        have hinv' : BatchLoopInv G X origPairs (routeD Δ b L) (t + 1) remPairs acc' :=
          { len_cur := hb_len2.trans hinv.len_cur
            len_acc := hacc'_len
            valid_cur := hb_valid
            walks_ok := hacc'_walks
            cong_le := hacc'_cong
            per_pair := hacc'_pair }
        have hdecay' : (routeHBatch Δ b L) ^ (t + 1) * totalDemand remPairs ≤
            (routeHBatch Δ b L - 1) ^ (t + 1) * totalDemand origPairs := by
          set H := routeHBatch Δ b L
          calc
            H ^ (t + 1) * totalDemand remPairs
                = H ^ t * (H * totalDemand remPairs) := by rw [Nat.pow_succ]; ring
            _ ≤ H ^ t * ((H - 1) * totalDemand curPairs) := Nat.mul_le_mul_left (H ^ t) hb_prog
            _ = (H - 1) * (H ^ t * totalDemand curPairs) := by ring
            _ ≤ (H - 1) * ((H - 1) ^ t * totalDemand origPairs) :=
                  Nat.mul_le_mul_left (H - 1) hdecay
            _ = (H - 1) ^ (t + 1) * totalDemand origPairs := by rw [Nat.pow_succ]; ring
        have hrec := ih (t + 1) (by omega) remPairs acc' (cost + br.cost) hinv' hdecay'
        rcases hrec with ⟨hspec_rec, hcost_rec⟩
        refine ⟨hspec_rec, ?_⟩
        have hmul : (rem + 1) * (routeCostConst * origPairs.length *
            (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) =
            rem * (routeCostConst * origPairs.length *
              (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) +
            routeCostConst * origPairs.length *
              (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1) := by ring
        omega

/-! ### Router correctness (`routeOrCut_spec`) and running-time bound (`routeOrCutCost_le`) -/

/-- **`RouteOrCut` correctness and step count.**
On any graph `(G, X)` with maximum degree `≤ Δ`, `|X| < 2^L`, `b ≥ 2`, and pairwise disjoint
terminal pairs `pairs` with `|A_i| ≤ |B_i|`:
* `routeOrCut` returns either partial matchings with total deficit `≤ z`, embedding walks of
  length `≤ d = 32 Δ b L`, and edge congestion `≤ R = H_batch * L` in `G[X]`, or a cut `U ⊆ X`
  of the original host `G[X]` with `b * G.cutIn X U ≤ min |U| |X \ U|` and both sides at least
  `(z + 1) / 2`.
* `routeOrCutCost ≤ 20 * k * (|X| + (G.inside X).length + 1) * (d + 1) * R`. -/
theorem routeOrCut_spec_and_cost (G : Graph) {X : Finset ℕ}
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs)
    {Δ L b z : ℕ} (hΔ : 1 ≤ Δ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L) :
    RouteSpec G X pairs Δ L b z (routeOrCut G X pairs Δ L b z) ∧
    routeOrCutCost G X pairs Δ L b z ≤
      routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
        (routeD Δ b L + 1) * routeR Δ b L := by
  unfold routeOrCut routeOrCutCost routeOrCutRaw
  by_cases hdone : totalDemand pairs ≤ z
  · simp only [eq_true hdone, ↓reduceIte]
    refine ⟨?_, Nat.zero_le _⟩
    unfold RouteSpec RouteMatchedSpec
    dsimp only
    have hflat_nil : (List.replicate pairs.length ([] : List (ℕ × ℕ))).flatten = [] := by
      induction pairs.length with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hget : (List.replicate pairs.length ([] : List (ℕ × ℕ))).getD i [] = [] := by
        rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_replicate]
      rw [hget]
      simp
    · have hzip : (List.zipWith (fun (p : Finset ℕ × Finset ℕ) (M : List (ℕ × ℕ)) =>
          p.1.card - M.length) pairs (List.replicate pairs.length [])).sum = totalDemand pairs := by
        unfold totalDemand
        clear hdone hvalid hflat_nil
        induction pairs with
        | nil => simp
        | cons p rest ih => simp [List.replicate_succ, ih]
      rw [hzip]
      exact hdone
    · intro j hj
      unfold Graph.m at hj
      rw [hflat_nil] at hj
      simp at hj
    · intro j hj
      rw [hflat_nil] at hj
      simp at hj
    · intro e _
      unfold congestion Graph.m
      rw [hflat_nil]
      simp
  · simp only [eq_false hdone, ↓reduceIte]
    set initAcc : List (List ((ℕ × ℕ) × List ℕ)) := List.replicate pairs.length []
    have hflat_nil : initAcc.flatten = [] := by
      unfold initAcc
      induction pairs.length with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih]
    have hinv0 : BatchLoopInv G X pairs (routeD Δ b L) 0 pairs initAcc :=
      { len_cur := rfl
        len_acc := by simp [initAcc]
        valid_cur := hvalid
        walks_ok := fun _ hp => by rw [hflat_nil] at hp; simp at hp
        cong_le := fun e => by simp [edgeUses, hflat_nil]
        per_pair := fun i hi => by
          have hgetP : pairs.getD i (∅, ∅) = pairs[i]'hi := List.getD_eq_getElem _ _ hi
          have hgetA : initAcc.getD i [] = [] := by
            rw [List.getD_eq_getElem _ _ (by simp [initAcc, hi])]
            simp only [initAcc, List.getElem_replicate]
          dsimp only
          rw [hgetP, hgetA]
          simp }
    have hres := routeBatches_spec G pairs hvalid (z := z) hΔ hb hL hdeg hcard (routeR Δ b L) 0
      (Nat.zero_add _) pairs initAcc 0 hinv0 (by simp)
    rcases hres with ⟨hspec, hcost⟩
    refine ⟨hspec, ?_⟩
    have hmul : routeR Δ b L * (routeCostConst * pairs.length *
        (X.card + (G.inside X).length + 1) * (routeD Δ b L + 1)) =
        routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
          (routeD Δ b L + 1) * routeR Δ b L := by ring
    omega

/-- **`RouteOrCut` correctness.** -/
theorem routeOrCut_spec (G : Graph) {X : Finset ℕ}
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs)
    {Δ L b z : ℕ} (hΔ : 1 ≤ Δ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L) :
    RouteSpec G X pairs Δ L b z (routeOrCut G X pairs Δ L b z) :=
  (routeOrCut_spec_and_cost G pairs hvalid hΔ hb hL hdeg hcard).1

/-- **Step-count bound** for `routeOrCutCost` with explicit constant
`routeCostConst = 20`. -/
theorem routeOrCutCost_le (G : Graph) {X : Finset ℕ}
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs)
    {Δ L b z : ℕ} (hΔ : 1 ≤ Δ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L) :
    routeOrCutCost G X pairs Δ L b z ≤
      routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
        (routeD Δ b L + 1) * routeR Δ b L :=
  (routeOrCut_spec_and_cost G pairs hvalid hΔ hb hL hdeg hcard).2

end MinCostFlow.ExpanderDecomp
