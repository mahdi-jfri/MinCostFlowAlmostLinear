module

public import MinCostFlow.ExpanderDecomp.RouteShortPath
public import MinCostFlow.ExpanderDecomp.RouteBall
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One routing batch

Given pairwise disjoint terminal pairs `(A_1, B_1), ..., (A_k, B_k)` inside `X` with
`|A_i| ≤ |B_i|` and positive total demand `D_dem = ∑ |A_i|`:

1. Process the pairs in order, running `shortPathBlock` in the common residual graph `G[V_act]`
   (with `V_act` starting at `X`), globally isolating all vertices on accepted paths.
2. Remove only matched endpoints from `(A_i, B_i)`; unmatched terminals that occurred internally
   on another pair's path remain in their terminal set and in `X`, isolated.
3. Let `p` be the total number of accepted paths. If `p * H_batch ≥ D_dem`, the batch succeeds
   and reduces demand to `D_dem - p ≤ (1 - 1/H_batch) D_dem`.
4. Otherwise, in `H_res = ⟨G.n, G.inside V_act_final⟩`, every remaining pair has distance `> d`,
   and the deleted volume satisfies `16 * b * vol_G(X \ V_act_final) < D_dem`. Repeatedly apply
   `growBall` until `4 * |U| ≥ |X|` or all pairs are exhausted. The resulting cut
   `U ⊆ X` satisfies `b * G.cutIn X U ≤ min(|U|, |X \ U|)` and `2 * |U|, 2 * |X \ U| ≥ D_dem`
   in the original host `G[X]`.

The step count of one batch is bounded by `20 * k * (|X| + (G.inside X).length + 1) * (d + 1)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Result of routing all terminal pairs through `shortPathBlock` in one batch. -/
structure BatchRouteResult where
  /-- Per-pair lists of routed walks `((a, b), es)`. -/
  perPairPaths : List (List ((ℕ × ℕ) × List ℕ))
  /-- Remaining unmatched terminal pairs `(A_i', B_i')`. -/
  remPairs : List (Finset ℕ × Finset ℕ)
  /-- Remaining unisolated vertices `V_act_final ⊆ X`. -/
  remVerts : Finset ℕ
  /-- Total number of paths accepted across all pairs. -/
  routedCount : ℕ
  /-- Exact operation count of the routing pass. -/
  cost : ℕ

/-- Process terminal pairs sequentially in the common residual graph `G[V]`, globally isolating
vertices of accepted paths and removing only matched endpoints from each pair. -/
def batchRoutePairs (adj : ℕ → List (ℕ × ℕ)) (d : ℕ) :
    List (Finset ℕ × Finset ℕ) → Finset ℕ → BatchRouteResult
  | [], V =>
    { perPairPaths := [], remPairs := [], remVerts := V, routedCount := 0, cost := 0 }
  | (A, B) :: rest, V =>
    let sp := shortPathBlock adj V A B d
    let matchedL := (sp.paths.map fun p => p.1.1).toFinset
    let matchedR := (sp.paths.map fun p => p.1.2).toFinset
    let A' := A \ matchedL
    let B' := B \ matchedR
    let tail := batchRoutePairs adj d rest sp.remVerts
    { perPairPaths := sp.paths :: tail.perPairPaths
      remPairs := (A', B') :: tail.remPairs
      remVerts := tail.remVerts
      routedCount := sp.paths.length + tail.routedCount
      cost := sp.cost + tail.cost + 1 }

/-- Repeatedly grow low-boundary balls in `H_res` over remaining terminal pairs until
`4 * |U| ≥ |X|` or all pairs are exhausted. Returns `(U, cost)`. -/
def batchBallLoop (adjRes : ℕ → List (ℕ × ℕ)) (X : Finset ℕ) (b h L : ℕ) :
    List (Finset ℕ × Finset ℕ) → Finset ℕ → Finset ℕ → ℕ → Finset ℕ × ℕ
  | [], U, _Vlive, cost => (U, cost)
  | (A', B') :: rest, U, Vlive, cost =>
    if 4 * U.card ≥ X.card then
      (U, cost + 1)
    else
      let S := A' ∩ Vlive
      let T := B' ∩ Vlive
      if S = ∅ ∨ T = ∅ then
        batchBallLoop adjRes X b h L rest U Vlive (cost + 1)
      else
        let br := growBall adjRes Vlive S T b h L
        batchBallLoop adjRes X b h L rest (U ∪ br.ball) (Vlive \ br.ball) (cost + br.cost + 1)

/-- Outcome of one routing batch. -/
inductive BatchOutcome
  | matched (perPairPaths : List (List ((ℕ × ℕ) × List ℕ)))
      (remPairs : List (Finset ℕ × Finset ℕ))
  | cut (U : Finset ℕ)

/-- Result of one routing batch together with its exact operation count. -/
structure BatchResult where
  outcome : BatchOutcome
  cost : ℕ

/-- `runBatch`: one routing batch on `(G, X)` with parameters `(Δ, b, L)` and
disjoint terminal pairs `pairs`. -/
def runBatch (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) : BatchResult :=
  let adj := adjOf G X
  let d := routeD Δ b L
  let br := batchRoutePairs adj d pairs X
  let Ddem := totalDemand pairs
  let Hbatch := routeHBatch Δ b L
  if br.routedCount * Hbatch ≥ Ddem then
    { outcome := BatchOutcome.matched br.perPairPaths br.remPairs
      cost := br.cost + pairs.length + 1 }
  else
    let Hres : Graph := ⟨G.n, G.inside br.remVerts⟩
    let adjRes := adjOf Hres X
    let resBuildCost := X.card + 2 * (G.inside X).length + 1
    let cutRes := batchBallLoop adjRes X b (routeH Δ b) L br.remPairs ∅ X
      (br.cost + pairs.length + 1 + resBuildCost)
    { outcome := BatchOutcome.cut cutRes.1
      cost := cutRes.2 }

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Helper lemmas for matching endpoints and `batchRoutePairs` -/

private lemma map_fst_nodup_of_walkVerts_pairwise {G : Graph} {ps : List ((ℕ × ℕ) × List ℕ)}
    (hdisj : ps.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) :
    (ps.map fun p => p.1.1).Nodup := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.pairwise_cons] at hdisj
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hdisj.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨q, hq, hEq⟩ := hmem
    have hp1 : p.1.1 ∈ (walkVerts G.edges p.1.1 p.2).toFinset :=
      List.mem_toFinset.mpr (mem_walkVerts_start _ _ _)
    have hq1 : p.1.1 ∈ (walkVerts G.edges q.1.1 q.2).toFinset := by
      rw [← hEq]
      exact List.mem_toFinset.mpr (mem_walkVerts_start _ _ _)
    exact Finset.disjoint_left.mp (hdisj.1 q hq) hp1 hq1

private lemma map_snd_nodup_of_walkVerts_pairwise {G : Graph} {ps : List ((ℕ × ℕ) × List ℕ)}
    (hwalk : ∀ p ∈ ps, IsEdgeWalk G.edges p.1.1 p.1.2 p.2)
    (hdisj : ps.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) :
    (ps.map fun p => p.1.2).Nodup := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    rw [List.pairwise_cons] at hdisj
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun q hq => hwalk q (List.mem_cons_of_mem _ hq)) hdisj.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨q, hq, hEq⟩ := hmem
    have hp2 : p.1.2 ∈ (walkVerts G.edges p.1.1 p.2).toFinset :=
      List.mem_toFinset.mpr (hwalk p List.mem_cons_self).mem_walkVerts_end
    have hq2 : p.1.2 ∈ (walkVerts G.edges q.1.1 q.2).toFinset := by
      rw [← hEq]
      exact List.mem_toFinset.mpr (hwalk q (List.mem_cons_of_mem _ hq)).mem_walkVerts_end
    exact Finset.disjoint_left.mp (hdisj.1 q hq) hp2 hq2

private lemma routedVerts_append' (G : Graph) (ps qs : List ((ℕ × ℕ) × List ℕ)) :
    routedVerts G (ps ++ qs) = routedVerts G ps ∪ routedVerts G qs := by
  induction ps with
  | nil => simp [routedVerts]
  | cons p rest ih =>
    simp only [List.cons_append, routedVerts, List.foldr_cons] at ih ⊢
    rw [ih, Finset.union_assoc]

/-- Specification of `batchRoutePairs`. -/
private theorem batchRoutePairs_spec (G : Graph) {X : Finset ℕ} (d : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs)
    (V : Finset ℕ) (hVX : V ⊆ X) :
    let res := batchRoutePairs (adjOf G X) d pairs V
    res.perPairPaths.length = pairs.length ∧
    res.remPairs.length = pairs.length ∧
    res.routedCount = res.perPairPaths.flatten.length ∧
    res.remVerts ⊆ V ∧
    res.remVerts = V \ routedVerts G res.perPairPaths.flatten ∧
    routedVerts G res.perPairPaths.flatten ⊆ V ∧
    (∀ p ∈ res.perPairPaths.flatten,
      p.2.length ≤ d ∧ IsSimpleWalkIn G V p.1.1 p.1.2 p.2) ∧
    (res.perPairPaths.flatten.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) ∧
    (∀ i (hi : i < pairs.length),
      let (A, B) := pairs[i]'hi
      let ps := res.perPairPaths.getD i []
      let (A', B') := res.remPairs.getD i (∅, ∅)
      (∀ q ∈ ps, q.1.1 ∈ A ∧ q.1.2 ∈ B ∧ q.2.length ≤ d ∧ IsSimpleWalkIn G X q.1.1 q.1.2 q.2) ∧
      (ps.map fun q => q.1.1).Nodup ∧
      (ps.map fun q => q.1.2).Nodup ∧
      A' = A \ (ps.map fun q => q.1.1).toFinset ∧
      B' = B \ (ps.map fun q => q.1.2).toFinset ∧
      A'.card + ps.length = A.card ∧
      B'.card + ps.length = B.card ∧
      A' ⊆ A ∧ B' ⊆ B ∧ A'.card ≤ B'.card ∧ Disjoint A' B' ∧
      (∀ a ∈ A', ∀ b ∈ B', ∀ es, IsEdgeWalkIn G res.remVerts a b es →
        a ∈ res.remVerts → b ∈ res.remVerts → d < es.length)) ∧
    RouteTerminalPairs X res.remPairs ∧
    totalDemand res.remPairs + res.routedCount = totalDemand pairs ∧
    res.cost ≤ pairs.length * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) := by
  induction pairs generalizing V with
  | nil =>
    simp only [batchRoutePairs, List.length_nil, List.flatten_nil, routedVerts, List.foldr_nil,
      Finset.sdiff_empty, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
      Nat.not_lt_zero, totalDemand, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_mul,
      le_refl, and_true, true_and, Finset.empty_subset]
    exact ⟨by simp, List.Pairwise.nil⟩
  | cons ab rest ih =>
    rcases ab with ⟨A, B⟩
    have hAB := hvalid.1 (A, B) List.mem_cons_self
    rcases hAB with ⟨hAX, hBX, hAB_card, hAB_disj⟩
    dsimp only at hAX hBX hAB_card hAB_disj
    have hrest_valid : RouteTerminalPairs X rest :=
      ⟨fun q hq => hvalid.1 q (List.mem_cons_of_mem _ hq), (List.pairwise_cons.mp hvalid.2).2⟩
    simp only [batchRoutePairs]
    set sp := shortPathBlock (adjOf G X) V A B d with hsp_def
    have hsp := shortPathBlock_spec G hVX A B hAB_disj d
    rcases hsp with ⟨hsp_subV, hsp_rem, hsp_verts_sub, hsp_valid, hsp_disj, hsp_nofar, hsp_cost⟩
    change sp.remVerts ⊆ V at hsp_subV
    change sp.remVerts = V \ routedVerts G sp.paths at hsp_rem
    change routedVerts G sp.paths ⊆ V at hsp_verts_sub
    change sp.cost ≤ 7 * (X.card + (G.inside X).length + 1) * (d + 1) at hsp_cost
    have hrec := ih hrest_valid sp.remVerts (le_trans hsp_subV hVX)
    set tail := batchRoutePairs (adjOf G X) d rest sp.remVerts with htail_def
    rcases hrec with ⟨ht_len1, ht_len2, ht_cnt, ht_subV, ht_rem, ht_verts_sub, ht_walk, ht_disj,
      ht_idx, ht_valid, ht_dem, ht_cost⟩
    have hndL : (sp.paths.map fun q => q.1.1).Nodup :=
      map_fst_nodup_of_walkVerts_pairwise hsp_disj
    have hndR : (sp.paths.map fun q => q.1.2).Nodup :=
      map_snd_nodup_of_walkVerts_pairwise (fun q hq => (hsp_valid q hq).2.2.2.1.1) hsp_disj
    have hL_subA : (sp.paths.map fun q => q.1.1).toFinset ⊆ A := by
      intro x hx
      rw [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact (Finset.mem_inter.mp (hsp_valid q hq).1).1
    have hR_subB : (sp.paths.map fun q => q.1.2).toFinset ⊆ B := by
      intro x hx
      rw [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact (Finset.mem_inter.mp (hsp_valid q hq).2.1).1
    have hcardL : (sp.paths.map fun q => q.1.1).toFinset.card = sp.paths.length := by
      rw [List.toFinset_card_of_nodup hndL, List.length_map]
    have hcardR : (sp.paths.map fun q => q.1.2).toFinset.card = sp.paths.length := by
      rw [List.toFinset_card_of_nodup hndR, List.length_map]
    have hA'_card : (A \ (sp.paths.map fun q => q.1.1).toFinset).card + sp.paths.length = A.card := by
      rw [← hcardL]; exact Finset.card_sdiff_add_card_eq_card hL_subA
    have hB'_card : (B \ (sp.paths.map fun q => q.1.2).toFinset).card + sp.paths.length = B.card := by
      rw [← hcardR]; exact Finset.card_sdiff_add_card_eq_card hR_subB
    have hrem_eq : tail.remVerts = V \ routedVerts G (sp.paths ++ tail.perPairPaths.flatten) := by
      rw [ht_rem, hsp_rem, routedVerts_append']
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hverts_all_sub : routedVerts G (sp.paths ++ tail.perPairPaths.flatten) ⊆ V := by
      rw [routedVerts_append']
      exact Finset.union_subset hsp_verts_sub (le_trans ht_verts_sub hsp_subV)
    have hdisj_all : (sp.paths ++ tail.perPairPaths.flatten).Pairwise fun p q =>
        Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset := by
      rw [List.pairwise_append]
      refine ⟨hsp_disj, ht_disj, fun p hp q hq => ?_⟩
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      have hv_sp : v ∈ routedVerts G sp.paths :=
        (mem_routedVerts_iff G sp.paths v).mpr ⟨p, hp, List.mem_toFinset.mp hv1⟩
      have hv_tail : v ∈ routedVerts G tail.perPairPaths.flatten :=
        (mem_routedVerts_iff G tail.perPairPaths.flatten v).mpr ⟨q, hq, List.mem_toFinset.mp hv2⟩
      have hv_rem : v ∈ sp.remVerts := ht_verts_sub hv_tail
      rw [hsp_rem] at hv_rem
      exact (Finset.mem_sdiff.mp hv_rem).2 hv_sp
    have hvalid_rem : RouteTerminalPairs X
        ((A \ (sp.paths.map fun q => q.1.1).toFinset,
          B \ (sp.paths.map fun q => q.1.2).toFinset) :: tail.remPairs) := by
      constructor
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · dsimp only
          exact ⟨le_trans Finset.sdiff_subset hAX, le_trans Finset.sdiff_subset hBX,
            by omega, Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset hAB_disj⟩
        · exact ht_valid.1 p hp
      · rw [List.pairwise_cons]
        refine ⟨?_, ht_valid.2⟩
        intro q hq
        rw [List.mem_iff_getElem] at hq
        obtain ⟨j, hj, rfl⟩ := hq
        have hj_rest : j < rest.length := by omega
        have hj_spec := ht_idx j hj_rest
        have hgetD : tail.remPairs.getD j (∅, ∅) = tail.remPairs[j]'hj :=
          List.getD_eq_getElem _ _ hj
        rw [hgetD] at hj_spec
        have hq_sub : (tail.remPairs[j]'hj).1 ∪ (tail.remPairs[j]'hj).2 ⊆
            (rest[j]'hj_rest).1 ∪ (rest[j]'hj_rest).2 :=
          Finset.union_subset_union hj_spec.2.2.2.2.2.2.2.1 hj_spec.2.2.2.2.2.2.2.2.1
        have hdisj_orig : Disjoint (A ∪ B) ((rest[j]'hj_rest).1 ∪ (rest[j]'hj_rest).2) :=
          (List.pairwise_cons.mp hvalid.2).1 (rest[j]'hj_rest) (List.getElem_mem hj_rest)
        exact Disjoint.mono (Finset.union_subset_union Finset.sdiff_subset Finset.sdiff_subset)
          hq_sub hdisj_orig
    refine ⟨by simp [ht_len1], by simp [ht_len2], by simp [ht_cnt],
      le_trans ht_subV hsp_subV, by simpa using hrem_eq, by simpa using hverts_all_sub,
      ?_, by simpa using hdisj_all, ?_, hvalid_rem, ?_, ?_⟩
    · intro p hp
      simp only [List.flatten_cons, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ⟨(hsp_valid p hp).2.2.1, (hsp_valid p hp).2.2.2⟩
      · obtain ⟨hlen, hw, hnd⟩ := ht_walk p hp
        exact ⟨hlen, hw.mono hsp_subV, hnd⟩
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getD_cons_zero]
        refine ⟨?_, hndL, hndR, trivial, trivial, hA'_card, hB'_card, Finset.sdiff_subset,
          Finset.sdiff_subset, by omega,
          Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset hAB_disj, ?_⟩
        · intro q hq
          obtain ⟨h1, h2, h3, hw, hnd⟩ := hsp_valid q hq
          exact ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1, h3, hw.mono hVX, hnd⟩
        · intro a ha b hb es hw haV hbV
          exact hsp_nofar a (Finset.sdiff_subset ha) b (Finset.sdiff_subset hb) es
            (hw.mono ht_subV) (ht_subV haV) (ht_subV hbV)
      | succ i' =>
        simp only [List.getElem_cons_succ, List.getD_cons_succ]
        exact ht_idx i' (by simpa using hi)
    · simp only [totalDemand, List.map_cons, List.sum_cons] at ht_dem ⊢
      omega
    · simp only [List.length_cons]
      have hmul : (rest.length + 1) * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) =
          rest.length * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) +
            (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) := by ring
      omega

/-! ### Specification of `batchBallLoop` -/

private lemma card_union_covered_ge {U : Finset ℕ} (pairs : List (Finset ℕ × Finset ℕ))
    (hpw : pairs.Pairwise fun p q => Disjoint (p.1 ∪ p.2) (q.1 ∪ q.2))
    (hcard : ∀ p ∈ pairs, p.1.card ≤ p.2.card)
    (hcov : ∀ p ∈ pairs, p.1 ⊆ U ∨ p.2 ⊆ U) :
    totalDemand pairs ≤ U.card := by
  have haux : ∀ (S : Finset ℕ),
      (∀ p ∈ pairs, p.1 ⊆ S ∨ p.2 ⊆ S) → totalDemand pairs ≤ S.card := by
    clear hcov
    induction pairs with
    | nil => intro S _; simp [totalDemand]
    | cons p rest ih =>
      intro S hS
      rw [List.pairwise_cons] at hpw
      have hp_card : p.1.card ≤ p.2.card := hcard p List.mem_cons_self
      have hrest_card : ∀ q ∈ rest, q.1.card ≤ q.2.card :=
        fun q hq => hcard q (List.mem_cons_of_mem _ hq)
      set C : Finset ℕ := if p.1 ⊆ S then p.1 else p.2
      have hCS : C ⊆ S := by
        dsimp only [C]
        split_ifs with h1
        · exact h1
        · exact (hS p List.mem_cons_self).resolve_left h1
      have hC_ge : p.1.card ≤ C.card := by
        dsimp only [C]
        split_ifs
        · exact le_refl _
        · exact hp_card
      have hC_sub_union : C ⊆ p.1 ∪ p.2 := by
        dsimp only [C]
        split_ifs
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
      have hrest_cov : ∀ q ∈ rest, q.1 ⊆ S \ C ∨ q.2 ⊆ S \ C := by
        intro q hq
        have hdisj_pq : Disjoint (p.1 ∪ p.2) (q.1 ∪ q.2) := hpw.1 q hq
        have hdisj_C : Disjoint C (q.1 ∪ q.2) := Disjoint.mono_left hC_sub_union hdisj_pq
        rcases hS q (List.mem_cons_of_mem _ hq) with hq1 | hq2
        · left
          rw [Finset.subset_sdiff]
          exact ⟨hq1, (Disjoint.mono_right Finset.subset_union_left hdisj_C).symm⟩
        · right
          rw [Finset.subset_sdiff]
          exact ⟨hq2, (Disjoint.mono_right Finset.subset_union_right hdisj_C).symm⟩
      have hrec := ih hpw.2 hrest_card (S \ C) hrest_cov
      have hsplit : (S \ C).card + C.card = S.card := Finset.card_sdiff_add_card_eq_card hCS
      simp only [totalDemand, List.map_cons, List.sum_cons] at hrec ⊢
      omega
  exact haux U hcov

private theorem batchBallLoop_spec (Hres : Graph) {X : Finset ℕ}
    {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, Hres.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L)
    (remPairs : List (Finset ℕ × Finset ℕ))
    (hvalid : RouteTerminalPairs X remPairs)
    (hfar : ∀ p ∈ remPairs, ∀ a ∈ p.1, ∀ b' ∈ p.2, ∀ es,
      IsEdgeWalkIn Hres X a b' es → 2 * routeH Δ b * L < es.length)
    (U : Finset ℕ) (hUX : U ⊆ X) (hU_small : 8 * U.card < 5 * X.card)
    (hU_cut : 16 * b * Hres.cutIn X U ≤ U.card)
    (cost : ℕ) :
    let res := batchBallLoop (adjOf Hres X) X b (routeH Δ b) L remPairs U (X \ U) cost
    res.1 ⊆ X ∧
    U ⊆ res.1 ∧
    8 * res.1.card < 5 * X.card ∧
    16 * b * Hres.cutIn X res.1 ≤ res.1.card ∧
    (4 * res.1.card ≥ X.card ∨ ∀ p ∈ remPairs, p.1 ⊆ res.1 ∨ p.2 ⊆ res.1) ∧
    res.2 ≤ cost + remPairs.length * (8 * (X.card + (Hres.inside X).length + 1) + 1) + 1 := by
  induction remPairs generalizing U cost with
  | nil =>
    simp only [batchBallLoop, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨hUX, Finset.Subset.refl _, hU_small, hU_cut, Or.inr (by simp), by omega⟩
  | cons ab rest ih =>
    rcases ab with ⟨A', B'⟩
    simp only [batchBallLoop]
    by_cases hbig : 4 * U.card ≥ X.card
    · simp only [hbig, ↓reduceIte]
      exact ⟨hUX, Finset.Subset.refl _, hU_small, hU_cut, Or.inl trivial, by omega⟩
    · simp only [hbig, ↓reduceIte]
      have hrest_valid : RouteTerminalPairs X rest :=
        ⟨fun q hq => hvalid.1 q (List.mem_cons_of_mem _ hq), (List.pairwise_cons.mp hvalid.2).2⟩
      have hrest_far : ∀ p ∈ rest, ∀ a ∈ p.1, ∀ b' ∈ p.2, ∀ es,
          IsEdgeWalkIn Hres X a b' es → 2 * routeH Δ b * L < es.length :=
        fun p hp => hfar p (List.mem_cons_of_mem _ hp)
      have hA'X : A' ⊆ X := (hvalid.1 (A', B') List.mem_cons_self).1
      have hB'X : B' ⊆ X := (hvalid.1 (A', B') List.mem_cons_self).2.1
      set S := A' ∩ (X \ U)
      set T := B' ∩ (X \ U)
      by_cases hemp : S = ∅ ∨ T = ∅
      · simp only [eq_true hemp, ↓reduceIte]
        have hrec := ih hrest_valid hrest_far U hUX hU_small hU_cut (cost + 1)
        rcases hrec with ⟨h1, h2, h3, h4, h5, h6⟩
        refine ⟨h1, h2, h3, h4, ?_, ?_⟩
        · rcases h5 with h5 | h5
          · exact Or.inl h5
          · right
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · rcases hemp with hS0 | hT0
              · left
                intro x hx
                by_contra hxU
                have hxS : x ∈ S := Finset.mem_inter.mpr
                  ⟨hx, Finset.mem_sdiff.mpr ⟨hA'X hx, fun hu => hxU (h2 hu)⟩⟩
                rw [hS0] at hxS
                exact Finset.notMem_empty _ hxS
              · right
                intro x hx
                by_contra hxU
                have hxT : x ∈ T := Finset.mem_inter.mpr
                  ⟨hx, Finset.mem_sdiff.mpr ⟨hB'X hx, fun hu => hxU (h2 hu)⟩⟩
                rw [hT0] at hxT
                exact Finset.notMem_empty _ hxT
            · exact h5 p hp
        · simp only [List.length_cons]
          have hmul : (rest.length + 1) * (8 * (X.card + (Hres.inside X).length + 1) + 1) =
              rest.length * (8 * (X.card + (Hres.inside X).length + 1) + 1) +
                (8 * (X.card + (Hres.inside X).length + 1) + 1) := by ring
          omega
      · simp only [eq_false hemp, ↓reduceIte]
        rw [not_or] at hemp
        have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp.1
        have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp.2
        have hVsubX : X \ U ⊆ X := Finset.sdiff_subset
        have hdegV : ∀ v ∈ X \ U, Hres.degIn (X \ U) v ≤ Δ :=
          fun v hv => le_trans (degIn_mono hVsubX v) (hdeg v (hVsubX hv))
        have hcardV : (X \ U).card < 2 ^ L :=
          lt_of_le_of_lt (Finset.card_le_card hVsubX) hcard
        have hfarV : ∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn Hres (X \ U) s t es →
            2 * routeH Δ b * L < es.length := by
          intro s hs t ht es hw
          exact hfar (A', B') List.mem_cons_self s (Finset.mem_inter.mp hs).1
            t (Finset.mem_inter.mp ht).1 es (hw.mono hVsubX)
        have hball := growBall_spec Hres hVsubX Finset.inter_subset_right Finset.inter_subset_right
          hSne hTne hΔ hb hL hdegV hcardV hfarV
        set br := growBall (adjOf Hres X) (X \ U) S T b (routeH Δ b) L with hbr_def
        rcases hball with ⟨hB_subV, hB_cov, hB_half, hB_cut, hB_cost⟩
        change br.ball ⊆ X \ U at hB_subV
        change 2 * br.ball.card ≤ (X \ U).card at hB_half
        change 16 * b * Hres.cutIn (X \ U) br.ball ≤ br.ball.card at hB_cut
        change br.cost ≤ 8 * (X.card + (Hres.inside X).length + 1) at hB_cost
        have hU'_subX : U ∪ br.ball ⊆ X :=
          Finset.union_subset hUX (le_trans hB_subV hVsubX)
        have hdisj_UB : Disjoint U br.ball :=
          Disjoint.mono_right hB_subV disjoint_sdiff_self_right
        have hU'_card : (U ∪ br.ball).card = U.card + br.ball.card :=
          Finset.card_union_of_disjoint hdisj_UB
        have hXU_card : (X \ U).card + U.card = X.card := Finset.card_sdiff_add_card_eq_card hUX
        have hU'_small : 8 * (U ∪ br.ball).card < 5 * X.card := by omega
        have hU'_cut : 16 * b * Hres.cutIn X (U ∪ br.ball) ≤ (U ∪ br.ball).card := by
          have hcu := cutIn_union_le Hres hUX hB_subV
          have hm := Nat.mul_le_mul_left (16 * b) hcu
          rw [Nat.mul_add] at hm
          omega
        have hsdiff_eq : (X \ U) \ br.ball = X \ (U ∪ br.ball) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
        rw [hsdiff_eq]
        have hrec := ih hrest_valid hrest_far (U ∪ br.ball) hU'_subX hU'_small hU'_cut
          (cost + br.cost + 1)
        rcases hrec with ⟨h1, h2, h3, h4, h5, h6⟩
        refine ⟨h1, le_trans Finset.subset_union_left h2, h3, h4, ?_, ?_⟩
        · rcases h5 with h5 | h5
          · exact Or.inl h5
          · right
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · rcases hB_cov with hSB | hTB
              · left
                intro x hx
                apply h2
                by_cases hxU : x ∈ U
                · exact Finset.mem_union_left _ hxU
                · exact Finset.mem_union_right _ (hSB (Finset.mem_inter.mpr
                    ⟨hx, Finset.mem_sdiff.mpr ⟨hA'X hx, hxU⟩⟩))
              · right
                intro x hx
                apply h2
                by_cases hxU : x ∈ U
                · exact Finset.mem_union_left _ hxU
                · exact Finset.mem_union_right _ (hTB (Finset.mem_inter.mpr
                    ⟨hx, Finset.mem_sdiff.mpr ⟨hB'X hx, hxU⟩⟩))
            · exact h5 p hp
        · simp only [List.length_cons]
          have hmul : (rest.length + 1) * (8 * (X.card + (Hres.inside X).length + 1) + 1) =
              rest.length * (8 * (X.card + (Hres.inside X).length + 1) + 1) +
                (8 * (X.card + (Hres.inside X).length + 1) + 1) := by ring
          omega

/-! ### Main specification of `runBatch` -/

/-- **`runBatch` specification.**
On a graph `(G, X)` of maximum degree `≤ Δ`, `|X| < 2^L`, `b ≥ 2`, and valid terminal pairs
with positive total demand `D_dem = totalDemand pairs`, `runBatch` returns either:
* `BatchOutcome.matched perPairPaths remPairs`: pairwise vertex-disjoint simple walks in `G[X]`
  of length `≤ d`, partial matchings `M_i ⊆ A_i × B_i` whose removal leaves valid pairs
  `remPairs` with `H_batch * totalDemand remPairs ≤ (H_batch - 1) * totalDemand pairs`; or
* `BatchOutcome.cut U`: a cut `U ⊆ X` in the **original** host `G[X]` satisfying
  `b * G.cutIn X U ≤ min U.card (X \ U).card`, `D_dem ≤ 2 * U.card`, and
  `D_dem ≤ 2 * (X \ U).card`.

In either outcome, `res.cost ≤ 20 * pairs.length * (X.card + (G.inside X).length + 1) * (d + 1)`. -/
theorem runBatch_spec (G : Graph) {X : Finset ℕ}
    {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 2 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ)
    (hcard : X.card < 2 ^ L)
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs)
    (hdem_pos : 1 ≤ totalDemand pairs) :
    let res := runBatch G X Δ b L pairs
    let d := routeD Δ b L
    let Hbatch := routeHBatch Δ b L
    (∀ perPairPaths remPairs, res.outcome = BatchOutcome.matched perPairPaths remPairs →
      perPairPaths.length = pairs.length ∧
      remPairs.length = pairs.length ∧
      (∀ p ∈ perPairPaths.flatten, p.2.length ≤ d ∧ IsSimpleWalkIn G X p.1.1 p.1.2 p.2) ∧
      (perPairPaths.flatten.Pairwise fun p q =>
        Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) ∧
      (∀ i (hi : i < pairs.length),
        let (A, B) := pairs[i]'hi
        let ps := perPairPaths.getD i []
        let (A', B') := remPairs.getD i (∅, ∅)
        (∀ q ∈ ps, q.1.1 ∈ A ∧ q.1.2 ∈ B ∧ q.2.length ≤ d ∧ IsSimpleWalkIn G X q.1.1 q.1.2 q.2) ∧
        (ps.map fun q => q.1.1).Nodup ∧
        (ps.map fun q => q.1.2).Nodup ∧
        A' = A \ (ps.map fun q => q.1.1).toFinset ∧
        B' = B \ (ps.map fun q => q.1.2).toFinset ∧
        A'.card + ps.length = A.card ∧
        B'.card + ps.length = B.card) ∧
      RouteTerminalPairs X remPairs ∧
      totalDemand remPairs + perPairPaths.flatten.length = totalDemand pairs ∧
      Hbatch * totalDemand remPairs ≤ (Hbatch - 1) * totalDemand pairs) ∧
    (∀ U, res.outcome = BatchOutcome.cut U →
      U ⊆ X ∧
      b * G.cutIn X U ≤ min U.card (X \ U).card ∧
      totalDemand pairs ≤ 2 * U.card ∧
      totalDemand pairs ≤ 2 * (X \ U).card) ∧
    res.cost ≤ 20 * pairs.length * (X.card + (G.inside X).length + 1) * (d + 1) := by
  unfold runBatch
  dsimp only
  set d := routeD Δ b L
  set Hbatch := routeHBatch Δ b L
  have hb1 : 1 ≤ b := by omega
  have hpairs_pos : 1 ≤ pairs.length := by
    cases pairs with
    | nil => simp [totalDemand] at hdem_pos
    | cons _ _ => simp
  have hbr := batchRoutePairs_spec G d pairs hvalid X (Finset.Subset.refl _)
  set br := batchRoutePairs (adjOf G X) d pairs X with hbr_def
  rcases hbr with ⟨hbr_len1, hbr_len2, hbr_cnt, hbr_subX, hbr_rem, hbr_verts_sub, hbr_walk,
    hbr_disj, hbr_idx, hbr_valid, hbr_dem, hbr_cost⟩
  change br.cost ≤ pairs.length * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) at hbr_cost
  by_cases hsucc : br.routedCount * Hbatch ≥ totalDemand pairs
  · simp only [eq_true hsucc, ↓reduceIte]
    refine ⟨?_, (fun _ h => by cases h), ?_⟩
    · intro perPairPaths remPairs hEq
      cases hEq
      have hH_ge : 2 ≤ Hbatch := routeHBatch_ge_two hΔ hb1
      have hprog : Hbatch * totalDemand br.remPairs ≤ (Hbatch - 1) * totalDemand pairs := by
        have h1 : Hbatch * totalDemand br.remPairs + Hbatch * br.routedCount =
            Hbatch * totalDemand pairs := by
          rw [← Nat.mul_add, hbr_dem]
        have h2 : Hbatch * br.routedCount = br.routedCount * Hbatch := Nat.mul_comm _ _
        have h3 : (Hbatch - 1) * totalDemand pairs + totalDemand pairs =
            Hbatch * totalDemand pairs := by
          have : Hbatch = (Hbatch - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
        omega
      refine ⟨hbr_len1, hbr_len2, hbr_walk, hbr_disj, ?_, hbr_valid, hbr_cnt ▸ hbr_dem, hprog⟩
      intro i hi
      have hi' := hbr_idx i hi
      exact ⟨hi'.1, hi'.2.1, hi'.2.2.1, hi'.2.2.2.1, hi'.2.2.2.2.1, hi'.2.2.2.2.2.1,
        hi'.2.2.2.2.2.2.1⟩
    · have h1 : pairs.length ≤ pairs.length * (X.card + (G.inside X).length + 1) * (d + 1) := by
        have hge : 1 ≤ (X.card + (G.inside X).length + 1) * (d + 1) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
        calc pairs.length = pairs.length * 1 := (Nat.mul_one _).symm
          _ ≤ pairs.length * ((X.card + (G.inside X).length + 1) * (d + 1)) :=
              Nat.mul_le_mul_left _ hge
          _ = pairs.length * (X.card + (G.inside X).length + 1) * (d + 1) := by ring
      have h2 : 1 ≤ pairs.length * (X.card + (G.inside X).length + 1) * (d + 1) := le_trans hpairs_pos h1
      have h3 : pairs.length * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) ≤
          8 * (pairs.length * (X.card + (G.inside X).length + 1) * (d + 1)) := by
        have hexp : pairs.length * (7 * (X.card + (G.inside X).length + 1) * (d + 1) + 1) =
            7 * (pairs.length * (X.card + (G.inside X).length + 1) * (d + 1)) + pairs.length := by ring
        omega
      have hrhs20 : 20 * pairs.length * (X.card + (G.inside X).length + 1) * (d + 1) =
          20 * (pairs.length * (X.card + (G.inside X).length + 1) * (d + 1)) := by ring
      omega
  · simp only [eq_false hsucc, ↓reduceIte]
    have hfail : br.routedCount * Hbatch < totalDemand pairs := Nat.lt_of_not_ge hsucc
    set Hres : Graph := ⟨G.n, G.inside br.remVerts⟩
    have hHres_inside : Hres.inside X = G.inside br.remVerts := by
      change (G.inside br.remVerts).filter (fun e => decide (e.1 ∈ X) && decide (e.2 ∈ X)) =
        G.inside br.remVerts
      unfold Graph.inside
      rw [List.filter_filter]
      apply List.filter_congr
      intro e _
      by_cases h1 : e.1 ∈ br.remVerts <;> by_cases h2 : e.2 ∈ br.remVerts
      · simp [h1, h2, hbr_subX h1, hbr_subX h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hHres_len_le : (Hres.inside X).length ≤ (G.inside X).length := by
      rw [hHres_inside]
      unfold Graph.inside
      apply length_filter_le_of_imp
      intro e _ he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he ⊢
      exact ⟨hbr_subX he.1, hbr_subX he.2⟩
    have hHres_deg : ∀ v ∈ X, Hres.degIn X v ≤ Δ := by
      intro v hv
      have heq : Hres.degIn X v = G.degIn br.remVerts v := by
        unfold Graph.degIn
        rw [hHres_inside]
      rw [heq]
      exact le_trans (degIn_mono hbr_subX v) (hdeg v hv)
    have hHres_far : ∀ p ∈ br.remPairs, ∀ a ∈ p.1, ∀ b' ∈ p.2, ∀ es,
        IsEdgeWalkIn Hres X a b' es → 2 * routeH Δ b * L < es.length := by
      intro p hp a ha b' hb' es hw
      rw [List.mem_iff_getElem] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      have hi_p : i < pairs.length := by omega
      have hi_spec := hbr_idx i hi_p
      have hgetD : br.remPairs.getD i (∅, ∅) = br.remPairs[i]'hi :=
        List.getD_eq_getElem _ _ hi
      rw [hgetD] at hi_spec
      have hdisj_ab : Disjoint (br.remPairs[i]'hi).1 (br.remPairs[i]'hi).2 :=
        hi_spec.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨es', hlen', hw'⟩ := hw.of_inside_graph
      have hw_act : IsEdgeWalkIn G br.remVerts a b' es' := hw'.mono Finset.inter_subset_right
      have hne_ab : a ≠ b' := fun hEq => Finset.disjoint_left.mp hdisj_ab ha (hEq ▸ hb')
      have hes'_ne : es' ≠ [] := by
        intro hnil
        rw [hnil] at hw_act
        cases hw_act.1
        exact hne_ab rfl
      cases hes'_eq : es' with
      | nil => exact absurd hes'_eq hes'_ne
      | cons e0 es_tl =>
        rw [hes'_eq] at hw_act
        have hin0 : insideB br.remVerts (edgeAt G.edges e0) = true :=
          hw_act.2 e0 List.mem_cons_self
        unfold insideB at hin0
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin0
        have ha_act : a ∈ br.remVerts := by
          cases hw_act.1 with
          | cons _ hend _ =>
            rcases hend with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact h1 ▸ hin0.1
            · exact h2 ▸ hin0.2
        have hb'_act : b' ∈ br.remVerts :=
          hw_act.walkVerts_subset ha_act b' hw_act.1.mem_walkVerts_end
        have hgt := hi_spec.2.2.2.2.2.2.2.2.2.2.2 a ha b' hb' (e0 :: es_tl) hw_act ha_act hb'_act
        rw [← routeD_eq_two_mul_routeH]
        have hlen_eq : (e0 :: es_tl).length = es.length := hes'_eq ▸ hlen'
        change d < es.length
        omega
    have hX_pos : 1 ≤ X.card := by
      have := two_mul_totalDemand_le hvalid
      omega
    have hball_loop := batchBallLoop_spec Hres hΔ hb1 hL hHres_deg hcard br.remPairs hbr_valid
      hHres_far ∅ (Finset.empty_subset _) (by simp only [Finset.card_empty, Nat.mul_zero]; omega)
      (by simp [Graph.cutIn])
      (br.cost + pairs.length + 1 + (X.card + 2 * (G.inside X).length + 1))
    rw [Finset.sdiff_empty] at hball_loop
    set cutRes := batchBallLoop (adjOf Hres X) X b (routeH Δ b) L br.remPairs ∅ X
      (br.cost + pairs.length + 1 + (X.card + 2 * (G.inside X).length + 1))
    rcases hball_loop with ⟨hUX, _, hU_small, hU_res_cut, hU_large, hcut_cost⟩
    refine ⟨(fun _ _ h => by cases h), ?_, ?_⟩
    · intro U hEq
      cases hEq
      have h2D_le_X : 2 * totalDemand pairs ≤ X.card := two_mul_totalDemand_le hvalid
      have hH_ge : 2 ≤ Hbatch := routeHBatch_ge_two hΔ hb1
      have h2p_lt_D : 2 * br.routedCount < totalDemand pairs := by
        have : 2 * br.routedCount ≤ br.routedCount * Hbatch := by
          calc 2 * br.routedCount = br.routedCount * 2 := Nat.mul_comm _ _
            _ ≤ br.routedCount * Hbatch := Nat.mul_le_mul_left _ hH_ge
        omega
      have hD_le_2U : totalDemand pairs ≤ 2 * cutRes.1.card := by
        rcases hU_large with h4U | hcov
        · omega
        · have hge := card_union_covered_ge br.remPairs hbr_valid.2
            (fun p hp => (hbr_valid.1 p hp).2.2.1) hcov
          omega
      have hXU_card : (X \ cutRes.1).card + cutRes.1.card = X.card :=
        Finset.card_sdiff_add_card_eq_card hUX
      have hD_le_2XU : totalDemand pairs ≤ 2 * (X \ cutRes.1).card := by omega
      -- Restore `F_del`:
      have hvol_del : G.volIn X (X \ br.remVerts) ≤ Δ * (d + 1) * br.routedCount := by
        have hv1 : G.volIn X (X \ br.remVerts) ≤ Δ * (X \ br.remVerts).card :=
          volIn_le_mul_card Finset.sdiff_subset hdeg
        have hsdiff_eq : X \ br.remVerts = routedVerts G br.perPairPaths.flatten := by
          rw [hbr_rem, Finset.sdiff_sdiff_eq_self hbr_verts_sub]
        have hrcard : (routedVerts G br.perPairPaths.flatten).card ≤ (d + 1) * br.routedCount := by
          rw [hbr_cnt]
          exact card_routedVerts_le G d br.perPairPaths.flatten (fun p hp => (hbr_walk p hp).1)
        calc G.volIn X (X \ br.remVerts)
            ≤ Δ * (X \ br.remVerts).card := hv1
          _ = Δ * (routedVerts G br.perPairPaths.flatten).card := by rw [hsdiff_eq]
          _ ≤ Δ * ((d + 1) * br.routedCount) := Nat.mul_le_mul_left Δ hrcard
          _ = Δ * (d + 1) * br.routedCount := by ring
      have h16b_del : 16 * b * G.volIn X (X \ br.remVerts) < totalDemand pairs := by
        have h1 : 16 * b * G.volIn X (X \ br.remVerts) ≤ 16 * b * (Δ * (d + 1) * br.routedCount) :=
          Nat.mul_le_mul_left (16 * b) hvol_del
        have h2 : 16 * b * (Δ * (d + 1) * br.routedCount) = br.routedCount * Hbatch := by
          unfold Hbatch routeHBatch routeBatchH; ring
        omega
      have hcut_restore : G.cutIn X cutRes.1 ≤ Hres.cutIn X cutRes.1 + G.volIn X (X \ br.remVerts) :=
        cutIn_le_cutIn_restrict_add_volIn G hbr_subX
      have h16b_cut : 16 * b * G.cutIn X cutRes.1 < 3 * cutRes.1.card := by
        have hm := Nat.mul_le_mul_left (16 * b) hcut_restore
        rw [Nat.mul_add] at hm
        omega
      have hcut_le_min : b * G.cutIn X cutRes.1 ≤ min cutRes.1.card (X \ cutRes.1).card := by
        rw [le_min_iff]
        constructor
        · have hmul : 16 * (b * G.cutIn X cutRes.1) = 16 * b * G.cutIn X cutRes.1 := by ring
          omega
        · have hmul : 16 * (b * G.cutIn X cutRes.1) = 16 * b * G.cutIn X cutRes.1 := by ring
          omega
      exact ⟨hUX, hcut_le_min, hD_le_2U, hD_le_2XU⟩
    · -- Cost bound for cut branch:
      set S0 := X.card + (G.inside X).length + 1
      have hS0_pos : 1 ≤ S0 := by omega
      have hd1_pos : 1 ≤ d + 1 := Nat.succ_pos _
      have hterm_ge_S0 : S0 ≤ pairs.length * S0 * (d + 1) := by
        calc S0 = 1 * S0 * 1 := by ring
          _ ≤ pairs.length * S0 * (d + 1) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right S0 hpairs_pos) hd1_pos
      have hterm_ge_k : pairs.length ≤ pairs.length * S0 * (d + 1) := by
        calc pairs.length = pairs.length * 1 * 1 := by ring
          _ ≤ pairs.length * S0 * (d + 1) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left pairs.length hS0_pos) hd1_pos
      have hterm_ge_kS0 : pairs.length * S0 ≤ pairs.length * S0 * (d + 1) :=
        Nat.le_mul_of_pos_right _ hd1_pos
      have hbr_c : br.cost ≤ 8 * (pairs.length * S0 * (d + 1)) := by
        have hexp : pairs.length * (7 * S0 * (d + 1) + 1) =
            7 * (pairs.length * S0 * (d + 1)) + pairs.length := by ring
        omega
      have hball_c : br.remPairs.length * (8 * (X.card + (Hres.inside X).length + 1) + 1) ≤
          9 * (pairs.length * S0 * (d + 1)) := by
        have h1 : 8 * (X.card + (Hres.inside X).length + 1) + 1 ≤ 9 * S0 := by omega
        calc br.remPairs.length * (8 * (X.card + (Hres.inside X).length + 1) + 1)
            = pairs.length * (8 * (X.card + (Hres.inside X).length + 1) + 1) := by rw [hbr_len2]
          _ ≤ pairs.length * (9 * S0) := Nat.mul_le_mul_left _ h1
          _ = 9 * (pairs.length * S0) := by ring
          _ ≤ 9 * (pairs.length * S0 * (d + 1)) := Nat.mul_le_mul_left 9 hterm_ge_kS0
      have hbuild_c : X.card + 2 * (G.inside X).length + 1 ≤ 2 * (pairs.length * S0 * (d + 1)) := by
        have h1 : X.card + 2 * (G.inside X).length + 1 ≤ 2 * S0 := by omega
        omega
      have hrhs_eq : 20 * pairs.length * S0 * (d + 1) = 20 * (pairs.length * S0 * (d + 1)) := by ring
      omega

end MinCostFlow.ExpanderDecomp
