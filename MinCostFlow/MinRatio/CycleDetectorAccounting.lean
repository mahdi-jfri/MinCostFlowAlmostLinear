module

public import MinCostFlow.Chain.CyclePathRep
import MinCostFlow.MinRatio.PathCancellationAccounting
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Ring

/-!
# Accounting for a cycle's tree paths and explicit edges

Algorithm 2 (page 29) adds the absolute normalized circulation to the
detector. On tree edges the cancellation-free endpoint paths give
this amount. On off-tree edges the explicit occurrences are summed
before taking the absolute value. The two contributions have
disjoint supports.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

private theorem treePath_zero_offTree {F : MGraph} {p : ℕ × ℕ}
    (hp : F.Connected p.1 p.2) {e : ℕ} (he : e ∉ F.E) :
    walkFlow (F.forestPath p.1 p.2) e = 0 := by
  apply walkFlow_eq_zero_of_not_mem
  intro hw
  rw [walkEdges, List.mem_toFinset, List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  exact he (MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath hp) x hx)

/-- The cycle from Algorithm 1 has a route of the same bounded size
whose detector contribution is the exact absolute normalized
coordinate. Each explicit edge uses its net signed occurrence count. -/
theorem findCycle_lift_detector_account {cfg : Alg2Config} (hV : cfg.ValidNoHidden) (s : Alg2State cfg)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ s.chain)
    (hFresh : FreshInv s.extG (s.chain.G 0) s.extToInt s.intToExt s.nextFresh) :
    let C := liftEdgeFn s.extG s.extToInt (algorithm1_findCycle s.chain).1
    let parts := Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1
    ∃ (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)),
      edges.length ≤ parts ∧ (∀ x ∈ edges, x.1 ∈ s.extG.E \ s.extTree.E) ∧
      paths.length ≤ 2 * parts ∧ (∀ p ∈ paths, s.extTree.Connected p.1 p.2) ∧
      (∀ e, C e = (edges.map (fun x => walkFlow [x] e)).sum +
        (paths.map (fun p => walkFlow (s.extTree.forestPath p.1 p.2) e)).sum) ∧
      ∀ (e : ℕ) (k : ℝ),
        |k * C e| =
          |k * (edges.map (fun x => walkFlow [x] e)).sum| +
          (paths.map (fun p => |k * walkFlow (s.extTree.forestPath p.1 p.2) e|)).sum := by
  dsimp only
  obtain ⟨edges, paths, he, heMem, hp, hc, hf⟩ := findCycle_tree_path_rep hV s hInv hFresh
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hT hV.hMWU hV.hEmb hV.hγM₀ hV.hγk
  have hSub := s.chain.toTreeChain.forestsAreSubgraphs_of_holds hTH.1
  have hF := extTree_isForest s (hFresh.isValid_iff.mp hInv.hG0Valid) hFresh
    (s.chain.toTreeChain.chainTree_isForest hTH.1 hSub)
  obtain ⟨route, hlen, hr, hroute, hdet⟩ := pathCancel_route_account s.extTree hF paths hc
  refine ⟨edges, route, he, heMem, hlen ▸ hp, hr, fun e => (hroute e).symm ▸ hf e, ?_⟩
  intro e k
  rw [hf e, hdet e k]
  by_cases het : e ∈ s.extTree.E
  · have hzero : (edges.map (fun x => walkFlow [x] e)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      apply walkFlow_eq_zero_of_not_mem
      have hn : x.1 ≠ e := fun h => (Finset.mem_sdiff.mp (heMem x hx)).2 (h.symm ▸ het)
      simp [walkEdges, Ne.symm hn]
    simp [hzero]
  · have hzero : (paths.map (fun p => walkFlow (s.extTree.forestPath p.1 p.2) e)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact treePath_zero_offTree (hc x hx) het
    simp [hzero]

/-- Grouping the explicit occurrences of an edge gives its signed
coefficient as a difference of two ordinary counts. -/
theorem explicitEdge_signed_count (edges : List (ℕ × Bool)) (e : ℕ) :
    (edges.map (fun x => walkFlow [x] e)).sum =
      ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ) : ℤ) := by
  induction edges with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    obtain ⟨name, dir⟩ := x
    by_cases he : name = e
    · subst name
      cases dir <;>
        simp [walkFlow] <;> ring
    · have htrue : (name, dir) ≠ (e, true) := fun h => he (congrArg Prod.fst h)
      have hfalse : (name, dir) ≠ (e, false) := fun h => he (congrArg Prod.fst h)
      simp [walkFlow, he, List.count_cons_of_ne htrue, List.count_cons_of_ne hfalse]

/-- The net signed count has magnitude at most the explicit
list length. This bound lets the grouped increment use a word-sized
count when the list length fits. -/
theorem explicitEdge_signed_count_bound (edges : List (ℕ × Bool)) (e : ℕ) :
    |((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ))| ≤ (edges.length : ℤ) := by
  have h₁ : edges.count (e, true) ≤ edges.length := List.count_le_length
  have h₂ : edges.count (e, false) ≤ edges.length := List.count_le_length
  exact abs_le.mpr (by omega)

/-- An explicit route that fits in a machine word also has a
word-sized magnitude for every grouped count. -/
theorem explicitEdge_signed_count_natAbs_le (edges : List (ℕ × Bool)) (e : ℕ) :
    ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)).natAbs ≤ edges.length := by
  exact_mod_cast (show
    (((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)).natAbs : ℤ) ≤
      (edges.length : ℤ) by
    rw [Int.natCast_natAbs]
    exact explicitEdge_signed_count_bound edges e)

/-- A prefix scan can accumulate positive and negative counts separately.
Appending a scanned row increments only its matching direction counter. -/
theorem explicitEdge_count_snoc (scanned : List (ℕ × Bool)) (row : ℕ × Bool)
    (e : ℕ) (dir : Bool) :
    (scanned ++ [row]).count (e, dir) =
      scanned.count (e, dir) + if row = (e, dir) then 1 else 0 := by
  rw [List.count_append]
  by_cases h : row = (e, dir)
  · subst row
    simp
  · rw [ite_eq_right h, List.count_cons_of_ne h]
    rfl

/-- A row is processed once per edge by using the first occurrence of
its name, regardless of traversal direction. -/
theorem explicitEdge_unique_first (edges : List (ℕ × Bool)) (e : ℕ)
    (he : e ∈ edges.map Prod.fst) :
    ∃! i : ℕ, ∃ hi : i < edges.length,
      edges[i].1 = e ∧ ∀ j : ℕ, ∀ hj : j < i,
        (edges[j]'(lt_trans hj hi)).1 ≠ e := by
  have hex : ∃ i : ℕ, ∃ hi : i < edges.length, edges[i].1 = e := by
    obtain ⟨row, hr, hn⟩ := List.mem_map.mp he
    obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp hr
    exact ⟨i, hi, congrArg Prod.fst hrow |>.trans hn⟩
  let i := Nat.find hex
  obtain ⟨hi, hname⟩ := Nat.find_spec hex
  have hfirst : ∀ j : ℕ, ∀ hj : j < i, (edges[j]'(lt_trans hj hi)).1 ≠ e := by
    intro j hj hn
    exact (Nat.find_min hex hj) ⟨lt_trans hj hi, hn⟩
  refine ⟨i, ⟨hi, hname, hfirst⟩, ?_⟩
  intro j hj
  obtain ⟨hj, hnamej, hfirstj⟩ := hj
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt (fun h => hfirstj i h hname)
  · exact Nat.find_min' hex ⟨hj, hnamej⟩

/-- On an off-tree edge, applying the multiplier to its net count
gives both the signed increment and the absolute increment used by
Algorithm 2 (page 29). -/
theorem offTree_cycle_increment_of_signed_count {F : MGraph} {e : ℕ}
    (he : e ∉ F.E) (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ))
    (hc : ∀ p ∈ paths, F.Connected p.1 p.2) (C : ℕ → ℝ)
    (hC : C e = (edges.map (fun x => walkFlow [x] e)).sum +
      (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum) (k : ℝ) :
    let delta := k * ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ) : ℤ)
    k * C e = delta ∧ |k * C e| = |delta| := by
  have hzero : (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum = 0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact treePath_zero_offTree (hc p hp) he
  rw [hC, hzero, add_zero, explicitEdge_signed_count]
  exact ⟨rfl, rfl⟩

private theorem sum_weighted_path_contributions (G F : MGraph) (length : ℕ → ℝ)
    (paths : List (ℕ × ℕ)) :
    (∑ e ∈ G.E, length e * (paths.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum) =
      (paths.map (fun p => G.lnorm length (walkFlow (F.forestPath p.1 p.2)))).sum := by
  induction paths with
  | nil => simp
  | cons p paths ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih, MGraph.lnorm]

/-- Exact absolute accounting also gives the cycle length as one sum
of grouped explicit edge contributions and one sum of path lengths. -/
theorem cycleLength_of_detector_account {G F : MGraph} (hsub : G.IsSubgraph F)
    (length C : ℕ → ℝ) (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ))
    (heG : ∀ x ∈ edges, x.1 ∈ G.E)
    (hc : ∀ p ∈ paths, F.Connected p.1 p.2)
    (hdet : ∀ e ∈ G.E, |C e| =
      |(edges.map (fun x => walkFlow [x] e)).sum| +
      (paths.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum) :
    G.lnorm length C =
      (∑ e ∈ walkEdges edges, length e * |(edges.map (fun x => walkFlow [x] e)).sum|) +
      (paths.map (fun p => walkLength length (F.forestPath p.1 p.2))).sum := by
  unfold MGraph.lnorm
  have hsum : (∑ e ∈ G.E, length e * |C e|) =
      ∑ e ∈ G.E, (length e * |(edges.map (fun x => walkFlow [x] e)).sum| +
        length e * (paths.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hdet e he, mul_add]
  have hedgeSub : walkEdges edges ⊆ G.E := by
    intro e he
    rw [walkEdges, List.mem_toFinset, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact heG x hx
  have hexp :
      (∑ e ∈ walkEdges edges, length e * |(edges.map (fun x => walkFlow [x] e)).sum|) =
        ∑ e ∈ G.E, length e * |(edges.map (fun x => walkFlow [x] e)).sum| := by
    apply Finset.sum_subset hedgeSub
    intro e _ he
    have hz : (edges.map (fun x => walkFlow [x] e)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      apply walkFlow_eq_zero_of_not_mem
      have hn : e ≠ x.1 := fun heq => he (heq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem hx))
      simp [walkEdges, hn]
    simp [hz]
  rw [hsum, Finset.sum_add_distrib, sum_weighted_path_contributions, hexp]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hwalk := MGraph.isWalk_forestPath (hc p hp)
  apply (walkLength_eq_sum_of_subset ?_).symm
  intro e he
  rw [walkEdges, List.mem_toFinset, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  exact hsub.2.1 (MGraph.isWalk_edges_mem hwalk x hx)

end MinCostFlow.MinRatio
