module

public import MinCostFlow.Basic.Forest
import MinCostFlow.LSF.Walks
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic.Linarith

/-!
# Canceling opposite traversals in tree-path routing

Algorithm 2 (page 29) adds the absolute change of the circulation to
each detector account. Two paths can traverse an edge in opposite
directions. Swapping the destination endpoints of the two paths
preserves their signed flow. If they traverse an edge in opposite
directions, the swapped pair also uses strictly fewer steps.
-/

public section

namespace MinCostFlow.MinRatio

open LSF

private theorem isWalk_cut_edge {F : MGraph} {a b : ℕ} {p q : List (ℕ × Bool)}
    {x : ℕ × Bool} (hw : F.IsWalk a b (p ++ x :: q)) :
    F.IsWalk a (F.src x) p ∧ F.IsWalk (F.dst x) b q := by
  induction p generalizing a with
  | nil =>
    cases hw with
    | cons _ hs hq =>
      subst a
      exact ⟨.nil _, hq⟩
  | cons y ys ih =>
    cases hw with
    | cons he hs hrest =>
      obtain ⟨hp, hq⟩ := ih hrest
      exact ⟨.cons he hs hp, hq⟩

private theorem forestPath_length_le_walk {F : MGraph} (hF : F.IsForest)
    {a b : ℕ} {walk : List (ℕ × Bool)} (hw : F.IsWalk a b walk) :
    (F.forestPath a b).length ≤ walk.length := by
  obtain ⟨p, hp, hs, _⟩ := exists_isPath_of_isWalk hw
  rw [forestPath_eq_of_isPath hF hp]
  have hcard := Finset.card_le_card hs
  rw [walkEdges, List.toFinset_card_of_nodup (isPath_nodup_edges hp), List.length_map] at hcard
  exact hcard.trans (by
    unfold walkEdges
    simpa only [List.length_map] using (walk.map Prod.fst).toFinset_card_le)

private theorem sum_distinct_le_occurrences (length : ℕ → ℝ) (xs : List ℕ)
    (hℓ : ∀ e ∈ xs, 0 ≤ length e) :
    (∑ e ∈ xs.toFinset, length e) ≤ (xs.map length).sum := by
  induction xs with
  | nil => simp
  | cons e rest ih =>
    have hr := ih (fun x hx => hℓ x (List.mem_cons_of_mem _ hx))
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases he : e ∈ rest.toFinset
    · rw [Finset.insert_eq_of_mem he]
      exact hr.trans (le_add_of_nonneg_left (hℓ e List.mem_cons_self))
    · rw [Finset.sum_insert he]
      exact add_le_add le_rfl hr

private theorem weighted_forestPath_le_walk {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 ≤ length e)
    {a b : ℕ} {walk : List (ℕ × Bool)} (hw : F.IsWalk a b walk) :
    walkLength length (F.forestPath a b) ≤ (walk.map (fun x => length x.1)).sum := by
  obtain ⟨p, hp, hsub, _⟩ := exists_isPath_of_isWalk hw
  rw [forestPath_eq_of_isPath hF hp, walkLength_eq_sum_of_isPath length hp]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans ?_
  · intro e he _
    rw [walkEdges, List.mem_toFinset, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact hℓ _ (MGraph.isWalk_edges_mem hw x hx)
  · unfold walkEdges
    simpa only [List.map_map, Function.comp_def] using
      sum_distinct_le_occurrences length (walk.map Prod.fst) (fun e he => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        exact hℓ _ (MGraph.isWalk_edges_mem hw x hx))

private theorem rev_src {F : MGraph} (x : ℕ × Bool) :
    F.src (x.1, !x.2) = F.dst x := by
  cases hx : x.2 <;> simp [MGraph.src, MGraph.dst, hx]

private theorem rev_dst {F : MGraph} (x : ℕ × Bool) :
    F.dst (x.1, !x.2) = F.src x := by
  cases hx : x.2 <;> simp [MGraph.src, MGraph.dst, hx]

private theorem edgeFlow_cancel (x : ℕ × Bool) (e : ℕ) :
    walkFlow [x] e + walkFlow [(x.1, !x.2)] e = 0 := by
  simp only [walkFlow_cons, walkFlow_nil, add_zero]
  by_cases he : x.1 = e <;> cases x.2 <;> simp [he]

/-- Swapping destinations cancels a shared oppositely traversed edge.
The pair still has two connected endpoint pairs and its signed
edgewise flow is unchanged. The total length in edges decreases. -/
theorem pathCancel_swap {F : MGraph} (hF : F.IsForest)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) :
    F.Connected a d ∧ F.Connected c b ∧
    (∀ e, walkFlow (F.forestPath a b) e + walkFlow (F.forestPath c d) e =
      walkFlow (F.forestPath a d) e + walkFlow (F.forestPath c b) e) ∧
    (F.forestPath a d).length + (F.forestPath c b).length <
      (F.forestPath a b).length + (F.forestPath c d).length := by
  obtain ⟨p, q, hpq⟩ := List.mem_iff_append.mp hx
  obtain ⟨r, s, hrs⟩ := List.mem_iff_append.mp hy
  have hW₁ := MGraph.isWalk_forestPath hab
  have hW₂ := MGraph.isWalk_forestPath hcd
  rw [hpq] at hW₁
  rw [hrs] at hW₂
  obtain ⟨hp, hq⟩ := isWalk_cut_edge hW₁
  obtain ⟨hr, hs⟩ := isWalk_cut_edge hW₂
  rw [rev_src] at hr
  rw [rev_dst] at hs
  have had := MGraph.isWalk_append hp hs
  have hcb := MGraph.isWalk_append hr hq
  refine ⟨⟨_, had⟩, ⟨_, hcb⟩, ?_, ?_⟩
  · intro e
    rw [walkFlow_eq_of_isForest hF (MGraph.isWalk_forestPath ⟨_, had⟩) had e,
      walkFlow_eq_of_isForest hF (MGraph.isWalk_forestPath ⟨_, hcb⟩) hcb e,
      hpq, hrs]
    have hseg₁ : x :: q = [x] ++ q := rfl
    have hseg₂ : (x.1, !x.2) :: s = [(x.1, !x.2)] ++ s := rfl
    rw [hseg₁, hseg₂]
    simp only [walkFlow_append]
    have hz := edgeFlow_cancel x e
    linarith only [hz]
  · have h₁ := forestPath_length_le_walk hF had
    have h₂ := forestPath_length_le_walk hF hcb
    rw [hpq, hrs]
    simp only [List.length_append, List.length_cons] at h₁ h₂ ⊢
    omega

/-- A destination swap within a component preserves the signed flow
even when the choice is made from lengths alone. -/
theorem pathCancel_swap_flow {F : MGraph} (hF : F.IsForest)
    {a b c d : ℕ} (hab : F.Connected a b) (hac : F.Connected a c)
    (hcd : F.Connected c d) (e : ℕ) :
    walkFlow (F.forestPath a b) e + walkFlow (F.forestPath c d) e =
      walkFlow (F.forestPath a d) e + walkFlow (F.forestPath c b) e := by
  have h₁ := walkFlow_forestPath_add hF hac (MGraph.connected_trans (MGraph.connected_symm hac) hab) e
  have h₂ := walkFlow_forestPath_add hF hac hcd e
  linarith only [h₁, h₂]

/-- A swap witnessed by an opposite traversal removes at least two
copies of its edge from the total weighted length. Other edges can
have zero weight, so the bound also applies to individual edge counts. -/
theorem pathCancel_weighted_swap_saving {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 ≤ length e)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) :
    walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) + 2 * length x.1 ≤
      walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) := by
  obtain ⟨p, q, hpq⟩ := List.mem_iff_append.mp hx
  obtain ⟨r, s, hrs⟩ := List.mem_iff_append.mp hy
  have hP := forestPath_isPath hF hab
  have hQ := forestPath_isPath hF hcd
  have hW₁ := hP.1
  have hW₂ := hQ.1
  rw [hpq] at hW₁
  rw [hrs] at hW₂
  obtain ⟨hp, hq⟩ := isWalk_cut_edge hW₁
  obtain ⟨hr, hs⟩ := isWalk_cut_edge hW₂
  rw [rev_src] at hr
  rw [rev_dst] at hs
  have had := weighted_forestPath_le_walk hF length hℓ
    (MGraph.isWalk_append hp hs)
  have hcb := weighted_forestPath_le_walk hF length hℓ
    (MGraph.isWalk_append hr hq)
  rw [walkLength_eq_sum_of_isPath length hP, walkLength_eq_sum_of_isPath length hQ]
  have hsumP := List.sum_toFinset length (isPath_nodup_edges hP)
  have hsumQ := List.sum_toFinset length (isPath_nodup_edges hQ)
  unfold walkEdges
  rw [hsumP, hsumQ, hpq, hrs]
  simp only [List.map_map, Function.comp_def, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons] at had hcb ⊢
  linarith only [had, hcb]

/-- Any opposite traversal passes the strict comparison of the
four weighted path lengths used by the machine swap test. -/
theorem pathCancel_weighted_swap {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) :
    walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) <
      walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) := by
  have hs := pathCancel_weighted_swap_saving hF length (fun e he => (hℓ e he).le) hab hcd hx hy
  have hp := hℓ x.1 (MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath hab) x hx)
  linarith only [hs, hp]

private theorem single_edge_weight_length (walk : List (ℕ × Bool)) (e : ℕ) :
    walkLength (fun z => if z = e then 1 else 0) walk = |walkFlow walk e| := by
  classical
  by_cases he : e ∈ walkEdges walk
  · unfold walkLength
    rw [Finset.sum_eq_single e (fun z _ hz => by simp [hz]) (fun h => (h he).elim)]
    simp
  · rw [walkFlow_eq_zero_of_not_mem he, abs_zero]
    unfold walkLength
    apply Finset.sum_eq_zero
    intro z hz
    have hne : z ≠ e := fun h => he (h ▸ hz)
    simp [hne]

/-- An improving swap only removes traversals. On its witness edge
the total absolute coefficient drops by at least two. -/
theorem pathCancel_swap_edge_usage {F : MGraph} (hF : F.IsForest)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) (e : ℕ) :
    |walkFlow (F.forestPath a d) e| + |walkFlow (F.forestPath c b) e| +
        (if x.1 = e then 2 else 0 : ℝ) ≤
      |walkFlow (F.forestPath a b) e| + |walkFlow (F.forestPath c d) e| := by
  have hs := pathCancel_weighted_swap_saving hF (fun z => if z = e then 1 else 0)
    (fun z _ => by split <;> norm_num) hab hcd hx hy
  simp only [single_edge_weight_length] at hs
  by_cases he : x.1 = e <;> simpa [he] using hs

end MinCostFlow.MinRatio
