module

public import MinCostFlow.MinRatio.PathCancellationRoute
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.LSF.Walks
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Absolute changes on a cancellation-free route

Algorithm 2 (page 29) adds the absolute traversal change to each
detector. On a route with no opposite traversals, a tree edge receives
increments of only one sign. Summing the absolute increments then
gives the exact change required by the detector.
-/

public section

namespace MinCostFlow.MinRatio

private theorem walkFlow_nonneg_of_no_reverse (walk : List (ℕ × Bool)) (e : ℕ)
    (h : (e, false) ∉ walk) : 0 ≤ walkFlow walk e := by
  induction walk with
  | nil => simp [walkFlow_nil]
  | cons x rest ih =>
    obtain ⟨name, dir⟩ := x
    have hrest : (e, false) ∉ rest := fun hr => h (List.mem_cons_of_mem _ hr)
    rw [walkFlow_cons]
    apply add_nonneg _ (ih hrest)
    by_cases hn : name = e
    · subst name
      cases dir
      · exact (h List.mem_cons_self).elim
      · simp
    · simp [hn]

private theorem walkFlow_nonpos_of_no_forward (walk : List (ℕ × Bool)) (e : ℕ)
    (h : (e, true) ∉ walk) : walkFlow walk e ≤ 0 := by
  induction walk with
  | nil => simp [walkFlow_nil]
  | cons x rest ih =>
    obtain ⟨name, dir⟩ := x
    have hrest : (e, true) ∉ rest := fun hr => h (List.mem_cons_of_mem _ hr)
    rw [walkFlow_cons]
    apply add_nonpos _ (ih hrest)
    by_cases hn : name = e
    · subst name
      cases dir
      · simp
      · exact (h List.mem_cons_self).elim
    · simp [hn]

/-- On each fixed edge, the cancellation-free route's contributions
have a common sign. -/
theorem pathCancel_route_sign (F : MGraph) (Q : List (ℕ × ℕ))
    (hcancel : ∀ (x : ℕ × Bool) p q, p ∈ Q → q ∈ Q → x ∈ F.forestPath p.1 p.2 →
      (x.1, !x.2) ∉ F.forestPath q.1 q.2) (e : ℕ) :
    (∀ p ∈ Q, 0 ≤ walkFlow (F.forestPath p.1 p.2) e) ∨
    (∀ p ∈ Q, walkFlow (F.forestPath p.1 p.2) e ≤ 0) := by
  classical
  by_cases hex : ∃ p ∈ Q, (e, true) ∈ F.forestPath p.1 p.2
  · obtain ⟨p, hp, hfor⟩ := hex
    exact Or.inl fun q hq => walkFlow_nonneg_of_no_reverse _ e (hcancel (e, true) p q hp hq hfor)
  · exact Or.inr fun p hp => walkFlow_nonpos_of_no_forward _ e (fun h => hex ⟨p, hp, h⟩)

/-- A route without opposite traversals accounts for the exact
absolute change produced by a common multiplier. -/
theorem pathCancel_account_of_no_reverse (F : MGraph) (Q : List (ℕ × ℕ))
    (hcancel : ∀ (x : ℕ × Bool) p q, p ∈ Q → q ∈ Q → x ∈ F.forestPath p.1 p.2 →
      (x.1, !x.2) ∉ F.forestPath q.1 q.2) (e : ℕ) (k : ℝ) :
    (Q.map (fun p => |k * walkFlow (F.forestPath p.1 p.2) e|)).sum =
      |k * (Q.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum| := by
  simp only [abs_mul]
  rw [List.sum_map_mul_left]
  congr 1
  rcases pathCancel_route_sign F Q hcancel e with h | h
  · have hn : 0 ≤ (Q.map fun p => walkFlow (F.forestPath p.1 p.2) e).sum :=
      List.sum_nonneg fun _ hv => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
        exact h p hp
    rw [abs_of_nonneg hn]
    exact congrArg List.sum (List.map_congr_left fun p hp => abs_of_nonneg (h p hp))
  · have hn : (Q.map fun p => walkFlow (F.forestPath p.1 p.2) e).sum ≤ 0 := by
      have hsum (ps : List (ℕ × ℕ))
          (hs : ∀ p ∈ ps, walkFlow (F.forestPath p.1 p.2) e ≤ 0) :
          (ps.map fun p => walkFlow (F.forestPath p.1 p.2) e).sum ≤ 0 := by
        induction ps with
        | nil => simp
        | cons p rest ih =>
          exact add_nonpos (hs p List.mem_cons_self)
            (ih fun q hq => hs q (List.mem_cons_of_mem _ hq))
      exact hsum Q h
    rw [abs_of_nonpos hn, List.sum_neg]
    simpa only [List.map_map, Function.comp_def] using
      congrArg List.sum (List.map_congr_left fun p hp => abs_of_nonpos (h p hp))

/-- Rerouting preserves the signed flow and lets the detector sum
absolute changes separately over paths, for every common multiplier. -/
theorem pathCancel_route_account (F : MGraph) (hF : F.IsForest) (paths : List (ℕ × ℕ))
    (hconn : ∀ p ∈ paths, F.Connected p.1 p.2) :
    ∃ Q : List (ℕ × ℕ), Q.length = paths.length ∧ (∀ p ∈ Q, F.Connected p.1 p.2) ∧
      (∀ e, (Q.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
        (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum) ∧
      ∀ (e : ℕ) (k : ℝ), (Q.map (fun p => |k * walkFlow (F.forestPath p.1 p.2) e|)).sum =
        |k * (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum| := by
  obtain ⟨Q, hlen, hc, hf, hcancel⟩ := pathCancel_route hF paths hconn
  refine ⟨Q, hlen, hc, hf, ?_⟩
  intro e k
  rw [← hf e]
  exact pathCancel_account_of_no_reverse F Q hcancel e k

private theorem pathCancel_abs_pair {F : MGraph} {a b c d : ℕ}
    (hF : F.IsForest) (hab : F.Connected a b)
    (hno : ∀ x ∈ F.forestPath a b, (x.1, !x.2) ∉ F.forestPath c d) (e : ℕ) :
    |walkFlow (F.forestPath a b) e + walkFlow (F.forestPath c d) e| =
      |walkFlow (F.forestPath a b) e| + |walkFlow (F.forestPath c d) e| := by
  classical
  have hnd := LSF.isPath_nodup_edges (LSF.forestPath_isPath hF hab)
  have hdistinct (ht : (e, true) ∈ F.forestPath a b)
      (hf : (e, false) ∈ F.forestPath a b) : False := by
    have heq := List.inj_on_of_nodup_map hnd ht hf rfl
    exact Bool.noConfusion (congrArg Prod.snd heq)
  by_cases ht : (e, true) ∈ F.forestPath a b
  · have h₁ := walkFlow_nonneg_of_no_reverse _ e (hdistinct ht)
    have h₂ := walkFlow_nonneg_of_no_reverse _ e (hno (e, true) ht)
    rw [abs_of_nonneg (add_nonneg h₁ h₂), abs_of_nonneg h₁, abs_of_nonneg h₂]
  · by_cases hf : (e, false) ∈ F.forestPath a b
    · have h₁ := walkFlow_nonpos_of_no_forward _ e ht
      have h₂ := walkFlow_nonpos_of_no_forward _ e (hno (e, false) hf)
      rw [abs_of_nonpos (add_nonpos h₁ h₂), abs_of_nonpos h₁, abs_of_nonpos h₂, neg_add]
    · have hz := le_antisymm (walkFlow_nonpos_of_no_forward _ e ht)
        (walkFlow_nonneg_of_no_reverse _ e hf)
      rw [hz, zero_add, abs_zero, zero_add]

private theorem pathLength_eq_forestSum {F : MGraph} {a b : ℕ}
    (h : F.Connected a b) (length : ℕ → ℝ) :
    walkLength length (F.forestPath a b) = ∑ e ∈ F.E, length e * |walkFlow (F.forestPath a b) e| := by
  apply walkLength_eq_sum_of_subset
  intro e he
  rw [walkEdges, List.mem_toFinset, List.mem_map] at he
  obtain ⟨x, hx, rfl⟩ := he
  exact MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath h) x hx

/-- Swapping destinations cannot lower the total weighted length
of two paths when the original paths have no opposite traversal. -/
theorem pathCancel_weighted_swap_le_of_no_reverse {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 ≤ length e)
    {a b c d : ℕ} (hab : F.Connected a b) (hac : F.Connected a c)
    (hcd : F.Connected c d)
    (hno : ∀ x ∈ F.forestPath a b, (x.1, !x.2) ∉ F.forestPath c d) :
    walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) ≤
      walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) := by
  have had := MGraph.connected_trans hac hcd
  have hcb := MGraph.connected_trans (MGraph.connected_symm hac) hab
  rw [pathLength_eq_forestSum hab, pathLength_eq_forestSum hcd,
    pathLength_eq_forestSum had, pathLength_eq_forestSum hcb,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  rw [← mul_add, ← mul_add, ← pathCancel_abs_pair hF hab hno,
    pathCancel_swap_flow hF hab hac hcd]
  exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (hℓ e he)

/-- For positive weights, four weighted path lengths detect exactly
whether two paths in one component traverse an edge oppositely. -/
theorem pathCancel_weighted_swap_iff {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e)
    {a b c d : ℕ} (hab : F.Connected a b) (hac : F.Connected a c)
    (hcd : F.Connected c d) :
    walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) <
      walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) ↔
      ∃ x ∈ F.forestPath a b, (x.1, !x.2) ∈ F.forestPath c d := by
  classical
  constructor
  · intro hlt
    by_contra hn
    apply (not_lt_of_ge (pathCancel_weighted_swap_le_of_no_reverse hF length
      (fun e he => (hℓ e he).le) hab hac hcd (fun x hx hy => hn ⟨x, hx, hy⟩))) hlt
  · rintro ⟨x, hx, hy⟩
    exact pathCancel_weighted_swap hF length hℓ hab hcd hx hy

/-- When the pair scan finds no strictly improving swap, the route
has no opposite traversal, including when it spans several components. -/
theorem pathCancel_no_reverse_of_scan {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e) (Q : List (ℕ × ℕ))
    (hc : ∀ p ∈ Q, F.Connected p.1 p.2)
    (hscan : ∀ p ∈ Q, ∀ q ∈ Q, F.Connected p.1 q.1 →
      walkLength length (F.forestPath p.1 p.2) + walkLength length (F.forestPath q.1 q.2) ≤
        walkLength length (F.forestPath p.1 q.2) + walkLength length (F.forestPath q.1 p.2)) :
    ∀ (x : ℕ × Bool) p q, p ∈ Q → q ∈ Q → x ∈ F.forestPath p.1 p.2 →
      (x.1, !x.2) ∉ F.forestPath q.1 q.2 := by
  intro x p q hp hq hx hy
  have hpw := MGraph.isWalk_forestPath (hc p hp)
  have hqw := MGraph.isWalk_forestPath (hc q hq)
  obtain ⟨a, _, _, ha, _⟩ := LSF.IsWalk_mem_split_edge hpw hx
  obtain ⟨b, _, _, hb, _⟩ := LSF.IsWalk_mem_split_edge hqw hy
  have he := MGraph.isWalk_edges_mem hpw x hx
  have hflip : F.src (x.1, !x.2) = F.dst x := by
    cases h : x.2 <;> simp [MGraph.src, MGraph.dst, h]
  rw [hflip] at hb
  have hgo : F.Connected (F.src x) (F.dst x) := ⟨[x], .cons he rfl (.nil _)⟩
  have hconn : F.Connected p.1 q.1 :=
    MGraph.connected_trans (MGraph.connected_trans ⟨a, ha⟩ hgo)
      (MGraph.connected_symm ⟨b, hb⟩)
  exact (not_lt_of_ge (hscan p hp q hq hconn))
    (pathCancel_weighted_swap hF length hℓ (hc p hp) (hc q hq) hx hy)

/-- A scan over increasing index pairs suffices. At its stopping
point the absolute accounting identity holds on every edge. -/
theorem pathCancel_account_of_index_scan {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e) (Q : List (ℕ × ℕ))
    (hc : ∀ p ∈ Q, F.Connected p.1 p.2)
    (hscan : ∀ i j (hi : i < Q.length) (hj : j < Q.length), i < j →
      F.Connected Q[i].1 Q[j].1 →
      walkLength length (F.forestPath Q[i].1 Q[i].2) +
        walkLength length (F.forestPath Q[j].1 Q[j].2) ≤
      walkLength length (F.forestPath Q[i].1 Q[j].2) +
        walkLength length (F.forestPath Q[j].1 Q[i].2))
    (e : ℕ) (k : ℝ) :
    (Q.map (fun p => |k * walkFlow (F.forestPath p.1 p.2) e|)).sum =
      |k * (Q.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum| := by
  apply pathCancel_account_of_no_reverse F Q _ e k
  apply pathCancel_no_reverse_of_scan hF length hℓ Q hc
  intro p hp q hq hconn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  rcases lt_trichotomy i j with h | rfl | h
  · exact hscan i j hi hj h hconn
  · exact le_rfl
  · simpa only [add_comm] using hscan j i hj hi h (MGraph.connected_symm hconn)

end MinCostFlow.MinRatio
