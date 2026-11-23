module

public import MinCostFlow.MinRatio.PathCancellation
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.LSF.Walks
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Counting cancellation swaps by representative edges

Algorithm 2 (page 29) needs a short route whose absolute increments
equal the net absolute change. To bound destination swaps, count the
traversals on a chosen set of forest edges. A swap cannot raise this
count, and loses two if one of the chosen edges witnesses the swap.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Total absolute traversal count on the selected edges. -/
noncomputable def pathSwapPotential (F : MGraph) (sample : Finset ℕ)
    (route : List (ℕ × ℕ)) : ℝ :=
  ∑ e ∈ sample, (route.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

private theorem pathSwapPotential_nonneg (F : MGraph) (sample : Finset ℕ)
    (route : List (ℕ × ℕ)) : 0 ≤ pathSwapPotential F sample route := by
  apply Finset.sum_nonneg
  intro e _
  apply List.sum_nonneg
  intro r hr
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
  exact abs_nonneg _

private theorem pathSwapPotential_le (F : MGraph) (hF : F.IsForest)
    (sample : Finset ℕ) (route : List (ℕ × ℕ))
    (hc : ∀ p ∈ route, F.Connected p.1 p.2) :
    pathSwapPotential F sample route ≤ (sample.card : ℝ) * route.length := by
  unfold pathSwapPotential
  calc
    _ ≤ ∑ _ ∈ sample, (route.length : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      induction route with
      | nil => simp
      | cons p rest ih =>
        have hp := LSF.forestPath_isPath hF (hc p List.mem_cons_self)
        have h₁ : |walkFlow (F.forestPath p.1 p.2) e| ≤ 1 := by
          rw [LSF.walkFlow_abs_of_nodup (LSF.isPath_nodup_edges hp)]
          split <;> norm_num
        have hr := ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
        linarith only [h₁, hr]
    _ = _ := by simp

/-- If a sampled edge has the same usage as the witness on all four
paths of a swap, the sampled traversal count decreases by at least
two. Order in the route list is immaterial. -/
theorem pathSwapPotential_drop_of_representative {F : MGraph} (hF : F.IsForest) (sample : Finset ℕ)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) {representative : ℕ}
    (hmem : representative ∈ sample)
    (hrep : ∀ p ∈ [(a,b), (c,d), (a,d), (c,b)],
      |walkFlow (F.forestPath p.1 p.2) representative| = |walkFlow (F.forestPath p.1 p.2) x.1|)
    (rest before after : List (ℕ × ℕ))
    (hBefore : before.Perm ((a,b) :: (c,d) :: rest))
    (hAfter : after.Perm ((a,d) :: (c,b) :: rest)) :
    pathSwapPotential F sample after + 2 ≤ pathSwapPotential F sample before := by
  classical
  have hs : (∑ e ∈ sample, (if representative = e then 2 else 0 : ℝ)) = 2 := by
    rw [Finset.sum_eq_single representative (fun e _ hne => by simp [Ne.symm hne])
      (fun h => (h hmem).elim)]
    simp
  unfold pathSwapPotential
  rw [← hs, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  rw [(hBefore.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum_eq,
    (hAfter.map (fun p => |walkFlow (F.forestPath p.1 p.2) e|)).sum_eq]
  simp only [List.map_cons, List.sum_cons]
  by_cases he : representative = e
  · subst e
    have h := pathCancel_swap_edge_usage hF hab hcd hx hy x.1
    rw [hrep (a,b) (by simp), hrep (c,d) (by simp), hrep (a,d) (by simp),
      hrep (c,b) (by simp)]
    simp only [eq_self, ↓reduceIte] at h ⊢
    linarith only [h]
  · have h := pathCancel_swap_edge_usage hF hab hcd hx hy e
    have hz : 0 ≤ (if x.1 = e then 2 else 0 : ℝ) := by split <;> norm_num
    rw [ite_eq_right he]
    linarith only [h, hz]

/-- A sampled witness can serve as its own representative. -/
theorem pathSwapPotential_drop {F : MGraph} (hF : F.IsForest) (sample : Finset ℕ)
    {a b c d : ℕ} (hab : F.Connected a b) (hcd : F.Connected c d)
    {x : ℕ × Bool} (hx : x ∈ F.forestPath a b)
    (hy : (x.1, !x.2) ∈ F.forestPath c d) (hmem : x.1 ∈ sample)
    (rest before after : List (ℕ × ℕ))
    (hBefore : before.Perm ((a,b) :: (c,d) :: rest))
    (hAfter : after.Perm ((a,d) :: (c,b) :: rest)) :
    pathSwapPotential F sample after + 2 ≤ pathSwapPotential F sample before :=
  pathSwapPotential_drop_of_representative hF sample hab hcd hx hy hmem
    (fun _ _ => rfl) rest before after hBefore hAfter

/-- Once every swap has a witness in the sampled edge set, the whole
history has at most half its initial path count times the sample size
in swaps. This bound does not count expanded path lengths. -/
theorem pathSwapPotential_history_bound (F : MGraph) (hF : F.IsForest) (sample : Finset ℕ)
    (route : ℕ → List (ℕ × ℕ)) (steps : ℕ)
    (hc : ∀ p ∈ route 0, F.Connected p.1 p.2)
    (hdrop : ∀ t < steps, pathSwapPotential F sample (route (t + 1)) + 2 ≤
      pathSwapPotential F sample (route t)) :
    2 * steps ≤ sample.card * (route 0).length := by
  have htotal : ∀ t ≤ steps, pathSwapPotential F sample (route t) + 2 * (t : ℝ) ≤
      pathSwapPotential F sample (route 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro ht
      have h := hdrop t (by omega)
      have h' := ih (by omega)
      rw [Nat.cast_succ]
      linarith only [h, h']
  have hh := htotal steps le_rfl
  have h₀ := pathSwapPotential_nonneg F sample (route steps)
  have hcap := pathSwapPotential_le F hF sample (route 0) hc
  have hreal : 2 * (steps : ℝ) ≤ (sample.card : ℝ) * (route 0).length :=
    by linarith only [hh, h₀, hcap]
  exact_mod_cast hreal

end MinCostFlow.MinRatio
