module

public import MinCostFlow.Basic.Forest
import MinCostFlow.MinRatio.PathSwapTransition
import MinCostFlow.MinRatio.TerminalSwapBound

/-!
# Bounding a history of successful indexed swaps

In the routing step of Algorithm 2 (page 29), the route changes only
when the pair scan finds a strictly smaller weighted length. The
indexed transition preserves the represented flow. The forest swap
bound limits the number of scans that can succeed.
-/

public section

namespace MinCostFlow.MinRatio

/-- A route history consisting of successful comparisons and their
indexed exchanges preserves the initial circulation. It can have
at most `4 * K^4` successful comparisons for `K` initial paths. -/
theorem pathSwap_index_history {F : MGraph} (hF : F.IsForest) (length : ℕ → ℝ)
    (hℓ : ∀ e ∈ F.E, 0 < length e) (route : ℕ → List (ℕ × ℕ)) (steps : ℕ)
    (hconn : ∀ p ∈ route 0, F.Connected p.1 p.2)
    (hstep : ∀ t < steps, ∃ i j : ℕ, ∃ hij : i < j, ∃ hj : j < (route t).length,
      let hi := hij.trans hj
      let a := (route t)[i].1
      let b := (route t)[i].2
      let c := (route t)[j].1
      let d := (route t)[j].2
      F.Connected a c ∧
      walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) <
        walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) ∧
      route (t + 1) = ((route t).set i (a,d)).set j (c,b)) :
    steps ≤ 4 * (route 0).length ^ 4 ∧
    ∀ t ≤ steps, (route t).length = (route 0).length ∧
      (∀ p ∈ route t, F.Connected p.1 p.2) ∧
      ∀ e, ((route t).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
        ((route 0).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum := by
  have hInv : ∀ t ≤ steps, (route t).length = (route 0).length ∧
      (∀ p ∈ route t, F.Connected p.1 p.2) ∧
      ∀ e, ((route t).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
        ((route 0).map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨rfl, hconn, fun _ => rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨hlen, hc, hf⟩ := ih (by omega)
      obtain ⟨i, j, hij, hj, hac, hlt, heq⟩ := hstep t (by omega)
      obtain ⟨hn, hnc, hnf, _⟩ := pathSwap_index_transition hF length hℓ (route t) hij hj hc hac hlt
      rw [heq]
      exact ⟨hn.trans hlen, hnc, fun e => (hnf e).trans (hf e)⟩
  refine ⟨terminalSwapBound_pathCount hF route steps hconn ?_, hInv⟩
  intro t ht
  have hc := (hInv t ht.le).2.1
  obtain ⟨i, j, hij, hj, hac, hlt, heq⟩ := hstep t ht
  have hi : i < (route t).length := hij.trans hj
  have hab := hc (route t)[i] (List.getElem_mem hi)
  have hcd := hc (route t)[j] (List.getElem_mem hj)
  obtain ⟨_, _, _, x, rest, hx, hy, hb, ha⟩ :=
    pathSwap_index_transition hF length hℓ (route t) hij hj hc hac hlt
  exact ⟨_, _, _, _, x, rest, hab, hac, hcd, hx, hy, hb, heq.symm ▸ ha⟩

/-- The two increasing-index loops visit precisely the candidates
of the swap test. -/
theorem pathSwap_scan_indices (K : ℕ) :
    let pairs := (List.range K).flatMap fun i =>
      ((List.range K).filter fun j => i < j).map fun j => (i,j)
    pairs.length ≤ K * K ∧
      ∀ i j, (i,j) ∈ pairs ↔ i < j ∧ j < K := by
  dsimp only
  constructor
  · have h (rows : List ℕ) :
        (rows.flatMap fun i => ((List.range K).filter fun j => i < j).map fun j => (i,j)).length
          ≤ rows.length * K := by
      induction rows with
      | nil => simp
      | cons i rows ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, Nat.succ_mul]
        have hi : ((List.range K).filter fun j => i < j).length ≤ K := by
          simpa only [List.length_range] using
            (List.length_filter_le (p := fun j => decide (i < j)) (List.range K))
        exact (add_le_add hi ih).trans_eq (Nat.add_comm ..)
    simpa only [List.length_range] using h (List.range K)
  · intro i j
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a, _, b, ⟨hb, hab⟩, rfl, rfl⟩
      exact ⟨hab, hb⟩
    · rintro ⟨hij, hj⟩
      exact ⟨i, hij.trans hj, j, ⟨hj, hij⟩, rfl, rfl⟩

/-- A scan that visits each increasing index pair at most once
performs at most `K^2` comparisons. Including the last unsuccessful
scan, at most `(4 * K^4 + 1) * K^2` comparisons are needed. -/
theorem pathSwap_comparison_budget (K swaps : ℕ) (counts : List ℕ)
    (hs : swaps ≤ 4 * K ^ 4) (hn : counts.length ≤ swaps + 1)
    (hc : ∀ c ∈ counts, c ≤ K * K) :
    counts.sum ≤ (4 * K ^ 4 + 1) * (K * K) := by
  have hsum : counts.sum ≤ counts.length * (K * K) := by
    induction counts with
    | nil => simp
    | cons n rest ih =>
      have ht : rest.length ≤ swaps + 1 := by
        simp only [List.length_cons] at hn
        omega
      have hr := ih ht (fun c h => hc c (List.mem_cons_of_mem _ h))
      simpa only [List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm] using
        add_le_add (hc n List.mem_cons_self) hr
  refine hsum.trans (Nat.mul_le_mul_right _ (hn.trans ?_))
  omega

end MinCostFlow.MinRatio
