module

public import MinCostFlow.Scaling.BottleneckBudget
import WordRAM.LinkDefs

/-!
# Polynomial host storage for threshold-solver guests

A threshold query has unit capacities, the original costs, and one extra
vertex. Its encoding size base is at most twice the original encoding
size base. A multiplier-five guest therefore uses at most the tenth
power of the original base in addressable cells. Taking the maximum over
candidate thresholds preserves this bound.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem graph_words_bound (K : Circulation) (B : ℕ) (hn : K.n≤B) (hm : K.m≤B)
    (hu : ∀ e,K.capacity e≤B) (hc : K.CostsBounded B) (h1 : 1≤B) :
    ∀ x ∈ K.solverWords,x≤B := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
  simp only [Circulation.solverEdgeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (K.tail e).isLt.le.trans hn
  · exact (K.head e).isLt.le.trans hn
  · exact hu e
  · split <;> omega
  · exact hc e

private theorem max_bound (xs : List ℕ) (B : ℕ) (h : ∀ x ∈ xs,x≤B) : xs.foldr max 0≤B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih => exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Bounds on a circulation's dimensions, capacities, and costs bound
every word of its common encoding, including endpoint and sign words. -/
theorem solverWords_max_le_of_bounds (J : Circulation) (B : ℕ) (hn : J.n≤B) (hm : J.m≤B)
    (hu : ∀ e,J.capacity e≤B) (hc : J.CostsBounded B) (h1 : 1≤B) :
    J.solverWords.foldr max 0≤B :=
  max_bound J.solverWords B (graph_words_bound J B hn hm hu hc h1)

/-- Every threshold query's addressable guest region is polynomial in the
original source encoding base, independently of its threshold. -/
theorem bottleneckGuest_space_le (J : Circulation) (u : ℕ) :
    2^wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords≤
      (J.solverWords.length+J.solverWords.foldr max 0+2)^10 := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  let K := (J.bottleneckGraph u).positiveInstance
  let Q := K.solverWords.length+K.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hn : J.n≤J.solverWords.foldr max 0 := Link.elem_le_foldr_max List.mem_cons_self
  have hB : 4+5*J.m+J.n≤B := by dsimp only [B]; omega
  have hsourceCost : J.CostsBounded B := by
    intro e
    have h : (J.cost e).natAbs≤J.solverWords.foldr max 0 :=
      Link.elem_le_foldr_max (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    dsimp only [B]
    omega
  have hcost := (J.bottleneckGraph u).positiveInstance_costsBounded B hsourceCost
  have hcap : ∀ e,K.capacity e≤B := by
    intro e
    have h := (J.bottleneckGraph u).positiveInstance_capacitiesBounded 1 (by decide)
      (J.bottleneckGraph_capacities u) e
    exact h.2.trans (by omega)
  have hwords := graph_words_bound K B (by change J.n+1≤B; omega)
    (by change J.m≤B; omega) hcap hcost (by omega)
  have hmax := max_bound K.solverWords B hwords
  have hQ : Q≤2*B := by dsimp only [Q]; rw [K.solverWords_length]; change 2+5*J.m+K.solverWords.foldr max 0+2≤2*B; omega
  have hQpositive : 0<Q := by dsimp only [Q]; omega
  have hlog : 2^(Nat.log 2 Q+1)≤2*Q := by
    rw [pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (Nat.ne_of_gt hQpositive))
  have hfour : 4*B≤B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right B (show 4≤B by omega)
  have hpower := Nat.pow_le_pow_left (hlog.trans (by omega : 2*Q≤B^2)) 5
  change 2^(5*(Nat.log 2 Q+1))≤B^10
  calc
    _ = (2^(Nat.log 2 Q+1))^5 := by rw [Nat.mul_comm 5, pow_mul]
    _ ≤ (B^2)^5 := hpower
    _ = B^10 := by rw [←pow_mul]

private theorem pow_max_bound (xs : List ℕ) (B : ℕ) (h1 : 1≤B)
    (h : ∀ x ∈ xs,2^x≤B) : 2^(xs.foldr max 0)≤B := by
  induction xs with
  | nil => exact h1
  | cons x xs ih =>
    change 2^max x (xs.foldr max 0)≤B
    by_cases hx : x≤xs.foldr max 0
    · rw [max_eq_right hx]
      exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    · rw [max_eq_left (Nat.le_of_not_ge hx)]
      exact h x List.mem_cons_self

/-- The largest addressable threshold guest over any candidate list has
the same polynomial source-encoding bound. -/
theorem bottleneckGuestBound_space_le (J : Circulation) (candidates : List ℕ) :
    2^bottleneckGuestBound J candidates≤
      (J.solverWords.length+J.solverWords.foldr max 0+2)^10 := by
  apply pow_max_bound
  · have hbase : 1≤J.solverWords.length+J.solverWords.foldr max 0+2 := by omega
    exact Nat.one_le_pow 10 _ hbase
  · intro x hx
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    exact bottleneckGuest_space_le J u

end MinCostFlow.Scaling.Machine
