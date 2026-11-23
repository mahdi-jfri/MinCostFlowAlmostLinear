module

public import MinCostFlow.Scaling.BottleneckBudget
import WordRAM.Entry

/-!
# Logarithmic canonical widths for bottleneck tests

After vertex compression, at most twice as many vertices as edges remain.
Every threshold solver graph has unit capacities and costs bounded by
`m^10`. Its encoding size and largest word are therefore polynomial in
`m+2`, regardless of the original capacities or chosen threshold.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem foldr_max_le (xs : List ℕ) (M : ℕ) (h : ∀ x ∈ xs,x≤M) : xs.foldr max 0≤M := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem graph_words_le (K : Circulation) (M : ℕ) (hn : K.n≤M) (hm : K.m≤M)
    (hu : ∀ e,K.capacity e≤M) (hc : K.CostsBounded M) (h1 : 1≤M) :
    ∀ x ∈ K.solverWords,x≤M := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
  simp only [Circulation.solverEdgeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (Nat.le_of_lt (K.tail e).isLt).trans hn
  · exact (Nat.le_of_lt (K.head e).isLt).trans hn
  · exact hu e
  · split <;> omega
  · exact hc e

private theorem encoding_base_polynomial (m n : ℕ) (hn : n≤2*m) :
    n+6*m+m^10+6≤(m+2)^14 := by
  let M := m+2
  have hM : 0<M := by dsimp only [M]; omega
  have hm : m^10≤M^10 := Nat.pow_le_pow_left (show m≤M by dsimp only [M]; omega) 10
  have hlinear : M≤M^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hM (by decide : 1≤10)
  have hlinear' : m+2≤M^10 := hlinear
  have hsum : n+6*m+m^10+6≤9*M^10 := by omega
  have hfour : 16≤M^4 := Nat.pow_le_pow_left (show 2≤M by dsimp only [M]; omega) 4
  have hmul : 9*M^10≤M^4*M^10 := Nat.mul_le_mul_right _ (show 9≤M^4 by omega)
  have hpow : M^4*M^10=M^14 := by rw [←pow_add]
  exact hsum.trans (hmul.trans_eq hpow)

/-- Every threshold's canonical guest uses at most a fixed multiple of
`clog_2(m+2)+1` bits on a compressed polynomial-cost graph. -/
theorem bottleneckGuest_width_le (J : Circulation) (u : ℕ)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords ≤
      75*(Nat.clog 2 (J.m+2)+1) := by
  let K := (J.bottleneckGraph u).positiveInstance
  let M := J.n+J.m+J.m^10+2
  have hcost : K.CostsBounded M := by
    have h := (J.bottleneckGraph u).positiveInstance_costsBounded (J.m^10) hc
    intro e
    exact (h e).trans (by dsimp only [M]; omega)
  have hcap : ∀ e,K.capacity e≤M := by
    intro e
    have h := (J.bottleneckGraph u).positiveInstance_capacitiesBounded 1 (by decide)
      (J.bottleneckGraph_capacities u) e
    exact h.2.trans (by dsimp only [M]; omega)
  have hwords := graph_words_le K M (by change J.n+1≤M; dsimp only [M]; omega)
    (by change J.m≤M; dsimp only [M]; omega) hcap hcost (by dsimp only [M]; omega)
  have hmax := foldr_max_le K.solverWords M hwords
  have hbase : K.solverWords.length+K.solverWords.foldr max 0+2≤(J.m+2)^14 := by
    rw [K.solverWords_length]
    have hp := encoding_base_polynomial J.m J.n hn
    change 2+5*J.m+K.solverWords.foldr max 0+2≤_
    dsimp only [M] at hmax
    omega
  have hpow : (J.m+2)^14≤2^(Nat.clog 2 (J.m+2)*14) := by
    have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) (J.m+2)) 14
    simpa only [←pow_mul] using h
  have hlog : Nat.log 2 (K.solverWords.length+K.solverWords.foldr max 0+2)≤
      Nat.clog 2 (J.m+2)*14 :=
    (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (hbase.trans hpow))
  change 5*(Nat.log 2 (K.solverWords.length+K.solverWords.foldr max 0+2)+1)≤_
  omega

/-- The maximum guest width over any candidate list has the same
logarithmic bound, independently of candidate capacities and repetitions. -/
theorem bottleneckGuestBound_le (J : Circulation) (candidates : List ℕ)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    bottleneckGuestBound J candidates≤75*(Nat.clog 2 (J.m+2)+1) := by
  apply foldr_max_le
  intro x hx
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
  exact bottleneckGuest_width_le J u hn hc

end MinCostFlow.Scaling.Machine
