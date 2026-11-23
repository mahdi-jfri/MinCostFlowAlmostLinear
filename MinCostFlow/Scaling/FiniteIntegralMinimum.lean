module

public import MinCostFlow.Scaling.ReductionAlgorithm
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum

/-!
# A least-cost feasible integer circulation

The gap argument in the proof of Lemma C.9 of Chen et al.,
arXiv:2203.00671v2, Appendix C, uses integral optima. First, bounded integral
flows form a finite nonempty set: zero is feasible, and edge `e` has only
`u_e+1` possibilities. Minimizing the integral objective over that finite set
gives a feasible integer circulation no worse than any other integer flow.
The residual approximation argument upgrades it to a real optimum separately.
-/

public section
namespace MinCostFlow.Scaling.Circulation

/-- Every circulation instance has a feasible integral flow minimizing among
all feasible integral flows, by finite enumeration of capacity-bounded tables. -/
theorem exists_integral_minimum (I : Circulation) :
    ∃ f : Fin I.m → ℤ, I.Feasible (fun e => (f e : ℝ)) ∧
      ∀ g : Fin I.m → ℤ, I.Feasible (fun e => (g e : ℝ)) → I.integerObjective f ≤ I.integerObjective g := by
  classical
  let Tables := (e : Fin I.m) → Fin (I.capacity e + 1)
  let intFlow : Tables → Fin I.m → ℤ := fun f e => (f e).val
  let S : Finset Tables := Finset.univ.filter (fun f => I.Conserves (fun e => (intFlow f e : ℝ)))
  let zero : Tables := fun e => ⟨0, Nat.zero_lt_succ _⟩
  have hzero : zero ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [intFlow, zero, Nat.cast_zero, Int.cast_zero] using I.zero_feasible.1
  obtain ⟨f, hf, hmin⟩ := S.exists_min_image (fun f => I.integerObjective (intFlow f)) ⟨zero, hzero⟩
  have hfeas : I.Feasible (fun e => (intFlow f e : ℝ)) := by
    refine ⟨(Finset.mem_filter.mp hf).2, ?_⟩
    intro e
    have hh : (f e).val ≤ I.capacity e := Nat.le_of_lt_succ (f e).isLt
    dsimp only [intFlow]
    simp only [Int.cast_natCast]
    exact ⟨by exact_mod_cast Nat.zero_le (f e).val, by exact_mod_cast hh⟩
  refine ⟨intFlow f, hfeas, ?_⟩
  intro g hg
  have hgnon (e : Fin I.m) : 0 ≤ g e := Int.cast_nonneg_iff.mp (hg.2 e).1
  have hgle (e : Fin I.m) : g e ≤ (I.capacity e : ℤ) := by
    have hh := (hg.2 e).2
    dsimp only at hh
    exact_mod_cast hh
  let table : Tables := fun e => ⟨(g e).toNat, by have hh := hgnon e; have hl := hgle e; omega⟩
  have htable : intFlow table = g := by
    funext e
    exact Int.toNat_of_nonneg (hgnon e)
  have hmem : table ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [htable]
    exact hg.1
  have hh := hmin table hmem
  rw [htable] at hh
  exact hh

end MinCostFlow.Scaling.Circulation
