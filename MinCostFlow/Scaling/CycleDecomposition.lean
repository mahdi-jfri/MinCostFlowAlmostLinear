module

public import MinCostFlow.Scaling.CycleSubtraction
import Mathlib.Tactic.Ring

/-!
# Decomposing a circulation into at most m simple cycles

The proofs used for Lemma C.9 in Appendix C of Chen et al.,
arXiv:2203.00671v2, decompose an optimal circulation into nonnegative cycle
flows. Repeatedly subtract the minimum on a simple positive-support cycle.
Each subtraction removes an edge, so there are at most `m` terms. The cycles
may overlap: this repairs the source's edge-disjoint claim without changing
its coefficient and cost estimates.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- One weighted closed walk. Its simplicity and coefficient sign are proved
by the decomposition theorem rather than stored as result fields. -/
structure CycleTerm (I : Circulation) where
  vertex : Fin I.n
  walk : I.DirectedWalk vertex vertex
  amount : ℝ

/-- The flow represented by a list of weighted cycles. -/
def cycleSum (I : Circulation) (terms : List (CycleTerm I)) (e : Fin I.m) : ℝ :=
  (terms.map (fun t => t.amount * (t.walk.count e : ℝ))).sum

private theorem decompose_support (I : Circulation) (k : ℕ) :
    ∀ f : Fin I.m → ℝ, I.Feasible f → (I.flowSupport f).card ≤ k →
    ∃ terms : List (CycleTerm I), terms.length ≤ (I.flowSupport f).card ∧
      (∀ t ∈ terms, 0 < t.amount ∧ 0 < t.walk.length ∧ ∀ e, t.walk.count e ≤ 1) ∧
      I.cycleSum terms = f := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hf hcard
    by_cases hpos : ∃ e, 0 < f e
    · obtain ⟨v, p, a, hlen, hcount, ha, _, hrem, hlt⟩ := I.exists_cycle_subtraction f hf hpos
      let rem : Fin I.m → ℝ := fun e => f e - a * (p.count e : ℝ)
      change (I.flowSupport rem).card < (I.flowSupport f).card at hlt
      have hlt' : (I.flowSupport rem).card < k := lt_of_lt_of_le hlt hcard
      obtain ⟨terms, hlength, hterms, hsum⟩ := ih (I.flowSupport rem).card hlt' rem hrem le_rfl
      let t : CycleTerm I := ⟨v, p, a⟩
      refine ⟨t :: terms, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro u hu
        rcases List.mem_cons.mp hu with he | he
        · subst u
          exact ⟨ha, hlen, hcount⟩
        · exact hterms u he
      · funext e
        change a * (p.count e : ℝ) + I.cycleSum terms e = f e
        rw [hsum]
        dsimp only [rem]
        ring
    · have hfzero : f = fun _ => 0 := by
        funext e
        have hh : ¬ 0 < f e := fun he => hpos ⟨e, he⟩
        have hn := (hf.2 e).1
        exact le_antisymm (le_of_not_gt hh) hn
      refine ⟨[], Nat.zero_le _, ?_, ?_⟩
      · intro t ht; cases ht
      · funext e
        simp only [cycleSum, List.map_nil, List.sum_nil]
        rw [hfzero]

/-- Every nonnegative feasible circulation is a sum of at most `m` positively
weighted, nonempty simple cycles. Cycles may share edges, correcting the
source's edge-disjoint claim in the proofs of Lemmas C.10 and C.12. -/
theorem exists_cycle_decomposition (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) :
    ∃ terms : List (CycleTerm I), terms.length ≤ I.m ∧
      (∀ t ∈ terms, 0 < t.amount ∧ 0 < t.walk.length ∧ ∀ e, t.walk.count e ≤ 1) ∧
      I.cycleSum terms = f := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := decompose_support I (I.flowSupport f).card f hf le_rfl
  have hcard : (I.flowSupport f).card ≤ I.m := by
    exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  exact ⟨terms, le_trans hlen hcard, hterms, hsum⟩

end MinCostFlow.Scaling.Circulation
