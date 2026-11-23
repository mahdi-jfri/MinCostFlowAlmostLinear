module

public import MinCostFlow.Scaling.BinarySearchSelection

/-!
# Selection by the finite bottleneck search

The binary search in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, exhausts its interval within the proved logarithmic budget.
Induction of the selection invariants shows that its stored output is a
genuine negative unit optimum at the last accepted capacity slot, and all
slots after it are rejected. If none was accepted, every slot is rejected.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- The actual finite search selects a genuine accepted predecessor and
rejects all candidates from its final endpoint onward. -/
theorem bottleneckSearch_selection (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) :
    let candidates := (sortCapacities (List.ofFn I.capacity)).1
    let s := (bottleneckSearch solve I).value
    s.lower = s.upper ∧ s.upper ≤ candidates.length ∧
      (∀ i, s.upper ≤ i → i < candidates.length →
        ¬ I.bottleneckAccepts solve (candidates.getD i 0)) ∧
      (match s.best with
       | none => s.lower = 0
       | some (u, f) => 0 < s.lower ∧ u = candidates.getD (s.lower - 1) 0 ∧
          f = Circulation.solveWithZeroCapacities solve (I.bottleneckGraph u) ∧
          (I.bottleneckGraph u).integerObjective f < 0) := by
  let candidates := (sortCapacities (List.ofFn I.capacity)).1
  have hlen : candidates.length = I.m := by
    simpa only [List.length_ofFn] using (sortCapacities_perm (List.ofFn I.capacity)).length_eq
  let P (s : BottleneckState I) :=
    (s.lower ≤ s.upper ∧ s.upper ≤ candidates.length) ∧
    (∀ i, s.upper ≤ i → i < candidates.length →
      ¬ I.bottleneckAccepts solve (candidates.getD i 0)) ∧
    (match s.best with
     | none => s.lower = 0
     | some (u, f) => 0 < s.lower ∧ u = candidates.getD (s.lower - 1) 0 ∧
        f = Circulation.solveWithZeroCapacities solve (I.bottleneckGraph u) ∧
        (I.bottleneckGraph u).integerObjective f < 0)
  have hstep : ∀ s, P s → P (s.step solve candidates).value := by
    intro s hs
    exact ⟨s.step_interval solve candidates hs.1,
      s.step_rejected_suffix solve candidates (sortCapacities_sorted _)
        (fun u v huv => I.bottleneckAccepts_mono solve hsolve hc u v huv) hs.1 hs.2.1,
      s.step_best solve candidates hs.2.2⟩
  have hinit : P ⟨0, I.m, none⟩ := by
    refine ⟨⟨Nat.zero_le _, by rw [hlen]⟩, ?_, rfl⟩
    intro i hi hil
    rw [hlen] at hil
    change I.m ≤ i at hi
    omega
  have hfinal := CallResult.forRounds_invariant (BottleneckState.step solve candidates) P hstep
    (Nat.clog 2 (I.m + 1)) (⟨0, I.m, none⟩ : BottleneckState I) hinit
  change P (bottleneckSearch solve I).value at hfinal
  have hd := bottleneckSearch_done solve I
  change (bottleneckSearch solve I).value.upper - (bottleneckSearch solve I).value.lower = 0 at hd
  have he : (bottleneckSearch solve I).value.lower = (bottleneckSearch solve I).value.upper := by
    have hh := hfinal.1.1
    omega
  exact ⟨he, hfinal.1.2, hfinal.2.1, hfinal.2.2⟩

end MinCostFlow.Scaling
