module

public import MinCostFlow.IPM.HiddenBounds
public import MinCostFlow.IPM.MinRatioSpec
import MinCostFlow.IPM.Iteration
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.WeightedBounds
import Mathlib.Tactic.Linarith

/-!
# Hidden stability of the IPM's dynamic instances

Chen et al., arXiv:2203.00671v2, Lemma 9.2 (pages 70--71), is adapted
to the fixed graph and edge updates of Definition 4.5 (page 14 of
arXiv:2309.16629v1). The witnesses are the direction to an optimum and
`50 + |ℓ(f*-f)|`. The five hidden-stability conditions follow from the
IPM's routing, potential and approximation bounds, and from the small
coordinate displacement between explicit edge insertions. The logarithmic
bounds use the barrier sum as proved in `HiddenBounds`.
-/

public section
namespace MinCostFlow.IPM

/-- Chen et al., arXiv:2203.00671v2, Lemma 9.2 (pages 70--71), adapted
to Definition 4.5. The numerical hypotheses are the IPM invariants and
the Detect displacement bound, rather than an assumed hidden witness.
The hidden stability parameter is `alpha I U / 8`, and the explicit
item-5 bound is `ipmPsi I U`. -/
theorem lemma_9_2 (I : Instance) (U F ε : ℝ) (D : DynamicInstance) (T : ℕ)
    (fstar : Fin I.m → ℝ) (f g ℓ : ℕ → Fin I.m → ℝ) (r : ℕ → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (he : 0 ≤ ε) (he' : ε ≤ 1)
    (hG : ∀ t ≤ T, D.G t = namedInstance I)
    (hg : ∀ t ≤ T, D.g t = namedVector (g t))
    (hℓ : ∀ t ≤ T, D.ℓ t = namedVector (ℓ t))
    (hf : ∀ t ≤ T, StrictlyInside I (f t)) (hroute : ∀ t ≤ T, I.Routes (f t))
    (hbefore : ∀ t ≤ T, Real.rpow (I.m*U) (-10) < residual I F (f t))
    (hpot : ∀ t ≤ T, potential I (alpha I U) F (f t) ≤ 200*I.m*Real.log (I.m*U))
    (hres : ∀ t ≤ T, ScalarApprox (1+ε) (r t) (residual I F (f t)))
    (hgrad : ∀ t ≤ T, GradientTolerance (lengths I (alpha I U) (f t))
      (fun e => (r t/residual I F (f t))*g t e) (gradient I (alpha I U) F (f t)) (alpha I U/2))
    (hlen : ∀ t ≤ T, VectorApprox 2 (ℓ t) (lengths I (alpha I U) (f t)))
    (hclose : ∀ t ≤ T, ∀ e : Fin I.m, ∀ t' ≤ t, D.NotInsertedBetween e t' t →
      ℓ t e = ℓ t' e ∧ |ℓ t e*(f t e-f t' e)| ≤ 1) :
    D.HiddenStable T (alpha I U/8) (ipmPsi I U) := by
  refine ⟨fun t => namedVector (fun e => fstar e-f t e),
    fun t => namedVector (hiddenWidth fstar (f t) (ℓ t)), ?_⟩
  intro t ht
  have hvalid := hiddenWidth_valid I fstar (f t) (ℓ t) hs.1 (hroute t ht)
  have hr : 0 < residual I F (f t) := lt_trans
    (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hsize) _) (hbefore t ht)
  have hlog := log_residual_before_stop I U F (f t) hsize (hbefore t ht)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hG t ht]
    exact hvalid.1
  · rw [hG t ht, hℓ t ht]
    exact hvalid
  · rw [hG t ht, hg t ht]
    exact hiddenWidth_ratio I U F ε (r t) fstar (f t) (g t) (ℓ t) hm hsize
      (hf t ht) hs hr hF he he' (hres t ht) (hgrad t ht) (hlen t ht) (hpot t ht) hlog
  · intro e heMem t' ht' hnot
    rw [hG t ht] at heMem
    have heI : e < I.m := Finset.mem_range.mp heMem
    let j : Fin I.m := ⟨e, heI⟩
    have hc := hclose t ht j t' ht' hnot
    simp only [namedVector, heI, ↓reduceDIte]
    change hiddenWidth fstar (f t) (ℓ t) j ≤ 2*hiddenWidth fstar (f t') (ℓ t') j
    have hh := hiddenWidth_stable fstar (f t) (f t') (ℓ t) j hc.2
    have hw : hiddenWidth fstar (f t') (ℓ t) j = hiddenWidth fstar (f t') (ℓ t') j := by
      unfold hiddenWidth
      rw [hc.1]
    rw [hw] at hh
    exact hh
  · intro e heMem
    rw [hG t ht] at heMem
    have heI : e < I.m := Finset.mem_range.mp heMem
    rw [hℓ t ht]
    simp only [namedVector, heI, ↓reduceDIte]
    exact hiddenWidth_log_bounds I U F fstar (f t) (ℓ t) hm hU hsize hnums
      (hf t ht) (hroute t ht) hs (hlen t ht) (hpot t ht) hlog ⟨e, heI⟩

/-- The additional sequence hypotheses of `lemma_9_2` can hold together.
An unchanged nonterminal IPM flow, with exact gradients and lengths,
gives a hidden stable dynamic input for every finite horizon. -/
theorem constant_ipm_hiddenStable (I : Instance) (U F : ℝ) (f fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hs : I.IsMinCostFlow fstar) (hF : I.cost fstar = F)
    (hbefore : Real.rpow (I.m*U) (-10) < residual I F f)
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U)) (T : ℕ) :
    ∃ D : DynamicInstance, (∀ t, D.G t = namedInstance I ∧ D.U t = []) ∧
      D.HiddenStable T (alpha I U/8) (ipmPsi I U) := by
  let D : DynamicInstance :=
    { G := fun _ => namedInstance I, U := fun _ => [],
      g := fun _ => namedVector (gradient I (alpha I U) F f),
      ℓ := fun _ => namedVector (lengths I (alpha I U) f) }
  refine ⟨D, fun _ => ⟨rfl, rfl⟩, ?_⟩
  have hr : 0 < residual I F f := lt_trans
    (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hsize) _) hbefore
  have happrox := exact_approximations I (alpha I U) F (alpha I U/2) f hf
    (div_nonneg (alpha_pos I U hsize).le (by norm_num : (0 : ℝ) ≤ 2))
  apply lemma_9_2 I U F 0 D T fstar (fun _ => f)
    (fun _ => gradient I (alpha I U) F f) (fun _ => lengths I (alpha I U) f)
    (fun _ => residual I F f) hm hU hsize hnums hs.1 hF.le (by norm_num) (by norm_num)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => hf)
    (fun _ _ => hroute) (fun _ _ => hbefore) (fun _ _ => hpot)
  · intro t _
    refine ⟨hr, hr, ?_, ?_⟩ <;> norm_num
  · intro t _
    simpa only [div_self hr.ne', one_mul] using happrox.1
  · intro t _
    exact happrox.2
  · intro t _ e t' _ _
    exact ⟨rfl, by simp⟩

end MinCostFlow.IPM
