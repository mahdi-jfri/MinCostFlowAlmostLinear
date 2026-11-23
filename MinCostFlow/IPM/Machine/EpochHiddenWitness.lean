module

public import MinCostFlow.IPM.Machine.PrecisionHiddenRatio
public import MinCostFlow.IPM.Machine.PrecisionHiddenRange
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hidden stability of the computed coefficients at the stored exponent

Lemma 9.2 of Chen et al., arXiv:2203.00671v2 (pages 70–71), chooses the
direction to the optimum at each input stage. Here the ratio uses the
stored exponent, and the width range uses the actual coefficient guard.
To compare widths, use the same cached coordinate throughout an interval
with no insertion and bound the error at its two endpoints.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem unchanged_cache_between (D : DynamicInstance) {m : ℕ}
    (stored : ℕ → Fin m → ℝ) (T t u : ℕ) (e : Fin m) (htu : t≤u) (hu : u≤T)
    (hnot : D.NotInsertedBetween e t u)
    (hstep : ∀ j<T, ∀ e : Fin m, D.NotInsertedBetween e j (j+1) → stored (j+1) e=stored j e) :
    stored u e=stored t e := by
  induction u with
  | zero => have heq : t=0 := by omega
            rw [heq]
  | succ u ih =>
    by_cases heq : t=u+1
    · rw [heq]
    · have htu' : t≤u := by omega
      have hone : D.NotInsertedBetween e u (u+1) :=
        fun j hj hj' => hnot j (lt_of_le_of_lt htu' hj) hj'
      have hpast : D.NotInsertedBetween e t u :=
        fun j hj hj' => hnot j hj (hj'.trans (Nat.le_succ _))
      exact (hstep u (by omega) e hone).trans (ih htu' (by omega) hpast)

/-- A half unit of weighted error at each endpoint is enough to compare
the hidden widths. The coefficient and coordinate are constant between
these endpoints when the edge is never inserted. -/
theorem epoch_cached_motion_between (D : DynamicInstance) {m : ℕ}
    (stored f ell : ℕ → Fin m → ℝ) (T t u : ℕ) (e : Fin m) (htu : t≤u) (hu : u≤T)
    (hnot : D.NotInsertedBetween e t u)
    (hcoeff : ell u e=ell t e)
    (hstep : ∀ j<T, ∀ e : Fin m, D.NotInsertedBetween e j (j+1) → stored (j+1) e=stored j e)
    (hclose : ∀ j≤T, ∀ e, |ell j e*(f j e-stored j e)|≤1/2) :
    |ell u e*(f u e-f t e)|≤1 := by
  have hsame := unchanged_cache_between D stored T t u e htu hu hnot hstep
  calc
    _ = |ell u e*(f u e-stored u e) - ell t e*(f t e-stored t e)| := by
      rw [hsame,hcoeff]
      ring_nf
    _ ≤ |ell u e*(f u e-stored u e)|+|ell t e*(f t e-stored t e)| := abs_sub _ _
    _ ≤ 1 := by linarith only [hclose u hu e,hclose t (htu.trans hu) e]

/-- Lemma 9.2 (Chen et al., arXiv:2203.00671v2, pages 70–71) at the stored
exponent. This uses the actual computed coefficients in every ratio,
and the supplied binary range for Definition 4.4's item 5 (page 14). -/
theorem epoch_hidden_at_range (I : Instance) (U R : ℕ) (target a ε : ℝ)
    (D : DynamicInstance) (T : ℕ) (fstar : Fin I.m → ℝ)
    (f stored g ell : ℕ → Fin I.m → ℝ) (r : ℝ)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤(I.m:ℝ)*U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (ha : 0<a) (ha' : a≤alpha I U) (he : 0≤ε) (he' : ε≤1)
    (hG : ∀ t≤T,D.G t=namedInstance I)
    (hg : ∀ t≤T,D.g t=namedVector (g t))
    (hl : ∀ t≤T,D.ℓ t=namedVector (ell t))
    (hf : ∀ t≤T,StrictlyInside I (f t)) (hroutes : ∀ t≤T,I.Routes (f t))
    (hres : ∀ t≤T,0<residual I target (f t))
    (hreslog : ∀ t≤T,-10*Real.log (I.m*U)≤Real.log (residual I target (f t)))
    (hpot : ∀ t≤T,potential I a target (f t)≤200*I.m*Real.log (I.m*U))
    (hresidualApprox : ∀ t≤T,ScalarApprox (1+ε) r (residual I target (f t)))
    (hgrad : ∀ t≤T,GradientTolerance (lengths I a (f t))
      (fun e => (r/residual I target (f t))*g t e) (gradient I a target (f t)) (a/2))
    (hlen : ∀ t≤T,VectorApprox 2 (ell t) (lengths I a (f t)))
    (hrange : ∀ t≤T,∀ e,1/(2:ℝ)^(R)≤ell t e ∧ ell t e≤(2:ℝ)^(R))
    (hconstant : ∀ t≤T,∀ u≤t,∀ e : Fin I.m,D.NotInsertedBetween e u t → ell t e=ell u e)
    (hcache : ∀ t<T,∀ e : Fin I.m,D.NotInsertedBetween e t (t+1) → stored (t+1) e=stored t e)
    (hclose : ∀ t≤T,∀ e,|ell t e*(f t e-stored t e)|≤1/2) :
    D.HiddenStable T (a/8) ((R+slackRangeExponent I.m U+6 : ℕ) : ℝ) := by
  refine ⟨fun t => namedVector (fun e => fstar e-f t e),
    fun t => namedVector (hiddenWidth fstar (f t) (ell t)),?_⟩
  intro t ht
  have hv := hiddenWidth_valid I fstar (f t) (ell t) hs.1 (hroutes t ht)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hG t ht]
    exact hv.1
  · rw [hG t ht,hl t ht]
    exact hv
  · rw [hG t ht,hg t ht]
    exact hiddenWidth_ratio_at_exponent I U a target ε r fstar (f t) (g t) (ell t)
      hm hsize ha ha' (hf t ht) hs (hres t ht) hF he he' (hresidualApprox t ht)
      (hgrad t ht) (hlen t ht) (hpot t ht) (hreslog t ht)
  · intro e heG u hu hnot
    rw [hG t ht] at heG
    have hei : e<I.m := Finset.mem_range.mp heG
    let edge : Fin I.m := ⟨e,hei⟩
    simp only [namedVector,hei,↓reduceDIte]
    change hiddenWidth fstar (f t) (ell t) edge≤2*hiddenWidth fstar (f u) (ell u) edge
    have hsamel := hconstant t ht u hu edge hnot
    have hmove := epoch_cached_motion_between D stored f ell T u t edge hu ht hnot hsamel hcache hclose
    have hw := hiddenWidth_stable fstar (f t) (f u) (ell t) edge hmove
    have hw' : hiddenWidth fstar (f u) (ell t) edge=hiddenWidth fstar (f u) (ell u) edge := by
      unfold hiddenWidth
      rw [hsamel]
    rwa [hw'] at hw
  · intro e heG
    rw [hG t ht] at heG
    have hei : e<I.m := Finset.mem_range.mp heG
    rw [hl t ht]
    simp only [namedVector,hei,↓reduceDIte]
    let edge : Fin I.m := ⟨e,hei⟩
    have hfeasible : I.IsFeasible (f t) :=
      ⟨hroutes t ht,fun e => ⟨(hf t ht e).1.le,(hf t ht e).2.le⟩⟩
    exact precision_hidden_log_ranges_at_range I U R fstar (f t) (ell t) hm hU hnums hs hfeasible edge (hrange t ht edge)

/-- Lemma 9.2 (Chen et al., arXiv:2203.00671v2, pages 70–71) at the stored
exponent. This uses the actual computed coefficients in every ratio,
and `precisionHiddenPsi` for Definition 4.4's item 5 (page 14). -/
theorem epoch_hidden_at_stored_exponent (I : Instance) (U : ℕ) (target a ε : ℝ)
    (D : DynamicInstance) (T : ℕ) (fstar : Fin I.m → ℝ)
    (f stored g ell : ℕ → Fin I.m → ℝ) (r : ℝ)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤(I.m:ℝ)*U)
    (hnums : NumbersBounded I U) (hs : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (ha : 0<a) (ha' : a≤alpha I U) (he : 0≤ε) (he' : ε≤1)
    (hG : ∀ t≤T,D.G t=namedInstance I)
    (hg : ∀ t≤T,D.g t=namedVector (g t))
    (hl : ∀ t≤T,D.ℓ t=namedVector (ell t))
    (hf : ∀ t≤T,StrictlyInside I (f t)) (hroutes : ∀ t≤T,I.Routes (f t))
    (hres : ∀ t≤T,0<residual I target (f t))
    (hreslog : ∀ t≤T,-10*Real.log (I.m*U)≤Real.log (residual I target (f t)))
    (hpot : ∀ t≤T,potential I a target (f t)≤200*I.m*Real.log (I.m*U))
    (hresidualApprox : ∀ t≤T,ScalarApprox (1+ε) r (residual I target (f t)))
    (hgrad : ∀ t≤T,GradientTolerance (lengths I a (f t))
      (fun e => (r/residual I target (f t))*g t e) (gradient I a target (f t)) (a/2))
    (hlen : ∀ t≤T,VectorApprox 2 (ell t) (lengths I a (f t)))
    (hrange : ∀ t≤T,∀ e,1/(2:ℝ)^(ipmRangeExponent I.m U)≤ell t e ∧ ell t e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hconstant : ∀ t≤T,∀ u≤t,∀ e : Fin I.m,D.NotInsertedBetween e u t → ell t e=ell u e)
    (hcache : ∀ t<T,∀ e : Fin I.m,D.NotInsertedBetween e t (t+1) → stored (t+1) e=stored t e)
    (hclose : ∀ t≤T,∀ e,|ell t e*(f t e-stored t e)|≤1/2) :
    D.HiddenStable T (a/8) (precisionHiddenPsi I.m U) :=
  epoch_hidden_at_range I U _ target a ε D T fstar f stored g ell r hm hU hsize
    hnums hs hF ha ha' he he' hG hg hl hf hroutes hres hreslog hpot hresidualApprox
    hgrad hlen hrange hconstant hcache hclose

end MinCostFlow.IPM.Machine
