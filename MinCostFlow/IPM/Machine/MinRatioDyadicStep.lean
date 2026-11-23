module

public import MinCostFlow.IPM.Machine.DyadicRun
import MinCostFlow.IPM.Machine.DyadicMovement
public import MinCostFlow.IPM.Machine.MinRatioBridge
import MinCostFlow.IPM.NamedInstance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# The min-ratio history gives an actual dyadic-request step

Definition 4.5 (page 14) supplies a circulation and its ratio bound on a
hidden-stable prefix. Restrict its named edges to the fixed IPM graph.
The machine's actual normalization is used in the history increment.
Combining these facts gives the step relation used in the adapted Lemma
9.3 of Chen et al., arXiv:2203.00671v2 (page 71), without assuming the
returned direction's quality as a separate input hypothesis.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The exact dyadic request and the parameter's permitted scalar interval
give the relative rounding factor used by the dyadic step relation. -/
theorem normalization_factor_of_dyadic_request {q actual : ℝ} (hq : 0<q)
    (hn : NormalizationWithin ((25/32:ℝ)*q^2/50) actual) :
    ∃ r : ℝ,((1/2:ℝ)≤r ∧ r≤2) ∧ actual=((25/32:ℝ)*r)*q^2/50 := by
  have hrequest : 0<(25/32:ℝ)*q^2/50 := by positivity
  refine ⟨actual/((25/32:ℝ)*q^2/50),hn.div_bounds hrequest,?_⟩
  field_simp [hq.ne']

/-- A hidden-stable actual history Update under `P` cannot fail and gives a dyadic
admissible step. -/
theorem minRatio_history_dyadic_step_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (I : Instance) (U : ℕ) (F κ Ψ eps : ℝ) (A : MinRatioDataStructureWithFailure)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8) Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base g l : Fin I.m → ℝ) (s : ℝ) (hκ : 0<κ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (ht : t+1≤T) (hop : op (t+1)=true)
    (hG : D.G (t+1)=namedInstance I)
    (hgNames : D.g (t+1)=namedVector g) (hlNames : D.ℓ (t+1)=namedVector l)
    (hhidden : D.HiddenStable (t+1) (Num.IPM.alphaPrime I.m U/8) Ψ)
    (hs : (3/4:ℝ)≤s ∧ s≤4/3)
    (hg : GradientTolerance
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      (fun e => s*g e)
      (gradient I (Num.IPM.alphaPrime I.m U) F (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      ((κ*Num.IPM.alphaPrime I.m U/32)/16))
    (hl : VectorApprox 2 l
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)))
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (t+1))) :
    (minRatioFailureDirection A D eta op t).isSome=true ∧
      DyadicAdmissibleStep I U F (κ*Num.IPM.alphaPrime I.m U/32)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op (t+1) e) ∧
      (D.G (t+1)).lnorm (D.ℓ (t+1))
        (minRatioIncrement A.eraseFailure D eta op (t+1))≤(κ*Num.IPM.alphaPrime I.m U/32)/128 := by
  have ha : 0<Num.IPM.alphaPrime I.m U := by unfold Num.IPM.alphaPrime; positivity
  have hq : 0<κ*Num.IPM.alphaPrime I.m U/32 := div_pos (mul_pos hκ ha) (by norm_num)
  obtain ⟨r,hr,heta⟩ := normalization_factor_of_dyadic_request hq hnorm
  have hspec := ((hA D eta op T hvalid hsize hP).1.2.1 t ht hop)
  have hc : IsCirculation I (fun e => minRatioDirection A.eraseFailure D eta op t e) := by
    apply namedInstance_restrict_circulation I _
    rw [← hG]
    exact hspec.1
  have hratio := hspec.2 hhidden
  rw [hG,hgNames,hlNames,namedInstance_inner_restrict,
    namedInstance_lnorm_restrict I l _ (fun e => (hl e).1)] at hratio
  have hquality : dot g (fun e => minRatioDirection A.eraseFailure D eta op t e)/
      weightedLength l (fun e => minRatioDirection A.eraseFailure D eta op t e)≤
      -4*(κ*Num.IPM.alphaPrime I.m U/32) := by
    convert hratio using 1
    ring
  have hlen0 : 0≤weightedLength l (fun e => minRatioDirection A.eraseFailure D eta op t e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0<weightedLength l (fun e => minRatioDirection A.eraseFailure D eta op t e) := by
    by_contra hh
    have hz := le_antisymm (not_lt.mp hh) hlen0
    rw [hz,div_zero] at hquality
    linarith only [hquality,hq]
  have hneg : dot g (fun e => minRatioDirection A.eraseFailure D eta op t e)<0 := by
    have hh := (div_le_iff₀ hlen).mp hquality
    exact lt_of_le_of_lt hh (mul_neg_of_neg_of_pos (by linarith only [hq]) hlen)
  let d : Fin I.m → ℝ := fun e => minRatioDirection A.eraseFailure D eta op t e
  have hinc (e : Fin I.m) :
      minRatioIncrement A.eraseFailure D eta op (t+1) e=
        (((25/32:ℝ)*r)*(κ*Num.IPM.alphaPrime I.m U/32)^2/(50*|dot g d|))*d e := by
    have he : (e:ℕ)∈(D.G (t+1)).E := by
      rw [hG]
      exact Finset.mem_range.mpr e.2
    simp only [minRatioIncrement,hop,true_and,he,ite_true]
    rw [hG,hgNames,namedInstance_inner_restrict,heta,show _=dot g d from rfl,abs_of_neg hneg]
    dsimp only [d]
    field_simp [hneg.ne]
  refine ⟨(hA D eta op T hvalid hsize hP).2 t ht hop hhidden,
    ⟨g,l,d,s,r,hs,hr,hg,hl,hc,hquality,?_⟩,?_⟩
  · funext e
    rw [minRatioFlow_succ,hinc,add_assoc]
  · rw [hG,hlNames,namedInstance_lnorm_restrict I l _ (fun e => (hl e).1)]
    rw [show (fun e : Fin I.m => minRatioIncrement A.eraseFailure D eta op (t+1) e)=_ from funext hinc]
    exact dyadic_requested_movement _ r g l d hq hr hquality

/-- A hidden-stable actual history Update cannot fail and gives a dyadic
admissible step. Its circulation and ratio are derived from the exact
Definition 4.5 parameter specification. The normalization interval is
that decoded from the machine's actual doubled-width output block. -/
theorem minRatio_history_dyadic_step_upTo (I : Instance) (U : ℕ) (F κ Ψ eps : ℝ)
    (A : MinRatioDataStructureWithFailure)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base g l : Fin I.m → ℝ) (s : ℝ) (hκ : 0<κ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T) (hop : op (t+1)=true)
    (hG : D.G (t+1)=namedInstance I)
    (hgNames : D.g (t+1)=namedVector g) (hlNames : D.ℓ (t+1)=namedVector l)
    (hhidden : D.HiddenStable (t+1) (Num.IPM.alphaPrime I.m U/8) Ψ)
    (hs : (3/4:ℝ)≤s ∧ s≤4/3)
    (hg : GradientTolerance
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      (fun e => s*g e)
      (gradient I (Num.IPM.alphaPrime I.m U) F (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      ((κ*Num.IPM.alphaPrime I.m U/32)/16))
    (hl : VectorApprox 2 l
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)))
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (t+1))) :
    (minRatioFailureDirection A D eta op t).isSome=true ∧
      DyadicAdmissibleStep I U F (κ*Num.IPM.alphaPrime I.m U/32)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op (t+1) e) ∧
      (D.G (t+1)).lnorm (D.ℓ (t+1))
        (minRatioIncrement A.eraseFailure D eta op (t+1))≤(κ*Num.IPM.alphaPrime I.m U/32)/128 :=
  minRatio_history_dyadic_step_upTo_on I U F κ Ψ eps A (hA.upToOn (P := fun _ _ => True)) D eta op T t
    base g l s hκ hvalid hsize (fun _ _ => trivial) ht hop hG hgNames hlNames hhidden hs hg hl hnorm

/-- A hidden-stable actual history Update cannot fail and gives a dyadic
admissible step. Its circulation and ratio are derived from the exact
Definition 4.5 parameter specification. The normalization interval is
that decoded from the machine's actual doubled-width output block. -/
theorem minRatio_history_dyadic_step (I : Instance) (U : ℕ) (F κ Ψ eps : ℝ)
    (A : MinRatioDataStructureWithFailure)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base g l : Fin I.m → ℝ) (s : ℝ) (hκ : 0<κ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=true)
    (hG : D.G (t+1)=namedInstance I)
    (hgNames : D.g (t+1)=namedVector g) (hlNames : D.ℓ (t+1)=namedVector l)
    (hhidden : D.HiddenStable (t+1) (Num.IPM.alphaPrime I.m U/8) Ψ)
    (hs : (3/4:ℝ)≤s ∧ s≤4/3)
    (hg : GradientTolerance
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      (fun e => s*g e)
      (gradient I (Num.IPM.alphaPrime I.m U) F (fun e => base e+minRatioFlow A.eraseFailure D eta op t e))
      ((κ*Num.IPM.alphaPrime I.m U/32)/16))
    (hl : VectorApprox 2 l
      (lengths I (Num.IPM.alphaPrime I.m U) (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)))
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (t+1))) :
    (minRatioFailureDirection A D eta op t).isSome=true ∧
      DyadicAdmissibleStep I U F (κ*Num.IPM.alphaPrime I.m U/32)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op t e)
        (fun e => base e+minRatioFlow A.eraseFailure D eta op (t+1) e) ∧
      (D.G (t+1)).lnorm (D.ℓ (t+1))
        (minRatioIncrement A.eraseFailure D eta op (t+1))≤(κ*Num.IPM.alphaPrime I.m U/32)/128 := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatio_history_dyadic_step_upTo I U F κ Ψ eps A (hA.upTo M N) D eta op T t
    base g l s hκ hvalid hsize ht hop hG hgNames hlNames hhidden hs hg hl hnorm

end MinCostFlow.IPM.Machine
