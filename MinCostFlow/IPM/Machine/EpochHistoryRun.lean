module

public import MinCostFlow.IPM.Machine.EpochHistoryAccuracy
public import MinCostFlow.IPM.Machine.DyadicResidualDrift

/-!
# Routing, potential and residual along the actual history

The dyadic progress theorem applies to the even stages, each of which
adds one rounded circulation. An odd stage is a Detect with zero flow
increment. Thus all inputs of an attempted pair use flows from the
already accepted prefix.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- The odd stages of a machine epoch are Detect operations. -/
def EpochDetectSchedule (op : ℕ → Bool) (i : ℕ) : Prop :=
  ∀ j< i,op (2*j+1)=false

/-- The accepted pairs satisfy the rounded form of Lemma 9.3. The
unchanged Detect stage is skipped when applying the progress theorem. -/
def EpochDyadicPrefix (I : Instance) (U : ℕ) (target q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (i : ℕ) : Prop :=
  ∀ j< i,DyadicAdmissibleStep I U target q
    (epochHistoryFlow I A D eta op (2*j) base)
    (epochHistoryFlow I A D eta op (2*(j+1)) base)

/-- The next pair adds one Detect to the schedule. -/
theorem epochDetectSchedule_append (op : ℕ → Bool) (i : ℕ) (h : EpochDetectSchedule op i) :
    EpochDetectSchedule (appendHistoryIterationOp op (2*i)) (i+1) := by
  intro j hj
  by_cases hOld : j< i
  · simpa only [appendHistoryIterationOp,Function.update_of_ne (by omega : 2*j+1≠2*i+1+1),
      Function.update_of_ne (by omega : 2*j+1≠2*i+1)] using h j hOld
  · have heq : j=i := by omega
    subst j
    simp only [appendHistoryIterationOp,Function.update_of_ne (by omega : 2*i+1≠2*i+1+1),
      Function.update_self]

/-- At an input stage, the preceding even flow equals its current flow.
This includes the last attempted Update, since Detect adds zero flow. -/
theorem epochInputFlow_eq_even (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (i t : ℕ) (base : Fin I.m → ℝ)
    (hs : EpochDetectSchedule op (i+1)) (ht : t≤2*i+1+1) :
    epochInputFlow I A D eta op t base=epochHistoryFlow I A D eta op (2*((t-1)/2)) base := by
  let j := (t-1)/2
  change epochInputFlow I A D eta op t base=epochHistoryFlow I A D eta op (2*j) base
  have hj : j≤ i := by omega
  by_cases he : t-1=2*j
  · unfold epochInputFlow
    rw [he]
  · have ho : t-1=2*j+1 := by omega
    have hz := hs j (by omega)
    funext e
    unfold epochInputFlow epochHistoryFlow
    rw [ho,minRatioFlow_succ]
    simp only [minRatioIncrement,hz,Bool.false_eq_true,false_and,ite_false,add_zero]

/-- Earlier accepted steps are preserved even if the newly appended
attempt has not been proved admissible. -/
theorem epochDyadicPrefix_append_past (I : Instance) (U : ℕ) (target q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (i : ℕ) (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hold : EpochDyadicPrefix I U target q A D eta op base i) :
    EpochDyadicPrefix I U target q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base i := by
  intro j hj
  have hpast (t : ℕ) (ht : t≤2*i) :
      epochHistoryFlow I A (appendHistoryIteration D (2*i) es g ell)
        (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) t base=
        epochHistoryFlow I A D eta op t base := by
    funext e
    unfold epochHistoryFlow
    rw [appendHistoryIteration_past_flow A.eraseFailure D eta op (2*i) es g ell actual t e ht]
  rw [hpast _ (by omega),hpast _ (by omega)]
  exact hold j hj

/-- Appending an admissible actual Update adds one step to the rounded
IPM run. -/
theorem epochDyadicPrefix_append (I : Instance) (U : ℕ) (target q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (i : ℕ) (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hold : EpochDyadicPrefix I U target q A D eta op base i)
    (hstep : let D' := appendHistoryIteration D (2*i) es g ell
             let eta' := appendHistoryIterationEta eta (2*i) actual
             let op' := appendHistoryIterationOp op (2*i)
             DyadicAdmissibleStep I U target q (epochHistoryFlow I A D' eta' op' (2*i) base)
               (epochHistoryFlow I A D' eta' op' (2*i+1+1) base)) :
    EpochDyadicPrefix I U target q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base (i+1) := by
  intro j hj
  by_cases hOld : j< i
  · exact epochDyadicPrefix_append_past I U target q A D eta op base i es g ell actual hold j hOld
  · have heq : j=i := by omega
    subst j
    simpa only [show 2*i+1+1=2*(i+1) by omega] using hstep

/-- At stage zero no implicit flow has been added. -/
theorem epochHistoryFlow_zero (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (base : Fin I.m → ℝ) :
    epochHistoryFlow I A D eta op 0 base=base := by
  funext e
  simp only [epochHistoryFlow,minRatioFlow_zero,add_zero]

/-- The potential and held-residual consequences of a certified run of
at most one epoch, at every accepted even stage. -/
theorem epochDyadicPrefix_state (I : Instance) (U i : ℕ) (target q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (hm : 0<I.m) (hi : i≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hq' : q≤1/2)
    (hf : StrictlyInside I base) (hroute : I.Routes base) (hr : 0<residual I target base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : EpochDyadicPrefix I U target q A D eta op base i) :
    ∀ j≤ i,
      let f := epochHistoryFlow I A D eta op (2*j) base
      I.Routes f ∧ StrictlyInside I f ∧
      potential I (Num.IPM.alphaPrime I.m U) target f≤200*I.m*Real.log (I.m*(U:ℝ)) ∧
      ScalarApprox (1+q/4) (residual I target base) (residual I target f) := by
  let f := fun j => epochHistoryFlow I A D eta op (2*j) base
  have hzero : f 0=base := epochHistoryFlow_zero I A D eta op base
  have hrun := dyadic_run_budget I U i target q f hm hsize hnums hq hq'
    (hzero.symm ▸ hf) (hzero.symm ▸ hroute) (hzero.symm ▸ hr) (hzero.symm ▸ hpot) hsteps
  have hdrift := dyadic_run_residual_approx I U i target q f hm hsize hi hnums hq hq'
    (hzero.symm ▸ hf) (hzero.symm ▸ hroute) (hzero.symm ▸ hr) (hzero.symm ▸ hpot) hsteps
  rw [hzero] at hdrift
  intro j hj
  exact ⟨(hrun j hj).1,(hrun j hj).2.1,(hrun j hj).2.2.2,hdrift j hj⟩

end MinCostFlow.IPM.Machine
