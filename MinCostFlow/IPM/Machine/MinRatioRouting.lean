module

public import MinCostFlow.IPM.Machine.MinRatioBridge
public import MinCostFlow.IPM.NamedInstance
import Mathlib.Tactic.Ring

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# Routing on every valid fixed-graph history

Definition 4.5 (page 14) gives a circulation on every Update, even without
hidden stability. Its scalar multiple remains a circulation, including
on failure or when the normalization denominator is zero. Detect adds
zero flow. Hence every represented flow routes the base demands. This
is the routing part of the guarded lower-target acceptance argument of
Chen et al., arXiv:2203.00671v2, Algorithm 7 (page 69).
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Every actual history increment on `P` is a circulation on the fixed graph. -/
theorem minRatio_history_increment_circulation_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (ht : t+1≤T)
    (hG : D.G (t+1)=namedInstance I) :
    IsCirculation I (fun e => minRatioIncrement A.eraseFailure D eta op (t+1) e) := by
  cases hop : op (t+1) with
  | false =>
    intro v
    simp only [minRatioIncrement,hop,Bool.false_eq_true,false_and,ite_false,mul_zero,Finset.sum_const_zero]
  | true =>
    have hc := ((hA D eta op T hvalid hsize hP).1.2.1 t ht hop).1
    rw [hG] at hc
    have hfinite := namedInstance_restrict_circulation I _ hc
    let factor := -(eta (t+1)/(D.G (t+1)).inner (D.g (t+1))
      (minRatioDirection A.eraseFailure D eta op t))
    have hinc (e : Fin I.m) : minRatioIncrement A.eraseFailure D eta op (t+1) e=
        factor*minRatioDirection A.eraseFailure D eta op t e := by
      have he : (e:ℕ)∈(D.G (t+1)).E := by
        rw [hG]
        exact Finset.mem_range.mpr e.2
      simp only [minRatioIncrement,hop,true_and,he,ite_true]
      rfl
    intro v
    simp_rw [hinc]
    calc
      _=factor*(∑ e : Fin I.m,(I.edge e).b v*minRatioDirection A.eraseFailure D eta op t e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _=0 := by rw [hfinite v,mul_zero]

/-- Every actual history increment is a circulation on the fixed graph.
No hidden witness, direction-quality or sign hypothesis is needed. -/
theorem minRatio_history_increment_circulation_upTo (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T)
    (hG : D.G (t+1)=namedInstance I) :
    IsCirculation I (fun e => minRatioIncrement A.eraseFailure D eta op (t+1) e) :=
  minRatio_history_increment_circulation_upTo_on I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T t hvalid hsize (fun _ _ => trivial) ht hG

/-- Every actual history increment is a circulation on the fixed graph.
No hidden witness, direction-quality or sign hypothesis is needed. -/
theorem minRatio_history_increment_circulation (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T)
    (hG : D.G (t+1)=namedInstance I) :
    IsCirculation I (fun e => minRatioIncrement A.eraseFailure D eta op (t+1) e) := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatio_history_increment_circulation_upTo I A κ α Ψ eps (hA.upTo M N) D eta op T t
    hvalid hsize ht hG

/-- Every valid fixed-graph history under `P` preserves the base routing equations. -/
theorem minRatio_history_routes_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) :
    ∀ t≤T,I.Routes (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) := by
  intro t
  induction t with
  | zero =>
    intro _
    simpa only [minRatioFlow_zero,add_zero] using hbase
  | succ t ih =>
    intro ht
    have hp := ih (by omega)
    have hc := minRatio_history_increment_circulation_upTo_on I A κ α Ψ eps hA D eta op T t
      hvalid (namedHistory_bounded hG) hPD ht (hG _ ht)
    intro v
    simp_rw [minRatioFlow_succ]
    have heq (e : Fin I.m) : base e+(minRatioFlow A.eraseFailure D eta op t e+
        minRatioIncrement A.eraseFailure D eta op (t+1) e)=
        (base e+minRatioFlow A.eraseFailure D eta op t e)+minRatioIncrement A.eraseFailure D eta op (t+1) e := by ring
    simp_rw [heq]
    simp only [mul_add,Finset.sum_add_distrib,hc v,add_zero]
    simpa only [mul_add,Finset.sum_add_distrib] using hp v

/-- Every valid fixed-graph history preserves the base routing equations,
including histories from guesses below the optimum. -/
theorem minRatio_history_routes_upTo (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I) :
    ∀ t≤T,I.Routes (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) :=
  minRatio_history_routes_upTo_on I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T base hbase hvalid hG (fun _ _ => trivial)

/-- Every valid fixed-graph history preserves the base routing equations,
including histories from guesses below the optimum. -/
theorem minRatio_history_routes (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I) :
    ∀ t≤T,I.Routes (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) :=
  minRatio_history_routes_upTo I A κ α Ψ eps (hA.upTo I.m I.n) D eta op T base hbase hvalid hG

/-- A completed full-coordinate guard gives a feasible represented flow
on every valid fixed-graph history under `P`. -/
theorem minRatio_history_feasible_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (ht : t≤T)
    (hbox : ∀ e : Fin I.m,((I.edge e).lower:ℝ)≤base e+minRatioFlow A.eraseFailure D eta op t e ∧
      base e+minRatioFlow A.eraseFailure D eta op t e≤(I.edge e).upper) :
    I.IsFeasible (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) :=
  ⟨minRatio_history_routes_upTo_on I A κ α Ψ eps hA D eta op T base hbase hvalid hG hPD t ht,hbox⟩

/-- A completed full-coordinate guard gives a feasible represented flow
on every valid fixed-graph history. Hidden stability is needed for
progress on upper targets, not for soundness of an accepted lower test. -/
theorem minRatio_history_feasible_upTo (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I) (ht : t≤T)
    (hbox : ∀ e : Fin I.m,((I.edge e).lower:ℝ)≤base e+minRatioFlow A.eraseFailure D eta op t e ∧
      base e+minRatioFlow A.eraseFailure D eta op t e≤(I.edge e).upper) :
    I.IsFeasible (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) :=
  minRatio_history_feasible_upTo_on I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T t base hbase hvalid hG (fun _ _ => trivial) ht hbox

/-- A completed full-coordinate guard gives a feasible represented flow
on every valid fixed-graph history. Hidden stability is needed for
progress on upper targets, not for soundness of an accepted lower test. -/
theorem minRatio_history_feasible (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (base : Fin I.m → ℝ) (hbase : I.Routes base)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I) (ht : t≤T)
    (hbox : ∀ e : Fin I.m,((I.edge e).lower:ℝ)≤base e+minRatioFlow A.eraseFailure D eta op t e ∧
      base e+minRatioFlow A.eraseFailure D eta op t e≤(I.edge e).upper) :
    I.IsFeasible (fun e => base e+minRatioFlow A.eraseFailure D eta op t e) :=
  minRatio_history_feasible_upTo I A κ α Ψ eps (hA.upTo I.m I.n) D eta op T t base hbase hvalid
    hG ht hbox

end MinCostFlow.IPM.Machine
