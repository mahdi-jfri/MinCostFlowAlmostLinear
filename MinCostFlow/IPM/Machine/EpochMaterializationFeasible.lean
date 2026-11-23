module

public import MinCostFlow.IPM.Machine.EpochMaterialization
public import MinCostFlow.IPM.Machine.MinRatioRouting

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# A materialized epoch flow is feasible

The unconditional min-ratio history specification preserves routing on
all target guesses. Full-coordinate materialization checks both strict
capacity bounds. Combining those facts proves feasibility of the actual
stored fixed-point flow, before the exact residual procedure is called.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The stored flow after a successful full materialization under `P` is feasible
on every valid fixed-graph history. -/
theorem epoch_materialized_feasible_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (ht : t≤T)
    {q base lo up f c r a ld gd : ℕ} {mem : ℕ → ℕ}
    (hbase : I.Routes (fun e => Num.fixVal mem (base+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision))
    (hlo : ∀ e : Fin I.m,Num.fixVal mem (lo+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).lower)
    (hup : ∀ e : Fin I.m,Num.fixVal mem (up+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).upper)
    (hcache : ∀ e∈(namedInstance I).E,
      reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
        I.m q base lo up f c r a ld gd e mem) :
    I.IsFeasible (fun e => Num.fixVal mem (f+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision) := by
  have he (e : Fin I.m) : (e:ℕ)∈(namedInstance I).E := Finset.mem_range.mpr e.2
  have hflow (e : Fin I.m) : Num.fixVal mem (f+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e :=
    reportedCachePost_history_flow_upTo_on F A κ α Ψ eps hA D eta op T t hvalid (namedHistory_bounded hG)
      hPD ht (by rw [hG t ht]; exact he e) (hcache e (he e))
  have hbox (e : Fin I.m) : ((I.edge e).lower:ℝ)≤
      Num.fixVal mem (base+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e ∧
      Num.fixVal mem (base+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op t e≤(I.edge e).upper := by
    have hin := (hcache e (he e)).2.2.2.2.2.2
    rw [hlo e,hup e,hflow e] at hin
    exact ⟨hin.1.le,hin.2.le⟩
  have hh := minRatio_history_feasible_upTo_on I A κ α Ψ eps hA D eta op T t _ hbase hvalid hG hPD ht hbox
  have heq : (fun e : Fin I.m => Num.fixVal mem (f+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision)=
      (fun e : Fin I.m => Num.fixVal mem (base+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision+minRatioFlow A.eraseFailure D eta op t e) :=
    funext hflow
  exact heq ▸ hh

/-- The stored flow after a successful full materialization is feasible
on every valid fixed-graph history, including guesses below the optimum.
The strict bounds come from actual coordinate guards. -/
theorem epoch_materialized_feasible_upTo {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I) (ht : t≤T)
    {q base lo up f c r a ld gd : ℕ} {mem : ℕ → ℕ}
    (hbase : I.Routes (fun e => Num.fixVal mem (base+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision))
    (hlo : ∀ e : Fin I.m,Num.fixVal mem (lo+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).lower)
    (hup : ∀ e : Fin I.m,Num.fixVal mem (up+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).upper)
    (hcache : ∀ e∈(namedInstance I).E,
      reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
        I.m q base lo up f c r a ld gd e mem) :
    I.IsFeasible (fun e => Num.fixVal mem (f+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision) :=
  epoch_materialized_feasible_upTo_on F I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    D eta op T t hvalid hG (fun _ _ => trivial) ht hbase hlo hup hcache

/-- The stored flow after a successful full materialization is feasible
on every valid fixed-graph history, including guesses below the optimum.
The strict bounds come from actual coordinate guards. -/
theorem epoch_materialized_feasible {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I) (ht : t≤T)
    {q base lo up f c r a ld gd : ℕ} {mem : ℕ → ℕ}
    (hbase : I.Routes (fun e => Num.fixVal mem (base+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision))
    (hlo : ∀ e : Fin I.m,Num.fixVal mem (lo+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).lower)
    (hup : ∀ e : Fin I.m,Num.fixVal mem (up+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision=(I.edge e).upper)
    (hcache : ∀ e∈(namedInstance I).E,
      reportedCachePost F A (minRatioState A.eraseFailure D eta op t)
        I.m q base lo up f c r a ld gd e mem) :
    I.IsFeasible (fun e => Num.fixVal mem (f+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision) :=
  epoch_materialized_feasible_upTo F I A κ α Ψ eps (hA.upTo I.m I.n) D eta op T t hvalid hG ht
    hbase hlo hup hcache

end MinCostFlow.IPM.Machine
