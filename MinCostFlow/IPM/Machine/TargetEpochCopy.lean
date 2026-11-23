module

public import MinCostFlow.IPM.Machine.TargetEpochStartupPre
public import MinCostFlow.IPM.Machine.TargetEpochArguments
public import MinCostFlow.IPM.Machine.EpochBaseOutput
public import MinCostFlow.IPM.Machine.EpochCacheCoefficients
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Geometry and values after copying the current flow

The previous flow remains the immutable base of the next epoch.
Its new mutable copy starts just after the exact held residual.
Both views decode to the incoming feasible flow.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On the continuing branch, the new epoch retains its original
source blocks and the exact current flow in both views. -/
theorem targetEpoch_copied_sources {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (old : EpochLayout) (source heap names : ℕ)
    {mem copied : ℕ → ℕ} {f : Fin I.m → ℝ} {a r : ℝ}
    (hframe : ∀ z<heap,copied z=mem z)
    (harrays : ∀ p∈[source,old.cost,old.lower,old.upper],p+I.m*F.limbs≤heap)
    (hAlpha : ScalarAt mem old.alpha F.fmt.limbBits F.limbs F.fmt.precision a)
    (hAlphaEnd : old.alpha+F.limbs≤heap)
    (hLower : ∀ e : Fin I.m,ScalarAt mem (old.lower+e.val*F.limbs) F.fmt.limbBits F.limbs
      F.fmt.precision (I.edge e).lower)
    (hUpper : ∀ e : Fin I.m,ScalarAt mem (old.upper+e.val*F.limbs) F.fmt.limbBits F.limbs
      F.fmt.precision (I.edge e).upper)
    (hCost : ∀ e : Fin I.m,ScalarAt mem (old.cost+e.val*F.limbs) F.fmt.limbBits F.limbs
      0 (I.edge e).cost)
    (hBase : ∀ e : Fin I.m,ScalarAt mem (source+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision (f e))
    (hResidual : ScalarAt copied (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r)
    (hCopy : ∀ e : Fin I.m,ScalarAt copied (epochResidualEnd I.m F.limbs heap+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision (f e)) :
    let flow := epochResidualEnd I.m F.limbs heap
    let rp := heap+(8*I.m+3)*F.limbs
    let L := old.next F I source rp flow (flow+I.m*F.limbs) names
    epochSourcesAt F I L a r copied ∧
      epochVector F I copied L.base=f ∧ epochVector F I copied L.flow=f ∧
      (∀ e : Fin I.m,Num.Valid copied (L.base+e.val*F.limbs) F.fmt.limbBits F.limbs) ∧
      L.residual+F.limbs=L.flow ∧ (∀ p∈[L.base,L.cost,L.lower,L.upper],p+I.m*F.limbs≤L.flow) := by
  let flow := epochResidualEnd I.m F.limbs heap
  let rp := heap+(8*I.m+3)*F.limbs
  let L := old.next F I source rp flow (flow+I.m*F.limbs) names
  have hentry (p : ℕ) (hp : p∈[source,old.cost,old.lower,old.upper]) (e : Fin I.m) :
      p+e.val*F.limbs+F.limbs≤heap :=
    (reported_entry_end p F.limbs e.val I.m e.isLt).trans (harrays p hp)
  have hfix (p : ℕ) (hp : p∈[source,old.cost,old.lower,old.upper]) (e : Fin I.m)
      {x : ℝ} (hs : ScalarAt mem (p+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision x) :
      epochVector F I copied p e=x :=
    (Num.IPM.fixVal_frozen hframe (hentry p hp e)).trans hs.2
  have ha := (Num.IPM.fixVal_frozen hframe hAlphaEnd).trans hAlpha.2
  have hrEnd : rp+F.limbs=flow := by
    simp [rp,flow,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hcost (e : Fin I.m) : Num.intVal copied (old.cost+e.val*F.limbs)
      F.fmt.limbBits F.limbs=(I.edge e).cost := by
    have hfrozen := (Num.IPM.fixVal_frozen (P:=0) hframe (hentry old.cost (by simp) e)).trans (hCost e).2
    simpa [Num.fixVal] using hfrozen
  refine ⟨⟨ha,hResidual.2,fun e => ⟨hfix old.lower (by simp) e (hLower e),hfix old.upper (by simp) e (hUpper e),hcost e⟩⟩,
    funext (fun e => hfix source (by simp) e (hBase e)),funext (fun e => (hCopy e).2),
    fun e => Num.IPM.valid_frozen hframe (hentry source (by simp) e) (hBase e).1,hrEnd,?_⟩
  intro p hp
  exact (harrays p hp).trans (Nat.le_add_right _ _)

end MinCostFlow.IPM.Machine
