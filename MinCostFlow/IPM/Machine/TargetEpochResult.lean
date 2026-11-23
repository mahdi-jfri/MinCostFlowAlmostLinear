module

public import MinCostFlow.IPM.Machine.TargetEpochTerminal
public import MinCostFlow.IPM.Machine.TargetEpochSetup
public import MinCostFlow.IPM.Machine.EpochBaseOutput
public import MinCostFlow.IPM.Machine.EpochCacheCoefficients

/-!
# Result of one target stage

The status word distinguishes rejection, a flow within a quarter of
the target, and one further epoch. Only the continuing path needs the
strict guarded slack range to use as its next input.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decoded fixed-point flow and strict round-to-round slack bounds. -/
def TargetStageFlow {w : ℕ} (F : MinRatioFormat w) (I : Instance) (E source heap : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  source+I.m*F.limbs≤heap ∧ I.IsFeasible (epochVector F I mem source) ∧
  ∀ e : Fin I.m,Num.Valid mem (source+e.val*F.limbs) F.fmt.limbBits F.limbs ∧
    (1/(2:ℝ)^E<(I.edge e).upper-epochVector F I mem source e ∧
      (I.edge e).upper-epochVector F I mem source e<(2:ℝ)^E) ∧
    (1/(2:ℝ)^E<epochVector F I mem source e-(I.edge e).lower ∧
      epochVector F I mem source e-(I.edge e).lower<(2:ℝ)^E)

/-- The upper-target promise used during a run. The initial potential
bound is retained across all continuing stages. -/
def TargetStagePromise (I : Instance) (U : ℕ) (target : ℝ) (f : Fin I.m → ℝ) : Prop :=
  (∃ g, I.IsFeasible g ∧ I.cost g≤target) ∧
  potential I (Num.IPM.alphaPrime I.m U) target f≤200*I.m*Real.log (I.m*(U:ℝ))

/-- An actual target-stage postcondition. The address record describes
the stored flow, and the three outcomes retain their own exact facts. -/
def TargetStageResult {w : ℕ} (F : MinRatioFormat w) (I : Instance) (U E : ℕ)
    (κ target : ℝ) (source heap out : ℕ) (mem final : ℕ → ℕ) : Prop :=
  let status := final (out-1)
  let ptr := final (out-2)
  heap+2≤out ∧ out<2^w ∧ ZeroFrom final out ∧ (∀ z<heap,final z=mem z) ∧
  status≤2 ∧
  (status=0 → 1/4<residual I target (epochVector F I mem source) ∧
    ¬TargetStagePromise I U target (epochVector F I mem source)) ∧
  (status=1 → TargetStageFlow F I E ptr out final ∧ residual I target (epochVector F I final ptr)≤1/4) ∧
  (status=2 → TargetStageFlow F I E ptr out final ∧
    1/4<residual I target (epochVector F I mem source) ∧
    (TargetStagePromise I U target (epochVector F I mem source) →
      potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I final ptr)≤
        potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem source)-
          (I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000))

/-- An unchanged prefix containing the whole flow preserves both its
encoding and all slack inequalities. -/
theorem TargetStageFlow.frozen {w : ℕ} {F : MinRatioFormat w} {I : Instance} {E source heap next : ℕ}
    {mem final : ℕ → ℕ} (h : TargetStageFlow F I E source heap mem)
    (hframe : ∀ z<heap,final z=mem z) (hle : heap≤next) :
    TargetStageFlow F I E source next final := by
  have hend (e : Fin I.m) : source+e.val*F.limbs+F.limbs≤heap := by
    have he := Nat.mul_le_mul_right F.limbs (Nat.succ_le_of_lt e.isLt)
    calc
      source+e.val*F.limbs+F.limbs = source+(e.val+1)*F.limbs := by rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
      _ ≤ heap := (Nat.add_le_add_left he source).trans h.1
  have hflow : epochVector F I final source=epochVector F I mem source := by
    funext e
    exact Num.IPM.fixVal_frozen hframe (hend e)
  refine ⟨h.1.trans hle,by rw [hflow]; exact h.2.1,?_⟩
  intro e
  have hs := h.2.2 e
  rw [hflow]
  exact ⟨Num.IPM.valid_frozen hframe (hend e) hs.1,hs.2⟩

end MinCostFlow.IPM.Machine
