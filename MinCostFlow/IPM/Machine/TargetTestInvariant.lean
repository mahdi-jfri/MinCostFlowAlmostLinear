module

public import MinCostFlow.IPM.Machine.TargetTestLayout
public import MinCostFlow.IPM.Machine.TargetEpochStatic
public import MinCostFlow.IPM.Machine.TargetEpochBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The bounded target test's current flow and budget

At the start of a stage the current explicit flow is feasible and in
range. Under the original upper-target promise its potential pays for
each previously completed epoch. The last possible stage must
terminate on a promised target.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The number of stages includes one final residual test after the
last full epoch allowed by the rounded iteration budget. -/
def targetTestLimit (m U k : ℕ) : ℕ :=
  dyadicEpochLimit (m.size+U.size) k (Num.IPM.alphaExponent m U)+1

/-- The finite test's current fixed-point invariant and conditional
potential accounting. -/
def TargetTestInvariant {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U k : ℕ) (L : EpochLayout) (tp qp src heap space : ℕ)
    (target : ℝ) (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  let limit := targetTestLimit I.m U k
  let flow := epochVector F I st.mem (st.regs 20)
  let initial := epochVector F I mem src
  let a := Num.IPM.alphaPrime I.m U
  let q := (1/(2:ℝ)^k)*a/32
  st.regs 26=i ∧ st.regs 23=limit ∧
  (∀ j<23,st.regs j=(targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21)).getD j 0) ∧
  (∀ z∈targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21),z<2^w) ∧
  heap≤st.regs 21 ∧ st.regs 21≤heap+i*space ∧
  (∀ z<heap,st.mem z=mem z) ∧ ZeroFrom st.mem (st.regs 21) ∧
  TargetStageFlow F I L.exponent (st.regs 20) (st.regs 21) st.mem ∧
  (TargetStagePromise I U target initial →
    potential I a target flow≤potential I a target initial-(I.m:ℝ)*(i:ℝ)*q^2/2000) ∧
  (i=limit → ¬TargetStagePromise I U target initial) ∧
  (0 < i → 1/4<residual I target initial) ∧
  (i=0 → flow=initial)

/-- The returned record has a binary flag and retains the original
memory. On success it points at an exact feasible flow within a
quarter of the target. Failure contradicts the original promise. -/
def TargetTestResult {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U E src heap out : ℕ) (target : ℝ) (mem final : ℕ → ℕ) : Prop :=
  let bit := final (out-1)
  let ptr := final (out-2)
  heap+2≤out ∧ out<2^w ∧ ZeroFrom final out ∧ (∀ z<heap,final z=mem z) ∧ bit≤1 ∧
  (bit=0 → 1/4<residual I target (epochVector F I mem src) ∧
    ¬TargetStagePromise I U target (epochVector F I mem src)) ∧
  (bit=1 → TargetStageFlow F I E ptr out final ∧ residual I target (epochVector F I final ptr)≤1/4)

/-- The paid potential decrease preserves the promise's potential
upper bound for the next stage. -/
theorem targetTest_promise_at_flow (I : Instance) (U i : ℕ)
    (a q target : ℝ) (f flow : Fin I.m → ℝ)
    (ha : a=Num.IPM.alphaPrime I.m U)
    (hp : TargetStagePromise I U target f)
    (hcost : potential I a target flow≤potential I a target f-(I.m:ℝ)*(i:ℝ)*q^2/2000) :
    TargetStagePromise I U target flow := by
  subst a
  have hnonneg : 0≤(I.m:ℝ)*(i:ℝ)*q^2/2000 := by positivity
  exact ⟨hp.1,by linarith only [hcost,hnonneg,hp.2]⟩

/-- At the last stage, a nonterminal residual contradicts the
rounded budget on a promised target. -/
theorem targetTest_last_stage_terminal (I : Instance) (U k : ℕ)
    (target : ℝ) (f flow : Fin I.m → ℝ)
    (hm : 0<I.m) (hsize : 2≤I.m*U) (hflow : StrictlyInside I flow)
    (hr : 1/4<residual I target flow) (hp : TargetStagePromise I U target f)
    (hcost : let a := Num.IPM.alphaPrime I.m U
      let q := (1/(2:ℝ)^k)*a/32
      potential I a target flow≤potential I a target f-
        (I.m:ℝ)*(dyadicEpochLimit (I.m.size+U.size) k (Num.IPM.alphaExponent I.m U):ℝ)*q^2/2000) :
    False := by
  dsimp only at hcost
  have hq : (1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/32=
      1/(2:ℝ)^(k+Num.IPM.alphaExponent I.m U+5) := by
    rw [Num.IPM.alphaPrime,pow_add,pow_add]
    norm_num
    ring
  rw [hq] at hcost
  exact target_epoch_budget_exhausted I U k (Num.IPM.alphaExponent I.m U) target
    (Num.IPM.alphaPrime I.m U) f flow hm hsize hflow hr hp.2 hcost

end MinCostFlow.IPM.Machine
