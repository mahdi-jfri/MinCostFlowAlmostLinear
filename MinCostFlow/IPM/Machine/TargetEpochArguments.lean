module

public import MinCostFlow.IPM.Machine.TargetEpoch
import WordRAM.Tactic

/-!
# The stage's computed addresses match the next epoch packet

The stage remembers the beginning of the new coefficient workspace
and its initialized endpoint. Recover the full name list by removing
the budget suffix and the actual number of edge names. The other
arguments are exactly the fixed initial source words.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Define the prepared residual pointer from the old heap. -/
theorem epoch_residual_end_sub (m L heap : ℕ) :
    epochResidualEnd m L heap-L=heap+(8*m+3)*L := by
  have h : epochResidualEnd m L heap=heap+(8*m+3)*L+L := by
    simp [epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  omega

/-- Forward the fifteen coefficient-startup arguments and the exact
three constant blocks used by its full-array scan. -/
theorem targetEpoch_startup_args {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp source inputHeap rp fp coeffHeap : ℕ) (st : State)
    (hfixed : ∀ j<23,st.regs j=(targetEpochPacket L F I tp qp source inputHeap).getD j 0)
    (hR : st.regs 24=rp) (hF : st.regs 23=fp) (hH : st.regs 30=coeffHeap) :
    evalArgs w st targetEpochStartupArgs=
      some ((L.next F I source rp fp coeffHeap 0).startupPacket F I) := by
  simp [targetEpochStartupArgs,EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next,
    evalArgs,Expr.eval,hfixed,hR,hF,hH,targetEpochPacket]

/-- Forward the fifteen coefficient-startup arguments, the three scan constants, and `V` (in `.reg 29`). -/
theorem targetEpoch_startupWithV_args {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp source inputHeap rp fp coeffHeap V : ℕ) (st : State)
    (hfixed : ∀ j<23,st.regs j=(targetEpochPacket L F I tp qp source inputHeap).getD j 0)
    (hR : st.regs 24=rp) (hF : st.regs 23=fp) (hH : st.regs 30=coeffHeap) (hV : st.regs 29=V) :
    evalArgs w st targetEpochStartupArgsWithV=
      some ((L.next F I source rp fp coeffHeap 0).startupPacket F I ++ [V]) := by
  simp [targetEpochStartupArgsWithV,targetEpochStartupArgs,EpochLayout.startupPacket,
    EpochLayout.startPacket,EpochLayout.next,evalArgs,Expr.eval,hfixed,hR,hF,hH,hV,targetEpochPacket]

/-- The actual successful startup's endpoint gives the exact lazy-loop
packet, including the number of iterations equal to the edge count. -/
theorem targetEpoch_complete_args {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp source inputHeap rp fp coeffHeap names initialized : ℕ) (st : State)
    (hfixed : ∀ j<23,st.regs j=(targetEpochPacket L F I tp qp source inputHeap).getD j 0)
    (hR : st.regs 24=rp) (hF : st.regs 23=fp) (hH : st.regs 30=coeffHeap)
    (hinit : st.regs 25=initialized) (hnames : initialized=names+I.m+3)
    (hinitFit : initialized<2^w) (hThree : 3<2^w)
    (hspace : (L.next F I source rp fp coeffHeap names).handle<2^w) :
    evalArgs w st targetEpochCompleteArgs=
      some ((L.next F I source rp fp coeffHeap names).packet F I initialized++[I.m]) := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision L.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision L.exponent
  change coeffHeap+(la+ga)<2^w at hspace
  have hsum : la+ga<2^w := by omega
  have hg : coeffHeap+la<2^w := by omega
  have hminus : initialized-3<2^w := by omega
  have hn : names<2^w := by omega
  have heq : initialized-3-I.m=names := by omega
  simp [targetEpochCompleteArgs,EpochLayout.packet,EpochLayout.next,evalArgs,Expr.eval,
    BinOp.eval,hfixed,hR,hF,hH,hinit,targetEpochPacket,hThree,heq,hn,
    show coeffHeap+(la+ga)<2^w from hspace,hsum,hg,hminus,la,ga]

end MinCostFlow.IPM.Machine
