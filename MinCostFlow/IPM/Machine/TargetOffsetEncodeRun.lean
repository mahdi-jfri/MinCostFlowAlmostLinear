module

public import MinCostFlow.IPM.Machine.TargetSearch
public import MinCostFlow.IPM.Machine.TargetTestLayout
import WordRAM.Tactic
import Mathlib.Tactic.IntervalCases

/-!
# The actual offset encoding call

The numerical test receives the exact new target block and its
advanced heap. All other test operands are forwarded unchanged.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Execute the signed target write and the two caller register updates from a compatible state,
preserving all caller registers other than `6`, `21`, and `25`. -/
theorem targetOffsetEncode_runs_of_regs {w guess : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (offset qp source heap limit radius : ℕ) (mem : ℕ → ℕ)
    (init : State) (ω : ℕ → Bool) {p : Program}
    (hguess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (hwords : ∀ z∈targetOffsetPacket L F I offset qp source heap limit radius,z<2^w)
    (hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem)
    (hspace : heap+3*F.limbs<2^w)
    (hmem : init.mem=mem)
    (hregs : ∀ j<25,init.regs j=(targetOffsetPacket L F I offset qp source heap limit radius).getD j 0) :
    let n := offsetTarget radius offset
    let target := heap+2*F.limbs
    let next := heap+3*F.limbs
    ∃ st c,
      Runs w p ω (targetOffsetEncode guess) init .normal st c ∧
      (∀ j<24,st.regs j=((targetEpochPacket L F I target qp source next)++[limit]).getD j 0) ∧
      (∀ j,j≠6 → j≠21 → j≠25 → st.regs j=init.regs j) ∧
      (∀ z<heap,st.mem z=mem z) ∧ ZeroFrom st.mem next ∧
      ScalarAt st.mem target F.fmt.limbBits F.limbs F.fmt.precision (n:ℝ) ∧ c≤100*F.limbs+260 := by
  dsimp only
  subst mem
  let args := [offset,radius,F.limbs,F.fmt.precision,heap]
  let target := heap+2*F.limbs
  let next := heap+3*F.limbs
  have hArgs : ∀ z∈args,z<2^w := by
    intro z hz
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    all_goals exact hwords _ (by simp [targetOffsetPacket,targetEpochPacket])
  obtain ⟨body,hbody,o,st,c,hRun,hout,hcost⟩ := hguess args init.mem init.pos ω hArgs hpre
  have hOut : (fixedIntegerBlockContract w F.fmt.limbBits).post
      (encodeSignedPair (offsetTarget radius offset)++[F.limbs,F.fmt.precision,heap]) init.mem o.value st.mem := hout
  have hEnd : o.value=next := hOut.2
  let mid : State := ⟨st.mem,Function.update init.regs 25 next,st.pos⟩
  let stored : State := {mid with regs:=Function.update mid.regs 6 target}
  let final : State := {stored with regs:=Function.update stored.regs 21 next}
  have hr6 : init.regs 6=offset := (hregs 6 (by decide)).trans (by simp [targetOffsetPacket,targetEpochPacket])
  have hr24 : init.regs 24=radius := (hregs 24 (by decide)).trans (by simp [targetOffsetPacket,targetEpochPacket,targetEpochPacket_length])
  have hr15 : init.regs 15=F.limbs := (hregs 15 (by decide)).trans (by simp [targetOffsetPacket,targetEpochPacket])
  have hr16 : init.regs 16=F.fmt.precision := (hregs 16 (by decide)).trans (by simp [targetOffsetPacket,targetEpochPacket])
  have hr21 : init.regs 21=heap := (hregs 21 (by decide)).trans (by simp [targetOffsetPacket,targetEpochPacket])
  have hEvalArgs : evalArgs w init [.reg 6,.reg 24,.reg 15,.reg 16,.reg 21]=some args := by
    refine evalArgs_cons (by simp [Expr.eval,hr6,hArgs offset (by simp [args])]) ?_
    refine evalArgs_cons (by simp [Expr.eval,hr24,hArgs radius (by simp [args])]) ?_
    refine evalArgs_cons (by simp [Expr.eval,hr15,hArgs F.limbs (by simp [args])]) ?_
    refine evalArgs_cons (by simp [Expr.eval,hr16]) ?_
    exact evalArgs_cons (by simp [Expr.eval,hr21]) rfl
  have hCall : Runs w p ω (.call 25 guess [.reg 6,.reg 24,.reg 15,.reg 16,.reg 21]) init .normal mid (c+6) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,o,st,c,hEvalArgs,hbody,hRun,rfl,?_,by change c+6=5+c+1; omega⟩
    cases st
    simp [mid,hEnd]
  have h2 : next-F.limbs=target := by
    dsimp only [next,target]
    omega
  have hr15mid : mid.regs 15=F.limbs := by simp [mid,hr15]
  have hr25mid : mid.regs 25=next := by simp [mid]
  have hLoad : Runs w p ω (.assign 6 (.bin .sub (.reg 25) (.reg 15))) mid .normal stored 4 := by
    apply runs_assign_iff.mpr
    refine ⟨target,?_,rfl,rfl,rfl⟩
    rw [← h2]
    exact Expr.eval_sub (by simp [Expr.eval,hr25mid]) (by simp [Expr.eval,hr15mid]) hspace
  have hHeap : Runs w p ω (.assign 21 (.reg 25)) stored .normal final 2 :=
    runs_assign_iff.mpr ⟨next,by simp [stored,mid,Expr.eval],rfl,rfl,rfl⟩
  have hCost : c≤100*F.limbs+240 := hcost
  refine ⟨final,c+14,?_,?_,?_,hOut.1.2.2.1,?_,?_,by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,c+6,7,hCall,
      runs_seq_iff.mpr (Or.inr ⟨stored,4,2,hLoad,hHeap,rfl⟩),by omega⟩)
  · intro j hj
    have h0 : init.regs j=(targetOffsetPacket L F I offset qp source heap limit radius).getD j 0 :=
      hregs j (by omega)
    interval_cases j <;> simp [final,stored,mid,h0,targetOffsetPacket,targetEpochPacket,target,next]
  · intro j h6 h21 h25
    simp [final,stored,mid,h6,h21,h25]
  · change ZeroFrom st.mem next
    rw [← hEnd]
    exact hOut.1.2.2.2.1
  · have hv := hOut.1.2.2.2.2
    change ScalarAt st.mem target F.fmt.limbBits F.limbs F.fmt.precision
      (Num.decodeIntWords _ _ : ℝ) at hv
    simpa only [encodeSignedPair,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ,
      Num.decodeIntWords_encodeInt] using hv

/-- Execute the signed target write and the two caller register updates. -/
theorem targetOffsetEncode_runs {w guess : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (offset qp source heap limit radius : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool) {p : Program}
    (hguess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (hwords : ∀ z∈targetOffsetPacket L F I offset qp source heap limit radius,z<2^w)
    (hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem)
    (hspace : heap+3*F.limbs<2^w) :
    let n := offsetTarget radius offset
    let target := heap+2*F.limbs
    let next := heap+3*F.limbs
    ∃ st c,
      Runs w p ω (targetOffsetEncode guess)
        (startState (targetOffsetPacket L F I offset qp source heap limit radius) mem pos) .normal st c ∧
      (∀ j<24,st.regs j=((targetEpochPacket L F I target qp source next)++[limit]).getD j 0) ∧
      (∀ z<heap,st.mem z=mem z) ∧ ZeroFrom st.mem next ∧
      ScalarAt st.mem target F.fmt.limbBits F.limbs F.fmt.precision (n:ℝ) ∧ c≤100*F.limbs+260 := by
  obtain ⟨st,c,hRun,hRegs,_,hFrame,hZero,hScalar,hCost⟩ :=
    targetOffsetEncode_runs_of_regs F I L offset qp source heap limit radius mem
      (startState (targetOffsetPacket L F I offset qp source heap limit radius) mem pos) ω
      hguess hwords hpre hspace rfl (fun _ _ => rfl)
  exact ⟨st,c,hRun,hRegs,hFrame,hZero,hScalar,hCost⟩

end MinCostFlow.IPM.Machine
