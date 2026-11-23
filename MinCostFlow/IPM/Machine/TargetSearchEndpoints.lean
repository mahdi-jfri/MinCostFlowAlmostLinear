module

public import MinCostFlow.IPM.Machine.TargetSearchInvariant
import WordRAM.Tactic

/-!
# Entering and returning from the binary search

Initialize the counted loop with the full offset interval. After the
bracket has collapsed, the caller returns the exact record of the
final successful test.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Initialize the full interval and its reserved heap invariant. -/
theorem targetSearch_init_runs {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius tick space : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program}
    (hRadius : 2*radius<2^w) (hTwo : 2<2^w) (htick : tick≤2*radius)
    (hzero : ZeroFrom mem heap) :
    let rounds := targetSearchRounds radius
    let start := startState (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds]) mem pos
    ∃ st,
      Runs w p ω targetSearchInit start .normal st 10 ∧
      TargetSearchInvariant F I L qp source heap limit radius tick space mem 0 st := by
  dsimp only
  let rounds := targetSearchRounds radius
  let start := startState (targetOffsetPacket L F I 0 qp source heap limit radius++[rounds]) mem pos
  let lo : State := {start with regs:=Function.update start.regs 26 0}
  let hi : State := {lo with regs:=Function.update lo.regs 27 (2*radius)}
  let st : State := {hi with regs:=Function.update hi.regs 28 0}
  have h0 : 0<2^w := by omega
  have hlo : Runs w p ω (.assign 26 (.const 0)) start .normal lo 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const h0,rfl,rfl,rfl⟩
  have hhi : Runs w p ω (.assign 27 (.bin .mul (.const 2) (.reg 24))) lo .normal hi 4 := by
    have hr : lo.regs 24=radius := rfl
    exact runs_assign_iff.mpr ⟨2*radius,by eval_expr,rfl,rfl,rfl⟩
  have hcounter : Runs w p ω (.assign 28 (.const 0)) hi .normal st 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const h0,rfl,rfl,rfl⟩
  have hStart : Runs w p ω targetSearchInit start .normal st 10 :=
    runs_seq_iff.mpr (Or.inr ⟨lo,2,7,hlo,runs_seq_iff.mpr (Or.inr ⟨hi,4,2,hhi,hcounter,rfl⟩),rfl⟩)
  have hHeap : st.regs 21=heap := rfl
  have hLo : st.regs 26=0 := by simp [st,hi,lo]
  have hHi : st.regs 27=2*radius := by simp [st,hi]
  refine ⟨st,hStart,?_⟩
  unfold TargetSearchInvariant
  dsimp only
  rw [hHeap,hLo,hHi]
  refine ⟨by simp [st],rfl,?_,Nat.zero_le _,htick,le_rfl,?_,le_rfl,by simp,fun _ _ => rfl,hzero⟩
  · intro j hj _
    simp only [st,hi,lo,Function.update_of_ne (by omega : j≠28),Function.update_of_ne (by omega : j≠27),
      Function.update_of_ne (by omega : j≠26)]
    exact List.getD_append _ _ _ _ hj
  · simpa only [Nat.sub_zero] using targetSearch_rounds_fit_span radius

/-- Return the actual record at the final target without modifying
its flow, flag or memory. -/
theorem targetSearch_finish_runs {w offsetTest v cost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st result : State) {body : Stmt} {args : List ℕ}
    (hbody : p.procs[offsetTest]?=some body)
    (hargs : evalArgs w st (targetSearchArgs 26)=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost) :
    ∃ final,Runs w p ω (targetSearchFinish offsetTest) st (.returned v) final (cost+29) ∧ final.mem=result.mem := by
  let final : State := ⟨result.mem,Function.update st.regs 30 v,result.pos⟩
  have hcall : Runs w p ω (.call 30 offsetTest (targetSearchArgs 26)) st .normal final (cost+26) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,by change cost+26=25+cost+1; omega⟩
    cases result
    rfl
  have hret : Runs w p ω (.ret (.reg 30)) final (.returned v) final 2 :=
    runs_ret_iff.mpr ⟨v,by simp [Expr.eval,final],rfl,rfl,rfl⟩
  exact ⟨final,runs_seq_iff.mpr (Or.inr ⟨final,cost+26,2,hcall,hret,by omega⟩),rfl⟩

/-- `V`-passing variant of `targetSearch_init_runs`: preserves `V` in `.reg 32`. -/
theorem targetSearchWithV_init_runs {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (qp source heap limit radius tick space V : ℕ)
    (mem : ℕ → ℕ) (st0 : State) (ω : ℕ → Bool) {p : Program}
    (hRadius : 2*radius<2^w) (hTwo : 2<2^w) (htick : tick≤2*radius)
    (hzero : ZeroFrom mem heap)
    (hmem : st0.mem=mem)
    (hregs : ∀ j<26,st0.regs j=(targetOffsetPacket L F I 0 qp source heap limit radius++[targetSearchRounds radius]).getD j 0)
    (h32 : st0.regs 32=V) :
    let rounds := targetSearchRounds radius
    ∃ st,
      Runs w p ω targetSearchInit st0 .normal st 10 ∧
      TargetSearchInvariant F I L qp source heap limit radius tick space mem 0 st ∧
      st.regs 32=V := by
  dsimp only
  subst mem
  let rounds := targetSearchRounds radius
  let lo : State := {st0 with regs:=Function.update st0.regs 26 0}
  let hi : State := {lo with regs:=Function.update lo.regs 27 (2*radius)}
  let st : State := {hi with regs:=Function.update hi.regs 28 0}
  have h0 : 0<2^w := by omega
  have hr24 : lo.regs 24=radius := by
    have h0' := hregs 24 (by decide)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [targetOffsetPacket_length]; decide),
      ← List.getD_eq_getElem?_getD] at h0'
    simpa [lo,targetOffsetPacket,targetEpochPacket,targetEpochPacket_length] using h0'
  have hlo : Runs w p ω (.assign 26 (.const 0)) st0 .normal lo 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const h0,rfl,rfl,rfl⟩
  have hhi : Runs w p ω (.assign 27 (.bin .mul (.const 2) (.reg 24))) lo .normal hi 4 :=
    runs_assign_iff.mpr ⟨2*radius,by eval_expr,rfl,rfl,rfl⟩
  have hcounter : Runs w p ω (.assign 28 (.const 0)) hi .normal st 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const h0,rfl,rfl,rfl⟩
  have hStart : Runs w p ω targetSearchInit st0 .normal st 10 :=
    runs_seq_iff.mpr (Or.inr ⟨lo,2,7,hlo,runs_seq_iff.mpr (Or.inr ⟨hi,4,2,hhi,hcounter,rfl⟩),rfl⟩)
  have hHeap : st.regs 21=heap := by
    have h0' := hregs 21 (by decide)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [targetOffsetPacket_length]; decide),
      ← List.getD_eq_getElem?_getD] at h0'
    simpa [st,hi,lo,targetOffsetPacket,targetEpochPacket] using h0'
  have hLo : st.regs 26=0 := by simp [st,hi,lo]
  have hHi : st.regs 27=2*radius := by simp [st,hi]
  have hLimit : st.regs 25=rounds := by
    have h0' := hregs 25 (by decide)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [targetOffsetPacket_length]),
      targetOffsetPacket_length] at h0'
    simpa [st,hi,lo] using h0'
  refine ⟨st,hStart,⟨?_,by simp [st,hi,lo,h32]⟩⟩
  unfold TargetSearchInvariant
  dsimp only
  rw [hHeap,hLo,hHi]
  refine ⟨by simp [st],hLimit,?_,Nat.zero_le _,htick,le_rfl,?_,le_rfl,by simp,fun _ _ => rfl,hzero⟩
  · intro j hj _
    have h0' := hregs j (by omega)
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [targetOffsetPacket_length]; exact hj),
      ← List.getD_eq_getElem?_getD] at h0'
    simpa only [st,hi,lo,Function.update_of_ne (by omega : j≠28),Function.update_of_ne (by omega : j≠27),
      Function.update_of_ne (by omega : j≠26)] using h0'
  · simpa only [Nat.sub_zero] using targetSearch_rounds_fit_span radius

/-- `V`-passing variant of `targetSearch_finish_runs`. -/
theorem targetSearchWithV_finish_runs {w offsetTest v cost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st result : State) {body : Stmt} {args : List ℕ}
    (hbody : p.procs[offsetTest]?=some body)
    (hargs : evalArgs w st (targetSearchArgsWithV 26)=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost) :
    ∃ final,Runs w p ω (targetSearchFinishWithV offsetTest) st (.returned v) final (cost+30) ∧ final.mem=result.mem := by
  let final : State := ⟨result.mem,Function.update st.regs 30 v,result.pos⟩
  have hSize : argsSize (targetSearchArgsWithV 26)=26 := by decide
  have hcall : Runs w p ω (.call 30 offsetTest (targetSearchArgsWithV 26)) st .normal final (cost+27) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,by rw [hSize]; omega⟩
    cases result
    rfl
  have hret : Runs w p ω (.ret (.reg 30)) final (.returned v) final 2 :=
    runs_ret_iff.mpr ⟨v,by simp [Expr.eval,final],rfl,rfl,rfl⟩
  exact ⟨final,runs_seq_iff.mpr (Or.inr ⟨final,cost+27,2,hcall,hret,by omega⟩),rfl⟩

end MinCostFlow.IPM.Machine
