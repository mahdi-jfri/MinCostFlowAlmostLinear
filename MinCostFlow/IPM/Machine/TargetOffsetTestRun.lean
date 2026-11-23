module

public import MinCostFlow.IPM.Machine.TargetOffsetEncodeRun
public import MinCostFlow.IPM.Machine.TargetTestDecision
public import MinCostFlow.IPM.Machine.TargetEpochStatic
import Mathlib.Tactic.Linarith
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Testing one unsigned search offset

The wrapper installs an exact signed target and calls the bounded
test on the unchanged half-slack starting flow. The bit compares
the guessed target with the integer optimum.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Outcome of one target comparison during bisection. -/
def TargetOffsetResult {w : ℕ} (F : MinRatioFormat w) (I : Instance) (E heap out : ℕ)
    (guess optimum : ℤ) (mem final : ℕ → ℕ) : Prop :=
  heap+2≤out ∧ out<2^w ∧ ZeroFrom final out ∧ (∀ z<heap,final z=mem z) ∧
  final (out-1)≤1 ∧ (final (out-1)=1 ↔ optimum≤guess) ∧
  (final (out-1)=1 → TargetStageFlow F I E (final (out-2)) out final ∧
    I.cost (epochVector F I final (final (out-2)))≤(guess:ℝ)+1/4)

/-- Link the encoded target to the actual numerical test and return
its record. The target runner is the verified test at its new heap. -/
theorem targetOffsetTest_runs_of_test {w guess test epoch record : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (L : EpochLayout) (offset qp source heap limit radius space price : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program}
    (hguess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (htest : p.procs[test]?=some (targetTestBody epoch record))
    (hwords : ∀ z∈targetOffsetPacket L F I offset qp source heap limit radius,z<2^w)
    (hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem)
    (hspace : heap+3*F.limbs<2^w)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hF : -(I.m*(U:ℝ)^2)≤(offsetTarget radius offset:ℝ))
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hz : I.cost fstar=(z:ℝ))
    (hRunner : ∀ (st : State) target next,
      target=heap+2*F.limbs → next=heap+3*F.limbs →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem next →
      ScalarAt st.mem target F.fmt.limbBits F.limbs F.fmt.precision (offsetTarget radius offset:ℝ) →
      ∃ v final cost,
        Runs w p ω (targetTestBody epoch record)
          (startState (targetEpochPacket L F I target qp source next++[limit]) st.mem st.pos) (.returned v) final cost ∧
        TargetTestResult F I U L.exponent source next v (offsetTarget radius offset:ℝ) st.mem final.mem ∧
        v≤next+space ∧ cost≤price) :
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBody guess test)
        (startState (targetOffsetPacket L F I offset qp source heap limit radius) mem pos) (.returned v) final cost ∧
      TargetOffsetResult F I L.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+3*F.limbs+space ∧ cost≤price+100*F.limbs+300 := by
  let tp := heap+2*F.limbs
  let next := heap+3*F.limbs
  let initial := startState (targetOffsetPacket L F I offset qp source heap limit radius) mem pos
  let value := offsetTarget radius offset
  obtain ⟨st,c,hEnc,hRegs,hFrame,hZero,hTarget,hCost⟩ :=
    targetOffsetEncode_runs F I L offset qp source heap limit radius mem pos ω hguess hwords hpre hspace
  obtain ⟨v,res,d,hRun,hRes,hEnd,hCost'⟩ := hRunner st tp next rfl rfl hFrame hZero hTarget
  have hargs : evalArgs w st ((List.range 24).map Expr.reg)=
      some (targetEpochPacket L F I tp qp source next++[limit]) := by
    have h := evalArgs_range_regs (w:=w) st (targetEpochPacket L F I tp qp source next++[limit]) 0
      (fun j hj => by simpa only [Nat.zero_add] using hRegs j hj)
    exact h
  let final : State := ⟨res.mem,Function.update st.regs 26 v,res.pos⟩
  have hCall : Runs w p ω (.call 26 test ((List.range 24).map Expr.reg)) st .normal final (d+25) := by
    apply runs_call_iff.mpr
    refine ⟨_,_,.returned v,res,d,hargs,htest,hRun,rfl,?_,by change d+25=24+d+1; omega⟩
    cases res
    rfl
  have hRet : Runs w p ω (.ret (.reg 26)) final (.returned v) final 2 :=
    runs_ret_iff.mpr ⟨v,by simp [Expr.eval,final],rfl,rfl,rfl⟩
  have hTail := runs_seq_iff.mpr (Or.inr ⟨final,d+25,2,hCall,hRet,rfl⟩)
  have hf := hflow.frozen hFrame (show heap≤next from Nat.le_add_right _ _)
  have hsame : epochVector F I st.mem source=epochVector F I mem source := by
    funext e
    exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
  have hbit := targetTest_integer_decision F I U L.exponent source next v value z st.mem res.mem hRes
    hm hU hsize hnums hF hf.2.1 (hsame.symm ▸ hhalf) fstar hstar hz
  obtain ⟨hLo,hV,hZ,hMem,hBool,_,hYes⟩ := hRes
  have hLo' : next+2≤v := hLo
  have hEnd' : v≤next+space := hEnd
  have hBack : ∀ b<heap,res.mem b=mem b :=
    fun b hb => (hMem b (hb.trans_le (Nat.le_add_right _ _))).trans (hFrame b hb)
  have hresult : TargetOffsetResult F I L.exponent heap v value z mem res.mem :=
    ⟨by dsimp only [next] at hLo'; omega,hV,hZ,hBack,hBool,hbit,fun hb => by
      obtain ⟨hv,hres⟩ := hYes hb
      exact ⟨hv,by unfold residual at hres; linarith only [hres]⟩⟩
  exact ⟨v,final,c+(d+28)+1,runs_seq_iff.mpr (Or.inr ⟨st,c,d+28,hEnc,hTail,rfl⟩),
    hresult,hEnd',by omega⟩

/-- `V`-passing variant of `targetOffsetTest_runs_of_test`. -/
theorem targetOffsetTestWithV_runs_of_test {w guess test epoch record : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U V : ℕ) (L : EpochLayout) (offset qp source heap limit radius space price : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program}
    (hguess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (htest : p.procs[test]?=some (targetTestBodyWithV epoch record))
    (hwords : ∀ z∈targetOffsetPacket L F I offset qp source heap limit radius,z<2^w)
    (hV : V<2^w)
    (hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem)
    (hspace : heap+3*F.limbs<2^w)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hF : -(I.m*(U:ℝ)^2)≤(offsetTarget radius offset:ℝ))
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hz : I.cost fstar=(z:ℝ))
    (hRunner : ∀ (st : State) target next,
      target=heap+2*F.limbs → next=heap+3*F.limbs →
      (∀ b<heap,st.mem b=mem b) → ZeroFrom st.mem next →
      ScalarAt st.mem target F.fmt.limbBits F.limbs F.fmt.precision (offsetTarget radius offset:ℝ) →
      ∃ v final cost,
        Runs w p ω (targetTestBodyWithV epoch record)
          (startState (targetEpochPacket L F I target qp source next++[limit,V]) st.mem st.pos) (.returned v) final cost ∧
        TargetTestResult F I U L.exponent source next v (offsetTarget radius offset:ℝ) st.mem final.mem ∧
        v≤next+space ∧ cost≤price) :
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBodyWithV guess test)
        (startState (targetOffsetPacketWithV L F I offset qp source heap limit radius V) mem pos) (.returned v) final cost ∧
      TargetOffsetResult F I L.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+3*F.limbs+space ∧ cost≤price+100*F.limbs+300 := by
  let tp := heap+2*F.limbs
  let next := heap+3*F.limbs
  let initial := startState (targetOffsetPacketWithV L F I offset qp source heap limit radius V) mem pos
  let saved : State := {initial with regs := Function.update initial.regs 27 V}
  let value := offsetTarget radius offset
  have hlen : (targetOffsetPacket L F I offset qp source heap limit radius).length=25 := by
    simp [targetOffsetPacket,targetEpochPacket]
  have hsaveReg : initial.regs 25=V := by
    simp [initial,startState,targetOffsetPacketWithV,targetOffsetPacket,targetEpochPacket]
  have hsave : Runs w p ω (.assign 27 (.reg 25)) initial .normal saved 2 :=
    runs_assign_iff.mpr ⟨V,by simp [Expr.eval,hsaveReg],rfl,rfl,rfl⟩
  have hsavedRegs : ∀ j<25,saved.regs j=(targetOffsetPacket L F I offset qp source heap limit radius).getD j 0 := by
    intro j hj
    rw [show saved.regs j=initial.regs j by simp [saved,Function.update_of_ne (by omega : j≠27)]]
    change (targetOffsetPacket L F I offset qp source heap limit radius++[V]).getD j 0=_
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (hlen ▸ hj)]
  obtain ⟨st,c,hEnc,hRegs,hRegFrame,hFrame,hZero,hTarget,hCost⟩ :=
    targetOffsetEncode_runs_of_regs F I L offset qp source heap limit radius mem saved ω
      hguess hwords hpre hspace rfl hsavedRegs
  obtain ⟨v,res,d,hRun,hRes,hEnd,hCost'⟩ := hRunner st tp next rfl rfl hFrame hZero hTarget
  have hst27 : st.regs 27=V := (hRegFrame 27 (by decide) (by decide) (by decide)).trans (by simp [saved])
  have hargs : evalArgs w st ((List.range 24).map Expr.reg ++ [.reg 27])=
      some (targetEpochPacket L F I tp qp source next++[limit,V]) := by
    have h := evalArgs_range_regs (w:=w) st (targetEpochPacket L F I tp qp source next++[limit]) 0
      (fun j hj => by simpa only [Nat.zero_add] using hRegs j hj)
    have hlen24 : (targetEpochPacket L F I tp qp source next++[limit]).length=24 := by
      simp [targetEpochPacket]
    rw [hlen24,← List.range_eq_range'] at h
    rw [show targetEpochPacket L F I tp qp source next++[limit,V]=
      (targetEpochPacket L F I tp qp source next++[limit])++[V] by simp]
    exact evalArgs_append h (by simp [evalArgs,Expr.eval,hst27])
  let final : State := ⟨res.mem,Function.update st.regs 26 v,res.pos⟩
  have hCall : Runs w p ω (.call 26 test ((List.range 24).map Expr.reg ++ [.reg 27])) st .normal final (d+26) := by
    apply runs_call_iff.mpr
    refine ⟨_,_,.returned v,res,d,hargs,htest,hRun,rfl,?_,by
      change d+26=argsSize ((List.range 24).map Expr.reg ++ [.reg 27])+d+1
      have : argsSize ((List.range 24).map Expr.reg ++ [.reg 27])=25 := by decide
      omega⟩
    cases res
    rfl
  have hRet : Runs w p ω (.ret (.reg 26)) final (.returned v) final 2 :=
    runs_ret_iff.mpr ⟨v,by simp [Expr.eval,final],rfl,rfl,rfl⟩
  have hTail := runs_seq_iff.mpr (Or.inr ⟨final,d+26,2,hCall,hRet,rfl⟩)
  have hf := hflow.frozen hFrame (show heap≤next from Nat.le_add_right _ _)
  have hsame : epochVector F I st.mem source=epochVector F I mem source := by
    funext e
    exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
  have hbit := targetTest_integer_decision F I U L.exponent source next v value z st.mem res.mem hRes
    hm hU hsize hnums hF hf.2.1 (hsame.symm ▸ hhalf) fstar hstar hz
  obtain ⟨hLo,hVout,hZ,hMem,hBool,_,hYes⟩ := hRes
  have hLo' : next+2≤v := hLo
  have hEnd' : v≤next+space := hEnd
  have hBack : ∀ b<heap,res.mem b=mem b :=
    fun b hb => (hMem b (hb.trans_le (Nat.le_add_right _ _))).trans (hFrame b hb)
  have hresult : TargetOffsetResult F I L.exponent heap v value z mem res.mem :=
    ⟨by dsimp only [next] at hLo'; omega,hVout,hZ,hBack,hBool,hbit,fun hb => by
      obtain ⟨hv,hres⟩ := hYes hb
      exact ⟨hv,by unfold residual at hres; linarith only [hres]⟩⟩
  have hEncTail := runs_seq_iff.mpr (Or.inr ⟨st,c,d+29,hEnc,hTail,rfl⟩)
  exact ⟨v,final,2+(c+(d+29)+1)+1,runs_seq_iff.mpr (Or.inr ⟨saved,2,c+(d+29)+1,hsave,hEncTail,rfl⟩),
    hresult,hEnd',by omega⟩

end MinCostFlow.IPM.Machine
