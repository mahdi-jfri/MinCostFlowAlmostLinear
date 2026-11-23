module

public import MinCostFlow.IPM.Machine.TargetEpochReturn
import WordRAM.Tactic

/-!
# The actual residual call at the start of a target stage

The caller keeps the old flow and target pointers. Register 30
receives the guarded residual result. Register 23 always points
just after the residual workspace, on both the terminal and the
continuing path.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Execute the machine's first call and exact address arithmetic.
The callee's postcondition retains the actual old and new views. -/
theorem targetEpochSetup_runs {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (target quarter source heap : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hwords : ∀ z∈targetEpochPacket L F I target quarter source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hspace : epochResidualEnd I.m F.limbs heap<2^w) :
    let initial := startState (targetEpochPacket L F I target quarter source heap) mem pos
    ∃ v final cost,
      Runs w p ω (targetEpochSetup base) initial .normal final cost ∧
      (epochBaseContract w F.fmt.limbBits).post
        [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter] mem v final.mem ∧
      final.regs 30=v ∧ final.regs 23=epochResidualEnd I.m F.limbs heap ∧
      (∀ j<23,final.regs j=initial.regs j) ∧
      cost≤epochBaseCost I.m F.limbs+30 := by
  dsimp only
  let args := [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter]
  let initial := startState (targetEpochPacket L F I target quarter source heap) mem pos
  have hArg : ∀ z∈args,z<2^w := by
    intro z hz
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hwords _ (by simp [targetEpochPacket])
  obtain ⟨body,hbody,o,st,c,hRun,hOut,hCost⟩ := hbase args mem pos ω hArg hpre
  let after : State := ⟨st.mem,Function.update initial.regs 30 o.value,st.pos⟩
  let final : State := {after with regs := Function.update after.regs 23 (epochResidualEnd I.m F.limbs heap)}
  have hCall : Runs w p ω (.call 30 base [.reg 1,.reg 20,.reg 0,.reg 6,.reg 15,.reg 21,.reg 7,.reg 8,.reg 9])
      initial .normal after (c+10) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,o,st,c,rfl,hbody,hRun,rfl,?_,by change c+10=9+c+1; omega⟩
    cases st
    rfl
  have hSmall : 8*I.m+4<2^w := (Nat.le_mul_of_pos_right (n:=8*I.m+4) hL).trans_lt
    ((Nat.le_add_left _ _).trans_lt hspace)
  have hm : 8*I.m<2^w := by omega
  have h4 : 4<2^w := by omega
  have hmL : (8*I.m+4)*F.limbs<2^w := (Nat.le_add_left _ _).trans_lt hspace
  have hEval : (Expr.bin .add (.reg 21)
    (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 4)) (.reg 15))).eval w after=
      some (epochResidualEnd I.m F.limbs heap) := by
    dsimp only [after,initial,epochResidualEnd]
    unfold targetEpochPacket
    eval_expr
  have hSet : Runs w p ω (.assign 23 (.bin .add (.reg 21)
    (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 4)) (.reg 15)))) after .normal final 10 := by
    exact runs_assign_iff.mpr ⟨_,hEval,rfl,rfl,rfl⟩
  have hc : c≤epochBaseCost I.m F.limbs := hCost
  refine ⟨o.value,final,c+21,runs_seq_iff.mpr (Or.inr ⟨after,_,_,hCall,hSet,by omega⟩),
    hOut,by simp [final,after],by simp [final],?_,by omega⟩
  intro j hj
  simp only [final,after,Function.update_of_ne (by omega : j≠23),Function.update_of_ne (by omega : j≠30)]
  rfl

/-- Save `V` from `.reg 23` into `.reg 29` and execute the machine setup call and
exact address arithmetic, keeping the total cost within `epochBaseCost I.m F.limbs + 30`. -/
theorem targetEpochSetupWithV_runs {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (target quarter source heap V : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hwords : ∀ z∈targetEpochPacket L F I target quarter source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hspace : epochResidualEnd I.m F.limbs heap<2^w) :
    let initial := startState (targetEpochPacketWithV L F I target quarter source heap V) mem pos
    ∃ v final cost,
      Runs w p ω (targetEpochSetupWithV base) initial .normal final cost ∧
      (epochBaseContract w F.fmt.limbBits).post
        [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter] mem v final.mem ∧
      final.regs 30=v ∧ final.regs 23=epochResidualEnd I.m F.limbs heap ∧ final.regs 29=V ∧
      (∀ j<23,final.regs j=initial.regs j) ∧
      cost≤epochBaseCost I.m F.limbs+30 := by
  dsimp only
  let args := [L.cost,source,I.m,target,F.limbs,heap,L.slackMin,L.slackMax,quarter]
  let initial := startState (targetEpochPacketWithV L F I target quarter source heap V) mem pos
  have hArg : ∀ z∈args,z<2^w := by
    intro z hz
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hwords _ (by simp [targetEpochPacket])
  obtain ⟨body,hbody,o,st,c,hRun,hOut,hCost⟩ := hbase args mem pos ω hArg hpre
  have h23 : initial.regs 23=V := rfl
  let saved : State := {initial with regs:=Function.update initial.regs 29 V}
  let after : State := ⟨st.mem,Function.update saved.regs 30 o.value,st.pos⟩
  let final : State := {after with regs := Function.update after.regs 23 (epochResidualEnd I.m F.limbs heap)}
  have hSave : Runs w p ω (.assign 29 (.reg 23)) initial .normal saved 2 :=
    runs_assign_iff.mpr ⟨V,by simp [Expr.eval,h23],rfl,rfl,rfl⟩
  have hRegsSaved (j : ℕ) (hj : j<23) : saved.regs j=
      (targetEpochPacket L F I target quarter source heap).getD j 0 := by
    simp only [saved,Function.update_of_ne (by omega : j≠29)]
    exact List.getD_append _ _ _ _ hj
  have hEvalArgs : evalArgs w saved [.reg 1,.reg 20,.reg 0,.reg 6,.reg 15,.reg 21,.reg 7,.reg 8,.reg 9] =
      some args := by
    simp only [args,evalArgs,Expr.eval,hRegsSaved 1 (by decide),hRegsSaved 20 (by decide),
      hRegsSaved 0 (by decide),hRegsSaved 6 (by decide),hRegsSaved 15 (by decide),
      hRegsSaved 21 (by decide),hRegsSaved 7 (by decide),hRegsSaved 8 (by decide),hRegsSaved 9 (by decide)]
    rfl
  have hCall : Runs w p ω (.call 30 base [.reg 1,.reg 20,.reg 0,.reg 6,.reg 15,.reg 21,.reg 7,.reg 8,.reg 9])
      saved .normal after (c+10) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,o,st,c,hEvalArgs,hbody,hRun,rfl,?_,by change c+10=9+c+1; omega⟩
    cases st
    rfl
  have hSmall : 8*I.m+4<2^w := (Nat.le_mul_of_pos_right (n:=8*I.m+4) hL).trans_lt
    ((Nat.le_add_left _ _).trans_lt hspace)
  have hm : 8*I.m<2^w := by omega
  have h4 : 4<2^w := by omega
  have hmL : (8*I.m+4)*F.limbs<2^w := (Nat.le_add_left _ _).trans_lt hspace
  have hEval : (Expr.bin .add (.reg 21)
    (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 4)) (.reg 15))).eval w after=
      some (epochResidualEnd I.m F.limbs heap) := by
    have ha0 : after.regs 0=I.m := hRegsSaved 0 (by decide)
    have ha15 : after.regs 15=F.limbs := hRegsSaved 15 (by decide)
    have ha21 : after.regs 21=heap := hRegsSaved 21 (by decide)
    dsimp only [epochResidualEnd]
    eval_expr
  have hSet : Runs w p ω (.assign 23 (.bin .add (.reg 21)
    (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 4)) (.reg 15)))) after .normal final 10 :=
    runs_assign_iff.mpr ⟨_,hEval,rfl,rfl,rfl⟩
  have hSetup : Runs w p ω (targetEpochSetup base) saved .normal final (c+21) :=
    runs_seq_iff.mpr (Or.inr ⟨after,_,_,hCall,hSet,by omega⟩)
  have hc : c≤epochBaseCost I.m F.limbs := hCost
  refine ⟨o.value,final,c+24,runs_seq_iff.mpr (Or.inr ⟨saved,2,c+21,hSave,hSetup,by omega⟩),
    hOut,by simp [final,after],by simp [final],by simp [final,after,saved],?_,by omega⟩
  intro j hj
  simp only [final,after,saved,Function.update_of_ne (by omega : j≠23),
    Function.update_of_ne (by omega : j≠30),Function.update_of_ne (by omega : j≠29)]
  rfl

end MinCostFlow.IPM.Machine
