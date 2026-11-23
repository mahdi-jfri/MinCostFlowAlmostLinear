module

public import MinCostFlow.IPM.Machine.TargetSearchLayout
public import MinCostFlow.IPM.Machine.TargetSearchArithmetic
import WordRAM.Tactic

/-!
# Updating the real signed search bracket

The unsigned midpoint and selected endpoint are computed in proper
word range. A target call changes only the search heap and bracket.
An already collapsed bracket makes no target call.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The register state after computing the exact unsigned midpoint. -/
@[expose] def targetSearchMidState (st : State) (lo hi : ℕ) : State :=
  {st with regs:=Function.update st.regs 29 (lo+(hi-lo)/2)}

/-- One active bisection step using the actual result of its midpoint
call. Only the indicated packet and scratch registers can change. -/
theorem targetSearchStep_active {w offsetTest lo hi v cost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st result : State) {body : Stmt} {args : List ℕ}
    (hbody : p.procs[offsetTest]?=some body)
    (hlo : st.regs 26=lo) (hhi : st.regs 27=hi) (hactive : lo<hi)
    (hfit : hi<2^w) (hTwo : 2<2^w) (hv : v<2^w)
    (hargs : evalArgs w (targetSearchMidState st lo hi) (targetSearchArgs 29)=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hb : result.mem (v-1)≤1) :
    let mid := lo+(hi-lo)/2
    let bit := result.mem (v-1)
    ∃ final c,
      Runs w p ω (targetSearchStep offsetTest) st .normal final c ∧
      final.mem=result.mem ∧ final.regs 21=v ∧
      final.regs 26=(if bit=1 then lo else mid+1) ∧
      final.regs 27=(if bit=1 then mid else hi) ∧
      (∀ j,j≠21 → j≠26 → j≠27 → j≠29 → j≠30 → j≠31 → final.regs j=st.regs j) ∧
      c≤cost+60 := by
  dsimp only
  let mid := lo+(hi-lo)/2
  let bit := result.mem (v-1)
  let first := targetSearchMidState st lo hi
  let called : State := ⟨result.mem,Function.update first.regs 30 v,result.pos⟩
  let read : State := {called with regs:=Function.update called.regs 31 bit}
  let alloc : State := {read with regs:=Function.update read.regs 21 v}
  let midpoint := Expr.bin .add (.reg 26) (.bin .div (.bin .sub (.reg 27) (.reg 26)) (.const 2))
  have hmidLt := (targetSearch_midpoint lo hi hactive).2
  have hmid : mid<2^w := hmidLt.trans hfit
  have hsucc : mid+1<2^w := (Nat.succ_le_of_lt hmidLt).trans_lt hfit
  have hloFit : lo<2^w := hactive.trans hfit
  have hdiff : hi-lo<2^w := (Nat.sub_le _ _).trans_lt hfit
  have hHalf : (hi-lo)/2<2^w := (Nat.div_le_self _ _).trans_lt hdiff
  have hOne : 1<2^w := by omega
  have hbit := hb.trans_lt hOne
  have hvSlot : v-1<2^w := (Nat.sub_le _ _).trans_lt hv
  have hEval : midpoint.eval w st=some mid := by
    dsimp only [midpoint]
    eval_expr
  have hSet : Runs w p ω (.assign 29 midpoint) st .normal first 8 :=
    runs_assign_iff.mpr ⟨mid,hEval,rfl,rfl,rfl⟩
  have hCall : Runs w p ω (.call 30 offsetTest (targetSearchArgs 29)) first .normal called (cost+26) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,?_⟩
    · cases result
      rfl
    · change cost+26=25+cost+1
      omega
  have hRead : Runs w p ω (.assign 31 (.load (.bin .sub (.reg 30) (.const 1)))) called .normal read 5 :=
    runs_assign_iff.mpr ⟨bit,by dsimp only [called]; eval_expr,rfl,rfl,rfl⟩
  have hHeap : Runs w p ω (.assign 21 (.reg 30)) read .normal alloc 2 :=
    runs_assign_iff.mpr ⟨v,by simp [read,called,Expr.eval],rfl,rfl,rfl⟩
  have hCond : (Expr.bin .lt (.reg 26) (.reg 27)).eval w st=some 1 :=
    Expr.eval_lt_true (by eval_expr) (by eval_expr) hactive hOne
  have hReadBit : (Expr.reg 31).eval w alloc=some bit := by simp [alloc,read,Expr.eval]
  have hMidReg : alloc.regs 29=mid := by simp [alloc,read,called,first,targetSearchMidState,mid]
  have frame (final : State) (d : ℕ)
      (hchoose : Runs w p ω (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final d) :
      Runs w p ω (targetSearchStep offsetTest) st .normal final (cost+49+d) := by
    have hseq : Runs w p ω
        (.assign 29 midpoint ;;
          .call 30 offsetTest (targetSearchArgs 29) ;;
          .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
          .assign 21 (.reg 30) ;;
          .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        st .normal final (cost+45+d) := runs_seq_iff.mpr (Or.inr ⟨first,8,cost+36+d,hSet,
      runs_seq_iff.mpr (Or.inr ⟨called,cost+26,9+d,hCall,
        runs_seq_iff.mpr (Or.inr ⟨read,5,3+d,hRead,
          runs_seq_iff.mpr (Or.inr ⟨alloc,2,d,hHeap,hchoose,by omega⟩),by omega⟩),by omega⟩),by omega⟩)
    exact runs_cond_iff.mpr ⟨1,cost+45+d,hCond,by simpa [targetSearchStep,midpoint] using hseq,by change cost+49+d=3+(cost+45+d)+1; omega⟩
  by_cases h : bit=1
  · let final : State := {alloc with regs:=Function.update alloc.regs 27 mid}
    have ha : Runs w p ω (.assign 27 (.reg 29)) alloc .normal final 2 :=
      runs_assign_iff.mpr ⟨mid,by simp [Expr.eval,hMidReg],rfl,rfl,rfl⟩
    have hc : Runs w p ω
        (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final 4 :=
      runs_cond_iff.mpr ⟨bit,2,hReadBit,by simpa [h] using ha,rfl⟩
    refine ⟨final,cost+49+4,frame final 4 hc,rfl,by simp [final,alloc],?_,?_,?_,by omega⟩
    · have hb' : result.mem (v-1)=1 := h
      simp [final,alloc,read,called,first,targetSearchMidState,hb',hlo]
    · have hb' : result.mem (v-1)=1 := h
      simp [final,hb',mid]
    · intro j h21 h26 h27 h29 h30 h31
      simp [final,alloc,read,called,first,targetSearchMidState,h21,h27,h29,h30,h31]
  · have hzero : bit=0 := by change bit≤1 at hb; omega
    let final : State := {alloc with regs:=Function.update alloc.regs 26 (mid+1)}
    have ha : Runs w p ω (.assign 26 (.bin .add (.reg 29) (.const 1))) alloc .normal final 4 :=
      runs_assign_iff.mpr ⟨mid+1,by eval_expr,rfl,rfl,rfl⟩
    have hc : Runs w p ω
        (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final 6 :=
      runs_cond_iff.mpr ⟨bit,4,hReadBit,by simpa [hzero] using ha,rfl⟩
    refine ⟨final,cost+49+6,frame final 6 hc,rfl,by simp [final,alloc],?_,?_,?_,by omega⟩
    · have hb' : result.mem (v-1)≠1 := h
      simp [final,hb',mid]
    · have hb' : result.mem (v-1)≠1 := h
      simp [final,alloc,read,called,first,targetSearchMidState,hb',hhi]
    · intro j h21 h26 h27 h29 h30 h31
      simp [final,alloc,read,called,first,targetSearchMidState,h21,h26,h29,h30,h31]

/-- A collapsed bracket performs no test and leaves the state intact. -/
theorem targetSearchStep_inactive {w offsetTest : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (h : st.regs 27≤st.regs 26) (hOne : 1<2^w) :
    Runs w p ω (targetSearchStep offsetTest) st .normal st 6 := by
  have htest : (Expr.bin .lt (.reg 26) (.reg 27)).eval w st=some 0 :=
    Expr.eval_lt_false (by simp [Expr.eval]) (by simp [Expr.eval]) h hOne
  have hregs : Function.update st.regs 26 (st.regs 26)=st.regs := by simp
  have ha : Runs w p ω (.assign 26 (.reg 26)) st .normal st 2 :=
    runs_assign_iff.mpr ⟨st.regs 26,rfl,rfl,by rw [hregs],rfl⟩
  exact runs_cond_iff.mpr ⟨0,2,htest,by simpa [targetSearchStep] using ha,rfl⟩

/-- Shared active step parameterized by call argument expressions. -/
private theorem targetSearchStep_active_of_args {w offsetTest lo hi v cost callCost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st result : State) {body : Stmt} {argsExpr : List Expr} {args : List ℕ}
    (hbody : p.procs[offsetTest]?=some body)
    (hlo : st.regs 26=lo) (hhi : st.regs 27=hi) (hactive : lo<hi)
    (hfit : hi<2^w) (hTwo : 2<2^w) (hv : v<2^w)
    (hargs : evalArgs w (targetSearchMidState st lo hi) argsExpr=some args)
    (hsize : argsSize argsExpr+1≤callCost) (hbound : callCost≤27)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hb : result.mem (v-1)≤1) :
    let mid := lo+(hi-lo)/2
    let bit := result.mem (v-1)
    let step : Stmt :=
      .cond (.bin .lt (.reg 26) (.reg 27))
        (.assign 29 (.bin .add (.reg 26)
          (.bin .div (.bin .sub (.reg 27) (.reg 26)) (.const 2))) ;;
          .call 30 offsetTest argsExpr ;;
          .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
          .assign 21 (.reg 30) ;;
          .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        (.assign 26 (.reg 26))
    ∃ final c,
      Runs w p ω step st .normal final c ∧
      final.mem=result.mem ∧ final.regs 21=v ∧
      final.regs 26=(if bit=1 then lo else mid+1) ∧
      final.regs 27=(if bit=1 then mid else hi) ∧
      (∀ j,j≠21 → j≠26 → j≠27 → j≠29 → j≠30 → j≠31 → final.regs j=st.regs j) ∧
      c≤cost+60 := by
  dsimp only
  let mid := lo+(hi-lo)/2
  let bit := result.mem (v-1)
  let first := targetSearchMidState st lo hi
  let called : State := ⟨result.mem,Function.update first.regs 30 v,result.pos⟩
  let read : State := {called with regs:=Function.update called.regs 31 bit}
  let alloc : State := {read with regs:=Function.update read.regs 21 v}
  let midpoint := Expr.bin .add (.reg 26) (.bin .div (.bin .sub (.reg 27) (.reg 26)) (.const 2))
  have hmidLt := (targetSearch_midpoint lo hi hactive).2
  have hmid : mid<2^w := hmidLt.trans hfit
  have hsucc : mid+1<2^w := (Nat.succ_le_of_lt hmidLt).trans_lt hfit
  have hloFit : lo<2^w := hactive.trans hfit
  have hdiff : hi-lo<2^w := (Nat.sub_le _ _).trans_lt hfit
  have hHalf : (hi-lo)/2<2^w := (Nat.div_le_self _ _).trans_lt hdiff
  have hOne : 1<2^w := by omega
  have hbit := hb.trans_lt hOne
  have hvSlot : v-1<2^w := (Nat.sub_le _ _).trans_lt hv
  have hEval : midpoint.eval w st=some mid := by
    dsimp only [midpoint]
    eval_expr
  have hSet : Runs w p ω (.assign 29 midpoint) st .normal first 8 :=
    runs_assign_iff.mpr ⟨mid,hEval,rfl,rfl,rfl⟩
  have hCall : Runs w p ω (.call 30 offsetTest argsExpr) first .normal called (cost+argsSize argsExpr+1) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,by omega⟩
    cases result
    rfl
  have hRead : Runs w p ω (.assign 31 (.load (.bin .sub (.reg 30) (.const 1)))) called .normal read 5 :=
    runs_assign_iff.mpr ⟨bit,by dsimp only [called]; eval_expr,rfl,rfl,rfl⟩
  have hHeap : Runs w p ω (.assign 21 (.reg 30)) read .normal alloc 2 :=
    runs_assign_iff.mpr ⟨v,by simp [read,called,Expr.eval],rfl,rfl,rfl⟩
  have hCond : (Expr.bin .lt (.reg 26) (.reg 27)).eval w st=some 1 :=
    Expr.eval_lt_true (by eval_expr) (by eval_expr) hactive hOne
  have hReadBit : (Expr.reg 31).eval w alloc=some bit := by simp [alloc,read,Expr.eval]
  have hMidReg : alloc.regs 29=mid := by simp [alloc,read,called,first,targetSearchMidState,mid]
  have frame (final : State) (d : ℕ)
      (hchoose : Runs w p ω (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final d) :
      Runs w p ω (.cond (.bin .lt (.reg 26) (.reg 27))
        (.assign 29 midpoint ;; .call 30 offsetTest argsExpr ;;
          .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
          .assign 21 (.reg 30) ;;
          .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        (.assign 26 (.reg 26))) st .normal final (cost+argsSize argsExpr+24+d) := by
    have hseq : Runs w p ω
        (.assign 29 midpoint ;;
          .call 30 offsetTest argsExpr ;;
          .assign 31 (.load (.bin .sub (.reg 30) (.const 1))) ;;
          .assign 21 (.reg 30) ;;
          .cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        st .normal final (cost+argsSize argsExpr+20+d) := runs_seq_iff.mpr (Or.inr ⟨first,8,cost+argsSize argsExpr+11+d,hSet,
      runs_seq_iff.mpr (Or.inr ⟨called,cost+argsSize argsExpr+1,9+d,hCall,
        runs_seq_iff.mpr (Or.inr ⟨read,5,3+d,hRead,
          runs_seq_iff.mpr (Or.inr ⟨alloc,2,d,hHeap,hchoose,by omega⟩),by omega⟩),by omega⟩),by omega⟩)
    exact runs_cond_iff.mpr ⟨1,cost+argsSize argsExpr+20+d,hCond,hseq,
      by change cost+argsSize argsExpr+24+d=3+(cost+argsSize argsExpr+20+d)+1; omega⟩
  by_cases h : bit=1
  · let final : State := {alloc with regs:=Function.update alloc.regs 27 mid}
    have ha : Runs w p ω (.assign 27 (.reg 29)) alloc .normal final 2 :=
      runs_assign_iff.mpr ⟨mid,by simp [Expr.eval,hMidReg],rfl,rfl,rfl⟩
    have hc : Runs w p ω
        (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final 4 :=
      runs_cond_iff.mpr ⟨bit,2,hReadBit,by simpa [h] using ha,rfl⟩
    refine ⟨final,cost+argsSize argsExpr+24+4,frame final 4 hc,rfl,by simp [final,alloc],?_,?_,?_,by omega⟩
    · have hb' : result.mem (v-1)=1 := h
      simp [final,alloc,read,called,first,targetSearchMidState,hb',hlo]
    · have hb' : result.mem (v-1)=1 := h
      simp [final,hb',mid]
    · intro j h21 h26 h27 h29 h30 h31
      simp [final,alloc,read,called,first,targetSearchMidState,h21,h27,h29,h30,h31]
  · have hzero : bit=0 := by change bit≤1 at hb; omega
    let final : State := {alloc with regs:=Function.update alloc.regs 26 (mid+1)}
    have ha : Runs w p ω (.assign 26 (.bin .add (.reg 29) (.const 1))) alloc .normal final 4 :=
      runs_assign_iff.mpr ⟨mid+1,by eval_expr,rfl,rfl,rfl⟩
    have hc : Runs w p ω
        (.cond (.reg 31) (.assign 27 (.reg 29)) (.assign 26 (.bin .add (.reg 29) (.const 1))))
        alloc .normal final 6 :=
      runs_cond_iff.mpr ⟨bit,4,hReadBit,by simpa [hzero] using ha,rfl⟩
    refine ⟨final,cost+argsSize argsExpr+24+6,frame final 6 hc,rfl,by simp [final,alloc],?_,?_,?_,by omega⟩
    · have hb' : result.mem (v-1)≠1 := h
      simp [final,hb',mid]
    · have hb' : result.mem (v-1)≠1 := h
      simp [final,alloc,read,called,first,targetSearchMidState,hb',hhi]
    · intro j h21 h26 h27 h29 h30 h31
      simp [final,alloc,read,called,first,targetSearchMidState,h21,h26,h29,h30,h31]

/-- `V`-passing variant of `targetSearchStep_active`. -/
theorem targetSearchStepWithV_active {w offsetTest lo hi v cost : ℕ} {p : Program} {ω : ℕ → Bool}
    (st result : State) {body : Stmt} {args : List ℕ}
    (hbody : p.procs[offsetTest]?=some body)
    (hlo : st.regs 26=lo) (hhi : st.regs 27=hi) (hactive : lo<hi)
    (hfit : hi<2^w) (hTwo : 2<2^w) (hv : v<2^w)
    (hargs : evalArgs w (targetSearchMidState st lo hi) (targetSearchArgsWithV 29)=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hb : result.mem (v-1)≤1) :
    let mid := lo+(hi-lo)/2
    let bit := result.mem (v-1)
    ∃ final c,
      Runs w p ω (targetSearchStepWithV offsetTest) st .normal final c ∧
      final.mem=result.mem ∧ final.regs 21=v ∧
      final.regs 26=(if bit=1 then lo else mid+1) ∧
      final.regs 27=(if bit=1 then mid else hi) ∧
      (∀ j,j≠21 → j≠26 → j≠27 → j≠29 → j≠30 → j≠31 → final.regs j=st.regs j) ∧
      c≤cost+60 := by
  have hSize : argsSize (targetSearchArgsWithV 29)+1≤27 := by decide
  exact targetSearchStep_active_of_args st result hbody hlo hhi hactive hfit hTwo hv hargs hSize (le_refl 27) hrun hb

/-- `V`-passing variant of `targetSearchStep_inactive`. -/
theorem targetSearchStepWithV_inactive {w offsetTest : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (h : st.regs 27≤st.regs 26) (hOne : 1<2^w) :
    Runs w p ω (targetSearchStepWithV offsetTest) st .normal st 6 := by
  have htest : (Expr.bin .lt (.reg 26) (.reg 27)).eval w st=some 0 :=
    Expr.eval_lt_false (by simp [Expr.eval]) (by simp [Expr.eval]) h hOne
  have hregs : Function.update st.regs 26 (st.regs 26)=st.regs := by simp
  have ha : Runs w p ω (.assign 26 (.reg 26)) st .normal st 2 :=
    runs_assign_iff.mpr ⟨st.regs 26,rfl,rfl,by rw [hregs],rfl⟩
  exact runs_cond_iff.mpr ⟨0,2,htest,by simpa [targetSearchStepWithV] using ha,rfl⟩

end MinCostFlow.IPM.Machine
