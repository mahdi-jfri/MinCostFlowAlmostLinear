module

public import MinCostFlow.IPM.Machine.TargetTestAdvance
public import MinCostFlow.IPM.Machine.TargetEpochReturn
import WordRAM.Tactic

/-!
# Running the full bounded target test

The guard stops at the first terminal stage. If all stages continue,
the final return writes failure and the invariant excludes the
original upper-target promise. The counted loop uses its exact stage
budget and retains the old input prefix.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 450000 in
/-- Compose the actual bounded loop from its verified stage entry.
The result concerns the original target and initial flow. -/
theorem targetTest_runs_of_stage {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U k : ℕ) (L : EpochLayout) (tp qp src heap space price : ℕ) (target : ℝ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {epoch record : ℕ} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hTwo : 2<2^w) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (hWords : ∀ z∈targetEpochPacket L F I tp qp src heap,z<2^w)
    (hlimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*space+2<2^w)
    (hflow : TargetStageFlow F I L.exponent src heap mem) (hzero : ZeroFrom mem heap)
    (hstage : ∀ st i (stream : ℕ → Bool),
      TargetTestInvariant F I U k L tp qp src heap space target mem i st →
      st.regs 21+space<2^w →
      ∃ out final cost,
        Runs w p stream body (startState (targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21)) st.mem st.pos)
          (.returned out) final cost ∧
        TargetStageResult F I U L.exponent (1/(2:ℝ)^k) target (st.regs 20) (st.regs 21) out st.mem final.mem ∧
        out≤st.regs 21+space ∧ cost≤price) :
    let limit := targetTestLimit I.m U k
    ∃ v final cost,
      Runs w p ω (targetTestBody epoch record)
        (startState (targetEpochPacket L F I tp qp src heap++[limit]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U L.exponent src heap v target mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  dsimp only
  let limit := targetTestLimit I.m U k
  change heap+limit*space+2<2^w at hspace
  let Inv := TargetTestInvariant F I U k L tp qp src heap space target mem
  let Q := fun v (st : State) => TargetTestResult F I U L.exponent src heap v target mem st.mem ∧ v≤heap+limit*space
  let initial := startState (targetEpochPacket L F I tp qp src heap++[limit]) mem pos
  let first : State := {initial with regs := Function.update initial.regs 26 0}
  have hOne : 1<2^w := by omega
  obtain ⟨hlimitReg,hregs⟩ := targetTest_start_registers F I L tp qp src heap limit pos mem
  have hSrc : first.regs 20=src := by
    rw [show first.regs 20=initial.regs 20 by simp [first]]
    exact hregs 20 (by decide)
  have hHeap : first.regs 21=heap := by
    rw [show first.regs 21=initial.regs 21 by simp [first]]
    exact hregs 21 (by decide)
  have hfirst : Inv 0 first := by
    unfold Inv TargetTestInvariant
    dsimp only
    rw [hSrc,hHeap]
    refine ⟨by simp [first],by simpa [first] using hlimitReg,?_,hWords,le_rfl,by simp,
      fun _ _ => rfl,hzero,hflow,?_,?_,by omega,fun _ => rfl⟩
    · intro j hj
      simpa only [first,Function.update_of_ne (by omega : j≠26)] using hregs j hj
    · intro _
      simp [first,initial,startState]
    · intro h
      unfold targetTestLimit at h
      omega
  have hinit : Runs w p ω (.assign 26 (.const 0)) initial .normal first 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const (by omega),rfl,rfl,rfl⟩
  have hLoop := Triple.forUp (r:=26) (hi:=.reg 23) (body:=targetTestStep epoch)
    (Inv:=Inv) (Q_ret:=Q) (fun _ => price+50) 0 limit hOne (fun _ => hlimit)
    (fun i st _ _ h => h.1) (fun i st _ _ h => by change some (st.regs 23)=some limit; exact congrArg some h.2.1) (by
      intro i _ hi st ω' h
      have hcurr : st.regs 21≤heap+i*space := h.2.2.2.2.2.1
      have hmul := Nat.mul_le_mul_right space (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hmul
      obtain ⟨out,res,c,hrun,hres,hend,hcost⟩ := hstage st i ω' h (by omega)
      obtain ⟨o,final,c',hRun,hPost,hCost⟩ := targetTest_advance F I U k L tp qp src heap space i target mem
        st ω' hbody hTwo hm hsize h out c res hrun hres hend
      refine ⟨o,final,c',hRun,?_,?_⟩
      · cases o with
        | normal => exact hPost
        | returned v => exact ⟨hPost.1,hPost.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right space (Nat.succ_le_of_lt hi)) _)⟩
      · change c'≤price+50
        omega)
  obtain ⟨o,st,c,hRun,hPost,hCost⟩ := hLoop first ω hfirst
  have hC : c≤limit*(price+59)+4 := by
    change c≤rangeCost (fun _ => price+50) 0 limit+(limit-0)*(1+8)+(1+3) at hCost
    simpa only [rangeCost_const,Nat.sub_zero,← Nat.mul_add,Nat.reduceAdd] using hCost
  cases o with
  | returned v =>
    obtain ⟨hres,hEnd⟩ := hPost
    have hseq : Runs w p ω (forUp 26 (.reg 23) (targetTestStep epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) first (.returned v) st (c+1) :=
      runs_seq_iff.mpr (Or.inl ⟨v,c,hRun,rfl,rfl⟩)
    exact ⟨v,st,c+4,runs_seq_iff.mpr (Or.inr ⟨first,2,c+1,hinit,hseq,by omega⟩),
      hres,hEnd.trans (Nat.le_add_right _ _),by change c+4≤limit*(price+59)+50; omega⟩
  | normal =>
    have hInv : Inv limit st := by simpa only [Nat.zero_max] using hPost
    obtain ⟨_,_,_,hWords',hLo,hHi,hFrame,hZ,_,_,hFail,hRoot,_⟩ := hInv
    let ptr := st.regs 20
    let cur := st.regs 21
    have hPtr : ptr<2^w := hWords' ptr (by simp [targetEpochPacket,ptr])
    have hCur : cur<2^w := hWords' cur (by simp [targetEpochPacket,cur])
    have hzeroW : 0<2^w := by omega
    have hArgs : evalArgs w st [.reg 20,.const 0,.reg 21]=some [ptr,0,cur] := by
      eval_expr
    have hFit : cur+2<2^w := by omega
    obtain ⟨v,final,d,hRet,hRecord,hV,hD⟩ := targetEpochReturn_runs st ω (.reg 20) (.const 0) (.reg 21)
      hrecord hArgs (by wram_words) (by decide) hZ hFit
    have hVeq : v=cur+2 := hRecord.2
    have hStatus : final.mem (cur+1)=0 := hRecord.1.2.2.2.2.2
    have hIdx : v-1=cur+1 := by omega
    have hFrame' : ∀ z<heap,final.mem z=mem z := fun z hz =>
      (hRecord.1.2.2.1 z (show z<cur by omega)).trans (hFrame z hz)
    have hresult : TargetTestResult F I U L.exponent src heap v target mem final.mem := by
      unfold TargetTestResult
      rw [hIdx,hStatus]
      exact ⟨by omega,hV,hRecord.1.2.2.2.1,hFrame',by decide,fun _ => ⟨hRoot (Nat.succ_pos _),hFail rfl⟩,by simp⟩
    have htail : Runs w p ω (forUp 26 (.reg 23) (targetTestStep epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) first (.returned v) final (c+d+1) :=
      runs_seq_iff.mpr (Or.inr ⟨st,c,d,hRun,hRet,rfl⟩)
    have hReturnCost : d≤37 := hD
    exact ⟨v,final,c+d+4,runs_seq_iff.mpr (Or.inr ⟨first,2,c+d+1,hinit,htail,by omega⟩),
      hresult,by change v≤heap+limit*space+2; omega,
      by change c+d+4≤limit*(price+59)+50; omega⟩

/-- `V`-passing variant of `targetTest_runs_of_stage`. -/
theorem targetTestWithV_runs_of_stage {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U k V : ℕ) (L : EpochLayout) (tp qp src heap space price : ℕ) (target : ℝ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {epoch record : ℕ} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hTwo : 2<2^w) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (hWords : ∀ z∈targetEpochPacket L F I tp qp src heap,z<2^w)
    (hV : V<2^w)
    (hlimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*space+2<2^w)
    (hflow : TargetStageFlow F I L.exponent src heap mem) (hzero : ZeroFrom mem heap)
    (hstage : ∀ st i (stream : ℕ → Bool),
      TargetTestInvariant F I U k L tp qp src heap space target mem i st →
      st.regs 27=V →
      st.regs 21+space<2^w →
      ∃ out final cost,
        Runs w p stream body
          (startState (targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21) ++ [V]) st.mem st.pos)
          (.returned out) final cost ∧
        TargetStageResult F I U L.exponent (1/(2:ℝ)^k) target (st.regs 20) (st.regs 21) out st.mem final.mem ∧
        out≤st.regs 21+space ∧ cost≤price) :
    let limit := targetTestLimit I.m U k
    ∃ v final cost,
      Runs w p ω (targetTestBodyWithV epoch record)
        (startState (targetEpochPacket L F I tp qp src heap++[limit,V]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U L.exponent src heap v target mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  dsimp only
  let limit := targetTestLimit I.m U k
  change heap+limit*space+2<2^w at hspace
  let Inv := fun i st => TargetTestInvariant F I U k L tp qp src heap space target mem i st ∧ st.regs 27 = V
  let Q := fun v (st : State) => TargetTestResult F I U L.exponent src heap v target mem st.mem ∧ v≤heap+limit*space
  let initial := startState (targetEpochPacket L F I tp qp src heap++[limit,V]) mem pos
  let saved : State := {initial with regs := Function.update initial.regs 27 V}
  let first : State := {saved with regs := Function.update saved.regs 26 0}
  have hOne : 1<2^w := by omega
  have hlen : (targetEpochPacket L F I tp qp src heap).length=23 := targetEpochPacket_length F I L tp qp src heap
  have hsaveReg : initial.regs 24=V := by
    simp [initial,startState,targetEpochPacket]
  have hsave : Runs w p ω (.assign 27 (.reg 24)) initial .normal saved 2 :=
    runs_assign_iff.mpr ⟨V,by simp [Expr.eval,hsaveReg],rfl,rfl,rfl⟩
  have hlimitReg : first.regs 23=limit := by
    simp [first,saved,initial,startState,targetEpochPacket]
  have hregs0 : ∀ j<23,initial.regs j=(targetEpochPacket L F I tp qp src heap).getD j 0 := by
    intro j hj
    change (targetEpochPacket L F I tp qp src heap++[limit,V]).getD j 0=_
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left (hlen ▸ hj)]
  have hSrc : first.regs 20=src := by
    change saved.regs 20=src
    change initial.regs 20=src
    exact (hregs0 20 (by decide)).trans (by simp [targetEpochPacket])
  have hHeap : first.regs 21=heap := by
    change saved.regs 21=heap
    change initial.regs 21=heap
    exact (hregs0 21 (by decide)).trans (by simp [targetEpochPacket])
  have hfirst : Inv 0 first := by
    refine ⟨?_,by simp [first,saved]⟩
    unfold TargetTestInvariant
    dsimp only
    rw [hSrc,hHeap]
    refine ⟨by simp [first],hlimitReg,?_,hWords,le_rfl,by simp,fun _ _ => rfl,hzero,hflow,?_,?_,by omega,fun _ => rfl⟩
    · intro j hj
      simpa only [first,saved,Function.update_of_ne (by omega : j≠26),Function.update_of_ne (by omega : j≠27)] using hregs0 j hj
    · intro _
      simp [first,saved,initial,startState]
    · intro h
      unfold targetTestLimit at h
      omega
  have hinit : Runs w p ω (.assign 26 (.const 0)) saved .normal first 2 :=
    runs_assign_iff.mpr ⟨0,Expr.eval_const (by omega),rfl,rfl,rfl⟩
  have hLoop := Triple.forUp (r:=26) (hi:=.reg 23) (body:=targetTestStepWithV epoch)
    (Inv:=Inv) (Q_ret:=Q) (fun _ => price+50) 0 limit hOne (fun _ => hlimit)
    (fun i st _ _ h => h.1.1) (fun i st _ _ h => by change some (st.regs 23)=some limit; exact congrArg some h.1.2.1) (by
      intro i _ hi st ω' h
      have hcurr : st.regs 21≤heap+i*space := h.1.2.2.2.2.2.1
      have hmul := Nat.mul_le_mul_right space (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hmul
      obtain ⟨out,res,c,hrun,hres,hend,hcost⟩ := hstage st i ω' h.1 h.2 (by omega)
      obtain ⟨o,final,c',hRun,hPost,hCost⟩ := targetTestWithV_advance F I U k L tp qp src heap space i V target mem
        st ω' hbody hTwo hm hsize h.1 h.2 hV out c res hrun hres hend
      refine ⟨o,final,c',hRun,?_,?_⟩
      · cases o with
        | normal => exact hPost
        | returned v => exact ⟨hPost.1,hPost.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right space (Nat.succ_le_of_lt hi)) _)⟩
      · change c'≤price+50
        omega)
  obtain ⟨o,st,c,hRun,hPost,hCost⟩ := hLoop first ω hfirst
  have hC : c≤limit*(price+59)+4 := by
    change c≤rangeCost (fun _ => price+50) 0 limit+(limit-0)*(1+8)+(1+3) at hCost
    simpa only [rangeCost_const,Nat.sub_zero,← Nat.mul_add,Nat.reduceAdd] using hCost
  cases o with
  | returned v =>
    obtain ⟨hres,hEnd⟩ := hPost
    have hseq : Runs w p ω (forUp 26 (.reg 23) (targetTestStepWithV epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) first (.returned v) st (c+1) :=
      runs_seq_iff.mpr (Or.inl ⟨v,c,hRun,rfl,rfl⟩)
    have hinner : Runs w p ω (.assign 26 (.const 0) ;;
        forUp 26 (.reg 23) (targetTestStepWithV epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) saved (.returned v) st (c+4) :=
      runs_seq_iff.mpr (Or.inr ⟨first,2,c+1,hinit,hseq,by omega⟩)
    exact ⟨v,st,c+7,runs_seq_iff.mpr (Or.inr ⟨saved,2,c+4,hsave,hinner,by omega⟩),
      hres,hEnd.trans (Nat.le_add_right _ _),by change c+7≤limit*(price+59)+50; omega⟩
  | normal =>
    have hInv : TargetTestInvariant F I U k L tp qp src heap space target mem limit st := by
      simpa only [Nat.zero_max] using hPost.1
    obtain ⟨_,_,_,hWords',hLo,hHi,hFrame,hZ,_,_,hFail,hRoot,_⟩ := hInv
    let ptr := st.regs 20
    let cur := st.regs 21
    have hPtr : ptr<2^w := hWords' ptr (by simp [targetEpochPacket,ptr])
    have hCur : cur<2^w := hWords' cur (by simp [targetEpochPacket,cur])
    have hzeroW : 0<2^w := by omega
    have hArgs : evalArgs w st [.reg 20,.const 0,.reg 21]=some [ptr,0,cur] := by
      eval_expr
    have hFit : cur+2<2^w := by omega
    obtain ⟨v,final,d,hRet,hRecord,hVout,hD⟩ := targetEpochReturn_runs st ω (.reg 20) (.const 0) (.reg 21)
      hrecord hArgs (by wram_words) (by decide) hZ hFit
    have hStatus : final.mem (cur+1)=0 := hRecord.1.2.2.2.2.2
    have hIdx : v-1=cur+1 := by have hVeq : v=cur+2 := hRecord.2; omega
    have hFrame' : ∀ z<heap,final.mem z=mem z := fun z hz =>
      (hRecord.1.2.2.1 z (show z<cur by omega)).trans (hFrame z hz)
    have hresult : TargetTestResult F I U L.exponent src heap v target mem final.mem := by
      unfold TargetTestResult
      rw [hIdx,hStatus]
      exact ⟨by have := hRecord.2; omega,hVout,hRecord.1.2.2.2.1,hFrame',by decide,fun _ => ⟨hRoot (Nat.succ_pos _),hFail rfl⟩,by simp⟩
    have htail : Runs w p ω (forUp 26 (.reg 23) (targetTestStepWithV epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) first (.returned v) final (c+d+1) :=
      runs_seq_iff.mpr (Or.inr ⟨st,c,d,hRun,hRet,rfl⟩)
    have hinner : Runs w p ω (.assign 26 (.const 0) ;;
        forUp 26 (.reg 23) (targetTestStepWithV epoch) ;;
        targetEpochReturn record (.reg 20) (.const 0) (.reg 21)) saved (.returned v) final (c+d+4) :=
      runs_seq_iff.mpr (Or.inr ⟨first,2,c+d+1,hinit,htail,by omega⟩)
    have hReturnCost : d≤37 := hD
    exact ⟨v,final,c+d+7,runs_seq_iff.mpr (Or.inr ⟨saved,2,c+d+4,hsave,hinner,by omega⟩),
      hresult,by change v≤heap+limit*space+2; have := hRecord.2; omega,
      by change c+d+7≤limit*(price+59)+50; omega⟩

end MinCostFlow.IPM.Machine
