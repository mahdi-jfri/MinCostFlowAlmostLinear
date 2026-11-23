module

public import MinCostFlow.IPM.Machine.EpochStartupTail
import WordRAM.Tactic

/-!
# The complete startup call with the original initialized state

The outer startup forwards the fifteen numerical Init arguments.
The remaining three words name the scan limits. The actual returned
budget record determines the name-list address, so the scan uses the
same memory and arrays established by Init.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Compose the actual numeric startup with the read-only full scan.
The final successful endpoint retains the original credited state. -/
theorem epochStartup_runs_of_start {w h start scan flag m cp rp lo fp up ap one L P E la ga heap graph
    neg mx mn startEnd names cost : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ} {st : State} {body : Stmt}
    (hbody : p.procs[start]?=some body)
    (hstart : Runs w p ω body (startState [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph] mem pos)
      (.returned startEnd) st cost)
    (hscan : MeetsContract w p scan (coefficientRangeListContract w h))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hfit : startEnd+1<2^w) (hThree : 3<2^w)
    (hEnd : startEnd=names+m+3)
    (hgr : heap+la<2^w)
    (hwords : ∀ z∈[names,m,heap+la,heap,neg,mx,mn,L],z<2^w)
    (hpre : (coefficientRangeListContract w h).pre [names,m,heap+la,heap,neg,mx,mn,L] st.mem)
    (hbit : st.mem (startEnd-1)=1) (hz : ZeroFrom st.mem startEnd) :
    let input := [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,neg,mx,mn]
    ∃ v final c bit,
      Runs w p ω (epochStartupBody start scan flag) (startState input mem pos) (.returned v) final c ∧
      (coefficientRangeListContract w h).post [names,m,heap+la,heap,neg,mx,mn,L] st.mem bit st.mem ∧
      (if bit=1 then v=startEnd ∧ final.mem=st.mem
        else (flagRecordContract w).post [0,startEnd] st.mem v final.mem) ∧
      final.mem (v-1)=bit ∧ v<2^w ∧ c≤cost+m*(164*L+500)+167 := by
  dsimp only
  let input := [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,neg,mx,mn]
  let initial := startState input mem pos
  let after : State := ⟨st.mem,Function.update initial.regs 18 startEnd,st.pos⟩
  have hinit : Runs w p ω (.call 18 start ((List.range 15).map Expr.reg))
      initial .normal after (cost+16) := by
    apply runs_call_iff.mpr
    refine ⟨[m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph],body,.returned startEnd,st,cost,
      rfl,hbody,hstart,rfl,?_,?_⟩
    · cases st
      rfl
    · change cost+16=15+cost+1
      omega
  have hHeap : after.regs 18=startEnd := by simp [after]
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hMinus : startEnd-3<2^w := by omega
  have hNames : startEnd-3-m=names := by omega
  have hArguments : evalArgs w after epochStartupScanArgs=some [names,m,heap+la,heap,neg,mx,mn,L] := by
    rw [← hNames]
    unfold epochStartupScanArgs
    dsimp only [after,initial,input]
    eval_expr
  obtain ⟨v,final,c,bit,hTail,hScan,hout,hFinalBit,hCost⟩ :=
    epochStartupTail_runs after ω hscan hflag hArguments hwords hpre hHeap hbit hz hfit hOne
  have hw : v<2^w := by
    split_ifs at hout
    · omega
    · have h := hout.2
      change v=startEnd+1 at h
      omega
  exact ⟨v,final,cost+16+c+1,bit,runs_seq_iff.mpr (Or.inr ⟨after,cost+16,c,hinit,hTail,rfl⟩),
    hScan,hout,hFinalBit,hw,by omega⟩

/-- `V`-passing variant of `epochStartup_runs_of_start`. -/
theorem epochStartupWithV_runs_of_start {w h start scan flag m cp rp lo fp up ap one L P E la ga heap graph
    neg mx mn V startEnd names cost : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ} {st : State} {body : Stmt}
    (hbody : p.procs[start]?=some body)
    (hstart : Runs w p ω body (startState [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,V] mem pos)
      (.returned startEnd) st cost)
    (hscan : MeetsContract w p scan (coefficientRangeListContract w h))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hfit : startEnd+1<2^w) (hThree : 3<2^w)
    (hEnd : startEnd=names+m+3)
    (hgr : heap+la<2^w)
    (hwords : ∀ z∈[names,m,heap+la,heap,neg,mx,mn,L],z<2^w)
    (hpre : (coefficientRangeListContract w h).pre [names,m,heap+la,heap,neg,mx,mn,L] st.mem)
    (hbit : st.mem (startEnd-1)=1) (hz : ZeroFrom st.mem startEnd) :
    let input := [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,neg,mx,mn,V]
    ∃ v final c bit,
      Runs w p ω (epochStartupBodyWithV start scan flag) (startState input mem pos) (.returned v) final c ∧
      (coefficientRangeListContract w h).post [names,m,heap+la,heap,neg,mx,mn,L] st.mem bit st.mem ∧
      (if bit=1 then v=startEnd ∧ final.mem=st.mem
        else (flagRecordContract w).post [0,startEnd] st.mem v final.mem) ∧
      final.mem (v-1)=bit ∧ v<2^w ∧ c≤cost+m*(164*L+500)+168 := by
  dsimp only
  let input := [m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,neg,mx,mn,V]
  let initial := startState input mem pos
  let after : State := ⟨st.mem,Function.update initial.regs 18 startEnd,st.pos⟩
  have hinit : Runs w p ω (.call 18 start ((List.range 15).map Expr.reg ++ [.reg 18]))
      initial .normal after (cost+17) := by
    apply runs_call_iff.mpr
    refine ⟨[m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,graph,V],body,.returned startEnd,st,cost,
      rfl,hbody,hstart,rfl,?_,?_⟩
    · cases st
      rfl
    · change cost+17=16+cost+1
      omega
  have hHeap : after.regs 18=startEnd := by simp [after]
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hMinus : startEnd-3<2^w := by omega
  have hNames : startEnd-3-m=names := by omega
  have hArguments : evalArgs w after epochStartupScanArgs=some [names,m,heap+la,heap,neg,mx,mn,L] := by
    rw [← hNames]
    unfold epochStartupScanArgs
    dsimp only [after,initial,input]
    eval_expr
  obtain ⟨v,final,c,bit,hTail,hScan,hout,hFinalBit,hCost⟩ :=
    epochStartupTail_runs after ω hscan hflag hArguments hwords hpre hHeap hbit hz hfit hOne
  have hw : v<2^w := by
    split_ifs at hout
    · omega
    · have h := hout.2
      change v=startEnd+1 at h
      omega
  exact ⟨v,final,cost+17+c+1,bit,runs_seq_iff.mpr (Or.inr ⟨after,cost+17,c,hinit,hTail,rfl⟩),
    hScan,hout,hFinalBit,hw,by omega⟩

end MinCostFlow.IPM.Machine
