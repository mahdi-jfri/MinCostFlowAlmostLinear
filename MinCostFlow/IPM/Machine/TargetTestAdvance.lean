module

public import MinCostFlow.IPM.Machine.TargetTestInvariant
public import MinCostFlow.IPM.Machine.TargetTestStepRun
import Mathlib.Tactic.LinearCombination

/-!
# Advancing the bounded target test by one verified stage

The caller only advances after a complete epoch. Rejection or
convergence returns its exact record. The last iteration can
continue only when the original upper-target promise fails.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Shared step-advance logic parameterized by the caller step statement. -/
private theorem targetTest_advance_of_step {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U k : ℕ) (L : EpochLayout) (tp qp src heap space i : ℕ) (target : ℝ)
    (mem : ℕ → ℕ) (st : State) {step : Stmt} {ω : ℕ → Bool} {p : Program}
    (hm : 0<I.m) (hsize : 2≤I.m*U)
    (h : TargetTestInvariant F I U k L tp qp src heap space target mem i st)
    (v c : ℕ) (result : State)
    (hresult : TargetStageResult F I U L.exponent (1/(2:ℝ)^k) target (st.regs 20) (st.regs 21) v st.mem result.mem)
    (hspace : v≤st.regs 21+space)
    (hstep : ∃ o final cost,
      Runs w p ω step st o final cost ∧ final.mem=result.mem ∧
      (if result.mem (v-1)=2 then o=.normal ∧ final.regs 20=result.mem (v-2) ∧ final.regs 21=v
        else o=.returned v) ∧
      (∀ j,j≠20 → j≠21 → j≠24 → j≠25 → final.regs j=st.regs j) ∧ cost≤c+50) :
    ∃ o final cost,
      Runs w p ω step st o final cost ∧
      (match o with
      | .returned out => TargetTestResult F I U L.exponent src heap out target mem final.mem ∧ out≤heap+(i+1)*space
      | .normal => TargetTestInvariant F I U k L tp qp src heap space target mem (i+1)
          { final with regs := Function.update final.regs 26 (i+1) } ∧ final.regs 26=i ∧
          (∀ j,j≠20 → j≠21 → j≠24 → j≠25 → final.regs j=st.regs j)) ∧
      cost≤c+50 := by
  let counter := targetTestLimit I.m U k
  let a := Num.IPM.alphaPrime I.m U
  let q := (1/(2:ℝ)^k)*a/32
  let original := epochVector F I mem src
  let current := epochVector F I st.mem (st.regs 20)
  let status := result.mem (v-1)
  let ptr := result.mem (v-2)
  obtain ⟨hIndex,hLimit,hRegs,hWords,hLo,hHi,hFrame,_,hFlow,hProgress,_,hRoot,hInitial⟩ := h
  obtain ⟨hVLo,hVWord,hZero,hVFrame,hStatus,hFail,hFinish,hContinue⟩ := hresult
  obtain ⟨o,final,d,hRun,hMem,hOut,hRegFrame,hCost⟩ := hstep
  have hnext : v≤heap+(i+1)*space := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hPrefix : ∀ z<heap,result.mem z=mem z :=
    fun z hz => (hVFrame z (hz.trans_le hLo)).trans (hFrame z hz)
  have hPromise (hp : TargetStagePromise I U target original) : TargetStagePromise I U target current :=
    targetTest_promise_at_flow I U i a q target original current rfl hp (hProgress hp)
  have hInitialResidual (hnonterminal : 1/4<residual I target current) :
      1/4<residual I target original := by
    by_cases hpos : 0 < i
    · exact hRoot hpos
    · have hzero : i=0 := by omega
      -- At stage zero the explicit pointer and flow still name the original input.
      change 1/4<residual I target (epochVector F I mem src)
      rw [← hInitial hzero]
      exact hnonterminal
  by_cases hb : status=2
  · have hb' : result.mem (v-1)=2 := hb
    rw [ite_eq_left hb'] at hOut
    obtain ⟨rfl,hSrc,hHeap⟩ := hOut
    obtain ⟨hNew,hResidual,hDrop⟩ := hContinue hb'
    have hNew' : TargetStageFlow F I L.exponent ptr v result.mem := hNew
    have hPtrWord : ptr<2^w := (Nat.le_add_right _ _).trans_lt (hNew'.1.trans_lt hVWord)
    have hWords' := targetEpochPacket_words F I L tp qp (st.regs 20) (st.regs 21) ptr v hWords hPtrWord hVWord
    have hRegs' : ∀ j<23,final.regs j=(targetEpochPacket L F I tp qp ptr v).getD j 0 := by
      intro j hj
      by_cases h20 : j=20
      · subst j
        exact hSrc
      by_cases h21 : j=21
      · subst j
        exact hHeap
      exact (hRegFrame j h20 h21 (by omega) (by omega)).trans
        ((hRegs j hj).trans (targetEpochPacket_fixed F I L tp qp _ _ ptr v j hj h20 h21))
    have hFinalIndex := hRegFrame 26 (by decide) (by decide) (by decide) (by decide)
    have hFinalLimit := hRegFrame 23 (by decide) (by decide) (by decide) (by decide)
    have hpaid (hp : TargetStagePromise I U target original) :
        potential I a target (epochVector F I result.mem ptr)≤
          potential I a target original-(I.m:ℝ)*((i+1:ℕ):ℝ)*q^2/2000 := by
      have hh := hDrop (hPromise hp)
      have hc := hProgress hp
      change potential I a target (epochVector F I result.mem ptr)≤potential I a target current-(I.m:ℝ)*q^2/2000 at hh
      change potential I a target current≤potential I a target original-(I.m:ℝ)*(i:ℝ)*q^2/2000 at hc
      push_cast
      linear_combination hh + hc
    have hLast (hEnd : i+1=counter) (hp : TargetStagePromise I U target original) : False := by
      have hi' : i=dyadicEpochLimit (I.m.size+U.size) k (Num.IPM.alphaExponent I.m U) :=
        Nat.add_right_cancel hEnd
      apply targetTest_last_stage_terminal I U k target original current hm hsize hFlow.inside hResidual hp
      rw [← hi']
      exact hProgress hp
    let next := { final with regs := Function.update final.regs 26 (i+1) }
    have hnext20 : next.regs 20=ptr := by simpa [next] using hSrc
    have hnext21 : next.regs 21=v := by simpa [next] using hHeap
    have hnextReg : ∀ j<23,next.regs j=(targetEpochPacket L F I tp qp ptr v).getD j 0 := by
      intro j hj
      simpa only [next,Function.update_of_ne (by omega : j≠26)] using hRegs' j hj
    have hNextInv : TargetTestInvariant F I U k L tp qp src heap space target mem (i+1) next := by
      unfold TargetTestInvariant
      dsimp only
      rw [hnext20,hnext21]
      change next.regs 26=i+1 ∧ next.regs 23=counter ∧ _
      refine ⟨by simp [next],by simpa [next,hLimit] using hFinalLimit,hnextReg,hWords',by omega,hnext,?_,?_,?_,?_,hLast,fun _ => hInitialResidual hResidual,by omega⟩
      · exact hMem ▸ hPrefix
      · exact hMem ▸ hZero
      · exact hMem ▸ hNew'
      · exact hMem ▸ hpaid
    exact ⟨.normal,final,d,hRun,⟨hNextInv,hFinalIndex.trans hIndex,hRegFrame⟩,hCost⟩
  · have hb' : result.mem (v-1)≠2 := hb
    rw [ite_eq_right hb'] at hOut
    subst o
    have ht : TargetTestResult F I U L.exponent src heap v target mem result.mem :=
      ⟨by omega,hVWord,hZero,hPrefix,by omega,fun hbad => ⟨hInitialResidual (hFail hbad).1,fun hp => (hFail hbad).2 (hPromise hp)⟩,hFinish⟩
    exact ⟨.returned v,final,d,hRun,⟨hMem ▸ ht,hnext⟩,hCost⟩

set_option maxHeartbeats 450000 in
/-- Execute one caller step using the actual stage result and preserve
the outer fixed-point and progress invariants. -/
theorem targetTest_advance {w epoch : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U k : ℕ) (L : EpochLayout) (tp qp src heap space i : ℕ) (target : ℝ)
    (mem : ℕ → ℕ) (st : State) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hTwo : 2<2^w) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (h : TargetTestInvariant F I U k L tp qp src heap space target mem i st)
    (v c : ℕ) (result : State)
    (hrun : Runs w p ω body
      (startState (targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21)) st.mem st.pos)
      (.returned v) result c)
    (hresult : TargetStageResult F I U L.exponent (1/(2:ℝ)^k) target (st.regs 20) (st.regs 21) v st.mem result.mem)
    (hspace : v≤st.regs 21+space) :
    ∃ o final cost,
      Runs w p ω (targetTestStep epoch) st o final cost ∧
      (match o with
      | .returned out => TargetTestResult F I U L.exponent src heap out target mem final.mem ∧ out≤heap+(i+1)*space
      | .normal => TargetTestInvariant F I U k L tp qp src heap space target mem (i+1)
          { final with regs := Function.update final.regs 26 (i+1) } ∧ final.regs 26=i) ∧
      cost≤c+50 := by
  have hArgs := targetTestStep_args (w:=w) F I L tp qp (st.regs 20) (st.regs 21) st h.2.2.1
  have hstep := targetTestStep_runs st result ω hbody hArgs hrun hresult.2.1 hTwo rfl hresult.2.2.2.2.1 rfl
  obtain ⟨o,final,cost,hRun,hPost,hCost⟩ := targetTest_advance_of_step F I U k L tp qp src heap space i
    target mem st hm hsize h v c result hresult hspace hstep
  refine ⟨o,final,cost,hRun,?_,hCost⟩
  cases o with
  | returned _ => exact hPost
  | normal => exact ⟨hPost.1,hPost.2.1⟩

/-- `V`-passing variant of `targetTest_advance`. -/
theorem targetTestWithV_advance {w epoch : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U k : ℕ) (L : EpochLayout) (tp qp src heap space i V : ℕ) (target : ℝ)
    (mem : ℕ → ℕ) (st : State) (ω : ℕ → Bool) {p : Program} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hTwo : 2<2^w) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (h : TargetTestInvariant F I U k L tp qp src heap space target mem i st)
    (hVreg : st.regs 27=V) (_hVword : V<2^w)
    (v c : ℕ) (result : State)
    (hrun : Runs w p ω body
      (startState (targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21) ++ [V]) st.mem st.pos)
      (.returned v) result c)
    (hresult : TargetStageResult F I U L.exponent (1/(2:ℝ)^k) target (st.regs 20) (st.regs 21) v st.mem result.mem)
    (hspace : v≤st.regs 21+space) :
    ∃ o final cost,
      Runs w p ω (targetTestStepWithV epoch) st o final cost ∧
      (match o with
      | .returned out => TargetTestResult F I U L.exponent src heap out target mem final.mem ∧ out≤heap+(i+1)*space
      | .normal => (TargetTestInvariant F I U k L tp qp src heap space target mem (i+1)
          { final with regs := Function.update final.regs 26 (i+1) } ∧
          ({ final with regs := Function.update final.regs 26 (i+1) }).regs 27 = V) ∧
          final.regs 26=i) ∧
      cost≤c+50 := by
  have hArgs0 := targetTestStep_args (w:=w) F I L tp qp (st.regs 20) (st.regs 21) st h.2.2.1
  have hArgs : evalArgs w st ((List.range 23).map Expr.reg ++ [.reg 27]) =
      some (targetEpochPacket L F I tp qp (st.regs 20) (st.regs 21) ++ [V]) :=
    evalArgs_append hArgs0 (by simp [evalArgs,Expr.eval,hVreg])
  have hstep := targetTestStepWithV_runs st result ω hbody hArgs hrun hresult.2.1 hTwo rfl hresult.2.2.2.2.1 rfl
  obtain ⟨o,final,cost,hRun,hPost,hCost⟩ := targetTest_advance_of_step F I U k L tp qp src heap space i
    target mem st hm hsize h v c result hresult hspace hstep
  refine ⟨o,final,cost,hRun,?_,hCost⟩
  cases o with
  | returned _ => exact hPost
  | normal =>
    refine ⟨⟨hPost.1,?_,⟩,hPost.2.1⟩
    simp [hPost.2.2 27 (by decide) (by decide) (by decide) (by decide),hVreg]

end MinCostFlow.IPM.Machine
