module

public import MinCostFlow.Scaling.BottleneckStateLayout
public import MinCostFlow.Scaling.WordFiveProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Retaining the result of one bottleneck test

A negative signed objective advances the lower endpoint and retains the
new threshold and flow. Otherwise the midpoint becomes the upper endpoint
and the previous best result is copied. Both branches write a fresh
five-word header, preserving every referenced flow.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[state,mid,threshold,flow,objectiveSign,heap]`. -/
def bottleneckUpdateBody (writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 4) (.const 1))
    (.call 6 writer [.bin .add (.reg 1) (.const 1),.load (.bin .add (.reg 0) (.const 1)),
      .const 1,.reg 2,.reg 3,.reg 5] ;; .ret (.reg 6))
    (.call 6 writer [.load (.reg 0),.reg 1,.load (.bin .add (.reg 0) (.const 2)),
      .load (.bin .add (.reg 0) (.const 3)),.load (.bin .add (.reg 0) (.const 4)),.reg 5] ;;
      .ret (.reg 6))

/-- The header update and the shared five-word writer. -/
def bottleneckUpdateModule (b : ℕ) : List Stmt := [bottleneckUpdateBody (b+1),wordFiveBody]

/-- Updating interval endpoints and optional best flow is a constant-cost
operation on stored data. Both source headers and flow arrays precede heap. -/
def bottleneckUpdateContract (w : ℕ) {J : Circulation} (s : BottleneckState J)
    (mid threshold : ℕ) (flow : Fin J.m → ℤ) (objective : ℤ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ base ptr heap,args=[base,mid,threshold,ptr,if objective<0 then 1 else 0,heap] ∧
      BottleneckStateAt mem base s ∧ base+5 ≤ heap ∧ ptr+J.m ≤ heap ∧
      J.readSolverFlow mem ptr=flow ∧ mid+1<2^w ∧
      (∀ i<5,mem (base+i)<2^w) ∧
      (∀ u f,s.best=some (u,f) → mem (base+4)+J.m ≤ heap))
    (fun _ _ _ => True) (fun _ _ => 140) (fun _ _ => 5)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+5 ∧
      BottleneckStateAt mem' (ret-5) (if objective<0 then ⟨mid+1,s.upper,some (threshold,flow)⟩ else {s with upper:=mid}) ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u f,(if objective<0 then (⟨mid+1,s.upper,some (threshold,flow)⟩ : BottleneckState J)
        else {s with upper:=mid}).best=some (u,f) → mem' (ret-5+4)+J.m ≤ ret) }

/-- Header updates use no random instruction. -/
theorem bottleneckUpdateModule_noRand (b : ℕ) : ∀ body ∈ bottleneckUpdateModule b,body.NoRand := by
  simp only [bottleneckUpdateModule,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨by simp only [bottleneckUpdateBody,Stmt.NoRand,and_self],wordFiveBody_noRand⟩

private theorem update_read_preserved (J : Circulation) {mem mem' : ℕ → ℕ} {ptr heap : ℕ}
    {flow : Fin J.m → ℤ} (hread : J.readSolverFlow mem ptr=flow)
    (hbound : ptr+J.m ≤ heap) (hframe : ∀ x<heap,mem' x=mem x) :
    J.readSolverFlow mem' ptr=flow := by
  funext e
  have h := congrFun hread e
  change (mem' (ptr+e.val) : ℤ)=flow e
  change (mem (ptr+e.val) : ℤ)=flow e at h
  rw [hframe (ptr+e.val) (by have hi := e.isLt; omega)]
  exact h

/-- Both branches implement the model's acceptance update exactly,
including preservation of the previous best flow after a failed test. -/
theorem bottleneckUpdate_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (bottleneckUpdateModule b)) {J : Circulation} (s : BottleneckState J)
    (mid threshold : ℕ) (flow : Fin J.m → ℤ) (objective : ℤ) :
    MeetsContract w p b (bottleneckUpdateContract w s mid threshold flow objective) := by
  have hwriter : p.HasAt (b+1) wordFiveModule := hasAt_tail hp
  have hk := wordFive_meetsContract (w := w) hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨base,ptr,heap,rfl,hstate,hbase,hptr,hread,hmid,hheader,hbestBound⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+5<2^w at hs
  have hh : heap<2^w := by omega
  have hb : base<2^w := by omega
  have hb1 : base+1<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb3 : base+3<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hmid0 : mid<2^w := by omega
  have hthreshold : threshold<2^w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hpword : ptr<2^w := by omega
  have hw : 1<2^w := by omega
  have hl := hstate.1
  have hu := hstate.2.1
  have hupper : s.upper<2^w := by simpa only [hu] using hheader 1 (by decide)
  have h0 : mem base<2^w := by simpa only [Nat.add_zero] using hheader 0 (by decide)
  have hlower : s.lower<2^w := by rw [←hl]; exact h0
  have h2 := hheader 2 (by decide)
  have h3 := hheader 3 (by decide)
  have h4 := hheader 4 (by decide)
  apply runs_start_le
  unfold bottleneckUpdateBody
  wram_step
  · have hnegative : objective<0 := by
      by_contra hn
      simp [hn] at hcond
    refine runs_seq_call_le hk (vs := [mid+1,s.upper,1,threshold,ptr,heap]) (by eval_expr) (by wram_words)
      ⟨⟨mid+1,s.upper,1,threshold,ptr,heap,rfl⟩,hz,hs⟩ ?_
    intro ret memR posR hpost
    obtain ⟨⟨hlo,hhi,hframe,hzR,hat⟩,hret⟩ := hpost
    change ret=heap+5 at hret
    change (∀ x<heap,memR x=mem x) at hframe
    change ZeroFrom memR ret at hzR
    change ListAt memR heap [mid+1,s.upper,1,threshold,ptr] at hat
    have hr : ret<2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap≤ret ∧ ret≤heap+5 ∧ (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧
        ret=heap+5 ∧ BottleneckStateAt memR (ret-5) _ ∧ (∀ i<5,memR (ret-5+i)<2^w) ∧ _
      refine ⟨⟨by omega,by omega,hframe,hzR,True.intro⟩,hret,?_,?_,?_⟩
      · simp only [hnegative,↓reduceIte,hret,Nat.add_sub_cancel]
        exact bottleneckStateAt_of_header_some hat (update_read_preserved J hread hptr hframe)
      · intro i hi
        have hcell := hat i (by change i<5; exact hi)
        have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
        rw [hret,Nat.add_sub_cancel]
        rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.getElem_cons_zero,List.getElem_cons_succ] at hcell <;> rw [hcell] <;> omega
      · intro u f _
        have hp := hat 4 (by change 4<5; decide)
        change memR (heap+4)=ptr at hp
        change memR (ret-5+4)+J.m ≤ ret
        rw [hret,Nat.add_sub_cancel,hp]
        omega
    · simp only [bottleneckUpdateContract,wordFiveContract,heapContract,argsSize_cons,argsSize_nil,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega
  · have hnegative : ¬objective<0 := by
      intro hn
      simp [hn] at hcond
    refine runs_seq_call_le hk (vs := [mem base,mid,mem (base+2),mem (base+3),mem (base+4),heap])
      (by eval_expr) (by wram_words) ⟨⟨mem base,mid,mem (base+2),mem (base+3),mem (base+4),heap,rfl⟩,hz,hs⟩ ?_
    intro ret memR posR hpost
    obtain ⟨⟨_,_,hframe,hzR,hat⟩,hret⟩ := hpost
    change ret=heap+5 at hret
    change (∀ x<heap,memR x=mem x) at hframe
    change ZeroFrom memR ret at hzR
    change ListAt memR heap [mem base,mid,mem (base+2),mem (base+3),mem (base+4)] at hat
    have hr : ret<2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap≤ret ∧ ret≤heap+5 ∧ (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧
        ret=heap+5 ∧ BottleneckStateAt memR (ret-5) _ ∧ (∀ i<5,memR (ret-5+i)<2^w) ∧ _
      refine ⟨⟨by omega,by omega,hframe,hzR,True.intro⟩,hret,?_,?_,?_⟩
      · simp only [hnegative,↓reduceIte,hret,Nat.add_sub_cancel]
        have hlow : mem base=s.lower := hl
        rw [hlow] at hat
        cases heq : s.best with
        | none =>
          have hflag := hstate.2.2
          rw [heq] at hflag
          rw [hflag] at hat
          have hout := bottleneckStateAt_of_header_none (J := J) hat
          simpa only [BottleneckStateAt,heq] using hout
        | some pair =>
          obtain ⟨u,f⟩ := pair
          have hbest := hstate.2.2
          rw [heq] at hbest
          obtain ⟨hflag,hu,hf⟩ := hbest
          rw [hflag,hu] at hat
          have hreadR := update_read_preserved J hf (hbestBound u f heq) hframe
          have hout := bottleneckStateAt_of_header_some hat hreadR
          simpa only [BottleneckStateAt,heq] using hout
      · intro i hi
        have hcell := hat i (by change i<5; exact hi)
        have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
        rw [hret,Nat.add_sub_cancel]
        rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
          simp only [List.getElem_cons_zero,List.getElem_cons_succ] at hcell <;> rw [hcell] <;> omega
      · intro u f hbestNew
        simp only [hnegative,↓reduceIte] at hbestNew
        have hbound := hbestBound u f hbestNew
        have hp := hat 4 (by change 4<5; decide)
        change memR (heap+4)=mem (base+4) at hp
        change memR (ret-5+4)+J.m ≤ ret
        rw [hret,Nat.add_sub_cancel,hp]
        omega
    · simp only [bottleneckUpdateContract,wordFiveContract,heapContract,argsSize_cons,argsSize_nil,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

end MinCostFlow.Scaling.Machine
