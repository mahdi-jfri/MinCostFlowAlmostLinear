module

public import MinCostFlow.IPM.Machine.RefreshRecord
public import WordRAM.Logic
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Serializing a list of changed edges

Read each reported edge name, then its two endpoints in the shared
stride-five graph encoding. Append the six-word delete/reinsert record.
The counted loop preserves the name list and graph and tracks the exact
written prefix, with linear cost in the number of changed edges.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The exact words read and written by a changed-edge scan. -/
def refreshScanWords (mem : ℕ → ℕ) (a names k : ℕ) : List ℕ :=
  (List.range k).flatMap (fun i => let e := mem (names+i)
    [1,e,0,e,mem (a+5*e),mem (a+1+5*e)])

private theorem refreshScanWords_length (mem : ℕ → ℕ) (a names k : ℕ) :
    (refreshScanWords mem a names k).length=6*k := by
  simp [refreshScanWords,List.length_flatMap]
  omega

private theorem refreshScanWords_succ (mem : ℕ → ℕ) (a names i : ℕ) :
    refreshScanWords mem a names (i+1)=refreshScanWords mem a names i++
      [1,mem (names+i),0,mem (names+i),mem (a+5*mem (names+i)),mem (a+1+5*mem (names+i))] := by
  simp [refreshScanWords,List.range_succ,List.flatMap_append]

/-- Arguments `[tailAddress,names,count,heap]`. -/
def refreshScanBody (record : ℕ) : Stmt :=
  .assign 5 (.reg 3) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 6)))) ;;
     .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 6)))) ;;
     .call 5 record [.reg 6,.reg 7,.reg 8,.reg 5]) ;;
  .ret (.reg 5)

/-- Changed-edge scanner followed by its record writer. -/
def refreshScanModule (b : ℕ) : List Stmt := [refreshScanBody (b+1)] ++ refreshRecordModule

/-- Source names and endpoints are below the incoming heap and fit.
The scan writes six words per entry and returns their exact endpoint. -/
def refreshScanContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a names k heap,args=[a,names,k,heap] ∧ ∀ i < k,
      names+i < heap ∧ mem (names+i) < 2^w ∧
      a+1+5*mem (names+i) < heap ∧ mem (a+5*mem (names+i)) < 2^w ∧
      mem (a+1+5*mem (names+i)) < 2^w)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (refreshScanWords mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)))
    (fun args _ => 180*args.getD 2 0+200) (fun args _ => 6*args.getD 2 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6*args.getD 2 0}

/-- All reported-edge reads and record writes are deterministic. -/
theorem refreshScanModule_noRand (b : ℕ) : ∀ body ∈ refreshScanModule b,body.NoRand := by
  intro body hb
  simp only [refreshScanModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [refreshScanBody,forRange,forUp,Stmt.NoRand]
  · have he : body=refreshRecordBody := by simpa [refreshRecordModule] using hb
    subst body
    exact refreshRecord_noRand

private theorem refresh_scan_loop {w a names k heap record : ℕ} (p : Program) (mem : ℕ → ℕ)
    (hw : 5 < 2^w) (hk : k < 2^w) (hspace : heap+6*k < 2^w) (hz : ZeroFrom mem heap)
    (hsource : ∀ i < k,names+i < heap ∧ mem (names+i) < 2^w ∧
      a+1+5*mem (names+i) < heap ∧ mem (a+5*mem (names+i)) < 2^w ∧
      mem (a+1+5*mem (names+i)) < 2^w)
    (hrecord : MeetsContract w p record (refreshRecordContract w)) :
    Triple w p
      (fun st => st.regs 0=a ∧ st.regs 1=names ∧ st.regs 2=k ∧ st.regs 3=heap ∧
        st.regs 5=heap ∧ st.mem=mem)
      (forRange 4 (.const 0) (.reg 2)
        (.assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 6)))) ;;
         .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 6)))) ;;
         .call 5 record [.reg 6,.reg 7,.reg 8,.reg 5]))
      (normalPost fun st => st.regs 5=heap+6*k ∧ ListAt st.mem heap (refreshScanWords mem a names k) ∧
        (∀ x < heap,st.mem x=mem x) ∧ ZeroFrom st.mem (heap+6*k))
      (fun _ => 180*k+100) := by
  have hl := Triple.forRange_const (w:=w) (p:=p) (r:=4) (lo:=.const 0) (hi:=.reg 2)
    (body:=.assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
      .assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 6)))) ;;
      .assign 8 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 6)))) ;;
      .call 5 record [.reg 6,.reg 7,.reg 8,.reg 5])
    (P:=fun st => st.regs 0=a ∧ st.regs 1=names ∧ st.regs 2=k ∧ st.regs 3=heap ∧
      st.regs 5=heap ∧ st.mem=mem)
    (Inv:=fun i st => st.regs 0=a ∧ st.regs 1=names ∧ st.regs 2=k ∧ st.regs 3=heap ∧
      st.regs 4=i ∧ st.regs 5=heap+6*i ∧ ListAt st.mem heap (refreshScanWords mem a names i) ∧
      (∀ x < heap,st.mem x=mem x) ∧ ZeroFrom st.mem (heap+6*i))
    140 0 k (Nat.zero_le k) (by omega) (fun _ => hk)
    (fun st hh => by
      obtain ⟨h0,h1,h2,h3,h5,hm⟩ := hh
      refine ⟨by eval_expr,?_⟩
      simpa [hm,refreshScanWords] using And.intro h0
        (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h5 hz)))))
    (fun _ _ _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω hst
      obtain ⟨h0,h1,h2,h3,h4,h5,hprefix,hframe,hfresh⟩ := hst
      obtain ⟨hnameAddr,hnameWord,hend,htailWord,hheadWord⟩ := hsource i hi
      have hnameRead : st.mem (names+i)=mem (names+i) := hframe _ hnameAddr
      have htailRead : st.mem (a+5*mem (names+i))=mem (a+5*mem (names+i)) := hframe _ (by omega)
      have hheadRead : st.mem (a+1+5*mem (names+i))=mem (a+1+5*mem (names+i)) := hframe _ hend
      have hnameAddrWord : names+i < 2^w := by omega
      have htailAddr : a+5*mem (names+i) < 2^w := by omega
      have hheadAddr : a+1+5*mem (names+i) < 2^w := by omega
      have hmul : 5*mem (names+i) < 2^w := by omega
      have hheap : heap+6*i < 2^w := by omega
      have hnext : heap+6*i+6 < 2^w := by omega
      apply runs_start_le
      refine runs_seq_assign_le (v:=mem (names+i)) (by eval_expr) ?_
      refine runs_seq_assign_le (v:=mem (a+5*mem (names+i))) (by eval_expr) ?_
      refine runs_seq_assign_le (v:=mem (a+1+5*mem (names+i))) (by eval_expr) ?_
      refine runs_call_le hrecord
        (vs:=[mem (names+i),mem (a+5*mem (names+i)),mem (a+1+5*mem (names+i)),heap+6*i])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,rfl⟩,hfresh,hnext⟩
      · intro v mem1 pos1 hp1
        obtain ⟨⟨_,_,hkeep,hzero1,hrec⟩,hv⟩ := hp1
        change v=heap+6*i+6 at hv
        change ∀ x < heap+6*i,mem1 x=st.mem x at hkeep
        change ListAt mem1 (heap+6*i)
          [1,mem (names+i),0,mem (names+i),mem (a+5*mem (names+i)),mem (a+1+5*mem (names+i))] at hrec
        have hp' : ListAt mem1 heap (refreshScanWords mem a names i) :=
          hprefix.of_agree_below (by rw [refreshScanWords_length]) hkeep
        have hcombined : ListAt mem1 heap (refreshScanWords mem a names (i+1)) := by
          rw [refreshScanWords_succ,listAt_append]
          exact ⟨hp',by simpa only [refreshScanWords_length] using hrec⟩
        have hv' : v=heap+6*(i+1) := by omega
        constructor
        · change (_ ∧ _) ∧ _
          refine ⟨⟨?_,?_,?_,?_,?_,?_,hcombined,?_,?_⟩,h4⟩
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simpa using h3
          · simp
          · simpa using hv'
          · intro x hx
            exact (hkeep x (by omega)).trans (hframe x hx)
          · simpa only [hv'] using hzero1
        · simp only [refreshRecordContract,heapContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega)
  refine hl.conseq (fun _ hh => hh) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => obtain ⟨_,_,_,_,_,h5,hp,hf,hz⟩ := ho; exact ⟨h5,hp,hf,hz⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The machine serializes exactly the reported list in linear time,
preserving all earlier allocations and returning the exact output end. -/
theorem refreshScan_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (refreshScanModule b)) : MeetsContract w p b (refreshScanContract w) := by
  have hrecord : p.HasAt (b+1) refreshRecordModule := Num.hasAt_append_right hp
  have hspec := refreshRecord_meetsContract (w:=w) hrecord
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,names,k,heap,rfl,hsource⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+6*k < 2^w at hspace
  have hk : k < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold refreshScanBody
  wram_step
  refine runs_seq_triple_le (refresh_scan_loop p mem hw hk hspace hz hsource hspec)
    (by simp [startState]) ?_
  intro st ⟨h5,hprefix,hframe,hfresh⟩
  refine runs_ret_le (v:=heap+6*k) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+6*k ∧ heap+6*k ≤ heap+6*k ∧ (∀ x < heap,st.mem x=mem x) ∧
      ZeroFrom st.mem (heap+6*k) ∧ ListAt st.mem heap (refreshScanWords mem a names k)) ∧ heap+6*k=heap+6*k
    exact ⟨⟨by omega,le_rfl,hframe,hfresh,hprefix⟩,rfl⟩
  · simp only [refreshScanContract,heapContract,Expr.size_reg,List.getD_cons_zero,List.getD_cons_succ]
    omega

end MinCostFlow.IPM.Machine
