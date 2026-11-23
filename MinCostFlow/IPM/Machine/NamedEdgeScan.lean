module

public import MinCostFlow.IPM.Machine.NamedEdgeRecord
public import WordRAM.Logic
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Serializing the fixed graph's named edges

The source endpoint fields are five words apart. Read both endpoints,
keep the original edge index as its name, and append the three-word
min-ratio record. The proof tracks the exact written prefix and charges
every read, record call and loop iteration.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The endpoint scan's exact output words. -/
def edgeTripleWords (mem : ℕ → ℕ) (a m : ℕ) : List ℕ :=
  (List.range m).flatMap (fun i => [i,mem (a+5*i),mem (a+1+5*i)])

private theorem edgeTripleWords_length (mem : ℕ → ℕ) (a m : ℕ) :
    (edgeTripleWords mem a m).length=3*m := by
  simp [edgeTripleWords,List.length_flatMap]
  omega

private theorem edgeTripleWords_succ (mem : ℕ → ℕ) (a i : ℕ) :
    edgeTripleWords mem a (i+1)=edgeTripleWords mem a i++[i,mem (a+5*i),mem (a+1+5*i)] := by
  simp [edgeTripleWords,List.range_succ,List.flatMap_append]

/-- Arguments `[tailAddress,m,heap]`. Heads follow each tail word. -/
def namedEdgeScanBody (record : ℕ) : Stmt :=
  .assign 4 (.reg 2) ;;
  forRange 3 (.const 0) (.reg 1)
    (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3)))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 3)))) ;;
     .call 4 record [.reg 3,.reg 5,.reg 6,.reg 4]) ;;
  .ret (.reg 4)

/-- Endpoint scan followed by the three-word writer. -/
def namedEdgeScanModule (b : ℕ) : List Stmt :=
  [namedEdgeScanBody (b+1)] ++ namedEdgeRecordModule

/-- Exactly three output words per edge, preserving the entire source. -/
def namedEdgeScanContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a m heap,args=[a,m,heap] ∧
      ∀ i < m,a+1+5*i < heap ∧ mem (a+5*i) < 2^w ∧ mem (a+1+5*i) < 2^w)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (edgeTripleWords mem (args.getD 0 0) (args.getD 1 0)))
    (fun args _ => 100*args.getD 1 0+100) (fun args _ => 3*args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+3*args.getD 1 0}

/-- Endpoint reads and record writes are deterministic. -/
theorem namedEdgeScanModule_noRand (b : ℕ) :
    ∀ body ∈ namedEdgeScanModule b,body.NoRand := by
  intro body hb
  simp only [namedEdgeScanModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [namedEdgeScanBody,forRange,forUp,Stmt.NoRand]
  · have he : body=namedEdgeRecordBody := by simpa [namedEdgeRecordModule] using hb
    subst body
    exact namedEdgeRecord_noRand

private theorem edge_scan_loop {w a m heap record : ℕ} (p : Program) (mem : ℕ → ℕ)
    (hw : 5 < 2^w) (hm : m < 2^w) (hspace : heap+3*m < 2^w) (hzero : ZeroFrom mem heap)
    (hsource : ∀ i < m,a+1+5*i < heap ∧ mem (a+5*i) < 2^w ∧ mem (a+1+5*i) < 2^w)
    (hrecord : MeetsContract w p record (namedEdgeRecordContract w)) :
    Triple w p
      (fun st => st.regs 0=a ∧ st.regs 1=m ∧ st.regs 2=heap ∧ st.regs 4=heap ∧ st.mem=mem)
      (forRange 3 (.const 0) (.reg 1)
        (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3)))) ;;
         .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 3)))) ;;
         .call 4 record [.reg 3,.reg 5,.reg 6,.reg 4]))
      (normalPost fun st => st.regs 4=heap+3*m ∧ ListAt st.mem heap (edgeTripleWords mem a m) ∧
        (∀ x < heap,st.mem x=mem x) ∧ ZeroFrom st.mem (heap+3*m))
      (fun _ => 100*m+50) := by
  have hl := Triple.forRange_const (w:=w) (p:=p) (r:=3) (lo:=.const 0) (hi:=.reg 1)
    (body:=.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 3)))) ;;
      .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.bin .mul (.const 5) (.reg 3)))) ;;
      .call 4 record [.reg 3,.reg 5,.reg 6,.reg 4])
    (P:=fun st => st.regs 0=a ∧ st.regs 1=m ∧ st.regs 2=heap ∧ st.regs 4=heap ∧ st.mem=mem)
    (Inv:=fun i st => st.regs 0=a ∧ st.regs 1=m ∧ st.regs 2=heap ∧ st.regs 3=i ∧
      st.regs 4=heap+3*i ∧ ListAt st.mem heap (edgeTripleWords mem a i) ∧
      (∀ x < heap,st.mem x=mem x) ∧ ZeroFrom st.mem (heap+3*i))
    70 0 m (Nat.zero_le m) (by omega) (fun _ => hm)
    (fun st hh => by
      obtain ⟨h0,h1,h2,h4,hmem⟩ := hh
      refine ⟨by eval_expr,?_⟩
      simpa [hmem,edgeTripleWords] using And.intro h0
        (And.intro h1 (And.intro h2 (And.intro h4 hzero))))
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω hst
      obtain ⟨h0,h1,h2,h3,h4,hprefix,hframe,hfresh⟩ := hst
      obtain ⟨hbefore,htail, hhead⟩ := hsource i hi
      have htailRead : st.mem (a+5*i)=mem (a+5*i) := hframe _ (by omega)
      have hheadRead : st.mem (a+1+5*i)=mem (a+1+5*i) := hframe _ hbefore
      have haddrTail : a+5*i < 2^w := by omega
      have haddrHead : a+1+5*i < 2^w := by omega
      have hmul : 5*i < 2^w := by omega
      have hheap : heap+3*i < 2^w := by omega
      have hnextSpace : heap+3*i+3 < 2^w := by omega
      have hiword : i < 2^w := hi.trans hm
      apply runs_start_le
      refine runs_seq_assign_le (v:=mem (a+5*i)) (by eval_expr) ?_
      refine runs_seq_assign_le (v:=mem (a+1+5*i)) (by eval_expr) ?_
      refine runs_call_le hrecord (vs:=[i,mem (a+5*i),mem (a+1+5*i),heap+3*i])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,rfl⟩,hfresh,hnextSpace⟩
      · intro v mem1 pos1 hp1
        obtain ⟨⟨hlo,hhi,hkeep,hzero1,hrec⟩,hv⟩ := hp1
        change v=heap+3*i+3 at hv
        change ∀ x < heap+3*i,mem1 x=st.mem x at hkeep
        change ListAt mem1 (heap+3*i) [i,mem (a+5*i),mem (a+1+5*i)] at hrec
        have hprefix' : ListAt mem1 heap (edgeTripleWords mem a i) :=
          hprefix.of_agree_below (by rw [edgeTripleWords_length]) hkeep
        have hcombined : ListAt mem1 heap (edgeTripleWords mem a (i+1)) := by
          rw [edgeTripleWords_succ,listAt_append]
          exact ⟨hprefix',by simpa only [edgeTripleWords_length] using hrec⟩
        have hv' : v=heap+3*(i+1) := by omega
        constructor
        · change (_ ∧ _) ∧ _
          refine ⟨⟨?_,?_,?_,?_,?_,hcombined,?_,?_⟩,h3⟩
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simp
          · simpa using hv'
          · intro x hx
            exact (hkeep x (by omega)).trans (hframe x hx)
          · simpa only [hv'] using hzero1
        · simp only [namedEdgeRecordContract,heapContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega)
  refine hl.conseq (fun _ hh => hh) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => obtain ⟨_,_,_,_,h4,hp,hf,hz⟩ := ho; exact ⟨h4,hp,hf,hz⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The endpoint scan writes precisely the canonical named-edge list in
linear time, preserving its source and all previous allocations. -/
theorem namedEdgeScan_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (namedEdgeScanModule b)) : MeetsContract w p b (namedEdgeScanContract w) := by
  have hrecord : p.HasAt (b+1) namedEdgeRecordModule := Num.hasAt_append_right hp
  have hrecordSpec := namedEdgeRecord_meetsContract (w:=w) hrecord
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,m,heap,rfl,hsource⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+3*m < 2^w at hspace
  have hm : m < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold namedEdgeScanBody
  wram_step
  refine runs_seq_triple_le (edge_scan_loop p mem hw hm hspace hzero hsource hrecordSpec)
    (by simp [startState]) ?_
  intro st ⟨h4,hprefix,hframe,hfresh⟩
  refine runs_ret_le (v:=heap+3*m) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+3*m ∧ heap+3*m ≤ heap+3*m ∧ (∀ x < heap,st.mem x=mem x) ∧
      ZeroFrom st.mem (heap+3*m) ∧ ListAt st.mem heap (edgeTripleWords mem a m)) ∧ heap+3*m=heap+3*m
    exact ⟨⟨by omega,le_rfl,hframe,hfresh,hprefix⟩,rfl⟩
  · simp only [namedEdgeScanContract,heapContract,Expr.size_reg,
      List.getD_cons_zero,List.getD_cons_succ]
    omega

end MinCostFlow.IPM.Machine
