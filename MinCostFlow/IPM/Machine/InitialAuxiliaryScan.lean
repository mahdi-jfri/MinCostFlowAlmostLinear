module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryPrefix
public import WordRAM.Logic
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Emitting all auxiliary edges in increasing vertex order

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) adds an auxiliary edge at precisely the vertices
with nonzero midpoint deficit. This entry reads the two verified
endpoint tables and invokes the exact one-vertex selector. Its output
is their increasing-order record concatenation. Empty records consume
no space, while five words per vertex bound the total allocation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[incoming,outgoing,n,penalty,heap]`. -/
def initialAuxiliaryScanBody (emit : ℕ) : Stmt :=
  .assign 6 (.reg 4) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .call 6 emit [.reg 5,.reg 2,.reg 7,.reg 8,.reg 3,.reg 6]) ;;
  .ret (.reg 6)

/-- Scan entry, selector and its record writer. -/
def initialAuxiliaryScanModule (b : ℕ) : List Stmt :=
  [initialAuxiliaryScanBody (b+1)] ++ initialAuxiliaryEdgeModule (b+1)

/-- The scan emits the exact record emitted using at most `5n` words and
`250n+100` operations. Input tables remain unchanged. -/
def initialAuxiliaryScanContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a c n penalty heap, args = [a,c,n,penalty,heap] ∧
      ∀ i < n, a+i < heap ∧ c+i < heap ∧ mem (a+i) < 2^w ∧ mem (c+i) < 2^w)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (initialAuxiliaryPrefix (fun i => mem (args.getD 0 0+i))
        (fun i => mem (args.getD 1 0+i)) (args.getD 2 0) (args.getD 3 0) (args.getD 2 0)))
    (fun args _ => 250*args.getD 2 0+100) (fun args _ => 5*args.getD 2 0)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+(initialAuxiliaryPrefix (fun i => mem (args.getD 0 0+i))
        (fun i => mem (args.getD 1 0+i)) (args.getD 2 0) (args.getD 3 0) (args.getD 2 0)).length }

/-- The emitted graph is computed without randomness. -/
theorem initialAuxiliaryScanModule_noRand (b : ℕ) :
    ∀ body ∈ initialAuxiliaryScanModule b, body.NoRand := by
  intro body hb
  simp only [initialAuxiliaryScanModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [initialAuxiliaryScanBody,forRange,forUp,Stmt.NoRand]
  · exact initialAuxiliaryEdgeModule_noRand _ body hb

private theorem auxiliary_loop {w a c n penalty heap emit : ℕ} (p : Program)
    (mem : ℕ → ℕ) (hw : 5 < 2^w) (hn : n < 2^w) (hk : penalty < 2^w)
    (hspace : heap+5*n < 2^w) (hzero : ZeroFrom mem heap)
    (hsource : ∀ i < n, a+i < heap ∧ c+i < heap ∧ mem (a+i) < 2^w ∧ mem (c+i) < 2^w)
    (hemit : MeetsContract w p emit (initialAuxiliaryEdgeContract w)) :
    let incoming := fun i => mem (a+i)
    let outgoing := fun i => mem (c+i)
    let emitted := initialAuxiliaryPrefix incoming outgoing n penalty
    Triple w p
      (fun st => st.regs 0 = a ∧ st.regs 1 = c ∧ st.regs 2 = n ∧ st.regs 3 = penalty ∧
        st.regs 4 = heap ∧ st.regs 6 = heap ∧ st.mem = mem)
      (forRange 5 (.const 0) (.reg 2)
        (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))) ;;
         .assign 8 (.load (.bin .add (.reg 1) (.reg 5))) ;;
         .call 6 emit [.reg 5,.reg 2,.reg 7,.reg 8,.reg 3,.reg 6]))
      (normalPost fun st => st.regs 6 = heap+(emitted n).length ∧ ListAt st.mem heap (emitted n) ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+(emitted n).length))
      (fun _ => 250*n+50) := by
  dsimp only
  let incoming := fun i => mem (a+i)
  let outgoing := fun i => mem (c+i)
  let emitted := initialAuxiliaryPrefix incoming outgoing n penalty
  have hl := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .assign 7 (.load (.bin .add (.reg 0) (.reg 5))) ;;
      .assign 8 (.load (.bin .add (.reg 1) (.reg 5))) ;;
      .call 6 emit [.reg 5,.reg 2,.reg 7,.reg 8,.reg 3,.reg 6])
    (P := fun st => st.regs 0 = a ∧ st.regs 1 = c ∧ st.regs 2 = n ∧ st.regs 3 = penalty ∧
      st.regs 4 = heap ∧ st.regs 6 = heap ∧ st.mem = mem)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = c ∧ st.regs 2 = n ∧ st.regs 3 = penalty ∧
      st.regs 4 = heap ∧ st.regs 5 = i ∧ st.regs 6 = heap+(emitted i).length ∧
      ListAt st.mem heap (emitted i) ∧ (∀ x < heap, st.mem x = mem x) ∧
      ZeroFrom st.mem (heap+(emitted i).length))
    200 0 n (Nat.zero_le n) (by omega) (fun _ => hn)
    (fun st hh => by
      obtain ⟨h0,h1,h2,h3,h4,h6,hmem⟩ := hh
      refine ⟨by eval_expr,?_⟩
      simpa [emitted,initialAuxiliaryPrefix,ListAt,hmem] using
        And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
          (And.intro h4 (And.intro h6 hzero))))))
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st omegaBits hst
      obtain ⟨h0,h1,h2,h3,h4,h5,h6,hprefix,hframe,hfresh⟩ := hst
      obtain ⟨ha,hc,hinc,hout⟩ := hsource i hi
      have hra : st.mem (a+i) = incoming i := hframe _ ha
      have hrc : st.mem (c+i) = outgoing i := hframe _ hc
      have hlen := initialAuxiliaryPrefix_length_le incoming outgoing n penalty i
      change (emitted i).length ≤ 5*i at hlen
      have hincword : incoming i < 2^w := hinc
      have houtword : outgoing i < 2^w := hout
      have hfit : heap+(emitted i).length+5 < 2^w := by omega
      have hptr : heap+(emitted i).length < 2^w := by omega
      have hiw : i < 2^w := hi.trans hn
      apply runs_start_le
      refine runs_seq_assign_le (v := incoming i) (by eval_expr) ?_
      refine runs_seq_assign_le (v := outgoing i) (by eval_expr) ?_
      refine runs_call_le hemit
        (vs := [i,n,incoming i,outgoing i,penalty,heap+(emitted i).length])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,_,rfl,hi⟩,hfresh,hfit⟩
      · intro value mem' pos' hpost
        obtain ⟨⟨hlo,hhi,hpreserve,hnewzero,hrecord⟩,hvalue⟩ := hpost
        change value = heap+(emitted i).length+
          (initialAuxiliaryWords i n (incoming i) (outgoing i) penalty).length at hvalue
        have hnext : value = heap+(emitted (i+1)).length := by
          simpa only [emitted,initialAuxiliaryPrefix,List.length_append,Nat.add_assoc] using hvalue
        have hprefix' : ListAt mem' heap (emitted (i+1)) := by
          apply listAt_append.mpr
          constructor
          · intro j hj
            change j < (emitted i).length at hj
            exact (hpreserve _ (by change heap+j < heap+(emitted i).length; omega)).trans (hprefix j hj)
          · exact hrecord
        constructor
        · change (_ ∧ _) ∧ _
          refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,hprefix',?_,?_⟩,h5⟩
          · simpa using h0
          · simpa using h1
          · simpa using h2
          · simpa using h3
          · simpa using h4
          · simp
          · simpa using hnext
          · intro x hx
            exact (hpreserve _ (by change x < heap+(emitted i).length; omega)).trans (hframe x hx)
          · simpa only [hnext] using hnewzero
        · simp only [initialAuxiliaryEdgeContract,heapContract,Expr.size_bin,Expr.size_load,
            Expr.size_reg,argsSize_cons,argsSize_nil]
          omega)
  refine hl.conseq (fun _ hh => hh) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal =>
      obtain ⟨_,_,_,_,_,_,h6,hp,hf,hz⟩ := ho
      exact ⟨h6,hp,hf,hz⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The complete auxiliary scan agrees with its increasing-order output
model and satisfies a linear machine cost on every random tape. -/
theorem initialAuxiliaryScan_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialAuxiliaryScanModule b)) :
    MeetsContract w p b (initialAuxiliaryScanContract w) := by
  have hemit : p.HasAt (b+1) (initialAuxiliaryEdgeModule (b+1)) := Num.hasAt_append_right hp
  have hk := initialAuxiliaryEdge_meetsContract hw hemit
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,c,n,penalty,heap,rfl,hsource⟩,hzero,hspace⟩ := hpre
  change heap+5*n < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hn : n < 2^w := hwords _ (by simp)
  have hpenalty : penalty < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hloop := auxiliary_loop p mem hw hn hpenalty hspace hzero hsource hk
  apply runs_start_le
  unfold initialAuxiliaryScanBody
  refine runs_seq_assign_le (v := heap) (by eval_expr) ?_
  refine runs_seq_triple_le hloop (by simp [startState]) ?_
  intro st ⟨h6,hprefix,hframe,hfresh⟩
  have hlen := initialAuxiliaryPrefix_length_le (fun i => mem (a+i)) (fun i => mem (c+i)) n penalty n
  have hvword : heap+(initialAuxiliaryPrefix (fun i => mem (a+i))
      (fun i => mem (c+i)) n penalty n).length < 2^w := by omega
  refine runs_ret_le (by eval_expr) ?_ ?_
  · let records := initialAuxiliaryPrefix (fun i => mem (a+i)) (fun i => mem (c+i)) n penalty n
    change (heap ≤ heap+records.length ∧ heap+records.length ≤ heap+5*n ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+records.length) ∧
      ListAt st.mem heap records) ∧ heap+records.length = heap+records.length
    change records.length ≤ 5*n at hlen
    exact ⟨⟨by omega,by omega,hframe,hfresh,hprefix⟩,rfl⟩
  · simp only [initialAuxiliaryScanContract,heapContract,Expr.size_reg,List.getD_cons_zero,List.getD_cons_succ]
    omega

end MinCostFlow.IPM.Machine
