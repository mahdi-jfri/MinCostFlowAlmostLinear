module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryScan
public import MinCostFlow.IPM.Machine.InitialCapacities
public import WordRAM.CopyWords
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Assembling the augmented graph's encoded records

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) retains the original edges and appends the
auxiliary edges. This procedure copies the original five-word solver
records, invokes the verified auxiliary scan, and writes the new graph
header. Its postcondition describes every output word and the exact
returned heap. Identification with the indexed construction uses the
separate ordering lemmas; no optimum is an input to this assembly.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Header and records produced by the assembly, in original-edge order
followed by the increasing-vertex-order auxiliary records. -/
def initialAssemblyWords (J : Circulation) (incoming outgoing : ℕ → ℕ) (penalty : ℕ) : List ℕ :=
  let records := initialAuxiliaryPrefix incoming outgoing J.n penalty J.n
  [J.n+1,J.m+records.length/5] ++ J.solverWords.drop 2 ++ records

/-- Arguments `[input,incoming,outgoing,penalty,heap]`. -/
def initialRecordAssemblyBody (copy emit : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.bin .add (.reg 4) (.const 2)) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .mul (.const 5) (.reg 6))) ;;
  .call 9 copy [.bin .add (.reg 0) (.const 2),.reg 7,.bin .mul (.const 5) (.reg 6)] ;;
  .call 10 emit [.reg 1,.reg 2,.reg 5,.reg 3,.reg 8] ;;
  .store (.reg 4) (.bin .add (.reg 5) (.const 1)) ;;
  .store (.bin .add (.reg 4) (.const 1))
    (.bin .add (.reg 6) (.bin .div (.bin .sub (.reg 10) (.reg 8)) (.const 5))) ;;
  .ret (.reg 10)

/-- Entry, the library's word copier, and the auxiliary scan. -/
def initialRecordAssemblyModule (b : ℕ) : List Stmt :=
  [initialRecordAssemblyBody (b+1) (b+2),copyWords] ++ initialAuxiliaryScanModule (b+2)

/-- Exact record assembly. The two input tables must already be below
heap. Worst-case space is `2+5m+5n` and cost is `100m+300n+400`. -/
def initialRecordAssemblyContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a inc out penalty heap, args = [a,inc,out,penalty,heap] ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧
      ∀ i < J.n, inc+i < heap ∧ out+i < heap ∧ mem (inc+i) < 2^w ∧ mem (out+i) < 2^w)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (initialAssemblyWords J (fun i => mem (args.getD 1 0+i))
        (fun i => mem (args.getD 2 0+i)) (args.getD 3 0)))
    (fun _ _ => 100*J.m+300*J.n+400) (fun _ _ => 2+5*J.m+5*J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+2+5*J.m+
        (initialAuxiliaryPrefix (fun i => mem (args.getD 1 0+i))
          (fun i => mem (args.getD 2 0+i)) J.n (args.getD 3 0) J.n).length }

/-- Every procedure in the record assembly is deterministic. -/
theorem initialRecordAssemblyModule_noRand (b : ℕ) :
    ∀ body ∈ initialRecordAssemblyModule b, body.NoRand := by
  intro body hb
  simp only [initialRecordAssemblyModule,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with (rfl | rfl) | hb
  · simp [initialRecordAssemblyBody,Stmt.NoRand]
  · simp [copyWords,forRange,forUp,Stmt.NoRand]
  · exact initialAuxiliaryScanModule_noRand _ body hb

/-- Exact machine record assembly, with full memory framing, no random
instructions, and linear cost in the original vertices and edges. -/
theorem initialRecordAssembly_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialRecordAssemblyModule b)) (J : Circulation) :
    MeetsContract w p b (initialRecordAssemblyContract w J) := by
  have hfirst : p.HasAt b [initialRecordAssemblyBody (b+1) (b+2),copyWords] :=
    Num.hasAt_append_left hp
  have hcopyplace : p.HasAt (b+1) [copyWords] := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa using hfirst 1 (by simp)
  have hemit : p.HasAt (b+2) (initialAuxiliaryScanModule (b+2)) := Num.hasAt_append_right hp
  have hcopy := copyWords_meetsContract (w := w) hcopyplace
  have hemitSpec := initialAuxiliaryScan_meetsContract hw hemit
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,inc,out,penalty,heap,rfl,hat,hend,hinput,htables⟩,hzero,hspace⟩ := hpre
  change heap+(2+5*J.m+5*J.n) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  let records := initialAuxiliaryPrefix (fun i => mem (inc+i)) (fun i => mem (out+i)) J.n penalty J.n
  have hlen : records.length ≤ 5*J.n := initialAuxiliaryPrefix_length_le _ _ _ _ _
  have hlength := J.solverWords_length
  have hheader := (Scaling.Machine.solverWords_at_iff J mem a).mp hat
  have hN := hheader.1
  have hM := hheader.2.1
  have hnw : J.n < 2^w := hinput _ List.mem_cons_self
  have hmw : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hincw : inc < 2^w := hwords _ (by simp)
  have houtw : out < 2^w := hwords _ (by simp)
  have hkw : penalty < 2^w := hwords _ (by simp)
  have hheapw : heap < 2^w := hwords _ (by simp)
  have ha1 : a+1 < 2^w := by omega
  have ha2 : a+2 < 2^w := by omega
  have hd : heap+2 < 2^w := by omega
  have hmul : 5*J.m < 2^w := by omega
  have haux : heap+2+5*J.m < 2^w := by omega
  have hnplus : J.n+1 < 2^w := by omega
  apply runs_start_le
  unfold initialRecordAssemblyBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+2) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+2+5*J.m) (by eval_expr) ?_
  refine runs_seq_call_le hcopy (vs := [a+2,heap+2,5*J.m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨_,_,_,rfl,by omega,by omega,by omega,Or.inr (by omega)⟩
  · intro ignored mem1 pos1 hc
    obtain ⟨src,dst,len,heq,_,hcopied,hframe1⟩ := hc
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    change ∀ i < 5*J.m, mem1 (heap+2+i) = mem (a+2+i) at hcopied
    change ∀ x, x < heap+2 ∨ heap+2+5*J.m ≤ x → mem1 x = mem x at hframe1
    have hrowlen : (J.solverWords.drop 2).length = 5*J.m := by
      rw [List.length_drop,hlength]
      omega
    have hrows : ListAt mem1 (heap+2) (J.solverWords.drop 2) :=
      copyWords_listAt (hat.drop 2) hrowlen hcopied
    have hkeep : ∀ x < heap+2, mem1 x = mem x := fun x hx => hframe1 x (Or.inl hx)
    have hzero1 : ZeroFrom mem1 (heap+2+5*J.m) := by
      intro x hx
      exact (hframe1 x (Or.inr hx)).trans (hzero x (by omega))
    have hsource1 : ∀ i < J.n,
        inc+i < heap+2+5*J.m ∧ out+i < heap+2+5*J.m ∧
        mem1 (inc+i) < 2^w ∧ mem1 (out+i) < 2^w := by
      intro i hi
      obtain ⟨hib,hob,hiv,hov⟩ := htables i hi
      exact ⟨by omega,by omega,by simpa only [hkeep (inc+i) (by omega)] using hiv,
        by simpa only [hkeep (out+i) (by omega)] using hov⟩
    have hrecords : initialAuxiliaryPrefix (fun i => mem1 (inc+i)) (fun i => mem1 (out+i))
        J.n penalty J.n = records := by
      apply initialAuxiliaryPrefix_congr
      · intro i hi; exact hkeep _ (by have hh := (htables i hi).1; omega)
      · intro i hi; exact hkeep _ (by have hh := (htables i hi).2.1; omega)
    refine runs_seq_call_le hemitSpec (vs := [inc,out,J.n,penalty,heap+2+5*J.m])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,_,rfl,hsource1⟩,hzero1,
        by change heap+2+5*J.m+5*J.n < 2^w; omega⟩
    · intro value mem2 pos2 hp2
      obtain ⟨⟨hlo,hhi,hframe2,hzero2,hrecordAt⟩,hv⟩ := hp2
      change value = heap+2+5*J.m+(initialAuxiliaryPrefix
        (fun i => mem1 (inc+i)) (fun i => mem1 (out+i)) J.n penalty J.n).length at hv
      rw [hrecords] at hv
      change ListAt mem2 (heap+2+5*J.m) (initialAuxiliaryPrefix
        (fun i => mem1 (inc+i)) (fun i => mem1 (out+i)) J.n penalty J.n) at hrecordAt
      rw [hrecords] at hrecordAt
      change ∀ x < heap+2+5*J.m, mem2 x = mem1 x at hframe2
      have hvw : value < 2^w := by omega
      have hcountw : J.m+(value-(heap+2+5*J.m))/5 < 2^w := by omega
      have hcount : J.m+(value-(heap+2+5*J.m))/5 = J.m+records.length/5 := by omega
      have hbodyAt : ListAt mem2 (heap+2) (J.solverWords.drop 2 ++ records) := by
        apply listAt_append.mpr
        constructor
        · intro i hi
          exact (hframe2 _ (by rw [hrowlen] at hi; omega)).trans (hrows i hi)
        · simpa only [hrowlen] using hrecordAt
      wram_step
      wram_step
      refine runs_ret_le (v := value) (by eval_expr) ?_ ?_
      · let resultMem := Function.update (Function.update mem2 heap (J.n+1))
          (heap+1) (J.m+(value-(heap+2+5*J.m))/5)
        change (heap ≤ value ∧ value ≤ heap+(2+5*J.m+5*J.n) ∧
          (∀ x < heap, resultMem x = mem x) ∧ ZeroFrom resultMem value ∧
          ListAt resultMem heap (initialAssemblyWords J (fun i => mem (inc+i))
            (fun i => mem (out+i)) penalty)) ∧ value = heap+2+5*J.m+records.length
        refine ⟨⟨by omega,by omega,?_,?_,?_⟩,hv⟩
        · intro x hx
          dsimp only [resultMem]
          rw [Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
          exact (hframe2 _ (by omega)).trans (hkeep _ (by omega))
        · intro x hx
          dsimp only [resultMem]
          rw [Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
          exact hzero2 x hx
        · change ListAt resultMem heap ([J.n+1,J.m+records.length/5] ++ (J.solverWords.drop 2 ++ records))
          apply listAt_append.mpr
          constructor
          · intro i hi
            have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
            rcases he with rfl | rfl <;> simp [resultMem,hcount]
          · intro i hi
            dsimp only [resultMem]
            rw [Function.update_of_ne (by change heap+2+i ≠ heap+1; omega),
              Function.update_of_ne (by change heap+2+i ≠ heap; omega)]
            exact hbodyAt i hi
      · simp only [initialRecordAssemblyContract,initialAuxiliaryScanContract,copyWordsContract,
          heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil,
          List.getD_cons_zero,List.getD_cons_succ]
        omega

end MinCostFlow.IPM.Machine
