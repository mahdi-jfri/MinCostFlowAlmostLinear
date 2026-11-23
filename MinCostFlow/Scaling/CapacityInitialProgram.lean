module

public import MinCostFlow.Scaling.CapacityStateLayout
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Initializing the capacity-scaling state

The fresh heap supplies the initial zero flow array. Reserve its `m`
cells and write a two-word header containing its pointer and a false
stop flag. This is exactly the capacity model's initial state and leaves
a fresh zero tail for the subsequent iterations.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`; return the heap after the initial state header. -/
def capacityInitialBody (pair : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 pair [.reg 1,.const 0,.bin .add (.reg 1) (.reg 2)] ;;
  .ret (.reg 3)

/-- Initialization entry followed by the shared two-word writer. -/
def capacityInitialModule (b : ℕ) : List Stmt := capacityInitialBody (b+1) :: wordPairModule

/-- The initial flow array and final two-word capacity-state header. -/
def capacityInitialContract (w : ℕ) (J : Circulation) : Contract where
  pre args mem := ∃ a heap,args=[a,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤heap ∧ ZeroFrom mem heap ∧ heap+J.m+2<2^w ∧ 2<2^w
  post args mem ret mem' := ret=heapArg args+J.m+2 ∧
    CapacityStateAt mem' (ret-2) ret (CapacityState.initial J) ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 60

/-- Initializing the zero state uses no random instruction. -/
theorem capacityInitialModule_noRand (b : ℕ) : ∀ body ∈ capacityInitialModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityInitialBody,Stmt.NoRand,and_self]
  · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hb
    subst body
    exact wordPairBody_noRand

/-- Initialization constructs the exact model state with `m+2` reserved
cells, cost 60, and the full old-memory frame. -/
theorem capacityInitial_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityInitialModule b)) (J : Circulation) :
    MeetsContract w p b (capacityInitialContract w J) := by
  have hk := wordPair_meetsContract (w := w) (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hzero,hspace,hw⟩ := hpre
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := by omega
  have hheader : heap+J.m<2^w := by omega
  have hM := (solver_header_at J hgraph).2
  have hflow : ListAt mem heap (List.ofFn (fun _ : Fin J.m => (0 : ℕ))) := by
    intro i hi
    change mem (heap+i)=(List.ofFn (fun _ : Fin J.m => (0 : ℕ)))[i]
    rw [hzero _ (by omega),List.getElem_ofFn]
  apply runs_start_le
  unfold capacityInitialBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [heap,0,heap+J.m]) (by eval_expr) (by wram_words)
    ⟨⟨heap,0,heap+J.m,rfl⟩,(by change ZeroFrom mem (heap+J.m); exact hzero.mono (by omega)),hspace⟩ ?_
  intro ret memP posP hpostP
  obtain ⟨⟨_,_,hframe,hz,hpair⟩,hret⟩ := hpostP
  change ret=heap+J.m+2 at hret
  change ListAt memP (heap+J.m) [heap,0] at hpair
  change ZeroFrom memP ret at hz
  change (∀ x<heap+J.m,memP x=mem x) at hframe
  have hflowP := hflow.of_agree_below (h₀ := heap+J.m) (by simp only [List.length_ofFn]; omega) hframe
  have hstart : ret-2=heap+J.m := by omega
  have hstate : CapacityStateAt memP (ret-2) ret (CapacityState.initial J) := by
    rw [hstart]
    apply capacityStateAt_of_array hpair (by omega)
    · simpa only [CapacityState.initial,Int.toNat_zero] using hflowP
    · intro e
      exact le_rfl
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change ret=heap+J.m+2 ∧ CapacityStateAt memP (ret-2) ret (CapacityState.initial J) ∧
      ZeroFrom memP ret ∧ ∀ x<heap,memP x=mem x
    exact ⟨hret,hstate,hz,fun x hx => hframe x (by omega)⟩
  · simp only [capacityInitialContract,wordPairContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

/-- Canonical source memory meets all initializer premises jointly at
word-size multiplier two. -/
theorem capacityInitial_pre_wordSize (J : Circulation) :
    (∀ x ∈ [0,J.solverWords.length],x<2^wordSize 2 J.solverWords) ∧
      (capacityInitialContract (wordSize 2 J.solverWords) J).pre
        [0,J.solverWords.length] (initMem J.solverWords) := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hB : 4+5*J.m≤B := by dsimp only [B]; omega
  have hspace : J.solverWords.length+J.m+2≤2*B := by dsimp only [B]; omega
  have hB2 : 2*B≤B^2 := by simpa only [pow_two] using Nat.mul_le_mul_right B (show 2≤B by omega)
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤2) J.solverWords
  change B^2<2^wordSize 2 J.solverWords at hp
  have hs := (hspace.trans hB2).trans_lt hp
  refine ⟨?_,0,J.solverWords.length,rfl,listAt_initMem _,by omega,zeroFrom_initMem _,hs,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
