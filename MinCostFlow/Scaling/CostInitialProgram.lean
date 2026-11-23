module

public import MinCostFlow.Scaling.CostStateLayout
public import MinCostFlow.Scaling.CostHeaderProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Initializing the integer cost-scaling state

The fresh heap already contains the initial zero flow and zero signed
potential pairs. Reserve these arrays, then write a header with their
pointers and denominator power one. This constructs exactly the model's
initial state without scanning zero-filled storage.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`. -/
def costInitialBody (header : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 1) (.reg 3)) ;;
  .assign 5 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 2))) ;;
  .call 6 header [.reg 1,.reg 4,.const 1,.reg 5] ;;
  .ret (.reg 6)

/-- Initial array reservation followed by the three-word header writer. -/
def costInitialModule (b : ℕ) : List Stmt := costInitialBody (b+1) :: costHeaderModule

/-- The exact initial model state, with `m+2*n+3` fresh words. -/
def costInitialContract (w : ℕ) (J : Circulation) : Contract where
  pre args mem := ∃ a heap,args=[a,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤heap ∧ ZeroFrom mem heap ∧ heap+J.m+2*J.n+3<2^w
  post args mem ret mem' := ret=heapArg args+J.m+2*J.n+3 ∧
    CostStateAt mem' (ret-3) ret (CostState.initial J) ∧ ZeroFrom mem' ret ∧
    ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 100

/-- Cost-state initialization uses no random instruction. -/
theorem costInitialModule_noRand (b : ℕ) : ∀ body ∈ costInitialModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costInitialBody,Stmt.NoRand,and_self]
  · have heq : body=costHeaderBody := List.mem_singleton.mp hb
    subst body
    exact costHeaderBody_noRand

/-- Initialization returns the model's exact zero flow, zero potential,
and power-one state, with constant cost and the full source frame. -/
theorem costInitial_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costInitialModule b)) (J : Circulation) :
    MeetsContract w p b (costInitialContract w J) := by
  have hk := costHeader_meetsContract (w := w) (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hz,hs⟩ := hpre
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by omega
  have hpot : heap+J.m<2^w := by omega
  have htwon : 2*J.n<2^w := by omega
  have hheader : heap+J.m+2*J.n<2^w := by omega
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hflow : ListAt mem heap (List.ofFn (fun _ : Fin J.m => (0 : ℕ))) := by
    intro i hi
    rw [hz _ (by omega),List.getElem_ofFn]
  have hpotZero : SignedTableAt mem (heap+J.m) (fun _ : Fin J.n => (0 : ℤ)) := by
    intro v i hi
    have hi' : i=0 ∨ i=1 := by change i<2 at hi; omega
    rcases hi' with rfl | rfl <;>
      simp only [encodeInt,Int.lt_irrefl,↓reduceIte,Int.natAbs_zero,List.getElem_cons_zero,List.getElem_cons_succ] <;>
      exact hz _ (by omega)
  apply runs_start_le
  unfold costInitialBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+J.m+2*J.n) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [heap,heap+J.m,1,heap+J.m+2*J.n]) (by eval_expr) (by wram_words)
    ⟨by rfl,(by change ZeroFrom mem (heap+J.m+2*J.n); exact hz.mono (by omega)),hs⟩ ?_
  intro ret memH posH hpostH
  obtain ⟨⟨_,_,hframeH,hzH,hheaderH⟩,hretH⟩ := hpostH
  change ret=heap+J.m+2*J.n+3 at hretH
  change (∀ x<heap+J.m+2*J.n,memH x=mem x) at hframeH
  change ZeroFrom memH ret at hzH
  change ListAt memH (heap+J.m+2*J.n) [heap,heap+J.m,1] at hheaderH
  have hflowH := hflow.of_agree_below (h₀ := heap+J.m+2*J.n)
    (by simp only [List.length_ofFn]; omega) hframeH
  have hpotH := hpotZero.of_agree_below (by omega : heap+J.m+2*J.n≤heap+J.m+2*J.n) hframeH
  have hstate : CostStateAt memH (ret-3) ret (CostState.initial J) := by
    have hbase : ret-3=heap+J.m+2*J.n := by omega
    rw [hbase]
    apply costStateAt_of_arrays (flow := heap) (pot := heap+J.m) hheaderH (by omega) (by omega)
    · simpa only [CostState.initial,Int.toNat_zero] using hflowH
    · exact fun _ => le_rfl
    · exact hpotH
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change ret=heap+J.m+2*J.n+3 ∧ CostStateAt memH (ret-3) ret (CostState.initial J) ∧
      ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
    exact ⟨hretH,hstate,hzH,fun x hx => hframeH x (by omega)⟩
  · simp only [costInitialContract,costHeaderContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

/-- Fixed multiplier two on the graph encoding supplies every initializer
premise and argument word, including empty graphs. -/
theorem costInitial_pre_wordSize (J : Circulation) :
    (∀ x∈[0,J.solverWords.length],x<2^wordSize 2 J.solverWords) ∧
      (costInitialContract (wordSize 2 J.solverWords) J).pre
        [0,J.solverWords.length] (initMem J.solverWords) := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hn : J.n≤J.solverWords.foldr max 0 := Link.elem_le_foldr_max List.mem_cons_self
  have hB : 4+5*J.m≤B := by dsimp only [B]; omega
  have hspace : J.solverWords.length+J.m+2*J.n+3≤3*B := by dsimp only [B]; omega
  have hB2 : 3*B≤B^2 := by simpa only [pow_two] using Nat.mul_le_mul_right B (show 3≤B by omega)
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤2) J.solverWords
  change B^2<2^wordSize 2 J.solverWords at hp
  have hs := (hspace.trans hB2).trans_lt hp
  refine ⟨?_,0,J.solverWords.length,rfl,listAt_initMem _,by omega,zeroFrom_initMem _,hs⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
