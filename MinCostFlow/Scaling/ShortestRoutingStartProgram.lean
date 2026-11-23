module

public import MinCostFlow.Scaling.ShortestRoutingModel
public import MinCostFlow.Scaling.WordFillProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# The shortest-routing starting flow as a word array

The model routes one unit from the added source to each original vertex.
Its original edge slots have flow zero and its new source arcs have flow
one. Read the two graph dimensions and fill these consecutive blocks.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The model's starting vector is a zero block followed by a one block. -/
theorem shortestRoutingStart_words (J : Circulation) :
    List.ofFn (fun e => (J.shortestRoutingStart e).toNat) =
      List.replicate J.m 0 ++ List.replicate J.n 1 := by
  rw [List.ofFn_add]
  change (List.ofFn (fun i => (J.shortestRoutingStart (Fin.castAdd J.n i)).toNat)) ++
    (List.ofFn (fun i => (J.shortestRoutingStart (Fin.natAdd J.m i)).toNat)) = _
  simp only [Circulation.shortestRoutingStart, Fin.addCases_left, Fin.addCases_right,
    Int.toNat_zero, Int.toNat_one, List.ofFn_const]

/-- Arguments `[graph,heap]`. -/
def shortestRoutingStartBody (fill : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 fill [.reg 3, .const 0, .reg 1] ;;
  .call 5 fill [.reg 2, .const 1, .reg 4] ;;
  .ret (.reg 5)

/-- Starting-vector entry and the constant-array procedure. -/
def shortestRoutingStartModule (b : ℕ) : List Stmt :=
  shortestRoutingStartBody (b+1) :: wordFillModule (b+1)

/-- The unsigned starting vector occupies exactly `m+n` fresh words. -/
def shortestRoutingStartContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (List.ofFn (fun e => (J.shortestRoutingStart e).toNat)))
    (fun _ _ => 40*(J.m+J.n)+200) (fun _ _ => J.m+J.n)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+J.m+J.n }

/-- Starting-vector construction uses no random instruction. -/
theorem shortestRoutingStartModule_noRand (b : ℕ) :
    ∀ body ∈ shortestRoutingStartModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [shortestRoutingStartBody, Stmt.NoRand, and_self]
  · have hh : body = wordFillBody (b+1) := by simpa only [wordFillModule, List.mem_singleton] using hb
    subst body
    exact wordFillBody_noRand _

/-- The procedure computes exactly the unsigned model starting vector,
with linear cost, exact allocation, and preservation of the graph prefix. -/
theorem shortestRoutingStart_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (shortestRoutingStartModule b)) (J : Circulation) :
    MeetsContract w p b (shortestRoutingStartContract w J) := by
  have hfill := hasAt_tail hp
  have hk0 := wordFill_meetsContract (w := w) hfill J.m 0
  have hk1 := wordFill_meetsContract (w := w) hfill J.n 1
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hw⟩, hz, hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(J.m+J.n) < 2^w at hs
  have hheader := solver_header_at J hat
  obtain ⟨hN, hM⟩ := hheader
  have hh : heap < 2^w := by omega
  have hm : J.m < 2^w := by omega
  have hn : J.n < 2^w := by omega
  have hhM : heap+J.m < 2^w := by omega
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hone : 1 < 2^w := by omega
  apply runs_start_le
  unfold shortestRoutingStartBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk0 (vs := [J.m,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨heap,rfl,by omega,hone⟩,hz,hhM⟩
  · intro mid mem0 pos0 hpost0
    obtain ⟨⟨_,_,hframe0,hz0,hat0⟩,hmid⟩ := hpost0
    change mid = heap+J.m at hmid
    change ZeroFrom mem0 mid at hz0
    change (∀ x < heap, mem0 x = mem x) at hframe0
    change ListAt mem0 heap (List.replicate J.m 0) at hat0
    have hmidWord : mid < 2^w := by omega
    refine runs_seq_call_le hk1 (vs := [J.n,1,mid]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨mid,rfl,hone,hone⟩,hz0,by change mid+J.n < 2^w; omega⟩
    · intro ret mem1 pos1 hpost1
      obtain ⟨⟨_,_,hframe1,hz1,hat1⟩,hret⟩ := hpost1
      change ret = mid+J.n at hret
      change (∀ x < mid, mem1 x = mem0 x) at hframe1
      change ZeroFrom mem1 ret at hz1
      change ListAt mem1 mid (List.replicate J.n 1) at hat1
      have hr : ret < 2^w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap ≤ ret ∧ ret ≤ heap+(J.m+J.n) ∧ (∀ x < heap, mem1 x = mem x) ∧
          ZeroFrom mem1 ret ∧ ListAt mem1 heap (List.ofFn (fun e => (J.shortestRoutingStart e).toNat))) ∧
          ret = heap+J.m+J.n
        refine ⟨⟨by omega,by omega,?_,hz1,?_⟩,by omega⟩
        · intro x hx
          exact (hframe1 x (by omega)).trans (hframe0 x hx)
        · rw [shortestRoutingStart_words]
          apply listAt_append.mpr
          refine ⟨hat0.of_agree_below (by simpa only [List.length_replicate] using hmid.ge) hframe1, ?_⟩
          simpa only [List.length_replicate, hmid] using hat1
      · simp only [shortestRoutingStartContract, wordFillContract, heapContract,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

/-- Multiplier two on the graph encoding fits the complete starting-vector
construction in its canonical input memory. -/
theorem shortestRoutingStart_pre_wordSize (J : Circulation) :
    (∀ x ∈ [0,J.solverWords.length], x < 2^wordSize 2 J.solverWords) ∧
    (shortestRoutingStartContract (wordSize 2 J.solverWords) J).pre
      [0,J.solverWords.length] (initMem J.solverWords) := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hn : J.n ≤ J.solverWords.foldr max 0 := Link.elem_le_foldr_max List.mem_cons_self
  have hB : J.n+4+5*J.m ≤ B := by dsimp only [B]; omega
  have hB4 : 4 ≤ B := by omega
  have hfour : 4*B ≤ B^2 := by simpa only [pow_two] using Nat.mul_le_mul_right B hB4
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) J.solverWords
  change B^2 < 2^wordSize 2 J.solverWords at hp
  have hs : J.solverWords.length+J.m+J.n < 2^wordSize 2 J.solverWords := by omega
  refine ⟨?_,⟨0,J.solverWords.length,rfl,listAt_initMem _,by omega,by omega⟩,
    zeroFrom_initMem _,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · change J.solverWords.length+(J.m+J.n) < _
    simpa only [Nat.add_assoc] using hs

end MinCostFlow.Scaling.Machine
