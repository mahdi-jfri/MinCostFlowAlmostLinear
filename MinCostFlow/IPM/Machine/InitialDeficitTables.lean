module

public import MinCostFlow.IPM.Machine.InitialEndpointTable
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Computing both tables for Lemma 4.12's routing deficits

Appendix B.1 of Chen et al., arXiv:2203.00671v2 (page 92,
Lemma 4.12 on page 31), adds one auxiliary edge for each nonzero
midpoint routing deficit. This entry scans tails and heads into two
fresh consecutive unsigned arrays. Their signed difference is exactly
the existing `twiceDeficit`. Neither scan reads any future flow or
assumes an auxiliary-edge correctness oracle.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[input,heap]`. The incoming scan starts at the heap
returned by the outgoing scan, so the two tables are disjoint. -/
def initialDeficitTablesBody (outScan inScan : ℕ) : Stmt :=
  .call 2 outScan [.reg 0,.reg 1] ;;
  .call 3 inScan [.reg 0,.reg 2] ;;
  .ret (.reg 3)

/-- Entry plus the two instantiated endpoint scans. -/
def initialDeficitTablesModule (b : ℕ) : List Stmt :=
  [initialDeficitTablesBody (b+1) (b+3)] ++
    (initialEndpointTableModule (b+1) false ++ initialEndpointTableModule (b+3) true)

/-- The outgoing and incoming tables occupy `2n` words, with full heap
framing and cost at most `160m+400`. -/
def initialDeficitTablesContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,heap] ∧ 0 < J.m ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧ (∑ e : Fin J.m, J.capacity e) < 2^w)
    (fun args _ mem' => ∀ v < J.n,
      mem' (heapArg args+v) = outgoingCapacity J v ∧
      mem' (heapArg args+J.n+v) = incomingCapacity J v)
    (fun _ _ => 160*J.m+400) (fun _ _ => 2*J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+2*J.n }

/-- Both scans and their caller are deterministic. -/
theorem initialDeficitTablesModule_noRand (b : ℕ) :
    ∀ body ∈ initialDeficitTablesModule b, body.NoRand := by
  intro body hb
  simp only [initialDeficitTablesModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [initialDeficitTablesBody,Stmt.NoRand]
  · exact initialEndpointTableModule_noRand _ _ body hb
  · exact initialEndpointTableModule_noRand _ _ body hb

/-- The paired endpoint scans compute the complete original midpoint
routing data in linear time and exactly `2n` newly allocated words. -/
theorem initialDeficitTables_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialDeficitTablesModule b)) (J : Circulation) :
    MeetsContract w p b (initialDeficitTablesContract w J) := by
  have hrest : p.HasAt (b+1)
      (initialEndpointTableModule (b+1) false ++ initialEndpointTableModule (b+3) true) :=
    Num.hasAt_append_right hp
  have hout := Num.hasAt_append_left hrest
  have hin : p.HasAt (b+3) (initialEndpointTableModule (b+3) true) :=
    Num.hasAt_append_right hrest
  have hcout := initialEndpointTable_meetsContract hw false hout J
  have hcin := initialEndpointTable_meetsContract hw true hin J
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,heap,rfl,hm,hat,hend,hinput,htotal⟩,hzero,hspace⟩ := hpre
  change heap+2*J.n < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have ha : a < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold initialDeficitTablesBody
  refine runs_seq_call_le hcout (vs := [a,heap]) (by eval_expr) hwords ?_ ?_
  · exact ⟨⟨a,heap,rfl,hm,hat,hend,hinput,htotal⟩,hzero,by change heap+J.n < 2^w; omega⟩
  · intro v1 mem1 pos1 hp1
    obtain ⟨⟨hlo1,hhi1,hframe1,hzero1,htable1⟩,hv1⟩ := hp1
    change v1 = heap+J.n at hv1
    change ∀ x < heap, mem1 x = mem x at hframe1
    have hv1w : v1 < 2^w := by omega
    have hat1 : ListAt mem1 a J.solverWords := by
      intro i hi
      exact (hframe1 _ (by omega)).trans (hat i hi)
    refine runs_seq_call_le hcin (vs := [a,v1]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨a,v1,rfl,hm,hat1,by omega,hinput,htotal⟩,hzero1,
        by change v1+J.n < 2^w; omega⟩
    · intro v2 mem2 pos2 hp2
      obtain ⟨⟨hlo2,hhi2,hframe2,hzero2,htable2⟩,hv2⟩ := hp2
      change v2 = v1+J.n at hv2
      change ∀ x < v1, mem2 x = mem1 x at hframe2
      have hv2w : v2 < 2^w := by omega
      refine runs_ret_le (v := v2) (by eval_expr) ?_ ?_
      · change (heap ≤ v2 ∧ v2 ≤ heap+2*J.n ∧
          (∀ x < heap, mem2 x = mem x) ∧ ZeroFrom mem2 v2 ∧
          (∀ v < J.n, mem2 (heap+v) = outgoingCapacity J v ∧
            mem2 (heap+J.n+v) = incomingCapacity J v)) ∧ v2 = heap+2*J.n
        refine ⟨⟨by omega,by omega,?_,hzero2,?_⟩,by omega⟩
        · intro x hx
          exact (hframe2 x (by omega)).trans (hframe1 x hx)
        · intro v hv
          constructor
          · exact (hframe2 _ (by omega)).trans (htable1 v hv)
          · change ∀ v < J.n, mem2 (v1+v) = incomingCapacity J v at htable2
            simpa only [hv1] using htable2 v hv
      · simp only [initialDeficitTablesContract,initialEndpointTableContract,heapContract,
          Expr.size_reg,argsSize_cons,argsSize_nil]
        omega

/-- Subtracting the two output entries, as signed integers, gives the
precise doubled deficit used to orient and size the auxiliary edge. -/
theorem initialDeficitTables_deficit (J : Circulation) (mem' : ℕ → ℕ) (heap : ℕ)
    (hout : ∀ v < J.n, mem' (heap+v) = outgoingCapacity J v ∧
      mem' (heap+J.n+v) = incomingCapacity J v) (v : Fin J.n) :
    (mem' (heap+J.n+v) : ℤ)-(mem' (heap+v) : ℤ) = twiceDeficit J.toInstance v := by
  rw [(hout v v.isLt).1,(hout v v.isLt).2,twiceDeficit_eq_capacity_difference]

end MinCostFlow.IPM.Machine
