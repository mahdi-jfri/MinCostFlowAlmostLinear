module

public import MinCostFlow.IPM.Machine.InitialDeficitTables
public import MinCostFlow.IPM.Machine.ConnectedRecordAssembly
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic

/-!
# Building the connected graph

The connected version of Lemma 4.12 (page 31, Appendix B.1 page 92 of
Chen et al., arXiv:2203.00671v2) reuses the endpoint sums and emits
the original deficit edges followed by the two zero-deficit blocks.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[input,penalty,heap]`. The graph follows the two deficit tables. -/
def connectedGraphBody (tables assemble : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .call 3 tables [.reg 0,.reg 2] ;;
  .call 4 assemble [.reg 0,.bin .add (.reg 2) (.reg 5),.reg 2,.reg 1,.reg 3] ;;
  .ret (.reg 4)

/-- Entry and the two previously verified initialization stages. -/
def connectedGraphModule (b : ℕ) : List Stmt :=
  [connectedGraphBody (b+1) (b+6)] ++
    (initialDeficitTablesModule (b+1) ++ connectedRecordAssemblyModule (b+6))

/-- The graph starts at `heap+2n`; the first `2n` words are the scratch
endpoint tables. Total worst-case space is `2+5m+17n`. The graph is exactly
the connected augmentation with both zero-deficit blocks. -/
def connectedGraphContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a penalty heap, args = [a,penalty,heap] ∧ 0 < J.m ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧ (∀ e, 1 ≤ J.capacity e) ∧
      (∑ e : Fin J.m, J.capacity e) < 2^w)
    (fun args _ mem' => ZeroLowerAt mem' (heapArg args+2*J.n)
      (connectedInitialInstance J.toInstance (args.getD 1 0 : ℕ)))
    (fun _ _ => 300*J.m+900*J.n+1600) (fun _ _ => 2+5*J.m+17*J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+2*J.n+2+5*(connectedInitialInstance J.toInstance (args.getD 1 0 : ℕ)).m }

/-- Graph initialization is deterministic, including its two scan modules. -/
theorem connectedGraphModule_noRand (b : ℕ) : ∀ body ∈ connectedGraphModule b, body.NoRand := by
  intro body hb
  simp only [connectedGraphModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [connectedGraphBody,Stmt.NoRand]
  · exact initialDeficitTablesModule_noRand _ body hb
  · exact connectedRecordAssemblyModule_noRand _ body hb

/-- The complete graph-building entry meets its named-instance, memory,
space and linear-cost specification for every random tape. -/
theorem connectedGraph_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (connectedGraphModule b)) (J : Circulation) :
    MeetsContract w p b (connectedGraphContract w J) := by
  have hrest : p.HasAt (b+1) (initialDeficitTablesModule (b+1) ++ connectedRecordAssemblyModule (b+6)) :=
    Num.hasAt_append_right hp
  have htables := Num.hasAt_append_left hrest
  have hassembly : p.HasAt (b+6) (connectedRecordAssemblyModule (b+6)) := Num.hasAt_append_right hrest
  have htableSpec := initialDeficitTables_meetsContract hw htables J
  have hassemblySpec := connectedRecordAssembly_meetsContract hw hassembly J
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,penalty,heap,rfl,hm,hat,hend,hinput,hpositive,htotal⟩,hzero,hspace⟩ := hpre
  change heap+(2+5*J.m+17*J.n) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hnw : J.n < 2^w := hinput _ List.mem_cons_self
  have hkw : penalty < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have ha : a < 2^w := hwords _ (by simp)
  have hincw : heap+J.n < 2^w := by omega
  apply runs_start_le
  unfold connectedGraphBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_call_le htableSpec (vs := [a,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a,heap,rfl,hm,hat,hend,hinput,htotal⟩,hzero,by change heap+2*J.n < 2^w; omega⟩
  · intro v1 mem1 pos1 hp1
    obtain ⟨⟨hlo1,hhi1,hframe1,hzero1,hsums⟩,hv1⟩ := hp1
    change v1 = heap+2*J.n at hv1
    change ∀ x < heap, mem1 x = mem x at hframe1
    change ∀ v < J.n, mem1 (heap+v) = outgoingCapacity J v ∧
      mem1 (heap+J.n+v) = incomingCapacity J v at hsums
    have hv1w : v1 < 2^w := by omega
    have hat1 : ListAt mem1 a J.solverWords := by
      intro i hi
      exact (hframe1 _ (by omega)).trans (hat i hi)
    have hinputTables : ∀ i < J.n, heap+J.n+i < v1 ∧ heap+i < v1 ∧
        mem1 (heap+J.n+i) = incomingCapacity J i ∧ mem1 (heap+i) = outgoingCapacity J i ∧
        mem1 (heap+J.n+i) < 2^w ∧ mem1 (heap+i) < 2^w := by
      intro i hi
      refine ⟨by omega,by omega,(hsums i hi).2,(hsums i hi).1,?_,?_⟩
      · rw [(hsums i hi).2]
        exact (incomingCapacity_le_total J i).trans_lt htotal
      · rw [(hsums i hi).1]
        exact (outgoingCapacity_le_total J i).trans_lt htotal
    refine runs_seq_call_le hassemblySpec (vs := [a,heap+J.n,heap,penalty,v1])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,_,rfl,hat1,by omega,hinput,hpositive,hinputTables⟩,hzero1,
        by change v1+(2+5*J.m+15*J.n) < 2^w; omega⟩
    · intro v2 mem2 pos2 hp2
      obtain ⟨⟨hlo2,hhi2,hframe2,hzero2,hgraph⟩,hv2⟩ := hp2
      change ZeroLowerAt mem2 v1 (connectedInitialInstance J.toInstance (penalty : ℤ)) at hgraph
      change v2 = v1+2+5*(connectedInitialInstance J.toInstance (penalty : ℤ)).m at hv2
      change v2 ≤ v1+(2+5*J.m+15*J.n) at hhi2
      change ∀ x < v1, mem2 x = mem1 x at hframe2
      have hv2w : v2 < 2^w := by omega
      refine runs_ret_le (v := v2) (by eval_expr) ?_ ?_
      · change (heap ≤ v2 ∧ v2 ≤ heap+(2+5*J.m+17*J.n) ∧
          (∀ x < heap, mem2 x = mem x) ∧ ZeroFrom mem2 v2 ∧
          ZeroLowerAt mem2 (heap+2*J.n) (connectedInitialInstance J.toInstance (penalty : ℤ))) ∧
          v2 = heap+2*J.n+2+5*(connectedInitialInstance J.toInstance (penalty : ℤ)).m
        refine ⟨⟨by omega,by omega,?_,hzero2,by simpa only [hv1] using hgraph⟩,by omega⟩
        intro x hx
        exact (hframe2 x (by omega)).trans (hframe1 x hx)
      · simp only [connectedGraphContract,initialDeficitTablesContract,connectedRecordAssemblyContract,
          heapContract,Expr.size_reg,Expr.size_load,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
