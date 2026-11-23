module

public import MinCostFlow.IPM.Machine.InitialDeficitTables
public import MinCostFlow.IPM.Machine.InitialEncodedInstance
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic

/-!
# The initialized graph as a verified machine procedure

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) builds an augmented graph from the original
midpoint deficits. This entry computes both endpoint tables and then
assembles the graph. Its postcondition names the existing
`initialInstance` itself and the exact output address. The artificial
penalty is supplied as a nonnegative machine word; the outer
initialization supplies the prescribed `4mU²`.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[input,penalty,heap]`. The graph follows the two deficit tables. -/
def initialGraphBody (tables assemble : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .call 3 tables [.reg 0,.reg 2] ;;
  .call 4 assemble [.reg 0,.bin .add (.reg 2) (.reg 5),.reg 2,.reg 1,.reg 3] ;;
  .ret (.reg 4)

/-- Entry and the two previously verified initialization stages. -/
def initialGraphModule (b : ℕ) : List Stmt :=
  [initialGraphBody (b+1) (b+6)] ++
    (initialDeficitTablesModule (b+1) ++ initialRecordAssemblyModule (b+6))

/-- The graph starts at `heap+2n`; the first `2n` words are the scratch
endpoint tables. Total worst-case space is `2+5m+7n`, and the body costs
at most `300m+400n+1200`. Its graph output is exactly Lemma 4.12's
construction, not merely an arbitrary feasible augmented graph. -/
def initialGraphContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a penalty heap, args = [a,penalty,heap] ∧ 0 < J.m ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧ (∀ e, 1 ≤ J.capacity e) ∧
      (∑ e : Fin J.m, J.capacity e) < 2^w)
    (fun args _ mem' => ZeroLowerAt mem' (heapArg args+2*J.n)
      (initialInstance J.toInstance (args.getD 1 0 : ℕ)))
    (fun _ _ => 300*J.m+400*J.n+1200) (fun _ _ => 2+5*J.m+7*J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+2*J.n+2+5*(initialInstance J.toInstance (args.getD 1 0 : ℕ)).m }

/-- Graph initialization is deterministic, including its two scan modules. -/
theorem initialGraphModule_noRand (b : ℕ) : ∀ body ∈ initialGraphModule b, body.NoRand := by
  intro body hb
  simp only [initialGraphModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [initialGraphBody,Stmt.NoRand]
  · exact initialDeficitTablesModule_noRand _ body hb
  · exact initialRecordAssemblyModule_noRand _ body hb

/-- The complete graph-building entry meets its named-instance, memory,
space and linear-cost specification for every random tape. -/
theorem initialGraph_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialGraphModule b)) (J : Circulation) :
    MeetsContract w p b (initialGraphContract w J) := by
  have hrest : p.HasAt (b+1) (initialDeficitTablesModule (b+1) ++ initialRecordAssemblyModule (b+6)) :=
    Num.hasAt_append_right hp
  have htables := Num.hasAt_append_left hrest
  have hassembly : p.HasAt (b+6) (initialRecordAssemblyModule (b+6)) := Num.hasAt_append_right hrest
  have htableSpec := initialDeficitTables_meetsContract hw htables J
  have hassemblySpec := initialRecordAssembly_meetsContract hw hassembly J
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,penalty,heap,rfl,hm,hat,hend,hinput,hpositive,htotal⟩,hzero,hspace⟩ := hpre
  change heap+(2+5*J.m+7*J.n) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hnw : J.n < 2^w := hinput _ List.mem_cons_self
  have hkw : penalty < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have ha : a < 2^w := hwords _ (by simp)
  have hincw : heap+J.n < 2^w := by omega
  have hfree : (freeEdges J.toInstance).card = J.m := by
    rw [freeEdges_circulation J hpositive,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
  have hM : (initialInstance J.toInstance penalty).m = J.m+(deficitVertices J.toInstance).card := by
    rw [initialInstance_m,hfree]
  apply runs_start_le
  unfold initialGraphBody
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
        mem1 (heap+J.n+i) < 2^w ∧ mem1 (heap+i) < 2^w := by
      intro i hi
      refine ⟨by omega,by omega,?_,?_⟩
      · rw [(hsums i hi).2]
        exact (incomingCapacity_le_total J i).trans_lt htotal
      · rw [(hsums i hi).1]
        exact (outgoingCapacity_le_total J i).trans_lt htotal
    refine runs_seq_call_le hassemblySpec (vs := [a,heap+J.n,heap,penalty,v1])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,_,rfl,hat1,by omega,hinput,hinputTables⟩,hzero1,
        by change v1+(2+5*J.m+5*J.n) < 2^w; omega⟩
    · intro v2 mem2 pos2 hp2
      obtain ⟨⟨hlo2,hhi2,hframe2,hzero2,hgraph⟩,hv2⟩ := hp2
      change ListAt mem2 v1 (initialAssemblyWords J (fun i => mem1 (heap+J.n+i))
        (fun i => mem1 (heap+i)) penalty) at hgraph
      change v2 = v1+2+5*J.m+(initialAuxiliaryPrefix (fun i => mem1 (heap+J.n+i))
        (fun i => mem1 (heap+i)) J.n penalty J.n).length at hv2
      change ∀ x < v1, mem2 x = mem1 x at hframe2
      have hauxeq : initialAuxiliaryPrefix (fun i => mem1 (heap+J.n+i)) (fun i => mem1 (heap+i))
          J.n penalty J.n = initialAuxiliaryPrefix (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n :=
        initialAuxiliaryPrefix_congr _ _ _ _ _ _ _ (fun i hi => (hsums i hi).2) (fun i hi => (hsums i hi).1)
      have hgrapheq : initialAssemblyWords J (fun i => mem1 (heap+J.n+i)) (fun i => mem1 (heap+i)) penalty =
          zeroLowerWords (initialInstance J.toInstance penalty) := by
        unfold initialAssemblyWords
        rw [hauxeq]
        exact initialAssemblyWords_eq_initialInstance J hpositive penalty
      rw [hgrapheq] at hgraph
      rw [hauxeq,initialAuxiliaryPrefix_length_deficit] at hv2
      have hreturn : v2 = heap+2*J.n+2+5*(initialInstance J.toInstance penalty).m := by
        rw [hM]
        omega
      have hv2w : v2 < 2^w := by
        have hmax : (deficitVertices J.toInstance).card ≤ J.n :=
          (Finset.card_filter_le _ _).trans (by simp)
        omega
      refine runs_ret_le (v := v2) (by eval_expr) ?_ ?_
      · change (heap ≤ v2 ∧ v2 ≤ heap+(2+5*J.m+7*J.n) ∧
          (∀ x < heap, mem2 x = mem x) ∧ ZeroFrom mem2 v2 ∧
          ZeroLowerAt mem2 (heap+2*J.n) (initialInstance J.toInstance penalty)) ∧
          v2 = heap+2*J.n+2+5*(initialInstance J.toInstance penalty).m
        have hbound : (deficitVertices J.toInstance).card ≤ J.n :=
          (Finset.card_filter_le _ _).trans (by simp)
        refine ⟨⟨by omega,by omega,?_,hzero2,?_,?_,?_⟩,hreturn⟩
        · intro x hx
          exact (hframe2 x (by omega)).trans (hframe1 x hx)
        · exact (initialInstance_zeroLower J hpositive penalty).1
        · exact (initialInstance_zeroLower J hpositive penalty).2
        · simpa only [hv1] using hgraph
      · simp only [initialGraphContract,initialDeficitTablesContract,initialRecordAssemblyContract,heapContract,
          Expr.size_reg,Expr.size_load,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
