module

public import MinCostFlow.IPM.Machine.RefreshSource
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Preparing an Update batch from changed edge names

Write the number of primitive updates, then scan the reported edge list.
Each changed edge contributes a deletion and reinsertion with its old
endpoints. The result is exactly the model batch used for coefficient
refresh on the fixed graph, with all source memory preserved.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[sourceGraph,names,count,heap]`. -/
def refreshBatchBody (scan : ℕ) : Stmt :=
  .store (.reg 3) (.bin .mul (.const 2) (.reg 2)) ;;
  .call 4 scan [.bin .add (.reg 0) (.const 2),.reg 1,.reg 2,.bin .add (.reg 3) (.const 1)] ;;
  .ret (.reg 4)

/-- Header entry followed by the changed-edge scanner. -/
def refreshBatchModule (b : ℕ) : List Stmt := [refreshBatchBody (b+1)] ++ refreshScanModule (b+1)

/-- The actual count-prefixed model batch, including header allocation. -/
def refreshBatchContract (w : ℕ) (I : Instance) (es : List ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a names heap,args=[a,names,es.length,heap] ∧ I.IsValid ∧
      ListAt mem a (zeroLowerWords I) ∧ ListAt mem names es ∧
      (∀ e ∈ es,e < I.m) ∧ a+(zeroLowerWords I).length ≤ heap ∧
      names+es.length ≤ heap ∧ ∀ x ∈ zeroLowerWords I,x < 2^w)
    (fun args _ mem' => BatchAt mem' (heapArg args) (refreshEdges (namedInstance I) es))
    (fun _ _ => 180*es.length+300) (fun _ _ => 1+6*es.length)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+(1+6*es.length)}

/-- The batch header, name reads and endpoint writes are deterministic. -/
theorem refreshBatchModule_noRand (b : ℕ) : ∀ body ∈ refreshBatchModule b,body.NoRand := by
  intro body hb
  simp only [refreshBatchModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [refreshBatchBody,Stmt.NoRand]
  · exact refreshScanModule_noRand _ _ hb

/-- The actual program prepares precisely the model refresh batch,
with a linear cost bound, exact heap endpoint and full input framing. -/
theorem refreshBatch_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (I : Instance) (es : List ℕ) (hp : p.HasAt b (refreshBatchModule b)) :
    MeetsContract w p b (refreshBatchContract w I es) := by
  have hs : p.HasAt (b+1) (refreshScanModule (b+1)) := Num.hasAt_append_right hp
  have hscan := refreshScan_meetsContract hw hs
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,names,heap,rfl,hI,hgraph,hnames,hes,hgEnd,hnEnd,hinput⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(1+6*es.length) < 2^w at hspace
  have hk : es.length < 2^w := hwords _ (by simp)
  have hheader : 2*es.length < 2^w := by omega
  have hgraphEnd : a+(2+5*I.m) ≤ heap := by
    simpa only [zeroLowerWords_length I hI] using hgEnd
  have ha : a < 2^w := hwords _ (by simp)
  have hn : names < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  let mem0 := Function.update mem heap (2*es.length)
  have hkeep : ∀ x < heap,mem0 x=mem x := by
    intro x hx
    dsimp only [mem0]
    rw [Function.update_of_ne (by omega : x ≠ heap)]
  have hgraph0 := hgraph.of_agree_below hgEnd hkeep
  have hnames0 := hnames.of_agree_below hnEnd hkeep
  have hz0 : ZeroFrom mem0 (heap+1) := by
    intro x hx
    dsimp only [mem0]
    rw [Function.update_of_ne (by omega : x ≠ heap)]
    exact hz x (by omega)
  have hpre0 := refreshScan_pre_from_instance I hI es hgraph0 hnames0 hes
    (hgEnd.trans (by omega)) (hnEnd.trans (by omega)) hinput hz0
    (by omega : heap+1+6*es.length < 2^w)
  have hmodel := refreshScanWords_namedInstance I hI mem0 a names es hgraph0 hnames0 hes
  apply runs_start_le
  unfold refreshBatchBody
  wram_step
  refine runs_seq_call_le hscan (vs:=[a+2,names,es.length,heap+1])
    (by eval_expr) (by wram_words) hpre0 ?_
  intro v mem1 pos1 hp1
  obtain ⟨⟨_,_,hframe,hfresh,hbody⟩,hv⟩ := hp1
  change v=heap+1+6*es.length at hv
  change ∀ x < heap+1,mem1 x=mem0 x at hframe
  change ListAt mem1 (heap+1) (refreshScanWords mem0 (a+2) names es.length) at hbody
  refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
  · change (heap ≤ v ∧ v ≤ heap+(1+6*es.length) ∧ (∀ x < heap,mem1 x=mem x) ∧
      ZeroFrom mem1 v ∧ BatchAt mem1 heap (refreshEdges (namedInstance I) es)) ∧
      v=heap+(1+6*es.length)
    refine ⟨⟨by omega,by omega,?_,hfresh,?_⟩,by omega⟩
    · intro x hx
      exact (hframe x (by omega)).trans (hkeep x hx)
    · change ListAt mem1 heap (batchWords (refreshEdges (namedInstance I) es))
      rw [batchWords_refreshEdges,listAt_cons]
      refine ⟨?_,?_⟩
      · rw [hframe heap (by omega)]
        simp [mem0]
      · simpa only [hmodel] using hbody
  · simp only [refreshBatchContract,refreshScanContract,heapContract,
      List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
