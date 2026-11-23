module

public import MinCostFlow.IPM.Machine.RefreshBatchProgram
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Turning a Detect answer into an Update batch

Definition 4.5 (page 14) returns a set of reported edges in any distinct
order. Read its count and pass that actual order to the fixed-graph batch
writer. The resulting batch refreshes exactly those edges and preserves
the original graph. The answer's full memory extent is reserved by the
caller before this entry allocates its own output.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[sourceGraph,detectAnswer,heap]`. -/
def detectBatchBody (batch : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .call 4 batch [.reg 0,.bin .add (.reg 1) (.const 1),.reg 3,.reg 2] ;;
  .ret (.reg 4)

/-- Detect header reader followed by the full batch writer. -/
def detectBatchModule (b : ℕ) : List Stmt := [detectBatchBody (b+1)] ++ refreshBatchModule (b+1)

/-- Prepare a valid fixed-graph batch for exactly the returned set,
retaining its actual distinct output order. -/
def detectBatchContract (w : ℕ) (I : Instance) (S : Finset ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a report heap,args=[a,report,heap] ∧ I.IsValid ∧
      ListAt mem a (zeroLowerWords I) ∧ DetectAt mem report S ∧
      S ⊆ (namedInstance I).E ∧ a+(zeroLowerWords I).length ≤ heap ∧
      report+1+S.card ≤ heap ∧ ∀ x ∈ zeroLowerWords I,x < 2^w)
    (fun args _ mem' => ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧
      BatchAt mem' (heapArg args) (refreshEdges (namedInstance I) es) ∧
      RefreshBatch (namedInstance I) (refreshEdges (namedInstance I) es))
    (fun _ _ => 180*S.card+400) (fun _ _ => 1+6*S.card)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+(1+6*S.card)}

/-- Reading Detect's header and preparing its batch are deterministic. -/
theorem detectBatchModule_noRand (b : ℕ) : ∀ body ∈ detectBatchModule b,body.NoRand := by
  intro body hb
  simp only [detectBatchModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [detectBatchBody,Stmt.NoRand]
  · exact refreshBatchModule_noRand _ _ hb

/-- The actual Detect output, in any reported order, yields exactly the
model's valid coefficient-refresh batch with a linear operation bound. -/
theorem detectBatch_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (I : Instance) (S : Finset ℕ) (hp : p.HasAt b (detectBatchModule b)) :
    MeetsContract w p b (detectBatchContract w I S) := by
  have hbatch : p.HasAt (b+1) (refreshBatchModule (b+1)) := Num.hasAt_append_right hp
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,report,heap,rfl,hI,hgraph,hdetect,hsubset,hgEnd,hdEnd,hinput⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(1+6*S.card) < 2^w at hspace
  have hcount := hdetect.count
  obtain ⟨es,hnd,hset,hheader,hnames⟩ := hdetect
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hes : ∀ e ∈ es,e < I.m := by
    intro e he
    have hs : e ∈ S := by rw [← hset]; exact List.mem_toFinset.mpr he
    exact Finset.mem_range.mp (hsubset hs)
  have hcountWord : S.card < 2^w := by omega
  have ha : a < 2^w := hwords _ (by simp)
  have hr : report < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  have hreport : report+1 < 2^w := by omega
  have hbatchSpec := refreshBatch_meetsContract hw I es hbatch
  have hbatchPre : (refreshBatchContract w I es).pre [a,report+1,S.card,heap] mem := by
    rw [← hlen]
    exact ⟨⟨a,report+1,heap,rfl,hI,hgraph,hnames,hes,hgEnd,by omega,hinput⟩,hz,by change heap+(1+6*es.length) < 2^w; simpa only [hlen] using hspace⟩
  apply runs_start_le
  unfold detectBatchBody
  wram_step
  refine runs_seq_call_le hbatchSpec (vs:=[a,report+1,S.card,heap])
    (by eval_expr) (by wram_words) hbatchPre ?_
  intro v mem1 pos1 hp1
  obtain ⟨⟨_,_,hframe,hfresh,hbody⟩,hv⟩ := hp1
  change v=heap+(1+6*es.length) at hv
  change ∀ x < heap,mem1 x=mem x at hframe
  change BatchAt mem1 heap (refreshEdges (namedInstance I) es) at hbody
  refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
  · change (heap ≤ v ∧ v ≤ heap+(1+6*S.card) ∧ (∀ x < heap,mem1 x=mem x) ∧
      ZeroFrom mem1 v ∧ ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧
        BatchAt mem1 heap (refreshEdges (namedInstance I) es) ∧
        RefreshBatch (namedInstance I) (refreshEdges (namedInstance I) es)) ∧
      v=heap+(1+6*S.card)
    refine ⟨⟨by omega,by omega,hframe,hfresh,es,hnd,hset,hbody,?_⟩,by omega⟩
    apply refreshEdges_isRefreshBatch _ (namedInstance_valid I hI) es
    intro e he
    exact Finset.mem_range.mpr (hes e he)
  · simp only [detectBatchContract,refreshBatchContract,heapContract,
      Expr.size_reg,Expr.size_load,
      Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
