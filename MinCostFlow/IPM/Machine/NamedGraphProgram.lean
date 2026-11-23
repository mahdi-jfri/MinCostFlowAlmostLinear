module

public import MinCostFlow.IPM.Machine.NamedGraphSource
public import MinCostFlow.IPM.Machine.VertexNames
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Preparing the fixed graph for min-ratio initialization

Read the shared instance dimensions, write the graph header, then call
the vertex-name and endpoint serializers. The output is the named graph
used by the IPM model, including its isolated vertices.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[sourceGraph,heap]`. -/
def namedGraphBody (vertices edges : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .store (.reg 1) (.reg 2) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 3) ;;
  .call 4 vertices [.reg 2,.bin .add (.reg 1) (.const 2)] ;;
  .call 5 edges [.bin .add (.reg 0) (.const 2),.reg 3,.reg 4] ;;
  .ret (.reg 5)

/-- Entry, vertex writer, endpoint scanner and record writer. -/
def namedGraphModule (b : ℕ) : List Stmt :=
  [namedGraphBody (b+1) (b+2)] ++ (vertexNamesModule ++ namedEdgeScanModule (b+2))

/-- The exact graph input layout for the min-ratio data structure. -/
def namedGraphContract (w : ℕ) (I : Instance) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args=[a,heap] ∧ I.IsValid ∧
      ListAt mem a (zeroLowerWords I) ∧ a+(zeroLowerWords I).length ≤ heap ∧
      ∀ x ∈ zeroLowerWords I,x < 2^w)
    (fun args _ mem' => GraphAt mem' (heapArg args) (namedInstance I))
    (fun _ _ => 30*I.n+100*I.m+300) (fun _ _ => 2+I.n+3*I.m)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+(2+I.n+3*I.m)}

/-- Graph preparation contains no random instruction. -/
theorem namedGraphModule_noRand (b : ℕ) :
    ∀ body ∈ namedGraphModule b,body.NoRand := by
  intro body hb
  simp only [namedGraphModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [namedGraphBody,Stmt.NoRand]
  · have he : body=vertexNamesBody := by simpa [vertexNamesModule] using hb
    subst body
    exact vertexNames_noRand
  · exact namedEdgeScanModule_noRand _ _ hb

/-- The graph serializer writes the actual named model graph, with a
linear operation bound and exact allocation. -/
theorem namedGraph_meetsContract {w b : ℕ} {p : Program}
    (hw : 5 < 2^w) (I : Instance) (hp : p.HasAt b (namedGraphModule b)) :
    MeetsContract w p b (namedGraphContract w I) := by
  have ht := Num.hasAt_append_right hp
  have hv : p.HasAt (b+1) vertexNamesModule := Num.hasAt_append_left ht
  have he : p.HasAt (b+2) (namedEdgeScanModule (b+2)) := by
    simpa [vertexNamesModule,Nat.add_assoc] using Num.hasAt_append_right ht
  have vSpec := vertexNames_meetsContract (by omega : 1 < 2^w) hv
  have eSpec := namedEdgeScan_meetsContract hw he
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hI,hat,hend,hinput⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(2+I.n+3*I.m) < 2^w at hspace
  have hlen := zeroLowerWords_length I hI
  have hheader := zeroLower_header_at I hI mem a hat
  have hn : I.n < 2^w := by
    rw [← hheader.1]
    simpa only [Nat.add_zero] using hat.words_lt hinput (i:=0) (by rw [hlen]; omega)
  have hm : I.m < 2^w := by
    rw [← hheader.2]
    exact hat.words_lt hinput (by rw [hlen]; omega)
  have ha : a < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  have hs : a+(2+5*I.m) ≤ heap := by simpa only [hlen] using hend
  apply runs_start_le
  unfold namedGraphBody
  wram_step
  wram_step
  wram_step
  wram_step
  simp only [startState,hheader.1,hheader.2]
  refine runs_seq_call_le vSpec (vs:=[I.n,heap+2]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · refine ⟨⟨_,_,rfl⟩,?_,?_⟩
    · change ZeroFrom (Function.update (Function.update mem heap I.n) (heap+1) I.m) (heap+2)
      intro x hx
      simp only [Function.update_of_ne (by omega : x ≠ heap+1),
        Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · change heap+2+I.n < 2^w
      omega
  · intro v mem0 pos0 hp0
    obtain ⟨⟨hlo,hhi,hframe,hfresh,hnames⟩,hv0⟩ := hp0
    change v=heap+2+I.n at hv0
    change ListAt mem0 (heap+2) (List.range I.n) at hnames
    change ∀ x < heap+2,mem0 x=(Function.update (Function.update mem heap I.n) (heap+1) I.m) x at hframe
    have hkeep : ∀ x < heap,mem0 x=mem x := by
      intro x hx
      rw [hframe x (by omega)]
      simp only [Function.update_of_ne (by omega : x ≠ heap+1),
        Function.update_of_ne (by omega : x ≠ heap)]
    have hsource := hat.of_agree_below hend hkeep
    have hendpoints := edgeTripleWords_namedInstance I hI mem0 a hsource
    have hvw : v < 2^w := by omega
    refine runs_seq_call_le eSpec (vs:=[a+2,I.m,v]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨_,_,_,rfl,?_⟩,hfresh,?_⟩
      · intro i hi
        have he0 := zeroLower_endpoints_at I hI mem0 a hsource ⟨i,hi⟩
        refine ⟨by omega,?_,?_⟩
        · change mem0 (a+2+5*i) < 2^w
          rw [he0.1]
          exact (hI.1 (I.edge ⟨i,hi⟩) (List.getElem_mem hi)).1.trans hn
        · change mem0 (a+2+1+5*i) < 2^w
          rw [show a+2+1+5*i=a+3+5*i by omega,he0.2]
          exact (hI.1 (I.edge ⟨i,hi⟩) (List.getElem_mem hi)).2.trans hn
      · change v+3*I.m < 2^w
        omega
    · intro v1 mem1 pos1 hp1
      obtain ⟨⟨hlo1,hhi1,hframe1,hfresh1,hedges⟩,hv1⟩ := hp1
      change v1=v+3*I.m at hv1
      change ∀ x < v,mem1 x=mem0 x at hframe1
      change ListAt mem1 v (edgeTripleWords mem0 (a+2) I.m) at hedges
      refine runs_ret_le (v:=v1) (by eval_expr) ?_ ?_
      · change (heap ≤ v1 ∧ v1 ≤ heap+(2+I.n+3*I.m) ∧
          (∀ x < heap,mem1 x=mem x) ∧ ZeroFrom mem1 v1 ∧
          GraphAt mem1 heap (namedInstance I)) ∧ v1=heap+(2+I.n+3*I.m)
        refine ⟨⟨by omega,by omega,?_,hfresh1,?_⟩,by omega⟩
        · intro x hx
          exact (hframe1 x (by omega)).trans (hkeep x hx)
        · change ListAt mem1 heap (graphWords (namedInstance I))
          rw [graphWords_namedInstance]
          have hh0 : ListAt mem1 heap [I.n,I.m] := by
            intro i hi
            have hii : i < 2 := by simpa using hi
            interval_cases i <;> simp only [List.getElem_cons_zero,List.getElem_cons_succ]
            · rw [Nat.add_zero,hframe1 heap (by omega),hframe heap (by omega)]
              simp
            · rw [hframe1 (heap+1) (by omega),hframe (heap+1) (by omega)]
              simp
          have hnames1 := hnames.of_agree_below (by simp only [List.length_range]; omega) hframe1
          have hhead : ListAt mem1 heap ([I.n,I.m]++List.range I.n) :=
            (listAt_append).mpr ⟨hh0,by simpa using hnames1⟩
          apply (listAt_append).mpr
          refine ⟨hhead,?_⟩
          simpa only [List.length_append,List.length_cons,List.length_nil,List.length_range,
            hendpoints,show heap+(1+(1+0)+I.n)=v by omega] using hedges
      · simp only [namedGraphContract,heapContract,vertexNamesContract,namedEdgeScanContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_load,
          Expr.size_bin,Expr.size_const,argsSize,heapArg]
        omega

end MinCostFlow.IPM.Machine
