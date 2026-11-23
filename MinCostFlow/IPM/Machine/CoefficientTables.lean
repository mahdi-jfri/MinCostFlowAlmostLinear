module

public import MinCostFlow.IPM.Machine.GraphCoefficientTable
public import MinCostFlow.IPM.Machine.ZeroTable
public import MinCostFlow.IPM.Machine.DyadicBlock
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Preparing the numerical inputs of a target test

Reserve the zero lower-capacity array, load signed costs at precision
zero, load upper capacities on the flow grid, and store the exact unit
block required by the power procedures. All arrays name the actual fixed
graph's coefficients. Numerical scratch remains after each dense array
and is included in the allocation and cost bounds.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[graph,L,P,heap]`. -/
def coefficientTablesBody (zeroEntry costs uppers one : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 zeroEntry [.reg 4,.reg 1,.reg 3] ;;
  .call 6 costs [.reg 0,.reg 1,.const 0,.reg 5] ;;
  .call 7 uppers [.reg 0,.reg 1,.reg 2,.reg 6] ;;
  .call 8 one [.const 0,.reg 1,.reg 2,.reg 7] ;;
  .ret (.reg 8)

/-- Zero reservation, the two graph-table loaders and exact unit storage. -/
def coefficientTablesModule (b h : ℕ) : List Stmt :=
  [coefficientTablesBody (b+1) (b+2) (b+13) (b+24)] ++
    (zeroTableModule ++ (graphCoefficientTableModule (b+2) h true ++
      (graphCoefficientTableModule (b+13) h false ++ dyadicBlockModule)))

/-- The array layout is lower at heap, costs at `heap+mL`, uppers at
`heap+5mL`, and the unit block at `heap+9mL`. -/
def coefficientTablesContract (w h : ℕ) (I : Instance) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L P heap,args=[a,L,P,heap] ∧ I.IsValid ∧ 0 < I.m ∧
      ZeroLowerAt mem a I ∧ a+(zeroLowerWords I).length ≤ heap ∧
      (∀ x ∈ zeroLowerWords I,x < 2^w) ∧ P+2 ≤ h*L ∧
      (∀ e : Fin I.m,Num.Fits h L (I.edge e).cost) ∧
      ∀ e : Fin I.m,Num.Fits h L (I.edge e).upper ∧ Num.Fits h L ((I.edge e).upper*(2:ℤ)^P))
    (fun args _ mem' =>
      let L := args.getD 1 0
      let P := args.getD 2 0
      let heap := heapArg args
      (∀ e : Fin I.m,ScalarAt mem' (heap+e.val*L) h L P 0 ∧
        ScalarAt mem' (heap+I.m*L+e.val*L) h L 0 ((I.edge e).cost:ℝ) ∧
        ScalarAt mem' (heap+5*(I.m*L)+e.val*L) h L P ((I.edge e).upper:ℝ)) ∧
      ScalarAt mem' (heap+9*(I.m*L)) h L P 1)
    (fun args _ => I.m*(600*args.getD 1 0+1800)+700)
    (fun args _ => (9*I.m+1)*args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+(9*I.m+1)*args.getD 1 0}

/-- All numerical table-preparation modules are deterministic. -/
theorem coefficientTablesModule_noRand (b h : ℕ) :
    ∀ body ∈ coefficientTablesModule b h,body.NoRand := by
  intro body hb
  simp only [coefficientTablesModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb | hb | hb
  · simp [coefficientTablesBody,Stmt.NoRand]
  · have he : body=zeroTableBody := by simpa [zeroTableModule] using hb
    subst body
    exact zeroTable_noRand
  · exact graphCoefficientTableModule_noRand _ _ _ _ hb
  · exact graphCoefficientTableModule_noRand _ _ _ _ hb
  · have he : body=dyadicBlockBody := by simpa [dyadicBlockModule] using hb
    subst body
    exact dyadicBlock_noRand

private theorem table_scalar_frozen {mem mem' : ℕ → ℕ} {a h L P heap : ℕ} {x : ℝ}
    (hf : ∀ i < heap,mem' i=mem i) (ha : a+L ≤ heap)
    (hx : ScalarAt mem a h L P x) : ScalarAt mem' a h L P x :=
  ⟨Num.IPM.valid_frozen hf ha hx.1,(Num.IPM.fixVal_frozen hf ha).trans hx.2⟩

/-- The zero lower array, signed cost table, upper-capacity table and unit
block are all prepared by actual verified calls, with explicit total cost. -/
theorem coefficientTables_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hh4 : h=4) (hconst : 16 < 2^w) (I : Instance)
    (hp : p.HasAt b (coefficientTablesModule b h)) :
    MeetsContract w p b (coefficientTablesContract w h I) := by
  subst h
  have htail := Num.hasAt_append_right hp
  have hz : p.HasAt (b+1) zeroTableModule := Num.hasAt_append_left htail
  have ht1 := Num.hasAt_append_right htail
  have hc : p.HasAt (b+2) (graphCoefficientTableModule (b+2) 4 true) := by
    simpa [zeroTableModule] using Num.hasAt_append_left ht1
  have ht2 := Num.hasAt_append_right ht1
  have hu : p.HasAt (b+13) (graphCoefficientTableModule (b+13) 4 false) := by
    simpa [zeroTableModule,graphCoefficientTableModule,fixedIntegerVectorModule,
      fixedIntegerBlockModule,Num.loadIntModule,Num.negateModule,Num.shiftLeftModule,
      Num.IPM.writeBlockModule,Num.copyModule,Nat.add_assoc] using Num.hasAt_append_left ht2
  have hone : p.HasAt (b+24) dyadicBlockModule := by
    simpa [zeroTableModule,graphCoefficientTableModule,fixedIntegerVectorModule,
      fixedIntegerBlockModule,Num.loadIntModule,Num.negateModule,Num.shiftLeftModule,
      Num.IPM.writeBlockModule,Num.copyModule,Nat.add_assoc] using Num.hasAt_append_right ht2
  have hcSpec := graphCoefficientTable_meetsContract hh hw (by omega : 6 < 2^w) I true hc
  have huSpec := graphCoefficientTable_meetsContract hh hw (by omega : 6 < 2^w) I false hu
  have hoSpec := dyadicBlock_meetsContract hconst hone
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,L,P,heap,rfl,hI,hm,hat,hend,hinput,hwidth,hcost,hupper⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  have halloc : (9*I.m+1)*L=9*(I.m*L)+L := by ring
  change heap+(9*I.m+1)*L < 2^w at hspace
  rw [halloc] at hspace
  have hlen := zeroLowerWords_length I hI
  have hheader := zeroLower_header_at I hI mem a hat.2.2
  have hM : mem (a+1)=I.m := hheader.2
  have hcostId : I.m*(600*L+1800)=2*(I.m*(300*L+900)) := by ring
  have ha : a < 2^w := hwords _ (by simp)
  have hL : L < 2^w := hwords _ (by simp)
  have hP : P < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hend' : a+(2+5*I.m) ≤ heap := by simpa only [hlen] using hend
  have hmw : I.m < 2^w := by
    rw [← hheader.2]
    exact hat.2.2.words_lt hinput (by rw [hlen]; omega)
  have hzSpec := zeroTable_meetsContract (w:=w) (h:=4) (P:=P) hz
  apply runs_start_le
  unfold coefficientTablesBody
  wram_step
  refine runs_seq_call_le hzSpec (vs:=[I.m,L,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_,_,_,rfl⟩,hzero,by change heap+I.m*L < 2^w; omega⟩
  · intro v0 mem0 pos0 hp0
    obtain ⟨⟨hlo0,hhi0,hframe0,hfresh0,hlower⟩,hv0⟩ := hp0
    change v0=heap+I.m*L at hv0
    change ∀ i < I.m,ScalarAt mem0 (heap+i*L) 4 L P 0 at hlower
    change ∀ x < heap,mem0 x=mem x at hframe0
    have hgraph0 : ZeroLowerAt mem0 a I :=
      ⟨hat.1,hat.2.1,hat.2.2.of_agree_below hend hframe0⟩
    have hv0w : v0 < 2^w := by omega
    refine runs_seq_call_le hcSpec (vs:=[a,L,0,v0]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a,L,0,v0,rfl,hI,hm,hgraph0,by omega,hinput,?_⟩,hfresh0,?_⟩
      · intro e
        simpa only [↓reduceIte,pow_zero,mul_one] using And.intro (hcost e) (hcost e)
      · change v0+4*(I.m*L) < 2^w
        omega
    · intro v1 mem1 pos1 hp1
      obtain ⟨⟨hlo1,hhi1,hframe1,hfresh1,hcosts⟩,hv1⟩ := hp1
      change v1=v0+4*(I.m*L) at hv1
      change ∀ e : Fin I.m,ScalarAt mem1 (v0+e.val*L) 4 L 0 ((I.edge e).cost:ℝ) at hcosts
      change ∀ x < v0,mem1 x=mem0 x at hframe1
      have hgraph1 : ZeroLowerAt mem1 a I :=
        ⟨hat.1,hat.2.1,hgraph0.2.2.of_agree_below (by omega) hframe1⟩
      have hv1w : v1 < 2^w := by omega
      refine runs_seq_call_le huSpec (vs:=[a,L,P,v1]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨a,L,P,v1,rfl,hI,hm,hgraph1,by omega,hinput,hupper⟩,hfresh1,
          by change v1+4*(I.m*L) < 2^w; omega⟩
      · intro v2 mem2 pos2 hp2
        obtain ⟨⟨hlo2,hhi2,hframe2,hfresh2,huppers⟩,hv2⟩ := hp2
        change v2=v1+4*(I.m*L) at hv2
        change ∀ e : Fin I.m,ScalarAt mem2 (v1+e.val*L) 4 L P ((I.edge e).upper:ℝ) at huppers
        change ∀ x < v1,mem2 x=mem1 x at hframe2
        have hv2w : v2 < 2^w := by omega
        refine runs_seq_call_le hoSpec (vs:=[0,L,P,v2]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨⟨0,L,P,v2,rfl,Nat.zero_le _,hwidth⟩,hfresh2,
            by change v2+L < 2^w; omega⟩
        · intro v3 mem3 pos3 hp3
          obtain ⟨⟨hlo3,hhi3,hframe3,hfresh3,hunit⟩,hv3⟩ := hp3
          change v3=v2+L at hv3
          change ScalarAt mem3 v2 4 L P (1/(2:ℝ)^0) at hunit
          change ∀ x < v2,mem3 x=mem2 x at hframe3
          have hv3w : v3 < 2^w := by omega
          have hunit' : ScalarAt mem3 (heap+9*(I.m*L)) 4 L P 1 := by
            have he : v2=heap+9*(I.m*L) := by omega
            simpa only [he,pow_zero,div_one] using hunit
          refine runs_ret_le (v:=v3) (by eval_expr) ?_ ?_
          · change (heap ≤ v3 ∧ v3 ≤ heap+(9*I.m+1)*L ∧
              (∀ x < heap,mem3 x=mem x) ∧ ZeroFrom mem3 v3 ∧
              (∀ e : Fin I.m,ScalarAt mem3 (heap+e.val*L) 4 L P 0 ∧
                ScalarAt mem3 (heap+I.m*L+e.val*L) 4 L 0 ((I.edge e).cost:ℝ) ∧
                ScalarAt mem3 (heap+5*(I.m*L)+e.val*L) 4 L P ((I.edge e).upper:ℝ)) ∧
              ScalarAt mem3 (heap+9*(I.m*L)) 4 L P 1) ∧ v3=heap+(9*I.m+1)*L
            rw [halloc]
            refine ⟨⟨by omega,by omega,?_,hfresh3,?_,?_⟩,by omega⟩
            · intro x hx
              exact (hframe3 x (by omega)).trans ((hframe2 x (by omega)).trans
                ((hframe1 x (by omega)).trans (hframe0 x hx)))
            · intro e
              have hcoord : e.val*L+L ≤ I.m*L := by
                simpa only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] using
                  Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.2)
              have hkeep : ∀ x < v0,mem3 x=mem0 x := by
                intro x hx
                exact (hframe3 x (by omega)).trans ((hframe2 x (by omega)).trans (hframe1 x hx))
              have hkeepCost : ∀ x < v1,mem3 x=mem1 x := by
                intro x hx
                exact (hframe3 x (by omega)).trans (hframe2 x hx)
              have hl := table_scalar_frozen hkeep (by omega) (hlower e.val e.2)
              have hc := table_scalar_frozen hkeepCost (by omega) (hcosts e)
              have hu := table_scalar_frozen hframe3 (by omega) (huppers e)
              have hV1 : v1=heap+5*(I.m*L) := by omega
              exact ⟨hl,by simpa only [hv0] using hc,by simpa only [hV1] using hu⟩
            · exact hunit'
          · simp [coefficientTablesContract,zeroTableContract,graphCoefficientTableContract,
              dyadicBlockContract,heapContract,argsSize,startState,Expr.size_bin,Expr.size_load,
              Expr.size_reg,Expr.size_const]
            rw [hcostId]
            omega

end MinCostFlow.IPM.Machine
