module

public import MinCostFlow.IPM.Machine.GraphCoefficientRead
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Loading a target test's actual graph coefficients

The wrapper reads the fixed graph's edge count and selects either its
cost sign/magnitude fields or its unsigned upper-capacity field. The
verified strided loader then produces the dense blocks expected by the
numerical gradient and length procedures. The postcondition names the
actual instance coefficients, not an unrelated ghost input array.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[graph,L,P,heap]`. Signed mode loads costs, unsigned
mode loads upper capacities at the supplied precision. -/
def graphCoefficientTableBody (load : ℕ) (signed : Bool) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 load [.bin .add (.reg 0) (.const (if signed then 5 else 3)),
    .reg 4,.reg 1,.reg 2,.reg 3] ;;
  .ret (.reg 5)

/-- Header reader and exact signed/unsigned coefficient-table loader. -/
def graphCoefficientTableModule (b h : ℕ) (signed : Bool) : List Stmt :=
  [graphCoefficientTableBody (b+1) signed] ++ fixedIntegerVectorModule (b+1) h signed

/-- Every loaded coefficient and its shifted numerator must fit. These
are supplied by the proved precision ranges in the target-test caller. -/
def graphCoefficientTableContract (w h : ℕ) (I : Instance) (signed : Bool) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L P heap,args=[a,L,P,heap] ∧ I.IsValid ∧ 0 < I.m ∧
      ZeroLowerAt mem a I ∧ a+(zeroLowerWords I).length ≤ heap ∧
      (∀ x ∈ zeroLowerWords I,x < 2^w) ∧ ∀ e : Fin I.m,
        let n := if signed then (I.edge e).cost else (I.edge e).upper
        Num.Fits h L n ∧ Num.Fits h L (n*(2:ℤ)^P))
    (fun args _ mem' => ∀ e : Fin I.m,ScalarAt mem'
      (heapArg args+e.val*args.getD 1 0) h (args.getD 1 0) (args.getD 2 0)
      ((if signed then (I.edge e).cost else (I.edge e).upper:ℤ):ℝ))
    (fun args _ => I.m*(300*args.getD 1 0+900)+200)
    (fun args _ => 4*(I.m*args.getD 1 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+4*(I.m*args.getD 1 0)}

/-- Graph coefficient-table loading is deterministic. -/
theorem graphCoefficientTableModule_noRand (b h : ℕ) (signed : Bool) :
    ∀ body ∈ graphCoefficientTableModule b h signed,body.NoRand := by
  intro body hb
  simp only [graphCoefficientTableModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · cases signed <;> simp [graphCoefficientTableBody,Stmt.NoRand]
  · exact fixedIntegerVectorModule_noRand _ _ _ _ hb

/-- The actual graph's costs or capacities are loaded exactly into the
numeric table, with all source lookup, framing and scratch costs proved. -/
theorem graphCoefficientTable_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hconst : 6 < 2^w) (I : Instance) (signed : Bool)
    (hp : p.HasAt b (graphCoefficientTableModule b h signed)) :
    MeetsContract w p b (graphCoefficientTableContract w h I signed) := by
  have hload : p.HasAt (b+1) (fixedIntegerVectorModule (b+1) h signed) := Num.hasAt_append_right hp
  have hloadSpec := fixedIntegerVector_meetsContract signed hh hw (by omega : 5 < 2^w) hload
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,L,P,heap,rfl,hI,hm,hat,hend,hinput,hfits⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+4*(I.m*L) < 2^w at hspace
  have hlen := zeroLowerWords_length I hI
  have hheader := zeroLower_header_at I hI mem a hat.2.2
  have ha : a < 2^w := hwords _ (by simp)
  have hL : L < 2^w := hwords _ (by simp)
  have hP : P < 2^w := hwords _ (by simp)
  have hhptr : heap < 2^w := hwords _ (by simp)
  have hend' : a+(2+5*I.m) ≤ heap := by simpa only [hlen] using hend
  have hmemBound (j : ℕ) (hj : j < 2+5*I.m) : mem (a+j) < 2^w :=
    hat.2.2.words_lt hinput (by rw [hlen]; exact hj)
  have hmword : I.m < 2^w := by
    rw [← hheader.2]
    exact hmemBound 1 (by omega)
  have hsource : ∀ i < I.m,a+(if signed then 5 else 3)+1+5*i < heap ∧
      (if signed then mem (a+(if signed then 5 else 3)+5*i) else 0) < 2^w ∧
      mem (a+(if signed then 5 else 3)+1+5*i) < 2^w ∧
      [if signed then mem (a+(if signed then 5 else 3)+5*i) else 0,
        mem (a+(if signed then 5 else 3)+1+5*i)] =
        encodeInt (stridedInteger signed mem (a+(if signed then 5 else 3)) i) ∧
      Num.Fits h L (stridedInteger signed mem (a+(if signed then 5 else 3)) i) ∧
      Num.Fits h L (stridedInteger signed mem (a+(if signed then 5 else 3)) i*(2:ℤ)^P) := by
    intro i hi
    let e : Fin I.m := ⟨i,hi⟩
    cases signed
    · simp only [Bool.false_eq_true,↓reduceIte]
      have hvalue := zeroLower_strided_capacity I hI mem a hat e
      change stridedInteger false mem (a+3) i=(I.edge e).upper at hvalue
      refine ⟨by omega,by omega,?_,?_,?_,?_⟩
      · rw [show a+3+1+5*i=a+(4+5*i) by omega]
        exact hmemBound _ (by omega)
      · unfold stridedInteger
        simp [Num.decodeIntWords,encodeInt]
      · rw [hvalue]
        exact (hfits e).1
      · rw [hvalue]
        exact (hfits e).2
    · simp only [↓reduceIte]
      have hvalue := zeroLower_strided_cost I hI mem a hat.2.2 e
      change stridedInteger true mem (a+5) i=(I.edge e).cost at hvalue
      refine ⟨by omega,?_,?_,?_,?_,?_⟩
      · rw [show a+5+5*i=a+(5+5*i) by omega]
        exact hmemBound _ (by omega)
      · rw [show a+5+1+5*i=a+(6+5*i) by omega]
        exact hmemBound _ (by omega)
      · rw [hvalue]
        simpa only [show a+5+1+5*i=a+6+5*i by omega] using zeroLower_cost_at I hI mem a hat.2.2 e
      · rw [hvalue]
        exact (hfits e).1
      · rw [hvalue]
        exact (hfits e).2
  have hsourcePtr : a+(if signed then 5 else 3) < 2^w := by cases signed <;> simp <;> omega
  have hoff : (if signed then 5 else 3) < 2^w := by cases signed <;> simp <;> omega
  apply runs_start_le
  unfold graphCoefficientTableBody
  wram_step
  refine runs_seq_call_le hloadSpec (vs:=[a+(if signed then 5 else 3),I.m,L,P,heap]) ?_ ?_ ?_ ?_
  · cases signed <;> simp only [Bool.false_eq_true,↓reduceIte] <;> eval_expr
  · wram_words
  · exact ⟨⟨_,_,_,_,_,rfl,hsource⟩,hzero,hspace⟩
  · intro v mem1 pos1 hp1
    obtain ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩ := hp1
    change v=heap+4*(I.m*L) at hv
    have hvw : v < 2^w := hv ▸ hspace
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · refine ⟨⟨hlo,hhi,hframe,hfresh,?_⟩,hv⟩
      intro e
      have he := hout e.val e.2
      change ScalarAt mem1 (heap+e.val*L) h L P
        (stridedInteger signed mem (a+(if signed then 5 else 3)) e.val:ℝ) at he
      change ScalarAt mem1 (heap+e.val*L) h L P
        ((if signed then (I.edge e).cost else (I.edge e).upper:ℤ):ℝ)
      cases signed
      · simpa only [Bool.false_eq_true,↓reduceIte,zeroLower_strided_capacity I hI mem a hat e] using he
      · simpa only [↓reduceIte,zeroLower_strided_cost I hI mem a hat.2.2 e] using he
    · simp only [graphCoefficientTableContract,fixedIntegerVectorContract,heapContract,
        Expr.size_load,Expr.size_bin,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil,
        List.getD_cons_zero,List.getD_cons_succ]
      omega

end MinCostFlow.IPM.Machine
