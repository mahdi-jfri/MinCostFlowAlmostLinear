module

public import MinCostFlow.IPM.Machine.SolverGuardTables
public import MinCostFlow.IPM.Machine.SolverInitialize
public import MinCostFlow.IPM.Machine.SolverAugmentedBounds
public import MinCostFlow.IPM.Machine.TargetEpochStatic
public import MinCostFlow.IPM.Machine.NamedGraphProgram
public import MinCostFlow.IPM.Machine.CoefficientTablePrecision
import MinCostFlow.IPM.Machine.NamedGraphLayout
import Mathlib.Tactic
import WordRAM.Tactic
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Static inputs for a bounded instance's repeated IPM tests

Each test uses the same row graph, named graph, midpoint table and
vectors of original coefficients. Only the target changes. This file
describes the exact addresses of the shared fixed-point inputs.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The first fresh address after the named graph. -/
def solverCoefficientBase (I : Instance) (heap : ℕ) : ℕ := heap+2+I.n+3*I.m

/-- The first fresh address after the immutable coefficient blocks. -/
def solverGuardBase (I : Instance) (L heap : ℕ) : ℕ :=
  solverCoefficientBase I heap+(9*I.m+1)*L

/-- The setup's exact fresh allocation, including both graph views'
shared coefficient tables and the five guard blocks. -/
def solverSearchSetupSpace (I : Instance) (L : ℕ) : ℕ :=
  2+I.n+3*I.m+(9*I.m+1)*L+5*L

/-- Pointers used by the first state of the target search. The two graph
pointers retain the distinct row and name formats. -/
def solverEpochLayout (I : Instance) (L E graph alpha heap : ℕ) : EpochLayout :=
  let c := solverCoefficientBase I heap
  let g := solverGuardBase I L heap
  { handle := 0, names := 0, base := 0, lower := c, upper := c+5*(I.m*L), flow := 0,
    cost := c+I.m*L, residual := 0, alpha := alpha, one := c+9*(I.m*L),
    slackMin := g, slackMax := g+L, exponent := E, lengths := 0, gradient := 0,
    graph := graph, initGraph := heap, request := g+4*L,
    gradientMin := g+3*L, gradientMax := g+L, lengthMin := g, sourceEnd := 0, tableEnd := 0 }

/-- Arguments `[graph,R,L,P,k,j,heap]` at the selected precision. -/
def solverSearchSetupBody (named coefficients guards : ℕ) : Stmt :=
  .call 7 named [.reg 0,.reg 6] ;;
  .call 8 coefficients [.reg 0,.reg 2,.reg 3,.reg 7] ;;
  .call 9 guards [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 8] ;;
  .ret (.reg 9)

/-- Exact values present at the shared addresses after setup. -/
def SolverSearchTablesAt (I : Instance) (V k g a h : ℕ) (mem : ℕ → ℕ) : Prop :=
  let L := ipmLimbs I.m V
  let P := ipmPrecision I.m V
  let E := ipmRangeExponent I.m V
  let old := solverEpochLayout I L E g a h
  ZeroLowerAt mem g I ∧ GraphAt mem h (namedInstance I) ∧
    (∀ e : Fin I.m, ScalarAt mem (old.lower+e.val*L) 4 L P (I.edge e).lower ∧
      ScalarAt mem (old.cost+e.val*L) 4 L 0 (I.edge e).cost ∧
      ScalarAt mem (old.upper+e.val*L) 4 L P (I.edge e).upper) ∧
    ScalarAt mem old.one 4 L P 1 ∧
    SolverGuardTablesAt mem old.slackMin E L P k (Num.IPM.alphaExponent I.m V)

theorem solverSearchSetupBody_noRand (named coefficients guards : ℕ) :
    (solverSearchSetupBody named coefficients guards).NoRand := by
  simp [solverSearchSetupBody,Stmt.NoRand]

/-- The complete immutable preparation from the augmented row graph. -/
def solverSearchSetupContract (w : ℕ) (I : Instance) (V k : ℕ) : Contract :=
  let L := ipmLimbs I.m V
  let P := ipmPrecision I.m V
  let E := ipmRangeExponent I.m V
  let j := Num.IPM.alphaExponent I.m V
  let C := heapContract w
    (fun args mem => ∃ g h,args=[g,E,L,P,k,j,h] ∧ I.IsValid ∧ 0 < I.m ∧
      0 < V ∧ 2≤I.m*V ∧ k≤slackRangeExponent I.m V ∧ ipmParameterWordBits I.m V≤w ∧
      ZeroLowerAt mem g I ∧ g+(zeroLowerWords I).length≤h ∧
      (∀ x∈zeroLowerWords I,x<2^w) ∧ NumbersBounded I V)
    (fun args _ mem => SolverSearchTablesAt I V k (args.getD 0 0) 0 (heapArg args) mem)
    (fun _ _ => 30*I.n+I.m*(600*L+1900)+36*L+1800)
    (fun _ _ => solverSearchSetupSpace I L)
  {C with post := fun args mem out final => C.post args mem out final ∧
    out=heapArg args+solverSearchSetupSpace I L }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 420000 in
/-- The row graph is copied into a named graph. The remaining calls
materialize every scalar and array used by the static part of a test. -/
theorem solverSearchSetup_meetsContract {w entry named coefficients guards : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverSearchSetupBody named coefficients guards))
    (hn : p.HasAt named (namedGraphModule named))
    (hc : p.HasAt coefficients (coefficientTablesModule coefficients 4))
    (hg : MeetsContract w p guards (solverGuardTablesContract w))
    (I : Instance) (V k : ℕ) : MeetsContract w p entry (solverSearchSetupContract w I V k) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hWords hPre
  obtain ⟨⟨g,h,rfl,hI,hm,hV,hSize,hk,hw,hGraph,hGraphEnd,hGraphWords,hNums⟩,hZero,hSpace⟩ := hPre
  let L := ipmLimbs I.m V
  let P := ipmPrecision I.m V
  let E := ipmRangeExponent I.m V
  let j := Num.IPM.alphaExponent I.m V
  let b := solverCoefficientBase I h
  let r := solverGuardBase I L h
  let old := solverEpochLayout I L E g 0 h
  have hW := ipm_parameter_words_fit I.m V hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hNamed := namedGraph_meetsContract (by omega : 5<2^w) I hn
  have hCoeff := coefficientTables_meetsContract (by decide : 0<4)
    (by have := hW.1; omega : 2*4+2≤w) rfl h16 I hc
  change ZeroFrom mem h at hZero
  change h+solverSearchSetupSpace I L<2^w at hSpace
  have hbr : r=b+(9*I.m+1)*L := rfl
  have hb : b=h+2+I.n+3*I.m := rfl
  have hCombined : h+solverSearchSetupSpace I L=r+5*L := by
    simp only [solverSearchSetupSpace,hbr,hb]
    omega
  rw [hCombined] at hSpace
  have hHbr : h≤b := by omega
  have hbR : b≤r := by omega
  have hbW : b<2^w := by omega
  have hrW : r<2^w := by omega
  have hhW : h<2^w := by omega
  have hgW : g<2^w := hWords _ (by simp)
  have hLW : L<2^w := hW.2.1
  have hPW : P<2^w := hW.2.2.1
  have hEW : E<2^w := hW.2.2.2.1
  have hkW : k<2^w := hWords _ (by simp)
  have hjW : j<2^w := hWords _ (by simp [j])
  apply runs_start_le
  unfold solverSearchSetupBody
  refine runs_seq_call_le hNamed (vs:=[g,h]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨g,h,rfl,hI,hGraph.2.2,hGraphEnd,hGraphWords⟩,hZero,
      by change h+(2+I.n+3*I.m)<2^w; omega⟩
  intro mid mem₁ pos₁ o₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hNamedAt⟩,hEnd₁⟩ := o₁
  change mid=h+(2+I.n+3*I.m) at hEnd₁
  have he₁ : mid=b := by omega
  clear hEnd₁
  subst mid
  change ∀ x<h,mem₁ x=mem x at hFrame₁
  change GraphAt mem₁ h (namedInstance I) at hNamedAt
  have hRow₁ : ZeroLowerAt mem₁ g I := ⟨hGraph.1,hGraph.2.1,
    hGraph.2.2.of_agree_below hGraphEnd hFrame₁⟩
  refine runs_seq_call_le hCoeff (vs:=[g,L,P,b]) (by eval_expr) (by wram_words) ?_ ?_
  · exact coefficientTables_pre_of_chosen_precision I V hI hm hV hNums hRow₁
      (hGraphEnd.trans hHbr) hGraphWords hZero₁ hrW
  intro mid mem₂ pos₂ o₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hCoeffAt,hUnit⟩,hEnd₂⟩ := o₂
  change mid=r at hEnd₂
  subst mid
  change ∀ x<b,mem₂ x=mem₁ x at hFrame₂
  refine runs_seq_call_le hg (vs:=[E,L,P,k,j,r]) (by eval_expr) (by wram_words)
    ⟨⟨I.m,V,k,r,rfl,hSize,hk,hw⟩,hZero₂,hSpace⟩ ?_
  intro out final newPos o₃
  obtain ⟨⟨_,_,hFrame₃,hZero₃,hGuardAt⟩,hEnd₃⟩ := o₃
  change out=r+5*L at hEnd₃
  change ∀ x<r,final x=mem₂ x at hFrame₃
  have hOutW : out<2^w := hEnd₃ ▸ hSpace
  have hFrame : ∀ x<h,final x=mem x := fun x hx =>
    (hFrame₃ x (by omega)).trans ((hFrame₂ x (by omega)).trans (hFrame₁ x hx))
  have hNamedEnd : h+(graphWords (namedInstance I)).length≤b := by
    rw [graphWords_namedInstance_length]
    omega
  have hNamedFinal : GraphAt final h (namedInstance I) :=
    (hNamedAt.of_agree_below hNamedEnd hFrame₂).of_agree_below (hNamedEnd.trans hbR) hFrame₃
  have freeze (a prec : ℕ) (x : ℝ) (hEnd : a+L≤r) (hAt : ScalarAt mem₂ a 4 L prec x) :
      ScalarAt final a 4 L prec x :=
    ⟨Num.IPM.valid_frozen hFrame₃ hEnd hAt.1,(Num.IPM.fixVal_frozen hFrame₃ hEnd).trans hAt.2⟩
  have hML : (9*I.m+1)*L=9*(I.m*L)+L := by ring
  have hCosts : SolverSearchTablesAt I V k g 0 h final := by
    refine ⟨⟨hGraph.1,hGraph.2.1,hGraph.2.2.of_agree_below hGraphEnd hFrame⟩,hNamedFinal,
      ?_,?_,hGuardAt⟩
    · intro e
      have he := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
      rw [Nat.succ_mul] at he
      have hLower : (I.edge e).lower=0 := (hGraph.1 e).1
      change ScalarAt final (b+e.val*L) 4 L P ((I.edge e).lower:ℝ) ∧
        ScalarAt final (b+I.m*L+e.val*L) 4 L 0 ((I.edge e).cost:ℝ) ∧
        ScalarAt final (b+5*(I.m*L)+e.val*L) 4 L P ((I.edge e).upper:ℝ)
      rw [hLower,Int.cast_zero]
      exact ⟨freeze _ _ _ (by omega) (hCoeffAt e).1,
        freeze _ _ _ (by omega) (hCoeffAt e).2.1,
        freeze _ _ _ (by omega) (hCoeffAt e).2.2⟩
    · exact freeze (b+9*(I.m*L)) _ _ (by omega) hUnit
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · have hOut : out=h+solverSearchSetupSpace I L := hEnd₃.trans hCombined.symm
    exact ⟨⟨show h≤out by omega,hOut.le,hFrame,hZero₃,hCosts⟩,hOut⟩
  · simp only [namedGraphContract,coefficientTablesContract,solverGuardTablesContract,solverSearchSetupContract,
      heapContract, argsSize_cons,argsSize_nil,Expr.size_reg,List.getD_cons_zero,List.getD_cons_succ]
    change _ ≤ 30*I.n+I.m*(600*L+1900)+36*L+1800
    have he : I.m*(600*L+1900)=I.m*(600*L+1800)+100*I.m := by ring
    omega

/-- Exact values present at the shared addresses after setup. -/
def SolverQualitySearchTablesAt (I : Instance) (V k g a h : ℕ) (mem : ℕ → ℕ) : Prop :=
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let E := ipmQualityRangeExponent I.m V k
  let old := solverEpochLayout I L E g a h
  ZeroLowerAt mem g I ∧ GraphAt mem h (namedInstance I) ∧
    (∀ e : Fin I.m, ScalarAt mem (old.lower+e.val*L) 4 L P (I.edge e).lower ∧
      ScalarAt mem (old.cost+e.val*L) 4 L 0 (I.edge e).cost ∧
      ScalarAt mem (old.upper+e.val*L) 4 L P (I.edge e).upper) ∧
    ScalarAt mem old.one 4 L P 1 ∧
    SolverGuardTablesAt mem old.slackMin E L P k (Num.IPM.alphaExponent I.m V)

/-- The complete immutable preparation from the augmented row graph. -/
def solverQualitySearchSetupContract (w : ℕ) (I : Instance) (V k : ℕ) : Contract :=
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let E := ipmQualityRangeExponent I.m V k
  let j := Num.IPM.alphaExponent I.m V
  let C := heapContract w
    (fun args mem => ∃ g h,args=[g,E,L,P,k,j,h] ∧ I.IsValid ∧ 0 < I.m ∧
      0 < V ∧ 2≤I.m*V ∧ ipmQualityParameterWordBits I.m V k≤w ∧
      ZeroLowerAt mem g I ∧ g+(zeroLowerWords I).length≤h ∧
      (∀ x∈zeroLowerWords I,x<2^w) ∧ NumbersBounded I V)
    (fun args _ mem => SolverQualitySearchTablesAt I V k (args.getD 0 0) 0 (heapArg args) mem)
    (fun _ _ => 30*I.n+I.m*(600*L+1900)+36*L+1800)
    (fun _ _ => solverSearchSetupSpace I L)
  {C with post := fun args mem out final => C.post args mem out final ∧
    out=heapArg args+solverSearchSetupSpace I L }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 420000 in
/-- The row graph is copied into a named graph. The remaining calls
materialize every scalar and array used by the static part of a test. -/
theorem solverQualitySearchSetup_meetsContract {w entry named coefficients guards : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverSearchSetupBody named coefficients guards))
    (hn : p.HasAt named (namedGraphModule named))
    (hc : p.HasAt coefficients (coefficientTablesModule coefficients 4))
    (hg : MeetsContract w p guards (solverQualityGuardTablesContract w))
    (I : Instance) (V k : ℕ) : MeetsContract w p entry (solverQualitySearchSetupContract w I V k) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hWords hPre
  obtain ⟨⟨g,h,rfl,hI,hm,hV,hSize,hw,hGraph,hGraphEnd,hGraphWords,hNums⟩,hZero,hSpace⟩ := hPre
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let E := ipmQualityRangeExponent I.m V k
  let j := Num.IPM.alphaExponent I.m V
  let b := solverCoefficientBase I h
  let r := solverGuardBase I L h
  let old := solverEpochLayout I L E g 0 h
  have hW := ipm_quality_parameter_words_fit I.m V k hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hNamed := namedGraph_meetsContract (by omega : 5<2^w) I hn
  have hCoeff := coefficientTables_meetsContract (by decide : 0<4)
    (by have := hW.1; omega : 2*4+2≤w) rfl h16 I hc
  change ZeroFrom mem h at hZero
  change h+solverSearchSetupSpace I L<2^w at hSpace
  have hbr : r=b+(9*I.m+1)*L := rfl
  have hb : b=h+2+I.n+3*I.m := rfl
  have hCombined : h+solverSearchSetupSpace I L=r+5*L := by
    simp only [solverSearchSetupSpace,hbr,hb]
    omega
  rw [hCombined] at hSpace
  have hHbr : h≤b := by omega
  have hbR : b≤r := by omega
  have hbW : b<2^w := by omega
  have hrW : r<2^w := by omega
  have hhW : h<2^w := by omega
  have hgW : g<2^w := hWords _ (by simp)
  have hLW : L<2^w := hW.2.1
  have hPW : P<2^w := hW.2.2.1
  have hEW : E<2^w := hW.2.2.2.1
  have hkW : k<2^w := hWords _ (by simp)
  have hjW : j<2^w := hWords _ (by simp [j])
  apply runs_start_le
  unfold solverSearchSetupBody
  refine runs_seq_call_le hNamed (vs:=[g,h]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨g,h,rfl,hI,hGraph.2.2,hGraphEnd,hGraphWords⟩,hZero,
      by change h+(2+I.n+3*I.m)<2^w; omega⟩
  intro mid mem₁ pos₁ o₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hNamedAt⟩,hEnd₁⟩ := o₁
  change mid=h+(2+I.n+3*I.m) at hEnd₁
  have he₁ : mid=b := by omega
  clear hEnd₁
  subst mid
  change ∀ x<h,mem₁ x=mem x at hFrame₁
  change GraphAt mem₁ h (namedInstance I) at hNamedAt
  have hRow₁ : ZeroLowerAt mem₁ g I := ⟨hGraph.1,hGraph.2.1,
    hGraph.2.2.of_agree_below hGraphEnd hFrame₁⟩
  refine runs_seq_call_le hCoeff (vs:=[g,L,P,b]) (by eval_expr) (by wram_words) ?_ ?_
  · exact coefficientTables_pre_of_widened_precision I V k hI hm hV hNums hRow₁
      (hGraphEnd.trans hHbr) hGraphWords hZero₁ hrW
  intro mid mem₂ pos₂ o₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hCoeffAt,hUnit⟩,hEnd₂⟩ := o₂
  change mid=r at hEnd₂
  subst mid
  change ∀ x<b,mem₂ x=mem₁ x at hFrame₂
  refine runs_seq_call_le hg (vs:=[E,L,P,k,j,r]) (by eval_expr) (by wram_words)
    ⟨⟨I.m,V,k,r,rfl,hSize,hw⟩,hZero₂,hSpace⟩ ?_
  intro out final newPos o₃
  obtain ⟨⟨_,_,hFrame₃,hZero₃,hGuardAt⟩,hEnd₃⟩ := o₃
  change out=r+5*L at hEnd₃
  change ∀ x<r,final x=mem₂ x at hFrame₃
  have hOutW : out<2^w := hEnd₃ ▸ hSpace
  have hFrame : ∀ x<h,final x=mem x := fun x hx =>
    (hFrame₃ x (by omega)).trans ((hFrame₂ x (by omega)).trans (hFrame₁ x hx))
  have hNamedEnd : h+(graphWords (namedInstance I)).length≤b := by
    rw [graphWords_namedInstance_length]
    omega
  have hNamedFinal : GraphAt final h (namedInstance I) :=
    (hNamedAt.of_agree_below hNamedEnd hFrame₂).of_agree_below (hNamedEnd.trans hbR) hFrame₃
  have freeze (a prec : ℕ) (x : ℝ) (hEnd : a+L≤r) (hAt : ScalarAt mem₂ a 4 L prec x) :
      ScalarAt final a 4 L prec x :=
    ⟨Num.IPM.valid_frozen hFrame₃ hEnd hAt.1,(Num.IPM.fixVal_frozen hFrame₃ hEnd).trans hAt.2⟩
  have hML : (9*I.m+1)*L=9*(I.m*L)+L := by ring
  have hCosts : SolverQualitySearchTablesAt I V k g 0 h final := by
    refine ⟨⟨hGraph.1,hGraph.2.1,hGraph.2.2.of_agree_below hGraphEnd hFrame⟩,hNamedFinal,
      ?_,?_,hGuardAt⟩
    · intro e
      have he := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
      rw [Nat.succ_mul] at he
      have hLower : (I.edge e).lower=0 := (hGraph.1 e).1
      change ScalarAt final (b+e.val*L) 4 L P ((I.edge e).lower:ℝ) ∧
        ScalarAt final (b+I.m*L+e.val*L) 4 L 0 ((I.edge e).cost:ℝ) ∧
        ScalarAt final (b+5*(I.m*L)+e.val*L) 4 L P ((I.edge e).upper:ℝ)
      rw [hLower,Int.cast_zero]
      exact ⟨freeze _ _ _ (by omega) (hCoeffAt e).1,
        freeze _ _ _ (by omega) (hCoeffAt e).2.1,
        freeze _ _ _ (by omega) (hCoeffAt e).2.2⟩
    · exact freeze (b+9*(I.m*L)) _ _ (by omega) hUnit
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · have hOut : out=h+solverSearchSetupSpace I L := hEnd₃.trans hCombined.symm
    exact ⟨⟨show h≤out by omega,hOut.le,hFrame,hZero₃,hCosts⟩,hOut⟩
  · simp only [namedGraphContract,coefficientTablesContract,solverQualityGuardTablesContract,solverQualitySearchSetupContract,
      heapContract, argsSize_cons,argsSize_nil,Expr.size_reg,List.getD_cons_zero,List.getD_cons_succ]
    change _ ≤ 30*I.n+I.m*(600*L+1900)+36*L+1800
    have he : I.m*(600*L+1900)=I.m*(600*L+1800)+100*I.m := by ring
    omega

end MinCostFlow.IPM.Machine
