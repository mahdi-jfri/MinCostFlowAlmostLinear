module

public import MinCostFlow.IPM.Machine.CoefficientRangeGuard
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Checking exactly the reported coefficient list

Read each name from the caller-owned Detect snapshot and check its two
stored coefficients. Accumulate the acceptance bits without changing
memory. The work is linear in the report size times the scalar width.
Unreported entries are not read by this procedure.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The integer interval tested by the scalar guard. -/
abbrev coefficientsInRange (mem : ℕ → ℕ) (h neg g mx mn l L : ℕ) : Prop :=
  Num.intVal mem neg h L<Num.intVal mem g h L ∧
  Num.intVal mem g h L<Num.intVal mem mx h L ∧
  Num.intVal mem mn h L<Num.intVal mem l h L ∧
  Num.intVal mem l h L<Num.intVal mem mx h L

/-- One reported name, its scalar offset, and its two read-only checks. -/
def coefficientRangeListStep (guard : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 0) (.reg 8))) ;;
  .assign 11 (.bin .mul (.reg 10) (.reg 7)) ;;
  .call 12 guard [.reg 4,.bin .add (.reg 2) (.reg 11),.reg 5,.reg 6,
    .bin .add (.reg 3) (.reg 11),.reg 7] ;;
  .assign 9 (.bin .mul (.reg 9) (.reg 12))

/-- Arguments `[names,count,gradientTable,lengthTable,negativeMaximum,
maximum,minimum,L]`. Return a bit, with no allocation. -/
def coefficientRangeListBody (guard : ℕ) : Stmt :=
  .assign 9 (.const 1) ;;
  forRange 8 (.const 0) (.reg 1) (coefficientRangeListStep guard) ;;
  .ret (.reg 9)

/-- Every reported entry supplies the complete scalar guard precondition.
The list may be empty and need not be sorted. -/
def coefficientRangeListContract (w h : ℕ) : Contract where
  pre args mem := ∃ names count g l neg mx mn L,
    args=[names,count,g,l,neg,mx,mn,L] ∧ 1<2^w ∧
    ∀ i<count,names+i<2^w ∧ mem (names+i)<2^w ∧
      (coefficientRangeGuardContract w h).pre
        [neg,g+mem (names+i)*L,mx,mn,l+mem (names+i)*L,L] mem
  post args mem v mem' := mem'=mem ∧ v≤1 ∧
    (v=1 ↔ ∀ i<args.getD 1 0,coefficientsInRange mem h
      (args.getD 4 0) (args.getD 2 0+mem (args.getD 0 0+i)*args.getD 7 0)
      (args.getD 5 0) (args.getD 6 0)
      (args.getD 3 0+mem (args.getD 0 0+i)*args.getD 7 0) (args.getD 7 0))
  cost args _ := args.getD 1 0*(164*args.getD 7 0+500)+100

/-- The reported-list check contains no random statement. -/
theorem coefficientRangeListBody_noRand (guard : ℕ) :
    (coefficientRangeListBody guard).NoRand := by
  simp [coefficientRangeListBody,coefficientRangeListStep,forRange,forUp,Stmt.NoRand]

private theorem bit_product {x y : ℕ} {P Q : Prop}
    (hx : x≤1) (hy : y≤1) (hP : x=1 ↔ P) (hQ : y=1 ↔ Q) :
    x*y≤1 ∧ (x*y=1 ↔ P ∧ Q) := by
  have hbound : x*y≤1 := by simpa using Nat.mul_le_mul hx hy
  refine ⟨hbound,?_⟩
  rw [← hP,← hQ]
  have hx01 : x=0 ∨ x=1 := by omega
  have hy01 : y=0 ∨ y=1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> simp

/-- The loop preserves all memory, maintains the conjunction of exactly
its processed interval tests, and has the claimed per-entry cost. -/
theorem coefficientRangeList_loop {w h guard names count g l neg mx mn L : ℕ}
    {p : Program} (mem : ℕ → ℕ)
    (hguard : MeetsContract w p guard (coefficientRangeGuardContract w h))
    (hw : 1<2^w) (hc : count<2^w)
    (hwords : ∀ z∈[names,count,g,l,neg,mx,mn,L],z<2^w)
    (hsource : ∀ i<count,names+i<2^w ∧ mem (names+i)<2^w ∧
      (coefficientRangeGuardContract w h).pre
        [neg,g+mem (names+i)*L,mx,mn,l+mem (names+i)*L,L] mem) :
    Triple w p
      (fun st => (∀ j<8,st.regs j=[names,count,g,l,neg,mx,mn,L].getD j 0) ∧
        st.regs 9=1 ∧ st.mem=mem)
      (forRange 8 (.const 0) (.reg 1) (coefficientRangeListStep guard))
      (normalPost fun st => st.mem=mem ∧ st.regs 9≤1 ∧
        (st.regs 9=1 ↔ ∀ i<count,coefficientsInRange mem h neg (g+mem (names+i)*L) mx mn
          (l+mem (names+i)*L) L))
      (fun _ => count*(164*L+500)+50) := by
  let Inv := fun i (st : State) =>
    (∀ j<8,st.regs j=[names,count,g,l,neg,mx,mn,L].getD j 0) ∧
    st.regs 8=i ∧ st.mem=mem ∧ st.regs 9≤1 ∧
    (st.regs 9=1 ↔ ∀ j < i,coefficientsInRange mem h neg (g+mem (names+j)*L) mx mn
      (l+mem (names+j)*L) L)
  have hlp := Triple.forRange_const (w:=w) (p:=p) (r:=8) (lo:=.const 0) (hi:=.reg 1)
    (body:=coefficientRangeListStep guard)
    (P:=fun st => (∀ j<8,st.regs j=[names,count,g,l,neg,mx,mn,L].getD j 0) ∧
      st.regs 9=1 ∧ st.mem=mem) (Inv:=Inv)
    (164*L+460) 0 count (Nat.zero_le _) hw (fun _ => hc)
    (fun st hs => by
      obtain ⟨hfixed,hbit,hm⟩ := hs
      refine ⟨by eval_expr,?_,?_,?_,?_,?_⟩
      · intro j hj
        simpa only [Function.update_of_ne (by omega : j≠8)] using hfixed j hj
      · simp
      · exact hm
      · simpa only [Function.update_of_ne (by decide : 9≠8),hbit] using (by decide : 1≤1)
      · simp [hbit])
    (fun _ _ _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by have h1 := hi.1 1 (by decide); simp only [List.getD_cons_succ,List.getD_cons_zero] at h1; eval_expr)
    (fun i _ hi => by
      intro st ω hst
      obtain ⟨hfixed,h8,hm,hbit,hprior⟩ := hst
      have h0 := hfixed 0 (by decide)
      have h2 := hfixed 2 (by decide)
      have h3 := hfixed 3 (by decide)
      have h4 := hfixed 4 (by decide)
      have h5 := hfixed 5 (by decide)
      have h6 := hfixed 6 (by decide)
      have h7 := hfixed 7 (by decide)
      simp only [List.getD_cons_succ,List.getD_cons_zero] at h0 h2 h3 h4 h5 h6 h7
      obtain ⟨haddr,heword,hpre⟩ := hsource i hi
      have hpreCopy := hpre
      obtain ⟨neg',g',mx',mn',l',L',heq,hgp,hlp⟩ := hpreCopy
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      obtain ⟨_,_,_,_,heq,_,hgEnd,_⟩ := hgp
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
      obtain ⟨_,_,_,_,heq,_,hlEnd,_⟩ := hlp
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
      have hoff : mem (names+i)*L<2^w := by omega
      have hgword : g+mem (names+i)*L<2^w := by omega
      have hlword : l+mem (names+i)*L<2^w := by omega
      have hnword := hwords neg (by simp)
      have hxword := hwords mx (by simp)
      have hmword := hwords mn (by simp)
      have hLword := hwords L (by simp)
      have hname : st.mem (names+i)=mem (names+i) := congrFun hm _
      apply runs_start_le
      unfold coefficientRangeListStep
      refine runs_seq_assign_le (v:=mem (names+i)) (by eval_expr) ?_
      refine runs_seq_assign_le (v:=mem (names+i)*L) (by eval_expr) ?_
      refine runs_seq_call_le hguard
        (vs:=[neg,g+mem (names+i)*L,mx,mn,l+mem (names+i)*L,L])
        (by eval_expr) (by wram_words) (by simpa only [hm] using hpre) ?_
      intro v mem1 pos1 hout
      have hmem1 : mem1=mem := hout.1.trans hm
      have hv : v=if coefficientsInRange mem h neg (g+mem (names+i)*L) mx mn
          (l+mem (names+i)*L) L then 1 else 0 := by simpa only [hm,coefficientsInRange,List.getD_cons_zero,List.getD_cons_succ] using hout.2
      have hvbit : v≤1 := by split_ifs at hv <;> omega
      have hviff : v=1 ↔ coefficientsInRange mem h neg (g+mem (names+i)*L) mx mn
          (l+mem (names+i)*L) L := by
        rw [hv]
        split_ifs with hh
        · exact iff_of_true rfl hh
        · exact iff_of_false (by decide) hh
      have hcombined := bit_product hbit hvbit hprior hviff
      have hprod : st.regs 9*v<2^w := hcombined.1.trans_lt hw
      refine runs_assign_le (v:=st.regs 9*v) (by eval_expr) ?_ ?_
      · change Inv (i+1) _ ∧ _
        refine ⟨⟨?_,?_,hmem1,?_,?_⟩,?_⟩
        · intro j hj
          simpa only [Function.update_of_ne (by omega : j≠8),Function.update_of_ne (by omega : j≠9),
            Function.update_of_ne (by omega : j≠12),Function.update_of_ne (by omega : j≠11),
            Function.update_of_ne (by omega : j≠10)] using hfixed j hj
        · simp
        · simpa using hcombined.1
        · change st.regs 9*v=1 ↔ _
          rw [hcombined.2]
          constructor
          · rintro ⟨hprev,hnow⟩ j hj
            by_cases hji : j < i
            · exact hprev j hji
            · have : j=i := by omega
              simpa only [this] using hnow
          · intro hall
            exact ⟨fun j hj => hall j (by omega),hall i (by omega)⟩
        · simpa using h8
      · simp only [coefficientRangeGuardContract,List.getD_cons_zero,List.getD_cons_succ,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_load]
        omega)
  refine hlp.conseq (fun _ hs => hs) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_reg,Expr.size_const,Nat.mul_add]
    omega

/-- The complete actual list entry checks exactly the reported names,
with unchanged memory and no graph-size factor in its operation bound. -/
theorem coefficientRangeList_meetsContract {w h entry guard : ℕ} {p : Program}
    (hguard : MeetsContract w p guard (coefficientRangeGuardContract w h))
    (hp : p.procs[entry]?=some (coefficientRangeListBody guard)) :
    MeetsContract w p entry (coefficientRangeListContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨names,count,g,l,neg,mx,mn,L,rfl,hw,hsource⟩ := hpre
  have hc := hwords count (by simp)
  have hloop := coefficientRangeList_loop mem hguard hw hc hwords hsource
  apply runs_start_le
  unfold coefficientRangeListBody
  wram_step
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨?_,by simp, rfl⟩
    intro j hj
    simp only [Function.update_of_ne (by omega : j≠9),startState]
  · intro st ⟨hm,hbit,haccept⟩
    have hvalue : st.regs 9<2^w := hbit.trans_lt hw
    refine runs_ret_le (v:=st.regs 9) (by eval_expr) ?_ ?_
    · exact ⟨hm,hbit,haccept⟩
    · simp only [coefficientRangeListContract,List.getD_cons_zero,List.getD_cons_succ,
        Expr.size_reg,Expr.size_const]
      omega

end MinCostFlow.IPM.Machine
