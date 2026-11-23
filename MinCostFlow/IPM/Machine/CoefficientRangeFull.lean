module

public import MinCostFlow.IPM.Machine.CoefficientRangeList
public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.NamedInstance
import MinCostFlow.IPM.Machine.ReportedTableLayout
import WordRAM.Tactic
import Mathlib.Tactic.Positivity

/-!
# Checking all freshly computed coefficient entries before Init

Scan indices `0, ..., count - 1` directly against the signed gradient
and positive length range limits without allocating a name list. The
procedure is read-only and leaves the fresh heap untouched, so an
accepted scan certifies `LengthsWithin` before calling min-ratio Init.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- One edge index, its scalar offset, and its two read-only checks. -/
def coefficientRangeFullStep (guard : ℕ) : Stmt :=
  .assign 9 (.bin .mul (.reg 7) (.reg 6)) ;;
  .call 10 guard [.reg 3,.bin .add (.reg 1) (.reg 9),.reg 4,.reg 5,
    .bin .add (.reg 2) (.reg 9),.reg 6] ;;
  .assign 8 (.bin .mul (.reg 8) (.reg 10))

/-- Arguments `[count,gradientTable,lengthTable,negativeMaximum,maximum,minimum,L]`.
Return a bit, with no allocation. -/
def coefficientRangeFullBody (guard : ℕ) : Stmt :=
  .assign 8 (.const 1) ;;
  forRange 7 (.const 0) (.reg 0) (coefficientRangeFullStep guard) ;;
  .ret (.reg 8)

/-- Every index `i < count` supplies the complete scalar guard precondition. -/
def coefficientRangeFullContract (w h : ℕ) : Contract where
  pre args mem := ∃ count g l neg mx mn L,
    args=[count,g,l,neg,mx,mn,L] ∧ 1<2^w ∧
    ∀ i<count,
      (coefficientRangeGuardContract w h).pre [neg,g+i*L,mx,mn,l+i*L,L] mem
  post args mem v mem' := mem'=mem ∧ v≤1 ∧
    (v=1 ↔ ∀ i<args.getD 0 0,coefficientsInRange mem h
      (args.getD 3 0) (args.getD 1 0+i*args.getD 6 0)
      (args.getD 4 0) (args.getD 5 0)
      (args.getD 2 0+i*args.getD 6 0) (args.getD 6 0))
  cost args _ := args.getD 0 0*(164*args.getD 6 0+500)+100

/-- The direct full-array check contains no random statement. -/
theorem coefficientRangeFullBody_noRand (guard : ℕ) :
    (coefficientRangeFullBody guard).NoRand := by
  simp [coefficientRangeFullBody,coefficientRangeFullStep,forRange,forUp,Stmt.NoRand]

private theorem full_bit_product {x y : ℕ} {P Q : Prop}
    (hx : x≤1) (hy : y≤1) (hP : x=1 ↔ P) (hQ : y=1 ↔ Q) :
    x*y≤1 ∧ (x*y=1 ↔ P ∧ Q) := by
  have hbound : x*y≤1 := by simpa using Nat.mul_le_mul hx hy
  refine ⟨hbound,?_⟩
  rw [← hP,← hQ]
  have hx01 : x=0 ∨ x=1 := by omega
  have hy01 : y=0 ∨ y=1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> simp

/-- The loop preserves all memory, maintains the conjunction of all
processed interval tests, and has the claimed per-entry cost. -/
theorem coefficientRangeFull_loop {w h guard count g l neg mx mn L : ℕ}
    {p : Program} (mem : ℕ → ℕ)
    (hguard : MeetsContract w p guard (coefficientRangeGuardContract w h))
    (hw : 1<2^w) (hc : count<2^w)
    (hwords : ∀ z∈[count,g,l,neg,mx,mn,L],z<2^w)
    (hsource : ∀ i<count,
      (coefficientRangeGuardContract w h).pre [neg,g+i*L,mx,mn,l+i*L,L] mem) :
    Triple w p
      (fun st => (∀ j<7,st.regs j=[count,g,l,neg,mx,mn,L].getD j 0) ∧
        st.regs 8=1 ∧ st.mem=mem)
      (forRange 7 (.const 0) (.reg 0) (coefficientRangeFullStep guard))
      (normalPost fun st => st.mem=mem ∧ st.regs 8≤1 ∧
        (st.regs 8=1 ↔ ∀ i<count,coefficientsInRange mem h neg (g+i*L) mx mn (l+i*L) L))
      (fun _ => count*(164*L+500)+50) := by
  let Inv := fun i (st : State) =>
    (∀ j<7,st.regs j=[count,g,l,neg,mx,mn,L].getD j 0) ∧
    st.regs 7=i ∧ st.mem=mem ∧ st.regs 8≤1 ∧
    (st.regs 8=1 ↔ ∀ j < i,coefficientsInRange mem h neg (g+j*L) mx mn (l+j*L) L)
  have hbody : ∀ i, 0 ≤ i → i < count →
      Triple w p (Inv i) (coefficientRangeFullStep guard)
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧ st₁.regs 7 = i)
        (fun _ => 164 * L + 460) := by
    intro i _ hi st ω hst
    obtain ⟨hfixed,h7,hm,hbit,hprior⟩ := hst
    have h1 := hfixed 1 (by decide)
    have h2 := hfixed 2 (by decide)
    have h3 := hfixed 3 (by decide)
    have h4 := hfixed 4 (by decide)
    have h5 := hfixed 5 (by decide)
    have h6 := hfixed 6 (by decide)
    simp only [List.getD_cons_succ,List.getD_cons_zero] at h1 h2 h3 h4 h5 h6
    have hpre := hsource i hi
    have hpreCopy := hpre
    obtain ⟨neg',g',mx',mn',l',L',heq,hgp,hlp'⟩ := hpreCopy
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    obtain ⟨_,_,_,_,heq,_,hgEnd,_⟩ := hgp
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
    obtain ⟨_,_,_,_,heq,_,hlEnd,_⟩ := hlp'
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
    have hoff : i*L<2^w := by omega
    have hgword : g+i*L<2^w := by omega
    have hlword : l+i*L<2^w := by omega
    have hnword := hwords neg (by simp)
    have hxword := hwords mx (by simp)
    have hmword := hwords mn (by simp)
    have hLword := hwords L (by simp)
    apply runs_start_le
    unfold coefficientRangeFullStep
    refine runs_seq_assign_le (v:=i*L) (by eval_expr) ?_
    refine runs_seq_call_le hguard
      (vs:=[neg,g+i*L,mx,mn,l+i*L,L])
      (by eval_expr) (by wram_words) (by simpa only [hm] using hpre) ?_
    intro v mem1 pos1 hout
    have hmem1 : mem1=mem := hout.1.trans hm
    have hv : v=if coefficientsInRange mem h neg (g+i*L) mx mn (l+i*L) L then 1 else 0 := by
      simpa only [hm,coefficientsInRange,List.getD_cons_zero,List.getD_cons_succ] using hout.2
    have hvbit : v≤1 := by split_ifs at hv <;> omega
    have hviff : v=1 ↔ coefficientsInRange mem h neg (g+i*L) mx mn (l+i*L) L := by
      rw [hv]
      split_ifs with hh
      · exact iff_of_true rfl hh
      · exact iff_of_false (by decide) hh
    have hcombined := full_bit_product hbit hvbit hprior hviff
    have hprod : st.regs 8*v<2^w := hcombined.1.trans_lt hw
    refine runs_assign_le (v:=st.regs 8*v) (by eval_expr) ?_ ?_
    · change Inv (i+1) _ ∧ _
      refine ⟨⟨?_,?_,hmem1,?_,?_⟩,?_⟩
      · intro j hj
        simpa only [Function.update_of_ne (by omega : j≠7),Function.update_of_ne (by omega : j≠8),
          Function.update_of_ne (by omega : j≠10),Function.update_of_ne (by omega : j≠9)] using hfixed j hj
      · simp
      · simpa using hcombined.1
      · change st.regs 8*v=1 ↔ _
        rw [hcombined.2]
        constructor
        · rintro ⟨hprev,hnow⟩ j hj
          by_cases hji : j < i
          · exact hprev j hji
          · have : j=i := by omega
            simpa only [this] using hnow
        · intro hall
          exact ⟨fun j hj => hall j (by omega),hall i (by omega)⟩
      · simpa using h7
    · simp only [coefficientRangeGuardContract,List.getD_cons_zero,List.getD_cons_succ,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg]
      omega
  have hlp := Triple.forRange_const (w:=w) (p:=p) (r:=7) (lo:=.const 0) (hi:=.reg 0)
    (body:=coefficientRangeFullStep guard)
    (P:=fun st => (∀ j<7,st.regs j=[count,g,l,neg,mx,mn,L].getD j 0) ∧
      st.regs 8=1 ∧ st.mem=mem) (Inv:=Inv)
    (164*L+460) 0 count (Nat.zero_le _) hw (fun _ => hc)
    (fun st hs => by
      obtain ⟨hfixed,hbit,hm⟩ := hs
      refine ⟨by eval_expr,?_,?_,?_,?_,?_⟩
      · intro j hj
        simpa only [Function.update_of_ne (by omega : j≠7)] using hfixed j hj
      · simp
      · exact hm
      · simpa only [Function.update_of_ne (by decide : 8≠7),hbit] using (by decide : 1≤1)
      · simp [hbit])
    (fun _ _ _ _ hi => hi.2.1)
    (fun _ st _ _ hi => by
      have h0 := hi.1 0 (by decide)
      simp only [List.getD_cons_zero] at h0
      eval_expr)
    hbody
  refine hlp.conseq (fun _ hs => hs) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_reg,Expr.size_const,Nat.mul_add]
    omega

/-- The direct full-array scan meets its read-only contract. -/
theorem coefficientRangeFull_meetsContract {w h entry guard : ℕ} {p : Program}
    (hguard : MeetsContract w p guard (coefficientRangeGuardContract w h))
    (hp : p.procs[entry]?=some (coefficientRangeFullBody guard)) :
    MeetsContract w p entry (coefficientRangeFullContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨count,g,l,neg,mx,mn,L,rfl,hw,hsource⟩ := hpre
  have hc := hwords count (by simp)
  have hloop := coefficientRangeFull_loop mem hguard hw hc hwords hsource
  apply runs_start_le
  unfold coefficientRangeFullBody
  wram_step
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨?_,by simp,rfl⟩
    intro j hj
    simp only [Function.update_of_ne (by omega : j≠8),startState]
  · intro st ⟨hm,hbit,haccept⟩
    have hvalue : st.regs 8<2^w := hbit.trans_lt hw
    refine runs_ret_le (v:=st.regs 8) (by eval_expr) ?_ ?_
    · exact ⟨hm,hbit,haccept⟩
    · simp only [coefficientRangeFullContract,List.getD_cons_zero,List.getD_cons_succ,
        Expr.size_reg,Expr.size_const]
      omega

/-- Fitting scalar blocks supply the read-only direct scan's precondition. -/
theorem coefficientRangeFull_pre {w h m g l neg mx mn L : ℕ} {mem : ℕ → ℕ}
    (hOne : 1<2^w) (hg : g+m*L<2^w) (hl : l+m*L<2^w)
    (hneg : neg+L<2^w) (hmax : mx+L<2^w) (hmin : mn+L<2^w)
    (hvneg : Num.Valid mem neg h L) (hvmax : Num.Valid mem mx h L)
    (hvmin : Num.Valid mem mn h L)
    (hvalid : ∀ e<m,Num.Valid mem (g+e*L) h L ∧ Num.Valid mem (l+e*L) h L) :
    (coefficientRangeFullContract w h).pre [m,g,l,neg,mx,mn,L] mem := by
  refine ⟨m,g,l,neg,mx,mn,L,rfl,hOne,?_⟩
  intro i hi
  exact ⟨neg,g+i*L,mx,mn,l+i*L,L,rfl,
    ⟨neg,g+i*L,mx,L,rfl,hneg,(reported_entry_end g L i m hi).trans_lt hg,hmax,hvneg,(hvalid i hi).1,hvmax⟩,
    ⟨mn,l+i*L,mx,L,rfl,hmin,(reported_entry_end l L i m hi).trans_lt hl,hmax,hvmin,(hvalid i hi).2,hvmax⟩⟩

/-- Decode the direct full scan's bit in the common fixed-point scale. -/
theorem coefficientRangeFull_output {w h m g l neg mx mn L P v : ℕ}
    {mem final : ℕ → ℕ} {maximum minimum : ℝ}
    (hn : ScalarAt mem neg h L P (-maximum)) (hx : ScalarAt mem mx h L P maximum)
    (hm : ScalarAt mem mn h L P minimum)
    (hout : (coefficientRangeFullContract w h).post [m,g,l,neg,mx,mn,L] mem v final) :
    v=1 ↔ ∀ e<m,|Num.fixVal mem (g+e*L) h L P|<maximum ∧
      minimum<Num.fixVal mem (l+e*L) h L P ∧ Num.fixVal mem (l+e*L) h L P<maximum := by
  have htest := hout.2.2
  change (v=1 ↔ ∀ i<m,coefficientsInRange mem h neg (g+i*L) mx mn (l+i*L) L) at htest
  rw [htest]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [abs_lt,← hn.2,← hx.2,← hm.2]
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<2^P)]
  norm_cast
  tauto

/-- An accepted direct scan puts every edge length in `[2^{-E}, 2^E]` for
`E = F.rangeExponent`, meeting the Init length-range precondition. -/
theorem coefficientRangeFull_lengthsWithin {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    {g l neg mx mn : ℕ} {mem : ℕ → ℕ}
    (hmin : ScalarAt mem mn F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem mx F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hout : (coefficientRangeFullContract w F.fmt.limbBits).post
      [I.m,g,l,neg,mx,mn,F.limbs] mem 1 mem) :
    LengthsWithin (namedInstance I) F.rangeExponent
      (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
  intro e he
  have heM : e<I.m := Finset.mem_range.mp he
  have hr := (coefficientRangeFull_output hneg hmax hmin hout).mp rfl e heM
  simpa only [readVector,heM,↓reduceIte] using (show _ ∧ _ from ⟨hr.2.1.le,hr.2.2.le⟩)

/-- An accepted direct scan bounds every edge gradient by `2^E` in absolute value for
`E = F.rangeExponent`, meeting the Init gradient-range precondition. -/
theorem coefficientRangeFull_gradientsWithin {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    {g l neg mx mn : ℕ} {mem : ℕ → ℕ}
    (hmin : ScalarAt mem mn F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem mx F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hout : (coefficientRangeFullContract w F.fmt.limbBits).post
      [I.m,g,l,neg,mx,mn,F.limbs] mem 1 mem) :
    ∀ e ∈ (namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e| ≤ (2:ℝ)^F.rangeExponent := by
  intro e he
  have heM : e<I.m := Finset.mem_range.mp he
  have hr := (coefficientRangeFull_output hneg hmax hmin hout).mp rfl e heM
  simpa only [readVector,heM,↓reduceIte] using hr.1.le

/-- An accepted direct scan transfers across a prefix frame to the list-scan
postcondition once the canonical name list `List.range m` has been written. -/
theorem coefficientRangeFull_to_listPost {w h names m g l neg mx mn L bound : ℕ}
    {coeffMem started : ℕ → ℕ}
    (hlist : ListAt started names (List.range m))
    (hframe : ∀ z<bound,started z=coeffMem z)
    (hg : g+m*L≤bound) (hl : l+m*L≤bound)
    (hneg : neg+L≤bound) (hmax : mx+L≤bound) (hmin : mn+L≤bound)
    (hout : (coefficientRangeFullContract w h).post [m,g,l,neg,mx,mn,L] coeffMem 1 coeffMem) :
    (coefficientRangeListContract w h).post [names,m,g,l,neg,mx,mn,L] started 1 started := by
  refine ⟨rfl,le_rfl,iff_of_true rfl ?_⟩
  intro i hi
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hi ⊢
  have hread : started (names+i)=i :=
    (hlist i (by simpa only [List.length_range] using hi)).trans (List.getElem_range _)
  rw [hread]
  have hraw := hout.2.2.mp rfl i hi
  have hgEnd : g+i*L+L≤bound := (reported_entry_end g L i m hi).trans hg
  have hlEnd : l+i*L+L≤bound := (reported_entry_end l L i m hi).trans hl
  simp only [coefficientsInRange,
    Num.IPM.value_frozen hframe hneg,
    Num.IPM.value_frozen hframe hgEnd,
    Num.IPM.value_frozen hframe hmax,
    Num.IPM.value_frozen hframe hmin,
    Num.IPM.value_frozen hframe hlEnd]
  exact hraw

end MinCostFlow.IPM.Machine
