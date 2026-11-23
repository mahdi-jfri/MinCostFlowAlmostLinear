module

public import MinCostFlow.IPM.Machine.InitialMidpointBlock
public import MinCostFlow.Num.IPM.WriteBlock
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic

/-!
# Loading a contiguous initial fixed-point flow array

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) gives half-integral midpoints. Reserve a dense
array, load each capacity's exact half using the verified scalar
wrapper, and copy the resulting block into that array. Numerical
scratch is kept after the whole output array. All source words and
all already written coordinates are preserved at every iteration.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[capacityAddress,m,L,P,heap]`, with capacities at stride five. -/
def initialMidpointVectorBody (load write : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.reg 1) (.reg 2))) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
     .call 6 load [.reg 7,.reg 2,.reg 3,.reg 6] ;;
     .call 8 write [.bin .sub (.reg 6) (.reg 2),.reg 2,
       .bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 2))]) ;;
  .ret (.reg 6)

/-- Entry, scalar block loader and exact array writer. -/
def initialMidpointVectorModule (b h : ℕ) : List Stmt :=
  [initialMidpointVectorBody (b+1) (b+9)] ++
    (initialMidpointBlockModule (b+1) h ++ Num.IPM.writeBlockModule (b+9))

/-- Dense output begins at the old heap. Space including scratch is
`4mL`, cost at most `m(200L+600)+100`, and return is `heap+4mL`.
Every output entry equals exactly half its input capacity. -/
def initialMidpointVectorContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a m L P heap, args = [a,m,L,P,heap] ∧ 1 ≤ P ∧
      ∀ i < m, a+5*i < heap ∧ mem (a+5*i) < 2^w ∧
        Num.Fits h L (mem (a+5*i) : ℤ) ∧
        Num.Fits h L ((mem (a+5*i) : ℤ)*(2 : ℤ)^(P-1)))
    (fun args mem mem' => ∀ i < args.getD 1 0,
      ScalarAt mem' (heapArg args+i*args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)
        ((mem (args.getD 0 0+5*i) : ℝ)/2))
    (fun args _ => args.getD 1 0*(200*args.getD 2 0+600)+100)
    (fun args _ => 4*(args.getD 1 0*args.getD 2 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+4*(args.getD 1 0*args.getD 2 0) }

/-- All numerical procedures used by the flow-array initializer are deterministic. -/
theorem initialMidpointVectorModule_noRand (b h : ℕ) :
    ∀ body ∈ initialMidpointVectorModule b h, body.NoRand := by
  intro body hb
  simp only [initialMidpointVectorModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [initialMidpointVectorBody,forRange,forUp,Stmt.NoRand]
  · exact initialMidpointBlockModule_noRand _ _ body hb
  · exact Num.IPM.writeBlockModule_noRand _ body hb

set_option maxRecDepth 4096 in
private theorem vector_loop {w h a m L P heap load write : ℕ} (p : Program) (mem : ℕ → ℕ)
    (hw : 5 < 2^w) (hm : m < 2^w) (hL : L < 2^w) (hP : P < 2^w)
    (hprec : 1 ≤ P) (hspace : heap+4*(m*L) < 2^w) (hzero : ZeroFrom mem heap)
    (hsource : ∀ i < m, a+5*i < heap ∧ mem (a+5*i) < 2^w ∧
      Num.Fits h L (mem (a+5*i) : ℤ) ∧ Num.Fits h L ((mem (a+5*i) : ℤ)*(2 : ℤ)^(P-1)))
    (hload : MeetsContract w p load (initialMidpointBlockContract w h))
    (hwrite : MeetsContract w p write (Num.IPM.writeBlockContract w h)) :
    Triple w p
      (fun st => st.regs 0 = a ∧ st.regs 1 = m ∧ st.regs 2 = L ∧ st.regs 3 = P ∧
        st.regs 4 = heap ∧ st.regs 6 = heap+m*L ∧ st.mem = mem)
      (forRange 5 (.const 0) (.reg 1)
        (.assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
         .call 6 load [.reg 7,.reg 2,.reg 3,.reg 6] ;;
         .call 8 write [.bin .sub (.reg 6) (.reg 2),.reg 2,
           .bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 2))]))
      (normalPost fun st => st.regs 6 = heap+4*(m*L) ∧
        (∀ i < m, ScalarAt st.mem (heap+i*L) h L P ((mem (a+5*i) : ℝ)/2)) ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+4*(m*L)))
      (fun _ => m*(200*L+600)+50) := by
  have hl := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (body := .assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 5) (.reg 5)))) ;;
      .call 6 load [.reg 7,.reg 2,.reg 3,.reg 6] ;;
      .call 8 write [.bin .sub (.reg 6) (.reg 2),.reg 2,
        .bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 2))])
    (P := fun st => st.regs 0 = a ∧ st.regs 1 = m ∧ st.regs 2 = L ∧ st.regs 3 = P ∧
      st.regs 4 = heap ∧ st.regs 6 = heap+m*L ∧ st.mem = mem)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = m ∧ st.regs 2 = L ∧ st.regs 3 = P ∧
      st.regs 4 = heap ∧ st.regs 5 = i ∧ st.regs 6 = heap+m*L+3*(i*L) ∧
      (∀ j < i, ScalarAt st.mem (heap+j*L) h L P ((mem (a+5*j) : ℝ)/2)) ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+m*L+3*(i*L)))
    (150*L+500) 0 m (Nat.zero_le m) (by omega) (fun _ => hm)
    (fun st hh => by
      obtain ⟨h0,h1,h2,h3,h4,h6,hmem⟩ := hh
      refine ⟨by eval_expr,?_⟩
      have hz : ZeroFrom mem (heap+m*L) := fun x hx => hzero x (by omega)
      simpa [hmem] using
        And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h6 hz))))))
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st omegaBits hst
      obtain ⟨h0,h1,h2,h3,h4,h5,h6,htable,hframe,hfresh⟩ := hst
      obtain ⟨hbefore,hword,hcap,hscaled⟩ := hsource i hi
      have hread : st.mem (a+5*i) = mem (a+5*i) := hframe _ hbefore
      have hmul : i*L+L ≤ m*L := by
        simpa only [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      have hsfit : heap+m*L+3*(i*L)+3*L < 2^w := by omega
      have hsw : heap+m*L+3*(i*L) < 2^w := by omega
      have hmulw : i*L < 2^w := by omega
      have haddr : a+5*i < 2^w := by omega
      have h5iw : 5*i < 2^w := by omega
      apply runs_start_le
      refine runs_seq_assign_le (v := mem (a+5*i)) (by eval_expr) ?_
      refine runs_seq_call_le hload (vs := [mem (a+5*i),L,P,heap+m*L+3*(i*L)]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,rfl,hprec,hcap,hscaled⟩,hfresh,hsfit⟩
      · intro v1 mem1 pos1 hp1
        obtain ⟨⟨hlo,hhi,hframe1,hzero1,hblock⟩,hv1⟩ := hp1
        change v1 = heap+m*L+3*(i*L)+3*L at hv1
        change ScalarAt mem1 (heap+m*L+3*(i*L)+2*L) h L P ((mem (a+5*i) : ℝ)/2) at hblock
        change ∀ x < heap+m*L+3*(i*L), mem1 x = st.mem x at hframe1
        have hv1w : v1 < 2^w := by omega
        have hsrc : v1-L = heap+m*L+3*(i*L)+2*L := by omega
        have hsrcw : v1-L < 2^w := by omega
        have hdstw : heap+i*L < 2^w := by omega
        refine runs_call_le hwrite (vs := [v1-L,L,heap+i*L]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · refine ⟨_,_,_,rfl,by omega,by omega,Or.inr (by omega),?_⟩
          simpa only [hsrc] using hblock.1
        · intro ignored mem2 pos2 hp2
          obtain ⟨_,hframe2,_,hvalid,hvalue⟩ := hp2
          change ∀ x, x < heap+i*L ∨ heap+i*L+L ≤ x → mem2 x = mem1 x at hframe2
          change Num.Valid mem2 (heap+i*L) h L at hvalid
          change Num.intVal mem2 (heap+i*L) h L = Num.intVal mem1 (v1-L) h L at hvalue
          have hnew : ScalarAt mem2 (heap+i*L) h L P ((mem (a+5*i) : ℝ)/2) := by
            refine ⟨hvalid,?_⟩
            change (Num.intVal mem2 (heap+i*L) h L : ℝ)/(2 : ℝ)^P = _
            rw [hvalue,hsrc]
            exact hblock.2
          have hboth : ∀ x < heap+i*L, mem2 x = st.mem x := by
            intro x hx
            exact (hframe2 x (Or.inl hx)).trans (hframe1 x (by omega))
          have hnext : v1 = heap+m*L+3*((i+1)*L) := by
            rw [Nat.add_mul,Nat.one_mul]
            omega
          constructor
          · change (_ ∧ _) ∧ _
            refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,h5⟩
            · simpa using h0
            · simpa using h1
            · simpa using h2
            · simpa using h3
            · simpa using h4
            · simp
            · simpa using hnext
            · intro j hj
              by_cases he : j = i
              · subst j; exact hnew
              · have hji : j+1 ≤ i := by omega
                have hend : heap+j*L+L ≤ heap+i*L := by
                  have hh := Nat.mul_le_mul_right L hji
                  rw [Nat.add_mul,Nat.one_mul] at hh
                  omega
                have hprev := htable j (by omega)
                exact ⟨Num.IPM.valid_frozen hboth hend hprev.1,
                  (Num.IPM.fixVal_frozen hboth hend).trans hprev.2⟩
            · intro x hx
              exact (hframe2 x (Or.inl (by omega))).trans ((hframe1 x (by omega)).trans (hframe x hx))
            · have hz := Num.IPM.zeroFrom_writeBlock hframe2 (by omega) hzero1
              simpa only [hnext] using hz
          · simp only [initialMidpointBlockContract,Num.IPM.writeBlockContract,heapContract,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil,
              List.getD_cons_zero,List.getD_cons_succ]
            omega)
  refine hl.conseq (fun _ hh => hh) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal =>
      obtain ⟨_,_,_,_,_,_,h6,ht,hf,hz⟩ := ho
      have heq : heap+m*L+3*(m*L) = heap+4*(m*L) := by omega
      rw [heq] at h6 hz
      exact ⟨h6,ht,hf,hz⟩
  · intro _ _
    have hh := Nat.mul_le_mul_left m (show 150*L+500+1+8 ≤ 200*L+600 by omega)
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- The exact midpoint loader produces a dense fixed-point flow array,
counts all numerical scratch and copies, and preserves the input. -/
theorem initialMidpointVector_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hwordsConst : 5 < 2^w)
    (hp : p.HasAt b (initialMidpointVectorModule b h)) :
    MeetsContract w p b (initialMidpointVectorContract w h) := by
  have hrest : p.HasAt (b+1) (initialMidpointBlockModule (b+1) h ++ Num.IPM.writeBlockModule (b+9)) :=
    Num.hasAt_append_right hp
  have hload := Num.hasAt_append_left hrest
  have hwrite : p.HasAt (b+9) (Num.IPM.writeBlockModule (b+9)) := Num.hasAt_append_right hrest
  have hloadSpec := initialMidpointBlock_meetsContract hh hw hload
  have hwriteSpec := Num.IPM.writeBlock_meetsContract (h := h) (by omega : 1 < 2^w) hwrite
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,m,L,P,heap,rfl,hprec,hsource⟩,hzero,hspace⟩ := hpre
  change heap+4*(m*L) < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hm : m < 2^w := hwords _ (by simp)
  have hL : L < 2^w := hwords _ (by simp)
  have hP : P < 2^w := hwords _ (by simp)
  have hmL : m*L < 2^w := by omega
  have hinit : heap+m*L < 2^w := by omega
  have hloop := vector_loop p mem hwordsConst hm hL hP hprec hspace hzero hsource hloadSpec hwriteSpec
  apply runs_start_le
  unfold initialMidpointVectorBody
  refine runs_seq_assign_le (v := heap+m*L) (by eval_expr) ?_
  refine runs_seq_triple_le hloop (by simp [startState]) ?_
  intro st ⟨h6,htable,hframe,hfresh⟩
  refine runs_ret_le (v := heap+4*(m*L)) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+4*(m*L) ∧ heap+4*(m*L) ≤ heap+4*(m*L) ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap+4*(m*L)) ∧ _) ∧ _
    exact ⟨⟨by omega,le_rfl,hframe,hfresh,htable⟩,rfl⟩
  · simp only [initialMidpointVectorContract,heapContract,Expr.size_bin,Expr.size_reg,
      List.getD_cons_zero,List.getD_cons_succ]
    omega

end MinCostFlow.IPM.Machine
