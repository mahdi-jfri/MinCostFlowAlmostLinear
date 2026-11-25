module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Num.LoadInt
public import MinCostFlow.Num.ShiftLeft
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import Mathlib.Tactic.FieldSimp

/-!
# Storing an initial half-integral flow at fixed precision

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) initializes zero-lower-bound edges at half their
integral capacity. The model of page 7 stores fixed-point numbers.
Load the capacity as an exact integer and shift it left by `P-1` bits.
At precision `P` the resulting block is exactly half the capacity,
including odd capacities. The existing verified numerical procedures
perform both operations; this wrapper counts their costs and space.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[capacity,L,P,heap]`. -/
def initialMidpointBlockBody (load shift : ℕ) : Stmt :=
  .call 4 load [.const 0,.reg 0,.reg 1,.reg 3] ;;
  .call 5 shift [.bin .add (.reg 3) (.reg 1),.reg 1,
    .bin .sub (.reg 2) (.const 1),.reg 4] ;;
  .ret (.reg 5)

/-- Entry, integer loader and left-shift module. -/
def initialMidpointBlockModule (b h : ℕ) : List Stmt :=
  [initialMidpointBlockBody (b+1) (b+6)] ++
    (Num.loadIntModule (b+1) h ++ Num.shiftLeftModule (b+6) h)

/-- The output is at `heap+2L`, return `heap+3L`, space `3L`, cost at
most `100L+200`. The precondition states numeric fits, never a decoding
or correctness result that the caller would first have to prove. -/
def initialMidpointBlockContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ cap L P heap, args = [cap,L,P,heap] ∧ 1 ≤ P ∧
      Num.Fits h L (cap : ℤ) ∧ Num.Fits h L ((cap : ℤ)*(2 : ℤ)^(P-1)))
    (fun args _ mem' => ScalarAt mem' (heapArg args+2*args.getD 1 0) h
      (args.getD 1 0) (args.getD 2 0) (((args.getD 0 0 : ℕ) : ℝ)/2))
    (fun args _ => 100*args.getD 1 0+200) (fun args _ => 3*args.getD 1 0)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+3*args.getD 1 0 }

/-- Initialization's block loader has no random instruction. -/
theorem initialMidpointBlockModule_noRand (b h : ℕ) :
    ∀ body ∈ initialMidpointBlockModule b h, body.NoRand := by
  intro body hb
  simp only [initialMidpointBlockModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [initialMidpointBlockBody,Stmt.NoRand]
  · exact Num.loadIntModule_noRand _ _ body hb
  · exact Num.shiftLeftModule_noRand _ _ body hb

/-- The initial midpoint is represented exactly as a multiword dyadic
number. All rounding and wrap-around are eliminated by the explicit
fit premises. This proof uses the existing arithmetic contracts. -/
theorem initialMidpointBlock_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (initialMidpointBlockModule b h)) :
    MeetsContract w p b (initialMidpointBlockContract w h) := by
  have hrest : p.HasAt (b+1) (Num.loadIntModule (b+1) h ++ Num.shiftLeftModule (b+6) h) :=
    Num.hasAt_append_right hp
  have hload := Num.hasAt_append_left hrest
  have hshift : p.HasAt (b+6) (Num.shiftLeftModule (b+6) h) := Num.hasAt_append_right hrest
  have hw1 : 1 < 2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) (Num.base_lt_word hw)
  have hloadSpec := Num.loadInt_meetsContract hw1 (Num.base_lt_word hw) hload
  have hshiftSpec := Num.shiftLeft_meetsContract hh hw hshift
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨cap,L,P,heap,rfl,hP,hcap,hfinal⟩,hzero,hspace⟩ := hpre
  change heap+3*L < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hc : cap < 2^w := hwords _ (by simp)
  have hL : L < 2^w := hwords _ (by simp)
  have hPw : P < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hsource : heap+L < 2^w := by omega
  have hPm : P-1 < 2^w := by omega
  apply runs_start_le
  unfold initialMidpointBlockBody
  refine runs_seq_call_le hloadSpec (vs := [0,cap,L,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨(cap : ℤ),L,heap,by simp [encodeSignedPair]⟩,hzero,by change heap+2*L < 2^w; omega⟩
  · intro v1 mem1 pos1 hp1
    obtain ⟨hv1,hlo1,hhi1,hframe1,hzero1,hvalid,hvalue⟩ := hp1
    change v1 = heap+2*L at hv1
    change Num.Valid mem1 (heap+L) h L at hvalid
    change Num.intVal mem1 (heap+L) h L = Num.wrap h L (Num.decodeIntWords 0 cap) at hvalue
    simp only [Num.decodeIntWords,↓reduceIte,Num.wrap_of_fits hcap] at hvalue
    have hv1w : v1 < 2^w := by omega
    refine runs_seq_call_le hshiftSpec (vs := [heap+L,L,P-1,v1]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,rfl,by omega,hvalid⟩,hzero1,by change v1+L < 2^w; omega⟩
    · intro v2 mem2 pos2 hp2
      obtain ⟨hv2,hlo2,hhi2,hframe2,hzero2,hvalid2,hvalue2⟩ := hp2
      change v2 = v1+L at hv2
      change Num.Valid mem2 v1 h L at hvalid2
      change Num.intVal mem2 v1 h L = Num.wrap h L (Num.intVal mem1 (heap+L) h L*(2 : ℤ)^(P-1)) at hvalue2
      rw [hvalue,Num.wrap_of_fits hfinal] at hvalue2
      have hv2w : v2 < 2^w := by omega
      refine runs_ret_le (v := v2) (by eval_expr) ?_ ?_
      · change (heap ≤ v2 ∧ v2 ≤ heap+3*L ∧ (∀ x < heap, mem2 x = mem x) ∧
          ZeroFrom mem2 v2 ∧ ScalarAt mem2 (heap+2*L) h L P ((cap : ℝ)/2)) ∧ v2 = heap+3*L
        refine ⟨⟨by omega,by omega,?_,hzero2,?_,?_⟩,by omega⟩
        · intro x hx
          exact (hframe2 x (by change x < v1; omega)).trans (hframe1 x hx)
        · simpa only [hv1] using hvalid2
        · change Num.fixVal mem2 (heap+2*L) h L P = (cap : ℝ)/2
          rw [← hv1,Num.fixVal,hvalue2]
          simp only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Int.cast_ofNat]
          have hpow : (2 : ℝ)^P = (2 : ℝ)^(P-1)*2 := by
            conv_lhs => rw [show P = P-1+1 by omega]
            rw [pow_succ]
          rw [hpow]
          field_simp
      · simp only [initialMidpointBlockContract,Num.loadIntContract,Num.shiftLeftContract,heapContract,
          Expr.size_bin,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil,List.getD_cons_zero,List.getD_cons_succ]
        omega

end MinCostFlow.IPM.Machine
