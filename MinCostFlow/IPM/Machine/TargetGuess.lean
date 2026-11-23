module

public import MinCostFlow.IPM.Machine.FixedIntegerBlock
public import MinCostFlow.IPM.Machine.PrecisionProducts
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Encoding an integer target from a search offset

Bisection uses unsigned offsets from its lower endpoint. The
numerical test takes the signed difference in fixed-point format.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The integer represented by an unsigned offset. -/
def offsetTarget (radius offset : ℕ) : ℤ := (offset:ℤ)-radius

/-- The sign-magnitude operands computed by the target encoder. -/
theorem encodeInt_offsetTarget (radius offset : ℕ) :
    encodeInt (offsetTarget radius offset)=
      if offset < radius then [1,radius-offset] else [0,offset-radius] := by
  by_cases h : offset < radius
  · have hneg : offsetTarget radius offset<0 := by unfold offsetTarget; omega
    have he : offsetTarget radius offset= -(↑(radius-offset):ℤ) := by unfold offsetTarget; omega
    unfold encodeInt
    rw [ite_eq_left hneg,ite_eq_left h,he,Int.natAbs_neg,Int.natAbs_natCast]
  · have hpos : 0≤offsetTarget radius offset := by unfold offsetTarget; omega
    have he : offsetTarget radius offset=(↑(offset-radius):ℤ) := by unfold offsetTarget; omega
    unfold encodeInt
    rw [ite_eq_right (not_lt_of_ge hpos),ite_eq_right h,he,Int.natAbs_natCast]

/-- Arguments [offset,radius,L,P,heap]. Return the exact signed
target in a fixed-point block. -/
def targetGuessBody (write : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 0) (.reg 1))
    (.call 5 write [.const 1,.bin .sub (.reg 1) (.reg 0),.reg 2,.reg 3,.reg 4] ;; .ret (.reg 5))
    (.call 5 write [.const 0,.bin .sub (.reg 0) (.reg 1),.reg 2,.reg 3,.reg 4] ;; .ret (.reg 5))

/-- Offset target writer with the exact three-block layout. -/
def targetGuessContract (w h : ℕ) : Contract where
  pre args mem := ∃ offset radius L P heap,args=[offset,radius,L,P,heap] ∧
    (fixedIntegerBlockContract w h).pre (encodeInt (offsetTarget radius offset)++[L,P,heap]) mem
  post args mem v final :=
    let n := offsetTarget (args.getD 1 0) (args.getD 0 0)
    (fixedIntegerBlockContract w h).post (encodeInt n++args.drop 2) mem v final
  cost args _ := 100*args.getD 2 0+240

/-- The target encoder uses only word arithmetic and calls. -/
theorem targetGuess_noRand (write : ℕ) : (targetGuessBody write).NoRand := by
  simp [targetGuessBody,Stmt.NoRand]

/-- Every represented guess in the bounded cost interval fits at the
selected fixed-point precision. -/
theorem offsetTarget_precision (m U offset : ℕ)
    (hm : 0<m) (hU : 0<U) (hOffset : offset≤2*(m*U^2)) :
    let radius := m*U^2
    let n := offsetTarget radius offset
    |(n:ℝ)|≤(m:ℝ)*(U:ℝ)^2 ∧
      Num.Fits 4 (ipmLimbs m U) n ∧ Num.Fits 4 (ipmLimbs m U) (n*(2:ℤ)^(ipmPrecision m U)) := by
  dsimp only
  let B := m*U^2
  let n := offsetTarget B offset
  have hlo : -(B:ℤ)≤n := by unfold n offsetTarget; omega
  have hhi : n≤(B:ℤ) := by change offset≤2*B at hOffset; unfold n offsetTarget; omega
  have hb : |(n:ℝ)|≤(m:ℝ)*(U:ℝ)^2 := by
    have h : |(n:ℝ)|≤(B:ℝ) := abs_le.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
    simpa only [B,Nat.cast_mul,Nat.cast_pow] using h
  have htwice := twice_search_radius_le_dyadic m U hm hU
  have hsmall : (m:ℝ)*(U:ℝ)^2≤(2:ℝ)^(slackRangeExponent m U) := by
    have h0 : (0:ℝ)≤(m:ℝ)*(U:ℝ)^2 := by positivity
    linarith only [htwice,h0]
  have hp : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(ipmRangeExponent m U) :=
    pow_le_pow_right₀ (by norm_num) (by unfold ipmRangeExponent; omega)
  exact ⟨hb,fits_integer_at_chosen_precision m U n (hb.trans (hsmall.trans hp))⟩

/-- Combine exact numerical fit with the fresh allocation for the target. -/
theorem targetGuess_pre_of_fits {w h offset radius L P heap : ℕ} {mem : ℕ → ℕ}
    (hfits : Num.Fits h L (offsetTarget radius offset))
    (hscaled : Num.Fits h L (offsetTarget radius offset*(2:ℤ)^P))
    (hz : ZeroFrom mem heap) (hspace : heap+3*L<2^w) :
    (targetGuessContract w h).pre [offset,radius,L,P,heap] mem :=
  ⟨offset,radius,L,P,heap,rfl,
    ⟨⟨offsetTarget radius offset,L,P,heap,rfl,hfits,hscaled⟩,hz,hspace⟩⟩

/-- Execute the target encoder using the exact signed fixed-point writer. -/
theorem targetGuess_meetsContract {w h entry write : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (targetGuessBody write))
    (hwrite : MeetsContract w p write (fixedIntegerBlockContract w h))
    (hOne : 1<2^w) : MeetsContract w p entry (targetGuessContract w h) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨i,B,L,P,heap,rfl,hpre⟩ := hpre
  have hi : i<2^w := hwords _ (by simp)
  have hB : B<2^w := hwords _ (by simp)
  have hL : L<2^w := hwords _ (by simp)
  have hP : P<2^w := hwords _ (by simp)
  have hh : heap<2^w := hwords _ (by simp)
  have hiB : i-B<2^w := (Nat.sub_le _ _).trans_lt hi
  have hBi : B-i<2^w := (Nat.sub_le _ _).trans_lt hB
  have hz : 0<2^w := by omega
  have hforward (sign mag : ℕ) (hs : sign<2^w) (hm : mag<2^w) :
      ∀ x∈[sign,mag,L,P,heap],x<2^w := by wram_words
  apply runs_start_le
  unfold targetGuessBody
  by_cases hneg : i < B
  · refine runs_cond_le (v:=1) (Expr.eval_lt_true (by eval_expr) (by eval_expr) hneg hOne) ?_ (fun h => by omega)
    intro _
    refine runs_seq_call_le hwrite (vs:=[1,B-i,L,P,heap]) (by eval_expr) (hforward 1 _ hOne hBi) ?_ ?_
    · change (fixedIntegerBlockContract w h).pre [1,B-i,L,P,heap] mem
      simpa only [encodeInt_offsetTarget,hneg,ite_true,List.cons_append,List.nil_append] using hpre
    · intro v final newPos hout
      have hpost : (targetGuessContract w h).post [i,B,L,P,heap] mem v final := by
        change (fixedIntegerBlockContract w h).post (encodeInt (offsetTarget B i)++[L,P,heap]) mem v final
        rw [encodeInt_offsetTarget,ite_eq_left hneg]
        exact hout
      have hv : v=heap+3*L := hout.2
      refine runs_ret_le (v:=v) (by eval_expr) hpost ?_
      simp only [targetGuessContract,fixedIntegerBlockContract,heapContract,argsSize,Expr.size, List.getD_cons_zero,
        List.getD_cons_succ]
      omega
  · refine runs_cond_le (v:=0) (Expr.eval_lt_false (by eval_expr) (by eval_expr) (Nat.le_of_not_gt hneg) hOne)
      (fun h => (h rfl).elim) ?_
    intro _
    refine runs_seq_call_le hwrite (vs:=[0,i-B,L,P,heap]) (by eval_expr) (hforward 0 _ hz hiB) ?_ ?_
    · change (fixedIntegerBlockContract w h).pre [0,i-B,L,P,heap] mem
      simpa only [encodeInt_offsetTarget,hneg,ite_false,List.cons_append,List.nil_append] using hpre
    · intro v final newPos hout
      have hpost : (targetGuessContract w h).post [i,B,L,P,heap] mem v final := by
        change (fixedIntegerBlockContract w h).post (encodeInt (offsetTarget B i)++[L,P,heap]) mem v final
        rw [encodeInt_offsetTarget,ite_eq_right hneg]
        exact hout
      have hv : v=heap+3*L := hout.2
      refine runs_ret_le (v:=v) (by eval_expr) hpost ?_
      simp only [targetGuessContract,fixedIntegerBlockContract,heapContract,argsSize,Expr.size, List.getD_cons_zero,
        List.getD_cons_succ]
      omega

end MinCostFlow.IPM.Machine
