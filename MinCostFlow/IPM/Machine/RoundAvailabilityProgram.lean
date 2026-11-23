module

public import MinCostFlow.IPM.Machine.RoundAvailability
public import MinCostFlow.IPM.Machine.RoundRatFacts
import WordRAM.Tactic

/-!
# Allocating both availabilities for a new forest edge

Compute the floor, restore its precision, subtract it from the
initial flow, then subtract the fractional part from one. All
outputs use the original signed fixed-point scale.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Arguments [flow,one,L,P,heap]. Return the allocation endpoint
with backward and forward availability at fixed offsets. -/
def roundAvailabilityBody (floor shift subtract : ℕ) : Stmt :=
  .call 5 floor [.reg 0,.reg 2,.reg 3,.reg 4] ;;
  .call 6 shift [.bin .sub (.reg 5) (.reg 2),.reg 2,.reg 3,.reg 5] ;;
  .call 7 subtract [.reg 0,.reg 5,.reg 2,.reg 6] ;;
  .call 8 subtract [.reg 1,.bin .sub (.reg 7) (.reg 2),.reg 2,.reg 7] ;;
  .ret (.reg 8)

/-- Fractional coordinates need two exact signed availability
blocks and one integer floor. -/
def roundAvailabilityContract (w h : ℕ) : Contract where
  pre args mem := ∃ flow one L P heap x,
    args=[flow,one,L,P,heap] ∧ RatAt mem flow h L P x ∧ RatAt mem one h L P 1 ∧
    isIntRat x=false ∧ flow+L≤heap ∧ one+L≤heap ∧
    RatFits h L P (⌊x⌋:ℚ) ∧ RatFits h L P (x-(⌊x⌋:ℚ)) ∧ RatFits h L P ((⌈x⌉:ℚ)-x) ∧
    ZeroFrom mem heap ∧ heap+7*L+1<2^w
  post args mem v final :=
    let L := args.getD 2 0
    let P := args.getD 3 0
    let heap := args.getD 4 0
    let x := readRat mem (args.getD 0 0) h L P
    v=heap+7*L+1 ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧
    RatAt final (heap+4*L+1) h L P (x-(⌊x⌋:ℚ)) ∧ RatAt final (heap+6*L+1) h L P ((⌈x⌉:ℚ)-x)
  cost args _ := 249*args.getD 2 0+300

/-- The availability procedure uses no randomness. -/
theorem roundAvailability_noRand (floor shift subtract : ℕ) :
    (roundAvailabilityBody floor shift subtract).NoRand := by
  simp [roundAvailabilityBody,Stmt.NoRand]

set_option maxHeartbeats 650000 in
/-- Rounding's exact availability computation costs linear work
in the number of limbs. -/
theorem roundAvailability_meetsContract {w h entry floor shift subtract : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (roundAvailabilityBody floor shift subtract))
    (hfloor : MeetsContract w p floor (Num.floorContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hsubtract : MeetsContract w p subtract (Num.subtractContract w h)) :
    MeetsContract w p entry (roundAvailabilityContract w h) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨a,one,L,P,heap,x,rfl,ha,hone,hfrac,haEnd,hOneEnd,hFitFl,hFitB,hFitF,hz,hSpace⟩ := hpre
  have haW : a<2^w := hwords _ (by simp)
  have hoW : one<2^w := hwords _ (by simp)
  have hL : L<2^w := hwords _ (by simp)
  have hP : P<2^w := hwords _ (by simp)
  have hHeap : heap<2^w := hwords _ (by simp)
  have hFP : IsFixedPoint P x := ⟨Num.intVal mem a h L,ha.2.symm⟩
  have he := (round_availability_bounds P x hFP hfrac).2.2.2.2.2.2
  apply runs_start_le
  unfold roundAvailabilityBody
  refine runs_seq_call_le hfloor (vs:=[a,L,P,heap]) (by eval_expr) (by wram_words)
    ⟨⟨a,L,P,heap,rfl,haEnd,ha.1⟩,hz,by change heap+(2*L+1)<2^w; omega⟩ ?_
  intro v1 m1 p1 hpost1
  obtain ⟨hv1,hf1,hz1,hn1,hval1⟩ := round_floor_output ha hpost1
  have hv1W : v1<2^w := by omega
  have hflPtr : v1-L=heap+L+1 := by omega
  have hflW : heap+L+1<2^w := by omega
  refine runs_seq_call_le hshift (vs:=[heap+L+1,L,P,v1])
    (by eval_expr; simp [Expr.eval,BinOp.eval,startState,hflPtr,hflW]) (by wram_words)
    ⟨⟨heap+L+1,L,P,v1,rfl,by omega,hn1⟩,hz1,by change v1+L<2^w; omega⟩ ?_
  intro v2 m2 p2 hpost2
  obtain ⟨hv2,hf2,hz2,hval2⟩ := round_shift_output hval1 hFitFl hpost2
  have hv2W : v2<2^w := by omega
  have hal := (ha.frozen hf1 haEnd).frozen hf2 (by omega)
  have hol := (hone.frozen hf1 hOneEnd).frozen hf2 (by omega)
  refine runs_seq_call_le hsubtract (vs:=[a,v1,L,v2]) (by eval_expr) (by wram_words)
    ⟨⟨a,v1,L,v2,rfl,by omega,by omega,hal.1,hval2.1⟩,hz2,by change v2+2*L<2^w; omega⟩ ?_
  intro v3 m3 p3 hpost3
  obtain ⟨hv3,hf3,hz3,hval3⟩ := round_subtract_output hal hval2 hFitB hpost3
  have hv3W : v3<2^w := by omega
  have hBPtr : v3-L=v2+L := by omega
  have hBW : v2+L<2^w := by omega
  have hOne3 := hol.frozen hf3 (by omega)
  refine runs_seq_call_le hsubtract (vs:=[one,v2+L,L,v3])
    (by eval_expr; simp [Expr.eval,BinOp.eval,startState,hBPtr,hBW]) (by wram_words)
    ⟨⟨one,v2+L,L,v3,rfl,by omega,by omega,hOne3.1,hval3.1⟩,hz3,by change v3+2*L<2^w; omega⟩ ?_
  intro v4 m4 p4 hpost4
  obtain ⟨hv4,hf4,hz4,hval4⟩ := round_subtract_output hOne3 hval3 (he ▸ hFitF) hpost4
  have hback := hval3.frozen hf4 (by omega)
  have hv4W : v4<2^w := by omega
  have hbackPtr : v2+L=heap+4*L+1 := by omega
  have hfwdPtr : v3+L=heap+6*L+1 := by omega
  have hv4End : v4=heap+7*L+1 := by omega
  refine runs_ret_le (v:=v4) (by eval_expr) ?_ ?_
  · change v4=heap+7*L+1 ∧ (∀ z<heap,m4 z=mem z) ∧ ZeroFrom m4 v4 ∧
      RatAt m4 (heap+4*L+1) h L P (readRat mem a h L P-(⌊readRat mem a h L P⌋:ℚ)) ∧
      RatAt m4 (heap+6*L+1) h L P ((⌈readRat mem a h L P⌉:ℚ)-readRat mem a h L P)
    rw [ha.2,← hbackPtr,← hfwdPtr,he]
    exact ⟨hv4End,fun z hz' => (hf4 z (by omega)).trans
      ((hf3 z (by omega)).trans ((hf2 z (by omega)).trans (hf1 z hz'))),hz4,hback,hval4⟩
  · simp only [roundAvailabilityContract,Num.floorContract,Num.shiftRightContract,Num.shiftLeftContract,
      Num.subtractContract,heapContract,argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,
      List.getD_cons_zero,List.getD_cons_succ]
    omega

end MinCostFlow.IPM.Machine
