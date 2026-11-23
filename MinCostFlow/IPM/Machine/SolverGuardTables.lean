module

public import MinCostFlow.IPM.Machine.SignedGuardConstants
public import MinCostFlow.IPM.Machine.NormalizationProgram
public import MinCostFlow.IPM.Machine.PrecisionCallRanges
import WordRAM.Tactic
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic

/-!
# The bounded solver's immutable guard and normalization blocks

The two range guards share the selected common exponent. The same
positive minimum also bounds the approximate lengths. The six-word
precision record gives the range and the stored barrier exponent.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[R,L,P,k,j,heap]`. The four guard blocks precede the request. -/
def solverGuardTablesBody (constants normalization : ℕ) : Stmt :=
  .call 6 constants [.reg 0,.reg 1,.reg 2,.reg 5] ;;
  .call 7 normalization [.reg 3,.reg 4,.reg 1,.reg 2,.reg 6] ;;
  .ret (.reg 7)

/-- The block layout for the read-only guard and request values. -/
def SolverGuardTablesAt (mem : ℕ → ℕ) (heap R L P k j : ℕ) : Prop :=
  ScalarAt mem heap 4 L P (1/(2:ℝ)^R) ∧
  ScalarAt mem (heap+L) 4 L P ((2:ℝ)^R) ∧
  ScalarAt mem (heap+2*L) 4 L P (1/4) ∧
  ScalarAt mem (heap+3*L) 4 L P (-(2:ℝ)^R) ∧
  ScalarAt mem (heap+4*L) 4 L P (1/(2:ℝ)^(dyadicNormalizationExponent k j))

/-- The exact guard values are produced in five consecutive blocks. -/
def solverGuardTablesContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k heap,args=[ipmRangeExponent m U,ipmLimbs m U,ipmPrecision m U,
      k,Num.IPM.alphaExponent m U,heap] ∧ 2≤m*U ∧ k≤slackRangeExponent m U ∧
      ipmParameterWordBits m U≤w)
    (fun args _ mem' => SolverGuardTablesAt mem' (heapArg args) (args.getD 0 0) (args.getD 1 0)
      (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
    (fun args _ => 36*args.getD 1 0+640) (fun args _ => 5*args.getD 1 0)
  { C with post := fun args mem out final => C.post args mem out final ∧
      out=heapArg args+5*args.getD 1 0 }

/-- The guard-table entry contains only deterministic calls and a return. -/
theorem solverGuardTablesBody_noRand (constants normalization : ℕ) :
    (solverGuardTablesBody constants normalization).NoRand := by
  simp [solverGuardTablesBody,Stmt.NoRand]

set_option maxHeartbeats 320000 in
/-- The signed guards and the dyadic request are computed at the actual
chosen precision, with exact allocation and additive word cost. -/
theorem solverGuardTables_meetsContract {w entry constants normalization : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverGuardTablesBody constants normalization))
    (hc : p.HasAt constants (signedGuardConstantsModule constants))
    (hn : p.HasAt normalization (normalizationModule normalization)) :
    MeetsContract w p entry (solverGuardTablesContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,k,heap,rfl,hsize,hk,hw⟩,hzero,hspace⟩ := hpre
  let R := ipmRangeExponent m U
  let L := ipmLimbs m U
  let P := ipmPrecision m U
  let j := Num.IPM.alphaExponent m U
  have hw' := ipm_parameter_words_fit m U hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hw'.1)
  have hcSpec := signedGuardConstants_meetsContract h16 hc
  have hnSpec := normalization_meetsContract h16 hn
  change ZeroFrom mem heap at hzero
  change heap+5*L<2^w at hspace
  have hR : R<2^w := hw'.2.2.2.1
  have hL : L<2^w := hw'.2.1
  have hP : P<2^w := hw'.2.2.1
  have hkW : k<2^w := hwords _ (by simp)
  have hjW : j<2^w := hwords _ (by simp [j])
  have hHeap : heap<2^w := by omega
  have hGP := guardConstants_pre_of_chosen_precision m U hw hzero (by omega : heap+3*L<2^w)
  obtain ⟨⟨_,_,_,_,he,hRP,hP2,hWidth,hWord⟩,_,_⟩ := hGP
  simp only [List.cons.injEq] at he
  obtain ⟨rfl,rfl,rfl,rfl,_⟩ := he
  apply runs_start_le
  unfold solverGuardTablesBody
  refine runs_seq_call_le hcSpec (vs:=[R,L,P,heap]) (by eval_expr) (by wram_words)
    ⟨⟨R,L,P,heap,rfl,hRP,hP2,hWidth,hWord⟩,hzero,by change heap+4*L<2^w; omega⟩ ?_
  intro mid mem₁ pos₁ out₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hMin,hMax,hQuarter,hNeg⟩,hMid⟩ := out₁
  change mid=heap+4*L at hMid
  subst mid
  have hMidW : heap+4*L<2^w := by omega
  have hNorm : dyadicNormalizationExponent k j≤P := by
    exact selected_normalization_exponent_le m U k hsize hk
  refine runs_seq_call_le hnSpec (vs:=[k,j,L,P,heap+4*L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨k,j,L,P,heap+4*L,rfl,hNorm,by omega⟩,hZero₁,
      by change heap+4*L+L<2^w; omega⟩
  intro out mem₂ pos₂ out₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hRequest⟩,hOut⟩ := out₂
  change out=heap+4*L+L at hOut
  change ∀ x<heap+4*L,mem₂ x=mem₁ x at hFrame₂
  change ScalarAt mem₂ (heap+4*L) 4 L P (1/(2:ℝ)^(dyadicNormalizationExponent k j)) at hRequest
  have hOutW : out<2^w := by omega
  have freeze (a : ℕ) (ha : a+L≤heap+4*L) (x : ℝ) (hx : ScalarAt mem₁ a 4 L P x) :
      ScalarAt mem₂ a 4 L P x :=
    ⟨Num.IPM.valid_frozen hFrame₂ ha hx.1,(Num.IPM.fixVal_frozen hFrame₂ ha).trans hx.2⟩
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · have ht : SolverGuardTablesAt mem₂ heap R L P k j :=
      ⟨freeze heap (by omega) _ hMin,freeze (heap+L) (by omega) _ hMax,
        freeze (heap+2*L) (by omega) _ hQuarter,freeze (heap+3*L) (by omega) _ hNeg,hRequest⟩
    have hframe : ∀ x<heap,mem₂ x=mem x := fun x hx =>
      (hFrame₂ x (by omega)).trans (hFrame₁ x hx)
    exact ⟨⟨show heap≤out by omega,show out≤heap+5*L by omega,hframe,hZero₂,ht⟩,
      show out=heap+5*L by omega⟩
  · simp only [solverGuardTablesContract,signedGuardConstantsContract,normalizationContract,
      heapContract,argsSize_cons,argsSize_nil,Expr.size_reg,List.getD_cons_succ,List.getD_cons_zero]
    omega

/-- The exact guard values are produced in five consecutive blocks. -/
def solverQualityGuardTablesContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k heap,args=[ipmQualityRangeExponent m U k,ipmQualityLimbs m U k,ipmQualityPrecision m U k,
      k,Num.IPM.alphaExponent m U,heap] ∧ 2≤m*U ∧
      ipmQualityParameterWordBits m U k≤w)
    (fun args _ mem' => SolverGuardTablesAt mem' (heapArg args) (args.getD 0 0) (args.getD 1 0)
      (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
    (fun args _ => 36*args.getD 1 0+640) (fun args _ => 5*args.getD 1 0)
  { C with post := fun args mem out final => C.post args mem out final ∧
      out=heapArg args+5*args.getD 1 0 }

set_option maxHeartbeats 320000 in
/-- The signed guards and the dyadic request are computed at the actual
chosen precision, with exact allocation and additive word cost. -/
theorem solverQualityGuardTables_meetsContract {w entry constants normalization : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverGuardTablesBody constants normalization))
    (hc : p.HasAt constants (signedGuardConstantsModule constants))
    (hn : p.HasAt normalization (normalizationModule normalization)) :
    MeetsContract w p entry (solverQualityGuardTablesContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,k,heap,rfl,hsize,hw⟩,hzero,hspace⟩ := hpre
  let R := ipmQualityRangeExponent m U k
  let L := ipmQualityLimbs m U k
  let P := ipmQualityPrecision m U k
  let j := Num.IPM.alphaExponent m U
  have hw' := ipm_quality_parameter_words_fit m U k hw
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hw'.1)
  have hcSpec := signedGuardConstants_meetsContract h16 hc
  have hnSpec := normalization_meetsContract h16 hn
  change ZeroFrom mem heap at hzero
  change heap+5*L<2^w at hspace
  have hR : R<2^w := hw'.2.2.2.1
  have hL : L<2^w := hw'.2.1
  have hP : P<2^w := hw'.2.2.1
  have hkW : k<2^w := hwords _ (by simp)
  have hjW : j<2^w := hwords _ (by simp [j])
  have hHeap : heap<2^w := by omega
  have hGP := guardConstants_pre_of_quality_precision m U k hw hzero (by omega : heap+3*L<2^w)
  obtain ⟨⟨_,_,_,_,he,hRP,hP2,hWidth,hWord⟩,_,_⟩ := hGP
  simp only [List.cons.injEq] at he
  obtain ⟨rfl,rfl,rfl,rfl,_⟩ := he
  apply runs_start_le
  unfold solverGuardTablesBody
  refine runs_seq_call_le hcSpec (vs:=[R,L,P,heap]) (by eval_expr) (by wram_words)
    ⟨⟨R,L,P,heap,rfl,hRP,hP2,hWidth,hWord⟩,hzero,by change heap+4*L<2^w; omega⟩ ?_
  intro mid mem₁ pos₁ out₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hMin,hMax,hQuarter,hNeg⟩,hMid⟩ := out₁
  change mid=heap+4*L at hMid
  subst mid
  have hMidW : heap+4*L<2^w := by omega
  have hNorm : dyadicNormalizationExponent k j≤P := by
    exact quality_normalization_exponent_le m U k hsize
  refine runs_seq_call_le hnSpec (vs:=[k,j,L,P,heap+4*L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨k,j,L,P,heap+4*L,rfl,hNorm,by omega⟩,hZero₁,
      by change heap+4*L+L<2^w; omega⟩
  intro out mem₂ pos₂ out₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hRequest⟩,hOut⟩ := out₂
  change out=heap+4*L+L at hOut
  change ∀ x<heap+4*L,mem₂ x=mem₁ x at hFrame₂
  change ScalarAt mem₂ (heap+4*L) 4 L P (1/(2:ℝ)^(dyadicNormalizationExponent k j)) at hRequest
  have hOutW : out<2^w := by omega
  have freeze (a : ℕ) (ha : a+L≤heap+4*L) (x : ℝ) (hx : ScalarAt mem₁ a 4 L P x) :
      ScalarAt mem₂ a 4 L P x :=
    ⟨Num.IPM.valid_frozen hFrame₂ ha hx.1,(Num.IPM.fixVal_frozen hFrame₂ ha).trans hx.2⟩
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · have ht : SolverGuardTablesAt mem₂ heap R L P k j :=
      ⟨freeze heap (by omega) _ hMin,freeze (heap+L) (by omega) _ hMax,
        freeze (heap+2*L) (by omega) _ hQuarter,freeze (heap+3*L) (by omega) _ hNeg,hRequest⟩
    have hframe : ∀ x<heap,mem₂ x=mem x := fun x hx =>
      (hFrame₂ x (by omega)).trans (hFrame₁ x hx)
    exact ⟨⟨show heap≤out by omega,show out≤heap+5*L by omega,hframe,hZero₂,ht⟩,
      show out=heap+5*L by omega⟩
  · simp only [solverQualityGuardTablesContract,signedGuardConstantsContract,normalizationContract,
      heapContract,argsSize_cons,argsSize_nil,Expr.size_reg,List.getD_cons_succ,List.getD_cons_zero]
    omega

end MinCostFlow.IPM.Machine
