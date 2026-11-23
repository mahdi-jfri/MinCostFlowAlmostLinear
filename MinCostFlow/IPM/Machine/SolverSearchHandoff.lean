module

public import MinCostFlow.IPM.Machine.SolverSearchInputs
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.Machine.InitialPolynomialSize
import MinCostFlow.IPM.Machine.PrecisionResidual
import MinCostFlow.IPM.Machine.NamedGraphLayout
import Mathlib.Tactic

/-!
# From initialization and shared tables to the first search test

The precise addresses of the initialized graph, midpoint flow and
constant tables give the fixed-input invariant of the IPM. The
half-slack bound of Lemma 4.12 gives the first test's strict range.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The five fixed-point guard blocks and coefficient tables satisfy the
static search invariant. The quarter block supplies the initial target
slot before binary search substitutes an actual target. -/
theorem solverSearchTables_fixed {w : ℕ} (I : Instance) (V k g a h : ℕ) (mem : ℕ → ℕ)
    (hw : ipmParameterWordBits I.m V≤w)
    (ht : SolverSearchTablesAt I V k g a h mem)
    (hI : I.IsValid) (hn : I.n<2^w) (hm : I.m<2^w)
    (hWords : ∀ x∈zeroLowerWords I,x<2^w)
    (hRow : g+(zeroLowerWords I).length≤h)
    (ha : a+ipmLimbs I.m V≤h)
    (hAlpha : ScalarAt mem a 4 (ipmLimbs I.m V) (ipmPrecision I.m V) (Num.IPM.alphaPrime I.m V)) :
    let L := ipmLimbs I.m V
    let E := ipmRangeExponent I.m V
    let t := h+solverSearchSetupSpace I L
    let old := solverEpochLayout I L E g a h
    let qp := old.slackMin+2*L
    let κ := (1:ℝ)/(2:ℝ)^k
    TargetFixedInputs (ipmMinRatioFormat I.m V hw) I old qp qp t (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem := by
  dsimp only
  let L := ipmLimbs I.m V
  let P := ipmPrecision I.m V
  let E := ipmRangeExponent I.m V
  let c := solverCoefficientBase I h
  let s := solverGuardBase I L h
  let t := h+solverSearchSetupSpace I L
  have hc : c=h+2+I.n+3*I.m := rfl
  have hs : s=c+9*(I.m*L)+L := by
    unfold s solverGuardBase
    change c+(9*I.m+1)*L=_
    ring
  have ht' : t=s+5*L := by unfold t s solverSearchSetupSpace solverGuardBase solverCoefficientBase; omega
  obtain ⟨hRows,hGraph,hArray,hOne,hMin,hMax,hQuarter,hNeg,hRequest⟩ := ht
  have hRequest' : ScalarAt mem (s+4*L) 4 L P
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) := by
    rw [mul_div_assoc]
    rw [Num.IPM.alphaPrime,←dyadicNormalization_eq]
    exact hRequest
  have hMin' : ScalarAt mem s 4 L P ((2:ℝ)^(-(E:ℤ))) := by
    rw [zpow_neg,zpow_natCast,←one_div]
    exact hMin
  refine ⟨hRows.2.2,?_,hWords,hGraph,?_,graphWords_namedInstance_words_fit I hI hn hm,
    ?_,?_,fun e => (hArray e).2.1,fun e => (hArray e).1,fun e => (hArray e).2.2,
    hAlpha,hOne,hQuarter,hQuarter,hMin,hMax,hRequest',hNeg,hMax,hMin'⟩
  · change g+(zeroLowerWords I).length≤t
    omega
  · rw [graphWords_namedInstance_length]
    change h+(2+I.n+3*I.m)≤t
    omega
  · intro p hp
    change p∈[c+I.m*L,c,c+5*(I.m*L)] at hp
    change p+I.m*L≤t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> omega
  · intro p hp
    change p∈[s+2*L,s+2*L,a,c+9*(I.m*L),s,s+L,s+4*L,s+3*L,s+L,s] at hp
    change p+L≤t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- At the initial midpoint the guarded slack ranges are strict and the
decoded starting flow is the exact Lemma 4.12 flow. -/
theorem solverInitialFlow_stage {w : ℕ} (J : Circulation) (V : ℕ) (source heap : ℕ)
    (mem : ℕ → ℕ) (hm : 0 < J.m) (hV : 0 < V) (hp : ∀ e,1≤J.capacity e)
    (hw : ipmParameterWordBits (initialInstance J.toInstance (V:ℤ)).m V≤w)
    (hEnd : source+(initialInstance J.toInstance (V:ℤ)).m*ipmLimbs (initialInstance J.toInstance (V:ℤ)).m V≤heap)
    (hNums : NumbersBounded (initialInstance J.toInstance (V:ℤ)) (V:ℝ))
    (hAt : ∀ e : Fin (initialInstance J.toInstance (V:ℤ)).m,
      ScalarAt mem (source+e.val*ipmLimbs (initialInstance J.toInstance (V:ℤ)).m V)
        4 (ipmLimbs (initialInstance J.toInstance (V:ℤ)).m V)
        (ipmPrecision (initialInstance J.toInstance (V:ℤ)).m V) (IPM.initialFlow J.toInstance (V:ℤ) e)) :
    let I := initialInstance J.toInstance (V:ℤ)
    let F := ipmMinRatioFormat I.m V hw
    TargetStageFlow F I F.rangeExponent source heap mem ∧
      ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e := by
  dsimp only
  let I := initialInstance J.toInstance (V:ℤ)
  let F := ipmMinRatioFormat I.m V hw
  let E := ipmRangeExponent I.m V
  let f := IPM.initialFlow J.toInstance (V:ℤ)
  have hM : 0 < I.m := hm.trans_le (circulation_augmented_m_ge J _ hp)
  have hEq : epochVector F I mem source=f := funext fun e => (hAt e).2
  have hFeas : I.IsFeasible f := by
    apply initialFlow_feasible J.toInstance (V:ℤ) J.toInstance_valid
    · intro e
      rw [Circulation.toInstance_edge]
      simp [Circulation.inputEdge]
    · simp [Instance.d]
  have hVE : slackRangeExponent I.m V≤E := by unfold E ipmRangeExponent; omega
  have hMon := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hVE
  have hlo : 1/(2:ℝ)^E < 1/2 :=
    ((one_div_le_one_div_of_le (by positivity) hMon).trans (dyadic_le_quarter I.m V hM hV)).trans_lt (by norm_num)
  have hv : (0:ℝ)<V := Nat.cast_pos.mpr hV
  have hhi : (V:ℝ)<(2:ℝ)^E := by
    have hb := (twice_capacity_le_dyadic I.m V hM hV).trans hMon
    linarith only [hb,hv]
  change TargetStageFlow F I E source heap mem ∧ _
  have hHalf := initialFlow_slacks J.toInstance (V:ℤ)
  refine ⟨⟨hEnd,hEq.symm ▸ hFeas,?_⟩,?_⟩
  · intro e
    rw [hEq]
    have hs := hHalf e
    have hU := (le_abs_self ((I.edge e).upper:ℝ)).trans (hNums.2 e).2.1
    have hL : (I.edge e).lower=0 := ((initialInstance_zeroLower J hp V).1 e).1
    have hf₀ : (0:ℝ)≤f e := by rw [hL,Int.cast_zero] at hs; linarith only [hs.1]
    refine ⟨(hAt e).1,⟨hlo.trans_le hs.2,?_⟩,⟨hlo.trans_le hs.1,?_⟩⟩
    · linarith only [hU,hhi,hf₀]
    · rw [hL,Int.cast_zero,sub_zero]
      exact (hFeas.2 e).2.trans_lt (hU.trans_lt hhi)
  · intro e
    rw [hEq]
    exact hHalf e

/-- The five fixed-point guard blocks and coefficient tables satisfy the
static search invariant. The quarter block supplies the initial target
slot before binary search substitutes an actual target. -/
theorem solverQualitySearchTables_fixed {w : ℕ} (I : Instance) (V k g a h : ℕ) (mem : ℕ → ℕ)
    (hw : ipmQualityParameterWordBits I.m V k≤w)
    (ht : SolverQualitySearchTablesAt I V k g a h mem)
    (hI : I.IsValid) (hn : I.n<2^w) (hm : I.m<2^w)
    (hWords : ∀ x∈zeroLowerWords I,x<2^w)
    (hRow : g+(zeroLowerWords I).length≤h)
    (ha : a+ipmQualityLimbs I.m V k≤h)
    (hAlpha : ScalarAt mem a 4 (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) (Num.IPM.alphaPrime I.m V)) :
    let L := ipmQualityLimbs I.m V k
    let E := ipmQualityRangeExponent I.m V k
    let t := h+solverSearchSetupSpace I L
    let old := solverEpochLayout I L E g a h
    let qp := old.slackMin+2*L
    let κ := (1:ℝ)/(2:ℝ)^k
    TargetFixedInputs (ipmQualityMinRatioFormat I.m V k hw) I old qp qp t (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem := by
  dsimp only
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let E := ipmQualityRangeExponent I.m V k
  let c := solverCoefficientBase I h
  let s := solverGuardBase I L h
  let t := h+solverSearchSetupSpace I L
  have hc : c=h+2+I.n+3*I.m := rfl
  have hs : s=c+9*(I.m*L)+L := by
    unfold s solverGuardBase
    change c+(9*I.m+1)*L=_
    ring
  have ht' : t=s+5*L := by unfold t s solverSearchSetupSpace solverGuardBase solverCoefficientBase; omega
  obtain ⟨hRows,hGraph,hArray,hOne,hMin,hMax,hQuarter,hNeg,hRequest⟩ := ht
  have hRequest' : ScalarAt mem (s+4*L) 4 L P
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) := by
    rw [mul_div_assoc]
    rw [Num.IPM.alphaPrime,←dyadicNormalization_eq]
    exact hRequest
  have hMin' : ScalarAt mem s 4 L P ((2:ℝ)^(-(E:ℤ))) := by
    rw [zpow_neg,zpow_natCast,←one_div]
    exact hMin
  refine ⟨hRows.2.2,?_,hWords,hGraph,?_,graphWords_namedInstance_words_fit I hI hn hm,
    ?_,?_,fun e => (hArray e).2.1,fun e => (hArray e).1,fun e => (hArray e).2.2,
    hAlpha,hOne,hQuarter,hQuarter,hMin,hMax,hRequest',hNeg,hMax,hMin'⟩
  · change g+(zeroLowerWords I).length≤t
    omega
  · rw [graphWords_namedInstance_length]
    change h+(2+I.n+3*I.m)≤t
    omega
  · intro p hp
    change p∈[c+I.m*L,c,c+5*(I.m*L)] at hp
    change p+I.m*L≤t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> omega
  · intro p hp
    change p∈[s+2*L,s+2*L,a,c+9*(I.m*L),s,s+L,s+4*L,s+3*L,s+L,s] at hp
    change p+L≤t
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- At the initial midpoint the guarded slack ranges are strict and the
decoded starting flow is the exact Lemma 4.12 flow. -/
theorem solverQualityInitialFlow_stage {w : ℕ} (J : Circulation) (V k : ℕ) (source heap : ℕ)
    (mem : ℕ → ℕ) (hm : 0 < J.m) (hV : 0 < V) (hp : ∀ e,1≤J.capacity e)
    (hw : ipmQualityParameterWordBits (initialInstance J.toInstance (V:ℤ)).m V k≤w)
    (hEnd : source+(initialInstance J.toInstance (V:ℤ)).m*ipmQualityLimbs (initialInstance J.toInstance (V:ℤ)).m V k≤heap)
    (hNums : NumbersBounded (initialInstance J.toInstance (V:ℤ)) (V:ℝ))
    (hAt : ∀ e : Fin (initialInstance J.toInstance (V:ℤ)).m,
      ScalarAt mem (source+e.val*ipmQualityLimbs (initialInstance J.toInstance (V:ℤ)).m V k)
        4 (ipmQualityLimbs (initialInstance J.toInstance (V:ℤ)).m V k)
        (ipmQualityPrecision (initialInstance J.toInstance (V:ℤ)).m V k) (IPM.initialFlow J.toInstance (V:ℤ) e)) :
    let I := initialInstance J.toInstance (V:ℤ)
    let F := ipmQualityMinRatioFormat I.m V k hw
    TargetStageFlow F I F.rangeExponent source heap mem ∧
      ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e := by
  dsimp only
  let I := initialInstance J.toInstance (V:ℤ)
  let F := ipmQualityMinRatioFormat I.m V k hw
  let E := ipmQualityRangeExponent I.m V k
  let f := IPM.initialFlow J.toInstance (V:ℤ)
  have hM : 0 < I.m := hm.trans_le (circulation_augmented_m_ge J _ hp)
  have hEq : epochVector F I mem source=f := funext fun e => (hAt e).2
  have hFeas : I.IsFeasible f := by
    apply initialFlow_feasible J.toInstance (V:ℤ) J.toInstance_valid
    · intro e
      rw [Circulation.toInstance_edge]
      simp [Circulation.inputEdge]
    · simp [Instance.d]
  have hVE : slackRangeExponent I.m V≤E := by
    have hs := slackRangeExponent_le_qualitySlackExponent I.m V k
    unfold E ipmQualityRangeExponent
    omega
  have hMon := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hVE
  have hlo : 1/(2:ℝ)^E < 1/2 :=
    ((one_div_le_one_div_of_le (by positivity) hMon).trans (dyadic_le_quarter I.m V hM hV)).trans_lt (by norm_num)
  have hv : (0:ℝ)<V := Nat.cast_pos.mpr hV
  have hhi : (V:ℝ)<(2:ℝ)^E := by
    have hb := (twice_capacity_le_dyadic I.m V hM hV).trans hMon
    linarith only [hb,hv]
  change TargetStageFlow F I E source heap mem ∧ _
  have hHalf := initialFlow_slacks J.toInstance (V:ℤ)
  refine ⟨⟨hEnd,hEq.symm ▸ hFeas,?_⟩,?_⟩
  · intro e
    rw [hEq]
    have hs := hHalf e
    have hU := (le_abs_self ((I.edge e).upper:ℝ)).trans (hNums.2 e).2.1
    have hL : (I.edge e).lower=0 := ((initialInstance_zeroLower J hp V).1 e).1
    have hf₀ : (0:ℝ)≤f e := by rw [hL,Int.cast_zero] at hs; linarith only [hs.1]
    refine ⟨(hAt e).1,⟨hlo.trans_le hs.2,?_⟩,⟨hlo.trans_le hs.1,?_⟩⟩
    · linarith only [hU,hhi,hf₀]
    · rw [hL,Int.cast_zero,sub_zero]
      exact (hFeas.2 e).2.trans_lt (hU.trans_lt hhi)
  · intro e
    rw [hEq]
    exact hHalf e

end MinCostFlow.IPM.Machine
