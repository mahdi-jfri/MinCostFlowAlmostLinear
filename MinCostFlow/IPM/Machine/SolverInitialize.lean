module

public import MinCostFlow.IPM.Machine.SolverInitialBounds
public import MinCostFlow.IPM.Machine.PrecisionAlpha
public import MinCostFlow.IPM.Machine.InitialGraph
public import MinCostFlow.IPM.Machine.SolverDataStructures
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Initializing the bounded solver at the selected precision

The machine first builds the augmented graph of Lemma 4.12 (Chen et
al., arXiv:2203.00671v2, page 31). Its edge count determines the
precision for the subsequent midpoint flow. All three results remain
available below the returned heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Arguments `[input,heap]` with positive edge count. -/
def solverInitializeBody (penalty graph alpha flow : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 penalty [.reg 2] ;;
  .call 4 graph [.reg 0,.reg 3,.reg 1] ;;
  .assign 5 (.bin .add (.reg 1) (.bin .mul (.const 2) (.load (.reg 0)))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .call 7 alpha [.reg 6,.reg 3,.reg 4] ;;
  .call 8 flow [.reg 5,.load (.bin .add (.reg 4) (.const 5)),.load (.bin .add (.reg 4) (.const 4)),.reg 7] ;;
  .ret (.reg 8)

/-- Exact positions of the initial graph, precision record and flow. -/
def solverInitialPointers (J : Circulation) (heap : ℕ) : ℕ × ℕ × ℕ :=
  let graph := heap+2*J.n
  let param := graph+2+5*(solverAugmented J).m
  (graph,param,param+7+ipmLimbs (solverAugmented J).m (solverPenalty J.m))

/-- Workspace including the worst-case address of the graph routine. -/
def solverInitializeSpace (J : Circulation) : ℕ :=
  2+5*J.m+7*J.n+7+ipmLimbs (solverAugmented J).m (solverPenalty J.m)+
    4*((solverAugmented J).m*ipmLimbs (solverAugmented J).m (solverPenalty J.m))

/-- Startup cost for the graph scan, format selection, and midpoint table. -/
def solverInitializeCost (J : Circulation) : ℕ :=
  let M := (solverAugmented J).m
  let V := solverPenalty J.m
  300*J.m+400*J.n+M*(200*ipmLimbs M V+600)+20028*(M.size+V.size)+23000

/-- The exact graph, precision and starting flow, with standard heap framing. -/
def solverInitializeContract (w : ℕ) (J : Circulation) : Contract :=
  let I := solverAugmented J
  let V := solverPenalty J.m
  let L := ipmLimbs I.m V
  let P := ipmPrecision I.m V
  let C := heapContract w
    (fun args mem => ∃ a h,args=[a,h] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤h ∧ (∀ x∈J.solverWords,x<2^w) ∧ 0 < J.m ∧
      J.CostsBounded (J.m^10) ∧ (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) ∧
      V<2^w ∧ ipmParameterWordBits I.m V≤w)
    (fun args _ mem =>
      let (g,b,f) := solverInitialPointers J (heapArg args)
      ZeroLowerAt mem g I ∧ ListAt mem b (precisionWords I.m V) ∧
      mem (b+6)=Num.IPM.alphaExponent I.m V ∧
      ScalarAt mem (b+7) 4 L P (Num.IPM.alphaPrime I.m V) ∧
      ∀ e, ScalarAt mem (f+e.val*L) 4 L P (IPM.initialFlow J.toInstance (V:ℤ) e))
    (fun _ _ => solverInitializeCost J) (fun _ _ => solverInitializeSpace J)
  { C with post := fun args mem out final => C.post args mem out final ∧
      out=(solverInitialPointers J (heapArg args)).2.2+4*(I.m*L) }

theorem solverInitializeBody_noRand (penalty graph alpha flow : ℕ) :
    (solverInitializeBody penalty graph alpha flow).NoRand := by
  simp [solverInitializeBody,Stmt.NoRand]

set_option maxHeartbeats 350000 in
set_option maxRecDepth 4096 in
/-- The positive-size initialization runs on the bounded solver's actual
input words and leaves the prescribed flow in the selected fixed format. -/
theorem solverInitialize_meetsContract {w entry penalty graph alpha flow : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverInitializeBody penalty graph alpha flow))
    (hpen : MeetsContract w p penalty (solverPenaltyContract w))
    (hg : p.HasAt graph (initialGraphModule graph))
    (ha : p.HasAt alpha (precisionAlphaModule alpha))
    (hf : p.HasAt flow (initialFlowModule flow 4))
    (J : Circulation) :
    MeetsContract w p entry (solverInitializeContract w J) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hm,hcost,hcap,hVword,hw⟩,hzero,hspace⟩ := hpre
  let V := solverPenalty J.m
  let U := solverCapacityBound J.m
  let I := solverAugmented J
  let M := I.m
  let L := ipmLimbs M V
  let P := ipmPrecision M V
  let g := heap+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  have hpos : ∀ e,1 ≤ J.capacity e := fun e => (hcap e).1
  obtain ⟨hupper,hcostU⟩ := solverCapacityBound_input J hm hcost (fun e => (hcap e).2)
  have hU : 2 ≤ U := le_max_left _ _
  have hpenEq : initialPenaltyWord J U = V := rfl
  have htotal := (total_capacity_le_penalty J U hm hU hupper).trans_lt (show initialPenaltyWord J U < 2^w by exact hVword)
  have hM : 0 < M := hm.trans_le (solverAugmented_size J hpos).1
  have hV : 2 ≤ V := by
    have hv := (initialPenaltyWord_intermediates J U hm hU).2.1
    rw [hpenEq] at hv
    omega
  have hsize : 2 ≤ M*V := hV.trans (by simpa only [Nat.one_mul] using
    (Nat.mul_le_mul_right V (show 1 ≤ M from hM)))
  have hword := ipm_parameter_words_fit M V hw
  have hconst : 5 < 2^w := (by decide : 5 < 2^14).trans_le (Nat.pow_le_pow_right (by decide) hword.1)
  have hLw : L < 2^w := hword.2.1
  have hPw : P < 2^w := hword.2.2.1
  have hPrec : 1 ≤ P := by unfold P ipmPrecision; omega
  have hh := twice_capacity_le_dyadic M V hM (by omega)
  have hVnonneg : (0:ℝ) ≤ (V:ℝ) := Nat.cast_nonneg _
  have hR : (V:ℝ) ≤ (2:ℝ)^(ipmRangeExponent M V) := by
    refine (show (V:ℝ) ≤ (2:ℝ)^(slackRangeExponent M V) by
      linarith only [hh,hVnonneg]).trans (pow_le_pow_right₀ (by norm_num) ?_)
    unfold ipmRangeExponent
    omega
  have hF := fits_integer_at_chosen_precision M V (V:ℤ) (by
    simpa only [Int.cast_natCast,abs_of_nonneg hVnonneg] using hR)
  have hScaled : Num.Fits 4 L ((V:ℤ)*(2:ℤ)^(P-1)) := by
    refine fits_of_nonneg_le 4 L _ _ (by positivity) ?_ hF.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)
  have hGraph := initialGraph_meetsContract hconst hg J
  have hAlpha := precisionAlpha_meetsContract (w:=w) ha
  have hFlow := initialFlow_meetsContract (by decide : 0 < 4) (by have := hword.1; omega : 2*4+2≤w)
    hconst hf J (V:ℤ)
  have hValid : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hlen : (zeroLowerWords I).length=2+5*M := zeroLowerWords_length I hValid
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hmw := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  rw [J.solverWords_length] at hend
  have hb₀ : 2+5*M ≤ 2+5*J.m+5*J.n := by
    have hAux : (deficitVertices J.toInstance).card ≤ J.n := (Finset.card_filter_le _ _).trans (by simp)
    change 2+5*(initialInstance J.toInstance (V:ℤ)).m ≤ _
    rw [initialInstance_m,freeEdges_circulation J hpos,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
    omega
  change heap+(2+5*J.m+7*J.n+7+L+4*(M*L))<2^w at hspace
  have hfSpace : f+4*(M*L)<2^w := by dsimp [f,b,g]; omega
  have hbW : b<2^w := by dsimp [f] at hfSpace; omega
  have hgW : g+1<2^w := by dsimp [b] at hbW; omega
  have hgEq : heap+2*J.n=g := rfl
  have hheap : heap<2^w := by omega
  have ha1 : a+1 < 2^w := by omega
  have haW : a<2^w := by omega
  have hmW : J.m<2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hMW : M<2^w := by dsimp [b] at hbW; omega
  apply runs_start_le
  unfold solverInitializeBody
  refine runs_seq_assign_le (v:=J.m) (by eval_expr) ?_
  refine runs_seq_call_le hpen (vs:=[J.m]) (by eval_expr) (by wram_words)
    ⟨J.m,rfl,hm,hVword⟩ ?_
  intro v₀ mem₀ pos₀ h₀
  change mem₀=mem ∧ v₀=V at h₀
  obtain ⟨hMem₀,hV₀⟩ := h₀
  subst mem₀ v₀
  refine runs_seq_call_le hGraph (vs:=[a,V,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,V,heap,rfl,hm,hat,by simpa only [J.solverWords_length] using hend,hinput,hpos,htotal⟩,hzero,
      by change heap+(2+5*J.m+7*J.n)<2^w; omega⟩
  intro v₁ mem₁ pos₁ h₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hGraphAt⟩,hEnd₁⟩ := h₁
  change v₁=b at hEnd₁
  change ZeroLowerAt mem₁ g I at hGraphAt
  subst v₁
  change ∀ x<heap,mem₁ x=mem x at hFrame₁
  have hn₁ : mem₁ a = J.n := (hFrame₁ a (by have hl := J.solverWords_length; omega)).trans hn
  have hM₁ : mem₁ (g+1)=M := (zeroLower_header_at I hValid mem₁ g hGraphAt.2.2).2
  have h2n : 2*J.n<2^w := by dsimp [g] at hgW; omega
  refine runs_seq_assign_le (v:=g) (by change _ = some (heap+2*J.n); eval_expr) ?_
  refine runs_seq_assign_le (v:=M) (by eval_expr) ?_
  refine runs_seq_call_le hAlpha (vs:=[M,V,b]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨M,V,b,rfl,hsize,hw⟩,hZero₁,
      by change b+(7+L)<2^w; dsimp [f] at hfSpace; omega⟩
  intro v₂ mem₂ pos₂ h₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hRecord,hExp,hAlphaAt⟩,hEnd₂⟩ := h₂
  change v₂=f at hEnd₂
  change ListAt mem₂ b (precisionWords M V) at hRecord
  change ∀ x<b, mem₂ x=mem₁ x at hFrame₂
  subst v₂
  have hLmem : mem₂ (b+5)=L := hRecord 5 (by change 5<6; decide)
  have hPmem : mem₂ (b+4)=P := hRecord 4 (by change 4<6; decide)
  have hb4 : b+4<2^w := by dsimp [f] at hfSpace; omega
  have hb5 : b+5<2^w := by dsimp [f] at hfSpace; omega
  have hfW : f<2^w := by omega
  have hGend : g+(zeroLowerWords I).length ≤ b := by rw [hlen]; dsimp [b]; omega
  have hG₂ : ZeroLowerAt mem₂ g I :=
    ⟨hGraphAt.1,hGraphAt.2.1,hGraphAt.2.2.of_agree_below hGend hFrame₂⟩
  refine runs_seq_call_le hFlow (vs:=[g,L,P,f]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨⟨g,L,P,f,rfl,hm,hpos,hPrec,hG₂,?_,?_⟩,hZero₂,hfSpace⟩
    · exact hGend.trans (by dsimp [f]; omega)
    · intro e
      have hcap₁ := initial_capacity_le_penalty J U hm hU hupper hcostU
      have hfit₁ := initial_capacity_fits J U 4 L P hm hU hupper hcostU
      rw [hpenEq] at hcap₁ hfit₁
      exact ⟨(hcap₁ e).trans_lt hVword,hfit₁ hF.1 hScaled e⟩
  intro out final endPos h₃
  obtain ⟨⟨_,_,hFrame₃,hZero₃,hFlowAt⟩,hEnd₃⟩ := h₃
  change out=f+4*(M*L) at hEnd₃
  change ScalarAt mem₂ (b+7) 4 L P (Num.IPM.alphaPrime M V) at hAlphaAt
  change ∀ x<f, final x=mem₂ x at hFrame₃
  have hout : out<2^w := hEnd₃ ▸ hfSpace
  have hbHeap : heap≤b := by dsimp [b,g]; omega
  have hbf : b≤f := by dsimp [f]; omega
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · refine ⟨⟨show heap≤out by omega,?_,?_,hZero₃,?_,?_,?_,?_,hFlowAt⟩,hEnd₃⟩
    · change out≤heap+(2+5*J.m+7*J.n+7+L+4*(M*L))
      dsimp [f,b,g] at hEnd₃
      omega
    · intro x hx
      change x<heap at hx
      exact (hFrame₃ x (by omega)).trans ((hFrame₂ x (by omega)).trans (hFrame₁ x hx))
    · exact ⟨hG₂.1,hG₂.2.1,hG₂.2.2.of_agree_below (hGend.trans hbf) hFrame₃⟩
    · exact hRecord.of_agree_below (by change b+6≤f; dsimp [f]; omega) hFrame₃
    · exact (hFrame₃ (b+6) (by dsimp [f]; omega)).trans hExp
    · have he : b+7+L≤f := le_rfl
      exact ⟨Num.IPM.valid_frozen hFrame₃ he hAlphaAt.1,
        (Num.IPM.fixVal_frozen hFrame₃ he).trans hAlphaAt.2⟩
  · simp only [solverInitializeContract,solverInitializeCost,solverPenaltyContract,initialGraphContract,
      precisionAlphaContract,initialFlowContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_const,Expr.size_reg,Expr.size_bin,Expr.size_load,List.getD_cons_zero,List.getD_cons_succ]
    dsimp [M,I,solverAugmented,V,L]
    omega

/-- Arguments `[input,heap]` with positive edge count. -/
def solverQualityInitializeBody (quality penalty graph alpha flow : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 penalty [.reg 2] ;;
  .call 4 graph [.reg 0,.reg 3,.reg 1] ;;
  .assign 5 (.bin .add (.reg 1) (.bin .mul (.const 2) (.load (.reg 0)))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .call 9 quality [.reg 6] ;;
  .call 7 alpha [.reg 6,.reg 3,.reg 9,.reg 4] ;;
  .call 8 flow [.reg 5,.load (.bin .add (.reg 4) (.const 5)),.load (.bin .add (.reg 4) (.const 4)),.reg 7] ;;
  .ret (.reg 8)

/-- Exact positions of the initial graph, precision record and flow. -/
def solverQualityInitialPointers (J : Circulation) (k heap : ℕ) : ℕ × ℕ × ℕ :=
  let graph := heap+2*J.n
  let param := graph+2+5*(solverAugmented J).m
  (graph,param,param+7+ipmQualityLimbs (solverAugmented J).m (solverPenalty J.m) k)

/-- Workspace including the worst-case address of the graph routine. -/
def solverQualityInitializeSpace (J : Circulation) (k : ℕ) : ℕ :=
  2+5*J.m+7*J.n+7+ipmQualityLimbs (solverAugmented J).m (solverPenalty J.m) k+
    4*((solverAugmented J).m*ipmQualityLimbs (solverAugmented J).m (solverPenalty J.m) k)

/-- Startup cost for the graph scan, format selection, and midpoint table. -/
def solverQualityInitializeCost (J : Circulation) (k charge : ℕ) : ℕ :=
  let M := (solverAugmented J).m
  let V := solverPenalty J.m
  300*J.m+400*J.n+M*(200*ipmQualityLimbs M V k+600)+20028*(M.size+V.size)+23020+charge

/-- The exact graph, precision and starting flow, with standard heap framing. -/
def solverQualityInitializeContract (w : ℕ) (J : Circulation) (k charge : ℕ) : Contract :=
  let I := solverAugmented J
  let V := solverPenalty J.m
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let C := heapContract w
    (fun args mem => ∃ a h,args=[a,h] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤h ∧ (∀ x∈J.solverWords,x<2^w) ∧ 0 < J.m ∧
      J.CostsBounded (J.m^10) ∧ (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) ∧
      V<2^w ∧ ipmQualityParameterWordBits I.m V k≤w)
    (fun args _ mem =>
      let (g,b,f) := solverQualityInitialPointers J k (heapArg args)
      ZeroLowerAt mem g I ∧ ListAt mem b (qualityPrecisionWords I.m V k) ∧
      mem (b+6)=Num.IPM.alphaExponent I.m V ∧
      ScalarAt mem (b+7) 4 L P (Num.IPM.alphaPrime I.m V) ∧
      ∀ e, ScalarAt mem (f+e.val*L) 4 L P (IPM.initialFlow J.toInstance (V:ℤ) e))
    (fun _ _ => solverQualityInitializeCost J k charge) (fun _ _ => solverQualityInitializeSpace J k)
  { C with post := fun args mem out final => C.post args mem out final ∧
      out=(solverQualityInitialPointers J k (heapArg args)).2.2+4*(I.m*L) }

theorem solverQualityInitializeBody_noRand (quality penalty graph alpha flow : ℕ) :
    (solverQualityInitializeBody quality penalty graph alpha flow).NoRand := by
  simp [solverQualityInitializeBody,Stmt.NoRand]

set_option maxHeartbeats 350000 in
set_option maxRecDepth 4096 in
/-- The positive-size initialization runs on the bounded solver's actual
input words and leaves the prescribed flow in the selected fixed format. -/
theorem solverQualityInitialize_meetsContract {w entry quality penalty graph alpha flow : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverQualityInitializeBody quality penalty graph alpha flow))
    (hpen : MeetsContract w p penalty (solverPenaltyContract w))
    (hg : p.HasAt graph (initialGraphModule graph))
    (ha : p.HasAt alpha (qualityPrecisionAlphaModule alpha))
    (hf : p.HasAt flow (initialFlowModule flow 4))
    (J : Circulation) (qualityExponent charge : ℕ → ℕ)
    (hQuality : MeetsContract w p quality (solverQualityContract w qualityExponent charge))
    (hQualityWord : qualityExponent (solverAugmented J).m < 2^w) :
    MeetsContract w p entry (solverQualityInitializeContract w J
      (qualityExponent (solverAugmented J).m) (charge (solverAugmented J).m)) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hm,hcost,hcap,hVword,hw⟩,hzero,hspace⟩ := hpre
  let V := solverPenalty J.m
  let U := solverCapacityBound J.m
  let I := solverAugmented J
  let M := I.m
  let k := qualityExponent M
  let L := ipmQualityLimbs M V k
  let P := ipmQualityPrecision M V k
  let g := heap+2*J.n
  let b := g+2+5*M
  let f := b+7+L
  have hpos : ∀ e,1 ≤ J.capacity e := fun e => (hcap e).1
  obtain ⟨hupper,hcostU⟩ := solverCapacityBound_input J hm hcost (fun e => (hcap e).2)
  have hU : 2 ≤ U := le_max_left _ _
  have hpenEq : initialPenaltyWord J U = V := rfl
  have htotal := (total_capacity_le_penalty J U hm hU hupper).trans_lt (show initialPenaltyWord J U < 2^w by exact hVword)
  have hM : 0 < M := hm.trans_le (solverAugmented_size J hpos).1
  have hV : 2 ≤ V := by
    have hv := (initialPenaltyWord_intermediates J U hm hU).2.1
    rw [hpenEq] at hv
    omega
  have hsize : 2 ≤ M*V := hV.trans (by simpa only [Nat.one_mul] using
    (Nat.mul_le_mul_right V (show 1 ≤ M from hM)))
  have hword := ipm_quality_parameter_words_fit M V k hw
  have hconst : 5 < 2^w := (by decide : 5 < 2^14).trans_le (Nat.pow_le_pow_right (by decide) hword.1)
  have hLw : L < 2^w := hword.2.1
  have hPw : P < 2^w := hword.2.2.1
  have hPrec : 1 ≤ P := by unfold P ipmQualityPrecision; omega
  have hh := twice_capacity_le_dyadic M V hM (by omega)
  have hVnonneg : (0:ℝ) ≤ (V:ℝ) := Nat.cast_nonneg _
  have hR : (V:ℝ) ≤ (2:ℝ)^(ipmQualityRangeExponent M V k) := by
    refine (show (V:ℝ) ≤ (2:ℝ)^(slackRangeExponent M V) by
      linarith only [hh,hVnonneg]).trans (pow_le_pow_right₀ (by norm_num) ?_)
    have hs := slackRangeExponent_le_qualitySlackExponent M V k
    unfold ipmQualityRangeExponent
    omega
  have hF := fits_integer_at_quality_precision M V k (V:ℤ) (by
    simpa only [Int.cast_natCast,abs_of_nonneg hVnonneg] using hR)
  have hScaled : Num.Fits 4 L ((V:ℤ)*(2:ℤ)^(P-1)) := by
    refine fits_of_nonneg_le 4 L _ _ (by positivity) ?_ hF.2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)
  have hGraph := initialGraph_meetsContract hconst hg J
  have hAlpha := qualityPrecisionAlpha_meetsContract (w:=w) ha
  have hFlow := initialFlow_meetsContract (by decide : 0 < 4) (by have := hword.1; omega : 2*4+2≤w)
    hconst hf J (V:ℤ)
  have hValid : I.IsValid := initialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hlen : (zeroLowerWords I).length=2+5*M := zeroLowerWords_length I hValid
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hmw := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  rw [J.solverWords_length] at hend
  have hb₀ : 2+5*M ≤ 2+5*J.m+5*J.n := by
    have hAux : (deficitVertices J.toInstance).card ≤ J.n := (Finset.card_filter_le _ _).trans (by simp)
    change 2+5*(initialInstance J.toInstance (V:ℤ)).m ≤ _
    rw [initialInstance_m,freeEdges_circulation J hpos,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
    omega
  change heap+(2+5*J.m+7*J.n+7+L+4*(M*L))<2^w at hspace
  have hfSpace : f+4*(M*L)<2^w := by dsimp [f,b,g]; omega
  have hbW : b<2^w := by dsimp [f] at hfSpace; omega
  have hgW : g+1<2^w := by dsimp [b] at hbW; omega
  have hgEq : heap+2*J.n=g := rfl
  have hheap : heap<2^w := by omega
  have ha1 : a+1 < 2^w := by omega
  have haW : a<2^w := by omega
  have hmW : J.m<2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hMW : M<2^w := by dsimp [b] at hbW; omega
  apply runs_start_le
  unfold solverQualityInitializeBody
  refine runs_seq_assign_le (v:=J.m) (by eval_expr) ?_
  refine runs_seq_call_le hpen (vs:=[J.m]) (by eval_expr) (by wram_words)
    ⟨J.m,rfl,hm,hVword⟩ ?_
  intro v₀ mem₀ pos₀ h₀
  change mem₀=mem ∧ v₀=V at h₀
  obtain ⟨hMem₀,hV₀⟩ := h₀
  subst mem₀ v₀
  refine runs_seq_call_le hGraph (vs:=[a,V,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,V,heap,rfl,hm,hat,by simpa only [J.solverWords_length] using hend,hinput,hpos,htotal⟩,hzero,
      by change heap+(2+5*J.m+7*J.n)<2^w; omega⟩
  intro v₁ mem₁ pos₁ h₁
  obtain ⟨⟨_,_,hFrame₁,hZero₁,hGraphAt⟩,hEnd₁⟩ := h₁
  change v₁=b at hEnd₁
  change ZeroLowerAt mem₁ g I at hGraphAt
  subst v₁
  change ∀ x<heap,mem₁ x=mem x at hFrame₁
  have hn₁ : mem₁ a = J.n := (hFrame₁ a (by have hl := J.solverWords_length; omega)).trans hn
  have hM₁ : mem₁ (g+1)=M := (zeroLower_header_at I hValid mem₁ g hGraphAt.2.2).2
  have h2n : 2*J.n<2^w := by dsimp [g] at hgW; omega
  refine runs_seq_assign_le (v:=g) (by change _ = some (heap+2*J.n); eval_expr) ?_
  refine runs_seq_assign_le (v:=M) (by eval_expr) ?_
  have hk : k<2^w := hQualityWord
  refine runs_seq_call_le hQuality (vs:=[M]) (by eval_expr) (by wram_words) ⟨M,rfl,hk⟩ ?_
  intro kval memQ posQ hQ
  change memQ=mem₁ ∧ kval=k at hQ
  obtain ⟨hmQ,hkQ⟩ := hQ
  subst memQ kval
  refine runs_seq_call_le hAlpha (vs:=[M,V,k,b]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨M,V,k,b,rfl,hsize,hw⟩,hZero₁,
      by change b+(7+L)<2^w; dsimp [f] at hfSpace; omega⟩
  intro v₂ mem₂ pos₂ h₂
  obtain ⟨⟨_,_,hFrame₂,hZero₂,hRecord,hExp,hAlphaAt⟩,hEnd₂⟩ := h₂
  change v₂=f at hEnd₂
  change ListAt mem₂ b (qualityPrecisionWords M V k) at hRecord
  change ∀ x<b, mem₂ x=mem₁ x at hFrame₂
  subst v₂
  have hLmem : mem₂ (b+5)=L := hRecord 5 (by change 5<6; decide)
  have hPmem : mem₂ (b+4)=P := hRecord 4 (by change 4<6; decide)
  have hb4 : b+4<2^w := by dsimp [f] at hfSpace; omega
  have hb5 : b+5<2^w := by dsimp [f] at hfSpace; omega
  have hfW : f<2^w := by omega
  have hGend : g+(zeroLowerWords I).length ≤ b := by rw [hlen]; dsimp [b]; omega
  have hG₂ : ZeroLowerAt mem₂ g I :=
    ⟨hGraphAt.1,hGraphAt.2.1,hGraphAt.2.2.of_agree_below hGend hFrame₂⟩
  refine runs_seq_call_le hFlow (vs:=[g,L,P,f]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨⟨g,L,P,f,rfl,hm,hpos,hPrec,hG₂,?_,?_⟩,hZero₂,hfSpace⟩
    · exact hGend.trans (by dsimp [f]; omega)
    · intro e
      have hcap₁ := initial_capacity_le_penalty J U hm hU hupper hcostU
      have hfit₁ := initial_capacity_fits J U 4 L P hm hU hupper hcostU
      rw [hpenEq] at hcap₁ hfit₁
      exact ⟨(hcap₁ e).trans_lt hVword,hfit₁ hF.1 hScaled e⟩
  intro out final endPos h₃
  obtain ⟨⟨_,_,hFrame₃,hZero₃,hFlowAt⟩,hEnd₃⟩ := h₃
  change out=f+4*(M*L) at hEnd₃
  change ScalarAt mem₂ (b+7) 4 L P (Num.IPM.alphaPrime M V) at hAlphaAt
  change ∀ x<f, final x=mem₂ x at hFrame₃
  have hout : out<2^w := hEnd₃ ▸ hfSpace
  have hbHeap : heap≤b := by dsimp [b,g]; omega
  have hbf : b≤f := by dsimp [f]; omega
  refine runs_ret_le (v:=out) (by eval_expr) ?_ ?_
  · refine ⟨⟨show heap≤out by omega,?_,?_,hZero₃,?_,?_,?_,?_,hFlowAt⟩,hEnd₃⟩
    · change out≤heap+(2+5*J.m+7*J.n+7+L+4*(M*L))
      dsimp [f,b,g] at hEnd₃
      omega
    · intro x hx
      change x<heap at hx
      exact (hFrame₃ x (by omega)).trans ((hFrame₂ x (by omega)).trans (hFrame₁ x hx))
    · exact ⟨hG₂.1,hG₂.2.1,hG₂.2.2.of_agree_below (hGend.trans hbf) hFrame₃⟩
    · exact hRecord.of_agree_below (by change b+6≤f; dsimp [f]; omega) hFrame₃
    · exact (hFrame₃ (b+6) (by dsimp [f]; omega)).trans hExp
    · have he : b+7+L≤f := le_rfl
      exact ⟨Num.IPM.valid_frozen hFrame₃ he hAlphaAt.1,
        (Num.IPM.fixVal_frozen hFrame₃ he).trans hAlphaAt.2⟩
  · simp only [solverQualityInitializeContract,solverQualityInitializeCost,solverPenaltyContract,initialGraphContract,
      solverQualityContract,qualityPrecisionAlphaContract,initialFlowContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_const,Expr.size_reg,Expr.size_bin,Expr.size_load,List.getD_cons_zero,List.getD_cons_succ]
    dsimp [M,I,solverAugmented,V,L,k]
    omega

end MinCostFlow.IPM.Machine
