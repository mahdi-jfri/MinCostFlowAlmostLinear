module

public import MinCostFlow.IPM.Machine.SolverInitialize
public import MinCostFlow.IPM.Machine.ConnectedGraph
public import MinCostFlow.IPM.Machine.ConnectedMidpoint
import MinCostFlow.IPM.ConnectedInitialRecovery
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Starting the bounded IPM on the connected graph

The graph-building call emits the connected augmentation. Its header
drives the same quality and precision calls as before, and the
midpoint loader reads the capacity of each emitted edge.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The connected instance at the bounded solver's original penalty. -/
def solverConnectedAugmented (J : Circulation) : Instance :=
  connectedInitialInstance J.toInstance (solverPenalty J.m : ℤ)

/-- The connected graph has linear size for a compressed solver input. -/
theorem solverConnectedAugmented_size (J : Circulation) (hn : J.n ≤ 2*J.m+1)
    (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    J.m ≤ (solverConnectedAugmented J).m ∧ (solverConnectedAugmented J).m ≤ 7*J.m := by
  refine ⟨connectedInitial_circulation_m_ge J hp _, ?_⟩
  have hs := connectedInitialInstance_m_le J.toInstance (solverPenalty J.m : ℤ)
  rw [Circulation.toInstance_m] at hs
  change (solverConnectedAugmented J).m ≤ J.m+2*J.n at hs
  omega

private theorem connected_capacity_le_penalty (J : Circulation) (U : ℕ)
    (hm : 0 < J.m) (hU : 2 ≤ U) (hcap : ∀ e, J.capacity e ≤ U) (hcost : J.CostsBounded U)
    (e : Fin (connectedInitialInstance J.toInstance (initialPenaltyWord J U : ℤ)).m) :
    ((connectedInitialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper.toNat ≤
      initialPenaltyWord J U := by
  have hnums := circulation_numbersBounded J U hcap hcost
  have heq : ((initialPenaltyWord J U : ℤ) : ℝ) = 4*J.toInstance.m*(U : ℝ)^2 := by
    simp [initialPenaltyWord,Circulation.toInstance_m]
  have hK : |((initialPenaltyWord J U : ℤ) : ℝ)| ≤ 4*J.toInstance.m*(U : ℝ)^2 := by
    rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le (initialPenaltyWord J U))),heq]
  have hn := connectedInitialInstance_numbers J.toInstance (U : ℝ) (initialPenaltyWord J U : ℤ)
    (by simpa only [Circulation.toInstance_m] using hm)
    (by exact_mod_cast (show 1 ≤ U by omega)) hnums hK
  have hb : (((connectedInitialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper : ℝ) ≤
      ((initialPenaltyWord J U : ℤ) : ℝ) := by
    rw [heq]
    exact (le_abs_self _).trans (hn.2 e).2.1
  have hbi : ((connectedInitialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper ≤
      (initialPenaltyWord J U : ℤ) := by exact_mod_cast hb
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hbi

/-- Exact positions of the initial graph, precision record and flow. -/
def connectedSolverInitialPointers (J : Circulation) (k heap : ℕ) : ℕ × ℕ × ℕ :=
  let graph := heap+2*J.n
  let param := graph+2+5*(solverConnectedAugmented J).m
  (graph,param,param+7+ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m) k)

/-- Workspace including the worst-case address of the graph routine. -/
def connectedSolverInitializeSpace (J : Circulation) (k : ℕ) : ℕ :=
  2+5*J.m+17*J.n+7+ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m) k+
    4*((solverConnectedAugmented J).m*ipmQualityLimbs (solverConnectedAugmented J).m (solverPenalty J.m) k)

/-- Startup cost for the graph scan, format selection, and midpoint table. -/
def connectedSolverInitializeCost (J : Circulation) (k charge : ℕ) : ℕ :=
  let M := (solverConnectedAugmented J).m
  let V := solverPenalty J.m
  300*J.m+900*J.n+M*(200*ipmQualityLimbs M V k+600)+20028*(M.size+V.size)+23420+charge

/-- The exact graph, precision and starting flow, with standard heap framing. -/
def connectedSolverInitializeContract (w : ℕ) (J : Circulation) (k charge : ℕ) : Contract :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let C := heapContract w
    (fun args mem => ∃ a h,args=[a,h] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤h ∧ (∀ x∈J.solverWords,x<2^w) ∧ 0 < J.m ∧
      J.CostsBounded (J.m^10) ∧ (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) ∧
      V<2^w ∧ ipmQualityParameterWordBits I.m V k≤w)
    (fun args _ mem =>
      let (g,b,f) := connectedSolverInitialPointers J k (heapArg args)
      ZeroLowerAt mem g I ∧ ListAt mem b (qualityPrecisionWords I.m V k) ∧
      mem (b+6)=Num.IPM.alphaExponent I.m V ∧
      ScalarAt mem (b+7) 4 L P (Num.IPM.alphaPrime I.m V) ∧
      ∀ e, ScalarAt mem (f+e.val*L) 4 L P (connectedInitialFlow J.toInstance (V:ℤ) e))
    (fun _ _ => connectedSolverInitializeCost J k charge) (fun _ _ => connectedSolverInitializeSpace J k)
  { C with post := fun args mem out final => C.post args mem out final ∧
      out=(connectedSolverInitialPointers J k (heapArg args)).2.2+4*(I.m*L) }

set_option maxHeartbeats 350000 in
set_option maxRecDepth 4096 in
/-- The positive-size initialization runs on the bounded solver's actual
input words and leaves the prescribed flow in the selected fixed format. -/
theorem connectedSolverInitialize_meetsContract {w entry quality penalty graph alpha flow : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverQualityInitializeBody quality penalty graph alpha flow))
    (hpen : MeetsContract w p penalty (solverPenaltyContract w))
    (hg : p.HasAt graph (connectedGraphModule graph))
    (ha : p.HasAt alpha (qualityPrecisionAlphaModule alpha))
    (hf : p.HasAt flow (initialFlowModule flow 4))
    (J : Circulation) (qualityExponent charge : ℕ → ℕ)
    (hQuality : MeetsContract w p quality (solverQualityContract w qualityExponent charge))
    (hQualityWord : qualityExponent (solverConnectedAugmented J).m < 2^w) :
    MeetsContract w p entry (connectedSolverInitializeContract w J
      (qualityExponent (solverConnectedAugmented J).m) (charge (solverConnectedAugmented J).m)) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hm,hcost,hcap,hVword,hw⟩,hzero,hspace⟩ := hpre
  let V := solverPenalty J.m
  let U := solverCapacityBound J.m
  let I := solverConnectedAugmented J
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
  have hM : 0 < M := hm.trans_le (connectedInitial_circulation_m_ge J hpos (V : ℤ))
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
  have hGraph := connectedGraph_meetsContract hconst hg J
  have hAlpha := qualityPrecisionAlpha_meetsContract (w:=w) ha
  have hFlow := connectedMidpoint_meetsContract (by decide : 0 < 4)
    (by have := hword.1; omega : 2*4+2≤w) hconst hf J hm hpos (V:ℤ)
  have hValid : I.IsValid := connectedInitialInstance_valid J.toInstance (V:ℤ) J.toInstance_valid
  have hlen : (zeroLowerWords I).length=2+5*M := zeroLowerWords_length I hValid
  have hn := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).1
  have hmw := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  rw [J.solverWords_length] at hend
  have hb₀ : 2+5*M ≤ 2+5*J.m+15*J.n := by
    have hs := (connectedInitialInstance_m_le J.toInstance (V : ℤ))
    rw [Circulation.toInstance_m] at hs
    change M ≤ J.m+2*J.n at hs
    omega
  change heap+(2+5*J.m+17*J.n+7+L+4*(M*L))<2^w at hspace
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
      by change heap+(2+5*J.m+17*J.n)<2^w; omega⟩
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
  · refine ⟨⟨g,L,P,f,rfl,hPrec,hG₂,?_,?_⟩,hZero₂,hfSpace⟩
    · exact hGend.trans (by dsimp [f]; omega)
    · intro e
      have hcap₁ := connected_capacity_le_penalty J U hm hU hupper hcostU
      rw [hpenEq] at hcap₁
      have hle : ((I.edge e).upper.toNat : ℤ) ≤ (V : ℤ) := by
        exact_mod_cast hcap₁ e
      refine ⟨(hcap₁ e).trans_lt hVword,
        fits_of_nonneg_le 4 L _ _ (Int.natCast_nonneg _) hle hF.1,
        fits_of_nonneg_le 4 L _ _ (mul_nonneg (Int.natCast_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right hle (by positivity)) hScaled⟩
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
    · change out≤heap+(2+5*J.m+17*J.n+7+L+4*(M*L))
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
  · simp only [connectedSolverInitializeContract,connectedSolverInitializeCost,solverPenaltyContract,connectedGraphContract,
      solverQualityContract,qualityPrecisionAlphaContract,midpointFlowContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_const,Expr.size_reg,Expr.size_bin,Expr.size_load,List.getD_cons_zero,List.getD_cons_succ]
    dsimp [M,I,solverConnectedAugmented,V,L,k]
    omega

end MinCostFlow.IPM.Machine
