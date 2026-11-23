module

public import MinCostFlow.IPM.Machine.EpochCacheMovement
public import MinCostFlow.IPM.Machine.CoefficientRangeAdmissible
public import MinCostFlow.IPM.Machine.CheckedUpdateTransition
import MinCostFlow.IPM.Machine.CoefficientRangeReportOutput
import MinCostFlow.IPM.Machine.EpochMaterialization
import MinCostFlow.IPM.Machine.EpochInitialFlow
import Mathlib.Tactic.NormNum

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# Acceptance of an actual coefficient scan

The reported entries are evaluated at the current flow. Their exact
slacks determine the range margin from the potential. The scan compares
the stored fixed-point coefficients with that margin's endpoints.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The numerical error unit of any fixed-point coefficient pass
leaves a strict margin when the stored coordinates and residual
are in the potential-derived range. -/
theorem epoch_cache_coefficients_in_range (I : Instance) (U q : ℕ)
    (a r : ℝ) (stored : Fin I.m → ℝ) (e : Fin I.m) (g ell : ℝ)
    (ha0 : 0≤a) (ha1 : a≤1) (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hu : 1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-stored e ∧
      (I.edge e).upper-stored e≤(2:ℝ)^(slackRangeExponent I.m U))
    (hd : 1/(2:ℝ)^(slackRangeExponent I.m U)≤stored e-(I.edge e).lower ∧
      stored e-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U))
    (hl : ScalarApprox (1+1/(2:ℝ)^q) ell (lengths I a stored e))
    (hg : |g-gradientWithResidual I a r stored e|≤(1/(2:ℝ)^q)*lengths I a stored e) :
    |g|<(2:ℝ)^(ipmRangeExponent I.m U) ∧ 1/(2:ℝ)^(ipmRangeExponent I.m U)<ell ∧
      ell<(2:ℝ)^(ipmRangeExponent I.m U) := by
  have hpow : (1:ℝ)≤2^q := one_le_pow₀ (by norm_num)
  have hδ : 1/(2:ℝ)^q≤1 := (div_le_iff₀ (by positivity)).2 (by simpa only [one_mul] using hpow)
  have hb : 1+1/(2:ℝ)^q≤2 := by linarith only [hδ]
  have hbpos : 0<1+1/(2:ℝ)^q := by positivity
  have hinv : (2:ℝ)⁻¹≤(1+1/(2:ℝ)^q)⁻¹ := inv_anti₀ hbpos hb
  have hl' : ScalarApprox 2 (ell)
      (lengths I a stored e) :=
    ⟨hl.1,hl.2.1,(mul_le_mul_of_nonneg_right hinv hl.2.1.le).trans hl.2.2.1,
      hl.2.2.2.trans (mul_le_mul_of_nonneg_right hb hl.2.1.le)⟩
  have hg' := hg.trans ((mul_le_mul_of_nonneg_right hδ hl.2.1.le).trans_eq
    (one_mul (lengths I a stored e)))
  exact computed_epoch_coefficients_strict_range I U a r _ _ _ ha0 ha1 hnums e hu hd hr hl' hg'

/-- The numerical error budget (2^{-q}) under `P` puts each reported coefficient
strictly inside the selected range whenever the current slacks and held
residual have the potential-derived bounds. -/
theorem epoch_reported_coefficients_in_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (L : EpochLayout) (U q : ℕ) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (hG : D.G T=namedInstance I)
    (ha0 : 0≤a) (ha1 : a≤1) (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hcache : ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
        I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      |Num.fixVal mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|<
        (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)<
        Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        (2:ℝ)^(ipmRangeExponent I.m U) := by
  intro e he
  have heG := minRatio_valid_detect_subset_upTo_on A κ α Ψ eps hA D eta op T hvalid hsize hP he
  have heI : e∈(namedInstance I).E := hG ▸ heG
  let idx : Fin I.m := ⟨e,Finset.mem_range.mp heI⟩
  have hc := hcache e he
  obtain ⟨hl,hg,_⟩ := reportedCachePost_coefficients F I A L a r mem hsource q idx _ hc
  have hf : epochVector F I mem L.flow idx=
      epochHistoryFlow I A D eta op T (epochVector F I mem L.base) idx :=
    reportedCachePost_detect_flow_upTo_on F A κ α Ψ eps hA D eta op T hvalid hsize hP heG hc
  have hsl := hslacks idx
  dsimp only at hsl
  rw [← hf] at hsl
  exact epoch_cache_coefficients_in_range I U q a r _ idx _ _ ha0 ha1 hnums hr hsl.1 hsl.2 hl hg

/-- The numerical error budget (2^{-q}) puts each reported coefficient
strictly inside the selected range whenever the current slacks and held
residual have the potential-derived bounds. -/
theorem epoch_reported_coefficients_in_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (L : EpochLayout) (U q : ℕ) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (hG : D.G T=namedInstance I)
    (ha0 : 0≤a) (ha1 : a≤1) (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hcache : ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
        I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      |Num.fixVal mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|<
        (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)<
        Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        (2:ℝ)^(ipmRangeExponent I.m U) :=
  epoch_reported_coefficients_in_range_upTo_on F I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    L U q a r mem hsource D eta op T hvalid hsize (fun _ _ => trivial) hG ha0 ha1 hnums hr
    hslacks hcache

/-- The numerical error budget (2^{-q}) puts each reported coefficient
strictly inside the selected range whenever the current slacks and held
residual have the potential-derived bounds. -/
theorem epoch_reported_coefficients_in_range {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (U q : ℕ) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    (ha0 : 0≤a) (ha1 : a≤1) (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hcache : ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      reportedCachePost F A (A.detect (minRatioState A.eraseFailure D eta op T)).2
        I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    ∀ e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1,
      |Num.fixVal mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|<
        (2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)<
        Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        (2:ℝ)^(ipmRangeExponent I.m U) := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact epoch_reported_coefficients_in_range_upTo F I A κ α Ψ eps (hA.upTo M N) L U q a r mem
    hsource D eta op T hvalid hsize hG ha0 ha1 hnums hr hslacks hcache

/-- Strict ranges in the actual scan input force the checked driver to
enter its batch and Update branch. -/
theorem checkedUpdate_scan_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {S : Finset ℕ}
    {s : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (hout : (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem v final)
    (hrange : ∀ e∈S,
      |Num.fixVal mem (g+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|<(2:ℝ)^F.rangeExponent ∧
      1/(2:ℝ)^F.rangeExponent<Num.fixVal mem (l+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (l+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<(2:ℝ)^F.rangeExponent) :
    final (v-1)=1 := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,_,hscan,_,_,_,_,_,_,_,_,_,_,_,_,_,hn,hx,hm,_,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hreport : DetectAt mem report S := by
    obtain ⟨report',g',l',neg',mx',mn',L',heap',heq,hd,_,_⟩ := hscan
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,_,_,_,_,_,_,_⟩ := heq
    exact hd
  have hpost := coefficientRangeReport_output hscan hout
  rw [zpow_neg,zpow_natCast,← one_div] at hm
  exact coefficientRangeList_accepts hreport hpost.2.2.2.1 hn hx hm hrange

end MinCostFlow.IPM.Machine
