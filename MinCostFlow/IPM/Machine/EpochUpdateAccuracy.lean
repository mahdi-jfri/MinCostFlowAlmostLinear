module

public import MinCostFlow.IPM.Machine.EpochInputFromCache
public import MinCostFlow.IPM.Machine.EpochRefreshedCache
import Mathlib.Tactic.Linarith

/-!
# Accuracy of the coefficients supplied to Update

Refresh gives exact current coordinates for the reported edges and
small stale-coordinate error elsewhere. Its numerically computed
lengths and gradients satisfy Lemma 9.1 at the shared pre-Update flow.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The next Update input has certified coefficient accuracy,
independently of its direction answer. -/
theorem epoch_update_input_accuracy_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (i K heap v : ℕ) (credit : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (es : List ℕ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let D' := appendHistoryIteration D (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    EpochInputAccuracy I U target a r (x/32) A D'
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1+1) := by
  dsimp only
  let base := epochVector F I mem L.base
  let T := 2*i
  let g := readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m
  let l := readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m
  let D' := appendHistoryIteration D T es g l
  let eta' := appendHistoryIterationEta eta T actual
  let op' := appendHistoryIterationOp op T
  have hh := selected_epoch_error_bounds I.m U x hxlo hxhi
  have he : 0≤x/1024 := by linarith only [hh.1]
  obtain ⟨hstrict,hnumL,hnumG,hclose⟩ :=
    epoch_refresh_cache_accuracy_upTo F A I κ α Ψ _ rate allocation R hA he L
      (ipmErrorBits I.m U) K heap v T credit a r mem refreshed D eta op hv hG hl hpre hout haccept
      hsource harrays hscalars hcache
  have hf := (epochInputFlow_append I A D eta op T es g l actual base).2
  have hs := epochHistoryCache_eq_refreshed_upTo F A I κ α Ψ _ hA rate allocation R L
    (ipmErrorBits I.m U) K heap v i credit mem refreshed D eta op es g l actual hv hG hpre hout haccept
    (harrays L.base (by simp)) hcache
  refine epochInputAccuracy_of_cache F I U target a x r A L D' eta' op' (T+1+1) base refreshed
    hm hsize hnums ha0 ha hxlo hxhi (Function.update_self _ _ _) (Function.update_self _ _ _)
    hs.symm hstrict hnumL hnumG hranges (hf.symm ▸ hres) ?_ ?_
  · rw [hf]
    intro e
    exact (hclose e).trans (by linarith only [he])
  · rw [hf]
    intro e
    let f := epochHistoryFlow I A D eta op T base
    let cache := epochVector F I refreshed L.flow
    have hcoef := (hnumL e).2.2.2
    have hpos := (hnumL e).2.1
    have hL : epochVector F I refreshed L.lengths e≤2*lengths I a cache e := by
      refine hcoef.trans (mul_le_mul_of_nonneg_right ?_ hpos.le)
      linarith only [hh.2.2.2]
    have hBound := mul_le_mul_of_nonneg_right hL (abs_nonneg (f e-cache e))
    have hC : |lengths I a cache e*(f e-cache e)|≤2*(x/1024) := hclose e
    rw [abs_mul,abs_of_pos hpos] at hC
    change |epochVector F I refreshed L.lengths e*(f e-cache e)|≤1/2
    rw [abs_mul,abs_of_pos (hnumL e).1]
    linarith only [hBound,hC,hxhi]

/-- The next Update input has certified coefficient accuracy,
independently of its direction answer. -/
theorem epoch_update_input_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ (x/1024))
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (i K heap v : ℕ) (credit : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (es : List ℕ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let D' := appendHistoryIteration D (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    EpochInputAccuracy I U target a r (x/32) A D'
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1+1) :=
  epoch_update_input_accuracy_upTo F A I U κ α Ψ x target a r (hA.upTo I.m I.n)
    rate allocation R L i K heap v credit mem refreshed D eta op es actual hm hsize hnums
    ha0 ha hxlo hxhi hsource hv hG hl hpre hout haccept harrays hscalars hranges hres hcache

/-- The next Update input under `P` has certified coefficient accuracy,
independently of its direction answer. -/
theorem epoch_update_input_accuracy_widened_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ (x/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (i K heap v : ℕ) (credit : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (es : List ℕ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hPD : ∀ j ≤ 2*i, P (D.G j) (D.ℓ j))
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let D' := appendHistoryIteration D (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A D'
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1+1) := by
  dsimp only
  let base := epochVector F I mem L.base
  let T := 2*i
  let g := readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m
  let l := readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m
  let D' := appendHistoryIteration D T es g l
  let eta' := appendHistoryIterationEta eta T actual
  let op' := appendHistoryIterationOp op T
  have hh := widened_epoch_error_bounds I.m U k x hxlo hxhi
  have he : 0≤x/1024 := by linarith only [hh.1]
  obtain ⟨hstrict,hnumL,hnumG,hclose⟩ :=
    epoch_refresh_cache_accuracy_upTo_on F A I κ α Ψ _ rate allocation R hA he L
      (ipmQualityErrorBits I.m U k) K heap v T credit a r mem refreshed D eta op hv hG hPD hl hpre hout haccept
      hsource harrays hscalars hcache
  have hf := (epochInputFlow_append I A D eta op T es g l actual base).2
  have hs := epochHistoryCache_eq_refreshed_upTo_on F A I κ α Ψ _ hA rate allocation R L
    (ipmQualityErrorBits I.m U k) K heap v i credit mem refreshed D eta op es g l actual hv hG hPD hpre hout haccept
    (harrays L.base (by simp)) hcache
  refine epochInputAccuracyAt_of_cache F I U k target a x r A L D' eta' op' (T+1+1) base refreshed
    hm hsize hnums ha0 ha hxlo hxhi (Function.update_self _ _ _) (Function.update_self _ _ _)
    hs.symm hstrict hnumL hnumG hranges (hf.symm ▸ hres) ?_ ?_
  · rw [hf]
    intro e
    exact (hclose e).trans (by linarith only [he])
  · rw [hf]
    intro e
    let f := epochHistoryFlow I A D eta op T base
    let cache := epochVector F I refreshed L.flow
    have hcoef := (hnumL e).2.2.2
    have hpos := (hnumL e).2.1
    have hL : epochVector F I refreshed L.lengths e≤2*lengths I a cache e := by
      refine hcoef.trans (mul_le_mul_of_nonneg_right ?_ hpos.le)
      linarith only [hh.2.2.2]
    have hBound := mul_le_mul_of_nonneg_right hL (abs_nonneg (f e-cache e))
    have hC : |lengths I a cache e*(f e-cache e)|≤2*(x/1024) := hclose e
    rw [abs_mul,abs_of_pos hpos] at hC
    change |epochVector F I refreshed L.lengths e*(f e-cache e)|≤1/2
    rw [abs_mul,abs_of_pos (hnumL e).1]
    linarith only [hBound,hC,hxhi]

/-- The next Update input has certified coefficient accuracy,
independently of its direction answer. -/
theorem epoch_update_input_accuracy_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (L : EpochLayout) (i K heap v : ℕ) (credit : R.τ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (es : List ℕ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).pre
      ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op (2*i)) credit (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).post
      ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let D' := appendHistoryIteration D (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A D'
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1+1) :=
  epoch_update_input_accuracy_widened_upTo_on F A I U k κ α Ψ x target a r
    (hA.upToOn (P := fun _ _ => True)) rate allocation R L i K heap v credit mem refreshed
    D eta op es actual hm hsize hnums ha0 ha hxlo hxhi hsource hv hG (fun _ _ => trivial) hl hpre hout haccept
    harrays hscalars hranges hres hcache

end MinCostFlow.IPM.Machine
