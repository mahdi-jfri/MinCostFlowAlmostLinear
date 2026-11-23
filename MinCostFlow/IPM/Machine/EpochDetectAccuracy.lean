module

public import MinCostFlow.IPM.Machine.EpochInputFromCache
public import MinCostFlow.IPM.Machine.EpochPreDetectCache
import Mathlib.Tactic.Linarith

/-!
# Accuracy of the coefficients used at Detect

Before each Detect, the current implicit flow differs from the held
coordinate by at most the uncharged movement of that edge. This bound
holds for every edge. Detect presents the old coefficient arrays, so
their cache accuracy applies directly to this input.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The next Detect satisfies Lemma 9.1 with the previous cache and
the pending-movement bound after the previous Update. -/
theorem epoch_detect_input_accuracy_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hg : D.g (2*i)=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hpend : ∀ e<I.m,epochPendingMovement A.eraseFailure D eta op (2*i) e≤x/1024+(x/1024)/4) :
    EpochInputAccuracy I U target a r (x/32) A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1) := by
  let base := epochVector F I mem L.base
  let current := epochHistoryFlow I A D eta op (2*i) base
  let stored := epochVector F I mem L.flow
  let D' := appendHistoryIteration D (2*i) es g ell
  let eta' := appendHistoryIterationEta eta (2*i) actual
  let op' := appendHistoryIterationOp op (2*i)
  have hcoeff (e : Fin I.m) := reportedCachePost_coefficients F I A L a r mem hsource
    (ipmErrorBits I.m U) e _ (hcache e.val e.isLt)
  have hcurr : epochInputFlow I A D' eta' op' (2*i+1) base=current :=
    (epochInputFlow_append I A D eta op (2*i) es g ell actual base).1
  have hst : epochHistoryCache I A D' eta' op' (2*i+1) base=stored :=
    (epochHistoryCache_detect I A D eta op i es g ell actual base).trans
      (funext fun e => (epochHistoryCache_eq_cache_upTo F A I κ α Ψ _ hA L
        (ipmErrorBits I.m U) i mem D eta op hv hG e (hcache e.val e.isLt)).symm)
  have hweighted (e : Fin I.m) :
      |epochVector F I mem L.lengths e*(current e-stored e)|≤x/1024+(x/1024)/4 :=
    (epoch_cache_displacement_le_pending_upTo F A I κ α Ψ _ hA L (ipmErrorBits I.m U) (2*i) mem
      D eta op hv hG hl e (hcache e.val e.isLt)).trans (hpend e.val e.isLt)
  have ⟨he,_,hd,hd'⟩ := selected_epoch_error_bounds I.m U x hxlo hxhi
  have hclose := epoch_exact_cache_displacement (x/1024) (1/(2:ℝ)^(ipmErrorBits I.m U))
    (lengths I a stored) (epochVector F I mem L.lengths) stored current
    (by linarith only [he]) hd (by linarith only [hd']) (fun e => (hcoeff e).1) hweighted
  have hg' : D'.g (2*i+1)=D.g (2*i) := by
    simp only [D',appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : 2*i+1≠2*i+1+1),
      Function.update_self]
  have hl' : D'.ℓ (2*i+1)=D.ℓ (2*i) := by
    simp only [D',appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : 2*i+1≠2*i+1+1),
      Function.update_self]
  refine epochInputAccuracy_of_cache F I U target a x r A L D' eta' op' (2*i+1) base mem
    hm hsize hnums ha0 ha hxlo hxhi (hg'.trans hg) (hl'.trans hl) hst
    (fun e => (hcoeff e).2.2) (fun e => (hcoeff e).1) (fun e => (hcoeff e).2.1) hranges
    (hcurr.symm ▸ hres) ?_ ?_
  · rw [hcurr]
    exact hclose
  · rw [hcurr]
    intro e
    exact (hweighted e).trans (by linarith only [hxhi])

/-- The next Detect satisfies Lemma 9.1 with the previous cache and
the pending-movement bound after the previous Update. -/
theorem epoch_detect_input_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ (x/1024))
    (L : EpochLayout) (i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hg : D.g (2*i)=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hpend : ∀ e<I.m,epochPendingMovement A.eraseFailure D eta op (2*i) e≤x/1024+(x/1024)/4) :
    EpochInputAccuracy I U target a r (x/32) A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1) :=
  epoch_detect_input_accuracy_upTo F A I U κ α Ψ x target a r (hA.upTo I.m I.n)
    L i mem D eta op es g ell actual hm hsize hnums ha0 ha hxlo hxhi hsource
    hv hG hg hl hranges hres hcache hpend

/-- The next Detect under `P` satisfies Lemma 9.1 with the previous cache and
the pending-movement bound after the previous Update. -/
theorem epoch_detect_input_accuracy_widened_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hPD : ∀ j ≤ 2*i, P (D.G j) (D.ℓ j))
    (hg : D.g (2*i)=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hpend : ∀ e<I.m,epochPendingMovement A.eraseFailure D eta op (2*i) e≤x/1024+(x/1024)/4) :
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1) := by
  let base := epochVector F I mem L.base
  let current := epochHistoryFlow I A D eta op (2*i) base
  let stored := epochVector F I mem L.flow
  let D' := appendHistoryIteration D (2*i) es g ell
  let eta' := appendHistoryIterationEta eta (2*i) actual
  let op' := appendHistoryIterationOp op (2*i)
  have hcoeff (e : Fin I.m) := reportedCachePost_coefficients F I A L a r mem hsource
    (ipmQualityErrorBits I.m U k) e _ (hcache e.val e.isLt)
  have hcurr : epochInputFlow I A D' eta' op' (2*i+1) base=current :=
    (epochInputFlow_append I A D eta op (2*i) es g ell actual base).1
  have hst : epochHistoryCache I A D' eta' op' (2*i+1) base=stored :=
    (epochHistoryCache_detect I A D eta op i es g ell actual base).trans
      (funext fun e => (epochHistoryCache_eq_cache_upTo_on F A I κ α Ψ _ hA L
        (ipmQualityErrorBits I.m U k) i mem D eta op hv hG hPD e (hcache e.val e.isLt)).symm)
  have hweighted (e : Fin I.m) :
      |epochVector F I mem L.lengths e*(current e-stored e)|≤x/1024+(x/1024)/4 :=
    (epoch_cache_displacement_le_pending_upTo_on F A I κ α Ψ _ hA L (ipmQualityErrorBits I.m U k) (2*i) mem
      D eta op hv hG hPD hl e (hcache e.val e.isLt)).trans (hpend e.val e.isLt)
  have ⟨he,_,hd,hd'⟩ := widened_epoch_error_bounds I.m U k x hxlo hxhi
  have hclose := epoch_exact_cache_displacement (x/1024) (1/(2:ℝ)^(ipmQualityErrorBits I.m U k))
    (lengths I a stored) (epochVector F I mem L.lengths) stored current
    (by linarith only [he]) hd (by linarith only [hd']) (fun e => (hcoeff e).1) hweighted
  have hg' : D'.g (2*i+1)=D.g (2*i) := by
    simp only [D',appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : 2*i+1≠2*i+1+1),
      Function.update_self]
  have hl' : D'.ℓ (2*i+1)=D.ℓ (2*i) := by
    simp only [D',appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : 2*i+1≠2*i+1+1),
      Function.update_self]
  refine epochInputAccuracyAt_of_cache F I U k target a x r A L D' eta' op' (2*i+1) base mem
    hm hsize hnums ha0 ha hxlo hxhi (hg'.trans hg) (hl'.trans hl) hst
    (fun e => (hcoeff e).2.2) (fun e => (hcoeff e).1) (fun e => (hcoeff e).2.1) hranges
    (hcurr.symm ▸ hres) ?_ ?_
  · rw [hcurr]
    exact hclose
  · rw [hcurr]
    intro e
    exact (hweighted e).trans (by linarith only [hxhi])

/-- The next Detect satisfies Lemma 9.1 with the previous cache and
the pending-movement bound after the previous Update. -/
theorem epoch_detect_input_accuracy_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (i : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hv : MinRatioHistoryValid D op (2*i)) (hG : ∀ j≤2*i,D.G j=namedInstance I)
    (hg : D.g (2*i)=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ (2*i)=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hres : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A D eta op (2*i) (epochVector F I mem L.base))))
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op (2*i) e))
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hpend : ∀ e<I.m,epochPendingMovement A.eraseFailure D eta op (2*i) e≤x/1024+(x/1024)/4) :
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i))
      (epochVector F I mem L.base) (2*i+1) :=
  epoch_detect_input_accuracy_widened_upTo_on F A I U k κ α Ψ x target a r
    (hA.upToOn (P := fun _ _ => True)) L i mem D eta op es g ell actual hm hsize hnums
    ha0 ha hxlo hxhi hsource hv hG (fun _ _ => trivial) hg hl hranges hres hcache hpend

end MinCostFlow.IPM.Machine
