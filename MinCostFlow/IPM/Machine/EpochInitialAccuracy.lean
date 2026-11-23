module

public import MinCostFlow.IPM.Machine.EpochInputFromCache
import MinCostFlow.IPM.Machine.EpochHistoryRun
import Mathlib.Tactic.Linarith

/-!
# Accuracy at the initial min-ratio state of an epoch

Init starts at zero implicit flow and the initial cache is evaluated
at the base. There is no stale-coordinate error in either the exact
or the computed lengths. The held residual is the base's exact cost
minus the target.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The initial coefficient arrays establish Lemma 9.1 at stage zero,
where the cache and input flow equal the base coordinate array. -/
theorem epoch_initial_input_accuracy_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (mem : ℕ → ℕ) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hr : 0<r) (hres : r=residual I target (epochVector F I mem L.base))
    (hv : MinRatioHistoryValid D op 0) (hG : D.G 0=namedInstance I)
    (hg : D.g 0=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ 0=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op 0)
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    EpochInputAccuracy I U target a r (x/32) A D eta op (epochVector F I mem L.base) 0 := by
  let base := epochVector F I mem L.base
  have hf : epochInputFlow I A D eta op 0 base=base :=
    epochHistoryFlow_zero I A D eta op base
  have hs : epochHistoryCache I A D eta op 0 base=base :=
    epochHistoryFlow_zero I A D eta op base
  have hst : epochHistoryCache I A D eta op 0 base=epochVector F I mem L.flow := by
    funext e
    exact (epochHistoryCache_eq_cache_upTo F A I κ α Ψ _ hA L (ipmErrorBits I.m U) 0 mem D eta op hv
      (by
        intro j hj
        have heq : j=0 := by omega
        exact heq.symm ▸ hG) e (hcache e.val e.isLt)).symm
  have hcoeff (e : Fin I.m) := reportedCachePost_coefficients F I A L a r mem hsource
    (ipmErrorBits I.m U) e _ (hcache e.val e.isLt)
  have hx : 0≤8*(x/1024) := (selected_epoch_error_bounds I.m U x hxlo hxhi).1
  have hfactor : 1≤1+8*(x/1024) := by linarith only [hx]
  have hpositive : 0<1+8*(x/1024) := by linarith only [hfactor]
  have hInv : (1+8*(x/1024))⁻¹≤1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hfactor
  have hround : ScalarApprox (1+8*(x/1024)) r (residual I target (epochInputFlow I A D eta op 0 base)) := by
    rw [hf,← hres]
    exact ⟨hr,hr,(mul_le_mul_of_nonneg_right hInv hr.le).trans_eq (one_mul _),
      (one_mul r).symm.le.trans (mul_le_mul_of_nonneg_right hfactor hr.le)⟩
  refine epochInputAccuracy_of_cache F I U target a x r A L D eta op 0 base mem
    hm hsize hnums ha0 ha hxlo hxhi hg hl hst (fun e => (hcoeff e).2.2)
    (fun e => (hcoeff e).1) (fun e => (hcoeff e).2.1) hranges hround ?_ ?_
  · rw [hf,← hst,hs]
    simpa only [sub_self,mul_zero,abs_zero] using (fun _ : Fin I.m => hx)
  · rw [hf,← hst,hs]
    simp only [sub_self,mul_zero,abs_zero]
    exact fun _ => by norm_num

/-- The initial coefficient arrays establish Lemma 9.1 at stage zero,
where the cache and input flow equal the base coordinate array. -/
theorem epoch_initial_input_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ (x/1024))
    (L : EpochLayout) (mem : ℕ → ℕ) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hr : 0<r) (hres : r=residual I target (epochVector F I mem L.base))
    (hv : MinRatioHistoryValid D op 0) (hG : D.G 0=namedInstance I)
    (hg : D.g 0=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ 0=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op 0)
      I.m (ipmErrorBits I.m U) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    EpochInputAccuracy I U target a r (x/32) A D eta op (epochVector F I mem L.base) 0 :=
  epoch_initial_input_accuracy_upTo F A I U κ α Ψ x target a r (hA.upTo I.m I.n) L mem D eta op
    hm hsize hnums ha0 ha hxlo hxhi hsource hr hres hv hG hg hl hranges hcache

/-- The initial coefficient arrays under `P` establish Lemma 9.1 at stage zero,
where the cache and input flow equal the base coordinate array. -/
theorem epoch_initial_input_accuracy_widened_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (mem : ℕ → ℕ) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hr : 0<r) (hres : r=residual I target (epochVector F I mem L.base))
    (hv : MinRatioHistoryValid D op 0) (hG : D.G 0=namedInstance I) (hPD : P (D.G 0) (D.ℓ 0))
    (hg : D.g 0=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ 0=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op 0)
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A D eta op (epochVector F I mem L.base) 0 := by
  let base := epochVector F I mem L.base
  have hf : epochInputFlow I A D eta op 0 base=base :=
    epochHistoryFlow_zero I A D eta op base
  have hs : epochHistoryCache I A D eta op 0 base=base :=
    epochHistoryFlow_zero I A D eta op base
  have hst : epochHistoryCache I A D eta op 0 base=epochVector F I mem L.flow := by
    funext e
    exact (epochHistoryCache_eq_cache_upTo_on F A I κ α Ψ _ hA L (ipmQualityErrorBits I.m U k) 0 mem D eta op hv
      (by
        intro j hj
        have heq : j=0 := by omega
        exact heq.symm ▸ hG)
      (fun j hj => by obtain rfl : j=0 := by omega
                      exact hPD) e (hcache e.val e.isLt)).symm
  have hcoeff (e : Fin I.m) := reportedCachePost_coefficients F I A L a r mem hsource
    (ipmQualityErrorBits I.m U k) e _ (hcache e.val e.isLt)
  have hx : 0≤8*(x/1024) := (widened_epoch_error_bounds I.m U k x hxlo hxhi).1
  have hfactor : 1≤1+8*(x/1024) := by linarith only [hx]
  have hpositive : 0<1+8*(x/1024) := by linarith only [hfactor]
  have hInv : (1+8*(x/1024))⁻¹≤1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hfactor
  have hround : ScalarApprox (1+8*(x/1024)) r (residual I target (epochInputFlow I A D eta op 0 base)) := by
    rw [hf,← hres]
    exact ⟨hr,hr,(mul_le_mul_of_nonneg_right hInv hr.le).trans_eq (one_mul _),
      (one_mul r).symm.le.trans (mul_le_mul_of_nonneg_right hfactor hr.le)⟩
  refine epochInputAccuracyAt_of_cache F I U k target a x r A L D eta op 0 base mem
    hm hsize hnums ha0 ha hxlo hxhi hg hl hst (fun e => (hcoeff e).2.2)
    (fun e => (hcoeff e).1) (fun e => (hcoeff e).2.1) hranges hround ?_ ?_
  · rw [hf,← hst,hs]
    simpa only [sub_self,mul_zero,abs_zero] using (fun _ : Fin I.m => hx)
  · rw [hf,← hst,hs]
    simp only [sub_self,mul_zero,abs_zero]
    exact fun _ => by norm_num

/-- The initial coefficient arrays establish Lemma 9.1 at stage zero,
where the cache and input flow equal the base coordinate array. -/
theorem epoch_initial_input_accuracy_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ α Ψ x target a r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ (x/1024) I.m I.n)
    (L : EpochLayout) (mem : ℕ → ℕ) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hsource : epochSourcesAt F I L a r mem)
    (hr : 0<r) (hres : r=residual I target (epochVector F I mem L.base))
    (hv : MinRatioHistoryValid D op 0) (hG : D.G 0=namedInstance I)
    (hg : D.g 0=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ 0=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hranges : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op 0)
      I.m (ipmQualityErrorBits I.m U k) L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A D eta op (epochVector F I mem L.base) 0 :=
  epoch_initial_input_accuracy_widened_upTo_on F A I U k κ α Ψ x target a r
    (hA.upToOn (P := fun _ _ => True)) L mem D eta op hm hsize hnums ha0 ha hxlo hxhi
    hsource hr hres hv hG trivial hg hl hranges hcache


end MinCostFlow.IPM.Machine
