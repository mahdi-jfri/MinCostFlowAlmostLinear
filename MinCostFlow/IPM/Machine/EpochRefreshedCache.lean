module

public import MinCostFlow.IPM.Machine.EpochCacheMovement
import MinCostFlow.IPM.Machine.DetectRefreshOutput
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.IPM.Machine.DetectRefreshUnreported
import MinCostFlow.IPM.Machine.DetectRefreshUnreportedFlow
import MinCostFlow.IPM.Machine.ReportedCacheCongr
import MinCostFlow.IPM.Machine.EpochMaterialization
import MinCostFlow.IPM.Machine.ReportedTableLayout
import Mathlib.Tactic.Linarith

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# Cache and stale-coordinate bounds after the actual refresh

Reported entries are computed at the current flow and have zero stale
error. Unreported entries keep their full cache and the movement bound
provided by Detect. The resulting dense arrays are the inputs to the
coefficient range check and the next Update.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- An accepted Detect/refresh under `P` supplies the numerical cache and the
stale-coordinate bound at the actual current history flow. -/
theorem epoch_refresh_cache_accuracy_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (heps : 0≤eps)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ)
    (a r : ℝ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j))
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
        ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hOldSource : epochSourcesAt F I L a r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let stored := epochVector F I refreshed L.flow
    let current := epochHistoryFlow I A D eta op T (epochVector F I mem L.base)
    StrictlyInside I stored ∧
    VectorApprox (1+1/(2:ℝ)^q) (epochVector F I refreshed L.lengths) (lengths I a stored) ∧
    (∀ e,|epochVector F I refreshed L.gradient e-gradientWithResidual I a r stored e|≤
      (1/(2:ℝ)^q)*lengths I a stored e) ∧
    ∀ e, |lengths I a stored e*(current e-stored e)|≤2*eps := by
  let s := minRatioState A.eraseFailure D eta op T
  have hFrame := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hNewSource := hOldSource.frozen hFrame harrays hscalars
  have hReport := (detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hout).2.2.2.2 haccept
  have hOne (e : Fin I.m) :
      (∃ cached,reportedCachePost F A cached I.m q L.base L.lower L.upper L.flow L.cost
        L.residual L.alpha L.lengths L.gradient e.val refreshed) ∧
      |lengths I a (epochVector F I refreshed L.flow) e*
        (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-
          epochVector F I refreshed L.flow e)|≤2*eps := by
    have hEnd (ptr : ℕ) (hp : ptr∈[L.base,L.cost,L.lower,L.upper]) :
        ptr+e.val*F.limbs+F.limbs≤L.flow :=
      (reported_entry_end ptr F.limbs e.val I.m e.isLt).trans (harrays ptr hp)
    by_cases hmem : e.val∈(A.detect s).1
    · have hc := hReport _ hmem
      have he : e.val∈(D.G T).E := by rw [hG T le_rfl]; exact Finset.mem_range.mpr e.isLt
      have hCurrent := reportedCachePost_detect_flow_upTo_on F A κ α Ψ eps hA D eta op T hvalid
        (namedHistory_bounded hG) hPD he hc
      have hBase : epochVector F I refreshed L.base e=epochVector F I mem L.base e :=
        Num.IPM.fixVal_frozen hFrame (hEnd L.base (by simp))
      refine ⟨⟨(A.detect s).2,hc⟩,?_⟩
      have heq : epochVector F I refreshed L.flow e=
          epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e :=
        hCurrent.trans (congrArg (fun z => z+minRatioFlow A.eraseFailure D eta op T e.val) hBase)
      rw [heq,sub_self,mul_zero,abs_zero]
      exact mul_nonneg (by norm_num) heps
    · have hflow := detectRefresh_unreported_flow F A (namedInstance I) I.m κ α rate allocation R hpre hout e.isLt hmem
      have hcoef := detectRefresh_unreported_coefficients F A (namedInstance I) I.m κ α rate allocation R
        hpre hout e.isLt hmem
      have hc := hcache e.val e.isLt
      have hNew := reportedCachePost_congr F A _ (mem:=mem) (mem':=refreshed) (by
        intro ptr hp j hj
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
        all_goals subst ptr
        · have hh := hEnd L.base (by simp)
          exact hFrame _ (by omega)
        · have hh := hEnd L.cost (by simp)
          exact hFrame _ (by omega)
        · exact hFrame _ (by have hh := hscalars.1; omega)
        · have hh := hEnd L.lower (by simp)
          exact hFrame _ (by omega)
        · exact hflow j hj
        · have hh := hEnd L.upper (by simp)
          exact hFrame _ (by omega)
        · exact hFrame _ (by have hh := hscalars.2; omega)
        · exact hcoef L.lengths (by simp) j hj
        · exact hcoef L.gradient (by simp) j hj) hc
      have hmove := epoch_unreported_cache_movement_upTo_on F I A κ α Ψ eps hA L a r mem q hOldSource
        D eta op T hvalid hG hPD hℓ e hmem hc
      have hSame : epochVector F I refreshed L.flow e=epochVector F I mem L.flow e := by
        unfold epochVector Num.fixVal
        rw [Num.intVal_congr hflow]
      have hlength : lengths I a (epochVector F I refreshed L.flow) e=
          lengths I a (epochVector F I mem L.flow) e := by
        simp only [lengths,hSame]
      refine ⟨⟨_,hNew⟩,?_⟩
      rw [hlength,hSame]
      exact hmove
  have hCoefs (e : Fin I.m) :
      ScalarApprox (1+1/(2:ℝ)^q) (epochVector F I refreshed L.lengths e)
        (lengths I a (epochVector F I refreshed L.flow) e) ∧
      |epochVector F I refreshed L.gradient e-gradientWithResidual I a r (epochVector F I refreshed L.flow) e|≤
        (1/(2:ℝ)^q)*lengths I a (epochVector F I refreshed L.flow) e ∧
      (I.edge e).lower<epochVector F I refreshed L.flow e ∧
        epochVector F I refreshed L.flow e<(I.edge e).upper := by
    obtain ⟨⟨cached,hc⟩,_⟩ := hOne e
    exact reportedCachePost_coefficients F I A L a r refreshed hNewSource q e cached hc
  exact ⟨fun e => (hCoefs e).2.2,fun e => (hCoefs e).1,fun e => (hCoefs e).2.1,fun e => (hOne e).2⟩

/-- An accepted Detect/refresh supplies the numerical cache and the
stale-coordinate bound at the actual current history flow. -/
theorem epoch_refresh_cache_accuracy_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (heps : 0≤eps)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ)
    (a r : ℝ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
        ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hOldSource : epochSourcesAt F I L a r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let stored := epochVector F I refreshed L.flow
    let current := epochHistoryFlow I A D eta op T (epochVector F I mem L.base)
    StrictlyInside I stored ∧
    VectorApprox (1+1/(2:ℝ)^q) (epochVector F I refreshed L.lengths) (lengths I a stored) ∧
    (∀ e,|epochVector F I refreshed L.gradient e-gradientWithResidual I a r stored e|≤
      (1/(2:ℝ)^q)*lengths I a stored e) ∧
    ∀ e, |lengths I a stored e*(current e-stored e)|≤2*eps :=
  epoch_refresh_cache_accuracy_upTo_on F A I κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) heps L q K heap v T x a r mem refreshed
    D eta op hvalid hG (fun _ _ => trivial) hℓ hpre hout haccept hOldSource harrays hscalars hcache

/-- An accepted Detect/refresh supplies the numerical cache and the
stale-coordinate bound at the actual current history flow. -/
theorem epoch_refresh_cache_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (heps : 0≤eps)
    (L : EpochLayout) (q K heap v T : ℕ) (x : R.τ)
    (a r : ℝ) (mem refreshed : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure D eta op T) x q K L.sourceEnd L.tableEnd).post
        ((L.packet F I heap).take 20) mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hOldSource : epochSourcesAt F I L a r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hcache : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    let stored := epochVector F I refreshed L.flow
    let current := epochHistoryFlow I A D eta op T (epochVector F I mem L.base)
    StrictlyInside I stored ∧
    VectorApprox (1+1/(2:ℝ)^q) (epochVector F I refreshed L.lengths) (lengths I a stored) ∧
    (∀ e,|epochVector F I refreshed L.gradient e-gradientWithResidual I a r stored e|≤
      (1/(2:ℝ)^q)*lengths I a stored e) ∧
    ∀ e, |lengths I a stored e*(current e-stored e)|≤2*eps :=
  epoch_refresh_cache_accuracy_upTo F A I κ α Ψ eps rate allocation R (hA.upTo I.m I.n)
    heps L q K heap v T x a r mem refreshed D eta op hvalid hG hℓ hpre hout haccept
    hOldSource harrays hscalars hcache

end MinCostFlow.IPM.Machine
