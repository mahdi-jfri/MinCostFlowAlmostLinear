module

public import MinCostFlow.IPM.Machine.EpochComputedTolerances
public import MinCostFlow.IPM.Machine.EpochMovementAccount
import MinCostFlow.IPM.Machine.MinRatioUnreportedMovement
import Mathlib.Tactic.Linarith

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# The held cache before Detect, including about-to-be-reported edges

One Update adds at most a quarter of the Detect threshold in the held
lengths. Thus the movement pending at the next Detect is small even on
edges that will be reported. This gives Lemma 9.1's length and gradient
tolerances for the unchanged Detect-stage input.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The exact current displacement from the last cached report costs
at most the pending movement account, under a graph invariant `P`. -/
theorem epoch_cache_displacement_le_pending_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q T : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j))
    (hl : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    |epochVector F I mem L.lengths e*
        (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-epochVector F I mem L.flow e)|≤
      epochPendingMovement A.eraseFailure D eta op T e := by
  let t := minRatioLast A.eraseFailure D eta op T e
  have ht : t≤T := minRatioLast_le A.eraseFailure D eta op T e
  have he : e.val∈(D.G t).E := by rw [hG t ht]; exact Finset.mem_range.mpr e.isLt
  have hcur : e.val∈(D.G T).E := by rw [hG T le_rfl]; exact Finset.mem_range.mpr e.isLt
  have hq := (hA D eta op T hv (namedHistory_bounded hG) hPD).1.1 t ht e he
  have hf : epochVector F I mem L.flow e=epochVector F I mem L.base e+
      minRatioFlow A.eraseFailure D eta op t e :=
    hcache.2.1.trans (congrArg (epochVector F I mem L.base e+·) hq)
  have hlen : D.ℓ T e=epochVector F I mem L.lengths e := by
    simp only [hl,readVector,epochVector,e.isLt,ite_true]
  rw [← hlen,epochHistoryFlow,hf,add_sub_add_left_eq_sub,abs_mul,
    abs_of_pos ((hv.2.1 T le_rfl).2 e hcur),
    minRatioFlow_sub_eq_sum A.eraseFailure D eta op _ _ _ ht]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) ((hv.2.1 T le_rfl).2 e hcur).le

/-- The exact current displacement from the last cached report costs
at most the pending movement account. -/
theorem epoch_cache_displacement_le_pending_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q T : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hl : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    |epochVector F I mem L.lengths e*
        (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-epochVector F I mem L.flow e)|≤
      epochPendingMovement A.eraseFailure D eta op T e :=
  epoch_cache_displacement_le_pending_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    L q T mem D eta op hv hG (fun _ _ => trivial) hl e hcache

/-- The exact current displacement from the last cached report costs
at most the pending movement account. -/
theorem epoch_cache_displacement_le_pending {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (q T : ℕ) (mem : ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hl : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem) :
    |epochVector F I mem L.lengths e*
        (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-epochVector F I mem L.flow e)|≤
      epochPendingMovement A.eraseFailure D eta op T e :=
  epoch_cache_displacement_le_pending_upTo F A I κ α Ψ eps (hA.upTo I.m I.n)
    L q T mem D eta op hv hG hl e hcache

/-- At most two units of exact length correspond to one unit of
computed length. The pending account thus gives the stale-coordinate
budget needed for the unchanged Detect-stage input. -/
theorem epoch_exact_cache_displacement {n : ℕ} (eps δ : ℝ)
    (exactLen computed stored current : Fin n → ℝ)
    (heps : 0≤eps) (hδ : 0≤δ) (hδ' : δ≤1)
    (hl : VectorApprox (1+δ) computed exactLen)
    (hmovement : ∀ e,|computed e*(current e-stored e)|≤eps+eps/4) :
    ∀ e,|exactLen e*(current e-stored e)|≤8*eps := by
  intro e
  have hp : 0<1+δ := by linarith only [hδ]
  have hh : exactLen e≤2*computed e :=
    ((inv_mul_le_iff₀ hp).mp (hl e).2.2.1).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hδ']) (hl e).1.le)
  have hm := mul_le_mul_of_nonneg_right hh (abs_nonneg (current e-stored e))
  have h := hmovement e
  rw [abs_mul,abs_of_pos (hl e).1] at h
  rw [abs_mul,abs_of_pos (hl e).2.1]
  linarith only [hm,h,heps]

end MinCostFlow.IPM.Machine
