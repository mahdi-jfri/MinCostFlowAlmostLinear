module

public import MinCostFlow.IPM.Machine.EpochCacheCoefficients
public import MinCostFlow.IPM.Machine.HistoryAppend
import MinCostFlow.IPM.Machine.MinRatioUnreportedMovement
import MinCostFlow.IPM.Machine.EpochConditions
import Mathlib.Tactic.Linarith

/-!
# Movement of the actual cache at a Detect call

In Definition 4.5 (page 14), Detect tests movement in the computed
length at each stored coordinate. That length approximates the exact
length at the same coordinate. For any edge omitted from the report,
the two facts give the stale-coordinate bound for Lemma 9.1.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Current flow in an epoch is its explicit base plus the implicit
flow accumulated by the shared history. -/
noncomputable def epochHistoryFlow (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ)
    (base : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  base e+minRatioFlow A.eraseFailure D eta op t e.val

/-- The pre-Detect cache on an omitted edge is within twice the Detect
threshold of the current flow in the exact length at the stored flow,
under a graph invariant `P`. -/
theorem epoch_unreported_cache_movement_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w) (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ) (q : ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j))
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hnot : e.val∉(A.detect (minRatioState A.eraseFailure D eta op T)).1)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e.val))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e.val mem) :
    |lengths I a (epochVector F I mem L.flow) e*
      (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-
        epochVector F I mem L.flow e)|≤2*eps := by
  let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let eta' := Function.update eta (T+1) 0
  let op' := Function.update op (T+1) false
  let last := minRatioLast A.eraseFailure D eta op T e.val
  have hlast : last≤T := minRatioLast_le A.eraseFailure D eta op T e.val
  have he : e.val∈(namedInstance I).E := Finset.mem_range.mpr e.isLt
  have heLast : e.val∈(D.G last).E := by rw [hG last hlast]; exact he
  have heNext : e.val∈(D'.G (T+1)).E := by
    simpa only [D',appendHistoryStage,Function.update_self,hG T le_rfl] using he
  have hnew := appendHistoryStage_valid_detect D op T hvalid
  have hstate := appendHistoryStage_past_state A.eraseFailure D eta op T [] (D.g T) (D.ℓ T) 0 false T le_rfl
  have hnone : e.val∉(A.eraseFailure.detect (minRatioState A.eraseFailure D' eta' op' T)).1 := by
    change e.val∉(A.eraseFailure.detect (minRatioState A.eraseFailure
      (appendHistoryStage D T [] (D.g T) (D.ℓ T)) (Function.update eta (T+1) 0)
      (Function.update op (T+1) false) T)).1
    rw [hstate]
    exact hnot
  have hsize := appendHistoryStage_bounded [] (D.g T) (D.ℓ T) (namedHistory_bounded hG)
  have hPD' := appendHistoryStage_stage_on (D:=D) (T:=T) [] (D.g T) (D.ℓ T) hPD (hPD T le_rfl)
  have hSpec := (hA D' eta' op' (T+1) hnew hsize hPD').1
  have hMove := minRatio_unreported_movement_on A.eraseFailure κ α Ψ eps D' eta' op'
    (T+1) T e.val hnew hSpec le_rfl (by simp [op']) heNext hnone
  change D'.ℓ (T+1) e.val * |minRatioFlow A.eraseFailure D' eta' op' (T+1) e.val-
    minRatioFlow A.eraseFailure D' eta' op' (minRatioLast A.eraseFailure D' eta' op' T e.val) e.val|<eps at hMove
  have hLast' : minRatioLast A.eraseFailure D' eta' op' T e.val=last :=
    appendHistoryStage_past_last A.eraseFailure D eta op T [] (D.g T) (D.ℓ T) 0 false T e.val le_rfl
  rw [hLast'] at hMove
  have hOld : minRatioFlow A.eraseFailure D' eta' op' last e.val=minRatioFlow A.eraseFailure D eta op last e.val :=
    appendHistoryStage_past_flow A.eraseFailure D eta op T [] (D.g T) (D.ℓ T) 0 false last e.val hlast
  have hCur : minRatioFlow A.eraseFailure D' eta' op' (T+1) e.val=minRatioFlow A.eraseFailure D eta op T e.val :=
    appendHistoryStage_detect_flow A.eraseFailure D eta op T 0 e.val
  have hLength : D'.ℓ (T+1) e.val=epochVector F I mem L.lengths e := by
    simp only [D',appendHistoryStage,Function.update_self,hℓ,readVector,epochVector,e.isLt,ite_true]
  rw [hOld,hCur,hLength] at hMove
  have hQuery := (hA D eta op T hvalid (namedHistory_bounded hG) hPD).1.1 last hlast e.val heLast
  have hFlow : epochVector F I mem L.flow e=epochVector F I mem L.base e+
      minRatioFlow A.eraseFailure D eta op last e.val :=
    hcache.2.1.trans (congrArg (epochVector F I mem L.base e+·) hQuery)
  have happrox := (reportedCachePost_coefficients F I A L a r mem hsource q e _ hcache).1
  have hδ : 1/(2:ℝ)^q≤1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : (1:ℝ)≤2^q)
  have hfac : 0<1+1/(2:ℝ)^q := by positivity
  have hl : lengths I a (epochVector F I mem L.flow) e≤2*epochVector F I mem L.lengths e := by
    have h := (inv_mul_le_iff₀ hfac).mp happrox.2.2.1
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith only [hδ]) happrox.1.le)
  rw [epochHistoryFlow,hFlow,add_sub_add_left_eq_sub,abs_mul,abs_of_pos happrox.2.1]
  have hm := mul_le_mul_of_nonneg_right hl
    (abs_nonneg (minRatioFlow A.eraseFailure D eta op T e.val-minRatioFlow A.eraseFailure D eta op last e.val))
  linarith only [hm,hMove]

/-- The pre-Detect cache on an omitted edge is within twice the Detect
threshold of the current flow in the exact length at the stored flow. -/
theorem epoch_unreported_cache_movement_upTo {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ) (q : ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hnot : e.val∉(A.detect (minRatioState A.eraseFailure D eta op T)).1)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e.val))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e.val mem) :
    |lengths I a (epochVector F I mem L.flow) e*
      (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-
        epochVector F I mem L.flow e)|≤2*eps :=
  epoch_unreported_cache_movement_upTo_on F I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    L a r mem q hsource D eta op T hvalid hG (fun _ _ => trivial) hℓ e hnot hcache


/-- The pre-Detect cache on an omitted edge is within twice the Detect
threshold of the current flow in the exact length at the stored flow. -/
theorem epoch_unreported_cache_movement {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ) (q : ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hℓ : D.ℓ T=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (e : Fin I.m)
    (hnot : e.val∉(A.detect (minRatioState A.eraseFailure D eta op T)).1)
    (hcache : reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e.val))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e.val mem) :
    |lengths I a (epochVector F I mem L.flow) e*
      (epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e-
        epochVector F I mem L.flow e)|≤2*eps :=
  epoch_unreported_cache_movement_upTo F I A κ α Ψ eps (hA.upTo I.m I.n) L a r mem q
    hsource D eta op T hvalid hG hℓ e hnot hcache

end MinCostFlow.IPM.Machine
