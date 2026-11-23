module

public import MinCostFlow.IPM.Machine.EpochCacheMovement
public import MinCostFlow.IPM.Machine.DetectRefreshSafety

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# Safe current slacks force acceptance of all reported coordinates

On the actual valid history, Detect has no flow increment and Query
returns the current implicit flow. Adding the immutable base gives
the exact candidate checked by each guard. The reported-list theorem
then turns the current flow's strict slack bounds into success.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The actual candidate on a reported edge under `P` has the current flow's
slacks, so the analytic strict bounds imply the machine guard range. -/
theorem epoch_reported_candidate_safe_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (hG : D.G T=namedInstance I)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    ∀ e∈(namedInstance I).E,
      ReportedCandidateSafe F A (A.detect (minRatioState A.eraseFailure D eta op T)).2 mem
        e (L.base+e*F.limbs) (L.lower+e*F.limbs) (L.upper+e*F.limbs) L.exponent := by
  intro e he
  let idx : Fin I.m := ⟨e,Finset.mem_range.mp he⟩
  let D' := appendHistoryStage D T [] (D.g T) (D.ℓ T)
  let eta' := Function.update eta (T+1) 0
  let op' := Function.update op (T+1) false
  have hvalid' : MinRatioHistoryValid D' op' (T+1) := appendHistoryStage_valid_detect D op T hvalid
  have hP' := appendHistoryStage_stage_on (D:=D) (T:=T) [] (D.g T) (D.ℓ T) hP (hP T le_rfl)
  have he' : e∈(D'.G (T+1)).E := by simpa only [D',appendHistoryStage,Function.update_self,hG] using he
  have hQuery := (hA D' eta' op' (T+1) hvalid' (appendHistoryStage_bounded [] _ _ hsize) hP').1.1
    (T+1) le_rfl e he'
  dsimp only [D',eta',op'] at hQuery
  rw [appendHistoryStage_detect_state,appendHistoryStage_detect_flow] at hQuery
  have hf : epochVector F I mem L.base idx+A.query (A.detect (minRatioState A.eraseFailure D eta op T)).2 e=
      epochHistoryFlow I A D eta op T (epochVector F I mem L.base) idx :=
    congrArg (epochVector F I mem L.base idx+·) hQuery
  let value := epochVector F I mem L.base idx+A.query (A.detect (minRatioState A.eraseFailure D eta op T)).2 e
  change (1/(2:ℝ)^L.exponent<epochVector F I mem L.upper idx-value ∧
    epochVector F I mem L.upper idx-value<(2:ℝ)^L.exponent) ∧
    (1/(2:ℝ)^L.exponent<value-epochVector F I mem L.lower idx ∧
    value-epochVector F I mem L.lower idx<(2:ℝ)^L.exponent)
  change value=_ at hf
  rw [hf,(hsource.2.2 idx).1,(hsource.2.2 idx).2.1]
  exact hslacks idx

/-- The actual candidate on a reported edge has the current flow's
slacks, so the analytic strict bounds imply the machine guard range. -/
theorem epoch_reported_candidate_safe_upTo {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (hG : D.G T=namedInstance I)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    ∀ e∈(namedInstance I).E,
      ReportedCandidateSafe F A (A.detect (minRatioState A.eraseFailure D eta op T)).2 mem
        e (L.base+e*F.limbs) (L.lower+e*F.limbs) (L.upper+e*F.limbs) L.exponent :=
  epoch_reported_candidate_safe_upTo_on F I A κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    L a r mem hsource D eta op T hvalid hsize (fun _ _ => trivial) hG hslacks

/-- The actual candidate on a reported edge has the current flow's
slacks, so the analytic strict bounds imply the machine guard range. -/
theorem epoch_reported_candidate_safe {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (A : MinRatioDataStructureWithFailure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A D eta op T (epochVector F I mem L.base) e
      (1/(2:ℝ)^L.exponent<(I.edge e).upper-f ∧ (I.edge e).upper-f<(2:ℝ)^L.exponent) ∧
      (1/(2:ℝ)^L.exponent<f-(I.edge e).lower ∧ f-(I.edge e).lower<(2:ℝ)^L.exponent)) :
    ∀ e∈(namedInstance I).E,
      ReportedCandidateSafe F A (A.detect (minRatioState A.eraseFailure D eta op T)).2 mem
        e (L.base+e*F.limbs) (L.lower+e*F.limbs) (L.upper+e*F.limbs) L.exponent := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact epoch_reported_candidate_safe_upTo F I A κ α Ψ eps (hA.upTo M N) L a r mem hsource D eta
    op T hvalid hsize hG hslacks

end MinCostFlow.IPM.Machine
