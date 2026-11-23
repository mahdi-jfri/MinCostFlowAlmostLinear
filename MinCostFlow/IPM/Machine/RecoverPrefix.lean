module

public import MinCostFlow.IPM.Machine.InitialPolynomialSize
public import MinCostFlow.IPM.InitialOptimalAuxiliary
public import MinCostFlow.Rounding.Rounding
import Mathlib.Tactic

/-!
# Recovering the original positive-capacity circulation

Lemma 4.12 (page 31) keeps every positive-capacity original edge,
in its input order. Its recovery on this domain is the prefix of
the augmented optimum. The zero circulation rules out the
infeasible outcome.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Scaling Rounding

/-- An original edge has its input index in the augmented table. -/
def augmentedOriginalIndex (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (j : Fin J.m) : Fin (initialInstance J.toInstance K).m :=
  ⟨j.val,j.isLt.trans_le (circulation_augmented_m_ge J K hp)⟩

/-- On the solver input domain the reconstruction map reads a
prefix of the augmented table, with no fixed edges to reinsert. -/
theorem recoverInitialFlow_prefix (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (g : Fin (initialInstance J.toInstance K).m → ℝ) :
    recoverInitialFlow J.toInstance K g =
      J.inputFlow (fun e => g (augmentedOriginalIndex J K hp e)) := by
  funext e
  have hfree := freeEdges_circulation J hp
  have he : e∈freeEdges J.toInstance := by simp [hfree]
  let q := (freeIndex J.toInstance).symm ⟨e,he⟩
  have hf : (freeIndex J.toInstance q).val=e := congrArg Subtype.val ((freeIndex J.toInstance).apply_symm_apply ⟨e,he⟩)
  have hq := freeIndex_val_of_univ J.toInstance hfree q
  have hIndex : q.val=e.val := hq.symm.trans (congrArg Fin.val hf)
  unfold recoverInitialFlow liftFreeFlow expandFreeFlow
  rw [dite_eq_left he]
  change flowToArray (freeEdgeArray J.toInstance) (freeDemands J.toInstance)
      (initialOriginalFlow J.toInstance K g) q=_
  simp only [initialOriginalFlow,flowToArray,flowOfArray,Equiv.apply_symm_apply,Circulation.inputFlow]
  congr 1
  apply Fin.ext
  exact hIndex

/-- Reading the first m rounded coordinates yields an optimal original
circulation with nonnegative integral coordinates. -/
theorem recoverPrefix_optimal (J : Circulation) (U : ℝ) (K : ℤ)
    (hp : ∀ e,1≤J.capacity e) (hU : 0≤U) (hNums : NumbersBounded J.toInstance U)
    (hPenalty : 0≤(K:ℝ)) (hLarge : 2*J.toInstance.m*U<(K:ℝ))
    (g : Fin (initialInstance J.toInstance K).m → ℚ)
    (hg : (initialInstance J.toInstance K).IsMinCostFlow (fun e => (g e:ℝ)))
    (hz : IsIntegral (fun e => (g e:ℝ))) :
    ∃ q : Fin J.m → ℕ,
      (∀ e,g (augmentedOriginalIndex J K hp e)=(q e:ℚ)) ∧
      J.Optimal (fun e => (q e:ℝ)) ∧ ∀ e,q e≤J.capacity e := by
  let f : Fin J.m → ℝ := fun e => (g (augmentedOriginalIndex J K hp e):ℝ)
  have hOrdered (e : Fin J.toInstance.m) : (J.toInstance.edge e).lower≤(J.toInstance.edge e).upper := by
    rw [Circulation.toInstance_edge]
    exact Int.natCast_nonneg _
  have hsome : ∃ f,J.toInstance.IsFeasible f := ⟨_,(J.toInstance_feasible_iff _).mpr J.zero_feasible⟩
  have hOriginal : J.toInstance.IsMinCostFlow (J.inputFlow f) := by
    rw [← recoverInitialFlow_prefix J K hp (fun e => (g e:ℝ))]
    exact (initial_optimum_recovery J.toInstance U K J.toInstance_valid hOrdered hU hNums hPenalty hLarge _ hg).resolve_right
      (fun hh => hh hsome)
  have hOpt := (J.toInstance_minCostFlow_iff f).mp hOriginal
  have hInt : ∀ e : Fin J.m,∃ n : ℤ, f e=n := fun e => hz (augmentedOriginalIndex J K hp e)
  choose n hn using hInt
  let q := fun e => (n e).toNat
  have hq (e : Fin J.m) : f e=(q e:ℝ) := by
    have hNon : 0≤(n e:ℝ) := (hn e) ▸ (hOpt.1.2 e).1
    have hh : 0≤n e := by exact_mod_cast hNon
    have he : (q e:ℤ)=n e := Int.toNat_of_nonneg hh
    rw [hn e,← he,Int.cast_natCast]
  refine ⟨q,?_,?_,?_⟩
  · intro e
    have he : (g (augmentedOriginalIndex J K hp e):ℝ)=(q e:ℝ) := hq e
    exact_mod_cast he
  · exact (funext hq) ▸ hOpt
  · intro e
    have h := (hOpt.1.2 e).2
    rw [hq e] at h
    exact_mod_cast h

end MinCostFlow.IPM.Machine
