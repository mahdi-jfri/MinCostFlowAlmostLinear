module

public import MinCostFlow.IPM.LazyAlgorithm
import Lean.Elab.Tactic.Omega

/-!
# Relating the IPM epoch to the data structure history

The single-flow adaptation of Algorithm 7 (Chen et al.,
arXiv:2203.00671v2, Section 9, page 69) alternates one Update and one
Detect. This file proves that its causal epoch states are exactly the
states obtained by the operation history in `MinRatioSpec`. It also
proves that pending refreshes are graph edges and that unreported
coordinates retain their stored values.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The abstract operation-history state for the epoch input sequence. -/
def epochTrace (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) : A.State :=
  minRatioState A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate t

private theorem odd_isUpdate (t : ℕ) : epochIsUpdate (2*t+1) = true := by
  unfold epochIsUpdate
  apply decide_eq_true
  omega

private theorem even_isDetect (t : ℕ) : epochIsUpdate (2*t+2) = false := by
  unfold epochIsUpdate
  apply decide_eq_false
  omega

private theorem epochTrace_odd_of_even (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ)
    (heven : epochTrace I U κ r A base (2*t) = (epochState I U κ r A base t).ds) :
    epochTrace I U κ r A base (2*t+1) =
      (epochUpdate I U κ r A (epochState I U κ r A base t)).1 := by
  have hstep : epochTrace I U κ r A base (2*t+1) =
      if epochIsUpdate (2*t+1) then
        (A.update (epochTrace I U κ r A base (2*t))
          ((epochInstance I U κ r A base).U (2*t+1))
          ((epochInstance I U κ r A base).g (2*t+1))
          ((epochInstance I U κ r A base).ℓ (2*t+1)) (epochEta I U κ (2*t+1))).1
      else (A.detect (epochTrace I U κ r A base (2*t))).2 := by rfl
  simp only [hstep, odd_isUpdate, ↓reduceIte, heven]
  have hmod : (2*t+1)%2 = 1 := by omega
  have hidx : (2*t+1-1)/2 = t := by omega
  simp only [epochInstance, epochEta, hmod, hidx, ↓reduceIte, epochUpdate]

/-- The epoch's stored data structure state is the state after its Update
and Detect pair. The intervening state is the Update's returned state. -/
theorem epochTrace_pair (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) :
    epochTrace I U κ r A base (2*t) = (epochState I U κ r A base t).ds ∧
      epochTrace I U κ r A base (2*t+1) =
        (epochUpdate I U κ r A (epochState I U κ r A base t)).1 := by
  induction t with
  | zero =>
    have he : epochTrace I U κ r A base (2*0) = (epochState I U κ r A base 0).ds := by rfl
    exact ⟨he, epochTrace_odd_of_even I U κ r A base 0 he⟩
  | succ t ih =>
    have he : epochTrace I U κ r A base (2*(t+1)) = (epochState I U κ r A base (t+1)).ds := by
      have hidx : 2*(t+1) = (2*t+1)+1 := by omega
      rw [hidx]
      have hstep : epochTrace I U κ r A base ((2*t+1)+1) =
          if epochIsUpdate ((2*t+1)+1) then
            (A.update (epochTrace I U κ r A base (2*t+1))
              ((epochInstance I U κ r A base).U ((2*t+1)+1))
              ((epochInstance I U κ r A base).g ((2*t+1)+1))
              ((epochInstance I U κ r A base).ℓ ((2*t+1)+1))
              (epochEta I U κ ((2*t+1)+1))).1
          else (A.detect (epochTrace I U κ r A base (2*t+1))).2 := by rfl
      simp only [hstep, show epochIsUpdate ((2*t+1)+1) = false from even_isDetect t,
        Bool.false_eq_true, ↓reduceIte, ih.2]
      rfl
    exact ⟨he, epochTrace_odd_of_even I U κ r A base (t+1) he⟩

/-- Every pending refresh has an original edge name, even before the
specification of the supplied data structure is used. -/
theorem epoch_pending_mem (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t e : ℕ) (he : e ∈ (epochState I U κ r A base t).pending) :
    e < I.m := by
  cases t with
  | zero => exact False.elim (Finset.notMem_empty _ he)
  | succ t => exact (Finset.mem_filter.mp he).2

/-- An edge not reported by the preceding Detect retains its stored flow
coordinate. This is the only way stored coordinates change in an epoch. -/
theorem epoch_stored_unchanged (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) (e : Fin I.m)
    (he : (e : ℕ) ∉ (epochState I U κ r A base (t+1)).pending) :
    (epochState I U κ r A base (t+1)).stored e = (epochState I U κ r A base t).stored e := by
  change (if (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending then _ else _) = _
  rw [ite_eq_right he]

/-- The epoch input history satisfies every structural requirement of the
min-ratio specification whenever its stored coordinates stay strictly
inside capacities. This proof does not assume hidden stability. -/
theorem epoch_history_valid_prefix (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid)
    (hstored : ∀ t ≤ (n-1)/2, StrictlyInside I (epochState I U κ r A base t).stored) :
    MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate n := by
  have hG := namedInstance_valid I hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs _
    change (namedInstance I).BatchIsValid ((epochInstance I U κ r A base).U s) ∧
      namedInstance I = (namedInstance I).applyBatch ((epochInstance I U κ r A base).U s)
    dsimp only [epochInstance]
    split_ifs with hodd
    · have hh := refreshEdges_spec (namedInstance I) hG
        (epochState I U κ r A base ((s-1)/2)).pending.toList (by
          intro e he
          exact Finset.mem_range.mpr (epoch_pending_mem I U κ r A base _ e (Finset.mem_toList.mp he)))
      exact ⟨hh.1, hh.2.1.symm⟩
    · exact ⟨trivial, rfl⟩
  · intro s hs
    refine ⟨hG, ?_⟩
    intro e he
    have heI : e < I.m := Finset.mem_range.mp he
    have ht : (s-1)/2 ≤ (n-1)/2 := by omega
    change namedVector (lengths I (alpha I U) (epochState I U κ r A base ((s-1)/2)).stored) e > 0
    simp only [namedVector, heI, ↓reduceDIte]
    exact lengths_pos I (alpha I U) _ (hstored _ ht) ⟨e, heI⟩
  · intro s hs _ hop
    have hnot : s%2 ≠ 1 := by
      intro hh
      have ht : epochIsUpdate s = true := decide_eq_true hh
      rw [hop] at ht
      contradiction
    have hidx : (s-1)/2 = (s-1-1)/2 := by omega
    simp only [epochInstance, hnot, ↓reduceIte, hidx, and_self]
  · intro s hs _ e he hnot
    have heI : e < I.m := Finset.mem_range.mp he
    let t := (s-1)/2
    by_cases hodd : s%2 = 1
    · have hpending : e ∉ (epochState I U κ r A base t).pending := by
        intro hmem
        have hex := (refreshEdges_inserts (namedInstance I)
          (epochState I U κ r A base t).pending.toList e).mpr (Finset.mem_toList.mpr hmem)
        obtain ⟨u, hu, hins⟩ := hex
        have hu' : u ∈ (epochInstance I U κ r A base).U s := by
          simpa only [epochInstance, hodd, ↓reduceIte] using hu
        exact hnot s (by omega) le_rfl u hu' hins
      have hcoord : (epochState I U κ r A base t).stored ⟨e, heI⟩ =
          (epochState I U κ r A base ((s-1-1)/2)).stored ⟨e, heI⟩ := by
        by_cases ht : t = 0
        · have ht' : (s-1-1)/2 = 0 := by dsimp only [t] at ht; omega
          rw [ht, ht']
        · have hidx : t = ((s-1-1)/2)+1 := by dsimp only [t] at *; omega
          rw [hidx] at hpending ⊢
          exact epoch_stored_unchanged I U κ r A base _ ⟨e, heI⟩ hpending
      change namedVector (epochGradient I U r (epochState I U κ r A base t).stored) e = _ ∧
        namedVector (lengths I (alpha I U) (epochState I U κ r A base t).stored) e = _
      simp only [epochInstance, namedVector, heI, ↓reduceDIte, epochGradient,
        gradientWithResidual, lengths, hcoord, and_self]
    · have hidx : (s-1)/2 = (s-1-1)/2 := by omega
      simp only [epochInstance, hidx, and_self]

end MinCostFlow.IPM
