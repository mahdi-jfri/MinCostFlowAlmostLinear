module

public import MinCostFlow.IPM.EpochQuery
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The remembered coordinate is the last reported flow value

In Algorithm 7 (Chen et al., arXiv:2203.00671v2, Section 9, page 69),
each stored coordinate is replaced exactly when Detect reports it.
This file proves that it equals the represented flow at its most recent
Detect report, or the base flow if never reported. The proof uses the
exact Query semantics and the `last_e` history of Definition 4.5.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Most recent report of edge `e` after an epoch's first `t` iterations. -/
def epochLast (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t e : ℕ) : ℕ :=
  minRatioLast A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t) e

/-- For original edges, filtering the Detect output does not change
whether the edge is pending a coefficient refresh. -/
theorem epoch_pending_iff (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) (e : Fin I.m) :
    (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending ↔
      (e : ℕ) ∈ (A.detect (epochUpdate I U κ r A (epochState I U κ r A base t)).1).1 := by
  change (e : ℕ) ∈ (A.detect (epochUpdate I U κ r A (epochState I U κ r A base t)).1).1.filter
    (fun e => e < I.m) ↔ _
  simp only [Finset.mem_filter, e.2, and_true]

/-- The most recent report changes precisely for reported edges. -/
theorem epochLast_succ (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) (e : Fin I.m) :
    epochLast I U κ r A base (t+1) e =
      if (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending then 2*(t+1)
      else epochLast I U κ r A base t e := by
  have hodd : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  have heven : epochIsUpdate ((2*t+1)+1) = false := by
    unfold epochIsUpdate
    apply decide_eq_false
    omega
  have hidx : 2*(t+1) = (2*t+1)+1 := by omega
  unfold epochLast
  rw [hidx]
  conv_lhs => unfold minRatioLast
  simp only [heven, true_and]
  change (if (e : ℕ) ∈ (A.detect (epochTrace I U κ r A base (2*t+1))).1 then (2*t+1)+1
    else minRatioLast A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t+1) e) = _
  rw [(epochTrace_pair I U κ r A base t).2]
  have hlast : minRatioLast A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t+1) e =
      minRatioLast A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t) e := by
    conv_lhs => unfold minRatioLast
    simp only [hodd, Bool.true_eq_false, false_and, ↓reduceIte]
  rw [hlast]
  simp only [epoch_pending_iff]

/-- Every stored coordinate is exactly the flow at the most recent
Detect report, expressed as the base plus the accumulated increments.
The statement holds on every valid prefix, without a hidden witness. -/
theorem epoch_stored_at_last (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) (e : Fin I.m) :
    (epochState I U κ r A base n).stored e =
      base e+epochAccum I U κ r A base (epochLast I U κ r A base n e) e := by
  induction n with
  | zero =>
    change base e = base e+minRatioFlow A _ _ _ 0 e
    rw [minRatioFlow_zero, add_zero]
  | succ n ih =>
    have hi := ih (by omega)
    rw [epochLast_succ]
    by_cases he : (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending
    · rw [ite_eq_left he]
      have hquery := epoch_query I U κ r α Ψ ε A base T (n+1) hA hvalid hn e
      change (if (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending then
        epochFlow I U κ r A base (n+1) e else _) = _
      rw [ite_eq_left he]
      exact hquery
    · rw [ite_eq_right he, epoch_stored_unchanged I U κ r A base n e he]
      exact hi

/-- Exact Detect semantics bound every remembered-coordinate error by
its threshold after each Update--Detect pair. This derives the numerical
input to Lemma 9.1 from Definition 4.5, rather than assuming it. -/
theorem epoch_stored_error (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) (he : 0 ≤ ε) (e : Fin I.m) :
    |lengths I (alpha I U) (epochState I U κ r A base n).stored e*
      (epochFlow I U κ r A base n e-(epochState I U κ r A base n).stored e)| ≤ ε := by
  cases n with
  | zero =>
    rw [epoch_query I U κ r α Ψ ε A base T 0 hA hvalid (by omega)]
    change |lengths I (alpha I U) base e*(base e+minRatioFlow A _ _ _ 0 e-base e)| ≤ ε
    rw [minRatioFlow_zero, add_zero, sub_self, mul_zero, abs_zero]
    exact he
  | succ n =>
    let D := epochInstance I U κ r A base
    let η := epochEta I U κ
    have hfalse : epochIsUpdate ((2*n+1)+1) = false := by
      unfold epochIsUpdate
      apply decide_eq_false
      omega
    have hidx : 2*(n+1) = (2*n+1)+1 := by omega
    by_cases hmem : (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending
    · have hstored : (epochState I U κ r A base (n+1)).stored e =
          epochFlow I U κ r A base (n+1) e := by
        change (if (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending then _ else _) = _
        rw [ite_eq_left hmem]
        rfl
      rw [hstored, sub_self, mul_zero, abs_zero]
      exact he
    · have hnraw : (e : ℕ) ∉ (A.detect (epochUpdate I U κ r A (epochState I U κ r A base n)).1).1 :=
        fun hh => hmem ((epoch_pending_iff I U κ r A base n e).mpr hh)
      have hdetect := (hA D η epochIsUpdate T hvalid).2.2 (2*n+1) (by omega) hfalse
      change (A.detect (epochTrace I U κ r A base (2*n+1))).1 = _ at hdetect
      rw [(epochTrace_pair I U κ r A base n).2] at hdetect
      have hbound : D.ℓ (2*(n+1)) e*
          (∑ j ∈ Finset.Ioc (minRatioLast A D η epochIsUpdate (2*n+1) e) (2*(n+1)),
            |minRatioIncrement A D η epochIsUpdate j e|) < ε := by
        apply lt_of_not_ge
        intro hh
        apply hnraw
        rw [hdetect]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr e.2, by simpa only [hidx] using hh⟩
      have hlast : epochLast I U κ r A base (n+1) e =
          minRatioLast A D η epochIsUpdate (2*n+1) e := by
        change minRatioLast A D η epochIsUpdate (2*(n+1)) e = _
        rw [hidx]
        conv_lhs => unfold minRatioLast
        simp only [hfalse, true_and]
        change (if (e : ℕ) ∈ (A.detect (epochTrace I U κ r A base (2*n+1))).1 then _ else _) = _
        rw [(epochTrace_pair I U κ r A base n).2, ite_eq_right hnraw]
      have hcoord := epoch_stored_unchanged I U κ r A base n e hmem
      have hℓ : D.ℓ (2*(n+1)) e = lengths I (alpha I U)
          (epochState I U κ r A base (n+1)).stored e := by
        have hindex : (2*(n+1)-1)/2 = n := by omega
        change namedVector (lengths I (alpha I U)
          (epochState I U κ r A base ((2*(n+1)-1)/2)).stored) e = _
        rw [hindex, namedVector_fin]
        unfold lengths
        rw [hcoord]
      have hℓpos : 0 < D.ℓ (2*(n+1)) e := (hvalid.2.1 _ hn).2 e (Finset.mem_range.mpr e.2)
      rw [← hℓ, epoch_query I U κ r α Ψ ε A base T (n+1) hA hvalid hn,
        epoch_stored_at_last I U κ r α Ψ ε A base T (n+1) hA hvalid hn, hlast]
      have hid : (base e+epochAccum I U κ r A base (2*(n+1)) e)-
          (base e+epochAccum I U κ r A base (minRatioLast A D η epochIsUpdate (2*n+1) e) e) =
          minRatioFlow A D η epochIsUpdate (2*(n+1)) e-
            minRatioFlow A D η epochIsUpdate (minRatioLast A D η epochIsUpdate (2*n+1) e) e := by
        change (base e+minRatioFlow A D η epochIsUpdate (2*(n+1)) e)-
          (base e+minRatioFlow A D η epochIsUpdate (minRatioLast A D η epochIsUpdate (2*n+1) e) e) = _
        ring
      rw [hid, minRatioFlow_sub A D η epochIsUpdate _ _ e
        ((minRatioLast_le A D η epochIsUpdate (2*n+1) e).trans (by omega)),
        abs_mul, abs_of_pos hℓpos]
      exact (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hℓpos.le).trans hbound.le

end MinCostFlow.IPM
