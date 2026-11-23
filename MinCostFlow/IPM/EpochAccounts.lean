module

public import MinCostFlow.IPM.EpochMemory
public import MinCostFlow.IPM.DetectCount
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Movement accounts for the actual epoch Detect calls

Chen et al., arXiv:2203.00671v2, Lemma 9.4 (pages 71--72), charges each
reported edge to its movement since the last report. This file identifies
the abstract accounts in `DetectCount` with the actual scaled increments
and last-report times of the epoch loop. Length changes occur only when
the account resets. Thus the charging proof applies to Definition 4.5's
exact Detect operation.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Detect's pending edge set in the finite coordinates of the IPM. -/
def epochReports (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) : Finset (Fin I.m) :=
  Finset.univ.filter fun e => (e : ℕ) ∈ (epochState I U κ r A base t).pending

/-- Absolute weighted movement in one Update. The length is the value
before the following Detect and any coefficient refresh. -/
def epochMovement (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : ℕ → Fin I.m → ℝ
  | 0, _ => 0
  | t+1, e => |lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      epochIncrement I U κ r A base t e|

/-- A positive even stage leaves the last-report index unchanged until
its Detect output is incorporated. The preceding Update never reports. -/
theorem epoch_last_before_detect (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t e : ℕ) :
    minRatioLast A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t+1) e =
      epochLast I U κ r A base t e := by
  have hop : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  conv_lhs => unfold minRatioLast
  simp only [hop, Bool.true_eq_false, false_and, ↓reduceIte]
  rfl

/-- Every weighted movement account equals the exact sum since the most
recent Detect report. This accounts for changes of lengths at reports. -/
theorem epoch_account_eq (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) (e : Fin I.m) :
    detectAccount (epochMovement I U κ r A base) (epochReports I U κ r A base) n e =
      lengths I (alpha I U) (epochState I U κ r A base n).stored e*
        ∑ j ∈ Finset.Ioc (epochLast I U κ r A base n e) (2*n),
          |minRatioIncrement A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate j e| := by
  classical
  induction n with
  | zero => simp only [detectAccount, epochLast, minRatioLast,
      Finset.Ioc_self, Finset.sum_empty, mul_zero]
  | succ n ih =>
    have hi := ih (by omega)
    have hm : (e ∈ epochReports I U κ r A base (n+1)) ↔
        (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending := by
      simp only [epochReports, Finset.mem_filter, Finset.mem_univ, true_and]
    have hrec : detectAccount (epochMovement I U κ r A base) (epochReports I U κ r A base) (n+1) e =
        if e ∈ epochReports I U κ r A base (n+1) then 0 else
          detectAccount (epochMovement I U κ r A base) (epochReports I U κ r A base) n e+
            epochMovement I U κ r A base (n+1) e := by rfl
    rw [hrec, epochLast_succ]
    by_cases he : (e : ℕ) ∈ (epochState I U κ r A base (n+1)).pending
    · simp only [hm, he, ↓reduceIte, Finset.Ioc_self, Finset.sum_empty, mul_zero]
    · simp only [hm, he, ↓reduceIte]
      rw [hi]
      have hcoord := epoch_stored_unchanged I U κ r A base n e he
      have hℓ : lengths I (alpha I U) (epochState I U κ r A base (n+1)).stored e =
          lengths I (alpha I U) (epochState I U κ r A base n).stored e := by
        unfold lengths
        rw [hcoord]
      rw [hℓ]
      have hidx : 2*(n+1) = (2*n+1)+1 := by omega
      have hlast := minRatioLast_le A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*n) e
      change epochLast I U κ r A base n e ≤ 2*n at hlast
      rw [hidx, Finset.sum_Ioc_succ_top (hlast.trans (by omega)),
        epoch_detect_increment_zero I U κ r A base n, abs_zero, add_zero,
        Finset.sum_Ioc_succ_top hlast]
      have hpos : 0 < lengths I (alpha I U) (epochState I U κ r A base n).stored e := by
        have hh := (hvalid.2.1 (2*n+1) (by omega)).2 e (Finset.mem_range.mpr e.2)
        have hi : (2*n+1-1)/2 = n := by omega
        simpa only [epochInstance, hi, namedVector_fin] using hh
      change _+|lengths I (alpha I U) (epochState I U κ r A base n).stored e*
        epochIncrement I U κ r A base n e| = _
      rw [abs_mul, abs_of_pos hpos]
      unfold epochIncrement
      ring

/-- Every actual Detect report is paid for by the corresponding movement
account. This derives the charging hypothesis of Lemma 9.4 from the
operation specification. -/
theorem epoch_report_paid (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*(t+1) ≤ T) (e : Fin I.m) (he : e ∈ epochReports I U κ r A base (t+1)) :
    ε ≤ detectAccount (epochMovement I U κ r A base) (epochReports I U κ r A base) t e+
      epochMovement I U κ r A base (t+1) e := by
  have hmem : (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending := (Finset.mem_filter.mp he).2
  have hraw := (epoch_pending_iff I U κ r A base t e).mp hmem
  have hfalse : epochIsUpdate ((2*t+1)+1) = false := by
    unfold epochIsUpdate
    apply decide_eq_false
    omega
  have hd := (hA _ (epochEta I U κ) epochIsUpdate T hvalid).2.2 (2*t+1) (by omega) hfalse
  change (A.detect (epochTrace I U κ r A base (2*t+1))).1 = _ at hd
  rw [(epochTrace_pair I U κ r A base t).2] at hd
  rw [hd] at hraw
  have hp := (Finset.mem_filter.mp hraw).2
  have hlast := minRatioLast_le A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t) e
  change epochLast I U κ r A base t e ≤ 2*t at hlast
  change ε ≤ (epochInstance I U κ r A base).ℓ ((2*t+1)+1) e*
    (∑ j ∈ Finset.Ioc (minRatioLast A _ _ _ (2*t+1) e) ((2*t+1)+1),
      |minRatioIncrement A _ _ _ j e|) at hp
  rw [epoch_last_before_detect, Finset.sum_Ioc_succ_top (hlast.trans (by omega)),
    epoch_detect_increment_zero I U κ r A base t, abs_zero, add_zero,
    Finset.sum_Ioc_succ_top hlast] at hp
  have hindex : ((2*t+1)+1-1)/2 = t := by omega
  have hℓ : (epochInstance I U κ r A base).ℓ ((2*t+1)+1) e =
      lengths I (alpha I U) (epochState I U κ r A base t).stored e := by
    simp only [epochInstance, hindex, namedVector_fin]
  have hpos : 0 < lengths I (alpha I U) (epochState I U κ r A base t).stored e := by
    rw [← hℓ]
    exact (hvalid.2.1 _ (by omega)).2 e (Finset.mem_range.mpr e.2)
  rw [hℓ, mul_add] at hp
  rw [epoch_account_eq I U κ r A base T t hvalid (by omega)]
  change ε ≤ _+|lengths I (alpha I U) (epochState I U κ r A base t).stored e*
    epochIncrement I U κ r A base t e|
  rw [abs_mul, abs_of_pos hpos]
  exact hp

/-- The two representations of the reported edge set have equal size. -/
theorem epochReports_card (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) :
    (epochReports I U κ r A base t).card = (epochState I U κ r A base t).pending.card := by
  classical
  apply Finset.card_bij (fun (e : Fin I.m) _ => (e : ℕ))
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · intro e _ e' _ heq
    exact Fin.ext heq
  · intro e he
    have heI := epoch_pending_mem I U κ r A base t e he
    exact ⟨⟨e, heI⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

/-- The number of coordinate Queries is exactly the total report count. -/
theorem epoch_queries_eq (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) :
    (epochState I U κ r A base n).queries =
      ∑ t ∈ Finset.range n, (epochReports I U κ r A base (t+1)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, epochReports_card]
    rfl

/-- Primitive refresh updates have total size at most twice the Query
count. A pending final report has not yet been refreshed. -/
theorem epoch_updateSize_le (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) :
    (epochState I U κ r A base n).updateSize ≤ 2*(epochState I U κ r A base n).queries := by
  have hh : ∀ n, (epochState I U κ r A base n).updateSize+
      2*(epochState I U κ r A base n).pending.card = 2*(epochState I U κ r A base n).queries := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((epochState I U κ r A base n).updateSize+2*(epochState I U κ r A base n).pending.card)+
          2*(epochState I U κ r A base (n+1)).pending.card =
        2*((epochState I U κ r A base n).queries+(epochState I U κ r A base (n+1)).pending.card)
      omega
  have h := hh n
  omega

/-- Applying Lemma 9.4 to the actual epoch reports bounds all coordinate
Queries and primitive refresh updates. The movement bound is the only
numerical input, supplied by the normalized min-ratio update analysis. -/
theorem epoch_refresh_counts (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) (he : 0 < ε)
    (hmove : ∀ t < n, weightedLength
      (lengths I (alpha I U) (epochState I U κ r A base t).stored)
      (fun e => epochIncrement I U κ r A base t e) ≤ 5*ε) :
    (epochState I U κ r A base n).queries ≤ 5*n ∧
      (epochState I U κ r A base n).updateSize ≤ 10*n := by
  have hcount := lemma_9_4 (epochMovement I U κ r A base) (epochReports I U κ r A base) ε n he
    (by
      intro t e
      cases t with
      | zero => exact le_rfl
      | succ t => exact abs_nonneg _)
    (by intro t ht e he; exact epoch_report_paid I U κ r α Ψ ε A base T t hA hvalid (by omega) e he)
    (by intro t ht; exact hmove t ht)
  rw [epoch_queries_eq]
  refine ⟨hcount, ?_⟩
  have hh := epoch_updateSize_le I U κ r A base n
  rw [epoch_queries_eq] at hh
  omega

/-- A specified Detect never returns names outside the fixed graph, so
the epoch's total raw Detect output size equals its coordinate Query count. -/
theorem epoch_detected_eq_queries (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) :
    (epochState I U κ r A base n).detected = (epochState I U κ r A base n).queries := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (by omega)
    have hfalse : epochIsUpdate ((2*n+1)+1) = false := by
      unfold epochIsUpdate
      apply decide_eq_false
      omega
    have hd := (hA _ (epochEta I U κ) epochIsUpdate T hvalid).2.2 (2*n+1) (by omega) hfalse
    change (A.detect (epochTrace I U κ r A base (2*n+1))).1 = _ at hd
    rw [(epochTrace_pair I U κ r A base n).2] at hd
    let S := (A.detect (epochUpdate I U κ r A (epochState I U κ r A base n)).1).1
    have hfilter : S.filter (fun e => e < I.m) = S := by
      apply Finset.filter_eq_self.mpr
      intro e he
      change e ∈ (A.detect (epochUpdate I U κ r A (epochState I U κ r A base n)).1).1 at he
      rw [hd] at he
      exact Finset.mem_range.mp (Finset.mem_filter.mp he).1
    change (epochState I U κ r A base n).detected+S.card =
      (epochState I U κ r A base n).queries+(S.filter (fun e => e < I.m)).card
    rw [hi, hfilter]

end MinCostFlow.IPM
