module

public import MinCostFlow.IPM.EpochMemory
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Coordinate stability between explicit insertions

The witness in Chen et al., arXiv:2203.00671v2, Lemma 9.2
(pages 70--71), needs small displacement on every edge not reinserted
between two stages. In the epoch loop, a stored coordinate changes only
at the refresh following its Detect report. That refresh explicitly
reinserts the edge. Hence, without an intervening insertion, both flows
are close to the same remembered coordinate with the same length.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The remembered flow at an operation stage. A Detect stage uses the
same coefficients as its preceding Update. -/
def epochRemembered (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s : ℕ) : Fin I.m → ℝ :=
  (epochState I U κ r A base ((s-1)/2)).stored

/-- The actual flow before the circulation is selected at an Update
stage, and after the preceding Update at a Detect stage. -/
def epochStageFlow (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s : ℕ) : Fin I.m → ℝ := epochFlow I U κ r A base (s/2)

private theorem remembered_adjacent (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s : ℕ) (hs : 1 ≤ s) (e : Fin I.m)
    (hnot : (epochInstance I U κ r A base).NotInsertedBetween e (s-1) s) :
    epochRemembered I U κ r A base s e = epochRemembered I U κ r A base (s-1) e := by
  let t := (s-1)/2
  by_cases hodd : s%2 = 1
  · have hpend : (e : ℕ) ∉ (epochState I U κ r A base t).pending := by
      intro hm
      obtain ⟨u, hu, hins⟩ := (refreshEdges_inserts (namedInstance I)
        (epochState I U κ r A base t).pending.toList e).mpr (Finset.mem_toList.mpr hm)
      have hu' : u ∈ (epochInstance I U κ r A base).U s := by
        simpa only [epochInstance, hodd, ↓reduceIte] using hu
      exact hnot s (by omega) le_rfl u hu' hins
    change (epochState I U κ r A base t).stored e =
      (epochState I U κ r A base ((s-1-1)/2)).stored e
    by_cases ht : t = 0
    · have ht' : (s-1-1)/2 = 0 := by dsimp only [t] at ht; omega
      rw [ht, ht']
    · have hidx : t = (s-1-1)/2+1 := by dsimp only [t] at *; omega
      rw [hidx] at hpend ⊢
      exact epoch_stored_unchanged I U κ r A base _ e hpend
  · have hidx : (s-1)/2 = (s-1-1)/2 := by omega
    exact congrArg (fun j => (epochState I U κ r A base j).stored e) hidx

/-- Without an explicit insertion, the remembered coordinate does not
change between any two operation stages. -/
theorem epoch_remembered_notInserted (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s t : ℕ) (hst : s ≤ t) (e : Fin I.m)
    (hnot : (epochInstance I U κ r A base).NotInsertedBetween e s t) :
    epochRemembered I U κ r A base t e = epochRemembered I U κ r A base s e := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    have hprev : (epochInstance I U κ r A base).NotInsertedBetween e s t := by
      intro j hj hji u hu
      exact hnot j hj (Nat.le_succ_of_le hji) u hu
    have hadj : (epochInstance I U κ r A base).NotInsertedBetween e (t+1-1) (t+1) := by
      intro j hj hji u hu
      exact hnot j (by omega) hji u hu
    rw [remembered_adjacent I U κ r A base (t+1) (by omega) e hadj, Nat.add_sub_cancel]
    exact ih hprev

/-- The coordinate error before the next refresh is at most the previous
Detect error plus the weighted movement of that Update. -/
theorem epoch_before_refresh_error (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*(t+1) ≤ T) (he : 0 ≤ ε)
    (hmove : weightedLength (lengths I (alpha I U) (epochState I U κ r A base t).stored)
      (fun e => epochIncrement I U κ r A base t e) ≤ ε) (e : Fin I.m) :
    |lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      (epochFlow I U κ r A base (t+1) e-(epochState I U κ r A base t).stored e)| ≤ 2*ε := by
  have herror := epoch_stored_error I U κ r α Ψ ε A base T t hA hvalid (by omega) he e
  have hsingle : |lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      epochIncrement I U κ r A base t e| ≤ ε :=
    (Finset.single_le_sum (fun j _ => abs_nonneg _) (Finset.mem_univ e)).trans hmove
  rw [epoch_flow_step I U κ r α Ψ ε A base T t hA hvalid ht]
  have hid : lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      (epochFlow I U κ r A base t e+epochIncrement I U κ r A base t e-
        (epochState I U κ r A base t).stored e) =
    lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      (epochFlow I U κ r A base t e-(epochState I U κ r A base t).stored e)+
    lengths I (alpha I U) (epochState I U κ r A base t).stored e*epochIncrement I U κ r A base t e := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [herror, hsingle])

/-- Every operation stage has remembered-coordinate error at most two
thresholds, including the Detect stage before its reports are refreshed. -/
theorem epoch_stage_error (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (he : 0 ≤ ε)
    (hmove : ∀ t, 2*(t+1) ≤ T → weightedLength
      (lengths I (alpha I U) (epochState I U κ r A base t).stored)
      (fun e => epochIncrement I U κ r A base t e) ≤ ε)
    (s : ℕ) (hs : s ≤ T) (e : Fin I.m) :
    |lengths I (alpha I U) (epochRemembered I U κ r A base s) e*
      (epochStageFlow I U κ r A base s e-epochRemembered I U κ r A base s e)| ≤ 2*ε := by
  by_cases hsame : s/2 = (s-1)/2
  · unfold epochStageFlow epochRemembered
    rw [hsame]
    exact (epoch_stored_error I U κ r α Ψ ε A base T ((s-1)/2) hA hvalid (by omega) he e).trans
      (by linarith only [he])
  · have hidx : s = 2*((s-1)/2+1) := by omega
    have hdiv : s/2 = (s-1)/2+1 := by omega
    unfold epochStageFlow epochRemembered
    rw [hdiv]
    exact epoch_before_refresh_error I U κ r α Ψ ε A base T ((s-1)/2) hA hvalid (by omega)
      he (hmove _ (by omega)) e

/-- With no intervening insertion, both operation-stage flows are close
to the same remembered coordinate and use the same stored length.
The displacement bound is four Detect thresholds. -/
theorem epoch_notInserted_displacement (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (he : 0 ≤ ε)
    (hmove : ∀ j, 2*(j+1) ≤ T → weightedLength
      (lengths I (alpha I U) (epochState I U κ r A base j).stored)
      (fun e => epochIncrement I U κ r A base j e) ≤ ε)
    (s t : ℕ) (hst : s ≤ t) (ht : t ≤ T) (e : Fin I.m)
    (hnot : (epochInstance I U κ r A base).NotInsertedBetween e s t) :
    lengths I (alpha I U) (epochRemembered I U κ r A base t) e =
        lengths I (alpha I U) (epochRemembered I U κ r A base s) e ∧
      |lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
        (epochStageFlow I U κ r A base t e-epochStageFlow I U κ r A base s e)| ≤ 4*ε := by
  have hcoord := epoch_remembered_notInserted I U κ r A base s t hst e hnot
  have hℓ : lengths I (alpha I U) (epochRemembered I U κ r A base t) e =
      lengths I (alpha I U) (epochRemembered I U κ r A base s) e := by
    unfold lengths
    rw [hcoord]
  refine ⟨hℓ, ?_⟩
  have hnew := epoch_stage_error I U κ r α Ψ ε A base T hA hvalid he hmove t ht e
  have hold := epoch_stage_error I U κ r α Ψ ε A base T hA hvalid he hmove s (hst.trans ht) e
  rw [← hℓ] at hold
  have hid : lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
      (epochStageFlow I U κ r A base t e-epochStageFlow I U κ r A base s e) =
    lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
      (epochStageFlow I U κ r A base t e-epochRemembered I U κ r A base t e)-
    lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
      (epochStageFlow I U κ r A base s e-epochRemembered I U κ r A base s e) := by
    rw [hcoord]
    ring
  rw [hid]
  have htri := abs_sub_le
    (lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
      (epochStageFlow I U κ r A base t e-epochRemembered I U κ r A base t e)) 0
    (lengths I (alpha I U) (epochRemembered I U κ r A base t) e*
      (epochStageFlow I U κ r A base s e-epochRemembered I U κ r A base s e))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  linarith only [htri, hnew, hold]

end MinCostFlow.IPM
