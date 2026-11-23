module

public import MinCostFlow.IPM.EpochTrace
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Query and Detect semantics within an IPM epoch

The operation specification of Definition 4.5 (page 14) gives exact
flow queries, even without a hidden-stability witness. This file relates
the epoch's mathematical flow to the sum of the scaled data structure
increments. It then proves that one epoch iteration adds its Update
increment and that Detect itself leaves the represented flow unchanged.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The abstract accumulated flow of an epoch's operation history. -/
@[expose] def epochAccum (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s e : ℕ) : ℝ :=
  minRatioFlow A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate s e

/-- The increment at an epoch's Update stage, extended by zero outside
the original edge set as in the data structure specification. -/
@[expose] def epochIncrement (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t e : ℕ) : ℝ :=
  minRatioIncrement A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t+1) e

/-- Exact Query semantics after an epoch's `t` Update--Detect pairs. -/
theorem epoch_query (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*t ≤ T) (e : Fin I.m) :
    epochFlow I U κ r A base t e = base e+epochAccum I U κ r A base (2*t) e := by
  have hs := (hA _ (epochEta I U κ) epochIsUpdate T hvalid).1 (2*t) ht e
    (show (e : ℕ) ∈ ((epochInstance I U κ r A base).G (2*t)).E from Finset.mem_range.mpr e.2)
  change A.query (epochTrace I U κ r A base (2*t)) e = _ at hs
  rw [(epochTrace_pair I U κ r A base t).1] at hs
  exact congrArg (fun z => base e+z) hs

/-- Detect has zero flow increment at each positive even stage. -/
theorem epoch_detect_increment_zero (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t e : ℕ) :
    minRatioIncrement A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t+2) e = 0 := by
  have hop : epochIsUpdate (2*t+2) = false := by
    unfold epochIsUpdate
    apply decide_eq_false
    omega
  have heq : 2*t+2 = (2*t+1)+1 := by omega
  rw [heq]
  simp only [minRatioIncrement, hop, Bool.false_eq_true, false_and, ↓reduceIte]

/-- Two successive represented flows differ by exactly the normalized
circulation added by the Update between them. -/
theorem epoch_flow_step (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*(t+1) ≤ T) (e : Fin I.m) :
    epochFlow I U κ r A base (t+1) e =
      epochFlow I U κ r A base t e+epochIncrement I U κ r A base t e := by
  rw [epoch_query I U κ r α Ψ ε A base T (t+1) hA hvalid ht,
    epoch_query I U κ r α Ψ ε A base T t hA hvalid (by omega)]
  have heq : 2*(t+1) = (2*t+1)+1 := by omega
  unfold epochAccum epochIncrement
  rw [heq, minRatioFlow_succ, epoch_detect_increment_zero I U κ r A base t,
    add_zero, minRatioFlow_succ]
  ring

/-- The flow difference between two stages is the sum of the intervening
scaled increments. This is the telescoping identity used by Detect. -/
theorem minRatioFlow_sub (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (s t e : ℕ) (hst : s ≤ t) :
    minRatioFlow A D η op t e-minRatioFlow A D η op s e =
      ∑ j ∈ Finset.Ioc s t, minRatioIncrement A D η op j e := by
  induction t, hst using Nat.le_induction with
  | base => simp only [sub_self, Finset.Ioc_self, Finset.sum_empty]
  | succ t hst ih =>
    rw [minRatioFlow_succ, Finset.sum_Ioc_succ_top hst, ← ih]
    ring

end MinCostFlow.IPM
