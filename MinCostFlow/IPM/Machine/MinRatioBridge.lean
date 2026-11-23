module

public import MinCostFlow.IPM.Machine.MinRatioContract

import Mathlib.Data.Finset.Lattice.Fold

/-!
# Connecting the machine calls to the model history

The machine contract uses exactly the model's abstract state. This file
proves that decoded Update, Query and Detect calls follow that history.
Update uses the actual normalization in its output block. Its success
bit cannot report failure on a hidden-stable prefix. Query gives the
model's accumulated flow, and Detect gives the exact set defined using
`last_e`, including every accumulated actual increment.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The machine Update advances the exact model state at its decoded
actual normalization. Its batch, gradients and lengths are the inputs
of the current history stage. No unrounded-normalization identity is
assumed or substituted for the block returned by the machine. -/
theorem minRatioMachine_update_transition {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hop : op (t+1) = true)
    (hbatch : BatchAt mem (args.getD 1 0) (D.U (t+1)))
    (hg : readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m = D.g (t+1))
    (hl : readVector mem (args.getD 3 0) F.fmt.limbBits F.limbs F.fmt.precision m = D.ℓ (t+1))
    (heta : Num.fixVal mem' (heapArg args+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) = eta (t+1))
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 0
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    s' = minRatioState A.eraseFailure D eta op (t+1) ∧
      AnswerAt mem' (heapArg args) (minRatioFailureDirection A D eta op t) ∧
      NormalizationWithin
        (Num.fixVal mem (args.getD 4 0) F.fmt.limbBits F.limbs F.fmt.precision) (eta (t+1)) := by
  obtain ⟨actual, hblock, hnorm, _, hstep⟩ := hq
  have heq : actual = eta (t+1) := hblock.2.symm.trans heta
  subst actual
  have hh := hstep (D.U (t+1)) hbatch
  rw [hg, hl] at hh
  refine ⟨?_, hh.2, hnorm⟩
  simpa only [minRatioState, hop, ↓reduceIte, MinRatioDataStructureWithFailure.eraseFailure] using hh.1

/-- Every finite history prefix has edge and vertex bounds. -/
theorem exists_minRatioHistoryBounded (D : DynamicInstance) (T : ℕ) :
    ∃ M N, MinRatioHistoryBounded D T M N := by
  refine ⟨(Finset.range (T+1)).sup (fun t => (D.G t).m),
    (Finset.range (T+1)).sup (fun t => (D.G t).n), ?_, ?_⟩
  · intro t ht
    exact Finset.le_sup (f := fun t => (D.G t).m) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
  · intro t ht
    exact Finset.le_sup (f := fun t => (D.G t).n) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

/-- On a hidden-stable input prefix satisfying `P`, the machine's success bit is one.
This is derived from the failure-aware model specification on `P`. -/
theorem minRatioMachine_no_failure_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (ht : t+1 ≤ T) (hop : op (t+1) = true)
    (hhidden : D.HiddenStable (t+1) α Ψ) (mem' : ℕ → ℕ) (a : ℕ)
    (hanswer : AnswerAt mem' a (minRatioFailureDirection A D eta op t)) : mem' a = 1 := by
  have hs := (hA D eta op T hvalid hsize hP).2 t ht hop hhidden
  change mem' a = if (minRatioFailureDirection A D eta op t).isSome then 1 else 0 at hanswer
  simpa only [hs, ↓reduceIte] using hanswer

/-- On a hidden-stable input prefix the machine's success bit is one.
This is derived from the original failure-aware model specification,
not an additional guarantee put into the machine's abstract state. -/
theorem minRatioMachine_no_failure_upTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1 ≤ T) (hop : op (t+1) = true)
    (hhidden : D.HiddenStable (t+1) α Ψ) (mem' : ℕ → ℕ) (a : ℕ)
    (hanswer : AnswerAt mem' a (minRatioFailureDirection A D eta op t)) : mem' a = 1 :=
  minRatioMachine_no_failure_upTo_on A κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) D eta op T t
    hvalid hsize (fun _ _ => trivial) ht hop hhidden mem' a hanswer

/-- On a hidden-stable input prefix the machine's success bit is one.
This is derived from the original failure-aware model specification,
not an additional guarantee put into the machine's abstract state. -/
theorem minRatioMachine_no_failure (A : MinRatioDataStructureWithFailure)
    (κ α Ψ eps : ℝ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1 ≤ T) (hop : op (t+1) = true)
    (hhidden : D.HiddenStable (t+1) α Ψ) (mem' : ℕ → ℕ) (a : ℕ)
    (hanswer : AnswerAt mem' a (minRatioFailureDirection A D eta op t)) : mem' a = 1 := by
  obtain ⟨M, N, hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatioMachine_no_failure_upTo A κ α Ψ eps (hA.upTo M N) D eta op T t
    hvalid hsize ht hop hhidden mem' a hanswer

/-- A machine Query returns the accumulated flow of the actual history
along histories satisfying `P`. -/
theorem minRatioMachine_query_flow_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (ht : t ≤ T)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (he : args.getD 1 0 ∈ (D.G t).E)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 1
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    Num.fixVal mem' (heapArg args) F.fmt.limbBits F.limbs F.fmt.precision =
      minRatioFlow A.eraseFailure D eta op t (args.getD 1 0) :=
  hq.2.2.trans ((hA D eta op T hvalid hsize hP).1.1 t ht _ he)

/-- A machine Query returns the accumulated flow of the actual history.
Its fixed-point output format is provided by the machine contract. -/
theorem minRatioMachine_query_flow_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t ≤ T)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (he : args.getD 1 0 ∈ (D.G t).E)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 1
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    Num.fixVal mem' (heapArg args) F.fmt.limbBits F.limbs F.fmt.precision =
      minRatioFlow A.eraseFailure D eta op t (args.getD 1 0) :=
  minRatioMachine_query_flow_upTo_on F A G m κ α Ψ eps rate allocation (hA.upToOn (P := fun _ _ => True))
    D eta op T t hvalid hsize (fun _ _ => trivial) ht s' args mem mem' he hq

/-- A machine Query returns the accumulated flow of the actual history.
Its fixed-point output format is provided by the machine contract. -/
theorem minRatioMachine_query_flow {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t ≤ T)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (he : args.getD 1 0 ∈ (D.G t).E)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 1
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    Num.fixVal mem' (heapArg args) F.fmt.limbBits F.limbs F.fmt.precision =
      minRatioFlow A.eraseFailure D eta op t (args.getD 1 0) := by
  obtain ⟨M, N, hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatioMachine_query_flow_upTo F A G m κ α Ψ eps rate allocation (hA.upTo M N)
    D eta op T t hvalid hsize ht s' args mem mem' he hq

/-- A machine Detect produces exactly the source's set based on `last_e`
and actual increments, along histories satisfying `P`. -/
theorem minRatioMachine_detect_set_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N)
    (hP : ∀ s ≤ T, P (D.G s) (D.ℓ s)) (ht : t+1 ≤ T) (hop : op (t+1) = false)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 2
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    DetectAt mem' (heapArg args) (minRatioDetectSet A.eraseFailure D eta op eps t) := by
  have hs := (hA D eta op T hvalid hsize hP).1.2.2 t ht hop
  change (A.detect (minRatioState A.eraseFailure D eta op t)).1 = _ at hs
  rw [← hs]
  exact hq.2.1

/-- A machine Detect produces exactly the source's set based on `last_e`
and actual increments. This holds without hidden stability, so it also
applies to guarded lower-target tests before their first failure. -/
theorem minRatioMachine_detect_set_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1 ≤ T) (hop : op (t+1) = false)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 2
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    DetectAt mem' (heapArg args) (minRatioDetectSet A.eraseFailure D eta op eps t) :=
  minRatioMachine_detect_set_upTo_on F A G m κ α Ψ eps rate allocation (hA.upToOn (P := fun _ _ => True))
    D eta op T t hvalid hsize (fun _ _ => trivial) ht hop s' args mem mem' hq

/-- A machine Detect produces exactly the source's set based on `last_e`
and actual increments. This holds without hidden stability, so it also
applies to guarded lower-target tests before their first failure. -/
theorem minRatioMachine_detect_set {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1 ≤ T) (hop : op (t+1) = false)
    (s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 2
      (minRatioState A.eraseFailure D eta op t) args mem s' mem') :
    DetectAt mem' (heapArg args) (minRatioDetectSet A.eraseFailure D eta op eps t) := by
  obtain ⟨M, N, hsize⟩ := exists_minRatioHistoryBounded D T
  exact minRatioMachine_detect_set_upTo F A G m κ α Ψ eps rate allocation (hA.upTo M N)
    D eta op T t hvalid hsize ht hop s' args mem mem' hq

end MinCostFlow.IPM.Machine
