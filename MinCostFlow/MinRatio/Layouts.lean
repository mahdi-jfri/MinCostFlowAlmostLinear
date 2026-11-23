module

public import MinCostFlow.Basic.LSF
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.Num.Representation
public import MinCostFlow.MinRatio.StretchLayout
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Readout layouts for a level of the tree chain

Definition 5.12 (page 22) and Lemma 5.17 (page 23) use low-stretch
forests, lengths, and gradients. Graphs use the dynamic named-graph layout.
Each stored numeric entry uses the fixed-point limbs of the computational model
(page 7). A forest readout has two graph pointers, a root-bit table pointer,
and a stretch descriptor pointer. A collection has a count followed by pointers.
These are memory layouts only. They assert no stretch or cycle-quality bound.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- A fixed-point table indexed by edge names. Only entries on `E` are read.
Each entry occupies `L` limbs, including when edge names have gaps. -/
def EdgeValuesAt (mem : ℕ → ℕ) (a h L P : ℕ) (E : Finset ℕ)
    (values : ℕ → ℝ) : Prop :=
  ∀ e ∈ E, Num.Valid mem (a + e * L) h L ∧
    Num.fixVal mem (a + e * L) h L P = values e

/-- Root membership is stored as a bit for each vertex name. -/
def RootsAt (mem : ℕ → ℕ) (a vCap : ℕ) (R : Finset ℕ) : Prop :=
  (∀ v ∈ R, v < vCap) ∧
  ∀ v < vCap, (v ∈ R ∧ mem (a + v) = 1) ∨ (v ∉ R ∧ mem (a + v) = 0)

/-- Readout of an LSF (Lemma 5.4, page 17).
The four header words point to `T`, `F`, the root bits, and the two-table
stretch descriptor. Its fixed-point numerator and denominator blocks recover
the exact stretch as their quotient.
The domain of the stretch table is the input graph's edge set. -/
def LSFAt (mem : ℕ → ℕ) (a vCap eCap h L P : ℕ) (E : Finset ℕ)
    (forest : LSF) : Prop :=
  DynGraphAt mem (mem a) vCap eCap forest.T ∧
  DynGraphAt mem (mem (a + 1)) vCap eCap forest.F.F ∧
  RootsAt mem (mem (a + 2)) vCap forest.F.R ∧
  StretchValuesAt mem (mem (a + 3)) h L P E forest.wstr

/-- The last-level collection in Definition 5.8 (pages 19–20): its branch
count followed by an array of pointers to LSF readouts. -/
def LSFCollectionAt (mem : ℕ → ℕ) (a vCap eCap h L P : ℕ) (E : Finset ℕ)
    (forests : ℕ × (ℕ → LSF)) : Prop :=
  mem a = forests.1 ∧
  ∀ j < forests.1, LSFAt mem (mem (a + 1 + j)) vCap eCap h L P E (forests.2 j)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- Edge entries depend only on their own limbs. -/
theorem EdgeValuesAt.congr {mem mem' : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {values : ℕ → ℝ} (hv : EdgeValuesAt mem a h L P E values)
    (heq : ∀ e ∈ E, ∀ i < L, mem' (a + e * L + i) = mem (a + e * L + i)) :
    EdgeValuesAt mem' a h L P E values := by
  intro e he
  refine ⟨fun i hi => (heq e he i hi) ▸ (hv e he).1 i hi, ?_⟩
  unfold Num.fixVal
  rw [Num.intVal_congr (heq e he)]
  exact (hv e he).2

/-- Values outside the active edge set do not change the readout. -/
theorem EdgeValuesAt.of_eqOn {mem : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {values values' : ℕ → ℝ}
    (hv : EdgeValuesAt mem a h L P E values)
    (heq : ∀ e ∈ E, values e = values' e) : EdgeValuesAt mem a h L P E values' := by
  intro e he
  exact ⟨(hv e he).1, (hv e he).2.trans (heq e he)⟩

/-- The empty edge set needs no numeric cells. -/
theorem edgeValuesAt_empty (mem : ℕ → ℕ) (a h L P : ℕ) (values : ℕ → ℝ) :
    EdgeValuesAt mem a h L P ∅ values := by
  intro e he
  cases he

/-- Fresh zero cells give a table of zero fixed-point values. -/
theorem edgeValuesAt_zero {mem : ℕ → ℕ} {heap a h L P : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) (E : Finset ℕ) :
    EdgeValuesAt mem a h L P E (fun _ => 0) := by
  intro e _
  have he : heap ≤ a + e * L := ha.trans (Nat.le_add_right _ _)
  exact ⟨Num.zeroFrom_valid hz he, Num.fixVal_zeroFrom hz he⟩

/-- The root table determines membership within its vertex capacity. -/
theorem RootsAt.mem_iff {mem : ℕ → ℕ} {a vCap : ℕ} {R : Finset ℕ}
    (hr : RootsAt mem a vCap R) {v : ℕ} (hv : v < vCap) :
    v ∈ R ↔ mem (a + v) = 1 := by
  rcases hr.2 v hv with ⟨hmem, hbit⟩ | ⟨hmem, hbit⟩
  · exact ⟨fun _ => hbit, fun _ => hmem⟩
  · constructor
    · exact fun h => False.elim (hmem h)
    · intro h
      rw [hbit] at h
      cases h

/-- A collection exposes its branch count at the header. -/
theorem LSFCollectionAt.count {mem : ℕ → ℕ} {a vCap eCap h L P : ℕ}
    {E : Finset ℕ} {forests : ℕ × (ℕ → LSF)}
    (hf : LSFCollectionAt mem a vCap eCap h L P E forests) : mem a = forests.1 := hf.1

/-- Two scalar tables give the exact quotient table exposed by a forest.
The numerator and denominator stay in the shared fixed-point format. -/
theorem stretchValuesAt_of_tables {mem : ℕ → ℕ} {a h L P : ℕ} {E : Finset ℕ}
    {numerator denominator values : ℕ → ℝ}
    (hn : EdgeValuesAt mem (mem a) h L P E numerator)
    (hd : EdgeValuesAt mem (mem (a + 1)) h L P E denominator)
    (hp : ∀ e ∈ E, 0 < denominator e)
    (hq : ∀ e ∈ E, numerator e / denominator e = values e) :
    StretchValuesAt mem a h L P E values := by
  intro e he
  refine ⟨(hn e he).1, (hd e he).1, ?_, ?_⟩
  · rw [(hd e he).2]
    exact hp e he
  · rw [(hn e he).2, (hd e he).2]
    exact hq e he

/-- The stretch formula in Definition 5.3 (page 17) can be read exactly
from `length + pathLength` and `length` tables. No single fixed-point
block is required to store the result of the division. -/
theorem stretchValuesAt_of_path_lengths {mem : ℕ → ℕ} {a h L P : ℕ} {E : Finset ℕ}
    {length pathLength : ℕ → ℝ}
    (hn : EdgeValuesAt mem (mem a) h L P E (fun e => length e + pathLength e))
    (hd : EdgeValuesAt mem (mem (a + 1)) h L P E length)
    (hp : ∀ e ∈ E, 0 < length e) :
    StretchValuesAt mem a h L P E (fun e => 1 + pathLength e / length e) := by
  apply stretchValuesAt_of_tables hn hd hp
  intro e he
  have hne := ne_of_gt (hp e he)
  field_simp

end MinCostFlow.MinRatio
