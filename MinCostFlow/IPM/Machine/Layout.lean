module

public import MinCostFlow.IPM.MinRatioSpec
public import MinCostFlow.Num.Encoding
public import WordRAM.DataStructure
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.NormNum

/-!
# Memory layouts for the IPM data structure calls

Definition 4.5 (page 14) supplies graph updates, gradients, lengths,
and a normalization to Update, and receives scalar Query answers and
sets from Detect. Numbers use the fixed-point representation of page 7,
implemented by `Num`: `L` little-endian two's-complement limbs of `h`
bits, with precision `P`. Edge vectors are dense tables indexed by edge
name. Graph and batch encodings retain the shared named graph objects.

An update batch is a length-prefixed sequence of records. Insertion is
`[0,e,u,v]`, deletion is `[1,e]`, and splitting is
`[2,v,v',numberMoved,movedEdges...]`. Detect writes a length-prefixed
list of distinct edge names. The list need not be sorted.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A fixed-point scalar block, including limb validity. -/
def ScalarAt (mem : ℕ → ℕ) (a h L P : ℕ) (x : ℝ) : Prop :=
  Num.Valid mem a h L ∧ Num.fixVal mem a h L P = x

/-- Read a dense table, extending by zero outside its allocated names. -/
def readVector (mem : ℕ → ℕ) (a h L P m : ℕ) (e : ℕ) : ℝ :=
  if e < m then Num.fixVal mem (a+e*L) h L P else 0

/-- A table of valid scalar blocks on the names `0,...,m-1`. -/
def VectorAt (mem : ℕ → ℕ) (a h L P m : ℕ) (f : ℕ → ℝ) : Prop :=
  (∀ e < m, ScalarAt mem (a+e*L) h L P (f e)) ∧ ∀ e, m ≤ e → f e = 0

/-- Every coordinate of a represented scalar has the paper's fixed-point
form. This is a decoding fact, independent of an algorithm's correctness. -/
theorem ScalarAt.exists_dyadic {mem : ℕ → ℕ} {a h L P : ℕ} {x : ℝ}
    (hx : ScalarAt mem a h L P x) : ∃ z : ℤ, x = (z : ℝ)/(2 : ℝ)^P := by
  exact ⟨Num.intVal mem a h L, hx.2.symm⟩

/-- Valid input tables have exactly the canonical zero-extended decoding. -/
theorem VectorAt.read_eq {mem : ℕ → ℕ} {a h L P m : ℕ} {f : ℕ → ℝ}
    (hf : VectorAt mem a h L P m f) : readVector mem a h L P m = f := by
  funext e
  unfold readVector
  split_ifs with he
  · exact (hf.1 e he).2
  · exact (hf.2 e (Nat.le_of_not_gt he)).symm

/-- Every valid dense table represents its own decoding. -/
theorem vectorAt_readVector {mem : ℕ → ℕ} {a h L P m : ℕ}
    (hv : ∀ e < m, Num.Valid mem (a+e*L) h L) :
    VectorAt mem a h L P m (readVector mem a h L P m) := by
  constructor
  · intro e he
    exact ⟨hv e he, by simp only [readVector, he, ↓reduceIte]⟩
  · intro e he
    simp only [readVector, Nat.not_lt.mpr he, ↓reduceIte]

/-- The integer words in one shared graph update. -/
def updateWords : MinCostFlow.Update → List ℕ
  | .insert e u v => [0,e,u,v]
  | .delete e => [1,e]
  | .split v v' movedT movedH =>
      [2,v,v',movedT.card,movedH.card] ++ (movedT.sort (· ≤ ·)) ++ (movedH.sort (· ≤ ·))

/-- Batch count followed by the self-delimiting update records. -/
def batchWords (U : List MinCostFlow.Update) : List ℕ :=
  U.length :: U.flatMap updateWords

/-- The exact batch input, with no gradient or length values hidden in
integer update records. Those values live in the separate dense tables. -/
def BatchAt (mem : ℕ → ℕ) (a : ℕ) (U : List MinCostFlow.Update) : Prop :=
  ListAt mem a (batchWords U)

/-- Graph header `[numberVertices,numberEdges]`, the vertex names, then
triples `[edge,tail,head]`. Endpoint functions away from edges are unused. -/
def graphWords (G : MGraph) : List ℕ :=
  [G.V.card,G.E.card] ++ (G.V.sort (· ≤ ·)) ++
    (G.E.sort (· ≤ ·)).flatMap (fun e => [e,G.tail e,G.head e])

/-- The graph argument of initialization. -/
def GraphAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : Prop := ListAt mem a (graphWords G)

/-- Detect output is a count followed by distinct edge names in any order. -/
def DetectAt (mem : ℕ → ℕ) (a : ℕ) (S : Finset ℕ) : Prop :=
  ∃ es : List ℕ, es.Nodup ∧ es.toFinset = S ∧ SeqAt mem a es

/-- Detect's header is exactly the set size, regardless of output order. -/
theorem DetectAt.count {mem : ℕ → ℕ} {a : ℕ} {S : Finset ℕ}
    (hs : DetectAt mem a S) : mem a = S.card := by
  obtain ⟨es, hnd, rfl, hc, _⟩ := hs
  simpa only [List.toFinset_card_of_nodup hnd] using hc

/-- Every Detect output entry is a reported edge. -/
theorem DetectAt.mem {mem : ℕ → ℕ} {a : ℕ} {S : Finset ℕ}
    (hs : DetectAt mem a S) (i : ℕ) (hi : i < S.card) : mem (a+1+i) ∈ S := by
  obtain ⟨es, hnd, rfl, _, hat⟩ := hs
  have hlen : i < es.length := by simpa only [List.toFinset_card_of_nodup hnd] using hi
  rw [hat i hlen]
  exact List.mem_toFinset.mpr (List.getElem_mem hlen)

/-- An empty vector has a valid representation without allocating a cell. -/
theorem vectorAt_empty (mem : ℕ → ℕ) (a h L P : ℕ) :
    VectorAt mem a h L P 0 (fun _ => 0) := by
  exact ⟨fun _ he => False.elim (Nat.not_lt_zero _ he), fun _ _ => rfl⟩

end MinCostFlow.IPM.Machine
