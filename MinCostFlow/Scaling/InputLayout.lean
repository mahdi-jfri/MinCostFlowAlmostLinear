module

public import MinCostFlow.Statement.Problem
public import WordRAM.Layout
import Mathlib.Tactic.NormNum
import WordRAM.Memory

/-!
# Reading the problem statement's input layout

The outer scaling program reads `Instance.encode` from the statement of
Theorem 1.1 (page 2). Its two header words precede eight words per edge and
two words per demand. This file identifies demand magnitude cells and bounds
the complete input length. No alternative problem encoding is introduced.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A signed input integer always occupies two words. -/
theorem encodeInt_length (z : ℤ) : (encodeInt z).length = 2 := rfl

/-- An input edge always occupies eight words. -/
theorem edge_encode_length (e : Edge) : e.encode.length = 8 := by
  simp only [Edge.encode, List.length_cons, List.length_append, encodeInt_length]

/-- Flattening all input edge records uses exactly eight words per edge. -/
theorem edges_encode_length (edges : List Edge) : (edges.flatMap Edge.encode).length = 8 * edges.length := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
    simp only [List.flatMap_cons, List.length_append, edge_encode_length, List.length_cons, ih]
    omega

/-- Flattening signed integers uses exactly two words per entry. -/
theorem integers_encode_length (zs : List ℤ) : (zs.flatMap encodeInt).length = 2 * zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.length_append, encodeInt_length, List.length_cons, ih]
    omega

/-- The complete input length, including its two-word header. -/
theorem instance_encode_length (I : Instance) (hv : I.IsValid) :
    I.encode.length = 2 + 8 * I.m + 2 * I.n := by
  simp only [Instance.encode, List.length_cons, List.length_append,
    edges_encode_length, integers_encode_length, hv.2]
  unfold Instance.m
  omega

/-- Header cells give the instance dimensions at any input base. -/
theorem instance_header_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) : mem a = I.n ∧ mem (a + 1) = I.m := by
  have hn := hat 0 (by simp only [Instance.encode, List.length_cons]; omega)
  have hm := hat 1 (by simp only [Instance.encode, List.length_cons]; omega)
  simpa only [Instance.encode, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using And.intro hn hm

/-- The odd cell in a signed integer record is its magnitude. -/
theorem integers_encode_magnitude (zs : List ℤ) (i : ℕ) (hi : i < zs.length) :
    (zs.flatMap encodeInt).getD (2 * i + 1) 0 = (zs.getD i 0).natAbs := by
  induction zs generalizing i with
  | nil => cases hi
  | cons z zs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < zs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hh := ih i hi'
      simpa only [List.flatMap_cons, encodeInt, List.cons_append, List.nil_append,
        Nat.mul_succ, Nat.add_assoc, List.getD_cons_succ] using hh

/-- Read the magnitude of demand `v` in the statement's input format. -/
theorem instance_encode_demand_magnitude (I : Instance) (hv : I.IsValid) (v : Fin I.n) :
    I.encode.getD (2 + 8 * I.m + 2 * v.val + 1) 0 = (I.d v).natAbs := by
  have hi : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
  have hh := integers_encode_magnitude I.demand v.val hi
  unfold Instance.encode
  rw [show 2 + 8 * I.m + 2 * v.val + 1 = (8 * I.m + 2 * v.val + 1) + 1 + 1 by omega]
  simp only [List.getD_cons_succ]
  rw [List.getD_append_right _ _ _ _ (by rw [edges_encode_length]; change 8 * I.m ≤ _; omega)]
  rw [edges_encode_length]
  change (I.demand.flatMap encodeInt).getD (8 * I.m + 2 * v.val + 1 - 8 * I.m) 0 = _
  rw [show 8 * I.m + 2 * v.val + 1 - 8 * I.m = 2 * v.val + 1 by omega]
  exact hh

/-- The same demand magnitude at an arbitrary base address in memory. -/
theorem demand_magnitude_at (I : Instance) (hv : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) (v : Fin I.n) :
    mem (a + (2 + 8 * I.m + 2 * v.val + 1)) = (I.d v).natAbs := by
  have hi : 2 + 8 * I.m + 2 * v.val + 1 < I.encode.length := by
    rw [instance_encode_length I hv]
    have hh := v.isLt
    omega
  have hget := instance_encode_demand_magnitude I hv v
  rw [List.getD_eq_getElem _ _ hi] at hget
  exact (hat _ hi).trans hget

/-- The contiguous edge block follows the two input header cells. -/
theorem instance_edges_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) :
    ListAt mem (a + 2) (I.edges.flatMap Edge.encode) := by
  have hrest := (listAt_cons.mp (listAt_cons.mp hat).2).2
  have hedge := (listAt_append.mp hrest).1
  simpa only [Nat.add_assoc] using hedge

/-- Every word of an input edge block is a word of the whole instance. -/
theorem instance_edges_word_mem (I : Instance) {x : ℕ}
    (hx : x ∈ I.edges.flatMap Edge.encode) : x ∈ I.encode :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx))

/-- The contiguous demand block follows all eight-word edge records. -/
theorem instance_demands_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) :
    ListAt mem (a + 2 + 8 * I.m) (I.demand.flatMap encodeInt) := by
  have hrest := (listAt_cons.mp (listAt_cons.mp hat).2).2
  have hdemands := (listAt_append.mp hrest).2
  have he : a + 2 + 8 * I.m = a + 1 + 1 + (I.edges.flatMap Edge.encode).length := by
    rw [edges_encode_length]
    change a + 2 + 8 * I.m = a + 1 + 1 + 8 * I.m
    omega
  rw [he]
  exact hdemands

end MinCostFlow.Scaling.Machine
