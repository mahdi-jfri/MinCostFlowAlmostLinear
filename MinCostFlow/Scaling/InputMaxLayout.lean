module

public import MinCostFlow.Scaling.InputLayout
import WordRAM.Memory

/-!
# Field maxima in the original input

The entry scan reads the three magnitude fields in each eight-word edge
record and the demand magnitudes. These lemmas identify the selected
words and show that their maxima are exactly the statement's bounds.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A fixed field of each edge record is selected by a stride-eight scan. -/
theorem edge_field_at (es : List Edge) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (es.flatMap Edge.encode)) (j : Fin 8) (i : Fin es.length) :
    mem (a+8*i.val+j.val)=(es[i.val].encode)[j.val]'(by rw [edge_encode_length]; exact j.isLt) := by
  induction es generalizing a with
  | nil => exact Fin.elim0 i
  | cons e es ih =>
    obtain ⟨hh,ht⟩ := listAt_append.mp hat
    change ListAt mem a e.encode at hh
    change ListAt mem (a+8) (es.flatMap Edge.encode) at ht
    cases i using Fin.cases with
    | zero => simpa using hh j.val (by rw [edge_encode_length]; exact j.isLt)
    | succ i =>
      have h := ih (a+8) ht i
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Lower-capacity magnitudes occupy field three of each edge. -/
theorem lower_field_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) (i : Fin I.edges.length) :
    mem (a+5+8*i.val)=(I.edges.map (fun e => e.lower.natAbs))[i.val] := by
  have h := edge_field_at I.edges mem (a+2) (instance_edges_at I mem a hat) ⟨3,by decide⟩ i
  have he : a+2+8*i.val+3=a+5+8*i.val := by omega
  change mem (a+2+8*i.val+3)=_ at h
  rw [he] at h
  simpa [Edge.encode,encodeInt] using h

/-- Upper-capacity magnitudes occupy field five of each edge. -/
theorem upper_field_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) (i : Fin I.edges.length) :
    mem (a+7+8*i.val)=(I.edges.map (fun e => e.upper.natAbs))[i.val] := by
  have h := edge_field_at I.edges mem (a+2) (instance_edges_at I mem a hat) ⟨5,by decide⟩ i
  have he : a+2+8*i.val+5=a+7+8*i.val := by omega
  change mem (a+2+8*i.val+5)=_ at h
  rw [he] at h
  simpa [Edge.encode,encodeInt] using h

/-- Cost magnitudes occupy field seven of each edge. -/
theorem cost_field_at (I : Instance) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a I.encode) (i : Fin I.edges.length) :
    mem (a+9+8*i.val)=(I.edges.map (fun e => e.cost.natAbs))[i.val] := by
  have h := edge_field_at I.edges mem (a+2) (instance_edges_at I mem a hat) ⟨7,by decide⟩ i
  have he : a+2+8*i.val+7=a+9+8*i.val := by omega
  change mem (a+2+8*i.val+7)=_ at h
  rw [he] at h
  simpa [Edge.encode,encodeInt] using h

private theorem fold_max_append (xs ys : List ℕ) :
    (xs++ys).foldr max 0=max (xs.foldr max 0) (ys.foldr max 0) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append,List.foldr_cons,ih,max_assoc]

private theorem fold_max_pair (es : List Edge) :
    (es.map (fun e => max e.lower.natAbs e.upper.natAbs)).foldr max 0=
      max ((es.map (fun e => e.lower.natAbs)).foldr max 0)
        ((es.map (fun e => e.upper.natAbs)).foldr max 0) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons,List.foldr_cons,ih]; omega

/-- Three scanned maxima combine to the exact capacity bound, which also
includes demands. -/
theorem maxCapacity_eq_field_maxima (I : Instance) :
    I.maxCapacity=max (max ((I.edges.map (fun e => e.lower.natAbs)).foldr max 0)
      ((I.edges.map (fun e => e.upper.natAbs)).foldr max 0))
      ((I.demand.map Int.natAbs).foldr max 0) := by
  unfold Instance.maxCapacity
  rw [fold_max_append,fold_max_pair]

end MinCostFlow.Scaling.Machine
