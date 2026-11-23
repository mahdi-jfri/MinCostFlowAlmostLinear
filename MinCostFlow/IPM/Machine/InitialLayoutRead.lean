module

public import MinCostFlow.IPM.Machine.InitialEncodedInstance
import MinCostFlow.Scaling.SolverInputLayout

/-!
# Reading the augmented graph through the shared solver layout

Lemma 4.12's augmented graph has zero demands, zero lower capacities,
and nonnegative upper capacities on bounded circulation input. Its
five-word encoding has been identified with the shared solver layout.
This file transports that layout's existing header and capacity lookup
lemmas to `Instance`, preserving the natural edge index exactly.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Scaling WordRAM

/-- Use the existing typed circulation representation to read a zero-lower
instance. `ZeroLowerAt` separately supplies the losslessness conditions.
The edge index is unchanged and both endpoint proofs come from validity. -/
def zeroLowerCirculation (I : Instance) (hI : I.IsValid) : Circulation where
  n := I.n
  m := I.m
  tail e := ⟨(I.edge e).tail,(hI.1 _ (List.getElem_mem e.isLt)).1⟩
  head e := ⟨(I.edge e).head,(hI.1 _ (List.getElem_mem e.isLt)).2⟩
  capacity e := (I.edge e).upper.toNat
  cost e := (I.edge e).cost

/-- The transport uses exactly the shared solver record format. -/
theorem zeroLowerCirculation_words (I : Instance) (hI : I.IsValid) :
    (zeroLowerCirculation I hI).solverWords = zeroLowerWords I := by
  have he : List.ofFn (fun e : Fin I.m => I.edge e) = I.edges := by
    apply List.ext_getElem
    · simp [Instance.m]
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  unfold Circulation.solverWords zeroLowerWords
  change [I.n,I.m] ++ (List.finRange I.m).flatMap (zeroLowerCirculation I hI).solverEdgeWords =
    [I.n,I.m] ++ I.edges.flatMap zeroLowerEdgeWords
  rw [← he,← List.ofFn_id I.m]
  simp only [zeroLowerCirculation,Circulation.solverEdgeWords,zeroLowerEdgeWords,
    List.flatMap,List.map_ofFn,Function.comp_def]
  rfl

/-- The exact encoded length is two header words and five per edge. -/
theorem zeroLowerWords_length (I : Instance) (hI : I.IsValid) :
    (zeroLowerWords I).length = 2+5*I.m := by
  rw [← zeroLowerCirculation_words I hI]
  exact (zeroLowerCirculation I hI).solverWords_length

/-- Header decoding for the prescribed augmented input representation. -/
theorem zeroLower_header_at (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zeroLowerWords I)) : mem a = I.n ∧ mem (a+1) = I.m := by
  rw [← zeroLowerCirculation_words I hI] at hat
  have hh := (Scaling.Machine.solverWords_at_iff (zeroLowerCirculation I hI) mem a).mp hat
  exact ⟨hh.1,hh.2.1⟩

/-- Capacity lookup reuses the proved five-word solver lookup. -/
theorem zeroLower_capacity_at (I : Instance) (hI : I.IsValid) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a (zeroLowerWords I)) (e : Fin I.m) :
    mem (a+4+5*e.val) = (I.edge e).upper.toNat := by
  rw [← zeroLowerCirculation_words I hI] at hat
  exact solver_capacity_at (zeroLowerCirculation I hI) mem a hat e

end MinCostFlow.IPM.Machine
