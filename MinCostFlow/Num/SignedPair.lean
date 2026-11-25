module

/-!
# Two-word signed integer encoding

Encodes an integer `z : Int` as the two-word sign-magnitude pair `[if z < 0 then 1 else 0, z.natAbs]`
used internally by the bounded-circulation solver, min-ratio data structure, and label propagation.
-/

@[expose] public section
namespace MinCostFlow

/-- An integer written as a two-word sign-magnitude pair: `1` if negative and `0` otherwise,
followed by its absolute value. -/
def encodeSignedPair (z : Int) : List Nat :=
  [if z < 0 then 1 else 0, z.natAbs]

/-- Each `encodeSignedPair` block has length `2`. -/
theorem flatMap_encodeSignedPair_length (zs : List Int) :
    (zs.flatMap encodeSignedPair).length = 2 * zs.length := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, encodeSignedPair,
      List.length_nil]
    omega

end MinCostFlow
