module

public import MinCostFlow.HierPaths.IndexArrays
public import MinCostFlow.HierPaths.DeleteState

/-!
# The static arrays of the hierarchy

This file assembles the arrays of `HierPaths/Index*.lean` into the `StaticArrays` that `Delete`
reads (`HierPaths/DeleteState.lean`), and proves its specification `StaticArrays.Spec`
(`staticArrays_spec`).

The pairs of children are numbered by depth, first child and the position of the second child
among its siblings: the connector with depth `t`, children `c < c'` gets the pair number
`(t · 2^x + c) · 2^b + (c' mod 2^b)`, below `leafDepth · 2^x · 2^b`. The connector array of a pair
lists the connectors with that pair number, so it is exactly the set of connectors of the pair.
The reverse lists have at most `ξ` entries (`length_revIdx_le`), and the connector lists
of the terminals at most `leafDepth · (2^b − 1)` (`length_termConns_le`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The pair number of a stored connector. -/
def pairNum (x b : ℕ) (r : ConnRec) : ℕ := (r.depth * 2 ^ x + r.child) * 2 ^ b + r.child' % 2 ^ b

/-- The number of pair numbers. -/
def numPairsOf (x b : ℕ) : ℕ := leafDepth x b * 2 ^ x * 2 ^ b

/-- The static arrays of the hierarchy `H`, for the owners and labels of the root host. -/
def staticArrays (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) :
    StaticArrays where
  C := connSystem H x b owner label
  x := x
  b := b
  revList := revIdx H x b owner label
  termConns := termConns H x b
  numPairs := numPairsOf x b
  pairConns p := (List.range (connRecs H x b).length).filter fun k =>
    pairNum x b ((connRecs H x b).getD k default) = p
  pairOf k := pairNum x b ((connRecs H x b).getD k default)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

theorem numGroups_le_pow (j : ℕ) : numGroups x b j ≤ 2 ^ x := by
  rw [← numGroups_mul_groupSize (j := j) (b := b)]
  exact Nat.le_mul_of_pos_right _ groupSize_pos

theorem pairNum_lt {r : ConnRec} (hr : r ∈ connRecs H x b) : pairNum x b r < numPairsOf x b := by
  obtain ⟨t, ht, g, hg, c, hc, c', _, _, q, _, rfl⟩ := mem_connRecs.mp hr
  have hc1 : c < 2 ^ x := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow _)
  have hmod : c' % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  unfold pairNum numPairsOf
  simp only
  have h1 : t * 2 ^ x + c < leafDepth x b * 2 ^ x := by
    have : (t + 1) * 2 ^ x ≤ leafDepth x b * 2 ^ x := Nat.mul_le_mul_right _ ht
    rw [Nat.succ_mul] at this
    omega
  have h2 : (t * 2 ^ x + c + 1) * 2 ^ b ≤ leafDepth x b * 2 ^ x * 2 ^ b :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.succ_mul] at h2
  omega

/-- **The specification of the static arrays.** For a valid hierarchy whose root host projects onto
`G`, with owners in `G`, the arrays meet `StaticArrays.Spec` with the bound `ξ` on the reverse
lists and `leafDepth · (2^b − 1)` on the connector lists of the terminals. -/
theorem staticArrays_spec (hb : 0 < b) (hH : H.IsValid x b) {G : Graph} {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hproj : IsProjection G (H.host 0 0).edges owner label)
    (hown : ∀ p < 2 ^ x, owner p < G.n) {ξ : ℕ}
    (hξ : ∀ e, (revIdx H x b owner label e).length ≤ ξ) :
    (staticArrays H x b owner label).Spec G ξ (leafDepth x b * (2 ^ b - 1)) := by
  refine ⟨rfl, hb, connSystem_fitsGraph hb hH hproj hown, ?_, ?_, hξ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e t ht
    simp only [staticArrays, revIdx, List.mem_flatMap, List.mem_replicate] at ht
    obtain ⟨r, hr, _, rfl⟩ := ht
    exact (connRec_spec hb hH hr).2.2.2.1
  · intro c hc e he
    exact mem_revIdx hc he
  · intro t _ c
    exact mem_termConns
  · intro t
    exact List.nodup_range.filter _
  · intro t
    exact length_termConns_le hb hH t
  · intro p
    exact List.nodup_range.filter _
  · intro p c hc
    simp only [staticArrays, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
    exact hc
  · intro c hc
    exact pairNum_lt (getD_mem_connRecs hc)

/-- The specification with the numbers of `HierPaths/Params.lean`: reverse lists of length at most
`ξ = xiOf a d m`. -/
theorem staticArrays_spec_xiOf (hb : 0 < b) (hH : H.IsValid x b) {a dd m : ℕ}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a m)) (lvlBound (hOf dd) (uOf a m))
      (lvlBound (hOf dd) (uOf a m)))
    (hh : leafDepth x b ≤ depthOf m) (hBb : 2 ^ b ≤ branchOf m) {G : Graph} {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hproj : IsProjection G (H.host 0 0).edges owner label)
    (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j')
    (hown : ∀ p < 2 ^ x, owner p < G.n) :
    (staticArrays H x b owner label).Spec G (xiOf a dd m) (leafDepth x b * (2 ^ b - 1)) :=
  staticArrays_spec hb hH hproj hown (length_revIdx_le hb hH hB hh hBb hinj)

end MinCostFlow.HierPaths
