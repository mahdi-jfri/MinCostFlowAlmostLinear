module

public import MinCostFlow.IPM.Machine.ConnectedPairScan
public import MinCostFlow.IPM.Machine.InitialEncodedInstance
public import MinCostFlow.IPM.ConnectedInitialConstruction
import MinCostFlow.IPM.InitialDomain

/-!
# The zero-deficit scan agrees with the connected augmentation

The two scans write the same edge records as the two blocks appended
to the original Lemma 4.12 graph. Both use increasing vertex order.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- Only entries of the two deficit tables visited by a scan affect its output. -/
theorem connectedPairPrefix_congr (reverse : Bool) (inc out inc' out' : ℕ → ℕ)
    (n penalty k : ℕ) (hi : ∀ i < k, inc i = inc' i) (ho : ∀ i < k, out i = out' i) :
    connectedPairPrefix reverse inc out n penalty k =
      connectedPairPrefix reverse inc' out' n penalty k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [connectedPairPrefix, connectedPairPrefix,
      ih (fun i hh => hi i (hh.trans (Nat.lt_succ_self k)))
        (fun i hh => ho i (hh.trans (Nat.lt_succ_self k))),
      hi k (Nat.lt_succ_self k), ho k (Nat.lt_succ_self k)]

private theorem pair_prefix_flatMap (reverse : Bool) (inc out : ℕ → ℕ)
    (n penalty k : ℕ) :
    connectedPairPrefix reverse inc out n penalty k =
      (List.range k).flatMap (fun v => connectedPairRecordWords
        (if reverse then n else v) (if reverse then v else n) (inc v) (out v) penalty) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [connectedPairPrefix, List.range_succ, List.flatMap_append, ih]
    simp

/-- Each direction's emitted records agree with the corresponding
array of capacity-two hub edges. -/
theorem connectedPairPrefix_eq_words (J : Circulation) (penalty : ℕ) (reverse : Bool) :
    connectedPairPrefix reverse (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n =
      (List.ofFn (fun j : Fin (zeroDeficitVertices J.toInstance).card =>
        zeroLowerEdgeWords (starEdge J.n (zeroDeficitIndex J.toInstance j).1
          (if reverse then -2 else 2) penalty))).flatten := by
  let p := fun v : Fin J.n => incomingCapacity J v = outgoingCapacity J v
  let f := fun v : Fin J.n => connectedPairRecordWords
    (if reverse then J.n else v) (if reverse then (v : ℕ) else J.n)
    (incomingCapacity J v) (outgoingCapacity J v) penalty
  have hrange : List.range J.n = (List.finRange J.n).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [pair_prefix_flatMap, hrange, List.flatMap_map]
  change (List.finRange J.n).flatMap f = _
  have hs := ordered_vertex_records p f (fun v hv => by simpa [f, p, connectedPairRecordWords] using
    (show ¬ incomingCapacity J v = outgoingCapacity J v from hv))
  have hset : Finset.univ.filter p = zeroDeficitVertices J.toInstance := by
    ext v
    simp [p, zeroDeficitVertices, twiceDeficit_eq_capacity_difference, sub_eq_zero]
  dsimp only at hs
  rw [hset] at hs
  refine hs.trans ?_
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  let v := (zeroDeficitIndex J.toInstance j).1
  have hz : twiceDeficit J.toInstance v = 0 :=
    (Finset.mem_filter.mp (zeroDeficitIndex J.toInstance j).2).2
  have he : incomingCapacity J v = outgoingCapacity J v := by
    rw [twiceDeficit_eq_capacity_difference, sub_eq_zero] at hz
    exact_mod_cast hz
  change f v = zeroLowerEdgeWords (starEdge J.n v (if reverse then -2 else 2) penalty)
  cases reverse <;> simp [f, he, connectedPairRecordWords, zeroLowerEdgeWords, starEdge]

/-- Each zero deficit contributes exactly five words in each direction. -/
theorem connectedPairPrefix_length_eq (J : Circulation) (penalty : ℕ) (reverse : Bool) :
    (connectedPairPrefix reverse (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n).length =
      5*(zeroDeficitVertices J.toInstance).card := by
  rw [connectedPairPrefix_eq_words]
  simp [List.length_flatten, List.map_ofFn, Function.comp_def, zeroLowerEdgeWords, Nat.mul_comm]

/-- The connected graph encoding changes the old edge count and appends
the two zero-deficit record blocks. -/
theorem zeroLowerWords_connected (J : Circulation) (penalty : ℕ) :
    let I := J.toInstance
    let old := initialInstance I penalty
    let aug := connectedInitialInstance I penalty
    zeroLowerWords aug = [J.n+1, aug.m] ++ (zeroLowerWords old).drop 2 ++
      connectedPairPrefix false (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n ++
      connectedPairPrefix true (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n := by
  dsimp only
  rw [connectedPairPrefix_eq_words, connectedPairPrefix_eq_words]
  have he : (connectedInitialInstance J.toInstance penalty).edges =
      (initialInstance J.toInstance penalty).edges ++
        (List.ofFn (fun j => starEdge J.n (zeroDeficitIndex J.toInstance j).1 2 penalty) ++
         List.ofFn (fun j => starEdge J.n (zeroDeficitIndex J.toInstance j).1 (-2) penalty)) := by
    let left := fun j => starEdge J.n (zeroDeficitIndex J.toInstance j).1 2 penalty
    let right := fun j => starEdge J.n (zeroDeficitIndex J.toInstance j).1 (-2) penalty
    calc
      _ = (initialInstance J.toInstance penalty).edges ++ List.ofFn (Fin.append left right) :=
        List.ofFn_fin_append (initialEdgeArray J.toInstance penalty) (Fin.append left right)
      _ = _ := by rw [List.ofFn_fin_append]
  unfold zeroLowerWords
  rw [he]
  simp only [List.flatMap_append]
  simp only [List.flatMap, List.map_ofFn, Function.comp_def, List.append_assoc,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The connected solver graph retains unsigned capacities and zero demands. -/
theorem connectedInitialInstance_zeroLower (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e)
    (penalty : ℤ) :
    (∀ e : Fin (connectedInitialInstance J.toInstance penalty).m,
      ((connectedInitialInstance J.toInstance penalty).edge e).lower = 0 ∧
        0 ≤ ((connectedInitialInstance J.toInstance penalty).edge e).upper) ∧
      (∀ v : Fin (connectedInitialInstance J.toInstance penalty).n,
        (connectedInitialInstance J.toInstance penalty).d v = 0) := by
  constructor
  · intro e
    rw [show (connectedInitialInstance J.toInstance penalty).edge e = _ from
      instanceOfArrays_edge _ _ e]
    generalize arrayIndex (connectedInitialEdgeArray J.toInstance penalty)
      (initialDemands J.toInstance) e = j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [connectedInitialEdgeArray, Fin.addCases_left]
      let k : Fin (initialInstance J.toInstance penalty).m :=
        (arrayIndex (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance)).symm i
      have hk := (initialInstance_zeroLower J hp penalty).1 k
      rw [show (initialInstance J.toInstance penalty).edge k = _ from
        instanceOfArrays_edge _ _ k, Equiv.apply_symm_apply] at hk
      exact hk
    · simp only [connectedInitialEdgeArray, Fin.addCases_right]
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right, starEdge_lower, starEdge_upper,
          abs_nonneg, true_and]
  · intro v
    rw [show (connectedInitialInstance J.toInstance penalty).d v = _ from
      instanceOfArrays_d _ _ v]
    exact initialDemands_circulation J hp v

/-- Every positive-capacity solver edge remains at its original index. In
particular the connected augmentation has at least as many edges. -/
theorem connectedInitial_circulation_m_ge (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e)
    (penalty : ℤ) : J.m ≤ (connectedInitialInstance J.toInstance penalty).m := by
  rw [connectedInitialInstance, instanceOfArrays_m, freeEdges_circulation J hp,
    Finset.card_univ, Fintype.card_fin, Circulation.toInstance_m]
  omega

end MinCostFlow.IPM.Machine
