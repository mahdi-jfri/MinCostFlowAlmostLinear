module

public import MinCostFlow.IPM.Machine.InitialRecordAssembly
public import MinCostFlow.IPM.Machine.InitialAuxiliaryOrder
public import MinCostFlow.IPM.Machine.InitialPositiveInput
import MinCostFlow.IPM.InitialDomain

/-!
# Identifying the assembled encoding with Lemma 4.12

The bounded solver uses five words per edge because lower capacities
and demands are zero. The same representation applies to its augmented
instance. This file identifies the exact assembled words with the
existing `initialInstance`, using the original retained-edge order and
`deficitIndex` for auxiliary edges. No second initialization construction
or new optimality premise is introduced.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine
open Scaling WordRAM

/-- The solver's existing five-word edge representation, on an `Edge`
whose lower capacity is zero and whose upper capacity is nonnegative. -/
def zeroLowerEdgeWords (e : Edge) : List ℕ :=
  [e.tail,e.head,e.upper.toNat,if e.cost < 0 then 1 else 0,e.cost.natAbs]

/-- The existing circulation layout, expressed on a zero-demand `Instance`.
The representation predicate below requires exactly the side conditions
that make its unsigned capacity words lossless. -/
def zeroLowerWords (I : Instance) : List ℕ :=
  [I.n,I.m] ++ I.edges.flatMap zeroLowerEdgeWords

/-- Lossless use of the circulation encoding for a general instance. -/
def ZeroLowerAt (mem : ℕ → ℕ) (a : ℕ) (I : Instance) : Prop :=
  (∀ e : Fin I.m, (I.edge e).lower = 0 ∧ 0 ≤ (I.edge e).upper) ∧
    (∀ v : Fin I.n, I.d v = 0) ∧ ListAt mem a (zeroLowerWords I)

/-- This is precisely the shared solver encoding on circulation input. -/
theorem zeroLowerWords_circulation (J : Circulation) : zeroLowerWords J.toInstance = J.solverWords := by
  simp only [zeroLowerWords,Circulation.toInstance_m,Circulation.toInstance,Circulation.solverWords]
  rw [← List.ofFn_id J.m]
  simp only [List.flatMap,List.map_ofFn,Function.comp_def]
  congr 2

private theorem initial_edges_list (I : Instance) (penalty : ℤ) :
    (initialInstance I penalty).edges = List.ofFn (freeEdgeArray I) ++
      List.ofFn (fun j => starEdge I.n (deficitIndex I j).val (twiceDeficit I (deficitIndex I j).val) penalty) :=
  List.ofFn_fin_append _ _

private theorem star_words (n : ℕ) (v : Fin n) (deficit : ℤ) (penalty : ℕ) :
    zeroLowerEdgeWords (starEdge n v deficit penalty) =
      [(starEdge n v deficit penalty).tail,(starEdge n v deficit penalty).head,
        (starEdge n v deficit penalty).upper.toNat,0,penalty] := by
  simp [zeroLowerEdgeWords,starEdge_cost]

/-- The number of emitted words is exactly five times the number of
auxiliary edges in the existing finite-set construction. -/
theorem initialAuxiliaryPrefix_length_deficit (J : Circulation) (penalty : ℕ) :
    (initialAuxiliaryPrefix (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n).length =
      5*(deficitVertices J.toInstance).card := by
  rw [initialAuxiliaryPrefix_eq_initial_stars]
  simp [List.length_flatten,List.map_ofFn,Function.comp_def,Nat.mul_comm]

/-- With the model's exact endpoint tables and positive input capacities,
the assembled machine graph is the prescribed `initialInstance`, word
for word, including every edge index and the two header counts. -/
theorem initialAssemblyWords_eq_initialInstance (J : Circulation)
    (hp : ∀ e, 1 ≤ J.capacity e) (penalty : ℕ) :
    initialAssemblyWords J (incomingCapacity J) (outgoingCapacity J) penalty =
      zeroLowerWords (initialInstance J.toInstance penalty) := by
  have hfree : (freeEdges J.toInstance).card = J.m := by
    rw [freeEdges_circulation J hp,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
  have haux := initialAuxiliaryPrefix_eq_initial_stars J penalty
  have hlen := initialAuxiliaryPrefix_length_deficit J penalty
  have hrows : J.toInstance.edges.flatMap zeroLowerEdgeWords = J.solverWords.drop 2 := by
    have hh := congrArg (List.drop 2) (zeroLowerWords_circulation J)
    simpa [zeroLowerWords] using hh

  rw [initialAssemblyWords,zeroLowerWords,initialInstance_n,initialInstance_m,hfree]
  simp only [hlen,Nat.mul_div_right _ (by decide : 0 < 5)]
  rw [initial_edges_list,freeEdgeArray_circulation J hp,List.flatMap_append,hrows]
  rw [haux]
  simp only [List.append_assoc]
  apply congrArg (fun extras : List ℕ =>
    [J.n+1,J.m+(deficitVertices J.toInstance).card] ++ (J.solverWords.drop 2 ++ extras))
  simp only [List.flatMap,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  exact (star_words _ _ _ _).symm

/-- All lower capacities and demands of this augmented instance are zero,
and its upper capacities are nonnegative. Hence its five-word encoding
satisfies the explicit losslessness conditions of `ZeroLowerAt`. -/
theorem initialInstance_zeroLower (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e) (penalty : ℤ) :
    (∀ e : Fin (initialInstance J.toInstance penalty).m,
      ((initialInstance J.toInstance penalty).edge e).lower = 0 ∧
        0 ≤ ((initialInstance J.toInstance penalty).edge e).upper) ∧
      (∀ v : Fin (initialInstance J.toInstance penalty).n,
        (initialInstance J.toInstance penalty).d v = 0) := by
  constructor
  · intro e
    have harr : ∀ j, (initialEdgeArray J.toInstance penalty j).lower = 0 ∧
        0 ≤ (initialEdgeArray J.toInstance penalty j).upper := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [initialEdgeArray,Fin.addCases_left,freeEdgeArray,Circulation.toInstance_edge,Circulation.inputEdge]
        exact ⟨trivial,Int.natCast_nonneg _⟩
      · simp only [initialEdgeArray,Fin.addCases_right,starEdge]
        split_ifs <;> exact ⟨rfl,abs_nonneg _⟩
    have he := instanceOfArrays_edge (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance) e
    have hj := harr (arrayIndex (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance) e)
    exact ⟨(congrArg Edge.lower he).trans hj.1,(congrArg Edge.upper he).symm ▸ hj.2⟩
  · intro v
    let u : Fin (J.n+1) := ⟨v.val,by simpa only [initialInstance_n] using v.isLt⟩
    exact (instanceOfArrays_d (initialEdgeArray J.toInstance penalty) (initialDemands J.toInstance) u).trans
      (initialDemands_circulation J hp u)

end MinCostFlow.IPM.Machine
