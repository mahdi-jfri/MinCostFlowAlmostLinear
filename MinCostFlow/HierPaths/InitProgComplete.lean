module

public import MinCostFlow.HierPaths.InitProgReverseSec
public import MinCostFlow.HierPaths.InitProgSupportSec
public import MinCostFlow.HierPaths.InitProgKnownCost
public import MinCostFlow.HierPaths.InitProgTermWriter
public import MinCostFlow.HierPaths.InitProgPairBuckets
public import MinCostFlow.HierPaths.InitProgPairTable
import MinCostFlow.HierPaths.InitProgProjectedCost

/-!
# The initialized hierarchy block

The section writers run in layout order. Each uses the static output
below the heap pointer and returns its scratch cells to zero.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

def initMiddleWriters (a : ℕ) : List (SecW a) :=
  endpointWriters a ++
    [connectorPairW a, reverseBucketW a, termBucketW a, pairBucketW a, supportBucketW a,
      projectedW a true, projectedW a false, pairTableW a]

/-- The middle writers materialize sections 2 through 12 in the required order. -/
theorem initMiddleWriters_sections (S : StaticData) (G : Graph) (a pn pd M : ℕ)
    (base : List ℕ) (hgood : S.Good a (dOf pn pd) M G) :
    (initMiddleWriters a).map (fun W => W.l S G base) =
      ((initConcrete S a (initAbs pn pd M G)).sections.drop 2).take 11 := by
  let s := initAbs pn pd M G
  let A := (initConcrete S a s).sections
  obtain ⟨h2, h3, h4⟩ := initEndpointWords_sections S a s
  change [initEndpointWords S 0, initEndpointWords S 1, initEndpointWords S 0,
    (connectorPairW a).l S G base, initReverseSection S G, initTermSection S, initPairSection S,
    initSupportSection S G, initProjectedSection S true, initProjectedSection S false,
    initPairTable S] =
    [A.getD 2 [], A.getD 3 [], A.getD 4 [], A.getD 5 [], A.getD 6 [], A.getD 7 [],
      A.getD 8 [], A.getD 9 [], A.getD 10 [], A.getD 11 [], A.getD 12 []]
  rw [← h2, ← h3, connectorPairW_section S a G s base, ← initReverseSection_eq S G a pn pd M,
    ← initTermSection_eq S a s hgood.b_pos hgood.valid, ← initPairSection_eq S a s,
    ← show A.getD 9 [] = initSupportSection S G from initSupportSection_eq S G a pn pd M, ← initProjectedSection_eq S a s true,
    ← initProjectedSection_eq S a s false, ← initPairTable_section S a s]
  have he : A.getD 2 [] = A.getD 4 [] := h2.trans h4.symm
  exact congrArg (fun z => [A.getD 2 [], A.getD 3 [], z, A.getD 5 [], A.getD 6 [],
    A.getD 7 [], A.getD 8 [], A.getD 9 [], A.getD 10 [], A.getD 11 [], A.getD 12 []]) he

/-- Every section length is bounded by the initialized block length. -/
theorem initBlock_section_le (S : StaticData) (G : Graph) (a pn pd M i : ℕ) :
    ((initConcrete S a (initAbs pn pd M G)).sections.getD i []).length ≤
      (initBlock S a G pn pd M).length := by
  let A := initConcrete S a (initAbs pn pd M G)
  change (A.sections.getD i []).length ≤ A.encode.length
  by_cases hi : i < A.sections.length
  · rw [List.getD_eq_getElem _ _ hi, length_encode]
    have hl := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) (List.getElem_mem hi))
    omega
  · have ho : A.sections[i]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, ho]
    simp

end MinCostFlow.HierPaths

end
