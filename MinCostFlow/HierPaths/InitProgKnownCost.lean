module

public import MinCostFlow.HierPaths.InitAssemble

/-!
# Cost of the completed section writers

The cost of the header depends on the input edge count. The owner and counter writers
take time proportional to their table sizes. The remaining completed sections start
zero and need only fixed work to return their end addresses.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited

private theorem initBlock_length_lower (S : StaticData) (a : ℕ) (G : Graph)
    (phiNum phiDen M : ℕ) :
    1 + G.m + 2 ^ S.x + leafDepth S.x S.b ≤ (initBlock S a G phiNum phiDen M).length := by
  let X := initConcrete S a (initAbs phiNum phiDen M G)
  have hm : X.m = G.m := rfl
  have hterm : X.H.A.C.numTerm = 2 ^ S.x := rfl
  have hd : X.depth = leafDepth S.x S.b := rfl
  change _ ≤ X.encode.length
  rw [length_encode_eq]
  omega

/-- The prefix and suffix writers of the block cost at most a constant per block word.
Only the cost of sections 2 through 12 remains on the right. -/
theorem hierInitBuilder_cost_le (S : StaticData) (a : ℕ) (ha : 1 ≤ a)
    (G : Graph) (gAddr phiNum phiDen M h h₁ : ℕ) (Wm : List (SecW a)) :
    ((initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) Wm).map fun W =>
        W.cost S G [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum + 30 ≤
      4000 * (initBlock S a G phiNum phiDen M).length +
        (Wm.map fun W => W.cost S G [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum := by
  have hc := initBoundWordCost_le_affine G
  have hb := initBlock_length_lower S a G phiNum phiDen M
  simp only [initWriters, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, headerW, valsW, graphW, numTermW, numConnW, numPairsW, staticW,
    depthW, initBoundW, kappaW, argW, zeroW, ownerW, zeroPowW, zeroValW, zeroGraphW, countersW,
    pairCurW, stackW]
  change _ ≤ _
  omega

end MinCostFlow.HierPaths
