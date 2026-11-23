module

public import MinCostFlow.HierPaths.InitProgComplete
public import MinCostFlow.HierPaths.ImplParts
import MinCostFlow.HierPaths.InitProgTermWriter
import MinCostFlow.HierPaths.InitProgPairBuckets
import MinCostFlow.HierPaths.InitProgPairTable
import MinCostFlow.HierPaths.InitProgProjectedCost

/-!
# Cost and space of building the initialized block

The traversals charge flattening and projection to the model work.
The counting sorts, column scans, and cleanup charge a fixed amount
per initialized word. The same counts bound all temporary space.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

private theorem initBuilder_counts (S : StaticData) (G : Graph) (a pn pd M : ℕ)
    (hg : S.Good a (dOf pn pd) M G) :
    let B := (initBlock S a G pn pd M).length
    G.m ≤ B ∧ G.n ≤ B ∧ S.numTerm ≤ B ∧ S.numConn ≤ B ∧ numPairsOf S.x S.b ≤ B ∧
    (initReverseRecords S).length ≤ B ∧ (initSupportRecords S).length ≤ B ∧
    (initProjectedSection S true).length ≤ B ∧ (initProjectedSection S false).length ≤ B ∧
    (initPairTable S).length ≤ B ∧ 1 ≤ B := by
  let X := initConcrete S a (initAbs pn pd M G)
  let B := (initBlock S a G pn pd M).length
  have hm : X.m = G.m := rfl
  have hn : X.n = G.n := rfl
  have hP : X.H.A.C.numTerm = S.numTerm := rfl
  have hN : X.H.A.C.numConn = S.numConn := rfl
  have hQ : X.H.A.numPairs = numPairsOf S.x S.b := rfl
  have he : B = X.encode.length := rfl
  have hLow := length_encode_eq X
  rw [hm, hn, hP, hN, hQ, ← he] at hLow
  have hRev := initBlock_section_le S G a pn pd M 6
  rw [initReverseSection_eq, initReverseSection_length hg] at hRev
  have hSupp := initBlock_section_le S G a pn pd M 9
  rw [initSupportSection_eq, csrList, List.length_append, length_csrOffsets,
    initBucket_data_length _ _ (fun _ hi => initSupportRecords_key_lt hg hi)] at hSupp
  have hV := initBlock_section_le S G a pn pd M 10
  change (X.sections.getD (if true then 10 else 11) []).length ≤ B at hV
  rw [initProjectedSection_eq] at hV
  have hE := initBlock_section_le S G a pn pd M 11
  change (X.sections.getD (if false then 10 else 11) []).length ≤ B at hE
  rw [initProjectedSection_eq] at hE
  have hTable := initBlock_section_le S G a pn pd M 12
  rw [initPairTable_section] at hTable
  change _ ≤ B at hRev hSupp hTable
  dsimp only
  change G.m ≤ B ∧ G.n ≤ B ∧ S.numTerm ≤ B ∧ S.numConn ≤ B ∧
    numPairsOf S.x S.b ≤ B ∧ (initReverseRecords S).length ≤ B ∧
    (initSupportRecords S).length ≤ B ∧ (initProjectedSection S true).length ≤ B ∧
    (initProjectedSection S false).length ≤ B ∧ (initPairTable S).length ≤ B ∧ 1 ≤ B
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, hV, hE, hTable, by omega⟩

private theorem initBuilder_work_bound (S : StaticData) (G : Graph) (a : ℕ) (ha : 1 ≤ a)
    (ga pn pd M h h₁ : ℕ) (hg : S.Good a (dOf pn pd) M G) :
    ((initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) (initMiddleWriters a)).map
      fun W => W.cost S G [ga, pn, pd, M, h, h₁] + 40).sum + 30 ≤
        40000 * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
          (initBlock S a G pn pd M).length) := by
  refine (hierInitBuilder_cost_le S a ha G ga pn pd M h h₁ _).trans ?_
  obtain ⟨hm, hn, hP, hN, hQ, hR, hS, hV, hE, hT, h1⟩ := initBuilder_counts S G a pn pd M hg
  have hEnd := initEndpointSectionCost_le S hg.b_pos hg.valid
  have hPV := initProjectedWriterCost_le S G true hg.b_pos hg.valid
  have hPE := initProjectedWriterCost_le S G false hg.b_pos hg.valid
  have hTable := initPairTableCost_le S
  simp only [initMiddleWriters, endpointWriters, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, endpointW, connectorPairW, reverseBucketW,
    termBucketW, pairBucketW, supportBucketW, projectedW, pairTableW, initReverseWriterCost,
    initTermWriterCost, initPairBucketCost, initSupportWriterCost, initRestSteps]
  omega

/-- A single polynomial bound pays for the initialized block and all section scratch. -/
noncomputable def hierBuilderSpace (a : ℕ) (pn pd _n m M : ℕ) : ℕ :=
  300000 * m * gammaHP a (dOf pn pd) M

theorem hierBuilderSpace_form (a : ℕ) : SpaceForm a (hierBuilderSpace a) 300000 2 := by
  intro pn pd n m M h1 h2
  unfold hierBuilderSpace
  rw [dOf, nat_ceil_div_eq h1 h2]
  set Γ := gammaHP a ((pd + pn - 1) / pn) M
  set B := pd + n + m + M + Γ + 2
  calc
    300000 * m * Γ = 300000 * (m * Γ) := Nat.mul_assoc ..
    _ ≤ 300000 * (B * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    _ = 300000 * B ^ 2 := by rw [pow_two]

private theorem initBuilder_space_bound (S : StaticData) (G : Graph) (a : ℕ) (ha : 1 ≤ a)
    (ga pn pd M h h₁ : ℕ) (hg : S.Good a (dOf pn pd) M G) :
    (initBlock S a G pn pd M).length +
      ((initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) (initMiddleWriters a)).map
        fun W => W.scratch S G [ga, pn, pd, M, h, h₁]).sum ≤ hierBuilderSpace a pn pd G.n G.m M := by
  obtain ⟨hm, hn, hP, hN, hQ, hR, hS, hV, hE, hT, h1⟩ := initBuilder_counts S G a pn pd M hg
  have hPV := initProjectedWriterScratch_le S true hg.b_pos hg.valid
  have hPE := initProjectedWriterScratch_le S false hg.b_pos hg.valid
  have hsteps := initRestSteps_le_gamma hg.b_pos hg.valid ha hg.bounds hg.depth hg.branch
    hg.terms hg.verts hg.mM hg.proj hg.owner_lt
  have hblock := length_initBlock_le S ha G pn pd hg
  simp only [initWriters, initMiddleWriters, endpointWriters, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, headerW, valsW, graphW, numTermW,
    numConnW, numPairsW, staticW, depthW, initBoundW, kappaW, argW, zeroW, ownerW, zeroPowW,
    zeroValW, zeroGraphW, countersW, pairCurW, stackW, endpointW, connectorPairW, reverseBucketW,
    termBucketW, pairBucketW, supportBucketW, projectedW, pairTableW, initReverseWriterScratch,
    initTermWriterScratch, initPairBucketScratch, initSupportWriterScratch, Nat.zero_add, Nat.add_zero]
  unfold hierBuilderSpace
  unfold initRestSteps at hsteps
  let Γ := gammaHP a (dOf pn pd) M
  have hsmall : 1 ≤ (initBlock S a G pn pd M).length := h1
  have hl : 2000 * G.m * Γ = 2000 * (G.m * Γ) := Nat.mul_assoc ..
  have hs : 63 * G.m * Γ = 63 * (G.m * Γ) := Nat.mul_assoc ..
  rw [hl] at hblock
  rw [hs] at hsteps
  change _ ≤ 300000 * G.m * Γ
  rw [Nat.mul_assoc]
  omega

/-- The concrete RAM builder meets the verified time and space contract. -/
theorem hierInitBlockBuilder_spec (a : ℕ) (ha : 1 ≤ a) :
    BuildProcSpec a (hierInitBuilder a ha (initMiddleWriters a)) 40000
      (hierBuilderSpace a) 300000 2 :=
  hierInitBuilder_spec ha (initMiddleWriters a) rfl
    (fun S G ga pn pd M h h₁ hg =>
      initMiddleWriters_sections S G a pn pd M [ga, pn, pd, M, h, h₁] hg)
    (fun S G ga pn pd M h h₁ _ _ => initBuilder_space_bound S G a ha ga pn pd M h h₁)
    (fun S G => initBuilder_work_bound S G a ha)
    (hierBuilderSpace_form a)

end MinCostFlow.HierPaths

end
