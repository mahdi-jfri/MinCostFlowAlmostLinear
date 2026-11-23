module

public import MinCostFlow.SparseCore.Program.SpanModuleDefs

/-!
# Relocatable Deterministic Module for `dynSpannerDS`: Verification (`SpanModule`)

Proves length, determinism (`Stmt.NoRand`), and `DSRep.Implements` for `dynSpannerDSProcs impl b`
(`SpanModuleDefs.lean`):

* `dynSpannerDSProcs_length`: `(dynSpannerDSProcs impl b).length = 109 + impl.procs.length`.
* `dynSpannerDSProcs_noRand`: every procedure in `dynSpannerDSProcs impl b` has no `rand`.
* `dynSpannerDSProcs_unpack`: unpacks `HasDSInitProcs`, `HasUpdateLoopProcs`, and `dsOpProcs` from
  a single `p.HasAt b (dynSpannerDSProcs impl b)`.
* `dynSpannerDSProcs_implements`: `(dynSpannerRep P).Implements P.w p (b + dynSpannerInitOff)
  (fun i => b + dynSpannerUpdateOff + i) (dynSpannerDS P)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-! ## Private `HasAt`, length, and `NoRand` helpers -/

private lemma hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := by
  intro i hi
  have h1 := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at h1

private lemma hasAt_append_right {p : Program} {b n : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : xs.length = n) : p.HasAt (b + n) ys := by
  intro i hi
  have h1 := h (n + i) (by rw [List.length_append, hlen]; omega)
  rw [Nat.add_assoc]
  rw [List.getElem_append_right (by omega)] at h1
  simpa [hlen] using h1

private lemma hasAt_shift {p : Program} {b k₁ k₂ : ℕ} {xs : List Stmt}
    (h : p.HasAt ((b + k₁) + k₂) xs) {k : ℕ} (hk : k₁ + k₂ = k) : p.HasAt (b + k) xs := by
  rw [← hk, ← Nat.add_assoc]; exact h

private lemma noRand_append {xs ys : List Stmt}
    (hx : ∀ s ∈ xs, s.NoRand) (hy : ∀ s ∈ ys, s.NoRand) :
    ∀ s ∈ xs ++ ys, s.NoRand := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hx s h
  · exact hy s h

private lemma relocStmt_noRand (R b : ℕ) {s : Stmt} (h : s.NoRand) :
    (relocStmt R b s).NoRand := by
  induction s with
  | nop => trivial
  | assign _ _ => trivial
  | store _ _ => trivial
  | rand _ => exact False.elim h
  | ret _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | cond _ _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | loop _ _ ih => exact ih h
  | call _ _ _ => trivial

private lemma gtRevPrimProcs_length : gtRevPrimProcs.length = 2 := rfl
private lemma gtRevCoreProcs_length (a b : ℕ) : (gtRevCoreProcs a b).length = 1 := rfl
private lemma gtRevDynProcs_length (a b c : ℕ) : (gtRevDynProcs a b c).length = 1 := rfl
private lemma sparsifyDynProcs_length (a b c d e : ℕ) :
    (sparsifyDynProcs a b c d e).length = 1 := rfl
private lemma filterCopyProcs_length : filterCopyProcs.length = 1 := rfl
private lemma restrictRecProcs_length (a : ℕ) : (restrictRecProcs a).length = 1 := rfl
private lemma levelsDeleteProcs_length (a : ℕ) : (levelsDeleteProcs a).length = 1 := rfl
private lemma applyUProcs_length (a b : ℕ) : (applyUProcs a b).length = 1 := rfl
private lemma stepPrefixProcs_length (a b : ℕ) : (stepPrefixProcs a b).length = 1 := rfl
private lemma clearBucketsProcs_length : clearBucketsProcs.length = 1 := rfl
private lemma zeroRangeProcs_length : zeroRangeProcs.length = 1 := rfl
private lemma clearAboveProcs_length (a : ℕ) : (clearAboveProcs a).length = 1 := rfl
private lemma sparsifyStageProcs_length (a b : ℕ) : (sparsifyStageProcs a b).length = 1 := rfl
private lemma compProcs_length (a : ℕ) : (compProcs a).length = 1 := rfl
private lemma compAllProcs_length (a : ℕ) : (compAllProcs a).length = 1 := rfl
private lemma reembedProcs_length (a : ℕ) : (reembedProcs a).length = 1 := rfl
private lemma reembedAllProcs_length (a b : ℕ) : (reembedAllProcs a b).length = 1 := rfl
private lemma reembStageProcs_length (a b : ℕ) : (reembStageProcs a b).length = 1 := rfl
private lemma delRecordsProcs_length : delRecordsProcs.length = 1 := rfl
private lemma delAllProcs_length (a : ℕ) : (delAllProcs a).length = 1 := rfl
private lemma insRecordsProcs_length (a : ℕ) : (insRecordsProcs a).length = 1 := rfl
private lemma uhTailProcs_length (a b : ℕ) : (uhTailProcs a b).length = 1 := rfl
private lemma applyUHProcs_length (a : ℕ) : (applyUHProcs a).length = 1 := rfl
private lemma uhEndProcs_length (a b : ℕ) : (uhEndProcs a b).length = 1 := rfl
private lemma fillLevelProcs_length (a : ℕ) : (fillLevelProcs a).length = 1 := rfl
private lemma rebuildBucketsProcs_length (a b : ℕ) : (rebuildBucketsProcs a b).length = 1 := rfl
private lemma stepEndProcs_length (a b : ℕ) : (stepEndProcs a b).length = 1 := rfl
private lemma stepTailProcs_length (a b : ℕ) : (stepTailProcs a b).length = 1 := rfl
private lemma stepFinishProcs_length (a b : ℕ) : (stepFinishProcs a b).length = 1 := rfl
private lemma collectDProcs_length : collectDProcs.length = 1 := rfl
private lemma stepPosNonEmptyProcs_length (a b c d e : ℕ) :
    (stepPosNonEmptyProcs a b c d e).length = 1 := rfl
private lemma stepPosEmptyProcs_length (a : ℕ) : (stepPosEmptyProcs a).length = 1 := rfl
private lemma stepPosEpilogueProcs_length (a b : ℕ) :
    (stepPosEpilogueProcs a b).length = 1 := rfl
private lemma stepPosProcs_length (a b c : ℕ) : (stepPosProcs a b c).length = 1 := rfl
private lemma stepHeadProcs_length (a b : ℕ) : (stepHeadProcs a b).length = 1 := rfl
private lemma walkPtrsProcs_length : walkPtrsProcs.length = 1 := rfl
private lemma projProcs_length (a : ℕ) : (projProcs a).length = 1 := rfl
private lemma buildProjProcs_length (a b c : ℕ) : (buildProjProcs a b c).length = 1 := rfl
private lemma projStageProcs_length (a b : ℕ) : (projStageProcs a b).length = 1 := rfl
private lemma affStageProcs_length (a b : ℕ) : (affStageProcs a b).length = 1 := rfl
private lemma wordSumProcs_length : wordSumProcs.length = 1 := rfl
private lemma stepPosFullProcs_length (a b c d : ℕ) :
    (stepPosFullProcs a b c d).length = 1 := rfl
private lemma dsOpProcs_length (a b : ℕ) : (dsOpProcs a b).length = 1 := rfl

private lemma chunk1_length (b : ℕ) : (dynSpannerChunk1 b).length = 35 := by
  simp only [dynSpannerChunk1, List.length_append, stepAuxProcs_length, sortProcs_length,
    dgOpsProcs_length, dgEdgeProcs_length, dgSplitProcs_length, dgBatchProcs_length,
    gtProcs_length, gtEmitProcs_length, gtForwardProcs_length]

private lemma chunk2_length (impl : SparsifyImpl) (b : ℕ) :
    (dynSpannerChunk2 impl b).length = 18 := by
  simp only [dynSpannerChunk2, List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
    gtRevDynProcs_length, sparsifyDynProcs_length, revProcs_length, levelWalkProcs_length,
    phaseProcs_length, initProcs_length]

private lemma chunk3_length (b : ℕ) : (dynSpannerChunk3 b).length = 12 := by
  simp only [dynSpannerChunk3, List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
    restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length, stepPrefixProcs_length,
    clearBucketsProcs_length, zeroRangeProcs_length, clearAboveProcs_length, stepZeroProcs_length]

private lemma chunk4_length (b : ℕ) : (dynSpannerChunk4 b).length = 23 := by
  simp only [dynSpannerChunk4, List.length_append, sparsifyStageProcs_length, embOpsProcs_length,
    compProcs_length, compAllProcs_length, reembedProcs_length, reembedAllProcs_length,
    reembStageProcs_length, delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length,
    uhTailProcs_length, applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length,
    rebuildBucketsProcs_length, stepEndProcs_length, stepTailProcs_length, stepFinishProcs_length,
    collectDProcs_length, stepPosNonEmptyProcs_length]

private lemma chunk5_length (b : ℕ) : (dynSpannerChunk5 b).length = 20 := by
  simp only [dynSpannerChunk5, List.length_append, stepPosEmptyProcs_length,
    stepPosEpilogueProcs_length, stepPosProcs_length, affectedProcs_length, stepHeadProcs_length,
    walkPtrsProcs_length, projProcs_length, buildProjProcs_length, projStageProcs_length,
    affStageProcs_length, wordSumProcs_length, stepPosFullProcs_length, updateLoopProcs_length,
    dsOpProcs_length]

private lemma gtRevPrimProcs_noRand : ∀ s ∈ gtRevPrimProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

private lemma gtRevCoreProcs_noRand (bBatch bRevPrim : ℕ) :
    ∀ s ∈ gtRevCoreProcs bBatch bRevPrim, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

private lemma gtRevDynProcs_noRand (bOps bGT bRevCore : ℕ) :
    ∀ s ∈ gtRevDynProcs bOps bGT bRevCore, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

private lemma sparsifyDynProcs_noRand (R cw bFwd bRevDyn bGuest : ℕ) :
    ∀ s ∈ sparsifyDynProcs R cw bFwd bRevDyn bGuest, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · cases cw <;> simp [sparsifyDynStmt, computeWordSizeStmt, spHostSetupRevStmt, Stmt.NoRand]
  cases hs

private lemma sparsifyGuestProcs_noRand (impl : SparsifyImpl) (bGuest : ℕ) :
    ∀ s ∈ sparsifyGuestProcs impl bGuest, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · trivial
  · rcases List.mem_map.mp hs with ⟨t, ht, rfl⟩
    exact relocStmt_noRand impl.program.regBound bGuest (impl.hprocs_noRand t ht)

/-! ## Public length, determinism, and `DSRep.Implements` theorems -/

public section

theorem dynSpannerDSProcs_length (impl : SparsifyImpl) (b : ℕ) :
    (dynSpannerDSProcs impl b).length = 109 + impl.procs.length := by
  unfold dynSpannerDSProcs
  simp only [List.length_append, chunk1_length, chunk2_length, chunk3_length, chunk4_length,
    chunk5_length, sparsifyGuestProcs, List.length_cons, List.length_map]
  omega

/-- Every procedure in `dynSpannerDSProcs impl b` is deterministic (`Stmt.NoRand`). -/
theorem dynSpannerDSProcs_noRand (impl : SparsifyImpl) (b : ℕ) :
    ∀ s ∈ dynSpannerDSProcs impl b, s.NoRand := by
  have h1 : ∀ s ∈ dynSpannerChunk1 b, s.NoRand := by
    unfold dynSpannerChunk1
    refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append stepAuxProcs_noRand (sortProcs_noRand _))
      dgOpsProcs_noRand) (dgEdgeProcs_noRand _)) (dgSplitProcs_noRand _ _))
      (dgBatchProcs_noRand _ _ _ _)) (gtProcs_noRand _ _)) (gtEmitProcs_noRand _ _ _))
      (gtForwardProcs_noRand _ _ _ _)
  have h2 : ∀ s ∈ dynSpannerChunk2 impl b, s.NoRand := by
    unfold dynSpannerChunk2
    refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append gtRevPrimProcs_noRand (gtRevCoreProcs_noRand _ _))
      (gtRevDynProcs_noRand _ _ _)) (sparsifyDynProcs_noRand _ _ _ _ _))
      (revProcs_noRand _ _)) (levelWalkProcs_noRand _ _)) (phaseProcs_noRand _ _))
      (initProcs_noRand _ _ _ _ _ _ _)
  have h3 : ∀ s ∈ dynSpannerChunk3 b, s.NoRand := by
    unfold dynSpannerChunk3
    refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (noRand_append (stepZeroAuxProcs_noRand _)
      filterCopyProcs_noRand) (restrictRecProcs_noRand _)) (levelsDeleteProcs_noRand _))
      (applyUProcs_noRand _ _)) (stepPrefixProcs_noRand _ _)) clearBucketsProcs_noRand)
      zeroRangeProcs_noRand) (clearAboveProcs_noRand _)) (stepZeroProcs_noRand _ _ _ _ _ _ _)
  have h4 : ∀ s ∈ dynSpannerChunk4 b, s.NoRand := by
    unfold dynSpannerChunk4
    refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (noRand_append (sparsifyStageProcs_noRand _ _)
      (embOpsProcs_noRand _)) (compProcs_noRand _)) (compAllProcs_noRand _))
      (reembedProcs_noRand _)) (reembedAllProcs_noRand _ _)) (reembStageProcs_noRand _ _))
      delRecordsProcs_noRand) (delAllProcs_noRand _)) (insRecordsProcs_noRand _))
      (uhTailProcs_noRand _ _)) (applyUHProcs_noRand _)) (uhEndProcs_noRand _ _))
      (fillLevelProcs_noRand _)) (rebuildBucketsProcs_noRand _ _)) (stepEndProcs_noRand _ _))
      (stepTailProcs_noRand _ _)) (stepFinishProcs_noRand _ _)) collectDProcs_noRand)
      (stepPosNonEmptyProcs_noRand _ _ _ _ _)
  have h5 : ∀ s ∈ dynSpannerChunk5 b, s.NoRand := by
    unfold dynSpannerChunk5
    refine noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (noRand_append (noRand_append
      (noRand_append (noRand_append (noRand_append (stepPosEmptyProcs_noRand _)
      (stepPosEpilogueProcs_noRand _ _)) (stepPosProcs_noRand _ _ _)) (affectedProcs_noRand _))
      (stepHeadProcs_noRand _ _)) walkPtrsProcs_noRand) (projProcs_noRand _))
      (buildProjProcs_noRand _ _ _)) (projStageProcs_noRand _ _)) (affStageProcs_noRand _ _))
      wordSumProcs_noRand) (stepPosFullProcs_noRand _ _ _ _)) (updateLoopProcs_noRand _ _ _ _ _))
      (dsOpProcs_noRand _ _)
  unfold dynSpannerDSProcs
  exact noRand_append (noRand_append (noRand_append (noRand_append (noRand_append h1 h2) h3) h4) h5)
    (sparsifyGuestProcs_noRand impl _)

/-- Unpack all sub-library `HasAt` witnesses for `dynSpannerDS_implements` from a single
`p.HasAt b (dynSpannerDSProcs impl b)`. -/
theorem dynSpannerDSProcs_unpack {impl : SparsifyImpl} {p : Program} {b : ℕ}
    (hp : p.HasAt b (dynSpannerDSProcs impl b)) :
    HasDSInitProcs impl p (dynSpannerDSInitBases b) ∧
    HasUpdateLoopProcs impl p (dynSpannerDSUpdateLoopBases b) ∧
    p.HasAt (b + dynSpannerUpdateOff) (dsOpProcs (b + dsOffAux) (b + dsOffUL)) := by
  have h12345 := hasAt_append_left hp
  have hGuest : p.HasAt (b + 108) (sparsifyGuestProcs impl (b + dsOffGuest)) :=
    hasAt_append_right hp (by
      simp only [List.length_append, chunk1_length, chunk2_length, chunk3_length, chunk4_length,
        chunk5_length])
  have h1234 := hasAt_append_left h12345
  have hc5 : p.HasAt (b + 88) (dynSpannerChunk5 b) :=
    hasAt_append_right h12345 (by
      simp only [List.length_append, chunk1_length, chunk2_length, chunk3_length, chunk4_length])
  have h123 := hasAt_append_left h1234
  have hc4 : p.HasAt (b + 65) (dynSpannerChunk4 b) :=
    hasAt_append_right h1234 (by
      simp only [List.length_append, chunk1_length, chunk2_length, chunk3_length])
  have h12 := hasAt_append_left h123
  have hc3 : p.HasAt (b + 53) (dynSpannerChunk3 b) :=
    hasAt_append_right h123 (by
      simp only [List.length_append, chunk1_length, chunk2_length])
  have hc1 : p.HasAt b (dynSpannerChunk1 b) := hasAt_append_left h12
  have hc2 : p.HasAt (b + 35) (dynSpannerChunk2 impl b) :=
    hasAt_append_right h12 (chunk1_length b)
  -- Chunk 1 (offsets 0..34)
  have hFwd := hasAt_append_right hc1 (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length, dgOpsProcs_length,
      dgEdgeProcs_length, dgSplitProcs_length, dgBatchProcs_length, gtProcs_length,
      gtEmitProcs_length]; rfl : _ = dsOffFwd)
  have c1a := hasAt_append_left hc1
  have hEmit := hasAt_append_right c1a (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length, dgOpsProcs_length,
      dgEdgeProcs_length, dgSplitProcs_length, dgBatchProcs_length, gtProcs_length]; rfl : _ = dsOffEmit)
  have c1b := hasAt_append_left c1a
  have hGT := hasAt_append_right c1b (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length, dgOpsProcs_length,
      dgEdgeProcs_length, dgSplitProcs_length, dgBatchProcs_length]; rfl : _ = dsOffGT)
  have c1c := hasAt_append_left c1b
  have hBatch := hasAt_append_right c1c (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length, dgOpsProcs_length,
      dgEdgeProcs_length, dgSplitProcs_length]; rfl : _ = dsOffBatch)
  have c1d := hasAt_append_left c1c
  have hSplit := hasAt_append_right c1d (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length, dgOpsProcs_length,
      dgEdgeProcs_length]; rfl : _ = dsOffSplit)
  have c1e := hasAt_append_left c1d
  have hEdge := hasAt_append_right c1e (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length,
      dgOpsProcs_length]; rfl : _ = dsOffEdge)
  have c1f := hasAt_append_left c1e
  have hOps := hasAt_append_right c1f (by
    simp only [List.length_append, stepAuxProcs_length, sortProcs_length]; rfl : _ = dsOffOps)
  have c1g := hasAt_append_left c1f
  have hSort := hasAt_append_right c1g (by exact stepAuxProcs_length : _ = dsOffSort)
  have hAux : p.HasAt (b + dsOffAux) stepAuxProcs := by simpa [dsOffAux] using hasAt_append_left c1g
  -- Chunk 2 (offsets 35..52)
  have hInit := hasAt_shift (hasAt_append_right hc2 (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
      gtRevDynProcs_length, sparsifyDynProcs_length, revProcs_length, levelWalkProcs_length,
      phaseProcs_length] : _ = 15)) (rfl : 35 + 15 = dsOffInit)
  have c2a := hasAt_append_left hc2
  have hPhase := hasAt_shift (hasAt_append_right c2a (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
      gtRevDynProcs_length, sparsifyDynProcs_length, revProcs_length,
      levelWalkProcs_length] : _ = 10)) (rfl : 35 + 10 = dsOffPhase)
  have c2b := hasAt_append_left c2a
  have hLW := hasAt_shift (hasAt_append_right c2b (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
      gtRevDynProcs_length, sparsifyDynProcs_length, revProcs_length] : _ = 7))
    (rfl : 35 + 7 = dsOffLW)
  have c2c := hasAt_append_left c2b
  have hRev := hasAt_shift (hasAt_append_right c2c (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
      gtRevDynProcs_length, sparsifyDynProcs_length] : _ = 5)) (rfl : 35 + 5 = dsOffRev)
  have c2d := hasAt_append_left c2c
  have hSpDyn := hasAt_shift (hasAt_append_right c2d (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length,
      gtRevDynProcs_length] : _ = 4)) (rfl : 35 + 4 = dsOffSpDyn)
  have c2e := hasAt_append_left c2d
  have hRevDyn := hasAt_shift (hasAt_append_right c2e (by
    simp only [List.length_append, gtRevPrimProcs_length, gtRevCoreProcs_length] : _ = 3))
    (rfl : 35 + 3 = dsOffRevDyn)
  have c2f := hasAt_append_left c2e
  have hRevCore := hasAt_shift (hasAt_append_right c2f (by exact gtRevPrimProcs_length : _ = 2))
    (rfl : 35 + 2 = dsOffRevCore)
  have hRevPrim := hasAt_append_left c2f
  -- Chunk 3 (offsets 53..64)
  have hSZ := hasAt_shift (hasAt_append_right hc3 (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length, stepPrefixProcs_length,
      clearBucketsProcs_length, zeroRangeProcs_length, clearAboveProcs_length] : _ = 11))
    (rfl : 53 + 11 = dsOffSZ)
  have c3a := hasAt_append_left hc3
  have hClrA := hasAt_shift (hasAt_append_right c3a (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length, stepPrefixProcs_length,
      clearBucketsProcs_length, zeroRangeProcs_length] : _ = 10)) (rfl : 53 + 10 = dsOffClrA)
  have c3b := hasAt_append_left c3a
  have hZ := hasAt_shift (hasAt_append_right c3b (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length, stepPrefixProcs_length,
      clearBucketsProcs_length] : _ = 9)) (rfl : 53 + 9 = dsOffZ)
  have c3c := hasAt_append_left c3b
  have hCB := hasAt_shift (hasAt_append_right c3c (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length,
      stepPrefixProcs_length] : _ = 8)) (rfl : 53 + 8 = dsOffCB)
  have c3d := hasAt_append_left c3c
  have hPref := hasAt_shift (hasAt_append_right c3d (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length, applyUProcs_length] : _ = 7))
    (rfl : 53 + 7 = dsOffPref)
  have c3e := hasAt_append_left c3d
  have hU := hasAt_shift (hasAt_append_right c3e (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length, levelsDeleteProcs_length] : _ = 6)) (rfl : 53 + 6 = dsOffU)
  have c3f := hasAt_append_left c3e
  have hD := hasAt_shift (hasAt_append_right c3f (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length,
      restrictRecProcs_length] : _ = 5)) (rfl : 53 + 5 = dsOffD)
  have c3g := hasAt_append_left c3f
  have hR := hasAt_shift (hasAt_append_right c3g (by
    simp only [List.length_append, stepZeroAuxProcs_length, filterCopyProcs_length] : _ = 4))
    (rfl : 53 + 4 = dsOffR)
  have c3h := hasAt_append_left c3g
  have hF := hasAt_shift (hasAt_append_right c3h (by exact stepZeroAuxProcs_length _ : _ = 3))
    (rfl : 53 + 3 = dsOffF)
  have hZAux := hasAt_append_left c3h
  -- Chunk 4 (offsets 65..87)
  have hNE := hasAt_shift (hasAt_append_right hc4 (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length, rebuildBucketsProcs_length,
      stepEndProcs_length, stepTailProcs_length, stepFinishProcs_length,
      collectDProcs_length] : _ = 22)) (rfl : 65 + 22 = dsOffNE)
  have c4a := hasAt_append_left hc4
  have hCD := hasAt_shift (hasAt_append_right c4a (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length, rebuildBucketsProcs_length,
      stepEndProcs_length, stepTailProcs_length, stepFinishProcs_length] : _ = 21))
    (rfl : 65 + 21 = dsOffCD)
  have c4b := hasAt_append_left c4a
  have hFin := hasAt_shift (hasAt_append_right c4b (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length, rebuildBucketsProcs_length,
      stepEndProcs_length, stepTailProcs_length] : _ = 20)) (rfl : 65 + 20 = dsOffFin)
  have c4c := hasAt_append_left c4b
  have hST := hasAt_shift (hasAt_append_right c4c (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length, rebuildBucketsProcs_length,
      stepEndProcs_length] : _ = 19)) (rfl : 65 + 19 = dsOffST)
  have c4d := hasAt_append_left c4c
  have hSE := hasAt_shift (hasAt_append_right c4d (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length,
      rebuildBucketsProcs_length] : _ = 18)) (rfl : 65 + 18 = dsOffSE)
  have c4e := hasAt_append_left c4d
  have hRB := hasAt_shift (hasAt_append_right c4e (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length, fillLevelProcs_length] : _ = 17))
    (rfl : 65 + 17 = dsOffRB)
  have c4f := hasAt_append_left c4e
  have hFL := hasAt_shift (hasAt_append_right c4f (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length, uhEndProcs_length] : _ = 16)) (rfl : 65 + 16 = dsOffFL)
  have c4g := hasAt_append_left c4f
  have hUE := hasAt_shift (hasAt_append_right c4g (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length, uhTailProcs_length,
      applyUHProcs_length] : _ = 15)) (rfl : 65 + 15 = dsOffUE)
  have c4h := hasAt_append_left c4g
  have hAU := hasAt_shift (hasAt_append_right c4h (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length,
      uhTailProcs_length] : _ = 14)) (rfl : 65 + 14 = dsOffAU)
  have c4i := hasAt_append_left c4h
  have hUT := hasAt_shift (hasAt_append_right c4i (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length, insRecordsProcs_length] : _ = 13))
    (rfl : 65 + 13 = dsOffUT)
  have c4j := hasAt_append_left c4i
  have hIR := hasAt_shift (hasAt_append_right c4j (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length, delAllProcs_length] : _ = 12)) (rfl : 65 + 12 = dsOffIR)
  have c4k := hasAt_append_left c4j
  have hDA := hasAt_shift (hasAt_append_right c4k (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length, reembStageProcs_length,
      delRecordsProcs_length] : _ = 11)) (rfl : 65 + 11 = dsOffDA)
  have c4l := hasAt_append_left c4k
  have hDR := hasAt_shift (hasAt_append_right c4l (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length,
      reembStageProcs_length] : _ = 10)) (rfl : 65 + 10 = dsOffDR)
  have c4m := hasAt_append_left c4l
  have hRS := hasAt_shift (hasAt_append_right c4m (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length, reembedAllProcs_length] : _ = 9))
    (rfl : 65 + 9 = dsOffRS)
  have c4n := hasAt_append_left c4m
  have hRA := hasAt_shift (hasAt_append_right c4n (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length, reembedProcs_length] : _ = 8)) (rfl : 65 + 8 = dsOffRA)
  have c4o := hasAt_append_left c4n
  have hRe := hasAt_shift (hasAt_append_right c4o (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length, compProcs_length,
      compAllProcs_length] : _ = 7)) (rfl : 65 + 7 = dsOffRe)
  have c4p := hasAt_append_left c4o
  have hCA := hasAt_shift (hasAt_append_right c4p (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length,
      compProcs_length] : _ = 6)) (rfl : 65 + 6 = dsOffCA)
  have c4q := hasAt_append_left c4p
  have hC := hasAt_shift (hasAt_append_right c4q (by
    simp only [List.length_append, sparsifyStageProcs_length, embOpsProcs_length] : _ = 5))
    (rfl : 65 + 5 = dsOffC)
  have c4r := hasAt_append_left c4q
  have hEmb := hasAt_shift (hasAt_append_right c4r (by exact sparsifyStageProcs_length _ _ : _ = 1))
    (rfl : 65 + 1 = dsOffEmb)
  have hSS := hasAt_append_left c4r
  -- Chunk 5 (offsets 88..107)
  have hOp := hasAt_shift (hasAt_append_right hc5 (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length, projStageProcs_length, affStageProcs_length,
      wordSumProcs_length, stepPosFullProcs_length, updateLoopProcs_length] : _ = 19))
    (rfl : 88 + 19 = dsOffOp)
  have c5a := hasAt_append_left hc5
  have hUL := hasAt_shift (hasAt_append_right c5a (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length, projStageProcs_length, affStageProcs_length,
      wordSumProcs_length, stepPosFullProcs_length] : _ = 14)) (rfl : 88 + 14 = dsOffUL)
  have c5b := hasAt_append_left c5a
  have hFull := hasAt_shift (hasAt_append_right c5b (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length, projStageProcs_length, affStageProcs_length,
      wordSumProcs_length] : _ = 13)) (rfl : 88 + 13 = dsOffFull)
  have c5c := hasAt_append_left c5b
  have hSum := hasAt_shift (hasAt_append_right c5c (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length, projStageProcs_length,
      affStageProcs_length] : _ = 12)) (rfl : 88 + 12 = dsOffSum)
  have c5d := hasAt_append_left c5c
  have hAS := hasAt_shift (hasAt_append_right c5d (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length, projStageProcs_length] : _ = 11))
    (rfl : 88 + 11 = dsOffAS)
  have c5e := hasAt_append_left c5d
  have hPS := hasAt_shift (hasAt_append_right c5e (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length, buildProjProcs_length] : _ = 10)) (rfl : 88 + 10 = dsOffPS)
  have c5f := hasAt_append_left c5e
  have hBP := hasAt_shift (hasAt_append_right c5f (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length, walkPtrsProcs_length,
      projProcs_length] : _ = 9)) (rfl : 88 + 9 = dsOffBP)
  have c5g := hasAt_append_left c5f
  have hProj := hasAt_shift (hasAt_append_right c5g (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length,
      walkPtrsProcs_length] : _ = 8)) (rfl : 88 + 8 = dsOffProj)
  have c5h := hasAt_append_left c5g
  have hWP := hasAt_shift (hasAt_append_right c5h (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length, stepHeadProcs_length] : _ = 7))
    (rfl : 88 + 7 = dsOffWP)
  have c5i := hasAt_append_left c5h
  have hHead := hasAt_shift (hasAt_append_right c5i (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length, affectedProcs_length] : _ = 6)) (rfl : 88 + 6 = dsOffHead)
  have c5j := hasAt_append_left c5i
  have hAffP := hasAt_shift (hasAt_append_right c5j (by
    simp only [List.length_append, stepPosEmptyProcs_length, stepPosEpilogueProcs_length,
      stepPosProcs_length] : _ = 3)) (rfl : 88 + 3 = dsOffAffP)
  have c5k := hasAt_append_left c5j
  have hPos := hasAt_shift (hasAt_append_right c5k (by
    simp only [List.length_append, stepPosEmptyProcs_length,
      stepPosEpilogueProcs_length] : _ = 2)) (rfl : 88 + 2 = dsOffPos)
  have c5l := hasAt_append_left c5k
  have hEp := hasAt_shift (hasAt_append_right c5l (by exact stepPosEmptyProcs_length _ : _ = 1))
    (rfl : 88 + 1 = dsOffEp)
  have hEm := hasAt_append_left c5l
  refine ⟨⟨hInit, hOps, hBatch, hPhase, hLW, hRev, hSpDyn, hGuest, hFwd, hEmit, hRevDyn,
    hRevCore, hRevPrim, hEdge, hGT, hSort⟩,
    ⟨⟨hAux, hZAux, hSort, hOps, hEdge, hSplit, hBatch, hGT, hEmit, hFwd, hRevPrim, hRevCore,
      hRevDyn, hGuest, hSpDyn, hRev, hLW, hPhase, hInit, hF, hR, hD, hU, hPref, hCB, hZ, hClrA,
      hSZ⟩,
     ⟨⟨⟨hAux, hSort, hOps, hEdge, hSplit, hBatch, hGT, hEmit, hFwd, hRevPrim, hRevCore,
        hRevDyn, hGuest, hSpDyn, hRev, hLW, hSS, hEmb, hC, hCA, hRe, hRA, hRS, hDR, hDA, hIR,
        hUT, hAU, hUE, hCB, hPhase, hFL, hRB, hSE, hZ, hClrA, hST, hFin, hCD, hNE⟩,
       hEm, hEp, hPos⟩,
      hAffP, hD, hU, hF, hR, hPref, hHead, hWP, hProj, hBP, hPS, hAS, hSum, hFull⟩,
     hUL⟩,
    hOp⟩

/-- Any program containing `dynSpannerDSProcs P.impl b` at index `b` implements `dynSpannerDS P`
with initialization at `b + dynSpannerInitOff` and operation `0` at `b + dynSpannerUpdateOff`. -/
theorem dynSpannerDSProcs_implements (P : DSParams) {p : Program} {b : ℕ}
    (hp : p.HasAt b (dynSpannerDSProcs P.impl b)) :
    (dynSpannerRep P).Implements P.w p (b + dynSpannerInitOff)
      (fun i => b + dynSpannerUpdateOff + i) (dynSpannerDS P) := by
  obtain ⟨hpI, hps, hpOp⟩ := dynSpannerDSProcs_unpack hp
  have h := dynSpannerDS_implements P hpI hps hpOp
  simpa only [dynSpannerDSInitBases, dynSpannerInitOff, Nat.add_assoc] using h

end

end MinCostFlow.SparseCore.Program
