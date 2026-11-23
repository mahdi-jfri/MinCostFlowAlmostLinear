module

public import MinCostFlow.SparseCore.Program.CompBatchLoop
public import MinCostFlow.SparseCore.Program.CompSplitListBranch
public import MinCostFlow.SparseCore.Program.CompSplitListPhi
import WordRAM.Tactic

/-!
# Batch-Update Loop Helpers with Canonical Split Lists (`CompSplitListBatchLoopBase`)

Defines `compEmitAllBranchesStmt` and `compBatchWithSplitsLoopStmt`, proves the pure cardinality
bridge `canonStepSplits_length_eq_card_sdiff`, and verifies `compEmitAllBranches_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Loop statements -/

/-- Inner loop over branches `j = 0 .. k - 1` calling `bEmit` (`compEmitBranchSplitProc`).
Expects: `r0 = b`, `r3 = k`, `r4 = vCap`, `r7 = cntBase`, `r13 = tag`, `r14 = delE`,
`r15 = x0`, `r16 = y0`, `r17 = spBufBase`, `r18 = spCntBase`, `r19 = oldCntBase`,
`r20 = ufBase`, `r21 = 0`. -/
def compEmitAllBranchesStmt (bEmit : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 21) (.reg 3))
    (.assign 22 (.load (.bin .add (.reg 19) (.reg 21))) ;;
     .assign 23 (.load (.bin .add (.reg 7) (.reg 21))) ;;
     .assign 24 (.bin .mul (.reg 21) (.reg 4)) ;;
     .assign 25 (.bin .add (.bin .add (.reg 7) (.reg 3)) (.reg 24)) ;;
     .assign 26 (.bin .add (.reg 25) (.bin .mul (.reg 3) (.reg 4))) ;;
     .assign 27 (.bin .add (.reg 17) (.bin .mul (.const 4) (.reg 24))) ;;
     .assign 28 (.bin .add (.reg 18) (.reg 21)) ;;
     .call 29 bEmit [.reg 0, .reg 21, .reg 25, .reg 26, .reg 22, .reg 23,
       .reg 13, .reg 14, .reg 15, .reg 16, .reg 27, .reg 28, .reg 20] ;;
     .assign 21 (.bin .add (.reg 21) (.const 1)))

/-- Main batch loop with canonical split emission. Uses registers `r0..r12` identically to
`compBatchLoopStmt`, and stores `[tag, delE]` transiently in `[ufBase, ufBase + 2)` and `[x0, y0]`
in `[endsTmp, endsTmp + 2)` across `compBatchDispStmt`, zeroing all four before invoking
`compEmitAllBranchesStmt`. -/
def compBatchWithSplitsLoopStmt (bIns bDel bSplit bEnds bEmit : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 6))
    (.assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
     .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
     .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
     .assign 20 (.bin .add (.reg 19) (.reg 3)) ;;
     .assign 21 (.bin .add (.reg 20) (.const 2)) ;;
     compCopySliceStmt 7 19 3 22 23 ;;
     .assign 13 (.load (.reg 11)) ;;
     .store (.reg 21) (.reg 13) ;;
     .cond (.bin .eq (.reg 13) (.const 1))
       (.assign 14 (.load (.bin .add (.reg 11) (.const 1))) ;;
        .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
        .call 22 bEnds [.reg 0, .reg 14, .reg 20])
       (.cond (.bin .lt (.const 1) (.reg 13))
         (.store (.reg 20) (.load (.bin .add (.reg 11) (.const 1))) ;;
          .store (.bin .add (.reg 20) (.const 1)) (.load (.bin .add (.reg 11) (.const 2))))
         (.assign 14 (.const 0))) ;;
     compBatchDispStmt bIns bDel bSplit ;;
     .assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
     .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
     .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
     .assign 21 (.bin .add (.reg 19) (.reg 3)) ;;
     .assign 20 (.bin .add (.reg 21) (.const 2)) ;;
     .assign 13 (.load (.reg 20)) ;;
     .assign 14 (.load (.bin .add (.reg 20) (.const 1))) ;;
     .assign 15 (.load (.reg 21)) ;;
     .assign 16 (.load (.bin .add (.reg 21) (.const 1))) ;;
     .store (.reg 20) (.const 0) ;;
     .store (.bin .add (.reg 20) (.const 1)) (.const 0) ;;
     .store (.reg 21) (.const 0) ;;
     .store (.bin .add (.reg 21) (.const 1)) (.const 0) ;;
     .assign 21 (.const 0) ;;
     compEmitAllBranchesStmt bEmit ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

lemma compEmitAllBranchesStmt_noRand (bEmit : ℕ) : (compEmitAllBranchesStmt bEmit).NoRand := by
  simp [compEmitAllBranchesStmt, Stmt.NoRand]

lemma compBatchWithSplitsLoopStmt_noRand (bIns bDel bSplit bEnds bEmit : ℕ) :
    (compBatchWithSplitsLoopStmt bIns bDel bSplit bEnds bEmit).NoRand := by
  simp [compBatchWithSplitsLoopStmt, compCopySliceStmt, compBatchDispStmt,
    compEmitAllBranchesStmt, Stmt.NoRand]

/-! ## 2. Pure cardinality bridge for `canonStepSplits` -/

lemma canonStepSplits_length_eq_card_sdiff {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu_val : cs.G.UpdateIsValid u)
    {cuts1 : List (ℕ × ℕ)} (hndE : (cuts1.map Prod.fst).Nodup)
    (hsetE : (cuts1.map Prod.fst).toFinset = cs.RF.F.E \ (compLSFStepSingle cs u).RF.F.E)
    (hndR : (cuts1.map Prod.snd).Nodup)
    (hdisj : ∀ r ∈ cuts1.map Prod.snd,
      r ∉ (match u with | .split _ v' _ _ => [v'] | _ => []))
    (hsetR : (cuts1.map Prod.snd).toFinset ∪
        (match u with | .split _ v' _ _ => {v'} | _ => ∅) =
      (compLSFStepSingle cs u).RF.R \ cs.RF.R) :
    (canonStepSplits cs u).length = ((compLSFStepSingle cs u).RF.R \ cs.RF.R).card := by
  classical
  have hlen_cuts : cuts1.length = (cs.RF.F.E \ (compLSFStepSingle cs u).RF.F.E).card := by
    have := congrArg Finset.card hsetE
    rwa [List.toFinset_card_of_nodup hndE, List.length_map] at this
  simp only [canonStepSplits, List.length_append, releasesSplitEntries_length, Finset.length_sort]
  cases u with
  | insert e a b =>
    have hR := congrArg Finset.card hsetR
    simp only [Finset.union_empty, List.toFinset_card_of_nodup hndR, List.length_map] at hR
    simp only [inputSplitEntries, List.length_nil, Nat.zero_add, forestAfterInput]
    omega
  | delete e =>
    have hR := congrArg Finset.card hsetR
    simp only [Finset.union_empty, List.toFinset_card_of_nodup hndR, List.length_map] at hR
    have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs (.delete e)) :=
      compLSFBatch_inv (U := [.delete e]) hI ⟨hu_val, trivial⟩
    have hnotE : e ∉ (compLSFStepSingle cs (.delete e)).RF.F.E := fun h => by
      have := (compLSF_F_edge_orig hI1 h).1
      simp [compLSFStepSingle, MGraph.applyUpdate] at this
    by_cases heF : e ∈ cs.RF.F.E
    · have hsdiff_eq : (cs.RF.F.E.erase e) \ (compLSFStepSingle cs (.delete e)).RF.F.E =
          (cs.RF.F.E \ (compLSFStepSingle cs (.delete e)).RF.F.E).erase e := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
      have heS : e ∈ cs.RF.F.E \ (compLSFStepSingle cs (.delete e)).RF.F.E :=
        Finset.mem_sdiff.mpr ⟨heF, hnotE⟩
      simp only [inputSplitEntries, heF, ↓reduceIte, List.length_singleton, forestAfterInput,
        eraseForestEdge, hsdiff_eq, Finset.card_erase_of_mem heS]
      have hpos : 1 ≤ (cs.RF.F.E \ (compLSFStepSingle cs (.delete e)).RF.F.E).card :=
        Finset.card_pos.mpr ⟨e, heS⟩
      omega
    · have her : cs.RF.F.E.erase e = cs.RF.F.E := Finset.erase_eq_of_notMem heF
      simp only [inputSplitEntries, heF, ↓reduceIte, List.length_nil, Nat.zero_add,
        forestAfterInput, eraseForestEdge, her]
      omega
  | split v v' St Sh =>
    have hR := congrArg Finset.card hsetR
    have hnv : v' ∉ (cuts1.map Prod.snd).toFinset := fun h =>
      hdisj v' (List.mem_toFinset.mp h) (by simp)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hnv),
      Finset.card_singleton, List.toFinset_card_of_nodup hndR, List.length_map] at hR
    simp only [inputSplitEntries, List.length_singleton, forestAfterInput, MGraph.applyUpdate]
    omega

lemma canonStepSplits_length_le_succ_t (cs : CompLSFState) (u : Update) :
    (canonStepSplits cs u).length ≤
      1 + ((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).card := by
  simp only [canonStepSplits, List.length_append, releasesSplitEntries_length, Finset.length_sort]
  cases u with
  | insert _ _ _ => simp [inputSplitEntries]
  | delete e => by_cases h : e ∈ cs.RF.F.E <;> simp [inputSplitEntries, h]
  | split _ _ _ _ => simp [inputSplitEntries]

/-! ## 3. Inner loop verification (`compEmitAllBranches_runs`) -/

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compEmitAllBranchesStmt`: invokes `compEmitBranchSplitProc` for every
branch `j : Fin k`, appending `canonStepSplits (S j) u` at `spBufBase + 4 * (j * vCap) + 4 * spCnts j`,
updating `spCntBase + j`, leaving `ufBase` zeroed, preserving all other memory, and costing
`≤ 1500 * (Nat.log 2 (x1.m0Total + 2) + 1) * ∑ j, t_j + 1400 * k + 10`. -/
lemma compEmitAllBranches_runs {W : LSFWindowImpl}
    {w k b bZero bSort bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean bEmit
      cntBase spBufBase spCntBase oldCntBase ufBase tag delE x0 y0 : ℕ}
    {S : CompLSFFamily k} {x1 : CompLSFMeta k} {touched1 : List ℕ} {u : Update}
    {oldCnts spCnts : Fin k → ℕ} {cuts1 : Fin k → List (ℕ × ℕ)}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpRootVal : p.procs[bRootVal]? = some compRootValProc)
    (hpEndRoots : p.procs[bEndRoots]? = some compEdgeEndRootsProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hpClean : p.procs[bUFClean]? = some compUFCleanProc)
    (hpEmit : p.procs[bEmit]? = some (compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort)
      bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep0 : ∃ ℓ₀, ∀ j : Fin k, CompLSFInv W.C_lsst ℓ₀ (S j))
    (hu_val : ∀ j : Fin k, (S j).G.UpdateIsValid u)
    (hrep1 : CompLSFRepDirty W k b (fun j => compLSFStepSingle (S j) u) x1 touched1 st.mem)
    (hend_le_cnt : x1.endAddr ≤ cntBase)
    (hcnt_le_sp : cntBase + k + 2 * (k * x1.vCap) ≤ spBufBase)
    (hsp_le_cnt : spBufBase + 4 * (k * x1.vCap) ≤ spCntBase)
    (hcnt_le_old : spCntBase + k ≤ oldCntBase)
    (hold_le_uf : oldCntBase + k ≤ ufBase)
    (huf_w : ufBase + ufEmitScratchSize x1.vCap < 2 ^ w)
    (hargs_w : tag < 2 ^ w ∧ delE < 2 ^ w ∧ x0 < 2 ^ w ∧ y0 < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr3 : st.regs 3 = k) (hr4 : st.regs 4 = x1.vCap)
    (hr7 : st.regs 7 = cntBase) (hr13 : st.regs 13 = tag) (hr14 : st.regs 14 = delE)
    (hr15 : st.regs 15 = x0) (hr16 : st.regs 16 = y0)
    (hr17 : st.regs 17 = spBufBase) (hr18 : st.regs 18 = spCntBase)
    (hr19 : st.regs 19 = oldCntBase) (hr20 : st.regs 20 = ufBase) (hr21 : st.regs 21 = 0)
    (hold_m : ∀ j : Fin k, st.mem (oldCntBase + j.1) = oldCnts j)
    (hnew_m : ∀ j : Fin k, st.mem (cntBase + j.1) = oldCnts j + (cuts1 j).length)
    (hcut_m : ∀ j : Fin k, ∀ i (hi : i < (cuts1 j).length),
      st.mem (cntBase + k + j.1 * x1.vCap + (oldCnts j + i)) = (cuts1 j)[i].2 ∧
      st.mem (cntBase + k + k * x1.vCap + j.1 * x1.vCap + (oldCnts j + i)) = (cuts1 j)[i].1)
    (hcut_bd : ∀ j : Fin k, oldCnts j + (cuts1 j).length ≤ x1.vCap)
    (hcut_spec : ∀ j : Fin k,
      ((cuts1 j).map Prod.fst).Nodup ∧
      ((cuts1 j).map Prod.fst).toFinset = (S j).RF.F.E \ (compLSFStepSingle (S j) u).RF.F.E ∧
      ((cuts1 j).map Prod.snd).toFinset ∪
        (match u with | .split _ v' _ _ => {v'} | _ => ∅) =
        (compLSFStepSingle (S j) u).RF.R \ (S j).RF.R ∧
      (∀ q ∈ cuts1 j, q.2 < x1.vCap))
    (htag_spec : ∀ j : Fin k, match u with
      | .insert _ _ _ => tag = 0
      | .delete e => tag = 1 ∧ delE = e ∧
          (e ∈ (S j).RF.F.E → x0 = (S j).G.tail e ∧ y0 = (S j).G.head e)
      | .split v v' _ _ => 2 ≤ tag ∧ x0 = v ∧ y0 = v')
    (hspCnt_m : ∀ j : Fin k, st.mem (spCntBase + j.1) = spCnts j)
    (hspCnt_bd : ∀ j : Fin k, spCnts j + (canonStepSplits (S j) u).length ≤ x1.vCap)
    (huf_zero : ∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → st.mem a = 0) :
    ∃ st' c,
      Runs w p ω (compEmitAllBranchesStmt bEmit) st .normal st' c ∧
      (∀ r < 13, st'.regs r = st.regs r) ∧
      (∀ j : Fin k,
        let step := canonStepSplits (S j) u
        st'.mem (spCntBase + j.1) = spCnts j + step.length ∧
        (∀ idx (hidx : idx < step.length),
          let e := step[idx]
          st'.mem (spBufBase + 4 * (j.1 * x1.vCap) + 4 * (spCnts j + idx)) =
            (if e.isRelease then 1 else 0) ∧
          st'.mem (spBufBase + 4 * (j.1 * x1.vCap) + 4 * (spCnts j + idx) + 1) = e.edge ∧
          st'.mem (spBufBase + 4 * (j.1 * x1.vCap) + 4 * (spCnts j + idx) + 2) = e.kept ∧
          st'.mem (spBufBase + 4 * (j.1 * x1.vCap) + 4 * (spCnts j + idx) + 3) = e.fresh)) ∧
      (∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → st'.mem a = 0) ∧
      (∀ a, (∀ j : Fin k, a ≠ spCntBase + j.1) →
        (∀ j : Fin k, a < spBufBase + 4 * (j.1 * x1.vCap) + 4 * spCnts j ∨
          spBufBase + 4 * (j.1 * x1.vCap) + 4 * (spCnts j + (canonStepSplits (S j) u).length) ≤ a) →
        (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) →
        st'.mem a = st.mem a) ∧
      c ≤ 1500 * (Nat.log 2 (x1.m0Total + 2) + 1) *
            (Finset.univ.sum fun j : Fin k =>
              ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card) +
          1400 * k + 10 := by
  have hk : 1 ≤ k := hrep1.1
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have huf_sz : ufEmitScratchSize x1.vCap = 8 * x1.vCap + 3 := rfl
  let stepFn : Fin k → List CompSplitEntry := fun j => canonStepSplits (S j) u
  let tFn : Fin k → ℕ := fun j =>
    ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card
  let loopBody : Stmt :=
    .assign 22 (.load (.bin .add (.reg 19) (.reg 21))) ;;
    .assign 23 (.load (.bin .add (.reg 7) (.reg 21))) ;;
    .assign 24 (.bin .mul (.reg 21) (.reg 4)) ;;
    .assign 25 (.bin .add (.bin .add (.reg 7) (.reg 3)) (.reg 24)) ;;
    .assign 26 (.bin .add (.reg 25) (.bin .mul (.reg 3) (.reg 4))) ;;
    .assign 27 (.bin .add (.reg 17) (.bin .mul (.const 4) (.reg 24))) ;;
    .assign 28 (.bin .add (.reg 18) (.reg 21)) ;;
    .call 29 bEmit [.reg 0, .reg 21, .reg 25, .reg 26, .reg 22, .reg 23,
      .reg 13, .reg 14, .reg 15, .reg 16, .reg 27, .reg 28, .reg 20] ;;
    .assign 21 (.bin .add (.reg 21) (.const 1))
  have hloop : ∀ rem j (s : State), j ≤ k → k - j = rem →
      (∀ r < 21, s.regs r = st.regs r) → s.regs 21 = j →
      (∀ q : Fin k, q.1 < j →
        s.mem (spCntBase + q.1) = spCnts q + (stepFn q).length ∧
        (∀ idx (hidx : idx < (stepFn q).length),
          let e := (stepFn q)[idx]
          s.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx)) =
            (if e.isRelease then 1 else 0) ∧
          s.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 1) = e.edge ∧
          s.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 2) = e.kept ∧
          s.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 3) = e.fresh)) →
      (∀ q : Fin k, j ≤ q.1 → s.mem (spCntBase + q.1) = spCnts q) →
      (∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → s.mem a = 0) →
      (∀ a, (∀ q : Fin k, q.1 < j → a ≠ spCntBase + q.1) →
        (∀ q : Fin k, q.1 < j → a < spBufBase + 4 * (q.1 * x1.vCap) + 4 * spCnts q ∨
          spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + (stepFn q).length) ≤ a) →
        (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) →
        s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω (.loop (.bin .lt (.reg 21) (.reg 3)) loopBody) s .normal st' c ∧
        (∀ r < 13, st'.regs r = st.regs r) ∧
        (∀ q : Fin k,
          st'.mem (spCntBase + q.1) = spCnts q + (stepFn q).length ∧
          (∀ idx (hidx : idx < (stepFn q).length),
            let e := (stepFn q)[idx]
            st'.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx)) =
              (if e.isRelease then 1 else 0) ∧
            st'.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 1) = e.edge ∧
            st'.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 2) = e.kept ∧
            st'.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + 3) = e.fresh)) ∧
        (∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → st'.mem a = 0) ∧
        (∀ a, (∀ q : Fin k, a ≠ spCntBase + q.1) →
          (∀ q : Fin k, a < spBufBase + 4 * (q.1 * x1.vCap) + 4 * spCnts q ∨
            spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + (stepFn q).length) ≤ a) →
          (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) →
          st'.mem a = st.mem a) ∧
        c ≤ 1500 * (Nat.log 2 (x1.m0Total + 2) + 1) *
              ((Finset.univ.filter fun q : Fin k => j ≤ q.1).sum tFn) +
            1400 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrem hr_lt hr21 hdone _ huf hfr
      have hjk : j = k := by omega
      subst hjk
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr21, hr_lt 3 (by omega), hr3],
        rfl, rfl, by simp [Expr.size]⟩), fun r hr => hr_lt r (by omega), fun q => hdone q q.2, huf,
        fun a h1 h2 h3 => hfr a (fun q _ => h1 q) (fun q _ => h2 q) h3, by omega⟩
    | succ rem ih =>
      intro j s hj hrem hr_lt hr21 hdone hrem_c huf hfr
      have hjlt : j < k := by omega
      let jf : Fin k := ⟨j, hjlt⟩
      have hjv_le : j * x1.vCap + x1.vCap ≤ k * x1.vCap := by
        have := Nat.mul_le_mul_right x1.vCap (show j + 1 ≤ k by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have hbelow_sp : ∀ a < spBufBase, s.mem a = st.mem a := fun a ha =>
        hfr a (fun _ _ => by omega) (fun _ _ => Or.inl (by omega)) (Or.inl (by omega))
      have hold_s : s.mem (oldCntBase + j) = oldCnts jf :=
        (hfr _ (fun _ _ => by omega) (fun q _ => Or.inr (by
          have hq : q.1 * x1.vCap + x1.vCap ≤ k * x1.vCap := by
            have := Nat.mul_le_mul_right x1.vCap (show q.1 + 1 ≤ k by have := q.2; omega)
            rw [Nat.add_mul, Nat.one_mul] at this; exact this
          have := hspCnt_bd q; dsimp only [stepFn]; omega)) (Or.inl (by omega))).trans (hold_m jf)
      have hnew_s : s.mem (cntBase + j) = oldCnts jf + (cuts1 jf).length :=
        (hbelow_sp _ (by omega)).trans (hnew_m jf)
      set rootsPtr := cntBase + k + j * x1.vCap
      set fDelPtr := rootsPtr + k * x1.vCap
      set spBufJ := spBufBase + 4 * (j * x1.vCap)
      set spCntAddr := spCntBase + j
      let s1 : State := { s with regs := Function.update s.regs 22 (oldCnts jf) }
      let s2 : State := { s1 with regs := Function.update s1.regs 23 (oldCnts jf + (cuts1 jf).length) }
      let s3 : State := { s2 with regs := Function.update s2.regs 24 (j * x1.vCap) }
      let s4 : State := { s3 with regs := Function.update s3.regs 25 rootsPtr }
      let s5 : State := { s4 with regs := Function.update s4.regs 26 fDelPtr }
      let s6 : State := { s5 with regs := Function.update s5.regs 27 spBufJ }
      let s7 : State := { s6 with regs := Function.update s6.regs 28 spCntAddr }
      have hs1 : Runs w p ω (.assign 22 (.load (.bin .add (.reg 19) (.reg 21)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨oldCnts jf, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_lt 19 (by omega), hr19, hr21,
            show oldCntBase + j < 2 ^ w by omega]) hold_s, rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 7) (.reg 21)))) s1 .normal s2 5 :=
        runs_assign_iff.mpr ⟨oldCnts jf + (cuts1 jf).length, Expr.eval_load_of_eq (by
          simp [s1, Expr.eval, BinOp.eval, hr_lt 7 (by omega), hr7, hr21,
            show cntBase + j < 2 ^ w by omega]) hnew_s, rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w p ω (.assign 24 (.bin .mul (.reg 21) (.reg 4))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨j * x1.vCap, by
          simp [s2, s1, Expr.eval, BinOp.eval, hr21, hr_lt 4 (by omega), hr4,
            show j * x1.vCap < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hs4 : Runs w p ω (.assign 25 (.bin .add (.bin .add (.reg 7) (.reg 3)) (.reg 24))) s3 .normal s4 6 :=
        runs_assign_iff.mpr ⟨rootsPtr, by
          simp [s3, s2, s1, Expr.eval, BinOp.eval, hr_lt 7 (by omega), hr7, hr_lt 3 (by omega), hr3,
            show cntBase + k < 2 ^ w by omega, show rootsPtr < 2 ^ w by omega, rootsPtr],
          rfl, rfl, by simp [Expr.size]⟩
      have hs5 : Runs w p ω (.assign 26 (.bin .add (.reg 25) (.bin .mul (.reg 3) (.reg 4)))) s4 .normal s5 6 :=
        runs_assign_iff.mpr ⟨fDelPtr, by
          simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr_lt 3 (by omega), hr3, hr_lt 4 (by omega), hr4,
            show k * x1.vCap < 2 ^ w by omega, show fDelPtr < 2 ^ w by omega, fDelPtr],
          rfl, rfl, by simp [Expr.size]⟩
      have hs6 : Runs w p ω (.assign 27 (.bin .add (.reg 17) (.bin .mul (.const 4) (.reg 24)))) s5 .normal s6 6 :=
        runs_assign_iff.mpr ⟨spBufJ, by
          simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr_lt 17 (by omega), hr17, hw4,
            show 4 * (j * x1.vCap) < 2 ^ w by omega, show spBufJ < 2 ^ w by omega, spBufJ],
          rfl, rfl, by simp [Expr.size]⟩
      have hs7 : Runs w p ω (.assign 28 (.bin .add (.reg 18) (.reg 21))) s6 .normal s7 4 :=
        runs_assign_iff.mpr ⟨spCntAddr, by
          simp [s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr_lt 18 (by omega), hr18, hr21,
            show spCntAddr < 2 ^ w by omega, spCntAddr], rfl, rfl, by simp [Expr.size]⟩
      have hrep1_s : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 s.mem :=
        compLSFRepDirty_of_agree hrep1 (fun a ha1 ha2 => hbelow_sp a (by omega))
      have hcut_bd_j := hcut_bd jf
      have hcut_sp_j := hcut_spec jf
      obtain ⟨sE, cE, hrE, hE_cnt, hE_buf, hE_uf, hE_fr, hcE⟩ :=
        compEmitBranchSplit_runs (W := W) (w := w) (k := k) (b := b)
          (rootsPtr := rootsPtr) (fDelPtr := fDelPtr) (oldC := oldCnts jf)
          (tag := tag) (delE := delE) (x0 := x0) (y0 := y0)
          (spBufJ := spBufJ) (spCntAddr := spCntAddr) (ufBase := ufBase) (spCnt := spCnts jf)
          (S := S) (x1 := x1) (touched1 := touched1) (u := u) (cuts1 := cuts1 jf)
          (p := p) (mem := s.mem) (pos := s7.pos) (ω := ω) jf
          hpZero hpSort hpRootVal hpEndRoots hpInitFind hpPairUnion hpClean hw16
          (by obtain ⟨ℓ₀, hI⟩ := hrep0; exact ⟨ℓ₀, hI jf⟩) (hu_val jf) hrep1_s
          (by omega) (by dsimp only [rootsPtr, fDelPtr]; omega)
          (by dsimp only [rootsPtr, fDelPtr, spBufJ]; omega)
          (by dsimp only [spBufJ, spCntAddr]; omega)
          (by dsimp only [spCntAddr]; omega) huf_w hargs_w
          hcut_sp_j.1 hcut_sp_j.2.1 (by cases u <;> exact hcut_sp_j.2.2.1) hcut_sp_j.2.2.2
          (fun i hi => by
            have hc := hcut_m jf i hi
            have h1 := hbelow_sp (rootsPtr + (oldCnts jf + i)) (by dsimp only [rootsPtr]; omega)
            have h2 := hbelow_sp (fDelPtr + (oldCnts jf + i)) (by dsimp only [rootsPtr, fDelPtr]; omega)
            have hfEq : fDelPtr = cntBase + k + k * x1.vCap + j * x1.vCap := by dsimp only [rootsPtr, fDelPtr]; omega
            rw [h1, h2, hfEq]; exact hc)
          (htag_spec jf) (hrem_c jf le_rfl) (hspCnt_bd jf) huf
      let s8 : State := { s7 with regs := Function.update s7.regs 29 0, mem := sE.mem, pos := sE.pos }
      have hs8 : Runs w p ω
          (.call 29 bEmit [.reg 0, .reg 21, .reg 25, .reg 26, .reg 22, .reg 23,
            .reg 13, .reg 14, .reg 15, .reg 16, .reg 27, .reg 28, .reg 20])
          s7 .normal s8 (13 + cE + 1) :=
        runs_call_iff.mpr ⟨[b, j, rootsPtr, fDelPtr, oldCnts jf, oldCnts jf + (cuts1 jf).length,
          tag, delE, x0, y0, spBufJ, spCntAddr, ufBase], _, .returned 0, sE, cE,
          by simp [evalArgs, Expr.eval, s7, s6, s5, s4, s3, s2, s1,
            hr_lt 0 (by omega), hr0, hr21, hr_lt 13 (by omega), hr13, hr_lt 14 (by omega), hr14,
            hr_lt 15 (by omega), hr15, hr_lt 16 (by omega), hr16, hr_lt 20 (by omega), hr20],
          hpEmit, hrE, rfl, rfl, by simp [argsSize, Expr.size]⟩
      let s9 : State := { s8 with regs := Function.update s8.regs 21 (j + 1) }
      have hs9 : Runs w p ω (.assign 21 (.bin .add (.reg 21) (.const 1))) s8 .normal s9 4 :=
        runs_assign_iff.mpr ⟨j + 1, by
          simp [s8, s7, s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr21, hw1,
            show j + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have q8 := runs_seq_iff.mpr (Or.inr ⟨s8, 13 + cE + 1, 4, hs8, hs9, rfl⟩)
      have q7 := runs_seq_iff.mpr (Or.inr ⟨s7, 4, _, hs7, q8, rfl⟩)
      have q6 := runs_seq_iff.mpr (Or.inr ⟨s6, 6, _, hs6, q7, rfl⟩)
      have q5 := runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, hs5, q6, rfl⟩)
      have q4 := runs_seq_iff.mpr (Or.inr ⟨s4, 6, _, hs4, q5, rfl⟩)
      have q3 := runs_seq_iff.mpr (Or.inr ⟨s3, 4, _, hs3, q4, rfl⟩)
      have q2 := runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2, q3, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hs1, q2, rfl⟩)
      obtain ⟨st', cRest, hrest_run, hr_fin, hdone_fin, huf_fin, hfr_fin, hcRest⟩ :=
        ih (j + 1) s9 (by omega) (by omega)
          (fun r hr => by
            simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1,
              Function.update_of_ne (show r ≠ 21 by omega), Function.update_of_ne (show r ≠ 29 by omega),
              Function.update_of_ne (show r ≠ 28 by omega), Function.update_of_ne (show r ≠ 27 by omega),
              Function.update_of_ne (show r ≠ 26 by omega), Function.update_of_ne (show r ≠ 25 by omega),
              Function.update_of_ne (show r ≠ 24 by omega), Function.update_of_ne (show r ≠ 23 by omega),
              Function.update_of_ne (show r ≠ 22 by omega)]
            exact hr_lt r hr)
          (by simp [s9])
          (fun q hq => by
            by_cases hqj : q.1 = j
            · have hqe : q = jf := Fin.ext hqj; subst hqe
              exact ⟨hE_cnt, hE_buf⟩
            · have hqlt : q.1 < j := by omega
              have hqv_le : q.1 * x1.vCap + x1.vCap ≤ j * x1.vCap := by
                have := Nat.mul_le_mul_right x1.vCap (show q.1 + 1 ≤ j by omega)
                rw [Nat.add_mul, Nat.one_mul] at this; exact this
              have hqbd := hspCnt_bd q
              have hjbd := hspCnt_bd jf
              obtain ⟨hd1, hd2⟩ := hdone q hqlt
              refine ⟨(hE_fr _ (by dsimp only [spCntAddr]; omega) (Or.inr (by dsimp only [spBufJ]; omega))
                  (Or.inl (by omega))).trans hd1, fun idx hidx => ?_⟩
              have he := hd2 idx hidx
              have hfr_q : ∀ off < 4, s9.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + off) =
                  s.mem (spBufBase + 4 * (q.1 * x1.vCap) + 4 * (spCnts q + idx) + off) := fun off hoff =>
                hE_fr _ (by dsimp only [spCntAddr, stepFn] at hidx ⊢; omega)
                  (Or.inl (by dsimp only [spBufJ, stepFn] at hidx ⊢; omega))
                  (Or.inl (by dsimp only [stepFn] at hidx ⊢; omega))
              exact ⟨by simpa using (hfr_q 0 (by omega)).trans he.1, (hfr_q 1 (by omega)).trans he.2.1,
                (hfr_q 2 (by omega)).trans he.2.2.1, (hfr_q 3 (by omega)).trans he.2.2.2⟩)
          (fun q hq => (hE_fr _ (by dsimp only [spCntAddr]; omega)
            (Or.inr (by dsimp only [spBufJ]; have := hspCnt_bd jf; omega)) (Or.inl (by omega))).trans
            (hrem_c q (by omega)))
          hE_uf
          (fun a h1 h2 h3 => (hE_fr a (h1 jf (by dsimp [jf]; omega)) (h2 jf (by dsimp [jf]; omega)) h3).trans
            (hfr a (fun q hq => h1 q (by omega)) (fun q hq => h2 q (by omega)) h3))
      have hsum_split : ((Finset.univ.filter fun q : Fin k => j ≤ q.1).sum tFn) =
          tFn jf + ((Finset.univ.filter fun q : Fin k => j + 1 ≤ q.1).sum tFn) := by
        have hpart : (Finset.univ.filter fun q : Fin k => j ≤ q.1) =
            insert jf (Finset.univ.filter fun q : Fin k => j + 1 ≤ q.1) := by
          ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, jf]; omega
        rw [hpart, Finset.sum_insert (by simp [jf])]
      have hmul_c : 1500 * (Nat.log 2 (x1.m0Total + 2) + 1) *
            ((Finset.univ.filter fun q : Fin k => j ≤ q.1).sum tFn) =
          1500 * tFn jf * (Nat.log 2 (x1.m0Total + 2) + 1) +
          1500 * (Nat.log 2 (x1.m0Total + 2) + 1) *
            ((Finset.univ.filter fun q : Fin k => j + 1 ≤ q.1).sum tFn) := by
        rw [hsum_split]; ring
      have h1400 : 1400 * (rem + 1) = 1400 * rem + 1400 := by ring
      have hcond : (Expr.bin .lt (.reg 21) (.reg 3)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr21, hr_lt 3 (by omega), hr3, hjlt, hw1]
      exact ⟨st', _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s9, _, cRest, hcond, by decide,
        hbody, hrest_run, by simp [Expr.size]; rfl⟩)), hr_fin, hdone_fin, huf_fin, hfr_fin,
        by dsimp only [tFn] at hmul_c hcRest ⊢; omega⟩
  obtain ⟨st', c, hrun, hr_fin, hdone_fin, huf_fin, hfr_fin, hc⟩ :=
    hloop k 0 st (Nat.zero_le k) (by omega) (fun _ _ => rfl) hr21
      (fun _ h => by omega) (fun q _ => hspCnt_m q) huf_zero (fun _ _ _ _ => rfl)
  have hfilt : (Finset.univ.filter fun q : Fin k => 0 ≤ q.1) = Finset.univ := by ext q; simp
  rw [hfilt] at hc
  exact ⟨st', c, hrun, hr_fin, hdone_fin, huf_fin, hfr_fin, by dsimp only [tFn] at hc; omega⟩

end

end MinCostFlow.SparseCore.Program
