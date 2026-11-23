module

public import MinCostFlow.SparseCore.Program.CompSplitListBatchLoop
public import MinCostFlow.SparseCore.Program.CompSplitListPack
public import MinCostFlow.SparseCore.Program.CompBatchProcs
import WordRAM.Tactic

/-!
# Batch-Update Helpers with Canonical Split Lists (`CompSplitListBatchBase`)

Defines `compBatchWithSplitsProc`, proves `compBatchWithSplitsProc_noRand`, the prefix-location
and canonical split-entry word-bound lemmas (`prefix_locate`, `canonSplitList_entries_lt`), and
the `CompLSFRepAt` / `compPhiFull` restoration helper after unmarking `touchMark`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Batch-update procedure with canonical split lists -/

/-- `op 0` (`args = [b, batchPtr, heap]`): executes an encoded `BatchAt` batch `U` sequentially,
writes `[numTouched, c_0, ..., c_{r-1}, chgPtr_0, ..., chgPtr_{k-1}, spPtr_0, ..., spPtr_{k-1}]`
plus packed `LSFChangeAt` and `SplitEntriesAt` records in `[heap, outEnd)`, clears `touchMark`
and all scratch buffers so `ZeroFrom st'.mem outEnd` holds, and returns `outEnd`. -/
def compBatchWithSplitsProc (bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))) ;;
  .assign 6 (.load (.reg 1)) ;;
  .assign 7 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 6)))
    (.bin .mul (.reg 3) (.bin .add (.const 5) (.bin .mul (.const 6) (.reg 4))))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 7) (.reg 3))
    (.bin .mul (.const 2) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 3)) ;;
  .assign 9 (.bin .add (.bin .add (.reg 20) (.const 2))
    (.bin .add (.bin .mul (.const 8) (.reg 4)) (.const 3))) ;;
  .store (.reg 2) (.const 0) ;;
  .assign 10 (.const 0) ;;
  .assign 11 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 12 (.const 0) ;;
  compBatchWithSplitsLoopStmt bIns bDel bSplit bEnds bEmit ;;
  .assign 13 (.load (.reg 2)) ;;
  .assign 14 (.const 0) ;;
  .loop (.bin .lt (.reg 14) (.reg 13))
    (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))) ;;
     .store (.bin .add (.reg 5) (.reg 15)) (.const 0) ;;
     .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
  .call 15 bZero
    [.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13),
     .bin .sub (.bin .mul (.const 2) (.reg 6)) (.reg 13)] ;;
  .call 15 bPackChg [.reg 0, .bin .add (.reg 2) (.reg 3), .reg 13, .reg 7, .reg 8, .reg 12] ;;
  .assign 16 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13)) ;;
  .assign 17 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 4) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 3)) ;;
  .call 15 bPackSp [.reg 0, .reg 16, .reg 15, .reg 18, .reg 17, .reg 19] ;;
  .ret (.reg 15)

lemma compBatchWithSplitsProc_noRand (bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp : ℕ) :
    (compBatchWithSplitsProc bZero bIns bDel bSplit bEnds bEmit bPackChg bPackSp).NoRand := by
  simp [compBatchWithSplitsProc, compBatchWithSplitsLoopStmt, compCopySliceStmt,
    compBatchDispStmt, compEmitAllBranchesStmt, Stmt.NoRand]

/-! ## 2. Word-bound helpers for packed change and split-list records -/

lemma prefix_locate {k base a : ℕ} (f : Fin k → ℕ)
    (h1 : base ≤ a) (h2 : a < base + (Finset.range k).sum fun i => if hi : i < k then f ⟨i, hi⟩ else 0) :
    ∃ j : Fin k,
      base + ((Finset.range j.1).sum fun i => if hi : i < k then f ⟨i, hi⟩ else 0) ≤ a ∧
      a < base + ((Finset.range j.1).sum fun i => if hi : i < k then f ⟨i, hi⟩ else 0) + f j := by
  have haux : ∀ m ≤ k, a < base + (Finset.range m).sum (fun i => if hi : i < k then f ⟨i, hi⟩ else 0) →
      ∃ j : Fin k, j.1 < m ∧
        base + ((Finset.range j.1).sum fun i => if hi : i < k then f ⟨i, hi⟩ else 0) ≤ a ∧
        a < base + ((Finset.range j.1).sum fun i => if hi : i < k then f ⟨i, hi⟩ else 0) + f j := by
    intro m
    induction m with
    | zero => intro _ hlt; simp at hlt; omega
    | succ m ih =>
      intro hm hlt
      simp only [Finset.sum_range_succ, show m < k by omega, ↓reduceDIte] at hlt
      by_cases hlt' : a < base + (Finset.range m).sum (fun i => if hi : i < k then f ⟨i, hi⟩ else 0)
      · obtain ⟨j, hj, hlo, hhi⟩ := ih (by omega) hlt'
        exact ⟨j, by omega, hlo, hhi⟩
      · exact ⟨⟨m, by omega⟩, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩
  obtain ⟨j, _, hlo, hhi⟩ := haux k le_rfl h2
  exact ⟨j, hlo, hhi⟩

private lemma canonPick_lt {old final A : Finset ℕ} {vCap : ℕ}
    (hv : 0 < vCap) (ho : ∀ r ∈ old, r < vCap) (hf : ∀ r ∈ final, r < vCap) :
    canonPick old final A < vCap := by
  unfold canonPick
  split_ifs with h1 h2
  · exact ho _ (Finset.mem_inter.mp (Finset.min'_mem _ h1)).2
  · exact hf _ (Finset.mem_inter.mp (Finset.min'_mem _ h2)).2
  · exact hv

private lemma canonRoots_lt {F : MGraph} {old final : Finset ℕ} {vCap : ℕ}
    (hv : 0 < vCap) (ho : ∀ r ∈ old, r < vCap) (hf : ∀ r ∈ final, r < vCap) :
    ∀ r ∈ canonRoots F old final, r < vCap := fun r hr => by
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hr
  exact canonPick_lt hv ho hf

private lemma newRoot_lt {R old : Finset ℕ} {vCap : ℕ}
    (hv : 0 < vCap) (hR : ∀ r ∈ R, r < vCap) : newRoot R old < vCap := by
  unfold newRoot
  exact (Finset.sup_lt_iff hv).mpr fun r hr => hR r (Finset.mem_sdiff.mp hr).1

private lemma rf_root_lt {RF : RootedForest} {vCap v : ℕ}
    (hR : ∀ r ∈ RF.R, r < vCap) (hv : v < vCap) : RF.root v < vCap := by
  unfold RootedForest.root
  split_ifs with h
  · exact hR _ (Classical.choose_spec h).1
  · exact hv

private lemma releasesSplitEntries_lt {final : Finset ℕ} {vCap eCap : ℕ}
    (hv : 0 < vCap) (hfin : ∀ r ∈ final, r < vCap) :
    ∀ (cuts : List ℕ) (L : LSF),
      cuts.Nodup →
      (∀ r ∈ L.F.R, r < vCap) →
      (∀ e ∈ L.F.F.E, L.F.F.tail e < vCap) →
      (∀ e ∈ cuts, e ∈ L.F.F.E ∧ e < eCap) →
      ∀ s ∈ releasesSplitEntries final L cuts,
        s.edge < eCap ∧ s.kept < vCap ∧ s.fresh < vCap := by
  intro cuts
  induction cuts with
  | nil => intro _ _ _ _ _ _ h; simp [releasesSplitEntries] at h
  | cons e rest ih =>
    intro L hnd hR htail hcuts s hs
    simp only [releasesSplitEntries, List.mem_cons] at hs
    obtain ⟨hne, hnd_r⟩ := List.nodup_cons.mp hnd
    have he := hcuts e (by simp)
    have hR' : ∀ r ∈ canonRoots (eraseForestEdge L.F.F e) L.F.R final, r < vCap :=
      canonRoots_lt hv hR hfin
    rcases hs with rfl | hs'
    · exact ⟨he.2, rf_root_lt hR (htail e he.1), newRoot_lt hv hR'⟩
    · exact ih { T := L.T, F := { F := eraseForestEdge L.F.F e, R := canonRoots (eraseForestEdge L.F.F e) L.F.R final }, wstr := L.wstr }
        hnd_r hR'
        (fun f hf => htail f (Finset.mem_erase.mp hf).2)
        (fun f hf => ⟨Finset.mem_erase.mpr ⟨by rintro rfl; exact hne hf, (hcuts f (List.mem_cons_of_mem e hf)).1⟩,
          (hcuts f (List.mem_cons_of_mem e hf)).2⟩) s hs'

lemma canonSplitList_entries_lt {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap eCap : ℕ}
    (hv : 0 < vCap) (he : 0 < eCap) :
    ∀ (U : List Update) (cs : CompLSFState),
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U → BatchWithinCaps vCap eCap U →
      (∀ v ∈ cs.G.V, v < vCap) → (∀ e ∈ cs.G.E, e < eCap) →
      ∀ s ∈ canonSplitList cs U, s.edge < eCap ∧ s.kept < vCap ∧ s.fresh < vCap := by
  intro U
  induction U with
  | nil => intro _ _ _ _ _ _ _ h; simp [canonSplitList] at h
  | cons u us ih =>
    intro cs hI hVal hCaps hV hE s hs
    rcases hVal with ⟨hu_val, hVal2⟩
    have hCaps1 : UpdateWithinCaps vCap eCap u ∧ BatchWithinCaps vCap eCap us := by
      simpa [BatchWithinCaps] using hCaps
    let cs1 := compLSFStepSingle cs u
    have hI1 : CompLSFInv C_lsst ℓ₀ cs1 := compLSFBatch_inv (U := [u]) hI ⟨hu_val, trivial⟩
    have hV1 : ∀ v ∈ cs1.G.V, v < vCap := fun v hv1 => by
      dsimp only [cs1, compLSFStepSingle] at hv1
      cases u with
      | insert _ _ _ => exact hV v hv1
      | delete _ => exact hV v hv1
      | split _ v' _ _ =>
        rcases Finset.mem_insert.mp hv1 with rfl | hv0
        · exact hCaps1.1
        · exact hV v hv0
    have hE1 : ∀ e ∈ cs1.G.E, e < eCap := fun e he1 => by
      dsimp only [cs1, compLSFStepSingle] at he1
      cases u with
      | insert e0 _ _ =>
        rcases Finset.mem_insert.mp he1 with rfl | he0
        · exact hCaps1.1
        · exact hE e he0
      | delete _ => exact hE e (Finset.mem_erase.mp he1).2
      | split _ _ _ _ => exact hE e he1
    simp only [canonSplitList, List.mem_append] at hs
    rcases hs with hstep | hrest
    · have hRSF0 := compLSF_RF_isRSF hI
      have hRSF1 := compLSF_RF_isRSF hI1
      have hR0 : ∀ r ∈ cs.RF.R, r < vCap := fun r hr => hV r (hRSF0.2.2.1 hr)
      have hR1 : ∀ r ∈ cs1.RF.R, r < vCap := fun r hr => hV1 r (hRSF1.2.2.1 hr)
      have hMidR : ∀ r ∈ (inputMid cs u).F.R, r < vCap := by
        cases u with
        | insert _ _ _ => exact hR0
        | delete e0 =>
          dsimp only [inputMid]; split_ifs
          · exact canonRoots_lt hv hR0 hR1
          · exact hR0
        | split _ _ _ _ =>
          dsimp only [inputMid]; exact canonRoots_lt hv hR0 hR1
      have hMidTail : ∀ f ∈ (inputMid cs u).F.F.E, (inputMid cs u).F.F.tail f < vCap := by
        intro f hf
        cases u with
        | insert _ _ _ => exact hV _ (hRSF0.2.1 ▸ (hRSF0.1.1 f hf).1)
        | delete e0 =>
          dsimp only [inputMid] at hf ⊢
          split_ifs at hf ⊢
          · exact hV _ (hRSF0.2.1 ▸ (hRSF0.1.1 f (Finset.mem_erase.mp hf).2).1)
          · exact hV _ (hRSF0.2.1 ▸ (hRSF0.1.1 f hf).1)
        | split v v' St Sh =>
          dsimp only [inputMid, forestAfterInput, MGraph.applyUpdate] at hf ⊢
          have ht0 : cs.RF.F.tail f ∈ cs.G.V := hRSF0.2.1 ▸ (hRSF0.1.1 f hf).1
          split_ifs
          · exact hCaps1.1
          · exact hV _ ht0
      have hMidE : ∀ f ∈ (forestAfterInput cs.RF.F u).E, f ∈ (inputMid cs u).F.F.E ∧ f < eCap := by
        intro f hf
        cases u with
        | insert _ _ _ => exact ⟨hf, hE f (hRSF0.2.2.2.2.2.1 hf)⟩
        | delete e0 =>
          have hf0 := (Finset.mem_erase.mp hf).2
          refine ⟨?_, hE f (hRSF0.2.2.2.2.2.1 hf0)⟩
          dsimp only [inputMid]; split_ifs
          · exact hf
          · exact hf0
        | split _ _ _ _ => exact ⟨hf, hE f (hRSF0.2.2.2.2.2.1 hf)⟩
      simp only [canonStepSplits, List.mem_append] at hstep
      rcases hstep with hinp | hrel
      · cases u with
        | insert _ _ _ => simp [inputSplitEntries] at hinp
        | delete e0 =>
          simp only [inputSplitEntries] at hinp
          split_ifs at hinp with heF
          · simp only [List.mem_singleton] at hinp; subst hinp
            exact ⟨he, rf_root_lt hR0 (hV _ (hRSF0.2.1 ▸ (hRSF0.1.1 e0 heF).1)), newRoot_lt hv hMidR⟩
          · simp at hinp
        | split v v' _ _ =>
          simp only [inputSplitEntries, List.mem_singleton] at hinp; subst hinp
          exact ⟨he, rf_root_lt hR0 (hV v hu_val.1), newRoot_lt hv hMidR⟩
      · exact releasesSplitEntries_lt hv hR1 _ (inputMid cs u) (Finset.sort_nodup _ _) hMidR hMidTail
          (fun f hf => hMidE f (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp hf)).1) s hrel
    · exact ih cs1 hI1 hVal2 hCaps1.2 hV1 hE1 s hrest

/-! ## 3. Restoration of `CompLSFRepAt` and `compPhiFull` after unmarking `touchMark` -/

lemma compLSFRepAt_of_unmarked {W : LSFWindowImpl} {k b : ℕ}
    {S' : CompLSFFamily k} {xL : CompLSFMeta k} {touched' : List ℕ} {memL memF : ℕ → ℕ}
    (hrepL : CompLSFRepDirty W k b S' xL touched' memL)
    (hzero_tm : ∀ c ∈ touched', memF (compTouchMarkBase b xL.vCap xL.eCap + c) = 0)
    (hag_not_tm : ∀ a < xL.endAddr,
      (a < compTouchMarkBase b xL.vCap xL.eCap ∨ compTouchMarkBase b xL.vCap xL.eCap + xL.vCap ≤ a) →
      memF a = memL a)
    (hag_tm_untouched : ∀ c < xL.vCap, c ∉ touched' →
      memF (compTouchMarkBase b xL.vCap xL.eCap + c) = memL (compTouchMarkBase b xL.vCap xL.eCap + c)) :
    CompLSFRepAt W k b S' xL memF ∧ compPhiFull k b xL memF = compPhiFull k b xL memL := by
  have hrep_orig := hrepL
  obtain ⟨hkL, hhL, hLinL, hPfpL, hLwL, hhLwL, heCapL, hncL, hneL, hTEL, hhdrL, hBrL, hm0L,
    hTL, hCompL, hEfL, hVCL, hECL, hFlL, hGhL, hTML, hOneL, hWinL, hDisjL⟩ := hrepL
  set tmBase := compTouchMarkBase b xL.vCap xL.eCap
  have htm_le_end : tmBase + xL.vCap ≤ xL.endAddr := by
    have : tmBase + xL.vCap ≤ compTablesEnd b xL.vCap xL.eCap xL.L_w xL.m0Total k := by
      dsimp only [tmBase, compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase,
        compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
        compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hb_hdr_lt : b + compHdrSize ≤ xL.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b xL.vCap xL.eCap xL.L_w xL.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hge_tm : tmBase + xL.vCap ≤ compHandlesBase b xL.vCap xL.eCap xL.L_w := by
    dsimp only [tmBase, compHandlesBase, compStaticSize, compTouchMarkBase,
      compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
      compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
  have hrep_final : CompLSFRepAt W k b S' xL memF := by
    rw [← compLSFRepDirty_nil_iff]
    refine ⟨hkL, hhL, hLinL, hPfpL, hLwL, hhLwL, heCapL, hncL, hneL, hTEL,
      compHeaderAt_of_agree hhdrL (fun a ha1 ha2 => hag_not_tm a (by omega) (Or.inl (by
        dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase,
          compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
          compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha2 ⊢; omega))),
      hBrL, hm0L, hTL, ?_, hEfL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDisjL⟩
    · intro c; obtain ⟨c1, c2, c3, c4⟩ := hCompL c; have hc_lt : c.1 < xL.vCap := lt_of_lt_of_le c.2 hncL
      refine ⟨(hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega))).trans c1,
        (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base]; omega))).trans c2,
        (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base]; omega))).trans c3, fun hp => ?_⟩
      obtain ⟨ec, e1, e2, e3⟩ := c4 hp
      exact ⟨ec, e1, (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega))).trans e2, e3⟩
    · intro c v hv
      have hv_lt : v < xL.vCap := hTL.hVlt v (by
        obtain ⟨ℓ₀', hBr'⟩ := hBrL
        exact (hBr' ⟨0, hkL⟩).1.hV_eq ▸ Finset.mem_biUnion.mpr ⟨xL.compOf c, hTL.compOf_mem c, hv⟩)
      exact (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega))).trans (hVCL c v hv)
    · intro e he; have he_lt : e < xL.eCap := hTL.hElt e he
      exact ⟨(hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base]; omega))).trans (hECL e he).1,
        (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega))).trans (hECL e he).2⟩
    · intro e he
      exact ⟨(hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega))).trans (hFlL e he).1,
        (hag_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase]; omega))).trans (hFlL e he).2⟩
    · set gPtr := compGhostBase b xL.vCap xL.eCap
      have hgh_ag : ∀ a, gPtr ≤ a → a < tmBase → memF a = memL a := fun a h1 h2 =>
        hag_not_tm a (by omega) (Or.inl h2)
      refine ⟨fun u hu => ?_, fun e he hcr => ?_⟩
      · obtain ⟨g1, g2, g3, g4⟩ := hGhL.1 u hu
        exact ⟨g1.of_agree
            (hgh_ag _ (by dsimp only [ghostTHeadBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostTHeadBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTPrevBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostTPrevBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTNextBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostTNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostTCntBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostTCntBase, gPtr]; omega)).trans g2,
          g3.of_agree
            (hgh_ag _ (by dsimp only [ghostHHeadBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostHHeadBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHPrevBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostHPrevBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHNextBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostHNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostHCntBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostHCntBase, gPtr]; omega)).trans g4⟩
      · have he_lt : e < xL.eCap := hTL.hElt e he
        exact ⟨(hgh_ag _ (by dsimp only [ghostTVertBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostTVertBase, gPtr]; omega)).trans (hGhL.2 e he hcr).1,
          (hgh_ag _ (by dsimp only [ghostHVertBase]; omega) (by dsimp only [tmBase, compTouchMarkBase, compGhostSize, ghostHVertBase, gPtr]; omega)).trans (hGhL.2 e he hcr).2⟩
    · intro c hc; simp only [List.not_mem_nil, ↓reduceIte]
      by_cases hct : c ∈ touched'
      · exact hzero_tm c hct
      · rw [hag_tm_untouched c hc hct]; simpa [hct] using hTML c hc
    · have hone_ag : ∀ i < xL.L_w, memF (compOneLimbBase b xL.vCap xL.eCap + i) =
          memL (compOneLimbBase b xL.vCap xL.eCap + i) := fun i hi => by
        have h1e := compOneLimb_end_eq b xL.vCap xL.eCap xL.L_w
        have hlt_e : compOneLimbBase b xL.vCap xL.eCap + i < xL.endAddr := by
          dsimp only [compTablesEnd] at hTEL; omega
        exact hag_not_tm _ hlt_e (Or.inr (by dsimp only [tmBase, compOneLimbBase]; omega))
      exact ⟨(hone_ag 0 hLwL).trans hOneL.1, fun i h1 h2 => (hone_ag i h2).trans (hOneL.2 i h1 h2)⟩
    · intro ec j; obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := hWinL ec j
      have hslot_lt : compHandlesBase b xL.vCap xL.eCap xL.L_w + (ec.1 * k + j.1) < xL.endAddr := by
        have h1 : (ec.1 + 1) * k ≤ xL.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd] at hTEL; omega
      refine ⟨(hag_not_tm _ hslot_lt (Or.inr (by omega))).trans w1,
        (lsfRep_local W.h _ _ _ memL memF fun a ha => (hag_not_tm a (lt_of_lt_of_le ha.2 w7)
          (Or.inr (by have := ha.1; dsimp only [compTablesEnd] at w6; omega))).symm).1 w2,
        w3, w4, w5, w6, w7⟩
  refine ⟨hrep_final, ?_⟩
  have h1 : compPhi b xL memF = compPhi b xL memL := by
    rw [compPhi_eq_sum_dirty (compLSFRepDirty_nil_iff.mpr hrep_final), compPhi_eq_sum_dirty hrep_orig]
    refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨_, _, _, _, _, w6, w7⟩ := hWinL ec j
    exact lsfPhi_congr fun a ha1 ha2 => hag_not_tm a (lt_of_lt_of_le ha2 w7)
      (Or.inr (by dsimp only [compTablesEnd] at w6; omega))
  have h2 : compSplitPhi k b xL memF = compSplitPhi k b xL memL := by
    rw [compSplitPhi_eq_sum_dirty (compLSFRepDirty_nil_iff.mpr hrep_final), compSplitPhi_eq_sum_dirty hrep_orig]
  simp only [compPhiFull, h1, h2]

end

end MinCostFlow.SparseCore.Program
