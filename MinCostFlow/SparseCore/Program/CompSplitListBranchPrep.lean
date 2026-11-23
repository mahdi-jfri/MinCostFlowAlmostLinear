module

public import MinCostFlow.SparseCore.Program.CompSplitListScan
public import MinCostFlow.SparseCore.Program.CompSplitListRevLoop
public import MinCostFlow.DynSpanner.Program.MergeSort
import MinCostFlow.SparseCore.CompLSFBridge
import WordRAM.Tactic

/-!
# Per-Branch Canonical Split-List Emitter: Phase 1 (`CompSplitListBranchPrep`)

Defines `ufEmitScratchSize`, `compEmitPhase1Stmt`, `compEmitPhase2Stmt`, and
`compEmitBranchSplitProc`, proves pure graph/forest helpers, and verifies Phase 1
(`compEmitPhase1_runs`: cut scan, split-root marking, merge sort of released edges,
and reverse Union-Find release emission).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Scratch size and procedure definitions -/

/-- Total scratch words required by `compEmitBranchSplitProc`:
* `[ufBase, ufBase + 6 * vCap + 1)`: Reverse Union-Find arrays (`isNew, par, sz, minF, oldR, act, actLen`);
* `[ufBase + 6 * vCap + 1, ufBase + 7 * vCap + 1)`: `dBuf` (sorted released edges);
* `[ufBase + 7 * vCap + 1, ufBase + 8 * vCap + 1)`: `sortScr` (merge-sort scratch);
* `[ufBase + 8 * vCap + 1, ufBase + 8 * vCap + 3)`: `tmp2` (2-word buffer for `bEndRoots`). -/
def ufEmitScratchSize (vCap : ℕ) : ℕ := 8 * vCap + 3

/-- Phase 1 of the slow path of `compEmitBranchSplitProc`: sets up `dBuf/sortScr/tmp2`, scans
cut log entries into `dBuf` and `isNew`, marks the split vertex if `1 < tag`, sorts `dBuf`,
loads `spCnt`, and executes `compRevLoopStmt`. -/
def compEmitPhase1Stmt (bSort bEndRoots bUFInitFind bUFPairUnion : ℕ) : Stmt :=
  .assign 15 (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 6) (.reg 13))) (.const 1)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 13)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 13)) ;;
  .assign 18 (.const 0) ;;
  .assign 19 (.const 0) ;;
  .assign 20 (.reg 4) ;;
  compScanCutsStmt ;;
  .cond (.bin .lt (.const 1) (.reg 6))
    (.assign 19 (.const 1) ;; .store (.bin .add (.reg 12) (.reg 9)) (.const 1))
    .nop ;;
  .cond (.bin .lt (.const 0) (.reg 18))
    (.call 23 bSort [.reg 15, .reg 18, .reg 16])
    .nop ;;
  .assign 24 (.load (.reg 11)) ;;
  .assign 20 (.reg 18) ;;
  compRevLoopStmt bEndRoots bUFInitFind bUFPairUnion

/-- Phase 2 of the slow path of `compEmitBranchSplitProc`: conditionally emits the input
delete/split entry at slot `spCnt`, writes `spCnt + hasInp + t` at `spCntAddr`, clears `isNew`,
cleans the Reverse Union-Find, zeroes `dBuf`/`sortScr`/`tmp2`, and returns `0`. -/
def compEmitPhase2Stmt (bZero bRootVal bUFInitFind bUFPairUnion bUFClean : ℕ) : Stmt :=
  .cond (.reg 19)
    (.call 22 bRootVal [.reg 0, .reg 1, .reg 8] ;;
     .call 23 bRootVal [.reg 0, .reg 1, .reg 9] ;;
     .call 25 bUFInitFind [.reg 12, .reg 13, .reg 22] ;;
     .call 26 bUFInitFind [.reg 12, .reg 13, .reg 23] ;;
     .assign 27 (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 24))) ;;
     .call 23 bUFPairUnion [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 0, .const 0, .const 0])
    .nop ;;
  .store (.reg 11) (.bin .add (.bin .add (.reg 24) (.reg 19)) (.reg 18)) ;;
  .assign 20 (.reg 4) ;;
  compUnmarkIsNewStmt ;;
  .cond (.bin .lt (.const 1) (.reg 6))
    (.store (.bin .add (.reg 12) (.reg 9)) (.const 0))
    .nop ;;
  .call 23 bUFClean [.reg 12, .reg 13] ;;
  .call 23 bZero [.reg 15, .reg 18] ;;
  .call 23 bZero [.reg 16, .reg 18] ;;
  .store (.reg 17) (.const 0) ;;
  .store (.bin .add (.reg 17) (.const 1)) (.const 0) ;;
  .ret (.const 0)

/-- Per-branch canonical split emitter.
`args = [b, j, rootsPtr, fDelPtr, oldC, newC, tag, delE, x0, y0, spBufJ, spCntAddr, ufBase]`. -/
def compEmitBranchSplitProc
    (bZero bSort bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean : ℕ) : Stmt :=
  .assign 13 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 14 (.bin .sub (.reg 5) (.reg 4)) ;;
  .cond (.bin .add (.reg 14) (.bin .lt (.const 1) (.reg 6)))
    (compEmitPhase1Stmt bSort bEndRoots bUFInitFind bUFPairUnion ;;
     compEmitPhase2Stmt bZero bRootVal bUFInitFind bUFPairUnion bUFClean)
    (.ret (.const 0))

lemma compEmitBranchSplitProc_noRand (a b c d e f g : ℕ) :
    (compEmitBranchSplitProc a b c d e f g).NoRand := by
  simp [compEmitBranchSplitProc, compEmitPhase1Stmt, compEmitPhase2Stmt,
    compScanCutsStmt, compRevLoopStmt, compUnmarkIsNewStmt, Stmt.NoRand]

/-! ## 2. Pure and sub-procedure helpers -/

lemma compEmitZeroRange_call {w bZero ptr len : ℕ} {p : Program} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hw16 : 16 ≤ 2 ^ w) (hbd : ptr + len < 2 ^ w) :
    ∃ o st' c, Runs w p ω compZeroRangeProc (startState [ptr, len] mem pos) o st' c ∧
      o.value = 0 ∧ (∀ i < len, st'.mem (ptr + i) = 0) ∧
      (∀ a, a < ptr ∨ ptr + len ≤ a → st'.mem a = mem a) ∧ c ≤ 20 * len + 15 := by
  obtain ⟨body, hbody, o, st', c, hrun, ⟨p', l', harg, hval, hpost, hfr⟩, hcost⟩ :=
    compZeroRange_meetsContract hpZero [ptr, len] mem pos ω (by simp; omega) ⟨ptr, len, rfl, hw16, hbd⟩
  have hb : body = compZeroRangeProc := Option.some.inj (hbody.symm.trans hpZero)
  have ⟨hp, hl⟩ : ptr = p' ∧ len = l' := by simpa using harg
  subst hb hp hl
  exact ⟨o, st', c, hrun, hval, hpost, hfr, by dsimp only [compZeroRangeContract] at hcost; exact hcost⟩

lemma compEmitMergeSort_call {w bSort a scratch : ℕ} {L : List ℕ} {p : Program}
    {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w) (ha_w : a + L.length < 2 ^ w) (hsc_w : scratch + L.length < 2 ^ w)
    (hdisj : a + L.length ≤ scratch ∨ scratch + L.length ≤ a)
    (hLat : ListAt mem a L) (hLw : ∀ x ∈ L, x < 2 ^ w) :
    ∃ body o st' c L',
      p.procs[bSort + sortIdxMergeSort]? = some body ∧
      Runs w p ω body (startState [a, L.length, scratch] mem pos) o st' c ∧
      o.value = 0 ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·) ∧ ListAt st'.mem a L' ∧
      (∀ addr, (addr < a ∨ a + L.length ≤ addr) → (addr < scratch ∨ scratch + L.length ≤ addr) →
        st'.mem addr = mem addr) ∧
      c ≤ 200 * L.length * (Nat.log 2 (L.length + 1) + 1) + 50 := by
  have hmc := mergeSort_meetsContract (w := w) (L := L) hpSort hpSort
  obtain ⟨body, hbody, o, st', c, hrun, ⟨a', sc', L', harg, hval, hperm, hpw, hLat', hfr⟩, hcost⟩ :=
    hmc [a, L.length, scratch] mem pos ω (by simp; omega) ⟨a, scratch, rfl, hw16, ha_w, hsc_w, hdisj, hLat, hLw⟩
  have ⟨ha, hsc⟩ : a = a' ∧ scratch = sc' := by
    have h1 : a = a' := by simpa using congrArg (fun l => l.getD 0 0) harg
    have h2 : scratch = sc' := by simpa using congrArg (fun l => l.getD 2 0) harg
    exact ⟨h1, h2⟩
  subst ha hsc
  exact ⟨body, o, st', c, L', hbody, hrun, hval, hperm, hpw, hLat', hfr,
    by dsimp only [mergeSortContract] at hcost; exact hcost⟩

lemma revUFMemAt_init_zero {mem : ℕ → ℕ} {ufBase vCap : ℕ} {isNew : ℕ → Bool}
    (hIs : ∀ v < vCap, mem (ufBase + v) = if isNew v then 1 else 0)
    (hz : ∀ a, ufBase + vCap ≤ a → a < ufBase + ufScratchSize vCap → mem a = 0) :
    RevUFMemAt mem ufBase vCap isNew RevUFState.zero [] := by
  have hsz : ufScratchSize vCap = 6 * vCap + 1 := rfl
  refine ⟨hIs, fun v hv => ⟨hz _ (by dsimp [ufParBase]; omega) (by dsimp [ufParBase]; omega),
      hz _ (by dsimp [ufSzBase]; omega) (by dsimp [ufSzBase]; omega),
      hz _ (by dsimp [ufMinFBase]; omega) (by dsimp [ufMinFBase]; omega),
      hz _ (by dsimp [ufOldRBase]; omega) (by dsimp [ufOldRBase]; omega)⟩,
    List.nodup_nil, fun _ h => by simp at h, fun _ _ => by simp [RevUFState.zero],
    fun _ _ _ => by simp [RevUFState.zero],
    hz _ (by dsimp [ufActLenAddr]; omega) (by dsimp [ufActLenAddr]; omega),
    fun _ h => by simp at h,
    fun i _ hi => hz _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase]; omega), by simp⟩

lemma log_2t_add2_le {t m0 : ℕ} (ht : t ≤ m0) :
    Nat.log 2 (2 * t + 2) ≤ Nat.log 2 (m0 + 2) + 1 := by
  have h1 : 2 * t + 2 ≤ (m0 + 2) * 2 := by omega
  have h2 : Nat.log 2 (2 * t + 2) ≤ Nat.log 2 ((m0 + 2) * 2) := Nat.log_mono_right h1
  rw [Nat.log_mul_base (by decide) (by omega : m0 + 2 ≠ 0)] at h2
  exact h2

lemma compEmit_R_old_sep {G : MGraph} {RF0 : RootedForest} {u : Update}
    (hRF0 : RF0.IsRootedSpanningForestOf G) (hu_val : G.UpdateIsValid u) :
    ∀ r ∈ RF0.R, ∀ s ∈ RF0.R, (forestAfterInput RF0.F u).Connected r s → r = s := by
  intro r hr s hs ⟨P, hP⟩
  have hconn0 : RF0.F.Connected r s := by
    cases u with
    | insert _ _ _ => exact ⟨P, hP⟩
    | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph RF0.F e) ⟨P, hP⟩
    | split v v' At Ah =>
      have hv_not : v' ∉ RF0.F.V := by rw [hRF0.2.1]; exact hu_val.2.1
      have hr_ne : r ≠ v' := fun h => hv_not (h ▸ (hRF0.2.1.symm ▸ hRF0.2.2.1 hr))
      have hs_ne : s ≠ v' := fun h => hv_not (h ▸ (hRF0.2.1.symm ▸ hRF0.2.2.1 hs))
      let proj : ℕ → ℕ := fun z => if z = v' then v else z
      have hlift : ∀ {a b : ℕ} {Q : List (ℕ × Bool)},
          (RF0.F.applyUpdate (.split v v' At Ah)).IsWalk a b Q → RF0.F.IsWalk (proj a) (proj b) Q := by
        intro a b Q hQ; induction hQ with
        | nil z => exact .nil (proj z)
        | @cons a b z rest he hsW _ ih =>
          have htne : RF0.F.tail z.1 ≠ v' := fun h => hv_not (h ▸ (hRF0.1.1 z.1 he).1)
          have hhne : RF0.F.head z.1 ≠ v' := fun h => hv_not (h ▸ (hRF0.1.1 z.1 he).2)
          have hsrc : RF0.F.src z = proj a := by
            rw [← hsW]; rcases z with ⟨e, _ | _⟩ <;>
              simp only [MGraph.src, MGraph.applyUpdate, proj] at htne hhne ⊢ <;> split_ifs with h1 h2 <;> simp_all
          have hdst : RF0.F.dst z = proj ((RF0.F.applyUpdate (.split v v' At Ah)).dst z) := by
            rcases z with ⟨e, _ | _⟩ <;>
              simp only [MGraph.dst, MGraph.applyUpdate, proj] at htne hhne ⊢ <;> split_ifs with h1 h2 <;> simp_all
          exact .cons he hsrc (hdst ▸ ih)
      exact ⟨P, by simpa [proj, hr_ne, hs_ne] using hlift hP⟩
  obtain ⟨r', _, huniq⟩ := hRF0.2.2.2.1 r (hRF0.2.2.1 hr)
  exact (huniq r ⟨hr, ⟨[], .nil r⟩⟩).trans (huniq s ⟨hs, hconn0⟩).symm

lemma compEmit_L0_R {cs : CompLSFState} {u : Update}
    (hRF0 : cs.RF.IsRootedSpanningForestOf cs.G) :
    (inputMid cs u).F.R = canonRoots (forestAfterInput cs.RF.F u) cs.RF.R (compLSFStepSingle cs u).RF.R := by
  cases u with
  | insert _ _ _ => exact (canonRoots_self_of_rsf hRF0).symm
  | delete e =>
    by_cases he : e ∈ cs.RF.F.E
    · simp [inputMid, forestAfterInput, he]
    · have heq : eraseForestEdge cs.RF.F e = cs.RF.F := by
        simp only [eraseForestEdge, Finset.erase_eq_of_notMem he]
      simp only [inputMid, he, ↓reduceIte, forestAfterInput, heq]
      exact (canonRoots_self_of_rsf hRF0).symm
  | split _ _ _ _ => rfl

lemma compEmit_F_mid_subRF' {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {u : Update}
    (hI0 : CompLSFInv C_lsst ℓ₀ cs) (hu_val : cs.G.UpdateIsValid u) :
    (forestAfterInput cs.RF.F u).IsSubgraph (compLSFStepSingle cs u).RF.F := by
  have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) :=
    compLSFBatch_inv (U := [u]) hI0 ⟨hu_val, trivial⟩
  have hRF0 := compLSF_RF_isRSF hI0
  have hRF' := compLSF_RF_isRSF hI1
  have hdec := compLSFBatch_decremental (U := [u]) hI0 ⟨hu_val, trivial⟩
  have hEsub : (compLSFStepSingle cs u).RF.F.E ⊆ (forestAfterInput cs.RF.F u).E := by
    cases u with
    | insert _ _ _ => exact hdec.1
    | delete e =>
      intro f hf
      have hne : f ≠ e := fun h => by
        have := (compLSF_F_edge_orig hI1 hf).1
        rw [h] at this; simp [compLSFStepSingle, MGraph.applyUpdate] at this
      exact Finset.mem_erase.mpr ⟨hne, hdec.1 hf⟩
    | split _ _ _ _ => exact hdec.1
  have hVm : (forestAfterInput cs.RF.F u).V = (compLSFStepSingle cs u).G.V := by
    have hV0 := hRF0.2.1
    cases u <;> simp [forestAfterInput, eraseForestEdge, compLSFStepSingle, MGraph.applyUpdate, hV0]
  refine ⟨hRF'.2.1.trans hVm.symm ▸ Finset.Subset.rfl, hEsub, fun f hf => ?_⟩
  have ho1 := compLSF_F_edge_orig hI1 hf
  cases u with
  | insert e _ _ =>
    have ho0 := compLSF_F_edge_orig hI0 (hdec.1 hf)
    have hne : f ≠ e := fun h => hu_val.1 (h ▸ ho0.1)
    rw [ho1.2.2.2.1, ho1.2.2.2.2]
    simp only [forestAfterInput, compLSFStepSingle, MGraph.applyUpdate, Function.update_of_ne hne,
      ho0.2.2.2.1, ho0.2.2.2.2, and_self]
  | delete _ =>
    have ho0 := compLSF_F_edge_orig hI0 (hdec.1 hf)
    rw [ho1.2.2.2.1, ho1.2.2.2.2]
    simp only [forestAfterInput, eraseForestEdge, compLSFStepSingle, MGraph.applyUpdate,
      ho0.2.2.2.1, ho0.2.2.2.2, and_self]
  | split _ _ _ _ =>
    have ho0 := compLSF_F_edge_orig hI0 (hdec.1 hf)
    rw [ho1.2.2.2.1, ho1.2.2.2.2]
    simp only [forestAfterInput, compLSFStepSingle, MGraph.applyUpdate, ho0.2.2.2.1, ho0.2.2.2.2, and_self]

/-! ## 3. Phase 1 verification (`compEmitPhase1_runs`) -/

set_option maxHeartbeats 1200000 in
/-- Verifies `compEmitPhase1Stmt`: scans `cuts1`, marks `y0` when `1 < tag`, sorts `dBuf`,
loads `spCnt`, and executes `compRevLoopStmt` to emit all released-edge split entries. -/
theorem compEmitPhase1_runs {W : LSFWindowImpl}
    {w k b bSort bEndRoots bUFInitFind bUFPairUnion
      rootsPtr fDelPtr oldC tag delE x0 y0 spBufJ spCntAddr ufBase spCnt : ℕ}
    {S : CompLSFFamily k} {x1 : CompLSFMeta k} {touched1 : List ℕ} {u : Update}
    {cuts1 : List (ℕ × ℕ)} {p : Program} {ω : ℕ → Bool} {st : State} (j : Fin k)
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpEndRoots : p.procs[bEndRoots]? = some compEdgeEndRootsProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep0 : ∃ ℓ₀, CompLSFInv W.C_lsst ℓ₀ (S j))
    (hu_val : (S j).G.UpdateIsValid u)
    (hrep1 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 st.mem)
    (hend_le_rts : x1.endAddr ≤ rootsPtr)
    (hrts_le_fdel : rootsPtr + oldC + cuts1.length ≤ fDelPtr)
    (hfdel_le_sp : fDelPtr + oldC + cuts1.length ≤ spBufJ)
    (hsp_le_cnt : spBufJ + 4 * x1.vCap ≤ spCntAddr)
    (hcnt_lt_uf : spCntAddr + 1 ≤ ufBase)
    (huf_w : ufBase + ufEmitScratchSize x1.vCap < 2 ^ w)
    (hargs_w : tag < 2 ^ w ∧ delE < 2 ^ w ∧ x0 < 2 ^ w ∧ y0 < 2 ^ w)
    (hcut_ndE : (cuts1.map Prod.fst).Nodup)
    (hcut_setE : (cuts1.map Prod.fst).toFinset = (S j).RF.F.E \ (compLSFStepSingle (S j) u).RF.F.E)
    (hcut_setR : (cuts1.map Prod.snd).toFinset ∪
        (match u with | .split _ v' _ _ => {v'} | _ => ∅) =
      (compLSFStepSingle (S j) u).RF.R \ (S j).RF.R)
    (hcut_r_lt : ∀ q ∈ cuts1, q.2 < x1.vCap)
    (hcut_m : ∀ i (hi : i < cuts1.length),
      st.mem (rootsPtr + (oldC + i)) = cuts1[i].2 ∧ st.mem (fDelPtr + (oldC + i)) = cuts1[i].1)
    (htag_spec : match u with
      | .insert _ _ _ => tag = 0
      | .delete e => tag = 1 ∧ delE = e ∧
          (e ∈ (S j).RF.F.E → x0 = (S j).G.tail e ∧ y0 = (S j).G.head e)
      | .split v v' _ _ => 2 ≤ tag ∧ x0 = v ∧ y0 = v')
    (hspCnt_m : st.mem spCntAddr = spCnt)
    (hspCnt_bd : spCnt + (canonStepSplits (S j) u).length ≤ x1.vCap)
    (huf_zero : ∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → st.mem a = 0)
    (hregs : st.regs 0 = b ∧ st.regs 1 = j.1 ∧ st.regs 2 = rootsPtr ∧ st.regs 3 = fDelPtr ∧
      st.regs 4 = oldC ∧ st.regs 5 = oldC + cuts1.length ∧ st.regs 6 = tag ∧ st.regs 7 = delE ∧
      st.regs 8 = x0 ∧ st.regs 9 = y0 ∧ st.regs 10 = spBufJ ∧ st.regs 11 = spCntAddr ∧
      st.regs 12 = ufBase ∧ st.regs 13 = x1.vCap) :
    let cs1 := compLSFStepSingle (S j) u
    let RF0 := (S j).RF
    let RF' := cs1.RF
    let F_mid := forestAfterInput RF0.F u
    let D_sorted := (F_mid.E \ RF'.F.E).sort (· ≤ ·)
    let t := D_sorted.length
    let hasInp := (inputSplitEntries (S j) u).length
    let isNew : ℕ → Bool := fun v => decide (v ∈ RF'.R \ RF0.R)
    ∃ s14 c1 U_end act_end,
      Runs w p ω (compEmitPhase1Stmt (bSort + sortIdxMergeSort) bEndRoots bUFInitFind bUFPairUnion)
        st .normal s14 c1 ∧
      (∀ r < 14, s14.regs r = st.regs r) ∧
      s14.regs 15 = ufBase + 6 * x1.vCap + 1 ∧
      s14.regs 16 = ufBase + 7 * x1.vCap + 1 ∧
      s14.regs 17 = ufBase + 8 * x1.vCap + 1 ∧
      s14.regs 18 = t ∧ s14.regs 19 = hasInp ∧ s14.regs 24 = spCnt ∧
      RevUFInv F_mid RF' RF0.R U_end ∧
      RevUFMemAt s14.mem ufBase x1.vCap isNew U_end act_end ∧
      act_end.length ≤ 2 * t ∧
      (∀ idx (hidx : idx < D_sorted.length),
        let e := (releasesSplitEntries RF'.R (inputMid (S j) u) D_sorted)[idx]'(by rw [releasesSplitEntries_length]; exact hidx)
        s14.mem (spBufJ + 4 * (spCnt + hasInp + idx)) = (if e.isRelease then 1 else 0) ∧
        s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 1) = e.edge ∧
        s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 2) = e.kept ∧
        s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 3) = e.fresh) ∧
      (∀ a, (a < spBufJ + 4 * (spCnt + hasInp) ∨ spBufJ + 4 * (spCnt + hasInp + t) ≤ a) →
        (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) → s14.mem a = st.mem a) ∧
      (∀ a, ufBase + 6 * x1.vCap + 1 + t ≤ a → a < ufBase + 7 * x1.vCap + 1 → s14.mem a = 0) ∧
      (∀ a, ufBase + 7 * x1.vCap + 1 + t ≤ a → a < ufBase + 8 * x1.vCap + 1 → s14.mem a = 0) ∧
      c1 ≤ 55 * cuts1.length + (if t = 0 then 10 else 200 * t * (Nat.log 2 (t + 1) + 1) + 65) +
        t * (40 * Nat.log 2 (2 * t + 2) + 820) + 120 := by
  classical
  intro cs1 RF0 RF' F_mid D_sorted t hasInp isNew
  obtain ⟨ℓ₀, hIj⟩ := hrep0
  have hI1 : CompLSFInv W.C_lsst ℓ₀ cs1 := compLSFBatch_inv (U := [u]) hIj ⟨hu_val, trivial⟩
  have hRF0 : RF0.IsRootedSpanningForestOf (S j).G := compLSF_RF_isRSF hIj
  have hRF' : RF'.IsRootedSpanningForestOf cs1.G := compLSF_RF_isRSF hI1
  have hdec := compLSFBatch_decremental (U := [u]) hIj ⟨hu_val, trivial⟩
  have hR_old_sub : RF0.R ⊆ RF'.R := hdec.2
  have hrep1_orig := hrep1
  obtain ⟨hk, _, _, _, _, _, _, _, _, hTE1, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
  have hG_j := (hBr1 j).2.2.1
  have hR_lt : ∀ r ∈ RF'.R, r < x1.vCap := fun r hr => hT1.hVlt r (hG_j ▸ hRF'.2.2.1 hr)
  -- Key pure identities for `D_raw`, `hasInp`, `t`, `cuts1.length`
  set D_raw := if tag = 1 then (cuts1.map Prod.fst).filter (· ≠ delE) else cuts1.map Prod.fst
  set hasInp0 := if tag = 1 ∧ delE ∈ cuts1.map Prod.fst then 1 else 0
  have hD_raw_nd : D_raw.Nodup := by
    dsimp only [D_raw]; split_ifs
    · exact hcut_ndE.filter _
    · exact hcut_ndE
  have hD_raw_mem : ∀ e, e ∈ D_raw ↔ e ∈ F_mid.E \ RF'.F.E := fun e => by
    have hcm : e ∈ cuts1.map Prod.fst ↔ e ∈ RF0.F.E \ RF'.F.E := by
      rw [← List.mem_toFinset, hcut_setE]
    cases u with
    | insert _ _ _ => simp [D_raw, htag_spec, hcm, F_mid, forestAfterInput]
    | delete e0 =>
      have ⟨ht1, hde, _⟩ := htag_spec
      simp only [D_raw, ht1, ↓reduceIte, List.mem_filter, hcm, hde, decide_eq_true_eq,
        F_mid, forestAfterInput, eraseForestEdge, Finset.mem_sdiff, Finset.mem_erase]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h3, h1⟩, h2⟩, fun ⟨⟨h3, h1⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    | split _ _ _ _ =>
      have ht2 := htag_spec.1
      simp [D_raw, show tag ≠ 1 by omega, hcm, F_mid, forestAfterInput, MGraph.applyUpdate]
  have hD_raw_len : D_raw.length = t := by
    dsimp only [t, D_sorted]; rw [Finset.length_sort, ← List.toFinset_card_of_nodup hD_raw_nd]
    congr 1; ext e; rw [List.mem_toFinset, hD_raw_mem]
  have hhasInp_eq : (if 1 < tag then 1 else hasInp0) = hasInp := by
    dsimp only [hasInp]
    cases u with
    | insert _ _ _ => simp [hasInp0, htag_spec, inputSplitEntries]
    | delete e0 =>
      have ⟨ht1, hde, _⟩ := htag_spec
      have he_not_RF' : e0 ∉ RF'.F.E := fun h => by
        have hG := (compLSF_F_edge_orig hI1 h).1
        simp [cs1, compLSFStepSingle, MGraph.applyUpdate] at hG
      have hmem_iff : e0 ∈ cuts1.map Prod.fst ↔ e0 ∈ (S j).RF.F.E := by
        rw [← List.mem_toFinset, hcut_setE, Finset.mem_sdiff]
        exact ⟨fun h => h.1, fun h => ⟨h, he_not_RF'⟩⟩
      by_cases he : e0 ∈ (S j).RF.F.E <;>
        simp [hasInp0, ht1, hde, hmem_iff, he, inputSplitEntries]
    | split _ _ _ _ =>
      have ht2 := htag_spec.1
      simp [show 1 < tag by omega, inputSplitEntries]
  have hstep_len : (canonStepSplits (S j) u).length = hasInp + t := by
    simp only [canonStepSplits, List.length_append, releasesSplitEntries_length]
    rfl
  have hcuts1_le_vCap : cuts1.length ≤ x1.vCap := by
    cases u with
    | insert _ _ _ =>
      have : D_raw.length = cuts1.length := by simp [D_raw, htag_spec]
      omega
    | delete e0 =>
      have ⟨ht1, hde, _⟩ := htag_spec
      by_cases he : e0 ∈ cuts1.map Prod.fst
      · have hhi : hasInp = 1 := by rw [← hhasInp_eq]; simp [hasInp0, ht1, hde, he]
        have hsub : (cuts1.map Prod.fst).toFinset ⊆ insert e0 (F_mid.E \ RF'.F.E) := by
          intro e hm; rw [hcut_setE, Finset.mem_sdiff] at hm
          by_cases heq : e = e0
          · exact Finset.mem_insert.mpr (Or.inl heq)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr
              ⟨Finset.mem_erase.mpr ⟨heq, hm.1⟩, hm.2⟩))
        have hc := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hcut_ndE, List.length_map] at hc
        have := le_trans hc (Finset.card_insert_le _ _)
        have htl : t = (F_mid.E \ RF'.F.E).card := Finset.length_sort _
        omega
      · have : D_raw = cuts1.map Prod.fst := by
          simp only [D_raw, ht1, ↓reduceIte]
          exact List.filter_eq_self.mpr fun x hx => by
            simp only [ne_eq, decide_eq_true_eq]
            intro h; rw [h, hde] at hx; exact he hx
        have : D_raw.length = cuts1.length := by rw [this, List.length_map]
        omega
    | split _ _ _ _ =>
      have ht2 := htag_spec.1
      have : D_raw.length = cuts1.length := by simp [D_raw, show tag ≠ 1 by omega]
      omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have huf_sz : ufEmitScratchSize x1.vCap = 8 * x1.vCap + 3 := rfl
  have huf_scr : ufScratchSize x1.vCap = 6 * x1.vCap + 1 := rfl
  set dBuf := ufBase + 6 * x1.vCap + 1
  set sortScr := dBuf + x1.vCap
  set tmp2 := sortScr + x1.vCap
  have ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13⟩ := hregs
  let s3 : State := { st with regs := Function.update st.regs 15 dBuf }
  let s4 : State := { s3 with regs := Function.update s3.regs 16 sortScr }
  let s5 : State := { s4 with regs := Function.update s4.regs 17 tmp2 }
  let s6 : State := { s5 with regs := Function.update s5.regs 18 0 }
  let s7 : State := { s6 with regs := Function.update s6.regs 19 0 }
  let s8 : State := { s7 with regs := Function.update s7.regs 20 oldC }
  have hs3 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 6) (.reg 13))) (.const 1)))
      st .normal s3 8 :=
    runs_assign_iff.mpr ⟨dBuf, by
      simp [Expr.eval, BinOp.eval, hr12, hr13, hw1, hw6, dBuf,
        show 6 * x1.vCap < 2 ^ w by omega, show ufBase + 6 * x1.vCap < 2 ^ w by omega,
        show dBuf < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hs4 : Runs w p ω (.assign 16 (.bin .add (.reg 15) (.reg 13))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨sortScr, by
      simp [s3, Expr.eval, BinOp.eval, hr13, sortScr, show sortScr < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hs5 : Runs w p ω (.assign 17 (.bin .add (.reg 16) (.reg 13))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨tmp2, by
      simp [s4, s3, Expr.eval, BinOp.eval, hr13, tmp2, show tmp2 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hs6 : Runs w p ω (.assign 18 (.const 0)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hs7 : Runs w p ω (.assign 19 (.const 0)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hs8 : Runs w p ω (.assign 20 (.reg 4)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨oldC, by simp [s7, s6, s5, s4, s3, hr4, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  -- Loop 1: `compScanCutsStmt`
  obtain ⟨s9, cSc, hs9, hr9_o, hr9_18, hr9_19, hLA9, hIs9, hfr9, hcSc⟩ :=
    compScanCuts_runs (tag := tag) (delE := delE) (ufBase := ufBase) (dBuf := dBuf)
      (p := p) (ω := ω) (st := s8) (cuts1 := cuts1) (vCap := x1.vCap)
      hw16 (by omega) (by omega) (by omega) (by dsimp [dBuf]; omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by dsimp [dBuf]; omega)) (Or.inl (by dsimp [dBuf]; omega))
      (by dsimp [dBuf]; omega) hcut_r_lt hcut_m
      (by simp [s8, s7, s6, s5, s4, s3, hr2]) (by simp [s8, s7, s6, s5, s4, s3, hr3])
      (by simp [s8, s7, s6, s5, s4, s3, hr5]) (by simp [s8, s7, s6, s5, s4, s3, hr6])
      (by simp [s8, s7, s6, s5, s4, s3, hr7]) (by simp [s8, s7, s6, s5, s4, s3, hr12])
      (by simp [s8, s7, s6, s5, s4, s3]) (by simp [s8, s7, s6]) (by simp [s8, s7]) (by simp [s8])
  -- Conditional split mark
  have hspMark : ∃ s10 cSpM,
      Runs w p ω
        (.cond (.bin .lt (.const 1) (.reg 6))
          (.assign 19 (.const 1) ;; .store (.bin .add (.reg 12) (.reg 9)) (.const 1)) .nop)
        s9 .normal s10 cSpM ∧
      (∀ r < 19, s10.regs r = s9.regs r) ∧ s10.regs 19 = hasInp ∧
      ListAt s10.mem dBuf D_raw ∧
      (∀ v < x1.vCap, s10.mem (ufBase + v) = if isNew v then 1 else 0) ∧
      (∀ a, (a < ufBase ∨ ufBase + x1.vCap ≤ a) → (a < dBuf ∨ dBuf + t ≤ a) → s10.mem a = st.mem a) ∧
      cSpM ≤ 15 := by
    have hIs_eq_split : ∀ (v : ℕ),
        (v ∈ cuts1.map Prod.snd ∨ (1 < tag ∧ v = y0)) ↔ v ∈ RF'.R \ RF0.R := fun v => by
      rw [← hcut_setR, Finset.mem_union, List.mem_toFinset]
      cases u with
      | insert _ _ _ => simp [htag_spec]
      | delete _ => simp [htag_spec.1]
      | split _ v' _ _ =>
        have ⟨ht2, _, hy⟩ := htag_spec
        simp [show 1 < tag by omega, hy]
    by_cases ht1 : 1 < tag
    · have hy0_lt : y0 < x1.vCap := by
        cases u with
        | insert _ _ _ => have := htag_spec; omega
        | delete _ => have := htag_spec.1; omega
        | split _ v' _ _ =>
          rw [htag_spec.2.2]
          exact hT1.hVlt v' (hG_j ▸ by simp [compLSFStepSingle, MGraph.applyUpdate])
      let s9a : State := { s9 with regs := Function.update s9.regs 19 1 }
      let s10 : State := { s9a with mem := Function.update s9a.mem (ufBase + y0) 1 }
      have ha : Runs w p ω (.assign 19 (.const 1)) s9 .normal s9a 2 :=
        runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
      have hb : Runs w p ω (.store (.bin .add (.reg 12) (.reg 9)) (.const 1)) s9a .normal s10 5 :=
        runs_store_iff.mpr ⟨ufBase + y0, 1,
          by simp [s9a, Expr.eval, BinOp.eval, hr9_o 12 (by omega), hr9_o 9 (by omega),
            s8, s7, s6, s5, s4, s3, hr12, hr9, show ufBase + y0 < 2 ^ w by omega],
          by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
      have hseq := runs_seq_iff.mpr (Or.inr ⟨s9a, 2, 5, ha, hb, rfl⟩)
      refine ⟨s10, 12, runs_cond_iff.mpr ⟨1, 8,
        by simp [Expr.eval, BinOp.eval, hr9_o 6 (by omega), s8, s7, s6, s5, s4, s3, hr6, hw1, ht1],
        by simp only [one_ne_zero, ↓reduceIte]; exact hseq, by simp [Expr.size]⟩,
        fun r hr => by simp [s10, s9a, show r ≠ 19 by omega], by rw [← hhasInp_eq]; simp [s10, s9a, ht1],
        fun q hq => by dsimp only [s10, s9a]; rw [Function.update_of_ne (by omega)]; exact hLA9 q hq,
        fun v hv => by
          dsimp only [s10, s9a, isNew]
          by_cases hvy : v = y0
          · subst hvy; rw [Function.update_self]
            have hm : v ∈ RF'.R \ RF0.R := (hIs_eq_split v).mp (Or.inr ⟨ht1, rfl⟩)
            simp [hm]
          · rw [Function.update_of_ne (by omega), hIs9 v hv, huf_zero (ufBase + v) (by omega) (by omega)]
            by_cases hc : v ∈ cuts1.map Prod.snd
            · have hm : v ∈ RF'.R \ RF0.R := (hIs_eq_split v).mp (Or.inl hc); simp [hc, hm]
            · have hm : v ∉ RF'.R \ RF0.R := fun h => by
                rcases (hIs_eq_split v).mpr h with h1 | ⟨_, h2⟩
                · exact hc h1
                · exact hvy h2
              simp [hc, hm],
        fun a ha1 ha2 => by
          dsimp only [s10, s9a]; rw [Function.update_of_ne (by omega)]
          exact hfr9 a ha1 (hD_raw_len ▸ ha2), by omega⟩
    · refine ⟨s9, 5, runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, hr9_o 6 (by omega), s8, s7, s6, s5, s4, s3, hr6, hw1, ht1],
        by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        fun _ _ => rfl, by rw [← hhasInp_eq]; simp only [ht1, ↓reduceIte, hr9_19, hasInp0], hLA9,
        fun v hv => by
          rw [hIs9 v hv, huf_zero (ufBase + v) (by omega) (by omega)]
          dsimp only [isNew]
          by_cases hc : v ∈ cuts1.map Prod.snd
          · have hm : v ∈ RF'.R \ RF0.R := (hIs_eq_split v).mp (Or.inl hc); simp [hc, hm]
          · have hm : v ∉ RF'.R \ RF0.R := fun h => by
              rcases (hIs_eq_split v).mpr h with h1 | ⟨h2, _⟩
              · exact hc h1
              · exact ht1 h2
            simp [hc, hm],
        fun a ha1 ha2 => hfr9 a ha1 (hD_raw_len ▸ ha2), by omega⟩
  obtain ⟨s10, cSpM, hs10, hr10_o, hr10_19, hLA10, hIs10, hfr10, hcSpM⟩ := hspMark
  -- Conditional merge sort
  have hsort_branch : ∃ s11 cSort,
      Runs w p ω
        (.cond (.bin .lt (.const 0) (.reg 18))
          (.call 23 (bSort + sortIdxMergeSort) [.reg 15, .reg 18, .reg 16]) .nop)
        s10 .normal s11 cSort ∧
      (∀ r < 20, s11.regs r = s10.regs r) ∧
      ListAt s11.mem dBuf D_sorted ∧
      (∀ a, (a < dBuf ∨ dBuf + t ≤ a) → (a < sortScr ∨ sortScr + t ≤ a) → s11.mem a = s10.mem a) ∧
      cSort ≤ (if t = 0 then 10 else 200 * t * (Nat.log 2 (t + 1) + 1) + 65) := by
    have hr10_18 : s10.regs 18 = t := (hr10_o 18 (by omega)).trans (hr9_18.trans hD_raw_len)
    have hr10_15 : s10.regs 15 = dBuf := by
      rw [hr10_o 15 (by omega), hr9_o 15 (by omega)]; simp [s8, s7, s6, s5, s4, s3]
    have hr10_16 : s10.regs 16 = sortScr := by
      rw [hr10_o 16 (by omega), hr9_o 16 (by omega)]; simp [s8, s7, s6, s5, s4]
    by_cases ht0 : t = 0
    · have hDs0 : D_sorted = [] := List.eq_nil_of_length_eq_zero ht0
      refine ⟨s10, 5, runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, hr10_18, ht0, hw0'],
        by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        fun _ _ => rfl, by rw [hDs0]; intro q hq; simp at hq, fun _ _ _ => rfl, by simp [ht0]⟩
    · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
      have hDw : ∀ e ∈ D_raw, e < 2 ^ w := fun e he => by
        have he_mid := (Finset.mem_sdiff.mp ((hD_raw_mem e).mp he)).1
        have he_orig : e ∈ RF0.F.E := by
          cases u with
          | insert _ _ _ => exact he_mid
          | delete _ => exact (Finset.mem_erase.mp he_mid).2
          | split _ _ _ _ => exact he_mid
        have heG1 : e ∈ cs1.G.E := by
          have ho := (compLSF_F_edge_orig hIj he_orig).1
          cases u with
          | insert _ _ _ => exact Finset.mem_insert_of_mem ho
          | delete _ => exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he_mid).1, ho⟩
          | split _ _ _ _ => exact ho
        have helt := hT1.hElt e (hG_j ▸ heG1)
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostSize, compHdrSize] at hTE1
        omega
      obtain ⟨bodyS, oS, stS, cS, L', hbodyS, hrunS, hoS, hpermS, hpwS, hLA', hfrS, hcS⟩ :=
        compEmitMergeSort_call hpSort (a := dBuf) (scratch := sortScr) (L := D_raw)
          (mem := s10.mem) (pos := s10.pos) (ω := ω) hw16 (by omega) (by omega)
          (Or.inl (by dsimp [sortScr]; omega)) hLA10 hDw
      have hL'_eq : L' = D_sorted :=
        list_eq_finset_sort (hpermS.nodup_iff.mpr hD_raw_nd) hpwS
          fun e => (hpermS.mem_iff).trans (hD_raw_mem e)
      rw [hL'_eq] at hLA'
      let s11 : State := { s10 with regs := Function.update s10.regs 23 0, mem := stS.mem, pos := stS.pos }
      have hcallS : Runs w p ω (.call 23 (bSort + sortIdxMergeSort) [.reg 15, .reg 18, .reg 16])
          s10 .normal s11 (cS + 4) :=
        runs_call_iff.mpr ⟨[dBuf, D_raw.length, sortScr], bodyS, oS, stS, cS,
          by simp [evalArgs, Expr.eval, hr10_15, hr10_18, hr10_16, hD_raw_len],
          hbodyS, hrunS, rfl, by simp [s11, hoS], by simp [argsSize, Expr.size]; omega⟩
      refine ⟨s11, cS + 8, runs_cond_iff.mpr ⟨1, cS + 4,
        by simp [Expr.eval, BinOp.eval, hr10_18, ht_pos, hw0, hw0'],
        by simp only [one_ne_zero, ↓reduceIte]; exact hcallS, by simp [Expr.size]; omega⟩,
        fun r hr => by simp [s11, show r ≠ 23 by omega], hLA',
        fun a ha1 ha2 => hfrS a (hD_raw_len.symm ▸ ha1) (hD_raw_len.symm ▸ ha2),
        by rw [hD_raw_len] at hcS; simp [ht0]; omega⟩
  obtain ⟨s11, cSort, hs11, hr11_o, hLA11, hfr11, hcSort⟩ := hsort_branch
  -- Load `spCnt`, set `r20 := t`, run `compRevLoopStmt`
  have hr11_18 : s11.regs 18 = t :=
    (hr11_o 18 (by omega)).trans ((hr10_o 18 (by omega)).trans (hr9_18.trans hD_raw_len))
  have hspCnt_s11 : s11.mem spCntAddr = spCnt := by
    rw [hfr11 spCntAddr (Or.inl (by omega)) (Or.inl (by omega)),
        hfr10 spCntAddr (Or.inl (by omega)) (Or.inl (by omega)), hspCnt_m]
  let s12 : State := { s11 with regs := Function.update s11.regs 24 spCnt }
  let s13 : State := { s12 with regs := Function.update s12.regs 20 t }
  have hs12 : Runs w p ω (.assign 24 (.load (.reg 11))) s11 .normal s12 3 :=
    runs_assign_iff.mpr ⟨spCnt, Expr.eval_load_of_eq (by
      simp [Expr.eval, hr11_o 11 (by omega), hr10_o 11 (by omega), hr9_o 11 (by omega),
        s8, s7, s6, s5, s4, s3, hr11]) hspCnt_s11, rfl, rfl, by simp [Expr.size]⟩
  have hs13 : Runs w p ω (.assign 20 (.reg 18)) s12 .normal s13 2 :=
    runs_assign_iff.mpr ⟨t, by simp [s12, Expr.eval, hr11_18], rfl, rfl, by simp [Expr.size]⟩
  have hrep1_s13 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 s13.mem :=
    compLSFRepDirty_of_agree hrep1_orig fun a _ ha2 =>
      (hfr11 a (Or.inl (by omega)) (Or.inl (by omega))).trans
        (hfr10 a (Or.inl (by omega)) (Or.inl (by omega)))
  have hMem0_s13 : RevUFMemAt s13.mem ufBase x1.vCap isNew RevUFState.zero [] :=
    revUFMemAt_init_zero
      (fun v hv => (hfr11 _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hIs10 v hv))
      (fun a ha1 ha2 => (hfr11 a (Or.inl (by omega)) (Or.inl (by omega))).trans
        ((hfr10 a (Or.inr (by omega)) (Or.inl (by omega))).trans (huf_zero a (by omega) (by omega))))
  have hsp_le_uf' : spBufJ + 4 * (spCnt + hasInp + D_sorted.length) ≤ ufBase := by
    have : D_sorted.length = t := rfl; omega
  obtain ⟨s14, cRev, U_end, act_end, hs14, hr14_o, hr14_24, hU_end, hMem_end, hact_end, hrels14, hfr14, hcRev⟩ :=
    compRevLoop_runs (bEndRoots := bEndRoots) (bUFInitFind := bUFInitFind)
      (bUFPairUnion := bUFPairUnion) (spBufJ := spBufJ) (ufBase := ufBase) (dBuf := dBuf)
      (tmp2 := tmp2) (spCnt := spCnt) (hasInp := hasInp) (R_old := RF0.R) (isNew := isNew)
      (p := p) (ω := ω) (st := s13) j hpEndRoots hpInitFind hpPairUnion hw16 ⟨ℓ₀, hIj⟩ hu_val
      hrep1_s13 (by omega) hsp_le_uf' (by dsimp [dBuf]; omega) (by dsimp [tmp2, sortScr]; omega)
      (by dsimp [tmp2, sortScr, dBuf]; omega) rfl hLA11 hR_old_sub (compEmit_R_old_sep hRF0 hu_val)
      (compEmit_L0_R hRF0)
      (fun r hr => by
        simp only [isNew, decide_eq_false_iff_not, Finset.mem_sdiff]
        exact ⟨fun h => by_contra fun hn => h ⟨hr, hn⟩, fun h ⟨_, hn⟩ => hn h⟩)
      hMem0_s13
      (by simp [s13, s12, hr11_o 0 (by omega), hr10_o 0 (by omega), hr9_o 0 (by omega), s8, s7, s6, s5, s4, s3, hr0])
      (by simp [s13, s12, hr11_o 1 (by omega), hr10_o 1 (by omega), hr9_o 1 (by omega), s8, s7, s6, s5, s4, s3, hr1])
      (by simp [s13, s12, hr11_o 10 (by omega), hr10_o 10 (by omega), hr9_o 10 (by omega), s8, s7, s6, s5, s4, s3, hr10])
      (by simp [s13, s12, hr11_o 12 (by omega), hr10_o 12 (by omega), hr9_o 12 (by omega), s8, s7, s6, s5, s4, s3, hr12])
      (by simp [s13, s12, hr11_o 13 (by omega), hr10_o 13 (by omega), hr9_o 13 (by omega), s8, s7, s6, s5, s4, s3, hr13])
      (by simp [s13, s12, hr11_o 15 (by omega), hr10_o 15 (by omega), hr9_o 15 (by omega), s8, s7, s6, s5, s4, s3])
      (by simp [s13, s12, hr11_o 17 (by omega), hr10_o 17 (by omega), hr9_o 17 (by omega), s8, s7, s6, s5])
      (by simp [s13, s12, hr11_o 19 (by omega), hr10_19])
      (by simp only [s13, Function.update_self]; rfl) (by simp [s13, s12])
  have hcRev' : cRev ≤ t * (40 * Nat.log 2 (2 * t + 2) + 820) + 10 := hcRev
  have hfr14' : ∀ a, (a < spBufJ + 4 * (spCnt + hasInp) ∨ spBufJ + 4 * (spCnt + hasInp + t) ≤ a) →
      (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) →
      (a < tmp2 ∨ tmp2 + 2 ≤ a) → s14.mem a = s13.mem a := hfr14
  have hchain : Runs w p ω (compEmitPhase1Stmt (bSort + sortIdxMergeSort) bEndRoots bUFInitFind bUFPairUnion)
      st .normal s14 (8 + (4 + (4 + (2 + (2 + (2 + (cSc + (cSpM + (cSort + (3 + (2 + cRev + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    have k13 := runs_seq_iff.mpr (Or.inr ⟨s13, 2, cRev, hs13, hs14, rfl⟩)
    have k12 := runs_seq_iff.mpr (Or.inr ⟨s12, 3, _, hs12, k13, rfl⟩)
    have k11 := runs_seq_iff.mpr (Or.inr ⟨s11, cSort, _, hs11, k12, rfl⟩)
    have k10 := runs_seq_iff.mpr (Or.inr ⟨s10, cSpM, _, hs10, k11, rfl⟩)
    have k9 := runs_seq_iff.mpr (Or.inr ⟨s9, cSc, _, hs9, k10, rfl⟩)
    have k8 := runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, hs8, k9, rfl⟩)
    have k7 := runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, hs7, k8, rfl⟩)
    have k6 := runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, hs6, k7, rfl⟩)
    have k5 := runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, hs5, k6, rfl⟩)
    have k4 := runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, hs4, k5, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s3, 8, _, hs3, k4, rfl⟩)
  refine ⟨s14, _, U_end, act_end, hchain,
    fun r hr => by
      rw [hr14_o r (by omega)]; dsimp [s13, s12]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          hr11_o r (by omega), hr10_o r (by omega), hr9_o r (by omega)]
      simp [s8, s7, s6, s5, s4, s3, show r ≠ 15 by omega, show r ≠ 16 by omega, show r ≠ 17 by omega,
        show r ≠ 18 by omega, show r ≠ 19 by omega, show r ≠ 20 by omega],
    by rw [hr14_o 15 (by omega)]; simp [s13, s12, hr11_o 15 (by omega), hr10_o 15 (by omega), hr9_o 15 (by omega), s8, s7, s6, s5, s4, s3, dBuf],
    by rw [hr14_o 16 (by omega)]; simp [s13, s12, hr11_o 16 (by omega), hr10_o 16 (by omega), hr9_o 16 (by omega), s8, s7, s6, s5, s4, sortScr, dBuf]; omega,
    by rw [hr14_o 17 (by omega)]; simp [s13, s12, hr11_o 17 (by omega), hr10_o 17 (by omega), hr9_o 17 (by omega), s8, s7, s6, s5, tmp2, sortScr, dBuf]; omega,
    by rw [hr14_o 18 (by omega)]; simp [s13, s12, hr11_18],
    by rw [hr14_o 19 (by omega)]; simp [s13, s12, hr11_o 19 (by omega), hr10_19],
    hr14_24, hU_end, hMem_end, hact_end, hrels14,
    fun a ha1 ha2 =>
      (hfr14' a ha1 (by omega) (by dsimp [tmp2, sortScr, dBuf]; omega)).trans
        ((hfr11 a (by dsimp [dBuf]; omega) (by dsimp [sortScr, dBuf]; omega)).trans
          (hfr10 a (by omega) (by dsimp [dBuf]; omega))),
    fun a ha1 ha2 =>
      (hfr14' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by dsimp [tmp2, sortScr, dBuf]; omega))).trans
        ((hfr11 a (Or.inr (by dsimp [dBuf]; omega)) (Or.inl (by dsimp [sortScr, dBuf]; omega))).trans
          ((hfr10 a (Or.inr (by omega)) (Or.inr (by dsimp [dBuf]; omega))).trans
            (huf_zero a (by omega) (by omega)))),
    fun a ha1 ha2 =>
      (hfr14' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by dsimp [tmp2, sortScr, dBuf]; omega))).trans
        ((hfr11 a (Or.inr (by dsimp [dBuf]; omega)) (Or.inr (by dsimp [sortScr, dBuf]; omega))).trans
          ((hfr10 a (Or.inr (by omega)) (Or.inr (by dsimp [dBuf]; omega))).trans
            (huf_zero a (by omega) (by omega)))),
    by omega⟩

end

end MinCostFlow.SparseCore.Program
