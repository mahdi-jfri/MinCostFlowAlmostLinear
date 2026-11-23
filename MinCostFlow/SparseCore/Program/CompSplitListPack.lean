module

public import MinCostFlow.SparseCore.Program.CompBatchPack
public import MinCostFlow.SparseCore.Program.CompSplitListModel
import WordRAM.Tactic

/-!
# Per-Branch Canonical Split-List Packing (`CompSplitListPack`)

Defines and verifies `compPackSplitsProc (bZero : ℕ)`:
given `[b, ptrBase, midEnd, spCntBase, spBufBase, oldCntBase]`, runs right after
`compPackChangesProc` (invoked with `heap + k` so `[ptrBase + k, ptrBase + 2 * k)` holds
`chgPtr_0..chgPtr_{k-1}` and `[ptrBase + 2 * k, midEnd)` holds the `k` `Read.LSFChangeAt`
payloads):

1. Copies `[ptrBase + k, ptrBase + 2 * k)` down to `[ptrBase, ptrBase + k)`, placing
   `chgPtr_0..chgPtr_{k-1}` at `ptrBase` without moving any payload.
2. Iterates `j = 0 .. k - 1`, storing `spPtr_j = cur` at `ptrBase + k + j`, packing
   `[spCnt_j, entry_0, ..., entry_{spCnt_j - 1}]` at `[cur, cur + 1 + 4 * spCnt_j)` via
   `compCopySliceStmt`, zeroing `spBufBase + 4 * j * vCap` (length `4 * spCnt_j`) via `bZero`
   and clearing `spCntBase + j := 0`.
3. Zeroes `oldCntBase` (length `k`) via `bZero`, leaves `ZeroFrom st'.mem outEnd`, and returns
   `outEnd`.

Total cost is `≤ 180 * (∑ j, (splits j).length) + 150 * k + 80`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Packing procedure -/

/-- `args = [b, ptrBase, midEnd, spCntBase, spBufBase, oldCntBase]`: shifts `chgPtr_0..chgPtr_{k-1}`
down from `ptrBase + k` to `ptrBase`, packs all `k` per-branch `SplitEntriesAt` records starting
at `midEnd`, writes their pointers at `[ptrBase + k, ptrBase + 2 * k)`, zeroes all split-buffer
and `oldCnt` scratch cells via `bZero`, and returns `outEnd`. -/
def compPackSplitsProc (bZero : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 8 (.bin .add (.reg 1) (.reg 6)) ;;
  compCopySliceStmt 8 1 6 12 13 ;;
  .assign 9 (.reg 2) ;;
  .assign 10 (.const 0) ;;
  .loop (.bin .lt (.reg 10) (.reg 6))
    (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
     .store (.bin .add (.reg 8) (.reg 10)) (.reg 9) ;;
     .store (.reg 9) (.reg 11) ;;
     .assign 12 (.bin .mul (.const 4) (.reg 11)) ;;
     .assign 13 (.bin .add (.reg 4) (.bin .mul (.const 4) (.bin .mul (.reg 10) (.reg 7)))) ;;
     .assign 14 (.bin .add (.reg 9) (.const 1)) ;;
     compCopySliceStmt 13 14 12 15 16 ;;
     .assign 9 (.bin .add (.reg 14) (.reg 12)) ;;
     .call 15 bZero [.reg 13, .reg 12] ;;
     .store (.bin .add (.reg 3) (.reg 10)) (.const 0) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1))) ;;
  .call 15 bZero [.reg 5, .reg 6] ;;
  .ret (.reg 9)

lemma compPackSplitsProc_noRand (bZero : ℕ) : (compPackSplitsProc bZero).NoRand := by
  simp [compPackSplitsProc, compCopySliceStmt, Stmt.NoRand]

/-! ## 2. Prefix word-count helpers -/

/-- Sum of `splitEntriesWords (splits i)` over the first `j` branches. -/
def compSplitPrefixWords {k : ℕ} (splits : Fin k → List CompSplitEntry) (j : ℕ) : ℕ :=
  (Finset.range j).sum fun i =>
    if hi : i < k then splitEntriesWords (splits ⟨i, hi⟩) else 0

lemma compSplitPrefixWords_succ {k : ℕ} (splits : Fin k → List CompSplitEntry) {j : ℕ} (hj : j < k) :
    compSplitPrefixWords splits (j + 1) =
      compSplitPrefixWords splits j + splitEntriesWords (splits ⟨j, hj⟩) := by
  simp [compSplitPrefixWords, Finset.sum_range_succ, hj]

lemma compSplitPrefixWords_le {k vCap : ℕ} (splits : Fin k → List CompSplitEntry)
    (hbd : ∀ j : Fin k, (splits j).length ≤ vCap) :
    ∀ j ≤ k, compSplitPrefixWords splits j ≤ j * (1 + 4 * vCap)
  | 0, _ => by simp [compSplitPrefixWords]
  | j + 1, hj => by
    rw [compSplitPrefixWords_succ splits (by omega)]
    have h1 := compSplitPrefixWords_le splits hbd j (by omega)
    have h2 := hbd ⟨j, by omega⟩
    dsimp only [splitEntriesWords]
    have hmul : (j + 1) * (1 + 4 * vCap) = j * (1 + 4 * vCap) + (1 + 4 * vCap) := by ring
    omega

private lemma compPackZeroRange_call {w bZero ptr len : ℕ} {p : Program} {mem : ℕ → ℕ} {pos : ℕ}
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

/-! ## 3. Verification of `compPackSplitsProc` -/

set_option maxHeartbeats 800000 in
/-- Verification of `compPackSplitsProc`: shifts `[ptrBase + k, ptrBase + 2 * k)` to
`[ptrBase, ptrBase + k)`, packs every branch's `SplitEntriesAt` record at `[midEnd, outEnd)`,
writes `[spPtr_0 .. spPtr_{k-1}]` at `[ptrBase + k, ptrBase + 2 * k)`, zeroes all split-buffer
and `oldCnt` scratch cells so `ZeroFrom st'.mem outEnd` holds, and preserves memory outside
`[ptrBase, ptrBase + 2 * k)` and `[midEnd, ∞)`. -/
theorem compPackSplits_runs {w k b bZero ptrBase midEnd spCntBase spBufBase oldCntBase vCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {splits : Fin k → List CompSplitEntry}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k)
    (hK_m : mem (b + compOffK) = k) (hVCap_m : mem (b + compOffVCap) = vCap)
    (hb_hdr_w : b + compHdrSize < 2 ^ w)
    (hptr_le_mid : ptrBase + 2 * k ≤ midEnd)
    (hmid_le_buf : midEnd + k * (1 + 4 * vCap) ≤ spBufBase)
    (hbuf_le_cnt : spBufBase + 4 * (k * vCap) ≤ spCntBase)
    (hcnt_le_old : spCntBase + k ≤ oldCntBase)
    (hold_w : oldCntBase + k < 2 ^ w)
    (hbd : ∀ j : Fin k, (splits j).length ≤ vCap)
    (hcnt_m : ∀ j : Fin k, mem (spCntBase + j.1) = (splits j).length)
    (hbuf_m : ∀ j : Fin k, ∀ i (hi : i < (splits j).length),
      mem (spBufBase + 4 * (j.1 * vCap) + 4 * i) = (if (splits j)[i].isRelease then 1 else 0) ∧
      mem (spBufBase + 4 * (j.1 * vCap) + 4 * i + 1) = (splits j)[i].edge ∧
      mem (spBufBase + 4 * (j.1 * vCap) + 4 * i + 2) = (splits j)[i].kept ∧
      mem (spBufBase + 4 * (j.1 * vCap) + 4 * i + 3) = (splits j)[i].fresh)
    (hz_mid : ∀ a, midEnd ≤ a → a < spBufBase → mem a = 0)
    (hz_gap1 : ∀ a, spBufBase + 4 * (k * vCap) ≤ a → a < spCntBase → mem a = 0)
    (hz_buf_tail : ∀ j : Fin k, ∀ t, 4 * (splits j).length ≤ t → t < 4 * vCap →
      mem (spBufBase + 4 * (j.1 * vCap) + t) = 0)
    (hz_gap2 : ∀ a, spCntBase + k ≤ a → a < oldCntBase → mem a = 0)
    (hz_above : ZeroFrom mem (oldCntBase + k)) :
    let outEnd := midEnd + compSplitPrefixWords splits k
    ∃ st' c,
      Runs w p ω (compPackSplitsProc bZero)
        (startState [b, ptrBase, midEnd, spCntBase, spBufBase, oldCntBase] mem pos)
        (.returned outEnd) st' c ∧
      (∀ j : Fin k, st'.mem (ptrBase + j.1) = mem (ptrBase + k + j.1)) ∧
      (∀ a, ptrBase + 2 * k ≤ a → a < midEnd → st'.mem a = mem a) ∧
      (∀ j : Fin k,
        let spPtr := st'.mem (ptrBase + k + j.1)
        spPtr = midEnd + compSplitPrefixWords splits j.1 ∧
        SplitEntriesAt st'.mem spPtr (splits j) ∧
        ptrBase + 2 * k ≤ spPtr ∧
        spPtr + splitEntriesWords (splits j) ≤ outEnd) ∧
      outEnd ≤ spBufBase ∧
      ZeroFrom st'.mem outEnd ∧
      (∀ a < ptrBase, st'.mem a = mem a) ∧
      c ≤ 180 * (∑ j : Fin k, (splits j).length) + 150 * k + 80 := by
  intro outEnd
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_w hoff; omega
  have hout_le : outEnd ≤ spBufBase := by
    have := compSplitPrefixWords_le splits hbd k le_rfl
    dsimp only [outEnd]; omega
  -- Prefix: load `k, vCap`, compute `r8 = ptrBase + k`, copy `k` pointers to `ptrBase`, set `r9 = midEnd, r10 = 0`
  set st0 := startState [b, ptrBase, midEnd, spCntBase, spBufBase, oldCntBase] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 6 k }
  let st2 : State := { st1 with regs := Function.update st1.regs 7 vCap }
  let st3 : State := { st2 with regs := Function.update st2.regs 8 (ptrBase + k) }
  have hp1 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffK)))) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      have := hb_off compOffK (by decide); simp [st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hK_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffVCap (by decide); simp [st1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hVCap_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 8 (.bin .add (.reg 1) (.reg 6))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨ptrBase + k, by
      simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, show ptrBase + k < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st4, cShift, hshift, hst4_r, hst4_cp, hst4_fr, hcShift⟩ :=
    compCopySlice_runs (w := w) (rSrc := 8) (rDst := 1) (rLen := 6) (rIdx := 12) (rTmp := 13)
      (src := ptrBase + k) (dst := ptrBase) (len := k) (p := p) (ω := ω) (st := st3)
      (by decide) hw16 (by omega) (by omega) (Or.inr le_rfl)
      (by simp [st3]) (by simp [st3, st2, st1, st0, startState]) (by simp [st3, st2, st1])
  let st5 : State := { st4 with regs := Function.update st4.regs 9 midEnd }
  let st6 : State := { st5 with regs := Function.update st5.regs 10 0 }
  have hp5 : Runs w p ω (.assign 9 (.reg 2)) st4 .normal st5 2 :=
    runs_assign_iff.mpr ⟨midEnd, by
      simp [Expr.eval, hst4_r 2 (by decide), st3, st2, st1, st0, startState], rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 10 (.const 0)) st5 .normal st6 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Main packing loop over `j = 0 .. k - 1`
  have hloop : ∀ rem j (s : State) (hj : j ≤ k), k - j = rem →
      s.regs 3 = spCntBase → s.regs 4 = spBufBase → s.regs 5 = oldCntBase →
      s.regs 6 = k → s.regs 7 = vCap → s.regs 8 = ptrBase + k →
      s.regs 9 = midEnd + compSplitPrefixWords splits j → s.regs 10 = j →
      (∀ t : Fin k, t.1 < j →
        let spPtr := midEnd + compSplitPrefixWords splits t.1
        s.mem (ptrBase + k + t.1) = spPtr ∧
        SplitEntriesAt s.mem spPtr (splits t) ∧
        s.mem (spCntBase + t.1) = 0 ∧
        (∀ off < 4 * vCap, s.mem (spBufBase + 4 * (t.1 * vCap) + off) = 0)) →
      (∀ a, midEnd + compSplitPrefixWords splits j ≤ a → a < spBufBase → s.mem a = 0) →
      (∀ t : Fin k, j ≤ t.1 →
        s.mem (spCntBase + t.1) = (splits t).length ∧
        (∀ i (hi : i < (splits t).length),
          s.mem (spBufBase + 4 * (t.1 * vCap) + 4 * i) = (if (splits t)[i].isRelease then 1 else 0) ∧
          s.mem (spBufBase + 4 * (t.1 * vCap) + 4 * i + 1) = (splits t)[i].edge ∧
          s.mem (spBufBase + 4 * (t.1 * vCap) + 4 * i + 2) = (splits t)[i].kept ∧
          s.mem (spBufBase + 4 * (t.1 * vCap) + 4 * i + 3) = (splits t)[i].fresh) ∧
        (∀ off, 4 * (splits t).length ≤ off → off < 4 * vCap →
          s.mem (spBufBase + 4 * (t.1 * vCap) + off) = 0)) →
      (∀ a, spBufBase + 4 * (k * vCap) ≤ a → a < spCntBase → s.mem a = 0) →
      (∀ a, spCntBase + k ≤ a → a < oldCntBase → s.mem a = 0) →
      ZeroFrom s.mem (oldCntBase + k) →
      (∀ a, a < ptrBase + k ∨ (ptrBase + 2 * k ≤ a ∧ a < midEnd) → s.mem a = st4.mem a) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 10) (.reg 6))
            (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
             .store (.bin .add (.reg 8) (.reg 10)) (.reg 9) ;;
             .store (.reg 9) (.reg 11) ;;
             .assign 12 (.bin .mul (.const 4) (.reg 11)) ;;
             .assign 13 (.bin .add (.reg 4) (.bin .mul (.const 4) (.bin .mul (.reg 10) (.reg 7)))) ;;
             .assign 14 (.bin .add (.reg 9) (.const 1)) ;;
             compCopySliceStmt 13 14 12 15 16 ;;
             .assign 9 (.bin .add (.reg 14) (.reg 12)) ;;
             .call 15 bZero [.reg 13, .reg 12] ;;
             .store (.bin .add (.reg 3) (.reg 10)) (.const 0) ;;
             .assign 10 (.bin .add (.reg 10) (.const 1))))
          s .normal st' c ∧
        st'.regs 5 = oldCntBase ∧ st'.regs 6 = k ∧ st'.regs 9 = outEnd ∧
        (∀ t : Fin k,
          let spPtr := midEnd + compSplitPrefixWords splits t.1
          st'.mem (ptrBase + k + t.1) = spPtr ∧
          SplitEntriesAt st'.mem spPtr (splits t) ∧
          st'.mem (spCntBase + t.1) = 0 ∧
          (∀ off < 4 * vCap, st'.mem (spBufBase + 4 * (t.1 * vCap) + off) = 0)) ∧
        (∀ a, outEnd ≤ a → a < spBufBase → st'.mem a = 0) ∧
        (∀ a, spBufBase + 4 * (k * vCap) ≤ a → a < spCntBase → st'.mem a = 0) ∧
        (∀ a, spCntBase + k ≤ a → a < oldCntBase → st'.mem a = 0) ∧
        ZeroFrom st'.mem (oldCntBase + k) ∧
        (∀ a, a < ptrBase + k ∨ (ptrBase + 2 * k ≤ a ∧ a < midEnd) → st'.mem a = st4.mem a) ∧
        c ≤ 180 * ((Finset.univ.filter fun t : Fin k => j ≤ t.1).sum fun t => (splits t).length) +
            90 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrem _ _ hr5 hr6 _ _ hr9 hr10 hdone hz_m _ hz_g1 hz_g2 hz_ab hfr
      have hjk : j = k := by omega
      subst hjk
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr10, hr6],
        rfl, rfl, by simp [Expr.size]⟩), hr5, hr6, hr9, fun t => hdone t t.2, hz_m, hz_g1, hz_g2, hz_ab, hfr, by omega⟩
    | succ rem ih =>
      intro j s hj hrem hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hdone hz_m hrest hz_g1 hz_g2 hz_ab hfr
      have hjlt : j < k := by omega
      let jf : Fin k := ⟨j, hjlt⟩
      set cnt := (splits jf).length
      have hcnt_le : cnt ≤ vCap := hbd jf
      set cur := midEnd + compSplitPrefixWords splits j
      have hcur_le : cur + (1 + 4 * cnt) ≤ spBufBase := by
        have h1 := compSplitPrefixWords_le splits hbd (j + 1) (by omega)
        rw [compSplitPrefixWords_succ splits hjlt] at h1
        have h2 : (j + 1) * (1 + 4 * vCap) ≤ k * (1 + 4 * vCap) := Nat.mul_le_mul_right _ (by omega)
        dsimp only [cur, splitEntriesWords, jf, cnt] at *; omega
      have hjv_le : j * vCap + vCap ≤ k * vCap := by
        have := Nat.mul_le_mul_right vCap (show j + 1 ≤ k by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
      set srcJ := spBufBase + 4 * (j * vCap)
      obtain ⟨hcnt_j, hbuf_j, htail_j⟩ := hrest jf le_rfl
      let s1 : State := { s with regs := Function.update s.regs 11 cnt }
      let s2 : State := { s1 with mem := Function.update s1.mem (ptrBase + k + j) cur }
      let s3 : State := { s2 with mem := Function.update s2.mem cur cnt }
      let s4 : State := { s3 with regs := Function.update s3.regs 12 (4 * cnt) }
      let s5 : State := { s4 with regs := Function.update s4.regs 13 srcJ }
      let s6 : State := { s5 with regs := Function.update s5.regs 14 (cur + 1) }
      have hcnt_j' : s.mem (spCntBase + j) = cnt := hcnt_j
      have hs1 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 3) (.reg 10)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨cnt, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr3, hr10, show spCntBase + j < 2 ^ w by omega]) hcnt_j',
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 8) (.reg 10)) (.reg 9)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨ptrBase + k + j, cur,
          by simp [s1, Expr.eval, BinOp.eval, hr8, hr10, show ptrBase + k + j < 2 ^ w by omega],
          by simp [s1, Expr.eval, hr9], rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w p ω (.store (.reg 9) (.reg 11)) s2 .normal s3 3 :=
        runs_store_iff.mpr ⟨cur, cnt, by simp [s2, s1, Expr.eval, hr9], by simp [s2, s1, Expr.eval],
          rfl, rfl, by simp [Expr.size]⟩
      have hs4 : Runs w p ω (.assign 12 (.bin .mul (.const 4) (.reg 11))) s3 .normal s4 4 :=
        runs_assign_iff.mpr ⟨4 * cnt, by
          simp [s3, s2, s1, Expr.eval, BinOp.eval, hw4, show 4 * cnt < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hs5 : Runs w p ω (.assign 13 (.bin .add (.reg 4) (.bin .mul (.const 4) (.bin .mul (.reg 10) (.reg 7)))))
          s4 .normal s5 8 :=
        runs_assign_iff.mpr ⟨srcJ, by
          simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr4, hr10, hr7, hw4, srcJ,
            show j * vCap < 2 ^ w by omega, show 4 * (j * vCap) < 2 ^ w by omega, show srcJ < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hs6 : Runs w p ω (.assign 14 (.bin .add (.reg 9) (.const 1))) s5 .normal s6 4 :=
        runs_assign_iff.mpr ⟨cur + 1, by
          simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr9, hw1, show cur + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨s7, cCp, hs7, hr7_o, hcp7, hfr7, hcCp⟩ :=
        compCopySlice_runs (w := w) (rSrc := 13) (rDst := 14) (rLen := 12) (rIdx := 15) (rTmp := 16)
          (src := srcJ) (dst := cur + 1) (len := 4 * cnt) (p := p) (ω := ω) (st := s6)
          (by decide) hw16 (by omega) (by omega) (Or.inr (by omega))
          (by simp [s6, s5]) (by simp [s6]) (by simp [s6, s5, s4])
      let s8 : State := { s7 with regs := Function.update s7.regs 9 (cur + 1 + 4 * cnt) }
      have hs8 : Runs w p ω (.assign 9 (.bin .add (.reg 14) (.reg 12))) s7 .normal s8 4 :=
        runs_assign_iff.mpr ⟨cur + 1 + 4 * cnt, by
          simp [Expr.eval, BinOp.eval, hr7_o 14 (by decide), hr7_o 12 (by decide), s6, s5, s4,
            show cur + 1 + 4 * cnt < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨oZ, sZ, cZ, hrZ, hoZ, hZ_post, hZ_out, hcZ⟩ :=
        compPackZeroRange_call hpZero hw16 (ptr := srcJ) (len := 4 * cnt) (mem := s8.mem) (pos := s8.pos)
          (ω := ω) (by omega)
      let s9 : State := { s8 with regs := Function.update s8.regs 15 0, mem := sZ.mem, pos := sZ.pos }
      have hs9 : Runs w p ω (.call 15 bZero [.reg 13, .reg 12]) s8 .normal s9 (2 + cZ + 1) :=
        runs_call_iff.mpr ⟨[srcJ, 4 * cnt], compZeroRangeProc, oZ, sZ, cZ,
          by simp [evalArgs, Expr.eval, s8, hr7_o 13 (by decide), hr7_o 12 (by decide), s6, s5, s4],
          hpZero, hrZ, rfl, by simp [s9, hoZ], by simp [argsSize, Expr.size]⟩
      let s10 : State := { s9 with mem := Function.update s9.mem (spCntBase + j) 0 }
      let s11 : State := { s10 with regs := Function.update s10.regs 10 (j + 1) }
      have hs10 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 10)) (.const 0)) s9 .normal s10 5 :=
        runs_store_iff.mpr ⟨spCntBase + j, 0,
          by simp [s9, s8, hr7_o 3 (by decide), hr7_o 10 (by decide), s6, s5, s4, s3, s2, s1,
            Expr.eval, BinOp.eval, hr3, hr10, show spCntBase + j < 2 ^ w by omega],
          by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hs11 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) s10 .normal s11 4 :=
        runs_assign_iff.mpr ⟨j + 1, by
          simp [s10, s9, s8, hr7_o 10 (by decide), s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval,
            hr10, hw1, show j + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hstep_fr : ∀ a, a ≠ ptrBase + k + j → (a < cur ∨ cur + 1 + 4 * cnt ≤ a) →
          a ≠ spCntBase + j → (a < srcJ ∨ srcJ + 4 * cnt ≤ a) → s11.mem a = s.mem a := fun a h1 h2 h3 h4 => by
        dsimp only [s11, s10, s9]
        rw [Function.update_of_ne h3, hZ_out a h4]
        dsimp only [s8]
        rw [hfr7 a (by omega)]
        dsimp only [s6, s5, s4, s3, s2, s1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne h1]
      have hcur_next : cur + 1 + 4 * cnt = midEnd + compSplitPrefixWords splits (j + 1) := by
        rw [compSplitPrefixWords_succ splits hjlt]; dsimp only [cur, splitEntriesWords, cnt, jf]; omega
      have t10 := runs_seq_iff.mpr (Or.inr ⟨s10, 5, 4, hs10, hs11, rfl⟩)
      have t9 := runs_seq_iff.mpr (Or.inr ⟨s9, 2 + cZ + 1, _, hs9, t10, rfl⟩)
      have t8 := runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, hs8, t9, rfl⟩)
      have t7 := runs_seq_iff.mpr (Or.inr ⟨s7, cCp, _, hs7, t8, rfl⟩)
      have t6 := runs_seq_iff.mpr (Or.inr ⟨s6, 4, _, hs6, t7, rfl⟩)
      have t5 := runs_seq_iff.mpr (Or.inr ⟨s5, 8, _, hs5, t6, rfl⟩)
      have t4 := runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, hs4, t5, rfl⟩)
      have t3 := runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, hs3, t4, rfl⟩)
      have t2 := runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2, t3, rfl⟩)
      have hbody := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hs1, t2, rfl⟩)
      obtain ⟨st', cRest, hrest_run, hr5', hr6', hr9', hdone', hzm', hzg1', hzg2', hzab', hfr', hcRest⟩ :=
        ih (j + 1) s11 (by omega) (by omega)
          (by simp [s11, s10, s9, s8, hr7_o 3 (by decide), s6, s5, s4, s3, s2, s1, hr3])
          (by simp [s11, s10, s9, s8, hr7_o 4 (by decide), s6, s5, s4, s3, s2, s1, hr4])
          (by simp [s11, s10, s9, s8, hr7_o 5 (by decide), s6, s5, s4, s3, s2, s1, hr5])
          (by simp [s11, s10, s9, s8, hr7_o 6 (by decide), s6, s5, s4, s3, s2, s1, hr6])
          (by simp [s11, s10, s9, s8, hr7_o 7 (by decide), s6, s5, s4, s3, s2, s1, hr7])
          (by simp [s11, s10, s9, s8, hr7_o 8 (by decide), s6, s5, s4, s3, s2, s1, hr8])
          (by simp [s11, s10, s9, s8, hcur_next]) (by simp [s11])
          (fun t ht => by
            by_cases htj : t.1 = j
            · have ht_eq : t = jf := Fin.ext htj
              subst ht_eq
              have hs11_ptr : s11.mem (ptrBase + k + j) = cur := by
                dsimp only [s11, s10, s9]; rw [Function.update_of_ne (by omega), hZ_out _ (Or.inl (by omega))]
                dsimp only [s8]; rw [hfr7 _ (Or.inl (by omega))]
                dsimp only [s6, s5, s4, s3, s2, s1]; rw [Function.update_of_ne (by omega), Function.update_self]
              have hs11_len : s11.mem cur = cnt := by
                dsimp only [s11, s10, s9]; rw [Function.update_of_ne (by omega), hZ_out _ (Or.inl (by omega))]
                dsimp only [s8]; rw [hfr7 _ (Or.inl (by omega))]
                dsimp only [s6, s5, s4, s3]; simp
              have hs11_ent : ∀ idx (hidx : idx < cnt),
                  s11.mem (cur + 1 + 4 * idx) = (if (splits jf)[idx].isRelease then 1 else 0) ∧
                  s11.mem (cur + 1 + 4 * idx + 1) = (splits jf)[idx].edge ∧
                  s11.mem (cur + 1 + 4 * idx + 2) = (splits jf)[idx].kept ∧
                  s11.mem (cur + 1 + 4 * idx + 3) = (splits jf)[idx].fresh := fun idx hidx => by
                have hcp_cell : ∀ off < 4, s11.mem (cur + 1 + (4 * idx + off)) = s.mem (srcJ + (4 * idx + off)) := fun off hoff => by
                  dsimp only [s11, s10, s9]; rw [Function.update_of_ne (by omega), hZ_out _ (Or.inl (by omega))]
                  dsimp only [s8]; rw [hcp7 (4 * idx + off) (by omega)]
                  dsimp only [s6, s5, s4, s3, s2, s1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                have hb := hbuf_j idx hidx
                have h0 := hcp_cell 0 (by omega); simp only [Nat.add_zero] at h0
                have h1 : s11.mem (cur + 1 + 4 * idx + 1) = s.mem (srcJ + 4 * idx + 1) := by
                  simpa [Nat.add_assoc] using hcp_cell 1 (by omega)
                have h2 : s11.mem (cur + 1 + 4 * idx + 2) = s.mem (srcJ + 4 * idx + 2) := by
                  simpa [Nat.add_assoc] using hcp_cell 2 (by omega)
                have h3 : s11.mem (cur + 1 + 4 * idx + 3) = s.mem (srcJ + 4 * idx + 3) := by
                  simpa [Nat.add_assoc] using hcp_cell 3 (by omega)
                exact ⟨h0.trans hb.1, h1.trans hb.2.1, h2.trans hb.2.2.1, h3.trans hb.2.2.2⟩
              refine ⟨hs11_ptr, ⟨hs11_len, hs11_ent⟩, by simp [s11, s10, jf], fun off hoff => ?_⟩
              change s11.mem (srcJ + off) = 0
              dsimp only [s11, s10, s9]; rw [Function.update_of_ne (by dsimp [srcJ]; omega)]
              by_cases hlt : off < 4 * cnt
              · exact hZ_post off hlt
              · rw [hZ_out _ (Or.inr (by omega))]; dsimp only [s8]; rw [hfr7 _ (Or.inr (by dsimp [srcJ]; omega))]
                dsimp only [s6, s5, s4, s3, s2, s1]
                rw [Function.update_of_ne (by dsimp [srcJ]; omega), Function.update_of_ne (by dsimp [srcJ]; omega)]
                exact htail_j off (by omega) hoff
            · have ht_lt : t.1 < j := by omega
              obtain ⟨hd1, ⟨hd2a, hd2b⟩, hd3, hd4⟩ := hdone t ht_lt
              have hpref_t : compSplitPrefixWords splits t.1 + splitEntriesWords (splits t) ≤
                  compSplitPrefixWords splits j := by
                rw [← compSplitPrefixWords_succ splits t.2]
                exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
              dsimp only [splitEntriesWords] at hpref_t
              have htv_le : t.1 * vCap + vCap ≤ j * vCap := by
                have := Nat.mul_le_mul_right vCap (show t.1 + 1 ≤ j by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
              refine ⟨(hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans hd1,
                ⟨(hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans hd2a,
                 fun idx hidx => by
                   have he := hd2b idx hidx
                   exact ⟨(hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans he.1,
                     (hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans he.2.1,
                     (hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans he.2.2.1,
                     (hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans he.2.2.2⟩⟩,
                (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans hd3,
                fun off hoff => (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans (hd4 off hoff)⟩)
          (fun a ha1 ha2 => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))).trans (hz_m a (by omega) ha2))
          (fun t ht => by
            obtain ⟨hr1, hr2, hr3⟩ := hrest t (by omega)
            have hjv_t : j * vCap + vCap ≤ t.1 * vCap := by
              have := Nat.mul_le_mul_right vCap (show j + 1 ≤ t.1 by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
            have htv_k : t.1 * vCap + vCap ≤ k * vCap := by
              have := Nat.mul_le_mul_right vCap (show t.1 + 1 ≤ k by have := t.2; omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
            have ht_bd : (splits t).length ≤ vCap := hbd t
            refine ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans hr1,
              fun idx hidx => by
                have he := hr2 idx hidx
                exact ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans he.1,
                  (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans he.2.1,
                  (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans he.2.2.1,
                  (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans he.2.2.2⟩,
              fun off ho1 ho2 => (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hr3 off ho1 ho2)⟩)
          (fun a ha1 ha2 => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hz_g1 a ha1 ha2))
          (fun a ha1 ha2 => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hz_g2 a ha1 ha2))
          (fun a ha => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))).trans (hz_ab a ha))
          (fun a ha => (hstep_fr a (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega))).trans (hfr a ha))
      have hsum_split : ((Finset.univ.filter fun t : Fin k => j ≤ t.1).sum fun t => (splits t).length) =
          cnt + ((Finset.univ.filter fun t : Fin k => j + 1 ≤ t.1).sum fun t => (splits t).length) := by
        have hpart : (Finset.univ.filter fun t : Fin k => j ≤ t.1) =
            insert jf (Finset.univ.filter fun t : Fin k => j + 1 ≤ t.1) := by
          ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, jf]; omega
        rw [hpart, Finset.sum_insert (by simp [jf])]
      have hfull := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s11, _, cRest,
        by simp [Expr.eval, BinOp.eval, hr10, hr6, hjlt, hw1], by decide, hbody, hrest_run, by simp [Expr.size]; rfl⟩))
      exact ⟨st', _, hfull, hr5', hr6', hr9', hdone', hzm', hzg1', hzg2', hzab', hfr', by omega⟩
  -- Run loop from `j = 0`, zero `oldCntBase`, return `outEnd`
  obtain ⟨stL, cL, hrL, hrL5, hrL6, hrL9, hdoneL, hzmL, hzg1L, hzg2L, hzabL, hfrL, hcL⟩ :=
    hloop k 0 st6 (Nat.zero_le k) (by omega)
      (by simp [st6, st5, hst4_r 3 (by decide), st3, st2, st1, st0, startState])
      (by simp [st6, st5, hst4_r 4 (by decide), st3, st2, st1, st0, startState])
      (by simp [st6, st5, hst4_r 5 (by decide), st3, st2, st1, st0, startState])
      (by simp [st6, st5, hst4_r 6 (by decide), st3, st2, st1])
      (by simp [st6, st5, hst4_r 7 (by decide), st3, st2])
      (by simp [st6, st5, hst4_r 8 (by decide), st3])
      (by simp [st6, st5, compSplitPrefixWords]) (by simp [st6])
      (fun _ h => by omega)
      (fun a ha1 ha2 => (hst4_fr a (Or.inr (by simp [compSplitPrefixWords] at ha1; omega))).trans
        (hz_mid a (by simp [compSplitPrefixWords] at ha1; omega) ha2))
      (fun t _ => ⟨(hst4_fr _ (Or.inr (by omega))).trans (hcnt_m t),
        fun i hi => by
          have hb := hbuf_m t i hi
          exact ⟨(hst4_fr _ (Or.inr (by omega))).trans hb.1, (hst4_fr _ (Or.inr (by omega))).trans hb.2.1,
            (hst4_fr _ (Or.inr (by omega))).trans hb.2.2.1, (hst4_fr _ (Or.inr (by omega))).trans hb.2.2.2⟩,
        fun off ho1 ho2 => (hst4_fr _ (Or.inr (by omega))).trans (hz_buf_tail t off ho1 ho2)⟩)
      (fun a ha1 ha2 => (hst4_fr a (Or.inr (by omega))).trans (hz_gap1 a ha1 ha2))
      (fun a ha1 ha2 => (hst4_fr a (Or.inr (by omega))).trans (hz_gap2 a ha1 ha2))
      (fun a ha => (hst4_fr a (Or.inr (by omega))).trans (hz_above a ha))
      (fun _ _ => rfl)
  obtain ⟨oZo, stZo, cZo, hrZo, hoZo, hZo_post, hZo_out, hcZo⟩ :=
    compPackZeroRange_call hpZero hw16 (ptr := oldCntBase) (len := k) (mem := stL.mem) (pos := stL.pos) (ω := ω) hold_w
  let stEnd : State := { stL with regs := Function.update stL.regs 15 0, mem := stZo.mem, pos := stZo.pos }
  have hcallZo : Runs w p ω (.call 15 bZero [.reg 5, .reg 6]) stL .normal stEnd (2 + cZo + 1) :=
    runs_call_iff.mpr ⟨[oldCntBase, k], compZeroRangeProc, oZo, stZo, cZo,
      by simp [evalArgs, Expr.eval, hrL5, hrL6], hpZero, hrZo, rfl, by simp [stEnd, hoZo], by simp [argsSize, Expr.size]⟩
  have hret : Runs w p ω (.ret (.reg 9)) stEnd (.returned outEnd) stEnd 2 :=
    runs_ret_iff.mpr ⟨outEnd, by simp [stEnd, Expr.eval, hrL9], rfl, rfl, by simp [Expr.size]⟩
  have hfull : Runs w p ω (compPackSplitsProc bZero) st0 (.returned outEnd) stEnd
      (5 + (5 + (4 + (cShift + (2 + (2 + (cL + ((2 + cZo + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    have q7 := runs_seq_iff.mpr (Or.inr ⟨stEnd, 2 + cZo + 1, 2, hcallZo, hret, rfl⟩)
    have q6 := runs_seq_iff.mpr (Or.inr ⟨stL, cL, _, hrL, q7, rfl⟩)
    have q5 := runs_seq_iff.mpr (Or.inr ⟨st6, 2, _, hp6, q6, rfl⟩)
    have q4 := runs_seq_iff.mpr (Or.inr ⟨st5, 2, _, hp5, q5, rfl⟩)
    have q3 := runs_seq_iff.mpr (Or.inr ⟨st4, cShift, _, hshift, q4, rfl⟩)
    have q2 := runs_seq_iff.mpr (Or.inr ⟨st3, 4, _, hp3, q3, rfl⟩)
    have q1 := runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, hp2, q2, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hp1, q1, rfl⟩)
  have hfilt : (Finset.univ.filter fun t : Fin k => 0 ≤ t.1) = Finset.univ := by ext t; simp
  rw [hfilt] at hcL
  refine ⟨stEnd, _, hfull,
    fun j => (hZo_out _ (Or.inl (by have := j.2; omega))).trans ((hfrL _ (Or.inl (by have := j.2; omega))).trans (hst4_cp j.1 j.2)),
    fun a ha1 ha2 => (hZo_out a (Or.inl (by omega))).trans ((hfrL a (Or.inr ⟨ha1, ha2⟩)).trans (hst4_fr a (Or.inr (by omega)))),
    fun j => ?_, hout_le, fun a ha => ?_,
    fun a ha => (hZo_out a (Or.inl (by omega))).trans ((hfrL a (Or.inl (by omega))).trans (hst4_fr a (Or.inl ha))),
    by omega⟩
  · obtain ⟨hp_j, ⟨hsp_l, hsp_e⟩, _, _⟩ := hdoneL j
    have hpref_le : compSplitPrefixWords splits j.1 + splitEntriesWords (splits j) ≤
        compSplitPrefixWords splits k := by
      rw [← compSplitPrefixWords_succ splits j.2]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have hptr_j : stEnd.mem (ptrBase + k + j.1) = midEnd + compSplitPrefixWords splits j.1 :=
      (hZo_out _ (Or.inl (by have := j.2; omega))).trans hp_j
    refine ⟨hptr_j, ?_, by omega, by dsimp [outEnd]; omega⟩
    rw [hptr_j]
    dsimp only [splitEntriesWords] at hpref_le
    refine ⟨(hZo_out _ (Or.inl (by omega))).trans hsp_l, fun idx hidx => ?_⟩
    have he := hsp_e idx hidx
    exact ⟨(hZo_out _ (Or.inl (by omega))).trans he.1, (hZo_out _ (Or.inl (by omega))).trans he.2.1,
      (hZo_out _ (Or.inl (by omega))).trans he.2.2.1, (hZo_out _ (Or.inl (by omega))).trans he.2.2.2⟩
  · by_cases h1 : a < spBufBase
    · exact (hZo_out a (Or.inl (by omega))).trans (hzmL a ha h1)
    · by_cases h2 : a < spBufBase + 4 * (k * vCap)
      · have hvPos : 0 < 4 * vCap := by
          have : 0 < 4 * (k * vCap) := by omega
          have hmul : k * (4 * vCap) = 4 * (k * vCap) := by ring
          exact Nat.pos_of_mul_pos_left (by omega : 0 < k * (4 * vCap))
        have hlt_mul : a - spBufBase < (4 * vCap) * k := by
          have : (4 * vCap) * k = 4 * (k * vCap) := by ring
          omega
        let tf : Fin k := ⟨(a - spBufBase) / (4 * vCap),
          (Nat.div_lt_iff_lt_mul hvPos).mpr (by rw [Nat.mul_comm]; exact hlt_mul)⟩
        have ha_eq : a = spBufBase + 4 * (tf.1 * vCap) + (a - spBufBase) % (4 * vCap) := by
          have hdm := Nat.div_add_mod (a - spBufBase) (4 * vCap)
          have hmc : 4 * (tf.1 * vCap) = (4 * vCap) * ((a - spBufBase) / (4 * vCap)) := by dsimp [tf]; ring
          omega
        exact (hZo_out a (Or.inl (by omega))).trans (ha_eq ▸ (hdoneL tf).2.2.2 _ (Nat.mod_lt _ hvPos))
      · by_cases h3 : a < spCntBase
        · exact (hZo_out a (Or.inl (by omega))).trans (hzg1L a (by omega) h3)
        · by_cases h4 : a < spCntBase + k
          · let tf : Fin k := ⟨a - spCntBase, by omega⟩
            have hstL_a : stL.mem a = 0 := by
              have h := (hdoneL tf).2.2.1
              rwa [show spCntBase + tf.1 = a by dsimp [tf]; omega] at h
            exact (hZo_out a (Or.inl (by omega))).trans hstL_a
          · by_cases h5 : a < oldCntBase
            · exact (hZo_out a (Or.inl h5)).trans (hzg2L a (by omega) h5)
            · by_cases h6 : a < oldCntBase + k
              · have := hZo_post (a - oldCntBase) (by omega)
                rwa [show oldCntBase + (a - oldCntBase) = a by omega] at this
              · exact (hZo_out a (Or.inr (by omega))).trans (hzabL a (by omega))

end

end MinCostFlow.SparseCore.Program
