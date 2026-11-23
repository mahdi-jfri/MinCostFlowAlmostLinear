module

public import MinCostFlow.SparseCore.Program.CompBatchBase
public import MinCostFlow.SparseCore.Program.ReadSpec
import WordRAM.Tactic

/-!
# Per-Branch `LSFChangeAt` Packing & Scratch Zeroing (`CompBatchPack`)

Defines and verifies `compPackChangesProc (bZero : ℕ)`:
given `[b, heap, numTouched, cntBase, splitBase, numSplits]`, packs the `k` per-branch change
records `chg j := ⟨cuts_j.map Prod.snd ++ splitVerts, cuts_j.map Prod.fst⟩` consecutively
starting at `heap + 1 + numTouched + k`, writes the `k` pointers `[chgPtr_0, ..., chgPtr_{k-1}]`
at `[heap + 1 + numTouched, heap + 1 + numTouched + k)`, zeroes every written scratch cell in
`cntBase`, `rootsBase`, `fDelBase`, and `splitBase` so `ZeroFrom st'.mem outEnd` holds, and
returns `outEnd`.

Total cost is `≤ 100 * ∑_j (cuts j).length + 50 * k * (numSplits + 1) + 250 * k + 80`, paid
completely by the `120 * ∑_j (cuts j).length` credit from `compDispatchOne_runs` plus the
`compBatchUpdMul * k * (|U| + 1)` batch-update budget.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Packing procedure -/

/-- `args = [b, heap, numTouched, cntBase, splitBase, numSplits]`: packs the `k` per-branch
`Read.LSFChangeAt` records starting at `heap + 1 + numTouched + k`, stores their base addresses at
`[heap + 1 + numTouched, heap + 1 + numTouched + k)`, zeroes all written cut-log and split-vertex
scratch cells via `bZero`, and returns `outEnd`. -/
def compPackChangesProc (bZero : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 2)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 10 (.bin .add (.reg 3) (.reg 6)) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.reg 6) (.reg 7))) ;;
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.reg 12) (.reg 6))
    (.assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
     .store (.bin .add (.reg 8) (.reg 12)) (.reg 9) ;;
     .assign 14 (.bin .add (.reg 13) (.reg 5)) ;;
     .store (.reg 9) (.reg 14) ;;
     .assign 15 (.bin .mul (.reg 12) (.reg 7)) ;;
     .assign 16 (.bin .add (.reg 10) (.reg 15)) ;;
     .assign 17 (.bin .add (.reg 9) (.const 1)) ;;
     compCopySliceStmt 16 17 13 18 19 ;;
     .assign 17 (.bin .add (.reg 17) (.reg 13)) ;;
     compCopySliceStmt 4 17 5 18 19 ;;
     .assign 17 (.bin .add (.reg 17) (.reg 5)) ;;
     .store (.reg 17) (.reg 13) ;;
     .assign 16 (.bin .add (.reg 11) (.reg 15)) ;;
     .assign 17 (.bin .add (.reg 17) (.const 1)) ;;
     compCopySliceStmt 16 17 13 18 19 ;;
     .assign 9 (.bin .add (.reg 17) (.reg 13)) ;;
     .call 18 bZero [.bin .add (.reg 10) (.reg 15), .reg 13] ;;
     .call 18 bZero [.bin .add (.reg 11) (.reg 15), .reg 13] ;;
     .store (.bin .add (.reg 3) (.reg 12)) (.const 0) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1))) ;;
  .call 18 bZero [.reg 4, .reg 5] ;;
  .ret (.reg 9)

lemma compPackChangesProc_noRand (bZero : ℕ) : (compPackChangesProc bZero).NoRand := by
  simp [compPackChangesProc, compCopySliceStmt, Stmt.NoRand]

/-! ## 2. Verification of `compPackChangesProc` -/

/-- Packed change record for branch `j`: cut roots followed by split vertices, paired with cut
forest edges. -/
def compBranchChange (cuts : List (ℕ × ℕ)) (splitVerts : List ℕ) : Read.LSFChange :=
  ⟨cuts.map Prod.snd ++ splitVerts, cuts.map Prod.fst⟩

lemma compBranchChange_words (cuts : List (ℕ × ℕ)) (splitVerts : List ℕ) :
    (compBranchChange cuts splitVerts).words = 2 + 2 * cuts.length + splitVerts.length := by
  simp [compBranchChange, Read.LSFChange.words, Read.LSFChange.size]; omega

/-- Sum of `LSFChange.words` over the first `j` branches. -/
def compPackedPrefixWords {k : ℕ} (cuts : Fin k → List (ℕ × ℕ)) (splitVerts : List ℕ) (j : ℕ) : ℕ :=
  (Finset.range j).sum fun i =>
    if hi : i < k then (compBranchChange (cuts ⟨i, hi⟩) splitVerts).words else 0

private lemma compPackedPrefixWords_succ {k : ℕ} (cuts : Fin k → List (ℕ × ℕ))
    (splitVerts : List ℕ) {j : ℕ} (hj : j < k) :
    compPackedPrefixWords cuts splitVerts (j + 1) =
      compPackedPrefixWords cuts splitVerts j + (compBranchChange (cuts ⟨j, hj⟩) splitVerts).words := by
  simp [compPackedPrefixWords, Finset.sum_range_succ, hj]

private lemma compPackedPrefixWords_le {k vCap : ℕ} (cuts : Fin k → List (ℕ × ℕ))
    (splitVerts : List ℕ) (hbd : ∀ j : Fin k, (cuts j).length + splitVerts.length ≤ vCap) :
    ∀ j ≤ k, compPackedPrefixWords cuts splitVerts j ≤ j * (2 + 2 * vCap)
  | 0, _ => by simp [compPackedPrefixWords]
  | j + 1, hj => by
    rw [compPackedPrefixWords_succ cuts splitVerts (by omega), compBranchChange_words]
    have h1 := compPackedPrefixWords_le cuts splitVerts hbd j (by omega)
    have h2 := hbd ⟨j, by omega⟩
    have hmul : (j + 1) * (2 + 2 * vCap) = j * (2 + 2 * vCap) + (2 + 2 * vCap) := by ring
    omega

private lemma compZeroRange_call {w bZero ptr len : ℕ} {p : Program} {mem : ℕ → ℕ} {pos : ℕ}
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

set_option maxHeartbeats 600000 in
/-- Verification of `compPackChangesProc` with a general frame above `splitBase + splitVerts.length`:
packs every branch's `Read.LSFChangeAt` record into `[heap + 1 + numTouched + k, outEnd)`, stores
the `k` pointers at `[heap + 1 + numTouched, +k)`, zeroes `[outEnd, splitBase + splitVerts.length)`,
and preserves memory outside `[heap + 1 + numTouched, splitBase + splitVerts.length)`. -/
theorem compPackChanges_runs_gen {w k b bZero heap numTouched cntBase splitBase vCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {cuts : Fin k → List (ℕ × ℕ)} {splitVerts : List ℕ}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k)
    (hK_m : mem (b + compOffK) = k) (hVCap_m : mem (b + compOffVCap) = vCap)
    (hb_hdr_w : b + compHdrSize < 2 ^ w)
    (hptr_le : heap + 1 + numTouched + k + k * (2 + 2 * vCap) ≤ cntBase)
    (hsplit_ge : cntBase + k + 2 * (k * vCap) ≤ splitBase)
    (hsplit_w : splitBase + splitVerts.length < 2 ^ w)
    (hcut_bd : ∀ j : Fin k, (cuts j).length + splitVerts.length ≤ vCap)
    (hcnt_m : ∀ j : Fin k, mem (cntBase + j.1) = (cuts j).length)
    (hlog_m : ∀ j : Fin k, ∀ i (hi : i < (cuts j).length),
      mem (cntBase + k + j.1 * vCap + i) = (cuts j)[i].2 ∧
      mem (cntBase + k + k * vCap + j.1 * vCap + i) = (cuts j)[i].1)
    (hsp_m : ListAt mem splitBase splitVerts)
    (hz_ptr : ∀ a, heap + 1 + numTouched ≤ a → a < cntBase → mem a = 0)
    (hz_roots : ∀ j : Fin k, ∀ i, (cuts j).length ≤ i → i < vCap →
      mem (cntBase + k + j.1 * vCap + i) = 0 ∧
      mem (cntBase + k + k * vCap + j.1 * vCap + i) = 0)
    (hz_gap : ∀ a, cntBase + k + 2 * (k * vCap) ≤ a → a < splitBase → mem a = 0) :
    let ptrBase := heap + 1 + numTouched
    let outEnd := ptrBase + k + compPackedPrefixWords cuts splitVerts k
    ∃ st' c,
      Runs w p ω (compPackChangesProc bZero)
        (startState [b, heap, numTouched, cntBase, splitBase, splitVerts.length] mem pos)
        (.returned outEnd) st' c ∧
      (∀ j : Fin k,
        let chgPtr := st'.mem (ptrBase + j.1)
        chgPtr = ptrBase + k + compPackedPrefixWords cuts splitVerts j.1 ∧
        Read.LSFChangeAt st'.mem chgPtr (compBranchChange (cuts j) splitVerts) ∧
        ptrBase + k ≤ chgPtr ∧
        chgPtr + (compBranchChange (cuts j) splitVerts).words ≤ outEnd) ∧
      outEnd ≤ cntBase ∧
      (∀ a, outEnd ≤ a → a < splitBase + splitVerts.length → st'.mem a = 0) ∧
      (∀ a, splitBase + splitVerts.length ≤ a → st'.mem a = mem a) ∧
      (∀ a < ptrBase, st'.mem a = mem a) ∧
      c ≤ 100 * (∑ j : Fin k, (cuts j).length) + 45 * k * splitVerts.length + 260 * k +
        20 * splitVerts.length + 90 := by
  intro ptrBase outEnd
  set rootsBase := cntBase + k
  set fDelBase := cntBase + k + k * vCap
  set numSplits := splitVerts.length
  have hw0 : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hout_le : outEnd ≤ cntBase := by
    have := compPackedPrefixWords_le cuts splitVerts hcut_bd k (le_refl k)
    dsimp only [outEnd, ptrBase]; omega
  -- Prefix (7 assigns)
  let st0 := startState [b, heap, numTouched, cntBase, splitBase, numSplits] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 6 k }
  let st2 : State := { st1 with regs := Function.update st1.regs 7 vCap }
  let st3 : State := { st2 with regs := Function.update st2.regs 8 ptrBase }
  let st4 : State := { st3 with regs := Function.update st3.regs 9 (ptrBase + k) }
  let st5 : State := { st4 with regs := Function.update st4.regs 10 rootsBase }
  let st6 : State := { st5 with regs := Function.update st5.regs 11 fDelBase }
  let st7 : State := { st6 with regs := Function.update st6.regs 12 0 }
  have hp1 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffK)))) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      simp [st0, Expr.eval, BinOp.eval, startState,
        show compOffK < 2 ^ w by dsimp [compOffK, compHdrSize] at hb_hdr_w ⊢; omega,
        show b + compOffK < 2 ^ w by dsimp [compOffK, compHdrSize] at hb_hdr_w ⊢; omega]) hK_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨vCap, Expr.eval_load_of_eq (by
      simp [st1, st0, Expr.eval, BinOp.eval, startState,
        show compOffVCap < 2 ^ w by dsimp [compOffVCap, compHdrSize] at hb_hdr_w ⊢; omega,
        show b + compOffVCap < 2 ^ w by dsimp [compOffVCap, compHdrSize] at hb_hdr_w ⊢; omega]) hVCap_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 8 (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 2))) st2 .normal st3 6 :=
    runs_assign_iff.mpr ⟨ptrBase, by
      simp [st2, st1, st0, Expr.eval, BinOp.eval, startState, ptrBase, hw1,
        show heap + 1 < 2 ^ w by omega, show heap + 1 + numTouched < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 6))) st3 .normal st4 4 :=
    runs_assign_iff.mpr ⟨ptrBase + k, by
      simp [st3, st2, st1, Expr.eval, BinOp.eval, show ptrBase + k < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 10 (.bin .add (.reg 3) (.reg 6))) st4 .normal st5 4 :=
    runs_assign_iff.mpr ⟨rootsBase, by
      simp [st4, st3, st2, st1, st0, Expr.eval, BinOp.eval, startState, rootsBase,
        show cntBase + k < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.bin .mul (.reg 6) (.reg 7)))) st5 .normal st6 6 :=
    runs_assign_iff.mpr ⟨fDelBase, by
      simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, rootsBase, fDelBase,
        show k * vCap < 2 ^ w by omega, show cntBase + k + k * vCap < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 12 (.const 0)) st6 .normal st7 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  -- Loop body
  let loopBody : Stmt :=
    .assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
    .store (.bin .add (.reg 8) (.reg 12)) (.reg 9) ;;
    .assign 14 (.bin .add (.reg 13) (.reg 5)) ;;
    .store (.reg 9) (.reg 14) ;;
    .assign 15 (.bin .mul (.reg 12) (.reg 7)) ;;
    .assign 16 (.bin .add (.reg 10) (.reg 15)) ;;
    .assign 17 (.bin .add (.reg 9) (.const 1)) ;;
    compCopySliceStmt 16 17 13 18 19 ;;
    .assign 17 (.bin .add (.reg 17) (.reg 13)) ;;
    compCopySliceStmt 4 17 5 18 19 ;;
    .assign 17 (.bin .add (.reg 17) (.reg 5)) ;;
    .store (.reg 17) (.reg 13) ;;
    .assign 16 (.bin .add (.reg 11) (.reg 15)) ;;
    .assign 17 (.bin .add (.reg 17) (.const 1)) ;;
    compCopySliceStmt 16 17 13 18 19 ;;
    .assign 9 (.bin .add (.reg 17) (.reg 13)) ;;
    .call 18 bZero [.bin .add (.reg 10) (.reg 15), .reg 13] ;;
    .call 18 bZero [.bin .add (.reg 11) (.reg 15), .reg 13] ;;
    .store (.bin .add (.reg 3) (.reg 12)) (.const 0) ;;
    .assign 12 (.bin .add (.reg 12) (.const 1))
  -- Loop induction over `rem = k - j`
  have hloop : ∀ rem j (s : State), j ≤ k → k - j = rem →
      let cur := ptrBase + k + compPackedPrefixWords cuts splitVerts j
      s.regs 3 = cntBase → s.regs 4 = splitBase → s.regs 5 = numSplits →
      s.regs 6 = k → s.regs 7 = vCap → s.regs 8 = ptrBase → s.regs 9 = cur →
      s.regs 10 = rootsBase → s.regs 11 = fDelBase → s.regs 12 = j →
      (∀ t : Fin k, t.1 < j →
        let chgPtr := ptrBase + k + compPackedPrefixWords cuts splitVerts t.1
        s.mem (ptrBase + t.1) = chgPtr ∧
        Read.LSFChangeAt s.mem chgPtr (compBranchChange (cuts t) splitVerts) ∧
        s.mem (cntBase + t.1) = 0 ∧
        (∀ i < vCap, s.mem (rootsBase + t.1 * vCap + i) = 0 ∧ s.mem (fDelBase + t.1 * vCap + i) = 0)) →
      (∀ a, cur ≤ a → a < cntBase → s.mem a = 0) →
      (∀ t : Fin k, j ≤ t.1 → s.mem (cntBase + t.1) = (cuts t).length ∧
        (∀ i (hi : i < (cuts t).length),
          s.mem (rootsBase + t.1 * vCap + i) = (cuts t)[i].2 ∧
          s.mem (fDelBase + t.1 * vCap + i) = (cuts t)[i].1) ∧
        (∀ i, (cuts t).length ≤ i → i < vCap →
          s.mem (rootsBase + t.1 * vCap + i) = 0 ∧ s.mem (fDelBase + t.1 * vCap + i) = 0)) →
      (∀ a, cntBase + k + 2 * (k * vCap) ≤ a → a < splitBase → s.mem a = 0) →
      ListAt s.mem splitBase splitVerts →
      (∀ a, splitBase + numSplits ≤ a → s.mem a = mem a) →
      (∀ a < ptrBase, s.mem a = mem a) →
      ∃ stL cL,
        Runs w p ω (.loop (.bin .lt (.reg 12) (.reg 6)) loopBody) s .normal stL cL ∧
        stL.regs 4 = splitBase ∧ stL.regs 5 = numSplits ∧ stL.regs 9 = outEnd ∧
        (∀ t : Fin k,
          let chgPtr := ptrBase + k + compPackedPrefixWords cuts splitVerts t.1
          stL.mem (ptrBase + t.1) = chgPtr ∧
          Read.LSFChangeAt stL.mem chgPtr (compBranchChange (cuts t) splitVerts) ∧
          stL.mem (cntBase + t.1) = 0 ∧
          (∀ i < vCap, stL.mem (rootsBase + t.1 * vCap + i) = 0 ∧ stL.mem (fDelBase + t.1 * vCap + i) = 0)) ∧
        (∀ a, outEnd ≤ a → a < cntBase → stL.mem a = 0) ∧
        (∀ a, cntBase + k + 2 * (k * vCap) ≤ a → a < splitBase → stL.mem a = 0) ∧
        (∀ a, splitBase + numSplits ≤ a → stL.mem a = mem a) ∧
        (∀ a < ptrBase, stL.mem a = mem a) ∧
        cL ≤ 100 * ((Finset.univ.filter fun t : Fin k => j ≤ t.1).sum fun t => (cuts t).length) +
          rem * (45 * numSplits + 260) + 6 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrem cur _ hr4 hr5 hr6 _ _ hr9 _ _ hr12 hdone hz_cur _ hgap _ habove hbelow
      have hjk : j = k := by omega
      subst hjk
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr12, hr6],
        rfl, rfl, by simp [Expr.size]⟩), hr4, hr5, hr9, fun t => hdone t t.2, hz_cur, hgap, habove,
        hbelow, by omega⟩
    | succ rem ih =>
      intro j s hj hrem cur hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hdone hz_cur hrest hgap hsp habove hbelow
      have hjlt : j < k := by omega
      let jf : Fin k := ⟨j, hjlt⟩
      set cnt := (cuts jf).length
      set wJ := (compBranchChange (cuts jf) splitVerts).words
      have hwJ_eq : wJ = 2 + 2 * cnt + numSplits := compBranchChange_words (cuts jf) splitVerts
      have hcur_next : cur + wJ = ptrBase + k + compPackedPrefixWords cuts splitVerts (j + 1) := by
        dsimp only [cur, wJ, jf]; rw [compPackedPrefixWords_succ cuts splitVerts hjlt]; omega
      have hcur_next_le : cur + wJ ≤ cntBase := by
        rw [hcur_next]
        have := compPackedPrefixWords_le cuts splitVerts hcut_bd (j + 1) (by omega)
        have hmul : (j + 1) * (2 + 2 * vCap) ≤ k * (2 + 2 * vCap) := Nat.mul_le_mul_right _ (by omega)
        omega
      have hjv_le : (j + 1) * vCap ≤ k * vCap := Nat.mul_le_mul_right vCap (by omega)
      have hjv_eq : (j + 1) * vCap = j * vCap + vCap := by ring
      have hcnt_le : cnt + numSplits ≤ vCap := hcut_bd jf
      obtain ⟨hcnt_js, hlog_js, hzr_js⟩ := hrest jf (le_refl j)
      -- Execute 1 iteration of `loopBody`
      let s1 : State := { s with regs := Function.update s.regs 13 cnt }
      let s2 : State := { s1 with mem := Function.update s1.mem (ptrBase + j) cur }
      let s3 : State := { s2 with regs := Function.update s2.regs 14 (cnt + numSplits) }
      let s4 : State := { s3 with mem := Function.update s3.mem cur (cnt + numSplits) }
      let s5 : State := { s4 with regs := Function.update s4.regs 15 (j * vCap) }
      let s6 : State := { s5 with regs := Function.update s5.regs 16 (rootsBase + j * vCap) }
      let s7 : State := { s6 with regs := Function.update s6.regs 17 (cur + 1) }
      have hcnt_js' : s.mem (cntBase + j) = cnt := hcnt_js
      have hb1 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 3) (.reg 12)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨cnt, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr3, hr12, show cntBase + j < 2 ^ w by omega]) hcnt_js',
          rfl, rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.store (.bin .add (.reg 8) (.reg 12)) (.reg 9)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨ptrBase + j, cur,
          by simp [s1, Expr.eval, BinOp.eval, hr8, hr12, show ptrBase + j < 2 ^ w by omega],
          by simp [s1, Expr.eval, hr9], rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 5))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨cnt + numSplits, by
          simp [s2, s1, Expr.eval, BinOp.eval, hr5, show cnt + numSplits < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb4 : Runs w p ω (.store (.reg 9) (.reg 14)) s3 .normal s4 3 :=
        runs_store_iff.mpr ⟨cur, cnt + numSplits, by simp [s3, s2, s1, Expr.eval, hr9],
          by simp [s3, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hb5 : Runs w p ω (.assign 15 (.bin .mul (.reg 12) (.reg 7))) s4 .normal s5 4 :=
        runs_assign_iff.mpr ⟨j * vCap, by
          simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr12, hr7, show j * vCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb6 : Runs w p ω (.assign 16 (.bin .add (.reg 10) (.reg 15))) s5 .normal s6 4 :=
        runs_assign_iff.mpr ⟨rootsBase + j * vCap, by
          simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr10, show rootsBase + j * vCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb7 : Runs w p ω (.assign 17 (.bin .add (.reg 9) (.const 1))) s6 .normal s7 4 :=
        runs_assign_iff.mpr ⟨cur + 1, by
          simp [s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr9, hw1, show cur + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨s8, c8, hb8, hr8_pres, hcp8, hfr8, hc8⟩ :=
        compCopySlice_runs (rSrc := 16) (rDst := 17) (rLen := 13) (rIdx := 18) (rTmp := 19)
          (src := rootsBase + j * vCap) (dst := cur + 1) (len := cnt)
          (p := p) (ω := ω) (st := s7) (by decide) hw16
          (by omega) (by omega) (Or.inr (by omega))
          (by simp [s7, s6]) (by simp [s7]) (by simp [s7, s6, s5, s4, s3, s2, s1])
      let s9 : State := { s8 with regs := Function.update s8.regs 17 (cur + 1 + cnt) }
      have hb9 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.reg 13))) s8 .normal s9 4 :=
        runs_assign_iff.mpr ⟨cur + 1 + cnt, by
          simp [Expr.eval, BinOp.eval, hr8_pres 17 (by decide) (by decide),
            hr8_pres 13 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, show cur + 1 + cnt < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨s10, c10, hb10, hr10_pres, hcp10, hfr10, hc10⟩ :=
        compCopySlice_runs (rSrc := 4) (rDst := 17) (rLen := 5) (rIdx := 18) (rTmp := 19)
          (src := splitBase) (dst := cur + 1 + cnt) (len := numSplits)
          (p := p) (ω := ω) (st := s9) (by decide) hw16
          (by omega) (by omega) (Or.inr (by omega))
          (by simp [s9, hr8_pres 4 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr4])
          (by simp [s9])
          (by simp [s9, hr8_pres 5 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr5])
      let s11 : State := { s10 with regs := Function.update s10.regs 17 (cur + 1 + cnt + numSplits) }
      let s12 : State := { s11 with mem := Function.update s11.mem (cur + 1 + cnt + numSplits) cnt }
      let s13 : State := { s12 with regs := Function.update s12.regs 16 (fDelBase + j * vCap) }
      let s14 : State := { s13 with regs := Function.update s13.regs 17 (cur + 2 + cnt + numSplits) }
      have hb11 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.reg 5))) s10 .normal s11 4 :=
        runs_assign_iff.mpr ⟨cur + 1 + cnt + numSplits, by
          simp [Expr.eval, BinOp.eval, hr10_pres 17 (by decide) (by decide),
            hr10_pres 5 (by decide) (by decide), s9, hr8_pres 5 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, hr5, show cur + 1 + cnt + numSplits < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb12 : Runs w p ω (.store (.reg 17) (.reg 13)) s11 .normal s12 3 :=
        runs_store_iff.mpr ⟨cur + 1 + cnt + numSplits, cnt,
          by simp [s11, Expr.eval],
          by simp [s11, Expr.eval, hr10_pres 13 (by decide) (by decide), s9,
            hr8_pres 13 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1],
          rfl, rfl, by simp [Expr.size]⟩
      have hb13 : Runs w p ω (.assign 16 (.bin .add (.reg 11) (.reg 15))) s12 .normal s13 4 :=
        runs_assign_iff.mpr ⟨fDelBase + j * vCap, by
          simp [s12, s11, Expr.eval, BinOp.eval, hr10_pres 11 (by decide) (by decide),
            hr10_pres 15 (by decide) (by decide), s9, hr8_pres 11 (by decide) (by decide),
            hr8_pres 15 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr11,
            show fDelBase + j * vCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb14 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.const 1))) s13 .normal s14 4 :=
        runs_assign_iff.mpr ⟨cur + 2 + cnt + numSplits, by
          simp [s13, s12, s11, Expr.eval, BinOp.eval, hw1,
            show cur + 1 + cnt + numSplits + 1 = cur + 2 + cnt + numSplits by omega,
            show cur + 2 + cnt + numSplits < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨s15, c15, hb15, hr15_pres, hcp15, hfr15, hc15⟩ :=
        compCopySlice_runs (rSrc := 16) (rDst := 17) (rLen := 13) (rIdx := 18) (rTmp := 19)
          (src := fDelBase + j * vCap) (dst := cur + 2 + cnt + numSplits) (len := cnt)
          (p := p) (ω := ω) (st := s14) (by decide) hw16
          (by omega) (by omega) (Or.inr (by omega))
          (by simp [s14, s13]) (by simp [s14])
          (by simp [s14, s13, s12, s11, hr10_pres 13 (by decide) (by decide), s9,
            hr8_pres 13 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1])
      let s16 : State := { s15 with regs := Function.update s15.regs 9 (cur + wJ) }
      have hb16 : Runs w p ω (.assign 9 (.bin .add (.reg 17) (.reg 13))) s15 .normal s16 4 :=
        runs_assign_iff.mpr ⟨cur + wJ, by
          simp [Expr.eval, BinOp.eval, hr15_pres 17 (by decide) (by decide),
            hr15_pres 13 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 13 (by decide) (by decide), s9, hr8_pres 13 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, show cur + 2 + cnt + numSplits + cnt = cur + wJ by omega,
            show cur + wJ < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      -- Zero branch `jf`'s rootsBuf and fDelBuf slices + `cntBase + j`
      obtain ⟨oZr, stZr, cZr, hrZr, hoZr, hZr_post, hZr_out, hZr_cost⟩ :=
        compZeroRange_call hpZero hw16 (ptr := rootsBase + j * vCap) (len := cnt) (mem := s16.mem) (pos := s16.pos) (ω := ω) (by omega)
      let s17 : State := { mem := stZr.mem, regs := Function.update s16.regs 18 0, pos := stZr.pos }
      have hb17 : Runs w p ω (.call 18 bZero [.bin .add (.reg 10) (.reg 15), .reg 13]) s16 .normal s17 (4 + cZr + 1) :=
        runs_call_iff.mpr ⟨[rootsBase + j * vCap, cnt], compZeroRangeProc, oZr, stZr, cZr,
          by simp [s16, evalArgs, Expr.eval, BinOp.eval,
            hr15_pres 10 (by decide) (by decide), hr15_pres 15 (by decide) (by decide),
            hr15_pres 13 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 10 (by decide) (by decide), hr10_pres 15 (by decide) (by decide),
            hr10_pres 13 (by decide) (by decide), s9, hr8_pres 10 (by decide) (by decide),
            hr8_pres 15 (by decide) (by decide), hr8_pres 13 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, hr10, show rootsBase + j * vCap < 2 ^ w by omega],
          hpZero, hrZr, rfl, by simp [s17, hoZr], by simp [argsSize, Expr.size]⟩
      obtain ⟨oZf, stZf, cZf, hrZf, hoZf, hZf_post, hZf_out, hZf_cost⟩ :=
        compZeroRange_call hpZero hw16 (ptr := fDelBase + j * vCap) (len := cnt) (mem := s17.mem) (pos := s17.pos) (ω := ω) (by omega)
      let s18 : State := { mem := stZf.mem, regs := Function.update s17.regs 18 0, pos := stZf.pos }
      have hb18 : Runs w p ω (.call 18 bZero [.bin .add (.reg 11) (.reg 15), .reg 13]) s17 .normal s18 (4 + cZf + 1) :=
        runs_call_iff.mpr ⟨[fDelBase + j * vCap, cnt], compZeroRangeProc, oZf, stZf, cZf,
          by simp [s17, s16, evalArgs, Expr.eval, BinOp.eval,
            hr15_pres 11 (by decide) (by decide), hr15_pres 15 (by decide) (by decide),
            hr15_pres 13 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 11 (by decide) (by decide), hr10_pres 15 (by decide) (by decide),
            hr10_pres 13 (by decide) (by decide), s9, hr8_pres 11 (by decide) (by decide),
            hr8_pres 15 (by decide) (by decide), hr8_pres 13 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, hr11, show fDelBase + j * vCap < 2 ^ w by omega],
          hpZero, hrZf, rfl, by simp [s18, hoZf], by simp [argsSize, Expr.size]⟩
      let s19 : State := { s18 with mem := Function.update s18.mem (cntBase + j) 0 }
      let s20 : State := { s19 with regs := Function.update s19.regs 12 (j + 1) }
      have hb19 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 12)) (.const 0)) s18 .normal s19 5 :=
        runs_store_iff.mpr ⟨cntBase + j, 0,
          by simp [s18, s17, s16, Expr.eval, BinOp.eval,
            hr15_pres 3 (by decide) (by decide), hr15_pres 12 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 3 (by decide) (by decide), hr10_pres 12 (by decide) (by decide), s9,
            hr8_pres 3 (by decide) (by decide), hr8_pres 12 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, hr3, hr12, show cntBase + j < 2 ^ w by omega],
          by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
      have hb20 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) s19 .normal s20 4 :=
        runs_assign_iff.mpr ⟨j + 1, by
          simp [s19, s18, s17, s16, Expr.eval, BinOp.eval,
            hr15_pres 12 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 12 (by decide) (by decide), s9, hr8_pres 12 (by decide) (by decide),
            s7, s6, s5, s4, s3, s2, s1, hr12, hw1, show j + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω loopBody s .normal s20 (c8 + c10 + c15 + cZr + cZf + 90) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, c8 + c10 + c15 + cZr + cZf + 84, hb1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, c8 + c10 + c15 + cZr + cZf + 78, hb2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 4, c8 + c10 + c15 + cZr + cZf + 73, hb3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 3, c8 + c10 + c15 + cZr + cZf + 69, hb4,
        runs_seq_iff.mpr (Or.inr ⟨s5, 4, c8 + c10 + c15 + cZr + cZf + 64, hb5,
        runs_seq_iff.mpr (Or.inr ⟨s6, 4, c8 + c10 + c15 + cZr + cZf + 59, hb6,
        runs_seq_iff.mpr (Or.inr ⟨s7, 4, c8 + c10 + c15 + cZr + cZf + 54, hb7,
        runs_seq_iff.mpr (Or.inr ⟨s8, c8, c10 + c15 + cZr + cZf + 53, hb8,
        runs_seq_iff.mpr (Or.inr ⟨s9, 4, c10 + c15 + cZr + cZf + 48, hb9,
        runs_seq_iff.mpr (Or.inr ⟨s10, c10, c15 + cZr + cZf + 47, hb10,
        runs_seq_iff.mpr (Or.inr ⟨s11, 4, c15 + cZr + cZf + 42, hb11,
        runs_seq_iff.mpr (Or.inr ⟨s12, 3, c15 + cZr + cZf + 38, hb12,
        runs_seq_iff.mpr (Or.inr ⟨s13, 4, c15 + cZr + cZf + 33, hb13,
        runs_seq_iff.mpr (Or.inr ⟨s14, 4, c15 + cZr + cZf + 28, hb14,
        runs_seq_iff.mpr (Or.inr ⟨s15, c15, cZr + cZf + 27, hb15,
        runs_seq_iff.mpr (Or.inr ⟨s16, 4, cZr + cZf + 22, hb16,
        runs_seq_iff.mpr (Or.inr ⟨s17, 4 + cZr + 1, cZf + 16, hb17,
        runs_seq_iff.mpr (Or.inr ⟨s18, 4 + cZf + 1, 10, hb18,
        runs_seq_iff.mpr (Or.inr ⟨s19, 5, 4, hb19, hb20, by omega⟩), by omega⟩), by omega⟩),
          by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩),
          by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩),
          by omega⟩), by omega⟩)
      -- Memory frame of 1 iteration
      have hstep_fr : ∀ a, a ≠ ptrBase + j → (a < cur ∨ cur + wJ ≤ a) → a ≠ cntBase + j →
          (a < rootsBase + j * vCap ∨ rootsBase + j * vCap + cnt ≤ a) →
          (a < fDelBase + j * vCap ∨ fDelBase + j * vCap + cnt ≤ a) → s20.mem a = s.mem a := by
        intro a h1 h2 h3 h4 h5
        have h19 : s20.mem a = stZf.mem a := by dsimp only [s20, s19]; rw [Function.update_of_ne h3]
        have h15 : s15.mem a = s12.mem a := hfr15 a (by omega)
        have h12 : s12.mem a = s10.mem a := by dsimp only [s12, s11]; rw [Function.update_of_ne (by omega)]
        have h10 : s10.mem a = s8.mem a := hfr10 a (by omega)
        have h8 : s8.mem a = s4.mem a := hfr8 a (by omega)
        have h4m : s4.mem a = s2.mem a := by dsimp only [s4, s3]; rw [Function.update_of_ne (by omega)]
        have h2m : s2.mem a = s.mem a := by dsimp only [s2, s1]; rw [Function.update_of_ne h1]
        rw [h19, hZf_out a h5, hZr_out a h4, h15, h12, h10, h8, h4m, h2m]
      -- Verify `Read.LSFChangeAt` for branch `jf`
      have hchg_jf : Read.LSFChangeAt s20.mem cur (compBranchChange (cuts jf) splitVerts) := by
        have hkeep : ∀ a, cur ≤ a → a < cur + wJ → s20.mem a = s15.mem a := fun a ha1 ha2 => by
          have : s20.mem a = stZf.mem a := by dsimp only [s20, s19]; rw [Function.update_of_ne (by omega)]
          rw [this, hZf_out a (Or.inl (by omega)), hZr_out a (Or.inl (by omega))]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hkeep cur (le_refl _) (by omega), hfr15 cur (Or.inl (by omega))]
          have : s12.mem cur = s10.mem cur := by dsimp only [s12, s11]; rw [Function.update_of_ne (by omega)]
          rw [this, hfr10 cur (Or.inl (by omega)), hfr8 cur (Or.inl (by omega))]
          dsimp only [s7, s6, s5, s4, compBranchChange, cnt, numSplits]; rw [Function.update_self]; simp
        · intro i hi
          have hi' : i < cnt + numSplits := by simp [compBranchChange] at hi; exact hi
          rw [hkeep (cur + 1 + i) (by omega) (by omega), hfr15 (cur + 1 + i) (Or.inl (by omega))]
          have : s12.mem (cur + 1 + i) = s10.mem (cur + 1 + i) := by
            dsimp only [s12, s11]; rw [Function.update_of_ne (by omega)]
          rw [this]
          by_cases hic : i < cnt
          · rw [hfr10 (cur + 1 + i) (Or.inl (by omega)), hcp8 i hic]
            have hm4 : s7.mem (rootsBase + j * vCap + i) = s.mem (rootsBase + j * vCap + i) := by
              dsimp only [s7, s6, s5, s4, s3, s2, s1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            rw [hm4, (hlog_js i hic).1]
            dsimp only [compBranchChange] at hi ⊢
            rw [List.getElem_append_left (by simp; exact hic), List.getElem_map]
          · have his : i - cnt < numSplits := by omega
            have hidx : cur + 1 + i = cur + 1 + cnt + (i - cnt) := by omega
            rw [hidx, hcp10 (i - cnt) his]
            have hm9 : s9.mem (splitBase + (i - cnt)) = s.mem (splitBase + (i - cnt)) := by
              dsimp only [s9]
              rw [hfr8 _ (Or.inr (by omega))]
              dsimp only [s7, s6, s5, s4, s3, s2, s1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            rw [hm9, hsp (i - cnt) his]
            dsimp only [compBranchChange] at hi ⊢
            rw [List.getElem_append_right (by simp; omega)]
            simp [cnt]
        · have hrl : (compBranchChange (cuts jf) splitVerts).roots.length = cnt + numSplits := by
            simp [compBranchChange, cnt, numSplits]
          rw [hrl, show cur + 1 + (cnt + numSplits) = cur + 1 + cnt + numSplits by omega]
          rw [hkeep _ (by omega) (by omega), hfr15 _ (Or.inl (by omega))]
          dsimp only [s14, s13, s12, compBranchChange, cnt]; rw [Function.update_self]; simp
        · intro i hi
          have hi' : i < cnt := by simp [compBranchChange] at hi; exact hi
          have hrl : (compBranchChange (cuts jf) splitVerts).roots.length = cnt + numSplits := by
            simp [compBranchChange, cnt, numSplits]
          rw [hrl, show cur + 2 + (cnt + numSplits) + i = cur + 2 + cnt + numSplits + i by omega]
          rw [hkeep _ (by omega) (by omega), hcp15 i hi']
          have hm14 : s14.mem (fDelBase + j * vCap + i) = s.mem (fDelBase + j * vCap + i) := by
            dsimp only [s14, s13, s12, s11]
            rw [Function.update_of_ne (by omega), hfr10 _ (Or.inr (by omega)),
              hfr8 _ (Or.inr (by omega))]
            dsimp only [s7, s6, s5, s4, s3, s2, s1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          rw [hm14, (hlog_js i hi').2]; simp [compBranchChange]
      -- Verify IH invariants for `j + 1`
      have hdone1 : ∀ t : Fin k, t.1 < j + 1 →
          let chgPtr := ptrBase + k + compPackedPrefixWords cuts splitVerts t.1
          s20.mem (ptrBase + t.1) = chgPtr ∧
          Read.LSFChangeAt s20.mem chgPtr (compBranchChange (cuts t) splitVerts) ∧
          s20.mem (cntBase + t.1) = 0 ∧
          (∀ i < vCap, s20.mem (rootsBase + t.1 * vCap + i) = 0 ∧ s20.mem (fDelBase + t.1 * vCap + i) = 0) := by
        intro t ht
        by_cases htj : t = jf
        · subst htj
          dsimp only [jf]
          refine ⟨?_, hchg_jf, by simp [s20, s19], fun i hi => ⟨?_, ?_⟩⟩
          · have : s20.mem (ptrBase + j) = stZf.mem (ptrBase + j) := by
              dsimp only [s20, s19]; rw [Function.update_of_ne (by omega)]
            rw [this, hZf_out _ (Or.inl (by omega)), hZr_out _ (Or.inl (by omega)),
              hfr15 _ (Or.inl (by omega))]
            have : s12.mem (ptrBase + j) = s10.mem (ptrBase + j) := by
              dsimp only [s12, s11]; rw [Function.update_of_ne (by omega)]
            rw [this, hfr10 _ (Or.inl (by omega)), hfr8 _ (Or.inl (by omega))]
            dsimp only [s7, s6, s5, s4, s3, s2]
            rw [Function.update_of_ne (by omega), Function.update_self]
          · by_cases hic : i < cnt
            · have : s20.mem (rootsBase + j * vCap + i) = stZf.mem (rootsBase + j * vCap + i) := by
                dsimp only [s20, s19]; rw [Function.update_of_ne (by omega)]
              rw [this, hZf_out _ (Or.inl (by omega))]; exact hZr_post i hic
            · exact (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
                (Or.inl (by omega))).trans (hzr_js i (by omega) hi).1
          · by_cases hic : i < cnt
            · have : s20.mem (fDelBase + j * vCap + i) = stZf.mem (fDelBase + j * vCap + i) := by
                dsimp only [s20, s19]; rw [Function.update_of_ne (by omega)]
              rw [this]; exact hZf_post i hic
            · exact (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
                (Or.inr (by omega))).trans (hzr_js i (by omega) hi).2
        · have htlt : t.1 < j := by have : t.1 ≠ j := fun h => htj (Fin.ext h); omega
          obtain ⟨hp_t, hchg_t, hc_t, hzr_t⟩ := hdone t htlt
          have hpref_le : compPackedPrefixWords cuts splitVerts t.1 +
              (compBranchChange (cuts t) splitVerts).words ≤ compPackedPrefixWords cuts splitVerts j := by
            rw [← compPackedPrefixWords_succ cuts splitVerts t.2]
            exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
          have ht_le : (t.1 + 1) * vCap ≤ j * vCap := Nat.mul_le_mul_right vCap (by omega)
          have ht_eq : (t.1 + 1) * vCap = t.1 * vCap + vCap := by ring
          have hchg_t' : Read.LSFChangeAt s20.mem (ptrBase + k + compPackedPrefixWords cuts splitVerts t.1)
              (compBranchChange (cuts t) splitVerts) := by
            have hfr_t : ∀ a, ptrBase + k + compPackedPrefixWords cuts splitVerts t.1 ≤ a →
                a < ptrBase + k + compPackedPrefixWords cuts splitVerts t.1 +
                  (compBranchChange (cuts t) splitVerts).words → s20.mem a = s.mem a := fun a ha1 ha2 =>
              hstep_fr a (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
            have hw_t : (compBranchChange (cuts t) splitVerts).words =
                2 + (compBranchChange (cuts t) splitVerts).roots.length +
                  (compBranchChange (cuts t) splitVerts).fDel.length := by
              simp [Read.LSFChange.words, Read.LSFChange.size]; omega
            refine ⟨(hfr_t _ (le_refl _) (by omega)).trans hchg_t.1,
              fun i hi => (hfr_t _ (by omega) (by omega)).trans (hchg_t.2.1 i hi),
              (hfr_t _ (by omega) (by omega)).trans hchg_t.2.2.1,
              fun i hi => (hfr_t _ (by omega) (by omega)).trans (hchg_t.2.2.2 i hi)⟩
          refine ⟨(hstep_fr _ (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans hp_t,
            hchg_t',
            (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans hc_t,
            fun i hi => ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (hzr_t i hi).1,
              (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (hzr_t i hi).2⟩⟩
      have hrest1 : ∀ t : Fin k, j + 1 ≤ t.1 → s20.mem (cntBase + t.1) = (cuts t).length ∧
          (∀ i (hi : i < (cuts t).length),
            s20.mem (rootsBase + t.1 * vCap + i) = (cuts t)[i].2 ∧
            s20.mem (fDelBase + t.1 * vCap + i) = (cuts t)[i].1) ∧
          (∀ i, (cuts t).length ≤ i → i < vCap →
            s20.mem (rootsBase + t.1 * vCap + i) = 0 ∧ s20.mem (fDelBase + t.1 * vCap + i) = 0) := by
        intro t ht
        obtain ⟨h1, h2, h3⟩ := hrest t (by omega)
        have hjt : (j + 1) * vCap ≤ t.1 * vCap := Nat.mul_le_mul_right vCap ht
        have ht_le : (t.1 + 1) * vCap ≤ k * vCap := Nat.mul_le_mul_right vCap (by omega)
        have ht_eq : (t.1 + 1) * vCap = t.1 * vCap + vCap := by ring
        have hct_le : (cuts t).length ≤ vCap := by have := hcut_bd t; omega
        refine ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans h1,
          fun i hi => ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (h2 i hi).1,
            (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (h2 i hi).2⟩,
          fun i hi1 hi2 => ⟨(hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (h3 i hi1 hi2).1,
            (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (h3 i hi1 hi2).2⟩⟩
      obtain ⟨stL, cL, hrL, hrL4, hrL5, hrL9, hdoneL, hz_outL, hgapL, haboveL, hbelowL, hcL⟩ :=
        ih (j + 1) s20 (by omega) (by omega)
          (by simp [s20, s19, s18, s17, s16, hr15_pres 3 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 3 (by decide) (by decide), s9, hr8_pres 3 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr3])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 4 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 4 (by decide) (by decide), s9, hr8_pres 4 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr4])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 5 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 5 (by decide) (by decide), s9, hr8_pres 5 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr5])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 6 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 6 (by decide) (by decide), s9, hr8_pres 6 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr6])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 7 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 7 (by decide) (by decide), s9, hr8_pres 7 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr7])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 8 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 8 (by decide) (by decide), s9, hr8_pres 8 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr8])
          (by simp [s20, s19, s18, s17, s16, hcur_next])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 10 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 10 (by decide) (by decide), s9, hr8_pres 10 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr10])
          (by simp [s20, s19, s18, s17, s16, hr15_pres 11 (by decide) (by decide), s14, s13, s12, s11,
            hr10_pres 11 (by decide) (by decide), s9, hr8_pres 11 (by decide) (by decide), s7, s6, s5, s4, s3, s2, s1, hr11])
          (by simp [s20]) hdone1
          (fun a ha1 ha2 => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (hz_cur a (by omega) ha2))
          hrest1
          (fun a ha1 ha2 => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (hgap a ha1 ha2))
          (fun i hi => (hstep_fr _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (hsp i hi))
          (fun a ha => (hstep_fr a (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (habove a ha))
          (fun a ha => (hstep_fr a (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (hbelow a ha))
      have hcond : (Expr.bin .lt (.reg 12) (.reg 6)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr12, hr6, hjlt, hw1]
      have hsum_split : ((Finset.univ.filter fun t : Fin k => j ≤ t.1).sum fun t => (cuts t).length) =
          cnt + ((Finset.univ.filter fun t : Fin k => j + 1 ≤ t.1).sum fun t => (cuts t).length) := by
        have hpart : (Finset.univ.filter fun t : Fin k => j ≤ t.1) =
            insert jf (Finset.univ.filter fun t : Fin k => j + 1 ≤ t.1) := by
          ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, jf]
          omega
        rw [hpart, Finset.sum_insert (by simp [jf])]
      have hmul : (rem + 1) * (45 * numSplits + 260) = rem * (45 * numSplits + 260) + (45 * numSplits + 260) := by ring
      exact ⟨stL, 3 + (c8 + c10 + c15 + cZr + cZf + 90) + cL + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s20, c8 + c10 + c15 + cZr + cZf + 90, cL, hcond, by decide,
          hbody, hrL, by simp [Expr.size]⟩)),
        hrL4, hrL5, hrL9, hdoneL, hz_outL, hgapL, haboveL, hbelowL, by omega⟩
  -- Run loop from `j = 0`, zero `[splitBase, splitBase + numSplits)`, and return `outEnd`
  obtain ⟨stL, cL, hrL, hrL4, hrL5, hrL9, hdoneL, hz_outL, hgapL, haboveL, hbelowL, hcL⟩ :=
    hloop k 0 st7 (Nat.zero_le k) (by omega)
      (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st7, st6, st5, st4, st3, st2, st1])
      (by simp [st7, st6, st5, st4, st3, st2])
      (by simp [st7, st6, st5, st4, st3])
      (by simp [st7, st6, st5, st4, compPackedPrefixWords])
      (by simp [st7, st6, st5]) (by simp [st7, st6]) (by simp [st7])
      (fun _ h => by omega)
      (fun a ha1 ha2 => hz_ptr a (by simp [compPackedPrefixWords] at ha1; omega) ha2)
      (fun t _ => ⟨hcnt_m t, hlog_m t, hz_roots t⟩)
      hz_gap hsp_m (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨oZs, stZs, cZs, hrZs, hoZs, hZs_post, hZs_out, hZs_cost⟩ :=
    compZeroRange_call hpZero hw16 (ptr := splitBase) (len := numSplits) (mem := stL.mem) (pos := stL.pos) (ω := ω) (by omega)
  let stEnd : State := { mem := stZs.mem, regs := Function.update stL.regs 18 0, pos := stZs.pos }
  have hcallZs : Runs w p ω (.call 18 bZero [.reg 4, .reg 5]) stL .normal stEnd (2 + cZs + 1) :=
    runs_call_iff.mpr ⟨[splitBase, numSplits], compZeroRangeProc, oZs, stZs, cZs,
      by simp [evalArgs, Expr.eval, hrL4, hrL5], hpZero, hrZs, rfl, by simp [stEnd, hoZs], by simp [argsSize, Expr.size]⟩
  have hret : Runs w p ω (.ret (.reg 9)) stEnd (.returned outEnd) stEnd 2 :=
    runs_ret_iff.mpr ⟨outEnd, by simp [stEnd, Expr.eval, hrL9], rfl, rfl, by simp [Expr.size]⟩
  have hfull : Runs w p ω (compPackChangesProc bZero) st0 (.returned outEnd) stEnd (cL + cZs + 46) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, cL + cZs + 40, hp1,
    runs_seq_iff.mpr (Or.inr ⟨st2, 5, cL + cZs + 34, hp2,
    runs_seq_iff.mpr (Or.inr ⟨st3, 6, cL + cZs + 27, hp3,
    runs_seq_iff.mpr (Or.inr ⟨st4, 4, cL + cZs + 22, hp4,
    runs_seq_iff.mpr (Or.inr ⟨st5, 4, cL + cZs + 17, hp5,
    runs_seq_iff.mpr (Or.inr ⟨st6, 6, cL + cZs + 10, hp6,
    runs_seq_iff.mpr (Or.inr ⟨st7, 2, cL + cZs + 7, hp7,
    runs_seq_iff.mpr (Or.inr ⟨stL, cL, cZs + 6, hrL,
    runs_seq_iff.mpr (Or.inr ⟨stEnd, 2 + cZs + 1, 2, hcallZs, hret, by omega⟩), by omega⟩),
      by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  refine ⟨stEnd, cL + cZs + 46, hfull, ?_, hout_le, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨hp_j, hchg_j, _, _⟩ := hdoneL j
    have hpref_le : compPackedPrefixWords cuts splitVerts j.1 +
        (compBranchChange (cuts j) splitVerts).words ≤ compPackedPrefixWords cuts splitVerts k := by
      rw [← compPackedPrefixWords_succ cuts splitVerts j.2]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    have hw_j : (compBranchChange (cuts j) splitVerts).words =
        2 + (compBranchChange (cuts j) splitVerts).roots.length +
          (compBranchChange (cuts j) splitVerts).fDel.length := by
      simp [Read.LSFChange.words, Read.LSFChange.size]; omega
    have hptr_j : stEnd.mem (ptrBase + j.1) = ptrBase + k + compPackedPrefixWords cuts splitVerts j.1 :=
      (hZs_out _ (Or.inl (by have := j.2; omega))).trans hp_j
    refine ⟨hptr_j, ?_, by omega, by dsimp [outEnd]; omega⟩
    rw [hptr_j]
    refine ⟨(hZs_out _ (Or.inl (by omega))).trans hchg_j.1,
      fun i hi => (hZs_out _ (Or.inl (by omega))).trans (hchg_j.2.1 i hi),
      (hZs_out _ (Or.inl (by omega))).trans hchg_j.2.2.1,
      fun i hi => (hZs_out _ (Or.inl (by omega))).trans (hchg_j.2.2.2 i hi)⟩
  · intro a ha ha_lt
    by_cases h1 : a < cntBase
    · exact (hZs_out a (Or.inl (by omega))).trans (hz_outL a ha h1)
    · by_cases h2 : a < rootsBase
      · let jf : Fin k := ⟨a - cntBase, by omega⟩
        have ha_eq : a = cntBase + jf.1 := by dsimp [jf]; omega
        exact (hZs_out a (Or.inl (by omega))).trans (ha_eq ▸ (hdoneL jf).2.2.1)
      · by_cases h3 : a < fDelBase
        · have hvPos : 0 < vCap := by
            have : 0 < k * vCap := by omega
            exact Nat.pos_of_mul_pos_left this
          let jf : Fin k := ⟨(a - rootsBase) / vCap, (Nat.div_lt_iff_lt_mul hvPos).mpr (by omega)⟩
          have ha_eq : a = rootsBase + jf.1 * vCap + (a - rootsBase) % vCap := by
            have hdm := Nat.div_add_mod (a - rootsBase) vCap
            have hmc := Nat.mul_comm vCap ((a - rootsBase) / vCap)
            dsimp [jf]; omega
          exact (hZs_out a (Or.inl (by omega))).trans
            (ha_eq ▸ ((hdoneL jf).2.2.2 _ (Nat.mod_lt _ hvPos)).1)
        · by_cases h4 : a < cntBase + k + 2 * (k * vCap)
          · have hvPos : 0 < vCap := by
              have : 0 < k * vCap := by omega
              exact Nat.pos_of_mul_pos_left this
            let jf : Fin k := ⟨(a - fDelBase) / vCap, (Nat.div_lt_iff_lt_mul hvPos).mpr (by omega)⟩
            have ha_eq : a = fDelBase + jf.1 * vCap + (a - fDelBase) % vCap := by
              have hdm := Nat.div_add_mod (a - fDelBase) vCap
              have hmc := Nat.mul_comm vCap ((a - fDelBase) / vCap)
              dsimp [jf]; omega
            exact (hZs_out a (Or.inl (by omega))).trans
              (ha_eq ▸ ((hdoneL jf).2.2.2 _ (Nat.mod_lt _ hvPos)).2)
          · by_cases h5 : a < splitBase
            · exact (hZs_out a (Or.inl h5)).trans (hgapL a (by omega) h5)
            · have := hZs_post (a - splitBase) (by omega)
              rwa [show splitBase + (a - splitBase) = a by omega] at this
  · intro a ha
    exact (hZs_out a (Or.inr ha)).trans (haboveL a ha)
  · intro a ha
    exact (hZs_out a (Or.inl (by omega))).trans (hbelowL a ha)
  · have hfilt : (Finset.univ.filter fun t : Fin k => 0 ≤ t.1) = Finset.univ := by
      ext t; simp
    rw [hfilt] at hcL
    have hmul : k * (45 * numSplits + 260) = 45 * k * numSplits + 260 * k := by ring
    omega

/-- Verification of `compPackChangesProc` when memory above `splitBase + splitVerts.length` is zero. -/
theorem compPackChanges_runs {w k b bZero heap numTouched cntBase splitBase vCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {cuts : Fin k → List (ℕ × ℕ)} {splitVerts : List ℕ}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k)
    (hK_m : mem (b + compOffK) = k) (hVCap_m : mem (b + compOffVCap) = vCap)
    (hb_hdr_w : b + compHdrSize < 2 ^ w)
    (hptr_le : heap + 1 + numTouched + k + k * (2 + 2 * vCap) ≤ cntBase)
    (hsplit_ge : cntBase + k + 2 * (k * vCap) ≤ splitBase)
    (hsplit_w : splitBase + splitVerts.length < 2 ^ w)
    (hcut_bd : ∀ j : Fin k, (cuts j).length + splitVerts.length ≤ vCap)
    (hcnt_m : ∀ j : Fin k, mem (cntBase + j.1) = (cuts j).length)
    (hlog_m : ∀ j : Fin k, ∀ i (hi : i < (cuts j).length),
      mem (cntBase + k + j.1 * vCap + i) = (cuts j)[i].2 ∧
      mem (cntBase + k + k * vCap + j.1 * vCap + i) = (cuts j)[i].1)
    (hsp_m : ListAt mem splitBase splitVerts)
    (hz_ptr : ∀ a, heap + 1 + numTouched ≤ a → a < cntBase → mem a = 0)
    (hz_roots : ∀ j : Fin k, ∀ i, (cuts j).length ≤ i → i < vCap →
      mem (cntBase + k + j.1 * vCap + i) = 0 ∧
      mem (cntBase + k + k * vCap + j.1 * vCap + i) = 0)
    (hz_gap : ∀ a, cntBase + k + 2 * (k * vCap) ≤ a → a < splitBase → mem a = 0)
    (hz_above : ZeroFrom mem (splitBase + splitVerts.length)) :
    let ptrBase := heap + 1 + numTouched
    let outEnd := ptrBase + k + compPackedPrefixWords cuts splitVerts k
    ∃ st' c,
      Runs w p ω (compPackChangesProc bZero)
        (startState [b, heap, numTouched, cntBase, splitBase, splitVerts.length] mem pos)
        (.returned outEnd) st' c ∧
      (∀ j : Fin k,
        let chgPtr := st'.mem (ptrBase + j.1)
        chgPtr = ptrBase + k + compPackedPrefixWords cuts splitVerts j.1 ∧
        Read.LSFChangeAt st'.mem chgPtr (compBranchChange (cuts j) splitVerts) ∧
        ptrBase + k ≤ chgPtr ∧
        chgPtr + (compBranchChange (cuts j) splitVerts).words ≤ outEnd) ∧
      outEnd ≤ cntBase ∧
      ZeroFrom st'.mem outEnd ∧
      (∀ a < ptrBase, st'.mem a = mem a) ∧
      c ≤ 100 * (∑ j : Fin k, (cuts j).length) + 45 * k * splitVerts.length + 260 * k +
        20 * splitVerts.length + 90 := by
  obtain ⟨st', c, hr, hchg, hout, hz1, hab, hbl, hc⟩ :=
    compPackChanges_runs_gen hpZero hw16 hk hK_m hVCap_m hb_hdr_w hptr_le hsplit_ge hsplit_w
      hcut_bd hcnt_m hlog_m hsp_m hz_ptr hz_roots hz_gap
  exact ⟨st', c, hr, hchg, hout, fun a ha => by
    by_cases hlt : a < splitBase + splitVerts.length
    · exact hz1 a ha hlt
    · exact (hab a (by omega)).trans (hz_above a (by omega)), hbl, hc⟩

end

end MinCostFlow.SparseCore.Program
