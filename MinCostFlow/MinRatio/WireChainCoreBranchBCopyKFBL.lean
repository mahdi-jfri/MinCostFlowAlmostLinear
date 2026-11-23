module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadKFBL
import WordRAM.Tactic

/-!
# The copies after op `0` in a Branch B level step (`WireChainCoreBranchBCopyKFBL`)

The select part of `Update` reads, at each level that `Update` does not rebuild, the edges that
leave the forest of the active branch (`fDel`) and the re-embedding list of that branch. Op `0`
leaves both in its output region, which is not safe: the core footprint may grow into it, so the
lists need not stay off the footprint, and nothing keeps them from later calls. So right after the
head of the step (`wireBranchBStepHeadKFBL`) the core copies both lists to its first free word.
This file gives that part, `wireBranchBCopyListsStmt`, and its run lemma
`wireBranchBCopyListsStmt_runs`. The copies use `wireRawCopyBody`, which needs no bound on the
copied words.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Copy the `fDel` list of the change record of branch `reg 2` and the re-embedding list of that
branch, which op `0` left at the heap pointer `reg 25` (with `k = reg 76` branches), to the first
free word `reg 4`. Afterwards `regs 26, 27` hold the place and length of the `fDel` copy,
`regs 28, 29` those of the re-embedding copy, and `reg 4` the next free word. -/
@[expose] def wireBranchBCopyListsStmt (copyProc : ℕ) : Stmt :=
  .assign 20 (.load (.bin .add (.bin .add (.reg 25) (.const 1)) (.bin .mul (.const 6) (.reg 76)))) ;;
  .assign 21 (.load (.bin .add (.reg 20) (.reg 2))) ;;
  .assign 22 (.load (.reg 21)) ;;
  .assign 27 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 22))) ;;
  .assign 26 (.reg 4) ;;
  .call 30 copyProc [.reg 27, .bin .add (.bin .add (.reg 21) (.const 2)) (.reg 22), .reg 26] ;;
  .assign 20 (.bin .add (.bin .add (.bin .add (.reg 25) (.const 1))
    (.bin .mul (.const 4) (.reg 76))) (.bin .mul (.const 2) (.reg 2))) ;;
  .assign 29 (.load (.bin .add (.reg 20) (.const 1))) ;;
  .assign 28 (.bin .add (.reg 26) (.reg 27)) ;;
  .call 30 copyProc [.reg 29, .load (.reg 20), .reg 28] ;;
  .assign 4 (.bin .add (.reg 28) (.reg 29))

theorem wireBranchBCopyListsStmt_noRand (copyProc : ℕ) :
    (wireBranchBCopyListsStmt copyProc).NoRand := by
  simp [wireBranchBCopyListsStmt, Stmt.NoRand]

set_option maxHeartbeats 1600000 in
/-- One run of `wireBranchBCopyListsStmt`. The change records of op `0` (`BranchOutFChgAt`) and the
re-embedding list of branch `b` lie in the op-`0` output `[heap, h1)`, and `h1` is the first free
word. The run copies the `fDel` list of the change record `c` of branch `b` to `h1` and the
re-embedding list right after it, changes no other word, and costs at most `20` steps per copied
entry and a constant. -/
theorem wireBranchBCopyListsStmt_runs {w copyProc heap h1 k b : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : State} {oldLsf newLsf : ℕ → LSF} {reemb : List ℕ}
    (hw : 6 < 2 ^ w)
    (hCopy : p.procs[copyProc]? = some wireRawCopyBody)
    (hr2 : s.regs 2 = b) (hr4 : s.regs 4 = h1) (hr25 : s.regs 25 = heap) (hr76 : s.regs 76 = k)
    (hb : b < k)
    (hF : BranchOutFChgAt w s.mem heap h1 k oldLsf newLsf)
    (hR : ReembListAt s.mem (s.mem (heap + 1 + 4 * k + 2 * b))
      (s.mem (heap + 2 + 4 * k + 2 * b)) reemb)
    (hRlo : heap ≤ s.mem (heap + 1 + 4 * k + 2 * b))
    (hRhi : s.mem (heap + 1 + 4 * k + 2 * b) + s.mem (heap + 2 + 4 * k + 2 * b) ≤ h1)
    (hRoom : h1 + 2 * (h1 - heap) < 2 ^ w) :
    ∃ (out : State) (cost : ℕ) (c : Read.LSFChange),
      Runs w p ω (wireBranchBCopyListsStmt copyProc) s .normal out cost ∧
      c.Exact (oldLsf b) (newLsf b) ∧ (∀ e ∈ c.fDel, e < 2 ^ w) ∧
      c.fDel.length ≤ h1 - heap ∧ reemb.length ≤ h1 - heap ∧
      out.regs 26 = h1 ∧ out.regs 27 = c.fDel.length ∧
      out.regs 28 = h1 + c.fDel.length ∧ out.regs 29 = reemb.length ∧
      out.regs 4 = h1 + c.fDel.length + reemb.length ∧
      ListAt out.mem h1 c.fDel ∧ ListAt out.mem (h1 + c.fDel.length) reemb ∧
      (∀ a, (a < h1 ∨ h1 + c.fDel.length + reemb.length ≤ a) → out.mem a = s.mem a) ∧
      (∀ r, r ≠ 4 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
        out.regs r = s.regs r) ∧
      cost ≤ 20 * (c.fDel.length + reemb.length) + 150 := by
  have hCopyC := wireRawCopyBody_meets (w := w) hCopy
  dsimp only [BranchOutFChgAt] at hF
  obtain ⟨hF0, hF1, hF2, hF3⟩ := hF
  obtain ⟨fP, hfP⟩ : ∃ x, s.mem (heap + 1 + 6 * k) = x := ⟨_, rfl⟩
  rw [hfP] at hF1 hF2 hF3
  obtain ⟨c, hc, hex, hclo, hchi, hcw⟩ := hF3 b hb
  obtain ⟨cP, hcP⟩ : ∃ x, s.mem (fP + b) = x := ⟨_, rfl⟩
  rw [hcP] at hc hclo hchi
  obtain ⟨hc0, hcRoots, hc1, hcFDel⟩ := hc
  have hWords : c.words = 2 + c.roots.length + c.fDel.length := by
    simp only [Read.LSFChange.words, Read.LSFChange.size]; omega
  obtain ⟨rP, hrP⟩ : ∃ x, s.mem (heap + 1 + 4 * k + 2 * b) = x := ⟨_, rfl⟩
  obtain ⟨hRL, hRList⟩ := hR
  rw [hrP] at hRList hRlo hRhi
  rw [hRL] at hRhi
  suffices h : ∃ o st' cost, Runs w p ω (wireBranchBCopyListsStmt copyProc) s o st' cost ∧
      (o = .normal ∧
        st'.regs 26 = h1 ∧ st'.regs 27 = c.fDel.length ∧
        st'.regs 28 = h1 + c.fDel.length ∧ st'.regs 29 = reemb.length ∧
        st'.regs 4 = h1 + c.fDel.length + reemb.length ∧
        ListAt st'.mem h1 c.fDel ∧ ListAt st'.mem (h1 + c.fDel.length) reemb ∧
        (∀ a, (a < h1 ∨ h1 + c.fDel.length + reemb.length ≤ a) → st'.mem a = s.mem a) ∧
        (∀ r, r ≠ 4 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
          st'.regs r = s.regs r)) ∧
      0 + cost ≤ 20 * (c.fDel.length + reemb.length) + 150 by
    obtain ⟨o, st', cost, hr, ⟨rfl, hq⟩, hcost⟩ := h
    exact ⟨st', cost, c, hr, hex, hcw, by omega, by omega, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
      hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.2,
      by omega⟩
  unfold wireBranchBCopyListsStmt
  refine runs_seq_assign_le (v := fP) (by eval_expr) ?_
  refine runs_seq_assign_le (v := cP) (by eval_expr) ?_
  refine runs_seq_assign_le (v := c.roots.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := c.fDel.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := h1) (by eval_expr) ?_
  have hFL : c.fDel.length ≤ h1 - heap := by omega
  have hRLe : reemb.length ≤ h1 - heap := by omega
  refine runs_seq_call_le hCopyC (vs := [c.fDel.length, cP + 2 + c.roots.length, h1])
    (by eval_expr) (by wram_words) ?_ ?_
  · simp only [wireRawCopyContract, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨trivial, by omega, by omega, by omega, Or.inl (by omega)⟩
  intro v1 m2 pos2 ⟨hc2, hf2⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc2 hf2
  have hm2R : m2 (heap + 1 + 4 * k + 2 * b + 1) = reemb.length := by
    rw [hf2 _ (Or.inl (by omega)), show heap + 1 + 4 * k + 2 * b + 1 = heap + 2 + 4 * k + 2 * b by
      omega]
    exact hRL
  have hm2P : m2 (heap + 1 + 4 * k + 2 * b) = rP := by
    rw [hf2 _ (Or.inl (by omega))]; exact hrP
  refine runs_seq_assign_le (v := heap + 1 + 4 * k + 2 * b) (by eval_expr) ?_
  refine runs_seq_assign_le (v := reemb.length) (by eval_expr) ?_
  refine runs_seq_assign_le (v := h1 + c.fDel.length) (by eval_expr) ?_
  refine runs_seq_call_le hCopyC (vs := [reemb.length, rP, h1 + c.fDel.length])
    (by eval_expr) (by wram_words) ?_ ?_
  · simp only [wireRawCopyContract, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨trivial, by omega, by omega, by omega, Or.inl (by omega)⟩
  intro v2 m3 pos3 ⟨hc3, hf3⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc3 hf3
  refine runs_assign_le (v := h1 + c.fDel.length + reemb.length) (by eval_expr) ?_ ?_
  · refine ⟨rfl, by simp, by simp, by simp, by simp, by simp, fun i hi => ?_, fun i hi => ?_, fun a ha => ?_,
      fun r h4 h20 h21 h22 h26 h27 h28 h29 h30 => ?_⟩
    · show m3 (h1 + i) = c.fDel[i]
      rw [hf3 _ (Or.inl (by omega)), hc2 i hi,
        show cP + 2 + c.roots.length + i = cP + 2 + c.roots.length + i from rfl]
      exact hcFDel i hi
    · show m3 (h1 + c.fDel.length + i) = reemb[i]
      rw [hc3 i hi, hf2 _ (Or.inl (by omega))]
      exact hRList i hi
    · show m3 a = s.mem a
      rw [hf3 a (by omega), hf2 a (by omega)]
    · simp [h4, h20, h21, h22, h26, h27, h28, h29, h30]
  · simp only [wireRawCopyContract, List.getD_cons_zero]
    wram_cost

end MinCostFlow.MinRatio
