module

public import MinCostFlow.MinRatio.WireSuffixEditsEmit
import WordRAM.Tactic

/-!
# Multi-forest suffix tree-edit packer: top-level theorem (`WireSuffixEdits`)

Composes Passes 1–2 (`markForestListStmt_runs`, `WireSuffixEditsBase.lean`) and Passes 3–4
(`emitForestListDiffStmt_runs`, `WireSuffixEditsEmit.lean`) to prove `wireSuffixPackEdits_runs`:
`wireSuffixPackEditsBody` packs `TreeEditsAt` for `TreeEditDifference oldUnion newUnion` at
`heap + 3 * intCap` in `O(cnt + graphListEdgeSum oldFs + graphListEdgeSum newFs)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program

/-- Execution theorem for `wireSuffixPackEditsBody`: packs `TreeEditsAt` for the symmetric
difference between `graphListEdgeUnion oldFs` and `graphListEdgeUnion newFs` at
`heap + 3 * intCap`, in `O(cnt + graphListEdgeSum oldFs + graphListEdgeSum newFs)` steps. -/
theorem wireSuffixPackEdits_runs
    {w oldPtrs newPtrs cnt intCap heap pos : ℕ} {oldFs newFs : List MGraph}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hOldLen : oldFs.length = cnt) (hNewLen : newFs.length = cnt)
    (hOld : ForestPtrListAt mem oldPtrs oldFs intCap heap)
    (hNew : ForestPtrListAt mem newPtrs newFs intCap heap)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + 3 * intCap + 2 * (graphListEdgeSum oldFs + graphListEdgeSum newFs) < 2 ^ w)
    (hw7 : 7 < 2 ^ w) :
    let oldE := graphListEdgeUnion oldFs
    let newE := graphListEdgeUnion newFs
    ∃ (out : State) (cost : ℕ) (edits : List TreeChange),
      Runs w p ω wireSuffixPackEditsBody
        (startState [oldPtrs, newPtrs, cnt, intCap, heap] mem pos)
        (.returned edits.length) out cost ∧
      cost ≤ 85 * (graphListEdgeSum oldFs + graphListEdgeSum newFs) + 210 * cnt + 120 ∧
      edits.length ≤ graphListEdgeSum oldFs + graphListEdgeSum newFs ∧
      TreeEditsAt out.mem (heap + 3 * intCap) edits ∧
      TreeEditDifference oldE newE edits ∧
      ZeroFrom out.mem (heap + 3 * intCap + 2 * edits.length) ∧
      (∀ a < heap, out.mem a = mem a) := by
  dsimp only
  let s0 := startState [oldPtrs, newPtrs, cnt, intCap, heap] mem pos
  let mOld := heap
  let mNew := heap + intCap
  let mEmit := heap + 2 * intCap
  let outBuf := heap + 3 * intCap
  let s1 := { s0 with regs := Function.update s0.regs 5 mOld }
  let s2 := { s1 with regs := Function.update s1.regs 6 mNew }
  let s3 := { s2 with regs := Function.update s2.regs 7 mEmit }
  let s4 := { s3 with regs := Function.update s3.regs 8 outBuf }
  let s5 := { s4 with regs := Function.update s4.regs 9 0 }
  let s6 := { s5 with regs := Function.update s5.regs 10 oldPtrs }
  let s7 := { s6 with regs := Function.update s6.regs 11 mOld }
  have r1 : Runs w p ω (.assign 5 (.reg 4)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨mOld, by simp [Expr.eval, s0, startState, mOld], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.reg 3))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨mNew, by simp [Expr.eval, BinOp.eval, s1, s0, startState, mNew,
      show heap + intCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 3))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨mEmit, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, mNew, mEmit,
      show heap + intCap + intCap = heap + 2 * intCap by omega, show heap + 2 * intCap < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 3))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨outBuf, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, mEmit, outBuf,
      show heap + 2 * intCap + intCap = heap + 3 * intCap by omega, show heap + 3 * intCap < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 9 (.const 0)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 10 (.reg 0)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨oldPtrs, by simp [Expr.eval, s5, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 11 (.reg 5)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨mOld, by simp [Expr.eval, s6, s5, s4, s3, s2, s1, Function.update_of_ne], rfl, rfl, rfl⟩
  -- Pass 1: mark `oldFs` in `mOld`
  obtain ⟨s8, c1, rP1, hc1, hMkOld8, hFr8, hRegs8⟩ :=
    markForestListStmt_runs (w := w) (ptrs := oldPtrs) (markBase := mOld) (intCap := intCap)
      (Fs := oldFs) (st := s7) (by simp [s7, s6, Function.update_of_ne])
      (by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState, hOldLen]) (by simp [s7])
      hOld (by omega) hw7
  let s9 := { s8 with regs := Function.update s8.regs 10 newPtrs }
  let s10 := { s9 with regs := Function.update s9.regs 11 mNew }
  have r9 : Runs w p ω (.assign 10 (.reg 1)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨newPtrs, by simp [Expr.eval, hRegs8 1 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 11 (.reg 6)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨mNew, by simp [Expr.eval, s9, Function.update_of_ne, hRegs8 6 (by omega),
      s7, s6, s5, s4, s3, s2], rfl, rfl, rfl⟩
  -- Pass 2: mark `newFs` in `mNew`
  have hNew10 : ForestPtrListAt s10.mem newPtrs newFs intCap mNew := by
    have h1 := hNew.congr (fun a ha => hFr8 a (Or.inl ha))
    have h11 := h1.1
    exact ⟨by dsimp [mNew]; omega, fun t ht => by
      obtain ⟨vc, ec, hG, hE, hC⟩ := h1.2 t ht
      exact ⟨vc, ec, hG, by change s8.mem _ + _ ≤ _; dsimp [mNew]; omega, hC⟩⟩
  obtain ⟨s11, c2, rP2, hc2, hMkNew11, hFr11, hRegs11⟩ :=
    markForestListStmt_runs (w := w) (ptrs := newPtrs) (markBase := mNew) (intCap := intCap)
      (Fs := newFs) (st := s10) (by simp [s10, s9, Function.update_of_ne])
      (by simp [s10, s9, Function.update_of_ne, hRegs8 2 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState, hNewLen])
      (by simp [s10]) hNew10 (by dsimp [mNew]; omega) hw7
  -- Pass 3: emit deletes from `oldFs`
  let s12 := { s11 with regs := Function.update s11.regs 10 oldPtrs }
  let s13 := { s12 with regs := Function.update s12.regs 11 mNew }
  let s14 := { s13 with regs := Function.update s13.regs 20 0 }
  have hs11_k (r : ℕ) (hr : r < 10) : s11.regs r = s7.regs r := by
    rw [hRegs11 r (by omega)]; simp only [s10, s9, Function.update_of_ne (by omega : r ≠ 11),
      Function.update_of_ne (by omega : r ≠ 10)]; exact hRegs8 r (by omega)
  have r12 : Runs w p ω (.assign 10 (.reg 0)) s11 .normal s12 2 :=
    runs_assign_iff.mpr ⟨oldPtrs, by simp [Expr.eval, hs11_k 0 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState],
      rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 11 (.reg 6)) s12 .normal s13 2 :=
    runs_assign_iff.mpr ⟨mNew, by simp [Expr.eval, s12, Function.update_of_ne, hs11_k 6 (by omega),
      s7, s6, s5, s4, s3, s2], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.assign 20 (.const 0)) s13 .normal s14 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  have hOld14 : ForestPtrListAt s14.mem oldPtrs oldFs intCap mEmit := by
    have h1 := hOld.congr (fun a ha => (hFr11 a (Or.inl (by dsimp [mNew]; omega))).trans (hFr8 a (Or.inl ha)))
    have h11 := h1.1
    exact ⟨by dsimp [mEmit]; omega, fun t ht => by
      obtain ⟨vc, ec, hG, hE, hC⟩ := h1.2 t ht
      exact ⟨vc, ec, hG, by change s11.mem _ + _ ≤ _; dsimp [mEmit]; omega, hC⟩⟩
  have hNewMark14 : ∀ e < intCap, s14.mem (mNew + e) = if e ∈ graphListEdgeUnion newFs then 1 else 0 :=
    fun e he => by
      change s11.mem (mNew + e) = _
      rw [hMkNew11 e he]
      have h0 : s10.mem (mNew + e) = 0 := by
        change s8.mem (mNew + e) = 0
        rw [hFr8 _ (Or.inr (by dsimp [mOld, mNew]; omega))]
        exact hz _ (by dsimp [mNew]; omega)
      rw [h0]
  have hEmitZero14 : ∀ e < intCap, s14.mem (mEmit + e) = if e ∈ (∅ : Finset ℕ) then 1 else 0 :=
    fun e he => by
      change s11.mem (mEmit + e) = _
      rw [hFr11 _ (Or.inr (by dsimp [mNew, mEmit]; omega))]
      have h0 : s10.mem (mEmit + e) = 0 := by
        change s8.mem (mEmit + e) = 0
        rw [hFr8 _ (Or.inr (by dsimp [mOld, mEmit]; omega))]
        exact hz _ (by dsimp [mEmit]; omega)
      simp [h0]
  let maxOut := graphListEdgeSum oldFs + graphListEdgeSum newFs
  obtain ⟨s15, c3, dels, rP3, hc3, hDelsNd, hDelsMem, hDelsLe, hs15_9, hEd15, hEm15, hFr15, hRegs15⟩ :=
    emitForestListDiffStmt_runs (w := w) (ptrs := oldPtrs) (otherBase := mNew) (emitBase := mEmit)
      (outBuf := outBuf) (intCap := intCap) (initLen := 0) (maxOut := maxOut) (tag := 0)
      (Fs := oldFs) (otherSet := graphListEdgeUnion newFs) (emitted0 := ∅) (st := s14)
      (by simp [s14, s13, s12, Function.update_of_ne])
      (by simp [s14, s13, s12, Function.update_of_ne, hs11_k 2 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState, hOldLen])
      (by simp [s14, s13, Function.update_of_ne])
      (by simp [s14, s13, s12, Function.update_of_ne, hs11_k 7 (by omega), s7, s6, s5, s4, s3])
      (by simp [s14, s13, s12, Function.update_of_ne, hs11_k 8 (by omega), s7, s6, s5, s4])
      (by simp [s14, s13, s12, Function.update_of_ne, hs11_k 9 (by omega), s7, s6, s5])
      (by simp [s14]) (Or.inl rfl) hOld14 hNewMark14 hEmitZero14
      (Or.inl (by dsimp [mNew, mEmit]; omega))
      ⟨by dsimp [mEmit, outBuf]; omega, by dsimp [mNew, outBuf]; omega⟩
      (by dsimp [maxOut]; omega) (by dsimp [outBuf, maxOut]; omega)
      (by dsimp [mEmit]; omega) (by dsimp [mNew]; omega) hw7
  -- Pass 4: emit inserts from `newFs`
  let s16 := { s15 with regs := Function.update s15.regs 10 newPtrs }
  let s17 := { s16 with regs := Function.update s16.regs 11 mOld }
  let s18 := { s17 with regs := Function.update s17.regs 20 1 }
  have hs15_k (r : ℕ) (hr : r < 9) : s15.regs r = s7.regs r := by
    rw [hRegs15 r (Or.inl ⟨by omega, by omega⟩)]
    simp only [s14, s13, s12, Function.update_of_ne (by omega : r ≠ 20),
      Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 10)]
    exact hs11_k r (by omega)
  have r16 : Runs w p ω (.assign 10 (.reg 1)) s15 .normal s16 2 :=
    runs_assign_iff.mpr ⟨newPtrs, by simp [Expr.eval, hs15_k 1 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState],
      rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.assign 11 (.reg 5)) s16 .normal s17 2 :=
    runs_assign_iff.mpr ⟨mOld, by simp [Expr.eval, s16, Function.update_of_ne, hs15_k 5 (by omega),
      s7, s6, s5, s4, s3, s2, s1], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.assign 20 (.const 1)) s17 .normal s18 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hNew18 : ForestPtrListAt s18.mem newPtrs newFs intCap mEmit := by
    have h1 := hNew.congr (fun a ha =>
      (hFr15 a (Or.inl (by dsimp [mEmit]; omega)) (Or.inl (by dsimp [outBuf]; omega))).trans
        ((hFr11 a (Or.inl (by dsimp [mNew]; omega))).trans (hFr8 a (Or.inl ha))))
    have h11 := h1.1
    exact ⟨by dsimp [mEmit]; omega, fun t ht => by
      obtain ⟨vc, ec, hG, hE, hC⟩ := h1.2 t ht
      exact ⟨vc, ec, hG, by change s15.mem _ + _ ≤ _; dsimp [mEmit]; omega, hC⟩⟩
  have hOldMark18 : ∀ e < intCap, s18.mem (mOld + e) = if e ∈ graphListEdgeUnion oldFs then 1 else 0 :=
    fun e he => by
      change s15.mem (mOld + e) = _
      rw [hFr15 _ (Or.inl (by dsimp [mOld, mEmit]; omega)) (Or.inl (by dsimp [mOld, outBuf]; omega))]
      change s11.mem (mOld + e) = _
      rw [hFr11 _ (Or.inl (by dsimp [mOld, mNew]; omega))]
      change s8.mem (mOld + e) = _
      rw [hMkOld8 e he]
      have h0 : s7.mem (mOld + e) = 0 := hz _ (by dsimp [mOld]; omega)
      rw [h0]
  have hEm18 : ∀ e < intCap, s18.mem (mEmit + e) = if e ∈ dels.toFinset then 1 else 0 :=
    fun e he => by simpa using hEm15 e he
  obtain ⟨s19, c4, ins, rP4, hc4, hInsNd, hInsMem, hInsLe, hs19_9, hEd19, _, hFr19, _⟩ :=
    emitForestListDiffStmt_runs (w := w) (ptrs := newPtrs) (otherBase := mOld) (emitBase := mEmit)
      (outBuf := outBuf) (intCap := intCap) (initLen := dels.length) (maxOut := maxOut) (tag := 1)
      (Fs := newFs) (otherSet := graphListEdgeUnion oldFs) (emitted0 := dels.toFinset) (st := s18)
      (by simp [s18, s17, s16, Function.update_of_ne])
      (by simp [s18, s17, s16, Function.update_of_ne, hs15_k 2 (by omega), s7, s6, s5, s4, s3, s2, s1, s0, startState, hNewLen])
      (by simp [s18, s17, Function.update_of_ne])
      (by simp [s18, s17, s16, Function.update_of_ne, hs15_k 7 (by omega), s7, s6, s5, s4, s3])
      (by simp [s18, s17, s16, Function.update_of_ne, hs15_k 8 (by omega), s7, s6, s5, s4])
      (by simp [s18, s17, s16, Function.update_of_ne, hs15_9])
      (by simp [s18]) (Or.inr rfl) hNew18 hOldMark18 hEm18
      (Or.inl (by dsimp [mOld, mEmit]; omega))
      ⟨by dsimp [mEmit, outBuf]; omega, by dsimp [mOld, outBuf]; omega⟩
      (by dsimp [maxOut]; omega) (by dsimp [outBuf, maxOut]; omega)
      (by dsimp [mEmit]; omega) (by dsimp [mOld]; omega) hw7
  let edits := dels.map TreeChange.delete ++ ins.map TreeChange.insert
  have hEdLen : edits.length = dels.length + ins.length := by simp [edits]
  have rRet : Runs w p ω (.ret (.reg 9)) s19 (.returned edits.length) s19 2 :=
    runs_ret_iff.mpr ⟨edits.length, by simp [Expr.eval, hs19_9, hEdLen], rfl, rfl, rfl⟩
  have rFull : Runs w p ω wireSuffixPackEditsBody s0 (.returned edits.length) s19
      (2 + (4 + (4 + (4 + (2 + (2 + (2 + (c1 + (2 + (2 + (c2 + (2 + (2 + (2 + (c3 +
        (2 + (2 + (2 + (c4 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 4, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, c1, _, rP1,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, c2, _, rP2,
    runs_seq_iff.mpr (Or.inr ⟨s12, 2, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 2, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 2, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, c3, _, rP3,
    runs_seq_iff.mpr (Or.inr ⟨s16, 2, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 2, _, r18,
    runs_seq_iff.mpr (Or.inr ⟨s19, c4, 2, rP4, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Verify `TreeEditsAt`, `TreeEditDifference`, `ZeroFrom`, frame
  have hEdAll : TreeEditsAt s19.mem outBuf edits := by
    rw [TreeEditsAt, List.flatMap_append]
    apply listAt_append.mpr
    constructor
    · intro i hi
      rw [treeEditWords_length, List.length_map] at hi
      rw [hFr19 _ (Or.inr (by dsimp [mEmit, outBuf]; omega)) (Or.inl (by omega))]
      simpa using hEd15 i (by rw [treeEditWords_length, List.length_map]; exact hi)
    · have hbase : outBuf + ((dels.map TreeChange.delete).flatMap treeEditWords).length =
          outBuf + 2 * dels.length := by rw [treeEditWords_length, List.length_map]
      rw [hbase]; simpa [TreeEditsAt] using hEd19
  have hDiff : TreeEditDifference (graphListEdgeUnion oldFs) (graphListEdgeUnion newFs) edits := by
    let oldE := graphListEdgeUnion oldFs
    let newE := graphListEdgeUnion newFs
    let common := (oldE ∩ newE).toList
    have hOldPerm : (dels ++ common).Perm oldE.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · rw [List.nodup_append]
        refine ⟨hDelsNd, Finset.nodup_toList _, fun a ha b hb heq => ?_⟩
        subst heq
        exact ((hDelsMem a).mp ha).2.1 (Finset.mem_inter.mp (Finset.mem_toList.mp hb)).2
      · exact Finset.nodup_toList _
      · ext e; simp [common, hDelsMem, Finset.mem_inter]; tauto
    have hNewPerm : (ins ++ common).Perm newE.toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · rw [List.nodup_append]
        refine ⟨hInsNd, Finset.nodup_toList _, fun a ha b hb heq => ?_⟩
        subst heq
        exact ((hInsMem a).mp ha).2.1 (Finset.mem_inter.mp (Finset.mem_toList.mp hb)).1
      · exact Finset.nodup_toList _
      · ext e; simp [common, hInsMem, hDelsMem, Finset.mem_inter]; tauto
    have hFiltOld : (dels ++ common).filter (fun e => decide (e ∉ newE)) = dels := by
      rw [List.filter_append,
        List.filter_eq_self.mpr (fun e he => by simp only [decide_eq_true_eq]; exact ((hDelsMem e).mp he).2.1),
        List.filter_eq_nil_iff.mpr (fun e he => by simp [(Finset.mem_inter.mp (Finset.mem_toList.mp he)).2]),
        List.append_nil]
    have hFiltNew : (ins ++ common).filter (fun e => decide (e ∉ oldE)) = ins := by
      rw [List.filter_append,
        List.filter_eq_self.mpr (fun e he => by simp only [decide_eq_true_eq]; exact ((hInsMem e).mp he).2.1),
        List.filter_eq_nil_iff.mpr (fun e he => by simp [(Finset.mem_inter.mp (Finset.mem_toList.mp he)).1]),
        List.append_nil]
    have hD := treeEditDifference_of_filter hOldPerm hNewPerm
    rwa [hFiltOld, hFiltNew] at hD
  have hzEnd : ZeroFrom s19.mem (outBuf + 2 * edits.length) := fun a ha => by
    rw [hFr19 a (Or.inr (by dsimp [mEmit, outBuf]; omega)) (Or.inr (by omega)),
      hFr15 a (Or.inr (by dsimp [mEmit, outBuf]; omega)) (Or.inr (by omega)),
      hFr11 a (Or.inr (by dsimp [mNew, outBuf]; omega)),
      hFr8 a (Or.inr (by dsimp [mOld, outBuf]; omega))]
    exact hz a (by omega)
  have hFrEnd : ∀ a < heap, s19.mem a = mem a := fun a ha => by
    rw [hFr19 a (Or.inl (by dsimp [mEmit]; omega)) (Or.inl (by dsimp [outBuf]; omega)),
      hFr15 a (Or.inl (by dsimp [mEmit]; omega)) (Or.inl (by dsimp [outBuf]; omega)),
      hFr11 a (Or.inl (by dsimp [mNew]; omega)),
      hFr8 a (Or.inl ha)]
    rfl
  refine ⟨s19, _, edits, rFull, ?_, by omega, hEdAll, hDiff, hzEnd, hFrEnd⟩
  rw [hOldLen] at hc1 hc3
  rw [hNewLen] at hc2 hc4
  omega

end MinCostFlow.MinRatio
