module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutHelpers

import WordRAM.Tactic

/-!
# Phase 4 candidate-superset seeding (`AssemblyFirstStepOutSeed`)

Verifies the two batch/lazy seeding routines that initialize the Phase 4 deduplicated candidate
supersets `delSup`, `insSup`, and `reembRaw`:
1. `asmFirstSeedBatch_runs`: verifies `asmFirstSeedBatchStmt fPush` (`AssemblyFirstStepOutHelpers`),
   seeding `delSup` with `batchDeletes U` and `insSup` with `batchDeletes U ∪ batchInsEdges U` in
   `≤ 130 * U.length + 30` steps with zero heap allocation.
2. `asmFirstSeedLazyStmt fAppend` and `asmFirstSeedLazy_runs`: loops over Phase 2's `nNew` lazy
   edge lists `[ptr_i, len_i]` at `lazyPtr + 2 * i`, appending every newly-active bundle edge into
   both `insSup` and `reembRaw` in `≤ 140 * (∑ |lazyE i|) + 65 * nNew + 25` steps with zero heap.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- **Seed `insSup` and `reembRaw` from Phase 2's `lazyPtr`**,
`[inInsSup, insSup, insLenAddr, inReemb, reemb, reembLenAddr, lazyPtr, nNew]`. -/
def asmFirstSeedLazyStmt (fAppend : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 7)
    (.assign 9 (.load (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8)))) ;;
     .assign 10 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8))) (.const 1))) ;;
     .call 11 fAppend [.reg 0, .reg 1, .reg 2, .reg 9, .reg 10] ;;
     .call 11 fAppend [.reg 3, .reg 4, .reg 5, .reg 9, .reg 10]) ;;
  .ret (.const 0)

/-- Workspace-region disjointness helper: `a` is outside `[p, p + len)`. -/
def OutOf (p len a : ℕ) : Prop := a < p ∨ p + len ≤ a

end

public section

theorem asmFirstSeedLazyStmt_noRand (fAppend : ℕ) : (asmFirstSeedLazyStmt fAppend).NoRand := by
  simp [asmFirstSeedLazyStmt, forRange, forUp, Stmt.NoRand]

private lemma mem_batchInsEdges_append_singleton (U : List Update) (u : Update) (e : ℕ) :
    e ∈ batchInsEdges (U ++ [u]) ↔ e ∈ batchInsEdges U ∨ ∃ a b, u = .insert e a b := by
  simp only [batchInsEdges, List.mem_toFinset, List.mem_filterMap, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨u', hu' | rfl, hsome⟩
    · exact Or.inl ⟨u', hu', hsome⟩
    · cases u' with
      | insert e' a b => simp only [Option.some.injEq] at hsome; subst hsome; exact Or.inr ⟨a, b, rfl⟩
      | delete _ => simp at hsome
      | split _ _ _ _ => simp at hsome
  · rintro (⟨u', hu', hsome⟩ | ⟨a, b, rfl⟩)
    · exact ⟨u', Or.inl hu', hsome⟩
    · exact ⟨.insert e a b, Or.inr rfl, rfl⟩

/-! ## Verification of `asmFirstSeedBatchStmt` -/

set_option maxHeartbeats 400000 in
theorem asmFirstSeedBatch_runs {w fPush batch words eCap pos : ℕ}
    {dFl dBuf dLen iFl iBuf iLen : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    {G₀ : MGraph} {U : List Update} {Ld0 Li0 : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hBat : BatchAt mem₀ batch G₀ U words)
    (hCaps : ∀ u ∈ U, match u with | .insert e _ _ => e < eCap | .delete e => e < eCap | .split _ _ _ _ => True)
    (hDd : DedupBufAt mem₀ dFl dBuf dLen eCap Ld0)
    (hDi : DedupBufAt mem₀ iFl iBuf iLen eCap Li0)
    (hReg : ∀ a, (dFl ≤ a ∧ a < dFl + eCap ∨ dBuf ≤ a ∧ a < dBuf + eCap ∨ a = dLen) →
      OutOf iFl eCap a ∧ OutOf iBuf eCap a ∧ a ≠ iLen)
    (hDisj_d : (dFl + eCap ≤ dBuf ∨ dBuf + eCap ≤ dFl) ∧ OutOf dFl eCap dLen ∧ OutOf dBuf eCap dLen)
    (hDisj_i : (iFl + eCap ≤ iBuf ∨ iBuf + eCap ≤ iFl) ∧ OutOf iFl eCap iLen ∧ OutOf iBuf eCap iLen)
    (hBat_disj : ∀ a, batch ≤ a → a < batch + words →
      OutOf dFl eCap a ∧ OutOf dBuf eCap a ∧ a ≠ dLen ∧
      OutOf iFl eCap a ∧ OutOf iBuf eCap a ∧ a ≠ iLen)
    (hBat_w : batch + words < 2 ^ w)
    (hdFl_w : dFl + eCap < 2 ^ w) (hdBuf_w : dBuf + eCap < 2 ^ w) (hdLen_w : dLen < 2 ^ w)
    (hiFl_w : iFl + eCap < 2 ^ w) (hiBuf_w : iBuf + eCap < 2 ^ w) (hiLen_w : iLen < 2 ^ w) :
    ∃ st' cost Ld Li,
      Runs w p ω (asmFirstSeedBatchStmt fPush)
        (startState [batch, dFl, dBuf, dLen, iFl, iBuf, iLen] mem₀ pos) (.returned 0) st' cost ∧
      DedupBufAt st'.mem dFl dBuf dLen eCap Ld ∧
      DedupBufAt st'.mem iFl iBuf iLen eCap Li ∧
      (∀ e, e ∈ Ld ↔ e ∈ Ld0 ∨ e ∈ batchDeletes U) ∧
      (∀ e, e ∈ Li ↔ e ∈ Li0 ∨ e ∈ batchDeletes U ∨ e ∈ batchInsEdges U) ∧
      (∀ a, OutOf dFl eCap a → OutOf dBuf eCap a → a ≠ dLen →
        OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen → st'.mem a = mem₀ a) ∧
      cost ≤ 130 * U.length + 30 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  have hUL : U.length < 2 ^ w := by have := batchBodyAt_length_le hBat.2.2; have := hBat.1; omega
  have hRegSym : ∀ a, (iFl ≤ a ∧ a < iFl + eCap ∨ iBuf ≤ a ∧ a < iBuf + eCap ∨ a = iLen) →
      OutOf dFl eCap a ∧ OutOf dBuf eCap a ∧ a ≠ dLen := by
    intro a hi
    refine ⟨?_, ?_, ?_⟩
    · by_contra h; simp only [OutOf, not_or, not_lt, not_le] at h
      have := hReg a (Or.inl h); rcases hi with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
    · by_contra h; simp only [OutOf, not_or, not_lt, not_le] at h
      have := hReg a (Or.inr (Or.inl h)); rcases hi with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
    · intro h; have := hReg a (Or.inr (Or.inr h))
      rcases hi with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
  set s0 := startState [batch, dFl, dBuf, dLen, iFl, iBuf, iLen] mem₀ pos
  set r1 := Function.update s0.regs 7 U.length
  set r2 := Function.update r1 8 (batch + 1)
  set r3 := Function.update r2 9 0
  have ha7 : Runs w p ω (.assign 7 (.load (.reg 0))) s0 .normal ⟨mem₀, r1, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨U.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) hBat.2.1, rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 0) (.const 1))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨batch + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
      (Expr.eval_const h1w) (by have := hBat.1; omega), rfl, rfl, rfl⟩
  have ha9 : Runs w p ω (.assign 9 (.const 0)) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hloop : ∀ (k : ℕ) (hk : k ≤ U.length) (cur W : ℕ) (stK : State) (Ldk Lik : List ℕ),
      batch < cur → cur + W ≤ batch + words →
      BatchBodyAt mem₀ cur (G₀.applyBatch (U.take k)) (U.drop k) W →
      stK.regs 1 = dFl → stK.regs 2 = dBuf → stK.regs 3 = dLen →
      stK.regs 4 = iFl → stK.regs 5 = iBuf → stK.regs 6 = iLen →
      stK.regs 7 = U.length → stK.regs 8 = cur → stK.regs 9 = k →
      DedupBufAt stK.mem dFl dBuf dLen eCap Ldk →
      DedupBufAt stK.mem iFl iBuf iLen eCap Lik →
      (∀ e, e ∈ Ldk ↔ e ∈ Ld0 ∨ e ∈ batchDeletes (U.take k)) →
      (∀ e, e ∈ Lik ↔ e ∈ Li0 ∨ e ∈ batchDeletes (U.take k) ∨ e ∈ batchInsEdges (U.take k)) →
      (∀ a, OutOf dFl eCap a → OutOf dBuf eCap a → a ≠ dLen →
        OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen → stK.mem a = mem₀ a) →
      ∃ st1 c1 Ld Li,
        Runs w p ω (forUp 9 (.reg 7) (asmFirstSeedBatchBody fPush)) stK .normal st1 c1 ∧
        DedupBufAt st1.mem dFl dBuf dLen eCap Ld ∧
        DedupBufAt st1.mem iFl iBuf iLen eCap Li ∧
        (∀ e, e ∈ Ld ↔ e ∈ Ld0 ∨ e ∈ batchDeletes U) ∧
        (∀ e, e ∈ Li ↔ e ∈ Li0 ∨ e ∈ batchDeletes U ∨ e ∈ batchInsEdges U) ∧
        (∀ a, OutOf dFl eCap a → OutOf dBuf eCap a → a ≠ dLen →
          OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen → st1.mem a = mem₀ a) ∧
        c1 ≤ 130 * (U.length - k) + 6 := by
    intro k
    induction hrem : U.length - k generalizing k with
    | zero =>
      intro hk cur W stK Ldk Lik _ _ _ _ _ _ _ _ _ r7k _ r9k hDdk hDik hLd hLi hfr
      have hkEq : k = U.length := by omega
      subst hkEq; rw [List.take_length] at hLd hLi
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stK = some 0 := by
        simp [Expr.eval, r7k, r9k, BinOp.eval, h0w]
      exact ⟨stK, 4, Ldk, Lik, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hDdk, hDik, hLd, hLi, hfr, by omega⟩
    | succ d ih =>
      intro hk cur W stK Ldk Lik hclo hchi hBB r1k r2k r3k r4k r5k r6k r7k r8k r9k hDdk hDik hLd hLi hfr
      have hklt : k < U.length := by omega
      obtain ⟨u, hu_eq⟩ : ∃ u, U[k]'hklt = u := ⟨_, rfl⟩
      have hdrop : U.drop k = u :: U.drop (k + 1) := by rw [← hu_eq]; exact List.drop_eq_getElem_cons hklt
      have htake : U.take (k + 1) = U.take k ++ [u] := by rw [← hu_eq]; exact List.take_succ_eq_append_getElem hklt
      rw [hdrop] at hBB
      obtain ⟨len, hlenW, huAt, hBBrest⟩ := hBB
      have huc := hCaps u (hu_eq ▸ List.getElem_mem hklt)
      have hbat_eq : ∀ a, cur ≤ a → a < cur + len → stK.mem a = mem₀ a := fun a ha1 ha2 => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hBat_disj a (by omega) (by omega)
        exact hfr a h1 h2 h3 h4 h5 h6
      have hbody : ∃ stA cA LdA LiA,
          Runs w p ω (asmFirstSeedBatchBody fPush) stK .normal stA cA ∧
          stA.regs 1 = dFl ∧ stA.regs 2 = dBuf ∧ stA.regs 3 = dLen ∧
          stA.regs 4 = iFl ∧ stA.regs 5 = iBuf ∧ stA.regs 6 = iLen ∧
          stA.regs 7 = U.length ∧ stA.regs 8 = cur + len ∧ stA.regs 9 = k ∧
          DedupBufAt stA.mem dFl dBuf dLen eCap LdA ∧
          DedupBufAt stA.mem iFl iBuf iLen eCap LiA ∧
          (∀ e, e ∈ LdA ↔ e ∈ Ld0 ∨ e ∈ batchDeletes (U.take (k + 1))) ∧
          (∀ e, e ∈ LiA ↔ e ∈ Li0 ∨ e ∈ batchDeletes (U.take (k + 1)) ∨ e ∈ batchInsEdges (U.take (k + 1))) ∧
          (∀ a, OutOf dFl eCap a → OutOf dBuf eCap a → a ≠ dLen →
            OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen → stA.mem a = mem₀ a) ∧
          cA ≤ 118 := by
        cases u with
        | insert e0 a0 b0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 0 := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          have hm1 : stK.mem (cur + 1) = e0 := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hL 1 (by simp))
          set rA := Function.update stK.regs 10 0
          set rB := Function.update rA 11 e0
          have h10 : Runs w p ω (.assign 10 (.load (.reg 8))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r8k) hm0, rfl, rfl, rfl⟩
          have heC : (Expr.bin .eq (.reg 10) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h0w, h1w]
          have h11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 8) (.const 1))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨e0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r8k])) (Expr.eval_const h1w) (by omega)) hm1, rfl, rfl, rfl⟩
          obtain ⟨stP, cP, hrP, hDi1, hfrP, hcP⟩ := asmFirstPushDedup_runs (p := p) (ω := ω) (pos := stK.pos)
            hw16 hDik huc hDisj_i.1 hDisj_i.2.1 hDisj_i.2.2 hiFl_w hiBuf_w hiLen_w
          have heArgs : evalArgs w ⟨stK.mem, rB, stK.pos⟩ [.reg 4, .reg 5, .reg 6, .reg 11] =
              some [iFl, iBuf, iLen, e0] :=
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r4k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r5k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB])) <| evalArgs_nil _ _
          set rC := Function.update rB 13 0
          set rD := Function.update rC 8 (cur + 4)
          have hcall : Runs w p ω (.call 13 fPush [.reg 4, .reg 5, .reg 6, .reg 11])
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stP.mem, rC, stP.pos⟩
              (argsSize [.reg 4, .reg 5, .reg 6, .reg 11] + cP + 1) :=
            runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP, cP, heArgs, hfPush, hrP, rfl, rfl, rfl⟩
          have h8 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 4)))
              ⟨stP.mem, rC, stP.pos⟩ .normal ⟨stP.mem, rD, stP.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 4, Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r8k]))
              (Expr.eval_const h4w) (by omega), rfl, rfl, rfl⟩
          have hDd1 : DedupBufAt stP.mem dFl dBuf dLen eCap Ldk :=
            dedupBufAt_of_agree hDdk
              (fun e he => let ⟨h1, h2, h3⟩ := hReg (dFl + e) (Or.inl ⟨by omega, by omega⟩); hfrP _ h1 h2 h3)
              (fun j hj => let hlt := dedupBuf_length_le hDdk
                let ⟨h1, h2, h3⟩ := hReg (dBuf + j) (Or.inr (Or.inl ⟨by omega, by omega⟩)); hfrP _ h1 h2 h3)
              (let ⟨h1, h2, h3⟩ := hReg dLen (Or.inr (Or.inr rfl)); hfrP _ h1 h2 h3)
          refine ⟨⟨stP.mem, rD, stP.pos⟩, _, Ldk, pushDedup Lik e0,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
              runs_cond_iff.mpr ⟨1, _, heC, by
                simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h11,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall, h8, rfl⟩), rfl⟩), rfl⟩, rfl⟩),
            by simp [rD, rC, rB, rA, r1k], by simp [rD, rC, rB, rA, r2k], by simp [rD, rC, rB, rA, r3k],
            by simp [rD, rC, rB, rA, r4k], by simp [rD, rC, rB, rA, r5k], by simp [rD, rC, rB, rA, r6k],
            by simp [rD, rC, rB, rA, r7k], by simp [rD], by simp [rD, rC, rB, rA, r9k],
            hDd1, hDi1, ?_, ?_, fun a h1 h2 h3 h4 h5 h6 => (hfrP a h4 h5 h6).trans (hfr a h1 h2 h3 h4 h5 h6),
            by simp only [Expr.size]; omega⟩
          · intro e; rw [htake, mem_batchDeletes_iff]; simp only [List.mem_append, List.mem_singleton]
            rw [hLd e, mem_batchDeletes_iff]; constructor
            · rintro (h | ⟨u', hu', rfl⟩); exact Or.inl h; exact Or.inr ⟨.delete e, Or.inl hu', rfl⟩
            · rintro (h | ⟨u', hu' | rfl, hdel⟩); exact Or.inl h; exact Or.inr ⟨u', hu', hdel⟩; cases hdel
          · intro e; rw [mem_pushDedup_iff, hLi e, htake, mem_batchInsEdges_append_singleton]
            have hdel_eq : e ∈ batchDeletes (U.take k ++ [.insert e0 a0 b0]) ↔ e ∈ batchDeletes (U.take k) := by
              simp only [mem_batchDeletes_iff, List.mem_append, List.mem_singleton]
              constructor
              · rintro ⟨u', hu' | rfl, hdel⟩; exact ⟨u', hu', hdel⟩; cases hdel
              · rintro ⟨u', hu', hdel⟩; exact ⟨u', Or.inl hu', hdel⟩
            rw [hdel_eq]; constructor
            · rintro ((h | h | h) | rfl); exact Or.inl h; exact Or.inr (Or.inl h)
              exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr ⟨a0, b0, rfl⟩))
            · rintro (h | h | h | ⟨a', b', hEq⟩)
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr (Or.inr h))
              · cases hEq; exact Or.inr rfl
        | delete e0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 1 := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          have hm1 : stK.mem (cur + 1) = e0 := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hL 1 (by simp))
          set rA := Function.update stK.regs 10 1
          set rB := Function.update rA 11 e0
          have h10 : Runs w p ω (.assign 10 (.load (.reg 8))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r8k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 10) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            simp [Expr.eval, rA, BinOp.eval, h0w]
          have heC1 : (Expr.bin .eq (.reg 10) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h1w]
          have h11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 8) (.const 1))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨e0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r8k])) (Expr.eval_const h1w) (by omega)) hm1, rfl, rfl, rfl⟩
          obtain ⟨stP1, cP1, hrP1, hDd1, hfrP1, hcP1⟩ := asmFirstPushDedup_runs (p := p) (ω := ω) (pos := stK.pos)
            hw16 hDdk huc hDisj_d.1 hDisj_d.2.1 hDisj_d.2.2 hdFl_w hdBuf_w hdLen_w
          have hDi_mid : DedupBufAt stP1.mem iFl iBuf iLen eCap Lik :=
            dedupBufAt_of_agree hDik
              (fun e he => let ⟨h1, h2, h3⟩ := hRegSym (iFl + e) (Or.inl ⟨by omega, by omega⟩); hfrP1 _ h1 h2 h3)
              (fun j hj => let hlt := dedupBuf_length_le hDik
                let ⟨h1, h2, h3⟩ := hRegSym (iBuf + j) (Or.inr (Or.inl ⟨by omega, by omega⟩)); hfrP1 _ h1 h2 h3)
              (let ⟨h1, h2, h3⟩ := hRegSym iLen (Or.inr (Or.inr rfl)); hfrP1 _ h1 h2 h3)
          obtain ⟨stP2, cP2, hrP2, hDi2, hfrP2, hcP2⟩ := asmFirstPushDedup_runs (p := p) (ω := ω) (pos := stP1.pos)
            hw16 hDi_mid huc hDisj_i.1 hDisj_i.2.1 hDisj_i.2.2 hiFl_w hiBuf_w hiLen_w
          have hDd2 : DedupBufAt stP2.mem dFl dBuf dLen eCap (pushDedup Ldk e0) :=
            dedupBufAt_of_agree hDd1
              (fun e he => let ⟨h1, h2, h3⟩ := hReg (dFl + e) (Or.inl ⟨by omega, by omega⟩); hfrP2 _ h1 h2 h3)
              (fun j hj => let hlt := dedupBuf_length_le hDd1
                let ⟨h1, h2, h3⟩ := hReg (dBuf + j) (Or.inr (Or.inl ⟨by omega, by omega⟩)); hfrP2 _ h1 h2 h3)
              (let ⟨h1, h2, h3⟩ := hReg dLen (Or.inr (Or.inr rfl)); hfrP2 _ h1 h2 h3)
          set rC := Function.update rB 13 0
          set rD := Function.update rC 13 0
          set rE := Function.update rD 8 (cur + 2)
          have heA1 : evalArgs w ⟨stK.mem, rB, stK.pos⟩ [.reg 1, .reg 2, .reg 3, .reg 11] =
              some [dFl, dBuf, dLen, e0] :=
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r1k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r2k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r3k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB])) <| evalArgs_nil _ _
          have hc1_run : Runs w p ω (.call 13 fPush [.reg 1, .reg 2, .reg 3, .reg 11])
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stP1.mem, rC, stP1.pos⟩
              (argsSize [.reg 1, .reg 2, .reg 3, .reg 11] + cP1 + 1) :=
            runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP1, cP1, heA1, hfPush, hrP1, rfl, rfl, rfl⟩
          have heA2 : evalArgs w ⟨stP1.mem, rC, stP1.pos⟩ [.reg 4, .reg 5, .reg 6, .reg 11] =
              some [iFl, iBuf, iLen, e0] :=
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r4k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r5k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r6k])) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB])) <| evalArgs_nil _ _
          have hc2_run : Runs w p ω (.call 13 fPush [.reg 4, .reg 5, .reg 6, .reg 11])
              ⟨stP1.mem, rC, stP1.pos⟩ .normal ⟨stP2.mem, rD, stP2.pos⟩
              (argsSize [.reg 4, .reg 5, .reg 6, .reg 11] + cP2 + 1) :=
            runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP2, cP2, heA2, hfPush, hrP2, rfl, rfl, rfl⟩
          have h8 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 2)))
              ⟨stP2.mem, rD, stP2.pos⟩ .normal ⟨stP2.mem, rE, stP2.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, r8k]))
              (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
          have hdel_iff : ∀ e, e ∈ batchDeletes (U.take k ++ [.delete e0]) ↔ e ∈ batchDeletes (U.take k) ∨ e = e0 := by
            intro e; simp only [mem_batchDeletes_iff, List.mem_append, List.mem_singleton]
            constructor
            · rintro ⟨u', hu' | rfl, hdel⟩; exact Or.inl ⟨u', hu', hdel⟩; cases hdel; exact Or.inr rfl
            · rintro (⟨u', hu', hdel⟩ | rfl); exact ⟨u', Or.inl hu', hdel⟩; exact ⟨.delete e, Or.inr rfl, rfl⟩
          refine ⟨⟨stP2.mem, rE, stP2.pos⟩, _, pushDedup Ldk e0, pushDedup Lik e0,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
              runs_cond_iff.mpr ⟨0, _, heC0, by
                simpa using runs_cond_iff.mpr ⟨1, _, heC1, by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h11,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc1_run,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc2_run, h8, rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
            by simp [rE, rD, rC, rB, rA, r1k], by simp [rE, rD, rC, rB, rA, r2k], by simp [rE, rD, rC, rB, rA, r3k],
            by simp [rE, rD, rC, rB, rA, r4k], by simp [rE, rD, rC, rB, rA, r5k], by simp [rE, rD, rC, rB, rA, r6k],
            by simp [rE, rD, rC, rB, rA, r7k], by simp [rE], by simp [rE, rD, rC, rB, rA, r9k],
            hDd2, hDi2, ?_, ?_,
            fun a h1 h2 h3 h4 h5 h6 => (hfrP2 a h4 h5 h6).trans ((hfrP1 a h1 h2 h3).trans (hfr a h1 h2 h3 h4 h5 h6)),
            by simp only [Expr.size]; omega⟩
          · intro e; rw [mem_pushDedup_iff, hLd e, htake, hdel_iff]; tauto
          · intro e; rw [mem_pushDedup_iff, hLi e, htake, hdel_iff, mem_batchInsEdges_append_singleton]
            simp only [reduceCtorEq, exists_false, or_false]; tauto
        | split v v' St Sh =>
          obtain ⟨tag, Lt, Lh, htag, hlen, hL⟩ :
              ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
                ListAt mem₀ cur ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
            rcases huAt with ⟨Lt, Lh, _, _, _, _, hlen, hL⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hL⟩
            · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hL⟩
            · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hL⟩
          have hm0 : stK.mem cur = tag := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          have hm3 : stK.mem (cur + 3) = Lt.length := (hbat_eq (cur + 3) (by omega) (by omega)).trans (by simpa using hL 3 (by simp))
          have hm4 : stK.mem (cur + 4) = Lh.length := (hbat_eq (cur + 4) (by omega) (by omega)).trans (by simpa using hL 4 (by simp))
          set rA := Function.update stK.regs 10 tag
          set rB := Function.update rA 11 Lt.length
          set rC := Function.update rB 12 Lh.length
          set rD := Function.update rC 8 (cur + len)
          have h10 : Runs w p ω (.assign 10 (.load (.reg 8))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r8k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 10) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, h0w]
          have heC1 : (Expr.bin .eq (.reg 10) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, h0w, h1w]
          have h11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 8) (.const 3))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lt.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r8k])) (Expr.eval_const h3w) (by omega)) hm3, rfl, rfl, rfl⟩
          have h12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 8) (.const 4))))
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stK.mem, rC, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lh.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r8k])) (Expr.eval_const h4w) (by omega)) hm4, rfl, rfl, rfl⟩
          have h8 : Runs w p ω (.assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 11)) (.reg 12)))
              ⟨stK.mem, rC, stK.pos⟩ .normal ⟨stK.mem, rD, stK.pos⟩ 8 := by
            have hrC8 : rC 8 = cur := by simp [rC, rB, rA, r8k]
            have hrC11 : rC 11 = Lt.length := by simp [rC, rB]
            have hrC12 : rC 12 = Lh.length := by simp [rC]
            have he1 : (Expr.bin .add (.reg 8) (.const 5)).eval w ⟨stK.mem, rC, stK.pos⟩ = some (cur + 5) :=
              Expr.eval_add (Expr.eval_reg_of_eq hrC8) (Expr.eval_const h5w) (by omega)
            have he2 : (Expr.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 11)).eval w ⟨stK.mem, rC, stK.pos⟩ =
                some (cur + 5 + Lt.length) := Expr.eval_add he1 (Expr.eval_reg_of_eq hrC11) (by omega)
            have he3 : (Expr.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 11)) (.reg 12)).eval w
                ⟨stK.mem, rC, stK.pos⟩ = some (cur + 5 + Lt.length + Lh.length) :=
              Expr.eval_add he2 (Expr.eval_reg_of_eq hrC12) (by omega)
            rw [show cur + 5 + Lt.length + Lh.length = cur + len by omega] at he3
            exact runs_assign_iff.mpr ⟨cur + len, he3, rfl, rfl, rfl⟩
          have hdel_eq : ∀ e, e ∈ batchDeletes (U.take k ++ [.split v v' St Sh]) ↔ e ∈ batchDeletes (U.take k) := by
            intro e; simp only [mem_batchDeletes_iff, List.mem_append, List.mem_singleton]
            constructor
            · rintro ⟨u', hu' | rfl, hdel⟩; exact ⟨u', hu', hdel⟩; cases hdel
            · rintro ⟨u', hu', hdel⟩; exact ⟨u', Or.inl hu', hdel⟩
          refine ⟨⟨stK.mem, rD, stK.pos⟩, 32, Ldk, Lik,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
              runs_cond_iff.mpr ⟨0, 24, heC0, by
                simpa using runs_cond_iff.mpr ⟨0, 20, heC1, by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h11,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h12, h8, rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
            by simp [rD, rC, rB, rA, r1k], by simp [rD, rC, rB, rA, r2k], by simp [rD, rC, rB, rA, r3k],
            by simp [rD, rC, rB, rA, r4k], by simp [rD, rC, rB, rA, r5k], by simp [rD, rC, rB, rA, r6k],
            by simp [rD, rC, rB, rA, r7k], by simp [rD], by simp [rD, rC, rB, rA, r9k],
            hDdk, hDik, fun e => by rw [htake, hdel_eq, hLd e],
            fun e => by rw [htake, hdel_eq, mem_batchInsEdges_append_singleton]; simp [hLi e],
            hfr, by omega⟩
      obtain ⟨stA, cA, LdA, LiA, hrA, r1A, r2A, r3A, r4A, r5A, r6A, r7A, r8A, r9A, hDdA, hDiA, hLdA, hLiA, hfrA, hcA⟩ := hbody
      set stB : State := ⟨stA.mem, Function.update stA.regs 9 (k + 1), stA.pos⟩
      have ha9s : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) stA .normal stB 4 :=
        runs_assign_iff.mpr ⟨k + 1, Expr.eval_add (Expr.eval_reg_of_eq r9A) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      have hGnext : G₀.applyBatch (U.take (k + 1)) = (G₀.applyBatch (U.take k)).applyUpdate u := by
        rw [htake, applyBatch_append]; rfl
      obtain ⟨st1, c1, Ld, Li, hr1, hDdf, hDif, hLdf, hLif, hfrf, hc1⟩ :=
        ih (k + 1) (by omega) (by omega) (cur + len) (W - len) stB LdA LiA (by omega) (by omega)
          (hGnext.symm ▸ hBBrest)
          (by simp [stB, r1A]) (by simp [stB, r2A]) (by simp [stB, r3A])
          (by simp [stB, r4A]) (by simp [stB, r5A]) (by simp [stB, r6A])
          (by simp [stB, r7A]) (by simp [stB, r8A]) (by simp [stB])
          hDdA hDiA hLdA hLiA hfrA
      have hcond : (Expr.bin .lt (.reg 9) (.reg 7)).eval w stK = some 1 := by
        simp [Expr.eval, r7k, r9k, BinOp.eval, hklt, h1w]
      exact ⟨st1, _, Ld, Li, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, _, c1, hcond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨stA, cA, 4, hrA, ha9s, rfl⟩), hr1, rfl⟩)),
        hDdf, hDif, hLdf, hLif, hfrf, by simp only [Expr.size]; omega⟩
  obtain ⟨st1, c1, Ld, Li, hrB, hDdf, hDif, hLdf, hLif, hfrf, hc1⟩ :=
    hloop 0 (Nat.zero_le _) (batch + 1) (words - 1) ⟨mem₀, r3, pos⟩ Ld0 Li0
      (by omega) (by have := hBat.1; omega) hBat.2.2
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1]) (by simp [r3, r2]) (by simp [r3])
      hDd hDi (fun e => by simp [batchDeletes]) (fun e => by simp [batchDeletes, batchInsEdges])
      (fun _ _ _ _ _ _ _ => rfl)
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hseqLoop : Runs w p ω (forRange 9 (.const 0) (.reg 7) (asmFirstSeedBatchBody fPush))
      ⟨mem₀, r2, pos⟩ .normal st1 (2 + c1 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha9, hrB, rfl⟩)
  exact ⟨st1, _, Ld, Li,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha8,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hseqLoop, hret, rfl⟩), rfl⟩), rfl⟩),
    hDdf, hDif, hLdf, hLif, hfrf, by omega⟩

/-! ## Verification of `asmFirstSeedLazyStmt` -/

theorem asmFirstSeedLazy_runs {w fPush fAppend lazyPtr nNew eCap pos : ℕ}
    {iFl iBuf iLen rFl rBuf rLen : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfAppend : p.procs[fAppend]? = some (asmFirstAppendListStmt fPush))
    {Li0 Lr0 : List ℕ} {lazyE : Fin nNew → List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDi : DedupBufAt mem₀ iFl iBuf iLen eCap Li0)
    (hDr : DedupBufAt mem₀ rFl rBuf rLen eCap Lr0)
    (hLazy : ∀ (i : Fin nNew),
      ∃ ptr, mem₀ (lazyPtr + 2 * i.1) = ptr ∧ mem₀ (lazyPtr + 2 * i.1 + 1) = (lazyE i).length ∧
        ListAt mem₀ ptr (lazyE i) ∧ ptr + (lazyE i).length < 2 ^ w ∧
        (∀ e ∈ lazyE i, e < eCap) ∧
        (ptr + (lazyE i).length ≤ iFl ∨ iFl + eCap ≤ ptr) ∧
        (ptr + (lazyE i).length ≤ iBuf ∨ iBuf + eCap ≤ ptr) ∧
        (iLen < ptr ∨ ptr + (lazyE i).length ≤ iLen) ∧
        (ptr + (lazyE i).length ≤ rFl ∨ rFl + eCap ≤ ptr) ∧
        (ptr + (lazyE i).length ≤ rBuf ∨ rBuf + eCap ≤ ptr) ∧
        (rLen < ptr ∨ ptr + (lazyE i).length ≤ rLen))
    (hLazy_disj : ∀ a, lazyPtr ≤ a → a < lazyPtr + 2 * nNew →
      OutOf iFl eCap a ∧ OutOf iBuf eCap a ∧ a ≠ iLen ∧
      OutOf rFl eCap a ∧ OutOf rBuf eCap a ∧ a ≠ rLen)
    (hReg : ∀ a, (iFl ≤ a ∧ a < iFl + eCap ∨ iBuf ≤ a ∧ a < iBuf + eCap ∨ a = iLen) →
      OutOf rFl eCap a ∧ OutOf rBuf eCap a ∧ a ≠ rLen)
    (hDisj_i : (iFl + eCap ≤ iBuf ∨ iBuf + eCap ≤ iFl) ∧ OutOf iFl eCap iLen ∧ OutOf iBuf eCap iLen)
    (hDisj_r : (rFl + eCap ≤ rBuf ∨ rBuf + eCap ≤ rFl) ∧ OutOf rFl eCap rLen ∧ OutOf rBuf eCap rLen)
    (hLazy_w : lazyPtr + 2 * nNew < 2 ^ w)
    (hiFl_w : iFl + eCap < 2 ^ w) (hiBuf_w : iBuf + eCap < 2 ^ w) (hiLen_w : iLen < 2 ^ w)
    (hrFl_w : rFl + eCap < 2 ^ w) (hrBuf_w : rBuf + eCap < 2 ^ w) (hrLen_w : rLen < 2 ^ w) :
    ∃ st' cost Li Lr,
      Runs w p ω (asmFirstSeedLazyStmt fAppend)
        (startState [iFl, iBuf, iLen, rFl, rBuf, rLen, lazyPtr, nNew] mem₀ pos) (.returned 0) st' cost ∧
      DedupBufAt st'.mem iFl iBuf iLen eCap Li ∧
      DedupBufAt st'.mem rFl rBuf rLen eCap Lr ∧
      (∀ e, e ∈ Li ↔ e ∈ Li0 ∨ ∃ i : Fin nNew, e ∈ lazyE i) ∧
      (∀ e, e ∈ Lr ↔ e ∈ Lr0 ∨ ∃ i : Fin nNew, e ∈ lazyE i) ∧
      (∀ a, OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen →
        OutOf rFl eCap a → OutOf rBuf eCap a → a ≠ rLen → st'.mem a = mem₀ a) ∧
      cost ≤ 130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum + 90 * nNew + 25 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hRegSym : ∀ a, (rFl ≤ a ∧ a < rFl + eCap ∨ rBuf ≤ a ∧ a < rBuf + eCap ∨ a = rLen) →
      OutOf iFl eCap a ∧ OutOf iBuf eCap a ∧ a ≠ iLen := by
    intro a hr
    refine ⟨?_, ?_, ?_⟩
    · by_contra h; simp only [OutOf, not_or, not_lt, not_le] at h
      have := hReg a (Or.inl h); rcases hr with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
    · by_contra h; simp only [OutOf, not_or, not_lt, not_le] at h
      have := hReg a (Or.inr (Or.inl h)); rcases hr with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
    · intro h; have := hReg a (Or.inr (Or.inr h))
      rcases hr with h1 | h1 | h1 <;> simp only [OutOf] at this <;> omega
  let stepCost : ℕ → ℕ := fun k =>
    if hk : k < nNew then 130 * (lazyE ⟨k, hk⟩).length + 75 else 0
  let inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = iFl ∧ st.regs 1 = iBuf ∧ st.regs 2 = iLen ∧
    st.regs 3 = rFl ∧ st.regs 4 = rBuf ∧ st.regs 5 = rLen ∧
    st.regs 6 = lazyPtr ∧ st.regs 7 = nNew ∧ st.regs 8 = k ∧
    (∃ Lik Lrk, DedupBufAt st.mem iFl iBuf iLen eCap Lik ∧ DedupBufAt st.mem rFl rBuf rLen eCap Lrk ∧
      (∀ e, e ∈ Lik ↔ e ∈ Li0 ∨ ∃ (j : Fin nNew), j.1 < k ∧ e ∈ lazyE j) ∧
      (∀ e, e ∈ Lrk ↔ e ∈ Lr0 ∨ ∃ (j : Fin nNew), j.1 < k ∧ e ∈ lazyE j)) ∧
    (∀ a, OutOf iFl eCap a → OutOf iBuf eCap a → a ≠ iLen →
      OutOf rFl eCap a → OutOf rBuf eCap a → a ≠ rLen → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := .assign 9 (.load (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8)))) ;;
      .assign 10 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8))) (.const 1))) ;;
      .call 11 fAppend [.reg 0, .reg 1, .reg 2, .reg 9, .reg 10] ;;
      .call 11 fAppend [.reg 3, .reg 4, .reg 5, .reg 9, .reg 10])
    (P := fun st => inv 0 { st with regs := Function.update st.regs 8 0 })
    (Inv := inv) stepCost 0 nNew (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.2.1)
    (fun k _ hk st ω' ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, ⟨Lik, Lrk, hDik, hDrk, hLik, hLrk⟩, hfr⟩ => by
      set kf : Fin nNew := ⟨k, hk⟩
      obtain ⟨ptr, hptr, hlen, hlat, hptr_w, hcap, hsf_i, hsb_i, hsl_i, hsf_r, hsb_r, hsl_r⟩ := hLazy kf
      have hm_ptr : st.mem (lazyPtr + 2 * k) = ptr := by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLazy_disj (lazyPtr + 2 * k) (by omega) (by omega)
        exact (hfr _ h1 h2 h3 h4 h5 h6).trans hptr
      have hm_len : st.mem (lazyPtr + 2 * k + 1) = (lazyE kf).length := by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hLazy_disj (lazyPtr + 2 * k + 1) (by omega) (by omega)
        exact (hfr _ h1 h2 h3 h4 h5 h6).trans hlen
      have hlat_st : ListAt st.mem ptr (lazyE kf) := fun j hj => by
        exact (hfr (ptr + j) (by rcases hsf_i with h | h <;> simp only [OutOf] <;> omega)
          (by rcases hsb_i with h | h <;> simp only [OutOf] <;> omega) (by rcases hsl_i with h | h <;> omega)
          (by rcases hsf_r with h | h <;> simp only [OutOf] <;> omega)
          (by rcases hsb_r with h | h <;> simp only [OutOf] <;> omega) (by rcases hsl_r with h | h <;> omega)).trans
          (hlat j hj)
      set rA := Function.update st.regs 9 ptr
      set rB := Function.update rA 10 (lazyE kf).length
      set rC := Function.update rB 11 0
      have h9 : Runs w p ω' (.assign 9 (.load (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8)))))
          st .normal ⟨st.mem, rA, st.pos⟩ 7 :=
        runs_assign_iff.mpr ⟨ptr, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r6)
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq r8) (by omega)) (by omega)) hm_ptr,
          rfl, rfl, rfl⟩
      have h10 : Runs w p ω'
          (.assign 10 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8))) (.const 1))))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩ 9 := by
        have he1 : (Expr.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8))).eval w ⟨st.mem, rA, st.pos⟩ =
            some (lazyPtr + 2 * k) :=
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6]))
            (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [rA, r8])) (by omega)) (by omega)
        exact runs_assign_iff.mpr ⟨(lazyE kf).length, Expr.eval_load_of_eq
          (Expr.eval_add he1 (Expr.eval_const h1w) (by omega)) hm_len, rfl, rfl, rfl⟩
      obtain ⟨st1, c1, hr1, hDi1, hfr1, hc1⟩ := asmFirstAppendList_runs (p := p) (ω := ω') (pos := st.pos)
        hfPush hw16 hDik hlat_st hcap hDisj_i.1 hDisj_i.2.1 hDisj_i.2.2 hsf_i hsb_i hsl_i
        hiFl_w hiBuf_w hiLen_w hptr_w
      have hDr_mid : DedupBufAt st1.mem rFl rBuf rLen eCap Lrk :=
        dedupBufAt_of_agree hDrk
          (fun e he => let ⟨h1, h2, h3⟩ := hRegSym (rFl + e) (Or.inl ⟨by omega, by omega⟩); hfr1 _ h1 h2 h3)
          (fun j hj => let hlt := dedupBuf_length_le hDrk
            let ⟨h1, h2, h3⟩ := hRegSym (rBuf + j) (Or.inr (Or.inl ⟨by omega, by omega⟩)); hfr1 _ h1 h2 h3)
          (let ⟨h1, h2, h3⟩ := hRegSym rLen (Or.inr (Or.inr rfl)); hfr1 _ h1 h2 h3)
      have hlat_1 : ListAt st1.mem ptr (lazyE kf) := fun j hj => by
        exact (hfr1 (ptr + j) (by rcases hsf_i with h | h <;> omega)
          (by rcases hsb_i with h | h <;> omega) (by rcases hsl_i with h | h <;> omega)).trans (hlat_st j hj)
      obtain ⟨st2, c2, hr2, hDr2, hfr2, hc2⟩ := asmFirstAppendList_runs (p := p) (ω := ω') (pos := st1.pos)
        hfPush hw16 hDr_mid hlat_1 hcap hDisj_r.1 hDisj_r.2.1 hDisj_r.2.2 hsf_r hsb_r hsl_r
        hrFl_w hrBuf_w hrLen_w hptr_w
      have hDi2 : DedupBufAt st2.mem iFl iBuf iLen eCap (appendDedup Lik (lazyE kf)) :=
        dedupBufAt_of_agree hDi1
          (fun e he => let ⟨h1, h2, h3⟩ := hReg (iFl + e) (Or.inl ⟨by omega, by omega⟩); hfr2 _ h1 h2 h3)
          (fun j hj => let hlt := dedupBuf_length_le hDi1
            let ⟨h1, h2, h3⟩ := hReg (iBuf + j) (Or.inr (Or.inl ⟨by omega, by omega⟩)); hfr2 _ h1 h2 h3)
          (let ⟨h1, h2, h3⟩ := hReg iLen (Or.inr (Or.inr rfl)); hfr2 _ h1 h2 h3)
      have heA1 : evalArgs w ⟨st.mem, rB, st.pos⟩ [.reg 0, .reg 1, .reg 2, .reg 9, .reg 10] =
          some [iFl, iBuf, iLen, ptr, (lazyE kf).length] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r0])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r1])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r2])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB])) <| evalArgs_nil _ _
      have hc1_run : Runs w p ω' (.call 11 fAppend [.reg 0, .reg 1, .reg 2, .reg 9, .reg 10])
          ⟨st.mem, rB, st.pos⟩ .normal ⟨st1.mem, rC, st1.pos⟩
          (argsSize [.reg 0, .reg 1, .reg 2, .reg 9, .reg 10] + c1 + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstAppendListStmt fPush, .returned 0, st1, c1, heA1, hfAppend, hr1, rfl, rfl, rfl⟩
      have heA2 : evalArgs w ⟨st1.mem, rC, st1.pos⟩ [.reg 3, .reg 4, .reg 5, .reg 9, .reg 10] =
          some [rFl, rBuf, rLen, ptr, (lazyE kf).length] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r3])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r4])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r5])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB])) <| evalArgs_nil _ _
      have hc2_run : Runs w p ω' (.call 11 fAppend [.reg 3, .reg 4, .reg 5, .reg 9, .reg 10])
          ⟨st1.mem, rC, st1.pos⟩ .normal ⟨st2.mem, Function.update rC 11 0, st2.pos⟩
          (argsSize [.reg 3, .reg 4, .reg 5, .reg 9, .reg 10] + c2 + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstAppendListStmt fPush, .returned 0, st2, c2, heA2, hfAppend, hr2, rfl, rfl, rfl⟩
      refine ⟨.normal, ⟨st2.mem, Function.update rC 11 0, st2.pos⟩, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc1_run, hc2_run, rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by simp [rC, rB, rA, r0], by simp [rC, rB, rA, r1], by simp [rC, rB, rA, r2],
          by simp [rC, rB, rA, r3], by simp [rC, rB, rA, r4], by simp [rC, rB, rA, r5],
          by simp [rC, rB, rA, r6], by simp [rC, rB, rA, r7], by simp,
          ⟨appendDedup Lik (lazyE kf), appendDedup Lrk (lazyE kf), hDi2, hDr2, ?_, ?_⟩,
          fun a h1 h2 h3 h4 h5 h6 => (hfr2 a h4 h5 h6).trans ((hfr1 a h1 h2 h3).trans (hfr a h1 h2 h3 h4 h5 h6))⟩,
         by simp [rC, rB, rA, r8]⟩, ?_⟩
      · intro e; rw [mem_appendDedup_iff, hLik e]; constructor
        · rintro ((h | ⟨j, hjk, hj⟩) | hk_e)
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, hj⟩
          · exact Or.inr ⟨kf, by simp [kf], hk_e⟩
        · rintro (h | ⟨j, hjk, hj⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hjeq : j.1 = k
            · exact Or.inr (by have : j = kf := Fin.ext hjeq; rwa [← this])
            · exact Or.inl (Or.inr ⟨j, by omega, hj⟩)
      · intro e; rw [mem_appendDedup_iff, hLrk e]; constructor
        · rintro ((h | ⟨j, hjk, hj⟩) | hk_e)
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, hj⟩
          · exact Or.inr ⟨kf, by simp [kf], hk_e⟩
        · rintro (h | ⟨j, hjk, hj⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hjeq : j.1 = k
            · exact Or.inr (by have : j = kf := Fin.ext hjeq; rwa [← this])
            · exact Or.inl (Or.inr ⟨j, by omega, hj⟩)
      · dsimp only [stepCost, kf] at hc1 hc2 ⊢; simp only [hk, ↓reduceDIte, argsSize, Expr.size]; omega)
  set s0 := startState [iFl, iBuf, iLen, rFl, rBuf, rLen, lazyPtr, nNew] mem₀ pos
  obtain ⟨o, st1, c1, hr1, hpost1, hc1⟩ := hloop s0 ω
    ⟨by simp [s0, startState], by simp [s0, startState], by simp [s0, startState],
     by simp [s0, startState], by simp [s0, startState], by simp [s0, startState],
     by simp [s0, startState], by simp [s0, startState], by simp,
     ⟨Li0, Lr0, by simpa [s0, startState] using hDi, by simpa [s0, startState] using hDr,
      fun e => by simp, fun e => by simp⟩, fun _ _ _ _ _ _ _ => rfl⟩
  cases o with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨Li, Lr, hDif, hDrf, hLif, hLrf⟩, hfrf⟩ := hpost1
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hrc : rangeCost stepCost 0 nNew =
      130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum + 75 * nNew := by
    have hsum : ∀ m (hm : m ≤ nNew),
        rangeCost stepCost 0 m =
          130 * (((List.finRange nNew).take m).map fun i => (lazyE i).length).sum + 75 * m := by
      intro m; induction m with
      | zero => intro _; simp [rangeCost]
      | succ k ih =>
        intro hk
        have h1 : rangeCost stepCost 0 (k + 1) = rangeCost stepCost 0 k + stepCost k := by
          simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.range_succ,
            List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, Nat.zero_add]
        have htk : (List.finRange nNew).take (k + 1) = (List.finRange nNew).take k ++ [⟨k, by omega⟩] := by
          rw [List.take_succ_eq_append_getElem (by simp; omega)]
          simp
        rw [h1, ih (by omega), htk, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        dsimp only [stepCost]; simp only [show k < nNew by omega, ↓reduceDIte]; omega
    have hfinal := hsum nNew le_rfl
    rwa [List.take_of_length_le (by simp)] at hfinal
  dsimp only at hc1; simp only [hrc, Nat.sub_zero, Expr.size] at hc1
  exact ⟨st1, c1 + 2 + 1, Li, Lr, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hret, rfl⟩),
    hDif, hDrf,
    fun e => by simpa using hLif e,
    fun e => by simpa using hLrf e,
    hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
