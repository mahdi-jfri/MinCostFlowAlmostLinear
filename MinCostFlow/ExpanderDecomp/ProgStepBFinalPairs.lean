module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBRound

import Mathlib.Tactic.Linarith

/-!
# Step B Final Phase Pair Encoding (`ProgStepBFinalPairs`)

Implements and verifies `sbFinalBuildPairsStmt`, encoding the final complement-injection
terminal pairs `injPairs = [(B_i \ S_i, S_i)]_{i < nBlocks}` into `[r12, r12 + 1 + nBlocks * (2 + b))`.

Main results:
- `sbFinalBuildPairsStmt`, `sbFinalBuildPairsStmt_noRand`
- `sbFinalBuildPairs_triple`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Encodes `injPairs = [(B_i \ S_i, S_i)]_{i < nBlocks}` into `[r12, r12 + 1 + nBlocks * (2 + b))`,
setting `r22 := r12` (`pairsA`) and `r23 := r12 + 1 + nBlocks * (2 + b)`. -/
def sbFinalBuildPairsStmt : Stmt :=
  seqStmts [
    .assign 22 (.reg 12),
    .store (.reg 22) (.reg 5),
    .assign 23 (.bin .add (.reg 22) (.const 1)),
    forRange 24 (.const 0) (.reg 5) (
      seqStmts [
        .assign 25 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 24))),
        .store (.reg 23) (.reg 25),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 19) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 25 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 25)),
        .assign 27 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 24))),
        .store (.reg 23) (.reg 27),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 18) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 27 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 27))
      ])
  ]

theorem sbFinalBuildPairsStmt_noRand : sbFinalBuildPairsStmt.NoRand := by
  simp [sbFinalBuildPairsStmt, scCopySliceStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. Pair-Encoding Triple (`sbFinalBuildPairs_triple`) -/

private lemma flatMap_encodePair_take_len {L : List (List ℕ × List ℕ)} {b j : ℕ}
    (hsum : ∀ p ∈ L, p.1.length + p.2.length = b) (hj : j ≤ L.length) :
    ((L.take j).flatMap encodePair).length = j * (2 + b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjlt : j < L.length := by omega
    rw [List.take_succ_eq_append_getElem hjlt, List.flatMap_append, List.flatMap_singleton,
      List.length_append, ih (by omega)]
    have hp := hsum (L[j]'hjlt) (List.getElem_mem hjlt)
    have he : (encodePair (L[j]'hjlt)).length = 2 + b := by
      simp only [encodePair, List.length_cons, List.length_append]; omega
    rw [he, Nat.succ_mul]

private lemma listAt_append_of_parts {mem : ℕ → ℕ} {a : ℕ} {l1 l2 : List ℕ}
    (h1 : ListAt mem a l1) (h2 : ListAt mem (a + l1.length) l2) :
    ListAt mem a (l1 ++ l2) := by
  intro idx hidx
  by_cases hlt : idx < l1.length
  · rw [List.getElem_append_left hlt]; exact h1 idx hlt
  · rw [List.getElem_append_right (by omega)]
    have hge : a + idx = a + l1.length + (idx - l1.length) := by omega
    rw [hge]; exact h2 (idx - l1.length) (by rw [List.length_append] at hidx; omega)

private lemma sbFinalBuildPairs_body {w b nBlocks pairsA actA savLenA cmpLenA savA cmpA j : ℕ}
    {p : Program} {cL sL : List ℕ} {st : State} {ω : ℕ → Bool}
    (hjlt : j < nBlocks) (hcs_sum : cL.length + sL.length = b)
    (hord : actA + nBlocks = savLenA ∧ savLenA + nBlocks = cmpLenA ∧ cmpLenA + nBlocks = savA ∧
      savA + nBlocks * b = cmpA ∧ cmpA + nBlocks * b ≤ pairsA)
    (hpairs_w : pairsA + 1 + nBlocks * (2 + b) < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hcmpLen_m : st.mem (cmpLenA + j) = cL.length) (hsavLen_m : st.mem (savLenA + j) = sL.length)
    (hcmpL_m : ListAt st.mem (cmpA + j * b) cL) (hsavL_m : ListAt st.mem (savA + j * b) sL)
    (hregs : st.regs 4 = b ∧ st.regs 5 = nBlocks ∧ st.regs 17 = actA ∧ st.regs 18 = savA ∧
      st.regs 19 = cmpA ∧ st.regs 22 = pairsA ∧ st.regs 23 = pairsA + 1 + j * (2 + b) ∧ st.regs 24 = j) :
    ∃ st4 c,
      Runs w p ω (seqStmts [
        .assign 25 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 24))),
        .store (.reg 23) (.reg 25),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 19) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 25 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 25)),
        .assign 27 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 24))),
        .store (.reg 23) (.reg 27),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 18) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 27 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 27))]) st .normal st4 c ∧
      st4.regs 22 = pairsA ∧
      st4.regs 23 = pairsA + 1 + (j + 1) * (2 + b) ∧
      st4.regs 24 = j ∧
      (∀ r < 22, st4.regs r = st.regs r) ∧
      st4.pos = st.pos ∧
      MemFrame st.mem st4.mem (pairsA + 1 + j * (2 + b)) (pairsA + 1 + (j + 1) * (2 + b)) ∧
      ListAt st4.mem (pairsA + 1 + j * (2 + b)) (encodePair (cL, sL)) ∧
      c ≤ 36 * b + 140 := by
  set pCur := pairsA + 1 + j * (2 + b)
  rcases hord with ⟨ho1, ho2, ho3, ho4, ho5⟩
  rcases hregs with ⟨hr4, hr5, hr17, hr18, hr19, hr22, hr23, hr24⟩
  have hjm : j * b + b ≤ nBlocks * b := by
    have := Nat.mul_le_mul_right b (show j + 1 ≤ nBlocks by omega); rwa [Nat.succ_mul] at this
  have hj2 : j * (2 + b) + (2 + b) ≤ nBlocks * (2 + b) := by
    have := Nat.mul_le_mul_right (2 + b) (show j + 1 ≤ nBlocks by omega); rwa [Nat.succ_mul] at this
  have hpCur_succ : pCur + (2 + b) = pairsA + 1 + (j + 1) * (2 + b) := by
    dsimp only [pCur]; rw [Nat.succ_mul]; omega
  have hrun : ∃ o st4 c,
      Runs w p ω (seqStmts [
        .assign 25 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 24))),
        .store (.reg 23) (.reg 25),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 19) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 25 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 25)),
        .assign 27 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 24))),
        .store (.reg 23) (.reg 27),
        .assign 23 (.bin .add (.reg 23) (.const 1)),
        .assign 26 (.bin .add (.reg 18) (.bin .mul (.reg 24) (.reg 4))),
        scCopySliceStmt 26 23 27 28 29,
        .assign 23 (.bin .add (.reg 23) (.reg 27))]) st o st4 c ∧
      (normalPost fun st4 =>
        st4.regs 22 = pairsA ∧ st4.regs 23 = pairsA + 1 + (j + 1) * (2 + b) ∧ st4.regs 24 = j ∧
        (∀ r < 22, st4.regs r = st.regs r) ∧ st4.pos = st.pos ∧
        MemFrame st.mem st4.mem pCur (pairsA + 1 + (j + 1) * (2 + b)) ∧
        ListAt st4.mem pCur (encodePair (cL, sL))) o st4 ∧
      c ≤ 36 * b + 140 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := cL.length)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr17)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr5) (by omega)) (by omega))
          (Expr.eval_reg_of_eq hr24) (by omega))
        (by have hcmp : actA + 2 * nBlocks + j = cmpLenA + j := by omega
            rw [hcmp]; exact hcmpLen_m)) ?_
    refine runs_seq_store_le (x := pCur) (v := cL.length)
      (Expr.eval_reg_of_eq (v := pCur) (by dsimp only; rw [Function.update_of_ne (by decide), hr23]))
      (Expr.eval_reg_of_eq (v := cL.length) (by simp)) ?_
    refine runs_seq_assign_le (v := pCur + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := pCur) (by dsimp only; rw [Function.update_of_ne (by decide), hr23]))
        (Expr.eval_const (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := cmpA + j * b)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := cmpA) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr19]))
        (Expr.eval_mul
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr24]))
          (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4]))
          (by omega)) (by omega)) ?_
    generalize hst1_eq : (State.mk (Function.update st.mem pCur cL.length)
      (Function.update (Function.update (Function.update st.regs 25 cL.length) 23 (pCur + 1)) 26 (cmpA + j * b))
      st.pos) = st1
    have hst1_m : ∀ a, a ≠ pCur → st1.mem a = st.mem a := fun a ha => by
      rw [← hst1_eq]; exact Function.update_of_ne ha _ _
    have hst1_r : st1.regs 26 = cmpA + j * b ∧ st1.regs 23 = pCur + 1 ∧ st1.regs 25 = cL.length ∧
        st1.regs 24 = j ∧ st1.regs 22 = pairsA ∧ (∀ r < 22, st1.regs r = st.regs r) := by
      rw [← hst1_eq]; refine ⟨by simp, by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr24],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr22],
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]⟩
    refine runs_seq_triple_le
      (scCopySlice_triple (w := w) (srcA := cmpA + j * b) (dstA := pCur + 1) (len := cL.length)
        (rSrc := 26) (rDst := 23) (rLen := 25) (rI := 28) (rTmp := 29) (by decide)
        p st1.mem cL st1 rfl (fun u hu => (hst1_m _ (by omega)).trans (hcmpL_m u hu))
        (Or.inr (by omega)) (by omega) (by omega) hw16 hst1_r.1 hst1_r.2.1 hst1_r.2.2.1 rfl) rfl ?_
    intro st2 ⟨hoth2, hpos2, hfr2, hcAt2⟩
    refine runs_seq_assign_le (v := pCur + 1 + cL.length)
      (Expr.eval_add (Expr.eval_reg_of_eq ((hoth2 23 (by decide) (by decide)).trans hst1_r.2.1))
        (Expr.eval_reg_of_eq ((hoth2 25 (by decide) (by decide)).trans hst1_r.2.2.1)) (by omega)) ?_
    refine runs_seq_assign_le (v := sL.length)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (v := actA) (by dsimp only; rw [Function.update_of_ne (by decide), hoth2 17 (by decide) (by decide), hst1_r.2.2.2.2.2 17 (by decide), hr17]))
          (Expr.eval_reg_of_eq (v := nBlocks) (by dsimp only; rw [Function.update_of_ne (by decide), hoth2 5 (by decide) (by decide), hst1_r.2.2.2.2.2 5 (by decide), hr5]))
          (by omega))
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hoth2 24 (by decide) (by decide), hst1_r.2.2.2.1]))
          (by omega))
        (by rw [ho1, hfr2 _ (Or.inl (by omega)), hst1_m _ (by omega)]; exact hsavLen_m)) ?_
    refine runs_seq_store_le (x := pCur + 1 + cL.length) (v := sL.length)
      (Expr.eval_reg_of_eq (v := pCur + 1 + cL.length) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
      (Expr.eval_reg_of_eq (v := sL.length) (by simp)) ?_
    refine runs_seq_assign_le (v := pCur + 2 + cL.length)
      (by have heq : pCur + 1 + cL.length + 1 = pCur + 2 + cL.length := by omega
          exact heq ▸ Expr.eval_add
            (Expr.eval_reg_of_eq (v := pCur + 1 + cL.length) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
            (Expr.eval_const (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := savA + j * b)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := savA) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth2 18 (by decide) (by decide), hst1_r.2.2.2.2.2 18 (by decide), hr18]))
        (Expr.eval_mul
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth2 24 (by decide) (by decide), hst1_r.2.2.2.1]))
          (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth2 4 (by decide) (by decide), hst1_r.2.2.2.2.2 4 (by decide), hr4]))
          (by omega)) (by omega)) ?_
    generalize hst3_eq : (State.mk (Function.update st2.mem (pCur + 1 + cL.length) sL.length)
      (Function.update (Function.update (Function.update (Function.update st2.regs 23 (pCur + 1 + cL.length)) 27 sL.length) 23 (pCur + 2 + cL.length)) 26 (savA + j * b))
      st2.pos) = st3
    have hst3_m : ∀ a, a ≠ pCur + 1 + cL.length → st3.mem a = st2.mem a := fun a ha => by
      rw [← hst3_eq]; exact Function.update_of_ne ha _ _
    have hst3_r : st3.regs 26 = savA + j * b ∧ st3.regs 23 = pCur + 2 + cL.length ∧ st3.regs 27 = sL.length ∧
        st3.regs 24 = j ∧ st3.regs 22 = pairsA ∧ (∀ r < 22, st3.regs r = st.regs r) := by
      rw [← hst3_eq]; refine ⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth2 24 (by decide) (by decide), hst1_r.2.2.2.1],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth2 22 (by decide) (by decide), hst1_r.2.2.2.2.1],
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth2 r (by omega) (by omega)]; exact hst1_r.2.2.2.2.2 r hr⟩
    refine runs_seq_triple_le
      (scCopySlice_triple (w := w) (srcA := savA + j * b) (dstA := pCur + 2 + cL.length) (len := sL.length)
        (rSrc := 26) (rDst := 23) (rLen := 27) (rI := 28) (rTmp := 29) (by decide)
        p st3.mem sL st3 rfl (fun u hu => (hst3_m _ (by omega)).trans ((hfr2 _ (Or.inl (by omega))).trans ((hst1_m _ (by omega)).trans (hsavL_m u hu))))
        (Or.inr (by omega)) (by omega) (by omega) hw16 hst3_r.1 hst3_r.2.1 hst3_r.2.2.1 rfl) rfl ?_
    intro st4 ⟨hoth4, hpos4, hfr4, hsAt4⟩
    refine runs_assign_le (v := pairsA + 1 + (j + 1) * (2 + b))
      (by have heq : pCur + 2 + cL.length + sL.length = pairsA + 1 + (j + 1) * (2 + b) := by omega
          exact heq ▸ Expr.eval_add
            (Expr.eval_reg_of_eq ((hoth4 23 (by decide) (by decide)).trans hst3_r.2.1))
            (Expr.eval_reg_of_eq ((hoth4 27 (by decide) (by decide)).trans hst3_r.2.2.1)) (by omega))
      ?_ (by simp only [Expr.size]; omega)
    refine ⟨by dsimp only; rw [Function.update_of_ne (by decide), hoth4 22 (by decide) (by decide), hst3_r.2.2.2.2.1],
      by simp,
      by dsimp only; rw [Function.update_of_ne (by decide), hoth4 24 (by decide) (by decide), hst3_r.2.2.2.1],
      fun r hr => by dsimp only; rw [Function.update_of_ne (by omega), hoth4 r (by omega) (by omega)]; exact hst3_r.2.2.2.2.2 r hr,
      by rw [hpos4, ← hst3_eq, hpos2, ← hst1_eq],
      fun a ha => by
        rw [hfr4 a (by rcases ha with h | h <;> [left; right] <;> omega),
          hst3_m a (by rcases ha with h | h <;> omega),
          hfr2 a (by rcases ha with h | h <;> [left; right] <;> omega),
          hst1_m a (by rcases ha with h | h <;> omega)], ?_⟩
    have hpart1 : ListAt st4.mem pCur (cL.length :: cL) := fun u hu => by
      cases u with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hfr4 pCur (Or.inl (by omega)), hst3_m pCur (by omega), hfr2 pCur (Or.inl (by omega)), ← hst1_eq]; simp
      | succ u =>
        simp only [List.getElem_cons_succ]
        have hadd : pCur + (u + 1) = pCur + 1 + u := by omega
        rw [hadd, hfr4 _ (Or.inl (by simp at hu; omega)), hst3_m _ (by simp at hu; omega)]
        exact hcAt2 u (by simp at hu; exact hu)
    have hpart2 : ListAt st4.mem (pCur + (cL.length :: cL).length) (sL.length :: sL) := fun u hu => by
      cases u with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, List.length_cons]
        have hadd : pCur + (cL.length + 1) = pCur + 1 + cL.length := by omega
        rw [hadd, hfr4 _ (Or.inl (by omega)), ← hst3_eq]; simp
      | succ u =>
        simp only [List.getElem_cons_succ, List.length_cons]
        have hadd : pCur + (cL.length + 1) + (u + 1) = pCur + 2 + cL.length + u := by omega
        rw [hadd]; exact hsAt4 u (by simp at hu; exact hu)
    simpa [encodePair] using listAt_append_of_parts hpart1 hpart2
  rcases hrun with ⟨o, st4, c, hr, hp, hc⟩
  cases o with
  | returned _ => exact False.elim hp
  | normal => exact ⟨st4, c, hr, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2, hc⟩

theorem sbFinalBuildPairs_triple {w k b nBlocks L h0 pairsA : ℕ}
    {p : Program} {mem : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState} {st₀ : State}
    (hX_card : X.card = k) (hb_pos : 0 < b) (hnb_b : nBlocks * b ≤ k)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hall_inact : ∀ i < nBlocks, bst.active i = false)
    (hsub_B : ∀ i < nBlocks, bst.savedS i ⊆ blockSet (X.sort (· ≤ ·)) b i)
    (hpers : SbPersistAt mem G X b nBlocks L h0 bst)
    (hpairs_ge : (sbPersist h0 k b nBlocks L).hPersist ≤ pairsA)
    (hpairs_w : pairsA + 1 + nBlocks * (2 + b) < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr5 : st₀.regs 5 = nBlocks)
    (hr12 : st₀.regs 12 = pairsA)
    (hr17 : st₀.regs 17 = (sbPersist h0 k b nBlocks L).actA)
    (hr18 : st₀.regs 18 = (sbPersist h0 k b nBlocks L).savA)
    (hr19 : st₀.regs 19 = (sbPersist h0 k b nBlocks L).cmpA)
    (hmem : st₀.mem = mem) :
    let vs := X.sort (· ≤ ·)
    let injPairLists : List (List ℕ × List ℕ) := (List.range nBlocks).map fun i =>
      ((blockSet vs b i \ bst.savedS i).sort (· ≤ ·), (bst.savedS i).sort (· ≤ ·))
    Triple w p (fun st => st = st₀) sbFinalBuildPairsStmt
      (normalPost fun st' =>
        st'.regs 22 = pairsA ∧
        st'.regs 23 = pairsA + 1 + nBlocks * (2 + b) ∧
        (∀ r < 22, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem pairsA (pairsA + 1 + nBlocks * (2 + b)) ∧
        MultiPairsAt st'.mem pairsA injPairLists ∧
        (encodePairs injPairLists).length = 1 + nBlocks * (2 + b))
      (fun _ => 40 * k + 160 * nBlocks + 40) := by
  intro vs injPairLists
  set ps := sbPersist h0 k b nBlocks L
  have hps_id : sbPersist h0 k b nBlocks L = ps := rfl
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hlen_ipl : injPairLists.length = nBlocks := by simp [injPairLists]
  have hpair_sum : ∀ pr ∈ injPairLists, pr.1.length + pr.2.length = b := by
    intro pr hpr
    rcases List.mem_map.mp hpr with ⟨i, hi, rfl⟩
    have hi_lt : i < nBlocks := List.mem_range.mp hi
    rw [Finset.length_sort, Finset.length_sort, Finset.card_sdiff_add_card_eq_card (hsub_B i hi_lt)]
    exact card_blockSet (Finset.sort_nodup X (· ≤ ·)) (hnb_eq ▸ hi_lt)
  have henc_full_len : (encodePairs injPairLists).length = 1 + nBlocks * (2 + b) := by
    simp only [encodePairs, List.length_cons]
    have h := flatMap_encodePair_take_len hpair_sum (le_refl injPairLists.length)
    rw [List.take_length, hlen_ipl] at h; omega
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbFinalBuildPairsStmt, seqStmts]
  refine runs_seq_assign_le (v := pairsA) (Expr.eval_reg_of_eq hr12) ?_
  refine runs_seq_store_le (x := pairsA) (v := nBlocks)
    (Expr.eval_reg_of_eq (by simp))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr5])) ?_
  refine runs_seq_assign_le (v := pairsA + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
  generalize hstA_eq : (State.mk (Function.update st₀.mem pairsA nBlocks)
    (Function.update (Function.update st₀.regs 22 pairsA) 23 (pairsA + 1)) st₀.pos) = stA
  have hstA_r22 : stA.regs 22 = pairsA := by
    rw [← hstA_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
  have hstA_r23 : stA.regs 23 = pairsA + 1 := by rw [← hstA_eq]; simp
  have hstA_lt22 : ∀ r < 22, stA.regs r = st₀.regs r := fun r hr => by
    rw [← hstA_eq]; dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hstA_pos : stA.pos = st₀.pos := by rw [← hstA_eq]
  have hstA_fr : MemFrame mem stA.mem pairsA (pairsA + 1 + nBlocks * (2 + b)) := by
    rw [← hstA_eq]; exact hmem ▸ memFrame_update (le_refl _) (by omega)
  have hstA_m0 : stA.mem pairsA = nBlocks := by rw [← hstA_eq]; simp
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 24 = j ∧ st.regs 22 = pairsA ∧ st.regs 23 = pairsA + 1 + j * (2 + b) ∧
    (∀ r < 22, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem pairsA (pairsA + 1 + nBlocks * (2 + b)) ∧
    st.mem pairsA = nBlocks ∧
    ListAt st.mem (pairsA + 1) ((injPairLists.take j).flatMap encodePair)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 24) (lo := .const 0) (hi := .reg 5)
    (body := seqStmts [
      .assign 25 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 24))),
      .store (.reg 23) (.reg 25),
      .assign 23 (.bin .add (.reg 23) (.const 1)),
      .assign 26 (.bin .add (.reg 19) (.bin .mul (.reg 24) (.reg 4))),
      scCopySliceStmt 26 23 25 28 29,
      .assign 23 (.bin .add (.reg 23) (.reg 25)),
      .assign 27 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 24))),
      .store (.reg 23) (.reg 27),
      .assign 23 (.bin .add (.reg 23) (.const 1)),
      .assign 26 (.bin .add (.reg 18) (.bin .mul (.reg 24) (.reg 4))),
      scCopySliceStmt 26 23 27 28 29,
      .assign 23 (.bin .add (.reg 23) (.reg 27))])
    (P := fun st => st = stA) (Inv := Inv) (36 * b + 140) 0 nBlocks (Nat.zero_le _)
    (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hstA_r22],
        by dsimp only; rw [Function.update_of_ne (by decide), hstA_r23]; omega,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hstA_lt22 r hr,
        hstA_pos, hstA_fr, hstA_m0, fun idx hidx => by simp at hidx⟩)
    (fun _ st _ _ hI => hI.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq (v := nBlocks) ((hI.2.2.2.1 5 (by decide)).trans hr5))
    (fun j _ hjlt => by
      intro st ω ⟨hr24, hr22, hr23, hlt22, hpos, hfr, hm0, hflat⟩
      have hsaved := hpers.inact_saved j hjlt (hall_inact j hjlt)
      dsimp only at hsaved; rw [hX_card, hps_id] at hsaved
      set cL := (blockSet vs b j \ bst.savedS j).sort (· ≤ ·)
      set sL := (bst.savedS j).sort (· ≤ ·)
      set pCur := pairsA + 1 + j * (2 + b)
      have hcLen : cL.length = (blockSet vs b j \ bst.savedS j).card := Finset.length_sort _
      have hsLen : sL.length = (bst.savedS j).card := Finset.length_sort _
      have hcs_sum : cL.length + sL.length = b := by
        rw [hcLen, hsLen, Finset.card_sdiff_add_card_eq_card (hsub_B j hjlt)]
        exact card_blockSet (Finset.sort_nodup X (· ≤ ·)) (hnb_eq ▸ hjlt)
      have hjm : (j + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega)
      have hj2 : (j + 1) * (2 + b) ≤ nBlocks * (2 + b) := Nat.mul_le_mul_right (2 + b) (by omega)
      rw [Nat.succ_mul] at hjm hj2
      have hcmpLen_m : st.mem (ps.cmpLenA + j) = cL.length := by
        rw [hfr _ (Or.inl (by omega)), hsaved.2.1, hcLen]
      have hsavLen_m : st.mem (ps.savLenA + j) = sL.length := by
        rw [hfr _ (Or.inl (by omega)), hsaved.1, hsLen]
      have hcmpL_m : ListAt st.mem (ps.cmpA + j * b) cL := fun u hu => by
        rw [hfr _ (Or.inl (by omega))]; exact hsaved.2.2.2 u hu
      have hsavL_m : ListAt st.mem (ps.savA + j * b) sL := fun u hu => by
        rw [hfr _ (Or.inl (by omega))]; exact hsaved.2.2.1 u hu
      have hflat_len : ((injPairLists.take j).flatMap encodePair).length = j * (2 + b) :=
        flatMap_encodePair_take_len hpair_sum (by omega)
      obtain ⟨st4, c, hr4', hr22', hr23', hr24', hlt22', hpos', hfr4', henc', hc'⟩ :=
        sbFinalBuildPairs_body (ω := ω) hjlt hcs_sum
          ⟨hps_ord.2.1, hps_ord.2.2.1, hps_ord.2.2.2.1, hps_ord.2.2.2.2.1, by omega⟩
          hpairs_w hw16 hcmpLen_m hsavLen_m hcmpL_m hsavL_m
          ⟨(hlt22 4 (by decide)).trans hr4, (hlt22 5 (by decide)).trans hr5,
           (hlt22 17 (by decide)).trans hr17, (hlt22 18 (by decide)).trans hr18,
           (hlt22 19 (by decide)).trans hr19, hr22, hr23, hr24⟩
      have hj2' : (j + 1) * (2 + b) ≤ nBlocks * (2 + b) := Nat.mul_le_mul_right (2 + b) (by omega)
      refine ⟨.normal, st4, c, hr4', ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hr22'],
        by dsimp only; rw [Function.update_of_ne (by decide), hr23'],
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact (hlt22' r hr).trans (hlt22 r hr),
        hpos'.trans hpos,
        fun a ha => (hfr4' a (by rcases ha with h | h <;> [left; right] <;> omega)).trans (hfr a ha),
        (hfr4' pairsA (Or.inl (by omega))).trans hm0, ?_⟩, hr24'⟩, hc'⟩
      rw [List.take_succ_eq_append_getElem (by omega), List.flatMap_append, List.flatMap_singleton]
      have hget_j : injPairLists[j]'(by omega) = (cL, sL) := by simp [injPairLists, cL, sL]
      rw [hget_j]
      refine listAt_append_of_parts (fun u hu => (hfr4' _ (Or.inl (by omega))).trans (hflat u hu)) ?_
      rw [hflat_len]; exact henc')
  refine runs_triple_le hloop rfl ?_ (by
    have h1 : (nBlocks - 0) * (36 * b + 140 + 1 + 8) = 36 * (nBlocks * b) + 149 * nBlocks := by
      simp only [Nat.sub_zero]; ring
    simp only [Expr.size]; omega)
  rintro (_ | _) st' h'
  · rcases h' with ⟨_, hr22', hr23', hlt22', hpos', hfr', hm0', hflat'⟩
    rw [← hlen_ipl, List.take_length] at hflat'
    have hmp : MultiPairsAt st'.mem pairsA injPairLists := fun u hu => by
      cases u with
      | zero => simp [encodePairs, hm0', hlen_ipl]
      | succ u =>
        simp only [encodePairs, List.getElem_cons_succ]
        have hadd : pairsA + (u + 1) = pairsA + 1 + u := by omega
        simp only [encodePairs, List.length_cons] at hu
        rw [hadd]; exact hflat' u (Nat.lt_of_succ_lt_succ hu)
    exact ⟨hr22', hr23', hlt22', hpos', hfr', hmp, henc_full_len⟩
  · exact h'


end MinCostFlow.ExpanderDecomp
