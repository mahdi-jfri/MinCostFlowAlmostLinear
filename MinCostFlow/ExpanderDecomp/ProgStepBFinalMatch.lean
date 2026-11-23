module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBRound

import Mathlib.Tactic.Linarith

/-!
# Step B Final Phase Matched Handler (`ProgStepBFinalMatch`)

Implements and verifies `sbFinalMatchedStmt`, which after the final complement-injection router
call returns `.matched matchings emb`, marks `matchings.flatten` in `locAddr`, completes fake
edges for all `nBlocks` blocks onto `fAddr`, restores `locAddr` to all zeros, writes `[1, totalFakeLen]`
to `outAddr`, and advances `r12 := hAfterRt + 2 * b`.

Main results:
- `sbFinalMatchedStmt`, `sbFinalMatchedStmt_noRand`
- `sbFinalMatched_triple`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Matched-branch final handler: marks `matchings.flatten` in `locA`, completes fake edges for all
`nBlocks` blocks into `fA` (updating `r14`), unmarks `locA` back to zeros, writes `[1, r14]` to
`outA`, and advances `r12 := r12 + 2 * b`. -/
def sbFinalMatchedStmt : Stmt :=
  seqStmts [
    .assign 25 (.load (.bin .add (.reg 24) (.const 1))),
    .assign 26 (.bin .add (.reg 24) (.const 2)),
    scSetMatchedStmt 25 26 8 27 28 29 1,
    .assign 30 (.reg 12),
    .assign 31 (.bin .add (.reg 12) (.reg 4)),
    forRange 32 (.const 0) (.reg 5) (
      seqStmts [
        .assign 33 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 32))),
        .assign 34 (.bin .add (.reg 19) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 34 33 8 30 35 39 40,
        .assign 36 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 32))),
        .assign 37 (.bin .add (.reg 18) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 37 36 8 31 38 39 40,
        scZipAppendStmt 30 35 31 38 9 14 39 40 41 42
      ]),
    scSetMatchedStmt 25 26 8 27 28 29 0,
    .store (.reg 10) (.const 1),
    .store (.bin .add (.reg 10) (.const 1)) (.reg 14),
    .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 4)))
  ]


theorem sbFinalMatchedStmt_noRand : sbFinalMatchedStmt.NoRand := by
  simp [sbFinalMatchedStmt, scSetMatchedStmt, scCollectUnmatchedStmt, scZipAppendStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 3. Matched-Branch Loop Body (`sbFinalMatched_body`) -/

private lemma sbFinalMatched_body {w n b k nBlocks locA fA hAfterRt actA savLenA cmpLenA savA cmpA curF j : ℕ}
    {p : Program} {S : Finset ℕ} {cL sL : List ℕ} {curFEs : List (ℕ × ℕ)} {st : State} {ω : ℕ → Bool}
    (hjlt : j < nBlocks) (hcs_sum : cL.length + sL.length = b)
    (hc_lt : ∀ u ∈ cL, u < n) (hs_lt : ∀ u ∈ sL, u < n)
    (hord : locA + n ≤ actA ∧ fA + 2 * k ≤ actA ∧ actA + nBlocks = savLenA ∧
      savLenA + nBlocks = cmpLenA ∧ cmpLenA + nBlocks = savA ∧
      savA + nBlocks * b = cmpA ∧ cmpA + nBlocks * b ≤ hAfterRt)
    (hhA_w : hAfterRt + 2 * b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hcmpLen_m : st.mem (cmpLenA + j) = cL.length) (hsavLen_m : st.mem (savLenA + j) = sL.length)
    (hcmpL_m : ListAt st.mem (cmpA + j * b) cL) (hsavL_m : ListAt st.mem (savA + j * b) sL)
    (hloc_st : ∀ u < n, st.mem (locA + u) = if u ∈ S then 1 else 0)
    (hcurLen : curFEs.length = curF) (hE_st : EdgesAt st.mem fA curFEs)
    (hcap : curF + min (cL.filter fun u => decide (u ∉ S)).length (sL.filter fun u => decide (u ∉ S)).length ≤ k)
    (hregs : st.regs 4 = b ∧ st.regs 5 = nBlocks ∧ st.regs 8 = locA ∧ st.regs 9 = fA ∧
      st.regs 14 = curF ∧ st.regs 17 = actA ∧ st.regs 18 = savA ∧ st.regs 19 = cmpA ∧
      st.regs 30 = hAfterRt ∧ st.regs 31 = hAfterRt + b ∧ st.regs 32 = j) :
    let unmA := cL.filter fun u => decide (u ∉ S)
    let unmB := sL.filter fun u => decide (u ∉ S)
    ∃ stZ c,
      Runs w p ω (seqStmts [
        .assign 33 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 32))),
        .assign 34 (.bin .add (.reg 19) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 34 33 8 30 35 39 40,
        .assign 36 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 32))),
        .assign 37 (.bin .add (.reg 18) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 37 36 8 31 38 39 40,
        scZipAppendStmt 30 35 31 38 9 14 39 40 41 42]) st .normal stZ c ∧
      stZ.regs 14 = curF + min unmA.length unmB.length ∧
      stZ.regs 32 = j ∧
      (∀ r < 32, r ≠ 14 → stZ.regs r = st.regs r) ∧
      (∀ a, (a < fA ∨ fA + 2 * k ≤ a) → (a < hAfterRt ∨ hAfterRt + 2 * b ≤ a) → stZ.mem a = st.mem a) ∧
      EdgesAt stZ.mem fA (curFEs ++ unmA.zip unmB) ∧
      c ≤ 120 * b + 150 := by
  intro unmA unmB
  rcases hord with ⟨hloc_a, hf_a, ho1, ho2, ho3, ho4, ho5⟩
  rcases hregs with ⟨hr4, hr5, hr8, hr9, hr14, hr17, hr18, hr19, hr30, hr31, hr32⟩
  have hjm : j * b + b ≤ nBlocks * b := by
    have := Nat.mul_le_mul_right b (show j + 1 ≤ nBlocks by omega); rwa [Nat.succ_mul] at this
  have hunmA_le : unmA.length ≤ cL.length := List.length_filter_le _ _
  have hunmB_le : unmB.length ≤ sL.length := List.length_filter_le _ _
  have hrun : ∃ o stZ c,
      Runs w p ω (seqStmts [
        .assign 33 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 32))),
        .assign 34 (.bin .add (.reg 19) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 34 33 8 30 35 39 40,
        .assign 36 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 32))),
        .assign 37 (.bin .add (.reg 18) (.bin .mul (.reg 32) (.reg 4))),
        scCollectUnmatchedStmt 37 36 8 31 38 39 40,
        scZipAppendStmt 30 35 31 38 9 14 39 40 41 42]) st o stZ c ∧
      (normalPost fun stZ =>
        stZ.regs 14 = curF + min unmA.length unmB.length ∧ stZ.regs 32 = j ∧
        (∀ r < 32, r ≠ 14 → stZ.regs r = st.regs r) ∧
        (∀ a, (a < fA ∨ fA + 2 * k ≤ a) → (a < hAfterRt ∨ hAfterRt + 2 * b ≤ a) → stZ.mem a = st.mem a) ∧
        EdgesAt stZ.mem fA (curFEs ++ unmA.zip unmB)) o stZ ∧
      c ≤ 120 * b + 150 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := cL.length)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr17)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr5) (by omega)) (by omega))
          (Expr.eval_reg_of_eq hr32) (by omega))
        (by have hcmp : actA + 2 * nBlocks + j = cmpLenA + j := by omega
            rw [hcmp]; exact hcmpLen_m)) ?_
    refine runs_seq_assign_le (v := cmpA + j * b)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := cmpA) (by dsimp only; rw [Function.update_of_ne (by decide), hr19]))
        (Expr.eval_mul
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hr32]))
          (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), hr4]))
          (by omega)) (by omega)) ?_
    generalize hstA_eq : (State.mk st.mem (Function.update (Function.update st.regs 33 cL.length) 34 (cmpA + j * b)) st.pos) = stA
    refine runs_seq_triple_le
      (scCollectUnmatched_triple (w := w) (n := n) (len := cL.length)
        (sa := cmpA + j * b) (la := locA) (da := hAfterRt)
        (rSrc := 34) (rLen := 33) (rLoc := 8) (rDst := 30) (rCnt := 35) (rI := 39) (rU := 40) (by decide)
        p st.mem cL S stA rfl hcmpL_m hc_lt hloc_st
        (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega) hw16
        (by rw [← hstA_eq]; simp)
        (by rw [← hstA_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])
        (by rw [← hstA_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
        (by rw [← hstA_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30])
        (by rw [← hstA_eq])) rfl ?_
    intro stB ⟨hr35B, hothB, _, hfrB, hunmA_B⟩
    have hstB_r : ∀ r < 33, stB.regs r = st.regs r := fun r hr => by
      rw [hothB r (by omega) (by omega) (by omega), ← hstA_eq]
      dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    refine runs_seq_assign_le (v := sL.length)
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hstB_r 17 (by decide)).trans hr17))
          (Expr.eval_reg_of_eq ((hstB_r 5 (by decide)).trans hr5)) (by omega))
          (Expr.eval_reg_of_eq ((hstB_r 32 (by decide)).trans hr32)) (by omega))
        (by rw [ho1, hfrB _ (Or.inl (by omega))]; exact hsavLen_m)) ?_
    refine runs_seq_assign_le (v := savA + j * b)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := savA) (by dsimp only; rw [Function.update_of_ne (by decide), hstB_r 18 (by decide), hr18]))
        (Expr.eval_mul
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hstB_r 32 (by decide), hr32]))
          (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), hstB_r 4 (by decide), hr4]))
          (by omega)) (by omega)) ?_
    generalize hstC_eq : (State.mk stB.mem (Function.update (Function.update stB.regs 36 sL.length) 37 (savA + j * b)) stB.pos) = stC
    refine runs_seq_triple_le
      (scCollectUnmatched_triple (w := w) (n := n) (len := sL.length)
        (sa := savA + j * b) (la := locA) (da := hAfterRt + b)
        (rSrc := 37) (rLen := 36) (rLoc := 8) (rDst := 31) (rCnt := 38) (rI := 39) (rU := 40) (by decide)
        p stB.mem sL S stC rfl
        (fun u hu => (hfrB _ (Or.inl (by omega))).trans (hsavL_m u hu))
        hs_lt (fun u hu => (hfrB _ (Or.inl (by omega))).trans (hloc_st u hu))
        (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega) hw16
        (by rw [← hstC_eq]; simp)
        (by rw [← hstC_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])
        (by rw [← hstC_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstB_r 8 (by decide), hr8])
        (by rw [← hstC_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstB_r 31 (by decide), hr31])
        (by rw [← hstC_eq])) rfl ?_
    intro stD ⟨hr38D, hothD, _, hfrD, hunmB_D⟩
    have hstD_r : ∀ r < 33, stD.regs r = st.regs r := fun r hr => by
      rw [hothD r (by omega) (by omega) (by omega), ← hstC_eq]
      dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hstB_r r hr
    have hstD_35 : stD.regs 35 = unmA.length := by
      rw [hothD 35 (by decide) (by decide) (by decide), ← hstC_eq]
      dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr35B]
    refine runs_triple_le
      (scZipAppend_triple (w := w) (cntA := unmA.length) (cntB := unmB.length)
        (prevM := curF) (cap := k) (outA := fA) (ua := hAfterRt) (ub := hAfterRt + b)
        (rUnmA := 30) (rCntA := 35) (rUnmB := 31) (rCntB := 38) (rOutEdges := 9) (rOutM := 14)
        (rLim := 39) (rI := 40) (rU := 41) (rV := 42) (by decide)
        p stD.mem unmA unmB curFEs stD rfl rfl hcurLen
        (fun u hu => (hfrD _ (Or.inl (by omega))).trans (hunmA_B u hu)) hunmB_D
        (fun idx hidx => by
          rw [hfrD _ (Or.inl (by omega)), hfrD _ (Or.inl (by omega)),
            hfrB _ (Or.inl (by omega)), hfrB _ (Or.inl (by omega))]
          exact hE_st idx hidx)
        hcap (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
        ((hstD_r 30 (by decide)).trans hr30) hstD_35
        ((hstD_r 31 (by decide)).trans hr31) hr38D
        ((hstD_r 9 (by decide)).trans hr9) ((hstD_r 14 (by decide)).trans hr14) rfl) rfl ?_ (by
          have hmin : min unmA.length unmB.length ≤ b := le_trans (Nat.min_le_left _ _) (by omega)
          simp only [Expr.size]; omega)
    rintro (_ | _) stZ hZ
    · rcases hZ with ⟨hr14Z, hothZ, _, hfrZ, hEZ⟩
      exact ⟨hr14Z,
        (hothZ 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((hstD_r 32 (by decide)).trans hr32),
        fun r hr h14 => (hothZ r h14 (by omega) (by omega) (by omega) (by omega)).trans (hstD_r r (by omega)),
        fun a ha1 ha2 => by
          rw [hfrZ a ha1, hfrD a (by rcases ha2 with h | h <;> [left; right] <;> omega),
            hfrB a (by rcases ha2 with h | h <;> [left; right] <;> omega)],
        hEZ⟩
    · exact hZ
  rcases hrun with ⟨o, stZ, c, hr, hp, hc⟩
  cases o with
  | returned _ => exact False.elim hp
  | normal => exact ⟨stZ, c, hr, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, hc⟩

/-! ## 4. Matched-Branch Handler Triple (`sbFinalMatched_triple`) -/

theorem sbFinalMatched_triple {w k b nBlocks L h0 locA fA outA rtOutA hAfterRt prevF : ℕ}
    {p : Program} {memR : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {matchings : List (List (ℕ × ℕ))} {prevFEs : List (ℕ × ℕ)} {stR : State}
    (hX_card : X.card = k) (hX_sub : X ⊆ Finset.range G.n) (hb_pos : 0 < b) (hnb_b : nBlocks * b ≤ k)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hall_inact : ∀ i < nBlocks, bst.active i = false)
    (hsub_B : ∀ i < nBlocks, bst.savedS i ⊆ blockSet (X.sort (· ≤ ·)) b i)
    (hvtp : ValidTerminalPairs X ((List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i)))
    (hmlen : matchings.length = nBlocks)
    (hpm : ∀ i, i < nBlocks →
      IsPartialMatching (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i) (bst.savedS i) (matchings.getD i []))
    (hflat_le_k : matchings.flatten.length ≤ k) (hflat_le_n : matchings.flatten.length ≤ G.n)
    (hpers : SbPersistAt memR G X b nBlocks L h0 bst)
    (hFlen : prevFEs.length = prevF) (hF_at : EdgesAt memR fA prevFEs)
    (hF_cap : prevF + (completeBatchFake
      ((List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i))
      matchings).length ≤ k)
    (hmLenR : memR (rtOutA + 1) = matchings.flatten.length)
    (hmAtR : EdgesAt memR (rtOutA + 2) matchings.flatten)
    (hlocR : ∀ u < G.n, memR (locA + u) = 0)
    (hbounds : locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n fA (2 * k) ∧ DisjointRange locA G.n outA (2 + k) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧
      (sbPersist h0 k b nBlocks L).hPersist ≤ rtOutA ∧
      rtOutA + 2 + 2 * G.n ≤ hAfterRt ∧ hAfterRt + 2 * b < 2 ^ w ∧ 16 < 2 ^ w)
    (hregs : stR.regs 4 = b ∧ stR.regs 5 = nBlocks ∧ stR.regs 8 = locA ∧ stR.regs 9 = fA ∧
      stR.regs 10 = outA ∧ stR.regs 12 = hAfterRt ∧ stR.regs 14 = prevF ∧
      stR.regs 17 = (sbPersist h0 k b nBlocks L).actA ∧
      stR.regs 18 = (sbPersist h0 k b nBlocks L).savA ∧
      stR.regs 19 = (sbPersist h0 k b nBlocks L).cmpA ∧
      stR.regs 24 = rtOutA)
    (hmemR : stR.mem = memR) :
    let injPairs := (List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i)
    Triple w p (fun st => st = stR) sbFinalMatchedStmt
      (normalPost fun st' =>
        st'.regs 12 = hAfterRt + 2 * b ∧
        st'.regs 14 = prevF + (completeBatchFake injPairs matchings).length ∧
        st'.mem outA = 1 ∧
        st'.mem (outA + 1) = prevF + (completeBatchFake injPairs matchings).length ∧
        EdgesAt st'.mem fA (prevFEs ++ completeBatchFake injPairs matchings) ∧
        (∀ u < G.n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + G.n ≤ a) → (a < fA ∨ fA + 2 * k ≤ a) →
          (a < outA ∨ outA + 2 ≤ a) → (a < hAfterRt ∨ hAfterRt + 2 * b ≤ a) →
          st'.mem a = memR a))
      (fun _ => 260 * k + 260 * nBlocks + 220) := by
  intro injPairs
  set ps := sbPersist h0 k b nBlocks L
  set vs := X.sort (· ≤ ·)
  have hps_id : sbPersist h0 k b nBlocks L = ps := rfl
  rcases hbounds with ⟨hloc_h, hf_h, hout_h, hd_lf, hd_lo, hd_of, hp_rt, hrt_hA, hhA_w, hw16⟩
  rcases hregs with ⟨hr4, hr5, hr8, hr9, hr10, hr12, hr14, hr17, hr18, hr19, hr24⟩
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hflat_lt : ∀ e ∈ matchings.flatten, e.1 < G.n ∧ e.2 < G.n := by
    intro e he
    rcases List.mem_flatten.mp he with ⟨M, hM, heM⟩
    rcases List.mem_iff_getElem.mp hM with ⟨idx, hidx, rfl⟩
    have hi : idx < nBlocks := hmlen ▸ hidx
    have hpm_i := hpm idx hi
    rw [List.getD_eq_getElem _ _ hidx] at hpm_i
    have h12 := hpm_i.1 e heM
    have hBsub : blockSet vs b idx ⊆ X := by
      have h := blockSet_subset_toFinset vs b idx; simpa [vs] using h
    exact ⟨Finset.mem_range.mp (hX_sub (hBsub (Finset.mem_sdiff.mp h12.1).1)),
      Finset.mem_range.mp (hX_sub (hBsub (hsub_B idx hi h12.2)))⟩
  have hinj_len : injPairs.length = nBlocks := by simp [injPairs]
  have hpm_p : ∀ i (hi : i < injPairs.length),
      IsPartialMatching (injPairs[i]'hi).1 (injPairs[i]'hi).2 (matchings.getD i []) := fun i hi => by
    have hget : injPairs[i]'hi = (blockSet vs b i \ bst.savedS i, bst.savedS i) := by simp [injPairs, vs]
    rw [hget]; exact hpm i (hinj_len ▸ hi)
  have hbatch_take_le : ∀ j ≤ nBlocks,
      (completeBatchFake (injPairs.take j) (matchings.take j)).length ≤
        (completeBatchFake injPairs matchings).length := fun j hj => by
    have hsub : List.Sublist (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) (injPairs.take j) (matchings.take j))
        (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) injPairs matchings) := by
      rw [← List.take_zipWith]; exact List.take_sublist _ _
    exact hsub.flatten.length_le
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbFinalMatchedStmt, seqStmts]
  -- r25 := mem[rtOutA + 1]; r26 := rtOutA + 2
  refine runs_seq_assign_le (v := matchings.flatten.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr24) (Expr.eval_const (by omega)) (by omega))
      (hmemR ▸ hmLenR)) ?_
  refine runs_seq_assign_le (v := rtOutA + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr24]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  -- Mark `matchings.flatten` in `locA`
  generalize hst01 : (State.mk stR.mem (Function.update (Function.update stR.regs 25 matchings.flatten.length) 26 (rtOutA + 2)) stR.pos) = st01
  refine runs_seq_triple_le
    (scSetMatched_triple (w := w) (n := G.n) (mE := matchings.flatten.length)
      (ea := rtOutA + 2) (la := locA) (rM := 25) (rEdges := 26) (rLoc := 8)
      (rI := 27) (rU := 28) (rV := 29) (val := 1) (by decide)
      p memR matchings.flatten st01 rfl hmAtR hflat_lt (Or.inl (by omega))
      (by omega) (by omega) (by omega) hw16
      (by rw [← hst01]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])
      (by rw [← hst01]; simp)
      (by rw [← hst01]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by rw [← hst01]; exact hmemR)) rfl ?_
  intro st1 ⟨hoth1, _, hfr1, hloc1⟩
  have hloc1' : ∀ u < G.n, st1.mem (locA + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 :=
    fun u hu => by rw [hloc1 u hu, hlocR u hu]
  have hst1_lt25 : ∀ r < 25, st1.regs r = stR.regs r := fun r hr => by
    rw [hoth1 r (by omega) (by omega) (by omega), ← hst01]
    dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hst1_25 : st1.regs 25 = matchings.flatten.length := by
    rw [hoth1 25 (by decide) (by decide) (by decide), ← hst01]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
  have hst1_26 : st1.regs 26 = rtOutA + 2 := by
    rw [hoth1 26 (by decide) (by decide) (by decide), ← hst01]; simp
  -- r30 := hAfterRt; r31 := hAfterRt + b
  refine runs_seq_assign_le (v := hAfterRt) (Expr.eval_reg_of_eq ((hst1_lt25 12 (by decide)).trans hr12)) ?_
  refine runs_seq_assign_le (v := hAfterRt + b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst1_lt25 12 (by decide), hr12]))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst1_lt25 4 (by decide), hr4])) (by omega)) ?_
  generalize hst2_eq : (State.mk st1.mem (Function.update (Function.update st1.regs 30 hAfterRt) 31 (hAfterRt + b)) st1.pos) = st2
  have hst2_m : st2.mem = st1.mem := by rw [← hst2_eq]
  have hst2_lt30 : ∀ r < 30, st2.regs r = st1.regs r := fun r hr => by
    rw [← hst2_eq]; dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hst2_30 : st2.regs 30 = hAfterRt := by
    rw [← hst2_eq]; dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
  have hst2_31 : st2.regs 31 = hAfterRt + b := by rw [← hst2_eq]; simp
  -- Loop over `i = 0 .. nBlocks - 1` collecting unmatched vertices and zipping fake edges into `fA`
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 32 = j ∧
    st.regs 14 = prevF + (completeBatchFake (injPairs.take j) (matchings.take j)).length ∧
    (∀ r < 32, r ≠ 14 → st.regs r = st2.regs r) ∧
    (∀ a, (a < fA ∨ fA + 2 * k ≤ a) → (a < hAfterRt ∨ hAfterRt + 2 * b ≤ a) → st.mem a = st1.mem a) ∧
    EdgesAt st.mem fA (prevFEs ++ completeBatchFake (injPairs.take j) (matchings.take j))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 32) (lo := .const 0) (hi := .reg 5)
    (body := seqStmts [
      .assign 33 (.load (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 5))) (.reg 32))),
      .assign 34 (.bin .add (.reg 19) (.bin .mul (.reg 32) (.reg 4))),
      scCollectUnmatchedStmt 34 33 8 30 35 39 40,
      .assign 36 (.load (.bin .add (.bin .add (.reg 17) (.reg 5)) (.reg 32))),
      .assign 37 (.bin .add (.reg 18) (.bin .mul (.reg 32) (.reg 4))),
      scCollectUnmatchedStmt 37 36 8 31 38 39 40,
      scZipAppendStmt 30 35 31 38 9 14 39 40 41 42])
    (P := fun st => st = st2) (Inv := Inv) (120 * b + 150) 0 nBlocks (Nat.zero_le _)
    (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hst2_lt30 14 (by decide), hst1_lt25 14 (by decide), hr14]; simp [completeBatchFake],
        fun r hr _ => by dsimp only; rw [Function.update_of_ne (by omega)],
        fun a _ _ => congrFun hst2_m a,
        by simp only [List.take_zero, completeBatchFake, List.zipWith_nil_left, List.flatten_nil, List.append_nil]
           intro idx hidx
           have h1 : fA + 2 * idx < locA ∨ locA + G.n ≤ fA + 2 * idx := by rcases hd_lf with h | h <;> [right; left] <;> omega
           have h2 : fA + 2 * idx + 1 < locA ∨ locA + G.n ≤ fA + 2 * idx + 1 := by rcases hd_lf with h | h <;> [right; left] <;> omega
           rw [hst2_m, hfr1 _ h1, hfr1 _ h2]; exact hF_at idx hidx⟩)
    (fun _ st _ _ hI => hI.1)
    (fun _ st _ _ hI => Expr.eval_reg_of_eq (v := nBlocks)
      ((hI.2.2.1 5 (by decide) (by decide)).trans ((hst2_lt30 5 (by decide)).trans ((hst1_lt25 5 (by decide)).trans hr5))))
    (fun j _ hjlt => by
      intro st ω ⟨hr32, hr14j, hlt32, hfrj, hEj⟩
      have hsaved := hpers.inact_saved j hjlt (hall_inact j hjlt)
      dsimp only at hsaved; rw [hX_card, hps_id] at hsaved
      set cL := (blockSet vs b j \ bst.savedS j).sort (· ≤ ·)
      set sL := (bst.savedS j).sort (· ≤ ·)
      have hcLen : cL.length = (blockSet vs b j \ bst.savedS j).card := Finset.length_sort _
      have hsLen : sL.length = (bst.savedS j).card := Finset.length_sort _
      have hcs_sum : cL.length + sL.length = b := by
        rw [hcLen, hsLen, Finset.card_sdiff_add_card_eq_card (hsub_B j hjlt)]
        exact card_blockSet (Finset.sort_nodup X (· ≤ ·)) (hnb_eq ▸ hjlt)
      have hjm : (j + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega)
      rw [Nat.succ_mul] at hjm
      have hBsub : blockSet vs b j ⊆ X := by
        have h := blockSet_subset_toFinset vs b j; simpa [vs] using h
      have hc_lt_n : ∀ u ∈ cL, u < G.n := fun u hu => by
        have hm : u ∈ blockSet vs b j \ bst.savedS j := (Finset.mem_sort _).mp hu
        exact Finset.mem_range.mp (hX_sub (hBsub (Finset.mem_sdiff.mp hm).1))
      have hs_lt_n : ∀ u ∈ sL, u < G.n := fun u hu => by
        have hm : u ∈ bst.savedS j := (Finset.mem_sort _).mp hu
        exact Finset.mem_range.mp (hX_sub (hBsub (hsub_B j hjlt hm)))
      have hst_pers : ∀ a, h0 ≤ a → a < ps.hPersist → st.mem a = memR a := fun a h1 h2 => by
        rw [hfrj a (Or.inr (by omega)) (Or.inl (by omega)), hfr1 a (Or.inr (by omega))]
      have hloc_st : ∀ u < G.n, st.mem (locA + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 := fun u hu => by
        rw [hfrj _ (by rcases hd_lf with h | h <;> [left; right] <;> omega) (Or.inl (by omega))]; exact hloc1' u hu
      have hreg_eq : ∀ r < 25, r ≠ 14 → st.regs r = stR.regs r := fun r hr h14 =>
        (hlt32 r (by omega) h14).trans ((hst2_lt30 r (by omega)).trans (hst1_lt25 r hr))
      set unmA := cL.filter fun u => decide (u ∉ matchedVerts matchings.flatten)
      set unmB := sL.filter fun u => decide (u ∉ matchedVerts matchings.flatten)
      have hcmf_eq : completeMatchingFake (injPairs[j]'(by rw [hinj_len]; omega)).1 (injPairs[j]'(by rw [hinj_len]; omega)).2
          (matchings[j]'(by omega)) = unmA.zip unmB := by
        have hget : injPairs[j]'(by rw [hinj_len]; omega) = (blockSet vs b j \ bst.savedS j, bst.savedS j) := by simp [injPairs, vs]
        exact completeMatchingFake_eq_of_flat hvtp (by rw [hinj_len]; omega) hpm_p (by rw [hinj_len]; omega)
          (pairwise_lt_sort _) (pairwise_lt_sort _)
          (by rw [hget]; ext u; simp [cL]) (by rw [hget]; ext u; simp [sL])
      have htake_succ : completeBatchFake (injPairs.take (j + 1)) (matchings.take (j + 1)) =
          completeBatchFake (injPairs.take j) (matchings.take j) ++ unmA.zip unmB := by
        unfold completeBatchFake
        rw [List.take_succ_eq_append_getElem (by rw [hinj_len]; omega),
          List.take_succ_eq_append_getElem (by omega),
          List.zipWith_append (by simp [hinj_len, hmlen]), List.flatten_append,
          List.zipWith_cons_cons, List.zipWith_nil_left, List.flatten_singleton, hcmf_eq]
      have hF_cap' : prevF + (completeBatchFake injPairs matchings).length ≤ k := hF_cap
      have hcap_j : prevF + (completeBatchFake (injPairs.take j) (matchings.take j)).length +
          min unmA.length unmB.length ≤ k := by
        have h1 := hbatch_take_le (j + 1) (by omega)
        rw [htake_succ, List.length_append, List.length_zip] at h1; omega
      obtain ⟨stZ, cZ, hrZ, hr14Z, hr32Z, hlt32Z, hfrZ, hEZ, hcZ⟩ :=
        sbFinalMatched_body (ω := ω) hjlt hcs_sum hc_lt_n hs_lt_n
          ⟨by omega, by omega, hps_ord.2.1, hps_ord.2.2.1, hps_ord.2.2.2.1, hps_ord.2.2.2.2.1, by omega⟩
          hhA_w hw16
          (by rw [hst_pers _ (by omega) (by omega), hsaved.2.1, hcLen])
          (by rw [hst_pers _ (by omega) (by omega), hsaved.1, hsLen])
          (fun u hu => (hst_pers _ (by omega) (by omega)).trans (hsaved.2.2.2 u hu))
          (fun u hu => (hst_pers _ (by omega) (by omega)).trans (hsaved.2.2.1 u hu))
          hloc_st (by rw [List.length_append, hFlen]) hEj hcap_j
          ⟨(hreg_eq 4 (by decide) (by decide)).trans hr4, (hreg_eq 5 (by decide) (by decide)).trans hr5,
           (hreg_eq 8 (by decide) (by decide)).trans hr8, (hreg_eq 9 (by decide) (by decide)).trans hr9,
           hr14j, (hreg_eq 17 (by decide) (by decide)).trans hr17,
           (hreg_eq 18 (by decide) (by decide)).trans hr18, (hreg_eq 19 (by decide) (by decide)).trans hr19,
           (hlt32 30 (by decide) (by decide)).trans hst2_30,
           (hlt32 31 (by decide) (by decide)).trans hst2_31, hr32⟩
      refine ⟨.normal, stZ, cZ, hrZ, ⟨⟨by simp,
        by dsimp only at hr14Z ⊢; rw [Function.update_of_ne (by decide), hr14Z, htake_succ, List.length_append, List.length_zip]; exact Nat.add_assoc _ _ _,
        fun r hr h14 => by dsimp only; rw [Function.update_of_ne (by omega)]; exact (hlt32Z r hr h14).trans (hlt32 r hr h14),
        fun a ha1 ha2 => (hfrZ a ha1 ha2).trans (hfrj a ha1 ha2),
        by rw [htake_succ, ← List.append_assoc]; exact hEZ⟩, hr32Z⟩, hcZ⟩)
  refine runs_seq_triple_le hloop rfl ?_
  intro st3 ⟨_, hr14_3, hlt32_3, hfr3, hE3⟩
  rw [← hinj_len, List.take_length, hinj_len, ← hmlen, List.take_length] at hr14_3 hE3
  -- Unmark `locA` back to all zeros
  have hst3_lt27 : ∀ r < 27, r ≠ 14 → st3.regs r = st1.regs r := fun r hr h14 =>
    (hlt32_3 r (by omega) h14).trans (hst2_lt30 r (by omega))
  refine runs_seq_triple_le
    (scSetMatched_triple (w := w) (n := G.n) (mE := matchings.flatten.length)
      (ea := rtOutA + 2) (la := locA) (rM := 25) (rEdges := 26) (rLoc := 8)
      (rI := 27) (rU := 28) (rV := 29) (val := 0) (by decide)
      p st3.mem matchings.flatten st3 rfl
      (fun idx hidx => by
        rw [hfr3 _ (Or.inr (by omega)) (Or.inl (by omega)), hfr3 _ (Or.inr (by omega)) (Or.inl (by omega)),
          hfr1 _ (Or.inr (by omega)), hfr1 _ (Or.inr (by omega))]
        exact hmAtR idx hidx)
      hflat_lt (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      ((hst3_lt27 25 (by decide) (by decide)).trans hst1_25)
      ((hst3_lt27 26 (by decide) (by decide)).trans hst1_26)
      ((hst3_lt27 8 (by decide) (by decide)).trans ((hst1_lt25 8 (by decide)).trans hr8)) rfl) rfl ?_
  intro st4 ⟨hoth4, _, hfr4, hloc4⟩
  have hloc4' : ∀ u < G.n, st4.mem (locA + u) = 0 := fun u hu => by
    rw [hloc4 u hu]; split_ifs with h
    · rfl
    · rw [hfr3 _ (by rcases hd_lf with h1 | h1 <;> [left; right] <;> omega) (Or.inl (by omega)), hloc1' u hu]
      simp [h]
  -- Store `mem[outA] := 1`, `mem[outA + 1] := r14`, `r12 := hAfterRt + 2 * b`
  refine runs_seq_store_le (x := outA) (v := 1)
    (Expr.eval_reg_of_eq ((hoth4 10 (by decide) (by decide) (by decide)).trans ((hst3_lt27 10 (by decide) (by decide)).trans ((hst1_lt25 10 (by decide)).trans hr10))))
    (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := outA + 1) (v := prevF + (completeBatchFake injPairs matchings).length)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hoth4 10 (by decide) (by decide) (by decide)).trans ((hst3_lt27 10 (by decide) (by decide)).trans ((hst1_lt25 10 (by decide)).trans hr10))))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq ((hoth4 14 (by decide) (by decide) (by decide)).trans hr14_3)) ?_
  refine runs_assign_le (v := hAfterRt + 2 * b)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hoth4 12 (by decide) (by decide) (by decide)).trans ((hst3_lt27 12 (by decide) (by decide)).trans ((hst1_lt25 12 (by decide)).trans hr12))))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq ((hoth4 4 (by decide) (by decide) (by decide)).trans ((hst3_lt27 4 (by decide) (by decide)).trans ((hst1_lt25 4 (by decide)).trans hr4))))
        (by omega)) (by omega)) ?_ (by
      have h1 : (nBlocks - 0) * (120 * b + 150 + 1 + 8) = 120 * (nBlocks * b) + 159 * nBlocks := by
        simp only [Nat.sub_zero]; ring
      simp only [Expr.size]; omega)
  refine ⟨by simp,
    by dsimp only; rw [Function.update_of_ne (by decide), hoth4 14 (by decide) (by decide) (by decide), hr14_3],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_self],
    fun idx hidx => by
      have hF_cap' : prevF + (completeBatchFake injPairs matchings).length ≤ k := hF_cap
      have hlt_k : idx < k := by rw [List.length_append, hFlen] at hidx; omega
      have hne1 : fA + 2 * idx ≠ outA + 1 := by rcases hd_of with h | h <;> omega
      have hne2 : fA + 2 * idx ≠ outA := by rcases hd_of with h | h <;> omega
      have hne3 : fA + 2 * idx + 1 ≠ outA + 1 := by rcases hd_of with h | h <;> omega
      have hne4 : fA + 2 * idx + 1 ≠ outA := by rcases hd_of with h | h <;> omega
      have h1 : fA + 2 * idx < locA ∨ locA + G.n ≤ fA + 2 * idx := by rcases hd_lf with h | h <;> [right; left] <;> omega
      have h2 : fA + 2 * idx + 1 < locA ∨ locA + G.n ≤ fA + 2 * idx + 1 := by rcases hd_lf with h | h <;> [right; left] <;> omega
      dsimp only
      rw [Function.update_of_ne hne1, Function.update_of_ne hne2, hfr4 _ h1,
        Function.update_of_ne hne3, Function.update_of_ne hne4, hfr4 _ h2]
      exact hE3 idx hidx,
    fun u hu => by
      have hne1 : locA + u ≠ outA + 1 := by rcases hd_lo with h | h <;> omega
      have hne2 : locA + u ≠ outA := by rcases hd_lo with h | h <;> omega
      dsimp only; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]; exact hloc4' u hu,
    fun a ha1 ha2 ha3 ha4 => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        hfr4 a ha1, hfr3 a ha2 ha4, hfr1 a ha1]⟩


end MinCostFlow.ExpanderDecomp
