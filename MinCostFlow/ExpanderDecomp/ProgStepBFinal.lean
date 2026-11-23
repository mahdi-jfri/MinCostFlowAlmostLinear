module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBFinalPairs
public import MinCostFlow.ExpanderDecomp.ProgStepBFinalMatch

import Mathlib.Tactic.Linarith

/-!
# Step B Final Complement-Injection Phase (`ProgStepBFinal`)

Combines `sbFinalBuildPairsStmt`, the final `bRoute` call, `sbCopyCutZeroStmt`, and
`sbFinalMatchedStmt` into `sbFinalInjStmt bRoute`, proving `sbFinalInj_run` meeting all
postconditions of `stepBContract`.

Main results:
- `sbFinalInjStmt`, `sbFinalInjStmt_noRand`
- `sbFinalInj_run`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Full final complement-injection phase of Step B (`r13 = 0` after `49 * L + 1` rounds). -/
def sbFinalInjStmt (bRoute : ℕ) : Stmt :=
  seqStmts [
    sbFinalBuildPairsStmt,
    .assign 24 (.reg 23),
    .assign 25 (.load (.reg 1)),
    .assign 26 (.bin .add (.bin .add (.reg 24) (.const 2)) (.bin .mul (.const 2) (.reg 25))),
    .assign 27 (.load (.bin .add (.reg 7) (.const 2))),
    .assign 28 (.load (.bin .add (.reg 7) (.const 1))),
    .call 12 bRoute [.reg 1, .reg 11, .reg 22, .reg 27, .reg 28, .const 100, .reg 6, .reg 24, .reg 26],
    .cond (.bin .eq (.load (.reg 24)) (.const 1))
      (seqStmts [sbCopyCutZeroStmt 24 10 27 28 29, .ret (.reg 12)])
      (seqStmts [sbFinalMatchedStmt, .ret (.reg 12)])
  ]

theorem sbFinalInjStmt_noRand (bRoute : ℕ) : (sbFinalInjStmt bRoute).NoRand := by
  simp [sbFinalInjStmt, sbFinalBuildPairsStmt_noRand, sbFinalMatchedStmt_noRand, sbCopyCutZeroStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 4. Full Final Complement-Injection Proof (`sbFinalInj_run`) -/

private lemma runs_ret_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {st : State} {v : ℕ}
    (he : e.eval w st = some v) :
    Runs w p ω (.ret e) st (.returned v) st (e.size + 1) :=
  runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

private lemma runs_seq_ret_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st1 st2 : State} {v c1 c2 : ℕ}
    (h1 : Runs w p ω s st .normal st1 c1) (h2 : Runs w p ω t st1 (.returned v) st2 c2) :
    Runs w p ω (.seq s t) st (.returned v) st2 (c1 + c2 + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩)

private lemma runs_cond_ret_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {v rv c1 : ℕ} (he : e.eval w st = some v) (hv : v ≠ 0)
    (hs : Runs w p ω s st (.returned rv) st' c1) :
    Runs w p ω (.cond e s t) st (.returned rv) st' (e.size + c1 + 1) :=
  runs_cond_iff.mpr ⟨v, c1, he, by simp only [hv, ↓reduceIte]; exact hs, rfl⟩

private lemma runs_cond_ret_f {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {rv c1 : ℕ} (he : e.eval w st = some 0)
    (ht : Runs w p ω t st (.returned rv) st' c1) :
    Runs w p ω (.cond e s t) st (.returned rv) st' (e.size + c1 + 1) :=
  runs_cond_iff.mpr ⟨0, c1, he, by simp only [↓reduceIte]; exact ht, rfl⟩

private lemma sbPersistAt_of_agree {mem1 mem2 : ℕ → ℕ} {G : Graph} {X : Finset ℕ}
    {k b nBlocks L h0 : ℕ} {bst : BlockGameState}
    (hX_card : X.card = k) (hnb_b : nBlocks * b ≤ k)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hsub_B : ∀ i < nBlocks, bst.savedS i ⊆ blockSet (X.sort (· ≤ ·)) b i)
    (hrounds_len : ∀ i < nBlocks, ∀ j < bst.numRounds i, (bst.rounds i j).length = b / 2)
    (hnum_le : ∀ i < nBlocks, bst.numRounds i ≤ 49 * L + 1)
    (hpers : SbPersistAt mem1 G X b nBlocks L h0 bst)
    (hagree : ∀ a, h0 ≤ a → a < (sbPersist h0 k b nBlocks L).hPersist → mem2 a = mem1 a) :
    SbPersistAt mem2 G X b nBlocks L h0 bst := by
  set ps := sbPersist h0 k b nBlocks L
  have hps_id : sbPersist h0 k b nBlocks L = ps := rfl
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  refine ⟨⟨(hagree h0 (le_refl _) (by omega)).trans hpers.xLen_at.1,
      fun idx hidx =>
        have hidx_k : idx < k := by rw [Finset.length_sort, hX_card] at hidx; exact hidx
        (hagree (h0 + 1 + idx) (by omega) (by omega)).trans (hpers.xLen_at.2 idx hidx)⟩,
    fun i hi => by
      have h0a := hpers.act_at i hi; rw [hX_card, hps_id] at h0a ⊢
      exact (hagree _ (by omega) (by omega)).trans h0a,
    fun i hi hnf => by
      dsimp only; rw [hX_card, hps_id]
      have h1 := hpers.inact_saved i hi hnf; dsimp only at h1; rw [hX_card, hps_id] at h1
      have hib : (i + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); rw [Nat.succ_mul] at hib
      have hBcard : (blockSet (X.sort (· ≤ ·)) b i).card = b :=
        card_blockSet (Finset.sort_nodup X (· ≤ ·)) (hnb_eq ▸ hi)
      have hSL : ((bst.savedS i).sort (· ≤ ·)).length ≤ b := by
        rw [Finset.length_sort]; exact (Finset.card_le_card (hsub_B i hi)).trans (le_of_eq hBcard)
      have hCL : ((blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i).sort (· ≤ ·)).length ≤ b := by
        rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBcard)
      exact ⟨(hagree _ (by omega) (by omega)).trans h1.1,
        (hagree _ (by omega) (by omega)).trans h1.2.1,
        fun idx hidx =>
          have : idx < b := lt_of_lt_of_le hidx hSL
          (hagree _ (by omega) (by omega)).trans (h1.2.2.1 idx hidx),
        fun idx hidx =>
          have : idx < b := lt_of_lt_of_le hidx hCL
          (hagree _ (by omega) (by omega)).trans (h1.2.2.2 idx hidx)⟩,
    fun i hi => by
      dsimp only; rw [hX_card, hps_id]
      have hW := hpers.w_at i hi; dsimp only at hW; rw [hX_card, hps_id] at hW
      have hiw : (i + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); rw [Nat.succ_mul] at hiw
      have hWlen : 2 + 2 * (witnessEdges (bst.rounds i) (bst.numRounds i)).length ≤ ps.wStride := by
        rw [witnessEdges_length (hrounds_len i hi)]
        have h1 := Nat.mul_le_mul_right (b / 2) (hnum_le i hi)
        have h2 : ps.wStride = 2 + 2 * ((49 * L + 1) * (b / 2)) := by dsimp only [ps, sbPersist]; ring
        omega
      rw [graphAt_mk_iff] at hW ⊢
      exact ⟨(hagree _ (by omega) (by omega)).trans hW.1,
        (hagree _ (by omega) (by omega)).trans hW.2.1,
        fun idx hidx => ⟨(hagree _ (by omega) (by omega)).trans (hW.2.2 idx hidx).1,
          (hagree _ (by omega) (by omega)).trans (hW.2.2 idx hidx).2⟩⟩,
    fun idx hidx => by
      have hidx' : idx < b := by simpa using hidx
      have h0r := hpers.rangeB_at; rw [hX_card, hps_id] at h0r ⊢
      exact (hagree _ (by omega) (by omega)).trans (h0r idx hidx)⟩

private lemma sbFinal_callRouter {w bRoute C_rt C_sp gA h0 pairsA Δ L z pA rtOutA hRt r1Bnd : ℕ}
    {p : Program} {G : Graph} {X : Finset ℕ} {vs : List ℕ}
    {injPairs : List (Finset ℕ × Finset ℕ)} {injPairLists : List (List ℕ × List ℕ)}
    {st st1 : State} {ω : ℕ → Bool}
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (hG_1 : GraphAt st1.mem gA G) (hXlen_1 : LenListAt st1.mem h0 vs)
    (hvs_fin : vs.toFinset = X) (hmp1 : MultiPairsAt st1.mem pairsA injPairLists)
    (hipl_map : injPairLists.map (fun pr => (pr.1.toFinset, pr.2.toFinset)) = injPairs)
    (hcp_L : st1.mem (pA + 1) = L) (hcp_Δ : st1.mem (pA + 2) = Δ)
    (hhRt : hRt = rtOutA + 2 + 2 * G.n)
    (hrcCost_le : routerCallCost G X injPairs Δ L 100 z ≤ r1Bnd)
    (hsp_mono : outerRouterSpace C_sp G.n (routerCallCost G X injPairs Δ L 100 z) ≤
      outerRouterSpace C_sp G.n r1Bnd)
    (hPreRt : (multiPairRouterContract C_rt C_sp w).pre
      [gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt] st1.mem)
    (hW : gA < 2 ^ w ∧ h0 < 2 ^ w ∧ pairsA < 2 ^ w ∧ Δ < 2 ^ w ∧ L < 2 ^ w ∧
      z < 2 ^ w ∧ pA + 2 < 2 ^ w ∧ rtOutA < 2 ^ w ∧ hRt < 2 ^ w ∧ 128 < 2 ^ w)
    (hr1 : st1.regs 1 = gA) (hr6 : st1.regs 6 = z) (hr7 : st1.regs 7 = pA)
    (hr11 : st1.regs 11 = h0) (hr22 : st1.regs 22 = pairsA) (hr23 : st1.regs 23 = rtOutA)
    (hlt22 : ∀ r < 22, st1.regs r = st.regs r) :
    ∃ (hAfterRt : ℕ) (memR : ℕ → ℕ) (stR : State) (cR : ℕ),
      Runs w p ω (seqStmts [
        .assign 24 (.reg 23),
        .assign 25 (.load (.reg 1)),
        .assign 26 (.bin .add (.bin .add (.reg 24) (.const 2)) (.bin .mul (.const 2) (.reg 25))),
        .assign 27 (.load (.bin .add (.reg 7) (.const 2))),
        .assign 28 (.load (.bin .add (.reg 7) (.const 1))),
        .call 12 bRoute [.reg 1, .reg 11, .reg 22, .reg 27, .reg 28, .const 100, .reg 6, .reg 24, .reg 26]])
        st1 .normal stR cR ∧
      stR.mem = memR ∧ stR.regs 12 = hAfterRt ∧ stR.regs 24 = rtOutA ∧
      (∀ r < 22, r ≠ 12 → stR.regs r = st.regs r) ∧
      RouteOutAt memR rtOutA (routeOrCut G X injPairs Δ L 100 z) ∧
      hRt ≤ hAfterRt ∧ hAfterRt ≤ hRt + outerRouterSpace C_sp G.n r1Bnd ∧
      ZeroFrom memR hAfterRt ∧
      (∀ a < hRt, (a < rtOutA ∨ rtOutA + 2 + 2 * G.n ≤ a) → memR a = st1.mem a) ∧
      cR ≤ C_rt * r1Bnd + C_rt + 50 := by
  rcases hW with ⟨_, _, _, _, _, _, _, _, _, _⟩
  have hrunR : ∃ o stR cR,
      Runs w p ω (seqStmts [
        .assign 24 (.reg 23),
        .assign 25 (.load (.reg 1)),
        .assign 26 (.bin .add (.bin .add (.reg 24) (.const 2)) (.bin .mul (.const 2) (.reg 25))),
        .assign 27 (.load (.bin .add (.reg 7) (.const 2))),
        .assign 28 (.load (.bin .add (.reg 7) (.const 1))),
        .call 12 bRoute [.reg 1, .reg 11, .reg 22, .reg 27, .reg 28, .const 100, .reg 6, .reg 24, .reg 26]])
        st1 o stR cR ∧
      (normalPost fun stR =>
        stR.regs 24 = rtOutA ∧ (∀ r < 22, r ≠ 12 → stR.regs r = st.regs r) ∧
        RouteOutAt stR.mem rtOutA (routeOrCut G X injPairs Δ L 100 z) ∧
        hRt ≤ stR.regs 12 ∧ stR.regs 12 ≤ hRt + outerRouterSpace C_sp G.n r1Bnd ∧
        ZeroFrom stR.mem (stR.regs 12) ∧
        (∀ a < hRt, (a < rtOutA ∨ rtOutA + 2 + 2 * G.n ≤ a) → stR.mem a = st1.mem a)) o stR ∧
      cR ≤ C_rt * r1Bnd + C_rt + 50 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := rtOutA) (Expr.eval_reg_of_eq hr23) ?_
    refine runs_seq_assign_le (v := G.n)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr1]))
        (graphAt_n hG_1)) ?_
    refine runs_seq_assign_le (v := hRt)
      (by rw [hhRt]; exact Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := Δ)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]))
        (Expr.eval_const (by omega)) (by omega)) hcp_Δ) ?_
    refine runs_seq_assign_le (v := L)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]))
        (Expr.eval_const (by omega)) (by omega)) hcp_L) ?_
    have hWords : ∀ v ∈ ([gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt] : List ℕ), v < 2 ^ w := by
      intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hreadG : readGraph st1.mem gA = G := readGraph_eq_of_graphAt hG_1
    have hreadX : (readLenPrefixedList st1.mem h0).toFinset = X := by
      rw [readLenPrefixedList_eq_of_lenListAt hXlen_1, hvs_fin]
    have hreadP : readMultiPairs st1.mem pairsA = injPairs := by
      rw [readMultiPairs_eq_of_multiPairsAt hmp1, hipl_map]
    refine runs_call_le hRoute (vs := [gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt]) (by
      have h100 : 100 < 2 ^ w := by omega
      simp only [evalArgs, Expr.eval, h100, ↓reduceIte]
      simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 28), Function.update_of_ne (by decide : (1 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (1 : ℕ) ≠ 26), Function.update_of_ne (by decide : (1 : ℕ) ≠ 25),
        Function.update_of_ne (by decide : (1 : ℕ) ≠ 24),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 28), Function.update_of_ne (by decide : (11 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 26), Function.update_of_ne (by decide : (11 : ℕ) ≠ 25),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 24),
        Function.update_of_ne (by decide : (22 : ℕ) ≠ 28), Function.update_of_ne (by decide : (22 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (22 : ℕ) ≠ 26), Function.update_of_ne (by decide : (22 : ℕ) ≠ 25),
        Function.update_of_ne (by decide : (22 : ℕ) ≠ 24),
        Function.update_of_ne (by decide : (27 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 28), Function.update_of_ne (by decide : (6 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 26), Function.update_of_ne (by decide : (6 : ℕ) ≠ 25),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 24),
        Function.update_of_ne (by decide : (24 : ℕ) ≠ 28), Function.update_of_ne (by decide : (24 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (24 : ℕ) ≠ 26), Function.update_of_ne (by decide : (24 : ℕ) ≠ 25),
        Function.update_of_ne (by decide : (26 : ℕ) ≠ 28), Function.update_of_ne (by decide : (26 : ℕ) ≠ 27),
        Function.update_self, hr1, hr11, hr6, hr22]) hWords hPreRt ?_ (by
      simp only [argsSize, Expr.size, multiPairRouterContract, List.getD_cons_zero, List.getD_cons_succ,
        hreadG, hreadX, hreadP]
      have := Nat.mul_le_mul_left C_rt hrcCost_le; omega)
    intro v memR _ hpostR
    simp only [multiPairRouterContract, List.getD_cons_zero, List.getD_cons_succ,
      hreadG, hreadX, hreadP] at hpostR
    rcases hpostR with ⟨hRout, hv1, hv2, hzfR, hfrR⟩
    refine ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self],
      fun r hr hne => by
        dsimp only
        rw [Function.update_of_ne hne, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          hlt22 r hr],
      hRout, by simp [hv1], by simp; exact le_trans hv2 (by omega), by simpa using hzfR, hfrR⟩
  rcases hrunR with ⟨o, stR, cR, hrR, hpR, hcR⟩
  cases o with
  | returned _ => exact False.elim hpR
  | normal =>
    rcases hpR with ⟨h24, hlt22R, hRout, h12ge, h12le, hzfR, hfrR⟩
    exact ⟨stR.regs 12, stR.mem, stR, cR, hrR, rfl, rfl, h24, hlt22R, hRout, h12ge, h12le, hzfR, hfrR, hcR⟩

private lemma sbFinalInj_matched {w k b nBlocks L h0 locA fA outA rtOutA hAfterRt : ℕ}
    {p : Program} {mem0 memR : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {matchings : List (List (ℕ × ℕ))} {stR : State} {ω : ℕ → Bool}
    (hX_card : X.card = k) (hX_sub : X ⊆ Finset.range G.n)
    (hb_pos : 0 < b) (hnb_b : nBlocks * b ≤ k)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hall_inact : ∀ i < nBlocks, bst.active i = false)
    (hsub_B : ∀ i < nBlocks, bst.savedS i ⊆ blockSet (X.sort (· ≤ ·)) b i)
    (hvtp : ValidTerminalPairs X ((List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i)))
    (hmlen : matchings.length = nBlocks)
    (hpm : ∀ i, i < nBlocks →
      IsPartialMatching (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i) (bst.savedS i) (matchings.getD i []))
    (hpersR : SbPersistAt memR G X b nBlocks L h0 bst)
    (hF_atR : EdgesAt memR fA (callsFakeEdges bst.calls))
    (hF_cap : (callsFakeEdges bst.calls).length +
      (completeBatchFake ((List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i)) matchings).length ≤ k)
    (htag0 : memR rtOutA = 0)
    (hmLenR : memR (rtOutA + 1) = matchings.flatten.length)
    (hmAtR : EdgesAt memR (rtOutA + 2) matchings.flatten)
    (hloc0 : ∀ u < G.n, mem0 (locA + u) = 0)
    (hlocR : ∀ u < G.n, memR (locA + u) = 0)
    (hzfR : ZeroFrom memR hAfterRt)
    (hfrR_0 : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) → (a < fA ∨ fA + 2 * k ≤ a) →
      (a < outA ∨ outA + 2 + k ≤ a) → memR a = mem0 a)
    (hgeom : locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n fA (2 * k) ∧ DisjointRange locA G.n outA (2 + k) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧
      (sbPersist h0 k b nBlocks L).hPersist ≤ rtOutA ∧
      rtOutA + 2 + 2 * G.n ≤ hAfterRt ∧ hAfterRt + 2 * b < 2 ^ w ∧ 128 < 2 ^ w)
    (hregs : stR.regs 4 = b ∧ stR.regs 5 = nBlocks ∧ stR.regs 8 = locA ∧ stR.regs 9 = fA ∧
      stR.regs 10 = outA ∧ stR.regs 12 = hAfterRt ∧ stR.regs 14 = (callsFakeEdges bst.calls).length ∧
      stR.regs 17 = (sbPersist h0 k b nBlocks L).actA ∧
      stR.regs 18 = (sbPersist h0 k b nBlocks L).savA ∧
      stR.regs 19 = (sbPersist h0 k b nBlocks L).cmpA ∧
      stR.regs 24 = rtOutA)
    (hmemR_eq : stR.mem = memR) :
    let injPairs := (List.range nBlocks).map fun i => (blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i, bst.savedS i)
    ∃ st2 cPost,
      Runs w p ω (.cond (.bin .eq (.load (.reg 24)) (.const 1))
          (seqStmts [sbCopyCutZeroStmt 24 10 27 28 29, .ret (.reg 12)])
          (seqStmts [sbFinalMatchedStmt, .ret (.reg 12)])) stR (.returned (hAfterRt + 2 * b)) st2 cPost ∧
      st2.mem outA = 1 ∧
      st2.mem (outA + 1) = (callsFakeEdges bst.calls).length + (completeBatchFake injPairs matchings).length ∧
      EdgesAt st2.mem fA (callsFakeEdges bst.calls ++ completeBatchFake injPairs matchings) ∧
      ZeroFrom st2.mem (hAfterRt + 2 * b) ∧
      (∀ u < G.n, st2.mem (locA + u) = 0) ∧
      (∀ a < h0, (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → st2.mem a = mem0 a) ∧
      cPost ≤ 260 * k + 260 * nBlocks + 240 := by
  intro injPairs
  rcases hgeom with ⟨hloc_h, hf_h, hout_h, hd_lf, hd_lo, hd_of, hps_rt, hRt_le, hAfter_w, hw128⟩
  have hps_ge : h0 ≤ (sbPersist h0 k b nBlocks L).hPersist := by dsimp [sbPersist]; omega
  have hflat_le_k : matchings.flatten.length ≤ k := by
    have h1 : matchings.flatten.length = (matchings.map List.length).sum := List.length_flatten
    rw [h1]
    have hgen : ∀ (L : List (List (ℕ × ℕ))), (∀ x ∈ L, x.length ≤ b) →
        (L.map List.length).sum ≤ L.length * b := by
      intro L; induction L with
      | nil => intro _; simp
      | cons a rest ih =>
        intro hall; simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        have := hall a List.mem_cons_self; have := ih fun x hx => hall x (List.mem_cons_of_mem _ hx); omega
    have h2 := hgen matchings fun x hx => by
      rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
      have hi : idx < nBlocks := hmlen ▸ hidx
      have hpmi := hpm idx hi
      have hsub1 : ((matchings.getD idx []).map Prod.fst).toFinset ⊆ blockSet (X.sort (· ≤ ·)) b idx \ bst.savedS idx := by
        intro v hv; rcases List.mem_map.mp (List.mem_toFinset.mp hv) with ⟨e, he, rfl⟩; exact (hpmi.1 e he).1
      have hle1 : (matchings.getD idx []).length ≤ (blockSet (X.sort (· ≤ ·)) b idx \ bst.savedS idx).card := by
        rw [← List.length_map Prod.fst, ← List.toFinset_card_of_nodup hpmi.2.1]
        exact Finset.card_le_card hsub1
      have hBcard : (blockSet (X.sort (· ≤ ·)) b idx).card = b :=
        card_blockSet (Finset.sort_nodup X (· ≤ ·)) (hnb_eq ▸ hi)
      have hle2 : (blockSet (X.sort (· ≤ ·)) b idx \ bst.savedS idx).card ≤ b :=
        (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBcard)
      simpa [List.getD_eq_getElem?_getD, hidx] using hle1.trans hle2
    rw [hmlen] at h2; omega
  have hflat_le_n : matchings.flatten.length ≤ G.n := by
    have : k ≤ G.n := by rw [← hX_card]; exact (Finset.card_le_card hX_sub).trans (by simp)
    omega
  obtain ⟨o2, st2, c2, hr2, hp2, hc2⟩ :=
    sbFinalMatched_triple (w := w) (p := p) hX_card hX_sub hb_pos hnb_b hnb_eq hall_inact hsub_B hvtp hmlen hpm
      hflat_le_k hflat_le_n hpersR rfl hF_atR hF_cap hmLenR hmAtR hlocR
      ⟨hloc_h, hf_h, hout_h, hd_lf, hd_lo, hd_of, hps_rt, hRt_le, hAfter_w, by omega⟩
      hregs hmemR_eq stR ω rfl
  dsimp only at hc2
  cases o2 with
  | returned _ => exact False.elim hp2
  | normal =>
    rcases hp2 with ⟨hr12_2, _, hout1, houtLen, hF2, hloc2, hfr2⟩
    have hret : Runs w p ω (.ret (.reg 12)) st2 (.returned (hAfterRt + 2 * b)) st2 (Expr.size (.reg 12) + 1) :=
      runs_ret_n (Expr.eval_reg_of_eq hr12_2)
    have hcond_f : (.bin .eq (.load (.reg 24)) (.const 1) : Expr).eval w stR = some 0 :=
      Expr.eval_eq_false (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hregs.2.2.2.2.2.2.2.2.2.2) (hmemR_eq ▸ htag0))
        (Expr.eval_const (by omega)) (by decide) (by omega)
    refine ⟨st2, _, runs_cond_ret_f hcond_f (runs_seq_ret_n hr2 hret),
      hout1, houtLen, hF2,
      fun a ha => by
        rw [hfr2 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr ha)]
        exact hzfR a (by omega),
      hloc2,
      fun a ha hfa hout => by
        by_cases hloc_a : a < locA ∨ locA + G.n ≤ a
        · rw [hfr2 a hloc_a hfa (by rcases hout with h | h <;> [left; right] <;> omega) (Or.inl (by omega))]
          exact hfrR_0 a ha hloc_a hfa hout
        · have hu : a - locA < G.n := by omega
          have ha_eq : a = locA + (a - locA) := by omega
          rw [ha_eq, hloc2 _ hu, hloc0 _ hu],
      by simp only [Expr.size]; omega⟩

/-- Executes `sbFinalInjStmt bRoute` from `SbLoopInv ... (49 * L + 1) st` with `st.regs 13 = 0`,
returning `.returned hRet` meeting every postcondition of `stepBContract`. -/
theorem sbFinalInj_run {cfg : ParamConfig} {M r q w bRoute C_rt C_sp Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {st : State} {ω : ℕ → Bool}
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt mem0 pA (coreParamsOf cfg M r) r)
    (hG_at : GraphAt mem0 gA G) (hG_val : G.IsValid)
    (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc0 : ∀ u < G.n, mem0 (locA + u) = 0)
    (hgeom : gA + 2 + 2 * G.m ≤ h0 ∧ xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n gA (2 + 2 * G.m) ∧ DisjointRange locA G.n xA k ∧
      DisjointRange locA G.n pA (coreParamsSize r) ∧ DisjointRange locA G.n fA (2 * k) ∧
      DisjointRange locA G.n outA (2 + k) ∧ DisjointRange outA (2 + k) gA (2 + 2 * G.m) ∧
      DisjointRange outA (2 + k) xA k ∧ DisjointRange outA (2 + k) pA (coreParamsSize r) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧ DisjointRange fA (2 * k) gA (2 + 2 * G.m) ∧
      DisjointRange fA (2 * k) xA k ∧ DisjointRange fA (2 * k) pA (coreParamsSize r))
    (hSpace_w : (sbPersist h0 k b nBlocks (LParam M)).hPersist +
      (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks +
      (outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
        3 * k + 2 * nBlocks + 2 * G.n + 5) < 2 ^ w)
    (hΔ_w : (coreParamsOf cfg M r).Δ < 2 ^ w)
    (hw128 : 128 < 2 ^ w)
    (hInv : SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X
      (49 * LParam M + 1) st)
    (hr13_0 : st.regs 13 = 0) :
    ∃ hRet st' cost,
      Runs w p ω (sbFinalInjStmt bRoute) st (.returned hRet) st' cost ∧
      ((st'.mem outA = 0 ∧ ∃ U : Finset ℕ, CoreOutAt st'.mem outA (.cut U) ∧ RouteCutSpec G X 100 z U) ∨
        (st'.mem outA = 1 ∧ ∃ callsB : List RoutedCall,
          callsB.length ≤ 49 * (coreParamsOf cfg M r).L + 2 ∧
          (∀ c ∈ callsB, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100 (coreParamsOf cfg M r).L) z) ∧
          (∀ i < nBlocks, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
            (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * ((coreParamsOf cfg M r).P (q - 1) : ℝ)))) ∧
          st'.mem (outA + 1) = (callsFakeEdges callsB).length ∧
          EdgesAt st'.mem fA (callsFakeEdges callsB))) ∧
      h0 ≤ hRet ∧
      hRet ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist +
        (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks +
        (outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
          3 * k + 2 * nBlocks + 2 * G.n + 5) ∧
      ZeroFrom st'.mem hRet ∧
      (∀ u < G.n, st'.mem (locA + u) = 0) ∧
      (∀ a < h0, (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → st'.mem a = mem0 a) ∧
      cost ≤ C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt + 320 * k + 460 * nBlocks + 360 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  rcases hgeom with ⟨hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h, hd_lg, hd_lx, hd_lp, hd_lf, hd_lo,
    hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp⟩
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_pos : 0 < b := by have := harith.2.2.1; omega
  have hXL : X.card < 2 ^ cp.L := by rw [← hX_at.1]; exact harith.2.2.2.2.2.2.2.2
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b; rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  rcases hInv.state_match with ⟨hr13_1, _⟩ | ⟨_, bst, hmod, hpers, hr14, hF_at⟩
  · omega
  -- Apply `sbModelInv_final_inj`
  have hfin := sbModelInv_final_inj hcfg hq2 hqr hX_sub hGloop hdegG hXL
    (Finset.sort_nodup X (· ≤ ·)) (by ext u; simp) hb_pos (hnb_eq ▸ hmod)
  dsimp only at hfin
  rcases hfin with ⟨hall_inact0, hvtp0, hrc_fin⟩
  have hall_inact : ∀ i < nBlocks, bst.active i = false := fun i hi => hall_inact0 i (hnb_eq ▸ hi)
  set injPairs := (List.range nBlocks).map fun i => (blockSet vs b i \ bst.savedS i, bst.savedS i)
  set injPairLists := (List.range nBlocks).map fun i =>
    ((blockSet vs b i \ bst.savedS i).sort (· ≤ ·), (bst.savedS i).sort (· ≤ ·))
  have hvtp : ValidTerminalPairs X injPairs := by rw [← hnb_eq] at hvtp0; exact hvtp0
  have hsub_B : ∀ i < nBlocks, bst.savedS i ⊆ blockSet vs b i :=
    fun i hi => (hmod.inactive_exp i hi (hall_inact i hi)).1
  set pairsA := st.regs 12
  set rtOutA := pairsA + 1 + nBlocks * (2 + b)
  set hRt := rtOutA + 2 + 2 * G.n
  have hpairs_le : pairsA ≤ ps.hPersist + (49 * LParam M + 1) *
      sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks := hInv.h_le
  have hpairs_ge : ps.hPersist ≤ pairsA := hInv.h_ge
  have hrt_space : hRt + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) + 2 * b ≤
      ps.hPersist + (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks +
        (outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
          3 * k + 2 * nBlocks + 2 * G.n + 5) := by
    have hmul : nBlocks * (2 + b) = 2 * nBlocks + nBlocks * b := by ring
    omega
  -- Step 1: Build `injPairLists` at `pairsA`
  obtain ⟨o1, st1, c1, hr1, hp1, hc1⟩ :=
    sbFinalBuildPairs_triple (w := w) (p := p) hX_at.1.symm hb_pos hnb_b hnb_eq hall_inact hsub_B hpers hpairs_ge
      (by omega) (by omega) hInv.args.r4 hInv.args.r5 rfl hInv.args.r17 hInv.args.r18 hInv.args.r19 rfl st ω rfl
  dsimp only at hc1
  cases o1 with
  | returned _ => exact False.elim hp1
  | normal =>
    rcases hp1 with ⟨hr22_1, hr23_1, hlt22_1, _, hfr1, hmp1, henc_len1⟩
    -- Step 2: Prepare args and call `bRoute`
    have hG_1 : GraphAt st1.mem gA G := by
      have hagree : ∀ a, gA ≤ a → a < gA + 2 + 2 * G.m → st1.mem a = mem0 a := fun a h1 h2 =>
        (hfr1 a (Or.inl (by omega))).trans (hInv.frame a (by omega)
          (by rcases hd_lg with h | h <;> [right; left] <;> omega)
          (by rcases hd_fg with h | h <;> [right; left] <;> omega)
          (by rcases hd_og with h | h <;> [right; left] <;> omega))
      cases G with | mk gn ges =>
        rw [graphAt_mk_iff] at hG_at ⊢
        exact ⟨(hagree gA (by omega) (by simp [Graph.m]; omega)).trans hG_at.1,
          (hagree (gA + 1) (by omega) (by simp [Graph.m]; omega)).trans hG_at.2.1,
          fun idx hidx => ⟨(hagree _ (by omega) (by simp [Graph.m]; omega)).trans (hG_at.2.2 idx hidx).1,
            (hagree _ (by omega) (by simp [Graph.m]; omega)).trans (hG_at.2.2 idx hidx).2⟩⟩
    have hcp_1 : CoreParamsAt st1.mem pA cp r := by
      have hagree : ∀ a, pA ≤ a → a < pA + coreParamsSize r → st1.mem a = mem0 a := fun a h1 h2 =>
        (hfr1 a (Or.inl (by omega))).trans (hInv.frame a (by omega)
          (by rcases hd_lp with h | h <;> [right; left] <;> omega)
          (by rcases hd_fp with h | h <;> [right; left] <;> omega)
          (by rcases hd_op with h | h <;> [right; left] <;> omega))
      refine ⟨(hagree pA (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.1,
        (hagree (pA + 1) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.1,
        (hagree (pA + 2) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.1,
        (hagree (pA + 3) (by omega) (by unfold coreParamsSize; omega)).trans hcp_at.2.2.2.1,
        fun i hi => (hagree (pA + 4 + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 5 + r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.1 i hi),
        fun i hi => (hagree (pA + 6 + 2 * r + i) (by omega) (by unfold coreParamsSize; omega)).trans (hcp_at.2.2.2.2.2.2 i hi)⟩
    have hXlen_1 : LenListAt st1.mem h0 vs :=
      ⟨(hfr1 h0 (Or.inl (by omega))).trans hpers.xLen_at.1,
        fun idx hidx => by
          have hidx' : idx < k := by rw [Finset.length_sort, ← hX_at.1] at hidx; exact hidx
          exact (hfr1 (h0 + 1 + idx) (Or.inl (by omega))).trans (hpers.xLen_at.2 idx hidx)⟩
    have hipl_nd : ∀ pr ∈ injPairLists, pr.1.Nodup ∧ pr.2.Nodup := by
      intro pr hpr; rcases List.mem_map.mp hpr with ⟨i, _, rfl⟩
      exact ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _⟩
    have hipl_map : injPairLists.map (fun pr => (pr.1.toFinset, pr.2.toFinset)) = injPairs := by
      simp only [injPairLists, injPairs, List.map_map]; congr 1; funext i
      ext u <;> simp
    have hrcCost_le : routerCallCost G X injPairs cp.Δ cp.L 100 z ≤ stepBRouterR1 (NOf M r) (LParam M) q :=
      stepB_single_routerCallCost_le ha hrl hqr hX_sub hGloop hdegG
        (by rw [← hX_at.1]; have := harith.2.2.1; omega) (by rw [← hX_at.1]; exact hkhi) hvtp
        (by simp only [injPairs, List.length_map, List.length_range]; exact harith.2.2.2.2.2.2.1)
    have hsp_mono : outerRouterSpace C_sp G.n (routerCallCost G X injPairs cp.Δ cp.L 100 z) ≤
        outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) := by
      unfold outerRouterSpace; exact Nat.mul_le_mul_left C_sp (by omega)
    have hvs_fin : vs.toFinset = X := by ext u; simp [vs]
    have hzf1 : ZeroFrom st1.mem rtOutA := fun a ha => by
      rw [hfr1 a (Or.inr ha)]; exact hInv.zf a (by omega)
    have hrt_w_bnd : hRt + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) < 2 ^ w := by omega
    have hPreRt : (multiPairRouterContract C_rt C_sp w).pre
        [gA, h0, pairsA, cp.Δ, cp.L, 100, z, rtOutA, hRt] st1.mem :=
      ⟨gA, h0, pairsA, cp.Δ, cp.L, 100, z, rtOutA, hRt, G, vs, injPairLists,
        rfl, hG_1, hG_val, hXlen_1, Finset.sort_nodup X (· ≤ ·), hvs_fin.symm ▸ hX_sub,
        hvs_fin.symm ▸ hGloop, by have := hcfg.hΔ; omega, hvs_fin.symm ▸ hdegG,
        by have := hcfg.hL; omega, hvs_fin.symm ▸ hXL, by decide,
        hmp1, hipl_nd, by rw [hvs_fin, hipl_map]; exact hvtp,
        fun a ha => hzf1 a (by omega),
        by omega, by rw [Finset.length_sort, ← hX_at.1]; omega, by rw [henc_len1]; omega,
        le_refl _, Or.inr (by omega), Or.inr (by rw [Finset.length_sort, ← hX_at.1]; omega),
        Or.inr (by rw [henc_len1]; omega),
        by rw [hvs_fin, hipl_map]; exact lt_of_le_of_lt (Nat.add_le_add_left hsp_mono hRt) hrt_w_bnd,
        by omega,
        by rw [Finset.length_sort, ← hX_at.1]; exact hmG,
        by rw [Finset.length_sort, ← hX_at.1, hz_eq]; exact Nat.div_le_self _ _⟩
    have hL_w : cp.L < 2 ^ w := by
      have : cp.L ≤ cp.Δ := by change LParam M ≤ 1024 * LParam M; omega
      omega
    have hz_le : z ≤ k := by rw [hz_eq]; exact Nat.div_le_self _ _
    obtain ⟨hAfterRt, memR, stR, cR, hrunsR, hmemR_eq, hr12R, hr24R, hlt22R, hRoutR,
        hRt_le, hRt_ub, hzfR, hfrR, hcR⟩ :=
      sbFinal_callRouter hRoute hG_1 hXlen_1 hvs_fin hmp1 hipl_map hcp_1.2.1 hcp_1.2.2.1 rfl
        hrcCost_le hsp_mono hPreRt
        ⟨by omega, by omega, by omega, hΔ_w, hL_w, by omega, by unfold coreParamsSize at hp_h; omega, by omega, by omega, hw128⟩
        ((hlt22_1 1 (by decide)).trans hInv.args.r1) ((hlt22_1 6 (by decide)).trans hInv.args.r6)
        ((hlt22_1 7 (by decide)).trans hInv.args.r7) ((hlt22_1 11 (by decide)).trans hInv.args.r11)
        hr22_1 hr23_1 hlt22_1
    -- Helper combining `hr1` + `hrunsR` + final conditional branch
    have hcomb : ∀ (hRet : ℕ) (st' : State) (cPost : ℕ),
        Runs w p ω (.cond (.bin .eq (.load (.reg 24)) (.const 1))
            (seqStmts [sbCopyCutZeroStmt 24 10 27 28 29, .ret (.reg 12)])
            (seqStmts [sbFinalMatchedStmt, .ret (.reg 12)])) stR (.returned hRet) st' cPost →
        ∃ cost, Runs w p ω (sbFinalInjStmt bRoute) st (.returned hRet) st' cost ∧
          cost ≤ c1 + cR + cPost + 20 := by
      intro hRet st' cPost hPost
      dsimp only [sbFinalInjStmt, seqStmts] at hrunsR ⊢
      rcases runs_seq_n_mp hrunsR with ⟨s1, c1a, c1b, h1a, h1b, hcR1⟩
      rcases runs_seq_n_mp h1b with ⟨s2, c2a, c2b, h2a, h2b, hcR2⟩
      rcases runs_seq_n_mp h2b with ⟨s3, c3a, c3b, h3a, h3b, hcR3⟩
      rcases runs_seq_n_mp h3b with ⟨s4, c4a, c4b, h4a, h4b, hcR4⟩
      rcases runs_seq_n_mp h4b with ⟨s5, c5a, c5b, h5a, h5b, hcR5⟩
      refine ⟨_, runs_seq_ret_n hr1 (runs_seq_ret_n h1a (runs_seq_ret_n h2a (runs_seq_ret_n h3a
        (runs_seq_ret_n h4a (runs_seq_ret_n h5a (runs_seq_ret_n h5b hPost)))))), ?_⟩
      omega
    have hfrR_below : ∀ a < rtOutA, memR a = st1.mem a := fun a ha => hfrR a (by omega) (Or.inl ha)
    have hlocR : ∀ u < G.n, memR (locA + u) = 0 := fun u hu => by
      rw [hfrR_below _ (by omega), hfr1 _ (Or.inl (by omega))]; exact hInv.loc0 u hu
    -- Case split on `routeOrCut G X injPairs cp.Δ cp.L 100 z`
    cases hrc_eq : routeOrCut G X injPairs cp.Δ cp.L 100 z with
    | cut U =>
      have hcut_spec : RouteCutSpec G X 100 z U := by
        rw [← hnb_eq] at hrc_fin; dsimp only [injPairs] at hrc_eq; rw [hrc_eq] at hrc_fin; exact hrc_fin
      rw [hrc_eq] at hRoutR
      rcases hRoutR with ⟨htag1, U_l, hU_nd, hU_fin, hU_len_mem, hU_atR⟩
      have hU_card : U_l.length = U.card := by rw [← hU_fin, List.toFinset_card_of_nodup hU_nd]
      have hU_le_k : U_l.length ≤ k := by rw [hU_card, hX_at.1]; exact Finset.card_le_card hcut_spec.1
      have hU_le_n : U_l.length ≤ G.n := by
        rw [hU_card]; exact Finset.card_range G.n ▸ Finset.card_le_card (hcut_spec.1.trans hX_sub)
      obtain ⟨o2, st2, c2, hr2, hp2, hc2⟩ :=
        sbCopyCutZero_triple (w := w) (cap := 2 + U_l.length) (srcA := rtOutA) (dstA := outA)
          (rSrc := 24) (rDst := 10) (rLen := 27) (rI := 28) (rU := 29) (by decide)
          p memR U_l stR hU_len_mem hU_atR (le_refl _) (Or.inl (by omega))
          (by omega) (by omega) (by omega) hr24R ((hlt22R 10 (by decide) (by decide)).trans hInv.args.r10)
          hmemR_eq stR ω rfl
      cases o2 with
      | returned _ => exact False.elim hp2
      | normal =>
        rcases hp2 with ⟨hoth2, _, hfr2, htag0, hlen2, hlat2⟩
        have hret : Runs w p ω (.ret (.reg 12)) st2 (.returned hAfterRt) st2 (Expr.size (.reg 12) + 1) :=
          runs_ret_n (Expr.eval_reg_of_eq ((hoth2 12 (by decide) (by decide) (by decide)).trans hr12R))
        have hcond_t : (.bin .eq (.load (.reg 24)) (.const 1) : Expr).eval w stR = some 1 :=
          Expr.eval_eq_true (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr24R) (hmemR_eq ▸ htag1))
            (Expr.eval_const (by omega)) rfl (by omega)
        obtain ⟨cost, hruns_full, hcost⟩ := hcomb hAfterRt st2 _ (runs_cond_ret_t hcond_t (by decide) (runs_seq_ret_n hr2 hret))
        refine ⟨hAfterRt, st2, cost, hruns_full,
          Or.inl ⟨htag0, U, ⟨htag0, U_l, hU_nd, hU_fin, hlen2, hlat2⟩, hcut_spec⟩,
          by omega, by omega,
          fun a ha => by rw [hfr2 a (Or.inr (by omega))]; exact hzfR a ha,
          fun u hu => by rw [hfr2 _ (by rcases hd_lo with h | h <;> [left; right] <;> omega)]; exact hlocR u hu,
          fun a ha hfa hout => by
            by_cases hloc_a : a < locA ∨ locA + G.n ≤ a
            · rw [hfr2 a (by rcases hout with h | h <;> [left; right] <;> omega),
                hfrR_below a (by omega), hfr1 a (Or.inl (by omega))]
              exact hInv.frame a ha hloc_a hfa hout
            · have hu : a - locA < G.n := by omega
              have ha_eq : a = locA + (a - locA) := by omega
              rw [ha_eq, hfr2 _ (by rcases hd_lo with h | h <;> [left; right] <;> omega), hlocR _ hu, hloc0 _ hu],
          by dsimp only at hc2; simp only [Expr.size] at hcost ⊢; omega⟩
    | matched matchings emb =>
      rw [← hnb_eq] at hrc_fin; dsimp only [injPairs] at hrc_eq; rw [hrc_eq] at hrc_fin
      rcases hrc_fin with ⟨hcalls_len, hcalls_val, hblocks_exp⟩
      rw [hrc_eq] at hRoutR
      rcases hRoutR with ⟨htag0, hmLenR, hmAtR⟩
      have hmspec := routeOrCut_isMatchingPlayer.spec G X injPairs cp.Δ cp.L 100 z
        hX_sub hGloop hcfg.hΔ_pos hdegG hcfg.hL hXL (by decide) hvtp
      rw [hrc_eq] at hmspec
      have hmlen : matchings.length = nBlocks := by rw [hmspec.1]; simp [injPairs]
      have hpm : ∀ i, i < nBlocks →
          IsPartialMatching (blockSet vs b i \ bst.savedS i) (bst.savedS i) (matchings.getD i []) := fun i hi => by
        have h := hmspec.2.1 i (by simp [injPairs, hi])
        dsimp only [injPairs] at h
        simp only [List.getD_eq_getElem?_getD, List.getElem_map, List.getElem_range] at h ⊢
        exact h
      have hF_cap : (callsFakeEdges bst.calls).length + (completeBatchFake injPairs matchings).length ≤ k := by
        have h := sb_callsFakeEdges_length_le_k hcfg (by omega) hqr hz_eq hcalls_len hcalls_val
        simpa [callsFakeEdges] using h
      have hpersR : SbPersistAt memR G X b nBlocks (LParam M) h0 bst :=
        sbPersistAt_of_agree hX_at.1.symm hnb_b hnb_eq hsub_B hmod.rounds_len hmod.numRounds_le hpers
          fun a h1 h2 => by
            rw [hps_id] at h2
            exact (hfrR_below a (by omega)).trans (hfr1 a (Or.inl (by omega)))
      have hF_atR : EdgesAt memR fA (callsFakeEdges bst.calls) := fun idx hidx => by
        have hlen_lt : (callsFakeEdges bst.calls).length ≤ k := by omega
        rw [hfrR_below _ (by omega), hfrR_below _ (by omega),
          hfr1 _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega))]
        exact hF_at idx hidx
      obtain ⟨st2, cPost, hrPost, hout1, houtLen, hF2, hzf2, hloc2, hfr2, hcPost⟩ :=
        sbFinalInj_matched hX_at.1.symm hX_sub hb_pos hnb_b hnb_eq hall_inact hsub_B hvtp hmlen hpm
          hpersR hF_atR hF_cap htag0 hmLenR hmAtR hloc0 hlocR hzfR
          (fun a ha hloc_a hfa hout => by
            rw [hfrR_below a (by omega), hfr1 a (Or.inl (by omega))]
            exact hInv.frame a ha hloc_a hfa hout)
          ⟨hloc_h, hf_h, hout_h, hd_lf, hd_lo, hd_of, by rw [hps_id]; omega, hRt_le, by omega, hw128⟩
          ⟨(hlt22R 4 (by decide) (by decide)).trans hInv.args.r4,
           (hlt22R 5 (by decide) (by decide)).trans hInv.args.r5,
           (hlt22R 8 (by decide) (by decide)).trans hInv.args.r8,
           (hlt22R 9 (by decide) (by decide)).trans hInv.args.r9,
           (hlt22R 10 (by decide) (by decide)).trans hInv.args.r10,
           hr12R,
           (hlt22R 14 (by decide) (by decide)).trans hr14,
           (hlt22R 17 (by decide) (by decide)).trans hInv.args.r17,
           (hlt22R 18 (by decide) (by decide)).trans hInv.args.r18,
           (hlt22R 19 (by decide) (by decide)).trans hInv.args.r19,
           hr24R⟩ hmemR_eq
      obtain ⟨cost, hruns_full, hcost⟩ := hcomb (hAfterRt + 2 * b) st2 cPost hrPost
      let callsB := bst.calls ++ [⟨matchings.flatten, emb, completeBatchFake injPairs matchings⟩]
      have hcf_eq : callsFakeEdges callsB = callsFakeEdges bst.calls ++ completeBatchFake injPairs matchings := by
        simp [callsB, callsFakeEdges]
      exact ⟨hAfterRt + 2 * b, st2, cost, hruns_full,
        Or.inr ⟨hout1, callsB, hcalls_len, hcalls_val, hblocks_exp,
          by rw [houtLen, hcf_eq, List.length_append], by rw [hcf_eq]; exact hF2⟩,
        by omega, by omega, hzf2, hloc2, hfr2, by omega⟩

end MinCostFlow.ExpanderDecomp
