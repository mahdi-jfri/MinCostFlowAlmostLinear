module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBRoundPost

import Mathlib.Tactic.Linarith

/-!
# Step B Single-Round Helper Lemmas (`ProgStepBRoundHelpers`)

Provides shared `Runs` combinators (`runs_seq_n`, `runs_seq_n_mp`, `runs_cond_t`, `runs_cond_f`,
`runs_store_n`, `runs_nop_n`, `runs_call_le`), the router-call helper `sbOneRound_callRouter`, and
the zero-cut-blocks branch `sbOneRound_afterQuery_zero` used by `ProgStepBRound.lean` and
`ProgStepBFinal.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `Runs` Combinators -/

lemma runs_seq_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st1 st2 : State} {c1 c2 : ℕ}
    (h1 : Runs w p ω s st .normal st1 c1) (h2 : Runs w p ω t st1 .normal st2 c2) :
    Runs w p ω (.seq s t) st .normal st2 (c1 + c2 + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩)

lemma runs_seq_n_mp {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st2 : State} {c : ℕ} (h : Runs w p ω (.seq s t) st .normal st2 c) :
    ∃ st1 c1 c2, Runs w p ω s st .normal st1 c1 ∧ Runs w p ω t st1 .normal st2 c2 ∧
      c = c1 + c2 + 1 := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hc, _⟩ | h2
  · cases hc
  · exact h2

lemma runs_cond_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {v c1 : ℕ} (he : e.eval w st = some v) (hv : v ≠ 0)
    (hs : Runs w p ω s st .normal st' c1) :
    Runs w p ω (.cond e s t) st .normal st' (e.size + c1 + 1) :=
  runs_cond_iff.mpr ⟨v, c1, he, by simp only [hv, ↓reduceIte]; exact hs, rfl⟩

lemma runs_cond_f {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st st' : State} {c1 : ℕ} (he : e.eval w st = some 0)
    (ht : Runs w p ω t st .normal st' c1) :
    Runs w p ω (.cond e s t) st .normal st' (e.size + c1 + 1) :=
  runs_cond_iff.mpr ⟨0, c1, he, by simp only [↓reduceIte]; exact ht, rfl⟩

lemma runs_store_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {st : State} {x v : ℕ} (ha : a.eval w st = some x) (he : e.eval w st = some v) :
    Runs w p ω (.store a e) st .normal { st with mem := Function.update st.mem x v } (a.size + e.size + 1) :=
  runs_store_iff.mpr ⟨x, v, ha, he, rfl, rfl, rfl⟩

lemma runs_nop_n {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    Runs w p ω .nop st .normal st 1 :=
  runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩

lemma runs_call_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {st : State} {vs : List ℕ} {k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C) (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w) (hpre : C.pre vs st.mem)
    (hpost : ∀ v mem' pos', C.post vs st.mem v mem' →
      Q .normal { mem := mem', regs := Function.update st.regs r v, pos := pos' })
    (hc : k + (argsSize args + C.cost vs st.mem + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases runs_call_of_meetsContract (r := r) hf hargs hwords hpre ω with
    ⟨st₁, c₁, v, hr₁, hcpost, hr, hother, hcost⟩
  have hst₁ : st₁ = { mem := st₁.mem, regs := Function.update st.regs r v, pos := st₁.pos } := by
    cases st₁; dsimp only at hr hother; simp only [State.mk.injEq, true_and, and_true]
    funext r'; by_cases hr' : r' = r
    · subst hr'; simp [hr]
    · simp [hr', hother]
  exact ⟨.normal, st₁, c₁, hr₁, hst₁ ▸ hpost v st₁.mem st₁.pos hcpost, by omega⟩

/-! ## 2. Router-Call Helper (`sbOneRound_callRouter`) -/

/-- Executes the 5 argument-loading assignments plus `.call 12 bRoute ...` inside one Step B round. -/
theorem sbOneRound_callRouter {w bRoute C_rt C_sp gA h0 pairsA pA z rtOutA hRt Δ L R1 : ℕ}
    {p : Program} {memP : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {stP : State} {ω : ℕ → Bool}
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (hG_P : GraphAt memP gA G) (hΔ_m : memP (pA + 2) = Δ) (hL_m : memP (pA + 1) = L)
    (hreadG : readGraph memP gA = G) (hreadX : (readLenPrefixedList memP h0).toFinset = X)
    (hreadP : readMultiPairs memP pairsA = pairs)
    (hrcCost_le : routerCallCost G X pairs Δ L 100 z ≤ R1)
    (hsp_mono : outerRouterSpace C_sp G.n (routerCallCost G X pairs Δ L 100 z) ≤ outerRouterSpace C_sp G.n R1)
    (hPreRt : (multiPairRouterContract C_rt C_sp w).pre [gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt] memP)
    (hRt_eq : hRt = rtOutA + 2 + 2 * G.n)
    (hw_bnds : gA < 2 ^ w ∧ h0 < 2 ^ w ∧ pairsA < 2 ^ w ∧ pA + 2 < 2 ^ w ∧ Δ < 2 ^ w ∧
      L < 2 ^ w ∧ z < 2 ^ w ∧ hRt < 2 ^ w ∧ 128 < 2 ^ w)
    (hregs : stP.regs 1 = gA ∧ stP.regs 6 = z ∧ stP.regs 7 = pA ∧ stP.regs 11 = h0 ∧
      stP.regs 12 = rtOutA ∧ stP.regs 23 = pairsA)
    (hmemP : stP.mem = memP) :
    ∃ (hAfterRt : ℕ) (memR : ℕ → ℕ) (stR : State) (cR : ℕ),
      Runs w p ω (seqStmts [
        .assign 27 (.reg 12),
        .assign 28 (.load (.reg 1)),
        .assign 29 (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 28))),
        .assign 30 (.load (.bin .add (.reg 7) (.const 2))),
        .assign 31 (.load (.bin .add (.reg 7) (.const 1))),
        .call 12 bRoute [.reg 1, .reg 11, .reg 23, .reg 30, .reg 31, .const 100, .reg 6, .reg 27, .reg 29]])
        stP .normal stR cR ∧
      stR.mem = memR ∧ stR.regs 12 = hAfterRt ∧ stR.regs 27 = rtOutA ∧
      (∀ r < 27, r ≠ 12 → stR.regs r = stP.regs r) ∧
      RouteOutAt memR rtOutA (routeOrCut G X pairs Δ L 100 z) ∧
      hRt ≤ hAfterRt ∧ hAfterRt ≤ hRt + outerRouterSpace C_sp G.n R1 ∧
      ZeroFrom memR hAfterRt ∧
      (∀ a < hRt, (a < rtOutA ∨ rtOutA + 2 + 2 * G.n ≤ a) → memR a = memP a) ∧
      cR ≤ C_rt * R1 + C_rt + 50 := by
  rcases hw_bnds with ⟨hg_w, hh0_w, hp_w, hpA_w, hΔ_w, hL_w, hz_w, hRt_w, hw128⟩
  rcases hregs with ⟨hr1, hr6, hr7, hr11, hr12, hr23⟩
  have hrunR : ∃ o stR cR,
      Runs w p ω (seqStmts [
        .assign 27 (.reg 12),
        .assign 28 (.load (.reg 1)),
        .assign 29 (.bin .add (.bin .add (.reg 27) (.const 2)) (.bin .mul (.const 2) (.reg 28))),
        .assign 30 (.load (.bin .add (.reg 7) (.const 2))),
        .assign 31 (.load (.bin .add (.reg 7) (.const 1))),
        .call 12 bRoute [.reg 1, .reg 11, .reg 23, .reg 30, .reg 31, .const 100, .reg 6, .reg 27, .reg 29]])
        stP o stR cR ∧
      (normalPost fun stR =>
        stR.regs 27 = rtOutA ∧ (∀ r < 27, r ≠ 12 → stR.regs r = stP.regs r) ∧
        RouteOutAt stR.mem rtOutA (routeOrCut G X pairs Δ L 100 z) ∧
        hRt ≤ stR.regs 12 ∧ stR.regs 12 ≤ hRt + outerRouterSpace C_sp G.n R1 ∧
        ZeroFrom stR.mem (stR.regs 12) ∧
        (∀ a < hRt, (a < rtOutA ∨ rtOutA + 2 + 2 * G.n ≤ a) → stR.mem a = memP a)) o stR ∧
      cR ≤ C_rt * R1 + C_rt + 50 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := rtOutA) (Expr.eval_reg_of_eq hr12) ?_
    refine runs_seq_assign_le (v := G.n)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr1]))
        (hmemP ▸ graphAt_n hG_P)) ?_
    refine runs_seq_assign_le (v := hRt)
      (by rw [hRt_eq]; exact Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := Δ)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]))
        (Expr.eval_const (by omega)) (by omega)) (hmemP ▸ hΔ_m)) ?_
    refine runs_seq_assign_le (v := L)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]))
        (Expr.eval_const (by omega)) (by omega)) (hmemP ▸ hL_m)) ?_
    have hWords : ∀ v ∈ ([gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt] : List ℕ), v < 2 ^ w := by
      intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine runs_call_le hRoute (vs := [gA, h0, pairsA, Δ, L, 100, z, rtOutA, hRt]) (by
      have h100 : 100 < 2 ^ w := by omega
      simp only [evalArgs, Expr.eval, h100, ↓reduceIte]
      simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 31), Function.update_of_ne (by decide : (1 : ℕ) ≠ 30),
        Function.update_of_ne (by decide : (1 : ℕ) ≠ 29), Function.update_of_ne (by decide : (1 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (1 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 31), Function.update_of_ne (by decide : (11 : ℕ) ≠ 30),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 29), Function.update_of_ne (by decide : (11 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (23 : ℕ) ≠ 31), Function.update_of_ne (by decide : (23 : ℕ) ≠ 30),
        Function.update_of_ne (by decide : (23 : ℕ) ≠ 29), Function.update_of_ne (by decide : (23 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (23 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (30 : ℕ) ≠ 31),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 31), Function.update_of_ne (by decide : (6 : ℕ) ≠ 30),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 29), Function.update_of_ne (by decide : (6 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (6 : ℕ) ≠ 27),
        Function.update_of_ne (by decide : (27 : ℕ) ≠ 31), Function.update_of_ne (by decide : (27 : ℕ) ≠ 30),
        Function.update_of_ne (by decide : (27 : ℕ) ≠ 29), Function.update_of_ne (by decide : (27 : ℕ) ≠ 28),
        Function.update_of_ne (by decide : (29 : ℕ) ≠ 31), Function.update_of_ne (by decide : (29 : ℕ) ≠ 30),
        Function.update_self, hr1, hr11, hr23, hr6]) hWords (hmemP ▸ hPreRt) ?_ (by
      simp only [argsSize, Expr.size, multiPairRouterContract, List.getD_cons_zero, List.getD_cons_succ,
        hmemP, hreadG, hreadX, hreadP]
      have := Nat.mul_le_mul_left C_rt hrcCost_le; omega)
    intro v memR _ hpostR
    simp only [multiPairRouterContract, List.getD_cons_zero, List.getD_cons_succ,
      hmemP, hreadG, hreadX, hreadP] at hpostR
    rcases hpostR with ⟨hRout, hv1, hv2, hzfR, hfrR⟩
    refine ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self],
      fun r hr hne => by
        dsimp only
        rw [Function.update_of_ne hne, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
      hRout, by simp [hv1], by simp; exact le_trans hv2 (by omega), by simpa using hzfR, hfrR⟩
  rcases hrunR with ⟨o, stR, cR, hrR, hpR, hcR⟩
  cases o with
  | returned _ => exact False.elim hpR
  | normal =>
    rcases hpR with ⟨h27, hlt27, hRout, h12ge, h12le, hzfR, hfrR⟩
    exact ⟨stR.regs 12, stR.mem, stR, cR, hrR, rfl, rfl, h27, hlt27, hRout, h12ge, h12le, hzfR, hfrR, hcR⟩

/-! ## 3. Zero-Cut-Blocks Post-Query Branch (`sbOneRound_afterQuery_zero`) -/

/-- Handles the `cutIds.length = 0` branch of `sbOneRoundAfterQueryStmt bRoute` (no router call). -/
theorem sbOneRound_afterQuery_zero {cfg : ParamConfig} {M r q w bRoute C_rt C_sp Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 hRound cutRecsA pairsA tmpA hSub0 m : ℕ}
    {p : Program} {mem0 memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {stQ : State} {ω : ℕ → Bool}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hm_le : m ≤ 49 * LParam M)
    (hmod : SbModelInv (coreParamsOf cfg M r) q G X (X.sort (· ≤ ·)) b nBlocks z m bst)
    (hpers : SbPersistAt memStart G X b nBlocks (LParam M) h0 bst)
    (hF_at0 : EdgesAt memStart fA (callsFakeEdges bst.calls))
    (hfr0 : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) →
      (a < fA ∨ fA + 2 * k ≤ a) → (a < outA ∨ outA + 2 + k ≤ a) → memStart a = mem0 a)
    (hgeom : locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ DisjointRange locA G.n fA (2 * k))
    (hlay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ hRound ∧
      hRound ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist +
        m * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks ∧
      cutRecsA = hRound ∧ pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧ hSub0 = tmpA + 4 * b + 2 + b ∧
      hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w ∧
      128 < 2 ^ w)
    (hInvQ : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst nBlocks res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists stQ)
    (hr14Q : stQ.regs 14 = (callsFakeEdges bst.calls).length)
    (hr15Q : stQ.regs 15 = m)
    (ht0 : cutIds.length = 0) :
    ∃ st' cost,
      Runs w p ω (sbOneRoundAfterQueryStmt bRoute) stQ .normal st' cost ∧
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X (m + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (m + 1), pos := st'.pos } ∧
      st'.regs 15 = m ∧
      cost ≤ C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt + 350 * k + 360 * nBlocks + 340 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
  rcases hgeom with ⟨hloc_h, hf_h, hd_lf⟩
  rcases hlay with ⟨hhP_le, hhR_le, hcut_eq, hpairs_eq, htmp_eq, hhSub_eq, hStep_w, hw16⟩
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_pos : 0 < b := by have := harith.2.2.1; omega
  have hb_even : Even b := harith.2.2.2.1
  have hXL : X.card < 2 ^ cp.L := by rw [← hX_at.1]; exact harith.2.2.2.2.2.2.2.2
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b; rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hsub0_bound : hSub0 ≤ hRound + 6 * k + 5 * nBlocks + 3 := by
    have hmul : nBlocks * (2 + b) = 2 * nBlocks + nBlocks * b := by ring
    omega
  have hstep_def : sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks =
      nBlocks * Sprev + outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
      6 * k + 6 * nBlocks + 2 * G.n + 10 := rfl
  have hQ12_step : stQ.regs 12 ≤ hRound + sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks := by
    have := hInvQ.h_le; omega
  have hstep_mod := sbModelInv_round_step hcfg hX_sub hGloop hdegG hXL
    (Finset.sort_nodup X (· ≤ ·)) (by ext u; simp) hb_pos hb_even
    (hnb_eq ▸ hmod) res (fun i hi hact => hInvQ.res_spec i (hnb_eq.symm ▸ hi) hact)
  dsimp only at hstep_mod
  set rpairs : List (ℕ × (Finset ℕ × Finset ℕ)) := (List.range nBlocks).filterMap fun i =>
    if bst.active i then match res i with
      | .expander _ => none
      | .cut U => let B := blockSet vs b i; let C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
    else none
  have hfs := sb_rpairs_fst_snd (nBlocks := nBlocks) (b := b) (vs := vs) (bst := bst) (res := res)
  have hpairs_rp : pairs = rpairs.map Prod.snd := hInvQ.pairs_eq.trans hfs.2.symm
  let memP := Function.update stQ.mem pairsA 0
  let stP : State := { mem := memP, regs := stQ.regs, pos := stQ.pos }
  have hstoreP : Runs w p ω (.store (.reg 23) (.reg 25)) stQ .normal stP
      (Expr.size (.reg 23) + Expr.size (.reg 25) + 1) :=
    runs_store_n (Expr.eval_reg_of_eq hInvQ.r23) (Expr.eval_reg_of_eq (hInvQ.r25.trans ht0))
  have hfrP_below : ∀ a < ps.wRelA, (a < locA ∨ locA + G.n ≤ a) →
      (a < ps.actA ∨ ps.wBaseA ≤ a) → memP a = memStart a := fun a ha h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_persist a ha h1 h2
  have hfrP_w : ∀ a, ps.wBaseA ≤ a → a < ps.wRelA → memP a = memStart a := fun a h1 h2 => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.frame_w a h1 h2
  have hlocP : ∀ u < G.n, memP (locA + u) = 0 := fun u hu => by
    dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.loc0 u hu
  have hzfP : ZeroFrom memP (stQ.regs 12) := fun a ha => by
    have := hInvQ.h_ge; dsimp only [memP]; rw [Function.update_of_ne (by omega)]; exact hInvQ.zf a ha
  have hpairs_nil : pairs = [] := List.eq_nil_of_length_eq_zero (by rw [hInvQ.lens_eq.2.2.2.2]; exact ht0)
  have hcut_nil : cutIds = [] := List.eq_nil_of_length_eq_zero ht0
  have hstep_rc := hstep_mod.2.2
  split at hstep_rc
  · next U hrt =>
    have hrc_nil : routeOrCut G X pairs cp.Δ cp.L 100 z = .matched [] (fun _ => []) := by
      rw [hpairs_nil]; simp [routeOrCut, routeOrCutRaw, totalDemand]
    have heq : routeOrCut G X pairs cp.Δ cp.L 100 z = .cut U := by
      rw [← hrt]; congr 1; rw [hpairs_rp, ← hnb_eq]; rfl
    rw [hrc_nil] at heq; cases heq
  · next matchings emb hrt =>
    rcases hstep_rc with ⟨hmod', _⟩
    have hcalls_nil : ∀ (ps1 : List (Finset ℕ × Finset ℕ)) (c : RoutedCall), ps1 = [] →
        (if ps1.isEmpty then bst.calls else bst.calls ++ [c]) = bst.calls := by
      rintro _ _ rfl; rfl
    have hpm_nil_nb : ∀ (f : ℕ → Option (ℕ × (Finset ℕ × Finset ℕ))),
        (∀ i, f i = if bst.active i = true then match res i with
          | .expander _ => none
          | .cut U => have B := blockSet (X.sort (· ≤ ·)) b i; have C' := padToHalf B (smallerSide B U); some (i, (C', B \ C'))
          else none) →
        List.map Prod.snd ((List.range nBlocks).filterMap f) = [] := by
      intro f hf
      rw [← hpairs_nil, hpairs_rp]; congr 2; funext i; exact hf i
    have hcond_t : (.bin .eq (.reg 25) (.const 0) : Expr).eval w stP = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (hInvQ.r25.trans ht0)) (Expr.eval_const (by omega)) rfl (by omega)
    have hrun : Runs w p ω (sbOneRoundAfterQueryStmt bRoute) stQ .normal stP _ :=
      runs_seq_n hstoreP (runs_cond_t hcond_t (by decide) runs_nop_n)
    have hno_cut : ∀ i < nBlocks, bst.active i = true → ∀ U, res i ≠ .cut U := by
      intro i hi hact U hU
      have hmem : i ∈ cutIds := by
        rw [hInvQ.cutIds_eq, List.mem_filterMap]
        exact ⟨i, List.mem_range.mpr hi, by simp [hact, hU]⟩
      rw [hcut_nil] at hmem; simp at hmem
    refine ⟨stP, _, hrun, ?_, hr15Q, by simp only [Expr.size]; omega⟩
    refine ⟨sbArgs_of_eq hInvQ.args (fun r hr => by dsimp only [stP]; rw [Function.update_of_ne (by omega)]),
      by simp, hlocP,
      by dsimp only [stP]; rw [Function.update_of_ne (by decide), hps_id]; have := hInvQ.h_ge; omega,
      by dsimp only [stP]; rw [Function.update_of_ne (by decide), hps_id]; rw [Nat.succ_mul]; omega,
      by dsimp only [stP]; rw [Function.update_of_ne (by decide)]; exact hzfP,
      fun a ha h1 h2 h3 => (hfrP_below a (by omega) h1 (Or.inl (by omega))).trans (hfr0 a ha h1 h2 h3),
      Or.inr ⟨by dsimp only [stP]; rw [Function.update_of_ne (by decide), hInvQ.r13], _, hnb_eq.symm ▸ hmod',
        ?_,
        by dsimp only [stP]; rw [Function.update_of_ne (by decide), hr14Q]
           congr 2; apply Eq.symm; apply hcalls_nil
           apply hpm_nil_nb; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl,
        by dsimp only [stP]
           have hlen_lt : (callsFakeEdges bst.calls).length ≤ k :=
             sb_callsFakeEdges_length_le_k hcfg (by omega) hqr hz_eq
               (hmod.calls_len.trans (by show m ≤ 49 * LParam M + 2; omega)) hmod.calls_valid
           have hF_P : EdgesAt memP fA (callsFakeEdges bst.calls) := fun idx hidx => by
             have h1 : fA + 2 * idx < locA ∨ locA + G.n ≤ fA + 2 * idx := by rcases hd_lf with h | h <;> [right; left] <;> omega
             have h2 : fA + 2 * idx + 1 < locA ∨ locA + G.n ≤ fA + 2 * idx + 1 := by rcases hd_lf with h | h <;> [right; left] <;> omega
             rw [hfrP_below _ (by omega) h1 (Or.inl (by omega)), hfrP_below _ (by omega) h2 (Or.inl (by omega))]
             exact hF_at0 idx hidx
           convert hF_P using 2; apply hcalls_nil
           apply hpm_nil_nb; intro i; by_cases h1 : bst.active i = true <;> simp [h1]; cases res i <;> rfl⟩⟩
    refine ⟨⟨(hfrP_below h0 (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans hpers.xLen_at.1,
        fun idx hidx => by
          have hidx' : idx < k := by rw [Finset.length_sort, ← hX_at.1] at hidx; exact hidx
          exact (hfrP_below (h0 + 1 + idx) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (hpers.xLen_at.2 idx hidx)⟩,
      fun i hi => by
        dsimp only [stP, memP]; rw [← hX_at.1, hps_id, Function.update_of_ne (by omega)]
        have haQ := hInvQ.act_mem i hi; dsimp only at haQ; rw [hps_id] at haQ
        rw [haQ]; simp only [hi, true_and]
        cases hact : bst.active i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        cases hri : res i with
        | expander S => rfl
        | cut U => exact absurd hri (hno_cut i hi hact U),
      fun i hi _ => by
        dsimp only [stP, memP]; rw [← hX_at.1, hps_id]
        have hsaved := hInvQ.saved_mem i hi; dsimp only at hsaved; rw [hps_id] at hsaved
        have hib : (i + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); rw [Nat.succ_mul] at hib
        have hBi_card : (blockSet (X.sort (· ≤ ·)) b i).card = b :=
          card_blockSet (Finset.sort_nodup X (· ≤ ·)) (by rw [← hnb_eq]; exact hi)
        cases hact : bst.active i with
        | false =>
          have h1 := hsaved.1 hact
          have hSL : ((bst.savedS i).sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card (hmod.inactive_exp i hi hact).1).trans (le_of_eq hBi_card)
          have hCL : ((blockSet (X.sort (· ≤ ·)) b i \ bst.savedS i).sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
          simp only [Bool.false_eq_true, and_false, ite_false]
          exact ⟨by rw [Function.update_of_ne (by omega)]; exact h1.1,
            by rw [Function.update_of_ne (by omega)]; exact h1.2.1,
            fun idx hidx => by rw [Function.update_of_ne (by omega)]; exact h1.2.2.1 idx hidx,
            fun idx hidx => by rw [Function.update_of_ne (by omega)]; exact h1.2.2.2 idx hidx⟩
        | true =>
          cases hri : res i with
          | cut U => exact absurd hri (hno_cut i hi hact U)
          | expander S =>
            have h1 := hsaved.2 hi hact S hri
            have hSp := hInvQ.res_spec i hi hact; rw [hri] at hSp
            have hSL : (S.sort (· ≤ ·)).length ≤ b := by
              rw [Finset.length_sort]; exact (Finset.card_le_card hSp.1).trans (le_of_eq hBi_card)
            have hCL : ((blockSet (X.sort (· ≤ ·)) b i \ S).sort (· ≤ ·)).length ≤ b := by
              rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
            simp only [hi, and_self, ite_true]
            exact ⟨by rw [Function.update_of_ne (by omega)]; exact h1.1,
              by rw [Function.update_of_ne (by omega)]; exact h1.2.1,
              fun idx hidx => by rw [Function.update_of_ne (by omega)]; exact h1.2.2.1 idx hidx,
              fun idx hidx => by rw [Function.update_of_ne (by omega)]; exact h1.2.2.2 idx hidx⟩,
      fun i hi => by
        dsimp only [stP]; rw [← hX_at.1, hps_id]
        have hWlen : 2 + 2 * (witnessEdges (bst.rounds i) (bst.numRounds i)).length ≤ ps.wStride := by
          rw [witnessEdges_length (hmod.rounds_len i hi)]
          have h1 : bst.numRounds i * (b / 2) ≤ (49 * LParam M + 1) * (b / 2) :=
            Nat.mul_le_mul_right _ ((hmod.numRounds_le i hi).trans (by omega))
          have h2 : ps.wStride = 2 + 2 * ((49 * LParam M + 1) * (b / 2)) := by dsimp only [ps, sbPersist]; ring
          omega
        have hiw : (i + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); rw [Nat.succ_mul] at hiw
        have hW0 := hpers.w_at i hi; dsimp only at hW0; rw [← hX_at.1, hps_id] at hW0
        have hW_P : GraphAt memP (ps.wBaseA + i * ps.wStride)
            (Graph.mk G.n (witnessEdges (bst.rounds i) (bst.numRounds i))) := by
          rw [graphAt_mk_iff] at hW0 ⊢
          exact ⟨(hfrP_w _ (by omega) (by omega)).trans hW0.1,
            (hfrP_w _ (by omega) (by omega)).trans hW0.2.1,
            fun idx hidx => ⟨(hfrP_w _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).1,
              (hfrP_w _ (by omega) (by omega)).trans (hW0.2.2 idx hidx).2⟩⟩
        convert hW_P using 2
        cases hact : bst.active i with
        | false => simp
        | true =>
          cases hri : res i with
          | expander S => simp [hi]
          | cut U => exact absurd hri (hno_cut i hi hact U),
      fun idx hidx => by
        have hidx' : idx < b := by simpa using hidx
        dsimp only [stP]; rw [← hX_at.1, hps_id, hfrP_w _ (by omega) (by omega)]
        have := hpers.rangeB_at; rw [← hX_at.1, hps_id] at this; exact this idx hidx⟩

end MinCostFlow.ExpanderDecomp
