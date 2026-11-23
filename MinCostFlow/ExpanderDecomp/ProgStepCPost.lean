module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCColor

import Mathlib.Tactic.Linarith

/-!
# Step C Post-Router Handler and Loop Invariant (`ProgStepCPost`)

Implements and verifies `scOneColorStmt bRoute`, one colour iteration `c ∈ {0, …, 16}` of
`stepCMacroLoop` (`OneShot.lean`), using `multiPairRouterContract` (`ProgStepCSpec.lean`),
`scExtractColorStmt` and `scBuildPairsStmt` (`ProgStepCExtract.lean`), `scMatchedPostStmt`
(`ProgStepCColor.lean`), and `scCopyCutStmt` (`ProgStepCBase.lean`).

Main results:
- `scOneColorStmt` / `scOneColorStmt_noRand`
- `ScArgs`, `ScLoopInv`, `scColorStepCost`
- `scOneColor_afterRoute`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Single-Colour Statement (`NoRand`) -/

/-- Execute one colour `c` (`r15`) of `stepCMacroLoop`, updating `r12` (`hCur`), `r13` (`isCut`),
and `r14` (`fakeM`). Input arguments remain read-only in `r0..r11`. -/
def scOneColorStmt (bRoute : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 13) (.const 0))
    (seqStmts [
      .assign 16 (.reg 12),
      scExtractColorStmt,
      .cond (.bin .eq (.reg 17) (.const 0))
        .nop
        (seqStmts [
          .assign 18 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))),
          scBuildPairsStmt,
          .assign 20 (.load (.reg 0)),
          .assign 21 (.bin .add (.bin .add (.reg 19) (.const 2)) (.bin .mul (.const 2) (.reg 20))),
          .call 12 bRoute [.reg 0, .reg 1, .reg 18, .reg 5, .reg 6, .const 100, .reg 4, .reg 19, .reg 21],
          .cond (.bin .eq (.load (.reg 19)) (.const 1))
            (seqStmts [
              scCopyCutStmt 19 10 22 23 24,
              .assign 13 (.const 1)
            ])
            scMatchedPostStmt
        ])
    ])
    .nop

theorem scOneColorStmt_noRand (bRoute : ℕ) : (scOneColorStmt bRoute).NoRand := by
  simp [scOneColorStmt, scExtractColorStmt, scBuildPairsStmt, scCopyCutStmt,
    scMatchedPostStmt, scSetMatchedStmt, scCompleteFakeLoopStmt, scCollectUnmatchedStmt,
    scZipAppendStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. Prefix Helpers and Loop Invariant -/

lemma stepCMacroLoop_fakes_len_le (cfg : CoreParams) (G : Graph) (vs : List ℕ)
    (b k z : ℕ) (hvs_nd : vs.Nodup) (hb : 0 < b) (hk : k = numFullBlocks vs b)
    (colored : List ((ℕ × ℕ) × ℕ))
    (hEc_v : ∀ c, ∀ e ∈ colorClass colored c, e.1 < k ∧ e.2 < k)
    (hEc_nd : ∀ c, (colorClass colored c |>.flatMap fun e => [e.1, e.2]).Nodup)
    (m : ℕ) :
    match stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored m with
    | Sum.inl _ => True
    | Sum.inr (cs, _) => (callsFakeEdges cs).length ≤ m * vs.length := by
  induction m with
  | zero => simp [stepCMacroLoop, callsFakeEdges]
  | succ m ih =>
    unfold stepCMacroLoop
    cases hprev : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored m with
    | inl U => trivial
    | inr cm =>
      rcases cm with ⟨cs, ms⟩
      rw [hprev] at ih
      dsimp only at ih ⊢
      unfold stepCMacroColor
      set Ec := colorClass colored m
      by_cases hemp : Ec.isEmpty = true
      · simp only [hemp, ↓reduceIte, List.append_nil]
        have h1 : m * vs.length ≤ (m + 1) * vs.length := Nat.mul_le_mul_right _ (Nat.le_succ m)
        omega
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        set pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
        have hvtp : ValidTerminalPairs vs.toFinset pairs :=
          validTerminalPairs_of_matching_edges hvs_nd hb (hk ▸ hEc_v m) (hEc_nd m)
        cases hrt : routeOrCut G vs.toFinset pairs cfg.Δ cfg.L 100 z with
        | cut U => trivial
        | matched matchings emb =>
          dsimp only
          have hfk := completeBatchFake_length_le_card (matchings := matchings) hvtp
          have hcard : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
          have hlen_app : (callsFakeEdges (cs ++ [⟨matchings.flatten, emb,
              completeBatchFake pairs matchings⟩])).length =
              (callsFakeEdges cs).length + (completeBatchFake pairs matchings).length := by
            simp [callsFakeEdges]
          have hmul : (m + 1) * vs.length = m * vs.length + vs.length := by ring
          omega

lemma stepCMacroLoopCost_mono (cfg : CoreParams) (G : Graph) (vs : List ℕ)
    (b z : ℕ) (colored : List ((ℕ × ℕ) × ℕ)) {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) :
    stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored m₁ ≤
      stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored m₂ := by
  induction hle with
  | refl => exact le_rfl
  | @step m _ ih =>
    simp only [stepCMacroLoopCost]
    exact le_trans ih (Nat.le_add_right _ _)

lemma stepCSpace_step_bound (C_sp n xLen k loopC costM : ℕ) (hle : loopC ≤ costM) :
    17 * (C_sp * ((n + 3) ^ 4 + 1) + 20 * (xLen + k + 1) + 2 * n + 10) + C_sp * loopC ≤
      stepCSpace C_sp n xLen k costM := by
  unfold stepCSpace
  have hpow : (n + 3) ^ 4 = n ^ 4 + 12 * n ^ 3 + 54 * n ^ 2 + 108 * n + 81 := by ring
  have h1 : 81 ≤ (n + 3) ^ 4 := by omega
  have h2 : 34 * n ≤ (n + 3) ^ 4 := by omega
  have h3 : 17 * ((n + 3) ^ 4 + 1) ≤ 20 * (n + 3) ^ 4 := by omega
  have h4 : C_sp * (17 * ((n + 3) ^ 4 + 1)) ≤ C_sp * (20 * (n + 3) ^ 4) := Nat.mul_le_mul_left C_sp h3
  have hmul1 : C_sp * loopC ≤ (C_sp + 1) * costM := Nat.mul_le_mul (Nat.le_succ C_sp) hle
  have hmul2 : 17 * (C_sp * ((n + 3) ^ 4 + 1)) + 34 * n + 170 ≤ (C_sp + 1) * (20 * (n + 3) ^ 4) := by
    have ha : (C_sp + 1) * (20 * (n + 3) ^ 4) = C_sp * (20 * (n + 3) ^ 4) + 20 * (n + 3) ^ 4 := by ring
    have hb : 17 * (C_sp * ((n + 3) ^ 4 + 1)) = C_sp * (17 * ((n + 3) ^ 4 + 1)) := by ring
    omega
  have hmul3 : 17 * (20 * (xLen + k + 1)) ≤ (C_sp + 1) * (400 * (xLen + k + 1)) := by
    have ha : (C_sp + 1) * (400 * (xLen + k + 1)) = C_sp * (400 * (xLen + k + 1)) + 400 * (xLen + k + 1) := by ring
    have hb : 17 * (20 * (xLen + k + 1)) ≤ 400 * (xLen + k + 1) := by omega
    omega
  have hexp : (C_sp + 1) * (costM + 20 * (n + 3) ^ 4 + 400 * (xLen + k + 1)) =
      (C_sp + 1) * costM + (C_sp + 1) * (20 * (n + 3) ^ 4) + (C_sp + 1) * (400 * (xLen + k + 1)) := by ring
  have hlhs : 17 * (C_sp * ((n + 3) ^ 4 + 1) + 20 * (xLen + k + 1) + 2 * n + 10) =
      17 * (C_sp * ((n + 3) ^ 4 + 1)) + 34 * n + 170 + 17 * (20 * (xLen + k + 1)) := by ring
  omega

/-- Register bundle keeping the 12 read-only arguments of `stepCProc` in `r0..r11`. -/
structure ScArgs (gA xA b k z Δ L colM colA locA outA h0 : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = gA
  r1 : st.regs 1 = xA
  r2 : st.regs 2 = b
  r3 : st.regs 3 = k
  r4 : st.regs 4 = z
  r5 : st.regs 5 = Δ
  r6 : st.regs 6 = L
  r7 : st.regs 7 = colM
  r8 : st.regs 8 = colA
  r9 : st.regs 9 = locA
  r10 : st.regs 10 = outA
  r11 : st.regs 11 = h0

lemma scArgs_of_eq {gA xA b k z Δ L colM colA locA outA h0 : ℕ} {st st' : State}
    (ha : ScArgs gA xA b k z Δ L colM colA locA outA h0 st)
    (heq : ∀ r < 12, st'.regs r = st.regs r) :
    ScArgs gA xA b k z Δ L colM colA locA outA h0 st' where
  r0 := (heq 0 (by decide)).trans ha.r0
  r1 := (heq 1 (by decide)).trans ha.r1
  r2 := (heq 2 (by decide)).trans ha.r2
  r3 := (heq 3 (by decide)).trans ha.r3
  r4 := (heq 4 (by decide)).trans ha.r4
  r5 := (heq 5 (by decide)).trans ha.r5
  r6 := (heq 6 (by decide)).trans ha.r6
  r7 := (heq 7 (by decide)).trans ha.r7
  r8 := (heq 8 (by decide)).trans ha.r8
  r9 := (heq 9 (by decide)).trans ha.r9
  r10 := (heq 10 (by decide)).trans ha.r10
  r11 := (heq 11 (by decide)).trans ha.r11

/-- State invariant after processing colours `0, …, m - 1` (`m ≤ 17`). -/
structure ScLoopInv (cfg : CoreParams) (cloud : ℕ → Graph) (C_sp : ℕ)
    (gA xA b k z colM colA locA outA h0 : ℕ) (mem0 : ℕ → ℕ) (G : Graph) (vs : List ℕ)
    (m : ℕ) (st : State) : Prop where
  args : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st
  rc : st.regs 15 = m
  loc0 : ∀ u < G.n, st.mem (locA + u) = 0
  h_ge : h0 ≤ st.regs 12
  h_le : st.regs 12 ≤ h0 + m * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
      C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z
        (edgeColor17 (cloud k)) m
  zf : ZeroFrom st.mem (st.regs 12)
  frame : ∀ a < h0, (a < locA ∨ locA + G.n ≤ a) →
      (a < outA ∨ outA + stepCOutSize vs.length ≤ a) → st.mem a = mem0 a
  out_match : match stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z (edgeColor17 (cloud k)) m with
    | Sum.inl U =>
        st.regs 13 = 1 ∧
        st.mem outA = 1 ∧
        ∃ U_list : List ℕ, U_list.Nodup ∧ U_list.toFinset = U ∧
          st.mem (outA + 1) = U_list.length ∧ ListAt st.mem (outA + 2) U_list
    | Sum.inr (cs, _) =>
        st.regs 13 = 0 ∧
        st.regs 14 = (callsFakeEdges cs).length ∧
        EdgesAt st.mem (outA + 2) (callsFakeEdges cs)

/-- Cost step per colour `c` in `scOneColorStmt`. -/
def scColorStepCost (cfg : CoreParams) (cloud : ℕ → Graph) (C_rt : ℕ)
    (G : Graph) (vs : List ℕ) (b k z c : ℕ) : ℕ :=
  match stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z (edgeColor17 (cloud k)) c with
  | Sum.inl _ => 20
  | Sum.inr _ =>
      let Ec := colorClass (edgeColor17 (cloud k)) c
      if Ec.isEmpty then
        380 * k + 80
      else
        let pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
        C_rt * routerCallCost G vs.toFinset pairs cfg.Δ cfg.L 100 z + C_rt +
          380 * vs.length + 720 * k + 350

/-! ## 3. Post-Router Execution Lemma and Single-Colour Execution Lemma -/

/-- Post-router branch of `scOneColorStmt`: handles `.cut U` (copying to `outA` and setting
`r13 := 1`) and `.matched matchings emb` (running `scMatchedPostStmt`), returning the updated
`ScLoopInv` for `c + 1`. -/
lemma scOneColor_afterRoute {cfg : CoreParams} {cloud : ℕ → Graph}
    {w C_sp gA xA b k z colM colA locA outA h0 c hCur pEnd hRt hAfterRt : ℕ}
    {p : Program} {mem0 mem4 mem5 : ℕ → ℕ} {G : Graph} {vs : List ℕ}
    {cs : List RoutedCall} {ms : List (List (ℕ × ℕ))} {st st5 : State} {ω : ℕ → Bool}
    (hvs_s : vs.Pairwise (· < ·))
    (hvs_sub : vs.toFinset ⊆ Finset.range G.n)
    (hGloop : ∀ ed ∈ G.inside vs.toFinset, ed.1 ≠ ed.2)
    (hΔ : 1 ≤ cfg.Δ) (hdegG : ∀ v ∈ vs.toFinset, G.degIn vs.toFinset v ≤ cfg.Δ)
    (hL : 1 ≤ cfg.L) (hvsL : vs.length < 2 ^ cfg.L)
    (hb : 0 < b) (hk2 : 2 ≤ k) (hk_eq : k = numFullBlocks vs b)
    (hcn : (cloud k).n = k) (hcval : (cloud k).IsValid) (hcdeg : ∀ v < k, (cloud k).deg v ≤ 9)
    (hc_lt : c < 17)
    (hx_h : xA + 1 + vs.length ≤ h0) (hloc_h : locA + G.n ≤ h0)
    (hout_h : outA + stepCOutSize vs.length ≤ h0)
    (hdl_x : DisjointRange locA G.n xA (1 + vs.length))
    (hdl_o : DisjointRange locA G.n outA (stepCOutSize vs.length))
    (hdo_x : DisjointRange outA (stepCOutSize vs.length) xA (1 + vs.length))
    (h16 : 16 < 2 ^ w)
    (hInv : ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs c st)
    (hprev : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z (edgeColor17 (cloud k)) c = Sum.inr (cs, ms))
    (hE_cs : EdgesAt st.mem (outA + 2) (callsFakeEdges cs))
    (hvs_st : LenListAt st.mem xA vs)
    (hEc_ne : (colorClass (edgeColor17 (cloud k)) c).isEmpty = false)
    (hEc_4 : EdgesAt mem4 hCur (colorClass (edgeColor17 (cloud k)) c))
    (hRouteOut : RouteOutAt mem5 pEnd
      (routeOrCut G vs.toFinset
        ((colorClass (edgeColor17 (cloud k)) c).map fun e => (blockSet vs b e.1, blockSet vs b e.2))
        cfg.Δ cfg.L 100 z))
    (hh0_cur : h0 ≤ hCur)
    (hcur_pEnd : hCur + 2 * (colorClass (edgeColor17 (cloud k)) c).length ≤ pEnd)
    (hpEnd_hRt : pEnd + 2 + 2 * G.n = hRt)
    (hhRt_le_after : hRt ≤ hAfterRt)
    (hAfter_h_le : hAfterRt + 2 * b ≤
      h0 + (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
        C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) (c + 1))
    (hAfter_w : hAfterRt + 2 * b < 2 ^ w)
    (hzf_5 : ZeroFrom mem5 hAfterRt)
    (hfr_5 : ∀ a < hRt, (a < pEnd ∨ pEnd + 2 + 2 * G.n ≤ a) → mem5 a = mem4 a)
    (hmem5_lt_hCur : ∀ a < hCur, mem5 a = st.mem a)
    (hArgs5 : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st5)
    (hr12_5 : st5.regs 12 = hAfterRt) (hr13_5 : st5.regs 13 = 0)
    (hr14_5 : st5.regs 14 = (callsFakeEdges cs).length) (hr15_5 : st5.regs 15 = c)
    (hr16_5 : st5.regs 16 = hCur) (hr17_5 : st5.regs 17 = (colorClass (edgeColor17 (cloud k)) c).length)
    (hr19_5 : st5.regs 19 = pEnd) (hmem5 : st5.mem = mem5) :
    ∃ st' cost,
      Runs w p ω
        (.cond (.bin .eq (.load (.reg 19)) (.const 1))
          (seqStmts [scCopyCutStmt 19 10 22 23 24, .assign 13 (.const 1)])
          scMatchedPostStmt)
        st5 .normal st' cost ∧
      ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs (c + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (c + 1), pos := st'.pos } ∧
      st'.regs 15 = c ∧
      cost ≤ 248 * vs.length + 150 * k + 160 := by
  set colored := edgeColor17 (cloud k)
  set Ec := colorClass colored c
  set pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
  have hvs_nd : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  have hvs_card : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
  have hvs_lt : ∀ u ∈ vs, u < G.n := fun u hu => Finset.mem_range.mp (hvs_sub (List.mem_toFinset.mpr hu))
  have hvs_le_n : vs.length ≤ G.n := by
    have := Finset.card_le_card hvs_sub; rw [Finset.card_range, hvs_card] at this; exact this
  have hkb_le : k * b ≤ vs.length := hk_eq ▸ Nat.div_mul_le_self vs.length b
  have hEc_le_k : Ec.length ≤ k := colorClass_length_le hcn hcval hcdeg c
  have hEc_b_le : Ec.length * b ≤ vs.length := le_trans (Nat.mul_le_mul_right b hEc_le_k) hkb_le
  have hcol_spec := edgeColor17_spec hcval (fun v hv => hcdeg v (hcn ▸ hv))
  have hEc_v : ∀ c', ∀ e ∈ colorClass colored c', e.1 < k ∧ e.2 < k := by
    intro c' e he
    unfold colorClass at he
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
    have hin : ec.1 ∈ (removeLoops (cloud k)).edges := by
      rw [← hcol_spec.1]; exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
    have hv := removeLoops_isValid hcval ec.1 hin
    rwa [removeLoops_n, hcn] at hv
  have hvtp : ValidTerminalPairs vs.toFinset pairs :=
    validTerminalPairs_of_matching_edges hvs_nd hb (hk_eq ▸ hEc_v c) (hcol_spec.2.2.1 c)
  have hprev_fk_le : (callsFakeEdges cs).length ≤ c * vs.length := by
    have h := stepCMacroLoop_fakes_len_le cfg G vs b k z hvs_nd hb hk_eq colored hEc_v hcol_spec.2.2.1 c
    rw [hprev] at h; exact h
  have hspec_rt := routeOrCut_isMatchingPlayer.spec G vs.toFinset pairs cfg.Δ cfg.L 100 z
    hvs_sub hGloop hΔ hdegG hL (by rwa [hvs_card]) (by decide) hvtp
  have hout_h' : outA + 2 + 2 * (17 * vs.length) ≤ h0 := by
    have : outA + (2 + 34 * vs.length) ≤ h0 := hout_h; omega
  suffices h : ∃ o st' cost,
      Runs w p ω
        (.cond (.bin .eq (.load (.reg 19)) (.const 1))
          (seqStmts [scCopyCutStmt 19 10 22 23 24, .assign 13 (.const 1)])
          scMatchedPostStmt)
        st5 o st' cost ∧
      (o = .normal ∧
        ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs (c + 1)
          { mem := st'.mem, regs := Function.update st'.regs 15 (c + 1), pos := st'.pos } ∧
        st'.regs 15 = c) ∧
      cost ≤ 248 * vs.length + 150 * k + 160 by
    rcases h with ⟨o, st', cost, hr, ⟨rfl, hInv', hr15'⟩, hcost⟩
    exact ⟨st', cost, hr, hInv', hr15', hcost⟩
  refine runs_start_le ?_
  cases hrt : routeOrCut G vs.toFinset pairs cfg.Δ cfg.L 100 z with
  | cut U =>
    rw [hrt] at hRouteOut hspec_rt
    rcases hRouteOut with ⟨htag, U_list, hUnd, hUfin, hUlen, hUat⟩
    have hU_len_le : U_list.length ≤ vs.length := by
      have hc1 : U_list.length = U.card := by rw [← hUfin, List.toFinset_card_of_nodup hUnd]
      have hc2 : U.card ≤ vs.toFinset.card := Finset.card_le_card hspec_rt.1
      omega
    have hnext_loop : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored (c + 1) = Sum.inl U := by
      simp [stepCMacroLoop, hprev, stepCMacroColor, Ec, hEc_ne, pairs, hrt]
    refine runs_cond_le (v := 1)
      (by have he : Expr.eval w st5 (.bin .eq (.load (.reg 19)) (.const 1)) = some (if 1 = 1 then 1 else 0) :=
            Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr19_5) (hmem5 ▸ htag))
              (Expr.eval_const (by omega)) (by omega)
          simpa using he)
      (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only [seqStmts]
    refine runs_seq_triple_le
      (scCopyCut_triple (w := w) (cap := 2 + U_list.length) (srcA := pEnd) (dstA := outA)
        (rSrc := 19) (rDst := 10) (rLen := 22) (rI := 23) (rU := 24)
        (by decide) p mem5 U_list st5 hUlen hUat le_rfl
        (Or.inl (by omega)) (by omega) (by omega) h16 hr19_5 hArgs5.r10 hmem5) rfl ?_
    intro st6 ⟨hoth6, _, hfr6, hU_out0, hU_out1, hU_out_at⟩
    refine runs_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
      (by simp only [Expr.size]; omega)
    refine ⟨rfl, ?_, ?_⟩
    · refine ⟨scArgs_of_eq hArgs5 (fun r hr => by
          dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            hoth6 r (by omega) (by omega) (by omega)]),
        by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        have hdisj_lo : locA + u < outA ∨ outA + (2 + U_list.length) ≤ locA + u := by
          rcases hdl_o with h | h
          · left; omega
          · right; unfold stepCOutSize at h; omega
        rw [hfr6 (locA + u) hdisj_lo, hmem5_lt_hCur (locA + u) (by omega)]
        exact hInv.loc0 u hu
      · dsimp only
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          hoth6 12 (by decide) (by decide) (by decide), hr12_5]
        omega
      · dsimp only
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          hoth6 12 (by decide) (by decide) (by decide), hr12_5]
        exact le_trans (Nat.le_add_right _ _) hAfter_h_le
      · intro a ha
        dsimp only at ha
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          hoth6 12 (by decide) (by decide) (by decide), hr12_5] at ha
        rw [hfr6 a (Or.inr (by omega))]
        exact hzf_5 a ha
      · intro a ha_h ha_loc ha_out
        have ha_out2 : a < outA ∨ outA + (2 + U_list.length) ≤ a := by
          rcases ha_out with h | h
          · left; omega
          · right; unfold stepCOutSize at h; omega
        rw [hfr6 a ha_out2, hmem5_lt_hCur a (by omega)]
        exact hInv.frame a ha_h ha_loc ha_out
      · rw [hnext_loop]
        exact ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
          hU_out0, U_list, hUnd, hUfin, hU_out1, hU_out_at⟩
    · dsimp only; rw [Function.update_of_ne (by decide), hoth6 15 (by decide) (by decide) (by decide), hr15_5]
  | matched matchings emb =>
    rw [hrt] at hRouteOut hspec_rt
    rcases hRouteOut with ⟨htag, hmLen, hmAt⟩
    rcases hspec_rt with ⟨hmlen_p, hpm_p, _, _, _, _⟩
    have hmlen_ec : matchings.length = Ec.length := by simpa [pairs] using hmlen_p
    have hflat_b := matched_flatten_bounds hvtp hmlen_p hpm_p
    have hflat_len : matchings.flatten.length ≤ vs.length := by have := hflat_b.2; omega
    have hflat_lt : ∀ e ∈ matchings.flatten, e.1 < G.n ∧ e.2 < G.n := fun e he =>
      ⟨Finset.mem_range.mp (hvs_sub (hflat_b.1 e he).1),
       Finset.mem_range.mp (hvs_sub (hflat_b.1 e he).2)⟩
    have hfk_len_le : (completeBatchFake pairs matchings).length ≤ vs.length := by
      have h1 := completeBatchFake_length_le_card (matchings := matchings) hvtp; omega
    have hnext_loop : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored (c + 1) =
        Sum.inr (cs ++ [⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩],
          ms ++ List.zipWith (fun p M => M ++ completeMatchingFake p.1 p.2 M) pairs matchings) := by
      simp [stepCMacroLoop, hprev, stepCMacroColor, Ec, hEc_ne, pairs, hrt]
    refine runs_cond_le (v := 0)
      (by have he : Expr.eval w st5 (.bin .eq (.load (.reg 19)) (.const 1)) = some (if 0 = 1 then 1 else 0) :=
            Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr19_5) (hmem5 ▸ htag))
              (Expr.eval_const (by omega)) (by omega)
          simpa using he)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hvs_5 : LenListAt mem5 xA vs :=
      ⟨by rw [hmem5_lt_hCur _ (by omega)]; exact hvs_st.1,
       fun i hi => by rw [hmem5_lt_hCur _ (by omega)]; exact hvs_st.2 i hi⟩
    have hEc_5 : EdgesAt mem5 hCur Ec := fun j hj => by
      rw [hfr_5 _ (by omega) (Or.inl (by omega)), hfr_5 _ (by omega) (Or.inl (by omega))]
      exact hEc_4 j hj
    have hloc0_5 : ∀ u < G.n, mem5 (locA + u) = 0 := fun u hu => by
      rw [hmem5_lt_hCur _ (by omega)]; exact hInv.loc0 u hu
    have hprev_5 : EdgesAt mem5 (outA + 2) (callsFakeEdges cs) := fun j hj => by
      have hjc : j < 17 * vs.length := by
        have : c * vs.length ≤ 17 * vs.length := Nat.mul_le_mul_right _ (by omega)
        omega
      rw [hmem5_lt_hCur _ (by omega), hmem5_lt_hCur _ (by omega)]
      exact hE_cs j hj
    have hd_out_vs : DisjointRange (outA + 2) (2 * (17 * vs.length)) (xA + 1) vs.length := by
      rcases hdo_x with h | h
      · left; unfold stepCOutSize at h; omega
      · right; omega
    have hd_out_loc : DisjointRange (outA + 2) (2 * (17 * vs.length)) locA G.n := by
      rcases hdl_o with h | h
      · right; omega
      · left; unfold stepCOutSize at h; omega
    have hcap_ec : (callsFakeEdges cs).length + Ec.length * b ≤ 17 * vs.length := by
      have h1 : (c + 1) * vs.length ≤ 17 * vs.length := Nat.mul_le_mul_right _ (by omega)
      have h2 : (c + 1) * vs.length = c * vs.length + vs.length := by ring
      omega
    have hcap_fk' : (callsFakeEdges cs).length +
        (completeBatchFake (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)) matchings).length ≤
        17 * vs.length := by
      have h1 : (c + 1) * vs.length ≤ 17 * vs.length := Nat.mul_le_mul_right _ (by omega)
      have h2 : (c + 1) * vs.length = c * vs.length + vs.length := by ring
      change (callsFakeEdges cs).length + (completeBatchFake pairs matchings).length ≤ 17 * vs.length
      omega
    refine runs_triple_le
      (scMatchedPost_triple (hAfterRt := hAfterRt) (pEnd := pEnd) (cap := 17 * vs.length)
        p mem5 vs Ec matchings (callsFakeEdges cs) st5
        hvs_5 hvs_s hvs_lt rfl hEc_5 (hk_eq ▸ hEc_v c) (hcol_spec.2.2.1 c) hb hmlen_ec
        (fun j hj => by
          have h := hpm_p j (by simpa [pairs] using hj)
          simpa [pairs, IsPartialMatching] using h)
        hmLen hmAt hflat_lt hloc0_5 rfl hprev_5 hcap_ec hcap_fk'
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hd_out_vs hd_out_loc hdl_x (Or.inl (by omega))
        hAfter_w h16 hArgs5.r1 hArgs5.r2 hArgs5.r9 hArgs5.r10 hr12_5 hr14_5 hr16_5 hr17_5 hr19_5 hmem5)
      rfl ?_ (by simp only [Expr.size]; omega)
    rintro (_ | _) st6 hq
    · rcases hq with ⟨hr12_6, hr14_6, hoth6, _, hloc0_6, hfr6, hE6⟩
      refine ⟨rfl, ?_, (hoth6 15 (by decide) (by decide) (by decide)).trans hr15_5⟩
      refine ⟨scArgs_of_eq hArgs5 (fun r hr => by
          dsimp only; rw [Function.update_of_ne (by omega)]
          exact hoth6 r (by omega) (by omega) (by omega)),
        by simp, hloc0_6,
        by dsimp only; rw [Function.update_of_ne (by decide), hr12_6]; omega,
        by dsimp only; rw [Function.update_of_ne (by decide), hr12_6]; exact hAfter_h_le,
        ?_, ?_, ?_⟩
      · intro a ha
        dsimp only at ha; rw [Function.update_of_ne (by decide), hr12_6] at ha
        rw [hfr6 a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
        exact hzf_5 a (by omega)
      · intro a ha_h ha_loc ha_out
        have ha_out2 : a < outA + 2 ∨ outA + 2 + 2 * (17 * vs.length) ≤ a := by
          rcases ha_out with h | h
          · left; omega
          · right; unfold stepCOutSize at h; omega
        rw [hfr6 a ha_loc ha_out2 (Or.inl (by omega)), hmem5_lt_hCur a (by omega)]
        exact hInv.frame a ha_h ha_loc ha_out
      · rw [hnext_loop]
        refine ⟨by dsimp only; rw [Function.update_of_ne (by decide)]
                   exact (hoth6 13 (by decide) (by decide) (by decide)).trans hr13_5,
          by dsimp only; rw [Function.update_of_ne (by decide), hr14_6]; simp [callsFakeEdges, pairs], ?_⟩
        have hE_eq : callsFakeEdges (cs ++ [⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩]) =
            callsFakeEdges cs ++ completeBatchFake pairs matchings := by simp [callsFakeEdges]
        rw [hE_eq]; exact hE6
    · exact False.elim hq


end MinCostFlow.ExpanderDecomp
