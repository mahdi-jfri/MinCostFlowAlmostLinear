module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCPost

import Mathlib.Tactic.Linarith

/-!
# Step C Single-Colour Iteration (`ProgStepCOneColor`)

Verifies `scOneColorStmt bRoute` (`ProgStepCPost.lean`) on a single colour `c ∈ {0, …, 16}` of
`stepCMacroLoop` (`OneShot.lean`), chaining `scExtractColorStmt`, `scBuildPairsStmt`, the
multi-pair router call (`multiPairRouterContract`), and `scOneColor_afterRoute`.

Main result:
- `scOneColor_step`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Single-colour execution lemma for `scOneColorStmt bRoute` on colour `c < 17`. -/
theorem scOneColor_step {cfg : CoreParams} {cloud : ℕ → Graph}
    {w bRoute C_rt C_sp gA xA b k z colM colA locA outA h0 c : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {vs : List ℕ} {st : State} {ω : ℕ → Bool}
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (hGA : GraphAt mem0 gA G) (hGval : G.IsValid)
    (hvs_at : LenListAt mem0 xA vs) (hvs_s : vs.Pairwise (· < ·))
    (hvs_sub : vs.toFinset ⊆ Finset.range G.n)
    (hGloop : ∀ ed ∈ G.inside vs.toFinset, ed.1 ≠ ed.2)
    (hΔ : 1 ≤ cfg.Δ) (hdegG : ∀ v ∈ vs.toFinset, G.degIn vs.toFinset v ≤ cfg.Δ)
    (hL : 1 ≤ cfg.L) (hvsL : vs.length < 2 ^ cfg.L)
    (hb : 0 < b) (hk2 : 2 ≤ k) (hk_eq : k = numFullBlocks vs b)
    (hcn : (cloud k).n = k) (hcval : (cloud k).IsValid) (hcdeg : ∀ v < k, (cloud k).deg v ≤ 9)
    (hcolM : colM = (edgeColor17 (cloud k)).length)
    (hcol_at : ColoredEdgesAt mem0 colA (edgeColor17 (cloud k)))
    (hΔ_w : cfg.Δ < 2 ^ w) (hL_w : cfg.L < 2 ^ w) (hz_w : z < 2 ^ w)
    (hGm : G.m ≤ 2 * cfg.Δ * vs.length) (hzv : z ≤ vs.length)
    (hlay : StepCLayout w G.n G.m vs.length k colM gA xA colA locA outA h0 C_sp
      (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z))
    (hc_lt : c < 17)
    (hInv : ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs c st) :
    ∃ st' cost,
      Runs w p ω (scOneColorStmt bRoute) st .normal st' cost ∧
      ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs (c + 1)
        { mem := st'.mem, regs := Function.update st'.regs 15 (c + 1), pos := st'.pos } ∧
      st'.regs 15 = c ∧
      cost ≤ scColorStepCost cfg cloud C_rt G vs b k z c := by
  rcases hlay with ⟨hg_h, hx_h, hcol_h, hloc_h, hout_h, hdl_g, hdl_x, hdl_c, hdl_o,
    hdo_g, hdo_x, hdo_c, hsp_w, h16⟩
  have h100 : 100 < 2 ^ w := by
    have hsp_ge := stepCSpace_step_bound C_sp G.n vs.length k 0
      (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z) (Nat.zero_le _)
    omega
  set colored := edgeColor17 (cloud k)
  have hcolM_le : colM ≤ 5 * k := hcolM ▸ edgeColor17_length_le_five_mul hcn hcval hcdeg
  have hvs_nd : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  have hvs_card : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
  have hvs_lt : ∀ u ∈ vs, u < G.n := fun u hu => Finset.mem_range.mp (hvs_sub (List.mem_toFinset.mpr hu))
  have hkb_le : k * b ≤ vs.length := hk_eq ▸ Nat.div_mul_le_self vs.length b
  have h2b_le : 2 * b ≤ vs.length := by
    have : 2 * b ≤ k * b := Nat.mul_le_mul_right b hk2
    omega
  have hk_le_vs : k ≤ vs.length := by
    have : k * 1 ≤ k * b := Nat.mul_le_mul_left k hb
    omega
  have hcol_spec := edgeColor17_spec hcval (fun v hv => hcdeg v (hcn ▸ hv))
  have hEc_v : ∀ c', ∀ e ∈ colorClass colored c', e.1 < k ∧ e.2 < k := by
    intro c' e he
    unfold colorClass at he
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
    have hin : ec.1 ∈ (removeLoops (cloud k)).edges := by
      rw [← hcol_spec.1]; exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
    have hv := removeLoops_isValid hcval ec.1 hin
    rwa [removeLoops_n, hcn] at hv
  have hcostM_eq : stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z =
      (200 * k + 1) + stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored 17 := by
    simp [stepCMacroCost, hk2, colored]
  have hloop_c_le : stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1) ≤
      stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z := by
    have h1 := stepCMacroLoopCost_mono cfg G vs b z colored (by omega : c + 1 ≤ 17)
    rw [hcostM_eq]; omega
  have hGA_st : GraphAt st.mem gA G := by
    intro i hi
    have hlen_enc : G.encode.length = 2 + 2 * G.m := graph_encode_length G
    have h1 : gA + i < locA ∨ locA + G.n ≤ gA + i := by
      rcases hdl_g with h | h <;> [right; left] <;> omega
    have h2 : gA + i < outA ∨ outA + stepCOutSize vs.length ≤ gA + i := by
      rcases hdo_g with h | h <;> [right; left] <;> omega
    rw [hInv.frame (gA + i) (by omega) h1 h2]
    exact hGA i hi
  have hvs_st : LenListAt st.mem xA vs := by
    have hx_out : ∀ i < 1 + vs.length, st.mem (xA + i) = mem0 (xA + i) := by
      intro i hi
      have h1 : xA + i < locA ∨ locA + G.n ≤ xA + i := by
        rcases hdl_x with h | h <;> [right; left] <;> omega
      have h2 : xA + i < outA ∨ outA + stepCOutSize vs.length ≤ xA + i := by
        rcases hdo_x with h | h <;> [right; left] <;> omega
      exact hInv.frame (xA + i) (by omega) h1 h2
    exact ⟨by simpa using (hx_out 0 (by omega)).trans hvs_at.1,
      fun i hi => by
        have h : st.mem (xA + 1 + i) = mem0 (xA + 1 + i) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx_out (i + 1) (by omega)
        rw [h]; exact hvs_at.2 i hi⟩
  have hcol_st : ColoredEdgesAt st.mem colA colored := by
    intro j hj
    have hc_out : ∀ off < 3, st.mem (colA + 3 * j + off) = mem0 (colA + 3 * j + off) := by
      intro off hoff
      have h1 : colA + 3 * j + off < locA ∨ locA + G.n ≤ colA + 3 * j + off := by
        rcases hdl_c with h | h <;> [right; left] <;> omega
      have h2 : colA + 3 * j + off < outA ∨ outA + stepCOutSize vs.length ≤ colA + 3 * j + off := by
        rcases hdo_c with h | h <;> [right; left] <;> omega
      exact hInv.frame (colA + 3 * j + off) (by omega) h1 h2
    exact ⟨by simpa using (hc_out 0 (by omega)).trans (hcol_at j hj).1,
      (hc_out 1 (by omega)).trans (hcol_at j hj).2.1,
      (hc_out 2 (by omega)).trans (hcol_at j hj).2.2⟩
  -- Split on whether `stepCMacroLoop ... c` already cut or continued.
  cases hprev : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored c with
  | inl U =>
    have hout := hInv.out_match
    rw [hprev] at hout
    rcases hout with ⟨hr13, hm0, U_list, hUnd, hUfin, hUlen, hUat⟩
    have hstep_cost : scColorStepCost cfg cloud C_rt G vs b k z c = 20 := by
      simp [scColorStepCost, colored, hprev]
    have hnext_loop : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored (c + 1) = Sum.inl U := by
      simp [stepCMacroLoop, hprev]
    have hnext_cost : stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1) =
        stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c := by
      simp [stepCMacroLoopCost, hprev]
    suffices h : ∃ o st' cost, Runs w p ω (scOneColorStmt bRoute) st o st' cost ∧
        (o = .normal ∧ st' = st) ∧ cost ≤ 20 by
      rcases h with ⟨o, st', cost, hr, ⟨rfl, rfl⟩, hcost⟩
      refine ⟨st', cost, hr, ?_, hInv.rc, by rw [hstep_cost]; exact hcost⟩
      refine ⟨scArgs_of_eq hInv.args (fun r hr' => by dsimp only; rw [Function.update_of_ne (by omega)]),
        by simp, hInv.loc0, by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.h_ge,
        ?_, by dsimp only; rw [Function.update_of_ne (by decide)]; exact hInv.zf, hInv.frame, ?_⟩
      · dsimp only; rw [Function.update_of_ne (by decide)]
        have h1 : st'.regs 12 ≤ h0 + c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
            C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c := hInv.h_le
        have h2 : c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) ≤
            (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) :=
          Nat.mul_le_mul_right _ (Nat.le_succ c)
        change st'.regs 12 ≤ _ + C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1)
        rw [hnext_cost]; omega
      · rw [hnext_loop]
        exact ⟨by dsimp only; rw [Function.update_of_ne (by decide), hr13], hm0, U_list, hUnd, hUfin, hUlen, hUat⟩
    refine runs_start_le ?_
    dsimp only [scOneColorStmt]
    refine runs_cond_le (v := 0)
      (by have he : Expr.eval w st (.bin .eq (.reg 13) (.const 0)) = some (if 1 = 0 then 1 else 0) :=
            Expr.eval_eq_op (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) (by omega)
          simpa using he)
      (fun h => absurd rfl h) (fun _ => ?_)
    exact runs_nop_le ⟨rfl, rfl⟩ (by simp [Expr.size])
  | inr cm =>
    rcases cm with ⟨cs, ms⟩
    have hout := hInv.out_match
    rw [hprev] at hout
    rcases hout with ⟨hr13, hr14, hE_cs⟩
    set hCur := st.regs 12
    set Ec := colorClass colored c
    have hEc_le_k : Ec.length ≤ k := colorClass_length_le hcn hcval hcdeg c
    have hEc_b_le : Ec.length * b ≤ vs.length := by
      have h1 : Ec.length * b ≤ k * b := Nat.mul_le_mul_right b hEc_le_k
      omega
    have hprev_fk_le : (callsFakeEdges cs).length ≤ c * vs.length := by
      have h := stepCMacroLoop_fakes_len_le cfg G vs b k z hvs_nd hb hk_eq colored hEc_v hcol_spec.2.2.1 c
      rw [hprev] at h; exact h
    have hnext_cost_eq : stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1) =
        stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c +
          stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec := by
      simp [stepCMacroLoopCost, hprev, Ec]
    have hstep_headroom :
        hCur + (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
          C_sp * stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec < 2 ^ w := by
      have h1 : hCur ≤ h0 + c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
          C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c := hInv.h_le
      have h2 : (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) ≤
          17 * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) :=
        Nat.mul_le_mul_right _ (by omega)
      have h4 := stepCSpace_step_bound C_sp G.n vs.length k
        (stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1))
        (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z) hloop_c_le
      have h5 : C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c +
          C_sp * stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec =
          C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1) := by
        rw [hnext_cost_eq, Nat.mul_add]
      have h6 : (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) =
          c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
          (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) := by ring
      omega
    suffices h : ∃ o st' cost,
        Runs w p ω (scOneColorStmt bRoute) st o st' cost ∧
        (o = .normal ∧
          ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs (c + 1)
            { mem := st'.mem, regs := Function.update st'.regs 15 (c + 1), pos := st'.pos } ∧
          st'.regs 15 = c) ∧
        cost ≤ scColorStepCost cfg cloud C_rt G vs b k z c by
      rcases h with ⟨o, st', cost, hr, ⟨rfl, hInv', hr15'⟩, hcost⟩
      exact ⟨st', cost, hr, hInv', hr15', hcost⟩
    refine runs_start_le ?_
    dsimp only [scOneColorStmt]
    refine runs_cond_le (v := 1)
      (by have he : Expr.eval w st (.bin .eq (.reg 13) (.const 0)) = some (if 0 = 0 then 1 else 0) :=
            Expr.eval_eq_op (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) (by omega)
          simpa using he)
      (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only [seqStmts]
    refine runs_seq_assign_le (v := hCur) (Expr.eval_reg_of_eq (v := hCur) rfl) ?_
    let st1 : State := { mem := st.mem, regs := Function.update st.regs 16 hCur, pos := st.pos }
    refine runs_seq_triple_le
      (scExtractColor_triple (c := c) (ecA := hCur) p st.mem colored st1 hcolM.symm hcol_st
        (Or.inr (by have := hInv.h_ge; omega)) (by omega) (by omega) h16
        (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hInv.args.r7])
        (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hInv.args.r8])
        (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hInv.rc])
        (by dsimp only [st1]; rw [Function.update_self]) rfl) rfl ?_
    intro st2 ⟨hEc_r17, hoth2, _, hfr2, hEc_at⟩
    have hArgs2 : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st2 :=
      scArgs_of_eq hInv.args (fun r hr => by
        rw [hoth2 r (by omega) (by omega) (by omega) (by omega) (by omega)]
        dsimp only [st1]; rw [Function.update_of_ne (by omega)])
    have hr12_2 : st2.regs 12 = hCur := by
      rw [hoth2 12 (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide)]
    have hr13_2 : st2.regs 13 = 0 := by
      rw [hoth2 13 (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr13]
    have hr14_2 : st2.regs 14 = (callsFakeEdges cs).length := by
      rw [hoth2 14 (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr14]
    have hr15_2 : st2.regs 15 = c := by
      rw [hoth2 15 (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hInv.rc]
    have hr16_2 : st2.regs 16 = hCur := by
      rw [hoth2 16 (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_self]
    refine runs_cond_le (v := if Ec.length = 0 then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq hEc_r17) (Expr.eval_const (by omega)) (by omega))
      (fun hEc0_ne => ?_) (fun hEc0_0 => ?_)
    · -- Case 1: `Ec` is empty
      have hEc0 : Ec.length = 0 := by by_contra h; simp [h] at hEc0_ne
      have hEc_nil : Ec = [] := List.eq_nil_of_length_eq_zero hEc0
      have hstep_cost : scColorStepCost cfg cloud C_rt G vs b k z c = 380 * k + 80 := by
        simp [scColorStepCost, colored, hprev, Ec, hEc_nil]
      have hnext_loop : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z colored (c + 1) =
          Sum.inr (cs, ms) := by
        simp [stepCMacroLoop, hprev, stepCMacroColor, Ec, hEc_nil]
      refine runs_nop_le ?_ (by rw [hstep_cost]; simp only [Expr.size]; omega)
      refine ⟨rfl, ?_, hr15_2⟩
      have hmem2_eq : st2.mem = st.mem := by
        funext a; exact hfr2 a (by rw [hEc0]; omega)
      refine ⟨scArgs_of_eq hArgs2 (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]),
        by simp, by rw [hmem2_eq]; exact hInv.loc0,
        by dsimp only; rw [Function.update_of_ne (by decide), hr12_2]; exact hInv.h_ge,
        ?_, by dsimp only; rw [Function.update_of_ne (by decide), hr12_2, hmem2_eq]; exact hInv.zf,
        by rw [hmem2_eq]; exact hInv.frame, ?_⟩
      · dsimp only; rw [Function.update_of_ne (by decide), hr12_2]
        have h1 : hCur ≤ h0 + c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
            C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c := hInv.h_le
        have h2 : c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) ≤
            (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) :=
          Nat.mul_le_mul_right _ (Nat.le_succ c)
        change hCur ≤ h0 + (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
          C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1)
        rw [hnext_cost_eq, Nat.mul_add]
        have h3 : C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c ≤
            C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c +
              C_sp * stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec := Nat.le_add_right _ _
        linarith only [h1, h2, h3]
      · rw [hnext_loop]
        exact ⟨by dsimp only; rw [Function.update_of_ne (by decide), hr13_2],
          by dsimp only; rw [Function.update_of_ne (by decide), hr14_2],
          by rw [hmem2_eq]; exact hE_cs⟩
    · -- Case 2: `Ec` is nonempty
      have hEc_pos : Ec.length ≠ 0 := fun h => by simp [h] at hEc0_0
      have hEc_ne : Ec.isEmpty = false := by
        cases h : Ec with
        | nil => simp [h] at hEc_pos
        | cons _ _ => rfl
      set pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
      set pairLists := Ec.map fun e => (blockList vs b e.1, blockList vs b e.2)
      set rcost := routerCallCost G vs.toFinset pairs cfg.Δ cfg.L 100 z
      have hcolorCost_eq : stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec =
          rcost + (vs.length + 1) := by
        simp [stepCMacroColorCost, hEc_ne, pairs, rcost, hvs_card]
      have hstep_cost : scColorStepCost cfg cloud C_rt G vs b k z c =
          C_rt * rcost + C_rt + 380 * vs.length + 720 * k + 350 := by
        simp [scColorStepCost, colored, hprev, Ec, hEc_ne, pairs, rcost]
      set pairsA := hCur + 2 * Ec.length
      set pEnd := pairsA + 1 + Ec.length * (2 * b + 2)
      set hRt := pEnd + 2 + 2 * G.n
      have hpairs_len : (encodePairs pairLists).length = 1 + Ec.length * (2 * b + 2) :=
        encodePairs_blocks_length (hk_eq ▸ hEc_v c)
      have hpEnd_le : pEnd ≤ hCur + 2 * vs.length + 4 * k + 1 := by
        have : Ec.length * (2 * b + 2) = 2 * (Ec.length * b) + 2 * Ec.length := by ring
        omega
      have hhRt_le : hRt ≤ hCur + 2 * vs.length + 4 * k + 2 * G.n + 3 := by omega
      have hvs_st2 : LenListAt st2.mem xA vs := by
        have hx : ∀ a < h0, st2.mem a = st.mem a := fun a ha => hfr2 a (Or.inl (by have := hInv.h_ge; omega))
        exact ⟨by rw [hx _ (by omega)]; exact hvs_st.1,
          fun i hi => by rw [hx _ (by omega)]; exact hvs_st.2 i hi⟩
      refine runs_seq_assign_le (v := pairsA)
        (Expr.eval_add (Expr.eval_reg_of_eq hr16_2)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hEc_r17) (by omega))
          (by omega)) ?_
      let st3 : State := { mem := st2.mem, regs := Function.update st2.regs 18 pairsA, pos := st2.pos }
      refine runs_seq_triple_le
        (scBuildPairs_triple (pA := pairsA) p st2.mem vs Ec st3 hvs_st2 rfl hEc_at (hk_eq ▸ hEc_v c)
          (Or.inr (by have := hInv.h_ge; omega)) (Or.inr (by omega))
          (by omega) (by omega) (by omega) h16
          (by dsimp only [st3]; rw [Function.update_of_ne (by decide), hArgs2.r1])
          (by dsimp only [st3]; rw [Function.update_of_ne (by decide), hArgs2.r2])
          (by dsimp only [st3]; rw [Function.update_of_ne (by decide), hr16_2])
          (by dsimp only [st3]; rw [Function.update_of_ne (by decide), hEc_r17])
          (by dsimp only [st3]; rw [Function.update_self]) rfl) rfl ?_
      intro st4 ⟨hpEnd_r19, hoth4, _, hfr4, hmp_at⟩
      have hArgs4 : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st4 :=
        scArgs_of_eq hArgs2 (fun r hr => by
          rw [hoth4 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
          dsimp only [st3]; rw [Function.update_of_ne (by omega)])
      have hr13_4 : st4.regs 13 = 0 := by
        rw [hoth4 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), hr13_2]
      have hr14_4 : st4.regs 14 = (callsFakeEdges cs).length := by
        rw [hoth4 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), hr14_2]
      have hr15_4 : st4.regs 15 = c := by
        rw [hoth4 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), hr15_2]
      have hr16_4 : st4.regs 16 = hCur := by
        rw [hoth4 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), hr16_2]
      have hr17_4 : st4.regs 17 = Ec.length := by
        rw [hoth4 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_of_ne (by decide), hEc_r17]
      have hr18_4 : st4.regs 18 = pairsA := by
        rw [hoth4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_self]
      have hmem4_lt_hCur : ∀ a < hCur, st4.mem a = st.mem a := fun a ha => by
        rw [hfr4 a (Or.inl (by omega)), hfr2 a (Or.inl ha)]
      have hEc_4 : EdgesAt st4.mem hCur Ec := fun j hj => by
        rw [hfr4 _ (Or.inl (by omega)), hfr4 _ (Or.inl (by omega))]; exact hEc_at j hj
      have hGA_4 : GraphAt st4.mem gA G := fun i hi => by
        rw [hmem4_lt_hCur _ (by have := graph_encode_length G; have := hInv.h_ge; omega)]
        exact hGA_st i hi
      have hvs_4 : LenListAt st4.mem xA vs :=
        ⟨by rw [hmem4_lt_hCur _ (by have := hInv.h_ge; omega)]; exact hvs_st.1,
         fun i hi => by rw [hmem4_lt_hCur _ (by have := hInv.h_ge; omega)]; exact hvs_st.2 i hi⟩
      have hzf_4 : ZeroFrom st4.mem hRt := fun a ha => by
        rw [hfr4 a (Or.inr (by omega)), hfr2 a (Or.inr (by omega))]
        exact hInv.zf a (by omega)
      refine runs_seq_assign_le (v := G.n)
        (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hArgs4.r0) (graphAt_n hGA_4)) ?_
      refine runs_seq_assign_le (v := hRt)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := pEnd) (by dsimp only; rw [Function.update_of_ne (by decide), hpEnd_r19]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := G.n) (by simp)) (by omega))
          (by omega)) ?_
      have hvtp : ValidTerminalPairs vs.toFinset pairs :=
        validTerminalPairs_of_matching_edges hvs_nd hb (hk_eq ▸ hEc_v c) (hcol_spec.2.2.1 c)
      have hmap_pl : pairLists.map (fun p => (p.1.toFinset, p.2.toFinset)) = pairs := by
        simp [pairLists, pairs, blockSet]
      have hrt_pre : (multiPairRouterContract C_rt C_sp w).pre
          [gA, xA, pairsA, cfg.Δ, cfg.L, 100, z, pEnd, hRt] st4.mem := by
        refine ⟨gA, xA, pairsA, cfg.Δ, cfg.L, 100, z, pEnd, hRt, G, vs, pairLists, rfl,
          hGA_4, hGval, hvs_4, hvs_nd, hvs_sub, hGloop, hΔ, hdegG, hL,
          by rwa [hvs_card], by decide, hmp_at, ?_, hmap_pl.symm ▸ hvtp, hzf_4,
          by have := hInv.h_ge; omega, by have := hInv.h_ge; omega, by rw [hpairs_len]; omega, le_rfl,
          Or.inr (by have := hInv.h_ge; omega), Or.inr (by have := hInv.h_ge; omega),
          Or.inr (by rw [hpairs_len]; omega), ?_, h16, hGm, hzv⟩
        · intro q hq
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp hq
          exact ⟨(pairwise_lt_blockList hvs_s b e.1).imp fun h => Nat.ne_of_lt h,
                 (pairwise_lt_blockList hvs_s b e.2).imp fun h => Nat.ne_of_lt h⟩
        · rw [hmap_pl]
          unfold outerRouterSpace
          rw [hcolorCost_eq] at hstep_headroom
          have hmul : C_sp * (rcost + (G.n + 3) ^ 4 + 1) =
              C_sp * rcost + C_sp * ((G.n + 3) ^ 4 + 1) := by ring
          have hmul2 : C_sp * (rcost + (vs.length + 1)) = C_sp * rcost + C_sp * (vs.length + 1) := by ring
          change hRt + C_sp * (rcost + (G.n + 3) ^ 4 + 1) < 2 ^ w
          rw [hmul]; rw [hmul2] at hstep_headroom
          omega
      have hread_rt : readGraph st4.mem gA = G ∧
          (readLenPrefixedList st4.mem xA).toFinset = vs.toFinset ∧
          readMultiPairs st4.mem pairsA = pairs :=
        ⟨readGraph_eq_of_graphAt hGA_4, by rw [readLenPrefixedList_eq_of_lenListAt hvs_4],
         by rw [readMultiPairs_eq_of_multiPairsAt hmp_at, hmap_pl]⟩
      refine runs_seq_call_le (C := multiPairRouterContract C_rt C_sp w)
        (vs := [gA, xA, pairsA, cfg.Δ, cfg.L, 100, z, pEnd, hRt]) hRoute ?_ ?_ hrt_pre ?_
      · simp only [evalArgs, Expr.eval, h100, ↓reduceIte]
        have hr0' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 0 = gA := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hArgs4.r0]
        have hr1' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 1 = xA := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hArgs4.r1]
        have hr18' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 18 = pairsA := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr18_4]
        have hr5' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 5 = cfg.Δ := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hArgs4.r5]
        have hr6' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 6 = cfg.L := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hArgs4.r6]
        have hr4' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 4 = z := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hArgs4.r4]
        have hr19' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 19 = pEnd := by
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hpEnd_r19]
        have hr21' : (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 21 = hRt := by
          rw [Function.update_self]
        simp only [hr0', hr1', hr18', hr5', hr6', hr4', hr19', hr21']
      · intro v hv_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_mem
        rcases hv_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have := hInv.h_ge; omega
        · have := hInv.h_ge; omega
        · omega
        · exact hΔ_w
        · exact hL_w
        · exact h100
        · exact hz_w
        · omega
        · omega
      · intro hAfterRt mem5 pos5 hrt_post
        dsimp only [multiPairRouterContract] at hrt_post
        simp only [List.getD_cons_zero, List.getD_cons_succ, hread_rt.1, hread_rt.2.1, hread_rt.2.2] at hrt_post
        rcases hrt_post with ⟨hRouteOut, hhRt_le_after, hAfter_le, hzf_5, hfr_5⟩
        have hcost_rt_eq : (multiPairRouterContract C_rt C_sp w).cost
            [gA, xA, pairsA, cfg.Δ, cfg.L, 100, z, pEnd, hRt] st4.mem =
            C_rt * rcost + C_rt := by
          simp [multiPairRouterContract, hread_rt.1, hread_rt.2.1, hread_rt.2.2, rcost]
        have hAfter_bound : hAfterRt + 2 * b ≤
            hCur + (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
              C_sp * stepCMacroColorCost cfg routerCallCost G vs.toFinset vs b z Ec := by
          unfold outerRouterSpace at hAfter_le
          rw [hcolorCost_eq]
          have hmul1 : C_sp * (rcost + (G.n + 3) ^ 4 + 1) =
              C_sp * rcost + C_sp * ((G.n + 3) ^ 4 + 1) := by ring
          have hmul2 : C_sp * (rcost + (vs.length + 1)) =
              C_sp * rcost + C_sp * (vs.length + 1) := by ring
          change hAfterRt ≤ hRt + C_sp * (rcost + (G.n + 3) ^ 4 + 1) at hAfter_le
          omega
        have hAfter_h_le : hAfterRt + 2 * b ≤
            h0 + (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
              C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored (c + 1) := by
          have h1 : hCur ≤ h0 + c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
              C_sp * stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z colored c := hInv.h_le
          have h2 : (c + 1) * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) =
              c * (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) +
              (C_sp * ((G.n + 3) ^ 4 + 1) + 20 * (vs.length + k + 1) + 2 * G.n + 10) := by ring
          rw [hnext_cost_eq, Nat.mul_add]
          linarith only [h1, h2, hAfter_bound]
        let regs5 := Function.update (Function.update (Function.update st4.regs 20 G.n) 21 hRt) 12 hAfterRt
        let st5 : State := { mem := mem5, regs := regs5, pos := pos5 }
        have hArgs5 : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st5 :=
          scArgs_of_eq hArgs4 (fun r hr => by
            dsimp only [st5, regs5]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)])
        have hr12_5 : st5.regs 12 = hAfterRt := by dsimp only [st5, regs5]; rw [Function.update_self]
        have hr13_5 : st5.regs 13 = 0 := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr13_4]
        have hr14_5 : st5.regs 14 = (callsFakeEdges cs).length := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr14_4]
        have hr15_5 : st5.regs 15 = c := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr15_4]
        have hr16_5 : st5.regs 16 = hCur := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr16_4]
        have hr17_5 : st5.regs 17 = Ec.length := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr17_4]
        have hr19_5 : st5.regs 19 = pEnd := by
          dsimp only [st5, regs5]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hpEnd_r19]
        have hmem5_lt_hCur : ∀ a < hCur, mem5 a = st.mem a := fun a ha => by
          rw [hfr_5 a (by omega) (Or.inl (by omega)), hmem4_lt_hCur a ha]
        obtain ⟨st6, cPost, hrPost, hInv6, hr15_6, hcPost⟩ :=
          scOneColor_afterRoute hvs_s hvs_sub hGloop hΔ hdegG hL hvsL hb hk2 hk_eq
            hcn hcval hcdeg hc_lt hx_h hloc_h hout_h hdl_x hdl_o hdo_x h16 hInv hprev hE_cs
            hvs_st hEc_ne hEc_4 hRouteOut hInv.h_ge
            (by change hCur + 2 * Ec.length ≤ pEnd; omega) rfl hhRt_le_after hAfter_h_le
            (by omega) hzf_5 hfr_5 hmem5_lt_hCur hArgs5 hr12_5 hr13_5 hr14_5 hr15_5 hr16_5
            hr17_5 hr19_5 rfl
        refine ⟨.normal, st6, cPost, hrPost, ⟨rfl, hInv6, hr15_6⟩, ?_⟩
        rw [hstep_cost, hcost_rt_eq]
        simp only [Expr.size, argsSize]
        omega

end MinCostFlow.ExpanderDecomp
