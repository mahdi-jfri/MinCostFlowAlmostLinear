module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCOneColor

import Mathlib.Tactic.Linarith

/-!
# Step C Macro-Join Word-RAM Procedure (`ProgStepC`)

Implements and verifies `stepCProc bRoute`, a deterministic (`NoRand`) Word-RAM procedure meeting
`stepCContract cfg cloud (C_rt + 2000) C_sp w` (`ProgStepCSpec.lean`), calling the multi-pair
router through `multiPairRouterContract C_rt C_sp w`:

- If `k < 2`, writes `[0, 0]` to `outAddr` and returns `h`.
- Otherwise, iterates `c = 0, …, 16` via `scOneColorStmt bRoute` (`ProgStepCOneColor.lean`),
  writing tag `0` and the accumulated fake-edge count at `outAddr` if no cut occurred, and
  returning the updated zero-heap cursor `hCur`.

Main results:
- `stepCProc` / `stepCProc_noRand`
- `stepCProc_spec : MeetsContract w p base (stepCContract cfg cloud (C_rt + 2000) C_sp w)`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Procedure (`NoRand`) -/

/-- Full Step C macro-join procedure (`stepCMacro`).
`args = [gAddr, xAddr, b, k, z, Δ, L, colM, colAddr, locAddr, outAddr, h]`. -/
def stepCProc (bRoute : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 3) (.const 2))
    (seqStmts [
      .store (.reg 10) (.const 0),
      .store (.bin .add (.reg 10) (.const 1)) (.const 0),
      .ret (.reg 11)
    ])
    (seqStmts [
      .assign 12 (.reg 11),
      .assign 13 (.const 0),
      .assign 14 (.const 0),
      forRange 15 (.const 0) (.const 17) (scOneColorStmt bRoute),
      .cond (.bin .eq (.reg 13) (.const 0))
        (seqStmts [
          .store (.reg 10) (.const 0),
          .store (.bin .add (.reg 10) (.const 1)) (.reg 14)
        ])
        .nop,
      .ret (.reg 12)
    ])

theorem stepCProc_noRand (bRoute : ℕ) : (stepCProc bRoute).NoRand := by
  simp [stepCProc, scOneColorStmt_noRand, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. 17-Colour Loop Verification -/

/-- Pure upper bound on one colour step's cost relative to `stepCMacroLoopCost`. -/
private lemma scColorStepCost_le (cfg : CoreParams) (cloud : ℕ → Graph) (C_rt : ℕ)
    (G : Graph) (vs : List ℕ) (b k z c : ℕ) (hvs_nd : vs.Nodup) :
    scColorStepCost cfg cloud C_rt G vs b k z c ≤
      (C_rt + 400) *
        (stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) (c + 1) -
         stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) c) +
      720 * k + 350 := by
  unfold scColorStepCost
  simp only [stepCMacroLoopCost]
  rw [Nat.add_sub_cancel_left]
  cases hprev : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z (edgeColor17 (cloud k)) c with
  | inl _ => dsimp only; omega
  | inr _ =>
    dsimp only
    unfold stepCMacroColorCost
    set Ec := colorClass (edgeColor17 (cloud k)) c
    by_cases hemp : Ec.isEmpty = true
    · simp only [hemp, ↓reduceIte]; omega
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hcard : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
      rw [hcard]
      set r := routerCallCost G vs.toFinset (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2))
        cfg.Δ cfg.L 100 z
      have hmul : (C_rt + 400) * (r + (vs.length + 1)) =
          C_rt * r + C_rt * vs.length + C_rt + 400 * r + 400 * vs.length + 400 := by ring
      omega

/-- Execute the remaining `17 - m` iterations of the `forUp` loop in `stepCProc`. -/
private lemma scLoop_run {cfg : CoreParams} {cloud : ℕ → Graph}
    {w bRoute C_rt C_sp gA xA b k z colM colA locA outA h0 : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {vs : List ℕ} {ω : ℕ → Bool}
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
    (rem : ℕ) :
    ∀ m st, m + rem = 17 →
      ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs m st →
      ∃ st' cost,
        Runs w p ω (forUp 15 (.const 17) (scOneColorStmt bRoute)) st .normal st' cost ∧
        ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem0 G vs 17 st' ∧
        cost ≤ (C_rt + 400) *
            (stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) 17 -
             stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) m) +
          rem * (720 * k + 370) + 10 := by
  have h17 : 17 < 2 ^ w := by
    have hsp := hlay.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h81 : 81 ≤ (G.n + 3) ^ 4 := by
      have : (G.n + 3) ^ 4 = G.n ^ 4 + 12 * G.n ^ 3 + 54 * G.n ^ 2 + 108 * G.n + 81 := by ring
      omega
    unfold stepCSpace at hsp
    have hge : 20 * 81 ≤ (C_sp + 1) * (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z +
        20 * (G.n + 3) ^ 4 + 400 * (vs.length + k + 1)) := by
      have h1 : 20 * 81 ≤ 20 * (G.n + 3) ^ 4 := Nat.mul_le_mul_left 20 h81
      have h2 : 1 * (20 * 81) ≤ (C_sp + 1) * (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z +
          20 * (G.n + 3) ^ 4 + 400 * (vs.length + k + 1)) :=
        Nat.mul_le_mul (Nat.succ_pos C_sp) (by omega)
      omega
    omega
  have hvs_nd : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  induction rem with
  | zero =>
    intro m st hm hInv
    have hm17 : m = 17 := by omega
    subst hm17
    refine ⟨st, (Expr.bin .lt (.reg 15) (.const 17)).size + 1, ?_, hInv, by simp [Expr.size]⟩
    dsimp only [forUp]
    refine runs_loop_iff.mpr (Or.inl ⟨?_, rfl, rfl, rfl⟩)
    exact Expr.eval_lt_false (Expr.eval_reg_of_eq hInv.rc) (Expr.eval_const h17) (by omega) (by omega)
  | succ rem ih =>
    intro m st hm hInv
    have hm_lt : m < 17 := by omega
    obtain ⟨st1, c1, hr1, hInv1, hr15_1, hc1⟩ := scOneColor_step hRoute hGA hGval hvs_at hvs_s hvs_sub
      hGloop hΔ hdegG hL hvsL hb hk2 hk_eq hcn hcval hcdeg hcolM hcol_at hΔ_w hL_w hz_w hGm hzv hlay hm_lt hInv
    let st2 : State := { mem := st1.mem, regs := Function.update st1.regs 15 (m + 1), pos := st1.pos }
    have hinc : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) st1 .normal st2
        ((Expr.bin .add (.reg 15) (.const 1)).size + 1) :=
      runs_assign_iff.mpr ⟨m + 1,
        Expr.eval_add (Expr.eval_reg_of_eq hr15_1) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    obtain ⟨st3, c3, hr3, hInv3, hc3⟩ := ih (m + 1) st2 (by omega) hInv1
    have hcond : Expr.eval w st (.bin .lt (.reg 15) (.const 17)) = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq hInv.rc) (Expr.eval_const h17) hm_lt (by omega)
    have hbody : Runs w p ω (.seq (scOneColorStmt bRoute) (.assign 15 (.bin .add (.reg 15) (.const 1))))
        st .normal st2 (c1 + ((Expr.bin .add (.reg 15) (.const 1)).size + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, hinc, rfl⟩)
    refine ⟨st3, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c3, hcond, by decide, hbody, hr3, rfl⟩)), hInv3, ?_⟩
    have hstep_le := scColorStepCost_le cfg cloud C_rt G vs b k z m hvs_nd
    have hmono1 := stepCMacroLoopCost_mono cfg G vs b z (edgeColor17 (cloud k)) (Nat.le_succ m)
    have hmono2 := stepCMacroLoopCost_mono cfg G vs b z (edgeColor17 (cloud k)) (by omega : m + 1 ≤ 17)
    set L0 := stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) m
    set L1 := stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) (m + 1)
    set L17 := stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) 17
    have hsub_add : (L1 - L0) + (L17 - L1) = L17 - L0 := by omega
    have hmul_add : (C_rt + 400) * (L1 - L0) + (C_rt + 400) * (L17 - L1) = (C_rt + 400) * (L17 - L0) := by
      rw [← Nat.mul_add, hsub_add]
    have hrem_mul : (rem + 1) * (720 * k + 370) = rem * (720 * k + 370) + (720 * k + 370) := by ring
    simp only [Expr.size]
    omega

/-! ## 3. Contract Proof (`stepCProc_spec`) -/

/-- `stepCProc bRoute` meets `stepCContract cfg cloud (C_rt + 2000) C_sp w` whenever `bRoute`
meets `multiPairRouterContract C_rt C_sp w`. -/
theorem stepCProc_spec {cfg : CoreParams} {cloud : ℕ → Graph} {w base bRoute C_rt C_sp : ℕ} {p : Program}
    (hp : p.procs[base]? = some (stepCProc bRoute))
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w)) :
    MeetsContract w p base (stepCContract cfg cloud (C_rt + 2000) C_sp w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨gA, xA, b, k, z, colM, colA, locA, outA, h0, G, vs, rfl,
    hGA, hGval, hvs_at, hvs_s, hvs_sub, hGloop, hΔ, hdegG, hL, hvsL, hb, hk_eq, hcloud,
    hloc0, hzf0, hlay, hGm, hzv⟩
  have hreadG : readGraph mem gA = G := readGraph_eq_of_graphAt hGA
  have hreadX : readLenPrefixedList mem xA = vs := readLenPrefixedList_eq_of_lenListAt hvs_at
  have hΔ_w : cfg.Δ < 2 ^ w := hwords cfg.Δ (by simp)
  have hL_w : cfg.L < 2 ^ w := hwords cfg.L (by simp)
  have hz_w : z < 2 ^ w := hwords z (by simp)
  have hlay_copy := hlay
  rcases hlay_copy with ⟨hg_h, hx_h, hcol_h, hloc_h, hout_h, hdl_g, hdl_x, hdl_c, hdl_o,
    hdo_g, hdo_x, hdo_c, hsp_w, h16⟩
  have h17 : 17 < 2 ^ w := by
    have h81 : 81 ≤ (G.n + 3) ^ 4 := by
      have : (G.n + 3) ^ 4 = G.n ^ 4 + 12 * G.n ^ 3 + 54 * G.n ^ 2 + 108 * G.n + 81 := by ring
      omega
    unfold stepCSpace at hsp_w
    have h2 : 1 * (20 * 81) ≤ (C_sp + 1) * (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z +
        20 * (G.n + 3) ^ 4 + 400 * (vs.length + k + 1)) :=
      Nat.mul_le_mul (Nat.succ_pos C_sp) (by have := Nat.mul_le_mul_left 20 h81; omega)
    omega
  let st0 := startState [gA, xA, b, k, z, cfg.Δ, cfg.L, colM, colA, locA, outA, h0] mem pos
  have hst0_args : ScArgs gA xA b k z cfg.Δ cfg.L colM colA locA outA h0 st0 :=
    ⟨by simp [st0, startState], by simp [st0, startState], by simp [st0, startState],
     by simp [st0, startState], by simp [st0, startState], by simp [st0, startState],
     by simp [st0, startState], by simp [st0, startState], by simp [st0, startState],
     by simp [st0, startState], by simp [st0, startState], by simp [st0, startState]⟩
  dsimp only [stepCProc, seqStmts, forRange]
  refine runs_start_le (T := (stepCContract cfg cloud (C_rt + 2000) C_sp w).cost
      [gA, xA, b, k, z, cfg.Δ, cfg.L, colM, colA, locA, outA, h0] mem) ?_
  by_cases hk2 : 2 ≤ k
  · -- Main branch: `2 ≤ k`
    rcases hcloud hk2 with ⟨hcn, hcval, hcdeg, hcolM, hcol_at⟩
    have hcond : Expr.eval w st0 (.bin .lt (.reg 3) (.const 2)) = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq hst0_args.r3) (Expr.eval_const (w := w) (by omega)) (by omega) (by omega)
    refine runs_cond_le (v := 0) hcond (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_assign_le (v := h0) (Expr.eval_reg_of_eq hst0_args.r11) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
    let st4 : State :=
      { mem := mem,
        regs := Function.update (Function.update (Function.update (Function.update st0.regs 12 h0) 13 0) 14 0) 15 0,
        pos := pos }
    have hInv0 : ScLoopInv cfg cloud C_sp gA xA b k z colM colA locA outA h0 mem G vs 0 st4 := by
      refine ⟨scArgs_of_eq hst0_args (fun r hr => by
          dsimp only [st4]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
        by simp [st4], hloc0,
        by dsimp only [st4]
           rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), Function.update_self],
        by dsimp only [st4]
           rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), Function.update_self]; omega,
        by dsimp only [st4]
           rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), Function.update_self]; exact hzf0,
        fun a _ _ _ => rfl, ?_⟩
      simp only [stepCMacroLoop, callsFakeEdges, List.flatMap_nil, List.length_nil]
      refine ⟨by dsimp only [st4]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self],
        by dsimp only [st4]; rw [Function.update_of_ne (by decide), Function.update_self],
        fun j hj => by simp at hj⟩
    obtain ⟨st5, cLoop, hrLoop, hInv5, hcLoop⟩ := scLoop_run hRoute hGA hGval hvs_at hvs_s hvs_sub
      hGloop hΔ hdegG hL hvsL hb hk2 hk_eq hcn hcval hcdeg hcolM hcol_at hΔ_w hL_w hz_w hGm hzv hlay 17 0 st4 rfl hInv0
    have hcostM_eq : stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z =
        (200 * k + 1) + stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z
          (edgeColor17 (cloud k)) 17 := by
      simp [stepCMacroCost, hk2]
    have hloop0 : stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z
        (edgeColor17 (cloud k)) 0 = 0 := rfl
    have h5_le_sp : st5.regs 12 ≤ h0 + stepCSpace C_sp G.n vs.length k
        (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z) := by
      have h1 := hInv5.h_le
      have hloop_le : stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z
          (edgeColor17 (cloud k)) 17 ≤
          stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z := by
        rw [hcostM_eq]; omega
      have h2 := stepCSpace_step_bound C_sp G.n vs.length k
        (stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) 17)
        (stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z) hloop_le
      omega
    have hcost_final : ∀ extra ≤ 60,
        cLoop + extra ≤ (C_rt + 2000) *
          stepCMacroCost cfg routeOrCut routerCallCost cloud G vs.toFinset vs b k z + (C_rt + 2000) := by
      intro extra hex
      rw [hloop0, Nat.sub_zero] at hcLoop
      rw [hcostM_eq]
      set L17 := stepCMacroLoopCost cfg routeOrCut routerCallCost G vs.toFinset vs b z (edgeColor17 (cloud k)) 17
      have hmul : (C_rt + 2000) * (200 * k + 1 + L17) =
          (C_rt + 2000) * (200 * k + 1) + (C_rt + 2000) * L17 := by ring
      have h1 : (C_rt + 400) * L17 ≤ (C_rt + 2000) * L17 := Nat.mul_le_mul_right L17 (by omega)
      have h2 : 17 * (720 * k + 370) + 10 + extra ≤ 2000 * (200 * k + 1) := by omega
      have h3 : 2000 * (200 * k + 1) ≤ (C_rt + 2000) * (200 * k + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    -- Splice the 17-colour loop run into the sequential chain
    suffices hrest : ∃ o st' c',
        Runs w p ω (.seq (.cond (.bin .eq (.reg 13) (.const 0))
            (.seq (.store (.reg 10) (.const 0)) (.store (.bin .add (.reg 10) (.const 1)) (.reg 14))) .nop)
          (.ret (.reg 12))) st5 o st' c' ∧
        (stepCContract cfg cloud (C_rt + 2000) C_sp w).post
            [gA, xA, b, k, z, cfg.Δ, cfg.L, colM, colA, locA, outA, h0] mem o.value st'.mem ∧
        0 + c' ≤ 30 by
      rcases hrest with ⟨o, st', c', hrRest, hpost, hc'⟩
      refine ⟨o, st', _, runs_seq_iff.mpr (Or.inr ⟨st5, cLoop, c', hrLoop, hrRest, rfl⟩), hpost, ?_⟩
      dsimp only [stepCContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, Expr.size]
      have := hcost_final (30 + c') (by omega)
      omega
    cases hfin : stepCMacroLoop cfg routeOrCut G vs.toFinset vs b z (edgeColor17 (cloud k)) 17 with
    | inl U =>
      have hout5 := hInv5.out_match; rw [hfin] at hout5
      rcases hout5 with ⟨hr13_5, hm0_5, U_list, hUnd, hUfin, hUlen, hUat⟩
      have hcond2 : Expr.eval w st5 (.bin .eq (.reg 13) (.const 0)) = some 0 := by
        have he : Expr.eval w st5 (.bin .eq (.reg 13) (.const 0)) = some (if 1 = 0 then 1 else 0) :=
          Expr.eval_eq_op (Expr.eval_reg_of_eq hr13_5) (Expr.eval_const (w := w) (by omega)) (by omega)
        simpa using he
      refine runs_seq_cond_le (v := 0) hcond2 (fun h => absurd rfl h) (fun _ => ?_)
      refine runs_seq_nop_le ?_
      refine runs_ret_le (v := st5.regs 12) (Expr.eval_reg_of_eq rfl) ?_ (by simp [Expr.size])
      dsimp only [stepCContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCMacro, hk2, ↓reduceIte, hfin]
      exact ⟨⟨hm0_5, U_list, hUnd, hUfin, hUlen, hUat⟩, hInv5.loc0, hInv5.h_ge, h5_le_sp, hInv5.zf, hInv5.frame⟩
    | inr cm =>
      rcases cm with ⟨cs, ms⟩
      have hout5 := hInv5.out_match; rw [hfin] at hout5
      rcases hout5 with ⟨hr13_5, hr14_5, hE_cs⟩
      have hcond2 : Expr.eval w st5 (.bin .eq (.reg 13) (.const 0)) = some 1 := by
        have he : Expr.eval w st5 (.bin .eq (.reg 13) (.const 0)) = some (if 0 = 0 then 1 else 0) :=
          Expr.eval_eq_op (Expr.eval_reg_of_eq hr13_5) (Expr.eval_const (w := w) (by omega)) (by omega)
        simpa using he
      refine runs_seq_cond_le (v := 1) hcond2 (fun _ => ?_) (fun h => absurd h (by decide))
      refine runs_seq_assoc_le ?_
      refine runs_seq_store_le (x := outA) (v := 0)
        (Expr.eval_reg_of_eq hInv5.args.r10) (Expr.eval_const (w := w) (by omega)) ?_
      refine runs_seq_store_le (x := outA + 1) (v := (callsFakeEdges cs).length)
        (Expr.eval_add (Expr.eval_reg_of_eq hInv5.args.r10) (Expr.eval_const (w := w) (by omega))
          (by unfold stepCOutSize at hout_h; omega)) (Expr.eval_reg_of_eq hr14_5) ?_
      refine runs_ret_le (v := st5.regs 12) (Expr.eval_reg_of_eq rfl) ?_ (by simp [Expr.size])
      dsimp only [stepCContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCMacro, hk2, ↓reduceIte, hfin]
      refine ⟨⟨by simp, by simp, fun j hj => ?_⟩, ?_, hInv5.h_ge, h5_le_sp, ?_, ?_⟩
      · have hne1 : outA + 2 + 2 * j ≠ outA := by omega
        have hne2 : outA + 2 + 2 * j ≠ outA + 1 := by omega
        have hne3 : outA + 2 + 2 * j + 1 ≠ outA := by omega
        have hne4 : outA + 2 + 2 * j + 1 ≠ outA + 1 := by omega
        simpa [hne1, hne2, hne3, hne4] using hE_cs j hj
      · intro u hu
        have hne1 : locA + u ≠ outA := by rcases hdl_o with h | h; omega; unfold stepCOutSize at h; omega
        have hne2 : locA + u ≠ outA + 1 := by rcases hdl_o with h | h; omega; unfold stepCOutSize at h; omega
        simp [hne1, hne2, hInv5.loc0 u hu]
      · intro a ha
        have hne1 : a ≠ outA := by have := hInv5.h_ge; unfold stepCOutSize at hout_h; omega
        have hne2 : a ≠ outA + 1 := by have := hInv5.h_ge; unfold stepCOutSize at hout_h; omega
        simp [hne1, hne2, hInv5.zf a ha]
      · intro a ha_h ha_loc ha_out
        have hne1 : a ≠ outA := by rcases ha_out with h | h; omega; unfold stepCOutSize at h; omega
        have hne2 : a ≠ outA + 1 := by rcases ha_out with h | h; omega; unfold stepCOutSize at h; omega
        simp [hne1, hne2, hInv5.frame a ha_h ha_loc ha_out]
  · -- Trivial branch: `k < 2`
    have hlt : k < 2 := by omega
    have hcond : Expr.eval w st0 (.bin .lt (.reg 3) (.const 2)) = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq hst0_args.r3) (Expr.eval_const (w := w) (by omega)) hlt (by omega)
    refine runs_cond_le (v := 1) hcond (fun _ => ?_) (fun h => absurd h (by decide))
    refine runs_seq_store_le (x := outA) (v := 0)
      (Expr.eval_reg_of_eq hst0_args.r10) (Expr.eval_const (w := w) (by omega)) ?_
    refine runs_seq_store_le (x := outA + 1) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq hst0_args.r10) (Expr.eval_const (w := w) (by omega))
        (by unfold stepCOutSize at hout_h; omega)) (Expr.eval_const (w := w) (by omega)) ?_
    refine runs_ret_le (v := h0) (Expr.eval_reg_of_eq hst0_args.r11) ?_
      (by dsimp only [stepCContract]
          simp only [List.getD_cons_zero, List.getD_cons_succ, stepCMacroCost, hk2, ↓reduceIte, Expr.size]
          omega)
    dsimp only [stepCContract, Outcome.value]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hreadG, hreadX, stepCMacro, hk2, ↓reduceIte]
    refine ⟨⟨by simp, by simp [callsFakeEdges], fun j hj => by simp [callsFakeEdges] at hj⟩, ?_, le_rfl, Nat.le_add_right _ _, ?_, ?_⟩
    · intro u hu
      have hne1 : locA + u ≠ outA := by rcases hdl_o with h | h; omega; unfold stepCOutSize at h; omega
      have hne2 : locA + u ≠ outA + 1 := by rcases hdl_o with h | h; omega; unfold stepCOutSize at h; omega
      simp [hne1, hne2, startState, hloc0 u hu]
    · intro a ha
      have hne1 : a ≠ outA := by unfold stepCOutSize at hout_h; omega
      have hne2 : a ≠ outA + 1 := by unfold stepCOutSize at hout_h; omega
      simp [hne1, hne2, startState, hzf0 a ha]
    · intro a _ _ ha_out
      have hne1 : a ≠ outA := by rcases ha_out with h | h; omega; unfold stepCOutSize at h; omega
      have hne2 : a ≠ outA + 1 := by rcases ha_out with h | h; omega; unfold stepCOutSize at h; omega
      simp [hne1, hne2, startState]

end MinCostFlow.ExpanderDecomp
