module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBInit
public import MinCostFlow.ExpanderDecomp.ProgStepBFinal
public import MinCostFlow.ExpanderDecomp.Used

import Mathlib.Tactic.Linarith

/-!
# Step B Parallel Cut-Matching Word-RAM Procedure and Module (`ProgStepB`)

Implements and verifies `stepBProc bSubCore bRoute`, a deterministic (`NoRand`), strictly local
Word-RAM procedure meeting `stepBContract cfg M r q w (stepBTimeConst C_rt) (stepBSpaceConst C_sp) Tprev Sprev`
(`ProgStepBSpec.lean`) for every `12 ≤ cfg.a₀`, `2 ≤ q ≤ r`, calling recursive `Core` via
`stepBSubCoreContract` and the multi-pair static router via `multiPairRouterContract C_rt C_sp w`.

Also delivers `stepBModule (C_rt C_sp : ℕ) : StepBModule C_rt C_sp` (`Used.lean`), bridging
`(coreOnContract ParamConfig.default M r w K_B K_C S_B S_C).below (fun args _ => args.getD 0 0) q`
to `stepBSubCoreContract` at level `q - 1`, ready to plug directly into
`Used.expanderDecompositionUsed_of_parts`.

Main results:
- `stepBProc`, `stepBProc_noRand`
- `stepBProc_spec`
- `stepBSubCoreContract_of_coreOnContract_below`
- `stepBModule`, `stepBModule_noRand`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Procedure (`NoRand`) -/

/-- Full Step B Word-RAM procedure (`OneShot` Step B).
`args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h]`. -/
def stepBProc (bSubCore bRoute : ℕ) : Stmt :=
  seqStmts [
    sbInitStmt,
    forRange 15 (.const 0) (.reg 21) (sbOneRoundStmt bSubCore bRoute),
    .cond (.bin .eq (.reg 13) (.const 0))
      (sbFinalInjStmt bRoute)
      (.ret (.reg 12))
  ]

theorem stepBProc_noRand (bSubCore bRoute : ℕ) : (stepBProc bSubCore bRoute).NoRand := by
  simp [stepBProc, sbInitStmt_noRand, sbOneRoundStmt_noRand, sbFinalInjStmt_noRand,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. Total Space and Cost Bounds -/

private lemma sbTotalSpace_le {cfg : ParamConfig} {M r q C_sp Sprev n k b nBlocks : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k)
    (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_div : nBlocks = k / b) (h0 : ℕ) :
    (sbPersist h0 k b nBlocks (LParam M)).hPersist +
      (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev n (NOf M r) (LParam M) q k nBlocks +
      (outerRouterSpace C_sp n (stepBRouterR1 (NOf M r) (LParam M) q) +
        3 * k + 2 * nBlocks + 2 * n + 5) ≤
      h0 + stepBSpace (stepBSpaceConst C_sp) n (NOf M r) (LParam M) q Sprev := by
  set N := NOf M r
  set L := LParam M
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hN4 : 4 ≤ N := harith.1
  have hL4 : 4 ≤ L := harith.2.1
  have hnb_le : nBlocks ≤ 2 * N := harith.2.2.2.2.2.2.1
  have hnb_b : nBlocks * b ≤ k := harith.2.2.2.2.2.2.2.1
  have hb_le : b ≤ k := by rw [hb_eq]; exact hklo
  have hpers_le := sbPersist_size_le (h0 := h0) (k := k) (b := b) (nBlocks := nBlocks) (L := L)
    hb_le hnb_b hL4
  have hsub_calls : (49 * L + 1) * nBlocks ≤ 100 * N * L := stepB_subCore_calls_le hL4 hnb_le
  have hsub_sp : (49 * L + 1) * (nBlocks * Sprev) ≤ 100 * N * L * Sprev := by
    have h1 : (49 * L + 1) * (nBlocks * Sprev) = ((49 * L + 1) * nBlocks) * Sprev := by ring
    rw [h1]; exact Nat.mul_le_mul_right Sprev hsub_calls
  have hk_Nq : k ≤ N ^ q := hkhi
  have h100kL : 100 * k * L + 6 * k + 6 * nBlocks + 4 ≤ 200 * N ^ q * L + 200 * N + 200 := by
    have h1 : k * L ≤ N ^ q * L := Nat.mul_le_mul_right L hk_Nq
    have h2 : k ≤ N ^ q * L := le_trans hk_Nq (Nat.le_mul_of_pos_right _ (by omega))
    have h3 : 100 * k * L = 100 * (k * L) := by ring
    have h4 : 200 * N ^ q * L = 200 * (N ^ q * L) := by ring
    omega
  have hround_split : (49 * L + 1) * sbRoundSpaceStep C_sp Sprev n N L q k nBlocks =
      (49 * L + 1) * (nBlocks * Sprev) +
      (49 * L + 1) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 6 * k + 6 * nBlocks + 2 * n + 10) := by
    unfold sbRoundSpaceStep; ring
  have hnon1 : (49 * L + 1) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 6 * k + 6 * nBlocks + 2 * n + 10) +
      (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 3 * k + 2 * nBlocks + 2 * n + 5) ≤
      (49 * L + 2) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20) := by
    have ha1 : outerRouterSpace C_sp n (stepBRouterR1 N L q) + 6 * k + 6 * nBlocks + 2 * n + 10 ≤
        outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20 := by omega
    have ha2 : outerRouterSpace C_sp n (stepBRouterR1 N L q) + 3 * k + 2 * nBlocks + 2 * n + 5 ≤
        outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20 := by omega
    have h1 := Nat.mul_le_mul_left (49 * L + 1) ha1
    have h2 : (49 * L + 2) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20) =
        (49 * L + 1) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20) +
        (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20) := by ring
    omega
  have hnon2 := stepB_nonSubCore_space_le (C_sp := C_sp) (n := n) (N := N) (L := L) (q := q) hN4 hL4
  unfold stepBSpace
  linarith

private lemma sbTotalCost_le {cfg : ParamConfig} {M r q C_rt Tprev k b nBlocks : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k)
    (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_div : nBlocks = k / b) :
    (50 * k + 35 * nBlocks + 220) +
      (49 * LParam M + 1) *
        (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
          1720 * k * LParam M + 750 * k + 1050 * nBlocks + 460) +
      (C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt + 320 * k + 460 * nBlocks + 410) ≤
      stepBCostBound (stepBTimeConst C_rt) (NOf M r) (LParam M) q Tprev := by
  set N := NOf M r
  set L := LParam M
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hN4 : 4 ≤ N := harith.1
  have hL4 : 4 ≤ L := harith.2.1
  have hnb_le : nBlocks ≤ 2 * N := harith.2.2.2.2.2.2.1
  have hsub_calls : (49 * L + 1) * nBlocks ≤ 100 * N * L := stepB_subCore_calls_le hL4 hnb_le
  have hsub_t : (49 * L + 1) * (nBlocks * Tprev) ≤ 100 * N * L * Tprev := by
    have h1 : (49 * L + 1) * (nBlocks * Tprev) = ((49 * L + 1) * nBlocks) * Tprev := by ring
    rw [h1]; exact Nat.mul_le_mul_right Tprev hsub_calls
  have hkL : k * L ≤ N ^ q * L := Nat.mul_le_mul_right L hkhi
  have hk_L : k ≤ N ^ q * L := le_trans hkhi (Nat.le_mul_of_pos_right _ (by omega))
  have hround_split : (49 * L + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 N L q + C_rt +
        1720 * k * L + 750 * k + 1050 * nBlocks + 460) =
      (49 * L + 1) * (nBlocks * Tprev) +
      (49 * L + 1) * (C_rt * stepBRouterR1 N L q + C_rt + 1720 * k * L + 750 * k + 1050 * nBlocks + 460) := by ring
  have ha1 : C_rt * stepBRouterR1 N L q + C_rt + 1720 * k * L + 750 * k + 1050 * nBlocks + 460 ≤
      C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000 := by
    have h1720 : 1720 * k * L = 1720 * (k * L) := by ring
    have h5000 : 5000 * N ^ q * L = 5000 * (N ^ q * L) := by ring
    have hnb1 : 1050 * nBlocks ≤ 2100 * N := by omega
    have hN_le : N ≤ N ^ q * L := by
      have h1 : N ≤ N ^ q := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ q := Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
    omega
  have ha2 : C_rt * stepBRouterR1 N L q + C_rt + 320 * k + 460 * nBlocks + 410 ≤
      C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000 := by
    have h5000 : 5000 * N ^ q * L = 5000 * (N ^ q * L) := by ring
    omega
  have hinit_le : 50 * k + 35 * nBlocks + 220 ≤ 2000 * N ^ q * L + 2000 := by
    have hN_le : N ≤ N ^ q * L := by
      have h1 : N ≤ N ^ q := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ q := Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
    have h2000 : 2000 * N ^ q * L = 2000 * (N ^ q * L) := by ring
    omega
  have hnon1 : (49 * L + 1) * (C_rt * stepBRouterR1 N L q + C_rt + 1720 * k * L + 750 * k + 1050 * nBlocks + 460) +
      (C_rt * stepBRouterR1 N L q + C_rt + 320 * k + 460 * nBlocks + 410) ≤
      (49 * L + 2) * (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) := by
    have h1 := Nat.mul_le_mul_left (49 * L + 1) ha1
    have h2 : (49 * L + 2) * (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) =
        (49 * L + 1) * (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) +
        (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) := by ring
    linarith
  have hnon2 := stepB_nonSubCore_cost_le (C_rt := C_rt) (N := N) (L := L) (q := q) hN4 hL4
  unfold stepBCostBound
  linarith

/-! ## 3. Round-Loop Induction (`sbLoop_run`) -/

private lemma sbLoop_run {cfg : ParamConfig} {M r q w bSubCore bRoute C_rt C_sp Tprev Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {ω : ℕ → Bool}
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w))
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt mem0 pA (coreParamsOf cfg M r) r)
    (hG_at : GraphAt mem0 gA G) (hG_val : G.IsValid)
    (hX_at : VertsAt mem0 xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2) (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k) (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hgeom : gA + 2 + 2 * G.m ≤ h0 ∧ xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n gA (2 + 2 * G.m) ∧ DisjointRange locA G.n xA k ∧
      DisjointRange locA G.n pA (coreParamsSize r) ∧ DisjointRange locA G.n fA (2 * k) ∧
      DisjointRange locA G.n outA (2 + k) ∧ DisjointRange outA (2 + k) gA (2 + 2 * G.m) ∧
      DisjointRange outA (2 + k) xA k ∧ DisjointRange outA (2 + k) pA (coreParamsSize r) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧ DisjointRange fA (2 * k) gA (2 + 2 * G.m) ∧
      DisjointRange fA (2 * k) xA k ∧ DisjointRange fA (2 * k) pA (coreParamsSize r))
    (hSpace_w : (sbPersist h0 k b nBlocks (LParam M)).hPersist +
      (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w)
    (hΔ_w : (coreParamsOf cfg M r).Δ < 2 ^ w)
    (hL_w : 49 * LParam M + 2 < 2 ^ w) (hw128 : 128 < 2 ^ w) (rem : ℕ) :
    ∀ m st, m + rem = 49 * LParam M + 1 →
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X m st →
      ∃ st' cost,
        Runs w p ω (forUp 15 (.reg 21) (sbOneRoundStmt bSubCore bRoute)) st .normal st' cost ∧
        SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X
          (49 * LParam M + 1) st' ∧
        cost ≤ rem * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
          1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) + 10 := by
  induction rem with
  | zero =>
    intro m st hm hInv
    have hmeq : m = 49 * LParam M + 1 := by omega
    subst hmeq
    have hcond : (.bin .lt (.reg 15) (.reg 21) : Expr).eval w st = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq hInv.rm) (Expr.eval_reg_of_eq hInv.args.r21)
        (by dsimp [sbPersist]; omega) (by omega)
    exact ⟨st, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hInv, by simp only [Expr.size]; omega⟩
  | succ rem ih =>
    intro m st hm hInv
    have hm_le : m ≤ 49 * LParam M := by omega
    have hsp_m : (sbPersist h0 k b nBlocks (LParam M)).hPersist +
        (m + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks < 2 ^ w := by
      have h1 := Nat.mul_le_mul_right (sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks)
        (show m + 1 ≤ 49 * LParam M + 1 by omega)
      omega
    obtain ⟨st1, c1, hr1, hInv1, hr15_1, hc1⟩ :=
      sbOneRound_step hSub hRoute ha0 ha hrl hq2 hqr hcp_at hG_at hG_val hX_at hX_sub hGloop hdegG hmG
        hklo hkhi hb_eq hnb_eq hz_eq hm_le hgeom hsp_m hΔ_w hw128 hInv
    let st2 : State := { mem := st1.mem, regs := Function.update st1.regs 15 (m + 1), pos := st1.pos }
    have hinc : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) st1 .normal st2
        (Expr.size (.bin .add (.reg 15) (.const 1)) + 1) :=
      runs_assign_iff.mpr ⟨m + 1,
        Expr.eval_add (Expr.eval_reg_of_eq hr15_1) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    obtain ⟨st', c2, hr2, hInv', hc2⟩ := ih (m + 1) st2 (by omega) hInv1
    have hcond : (.bin .lt (.reg 15) (.reg 21) : Expr).eval w st = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq hInv.rm) (Expr.eval_reg_of_eq hInv.args.r21)
        (by dsimp [sbPersist]; omega) (by omega)
    have hbody : Runs w p ω (.seq (sbOneRoundStmt bSubCore bRoute)
        (.assign 15 (.bin .add (.reg 15) (.const 1)))) st .normal st2 _ :=
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, hinc, rfl⟩)
    have hloop : Runs w p ω (forUp 15 (.reg 21) (sbOneRoundStmt bSubCore bRoute)) st .normal st' _ :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c2, hcond, by decide, hbody, hr2, rfl⟩))
    refine ⟨st', _, hloop, hInv', ?_⟩
    simp only [Expr.size]
    have hmul : (rem + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
          1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) =
        rem * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
          1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) +
        (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
          1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) := by ring
    omega

/-! ## 4. Main Contract Theorem (`stepBProc_spec`) -/

/-- `stepBProc bSubCore bRoute` meets `stepBContract cfg M r q w (stepBTimeConst C_rt) (stepBSpaceConst C_sp) Tprev Sprev`
whenever `12 ≤ cfg.a₀`, `bSubCore` meets `stepBSubCoreContract` at level `q - 1`, and `bRoute` meets
`multiPairRouterContract C_rt C_sp w`. -/
theorem stepBProc_spec {cfg : ParamConfig} {M r q w base bSubCore bRoute C_rt C_sp Tprev Sprev : ℕ}
    {p : Program}
    (ha0 : 12 ≤ cfg.a₀)
    (hp : p.procs[base]? = some (stepBProc bSubCore bRoute))
    (hSub : MeetsContract w p bSubCore (stepBSubCoreContract cfg M r (q - 1) w Tprev Sprev))
    (hRoute : MeetsContract w p bRoute (multiPairRouterContract C_rt C_sp w)) :
    MeetsContract w p base
      (stepBContract cfg M r q w (stepBTimeConst C_rt) (stepBSpaceConst C_sp) Tprev Sprev) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0, G, X, rfl,
    ha, hrl, hq2, hqr, hcp_at, hG_at, hG_val, hX_at, hX_sub, hGloop, hdegG, hmG,
    hklo, hkhi, hb_eq, hnb_eq, hz_eq, hloc0, hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h,
    hd_lg, hd_lx, hd_lp, hd_lf, hd_lo, hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp,
    hzf0, hsp_w⟩
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have htot_sp := sbTotalSpace_le (C_sp := C_sp) (Sprev := Sprev) (n := G.n) ha hrl hq2 hqr
    hklo hkhi hb_eq hnb_div h0
  have hSpace_all : (sbPersist h0 k b nBlocks (LParam M)).hPersist +
      (49 * LParam M + 1) * sbRoundSpaceStep C_sp Sprev G.n (NOf M r) (LParam M) q k nBlocks +
      (outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
        3 * k + 2 * nBlocks + 2 * G.n + 5) < 2 ^ w := lt_of_le_of_lt htot_sp hsp_w
  have hΔ_w : (coreParamsOf cfg M r).Δ < 2 ^ w := by
    have hL4 : 4 ≤ LParam M := harith.2.1
    have hN4 : 4 ≤ NOf M r := harith.1
    have hNq16 : 16 ≤ (NOf M r) ^ q := by
      calc 16 = 4 ^ 2 := by decide
        _ ≤ (NOf M r) ^ 2 := Nat.pow_le_pow_left hN4 2
        _ ≤ (NOf M r) ^ q := Nat.pow_le_pow_right (by omega) hq2
    have hnon2 := stepB_nonSubCore_space_le (C_sp := C_sp) (n := G.n) (N := NOf M r) (L := LParam M) (q := q) hN4 hL4
    have hterm : 1024 * LParam M ≤
        (49 * LParam M + 2) * (outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
          20 * (NOf M r) ^ q + 20 * NOf M r + 2 * G.n + 20) := by
      have h1 : 49 * LParam M ≤ 49 * LParam M + 2 := by omega
      have h2 : 320 ≤ outerRouterSpace C_sp G.n (stepBRouterR1 (NOf M r) (LParam M) q) +
          20 * (NOf M r) ^ q + 20 * NOf M r + 2 * G.n + 20 := by omega
      have h3 := Nat.mul_le_mul h1 h2
      have h4 : 1024 * LParam M ≤ (49 * LParam M) * 320 := by omega
      exact le_trans h4 h3
    have hsp_ge : 1024 * LParam M ≤ stepBSpace (stepBSpaceConst C_sp) G.n (NOf M r) (LParam M) q Sprev := by
      unfold stepBSpace; omega
    have hΔ_eq : (coreParamsOf cfg M r).Δ = 1024 * LParam M := rfl
    omega
  have hL_w : 49 * LParam M + 2 < 2 ^ w := by
    have hL4 : 4 ≤ LParam M := harith.2.1
    have hΔ_eq : (coreParamsOf cfg M r).Δ = 1024 * LParam M := rfl; omega
  have hw128 : 128 < 2 ^ w := by have hL4 : 4 ≤ LParam M := harith.2.1; omega
  have hP_w : (sbPersist h0 k b nBlocks (LParam M)).hPersist < 2 ^ w := by omega
  have hn_w : G.n < 2 ^ w := by omega
  have hgeom : gA + 2 + 2 * G.m ≤ h0 ∧ xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧
      locA + G.n ≤ h0 ∧ fA + 2 * k ≤ h0 ∧ outA + 2 + k ≤ h0 ∧
      DisjointRange locA G.n gA (2 + 2 * G.m) ∧ DisjointRange locA G.n xA k ∧
      DisjointRange locA G.n pA (coreParamsSize r) ∧ DisjointRange locA G.n fA (2 * k) ∧
      DisjointRange locA G.n outA (2 + k) ∧ DisjointRange outA (2 + k) gA (2 + 2 * G.m) ∧
      DisjointRange outA (2 + k) xA k ∧ DisjointRange outA (2 + k) pA (coreParamsSize r) ∧
      DisjointRange outA (2 + k) fA (2 * k) ∧ DisjointRange fA (2 * k) gA (2 + 2 * G.m) ∧
      DisjointRange fA (2 * k) xA k ∧ DisjointRange fA (2 * k) pA (coreParamsSize r) :=
    ⟨hg_h, hx_h, hp_h, hloc_h, hf_h, hout_h, hd_lg, hd_lx, hd_lp, hd_lf, hd_lo,
      hd_og, hd_ox, hd_op, hd_of, hd_fg, hd_fx, hd_fp⟩
  -- Phase 1: Init
  obtain ⟨st1, c1, hr1, hInv0, hc1⟩ :=
    sbInit_run (C_sp := C_sp) (Sprev := Sprev) (p := p) (pos := pos) (ω := ω) (z := z)
      (fA := fA) (outA := outA) ha hrl hq2 hqr hcp_at hG_at hX_at hX_sub hb_eq hklo hkhi hnb_eq
      hloc0 hx_h hp_h hloc_h hzf0 hP_w hn_w hw128
  -- `forRange 15 (.const 0) ...` begins with `.assign 15 (.const 0)` (no-op since `st1.regs 15 = 0`)
  have hset15_eq : { st1 with regs := Function.update st1.regs 15 0 } = st1 := by
    cases st1 with | mk m1 r1 p1 =>
      simp only [State.mk.injEq, true_and, and_true]
      funext reg; by_cases h : reg = 15
      · subst h; rw [Function.update_self]; exact hInv0.rm.symm
      · rw [Function.update_of_ne h]
  have hset15 : Runs w p ω (.assign 15 (.const 0)) st1 .normal st1 (Expr.size (.const 0) + 1) := by
    have h := runs_assign_iff (w := w) (p := p) (ω := ω) (r := 15) (e := .const 0) (st := st1).mpr
      ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    rwa [hset15_eq] at h
  -- Phase 2: `49 * L + 1` rounds
  obtain ⟨stL, cL, hrL, hInvL, hcL⟩ :=
    sbLoop_run hSub hRoute ha0 ha hrl hq2 hqr hcp_at hG_at hG_val hX_at hX_sub hGloop hdegG hmG
      hklo hkhi hb_eq hnb_eq hz_eq hgeom (by omega) hΔ_w hL_w hw128 (49 * LParam M + 1) 0 st1 (by omega) hInv0
  have hforR : Runs w p ω (forRange 15 (.const 0) (.reg 21) (sbOneRoundStmt bSubCore bRoute)) st1 .normal stL
      ((Expr.size (.const 0) + 1) + cL + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, _, cL, hset15, hrL, rfl⟩)
  -- Phase 3: Final conditional (`r13 = 0` → `sbFinalInjStmt`, else `.ret (.reg 12)`)
  have hcost_tot := sbTotalCost_le (C_rt := C_rt) (Tprev := Tprev) ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hcost_def : (stepBContract cfg M r q w (stepBTimeConst C_rt) (stepBSpaceConst C_sp) Tprev Sprev).cost
      [q, gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0] mem =
      stepBCostBound (stepBTimeConst C_rt) (NOf M r) (LParam M) q Tprev := rfl
  rw [hcost_def]
  have hps_ge : h0 ≤ (sbPersist h0 k b nBlocks (LParam M)).hPersist := by dsimp [sbPersist]; omega
  by_cases hr13 : stL.regs 13 = 0
  · obtain ⟨hRet, stF, cF, hrF, hresF, hh0_le, hhRet_le, hzfF, hlocF, hfrF, hcF⟩ :=
      sbFinalInj_run hRoute ha hrl hq2 hqr hcp_at hG_at hG_val hX_at hX_sub hGloop hdegG hmG
        hklo hkhi hb_eq hnb_eq hz_eq hloc0 hgeom hSpace_all hΔ_w hw128 hInvL hr13
    have hcond_t : (.bin .eq (.reg 13) (.const 0) : Expr).eval w stL = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) rfl (by omega)
    have htail : Runs w p ω (.cond (.bin .eq (.reg 13) (.const 0)) (sbFinalInjStmt bRoute) (.ret (.reg 12)))
        stL (.returned hRet) stF (Expr.size (.bin .eq (.reg 13) (.const 0)) + cF + 1) :=
      runs_cond_iff.mpr ⟨1, cF, hcond_t, by simp only [one_ne_zero, ↓reduceIte]; exact hrF, rfl⟩
    have hfull : Runs w p ω (stepBProc bSubCore bRoute)
        (startState [q, gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0] mem pos) (.returned hRet) stF
        (c1 + (((Expr.size (.const 0) + 1) + cL + 1) + (Expr.size (.bin .eq (.reg 13) (.const 0)) + cF + 1) + 1) + 1) := by
      dsimp only [stepBProc, seqStmts]
      exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hforR, htail, rfl⟩), rfl⟩)
    refine ⟨.returned hRet, stF, _, hfull, ?_, ?_⟩
    · intro gA' k' xA' b' nB' z' pA' locA' fA' outA' h0' G' X' hargs _ _ _ _ _ hG' _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      simp only [List.cons.injEq, and_true, true_and] at hargs
      rcases hargs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hGeq : G' = G := by rw [← readGraph_eq_of_graphAt hG', readGraph_eq_of_graphAt hG_at]
      have hXeq : X' = X := by
        have h1 : (X'.sort (· ≤ ·)) = (X.sort (· ≤ ·)) := by
          refine List.ext_getElem (by rw [Finset.length_sort, Finset.length_sort, ← hX'.1, ← hX_at.1]) fun i h1 h2 => ?_
          rw [← hX'.2 i h1, hX_at.2 i h2]
        ext u; rw [← Finset.mem_sort (· ≤ ·), h1, Finset.mem_sort]
      subst G'; subst X'
      exact ⟨hresF, hh0_le, le_trans hhRet_le htot_sp, hzfF, hlocF, hfrF⟩
    · simp only [Expr.size]
      have hL1 : 49 * LParam M + 1 ≥ 1 := by omega
      have hdiff : (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
            1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) + 10 ≤
          (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
            1720 * k * LParam M + 750 * k + 1050 * nBlocks + 460) := by
        have hmul : (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
              1720 * k * LParam M + 750 * k + 1050 * nBlocks + 460) =
            (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
              1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) + (49 * LParam M + 1) * 10 := by ring
        omega
      omega
  · rcases hInvL.state_match with ⟨hr13_1, U, hCoreOut, hCutSpec⟩ | ⟨hr13_0, _⟩
    · have hcond_f : (.bin .eq (.reg 13) (.const 0) : Expr).eval w stL = some 0 :=
        Expr.eval_eq_false (Expr.eval_reg_of_eq hr13_1) (Expr.eval_const (by omega)) (by decide) (by omega)
      have hret : Runs w p ω (.ret (.reg 12)) stL (.returned (stL.regs 12)) stL (Expr.size (.reg 12) + 1) :=
        runs_ret_iff.mpr ⟨stL.regs 12, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
      have htail : Runs w p ω (.cond (.bin .eq (.reg 13) (.const 0)) (sbFinalInjStmt bRoute) (.ret (.reg 12)))
          stL (.returned (stL.regs 12)) stL (Expr.size (.bin .eq (.reg 13) (.const 0)) + (Expr.size (.reg 12) + 1) + 1) :=
        runs_cond_iff.mpr ⟨0, _, hcond_f, by simp only [↓reduceIte]; exact hret, rfl⟩
      have hfull : Runs w p ω (stepBProc bSubCore bRoute)
          (startState [q, gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0] mem pos) (.returned (stL.regs 12)) stL
          (c1 + (((Expr.size (.const 0) + 1) + cL + 1) +
            (Expr.size (.bin .eq (.reg 13) (.const 0)) + (Expr.size (.reg 12) + 1) + 1) + 1) + 1) := by
        dsimp only [stepBProc, seqStmts]
        exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hforR, htail, rfl⟩), rfl⟩)
      refine ⟨.returned (stL.regs 12), stL, _, hfull, ?_, ?_⟩
      · intro gA' k' xA' b' nB' z' pA' locA' fA' outA' h0' G' X' hargs _ _ _ _ _ hG' _ hX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        simp only [List.cons.injEq, and_true, true_and] at hargs
        rcases hargs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hGeq : G' = G := by rw [← readGraph_eq_of_graphAt hG', readGraph_eq_of_graphAt hG_at]
        have hXeq : X' = X := by
          have h1 : (X'.sort (· ≤ ·)) = (X.sort (· ≤ ·)) := by
            refine List.ext_getElem (by rw [Finset.length_sort, Finset.length_sort, ← hX'.1, ← hX_at.1]) fun i h1 h2 => ?_
            rw [← hX'.2 i h1, hX_at.2 i h2]
          ext u; rw [← Finset.mem_sort (· ≤ ·), h1, Finset.mem_sort]
        subst G'; subst X'
        refine ⟨Or.inl ⟨hCoreOut.1, U, hCoreOut, hCutSpec⟩,
          le_trans hps_ge hInvL.h_ge,
          le_trans (le_trans hInvL.h_le (Nat.le_add_right _ _)) htot_sp,
          hInvL.zf, hInvL.loc0, fun a ha hfa hout => ?_⟩
        by_cases hloc_a : a < locA ∨ locA + G.n ≤ a
        · exact hInvL.frame a ha hloc_a hfa hout
        · have hu : a - locA < G.n := by omega
          have ha_eq : a = locA + (a - locA) := by omega
          rw [ha_eq, hInvL.loc0 _ hu, hloc0 _ hu]
      · simp only [Expr.size]
        have hL1 : 49 * LParam M + 1 ≥ 1 := by omega
        have hdiff : (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
              1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) + 10 ≤
            (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
              1720 * k * LParam M + 750 * k + 1050 * nBlocks + 460) := by
          have hmul : (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
                1720 * k * LParam M + 750 * k + 1050 * nBlocks + 460) =
              (49 * LParam M + 1) * (nBlocks * Tprev + C_rt * stepBRouterR1 (NOf M r) (LParam M) q + C_rt +
                1720 * k * LParam M + 750 * k + 1050 * nBlocks + 450) + (49 * LParam M + 1) * 10 := by ring
          omega
        omega
    · exact absurd hr13_0 hr13

/-! ## 5. Bridge to `Used.StepBModule` -/

/-- Bridges `(coreOnContract cfg M r w K_B K_C S_B S_C).below (fun args _ => args.getD 0 0) q`
(`2 ≤ q`) directly to `stepBSubCoreContract cfg M r (q - 1) w (coreProgTime ...) (coreProgSpace ...)`. -/
theorem stepBSubCoreContract_of_coreOnContract_below
    {cfg : ParamConfig} {M r q w K_B K_C S_B S_C coreOnIdx : ℕ} {p : Program}
    (hq2 : 2 ≤ q)
    (hCore : MeetsContract w p coreOnIdx
      ((coreOnContract cfg M r w K_B K_C S_B S_C).below (fun args _ => args.getD 0 0) q)) :
    MeetsContract w p coreOnIdx
      (stepBSubCoreContract cfg M r (q - 1) w
        (coreProgTime K_B K_C cfg M r (q - 1))
        (coreProgSpace S_B S_C cfg M r (q - 1))) := by
  intro args mem pos ω hwords hpre
  have hbelow_pre : ((coreOnContract cfg M r w K_B K_C S_B S_C).below (fun args _ => args.getD 0 0) q).pre args mem := by
    rcases hpre with ⟨gA, k, xA, pA, locA, outA, h0, G, X, rfl,
      ha0, ha, hrl, hqr, hcp, hG, hGv, hGn, hX, hXs, hGl, hkN, hdeg, hm, hloc,
      hg, hx, hp, hl, ho, d1, d2, d3, d4, d5, d6, d7, hzf, hsp⟩
    exact ⟨⟨q - 1, gA, k, xA, pA, locA, outA, h0, G, X, rfl,
      ha0, ha, hrl, hqr, hcp, hG, hGv, hGn, hX, hXs, hGl, hkN, hdeg, hm, hloc,
      hg, hx, hp, hl, ho, d1, d2, d3, d4, d5, d6, d7, hzf, hsp⟩, by dsimp only; rw [List.getD_cons_zero]; omega⟩
  rcases hCore args mem pos ω hwords hbelow_pre with ⟨body, hp, o, st', c, hrun, hpost, hcost⟩
  refine ⟨body, hp, o, st', c, hrun, ?_, ?_⟩
  · intro gA k xA pA locA outA h0 G X hargs ha0 ha hrl hqr hcp hG hGv hGn hX hXs hGl hkN hdeg hm hloc
      hg hx hp hl ho d1 d2 d3 d4 d5 d6 d7 hzf hsp
    exact hpost (q - 1) gA k xA pA locA outA h0 G X hargs ha0 ha hrl hqr hcp hG hGv hGn hX hXs hGl hkN
      hdeg hm hloc hg hx hp hl ho d1 d2 d3 d4 d5 d6 d7 hzf hsp
  · rcases hpre with ⟨gA, k, xA, pA, locA, outA, h0, G, X, rfl, _⟩
    simpa [Contract.below, coreOnContract, stepBSubCoreContract] using hcost

/-- Concrete deterministic (`NoRand`) `StepBModule C_rt C_sp` plugging into
`Used.expanderDecompositionUsed_of_parts`. -/
def stepBModule (C_rt C_sp : ℕ) : StepBModule C_rt C_sp where
  procs := fun _ coreOnIdx routeIdx => [stepBProc coreOnIdx routeIdx]
  entryOff := 0
  K_B := stepBTimeConst C_rt
  S_B := stepBSpaceConst C_sp
  meets := fun base coreOnIdx routeIdx M r q w p hq2 _ hAt hRoute hCore => by
    have hp : p.procs[base + 0]? = some (stepBProc coreOnIdx routeIdx) := by
      simpa using hAt 0 (by simp)
    exact stepBProc_spec (by decide) hp
      (stepBSubCoreContract_of_coreOnContract_below hq2 hCore) hRoute

theorem stepBModule_noRand (C_rt C_sp base coreOnIdx routeIdx : ℕ) :
    ∀ s ∈ (stepBModule C_rt C_sp).procs base coreOnIdx routeIdx, s.NoRand := by
  intro s hs
  simp only [stepBModule, List.mem_singleton] at hs
  subst hs
  exact stepBProc_noRand coreOnIdx routeIdx

end MinCostFlow.ExpanderDecomp
