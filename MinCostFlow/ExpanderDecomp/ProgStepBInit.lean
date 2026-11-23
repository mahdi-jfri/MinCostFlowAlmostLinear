module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBLayout

import Mathlib.Tactic.Linarith

/-!
# Step B Startup Initialization (`ProgStepBInit`)

Defines and verifies `sbInitStmt`, which computes the persistent layout constants `r16..r21`
and `r12 = hPersist`, copies `X.sort` into `LenListAt` at `h0`, initializes `actA[0..nBlocks-1] := 1`,
writes the empty witness graph headers `wBaseA[i * wStride] := G.n` (with `m_i = 0` from
`ZeroFrom mem0 h0`), initializes `rangeB_A[0..b-1] := [0, …, b - 1]`, and establishes
`SbLoopInv ... 0` in at most `50 * k + 35 * nBlocks + 220` steps.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Register-setup prefix of `sbInitStmt`: computes `r12..r25` and stores `mem[h0] := k`. -/
def sbInitSetupStmt : Stmt :=
  seqStmts [
    .assign 22 (.load (.reg 1)),
    .assign 23 (.load (.bin .add (.reg 7) (.const 1))),
    .assign 21 (.bin .add (.bin .mul (.const 49) (.reg 23)) (.const 1)),
    .assign 16 (.bin .add (.const 2) (.bin .mul (.const 2) (.bin .mul (.reg 21) (.bin .div (.reg 4) (.const 2))))),
    .assign 17 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 2)),
    .assign 18 (.bin .add (.reg 17) (.bin .mul (.const 3) (.reg 5))),
    .assign 19 (.bin .add (.reg 18) (.bin .mul (.reg 5) (.reg 4))),
    .assign 20 (.bin .add (.reg 19) (.bin .mul (.reg 5) (.reg 4))),
    .assign 24 (.bin .add (.reg 20) (.bin .mul (.reg 5) (.reg 16))),
    .assign 12 (.bin .add (.bin .add (.reg 24) (.reg 4)) (.reg 16)),
    .assign 13 (.const 0),
    .assign 14 (.const 0),
    .assign 15 (.const 0),
    .store (.reg 11) (.reg 2),
    .assign 25 (.bin .add (.reg 11) (.const 1))
  ]

/-- Initialization prelude of `stepBProc` (`r0..r11` hold the 12 Step B arguments). -/
def sbInitStmt : Stmt :=
  seqStmts [
    sbInitSetupStmt,
    scCopySliceStmt 3 25 2 26 27,
    forRange 26 (.const 0) (.reg 5) (seqStmts [
      .store (.bin .add (.reg 17) (.reg 26)) (.const 1),
      .store (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 16))) (.reg 22)
    ]),
    forRange 26 (.const 0) (.reg 4)
      (.store (.bin .add (.reg 24) (.reg 26)) (.reg 26))
  ]

theorem sbInitStmt_noRand : sbInitStmt.NoRand := by
  simp [sbInitStmt, sbInitSetupStmt, scCopySliceStmt, seqStmts, forRange, forUp, Stmt.NoRand]

private lemma sbInitSetup_run {w q gA k xA b nBlocks z pA locA fA outA h0 L n : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hgn : mem0 gA = n) (hL_mem : mem0 (pA + 1) = L) (hb2 : 2 ≤ b)
    (hp_h : pA + 2 ≤ h0) (hP_w : (sbPersist h0 k b nBlocks L).hPersist < 2 ^ w)
    (_hn_w : n < 2 ^ w) (_hL_w : L < 2 ^ w) (hw128 : 128 < 2 ^ w) :
    let st₀ := startState [q, gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0] mem0 pos
    let ps := sbPersist h0 k b nBlocks L
    ∃ st1 c1,
      Runs w p ω sbInitSetupStmt st₀ .normal st1 c1 ∧
      st1.mem = Function.update mem0 h0 k ∧
      SbArgs q gA k xA b nBlocks z pA locA fA outA h0 L st1 ∧
      st1.regs 12 = ps.hPersist ∧ st1.regs 13 = 0 ∧ st1.regs 14 = 0 ∧ st1.regs 15 = 0 ∧
      st1.regs 22 = n ∧ st1.regs 24 = ps.rangeB_A ∧ st1.regs 25 = h0 + 1 ∧
      c1 ≤ 120 := by
  intro st₀ ps
  have hps_ord : h0 + 1 + k = ps.actA ∧ ps.actA + 3 * nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b + ps.wStride = ps.hPersist ∧
      ps.maxR = 49 * L + 1 ∧ ps.wStride = 2 + 2 * (ps.maxR * (b / 2)) := by
    dsimp only [ps, sbPersist]; refine ⟨rfl, rfl, rfl, by omega, rfl, by omega, rfl, by ring⟩
  have hP_w' : ps.hPersist < 2 ^ w := hP_w
  have hmaxR_le : ps.maxR ≤ ps.maxR * (b / 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hr0 : st₀.regs 0 = q := by simp [st₀, startState]
  have hr1 : st₀.regs 1 = gA := by simp [st₀, startState]
  have hr2 : st₀.regs 2 = k := by simp [st₀, startState]
  have hr3 : st₀.regs 3 = xA := by simp [st₀, startState]
  have hr4 : st₀.regs 4 = b := by simp [st₀, startState]
  have hr5 : st₀.regs 5 = nBlocks := by simp [st₀, startState]
  have hr6 : st₀.regs 6 = z := by simp [st₀, startState]
  have hr7 : st₀.regs 7 = pA := by simp [st₀, startState]
  have hr8 : st₀.regs 8 = locA := by simp [st₀, startState]
  have hr9 : st₀.regs 9 = fA := by simp [st₀, startState]
  have hr10 : st₀.regs 10 = outA := by simp [st₀, startState]
  have hr11 : st₀.regs 11 = h0 := by simp [st₀, startState]
  have hrun : ∃ o st1 c1,
      Runs w p ω sbInitSetupStmt st₀ o st1 c1 ∧
      (normalPost fun st1 =>
        st1.mem = Function.update mem0 h0 k ∧
        SbArgs q gA k xA b nBlocks z pA locA fA outA h0 L st1 ∧
        st1.regs 12 = ps.hPersist ∧ st1.regs 13 = 0 ∧ st1.regs 14 = 0 ∧ st1.regs 15 = 0 ∧
        st1.regs 22 = n ∧ st1.regs 24 = ps.rangeB_A ∧ st1.regs 25 = h0 + 1) o st1 ∧
      c1 ≤ 120 := by
    refine runs_start_le ?_
    dsimp only [sbInitSetupStmt, seqStmts]
    refine runs_seq_assign_le (v := n) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr1) hgn) ?_
    refine runs_seq_assign_le (v := L)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr7])) (Expr.eval_const (by omega)) (by omega)) hL_mem) ?_
    refine runs_seq_assign_le (v := ps.maxR)
      (by have heq : 49 * L + 1 = ps.maxR := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
            (Expr.eval_const (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.wStride)
      (by have heq : 2 + 2 * (ps.maxR * (b / 2)) = ps.wStride := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_const (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp))
                (Expr.eval_div (Expr.eval_reg_of_eq (by simp [hr4])) (Expr.eval_const (by omega)) (by omega)) (by omega))
              (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.actA)
      (by have heq : h0 + 1 + k = ps.actA := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr11])) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (by simp [hr2])) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.savA)
      (by have heq : ps.actA + 3 * nBlocks = ps.savA := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr5])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.cmpA)
      (by have heq : ps.savA + nBlocks * b = ps.cmpA := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [hr5])) (Expr.eval_reg_of_eq (by simp [hr4])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.wBaseA)
      (by have heq : ps.cmpA + nBlocks * b = ps.wBaseA := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [hr5])) (Expr.eval_reg_of_eq (by simp [hr4])) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.rangeB_A)
      (by have heq : ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [hr5])) (Expr.eval_reg_of_eq (by simp)) (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := ps.hPersist)
      (by have heq : ps.rangeB_A + b + ps.wStride = ps.hPersist := by omega
          exact heq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_reg_of_eq (by simp [hr4])) (by omega))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := h0) (v := k) (Expr.eval_reg_of_eq (by simp [hr11])) (Expr.eval_reg_of_eq (by simp [hr2])) ?_
    refine runs_assign_le (v := h0 + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr11])) (Expr.eval_const (by omega)) (by omega))
      ?_ (by simp only [Expr.size]; omega)
    exact ⟨rfl,
      ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4], by simp [hr5],
       by simp [hr6], by simp [hr7], by simp [hr8], by simp [hr9], by simp [hr10], by simp [hr11],
       by simp [ps], by simp [ps], by simp [ps], by simp [ps], by simp [ps], by simp [ps]⟩,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  rcases hrun with ⟨o, st1, c1, hr, hp, hc⟩
  cases o with
  | returned _ => exact False.elim hp
  | normal => exact ⟨st1, c1, hr, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
      hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2, hc⟩

/-- Execution theorem for `sbInitStmt`: establishes `SbLoopInv ... 0` from Step B's input state. -/
theorem sbInit_run {cfg : ParamConfig} {M r q w C_sp Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 : ℕ}
    {p : Program} {mem0 : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hcp_at : CoreParamsAt mem0 pA (coreParamsOf cfg M r) r)
    (hG_at : GraphAt mem0 gA G)
    (hX_at : VertsAt mem0 xA k X) (_hX_sub : X ⊆ Finset.range G.n)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hklo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k)
    (hkhi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hloc0 : ∀ u < G.n, mem0 (locA + u) = 0)
    (hx_h : xA + k ≤ h0) (hp_h : pA + coreParamsSize r ≤ h0) (hloc_h : locA + G.n ≤ h0)
    (hzf0 : ZeroFrom mem0 h0)
    (hP_w : (sbPersist h0 k b nBlocks (LParam M)).hPersist < 2 ^ w)
    (hn_w : G.n < 2 ^ w) (hw128 : 128 < 2 ^ w) :
    let st₀ := startState [q, gA, k, xA, b, nBlocks, z, pA, locA, fA, outA, h0] mem0 pos
    ∃ st' cost,
      Runs w p ω sbInitStmt st₀ .normal st' cost ∧
      SbLoopInv cfg M r q C_sp Sprev gA k xA b nBlocks z pA locA fA outA h0 mem0 G X 0 st' ∧
      cost ≤ 50 * k + 35 * nBlocks + 220 := by
  intro st₀
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hcfg : CoreParamsValid cp r := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnb_div : nBlocks = k / b := by rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX_at.1]
  have harith := stepB_block_arith ha hrl hq2 hqr hklo hkhi hb_eq hnb_div
  have hb_even : Even b := harith.2.2.2.1
  have hb_le_k : b ≤ k := by rw [hb_eq]; exact hklo
  have hnb_b : nBlocks * b ≤ k := harith.2.2.2.2.2.2.2.1
  have hps_ord : h0 + 1 + k = ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist ∧ ps.maxR = 49 * LParam M + 1 ∧
      ps.wStride = 2 + 2 * (ps.maxR * (b / 2)) := by
    dsimp only [ps, sbPersist]; refine ⟨rfl, rfl, by omega, by omega, rfl, by omega, rfl, rfl, rfl, rfl, by ring⟩
  have hL_lt_w : LParam M < 2 ^ w := by
    have hb2 : 1 ≤ b / 2 := by have := harith.2.2.1; rcases hb_even with ⟨u, hu⟩; omega
    have h1 : ps.maxR ≤ ps.maxR * (b / 2) := Nat.le_mul_of_pos_right _ hb2
    omega
  obtain ⟨st1, c1, hrun1, hmem1, hargs1, hr12_1, hr13_1, hr14_1, hr15_1, hr22_1, hr24_1, hr25_1, hc1⟩ :=
    sbInitSetup_run (w := w) (q := q) (z := z) (locA := locA) (fA := fA) (outA := outA)
      (p := p) (pos := pos) (ω := ω) (graphAt_n hG_at) hcp_at.2.1 harith.2.2.1
      (by unfold coreParamsSize at hp_h; omega) hP_w hn_w hL_lt_w hw128
  have hX_at1 : ListAt st1.mem xA vs := fun idx hidx => by
    have hlen : vs.length = k := by rw [Finset.length_sort, ← hX_at.1]
    rw [hmem1, Function.update_of_ne (by omega)]; exact hX_at.2 idx hidx
  have htail : ∃ o st' c2,
      Runs w p ω (seqStmts [
        scCopySliceStmt 3 25 2 26 27,
        forRange 26 (.const 0) (.reg 5) (seqStmts [
          .store (.bin .add (.reg 17) (.reg 26)) (.const 1),
          .store (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 16))) (.reg 22)
        ]),
        forRange 26 (.const 0) (.reg 4)
          (.store (.bin .add (.reg 24) (.reg 26)) (.reg 26))]) st1 o st' c2 ∧
      (normalPost fun st' =>
        SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st' ∧
        st'.regs 12 = ps.hPersist ∧ st'.regs 13 = 0 ∧ st'.regs 14 = 0 ∧ st'.regs 15 = 0 ∧
        MemFrame mem0 st'.mem h0 ps.hPersist ∧
        LenListAt st'.mem h0 vs ∧
        (∀ i < nBlocks, st'.mem (ps.actA + i) = 1) ∧
        (∀ i < nBlocks, GraphAt st'.mem (ps.wBaseA + i * ps.wStride) (Graph.mk G.n [])) ∧
        ListAt st'.mem ps.rangeB_A (List.range b)) o st' ∧
      c2 ≤ 50 * k + 35 * nBlocks + 90 := by
    refine runs_start_le ?_
    dsimp only [seqStmts]
    refine runs_seq_triple_le
      (scCopySlice_triple (w := w) (srcA := xA) (dstA := h0 + 1) (len := k)
        (rSrc := 3) (rDst := 25) (rLen := 2) (rI := 26) (rTmp := 27) (by decide)
        p st1.mem vs st1 (by rw [Finset.length_sort, ← hX_at.1]) hX_at1
        (Or.inr (by omega)) (by omega) (by omega) (by omega)
        hargs1.r3 hr25_1 hargs1.r2 rfl) rfl ?_
    intro st2 ⟨hoth2, _, hfr2, hX_copy2⟩
    have hargs2 : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st2 :=
      sbArgs_of_eq hargs1 (fun r hr => hoth2 r (by omega) (by omega))
    let Inv1 : ℕ → State → Prop := fun j st =>
      st.regs 26 = j ∧
      (∀ r < 26, st.regs r = st2.regs r) ∧
      MemFrame st2.mem st.mem ps.actA ps.rangeB_A ∧
      (∀ i < j, i < nBlocks → st.mem (ps.actA + i) = 1 ∧
        st.mem (ps.wBaseA + i * ps.wStride) = G.n ∧ st.mem (ps.wBaseA + i * ps.wStride + 1) = 0) ∧
      (∀ i < nBlocks, j ≤ i → st.mem (ps.wBaseA + i * ps.wStride + 1) = 0)
    have hloop1 : Triple w p (fun st => st = st2)
        (forRange 26 (.const 0) (.reg 5) (seqStmts [
          .store (.bin .add (.reg 17) (.reg 26)) (.const 1),
          .store (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 16))) (.reg 22)
        ]))
        (normalPost (Inv1 nBlocks)) (fun _ => 30 * nBlocks + 20) := by
      have hl := Triple.forRange_const (w := w) (p := p) (r := 26) (lo := .const 0) (hi := .reg 5)
        (body := seqStmts [
          .store (.bin .add (.reg 17) (.reg 26)) (.const 1),
          .store (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 16))) (.reg 22)
        ])
        (P := fun st => st = st2) (Inv := Inv1) 18 0 nBlocks (Nat.zero_le _) (by omega) (fun _ => by omega)
        (fun st hs => by
          subst hs
          refine ⟨Expr.eval_const (by omega), by simp, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)],
            memFrame_refl _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun i hi _ => ?_⟩
          have hiw : i * ps.wStride + ps.wStride ≤ nBlocks * ps.wStride := by
            have : (i + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); linarith
          rw [hfr2 _ (Or.inr (by omega)), hmem1, Function.update_of_ne (by omega)]
          exact hzf0 _ (by omega))
        (fun _ _ _ _ hI => hI.1)
        (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.2.1 5 (by decide)).trans hargs2.r5))
        (fun j _ hj => by
          intro st ω ⟨hr26, hlt26, hfr, hdone, hrest⟩
          have hjw : j * ps.wStride + ps.wStride ≤ nBlocks * ps.wStride := by
            have : (j + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); linarith
          refine runs_start_le ?_
          dsimp only [seqStmts]
          refine runs_seq_store_le (x := ps.actA + j) (v := 1)
            (Expr.eval_add (Expr.eval_reg_of_eq ((hlt26 17 (by decide)).trans hargs2.r17)) (Expr.eval_reg_of_eq hr26) (by omega))
            (Expr.eval_const (by omega)) ?_
          refine runs_store_le (x := ps.wBaseA + j * ps.wStride) (v := G.n)
            (Expr.eval_add (Expr.eval_reg_of_eq ((hlt26 20 (by decide)).trans hargs2.r20))
              (Expr.eval_mul (Expr.eval_reg_of_eq hr26) (Expr.eval_reg_of_eq ((hlt26 16 (by decide)).trans hargs2.r16)) (by omega)) (by omega))
            (Expr.eval_reg_of_eq ((hlt26 22 (by decide)).trans ((hoth2 22 (by decide) (by decide)).trans hr22_1))) ?_
            (by simp only [Expr.size]; omega)
          refine ⟨⟨by simp, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt26 r hr,
            fun a ha => by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr a ha,
            fun i hi hin => ?_, fun i hin hji => ?_⟩, hr26⟩
          · dsimp only
            by_cases hij : i = j
            · subst hij
              exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
                by rw [Function.update_self],
                by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hrest i hin (le_refl _)⟩
            · have hwS2 : 2 ≤ ps.wStride := by omega
              have hne_w : ps.wBaseA + i * ps.wStride ≠ ps.wBaseA + j * ps.wStride := by
                intro heq
                exact hij (Nat.eq_of_mul_eq_mul_right (by omega : 0 < ps.wStride) (by omega))
              have hne_w1 : ps.wBaseA + i * ps.wStride + 1 ≠ ps.wBaseA + j * ps.wStride := by
                intro heq
                rcases lt_or_gt_of_ne hij with hlt | hgt
                · have h1 : (i + 1) * ps.wStride ≤ j * ps.wStride := Nat.mul_le_mul_right _ (by omega)
                  have h2 : (i + 1) * ps.wStride = i * ps.wStride + ps.wStride := by ring
                  omega
                · have h1 : (j + 1) * ps.wStride ≤ i * ps.wStride := Nat.mul_le_mul_right _ (by omega)
                  have h2 : (j + 1) * ps.wStride = j * ps.wStride + ps.wStride := by ring
                  omega
              exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hdone i (by omega) hin).1,
                by rw [Function.update_of_ne hne_w, Function.update_of_ne (by omega)]; exact (hdone i (by omega) hin).2.1,
                by rw [Function.update_of_ne hne_w1, Function.update_of_ne (by omega)]; exact (hdone i (by omega) hin).2.2⟩
          · dsimp only
            have h1 : (j + 1) * ps.wStride ≤ i * ps.wStride := Nat.mul_le_mul_right _ (by omega)
            have h2 : (j + 1) * ps.wStride = j * ps.wStride + ps.wStride := by ring
            have hwS2 : 2 ≤ ps.wStride := by omega
            have hne_w1 : ps.wBaseA + i * ps.wStride + 1 ≠ ps.wBaseA + j * ps.wStride := by omega
            rw [Function.update_of_ne hne_w1, Function.update_of_ne (by omega)]
            exact hrest i hin (by omega))
      exact hl.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => by simp only [Expr.size]; omega)
    refine runs_seq_triple_le hloop1 rfl ?_
    intro st3 ⟨_, hlt26_3, hfr3, hdone3, _⟩
    have hargs3 : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st3 :=
      sbArgs_of_eq hargs2 (fun r hr => hlt26_3 r (by omega))
    let Inv2 : ℕ → State → Prop := fun j st =>
      st.regs 26 = j ∧
      (∀ r < 26, st.regs r = st3.regs r) ∧
      MemFrame st3.mem st.mem ps.rangeB_A ps.wRelA ∧
      (∀ i < j, st.mem (ps.rangeB_A + i) = i)
    have hloop2 : Triple w p (fun st => st = st3)
        (forRange 26 (.const 0) (.reg 4) (.store (.bin .add (.reg 24) (.reg 26)) (.reg 26)))
        (normalPost (Inv2 b)) (fun _ => 20 * b + 20) := by
      have hl := Triple.forRange_const (w := w) (p := p) (r := 26) (lo := .const 0) (hi := .reg 4)
        (body := .store (.bin .add (.reg 24) (.reg 26)) (.reg 26))
        (P := fun st => st = st3) (Inv := Inv2) 10 0 b (Nat.zero_le _) (by omega) (fun _ => by omega)
        (fun st hs => by
          subst hs
          exact ⟨Expr.eval_const (by omega), by simp, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)],
            memFrame_refl _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
        (fun _ _ _ _ hI => hI.1)
        (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.2.1 4 (by decide)).trans hargs3.r4))
        (fun j _ hj => by
          intro st ω ⟨hr26, hlt26, hfr, hrg⟩
          refine runs_start_le ?_
          refine runs_store_le (x := ps.rangeB_A + j) (v := j)
            (Expr.eval_add (Expr.eval_reg_of_eq ((hlt26 24 (by decide)).trans ((hlt26_3 24 (by decide)).trans ((hoth2 24 (by decide) (by decide)).trans hr24_1))))
              (Expr.eval_reg_of_eq hr26) (by omega))
            (Expr.eval_reg_of_eq hr26) ?_ (by simp only [Expr.size]; omega)
          refine ⟨⟨by simp, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt26 r hr,
            fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha,
            fun i hi => ?_⟩, hr26⟩
          dsimp only
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hrg i (by omega))
      exact hl.conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => by simp only [Expr.size]; omega)
    refine runs_triple_le hloop2 rfl ?_ (by omega)
    rintro (_ | _) st4 h4
    · rcases h4 with ⟨_, hlt26_4, hfr4, hrg4⟩
      have hreg4 : ∀ r < 26, st4.regs r = st1.regs r := fun r hr =>
        (hlt26_4 r hr).trans ((hlt26_3 r hr).trans (hoth2 r (by omega) (by omega)))
      refine ⟨sbArgs_of_eq hargs3 (fun r hr => hlt26_4 r (by omega)),
        (hreg4 12 (by decide)).trans hr12_1,
        (hreg4 13 (by decide)).trans hr13_1,
        (hreg4 14 (by decide)).trans hr14_1,
        (hreg4 15 (by decide)).trans hr15_1,
        fun a ha => by
          rw [hfr4 a (by omega), hfr3 a (by omega), hfr2 a (by omega), hmem1, Function.update_of_ne (by omega)],
        ⟨by rw [hfr4 h0 (Or.inl (by omega)), hfr3 h0 (Or.inl (by omega)), hfr2 h0 (Or.inl (by omega)),
              hmem1, Function.update_self, Finset.length_sort, ← hX_at.1],
          fun idx hidx => by
            have hlen : vs.length = k := by rw [Finset.length_sort, ← hX_at.1]
            rw [hfr4 _ (Or.inl (by omega)), hfr3 _ (Or.inl (by omega))]
            exact hX_copy2 idx hidx⟩,
        fun i hi => by rw [hfr4 _ (Or.inl (by omega))]; exact (hdone3 i hi hi).1,
        fun i hi => by
          have hiw : i * ps.wStride + ps.wStride ≤ nBlocks * ps.wStride := by
            have : (i + 1) * ps.wStride ≤ nBlocks * ps.wStride := Nat.mul_le_mul_right _ (by omega); linarith
          rw [graphAt_mk_iff]
          exact ⟨by rw [hfr4 _ (Or.inl (by omega))]; exact (hdone3 i hi hi).2.1,
            by rw [hfr4 _ (Or.inl (by omega))]; exact (hdone3 i hi hi).2.2,
            fun _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun idx hidx => by simp only [List.length_range] at hidx; rw [List.getElem_range]; exact hrg4 idx hidx⟩
    · exact h4
  rcases htail with ⟨o, st', c2, hrun2, hpost, hc2⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hargs', hr12', hr13', hr14', hr15', hfr', hXlen', hact', hW', hrg'⟩
    refine ⟨st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hrun1, hrun2, rfl⟩), ?_, by omega⟩
    refine ⟨hargs', hr15',
      fun u hu => (hfr' (locA + u) (Or.inl (by omega))).trans (hloc0 u hu),
      by change ps.hPersist ≤ st'.regs 12; rw [hr12'],
      by rw [hr12']; simp only [Nat.zero_mul, Nat.add_zero]; exact le_refl _,
      fun a ha => by rw [hr12'] at ha; exact (hfr' a (Or.inr ha)).trans (hzf0 a (by omega)),
      fun a ha _ _ _ => hfr' a (Or.inl ha),
      Or.inr ⟨hr13', BlockGameState.init,
        sbModelInv_init cp q G X vs b nBlocks z,
        ⟨hXlen', fun i hi => by rw [← hX_at.1]; simpa [BlockGameState.init] using hact' i hi,
          fun _ _ hf => by simp [BlockGameState.init] at hf,
          fun i hi => by rw [← hX_at.1]; simpa [BlockGameState.init, witnessEdges] using hW' i hi,
          by rw [← hX_at.1]; exact hrg'⟩,
        by rw [hr14']; rfl, fun _ h => by simp [BlockGameState.init, callsFakeEdges] at h⟩⟩

end MinCostFlow.ExpanderDecomp
