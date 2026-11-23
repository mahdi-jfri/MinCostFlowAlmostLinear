module

public import MinCostFlow.ExpanderDecomp.OuterProgParamsBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of `computeParamsProc` (`OuterProgParams`)

Completes the staged Word-RAM verification of `computeParamsProc cfg` (`computeParamsProc_spec`)
using the definitions, `coreLevelProc_spec`, and first-stage loop triples from
`OuterProgParamsBase.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM

private lemma computeOuterQ_triple {w M r : ℕ} (cfg : ParamConfig) (pProg : Program) (st₀ : State)
    (h7 : st₀.regs 7 = LParam M) (h11 : st₀.regs 11 = tParam M) (h15 : st₀.regs 15 = PParam cfg M r)
    (hr1 : 1 ≤ r)
    (hQw : QOut cfg M r + 16 < 2 ^ w)
    (hkEw : 16 * cfg.kappa * cfg.E + 16 < 2 ^ w)
    (hAw : 16 * cfg.A + 16 < 2 ^ w) :
    Triple w pProg
      (fun st => st = st₀)
      (computeOuterQStmt cfg)
      (normalPost fun st' =>
        st'.regs 16 = bOut cfg M ∧ st'.regs 19 = Lambda cfg M r ∧
        st'.regs 20 = DOut cfg M r ∧ st'.regs 21 = QOut cfg M r ∧
        st'.regs 22 = 49 * LParam M + 1 ∧
        st'.mem = st₀.mem ∧ ∀ j, j ≤ 15 → st'.regs j = st₀.regs j)
      (fun _ => 120) := by
  rcases param_le_QOut cfg M hr1 with
    ⟨hF1, hFP, hPLam, hROLam, hRO, hdO, _, _, _, hLt, hLamD, hDQ, h49⟩
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hb1 : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have h16kL : 16 * cfg.kappa * (LParam M + 1) ≤ bOut cfg M := by
    unfold bOut
    calc 16 * cfg.kappa * (LParam M + 1) = 16 * cfg.kappa * (LParam M + 1) * 1 := (mul_one _).symm
      _ ≤ 16 * cfg.kappa * (LParam M + 1) * cfg.E := Nat.mul_le_mul_left _ cfg.hE
  have h320b : 320 * bOut cfg M ≤ dOut cfg M := by
    unfold dOut
    calc 320 * bOut cfg M = 320 * bOut cfg M * 1 := (mul_one _).symm
      _ ≤ 320 * bOut cfg M * LParam M := Nat.mul_le_mul_left _ (by omega)
  have h160b : 160 * bOut cfg M ≤ ROut cfg M := by
    unfold ROut
    have h1 : 1 ≤ (dOut cfg M + 1) * LParam M := by nlinarith
    calc 160 * bOut cfg M = 160 * bOut cfg M * 1 := (mul_one _).symm
      _ ≤ 160 * bOut cfg M * ((dOut cfg M + 1) * LParam M) := Nat.mul_le_mul_left _ h1
      _ = 160 * bOut cfg M * (dOut cfg M + 1) * LParam M := by ring
  have h160bd : 160 * bOut cfg M * (dOut cfg M + 1) ≤ ROut cfg M := by
    unfold ROut
    calc 160 * bOut cfg M * (dOut cfg M + 1) = (160 * bOut cfg M * (dOut cfg M + 1)) * 1 := (mul_one _).symm
      _ ≤ (160 * bOut cfg M * (dOut cfg M + 1)) * LParam M := Nat.mul_le_mul_left _ (by omega)
  have h2P : 2 * PParam cfg M r ≤ Lambda cfg M r := by
    unfold Lambda
    have h1 : 1 ≤ tParam M * ROut cfg M * (tParam M + 1) :=
      Nat.mul_pos (Nat.mul_pos (by unfold tParam; omega) (by omega)) (by omega)
    calc 2 * PParam cfg M r = (2 * PParam cfg M r) * 1 := (mul_one _).symm
      _ ≤ (2 * PParam cfg M r) * (tParam M * ROut cfg M * (tParam M + 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1) := by ring
  have h2Pt : 2 * PParam cfg M r * tParam M ≤ Lambda cfg M r := by
    unfold Lambda
    have h1 : 1 ≤ ROut cfg M * (tParam M + 1) := Nat.mul_pos (by omega) (by omega)
    calc 2 * PParam cfg M r * tParam M = (2 * PParam cfg M r * tParam M) * 1 := (mul_one _).symm
      _ ≤ (2 * PParam cfg M r * tParam M) * (ROut cfg M * (tParam M + 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1) := by ring
  have h2PtR : 2 * PParam cfg M r * tParam M * ROut cfg M ≤ Lambda cfg M r := by
    unfold Lambda
    calc 2 * PParam cfg M r * tParam M * ROut cfg M
        = (2 * PParam cfg M r * tParam M * ROut cfg M) * 1 := (mul_one _).symm
      _ ≤ (2 * PParam cfg M r * tParam M * ROut cfg M) * (tParam M + 1) :=
          Nat.mul_le_mul_left _ (by omega)
  have h16At : 16 * cfg.A * tParam M ≤ DOut cfg M r := by
    unfold DOut
    have h1 : 1 ≤ Lambda cfg M r * bOut cfg M := Nat.mul_pos (by omega) hb1
    calc 16 * cfg.A * tParam M = (16 * cfg.A * tParam M) * 1 := (mul_one _).symm
      _ ≤ (16 * cfg.A * tParam M) * (Lambda cfg M r * bOut cfg M) := Nat.mul_le_mul_left _ h1
      _ = 16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M := by ring
  have h16AtL : 16 * cfg.A * tParam M * Lambda cfg M r ≤ DOut cfg M r := by
    unfold DOut
    calc 16 * cfg.A * tParam M * Lambda cfg M r
        = (16 * cfg.A * tParam M * Lambda cfg M r) * 1 := (mul_one _).symm
      _ ≤ (16 * cfg.A * tParam M * Lambda cfg M r) * bOut cfg M := Nat.mul_le_mul_left _ hb1
  have h16kw : 16 * cfg.kappa < 2 ^ w := by
    have : 16 * cfg.kappa ≤ 16 * cfg.kappa * cfg.E := Nat.le_mul_of_pos_right _ cfg.hE
    omega
  have hEw : cfg.E < 2 ^ w := by
    have h1 : 1 ≤ 16 * cfg.kappa := by have := cfg.kappa_pos; omega
    have : cfg.E ≤ 16 * cfg.kappa * cfg.E := by
      calc cfg.E = 1 * cfg.E := (one_mul _).symm
        _ ≤ (16 * cfg.kappa) * cfg.E := Nat.mul_le_mul_right _ h1
    omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h16Aw : 16 * cfg.A < 2 ^ w := by omega
  have h320w : 320 < 2 ^ w := by omega
  have h160w : 160 < 2 ^ w := by omega
  have h49w : 49 < 2 ^ w := by omega
  have ht_le_Q : tParam M ≤ QOut cfg M r := by
    have : tParam M ≤ 2 * PParam cfg M r * tParam M := by
      have h1 : 1 ≤ 2 * PParam cfg M r := by omega
      calc tParam M = 1 * tParam M := (one_mul _).symm
        _ ≤ (2 * PParam cfg M r) * tParam M := Nat.mul_le_mul_right _ h1
    omega
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [computeOuterQStmt]
  have hq1 : Triple w pProg (fun s => s = st)
      (.assign 16 (.bin .mul (.const (16 * cfg.kappa)) (.bin .add (.reg 7) (.const 1))) ;;
       .assign 16 (.bin .mul (.reg 16) (.const cfg.E)) ;;
       .assign 17 (.bin .mul (.const 320) (.reg 16)) ;;
       .assign 17 (.bin .mul (.reg 17) (.reg 7)))
      (normalPost fun s' => s'.regs 16 = bOut cfg M ∧ s'.regs 17 = dOut cfg M ∧
        s'.mem = st.mem ∧ ∀ j, j ≤ 15 → s'.regs j = st.regs j)
      (fun _ => 30) := by
    intro s _ hs; subst hs
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := 16 * cfg.kappa * (LParam M + 1))
      (by simp [Expr.eval, BinOp.eval, h7, h1w, h16kw, (by omega : LParam M + 1 < 2 ^ w),
        (by omega : 16 * cfg.kappa * (LParam M + 1) < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := bOut cfg M)
      (by simp [Expr.eval, BinOp.eval, hEw, (by change bOut cfg M < 2 ^ w; omega :
            16 * cfg.kappa * (LParam M + 1) * cfg.E < 2 ^ w), bOut]) ?_
    refine runs_seq_assign_le (v := 320 * bOut cfg M)
      (by simp [Expr.eval, BinOp.eval, h320w, (by omega : 320 * bOut cfg M < 2 ^ w)]) ?_
    refine runs_assign_le (v := dOut cfg M)
      (by simp [Expr.eval, BinOp.eval, h7, (by change dOut cfg M < 2 ^ w; omega :
            320 * bOut cfg M * LParam M < 2 ^ w), dOut])
      ⟨by simp, by simp, rfl, fun j hj => by simp (disch := omega) only [Function.update_of_ne]⟩
      (by simp [Expr.size])
  refine runs_seq_triple_le hq1 rfl ?_
  intro st1 ⟨h1_16, h1_17, h1_mem, h1_keep⟩
  have h1_7 : st1.regs 7 = LParam M := by rw [h1_keep 7 (by omega)]; exact h7
  have h1_11 : st1.regs 11 = tParam M := by rw [h1_keep 11 (by omega)]; exact h11
  have h1_15 : st1.regs 15 = PParam cfg M r := by rw [h1_keep 15 (by omega)]; exact h15
  have hq2 : Triple w pProg (fun s => s = st1)
      (.assign 18 (.bin .mul (.const 160) (.reg 16)) ;;
       .assign 18 (.bin .mul (.reg 18) (.bin .add (.reg 17) (.const 1))) ;;
       .assign 18 (.bin .mul (.reg 18) (.reg 7)))
      (normalPost fun s' => s'.regs 16 = bOut cfg M ∧ s'.regs 18 = ROut cfg M ∧
        s'.mem = st1.mem ∧ ∀ j, j ≤ 15 → s'.regs j = st1.regs j)
      (fun _ => 25) := by
    intro s _ hs; subst hs
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := 160 * bOut cfg M)
      (by simp [Expr.eval, BinOp.eval, h1_16, h160w, (by omega : 160 * bOut cfg M < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 160 * bOut cfg M * (dOut cfg M + 1))
      (by simp [Expr.eval, BinOp.eval, h1_17, h1w, (by omega : dOut cfg M + 1 < 2 ^ w),
        (by omega : 160 * bOut cfg M * (dOut cfg M + 1) < 2 ^ w)]) ?_
    refine runs_assign_le (v := ROut cfg M)
      (by simp [Expr.eval, BinOp.eval, h1_7, (by change ROut cfg M < 2 ^ w; omega :
            160 * bOut cfg M * (dOut cfg M + 1) * LParam M < 2 ^ w), ROut])
      ⟨by simp [h1_16], by simp, rfl, fun j hj => by simp (disch := omega) only [Function.update_of_ne]⟩
      (by simp [Expr.size])
  refine runs_seq_triple_le hq2 rfl ?_
  intro st2 ⟨h2_16, h2_18, h2_mem, h2_keep⟩
  have h2_7 : st2.regs 7 = LParam M := by rw [h2_keep 7 (by omega)]; exact h1_7
  have h2_11 : st2.regs 11 = tParam M := by rw [h2_keep 11 (by omega)]; exact h1_11
  have h2_15 : st2.regs 15 = PParam cfg M r := by rw [h2_keep 15 (by omega)]; exact h1_15
  have hq3 : Triple w pProg (fun s => s = st2)
      (.assign 19 (.bin .mul (.const 2) (.reg 15)) ;;
       .assign 19 (.bin .mul (.reg 19) (.reg 11)) ;;
       .assign 19 (.bin .mul (.reg 19) (.reg 18)) ;;
       .assign 19 (.bin .mul (.reg 19) (.bin .add (.reg 11) (.const 1))))
      (normalPost fun s' => s'.regs 16 = bOut cfg M ∧ s'.regs 19 = Lambda cfg M r ∧
        s'.mem = st2.mem ∧ ∀ j, j ≤ 15 → s'.regs j = st2.regs j)
      (fun _ => 30) := by
    intro s _ hs; subst hs
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := 2 * PParam cfg M r)
      (by simp [Expr.eval, BinOp.eval, h2w, h2_15, (by omega : 2 * PParam cfg M r < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 2 * PParam cfg M r * tParam M)
      (by simp [Expr.eval, BinOp.eval, h2_11, (by omega : 2 * PParam cfg M r * tParam M < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 2 * PParam cfg M r * tParam M * ROut cfg M)
      (by simp [Expr.eval, BinOp.eval, h2_18,
        (by omega : 2 * PParam cfg M r * tParam M * ROut cfg M < 2 ^ w)]) ?_
    refine runs_assign_le (v := Lambda cfg M r)
      (by simp [Expr.eval, BinOp.eval, h2_11, h1w, (by omega : tParam M + 1 < 2 ^ w),
            (by change Lambda cfg M r < 2 ^ w; omega :
              2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1) < 2 ^ w), Lambda])
      ⟨by simp [h2_16], by simp, rfl, fun j hj => by simp (disch := omega) only [Function.update_of_ne]⟩
      (by simp [Expr.size])
  refine runs_seq_triple_le hq3 rfl ?_
  intro st3 ⟨h3_16, h3_19, h3_mem, h3_keep⟩
  have h3_7 : st3.regs 7 = LParam M := by rw [h3_keep 7 (by omega)]; exact h2_7
  have h3_11 : st3.regs 11 = tParam M := by rw [h3_keep 11 (by omega)]; exact h2_11
  refine runs_seq_assign_le (v := 16 * cfg.A * tParam M)
    (by simp [Expr.eval, BinOp.eval, h3_11, h16Aw, (by omega : 16 * cfg.A * tParam M < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 16 * cfg.A * tParam M * Lambda cfg M r)
    (by simp [Expr.eval, BinOp.eval, h3_19, (by omega : 16 * cfg.A * tParam M * Lambda cfg M r < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := DOut cfg M r)
    (by simp [Expr.eval, BinOp.eval, h3_16, (by change DOut cfg M r < 2 ^ w; omega :
          16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M < 2 ^ w), DOut]) ?_
  refine runs_seq_assign_le (v := QOut cfg M r)
    (by have h2D : 2 * DOut cfg M r < 2 ^ w := by unfold QOut at hQw; omega
        have hQ : 2 * DOut cfg M r + 2 < 2 ^ w := by unfold QOut at hQw; omega
        simp [Expr.eval, BinOp.eval, h2w, h2D, hQ, QOut]) ?_
  refine runs_assign_le (v := 49 * LParam M + 1)
    (by simp [Expr.eval, BinOp.eval, h3_7, h49w, h1w, (by omega : 49 * LParam M < 2 ^ w),
      (by omega : 49 * LParam M + 1 < 2 ^ w)]) ?_ (by simp [Expr.size])
  exact ⟨by simp [h3_16], by simp [h3_19], by simp, by simp, by simp,
    by rw [h3_mem, h2_mem, h1_mem], fun j hj => by
      simp (disch := omega) only [Function.update_of_ne]
      rw [h3_keep j hj, h2_keep j hj, h1_keep j hj]⟩

private lemma store4_triple {w pAddr off r0 r1 r2 r3 v0 v1 v2 v3 : ℕ}
    (pProg : Program) (st₀ : State)
    (h3 : st₀.regs 3 = pAddr)
    (hr0 : st₀.regs r0 = v0) (hr1 : st₀.regs r1 = v1)
    (hr2 : st₀.regs r2 = v2) (hr3 : st₀.regs r3 = v3)
    (hpw : pAddr + off + 4 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (.store (.bin .add (.reg 3) (.const (off + 0))) (.reg r0) ;;
       .store (.bin .add (.reg 3) (.const (off + 1))) (.reg r1) ;;
       .store (.bin .add (.reg 3) (.const (off + 2))) (.reg r2) ;;
       .store (.bin .add (.reg 3) (.const (off + 3))) (.reg r3))
      (normalPost fun s' =>
        s'.regs = st₀.regs ∧
        s'.mem (pAddr + (off + 0)) = v0 ∧
        s'.mem (pAddr + (off + 1)) = v1 ∧
        s'.mem (pAddr + (off + 2)) = v2 ∧
        s'.mem (pAddr + (off + 3)) = v3 ∧
        ∀ a, a < pAddr + off ∨ pAddr + off + 4 ≤ a → s'.mem a = st₀.mem a)
      (fun _ => 32) := by
  intro s _ hs; subst hs
  refine runs_start_le ?_
  refine runs_seq_store_le (x := pAddr + (off + 0)) (v := v0)
    (by simp [Expr.eval, BinOp.eval, h3, (by omega : off < 2 ^ w), (by omega : pAddr + off < 2 ^ w)])
    (by simp [Expr.eval, hr0]) ?_
  refine runs_seq_store_le (x := pAddr + (off + 1)) (v := v1)
    (by simp [Expr.eval, BinOp.eval, h3, (by omega : off + 1 < 2 ^ w), (by omega : pAddr + (off + 1) < 2 ^ w)])
    (by simp [Expr.eval, hr1]) ?_
  refine runs_seq_store_le (x := pAddr + (off + 2)) (v := v2)
    (by simp [Expr.eval, BinOp.eval, h3, (by omega : off + 2 < 2 ^ w), (by omega : pAddr + (off + 2) < 2 ^ w)])
    (by simp [Expr.eval, hr2]) ?_
  refine runs_store_le (x := pAddr + (off + 3)) (v := v3)
    (by simp [Expr.eval, BinOp.eval, h3, (by omega : off + 3 < 2 ^ w), (by omega : pAddr + (off + 3) < 2 ^ w)])
    (by simp [Expr.eval, hr3]) ?_ (by simp [Expr.size])
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  all_goals simp (disch := omega) only [Function.update_self, Function.update_of_ne]

private lemma storeParams_triple {w pAddr : ℕ} (cfg : ParamConfig) (n M r : ℕ) (pProg : Program)
    (st₀ : State)
    (h0 : st₀.regs 0 = n) (h1 : st₀.regs 1 = M) (h2 : st₀.regs 2 = r) (h3 : st₀.regs 3 = pAddr)
    (h5 : st₀.regs 5 = ell M) (h7 : st₀.regs 7 = LParam M) (h9 : st₀.regs 9 = NOf M r)
    (h11 : st₀.regs 11 = tParam M) (h16 : st₀.regs 16 = bOut cfg M)
    (h19 : st₀.regs 19 = Lambda cfg M r) (h20 : st₀.regs 20 = DOut cfg M r)
    (h21 : st₀.regs 21 = QOut cfg M r) (h22 : st₀.regs 22 = 49 * LParam M + 1)
    (hpw : pAddr + 12 < 2 ^ w) :
    Triple w pProg
      (fun st => st = st₀)
      storeParamsStmt
      (normalPost fun st' =>
        OuterParamBlockAt st'.mem pAddr cfg n M r ∧
        ∀ a, a < pAddr ∨ pAddr + 12 ≤ a → st'.mem a = st₀.mem a)
      (fun _ => 110) := by
  intro st ω hst; subst hst
  refine runs_start_le ?_
  dsimp only [storeParamsStmt]
  refine runs_seq_triple_le
    (store4_triple (w := w) (pAddr := pAddr) (off := 0) pProg st h3 h0 h1 h2 h5 (by omega)) rfl ?_
  intro st1 ⟨hr1, hm0, hm1, hm2, hm3, hf1⟩
  have h1_3 : st1.regs 3 = pAddr := by rw [hr1]; exact h3
  have h1_7 : st1.regs 7 = LParam M := by rw [hr1]; exact h7
  have h1_9 : st1.regs 9 = NOf M r := by rw [hr1]; exact h9
  have h1_11 : st1.regs 11 = tParam M := by rw [hr1]; exact h11
  have h1_16 : st1.regs 16 = bOut cfg M := by rw [hr1]; exact h16
  refine runs_seq_triple_le
    (store4_triple (w := w) (pAddr := pAddr) (off := 4) pProg st1 h1_3
      h1_7 h1_9 h1_11 h1_16 (by omega)) rfl ?_
  intro st2 ⟨hr2, hm4, hm5, hm6, hm7, hf2⟩
  have h2_3 : st2.regs 3 = pAddr := by rw [hr2]; exact h1_3
  have h2_19 : st2.regs 19 = Lambda cfg M r := by rw [hr2, hr1]; exact h19
  have h2_20 : st2.regs 20 = DOut cfg M r := by rw [hr2, hr1]; exact h20
  have h2_21 : st2.regs 21 = QOut cfg M r := by rw [hr2, hr1]; exact h21
  have h2_22 : st2.regs 22 = 49 * LParam M + 1 := by rw [hr2, hr1]; exact h22
  rcases store4_triple (w := w) (pAddr := pAddr) (off := 8) pProg st2
      h2_3 h2_19 h2_20 h2_21 h2_22 (by omega) st2 ω rfl with
    ⟨o3, st3, c3, hr3, hq3, hc3⟩
  cases o3 with
  | returned _ => exact False.elim hq3
  | normal =>
    rcases hq3 with ⟨_, hm8, hm9, hm10, hm11, hf3⟩
    refine ⟨.normal, st3, c3, hr3, ?_, by dsimp only at hc3 ⊢; omega⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm8, hm9, hm10, hm11⟩, ?_⟩
    · rw [hf3 _ (by omega), hf2 _ (by omega)]; exact hm0
    · rw [hf3 _ (by omega), hf2 _ (by omega)]; exact hm1
    · rw [hf3 _ (by omega), hf2 _ (by omega)]; exact hm2
    · rw [hf3 _ (by omega), hf2 _ (by omega)]; exact hm3
    · rw [hf3 _ (by omega)]; exact hm4
    · rw [hf3 _ (by omega)]; exact hm5
    · rw [hf3 _ (by omega)]; exact hm6
    · rw [hf3 _ (by omega)]; exact hm7
    · intro a ha
      rw [hf3 a (by omega), hf2 a (by omega), hf1 a (by omega)]

/-- Specification of `computeParamsProc cfg`: writes the 12-word parameter block
`OuterParamBlockAt mem' pAddr cfg n M r` in `O(ell M + r + 1)` steps. -/
theorem computeParamsProc_spec {cfg : ParamConfig} {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [computeParamsProc cfg]) :
    MeetsContract w pProg b (computeParamsContract cfg w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, M, r, pAddr, rfl, hr1, hrl, hpw, hnw, hMw, hQw, ha0w, hkEw, hAw⟩
  rcases param_le_QOut cfg M hr1 with
    ⟨hF1, hFP, hPLam, _, _, _, _, _, _, hLt, hLamD, hDQ, _⟩
  have hN_le : NOf M r ≤ 4 * M + 4 := NOf_le_four_mul M r hr1
  have hexpN_le : max 2 (ceilDiv (ell M) r) ≤ ell M + 1 := by
    have := ceilDiv_le_self (a := ell M) hr1; omega
  have hell1 : 1 ≤ ell M := one_le_ell M
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have hL_le_Q : LParam M ≤ QOut cfg M r := by
    have : tParam M ≤ QOut cfg M r := by
      have : tParam M ≤ FParam cfg M := by
        have h1 := param_le_QOut cfg M hr1; omega
      omega
    omega
  have hell_lt : 4 * ell M < 2 ^ w := by unfold LParam at hL_le_Q; omega
  refine runs_start_le ?_
  dsimp only [computeParamsProc]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le (ell_loop_triple (n := n) (M := M) (r := r) (pAddr := pAddr) pProg mem (by omega))
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp, by simp, rfl⟩ ?_
  intro st1 ⟨h1_0, h1_1, h1_2, h1_3, h1_5, h1_mem⟩
  refine runs_seq_assign_le (v := LParam M)
    (by simp [Expr.eval, BinOp.eval, h1_5, h4w, LParam, hell_lt]) ?_
  refine runs_seq_assign_le (v := ceilDiv (ell M) r)
    (by
      have hcd : (ell M + r - 1) / r < 2 ^ w := by
        have := ceilDiv_le_self (a := ell M) hr1; unfold ceilDiv at this; omega
      simp [Expr.eval, BinOp.eval, h1_5, h1_2, h1w, ceilDiv, (by omega : ell M + r < 2 ^ w),
        (by omega : ell M + r - 1 < 2 ^ w), hcd]) ?_
  have hcond_step :
      Triple w pProg
        (fun st => st.regs 0 = n ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = pAddr ∧
          st.regs 5 = ell M ∧ st.regs 7 = LParam M ∧
          st.regs 8 = ceilDiv (ell M) r ∧ st.mem = mem)
        (.cond (.bin .lt (.reg 8) (.const 2)) (.assign 8 (.const 2)) .nop)
        (normalPost fun st' =>
          st'.regs 0 = n ∧ st'.regs 1 = M ∧ st'.regs 2 = r ∧ st'.regs 3 = pAddr ∧
          st'.regs 5 = ell M ∧ st'.regs 7 = LParam M ∧
          st'.regs 8 = max 2 (ceilDiv (ell M) r) ∧ st'.mem = mem)
        (fun _ => 10) := by
    intro st2 ω ⟨h2_0, h2_1, h2_2, h2_3, h2_5, h2_7, h2_8, h2_mem⟩
    by_cases hlt : ceilDiv (ell M) r < 2
    · set st' : State := { st2 with regs := Function.update st2.regs 8 2 }
      refine ⟨.normal, st', 6, ?_, ?_, Nat.le_add_right 6 4⟩
      · rw [runs_cond_iff]
        refine ⟨1, 2, by simp [Expr.eval, BinOp.eval, h2_8, hlt, h1w, h2w], ?_, by simp [Expr.size]⟩
        simp only [one_ne_zero, ↓reduceIte]
        rw [runs_assign_iff]
        exact ⟨2, by simp [Expr.eval, h2w], rfl, rfl, by simp [Expr.size]⟩
      · exact ⟨by simp [st', h2_0], by simp [st', h2_1], by simp [st', h2_2],
          by simp [st', h2_3], by simp [st', h2_5], by simp [st', h2_7],
          by simp [st', max_eq_left (Nat.le_of_lt hlt)], h2_mem⟩
    · refine ⟨.normal, st2, 5, ?_, ?_, Nat.le_add_right 5 5⟩
      · rw [runs_cond_iff]
        refine ⟨0, 1, by simp [Expr.eval, BinOp.eval, h2_8, hlt, h2w], ?_, by simp [Expr.size]⟩
        simp only [↓reduceIte]
        exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      · exact ⟨h2_0, h2_1, h2_2, h2_3, h2_5, h2_7,
          by rw [h2_8, max_eq_right (Nat.le_of_not_lt hlt)], h2_mem⟩
  refine runs_seq_triple_le hcond_step
    ⟨by simp [h1_0], by simp [h1_1], by simp [h1_2], by simp [h1_3],
      by simp [h1_5], by simp, by simp, h1_mem⟩ ?_
  intro st3 ⟨h3_0, h3_1, h3_2, h3_3, h3_5, h3_7, h3_8, h3_mem⟩
  refine runs_seq_assign_le (by eval_expr) ?_
  have hpow2 := pow2_loop_triple (w := w) (expN := max 2 (ceilDiv (ell M) r)) pProg
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = pAddr ∧
      st.regs 5 = ell M ∧ st.regs 7 = LParam M ∧ st.regs 8 = max 2 (ceilDiv (ell M) r) ∧
      st.regs 9 = 1 ∧ st.mem = mem)
    (rKeep := fun j => j ≤ 7)
    (fun _ h => h.2.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2.2.1)
    (fun j hj => by omega) (by unfold NOf at hN_le; omega)
  refine runs_seq_triple_le hpow2
    ⟨by simp [h3_0], by simp [h3_1], by simp [h3_2], by simp [h3_3], by simp [h3_5],
      by simp [h3_7], by simp [h3_8], by simp, h3_mem⟩ ?_
  intro st4 ⟨h4_9, st4₀, h4₀, h4_mem, h4_keep⟩
  have h4_0 : st4.regs 0 = n := by rw [h4_keep 0 (by omega)]; exact h4₀.1
  have h4_1 : st4.regs 1 = M := by rw [h4_keep 1 (by omega)]; exact h4₀.2.1
  have h4_2 : st4.regs 2 = r := by rw [h4_keep 2 (by omega)]; exact h4₀.2.2.1
  have h4_3 : st4.regs 3 = pAddr := by rw [h4_keep 3 (by omega)]; exact h4₀.2.2.2.1
  have h4_5 : st4.regs 5 = ell M := by rw [h4_keep 5 (by omega)]; exact h4₀.2.2.2.2.1
  have h4_7 : st4.regs 7 = LParam M := by rw [h4_keep 7 (by omega)]; exact h4₀.2.2.2.2.2.1
  have h4_mem' : st4.mem = mem := by rw [h4_mem, h4₀.2.2.2.2.2.2.2.2]
  refine runs_seq_triple_le (computeCoreF_triple (M := M) cfg pProg st4 h4_7 (by omega) ha0w) rfl ?_
  intro st5 ⟨h5_11, h5_14, h5_15, h5_mem, h5_keep⟩
  have h5_0 : st5.regs 0 = n := by rw [h5_keep 0 (by omega)]; exact h4_0
  have h5_1 : st5.regs 1 = M := by rw [h5_keep 1 (by omega)]; exact h4_1
  have h5_2 : st5.regs 2 = r := by rw [h5_keep 2 (by omega)]; exact h4_2
  have h5_3 : st5.regs 3 = pAddr := by rw [h5_keep 3 (by omega)]; exact h4_3
  have h5_5 : st5.regs 5 = ell M := by rw [h5_keep 5 (by omega)]; exact h4_5
  have h5_7 : st5.regs 7 = LParam M := by rw [h5_keep 7 (by omega)]; exact h4_7
  have h5_9 : st5.regs 9 = NOf M r := by rw [h5_keep 9 (by omega)]; exact h4_9
  have h5_mem' : st5.mem = mem := by rw [h5_mem, h4_mem']
  have hpowF := powF_loop_triple (w := w) (r := r) (F := FParam cfg M) pProg
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = pAddr ∧
      st.regs 5 = ell M ∧ st.regs 7 = LParam M ∧ st.regs 9 = NOf M r ∧
      st.regs 11 = tParam M ∧ st.regs 14 = FParam cfg M ∧ st.regs 15 = 1 ∧ st.mem = mem)
    (rKeep := fun j => j ≤ 9 ∨ j = 11)
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2.2.2.2.1)
    (fun j hj => by omega) hF1 (by unfold PParam at hPLam; omega) (by unfold LParam at hL_le_Q; omega)
  refine runs_seq_triple_le hpowF
    ⟨h5_0, h5_1, h5_2, h5_3, h5_5, h5_7, h5_9, h5_11, h5_14, h5_15, h5_mem'⟩ ?_
  intro st6 ⟨h6_15, st6₀, h6₀, h6_mem, h6_keep⟩
  have h6_0 : st6.regs 0 = n := by rw [h6_keep 0 (by omega)]; exact h6₀.1
  have h6_1 : st6.regs 1 = M := by rw [h6_keep 1 (by omega)]; exact h6₀.2.1
  have h6_2 : st6.regs 2 = r := by rw [h6_keep 2 (by omega)]; exact h6₀.2.2.1
  have h6_3 : st6.regs 3 = pAddr := by rw [h6_keep 3 (by omega)]; exact h6₀.2.2.2.1
  have h6_5 : st6.regs 5 = ell M := by rw [h6_keep 5 (by omega)]; exact h6₀.2.2.2.2.1
  have h6_7 : st6.regs 7 = LParam M := by rw [h6_keep 7 (by omega)]; exact h6₀.2.2.2.2.2.1
  have h6_9 : st6.regs 9 = NOf M r := by rw [h6_keep 9 (by omega)]; exact h6₀.2.2.2.2.2.2.1
  have h6_11 : st6.regs 11 = tParam M := by rw [h6_keep 11 (by omega)]; exact h6₀.2.2.2.2.2.2.2.1
  have h6_mem' : st6.mem = mem := by rw [h6_mem, h6₀.2.2.2.2.2.2.2.2.2.2]
  refine runs_seq_triple_le
    (computeOuterQ_triple (M := M) (r := r) cfg pProg st6 h6_7 h6_11 h6_15 hr1 hQw hkEw hAw) rfl ?_
  intro st7 ⟨h7_16, h7_19, h7_20, h7_21, h7_22, h7_mem, h7_keep⟩
  have h7_0 : st7.regs 0 = n := by rw [h7_keep 0 (by omega)]; exact h6_0
  have h7_1 : st7.regs 1 = M := by rw [h7_keep 1 (by omega)]; exact h6_1
  have h7_2 : st7.regs 2 = r := by rw [h7_keep 2 (by omega)]; exact h6_2
  have h7_3 : st7.regs 3 = pAddr := by rw [h7_keep 3 (by omega)]; exact h6_3
  have h7_5 : st7.regs 5 = ell M := by rw [h7_keep 5 (by omega)]; exact h6_5
  have h7_7 : st7.regs 7 = LParam M := by rw [h7_keep 7 (by omega)]; exact h6_7
  have h7_9 : st7.regs 9 = NOf M r := by rw [h7_keep 9 (by omega)]; exact h6_9
  have h7_11 : st7.regs 11 = tParam M := by rw [h7_keep 11 (by omega)]; exact h6_11
  have h7_mem' : st7.mem = mem := by rw [h7_mem, h6_mem']
  refine runs_seq_triple_le
    (storeParams_triple cfg n M r pProg st7 h7_0 h7_1 h7_2 h7_3 h7_5 h7_7 h7_9 h7_11
      h7_16 h7_19 h7_20 h7_21 h7_22 hpw) rfl ?_
  intro st8 ⟨hblk, hframe⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · dsimp [computeParamsContract, Outcome.value]
    exact ⟨rfl, hblk, fun a ha => by rw [hframe a ha, h7_mem']⟩
  · simp only [computeParamsContract, computeParamsCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega

end MinCostFlow.ExpanderDecomp
