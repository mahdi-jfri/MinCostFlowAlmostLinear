module

public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Procedure for the `CoreParamsAt` Table (`CoreOuterParams`)

Provides a standalone deterministic Word-RAM procedure `writeCoreParamsProc` taking
`args = [M, r, pAddr]` that computes `coreParamsOf ParamConfig.default M r` (`N`, `L`, `Δ`, `r`,
`P_0..P_r`, `D_0..D_r`, `N^0..N^r`) and writes `CoreParamsAt mem' pAddr (coreParamsOf
ParamConfig.default M r) r` in `O(ell M + r + 1)` steps without modifying memory outside
`[pAddr, pAddr + coreParamsSize r)`.

Main results:
* `writeCoreParamsProc_noRand`: determinism (`NoRand`).
* `writeCoreParamsProc_runs`: direct `Runs` lemma on `startState [M, r, pAddr] mem pos`.
* `writeCoreParamsProc_meetsContract`: `MeetsContract` for `writeCoreParamsContract w`.
* `writeCoreParamsContract_pre_example`: non-vacuity witness for `writeCoreParamsContract`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Cost Bound, Procedure, and Contract -/

/-- Step-count bound for `writeCoreParamsProc`: linear in `ell M + r`. -/
def writeCoreParamsCost (M r : ℕ) : ℕ :=
  70 * (ell M + r) + 300

/-- Stage 1: from `reg 0 = M`, computes `reg 4 = ell M` and `reg 6 = LParam M = 4 * ell M`. -/
def writeCoreParamsEllStmt : Stmt :=
  seqStmts
    [ .assign 3 (.bin .add (.bin .mul (.const 2) (.reg 0)) (.const 2))
    , .assign 4 (.const 0)
    , .assign 5 (.const 1)
    , .loop (.bin .lt (.reg 5) (.reg 3))
        (seqStmts
          [ .assign 5 (.bin .mul (.const 2) (.reg 5))
          , .assign 4 (.bin .add (.reg 4) (.const 1)) ])
    , .assign 6 (.bin .mul (.const 4) (.reg 4)) ]

/-- Stage 2: from `reg 4 = ell M` and `reg 1 = r`, computes
`reg 8 = NOf M r = 2 ^ max 2 (ceilDiv (ell M) r)`. -/
def writeCoreParamsNStmt : Stmt :=
  seqStmts
    [ .assign 7 (.bin .div (.bin .sub (.bin .add (.reg 4) (.reg 1)) (.const 1)) (.reg 1))
    , .cond (.bin .lt (.reg 7) (.const 2)) (.assign 7 (.const 2)) .nop
    , .assign 8 (.const 1)
    , forRange 9 (.const 0) (.reg 7)
        (.assign 8 (.bin .mul (.const 2) (.reg 8))) ]

/-- Stage 3: from `reg 1 = r`, `reg 2 = pAddr`, `reg 6 = LParam M`, `reg 8 = NOf M r`,
computes `Δ`, `dCore`, `RCore`, `FParam`, `A * Δ` for `ParamConfig.default`, and writes the full
`CoreParamsAt` block at `[pAddr, pAddr + coreParamsSize r)`. -/
def writeCoreParamsFillStmt : Stmt :=
  seqStmts
    [ .assign 9 (.bin .mul (.const 1024) (.reg 6))
    , .assign 10 (.bin .mul (.bin .mul (.const 3200) (.reg 9)) (.reg 6))
    , .assign 11 (.bin .mul (.bin .mul (.bin .mul (.const 1600) (.reg 9))
        (.bin .add (.reg 10) (.const 1))) (.reg 6))
    , .assign 12 (.bin .mul (.bin .mul (.bin .mul (.const 23040) (.reg 9)) (.reg 9)) (.reg 11))
    , .assign 13 (.bin .mul (.const 240) (.reg 9))
    , .store (.reg 2) (.reg 8)
    , .store (.bin .add (.reg 2) (.const 1)) (.reg 6)
    , .store (.bin .add (.reg 2) (.const 2)) (.reg 9)
    , .store (.bin .add (.reg 2) (.const 3)) (.reg 1)
    , .assign 14 (.const 1)
    , .assign 15 (.const 1)
    , .store (.bin .add (.reg 2) (.const 4)) (.reg 14)
    , .store (.bin .add (.bin .add (.reg 2) (.const 5)) (.reg 1)) (.reg 13)
    , .store (.bin .add (.bin .add (.reg 2) (.const 6)) (.bin .mul (.const 2) (.reg 1))) (.reg 15)
    , forRange 3 (.const 0) (.reg 1)
        (seqStmts
          [ .assign 14 (.bin .mul (.reg 14) (.reg 12))
          , .assign 16 (.bin .mul (.reg 13) (.reg 14))
          , .assign 15 (.bin .mul (.reg 15) (.reg 8))
          , .assign 4 (.bin .add (.reg 3) (.const 1))
          , .store (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 4)) (.reg 14)
          , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 5)) (.reg 1)) (.reg 4))
              (.reg 16)
          , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 6))
              (.bin .mul (.const 2) (.reg 1))) (.reg 4)) (.reg 15) ]) ]

/-- Standalone deterministic Word-RAM procedure writing `CoreParamsAt mem' pAddr
(coreParamsOf ParamConfig.default M r) r` from `args = [M, r, pAddr]`. -/
def writeCoreParamsProc : Stmt :=
  seqStmts
    [ writeCoreParamsEllStmt
    , writeCoreParamsNStmt
    , writeCoreParamsFillStmt
    , .ret (.const 0) ]

/-- Contract for `writeCoreParamsProc`: `args = [M, r, pAddr]`. Requires `1 ≤ r` and word-size
headroom for `pAddr + coreParamsSize r`, `(NOf M r) ^ r`, and `DCore ParamConfig.default M r`;
writes `CoreParamsAt mem' pAddr (coreParamsOf ParamConfig.default M r) r`, preserves all memory
outside `[pAddr, pAddr + coreParamsSize r)`, and runs in `writeCoreParamsCost M r` steps. -/
noncomputable def writeCoreParamsContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ M r pAddr : ℕ,
      args = [M, r, pAddr] ∧
      1 ≤ r ∧
      pAddr + coreParamsSize r < 2 ^ w ∧
      (NOf M r) ^ r < 2 ^ w ∧
      DCore ParamConfig.default M r < 2 ^ w
  post args mem _v mem' :=
    ∀ M r pAddr : ℕ,
      args = [M, r, pAddr] →
      1 ≤ r →
      pAddr + coreParamsSize r < 2 ^ w →
      (NOf M r) ^ r < 2 ^ w →
      DCore ParamConfig.default M r < 2 ^ w →
      CoreParamsAt mem' pAddr (coreParamsOf ParamConfig.default M r) r ∧
      (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → mem' a = mem a)
  cost args _ :=
    writeCoreParamsCost (args.getD 0 0) (args.getD 1 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Determinism and Arithmetic Bounds -/

theorem writeCoreParamsProc_noRand : writeCoreParamsProc.NoRand := by
  simp [writeCoreParamsProc, writeCoreParamsEllStmt, writeCoreParamsNStmt,
    writeCoreParamsFillStmt, seqStmts, forRange, forUp, Stmt.NoRand]

private lemma ell_le_mul_ceilDiv (a r : ℕ) (hr : 1 ≤ r) : a ≤ r * ceilDiv a r := by
  unfold ceilDiv
  have hdm := Nat.div_add_mod (a + r - 1) r
  have hmod : (a + r - 1) % r < r := Nat.mod_lt _ (by omega)
  omega

private lemma two_pow_ell_le_NOf_pow (M r : ℕ) (hr : 1 ≤ r) :
    2 ^ ell M ≤ (NOf M r) ^ r := by
  unfold NOf
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have h1 : ell M ≤ r * ceilDiv (ell M) r := ell_le_mul_ceilDiv (ell M) r hr
  have h2 : ceilDiv (ell M) r ≤ max 2 (ceilDiv (ell M) r) := le_max_right _ _
  rw [Nat.mul_comm]
  exact le_trans h1 (Nat.mul_le_mul_left r h2)

private lemma ceilDiv_ell_le (M r : ℕ) (hr : 1 ≤ r) : ceilDiv (ell M) r ≤ ell M := by
  unfold ceilDiv
  have h1 : ell M + r - 1 ≤ r * ell M + (r - 1) := by
    have : ell M ≤ r * ell M := Nat.le_mul_of_pos_left _ hr
    omega
  have h2 : ell M + r - 1 < r * (ell M + 1) := by
    have : r * (ell M + 1) = r * ell M + r := by ring
    omega
  have h3 : (ell M + r - 1) / r < ell M + 1 := Nat.div_lt_of_lt_mul h2
  omega

private lemma FParam_default_pos (M : ℕ) : 1 ≤ FParam ParamConfig.default M := by
  have hell : 1 ≤ ell M := one_le_ell M
  have hL : 4 ≤ LParam M := by unfold LParam; omega
  have hΔ : 4096 ≤ deltaParam M := by unfold deltaParam tParam; omega
  have hR : 1 ≤ RCore M := by
    unfold RCore
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  unfold FParam ParamConfig.default
  dsimp only
  have h1 : 1 ≤ 1920 * 12 * (deltaParam M) ^ 2 := by nlinarith
  exact Nat.mul_pos h1 hR

private lemma coreParam_default_bounds {M r pAddr w : ℕ} (hr : 1 ≤ r)
    (hp_w : pAddr + coreParamsSize r < 2 ^ w)
    (hNr_w : (NOf M r) ^ r < 2 ^ w)
    (hDr_w : DCore ParamConfig.default M r < 2 ^ w) :
    983040 * ell M ≤ DCore ParamConfig.default M r ∧
    240 * deltaParam M ≤ DCore ParamConfig.default M r ∧
    FParam ParamConfig.default M ≤ DCore ParamConfig.default M r ∧
    RCore M ≤ FParam ParamConfig.default M ∧
    dCore M + 1 ≤ RCore M ∧
    ell M + r < 2 ^ w ∧
    2 * M + 2 < 2 ^ w ∧
    NOf M r < 2 ^ w := by
  have hell : 1 ≤ ell M := one_le_ell M
  have hL : LParam M = 4 * ell M := rfl
  have hΔ : deltaParam M = 1024 * LParam M := rfl
  have hF1 : 1 ≤ FParam ParamConfig.default M := FParam_default_pos M
  have hFr1 : 1 ≤ (FParam ParamConfig.default M) ^ r := Nat.one_le_pow r _ hF1
  have hF_le_Fr : FParam ParamConfig.default M ≤ (FParam ParamConfig.default M) ^ r := by
    calc FParam ParamConfig.default M = (FParam ParamConfig.default M) ^ 1 := (pow_one _).symm
      _ ≤ (FParam ParamConfig.default M) ^ r := Nat.pow_le_pow_right hF1 hr
  have hDr_eq : DCore ParamConfig.default M r =
      240 * deltaParam M * (FParam ParamConfig.default M) ^ r := by
    unfold DCore PParam ParamConfig.A ParamConfig.default
    rfl
  have h240Δ_le_Dr : 240 * deltaParam M ≤ DCore ParamConfig.default M r := by
    rw [hDr_eq]; exact Nat.le_mul_of_pos_right _ hFr1
  have h983040 : 983040 * ell M ≤ DCore ParamConfig.default M r := by
    have : 983040 * ell M = 240 * deltaParam M := by rw [hΔ, hL]; ring
    omega
  have hF_le_Dr : FParam ParamConfig.default M ≤ DCore ParamConfig.default M r := by
    rw [hDr_eq]
    have h240_pos : 1 ≤ 240 * deltaParam M := by rw [hΔ, hL]; omega
    exact le_trans hF_le_Fr (Nat.le_mul_of_pos_left _ h240_pos)
  have hRc_le_F : RCore M ≤ FParam ParamConfig.default M := by
    unfold FParam ParamConfig.default; dsimp only
    have hpos : 1 ≤ 1920 * 12 * (deltaParam M) ^ 2 := by rw [hΔ, hL]; nlinarith
    exact Nat.le_mul_of_pos_left _ hpos
  have hdc1_le_Rc : dCore M + 1 ≤ RCore M := by
    unfold RCore
    have h1 : 1 ≤ 1600 * deltaParam M := by rw [hΔ, hL]; omega
    have h2 : 1 ≤ LParam M := by rw [hL]; omega
    calc dCore M + 1 ≤ 1600 * deltaParam M * (dCore M + 1) := Nat.le_mul_of_pos_left _ h1
      _ ≤ 1600 * deltaParam M * (dCore M + 1) * LParam M := Nat.le_mul_of_pos_right _ h2
  have hell_add_r : ell M + r < 2 ^ w := by unfold coreParamsSize at hp_w; omega
  have h2M2 : 2 * M + 2 < 2 ^ w := by
    have h1 : 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by decide) (2 * M + 2)
    have h2 : 2 ^ ell M ≤ (NOf M r) ^ r := two_pow_ell_le_NOf_pow M r hr
    omega
  have hN_le_Nr : NOf M r ≤ (NOf M r) ^ r := by
    have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
    calc NOf M r = (NOf M r) ^ 1 := (pow_one _).symm
      _ ≤ (NOf M r) ^ r := Nat.pow_le_pow_right hN1 hr
  exact ⟨h983040, h240Δ_le_Dr, hF_le_Dr, hRc_le_F, hdc1_le_Rc, hell_add_r, h2M2,
    lt_of_le_of_lt hN_le_Nr hNr_w⟩

/-! ## 3. Stage Triples -/

private lemma writeCoreParamsEll_triple {w M r pAddr : ℕ} {p : Program}
    (hr : 1 ≤ r) (hp_w : pAddr + coreParamsSize r < 2 ^ w)
    (hNr_w : (NOf M r) ^ r < 2 ^ w) (hDr_w : DCore ParamConfig.default M r < 2 ^ w)
    (st₀ : State) (hr0 : st₀.regs 0 = M) (hr1 : st₀.regs 1 = r) (hr2 : st₀.regs 2 = pAddr) :
    Triple w p (fun st => st = st₀) writeCoreParamsEllStmt
      (normalPost fun st' =>
        st'.mem = st₀.mem ∧
        st'.regs 1 = r ∧
        st'.regs 2 = pAddr ∧
        st'.regs 4 = ell M ∧
        st'.regs 6 = LParam M)
      (fun _ => 20 * ell M + 30) := by
  have hb := coreParam_default_bounds hr hp_w hNr_w hDr_w
  have hell : 1 ≤ ell M := one_le_ell M
  have h2pow_ell_lt : 2 ^ ell M < 2 ^ w :=
    lt_of_le_of_lt (two_pow_ell_le_NOf_pow M r hr) hNr_w
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hL_lt : LParam M < 2 ^ w := by unfold LParam; omega
  have hloop :
      Triple w p
        (fun st => st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
          st.regs 3 = 2 * M + 2 ∧ st.regs 4 = 0 ∧ st.regs 5 = 1)
        (.loop (.bin .lt (.reg 5) (.reg 3))
          (seqStmts
            [ .assign 5 (.bin .mul (.const 2) (.reg 5))
            , .assign 4 (.bin .add (.reg 4) (.const 1)) ]))
        (normalPost fun st' =>
          st'.mem = st₀.mem ∧ st'.regs 1 = r ∧ st'.regs 2 = pAddr ∧ st'.regs 4 = ell M)
        (fun _ => 20 * ell M + 4) := by
    let Inv : List Unit → State → Prop := fun xs st =>
      xs.length ≤ ell M ∧
      st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
      st.regs 3 = 2 * M + 2 ∧
      st.regs 4 = ell M - xs.length ∧
      st.regs 5 = 2 ^ (ell M - xs.length)
    have hll := Triple.loop_list (w := w) (p := p) (β := Unit)
      (e := .bin .lt (.reg 5) (.reg 3))
      (body := seqStmts
        [ .assign 5 (.bin .mul (.const 2) (.reg 5))
        , .assign 4 (.bin .add (.reg 4) (.const 1)) ])
      (Inv := Inv)
      (Q := normalPost fun st' =>
        st'.mem = st₀.mem ∧ st'.regs 1 = r ∧ st'.regs 2 = pAddr ∧ st'.regs 4 = ell M)
      (bodyCost := fun _ => 14)
      (fun st ⟨_, hmem, h1, h2, h3, h4, h5⟩ => by
        simp only [List.length_nil, Nat.sub_zero] at h4 h5
        have hle : 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by decide) (2 * M + 2)
        refine ⟨Expr.eval_lt_false (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h3) hle
          (by omega), hmem, h1, h2, h4⟩)
      (fun _ xs st ⟨hlen, hmem, h1, h2, h3, h4, h5⟩ => by
        set k := ell M - (xs.length + 1)
        have hlen' : xs.length + 1 ≤ ell M := by simpa using hlen
        have hk_lt : k < ell M := by omega
        have hpow_lt : 2 ^ k < 2 * M + 2 := by
          by_contra hge
          have hclog : ell M ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
          omega
        have h2pow_k1 : 2 * 2 ^ k < 2 ^ w := by
          have : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
          rw [this]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) h2pow_ell_lt
        refine ⟨1, Expr.eval_lt_true (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h3) hpow_lt
          (by omega), by decide, ?_⟩
        intro s ω hs; subst hs
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := 2 * 2 ^ k)
          (Expr.eval_mul (Expr.eval_const hw2) (Expr.eval_reg_of_eq h5) h2pow_k1) ?_
        refine runs_assign_le (v := k + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h4, k])) (Expr.eval_const (by omega))
            (by omega)) ?_ (by simp [Expr.size])
        refine ⟨by omega, hmem, by simp [h1], by simp [h2], by simp [h3], by simp [k]; omega, ?_⟩
        have heq : ell M - xs.length = k + 1 := by omega
        simp [heq, pow_succ, Nat.mul_comm])
      (List.replicate (ell M) ())
    refine hll.conseq ?_ (fun _ _ h => h) ?_
    · intro st ⟨hmem, h1, h2, h3, h4, h5⟩
      exact ⟨by simp, hmem, h1, h2, h3, by simpa using h4, by simpa using h5⟩
    · intro _ _
      simp [Expr.size]; omega
  intro st ω hs; subst hs
  refine runs_start_le ?_
  dsimp only [writeCoreParamsEllStmt, seqStmts]
  refine runs_seq_assign_le (v := 2 * M + 2)
    (Expr.eval_add
      (Expr.eval_mul (Expr.eval_const hw2) (Expr.eval_reg_of_eq hr0) (by omega))
      (Expr.eval_const hw2) hb.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨rfl, by simp [hr1], by simp [hr2], by simp, by simp, by simp⟩ ?_
  intro st1 ⟨hmem1, h1, h2, h4⟩
  refine runs_assign_le (v := 4 * ell M)
    (Expr.eval_mul (Expr.eval_const hw4) (Expr.eval_reg_of_eq h4) hL_lt) ?_
    (by simp [Expr.size]; omega)
  exact ⟨hmem1, by simp [h1], by simp [h2], by simp [h4], by simp [LParam]⟩

private lemma writeCoreParamsN_triple {w M r pAddr : ℕ} {p : Program}
    (hr : 1 ≤ r) (hp_w : pAddr + coreParamsSize r < 2 ^ w)
    (hNr_w : (NOf M r) ^ r < 2 ^ w) (hDr_w : DCore ParamConfig.default M r < 2 ^ w)
    (st₀ : State) (hr1 : st₀.regs 1 = r) (hr2 : st₀.regs 2 = pAddr)
    (hr4 : st₀.regs 4 = ell M) (hr6 : st₀.regs 6 = LParam M) :
    Triple w p (fun st => st = st₀) writeCoreParamsNStmt
      (normalPost fun st' =>
        st'.mem = st₀.mem ∧
        st'.regs 1 = r ∧
        st'.regs 2 = pAddr ∧
        st'.regs 6 = LParam M ∧
        st'.regs 8 = NOf M r)
      (fun _ => 25 * ell M + 90) := by
  have hb := coreParam_default_bounds hr hp_w hNr_w hDr_w
  set eN : ℕ := max 2 (ceilDiv (ell M) r)
  have heN_le : eN ≤ ell M + 2 := by have := ceilDiv_ell_le M r hr; dsimp only [eN]; omega
  have heN_lt : eN < 2 ^ w := by omega
  have hN_eq : NOf M r = 2 ^ eN := rfl
  have hN_lt : 2 ^ eN < 2 ^ w := by rw [← hN_eq]; exact hb.2.2.2.2.2.2.2
  let Inv : ℕ → State → Prop := fun j st =>
    st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
    st.regs 6 = LParam M ∧ st.regs 7 = eN ∧ st.regs 8 = 2 ^ j ∧ st.regs 9 = j
  have hfor :
      Triple w p
        (fun st => st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
          st.regs 6 = LParam M ∧ st.regs 7 = eN ∧ st.regs 8 = 1)
        (forRange 9 (.const 0) (.reg 7) (.assign 8 (.bin .mul (.const 2) (.reg 8))))
        (normalPost fun st' =>
          st'.mem = st₀.mem ∧ st'.regs 1 = r ∧ st'.regs 2 = pAddr ∧
          st'.regs 6 = LParam M ∧ st'.regs 8 = NOf M r)
        (fun _ => 20 * eN + 12) := by
    have hfr := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 7)
      (body := .assign 8 (.bin .mul (.const 2) (.reg 8)))
      (P := fun st => st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
        st.regs 6 = LParam M ∧ st.regs 7 = eN ∧ st.regs 8 = 1)
      (Inv := Inv) 6 0 eN (Nat.zero_le eN) (by omega) (fun _ => by omega)
      (fun st ⟨hmem, h1, h2, h6, h7, h8⟩ =>
        ⟨Expr.eval_const (by omega), hmem, by simp [h1], by simp [h2], by simp [h6], by simp [h7],
          by simp [h8], by simp⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2)
      (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.1)
      (fun j _ hj => by
        intro st ω ⟨hmem, h1, h2, h6, h7, h8, h9⟩
        have h2pow : 2 * 2 ^ j < 2 ^ w := by
          have : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ, Nat.mul_comm]
          rw [this]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hN_lt
        refine runs_start_le ?_
        refine runs_assign_le (v := 2 * 2 ^ j)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h8) h2pow) ?_
          (by simp [Expr.size])
        refine ⟨⟨hmem, by simp [h1], by simp [h2], by simp [h6], by simp [h7],
          by simp [pow_succ, Nat.mul_comm], by simp⟩, by simp [h9]⟩)
    refine hfr.conseq (fun _ h => h) ?_ (fun _ _ => by simp [Expr.size]; omega)
    rintro (_ | v) st' hI
    · exact ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, by rw [hN_eq]; exact hI.2.2.2.2.2.1⟩
    · exact hI.elim
  have hcond :
      Triple w p
        (fun st => st.mem = st₀.mem ∧ st.regs 1 = r ∧ st.regs 2 = pAddr ∧
          st.regs 6 = LParam M ∧ st.regs 7 = ceilDiv (ell M) r)
        (.cond (.bin .lt (.reg 7) (.const 2)) (.assign 7 (.const 2)) .nop)
        (normalPost fun st' =>
          st'.mem = st₀.mem ∧ st'.regs 1 = r ∧ st'.regs 2 = pAddr ∧
          st'.regs 6 = LParam M ∧ st'.regs 7 = eN)
        (fun _ => 10) := by
    intro s ω ⟨hmem, h1, h2, h6, h7⟩
    refine runs_start_le ?_
    refine runs_cond_le
      (Expr.eval_lt_op (Expr.eval_reg_of_eq h7) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · intro hne
      have hlt : ceilDiv (ell M) r < 2 := by by_contra h; simp [h] at hne
      have heN_two : eN = 2 := by dsimp only [eN]; omega
      refine runs_assign_le (v := 2) (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
      exact ⟨hmem, by simp [h1], by simp [h2], by simp [h6], by simp [heN_two]⟩
    · intro hz
      have hge : 2 ≤ ceilDiv (ell M) r := by by_contra h; simp [Nat.lt_of_not_ge h] at hz
      have heN_eq : eN = ceilDiv (ell M) r := by dsimp only [eN]; omega
      exact runs_nop_le ⟨hmem, h1, h2, h6, by rw [heN_eq]; exact h7⟩ (by simp [Expr.size])
  intro st ω hs; subst hs
  refine runs_start_le ?_
  dsimp only [writeCoreParamsNStmt, seqStmts]
  refine runs_seq_assign_le (v := ceilDiv (ell M) r)
    (Expr.eval_div
      (Expr.eval_sub
        (Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_reg_of_eq hr1) hb.2.2.2.2.2.1)
        (Expr.eval_const (by omega)) hb.2.2.2.2.2.1)
      (Expr.eval_reg_of_eq hr1)
      (lt_of_le_of_lt (Nat.sub_le _ _) hb.2.2.2.2.2.1)) ?_
  refine runs_seq_triple_le hcond ⟨rfl, by simp [hr1], by simp [hr2], by simp [hr6], by simp⟩ ?_
  intro st1 ⟨hmem1, h1, h2, h6, h7⟩
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
  refine runs_triple_le hfor ⟨hmem1, by simp [h1], by simp [h2], by simp [h6], by simp [h7], by simp⟩
    (fun o s' h => h) (by simp [Expr.size]; omega)

private lemma writeCoreParamsFill_triple {w M r pAddr : ℕ} {p : Program}
    (hr : 1 ≤ r) (hp_w : pAddr + coreParamsSize r < 2 ^ w)
    (hNr_w : (NOf M r) ^ r < 2 ^ w) (hDr_w : DCore ParamConfig.default M r < 2 ^ w)
    (st₀ : State) (hr1 : st₀.regs 1 = r) (hr2 : st₀.regs 2 = pAddr)
    (hr6 : st₀.regs 6 = LParam M) (hr8 : st₀.regs 8 = NOf M r) :
    Triple w p (fun st => st = st₀) writeCoreParamsFillStmt
      (normalPost fun st' =>
        CoreParamsAt st'.mem pAddr (coreParamsOf ParamConfig.default M r) r ∧
        (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st'.mem a = st₀.mem a))
      (fun _ => 70 * r + 170) := by
  have hb := coreParam_default_bounds hr hp_w hNr_w hDr_w
  set cp := coreParamsOf ParamConfig.default M r
  have hell : 1 ≤ ell M := one_le_ell M
  have hL_ge4 : 4 ≤ LParam M := by unfold LParam; omega
  have hΔ_ge : 4096 ≤ deltaParam M := by unfold deltaParam tParam; omega
  have hF1 : 1 ≤ FParam ParamConfig.default M := FParam_default_pos M
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hF_lt : FParam ParamConfig.default M < 2 ^ w := lt_of_le_of_lt hb.2.2.1 hDr_w
  have hRc_lt : RCore M < 2 ^ w := lt_of_le_of_lt hb.2.2.2.1 hF_lt
  have hdc1_lt : dCore M + 1 < 2 ^ w := lt_of_le_of_lt hb.2.2.2.2.1 hRc_lt
  have hdc_lt : 3200 * deltaParam M * LParam M < 2 ^ w := by
    change dCore M < 2 ^ w; omega
  have hΔ_lt : deltaParam M < 2 ^ w := by
    have : deltaParam M ≤ 240 * deltaParam M := by omega
    exact lt_of_le_of_lt (le_trans this hb.2.1) hDr_w
  have h3200Δ_lt : 3200 * deltaParam M < 2 ^ w := by
    have : 3200 * deltaParam M ≤ dCore M := by unfold dCore; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h1600Δ_lt : 1600 * deltaParam M < 2 ^ w := by omega
  have h1600Δd_lt : 1600 * deltaParam M * (dCore M + 1) < 2 ^ w := by
    have : 1600 * deltaParam M * (dCore M + 1) ≤ RCore M := by
      unfold RCore; exact Nat.le_mul_of_pos_right _ (by omega)
    exact lt_of_le_of_lt this hRc_lt
  have h23040Δ2_le : 23040 * deltaParam M * deltaParam M ≤ FParam ParamConfig.default M := by
    unfold FParam ParamConfig.default; dsimp only
    have hR1 : 1 ≤ RCore M := by omega
    calc 23040 * deltaParam M * deltaParam M
        = 1920 * 12 * (deltaParam M) ^ 2 := by ring
      _ ≤ 1920 * 12 * (deltaParam M) ^ 2 * RCore M := Nat.le_mul_of_pos_right _ hR1
  have h23040Δ_lt : 23040 * deltaParam M < 2 ^ w :=
    lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right _ (by omega)) h23040Δ2_le) hF_lt
  have h23040Δ2_lt : 23040 * deltaParam M * deltaParam M < 2 ^ w :=
    lt_of_le_of_lt h23040Δ2_le hF_lt
  have hF_eq : 23040 * deltaParam M * deltaParam M * RCore M = FParam ParamConfig.default M := by
    unfold FParam ParamConfig.default; dsimp only; ring
  have hAΔ_lt : 240 * deltaParam M < 2 ^ w := lt_of_le_of_lt hb.2.1 hDr_w
  have hsz : coreParamsSize r = 7 + 3 * r := rfl
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 1 = r ∧ st.regs 2 = pAddr ∧ st.regs 3 = i ∧ st.regs 8 = NOf M r ∧
    st.regs 12 = FParam ParamConfig.default M ∧ st.regs 13 = 240 * deltaParam M ∧
    st.regs 14 = PParam ParamConfig.default M i ∧ st.regs 15 = (NOf M r) ^ i ∧
    st.mem pAddr = cp.N ∧ st.mem (pAddr + 1) = cp.L ∧
    st.mem (pAddr + 2) = cp.Δ ∧ st.mem (pAddr + 3) = r ∧
    (∀ j ≤ i, st.mem (pAddr + 4 + j) = cp.P j) ∧
    (∀ j ≤ i, st.mem (pAddr + 5 + r + j) = cp.D j) ∧
    (∀ j ≤ i, st.mem (pAddr + 6 + 2 * r + j) = cp.N ^ j) ∧
    (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st.mem a = st₀.mem a)
  have hfor :
      Triple w p
        (fun st =>
          st.regs 1 = r ∧ st.regs 2 = pAddr ∧ st.regs 8 = NOf M r ∧
          st.regs 12 = FParam ParamConfig.default M ∧ st.regs 13 = 240 * deltaParam M ∧
          st.regs 14 = 1 ∧ st.regs 15 = 1 ∧
          st.mem pAddr = cp.N ∧ st.mem (pAddr + 1) = cp.L ∧
          st.mem (pAddr + 2) = cp.Δ ∧ st.mem (pAddr + 3) = r ∧
          st.mem (pAddr + 4) = cp.P 0 ∧ st.mem (pAddr + 5 + r) = cp.D 0 ∧
          st.mem (pAddr + 6 + 2 * r) = cp.N ^ 0 ∧
          (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st.mem a = st₀.mem a))
        (forRange 3 (.const 0) (.reg 1)
          (seqStmts
            [ .assign 14 (.bin .mul (.reg 14) (.reg 12))
            , .assign 16 (.bin .mul (.reg 13) (.reg 14))
            , .assign 15 (.bin .mul (.reg 15) (.reg 8))
            , .assign 4 (.bin .add (.reg 3) (.const 1))
            , .store (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 4)) (.reg 14)
            , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 5)) (.reg 1)) (.reg 4))
                (.reg 16)
            , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 6))
                (.bin .mul (.const 2) (.reg 1))) (.reg 4)) (.reg 15) ]))
        (normalPost fun st' =>
          CoreParamsAt st'.mem pAddr cp r ∧
          (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st'.mem a = st₀.mem a))
        (fun _ => 65 * r + 15) := by
    have hfr := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
      (body := seqStmts
        [ .assign 14 (.bin .mul (.reg 14) (.reg 12))
        , .assign 16 (.bin .mul (.reg 13) (.reg 14))
        , .assign 15 (.bin .mul (.reg 15) (.reg 8))
        , .assign 4 (.bin .add (.reg 3) (.const 1))
        , .store (.bin .add (.bin .add (.reg 2) (.const 4)) (.reg 4)) (.reg 14)
        , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 5)) (.reg 1)) (.reg 4))
            (.reg 16)
        , .store (.bin .add (.bin .add (.bin .add (.reg 2) (.const 6))
            (.bin .mul (.const 2) (.reg 1))) (.reg 4)) (.reg 15) ])
      (P := fun st =>
        st.regs 1 = r ∧ st.regs 2 = pAddr ∧ st.regs 8 = NOf M r ∧
        st.regs 12 = FParam ParamConfig.default M ∧ st.regs 13 = 240 * deltaParam M ∧
        st.regs 14 = 1 ∧ st.regs 15 = 1 ∧
        st.mem pAddr = cp.N ∧ st.mem (pAddr + 1) = cp.L ∧
        st.mem (pAddr + 2) = cp.Δ ∧ st.mem (pAddr + 3) = r ∧
        st.mem (pAddr + 4) = cp.P 0 ∧ st.mem (pAddr + 5 + r) = cp.D 0 ∧
        st.mem (pAddr + 6 + 2 * r) = cp.N ^ 0 ∧
        (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st.mem a = st₀.mem a))
      (Inv := Inv) 55 0 r (Nat.zero_le r) (by omega) (fun _ => by omega)
      (fun st ⟨h1, h2, h8, h12, h13, h14, h15, hm0, hm1, hm2, hm3, hP0, hD0, hN0, hfr0⟩ =>
        ⟨Expr.eval_const (by omega), by simp [h1], by simp [h2], by simp, by simp [h8],
          by simp [h12], by simp [h13], by simp [h14, PParam], by simp [h15],
          hm0, hm1, hm2, hm3,
          fun j hj => by have hj0 : j = 0 := (by omega); subst hj0; simpa using hP0,
          fun j hj => by have hj0 : j = 0 := (by omega); subst hj0; simpa using hD0,
          fun j hj => by have hj0 : j = 0 := (by omega); subst hj0; simpa using hN0,
          hfr0⟩)
      (fun _ _ _ _ hI => hI.2.2.1)
      (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.1)
      (fun i _ hi => by
        intro st ω ⟨h1, h2, h3, h8, h12, h13, h14, h15, hm0, hm1, hm2, hm3, hP, hD, hN, hfr0⟩
        have hPi1_eq : PParam ParamConfig.default M i * FParam ParamConfig.default M =
            PParam ParamConfig.default M (i + 1) := by unfold PParam; rw [pow_succ]
        have hPi1_le : PParam ParamConfig.default M (i + 1) ≤ DCore ParamConfig.default M r := by
          unfold DCore PParam ParamConfig.A ParamConfig.default; dsimp only
          have hpow : (FParam ParamConfig.default M) ^ (i + 1) ≤
              (FParam ParamConfig.default M) ^ r := Nat.pow_le_pow_right hF1 (by omega)
          exact le_trans hpow (Nat.le_mul_of_pos_left _ (by omega))
        have hDi1_eq : 240 * deltaParam M * PParam ParamConfig.default M (i + 1) =
            DCore ParamConfig.default M (i + 1) := rfl
        have hDi1_le : DCore ParamConfig.default M (i + 1) ≤ DCore ParamConfig.default M r := by
          unfold DCore PParam
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hF1 (by omega))
        have hNi1_eq : (NOf M r) ^ i * NOf M r = (NOf M r) ^ (i + 1) := by rw [pow_succ]
        have hNi1_le : (NOf M r) ^ (i + 1) ≤ (NOf M r) ^ r := Nat.pow_le_pow_right hN1 (by omega)
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := PParam ParamConfig.default M (i + 1))
          (by rw [← hPi1_eq]
              exact Expr.eval_mul (Expr.eval_reg_of_eq h14) (Expr.eval_reg_of_eq h12)
                (by rw [hPi1_eq]; exact lt_of_le_of_lt hPi1_le hDr_w)) ?_
        refine runs_seq_assign_le (v := DCore ParamConfig.default M (i + 1))
          (by rw [← hDi1_eq]
              exact Expr.eval_mul (Expr.eval_reg_of_eq (by simp [h13]))
                (Expr.eval_reg_of_eq (by simp))
                (by rw [hDi1_eq]; exact lt_of_le_of_lt hDi1_le hDr_w)) ?_
        refine runs_seq_assign_le (v := (NOf M r) ^ (i + 1))
          (by rw [← hNi1_eq]
              exact Expr.eval_mul (Expr.eval_reg_of_eq (by simp [h15]))
                (Expr.eval_reg_of_eq (by simp [h8]))
                (by rw [hNi1_eq]; exact lt_of_le_of_lt hNi1_le hNr_w)) ?_
        refine runs_seq_assign_le (v := i + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h3])) (Expr.eval_const (by omega))
            (by omega)) ?_
        refine runs_seq_store_le (x := pAddr + 4 + (i + 1))
          (v := PParam ParamConfig.default M (i + 1))
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2])) (Expr.eval_const (by omega))
              (by omega))
            (Expr.eval_reg_of_eq (by simp)) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_seq_store_le (x := pAddr + 5 + r + (i + 1))
          (v := DCore ParamConfig.default M (i + 1))
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2])) (Expr.eval_const (by omega))
                (by omega))
              (Expr.eval_reg_of_eq (by simp [h1])) (by omega))
            (Expr.eval_reg_of_eq (by simp)) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_store_le (x := pAddr + 6 + 2 * r + (i + 1))
          (v := (NOf M r) ^ (i + 1))
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2])) (Expr.eval_const (by omega))
                (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [h1]))
                (by omega)) (by omega))
            (Expr.eval_reg_of_eq (by simp)) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_ (by simp [Expr.size])
        refine ⟨⟨by simp [h1], by simp [h2], by simp, by simp [h8], by simp [h12],
          by simp [h13], by simp, by simp,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), hm0],
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), hm1],
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), hm2],
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), hm3],
          ?_, ?_, ?_, ?_⟩, by simp [h3]⟩
        · intro j hj
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          by_cases hji : j = i + 1
          · subst hji; rw [Function.update_self]; rfl
          · rw [Function.update_of_ne (by omega)]; exact hP j (by omega)
        · intro j hj
          dsimp only
          rw [Function.update_of_ne (by omega)]
          by_cases hji : j = i + 1
          · subst hji; rw [Function.update_self]; rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hD j (by omega)
        · intro j hj
          dsimp only
          by_cases hji : j = i + 1
          · subst hji; rw [Function.update_self]; rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hN j (by omega)
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hfr0 a ha)
    refine hfr.conseq (fun _ h => h) ?_ (fun _ _ => by simp [Expr.size]; omega)
    rintro (_ | v) st' hI
    · rcases hI with ⟨_, _, _, _, _, _, _, _, hm0, hm1, hm2, hm3, hP, hD, hN, hfr0⟩
      exact ⟨⟨hm0, hm1, hm2, hm3, hP, hD, hN⟩, hfr0⟩
    · exact hI.elim
  intro st ω hs; subst hs
  refine runs_start_le ?_
  dsimp only [writeCoreParamsFillStmt, seqStmts]
  refine runs_seq_assign_le (v := deltaParam M)
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr6) hΔ_lt) ?_
  refine runs_seq_assign_le (v := dCore M)
    (Expr.eval_mul
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h3200Δ_lt)
      (Expr.eval_reg_of_eq (by simp [hr6])) hdc_lt) ?_
  refine runs_seq_assign_le (v := RCore M)
    (Expr.eval_mul
      (Expr.eval_mul
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h1600Δ_lt)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hdc1_lt)
        h1600Δd_lt)
      (Expr.eval_reg_of_eq (by simp [hr6])) hRc_lt) ?_
  refine runs_seq_assign_le (v := FParam ParamConfig.default M)
    (by rw [← hF_eq]
        exact Expr.eval_mul
          (Expr.eval_mul
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h23040Δ_lt)
            (Expr.eval_reg_of_eq (by simp)) h23040Δ2_lt)
          (Expr.eval_reg_of_eq (by simp))
          (by rw [hF_eq]; exact hF_lt)) ?_
  refine runs_seq_assign_le (v := 240 * deltaParam M)
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hAΔ_lt) ?_
  refine runs_seq_store_le (x := pAddr) (v := NOf M r)
    (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_reg_of_eq (by simp [hr8])) ?_
  refine runs_seq_store_le (x := pAddr + 1) (v := LParam M)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp [hr6])) ?_
  refine runs_seq_store_le (x := pAddr + 2) (v := deltaParam M)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := pAddr + 3) (v := r)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp [hr1])) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := pAddr + 4) (v := 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := pAddr + 5 + r) (v := 240 * deltaParam M)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [hr1])) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := pAddr + 6 + 2 * r) (v := 1)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr1])) (by omega))
      (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_triple_le hfor ?_ (fun o s' h => h) (by simp [Expr.size]; omega)
  refine ⟨by simp [hr1], by simp [hr2], by simp [hr8], by simp, by simp, by simp, by simp,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self];
       rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self];
       rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]; simp [cp, coreParamsOf, PParam],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]
       simp [cp, coreParamsOf, DCore, PParam, ParamConfig.A, ParamConfig.default],
    by dsimp only; rw [Function.update_self]; simp [cp, coreParamsOf],
    fun a ha => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]⟩

/-! ## 4. Main Run Lemma, `MeetsContract`, and Non-Vacuity -/

/-- Direct run lemma for `writeCoreParamsProc` from `startState [M, r, pAddr] mem pos`. -/
theorem writeCoreParamsProc_runs {w M r pAddr pos : ℕ} {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hr : 1 ≤ r) (hp_w : pAddr + coreParamsSize r < 2 ^ w)
    (hNr_w : (NOf M r) ^ r < 2 ^ w) (hDr_w : DCore ParamConfig.default M r < 2 ^ w) :
    ∃ st' c,
      Runs w p ω writeCoreParamsProc (startState [M, r, pAddr] mem pos) (.returned 0) st' c ∧
      CoreParamsAt st'.mem pAddr (coreParamsOf ParamConfig.default M r) r ∧
      (∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st'.mem a = mem a) ∧
      c ≤ writeCoreParamsCost M r := by
  have hb := coreParam_default_bounds hr hp_w hNr_w hDr_w
  suffices h : ∃ o st' c,
      Runs w p ω writeCoreParamsProc (startState [M, r, pAddr] mem pos) o st' c ∧
      (o = .returned 0 ∧ CoreParamsAt st'.mem pAddr (coreParamsOf ParamConfig.default M r) r ∧
        ∀ a, (a < pAddr ∨ pAddr + coreParamsSize r ≤ a) → st'.mem a = mem a) ∧
      c ≤ writeCoreParamsCost M r by
    rcases h with ⟨o, st', c, hrun, ⟨rfl, hcp, hfr⟩, hc⟩
    exact ⟨st', c, hrun, hcp, hfr, hc⟩
  refine runs_start_le ?_
  dsimp only [writeCoreParamsProc, seqStmts]
  refine runs_seq_triple_le
    (writeCoreParamsEll_triple hr hp_w hNr_w hDr_w (startState [M, r, pAddr] mem pos)
      (by simp [startState]) (by simp [startState]) (by simp [startState])) rfl ?_
  intro st1 ⟨hmem1, h1, h2, h4, h6⟩
  refine runs_seq_triple_le
    (writeCoreParamsN_triple hr hp_w hNr_w hDr_w st1 h1 h2 h4 h6) rfl ?_
  intro st2 ⟨hmem2, h1', h2', h6', h8'⟩
  refine runs_seq_triple_le
    (writeCoreParamsFill_triple hr hp_w hNr_w hDr_w st2 h1' h2' h6' h8') rfl ?_
  intro st3 ⟨hcp, hfr⟩
  refine runs_ret_le (Expr.eval_const (by omega))
    ⟨rfl, hcp, fun a ha => by rw [hfr a ha, hmem2, hmem1]; rfl⟩ ?_
  unfold writeCoreParamsCost
  simp [Expr.size]
  omega

/-- `writeCoreParamsProc` meets `writeCoreParamsContract w`. -/
theorem writeCoreParamsProc_meetsContract {w base : ℕ} {p : Program}
    (hp : p.procs[base]? = some writeCoreParamsProc) :
    MeetsContract w p base (writeCoreParamsContract w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨M, r, pAddr, rfl, hr, hp_w, hNr_w, hDr_w⟩
  rcases writeCoreParamsProc_runs (p := p) (mem := mem) (pos := pos) (ω := ω)
      hr hp_w hNr_w hDr_w with
    ⟨st', c, hrun, hcp, hfr, hc⟩
  refine ⟨writeCoreParamsProc, hp, .returned 0, st', c, hrun, ?_, ?_⟩
  · intro M' r' pAddr' heq _ _ _ _
    simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    exact ⟨hcp, hfr⟩
  · simpa [writeCoreParamsContract] using hc

/-- Non-vacuity of `writeCoreParamsContract`. -/
theorem writeCoreParamsContract_pre_example :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧ (writeCoreParamsContract w).pre args mem := by
  let w : ℕ := Nat.log 2 (DCore ParamConfig.default 0 1 + coreParamsSize 1 + (NOf 0 1) ^ 1 + 2) + 1
  have hw : DCore ParamConfig.default 0 1 + coreParamsSize 1 + (NOf 0 1) ^ 1 + 2 < 2 ^ w :=
    Nat.lt_pow_succ_log_self (by decide) _
  refine ⟨w, [0, 1, 0], fun _ => 0, ?_, 0, 1, 0, rfl, le_rfl, by omega, by omega, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> omega

end MinCostFlow.ExpanderDecomp
