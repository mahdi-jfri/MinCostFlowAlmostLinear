module

public import MinCostFlow.ExpanderDecomp.CoreProg
public import MinCostFlow.ExpanderDecomp.CoreOuterParams
import MinCostFlow.ExpanderDecomp.ProgDecompEntrySpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outer-to-Core Adapter Procedure and Contract (`CoreOuter`)

Adapts `CoreProg.coreEntryProc` (calling convention `[q, gAddr, pAddr, outAddr, h]`) to the outer
calling convention `[q, wAddr, M, r, outAddr, h]` by writing the `CoreParamsAt` parameter block at
the start of the zero-initialized heap (`CoreOuterParams.writeCoreParamsProc`) and then invoking
`coreEntryProc` with heap cursor `h + coreParamsSize r`.

Main results:
* `coreAdapterCost` and `coreAdapterCost_le`: concrete `coreCost` matching the size-sensitive cost bound
  (`IsCorePlayer.cost_le`).
* `coreAdapterProc` and `coreAdapterProc_noRand`: deterministic 4-statement adapter procedure.
* `coreAdapterSpace` and `coreAdapterContract`: existential outer core contract with `r ≤ ell M`
  and multiplicative space envelope `C_sp * (coreSpaceBase M r * (ccost + 1) + (n + 3) ^ 5 + 1)`.
* `coreAdapterProc_meetsContract`: proves `coreAdapterProc` meets `coreAdapterContract` given
  `writeCoreParamsContract` and `coreEntryContract`.
* `outerCoreSpace_too_small_counterexample`: witnesses that the additive space bound
  `OuterProgContracts.outerCoreSpace C_sp W.n (coreCost q W) = C_sp * (coreCost q W + (W.n + 3)^5 + 1)`
  cannot cover `coreParamsSize r + coreEntrySpace` for any fixed constant `C_sp`, even at
  `r = 1, q = 1, W = ⟨2, []⟩`.
* `coreAdapterContract_pre_example`: non-vacuity witness for `coreAdapterContract`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Cost, Space, Procedure, and Contract -/

/-- Concrete core cost matching the size-sensitive cost bound (`IsCorePlayer.cost_le`):
`W.n * (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)`. -/
def coreAdapterCost (M r _q : ℕ) (W : Graph) : ℕ :=
  W.n * (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)

/-- Time multiplier constant for `coreAdapterProc`. -/
def coreAdapterTimeConst (K_B C_stepC C_left : ℕ) : ℕ :=
  coreTimeConst K_B (stepCTimeConst C_stepC C_left) + 500

/-- Space multiplier constant for `coreAdapterProc`. -/
def coreAdapterSpaceConst (S_B C_sp_rt : ℕ) : ℕ :=
  coreSpaceConst S_B (stepCSpaceConst C_sp_rt) + 12

/-- Heap space envelope for the outer core adapter:
`C_sp * (coreSpaceBase M r * (ccost + 1) + (n + 3) ^ 5 + 1)`. -/
def coreAdapterSpace (C_sp M r n ccost : ℕ) : ℕ :=
  C_sp * (coreSpaceBase M r * (ccost + 1) + (n + 3) ^ 5 + 1)

/-- Deterministic adapter procedure taking `[q, wAddr, M, r, outAddr, h]`, writing
`CoreParamsAt` at `h` via `writeParamsIdx`, and calling `coreEntryIdx` on
`[q, wAddr, h, outAddr, h + coreParamsSize r]`. -/
def coreAdapterProc (writeParamsIdx coreEntryIdx : ℕ) : Stmt :=
  seqStmts
    [ .call 6 writeParamsIdx [.reg 2, .reg 3, .reg 5]
    , .assign 7 (.bin .add (.reg 5) (.bin .add (.const 7) (.bin .mul (.const 3) (.reg 3))))
    , .call 8 coreEntryIdx [.reg 0, .reg 1, .reg 5, .reg 4, .reg 7]
    , .ret (.reg 8) ]

/-- Existential outer core contract for `[q, wAddr, M, r, outAddr, h]` with `r ≤ ell M` and
space bound `coreAdapterSpace C_sp M r W.n (coreCost q W)`. -/
noncomputable def coreAdapterContract (M r : ℕ) (coreCost : ℕ → Graph → ℕ)
    (C_core C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (q wAddr outAddr h : ℕ) (W : Graph),
      args = [q, wAddr, M, r, outAddr, h] ∧
      1 ≤ q ∧ q ≤ r ∧ r ≤ ell M ∧
      GraphAt mem wAddr W ∧
      W.IsValid ∧ W.IsLoopless ∧
      (NOf M r) ^ (q - 1) < W.n ∧
      W.n ≤ (NOf M r) ^ q ∧
      (∀ v < W.n, W.deg v ≤ deltaParam M) ∧
      ZeroFrom mem h ∧
      wAddr + 2 + 2 * W.m ≤ h ∧
      outAddr + 2 + W.n ≤ h ∧
      DisjointRange outAddr (2 + W.n) wAddr (2 + 2 * W.m) ∧
      h + coreAdapterSpace C_sp M r W.n (coreCost q W) < 2 ^ w ∧
      16 < 2 ^ w ∧
      M < 2 ^ w ∧
      r < 2 ^ w
  post args mem v mem' :=
    let q := args.getD 0 0
    let wAddr := args.getD 1 0
    let outAddr := args.getD 4 0
    let h := args.getD 5 0
    let W := readGraph mem wAddr
    (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ CoreOutcomeSpec ParamConfig.default M q W res) ∧
    h ≤ v ∧
    v ≤ h + coreAdapterSpace C_sp M r W.n (coreCost q W) ∧
    ZeroFrom mem' v ∧
    (∀ a < h, (a < outAddr ∨ outAddr + 2 + W.n ≤ a) → mem' a = mem a)
  cost args mem :=
    let q := args.getD 0 0
    let wAddr := args.getD 1 0
    let W := readGraph mem wAddr
    C_core * coreCost q W + C_core

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Determinism, the Size-Sensitive Cost Bound, and Arithmetic Bounds -/

theorem coreAdapterProc_noRand (writeParamsIdx coreEntryIdx : ℕ) :
    (coreAdapterProc writeParamsIdx coreEntryIdx).NoRand := by
  simp [coreAdapterProc, seqStmts, Stmt.NoRand]

/-- `coreAdapterCost` satisfies the size-sensitive cost bound in the exact shape of `IsCorePlayer.cost_le`. -/
theorem coreAdapterCost_le (M r : ℕ) :
    ∀ q (G : Graph), 1 ≤ q → q ≤ r → G.IsValid → G.IsLoopless →
      (NOf M r) ^ (q - 1) < G.n → G.n ≤ (NOf M r) ^ q →
      (∀ v < G.n, G.deg v ≤ deltaParam M) →
      coreAdapterCost M r q G ≤ G.n * (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
  fun _ _ _ _ _ _ _ _ _ => le_rfl

private lemma coreTimeBound_le_coreAdapterCost {M r q : ℕ} {W : Graph}
    (hq1 : 1 ≤ q) (hqr : q ≤ r) (hlo : (NOf M r) ^ (q - 1) < W.n) :
    coreTimeBound ParamConfig.default M r q ≤ coreAdapterCost M r q W := by
  unfold coreTimeBound coreAdapterCost
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  have hNpow : (NOf M r) ^ (q + 1) ≤ W.n * (NOf M r) ^ 2 := by
    have hsplit : (NOf M r) ^ (q + 1) = (NOf M r) ^ (q - 1) * (NOf M r) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact Nat.mul_le_mul_right _ (le_of_lt hlo)
  have hWpow : (WParam ParamConfig.default M) ^ (10 * q ^ 2 + 10) ≤
      (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) := by
    apply Nat.pow_le_pow_right hW1
    have hq2 : q ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hqr 2
    omega
  exact Nat.mul_le_mul hNpow hWpow

private lemma DCore_default_le_coreAdapterCost {M r q : ℕ} {W : Graph}
    (hlo : (NOf M r) ^ (q - 1) < W.n) :
    DCore ParamConfig.default M r ≤ coreAdapterCost M r q W := by
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hWn1 : 1 ≤ W.n := by
    have : 1 ≤ (NOf M r) ^ (q - 1) := Nat.one_le_pow _ _ hN1
    omega
  have hell : 1 ≤ ell M := one_le_ell M
  have hL : 4 ≤ LParam M := by unfold LParam; omega
  have hΔ : 4096 ≤ deltaParam M := by unfold deltaParam tParam; omega
  have hR1 : 1 ≤ RCore M := by
    unfold RCore; exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have h240_le_F : 240 * deltaParam M ≤ FParam ParamConfig.default M := by
    unfold FParam ParamConfig.default; dsimp only
    have h1 : 240 * deltaParam M ≤ 1920 * 12 * (deltaParam M) ^ 2 := by nlinarith
    exact le_trans h1 (Nat.le_mul_of_pos_right _ hR1)
  have hF_le_W : FParam ParamConfig.default M ≤ WParam ParamConfig.default M := by
    unfold WParam; omega
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  have h240_le_W : 240 * deltaParam M ≤ WParam ParamConfig.default M :=
    le_trans h240_le_F hF_le_W
  have hDr_le_Wpow : DCore ParamConfig.default M r ≤
      (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) := by
    have hDr_eq : DCore ParamConfig.default M r =
        240 * deltaParam M * (FParam ParamConfig.default M) ^ r := rfl
    rw [hDr_eq]
    have hFr : (FParam ParamConfig.default M) ^ r ≤ (WParam ParamConfig.default M) ^ r :=
      Nat.pow_le_pow_left hF_le_W r
    have hmul : 240 * deltaParam M * (FParam ParamConfig.default M) ^ r ≤
        (WParam ParamConfig.default M) ^ (r + 1) := by
      rw [pow_succ', Nat.mul_comm (WParam ParamConfig.default M)]
      rw [Nat.mul_comm _ (WParam ParamConfig.default M)]
      exact Nat.mul_le_mul h240_le_W hFr
    have hexp : r + 1 ≤ 10 * r ^ 2 + 10 := by nlinarith
    exact le_trans hmul (Nat.pow_le_pow_right hW1 hexp)
  unfold coreAdapterCost
  have hWN : 1 ≤ W.n * (NOf M r) ^ 2 := Nat.mul_pos hWn1 (Nat.pow_pos hN1)
  exact le_trans hDr_le_Wpow (Nat.le_mul_of_pos_left _ hWN)

private lemma coreSpaceBase_bounds {M r q : ℕ} (hqr : q ≤ r) (hrl : r ≤ ell M) :
    coreParamsSize r ≤ 10 * coreSpaceBase M r ∧
    (NOf M r) ^ r < coreSpaceBase M r ∧
    (NOf M r) ^ q ≤ coreSpaceBase M r := by
  have hell : 1 ≤ ell M := one_le_ell M
  have hL : 4 * ell M = LParam M := rfl
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hNr1 : 1 ≤ (NOf M r) ^ r := Nat.one_le_pow r _ hN1
  have hbase_ge : 2048 * LParam M * (NOf M r) ^ r + 3 ≤ coreSpaceBase M r := by
    unfold coreSpaceBase
    exact Nat.le_self_pow (by decide) _
  have hNr_lt : (NOf M r) ^ r < coreSpaceBase M r := by
    have : (NOf M r) ^ r < 2048 * LParam M * (NOf M r) ^ r + 3 := by
      have : 1 ≤ 2048 * LParam M := by omega
      nlinarith
    omega
  have hNq_le : (NOf M r) ^ q ≤ coreSpaceBase M r :=
    le_trans (Nat.pow_le_pow_right hN1 hqr) (le_of_lt hNr_lt)
  have hsz : coreParamsSize r ≤ 10 * coreSpaceBase M r := by
    unfold coreParamsSize
    have h1 : 7 + 3 * r ≤ 2048 * LParam M * (NOf M r) ^ r + 3 := by
      have h2 : 4 * r ≤ LParam M := by omega
      have h3 : LParam M ≤ LParam M * (NOf M r) ^ r := Nat.le_mul_of_pos_right _ hNr1
      have h4 : 2048 * LParam M * (NOf M r) ^ r = 2048 * (LParam M * (NOf M r) ^ r) := by ring
      omega
    omega
  exact ⟨hsz, hNr_lt, hNq_le⟩

/-! ## 3. Verification of `coreAdapterProc` -/

/-- `coreAdapterProc` meets `coreAdapterContract` with concrete `coreAdapterCost` (satisfying
the size-sensitive cost bound), time constant `coreAdapterTimeConst`, and space constant `coreAdapterSpaceConst`. -/
theorem coreAdapterProc_meetsContract {w base writeParamsIdx coreEntryIdx : ℕ}
    {M r K_B C_stepC C_left S_B C_sp_rt : ℕ} {p : Program}
    (hp : p.procs[base]? = some (coreAdapterProc writeParamsIdx coreEntryIdx))
    (hParams : MeetsContract w p writeParamsIdx (writeCoreParamsContract w))
    (hCore : MeetsContract w p coreEntryIdx
      (coreEntryContract ParamConfig.default M r w K_B C_stepC C_left S_B C_sp_rt)) :
    MeetsContract w p base
      (coreAdapterContract M r (coreAdapterCost M r)
        (coreAdapterTimeConst K_B C_stepC C_left)
        (coreAdapterSpaceConst S_B C_sp_rt) w) := by
  intro args mem pos ω hwords hpre
  rcases hpre with
    ⟨q, wAddr, outAddr, h, W, rfl, hq1, hqr, hrl, hG_at, hGv, hGl, hlo, hhi, hdeg,
      hZero, hw_h, hout_h, hdisj, hspace_lt, h16, hM_w, hr_w⟩
  set C_core := coreAdapterTimeConst K_B C_stepC C_left
  set C_sp := coreAdapterSpaceConst S_B C_sp_rt
  set S_C := stepCSpaceConst C_sp_rt
  set K_C := stepCTimeConst C_stepC C_left
  have hreadW : readGraph mem wAddr = W := readGraph_eq_of_graphAt hG_at
  have hr1 : 1 ≤ r := by omega
  have hsb := coreSpaceBase_bounds hqr hrl
  have hCsp_ge : coreSpaceConst S_B S_C + 12 = C_sp := rfl
  have hCsp_pos : 12 ≤ C_sp := by omega
  have htb_le : coreTimeBound ParamConfig.default M r q ≤ coreAdapterCost M r q W :=
    coreTimeBound_le_coreAdapterCost hq1 hqr hlo
  have hDr_le : DCore ParamConfig.default M r ≤ coreAdapterCost M r q W :=
    DCore_default_le_coreAdapterCost hlo
  have htot_space :
      coreParamsSize r + coreEntrySpace S_B S_C ParamConfig.default M r q ≤
        coreAdapterSpace C_sp M r W.n (coreAdapterCost M r q W) := by
    unfold coreEntrySpace coreProgSpace coreAdapterSpace
    have hprog :
        coreSpaceConst S_B S_C * coreSpaceBase M r * coreTimeBound ParamConfig.default M r q ≤
          coreSpaceConst S_B S_C * coreSpaceBase M r * coreAdapterCost M r q W :=
      Nat.mul_le_mul_left _ htb_le
    have h1 :
        coreParamsSize r +
          (coreSpaceConst S_B S_C * coreSpaceBase M r * coreTimeBound ParamConfig.default M r q +
            2 * (NOf M r) ^ q) ≤
        (coreSpaceConst S_B S_C + 12) * coreSpaceBase M r * (coreAdapterCost M r q W + 1) := by
      have h2 : coreParamsSize r + 2 * (NOf M r) ^ q ≤ 12 * coreSpaceBase M r := by omega
      have h3 : (coreSpaceConst S_B S_C + 12) * coreSpaceBase M r * (coreAdapterCost M r q W + 1) =
          coreSpaceConst S_B S_C * coreSpaceBase M r * coreAdapterCost M r q W +
          12 * coreSpaceBase M r * coreAdapterCost M r q W +
          (coreSpaceConst S_B S_C + 12) * coreSpaceBase M r := by ring
      have h4 : 12 * coreSpaceBase M r ≤ (coreSpaceConst S_B S_C + 12) * coreSpaceBase M r :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have h5 :
        C_sp * coreSpaceBase M r * (coreAdapterCost M r q W + 1) ≤
          C_sp * (coreSpaceBase M r * (coreAdapterCost M r q W + 1) + (W.n + 3) ^ 5 + 1) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left C_sp (by omega)
    exact le_trans h1 (by simpa [hCsp_ge] using h5)
  have hbase_le_sp : coreSpaceBase M r ≤ coreAdapterSpace C_sp M r W.n (coreAdapterCost M r q W) := by
    unfold coreAdapterSpace
    have h1 : coreSpaceBase M r ≤ coreSpaceBase M r * (coreAdapterCost M r q W + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : coreSpaceBase M r ≤
        coreSpaceBase M r * (coreAdapterCost M r q W + 1) + (W.n + 3) ^ 5 + 1 := by omega
    exact le_trans h2 (Nat.le_mul_of_pos_left _ (by omega))
  have hDr_lt_w : DCore ParamConfig.default M r < 2 ^ w := by
    have h1 : coreAdapterCost M r q W ≤ coreAdapterSpace C_sp M r W.n (coreAdapterCost M r q W) := by
      unfold coreAdapterSpace
      have hbase1 : 1 ≤ coreSpaceBase M r := by unfold coreSpaceBase; exact Nat.one_le_pow _ _ (by omega)
      have h2 : coreAdapterCost M r q W ≤ coreSpaceBase M r * (coreAdapterCost M r q W + 1) := by
        calc coreAdapterCost M r q W ≤ coreAdapterCost M r q W + 1 := Nat.le_succ _
          _ ≤ coreSpaceBase M r * (coreAdapterCost M r q W + 1) := Nat.le_mul_of_pos_left _ hbase1
      exact le_trans h2 (le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega)))
    omega
  have hp_w : h + coreParamsSize r < 2 ^ w := by omega
  have hNr_w : (NOf M r) ^ r < 2 ^ w := by omega
  have hq_w : q < 2 ^ w := by omega
  have hwAddr_w : wAddr < 2 ^ w := by omega
  have houtAddr_w : outAddr < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hsz_eq : 7 + 3 * r = coreParamsSize r := rfl
  have hcost_total :
      writeCoreParamsCost M r + coreEntryTime K_B K_C ParamConfig.default M r q + 40 ≤
        C_core * coreAdapterCost M r q W + C_core := by
    have hcore_t := coreEntryTime_le_coreTimeBound K_B K_C ParamConfig.default M r q
    have hcore_t' :
        coreEntryTime K_B K_C ParamConfig.default M r q ≤
          (coreTimeConst K_B K_C + 25) * coreAdapterCost M r q W + 100 :=
      le_trans hcore_t (Nat.add_le_add_right (Nat.mul_le_mul_left _ htb_le) 100)
    have hell_le : ell M ≤ coreAdapterCost M r q W := by
      have h1 : ell M ≤ WParam ParamConfig.default M := by
        unfold WParam LParam; omega
      have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
      have h2 : WParam ParamConfig.default M ≤ (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
        Nat.le_self_pow (by omega) _
      have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
      have hWn1 : 1 ≤ W.n := by
        have : 1 ≤ (NOf M r) ^ (q - 1) := Nat.one_le_pow _ _ hN1
        omega
      have h3 : (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) ≤ coreAdapterCost M r q W := by
        unfold coreAdapterCost
        exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hWn1 (Nat.pow_pos hN1))
      exact le_trans h1 (le_trans h2 h3)
    have hr_le_cost : r ≤ coreAdapterCost M r q W := le_trans hrl hell_le
    unfold writeCoreParamsCost
    have hCcore : C_core = coreTimeConst K_B K_C + 500 := rfl
    have h1 : (coreTimeConst K_B K_C + 25) * coreAdapterCost M r q W +
        140 * coreAdapterCost M r q W ≤ C_core * coreAdapterCost M r q W := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨coreAdapterProc writeParamsIdx coreEntryIdx, hp, ?_⟩
  suffices hrun : ∃ o st' c,
      Runs w p ω (coreAdapterProc writeParamsIdx coreEntryIdx)
        (startState [q, wAddr, M, r, outAddr, h] mem pos) o st' c ∧
      (∃ v, o = .returned v ∧
        (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧
          CoreOutcomeSpec ParamConfig.default M q W res) ∧
        h ≤ v ∧
        v ≤ h + coreAdapterSpace C_sp M r W.n (coreAdapterCost M r q W) ∧
        ZeroFrom st'.mem v ∧
        (∀ a < h, (a < outAddr ∨ outAddr + 2 + W.n ≤ a) → st'.mem a = mem a)) ∧
      c ≤ C_core * coreAdapterCost M r q W + C_core by
    rcases hrun with ⟨o, st', c, hr, ⟨v, rfl, hres, hv1, hv2, hZ, hfr⟩, hc⟩
    refine ⟨.returned v, st', c, hr, ?_, ?_⟩
    · simp only [coreAdapterContract, List.getD_cons_zero, List.getD_cons_succ, hreadW]
      exact ⟨hres, hv1, hv2, hZ, hfr⟩
    · simp only [coreAdapterContract, List.getD_cons_zero, List.getD_cons_succ, hreadW]
      exact hc
  refine runs_start_le ?_
  dsimp only [coreAdapterProc, seqStmts]
  refine runs_seq_call_le (C := writeCoreParamsContract w) (vs := [M, r, h]) hParams ?_ ?_ ?_ ?_
  · simp [evalArgs, Expr.eval, startState]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · exact ⟨M, r, h, rfl, hr1, hp_w, hNr_w, hDr_lt_w⟩
  · intro v1 mem1 pos1 hpost1
    have ⟨hcp1, hfr1⟩ := hpost1 M r h rfl hr1 hp_w hNr_w hDr_lt_w
    have hG1 : GraphAt mem1 wAddr W := by
      intro i hi
      have hlt : wAddr + i < h := by
        have := graph_encode_length W
        omega
      rw [hfr1 _ (Or.inl hlt)]
      exact hG_at i hi
    have hZ1 : ZeroFrom mem1 (h + coreParamsSize r) := by
      intro a ha
      rw [hfr1 a (Or.inr ha)]
      exact hZero a (by omega)
    refine runs_seq_assign_le (v := h + coreParamsSize r)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_add (Expr.eval_const (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by simp [startState])) (by omega))
          (by omega))
        hp_w) ?_
    refine runs_seq_call_le
      (C := coreEntryContract ParamConfig.default M r w K_B C_stepC C_left S_B C_sp_rt)
      (vs := [q, wAddr, h, outAddr, h + coreParamsSize r]) hCore ?_ ?_ ?_ ?_
    · simp [evalArgs, Expr.eval, startState]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
    · refine ⟨q, wAddr, h, outAddr, h + coreParamsSize r, W, rfl,
        by decide, by decide, hrl, hqr, hcp1, hG1, hGv, hGl, hhi, hdeg,
        by omega, le_rfl, by omega, hdisj, Or.inl (by omega), hZ1,
        by dsimp only [S_C] at htot_space; omega⟩
    · intro v2 mem2 pos2 hpost2
      have ⟨hres, hv1, hv2, hZ2, hfr2⟩ :=
        hpost2 q wAddr h outAddr (h + coreParamsSize r) W rfl
          (by decide) (by decide) hrl hqr hcp1 hG1 hGv hGl hhi hdeg
          (by omega) le_rfl (by omega) hdisj (Or.inl (by omega)) hZ1
          (by dsimp only [S_C] at htot_space; omega)
      refine runs_ret_le (Expr.eval_reg_of_eq (by simp))
        ⟨v2, rfl, hres, by omega, by dsimp only [S_C] at htot_space; omega, hZ2,
          fun a ha hout => by
            dsimp only at hfr2 hfr1 ⊢
            rw [hfr2 a (by omega) hout, hfr1 a (Or.inl ha)]
            rfl⟩ ?_
      simp only [writeCoreParamsContract, coreEntryContract, List.getD_cons_zero,
        List.getD_cons_succ, argsSize, Expr.size]
      dsimp only [K_C] at hcost_total
      omega

/-! ## 4. Non-Vacuity and Counterexample for Additive `OuterProgContracts.outerCoreSpace` -/

/-- Non-vacuity witness for `coreAdapterContract`. -/
theorem coreAdapterContract_pre_example (C_core C_sp : ℕ) :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧
      (coreAdapterContract 0 1 (coreAdapterCost 0 1) C_core C_sp w).pre args mem := by
  let W : Graph := ⟨2, []⟩
  let wAddr : ℕ := 0
  let outAddr : ℕ := 2
  let h : ℕ := 6
  let w : ℕ := Nat.log 2 (h + coreAdapterSpace C_sp 0 1 2 (coreAdapterCost 0 1 1 W) + 17) + 1
  have hw : h + coreAdapterSpace C_sp 0 1 2 (coreAdapterCost 0 1 1 W) + 17 < 2 ^ w :=
    Nat.lt_pow_succ_log_self (by decide) _
  refine ⟨w, [1, wAddr, 0, 1, outAddr, h], initMem W.encode, ?_,
    1, wAddr, outAddr, h, W, rfl, le_rfl, le_rfl, one_le_ell 0,
    by simpa using graphAt_initMem_encode W [],
    fun _ hmem => by simp [W] at hmem,
    fun _ hmem => by simp [W] at hmem,
    by simp [W],
    by have := four_le_NOf 0 1; simp [W]; omega,
    fun v _ => by simp [W, Graph.deg, Graph.degIn, Graph.inside],
    fun a ha => zeroFrom_initMem W.encode a (by simp [W, Graph.encode]; omega),
    by simp [W, Graph.m, wAddr, h],
    by simp [W, outAddr, h],
    Or.inr (by simp [W, Graph.m, wAddr, outAddr]),
    by dsimp only [W] at hw ⊢; omega, by omega, by omega, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **Counterexample showing `OuterProgContracts.outerCoreSpace` is too small for `coreEntrySpace`:**
for every fixed space multiplier `C_sp : ℕ`, at `M = 2 ^ (C_sp + 1)`, `r = 1`, `q = 1`, and the
2-vertex empty graph `W = ⟨2, []⟩`, any `ccost ≤ 2 * (NOf M 1) ^ 2 * (WParam ParamConfig.default M) ^ 20`
(the size-sensitive cost bound) satisfies
`OuterProgContracts.outerCoreSpace C_sp W.n ccost < coreParamsSize 1 + coreEntrySpace S_B S_C ParamConfig.default M 1 1`. -/
theorem outerCoreSpace_too_small_counterexample (C_sp S_B S_C : ℕ) :
    let M := 2 ^ (C_sp + 1)
    let W : Graph := ⟨2, []⟩
    ∀ ccost : ℕ,
      ccost ≤ W.n * (NOf M 1) ^ 2 * (WParam ParamConfig.default M) ^ (10 * 1 ^ 2 + 10) →
      outerCoreSpace C_sp W.n ccost <
        coreParamsSize 1 + coreEntrySpace S_B S_C ParamConfig.default M 1 1 := by
  intro M W ccost hccost
  set T : ℕ := coreTimeBound ParamConfig.default M 1 1
  have hT_eq : T = (NOf M 1) ^ 2 * (WParam ParamConfig.default M) ^ 20 := rfl
  have hccost' : ccost ≤ 2 * T := by
    have h2 : W.n * (NOf M 1) ^ 2 * (WParam ParamConfig.default M) ^ (10 * 1 ^ 2 + 10) = 2 * T := by
      simp [W, T, coreTimeBound, Nat.mul_assoc]
    omega
  have hT_ge : 3126 ≤ T := by
    have hN4 : 4 ≤ NOf M 1 := four_le_NOf M 1
    have hW2 : 2 ≤ WParam ParamConfig.default M := by unfold WParam; omega
    have hW20 : 2 ^ 20 ≤ (WParam ParamConfig.default M) ^ 20 := Nat.pow_le_pow_left hW2 20
    have hN2 : 16 ≤ (NOf M 1) ^ 2 := by nlinarith
    rw [hT_eq]
    exact le_trans (by decide : 3126 ≤ 16 * 2 ^ 20) (Nat.mul_le_mul hN2 hW20)
  have hN_gt : C_sp < NOf M 1 := by
    have h1 : 2 * M + 2 ≤ (NOf M 1) ^ 1 := two_mul_add_two_le_NOf_pow (M := M) (r := 1) le_rfl
    have h2 : C_sp + 1 < 2 ^ (C_sp + 1) := Nat.lt_two_pow_self
    simp only [pow_one] at h1
    omega
  have houter_le : outerCoreSpace C_sp W.n ccost ≤ 3 * C_sp * T := by
    unfold outerCoreSpace
    have h1 : ccost + (W.n + 3) ^ 5 + 1 ≤ 3 * T := by
      have : (W.n + 3) ^ 5 + 1 = 3126 := by decide
      omega
    calc C_sp * (ccost + (W.n + 3) ^ 5 + 1) ≤ C_sp * (3 * T) := Nat.mul_le_mul_left C_sp h1
      _ = 3 * C_sp * T := by ring
  have hbase_gt : 3 * C_sp < coreSpaceConst S_B S_C * coreSpaceBase M 1 := by
    have hcs : 1000 ≤ coreSpaceConst S_B S_C := le_max_right _ _
    have hcb : NOf M 1 ≤ coreSpaceBase M 1 := by
      unfold coreSpaceBase
      have hL1 : 1 ≤ LParam M := by unfold LParam; have := one_le_ell M; omega
      have h1 : NOf M 1 ≤ 2048 * LParam M * (NOf M 1) ^ 1 + 3 := by
        simp only [pow_one]; nlinarith
      exact le_trans h1 (Nat.le_self_pow (by decide) _)
    calc 3 * C_sp < 3 * NOf M 1 := by omega
      _ ≤ 1000 * NOf M 1 := by omega
      _ ≤ coreSpaceConst S_B S_C * coreSpaceBase M 1 := Nat.mul_le_mul hcs hcb
  have hT_pos : 0 < T := by omega
  have hlt : 3 * C_sp * T < coreSpaceConst S_B S_C * coreSpaceBase M 1 * T :=
    Nat.mul_lt_mul_of_pos_right hbase_gt hT_pos
  unfold coreEntrySpace coreProgSpace
  dsimp only [T] at houter_le hlt
  omega

end MinCostFlow.ExpanderDecomp
