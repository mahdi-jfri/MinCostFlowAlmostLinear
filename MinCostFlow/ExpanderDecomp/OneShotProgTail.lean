module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgStepC3D
import MinCostFlow.ExpanderDecomp.RouteMeets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `OneShot` Word-RAM Definitions, Cost/Space Envelopes, and Steps C–D Tail (`OneShotProgTail`)

Defines the `OneShot` Word-RAM procedure (`oneShotStepC2Stmt`, `oneShotTailCD`, `oneShotProc`),
its contract (`oneShotContract`), its space/cost envelopes (`oneShotProgSpace`,
`oneShotProgCost`), and proves `oneShotTailCD_runs` combining Stage C1 (`OneShotProgStepC`),
`stepCMacro` (`ProgStepCSpec.stepCContract`), and Stage C3+D (`OneShotProgStepC3D`).
The top-level verification `oneShotProc_meetsContract` is in `OneShotProg.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Space, Cost, Procedure, and Contract -/

/-- Heap advance and word-size headroom bound for `oneShotProc` at level `q`, given per-call space
`Sprev` for `coreOn` at level `q - 1`. -/
def oneShotProgSpace (S_B S_C : ℕ) (cfg : ParamConfig) (M r q Sprev : ℕ) : ℕ :=
  let N := NOf M r
  let L := LParam M
  let F := FParam cfg M
  100 * N * L * Sprev + (S_B + S_C + 2) * coreSpaceBase M r * N ^ (q + 1) * L ^ 8 +
    65536 * N ^ q * L ^ 3 * F ^ (2 * q)

/-- Step-count bound for `oneShotProc` at level `q`, given per-call cost `Tprev` for `coreOn`
at level `q - 1`. -/
def oneShotProgCost (K_B K_C : ℕ) (cfg : ParamConfig) (M r q Tprev : ℕ) : ℕ :=
  let N := NOf M r
  let L := LParam M
  let F := FParam cfg M
  100 * N * L * Tprev + (K_B + K_C + 2) * N ^ (q + 1) * L ^ 8 +
    (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * F ^ (2 * q)

/-- Stage C2–D fragment inside `oneShotTailCD`: runs `idx.stepCMacro`, copies cut or appends fake
edges and continues into `oneShotStepC3DStmt`. -/
def oneShotStepC2Stmt (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 26 (.reg 17)
    , .assign 17 (.bin .add (.bin .add (.reg 26) (.const 2)) (.bin .mul (.const 34) (.reg 2)))
    , .call 17 idx.stepCMacro
        [.reg 1, .reg 20, .reg 14, .reg 15, .reg 13, .reg 9, .reg 8,
         .reg 25, .reg 24, .reg 5, .reg 26, .reg 17]
    , .assign 19 (.load (.reg 26))
    , .assign 27 (.load (.bin .add (.reg 26) (.const 1)))
    , .cond (.bin .eq (.reg 19) (.const 1))
        (copyCutRetStmt idx)
        (seqStmts
          [ .call 29 idx.copyWords
              [.bin .mul (.const 2) (.reg 27), .bin .add (.reg 26) (.const 2),
               .bin .add (.reg 16) (.bin .mul (.const 2) (.reg 18))]
          , .assign 18 (.bin .add (.reg 18) (.reg 27))
          , oneShotStepC3DStmt idx ]) ]

/-- Shared tail of `oneShotProc` running Steps C (cloud + 17-colouring + `stepCMacro` +
`stepCLeftover`) and D (`stepD`) after Step B (or immediately for `q = 1`).
Expects `r1=gAddr, r2=k, r3=xAddr, r5=locAddr, r6=outAddr, r8=L, r9=Δ, r11=Pq, r13=z, r14=b,
r15=nBlocks, r16=fAddr, r17=hCur, r18=mFB`. -/
def oneShotTailCD (idx : CoreIdx) : Stmt :=
  .seq (oneShotStepC1Stmt idx) (oneShotStepC2Stmt idx)

/-- Standalone deterministic Word-RAM procedure for `OneShot(q, G, X)`.
`args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h]`. -/
def oneShotProc (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 8  (.load (.bin .add (.reg 4) (.const 1)))
    , .assign 9  (.load (.bin .add (.reg 4) (.const 2)))
    , .assign 10 (.load (.bin .add (.reg 4) (.const 3)))
    , .assign 11 (.load (.bin .add (.bin .add (.reg 4) (.const 4)) (.reg 0)))
    , .assign 12 (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 5)) (.reg 10)) (.reg 0)))
    , .assign 13 (.bin .div (.reg 2) (.reg 12))
    , .assign 16 (.reg 7)
    , .assign 17 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 2)))
    , .cond (.bin .eq (.reg 0) (.const 1))
        (seqStmts
          [ .assign 14 (.const 1)
          , .assign 15 (.reg 2)
          , .assign 18 (.const 0)
          , oneShotTailCD idx ])
        (seqStmts
          [ .assign 14 (.bin .div
              (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 6))
                (.bin .mul (.const 2) (.reg 10))) (.bin .sub (.reg 0) (.const 1))))
              (.const 2))
          , .assign 15 (.bin .div (.reg 2) (.reg 14))
          , .call 17 idx.stepB
              [.reg 0, .reg 1, .reg 2, .reg 3, .reg 14, .reg 15, .reg 13,
               .reg 4, .reg 5, .reg 16, .reg 6, .reg 17]
          , .assign 19 (.load (.reg 6))
          , .cond (.bin .eq (.reg 19) (.const 0))
              (.ret (.reg 17))
              (seqStmts
                [ .assign 18 (.load (.bin .add (.reg 6) (.const 1)))
                , oneShotTailCD idx ]) ]) ]

/-- Contract for `oneShotProc`: `args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h]`.
Delivers `∃ res, CoreOutAt mem' outAddr res ∧ OneShotSpec (coreParamsOf cfg M r) q G X res`,
heap cursor `v ∈ [h, h + oneShotProgSpace]` with `ZeroFrom mem' v`, `locAddr` zero preservation,
and frame below `h` outside `[outAddr, outAddr + 2 + k)`. -/
noncomputable def oneShotContract (cfg : ParamConfig) (M r q w K_B K_C S_B S_C Tprev Sprev : ℕ) :
    Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    ∃ (gAddr k xAddr pAddr locAddr outAddr h : ℕ) (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] ∧
      12 ≤ cfg.a₀ ∧ 4 ≤ cfg.a ∧ r ≤ ell M ∧ 1 ≤ q ∧ q ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r ∧
      VertsAt mem xAddr k X ∧
      X ⊆ Finset.range G.n ∧
      (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) ∧
      G.m ≤ 2 * cp.Δ * k ∧
      (q = 1 → 2 ≤ k ∧ k ≤ cp.N) ∧
      (2 ≤ q → cp.N ^ (q - 1) / 2 ≤ k ∧ k ≤ cp.N ^ q) ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + k ≤ h ∧
      pAddr + coreParamsSize r ≤ h ∧
      locAddr + G.n ≤ h ∧
      outAddr + 2 + k ≤ h ∧
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) ∧
      DisjointRange locAddr G.n xAddr k ∧
      DisjointRange locAddr G.n pAddr (coreParamsSize r) ∧
      DisjointRange locAddr G.n outAddr (2 + k) ∧
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + k) xAddr k ∧
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) ∧
      ZeroFrom mem h ∧
      h + oneShotProgSpace S_B S_C cfg M r q Sprev < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    ∀ (gAddr k xAddr pAddr locAddr outAddr h : ℕ) (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] →
      12 ≤ cfg.a₀ → 4 ≤ cfg.a → r ≤ ell M → 1 ≤ q → q ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem gAddr G →
      G.IsValid →
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r →
      VertsAt mem xAddr k X →
      X ⊆ Finset.range G.n →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) →
      G.m ≤ 2 * cp.Δ * k →
      (q = 1 → 2 ≤ k ∧ k ≤ cp.N) →
      (2 ≤ q → cp.N ^ (q - 1) / 2 ≤ k ∧ k ≤ cp.N ^ q) →
      (∀ u < G.n, mem (locAddr + u) = 0) →
      gAddr + 2 + 2 * G.m ≤ h →
      xAddr + k ≤ h →
      pAddr + coreParamsSize r ≤ h →
      locAddr + G.n ≤ h →
      outAddr + 2 + k ≤ h →
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) →
      DisjointRange locAddr G.n xAddr k →
      DisjointRange locAddr G.n pAddr (coreParamsSize r) →
      DisjointRange locAddr G.n outAddr (2 + k) →
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) →
      DisjointRange outAddr (2 + k) xAddr k →
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) →
      ZeroFrom mem h →
      h + oneShotProgSpace S_B S_C cfg M r q Sprev < 2 ^ w →
      (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ OneShotSpec cp q G X res) ∧
      h ≤ v ∧ v ≤ h + oneShotProgSpace S_B S_C cfg M r q Sprev ∧
      ZeroFrom mem' v ∧
      (∀ u < G.n, mem' (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem' a = mem a)
  cost _ _ := oneShotProgCost K_B K_C cfg M r q Tprev

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. `NoRand` and Stage C2–D Verification -/

lemma oneShotStepC2Stmt_noRand (idx : CoreIdx) : (oneShotStepC2Stmt idx).NoRand := by
  simp [oneShotStepC2Stmt, copyCutRetStmt_noRand, oneShotStepC3DStmt_noRand, seqStmts, Stmt.NoRand]

lemma oneShotTailCD_noRand (idx : CoreIdx) : (oneShotTailCD idx).NoRand := by
  simp [oneShotTailCD, oneShotStepC1Stmt_noRand, oneShotStepC2Stmt_noRand, Stmt.NoRand]

lemma oneShotProc_noRand (idx : CoreIdx) : (oneShotProc idx).NoRand := by
  simp [oneShotProc, oneShotTailCD_noRand, seqStmts, Stmt.NoRand]

/-- Verified execution of `oneShotStepC2Stmt` (after Stage C1 has prepared `LenListAt` and
`edgeColor17 (cloud numBlk)`). -/
private lemma oneShotStepC2_runs {idx : CoreIdx} {cfg : ParamConfig}
    {M r q w C_stepC C_left C_sp : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hstepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud C_stepC C_sp w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w))
    (st1 : State) (ω : ℕ → Bool)
    {gAddr k xAddr locAddr outAddr h lenXAddr outC1 colAddr colM mFB b numBlk z hBound : ℕ}
    {G : Graph} {X : Finset ℕ} {callsB : List RoutedCall} {mem₀ : ℕ → ℕ}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hG : GraphAt st1.mem gAddr G) (hGvalid : G.IsValid)
    (hX : VertsAt st1.mem xAddr k X) (hLenX : LenListAt st1.mem lenXAddr (X.sort (· ≤ ·)))
    (hXrange : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hk2 : 2 ≤ k) (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_pos : 0 < b) (hble : b ≤ k)
    (hnb_eq : numBlk = numFullBlocks (X.sort (· ≤ ·)) b)
    (hnb_ge1 : 1 ≤ numBlk) (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc : ∀ u < G.n, st1.mem (locAddr + u) = 0)
    (hcallsB_len : callsB.length ≤ 49 * (coreParamsOf cfg M r).L + 2)
    (hcallsB_v : ∀ c ∈ callsB, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100
      (coreParamsOf cfg M r).L) z)
    (hcallsB_exp : ∀ i < numBlk,
      (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
        (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * ((coreParamsOf cfg M r).P (q - 1) : ℝ))))
    (hmFB_eq : mFB = (callsFakeEdges callsB).length)
    (hFB : EdgesAt st1.mem h (callsFakeEdges callsB))
    (hcloud_ok : 2 ≤ numBlk →
      (cloud numBlk).n = numBlk ∧
      (cloud numBlk).IsValid ∧
      (∀ v < numBlk, (cloud numBlk).deg v ≤ 9) ∧
      colM = (edgeColor17 (cloud numBlk)).length ∧
      ColoredEdgesAt st1.mem colAddr (edgeColor17 (cloud numBlk)))
    (hg_le : gAddr + 2 + 2 * G.m ≤ h) (hx_le : xAddr + k ≤ h)
    (hloc_le : locAddr + G.n ≤ h) (hout_le : outAddr + 2 + k ≤ h)
    (hlenX_ge : h + 2 * k ≤ lenXAddr) (hlenX_le : lenXAddr + 1 + k ≤ outC1)
    (hcol_ge : h ≤ colAddr) (hcol_le : colAddr + 3 * colM ≤ outC1)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hZero : ZeroFrom st1.mem outC1)
    (hframe₀ : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st1.mem a = mem₀ a)
    (hBound_ge : outC1 + (2 + 34 * k) +
      stepCSpace C_sp G.n k numBlk
        (stepCMacroCost (coreParamsOf cfg M r) routeOrCut routerCallCost cloud G X
          (X.sort (· ≤ ·)) b numBlk z) +
      (2 + 2 * k) +
      stepCLeftoverSpace C_sp G.n k
        (stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X (X.sort (· ≤ ·)) b z) +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound)
    (hBound_w : hBound < 2 ^ w)
    (hr1 : st1.regs 1 = gAddr) (hr2 : st1.regs 2 = k) (hr3 : st1.regs 3 = xAddr)
    (hr5 : st1.regs 5 = locAddr) (hr6 : st1.regs 6 = outAddr)
    (hr8 : st1.regs 8 = (coreParamsOf cfg M r).L) (hr9 : st1.regs 9 = (coreParamsOf cfg M r).Δ)
    (hr11 : st1.regs 11 = (coreParamsOf cfg M r).P q) (hr13 : st1.regs 13 = z)
    (hr14 : st1.regs 14 = b) (hr15 : st1.regs 15 = numBlk)
    (hr16 : st1.regs 16 = h) (hr17 : st1.regs 17 = outC1) (hr18 : st1.regs 18 = mFB)
    (hr20 : st1.regs 20 = lenXAddr) (hr24 : st1.regs 24 = colAddr) (hr25 : st1.regs 25 = colM) :
    ∃ v st' c,
      Runs w p ω (oneShotStepC2Stmt idx) st1 (.returned v) st' c ∧
      (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧
        OneShotSpec (coreParamsOf cfg M r) q G X res) ∧
      h ≤ v ∧ v ≤ hBound ∧
      ZeroFrom st'.mem v ∧
      (∀ u < G.n, st'.mem (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ (C_stepC * stepCMacroCost (coreParamsOf cfg M r) routeOrCut routerCallCost cloud G X
            (X.sort (· ≤ ·)) b numBlk z + C_stepC) +
          (C_left * stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X
            (X.sort (· ≤ ·)) b z + C_left) +
          copyWordsCost (2 * k) + copyWordsCost (2 * k) +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
            (FParam cfg M) ^ (2 * q) + 250 := by
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hpw : vs.Pairwise (· < ·) :=
    ((Finset.pairwise_sort X (· ≤ ·)).and hnd).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hvslen : vs.length = k := by rw [Finset.length_sort]; exact hX.1.symm
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hXL : X.card < 2 ^ cp.L := lt_of_le_of_lt (hX.1 ▸ hkNq) (hcfg.hNq_lt_two_pow hqr)
  have hnb_le_k : numBlk ≤ k := by
    rw [hnb_eq]; unfold numFullBlocks; rw [hvslen]; exact Nat.div_le_self k b
  set costM := stepCMacroCost cp routeOrCut routerCallCost cloud G X vs b numBlk z
  set costL := stepCLeftoverCost cp routerCallCost G X vs b z
  set hC1 := outC1 + 2 + 34 * k
  have hbig : 65536 ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
    have hN4 := four_le_NOf M r
    have h1 : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
        (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (one_le_FParam cfg M))
    calc 65536 = 65536 * 1 := (Nat.mul_one _).symm
      _ ≤ 65536 * ((NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
          Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  have hw32 : 32 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw32
  have h2_lt : 2 < 2 ^ w := by omega
  have h34_lt : 34 < 2 ^ w := by omega
  have hΔ_lt : cp.Δ < 2 ^ w := by
    have hN4 := four_le_NOf M r
    have h1 : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 2 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
        (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (one_le_FParam cfg M))
    have hle : cp.Δ ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
      have : cp.Δ = 1024 * LParam M := rfl
      calc cp.Δ = 1024 * LParam M * 1 := by rw [this, Nat.mul_one]
        _ ≤ 65536 * LParam M * ((NOf M r) ^ q * (LParam M) ^ 2 * (FParam cfg M) ^ (2 * q)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) h1
        _ = _ := by ring
    omega
  have hL_lt : cp.L < 2 ^ w := by
    have : cp.L ≤ cp.Δ := by change LParam M ≤ 1024 * LParam M; omega
    omega
  have hstepM_spec := stepCMacro_spec hcfg routeOrCut_isMatchingPlayer
    (isCloudExpander_cloud_of_paramConfig cfg M r ha0) (z := z)
    hXrange hGloop hdegG hXL hnd hvs hb_pos (hnb_eq ▸ hnb_ge1)
    (by have := hcfg.hP_pos (by omega : q - 1 ≤ r); positivity)
    (by
      rw [div_le_one (by have := hcfg.hP_pos (by omega : q - 1 ≤ r); positivity)]
      have : (1 : ℝ) ≤ cp.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega : q - 1 ≤ r)
      linarith)
    (hnb_eq ▸ hcallsB_exp)
  rw [← hnb_eq] at hstepM_spec
  suffices hret : ∃ out st' c,
      Runs w p ω (oneShotStepC2Stmt idx) st1 out st' c ∧
      (∃ v, out = .returned v ∧
        (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧ OneShotSpec cp q G X res) ∧
        h ≤ v ∧ v ≤ hBound ∧
        ZeroFrom st'.mem v ∧
        (∀ u < G.n, st'.mem (locAddr + u) = 0) ∧
        (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a)) ∧
      c ≤ (C_stepC * costM + C_stepC) + (C_left * costL + C_left) +
          copyWordsCost (2 * k) + copyWordsCost (2 * k) +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
            (FParam cfg M) ^ (2 * q) + 250 by
    rcases hret with ⟨_, st', c, hrun, ⟨v, rfl, hpost⟩, hc⟩
    exact ⟨v, st', c, hrun, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1,
      hpost.2.2.2.2.1, hpost.2.2.2.2.2, hc⟩
  refine runs_start_le ?_
  unfold oneShotStepC2Stmt seqStmts
  refine runs_seq_assign_le (v := outC1) (by rw [Expr.eval_reg, hr17]) ?_
  refine runs_seq_assign_le (v := hC1)
    (by simp [Expr.eval, hr2, hC1, h2_lt, h34_lt, show outC1 + 2 < 2 ^ w by omega,
      show 34 * k < 2 ^ w by omega, show outC1 + 2 + 34 * k < 2 ^ w by omega]) ?_
  have hstepC_pre : (stepCContract cp cloud C_stepC C_sp w).pre
      [gAddr, lenXAddr, b, numBlk, z, cp.Δ, cp.L, colM, colAddr, locAddr, outC1, hC1] st1.mem := by
    refine ⟨gAddr, lenXAddr, b, numBlk, z, colM, colAddr, locAddr, outC1, hC1, G, vs, rfl,
      hG, hGvalid, hLenX, hpw, hvs.symm ▸ hXrange, hvs.symm ▸ hGloop,
      hcfg.hΔ_pos, hvs.symm ▸ hdegG, by change 1 ≤ LParam M; omega,
      by rw [hvslen, hX.1]; exact hXL,
      hb_pos, hnb_eq, hcloud_ok, hloc, fun a ha => hZero a (by omega), ?_⟩
    rw [hvslen, hvs]
    refine ⟨⟨by omega, by omega, by omega, by omega, by unfold stepCOutSize; omega,
      hd_lg, Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), ?_, by omega⟩, hmG,
      by rw [hz_eq]; exact Nat.div_le_self _ _⟩
    change hC1 + stepCSpace C_sp G.n k numBlk costM < 2 ^ w
    omega
  refine runs_seq_call_le
    (vs := [gAddr, lenXAddr, b, numBlk, z, cp.Δ, cp.L, colM, colAddr, locAddr, outC1, hC1]) hstepC
    (by simp [evalArgs, Expr.eval, hr1, hr20, hr14, hr15, hr13, hr9, hr8, hr25, hr24, hr5])
    (by intro v hv; simp at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
        · rw [hz_eq]; have := Nat.div_le_self k (cp.D q); omega
        · exact hΔ_lt
        · exact hL_lt
        · omega
        · omega
        · omega
        · omega
        · omega)
    hstepC_pre ?_
  intro hAfterC1 mem2 _pos2 hpostM
  simp only [stepCContract, List.getD_cons_zero, List.getD_cons_succ] at hpostM
  have hrdG1 : readGraph st1.mem gAddr = G := readGraph_eq_of_graphAt hG
  have hrdX1 : readLenPrefixedList st1.mem lenXAddr = vs := readLenPrefixedList_eq_of_lenListAt hLenX
  rw [hrdG1, hrdX1, hvs, hvslen] at hpostM
  rcases hpostM with ⟨hOutM, hloc2, hhC1_le, hhC1_hi, hZero2, hframe2⟩
  have hhC1_le_Bound : hAfterC1 + (2 + 2 * k) + stepCLeftoverSpace C_sp G.n k costL +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound := by
    dsimp only [hC1] at hhC1_hi
    linarith only [hhC1_hi, hBound_ge]
  have hmem2_eq_lt_h : ∀ a < h, (a < locAddr ∨ locAddr + G.n ≤ a) → mem2 a = st1.mem a :=
    fun a ha hnl => hframe2 a (by omega) hnl (Or.inl (by omega))
  have hmem2_eq_f : ∀ a, h ≤ a → a < h + 2 * k → mem2 a = st1.mem a := fun a h1 h2 =>
    hframe2 a (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  refine runs_seq_assign_le (v := mem2 outC1) (by simp [Expr.eval]) ?_
  refine runs_seq_assign_le (v := mem2 (outC1 + 1))
    (by simp [Expr.eval, hw0, show outC1 + 1 < 2 ^ w by omega]) ?_
  cases hres : stepCMacro cp routeOrCut cloud G X vs b numBlk z with
  | inl U =>
    rw [hres] at hOutM hstepM_spec
    rcases hOutM with ⟨htag1, U_list, hUnd, hUfin, hUlen, hUlat⟩
    have hUsub : U ⊆ X := hstepM_spec.1
    have hUlen_le : U_list.length ≤ k := by
      rw [← List.toFinset_card_of_nodup hUnd, hUfin, hX.1]; exact Finset.card_le_card hUsub
    refine runs_cond_le (v := 1) (by simp [Expr.eval, htag1, hw0]) ?_ (fun h => absurd h (by decide))
    intro _
    have hfr2 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem2 a = mem₀ a := fun a ha hno => by
      by_cases hloca : locAddr ≤ a ∧ a < locAddr + G.n
      · have hu : a - locAddr < G.n := by omega
        have ha_eq : a = locAddr + (a - locAddr) := by omega
        rw [ha_eq, hloc2 (a - locAddr) hu, ← hloc (a - locAddr) hu, ← ha_eq, hframe₀ a ha hno]
      · rw [hmem2_eq_lt_h a ha (by omega)]
        exact hframe₀ a ha hno
    apply copyCutRet_conseq hcopy (outAddr := outAddr) (hRet := hAfterC1) (srcOut := outC1)
      (locAddr := locAddr) (h := h) (k := k) (n := G.n) (U := U) (U_list := U_list) (mem₀ := mem₀)
      (by simp [hr6]) (by simp) (by simp) (by simp [hUlen])
      hUnd hUfin hUlat hUlen_le (hUsub.trans hXrange) hout_le hloc_le (by omega)
      (by dsimp only [hC1] at hhC1_le; omega) (by omega) (by omega) hd_lo hZero2 hloc2 hfr2
    · intro stF hUout hZF hlocF hfrF
      exact ⟨hAfterC1, rfl, ⟨.cut U, hUout, by simpa [OneShotSpec, hz_eq, hX.1] using hstepM_spec⟩,
        by omega, by omega, hZF, hlocF, hfrF⟩
    · intro cF hcF
      simp only [Expr.size, argsSize, stepCContract,
        List.getD_cons_zero, List.getD_cons_succ, hrdG1, hrdX1, hvs]
      have hcp_le : copyWordsCost U_list.length ≤ copyWordsCost (2 * k) := by
        unfold copyWordsCost; omega
      dsimp only [costM, costL, cp, vs]
      omega
  | inr callsC =>
    rw [hres] at hOutM hstepM_spec
    rcases hOutM with ⟨htag0, hmC_eq, hFC_at⟩
    rcases hstepM_spec with ⟨hcallsC_len, hcallsC_v, hcallsBC_exp⟩
    set callsBC := callsB ++ callsC
    have hcallsBC_len : callsBC.length ≤ 49 * cp.L + 19 := by
      simp only [callsBC, List.length_append]; omega
    have hcallsBC_v : ∀ c ∈ callsBC, c.Valid G X (routeCong cp.Δ 100 cp.L) z := by
      intro c hc
      simp only [callsBC, List.mem_append] at hc
      rcases hc with h1 | h2
      · exact hcallsB_v c h1
      · exact hcallsC_v c h2
    have hBC_le_Δ : callsBC.length ≤ cp.Δ := by
      have hΔ : 49 * cp.L + 19 ≤ cp.Δ := by change 49 * LParam M + 19 ≤ 1024 * LParam M; omega
      omega
    have hmBC_le : (callsFakeEdges callsBC).length ≤ k :=
      callsFakeEdges_length_le_k ha hrl hq1 hqr hBC_le_Δ (hz_eq ▸ hcallsBC_v)
    have hmBC_sum : (callsFakeEdges callsBC).length = mFB + (callsFakeEdges callsC).length := by
      simp [callsBC, callsFakeEdges, hmFB_eq]
    set mC := (callsFakeEdges callsC).length
    refine runs_cond_le (v := 0) (by simp [Expr.eval, htag0, hw0]) (fun h => absurd rfl h) ?_
    intro _
    have hcp_pre : (copyWordsContract w).pre [2 * mC, outC1 + 2, h + 2 * mFB] mem2 := by
      refine ⟨2 * mC, outC1 + 2, h + 2 * mFB, rfl, by omega, by omega, by omega, by omega,
        Or.inl (by omega), fun i hi => ?_⟩
      have hlt := edgesAt_words_lt hFC_at hXrange (fun e he => by
        unfold callsFakeEdges at he
        obtain ⟨c, hc, hce⟩ := List.mem_flatMap.mp he
        exact (hcallsC_v c hc).2.2.2.1 e hce) i hi
      omega
    refine runs_seq_call_le (vs := [2 * mC, outC1 + 2, h + 2 * mFB]) hcopy
      (by simp [evalArgs, Expr.eval, hr16, hr18, hmC_eq, h2_lt,
        show 2 * mC < 2 ^ w by omega, show outC1 + 2 < 2 ^ w by omega,
        show 2 * mFB < 2 ^ w by omega, show h + 2 * mFB < 2 ^ w by omega])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      hcp_pre ?_
    intro _v3 mem3 _pos3 hpostCp
    simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
    rcases hpostCp with ⟨_, hcp_eq, hcp_fr⟩
    refine runs_seq_assign_le (v := mFB + mC)
      (by simp [Expr.eval, hr18, hmC_eq, show mFB + mC < 2 ^ w by omega]) ?_
    have hmem3_lt_h : ∀ a < h, (a < locAddr ∨ locAddr + G.n ≤ a) → mem3 a = st1.mem a :=
      fun a ha hnl => by rw [hcp_fr a (Or.inl (by omega))]; exact hmem2_eq_lt_h a ha hnl
    have hG3 : GraphAt mem3 gAddr G :=
      hG.congr fun a h1 h2 => by
        have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
        exact hmem3_lt_h a (by omega)
          (by rcases hd_lg with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
    have hX3 : VertsAt mem3 xAddr k X := by
      refine ⟨hX.1, fun i hi => ?_⟩
      have hik : i < k := by rw [Finset.length_sort] at hi; rw [hX.1]; exact hi
      rw [hmem3_lt_h (xAddr + i) (by omega)
        (by rcases hd_lx with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])]
      exact hX.2 i hi
    have hLenX3 : LenListAt mem3 lenXAddr vs := by
      have hag : ∀ a, lenXAddr ≤ a → a < lenXAddr + 1 + k → mem3 a = st1.mem a := fun a h1 h2 => by
        rw [hcp_fr a (Or.inr (by omega)), hframe2 a (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      refine ⟨by rw [hag lenXAddr le_rfl (by omega)]; exact hLenX.1,
        fun i hi => by rw [hag (lenXAddr + 1 + i) (by omega) (by omega)]; exact hLenX.2 i hi⟩
    have hFBC3 : EdgesAt mem3 h (callsFakeEdges callsBC) := by
      have hcat : callsFakeEdges callsBC = callsFakeEdges callsB ++ callsFakeEdges callsC := by
        simp [callsBC, callsFakeEdges]
      rw [hcat]
      refine edgesAt_append ?_ ?_
      · intro j hj
        have h1 := hFB j hj
        have hj' : j < mFB := by omega
        refine ⟨?_, ?_⟩
        · rw [hcp_fr (h + 2 * j) (Or.inl (by omega)), hmem2_eq_f (h + 2 * j) (by omega) (by omega)]
          exact h1.1
        · rw [hcp_fr (h + 2 * j + 1) (Or.inl (by omega)),
            hmem2_eq_f (h + 2 * j + 1) (by omega) (by omega)]
          exact h1.2
      · rw [← hmFB_eq]
        exact edgesAt_of_copyWords hFC_at hcp_eq
    have hloc3 : ∀ u < G.n, mem3 (locAddr + u) = 0 := fun u hu => by
      rw [hcp_fr (locAddr + u) (Or.inl (by omega))]; exact hloc2 u hu
    have hZero3 : ZeroFrom mem3 hAfterC1 := fun a ha => by
      rw [hcp_fr a (Or.inr (by omega))]; exact hZero2 a ha
    have hfr3 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem3 a = mem₀ a := fun a ha hno => by
      by_cases hloca : locAddr ≤ a ∧ a < locAddr + G.n
      · have hu : a - locAddr < G.n := by omega
        have ha_eq : a = locAddr + (a - locAddr) := by omega
        rw [ha_eq, hloc3 (a - locAddr) hu, ← hloc (a - locAddr) hu, ← ha_eq, hframe₀ a ha hno]
      · rw [hmem3_lt_h a ha (by omega)]
        exact hframe₀ a ha hno
    have hγ_eq : cp.α * (1 / (2 * (cp.P (q - 1) : ℝ))) / 10 =
        cp.α / (20 * (cp.P (q - 1) : ℝ)) := by ring
    rw [hγ_eq] at hcallsBC_exp
    apply oneShotStepC3D_conseq hcopy hleft hstepD (gAddr := gAddr) (k := k) (xAddr := xAddr)
      (locAddr := locAddr) (outAddr := outAddr) (h := h) (lenXAddr := lenXAddr) (hCur := hAfterC1)
      (mBC := mFB + mC) (b := b) (z := z) (hBound := hBound) (G := G) (X := X) (callsBC := callsBC)
      (mem₀ := mem₀) ha0 ha hrl hq1 hqr
      hG3 hGvalid hX3 hLenX3 hXrange hGloop hdegG hmG hk2 hkNq hb_pos hble hz_eq hloc3
      hcallsBC_len hcallsBC_v hcallsBC_exp hmBC_sum.symm hFBC3
      hg_le hx_le hloc_le hout_le hlenX_ge (by dsimp only [hC1] at hhC1_le; omega)
      hd_lg hd_lx hd_lo hd_og hd_ox hZero3 hfr3 hhC1_le_Bound hBound_w
      (by simp [hr1]) (by simp [hr2]) (by simp [hr3]) (by simp [hr5])
      (by simp [hr6]) (by simp [hr8, cp]) (by simp [hr9, cp]) (by simp [hr11, cp])
      (by simp [hr13]) (by simp [hr14]) (by simp [hr16])
      (by simp) (by simp) (by simp [hr20])
    · intro v stF hresF hv1 hv2 hZF hlocF hfrF
      exact ⟨v, rfl, hresF, hv1, hv2, hZF, hlocF, hfrF⟩
    · intro cF hcF
      simp only [Expr.size, argsSize, stepCContract, copyWordsContract,
        List.getD_cons_zero, List.getD_cons_succ, hrdG1, hrdX1, hvs]
      have hcp_le : copyWordsCost (2 * mC) ≤ copyWordsCost (2 * k) := by
        unfold copyWordsCost; omega
      dsimp only [costM, costL, cp, vs] at hcF ⊢
      omega

/-- Verified execution of `oneShotTailCD`: chains Stage C1 (`oneShotStepC1_runs`) and Stage C2–D
(`oneShotStepC2_runs`). -/
theorem oneShotTailCD_runs {idx : CoreIdx} {cfg : ParamConfig}
    {M r q w C_stepC C_left C_sp : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hcloud : MeetsContract w p idx.cloudExpander (cloudExpanderContract w))
    (hcol : MeetsContract w p idx.edgeColor17 (edgeColor17Contract w))
    (hstepC : MeetsContract w p idx.stepCMacro
      (stepCContract (coreParamsOf cfg M r) cloud C_stepC C_sp w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w))
    (st : State) (ω : ℕ → Bool)
    {gAddr k xAddr locAddr outAddr h hCur mFB b numBlk z hBound : ℕ}
    {G : Graph} {X : Finset ℕ} {callsB : List RoutedCall} {mem₀ : ℕ → ℕ}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hG : GraphAt st.mem gAddr G) (hGvalid : G.IsValid)
    (hGn : G.n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hX : VertsAt st.mem xAddr k X) (hXrange : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hk2 : 2 ≤ k) (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_pos : 0 < b) (hble : b ≤ k)
    (hnb_eq : numBlk = numFullBlocks (X.sort (· ≤ ·)) b)
    (hnb_ge1 : 1 ≤ numBlk) (hnb_le : numBlk ≤ 2 * (coreParamsOf cfg M r).N)
    (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hcallsB_len : callsB.length ≤ 49 * (coreParamsOf cfg M r).L + 2)
    (hcallsB_v : ∀ c ∈ callsB, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100
      (coreParamsOf cfg M r).L) z)
    (hcallsB_exp : ∀ i < numBlk,
      (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
        (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * ((coreParamsOf cfg M r).P (q - 1) : ℝ))))
    (hmFB_eq : mFB = (callsFakeEdges callsB).length)
    (hFB : EdgesAt st.mem h (callsFakeEdges callsB))
    (hg_le : gAddr + 2 + 2 * G.m ≤ h) (hx_le : xAddr + k ≤ h)
    (hloc_le : locAddr + G.n ≤ h) (hout_le : outAddr + 2 + k ≤ h)
    (hhCur_ge : h + 2 * k ≤ hCur)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hZero : ZeroFrom st.mem hCur)
    (hframe₀ : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)
    (hBound_ge : hCur +
      stepCSpaceConst C_sp * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound)
    (hBound_w : hBound < 2 ^ w)
    (hr1 : st.regs 1 = gAddr) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = outAddr)
    (hr8 : st.regs 8 = (coreParamsOf cfg M r).L) (hr9 : st.regs 9 = (coreParamsOf cfg M r).Δ)
    (hr11 : st.regs 11 = (coreParamsOf cfg M r).P q) (hr13 : st.regs 13 = z)
    (hr14 : st.regs 14 = b) (hr15 : st.regs 15 = numBlk)
    (hr16 : st.regs 16 = h) (hr17 : st.regs 17 = hCur) (hr18 : st.regs 18 = mFB) :
    ∃ v st' c,
      Runs w p ω (oneShotTailCD idx) st (.returned v) st' c ∧
      (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧
        OneShotSpec (coreParamsOf cfg M r) q G X res) ∧
      h ≤ v ∧ v ≤ hBound ∧
      ZeroFrom st'.mem v ∧
      (∀ u < G.n, st'.mem (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ stepCTimeConst C_stepC C_left * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
            (FParam cfg M) ^ (2 * q) := by
  set cp := coreParamsOf cfg M r
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hXL : X.card < 2 ^ cp.L := lt_of_le_of_lt (hX.1 ▸ hkNq) (hcfg.hNq_lt_two_pow hqr)
  have hnb_le_k : numBlk ≤ k := by
    rw [hnb_eq]; unfold numFullBlocks; rw [Finset.length_sort, ← hX.1]; exact Nat.div_le_self k b
  set costM := stepCMacroCost cp routeOrCut routerCallCost cloud G X (X.sort (· ≤ ·)) b numBlk z
  set costL := stepCLeftoverCost cp routerCallCost G X (X.sort (· ≤ ·)) b z
  have hcostM_bd := stepCMacroCost_le_oneShot (cfg := cfg) (z := z) hXrange hGloop hdegG hXL
    (hX.1 ▸ hk2) (hX.1 ▸ hkNq) hb_pos hnb_eq hnb_le
  have hcostL_bd := stepCLeftoverCost_le_oneShot (cfg := cfg) (z := z) hXrange hGloop hdegG hXL
    (hX.1 ▸ hk2) (hX.1 ▸ hkNq) hb_pos (hX.1 ▸ hble)
  have hsp_bd := stepC_space_le_oneShot (C_sp := C_sp) hqr hGn hkNq hnb_le_k hcostM_bd hcostL_bd
  have htm_bd := stepC_time_le_oneShot (C_stepC := C_stepC) (C_left := C_left) hkNq hnb_le_k
    hcostM_bd hcostL_bd
  have hw32 : 32 < 2 ^ w := by
    have hN4 := four_le_NOf M r
    have hL4 := four_le_LParam M
    have h1 : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
        (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (one_le_FParam cfg M))
    have hbig : 65536 ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
      calc 65536 = 65536 * 1 := (Nat.mul_one _).symm
        _ ≤ 65536 * ((NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
            Nat.mul_le_mul_left _ h1
        _ = _ := by ring
    omega
  have hC1_hw : hCur + (1 + k) + (3 + 41 * numBlk) + cloudExpanderSpace numBlk < 2 ^ w := by omega
  obtain ⟨o1, st1, c1, hrun1, hq1_out, hc1⟩ :=
    oneShotStepC1_runs hcopy hcloud hcol st ω hr2 hr3 hr15 hr17 hX hXrange (by omega)
      (by omega) hZero hC1_hw hw32
  cases o1 with
  | returned _ => exact False.elim hq1_out
  | normal =>
    rcases hq1_out with ⟨h1r20, h1r24, h1r25_le, h1r17_hi, h1r17_lo, h1regs, h1LenX, h1cloud, h1Zero, h1ag⟩
    have hG1 : GraphAt st1.mem gAddr G :=
      hG.congr fun a h1 h2 => by
        have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
        exact h1ag a (by omega)
    have hX1 : VertsAt st1.mem xAddr k X := by
      refine ⟨hX.1, fun i hi => ?_⟩
      have hik : i < k := by rw [Finset.length_sort] at hi; rw [hX.1]; exact hi
      rw [h1ag (xAddr + i) (by omega)]; exact hX.2 i hi
    have hloc1 : ∀ u < G.n, st1.mem (locAddr + u) = 0 := fun u hu => by
      rw [h1ag (locAddr + u) (by omega)]; exact hloc u hu
    have hFB1 : EdgesAt st1.mem h (callsFakeEdges callsB) := fun j hj => by
      have hmFB_le : (callsFakeEdges callsB).length ≤ k :=
        callsFakeEdges_length_le_k ha hrl hq1 hqr
          (by have := four_le_LParam M; change callsB.length ≤ 49 * LParam M + 2 at hcallsB_len;
              change callsB.length ≤ 1024 * LParam M; omega)
          (hz_eq ▸ hcallsB_v)
      have h1 := hFB j hj
      exact ⟨by rw [h1ag (h + 2 * j) (by omega)]; exact h1.1,
        by rw [h1ag (h + 2 * j + 1) (by omega)]; exact h1.2⟩
    have hfr1 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st1.mem a = mem₀ a :=
      fun a ha hno => by rw [h1ag a (by omega)]; exact hframe₀ a ha hno
    have hB2 : st1.regs 17 + (2 + 34 * k) + stepCSpace C_sp G.n k numBlk costM + (2 + 2 * k) +
        stepCLeftoverSpace C_sp G.n k costL +
        65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound := by
      dsimp only [costM, costL, cp]
      linarith only [h1r17_hi, hsp_bd, hBound_ge]
    obtain ⟨v, stF, c2, hrun2, hresF, hv1, hv2, hZF, hlocF, hfrF, hc2⟩ :=
      oneShotStepC2_runs hcopy hstepC hleft hstepD st1 ω ha0 ha hrl hq1 hqr
        hG1 hGvalid hX1 h1LenX hXrange hGloop hdegG hmG hk2 hkNq hb_pos hble hnb_eq hnb_ge1 hz_eq
        hloc1 hcallsB_len hcallsB_v hcallsB_exp hmFB_eq hFB1
        (fun h2 => by obtain ⟨a1, a2, a3, a4, _, a6⟩ := h1cloud h2; exact ⟨a1, a2, a3, a4, a6⟩)
        hg_le hx_le hloc_le hout_le hhCur_ge (by omega) (by omega) (by omega)
        hd_lg hd_lx hd_lo hd_og hd_ox h1Zero hfr1 hB2 hBound_w
        (by rw [h1regs 1 (by omega) (by omega), hr1])
        (by rw [h1regs 2 (by omega) (by omega), hr2])
        (by rw [h1regs 3 (by omega) (by omega), hr3])
        (by rw [h1regs 5 (by omega) (by omega), hr5])
        (by rw [h1regs 6 (by omega) (by omega), hr6])
        (by rw [h1regs 8 (by omega) (by omega), hr8])
        (by rw [h1regs 9 (by omega) (by omega), hr9])
        (by rw [h1regs 11 (by omega) (by omega), hr11])
        (by rw [h1regs 13 (by omega) (by omega), hr13])
        (by rw [h1regs 14 (by omega) (by omega), hr14])
        (by rw [h1regs 15 (by omega) (by omega), hr15])
        (by rw [h1regs 16 (by omega) (by omega), hr16])
        rfl (by rw [h1regs 18 (by omega) (by omega), hr18]) h1r20 rfl rfl
    refine ⟨v, stF, c1 + c2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hrun1, hrun2, rfl⟩),
      hresF, hv1, hv2, hZF, hlocF, hfrF, ?_⟩
    linarith only [hc1, hc2, htm_bd]

end MinCostFlow.ExpanderDecomp
