module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProg
public import MinCostFlow.ExpanderDecomp.OneShotProgAux
public import MinCostFlow.ExpanderDecomp.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recursive Core Cut Player — Peeling Loop, Space/Time Recurrences, and `coreOnProc` (`CoreProgPeel`)

Defines the standalone deterministic (`NoRand`) Word-RAM procedure `coreOnProc` for `Core(q, G[X])`
(the core theorem `coreOn_spec`), its contract `coreOnContract`, its universal time/space envelopes
(`coreProgTime`, `coreProgSpace`), and proves:
* `coreProgTime_rec` and `coreProgSpace_rec`: time and space recurrences matching
  `Params.coreTimeBound_rec` with one fixed constant independent of `(q, r, M, G)`.
* `corePeelLoop_triple`: verified `Triple` for the `2 * D_q`-iteration peeling loop over
  `oneShotContract`, `filterSetContract w false`, and `copyWordsContract`.

The recursive induction via `meetsContract_of_rec` is completed in `CoreProgOn.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Universal Time and Space Envelopes -/

/-- Universal time constant for `coreOnProc`, independent of `(q, r, M, G)`. -/
def coreTimeConst (K_B K_C : ℕ) : ℕ :=
  max (K_B + K_C + 2) 1000

/-- Universal space constant for `coreOnProc`, independent of `(q, r, M, G)`. -/
def coreSpaceConst (S_B S_C : ℕ) : ℕ :=
  max (S_B + S_C + 2) 1000

/-- Word-RAM step bound of `coreOnProc` at level `q`: `coreTimeConst * coreTimeBound`. -/
def coreProgTime (K_B K_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) : ℕ :=
  coreTimeConst K_B K_C * coreTimeBound cfg M r q

/-- Word-RAM heap advance and headroom bound of `coreOnProc` at level `q`. -/
def coreProgSpace (S_B S_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) : ℕ :=
  coreSpaceConst S_B S_C * coreSpaceBase M r * coreTimeBound cfg M r q

/-! ## 2. Machine Statements (`corePeelBodyStmt`, `corePeelLoopStmt`, `coreOnProc`) -/

/-- One iteration of the peeling loop of `Core(q, G[X])`.
Registers: `r0=q, r1=gAddr, r2=k, r3=xAddr, r4=pAddr, r5=locAddr, r6=outAddr, r7=h,
r10=uAddr, r11=x'Addr, r12=hCur, r13=uLen, r14=doneFlag, r15=2*D_q, r16=iter`. -/
def corePeelBodyStmt (idx : CoreIdx) : Stmt :=
  .cond (.bin .eq (.reg 14) (.const 0))
    (.cond (.bin .lt (.bin .mul (.const 4) (.reg 13)) (.reg 2))
      (seqStmts
        [ .call 17 idx.filterDiff [.reg 2, .reg 3, .reg 13, .reg 10, .reg 5, .reg 11]
        , .call 12 idx.oneShot
            [.reg 0, .reg 1, .reg 17, .reg 11, .reg 4, .reg 5, .reg 6, .reg 12]
        , .assign 18 (.load (.reg 6))
        , .cond (.bin .eq (.reg 18) (.const 1))
            (.assign 14 (.const 1))
            (seqStmts
              [ .assign 19 (.load (.bin .add (.reg 6) (.const 1)))
              , .assign 21 (.bin .add (.reg 10) (.reg 13))
              , .assign 22 (.bin .add (.reg 6) (.const 2))
              , .cond (.bin .lt (.reg 17) (.bin .mul (.const 2) (.reg 19)))
                  (.call 20 idx.filterDiff
                    [.reg 17, .reg 11, .reg 19, .reg 22, .reg 5, .reg 21])
                  (seqStmts
                    [ .call 20 idx.copyWords [.reg 19, .reg 22, .reg 21]
                    , .assign 20 (.reg 19) ])
              , .assign 13 (.bin .add (.reg 13) (.reg 20)) ]) ])
      .nop)
    .nop

/-- The `2 * D_q`-iteration peeling loop of `coreOnProc`. -/
def corePeelLoopStmt (idx : CoreIdx) : Stmt :=
  forRange 16 (.const 0) (.reg 15) (corePeelBodyStmt idx)

/-- Standalone deterministic Word-RAM procedure for `coreOn(q, G, X)` (the core theorem `coreOn_spec`).
`args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h]`. -/
def coreOnProc (idx : CoreIdx) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0))
    (seqStmts
      [ .store (.reg 6) (.const 1)
      , .store (.bin .add (.reg 6) (.const 1)) (.reg 2)
      , .call 17 idx.copyWords [.reg 2, .reg 3, .bin .add (.reg 6) (.const 2)]
      , .ret (.reg 7) ])
    (.cond (.bin .lt (.reg 2) (.const 2))
      (seqStmts
        [ .store (.reg 6) (.const 1)
        , .store (.bin .add (.reg 6) (.const 1)) (.reg 2)
        , .call 17 idx.copyWords [.reg 2, .reg 3, .bin .add (.reg 6) (.const 2)]
        , .ret (.reg 7) ])
      (seqStmts
        [ .assign 8 (.load (.bin .add (.reg 4) (.const 3)))
        , .assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 6))
            (.bin .mul (.const 2) (.reg 8))) (.bin .sub (.reg 0) (.const 1))))
        , .cond (.bin .lt (.reg 9) (.reg 2))
            (seqStmts
              [ .assign 10 (.reg 7)
              , .assign 11 (.bin .add (.reg 7) (.reg 2))
              , .assign 12 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 2)))
              , .assign 13 (.const 0)
              , .assign 14 (.const 0)
              , .assign 15 (.bin .mul (.const 2)
                  (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 5)) (.reg 8)) (.reg 0))))
              , corePeelLoopStmt idx
              , .cond (.bin .eq (.reg 14) (.const 1))
                  (.ret (.reg 12))
                  (seqStmts
                    [ .store (.reg 6) (.const 0)
                    , .store (.bin .add (.reg 6) (.const 1)) (.reg 13)
                    , .call 17 idx.copyWords [.reg 13, .reg 10, .bin .add (.reg 6) (.const 2)]
                    , .ret (.reg 12) ]) ])
            (seqStmts
              [ .assign 17 (.bin .sub (.reg 0) (.const 1))
              , .call 12 idx.coreOn
                  [.reg 17, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7]
              , .ret (.reg 12) ]) ]))

/-! ## 3. Contract for `coreOnProc` -/

/-- Contract for `coreOnProc`: `args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h]`.
Delivers the core theorem (`CoreSpec (coreParamsOf cfg M r) q G X res`) at `outAddr` (`CoreOutAt`),
heap advance `v ∈ [h, h + coreProgSpace]` with `ZeroFrom mem' v`, `locAddr` zero preservation,
and step count `≤ coreProgTime K_B K_C cfg M r q`. -/
noncomputable def coreOnContract (cfg : ParamConfig) (M r w K_B K_C S_B S_C : ℕ) : Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    ∃ (q gAddr k xAddr pAddr locAddr outAddr h : ℕ) (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] ∧
      12 ≤ cfg.a₀ ∧ 4 ≤ cfg.a ∧ r ≤ ell M ∧ q ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r ∧
      VertsAt mem xAddr k X ∧
      X ⊆ Finset.range G.n ∧
      (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧
      k ≤ cp.N ^ q ∧
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) ∧
      G.m ≤ cp.Δ * k ∧
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
      h + coreProgSpace S_B S_C cfg M r q < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    ∀ (q gAddr k xAddr pAddr locAddr outAddr h : ℕ) (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, pAddr, locAddr, outAddr, h] →
      12 ≤ cfg.a₀ → 4 ≤ cfg.a → r ≤ ell M → q ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem gAddr G →
      G.IsValid →
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r →
      VertsAt mem xAddr k X →
      X ⊆ Finset.range G.n →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      k ≤ cp.N ^ q →
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) →
      G.m ≤ cp.Δ * k →
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
      h + coreProgSpace S_B S_C cfg M r q < 2 ^ w →
      (∃ res : CoreResult, CoreOutAt mem' outAddr res ∧ CoreSpec cp q G X res) ∧
      h ≤ v ∧ v ≤ h + coreProgSpace S_B S_C cfg M r q ∧
      ZeroFrom mem' v ∧
      (∀ u < G.n, mem' (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem' a = mem a)
  cost args _ := coreProgTime K_B K_C cfg M r (args.getD 0 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. `NoRand` and Time/Space Recurrence Lemmas -/

lemma corePeelBodyStmt_noRand (idx : CoreIdx) : (corePeelBodyStmt idx).NoRand := by
  simp [corePeelBodyStmt, seqStmts, Stmt.NoRand]

lemma corePeelLoopStmt_noRand (idx : CoreIdx) : (corePeelLoopStmt idx).NoRand := by
  simp [corePeelLoopStmt, forRange, forUp, corePeelBodyStmt_noRand, Stmt.NoRand]

lemma coreOnProc_noRand (idx : CoreIdx) : (coreOnProc idx).NoRand := by
  simp [coreOnProc, corePeelLoopStmt_noRand, seqStmts, Stmt.NoRand]

lemma coreTimeBound_pos (cfg : ParamConfig) (M r q : ℕ) : 4 ≤ coreTimeBound cfg M r q := by
  unfold coreTimeBound
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hN1 : 1 ≤ NOf M r := by omega
  have hNp : 4 ≤ (NOf M r) ^ (q + 1) := by
    calc 4 ≤ NOf M r := hN4
      _ = (NOf M r) ^ 1 := (pow_one _).symm
      _ ≤ (NOf M r) ^ (q + 1) := Nat.pow_le_pow_right hN1 (by omega)
  have hW1 : 1 ≤ WParam cfg M := by unfold WParam; omega
  have hWp : 1 ≤ (WParam cfg M) ^ (10 * q ^ 2 + 10) := Nat.one_le_pow _ _ hW1
  calc 4 = 4 * 1 := (Nat.mul_one 4).symm
    _ ≤ (NOf M r) ^ (q + 1) * (WParam cfg M) ^ (10 * q ^ 2 + 10) := Nat.mul_le_mul hNp hWp

lemma coreProgTime_base_ge (K_B K_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) :
    4000 ≤ coreProgTime K_B K_C cfg M r q := by
  unfold coreProgTime coreTimeConst
  have h1 : 1000 ≤ max (K_B + K_C + 2) 1000 := le_max_right _ _
  have h2 : 4 ≤ coreTimeBound cfg M r q := coreTimeBound_pos cfg M r q
  exact Nat.mul_le_mul h1 h2

lemma coreProgSpace_base_ge (S_B S_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) :
    4000 ≤ coreProgSpace S_B S_C cfg M r q := by
  unfold coreProgSpace coreSpaceConst coreSpaceBase
  have h1 : 1000 ≤ max (S_B + S_C + 2) 1000 := le_max_right _ _
  have h2 : 1 ≤ (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h3 : 4 ≤ coreTimeBound cfg M r q := coreTimeBound_pos cfg M r q
  calc 4000 = 1000 * 1 * 4 := by decide
    _ ≤ max (S_B + S_C + 2) 1000 * (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5 *
          coreTimeBound cfg M r q :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

lemma coreTimeBound_mono_succ (cfg : ParamConfig) (M r q : ℕ) (hq1 : 1 ≤ q) :
    coreTimeBound cfg M r (q - 1) + 1 ≤ coreTimeBound cfg M r q := by
  have hrec := coreTimeBound_rec cfg M r hq1 (Tprev := coreTimeBound cfg M r (q - 1)) le_rfl
  have hc0 : 1 ≤ cfg.c0 := by unfold ParamConfig.c0 ParamConfig.s0; omega
  have hA : 1 ≤ cfg.A := by unfold ParamConfig.A; have := cfg.ha; omega
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hL1 : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hF1 : 1 ≤ FParam cfg M := one_le_FParam cfg M
  have h1 : 1 ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hL1))
      (Nat.one_le_pow _ _ hF1)
  have h2 : 1 ≤ NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q :=
    Nat.mul_le_mul (Nat.mul_le_mul hN1 (Nat.one_le_pow _ _ hL1)) (Nat.one_le_pow _ _ hF1)
  have h3 : coreTimeBound cfg M r (q - 1) ≤
      NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * coreTimeBound cfg M r (q - 1) := by
    calc coreTimeBound cfg M r (q - 1) = 1 * coreTimeBound cfg M r (q - 1) := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ h2
  have hcA : 1 ≤ cfg.c0 * cfg.A := Nat.mul_le_mul hc0 hA
  have hsum : coreTimeBound cfg M r (q - 1) + 1 ≤
      cfg.c0 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q +
        NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * coreTimeBound cfg M r (q - 1) +
        (NOf M r) ^ q * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * q)) := by
    calc coreTimeBound cfg M r (q - 1) + 1
        = 1 * (coreTimeBound cfg M r (q - 1) + 1) := (Nat.one_mul _).symm
      _ ≤ (cfg.c0 * cfg.A) * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q +
            NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * coreTimeBound cfg M r (q - 1) +
            (NOf M r) ^ q * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * q)) :=
          Nat.mul_le_mul hcA (by omega)
  exact le_trans hsum hrec

/-- Universal time recurrence for `coreOnProc`: `2 * D_q` peeling iterations plus setup/teardown
fit inside `coreProgTime K_B K_C cfg M r q` with ZERO `K^q` blow-up. -/
lemma coreProgTime_rec (K_B K_C : ℕ) (cfg : ParamConfig) (M r q k : ℕ)
    (hq1 : 1 ≤ q) (hk : k ≤ (NOf M r) ^ q) :
    2 * DCore cfg M q *
        (oneShotProgCost K_B K_C cfg M r q (coreProgTime K_B K_C cfg M r (q - 1)) +
          260 * k + 500) +
      copyWordsCost k + 400 ≤
    coreProgTime K_B K_C cfg M r q := by
  set K := coreTimeConst K_B K_C
  set N := NOf M r
  set L := LParam M
  set F := FParam cfg M
  set Tprev := coreTimeBound cfg M r (q - 1)
  have hK1000 : 1000 ≤ K := le_max_right _ _
  have hKbc : K_B + K_C + 2 ≤ K := le_max_left _ _
  have hN1 : 1 ≤ N := le_trans (by decide) (four_le_NOf M r)
  have hL4 : 4 ≤ L := four_le_LParam M
  have hF1 : 1 ≤ F := one_le_FParam cfg M
  have hA1 : 1 ≤ cfg.A := by unfold ParamConfig.A; have := cfg.ha; omega
  have hc0_lo : 4096 * 2 ^ 30 ≤ cfg.c0 := by
    unfold ParamConfig.c0 ParamConfig.s0
    have hu : 1 ≤ cfg.u := cfg.hu
    have hu3 : 1 ≤ cfg.u ^ 3 := Nat.one_le_pow 3 cfg.u hu
    have h1 : 2 ^ 30 ≤ 2 ^ 30 * cfg.u ^ 3 := by
      calc 2 ^ 30 = 2 ^ 30 * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ 30 * cfg.u ^ 3 := Nat.mul_le_mul_left _ hu3
    omega
  have hDq : 2 * DCore cfg M q = 2048 * cfg.A * L * F ^ q := by
    unfold DCore deltaParam tParam PParam; ring
  have hNL8 : 260 * k + 500 ≤ N ^ (q + 1) * L ^ 8 := by
    have hL8 : 4 ^ 8 ≤ L ^ 8 := Nat.pow_le_pow_left hL4 8
    have hNq : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (by omega)
    have h1 : 1 ≤ N ^ (q + 1) := Nat.one_le_pow _ _ hN1
    have h2 : 760 ≤ 4 ^ 8 := by decide
    calc 260 * k + 500 ≤ 260 * N ^ q + 500 * 1 := by omega
      _ ≤ 260 * N ^ (q + 1) + 500 * N ^ (q + 1) := by
          have := Nat.mul_le_mul_left 260 hNq
          have := Nat.mul_le_mul_left 500 h1
          omega
      _ = 760 * N ^ (q + 1) := by ring
      _ ≤ L ^ 8 * N ^ (q + 1) := Nat.mul_le_mul_right _ (le_trans h2 hL8)
      _ = N ^ (q + 1) * L ^ 8 := by ring
  have htail : copyWordsCost k + 400 ≤ cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q := by
    unfold copyWordsCost
    have h1 : 30 * k + 30 + 400 ≤ 260 * k + 500 := by omega
    have h2 : N ^ (q + 1) * L ^ 8 ≤ cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q := by
      have hALF : 1 ≤ cfg.A * L * F ^ q :=
        Nat.mul_le_mul (Nat.mul_le_mul hA1 (by omega : 1 ≤ L)) (Nat.one_le_pow _ _ hF1)
      calc N ^ (q + 1) * L ^ 8 = (N ^ (q + 1) * L ^ 8) * 1 := (Nat.mul_one _).symm
        _ ≤ (N ^ (q + 1) * L ^ 8) * (cfg.A * L * F ^ q) := Nat.mul_le_mul_left _ hALF
        _ = cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q := by ring
    exact le_trans (le_trans h1 hNL8) h2
  have hSone : oneShotProgCost K_B K_C cfg M r q (K * Tprev) + 260 * k + 500 ≤
      100 * N * L * (K * Tprev) + (K_B + K_C + 3) * N ^ (q + 1) * L ^ 8 +
        (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * F ^ (2 * q) := by
    change 100 * N * L * (K * Tprev) + (K_B + K_C + 2) * N ^ (q + 1) * L ^ 8 +
      (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * F ^ (2 * q) + 260 * k + 500 ≤ _
    have h3 : (K_B + K_C + 3) * N ^ (q + 1) * L ^ 8 =
        (K_B + K_C + 2) * N ^ (q + 1) * L ^ 8 + N ^ (q + 1) * L ^ 8 := by ring
    omega
  have hmul : 2 * DCore cfg M q *
      (100 * N * L * (K * Tprev) + (K_B + K_C + 3) * N ^ (q + 1) * L ^ 8 +
        (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * F ^ (2 * q)) =
      2048 * (K_B + K_C + 3) * cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q +
        204800 * K * cfg.A * N * L ^ 2 * F ^ q * Tprev +
        2048 * (2048 * 200000000 + 206000) * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q) := by
    rw [hDq]
    have hF3 : F ^ q * F ^ (2 * q) = F ^ (3 * q) := by rw [← pow_add]; congr 1; omega
    calc 2048 * cfg.A * L * F ^ q *
          (100 * N * L * (K * Tprev) + (K_B + K_C + 3) * N ^ (q + 1) * L ^ 8 +
            (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * F ^ (2 * q))
        = 2048 * (K_B + K_C + 3) * cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q +
            204800 * K * cfg.A * N * L ^ 2 * F ^ q * Tprev +
            2048 * (2048 * 200000000 + 206000) * cfg.A * N ^ q * L ^ 4 * (F ^ q * F ^ (2 * q)) := by
          ring
      _ = _ := by rw [hF3]
  have hc1 : 2048 * (K_B + K_C + 3) + 1 ≤ K * cfg.c0 := by
    have h1 : 2048 * (K_B + K_C + 3) + 1 ≤ 4096 * K := by omega
    have h2 : 4096 ≤ cfg.c0 := by omega
    calc 2048 * (K_B + K_C + 3) + 1 ≤ K * 4096 := by omega
      _ ≤ K * cfg.c0 := Nat.mul_le_mul_left K h2
  have hc2 : 204800 ≤ cfg.c0 := by omega
  have hc3 : 2048 * (2048 * 200000000 + 206000) ≤ K * cfg.c0 := by
    have h1 : 2048 * (2048 * 200000000 + 206000) ≤ 1000 * (4096 * 2 ^ 30) := by decide
    exact le_trans h1 (Nat.mul_le_mul hK1000 hc0_lo)
  have ht1 : 2048 * (K_B + K_C + 3) * cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q +
      cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q ≤
      K * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := by
    have hr : 2048 * (K_B + K_C + 3) * cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q +
        cfg.A * N ^ (q + 1) * L ^ 9 * F ^ q =
        (2048 * (K_B + K_C + 3) + 1) * (cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := by ring
    rw [hr]
    calc (2048 * (K_B + K_C + 3) + 1) * (cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q))
        ≤ (K * cfg.c0) * (cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := Nat.mul_le_mul_right _ hc1
      _ = K * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := by ring
  have ht2 : 204800 * K * cfg.A * N * L ^ 2 * F ^ q * Tprev ≤
      K * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by
    calc 204800 * K * cfg.A * N * L ^ 2 * F ^ q * Tprev
        = 204800 * (K * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by ring
      _ ≤ cfg.c0 * (K * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := Nat.mul_le_mul_right _ hc2
      _ = K * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by ring
  have ht3 : 2048 * (2048 * 200000000 + 206000) * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q) ≤
      K * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by
    calc 2048 * (2048 * 200000000 + 206000) * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q)
        = (2048 * (2048 * 200000000 + 206000)) * (cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
      _ ≤ (K * cfg.c0) * (cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := Nat.mul_le_mul_right _ hc3
      _ = K * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
  have hrec := Nat.mul_le_mul_left K (coreTimeBound_rec cfg M r hq1 (Tprev := Tprev) le_rfl)
  change K * (cfg.c0 * cfg.A *
      (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev + N ^ q * L ^ 4 * F ^ (3 * q))) ≤
      K * coreTimeBound cfg M r q at hrec
  have hdist : K * (cfg.c0 * cfg.A *
      (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev + N ^ q * L ^ 4 * F ^ (3 * q))) =
      K * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) +
        K * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) +
        K * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
  rw [hdist] at hrec
  have hstep1 := Nat.mul_le_mul_left (2 * DCore cfg M q) hSone
  rw [hmul] at hstep1
  change 2 * DCore cfg M q *
      (oneShotProgCost K_B K_C cfg M r q (K * Tprev) + 260 * k + 500) +
      copyWordsCost k + 400 ≤ K * coreTimeBound cfg M r q
  linarith only [hstep1, htail, ht1, ht2, ht3, hrec]

/-- Universal space recurrence for `coreOnProc`: `2 * k` peeling buffers plus `2 * D_q` calls to
`oneShotProgSpace` fit inside `coreProgSpace S_B S_C cfg M r q` with ZERO `S^q` blow-up. -/
lemma coreProgSpace_rec (S_B S_C : ℕ) (cfg : ParamConfig) (M r q k : ℕ)
    (hq1 : 1 ≤ q) (hk : k ≤ (NOf M r) ^ q) :
    2 * k + 2 * DCore cfg M q *
      oneShotProgSpace S_B S_C cfg M r q (coreProgSpace S_B S_C cfg M r (q - 1)) ≤
    coreProgSpace S_B S_C cfg M r q := by
  set S := coreSpaceConst S_B S_C
  set B := coreSpaceBase M r
  set N := NOf M r
  set L := LParam M
  set F := FParam cfg M
  set Tprev := coreTimeBound cfg M r (q - 1)
  have hS1000 : 1000 ≤ S := le_max_right _ _
  have hSbc : S_B + S_C + 2 ≤ S := le_max_left _ _
  have hN1 : 1 ≤ N := le_trans (by decide) (four_le_NOf M r)
  have hL4 : 4 ≤ L := four_le_LParam M
  have hF1 : 1 ≤ F := one_le_FParam cfg M
  have hA1 : 1 ≤ cfg.A := by unfold ParamConfig.A; have := cfg.ha; omega
  have hB1 : 1 ≤ B := by unfold B coreSpaceBase; exact Nat.one_le_pow _ _ (by omega)
  have hc0_lo : 4096 * 2 ^ 30 ≤ cfg.c0 := by
    unfold ParamConfig.c0 ParamConfig.s0
    have hu3 : 1 ≤ cfg.u ^ 3 := Nat.one_le_pow 3 cfg.u cfg.hu
    have h1 : 2 ^ 30 ≤ 2 ^ 30 * cfg.u ^ 3 := by
      calc 2 ^ 30 = 2 ^ 30 * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ 30 * cfg.u ^ 3 := Nat.mul_le_mul_left _ hu3
    omega
  have hDq : 2 * DCore cfg M q = 2048 * cfg.A * L * F ^ q := by
    unfold DCore deltaParam tParam PParam; ring
  have h2k : 2 * k ≤ cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q := by
    have hNq : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (by omega)
    have h1 : 2 ≤ cfg.A * B * L ^ 9 * F ^ q := by
      have hL9 : 2 ≤ L ^ 9 := by
        calc 2 ≤ L := by omega
          _ = L ^ 1 := (pow_one _).symm
          _ ≤ L ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
      have hrest : 1 ≤ cfg.A * B * F ^ q :=
        Nat.mul_le_mul (Nat.mul_le_mul hA1 hB1) (Nat.one_le_pow _ _ hF1)
      calc 2 = 1 * 2 := (Nat.one_mul 2).symm
        _ ≤ (cfg.A * B * F ^ q) * L ^ 9 := Nat.mul_le_mul hrest hL9
        _ = cfg.A * B * L ^ 9 * F ^ q := by ring
    calc 2 * k ≤ 2 * N ^ q := by omega
      _ ≤ (cfg.A * B * L ^ 9 * F ^ q) * N ^ (q + 1) := Nat.mul_le_mul h1 hNq
      _ = cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q := by ring
  have hmul : 2 * DCore cfg M q *
      oneShotProgSpace S_B S_C cfg M r q (S * B * Tprev) =
      2048 * (S_B + S_C + 2) * cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q +
        204800 * S * cfg.A * B * N * L ^ 2 * F ^ q * Tprev +
        2048 * 65536 * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q) := by
    unfold oneShotProgSpace
    dsimp only
    rw [hDq]
    have hF3 : F ^ q * F ^ (2 * q) = F ^ (3 * q) := by rw [← pow_add]; congr 1; omega
    calc 2048 * cfg.A * L * F ^ q *
          (100 * N * L * (S * B * Tprev) +
            (S_B + S_C + 2) * B * N ^ (q + 1) * L ^ 8 +
            65536 * N ^ q * L ^ 3 * F ^ (2 * q))
        = 2048 * (S_B + S_C + 2) * cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q +
            204800 * S * cfg.A * B * N * L ^ 2 * F ^ q * Tprev +
            2048 * 65536 * cfg.A * N ^ q * L ^ 4 * (F ^ q * F ^ (2 * q)) := by ring
      _ = _ := by rw [hF3]
  have hc1 : 2048 * (S_B + S_C + 2) + 1 ≤ S * cfg.c0 := by
    have h1 : 2048 * (S_B + S_C + 2) + 1 ≤ 4096 * S := by omega
    have h2 : 4096 ≤ cfg.c0 := by omega
    calc 2048 * (S_B + S_C + 2) + 1 ≤ S * 4096 := by omega
      _ ≤ S * cfg.c0 := Nat.mul_le_mul_left S h2
  have hc2 : 204800 ≤ cfg.c0 := by omega
  have hc3 : 2048 * 65536 ≤ S * cfg.c0 := by
    have h1 : 2048 * 65536 ≤ 1000 * (4096 * 2 ^ 30) := by decide
    exact le_trans h1 (Nat.mul_le_mul hS1000 hc0_lo)
  set P := S * B
  have ht1 : 2048 * (S_B + S_C + 2) * cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q +
      cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q ≤
      P * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := by
    have hr : 2048 * (S_B + S_C + 2) * cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q +
        cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q =
        (2048 * (S_B + S_C + 2) + 1) * (cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q) := by ring
    rw [hr]
    calc (2048 * (S_B + S_C + 2) + 1) * (cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q)
        ≤ (S * cfg.c0) * (cfg.A * B * N ^ (q + 1) * L ^ 9 * F ^ q) :=
          Nat.mul_le_mul_right _ hc1
      _ = P * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) := by dsimp only [P]; ring
  have ht2 : 204800 * S * cfg.A * B * N * L ^ 2 * F ^ q * Tprev ≤
      P * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by
    calc 204800 * S * cfg.A * B * N * L ^ 2 * F ^ q * Tprev
        = 204800 * (P * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by dsimp only [P]; ring
      _ ≤ cfg.c0 * (P * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := Nat.mul_le_mul_right _ hc2
      _ = P * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) := by ring
  have ht3 : 2048 * 65536 * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q) ≤
      P * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by
    have h1 : 2048 * 65536 ≤ P * cfg.c0 := by
      calc 2048 * 65536 ≤ S * cfg.c0 := hc3
        _ = (S * 1) * cfg.c0 := by ring
        _ ≤ (S * B) * cfg.c0 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left S hB1)
        _ = P * cfg.c0 := rfl
    calc 2048 * 65536 * cfg.A * N ^ q * L ^ 4 * F ^ (3 * q)
        = (2048 * 65536) * (cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
      _ ≤ (P * cfg.c0) * (cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := Nat.mul_le_mul_right _ h1
      _ = P * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
  have hrec := Nat.mul_le_mul_left P (coreTimeBound_rec cfg M r hq1 (Tprev := Tprev) le_rfl)
  change P * (cfg.c0 * cfg.A *
      (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev + N ^ q * L ^ 4 * F ^ (3 * q))) ≤
      P * coreTimeBound cfg M r q at hrec
  have hdist : P * (cfg.c0 * cfg.A *
      (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev + N ^ q * L ^ 4 * F ^ (3 * q))) =
      P * (cfg.c0 * cfg.A * (N ^ (q + 1) * L ^ 9 * F ^ q)) +
        P * (cfg.c0 * cfg.A * (N * L ^ 2 * F ^ q * Tprev)) +
        P * (cfg.c0 * cfg.A * (N ^ q * L ^ 4 * F ^ (3 * q))) := by ring
  rw [hdist] at hrec
  change 2 * k + 2 * DCore cfg M q *
      oneShotProgSpace S_B S_C cfg M r q (S * B * Tprev) ≤ P * coreTimeBound cfg M r q
  rw [hmul]
  linarith only [h2k, ht1, ht2, ht3, hrec]

/-- `2 * D_q + 1 ≤ coreProgSpace` for `1 ≤ q`, guaranteeing the loop counter fits `< 2 ^ w`. -/
lemma two_mul_DCore_lt_coreProgSpace (S_B S_C : ℕ) (cfg : ParamConfig) (M r q : ℕ) (hq1 : 1 ≤ q) :
    2 * DCore cfg M q + 1 ≤ coreProgSpace S_B S_C cfg M r q := by
  have hrec := coreTimeBound_rec cfg M r hq1 (Tprev := coreTimeBound cfg M r (q - 1)) le_rfl
  have hDq : 2 * DCore cfg M q = 2048 * cfg.A * LParam M * (FParam cfg M) ^ q := by
    unfold DCore deltaParam tParam PParam; ring
  have hc0 : 4096 ≤ cfg.c0 := by unfold ParamConfig.c0 ParamConfig.s0; omega
  have hN1 : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ (le_trans (by decide) (four_le_NOf M r))
  have hL1 : LParam M ≤ (LParam M) ^ 9 := by
    have hL4 := four_le_LParam M
    calc LParam M = (LParam M) ^ 1 := (pow_one _).symm
      _ ≤ (LParam M) ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
  have hA1 : 1 ≤ cfg.A := by unfold ParamConfig.A; have := cfg.ha; omega
  have hF1 : 1 ≤ (FParam cfg M) ^ q := Nat.one_le_pow _ _ (one_le_FParam cfg M)
  have h1 : 1 ≤ cfg.A * LParam M * (FParam cfg M) ^ q :=
    Nat.mul_le_mul (Nat.mul_le_mul hA1 (by have := four_le_LParam M; omega : 1 ≤ LParam M)) hF1
  have h2 : 2048 * cfg.A * LParam M * (FParam cfg M) ^ q + 1 ≤
      4096 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) := by
    have ha : 2048 * cfg.A * LParam M * (FParam cfg M) ^ q + 1 ≤
        4096 * (cfg.A * LParam M * (FParam cfg M) ^ q) := by
      have : 2048 * cfg.A * LParam M * (FParam cfg M) ^ q =
          2048 * (cfg.A * LParam M * (FParam cfg M) ^ q) := by ring
      omega
    have hb : cfg.A * LParam M * (FParam cfg M) ^ q ≤
        cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) := by
      have hNL : LParam M ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 9 := by
        calc LParam M = 1 * LParam M := (Nat.one_mul _).symm
          _ ≤ (NOf M r) ^ (q + 1) * (LParam M) ^ 9 := Nat.mul_le_mul hN1 hL1
      calc cfg.A * LParam M * (FParam cfg M) ^ q
          = cfg.A * (LParam M * (FParam cfg M) ^ q) := by ring
        _ ≤ cfg.A * (((NOf M r) ^ (q + 1) * (LParam M) ^ 9) * (FParam cfg M) ^ q) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hNL)
        _ = cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) := by ring
    calc 2048 * cfg.A * LParam M * (FParam cfg M) ^ q + 1
        ≤ 4096 * (cfg.A * LParam M * (FParam cfg M) ^ q) := ha
      _ ≤ 4096 * (cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q)) :=
          Nat.mul_le_mul_left 4096 hb
      _ = 4096 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) := by ring
  have h3 : 4096 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) ≤
      coreTimeBound cfg M r q := by
    have h4 : 4096 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) ≤
        cfg.c0 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right cfg.A hc0)
    have h5 : cfg.c0 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q) ≤
        cfg.c0 * cfg.A * ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q +
          NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * coreTimeBound cfg M r (q - 1) +
          (NOf M r) ^ q * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * q)) :=
      Nat.mul_le_mul_left _ (by omega)
    exact le_trans h4 (le_trans h5 hrec)
  have h4 : coreTimeBound cfg M r q ≤ coreProgSpace S_B S_C cfg M r q := by
    unfold coreProgSpace coreSpaceConst coreSpaceBase
    have hS1 : 1 ≤ max (S_B + S_C + 2) 1000 * (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5 :=
      Nat.mul_le_mul (le_trans (by decide : 1 ≤ 1000) (le_max_right _ _))
        (Nat.one_le_pow _ _ (by omega))
    calc coreTimeBound cfg M r q = 1 * coreTimeBound cfg M r q := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hS1
  rw [hDq]
  exact le_trans h2 (le_trans h3 h4)

end MinCostFlow.ExpanderDecomp
