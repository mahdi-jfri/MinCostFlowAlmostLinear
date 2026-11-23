module

public import MinCostFlow.HierPaths.BuildTopRecurse
public import MinCostFlow.HierPaths.BuildTopPackAll
public import MinCostFlow.HierPaths.InitEntry
public import MinCostFlow.HierPaths.BuildTopPlayerWords
import MinCostFlow.HierPaths.InitProgNumbers

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Top-level static hierarchy builder and `StaticProcSpec`

Assembles the full static construction `buildTopStaticProc PL : HierProc` from:
1. Root size and branch-exponent computation (`buildTopSize`, `buildTopBranchProc`),
2. Zero-heap compact padded root and schedule preparation (`buildTopPrepare` +
   `buildTopRootCompactModule` + `buildTopPlayerSetup` + `buildTopScheduleRun`),
3. Depth recursion (`buildTopDriver` + `buildTopAdvance` calling `PL`),
4. Full 6-section assembly and final packing (`buildTopPackAll` + `buildTopFinish`).

Proves `buildTopStatic_spec`: for any level procedure `PL` meeting `ProvidesBuildLevel`
with polynomial space bound `BuildLevelSpacePoly space Cs cs`, `buildTopStaticProc PL`
meets `StaticProcSpec` for every `a ≥ buildTopMinA`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp MinCostFlow.LowStretch
open scoped BigOperators

/-! ### Branch-exponent helper procedure -/

/-- Compute `buildTopBranch x m = min x (branchBits m)` from `[x, m]`. -/
def buildTopBranchProc : Stmt :=
  .assign 20 (.bin .add (.bin .mul (.const 8) (.reg 1)) (.const 8)) ;;
  clogBlock ;;
  .assign 2 (.reg 21) ;;
  .assign 20 (.reg 2) ;;
  cbrtBlock ;;
  .assign 3 (buildTopBranchBitsExpr (.reg 2) (.reg 21)) ;;
  .cond (.bin .lt (.reg 0) (.reg 3)) (.ret (.reg 0)) (.ret (.reg 3))

theorem buildTopBranchProc_noRand : buildTopBranchProc.NoRand := by
  simp [buildTopBranchProc, clogBlock_noRand, cbrtBlock_noRand, Stmt.NoRand]

def buildTopBranchProcContract (w x m : ℕ) : Contract where
  pre args _ := args = [x, m] ∧ 8 * m + 8 < 2 ^ w ∧ depthOf m ^ 3 < 2 ^ w ∧
    xOf m + depthOf m < 2 ^ w ∧ x < 2 ^ w
  post _ mem v mem' := v = buildTopBranch x m ∧ mem' = mem
  cost _ _ := 13 * (Nat.log 2 (8 * m + 7) + 1) + 19 * depthOf m + 120

theorem buildTopBranchProc_meetsContract {w f x m : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopBranchProc) :
    MeetsContract w p f (buildTopBranchProcContract w x m) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hm, hpow, hsum, hxw⟩ := hpre
  have h8 : 8 < 2 ^ w := by omega
  have h4 : 4 ≤ 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hs : xOf m < 2 ^ w := by
    unfold xOf
    apply lt_of_le_of_lt _ hm
    rw [Nat.clog_le_iff_le_pow (by decide)]
    exact Nat.lt_two_pow_self.le
  have hpos : 1 ≤ xOf m := by
    unfold xOf
    apply Nat.succ_le_of_lt
    rw [Nat.lt_clog_iff_pow_lt (by decide)]
    simp only [pow_zero]; omega
  refine runs_start_le ?_
  unfold buildTopBranchProc
  refine runs_seq_assign_le (v := 8 * m + 8)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const h8) (Expr.eval_reg_of_eq (v := m) rfl)
      (by omega)) (Expr.eval_const h8) hm) ?_
  refine runs_seq_triple_le (clogBlock_triple (by omega) hm h4 _ rfl) rfl ?_
  intro st1 ⟨hr1, hmem1, _, hpres1⟩
  have hr1_0 : st1.regs 0 = x := by
    have := hpres1 0 (by decide) (by decide) (by decide)
    simpa [startState] using this
  refine runs_seq_assign_le (v := xOf m) (Expr.eval_reg_of_eq hr1) ?_
  refine runs_seq_assign_le (v := xOf m) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_triple_le (cbrtBlock_triple hpos hs hpow h4 _ rfl) rfl ?_
  intro st2 ⟨hr2, hmem2, _, hpres2⟩
  have hr2_0 : st2.regs 0 = x := by
    have := hpres2 0 (by decide) (by decide) (by decide) (by decide)
    simpa [hr1_0] using this
  have hr2_2 : st2.regs 2 = xOf m := by
    have := hpres2 2 (by decide) (by decide) (by decide) (by decide)
    simpa using this
  refine runs_seq_assign_le (v := branchBits m)
    (eval_buildTopBranchBitsExpr (Expr.eval_reg_of_eq hr2_2) (Expr.eval_reg_of_eq hr2) hsum) ?_
  have hmem_eq : st2.mem = mem := hmem2.trans hmem1
  have hlog_eq : 8 * m + 8 - 1 = 8 * m + 7 := by omega
  by_cases hlt : x < branchBits m
  · refine runs_cond_le (v := 1)
      (by simp [Expr.eval, BinOp.eval, hr2_0, hlt, h1])
      (fun _ => ?_) (fun h => absurd h one_ne_zero)
    refine runs_ret_le (v := x) (Expr.eval_reg_of_eq (by simp [hr2_0]))
      ⟨by simp [Outcome.value, buildTopBranch, min_eq_left hlt.le], hmem_eq⟩ ?_
    simp only [buildTopBranchProcContract, buildTopBranchBitsExpr, Expr.size, depthOf, hlog_eq]
    omega
  · refine runs_cond_le (v := 0)
      (by simp [Expr.eval, BinOp.eval, hr2_0, hlt])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_ret_le (v := branchBits m) (Expr.eval_reg_of_eq (by simp))
      ⟨by simp [Outcome.value, buildTopBranch, min_eq_right (Nat.le_of_not_gt hlt)], hmem_eq⟩ ?_
    simp only [buildTopBranchProcContract, buildTopBranchBitsExpr, Expr.size, depthOf, hlog_eq]
    omega

/-! ### Top-level entry and `HierProc` assembly -/

/-- Initial parameter computation: read `n, m`, compute `x, P, b, 2^b, D, ownersAddr, rootGraph`
into registers `5..13`. -/
def buildTopStaticSetup (sizeProc branchProc : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 7 sizeProc [.reg 6] ;;
  .assign 8 (.bin .shiftLeft (.const 1) (.reg 7)) ;;
  .call 9 branchProc [.reg 7, .reg 6] ;;
  .assign 10 (.bin .shiftLeft (.const 1) (.reg 9)) ;;
  .assign 11 (.bin .div (.bin .sub (.bin .add (.reg 7) (.reg 9)) (.const 1)) (.reg 9)) ;;
  .assign 12 (.bin .add (.bin .add (.reg 4) (.reg 5)) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 4) (.reg 6)))

theorem buildTopStaticSetup_noRand (sizeProc branchProc : ℕ) :
    (buildTopStaticSetup sizeProc branchProc).NoRand := by
  simp [buildTopStaticSetup, Stmt.NoRand]

/-- Entry body of the static hierarchy builder.
Arguments: `[gAddr, phiNum, phiDen, M, h]`. -/
def buildTopStaticEntry (sizeProc branchProc prepProc driverProc packProc : ℕ) : Stmt :=
  buildTopStaticSetup sizeProc branchProc ;;
  .call 14 prepProc [.reg 0, .reg 4, .reg 8, .reg 13, .reg 11, .reg 7, .reg 9, .reg 6, .reg 1, .reg 2] ;;
  .assign 15 (.bin .add (.bin .add (.reg 14) (.reg 8)) (.const 1)) ;;
  .assign 16 (.bin .add (buildTopRepliesExpr (.reg 15) (.reg 11) (.reg 7) (.reg 11))
    (.bin .mul (.const 7) (.reg 11))) ;;
  .call 17 driverProc [.reg 15, .reg 11, .reg 16] ;;
  .call 18 packProc [.reg 15, .reg 11, .reg 8, .reg 10, .reg 7, .reg 9, .reg 13, .reg 12,
    .reg 6, .reg 17, .reg 4] ;;
  .ret (.reg 18)

theorem buildTopStaticEntry_noRand (sizeProc branchProc prepProc driverProc packProc : ℕ) :
    (buildTopStaticEntry sizeProc branchProc prepProc driverProc packProc).NoRand := by
  simp [buildTopStaticEntry, buildTopStaticSetup_noRand, Stmt.NoRand]

/-- Fixed 50-procedure helper prefix (offsets `k + 0 .. k + 49`), followed by `PL` at `k + 50`. -/
def buildTopStaticFixedHelpers (k : ℕ) : List Stmt :=
  [ buildTopSize,                                              -- k + 0
    buildTopBranchProc,                                        -- k + 1
    buildTopPrepare (k + 3) (k + 16) (k + 22),                 -- k + 2
    buildTopRootSeeded (k + 4) (k + 5),                        -- k + 3
    buildTopRootLayout (k + 7),                                -- k + 4
    buildTopSeedDepth (k + 13) (k + 6),                        -- k + 5
    buildTopSeedRoot ] ++                                      -- k + 6
  buildTopRootCompactHelpers (k + 7) ++                        -- k + 7 .. k + 15 (9 procs)
  [ buildTopPlayerSetup (k + 17) (k + 18) (k + 20),            -- k + 16
    buildTopPlayerRank,                                        -- k + 17
    buildTopPlayerScale (k + 19),                              -- k + 18
    buildTopPlayerPower,                                       -- k + 19
    buildTopPlayerTableLoop (k + 21),                          -- k + 20
    buildTopPlayerTableRow,                                    -- k + 21
    buildTopScheduleRun (k + 23),                              -- k + 22
    buildTopScheduleRow (k + 24) (k + 25) (k + 26),            -- k + 23
    buildTopSchedulePlayers,                                   -- k + 24
    buildTopScheduleGeometry,                                  -- k + 25
    buildTopScheduleAddresses,                                 -- k + 26
    buildTopDriver (k + 28),                                   -- k + 27
    buildTopAdvance (k + 29) (k + 31),                         -- k + 28
    buildTopDepth (k + 30),                                    -- k + 29
    buildTopParentCall (k + 50),                               -- k + 30
    buildTopNextDir (k + 32),                                  -- k + 31
    buildTopNextRow (k + 33),                                  -- k + 32
    buildTopReplyRead (k + 34),                                -- k + 33
    initCSRSeek,                                               -- k + 34
    buildTopPackAll (k + 36) (k + 37) (k + 39) (k + 41) (k + 43) (k + 45), -- k + 35
    buildTopNumConn,                                           -- k + 36
    buildTopLabels (k + 13) (k + 38),                          -- k + 37
    initFillWord,                                              -- k + 38
    buildTopSec3 (k + 40) (k + 46),                            -- k + 39
    buildTopSec3Dir (k + 48),                                  -- k + 40
    buildTopSec4 (k + 42) (k + 46),                            -- k + 41
    buildTopSec4Dir (k + 48),                                  -- k + 42
    buildTopSec5 (k + 44) (k + 46),                            -- k + 43
    buildTopSec5Dir (k + 48),                                  -- k + 44
    buildTopFinish (k + 46) (k + 49),                          -- k + 45
    initCSRWrite (k + 47),                                     -- k + 46
    buildTopRow (k + 11),                                      -- k + 47
    buildTopReplySpan (k + 33),                                -- k + 48
    copyDown ]                                                 -- k + 49

theorem buildTopStaticFixedHelpers_length (k : ℕ) :
    (buildTopStaticFixedHelpers k).length = 50 := by
  simp [buildTopStaticFixedHelpers, buildTopRootCompactHelpers]

/-- Complete static builder `HierProc`, parameterized by a level procedure `PL`. -/
def buildTopStaticProc (PL : HierProc) : HierProc where
  entry k := buildTopStaticEntry k (k + 1) (k + 2) (k + 27) (k + 35)
  helpers k := buildTopStaticFixedHelpers k ++ [PL.entry (k + 51)] ++ PL.helpers (k + 51)

theorem buildTopStaticProc_noRand {PL : HierProc} (hPL : PL.NoRand) :
    (buildTopStaticProc PL).NoRand := by
  intro k
  refine ⟨buildTopStaticEntry_noRand _ _ _ _ _, ?_⟩
  intro s hs
  simp only [buildTopStaticProc, buildTopStaticFixedHelpers, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with (((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hsRoot) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl)) | rfl) | hsPL)
  · exact buildTopSize_noRand
  · exact buildTopBranchProc_noRand
  · exact buildTopPrepare_noRand _ _ _
  · exact buildTopRootSeeded_noRand _ _
  · exact buildTopRootLayout_noRand _
  · exact buildTopSeedDepth_noRand _ _
  · exact buildTopSeedRoot_noRand
  · exact (buildTopRootCompactModule_noRand (k + 7)).2 s hsRoot
  · exact buildTopPlayerSetup_noRand _ _ _
  · exact buildTopPlayerRank_noRand
  · exact buildTopPlayerScale_noRand _
  · exact buildTopPlayerPower_noRand
  · exact buildTopPlayerTableLoop_noRand _
  · exact buildTopPlayerTableRow_noRand
  · exact buildTopScheduleRun_noRand _
  · exact buildTopScheduleRow_noRand _ _ _
  · exact buildTopSchedulePlayers_noRand
  · exact buildTopScheduleGeometry_noRand
  · exact buildTopScheduleAddresses_noRand
  · exact buildTopDriver_noRand _
  · exact buildTopAdvance_noRand _ _
  · exact buildTopDepth_noRand _
  · exact buildTopParentCall_noRand _
  · exact buildTopNextDir_noRand _
  · exact buildTopNextRow_noRand _
  · exact buildTopReplyRead_noRand _
  · exact initCSRSeek_noRand
  · exact buildTopPackAll_noRand _ _ _ _ _ _
  · exact buildTopNumConn_noRand
  · exact buildTopLabels_noRand _ _
  · exact initFillWord_noRand
  · exact buildTopSec3_noRand _ _
  · exact buildTopSec3Dir_noRand _
  · exact buildTopSec4_noRand _ _
  · exact buildTopSec4Dir_noRand _
  · exact buildTopSec5_noRand _ _
  · exact buildTopSec5Dir_noRand _
  · exact buildTopFinish_noRand _ _
  · exact initCSRWrite_noRand _
  · exact buildTopRow_noRand _
  · exact buildTopReplySpan_noRand _
  · exact copyDown_noRand
  · exact (hPL (k + 51)).1
  · exact (hPL (k + 51)).2 s hsPL

/-! ### Space function, `SpaceForm`, and numerical envelopes -/

/-- Space function for `buildTopStaticProc`, parameterized by the level cost constant `K`
and polynomial space envelope `(Cs, cs)`. -/
def buildTopStaticSpace (K Cs cs a phiNum phiDen n m M : ℕ) : ℕ :=
  let d := (phiDen + phiNum - 1) / phiNum
  let Γ := gammaHP a d M
  let B := phiDen + n + m + M + Γ + 2
  (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 + 5 * B ^ 2 * (Cs * (2000 * B ^ 2) ^ cs)

lemma dOf_eq_ceil_div {phiNum phiDen : ℕ} (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) :
    dOf phiNum phiDen = (phiDen + phiNum - 1) / phiNum := by
  rw [dOf_eq_div_pred phiNum phiDen (by omega) (by omega)]
  have h : phiDen + phiNum - 1 = (phiDen - 1) + phiNum := by omega
  rw [h, Nat.add_div_right _ (by omega)]

theorem buildTopStaticSpace_spaceForm (K Cs cs a : ℕ) :
    SpaceForm a (buildTopStaticSpace K Cs cs a)
      ((50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs) (max 4 (2 * cs + 2)) := by
  intro phiNum phiDen n m M _ _
  set B := phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2
  change (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 + 5 * B ^ 2 * (Cs * (2000 * B ^ 2) ^ cs) ≤
    ((50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs) * B ^ max 4 (2 * cs + 2)
  have hB1 : 1 ≤ B := by omega
  have hterm1 : (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 ≤
      (50000 + 2 ^ 15 * (K + 1)) * B ^ max 4 (2 * cs + 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (le_max_left _ _))
  have hterm2 : 5 * B ^ 2 * (Cs * (2000 * B ^ 2) ^ cs) ≤
      (5 * Cs * 2000 ^ cs) * B ^ max 4 (2 * cs + 2) := by
    calc 5 * B ^ 2 * (Cs * (2000 * B ^ 2) ^ cs)
        = 5 * B ^ 2 * (Cs * (2000 ^ cs * (B ^ 2) ^ cs)) := by rw [Nat.mul_pow]
      _ = (5 * Cs * 2000 ^ cs) * (B ^ (2 * cs) * B ^ 2) := by rw [← Nat.pow_mul]; ring
      _ = (5 * Cs * 2000 ^ cs) * B ^ (2 * cs + 2) := by rw [← pow_add]
      _ ≤ (5 * Cs * 2000 ^ cs) * B ^ max 4 (2 * cs + 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (le_max_right _ _))
  calc (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 + 5 * B ^ 2 * (Cs * (2000 * B ^ 2) ^ cs)
      ≤ (50000 + 2 ^ 15 * (K + 1)) * B ^ max 4 (2 * cs + 2) +
          (5 * Cs * 2000 ^ cs) * B ^ max 4 (2 * cs + 2) := Nat.add_le_add hterm1 hterm2
    _ = ((50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs) * B ^ max 4 (2 * cs + 2) :=
        (Nat.add_mul ..).symm

/-- Numerical bounds connecting `buildTopMinA ≤ a` to `PParam`, `depthOf`, root space,
level space, and preparation cost. -/
lemma buildTopStatic_numBounds {G : Graph} {Cs cs phiNum phiDen M a : ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hmM : G.m ≤ M) (hdeg : ∀ v < G.n, 1 ≤ G.deg v) (ha : buildTopMinA ≤ a)
    (hSpPoly : BuildLevelSpacePoly space Cs cs) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let D := leafDepth x b
    let d := dOf phiNum phiDen
    let Γ := gammaHP a d M
    let B := phiDen + G.n + G.m + M + Γ + 2
    4 * PParam ParamConfig.default (2 ^ x) (depthOf G.m) ≤ Γ ∧
    depthOf G.m ^ 3 ≤ Γ ∧
    d ≤ phiDen ∧
    xOf G.m ≤ 8 * G.m + 8 ∧
    buildTopRootSpace G.n G.m ≤ 50000 * B ^ 4 ∧
    (∀ h, buildTopPrepareHeap (h + buildTopRootWorkspace G.n G.m) x D - h ≤ 200 * G.m * Γ) ∧
    (∀ (H : Graph) (s k bh : ℕ), H.n = 2 ^ x →
      H.m ≤ (49 * (x + 1) + 2) * 2 ^ x → s ≤ 2 ^ x → k ≤ 2 ^ x →
      bh ≤ max (100 * d) (4 * PParam ParamConfig.default (2 ^ x) (depthOf G.m)) →
      space H s k (2 ^ x) (depthOf G.m) (49 * (x + 1) + 2) (x + 1) (x + 1) bh ≤
        Cs * (2000 * B ^ 2) ^ cs) ∧
    (∀ h, (buildTopPrepareCompactContract 0 0 h x b D phiNum phiDen G).cost [] (fun _ => 0) +
      (30 * G.m + 30) + (13 * (Nat.log 2 (8 * G.m + 7) + 1) + 19 * depthOf G.m + 120) ≤
      20000 * G.m * Γ) := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set D := leafDepth x b
  set d := dOf phiNum phiDen
  set Γ := gammaHP a d M
  set B := phiDen + G.n + G.m + M + Γ + 2
  generalize hcfg_eq : ParamConfig.default = cfg
  obtain ⟨_, _, hxpos, hlt4m, hxX⟩ := buildTop_x_facts hG hm
  have h2x_lt : 2 ^ x < 4 * G.m := hlt4m
  obtain ⟨_, hd1, _⟩ := dOf_spec h1 h2
  have hn2m : G.n ≤ 2 * G.m := n_le_two_m hG hdeg
  have hD_le : D ≤ depthOf G.m := leafDepth_buildTopBranch_le hxpos hxX
  have hΓ1 : 1 ≤ Γ := one_le_gammaHP a d M
  -- Bounds on 4 * PParam and depthOf^3 via BuildProgCost.exp_gamma
  obtain ⟨hV, hv1⟩ := BuildParams.num_v G.m
  set v := vxOf G.m
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  set c₁ := 90 + cfg.a₀ + 3 * cfg.c0 * cfg.A
  set Kc := 87 + cfg.a₀
  set Dd := (1 + (2 + d) ^ 4) ^ 2
  set E := 63 + 7 * v + 3 * (h * (Kc + 6 * v))
  set e := 10 * h ^ 2 + 10
  set S := 2 * h ^ 2 + 4 + (c₁ + 6 * v) * e + E
  have hDd : 1 ≤ Dd := Nat.one_le_pow _ _ (by omega)
  have hell : ell (2 ^ x) ≤ 2 ^ v := by
    have := (ell_two_pow x).2; omega
  have hP_le : PParam cfg (2 ^ x) h ≤ 2 ^ (h * (Kc + 6 * v)) := PParam_le hell h
  have ha_cfg : 10 * c₁ + 2 * Kc + 120 ≤ a := by
    have : buildTopMinA = 10 * c₁ + 2 * Kc + 120 := by simp only [buildTopMinA, c₁, Kc, hcfg_eq]
    omega
  have hexp := exp_gamma (c₁ := c₁) (K := Kc) ha_cfg hh hv1
  have hU : 2 ^ (h + (v + S)) ≤ uOf a G.m ^ (2 * h + 2) := by
    unfold uOf
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have : h + (v + S) = h + v + (2 * h ^ 2 + 4 + (c₁ + 6 * v) * (10 * h ^ 2 + 10) +
        (63 + 7 * v + 3 * (h * (Kc + 6 * v)))) := by simp only [S, E, e]; ring
    rw [this]
    exact hexp
  have hΓge : Dd * uOf a G.m ^ (2 * h + 2) ≤ Γ := BuildParams.gammaHP_ge a d hmM
  have h2S_le_Γ : 2 ^ (h + (v + S)) ≤ Γ := (hU.trans (Nat.le_mul_of_pos_left _ hDd)).trans hΓge
  have h4P_le_Γ : 4 * PParam cfg (2 ^ x) h ≤ Γ := by
    have h1' : 4 * PParam cfg (2 ^ x) h ≤ 2 ^ (2 + h * (Kc + 6 * v)) := by
      calc 4 * PParam cfg (2 ^ x) h = 2 ^ 2 * PParam cfg (2 ^ x) h := by ring
        _ ≤ 2 ^ 2 * 2 ^ (h * (Kc + 6 * v)) := Nat.mul_le_mul_left _ hP_le
        _ = 2 ^ (2 + h * (Kc + 6 * v)) := (pow_add ..).symm
    have h2' : 2 + h * (Kc + 6 * v) ≤ h + (v + S) := by
      dsimp only [S, E]
      have : h * (Kc + 6 * v) ≤ 3 * (h * (Kc + 6 * v)) := Nat.le_mul_of_pos_left _ (by decide)
      omega
    exact h1'.trans ((Nat.pow_le_pow_right (by norm_num) h2').trans h2S_le_Γ)
  have hh3_le_Γ : h ^ 3 ≤ Γ := by
    have hh2 : h ≤ 2 ^ h := Nat.lt_two_pow_self.le
    have h1' : h ^ 3 ≤ 2 ^ (3 * h) := by
      calc h ^ 3 ≤ (2 ^ h) ^ 3 := Nat.pow_le_pow_left hh2 3
        _ = 2 ^ (h * 3) := (pow_mul ..).symm
        _ = 2 ^ (3 * h) := by ring_nf
    have h2' : 3 * h ≤ h + (v + S) := by
      have hKc : 1 ≤ Kc + 6 * v := by dsimp only [Kc]; omega
      have hmul : h ≤ h * (Kc + 6 * v) := Nat.le_mul_of_pos_right h hKc
      dsimp only [S, E]; omega
    exact h1'.trans ((Nat.pow_le_pow_right (by norm_num) h2').trans h2S_le_Γ)
  have hh_le_Γ : h ≤ Γ := (Nat.le_self_pow (by decide : 3 ≠ 0) h).trans hh3_le_Γ
  have hd_le_den : d ≤ phiDen := by
    dsimp only [d]
    rw [dOf_eq_div_pred phiNum phiDen (by omega) (by omega)]
    have : (phiDen - 1) / phiNum ≤ phiDen - 1 := Nat.div_le_self _ _
    omega
  have hxOf_le : xOf G.m ≤ 8 * G.m + 8 := by
    unfold xOf
    rw [Nat.clog_le_iff_le_pow (by decide)]
    exact Nat.lt_two_pow_self.le
  have hlog_le : Nat.log 2 (8 * G.m + 7) + 1 ≤ 8 * G.m + 8 := by
    have := Nat.log_le_self 2 (8 * G.m + 7); omega
  -- Root space bound
  have hRootSp : buildTopRootSpace G.n G.m ≤ 50000 * B ^ 4 := by
    have hB_ge : G.m ≤ B := by omega
    have hBn_ge : G.n ≤ B := by omega
    have hB1 : 1 ≤ B := by omega
    have hB_pow : B ≤ B ^ 4 := Nat.le_self_pow (by decide : 4 ≠ 0) B
    have hm4 : G.m ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hB_ge 4
    have hdef : buildTopRootSpace G.n G.m = 4 * G.n + 48 * G.m + 6 + 41600 * G.m ^ 4 + 4 := by
      unfold buildTopRootSpace buildTopRootWorkspace portGraphWorkSpace portGraphHeapSpace; omega
    rw [hdef]
    have h1' : 4 * G.n + 48 * G.m + 10 ≤ 62 * B ^ 4 := by
      have : 4 * G.n + 48 * G.m + 10 ≤ 62 * B := by omega
      exact this.trans (Nat.mul_le_mul_left 62 hB_pow)
    have h2' : 41600 * G.m ^ 4 ≤ 41600 * B ^ 4 := Nat.mul_le_mul_left _ hm4
    clear * - h1' h2'
    omega
  -- Prepare heap offset bound
  have hPrepHeap : ∀ h0, buildTopPrepareHeap (h0 + buildTopRootWorkspace G.n G.m) x D - h0 ≤
      200 * G.m * Γ := by
    intro h0
    have hEq : buildTopPrepareHeap (h0 + buildTopRootWorkspace G.n G.m) x D - h0 =
        buildTopRootWorkspace G.n G.m + 2 ^ x + 1 + 13 * D + (D + 1) + D * 2 ^ x + 7 * D := by
      simp only [buildTopPrepareHeap, buildTopScheduleEnd, buildTopScheduleReplies,
        buildTopSchedulePointer, buildTopPrepareTable, Nat.add_assoc]
      exact Nat.add_sub_cancel_left h0 _
    rw [hEq]
    have hws : buildTopRootWorkspace G.n G.m ≤ 56 * G.m + 6 := by
      unfold buildTopRootWorkspace portGraphWorkSpace; omega
    have hDP : D * 2 ^ x ≤ 4 * (G.m * Γ) := by
      calc D * 2 ^ x ≤ Γ * (4 * G.m) := Nat.mul_le_mul (hD_le.trans hh_le_Γ) h2x_lt.le
        _ = 4 * (G.m * Γ) := by ring
    have hD_mΓ : D ≤ G.m * Γ := (hD_le.trans hh_le_Γ).trans (Nat.le_mul_of_pos_left _ hm)
    have hm_mΓ : G.m ≤ G.m * Γ := Nat.le_mul_of_pos_right _ hΓ1
    have h1_mΓ : 1 ≤ G.m * Γ := Nat.mul_pos hm hΓ1
    have h200 : 200 * G.m * Γ = 200 * (G.m * Γ) := by ring
    rw [h200]
    clear * - hws h2x_lt hDP hD_mΓ hm_mΓ h1_mΓ
    omega
  -- Level space bound
  have hW_le_Γ : (WParam cfg (2 ^ x)) ^ (10 * h ^ 2 + 10) ≤ Γ := by
    have hW1 : WParam cfg (2 ^ x) ≤ 2 ^ (c₁ + 6 * v) := by
      simpa only [c₁] using BuildParams.num_W_le (cfg := cfg) hell
    have hW2 : (WParam cfg (2 ^ x)) ^ e ≤ 2 ^ ((c₁ + 6 * v) * e) := by
      calc (WParam cfg (2 ^ x)) ^ e ≤ (2 ^ (c₁ + 6 * v)) ^ e := Nat.pow_le_pow_left hW1 e
        _ = 2 ^ ((c₁ + 6 * v) * e) := (pow_mul ..).symm
    have hExpLe : (c₁ + 6 * v) * e ≤ h + (v + S) := by dsimp only [S]; omega
    exact hW2.trans ((Nat.pow_le_pow_right (by norm_num) hExpLe).trans h2S_le_Γ)
  have hRank : h ≤ ell (2 ^ x) := depthOf_le_ell_two_pow hm
  have hLvlSp : ∀ (H : Graph) (s k bh : ℕ), H.n = 2 ^ x →
      H.m ≤ (49 * (x + 1) + 2) * 2 ^ x → s ≤ 2 ^ x → k ≤ 2 ^ x →
      bh ≤ max (100 * d) (4 * PParam cfg (2 ^ x) h) →
      space H s k (2 ^ x) h (49 * (x + 1) + 2) (x + 1) (x + 1) bh ≤ Cs * (2000 * B ^ 2) ^ cs := by
    intro H s k bh hHn hHm hs hk hbh
    refine (hSpPoly H s k (2 ^ x) h (49 * (x + 1) + 2) (x + 1) (x + 1) bh hRank).trans ?_
    apply Nat.mul_le_mul_left Cs
    apply Nat.pow_le_pow_left
    have hx_le : x ≤ 4 * G.m := (Nat.lt_two_pow_self.le).trans hlt4m.le
    have h2x_le_4B : 2 ^ x ≤ 4 * B := by omega
    have hΔ_le : 49 * (x + 1) + 2 ≤ 200 * B := by omega
    have hHm_le : H.m ≤ 800 * B ^ 2 := by
      calc H.m ≤ (49 * (x + 1) + 2) * 2 ^ x := hHm
        _ ≤ (200 * B) * (4 * B) := Nat.mul_le_mul hΔ_le h2x_le_4B
        _ = 800 * B ^ 2 := by ring
    have hbh_le : bh ≤ 100 * B := by
      have : max (100 * d) (4 * PParam cfg (2 ^ x) h) ≤ 100 * B := max_le (by omega) (by omega)
      exact hbh.trans this
    have hW_le_B : (WParam ParamConfig.default (2 ^ x)) ^ (10 * h ^ 2 + 10) ≤ B := by
      rw [hcfg_eq]; omega
    have hB_sq : B ≤ B ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) B
    have hRest : H.n + s + k + 2 ^ x + h + (49 * (x + 1) + 2) + (x + 1) + (x + 1) + bh +
        (WParam ParamConfig.default (2 ^ x)) ^ (10 * h ^ 2 + 10) + 2 ≤ 1200 * B ^ 2 := by
      have : H.n + s + k + 2 ^ x + h + (49 * (x + 1) + 2) + (x + 1) + (x + 1) + bh +
          (WParam ParamConfig.default (2 ^ x)) ^ (10 * h ^ 2 + 10) + 2 ≤ 1200 * B := by
        clear * - hHn hs hk h2x_le_4B hh_le_Γ hx_le hΔ_le hbh_le hW_le_B
        omega
      exact this.trans (Nat.mul_le_mul_left 1200 hB_sq)
    clear * - hHm_le hRest
    omega
  -- Preparation + size + branch cost bound
  have hPrepCost : ∀ h0,
      (buildTopPrepareCompactContract 0 0 h0 x b D phiNum phiDen G).cost [] (fun _ => 0) +
      (30 * G.m + 30) + (13 * (Nat.log 2 (8 * G.m + 7) + 1) + 19 * h + 120) ≤
      20000 * G.m * Γ := by
    intro h0
    simp only [buildTopPrepareCompactContract, buildTopRootSeededCompactContract,
      buildTopRootLayoutCompactContract, buildTopRootCompactContract,
      buildTopPortCompactWrapContract, buildTopPortCompactCost, buildTopPlayerSetupContract]
    have hD_mΓ : D ≤ G.m * Γ := (hD_le.trans hh_le_Γ).trans (Nat.le_mul_of_pos_left _ hm)
    have hh_mΓ : h ≤ G.m * Γ := hh_le_Γ.trans (Nat.le_mul_of_pos_left _ hm)
    have hm_mΓ : G.m ≤ G.m * Γ := Nat.le_mul_of_pos_right _ hΓ1
    have h1_mΓ : 1 ≤ G.m * Γ := Nat.mul_pos hm hΓ1
    have h20k : 20000 * G.m * Γ = 20000 * (G.m * Γ) := by ring
    rw [h20k]
    clear * - hn2m h2x_lt hlog_le hD_mΓ hh_mΓ hm_mΓ h1_mΓ
    omega
  exact ⟨h4P_le_Γ, hh3_le_Γ, hd_le_den, hxOf_le, hRootSp, hPrepHeap, hLvlSp, hPrepCost⟩

/-! ### Clean state-chaining helpers for `buildTopStaticEntry` -/

lemma static_seq_assign {w r v c₁ c₂ : ℕ} {e : Expr} {s₂ : Stmt} {p : Program}
    {ω : ℕ → Bool} {st : State} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (h₂ : ∀ st' : State, st'.mem = st.mem → st'.regs r = v →
      (∀ j, j ≠ r → st'.regs j = st.regs j) →
      ∃ o t c, Runs w p ω s₂ st' o t c ∧ Q o t ∧ c₁ + e.size + 2 + c ≤ c₂) :
    ∃ o t c, Runs w p ω (.seq (.assign r e) s₂) st o t c ∧ Q o t ∧ c₁ + c ≤ c₂ :=
  runs_seq_assign_le he (h₂ { st with regs := Function.update st.regs r v } rfl
    (Function.update_self r v st.regs) (fun _ hj => Function.update_of_ne hj v st.regs))

lemma static_seq_call {w r f c₁ c₂ : ℕ} {es : List Expr} {vs : List ℕ}
    {s₂ : Stmt} {p : Program} {ω : ℕ → Bool} {st : State} {C : Contract}
    {Q : Outcome → State → Prop}
    (hc : MeetsContract w p f C) (he : evalArgs w st es = some vs)
    (hw : ∀ v ∈ vs, v < 2 ^ w) (hpre : C.pre vs st.mem)
    (h₂ : ∀ v (st' : State), C.post vs st.mem v st'.mem → st'.regs r = v →
      (∀ j, j ≠ r → st'.regs j = st.regs j) →
      ∃ o t c, Runs w p ω s₂ st' o t c ∧ Q o t ∧
        c₁ + argsSize es + C.cost vs st.mem + 2 + c ≤ c₂) :
    ∃ o t c, Runs w p ω (.seq (.call r f es) s₂) st o t c ∧ Q o t ∧ c₁ + c ≤ c₂ :=
  runs_seq_call_le hc he hw hpre fun v mem' pos' hpost =>
    h₂ v { st with mem := mem', regs := Function.update st.regs r v, pos := pos' }
      hpost (Function.update_self r v st.regs) (fun _ hj => Function.update_of_ne hj v st.regs)

/-- Helper: extract individual `p.procs[k + i]?` facts from `p.HasAt k (buildTopStaticFixedHelpers k ++ ...)`. -/
private lemma fixed_proc_at {PL : HierProc} {p : Program} {k : ℕ}
    (hk : p.HasAt k ((buildTopStaticProc PL).helpers k))
    (i : ℕ) (hi : i < 50) :
    p.procs[k + i]? = some ((buildTopStaticFixedHelpers k)[i]'(by rw [buildTopStaticFixedHelpers_length]; exact hi)) := by
  have h1 := hasAt_append_left (hasAt_append_left hk)
  exact h1 i (by rw [buildTopStaticFixedHelpers_length]; exact hi)

lemma buildTopStatic_subprocs {PL : HierProc} {p : Program} {k : ℕ}
    (hk : p.HasAt k ((buildTopStaticProc PL).helpers k)) :
    p.procs[k]? = some buildTopSize ∧
    p.procs[k + 1]? = some buildTopBranchProc ∧
    p.procs[k + 2]? = some (buildTopPrepare (k + 3) (k + 16) (k + 22)) ∧
    p.procs[k + 3]? = some (buildTopRootSeeded (k + 4) (k + 5)) ∧
    buildTopRootCompactModule.At p (k + 4) (k + 7) ∧
    p.procs[k + 5]? = some (buildTopSeedDepth (k + 13) (k + 6)) ∧
    p.procs[k + 6]? = some buildTopSeedRoot ∧
    p.HasAt (k + 13) [iotaP] ∧
    p.procs[k + 11]? = some buildCopyProc ∧
    p.procs[k + 16]? = some (buildTopPlayerSetup (k + 17) (k + 18) (k + 20)) ∧
    p.procs[k + 17]? = some buildTopPlayerRank ∧
    p.procs[k + 18]? = some (buildTopPlayerScale (k + 19)) ∧
    p.procs[k + 19]? = some buildTopPlayerPower ∧
    p.procs[k + 20]? = some (buildTopPlayerTableLoop (k + 21)) ∧
    p.procs[k + 21]? = some buildTopPlayerTableRow ∧
    p.procs[k + 22]? = some (buildTopScheduleRun (k + 23)) ∧
    p.procs[k + 23]? = some (buildTopScheduleRow (k + 24) (k + 25) (k + 26)) ∧
    p.procs[k + 24]? = some buildTopSchedulePlayers ∧
    p.procs[k + 25]? = some buildTopScheduleGeometry ∧
    p.procs[k + 26]? = some buildTopScheduleAddresses ∧
    p.procs[k + 27]? = some (buildTopDriver (k + 28)) ∧
    p.procs[k + 28]? = some (buildTopAdvance (k + 29) (k + 31)) ∧
    p.procs[k + 29]? = some (buildTopDepth (k + 30)) ∧
    p.procs[k + 30]? = some (buildTopParentCall (k + 50)) ∧
    p.procs[k + 31]? = some (buildTopNextDir (k + 32)) ∧
    p.procs[k + 32]? = some (buildTopNextRow (k + 33)) ∧
    p.procs[k + 33]? = some (buildTopReplyRead (k + 34)) ∧
    p.procs[k + 34]? = some initCSRSeek ∧
    p.procs[k + 35]? = some (buildTopPackAll (k + 36) (k + 37) (k + 39) (k + 41) (k + 43) (k + 45)) ∧
    p.procs[k + 36]? = some buildTopNumConn ∧
    p.procs[k + 37]? = some (buildTopLabels (k + 13) (k + 38)) ∧
    p.procs[k + 38]? = some initFillWord ∧
    p.procs[k + 39]? = some (buildTopSec3 (k + 40) (k + 46)) ∧
    p.procs[k + 40]? = some (buildTopSec3Dir (k + 48)) ∧
    p.procs[k + 41]? = some (buildTopSec4 (k + 42) (k + 46)) ∧
    p.procs[k + 42]? = some (buildTopSec4Dir (k + 48)) ∧
    p.procs[k + 43]? = some (buildTopSec5 (k + 44) (k + 46)) ∧
    p.procs[k + 44]? = some (buildTopSec5Dir (k + 48)) ∧
    p.procs[k + 45]? = some (buildTopFinish (k + 46) (k + 49)) ∧
    p.procs[k + 46]? = some (initCSRWrite (k + 47)) ∧
    p.procs[k + 47]? = some (buildTopRow (k + 11)) ∧
    p.procs[k + 48]? = some (buildTopReplySpan (k + 33)) ∧
    p.procs[k + 49]? = some copyDown ∧
    PL.At p (k + 50) (k + 51) := by
  have hAt := fixed_proc_at hk
  have hRootH : p.HasAt (k + 7) (buildTopRootCompactHelpers (k + 7)) := by
    intro i hi
    have hi9 : i < 9 := by simpa [buildTopRootCompactHelpers] using hi
    have h := hAt (7 + i) (by omega)
    rw [show k + (7 + i) = k + 7 + i by omega] at h
    rw [h]
    congr 1
    simp only [buildTopStaticFixedHelpers, buildTopRootCompactHelpers]
    match i with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
    | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | i + 9 => omega
  have hIota : p.HasAt (k + 13) [iotaP] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 13 (by decide)
  have hPLAt : PL.At p (k + 50) (k + 51) := by
    have hk1 := hasAt_append_right (hasAt_append_left hk)
    have hk2 := hasAt_append_right hk
    simp only [buildTopStaticFixedHelpers_length, List.length_append,
      List.length_cons, List.length_nil] at hk1 hk2
    exact ⟨by simpa using hk1 0 (by simp), by simpa [Nat.add_assoc] using hk2⟩
  refine ⟨by simpa [buildTopStaticFixedHelpers] using hAt 0 (by decide),
    by simpa [buildTopStaticFixedHelpers] using hAt 1 (by decide),
    by simpa [buildTopStaticFixedHelpers] using hAt 2 (by decide),
    by simpa [buildTopStaticFixedHelpers] using hAt 3 (by decide),
    ⟨by simpa [buildTopStaticFixedHelpers, buildTopRootCompactModule] using hAt 4 (by decide), hRootH⟩,
    by simpa [buildTopStaticFixedHelpers] using hAt 5 (by decide),
    by simpa [buildTopStaticFixedHelpers] using hAt 6 (by decide),
    hIota,
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 11 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 16 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 17 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 18 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 19 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 20 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 21 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 22 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 23 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 24 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 25 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 26 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 27 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 28 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 29 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 30 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 31 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 32 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 33 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 34 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 35 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 36 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 37 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 38 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 39 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 40 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 41 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 42 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 43 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 44 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 45 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 46 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 47 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 48 (by decide),
    by simpa [buildTopStaticFixedHelpers, buildTopRootCompactHelpers] using hAt 49 (by decide),
    hPLAt⟩

/-! ### Setup phase triple (steps 1..9) -/

lemma staticSetup_triple {w sizeProc branchProc gAddr h : ℕ} {G : Graph}
    {p : Program} {st : State}
    (hSize : p.procs[sizeProc]? = some buildTopSize)
    (hBranch : p.procs[branchProc]? = some buildTopBranchProc)
    (r0 : st.regs 0 = gAddr) (r4 : st.regs 4 = h)
    (hGat0 : GraphAt st.mem gAddr G) (hm : 1 ≤ G.m)
    (hga1_w : gAddr + 1 < 2 ^ w)
    (h8m_w : 8 * G.m + 8 < 2 ^ w)
    (hpow_w : depthOf G.m ^ 3 < 2 ^ w)
    (hsum_w : xOf G.m + depthOf G.m < 2 ^ w)
    (hPw : 2 ^ Nat.clog 2 (2 * G.m) < 2 ^ w)
    (h2Pw : 2 * 2 ^ Nat.clog 2 (2 * G.m) < 2 ^ w)
    (hrootG_w : buildTopRootGraphAddr h G.n G.m < 2 ^ w) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    Triple w p (fun t => t = st) (buildTopStaticSetup sizeProc branchProc)
      (normalPost fun t =>
        t.mem = st.mem ∧
        (∀ i < 5, t.regs i = st.regs i) ∧
        t.regs 5 = G.n ∧ t.regs 6 = G.m ∧ t.regs 7 = x ∧ t.regs 8 = 2 ^ x ∧
        t.regs 9 = b ∧ t.regs 10 = 2 ^ b ∧ t.regs 11 = leafDepth x b ∧
        t.regs 12 = buildTopRootOwnersAddr h G.n ∧ t.regs 13 = buildTopRootGraphAddr h G.n G.m)
      (fun _ => (30 * G.m + 30) + (13 * (Nat.log 2 (8 * G.m + 7) + 1) + 19 * depthOf G.m + 120) + 100) := by
  dsimp only
  intro st' ω hst'
  subst st'
  set x := Nat.clog 2 (2 * G.m)
  set P := 2 ^ x
  set b := buildTopBranch x G.m
  set twoPowB := 2 ^ b
  set D := leafDepth x b
  set ownersAddr := buildTopRootOwnersAddr h G.n
  set rootGraph := buildTopRootGraphAddr h G.n G.m
  have h1w : 1 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have hbx : b ≤ x := buildTopBranch_le_x x G.m
  have hxw : x < 2 ^ w := x.lt_two_pow_self.trans hPw
  have h2Bw : twoPowB < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hbx) hPw
  have hown_le : ownersAddr ≤ rootGraph := by unfold rootGraph buildTopRootGraphAddr; omega
  have hown_w : ownersAddr < 2 ^ w := lt_of_le_of_lt hown_le hrootG_w
  have hhn_w : h + G.n < 2 ^ w := by unfold ownersAddr buildTopRootOwnersAddr buildTopRootLoc at hown_w; omega
  have h4m_w : 4 * G.m < 2 ^ w := by omega
  have hxb_w : x + b < 2 ^ w := by
    have hxP : x ≤ P := Nat.lt_two_pow_self.le
    omega
  refine runs_start_le ?_
  unfold buildTopStaticSetup
  refine static_seq_assign (v := G.n)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r0) (graphAt_n hGat0)) ?_
  intro s1 hm1 r1_5 hreg1
  refine static_seq_assign (v := G.m)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq ((hreg1 0 (by decide)).trans r0))
        (Expr.eval_const h1w) hga1_w)
      (by rw [hm1]; exact graphAt_m hGat0)) ?_
  intro s2 hm2 r2_6 hreg2
  have hm2' : s2.mem = st.mem := hm2.trans hm1
  have r2_low : ∀ i < 5, s2.regs i = st.regs i := fun i hi =>
    (hreg2 i (by omega)).trans (hreg1 i (by omega))
  have r2_5 : s2.regs 5 = G.n := (hreg2 5 (by decide)).trans r1_5
  refine static_seq_call (buildTopSize_meetsContract (w := w) hSize) (vs := [G.m])
    (by simp [evalArgs, Expr.eval, r2_6])
    (fun v hv => by simp at hv; subst v; omega)
    ⟨G.m, rfl, hm, by omega⟩ ?_
  intro v3 s3 ⟨hv3, hm3⟩ r3_7 hreg3
  have hv3' : v3 = x := by simpa [x] using hv3
  subst hv3'
  have hm3' : s3.mem = st.mem := hm3.trans hm2'
  have r3_low : ∀ i < 5, s3.regs i = st.regs i := fun i hi => (hreg3 i (by omega)).trans (r2_low i hi)
  have r3_5 : s3.regs 5 = G.n := (hreg3 5 (by decide)).trans r2_5
  have r3_6 : s3.regs 6 = G.m := (hreg3 6 (by decide)).trans r2_6
  refine static_seq_assign (v := P)
    (by
      have hsh := Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq r3_7)
        (by simpa only [Nat.shiftLeft_eq, Nat.one_mul] using hPw)
      simpa only [Nat.shiftLeft_eq, Nat.one_mul] using hsh) ?_
  intro s4 hm4 r4_8 hreg4
  have hm4' : s4.mem = st.mem := hm4.trans hm3'
  have r4_low : ∀ i < 5, s4.regs i = st.regs i := fun i hi => (hreg4 i (by omega)).trans (r3_low i hi)
  have r4_5 : s4.regs 5 = G.n := (hreg4 5 (by decide)).trans r3_5
  have r4_6 : s4.regs 6 = G.m := (hreg4 6 (by decide)).trans r3_6
  have r4_7 : s4.regs 7 = x := (hreg4 7 (by decide)).trans r3_7
  refine static_seq_call (buildTopBranchProc_meetsContract (w := w) (x := x) (m := G.m) hBranch)
    (vs := [x, G.m]) (by simp [evalArgs, Expr.eval, r4_6, r4_7])
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl <;> omega)
    ⟨rfl, h8m_w, hpow_w, hsum_w, hxw⟩ ?_
  intro v5 s5 ⟨hv5, hm5⟩ r5_9 hreg5
  have hv5' : v5 = b := hv5
  subst hv5'
  have hm5' : s5.mem = st.mem := hm5.trans hm4'
  have r5_low : ∀ i < 5, s5.regs i = st.regs i := fun i hi => (hreg5 i (by omega)).trans (r4_low i hi)
  have r5_5 : s5.regs 5 = G.n := (hreg5 5 (by decide)).trans r4_5
  have r5_6 : s5.regs 6 = G.m := (hreg5 6 (by decide)).trans r4_6
  have r5_7 : s5.regs 7 = x := (hreg5 7 (by decide)).trans r4_7
  have r5_8 : s5.regs 8 = P := (hreg5 8 (by decide)).trans r4_8
  refine static_seq_assign (v := twoPowB)
    (by
      have hsh := Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq r5_9)
        (by simpa only [Nat.shiftLeft_eq, Nat.one_mul] using h2Bw)
      simpa only [Nat.shiftLeft_eq, Nat.one_mul] using hsh) ?_
  intro s6 hm6 r6_10 hreg6
  refine static_seq_assign (v := D)
    (Expr.eval_div
      (Expr.eval_sub
        (Expr.eval_add (Expr.eval_reg_of_eq ((hreg6 7 (by decide)).trans r5_7))
          (Expr.eval_reg_of_eq ((hreg6 9 (by decide)).trans r5_9)) hxb_w)
        (Expr.eval_const h1w) hxb_w)
      (Expr.eval_reg_of_eq ((hreg6 9 (by decide)).trans r5_9)) (by omega)) ?_
  intro s7 hm7 r7_11 hreg7
  have r7_4 : s7.regs 4 = h := (hreg7 4 (by decide)).trans ((hreg6 4 (by decide)).trans ((r5_low 4 (by decide)).trans r4))
  have r7_5 : s7.regs 5 = G.n := (hreg7 5 (by decide)).trans ((hreg6 5 (by decide)).trans r5_5)
  refine static_seq_assign (v := ownersAddr)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r7_4) (Expr.eval_reg_of_eq r7_5) hhn_w)
      (Expr.eval_reg_of_eq r7_5) hown_w) ?_
  intro s8 hm8 r8_12 hreg8
  have r8_6 : s8.regs 6 = G.m := (hreg8 6 (by decide)).trans ((hreg7 6 (by decide)).trans ((hreg6 6 (by decide)).trans r5_6))
  refine runs_assign_le (v := rootGraph)
    (Expr.eval_add (Expr.eval_reg_of_eq r8_12)
      (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq r8_6) h4m_w) hrootG_w) ?_ ?_
  · refine ⟨hm8.trans (hm7.trans (hm6.trans hm5')), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      dsimp only; rw [Function.update_of_ne (by omega)]
      exact (hreg8 i (by omega)).trans ((hreg7 i (by omega)).trans ((hreg6 i (by omega)).trans (r5_low i hi)))
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 5 (by decide)).trans r7_5
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact r8_6
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 7 (by decide)).trans ((hreg7 7 (by decide)).trans ((hreg6 7 (by decide)).trans r5_7))
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 8 (by decide)).trans ((hreg7 8 (by decide)).trans ((hreg6 8 (by decide)).trans r5_8))
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 9 (by decide)).trans ((hreg7 9 (by decide)).trans ((hreg6 9 (by decide)).trans r5_9))
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 10 (by decide)).trans ((hreg7 10 (by decide)).trans r6_10)
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (hreg8 11 (by decide)).trans r7_11
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact r8_12
    · dsimp only; rw [Function.update_self]
  · simp only [buildTopSizeContract, buildTopBranchProcContract, Expr.size, argsSize,
      List.getD_cons_zero]
    omega

end MinCostFlow.HierPaths
