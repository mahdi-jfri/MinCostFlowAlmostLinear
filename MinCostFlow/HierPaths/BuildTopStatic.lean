module

public import MinCostFlow.HierPaths.BuildTopStaticSetup
import Mathlib.Tactic.Ring

/-!
# Top-level static hierarchy builder: `StaticProcSpec` proof

Proves `buildTopStatic_spec`: for any deterministic level procedure `PL` satisfying
`ProvidesBuildLevel` with polynomial space bound `BuildLevelSpacePoly space Cs cs`,
`buildTopStaticProc PL` meets `StaticProcSpec` for every `a ≥ buildTopMinA`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp MinCostFlow.LowStretch
open scoped BigOperators

/-! ### Main contract and `StaticProcSpec` theorem -/

/-- **Main theorem of the static hierarchy builder**: given a deterministic level procedure
`PL` satisfying `ProvidesBuildLevel` with a polynomial space envelope `BuildLevelSpacePoly`,
`buildTopStaticProc PL` meets `StaticProcSpec` for every `a ≥ buildTopMinA`. -/
theorem buildTopStatic_spec
    {PL : HierProc} {K Cs cs : ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hPL_nr : PL.NoRand)
    (hPL_spec : ∀ w p j k, PL.At p j k → ProvidesBuildLevel w K space p j)
    (hSpPoly : BuildLevelSpacePoly space Cs cs)
    (a : ℕ) (ha : buildTopMinA ≤ a) :
    StaticProcSpec a (buildTopStaticProc PL) (2 ^ 20 * (K + 1))
      (buildTopStaticSpace K Cs cs a)
      ((50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs) (max 4 (2 * cs + 2)) 1 := by
  refine ⟨buildTopStaticProc_noRand hPL_nr, buildTopStaticSpace_spaceForm K Cs cs a, ?_⟩
  intro hc _ w p j k ⟨hj, hk⟩
  obtain ⟨hSize, hBranch, hPrep, hRootSeed, hRootMod, hSeedDepth, hSeedRoot, hIota, hCopy,
    hPlaySetup, hPlayRank, hPlayScale, hPlayPow, hPlayLoop, hPlayRow,
    hSchRun, hSchRow, hSchPlay, hSchGeo, hSchAddr,
    hDrv, hAdv, hDep, hCall, hNext, hNextRow, hRead, hSeek,
    hPackAll, hNumConn, hLab, hFill, hSec3, hDir3, hSec4, hDir4, hSec5, hDir5,
    hFin, hGat, hRow, hSpan, hMove, hPLAt⟩ := buildTopStatic_subprocs hk
  have hLvl : ProvidesBuildLevel w K space p (k + 50) := hPL_spec w p (k + 50) (k + 51) hPLAt
  have hAdvAll : ∀ D : BuildTopDepthInput, MeetsContract w p (k + 28) (D.advanceContract w K space) :=
    buildTopAdvance_from_level hAdv hDep hCall hLvl hNext hNextRow hRead hSeek
  refine meetsContract_of_runs hj fun args mem pos ω hwords hpre => ?_
  obtain ⟨hInitPre, hZero0, hSpace0⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, G, rfl, hgh, hGat0, h1, h2, hG, hm, hmM, hdeg, hcond,
    _⟩ := hInitPre
  have hRG : readGraph mem gAddr = G := graphAt_iff_readGraph.mp hGat0
  have hZeroH : ZeroFrom mem h := by simpa [heapArg] using hZero0
  have hRoomS : h + buildTopStaticSpace K Cs cs a phiNum phiDen G.n G.m M < 2 ^ w := by
    have := hSpace0
    simp only [heapArg, List.getLastD, List.getD_cons_zero, List.getD_cons_succ, hRG] at this
    exact this
  set x := Nat.clog 2 (2 * G.m)
  set P := 2 ^ x
  set b := buildTopBranch x G.m
  set twoPowB := 2 ^ b
  set D := leafDepth x b
  set d := dOf phiNum phiDen
  set Γ := gammaHP a d M
  set B := phiDen + G.n + G.m + M + Γ + 2
  set ownersAddr := buildTopRootOwnersAddr h G.n
  set rootGraph := buildTopRootGraphAddr h G.n G.m
  set r := h + buildTopRootWorkspace G.n G.m
  set table := buildTopPrepareTable r x
  set heap₀ := buildTopPrepareHeap r x D
  set spaceBound := Cs * (2000 * B ^ 2) ^ cs
  obtain ⟨_, hP_hs, hxpos, hlt4m, hxX⟩ := buildTop_x_facts hG hm
  obtain ⟨_, hd1, _⟩ := dOf_spec h1 h2
  have hbpos : 0 < b := buildTopBranch_pos hxpos
  have hbx : b ≤ x := buildTopBranch_le_x x G.m
  have hD1 : 1 ≤ D := by
    unfold D leafDepth
    have : 1 * b ≤ x + b - 1 := by omega
    exact (Nat.le_div_iff_mul_le hbpos).mpr this
  have hD_le : D ≤ depthOf G.m := leafDepth_buildTopBranch_le hxpos hxX
  have hn2m : G.n ≤ 2 * G.m := n_le_two_m hG hdeg
  have hΓ1 : 1 ≤ Γ := one_le_gammaHP a d M
  have hB1 : 1 ≤ B := by omega
  have hB_pow4 : B ≤ B ^ 4 := Nat.le_self_pow (by decide : 4 ≠ 0) B
  have hB2_pow4 : B ^ 2 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by decide)
  obtain ⟨h4P_le_Γ, hh3_le_Γ, hd_le_den, hxOf_le, hRootSp, hPrepHeap, hLvlSp, hPrepCost⟩ :=
    buildTopStatic_numBounds (Cs := Cs) (cs := cs) h1 h2 hG hm hmM hdeg ha hSpPoly
  have hDrvCost : 2 ^ x * (∑ i ∈ Finset.range D, (buildTopDepthFactor K x G.m d i + 311)) +
      9 * D + 12 ≤ 2 ^ 14 * (K + 1) * G.m * Γ :=
    buildTopDriverTotalCost_le_gamma hG hm hmM hd1 ha
  have hDrvSum : ∑ i ∈ Finset.range D, buildTopRate K x G.m d i + 9 * D + 12 ≤
      2 ^ 14 * (K + 1) * G.m * Γ := by
    have hmul : ∑ i ∈ Finset.range D, buildTopRate K x G.m d i =
        2 ^ x * ∑ i ∈ Finset.range D, (buildTopDepthFactor K x G.m d i + 311) := by
      unfold buildTopRate; rw [Finset.mul_sum]
    rw [hmul]; exact hDrvCost
  have hmΓ_le_B2 : G.m * Γ ≤ B ^ 2 := by
    calc G.m * Γ ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
      _ = B ^ 2 := by ring
  -- Clear `ha` before heavy word-bound `omega` so `ParamConfig.default` is never unfolded
  have hStaticSp_def : buildTopStaticSpace K Cs cs a phiNum phiDen G.n G.m M =
      (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 + 5 * B ^ 2 * spaceBound := by
    unfold buildTopStaticSpace
    rw [← dOf_eq_ceil_div h1 h2]
  have hRoomExp : h + ((50000 + 2 ^ 15 * (K + 1)) * B ^ 4 + 5 * B ^ 2 * spaceBound) < 2 ^ w := by
    rw [← hStaticSp_def]; exact hRoomS
  have h50000B : 50000 * B ^ 4 < 2 ^ w := by
    have h1' : 50000 * B ^ 4 ≤ (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  have h250B : 250 * B < 2 ^ w := by
    have : 250 * B ≤ 50000 * B ^ 4 := by
      calc 250 * B ≤ 250 * B ^ 4 := Nat.mul_le_mul_left 250 hB_pow4
        _ ≤ 50000 * B ^ 4 := Nat.mul_le_mul_right _ (by decide)
    omega
  have h100B : 100 * B < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h24w : 24 < 2 ^ w := by omega
  have hPw : P < 2 ^ w := by have : P < 4 * G.m := hlt4m; omega
  have h2Pw : 2 * P < 2 ^ w := by have : P < 4 * G.m := hlt4m; omega
  have h2Bw : twoPowB < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hbx) hPw
  have hx_le_P : x ≤ P := Nat.lt_two_pow_self.le
  have hxw : x < 2 ^ w := lt_of_le_of_lt hx_le_P hPw
  have hbw : b < 2 ^ w := lt_of_le_of_lt hbx hxw
  have hhh3 : depthOf G.m ^ 3 ≤ Γ := hh3_le_Γ
  have h4P_Γ : 4 * PParam ParamConfig.default P (depthOf G.m) ≤ Γ := h4P_le_Γ
  have hDw : D < 2 ^ w := lt_of_le_of_lt (hD_le.trans ((Nat.le_self_pow (by decide : 3 ≠ 0) _).trans hhh3)) (by omega)
  have hPrepHeap' : heap₀ - h ≤ 200 * G.m * Γ := hPrepHeap h
  have hHeap0_le : heap₀ ≤ h + 200 * G.m * Γ := by omega
  have hDP_le : D * P ≤ 4 * (G.m * Γ) := by
    have hD_Γ : D ≤ Γ := hD_le.trans ((Nat.le_self_pow (by decide : 3 ≠ 0) _).trans hhh3)
    calc D * P ≤ Γ * (4 * G.m) := Nat.mul_le_mul hD_Γ hlt4m.le
      _ = 4 * (G.m * Γ) := by ring
  have hDP_le_4B2 : D * P ≤ 4 * B ^ 2 := hDP_le.trans (Nat.mul_le_mul_left 4 hmΓ_le_B2)
  have hDrvSpace_le : D * (P * spaceBound + P) ≤ 4 * B ^ 2 * spaceBound + 4 * (G.m * Γ) := by
    have h1' : D * (P * spaceBound + P) = (D * P) * spaceBound + D * P := by ring
    rw [h1']
    exact Nat.add_le_add (Nat.mul_le_mul_right spaceBound hDP_le_4B2) hDP_le
  have hSp_le_B2 : spaceBound ≤ B ^ 2 * spaceBound := by
    have h1' : 1 ≤ B ^ 2 := Nat.one_le_pow 2 B hB1
    simpa using Nat.mul_le_mul_right spaceBound h1'
  have hDrvRoom : heap₀ + D * (P * spaceBound + P) + spaceBound < 2 ^ w := by
    have h1' : 204 * (G.m * Γ) ≤ 2 ^ 15 * (K + 1) * B ^ 4 := by
      calc 204 * (G.m * Γ)
          ≤ (2 ^ 15 * (K + 1)) * (G.m * Γ) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 ^ 15 * (K + 1)) * B ^ 2 := Nat.mul_le_mul_left _ hmΓ_le_B2
        _ ≤ (2 ^ 15 * (K + 1)) * B ^ 4 := Nat.mul_le_mul_left _ hB2_pow4
    have h2' : 2 ^ 15 * (K + 1) * B ^ 4 ≤ (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    have e1 : 200 * G.m * Γ + 4 * (G.m * Γ) = 204 * (G.m * Γ) := by ring
    have e2 : 4 * B ^ 2 * spaceBound + B ^ 2 * spaceBound = 5 * B ^ 2 * spaceBound := by ring
    clear * - hRoomExp hHeap0_le hDrvSpace_le hSp_le_B2 h1' h2' e1 e2
    omega
  have hHeap0_w : heap₀ < 2 ^ w := by omega
  have hTable_le_heap0 : table + 13 * D ≤ heap₀ := by
    unfold heap₀ buildTopPrepareHeap buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer
    omega
  have hr_le_table : r + P < table := by
    unfold table buildTopPrepareTable; omega
  have hRootG_le_r : rootGraph ≤ r := by
    unfold r rootGraph buildTopRootWorkspace buildTopRootGraphAddr buildTopRootOwnersAddr
      buildTopRootLoc
    omega
  have hOwn_le_rootG : ownersAddr ≤ rootGraph := by
    unfold rootGraph buildTopRootGraphAddr; omega
  have hRootSp' : buildTopRootSpace G.n G.m ≤ 50000 * B ^ 4 := hRootSp
  have hRootSp_w : h + buildTopRootSpace G.n G.m < 2 ^ w := by
    have h1' : 50000 * B ^ 4 ≤ (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    clear * - hRoomExp hRootSp' h1'
    omega
  have hr_lt_table : r < table := by unfold table buildTopPrepareTable; omega
  have htable_lt_w : table < 2 ^ w := lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hTable_le_heap0) hHeap0_w
  have hr_lt_w : r < 2 ^ w := lt_trans hr_lt_table htable_lt_w
  have hrootG_w : rootGraph < 2 ^ w := lt_of_le_of_lt hRootG_le_r hr_lt_w
  have hown_w : ownersAddr < 2 ^ w := lt_of_le_of_lt hOwn_le_rootG hrootG_w
  have hrP2_w : r + P + 2 + 13 * D < 2 ^ w := by
    have h1' : table + 13 * D < heap₀ := by
      simp only [heap₀, buildTopPrepareHeap, buildTopScheduleEnd, buildTopScheduleReplies,
        buildTopSchedulePointer]
      omega
    unfold table buildTopPrepareTable at h1'
    omega
  have h49_w : 49 * (x + 1) + 2 < 2 ^ w := by
    have hx4m : x ≤ 4 * G.m := hx_le_P.trans (le_of_lt hlt4m)
    have hmB : G.m + 2 ≤ B := by omega
    clear * - hx4m hmB h250B
    omega
  have h4P_w : 4 * PParam ParamConfig.default P (depthOf G.m) < 2 ^ w :=
    lt_of_le_of_lt h4P_Γ (by omega)
  have h100d_w : 100 * d < 2 ^ w := by clear * - hd_le_den h100B; omega
  have hdepth3_w : depthOf G.m ^ 3 < 2 ^ w := lt_of_le_of_lt hhh3 (by omega)
  have hdepth_w : depthOf G.m < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_self_pow (by decide : 3 ≠ 0) _) hdepth3_w
  have hga1_w : gAddr + 1 < 2 ^ w := by have := graph_encode_length G; omega
  have h8m_w : 8 * G.m + 8 < 2 ^ w := by clear * - h100B; omega
  have hsum_w : xOf G.m + depthOf G.m < 2 ^ w := by
    have : depthOf G.m ≤ Γ := (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans hhh3
    clear * - hxOf_le this h100B; omega
  -- Prepare contract instance
  have hPrepC := buildTopPrepare_compact_meetsContract (w := w) (G := G)
    (ga := gAddr) (h := h) (x := x) (b := b) (n := D) (num := phiNum) (den := phiDen)
    hPrep
    (buildTopRootSeeded_compact_meetsContract hRootSeed
      (buildTopRootCompactModule_meetsContract hRootMod) hSeedDepth hIota hSeedRoot)
    (fun dst term => buildTopPlayerSetup_meetsContract hPlaySetup hPlayRank hPlayScale hPlayPow hPlayLoop hPlayRow)
    (fun tbl src term => buildTopScheduleRun_meetsContract hSchRun hSchRow hSchPlay hSchGeo hSchAddr)
  -- Execute buildTopStaticEntry step by step using clean state binders
  let initRegs : ℕ → ℕ := (startState [gAddr, phiNum, phiDen, M, h] mem pos).regs
  refine runs_start_le ?_
  change ∃ o st' c, Runs w p ω (buildTopStaticEntry k (k + 1) (k + 2) (k + 27) (k + 35))
      (startState [gAddr, phiNum, phiDen, M, h] mem pos) o st' c ∧ _ ∧ _
  unfold buildTopStaticEntry
  -- 1..9. buildTopStaticSetup
  refine runs_seq_triple_le
    (staticSetup_triple (w := w) (G := G) (gAddr := gAddr) (h := h) hSize hBranch
      rfl rfl hGat0 hm hga1_w h8m_w hdepth3_w hsum_w hPw h2Pw hrootG_w) rfl ?_
  intro s9 ⟨hm9', r9_low, _, r9_6, r9_7, r9_8, r9_9, r9_10, r9_11, r9_12, r9_13⟩
  -- 10. call prepProc [gAddr, h, P, rootGraph, D, x, b, G.m, phiNum, phiDen] -> reg 14 = r
  have hPrepPre : (buildTopPrepareCompactContract w gAddr h x b D phiNum phiDen G).pre
      [gAddr, h, P, rootGraph, D, x, b, G.m, phiNum, phiDen] s9.mem := by
    rw [hm9']
    refine ⟨rfl, ⟨rfl, ⟨gAddr, h, rfl, hGat0, hG, hm, hgh, hZeroH, hRootSp_w, h24w⟩, hrP2_w⟩,
      hxpos, by omega, by omega, hwords _ (by simp), h8m_w, hdepth3_w, h100d_w, h4P_w,
      hPw, h49_w, le_rfl, hbpos, hbx, hHeap0_w⟩
  refine static_seq_call hPrepC (vs := [gAddr, h, P, rootGraph, D, x, b, G.m, phiNum, phiDen])
    (by
      have i0 : s9.regs 0 = gAddr := by simpa [startState] using r9_low 0 (by decide)
      have i1 : s9.regs 1 = phiNum := by simpa [startState] using r9_low 1 (by decide)
      have i2 : s9.regs 2 = phiDen := by simpa [startState] using r9_low 2 (by decide)
      have i4 : s9.regs 4 = h := by simpa [startState] using r9_low 4 (by decide)
      simp [evalArgs, Expr.eval, i0, i1, i2, i4, r9_6, r9_7, r9_8, r9_9, r9_11, r9_13]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwords _ (by simp)
      · exact hwords _ (by simp)
      · exact hPw
      · exact hrootG_w
      · exact hDw
      · exact hxw
      · exact hbw
      · exact lt_of_le_of_lt (by omega) h8m_w
      · exact hwords _ (by simp)
      · exact hwords _ (by simp))
    hPrepPre ?_
  intro v10 s10 hPostPrep r10_14 hreg10
  obtain ⟨hreq, hGraphAtP, hOwnAtP, hFrameP, hDir0P, hPtr0P, hTermsP, hRowsP, hZeroP⟩ := hPostPrep
  have hv10_eq : v10 = r := hreq
  subst hv10_eq
  have hFrameP' : ∀ y < h, s10.mem y = mem y := fun y hy => (hFrameP y hy).trans (by rw [hm9']; rfl)
  have r10_4 : s10.regs 4 = h := (hreg10 4 (by decide)).trans (r9_low 4 (by decide))
  have r10_6 : s10.regs 6 = G.m := (hreg10 6 (by decide)).trans r9_6
  have r10_7 : s10.regs 7 = x := (hreg10 7 (by decide)).trans r9_7
  have r10_8 : s10.regs 8 = P := (hreg10 8 (by decide)).trans r9_8
  have r10_9 : s10.regs 9 = b := (hreg10 9 (by decide)).trans r9_9
  have r10_10 : s10.regs 10 = twoPowB := (hreg10 10 (by decide)).trans r9_10
  have r10_11 : s10.regs 11 = D := (hreg10 11 (by decide)).trans r9_11
  have r10_12 : s10.regs 12 = ownersAddr := (hreg10 12 (by decide)).trans r9_12
  have r10_13 : s10.regs 13 = rootGraph := (hreg10 13 (by decide)).trans r9_13
  -- 11. reg 15 := r + P + 1 = table
  refine static_seq_assign (v := table)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r10_14) (Expr.eval_reg_of_eq r10_8)
      (lt_trans hr_le_table htable_lt_w))
      (Expr.eval_const h1w) htable_lt_w) ?_
  intro s11 hm11 r11_15 hreg11
  -- 12. reg 16 := buildTopScheduleEnd table D x + 7 * D = heap₀
  have h13w : 13 < 2 ^ w := by omega
  have h7w : 7 < 2 ^ w := by omega
  have hEnd_le_heap0 : buildTopScheduleEnd table D x ≤ heap₀ := Nat.le_add_right _ _
  have hEndW : buildTopScheduleEnd table D x < 2 ^ w := lt_of_le_of_lt hEnd_le_heap0 hHeap0_w
  have h7D_w : 7 * D < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hHeap0_w
  refine static_seq_assign (v := heap₀)
    (Expr.eval_add
      (eval_buildTopRepliesExpr (Expr.eval_reg_of_eq r11_15)
        (Expr.eval_reg_of_eq ((hreg11 11 (by decide)).trans r10_11))
        (Expr.eval_reg_of_eq ((hreg11 7 (by decide)).trans r10_7))
        (Expr.eval_reg_of_eq ((hreg11 11 (by decide)).trans r10_11)) h13w hPw hEndW)
      (Expr.eval_mul (Expr.eval_const h7w)
        (Expr.eval_reg_of_eq ((hreg11 11 (by decide)).trans r10_11)) h7D_w)
      hHeap0_w) ?_
  intro s12 hm12 r12_16 hreg12
  have hm12' : s12.mem = s10.mem := hm12.trans hm11
  -- Wrap buildTopDriver_from_prepare into a one-shot Contract
  let drvC : Contract :=
    { pre := fun args m => args = [table, D, heap₀] ∧ m = s10.mem
      post := fun _ _ tail m' => BuildTopRecInv r x b D G.m d spaceBound (hostGraph cloud G) s10.mem D tail m'
      cost := fun _ _ => (∑ i ∈ Finset.range D, buildTopRate K x G.m d i) + 9 * D + 12 }
  have hDrvMC : MeetsContract w p (k + 27) drvC := by
    refine meetsContract_of_runs hDrv fun a' m' pos' ω' _ ⟨ha', hm'⟩ => ?_
    subst ha' hm'
    have hWordsBase : 100 * d < 2 ^ w ∧
        4 * PParam ParamConfig.default P (depthOf G.m) < 2 ^ w ∧
        depthOf G.m < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w :=
      ⟨h100d_w, h4P_w, hdepth_w, h49_w⟩
    obtain ⟨tail, t, c, hrun, hInv, hcost⟩ := buildTopDriver_from_prepare (w := w) (K := K)
      (advance := k + 28) (h := h) (r := r) (phiNum := phiNum) (phiDen := phiDen)
      (pos := pos') (spaceBound := spaceBound) (p := p) (G := G) (memPrep := s10.mem)
      (space := space) ω' h1 h2 hG hm hcond rfl hGraphAtP hDir0P hPtr0P hTermsP hRowsP hZeroP
      hAdvAll hLvlSp hDrvRoom hWordsBase
    exact ⟨.returned tail, t, c, hrun, hInv, hcost⟩
  -- 13. call driverProc [table, D, heap₀] -> reg 17 = tail0
  have r12_11 : s12.regs 11 = D := (hreg12 11 (by decide)).trans ((hreg11 11 (by decide)).trans r10_11)
  have r12_15 : s12.regs 15 = table := (hreg12 15 (by decide)).trans r11_15
  refine static_seq_call hDrvMC (vs := [table, D, heap₀])
    (by simp [evalArgs, Expr.eval, r12_15, r12_11, r12_16])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact htable_lt_w
      · exact hDw
      · exact hHeap0_w)
    ⟨rfl, hm12'⟩ ?_
  intro tail0 s13 hInvFinal r13_17 hreg13
  -- Extract certified replies, StaticData, Good, SpecRest, and encode length bounds
  obtain ⟨hFrDrv, hZeroDrv, hTailLo, hTailHi, reply, replyAddr, hRepGood, hRepEntries⟩ :=
    buildTopRecInv_final hbpos rfl hInvFinal
  set root := hostGraph cloud G
  set H := buildTopHierarchy x b root reply
  set S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
  obtain ⟨hSGood, hSSpecRest⟩ := buildTopStaticData_good_and_specRest h1 h2 hG hm hmM hdeg hcond ha hRepGood
  obtain ⟨hEncLen, hDirLen⟩ := buildTopStatic_encode_length_le h1 h2 hG hm hmM hcond ha hRepGood
  -- Build BuildTopRepliesInMem for packAll
  have hRepInMem : BuildTopRepliesInMem table D x b reply replyAddr tail0 s13.mem := by
    refine ⟨hTable_le_heap0.trans hTailLo, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hFrDrv (table + 13 * j + 1) (by omega)]
      have hrow := hRowsP j hj 0 (fun _ => 0) (fun _ => ⟨0, []⟩) 1 (by simp [BuildTopDepthInput.scheduleWords])
      simpa [BuildTopDepthInput.scheduleWords, buildTopScheduledDepth] using hrow
    · intro j hj
      rw [hFrDrv (table + 13 * j + 4) (by omega)]
      have hrow := hRowsP j hj 0 (fun _ => 0) (fun _ => ⟨0, []⟩) 4 (by simp [BuildTopDepthInput.scheduleWords])
      simpa [BuildTopDepthInput.scheduleWords, buildTopScheduledDepth] using hrow
    · intro j hj
      rw [hFrDrv (table + 13 * j + 5) (by omega)]
      have hrow := hRowsP j hj 0 (fun _ => 0) (fun _ => ⟨0, []⟩) 5 (by simp [BuildTopDepthInput.scheduleWords])
      simpa [BuildTopDepthInput.scheduleWords, buildTopScheduledDepth] using hrow
    · intro j hj
      have hle : buildTopScheduleReplies table D x j + numGroups x b j ≤ buildTopScheduleEnd table D x := by
        have hd := buildTopSchedule_disjoint (table := table) (n := D) (x := x) (b := b) hj
        exact hd.2.2.2
      exact hle.trans (hEnd_le_heap0.trans hTailLo)
    · intro j hj g hg
      obtain ⟨h1', _, h3', h4'⟩ := hRepEntries j hj g hg
      exact ⟨h1', h4', h3'⟩
  have hRootEnd_r : rootGraph + root.encode.length ≤ r := by
    have hE := graph_encode_length root
    have hmIn : 1 ≤ (G.inside G.verts).length := by rw [inside_verts_length hG]; exact hm
    have hmR : root.m ≤ 12 * G.m := by
      have := hostGraph_m_le (G := G) isCloudExpander_cloud hmIn
      rwa [inside_verts_length hG] at this
    unfold r rootGraph buildTopRootWorkspace buildTopRootGraphAddr buildTopRootOwnersAddr
      buildTopRootLoc portGraphWorkSpace
    omega
  have hOwnEnd_r : ownersAddr + P ≤ r := by
    have hPlt : P < 4 * G.m := hlt4m
    unfold r ownersAddr buildTopRootWorkspace buildTopRootOwnersAddr buildTopRootLoc portGraphWorkSpace
    omega
  have hr_le_tail0 : r ≤ tail0 := hr_lt_table.le.trans ((Nat.le_add_right _ _).trans (hTable_le_heap0.trans hTailLo))
  have hr_lt_t13 : r < table + 13 * D := lt_of_lt_of_le hr_lt_table (Nat.le_add_right _ _)
  have hRootAt13 : GraphAt s13.mem rootGraph root := fun i hi =>
    (hFrDrv (rootGraph + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi rootGraph) (hRootEnd_r.trans hr_lt_t13.le))).trans
      (hGraphAtP i hi)
  have hOwnAt13 : ListAt s13.mem ownersAddr (tabList P (hostOwner G)) := by
    have hP_eq : P = hostSize G := hP_hs
    rw [hP_eq]
    intro i hi
    have hiP : i < P := by simpa [tabList, hP_eq] using hi
    exact (hFrDrv (ownersAddr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hiP ownersAddr) (hOwnEnd_r.trans hr_lt_t13.le))).trans
      (hOwnAtP i hi)
  have hPackSpace : buildTopPackAllSpace S D P twoPowB ≤ 24 * G.m * Γ := by
    unfold buildTopPackAllSpace
    have h1mΓ : 1 ≤ G.m * Γ := Nat.mul_pos hm hΓ1
    have hEL : S.encode.length ≤ G.m * Γ := hEncLen
    have hDL : (D + 1) * P + D * P * twoPowB ≤ G.m * Γ := hDirLen
    have h24 : 24 * G.m * Γ = 24 * (G.m * Γ) := by ring
    rw [h24]
    clear * - h1mΓ hEL hDL
    omega
  have hTailHi' : tail0 ≤ h + 204 * (G.m * Γ) + 4 * B ^ 2 * spaceBound := by
    have hTH : tail0 ≤ heap₀ + D * (P * spaceBound + P) := hTailHi
    have e1 : 200 * G.m * Γ + 4 * (G.m * Γ) = 204 * (G.m * Γ) := by ring
    clear * - hTH hHeap0_le hDrvSpace_le e1
    omega
  have hPackBound : tail0 + buildTopPackAllSpace S D P twoPowB ≤
      h + buildTopStaticSpace K Cs cs a phiNum phiDen G.n G.m M := by
    have h1' : 228 * (G.m * Γ) ≤ 2 ^ 15 * (K + 1) * B ^ 4 := by
      calc 228 * (G.m * Γ)
          ≤ (2 ^ 15 * (K + 1)) * (G.m * Γ) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 ^ 15 * (K + 1)) * B ^ 2 := Nat.mul_le_mul_left _ hmΓ_le_B2
        _ ≤ (2 ^ 15 * (K + 1)) * B ^ 4 := Nat.mul_le_mul_left _ hB2_pow4
    have h2' : 2 ^ 15 * (K + 1) * B ^ 4 ≤ (50000 + 2 ^ 15 * (K + 1)) * B ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    have h3' : 4 * B ^ 2 * spaceBound ≤ 5 * B ^ 2 * spaceBound :=
      Nat.mul_le_mul_right spaceBound (Nat.mul_le_mul_right (B ^ 2) (by decide))
    have e1 : 204 * (G.m * Γ) + 24 * G.m * Γ = 228 * (G.m * Γ) := by ring
    rw [hStaticSp_def]
    clear * - hTailHi' hPackSpace h1' h2' h3' e1
    omega
  have hPackRoom : tail0 + buildTopPackAllSpace S D P twoPowB < 2 ^ w :=
    lt_of_le_of_lt hPackBound hRoomS
  have hTail0_w : tail0 < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hPackRoom
  -- 14. call packProc [table, D, P, twoPowB, x, b, rootGraph, ownersAddr, G.m, tail0, h] -> reg 18
  have hPackC := buildTopPackAll_meetsContract (w := w) (G := G)
    (table := table) (D := D) (x := x) (b := b) (rootGraph := rootGraph) (ownersAddr := ownersAddr)
    (tail0 := tail0) (h := h) (reply := reply) (replyAddr := replyAddr)
    hPackAll hNumConn hLab hIota hFill hSec3 hDir3 hSec4 hDir4 hSec5 hDir5
    hFin hGat hRow hCopy hSpan hRead hSeek hMove
  have r13_reg : ∀ i < 16, s13.regs i = s12.regs i := fun i hi => hreg13 i (by omega)
  have r12_reg : ∀ i < 15, s12.regs i = s10.regs i := fun i hi =>
    (hreg12 i (by omega)).trans (hreg11 i (by omega))
  refine static_seq_call hPackC
    (vs := [table, D, P, twoPowB, x, b, rootGraph, ownersAddr, G.m, tail0, h])
    (by
      have hr4 : s13.regs 4 = h := (r13_reg 4 (by decide)).trans ((r12_reg 4 (by decide)).trans r10_4)
      have hr6 : s13.regs 6 = G.m := (r13_reg 6 (by decide)).trans ((r12_reg 6 (by decide)).trans r10_6)
      have hr7 : s13.regs 7 = x := (r13_reg 7 (by decide)).trans ((r12_reg 7 (by decide)).trans r10_7)
      have hr8 : s13.regs 8 = P := (r13_reg 8 (by decide)).trans ((r12_reg 8 (by decide)).trans r10_8)
      have hr9 : s13.regs 9 = b := (r13_reg 9 (by decide)).trans ((r12_reg 9 (by decide)).trans r10_9)
      have hr10 : s13.regs 10 = twoPowB := (r13_reg 10 (by decide)).trans ((r12_reg 10 (by decide)).trans r10_10)
      have hr11 : s13.regs 11 = D := (r13_reg 11 (by decide)).trans r12_11
      have hr12 : s13.regs 12 = ownersAddr := (r13_reg 12 (by decide)).trans ((r12_reg 12 (by decide)).trans r10_12)
      have hr13 : s13.regs 13 = rootGraph := (r13_reg 13 (by decide)).trans ((r12_reg 13 (by decide)).trans r10_13)
      have hr15 : s13.regs 15 = table := (r13_reg 15 (by decide)).trans r12_15
      simp [evalArgs, Expr.eval, hr4, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr15, r13_17])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact htable_lt_w
      · exact hDw
      · exact hPw
      · exact h2Bw
      · exact hxw
      · exact hbw
      · exact hrootG_w
      · exact hown_w
      · exact lt_of_le_of_lt (by omega) h8m_w
      · exact hTail0_w
      · exact hwords _ (by simp))
    ⟨rfl, hG, hm, hxpos, hbpos, hbx, rfl, hD1, hP_hs, hSGood.valid,
      (Nat.le_add_right _ _).trans hr_le_tail0, hRepInMem, hRootAt13, hRootEnd_r.trans hr_le_tail0,
      hOwnAt13, hOwnEnd_r.trans hr_le_tail0, hZeroDrv, hPackRoom, h13w, h2Pw⟩ ?_
  intro vFin s14 ⟨hV_lo, hV_hi, hSO, hZeroFin, hFrFin⟩ r14_18 _
  -- 15. ret reg 18
  refine runs_ret_le (v := vFin) (Expr.eval_reg_of_eq r14_18) ?_ ?_
  · have hh_lt_t13 : h < table + 13 * D := lt_of_le_of_lt (Nat.le_add_right _ _) hr_lt_t13
    have hBelowH : ∀ y < h, s14.mem y = mem y := fun y hy =>
      (hFrFin y hy).trans ((hFrDrv y (lt_trans hy hh_lt_t13)).trans (hFrameP' y hy))
    have hV_le_sp : vFin ≤ h + buildTopStaticSpace K Cs cs a phiNum phiDen G.n G.m M :=
      hV_hi.trans hPackBound
    refine ⟨⟨?_, ?_, ?_, hZeroFin, trivial⟩, gAddr, phiNum, phiDen, M, h, G, S, rfl, hGat0, hSO,
      hV_lo, hSGood, hSSpecRest⟩
    · show h ≤ vFin; exact (Nat.le_add_right h _).trans hV_lo
    · show vFin ≤ h + buildTopStaticSpace K Cs cs a phiNum phiDen (readGraph mem gAddr).n
        (readGraph mem gAddr).m M
      rw [hRG]; exact hV_le_sp
    · intro y hy
      exact hBelowH y hy
  · -- Total cost bound ≤ 2 ^ 20 * (K + 1) * G.m * Γ
    have hPrepCostH := hPrepCost h
    have h1mΓ : 1 ≤ G.m * Γ := Nat.mul_pos hm hΓ1
    have hPackCost : 120 * S.encode.length +
        1000 * ((D + 1) * P + D * P * twoPowB) + 2000 ≤
        3120 * (G.m * Γ) := by
      have hEL : S.encode.length ≤ G.m * Γ := hEncLen
      have hDL : (D + 1) * P + D * P * twoPowB ≤ G.m * Γ := hDirLen
      clear * - hEL hDL h1mΓ; omega
    have hBudget : 20000 * G.m * Γ + 2 ^ 14 * (K + 1) * G.m * Γ +
        3120 * (G.m * Γ) + 500 * (G.m * Γ) ≤
        2 ^ 20 * (K + 1) * G.m * Γ := by
      have hcoef : 20000 + 2 ^ 14 * (K + 1) + 3120 + 500 ≤
          2 ^ 20 * (K + 1) := by clear * -; omega
      calc 20000 * G.m * Γ + 2 ^ 14 * (K + 1) * G.m * Γ +
            3120 * (G.m * Γ) + 500 * (G.m * Γ)
          = (20000 + 2 ^ 14 * (K + 1) + 3120 + 500) * (G.m * Γ) := by ring
        _ ≤ (2 ^ 20 * (K + 1)) * (G.m * Γ) := Nat.mul_le_mul_right _ hcoef
        _ = 2 ^ 20 * (K + 1) * G.m * Γ := by ring
    have hPrepCostEq :
        (buildTopPrepareCompactContract w gAddr h x b D phiNum phiDen G).cost
          [gAddr, h, P, rootGraph, D, x, b, G.m, phiNum, phiDen] s9.mem =
        (buildTopPrepareCompactContract 0 0 h x b D phiNum phiDen G).cost [] (fun _ => 0) := by
      simp [buildTopPrepareCompactContract, buildTopRootSeededCompactContract,
        buildTopRootLayoutCompactContract, buildTopRootCompactContract,
        buildTopPortCompactWrapContract, buildTopPlayerSetupContract]
    have hPrepCost' :
        (buildTopPrepareCompactContract w gAddr h x b D phiNum phiDen G).cost
          [gAddr, h, P, rootGraph, D, x, b, G.m, phiNum, phiDen] s9.mem +
          (30 * G.m + 30) + (13 * (Nat.log 2 (8 * G.m + 7) + 1) + 19 * depthOf G.m + 120) ≤
        20000 * G.m * Γ := by
      rw [hPrepCostEq]; exact hPrepCostH
    have hDrvCost' : drvC.cost [table, D, heap₀] s12.mem ≤ 2 ^ 14 * (K + 1) * G.m * Γ := hDrvSum
    have hPackCost' :
        (buildTopPackAllContract w table D x b rootGraph ownersAddr tail0 h G reply replyAddr).cost
          [table, D, P, twoPowB, x, b, rootGraph, ownersAddr, G.m, tail0, h] s13.mem ≤
        3120 * (G.m * Γ) := hPackCost
    have hTargetEq : (StaticContract w a (2 ^ 20 * (K + 1)) hc.params
        (buildTopStaticSpace K Cs cs a)).cost [gAddr, phiNum, phiDen, M, h] mem =
        2 ^ 20 * (K + 1) * G.m * Γ := by
      simp only [StaticContract, heapContract, List.getD_cons_zero, List.getD_cons_succ, hRG]
      rfl
    rw [hTargetEq]
    simp only [Expr.size, argsSize, buildTopRepliesExpr, buildTopPointerExpr]
    clear * - hPrepCost' hDrvCost' hPackCost' hBudget h1mΓ
    omega

end MinCostFlow.HierPaths

end
