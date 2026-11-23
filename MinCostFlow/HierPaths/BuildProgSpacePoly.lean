module

public import MinCostFlow.HierPaths.BuildProgGameBudgetBase
public import MinCostFlow.HierPaths.BuildCoreBridge
public import MinCostFlow.HierPaths.BuildTopRecBase
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Space envelope of `buildLevelSpace` with `coreBridgeSpace`

Proves three results about instantiating `buildLevelSpace` with the core bridge's
space function `coreBridgeSpace C_sp`:

1. **`coreBridgeSpace_exceeds_buildLevelCost`**: for every constant `K`
   and `C_sp ≥ 1`, there exist valid level parameters with `r = 1 ≤ ell M` where
   `buildLevelCost K ... < coreBridgeSpace C_sp M 1 2`. Thus a bump-allocating core
   cannot maintain `v ≤ h + buildLevelCost` in `buildLevelContract.post` without
   exceeding `buildLevelCost` time. This is why `BuildProgLevelSpec`, `BuildTop*` and
   `InitProg*` use the bump-heap form of the post.
2. **`coreBridgeSpace_not_poly_at_ell`**: for every `(Cs, cs)`, there
   exist `M = 2 ^ m` and `r = m + 1 ≤ ell M` where
   `Cs * (G.n + G.m + s + k + M + r + Δ + L + L' + bh + 2) ^ cs < buildLevelSpace sR (coreBridgeSpace 1) ...`,
   because `WParam M ^ (10 * r ^ 2 + 10) ≥ 2 ^ (10 * (m + 1) ^ 2)` is quasipolynomial in `M`.
   This is why `BuildLevelSpacePoly` has `r ≤ ell M` and the factor
   `WParam ParamConfig.default M ^ (10 * r ^ 2 + 10)`, which `gammaHP` in `BuildTopStaticSetup`
   absorbs.
3. **`buildLevelSpace_poly_coreBridge`**: for any router with polynomial space `sR`,
   `buildLevelSpace sR (coreBridgeSpace C_sp)` satisfies `BuildLevelSpacePoly`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-! ### Elementary `NOf` bounds under `r ≤ ell M` -/

lemma two_pow_ell_le (M : ℕ) : 2 ^ ell M ≤ 4 * M + 4 := by
  unfold ell
  have hpos : 0 < Nat.clog 2 (2 * M + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  have hlt : 2 ^ (Nat.clog 2 (2 * M + 2) - 1) < 2 * M + 2 :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega)
  have heq : 2 ^ Nat.clog 2 (2 * M + 2) = 2 * 2 ^ (Nat.clog 2 (2 * M + 2) - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  omega

lemma NOf_le_of_le_ell {M r : ℕ} (_hr : r ≤ ell M) : NOf M r ≤ 4 * M + 4 := by
  unfold NOf
  by_cases hM : M = 0
  · subst hM
    have hell0 : ell 0 = 1 := by decide
    have hcd : ceilDiv (ell 0) r ≤ 1 := by
      rw [hell0]
      rcases r with _ | r
      · simp [ceilDiv]
      · unfold ceilDiv; exact Nat.div_le_of_le_mul (by omega)
    have hmax : max 2 (ceilDiv (ell 0) r) = 2 := max_eq_left (by omega)
    rw [hmax]; decide
  · have hell2 : 2 ≤ ell M := by
      unfold ell
      have hlt : 1 < Nat.clog 2 (2 * M + 2) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
      omega
    have hcd : ceilDiv (ell M) r ≤ ell M := by
      rcases r with _ | r
      · simp [ceilDiv]
      · unfold ceilDiv
        apply Nat.div_le_of_le_mul
        have hsub : ell M + (r + 1) - 1 = ell M + r := by omega
        rw [hsub, Nat.succ_mul]
        have : r ≤ r * ell M := Nat.le_mul_of_pos_right r (by omega)
        omega
    have hmax : max 2 (ceilDiv (ell M) r) ≤ ell M := max_le hell2 hcd
    exact (Nat.pow_le_pow_right (by decide) hmax).trans (two_pow_ell_le M)

lemma NOf_pow_r_le_of_le_ell {M r : ℕ} (hr : r ≤ ell M) :
    (NOf M r) ^ r ≤ (4 * M + 4) ^ 2 := by
  rcases r with _ | r'
  · simp; exact Nat.one_le_pow 2 (4 * M + 4) (by omega)
  · unfold NOf
    rw [← pow_mul]
    have hcd : ceilDiv (ell M) (r' + 1) * (r' + 1) ≤ 2 * ell M := by
      unfold ceilDiv
      have hdiv := Nat.div_mul_le_self (ell M + (r' + 1) - 1) (r' + 1)
      omega
    have hmax : max 2 (ceilDiv (ell M) (r' + 1)) * (r' + 1) ≤ 2 * ell M := by
      rcases le_total 2 (ceilDiv (ell M) (r' + 1)) with h | h
      · rw [max_eq_right h]; exact hcd
      · rw [max_eq_left h]; omega
    calc 2 ^ (max 2 (ceilDiv (ell M) (r' + 1)) * (r' + 1))
        ≤ 2 ^ (2 * ell M) := Nat.pow_le_pow_right (by decide) hmax
      _ = (2 ^ ell M) ^ 2 := by rw [Nat.mul_comm, pow_mul]
      _ ≤ (4 * M + 4) ^ 2 := Nat.pow_le_pow_left (two_pow_ell_le M) 2

/-! ### Two lower bounds on `coreBridgeSpace` -/

/-- **The core bridge space exceeds the level cost.** `coreBridgeSpace C_sp M 1 2` grows like
`Ω(M^5 * N^3 * W^20)` while
`buildLevelCost K ...` at `r = 1` grows like `O(K * N^2 * W^20)`. Hence for every `K` and
`C_sp ≥ 1`, choosing `M = K + 10000` makes `coreBridgeSpace` strictly exceed `buildLevelCost`. -/
theorem coreBridgeSpace_exceeds_buildLevelCost (K : ℕ) {C_sp : ℕ} (hC : 1 ≤ C_sp) :
    let M := K + 10000
    let G : Graph := ⟨4, []⟩
    buildLevelCost K G 2 2 M 1 4 1 1 2 < coreBridgeSpace C_sp M 1 2 := by
  intro M G
  set N := NOf M 1
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  generalize hW_eq : WParam ParamConfig.default M = W at hW1 ⊢
  have hN_ge : 2 * M + 2 ≤ N := by
    simpa [N, pow_one] using two_mul_add_two_le_NOf_pow (M := M) (r := 1) le_rfl
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hW20_pos : 1 ≤ W ^ 20 := Nat.one_le_pow 20 W hW1
  have hN2_pos : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N (by omega)
  have hBase_ge : 2048 * 4 * N ≤ coreSpaceBase M 1 := by
    unfold coreSpaceBase
    have h1 : 2048 * 4 * N ≤ 2048 * LParam M * N ^ 1 + 3 := by
      simp only [pow_one]
      have : 2048 * 4 ≤ 2048 * LParam M := Nat.mul_le_mul_left 2048 hL4
      nlinarith
    exact h1.trans (Nat.le_self_pow (by decide) _)
  have hSp_ge : 8192 * N * (N ^ 3 * W ^ 20) ≤ coreBridgeSpace C_sp M 1 2 := by
    unfold coreBridgeSpace coreAdapterSpace
    rw [hW_eq]
    change 8192 * N * (N ^ 3 * W ^ 20) ≤
      6 + 3 * N ^ 1 + 2 * N ^ 2 +
        C_sp * (coreSpaceBase M 1 * (N ^ 3 * W ^ 20 + 1) + (N ^ 1 + 3) ^ 5 + 1) + 40
    have h1 : 8192 * N * (N ^ 3 * W ^ 20) ≤
        coreSpaceBase M 1 * (N ^ 3 * W ^ 20 + 1) := by
      calc 8192 * N * (N ^ 3 * W ^ 20)
          ≤ coreSpaceBase M 1 * (N ^ 3 * W ^ 20) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ coreSpaceBase M 1 * (N ^ 3 * W ^ 20 + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
    have h2 : coreSpaceBase M 1 * (N ^ 3 * W ^ 20 + 1) ≤
        C_sp * (coreSpaceBase M 1 * (N ^ 3 * W ^ 20 + 1) + (N ^ 1 + 3) ^ 5 + 1) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ hC)
    omega
  -- Upper bound on buildLevelCost at (s=2, k=2, r=1, Δ=4, L=1, L'=1, bh=2, G=⟨4,[]⟩)
  have hCost_le : buildLevelCost K G 2 2 M 1 4 1 1 2 ≤ K * (204 * N ^ 2 * W ^ 20 + 10 ^ 13) := by
    have hT : buildLevelDegree 1 = 51 := by decide
    have hd : routePathLen 4 2 1 = 256 := by decide
    have hR : routeCong 4 2 1 = 32896 := by decide
    have hGm : G.m = 0 := rfl
    unfold buildLevelCost
    rw [hT, hd, hR, hGm, hW_eq]
    apply Nat.mul_le_mul_left K
    have hNW : 51 * (2 * 2) * (N ^ 2 * W ^ 20 + 51 + 1) =
        204 * N ^ 2 * W ^ 20 + 10608 := by ring
    change 51 * (2 * 2) * (N ^ 2 * W ^ (10 * 1 ^ 2 + 10) + 51 + 1) +
        (51 * 2 + 2 * 2 + 1) * (2 * 2 + 0 + 1) * (256 + 1) * (32896 + 1) + 2 * 2 + 1 ≤ _
    rw [show 10 * 1 ^ 2 + 10 = 20 by decide, hNW]
    have hCst : 10608 + (51 * 2 + 2 * 2 + 1) * (2 * 2 + 0 + 1) * (256 + 1) * (32896 + 1) + 2 * 2 + 1 ≤
        10 ^ 13 := by norm_num
    clear * - hCst; omega
  have hK_lt_N : K + 10000 < N := by omega
  have h1 : K * (204 * N ^ 2 * W ^ 20) < 204 * N ^ 3 * W ^ 20 := by
    have : K * (204 * N ^ 2 * W ^ 20) < N * (204 * N ^ 2 * W ^ 20) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    calc K * (204 * N ^ 2 * W ^ 20) < N * (204 * N ^ 2 * W ^ 20) := this
      _ = 204 * N ^ 3 * W ^ 20 := by ring
  have h2 : K * 10 ^ 13 < 1000 * N ^ 4 * W ^ 20 := by
    have hN10 : 20000 ≤ N := le_trans (show 20000 ≤ 2 * (K + 10000) + 2 by clear * -; omega) hN_ge
    have hN3_ge : 10 ^ 12 ≤ N ^ 3 := by
      calc 10 ^ 12 = (10 ^ 4) ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left (le_trans (by norm_num) hN10) 3
    have hKN : K < N := lt_of_lt_of_le (show K < 2 * (K + 10000) + 2 by clear * -; omega) hN_ge
    calc K * 10 ^ 13 < N * 10 ^ 13 := Nat.mul_lt_mul_of_pos_right hKN (by norm_num)
      _ = 10 * (N * 10 ^ 12) := by ring
      _ ≤ 10 * (N * N ^ 3) := Nat.mul_le_mul_left 10 (Nat.mul_le_mul_left N hN3_ge)
      _ = 10 * N ^ 4 := by ring
      _ ≤ 1000 * N ^ 4 * W ^ 20 := by
          have : 10 * N ^ 4 ≤ 1000 * N ^ 4 := Nat.mul_le_mul_right _ (by decide)
          exact this.trans (Nat.le_mul_of_pos_right _ hW20_pos)
  have h3 : 204 * N ^ 3 * W ^ 20 + 1000 * N ^ 4 * W ^ 20 ≤ 8192 * N * (N ^ 3 * W ^ 20) := by
    have hN1 : 1 ≤ N := by clear * - hN_ge; omega
    have hA : 204 * N ^ 3 * W ^ 20 ≤ 204 * N ^ 4 * W ^ 20 := by
      have : N ^ 3 ≤ N ^ 4 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hN1
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
    calc 204 * N ^ 3 * W ^ 20 + 1000 * N ^ 4 * W ^ 20
        ≤ 204 * N ^ 4 * W ^ 20 + 1000 * N ^ 4 * W ^ 20 := Nat.add_le_add_right hA _
      _ = 1204 * (N ^ 4 * W ^ 20) := by ring
      _ ≤ 8192 * (N ^ 4 * W ^ 20) := Nat.mul_le_mul_right _ (by decide)
      _ = 8192 * N * (N ^ 3 * W ^ 20) := by ring
  rw [Nat.mul_add] at hCost_le
  clear * - hCost_le h1 h2 h3 hSp_ge
  omega

/-- **The core bridge space is not polynomial.** Even under `r ≤ ell M`, `coreBridgeSpace 1 M r 0`
(and hence
`buildLevelSpace sR (coreBridgeSpace 1)`) is quasipolynomial (`2^{Ω((log M)^2)}`), not
polynomial in `G.n + G.m + s + k + M + r + Δ + L + L' + bh + 2`. -/
theorem coreBridgeSpace_not_poly_at_ell (Cs cs : ℕ) (sR : ℕ → ℕ → ℕ → ℕ → ℕ) :
    ∃ (G : Graph) (s k M r Δ L L' bh : ℕ), r ≤ ell M ∧
      Cs * (G.n + G.m + s + k + M + r + Δ + L + L' + bh + 2) ^ cs <
        buildLevelSpace sR (coreBridgeSpace 1) G s k M r Δ L L' bh := by
  let m := Cs + cs + 10
  let M := 2 ^ m
  let r := m + 1
  let G : Graph := ⟨0, []⟩
  refine ⟨G, 1, 1, M, r, 1, 1, 1, 1, (ell_two_pow m).1, ?_⟩
  have hW2 : 2 ≤ WParam ParamConfig.default M := by
    unfold WParam LParam
    have hL4 := four_le_LParam M
    unfold LParam at hL4
    omega
  have hW_pow : 2 ^ (10 * r ^ 2 + 10) ≤ (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
    Nat.pow_le_pow_left hW2 _
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hBase1 : 1 ≤ coreSpaceBase M r := by
    unfold coreSpaceBase
    exact Nat.one_le_pow _ _ (by omega)
  have hCore_ge : 2 ^ (10 * r ^ 2 + 10) ≤ coreBridgeSpace 1 M r 0 := by
    unfold coreBridgeSpace coreAdapterSpace
    have h1 : (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) ≤
        (NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos hN1)
    have h2 : (NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 1 ≤
        coreSpaceBase M r *
          ((NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 1) :=
      Nat.le_mul_of_pos_left _ hBase1
    omega
  have hLvl_ge : coreBridgeSpace 1 M r 0 ≤
      buildLevelSpace sR (coreBridgeSpace 1) G 1 1 M r 1 1 1 1 := by
    have hMax : coreBridgeSpace 1 M r 0 ≤ maxCoreSpace (coreBridgeSpace 1 M r) (2 + buildLevelDegree 1 * 1) := by
      unfold maxCoreSpace
      exact Finset.le_sup (f := coreBridgeSpace 1 M r) (Finset.mem_range.mpr (by decide))
    unfold buildLevelSpace
    exact le_trans (by omega) (le_max_right _ _)
  have hSum_le : G.n + G.m + 1 + 1 + M + r + 1 + 1 + 1 + 1 + 2 ≤ 2 ^ (m + 2) := by
    have hGm : G.m = 0 := rfl
    have hGn : G.n = 0 := rfl
    have hm_le : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
    have h2m : 1024 ≤ 2 ^ m := by
      calc 1024 = 2 ^ 10 := by decide
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
    dsimp only [M, r]
    omega
  have hCs_le : Cs ≤ 2 ^ m := (show Cs ≤ m by omega).trans Nat.lt_two_pow_self.le
  have hLHS : Cs * (G.n + G.m + 1 + 1 + M + r + 1 + 1 + 1 + 1 + 2) ^ cs ≤
      2 ^ (m + (m + 2) * cs) := by
    calc Cs * (G.n + G.m + 1 + 1 + M + r + 1 + 1 + 1 + 1 + 2) ^ cs
        ≤ 2 ^ m * (2 ^ (m + 2)) ^ cs := Nat.mul_le_mul hCs_le (Nat.pow_le_pow_left hSum_le cs)
      _ = 2 ^ m * 2 ^ ((m + 2) * cs) := by rw [← pow_mul]
      _ = 2 ^ (m + (m + 2) * cs) := (pow_add ..).symm
  have hExp_lt : m + (m + 2) * cs < 10 * r ^ 2 + 10 := by
    have hcs_le : cs ≤ m := by omega
    have hr_eq : r = m + 1 := rfl
    have hmul : (m + 2) * cs ≤ (m + 2) * m := Nat.mul_le_mul_left _ hcs_le
    nlinarith
  have hPow_lt : 2 ^ (m + (m + 2) * cs) < 2 ^ (10 * r ^ 2 + 10) :=
    Nat.pow_lt_pow_right (by decide) hExp_lt
  exact lt_of_le_of_lt hLHS (lt_of_lt_of_le hPow_lt (hCore_ge.trans hLvl_ge))

/-! ### Positive theorem: `buildLevelSpace` with `coreBridgeSpace` satisfies `BuildLevelSpacePoly` -/

/-- Upper bound on `coreBridgeSpace C_sp M r gLen` under `r ≤ ell M` in terms of `B`. -/
lemma coreBridgeSpace_le_poly {C_sp M r gLen B : ℕ}
    (hr : r ≤ ell M) (hMB : M + 2 ≤ B)
    (hWB : (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) ≤ B) :
    coreBridgeSpace C_sp M r gLen ≤ (C_sp + 1) * 2 ^ 110 * B ^ 20 := by
  have hB1 : 1 ≤ B := by omega
  have hN_le : NOf M r ≤ 4 * B := (NOf_le_of_le_ell hr).trans (by omega)
  have hNr_le : (NOf M r) ^ r ≤ 16 * B ^ 2 := by
    calc (NOf M r) ^ r ≤ (4 * M + 4) ^ 2 := NOf_pow_r_le_of_le_ell hr
      _ ≤ (4 * B) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 16 * B ^ 2 := by ring
  have hNr1_le : (NOf M r) ^ (r + 1) ≤ 64 * B ^ 3 := by
    rw [pow_succ]
    calc (NOf M r) ^ r * NOf M r ≤ (16 * B ^ 2) * (4 * B) := Nat.mul_le_mul hNr_le hN_le
      _ = 64 * B ^ 3 := by ring
  have hNr2_le : (NOf M r) ^ (r + 2) ≤ 256 * B ^ 4 := by
    rw [pow_succ]
    calc (NOf M r) ^ (r + 1) * NOf M r ≤ (64 * B ^ 3) * (4 * B) := Nat.mul_le_mul hNr1_le hN_le
      _ = 256 * B ^ 4 := by ring
  have hL_le : LParam M ≤ 16 * B := by
    unfold LParam
    have he := (Nat.lt_two_pow_self (n := ell M)).le.trans (two_pow_ell_le M)
    omega
  have hBase_le : coreSpaceBase M r ≤ 2 ^ 100 * B ^ 15 := by
    unfold coreSpaceBase
    have hIn : 2048 * LParam M * (NOf M r) ^ r + 3 ≤ 2 ^ 20 * B ^ 3 := by
      have h1 : 2048 * LParam M * (NOf M r) ^ r ≤ 2048 * (16 * B) * (16 * B ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2048 hL_le) hNr_le
      have h2 : 2048 * (16 * B) * (16 * B ^ 2) = 2 ^ 19 * B ^ 3 := by ring
      have hB3 : 1 ≤ B ^ 3 := Nat.one_le_pow 3 B hB1
      have h3 : 2 ^ 20 * B ^ 3 = 2 ^ 19 * B ^ 3 + 2 ^ 19 * B ^ 3 := by ring
      omega
    calc (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5
        ≤ (2 ^ 20 * B ^ 3) ^ 5 := Nat.pow_le_pow_left hIn 5
      _ = 2 ^ 100 * B ^ 15 := by ring
  have hCC_le : (NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 1 ≤
      2 ^ 9 * B ^ 5 := by
    have h1 : (NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) ≤
        256 * B ^ 4 * B := Nat.mul_le_mul hNr2_le hWB
    have h2 : 256 * B ^ 4 * B = 256 * B ^ 5 := by ring
    have hB5 : 1 ≤ B ^ 5 := Nat.one_le_pow 5 B hB1
    omega
  have hPow5_le : ((NOf M r) ^ r + 3) ^ 5 ≤ 2 ^ 25 * B ^ 20 := by
    have hB2 : 1 ≤ B ^ 2 := Nat.one_le_pow 2 B hB1
    have hIn : (NOf M r) ^ r + 3 ≤ 32 * B ^ 2 := by omega
    have hB10 : B ^ 10 ≤ B ^ 20 := Nat.pow_le_pow_right hB1 (by decide)
    calc ((NOf M r) ^ r + 3) ^ 5
        ≤ (32 * B ^ 2) ^ 5 := Nat.pow_le_pow_left hIn 5
      _ = 2 ^ 25 * B ^ 10 := by ring
      _ ≤ 2 ^ 25 * B ^ 20 := Nat.mul_le_mul_left _ hB10
  have hAd_le : coreAdapterSpace C_sp M r ((NOf M r) ^ r)
      ((NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)) ≤
      C_sp * (2 ^ 110 * B ^ 20) := by
    unfold coreAdapterSpace
    apply Nat.mul_le_mul_left C_sp
    have hMul : coreSpaceBase M r *
        ((NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 1) ≤
        2 ^ 109 * B ^ 20 := by
      calc _ ≤ (2 ^ 100 * B ^ 15) * (2 ^ 9 * B ^ 5) := Nat.mul_le_mul hBase_le hCC_le
        _ = 2 ^ 109 * B ^ 20 := by ring
    have hB20 : 1 ≤ B ^ 20 := Nat.one_le_pow 20 B hB1
    have h210 : 2 ^ 110 * B ^ 20 = 2 ^ 109 * B ^ 20 + 2 ^ 109 * B ^ 20 := by ring
    omega
  have hPre_le : 6 + 3 * (NOf M r) ^ r + 2 * (NOf M r) ^ (r + 1) + 40 ≤ 2 ^ 110 * B ^ 20 := by
    have hB2 : B ^ 2 ≤ B ^ 20 := Nat.pow_le_pow_right hB1 (by decide)
    have hB3 : B ^ 3 ≤ B ^ 20 := Nat.pow_le_pow_right hB1 (by decide)
    have hB20 : 1 ≤ B ^ 20 := Nat.one_le_pow 20 B hB1
    have h1 : 3 * (NOf M r) ^ r ≤ 48 * B ^ 20 := by
      calc 3 * (NOf M r) ^ r ≤ 3 * (16 * B ^ 2) := Nat.mul_le_mul_left 3 hNr_le
        _ = 48 * B ^ 2 := by ring
        _ ≤ 48 * B ^ 20 := Nat.mul_le_mul_left 48 hB2
    have h2 : 2 * (NOf M r) ^ (r + 1) ≤ 128 * B ^ 20 := by
      calc 2 * (NOf M r) ^ (r + 1) ≤ 2 * (64 * B ^ 3) := Nat.mul_le_mul_left 2 hNr1_le
        _ = 128 * B ^ 3 := by ring
        _ ≤ 128 * B ^ 20 := Nat.mul_le_mul_left 128 hB3
    omega
  unfold coreBridgeSpace
  have hEq : (C_sp + 1) * 2 ^ 110 * B ^ 20 = C_sp * (2 ^ 110 * B ^ 20) + 2 ^ 110 * B ^ 20 := by ring
  omega

/-- Helper bounding `buildLevelSpace` given an abstract base `B` and core-space cap `coreMax`. -/
private lemma buildLevelSpace_le_of_caps
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {sC : ℕ → ℕ → ℕ → ℕ} {Cr cr C_sp B : ℕ}
    {G : Graph} {s k M r Δ L L' bh : ℕ}
    (hsR : ∀ n gLen pLen par, sR n gLen pLen par ≤ Cr * (n + gLen + pLen + par + 2) ^ cr)
    (hCore : ∀ gLen, sC M r gLen ≤ (C_sp + 1) * 2 ^ 110 * B ^ 20)
    (hN : NOf M r ≤ 4 * B)
    (hB : G.n + G.m + s + k + M + r + Δ + L + L' + bh + 2 ≤ B) :
    buildLevelSpace sR sC G s k M r Δ L L' bh ≤
      ((C_sp + 1) * 2 ^ 120 + (Cr + 1) * 8 ^ cr * 2 ^ 14) * B ^ max 24 (2 * cr + 4) := by
  set E := max 24 (2 * cr + 4)
  have hB2ge : 2 ≤ B := by omega
  have hB1 : 1 ≤ B := by omega
  have hB_pow (a : ℕ) (ha : a ≤ E) : B ^ a ≤ B ^ E := Nat.pow_le_pow_right hB1 ha
  have hMaxCore : ∀ sw, maxCoreSpace (sC M r) sw ≤ (C_sp + 1) * 2 ^ 110 * B ^ 20 := fun sw => by
    unfold maxCoreSpace
    exact Finset.sup_le fun g _ => hCore g
  have hT_le : buildLevelDegree L' ≤ 50 * B := by unfold buildLevelDegree; omega
  have hd_le : routePathLen Δ bh L ≤ 32 * B ^ 3 := by
    unfold routePathLen
    have h1 : Δ * bh * L ≤ B * B * B :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    calc 32 * Δ * bh * L = 32 * (Δ * bh * L) := by ring
      _ ≤ 32 * (B * B * B) := Nat.mul_le_mul_left 32 h1
      _ = 32 * B ^ 3 := by ring
  have hGLen_le : G.encode.length ≤ 2 * B := by
    have := graph_encode_length G; omega
  have hSw_le : 2 + buildLevelDegree L' * s ≤ 52 * B ^ 2 := by
    have h1 : buildLevelDegree L' * s ≤ 50 * B * B := Nat.mul_le_mul hT_le (by omega)
    have hB2 : 1 ≤ B ^ 2 := Nat.one_le_pow 2 B hB1
    have hEq : 50 * B * B = 50 * B ^ 2 := by ring
    clear * - h1 hB2 hEq; omega
  have hMaxPLen_le : 2 * k + 1 + k * s ≤ 4 * B ^ 2 := by
    have h1 : k * s ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
    have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
    have hEq : B * B = B ^ 2 := by ring
    have hkB : k + 1 ≤ B := by omega
    clear * - h1 hB2 hEq hkB; omega
  have hRoute_le : ∀ pLen parCap, pLen ≤ 4 * B ^ 2 → parCap ≤ Δ + L + B ^ 2 →
      routerSpaceUpTo sR G.n G.encode.length pLen parCap ≤ Cr * 8 ^ cr * B ^ (2 * cr) := by
    intro pLen parCap hpLen hparCap
    unfold routerSpaceUpTo
    refine Finset.sup_le fun par hpar => ?_
    have hparLe : par ≤ parCap := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpar)
    have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
    have hGnΔL2 : G.n + Δ + L + 2 ≤ B := by omega
    have hIn : G.n + G.encode.length + pLen + par + 2 ≤ 8 * B ^ 2 := by
      clear * - hGnΔL2 hGLen_le hpLen hparCap hparLe hB2; omega
    calc sR G.n G.encode.length pLen par
        ≤ Cr * (G.n + G.encode.length + pLen + par + 2) ^ cr := hsR _ _ _ _
      _ ≤ Cr * (8 * B ^ 2) ^ cr := Nat.mul_le_mul_left Cr (Nat.pow_le_pow_left hIn cr)
      _ = Cr * (8 ^ cr * (B ^ 2) ^ cr) := by rw [Nat.mul_pow]
      _ = Cr * 8 ^ cr * B ^ (2 * cr) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  have hParCap_le : ∀ s', s' ≤ B → Δ + L + max 2 (s' * k) ≤ Δ + L + B ^ 2 := by
    intro s' hs'
    have h1 : s' * k ≤ B ^ 2 := by
      calc s' * k ≤ B * B := Nat.mul_le_mul hs' (by omega)
        _ = B ^ 2 := by ring
    have h2 : 2 ≤ B ^ 2 := by nlinarith
    omega
  have hMaxRoute : maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
      (Δ + L + max 2 (s * k)) ≤ Cr * 8 ^ cr * B ^ (2 * cr) := by
    unfold maxRouteSpace
    exact Finset.sup_le fun p hp =>
      hRoute_le p _ (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)) hMaxPLen_le)
        (hParCap_le s (by omega))
  have hRouteCap_le :
      (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
        (Δ + L + max 2 (s * k)) ≤ 2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) := by
    have hsk1 : s * k + 1 ≤ 2 * B ^ 2 := by
      have hsk : s * k ≤ B ^ 2 := by
        calc s * k ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
          _ = B ^ 2 := by ring
      have hB2 : 1 ≤ B ^ 2 := Nat.one_le_pow 2 B hB1
      clear * - hsk hB2; omega
    calc (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
          (Δ + L + max 2 (s * k))
        ≤ (2 * B ^ 2) * (Cr * 8 ^ cr * B ^ (2 * cr)) := Nat.mul_le_mul hsk1 hMaxRoute
      _ = 2 * Cr * 8 ^ cr * (B ^ (2 * cr) * B ^ 2) := by ring
      _ = 2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) := by rw [← pow_add]
  have hConn_le : ∀ s', s' ≤ B →
      connAllSpace sR G s' k Δ L (routePathLen Δ bh L) ≤
        2 * Cr * 8 ^ cr * B ^ E + 300 * B ^ 6 := by
    intro s' hs'
    unfold connAllSpace connPairSpace
    have hGnB : G.n ≤ B := by omega
    have hB2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
    have hSR : routerSpaceUpTo sR G.n G.encode.length (3 + 2 * s') (Δ + L + max 2 (s' * k)) ≤
        Cr * 8 ^ cr * B ^ (2 * cr) :=
      hRoute_le (3 + 2 * s') _ (by clear * - hs' hB2 hB2ge; omega) (hParCap_le s' hs')
    have hs'k1 : s' * k + 1 ≤ 2 * B ^ 2 := by
      have hs'k : s' * k ≤ B ^ 2 := by
        calc s' * k ≤ B * B := Nat.mul_le_mul hs' (by omega)
          _ = B ^ 2 := by ring
      have hB2' : 1 ≤ B ^ 2 := Nat.one_le_pow 2 B hB1
      clear * - hs'k hB2'; omega
    have hTermSR : (s' * k + 1) *
        routerSpaceUpTo sR G.n G.encode.length (3 + 2 * s') (Δ + L + max 2 (s' * k)) ≤
        2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) := by
      calc _ ≤ (2 * B ^ 2) * (Cr * 8 ^ cr * B ^ (2 * cr)) := Nat.mul_le_mul hs'k1 hSR
        _ = 2 * Cr * 8 ^ cr * (B ^ (2 * cr) * B ^ 2) := by ring
        _ = 2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) := by rw [← pow_add]
    have hsd : s' * routePathLen Δ bh L ≤ 32 * B ^ 4 := by
      calc s' * routePathLen Δ bh L ≤ B * (32 * B ^ 3) := Nat.mul_le_mul hs' hd_le
        _ = 32 * B ^ 4 := by ring
    have hB14 : B ≤ B ^ 4 := Nat.le_self_pow (by decide) B
    have hB34 : B ^ 3 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by decide)
    have hB4 : 1 ≤ B ^ 4 := Nat.one_le_pow 4 B hB1
    have hPair : 3 + 2 * s' + (s' * k + 1) *
        routerSpaceUpTo sR G.n G.encode.length (3 + 2 * s') (Δ + L + max 2 (s' * k)) +
        22 + 10 * s' + 3 * (s' * routePathLen Δ bh L) + routePathLen Δ bh L + G.n ≤
        2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) + 200 * B ^ 4 := by
      clear * - hs' hGnB hTermSR hsd hd_le hB14 hB34 hB4; omega
    have hkk : k * k ≤ B ^ 2 := by
      calc k * k ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
        _ = B ^ 2 := by ring
    have hkkPair : (k * k) * (3 + 2 * s' + (s' * k + 1) *
        routerSpaceUpTo sR G.n G.encode.length (3 + 2 * s') (Δ + L + max 2 (s' * k)) +
        22 + 10 * s' + 3 * (s' * routePathLen Δ bh L) + routePathLen Δ bh L + G.n) ≤
        2 * Cr * 8 ^ cr * B ^ E + 200 * B ^ 6 := by
      have h1 : (k * k) * _ ≤ B ^ 2 * (2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) + 200 * B ^ 4) :=
        Nat.mul_le_mul hkk hPair
      have h2 : B ^ 2 * (2 * Cr * 8 ^ cr * B ^ (2 * cr + 2) + 200 * B ^ 4) =
          2 * Cr * 8 ^ cr * B ^ (2 * cr + 4) + 200 * B ^ 6 := by
        rw [Nat.mul_add]
        congr 1
        · calc B ^ 2 * (2 * Cr * 8 ^ cr * B ^ (2 * cr + 2))
              = 2 * Cr * 8 ^ cr * (B ^ (2 * cr + 2) * B ^ 2) := by ring
            _ = 2 * Cr * 8 ^ cr * B ^ (2 * cr + 4) := by rw [← pow_add]
        · ring
      have h3 : B ^ (2 * cr + 4) ≤ B ^ E := hB_pow (2 * cr + 4) (le_max_right _ _)
      have h4 : 2 * Cr * 8 ^ cr * B ^ (2 * cr + 4) ≤ 2 * Cr * 8 ^ cr * B ^ E :=
        Nat.mul_le_mul_left _ h3
      clear * - h1 h2 h4; omega
    have hkkIn : k * k * (8 + 3 * s' + s' * routePathLen Δ bh L) ≤ 50 * B ^ 6 := by
      calc k * k * (8 + 3 * s' + s' * routePathLen Δ bh L)
          ≤ B ^ 2 * (50 * B ^ 4) := Nat.mul_le_mul hkk (by clear * - hsd hs' hB14 hB4; omega)
        _ = 50 * B ^ 6 := by ring
    have hB26 : B ^ 2 ≤ B ^ 6 := Nat.pow_le_pow_right hB1 (by decide)
    have hB6 : 1 ≤ B ^ 6 := Nat.one_le_pow 6 B hB1
    clear * - hkkPair hkkIn hkk hB26 hB6; omega
  set RHS := ((C_sp + 1) * 2 ^ 120 + (Cr + 1) * 8 ^ cr * 2 ^ 14) * B ^ E
  have h8cr : 1 ≤ 8 ^ cr := Nat.one_le_pow cr 8 (by decide)
  have hTermR : 2 * Cr * 8 ^ cr * B ^ E + 1000 * B ^ 6 ≤ (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E := by
    have hB6 : B ^ 6 ≤ B ^ E := hB_pow 6 (le_trans (by decide) (le_max_left _ _))
    have h1 : 1000 * B ^ 6 ≤ 1000 * B ^ E := Nat.mul_le_mul_left 1000 hB6
    have h2 : 2 * Cr * 8 ^ cr * B ^ E + 1000 * B ^ E ≤ (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E := by
      have hc : 2 * (Cr * 8 ^ cr) + 1000 ≤ (Cr + 1) * 8 ^ cr * 2 ^ 14 := by nlinarith
      calc 2 * Cr * 8 ^ cr * B ^ E + 1000 * B ^ E
          = (2 * (Cr * 8 ^ cr) + 1000) * B ^ E := by ring
        _ ≤ ((Cr + 1) * 8 ^ cr * 2 ^ 14) * B ^ E := Nat.mul_le_mul_right _ hc
    clear * - h1 h2; omega
  unfold buildLevelSpace
  refine max_le ?_ ?_
  · dsimp only [singletonSpace]
    have hConn1 := hConn_le 1 hB1
    have hB16 : B ≤ B ^ 6 := Nat.le_self_pow (by decide) B
    have hB6 : 1 ≤ B ^ 6 := Nat.one_le_pow 6 B hB1
    have hRHS_ge : (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E ≤ RHS :=
      Nat.mul_le_mul_right (B ^ E) (Nat.le_add_left _ _)
    have hkG : k + G.n ≤ B := by omega
    clear * - hConn1 hB16 hB6 hTermR hRHS_ge hkG
    omega
  · set T := buildLevelDegree L'
    set d := routePathLen Δ bh L
    set sw := 2 + T * s
    set mpl := 2 * k + 1 + k * s
    set mC := maxCoreSpace (sC M r) sw
    set rCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length mpl (Δ + L + max 2 (s * k))
    have hmC : mC ≤ (C_sp + 1) * 2 ^ 110 * B ^ 20 := hMaxCore sw
    have hrCapE : rCap ≤ 2 * Cr * 8 ^ cr * B ^ E := by
      have h1 : B ^ (2 * cr + 2) ≤ B ^ E := hB_pow (2 * cr + 2) (le_trans (by omega) (le_max_right _ _))
      exact hRouteCap_le.trans (Nat.mul_le_mul_left _ h1)
    have hTrCapE : T * rCap ≤ 100 * Cr * 8 ^ cr * B ^ E := by
      have h1 : T * rCap ≤ (50 * B) * (2 * Cr * 8 ^ cr * B ^ (2 * cr + 2)) :=
        Nat.mul_le_mul hT_le hRouteCap_le
      have h2 : (50 * B) * (2 * Cr * 8 ^ cr * B ^ (2 * cr + 2)) =
          100 * Cr * 8 ^ cr * B ^ (2 * cr + 3) := by
        calc _ = 100 * Cr * 8 ^ cr * (B ^ (2 * cr + 2) * B) := by ring
          _ = 100 * Cr * 8 ^ cr * B ^ (2 * cr + 3) := by rw [← pow_succ]
      have h3 : B ^ (2 * cr + 3) ≤ B ^ E := hB_pow (2 * cr + 3) (le_trans (by omega) (le_max_right _ _))
      have h4 : 100 * Cr * 8 ^ cr * B ^ (2 * cr + 3) ≤ 100 * Cr * 8 ^ cr * B ^ E :=
        Nat.mul_le_mul_left _ h3
      clear * - h1 h2 h4; omega
    have hCoreCap : k * (mC + 3 * s) ≤ (C_sp + 1) * 2 ^ 111 * B ^ 21 := by
      have hB20 : B ≤ B ^ 20 := Nat.le_self_pow (by decide) B
      have hIn : mC + 3 * s ≤ (C_sp + 1) * 2 ^ 111 * B ^ 20 := by
        have h1 : 3 * s ≤ 3 * B ^ 20 := by omega
        have h2 : 1 ≤ C_sp + 1 := Nat.succ_pos C_sp
        have h3 : (C_sp + 1) * 2 ^ 111 * B ^ 20 =
            (C_sp + 1) * 2 ^ 110 * B ^ 20 + (C_sp + 1) * 2 ^ 110 * B ^ 20 := by ring
        have h4 : 3 * B ^ 20 ≤ (C_sp + 1) * 2 ^ 110 * B ^ 20 := by
          apply Nat.mul_le_mul_right
          have : 3 ≤ 1 * 2 ^ 110 := by norm_num
          exact this.trans (Nat.mul_le_mul_right _ h2)
        clear * - hmC h1 h3 h4; omega
      calc k * (mC + 3 * s)
          ≤ B * ((C_sp + 1) * 2 ^ 111 * B ^ 20) := Nat.mul_le_mul (by omega) hIn
        _ = (C_sp + 1) * 2 ^ 111 * B ^ 21 := by ring
    have hRNH : roundNonHoleCap s k d ≤ 250 * B ^ 5 := by
      unfold roundNonHoleCap
      have hsk : s * k ≤ B ^ 2 := by
        calc s * k ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
          _ = B ^ 2 := by ring
      have hskd : s * k * d ≤ 32 * B ^ 5 := by
        calc s * k * d ≤ B ^ 2 * (32 * B ^ 3) := Nat.mul_le_mul hsk hd_le
          _ = 32 * B ^ 5 := by ring
      have hB15 : B ≤ B ^ 5 := Nat.le_self_pow (by decide) B
      have hB25 : B ^ 2 ≤ B ^ 5 := Nat.pow_le_pow_right hB1 (by decide)
      have hB35 : B ^ 3 ≤ B ^ 5 := Nat.pow_le_pow_right hB1 (by decide)
      have hB5 : 1 ≤ B ^ 5 := Nat.one_le_pow 5 B hB1
      have hskB : s + k ≤ B := by omega
      clear * - hsk hskd hd_le hB15 hB25 hB35 hB5 hskB; omega
    have hInjEnd : T + 4 * k + 1 + k * sw + T * (roundNonHoleCap s k d + k * (mC + 3 * s) + G.n) ≤
        (C_sp + 1) * 2 ^ 119 * B ^ 22 := by
      have h1 : k * sw ≤ 52 * B ^ 3 := by
        calc k * sw ≤ B * (52 * B ^ 2) := Nat.mul_le_mul (by omega) hSw_le
          _ = 52 * B ^ 3 := by ring
      have hB21 : B ^ 5 ≤ B ^ 21 := Nat.pow_le_pow_right hB1 (by decide)
      have hB121 : B ≤ B ^ 21 := Nat.le_self_pow (by decide) B
      have hSumIn : roundNonHoleCap s k d + k * (mC + 3 * s) + G.n ≤
          (C_sp + 1) * 2 ^ 112 * B ^ 21 := by
        have h260 : 260 * B ^ 21 ≤ (C_sp + 1) * 2 ^ 111 * B ^ 21 := by
          apply Nat.mul_le_mul_right
          have : 260 ≤ 1 * 2 ^ 111 := by norm_num
          exact this.trans (Nat.mul_le_mul_right _ (Nat.succ_pos C_sp))
        have hSp : (C_sp + 1) * 2 ^ 112 * B ^ 21 =
            (C_sp + 1) * 2 ^ 111 * B ^ 21 + (C_sp + 1) * 2 ^ 111 * B ^ 21 := by ring
        have hRnG : roundNonHoleCap s k d + G.n ≤ 260 * B ^ 21 := by
          have : G.n ≤ B := by omega
          clear * - hRNH hB21 hB121 this; omega
        clear * - hRnG hCoreCap h260 hSp; omega
      have hTMul : T * (roundNonHoleCap s k d + k * (mC + 3 * s) + G.n) ≤
          (C_sp + 1) * 2 ^ 118 * B ^ 22 := by
        calc T * (roundNonHoleCap s k d + k * (mC + 3 * s) + G.n)
            ≤ (50 * B) * ((C_sp + 1) * 2 ^ 112 * B ^ 21) := Nat.mul_le_mul hT_le hSumIn
          _ = (C_sp + 1) * (50 * 2 ^ 112) * B ^ 22 := by ring
          _ ≤ (C_sp + 1) * 2 ^ 118 * B ^ 22 := by
              apply Nat.mul_le_mul_right
              apply Nat.mul_le_mul_left
              norm_num
      have hB122 : B ≤ B ^ 22 := Nat.le_self_pow (by decide) B
      have hB322 : B ^ 3 ≤ B ^ 22 := Nat.pow_le_pow_right hB1 (by decide)
      have hB22 : 1 ≤ B ^ 22 := Nat.one_le_pow 22 B hB1
      have hPre : T + 4 * k + 1 + k * sw ≤ (C_sp + 1) * 2 ^ 118 * B ^ 22 := by
        have hkB : k ≤ B := by omega
        have hP : T + 4 * k + 1 + k * sw ≤ 120 * B ^ 22 := by
          clear * - hT_le hkB h1 hB122 hB322 hB22; omega
        have h120 : 120 * B ^ 22 ≤ (C_sp + 1) * 2 ^ 118 * B ^ 22 := by
          apply Nat.mul_le_mul_right
          have : 120 ≤ 1 * 2 ^ 118 := by norm_num
          exact this.trans (Nat.mul_le_mul_right _ (Nat.succ_pos C_sp))
        exact hP.trans h120
      have hSp : (C_sp + 1) * 2 ^ 119 * B ^ 22 =
          (C_sp + 1) * 2 ^ 118 * B ^ 22 + (C_sp + 1) * 2 ^ 118 * B ^ 22 := by ring
      clear * - hPre hTMul hSp; omega
    have hRestPoly :
        (k + k * (T * s)) + (k + 1 + k * sw) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
        (6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
        NOf M r + d + G.n + 100 ≤ 4000 * B ^ 6 := by
      have hTs : T * s ≤ 50 * B ^ 2 := by
        calc T * s ≤ (50 * B) * B := Nat.mul_le_mul hT_le (by omega)
          _ = 50 * B ^ 2 := by ring
      have hTsd : T * s * d ≤ 1600 * B ^ 5 := by
        calc T * s * d ≤ (50 * B ^ 2) * (32 * B ^ 3) := Nat.mul_le_mul hTs hd_le
          _ = 1600 * B ^ 5 := by ring
      have hkTsd : k * (T * s + 1 + T * s * d) ≤ 1700 * B ^ 6 := by
        have hB25 : B ^ 2 ≤ B ^ 5 := Nat.pow_le_pow_right hB1 (by decide)
        have hB5 : 1 ≤ B ^ 5 := Nat.one_le_pow 5 B hB1
        calc k * (T * s + 1 + T * s * d)
            ≤ B * (1700 * B ^ 5) := Nat.mul_le_mul (by omega) (by clear * - hTs hTsd hB25 hB5; omega)
          _ = 1700 * B ^ 6 := by ring
      have hkTs : k * (T * s) ≤ 50 * B ^ 3 := by
        calc k * (T * s) ≤ B * (50 * B ^ 2) := Nat.mul_le_mul (by omega) hTs
          _ = 50 * B ^ 3 := by ring
      have hkSw : k * sw ≤ 52 * B ^ 3 := by
        calc k * sw ≤ B * (52 * B ^ 2) := Nat.mul_le_mul (by omega) hSw_le
          _ = 52 * B ^ 3 := by ring
      have hsk : s * k ≤ B ^ 2 := by
        calc s * k ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
          _ = B ^ 2 := by ring
      have hB16 : B ≤ B ^ 6 := Nat.le_self_pow (by decide) B
      have hB26 : B ^ 2 ≤ B ^ 6 := Nat.pow_le_pow_right hB1 (by decide)
      have hB36 : B ^ 3 ≤ B ^ 6 := Nat.pow_le_pow_right hB1 (by decide)
      have hB6 : 1 ≤ B ^ 6 := Nat.one_le_pow 6 B hB1
      have hLin : s + k + G.n ≤ B := by omega
      clear * - hT_le hd_le hkTsd hkTs hkSw hsk hN hB16 hB26 hB36 hB6 hLin
      omega
    have hConnS := hConn_le s (by omega)
    have hB20E : B ^ 20 ≤ B ^ E := hB_pow 20 (le_trans (by decide) (le_max_left _ _))
    have hB22E : B ^ 22 ≤ B ^ E := hB_pow 22 (le_trans (by decide) (le_max_left _ _))
    have hB6E : B ^ 6 ≤ B ^ E := hB_pow 6 (le_trans (by decide) (le_max_left _ _))
    have hC1 : (C_sp + 1) * 2 ^ 119 * B ^ 22 + (C_sp + 1) * 2 ^ 110 * B ^ 20 ≤
        (C_sp + 1) * 2 ^ 120 * B ^ E := by
      have hA : (C_sp + 1) * 2 ^ 119 * B ^ 22 ≤ (C_sp + 1) * 2 ^ 119 * B ^ E :=
        Nat.mul_le_mul_left _ hB22E
      have hB' : (C_sp + 1) * 2 ^ 110 * B ^ 20 ≤ (C_sp + 1) * 2 ^ 119 * B ^ E := by
        calc (C_sp + 1) * 2 ^ 110 * B ^ 20
            ≤ (C_sp + 1) * 2 ^ 119 * B ^ 20 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by norm_num))
          _ ≤ (C_sp + 1) * 2 ^ 119 * B ^ E := Nat.mul_le_mul_left _ hB20E
      have hSp : (C_sp + 1) * 2 ^ 120 * B ^ E =
          (C_sp + 1) * 2 ^ 119 * B ^ E + (C_sp + 1) * 2 ^ 119 * B ^ E := by ring
      clear * - hA hB' hSp; omega
    have hC2 : 100 * Cr * 8 ^ cr * B ^ E + 2 * Cr * 8 ^ cr * B ^ E +
        (2 * Cr * 8 ^ cr * B ^ E + 300 * B ^ 6) + 4000 * B ^ 6 ≤
        (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E := by
      have h1 : 300 * B ^ 6 + 4000 * B ^ 6 ≤ 4300 * B ^ E := by
        clear * - hB6E; omega
      have hc : 104 * (Cr * 8 ^ cr) + 4300 ≤ (Cr + 1) * 8 ^ cr * 2 ^ 14 := by nlinarith
      have h2 : 104 * (Cr * 8 ^ cr * B ^ E) + 4300 * B ^ E ≤
          (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E := by
        calc 104 * (Cr * 8 ^ cr * B ^ E) + 4300 * B ^ E
            = (104 * (Cr * 8 ^ cr) + 4300) * B ^ E := by ring
          _ ≤ ((Cr + 1) * 8 ^ cr * 2 ^ 14) * B ^ E := Nat.mul_le_mul_right _ hc
      have hSum : 100 * Cr * 8 ^ cr * B ^ E + 2 * Cr * 8 ^ cr * B ^ E + 2 * Cr * 8 ^ cr * B ^ E =
          104 * (Cr * 8 ^ cr * B ^ E) := by ring
      clear * - h1 h2 hSum; omega
    have hSplitT : T * (roundNonHoleCap s k d + k * (mC + 3 * s) + rCap + G.n) =
        T * (roundNonHoleCap s k d + k * (mC + 3 * s) + G.n) + T * rCap := by ring
    have hRHS_eq : RHS = (C_sp + 1) * 2 ^ 120 * B ^ E + (Cr + 1) * 8 ^ cr * 2 ^ 14 * B ^ E := by
      dsimp only [RHS]; rw [Nat.add_mul]
    rw [hSplitT]
    clear * - hInjEnd hmC hrCapE hTrCapE hRestPoly hConnS hC1 hC2 hRHS_eq
    omega

/-- **Main space-envelope theorem**: for any router with polynomial space `sR`,
`buildLevelSpace sR (coreBridgeSpace C_sp)` satisfies `BuildLevelSpacePoly`. -/
theorem buildLevelSpace_poly_coreBridge {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {Cr cr C_sp : ℕ}
    (hsR : ∀ n gLen pLen par, sR n gLen pLen par ≤ Cr * (n + gLen + pLen + par + 2) ^ cr) :
    BuildLevelSpacePoly (buildLevelSpace sR (coreBridgeSpace C_sp))
      ((C_sp + 1) * 2 ^ 120 + (Cr + 1) * 8 ^ cr * 2 ^ 14) (max 24 (2 * cr + 4)) := by
  intro G s k M r Δ L L' bh hr
  set B := G.n + G.m + s + k + M + r + Δ + L + L' + bh +
    (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 2
  exact buildLevelSpace_le_of_caps (B := B) hsR
    (fun _ => coreBridgeSpace_le_poly hr (by dsimp only [B]; omega) (by dsimp only [B]; omega))
    ((NOf_le_of_le_ell hr).trans (by dsimp only [B]; omega))
    (by dsimp only [B]; omega)

end MinCostFlow.HierPaths

end
