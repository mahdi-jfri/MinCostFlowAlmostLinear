module

public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.Expander.DecrementalPaths
public import MinCostFlow.Expander.PathDSBounds
public import MinCostFlow.Expander.PathDS
public import MinCostFlow.Expander.PruningProg
public import MinCostFlow.Expander.PathDSProg.FallbackCost
public import MinCostFlow.Expander.ExpanderDecomp

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computable Parameter Bundle and Complexity Bounds for `PathDSImpl`

Defines the concrete `Spanner.PathDSParams` bundle `pathDSParams Kγ c K_int cw_cs` from a
`Cited.DecrementalExpanderPaths` instantiation `(Kγ, c, K, cw_cs)`:

1. `phiOutDenImpl Kγ c d M := max 2 (max d (c * Cited.csGamma Kγ (3 * M)))`, matching
   `csPhiOut Kγ c (1 / d) M` (`pathDSOfCS_φ_out`).
2. `csExpFactor Kγ K_int M := 2 ^ (csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M) + 1`,
   a monotone `exp(O(log(M + 2)^{7/8}))` envelope covering both `(3 * M)^{1/q}` and
   `csGamma Kγ (4 * M)^{K * q}` inside `csTotal` and `csQuery`.
3. `zStarImpl d := 2 ^ zStarExp d` with `zStarExp d = natCbrtFloor ((Nat.log 2 (10 * d) + 1) ^ 4)`:
   whenever `phiNum / phiDen < 10 * Cited.csPhi Kγ c (3 * G.m)` (the fallback regime),
   `3 * G.m < zStarImpl ((phiDen + phiNum - 1) / phiNum)` holds (`three_m_lt_zStar`), so
   `fbCostCap d M` bounds both `pruneTimeBound G_s.n G_s.m H` and `350 * (G_s.n + G_s.m + 1)`
   when `G.m ≤ M` (`fbCostCap_covers_fallback`).
4. `gExpImpl Kγ c K_int d M := phiOutDenImpl Kγ c d M * lenFactor M + csExpFactor Kγ K_int M`
   bounds the length of a returned walk, with `lenFactor M = 120 · (log₂(6M + 2) + 1)`.
   The time of a query or a deletion is charged by
   `gQueryImpl = gBaseImpl + gExpImpl`, where `gBaseImpl = phiOutDen + csExpFactor + fbCostCap`
   covers the fallback cost. `gDelImpl K_int _ _ := max 190 (max K_int 7)`.
5. `ParamsConsumerBounds.lean` provides consumer upper bounds (`pathDSParams_phiOutDen_*`,
   `pathDSParams_gExp_at_phiConst*`, `pathDSParams_gExp_at_phiB1*`, `pathDSParams_gDel_*`)
   together with the fallback `7/8` impossibility theorems (`fallback_query_cost_forces_gamma`,
   `fallback_prevents_seven_eighths_gExp`, `exp_rpow_exceeds_seven_eighths`, `csPhi_b9`).
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Pure Computable Helpers -/

/-- Exponent `Kγ * (⌊(log₂ x + 1)^{3/4}⌋ + 1)` inside `Cited.csGamma Kγ x`. -/
def csGammaExp (Kγ x : ℕ) : ℕ :=
  Kγ * (Nat.sqrt (Nat.sqrt ((Nat.log 2 x + 1) ^ 3)) + 1)

lemma csGamma_eq_two_pow (Kγ x : ℕ) : Cited.csGamma Kγ x = 2 ^ csGammaExp Kγ x := rfl

lemma csGammaExp_mono {Kγ x y : ℕ} (hxy : x ≤ y) : csGammaExp Kγ x ≤ csGammaExp Kγ y := by
  unfold csGammaExp
  have h1 : Nat.log 2 x ≤ Nat.log 2 y := Nat.log_mono_right hxy
  have h2 : (Nat.log 2 x + 1) ^ 3 ≤ (Nat.log 2 y + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  exact Nat.mul_le_mul_left Kγ (Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt h2)) 1)

/-- Eighth root floor `⌊(log₂(M + 2))^{1/8}⌋` (`qOf M = qRoot M + 2`). -/
def qRoot (M : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.log 2 (M + 2))))

lemma qOf_eq_qRoot_add_two (M : ℕ) : qOf M = qRoot M + 2 := rfl

lemma qRoot_mono {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) : qRoot M₁ ≤ qRoot M₂ := by
  unfold qRoot
  exact Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))))

lemma qRoot_pow_eight_le (M : ℕ) : (qRoot M) ^ 8 ≤ Nat.log 2 (M + 2) := by
  set k := Nat.log 2 (M + 2)
  set a₁ := Nat.sqrt k
  set a₂ := Nat.sqrt a₁
  set a₃ := Nat.sqrt a₂
  change a₃ ^ 8 ≤ k
  have h3 : a₃ ^ 2 ≤ a₂ := by rw [sq]; exact Nat.sqrt_le a₂
  have h2 : a₂ ^ 2 ≤ a₁ := by rw [sq]; exact Nat.sqrt_le a₁
  have h1 : a₁ ^ 2 ≤ k := by rw [sq]; exact Nat.sqrt_le k
  calc a₃ ^ 8 = ((a₃ ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ (a₂ ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) 2
    _ ≤ a₁ ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ k := h1

lemma log_lt_succ_qRoot_pow_eight (M : ℕ) : Nat.log 2 (M + 2) + 1 ≤ (qRoot M + 1) ^ 8 := by
  set k := Nat.log 2 (M + 2)
  set a₁ := Nat.sqrt k
  set a₂ := Nat.sqrt a₁
  set a₃ := Nat.sqrt a₂
  change k + 1 ≤ (a₃ + 1) ^ 8
  have h1 : k + 1 ≤ (a₁ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt k
  have h2 : a₁ + 1 ≤ (a₂ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt a₁
  have h3 : a₂ + 1 ≤ (a₃ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt a₂
  calc k + 1 ≤ (a₁ + 1) ^ 2 := h1
    _ ≤ ((a₂ + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = (a₂ + 1) ^ 4 := by ring
    _ ≤ ((a₃ + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left h3 4
    _ = (a₃ + 1) ^ 8 := by ring

/-- Monotone exponent `(qRoot M + 1)^7 + 2` satisfying `(4 * M + 4)^{1 / qOf M} ≤ 2^{qExpPow M}`. -/
def qExpPow (M : ℕ) : ℕ :=
  (qRoot M + 1) ^ 7 + 2

lemma qExpPow_mono {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) : qExpPow M₁ ≤ qExpPow M₂ := by
  unfold qExpPow
  have hr := Nat.add_le_add_right (qRoot_mono hM) 1
  exact Nat.add_le_add_right (Nat.pow_le_pow_left hr 7) 2

lemma four_m_add_four_le_two_pow_q (M : ℕ) :
    4 * M + 4 ≤ 2 ^ (qOf M * qExpPow M) := by
  have hlt : M + 2 < 2 ^ (Nat.log 2 (M + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (M + 2)
  have h4m : 4 * M + 4 ≤ 4 * 2 ^ (Nat.log 2 (M + 2) + 1) := by omega
  have h4pow : 4 * 2 ^ (Nat.log 2 (M + 2) + 1) = 2 ^ (Nat.log 2 (M + 2) + 3) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]; congr 1; omega
  have h8 := log_lt_succ_qRoot_pow_eight M
  have hexp : Nat.log 2 (M + 2) + 3 ≤ qOf M * qExpPow M := by
    rw [qOf_eq_qRoot_add_two, qExpPow]
    set s := qRoot M
    have hmul : (s + 2) * ((s + 1) ^ 7 + 2) = (s + 1) ^ 8 + (s + 1) ^ 7 + 2 * s + 4 := by ring
    have hpow_ge : 1 ≤ (s + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc 4 * M + 4 ≤ 2 ^ (Nat.log 2 (M + 2) + 3) := by omega
    _ ≤ 2 ^ (qOf M * qExpPow M) := Nat.pow_le_pow_right (by decide) hexp

lemma rpow_inv_qOf_le_two_pow_qExpPow {m M : ℕ} (hmM : m ≤ M) :
    ((3 * m : ℝ) + 1) ^ (1 / (qOf M : ℝ)) ≤ ((2 ^ qExpPow M : ℕ) : ℝ) := by
  have hm4 : (3 * m : ℝ) + 1 ≤ ((2 ^ (qOf M * qExpPow M) : ℕ) : ℝ) := by
    have hnat : 3 * m + 1 ≤ 4 * M + 4 := by omega
    exact_mod_cast le_trans hnat (four_m_add_four_le_two_pow_q M)
  have hq2 : (2 : ℝ) ≤ (qOf M : ℝ) := by exact_mod_cast qOf_ge_two M
  have hqpos : (0 : ℝ) < (qOf M : ℝ) := by linarith
  have hpow : (((3 * m : ℝ) + 1) ^ (1 / (qOf M : ℝ))) ^ (qOf M : ℕ) ≤
      (((2 ^ qExpPow M : ℕ) : ℝ)) ^ (qOf M : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have hmul : (1 / (qOf M : ℝ)) * (qOf M : ℝ) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
    have hrhs : (((2 ^ qExpPow M : ℕ) : ℝ)) ^ (qOf M : ℕ) =
        ((2 ^ (qOf M * qExpPow M) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_mul, mul_comm]
    rw [hrhs]
    exact hm4
  exact le_of_pow_le_pow_left₀ (by have := qOf_ge_two M; omega) (by positivity) hpow

/-- Key fallback inversion: if `phiNum / phiDen < 10 * csPhi Kγ c (3 * G.m)` (with `1 ≤ Kγ, c, G.m`)
and `d = ⌈phiDen / phiNum⌉₊ = (phiDen + phiNum - 1) / phiNum`, then `3 * G.m < zStarImpl d`. -/
lemma three_m_lt_zStar {Kγ c phiNum phiDen m : ℕ}
    (hKγ : 1 ≤ Kγ) (hc : 1 ≤ c) (hpn : 1 ≤ phiNum) (_hpd : phiNum ≤ phiDen) (_hm : 1 ≤ m)
    (hlt : ((phiNum : ℝ) / (phiDen : ℝ)) < 10 * Cited.csPhi Kγ c (3 * m)) :
    3 * m < zStarImpl ((phiDen + phiNum - 1) / phiNum) := by
  set d := (phiDen + phiNum - 1) / phiNum
  have hpd_pos : 0 < phiDen := by omega
  have hd_mul : phiDen ≤ d * phiNum := by
    have h := Nat.lt_div_mul_add hpn (a := phiDen + phiNum - 1)
    dsimp only [d]
    omega
  have hcs_pos : (0 : ℝ) < (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by
    unfold Cited.csGamma
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    positivity
  have hmulR : (phiNum : ℝ) * ((c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ)) < 10 * (phiDen : ℝ) := by
    rw [Cited.csPhi, mul_one_div] at hlt
    have hpdR : (0 : ℝ) < (phiDen : ℝ) := by exact_mod_cast hpd_pos
    rw [div_lt_div_iff₀ hpdR hcs_pos] at hlt
    linarith
  have hmulN : phiNum * (c * Cited.csGamma Kγ (3 * m)) < 10 * phiDen := by
    exact_mod_cast hmulR
  have hcs_lt : Cited.csGamma Kγ (3 * m) < 10 * d := by
    have h1 : phiNum * Cited.csGamma Kγ (3 * m) ≤ phiNum * (c * Cited.csGamma Kγ (3 * m)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hc)
    have h2 : 10 * phiDen ≤ 10 * (d * phiNum) := Nat.mul_le_mul_left 10 hd_mul
    nlinarith
  have hpow_lt : 2 ^ csGammaExp Kγ (3 * m) < 2 ^ (Nat.log 2 (10 * d) + 1) := by
    rw [← csGamma_eq_two_pow]
    exact lt_of_lt_of_le hcs_lt (Nat.lt_pow_succ_log_self (by decide) (10 * d)).le
  have hexp_lt : csGammaExp Kγ (3 * m) < Nat.log 2 (10 * d) + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow_lt
  set s := Nat.sqrt (Nat.sqrt ((Nat.log 2 (3 * m) + 1) ^ 3))
  have hs1 : s + 1 ≤ Nat.log 2 (10 * d) := by
    have hle : s + 1 ≤ Kγ * (s + 1) := Nat.le_mul_of_pos_left (s + 1) hKγ
    change Kγ * (s + 1) < Nat.log 2 (10 * d) + 1 at hexp_lt
    omega
  have hcub_lt : (Nat.log 2 (3 * m) + 1) ^ 3 < (s + 1) ^ 4 := by
    set u := Nat.sqrt ((Nat.log 2 (3 * m) + 1) ^ 3)
    have h1 : (Nat.log 2 (3 * m) + 1) ^ 3 < (u + 1) ^ 2 := by
      rw [sq]; exact Nat.lt_succ_sqrt _
    have h2 : u + 1 ≤ (s + 1) ^ 2 := by
      rw [sq]; exact Nat.lt_succ_sqrt u
    have h2p : (u + 1) ^ 2 ≤ ((s + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    have hpow4 : ((s + 1) ^ 2) ^ 2 = (s + 1) ^ 4 := by ring
    omega
  have hpow4 : (s + 1) ^ 4 < (Nat.log 2 (10 * d) + 1) ^ 4 :=
    Nat.pow_lt_pow_left (by omega) (by decide)
  have hspec := (natCbrtFloor_spec ((Nat.log 2 (10 * d) + 1) ^ 4)).2
  change (Nat.log 2 (10 * d) + 1) ^ 4 < (zStarExp d + 1) ^ 3 at hspec
  have hcub_z : (Nat.log 2 (3 * m) + 1) ^ 3 < (zStarExp d + 1) ^ 3 := by omega
  have hlog_le : Nat.log 2 (3 * m) + 1 ≤ zStarExp d := by
    by_contra hgt
    have hge : zStarExp d + 1 ≤ Nat.log 2 (3 * m) + 1 := by omega
    have := Nat.pow_le_pow_left hge 3
    omega
  have h3m_lt : 3 * m < 2 ^ (Nat.log 2 (3 * m) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (3 * m)
  exact lt_of_lt_of_le h3m_lt (Nat.pow_le_pow_right (by decide) hlog_le)

/-! ## 2. Concrete Parameter Functions -/

/-- Effective conductance denominator `phiOutDen d M = max 2 (max d (c * csGamma Kγ (3 * M)))`. -/
def phiOutDenImpl (Kγ c d M : ℕ) : ℕ :=
  max 2 (max d (c * Cited.csGamma Kγ (3 * M)))

lemma phiOutDenImpl_mono {Kγ c d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    phiOutDenImpl Kγ c d₁ M₁ ≤ phiOutDenImpl Kγ c d₂ M₂ := by
  unfold phiOutDenImpl
  have hcs : c * Cited.csGamma Kγ (3 * M₁) ≤ c * Cited.csGamma Kγ (3 * M₂) :=
    Nat.mul_le_mul_left c (csGamma_mono (by omega))
  omega

/-- Monotone `[CS21]` envelope factor `2 ^ (csGammaExp Kγ (4*M) * K_int * qOf M + qExpPow M) + 1`. -/
def csExpFactor (Kγ K_int M : ℕ) : ℕ :=
  2 ^ (csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M) + 1

lemma csExpFactor_mono {Kγ K_int M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) :
    csExpFactor Kγ K_int M₁ ≤ csExpFactor Kγ K_int M₂ := by
  unfold csExpFactor
  have h1 : csGammaExp Kγ (4 * M₁) ≤ csGammaExp Kγ (4 * M₂) := csGammaExp_mono (by omega)
  have h2 : qOf M₁ ≤ qOf M₂ := qOf_mono hM
  have h3 : qExpPow M₁ ≤ qExpPow M₂ := qExpPow_mono hM
  have hmul : csGammaExp Kγ (4 * M₁) * K_int * qOf M₁ ≤
      csGammaExp Kγ (4 * M₂) * K_int * qOf M₂ :=
    Nat.mul_le_mul (Nat.mul_le_mul_right K_int h1) h2
  exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (by omega)) 1

lemma one_le_csExpFactor (Kγ K_int M : ℕ) : 1 ≤ csExpFactor Kγ K_int M := by
  unfold csExpFactor
  exact Nat.le_add_left _ _

lemma no_isolated_n_le_two_m_of_valid {G : Cited.Graph} (hV : G.IsValid)
    (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) : G.n ≤ 2 * G.m := by
  have hvol : G.vol G.verts = 2 * G.m := vol_verts_of_isValid hV
  have hsum : G.verts.card ≤ ∑ v ∈ G.verts, G.deg v := by
    have : G.verts.card = ∑ _v ∈ G.verts, 1 := by simp
    rw [this]
    refine Finset.sum_le_sum fun v hv => hnoIso v ?_
    simpa [Cited.Graph.verts] using hv
  have hcard : G.verts.card = G.n := by simp [Cited.Graph.verts]
  have hvol_eq : ∑ v ∈ G.verts, G.deg v = G.vol G.verts := rfl
  omega

/-- On a fallback cluster with `m ≤ M` edges, `fbCostCap d M` pays for pruning the subdivided
cluster and for one search over it. -/
lemma fbCostCap_covers_fallback {G : Cited.Graph} {d M : ℕ}
    (hV : G.IsValid) (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) (hm_lt : 3 * G.m < zStarImpl d)
    (hmM : G.m ≤ M) :
    let G_s := subdivGraph G
    let C_cap := 40 * d + 1
    let H := 4 * C_cap * (Nat.log 2 (2 * G_s.m + 1) + 1) + 2
    G_s.n ≤ 2 * zCap d M ∧
    G_s.m ≤ zCap d M ∧
    H ≤ 4 * (40 * d + 1) * (zStarExp d + 2) + 2 ∧
    pruneTimeBound G_s.n G_s.m H + 200 * G_s.n + 200 ≤ fbCostCap d M ∧
    350 * (G_s.n + G_s.m + 1) + 200 * G_s.n + 200 ≤ fbCostCap d M := by
  have hn_le_2m : G.n ≤ 2 * G.m := no_isolated_n_le_two_m_of_valid hV hnoIso
  have hcap : 3 * G.m < zCap d M := three_m_lt_zCap hmM hm_lt
  have hsn : (subdivGraph G).n ≤ 2 * zCap d M := by
    rw [subdivGraph_n]; omega
  have hsm : (subdivGraph G).m ≤ zCap d M := by
    rw [subdivGraph_m]; omega
  have hlog : Nat.log 2 (2 * (subdivGraph G).m + 1) + 1 ≤ zStarExp d + 2 := by
    have hlt2 : 2 * (subdivGraph G).m + 1 < 2 ^ (zStarExp d + 1) := by
      have : 2 * (subdivGraph G).m + 1 < 2 * zStarImpl d := by rw [subdivGraph_m]; omega
      calc 2 * (subdivGraph G).m + 1 < 2 * zStarImpl d := this
        _ = 2 ^ (zStarExp d + 1) := by rw [zStarImpl, pow_succ']
    have hlog_lt : Nat.log 2 (2 * (subdivGraph G).m + 1) < zStarExp d + 1 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt2
    omega
  have hH_le : 4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2 ≤
      4 * (40 * d + 1) * (zStarExp d + 2) + 2 := by
    have h1 := Nat.mul_le_mul_left (4 * (40 * d + 1)) hlog
    omega
  have hp_mono : pruneTimeBound (subdivGraph G).n (subdivGraph G).m
        (4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2) ≤
      pruneTimeBound (2 * zCap d M) (zCap d M) (4 * (40 * d + 1) * (zStarExp d + 2) + 2) := by
    unfold pruneTimeBound
    have hp1 : 4 * (4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2) + 14 ≤
        4 * (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 14 := by omega
    have hp2 : 4 * (4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2) + 4 ≤
        4 * (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 4 := by omega
    have hp3 : 2 * (subdivGraph G).m + 1 ≤ 2 * zCap d M + 1 := by omega
    have hmul : (4 * (4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2) + 14) *
          (4 * (4 * (40 * d + 1) * (Nat.log 2 (2 * (subdivGraph G).m + 1) + 1) + 2) + 4) *
          (2 * (subdivGraph G).m + 1) ≤
        (4 * (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 14) *
          (4 * (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 4) *
          (2 * zCap d M + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp1 hp2) hp3
    gcongr
  have h200 : 200 * (subdivGraph G).n + 200 ≤ 2000 * zCap d M := by
    have := one_le_zCap d M
    omega
  have h350 : 350 * ((subdivGraph G).n + (subdivGraph G).m + 1) + 200 * (subdivGraph G).n + 200 ≤
      2000 * zCap d M := by
    have hz1 := one_le_zCap d M
    omega
  refine ⟨hsn, hsm, hH_le, ?_, ?_⟩
  · have hfb : pruneTimeBound (2 * zCap d M) (zCap d M)
        (4 * (40 * d + 1) * (zStarExp d + 2) + 2) + 2000 * zCap d M ≤ fbCostCap d M := by
      unfold fbCostCap; dsimp only; omega
    omega
  · have hfb := zCap_le_fbCostCap d M
    omega

/-- The sum `phiOutDen + csExpFactor + fbCostCap`. It covers the time of one operation in either
mode, and `gQueryImpl` contains it. -/
def gBaseImpl (Kγ c K_int d M : ℕ) : ℕ :=
  phiOutDenImpl Kγ c d M + csExpFactor Kγ K_int M + fbCostCap d M

lemma gBaseImpl_le_fbCostBound (Kγ c K_int d M : ℕ) :
    gBaseImpl Kγ c K_int d M ≤ phiOutDenImpl Kγ c d M + csExpFactor Kγ K_int M + fbCostBound d := by
  have := fbCostCap_le d M
  unfold gBaseImpl
  omega

lemma gBaseImpl_mono {Kγ c K_int d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    gBaseImpl Kγ c K_int d₁ M₁ ≤ gBaseImpl Kγ c K_int d₂ M₂ := by
  unfold gBaseImpl
  exact Nat.add_le_add
    (Nat.add_le_add (phiOutDenImpl_mono hd hM) (csExpFactor_mono hM))
    (fbCostCap_mono hd hM)

/-- The factor `120 · (log₂(6M + 2) + 1)`. A fallback walk has at most
`phiOutDen · lenFactor M` edges: the kept part of the subdivided graph has conductance at least
`1 / (30 · d)` and volume at most `6M`, and the diameter bound gives the factor `4 · 30`. -/
def lenFactor (M : ℕ) : ℕ := 120 * (Nat.log 2 (6 * M + 2) + 1)

lemma lenFactor_mono {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) : lenFactor M₁ ≤ lenFactor M₂ := by
  unfold lenFactor
  have := Nat.log_mono_right (b := 2) (show 6 * M₁ + 2 ≤ 6 * M₂ + 2 by omega)
  omega

lemma two_hundred_forty_le_lenFactor (M : ℕ) : 240 ≤ lenFactor M := by
  unfold lenFactor
  have : 1 ≤ Nat.log 2 (6 * M + 2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  omega

lemma lenFactor_le (M : ℕ) : lenFactor M ≤ 720 * (M + 2) := by
  unfold lenFactor
  have := Nat.log_le_self 2 (6 * M + 2)
  omega

/-- Path-length parameter `gExpImpl d M = phiOutDen · lenFactor M + csExpFactor`. The term
`csExpFactor` covers the walks of the `[CS21]` mode and the term `phiOutDen · lenFactor M` covers
the walks of the fallback mode. -/
def gExpImpl (Kγ c K_int d M : ℕ) : ℕ :=
  phiOutDenImpl Kγ c d M * lenFactor M + csExpFactor Kγ K_int M

lemma phiOutDenImpl_le_gExpImpl (Kγ c K_int d M : ℕ) :
    phiOutDenImpl Kγ c d M ≤ gExpImpl Kγ c K_int d M := by
  unfold gExpImpl
  have := Nat.le_mul_of_pos_right (phiOutDenImpl Kγ c d M)
    (show 0 < lenFactor M by have := two_hundred_forty_le_lenFactor M; omega)
  omega

lemma csExpFactor_le_gExpImpl (Kγ c K_int d M : ℕ) :
    csExpFactor Kγ K_int M ≤ gExpImpl Kγ c K_int d M := by
  unfold gExpImpl
  omega

lemma two_le_gExpImpl (Kγ c K_int d M : ℕ) : 2 ≤ gExpImpl Kγ c K_int d M := by
  have := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
  unfold phiOutDenImpl at this
  omega

lemma gExpImpl_mono {Kγ c K_int d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    gExpImpl Kγ c K_int d₁ M₁ ≤ gExpImpl Kγ c K_int d₂ M₂ := by
  unfold gExpImpl
  exact Nat.add_le_add (Nat.mul_le_mul (phiOutDenImpl_mono hd hM) (lenFactor_mono hM))
    (csExpFactor_mono hM)

/-- Time parameter `gQueryImpl d M = gBaseImpl d M + gExpImpl d M`. It is at least `gExpImpl`,
and it covers the fallback cost `fbCostCap`. -/
def gQueryImpl (Kγ c K_int d M : ℕ) : ℕ :=
  gBaseImpl Kγ c K_int d M + gExpImpl Kγ c K_int d M

lemma gExpImpl_le_gQueryImpl (Kγ c K_int d M : ℕ) :
    gExpImpl Kγ c K_int d M ≤ gQueryImpl Kγ c K_int d M := by
  unfold gQueryImpl
  omega

lemma gQueryImpl_mono {Kγ c K_int d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    gQueryImpl Kγ c K_int d₁ M₁ ≤ gQueryImpl Kγ c K_int d₂ M₂ := by
  unfold gQueryImpl
  exact Nat.add_le_add (gBaseImpl_mono hd hM) (gExpImpl_mono hd hM)

/-- Deletion volume multiplier `gDelImpl`. -/
def gDelImpl (K_int _d _M : ℕ) : ℕ :=
  max 190 (max K_int 7)

/-! ### Polynomial upper bounds

The consumer of `PathDSParams` needs the bounds to fit in `O(log)`-bit words, so it needs them
polynomial in `d + M`. Each part of `gBaseImpl` is polynomial: `c · csGamma Kγ (3M)` has degree
`Kγ`, `csExpFactor` has degree `11 Kγ K_int + 131`, and `fbCostCap` has degree `11`. -/

private lemma sqrt_sqrt_pow_four_le (y : ℕ) : (Nat.sqrt (Nat.sqrt y)) ^ 4 ≤ y := by
  have h1 : Nat.sqrt (Nat.sqrt y) * Nat.sqrt (Nat.sqrt y) ≤ Nat.sqrt y := Nat.sqrt_le _
  have h2 : Nat.sqrt y * Nat.sqrt y ≤ y := Nat.sqrt_le _
  calc (Nat.sqrt (Nat.sqrt y)) ^ 4
      = (Nat.sqrt (Nat.sqrt y) * Nat.sqrt (Nat.sqrt y)) *
          (Nat.sqrt (Nat.sqrt y) * Nat.sqrt (Nat.sqrt y)) := by ring
    _ ≤ Nat.sqrt y * Nat.sqrt y := Nat.mul_le_mul h1 h1
    _ ≤ y := h2

/-- If `a ^ n ≤ b ^ n` with `n ≥ 1`, then `a ≤ b`. -/
private lemma le_of_pow_le_pow' {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  exact absurd h (not_le.mpr (Nat.pow_lt_pow_left (by omega) hn))

lemma csGammaExp_le_log (Kγ x : ℕ) : csGammaExp Kγ x ≤ Kγ * (Nat.log 2 x + 2) := by
  unfold csGammaExp
  have h4 := sqrt_sqrt_pow_four_le ((Nat.log 2 x + 1) ^ 3)
  have h34 : (Nat.log 2 x + 1) ^ 3 ≤ (Nat.log 2 x + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have hs : Nat.sqrt (Nat.sqrt ((Nat.log 2 x + 1) ^ 3)) ≤ Nat.log 2 x + 1 :=
    le_of_pow_le_pow' (by norm_num) (le_trans h4 h34)
  exact Nat.mul_le_mul_left Kγ (by omega)

lemma csGamma_three_le_poly (Kγ M : ℕ) :
    Cited.csGamma Kγ (3 * M) ≤ 16 ^ Kγ * (M + 2) ^ Kγ := by
  rw [csGamma_eq_two_pow]
  set l := Nat.log 2 (3 * M + 6)
  have hl : Nat.log 2 (3 * M) ≤ l := Nat.log_mono_right (by omega)
  have h2l : 2 ^ l ≤ 3 * M + 6 := Nat.pow_log_le_self 2 (by omega)
  have he : csGammaExp Kγ (3 * M) ≤ Kγ * (l + 2) :=
    le_trans (csGammaExp_le_log Kγ _) (Nat.mul_le_mul_left Kγ (by omega))
  calc 2 ^ csGammaExp Kγ (3 * M) ≤ 2 ^ (Kγ * (l + 2)) := Nat.pow_le_pow_right (by decide) he
    _ = (4 * 2 ^ l) ^ Kγ := by rw [mul_comm, pow_mul, pow_add]; ring
    _ ≤ (16 * (M + 2)) ^ Kγ := Nat.pow_le_pow_left (by omega) _
    _ = 16 ^ Kγ * (M + 2) ^ Kγ := mul_pow _ _ _

/-- Degree of the polynomial bound on `csExpFactor Kγ K_int M`. -/
def csExpDeg (Kγ K_int : ℕ) : ℕ := 11 * (Kγ * K_int) + 131

lemma csExpFactor_le_poly (Kγ K_int M : ℕ) :
    csExpFactor Kγ K_int M ≤ 2 * 2 ^ csExpDeg Kγ K_int * (M + 2) ^ csExpDeg Kγ K_int := by
  set k := Nat.log 2 (M + 2)
  set q := qRoot M
  set l := Nat.log 2 (4 * M)
  set s := Nat.sqrt (Nat.sqrt ((l + 1) ^ 3))
  set A := csExpDeg Kγ K_int
  have hq8 : q ^ 8 ≤ k := qRoot_pow_eight_le M
  have hl : l ≤ k + 2 := by
    have h1 : l ≤ Nat.log 2 ((M + 2) * 2 * 2) := Nat.log_mono_right (by omega)
    have h2 : Nat.log 2 ((M + 2) * 2 * 2) = k + 2 := by
      rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega)]
    omega
  have hs4 : s ^ 4 ≤ (k + 3) ^ 3 :=
    le_trans (sqrt_sqrt_pow_four_le _) (Nat.pow_le_pow_left (by omega) 3)
  have hs : s ≤ k + 3 :=
    le_of_pow_le_pow' (by norm_num)
      (le_trans hs4 (Nat.pow_le_pow_right (by omega) (by norm_num)))
  have hq : q ≤ k := le_trans (Nat.le_self_pow (by norm_num) q) hq8
  have hsq : s * q ≤ k + 3 := by
    have h8 : (s * q) ^ 8 ≤ (k + 3) ^ 7 := by
      calc (s * q) ^ 8 = (s ^ 4) ^ 2 * q ^ 8 := by ring
        _ ≤ ((k + 3) ^ 3) ^ 2 * (k + 3) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hs4 2) (by omega)
        _ = (k + 3) ^ 7 := by ring
    have h78 : (k + 3) ^ 7 ≤ (k + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact le_of_pow_le_pow' (by norm_num) (le_trans h8 h78)
  have hprod : (s + 1) * (q + 2) ≤ 11 * (k + 1) := by
    have : (s + 1) * (q + 2) = s * q + 2 * s + q + 2 := by ring
    omega
  have hqe : qExpPow M ≤ 128 * k + 3 := by
    unfold qExpPow
    change (q + 1) ^ 7 + 2 ≤ 128 * k + 3
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · rw [h0]; omega
    · have h1 : (q + 1) ^ 7 ≤ (2 * q) ^ 7 := Nat.pow_le_pow_left (by omega) 7
      have h2 : (2 * q) ^ 7 = 128 * q ^ 7 := by ring
      have h3 : q ^ 7 ≤ q ^ 8 := Nat.pow_le_pow_right hpos (by norm_num)
      omega
  have hE : csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M ≤ A * (k + 1) := by
    have h1 : csGammaExp Kγ (4 * M) * K_int * qOf M = (Kγ * K_int) * ((s + 1) * (q + 2)) := by
      unfold csGammaExp; rw [qOf_eq_qRoot_add_two]; ring
    have h2 : (Kγ * K_int) * ((s + 1) * (q + 2)) ≤ (Kγ * K_int) * (11 * (k + 1)) :=
      Nat.mul_le_mul_left _ hprod
    have h3 : A * (k + 1) = (Kγ * K_int) * (11 * (k + 1)) + 131 * (k + 1) := by
      simp only [A, csExpDeg]; ring
    omega
  have h2k : 2 ^ k ≤ M + 2 := Nat.pow_log_le_self 2 (by omega)
  unfold csExpFactor
  have hpow : 2 ^ (csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M) ≤
      2 ^ A * (M + 2) ^ A :=
    calc 2 ^ (csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M) ≤ 2 ^ (A * (k + 1)) :=
          Nat.pow_le_pow_right (by decide) hE
      _ = (2 * 2 ^ k) ^ A := by rw [mul_comm, pow_mul]; ring
      _ ≤ (2 * (M + 2)) ^ A := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ A * (M + 2) ^ A := mul_pow _ _ _
  have hone : 1 ≤ 2 ^ A * (M + 2) ^ A :=
    Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.one_le_pow _ _ (by omega))
  have hassoc : 2 * 2 ^ A * (M + 2) ^ A = 2 * (2 ^ A * (M + 2) ^ A) := by ring
  omega

/-- Degree of the polynomial bound on `gBaseImpl`. -/
def gExpDeg (Kγ K_int : ℕ) : ℕ := Kγ + csExpDeg Kγ K_int + 11

/-- Constant of the polynomial bound on `gBaseImpl`. -/
def gExpConst (Kγ c K_int : ℕ) : ℕ := 3 + c * 16 ^ Kγ + 2 * 2 ^ csExpDeg Kγ K_int + 10 ^ 20

lemma gBaseImpl_le_poly (Kγ c K_int d M : ℕ) :
    gBaseImpl Kγ c K_int d M ≤ gExpConst Kγ c K_int * (d + M + 2) ^ gExpDeg Kγ K_int := by
  set X := d + M + 2
  set N := gExpDeg Kγ K_int
  set A := csExpDeg Kγ K_int
  have hX : 1 ≤ X := by omega
  have hpowN : ∀ j, j ≤ N → X ^ j ≤ X ^ N := fun j hj => Nat.pow_le_pow_right hX hj
  have hMX : M + 2 ≤ X := by omega
  have hphi : phiOutDenImpl Kγ c d M ≤ 2 + X + c * 16 ^ Kγ * X ^ Kγ := by
    unfold phiOutDenImpl
    have h1 := Nat.mul_le_mul_left c (csGamma_three_le_poly Kγ M)
    have h2 : (M + 2) ^ Kγ ≤ X ^ Kγ := Nat.pow_le_pow_left hMX _
    have h3 : c * (16 ^ Kγ * (M + 2) ^ Kγ) ≤ c * 16 ^ Kγ * X ^ Kγ := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ h2
    omega
  have hcs : csExpFactor Kγ K_int M ≤ 2 * 2 ^ A * X ^ A :=
    le_trans (csExpFactor_le_poly Kγ K_int M) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMX _))
  have hfb : fbCostCap d M ≤ 10 ^ 20 * X ^ 11 := fbCostCap_le_poly d M
  have h1 : X ≤ X ^ N := by
    have := hpowN 1 (by simp only [N, gExpDeg]; omega); simpa using this
  have h0 : 1 ≤ X ^ N := Nat.one_le_pow _ _ hX
  have hK : X ^ Kγ ≤ X ^ N := hpowN Kγ (by simp only [N, gExpDeg]; omega)
  have hA : X ^ A ≤ X ^ N := hpowN A (by simp only [N, gExpDeg, A]; omega)
  have h11 : X ^ 11 ≤ X ^ N := hpowN 11 (by simp only [N, gExpDeg]; omega)
  have hK' : c * 16 ^ Kγ * X ^ Kγ ≤ c * 16 ^ Kγ * X ^ N := Nat.mul_le_mul_left _ hK
  have hA' : 2 * 2 ^ A * X ^ A ≤ 2 * 2 ^ A * X ^ N := Nat.mul_le_mul_left _ hA
  have h11' : 10 ^ 20 * X ^ 11 ≤ 10 ^ 20 * X ^ N := Nat.mul_le_mul_left _ h11
  have hsum : gExpConst Kγ c K_int * X ^ N =
      3 * X ^ N + c * 16 ^ Kγ * X ^ N + 2 * 2 ^ A * X ^ N + 10 ^ 20 * X ^ N := by
    simp only [gExpConst, A]; ring
  unfold gBaseImpl
  omega

/-- `gQueryImpl` is at most `721 · X · gBaseImpl` with `X = d + M + 2`, since
`gExpImpl ≤ lenFactor M · gBaseImpl` and `lenFactor M ≤ 720 · X`. -/
lemma gQueryImpl_le_poly (Kγ c K_int d M : ℕ) :
    gQueryImpl Kγ c K_int d M ≤
      (721 * gExpConst Kγ c K_int) * (d + M + 2) ^ (gExpDeg Kγ K_int + 1) := by
  set X := d + M + 2
  have hL : lenFactor M ≤ 720 * X := le_trans (lenFactor_le M) (by omega)
  have hE : gExpImpl Kγ c K_int d M ≤ lenFactor M * gBaseImpl Kγ c K_int d M := by
    unfold gExpImpl gBaseImpl
    have h1 : 1 ≤ lenFactor M := by have := two_hundred_forty_le_lenFactor M; omega
    have h2 : csExpFactor Kγ K_int M ≤ lenFactor M * csExpFactor Kγ K_int M :=
      Nat.le_mul_of_pos_left _ h1
    nlinarith
  have hB := gBaseImpl_le_poly Kγ c K_int d M
  have hX1 : 1 ≤ X := by omega
  have hQ : gQueryImpl Kγ c K_int d M ≤ 721 * X * gBaseImpl Kγ c K_int d M := by
    unfold gQueryImpl
    have h3 : lenFactor M * gBaseImpl Kγ c K_int d M ≤ 720 * X * gBaseImpl Kγ c K_int d M :=
      Nat.mul_le_mul_right _ hL
    have h4 : gBaseImpl Kγ c K_int d M ≤ X * gBaseImpl Kγ c K_int d M :=
      Nat.le_mul_of_pos_left _ hX1
    nlinarith
  calc gQueryImpl Kγ c K_int d M ≤ 721 * X * gBaseImpl Kγ c K_int d M := hQ
    _ ≤ 721 * X * (gExpConst Kγ c K_int * X ^ gExpDeg Kγ K_int) := Nat.mul_le_mul_left _ hB
    _ = (721 * gExpConst Kγ c K_int) * X ^ (gExpDeg Kγ K_int + 1) := by ring

lemma gDelImpl_le_poly (K_int d M k : ℕ) : gDelImpl K_int d M ≤ (190 + K_int) * (d + M + 2) ^ k := by
  have h : 1 ≤ (d + M + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : 190 + K_int ≤ (190 + K_int) * (d + M + 2) ^ k := Nat.le_mul_of_pos_right _ h
  unfold gDelImpl
  omega


/-- Complete `PathDSParams` bundle built from `[CS21]` constants `(Kγ, c, K_int, cw_cs)`. -/
noncomputable def pathDSParams (Kγ c K_int cw_cs : ℕ) : PathDSParams where
  phiOutDen := phiOutDenImpl Kγ c
  gExp := gExpImpl Kγ c K_int
  gDel := gDelImpl K_int
  gQuery := gQueryImpl Kγ c K_int
  hphiOutDen_ge d M hd := by
    unfold phiOutDenImpl
    omega
  hgExp_ge d M _ := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
  hgDel_ge _ _ _ := by
    unfold gDelImpl
    omega
  hphiOutDen_mono _ _ _ _ _ hd hM := phiOutDenImpl_mono hd hM
  hgExp_mono _ _ _ _ _ hd hM := gExpImpl_mono hd hM
  hgDel_mono _ _ _ _ _ _ _ := le_rfl
  hgQuery_ge d M _ := gExpImpl_le_gQueryImpl Kγ c K_int d M
  hgQuery_mono _ _ _ _ _ hd hM := gQueryImpl_mono hd hM
  hpoly := ⟨721 * gExpConst Kγ c K_int + 190 + K_int, gExpDeg Kγ K_int + 1, fun d M _ =>
    ⟨le_trans (gQueryImpl_le_poly Kγ c K_int d M) (Nat.mul_le_mul_right _ (by omega)),
     le_trans (gDelImpl_le_poly K_int d M _) (Nat.mul_le_mul_right _ (by omega))⟩⟩
  K_init := 10 * (K_int : ℝ) + 4000
  K_del := 24 * (K_int : ℝ) + 400
  K_query := 40 * (K_int : ℝ) + 400
  hK_init := by positivity
  hK_del := by positivity
  hK_query := by positivity
  K_bounds := 2000
  cw := max 24 (4 * cw_cs + 8)
  hcw_pos := by omega
  boundsSpace _ _ := 3
  initSpace phiNum phiDen n m M :=
    6 * n + 30 * m + 50 + 4 * K_int * (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
  delSpace phiNum phiDen n m M :=
    100 * (n + m + 1) + 4000 * phiDen * (m + 2) +
      4 * K_int * (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
  querySpace phiNum phiDen n m M :=
    20 * (n + m + 1) + 2 * K_int * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
  C_space := 4200 + 8 * K_int
  c_space := 2
  hC_space := by omega
  hboundsSpace_le d M := by
    have hdm : 2 ≤ d + M + 2 := by omega
    have h2 : 4 ≤ (d + M + 2) ^ 2 := by rw [sq]; nlinarith
    have h1 : 3 ≤ 4200 * (d + M + 2) ^ 2 := by nlinarith
    have h2' : 4200 * (d + M + 2) ^ 2 ≤ (4200 + 8 * K_int) * (d + M + 2) ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 h2'
  hinitSpace_le phiNum phiDen n m M _ _ := by
    set X := phiDen + n + m + M + gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M + 2
    have hm1 : m + 1 ≤ X := by dsimp [X]; omega
    have hg : gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M ≤ X := by dsimp [X]; omega
    have hmul : (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M ≤ X ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul hm1 hg
    have hlin : 6 * n + 30 * m + 50 ≤ 30 * X := by dsimp [X]; omega
    have hX1 : X ≤ X ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left X (by dsimp [X]; omega)
    calc 6 * n + 30 * m + 50 +
          4 * K_int * (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
        ≤ 30 * X + 4 * K_int * X ^ 2 := by nlinarith
      _ ≤ 30 * X ^ 2 + 4 * K_int * X ^ 2 := by gcongr
      _ ≤ (4200 + 8 * K_int) * X ^ 2 := by nlinarith
  hdelSpace_le phiNum phiDen n m M _ _ := by
    set X := phiDen + n + m + M + gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M + 2
    have hm1 : m + 1 ≤ X := by dsimp [X]; omega
    have hm2 : m + 2 ≤ X := by dsimp [X]; omega
    have hpd : phiDen ≤ X := by dsimp [X]; omega
    have hg : gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M ≤ X := by dsimp [X]; omega
    have hpm : phiDen * (m + 2) ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul hpd hm2
    have hmg : (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M ≤ X ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul hm1 hg
    have hlin : 100 * (n + m + 1) ≤ 100 * X := by dsimp [X]; omega
    have hX1 : X ≤ X ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left X (by dsimp [X]; omega)
    calc 100 * (n + m + 1) + 4000 * phiDen * (m + 2) +
          4 * K_int * (m + 1) * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
        ≤ 100 * X + 4000 * X ^ 2 + 4 * K_int * X ^ 2 := by nlinarith
      _ ≤ 100 * X ^ 2 + 4000 * X ^ 2 + 4 * K_int * X ^ 2 := by gcongr
      _ ≤ (4200 + 8 * K_int) * X ^ 2 := by nlinarith
  hquerySpace_le phiNum phiDen n m M _ _ := by
    set X := phiDen + n + m + M + gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M + 2
    have hX1 : X ≤ X ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left X (by dsimp [X]; omega)
    have hlin : 20 * (n + m + 1) + 2 * K_int * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M ≤
        (20 + 2 * K_int) * X := by
      dsimp [X]; nlinarith
    calc 20 * (n + m + 1) + 2 * K_int * gExpImpl Kγ c K_int ((phiDen + phiNum - 1) / phiNum) M
        ≤ (20 + 2 * K_int) * X := hlin
      _ ≤ (20 + 2 * K_int) * X ^ 2 := by gcongr
      _ ≤ (4200 + 8 * K_int) * X ^ 2 := by nlinarith

/-! ## 3. Parameter Comparison with `pathDSOfCS` and `[CS21]` Bounds -/

lemma pathDSParams_φ_out_eq {Kγ c K_int cw_cs : ℕ} (hc : 1 ≤ c)
    {φ_in : ℝ} (hφ : 0 < φ_in) (M : ℕ) :
    (pathDSParams Kγ c K_int cw_cs).φ_out (roundPhi φ_in) M = csPhiOut Kγ c (roundPhi φ_in) M := by
  have hceil_eq : Nat.ceil (1 / roundPhi φ_in) = Nat.ceil (1 / φ_in) := by
    unfold roundPhi
    rw [one_div_one_div]
    exact Nat.ceil_natCast (Nat.ceil (1 / φ_in))
  set d := Nat.ceil (1 / φ_in)
  have hd_eq : (1 / (d : ℝ)) = roundPhi φ_in := rfl
  dsimp only [PathDSParams.φ_out, pathDSParams, phiOutDenImpl, csPhiOut]
  rw [hceil_eq]
  dsimp only [d]
  have hpos_d : (0 : ℝ) < (d : ℝ) := by
    have : 1 ≤ d := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
    exact_mod_cast this
  have hpos_cs : (0 : ℝ) < (c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) := by
    unfold Cited.csGamma
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    positivity
  push_cast
  have hrhs1 : min (1 / 2 : ℝ) (Cited.csPhi Kγ c (3 * M)) =
      1 / max (2 : ℝ) ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ)) := by
    unfold Cited.csPhi
    rcases le_total (2 : ℝ) ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ)) with h | h
    · rw [max_eq_right h, min_eq_right (one_div_le_one_div_of_le (by norm_num) h)]
    · rw [max_eq_left h, min_eq_left (one_div_le_one_div_of_le hpos_cs h)]
  have hrhs2 : min (roundPhi φ_in) (1 / max (2 : ℝ) ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ))) =
      1 / max (d : ℝ) (max (2 : ℝ) ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ))) := by
    rw [← hd_eq]
    rcases le_total (d : ℝ) (max (2 : ℝ) ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ))) with h | h
    · rw [max_eq_right h, min_eq_right (one_div_le_one_div_of_le hpos_d h)]
    · rw [max_eq_left h, min_eq_left (one_div_le_one_div_of_le (by positivity) h)]
  rw [hrhs1, hrhs2]
  congr 1
  rw [max_comm (2 : ℝ) (max (d : ℝ) _), max_assoc, max_comm _ (2 : ℝ), ← max_assoc, max_comm]

lemma pathDSParams_γ_del_const (Kγ c K_int cw_cs : ℕ) (φ_in : ℝ) (M : ℕ) :
    (pathDSParams Kγ c K_int cw_cs).γ_del φ_in M = max (190 : ℝ) (max (K_int : ℝ) 7) := by
  dsimp [PathDSParams.γ_del, pathDSParams, gDelImpl]
  push_cast
  rfl

private lemma csGamma_rpow_nat_mul (Kγ x a b : ℕ) :
    (Cited.csGamma Kγ x : ℝ) ^ ((a * b : ℕ) : ℝ) =
      ((2 ^ (csGammaExp Kγ x * a * b) : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have h1 : Cited.csGamma Kγ x ^ (a * b) = 2 ^ (csGammaExp Kγ x * a * b) := by
    rw [csGamma_eq_two_pow, ← pow_mul, mul_assoc]
  exact_mod_cast h1

private lemma two_pow_mul_two_pow_cast (a b : ℕ) :
    ((2 ^ a : ℕ) : ℝ) * ((2 ^ b : ℕ) : ℝ) = ((2 ^ (b + a) : ℕ) : ℝ) := by
  have h : 2 ^ a * 2 ^ b = 2 ^ (b + a) := by rw [← pow_add, add_comm]
  exact_mod_cast h

private lemma nat_ceil_mul_add_one_le {K x : ℝ} {K_int coeff P : ℕ}
    (_hK0 : 0 ≤ K) (hK_le : K ≤ K_int) (hK1 : 1 ≤ K_int) (hc : 1 ≤ coeff)
    (hx0 : 0 ≤ x) (hx : x ≤ (coeff : ℝ) * (P : ℝ)) (hP : 1 ≤ P) :
    Nat.ceil (K * (x + 1)) ≤ (coeff + 1) * K_int * (P + 1) := by
  apply Nat.ceil_le.mpr
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hK1R : (1 : ℝ) ≤ (K_int : ℝ) := by exact_mod_cast hK1
  have hcR : (1 : ℝ) ≤ (coeff : ℝ) := by exact_mod_cast hc
  have hfin1 : K * (x + 1) ≤ (K_int : ℝ) * ((coeff : ℝ) * (P : ℝ) + 1) :=
    mul_le_mul hK_le (by linarith) (by linarith) (Nat.cast_nonneg _)
  have hfin2 : (K_int : ℝ) * ((coeff : ℝ) * (P : ℝ) + 1) ≤
      ((coeff : ℝ) + 1) * (K_int : ℝ) * ((P : ℝ) + 1) := by nlinarith
  have hcast : ((((coeff + 1) * K_int * (P + 1) : ℕ) : ℝ)) =
      ((coeff : ℝ) + 1) * (K_int : ℝ) * ((P : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  exact le_trans hfin1 hfin2

lemma csTotal_subdiv_le_csExpFactor {Kγ _c K_int _cw_cs : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} {M : ℕ} (hV : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hnoIso : ∀ v < G.n, 1 ≤ G.deg v) :
    let G_s := subdivGraph G
    Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤ 4 * K_int * G.m * csExpFactor Kγ K_int M := by
  dsimp only
  have hK_le : K ≤ (K_int : ℝ) := le_trans (le_max_left K 1) hK
  have hK1 : 1 ≤ K_int := by
    have : (1 : ℝ) ≤ (K_int : ℝ) := le_trans (le_max_right K 1) hK
    exact_mod_cast this
  by_cases hK_neg : K ≤ 0
  · unfold Cited.csTotal
    have hnonpos : K * (((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
        (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) + 1) ≤ 0 := by
      have hgm : 0 ≤ ((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hcs : 0 ≤ (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_nonpos_of_nonpos_of_nonneg hK_neg (by nlinarith)
    rw [Nat.ceil_eq_zero.mpr hnonpos]
    exact Nat.zero_le _
  have hK0 : 0 ≤ K := le_of_not_ge hK_neg
  have hn_le : G.n ≤ 2 * G.m := no_isolated_n_le_two_m_of_valid hV hnoIso
  have hsn_le : (subdivGraph G).n ≤ 4 * M := by rw [subdivGraph_n]; omega
  have hsm_eq : (subdivGraph G).m = 3 * G.m := subdivGraph_m G
  have hpow1q : ((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) =
      (3 * (G.m : ℝ)) * (3 * (G.m : ℝ)) ^ (1 / (qOf M : ℝ)) := by
    rw [hsm_eq]
    push_cast
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hpow_le : (3 * (G.m : ℝ)) ^ (1 / (qOf M : ℝ)) ≤ ((2 ^ qExpPow M : ℕ) : ℝ) := by
    have hle : (3 * (G.m : ℝ)) ^ (1 / (qOf M : ℝ)) ≤
        ((3 * G.m : ℝ) + 1) ^ (1 / (qOf M : ℝ)) := by
      apply Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    exact le_trans hle (rpow_inv_qOf_le_two_pow_qExpPow hmM)
  set A := csGammaExp Kγ (4 * M) * K_int * qOf M
  set B := qExpPow M
  set E := A + B
  have hcs_le : (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) ≤ ((2 ^ A : ℕ) : ℝ) := by
    have hgamma_mono : (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ≤
        (Cited.csGamma Kγ (4 * M) : ℝ) := by
      exact_mod_cast csGamma_mono hsn_le
    have hge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (4 * M) : ℝ) := by
      exact_mod_cast (by rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ 2 (by decide) :
        1 ≤ Cited.csGamma Kγ (4 * M))
    have hpow_kq : K * (qOf M : ℝ) ≤ ((K_int * qOf M : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg _)
    have hcs_nn : (0 : ℝ) ≤ (Cited.csGamma Kγ (subdivGraph G).n : ℝ) := Nat.cast_nonneg _
    calc (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ))
        ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K * (qOf M : ℝ)) :=
          Real.rpow_le_rpow hcs_nn hgamma_mono (mul_nonneg hK0 (Nat.cast_nonneg _))
      _ ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ ((K_int * qOf M : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hge1 hpow_kq
      _ = ((2 ^ A : ℕ) : ℝ) := csGamma_rpow_nat_mul Kγ (4 * M) K_int (qOf M)
  have hprod : ((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
        (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) ≤
      3 * (G.m : ℝ) * ((2 ^ E : ℕ) : ℝ) := by
    rw [hpow1q]
    have hgm_nn : (0 : ℝ) ≤ 3 * (G.m : ℝ) := by positivity
    have h3m_nn : (0 : ℝ) ≤ (3 * (G.m : ℝ)) ^ (1 / (qOf M : ℝ)) := Real.rpow_nonneg hgm_nn _
    have hcs_rpow_nn : (0 : ℝ) ≤ (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc 3 * (G.m : ℝ) * (3 * (G.m : ℝ)) ^ (1 / (qOf M : ℝ)) *
          (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ))
        ≤ 3 * (G.m : ℝ) * ((2 ^ B : ℕ) : ℝ) * ((2 ^ A : ℕ) : ℝ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow_le hgm_nn) hcs_le hcs_rpow_nn
            (mul_nonneg hgm_nn (Nat.cast_nonneg _))
      _ = 3 * (G.m : ℝ) * (((2 ^ B : ℕ) : ℝ) * ((2 ^ A : ℕ) : ℝ)) := by ring
      _ = 3 * (G.m : ℝ) * ((2 ^ E : ℕ) : ℝ) := by rw [two_pow_mul_two_pow_cast B A]
  have hprod' : ((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
        (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) ≤
      ((3 * G.m : ℕ) : ℝ) * ((2 ^ E : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact hprod
  have hx0 : 0 ≤ ((subdivGraph G).m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
      (Cited.csGamma Kγ (subdivGraph G).n : ℝ) ^ (K * (qOf M : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hbd := nat_ceil_mul_add_one_le hK0 hK_le hK1 (by omega : 1 ≤ 3 * G.m) hx0 hprod'
    (Nat.one_le_pow E 2 (by decide))
  calc Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M)
      ≤ (3 * G.m + 1) * K_int * (2 ^ E + 1) := hbd
    _ ≤ 4 * K_int * G.m * (2 ^ E + 1) := by
        have h1 : 3 * G.m + 1 ≤ 4 * G.m := by omega
        nlinarith
    _ = 4 * K_int * G.m * csExpFactor Kγ K_int M := rfl

lemma csQuery_subdiv_le_csExpFactor {Kγ K_int : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {m M : ℕ} (hm : 3 * m ≤ 4 * M) :
    Cited.csQuery Kγ K (3 * m) (qOf M) ≤ 2 * K_int * csExpFactor Kγ K_int M := by
  have hK_le : K ≤ (K_int : ℝ) := le_trans (le_max_left K 1) hK
  have hK1 : 1 ≤ K_int := by
    have : (1 : ℝ) ≤ (K_int : ℝ) := le_trans (le_max_right K 1) hK
    exact_mod_cast this
  by_cases hK_neg : K ≤ 0
  · unfold Cited.csQuery
    have hnonpos : K * ((Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) + 1) ≤ 0 := by
      have hcs : 0 ≤ (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      exact mul_nonpos_of_nonpos_of_nonneg hK_neg (by linarith)
    rw [Nat.ceil_eq_zero.mpr hnonpos]
    exact Nat.zero_le _
  have hK0 : 0 ≤ K := le_of_not_ge hK_neg
  have hgamma_mono : (Cited.csGamma Kγ (3 * m) : ℝ) ≤ (Cited.csGamma Kγ (4 * M) : ℝ) := by
    exact_mod_cast csGamma_mono hm
  have hge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (4 * M) : ℝ) := by
    exact_mod_cast (by rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ 2 (by decide) :
      1 ≤ Cited.csGamma Kγ (4 * M))
  set A := csGammaExp Kγ (4 * M) * K_int * qOf M
  set E := A + qExpPow M
  have hpow_le : (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) ≤ ((2 ^ E : ℕ) : ℝ) := by
    have hcs_nn : (0 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := Nat.cast_nonneg _
    have hpow_kq : K * (qOf M : ℝ) ≤ ((K_int * qOf M : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg _)
    calc (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ))
        ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K * (qOf M : ℝ)) :=
          Real.rpow_le_rpow hcs_nn hgamma_mono (mul_nonneg hK0 (Nat.cast_nonneg _))
      _ ≤ (Cited.csGamma Kγ (4 * M) : ℝ) ^ ((K_int * qOf M : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hge1 hpow_kq
      _ = ((2 ^ A : ℕ) : ℝ) := csGamma_rpow_nat_mul Kγ (4 * M) K_int (qOf M)
      _ ≤ ((2 ^ E : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_add_right A (qExpPow M))
  have hpow' : (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) ≤
      ((1 : ℕ) : ℝ) * ((2 ^ E : ℕ) : ℝ) := by
    rw [Nat.cast_one, one_mul]; exact hpow_le
  have hx0 : 0 ≤ (Cited.csGamma Kγ (3 * m) : ℝ) ^ (K * (qOf M : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbd := nat_ceil_mul_add_one_le hK0 hK_le hK1 (le_rfl : 1 ≤ 1) hx0 hpow'
    (Nat.one_le_pow E 2 (by decide))
  rw [show (1 : ℕ) + 1 = 2 by rfl] at hbd
  exact hbd

end MinCostFlow.Expander.PathDSProg
