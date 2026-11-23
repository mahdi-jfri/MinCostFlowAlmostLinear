module

public import MinCostFlow.HierPaths.BuildNumHier

/-!
# The work of the construction is at most a constant times `m Γ`

`StaticContract` asks the static construction to cost at most `Ks · m · Γ`, with
`Γ = gammaHP a d M`. This file proves that the operation count `buildCost` of the construction
with the numbers of `numParams` meets this bound, for `D ≤ depthOf m + 1` depths
(`buildCost_le_gamma`).

The idea. The work per terminal at a depth is `F_j(2^b) ≤ T (A + 6 k^2 C' Z_j)` (`unitCost_le`),
with `A = N^2 W^{10 h^2 + 10}` the work of the core per vertex, `k = 2^b` children, and `Z_j` the
router's work per pair and per vertex. Each factor is a power of two:
`N^2 ≤ 2^{2h^2 + 4}`, `W ≤ 2^{c₁ + 6v}`, `k^2 ≤ 2^{2h^2 + 2}`, and `Z_j ≤ (1 + (2 + d)^4)^2 2^E`.
All exponents are at most a constant times `h^2 v`, and `Γ ≥ (1 + (2 + d)^4)^2 U^{2h + 2}` with
`U = 2^{a h v}`, so for `a` large enough (a constant that depends on `cfg`) the sum over the
depths and terminals fits.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

variable (B : BuildParams)

/-- The router's work per pair and per vertex, plus one. -/
def routeZ (bh : ℕ) : ℕ := (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2) + 1

/-- **The work per terminal at one depth**: `F(k) ≤ T (A + 6 k^2 C' Z)`. -/
theorem unitCost_le {cfg : ParamConfig} {C' bh k : ℕ} (hk : 1 ≤ k) :
    B.unitCost cfg C' bh k ≤
      B.T * ((NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) +
        6 * (k * k) * (C' * B.routeZ bh)) := by
  have hT : 1 ≤ B.T := by unfold T; omega
  set Zp := (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2)
  have hZ : B.routeZ bh = Zp + 1 := rfl
  have hQk : B.routeUnit C' bh k ≤ k * (C' * B.routeZ bh) := by
    unfold routeUnit
    rw [hZ]
    have : k * Zp + 1 ≤ k * (Zp + 1) := by rw [Nat.mul_add]; omega
    calc C' * (k * (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2) + 1)
        = C' * (k * Zp + 1) := by simp only [Zp]; ring_nf
      _ ≤ C' * (k * (Zp + 1)) := Nat.mul_le_mul_left _ this
      _ = k * (C' * (Zp + 1)) := by ring
  have hQ1 : B.routeUnit C' bh 1 ≤ C' * B.routeZ bh := by
    unfold routeUnit
    rw [hZ]
    calc C' * (1 * (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2) + 1)
        = C' * (Zp + 1) := by simp only [Zp]; ring_nf
      _ ≤ _ := le_rfl
  unfold unitCost
  set A := (NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10)
  set Y := C' * B.routeZ bh
  set Qk := B.routeUnit C' bh k
  set Q1 := B.routeUnit C' bh 1
  set T := B.T
  have hkk : k ≤ k * k := Nat.le_mul_of_pos_left _ hk
  have h1 : T * (2 * Qk) ≤ 2 * (T * (k * k) * Y) := by
    calc T * (2 * Qk) ≤ T * (2 * (k * Y)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQk)
      _ ≤ T * (2 * (k * k * Y)) := by gcongr
      _ = 2 * (T * (k * k) * Y) := by ring
  have h2 : 2 * Qk ≤ 2 * (T * (k * k) * Y) := by
    calc 2 * Qk ≤ 2 * (k * Y) := Nat.mul_le_mul_left _ hQk
      _ ≤ 2 * (1 * (k * k) * Y) := by gcongr; omega
      _ ≤ 2 * (T * (k * k) * Y) := by gcongr
  have h3 : k * k * (2 * Q1) ≤ 2 * (T * (k * k) * Y) := by
    calc k * k * (2 * Q1) ≤ k * k * (2 * Y) := by gcongr
      _ = 2 * (1 * (k * k) * Y) := by ring
      _ ≤ 2 * (T * (k * k) * Y) := by gcongr
  have e : T * (A + 6 * (k * k) * Y) = T * A + 6 * (T * (k * k) * Y) := by ring
  rw [e, Nat.mul_add]
  omega

/-- `Z ≤ 2^42 b̂^3 V^7` when `Δ ≤ 64 V` and `L ≤ V`. -/
theorem routeZ_le {V bh : ℕ} (hΔ : B.Δ ≤ 64 * V) (hL : B.L ≤ V) (hb : 1 ≤ bh) (hV : 1 ≤ V) :
    B.routeZ bh ≤ 2 ^ 42 * bh ^ 3 * V ^ 7 := by
  have hd : routePathLen B.Δ bh B.L + 1 ≤ 2 ^ 12 * bh * V ^ 2 := by
    have h1 : routePathLen B.Δ bh B.L ≤ 32 * (64 * V) * bh * V := by
      unfold routePathLen
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hΔ)) hL
    have h2 : 32 * (64 * V) * bh * V = 2 ^ 11 * (bh * V ^ 2) := by ring
    have h3 : 1 ≤ bh * V ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by positivity))
    have h4 : 2 ^ 12 * bh * V ^ 2 = 2 ^ 12 * (bh * V ^ 2) := by ring
    rw [h2] at h1
    rw [h4]
    generalize bh * V ^ 2 = W at *
    omega
  have hR : routeCong B.Δ bh B.L ≤ 2 ^ 22 * bh ^ 2 * V ^ 4 := by
    calc routeCong B.Δ bh B.L ≤ 16 * bh * (64 * V) * (2 ^ 12 * bh * V ^ 2) * V := by
          unfold routeCong routeBatchH
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΔ) hd) hL
      _ = 2 ^ 22 * bh ^ 2 * V ^ 4 := by ring
  have hΔ2 : B.Δ + 2 ≤ 2 ^ 7 * V := by omega
  have hpos : 1 ≤ bh ^ 3 * V ^ 7 := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by positivity) (by positivity))
  unfold routeZ
  have hmain : (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2) ≤
      2 ^ 41 * (bh ^ 3 * V ^ 7) := by
    calc _ ≤ (2 ^ 12 * bh * V ^ 2) * (2 ^ 22 * bh ^ 2 * V ^ 4) * (2 ^ 7 * V) :=
          Nat.mul_le_mul (Nat.mul_le_mul hd hR) hΔ2
      _ = 2 ^ 41 * (bh ^ 3 * V ^ 7) := by ring
  have e : 2 ^ 42 * bh ^ 3 * V ^ 7 = 2 ^ 42 * (bh ^ 3 * V ^ 7) := by ring
  rw [e]
  generalize bh ^ 3 * V ^ 7 = W at *
  omega

end BuildParams

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- **The exponents fit**: with `c₁ = 89 + a₀ + 3 c₀ A` and `K = 87 + a₀`, the exponent of the
work is at most `a h v (2h + 2)` when `a ≥ 10 c₁ + 2K + 120`. -/
theorem exp_gamma {a c₁ K h v : ℕ} (ha : 10 * c₁ + 2 * K + 120 ≤ a) (hh : 1 ≤ h) (hv : 1 ≤ v) :
    h + v + (2 * h ^ 2 + 4 + (c₁ + 6 * v) * (10 * h ^ 2 + 10) +
      (63 + 7 * v + 3 * (h * (K + 6 * v)))) ≤ a * h * v * (2 * h + 2) := by
  have hhv : 1 ≤ h * v := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hQ1 : 1 ≤ h * h * v :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
  have hhQ : h ≤ h * h * v := by
    calc h = h * 1 * 1 := by ring
      _ ≤ h * h * v := by gcongr
  have hvQ : v ≤ h * h * v := by
    calc v = 1 * 1 * v := by ring
      _ ≤ h * h * v := by gcongr
  have hh2 : h * h ≤ h * h * v := Nat.le_mul_of_pos_right _ hv
  have hhvQ : h * v ≤ h * h * v := by
    calc h * v = 1 * h * v := by ring
      _ ≤ h * h * v := by gcongr
  have hc1 : c₁ * (h * h) ≤ c₁ * (h * h * v) := Nat.mul_le_mul_left _ hh2
  have hc2 : c₁ ≤ c₁ * (h * h * v) := Nat.le_mul_of_pos_right _ hQ1
  have hK : K * h ≤ K * (h * h * v) := Nat.mul_le_mul_left _ hhQ
  have hA : (10 * c₁ + 2 * K + 120) * (h * h * v) ≤ a * (h * h * v) := Nat.mul_le_mul_right _ ha
  have eL : h + v + (2 * h ^ 2 + 4 + (c₁ + 6 * v) * (10 * h ^ 2 + 10) +
      (63 + 7 * v + 3 * (h * (K + 6 * v)))) =
      h + v + 2 * (h * h) + 67 + 10 * (c₁ * (h * h)) + 10 * c₁ + 60 * (h * h * v) + 67 * v +
        3 * (K * h) + 18 * (h * v) := by ring
  have eR : a * h * v * (2 * h + 2) = 2 * (a * (h * h * v)) + 2 * (a * (h * v)) := by ring
  have eA : (10 * c₁ + 2 * K + 120) * (h * h * v) =
      10 * (c₁ * (h * h * v)) + 2 * (K * (h * h * v)) + 120 * (h * h * v) := by ring
  rw [eL, eR]
  rw [eA] at hA
  generalize h * h * v = Q at *
  generalize h * h = H2 at *
  generalize h * v = HV at *
  generalize c₁ * Q = CQ at *
  generalize c₁ * H2 = CH at *
  generalize K * Q = KQ at *
  generalize K * h = KH at *
  generalize a * Q = AQ at *
  generalize a * HV = AHV at *
  omega

namespace BuildParams

section num

variable {route : RouterFn} {core : ℕ → Graph → CoreResult} {G : Graph}

/-- `N^2 ≤ 2^{2h^2 + 4}`: `ℓ ≤ x + 2 ≤ h^3 + 2`, so `⌈ℓ/h⌉ ≤ h^2 + 2`. -/
theorem num_N_sq (hxX : (numParams route core G).x ≤ xOf G.m) :
    (NOf (numParams route core G).M (numParams route core G).r) ^ 2 ≤
      2 ^ (2 * depthOf G.m ^ 2 + 4) := by
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  have hX3 : xOf G.m ≤ h ^ 3 := le_ceilRoot_pow 2 (xOf G.m)
  have hell := (ell_two_pow (numParams route core G).x).2
  have hM : (numParams route core G).M = 2 ^ (numParams route core G).x := rfl
  have hr : (numParams route core G).r = h := rfl
  unfold NOf
  rw [hM, hr, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  have hcd : ceilDiv (ell (2 ^ (numParams route core G).x)) h ≤ h ^ 2 + 2 := by
    unfold ceilDiv
    apply Nat.div_le_of_le_mul
    have e : h * (h ^ 2 + 2) = h ^ 3 + 2 * h := by ring
    rw [e]
    omega
  have : max 2 (ceilDiv (ell (2 ^ (numParams route core G).x)) h) ≤ h ^ 2 + 2 :=
    max_le (by omega) hcd
  omega

/-- `(2^b)^2 ≤ 2^{2h^2 + 2}`: `b = ⌈x/h⌉ ≤ h^2 + 1`. -/
theorem num_k_sq : (2 ^ (numParams route core G).b) ^ 2 ≤ 2 ^ (2 * depthOf G.m ^ 2 + 2) := by
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  have hX3 : xOf G.m ≤ h ^ 3 := le_ceilRoot_pow 2 (xOf G.m)
  have hb : (numParams route core G).b ≤ h ^ 2 + 1 := by
    show (xOf G.m + h - 1) / h ≤ _
    apply Nat.div_le_of_le_mul
    have e : h * (h ^ 2 + 1) = h ^ 3 + h := by ring
    rw [e]
    omega
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- `W ≤ 2^{c₁ + 6 v}` with `c₁ = 90 + a₀ + 3 c₀ A`, when `ℓ(M) ≤ 2^v`. -/
theorem num_W_le {cfg : ParamConfig} {M v : ℕ} (hV : ell M ≤ 2 ^ v) :
    WParam cfg M ≤ 2 ^ (90 + cfg.a₀ + 3 * cfg.c0 * cfg.A + 6 * v) := by
  have hF := FParam_le (cfg := cfg) hV Nat.one_le_two_pow
  set c := 3 * cfg.c0 * cfg.A
  have ha : cfg.a₀ ≤ 2 ^ cfg.a₀ := (Nat.lt_two_pow_self).le
  have hc : c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
  set V6 := (2 ^ v) ^ 6 with hV6def
  have hV6 : 1 ≤ V6 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hV1 : 2 ^ v ≤ V6 := Nat.le_self_pow (by norm_num) _
  set Z := 2 ^ 87 * 2 ^ cfg.a₀ * 2 ^ c with hZ
  have h87 : 1 ≤ 2 ^ 87 := Nat.one_le_two_pow
  have hA1 : 1 ≤ 2 ^ cfg.a₀ := Nat.one_le_two_pow
  have hC1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hZ1 : 1 ≤ Z := by
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ Z := by rw [hZ]; gcongr
  have hcZ : c ≤ Z := by
    calc c ≤ 1 * 1 * 2 ^ c := by rw [one_mul, one_mul]; exact hc
      _ ≤ Z := by rw [hZ]; gcongr
  have haZ : 2 ^ 87 * cfg.a₀ ≤ Z := by
    calc 2 ^ 87 * cfg.a₀ = 2 ^ 87 * cfg.a₀ * 1 := by ring
      _ ≤ Z := by rw [hZ]; gcongr
  have hFZ : FParam cfg M ≤ Z * V6 := hF.trans (Nat.mul_le_mul_right _ haZ)
  have hL : LParam M ≤ 4 * V6 := by unfold LParam; omega
  have hZV : Z ≤ Z * V6 := Nat.le_mul_of_pos_right _ hV6
  have hZV' : V6 ≤ Z * V6 := Nat.le_mul_of_pos_left _ hZ1
  have hW : WParam cfg M ≤ 8 * (Z * V6) := by
    unfold WParam
    omega
  calc WParam cfg M ≤ 8 * (Z * V6) := hW
    _ = 2 ^ (90 + cfg.a₀ + c + 6 * v) := by
        rw [hZ, hV6def, ← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add,
          ← pow_add, ← pow_add]
        ring_nf

/-- **The router's work per depth**: `Z_j ≤ (1 + (2 + d)^4)^2 2^E` with
`E = 63 + 7 v + 3 h (K + 6 v)` and `K = 87 + a₀`. -/
theorem num_Z_le {cfg : ParamConfig} {dd : ℕ} (hd : 1 ≤ dd)
    (hxX : (numParams route core G).x ≤ xOf G.m) (j : ℕ) :
    (numParams route core G).routeZ ((numParams route core G).numBh cfg dd j) ≤
      (1 + (2 + dd) ^ 4) ^ 2 *
        2 ^ (63 + 7 * vxOf G.m + 3 * (depthOf G.m * (87 + cfg.a₀ + 6 * vxOf G.m))) := by
  set B := numParams route core G with hB
  obtain ⟨hV, _⟩ := num_v G.m
  set v := vxOf G.m
  set h := depthOf G.m
  have hxc : Nat.clog 2 (portCount G) ≤ xOf G.m := hxX
  have hΔ : B.Δ ≤ 64 * 2 ^ v := by
    show 49 * (Nat.clog 2 (portCount G) + 1) + 2 ≤ _; omega
  have hL : B.L ≤ 2 ^ v := by show Nat.clog 2 (portCount G) + 1 ≤ _; omega
  have hpow : (2 ^ v) ^ 7 = 2 ^ (7 * v) := by rw [← pow_mul, Nat.mul_comm]
  have hDd : 1 ≤ (1 + (2 + dd) ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  cases j with
  | zero =>
    have hZ := B.routeZ_le (bh := 100 * dd) hΔ hL (by omega) Nat.one_le_two_pow
    have hd3 : dd ^ 3 ≤ (1 + (2 + dd) ^ 4) ^ 2 :=
      calc dd ^ 3 ≤ (2 + dd) ^ 8 :=
            (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
        _ = ((2 + dd) ^ 4) ^ 2 := by ring
        _ ≤ (1 + (2 + dd) ^ 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    show B.routeZ (100 * dd) ≤ _
    calc B.routeZ (100 * dd) ≤ 2 ^ 42 * (100 * dd) ^ 3 * (2 ^ v) ^ 7 := hZ
      _ = 2 ^ 42 * 1000000 * dd ^ 3 * 2 ^ (7 * v) := by rw [hpow]; ring
      _ ≤ 2 ^ 62 * dd ^ 3 * 2 ^ (7 * v) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
      _ = dd ^ 3 * 2 ^ (62 + 7 * v) := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul hd3 (Nat.pow_le_pow_right (by norm_num) (by omega))
  | succ j =>
    have hP1 := one_le_PParam cfg B.M B.r
    have hZ := B.routeZ_le (bh := 4 * PParam cfg B.M B.r) hΔ hL (by omega) Nat.one_le_two_pow
    have hell : ell B.M ≤ 2 ^ v := by
      have := (ell_two_pow (Nat.clog 2 (portCount G))).2
      show ell (2 ^ Nat.clog 2 (portCount G)) ≤ _
      omega
    have hP := PParam_le (cfg := cfg) hell B.r
    have hr : B.r = h := rfl
    rw [hr] at hP
    show B.routeZ (4 * PParam cfg B.M B.r) ≤ _
    calc B.routeZ (4 * PParam cfg B.M B.r) ≤ 2 ^ 42 * (4 * PParam cfg B.M B.r) ^ 3 * (2 ^ v) ^ 7 :=
          hZ
      _ = 2 ^ 48 * PParam cfg B.M B.r ^ 3 * 2 ^ (7 * v) := by rw [hpow]; ring
      _ ≤ 2 ^ 48 * (2 ^ (h * (87 + cfg.a₀ + 6 * v))) ^ 3 * 2 ^ (7 * v) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 3))
      _ = 2 ^ (48 + 3 * (h * (87 + cfg.a₀ + 6 * v)) + 7 * v) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 1 * 2 ^ (63 + 7 * v + 3 * (h * (87 + cfg.a₀ + 6 * v))) := by
          rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.mul_le_mul_right _ hDd

end num

/-- `Γ ≥ (1 + (2 + d)^4)^2 U^{2h + 2}` with `U = uOf a m`, for `m ≤ M`. -/
theorem gammaHP_ge (a d : ℕ) {m M : ℕ} (hmM : m ≤ M) :
    (1 + (2 + d) ^ 4) ^ 2 * uOf a m ^ (2 * depthOf m + 2) ≤ gammaHP a d M := by
  have hU := uOf_le_bigUX a hmM
  have hJ := depthOf_le_bigJ hmM
  have hU1 := one_le_uOf a m
  have h1 : uOf a m ^ (2 * depthOf m + 2) ≤ bigUX a M ^ (2 * bigJ M + 2) :=
    (Nat.pow_le_pow_left hU _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hc : 1 ≤ 2 ^ 12 * (bigJ M + 2) ^ 4 * 4 ^ (bigJ M + 1) * (bigKB M + 1) ^ 4 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold gammaHP
  calc (1 + (2 + d) ^ 4) ^ 2 * uOf a m ^ (2 * depthOf m + 2)
      ≤ 1 * ((1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2)) := by
        rw [one_mul]; exact Nat.mul_le_mul_left _ h1
    _ ≤ (2 ^ 12 * (bigJ M + 2) ^ 4 * 4 ^ (bigJ M + 1) * (bigKB M + 1) ^ 4) *
        ((1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2)) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

section main

variable {route : RouterFn} {routeCost : RouterCostFn} {core : ℕ → Graph → CoreResult}
  {G : Graph}

/-- **The work of the construction is `O(m Γ)`.** With the numbers of `numParams` and the router
scales `numBh`, the work over `D ≤ depthOf m + 1` depths is at most `2^11 (C + 3) m Γ`, where
`C` is the router's constant and `a ≥ 10 c₁ + 2 K + 120` (`c₁ = 90 + a₀ + 3 c₀ A`,
`K = 87 + a₀`). -/
theorem buildCost_le_gamma (hrouter : IsMatchingPlayer route routeCost) {C : ℕ}
    (hC : RouteCostLe routeCost C) {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ}
    (hcore : IsCorePlayer cfg (numParams route core G).M (numParams route core G).r core coreCost)
    (hG : G.IsValid) (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ)
    (hcond : G.IsConductanceExpanderOn G.verts φ) {a dd M : ℕ}
    (ha : 10 * (90 + cfg.a₀ + 3 * cfg.c0 * cfg.A) + 2 * (87 + cfg.a₀) + 120 ≤ a)
    (hd : 1 ≤ dd) (hφd : 1 / (dd : ℝ) ≤ φ) (hmM : G.m ≤ M) {D : ℕ} (hD : D ≤ depthOf G.m + 1) :
    (numParams route core G).buildCost routeCost coreCost
        (hostGraph ExplicitExpander.explicitGraph G) D ≤
      2 ^ 11 * (C + 3) * G.m * gammaHP a dd M := by
  set B := numParams route core G with hB
  have hyp := num_buildHyp (route := route) (core := core) (cfg := cfg) hG hm hφ hcond hd hφd
  have hcost := buildCost_le (B := B) hrouter hC hcore hyp D
  obtain ⟨hlt, hxX⟩ := num_x (route := route) (core := core) hG hm hφ hcond
  obtain ⟨hV, hv1⟩ := num_v G.m
  set v := vxOf G.m
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  set c₁ := 90 + cfg.a₀ + 3 * cfg.c0 * cfg.A
  set K := 87 + cfg.a₀
  set Dd := (1 + (2 + dd) ^ 4) ^ 2
  set E := 63 + 7 * v + 3 * (h * (K + 6 * v))
  set e := 10 * h ^ 2 + 10
  set S := 2 * h ^ 2 + 4 + (c₁ + 6 * v) * e + E
  have hDd : 1 ≤ Dd := Nat.one_le_pow _ _ (by omega)
  -- the factors
  have hxc : Nat.clog 2 (portCount G) ≤ xOf G.m := hxX
  have hT : B.T ≤ 2 ^ 6 * 2 ^ v := by
    show 49 * (Nat.clog 2 (portCount G) + 1) + 1 ≤ _; omega
  have hN := num_N_sq (route := route) (core := core) hxX
  have hk := num_k_sq (route := route) (core := core) (G := G)
  have hell : ell B.M ≤ 2 ^ v := by
    have := (ell_two_pow (Nat.clog 2 (portCount G))).2
    show ell (2 ^ Nat.clog 2 (portCount G)) ≤ _
    omega
  have hW : (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) ≤ 2 ^ ((c₁ + 6 * v) * e) := by
    rw [pow_mul 2 (c₁ + 6 * v) e]
    exact Nat.pow_le_pow_left (num_W_le hell) _
  have hA : (NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) ≤
      2 ^ (2 * h ^ 2 + 4 + (c₁ + 6 * v) * e) := by
    rw [pow_add 2 (2 * h ^ 2 + 4)]; exact Nat.mul_le_mul hN hW
  have hk2 : 2 ^ B.b * 2 ^ B.b ≤ 2 ^ (2 * h ^ 2 + 2) := by rw [← sq]; exact hk
  -- one term
  have hterm : ∀ j, 2 ^ B.x * B.unitCost cfg (C + 2) (B.numBh cfg dd j) (2 ^ B.b) ≤
      1792 * (C + 3) * G.m * Dd * 2 ^ (v + S) := by
    intro j
    have hu := B.unitCost_le (cfg := cfg) (C' := C + 2) (bh := B.numBh cfg dd j)
      (k := 2 ^ B.b) Nat.one_le_two_pow
    have hZ := num_Z_le (route := route) (core := core) (cfg := cfg) hd hxX j
    have hS1 : 2 ^ (2 * h ^ 2 + 4 + (c₁ + 6 * v) * e) ≤ 2 ^ S :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hS2 : 2 ^ (2 * h ^ 2 + 2) * 2 ^ E ≤ 2 ^ S := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hinner : (NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) +
        6 * (2 ^ B.b * 2 ^ B.b) * ((C + 2) * B.routeZ (B.numBh cfg dd j)) ≤
        7 * (C + 3) * Dd * 2 ^ S := by
      have h1 : 6 * (2 ^ B.b * 2 ^ B.b) * ((C + 2) * B.routeZ (B.numBh cfg dd j)) ≤
          6 * (C + 3) * Dd * (2 ^ (2 * h ^ 2 + 2) * 2 ^ E) := by
        calc 6 * (2 ^ B.b * 2 ^ B.b) * ((C + 2) * B.routeZ (B.numBh cfg dd j))
            ≤ 6 * 2 ^ (2 * h ^ 2 + 2) * ((C + 3) * (Dd * 2 ^ E)) := by gcongr; omega
          _ = 6 * (C + 3) * Dd * (2 ^ (2 * h ^ 2 + 2) * 2 ^ E) := by ring
      have h2 : 6 * (C + 3) * Dd * (2 ^ (2 * h ^ 2 + 2) * 2 ^ E) ≤ 6 * (C + 3) * Dd * 2 ^ S :=
        Nat.mul_le_mul_left _ hS2
      have h3 : (NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) ≤
          (C + 3) * Dd * 2 ^ S := by
        exact (hA.trans hS1).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
      have e7 : 7 * (C + 3) * Dd * 2 ^ S = (C + 3) * Dd * 2 ^ S + 6 * (C + 3) * Dd * 2 ^ S := by
        generalize 2 ^ S = Y; ring
      rw [e7]
      exact Nat.add_le_add h3 (h1.trans h2)
    have hx4 : 2 ^ B.x ≤ 4 * G.m := hlt.le
    calc 2 ^ B.x * B.unitCost cfg (C + 2) (B.numBh cfg dd j) (2 ^ B.b)
        ≤ (4 * G.m) * (2 ^ 6 * 2 ^ v * (7 * (C + 3) * Dd * 2 ^ S)) :=
          Nat.mul_le_mul hx4 (hu.trans (Nat.mul_le_mul hT hinner))
      _ = 1792 * (C + 3) * G.m * Dd * 2 ^ (v + S) := by
          rw [pow_add 2 v S]; generalize 2 ^ S = Y; generalize 2 ^ v = Y'; ring
  -- the sum over the depths
  have hD2 : D ≤ 2 ^ h := le_trans hD Nat.lt_two_pow_self
  have hexp := exp_gamma (c₁ := c₁) (K := K) ha hh hv1
  have hsum : ∑ j ∈ Finset.range D, 2 ^ B.x * B.unitCost cfg (C + 2) (B.numBh cfg dd j)
      (2 ^ B.b) ≤ 2 ^ h * (1792 * (C + 3) * G.m * Dd * 2 ^ (v + S)) := by
    calc _ ≤ ∑ _j ∈ Finset.range D, 1792 * (C + 3) * G.m * Dd * 2 ^ (v + S) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = D * (1792 * (C + 3) * G.m * Dd * 2 ^ (v + S)) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hD2
  have hU : 2 ^ (h + (v + S)) ≤ uOf a G.m ^ (2 * h + 2) := by
    unfold uOf
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have : h + (v + S) = h + v + (2 * h ^ 2 + 4 + (c₁ + 6 * v) * (10 * h ^ 2 + 10) +
        (63 + 7 * v + 3 * (h * (K + 6 * v)))) := by simp only [S, E, e]; ring
    rw [this]
    exact hexp
  have hΓ := gammaHP_ge a dd hmM
  calc B.buildCost routeCost coreCost (hostGraph ExplicitExpander.explicitGraph G) D
      ≤ 2 ^ h * (1792 * (C + 3) * G.m * Dd * 2 ^ (v + S)) := hcost.trans hsum
    _ = 1792 * (C + 3) * G.m * (Dd * 2 ^ (h + (v + S))) := by
        rw [pow_add 2 h (v + S)]; generalize 2 ^ (v + S) = Y; generalize 2 ^ h = Y'; ring
    _ ≤ 2 ^ 11 * (C + 3) * G.m * (Dd * uOf a G.m ^ (2 * h + 2)) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
        · exact Nat.mul_le_mul_left _ hU
    _ ≤ 2 ^ 11 * (C + 3) * G.m * gammaHP a dd M := Nat.mul_le_mul_left _ hΓ

end main

end BuildParams

end MinCostFlow.HierPaths
