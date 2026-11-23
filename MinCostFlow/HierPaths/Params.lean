module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Log

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The numbers of the hierarchy of embedded matchings

The path data structure without a cited result is a hierarchy of groups of terminals, with a
stored matching between every two sibling groups. Its size depends on the edge count `m` of the
input graph through a few integers. This file defines them, and one number `Γ` that bounds every
cost and every loss of the structure, as a function of `d = ⌈1/φ⌉` and of an upper bound `M` on
`m`.

For an actual edge count `m` the integers are, with a fixed constant `a`,
`x = ⌈log₂(8m + 8)⌉`, the depth `h = ⌈x^{1/3}⌉`, the branching `B = 2^{⌈x/h⌉}`,
`v_x = ⌈log₂(x + 2)⌉`, `U = 2^{a h v_x}`, `V = U^h`, `H = (2 + d)^4`, the walk length `λ = H V`
and the edge load `ξ = h B² λ`. For an upper bound `M` the matching numbers are
`X = ⌈log₂(8M + 8)⌉`, `j = ⌈X^{1/3}⌉`, `K_B = 2^{1 + ⌈X^{2/3}⌉}`,
`U_X = 2^{a j ⌈log₂(X + 2)⌉}`, and
`Γ = 2^12 (j + 2)^4 4^{j+1} (K_B + 1)^4 (1 + (2 + d)^4)^2 U_X^{2j+2}`.
The roots are integer ceilings: `⌈n^{1/3}⌉` is the least `r` with `n ≤ r^3`.

We prove that the numbers for `M` dominate those for `m ≤ M` (`xOf_le_bigX`, `depthOf_le_bigJ`,
`branchOf_le_bigKB`, `uOf_le_bigUX`), that `Γ` is monotone with `max 2 d ≤ Γ`, and that `Γ`
bounds the four quantities that the analysis of the structure needs: the loss factor `4^h ξ`
(`lossFactor_le_gamma`), the walk length `(2^h + 1) λ` (`pathLen_le_gamma`), the coefficient
`(1 + ξ)(h + 2) 4^h (1 + h B)(1 + λ)` of the deletion time (`delCoeff_le_gamma`), the factor
`(h + 1)(B + 1)^2 H U^{h+1}` of the initialization time (`initFactor_le_gamma`), and the query
factor `2^h (1 + λ)` (`queryFactor_le_gamma`). These bounds use `2 + d`, which is at least `2 + 1/φ`
since `1/φ ≤ d`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-! ## Integer roots -/

/-- `ceilRoot k n` is the least `r` with `n ≤ r^(k+1)`, that is `⌈n^{1/(k+1)}⌉`. -/
def ceilRoot (k n : ℕ) : ℕ :=
  Nat.find (p := fun r => n ≤ r ^ (k + 1)) ⟨n, Nat.le_self_pow (Nat.succ_ne_zero k) n⟩

lemma le_ceilRoot_pow (k n : ℕ) : n ≤ ceilRoot k n ^ (k + 1) :=
  Nat.find_spec (p := fun r => n ≤ r ^ (k + 1)) _

lemma ceilRoot_le {k n r : ℕ} (h : n ≤ r ^ (k + 1)) : ceilRoot k n ≤ r :=
  Nat.find_min' (p := fun r => n ≤ r ^ (k + 1)) _ h

lemma ceilRoot_mono (k : ℕ) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : ceilRoot k n₁ ≤ ceilRoot k n₂ :=
  ceilRoot_le (le_trans h (le_ceilRoot_pow k n₂))

/-- Below the root the power is smaller than `n`. -/
lemma pow_lt_of_lt_ceilRoot {k n r : ℕ} (h : r < ceilRoot k n) : r ^ (k + 1) < n := by
  have := Nat.find_min (p := fun r => n ≤ r ^ (k + 1)) _ h
  omega

lemma ceilRoot_le_self (k n : ℕ) : ceilRoot k n ≤ n :=
  ceilRoot_le (Nat.le_self_pow (Nat.succ_ne_zero k) n)

lemma one_lt_ceilRoot {k n : ℕ} (hn : 2 ≤ n) : 2 ≤ ceilRoot k n := by
  by_contra hlt
  have h1 : ceilRoot k n ≤ 1 := by omega
  have := le_trans (le_ceilRoot_pow k n) (Nat.pow_le_pow_left h1 _)
  simp at this
  omega

/-! ## The numbers for an actual edge count `m` -/

/-- `x = ⌈log₂(8m + 8)⌉`. -/
def xOf (m : ℕ) : ℕ := Nat.clog 2 (8 * m + 8)

/-- The depth `h = ⌈x^{1/3}⌉`. -/
def depthOf (m : ℕ) : ℕ := ceilRoot 2 (xOf m)

/-- The number `⌈x/h⌉` of index bits that one level of the hierarchy uses. -/
def branchBits (m : ℕ) : ℕ := (xOf m + depthOf m - 1) / depthOf m

/-- The branching `B = 2^{⌈x/h⌉}`. -/
def branchOf (m : ℕ) : ℕ := 2 ^ branchBits m

/-- `v_x = ⌈log₂(x + 2)⌉`. -/
def vxOf (m : ℕ) : ℕ := Nat.clog 2 (xOf m + 2)

/-- `U = 2^{a h v_x}`. -/
def uOf (a m : ℕ) : ℕ := 2 ^ (a * depthOf m * vxOf m)

/-- `V = U^h`. -/
def vOf (a m : ℕ) : ℕ := uOf a m ^ depthOf m

/-- `H = (2 + d)^4`, with `d = ⌈1/φ⌉` in place of `1/φ`. -/
def hOf (d : ℕ) : ℕ := (2 + d) ^ 4

/-- The walk length bound `λ = H V`. -/
def lamOf (a d m : ℕ) : ℕ := hOf d * vOf a m

/-- The load bound `ξ = h B² λ`. -/
def xiOf (a d m : ℕ) : ℕ := depthOf m * branchOf m ^ 2 * lamOf a d m

/-- The loss factor `4^h ξ` of the loss bounds. -/
def lossFactor (a d m : ℕ) : ℕ := 4 ^ depthOf m * xiOf a d m

/-- The walk length bound `(2^h + 1) λ`. -/
def pathLen (a d m : ℕ) : ℕ := (2 ^ depthOf m + 1) * lamOf a d m

/-- The coefficient `(1 + ξ)(h + 2) 4^h (1 + h B)(1 + λ)` of `t` in the deletion cost bound. -/
def delCoeff (a d m : ℕ) : ℕ :=
  (1 + xiOf a d m) * (depthOf m + 2) * 4 ^ depthOf m * (1 + depthOf m * branchOf m) *
    (1 + lamOf a d m)

/-- The factor `(h + 1)(B + 1)^2 H U^{h+1}` of the initialization cost. -/
def initFactor (a d m : ℕ) : ℕ :=
  (depthOf m + 1) * (branchOf m + 1) ^ 2 * hOf d * uOf a m ^ (depthOf m + 1)

/-- The query factor `2^h (1 + λ)`. -/
def queryFactor (a d m : ℕ) : ℕ := 2 ^ depthOf m * (1 + lamOf a d m)

/-! ## The numbers for an upper bound `M` -/

/-- `X = ⌈log₂(8M + 8)⌉`. -/
def bigX (M : ℕ) : ℕ := Nat.clog 2 (8 * M + 8)

/-- `j = ⌈X^{1/3}⌉`. -/
def bigJ (M : ℕ) : ℕ := ceilRoot 2 (bigX M)

/-- `K_B = 2^{1 + ⌈X^{2/3}⌉}`. -/
def bigKB (M : ℕ) : ℕ := 2 ^ (1 + ceilRoot 2 (bigX M ^ 2))

/-- `U_X = 2^{a j ⌈log₂(X + 2)⌉}`. -/
def bigUX (a M : ℕ) : ℕ := 2 ^ (a * bigJ M * Nat.clog 2 (bigX M + 2))

/-- The number `Γ`, with `2 + d` in place of `2 + 1/φ`. -/
def gammaHP (a d M : ℕ) : ℕ :=
  2 ^ 12 * (bigJ M + 2) ^ 4 * 4 ^ (bigJ M + 1) * (bigKB M + 1) ^ 4 * (1 + (2 + d) ^ 4) ^ 2 *
    bigUX a M ^ (2 * bigJ M + 2)

/-! ## Basic facts -/

lemma bigX_eq_xOf (M : ℕ) : bigX M = xOf M := rfl

lemma three_le_xOf (m : ℕ) : 3 ≤ xOf m := by
  unfold xOf
  by_contra h
  have h2 : Nat.clog 2 (8 * m + 8) ≤ 2 := by omega
  have := (Nat.clog_le_iff_le_pow (by decide)).mp h2
  omega

lemma two_le_depthOf (m : ℕ) : 2 ≤ depthOf m :=
  one_lt_ceilRoot (by have := three_le_xOf m; omega)

lemma xOf_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : xOf m₁ ≤ xOf m₂ :=
  Nat.clog_mono_right 2 (by omega)

lemma bigX_mono {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) : bigX M₁ ≤ bigX M₂ := xOf_mono h

lemma bigJ_mono {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) : bigJ M₁ ≤ bigJ M₂ :=
  ceilRoot_mono 2 (bigX_mono h)

lemma bigKB_mono {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) : bigKB M₁ ≤ bigKB M₂ :=
  Nat.pow_le_pow_right (by decide)
    (by have := ceilRoot_mono 2 (Nat.pow_le_pow_left (bigX_mono h) 2); omega)

lemma bigUX_mono (a : ℕ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) : bigUX a M₁ ≤ bigUX a M₂ := by
  unfold bigUX
  apply Nat.pow_le_pow_right (by decide)
  have h1 := bigJ_mono h
  have h2 : Nat.clog 2 (bigX M₁ + 2) ≤ Nat.clog 2 (bigX M₂ + 2) :=
    Nat.clog_mono_right 2 (by have := bigX_mono h; omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left a h1) h2

lemma one_le_bigUX (a M : ℕ) : 1 ≤ bigUX a M := Nat.one_le_two_pow

lemma one_le_uOf (a m : ℕ) : 1 ≤ uOf a m := Nat.one_le_two_pow

lemma one_le_branchOf (m : ℕ) : 1 ≤ branchOf m := Nat.one_le_two_pow

/-! ## The numbers for `M` dominate those for `m ≤ M` -/

lemma xOf_le_bigX {m M : ℕ} (h : m ≤ M) : xOf m ≤ bigX M := xOf_mono h

lemma depthOf_le_bigJ {m M : ℕ} (h : m ≤ M) : depthOf m ≤ bigJ M :=
  ceilRoot_mono 2 (xOf_le_bigX h)

lemma vxOf_le {m M : ℕ} (h : m ≤ M) : vxOf m ≤ Nat.clog 2 (bigX M + 2) :=
  Nat.clog_mono_right 2 (by have := xOf_le_bigX h; omega)

/-- `⌈x/h⌉ ≤ ⌈x^{2/3}⌉`: from `x ≤ h^3` and `x^2 ≤ r^3` we get `x^3 ≤ (h r)^3`, so `x ≤ h r`. -/
lemma branchBits_le_ceilRoot (m : ℕ) : branchBits m ≤ ceilRoot 2 (xOf m ^ 2) := by
  set x := xOf m
  set h := depthOf m
  set r := ceilRoot 2 (x ^ 2)
  have hh : x ≤ h ^ 3 := le_ceilRoot_pow 2 x
  have hr : x ^ 2 ≤ r ^ 3 := le_ceilRoot_pow 2 (x ^ 2)
  have h2 : 2 ≤ h := two_le_depthOf m
  have hcube : x ^ 3 ≤ (h * r) ^ 3 := by
    calc x ^ 3 = x * x ^ 2 := by ring
      _ ≤ h ^ 3 * r ^ 3 := Nat.mul_le_mul hh hr
      _ = (h * r) ^ 3 := by ring
  have hxhr : x ≤ h * r := (Nat.pow_le_pow_iff_left (by decide)).mp hcube
  show (x + h - 1) / h ≤ r
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  calc x + h - 1 < h * r + h := by omega
    _ = (r + 1) * h := by ring

/-- The levels end by depth `h`: `⌈x / ⌈x/h⌉⌉ ≤ h`. -/
lemma depth_bound (m : ℕ) :
    (xOf m + branchBits m - 1) / branchBits m ≤ depthOf m ∧ 1 ≤ branchBits m := by
  set x := xOf m
  set h := depthOf m
  have h2 : 2 ≤ h := two_le_depthOf m
  have hx3 : 3 ≤ x := three_le_xOf m
  have hb : x ≤ h * branchBits m := by
    show x ≤ h * ((x + h - 1) / h)
    have := Nat.div_add_mod (x + h - 1) h
    have := Nat.mod_lt (x + h - 1) (show 0 < h by omega)
    generalize h * ((x + h - 1) / h) = P at *
    omega
  have hb1 : 1 ≤ branchBits m := by
    rcases Nat.eq_zero_or_pos (branchBits m) with h0 | h0
    · rw [h0] at hb; omega
    · exact h0
  refine ⟨?_, hb1⟩
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  calc x + branchBits m - 1 < h * branchBits m + branchBits m := by omega
    _ = (h + 1) * branchBits m := by ring

lemma branchOf_le_bigKB {m M : ℕ} (h : m ≤ M) : branchOf m ≤ bigKB M := by
  unfold branchOf bigKB
  apply Nat.pow_le_pow_right (by decide)
  have h1 := branchBits_le_ceilRoot m
  have h2 : ceilRoot 2 (xOf m ^ 2) ≤ ceilRoot 2 (bigX M ^ 2) :=
    ceilRoot_mono 2 (Nat.pow_le_pow_left (xOf_le_bigX h) 2)
  omega

lemma uOf_le_bigUX (a : ℕ) {m M : ℕ} (h : m ≤ M) : uOf a m ≤ bigUX a M := by
  unfold uOf bigUX
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left a (depthOf_le_bigJ h)) (vxOf_le h)

/-! ## Monotonicity of `Γ` and `max 2 d ≤ Γ` -/

lemma gammaHP_mono (a : ℕ) {d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    gammaHP a d₁ M₁ ≤ gammaHP a d₂ M₂ := by
  unfold gammaHP
  have hj := bigJ_mono hM
  have hK := bigKB_mono hM
  have hU := bigUX_mono a hM
  have hU1 := one_le_bigUX a M₂
  have hpow : bigUX a M₁ ^ (2 * bigJ M₁ + 2) ≤ bigUX a M₂ ^ (2 * bigJ M₂ + 2) :=
    le_trans (Nat.pow_le_pow_left hU _) (Nat.pow_le_pow_right hU1 (by omega))
  have h4 : 4 ^ (bigJ M₁ + 1) ≤ 4 ^ (bigJ M₂ + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  gcongr

lemma one_le_gammaHP (a d M : ℕ) : 1 ≤ gammaHP a d M := by
  unfold gammaHP
  have := one_le_bigUX a M
  have : 0 < 2 ^ 12 * (bigJ M + 2) ^ 4 * 4 ^ (bigJ M + 1) * (bigKB M + 1) ^ 4 *
      (1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2) := by positivity
  omega

/-- `max 2 d ≤ Γ`: the factor `2^12` is at least `2`, the factor `(1 + (2 + d)^4)^2` is at least
`d`, and every other factor is at least `1`. -/
lemma max_two_le_gammaHP (a d M : ℕ) : max 2 d ≤ gammaHP a d M := by
  have hd : d ≤ (1 + (2 + d) ^ 4) ^ 2 := by
    calc d ≤ 2 + d := by omega
      _ ≤ (2 + d) ^ 4 := Nat.le_self_pow (by decide) _
      _ ≤ 1 + (2 + d) ^ 4 := by omega
      _ ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.le_self_pow (by decide) _
  have hU := Nat.one_le_pow (2 * bigJ M + 2) _ (one_le_bigUX a M)
  have hA : 1 ≤ (bigJ M + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hB : 1 ≤ 4 ^ (bigJ M + 1) := Nat.one_le_pow _ _ (by omega)
  have hC : 1 ≤ (bigKB M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hD : 1 ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold gammaHP
  set A := (bigJ M + 2) ^ 4
  set B := 4 ^ (bigJ M + 1)
  set C := (bigKB M + 1) ^ 4
  set D := (1 + (2 + d) ^ 4) ^ 2
  set E := bigUX a M ^ (2 * bigJ M + 2)
  have hABCE : 1 ≤ A * B * C * E := by
    have : 0 < A * B * C * E := by positivity
    omega
  have heq : 2 ^ 12 * A * B * C * D * E = 2 ^ 12 * D * (A * B * C * E) := by ring
  rw [heq]
  refine max_le ?_ ?_
  · calc 2 ≤ 2 ^ 12 * 1 * 1 := by norm_num
      _ ≤ 2 ^ 12 * D * (A * B * C * E) := by gcongr
  · calc d ≤ 1 * D * 1 := by simpa using hd
      _ ≤ 2 ^ 12 * D * (A * B * C * E) := by gcongr; omega

/-! ## The four bounds by `Γ` -/

/-- Common form of the bounds: a product of six factors, each dominated by the matching factor
of `Γ`, is at most `Γ`. -/
private lemma le_gammaHP_of_factors {a d M c₀ c₁ c₂ c₃ c₄ c₅ : ℕ}
    (h₀ : c₀ ≤ 2 ^ 12) (h₁ : c₁ ≤ (bigJ M + 2) ^ 4) (h₂ : c₂ ≤ 4 ^ (bigJ M + 1))
    (h₃ : c₃ ≤ (bigKB M + 1) ^ 4) (h₄ : c₄ ≤ (1 + (2 + d) ^ 4) ^ 2)
    (h₅ : c₅ ≤ bigUX a M ^ (2 * bigJ M + 2)) :
    c₀ * c₁ * c₂ * c₃ * c₄ * c₅ ≤ gammaHP a d M := by
  unfold gammaHP
  gcongr

private lemma hOf_le (d : ℕ) : hOf d ≤ (1 + (2 + d) ^ 4) ^ 2 := by
  unfold hOf
  calc (2 + d) ^ 4 ≤ 1 + (2 + d) ^ 4 := by omega
    _ ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.le_self_pow (by decide) _

private lemma hOf_sq_le (d : ℕ) : hOf d ^ 2 ≤ (1 + (2 + d) ^ 4) ^ 2 := by
  unfold hOf
  exact Nat.pow_le_pow_left (by omega) 2

private lemma one_le_hOf (d : ℕ) : 1 ≤ hOf d := by unfold hOf; exact Nat.one_le_pow _ _ (by omega)

private lemma upow_le {a m M k : ℕ} (h : m ≤ M) (hk : k ≤ 2 * bigJ M + 2) :
    uOf a m ^ k ≤ bigUX a M ^ (2 * bigJ M + 2) :=
  le_trans (Nat.pow_le_pow_left (uOf_le_bigUX a h) k)
    (Nat.pow_le_pow_right (one_le_bigUX a M) hk)

private lemma four_pow_le {m M : ℕ} (h : m ≤ M) : 4 ^ depthOf m ≤ 4 ^ (bigJ M + 1) :=
  Nat.pow_le_pow_right (by decide) (by have := depthOf_le_bigJ h; omega)

private lemma branch_pow_le {m M k : ℕ} (h : m ≤ M) (hk : k ≤ 4) :
    branchOf m ^ k ≤ (bigKB M + 1) ^ 4 :=
  le_trans (Nat.pow_le_pow_left (by have := branchOf_le_bigKB h; omega) k)
    (Nat.pow_le_pow_right (by omega) hk)

private lemma depth_le_pow {m M : ℕ} (h : m ≤ M) : depthOf m ≤ (bigJ M + 2) ^ 4 :=
  le_trans (by have := depthOf_le_bigJ h; omega) (Nat.le_self_pow (by decide) _)

lemma one_le_xiOf (a d m : ℕ) : 1 ≤ xiOf a d m := by
  unfold xiOf lamOf vOf
  have := two_le_depthOf m
  have := one_le_branchOf m
  have := one_le_hOf d
  have := one_le_uOf a m
  have : 0 < depthOf m * branchOf m ^ 2 * (hOf d * uOf a m ^ depthOf m) := by positivity
  omega

lemma one_le_lamOf (a d m : ℕ) : 1 ≤ lamOf a d m := by
  unfold lamOf vOf
  have := one_le_hOf d
  have := one_le_uOf a m
  have : 0 < hOf d * uOf a m ^ depthOf m := by positivity
  omega

/-- `4^h ξ ≤ Γ`, used for the loss bounds. -/
theorem lossFactor_le_gamma (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    lossFactor a d m ≤ gammaHP a d M := by
  have heq : lossFactor a d m =
      1 * depthOf m * 4 ^ depthOf m * branchOf m ^ 2 * hOf d * uOf a m ^ depthOf m := by
    unfold lossFactor xiOf lamOf vOf; ring
  rw [heq]
  have := depthOf_le_bigJ h
  exact le_gammaHP_of_factors (by norm_num) (depth_le_pow h) (four_pow_le h)
    (branch_pow_le h (by norm_num)) (hOf_le d) (upow_le h (by omega))

/-- The stored reverse-list bound fits under the interface bound. -/
theorem xiOf_le_gamma (a d : ℕ) {m M : ℕ} (hm : m ≤ M) :
    xiOf a d m ≤ gammaHP a d M :=
  (Nat.le_mul_of_pos_left _ (by positivity : 0 < 4 ^ depthOf m)).trans
    (lossFactor_le_gamma a d hm)

/-- The walk-length bound is at most the reverse-list bound. -/
theorem lamOf_le_xiOf (a d m : ℕ) : lamOf a d m ≤ xiOf a d m := by
  unfold xiOf
  have hd : 0 < depthOf m := lt_of_lt_of_le (by decide : 0 < 2) (two_le_depthOf m)
  have hb : 0 < branchOf m := one_le_branchOf m
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hd (pow_pos hb _))

/-- `(2^h + 1) λ ≤ Γ`, used for the walk length bound. -/
theorem pathLen_le_gamma (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    pathLen a d m ≤ gammaHP a d M := by
  have heq : pathLen a d m =
      1 * 1 * (2 ^ depthOf m + 1) * 1 * hOf d * uOf a m ^ depthOf m := by
    unfold pathLen lamOf vOf; ring
  rw [heq]
  have := depthOf_le_bigJ h
  have h2 : 2 ^ depthOf m + 1 ≤ 4 ^ depthOf m := by
    have h4 : 4 ^ depthOf m = 2 ^ depthOf m * 2 ^ depthOf m := by
      rw [← mul_pow]; norm_num
    have : 2 ≤ 2 ^ depthOf m := by
      have := two_le_depthOf m
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ depthOf m := Nat.pow_le_pow_right (by decide) (by omega)
    rw [h4]; nlinarith
  exact le_gammaHP_of_factors (by norm_num) (Nat.one_le_pow _ _ (by omega))
    (le_trans h2 (four_pow_le h)) (Nat.one_le_pow _ _ (by omega)) (hOf_le d)
    (upow_le h (by omega))

/-- The coefficient `delCoeff` of `t` is at most `Γ`. With `1 ≤ ξ`, `1 ≤ h B` and `1 ≤ λ` the
coefficient is at most `8 · h²(h + 2) · 4^h · B³ · H² · U^{2h}`. -/
theorem delCoeff_le_gamma (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    delCoeff a d m ≤ gammaHP a d M := by
  have hxi := one_le_xiOf a d m
  have hlam := one_le_lamOf a d m
  have hB := one_le_branchOf m
  have hh := two_le_depthOf m
  have hhB : 1 ≤ depthOf m * branchOf m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hle : delCoeff a d m ≤
      (2 * xiOf a d m) * (depthOf m + 2) * 4 ^ depthOf m * (2 * (depthOf m * branchOf m)) *
        (2 * lamOf a d m) := by
    unfold delCoeff
    gcongr <;> omega
  refine le_trans hle ?_
  have heq : (2 * xiOf a d m) * (depthOf m + 2) * 4 ^ depthOf m *
      (2 * (depthOf m * branchOf m)) * (2 * lamOf a d m) =
      8 * (depthOf m * depthOf m * (depthOf m + 2)) * 4 ^ depthOf m * branchOf m ^ 3 *
        hOf d ^ 2 * uOf a m ^ (2 * depthOf m) := by
    unfold xiOf lamOf vOf; ring
  rw [heq]
  have hj := depthOf_le_bigJ h
  have hcub : depthOf m * depthOf m * (depthOf m + 2) ≤ (bigJ M + 2) ^ 4 := by
    calc depthOf m * depthOf m * (depthOf m + 2) ≤ (bigJ M + 2) * (bigJ M + 2) * (bigJ M + 2) :=
          by gcongr <;> omega
      _ = (bigJ M + 2) ^ 3 := by ring
      _ ≤ (bigJ M + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact le_gammaHP_of_factors (by norm_num) hcub (four_pow_le h) (branch_pow_le h (by norm_num))
    (hOf_sq_le d) (upow_le h (by omega))

/-- The factor `initFactor = (h + 1)(B + 1)^2 H U^{h+1}` is at most `Γ`. -/
theorem initFactor_le_gamma (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    initFactor a d m ≤ gammaHP a d M := by
  have heq : initFactor a d m =
      1 * (depthOf m + 1) * 1 * (branchOf m + 1) ^ 2 * hOf d * uOf a m ^ (depthOf m + 1) := by
    unfold initFactor; ring
  rw [heq]
  have hj := depthOf_le_bigJ h
  have hK := branchOf_le_bigKB h
  have hd1 : depthOf m + 1 ≤ (bigJ M + 2) ^ 4 :=
    le_trans (by omega) (Nat.le_self_pow (by decide) _)
  have hB2 : (branchOf m + 1) ^ 2 ≤ (bigKB M + 1) ^ 4 :=
    le_trans (Nat.pow_le_pow_left (by omega) 2) (Nat.pow_le_pow_right (by omega) (by norm_num))
  exact le_gammaHP_of_factors (by norm_num) hd1 (Nat.one_le_pow _ _ (by omega)) hB2 (hOf_le d)
    (upow_le h (by omega))

/-- The query factor `2^h (1 + λ)` is at most `Γ`. -/
theorem queryFactor_le_gamma (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    queryFactor a d m ≤ gammaHP a d M := by
  have hlam := one_le_lamOf a d m
  have hle : queryFactor a d m ≤ 2 ^ depthOf m * (2 * lamOf a d m) := by
    unfold queryFactor; gcongr; omega
  refine le_trans hle ?_
  have heq : 2 ^ depthOf m * (2 * lamOf a d m) =
      2 * 1 * 2 ^ depthOf m * 1 * hOf d * uOf a m ^ depthOf m := by
    unfold lamOf vOf; ring
  rw [heq]
  have hj := depthOf_le_bigJ h
  have h2 : 2 ^ depthOf m ≤ 4 ^ (bigJ M + 1) :=
    le_trans (Nat.pow_le_pow_left (by norm_num) _) (four_pow_le h)
  exact le_gammaHP_of_factors (by norm_num) (Nat.one_le_pow _ _ (by omega)) h2
    (Nat.one_le_pow _ _ (by omega)) (hOf_le d) (upow_le h (by omega))

end MinCostFlow.HierPaths
