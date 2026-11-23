module

public import MinCostFlow.Expander.PruningProg

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Time Bound of the Fallback of `PathDS`

On a cluster below the conductance of [CS21], the data structure of Theorem 8.6 prunes and
searches the cluster itself. This file defines the bound `fbCostBound d` on the time of one such
operation, where `d = ⌈1 / φ_in⌉`. It depends only on `d`: the fallback runs only on clusters
with fewer than `zStarImpl d` edges (`three_m_lt_zStar` in `Params.lean`). The bound
`fbCostCap d M` caps the cluster size by `M` as well, and covers pruning and search on any
such cluster (`fbCostCap_covers_fallback` in `Params.lean`).

`zStarImpl d = 2 ^ zStarExp d` with `zStarExp d = ⌊((log₂(10 d) + 1)^4)^{1/3}⌋`, computed by an
integer cube root (`natCbrtFloor`).

The cluster also has at most `M` edges. So the program uses the capped bound `fbCostCap d M`, in
which `zStarImpl d` is replaced by `zCap d M = 2 ^ min (zStarExp d) (log₂(3M + 1) + 1)`. The cap
keeps `fbCostCap d M` polynomial in `d + M` (`fbCostCap_le_poly`), and below `fbCostBound d`
(`fbCostCap_le`).
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open MinCostFlow.Expander

/-- Integer binary-search floor of `y^{1/3}` on `[lo, hi)` (returning `r` with `r^3 ≤ y < (r+1)^3`). -/
def natCbrtSearch (y lo hi : ℕ) : ℕ :=
  if h : lo + 1 < hi then
    let mid := (lo + hi) / 2
    if mid ^ 3 ≤ y then natCbrtSearch y mid hi
    else natCbrtSearch y lo mid
  else lo
termination_by hi - lo

lemma natCbrtSearch_spec (y : ℕ) :
    ∀ lo hi : ℕ, lo < hi → lo ^ 3 ≤ y → y < hi ^ 3 →
      let r := natCbrtSearch y lo hi
      r ^ 3 ≤ y ∧ y < (r + 1) ^ 3 := by
  intro lo hi hlt hlo hhi
  induction hdiff : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | _ d ih =>
    rw [natCbrtSearch]
    split_ifs with hstep
    · set mid := (lo + hi) / 2
      have hlo_mid : lo < mid := by omega
      have hmid_hi : mid < hi := by omega
      dsimp only
      split_ifs with hle
      · exact ih (hi - mid) (by omega) mid hi hmid_hi hle hhi rfl
      · exact ih (mid - lo) (by omega) lo mid hlo_mid hlo (by omega) rfl
    · have hhi_eq : hi = lo + 1 := by omega
      subst hhi_eq
      exact ⟨hlo, hhi⟩

/-- Floor cube root `⌊y^{1/3}⌋` computed via `natCbrtSearch y 0 (y + 1)`. -/
def natCbrtFloor (y : ℕ) : ℕ :=
  natCbrtSearch y 0 (y + 1)

lemma natCbrtFloor_spec (y : ℕ) :
    (natCbrtFloor y) ^ 3 ≤ y ∧ y < (natCbrtFloor y + 1) ^ 3 := by
  apply natCbrtSearch_spec y 0 (y + 1) (by omega) (by norm_num)
  have h1 : y < (y + 1) * (y + 1) * (y + 1) := by nlinarith
  simpa [pow_succ] using h1

lemma natCbrtSearch_eq_natCbrtFloor {y hi : ℕ} (hy : y < hi ^ 3) (hpos : 0 < hi) :
    natCbrtSearch y 0 hi = natCbrtFloor y := by
  have h1 := natCbrtSearch_spec y 0 hi hpos (by norm_num) hy
  have h2 := natCbrtFloor_spec y
  set r1 := natCbrtSearch y 0 hi
  set r2 := natCbrtFloor y
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hlt1 : r1 + 1 ≤ r2 := hlt
    have : (r1 + 1) ^ 3 ≤ r2 ^ 3 := Nat.pow_le_pow_left hlt1 3
    omega
  · have hlt1 : r2 + 1 ≤ r1 := hlt
    have : (r2 + 1) ^ 3 ≤ r1 ^ 3 := Nat.pow_le_pow_left hlt1 3
    omega

lemma natCbrtFloor_mono {y₁ y₂ : ℕ} (h : y₁ ≤ y₂) : natCbrtFloor y₁ ≤ natCbrtFloor y₂ := by
  have h1 := natCbrtFloor_spec y₁
  have h2 := natCbrtFloor_spec y₂
  have hpow : (natCbrtFloor y₁) ^ 3 < (natCbrtFloor y₂ + 1) ^ 3 := by omega
  by_contra hgt
  have hge : natCbrtFloor y₂ + 1 ≤ natCbrtFloor y₁ := by omega
  have := Nat.pow_le_pow_left hge 3
  omega

/-- Exponent `⌊((log₂(10 * d) + 1) ^ 4)^{1/3}⌋` for the fallback size cap `Z_*(d)`. -/
def zStarExp (d : ℕ) : ℕ :=
  natCbrtFloor ((Nat.log 2 (10 * d) + 1) ^ 4)

/-- Fallback edge threshold `Z_*(d) = 2 ^ zStarExp d`. -/
def zStarImpl (d : ℕ) : ℕ :=
  2 ^ zStarExp d

lemma zStarExp_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : zStarExp d₁ ≤ zStarExp d₂ := by
  unfold zStarExp
  exact natCbrtFloor_mono (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) 4)

lemma zStarImpl_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : zStarImpl d₁ ≤ zStarImpl d₂ :=
  Nat.pow_le_pow_right (by decide) (zStarExp_mono h)

lemma six_le_zStarExp {d : ℕ} (hd : 1 ≤ d) : 6 ≤ zStarExp d := by
  have hlog : 3 ≤ Nat.log 2 (10 * d) := by
    have h23 : 2 ^ 3 ≤ 10 * d := by omega
    exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr h23
  have hge : 256 ≤ (Nat.log 2 (10 * d) + 1) ^ 4 := by
    calc 256 = 4 ^ 4 := by decide
      _ ≤ (Nat.log 2 (10 * d) + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h6 : natCbrtFloor 256 ≤ zStarExp d := natCbrtFloor_mono hge
  have hfloor256 : 6 ≤ natCbrtFloor 256 := by
    have hs := natCbrtFloor_spec 256
    by_contra hlt
    have : natCbrtFloor 256 + 1 ≤ 6 := by omega
    have : (natCbrtFloor 256 + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left this 3
    omega
  exact le_trans hfloor256 h6

lemma sixty_four_le_zStarImpl {d : ℕ} (hd : 1 ≤ d) : 64 ≤ zStarImpl d := by
  calc 64 = 2 ^ 6 := by decide
    _ ≤ 2 ^ zStarExp d := Nat.pow_le_pow_right (by decide) (six_le_zStarExp hd)


/-- Time bound of one fallback `Delete` or `GetPath`, depending only on `d = ⌈1 / φ_in⌉`. -/
def fbCostBound (d : ℕ) : ℕ :=
  let z := zStarImpl d
  let b := zStarExp d
  let Hfb := 4 * (40 * d + 1) * (b + 2) + 2
  pruneTimeBound (2 * z) z Hfb + 2000 * z + 10 * d + 1000

lemma fbCostBound_mono {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) : fbCostBound d₁ ≤ fbCostBound d₂ := by
  unfold fbCostBound pruneTimeBound
  dsimp only
  have hz : zStarImpl d₁ ≤ zStarImpl d₂ := zStarImpl_mono hd
  have hb : zStarExp d₁ ≤ zStarExp d₂ := zStarExp_mono hd
  have hH : 4 * (40 * d₁ + 1) * (zStarExp d₁ + 2) + 2 ≤
      4 * (40 * d₂ + 1) * (zStarExp d₂ + 2) + 2 := by
    have hmul : (40 * d₁ + 1) * (zStarExp d₁ + 2) ≤ (40 * d₂ + 1) * (zStarExp d₂ + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hmul4 : 4 * ((40 * d₁ + 1) * (zStarExp d₁ + 2)) ≤
        4 * ((40 * d₂ + 1) * (zStarExp d₂ + 2)) := Nat.mul_le_mul_left 4 hmul
    nlinarith
  have hp1 : 4 * (4 * (40 * d₁ + 1) * (zStarExp d₁ + 2) + 2) + 14 ≤
      4 * (4 * (40 * d₂ + 1) * (zStarExp d₂ + 2) + 2) + 14 := by omega
  have hp2 : 4 * (4 * (40 * d₁ + 1) * (zStarExp d₁ + 2) + 2) + 4 ≤
      4 * (4 * (40 * d₂ + 1) * (zStarExp d₂ + 2) + 2) + 4 := by omega
  have hp3 : 2 * zStarImpl d₁ + 1 ≤ 2 * zStarImpl d₂ + 1 := by omega
  have hp : (4 * (4 * (40 * d₁ + 1) * (zStarExp d₁ + 2) + 2) + 14) *
        (4 * (4 * (40 * d₁ + 1) * (zStarExp d₁ + 2) + 2) + 4) * (2 * zStarImpl d₁ + 1) ≤
      (4 * (4 * (40 * d₂ + 1) * (zStarExp d₂ + 2) + 2) + 14) *
        (4 * (4 * (40 * d₂ + 1) * (zStarExp d₂ + 2) + 2) + 4) * (2 * zStarImpl d₂ + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hp1 hp2) hp3
  have hp360 := Nat.mul_le_mul_left 360 hp
  omega

lemma fbCostBound_ge_linear {d : ℕ} : 10 * d + 1000 ≤ fbCostBound d := by
  unfold fbCostBound
  dsimp only
  omega

/-- Capped fallback size `zCap d M = 2 ^ min (zStarExp d) (log₂(3M + 1) + 1)`. It is at most
`zStarImpl d` and at most `2 (3M + 1)`, and it exceeds `3m` for every cluster of the fallback with
`m ≤ M` edges (`three_m_lt_zCap`). -/
def zCap (d M : ℕ) : ℕ :=
  2 ^ min (zStarExp d) (Nat.log 2 (3 * M + 1) + 1)

lemma zCap_le_zStarImpl (d M : ℕ) : zCap d M ≤ zStarImpl d :=
  Nat.pow_le_pow_right (by decide) (min_le_left _ _)

lemma zCap_le_M (d M : ℕ) : zCap d M ≤ 6 * M + 2 := by
  have h1 : zCap d M ≤ 2 ^ (Nat.log 2 (3 * M + 1) + 1) :=
    Nat.pow_le_pow_right (by decide) (min_le_right _ _)
  have h2 : 2 ^ Nat.log 2 (3 * M + 1) ≤ 3 * M + 1 := Nat.pow_log_le_self 2 (by omega)
  rw [pow_succ] at h1
  omega

lemma zCap_mono {d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) : zCap d₁ M₁ ≤ zCap d₂ M₂ := by
  unfold zCap
  apply Nat.pow_le_pow_right (by decide)
  have h1 := zStarExp_mono hd
  have h2 : Nat.log 2 (3 * M₁ + 1) ≤ Nat.log 2 (3 * M₂ + 1) := Nat.log_mono_right (by omega)
  omega

lemma one_le_zCap (d M : ℕ) : 1 ≤ zCap d M := Nat.one_le_two_pow

/-- A fallback cluster with `m ≤ M` edges and `3m < zStarImpl d` has `3m < zCap d M`. -/
lemma three_m_lt_zCap {d M m : ℕ} (hmM : m ≤ M) (hz : 3 * m < zStarImpl d) :
    3 * m < zCap d M := by
  unfold zCap
  rcases le_total (zStarExp d) (Nat.log 2 (3 * M + 1) + 1) with h | h
  · rw [min_eq_left h]; exact hz
  · rw [min_eq_right h]
    have : 3 * M + 1 < 2 ^ (Nat.log 2 (3 * M + 1) + 1) := Nat.lt_pow_succ_log_self (by decide) _
    omega

/-- Capped time bound of one fallback operation: `fbCostBound d` with `zStarImpl d` replaced by
`zCap d M`. -/
def fbCostCap (d M : ℕ) : ℕ :=
  let z := zCap d M
  let b := zStarExp d
  let Hfb := 4 * (40 * d + 1) * (b + 2) + 2
  pruneTimeBound (2 * z) z Hfb + 2000 * z + 10 * d + 1000

private lemma fbCost_formula_mono {d₁ d₂ z₁ z₂ b₁ b₂ : ℕ} (hd : d₁ ≤ d₂) (hz : z₁ ≤ z₂)
    (hb : b₁ ≤ b₂) :
    pruneTimeBound (2 * z₁) z₁ (4 * (40 * d₁ + 1) * (b₁ + 2) + 2) + 2000 * z₁ + 10 * d₁ + 1000 ≤
      pruneTimeBound (2 * z₂) z₂ (4 * (40 * d₂ + 1) * (b₂ + 2) + 2) + 2000 * z₂ + 10 * d₂ +
        1000 := by
  unfold pruneTimeBound
  have hH : 4 * (40 * d₁ + 1) * (b₁ + 2) + 2 ≤ 4 * (40 * d₂ + 1) * (b₂ + 2) + 2 := by
    have hmul : (40 * d₁ + 1) * (b₁ + 2) ≤ (40 * d₂ + 1) * (b₂ + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hp : (4 * (4 * (40 * d₁ + 1) * (b₁ + 2) + 2) + 14) *
        (4 * (4 * (40 * d₁ + 1) * (b₁ + 2) + 2) + 4) * (2 * z₁ + 1) ≤
      (4 * (4 * (40 * d₂ + 1) * (b₂ + 2) + 2) + 14) *
        (4 * (4 * (40 * d₂ + 1) * (b₂ + 2) + 2) + 4) * (2 * z₂ + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  have hp360 := Nat.mul_le_mul_left 360 hp
  omega

lemma fbCostCap_le (d M : ℕ) : fbCostCap d M ≤ fbCostBound d :=
  fbCost_formula_mono le_rfl (zCap_le_zStarImpl d M) le_rfl

lemma fbCostCap_mono {d₁ d₂ M₁ M₂ : ℕ} (hd : d₁ ≤ d₂) (hM : M₁ ≤ M₂) :
    fbCostCap d₁ M₁ ≤ fbCostCap d₂ M₂ :=
  fbCost_formula_mono hd (zCap_mono hd hM) (zStarExp_mono hd)

lemma fbCostCap_ge_linear {d M : ℕ} : 10 * d + 1000 ≤ fbCostCap d M := by
  unfold fbCostCap
  dsimp only
  omega

lemma zCap_le_fbCostCap (d M : ℕ) : 2000 * zCap d M ≤ fbCostCap d M := by
  unfold fbCostCap
  dsimp only
  omega

lemma zStarExp_le_poly (d : ℕ) : zStarExp d ≤ (10 * d + 1) ^ 4 := by
  have hs := (natCbrtFloor_spec ((Nat.log 2 (10 * d) + 1) ^ 4)).1
  have hb : zStarExp d ≤ zStarExp d ^ 3 := Nat.le_self_pow (by norm_num) _
  have hl : Nat.log 2 (10 * d) + 1 ≤ 10 * d + 1 := by
    have := Nat.log_le_self 2 (10 * d)
    omega
  have hl4 := Nat.pow_le_pow_left hl 4
  unfold zStarExp at hb ⊢
  omega

/-- `fbCostCap d M` is polynomial in `d + M`. -/
lemma fbCostCap_le_poly (d M : ℕ) : fbCostCap d M ≤ 10 ^ 20 * (d + M + 2) ^ 11 := by
  set X := d + M + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hz : zCap d M ≤ 6 * X := by have := zCap_le_M d M; omega
  have hb : zStarExp d + 2 ≤ 2 * 10 ^ 4 * X ^ 4 := by
    have h1 := zStarExp_le_poly d
    have h2 : (10 * d + 1) ^ 4 ≤ (10 * X) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h3 : (10 * X) ^ 4 = 10 ^ 4 * X ^ 4 := by ring
    have h4 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hH : 4 * (40 * d + 1) * (zStarExp d + 2) + 2 ≤ 4 * 10 ^ 6 * X ^ 5 := by
    have h1 : 4 * (40 * d + 1) ≤ 164 * X := by omega
    have h2 := Nat.mul_le_mul h1 hb
    have h3 : 164 * X * (2 * 10 ^ 4 * X ^ 4) = 3280000 * X ^ 5 := by ring
    have h4 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  set H := 4 * (40 * d + 1) * (zStarExp d + 2) + 2
  set z := zCap d M
  have hp1 : 4 * H + 14 ≤ 2 * 10 ^ 7 * X ^ 5 := by
    have h4 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  have hp2 : 4 * H + 4 ≤ 2 * 10 ^ 7 * X ^ 5 := by omega
  have hp3 : 2 * z + 1 ≤ 13 * X := by omega
  have hprod : (4 * H + 14) * (4 * H + 4) * (2 * z + 1) ≤
      (2 * 10 ^ 7 * X ^ 5) * (2 * 10 ^ 7 * X ^ 5) * (13 * X) :=
    Nat.mul_le_mul (Nat.mul_le_mul hp1 hp2) hp3
  have hprod' : (2 * 10 ^ 7 * X ^ 5) * (2 * 10 ^ 7 * X ^ 5) * (13 * X) =
      52 * 10 ^ 14 * X ^ 11 := by ring
  have hX5 : X ^ 5 ≤ X ^ 11 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hX1 : X ≤ X ^ 11 := Nat.le_self_pow (by norm_num) _
  have hlin : 170 * (2 * z) + 140 * z + 30 * (H + 1) + 221 + 2000 * z + 10 * d + 1000 ≤
      10 ^ 9 * X ^ 11 := by
    have : 30 * (H + 1) ≤ 2 * 10 ^ 8 * X ^ 5 := by omega
    omega
  have hdef : fbCostCap d M = pruneTimeBound (2 * z) z H + 2000 * z + 10 * d + 1000 := rfl
  rw [hdef]
  unfold pruneTimeBound
  omega

end MinCostFlow.Expander.PathDSProg
