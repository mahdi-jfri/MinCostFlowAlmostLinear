module

public import MinCostFlow.LowStretch.Stretch1
public import MinCostFlow.LowStretch.Entropy

/-!
# Region growing pays for the cut pairs

The cost of a petal is the weight `cw/ω` of the active pairs that leave it. Region growing chose
the radius of the petal so that `cost · s_q ≤ 8 · vol`, where `s_q ≈ Δ / (8 L (λ_(q-1) + 3))`.
So `Δ · cost ≤ 128 L (λ_(q-1) + 3) vol` (`dcost_le`). The test `vol ≤ T_q` makes the level small
when the petal is large: `λ_(q-1) + 3 ≤ 9 + 2 log₂(V / vol)`, unless `vol < 2κ` (`lam_vol_le`).
Summed over the petals with the entropy inequality, this gives `Δ · ∑ cost ≤ 128 L (…)` with a
term `2 (F(S) - ∑ F(part))` for the sum `S = V + s κ` (`dcost_sum_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Real

/-- The level bound, in numbers. When `κ ≤ v ≤ S`, `κ ≤ V ≤ S`, `v ≤ 4V/2^λ + κ` and
`λ' = 2λ ≤ λ0`, then `(λ' + 3) v ≤ 2κ(λ0 + 3) + 9 v + 2 v log₂(S / v)`. -/
theorem lam_vol_le {κ v V S : ℝ} {lam lam0 : ℕ} (hκ : 0 < κ) (hv : κ ≤ v) (hvS : v ≤ S)
    (hV : κ ≤ V) (hVS : V ≤ S) (hT : v ≤ 4 * V / 2 ^ lam + κ) (hl : 2 * lam ≤ lam0) :
    ((2 * lam : ℕ) + 3 : ℝ) * v ≤ 2 * κ * (lam0 + 3) + 9 * v + 2 * v * logb 2 (S / v) := by
  have hvpos : 0 < v := by linarith
  have hlog : 0 ≤ logb 2 (S / v) := logb_nonneg_of_le hvpos hvS
  have hl' : ((2 * lam : ℕ) : ℝ) ≤ lam0 := by exact_mod_cast hl
  have h1 : 0 ≤ v * logb 2 (S / v) := mul_nonneg hvpos.le hlog
  by_cases hsmall : v < 2 * κ
  · have : ((2 * lam : ℕ) + 3 : ℝ) * v ≤ (lam0 + 3) * (2 * κ) := by
      exact mul_le_mul (by linarith) hsmall.le hvpos.le (by positivity)
    nlinarith
  · push Not at hsmall
    have h2 : (2 : ℝ) ^ lam * v ≤ 8 * S := by
      have hp : (0 : ℝ) < 2 ^ lam := by positivity
      have : v - κ ≤ 4 * V / 2 ^ lam := by linarith
      have : 2 ^ lam * (v - κ) ≤ 4 * V := by
        rw [le_div_iff₀ hp] at this; linarith
      nlinarith
    have h3 : (lam : ℝ) ≤ 3 + logb 2 (S / v) := by
      have e1 : logb 2 ((2 : ℝ) ^ lam) = lam := by
        rw [logb_pow, logb_self_eq_one (by norm_num), mul_one]
      have e2 : logb 2 (8 * (S / v)) = 3 + logb 2 (S / v) := by
        rw [logb_mul (by norm_num) (div_pos (by linarith) hvpos).ne']
        congr 1
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, logb_pow, logb_self_eq_one (by norm_num)]
        norm_num
      rw [← e1, ← e2]
      apply logb_le_logb_of_le (by norm_num) (by positivity)
      rw [mul_div_assoc', le_div_iff₀ hvpos]
      exact h2
    have e : ((2 * lam : ℕ) : ℝ) = 2 * lam := by push_cast; ring
    rw [e]
    nlinarith

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

theorem cost_nonneg (Y : Finset ℕ) (pd : PD) : 0 ≤ c.cost G P Y pd := by
  unfold cost
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem vol_ge (Y : Finset ℕ) (pd : PD) : (P.κ : ℝ) ≤ c.vol G P Y pd := by
  rw [vol_eq]
  have := Finset.sum_nonneg fun p (_ : p ∈ c.act G P) => contrib_nonneg (c := c) (G := G) (P := P) Y pd p
  linarith

theorem vstem_ge : (P.κ : ℝ) ≤ c.vstem G P D := by
  classical
  unfold vstem
  have : 0 ≤ ∑ p ∈ c.act G P, if Inside G (c.stem G D) p then (P.cw p : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  linarith

theorem V_ge : (P.κ : ℝ) ≤ c.V G P := by
  unfold V
  have : 0 ≤ ∑ p ∈ c.act G P, (P.cw p : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem part_ge (k : ℕ) : (P.κ : ℝ) ≤ c.part G P D k := by
  cases k with
  | zero => exact vstem_ge
  | succ k => exact vol_ge _ _

theorem lam_succ {q : ℕ} (h1 : 1 ≤ q) (h2 : q ≤ P.L) : lam P (q - 1) = 2 * lam P q := by
  unfold lam
  rw [show P.L - (q - 1) = (P.L - q) + 1 by omega, pow_succ]
  ring

theorem lam_le (q : ℕ) : lam P q ≤ lam P 0 :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Region growing: `Δ · cost ≤ 128 L (λ_(q-1) + 3) vol` for the bucket `q` of the petal. -/
theorem dcost_le (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length)
    (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G) :
    ∃ q, 1 ≤ q ∧ q ≤ P.L ∧
      (c.Δ G : ℝ) * c.cost G P (c.Z G D k) (D.pd k) ≤
        128 * P.L * ((lam P (q - 1) : ℕ) + 3 : ℝ) * c.vol G P (c.Z G D k) (D.pd k) ∧
      c.vol G P (c.Z G D k) (D.pd k) ≤ c.T G P q := by
  obtain ⟨-, -, -, -, -, q, hq1, hqL, -, -, hc, hv⟩ := petalOk hD hk
  refine ⟨q, hq1, hqL, ?_, hv⟩
  set M := 8 * P.L * (lam P (q - 1) + 3) with hM
  have hMΔ : M ≤ c.Δ G := by
    have := lam_le (P := P) (q - 1)
    have : M ≤ 8 * P.L * (lam P 0 + 3) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hMpos : 0 < M := by
    have : 0 < P.L := by omega
    positivity
  have hsq : c.sq G P q = c.Δ G / M := by
    unfold sq bw
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hM, ← Nat.mul_assoc]
  have h1 : c.Δ G ≤ 2 * (M * c.sq G P q) := by
    rw [hsq]
    have := Nat.lt_mul_div_succ (c.Δ G) hMpos
    have hs : 1 ≤ c.Δ G / M := (Nat.one_le_div_iff hMpos).mpr hMΔ
    have : M ≤ M * (c.Δ G / M) := Nat.le_mul_of_pos_right _ hs
    rw [Nat.mul_add, Nat.mul_one] at *
    omega
  have h1' : (c.Δ G : ℝ) ≤ 2 * M * c.sq G P q := by
    have : ((c.Δ G : ℕ) : ℝ) ≤ ((2 * (M * c.sq G P q) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hcost := cost_nonneg (c := c) (G := G) (P := P) (c.Z G D k) (D.pd k)
  have hMr : (M : ℝ) = 8 * P.L * ((lam P (q - 1) : ℕ) + 3 : ℝ) := by rw [hM]; push_cast; ring
  calc (c.Δ G : ℝ) * c.cost G P (c.Z G D k) (D.pd k)
      ≤ 2 * M * c.sq G P q * c.cost G P (c.Z G D k) (D.pd k) :=
        mul_le_mul_of_nonneg_right h1' hcost
    _ = 2 * M * (c.cost G P (c.Z G D k) (D.pd k) * c.sq G P q) := by ring
    _ ≤ 2 * M * (8 * c.vol G P (c.Z G D k) (D.pd k)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [hMr]; ring

/-- The parts of a step, summed: at most `S = V + s κ`. -/
theorem sum_part_le (hGo : G.Ok) (hc : c.Conn G) :
    ∑ k ∈ Finset.range D.nch, c.part G P D k ≤ c.V G P + D.ps.length * P.κ := by
  unfold Dec.nch
  rw [Finset.sum_range_succ']
  have := parts_sum (P := P) (D := D) hGo hc
  have e : ∑ k ∈ Finset.range D.ps.length, c.part G P D (k + 1) =
      ∑ k ∈ Finset.range D.ps.length, c.vol G P (c.Z G D k) (D.pd k) := rfl
  rw [e]
  show _ + c.vstem G P D ≤ _
  linarith

/-- Region growing over all petals: `Δ · ∑ cost ≤ 128 L (2 s κ (λ0 + 3) + 9 S + 2 (F S - ∑ F))`,
for `S = V + s κ` and `s` petals. -/
theorem dcost_sum_le (hGo : G.Ok) (hc : c.Conn G) (hD : c.DecOk G P D) (hκ : 1 ≤ P.κ)
    (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G) :
    (c.Δ G : ℝ) * ∑ k ∈ Finset.range D.ps.length, c.cost G P (c.Z G D k) (D.pd k) ≤
      128 * P.L * (2 * D.ps.length * P.κ * ((lam P 0 : ℕ) + 3) +
        9 * (c.V G P + D.ps.length * P.κ) +
        2 * (Fe P.κ (c.V G P + D.ps.length * P.κ) -
          ∑ k ∈ Finset.range D.nch, Fe P.κ (c.part G P D k))) := by
  set S := c.V G P + D.ps.length * P.κ with hS
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have hsum := sum_part_le (P := P) (D := D) hGo hc
  rw [← hS] at hsum
  have hpart : ∀ k, (P.κ : ℝ) ≤ c.part G P D k := fun k => part_ge k
  have hpS : ∀ k < D.nch, c.part G P D k ≤ S := by
    intro k hk
    have := Finset.single_le_sum (f := c.part G P D) (fun j _ => by linarith [hpart j])
      (Finset.mem_range.mpr hk)
    linarith
  have hVS : c.V G P ≤ S := by
    have : (0 : ℝ) ≤ D.ps.length * P.κ := by positivity
    linarith
  have hVκ : (P.κ : ℝ) ≤ c.V G P := V_ge
  -- each petal
  have hk : ∀ k ∈ Finset.range D.ps.length,
      (c.Δ G : ℝ) * c.cost G P (c.Z G D k) (D.pd k) ≤ 128 * P.L * (2 * P.κ * ((lam P 0 : ℕ) + 3) +
        9 * c.part G P D (k + 1) +
        2 * c.part G P D (k + 1) * logb 2 (S / c.part G P D (k + 1))) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨q, hq1, hqL, h1, h2⟩ := dcost_le hD hk' hΔ
    have hl := lam_succ (P := P) hq1 hqL
    have hl0 := lam_le (P := P) (q - 1)
    have h3 := lam_vol_le (lam := lam P q) (lam0 := lam P 0) hκr (part_ge (k + 1))
      (hpS (k + 1) (by unfold Dec.nch; omega)) hVκ hVS h2 (by omega)
    rw [← hl] at h3
    have hL : (0 : ℝ) ≤ 128 * P.L := by positivity
    calc (c.Δ G : ℝ) * c.cost G P (c.Z G D k) (D.pd k)
        ≤ 128 * P.L * ((lam P (q - 1) : ℕ) + 3 : ℝ) * c.vol G P (c.Z G D k) (D.pd k) := h1
      _ = 128 * P.L * (((lam P (q - 1) : ℕ) + 3 : ℝ) * c.part G P D (k + 1)) := by
          rw [mul_assoc]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hL
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum]
  -- the entropy sum over all parts
  have hent := entropy_le (Finset.range D.nch) (c.part G P D) hκr (fun k _ => hpart k)
    hsum (by linarith)
  have hst : ∑ k ∈ Finset.range D.ps.length,
      c.part G P D (k + 1) * logb 2 (S / c.part G P D (k + 1)) ≤
      ∑ k ∈ Finset.range D.nch, c.part G P D k * logb 2 (S / c.part G P D k) := by
    unfold Dec.nch
    rw [Finset.sum_range_succ' (fun k => c.part G P D k * logb 2 (S / c.part G P D k))]
    have := mul_nonneg (show 0 ≤ c.part G P D 0 by linarith [hpart 0])
      (logb_nonneg_of_le (show 0 < c.part G P D 0 by linarith [hpart 0])
        (hpS 0 (by unfold Dec.nch; omega)))
    linarith
  have hvs : ∑ k ∈ Finset.range D.ps.length, c.part G P D (k + 1) ≤ S := by
    have : ∑ k ∈ Finset.range D.nch, c.part G P D k =
        ∑ k ∈ Finset.range D.ps.length, c.part G P D (k + 1) + c.part G P D 0 := by
      unfold Dec.nch; rw [Finset.sum_range_succ']
    linarith [hpart 0]
  have e2 : ∑ k ∈ Finset.range D.ps.length,
      2 * c.part G P D (k + 1) * logb 2 (S / c.part G P D (k + 1)) =
      2 * ∑ k ∈ Finset.range D.ps.length,
        c.part G P D (k + 1) * logb 2 (S / c.part G P D (k + 1)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  rw [e2]
  nlinarith

end Cl

end MinCostFlow.LowStretch
