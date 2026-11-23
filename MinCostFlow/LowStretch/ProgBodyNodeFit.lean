module

public import MinCostFlow.LowStretch.ProgClusterSetupSpec
import MinCostFlow.LowStretch.ProgPSearchA

/-!
# The cost of the node part fits the share of the body

The node part pays the setup (`setupCostOf`), the petals (`Kφ J'` per unit of the potential at the
start of the loop, `CJ J' L` per petal, `500` per node), a few hundred steps of its own and the
child step (`childCost`). `node_fit` turns this into the bound of `BodyPost` and the bound of the
heap, through `body_fit` and `childCost_fit`.

The petals use `J' ≤ J + 5` classes (`SetupOutJ`), where `J = rootJ n`, and
`log J' ≤ log J + 3`.

The units: `U = unitCost n = 10⁶ (log J + 2 + L)`. The setup pays `U / 10` per stored pair (twice)
and per node; the potential is at most `2 |S| + 2 s` and `Kφ J' ≤ U / 400`; a petal pays at most
`U` and `150 J + 5000`; the child step pays `U` per active pair, per node, per split and once,
and `10⁴ (J + 1) + 50 (log w + 2)` per child. The nodes beyond the first `U` per node are paid by
the stored pairs, since `s ≤ |S| + 1`. Child `0` takes the `400 J + 10⁴` of the setup, child
`k + 1` the `150 J + 5000` of petal `k`; both fit `kidCost`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- `log (J + 5) ≤ log J + 3`, since `J + 5 ≤ 8 J` for `J ≥ 1`. -/
private theorem log_add_five {J : ℕ} (hJ : 1 ≤ J) : Nat.log 2 (J + 5) ≤ Nat.log 2 J + 3 := by
  have h1 : Nat.log 2 (J + 5) ≤ Nat.log 2 (J * 2 * 2 * 2) := Nat.log_mono_right (by omega)
  rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega),
    Nat.log_mul_base (by norm_num) (by omega)] at h1
  omega

private theorem rootJ_pos (n : ℕ) : 1 ≤ rootJ n := by unfold rootJ; omega

private theorem Kφ_le (n : ℕ) :
    400 * PW.Kφ (rootJ n + 5) ≤ 1000000 * (Nat.log 2 (rootJ n) + 3) := by
  have := log_add_five (rootJ_pos n)
  unfold PW.Kφ; omega

private theorem CJ_le (n : ℕ) :
    PW.CJ (rootJ n + 5) (pL n) ≤ unitCost n + 150 * rootJ n + 5000 := by
  have := log_add_five (rootJ_pos n)
  unfold PW.CJ psPreCost unitCost; omega

/-- **The cost of the node part fits.** `K` is the cost before the child step, `Φ0` the
potential at the start of the loop, `hS` the end of the heap of the setup and `cost` the cost of
the child step. -/
theorem node_fit {w : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl} {K cost h hS Φ0 : ℕ} (hL : P.L = pL G.n)
    (hs : R.nodes.length ≤ R.S.length + 1)
    (hΦ : Φ0 ≤ 2 * R.S.length + 2 * R.nodes.length)
    (hK : K ≤ setupCostOf ⟨T, G, P, c, R⟩ + PW.Kφ (rootJ G.n + 5) * Φ0 +
      PW.CJ (rootJ G.n + 5) (pL G.n) * D.ps.length + 500 * R.nodes.length + 3000)
    (hcost : cost ≤ childCost T G P c R D cs (rootJ G.n))
    (hreset : ∀ k < D.nch,
      Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card) < 2 ^ w)
    (hhS : hS ≤ h + 1000 * (rootJ G.n + 1) * (R.S.length + R.nodes.length + P.L + 10)) :
    K + cost + 500 ≤ bodyShare bodyA T G P c R D cs + D.nch * kidCost w G.n ∧
      hS + 16 + (rootJ G.n + 1) * childCost T G P c R D cs (rootJ G.n) ≤
        h + 4 + (rootJ G.n + 1) * (bodyShare bodyA T G P c R D cs + D.nch * kidCost w G.n) := by
  have hcc := childCost_fit (w := w) (cs := cs) (R := R) hreset
  set J := rootJ G.n with hJ
  set U := unitCost G.n with hU
  set S := R.S.length with hSd
  set s := R.nodes.length with hsd
  set V := ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ with hV
  set a := (c.act G P).card with ha
  set np := D.ps.length with hnp
  set KC := 10000 * (J + 1) + 50 * (Nat.log 2 w + 2) with hKC
  set cc := childCost T G P c R D cs J with hccd
  have hnch : D.nch = np + 1 := rfl
  -- the costs of the children
  let kc : ℕ → ℕ := fun k => KC + if k = 0 then 400 * J + 10000 else 150 * J + 5000
  have hkc : ∀ k < D.nch, kc k ≤ kidCost w G.n := fun k _ => by
    simp only [kc, kidCost, hKC]; split_ifs <;> omega
  have hsum : ∑ k ∈ Finset.range D.nch, kc k = D.nch * KC + (400 * J + 10000) + np * (150 * J + 5000) := by
    rw [hnch, Finset.sum_range_succ']
    simp only [kc, Nat.succ_ne_zero, ↓reduceIte, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring
  -- the unit facts
  have hU1 : 2000000 ≤ U := by rw [hU]; unfold unitCost; try rw [← hJ]; have := pL_pos G.n; omega
  have hUL : 1000000 * P.L ≤ U := by rw [hU, hL]; unfold unitCost; try rw [← hJ]; omega
  have hset : 10 * (100000 * (Nat.log 2 J + 2 + P.L) * (2 * S + s + 1)) =
      2 * (U * S) + U * s + U := by
    rw [hU, hL]; unfold unitCost; try rw [← hJ]; ring
  have hphi : 400 * (PW.Kφ (J + 5) * Φ0) ≤ 2 * (U * S) + 2 * (U * s) := by
    have h1 := Kφ_le G.n
    rw [← hJ] at h1
    have h2 : 1000000 * (Nat.log 2 J + 3) ≤ U := by
      rw [hU]; unfold unitCost; try rw [← hJ]
      have := pL_pos G.n; omega
    have h3 := Nat.mul_le_mul (h1.trans h2) hΦ
    have e : 400 * PW.Kφ (J + 5) * Φ0 = 400 * (PW.Kφ (J + 5) * Φ0) := by ring
    have e2 : U * (2 * S + 2 * s) = 2 * (U * S) + 2 * (U * s) := by ring
    omega
  have hcj : PW.CJ (J + 5) (pL G.n) * np ≤ U * np + np * (150 * J + 5000) := by
    have := Nat.mul_le_mul_right np (CJ_le G.n)
    simp only [← hJ, ← hU] at this
    have e : (U + 150 * J + 5000) * np = U * np + np * (150 * J + 5000) := by ring
    omega
  have hss : U * s ≤ U * S + U := by
    have := Nat.mul_le_mul_left U hs
    have e : U * (S + 1) = U * S + U := by ring
    omega
  have hs5 : 500000 * s ≤ U * s := Nat.mul_le_mul_right s (by omega)
  have hS1 : 2000 * S ≤ U * S := Nat.mul_le_mul_right S (by omega)
  have hs1 : 1000 * s ≤ U * s := Nat.mul_le_mul_right s (by omega)
  have hcc' : cc ≤ U * a + U * s + U + U * V + D.nch * KC := by
    have e : U * (a + s + 1 + V) = U * a + U * s + U + U * V := by ring
    rw [hccd]; omega
  have hshape : ∀ x, x ≤ U * a + U * S + U * s + U * np + 2 * U + U * V + D.nch * KC +
      (400 * J + 10000) + np * (150 * J + 5000) →
      x ≤ bodyShare bodyA T G P c R D cs + D.nch * kidCost w G.n := fun x hx =>
    body_fit (kc := kc) hL hs hkc (by
      rw [hsum]
      have e : U * (a + S + s + D.nch + 1 + V) =
          U * a + U * S + U * s + U * np + 2 * U + U * V := by rw [hnch]; ring
      rw [← hV, ← ha]
      simp only [← hU, ← hSd, ← hsd]
      omega)
  have hsc : setupCostOf ⟨T, G, P, c, R⟩ =
      100000 * (Nat.log 2 J + 2 + P.L) * (2 * S + s + 1) + 400 * J + 10000 := rfl
  rw [hsc] at hK
  generalize 100000 * (Nat.log 2 J + 2 + P.L) * (2 * S + s + 1) = X1 at hK hset
  refine ⟨hshape _ (by omega), ?_⟩
  have hY := hshape (1000 * (S + s + P.L + 10) + 12 + cc) (by omega)
  have h2 := Nat.mul_le_mul_left (J + 1) hY
  have e : (J + 1) * (1000 * (S + s + P.L + 10) + 12 + cc) =
      1000 * (J + 1) * (S + s + P.L + 10) + 12 * (J + 1) + (J + 1) * cc := by ring
  omega

end MinCostFlow.LowStretch
