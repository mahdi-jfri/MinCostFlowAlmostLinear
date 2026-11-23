module

public import MinCostFlow.LowStretch.ProgClusterSetupO4
public import MinCostFlow.LowStretch.ProgClusterSetupW

/-!
# The setup of a cluster: the sizes of the numbers that the petal searches multiply

The petal searches multiply the weights `2^Es / ω` of the active pairs by lengths up to `Δ` and
by the entries of the table `SQ`, which are up to `Sm = 2^2^L + Δ` (`PW.Ok.wT2`, `LW.wT1`).
Each of the three factors can be as large as the largest weight `Mw`: `2^Es` is the largest
weight of an active pair (`SuAt.pow_Es_le`), and `Δ ≤ n Mw`. So these products need room
`Mw³` in a word, which `SuRoom3` (in `setupPre`) asks. The other word bounds need only `Mw²`.

The first part gives the bounds on the start `loS` of the special petal (`loS_bw_le`,
`loS_far`); the second the bound on `2^Es`; the third the product `wT1` (`SuAt.wT1`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The start of the special petal -/

/-- `(L + 1) ⌊⌊Δ / 8⌋ / L⌋ ≤ 2 ⌊Δ / 8⌋`. -/
theorem succ_mul_div_le {Δ L : ℕ} : (L + 1) * (Δ / 8 / L) ≤ 2 * (Δ / 8) := by
  have h1 : L * (Δ / 8 / L) ≤ Δ / 8 := Nat.mul_div_le _ _
  have h2 : Δ / 8 / L ≤ Δ / 8 := Nat.div_le_self _ _
  rw [Nat.add_mul, one_mul]; omega

/-- The ranges of the special petal end by `Δ`: `loS + (L + 1) bw ≤ Δ`, for a target at
distance `d ≤ Δ`. -/
theorem loS_bw_le {Δ L d : ℕ} (hd : d ≤ Δ) :
    d - (Δ + 1) / 2 - Δ / 8 + (L + 1) * (Δ / 8 / L) ≤ Δ := by
  have := succ_mul_div_le (Δ := Δ) (L := L); omega

/-- For a far target (`5 Δ < 8 d`) and `Δ ≥ 1`, the last but one range of the special petal
ends before the target: `loS + L bw < d`. -/
theorem loS_far {Δ L d : ℕ} (hΔ : 1 ≤ Δ) (h5 : 5 * Δ < 8 * d) :
    d - (Δ + 1) / 2 - Δ / 8 + L * (Δ / 8 / L) < d := by
  have h1 : L * (Δ / 8 / L) ≤ Δ / 8 := Nat.mul_div_le _ _
  omega

/-! ### The largest weight of an active pair -/

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- **`2^Es` is at most the largest weight**, plus one: `Es` is `0` or the exponent of an
active pair, whose weight is `2^Es`. -/
theorem SuAt.pow_Es_le (hp : ClPre w A T G P c R GB RB h mem) {Mw : ℕ}
    (hMw : ∀ p < G.m, G.pω p ≤ Mw) : 2 ^ a.Es ≤ Mw + 1 := by
  rcases a.es_eq with h0 | ⟨j, hj, he⟩
  · rw [h0]; omega
  · have := SuAt.nA_le (a := a)
    rw [a.t4 j hj, a.n3_low (x := SuN.z 𝔑 0 8 0 2 + 2 * j) (by simp only [SuN.z]; omega),
      a.n3_low (a.exp_lt hp hj), a.exp_eq hp hj] at he
    have hx := (hp.actEnt a.hM hj).1.ex
    have hm := hMw _ (a.pr_lt hp hj)
    rw [he]
    have e : G.pω (a.W.pr j) = 2 ^ mem ((GlobL.read mem GB).EXP + a.W.pr j) := hx
    omega

/-! ### The product of the petal searches -/

/-- The arithmetic of `wT1`: with `M ≤ Y`, `κ + nA ≤ 2 K`, `b ≤ K Y`, `nA M ≤ K Y` and
`S + 1 ≤ 257 Q² K Y`, the product is at most `2^20 Q² K³ Y³`. -/
theorem wT1_arith {Q K Y M κ nA b S : ℕ} (hM : M ≤ Y) (hκ : κ + nA ≤ 2 * K) (hb : b ≤ K * Y)
    (hnA : nA * M ≤ K * Y) (hS : S + 1 ≤ 257 * (Q ^ 2 * K * Y)) (hK : 1 ≤ K) (hY : 1 ≤ Y) :
    (8 * M * (κ + nA) + b * (nA * M)) * (S + 1) ≤ 2 ^ 20 * Q ^ 2 * K ^ 3 * Y ^ 3 := by
  have hKY : 1 ≤ K * Y := Nat.mul_le_mul hK hY
  have h1 : 8 * M * (κ + nA) ≤ 16 * (K * Y) * (K * Y) := by
    calc 8 * M * (κ + nA) ≤ 8 * Y * (2 * K) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hκ
      _ = 16 * (K * Y) * 1 := by ring
      _ ≤ 16 * (K * Y) * (K * Y) := Nat.mul_le_mul_left _ hKY
  have h2 : b * (nA * M) ≤ (K * Y) * (K * Y) := Nat.mul_le_mul hb hnA
  have e1 : 16 * (K * Y) * (K * Y) = 16 * ((K * Y) * (K * Y)) := by ring
  have e2 : 17 * (K * Y) * (K * Y) = 17 * ((K * Y) * (K * Y)) := by ring
  calc (8 * M * (κ + nA) + b * (nA * M)) * (S + 1)
      ≤ (17 * (K * Y) * (K * Y)) * (257 * (Q ^ 2 * K * Y)) := Nat.mul_le_mul (by omega) hS
    _ = 4369 * Q ^ 2 * K ^ 3 * Y ^ 3 := by ring
    _ ≤ 2 ^ 20 * Q ^ 2 * K ^ 3 * Y ^ 3 := by gcongr; norm_num

set_option maxHeartbeats 1000000 in
/-- **The product `wT1` of the petal searches is a word.** -/
theorem SuAt.wT1 (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    (h3 : SuRoom3 w T G h) :
    (8 * a.W.M * (a.W.κ + a.W.nA) +
        (c.loS G + (a.W.Lb + 1) * a.W.bw + 1) * (a.W.nA * 2 ^ a.W.Es)) * (a.W.Sm + 1) <
      2 ^ w := by
  obtain ⟨Mw, hMw, hroom⟩ := h3
  have hEs := a.pow_Es_le hp hMw
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hp.ok.inv.sub
    simpa using this
  have hΔ : c.Δ G ≤ G.n * Mw :=
    (Cl.Δ_le_card_mul hp.ok.inv.good.conn hMw).trans (Nat.mul_le_mul_right _ hcard)
  have hN := hp.ok.tree.n_lt
  have hS := hp.ok.S_le
  have hnA := SuAt.nA_le (a := a)
  have hnS : (RecL.read mem RB).nS = R.S.length := hp.recAt.arcs.nS
  have vnS : SuN.nS 𝔑 = (RecL.read mem RB).nS := rfl
  have hm : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hn : (GlobL.read mem GB).n = G.n := hp.glob.n
  have hL1 : 1 ≤ P.L := by rw [hp.L_eq]; have := log_pa_le G.n; omega
  set K := T.N + G.m + 2 with hK
  set Y := Mw + 2 with hY
  set Q := 2 ^ rootJ G.n with hQ
  have hdt : c.d G c.x0 c.t ≤ c.Δ G := Cl.d_le_Δ hp.ok.inv.t_mem
  have hlo := loS_bw_le (Δ := c.Δ G) (d := c.d G c.x0 c.t) (L := P.L) hdt
  have hnK : G.n + 2 ≤ K := by omega
  have hnY : G.n * Mw + 1 ≤ K * Y := by
    have h1 : (G.n + 2) * (Mw + 2) ≤ K * Y := Nat.mul_le_mul hnK le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    omega
  -- `(n + 2)² ≤ 2^J`, so `2^2^L ≤ 256 Q²`
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ (GlobL.read mem GB).J := hp.glob.hJ
  rw [hp.J_eq] at hJ0
  have hB1 : 1 ≤ P.B := hp.ok.hB
  have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
  have hn2 : (G.n + 2) ^ 2 ≤ Q := by
    have : (G.n + 2) ^ 2 ≤ 9 * G.n ^ 2 := by nlinarith
    have : 9 * G.n ^ 2 ≤ 128 * P.B * G.n ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hp2 : 2 ^ 2 ^ P.L ≤ 256 * Q ^ 2 := by
    rw [hp.L_eq]
    refine (two_pow_two_pow_pL_le G.n).trans (Nat.mul_le_mul_left _ ?_)
    rw [show (G.n + 2) ^ 4 = ((G.n + 2) ^ 2) ^ 2 by ring]
    exact Nat.pow_le_pow_left hn2 2
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hK1 : 1 ≤ K := by omega
  have hY1 : 1 ≤ Y := by omega
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hQKY : K * Y ≤ Q ^ 2 * K * Y :=
    calc K * Y ≤ Q ^ 2 * (K * Y) := Nat.le_mul_of_pos_left _ hQ2
      _ = Q ^ 2 * K * Y := by ring
  have hQKY' : Q ^ 2 ≤ Q ^ 2 * K * Y := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_le_mul hK1 hY1)
  have hκ : G.m / (G.n * G.n) ≤ G.m := Nat.div_le_self _ _
  have hA := Nat.mul_le_mul (show a.hM.nA ≤ G.m by omega) hEs
  have hA' : G.m * (Mw + 1) ≤ K * Y := Nat.mul_le_mul (by omega) (by omega)
  have key := wT1_arith (Q := Q) (K := K) (Y := Y) (M := 2 ^ a.Es)
    (κ := G.m / (G.n * G.n) + 1) (nA := a.hM.nA)
    (b := c.loS G + (P.L + 1) * (c.Δ G / 8 / P.L) + 1)
    (S := 2 ^ 2 ^ P.L + c.Δ G) (by omega) (by omega) (by unfold Cl.loS; omega)
    (by omega) (by omega) hK1 hY1
  have e : 2 ^ (2 * rootJ G.n + 20) * K ^ 3 * Y ^ 3 = 2 ^ 20 * Q ^ 2 * K ^ 3 * Y ^ 3 := by
    rw [hQ, ← pow_mul, show 2 * rootJ G.n + 20 = 20 + rootJ G.n * 2 by ring, pow_add]
  show (8 * 2 ^ a.Es * ((GlobL.read mem GB).m / ((GlobL.read mem GB).n *
      (GlobL.read mem GB).n) + 1 + a.hM.nA) + (c.loS G + (P.L + 1) * (c.Δ G / 8 / P.L) + 1) *
      (a.hM.nA * 2 ^ a.Es)) * (2 ^ 2 ^ P.L + c.Δ G + 1) < 2 ^ w
  rw [hm, hn]
  omega

end MinCostFlow.LowStretch
