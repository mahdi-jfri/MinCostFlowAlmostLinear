module

public import MinCostFlow.LowStretch.ProgEntryWord
public import MinCostFlow.LowStretch.ProgEntrySpec

/-!
# The cost of the entry

The cost allowed for the first cluster depends on the merge tree only through bounds that hold for
every merge tree: the work is at most `260 (m + 1) ℓ` with `ℓ = log(n + 2)`, at most `m` pairs
are stored, and the splits still to come cost at most `n (log n + 1) + m + N`
(`KT.visTot_le`). So the part `recMain` of the cost that pays `A · L` per unit is at most
`clB A G` (`recMain_le`), where `clB` depends on `G` only, and
`clCost w A G T ≤ clB A G + 4 n kidCost + 30 m + 500` (`clCost_le`).

The cost per child `kidCost` holds `10⁵ (J + 1)` with `J ≤ 17 pa + 4` and `500 log w`. At word
size `w = wordSize c G.encode` we have `log w ≤ c + log log(n + m + W) + 2`, and
`n log log(5 (m + n + 1)) ≤ (m + 1)(4 pa + 16)`: if `m + n + 1 ≤ (n + 2)^4` this is a bound by
`log n`, and otherwise `n log x ≤ x` (`mul_log_le`). So `4 n kidCost` is at most
`(m + 1)` times a sum of `pa n`, `wsteps W`, `c` and a constant (`kidCost_le`). Then the
preprocessing, the first cluster and the output together cost at most
`K (m + 1) (log(n+2) log log(n+2) + log(n+2) log(log(W+2)+2))` (`entry_cost_le`).

The polynomial bounds `clB A G ≤ 170424 A (m + 1) (n + 2)²` (`clB_le_poly`) and
`kidCost ≤ 2^22 (A + 1) Y` give the word condition of `clC` at word size
`wordSize (340 + A) G.encode` (`clC_word`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited Real

variable {G : WGraph}

/-- A bound on the cost of the cluster procedure at the first cluster that does not depend on the
merge tree. -/
noncomputable def clB (A : ℕ) (G : WGraph) : ℕ :=
  ⌊(A : ℝ) * (162 * log (ell G.n)) * (1052 * ((G.m : ℝ) + 1) * ell G.n)⌋₊

theorem rootRec_S_length_le {T : KT} : (rootRec T G).S.length ≤ G.m := by
  classical
  unfold rootRec
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The splits that the run below the first cluster may still do. -/
theorem hidW_le {T : KT} (hok : (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G))
    (hN : T.N ≤ 2 * G.n) :
    T.hidW (pgOf G) (rootCl T G) ≤ G.n * pa G.n + G.m + 2 * G.n := by
  have h1 := KT.hidW_le_visTot (T := T) (G := pgOf G) (rootCl T G)
  have h2 := KT.visTot_le hok.tree hok.hG
  have hpn : (pgOf G).n = G.n := by simp [pgOf]
  rw [hpn, pgOf_m] at h2
  have hlog : Nat.log 2 G.n + 1 ≤ pa G.n := by
    have := Nat.log_mono_right (b := 2) (show G.n ≤ G.n + 2 by omega)
    unfold pa; omega
  have := Nat.mul_le_mul_left G.n hlog
  omega

/-- **The part of the cost of the cluster procedure at the first cluster that pays `A · L` per
unit** is at most `clB A G`. -/
theorem recMain_le (A : ℕ) (h : Allowed G) {T : KT}
    (hok : (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G)) (hN : T.N ≤ 2 * G.n) :
    recMain A T (pgOf G) (par G.n G.m) (rootCl T G) (rootRec T G) ≤ clB A G := by
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  obtain ⟨θ', T', hθ', hT'⟩ := exists_tree h
  have hnm := n_le_of_spanning (spanning h hθ' hT')
  have hWk := Wk_root_le h hok.inv hnm
  have hG0 := G0_le h
  have hpL := pL_le hn
  have hpa := pa_le G.n
  have hS : ((rootRec T G).S.length : ℝ) ≤ G.m := by exact_mod_cast rootRec_S_length_le
  have hH : (T.hidW (pgOf G) (rootCl T G) : ℝ) ≤ G.n * pa G.n + G.m + 2 * G.n := by
    exact_mod_cast hidW_le hok hN
  have hnm' : (G.n : ℝ) ≤ G.m + 1 := by exact_mod_cast hnm
  have hm : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hpL0 : (0 : ℝ) ≤ pL G.n := Nat.cast_nonneg _
  have hpa0 : (0 : ℝ) ≤ pa G.n := Nat.cast_nonneg _
  have hW : 2 * G0 (pgOf G) (par G.n G.m) + 2 ≤ 260 * ell G.n := by linarith
  have hWk' : (rootCl T G).Wk (pgOf G) (par G.n G.m) ≤ (G.m + 1) * (260 * ell G.n) :=
    hWk.trans (mul_le_mul_of_nonneg_left hW (by linarith))
  have hH' : (T.hidW (pgOf G) (rootCl T G) : ℝ) ≤ (G.m + 1) * (1.45 * ell G.n + 4) := by
    have : (G.n : ℝ) * pa G.n ≤ (G.m + 1) * (1.45 * ell G.n + 1) :=
      mul_le_mul hnm' hpa hpa0 (by linarith)
    nlinarith
  have hsum : 4 * ((G.m + 1) * (260 * ell G.n)) +
      (2 * (T.hidW (pgOf G) (rootCl T G) : ℝ) + (rootRec T G).S.length) ≤
        1052 * ((G.m : ℝ) + 1) * ell G.n := by
    have : (0 : ℝ) ≤ ((G.m : ℝ) + 1) * (ell G.n - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have ha0 : (0 : ℝ) ≤ A * (pL G.n : ℝ) := mul_nonneg hA hpL0
  have hfl : (⌊(A : ℝ) * (pL G.n : ℝ) * (4 * (rootCl T G).Wk (pgOf G) (par G.n G.m) - 2)⌋₊ : ℝ) ≤
      A * (pL G.n : ℝ) * (4 * ((G.m + 1) * (260 * ell G.n))) := by
    rcases le_or_gt 0 ((A : ℝ) * pL G.n * (4 * (rootCl T G).Wk (pgOf G) (par G.n G.m) - 2)) with
      h0 | h0
    · refine (Nat.floor_le h0).trans (mul_le_mul_of_nonneg_left ?_ ha0)
      linarith
    · rw [Nat.floor_eq_zero.mpr (by linarith)]
      have : (0 : ℝ) ≤ ell G.n := by linarith
      simp only [Nat.cast_zero]
      positivity
  have hb : (A : ℝ) * pL G.n ≤ A * (162 * log (ell G.n)) := mul_le_mul_of_nonneg_left hpL hA
  unfold recMain clB
  have hy : (0 : ℝ) ≤ (A : ℝ) * (162 * log (ell G.n)) * (1052 * ((G.m : ℝ) + 1) * ell G.n) := by
    have : (0 : ℝ) ≤ log (ell G.n) := by linarith
    have : (0 : ℝ) ≤ ell G.n := by linarith
    positivity
  rw [Nat.le_floor_iff hy]
  simp only [show (par G.n G.m).L = pL G.n from rfl]
  push_cast
  have hpos : (0 : ℝ) ≤ 1052 * ((G.m : ℝ) + 1) * ell G.n := by
    have : (0 : ℝ) ≤ ell G.n := by linarith
    positivity
  calc (⌊(A : ℝ) * (pL G.n : ℝ) * (4 * (rootCl T G).Wk (pgOf G) (par G.n G.m) - 2)⌋₊ : ℝ) +
        A * pL G.n * (2 * (T.hidW (pgOf G) (rootCl T G) : ℝ) + (rootRec T G).S.length) ≤
        A * pL G.n * (4 * ((G.m + 1) * (260 * ell G.n)) +
          (2 * (T.hidW (pgOf G) (rootCl T G) : ℝ) + (rootRec T G).S.length)) := by
          rw [mul_add]; linarith
    _ ≤ A * pL G.n * (1052 * ((G.m : ℝ) + 1) * ell G.n) := mul_le_mul_of_nonneg_left hsum ha0
    _ ≤ A * (162 * log (ell G.n)) * (1052 * ((G.m : ℝ) + 1) * ell G.n) :=
          mul_le_mul_of_nonneg_right hb hpos

/-- **The cost allowed by `clC`**: `recMain`, `kidCost` for each of the at most `2 n` clusters of
the recursion, and the steps of the root procedure. -/
theorem clCost_le (w A : ℕ) (h : Allowed G) {T : KT}
    (hok : (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G)) (hN : T.N ≤ 2 * G.n) :
    clCost w A G T ≤ clB A G + 4 * G.n * kidCost w G.n + 30 * G.m + 500 := by
  have h1 := recMain_le A h hok hN
  have hcard : (rootCl T G).X.card = G.n := by simp [rootCl, root, pgOf]
  have hpn : (pgOf G).n = G.n := by simp [pgOf]
  have h2 : 2 * kidCost w (pgOf G).n * (2 * (rootCl T G).X.card - 1) ≤
      4 * G.n * kidCost w G.n := by
    rw [hcard, hpn]
    calc 2 * kidCost w G.n * (2 * G.n - 1) ≤ 2 * kidCost w G.n * (2 * G.n) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 4 * G.n * kidCost w G.n := by ring
  unfold clCost recCost
  omega

/-- `n log x ≤ x` when `(n + 1)^4 ≤ x`. -/
theorem mul_log_le {n x : ℕ} (hx : (n + 1) ^ 4 ≤ x) : n * Nat.log 2 x ≤ x := by
  have hsq : ∀ L : ℕ, L * (L + 1) ≤ 2 ^ (L + 1) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      have := Nat.lt_two_pow_self (n := L)
      have e : (L + 1) * (L + 1 + 1) = L * (L + 1) + 2 * (L + 1) := by ring
      have e1 : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
      have e2 : 2 ^ (L + 1 + 1) = 2 * 2 ^ (L + 1) := by rw [pow_succ]; ring
      rw [e, e2]
      omega
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_pow _ _ (by omega)) hx
  have hpow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  set L := Nat.log 2 x with hL
  rcases le_or_gt L ((n + 1) ^ 3) with hle | hlt
  · calc n * L ≤ (n + 1) * (n + 1) ^ 3 := Nat.mul_le_mul (by omega) hle
      _ = (n + 1) ^ 4 := by ring
      _ ≤ x := hx
  · have h1 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [hL'] at hpow ⊢
    calc n * (L' + 1) ≤ L' * (L' + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ (L' + 1) := hsq L'
      _ ≤ x := hpow

/-- Every number of the input is at most `n + m + W`. -/
theorem encode_le (h : Allowed G) : G.encode.foldr max 0 ≤ G.n + G.m + G.maxWeight := by
  refine foldr_max_le fun x hx => ?_
  simp only [WGraph.encode, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | ⟨e, he, hx⟩
  · omega
  · omega
  · have hv := h.valid (e.1, e.2.1) (List.mem_map_of_mem he)
    have hw : e.2.2 ≤ G.maxWeight := foldr_max_le_aux (List.mem_map_of_mem he)
    simp only [WGraph.graph] at hv
    rcases hx with rfl | rfl | rfl <;> omega

/-- `log₂ (log₂ x + 2)` times `n` for `x = 5 (m + n + 1)`. -/
theorem n_loglog_le {n m : ℕ} (hnm : n ≤ m + 1) :
    n * Nat.log 2 (Nat.log 2 (5 * (m + n + 1)) + 2) ≤ (m + 1) * (4 * pa n + 16) := by
  set x := 5 * (m + n + 1) with hx
  have hk : Nat.log 2 (Nat.log 2 x + 2) ≤ Nat.log 2 x + 2 :=
    (Nat.log_lt_self 2 (by omega)).le
  rcases le_or_gt (m + n + 1) ((n + 2) ^ 4) with hA | hB
  · have h1 : n + 2 < 2 ^ pa n := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
      unfold pa; exact this
    have h2 : (n + 2) ^ 4 < (2 ^ pa n) ^ 4 := Nat.pow_lt_pow_left h1 (by norm_num)
    have h3 : x < 2 ^ (4 * pa n + 3) := by
      have e : (2 ^ pa n) ^ 4 = 2 ^ (4 * pa n) := by rw [← pow_mul, mul_comm]
      have e2 : 2 ^ (4 * pa n + 3) = 8 * 2 ^ (4 * pa n) := by rw [pow_add]; ring
      omega
    have h4 : Nat.log 2 x < 4 * pa n + 3 := Nat.log_lt_of_lt_pow (by omega) h3
    exact Nat.mul_le_mul hnm (by omega)
  · have h1 : (n + 1) ^ 4 ≤ x := by
      have : (n + 1) ^ 4 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    have h2 := mul_log_le h1
    have h3 : n * Nat.log 2 (Nat.log 2 x + 2) ≤ n * (Nat.log 2 x + 2) := Nat.mul_le_mul_left _ hk
    have e : n * (Nat.log 2 x + 2) = n * Nat.log 2 x + 2 * n := by ring
    have h4 : (m + 1) * 16 ≤ (m + 1) * (4 * pa n + 16) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- **The cost per child at the first cluster**, summed over `4 n` clusters, at word size
`wordSize c G.encode`. -/
theorem kidCost_le (c : ℕ) (h : Allowed G) :
    4 * G.n * kidCost (wordSize c G.encode) G.n ≤
      (G.m + 1) * (6808000 * pa G.n + 2000 * wsteps G.maxWeight + 2000 * c + 2040000) := by
  obtain ⟨θ', T', hθ', hT'⟩ := exists_tree h
  have hnm := n_le_of_spanning (spanning h hθ' hT')
  have hM := encode_le h
  have hlen := encode_length G
  set W := G.maxWeight
  set Y := G.encode.length + G.encode.foldr max 0 + 2 with hY
  -- `log₂ Y`
  have hY1 : Y ≤ 5 * (G.m + G.n + 1) * (W + 1) := by
    have : 5 * (G.m + G.n + 1) * (W + 1) = 5 * (G.m + G.n + 1) * W + 5 * (G.m + G.n + 1) := by
      ring
    have : W ≤ 5 * (G.m + G.n + 1) * W := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hLY : Nat.log 2 Y ≤ Nat.log 2 (5 * (G.m + G.n + 1)) + Nat.log 2 (W + 1) + 1 :=
    (Nat.log_mono_right hY1).trans (log_mul_le _ _)
  -- `log₂ (log₂ Y + 1)`
  set a := Nat.log 2 (5 * (G.m + G.n + 1))
  set b := Nat.log 2 (W + 1)
  have hab : Nat.log 2 Y + 1 ≤ (a + 2) * (b + 1) := by
    have : (a + 2) * (b + 1) = a * b + a + 2 * b + 2 := by ring
    omega
  have hLL : Nat.log 2 (Nat.log 2 Y + 1) ≤ Nat.log 2 (a + 2) + Nat.log 2 (b + 1) + 1 :=
    (Nat.log_mono_right hab).trans (log_mul_le _ _)
  have hb : Nat.log 2 (b + 1) ≤ wsteps W := by
    have h1 : b ≤ Nat.log 2 W + 1 := by
      rcases Nat.eq_zero_or_pos W with h0 | h0
      · simp [b, h0]
      · have : W + 1 ≤ W * 2 := by omega
        have := (Nat.log_mono_right (b := 2) this).trans_eq
          (Nat.log_mul_base (by norm_num) (by omega))
        exact this
    have h2 : b + 1 ≤ (Nat.log 2 W + 1) * 2 := by omega
    have := (Nat.log_mono_right (b := 2) h2).trans_eq (Nat.log_mul_base (by norm_num) (by omega))
    unfold wsteps; exact this
  -- `log₂ w`
  have hw : Nat.log 2 (wordSize c G.encode) ≤ c + Nat.log 2 (Nat.log 2 Y + 1) + 1 := by
    show Nat.log 2 (c * (Nat.log 2 Y + 1)) ≤ _
    have := log_mul_le c (Nat.log 2 Y + 1)
    have : Nat.log 2 c ≤ c := (Nat.log_le_self 2 c)
    omega
  have hnl := n_loglog_le (n := G.n) (m := G.m) hnm
  have ha2 : a = Nat.log 2 (5 * (G.m + G.n + 1)) := rfl
  -- `J`
  have hJ : rootJ G.n ≤ 17 * pa G.n + 4 := by
    have := pσ_le_pa G.n
    unfold rootJ; omega
  set lw := Nat.log 2 (wordSize c G.encode)
  have hn1 : G.n * lw ≤ (G.m + 1) * (c + 2 + wsteps W) + (G.m + 1) * (4 * pa G.n + 16) := by
    have e1 : G.n * lw ≤ G.n * (c + 2 + wsteps W) + G.n * Nat.log 2 (a + 2) := by
      have : lw ≤ (c + 2 + wsteps W) + Nat.log 2 (a + 2) := by omega
      calc G.n * lw ≤ G.n * ((c + 2 + wsteps W) + Nat.log 2 (a + 2)) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    have e2 : G.n * (c + 2 + wsteps W) ≤ (G.m + 1) * (c + 2 + wsteps W) :=
      Nat.mul_le_mul_right _ hnm
    have e3 : G.n * Nat.log 2 (a + 2) ≤ (G.m + 1) * (4 * pa G.n + 16) := by
      rw [ha2, show G.m + G.n + 1 = G.m + G.n + 1 from rfl]; exact hnl
    omega
  have hnJ : G.n * (rootJ G.n + 1) ≤ (G.m + 1) * (17 * pa G.n + 5) :=
    Nat.mul_le_mul hnm (by omega)
  show 4 * G.n * (100000 * (rootJ G.n + 1) + 500 * (lw + 2)) ≤ _
  have e : 4 * G.n * (100000 * (rootJ G.n + 1) + 500 * (lw + 2)) =
      400000 * (G.n * (rootJ G.n + 1)) + 2000 * (G.n * lw) + 4000 * G.n := by ring
  have e2 : (G.m + 1) * (6808000 * pa G.n + 2000 * wsteps W + 2000 * c + 2040000) =
      400000 * ((G.m + 1) * (17 * pa G.n + 5)) + 2000 * ((G.m + 1) * (c + 2 + wsteps W)) +
        2000 * ((G.m + 1) * (4 * pa G.n + 16)) + 4000 * (G.m + 1) := by ring
  omega

/-- A polynomial bound on `clB`. -/
theorem clB_le_poly (A : ℕ) (h : Allowed G) :
    clB A G ≤ 170424 * A * ((G.m + 1) * (G.n + 2) ^ 2) := by
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hℓn : ell G.n ≤ G.n + 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (G.n : ℝ) + 2 by positivity)
    unfold ell; linarith
  have hlog : log (ell G.n) ≤ G.n + 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ell G.n by linarith)
    linarith
  unfold clB
  refine (Nat.floor_le_floor (b := ((170424 * A * ((G.m + 1) * (G.n + 2) ^ 2) : ℕ) : ℝ)) ?_).trans
    (by rw [Nat.floor_natCast])
  push_cast
  have h1 : (A : ℝ) * (162 * log (ell G.n)) ≤ A * (162 * ((G.n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : 1052 * ((G.m : ℝ) + 1) * ell G.n ≤ 1052 * ((G.m : ℝ) + 1) * ((G.n : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hℓn (by positivity)
  have h0 : (0 : ℝ) ≤ 1052 * ((G.m : ℝ) + 1) * ell G.n := by
    have : (0 : ℝ) ≤ ell G.n := by linarith
    positivity
  calc (A : ℝ) * (162 * log (ell G.n)) * (1052 * ((G.m : ℝ) + 1) * ell G.n) ≤
      A * (162 * ((G.n : ℝ) + 2)) * (1052 * ((G.m : ℝ) + 1) * ((G.n : ℝ) + 2)) :=
        mul_le_mul h1 h2 h0 (by positivity)
    _ = 170424 * A * ((G.m + 1) * (G.n + 2) ^ 2) := by ring

set_option exponentiation.threshold 400 in
/-- The arithmetic of `clC_word`. -/
theorem poly_word {Y X C A H : ℕ} (hY : 2 ≤ Y) (hH : H + 2 ≤ X) (hX : X ≤ 2 ^ 15 * Y ^ 4)
    (hC : C ≤ 2 ^ 25 * (A + 1) * Y ^ 3) :
    H + 30 + 2 ^ 63 * X ^ 14 + 2 ^ 21 * X ^ 4 * C ≤ Y ^ (331 + A) := by
  have h2 : ∀ k, 2 ^ k ≤ Y ^ k := fun k => Nat.pow_le_pow_left hY k
  have hX' : X ≤ Y ^ 19 := hX.trans (by
    calc 2 ^ 15 * Y ^ 4 ≤ Y ^ 15 * Y ^ 4 := Nat.mul_le_mul_right _ (h2 15)
      _ = Y ^ 19 := by rw [← pow_add])
  have hC' : C ≤ (A + 1) * Y ^ 28 := hC.trans (by
    calc 2 ^ 25 * (A + 1) * Y ^ 3 = (A + 1) * (2 ^ 25 * Y ^ 3) := by ring
      _ ≤ (A + 1) * (Y ^ 25 * Y ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (h2 25))
      _ = (A + 1) * Y ^ 28 := by rw [← pow_add])
  have hX14 : X ^ 14 ≤ Y ^ 266 := (Nat.pow_le_pow_left hX' 14).trans_eq (by rw [← pow_mul])
  have hX4 : X ^ 4 ≤ Y ^ 76 := (Nat.pow_le_pow_left hX' 4).trans_eq (by rw [← pow_mul])
  have hA : A + 1 ≤ Y ^ A := (Nat.lt_two_pow_self (n := A)).trans_le (h2 A)
  have hXX : X ≤ X ^ 14 := Nat.le_self_pow (by norm_num) X
  have t1 : 2 ^ 63 * X ^ 14 ≤ Y ^ 329 := by
    calc 2 ^ 63 * X ^ 14 ≤ Y ^ 63 * Y ^ 266 := Nat.mul_le_mul (h2 63) hX14
      _ = Y ^ 329 := by rw [← pow_add]
  have t0 : H + 30 ≤ Y ^ 329 := by
    have : 2 ^ 5 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have : 2 ^ 5 * X ^ 14 ≤ 2 ^ 63 * X ^ 14 := Nat.mul_le_mul_right _ this
    omega
  have t2 : 2 ^ 21 * X ^ 4 * C ≤ (A + 1) * Y ^ 329 := by
    calc 2 ^ 21 * X ^ 4 * C ≤ Y ^ 21 * Y ^ 76 * ((A + 1) * Y ^ 28) :=
          Nat.mul_le_mul (Nat.mul_le_mul (h2 21) hX4) hC'
      _ = (A + 1) * Y ^ 125 := by rw [← pow_add]; ring
      _ ≤ (A + 1) * Y ^ 329 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hY4 : 4 ≤ Y ^ 2 := by nlinarith
  calc H + 30 + 2 ^ 63 * X ^ 14 + 2 ^ 21 * X ^ 4 * C ≤ (A + 1) * (4 * Y ^ 329) := by
        have : Y ^ 329 ≤ (A + 1) * Y ^ 329 := Nat.le_mul_of_pos_left _ (by omega)
        nlinarith
    _ ≤ Y ^ A * (Y ^ 2 * Y ^ 329) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ hY4)
    _ = Y ^ (331 + A) := by rw [← pow_add, ← pow_add]; ring_nf

/-- **The word condition of `clC`** holds at word size `wordSize (340 + A) G.encode`. -/
theorem clC_word (A : ℕ) (h : Allowed G) {T : KT}
    (hok : (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G)) (hN : T.N ≤ 2 * G.n) :
    aH G.n G.m + 30 + 2 ^ 63 * (aH G.n G.m + (pgOf G).maxω + 2) ^ 14 +
      2 ^ 21 * (aH G.n G.m + (pgOf G).maxω + 2) ^ 4 *
        clCost (wordSize (340 + A) G.encode) A G T < 2 ^ wordSize (340 + A) G.encode := by
  have hc := clCost_le (wordSize (340 + A) G.encode) A h hok hN
  have hp := clB_le_poly A h
  have hbase := base_le G
  have hlt := pow_lt_two_pow_wordSize (c := 340 + A) (by omega) G.encode
  have hlen := encode_length G
  have hn := n_le_encode (G := G)
  have hm := m_le_encode (G := G)
  have hpa := pa_le_lin G.n
  set Y := G.encode.length + G.encode.foldr max 0 + 2 with hY
  have hY2 : 2 ≤ Y := by omega
  -- the cost per child
  have hk : kidCost (wordSize (340 + A) G.encode) G.n ≤ 2 ^ 22 * (A + 1) * Y := by
    have h1 : Nat.log 2 (wordSize (340 + A) G.encode) ≤ (340 + A) * Y := by
      refine (Nat.log_le_self 2 _).trans ?_
      show (340 + A) * (Nat.log 2 Y + 1) ≤ _
      refine Nat.mul_le_mul_left _ ?_
      have := Nat.log_lt_self 2 (show Y ≠ 0 by omega)
      omega
    have h2 : rootJ G.n ≤ 38 * Y := by
      have := pσ_le_pa G.n
      unfold rootJ; omega
    unfold kidCost
    have e : 2 ^ 22 * (A + 1) * Y = 4194304 * (A * Y) + 4194304 * Y := by ring
    have e2 : (340 + A) * Y = 340 * Y + A * Y := by ring
    omega
  have hC : clCost (wordSize (340 + A) G.encode) A G T ≤ 2 ^ 25 * (A + 1) * Y ^ 3 := by
    have h1 : (G.m + 1) * (G.n + 2) ^ 2 ≤ Y * Y ^ 2 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
    have e : Y * Y ^ 2 = Y ^ 3 := by ring
    have h2 : 170424 * A * ((G.m + 1) * (G.n + 2) ^ 2) ≤ 170424 * A * Y ^ 3 :=
      Nat.mul_le_mul_left _ (h1.trans_eq e)
    have h3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) Y
    have h4 : 4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n ≤
        4 * Y * (2 ^ 22 * (A + 1) * Y) := Nat.mul_le_mul (by omega) hk
    have e4 : 4 * Y * (2 ^ 22 * (A + 1) * Y) = 16777216 * (A * (Y * Y)) + 16777216 * (Y * Y) := by
      ring
    have h5 : Y * Y ≤ Y ^ 3 := by
      calc Y * Y = Y ^ 2 := by ring
        _ ≤ Y ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : A * (Y * Y) ≤ A * Y ^ 3 := Nat.mul_le_mul_left _ h5
    have e2 : 2 ^ 25 * (A + 1) * Y ^ 3 = 33554432 * (A * Y ^ 3) + 33554432 * Y ^ 3 := by ring
    have e3 : 170424 * A * Y ^ 3 = 170424 * (A * Y ^ 3) := by ring
    omega
  have := poly_word hY2 (le_refl _) hbase hC
  have hle : Y ^ (331 + A) ≤ Y ^ (340 + A) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **The cost of the entry**: the preprocessing, the first cluster and the output. -/
theorem entry_cost_le (A : ℕ) (h : Allowed G) :
    (preCost G + clB A G + 4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n + 30 * G.m +
      17 * G.n + 1500 : ℝ) ≤
      (800000000 + 250000 * A) * (G.m + 1) *
        (logLogFactor G.n + weightFactor G.n G.maxWeight) := by
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  obtain ⟨θ', T', hθ', hT'⟩ := exists_tree h
  have hnm := n_le_of_spanning (spanning h hθ' hT')
  have hnm' : (G.n : ℝ) ≤ G.m + 1 := by exact_mod_cast hnm
  have hm : (0 : ℝ) ≤ G.m + 1 := by positivity
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hLLF : logLogFactor G.n = ell G.n * log (ell G.n) := rfl
  have hL1 : (1 : ℝ) ≤ 39 * (ell G.n * log (ell G.n)) := by nlinarith
  -- the preprocessing
  have hpre : (preCost G : ℝ) ≤ 20000 * (G.m + 1) * (pa G.n + wsteps G.maxWeight) := by
    exact_mod_cast preCost_le h
  have hpa : (pa G.n : ℝ) ≤ 100 * (ell G.n * log (ell G.n)) := by
    have := pa_le G.n
    nlinarith
  have hws := wsteps_le G.maxWeight
  have hwF : weightFactor G.n G.maxWeight = ell G.n * log (log ((G.maxWeight : ℝ) + 2) + 2) :=
    rfl
  have hl2 := log_two_gt
  have hLw : log 2 ≤ log (log ((G.maxWeight : ℝ) + 2) + 2) := by
    have : log 2 ≤ log ((G.maxWeight : ℝ) + 2) := Real.log_le_log (by norm_num) (by
      linarith [(Nat.cast_nonneg G.maxWeight : (0 : ℝ) ≤ G.maxWeight)])
    exact Real.log_le_log (by norm_num) (by linarith)
  have hws' : (wsteps G.maxWeight : ℝ) ≤ 4 * weightFactor G.n G.maxWeight := by
    rw [hwF]; nlinarith
  have hwF0 : 0 ≤ weightFactor G.n G.maxWeight := by rw [hwF]; nlinarith
  have hpre' : (preCost G : ℝ) ≤
      (G.m + 1) * (2000000 * (ell G.n * log (ell G.n)) + 80000 * weightFactor G.n G.maxWeight) := by
    have := mul_le_mul_of_nonneg_left (add_le_add hpa hws') (show (0 : ℝ) ≤ 20000 * (G.m + 1) by
      positivity)
    nlinarith
  -- the first cluster
  have hcl : (clB A G : ℝ) ≤ (G.m + 1) * (170424 * A * (ell G.n * log (ell G.n))) := by
    unfold clB
    refine (Nat.floor_le (by
      have : (0 : ℝ) ≤ log (ell G.n) := by linarith
      positivity)).trans (le_of_eq (by ring))
  -- the cost per child
  have hkid0 : ((4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n : ℕ) : ℝ) ≤
      (G.m + 1) * (6808000 * pa G.n + 2000 * wsteps G.maxWeight + 2000 * (340 + A) + 2040000) := by
    exact_mod_cast kidCost_le (340 + A) h
  have hkid : ((4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n : ℕ) : ℝ) ≤
      (G.m + 1) * ((786880000 + 78000 * A) * (ell G.n * log (ell G.n)) +
        8000 * weightFactor G.n G.maxWeight) := by
    have h1 : (6808000 * pa G.n + 2000 * wsteps G.maxWeight + 2000 * (340 + A) + 2040000 : ℝ) ≤
        (786880000 + 78000 * A) * (ell G.n * log (ell G.n)) +
          8000 * weightFactor G.n G.maxWeight := by
      have : (2720000 + 2000 * A : ℝ) ≤ (106080000 + 78000 * A) * (ell G.n * log (ell G.n)) := by
        nlinarith
      nlinarith
    exact hkid0.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h1) hm)
  push_cast at hkid
  -- the rest
  have hrest : (30 * G.m + 17 * G.n + 1500 : ℝ) ≤
      (G.m + 1) * (60333 * (ell G.n * log (ell G.n))) := by
    nlinarith
  rw [hLLF]
  have hAm : 0 ≤ (A : ℝ) * (G.m + 1) * (ell G.n * log (ell G.n)) := by
    have : (0 : ℝ) ≤ log (ell G.n) := by linarith
    have : (0 : ℝ) ≤ ell G.n := by linarith
    positivity
  have hLm : 0 ≤ ((G.m : ℝ) + 1) * (ell G.n * log (ell G.n)) := by
    have : (0 : ℝ) ≤ log (ell G.n) := by linarith
    have : (0 : ℝ) ≤ ell G.n := by linarith
    positivity
  have hWm : 0 ≤ ((G.m : ℝ) + 1) * weightFactor G.n G.maxWeight := mul_nonneg hm hwF0
  have hAW : 0 ≤ (A : ℝ) * ((G.m + 1) * weightFactor G.n G.maxWeight) := mul_nonneg hA hWm
  nlinarith

end MinCostFlow.LowStretch
