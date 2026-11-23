module

public import MinCostFlow.LowStretch.ProgPreCost

/-!
# The word size of the entry

The program runs at word size `wordSize c G.encode` with `c ≥ 320`. Let `X` be the length of the
input plus its largest number plus `2`. Then `n`, `m` and the largest weight are at most `X`, every
rounded weight is at most `2^14 X^4`, and so the number `aH + maxω + 2` of the word bound of the
preprocessing is at most `2^15 X^4` (`base_le`). Its `16`-th power is at most `X^320`, which fits
in a word (`word_bound`). The threshold of the first cluster also fits in a word (`rootθ_lt`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

variable {G : WGraph}

theorem encode_length (G : WGraph) : G.encode.length = 2 + 3 * G.m := by
  obtain ⟨n, E⟩ := G
  simp only [WGraph.encode, WGraph.m, List.length_cons]
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    simp at ih ⊢
    omega

theorem n_le_encode : G.n ≤ G.encode.foldr max 0 :=
  foldr_max_le_aux (by simp [WGraph.encode])

theorem m_le_encode : G.m ≤ G.encode.foldr max 0 :=
  foldr_max_le_aux (by simp [WGraph.encode])

theorem maxWeight_le_encode : G.maxWeight ≤ G.encode.foldr max 0 := by
  unfold WGraph.maxWeight
  refine foldr_max_le fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact foldr_max_le_aux (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨e, he, by simp⟩)))

theorem pow_log_le_succ (x : ℕ) : 2 ^ Nat.log 2 x ≤ x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega); omega

/-- The number `aH + maxω + 2` is at most `2^15 Y^4`, where `Y` is the length of the input plus its
largest number plus `2`. -/
theorem base_le (G : WGraph) : aH G.n G.m + (pgOf G).maxω + 2 ≤
    2 ^ 15 * (G.encode.length + G.encode.foldr max 0 + 2) ^ 4 := by
  have hlen := encode_length G
  have hn := n_le_encode (G := G)
  have hm := m_le_encode (G := G)
  have hW := maxWeight_le_encode (G := G)
  generalize G.encode.foldr max 0 = M at *
  generalize G.encode.length = len at *
  set X := len + M + 2 with hXd
  have hX2 : 2 ≤ X := by omega
  have hX3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hn4 : G.n + 4 ≤ 2 * X := by omega
  have hB : 8 * pB G.n * G.n ≤ 2048 * X ^ 3 :=
    calc 8 * pB G.n * G.n ≤ 8 * (64 * (G.n + 4) ^ 2) * G.n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (pB_le_poly G.n))
      _ ≤ 8 * (64 * (2 * X) ^ 2) * X :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left 64
            (Nat.pow_le_pow_left hn4 2))) (by omega)
      _ = 2048 * X ^ 3 := by ring
  have hσ : 2 ^ pσ G.n ≤ 2 ^ 14 * X ^ 3 := by
    unfold pσ
    rw [pow_succ]
    have := pow_log_le_succ (8 * pB G.n * G.n)
    omega
  have hL : 2 ^ Nat.log 2 G.maxWeight ≤ X := by
    have := pow_log_le_succ G.maxWeight; omega
  have hω : (pgOf G).maxω ≤ 2 ^ 14 * X ^ 4 :=
    calc (pgOf G).maxω ≤ 2 ^ (Nat.log 2 G.maxWeight + pσ G.n) := maxω_le
      _ = 2 ^ Nat.log 2 G.maxWeight * 2 ^ pσ G.n := pow_add _ _ _
      _ ≤ X * (2 ^ 14 * X ^ 3) := Nat.mul_le_mul hL hσ
      _ = 2 ^ 14 * X ^ 4 := by ring
  have hX4 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
  unfold aH; omega

/-- **The word bound of the preprocessing** holds at word size `wordSize c G.encode` for
`c ≥ 320`. -/
theorem word_bound {c : ℕ} (hc : 320 ≤ c) (G : WGraph) :
    (aH G.n G.m + (pgOf G).maxω + 2) ^ 16 < 2 ^ wordSize c G.encode := by
  have hlt := pow_lt_two_pow_wordSize (c := c) (by omega) G.encode
  have hbase := base_le G
  set X := G.encode.length + G.encode.foldr max 0 + 2 with hXd
  have hX2 : 2 ≤ X := by omega
  calc (aH G.n G.m + (pgOf G).maxω + 2) ^ 16 ≤ (2 ^ 15 * X ^ 4) ^ 16 := Nat.pow_le_pow_left hbase 16
    _ = 2 ^ 240 * X ^ 64 := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ X ^ 240 * X ^ 64 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX2 240)
    _ = X ^ 304 := by rw [← pow_add]
    _ ≤ X ^ c := Nat.pow_le_pow_right (by omega) (by omega)
    _ < _ := hlt

/-- The threshold of the first cluster fits in a word. -/
theorem rootθ_lt {w : ℕ} {mem : ℕ → ℕ} {T : KT} (hI : InG w G mem) (hT : T.Ok (pgOf G)) :
    rootθ T G < 2 ^ w := by
  have h1 := hI.add_lt
  have h2 := hI.par_lt
  have hmw : T.mw (T.N - 1) ≤ (pgOf G).maxω := KT.mw_le_maxω hT (by have := hT.n_lt; omega)
  have hB : 256 * (4 * pB G.n * G.n) ≤ 2 ^ 16 * (G.n + 4) ^ 4 :=
    calc 256 * (4 * pB G.n * G.n) ≤ 256 * (4 * (64 * (G.n + 4) ^ 2) * (G.n + 4)) :=
          Nat.mul_le_mul_left 256 (Nat.mul_le_mul (Nat.mul_le_mul_left 4 (pB_le_poly G.n))
            (by omega))
      _ = 2 ^ 16 * (G.n + 4) ^ 3 := by ring
      _ ≤ 2 ^ 16 * (G.n + 4) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hθ : rootθ T G ≤ max (T.mw (T.N - 1)) (4 * pB G.n * G.n) + 1 := by
    unfold rootθ thr
    exact (pow_log_le_succ _).trans (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
  have : max (T.mw (T.N - 1)) (4 * pB G.n * G.n) ≤ (pgOf G).maxω + 4 * pB G.n * G.n := by
    omega
  omega

end MinCostFlow.LowStretch
