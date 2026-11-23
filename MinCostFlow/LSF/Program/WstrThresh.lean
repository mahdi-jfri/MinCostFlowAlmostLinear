module

public import MinCostFlow.LSF.Program.UArithMul
public import MinCostFlow.LSF.Program.Utils

/-!
# The threshold and level-count blocks

The test of `wstrEdgeProc` (`WstrEdge.lean`) needs two blocks of `LB` limbs: the threshold
`θ = 9 H² C L₂² k` of `defaultThreshNat`, and `2 H`, where `H = hldDepthBound n + 1` is the
number of levels, `C = defaultC_ceil K_AN` and `L₂ = log₂(n + 2) + 1`.

The constant `C` does not depend on the input, but it may be larger than a word, so
`emitNatStmt` writes it limb by limb (`Utils.lean`). `threshProc` loads the other factors as
words and multiplies the blocks with `uMulProc`. The product is computed modulo the capacity, so
it is exact when `θ` fits (`threshProd_eq`). The procedure returns `H`. The cost is `O(LB²)`
plus two base-2 logarithms.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- The threshold, as `threshProc` multiplies it. -/
def threshProd (C n k : ℕ) : ℕ :=
  9 * (hldDepthBound n + 1) * (hldDepthBound n + 1) * C * (Nat.log 2 (n + 2) + 1) *
    (Nat.log 2 (n + 2) + 1) * k

lemma threshProd_eq (K_AN : ℝ) {n k : ℕ} (hk : 1 ≤ k) :
    threshProd (defaultC_ceil K_AN) n k = defaultThreshNat K_AN n k := by
  have hC : 1 ≤ defaultC_ceil K_AN := (defaultC_ceil_ge K_AN).2
  unfold threshProd defaultThreshNat
  rw [max_eq_right]
  · ring
  · have h1 : 1 ≤ (hldDepthBound n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (Nat.log 2 (n + 2) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ 9 * (hldDepthBound n + 1) ^ 2 := by omega
    have h4 : 1 ≤ 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    have h5 : 1 ≤ 9 * (hldDepthBound n + 1) ^ 2 * defaultC_ceil K_AN *
        (Nat.log 2 (n + 2) + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- A block that a write does not meet keeps its limbs. -/
lemma blk_keep {m m' : ℕ → ℕ} {d L x h : ℕ} (hfr : ∀ y, y < d ∨ d + L ≤ y → m' y = m y)
    (hx : x + L ≤ d ∨ d + L ≤ x) :
    (Valid m x h L → Valid m' x h L) ∧ unsignedVal m' x h L = unsignedVal m x h L := by
  have hag : ∀ i < L, m' (x + i) = m (x + i) := fun i hi => hfr _ (by omega)
  exact ⟨fun hv i hi => by rw [hag i hi]; exact hv i hi, unsignedVal_congr hag⟩

/-- Args: `[n, k, LB, thOut, k2Out, tA, tB, tF]`. Registers: `8 = log₂ n`, `9 = log₂ (n + 2)`,
`10 = H`, `11 = L₂`, `12` the result of each call. -/
def threshProc (bLog bLoad bMul bEmit : ℕ) : Stmt :=
  .call 8 bLog [.reg 0] ;;
  .call 9 bLog [.bin .add (.reg 0) (.const 2)] ;;
  .assign 10 (.bin .add (.bin .mul (.bin .add (.reg 8) (.const 1)) (.bin .add (.reg 8) (.const 2)))
    (.const 1)) ;;
  .assign 11 (.bin .add (.reg 9) (.const 1)) ;;
  .call 12 bLoad [.reg 5, .reg 2, .const 9] ;;
  .call 12 bLoad [.reg 7, .reg 2, .reg 10] ;;
  .call 12 bMul [.reg 6, .reg 5, .reg 7, .reg 2] ;;
  .call 12 bMul [.reg 5, .reg 6, .reg 7, .reg 2] ;;
  .call 12 bEmit [.reg 7, .reg 2] ;;
  .call 12 bMul [.reg 6, .reg 5, .reg 7, .reg 2] ;;
  .call 12 bLoad [.reg 7, .reg 2, .reg 11] ;;
  .call 12 bMul [.reg 5, .reg 6, .reg 7, .reg 2] ;;
  .call 12 bMul [.reg 6, .reg 5, .reg 7, .reg 2] ;;
  .call 12 bLoad [.reg 7, .reg 2, .reg 1] ;;
  .call 12 bMul [.reg 3, .reg 6, .reg 7, .reg 2] ;;
  .call 12 bLoad [.reg 4, .reg 2, .bin .add (.reg 10) (.reg 10)] ;;
  .ret (.reg 10)

lemma threshProc_noRand (bLog bLoad bMul bEmit : ℕ) :
    (threshProc bLog bLoad bMul bEmit).NoRand := by
  simp [threshProc, Stmt.NoRand]

/-- The contract of `threshProc` for the constant `C`. The five blocks follow each other. -/
def threshContract (w h C : ℕ) : Contract where
  pre args _ := ∃ (n k LB thOut k2Out tA tB tF : ℕ),
    args = [n, k, LB, thOut, k2Out, tA, tB, tF] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ n ∧
    2 * (hldDepthBound n + 1) < 2 ^ w ∧ n + 2 < 2 ^ w ∧ C < capacity h LB ∧
    k2Out + LB ≤ thOut ∧ thOut + LB ≤ tA ∧ tA + LB ≤ tB ∧ tB + LB ≤ tF ∧ tF + LB < 2 ^ w
  post args mem ret mem' := ∃ (n k LB thOut k2Out tA tB tF : ℕ),
    args = [n, k, LB, thOut, k2Out, tA, tB, tF] ∧ ret = hldDepthBound n + 1 ∧
    (∀ a, a < k2Out ∨ tF + LB ≤ a → mem' a = mem a) ∧
    Valid mem' thOut h LB ∧ unsignedVal mem' thOut h LB = threshProd C n k % capacity h LB ∧
    Valid mem' k2Out h LB ∧
    unsignedVal mem' k2Out h LB = 2 * (hldDepthBound n + 1) % capacity h LB
  cost args _ := 500 * args.getD 2 0 * args.getD 2 0 + 1000 * args.getD 2 0 +
    40 * Nat.log 2 (args.getD 0 0 + 2) + 600

theorem thresh_meetsContract {w h C : ℕ} {p : Program} {b bLog bLoad bMul bEmit : ℕ}
    (hLog : MeetsContract w p bLog log2Contract)
    (hLoad : MeetsContract w p bLoad (uLoadWordContract w h))
    (hMul : MeetsContract w p bMul (uMulContract w h))
    (hEmit : MeetsContract w p bEmit (emitNatContract w C h)) (hh : 1 ≤ h)
    (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (threshProc bLog bLoad bMul bEmit)) :
    MeetsContract w p b (threshContract w h C) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, k, LB, thOut, k2Out, tA, tB, tF, rfl, h16, hn1, hHw, hn2, hC, l1, l2, l3, l4, l5⟩ :=
    hpre
  set args := [n, k, LB, thOut, k2Out, tA, tB, tF] with hargs
  have hkw : k < 2 ^ w := hwords k (by simp [hargs])
  have hLBw : LB < 2 ^ w := hwords LB (by simp [hargs])
  have hbw : base h < 2 ^ w := by
    rw [base]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  set c := capacity h LB with hc
  set H := hldDepthBound n + 1 with hH
  set L2 := Nat.log 2 (n + 2) + 1 with hL2
  have hlogn : Nat.log 2 n ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  have hL2w : L2 < 2 ^ w := by
    have := Nat.log_lt_self 2 (show n + 2 ≠ 0 by omega)
    omega
  have hHeq : (Nat.log 2 n + 1) * (Nat.log 2 n + 2) + 1 = H := by
    simp only [hH, hldDepthBound]
  have hprod : (Nat.log 2 n + 1) * (Nat.log 2 n + 2) < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold threshProc
  -- the two logarithms
  refine runs_seq_call_le (vs := [n]) hLog (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl
      omega)
    ⟨n, rfl, hn1⟩ ?_
  rintro g₁ m₀ pos₀ ⟨x₀, heq₀, hm₀, rfl⟩
  simp only [List.cons.injEq, and_true] at heq₀
  subst heq₀
  have hm' : mem = m₀ := hm₀.symm
  subst hm'
  refine runs_seq_call_le (vs := [n + 2]) hLog (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl
      omega)
    ⟨n + 2, rfl, by omega⟩ ?_
  rintro g₂ m₀ pos₀ ⟨x₀, heq₀, hm₀, rfl⟩
  simp only [List.cons.injEq, and_true] at heq₀
  subst heq₀
  have hm' : mem = m₀ := hm₀.symm
  subst hm'
  have hlog2w : Nat.log 2 n + 2 < 2 ^ w := by
    have := Nat.log_lt_self 2 (show n ≠ 0 by omega)
    omega
  refine runs_seq_assign_le (v := H) (by rw [← hHeq]; eval_expr) ?_
  refine runs_seq_assign_le (v := L2) (by simp only [hL2]; eval_expr) ?_
  -- step 1: `tA := 9`
  refine runs_seq_call_le (vs := [tA, LB, 9]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v1 m1 pos1 ⟨d1, L1, x1, heq1, -, hfr1, hv1, hu1⟩
  simp only [List.cons.injEq, and_true] at heq1
  obtain ⟨rfl, rfl, rfl⟩ := heq1
  try dsimp only at hfr1 hv1 hu1
  -- step 2: `tF := H`
  refine runs_seq_call_le (vs := [tF, LB, (hldDepthBound n + 1)]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v2 m2 pos2 ⟨d2, L2, x2, heq2, -, hfr2, hv2, hu2⟩
  simp only [List.cons.injEq, and_true] at heq2
  obtain ⟨rfl, rfl, rfl⟩ := heq2
  try dsimp only at hfr2 hv2 hu2
  obtain ⟨hk2tA, hU2tA⟩ := blk_keep (x := tA) (h := h) hfr2 (by omega)
  have hV2tA := hk2tA hv1
  rw [hu1] at hU2tA
  -- step 3: `tB := tA · tF`
  refine runs_seq_call_le (vs := [tB, tA, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hV2tA, hv2, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v3 m3 pos3 ⟨d3, a3, b3, L3, heq3, -, hfr3, hv3, hu3⟩
  simp only [List.cons.injEq, and_true] at heq3
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq3
  try dsimp only at hfr3 hv3 hu3
  rw [hU2tA, hu2] at hu3
  obtain ⟨hk3tA, hU3tA⟩ := blk_keep (x := tA) (h := h) hfr3 (by omega)
  have hV3tA := hk3tA hV2tA
  rw [hU2tA] at hU3tA
  obtain ⟨hk3tF, hU3tF⟩ := blk_keep (x := tF) (h := h) hfr3 (by omega)
  have hV3tF := hk3tF hv2
  rw [hu2] at hU3tF
  -- step 4: `tA := tB · tF`
  refine runs_seq_call_le (vs := [tA, tB, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hv3, hV3tF, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v4 m4 pos4 ⟨d4, a4, b4, L4, heq4, -, hfr4, hv4, hu4⟩
  simp only [List.cons.injEq, and_true] at heq4
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq4
  try dsimp only at hfr4 hv4 hu4
  rw [hu3, hU3tF] at hu4
  obtain ⟨hk4tF, hU4tF⟩ := blk_keep (x := tF) (h := h) hfr4 (by omega)
  have hV4tF := hk4tF hV3tF
  rw [hU3tF] at hU4tF
  obtain ⟨hk4tB, hU4tB⟩ := blk_keep (x := tB) (h := h) hfr4 (by omega)
  have hV4tB := hk4tB hv3
  rw [hu3] at hU4tB
  -- step 5: `tF := C`
  refine runs_seq_call_le (vs := [tF, LB]) hEmit
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> omega)
    ⟨_, _, rfl, by omega, hbw, (natLimbs_length_le_iff (by omega)).mpr hC, by omega⟩ ?_
  rintro v5 m5 pos5 ⟨d5, L5, heq5, -, hv5, hu5, hfr5⟩
  simp only [List.cons.injEq, and_true] at heq5
  obtain ⟨rfl, rfl⟩ := heq5
  try dsimp only at hfr5 hv5 hu5
  rw [← Nat.mod_eq_of_lt hC] at hu5
  obtain ⟨hk5tB, hU5tB⟩ := blk_keep (x := tB) (h := h) hfr5 (by omega)
  have hV5tB := hk5tB hV4tB
  rw [hU4tB] at hU5tB
  obtain ⟨hk5tA, hU5tA⟩ := blk_keep (x := tA) (h := h) hfr5 (by omega)
  have hV5tA := hk5tA hv4
  rw [hu4] at hU5tA
  -- step 6: `tB := tA · tF`
  refine runs_seq_call_le (vs := [tB, tA, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hV5tA, hv5, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v6 m6 pos6 ⟨d6, a6, b6, L6, heq6, -, hfr6, hv6, hu6⟩
  simp only [List.cons.injEq, and_true] at heq6
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq6
  try dsimp only at hfr6 hv6 hu6
  rw [hU5tA, hu5] at hu6
  obtain ⟨hk6tA, hU6tA⟩ := blk_keep (x := tA) (h := h) hfr6 (by omega)
  have hV6tA := hk6tA hV5tA
  rw [hU5tA] at hU6tA
  obtain ⟨hk6tF, hU6tF⟩ := blk_keep (x := tF) (h := h) hfr6 (by omega)
  have hV6tF := hk6tF hv5
  rw [hu5] at hU6tF
  -- step 7: `tF := L2`
  refine runs_seq_call_le (vs := [tF, LB, (Nat.log 2 (n + 2) + 1)]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v7 m7 pos7 ⟨d7, L7, x7, heq7, -, hfr7, hv7, hu7⟩
  simp only [List.cons.injEq, and_true] at heq7
  obtain ⟨rfl, rfl, rfl⟩ := heq7
  try dsimp only at hfr7 hv7 hu7
  obtain ⟨hk7tA, hU7tA⟩ := blk_keep (x := tA) (h := h) hfr7 (by omega)
  have hV7tA := hk7tA hV6tA
  rw [hU6tA] at hU7tA
  obtain ⟨hk7tB, hU7tB⟩ := blk_keep (x := tB) (h := h) hfr7 (by omega)
  have hV7tB := hk7tB hv6
  rw [hu6] at hU7tB
  -- step 8: `tA := tB · tF`
  refine runs_seq_call_le (vs := [tA, tB, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hV7tB, hv7, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v8 m8 pos8 ⟨d8, a8, b8, L8, heq8, -, hfr8, hv8, hu8⟩
  simp only [List.cons.injEq, and_true] at heq8
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq8
  try dsimp only at hfr8 hv8 hu8
  rw [hU7tB, hu7] at hu8
  obtain ⟨hk8tB, hU8tB⟩ := blk_keep (x := tB) (h := h) hfr8 (by omega)
  have hV8tB := hk8tB hV7tB
  rw [hU7tB] at hU8tB
  obtain ⟨hk8tF, hU8tF⟩ := blk_keep (x := tF) (h := h) hfr8 (by omega)
  have hV8tF := hk8tF hv7
  rw [hu7] at hU8tF
  -- step 9: `tB := tA · tF`
  refine runs_seq_call_le (vs := [tB, tA, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hv8, hV8tF, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v9 m9 pos9 ⟨d9, a9, b9, L9, heq9, -, hfr9, hv9, hu9⟩
  simp only [List.cons.injEq, and_true] at heq9
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq9
  try dsimp only at hfr9 hv9 hu9
  rw [hu8, hU8tF] at hu9
  obtain ⟨hk9tF, hU9tF⟩ := blk_keep (x := tF) (h := h) hfr9 (by omega)
  have hV9tF := hk9tF hV8tF
  rw [hU8tF] at hU9tF
  obtain ⟨hk9tA, hU9tA⟩ := blk_keep (x := tA) (h := h) hfr9 (by omega)
  have hV9tA := hk9tA hv8
  rw [hu8] at hU9tA
  -- step 10: `tF := k`
  refine runs_seq_call_le (vs := [tF, LB, k]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v10 m10 pos10 ⟨d10, L10, x10, heq10, -, hfr10, hv10, hu10⟩
  simp only [List.cons.injEq, and_true] at heq10
  obtain ⟨rfl, rfl, rfl⟩ := heq10
  try dsimp only at hfr10 hv10 hu10
  obtain ⟨hk10tA, hU10tA⟩ := blk_keep (x := tA) (h := h) hfr10 (by omega)
  have hV10tA := hk10tA hV9tA
  rw [hU9tA] at hU10tA
  obtain ⟨hk10tB, hU10tB⟩ := blk_keep (x := tB) (h := h) hfr10 (by omega)
  have hV10tB := hk10tB hv9
  rw [hu9] at hU10tB
  -- step 11: `thOut := tB · tF`
  refine runs_seq_call_le (vs := [thOut, tB, tF, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hV10tB, hv10, by omega, by omega, by omega, by omega, by omega⟩ ?_
  rintro v11 m11 pos11 ⟨d11, a11, b11, L11, heq11, -, hfr11, hv11, hu11⟩
  simp only [List.cons.injEq, and_true] at heq11
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq11
  try dsimp only at hfr11 hv11 hu11
  rw [hU10tB, hu10] at hu11
  obtain ⟨hk11tA, hU11tA⟩ := blk_keep (x := tA) (h := h) hfr11 (by omega)
  have hV11tA := hk11tA hV10tA
  rw [hU10tA] at hU11tA
  obtain ⟨hk11tB, hU11tB⟩ := blk_keep (x := tB) (h := h) hfr11 (by omega)
  have hV11tB := hk11tB hV10tB
  rw [hU10tB] at hU11tB
  obtain ⟨hk11tF, hU11tF⟩ := blk_keep (x := tF) (h := h) hfr11 (by omega)
  have hV11tF := hk11tF hv10
  rw [hu10] at hU11tF
  -- step 12: `k2Out := 2H`
  refine runs_seq_call_le (vs := [k2Out, LB, (hldDepthBound n + 1 + (hldDepthBound n + 1))]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega⟩ ?_
  rintro v12 m12 pos12 ⟨d12, L12, x12, heq12, -, hfr12, hv12, hu12⟩
  simp only [List.cons.injEq, and_true] at heq12
  obtain ⟨rfl, rfl, rfl⟩ := heq12
  try dsimp only at hfr12 hv12 hu12
  obtain ⟨hk12tA, hU12tA⟩ := blk_keep (x := tA) (h := h) hfr12 (by omega)
  have hV12tA := hk12tA hV11tA
  rw [hU11tA] at hU12tA
  obtain ⟨hk12tB, hU12tB⟩ := blk_keep (x := tB) (h := h) hfr12 (by omega)
  have hV12tB := hk12tB hV11tB
  rw [hU11tB] at hU12tB
  obtain ⟨hk12tF, hU12tF⟩ := blk_keep (x := tF) (h := h) hfr12 (by omega)
  have hV12tF := hk12tF hV11tF
  rw [hU11tF] at hU12tF
  obtain ⟨hk12thOut, hU12thOut⟩ := blk_keep (x := thOut) (h := h) hfr12 (by omega)
  have hV12thOut := hk12thOut hv11
  rw [hu11] at hU12thOut
  have mm : ∀ a b : ℕ, (a % capacity h LB) * (b % capacity h LB) % capacity h LB =
      a * b % capacity h LB := fun a b => (Nat.mul_mod a b _).symm
  simp only [hc, mm] at hU12thOut
  have hfr : ∀ a, a < k2Out ∨ tF + LB ≤ a → m12 a = mem a := by
    intro a ha
    rw [hfr12 a (by omega), hfr11 a (by omega), hfr10 a (by omega), hfr9 a (by omega),
      hfr8 a (by omega), hfr7 a (by omega), hfr6 a (by omega), hfr5 a (by omega),
      hfr4 a (by omega), hfr3 a (by omega), hfr2 a (by omega), hfr1 a (by omega)]
  refine runs_ret_le (v := H) (by eval_expr) ⟨n, k, LB, thOut, k2Out, tA, tB, tF, rfl, rfl, hfr,
    hV12thOut, ?_, hv12, ?_⟩ ?_
  · rw [hU12thOut]; rfl
  · rw [hu12]; congr 1; omega
  · simp only [threshContract, uLoadWordContract, uMulContract, emitNatContract, log2Contract,
      hargs, List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Nat.mul_assoc]
    have hn : Nat.log 2 n ≤ Nat.log 2 (n + 2) := hlogn
    have hlen : (natLimbs h C).length ≤ LB := (natLimbs_length_le_iff (by omega)).mpr hC
    omega

end MinCostFlow.LSF.Program
