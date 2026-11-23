module

public import MinCostFlow.LSF.Program.UExt
public import MinCostFlow.Num.UnsignedLess

/-!
# The stretch of one edge

After the levels, an edge with length block `E` (the integer length `ℓ_int`) and accumulator
`A` (the sum of the level distances, at the same scale) has the raw stretch
`(2 K E + 2 A) / E`, where `K` is the number of levels. The model sets the stretch to `1` when
the raw stretch is at least the threshold `θ`, and keeps it otherwise.

`wstrEdgeProc` computes, in blocks of `LB` limbs and modulo the capacity,
`N = 2 A + K₂ E` (with `K₂ = 2 K` given as a block) and `Y = θ E`. If `N < Y` it writes the low
`L_w` limbs of `N` and of `E` as the numerator and denominator, and returns `0`. Otherwise it
writes `1` and `1`, and returns `1` (the edge is "high"). The cost is `O(LB²)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- The numerator that `wstrEdgeProc` computes, modulo the capacity `c`. -/
def wstrNumVal (c A K2 E : ℕ) : ℕ := (((0 + A) % c + A) % c + K2 * E % c) % c

lemma wstrNumVal_eq {c A K2 E : ℕ} (hfit : 2 * A + K2 * E < c) :
    wstrNumVal c A K2 E = 2 * A + K2 * E := by
  unfold wstrNumVal
  rw [zero_add, Nat.mod_eq_of_lt (show A < c by omega), Nat.mod_eq_of_lt (show A + A < c by omega),
    Nat.mod_eq_of_lt (show K2 * E < c by omega),
    Nat.mod_eq_of_lt (show A + A + K2 * E < c by omega)]
  omega

/-- Args: `[numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB, Lw]`. Register `10` is the result
of each call, register `11` is the comparison. -/
def wstrEdgeProc (bLoad bAcc bMul bLess bExt : ℕ) : Stmt :=
  .call 10 bLoad [.reg 6, .reg 8, .const 0] ;;
  .call 10 bAcc [.reg 6, .reg 2, .reg 8, .const 1, .const 0] ;;
  .call 10 bAcc [.reg 6, .reg 2, .reg 8, .const 1, .const 0] ;;
  .call 10 bMul [.reg 7, .reg 5, .reg 3, .reg 8] ;;
  .call 10 bAcc [.reg 6, .reg 7, .reg 8, .const 1, .const 0] ;;
  .call 10 bMul [.reg 7, .reg 4, .reg 3, .reg 8] ;;
  .call 11 bLess [.reg 6, .reg 7, .reg 8] ;;
  .cond (.reg 11)
    (.call 10 bExt [.reg 0, .reg 6, .reg 9, .reg 9] ;;
     .call 10 bExt [.reg 1, .reg 3, .reg 9, .reg 9] ;;
     .ret (.const 0))
    (.call 10 bLoad [.reg 0, .reg 9, .const 1] ;;
     .call 10 bLoad [.reg 1, .reg 9, .const 1] ;;
     .ret (.const 1))

lemma wstrEdgeProc_noRand (bLoad bAcc bMul bLess bExt : ℕ) :
    (wstrEdgeProc bLoad bAcc bMul bLess bExt).NoRand := by
  simp [wstrEdgeProc, Stmt.NoRand]

/-- The layout of `wstrEdgeProc`: the four source blocks lie below `tmp1`, the two scratch
blocks follow, and the two output blocks lie below everything else. -/
def WstrEdgeLayout (w h : ℕ) (mem : ℕ → ℕ) (numOut denOut acc le th k2 tmp1 tmp2 LB Lw : ℕ) :
    Prop :=
  16 ≤ 2 ^ w ∧ Lw ≤ LB ∧
  Valid mem acc h LB ∧ Valid mem le h LB ∧ Valid mem th h LB ∧ Valid mem k2 h LB ∧
  acc + LB ≤ tmp1 ∧ le + LB ≤ tmp1 ∧ th + LB ≤ tmp1 ∧ k2 + LB ≤ tmp1 ∧ tmp1 + LB ≤ tmp2 ∧
  tmp2 + LB < 2 ^ w ∧
  (∃ lo, lo ≤ acc ∧ lo ≤ le ∧ lo ≤ th ∧ lo ≤ k2 ∧ numOut + Lw ≤ lo ∧ denOut + Lw ≤ lo) ∧
  (numOut + Lw ≤ denOut ∨ denOut + Lw ≤ numOut)

/-- The contract of `wstrEdgeProc`. -/
def wstrEdgeContract (w h : ℕ) : Contract where
  pre args mem := ∃ (numOut denOut acc le th k2 tmp1 tmp2 LB Lw : ℕ),
    args = [numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB, Lw] ∧
    WstrEdgeLayout w h mem numOut denOut acc le th k2 tmp1 tmp2 LB Lw
  post args mem ret mem' := ∃ (numOut denOut acc le th k2 tmp1 tmp2 LB Lw : ℕ),
    args = [numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB, Lw] ∧
    (∀ a, (a < numOut ∨ numOut + Lw ≤ a) → (a < denOut ∨ denOut + Lw ≤ a) →
      (a < tmp1 ∨ tmp2 + LB ≤ a) → mem' a = mem a) ∧
    Valid mem' numOut h Lw ∧ Valid mem' denOut h Lw ∧
    let c := capacity h LB
    let A := unsignedVal mem acc h LB
    let E := unsignedVal mem le h LB
    let N := wstrNumVal c A (unsignedVal mem k2 h LB) E
    let Y := unsignedVal mem th h LB * E % c
    (N < Y → ret = 0 ∧ unsignedVal mem' numOut h Lw = N % capacity h Lw ∧
      unsignedVal mem' denOut h Lw = E % capacity h Lw) ∧
    (¬ N < Y → ret = 1 ∧ unsignedVal mem' numOut h Lw = 1 % capacity h Lw ∧
      unsignedVal mem' denOut h Lw = 1 % capacity h Lw)
  cost args _ := 200 * args.getD 8 0 * args.getD 8 0 + 600 * args.getD 8 0 + 500

theorem wstrEdge_meetsContract {w h : ℕ} {p : Program} {b bLoad bAcc bMul bLess bExt : ℕ}
    (hLoad : MeetsContract w p bLoad (uLoadWordContract w h))
    (hAcc : MeetsContract w p bAcc (uAccContract w h))
    (hMul : MeetsContract w p bMul (uMulContract w h))
    (hLess : MeetsContract w p bLess (unsignedLessContract w h))
    (hExt : MeetsContract w p bExt (uExtContract w h)) (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (wstrEdgeProc bLoad bAcc bMul bLess bExt)) :
    MeetsContract w p b (wstrEdgeContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB, Lw, rfl, h16, hLw, hva, hvl, hvt, hvk,
    hacc, hle, hth, hk2, ht12, ht2w, ⟨lo, hlo1, hlo2, hlo3, hlo4, hno, hdo⟩, hnd⟩ := hpre
  have hB0 : 0 < base h := base_pos h
  have hk1 : 1 < base h := by
    rw [base]; exact Nat.one_lt_two_pow (by omega)
  set args := [numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB, Lw] with hargs
  have hR : ∀ i < 10, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have r0 := hR 0 (by omega); have r1 := hR 1 (by omega); have r2 := hR 2 (by omega)
  have r3 := hR 3 (by omega); have r4 := hR 4 (by omega); have r5 := hR 5 (by omega)
  have r6 := hR 6 (by omega); have r7 := hR 7 (by omega); have r8 := hR 8 (by omega)
  have r9 := hR 9 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hw1 : 1 < 2 ^ w := by omega
  -- the sources do not change while the scratch blocks are written
  have hsrc : ∀ (m : ℕ → ℕ), (∀ a, a < tmp1 → m a = mem a) → ∀ x, x + LB ≤ tmp1 →
      Valid mem x h LB → Valid m x h LB ∧ unsignedVal m x h LB = unsignedVal mem x h LB := by
    intro m hm x hx hv
    have hag : ∀ i < LB, m (x + i) = mem (x + i) := fun i hi => hm _ (by omega)
    exact ⟨fun i hi => by rw [hag i hi]; exact hv i hi, unsignedVal_congr hag⟩
  refine runs_start_le ?_
  unfold wstrEdgeProc
  -- 1. `tmp1 := 0`
  refine runs_seq_call_le (vs := [tmp1, LB, 0]) hLoad
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨tmp1, LB, 0, rfl, by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨d₁, L₁, x₁, heq₁, -, hfr₁, hv₁, hu₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hv₁ hu₁
  have hlo₁ : ∀ a, a < tmp1 → m₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  -- 2, 3. `tmp1 += acc` twice
  obtain ⟨hva₁, hUa₁⟩ := hsrc m₁ hlo₁ acc hacc hva
  refine runs_seq_call_le (vs := [tmp1, acc, LB, 1, 0]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, rfl, by omega, hk1, hv₁, hva₁, Or.inl hacc, by omega, by omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨d₂, a₂, L₂, k₂, n₂, heq₂, -, hfr₂, hv₂, hu₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hv₂ hu₂
  have hlo₂ : ∀ a, a < tmp1 → m₂ a = mem a := fun a ha => (hfr₂ a (Or.inl ha)).trans (hlo₁ a ha)
  obtain ⟨hva₂, hUa₂⟩ := hsrc m₂ hlo₂ acc hacc hva
  refine runs_seq_call_le (vs := [tmp1, acc, LB, 1, 0]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, rfl, by omega, hk1, hv₂, hva₂, Or.inl hacc, by omega, by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨d₃, a₃, L₃, k₃, n₃, heq₃, -, hfr₃, hv₃, hu₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hv₃ hu₃
  have hlo₃ : ∀ a, a < tmp1 → m₃ a = mem a := fun a ha => (hfr₃ a (Or.inl ha)).trans (hlo₂ a ha)
  have hhi₃ : ∀ a, tmp1 + LB ≤ a → m₃ a = mem a := fun a ha =>
    (hfr₃ a (Or.inr ha)).trans ((hfr₂ a (Or.inr ha)).trans (hfr₁ a (Or.inr ha)))
  -- 4. `tmp2 := k2 · le`
  obtain ⟨hvk₃, hUk₃⟩ := hsrc m₃ hlo₃ k2 hk2 hvk
  obtain ⟨hvl₃, hUl₃⟩ := hsrc m₃ hlo₃ le hle hvl
  refine runs_seq_call_le (vs := [tmp2, k2, le, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hvk₃, hvl₃, Or.inl (by omega), Or.inl (by omega), by omega, by omega,
      by omega⟩ ?_
  rintro v₄ m₄ pos₄ ⟨d₄, a₄, b₄, L₄, heq₄, -, hfr₄, hv₄, hu₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hv₄ hu₄
  have hlo₄ : ∀ a, a < tmp1 → m₄ a = mem a := fun a ha =>
    (hfr₄ a (Or.inl (by omega))).trans (hlo₃ a ha)
  have ht1₄ : ∀ i < LB, m₄ (tmp1 + i) = m₃ (tmp1 + i) := fun i hi => hfr₄ _ (Or.inl (by omega))
  have hv1₄ : Valid m₄ tmp1 h LB := fun i hi => by rw [ht1₄ i hi]; exact hv₃ i hi
  -- 5. `tmp1 += tmp2`
  refine runs_seq_call_le (vs := [tmp1, tmp2, LB, 1, 0]) hAcc
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, _, rfl, by omega, hk1, hv1₄, hv₄, Or.inr ht12, by omega, by omega⟩ ?_
  rintro v₅ m₅ pos₅ ⟨d₅, a₅, L₅, k₅, n₅, heq₅, -, hfr₅, hv₅, hu₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr₅ hv₅ hu₅
  have hlo₅ : ∀ a, a < tmp1 → m₅ a = mem a := fun a ha => (hfr₅ a (Or.inl ha)).trans (hlo₄ a ha)
  -- 6. `tmp2 := th · le`
  obtain ⟨hvt₅, hUt₅⟩ := hsrc m₅ hlo₅ th hth hvt
  obtain ⟨hvl₅, hUl₅⟩ := hsrc m₅ hlo₅ le hle hvl
  refine runs_seq_call_le (vs := [tmp2, th, le, LB]) hMul
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> omega)
    ⟨_, _, _, _, rfl, hvt₅, hvl₅, Or.inl (by omega), Or.inl (by omega), by omega, by omega,
      by omega⟩ ?_
  rintro v₆ m₆ pos₆ ⟨d₆, a₆, b₆, L₆, heq₆, -, hfr₆, hv₆, hu₆⟩
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₆
  try dsimp only at hfr₆ hv₆ hu₆
  have hlo₆ : ∀ a, a < tmp1 → m₆ a = mem a := fun a ha =>
    (hfr₆ a (Or.inl (by omega))).trans (hlo₅ a ha)
  have ht1₆ : ∀ i < LB, m₆ (tmp1 + i) = m₅ (tmp1 + i) := fun i hi => hfr₆ _ (Or.inl (by omega))
  have hv1₆ : Valid m₆ tmp1 h LB := fun i hi => by rw [ht1₆ i hi]; exact hv₅ i hi
  have hU1₆ : unsignedVal m₆ tmp1 h LB = unsignedVal m₅ tmp1 h LB := unsignedVal_congr ht1₆
  -- the two values
  set c := capacity h LB with hc
  set A := unsignedVal mem acc h LB with hA
  set E := unsignedVal mem le h LB with hE
  set N := wstrNumVal c A (unsignedVal mem k2 h LB) E with hN
  set Y := unsignedVal mem th h LB * E % c with hY
  have hNv : unsignedVal m₆ tmp1 h LB = N := by
    rw [hU1₆, hu₅, unsignedVal_congr ht1₄, hu₄, hu₃, hu₂, hu₁, hUa₂, hUa₁, hUk₃, hUl₃]
    simp only [accTerm, if_neg (show (0 : ℕ) ≠ 1 by omega), one_mul, Nat.zero_mod, hN,
      wstrNumVal, zero_add]
  have hYv : unsignedVal m₆ tmp2 h LB = Y := by
    rw [hu₆, hUt₅, hUl₅]
  have hhi₆ : ∀ a, tmp2 + LB ≤ a → m₆ a = mem a := fun a ha =>
    (hfr₆ a (Or.inr ha)).trans ((hfr₅ a (Or.inr (by omega))).trans
      ((hfr₄ a (Or.inr ha)).trans (hhi₃ a (by omega))))
  -- 7. compare
  refine runs_seq_call_le (vs := [tmp1, tmp2, LB]) hLess
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, by omega, by omega, hv1₆, hv₆⟩ ?_
  rintro v₇ m₇ pos₇ ⟨hm₇, hv₇⟩
  have hm₇' : m₆ = m₇ := hm₇.symm
  subst hm₇'
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hv₇
  rw [hNv, hYv] at hv₇
  have hsrcL : ∀ x, lo ≤ x → x + LB ≤ tmp1 → Valid mem x h LB → ∀ (m : ℕ → ℕ),
      (∀ a, lo ≤ a → a < tmp1 → m a = mem a) → Valid m x h Lw ∧
        unsignedVal m x h Lw = unsignedVal mem x h Lw := by
    intro x hx1 hx2 hv m hm
    have hag : ∀ i < Lw, m (x + i) = mem (x + i) := fun i hi => hm _ (by omega) (by omega)
    exact ⟨fun i hi => by rw [hag i hi]; exact hv i (by omega), unsignedVal_congr hag⟩
  refine runs_cond_le (v := v₇) (by eval_expr) ?_ ?_
  · -- `N < Y`: copy the low limbs
    intro hne
    have hlt : N < Y := by by_contra hc; simp [hc] at hv₇; exact hne hv₇
    have hv1L : Valid m₆ tmp1 h Lw := fun i hi => hv1₆ i (by omega)
    refine runs_seq_call_le (vs := [numOut, tmp1, Lw, Lw]) hExt
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> omega)
      ⟨_, _, _, _, rfl, le_refl _, hv1L, Or.inr (by omega), by omega, by omega⟩ ?_
    rintro v₈ m₈ pos₈ ⟨d₈, a₈, La₈, L₈, heq₈, -, hfr₈, hv₈, hu₈⟩
    simp only [List.cons.injEq, and_true] at heq₈
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₈
    try dsimp only at hfr₈ hv₈ hu₈
    obtain ⟨hvl₈, hUl₈⟩ := hsrcL le hlo2 hle hvl m₈ (fun a ha1 ha2 =>
      (hfr₈ a (Or.inr (by omega))).trans (hlo₆ a ha2))
    refine runs_seq_call_le (vs := [denOut, le, Lw, Lw]) hExt
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> omega)
      ⟨_, _, _, _, rfl, le_refl _, hvl₈, Or.inr (by omega), by omega, by omega⟩ ?_
    rintro v₉ m₉ pos₉ ⟨d₉, a₉, La₉, L₉, heq₉, -, hfr₉, hv₉, hu₉⟩
    simp only [List.cons.injEq, and_true] at heq₉
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₉
    try dsimp only at hfr₉ hv₉ hu₉
    have hn₉ : ∀ i < Lw, m₉ (numOut + i) = m₈ (numOut + i) := fun i hi => hfr₉ _ (by omega)
    refine runs_ret_le (v := 0) (by eval_expr) ⟨numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB,
      Lw, rfl, fun a ha1 ha2 ha3 => ?_,
      fun i hi => by dsimp only; rw [hn₉ i hi]; exact hv₈ i hi, hv₉,
      fun _ => ⟨rfl, ?_, ?_⟩, fun hc => absurd hlt hc⟩ ?_
    · dsimp only; rw [hfr₉ a ha2, hfr₈ a ha1]
      rcases ha3 with ha3 | ha3
      · exact hlo₆ a ha3
      · exact hhi₆ a ha3
    · rw [unsignedVal_congr hn₉, hu₈, ← unsignedVal_mod_prefix hv1₆ hLw, hNv]
    · rw [hu₉, hUl₈, ← unsignedVal_mod_prefix hvl hLw]
    · simp only [wstrEdgeContract, uExtContract, uLoadWordContract, uAccContract, uMulContract,
        unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
        Expr.size_const, Expr.size_reg, Expr.size_bin]
      simp only [hargs, List.getD_cons_zero, List.getD_cons_succ, Nat.mul_assoc]
      omega
  · -- `N ≥ Y`: write `1` and `1`
    intro heq0
    have hge : ¬ N < Y := by intro hc; simp [hc] at hv₇; omega
    refine runs_seq_call_le (vs := [numOut, Lw, 1]) hLoad
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨_, _, _, rfl, by omega⟩ ?_
    rintro v₈ m₈ pos₈ ⟨d₈, L₈, x₈, heq₈, -, hfr₈, hv₈, hu₈⟩
    simp only [List.cons.injEq, and_true] at heq₈
    obtain ⟨rfl, rfl, rfl⟩ := heq₈
    try dsimp only at hfr₈ hv₈ hu₈
    refine runs_seq_call_le (vs := [denOut, Lw, 1]) hLoad
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_nil _ _))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨_, _, _, rfl, by omega⟩ ?_
    rintro v₉ m₉ pos₉ ⟨d₉, L₉, x₉, heq₉, -, hfr₉, hv₉, hu₉⟩
    simp only [List.cons.injEq, and_true] at heq₉
    obtain ⟨rfl, rfl, rfl⟩ := heq₉
    try dsimp only at hfr₉ hv₉ hu₉
    have hn₉ : ∀ i < Lw, m₉ (numOut + i) = m₈ (numOut + i) := fun i hi => hfr₉ _ (by omega)
    refine runs_ret_le (v := 1) (by eval_expr) ⟨numOut, denOut, acc, le, th, k2, tmp1, tmp2, LB,
      Lw, rfl, fun a ha1 ha2 ha3 => ?_,
      fun i hi => by dsimp only; rw [hn₉ i hi]; exact hv₈ i hi, hv₉,
      fun hc => absurd hc hge, fun _ => ⟨rfl, ?_, hu₉⟩⟩ ?_
    · dsimp only; rw [hfr₉ a ha2, hfr₈ a ha1]
      rcases ha3 with ha3 | ha3
      · exact hlo₆ a ha3
      · exact hhi₆ a ha3
    · rw [unsignedVal_congr hn₉, hu₈]
    · simp only [wstrEdgeContract, uExtContract, uLoadWordContract, uAccContract, uMulContract,
        unsignedLessContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
        Expr.size_const, Expr.size_reg, Expr.size_bin]
      simp only [hargs, List.getD_cons_zero, List.getD_cons_succ, Nat.mul_assoc]
      omega

end MinCostFlow.LSF.Program
