module

public import MinCostFlow.LSF.Program.CongScatterBase

/-!
# The four block updates of one scatter step

After the scratch block holds `q t`, one step of `congScatterProc` adds it into the blocks of
the two endpoints `u` and `v` and subtracts it twice from the block of their lowest common
ancestor `l`. `congScatter_tail` runs these four calls: the array state changes by `q t` times
the coefficient of `scatterWeight`, and only register `16` changes.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow.Num

@[expose] public section

set_option maxHeartbeats 800000 in
theorem congScatter_tail {w h : ℕ} {p : Program} {ω : ℕ → Bool} {bAdd bSub : ℕ}
    (hAdd : MeetsContract w p bAdd (addToContract w h))
    (hSub : MeetsContract w p bSub (subFromContract w h))
    {st : State} {mem₀ : ℕ → ℕ} {dPtr n K tmpPtr qv u v l k T : ℕ} {f : ℕ → ℤ}
    {Q : Outcome → State → Prop}
    (hh : 0 < h) (hw2 : 2 * h + 2 ≤ w) (hdt : dPtr + n * K ≤ tmpPtr) (htw : tmpPtr + K < 2 ^ w)
    (r5 : st.regs 5 = dPtr) (r6 : st.regs 6 = K) (r7 : st.regs 7 = tmpPtr)
    (r13 : st.regs 13 = u) (r14 : st.regs 14 = v) (r15 : st.regs 15 = l)
    (hun : u < n) (hvn : v < n) (hln : l < n)
    (hM : ScatterMid mem₀ st.mem dPtr n K tmpPtr h qv f)
    (hQ : ∀ st' : State, ScatterMid mem₀ st'.mem dPtr n K tmpPtr h qv (fun y => f y +
        (qv : ℤ) * ((if u = y then 1 else 0) + (if v = y then 1 else 0) -
          2 * (if l = y then 1 else 0))) →
      (∀ j, j ≠ 16 → st'.regs j = st.regs j) → Q .normal st')
    (hk : k + 4 * (65 * K + 27) ≤ T) :
    ∃ o st' c, Runs w p ω
      (.call 16 bAdd [.bin .add (.reg 5) (.bin .mul (.reg 13) (.reg 6)), .reg 7, .reg 6] ;;
       .call 16 bAdd [.bin .add (.reg 5) (.bin .mul (.reg 14) (.reg 6)), .reg 7, .reg 6] ;;
       .call 16 bSub [.bin .add (.reg 5) (.bin .mul (.reg 15) (.reg 6)), .reg 7, .reg 6] ;;
       .call 16 bSub [.bin .add (.reg 5) (.bin .mul (.reg 15) (.reg 6)), .reg 7, .reg 6])
      st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hbu : u * K + K ≤ n * K := by
    have := Nat.mul_le_mul_right K (show u + 1 ≤ n by omega); nlinarith
  have hbv : v * K + K ≤ n * K := by
    have := Nat.mul_le_mul_right K (show v + 1 ≤ n by omega); nlinarith
  have hbl : l * K + K ≤ n * K := by
    have := Nat.mul_le_mul_right K (show l + 1 ≤ n by omega); nlinarith
  have hKw : K < 2 ^ w := by omega
  have hdw : dPtr < 2 ^ w := by omega
  have huw : u * K < 2 ^ w := by omega
  have hvw : v * K < 2 ^ w := by omega
  have hlw : l * K < 2 ^ w := by omega
  refine runs_seq_call_le (vs := [dPtr + u * K, tmpPtr, K]) hAdd
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dPtr + u * K, tmpPtr, K, rfl, hh, hw2, by omega, by omega, Or.inl (by omega),
      (hM.2.2.2 _ hun).1, hM.2.1⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨d₄, s₄, l₄, heq₄, -, hv₄, hu₄, -, hfr₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hv₄ hu₄ hfr₄
  have hM₄ := hM.step (c := (qv : ℤ)) hun hdt hv₄
    (by rw [hu₄, Int.natCast_emod, Int.emod_emod_of_dvd _ (dvd_refl _)]; push_cast
        rw [hM.2.2.1]) hfr₄
  refine runs_seq_call_le (vs := [dPtr + v * K, tmpPtr, K]) hAdd
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dPtr + v * K, tmpPtr, K, rfl, hh, hw2, by omega, by omega, Or.inl (by omega),
      (hM₄.2.2.2 _ hvn).1, hM₄.2.1⟩ ?_
  rintro v₅ mem₅ pos₅ ⟨d₅, s₅, l₅, heq₅, -, hv₅, hu₅, -, hfr₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hv₅ hu₅ hfr₅
  have hM₅ := hM₄.step (c := (qv : ℤ)) hvn hdt hv₅
    (by rw [hu₅, Int.natCast_emod, Int.emod_emod_of_dvd _ (dvd_refl _)]; push_cast
        rw [hM₄.2.2.1]) hfr₅
  refine runs_seq_call_le (vs := [dPtr + l * K, tmpPtr, K]) hSub
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dPtr + l * K, tmpPtr, K, rfl, hh, hw2, by omega, by omega, Or.inl (by omega),
      (hM₅.2.2.2 _ hln).1, hM₅.2.1⟩ ?_
  rintro v₆ mem₆ pos₆ ⟨d₆, s₆, l₆, heq₆, -, hv₆, hi₆, hfr₆⟩
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl⟩ := heq₆
  try dsimp only at hv₆ hi₆ hfr₆
  have hM₆ := hM₅.step (c := -(qv : ℤ)) hln hdt hv₆
    (by rw [unsignedVal_emod_of_intVal_wrap hi₆, hM₅.2.2.1, sub_eq_add_neg]) hfr₆
  refine runs_call_le (vs := [dPtr + l * K, tmpPtr, K]) hSub
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))
    (by
      intro x hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dPtr + l * K, tmpPtr, K, rfl, hh, hw2, by omega, by omega, Or.inl (by omega),
      (hM₆.2.2.2 _ hln).1, hM₆.2.1⟩ ?_
  rintro v₇ mem₇ pos₇ ⟨d₇, s₇, l₇, heq₇, -, hv₇, hi₇, hfr₇⟩
  simp only [List.cons.injEq, and_true] at heq₇
  obtain ⟨rfl, rfl, rfl⟩ := heq₇
  try dsimp only at hv₇ hi₇ hfr₇
  have hM₇ := hM₆.step (c := -(qv : ℤ)) hln hdt hv₇
    (by rw [unsignedVal_emod_of_intVal_wrap hi₇, hM₆.2.2.1, sub_eq_add_neg]) hfr₇
  refine ⟨hQ _ (hM₇.congr_f fun y => scatter_combine (f y) (qv : ℤ) u v l y) fun j hj => ?_, ?_⟩
  · simp only [Function.update_of_ne hj]
  · simp [argsSize, Expr.size, addToContract, subFromContract]
    omega

end

end MinCostFlow.LSF.Program
