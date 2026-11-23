module

public import MinCostFlow.LowStretch.ProgClusterSetupTc

/-!
# The setup of a cluster: the first tables

After `pgP`, the setup copies the parents into `NXT` and the order of `pgP` into its own `ORD`,
writes `AS[i] = i / 2` and the exponents `EXP[j] = EXPg[ACT[2 j]]` of the active entries, finds
the largest exponent `Es` with `maxtP`, and computes `bw = Δ / 8 / L`. This file proves the run
of these six steps (`suT1_runs`) from the registers `SuR`, by one call lemma for each.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem lt_all2 {a b x : ℕ} (h1 : a < x) (h2 : b < x) : ∀ v ∈ [a, b], v < x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl) <;> assumption

theorem lt_all3 {a b c x : ℕ} (h1 : a < x) (h2 : b < x) (h3 : c < x) : ∀ v ∈ [a, b, c], v < x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl | rfl | rfl) <;> assumption

theorem lt_all4 {a b c d x : ℕ} (h1 : a < x) (h2 : b < x) (h3 : c < x) (h4 : d < x) :
    ∀ v ∈ [a, b, c, d], v < x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl) <;> assumption

variable {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : SuV} {L Δ nA : ℕ}

/-- The steps of `suTab` up to the assignment of `bw`, followed by `s`. -/
def suT1 (I : SuIdx) (s : Stmt) : Stmt :=
  .seq (.call 25 I.cp [.reg 13, suZ 18 19 0 6, suZ 0 0 0 0])
  (.seq (.call 25 I.cp [suMM, suZ 18 20 0 7, suZ 10 14 0 5])
  (.seq (.call 25 I.hl [mulC 2 30, suZ 20 21 0 7])
  (.seq (.call 25 I.ex [.reg 30, suZ 22 21 0 7, .reg 7, suZ 0 8 0 2])
  (.seq (.call 31 I.mx [.reg 30, suZ 22 21 0 7])
  (.seq (.assign 32 (.bin .div (.bin .div (.reg 23) (.const 8)) (.reg 28))) s)))))

/-- The steps of `suTab` after `bw`. -/
def suT2 (I : SuIdx) : Stmt :=
  .seq (.call 25 I.p2 [.bin .add (.reg 28) (.const 2), suZ 23 21 1 9, .reg 28, .reg 32])
  (.seq (.call 25 I.sq [.bin .add (.reg 28) (.const 2), suZ 23 21 0 7, .reg 28, .reg 32])
  (.seq (.assign 33 suRRE) (suEnd I)))

theorem suTab_eq (I : SuIdx) : suTab I = suT1 I (suT2 I) := rfl

theorem suT1_sizes : cpE.size ≤ 20 ∧ halfE.size ≤ 20 ∧ expE.size ≤ 20 ∧
    argsSize [.reg 13, suZ 18 19 0 6, suZ 0 0 0 0] ≤ 60 ∧
    argsSize [suMM, suZ 18 20 0 7, suZ 10 14 0 5] ≤ 60 ∧
    argsSize [mulC 2 30, suZ 20 21 0 7] ≤ 60 ∧
    argsSize [.reg 30, suZ 22 21 0 7, .reg 7, suZ 0 8 0 2] ≤ 60 ∧
    argsSize [.reg 30, suZ 22 21 0 7] ≤ 60 ∧
    (Expr.bin .div (.bin .div (.reg 23) (.const 8)) (.reg 28)).size ≤ 10 := by decide

/-- **The first tables.** From the registers `SuR` and a memory `M`, the copies, the halves, the
exponents, `Es` and `bw` leave the tables in the memories `M1`, …, `M4`, `Es` in register `31`
and `bw = Δ / 8 / L` in register `32`. The exponents `EXPg` that the entries name lie below `Z`. -/
theorem suT1_runs {I : SuIdx} (hCp : MeetsContract w p I.cp (suCpC w))
    (hHl : MeetsContract w p I.hl (suHalfC w)) (hEx : MeetsContract w p I.ex (suExpC w))
    (hMx : MeetsContract w p I.mx (maxtC w)) {st : State} (hR : SuR w V L Δ nA st)
    (hΔ : Δ < 2 ^ w) (hEG : V.EXP < 2 ^ w)
    (hexp : ∀ i < nA, V.EXP + st.mem ((V.N L).z 0 8 0 2 + 2 * i) < (V.N L).Z)
    (hexw : ∀ i < nA, st.mem (V.EXP + st.mem ((V.N L).z 0 8 0 2 + 2 * i)) < 2 ^ w)
    {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ (M1 M2 M3 M4 : ℕ → ℕ) (Es : ℕ),
      (∀ i < V.s, M1 ((V.N L).z 18 19 0 6 + i) = st.mem ((V.N L).Z + i)) →
      (∀ a, (a < (V.N L).z 18 19 0 6 ∨ (V.N L).z 18 19 0 6 + V.s ≤ a) → M1 a = st.mem a) →
      (∀ i < 2 * nA + V.s, M2 ((V.N L).z 18 20 0 7 + i) = M1 ((V.N L).z 10 14 0 5 + i)) →
      (∀ a, (a < (V.N L).z 18 20 0 7 ∨ (V.N L).z 18 20 0 7 + (2 * nA + V.s) ≤ a) →
        M2 a = M1 a) →
      (∀ i < 2 * nA, M3 ((V.N L).z 20 21 0 7 + i) = i / 2) →
      (∀ a, (a < (V.N L).z 20 21 0 7 ∨ (V.N L).z 20 21 0 7 + 2 * nA ≤ a) → M3 a = M2 a) →
      (∀ i < nA, M4 ((V.N L).z 22 21 0 7 + i) =
        M3 (V.EXP + M3 ((V.N L).z 0 8 0 2 + 2 * i))) →
      (∀ a, (a < (V.N L).z 22 21 0 7 ∨ (V.N L).z 22 21 0 7 + nA ≤ a) → M4 a = M3 a) →
      (∀ j < nA, M4 ((V.N L).z 22 21 0 7 + j) ≤ Es) →
      (Es = 0 ∨ ∃ j < nA, Es = M4 ((V.N L).z 22 21 0 7 + j)) →
      ∀ st' : State, SuR w V L Δ nA st' → st'.mem = M4 → st'.regs 31 = Es →
        st'.regs 32 = Δ / 8 / L →
        ∃ o st'' c', Runs w p ω s st' o st'' c' ∧ Q o st'' ∧
          k + 40 * V.s + 40 * (2 * nA + V.s) + 80 * nA + 40 * nA + 30 * nA + 1000 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (suT1 I s) st o st' c' ∧ Q o st' ∧ k + c' ≤ K := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := suT1_sizes
  set N := V.N L with hN
  have hS := hR.hS
  have w20 := hR.w20
  have hnA := hR.nA_le
  have es : N.hS = N.RR + 6 * N.s + 16 := rfl
  have eRR : N.D ≤ N.RR := by unfold SuN.RR; omega
  have eD : N.D = N.z 23 26 2 16 := rfl
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k := fun _ _ _ _ => rfl
  have vs : N.s = V.s := rfl
  have vn : N.nS = V.nS := rfl
  have hzD := ez 23 26 2 16
  have hz1 := ez 18 19 0 6
  have hz2 := ez 18 20 0 7
  have hz3 := ez 10 14 0 5
  have hz4 := ez 20 21 0 7
  have hz5 := ez 22 21 0 7
  have hz6 := ez 0 8 0 2
  have hz0 := ez 0 0 0 0
  have hbig : N.z 23 26 2 16 < 2 ^ w := hR.z_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  -- the copy of the parents
  have a1 : evalArgs w st [.reg 13, suZ 18 19 0 6, suZ 0 0 0 0] =
      some [V.s, N.z 18 19 0 6, N.z 0 0 0 0] :=
    evalArgs_cons (Expr.eval_reg_of_eq hR.r13) (evalArgs_cons (hR.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_cons (hR.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_nil _ _)))
  refine runs_seq_call_le hCp a1 (lt_all3 (by omega) (by omega) (by omega))
    ⟨⟨_, _, _, rfl, by omega, by omega⟩, by simp,
      (show N.z 18 19 0 6 + V.s + 1 < 2 ^ w by omega)⟩ (fun v1 M1 pos1 hp1 => ?_)
  obtain ⟨c1, f1⟩ := hp1
  simp only [List.getD_cons_zero, List.getD_cons_succ, cpF] at c1 f1
  have hR1 := hR.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v1 M1 pos1
  -- the copy of the order
  refine runs_seq_call_le hCp (vs := [2 * nA + V.s, N.z 18 20 0 7, N.z 10 14 0 5])
    (evalArgs_cons (Expr.eval_add (mulC_eval hR1.r30 (by omega) (by omega))
      (Expr.eval_reg_of_eq hR1.r13) (by omega)) (evalArgs_cons (hR1.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_cons (hR1.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_nil _ _)))) (lt_all3 (by omega) (by omega) (by omega))
    ⟨⟨_, _, _, rfl, by omega, by omega⟩, by simp,
      (show N.z 18 20 0 7 + (2 * nA + V.s) + 1 < 2 ^ w by omega)⟩ (fun v2 M2 pos2 hp2 => ?_)
  obtain ⟨c2, f2⟩ := hp2
  simp only [List.getD_cons_zero, List.getD_cons_succ, cpF] at c2 f2
  have hR2 := hR1.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v2 M2 pos2
  -- the halves
  refine runs_seq_call_le hHl (vs := [2 * nA, N.z 20 21 0 7])
    (evalArgs_cons (mulC_eval hR2.r30 (by omega) (by omega)) (evalArgs_cons (hR2.z_eval
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (evalArgs_nil _ _))) (lt_all2 (by omega) (by omega))
    ⟨⟨by omega, (show 2 * nA < 2 ^ w by omega)⟩, by simp,
      (show N.z 20 21 0 7 + 2 * nA + 1 < 2 ^ w by omega)⟩ (fun v3 M3 pos3 hp3 => ?_)
  obtain ⟨c3, f3⟩ := hp3
  simp only [List.getD_cons_zero, List.getD_cons_succ, halfF] at c3 f3
  have hR3 := hR2.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v3 M3 pos3
  -- the exponents
  have m3 : ∀ i < nA, M3 (N.z 0 8 0 2 + 2 * i) = st.mem (N.z 0 8 0 2 + 2 * i) := fun i hi => by
    rw [f3 _ (Or.inl (by omega)), f2 _ (Or.inl (by omega)), f1 _ (Or.inl (by omega))]
  refine runs_seq_call_le hEx (vs := [nA, N.z 22 21 0 7, V.EXP, N.z 0 8 0 2])
    (evalArgs_cons (Expr.eval_reg_of_eq hR3.r30) (evalArgs_cons (hR3.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_cons (Expr.eval_reg_of_eq
      (hR3.r (i := 7) (by norm_num))) (evalArgs_cons (hR3.z_eval (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) (evalArgs_nil _ _))))) (lt_all4 (by omega) (by omega) (by omega) (by omega))
    ⟨⟨_, _, _, _, rfl, by omega, by omega, by omega, fun i hi => by
      dsimp only; rw [m3 i hi]; exact lt_of_lt_of_le (hexp i hi) (by omega)⟩, by simp,
      (show N.z 22 21 0 7 + nA + 1 < 2 ^ w by omega)⟩ (fun v4 M4 pos4 hp4 => ?_)
  obtain ⟨c4, f4⟩ := hp4
  simp only [List.getD_cons_zero, List.getD_cons_succ, expF] at c4 f4
  have hR4 := hR3.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v4 M4 pos4
  -- the largest exponent
  have m4 : ∀ j < nA, M4 (N.z 22 21 0 7 + j) < 2 ^ w := fun j hj => by
    rw [c4 j hj, m3 j hj, f3 _ (Or.inl (by have := hexp j hj; omega)),
      f2 _ (Or.inl (by have := hexp j hj; omega)), f1 _ (Or.inl (by have := hexp j hj; omega))]
    exact hexw j hj
  refine runs_seq_call_le hMx (vs := [nA, N.z 22 21 0 7])
    (evalArgs_cons (Expr.eval_reg_of_eq hR4.r30) (evalArgs_cons (hR4.z_eval (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (evalArgs_nil _ _))) (lt_all2 (by omega) (by omega))
    ⟨_, _, rfl, by omega, fun j hj => m4 j hj⟩ (fun Es M5 pos5 hp5 => ?_)
  obtain ⟨hM5, c5, d5⟩ := hp5
  rw [hM5]
  simp only [List.getD_cons_zero, List.getD_cons_succ] at c5 d5
  have hR5 := hR4.upd (r := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) Es M4 pos5
  -- `bw`
  set st5 : State := { mem := M4, regs := Function.update (Function.update (Function.update
      (Function.update (Function.update st.regs 25 v1) 25 v2) 25 v3) 25 v4) 31 Es, pos := pos5 }
    with hst5
  have hbw : (Expr.bin .div (.bin .div (.reg 23) (.const 8)) (.reg 28)).eval w st5 =
      some (Δ / 8 / L) :=
    Expr.eval_div (Expr.eval_div (Expr.eval_reg_of_eq hR5.r23) (Expr.eval_const (by omega)) hΔ)
      (Expr.eval_reg_of_eq hR5.r28) (lt_of_le_of_lt (Nat.div_le_self _ _) hΔ)
  refine runs_seq_assign_le hbw ?_
  have hR6 := hR5.upd (r := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Δ / 8 / L) M4 pos5
  have hz00 : N.z 0 0 0 0 = N.Z := by simp [SuN.z]
  obtain ⟨o, st', c', r1, r2, r3⟩ := hrest M1 M2 M3 M4 Es (fun i hi => by rw [c1 i hi, hz00]) f1
    c2 f2 c3 f3 c4 f4 c5 d5 _ hR6 rfl
    (by dsimp only; rw [Function.update_of_ne (by norm_num), hst5]; dsimp only
        rw [Function.update_self])
    (by dsimp only; rw [Function.update_self])
  refine ⟨o, st', c', r1, r2, ?_⟩
  simp only [suCpC, suHalfC, suExpC, maxtC, tabC, List.getD_cons_zero, List.getD_cons_succ]
  have t1 : V.s * (cpE.size + 20) ≤ V.s * 40 := Nat.mul_le_mul_left _ (by omega)
  have t2 : (2 * nA + V.s) * (cpE.size + 20) ≤ (2 * nA + V.s) * 40 :=
    Nat.mul_le_mul_left _ (by omega)
  have t3 : 2 * nA * (halfE.size + 20) ≤ 2 * nA * 40 := Nat.mul_le_mul_left _ (by omega)
  have t4 : nA * (expE.size + 20) ≤ nA * 40 := Nat.mul_le_mul_left _ (by omega)
  omega

end MinCostFlow.LowStretch
