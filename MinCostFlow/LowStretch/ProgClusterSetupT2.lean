module

public import MinCostFlow.LowStretch.ProgClusterSetupSt

/-!
# The setup of a cluster: the tables of the tests and the queues

After `bw`, the setup writes the tables `P2` and `SQ` of the tests, computes the address `RR`
after the queues of the petal searches, writes the header `Jq, A2, INF` of these queues and
empties them with `pqClear`. This file proves the run of these steps (`suT2_runs`), up to the
stores of the block, from the registers `SuR`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : SuV} {L Δ nA : ℕ}

theorem SuR.setMem {st : State} (h : SuR w V L Δ nA st) (M : ℕ → ℕ) :
    SuR w V L Δ nA { st with mem := M } :=
  ⟨h.regs, h.r23, h.r24, h.r28, h.r30, h.hS, h.w20, h.nA_le⟩

theorem suT2_sizes : p2E.size ≤ 30 ∧ sqE.size ≤ 30 ∧
    argsSize [.bin .add (.reg 28) (.const 2), suZ 23 21 1 9, .reg 28, .reg 32] ≤ 50 ∧
    argsSize [.bin .add (.reg 28) (.const 2), suZ 23 21 0 7, .reg 28, .reg 32] ≤ 50 ∧
    suRRE.size ≤ 60 ∧ argsSize [suD, suJq, .reg 12] ≤ 40 ∧ suD.size ≤ 30 ∧ suJq.size ≤ 5 ∧
    suA.size ≤ 10 ∧ (Expr.bin .add suD (.const 1)).size ≤ 32 ∧
    (Expr.bin .add suD (.const 2)).size ≤ 32 := by decide

/-- The value of `RR`: `D + 3 + 4 Jq + 2 Jq A2`. -/
theorem SuN.RR_eq' (N : SuN) :
    N.RR = N.D + (3 + 4 * (N.J + 5)) + 2 * (N.J + 5) * (2 * N.nS + 2 * N.s) := by
  simp only [SuN.RR, SuN.Jq, SuN.A2]; ring

set_option maxRecDepth 20000 in
/-- **The tables of the tests and the queues.** From the registers `SuR` with `Es` in register
`31` and `bw` in register `32`, the tables `P2`, `SQ`, the address `RR`, the header of the queues
and `pqClear` leave the tables in `M1`, `M2`, empty queues at `D` in `M3`, and `RR` in register
`33`. -/
theorem suT2_runs {I : SuIdx} (hP2 : MeetsContract w p I.p2 (suP2C w))
    (hSq : MeetsContract w p I.sq (suSqC w)) (hCl : MeetsContract w p I.cl (pqClearC w))
    {st : State} (hR : SuR w V L Δ nA st) {Es bw : ℕ} (r31 : st.regs 31 = Es)
    (r32 : st.regs 32 = bw) (hbw : bw < 2 ^ w) (hp2 : 2 ^ 2 ^ L < 2 ^ w)
    (hsq : 2 ^ L + 3 < 2 ^ w) (hINF : V.INF * (V.J + 5) + (V.J + 5) < 2 ^ w)
    {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ (M1 M2 M3 : ℕ → ℕ),
      (∀ i < L + 2, M1 ((V.N L).z 23 21 1 9 + i) = 2 ^ 2 ^ (L - i)) →
      (∀ a, (a < (V.N L).z 23 21 1 9 ∨ (V.N L).z 23 21 1 9 + (L + 2) ≤ a) → M1 a = st.mem a) →
      (∀ i < L + 2, M2 ((V.N L).z 23 21 0 7 + i) = bw / (2 ^ (L - (i - 1)) + 3)) →
      (∀ a, (a < (V.N L).z 23 21 0 7 ∨ (V.N L).z 23 21 0 7 + (L + 2) ≤ a) → M2 a = M1 a) →
      PQRep M3 (V.N L).D (V.J + 5) (V.N L).A2 V.INF (fun _ => []) →
      (∀ c < V.J + 5, M3 (pqT (V.N L).D (V.J + 5) c) = 0) →
      (∀ a, ¬ pqOut (V.N L).D (V.J + 5) a → a ≠ (V.N L).D → a ≠ (V.N L).D + 1 →
        a ≠ (V.N L).D + 2 → M3 a = M2 a) →
      M3 (V.N L).D = V.J + 5 → M3 ((V.N L).D + 1) = (V.N L).A2 → M3 ((V.N L).D + 2) = V.INF →
      ∀ st' : State, SuR w V L Δ nA st' → st'.mem = M3 → st'.regs 31 = Es → st'.regs 32 = bw →
        st'.regs 33 = (V.N L).RR →
        ∃ o st'' c', Runs w p ω (suStores suBlk (.ret (.const 0))) st' o st'' c' ∧ Q o st'' ∧
          k + 100 * (L + 2) + 150 * (V.J + 5) + 1000 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (suT2 I) st o st' c' ∧ Q o st' ∧ k + c' ≤ K := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩ := suT2_sizes
  set N := V.N L with hN
  have w20 := hR.w20
  have hS := hR.hS
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k := fun _ _ _ _ => rfl
  have hbig : N.z 23 26 2 16 < 2 ^ w := hR.z_lt (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hz1 := ez 23 21 1 9
  have hz2 := ez 23 21 0 7
  have hzD := ez 23 26 2 16
  have eL : N.L = L := rfl
  have eD : N.D = N.z 23 26 2 16 := rfl
  have es : N.hS = N.RR + 6 * N.s + 16 := rfl
  have eRR := N.RR_eq'
  have hS' : N.hS < 2 ^ w := hR.hS
  have hRRw : N.RR < 2 ^ w := lt_of_le_of_lt (show N.RR ≤ N.hS by rw [es]; omega) hS'
  have hDw : N.D + 3 < 2 ^ w := by omega
  have hAw : 2 * N.nS + 2 * N.s < 2 ^ w := by
    have : 2 * N.nS + 2 * N.s ≤ N.z 23 26 2 16 := by rw [hzD]; omega
    omega
  have vJ : N.J = V.J := rfl
  -- `P2`
  have hL2 : L + 2 < 2 ^ w := by omega
  refine runs_seq_call_le hP2 (vs := [L + 2, N.z 23 21 1 9, L, bw])
    (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hR.r28) (Expr.eval_const (by omega)) hL2)
      (evalArgs_cons (hR.z_eval (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (Expr.eval_reg_of_eq hR.r28) (evalArgs_cons (Expr.eval_reg_of_eq r32)
      (evalArgs_nil _ _)))))
    (lt_all4 (by omega) (by omega) (by omega) hbw)
    ⟨hp2, by simp, (show N.z 23 21 1 9 + (L + 2) + 1 < 2 ^ w by omega)⟩
    (fun v1 M1 pos1 hp1 => ?_)
  obtain ⟨c1, f1⟩ := hp1
  have hR1 := hR.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v1 M1 pos1
  have q32 : Function.update st.regs 25 v1 32 = bw := by
    rw [Function.update_of_ne (by norm_num)]; exact r32
  -- `SQ`
  refine runs_seq_call_le hSq (vs := [L + 2, N.z 23 21 0 7, L, bw])
    (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hR1.r28) (Expr.eval_const (by omega)) hL2)
      (evalArgs_cons (hR1.z_eval (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (Expr.eval_reg_of_eq hR1.r28) (evalArgs_cons (Expr.eval_reg_of_eq q32)
      (evalArgs_nil _ _)))))
    (lt_all4 (by omega) (by omega) (by omega) hbw)
    ⟨⟨le_rfl, hsq, hbw⟩, by simp, (show N.z 23 21 0 7 + (L + 2) + 1 < 2 ^ w by omega)⟩
    (fun v2 M2 pos2 hp2' => ?_)
  obtain ⟨c2, f2⟩ := hp2'
  have hR2 := hR1.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v2 M2 pos2
  -- `RR`
  set st2 : State :=
    { mem := M2, regs := Function.update (Function.update st.regs 25 v1) 25 v2, pos := pos2 }
    with hst2
  have hJq : suJq.eval w st2 = some (N.J + 5) :=
    Expr.eval_add (Expr.eval_reg_of_eq hR2.r11) (Expr.eval_const (by omega)) (by omega)
  have hA : suA.eval w st2 = some (2 * N.nS + 2 * N.s) :=
    Expr.eval_add (mulC_eval hR2.r14 (by omega) (by omega)) (mulC_eval hR2.r13 (by omega)
      (by omega)) (by omega)
  have hDv : suD.eval w st2 = some N.D :=
    hR2.z_eval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hRRv : suRRE.eval w st2 = some N.RR := by
    rw [eRR]
    exact Expr.eval_add (Expr.eval_add hDv (Expr.eval_add (Expr.eval_const (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) hJq (by omega)) (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_mul (Expr.eval_const (by omega)) hJq (by omega)) hA
        (by omega)) (by omega)
  refine runs_seq_assign_le hRRv ?_
  have hR3 := hR2.upd (r := 33) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) N.RR M2 pos2
  -- the header
  set st3 : State := { st2 with regs := Function.update st2.regs 33 N.RR } with hst3
  have hR3' : SuR w V L Δ nA st3 := hR3
  have hD3 : suD.eval w st3 = some N.D :=
    hR3'.z_eval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hJ3 : suJq.eval w st3 = some (N.J + 5) :=
    Expr.eval_add (Expr.eval_reg_of_eq hR3'.r11) (Expr.eval_const (by omega)) (by omega)
  refine runs_seq_store_le hD3 hJ3 ?_
  set st4 : State := { st3 with mem := Function.update st3.mem N.D (N.J + 5) } with hst4
  have hR4 : SuR w V L Δ nA st4 := hR3'.setMem _
  refine runs_seq_store_le (x := N.D + 1) (Expr.eval_add (hR4.z_eval (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_add (mulC_eval (a := 2) hR4.r14 (by omega) (show 2 * N.nS < 2 ^ w by omega))
      (mulC_eval (a := 2) hR4.r13 (by omega) (show 2 * N.s < 2 ^ w by omega))
      (show 2 * N.nS + 2 * N.s < 2 ^ w by omega)) ?_
  set st5 : State :=
    { st4 with mem := Function.update st4.mem (N.D + 1) (2 * N.nS + 2 * N.s) } with hst5
  have hR5 : SuR w V L Δ nA st5 := hR4.setMem _
  have r12 : st5.regs 12 = V.INF := hR5.r (i := 12) (by norm_num)
  refine runs_seq_store_le (x := N.D + 2) (Expr.eval_add (hR5.z_eval (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq r12) ?_
  set st6 : State := { st5 with mem := Function.update st5.mem (N.D + 2) V.INF } with hst6
  have hR6 : SuR w V L Δ nA st6 := hR5.setMem _
  have hINFw : V.INF < 2 ^ w := by
    have : V.INF ≤ V.INF * (V.J + 5) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  -- `pqClear`
  have m6 : ∀ a, a ≠ N.D → a ≠ N.D + 1 → a ≠ N.D + 2 → st6.mem a = M2 a := fun a h1 h2 h3 => by
    simp only [hst6, hst5, hst4, hst3, hst2]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have m6D : st6.mem N.D = N.J + 5 := by
    simp only [hst6, hst5, hst4, hst3, hst2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have m6D1 : st6.mem (N.D + 1) = N.A2 := by
    simp only [hst6, hst5]
    rw [Function.update_of_ne (by omega), Function.update_self]; rfl
  have m6D2 : st6.mem (N.D + 2) = V.INF := by
    simp only [hst6]; rw [Function.update_self]
  have hfit : N.D + pqSize (N.J + 5) N.A2 < 2 ^ w := by
    have e := N.RR_eq; simp only [SuN.Jq] at e; omega
  refine runs_seq_call_le hCl (vs := [N.D, N.J + 5, V.INF])
    (evalArgs_cons (hR6.z_eval (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hR6.r11) (Expr.eval_const (by omega))
        (by omega)) (evalArgs_cons (Expr.eval_reg_of_eq (hR6.r (i := 12) (by norm_num)))
      (evalArgs_nil _ _))))
    (lt_all3 (by omega) (by omega) hINFw)
    ⟨_, _, _, _, rfl, m6D, m6D1, m6D2, by omega, hfit, hINF⟩ (fun v7 M3 pos7 hp7 => ?_)
  obtain ⟨c3, d3, f3⟩ := hp7 _ _ _ _ rfl m6D1
  have hR7 := hR6.upd (r := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) v7 M3 pos7
  have nD0 : ¬ pqOut N.D (N.J + 5) N.D := fun h => by unfold pqOut at h; omega
  have nD1 : ¬ pqOut N.D (N.J + 5) (N.D + 1) := fun h => by unfold pqOut at h; omega
  have nD2 : ¬ pqOut N.D (N.J + 5) (N.D + 2) := fun h => by unfold pqOut at h; omega
  obtain ⟨o, st', c', r1, r2, r3⟩ := hrest M1 M2 M3 c1 f1 c2 f2 c3 d3
    (fun a ha h1 h2 h3 => by rw [f3 a ha, m6 a h1 h2 h3])
    (by rw [f3 _ nD0, m6D]; rfl)
    (by rw [f3 _ nD1, m6D1])
    (by rw [f3 _ nD2, m6D2]) _ hR7 rfl
    (by dsimp only; rw [Function.update_of_ne (by norm_num)]
        simp only [hst6, hst5, hst4, hst3, hst2]
        rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
          Function.update_of_ne (by norm_num)]; exact r31)
    (by dsimp only; rw [Function.update_of_ne (by norm_num)]
        simp only [hst6, hst5, hst4, hst3, hst2]
        rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
          Function.update_of_ne (by norm_num)]; exact r32)
    (by dsimp only; rw [Function.update_of_ne (by norm_num)]
        simp only [hst6, hst5, hst4, hst3]
        rw [Function.update_self])
  refine ⟨o, st', c', r1, r2, ?_⟩
  dsimp only [suP2C, suSqC, pqClearC, tabC, List.getD_cons_zero, List.getD_cons_succ] at r3 ⊢
  have t1 : (L + 2) * (p2E.size + 20) ≤ (L + 2) * 50 := Nat.mul_le_mul_left _ (by omega)
  have t2 : (L + 2) * (sqE.size + 20) ≤ (L + 2) * 50 := Nat.mul_le_mul_left _ (by omega)
  have g1 : [L + 2, N.z 23 21 1 9, L, bw].getD 0 0 = L + 2 := rfl
  have g2 : [L + 2, N.z 23 21 0 7, L, bw].getD 0 0 = L + 2 := rfl
  have g3 : [N.D, N.J + 5, V.INF].getD 1 0 = V.J + 5 := rfl
  have g4 : (Expr.reg 12).size = 1 := rfl
  rw [g1, g2, g3, g4]
  clear * - r3 t1 t2 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11
  generalize p2E.size = q1 at *
  generalize sqE.size = q2 at *
  generalize suRRE.size = q3 at *
  generalize suD.size = q4 at *
  generalize suJq.size = q5 at *
  generalize suA.size = q6 at *
  generalize (Expr.bin BinOp.add suD (Expr.const 1)).size = q7 at *
  generalize (Expr.bin BinOp.add suD (Expr.const 2)).size = q8 at *
  generalize argsSize [suD, suJq, Expr.reg 12] = q9 at *
  generalize argsSize [Expr.bin BinOp.add (Expr.reg 28) (Expr.const 2), suZ 23 21 1 9,
    Expr.reg 28, Expr.reg 32] = q10 at *
  generalize argsSize [Expr.bin BinOp.add (Expr.reg 28) (Expr.const 2), suZ 23 21 0 7,
    Expr.reg 28, Expr.reg 32] = q11 at *
  omega

end MinCostFlow.LowStretch
