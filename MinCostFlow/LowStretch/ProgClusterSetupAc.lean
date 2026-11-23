module

public import MinCostFlow.LowStretch.ProgClusterSetupHf

/-!
# The setup of a cluster: the call of `actP`

After `hwFix`, the setup computes the bound `QD = (512 B n² Δ) · 2^lθ = Q Δ θ` of the active
pairs into register `29` and calls `actP`, which copies the stored entries with `ω² ≤ QD` to
`ACT = Z + 8 s + 2` and returns their number. This file proves the run of these two steps
(`suAc_runs`). The stored entries, the weights and the arrays that `actP` reads lie below
`h + 51`, where the memory is still the memory at the start of the setup (`ClPre.low3`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The bound `Q Δ θ` of the active pairs, from the loads and `Δ`. -/
def SuV.QD (V : SuV) (Δ : ℕ) : ℕ := 512 * V.B * (V.n * V.n) * Δ * 2 ^ V.lθ

/-- The arguments of the call of `actP`. -/
def suAcArgs : List Expr := [.reg 14, .reg 15, .reg 6, suZ 0 8 0 2, .reg 29]

theorem suAcArgs_size : argsSize suAcArgs ≤ 30 := by decide

theorem suQD_size : suQD.size ≤ 30 := by decide

/-- `Q Δ θ` in terms of the ghost. -/
theorem ClPre.QD_eq (hp : ClPre w A T G P c R GB RB h mem) :
    (suVOf GB RB h mem).QD (c.Δ G) = 512 * P.B * G.n ^ 2 * c.Δ G * c.θ := by
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  simp only [SuV.QD, suVOf, hθ, sq]
  rw [show (GlobL.read mem GB).n = G.n from hp.glob.n, show (GlobL.read mem GB).B = P.B from
    hp.glob.B]

/-- **The active entries.** From registers that hold the loads, `Δ`, `Z` and `L`, and a memory
`M3` that agrees with `mem` below `h + 51`, the assignment of `QD` and the call of `actP` write
the selected entries at `ACT = Z + 8 s + 2` and put their number in register `30`. -/
theorem suAc_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hAc : MeetsContract w p I.ac (actPC w)) (hp : ClPre w A T G P c R GB RB h mem)
    (hX : 2 ≤ c.X.card) {M3 : ℕ → ℕ} (hlow : ∀ a < h + 51, M3 a = mem a)
    {st : State} (hR : (suVOf GB RB h mem).Regs st) (h23 : st.regs 23 = c.Δ G)
    (h24 : st.regs 24 = ((suVOf GB RB h mem).N P.L).Z) (h28 : st.regs 28 = P.L)
    (hm : st.mem = M3) {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ M4 pos, ActDone M3 M4 (RecL.read mem RB).SA
        (((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2)
        (selL M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW ((suVOf GB RB h mem).QD (c.Δ G))
          (RecL.read mem RB).nS) →
      (∀ a, ¬ (((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2 ≤ a ∧
        a < ((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2 +
          2 * (RecL.read mem RB).nS) → M4 a = M3 a) →
      ∃ o st' c', Runs w p ω s ⟨M4, Function.update (Function.update st.regs 29
          ((suVOf GB RB h mem).QD (c.Δ G))) 30
          (selL M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW ((suVOf GB RB h mem).QD (c.Δ G))
            (RecL.read mem RB).nS).length, pos⟩ o st' c' ∧
        Q o st' ∧ k + 80 * (RecL.read mem RB).nS + 100 + c' ≤ K) :
    ∃ o st' c', Runs w p ω (.seq (.assign 29 suQD) (.seq (.call 30 I.ac suAcArgs) s)) st o st' c' ∧
      Q o st' ∧ k + c' ≤ K := by
  obtain ⟨hQ, hpw2⟩ := hp.words2 hX
  rw [← hp.QD_eq] at hQ
  set V := suVOf GB RB h mem with hV
  set N := V.N P.L with hN
  have hS := hp.hS_lt hX
  rw [← hV, ← hN] at hS
  have h20 : 2 ^ 20 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ h) hp.room_h)
  have r : ∀ i < 23, st.regs i = V.vals.getD i 0 := hR
  have hB : 1 ≤ V.B := by
    show 1 ≤ (GlobL.read mem GB).B
    rw [hp.glob.B]; exact hp.ok.hB
  have hn : 1 ≤ V.n := by
    show 1 ≤ (GlobL.read mem GB).n
    rw [hp.glob.n]; exact hp.ok.n_pos hX
  have hΔ1 : 1 ≤ c.Δ G := by
    have hB' : 1 ≤ P.B := hp.ok.hB
    rcases hp.ok.inv.big with h0 | h0
    · omega
    · have : 1 * 2 * 1 ≤ P.B * c.X.card * c.θ :=
        Nat.mul_le_mul (Nat.mul_le_mul hB' hX) hp.ok.inv.one_le
      omega
  have hl1 : 1 ≤ 2 ^ V.lθ := Nat.one_le_two_pow
  have hnn : 1 ≤ V.n * V.n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hQ1 : 512 * V.B * (V.n * V.n) * c.Δ G ≤ V.QD (c.Δ G) := Nat.le_mul_of_pos_right _ hl1
  have hQ2 : 512 * V.B * (V.n * V.n) ≤ 512 * V.B * (V.n * V.n) * c.Δ G :=
    Nat.le_mul_of_pos_right _ hΔ1
  have hQ3 : 512 * V.B ≤ 512 * V.B * (V.n * V.n) := Nat.le_mul_of_pos_right _ hnn
  have hQ4 : V.n * V.n ≤ 512 * V.B * (V.n * V.n) := Nat.le_mul_of_pos_left _ (by omega)
  have hQE : suQD.eval w st = some (V.QD (c.Δ G)) := by
    have e3 : st.regs 3 = V.n := r 3 (by norm_num)
    have e10 : st.regs 10 = V.B := r 10 (by norm_num)
    have e16 : st.regs 16 = V.lθ := r 16 (by norm_num)
    have hsh : (512 * V.B * (V.n * V.n) * c.Δ G) <<< V.lθ = V.QD (c.Δ G) := by
      rw [Nat.shiftLeft_eq]; rfl
    rw [← hsh]
    exact Expr.eval_shiftLeft (Expr.eval_mul (Expr.eval_mul (Expr.eval_mul (Expr.eval_const
      (by omega)) (Expr.eval_reg_of_eq e10) (by omega)) (Expr.eval_mul (Expr.eval_reg_of_eq e3)
      (Expr.eval_reg_of_eq e3) (by omega)) (by omega)) (Expr.eval_reg_of_eq h23) (by omega))
      (Expr.eval_reg_of_eq e16) (by omega)
  refine runs_seq_assign_le hQE ?_
  set st1 : State := { st with regs := Function.update st.regs 29 (V.QD (c.Δ G)) } with hst1
  have q : ∀ i < 23, st1.regs i = V.vals.getD i 0 := fun i hi => by
    rw [hst1]; dsimp only; rw [Function.update_of_ne (by omega)]; exact r i hi
  have q24 : st1.regs 24 = N.Z := by
    rw [hst1]; dsimp only; rw [Function.update_of_ne (by omega)]; exact h24
  have q28 : st1.regs 28 = N.L := by
    rw [hst1]; dsimp only; rw [Function.update_of_ne (by omega)]; exact h28
  have q29 : st1.regs 29 = V.QD (c.Δ G) := by rw [hst1]; dsimp only; rw [Function.update_self]
  have eS : N.hS = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) + 23 * N.nS + 26 * N.s + 2 * N.L + 16 + 3 + 4 * (N.J + 5) +
      2 * (N.J + 5) * (2 * N.nS + 2 * N.s) + 6 * N.s + 16 := by
    simp only [SuN.hS, SuN.r, SuN.RR, SuN.D, SuN.z, SuN.Z, SuN.H, SuN.A2, SuN.Jq] <;> ring
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have v1 : N.nS = (RecL.read mem RB).nS := rfl
  have v2 : N.s = (RecL.read mem RB).s := rfl
  have v3 : N.h = h := rfl
  have hargs : evalArgs w st1 suAcArgs = some [(RecL.read mem RB).nS, (RecL.read mem RB).SA,
      (GlobL.read mem GB).PW, N.Z + 8 * (RecL.read mem RB).s + 2, V.QD (c.Δ G)] := by
    simp only [suAcArgs]
    exact evalArgs_cons (Expr.eval_reg_of_eq (q 14 (by norm_num)))
      (evalArgs_cons (Expr.eval_reg_of_eq (q 15 (by norm_num)))
      (evalArgs_cons (Expr.eval_reg_of_eq (q 6 (by norm_num)))
      (evalArgs_cons (suZ_eval q24 (q 14 (by norm_num))
        (show st1.regs 13 = (RecL.read mem RB).s from q 13 (by norm_num)) q28 h20
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by ring) (by omega))
      (evalArgs_cons (Expr.eval_reg_of_eq q29) (evalArgs_nil _ _)))))
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS) (by simp [recRegs, RecL.regs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bSA bPW
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hA := hp.recAt.arcs
  have hnS : (RecL.read mem RB).nS = R.S.length := hA.nS
  have hent : ∀ j < (RecL.read mem RB).nS, gpr M3 (RecL.read mem RB).SA j < G.m ∧
      gfl M3 (RecL.read mem RB).SA j ≤ 1 ∧
      M3 ((GlobL.read mem GB).PW + gpr M3 (RecL.read mem RB).SA j) =
        G.pω (gpr M3 (RecL.read mem RB).SA j) := fun j hj => by
    have hj' : j < R.S.length := hnS ▸ hj
    obtain ⟨hpm, -, -, -, hf1, -⟩ := hp.ok.entry hj'
    have e1 : gpr M3 (RecL.read mem RB).SA j = (R.S.getD j (0, 0)).1 := by
      unfold gpr; rw [hlow _ (by omega)]; exact hA.pr j hj'
    have e2 : gfl M3 (RecL.read mem RB).SA j = (R.S.getD j (0, 0)).2 := by
      unfold gfl; rw [hlow _ (by omega)]; exact hA.fl j hj'
    rw [e1, e2, hlow _ (by omega)]
    exact ⟨hpm, hf1, hA.pw _ hpm⟩
  have hm1 : st1.mem = M3 := hm
  have hroom := hp.room_h
  have hwords : ∀ v ∈ [(RecL.read mem RB).nS, (RecL.read mem RB).SA, (GlobL.read mem GB).PW,
      N.Z + 8 * (RecL.read mem RB).s + 2, V.QD (c.Δ G)], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpre : (actPC w).pre [(RecL.read mem RB).nS, (RecL.read mem RB).SA, (GlobL.read mem GB).PW,
      N.Z + 8 * (RecL.read mem RB).s + 2, V.QD (c.Δ G)] st1.mem := by
    rw [hm1]
    refine ⟨_, _, _, _, _, rfl, by omega, by omega, fun j hj => ?_⟩
    obtain ⟨a1, a2, a3⟩ := hent j hj
    rw [a3]
    exact ⟨by omega, hpw2 _ a1, by omega, by omega⟩
  refine runs_seq_call_le hAc hargs hwords hpre (fun v mem' pos' hpost => ?_)
  obtain ⟨h1, h2, h3⟩ := hpost _ _ _ _ _ rfl
  rw [hm1] at h1 h2 h3
  subst h1
  obtain ⟨o, st', c', a1, a2, a3⟩ := hrest mem' pos' h2 h3
  refine ⟨o, st', c', a1, a2, ?_⟩
  have := suAcArgs_size
  have := suQD_size
  have e : (actPC w).cost [(RecL.read mem RB).nS, (RecL.read mem RB).SA, (GlobL.read mem GB).PW,
      N.Z + 8 * (RecL.read mem RB).s + 2, V.QD (c.Δ G)] st1.mem =
      80 * (RecL.read mem RB).nS + 30 := rfl
  omega

end MinCostFlow.LowStretch
