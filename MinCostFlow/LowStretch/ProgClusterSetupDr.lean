module

public import MinCostFlow.LowStretch.ProgClusterSetupL
public import MinCostFlow.LowStretch.ProgChildDelta

/-!
# The setup of a cluster: the precondition of the first run of Dijkstra

The setup calls `drawP` with the words it loaded, the cutoff `D = 32 B n² θ` of the stored
pairs and its arrays from `H = h + 51` on (`SuV.dwE`). This file proves the precondition
`drawPre` of this call from `ClPre` (`ClPre.drawPre`).

The word bounds come from one lemma (`ClPre.words`): `ClPre.room` leaves
`2^(2J + 20) (N + m + 2)² (Mw + 2)²` free words above `h`, and this pays for `INF · J`, for
`2^J θ` (so for `D`) and for `1000 (J + 1) (m + N + L + 10)`, which bounds the heap of the setup
since `|S| ≤ m` and `s ≤ N`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace SuV

variable (V : SuV)

/-- The cutoff `32 B n² θ` of the stored pairs of the first run (`suDc`). -/
def D : ℕ := 32 * V.B * (V.n * V.n) * 2 ^ V.lθ

/-- The arguments of `drawP` in the setup. -/
def dwE : DWE :=
  ⟨V.s, V.nS, V.SA, V.IN, V.PW, V.EXP, V.LAB, V.LOC, V.D, V.lθ, V.x0, V.J, V.INF, V.h + 51⟩

end SuV

/-- The ghost of `drawP` in the setup. -/
def SetG.dwG (g : SetG) : DWG := ⟨g.T, g.G, g.c, g.R, g.G.m, g.G.n, g.T.N⟩

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- `pL n ≤ 2 n + 9`. -/
theorem pL_le_two_mul (n : ℕ) : pL n ≤ 2 * n + 9 := by
  unfold pL pa
  have h1 := Nat.log_le_self 2 (n + 2)
  have h2 := Nat.log_le_self 2 (2 * (Nat.log 2 (n + 2) + 1) + 2)
  omega

/-- There are at most `N` nodes, since they are distinct nodes of the merge tree. -/
theorem Rec.Ok.s_le (h : R.Ok T G P c) : R.nodes.length ≤ T.N := by
  have hsub : R.nodes.toFinset ⊆ Finset.range T.N := fun x hx =>
    Finset.mem_range.mpr (h.node_lt x (List.mem_toFinset.mp hx))
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup h.nodup] at this
  simpa using this

/-- There are at most `m` stored pairs, since they are distinct pairs of `G`. -/
theorem Rec.Ok.S_le (h : R.Ok T G P c) : R.S.length ≤ G.m := by
  have hsub : (R.S.map Prod.fst).toFinset ⊆ Finset.range G.m := fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact Finset.mem_range.mpr (h.S_ok e he).1
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup h.S_nodup, List.length_map] at this
  simpa using this

private theorem words_arith {E Z J INF th q : ℕ} (hJ : J + 1 ≤ E) (hZ : 1 ≤ Z)
    (hINF : INF ≤ 4 * Z) (hth : th ≤ Z) (hq : q ≤ 19 * Z) :
    INF * J + J + INF + E * th + 1000 * (J + 1) * q ≤ 20000 * (E * Z) := by
  have h1 : INF * J ≤ 4 * Z * E := Nat.mul_le_mul hINF (by omega)
  have h2 : E * th ≤ E * Z := Nat.mul_le_mul_left _ hth
  have h3 : 1000 * (J + 1) * q ≤ 1000 * E * (19 * Z) := Nat.mul_le_mul (by omega) hq
  have h4 : E ≤ E * Z := Nat.le_mul_of_pos_right _ hZ
  have h5 : Z ≤ E * Z := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : 4 * Z * E = 4 * (E * Z) := by ring
  have e2 : 1000 * E * (19 * Z) = 19000 * (E * Z) := by ring
  omega

/-- **The word bound of the setup.** With `J`, `INF` of the global block, `θ` of the cluster and
`L` of the constants: `h + INF · J + J + INF + 2^J θ + 1000 (J + 1) (m + N + L + 10) < 2^w`. -/
theorem ClPre.words (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    h + (GlobL.read mem GB).INF * (GlobL.read mem GB).J + (GlobL.read mem GB).J +
      (GlobL.read mem GB).INF + 2 ^ (GlobL.read mem GB).J * c.θ +
      1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) < 2 ^ w := by
  obtain ⟨Mw, hM, hINF, hroom⟩ := hp.room_sq
  set J := (GlobL.read mem GB).J
  set INF := (GlobL.read mem GB).INF
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hp.ok.inv.sub
    simpa using this
  have hΔ : c.Δ G ≤ G.n * Mw :=
    (Cl.Δ_le_card_mul hp.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hθΔ : c.θ ≤ c.Δ G := by
    have hB : 1 ≤ P.B := hp.ok.hB
    rcases hp.ok.inv.big with h | h
    · omega
    · have : 1 * 1 * c.θ ≤ P.B * c.X.card * c.θ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hB (by omega))
      omega
  have hN := hp.ok.tree.n_lt
  have hL : P.L ≤ 2 * G.n + 9 := hp.L_eq ▸ pL_le_two_mul G.n
  set X0 := T.N + G.m + 2
  set Y0 := Mw + 2
  have hnM : G.n * Mw + 4 ≤ X0 * Y0 := by
    have : (G.n + 2) * (Mw + 2) ≤ X0 * Y0 := Nat.mul_le_mul (by omega) le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    omega
  have hXY : X0 ≤ X0 * Y0 := Nat.le_mul_of_pos_right _ (by omega)
  have hq : G.m + T.N + P.L + 10 ≤ 19 * (X0 * Y0) := by omega
  have hJE : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
  have hI4 : INF ≤ 4 * (X0 * Y0) := by
    have : INF ≤ 4 * (G.n * Mw) + 4 := by rw [← mul_assoc]; exact hINF
    omega
  have ha := words_arith (q := G.m + T.N + P.L + 10) hJE (by omega) hI4
    (show c.θ ≤ X0 * Y0 by omega) hq
  have hK : 20000 * (2 ^ J * (X0 * Y0)) < 2 ^ (2 * J + 20) * X0 ^ 2 * Y0 ^ 2 := by
    have e : 2 ^ (2 * J + 20) * X0 ^ 2 * Y0 ^ 2 = 2 ^ 20 * (2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2 := by
      rw [show 2 * J + 20 = 20 + (J + J) by omega, pow_add, pow_add]; ring
    rw [e]
    have hE : 1 ≤ 2 ^ J := Nat.one_le_two_pow
    have hZ : 1 ≤ X0 * Y0 := by omega
    have h1 : 2 ^ J * (X0 * Y0) ≤ (2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hE) (Nat.le_mul_of_pos_right _ hZ)
    have h2 : 0 < 2 ^ J * (X0 * Y0) := Nat.mul_pos hE hZ
    have e2 : 2 ^ 20 * (2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2 =
        2 ^ 20 * ((2 ^ J * 2 ^ J) * (X0 * Y0) ^ 2) := by
      ring
    rw [e2]
    omega
  have h0 := Nat.zero_le ((J + 2) * recCost w A T G P c R)
  omega

/-- The cutoff of the first run is at least the radius and its classes fit below `J`:
`Δ ≤ 32 B n² θ` (`Inv.small`) and `4 · 32 B n² θ < 2^J θ` (`GlobL.Ok.hJ`). -/
theorem ClPre.D_facts (hp : ClPre w A T G P c R GB RB h mem) :
    c.Δ G ≤ (suVOf GB RB h mem).D ∧
      4 * (suVOf GB RB h mem).D < 2 ^ ((GlobL.read mem GB).J + (RecL.read mem RB).lθ) ∧
      (suVOf GB RB h mem).D < 2 ^ (GlobL.read mem GB).J * c.θ := by
  have hs := hp.ok.inv.small
  have hJ : 128 * P.B * G.n ^ 2 < 2 ^ (GlobL.read mem GB).J := hp.glob.hJ
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  have h1 := hp.ok.inv.one_le
  have hD : (suVOf GB RB h mem).D = 32 * P.B * G.n ^ 2 * c.θ := by
    simp only [SuV.D, suVOf, hθ, sq]
    rw [show (GlobL.read mem GB).n = G.n from hp.glob.n, show (GlobL.read mem GB).B = P.B from
      hp.glob.B]
  have h2 : 128 * P.B * G.n ^ 2 * c.θ < 2 ^ (GlobL.read mem GB).J * c.θ :=
    Nat.mul_lt_mul_of_pos_right hJ (by omega)
  have e : 4 * (32 * P.B * G.n ^ 2 * c.θ) = 128 * P.B * G.n ^ 2 * c.θ := by ring
  rw [hD, pow_add, ← hθ]
  omega

/-- **The precondition of `drawP`** in the setup. -/
theorem ClPre.drawPre (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    drawPre w ⟨T, G, c, R, G.m, G.n, T.N⟩ (suVOf GB RB h mem).dwE.args mem := by
  have hW := hp.words hX
  obtain ⟨hDΔ, hD4, hDJ⟩ := hp.D_facts
  set E := GlobL.read mem GB with hE
  set L := RecL.read mem RB with hLd
  have hA : Rec.Mem T G c R (L.af E) mem := hp.recAt.arcs
  have hpr : ∀ j < R.S.length, mem (L.SA + 2 * j) = (R.S.getD j (0, 0)).1 := hA.pr
  have hfl : ∀ j < R.S.length, mem (L.SA + 2 * j + 1) = (R.S.getD j (0, 0)).2 := hA.fl
  have hends : ∀ p < G.m, mem (E.IN + 3 * p) = G.pu p ∧ mem (E.IN + 3 * p + 1) = G.pv p :=
    hA.ends
  have hpwm : ∀ p < G.m, mem (E.PW + p) = G.pω p := hA.pw
  have hexm : ∀ p < G.m, G.pω p = 2 ^ mem (E.EXP + p) := hA.ex
  have hlocm : ∀ v ∈ c.X, mem (E.LOC + mem (E.LAB + v)) = R.sv T c v := hA.loc
  have hOK : R.OkW T G c := hp.ok.toW
  have hG : E.Ok T G P mem := hp.glob
  have hm : E.m = G.m := hG.m
  have hb : ∀ r ∈ recRegs GB RB E L, r.1 + r.2 ≤ h := hp.below
  have bSA := hb (L.SA, 2 * L.nS) (by simp [recRegs, RecL.regs])
  have bIN := hb (E.IN, 3 * E.m) (by simp [recRegs])
  have bPW := hb (E.PW, E.m) (by simp [recRegs])
  have bEX := hb (E.EXP, E.m) (by simp [recRegs])
  dsimp only at bSA bIN bPW bEX
  have hlab : E.LAB + G.n ≤ h := hp.lab_below
  have hloc : E.LOC + T.N ≤ h := hp.loc_below
  have hnS : L.nS = R.S.length := hA.nS
  have hsL : L.s = R.nodes.length := hA.s
  have hSm := hp.ok.S_le
  have hsN := hp.ok.s_le
  have hJ1 : 1 ≤ E.J := by
    have hJ : 128 * P.B * G.n ^ 2 < 2 ^ E.J := hG.hJ
    have hB : 1 ≤ P.B := hp.ok.hB
    have hn : 1 ≤ G.n := hp.ok.n_pos hX
    rcases Nat.eq_zero_or_pos E.J with h0 | h0
    · rw [h0] at hJ
      have : 1 * 1 ≤ P.B * G.n ^ 2 := Nat.mul_le_mul hB (Nat.one_le_pow _ _ (by omega))
      simp at hJ
      omega
    · exact h0
  obtain ⟨Mw, hM, -, -⟩ := hp.room_sq
  have hpw : ∀ p < G.m, G.pω p < 2 ^ w := fun p hp' => by
    have h1 := hG.hINF p hp'
    have hn : 1 ≤ G.n := by have := (hG.hG p hp').1; omega
    have : G.pω p ≤ 2 * G.n * G.pω p := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hx0 : c.x0 ∈ c.X := hp.ok.inv.good.conn.1
  have hsv0 : (suVOf GB RB h mem).x0 = R.sv T c c.x0 := by
    show mem (E.LOC + mem (E.LAB + L.x0)) = _
    rw [hp.recAt.x0]; exact hlocm c.x0 hx0
  have hJN : E.J * L.nS ≤ E.J * G.m := Nat.mul_le_mul_left _ (by omega)
  have hJs : E.J * L.s ≤ E.J * T.N := Nat.mul_le_mul_left _ (by omega)
  have hend : h + 51 + 16 * L.nS + 8 * L.s + 9 +
      (3 + 4 * E.J + 2 * E.J * (2 * L.nS + L.s + 1)) + 2 + 51 ≤
      h + 1000 * (E.J + 1) * (G.m + T.N + P.L + 10) := by
    have e2 : 1000 * (E.J + 1) * (G.m + T.N + P.L + 10) =
      1000 * (E.J * G.m) + 1000 * (E.J * T.N) + 1000 * (E.J * P.L) + 10000 * E.J +
        1000 * G.m + 1000 * T.N + 1000 * P.L + 10000 := by ring
    have e3 : 2 * E.J * (2 * L.nS + L.s + 1) = 4 * (E.J * L.nS) + 2 * (E.J * L.s) + 2 * E.J := by
      ring
    omega
  have hsv := hOK.sv_lt hx0
  have hθ1 := hp.ok.inv.one_le
  have hEθ : 2 ^ E.J ≤ 2 ^ E.J * c.θ := Nat.le_mul_of_pos_right _ (by omega)
  have hea : ∀ j < L.nS, mem (E.LOC + mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j)))) < L.s ∧
      mem (E.LOC + mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j) + 1))) < L.s ∧
      mem (L.SA + 2 * j) < G.m ∧ mem (L.SA + 2 * j + 1) ≤ 1 := fun j hj => by
    have hj' : j < R.S.length := hnS ▸ hj
    obtain ⟨hpm, hu, hv, -, hf1, -⟩ := hp.ok.entry hj'
    rw [hpr j hj', hfl j hj', (hends _ hpm).1, (hends _ hpm).2, hlocm _ hu, hlocm _ hv, hsL]
    exact ⟨hOK.sv_lt hu, hOK.sv_lt hv, hpm, hf1⟩
  refine ⟨(suVOf GB RB h mem).dwE, rfl,
    ⟨hA.nS, hA.s, hA.pr, hA.fl, hA.ends, hA.pw, hA.ex, hA.loc, hA.th⟩, hOK,
    ⟨⟨fun j hj => (hea j hj).2.2.1, fun j hj => (hea j hj).2.2.2, fun p hp' => ?_,
      fun j hj => ?_, fun j hj => ?_, fun p hp' => ?_, fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun j hj => (hea j hj).1, fun j hj => (hea j hj).2.1, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hDΔ, ?_, hD4, hJ1, hsv0, ?_, ?_, ?_, ?_, ?_⟩
  · show mem (E.IN + 3 * p) < G.n ∧ mem (E.IN + 3 * p + 1) < G.n
    rw [(hends p hp').1, (hends p hp').2]; exact hG.hG p hp'
  · have hj' : j < R.S.length := hnS ▸ hj
    obtain ⟨hpm, -⟩ := hp.ok.entry hj'
    show mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j))) < T.N ∧
      mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j) + 1)) < T.N
    rw [hpr j hj', (hends _ hpm).1, (hends _ hpm).2]
    exact ⟨hp.lab_lt _ (hG.hG _ hpm).1, hp.lab_lt _ (hG.hG _ hpm).2⟩
  · have hj' : j < R.S.length := hnS ▸ hj
    obtain ⟨hpm, -⟩ := hp.ok.entry hj'
    show mem (E.LOC + mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j)))) < 2 ^ w ∧
      mem (E.LOC + mem (E.LAB + mem (E.IN + 3 * mem (L.SA + 2 * j) + 1))) < 2 ^ w
    rw [hpr j hj', (hends _ hpm).1, (hends _ hpm).2]
    exact ⟨hp.loc_w _ (hp.lab_lt _ (hG.hG _ hpm).1), hp.loc_w _ (hp.lab_lt _ (hG.hG _ hpm).2)⟩
  · show mem (E.PW + p) < 2 ^ w
    rw [hpwm p hp']; exact hpw p hp'
  · have e := hexm p hp'
    have h3 : mem (E.EXP + p) < 2 ^ mem (E.EXP + p) := Nat.lt_two_pow_self
    have := hpw p hp'
    have h4 : 2 ≤ 2 ^ w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0; omega
      · calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h0
    show mem (E.EXP + p) + 2 < 2 ^ w
    have h5 := hG.hINF p hp'
    have hn : 1 ≤ G.n := by have := (hG.hG p hp').1; omega
    have h6 : 2 * 1 * G.pω p ≤ 2 * G.n * G.pω p :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn)
    have h7 : 1 ≤ 2 ^ mem (E.EXP + p) := Nat.one_le_two_pow
    omega
  all_goals (try simp only [SuV.dwE, DWE.ap, AP.toAF, suVOf, drawEnd, DWE.Rr, DWE.Dq, DWE.Aq]
             try rw [← hE]
             try rw [← hLd])
  all_goals try omega
  · have hΔ2 : 2 ≤ c.Δ G := by
      have hB : 1 ≤ P.B := hp.ok.hB
      rcases hp.ok.inv.big with h0 | h0
      · omega
      · have : 1 * 2 * 1 ≤ P.B * c.X.card * c.θ :=
          Nat.mul_le_mul (Nat.mul_le_mul hB hX) hθ1
        omega
    have hm1 : 0 < G.m := by
      rcases Nat.eq_zero_or_pos G.m with h0 | h0
      · have := Cl.Δ_le_card_mul hp.ok.inv.good.conn (Mw := 0) (fun p hp' => by omega)
        simp at this; omega
      · exact h0
    have hI0 := hG.hINF 0 hm1
    have hcard : c.X.card ≤ G.n := by
      have := Finset.card_le_card hp.ok.inv.sub
      simpa using this
    exact Cl.Δ_lt_INF_of_pos hp.ok.inv.good.conn hcard (by omega) hG.hINF
  · have hx0L : L.x0 = c.x0 := hp.recAt.x0
    rw [hx0L, hlocm c.x0 hx0, hsL]; exact hsv
  · exact fun a ha => hp.zero a (by omega)
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hDJ.le _) (by omega)

/-- The arguments of the call of `drawP` in `suB`. -/
def suDrArgs : List Expr :=
  [.reg 13, .reg 14, .reg 15, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, suDc, .reg 16, .reg 17,
    .reg 11, .reg 12, .reg 21]

theorem suDrArgs_size : argsSize suDrArgs ≤ 30 := by decide

/-- **The call of `drawP`.** From registers that hold the loads, the call of `drawP` returns the
radius in register `23` and leaves a memory `M` with `Rec.First` (the arc graph and the state of
the first run). Its cost is `drawCost` of its arguments, plus `30` for the arguments. -/
theorem suDr_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hDr : MeetsContract w p I.dr (drawC2 w)) (hp : ClPre w A T G P c R GB RB h mem)
    (hX : 2 ≤ c.X.card) {st : State} (hR : (suVOf GB RB h mem).Regs st) (hm : st.mem = mem)
    {s : Stmt} {Q : Outcome → State → Prop} {k K : ℕ}
    (hrest : ∀ M pos, Rec.First w T G c R (suVOf GB RB h mem).dwE mem M →
      ∃ o st' c', Runs w p ω s ⟨M, Function.update st.regs 23 (c.Δ G), pos⟩ o st' c' ∧
        Q o st' ∧ k + 32 + drawCost (suVOf GB RB h mem).dwE.args mem + c' ≤ K) :
    ∃ o st' c', Runs w p ω (.seq (.call 23 I.dr suDrArgs) s) st o st' c' ∧ Q o st' ∧
      k + c' ≤ K := by
  set V := suVOf GB RB h mem with hV
  have hW := hp.words hX
  obtain ⟨-, -, hDJ⟩ := hp.D_facts
  have hpre := hp.drawPre hX
  obtain ⟨E', hE', hM, hok, hAP, hD, hI, -, -, hx0, hx0s, -, -, -, -⟩ := hpre
  obtain rfl := DWE.eq_of_args hE'
  have r : ∀ i < 23, st.regs i = V.vals.getD i 0 := hR
  have hB : 1 ≤ V.B := by
    show 1 ≤ (GlobL.read mem GB).B
    rw [hp.glob.B]; exact hp.ok.hB
  have hn : 1 ≤ V.n := by
    show 1 ≤ (GlobL.read mem GB).n
    rw [hp.glob.n]; exact hp.ok.n_pos hX
  have hDw : V.D < 2 ^ w := by
    have : V.D < 2 ^ V.J * c.θ := hDJ
    have e : V.J = (GlobL.read mem GB).J := rfl
    rw [e] at this
    omega
  have hθ : c.θ = 2 ^ V.lθ := hp.recAt.arcs.th
  have hl1 : 1 ≤ 2 ^ V.lθ := Nat.one_le_two_pow
  have hnn : 1 ≤ V.n * V.n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hD1 : 32 * V.B * (V.n * V.n) ≤ V.D := Nat.le_mul_of_pos_right _ hl1
  have hD2 : 32 * V.B ≤ 32 * V.B * (V.n * V.n) := Nat.le_mul_of_pos_right _ hnn
  have hD3 : V.n * V.n ≤ 32 * V.B * (V.n * V.n) := Nat.le_mul_of_pos_left _ (by omega)
  have hDc : suDc.eval w st = some V.D := by
    have e3 : st.regs 3 = V.n := r 3 (by norm_num)
    have e10 : st.regs 10 = V.B := r 10 (by norm_num)
    have e16 : st.regs 16 = V.lθ := r 16 (by norm_num)
    have hsh : (32 * V.B * (V.n * V.n)) <<< V.lθ = V.D := by
      rw [Nat.shiftLeft_eq]; rfl
    rw [← hsh]
    refine Expr.eval_shiftLeft (Expr.eval_mul (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq e10) (by omega)) (Expr.eval_mul (Expr.eval_reg_of_eq e3)
      (Expr.eval_reg_of_eq e3) (by omega)) (by omega)) (Expr.eval_reg_of_eq e16) (by omega)
  have hargs : evalArgs w st suDrArgs = some V.dwE.args := by
    have g : ∀ i (hi : i < 23), (Expr.reg i).eval w st = some (V.vals.getD i 0) :=
      fun i hi => Expr.eval_reg_of_eq (r i hi)
    simp only [suDrArgs]
    refine evalArgs_cons (g 13 (by norm_num)) (evalArgs_cons (g 14 (by norm_num))
      (evalArgs_cons (g 15 (by norm_num)) (evalArgs_cons (g 5 (by norm_num))
      (evalArgs_cons (g 6 (by norm_num)) (evalArgs_cons (g 7 (by norm_num))
      (evalArgs_cons (g 8 (by norm_num)) (evalArgs_cons (g 9 (by norm_num))
      (evalArgs_cons hDc (evalArgs_cons (g 16 (by norm_num)) (evalArgs_cons (g 17 (by norm_num))
      (evalArgs_cons (g 11 (by norm_num)) (evalArgs_cons (g 12 (by norm_num))
      (evalArgs_cons (g 21 (by norm_num)) (evalArgs_nil _ _))))))))))))))
  have hq : G.m + T.N + P.L + 10 + (GlobL.read mem GB).J ≤
      1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) := by
    have e : 1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) =
      1000 * ((GlobL.read mem GB).J * (G.m + T.N + P.L + 10)) + 1000 * (G.m + T.N + P.L + 10) := by
      ring
    have : (GlobL.read mem GB).J ≤ (GlobL.read mem GB).J * (G.m + T.N + P.L + 10) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hθJ : c.θ ≤ 2 ^ (GlobL.read mem GB).J * c.θ :=
    Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have hlθ : V.lθ < c.θ := by rw [hθ]; exact Nat.lt_two_pow_self
  have hs : V.s ≤ T.N := by
    have e : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
    show (RecL.read mem RB).s ≤ T.N
    rw [e]; exact hp.ok.s_le
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS) (by simp [recRegs, RecL.regs])
  have bIN := hb ((GlobL.read mem GB).IN, 3 * (GlobL.read mem GB).m) (by simp [recRegs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bSA bIN bPW bEX
  have hlab : (GlobL.read mem GB).LAB + G.n ≤ h := hp.lab_below
  have hloc : (GlobL.read mem GB).LOC + T.N ≤ h := hp.loc_below
  have hx0s' : V.x0 < V.s := hx0s
  have v1 : V.nS = (RecL.read mem RB).nS := rfl
  have v2 : V.SA = (RecL.read mem RB).SA := rfl
  have v3 : V.IN = (GlobL.read mem GB).IN := rfl
  have v4 : V.PW = (GlobL.read mem GB).PW := rfl
  have v5 : V.EXP = (GlobL.read mem GB).EXP := rfl
  have v6 : V.LAB = (GlobL.read mem GB).LAB := rfl
  have v7 : V.LOC = (GlobL.read mem GB).LOC := rfl
  have v8 : V.J = (GlobL.read mem GB).J := rfl
  have v9 : V.INF = (GlobL.read mem GB).INF := rfl
  have v10 : V.h = h := rfl
  have hroom := hp.room_h
  have hwords : ∀ v ∈ V.dwE.args, v < 2 ^ w := by
    intro v hv
    simp only [DWE.args, SuV.dwE, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    all_goals first | exact hDw | omega
  subst hm
  refine runs_seq_call_le hDr hargs hwords ⟨_, hp.drawPre hX⟩ (fun v mem' pos' hpost => ?_)
  obtain ⟨hv, hall⟩ := hpost _ (hp.drawPre hX)
  subst hv
  obtain ⟨o, st', c', h1, h2, h3⟩ := hrest mem' pos' ⟨hM, hok, hD, hI, hx0, hall _ rfl⟩
  refine ⟨o, st', c', h1, h2, ?_⟩
  have := suDrArgs_size
  have e : (drawC2 w).cost V.dwE.args st.mem = drawCost V.dwE.args st.mem := rfl
  omega

end MinCostFlow.LowStretch
