module

public import MinCostFlow.LowStretch.ProgClusterSetupPq
public import MinCostFlow.LowStretch.ProgClusterSetupT2
public import MinCostFlow.LowStretch.ProgClusterSetupPg

/-!
# The setup of a cluster: the chain of the calls

This file links the run lemmas of the calls of `setupP`, from the loads to the header of the
queues and `pqClear` (`suChain_runs`). What the setup knows just before the stores of the block is
collected in `SuAt`: the memories after each call, with what each call gives. The stores of the
block and the facts of `setupC` are proved from `SuAt` in later files.

The chain needs a few word bounds from `ClPre.room` (`SuWords`); `ClPre.suWords` proves them.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The word bounds that the calls after `pgP` ask, for the loads `V`, `L` buckets and the
radius `Δ`. -/
structure SuWords (w : ℕ) (V : SuV) (L Δ : ℕ) : Prop where
  hΔ : Δ < 2 ^ w
  hEXP : V.EXP < 2 ^ w
  hbw : Δ / 8 / L < 2 ^ w
  hp2 : 2 ^ 2 ^ L < 2 ^ w
  hsq : 2 ^ L + 3 < 2 ^ w
  hINF : V.INF * (V.J + 5) + (V.J + 5) < 2 ^ w

/-- **What the setup knows before the stores of the block**, at the state `st`: the memories
`M` to `M4` of `SuMem`, `M5` after `pgP`, `N1` to `N4` after the tables `NXT`, `ORD`, `AS` and
`EXP`, the largest exponent `Es`, and `P1` to `P3` after `P2`, `SQ` and `pqClear`. -/
structure SuAt (w : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ)
    (mem : ℕ → ℕ) (st : State) where
  M : ℕ → ℕ
  M2 : ℕ → ℕ
  M3 : ℕ → ℕ
  M4 : ℕ → ℕ
  hM : SuMem w T G P c R GB RB h mem M M2 M3 M4
  M5 : ℕ → ℕ
  vpg : ℕ
  pg : (pgPC w).post (suPGA (suVOf GB RB h mem) P.L hM.nA).args M4 vpg M5
  N1 : ℕ → ℕ
  N2 : ℕ → ℕ
  N3 : ℕ → ℕ
  N4 : ℕ → ℕ
  Es : ℕ
  t1 : ∀ i < (suVOf GB RB h mem).s, N1 (((suVOf GB RB h mem).N P.L).z 18 19 0 6 + i) =
    M5 (((suVOf GB RB h mem).N P.L).Z + i)
  t1f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 18 19 0 6 ∨
    ((suVOf GB RB h mem).N P.L).z 18 19 0 6 + (suVOf GB RB h mem).s ≤ a) → N1 a = M5 a
  t2 : ∀ i < 2 * hM.nA + (suVOf GB RB h mem).s,
    N2 (((suVOf GB RB h mem).N P.L).z 18 20 0 7 + i) =
      N1 (((suVOf GB RB h mem).N P.L).z 10 14 0 5 + i)
  t2f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 18 20 0 7 ∨
    ((suVOf GB RB h mem).N P.L).z 18 20 0 7 + (2 * hM.nA + (suVOf GB RB h mem).s) ≤ a) →
      N2 a = N1 a
  t3 : ∀ i < 2 * hM.nA, N3 (((suVOf GB RB h mem).N P.L).z 20 21 0 7 + i) = i / 2
  t3f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 20 21 0 7 ∨
    ((suVOf GB RB h mem).N P.L).z 20 21 0 7 + 2 * hM.nA ≤ a) → N3 a = N2 a
  t4 : ∀ i < hM.nA, N4 (((suVOf GB RB h mem).N P.L).z 22 21 0 7 + i) =
    N3 ((suVOf GB RB h mem).EXP + N3 (((suVOf GB RB h mem).N P.L).z 0 8 0 2 + 2 * i))
  t4f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 22 21 0 7 ∨
    ((suVOf GB RB h mem).N P.L).z 22 21 0 7 + hM.nA ≤ a) → N4 a = N3 a
  es_ge : ∀ j < hM.nA, N4 (((suVOf GB RB h mem).N P.L).z 22 21 0 7 + j) ≤ Es
  es_eq : Es = 0 ∨ ∃ j < hM.nA, Es = N4 (((suVOf GB RB h mem).N P.L).z 22 21 0 7 + j)
  P1 : ℕ → ℕ
  P2 : ℕ → ℕ
  P3 : ℕ → ℕ
  u1 : ∀ i < P.L + 2, P1 (((suVOf GB RB h mem).N P.L).z 23 21 1 9 + i) = 2 ^ 2 ^ (P.L - i)
  u1f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 23 21 1 9 ∨
    ((suVOf GB RB h mem).N P.L).z 23 21 1 9 + (P.L + 2) ≤ a) → P1 a = N4 a
  u2 : ∀ i < P.L + 2, P2 (((suVOf GB RB h mem).N P.L).z 23 21 0 7 + i) =
    c.Δ G / 8 / P.L / (2 ^ (P.L - (i - 1)) + 3)
  u2f : ∀ a, (a < ((suVOf GB RB h mem).N P.L).z 23 21 0 7 ∨
    ((suVOf GB RB h mem).N P.L).z 23 21 0 7 + (P.L + 2) ≤ a) → P2 a = P1 a
  pq : PQRep P3 ((suVOf GB RB h mem).N P.L).D ((suVOf GB RB h mem).J + 5)
    ((suVOf GB RB h mem).N P.L).A2 (suVOf GB RB h mem).INF (fun _ => [])
  pqT0 : ∀ c' < (suVOf GB RB h mem).J + 5,
    P3 (pqT ((suVOf GB RB h mem).N P.L).D ((suVOf GB RB h mem).J + 5) c') = 0
  u3f : ∀ a, ¬ pqOut ((suVOf GB RB h mem).N P.L).D ((suVOf GB RB h mem).J + 5) a →
    a ≠ ((suVOf GB RB h mem).N P.L).D → a ≠ ((suVOf GB RB h mem).N P.L).D + 1 →
    a ≠ ((suVOf GB RB h mem).N P.L).D + 2 → P3 a = P2 a
  d0 : P3 ((suVOf GB RB h mem).N P.L).D = (suVOf GB RB h mem).J + 5
  d1 : P3 (((suVOf GB RB h mem).N P.L).D + 1) = ((suVOf GB RB h mem).N P.L).A2
  d2 : P3 (((suVOf GB RB h mem).N P.L).D + 2) = (suVOf GB RB h mem).INF
  hR : SuR w (suVOf GB RB h mem) P.L (c.Δ G) hM.nA st
  mem_eq : st.mem = P3
  r31 : st.regs 31 = Es
  r32 : st.regs 32 = c.Δ G / 8 / P.L
  r33 : st.regs 33 = ((suVOf GB RB h mem).N P.L).RR

/-- The cost of the setup up to the stores of the block: the loads, `L`, `drawP` (cost `dc`),
`treeP`, `hwFix`, `actP`, `pgP`, the tables, `P2`, `SQ`, the queue header and `pqClear`. -/
def suChainCost (V : SuV) (L nA dc : ℕ) : ℕ :=
  300 + (100 * pL V.n + 200) + (32 + dc) + (300 * V.s + 400) + (250 * V.nH + 300) +
    (80 * V.nS + 100) + (nA * (80 * Nat.clog 2 (V.J + 3) + 1000) + 500 * V.s + 1000) +
    (40 * V.s + 40 * (2 * nA + V.s) + 80 * nA + 40 * nA + 30 * nA + 1000) +
    (100 * (L + 2) + 150 * (V.J + 5) + 1000)

private theorem suChain_aux {a N X W h : ℕ} (h1 : a < N) (h2 : 1000 * N ≤ X) (h3 : h + X < W)
    (h4 : h + 16777216 < W) : a + 1048576 < W := by omega

private theorem suChain_aux2 {h a b c d X W : ℕ} (hh : h + a + b + c + d + X < W) :
    h + X < W := by omega

set_option maxHeartbeats 4000000 in
/-- **The chain of the calls of the setup.** From the start of `setupP` with `args = [GB, RB, h]`,
the loads, `L`, `drawP`, `treeP`, `hwFix`, `actP`, `pgP`, the tables, `P2`, `SQ`, the queue
header and `pqClear` lead to a state with `SuAt`, where the stores of the block begin. -/
theorem suChain_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hLg : MeetsContract w p I.lg (log2C w)) (hDr : MeetsContract w p I.dr (drawC2 w))
    (hTr : MeetsContract w p I.tr (treePC w)) (hHf : MeetsContract w p I.hf (hwFixC w))
    (hAc : MeetsContract w p I.ac (actPC w)) (hPg : MeetsContract w p I.pg (pgPC w))
    (hCp : MeetsContract w p I.cp (suCpC w)) (hHl : MeetsContract w p I.hl (suHalfC w))
    (hEx : MeetsContract w p I.ex (suExpC w)) (hMx : MeetsContract w p I.mx (maxtC w))
    (hP2 : MeetsContract w p I.p2 (suP2C w)) (hSq : MeetsContract w p I.sq (suSqC w))
    (hCl : MeetsContract w p I.cl (pqClearC w))
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    (hW : SuWords w (suVOf GB RB h mem) P.L (c.Δ G)) {pos : ℕ} {Q : Outcome → State → Prop}
    {K : ℕ}
    (hrest : ∀ st (a : SuAt w T G P c R GB RB h mem st), ∃ o st' c',
      Runs w p ω (suStores suBlk (.ret (.const 0))) st o st' c' ∧ Q o st' ∧
        suChainCost (suVOf GB RB h mem) P.L a.hM.nA
          (drawCost (suVOf GB RB h mem).dwE.args mem) + c' ≤ K) :
    ∃ o st' c', Runs w p ω (setupP I) (startState (suVOf GB RB h mem).args mem pos) o st' c' ∧
      Q o st' ∧ c' ≤ K := by
  have hWd := hp.words hX
  have hN := hp.ok.tree.n_lt
  have hVn : (suVOf GB RB h mem).n = G.n := hp.glob.n
  have hLeq : P.L = pL (suVOf GB RB h mem).n := by rw [hp.L_eq, hVn]
  have h20 : 2 ^ 20 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    (lt_of_le_of_lt (Nat.le_add_left _ h) hp.room_h)
  have hw2 : 2 ≤ w := by
    by_contra hc
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine suPro_runs hp.suFacts (fun st1 hR1 hm1 => ?_)
  rw [suB_eq]
  have hn20 : (suVOf GB RB h mem).n + 2 ^ 20 < 2 ^ w := by
    have hq : 1000 * 1 * (G.m + T.N + P.L + 10) ≤
        1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have e20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
    have e24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    have h4 := hp.room_h
    rw [hVn, e20]; rw [e24] at h4
    set X := 1000 * ((GlobL.read mem GB).J + 1) * (G.m + T.N + P.L + 10) with hXd
    have h2 : 1000 * T.N ≤ X := by omega
    have h3 : h + X < 2 ^ w := suChain_aux2 hWd
    exact suChain_aux hN h2 h3 h4
  refine suL_runs hLg hR1 hw2 hn20 (fun st2 hR2 hm2 h28 => ?_)
  refine suDr_runs hDr hp hX hR2 (hm2.trans hm1) (fun M pos2 hF => ?_)
  set V := suVOf GB RB h mem with hV
  have hR3 : V.Regs ⟨M, Function.update st2.regs 23 (c.Δ G), pos2⟩ := hR2.upd (by norm_num) _ _ _
  have h28' : Function.update st2.regs 23 (c.Δ G) 28 = P.L := by
    rw [Function.update_of_ne (by norm_num), h28, hLeq]
  refine suTr_runs hTr hp hX hF hR3 h28' rfl (fun v2 M2 pos3 hT hTs hTf => ?_)
  have hR4 := (hR3.upd (r := 24) (by norm_num) (V.N P.L).Z M pos2).upd (r := 25) (by norm_num) v2
    M2 pos3
  refine suHf_runs hHf hp hX hF hTf hR4 (by simp [Function.update_apply] <;> rfl)
    (by simp only [Function.update_of_ne (show (28 : ℕ) ≠ 25 by norm_num),
      Function.update_of_ne (show (28 : ℕ) ≠ 24 by norm_num), h28']) rfl
    (fun v3 M3 pos4 hH hHfr => ?_)
  have hZ : h + 51 ≤ (V.N P.L).Z := by simp only [SuN.Z, SuN.H, SuV.N, hV, suVOf]; omega
  have hlow := ClPre.low3 hF hZ hTf hHfr
  have hR5 := hR4.upd (r := 25) (by norm_num) v3 M3 pos4
  refine suAc_runs hAc hp hX hlow hR5 (by simp [Function.update_apply] <;> rfl)
    (by simp [Function.update_apply] <;> rfl) (by simp only [Function.update_of_ne
      (show (28 : ℕ) ≠ 25 by norm_num), Function.update_of_ne (show (28 : ℕ) ≠ 24 by norm_num),
      h28']) rfl (fun M4 pos5 hAct hActf => ?_)
  have hM : SuMem w T G P c R GB RB h mem M M2 M3 M4 :=
    ⟨hF, hT, hTs, hTf, hH, hHfr, hAct, hActf⟩
  have hS := hp.hS_lt hX
  have hR6 : SuR w V P.L (c.Δ G) hM.nA ⟨M4, Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update st2.regs 23 (c.Δ G)) 24
        (V.N P.L).Z) 25 v2) 25 v3) 29 (V.QD (c.Δ G))) 30 hM.nA, pos5⟩ :=
    ⟨(hR5.upd (r := 29) (by norm_num) _ M3 pos4).upd (r := 30) (by norm_num) _ M4 pos5,
      by simp [Function.update_apply] <;> rfl, by simp [Function.update_apply] <;> rfl,
      by simp only [Function.update_apply]; simp; exact h28', by simp [Function.update_apply],
      hS, h20, selL_length_le _ _ _ _ _⟩
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h :=
    hp.below
  have bIN := hb ((GlobL.read mem GB).IN, 3 * (GlobL.read mem GB).m) (by simp [recRegs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bIN bPW bEX
  have hlab : (GlobL.read mem GB).LAB + G.n ≤ h := hp.lab_below
  have hloc : (GlobL.read mem GB).LOC + T.N ≤ h := hp.loc_below
  have hroom := hp.room_h
  obtain ⟨E', hE', -, -, -, -, -, -, -, -, hx0s, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  have hlθ : (RecL.read mem RB).lθ < c.θ := hθ ▸ Nat.lt_two_pow_self
  have hθJ : c.θ ≤ 2 ^ (GlobL.read mem GB).J * c.θ := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have hθw : c.θ < 2 ^ w := lt_of_le_of_lt hθJ (lt_of_le_of_lt (by omega) hWd)
  have es : (V.N P.L).s ≤ (V.N P.L).hS := by
    have := (V.N P.L).z_le_hS (a := 0) (b := 1) (c := 0) (k := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    simp only [SuN.z, SuN.Z, SuN.H] at this; omega
  have hpre := hp.pgPre hX hM
  refine suPg_runs hPg hR6 hpre ⟨show (GlobL.read mem GB).IN < 2 ^ w by omega,
    show (GlobL.read mem GB).PW < 2 ^ w by omega, show (GlobL.read mem GB).LAB < 2 ^ w by omega,
    show (GlobL.read mem GB).LOC < 2 ^ w by omega, show (RecL.read mem RB).lθ < 2 ^ w by omega,
    lt_of_lt_of_le hx0s (es.trans hS.le)⟩ (fun v4 M5 hpost st5 hR7 hm5 => ?_)
  have hfr5 : ∀ a, ¬ ((suPGA V P.L hM.nA).TL ≤ a ∧ a ≤ (suPGA V P.L hM.nA).OK +
      (suPGA V P.L hM.nA).s) → M5 a = M4 a := (hpost _ rfl).2.2.2.2.2.2.2.2.2.1
  have eTL : (suPGA V P.L hM.nA).TL = (V.N P.L).z 2 8 0 2 := rfl
  have ez : ∀ a b c k, (V.N P.L).z a b c k =
      (V.N P.L).Z + a * (RecL.read mem RB).nS + b * (RecL.read mem RB).s + c * P.L + k :=
    fun _ _ _ _ => rfl
  have hnA : hM.nA ≤ (RecL.read mem RB).nS := selL_length_le _ _ _ _ _
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hpr : ∀ i < hM.nA, M5 ((V.N P.L).z 0 8 0 2 + 2 * i) < G.m := fun i hi => by
    rw [hfr5 _ (fun h' => by rw [eTL, ez, ez] at h'; omega)]
    exact hpre.fill.pr_lt i hi
  have hexp : ∀ i < hM.nA, V.EXP + st5.mem ((V.N P.L).z 0 8 0 2 + 2 * i) < (V.N P.L).Z :=
    fun i hi => by
      have := hpr i hi
      rw [hm5]; show (GlobL.read mem GB).EXP + _ < _; omega
  have hexw : ∀ i < hM.nA, st5.mem (V.EXP + st5.mem ((V.N P.L).z 0 8 0 2 + 2 * i)) < 2 ^ w :=
    fun i hi => by
      have h1 := hpr i hi
      rw [hm5]
      set q := M5 ((V.N P.L).z 0 8 0 2 + 2 * i)
      show M5 ((GlobL.read mem GB).EXP + q) < 2 ^ w
      rw [hfr5 _ (fun h' => by rw [eTL, ez] at h'; omega), hM.low_h (by omega)]
      have := (hp.pw_words hX q h1).2
      omega
  rw [suTab_eq]
  refine suT1_runs hCp hHl hEx hMx hR7 hW.hΔ hW.hEXP hexp hexw
    (fun N1 N2 N3 N4 Es t1 t1f t2 t2f t3 t3f t4 t4f eg ee st6 hR8 hm6 r31 r32 => ?_)
  refine suT2_runs hP2 hSq hCl hR8 r31 r32 hW.hbw hW.hp2 hW.hsq hW.hINF
    (fun P1 P2 P3 u1 u1f u2 u2f pq pq0 u3f d0 d1 d2 st7 hR9 hm7 r31' r32' r33 => ?_)
  rw [hm5] at t1 t1f
  rw [hm6] at u1f
  obtain ⟨o, st', c', h1, h2, h3⟩ := hrest st7 ⟨M, M2, M3, M4, hM, M5, v4, hpost, N1, N2, N3,
    N4, Es, t1, t1f, t2, t2f, t3, t3f, t4, t4f, eg, ee, P1, P2, P3, u1, u1f, u2, u2f, pq, pq0,
    u3f, d0, d1, d2, hR9, hm7, r31', r32', r33⟩
  refine ⟨o, st', c', h1, h2, ?_⟩
  have e1 : V.s = (RecL.read mem RB).s := rfl
  have e2 : V.nS = (RecL.read mem RB).nS := rfl
  have e3 : V.nH = (RecL.read mem RB).nH := rfl
  unfold suChainCost at h3
  rw [e1, e2, e3] at h3
  linarith

end MinCostFlow.LowStretch
