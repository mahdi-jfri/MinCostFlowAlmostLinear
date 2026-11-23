module

public import MinCostFlow.LowStretch.ProgBodyNodeLoop
public import MinCostFlow.LowStretch.ProgBody

/-!
# The node part meets its contract

`nodeP_meets` builds the run of the node part forward: the three copies of the arguments, the
call of the setup (`setupCJ`), the loads of its block (`ldR_fwd`), the stamp, the petals
(`PW.nodeLoop`) and the tail (`PW.nodeTail_runs`). The cost before the tail is the setup, the
drop of the potential and the petals; `node_fit` shows that with the child step it fits the
share of the body, and `node_room` that the heap fits.

Four facts are hypotheses here. Two come from the setup and the loop of the petals (`setupCJ`: the
setup has `W.L.J ≤ rootJ n + 5`. `RegPrefix`: the loop keeps the special petal in front.)
`ProgramOwed.lean` proves them. Two are facts about clusters that the cost needs: a cluster with `s`
super-vertices has at least `s - 1` stored pairs (`hsS`), and the numbers of the reset rule of the
raw children are words (`hreset`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

private theorem Kφ_mono {a b : ℕ} (h : a ≤ b) : PW.Kφ a ≤ PW.Kφ b := by
  have := Nat.log_mono_right (b := 2) h
  unfold PW.Kφ; omega

private theorem CJ_mono {a b Lb : ℕ} (h : a ≤ b) : PW.CJ a Lb ≤ PW.CJ b Lb := by
  have := Nat.log_mono_right (b := 2) h
  unfold PW.CJ psPreCost; omega

open Classical in
set_option maxHeartbeats 4000000 in
/-- **The node part meets `MeetsNode`.** -/
theorem nodeP_meets {w : ℕ} {p : Program}
    {f bU bS bF bT bPush bPS bClr bP bC bR bK : ℕ}
    (hp : p.procs[f]? = some (nodeP bU bP bC bR bK))
    (hSetup : MeetsContract w p bU (setupCJ w))
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hbP : p.procs[bP]? = some (petalP bS bF bT))
    (hCp : 1 < 2 ^ w → MeetsContract w p bC (cpC w))
    (hbR : p.procs[bR]? = some (regP bP bC)) (hReg : RegPrefix w p bP bC)
    (hK : MeetsChild w p bK)
    (hsS : ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec), R.Ok T G P c →
      R.nodes.length ≤ R.S.length + 1)
    (hreset : ∀ (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ) (mem : ℕ → ℕ)
      (D : Cl.Dec), ClPre w bodyA T G P c R GB RB h mem → c.DecOk G P D → ∀ k < D.nch,
      Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card) < 2 ^ w) :
    MeetsNode w bodyA p f := by
  intro T G P c R GB RB h mem pos ω hpre hcw hPp h2
  refine ⟨_, hp, ?_⟩
  have hX2 := hpre.ok.two_le h2
  have hL1 : 1 ≤ P.L := hpre.L_eq ▸ pL_pos _
  have hs := hsS T G P c R hpre.ok
  have hS1 : 1 ≤ R.S.length := by omega
  obtain ⟨Mw, hMwb, -, hroomW⟩ := hpre.room
  have hpos : 1 ≤ 2 ^ (2 * (GlobL.read mem GB).J + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 :=
    Nat.mul_pos (Nat.mul_pos (Nat.one_le_two_pow) (pow_pos (by omega) 3)) (pow_pos (by omega) 3)
  have hbelow := hpre.below
  have hRB : RB + 9 ≤ h := by have := hbelow (RB, 9) (by simp [recRegs]); simpa using this
  have hGB : GB + 21 ≤ h := by have := hbelow (GB, 21) (by simp [recRegs]); simpa using this
  set J := (GlobL.read mem GB).J with hJd
  have hJ : J = rootJ G.n := hpre.J_eq
  have hZ : 1 ≤ 2 ^ (2 * J + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 := hpos
  have hZ2 : 2 ^ 20 ≤ 2 ^ (2 * J + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 := by
    have h1 : 2 ^ 20 ≤ 2 ^ (2 * J + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 :=
      Nat.mul_pos (pow_pos (by omega) 3) (pow_pos (by omega) 3)
    calc 2 ^ 20 ≤ 2 ^ (2 * J + 20) * 1 := by omega
      _ ≤ 2 ^ (2 * J + 20) * ((T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have hsu : SuRoom3 w T G h := ⟨Mw, hMwb, by rw [← hJ]; omega⟩
  generalize 2 ^ (2 * J + 20) * (T.N + G.m + 2) ^ 3 * (Mw + 2) ^ 3 = Z at hZ hZ2 hroomW
  have hh60 : h + 60 < 2 ^ w := by
    have : 2 ^ 20 = 1048576 := by norm_num
    omega
  have hCp := hCp (by omega)
  -- the three copies of the arguments
  set st0 := startState [GB, RB, h] mem pos with hst0
  have e1 : (Expr.reg 0).eval w st0 = some GB := Expr.eval_reg_of_eq (by simp [hst0, startState])
  have hA1 := run_assign (p := p) (ω := ω) (r := 60) e1
  set st1 := { st0 with regs := Function.update st0.regs 60 GB } with hst1
  have e2 : (Expr.reg 1).eval w st1 = some RB := Expr.eval_reg_of_eq (by simp [hst1, hst0, startState])
  have hA2 := run_assign (p := p) (ω := ω) (r := 61) e2
  set st1' := { st1 with regs := Function.update st1.regs 61 RB } with hst1'
  have e3 : (Expr.reg 2).eval w st1' = some h :=
    Expr.eval_reg_of_eq (by simp [hst1', hst1, hst0, startState])
  have hA3 := run_assign (p := p) (ω := ω) (r := 62) e3
  set stA := { st1' with regs := Function.update st1'.regs 62 h } with hstA
  have a60 : stA.regs 60 = GB := by simp [hstA, hst1', hst1]
  have a61 : stA.regs 61 = RB := by simp [hstA, hst1']
  have a62 : stA.regs 62 = h := by simp [hstA]
  have amem : stA.mem = mem := rfl
  -- the setup
  have hpreS : setupPre w ⟨T, G, P, c, R⟩ [GB, RB, h] mem :=
    ⟨GB, RB, h, rfl, hpre, hX2, hL1, hcw, hPp, hsu⟩
  obtain ⟨st2, c2, v2, hr2, hpost2, -, hother2, hc2⟩ :=
    runs_call_of_meetsContract (r := 59) (args := [.reg 60, .reg 61, .reg 62]) (st := stA)
      hSetup (by simp [evalArgs, Expr.eval, a60, a61, a62])
      (by intro v hv; simp at hv; omega) ⟨_, hpreS⟩ ω
  have hout : SetupOutJ w ⟨T, G, P, c, R⟩ h mem st2.mem := hpost2 _ hpreS GB RB h rfl
  have hc2' : c2 ≤ setupCostOf ⟨T, G, P, c, R⟩ + 4 := by
    have := setupCost_eq (g := ⟨T, G, P, c, R⟩) hpre
    simp only [argsSize, Expr.size] at hc2
    change c2 ≤ _ + setupCost [GB, RB, h] mem + 1 at hc2
    omega
  obtain ⟨W, A, Q, hSe, n, ACT, hWJ, eT, eG, eP, ec, eR, hact, m47, m48, m49, m50, hHD, hPP, hPF,
    hPA, hPB, -, -, -, hACTh, hPTs, -, hNXTs, -, -, -, -, -, -, hACTHD, hLA, hblk, hlow, hz, hhS,
    hInv, hL, hW, hsvt, htX, hok, hpath, hdc, wbS, wT1S, hRm, hINF, hdist, we⟩ := hout.ex
  have eT' : W.T = T := eT
  have eG' : W.G = G := eG
  have eP' : W.P = P := eP
  have ec' : W.c = c := ec
  have eR' : W.R = R := eR
  subst eT' eG' eP' ec' eR'
  dsimp only at hWJ hhS
  have hOS : W.s = W.R.nodes.length := rfl
  -- the loads
  have b62 : st2.regs 62 = h := by rw [hother2 62 (by omega), a62]
  obtain ⟨regs3, hld, hldo, hrunL⟩ := ldR_fwd (w := w) (p := p) (ω := ω) (c := h) blkRegs 0 st2 b62 (by decide)
    blkRegs_nodup (by rw [blkRegs_length]; omega)
  have q_lo : ∀ i < 43, regs3 i = (W.LReg A Q (W.c.Δ W.G)).getD i 0 := fun i hi => by
    have := hld i (by rw [blkRegs_length]; omega)
    rw [blkRegs_lt hi, Nat.add_zero] at this
    rw [this, hblk i (by omega), setupBlock_lt hi]
  have q_hi : ∀ j < 8, regs3 (50 + j) = st2.mem (h + (43 + j)) := fun j hj => by
    have := hld (43 + j) (by rw [blkRegs_length]; omega)
    rw [blkRegs_hi hj, Nat.add_zero] at this
    exact this
  have q50 : regs3 50 = W.c.loS W.G := by
    rw [q_hi 0 (by omega), hblk _ (by omega), show 43 + 0 = 43 + 0 from rfl, setupBlock_hi]; rfl
  have q51 : regs3 51 = W.sv W.c.t := by
    rw [q_hi 1 (by omega), hblk _ (by omega), setupBlock_hi]; rfl
  have q52 : regs3 52 = W.c.t := by
    rw [q_hi 2 (by omega), hblk _ (by omega), setupBlock_hi]; rfl
  have q53 : regs3 53 = if 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t then 1 else 0 := by
    rw [q_hi 3 (by omega), hblk _ (by omega), setupBlock_hi]; rfl
  have q54 : regs3 54 = A.PF := by rw [q_hi 4 (by omega)]; exact m47
  have q55 : regs3 55 = A.PB := by rw [q_hi 5 (by omega)]; exact m48
  have q56 : regs3 56 = ACT := by rw [q_hi 6 (by omega)]; exact m49
  have q57 : regs3 57 = hSe := by rw [q_hi 7 (by omega)]; exact m50
  have q6 : ∀ r, 60 ≤ r → r ≤ 62 → regs3 r = stA.regs r := fun r h1 h2 => by
    rw [hldo r (not_mem_blkRegs (by omega) (by omega)), hother2 r (by omega)]
  set st3 : State := { st2 with regs := regs3 } with hst3
  set st4 : State := { st3 with regs := Function.update st3.regs 13 1 } with hst4
  have h4m : st4.mem = st2.mem := rfl
  have h4r : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 →
      st4.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0 := fun i hi h13 _ _ => by
    simp only [hst4, hst3]; rw [Function.update_of_ne h13]; exact q_lo i hi
  have g4 : ∀ r, r ≠ 13 → st4.regs r = regs3 r := fun r hr => by
    simp only [hst4, hst3]; rw [Function.update_of_ne hr]
  have r32 : st4.regs 32 = 0 := by rw [g4 32 (by omega), q_lo 32 (by omega)]; simp [PW.LReg]
  have r41 : st4.regs 41 = 0 := by rw [g4 41 (by omega), q_lo 41 (by omega)]; simp [PW.LReg]
  have hI4 := hInv false st4 h4m h4r (by simp [hst4]) r32 r41
  have hOk0 : W.Ok w st2.mem := hI4.btw.ok
  have hT0 : W.Tree A st2.mem := hI4.tree
  -- the petals
  obtain ⟨sp, k0, a, st5, st6, c5, c7, hr5, hr7, hI6, hu6, hdec, hsp, hspec, h5r, hfr, hc57⟩ :=
    PW.nodeLoop (ω := ω) hS hPush hPS hClr hF hT' hbP hCp hbR hReg hInv hL hW hsvt htX hok hpath
      hdc wbS wT1S hRm hINF hdist we h4m h4r (by simp [hst4]) r32 r41
      (by rw [g4 _ (by omega), q50]) (by rw [g4 _ (by omega), q51]) (by rw [g4 _ (by omega), q52])
      (by rw [g4 _ (by omega), q53])
  set st7 : State := { st6 with regs := Function.update st5.regs 58 a.ps.length } with hst7
  have g7 : ∀ r, 48 ≤ r → r ≠ 58 → r ≠ 13 → st7.regs r = regs3 r := fun r h1 h2 h3 => by
    simp only [hst7]; rw [Function.update_of_ne h2, hfr r h1, g4 r h3]
  -- the cost so far and the fit
  have hΦ : W.Φ st2.mem ≤ 2 * W.R.S.length + 2 * W.R.nodes.length :=
    (hOk0.Φ_le_A).trans hLA
  have hLb : W.Lb = pL W.G.n := hOk0.hLb.trans hpre.L_eq
  set K := c2 + c5 + c7 + 400 with hKd
  have hKb : K ≤ setupCostOf ⟨W.T, W.G, W.P, W.c, W.R⟩ + PW.Kφ (rootJ W.G.n + 5) * W.Φ st2.mem +
      PW.CJ (rootJ W.G.n + 5) (pL W.G.n) * a.ps.length + 500 * W.R.nodes.length + 3000 := by
    have hKφ := Kφ_mono hWJ
    have hCJ := CJ_mono (Lb := pL W.G.n) hWJ
    have m1 := Nat.mul_le_mul_right (W.Φ st2.mem) hKφ
    have m2 := Nat.mul_le_mul_right a.ps.length hCJ
    rw [hLb, hOS] at hc57
    omega
  have hroom : hSe + 16 ≤ h + (J + 2) * recCost w bodyA W.T W.G W.P W.c W.R :=
    node_room (by unfold bodyA; omega) hL1 hS1 hs (by rw [hJ]; exact hhS)
  obtain ⟨o8, st8, c8, hr8, hpost8⟩ :=
    PW.nodeTail_runs (K := K) (st := st7) (stE := st6) hK hpre hX2 hOk0 hT0 hI6 hL hu6 hdec hlow hz
      hHD ⟨hPP, hPF, hPA, hPB⟩ hACTh hACTHD hPTs hNXTs hact (fun _ => ⟨n, hpath, hdc⟩) hspec hroom
      rfl (fun i hi a1 a2 a3 => by
        simp only [hst7]; rw [Function.update_of_ne (by omega)]; exact h5r i hi a1 a2 a3)
      (by rw [g7 _ (by omega) (by omega) (by omega), q52])
      (by
        rw [g7 _ (by omega) (by omega) (by omega), q53]
        cases sp <;> simp only [Bool.false_eq_true, true_iff, ↓reduceIte] at hsp ⊢ <;>
          simp [hsp])
      (by rw [g7 _ (by omega) (by omega) (by omega), q54])
      (by rw [g7 _ (by omega) (by omega) (by omega), q55])
      (by rw [g7 _ (by omega) (by omega) (by omega), q56])
      (by rw [g7 _ (by omega) (by omega) (by omega), q57])
      (by simp only [hst7, Function.update_self])
      (by rw [g7 _ (by omega) (by omega) (by omega), q6 _ (by omega) (by omega), a60])
      (by rw [g7 _ (by omega) (by omega) (by omega), q6 _ (by omega) (by omega), a61])
      (by rw [g7 _ (by omega) (by omega) (by omega), q6 _ (by omega) (by omega), a62])
      (by omega)
      (fun cs cost hcost => by
        rw [← hJd, hJ] at hcost ⊢
        exact node_fit hpre.L_eq hs hΦ hKb hcost (hreset _ _ _ _ _ _ _ _ _ _ hpre hdec) hhS)
  -- the whole run
  have hmid : Runs w p ω (nodeMid bP bC bR bK) st3 o8 st8 (2 + (c5 + (c7 + c8 + 1) + 1) + 1) := by
    rw [nodeMid_eq]
    exact run_seq (run_assign (Expr.eval_const (by omega))) (run_seq hr5 (run_seq hr7 hr8))
  obtain ⟨cL, hrL, hcL⟩ := hrunL _ _ _ _ hmid
  have hall : Runs w p ω (nodeP bU bP bC bR bK) st0 o8 st8
      (2 + (2 + (2 + (c2 + cL + 1) + 1) + 1) + 1) := by
    unfold nodeP
    exact run_seq hA1 (run_seq hA2 (run_seq hA3 (run_seq hr2 hrL)))
  refine ⟨o8, st8, _, hall, hpost8.mono ?_⟩
  rw [blkRegs_length] at hcL
  omega

end MinCostFlow.LowStretch
