module

public import MinCostFlow.LowStretch.ProgClusterLoop3

/-!
# The loop of the regular petals: one petal as a run

`PW.LInv.regPet_runs`: at an allowed far node `u`, the statement `regPet` followed by the step to
`u + 1` runs, and the invariant of the loop holds after it with the new petal added. Its cost is
paid by the drop of the potential, up to `CJ` and a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- The word facts of the loop. -/
structure LW (W : PW) (A : TA) (Q : LA) (w : ℕ) : Prop where
  wR : ∀ x ∈ W.LReg A Q (W.c.Δ W.G), x < 2 ^ w
  wb : (W.Lb + 1) * W.bw + 2 < 2 ^ w
  wT1 : (8 * W.M * (W.κ + W.nA) + ((W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
    (W.Sm + 1) < 2 ^ w
  hRm : (W.Lb + 1) * W.bw ≤ W.Rm
  hINF : (W.Lb + 1) * W.bw < W.L.INF
  wΔ : 3 * W.c.Δ W.G < 2 ^ w
  wd : ∀ a ∈ W.c.X, 4 * W.c.d W.G W.c.x0 a < 2 ^ w

open Classical in
set_option maxHeartbeats 8000000 in
/-- **One regular petal, as a run.** -/
theorem LInv.regPet_runs {p : Program} {bS bF bT bPush bPS bClr bP bC : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hbP : p.procs[bP]? = some (petalP bS bF bT)) (hCp : MeetsContract w p bC (cpC w))
    {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hW : W.LW A Q w) (hu : a.u < W.s)
    (hal : st.mem (W.L.OK + a.u) = W.L.os) (hfar : 3 * W.c.Δ W.G < 4 * st.mem (A.FD + a.u))
    (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (.seq (regPet bP bC) (.assign 32 (.bin .add (.reg 32) (.const 1))))
        st o st' c ∧ o = .normal ∧
      ∃ pd φ', W.LInv A Q sp k0 M0 w ⟨a.u + 1, a.rs + 1, a.ps ++ [pd], φ'⟩ st' ∧
        c + Kφ W.L.J * φ' ≤ Kφ W.L.J * a.φ + CJ W.L.J W.Lb + 400 := by
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL; have wSL := h.wSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc; have hpt := hL.pt
  have wpt := hL.wpt
  have hT := hI.tree
  have r0 : st.regs 0 = W.L.D := by
    simpa [LReg] using hI.regs 0 (by omega) (by omega) (by omega) (by omega)
  have r1 : st.regs 1 = W.L.J := by
    simpa [LReg] using hI.regs 1 (by omega) (by omega) (by omega) (by omega)
  have r2 : st.regs 2 = W.L.A := by
    simpa [LReg] using hI.regs 2 (by omega) (by omega) (by omega) (by omega)
  have r3 : st.regs 3 = W.L.INF := by
    simpa [LReg] using hI.regs 3 (by omega) (by omega) (by omega) (by omega)
  have r4 : st.regs 4 = W.L.LO := by
    simpa [LReg] using hI.regs 4 (by omega) (by omega) (by omega) (by omega)
  have r5 : st.regs 5 = W.L.HI := by
    simpa [LReg] using hI.regs 5 (by omega) (by omega) (by omega) (by omega)
  have r6 : st.regs 6 = W.L.HD := by
    simpa [LReg] using hI.regs 6 (by omega) (by omega) (by omega) (by omega)
  have r7 : st.regs 7 = W.L.CS := by
    simpa [LReg] using hI.regs 7 (by omega) (by omega) (by omega) (by omega)
  have r8 : st.regs 8 = W.L.CL := by
    simpa [LReg] using hI.regs 8 (by omega) (by omega) (by omega) (by omega)
  have r9 : st.regs 9 = W.L.OK := by
    simpa [LReg] using hI.regs 9 (by omega) (by omega) (by omega) (by omega)
  have r10 : st.regs 10 = W.L.os := by
    simpa [LReg] using hI.regs 10 (by omega) (by omega) (by omega) (by omega)
  have r11 : st.regs 11 = W.L.TS := by
    simpa [LReg] using hI.regs 11 (by omega) (by omega) (by omega) (by omega)
  have r12 : st.regs 12 = W.L.NN := by
    simpa [LReg] using hI.regs 12 (by omega) (by omega) (by omega) (by omega)
  have r14 : st.regs 14 = W.RR := by
    simpa [LReg] using hI.regs 14 (by omega) (by omega) (by omega) (by omega)
  have r15 : st.regs 15 = W.ORD := by
    simpa [LReg] using hI.regs 15 (by omega) (by omega) (by omega) (by omega)
  have r16 : st.regs 16 = W.AS := by
    simpa [LReg] using hI.regs 16 (by omega) (by omega) (by omega) (by omega)
  have r17 : st.regs 17 = W.EXP := by
    simpa [LReg] using hI.regs 17 (by omega) (by omega) (by omega) (by omega)
  have r18 : st.regs 18 = W.Es := by
    simpa [LReg] using hI.regs 18 (by omega) (by omega) (by omega) (by omega)
  have r19 : st.regs 19 = W.SUM := by
    simpa [LReg] using hI.regs 19 (by omega) (by omega) (by omega) (by omega)
  have r20 : st.regs 20 = W.M := by
    simpa [LReg] using hI.regs 20 (by omega) (by omega) (by omega) (by omega)
  have r21 : st.regs 21 = W.κ := by
    simpa [LReg] using hI.regs 21 (by omega) (by omega) (by omega) (by omega)
  have r22 : st.regs 22 = W.nact := by
    simpa [LReg] using hI.regs 22 (by omega) (by omega) (by omega) (by omega)
  have r23 : st.regs 23 = 0 := by
    simpa [LReg] using hI.regs 23 (by omega) (by omega) (by omega) (by omega)
  have r24 : st.regs 24 = W.bw := by
    simpa [LReg] using hI.regs 24 (by omega) (by omega) (by omega) (by omega)
  have r25 : st.regs 25 = W.Lb := by
    simpa [LReg] using hI.regs 25 (by omega) (by omega) (by omega) (by omega)
  have r26 : st.regs 26 = W.SQ := by
    simpa [LReg] using hI.regs 26 (by omega) (by omega) (by omega) (by omega)
  have r27 : st.regs 27 = W.P2 := by
    simpa [LReg] using hI.regs 27 (by omega) (by omega) (by omega) (by omega)
  have r28 : st.regs 28 = W.NXT := by
    simpa [LReg] using hI.regs 28 (by omega) (by omega) (by omega) (by omega)
  have r29 : st.regs 29 = W.SL := by
    simpa [LReg] using hI.regs 29 (by omega) (by omega) (by omega) (by omega)
  have r30 : st.regs 30 = W.s := by
    simpa [LReg] using hI.regs 30 (by omega) (by omega) (by omega) (by omega)
  have r31 : st.regs 31 = W.CTL := by
    simpa [LReg] using hI.regs 31 (by omega) (by omega) (by omega) (by omega)
  have r33 : st.regs 33 = Q.PL := by
    simpa [LReg] using hI.regs 33 (by omega) (by omega) (by omega) (by omega)
  have r34 : st.regs 34 = Q.PO := by
    simpa [LReg] using hI.regs 34 (by omega) (by omega) (by omega) (by omega)
  have r35 : st.regs 35 = Q.CT := by
    simpa [LReg] using hI.regs 35 (by omega) (by omega) (by omega) (by omega)
  have r36 : st.regs 36 = Q.CC := by
    simpa [LReg] using hI.regs 36 (by omega) (by omega) (by omega) (by omega)
  have r37 : st.regs 37 = Q.PT := by
    simpa [LReg] using hI.regs 37 (by omega) (by omega) (by omega) (by omega)
  have r38 : st.regs 38 = A.PP := by
    simpa [LReg] using hI.regs 38 (by omega) (by omega) (by omega) (by omega)
  have r39 : st.regs 39 = A.PA := by
    simpa [LReg] using hI.regs 39 (by omega) (by omega) (by omega) (by omega)
  have r40 : st.regs 40 = A.FD := by
    simpa [LReg] using hI.regs 40 (by omega) (by omega) (by omega) (by omega)
  have r42 : st.regs 42 = W.c.Δ W.G := by
    simpa [LReg] using hI.regs 42 (by omega) (by omega) (by omega) (by omega)
  have r13 := hI.r13; have r32 := hI.r32; have r41 := hI.r41
  have hrsw := hI.rsw; have hroom := hI.room; have hkle := hI.kle
  -- the node is not the node of the center
  have hr : a.u ≠ W.root := by
    intro hr
    have h0 := hT.fd _ h.conn.1
    rw [show W.c.d W.G W.c.x0 W.c.x0 = 0 from PG.dist_self (by simpa using h.conn.1)] at h0
    rw [hr] at hfar; unfold root at hfar; omega
  obtain ⟨n, hn1, hn2⟩ := hT.reach hu
  have hp : W.Path st.mem a.u n := ⟨hn1, hn2⟩
  obtain ⟨-, hpaX, hpa, -⟩ := hT.edge a.u hu hr
  have hfd := hT.fdA hu hr
  set e := st.mem (A.PA + a.u) with he
  obtain ⟨hw, hd⟩ := Tree.hwDec h hT n a.u e hp hpaX hpa
  have hp' : W.Path st.mem (W.sv e) n := by rw [hpa]; exact hp
  have hd' : W.c.HwDec W.G e (W.stp A st.mem (W.sv e) n) hw := by rw [hpa]; exact hd
  have hal' : st.mem (W.L.OK + W.sv e) = W.L.os := by rw [hpa]; exact hal
  have hdist : 0 + W.Lb * W.bw < W.c.d W.G W.c.x0 e := by
    have := Cl.L_mul_bw_le (G := W.G) (P := W.P) (c := W.c)
    rw [h.hLb, h.hbw]; rw [hfd] at hfar; omega
  have hwA : ∀ x ∈ W.pargs (W.on st.mem (W.sv e)) e (W.stp A st.mem (W.sv e) n) hw 0 a.rs,
      x < 2 ^ w := by
    intro x hx
    rw [pargs_eq] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | omega | exact hW.wR _ (by simp [LReg])
  obtain ⟨o1, st1, c1, hrun1, i, m, ℓ, hpet, hcarve, hnd, hsub, hmn, e0, e1, e2, q1, q2, q3, hB1,
    hT1, hc1, hok1, hsafe1, hlow1, hcost1⟩ := hI.btw.petal_runs (lo := 0) (hw := hw) hS hPush hPS
      hClr hF hT' hT hI.cone hL.taSafe hp' hpaX hal' hd' (by simpa using hW.wb)
      (by simpa using hW.wT1) (by simpa using hW.hRm) (by simpa using hW.hINF) (by omega) hwA
      hdist st.pos ω
  rw [hpa] at e0 e1 e2 q1
  -- counts
  have huN : a.u ∈ W.Nodes st.mem :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hal⟩
  have hN1 : 1 ≤ (W.Nodes st.mem).card := Finset.card_pos.mpr ⟨_, huN⟩
  have hℓN : ℓ.length ≤ (W.Nodes st.mem).card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun v hv => hsub v (List.mem_toFinset.mp hv)
  have hpm : W.pe st.mem a.u m < W.s := hp.lt h.root_lt hmn.le
  -- cells that the petal keeps
  have hPOk : st1.mem (Q.PO + a.ps.length) = st.mem (Q.PO + a.ps.length) :=
    hsafe1 _ (Or.inr (by omega))
  have hs1PA : st1.mem (A.PA + a.u) = e := hsafe1 _ (Or.inl (by omega))
  have hs1PAm : st1.mem (A.PA + W.pe st.mem a.u m) = st.mem (A.PA + W.pe st.mem a.u m) :=
    hsafe1 _ (Or.inl (by omega))
  have hs1PPm : st1.mem (A.PP + W.pe st.mem a.u m) = st.mem (A.PP + W.pe st.mem a.u m) :=
    hsafe1 _ (Or.inl (by omega))
  suffices key : ∃ o st' c, Runs w p ω (.seq (regPet bP bC)
      (.assign 32 (.bin .add (.reg 32) (.const 1)))) st o st' c ∧
      (o = .normal ∧ ∃ pd, W.LInv A Q sp k0 M0 w ⟨a.u + 1, a.rs + 1, a.ps ++ [pd],
        W.Φ st1.mem⟩ st') ∧ c ≤ c1 + 17 * ℓ.length + 390 by
    obtain ⟨o, st', c, hr, ⟨ho, pd, hI'⟩, hc⟩ := key
    have hφ := hI.φ
    rw [hφ] at hcost1
    exact ⟨o, st', c, hr, ho, pd, _, hI', by omega⟩
  refine runs_start_le ?_
  unfold regPet
  refine runs_seq_assoc_le ?_
  refine runs_seq_call_runs_le
    (vs := W.pargs (W.on st.mem (W.sv e)) e (W.stp A st.mem (W.sv e) n) hw 0 a.rs) ?_ hbP hrun1 ?_
  · rw [pargs_eq]; eval_expr
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := st.mem (Q.PO + a.ps.length)) (by eval_expr) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := ℓ.length) (by eval_expr) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_call_le (vs := [W.SL, ℓ.length, Q.PL + st.mem (Q.PO + a.ps.length)]) hCp
    (by eval_expr) (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, Or.inl (by omega), by omega, by omega⟩ ?_
  intro v2 mem2 pos2 hpost
  obtain ⟨hcp1, hcp2⟩ := hpost _ _ _ rfl
  have m2 : ∀ x, x < Q.PL → mem2 x = st1.mem x := fun x hx => hcp2 x (Or.inl (by omega))
  refine runs_seq_assoc_le ?_
  refine runs_seq_store_le (x := Q.PO + (a.ps.length + 1))
    (v := st.mem (Q.PO + a.ps.length) + ℓ.length) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_store_le (x := Q.CT + (a.ps.length + 1)) (v := e) (by eval_expr)
    (Expr.eval_load_of_eq (by eval_expr) (by
      show Function.update mem2 _ _ (A.PA + a.u) = e
      rw [Function.update_of_ne (by omega), m2 _ (by omega), hs1PA])) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := W.pe st.mem a.u m) (Expr.eval_load_of_eq (by eval_expr) (by
      show Function.update (Function.update mem2 _ _) _ _ (W.CTL + 3) = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), m2 _ (by omega), q1])) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_store_le (x := Q.CC + (a.ps.length + 1))
    (v := st.mem (A.PA + W.pe st.mem a.u m)) (by eval_expr)
    (Expr.eval_load_of_eq (by eval_expr) (by
      show Function.update (Function.update mem2 _ _) _ _ (A.PA + W.pe st.mem a.u m) = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), m2 _ (by omega), hs1PAm])) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_store_le (x := Q.PT + a.ps.length)
    (v := st.mem (A.PP + W.pe st.mem a.u m)) (by eval_expr)
    (Expr.eval_load_of_eq (by eval_expr) (by
      show Function.update (Function.update (Function.update mem2 _ _) _ _) _ _
        (A.PP + W.pe st.mem a.u m) = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), m2 _ (by omega), hs1PPm])) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := a.ps.length + 1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := a.rs + 1) (by eval_expr) ?_
  refine runs_assign_le (v := a.u + 1) (by eval_expr) ?_ ?_
  · refine ⟨rfl, ⟨e, hw, o1.value - 2, i⟩, ?_⟩
    refine hI.after_pet hL hu hfar hp hpa hpaX hd hpet hcarve hnd hsub hmn e0 e1 e2 hB1 hT1 hc1
      hok1 hsafe1 hlow1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
    · intro x hx
      unfold Out at hx
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcp2 x (by omega)]
    · intro j hj
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcp1 j hj, q3 j hj]
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_self]
    · dsimp only
      rw [Function.update_self]
    · intro x hx hn1 hn2 hn3 hn4 hn5
      unfold Out at hx
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcp2 x (by omega), hsafe1 x (Or.inr (by omega))]
    · intro j hj h13 h32 h41
      dsimp only
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | omega
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
  · simp only [cpC, List.getD_cons_succ, List.getD_cons_zero, argsSize_cons, argsSize_nil,
      Expr.size_reg, Expr.size_const, Expr.size_load, Expr.size_bin, pargs_eq]
    omega

end PW

end MinCostFlow.LowStretch
