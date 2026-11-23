module

public import MinCostFlow.LowStretch.ProgClusterLoop4
import MinCostFlow.LowStretch.ProgAmort

/-!
# The loop of the regular petals as a run

`PW.LInv.regBody_runs`: one pass of the body moves from `u` to `u + 1`. At an allowed far node it
carves a petal (`PW.LInv.regPet_runs`); otherwise it only moves on, and the node, if allowed, is
near.

`PW.LInv.regP_runs`: the whole loop. It ends at `u = s` and returns the number of petals. Its cost
is paid by the drop of the potential and by `CJ + 500` for each node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- **A node without a petal.** The loop only moves on. -/
theorem LInv.skip {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hu : a.u < W.s)
    (hnf : st.mem (W.L.OK + a.u) = W.L.os → 4 * st.mem (A.FD + a.u) ≤ 3 * W.c.Δ W.G) :
    W.LInv A Q sp k0 M0 w ⟨a.u + 1, a.rs, a.ps, a.φ⟩
      { st with regs := Function.update st.regs 32 (a.u + 1) } :=
  { hI with
    regs := fun i hi h13 h32 h41 => by
      show Function.update st.regs 32 (a.u + 1) i = _
      rw [Function.update_of_ne h32]; exact hI.regs i hi h13 h32 h41
    r13 := by show Function.update st.regs 32 (a.u + 1) 13 = _; simp [hI.r13]
    r32 := by show Function.update st.regs 32 (a.u + 1) 32 = _; simp
    r41 := by show Function.update st.regs 32 (a.u + 1) 41 = _; simp [hI.r41]
    scan := fun v hv hvs hok => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | hv
      · exact hI.scan v hv hvs hok
      · subst hv; exact hnf hok
    ule := hu
    rsw := by have := hI.rsw; dsimp only; omega }

open Classical in
set_option maxHeartbeats 4000000 in
/-- **One pass of the body of the loop.** -/
theorem LInv.regBody_runs {p : Program} {bS bF bT bPush bPS bClr bP bC : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hbP : p.procs[bP]? = some (petalP bS bF bT)) (hCp : MeetsContract w p bC (cpC w))
    {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hW : W.LW A Q w) (hu : a.u < W.s)
    (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (regBody bP bC) st o st' c ∧ o = .normal ∧
      ∃ a', W.LInv A Q sp k0 M0 w a' st' ∧ a'.u = a.u + 1 ∧ a.ps <+: a'.ps ∧
        a.ps.length ≤ a'.ps.length ∧ a'.ps.length ≤ a.ps.length + 1 ∧
        c + Kφ W.L.J * a'.φ + CJ W.L.J W.Lb * a.ps.length ≤
          Kφ W.L.J * a.φ + CJ W.L.J W.Lb * a'.ps.length + 450 := by
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have wpt := hL.wpt; have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt; have wSL := h.wSL; have hR := h.hR; have hCTL := h.hCTL; have hSUM := h.hSUM
  have hSL := h.hSL
  have hw1 : 1 < 2 ^ w := by have := h.os_lt; omega
  have r9 : st.regs 9 = W.L.OK := by simpa [LReg] using hI.regs 9 (by omega) (by omega) (by omega) (by omega)
  have r10 : st.regs 10 = W.L.os := by
    simpa [LReg] using hI.regs 10 (by omega) (by omega) (by omega) (by omega)
  have r40 : st.regs 40 = A.FD := by
    simpa [LReg] using hI.regs 40 (by omega) (by omega) (by omega) (by omega)
  have r42 : st.regs 42 = W.c.Δ W.G := by
    simpa [LReg] using hI.regs 42 (by omega) (by omega) (by omega) (by omega)
  have r32 := hI.r32
  have wΔ := hW.wΔ
  have hFD : 4 * st.mem (A.FD + a.u) < 2 ^ w := by
    obtain ⟨x, hx, hxu⟩ := h.sv_surj hu
    rw [← hxu, hI.tree.fd x hx]; exact hW.wd x hx
  have he : regCond.eval w st = some ((if st.mem (W.L.OK + a.u) = W.L.os then 1 else 0) *
      (if 3 * W.c.Δ W.G < 4 * st.mem (A.FD + a.u) then 1 else 0)) := by
    unfold regCond
    exact Expr.eval_mul (Expr.eval_eq_op (by eval_expr) (by eval_expr) hw1)
      (Expr.eval_lt_op (x := 3 * W.c.Δ W.G) (y := 4 * st.mem (A.FD + a.u)) (by eval_expr)
        (by eval_expr) hw1) (by split_ifs <;> omega)
  by_cases hc : st.mem (W.L.OK + a.u) = W.L.os ∧ 3 * W.c.Δ W.G < 4 * st.mem (A.FD + a.u)
  · obtain ⟨o, st', c, hr, ho, pd, φ', hI', hcost⟩ := hI.regPet_runs hS hPush hPS hClr hF hT' hbP hCp
      hL hW hu hc.1 hc.2 ω
    obtain ⟨o2, st2, c2, hr2, ⟨rfl, rfl⟩, hc2⟩ := runs_seq_cond_le (k := 0)
      (Q := fun o' st'' => o' = o ∧ st'' = st') (T := regCond.size + 1 + c) he
      (fun _ => ⟨o, st', c, hr, ⟨rfl, rfl⟩, by omega⟩)
      (fun hv => by rw [if_pos hc.1, if_pos hc.2] at hv; simp at hv)
    refine ⟨o2, st2, c2, hr2, ho, ⟨a.u + 1, a.rs + 1, a.ps ++ [pd], φ'⟩, hI', rfl,
      List.prefix_append _ _, by simp, by simp, ?_⟩
    simp only [regCond, Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const] at hc2
    dsimp only
    simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
    omega
  · have hnf : st.mem (W.L.OK + a.u) = W.L.os → 4 * st.mem (A.FD + a.u) ≤ 3 * W.c.Δ W.G :=
      fun hok => by by_contra hf; exact hc ⟨hok, by omega⟩
    have hI' := hI.skip hu hnf
    obtain ⟨o2, st2, c2, hr2, ⟨rfl, rfl⟩, hc2⟩ := runs_seq_cond_le (k := 0) (p := p) (ω := ω)
      (s₁ := regPet bP bC) (s₂ := .nop) (s := .assign 32 (.bin .add (.reg 32) (.const 1)))
      (Q := fun o' st'' => o' = .normal ∧
        st'' = { st with regs := Function.update st.regs 32 (a.u + 1) })
      (T := regCond.size + 1 + 10) he
      (fun hv => by
        exfalso; apply hc
        by_cases h1 : st.mem (W.L.OK + a.u) = W.L.os
        · by_cases h2 : 3 * W.c.Δ W.G < 4 * st.mem (A.FD + a.u)
          · exact ⟨h1, h2⟩
          · rw [if_neg h2] at hv; simp at hv
        · rw [if_neg h1] at hv; simp at hv)
      (fun _ => by
        refine runs_seq_nop_le ?_
        refine runs_assign_le (v := a.u + 1) (by eval_expr) ⟨rfl, rfl⟩ ?_
        simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega)
    refine ⟨_, _, c2, hr2, rfl, _, hI', rfl, List.prefix_refl _, le_rfl, by dsimp only; omega, ?_⟩
    simp only [regCond, Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const] at hc2
    dsimp only
    omega

/-- **The loop of the regular petals.** It ends at `u = s` and returns the number of petals. -/
theorem LInv.regP_runs {p : Program} {bS bF bT bPush bPS bClr bP bC : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hbP : p.procs[bP]? = some (petalP bS bF bT)) (hCp : MeetsContract w p bC (cpC w))
    {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a0 : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a0 st) (hL : W.LLay A Q w) (hW : W.LW A Q w) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (regP bP bC) st o st' c ∧
      ∃ a, o = .returned a.ps.length ∧ W.LInv A Q sp k0 M0 w a st' ∧ a.u = W.s ∧
        a0.ps <+: a.ps ∧ c + Kφ W.L.J * a.φ + CJ W.L.J W.Lb * a0.ps.length ≤
          Kφ W.L.J * a0.φ + CJ W.L.J W.Lb * a.ps.length + 500 * (W.s - a0.u) + 20 := by
  have hw1 : 1 < 2 ^ w := by have := hI.btw.ok.os_lt; omega
  obtain ⟨o, st', c, hr, r, ⟨ho, a, hIa, hau, hpa, hra⟩, hc⟩ :=
    runs_loop_amort (p := p) (ω := ω) (e := .bin .lt (.reg 32) (.reg 30)) (body := regBody bP bC)
      (Inv := fun a st => W.LInv A Q sp k0 M0 w a st ∧ a0.ps <+: a.ps)
      (Fin := fun o st r => o = .normal ∧ ∃ a, W.LInv A Q sp k0 M0 w a st ∧ a.u = W.s ∧
        a0.ps <+: a.ps ∧ r = Kφ W.L.J * a.φ + CJ W.L.J W.Lb * (W.s - a.ps.length))
      (fun a => W.s - a.u) (fun a => Kφ W.L.J * a.φ + CJ W.L.J W.Lb * (W.s - a.ps.length) +
        500 * (W.s - a.u) + 10)
      (condVal := fun st => if st.regs 32 < st.regs 30 then 1 else 0)
      (fun a st _ => Expr.eval_lt_op rfl rfl hw1)
      (fun a st ⟨hI, hpf⟩ hv => by
        have r30 : st.regs 30 = W.s := by
          simpa [LReg] using hI.regs 30 (by omega) (by omega) (by omega) (by omega)
        have hu : a.u = W.s := by
          have := hI.ule; have := hI.r32
          have : ¬ st.regs 32 < st.regs 30 := fun h1 => by simp [h1] at hv
          omega
        exact ⟨_, ⟨rfl, a, hI, hu, hpf, rfl⟩, by rw [hu]; simp; omega⟩)
      (fun a st ⟨hI, hpf⟩ hv => by
        have r30 : st.regs 30 = W.s := by
          simpa [LReg] using hI.regs 30 (by omega) (by omega) (by omega) (by omega)
        have hu : a.u < W.s := by
          have := hI.r32
          have : st.regs 32 < st.regs 30 := by by_contra h1; simp [h1] at hv
          omega
        obtain ⟨o1, st1, c1, hr1, rfl, a', hI', hu', hp', hl1, hl2, hc1⟩ :=
          hI.regBody_runs hS hPush hPS hClr hF hT' hbP hCp hL hW hu ω
        refine ⟨_, st1, c1, hr1, a', ⟨hI', hpf.trans hp'⟩, by omega, ?_⟩
        have hk' := hI'.kle
        have hm : 500 * (W.s - a.u) = 500 * (W.s - a'.u) + 500 := by
          rw [hu', show W.s - a.u = (W.s - (a.u + 1)) + 1 by omega, Nat.mul_succ]
        have e1 : CJ W.L.J W.Lb * (W.s - a.ps.length) =
            CJ W.L.J W.Lb * W.s - CJ W.L.J W.Lb * a.ps.length := Nat.mul_sub _ _ _
        have e2 : CJ W.L.J W.Lb * (W.s - a'.ps.length) =
            CJ W.L.J W.Lb * W.s - CJ W.L.J W.Lb * a'.ps.length := Nat.mul_sub _ _ _
        have f1 : CJ W.L.J W.Lb * a'.ps.length ≤ CJ W.L.J W.Lb * W.s :=
          Nat.mul_le_mul_left _ (by omega)
        have f2 : CJ W.L.J W.Lb * a.ps.length ≤ CJ W.L.J W.Lb * a'.ps.length :=
          Nat.mul_le_mul_left _ hl1
        simp only [Expr.size_bin, Expr.size_reg]
        omega)
      a0 st ⟨hI, List.prefix_refl _⟩
  subst ho hra
  refine ⟨.returned a.ps.length, st', c + 2 + 1, runs_seq_iff.mpr (Or.inr ⟨st', c, 2, hr,
    runs_ret_iff.mpr ⟨_, Expr.eval_reg_of_eq hIa.r41, rfl, rfl, rfl⟩, rfl⟩), a, rfl, hIa, hau, hpa,
    ?_⟩
  have hk0 := hI.kle; have hka := hIa.kle
  have e1 : CJ W.L.J W.Lb * (W.s - a0.ps.length) =
      CJ W.L.J W.Lb * W.s - CJ W.L.J W.Lb * a0.ps.length := Nat.mul_sub _ _ _
  have e2 : CJ W.L.J W.Lb * (W.s - a.ps.length) =
      CJ W.L.J W.Lb * W.s - CJ W.L.J W.Lb * a.ps.length := Nat.mul_sub _ _ _
  have f1 : CJ W.L.J W.Lb * a.ps.length ≤ CJ W.L.J W.Lb * W.s :=
    Nat.mul_le_mul_left _ (by omega)
  have f0 : CJ W.L.J W.Lb * a0.ps.length ≤ CJ W.L.J W.Lb * W.s :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end PW

end MinCostFlow.LowStretch
