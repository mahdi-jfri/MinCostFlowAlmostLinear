module

public import MinCostFlow.LowStretch.ProgBodyNodeRun
import MinCostFlow.LowStretch.ProgBodyNodeCongr

/-!
# The petals of the node part

After the block of the setup is loaded and the stamp is `1`, the node part runs the special
petal when the flag in register `53` is `1`, then calls the loop of the regular petals.
`PW.nodeLoop` gives the two runs, the invariant at the end of the loop, the rules of the step
(`LInv.decOk`) and the cost: the drop of the potential, `CJ` per petal and `500` per node.

The loop of the regular petals is used through `RegPrefix` (the run lemma `LInv.regP_runs` with
the petals of the start kept at the front of the list), which the special petal needs for
`LInv.decOk`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

theorem cond_spPet_writesBelow (bP bC : ℕ) :
    HierPaths.Stmt.WritesBelow 48 (.cond (.reg 53) (spPet bP bC) .nop) := by
  simp [spPet, regPet, HierPaths.Stmt.WritesBelow]

open Classical in
/-- **The petals of the node part.** From the state `st4` after the loads and the stamp, the
conditional special petal and the call of the loop run, and the loop ends with its invariant at
`u = s`, a step that meets `DecOk`, and the cost of the potential and the petals. -/
theorem nodeLoop {p : Program} {ω : ℕ → Bool} {bS bF bT bPush bPS bClr bP bC bR : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT' : MeetsContract w p bT (portC w))
    (hbP : p.procs[bP]? = some (petalP bS bF bT)) (hCp : MeetsContract w p bC (cpC w))
    (hbR : p.procs[bR]? = some (regP bP bC)) (hReg : RegPrefix w p bP bC)
    {M0 : ℕ → ℕ} {n : ℕ} {st4 : State}
    (hInv : ∀ (sp : Bool) (st : State), st.mem = M0 →
      (∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → st.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0) →
      st.regs 13 = 1 → st.regs 32 = 0 → st.regs 41 = 0 →
      W.LInv A Q sp 0 M0 w ⟨0, 1, [], W.Φ M0⟩ st)
    (hL : W.LLay A Q w) (hW : W.LW A Q w)
    (hsvt : W.sv W.c.t < W.s) (htX : W.c.t ∈ W.c.X) (hok : M0 (W.L.OK + W.sv W.c.t) = W.L.os)
    (hpath : W.Path M0 (W.sv W.c.t) n)
    (hdc : W.c.HwDec W.G W.c.t (W.stp A M0 (W.sv W.c.t) n) W.c.hw)
    (wbS : W.c.loS W.G + (W.Lb + 1) * W.bw + 2 < 2 ^ w)
    (wT1S : (8 * W.M * (W.κ + W.nA) + (W.c.loS W.G + (W.Lb + 1) * W.bw + 1) *
      (W.nA * 2 ^ W.Es)) * (W.Sm + 1) < 2 ^ w)
    (hRmS : W.c.loS W.G + (W.Lb + 1) * W.bw ≤ W.Rm)
    (hINFS : W.c.loS W.G + (W.Lb + 1) * W.bw < W.L.INF)
    (hdist : 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t →
      W.c.loS W.G + W.Lb * W.bw < W.c.d W.G W.c.x0 W.c.t)
    (we : W.c.t < 2 ^ w)
    (h4m : st4.mem = M0)
    (h4r : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → st4.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0)
    (r13 : st4.regs 13 = 1) (r32 : st4.regs 32 = 0) (r41 : st4.regs 41 = 0)
    (r50 : st4.regs 50 = W.c.loS W.G) (r51 : st4.regs 51 = W.sv W.c.t) (r52 : st4.regs 52 = W.c.t)
    (r53 : st4.regs 53 = if 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t then 1 else 0) :
    ∃ (sp : Bool) (k0 : ℕ) (a : LG) (st5 st6 : State) (c5 c7 : ℕ),
      Runs w p ω (.cond (.reg 53) (spPet bP bC) .nop) st4 .normal st5 c5 ∧
      Runs w p ω (.call 58 bR (rgs (List.range 43))) st5 .normal
        { st6 with regs := Function.update st5.regs 58 a.ps.length } c7 ∧
      W.LInv A Q sp k0 M0 w a st6 ∧ a.u = W.s ∧ W.c.DecOk W.G W.P ⟨sp, a.ps⟩ ∧
      (sp = true ↔ 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t) ∧
      (sp = true → 0 < a.ps.length ∧ ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).tj = W.c.t ∧
        ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).hw = W.c.hw) ∧
      (∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 →
        st5.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0) ∧
      (∀ r, 48 ≤ r → st5.regs r = st4.regs r) ∧
      c5 + c7 ≤ Kφ W.L.J * W.Φ M0 + CJ W.L.J W.Lb * a.ps.length + 500 * W.s + 600 := by
  set sp : Bool := decide (5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t) with hspd
  have hsp : sp = true ↔ 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t := by simp [hspd]
  have hI4 := hInv sp st4 h4m h4r r13 r32 r41
  have hY4 : W.Y st4.mem = W.c.X := hI4.Y
  have hk2 : 2 + W.s < 2 ^ w := by
    have := hL.wpt; have := hL.pl; have := hL.po; have := hL.ct; have := hL.cc; have := hL.pt
    omega
  -- the special petal, or nothing
  obtain ⟨k0, a1, st5, c5, hr5, hI5, hk0, hu1, hlen1, hsp1, hc5⟩ :
      ∃ (k0 : ℕ) (a1 : LG) (st5 : State) (c5 : ℕ),
        Runs w p ω (.cond (.reg 53) (spPet bP bC) .nop) st4 .normal st5 c5 ∧
        W.LInv A Q sp k0 M0 w a1 st5 ∧ k0 = (if sp then 1 else 0) ∧ a1.u = 0 ∧
        a1.ps.length = k0 ∧
        (sp = true → ∃ pd : PD, a1.ps = [pd] ∧ pd.tj = W.c.t ∧ pd.hw = W.c.hw ∧
          W.c.PetalOk W.G W.P W.c.X (W.c.loS W.G) pd) ∧
        c5 + Kφ W.L.J * a1.φ ≤ Kφ W.L.J * W.Φ M0 + CJ W.L.J W.Lb * k0 + 460 := by
    by_cases hs : 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t
    · have hsT : sp = true := by simp [hspd, hs]
      obtain ⟨o, st', c, hr, ho, r, i, φ', hI', hpo, hc⟩ :=
        hI4.spPet_runs hS hPush hPS hClr hF hT' hbP hCp hL hW rfl rfl (by simpa using hk2)
          hsvt htX rfl (by rw [h4m]; exact hok) (by rw [h4m]; exact hpath)
          (by rw [h4m]; exact hdc) wbS wT1S hRmS hINFS (hdist hs) r50 r51 r52 we ω
      subst ho
      refine ⟨1, _, st', 1 + c + 1, runs_cond_iff.mpr ⟨1, c, Expr.eval_reg_of_eq
        (by rw [r53]; simp [hs]), by simpa using hr, rfl⟩, hI', by simp [hsT], rfl, rfl,
        fun _ => ⟨_, rfl, rfl, rfl, by rw [← hY4]; exact hpo⟩, ?_⟩
      simp only [Nat.mul_one] at hc ⊢
      omega
    · have hsF : sp = false := by simp [hspd, hs]
      refine ⟨0, _, st4, 1 + 1 + 1, runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq
        (by rw [r53]; simp [hs]), by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
        hI4, by simp [hsF], rfl, rfl, fun h => by simp [hsF] at h, ?_⟩
      simp only [Nat.mul_zero]
      omega
  -- the registers after the special petal
  have hfr : ∀ r, 48 ≤ r → st5.regs r = st4.regs r :=
    runs_regs_frame (cond_spPet_writesBelow bP bC) hr5
  have h5r : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 →
      st5.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0 := hI5.regs
  -- the call of the loop
  set vs := (List.range 43).map st5.regs with hvs
  have hIc : W.LInv A Q sp k0 M0 w a1 (startState vs st5.mem st5.pos) :=
    hI5.congr rfl fun i hi => by simp [startState, hvs, hi]
  obtain ⟨o6, st6, c6, hr6, a, ho6, hI6, hu6, hpre6, hc6⟩ := hReg W A Q sp k0 M0 a1 _ ω hIc hL hW
  have hcall : Runs w p ω (.call 58 bR (rgs (List.range 43))) st5 .normal
      { st6 with regs := Function.update st5.regs 58 a.ps.length } (argsSize (rgs (List.range 43)) + c6 + 1) := by
    refine runs_call_iff.mpr ⟨vs, regP bP bC, o6, st6, c6, by rw [evalArgs_rgs], hbR, hr6, rfl,
      by rw [ho6]; rfl, rfl⟩
  have hspec : sp = true → 0 < a.ps.length ∧ ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).tj = W.c.t ∧
      ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).hw = W.c.hw ∧
      W.c.PetalOk W.G W.P W.c.X (W.c.loS W.G) ((⟨sp, a.ps⟩ : Cl.Dec).pd 0) := by
    intro hs
    obtain ⟨pd, hps, ht, hh, hok'⟩ := hsp1 hs
    obtain ⟨t, ht'⟩ := hpre6
    rw [hps] at ht'
    have hpd : (⟨sp, a.ps⟩ : Cl.Dec).pd 0 = pd := by
      simp [Cl.Dec.pd, ← ht']
    refine ⟨by rw [← ht']; simp, ?_, ?_, ?_⟩ <;> rw [hpd] <;> assumption
  have hdec : W.c.DecOk W.G W.P ⟨sp, a.ps⟩ := hI6.decOk hu6 hk0 hsp hspec
  have hk0le := hI6.k0le
  refine ⟨sp, k0, a, st5, st6, c5, _, hr5, hcall, hI6, hu6, hdec, hsp,
    fun hs => ⟨(hspec hs).1, (hspec hs).2.1, (hspec hs).2.2.1⟩, h5r, hfr, ?_⟩
  rw [argsSize_rgs, List.length_range]
  have hu0 : W.s - a1.u = W.s := by omega
  rw [hu0] at hc6
  have hcj : CJ W.L.J W.Lb * a1.ps.length ≤ CJ W.L.J W.Lb * a.ps.length :=
    Nat.mul_le_mul_left _ (by omega)
  rw [hlen1] at hc6 hcj
  omega

end PW

end MinCostFlow.LowStretch
