module

public import MinCostFlow.LowStretch.ProgClusterSetupSpec

/-!
# Two facts that the node part needs from the setup and the petal loop

The node part of the body uses the setup through its contract and the loop of the regular petals
through its run lemma. Two facts that it needs are not part of them. They are stated here, so
that the node part can take them as hypotheses. `ProgramOwed.lean` proves both.
- `SetupOutJ`: `SetupOut` with the number `J` of the classes of the queues of the petal searches
  at most `rootJ n + 5`, for the bound `rootJ n` of the global block (the setup uses `J + 5`).
  The cost of a petal (`CJ`, `Kφ`) is in terms of `W.L.J`, and the share of the body is in terms
  of `rootJ n`. `setupCJ` is `setupC` with this postcondition.
- `RegPrefix`: the run of the loop of the regular petals (`LInv.regP_runs`), where the list of
  petals at the end starts with the list at the start. With a special petal, the rules of the
  step (`LInv.decOk`) need that petal `0` is still the special petal.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `SetupOut` with `W.L.J ≤ rootJ n + 5`. -/
structure SetupOutJ (w : ℕ) (g : SetG) (h : ℕ) (mem mem' : ℕ → ℕ) : Prop where
  ex : ∃ (W : PW) (A : PW.TA) (Q : PW.LA) (hS n ACT : ℕ), W.L.J ≤ rootJ g.G.n + 5 ∧
    W.T = g.T ∧ W.G = g.G ∧ W.P = g.P ∧ W.c = g.c ∧ W.R = g.R ∧
    (∀ i < W.nA, mem' (ACT + 2 * i) = W.pr i ∧
      mem' (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0) ∧
    mem' (h + 47) = A.PF ∧ mem' (h + 48) = A.PB ∧ mem' (h + 49) = ACT ∧ mem' (h + 50) = hS ∧
    h + 51 ≤ W.L.HD ∧ h + 51 ≤ A.PP ∧ h + 51 ≤ A.PF ∧ h + 51 ≤ A.PA ∧ h + 51 ≤ A.PB ∧
    h + 51 ≤ A.FD ∧ h + 51 ≤ W.L.OK ∧ h + 51 ≤ W.NXT ∧ h + 51 ≤ ACT ∧
    Q.PT + W.s ≤ hS ∧ W.L.OK + W.s ≤ hS ∧ W.NXT + W.s + 1 ≤ hS ∧ A.PP + W.s ≤ hS ∧
    A.PF + W.s ≤ hS ∧ A.PA + W.s ≤ hS ∧ A.PB + W.s ≤ hS ∧ A.FD + W.s ≤ hS ∧
    ACT + 2 * W.nA ≤ hS ∧ ACT + 2 * W.nA ≤ W.L.HD ∧ W.L.A ≤ 2 * g.R.S.length + 2 * W.s ∧
    (∀ i < 47, mem' (h + i) = (setupBlock W A Q).getD i 0) ∧
    (∀ a < h, mem' a = mem a) ∧ ZeroFrom mem' hS ∧
    hS ≤ h + 1000 * (rootJ g.G.n + 1) * (g.R.S.length + g.R.nodes.length + g.P.L + 10) ∧
    (∀ (sp : Bool) (st : State), st.mem = mem' →
      (∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → st.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0) →
      st.regs 13 = 1 → st.regs 32 = 0 → st.regs 41 = 0 →
      W.LInv A Q sp 0 mem' w ⟨0, 1, [], W.Φ mem'⟩ st) ∧
    W.LLay A Q w ∧ W.LW A Q w ∧
    W.sv W.c.t < W.s ∧ W.c.t ∈ W.c.X ∧ mem' (W.L.OK + W.sv W.c.t) = W.L.os ∧
    W.Path mem' (W.sv W.c.t) n ∧ W.c.HwDec W.G W.c.t (W.stp A mem' (W.sv W.c.t) n) W.c.hw ∧
    W.c.loS W.G + (W.Lb + 1) * W.bw + 2 < 2 ^ w ∧
    (8 * W.M * (W.κ + W.nA) + (W.c.loS W.G + (W.Lb + 1) * W.bw + 1) * (W.nA * 2 ^ W.Es)) *
      (W.Sm + 1) < 2 ^ w ∧
    W.c.loS W.G + (W.Lb + 1) * W.bw ≤ W.Rm ∧ W.c.loS W.G + (W.Lb + 1) * W.bw < W.L.INF ∧
    (5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t →
      W.c.loS W.G + W.Lb * W.bw < W.c.d W.G W.c.x0 W.c.t) ∧
    W.c.t < 2 ^ w

/-- The contract of the setup with `SetupOutJ`. -/
def setupCJ (w : ℕ) : Contract :=
  ghostC (setupPre w) (fun g args mem _ mem' => ∀ GB RB h, args = [GB, RB, h] →
    SetupOutJ w g h mem mem') setupCost

/-- **The loop of the regular petals keeps the petals it started with.** This is the statement
of `LInv.regP_runs` with `a0.ps <+: a.ps` added. -/
def RegPrefix (w : ℕ) (p : Program) (bP bC : ℕ) : Prop :=
  ∀ (W : PW) (A : PW.TA) (Q : PW.LA) (sp : Bool) (k0 : ℕ) (M0 : ℕ → ℕ) (a0 : PW.LG)
    (st : State) (ω : ℕ → Bool), W.LInv A Q sp k0 M0 w a0 st → W.LLay A Q w → W.LW A Q w →
    ∃ o st' c, Runs w p ω (regP bP bC) st o st' c ∧
      ∃ a : PW.LG, o = .returned a.ps.length ∧ W.LInv A Q sp k0 M0 w a st' ∧ a.u = W.s ∧
        a0.ps <+: a.ps ∧
        c + PW.Kφ W.L.J * a.φ + PW.CJ W.L.J W.Lb * a0.ps.length ≤
          PW.Kφ W.L.J * a0.φ + PW.CJ W.L.J W.Lb * a.ps.length + 500 * (W.s - a0.u) + 20

end MinCostFlow.LowStretch
