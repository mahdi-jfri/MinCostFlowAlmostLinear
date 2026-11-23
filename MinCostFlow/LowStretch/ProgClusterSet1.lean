module

public import MinCostFlow.LowStretch.ProgChildDrawRun

/-!
# The setup of a cluster: the first run of Dijkstra

The setup of a cluster starts as `drawP` of the child step: it builds the arc graph of the record
with `arcP`, empties the queues, runs Dijkstra from the node of the center, and finds the radius
with `maxP`. The petals need more than the radius: the arc graph (for the pairs of the parent
arcs), the tentative costs (the distances to the center) and the parents. So we prove a stronger
contract for the same procedure (`drawP_spec2`): besides the radius, it gives the memory after
`arcP` and the state of Dijkstra at the end of the run.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The postcondition of `drawP` with the memory after `arcP` and the state of the run. -/
def drawPost2 (w : ℕ) (g : DWG) (args : List ℕ) (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  v = g.c.Δ g.G ∧ ∀ E : DWE, args = E.args → ∃ v1 mem1 M3 x,
    (arcPC w).post E.ap.args mem v1 mem1 ∧ (∀ a < E.TS, M3 a = mem1 a) ∧
    RunI w E.RG M3 x mem' ∧ (∀ cl, x.2.1 cl = []) ∧
    (∀ a, (a < E.TS ∨ E.Rr + 2 ≤ a) → mem' a = mem1 a) ∧
    ∀ a, (a < E.H ∨ drawEnd E ≤ a) → mem' a = mem a

/-- The stronger contract of `drawP`. -/
def drawC2 (w : ℕ) : Contract := ghostC (drawPre w) (drawPost2 w) drawCost

set_option maxHeartbeats 4000000 in
theorem drawP_spec2 {w : ℕ} {p : Program} {b bA bC bR bM : ℕ}
    (hp : p.HasAt b [drawP bA bC bR bM])
    (hA : MeetsContract w p bA (arcPC w)) (hC : MeetsContract w p bC (pqClearC w))
    (hR : MeetsContract w p bR (dijRunC w)) (hM : MeetsContract w p bM (maxPC w)) :
    MeetsContract w p b (drawC2 w) := by
  have hproc : p.procs[b]? = some (drawP bA bC bR bM) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro g args mem pos hwords hpre
  obtain ⟨E, rfl, hMem, hOk, hAP, hD, hINF, hJ, hJ1, hx0, hx0s, hZ, hEnd, hIJ, hID⟩ := hpre
  have hw := hwords
  simp only [DWE.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hw
  obtain ⟨ws, wnS, wSA, wIN, wPW, wEXP, wLAB, wLOC, wD, wlθ, wx0, wJ, wINF, wH⟩ := hw
  have g0 : E.args[0]?.getD 0 = E.s := rfl
  have g1 : E.args[1]?.getD 0 = E.nS := rfl
  have g2 : E.args[2]?.getD 0 = E.SA := rfl
  have g3 : E.args[3]?.getD 0 = E.IN := rfl
  have g4 : E.args[4]?.getD 0 = E.PW := rfl
  have g5 : E.args[5]?.getD 0 = E.EXP := rfl
  have g6 : E.args[6]?.getD 0 = E.LAB := rfl
  have g7 : E.args[7]?.getD 0 = E.LOC := rfl
  have g8 : E.args[8]?.getD 0 = E.D := rfl
  have g9 : E.args[9]?.getD 0 = E.lθ := rfl
  have g10 : E.args[10]?.getD 0 = E.x0 := rfl
  have g11 : E.args[11]?.getD 0 = E.J := rfl
  have g12 : E.args[12]?.getD 0 = E.INF := rfl
  have g13 : E.args[13]?.getD 0 = E.H := rfl
  wram_enter
  subst hpre
  dsimp only [drawP, layE, aqE, rrE]
  have l5 := hAP.l5
  have hRr : E.Rr + 2 < 2 ^ w := hEnd
  have eRr0 : E.Rr = E.Dq + (3 + 4 * E.J + 2 * E.J * E.Aq) := rfl
  have hDR : E.Dq + 3 + 4 * E.J ≤ E.Rr := by rw [eRr0]; omega
  have hpqS : E.Dq + pqSize E.J E.Aq = E.Rr := rfl
  have eDq : E.Dq = E.H + 16 * E.nS + 8 * E.s + 9 := rfl
  have eAq : E.Aq = 2 * E.nS + E.s + 1 := rfl
  have eTS : E.TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  wram_step
  · refine ⟨E.ap, g.m, g.n, g.NL, ?_, hAP⟩
    simp only [AP.args, DWE.ap, List.cons.injEq, true_and, and_true]; omega
  intro v1 mem1 pos1 hpost1
  have hp1 : (arcPC w).post E.ap.args mem v1 mem1 := fun A' hA' => by
    have := hpost1 A' (by
      rw [← hA']; simp only [AP.args, DWE.ap, List.cons.injEq, true_and, and_true]; omega)
    exact this
  clear hpost1
  have hfr1 := (hp1 E.ap rfl).2.2.2.2.2.2.2.2
  have hsh := Rec.shape_arcP (Dq := E.Dq) (J := E.J) (Aq := E.Aq) (INF := E.INF) (TS := E.TS)
    (rs := 1) hAP hp1 hMem hOk hD hJ hJ1 (by rw [eAq]; rfl) (by simp only [DWE.ap]; omega)
    (by simp only [DWE.ap]; omega) ⟨by rw [hpqS]; omega, hIJ, by omega⟩ (by omega)
    (by simp only [DWE.ap]; omega) (by omega) (by simp only [DWE.ap]; omega)
  have hRG : E.RG = ⟨E.ap.toDL E.Dq E.J E.Aq E.INF E.TS 1, Finset.range E.ap.s,
      g.R.sv g.T g.c g.c.x0, E.Rr⟩ := by
    simp only [DWE.RG, DWE.L, hx0]; rfl
  have hz1 : ∀ a, E.TS ≤ a → mem1 a = 0 := fun a ha => by
    rw [hfr1 a (by simp only [DWE.ap]; omega)]; exact hZ a (by omega)
  have hcells : ∀ M3 x M, (∀ a < E.TS, M3 a = mem1 a) → RunI w E.RG M3 x M →
      (∀ cl, x.2.1 cl = []) → ∀ u < E.s, M (E.TS + (E.s + 1) + u) < 2 ^ w :=
    fun M3 x M hM3 hI hE u hu => by
      rw [hRG] at hI
      exact lt_trans (Rec.draw_cells hp1 hMem hOk hD hINF (DL.g_congr E.L hsh hM3) hI hE hu) wINF
  obtain ⟨o, st', c, hrun, ⟨⟨M3, x, hlow, hI, hE, hv⟩, hfr⟩, hc⟩ :=
    drawT_runs (bC := bC) (bR := bR) (bM := bM) ω
      (st := State.mk mem1 (Function.update (startState E.args mem pos).regs 29 v1) pos1)
      ((DWE.regs_start E mem pos).upd (by omega) _ _ _) hC hR hM hwords hRr hJ1 hIJ hx0s hsh hz1
      hcells
  have hI' := hI
  rw [hRG] at hI'
  refine ⟨o, st', c, hrun, ⟨hv.trans (Rec.draw_result hp1 hMem hOk hD hINF
    (DL.g_congr E.L hsh hlow) hI' hE), fun E' hE' => ?_⟩, ?_⟩
  · have e := DWE.eq_of_args hE'
    subst e
    have hdE : drawEnd E' = E'.Rr + 2 := rfl
    refine ⟨v1, mem1, M3, x, hp1, hlow, hI, hE, fun a ha => hfr a ha, fun a ha => ?_⟩
    rw [hfr a (by omega)]
    exact hfr1 a (by simp only [DWE.ap]; omega)
  · simp only [drawCost, arcPC, DWE.args, AP.args, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil]
    have key : (200 * (Nat.log 2 E.J + 2) + 2000) * (E.Aq + E.s + 1) +
        1000 * (2 * E.nS + 2 * E.s + 2) =
        (200 * (Nat.log 2 E.J + 2) + 3000) * (2 * E.nS + 2 * E.s + 2) := by
      rw [eAq]; ring
    omega

end MinCostFlow.LowStretch
