module

public import MinCostFlow.LowStretch.ProgChildDrawP

/-!
# The radius of a raw child: the run

`drawP_spec`: `drawP` meets `drawC`. The proof follows the four calls. After `arcP` the graph has
the shape of Dijkstra (`Rec.shape_arcP`); `pqClear` leaves empty queues; the stamps are `0`
since the memory from `H` on was fresh, so a run with stamp `1` may start; at its end
`Rec.draw_result` reads the radius from the tentative costs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace DWE

variable {E : DWE}

/-- The ghost values of the run of Dijkstra in `drawP`. -/
def RG (E : DWE) : RunG := ⟨E.L, Finset.range E.s, E.x0, E.Rr⟩

theorem regs_start (E : DWE) (mem : ℕ → ℕ) (pos : ℕ) : E.Regs (startState E.args mem pos) :=
  fun _ _ => rfl

theorem Regs.upd {st : State} (h : E.Regs st) {r : ℕ} (hr : 14 ≤ r) (v : ℕ) (M : ℕ → ℕ) (q : ℕ) :
    E.Regs { mem := M, regs := Function.update st.regs r v, pos := q } := fun r' hr' => by
  simp only
  rw [Function.update_of_ne (by omega)]
  exact h r' hr'

theorem Regs.mem {st : State} (h : E.Regs st) (M : ℕ → ℕ) : E.Regs { st with mem := M } := h

end DWE

/-- The end of `drawP`: Dijkstra, then `maxP`. -/
theorem drawU_runs {w : ℕ} {p : Program} {bR bM : ℕ} (ω : ℕ → Bool) {E : DWE} {st : State}
    (hr : E.Regs st) (hR : MeetsContract w p bR (dijRunC w)) (hM : MeetsContract w p bM (maxPC w))
    (hwords : ∀ x ∈ E.args, x < 2 ^ w) (hEnd : E.Rr + 2 < 2 ^ w) (hJ1 : 1 ≤ E.J)
    (hpre : runPre w E.RG (E.L.argsS E.Rr E.x0) st.mem)
    (hcells : ∀ x M, RunI w E.RG st.mem x M → (∀ cl, x.2.1 cl = []) →
      ∀ u < E.s, M (E.TS + (E.s + 1) + u) < 2 ^ w) :
    ∃ o st' c, Runs w p ω (drawU bR bM) st o st' c ∧
      (∃ x, RunI w E.RG st.mem x st'.mem ∧ (∀ cl, x.2.1 cl = []) ∧
        o.value = (Finset.range E.s).sup (tvOf st'.mem E.TS (E.s + 1) 1 E.INF)) ∧
      c ≤ runCost (E.L.argsS E.Rr E.x0) st.mem + 60 * E.s + 500 := by
  have hw := hwords
  simp only [DWE.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hw
  obtain ⟨ws, wnS, wSA, wIN, wPW, wEXP, wLAB, wLOC, wD, wlθ, wx0, wJ, wINF, wH⟩ := hw
  have h0 : st.regs 0 = E.s := hr 0 (by omega)
  have h1 : st.regs 1 = E.nS := hr 1 (by omega)
  have h10 : st.regs 10 = E.x0 := hr 10 (by omega)
  have h11 : st.regs 11 = E.J := hr 11 (by omega)
  have h12 : st.regs 12 = E.INF := hr 12 (by omega)
  have h13 : st.regs 13 = E.H := hr 13 (by omega)
  have eRr : E.Rr + 2 = E.H + 16 * E.nS + 8 * E.s + 9 + (3 + 4 * E.J + 2 * E.J * (2 * E.nS + E.s + 1)) + 2 := rfl
  rw [eRr] at hEnd
  have hJA : 2 * E.J ≤ 2 * E.J * (2 * E.nS + E.s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  refine runs_start_le ?_
  dsimp only [drawU, layE, aqE, rrE]
  wram_step
  · exact ⟨E.RG, by simp only [DWE.RG, DL.argsS, DWE.L, AP.toDL, DWE.ap, DWE.TS, DWE.Dq, DWE.Aq, DWE.Rr, List.cons.injEq, true_and, and_true]; omega, hpre.2⟩
  intro v1 mem1 pos1 hpost1
  obtain ⟨x, hI, hE⟩ := hpost1 E.RG ⟨by simp only [DWE.RG, DL.argsS, DWE.L, AP.toDL, DWE.ap,
    DWE.TS, DWE.Dq, DWE.Aq, DWE.Rr, List.cons.injEq, true_and, and_true]; omega, hpre.2⟩
  clear hpost1
  have hTS : E.TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  wram_step
  · exact ⟨E.TS, E.s + 1, E.s, 1, E.INF, by simp only [List.cons.injEq, true_and, and_true]; omega,
      by omega, hcells x mem1 hI hE⟩
  intro v2 mem2 pos2 hpost2
  obtain ⟨rfl, hv2⟩ := hpost2
  have hv := hv2 E.TS (E.s + 1) E.s 1 E.INF (by simp only [List.cons.injEq, true_and, and_true]; omega)
  clear hv2
  wram_step
  · exact ⟨x, hI, hE, hv⟩
  · simp only [maxPC, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const, Expr.size_reg,
      Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
    simp only [dijRunC, ghostC, runCost, DL.argsS, DWE.L, AP.toDL, DWE.ap, DWE.Dq, DWE.Aq, DWE.TS,
      DWE.Rr, zero_mul, add_zero]
    omega

/-- The part of `drawP` after `arcP`. The memory holds the graph of `arcP` below `TS` and zeros
from `TS` on. -/
theorem drawT_runs {w : ℕ} {p : Program} {bC bR bM : ℕ} (ω : ℕ → Bool) {E : DWE} {st : State}
    (hr : E.Regs st) (hC : MeetsContract w p bC (pqClearC w))
    (hR : MeetsContract w p bR (dijRunC w)) (hM : MeetsContract w p bM (maxPC w))
    (hwords : ∀ x ∈ E.args, x < 2 ^ w) (hEnd : E.Rr + 2 < 2 ^ w) (hJ1 : 1 ≤ E.J)
    (hIJ : E.INF * E.J + E.J < 2 ^ w) (hx0 : E.x0 < E.s)
    (hsh : E.L.Shape w st.mem (Finset.range E.s)) (hz : ∀ a, E.TS ≤ a → st.mem a = 0)
    (hcells : ∀ M3 x M, (∀ a < E.TS, M3 a = st.mem a) → RunI w E.RG M3 x M →
      (∀ cl, x.2.1 cl = []) → ∀ u < E.s, M (E.TS + (E.s + 1) + u) < 2 ^ w) :
    ∃ o st' c, Runs w p ω (drawT bC bR bM) st o st' c ∧
      ((∃ M3 x, (∀ a < E.TS, M3 a = st.mem a) ∧ RunI w E.RG M3 x st'.mem ∧
        (∀ cl, x.2.1 cl = []) ∧
        o.value = (Finset.range E.s).sup (tvOf st'.mem E.TS (E.s + 1) 1 E.INF)) ∧
      (∀ a, (a < E.TS ∨ E.Rr + 2 ≤ a) → st'.mem a = st.mem a)) ∧
      c ≤ (200 * (Nat.log 2 E.J + 2) + 2000) * (E.Aq + E.s + 1) + 60 * E.s + 150 * E.J + 1000 := by
  have hw := hwords
  simp only [DWE.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hw
  obtain ⟨ws, wnS, wSA, wIN, wPW, wEXP, wLAB, wLOC, wD, wlθ, wx0, wJ, wINF, wH⟩ := hw
  have h0 : st.regs 0 = E.s := hr 0 (by omega)
  have h1 : st.regs 1 = E.nS := hr 1 (by omega)
  have h11 : st.regs 11 = E.J := hr 11 (by omega)
  have h12 : st.regs 12 = E.INF := hr 12 (by omega)
  have h13 : st.regs 13 = E.H := hr 13 (by omega)
  have eRr : E.Rr = E.Dq + (3 + 4 * E.J + 2 * E.J * E.Aq) := rfl
  have eDq : E.Dq = E.H + 16 * E.nS + 8 * E.s + 9 := rfl
  have eAq : E.Aq = 2 * E.nS + E.s + 1 := rfl
  have eTS : E.TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  have hpq : E.Dq + pqSize E.J E.Aq = E.Rr := rfl
  have hJ4 : E.Dq + 3 + 4 * E.J ≤ E.Rr := by rw [eRr]; omega
  refine runs_start_le ?_
  dsimp only [drawT, layE, aqE]
  wram_step
  wram_step
  wram_step
  wram_step
  · refine ⟨E.Dq, E.J, E.Aq, E.INF, by simp only [List.cons.injEq, and_true]; omega, ?_, ?_, ?_,
      hJ1, by omega, hIJ⟩ <;>
    · simp only [Function.update_apply]
      split_ifs <;> omega
  intro v3 mem3 pos3 hpost3
  obtain ⟨hpq3, ht3, hfr3⟩ := hpost3 E.Dq E.J E.Aq E.INF
    (by simp only [List.cons.injEq, and_true]; omega)
    (by simp only [Function.update_apply]; split_ifs <;> omega)
  have hk3 : ∀ a, ¬ pqOut E.Dq E.J a → (a < E.Dq ∨ E.Dq + 3 ≤ a) → mem3 a = st.mem a :=
    fun a h1 h2 => by
      rw [hfr3 a h1]
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | omega
  clear hfr3 hpost3
  have hlow : ∀ a < E.TS, mem3 a = st.mem a := fun a ha =>
    hk3 a (by unfold pqOut; omega) (by omega)
  have hpre : runPre w E.RG (E.L.argsS E.Rr E.x0) mem3 := by
    refine ⟨rfl, le_of_eq hpq, hEnd, DL.Shape.congr E.L hsh hlow, Finset.mem_range.mpr hx0, hpq3,
      fun c hc _ => ht3 c hc, fun v hv => ?_⟩
    have hv' : v < E.s + 1 := hv
    show mem3 (E.TS + v) < 1 ∧ mem3 (E.TS + 2 * (E.s + 1) + v) < 1
    rw [hk3 _ (by unfold pqOut; omega) (by omega), hk3 _ (by unfold pqOut; omega) (by omega),
      hz _ (by show E.TS ≤ E.TS + v; omega), hz _ (by show E.TS ≤ E.TS + 2 * (E.s + 1) + v; omega)]
    exact ⟨by decide, by decide⟩
  obtain ⟨o, st', c, hrun, ⟨x, hI, hE, hv⟩, hc⟩ :=
    drawU_runs (bR := bR) (bM := bM) ω (st := State.mk mem3 (Function.update st.regs 29 v3) pos3)
      (hr.upd (by omega) _ _ _) hR hM hwords hEnd hJ1 hpre
      (fun x M hI hE => hcells mem3 x M hlow hI hE)
  have hbud := DL.Shape.congr E.L hsh hlow |>.budget
  have hns := DL.nodeSum_eq (DL.Shape.congr E.L hsh hlow)
  refine ⟨o, st', c, hrun, ⟨⟨mem3, x, hlow, hI, hE, hv⟩, fun a ha => ?_⟩, ?_⟩
  · have hk := hI.2.2.2.2.2.2.2.2 a (by
      unfold DL.KeepS
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr ⟨by show E.Dq + pqSize E.J E.Aq ≤ a; omega, by show a ≠ E.Rr; omega,
        by show a ≠ E.Rr + 1; omega⟩))
    rw [hk]
    exact hk3 a (by unfold pqOut; omega) (by omega)
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons,
      argsSize_nil, pqClearC, List.getD_cons_zero, List.getD_cons_succ]
    have hrc : runCost (E.L.argsS E.Rr E.x0) mem3 =
        (200 * (Nat.log 2 E.J + 2) + 2000) * (E.L.nodeSum mem3 + 1) := rfl
    have hle : E.L.nodeSum mem3 ≤ E.Aq + E.s := by
      rw [hns, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have : E.L.A = E.Aq := rfl
      omega
    have := Nat.mul_le_mul_left (200 * (Nat.log 2 E.J + 2) + 2000)
      (show E.L.nodeSum mem3 + 1 ≤ E.Aq + E.s + 1 by omega)
    dsimp only at hc
    omega

set_option maxHeartbeats 4000000 in
theorem drawP_spec {w : ℕ} {p : Program} {b bA bC bR bM : ℕ} (hp : p.HasAt b [drawP bA bC bR bM])
    (hA : MeetsContract w p bA (arcPC w)) (hC : MeetsContract w p bC (pqClearC w))
    (hR : MeetsContract w p bR (dijRunC w)) (hM : MeetsContract w p bM (maxPC w)) :
    MeetsContract w p b (drawC w) := by
  have hproc : p.procs[b]? = some (drawP bA bC bR bM) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro g args mem pos hwords hpre
  obtain ⟨E, rfl, hMem, hOk, hAP, hD, hINF, hJ, hJ1, hx0, hx0s, hZ, hEnd, hIJ, hID⟩ := hpre
  have hw := hwords
  simp only [DWE.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hw
  obtain ⟨ws, wnS, wSA, wIN, wPW, wEXP, wLAB, wLOC, wD, wlθ, wx0, wJ, wINF, wH⟩ := hw
  have hEnd' : E.H + 16 * E.nS + 8 * E.s + 9 + (3 + 4 * E.J + 2 * E.J * (2 * E.nS + E.s + 1)) + 2
      < 2 ^ w := hEnd
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
  have eRr : E.Rr = E.Dq + (3 + 4 * E.J + 2 * E.J * E.Aq) := rfl
  wram_step
  · exact ⟨E.ap, g.m, g.n, g.NL, by simp only [AP.args, DWE.ap, List.cons.injEq, true_and, and_true]; omega, hAP⟩
  intro v1 mem1 pos1 hpost1
  have hp1 : (arcPC w).post E.ap.args mem v1 mem1 := fun A' hA' => by
    have := hpost1 A' (by rw [← hA']; simp only [AP.args, DWE.ap, List.cons.injEq, true_and, and_true]; omega)
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
  rw [hRG] at hI
  refine ⟨o, st', c, hrun, ⟨hv.trans (Rec.draw_result hp1 hMem hOk hD hINF
    (DL.g_congr E.L hsh hlow) hI hE), fun E' hE' a ha => ?_⟩, ?_⟩
  · have e := DWE.eq_of_args hE'
    rw [e] at ha
    have hdE : drawEnd E = E.Rr + 2 := rfl
    rw [hfr a (by omega)]
    exact hfr1 a (by simp only [DWE.ap]; omega)
  · simp only [drawCost, arcPC, DWE.args, AP.args, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil]
    have key : (200 * (Nat.log 2 E.J + 2) + 2000) * (E.Aq + E.s + 1) + 1000 * (2 * E.nS + 2 * E.s + 2)
        = (200 * (Nat.log 2 E.J + 2) + 3000) * (2 * E.nS + 2 * E.s + 2) := by
      rw [eAq]; ring
    omega

end MinCostFlow.LowStretch
