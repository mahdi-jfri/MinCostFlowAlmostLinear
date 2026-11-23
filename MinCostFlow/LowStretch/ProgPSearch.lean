module

public import MinCostFlow.LowStretch.PSearchInit
public import MinCostFlow.LowStretch.ProgDrain

/-!
# The petal search procedure

`psrch` runs one petal search. Its arguments are those of `pstep` and the highway node `H[0]`.
It starts Dijkstra at `H[0]`, sets the cells of the search (bucket `1`, no settled node, pointer
at `H[0]`, last key `0`, sums `0`) and calls `pstep` until it returns a value other than `1`
(`psLoop`). The caller has turned on the slot of `H[0]` and turned off the other slots.

When the loop stops, some test passed, at the tested radius `r` of the current bucket, and the
petal at `r` is the settled part. Then `psrch` runs Dijkstra to the end (`drLoop`), so that the
queue is empty for the next run, and returns `r + 2` (`psrch_spec`). The cells of the search
(the settled list, the pointer, the sums) and the graph are not touched by the last run. The
cost is the measure `μ` of the first state, twice the potential of the first state for the last
run, and a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `psrch`. Procedures `bPush`, `bStep` and `bPS` are `pqPush`, `dijStep` and `pstep`.
Register `32` holds `H[0]`. -/
def psrch (bPush bStep bPS : ℕ) : Stmt :=
  .seq (.store (.bin .add (.reg 11) (.reg 32)) (.reg 13))
  (.seq (.store (.bin .add (.bin .add (.reg 11) (.reg 12)) (.reg 32)) (.const 0))
  (.seq (.call 33 bPush [.reg 0, .reg 1, .reg 2, .const 0, .const 0, .reg 32])
  (.seq (.store (.reg 31) (.const 1))
  (.seq (.store (.bin .add (.reg 31) (.const 1)) (.const 0))
  (.seq (.store (.bin .add (.reg 31) (.const 2)) (.reg 32))
  (.seq (.store (.bin .add (.reg 31) (.const 3)) (.const 0))
  (.seq (.store (.reg 19) (.const 0))
  (.seq (.store (.bin .add (.reg 19) (.const 1)) (.const 0))
  (.seq (.store (.bin .add (.reg 19) (.const 2)) (.const 0))
  (.seq (.store (.bin .add (.reg 19) (.const 3)) (.const 0))
  (.seq (.store (.bin .add (.reg 19) (.const 4)) (.const 0))
  (.seq (.assign 32 (.const 1))
  (.seq (psLoop bPS)
  (.seq (.assign 34 (.reg 32))
  (.seq (.assign 33 (.const 1))
  (.seq (drLoop bStep)
  (.ret (.reg 34))))))))))))))))))

theorem psrch_noRand (bPush bStep bPS : ℕ) : (psrch bPush bStep bPS).NoRand := by
  simp [psrch, psLoop, drLoop, Stmt.NoRand]

namespace SC

/-- The precondition of `psrch`: the setting is good, the memory is `mem0`, the queue is empty,
the stamps are below `rs`, and only the slot of `H[0]` is on. -/
def SPre (w : ℕ) (C : SC) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  args = C.X.args ++ [C.X.G.s] ∧ mem = C.mem0 ∧ C.Ok w ∧ C.L.Shape w mem C.X.G.Nodes ∧
    PQRep mem C.L.D C.L.J C.L.A C.L.INF (fun _ => []) ∧ C.L.TZ mem (fun _ => []) ∧
    (∀ v < C.L.NN, mem (C.L.TS + v) < C.L.rs ∧ mem (C.L.TS + 2 * C.L.NN + v) < C.L.rs) ∧
    ∀ i < C.H.length, mem (C.L.HD + C.slot (C.hv i)) = if i = 0 then C.nx 0 else C.X.S

/-- The ghost values of the last run of Dijkstra. -/
def RG (C : SC) : RunG := ⟨C.L, C.X.G.Nodes, C.X.G.s, C.X.G.R⟩

open Classical in
/-- The postcondition of `psrch`: the state `a` of the search when it stopped, in the memory
`memL`; a radius `r = v - 2` that passed both tests in the current bucket, with the petal at `r`
the settled part of `a`; and the memory `mem'` after Dijkstra ran to the end from `memL`. -/
def SPost (w : ℕ) (C : SC) (_ : List ℕ) (_ : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  ∃ a memL x, C.Inv w a memL ∧ 2 ≤ v ∧
    C.c.cost C.G C.P C.Y (C.pd.withR (v - 2)) * C.c.sq C.G C.P a.q ≤
      8 * C.c.vol C.G C.P C.Y (C.pd.withR (v - 2)) ∧
    C.c.vol C.G C.P C.Y (C.pd.withR (v - 2)) ≤ C.c.T C.G C.P a.q ∧
    C.c.carve C.G C.Y (C.pd.withR (v - 2)) = C.Y.filter (fun x => a.d.sett (C.sv x)) ∧
    a.d.L ≤ v - 2 ∧ v - 2 ≤ C.Rm ∧ 1 ≤ a.q ∧ a.q ≤ C.X.Lb ∧
    C.X.lo + (a.q - 1) * C.X.bw ≤ v - 2 ∧ v - 2 ≤ C.X.lo + a.q * C.X.bw ∧
    v - 2 < memL (C.L.D + 4) / C.L.J ∧
    RunI w C.RG memL x mem' ∧ ∀ c, x.2.1 c = []

end SC

/-- The cost of `psrch`: `μ` of the first state, read from the arguments and the memory. -/
def psrchCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  6 * ((100 * (Nat.log 2 (args.getD 1 0) + 2) + 900) *
      (DL.mk (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0)
        (args.getD 5 0) (args.getD 6 0) (args.getD 7 0) (args.getD 8 0) (args.getD 9 0)
        (args.getD 10 0) (args.getD 11 0) (args.getD 12 0) (args.getD 13 0) 0).nodeSum mem +
      (50 * (Nat.log 2 (args.getD 1 0) + 2) + 600)) +
    500 * args.getD 25 0 + 3 * stCost (args.getD 1 0) + 50 * (Nat.log 2 (args.getD 1 0) + 2) +
    2600

/-- The contract of `psrch`. -/
def psrchC (w : ℕ) : Contract := ghostC (SC.SPre w) (SC.SPost w) psrchCost

theorem args_len (X : PSG) : X.args.length = 32 := by simp [PSG.args, DL.argsR]

/-- The memory after the cells of the search are set, from the memory `mem1` after the push. -/
def initM (X : PSG) (mem1 : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update mem1 X.CTL 1)
    (X.CTL + 1) 0) (X.CTL + 2) X.G.s) (X.CTL + 3) 0) X.SUM 0) (X.SUM + 1) 0) (X.SUM + 2) 0)
    (X.SUM + 3) 0) (X.SUM + 4) 0

theorem initM_top (X : PSG) (mem1 : ℕ → ℕ) {x : ℕ} (h : X.CTL + 4 ≤ X.SUM) (hx : X.SUM + 5 ≤ x) :
    initM X mem1 x = mem1 x := by
  simp only [initM, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem initM_facts (X : PSG) (mem1 : ℕ → ℕ) (h : X.CTL + 4 ≤ X.SUM) :
    (∀ x < X.CTL, initM X mem1 x = mem1 x) ∧ initM X mem1 X.CTL = 1 ∧
      initM X mem1 (X.CTL + 1) = 0 ∧ initM X mem1 (X.CTL + 2) = X.G.s ∧
      initM X mem1 (X.CTL + 3) = 0 ∧ ∀ t : Fin 5, initM X mem1 (X.SUM + t) = 0 := by
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, fun t => ?_⟩
  · simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · have := t.isLt
    simp only [initM, Function.update_apply]
    split_ifs <;> first | rfl | omega

/-- **The petal search.** -/
theorem psrch_spec {w : ℕ} {p : Program} {b bPush bStep bPS : ℕ}
    (hp : p.HasAt b [psrch bPush bStep bPS]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hStep : MeetsContract w p bStep (dijStepC w)) (hPS : MeetsContract w p bPS (pstepC w)) :
    MeetsContract w p b (psrchC w) := by
  have hproc : p.procs[b]? = some (psrch bPush bStep bPS) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro C args mem pos hwords hpre
  obtain ⟨rfl, rfl, h, hs, hpq, hz, hS, hsl⟩ := hpre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hsN : C.X.G.s ∈ C.X.G.Nodes := by rw [← h.H0]; exact h.HN 0 h.Hne
  have hsn : C.X.G.s < C.L.NN := ((hs.ok_iff _).mpr hsN).1
  have hJ1 := hpq.J_pos
  have hA1 : 1 ≤ C.L.A := by have := hs.budget; omega
  have hINF := hs.INF_pos
  have hR := h.hR
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have wSL := h.wSL
  have hfit := hs.fits
  obtain ⟨hf1, -, hf3⟩ := hfit
  unfold pqSize at hR hf1
  have hw1 : 1 < 2 ^ w := by omega
  have hwA : ∀ x ∈ C.X.args, x < 2 ^ w := fun x hx => hwords x (List.mem_append_left _ hx)
  have hpq' : PQRep (DL.initMem C.L C.mem0 C.X.G.s) C.L.D C.L.J C.L.A C.L.INF (fun _ => []) :=
    DL.PQRep.congr hpq fun a ha _ => by
      unfold DL.initMem; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hT0 : DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J 0) = 0 := by
    have := hz 0 hJ1 rfl
    unfold DL.initMem; rw [Function.update_of_ne (by unfold pqT; omega),
      Function.update_of_ne (by unfold pqT; omega)]; exact this
  have hw := hwords
  simp only [PSG.args, DL.argsR, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
  obtain ⟨wD, wJ, wA, wINF, wLO, wHI, wHD, wCS, wCL, wOK, wos, wTS, wNN, wrs, wR, wORD, wAS, wEXP,
    wEs, wSUM, wM, wκ, wnact, wlo, wbw, wLb, wSQ, wP2, wNXT, wSL', wS, wCTL, ws⟩ := hw
  have b1 : C.X.G.L.TS + C.X.G.s < 2 ^ w := by show C.L.TS + C.X.G.s < 2 ^ w; omega
  have b2 : C.X.G.L.TS + C.X.G.L.NN < 2 ^ w := by show C.L.TS + C.L.NN < 2 ^ w; omega
  have b3 : C.X.G.L.TS + C.X.G.L.NN + C.X.G.s < 2 ^ w := by
    show C.L.TS + C.L.NN + C.X.G.s < 2 ^ w; omega
  have hIall : ∀ mem1 : ℕ → ℕ, PQRep mem1 C.L.D C.L.J C.L.A C.L.INF (DL.qs1 C.X.G.s) →
      (∀ c' < C.L.J, mem1 (pqT C.L.D C.L.J c') = if c' = 0 then
        DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J 0) + 1 else
          DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J c')) →
      (∀ a, (a < C.L.D + 3 ∨ C.L.D + pqSize C.L.J C.L.A ≤ a) →
        mem1 a = DL.initMem C.L C.mem0 C.X.G.s a) → C.Inv w C.a0 (initM C.X mem1) := by
    intro mem1 hpq1 htails hfr
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := initM_facts C.X mem1 hSUM
    have hpq2 : PQRep (initM C.X mem1) C.L.D C.L.J C.L.A C.L.INF (DL.qs1 C.X.G.s) :=
      DL.PQRep.congr hpq1 fun a _ ha => m1 a (by unfold pqSize at ha; omega)
    have htails2 : ∀ c' < C.L.J, initM C.X mem1 (pqT C.L.D C.L.J c') = if c' = 0 then
        DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J 0) + 1 else
          DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J c') := fun c' hc' => by
      rw [m1 _ (by unfold pqT; omega)]; exact htails c' hc'
    exact C.init_inv h hs hS hz hsl hpq2 htails2
      (fun x hx hc => by rw [m1 x hc]; exact hfr x hx) m2 m3 m4 m5 m6 fun x hx => by
        have := h.hSL
        rw [initM_top C.X mem1 hSUM (by omega), hfr x (Or.inr (by unfold pqSize; omega))]
        unfold DL.initMem
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  wram_enter
  subst hpre
  dsimp only [psrch, PSG.args, DL.argsR, List.cons_append, List.nil_append]
  wram_step
  wram_step
  wram_step
  · exact ⟨C.L.D, C.L.J, C.L.A, C.L.INF, fun _ => [], 0, 0, C.X.G.s, rfl, hpq', hs.fits, hJ1,
      hT0.trans_lt hA1, hINF, by simp⟩
  · intro v mem1 pos1 hpost
    have hpost' := hpost C.L.D C.L.J C.L.A C.L.INF (fun _ => []) 0 0 C.X.G.s rfl hpq'
    change PQRep mem1 C.L.D C.L.J C.L.A C.L.INF (DL.qs1 C.X.G.s) ∧
      (∀ c' < C.L.J, mem1 (pqT C.L.D C.L.J c') = if c' = 0 then
        DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J 0) + 1 else
          DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J c')) ∧
      ∀ a, (a < C.L.D + 3 ∨ C.L.D + pqSize C.L.J C.L.A ≤ a) → mem1 a = DL.initMem C.L C.mem0 C.X.G.s a
      at hpost'
    obtain ⟨hpq1, htails, hfr⟩ := hpost'
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    have hI := hIall mem1 hpq1 htails hfr
    refine runs_seq_triple_le (SC.search_loop h hPS hw1 (args_len _) hwA (C.potA C.a0) (some C.a0))
      ⟨fun r hr => ?_, ?_, ⟨hI, le_rfl⟩⟩ (fun st' hst' => ?_)
    · simp only [startState]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact List.getD_append C.X.args [C.X.G.s] 0 r (by rw [args_len]; exact hr)
    · simp
    · obtain ⟨hreg, hv1, a, memL, ⟨hIa, hpa⟩, hpost⟩ := hst'
      obtain ⟨hm, hvr, t1, t2, hcv, f1, f2, f3, f4, f5, f6, f7⟩ := hIa.found h hpost hv1
      have hpot := DL.pot_d0 hs C.X.G.s hJ1
      have ens : ∀ L : DL, (DL.mk L.D L.J L.A L.INF L.LO L.HI L.HD L.CS L.CL L.OK L.os L.TS L.NN
          L.rs 0).nodeSum C.mem0 = L.nodeSum C.mem0 := fun _ => rfl
      have e0 : C.μ C.a0 = 4 * C.L.pot C.mem0 C.X.G.Nodes (C.L.d0 C.X.G.s) (DL.qs1 C.X.G.s) +
          500 * (C.X.Lb + 1 - 1) + 2 * stCost C.L.J + 2000 := rfl
      have hpa' : C.L.pot memL C.X.G.Nodes a.d a.qs ≤
          C.L.pot C.mem0 C.X.G.Nodes (C.L.d0 C.X.G.s) (DL.qs1 C.X.G.s) := by
        rw [SC.pot_eq_of_deg (hIa.deg h)]; exact hpa
      have hRI : RunI w C.RG memL (a.d, a.qs, a.cur, a.pos) memL :=
        ⟨hIa.shape, hIa.rep, hIa.inv, hIa.done, hIa.cap, hIa.par, hIa.tz, hIa.stamps,
          fun _ _ => rfl⟩
      have hw15 : ∀ x ∈ C.L.argsR C.X.G.R, x < 2 ^ w := fun x hx =>
        hwA x (by simp only [PSG.args]; exact List.mem_append_left _ hx)
      have hkk : C.kq memL ≤ memL (C.L.D + 4) / C.L.J := min_le_left _ _
      wram_step
      wram_step
      refine runs_seq_triple_le (drLoop_spec (G := C.RG) (mem0 := memL) hStep h.hR h.wR2 hw15
        ((C.Xf a).rr memL + 2) (some (a.d, a.qs, a.cur, a.pos)))
        ⟨fun r hr => ?_, ?_, by simp, hm ▸ hRI⟩ (fun st2 hst2 => ?_)
      · show Function.update (Function.update st'.regs 34 ((C.Xf a).rr memL + 2)) 33 1 r = _
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hreg r (by omega)]
        exact List.getD_append _ _ 0 r (by simp [DL.argsR]; omega)
      · show Function.update (Function.update st'.regs 34 ((C.Xf a).rr memL + 2)) 33 1 34 = _
        rw [Function.update_of_ne (by omega), Function.update_self]
      · obtain ⟨-, h34, -, x, hx, hall⟩ := hst2
        wram_step
        · simp only [Outcome.value, h34, Nat.add_sub_cancel]
          exact ⟨a, memL, x, hIa, by omega, t1, t2, hcv, f1, f2, f3, f4, f5, f6, by omega, hx, hall⟩
        · simp only [plrem, lrem, e0, hpot, pqPushC, psrchCost, List.getD_cons_succ,
            List.getD_cons_zero, Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize_cons,
            argsSize_nil, SC.L, ens]
          rw [hpot] at hpa'
          simp only [SC.RG, SC.L] at hpa' ⊢
          generalize Nat.log 2 C.X.G.L.J = B at hpa' ⊢
          generalize C.X.G.L.nodeSum C.mem0 = N at hpa' ⊢
          generalize stCost C.X.G.L.J = S0
          generalize C.X.G.L.pot memL C.X.G.Nodes a.d a.qs = P1 at hpa' ⊢
          omega

end MinCostFlow.LowStretch
