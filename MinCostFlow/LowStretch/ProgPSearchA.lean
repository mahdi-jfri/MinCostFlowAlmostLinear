module

public import MinCostFlow.LowStretch.ProgPSearch
public import MinCostFlow.LowStretch.ProgPLoopA
public import MinCostFlow.LowStretch.ProgPQClear

/-!
# The petal search procedure, with an amortized cost

`psrchA` is the petal search of `psrch` with a cheaper end. Instead of running Dijkstra to the
end, it empties the class queues with `pqClear`, which costs `O(J)`. Its cost is then bounded
by the drop of the measure `μ` from the first state to the stopped state, plus `O(J + log J)`.
This bound holds for each bit stream, as a run (`psrchA_runs`), and is what the loop over the
petals of a cluster needs: the unsettled nodes of one search are the nodes of the next one, so
the drops add up to the measure of the first search.

The procedure has three parts: `psPre` (start of Dijkstra at `H[0]` and the cells of the
search), `psLoop` and `psPost` (empty the queues and return `r + 2`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The start of the search: as in `psrch`, up to the loop. -/
def psPre (bPush : ℕ) : Stmt :=
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
  (.assign 32 (.const 1)))))))))))))

/-- The end of the search: keep the value, empty the queues, return the value. -/
def psPost (bClr : ℕ) : Stmt :=
  .seq (.assign 34 (.reg 32))
  (.seq (.call 33 bClr [.reg 0, .reg 1, .reg 3])
  (.ret (.reg 34)))

/-- `psrchA`. Procedures `bPush`, `bPS` and `bClr` are `pqPush`, `pstep` and `pqClear`. -/
def psrchA (bPush bPS bClr : ℕ) : Stmt := .seq (psPre bPush) (.seq (psLoop bPS) (psPost bClr))

theorem psrchA_noRand (bPush bPS bClr : ℕ) : (psrchA bPush bPS bClr).NoRand := by
  simp [psrchA, psPre, psPost, psLoop, Stmt.NoRand]

namespace SC

open Classical in
/-- What the search found: the stopped state `a` in the memory `memL`, and a radius `v - 2` that
passed both tests in bucket `a.q`, with the petal at `v - 2` the settled part of `a`. -/
def SFound (w : ℕ) (C : SC) (a : SG) (memL : ℕ → ℕ) (v : ℕ) : Prop :=
  C.Inv w a memL ∧ 2 ≤ v ∧
    C.c.cost C.G C.P C.Y (C.pd.withR (v - 2)) * C.c.sq C.G C.P a.q ≤
      8 * C.c.vol C.G C.P C.Y (C.pd.withR (v - 2)) ∧
    C.c.vol C.G C.P C.Y (C.pd.withR (v - 2)) ≤ C.c.T C.G C.P a.q ∧
    C.c.carve C.G C.Y (C.pd.withR (v - 2)) = C.Y.filter (fun x => a.d.sett (C.sv x)) ∧
    a.d.L ≤ v - 2 ∧ v - 2 ≤ C.Rm ∧ 1 ≤ a.q ∧ a.q ≤ C.X.Lb ∧
    C.X.lo + (a.q - 1) * C.X.bw ≤ v - 2 ∧ v - 2 ≤ C.X.lo + a.q * C.X.bw ∧
    v - 2 < memL (C.L.D + 4) / C.L.J

/-- The memory `mem'` after the queues of `memL` are emptied. -/
def SClr (C : SC) (memL mem' : ℕ → ℕ) : Prop :=
  PQRep mem' C.L.D C.L.J C.L.A C.L.INF (fun _ => []) ∧ (∀ c < C.L.J, mem' (pqT C.L.D C.L.J c) = 0) ∧
    ∀ x, ¬ pqOut C.L.D C.L.J x → mem' x = memL x

variable {C : SC} {w : ℕ}

/-- The last call of `pstep` costs `400`: it made a test, and the test passed. -/
theorem Inv.last_cost (h : C.Ok w) {a : SG} {mem mem' : ℕ → ℕ} (hI : C.Inv w a mem) {v : ℕ}
    (hp : (C.Xf a).Post mem w v mem') (hv : v ≠ 1) : pstepCost (C.Xf a).args mem = 400 := by
  by_cases hv0 : v = 0
  · subst hv0; exact (hI.not_zero h hp).elim
  rcases hp with ⟨-, hTB, -, hP, -⟩ | ⟨h1, -⟩ | ⟨-, mem1, v1, -, hc⟩
  · exact (C.Xf a).cost_400 mem ⟨hTB, Or.inr hP⟩
  · omega
  · rcases hc with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega

end SC

/-- The cost of `psPre`. -/
def psPreCost (J : ℕ) : ℕ := 50 * (Nat.log 2 J + 2) + 500

set_option maxHeartbeats 4000000 in
/-- **The start of the search** reaches the first state `a0` of the loop. -/
theorem psPre_triple {w : ℕ} {p : Program} {bPush : ℕ} (hPush : MeetsContract w p bPush (pqPushC w))
    {C : SC} {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} (hwords : ∀ x ∈ args, x < 2 ^ w)
    (hpre : SC.SPre w C args mem) :
    Triple w p (fun st => st = startState args mem pos) (psPre bPush)
      (normalPost (PLA (w := w) C.X.args C.Xf (C.Inv w) C.μ (.inl C.a0)))
      (fun _ => psPreCost C.L.J) := by
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
  dsimp only [psPre, PSG.args, DL.argsR, List.cons_append, List.nil_append]
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
    have hI := hIall mem1 hpq1 htails hfr
    wram_step
    · refine ⟨fun r hr => ?_, by simp, hI⟩
      simp only [startState, PSG.args, DL.argsR, List.cons_append, List.nil_append] at hr ⊢
      (try simp only [Function.update_apply])
      interval_cases r <;> rfl
    · simp only [pqPushC, psPreCost, List.getD_cons_succ, List.getD_cons_zero, SC.L] at *
      wram_cost

/-- **The end of the search** empties the queues and returns the value of register `32`. -/
theorem psPost_runs {w : ℕ} {p : Program} {bClr : ℕ} (hClr : MeetsContract w p bClr (pqClearC w))
    {C : SC} {a : SG} {memL : ℕ → ℕ} (hI : C.Inv w a memL) (st : State)
    (hwA : ∀ x ∈ C.X.args, x < 2 ^ w)
    (hreg : ∀ i < 32, st.regs i = C.X.args.getD i 0) (hm : st.mem = memL) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (psPost bClr) st o st' c ∧
      (o = .returned (st.regs 32) ∧ C.SClr memL st'.mem) ∧ c ≤ 150 * C.L.J + 60 := by
  have r0 : st.regs 0 = C.L.D := hreg 0 (by omega)
  have r1 : st.regs 1 = C.L.J := hreg 1 (by omega)
  have r3 : st.regs 3 = C.L.INF := hreg 3 (by omega)
  have hpq := hI.rep.pq
  obtain ⟨hf1, hf2, -⟩ := hI.shape.fits
  subst hm
  refine runs_start_le ?_
  dsimp only [psPost]
  have wD : C.L.D < 2 ^ w := hwA _ (by simp [PSG.args, DL.argsR, SC.L])
  have wJ : C.L.J < 2 ^ w := hwA _ (by simp [PSG.args, DL.argsR, SC.L])
  have wI : C.L.INF < 2 ^ w := hwA _ (by simp [PSG.args, DL.argsR, SC.L])
  wram_step
  wram_step
  all_goals first
    | (intro v hv
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
       rcases hv with rfl | rfl | rfl <;> assumption)
    | exact ⟨C.L.D, C.L.J, C.L.A, C.L.INF, by simp [r0, r1, r3], hpq.hJ, hpq.hA, hpq.hINF,
        hpq.J_pos, hf1, hf2⟩
    | (intro v mem' pos' hpost
       obtain ⟨c1, c2, c3⟩ := hpost C.L.D C.L.J C.L.A C.L.INF (by simp [r0, r1, r3]) hpq.hA
       wram_step
       · exact ⟨by simp, c1, c2, c3⟩
       · simp only [pqClearC, List.getD_cons_succ, List.getD_cons_zero, r1] at *
         wram_cost)

/-- **The petal search, amortized.** For every bit stream, the search runs and finds a radius
in the stopped state `a`. Its cost plus the measure of `a` is at most the measure of the first
state plus `O(J + log J)`. -/
theorem psrchA_runs {w : ℕ} {p : Program} {bPush bPS bClr : ℕ}
    (hPush : MeetsContract w p bPush (pqPushC w)) (hPS : MeetsContract w p bPS (pstepC w))
    (hClr : MeetsContract w p bClr (pqClearC w)) {C : SC} {args : List ℕ} {mem : ℕ → ℕ}
    (pos : ℕ) (ω : ℕ → Bool) (hwords : ∀ x ∈ args, x < 2 ^ w) (hpre : SC.SPre w C args mem) :
    ∃ o st' c, Runs w p ω (psrchA bPush bPS bClr) (startState args mem pos) o st' c ∧
      ∃ a memL, C.SFound w a memL o.value ∧ C.SClr memL st'.mem ∧
        c + C.μ a ≤ C.μ C.a0 + psPreCost C.L.J + 150 * C.L.J + 600 := by
  have h := hpre.2.2.1
  have hargs : args = C.X.args ++ [C.X.G.s] := hpre.1
  have hwA : ∀ x ∈ C.X.args, x < 2 ^ w := fun x hx => hwords x (by
    rw [hargs]; exact List.mem_append_left _ hx)
  have hw1 : 1 < 2 ^ w := by
    have := hpre.2.2.2.1.fits.2.2
    omega
  obtain ⟨o1, st1, c1, hr1, hq1, hc1⟩ :=
    psPre_triple (pos := pos) hPush hwords hpre (startState args mem pos) ω rfl
  cases o1 with
  | returned u => exact hq1.elim
  | normal =>
  obtain ⟨o2, st2, c2, hr2, r, ⟨rfl, hF⟩, hc2⟩ := psLoop_amort C.X.args C.Xf (C.Inv w) C.μ hPS hw1
    (args_len _) hwA (fun _ => rfl) (fun _ _ hI => hI.pre h) (fun _ _ hI => hI.pay h)
    (fun _ _ _ hI hp => by
      obtain ⟨a', h1, h2, -⟩ := hI.step h hp
      exact ⟨a', h1, h2⟩) ω C.a0 st1 hq1
  obtain ⟨hreg, hv1, a, memL, hIa, hpost, hra⟩ := hF
  obtain ⟨hm, hvr, t1, t2, hcv, f1, f2, f3, f4, f5, f6, f7⟩ := hIa.found h hpost hv1
  have hlast := hIa.last_cost h hpost hv1
  have hkk : C.kq memL ≤ memL (C.L.D + 4) / C.L.J := min_le_left _ _
  obtain ⟨o3, st3, c3, hr3, ⟨rfl, hclr⟩, hc3⟩ := psPost_runs hClr hIa st2 hwA hreg hm ω
  refine ⟨_, st3, c1 + (c2 + c3 + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + c3 + 1, hr1,
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, c3, hr2, hr3, rfl⟩), rfl⟩), a, memL, ?_, hclr, ?_⟩
  · simp only [Outcome.value, hvr, SC.SFound, Nat.add_sub_cancel]
    exact ⟨hIa, by omega, t1, t2, hcv, f1, f2, f3, f4, f5, f6, by omega⟩
  · change pstepCost C.X.args memL = 400 at hlast
    change c1 ≤ psPreCost C.L.J at hc1
    omega

end MinCostFlow.LowStretch
