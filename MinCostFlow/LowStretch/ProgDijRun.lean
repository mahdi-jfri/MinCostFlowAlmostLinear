module

public import MinCostFlow.LowStretch.DijInit

/-!
# A full run of Dijkstra

`dijRun (L.argsS R s)` writes the cost `0` of the source `s`, pushes `(0, s)`, and calls `dijStep`
until the queue is empty (`dijRun_spec`). At the end the memory holds a state of Dijkstra with an
empty queue, so `AG.Inv.path` gives the distances from `s`, and the parents lead back to `s`
(`AG.ParInv`). The cost is `O(log J)` for each vertex and each arc of the graph.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arguments of `dijRun`. -/
def DL.argsS (L : DL) (R s : ℕ) : List ℕ :=
  [L.D, L.J, L.A, L.INF, L.LO, L.HI, L.HD, L.CS, L.CL, L.OK, L.os, L.TS, L.NN, L.rs, R, s]

/-- The loop of `dijRun`, with the result of the last step in register `16`. -/
def dijLoop (bStep : ℕ) : Stmt :=
  .loop (.reg 16) (.call 16 bStep [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14])

/-- `dijRun`. Procedure `bPush` is `pqPush` and `bStep` is `dijStep`. -/
def dijRun (bPush bStep : ℕ) : Stmt :=
  .seq (.store (.bin .add (.reg 11) (.reg 15)) (.reg 13))
  (.seq (.store (.bin .add (.bin .add (.reg 11) (.reg 12)) (.reg 15)) (.const 0))
  (.seq (.call 16 bPush [.reg 0, .reg 1, .reg 2, .const 0, .const 0, .reg 15])
  (.seq (.assign 16 (.const 1))
  (.seq (dijLoop bStep)
  (.ret (.const 0))))))

theorem dijRun_noRand (bPush bStep : ℕ) : (dijRun bPush bStep).NoRand := by
  simp [dijRun, dijLoop, Stmt.NoRand]

/-- The ghost values of `dijRun`. -/
structure RunG where
  L : DL
  Nodes : Finset ℕ
  s : ℕ
  R : ℕ

/-- The precondition of `dijRun`: the queue is empty and every stamp is below `rs`. -/
def runPre (w : ℕ) (G : RunG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  args = G.L.argsS G.R G.s ∧ G.L.D + pqSize G.L.J G.L.A ≤ G.R ∧ G.R + 2 < 2 ^ w ∧
    G.L.Shape w mem G.Nodes ∧ G.s ∈ G.Nodes ∧ PQRep mem G.L.D G.L.J G.L.A G.L.INF (fun _ => []) ∧
    G.L.TZ mem (fun _ => []) ∧
    ∀ v < G.L.NN, mem (G.L.TS + v) < G.L.rs ∧ mem (G.L.TS + 2 * G.L.NN + v) < G.L.rs

/-- The ghost state of the loop: the state of Dijkstra, the lists, and the current vertex and
arc. -/
abbrev RunX := DS × (ℕ → List (ℕ × ℕ)) × ℕ × ℕ

/-- The memory holds the state `x` of a run that started at the memory `mem0`. -/
def RunI (w : ℕ) (G : RunG) (mem0 : ℕ → ℕ) (x : RunX) (M : ℕ → ℕ) : Prop :=
  G.L.Shape w M G.Nodes ∧ G.L.Rep M G.Nodes x.1 x.2.1 ∧
    (G.L.g mem0).Inv G.s G.L.INF x.2.2.1 x.2.2.2 x.1 ∧
    (x.1.sett x.2.2.1 → (G.L.g mem0).hi x.2.2.1 ≤ x.2.2.2) ∧
    (∀ c < G.L.J, M (pqT G.L.D G.L.J c) ≤ G.L.setSum mem0 G.Nodes x.1.sett + 1) ∧
    (G.L.g mem0).ParInv G.s G.L.INF x.1 (G.L.par M) (G.L.parc M) ∧ G.L.TZ M x.2.1 ∧
    G.L.Stamps M ∧ ∀ a, G.L.KeepS G.R a → M a = mem0 a

/-- The postcondition of `dijRun`: the memory holds a state with an empty queue. -/
def runPost (w : ℕ) (G : RunG) (_ : List ℕ) (mem : ℕ → ℕ) (_ : ℕ) (mem' : ℕ → ℕ) : Prop :=
  ∃ x, RunI w G mem x mem' ∧ ∀ c, x.2.1 c = []

/-- The cost of `dijRun`: `O(log J)` for each vertex and each arc. -/
def runCost : List ℕ → (ℕ → ℕ) → ℕ
  | [D, J, A, INF, LO, HI, HD, CS, CL, OK, os, TS, NN, rs, _, _], mem =>
    (200 * (Nat.log 2 J + 2) + 2000) *
      ((DL.mk D J A INF LO HI HD CS CL OK os TS NN rs 0).nodeSum mem + 1)
  | _, _ => 0

/-- The contract of `dijRun`. -/
def dijRunC (w : ℕ) : Contract := ghostC (runPre w) (runPost w) runCost

/-! ### The loop -/

section Loop

variable {w : ℕ} {G : RunG} {mem0 : ℕ → ℕ}

theorem RunI.g_eq {x : RunX} {M : ℕ → ℕ} (h : RunI w G mem0 x M) : G.L.g M = G.L.g mem0 :=
  (DL.g_congr G.L h.1 fun a ha => (h.2.2.2.2.2.2.2.2 a (Or.inl ha)).symm).symm

/-- The ghost values of the step from the state `x`. -/
def stepG (G : RunG) (x : RunX) : StG :=
  ⟨G.L, G.Nodes, G.s, x.2.2.1, x.2.2.2, x.1, x.2.1, G.R⟩

theorem RunI.stepPre {x : RunX} {M : ℕ → ℕ} (h : RunI w G mem0 x M)
    (hR : G.L.D + pqSize G.L.J G.L.A ≤ G.R) (hR2 : G.R + 2 < 2 ^ w) :
    stepPre w (stepG G x) (G.L.argsR G.R) M := by
  have hg := h.g_eq
  obtain ⟨hs, hr, hinv, hdone, hcap, hp, hz, hS, -⟩ := h
  rw [← hg] at hinv hdone hp
  refine ⟨rfl, hR, hR2, hs, hr, hinv, hdone, fun c hc => ?_, hp, hz, hS⟩
  simp only [stepG] at hc ⊢
  rw [DL.setSum_congr hg]
  exact hcap c hc

/-- The keep sets compose. -/
theorem keepS_trans {M M' : ℕ → ℕ} (h : ∀ a, G.L.KeepS G.R a → M a = mem0 a)
    (h' : ∀ a, G.L.KeepS G.R a → M' a = M a) : ∀ a, G.L.KeepS G.R a → M' a = mem0 a :=
  fun a ha => (h' a ha).trans (h a ha)

/-- A step that drops an entry. -/
theorem RunI.step1 {x : RunX} {M M' : ℕ → ℕ} (h : RunI w G mem0 x M)
    (hpost : stepPost w (stepG G x) (G.L.argsR G.R) M 1 M') :
    ∃ x', RunI w G mem0 x' M' ∧
      G.L.pot mem0 G.Nodes x'.1 x'.2.1 + dijCost (G.L.argsR G.R) M ≤ G.L.pot mem0 G.Nodes x.1 x.2.1 := by
  have hg := h.g_eq
  obtain ⟨hs, hr, hinv, hdone, hcap, hp, hz, hS, hk⟩ := h
  rcases hpost with ⟨h0, -⟩ | ⟨-, qs', hs', hr', hinv', hcap', hpot, hk', hp', hz', hS'⟩ | ⟨h2, -⟩
  · omega
  · simp only [stepG] at hs' hr' hinv' hcap' hpot hk' hp' hz' hS'
    rw [hg] at hinv' hp'
    rw [DL.pot_congr hg, DL.pot_congr hg] at hpot
    rw [DL.setSum_congr hg] at hcap'
    exact ⟨({ x.1 with Q := pqAll G.L.J qs' }, qs', x.2.2.1, x.2.2.2),
      ⟨hs', hr', hinv', hdone, hcap', hp', hz', hS', keepS_trans hk hk'⟩, hpot⟩
  · omega

/-- A step that settles a vertex. -/
theorem RunI.step2 {x : RunX} {M M' : ℕ → ℕ} (h : RunI w G mem0 x M)
    (hpost : stepPost w (stepG G x) (G.L.argsR G.R) M 2 M') :
    ∃ x', RunI w G mem0 x' M' ∧
      G.L.pot mem0 G.Nodes x'.1 x'.2.1 + dijCost (G.L.argsR G.R) M ≤ G.L.pot mem0 G.Nodes x.1 x.2.1 := by
  have hg := h.g_eq
  obtain ⟨hs, hr, hinv, hdone, hcap, hp, hz, hS, hk⟩ := h
  rcases hpost with ⟨h0, -⟩ | ⟨h1, -⟩ |
    ⟨-, d', qs', -, -, -, -, hs', hr', hinv', hcap', hpot, hk', hp', hz', hS', -⟩
  · omega
  · omega
  · simp only [stepG] at hs' hr' hinv' hcap' hpot hk' hp' hz' hS'
    rw [hg] at hinv' hp'
    rw [DL.pot_congr hg, DL.pot_congr hg] at hpot
    rw [DL.setSum_congr hg] at hcap'
    exact ⟨(d', qs', M' (G.R + 1), (G.L.g mem0).hi (M' (G.R + 1))),
      ⟨hs', hr', hinv', fun _ => le_rfl, hcap', hp', hz', hS', keepS_trans hk hk'⟩, hpot⟩

/-- A step on an empty queue. -/
theorem RunI.step0 {x : RunX} {M M' : ℕ → ℕ} {v : ℕ} (h : RunI w G mem0 x M) (hv : v = 0)
    (hpost : stepPost w (stepG G x) (G.L.argsR G.R) M v M') :
    RunI w G mem0 x M' ∧ (∀ c, x.2.1 c = []) ∧ dijCost (G.L.argsR G.R) M = stCost G.L.J := by
  rcases hpost with ⟨-, hall, hm⟩ | ⟨h1, -⟩ | ⟨h2, -⟩
  · simp only [stepG] at hall
    refine ⟨hm ▸ h, hall, ?_⟩
    have hr := h.2.1
    have hroot : G.L.INF ≤ M (G.L.D + 4) / G.L.J := by
      by_contra hn
      obtain ⟨e, rest, he, -⟩ := hr.pq.root_spec.1 (by rw [show G.L.D + 3 + 1 = G.L.D + 4 from rfl]; omega)
      rw [hall] at he
      exact List.cons_ne_nil _ _ he.symm
    exact dijCost_empty hroot
  · omega
  · omega

/-- The invariant of the loop. The ghost value is `none` once the last step found the queue
empty. -/
def LInv (w : ℕ) (G : RunG) (mem0 : ℕ → ℕ) : Option RunX → State → Prop
  | some x, st => (∀ r < 16, st.regs r = (G.L.argsS G.R G.s).getD r 0) ∧ st.regs 16 ≠ 0 ∧
      RunI w G mem0 x st.mem
  | none, st => (∀ r < 16, st.regs r = (G.L.argsS G.R G.s).getD r 0) ∧ st.regs 16 = 0 ∧
      ∃ x, RunI w G mem0 x st.mem ∧ ∀ c, x.2.1 c = []

/-- The measure of the loop. -/
noncomputable def lm (G : RunG) (mem0 : ℕ → ℕ) : Option RunX → ℕ
  | some x => G.L.pot mem0 G.Nodes x.1 x.2.1 + 1
  | none => 0

/-- The cost left in the loop. -/
noncomputable def lrem (G : RunG) (mem0 : ℕ → ℕ) : Option RunX → ℕ
  | some x => 2 * G.L.pot mem0 G.Nodes x.1 x.2.1 + stCost G.L.J + 70
  | none => 2

theorem step_args {st : State} (hR : ∀ r < 16, st.regs r = (G.L.argsS G.R G.s).getD r 0) :
    evalArgs w st [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
      .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] = some (G.L.argsR G.R) := by
  simp only [evalArgs, Expr.eval, hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num),
    hR 3 (by norm_num), hR 4 (by norm_num), hR 5 (by norm_num), hR 6 (by norm_num),
    hR 7 (by norm_num), hR 8 (by norm_num), hR 9 (by norm_num), hR 10 (by norm_num),
    hR 11 (by norm_num), hR 12 (by norm_num), hR 13 (by norm_num), hR 14 (by norm_num)]
  rfl

theorem regs_upd16 {st : State} {v : ℕ} (hR : ∀ r < 16, st.regs r = (G.L.argsS G.R G.s).getD r 0) :
    ∀ r < 16, Function.update st.regs 16 v r = (G.L.argsS G.R G.s).getD r 0 :=
  fun r hr => by rw [Function.update_of_ne (by omega), hR r hr]

theorem loop_cost_le (P P' dc S : ℕ) (h : P' + dc ≤ P) (hS : 500 ≤ S) (hdc : S ≤ dc) :
    1 + (dc + 60) + (2 * P' + S + 70) + 1 ≤ 2 * P + S + 70 := by omega

/-- **The loop.** -/
theorem dijLoop_spec {p : Program} {bStep : ℕ} (hStep : MeetsContract w p bStep (dijStepC w))
    (hR : G.L.D + pqSize G.L.J G.L.A ≤ G.R) (hR2 : G.R + 2 < 2 ^ w)
    (hwords : ∀ x ∈ G.L.argsR G.R, x < 2 ^ w) (x0 : Option RunX) :
    Triple w p (LInv w G mem0 x0) (dijLoop bStep) (normalPost (LInv w G mem0 none))
      (fun _ => lrem G mem0 x0) := by
  refine Triple.loop_inv (lm G mem0) (lrem G mem0) (condVal := fun st => st.regs 16) ?_ ?_ ?_ x0
  · intro a st _
    rfl
  · intro a st hI h0
    cases a with
    | none => exact ⟨hI, by simp [Expr.size, lrem]⟩
    | some x => exact absurd h0 hI.2.1
  · intro a st hI hne
    cases a with
    | none => exact absurd hI.2.1 hne
    | some x =>
      obtain ⟨hregs, -, hx⟩ := hI
      refine ⟨dijCost (G.L.argsR G.R) st.mem + 60, ?_⟩
      intro st' ω hst
      subst hst
      refine runs_start_le (runs_call_le (k := 0) hStep (step_args hregs) hwords ⟨stepG G x, hx.stepPre hR hR2⟩
        fun v mem' pos' hpost => ?_)
      have hp := hpost (stepG G x) (hx.stepPre hR hR2)
      have hS := stCost_le_dijCost (L := G.L) (R := G.R) (mem := st'.mem)
      have hS5 : 500 ≤ stCost G.L.J := by unfold stCost; omega
      refine ⟨?_, by simp only [dijStepC, ghostC, argsSize_cons, argsSize_nil, Expr.size_reg]; omega⟩
      by_cases hv : v = 0
      · obtain ⟨hx', hall, hc⟩ := hx.step0 hv hp
        refine ⟨none, ⟨regs_upd16 hregs, by simp [hv], x, hx', hall⟩, by simp [lm], ?_⟩
        simp only [lrem, Expr.size_reg]
        omega
      · have h12 : ∃ x', RunI w G mem0 x' mem' ∧ G.L.pot mem0 G.Nodes x'.1 x'.2.1 +
            dijCost (G.L.argsR G.R) st'.mem ≤ G.L.pot mem0 G.Nodes x.1 x.2.1 := by
          have h12 : v = 1 ∨ v = 2 := by
            rcases hp with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
          rcases h12 with rfl | rfl
          · exact hx.step1 hp
          · exact hx.step2 hp
        obtain ⟨x', hx', hpot⟩ := h12
        refine ⟨some x', ⟨regs_upd16 hregs, by simp [hv], hx'⟩, by simp only [lm]; omega, ?_⟩
        simp only [lrem, Expr.size_reg]
        exact loop_cost_le _ _ _ _ hpot hS5 hS

end Loop

theorem run_cost_le (b S X : ℕ) (hX : X ≤ 50 * (b + 2) + 330) :
    X + (2 * ((100 * (b + 2) + 900) * S + (50 * (b + 2) + 600)) + (50 * (b + 2) + 400) + 70) ≤
      (200 * (b + 2) + 2000) * (S + 1) := by
  nlinarith

/-- **A run of Dijkstra.** -/
theorem dijRun_spec {w : ℕ} {p : Program} {b bPush bStep : ℕ} (hp : p.HasAt b [dijRun bPush bStep])
    (hPush : MeetsContract w p bPush (pqPushC w)) (hStep : MeetsContract w p bStep (dijStepC w)) :
    MeetsContract w p b (dijRunC w) := by
  have hproc : p.procs[b]? = some (dijRun bPush bStep) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro G args mem pos hwords hpre
  obtain ⟨rfl, hR, hR2, hs, hsN, hpq, hz, hS⟩ := hpre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hsn : G.s < G.L.NN := ((hs.ok_iff _).mpr hsN).1
  have hJ1 := hpq.J_pos
  have hw := hwords
  simp only [DL.argsS, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
  obtain ⟨wD, wJ, wA, wINF, wLO, wHI, wHD, wCS, wCL, wOK, wos, wTS, wNN, wrs, wR, ws⟩ := hw
  have hw15 : ∀ x ∈ G.L.argsR G.R, x < 2 ^ w := by
    simp only [DL.argsR, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨wD, wJ, wA, wINF, wLO, wHI, wHD, wCS, wCL, wOK, wos, wTS, wNN, wrs, wR⟩
  have hA1 : 1 ≤ G.L.A := by have := hs.budget; omega
  have hpq' : PQRep (DL.initMem G.L mem G.s) G.L.D G.L.J G.L.A G.L.INF (fun _ => []) :=
    DL.PQRep.congr hpq fun a ha _ => by
      unfold DL.initMem; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hT0 : DL.initMem G.L mem G.s (pqT G.L.D G.L.J 0) = 0 := by
    have := hz 0 hJ1 rfl
    unfold DL.initMem; rw [Function.update_of_ne (by unfold pqT; omega),
      Function.update_of_ne (by unfold pqT; omega)]; exact this
  have hpot := DL.pot_d0 hs G.s hJ1
  have hcost : runCost [G.L.D, G.L.J, G.L.A, G.L.INF, G.L.LO, G.L.HI, G.L.HD, G.L.CS, G.L.CL, G.L.OK,
      G.L.os, G.L.TS, G.L.NN, G.L.rs, G.R, G.s] mem =
      (200 * (Nat.log 2 G.L.J + 2) + 2000) * (G.L.nodeSum mem + 1) := rfl
  have hINF := hs.INF_pos
  wram_enter
  subst hpre
  dsimp only [dijRun, DL.argsS]
  wram_step
  wram_step
  wram_step
  · exact ⟨G.L.D, G.L.J, G.L.A, G.L.INF, fun _ => [], 0, 0, G.s, rfl, hpq', hs.fits, hJ1,
      hT0.trans_lt hA1, hINF, by simp⟩
  · intro v mem1 pos1 hpost
    have hpost' := hpost G.L.D G.L.J G.L.A G.L.INF (fun _ => []) 0 0 G.s rfl hpq'
    change PQRep mem1 G.L.D G.L.J G.L.A G.L.INF (DL.qs1 G.s) ∧
      (∀ c' < G.L.J, mem1 (pqT G.L.D G.L.J c') = if c' = 0 then
        DL.initMem G.L mem G.s (pqT G.L.D G.L.J 0) + 1 else DL.initMem G.L mem G.s (pqT G.L.D G.L.J c')) ∧
      ∀ a, (a < G.L.D + 3 ∨ G.L.D + pqSize G.L.J G.L.A ≤ a) → mem1 a = DL.initMem G.L mem G.s a
      at hpost'
    obtain ⟨hpq1, htails, hfr⟩ := hpost'
    have hM : ∀ a < G.L.D, mem1 a = DL.initMem G.L mem G.s a := fun a ha => hfr a (Or.inl (by omega))
    obtain ⟨hs1, hr1⟩ := DL.init_rep hs hsN hS hpq1 hM
    have hzI : ∀ c < G.L.J, DL.initMem G.L mem G.s (pqT G.L.D G.L.J c) = 0 := fun c hc => by
      have := hz c hc rfl
      unfold DL.initMem
      rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne (by unfold pqT; omega)]
      exact this
    have hI : RunI w G mem (G.L.d0 G.s, DL.qs1 G.s, G.s, 0) mem1 := by
      refine ⟨hs1, hr1, AG.inv_init hINF, fun h => h.elim, fun c hc => ?_, AG.parInv_init _ _, ?_,
        DL.init_stamps l7 hS hM, fun a ha => ?_⟩
      · rw [htails c hc]
        split_ifs with h0
        · subst h0; rw [hzI 0 hJ1]; simp
        · rw [hzI c hc]; simp
      · exact DL.TZ.push (L := G.L) (mem := DL.initMem G.L mem G.s) (e := (0, G.s)) (c := 0)
          (fun c hc _ => hzI c hc) fun c' hc' hne => by rw [htails c' hc', if_neg hne]
      · rcases ha with ha | ⟨ha1, ha2⟩ | ⟨ha1, ha2, ha3⟩
        · rw [hM a (by omega)]; unfold DL.initMem
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · rw [hfr a (Or.inl ha2)]; unfold DL.initMem
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        · rw [hfr a (Or.inr ha1)]; unfold DL.initMem
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    wram_step
    refine runs_seq_triple_le (dijLoop_spec (mem0 := mem) hStep hR hR2 hw15
      (some (G.L.d0 G.s, DL.qs1 G.s, G.s, 0))) ⟨fun r hr => ?_, ?_, hI⟩ (fun st' hst' => ?_)
    · simp only [startState]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rfl
    · simp
    · obtain ⟨-, -, x, hx, hall⟩ := hst'
      wram_step
      · exact ⟨x, hx, hall⟩
      · rw [hcost]
        simp only [lrem, hpot, pqPushC, stCost, List.getD_cons_succ, List.getD_cons_zero,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
        refine le_trans ?_ (run_cost_le (Nat.log 2 G.L.J) (G.L.nodeSum mem) (50 * (Nat.log 2 G.L.J + 2) + 330) le_rfl)
        generalize (100 * (Nat.log 2 G.L.J + 2) + 900) * G.L.nodeSum mem = P
        generalize Nat.log 2 G.L.J = B
        clear * -
        omega

end MinCostFlow.LowStretch
