module

public import MinCostFlow.LowStretch.ProgDijRun

/-!
# Running Dijkstra to the end from any state

`drLoop` calls `dijStep` until the queue is empty, like `dijLoop`, but it reads the arguments of
`dijStep` from registers `0` to `14` and keeps its result in register `33`, so it can run inside
a procedure with more arguments. Registers other than `33` do not change. It starts from any
state of Dijkstra in memory (`RunI`) and ends with an empty queue (`drLoop_spec`). Its cost is
that of the potential, as for `dijLoop`. The petal search uses it to empty the queue after a
petal.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The loop: `dijStep` while its last result is not `0`. -/
def drLoop (bStep : ℕ) : Stmt :=
  .loop (.reg 33) (.call 33 bStep [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14])

section Loop

variable {w : ℕ} {G : RunG} {mem0 : ℕ → ℕ}

/-- The invariant of `drLoop`: registers `0` to `14` hold the arguments of `dijStep` and
register `34` holds `v0`. -/
def DInv (w : ℕ) (G : RunG) (mem0 : ℕ → ℕ) (v0 : ℕ) : Option RunX → State → Prop
  | some x, st => (∀ r < 15, st.regs r = (G.L.argsR G.R).getD r 0) ∧ st.regs 34 = v0 ∧
      st.regs 33 ≠ 0 ∧ RunI w G mem0 x st.mem
  | none, st => (∀ r < 15, st.regs r = (G.L.argsR G.R).getD r 0) ∧ st.regs 34 = v0 ∧
      st.regs 33 = 0 ∧ ∃ x, RunI w G mem0 x st.mem ∧ ∀ c, x.2.1 c = []

theorem dr_args {st : State} (hR : ∀ r < 15, st.regs r = (G.L.argsR G.R).getD r 0) :
    evalArgs w st [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
      .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] = some (G.L.argsR G.R) := by
  simp only [evalArgs, Expr.eval, hR 0 (by norm_num), hR 1 (by norm_num), hR 2 (by norm_num),
    hR 3 (by norm_num), hR 4 (by norm_num), hR 5 (by norm_num), hR 6 (by norm_num),
    hR 7 (by norm_num), hR 8 (by norm_num), hR 9 (by norm_num), hR 10 (by norm_num),
    hR 11 (by norm_num), hR 12 (by norm_num), hR 13 (by norm_num), hR 14 (by norm_num)]
  rfl

theorem dr_upd {st : State} {v : ℕ} (hR : ∀ r < 15, st.regs r = (G.L.argsR G.R).getD r 0) :
    ∀ r < 15, Function.update st.regs 33 v r = (G.L.argsR G.R).getD r 0 :=
  fun r hr => by rw [Function.update_of_ne (by omega), hR r hr]

/-- **The loop.** -/
theorem drLoop_spec {p : Program} {bStep : ℕ} (hStep : MeetsContract w p bStep (dijStepC w))
    (hR : G.L.D + pqSize G.L.J G.L.A ≤ G.R) (hR2 : G.R + 2 < 2 ^ w)
    (hwords : ∀ x ∈ G.L.argsR G.R, x < 2 ^ w) (v0 : ℕ) (x0 : Option RunX) :
    Triple w p (DInv w G mem0 v0 x0) (drLoop bStep) (normalPost (DInv w G mem0 v0 none))
      (fun _ => lrem G mem0 x0) := by
  refine Triple.loop_inv (lm G mem0) (lrem G mem0) (condVal := fun st => st.regs 33) ?_ ?_ ?_ x0
  · intro a st _
    rfl
  · intro a st hI h0
    cases a with
    | none => exact ⟨hI, by simp [Expr.size, lrem]⟩
    | some x => exact absurd h0 hI.2.2.1
  · intro a st hI hne
    cases a with
    | none => exact absurd hI.2.2.1 hne
    | some x =>
      obtain ⟨hregs, h34, -, hx⟩ := hI
      refine ⟨dijCost (G.L.argsR G.R) st.mem + 60, ?_⟩
      intro st' ω hst
      subst hst
      refine runs_start_le (runs_call_le (k := 0) hStep (dr_args hregs) hwords
        ⟨stepG G x, hx.stepPre hR hR2⟩ fun v mem' pos' hpost => ?_)
      have hp := hpost (stepG G x) (hx.stepPre hR hR2)
      have hS := stCost_le_dijCost (L := G.L) (R := G.R) (mem := st'.mem)
      have hS5 : 500 ≤ stCost G.L.J := by unfold stCost; omega
      have h34' : Function.update st'.regs 33 v 34 = v0 := by
        rw [Function.update_of_ne (by omega)]; exact h34
      refine ⟨?_, by simp only [dijStepC, ghostC, argsSize_cons, argsSize_nil, Expr.size_reg]; omega⟩
      by_cases hv : v = 0
      · obtain ⟨hx', hall, hc⟩ := hx.step0 hv hp
        refine ⟨none, ⟨dr_upd hregs, h34', by simp [hv], x, hx', hall⟩, by simp [lm], ?_⟩
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
        refine ⟨some x', ⟨dr_upd hregs, h34', by simp [hv], hx'⟩, by simp only [lm]; omega, ?_⟩
        simp only [lrem, Expr.size_reg]
        exact loop_cost_le _ _ _ _ hpot hS5 hS

end Loop

end MinCostFlow.LowStretch
