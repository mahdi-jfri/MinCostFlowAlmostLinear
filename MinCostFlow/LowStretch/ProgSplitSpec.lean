module

public import MinCostFlow.LowStretch.ProgSplitRun
public import MinCostFlow.LowStretch.ProgSplitLab

/-!
# The contract of the split walk

`splitP` meets `splitC`. The precondition holds for a ghost `(T, G, r, x)`: the merge tree, the
graph, the child and the new threshold. The postcondition is `SplitPost` without its cost, for
every ghost that meets the precondition; this is enough since runs are deterministic. The cost
of `splitP` depends on the ghost (it is a sum over the split nodes), so the contract cost is the
least bound over all ghosts that meet the precondition (`splitCost`). The caller gets the bound
of its own ghost from `splitCost_le`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The ghost of `splitP`. -/
structure SPG where
  T : KT
  G : PG
  r : Cl
  x : ℕ

/-- The precondition of `splitP` for the ghost `g`. -/
def splitPre (w : ℕ) (g : SPG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ E : SplitL, args = E.args ∧ SplitPre w g.T g.G g.r g.x E mem

/-- The cost bound of `splitP` for the ghost `g` and the layout `E`. -/
noncomputable def splitBd (g : SPG) (E : SplitL) : ℕ :=
  500 * (E.len0 + 1) + 800 * ∑ u ∈ g.T.splitSet g.G g.r g.x, (g.T.sz g.G (g.T.light g.G u) + 1)

/-- The cost of `splitP`: the least bound over the ghosts and layouts that meet the
precondition (`0` if there is none). -/
noncomputable def splitCost (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  sInf {b | ∃ (g : SPG) (E : SplitL), args = E.args ∧ SplitPre w g.T g.G g.r g.x E mem ∧ b = splitBd g E}

/-- The contract of `splitP`. -/
noncomputable def splitC (w : ℕ) : Contract where
  pre args mem := ∃ g, splitPre w g args mem
  post args mem v mem' := ∀ (g : SPG) (E : SplitL), args = E.args → SplitPre w g.T g.G g.r g.x E mem →
    SplitPost g.T g.G g.r g.x E mem v mem' 0
  cost := splitCost w

/-- The caller's bound on the cost of `splitP`. -/
theorem splitCost_le {w : ℕ} {g : SPG} {E : SplitL} {mem : ℕ → ℕ}
    (h : SplitPre w g.T g.G g.r g.x E mem) : splitCost w E.args mem ≤ splitBd g E :=
  Nat.sInf_le ⟨g, E, rfl, h, rfl⟩

/-- `SplitL.args` determines the layout. -/
theorem SplitL.args_inj {E E' : SplitL} (h : E.args = E'.args) : E = E' := by
  cases E; cases E'
  simp only [SplitL.args, List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rfl

/-- **`splitP` meets `splitC`.** -/
theorem splitP_spec {w : ℕ} {p : Program} {b bF : ℕ} (hp : p.HasAt b [splitP bF])
    (hF : MeetsContract w p bF (fillAtC w)) : MeetsContract w p b (splitC w) := by
  have hproc : p.procs[b]? = some (splitP bF) := hp 0 (by simp)
  intro args mem pos ω _ hpre
  obtain ⟨g0, E0, rfl, P0⟩ := hpre
  obtain ⟨o, st', c, hrun, hpost0, -⟩ := (splitP_runs hF P0 pos ω)
  refine ⟨_, hproc, o, st', c, hrun, fun g E hE P => ?_, ?_⟩
  · obtain rfl := SplitL.args_inj hE
    obtain ⟨o2, st2, c2, hrun2, hpost2⟩ := splitP_runs hF P pos ω
    obtain ⟨rfl, rfl, -⟩ := Runs.det hrun hrun2
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := hpost2
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, Nat.zero_le _⟩
  · have hm := Nat.sInf_mem (s := {b | ∃ (g : SPG) (E : SplitL), E0.args = E.args ∧
      SplitPre w g.T g.G g.r g.x E mem ∧ b = splitBd g E}) ⟨_, g0, E0, rfl, P0, rfl⟩
    obtain ⟨g, E, hE, P, hb⟩ := hm
    obtain rfl := SplitL.args_inj hE
    obtain ⟨o2, st2, c2, hrun2, hpost2⟩ := splitP_runs hF P pos ω
    obtain ⟨-, -, rfl⟩ := Runs.det hrun hrun2
    show c ≤ splitCost w E0.args mem
    rw [show splitCost w E0.args mem = _ from hb]
    exact hpost2.2.2.2.2.2.2.2.2

end MinCostFlow.LowStretch
