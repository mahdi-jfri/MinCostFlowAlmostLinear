module

public import MinCostFlow.LowStretch.ProgPSearchA
public import MinCostFlow.LowStretch.ProgPStep
public import MinCostFlow.LowStretch.ProgDijStep
public import MinCostFlow.LowStretch.ProgRelax
public import MinCostFlow.LowStretch.ProgPQPop
public import MinCostFlow.LowStretch.ProgTT
public import MinCostFlow.LowStretch.ProgPSum
public import MinCostFlow.LowStretch.ProgPTest
public import MinCostFlow.LowStretch.ProgPFin
public import MinCostFlow.LowStretch.ProgClusterPortal
public import MinCostFlow.LowStretch.ProgClusterPetalP
public import MinCostFlow.LowStretch.ProgCopy
public import MinCostFlow.LowStretch.ProgPQClear
public import MinCostFlow.LowStretch.ProgPQ

/-!
# The procedures of the petals

`petalProcs b` is the list of the `14` procedures that one petal uses, from index `b` on:

| index | procedure | calls |
|---|---|---|
| `b` | the search `psrchA` | `b + 1`, `b + 2`, `b + 3` |
| `b + 1` | `pqPush` | `b + 4` |
| `b + 2` | the step `pstep` | `b + 5`, `b + 6`, `b + 7` |
| `b + 3` | `pqClear` | |
| `b + 4` | `ttUpdate` | |
| `b + 5` | `dijStep` | `b + 8`, `b + 9` |
| `b + 6` | `psum` | |
| `b + 7` | `ptest` | |
| `b + 8` | `pqPop` | `b + 4` |
| `b + 9` | `relaxAll` | `b + 1` |
| `b + 10` | `pfin` | |
| `b + 11` | `portP` | |
| `b + 12` | one petal, `petalP` | `b`, `b + 10`, `b + 11` |
| `b + 13` | the copy `cpBody` | |

`petalProcs_meets` gives the contracts of the procedures that the node part calls, from the
contracts of each procedure on its own (`pqPush_spec`, `pstep_spec` and the others).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The procedures of the petals, from index `b` on. -/
def petalProcs (b : ℕ) : List Stmt :=
  [psrchA (b + 1) (b + 2) (b + 3), pqPush (b + 4), pstep (b + 5) (b + 6) (b + 7), pqClear,
    ttUpdate, dijStep (b + 8) (b + 9), psum, ptest, pqPop (b + 4), relaxAll (b + 1), pfin, portP,
    petalP b (b + 10) (b + 11), cpBody]

theorem petalProcs_length (b : ℕ) : (petalProcs b).length = 14 := rfl

/-- One procedure of a list placed at `b` is at its own index. -/
theorem hasAt_one {p : Program} {b : ℕ} {l : List Stmt} (h : p.HasAt b l) (i : ℕ)
    (hi : i < l.length) : p.HasAt (b + i) [l[i]] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  simpa using h i hi

/-- **The contracts of the petal procedures.** -/
theorem petalProcs_meets {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (petalProcs b)) :
    p.HasAt b [psrchA (b + 1) (b + 2) (b + 3)] ∧
      MeetsContract w p (b + 1) (pqPushC w) ∧ MeetsContract w p (b + 2) (pstepC w) ∧
      MeetsContract w p (b + 3) (pqClearC w) ∧ MeetsContract w p (b + 10) (pfinC w) ∧
      MeetsContract w p (b + 11) (portC w) ∧
      p.procs[b + 12]? = some (petalP b (b + 10) (b + 11)) ∧
      (1 < 2 ^ w → MeetsContract w p (b + 13) (cpC w)) := by
  have h : ∀ i (hi : i < (petalProcs b).length), p.HasAt (b + i) [(petalProcs b)[i]] :=
    hasAt_one hp
  have L := petalProcs_length b
  have hTT : MeetsContract w p (b + 4) (ttUpdateC w) := ttUpdate_spec (h 4 (by simp [L]))
  have hPush : MeetsContract w p (b + 1) (pqPushC w) := pqPush_spec (h 1 (by simp [L])) hTT
  have hPop : MeetsContract w p (b + 8) (pqPopC w) := pqPop_spec (h 8 (by simp [L])) hTT
  have hRel : MeetsContract w p (b + 9) (relaxAllC w) := relaxAll_spec (h 9 (by simp [L])) hPush
  have hStep : MeetsContract w p (b + 5) (dijStepC w) :=
    dijStep_spec (h 5 (by simp [L])) hPop hRel
  have hPS : MeetsContract w p (b + 2) (pstepC w) :=
    pstep_spec (h 2 (by simp [L])) hStep (psum_spec (h 6 (by simp [L])))
      (ptest_spec (h 7 (by simp [L])))
  refine ⟨Nat.add_zero b ▸ h 0 (by simp [L]), hPush, hPS, pqClear_spec (h 3 (by simp [L])),
    pfin_spec (h 10 (by simp [L])), portP_spec (h 11 (by simp [L])), ?_,
    fun hw => cp_meetsContract hw (h 13 (by simp [L]))⟩
  exact h 12 (by simp [L]) 0 (by simp)

/-- The step of Dijkstra at `b + 5`, which the first run of Dijkstra of a cluster (`dijRun`) also
calls. -/
theorem petalProcs_dijStep {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (petalProcs b)) :
    MeetsContract w p (b + 5) (dijStepC w) := by
  have h : ∀ i (hi : i < (petalProcs b).length), p.HasAt (b + i) [(petalProcs b)[i]] :=
    hasAt_one hp
  have L := petalProcs_length b
  have hTT : MeetsContract w p (b + 4) (ttUpdateC w) := ttUpdate_spec (h 4 (by simp [L]))
  exact dijStep_spec (h 5 (by simp [L])) (pqPop_spec (h 8 (by simp [L])) hTT)
    (relaxAll_spec (h 9 (by simp [L])) (pqPush_spec (h 1 (by simp [L])) hTT))

end MinCostFlow.LowStretch
