module

public import MinCostFlow.LastLevelProgram.RuntimeImplementation
public import MinCostFlow.MinRatio.ProgramShift
import MinCostFlow.LastLevelProgram.PackedNoRand

/-!
# The last-level program as bodies inside a larger program

The solver of Section 6 (page 26) rebuilds the last-level collection of Definition 5.8
(pages 19–20) from its own program. `packedLastLevelProgram_implements` proves the
implementation for the standalone program `packedLastLevelProgram guest d c`, whose calls name
its own procedures `0, 1, …`. Here we place the same bodies at any base `b` of a larger program,
with every call index raised by `b` (`packedLastLevelBodies`). A shifted body runs exactly as the
original one: it reads and writes the same cells, uses the same registers and has the same cost
(`MinRatio.dsRep_implements_shift`). So every program that holds the shifted bodies at `b`
implements the same contract, with initialization at `b + 15` and readout at `b + 16`
(`packedLastLevelBodies_implements`).

**The representation is chosen before the graph.** It is `lastLevelRepresentation vCap eCap 4 L P`,
a fixed family indexed by the two capacities and by an edge set `E`. It is used at
`E = G.E`. The index cannot be dropped: no single representation implements the contract for
two different vertex capacities, or for all graphs, since the postcondition of the readout
names the capacities and the edge set. The solver
reads `E` from its own abstract state (the last graph of the chain) and the capacities from its
concrete state, as `MinRatio.solverStateRep` does.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- The procedures of the last-level program with every call index raised by `b`. They are
meant for the indices `b, b + 1, …` of a larger program. -/
@[expose] def packedLastLevelBodies (guest : Program) (d c b : ℕ) : List Stmt :=
  MinRatio.shiftProgramProcs b (packedLastLevelProgram guest d c)

/-- Shifting the calls keeps the number of procedures. -/
theorem packedLastLevelBodies_length (guest : Program) (d c b : ℕ) :
    (packedLastLevelBodies guest d c b).length = (packedLastLevelProgram guest d c).procs.length := by
  simp [packedLastLevelBodies, MinRatio.shiftProgramProcs]

/-- The shifted bodies have no `rand` statement, for every guest program. -/
theorem packedLastLevelBodies_noRand (guest : Program) (d c b : ℕ) :
    ∀ s ∈ packedLastLevelBodies guest d c b, s.NoRand :=
  MinRatio.shiftProgramProcs_noRand (packedLastLevelProgram_isDeterministic guest d c)

/-- **The last-level data structure inside a larger program** (Definition 5.8, pages 19–20, as
used by the rebuild of Section 6, page 26). There are one guest program, one word constant and
one tool, chosen before everything else, such that every program `p` that holds
`packedLastLevelBodies guest d c b` at `b` implements the runtime last-level contract for every
connected graph `G` with `G.n ≤ G.m + 1`, at the entries `b + 15` (initialization) and `b + 16`
(readout). The representation `lastLevelRepresentation vCap eCap 4 L P` is a fixed family, used
at the edge set of `G`. The proof moves `packedLastLevelProgram_implements` along the shift. -/
theorem packedLastLevelBodies_implements :
    ∃ (guest : Program) (c : ℕ) (K Cf : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      let C := graphCanonicalConstant K Cf
      let d := ⌈max 1 C⌉₊
      let tool := fixedPointLastLevelTool oracle C
      tool.IsSpec (SparseCore.lastLevelParams (128 * max 1 C)) ∧
      ∀ {p : Program} {b : ℕ}, p.HasAt b (packedLastLevelBodies guest d c b) →
      ∀ {w L vCap eCap : ℕ} (fmt : Format w) (G : MGraph),
        fmt.limbBits = 4 →
        (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) → G.n ≤ G.m+1 →
        let P := (1024*d).size+3*(G.m+1).size
        let multiplier := packedLastLevelMultiplier guest c d K G L
        let alloc := packedRuntimeAllocation G guest C c L vCap eCap
        (lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
          w p (b+15) (fun _ => b+16)
          (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc) := by
  obtain ⟨guest,c,K,Cf,oracle,hSpec,himpl⟩ := packedLastLevelProgram_implements
  refine ⟨guest,c,K,Cf,oracle,hSpec,?_⟩
  intro p b hp w L vCap eCap fmt G hformat hconn hn P multiplier alloc
  have h := himpl (L := L) (vCap := vCap) (eCap := eCap) fmt G hformat hconn hn
  rw [hformat] at h
  exact MinRatio.dsRep_implements_shift hp h

end MinCostFlow.LastLevelProgram
