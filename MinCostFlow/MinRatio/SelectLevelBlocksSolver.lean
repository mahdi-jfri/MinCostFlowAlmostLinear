module

public import MinCostFlow.MinRatio.SelectLevelBlocks
public import MinCostFlow.MinRatio.WireSelectActiveS
public import MinCostFlow.MinRatio.SolverLevelCapsInv

/-!
# The level blocks on the solver's state (`SelectLevelBlocksSolver`)

`selectLevelMetaAt_of_blocks` (`SelectLevelBlocks.lean`) takes the solver's level graphs of
`j < d`, and the model fact `activeS j = G (j + 1)`, as hypotheses. On the solver's state both are
known:
* the solver's level graphs are those of `SolverLevelCapsInv` (`SolverLevelMetaAt` with the caps
  of `SolverLevelCapsAt`), at the pointers `levelMeta[d + j]`;
* `activeS j = G (j + 1)` holds under `SelectModelInv` (`SelectModelInv.activeS_eq_G_succ`).

* `solverLevelG`: the pointers to the level graphs, read from `levelMeta`. The solver's core
  lengths (`levelMeta[j]`) are not used: they are `C.chainLen ℓ j`, while the keys need
  `C.chainLen ℓ (j + 1)`, which the blocks own.
* `selectMlocOf_sPtr`: the table of the blocks points `S_j` at the graph of level `j + 1`.
* `selectLevelMetaAt_of_solver`: `SelectLevelMetaAt` from the table, the blocks,
  `SolverLevelCapsInv`, `SelectModelInv` and `SelectPotInv`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-- The solver's graph of level `j`, at `levelMeta[d + j]` (`SolverLevelMetaAt`). -/
def solverLevelG {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) (j : ℕ) : ℕ :=
  mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)

/-- The table of the blocks points `S_j` at the graph of level `j + 1`, at every interior level
`j < B.d`. -/
theorem selectMlocOf_sPtr (B : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (pLast : ℕ)
    {j : ℕ} (hj : j < B.d) :
    (selectMlocOf B metaBase solverG pLast).sPtr j =
      (selectMlocOf B metaBase solverG pLast).GPtr (j + 1) := by
  simp only [selectMlocOf, hj, ↓reduceIte]

/-- **The level data of select on the solver's state.** Let the blocks `B` have the depth and
the caps of the solver. The table and the blocks, the solver's level metadata at the caps
(`SolverLevelCapsInv`), the reached-state facts (`SelectModelInv`, which give
`activeS j = G (j + 1)`), and `SelectPotInv` give `SelectLevelMetaAt` for the chain of the
model, with `G_j` of `j < d` read from the solver and the core lengths `C.chainLen ℓ (j + 1)` of
the blocks. -/
theorem selectLevelMetaAt_of_solver {cfg : Alg2Config} {L P V vCap eCap metaBase pLast : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} {B : SelectBlocksLoc}
    {G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ}
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast))
    (hblk : SelectBlocksAt mem B P model.chain.toTreeChain model.chain.g model.chain.ℓ φ pLast)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hPot : SelectPotInv model.chain.toTreeChain model.chain.g φ) :
    SelectLevelMetaAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast) 4 P
      model.chain.toTreeChain model.chain.g model.chain.ℓ φ
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) := by
  have hd : model.chain.toTreeChain.d = B.d := by rw [hBd]; rfl
  refine selectLevelMetaAt_of_blocks hd htab (fun j hj => ?_) (fun j hj => ?_) hblk hPot
  · rw [hBd] at hj
    have h := (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).1
    rw [hBv, hBe]
    exact h
  · rw [hBd] at hj
    exact hmod.activeS_eq_G_succ j hj

end MinCostFlow.MinRatio
