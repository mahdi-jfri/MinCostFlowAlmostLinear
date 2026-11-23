module

public import MinCostFlow.Chain.Ordered.ActiveCoreSucc
public import MinCostFlow.MinRatio.SolverSelectState
public import MinCostFlow.MinRatio.WireSelectUpdateEdge
public import MinCostFlow.MinRatio.WireReembModel

/-!
# Aliasing `S_j` to `G_{j + 1}` in `SelectLevelMetaAt` (`WireSelectActiveS`)

Connects the chain model fact `C.activeS j = C.G (j + 1)` (`Chain/Ordered/ActiveCoreSucc.lean`) to
the reached states of the min-ratio solver and to `SelectLevelMetaAt` / `SelectMetaDisjoint`
(`WireSelectKeyEval.lean`, `WireSelectUpdateEdge.lean`), so `S_j` in `SelectLevelMetaAt` can point
directly at the solver's own graph `G_{j + 1}` with no copy.

* Reached solver states: `OrdSolverReached.activeS_eq_G_succ`,
  `OrdSolverReachedInv.activeS_eq_G_succ`, `OrdSolverReached.preLoop_activeS_eq_G_succ`,
  `SelectModelInv.activeS_eq_G_succ`, and `shiftLoopChainInv_activeS_eq_G_succ`.
* Program tool (`sparseCoreProgTool`): `progTool_S_updateOrd` (applying the forwarded batch
  `U_S b` to `T.S st b` yields `T.S st' b` literally), `progTool_activeS_eq_G_succ_of_shiftLoop`,
  and `progTool_activeS_eq_G_succ_of_reachedInv`.
* `SelectLevelMetaAt` and `SelectMetaDisjoint` aliasing helpers: `dynGraphAt_activeS_of_G_succ`,
  `selectLevelMetaAt_of_alias`, `selectMetaDisjoint_of_alias`,
  `selectLevelMetaAt_of_reachedInv_alias`, and `selectLevelMetaAt_of_shiftLoop_alias`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-! ## 1. `activeS j = G (j + 1)` on solver invariants -/

/-- On every state reached by ordered Algorithm 2 (`OrdSolverReached`), the active sparsified core
of every level `j < cfg.P.d` equals the graph of level `j + 1` (with no extra hypotheses). -/
theorem OrdSolverReached.activeS_eq_G_succ {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) :
    ∀ j < cfg.P.d, model.chain.toTreeChain.activeS j = model.chain.toTreeChain.G (j + 1) := by
  obtain ⟨D, η, op, T, _, _, _, _, rfl⟩ := h
  exact minRatioFailState_activeCoreEqNext cfg κ D η op T

/-- On every state meeting `OrdSolverReachedInv`, the active sparsified core of every level
`j < cfg.P.d` equals the graph of level `j + 1`. -/
theorem OrdSolverReachedInv.activeS_eq_G_succ {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (h : OrdSolverReachedInv κ G P model tok) :
    ∀ j < cfg.P.d, model.chain.toTreeChain.activeS j = model.chain.toTreeChain.G (j + 1) :=
  h.2.1.activeS_eq_G_succ

/-- On the pre-loop state of `Update` from a reached state (`alg2PreLoopState`), the active
sparsified core of every level `j < cfg.P.d` equals the graph of level `j + 1`. -/
theorem OrdSolverReached.preLoop_activeS_eq_G_succ {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (U : List Update)
    (g l : ℕ → ℝ) :
    ∀ j < cfg.P.d,
      (alg2PreLoopState cfg model U g l).chain.toTreeChain.activeS j =
        (alg2PreLoopState cfg model U g l).chain.toTreeChain.G (j + 1) :=
  algorithm1_update_activeCoreEqNext cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _
    h.activeS_eq_G_succ

/-- Under `SelectModelInv`, the active sparsified core of every level `j < cfg.P.d` equals the
graph of level `j + 1`. -/
theorem SelectModelInv.activeS_eq_G_succ {cfg : Alg2Config} {model : Alg2State cfg}
    {G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (h : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c) :
    ∀ j < cfg.P.d, model.chain.toTreeChain.activeS j = model.chain.toTreeChain.G (j + 1) :=
  fun _ hj => model.chain.toTreeChain.activeS_eq_G_succ h.1 hj

/-- Under `ShiftLoopChainInv`, the active sparsified core of every level `j < cfg.P.d` equals the
graph of level `j + 1`. -/
theorem shiftLoopChainInv_activeS_eq_G_succ {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}
    (h : ShiftLoopChainInv cfg ch) :
    ∀ j < cfg.P.d, ch.toTreeChain.activeS j = ch.toTreeChain.G (j + 1) :=
  h.activeS_eq_G_succ

/-! ## 2. Specialization to `sparseCoreProgTool` -/

/-- On `sparseCoreProgTool`, updating a state by `(U, ord')` applies the forwarded output batch
`U_S j` to each branch's sparsified core `S st j` literally (for both nonempty and empty states). -/
theorem progTool_S_updateOrd {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    (st : SparseCoreBundleState depth) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (j : ℕ) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    T.S (T.updateOrd st U ℓ g ord').1 j = (T.S st j).applyBatch ((T.updateOrd st U ℓ g ord').2 j) := by
  intro T
  by_cases hne : st.isNonempty = true
  · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) st hne U ℓ g ord'
    have hne' : (T.updateOrd st U ℓ g ord').1.isNonempty = true := by
      change ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.isNonempty = true
      rw [hup]; exact hne
    have hS' : T.S (T.updateOrd st U ℓ g ord').1 j =
        (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord').state.S_cur := by
      dsimp only [T]
      rw [progTool_S_of_nonempty _ hne', hup]
    have hS : T.S st j = (st.trees j).S_cur := progTool_S_of_nonempty st hne j
    have hU : (T.updateOrd st U ℓ g ord').2 j =
        (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord').U_S := by
      dsimp only [T]; rw [hup]
    rw [hS', hS, hU]
    rfl
  · have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) st hf U ℓ g ord'
    dsimp only [T]
    rw [hup]
    rfl

private theorem tool_S_cast {T₁ T₂ : SparseCoreRestartTool} (hT : T₁ = T₂)
    (st : T₁.State) (b : ℕ) : T₂.S (hT ▸ st) b = T₁.S st b := by
  subst hT; rfl

/-- Specialization of `ShiftLoopChainInv.activeS_eq_G_succ` to a configuration whose tool is
`sparseCoreProgTool`. -/
theorem progTool_activeS_eq_G_succ_of_shiftLoop {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    {ch : ChainState cfg.T cfg.P} (h : ShiftLoopChainInv cfg ch) :
    ∀ j < cfg.P.d,
      ch.toTreeChain.activeS j = ch.toTreeChain.G (j + 1) ∧
      (sparseCoreProgTool lsfInit C_lsst depth impl).S (hT ▸ ch.scState j) (ch.bran j) =
        ch.G (j + 1) := by
  intro j hj
  refine ⟨h.activeS_eq_G_succ j hj, ?_⟩
  rw [tool_S_cast hT]
  exact (activeCoreEqNext_iff ch).mp h.activeS_eq_G_succ j hj

/-- Specialization of `OrdSolverReachedInv.activeS_eq_G_succ` to a configuration whose tool is
`sparseCoreProgTool`. -/
theorem progTool_activeS_eq_G_succ_of_reachedInv {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (h : OrdSolverReachedInv κ G P model tok) :
    ∀ j < cfg.P.d,
      model.chain.toTreeChain.activeS j = model.chain.toTreeChain.G (j + 1) ∧
      (sparseCoreProgTool lsfInit C_lsst depth impl).S (hT ▸ model.chain.scState j)
          (model.chain.bran j) =
        model.chain.G (j + 1) := by
  intro j hj
  refine ⟨h.activeS_eq_G_succ j hj, ?_⟩
  rw [tool_S_cast hT]
  exact (activeCoreEqNext_iff model.chain).mp h.activeS_eq_G_succ j hj

/-! ## 3. Aliasing `sPtr j = GPtr (j + 1)` in `SelectLevelMetaAt` and `SelectMetaDisjoint` -/

/-- When `mloc.sPtr j` aliases `mloc.GPtr (j + 1)` at matching caps and `C.activeS j = C.G (j + 1)`,
the `DynGraphAt` clause for `C.activeS j` in `SelectLevelMetaAt` follows directly from the
`DynGraphAt` clause for `C.G (j + 1)`. -/
theorem dynGraphAt_activeS_of_G_succ {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {C : TreeChain}
    (hG : ∀ j ≤ C.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j))
    (hS : ∀ j < C.d, C.activeS j = C.G (j + 1))
    (hsPtr : ∀ j < C.d, mloc.sPtr j = mloc.GPtr (j + 1))
    (hvCap : ∀ j < C.d, mloc.vCap j = mloc.vCap (j + 1))
    (heCap : ∀ j < C.d, mloc.eCap j = mloc.eCap (j + 1)) :
    ∀ j < C.d, DynGraphAt mem (mloc.sPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeS j) := by
  intro j hj
  rw [hsPtr j hj, hvCap j hj, heCap j hj, hS j hj]
  exact hG (j + 1) hj

/-- Build `SelectLevelMetaAt` with `sPtr j` aliased to `GPtr (j + 1)` (no separate `S_j` copy). -/
theorem selectLevelMetaAt_of_alias {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hd : mloc.d = C.d)
    (hg0 : mem (mloc.metaBase + smG0Off) = mloc.g0Ptr)
    (hmd : mem (mloc.metaBase + smDOff) = mloc.d)
    (hptrs : ∀ j ≤ C.d,
      mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 4 j) = mloc.coreLenPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 5 j) = mloc.embPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 7 j) = mloc.sPtr j)
    (hg0At : EdgeValuesAt mem mloc.g0Ptr h mloc.Lk P (C.G 0).E g)
    (hG : ∀ j ≤ C.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j))
    (hphi : ∀ j ≤ C.d, EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V (φ j))
    (hclen : ∀ j ≤ C.d,
      EdgeValuesAt mem (mloc.coreLenPtr j) h mloc.Lk (coreLenPrec C.d P mloc.pLast j) (C.G j).E (coreLen j))
    (hemb : ∀ j < C.d, MEmbAt mem (mloc.embPtr j) (C.activeCore j).E (mloc.eCap j) (C.activeEmb j))
    (hF : ∀ j ≤ C.d, DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F)
    (hS : ∀ j < C.d, C.activeS j = C.G (j + 1))
    (hsPtr : ∀ j < C.d, mloc.sPtr j = mloc.GPtr (j + 1))
    (hvCap : ∀ j < C.d, mloc.vCap j = mloc.vCap (j + 1))
    (heCap : ∀ j < C.d, mloc.eCap j = mloc.eCap (j + 1))
    (hPot : SelectPotInv C g φ)
    (hCLen : SelectCoreLenInv C ℓ coreLen)
    (hpLast : mloc.sPtr mloc.d = mloc.pLast) :
    SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen :=
  ⟨hd, hg0, hmd, hptrs, hg0At, hG, hphi, hclen, hemb, hF,
    dynGraphAt_activeS_of_G_succ hG hS hsPtr hvCap heCap, hPot, hCLen, hpLast⟩

/-- Build `SelectMetaDisjoint` with `sPtr j` aliased to `GPtr (j + 1)`: the `sPtr` region bounds
and heap disjointness follow from the `GPtr (j + 1)` bounds. -/
theorem selectMetaDisjoint_of_alias {mloc : SelectLevelMetaLoc} {loc : SelectHeapLoc} {hi : ℕ}
    (hLk : mloc.Lk = loc.Lk)
    (hmetaHi : mloc.metaBase + selectLevelMetaSize mloc.d ≤ hi)
    (hmetaDisj : mloc.metaBase + selectLevelMetaSize mloc.d ≤ loc.hb ∨ loc.endAddr ≤ mloc.metaBase)
    (hGF : ∀ j ≤ mloc.d,
      mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
      (mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ loc.hb ∨ loc.endAddr ≤ mloc.GPtr j) ∧
      mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
      (mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ loc.hb ∨ loc.endAddr ≤ mloc.fPtr j))
    (hsPtr : ∀ j < mloc.d, mloc.sPtr j = mloc.GPtr (j + 1))
    (hvCap : ∀ j < mloc.d, mloc.vCap j = mloc.vCap (j + 1))
    (heCap : ∀ j < mloc.d, mloc.eCap j = mloc.eCap (j + 1))
    (htabs : SelectMetaTablesBelow mloc hi) :
    SelectMetaDisjoint mloc loc hi := by
  refine ⟨hLk, hmetaHi, hmetaDisj, fun j hj => ?_, htabs⟩
  obtain ⟨h1, h2, h3, h4⟩ := hGF j hj
  refine ⟨h1, h2, h3, h4, fun hlt => ?_⟩
  rw [hsPtr j hlt, hvCap j hlt, heCap j hlt]
  exact ⟨(hGF (j + 1) hlt).1, (hGF (j + 1) hlt).2.1⟩

/-- `DynGraphAt` for `activeS j` on a state meeting `OrdSolverReachedInv`, when `sPtr j` aliases
`GPtr (j + 1)` at uniform caps `(vCap, eCap)`. -/
theorem dynGraphAt_activeS_of_reachedInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P vCap eCap : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    (h : OrdSolverReachedInv κ G P model tok)
    (hG : ∀ j ≤ cfg.P.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j)
      (model.chain.toTreeChain.G j))
    (hsPtr : ∀ j < cfg.P.d, mloc.sPtr j = mloc.GPtr (j + 1))
    (hvCap : ∀ j ≤ cfg.P.d, mloc.vCap j = vCap)
    (heCap : ∀ j ≤ cfg.P.d, mloc.eCap j = eCap) :
    ∀ j < model.chain.toTreeChain.d,
      DynGraphAt mem (mloc.sPtr j) (mloc.vCap j) (mloc.eCap j)
        (model.chain.toTreeChain.activeS j) :=
  dynGraphAt_activeS_of_G_succ hG h.activeS_eq_G_succ hsPtr
    (fun j hj => (hvCap j (Nat.le_of_lt hj)).trans (hvCap (j + 1) hj).symm)
    (fun j hj => (heCap j (Nat.le_of_lt hj)).trans (heCap (j + 1) hj).symm)

/-- `DynGraphAt` for `activeS j` on a chain meeting `ShiftLoopChainInv`, when `sPtr j` aliases
`GPtr (j + 1)` at uniform caps `(vCap, eCap)`. -/
theorem dynGraphAt_activeS_of_shiftLoop {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}
    {vCap eCap : ℕ} {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    (h : ShiftLoopChainInv cfg ch)
    (hG : ∀ j ≤ cfg.P.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j)
      (ch.toTreeChain.G j))
    (hsPtr : ∀ j < cfg.P.d, mloc.sPtr j = mloc.GPtr (j + 1))
    (hvCap : ∀ j ≤ cfg.P.d, mloc.vCap j = vCap)
    (heCap : ∀ j ≤ cfg.P.d, mloc.eCap j = eCap) :
    ∀ j < ch.toTreeChain.d,
      DynGraphAt mem (mloc.sPtr j) (mloc.vCap j) (mloc.eCap j)
        (ch.toTreeChain.activeS j) :=
  dynGraphAt_activeS_of_G_succ hG h.activeS_eq_G_succ hsPtr
    (fun j hj => (hvCap j (Nat.le_of_lt hj)).trans (hvCap (j + 1) hj).symm)
    (fun j hj => (heCap j (Nat.le_of_lt hj)).trans (heCap (j + 1) hj).symm)

end MinCostFlow.MinRatio
