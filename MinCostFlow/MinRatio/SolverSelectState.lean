module

public import MinCostFlow.MinRatio.OrdSolverRepFull
public import MinCostFlow.MinRatio.WireSelectSpec
public import MinCostFlow.MinRatio.WireReembPotChain
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
import Mathlib.Tactic

/-!
# The select heap in the state of the solver (`SolverSelectState`)

The find step with the select heap (`FindCycleStepSpecHeap`, `WireSelectSpec.lean`) asks for a
heap block that matches the chain, the runtime-stored heap pointer at `table + dMul * d + kOff`,
and the owned embedding tables (`SelectMetaEmbsAt`) that `selectRawRouteBody` reads directly
without calling `opCore 4`. This file puts them into the state of the solver, as a wrapper of
`solverStateRepFull`, so that `SolverRep.lean` does not change.

* `selectHeapCap cfg G m = 2 (nfMax + 2 m)`, with `nfMax = alg2NameBase cfg G +
  intRebuildThreshold P N₀ 0`: the capacity of the heap. Internal names stay below it.
* `SelectGhost`: the ghost data of the select state (the layouts `loc` and `mloc`, the heap size,
  the frozen potentials `φ` and core lengths, the cells the select state owns, and the value of
  the re-embedding potential).
* `SelectStateAt`: the facts at one memory, including ownership of the heap, metadata table,
  level embedding pointer arrays and walk blocks, and the runtime heap-handle cell
  `mem (table + dMul * d + kOff) = sg.loc.hb`.
* `SolverSelectInv`: `SelectStateAt` at every memory that agrees on the solver's foot and on the
  owned cells (so it depends on nothing else), the owned cells lie off the solver's foot, and the
  reached-state facts `SelectModelInv`.
* `solverStateRepSel`: `solverStateRepFull` with `SolverSelectInv`, the owned cells added to the
  foot, and `K · chainReembPot pot` added to the potential (`WireReembPotChain.lean`).
* `solverStateRepSel_local`: the wrapper is local.
* `solverSelect_findHyps`: the hypotheses of the select heap that `FindCycleStepSpecHeap` takes,
  at any heap pointer above the foot of the wrapper.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-- The capacity of the select heap: twice the bound `nfMax + 2 m` on the names, with
`nfMax = alg2NameBase cfg G + intRebuildThreshold P N₀ 0`. -/
noncomputable def selectHeapCap (cfg : Alg2Config) (G : MGraph) (m : ℕ) : ℕ :=
  2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * m)

/-- The ghost data of the select state. -/
structure SelectGhost where
  /-- The layout of the heap block. -/
  loc : SelectHeapLoc
  /-- The layout of the level metadata. -/
  mloc : SelectLevelMetaLoc
  /-- The number of keys in the heap. -/
  size : ℕ
  /-- The frozen potentials of the levels. -/
  φ : ℕ → ℕ → ℝ
  /-- The core lengths of the levels. -/
  coreLen : ℕ → ℕ → ℝ
  /-- The cells that the select state owns. -/
  owned : ℕ → Prop
  /-- The re-embedding potential `chainReembPot pot` of the chain. -/
  reembPot : ℕ

/-- The facts of the select state at the memory `mem`, for the solver's foot `foot` and
metadata-region base `table`:
* the layout: capacity `selectHeapCap`, `d` levels, `L` limbs, and the two layouts agree on the
  metadata pointer and the gradient pointer;
* the runtime select-heap handle is stored at `table + dMul * cfg.P.d + kOff` inside the solver
  foot or owned select cells;
* the heap block, metadata block, and every level's embedding pointer array and walk words are
  owned by the select state;
* the heap matches the chain (`SelectHeapMatchesChain`), and the metadata holds the levels
  (`SelectLevelMetaAt`). -/
def SelectStateAt {cfg : Alg2Config} (G : MGraph) (L P m dMul kOff table : ℕ)
    (model : Alg2State cfg) (foot : ℕ → Prop) (sg : SelectGhost) (mem : ℕ → ℕ) : Prop :=
  sg.loc.cap = selectHeapCap cfg G m ∧ sg.loc.d = cfg.P.d ∧ sg.loc.Lk = L ∧
  sg.mloc.metaBase = sg.loc.metaPtr ∧ sg.mloc.g0Ptr = sg.loc.g0Ptr ∧ sg.mloc.Lk = L ∧
  mem (table + dMul * cfg.P.d + kOff) = sg.loc.hb ∧
  (foot (table + dMul * cfg.P.d + kOff) ∨ sg.owned (table + dMul * cfg.P.d + kOff)) ∧
  (∀ a, sg.loc.hb ≤ a → a < sg.loc.endAddr → sg.owned a) ∧
  (∀ a, sg.loc.metaPtr ≤ a → a < sg.loc.metaPtr + selectLevelMetaSize cfg.P.d → sg.owned a) ∧
  (∀ i < cfg.P.d,
    (∀ a, sg.mloc.embPtr i ≤ a → a < sg.mloc.embPtr i + sg.mloc.eCap i → sg.owned a) ∧
    (∀ e ∈ (model.chain.toTreeChain.activeCore i).E,
      ∀ t < (mWalkEncode (model.chain.toTreeChain.activeEmb i e)).length,
        sg.owned (mem (sg.mloc.embPtr i + e) + t))) ∧
  SelectHeapMatchesChain mem sg.loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ
    sg.size ∧
  SelectLevelMetaAt mem sg.mloc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ sg.φ
    sg.coreLen

/-- The invariant of the select state: `SelectStateAt` at every memory that agrees with `mem` on
the solver's level-metadata footprint `metaFoot` and on the owned cells (so tree, off-tree, and
header mutations outside `metaFoot` cannot affect it), the owned cells lie off the solver's full
foot `foot`, and the reached-state facts `SelectModelInv` hold for some base graph and parameters. -/
def SolverSelectInv {cfg : Alg2Config} (G : MGraph) (L P m dMul kOff table : ℕ)
    (model : Alg2State cfg) (foot metaFoot : ℕ → Prop) (sg : SelectGhost) (mem : ℕ → ℕ) : Prop :=
  (∀ mem' : ℕ → ℕ, (∀ a, metaFoot a ∨ sg.owned a → mem' a = mem a) →
    SelectStateAt G L P m dMul kOff table model metaFoot sg mem') ∧
  (∀ a, sg.owned a → ¬ foot a) ∧
  ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ), SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c

/-- **The representation of the solver with the select heap.** It is `solverStateRepFull` with
`SolverSelectInv` for the foot of `solverStateRepFull`, the level-metadata footprint
`LevelMetaFoot`, and `table = tok.1.1.1.table`. The ghost `reembPot` equals the re-embedding
potential `chainReembPot pot` of the chain, and the potential of the wrapper adds `K` times it,
with `K` the cost of one key (`WireReembPotChain.lean`). The foot adds the cells that the select
state owns. -/
noncomputable def solverStateRepSel (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (K : ℕ) (pot : cfg.T.State → ℕ) :
    DSRep (Alg2State cfg) where
  τ := (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ ×
    SelectGhost
  rep root model tok mem :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).rep
      root model tok.1 mem ∧
    SolverSelectInv G L P m dMul kOff tok.1.1.1.table model
      ((solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tok.1) (LevelMetaFoot tok.1.1.1) tok.2 mem ∧
    tok.2.reembPot = chainReembPot pot model.chain
  foot root tok a :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
      root tok.1 a ∨ tok.2.owned a
  phi root tok mem :=
    (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).phi
      root tok.1 mem + K * tok.2.reembPot

/-- `solverStateRepSel` is local, since `solverStateRepFull` is local, `LevelMetaFoot` lies inside
the solver's foot, and `SolverSelectInv` asks `SelectStateAt` at every memory that agrees on
`LevelMetaFoot` and the owned cells. -/
theorem solverStateRepSel_local (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff : ℕ)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local) (K : ℕ)
    (pot : cfg.T.State → ℕ) :
    (solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      Rcore K pot).Local := by
  intro root model tok mem₁ mem₂ hag
  have hfull := solverStateRepFull_local cfg κ G L P m V psi k epsExp drainUnit unit toolMul
    treeMul hlocalCore root model tok.1 mem₁ mem₂ (fun a ha => hag a (Or.inl ha))
  refine ⟨fun h => ⟨hfull.1 h.1, ⟨fun mem' hmem' => h.2.1.1 mem' fun a ha => ?_, h.2.1.2.1,
    h.2.1.2.2⟩, h.2.2⟩, ?_⟩
  · rw [hmem' a ha]
    exact (hag a (ha.imp (fun hm => LevelMetaFoot.mem_foot h.1.1.1 hm) id)).symm
  · change _ + _ = _ + _
    rw [hfull.2]

/-- **The hypotheses of the find step.** Let the heap pointer `heap` lie above every cell of the
foot of `solverStateRepSel` (the solver's foot and the owned cells), and let `metaFoot ⊆ foot`.
Then the select state gives all select-heap hypotheses that `FindCycleStepSpecHeap` takes:
`loc.Lk = L`, the runtime handle at `table + dMul * d + kOff`, `SelectHeapMatchesChain`,
`SelectMetaEmbsAt` below `heap`, the heap block below `heap` and off the solver's foot, and
`SelectModelInv`. -/
theorem solverSelect_findHyps {cfg : Alg2Config} {G : MGraph} {L P m dMul kOff table : ℕ}
    {model : Alg2State cfg} {foot metaFoot : ℕ → Prop} {sg : SelectGhost} {mem : ℕ → ℕ} {heap : ℕ}
    (hinv : SolverSelectInv G L P m dMul kOff table model foot metaFoot sg mem)
    (hmetaSub : ∀ a, metaFoot a → foot a)
    (hbelow : ∀ a, foot a ∨ sg.owned a → a < heap) :
    sg.loc.Lk = L ∧
      mem (table + dMul * cfg.P.d + kOff) = sg.loc.hb ∧
      table + dMul * cfg.P.d + kOff < heap ∧
      SelectHeapMatchesChain mem sg.loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ
        sg.size ∧
      SelectMetaEmbsAt mem sg.loc.metaPtr heap model.chain.toTreeChain ∧
      sg.loc.endAddr ≤ heap ∧
      (∀ a, sg.loc.hb ≤ a → a < sg.loc.endAddr → ¬ foot a) ∧
      ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ), SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c := by
  obtain ⟨hst, hoff, hmod⟩ := hinv
  obtain ⟨_, hlocD, hLk, hmetaEq, _, _, hhbRd, hhbOwn, hheapOwn, hmetaOwn, hembsOwn, hmatch, hmeta⟩ :=
    hst mem fun _ _ => rfl
  have hd : model.chain.toTreeChain.d = cfg.P.d := rfl
  have hendGt : sg.loc.hb < sg.loc.endAddr := by
    rw [sg.loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
  have hend : sg.loc.endAddr ≤ heap := by
    have := hbelow _ (Or.inr (hheapOwn (sg.loc.endAddr - 1) (by omega) (by omega)))
    omega
  refine ⟨hLk, hhbRd, hbelow _ (hhbOwn.imp (hmetaSub _) id), hmatch, ⟨?_, ?_⟩, hend,
    fun a h1 h2 => hoff a (hheapOwn a h1 h2), hmod⟩
  · -- The metadata table ends below `heap`.
    have hlast := hbelow _ (Or.inr (hmetaOwn (sg.loc.metaPtr + selectLevelMetaSize cfg.P.d - 1)
      (by unfold selectLevelMetaSize; omega) (by unfold selectLevelMetaSize; omega)))
    rw [hd]; unfold selectLevelMetaSize at hlast ⊢; omega
  · intro i hi e he
    rw [hd] at hi
    obtain ⟨hmd, _, _, hptrs, _, _, _, _, hemb, _⟩ := hmeta
    obtain ⟨hTabOwn, hWalkOwn⟩ := hembsOwn i hi
    have hptr : mem (smEntryAddr sg.loc.metaPtr model.chain.toTreeChain.d 5 i) = sg.mloc.embPtr i := by
      have := (hptrs i (by rw [hd]; omega)).2.2.2.2.2.1
      rwa [hmetaEq, hmd] at this
    dsimp only
    rw [hptr]
    obtain ⟨heCap, hmw⟩ := hemb i (by rw [hd]; exact hi) e he
    have hlenPos : 0 < (mWalkEncode (model.chain.toTreeChain.activeEmb i e)).length := by
      rw [mWalkEncode_length]; omega
    have htabLt := hbelow _ (Or.inr (hTabOwn (sg.mloc.embPtr i + e) (by omega) (by omega)))
    have hlastW := hbelow _ (Or.inr (hWalkOwn e he
      ((mWalkEncode (model.chain.toTreeChain.activeEmb i e)).length - 1) (by omega)))
    exact ⟨htabLt, by omega, hmw⟩

end MinCostFlow.MinRatio
