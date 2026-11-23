module

public import MinCostFlow.MinRatio.SolverSelectBlocks
public import MinCostFlow.MinRatio.SelectPhiBounded
import Mathlib.Tactic

/-!
# The select-region invariant of the solver (`SolverSelectRegionInv`)

`SolverSelectInv` says what the select state holds, but it leaves free the cells that it does
not read: the free slots of the level blocks, the address of the blocks, the slot size, and the
terminal precision `pLast`. It also does not bound the frozen potentials or the gradients. A
body that rebuilds a level needs all of these. It writes free slots in place, so these slots
must be owned. It reads the blocks address, so the address must be pinned. And it can only show
that its fixed-point values fit in `L` limbs if the potentials of the lower levels and the
gradients are bounded.

`SolverSelectRegionInv` adds exactly these facts:
* the owned layout `SolverSelectBlocksInv` for some blocks layout `B` with slot size `slot` and
  terminal precision `pLast`; it makes the owned cells exactly `[hb, B.endAddr)`;
* the bound `SelectPhiBoundedAt` with `N = 2 m + 2` and `M_g = 2 ^ E` at every level;
* the bound `|g e| ≤ 2 ^ E` on the gradients of the level-`0` edges.

The gradients are not bounded by `OrdSolverReached`, which bounds lengths only. So the last
fact is carried here. `Init` gets it from its input gradients and `Update` from its new ones.

The main result is `SolverSelectRegionInv.preserve_of_levelMeta`: a step that keeps the
level-metadata region, does not write the owned cells, and does not change the chain keeps the
invariant with the same ghost.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-- **The select-region invariant.** For the solver's foot `foot`, it asks:
* `SolverSelectBlocksInv` for some blocks layout `B` with `B.slot = slot`, at the caps
  `(vCap, eCap)` and the terminal precision `pLast`;
* `SelectPhiBoundedAt` with `N = 2 m + 2` and `M_g = 2 ^ E` at every level `j ≤ d`;
* `|g e| ≤ 2 ^ E` for every level-`0` edge `e`. -/
def SolverSelectRegionInv {cfg : Alg2Config} (G : MGraph) (L P m E pLast slot vCap eCap : ℕ)
    (model : Alg2State cfg) (foot : ℕ → Prop) {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (mem : ℕ → ℕ) : Prop :=
  (∃ B : SelectBlocksLoc, B.slot = slot ∧
    SolverSelectBlocksInv G L P m vCap eCap pLast B model foot tok sg mem) ∧
  (∀ j ≤ cfg.P.d,
    SelectPhiBoundedAt model.chain.toTreeChain sg.φ (2 * m + 2) ((2 : ℝ) ^ E) j) ∧
  (∀ e ∈ (model.chain.G 0).E, |model.chain.g e| ≤ (2 : ℝ) ^ E)

/-- The owned cells of the select ghost lie off the solver's foot. -/
theorem SolverSelectRegionInv.owned_not_foot {cfg : Alg2Config} {G : MGraph}
    {L P m E pLast slot vCap eCap : ℕ} {model : Alg2State cfg} {foot : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem : ℕ → ℕ}
    (h : SolverSelectRegionInv G L P m E pLast slot vCap eCap model foot tok sg mem) :
    ∀ a, sg.owned a → ¬ foot a := by
  obtain ⟨⟨B, _, hblk⟩, _, _⟩ := h
  exact hblk.2.2.2.2.2.2.2.1

/-- `SolverSelectRegionInv` gives `SolverSelectInv` at `(dMul, kOff) = (4, 2)` when the level
caps hold (`SolverSelectBlocksInv.toSolverSelectInv`). -/
theorem SolverSelectRegionInv.toSolverSelectInv {cfg : Alg2Config} {G : MGraph}
    {L P V m E pLast slot vCap eCap : ℕ} {model : Alg2State cfg} {foot : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem : ℕ → ℕ}
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (h : SolverSelectRegionInv G L P m E pLast slot vCap eCap model foot tok sg mem) :
    SolverSelectInv G L P m 4 2 tok.table model foot (LevelMetaFoot tok) sg mem := by
  obtain ⟨⟨B, _, hblk⟩, _, _⟩ := h
  exact hblk.toSolverSelectInv hcaps

/-- **Transfer to a new memory and token.** If the new memory agrees with the old one on the
owned cells, the level-metadata region is kept (`PreservesLevelMeta`), the owned cells lie off the
new foot, and the chain is kept, then `SolverSelectRegionInv` holds with the same ghost. -/
theorem SolverSelectRegionInv.congr {cfg : Alg2Config} {G : MGraph}
    {L P V m E pLast slot vCap eCap : ℕ}
    {model model' : Alg2State cfg} {foot foot' : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem mem' : ℕ → ℕ}
    (hInv : SolverSelectRegionInv G L P m E pLast slot vCap eCap model foot tok sg mem)
    (hcaps : SolverLevelMetaAt P V model tok mem)
    (hMeta : PreservesLevelMeta tok tok' mem mem')
    (hoff' : ∀ a, sg.owned a → ¬ foot' a)
    (hagOwn : ∀ a, sg.owned a → mem' a = mem a)
    (hChain : model'.chain = model.chain)
    (hExtG : model'.extG = model.extG)
    (hExtℓ : model'.extℓ = model.extℓ) :
    SolverSelectRegionInv G L P m E pLast slot vCap eCap model' foot' tok' sg mem' := by
  obtain ⟨⟨B, hslot, hblk⟩, hphi, hg⟩ := hInv
  have hown : sg.owned = fun a => sg.loc.hb ≤ a ∧ a < B.endAddr := hblk.2.2.2.2.2.2.1
  have hagOwn' : ∀ a, sg.loc.hb ≤ a → a < B.endAddr → mem' a = mem a := fun a h1 h2 =>
    hagOwn a (by rw [hown]; exact ⟨h1, h2⟩)
  have hmod' : ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ),
      SelectModelInv model' G₀ σ σ_mwu γ_ℓ γ_c := by
    obtain ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, hm⟩ := hblk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, by simpa [SelectModelInv, hChain, hExtG, hExtℓ] using hm⟩
  refine ⟨⟨B, hslot, hblk.preserve_of_levelMeta hcaps hMeta hoff' hagOwn'
    (by rw [hChain]) (by rw [hChain]) (by rw [hChain]) hmod'⟩, ?_, ?_⟩
  · rw [hChain]; exact hphi
  · rw [hChain]; exact hg

/-- **Preservation across steps that keep the select state.** Take a step that keeps the
level-metadata region (`PreservesLevelMeta`), keeps every cell below `frameHi` off the old foot,
adds to the foot only cells in `[footLo, nextHeap)` with `frameHi ≤ footLo`, and keeps the chain.
If the owned cells lie below `frameHi`, the step keeps `SolverSelectRegionInv` with the same
ghost `sg`. The owned cells are kept because they lie below `frameHi` and off the old foot, and
they stay off the new foot because the new foot cells are old foot cells or lie at or above
`footLo`. -/
theorem SolverSelectRegionInv.preserve_of_levelMeta {cfg : Alg2Config} {G : MGraph}
    {L P V m E pLast slot vCap eCap frameHi footLo nextHeap : ℕ}
    {model model' : Alg2State cfg} {foot foot' : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem mem' : ℕ → ℕ}
    (hInv : SolverSelectRegionInv G L P m E pLast slot vCap eCap model foot tok sg mem)
    (hcaps : SolverLevelMetaAt P V model tok mem)
    (hMeta : PreservesLevelMeta tok tok' mem mem')
    (hFrame : ∀ a < frameHi, ¬ foot a → mem' a = mem a)
    (hFoot : ∀ a, foot' a → foot a ∨ (footLo ≤ a ∧ a < nextHeap))
    (hBelow : ∀ a, sg.owned a → a < frameHi)
    (hLe : frameHi ≤ footLo)
    (hChain : model'.chain = model.chain)
    (hExtG : model'.extG = model.extG)
    (hExtℓ : model'.extℓ = model.extℓ) :
    SolverSelectRegionInv G L P m E pLast slot vCap eCap model' foot' tok' sg mem' := by
  have hoff : ∀ a, sg.owned a → ¬ foot a := hInv.owned_not_foot
  refine hInv.congr hcaps hMeta (fun a ho hf' => ?_)
    (fun a ho => hFrame a (hBelow a ho) (hoff a ho)) hChain hExtG hExtℓ
  rcases hFoot a hf' with hf | ⟨hlo, _⟩
  · exact hoff a ho hf
  · have := hBelow a ho
    omega

/-- A potential bound at a level `k` only reads the level-`k` potential, so changing the
potential of another level keeps it. -/
theorem selectPhiBoundedAt_update_ne {C : TreeChain} {φ : ℕ → ℕ → ℝ} {N : ℕ} {M_g : ℝ}
    {j k : ℕ} (φj : ℕ → ℝ) (hkj : k ≠ j) (h : SelectPhiBoundedAt C φ N M_g k) :
    SelectPhiBoundedAt C (Function.update φ j φj) N M_g k := by
  intro v hv
  rw [Function.update_of_ne hkj]
  exact h v hv

end MinCostFlow.MinRatio
