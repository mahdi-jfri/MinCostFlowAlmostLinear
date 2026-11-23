module

public import MinCostFlow.MinRatio.SolverSelectState
public import MinCostFlow.MinRatio.SelectLevelBlocksSolver
public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.SelectPhiFillMath
import Mathlib.Tactic

/-!
# Owned select-region invariant on the solver state (`SolverSelectBlocks`)

Connects the concrete select region (`SelectRegion`, `SelectMetaTableAt`, `SelectBlocksAt`)
to `SolverSelectInv` (`SolverSelectState.lean`) at `(dMul, kOff) = (4, 2)` and provides the
frame, disjointness, and prefix-layout lemmas needed by the select-maintenance procedures of
`Update`, `Refresh`, `ShiftTerm`, and `ShiftDeep`:

* `SolverSelectBlocksInv`: strengthens `SolverSelectInv` with the fixed select-block layout `B`,
  terminal rounding precision `pLast`, `SelectRegion`, `SelectMetaTableAt`, `SelectBlocksAt`,
  `SelectPotInv`, `mem (solverSelectBlocksAddr tok.table d) = B.base`, and `sg.owned = [hb, B.endAddr)`.
* `SolverSelectBlocksInv.toSolverSelectInv`: proves `SolverSelectInv` at `dMul = 4, kOff = 2`
  from `SolverSelectBlocksInv` and `SolverLevelCapsInv` via `selectLevelMetaAt_of_solver`.
* `SolverSelectBlocksInv.preserve_of_levelMeta`: any step preserving `LevelMetaFoot` and the
  select region `[hb, B.endAddr)` preserves `SolverSelectBlocksInv`.
* `selectMetaDisjoint_of_solver_region`: derives `SelectMetaDisjoint` from `selectMetaDisjoint_of_region`.
* `selectPhiFill_hyps_of_blocks`: derives `SelectPhiPrefixAt`, `SelectPhiPrefixBelow`, and
  `SelectPhiTargetDisjoint` at any level `j ≤ d` from `SelectRegion`, `SelectMetaTableAt`,
  `SelBlocksDataAt`, and `SolverLevelCapsInv`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine SparseCore.Program DynSpanner.Program

private theorem mul_add_lt_mul_sb {e c L i : ℕ} (he : e < c) (hi : i < L) :
    e * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at this
  omega

/-- Stronger select-region invariant on the solver state, storing the owned `SelectRegion`,
`SelectMetaTableAt`, `SelectBlocksAt`, `SelectPotInv`, and `solverSelectBlocksAddr`. Implies
`SolverSelectInv` at `(dMul, kOff) = (4, 2)` via `SolverSelectBlocksInv.toSolverSelectInv`. -/
def SolverSelectBlocksInv {cfg : Alg2Config} (G : MGraph) (L P m vCap eCap pLast : ℕ)
    (B : SelectBlocksLoc) (model : Alg2State cfg) (foot : ℕ → Prop)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (tok : SolverToken cfg L Rcore)
    (sg : SelectGhost) (mem : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  B.d = d ∧ B.vCap = vCap ∧ B.eCap = eCap ∧ B.Lk = L ∧
  sg.loc.cap = selectHeapCap cfg G m ∧
  SelectRegion sg.loc.hb sg.loc B sg.loc.metaPtr ∧
  sg.owned = (fun a => sg.loc.hb ≤ a ∧ a < B.endAddr) ∧
  (∀ a, sg.owned a → ¬ foot a) ∧
  mem (solverSelectHeapAddr tok.table d) = sg.loc.hb ∧
  mem (solverSelectBlocksAddr tok.table d) = B.base ∧
  sg.mloc = selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem) pLast ∧
  sg.coreLen = (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) ∧
  SelectMetaTableAt mem sg.mloc ∧
  SelectBlocksAt mem B P model.chain.toTreeChain model.chain.g model.chain.ℓ sg.φ pLast ∧
  SelectPotInv model.chain.toTreeChain model.chain.g sg.φ ∧
  SelectHeapMatchesChain mem sg.loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ sg.size ∧
  ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ), SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c

/-- Helper: `solverSelectHeapAddr table d = table + 4 * d + 2`. -/
theorem solverSelectHeapAddr_eq_four_two (table d : ℕ) :
    solverSelectHeapAddr table d = table + 4 * d + 2 := by
  unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr
  omega

/-- Helper: `loc.hb ≤ loc.endAddr = metaBase` and `metaBase + selectLevelMetaSize B.d = B.base ≤ B.endAddr`. -/
theorem SelectRegion.bounds {sb metaBase : ℕ} {loc : SelectHeapLoc} {B : SelectBlocksLoc}
    (hreg : SelectRegion sb loc B metaBase) :
    loc.hb ≤ loc.endAddr ∧ loc.endAddr = metaBase ∧
    metaBase + selectLevelMetaSize B.d = B.base ∧ B.base ≤ B.endAddr := by
  obtain ⟨_, h2, h3, h4, _, _, _⟩ := hreg
  refine ⟨by rw [loc.endAddr_eq]; omega, by omega, by omega, by rw [B.endAddr_eq]; omega⟩

/-- **Bridge to `SolverSelectInv`:** `SolverSelectBlocksInv` + `SolverLevelCapsInv` implies
`SolverSelectInv` at `(dMul, kOff) = (4, 2)` and `metaFoot = LevelMetaFoot tok`. -/
theorem SolverSelectBlocksInv.toSolverSelectInv {cfg : Alg2Config} {G : MGraph}
    {L P V m vCap eCap pLast : ℕ} {B : SelectBlocksLoc}
    {model : Alg2State cfg} {foot : ℕ → Prop} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok : SolverToken cfg L Rcore} {sg : SelectGhost} {mem : ℕ → ℕ}
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hblk : SolverSelectBlocksInv G L P m vCap eCap pLast B model foot tok sg mem) :
    SolverSelectInv G L P m 4 2 tok.table model foot (LevelMetaFoot tok) sg mem := by
  obtain ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown, hoff, hhbAddr, _, hmloc, hclen,
    htab, hblocks, hpot, hmatch, hmod⟩ := hblk
  obtain ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod'⟩ := hmod
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  refine ⟨fun mem' hmem' => ?_, hoff, G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod'⟩
  have hagOwn : ∀ a, sg.loc.hb ≤ a → a < B.endAddr → mem' a = mem a := fun a h1 h2 =>
    hmem' a (Or.inr (by rw [hown]; exact ⟨h1, h2⟩))
  have hagMeta : ∀ a, LevelMetaFoot tok a → mem' a = mem a := fun a ha =>
    hmem' a (Or.inl ha)
  have hhbFoot : LevelMetaFoot tok (tok.table + 4 * cfg.P.d + 2) := by
    rw [← solverSelectHeapAddr_eq_four_two]
    exact Or.inr (Or.inl hcaps.1.1.2.2.1)
  have hGeq : ∀ j < cfg.P.d, solverLevelG tok mem' j = solverLevelG tok mem j := fun j hj => by
    unfold solverLevelG
    have htag : tok.tag (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
      have := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      simpa [Nat.add_assoc] using this
    exact hagMeta _ (Or.inr (Or.inr (Or.inl htag)))
  have hmlocEq : selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem') pLast =
      selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem) pLast := by
    unfold selectMlocOf
    congr 1
    · funext j; split_ifs with h
      · exact hGeq j (hBd ▸ h)
      · rfl
    · funext j; split_ifs with h1 h2
      · exact hGeq (j + 1) (hBd ▸ h1)
      · rfl
      · rfl
  have hcaps' : SolverLevelCapsInv P V vCap eCap model tok mem' :=
    hcaps.preserve rfl hcaps.1.2.1 (fun a ha => ⟨rfl, hagMeta a ha⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have htab' : SelectMetaTableAt mem' sg.mloc :=
    htab.of_agree fun a h1 h2 => hagOwn a (by rw [hmloc] at h1; simp only [selectMlocOf] at h1; omega)
      (by rw [hmloc] at h2; simp only [selectMlocOf] at h2; omega)
  have hblocks' : SelectBlocksAt mem' B P model.chain.toTreeChain model.chain.g model.chain.ℓ
      sg.φ pLast :=
    hblocks.of_agree fun a h1 h2 => hagOwn a (by omega) h2
  have hmatch' : SelectHeapMatchesChain mem' sg.loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sg.size :=
    hmatch.of_agree fun a h1 h2 => hagOwn a h1 (by omega)
  have hmeta' : SelectLevelMetaAt mem' sg.mloc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sg.φ sg.coreLen := by
    rw [hmloc, hclen, ← hmlocEq]
    exact selectLevelMetaAt_of_solver hBd hBv hBe
      (by rw [hmlocEq, ← hmloc]; exact htab') hblocks' hcaps' hmod' hpot
  refine ⟨hcap, hreg.2.2.2.2.1.trans hBd, hreg.2.2.2.2.2.1.trans hBLk,
    by rw [hmloc]; rfl, by rw [hmloc]; exact hreg.2.2.2.2.2.2.symm,
    by rw [hmloc]; exact hBLk,
    (hagMeta _ hhbFoot).trans (by rw [← solverSelectHeapAddr_eq_four_two]; exact hhbAddr),
    Or.inl hhbFoot,
    fun a h1 h2 => by rw [hown]; exact ⟨h1, by omega⟩,
    fun a h1 h2 => by rw [hown]; rw [← hBd] at h2; exact ⟨by omega, by omega⟩,
    fun i hi => ?_, hmatch', hmeta'⟩
  have hiB : i < B.d := hBd.symm ▸ hi
  have hblkEnd := B.blk_le_last (Nat.le_of_lt hiB)
  have hlastEnd : B.lastGPtr ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hembLo : B.base ≤ B.embPtr i := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
      SelectBlocksLoc.fPtr; omega
  have hembEnd := B.blkEnd_eq i
  have hembEq := B.embPtr_eq i
  refine ⟨fun a h1 h2 => by
      rw [hmloc] at h1 h2; simp only [selectMlocOf] at h1 h2
      rw [hown]; exact ⟨by omega, by omega⟩,
    fun e he t ht => ?_⟩
  obtain ⟨heCap, hslotPtr, hlenLe, _⟩ := hblocks'.2.2.2.2.2.1 i hiB e he
  have hptr : mem' (sg.mloc.embPtr i + e) = B.slotPtr i e := by
    rw [hmloc]; simp only [selectMlocOf]; exact hslotPtr
  rw [hptr, hown]
  have htSlot : t < B.slot := lt_of_lt_of_le ht hlenLe
  have hmul := mul_add_lt_mul_sb heCap htSlot
  refine ⟨by unfold SelectBlocksLoc.slotPtr; omega, by unfold SelectBlocksLoc.slotPtr; omega⟩

/-- **Preservation across non-level-changing steps:** any step satisfying `PreservesLevelMeta`
that preserves `[sg.loc.hb, B.endAddr)` and keeps `foot'` disjoint from `sg.owned` preserves
`SolverSelectBlocksInv` with the exact same `sg`. -/
theorem SolverSelectBlocksInv.preserve_of_levelMeta {cfg : Alg2Config} {G : MGraph}
    {L P V m vCap eCap pLast : ℕ} {B : SelectBlocksLoc}
    {model model' : Alg2State cfg} {foot foot' : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {sg : SelectGhost} {mem mem' : ℕ → ℕ}
    (hblk : SolverSelectBlocksInv G L P m vCap eCap pLast B model foot tok sg mem)
    (hcaps : SolverLevelMetaAt P V model tok mem)
    (hpres : PreservesLevelMeta tok tok' mem mem')
    (hfoot' : ∀ a, sg.owned a → ¬ foot' a)
    (hagOwn : ∀ a, sg.loc.hb ≤ a → a < B.endAddr → mem' a = mem a)
    (hchain : model'.chain.toTreeChain = model.chain.toTreeChain)
    (hg : model'.chain.g = model.chain.g)
    (hℓ : model'.chain.ℓ = model.chain.ℓ)
    (hmod' : ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ), SelectModelInv model' G₀ σ σ_mwu γ_ℓ γ_c) :
    SolverSelectBlocksInv G L P m vCap eCap pLast B model' foot' tok' sg mem' := by
  obtain ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown, _, hhbAddr, hblkAddr, hmloc, hclen,
    htab, hblocks, hpot, hmatch, _⟩ := hblk
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  have htabEq : tok'.table = tok.table := hpres.1
  have hmemMeta : ∀ a, LevelMetaFoot tok a → mem' a = mem a := fun a ha => (hpres.metaEq a ha).2
  have hGeq : ∀ j < cfg.P.d, solverLevelG tok' mem' j = solverLevelG tok mem j := fun j hj => by
    unfold solverLevelG
    rw [htabEq]
    have htag : tok.tag (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
      have := hcaps.2.2.2.2.1 (cfg.P.d + j) (by omega)
      simpa [Nat.add_assoc] using this
    exact hmemMeta _ (Or.inr (Or.inr (Or.inl htag)))
  have hmlocEq : selectMlocOf B sg.loc.metaPtr (solverLevelG tok' mem') pLast =
      selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem) pLast := by
    unfold selectMlocOf
    congr 1
    · funext j; split_ifs with h
      · exact hGeq j (hBd ▸ h)
      · rfl
    · funext j; split_ifs with h1 h2
      · exact hGeq (j + 1) (hBd ▸ h1)
      · rfl
      · rfl
  refine ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown, hfoot',
    by rw [htabEq]; exact (hmemMeta _ (Or.inr (Or.inl hcaps.1.2.2.1))).trans hhbAddr,
    by rw [htabEq]; exact (hmemMeta _ (Or.inr (Or.inl hcaps.1.2.2.2))).trans hblkAddr,
    hmloc.trans hmlocEq.symm, by rw [hchain, hℓ]; exact hclen,
    htab.of_agree fun a h1 h2 => hagOwn a
      (by rw [hmloc] at h1; simp only [selectMlocOf] at h1; omega)
      (by rw [hmloc] at h2; simp only [selectMlocOf] at h2; omega),
    by rw [hchain, hg, hℓ]; exact hblocks.of_agree fun a h1 h2 => hagOwn a (by omega) h2,
    by rw [hchain, hg]; exact hpot,
    by rw [hchain, hg, hℓ]; exact hmatch.of_agree fun a h1 h2 => hagOwn a h1 (by omega),
    hmod'⟩

/-! ## Disjointness and `selectPhiFill` prefix hypotheses from `SelectRegion` -/

/-- `SelectMetaDisjoint` from `SelectRegion`, `SolverLevelCapsInv`, and every cell of
`foot ∨ sg.owned` lying below `hi`. -/
theorem selectMetaDisjoint_of_solver_region {cfg : Alg2Config} {L P V vCap eCap pLast hi : ℕ}
    {B : SelectBlocksLoc} {loc : SelectHeapLoc} {model : Alg2State cfg} {foot : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap)
    (hreg : SelectRegion loc.hb loc B loc.metaPtr)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hmetaSub : ∀ a, LevelMetaFoot tok a → foot a)
    (hoff : ∀ a, loc.hb ≤ a → a < B.endAddr → ¬ foot a)
    (hbelow : ∀ a, foot a ∨ (loc.hb ≤ a ∧ a < B.endAddr) → a < hi) :
    SelectMetaDisjoint (selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast) loc hi := by
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  have hszPos : 0 < selectHeapSize loc.cap loc.d loc.Lk := by
    unfold selectHeapSize shHdrSize; omega
  have hEndPos : loc.hb < B.endAddr := by rw [loc.endAddr_eq] at hlo2; omega
  have hBEnd : B.endAddr ≤ hi := by
    have := hbelow (B.endAddr - 1) (Or.inr ⟨by omega, by omega⟩)
    omega
  refine selectMetaDisjoint_of_region hreg hBEnd fun j hj => ?_
  have hjd : j < cfg.P.d := hBd ▸ hj
  have hGtags := (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hjd).2.2.2.2
  have hGszPos : 0 < dynGraphSize B.vCap B.eCap := by unfold dynGraphSize; omega
  have hGfoot : ∀ a, solverLevelG tok mem j ≤ a →
      a < solverLevelG tok mem j + dynGraphSize B.vCap B.eCap → foot a := fun a h1 h2 => by
    rw [hBv, hBe] at h2
    have ht := hGtags a h1 h2
    refine hmetaSub a ?_
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0] at ht
      exact Or.inl ht
    · rw [ite_eq_right hj0] at ht
      exact Or.inr (Or.inr (Or.inr ht))
  have hGhi : solverLevelG tok mem j + dynGraphSize B.vCap B.eCap ≤ hi := by
    have := hbelow (solverLevelG tok mem j + dynGraphSize B.vCap B.eCap - 1)
      (Or.inl (hGfoot _ (by omega) (by omega)))
    omega
  refine ⟨hGhi, ?_⟩
  by_contra h
  push Not at h
  let a := max (solverLevelG tok mem j) loc.hb
  have hf : foot a := hGfoot a (le_max_left _ _) (max_lt (by omega) (by omega))
  have ho : loc.hb ≤ a ∧ a < B.endAddr :=
    ⟨le_max_right _ _, max_lt (by omega) (by omega)⟩
  exact hoff a ho.1 ho.2 hf

/-- `SelectPhiPrefixAt`, `SelectPhiPrefixBelow`, and `SelectPhiTargetDisjoint` at any level `j ≤ d`
from `SelectRegion`, `SelectMetaTableAt`, `SelBlocksDataAt` (matching `C` on levels `< j` and `g`
on `G_0`), and `SolverLevelCapsInv`. -/
theorem selectPhiFill_hyps_of_blocks {cfg : Alg2Config} {L P V vCap eCap pLast j hi : ℕ}
    {B : SelectBlocksLoc} {loc : SelectHeapLoc} {model : Alg2State cfg} {foot : ℕ → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    {D : SelBlocksData}
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap)
    (hj : j ≤ cfg.P.d)
    (hreg : SelectRegion loc.hb loc B loc.metaPtr)
    (htab : SelectMetaTableAt mem (selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast))
    (hD : SelBlocksDataAt mem B P D pLast)
    (hDG0 : D.E0 = (model.chain.G 0).E ∧ D.g = model.chain.g)
    (hDV : ∀ k < j, D.V k = (model.chain.G k).V)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hmetaSub : ∀ a, LevelMetaFoot tok a → foot a)
    (hoff : ∀ a, loc.hb ≤ a → a < B.endAddr → ¬ foot a)
    (hbelow : ∀ a, foot a ∨ (loc.hb ≤ a ∧ a < B.endAddr) → a < hi) :
    let mloc := selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast
    SelectPhiPrefixAt mem mloc 4 P model.chain.toTreeChain model.chain.g D.φ j ∧
    SelectPhiPrefixBelow mloc j hi ∧
    SelectPhiTargetDisjoint mloc j hi := by
  intro mloc
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  have hEndPos : loc.hb < B.endAddr := by
    have : 0 < selectHeapSize loc.cap loc.d loc.Lk := by unfold selectHeapSize shHdrSize; omega
    rw [loc.endAddr_eq] at hlo2; omega
  have hBEnd : B.endAddr ≤ hi := by
    have := hbelow (B.endAddr - 1) (Or.inr ⟨by omega, by omega⟩); omega
  have hGprops : ∀ k < cfg.P.d,
      DynGraphAt mem (solverLevelG tok mem k) B.vCap B.eCap (model.chain.G k) ∧
      solverLevelG tok mem k + dynGraphSize B.vCap B.eCap ≤ hi ∧
      (solverLevelG tok mem k + dynGraphSize B.vCap B.eCap ≤ B.phiPtr j ∨
        B.phiPtr j + B.vCap * B.Lk ≤ solverLevelG tok mem k) := by
    intro k hk
    have hAt := SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 k hk
    have hDG : DynGraphAt mem (solverLevelG tok mem k) B.vCap B.eCap (model.chain.G k) := by
      rw [hBv, hBe]; exact hAt.1
    have hGszPos : 0 < dynGraphSize B.vCap B.eCap := by unfold dynGraphSize; omega
    have hGfoot : ∀ a, solverLevelG tok mem k ≤ a →
        a < solverLevelG tok mem k + dynGraphSize B.vCap B.eCap → foot a := fun a h1 h2 => by
      rw [hBv, hBe] at h2
      have ht := hAt.2.2.2.2 a h1 h2
      refine hmetaSub a ?_
      by_cases hk0 : k = 0
      · rw [ite_eq_left hk0] at ht; exact Or.inl ht
      · rw [ite_eq_right hk0] at ht; exact Or.inr (Or.inr (Or.inr ht))
    have hGhi : solverLevelG tok mem k + dynGraphSize B.vCap B.eCap ≤ hi := by
      have := hbelow (solverLevelG tok mem k + dynGraphSize B.vCap B.eCap - 1)
        (Or.inl (hGfoot _ (by omega) (by omega))); omega
    have hPhiIn : loc.hb ≤ B.phiPtr j ∧ B.phiPtr j + B.vCap * B.Lk ≤ B.endAddr := by
      have h1 := B.blk_le_last (hBd.symm ▸ hj)
      have h2 := B.blkEnd_eq j
      have h3 := B.phiPtr_eq j
      unfold SelectBlocksLoc.fPtr SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at *; omega
    refine ⟨hDG, hGhi, ?_⟩
    by_contra h
    push Not at h
    by_cases h0 : B.vCap * B.Lk = 0
    · have hlt1 : B.phiPtr j < solverLevelG tok mem k + dynGraphSize B.vCap B.eCap := h.1
      have hlt2 : solverLevelG tok mem k < B.phiPtr j := by omega
      have hPhiLtEnd : B.phiPtr j < B.endAddr := by
        have h1 := B.blk_le_last (hBd.symm ▸ hj)
        have h2 := B.blkEnd_eq j
        have h3 := B.phiPtr_eq j
        have hposLast : 0 < dynGraphSize B.vCap B.eCap := by unfold dynGraphSize; omega
        unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at *; omega
      exact hoff (B.phiPtr j) hPhiIn.1 hPhiLtEnd (hGfoot (B.phiPtr j) (le_of_lt hlt2) hlt1)
    · let a := max (solverLevelG tok mem k) (B.phiPtr j)
      have haPhi : a < B.phiPtr j + B.vCap * B.Lk := max_lt h.2 (by omega)
      exact hoff a (le_trans hPhiIn.1 (le_max_right _ _))
        (lt_of_lt_of_le haPhi hPhiIn.2)
        (hGfoot a (le_max_left _ _) (max_lt (by omega) h.1))
  have hblkEndJ : B.fPtr j + B.levelSize ≤ B.lastGPtr := B.blk_le_last (hBd.symm ▸ hj)
  have hPhiJEnd : B.phiPtr j + B.vCap * B.Lk ≤ B.lastGPtr := by
    have := B.blkEnd_eq j; have := B.phiPtr_eq j; omega
  have hFJEnd : B.fPtr j + dynGraphSize B.vCap B.eCap ≤ B.phiPtr j := by
    rw [B.phiPtr_eq j]
  refine ⟨⟨hBd, htab.1, htab.2.1, ?_, fun k hk => ?_⟩, ⟨?_, ?_, fun k hk => ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩⟩
  · simp only [mloc, selectMlocOf]
    change EdgeValuesAt mem B.g0Ptr 4 B.Lk P (model.chain.G 0).E model.chain.g
    simpa only [hDG0.1, hDG0.2] using hD.2.2.2.2.2.2
  · have hkd : k < cfg.P.d := by omega
    have hkB : k < B.d := hBd.symm ▸ hkd
    have hent := htab.2.2 k (Nat.le_of_lt hkB)
    refine ⟨hent.1, hent.2.1, hent.2.2.1, hent.2.2.2.1, ?_, ?_⟩
    · simp only [mloc, selectMlocOf, hkB, ↓reduceIte]
      exact (hGprops k hkd).1
    · simp only [mloc, selectMlocOf]
      have hpk := (hD.2.1 k (Nat.le_of_lt hkB)).2
      rwa [hDV k hk] at hpk
  · simp only [mloc, selectMlocOf]; omega
  · simp only [mloc, selectMlocOf]; unfold SelectBlocksLoc.endAddr at hBEnd; exact hBEnd
  · have hkd : k < cfg.P.d := by omega
    have hkB : k < B.d := hBd.symm ▸ hkd
    have hblkK := B.blk_le_last (Nat.le_of_lt hkB)
    have hPhiK := B.phiPtr_eq k; have hEndK := B.blkEnd_eq k
    simp only [mloc, selectMlocOf, hkB, ↓reduceIte]
    exact ⟨(hGprops k hkd).2.1, by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega⟩
  · simp only [mloc, selectMlocOf]
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
  · simp only [mloc, selectMlocOf]
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
  · left; simp only [mloc, selectMlocOf]
    unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
  · right; simp only [mloc, selectMlocOf]
    unfold SelectBlocksLoc.g0Ptr; omega
  · left; simp only [mloc, selectMlocOf]; exact hFJEnd
  · have hkd : k < cfg.P.d := by omega
    have hkB : k < B.d := hBd.symm ▸ hkd
    have hltKJ := B.blk_le_of_lt hk
    have hEndK := B.blkEnd_eq k; have hPhiK := B.phiPtr_eq k
    simp only [mloc, selectMlocOf, hkB, ↓reduceIte]
    exact ⟨(hGprops k hkd).2.2, Or.inl (by unfold SelectBlocksLoc.phiPtr; omega)⟩

end MinCostFlow.MinRatio
