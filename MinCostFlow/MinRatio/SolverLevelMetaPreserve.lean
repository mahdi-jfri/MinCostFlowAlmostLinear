module

public import MinCostFlow.MinRatio.SolverRep

/-!
# Preservation of the level-metadata region across non-level-changing solver steps

Defines `PreservesLevelMeta tok tok' mem mem'`, capturing that a solver step preserves:
- `tok.table` (and hence the addresses `n0Cell`, `lvlMTable`, and `levelMeta`),
- every sparse-core handle `tok.coreHandle j` for `j < cfg.P.d`,
- token ownership (`tok.owned ⊆ tok'.owned`), and
- both tags and memory contents on every address in the level-metadata regions
  (tags `20`, `21 + d`, `22 + d`, `23 + d`).

Defined in a leaf module importing only `SolverRep` so every non-level-changing solver
procedure (`Query`, `Detect`, `Update` prep/grow/goodApply/loop, cycle select/eval, terminal
shift) can export `PreservesLevelMeta` without introducing cyclic imports.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain SparseCore.Program

/-- Addresses of the solver's level-metadata region (tags `20`, `21 + d`, `22 + d`, `23 + d`),
including `n0Cell`, `lvlMTable`, `levelMeta`, `selectHeap`, `selectBlocks`, all per-level
length arrays, and all non-terminal level graphs `G_0, …, G_{d-1}`. -/
@[expose] def LevelMetaFoot {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (a : ℕ) : Prop :=
  tok.tag a = 20 ∨ tok.tag a = 21 + cfg.P.d ∨ tok.tag a = 22 + cfg.P.d ∨ tok.tag a = 23 + cfg.P.d

/-- A solver transition from `(tok, mem)` to `(tok', mem')` preserves the level-metadata region:
the table pointer, root edge capacity, all non-terminal core handles, ownership monotonicity,
and both tags and memory values on every address in `LevelMetaFoot tok`. -/
@[expose] def PreservesLevelMeta {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok tok' : SolverToken cfg L Rcore) (mem mem' : ℕ → ℕ) : Prop :=
  tok'.table = tok.table ∧
  tok'.rootECap = tok.rootECap ∧
  tok'.rootGraph = tok.rootGraph ∧
  (∀ j < cfg.P.d, tok'.coreHandle j = tok.coreHandle j) ∧
  (∀ a, tok.owned a → tok'.owned a) ∧
  (∀ a, LevelMetaFoot tok a → tok'.tag a = tok.tag a ∧ mem' a = mem a)

theorem LevelMetaFoot.tag_ne_zero {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {a : ℕ}
    (h : LevelMetaFoot tok a) : tok.tag a ≠ 0 := by
  rcases h with h | h | h | h <;> omega

theorem LevelMetaFoot.mem_foot {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    {a : ℕ} (ha : LevelMetaFoot tok a) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a :=
  Or.inl (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha.tag_ne_zero)

theorem PreservesLevelMeta.levelMetaFoot_mono {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} (h : PreservesLevelMeta tok tok' mem mem')
    {a : ℕ} (ha : LevelMetaFoot tok a) : LevelMetaFoot tok' a := by
  unfold LevelMetaFoot at ha ⊢
  rw [(h.2.2.2.2.2 a ha).1]
  exact ha

theorem PreservesLevelMeta.tableEq {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} (h : PreservesLevelMeta tok tok' mem mem') :
    tok'.table = tok.table := h.1

theorem PreservesLevelMeta.rootECapEq {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} (h : PreservesLevelMeta tok tok' mem mem') :
    tok'.rootECap = tok.rootECap := h.2.1

theorem PreservesLevelMeta.rootGraphEq {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} (h : PreservesLevelMeta tok tok' mem mem') :
    tok'.rootGraph = tok.rootGraph := h.2.2.1

theorem PreservesLevelMeta.metaEq {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} (h : PreservesLevelMeta tok tok' mem mem') :
    ∀ a, tok.tag a = 20 ∨ tok.tag a = 21 + cfg.P.d ∨ tok.tag a = 22 + cfg.P.d ∨
        tok.tag a = 23 + cfg.P.d →
      tok'.tag a = tok.tag a ∧ mem' a = mem a := h.2.2.2.2.2

theorem PreservesLevelMeta.refl {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) :
    PreservesLevelMeta tok tok mem mem :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ h => h, fun _ _ => ⟨rfl, rfl⟩⟩

theorem PreservesLevelMeta.trans {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok₁ tok₂ tok₃ : SolverToken cfg L Rcore} {mem₁ mem₂ mem₃ : ℕ → ℕ}
    (h₁₂ : PreservesLevelMeta tok₁ tok₂ mem₁ mem₂)
    (h₂₃ : PreservesLevelMeta tok₂ tok₃ mem₂ mem₃) :
    PreservesLevelMeta tok₁ tok₃ mem₁ mem₃ := by
  refine ⟨h₂₃.1.trans h₁₂.1, h₂₃.2.1.trans h₁₂.2.1, h₂₃.2.2.1.trans h₁₂.2.2.1,
    fun j hj => (h₂₃.2.2.2.1 j hj).trans (h₁₂.2.2.2.1 j hj),
    fun a ha => h₂₃.2.2.2.2.1 a (h₁₂.2.2.2.2.1 a ha), fun a ht => ?_⟩
  have h1 := h₁₂.2.2.2.2.2 a ht
  have ht2 : tok₂.tag a = 20 ∨ tok₂.tag a = 21 + cfg.P.d ∨ tok₂.tag a = 22 + cfg.P.d ∨
      tok₂.tag a = 23 + cfg.P.d := by
    rw [h1.1]; exact ht
  have h2 := h₂₃.2.2.2.2.2 a ht2
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem PreservesLevelMeta.congr_mem_right {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok tok' : SolverToken cfg L Rcore} {mem mem₁ mem₂ : ℕ → ℕ}
    (h : PreservesLevelMeta tok tok' mem mem₁)
    (hag : ∀ a, LevelMetaFoot tok' a → mem₂ a = mem₁ a) :
    PreservesLevelMeta tok tok' mem mem₂ := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a ht => ?_⟩
  have h1 := h.2.2.2.2.2 a ht
  exact ⟨h1.1, (hag a (h.levelMetaFoot_mono ht)).trans h1.2⟩

end MinCostFlow.MinRatio
