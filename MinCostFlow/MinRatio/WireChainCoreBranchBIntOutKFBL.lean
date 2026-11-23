module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntRebNewKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBIntTailKFBL

/-!
# The interior step of Branch B and its end state under `KFBL` (`WireChainCoreBranchBIntOutKFBL`)

When the plain-step loop of Branch B exits at a level `i₀` with `0 < i₀ < d`, the counter of
level `i₀` passed its threshold, so the levels from `i₀` on are rebuilt. The interior step
`wireBranchBIntKFBL` has three parts:
1. `wireBranchBIntOldKFBL`: collect the old forests of the levels `j ≥ i₀`, apply the batch to the
   graph of level `i₀`, read the order list of level `i₀ - 1` and count the rebuild;
2. `wireBranchBIntSuffixKFBL ;; wireBranchBIntNewStmt`: rebuild the levels from `i₀` on and the
   last level, then collect their new forests;
3. `wireBranchBIntTailKFBL`: zero the update counters of the rebuilt levels, store
   `firstReb = i₀` at the select base, and read the descriptor of level `i₀ - 1` again.

This file gives the step, the facts `BranchBIntOutKFBL` at its end state, and small layout lemmas
that the run lemma `wireBranchBIntKFBL_runs_exit` (in `WireChainCoreBranchBIntExitKFBL`) uses:
the words of the fixed arrays are static words, and a core footprint is off the fixed arrays and
off every graph block.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The interior step of Branch B: the first part, the suffix rebuild with the new-forest
collection, and the tail. -/
@[expose] def wireBranchBIntKFBL (dgApply init readGraph readLSF coreLenProc readOrd
    lastInit : ℕ) : Stmt :=
  wireBranchBIntOldKFBL dgApply readOrd readLSF ;;
  (wireBranchBIntSuffixKFBL init readGraph readLSF coreLenProc readOrd lastInit ;;
    wireBranchBIntNewStmt readLSF) ;;
  wireBranchBIntTailKFBL readLSF

theorem wireBranchBIntKFBL_noRand (dgApply init readGraph readLSF coreLenProc readOrd
    lastInit : ℕ) :
    (wireBranchBIntKFBL dgApply init readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchBIntKFBL, wireBranchBIntOldKFBL_noRand, wireBranchBIntSuffixKFBL_noRand,
    wireBranchBIntNewStmt_noRand, wireBranchBIntTailKFBL_noRand, Stmt.NoRand]

/-- The facts at the end state `out` of the interior step, from the exit state `sE` of the loop
at the level `i₀`, for the rebuilt chain `next`. The core of level `j` is at the handle
`mem (handleBase + j)` with the token `tokN j`, and its footprint lies in its old one or in the
fresh heap `[sE.regs 4, out.regs 4)`. The slots of the levels below `i₀` are finished, and
`firstReb = i₀` is at the select base. The cells, graphs and lengths of all levels and the new
last level are those of `next`. The old forests of the levels `i₀, …, d` are listed at
`oldPtrs + i₀`, the new ones at `newPtrs + i₀`. Below the select base, the step writes only the
footprints of the old cores, the fixed arrays, the graph blocks and the update counters. Between
the select slots and the heap floor, it writes only the two arrays of forest pointers. -/
structure BranchBIntOutKFBL {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (A : BranchBAddrs) (oldPtrs newPtrs intCap i₀ : ℕ)
    (ch0 ch next : ChainState cfg.T cfg.P) (levelU : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (sE out : State) (tok tokN : ℕ → Rcore.τ) (termTokN : ℕ) : Prop where
  heapLo : sE.regs 4 ≤ out.regs 4
  zero : ZeroFrom out.mem (out.regs 4)
  r97 : out.regs 97 = 1
  regs : ∀ r, 70 ≤ r → r ≠ 97 → r ≠ 99 → out.regs r = sE.regs r
  handlesLow : ∀ j < i₀, out.mem (A.handleBase + j) = A.coreH j
  reps : ∀ j < cfg.P.d,
    Rcore.rep (out.mem (A.handleBase + j)) (chainLevelOrdAbs next j) (tokN j) out.mem ∧
    ∀ a, Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (sE.regs 4 ≤ a ∧ a < out.regs 4)
  disj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
    Rcore.foot (out.mem (A.handleBase + j₁)) (tokN j₁) a →
      ¬ Rcore.foot (out.mem (A.handleBase + j₂)) (tokN j₂) a
  slots : BranchBDoneSlots w P cfg.P.d
    (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
    (fun r => Rcore.foot (out.mem (A.handleBase + r)) (tokN r)) A.heapFloor (out.regs 4)
    A.selBase out.mem i₀ D ch0.G levelU (fun j => (ch.G j).E)
    (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr)
  sel : out.mem A.selBase = i₀
  cells : ∀ j < cfg.P.d, out.mem (A.branchBase + j) = next.bran j ∧
    out.mem (A.ucBase + j) = next.updCount j ∧ out.mem (A.rcBase + j) = next.rebuildCount j
  lastB : out.mem (A.branchBase + cfg.P.d) = next.lastBran
  graphs : ∀ j < cfg.P.d,
    DynGraphAt out.mem (out.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (next.G j)
  lens : ∀ j < cfg.P.d, EdgeValuesAt out.mem (out.mem (A.levelMeta + j)) 4 L P (next.G j).E
    (next.toTreeChain.chainLen next.ℓ j)
  lastRep : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G cfg.P.d).E).rep
    (out.mem (A.handleBase + cfg.P.d)) (next.lastK, next.lastLSFs) termTokN out.mem
  lastFoot : ∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
      (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
    sE.regs 4 ≤ a ∧ a < out.regs 4 ∧
    ∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a
  oldF : ForestPtrListAt out.mem (oldPtrs + i₀) (chainSuffixForests ch0 i₀) intCap (out.regs 4)
  newF : ForestPtrListAt out.mem (newPtrs + i₀) (chainSuffixForests next i₀) intCap (out.regs 4)
  frame : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
    (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) →
    (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) →
    (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) → (a < A.rcBase ∨ A.rcBase + cfg.P.d ≤ a) →
    (∀ j < cfg.P.d, a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) →
    (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) → out.mem a = sE.mem a
  frameHeap : ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
    (a < oldPtrs ∨ oldPtrs + (cfg.P.d + 1) ≤ a) → (a < newPtrs ∨ newPtrs + (cfg.P.d + 1) ≤ a) →
    out.mem a = sE.mem a

/-- A word of the handle array (with the cell of the last level) is a static word. -/
theorem BranchBStaticWord.hb {d x : ℕ} {A : BranchBAddrs} (h1 : A.handleBase ≤ x)
    (h2 : x ≤ A.handleBase + d) : BranchBStaticWord d A x := by
  unfold BranchBStaticWord; exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))

/-- A word of the branch array (with the cell of the last level) is a static word. -/
theorem BranchBStaticWord.bb {d x : ℕ} {A : BranchBAddrs} (h1 : A.branchBase ≤ x)
    (h2 : x ≤ A.branchBase + d) : BranchBStaticWord d A x := by
  unfold BranchBStaticWord; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))

/-- A word of the level-meta array is a static word. -/
theorem BranchBStaticWord.lm {d x : ℕ} {A : BranchBAddrs} (h1 : A.levelMeta ≤ x)
    (h2 : x < A.levelMeta + 2 * d) : BranchBStaticWord d A x := by
  unfold BranchBStaticWord; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))

/-- A rebuild counter is a static word. -/
theorem BranchBStaticWord.rc {d x : ℕ} {A : BranchBAddrs} (h1 : A.rcBase ≤ x)
    (h2 : x < A.rcBase + d) : BranchBStaticWord d A x := by
  unfold BranchBStaticWord; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))

/-- A footprint of a core is off the handle, branch, level-meta, update-counter and
rebuild-counter arrays, and off the graph block of every level. -/
theorem branchBCoresDisjStatic_footSep {L vCap eCap : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs} {tok : ℕ → Rcore.τ}
    (hst : BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L A.handle A.table A.handleBase
      A.branchBase A.lvlMTable A.levelMeta A.rcBase A.ucBase (fun _ => vCap) (fun _ => eCap)
      A.gPtr0 A.lPtr0 A.coreH tok)
    {r a : ℕ} (hr : r < cfg.P.d) (ha : Rcore.foot (A.coreH r) (tok r) a) :
    (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) ∧
    (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) ∧
    (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) ∧
    (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) ∧
    (a < A.rcBase ∨ A.rcBase + cfg.P.d ≤ a) ∧
    (∀ j < cfg.P.d, a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) := by
  obtain ⟨_, _, sHB, sM, sG, _⟩ := hst r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · by_contra hc
    simp only [not_or, not_lt] at hc
    exact (sHB (a - A.handleBase) (by omega)).1 (by rwa [Nat.add_sub_cancel' hc.1])
  · by_contra hc
    simp only [not_or, not_lt] at hc
    exact (sHB (a - A.branchBase) (by omega)).2 (by rwa [Nat.add_sub_cancel' hc.1])
  · by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    by_cases hlt : a < A.levelMeta + cfg.P.d
    · exact (sM (a - A.levelMeta) (by omega)).2.1 (by rwa [Nat.add_sub_cancel' hc.1])
    · exact (sM (a - A.levelMeta - cfg.P.d) (by omega)).2.2.1
        (by rwa [show A.levelMeta + cfg.P.d + (a - A.levelMeta - cfg.P.d) = a by omega])
  · by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    exact (sM (a - A.ucBase) (by omega)).2.2.2.1 (by rwa [Nat.add_sub_cancel' hc.1])
  · by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    exact (sM (a - A.rcBase) (by omega)).2.2.2.2 (by rwa [Nat.add_sub_cancel' hc.1])
  · by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    exact sG j hj a hc.1 hc.2 ha

/-- The words of the fixed arrays that the first two parts of the interior step at level `i₀`
keep: all words but the rebuild counter of level `i₀` and the handle, branch and level-meta
cells of the levels from `i₀` on. -/
@[expose] def BranchBIntKeepCell (d i₀ : ℕ) (A : BranchBAddrs) (x : ℕ) : Prop :=
  x ≠ A.rcBase + i₀ ∧ (x < A.handleBase + i₀ ∨ A.handleBase + d < x) ∧
  (x < A.branchBase + i₀ ∨ A.branchBase + d < x) ∧
  ((x < A.levelMeta + (i₀ + 1) ∨ A.levelMeta + d ≤ x) ∧
    (x < A.levelMeta + d + (i₀ + 1) ∨ A.levelMeta + 2 * d ≤ x))

/-- A word off the handle, branch, level-meta and rebuild-counter arrays is kept. -/
theorem BranchBIntKeepCell.of_sep {d i₀ x : ℕ} {A : BranchBAddrs}
    (h1 : x < A.handleBase ∨ A.handleBase + d < x)
    (h2 : x < A.branchBase ∨ A.branchBase + d < x)
    (h3 : x < A.levelMeta ∨ A.levelMeta + 2 * d ≤ x)
    (h4 : x < A.rcBase ∨ A.rcBase + d ≤ x) (hi : i₀ < d) : BranchBIntKeepCell d i₀ A x := by
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

section KeepCell

variable {d L vCap eCap i₀ j : ℕ} {A : BranchBAddrs}
  (S : BranchBStatic d L A.handle A.table A.handleBase A.branchBase A.lvlMTable A.levelMeta
    A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0 A.coreH)
include S

/-- The handle cell of a level below `i₀` is kept. -/
theorem BranchBIntKeepCell.hb (hj : j < i₀) (hi : i₀ < d) :
    BranchBIntKeepCell d i₀ A (A.handleBase + j) := by
  have := S.sepRCHB; have := S.sepHB; have := S.sepHL
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The branch cell of a level below `i₀` is kept. -/
theorem BranchBIntKeepCell.bb (hj : j < i₀) (hi : i₀ < d) :
    BranchBIntKeepCell d i₀ A (A.branchBase + j) := by
  have := S.sepRCBB; have := S.sepHB; have := S.sepBL
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The length pointer of a level up to `i₀` is kept. -/
theorem BranchBIntKeepCell.lm (hj : j ≤ i₀) (hi : i₀ < d) :
    BranchBIntKeepCell d i₀ A (A.levelMeta + j) := by
  have := S.sepRCLM; have := S.sepHL; have := S.sepBL
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The graph pointer of a level up to `i₀` is kept. -/
theorem BranchBIntKeepCell.lmd (hj : j ≤ i₀) (hi : i₀ < d) :
    BranchBIntKeepCell d i₀ A (A.levelMeta + d + j) := by
  have := S.sepRCLM; have := S.sepHL; have := S.sepBL
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The rebuild counter of a level other than `i₀` is kept. -/
theorem BranchBIntKeepCell.rc (hj : j < d) (hne : j ≠ i₀) :
    BranchBIntKeepCell d i₀ A (A.rcBase + j) := by
  have := S.sepRCHB; have := S.sepRCBB; have := S.sepRCLM
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- An update counter is kept by the first two parts. -/
theorem BranchBIntKeepCell.uc (hj : j < d) (hi : i₀ < d) :
    BranchBIntKeepCell d i₀ A (A.ucBase + j) := by
  have := S.sepRCUC; have := S.sepUCHB; have := S.sepUCBB; have := S.sepUCLM
  unfold BranchBIntKeepCell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The rebuild counter of level `i₀` is off the handle, branch and level-meta arrays. -/
theorem branchBInt_rc_frame (hi : i₀ < d) :
    (A.rcBase + i₀ < A.handleBase + i₀ ∨ A.handleBase + d < A.rcBase + i₀) ∧
    (A.rcBase + i₀ < A.branchBase + i₀ ∨ A.branchBase + d < A.rcBase + i₀) ∧
    ((A.rcBase + i₀ < A.levelMeta + (i₀ + 1) ∨ A.levelMeta + d ≤ A.rcBase + i₀) ∧
      (A.rcBase + i₀ < A.levelMeta + d + (i₀ + 1) ∨ A.levelMeta + 2 * d ≤ A.rcBase + i₀)) := by
  have := S.sepRCHB; have := S.sepRCBB; have := S.sepRCLM
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- An update counter is not a handle, branch or graph-pointer cell. -/
theorem branchBStatic_uc_ne {z k : ℕ} (h1 : A.ucBase ≤ z) (h2 : z < A.ucBase + d)
    (hk : k < d) :
    z ≠ A.handleBase + k ∧ z ≠ A.branchBase + k ∧ z ≠ A.levelMeta + d + k := by
  have := S.sepUCHB; have := S.sepUCBB; have := S.sepUCLM
  refine ⟨?_, ?_, ?_⟩ <;> omega

end KeepCell

end MinCostFlow.MinRatio

end
