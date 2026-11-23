module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHead
public import MinCostFlow.DynSpanner.Program.DynSpannerAffStage
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullSum

/-!
# The whole step of Algorithm 6 for `0 < j`: procedure and contract

One update `u` of Algorithm 6 (Theorem 8.2, page 64) at a level `j = chooseLevel L q (k + 1) > 0`
runs in three parts, each a procedure with a proved contract:
1. `dsStepHeadStmt` adds the touched vertices to `S_i` for `i < j`, empties `S_i` for `i ≥ j`,
   and applies `u` to `G`, `H` and the buckets;
2. `dsAffStageStmt` computes the affected edges `E_aff` and the graph `J` (lines 70–77);
3. `dsStepPosStmt` finishes the step (`Sparsify`, the re-embedding, the new level `j`, `U_H`
   and `D`) and ends in `StepOutPost`.
Between the first two parts, `dsWordSumStmt` adds up the lengths of the buckets of the levels
`j, …, L`, which the last part needs to place its buffers.

This file defines the procedure `dsStepPosFullStmt` that makes these calls, the bounds on its heap
(`dsStepPosFullEnd`, `dsStepPosFullAffEnd`), its cost (`dsStepPosFullCost`) and its contract
(`dsStepPosFullContract`), whose pre is the state before the step and whose post is
`StepOutPost`. The proof is `dsStepPosFull_meetsContract` (`DynSpannerStepPosFull.lean`).

Layout of the step's heap, from `heapStep` on: the five words of the output header, the records of
`restrictUpdate u H` (at most `len` words, `len` the length of the record of `u`), the heap of
`dsUpdateSLevels` (at most `4 · j` words), and from `heapAff = heapStep + 5 + len + 4 · j` on the
heap of `dsAffStage` and of the last part.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## The procedure -/

/-- `args = [b, j, updPtr, heapStep, len]`. The addresses of the state block are computed from
`vCap`, `eCap` and `L` in the header. Returns what `dsStepPosStmt` returns. -/
def dsStepPosFullStmt (bH bW bA bP : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 7 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 5)))
    (.bin .mul (.const 9) (.reg 6))) ;;
  .assign 8 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 7)) ;;
  .assign 10 (.bin .add (.bin .add (.reg 9) (.reg 7)) (.reg 7)) ;;
  .assign 11 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
  .assign 12 (.bin .add (.reg 3) (.const 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 4)) ;;
  .call 14 (bH + stepHeadIdx)
    [.reg 0, .reg 1, .reg 2, .reg 13, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12] ;;
  .assign 15 (.bin .add (.reg 13) (.bin .mul (.const 4) (.reg 1))) ;;
  .assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const dsLOff))) (.const 1)) ;;
  .assign 16 (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 6))) (.reg 17)) ;;
  .call 18 (bW + wordSumIdx) [.reg 16, .reg 1, .reg 17] ;;
  .call 19 (bA + affStageIdx) [.reg 0, .reg 1, .reg 15] ;;
  .assign 20 (.load (.reg 15)) ;;
  .assign 21 (.load (.bin .add (.reg 15) (.const 1))) ;;
  .assign 22 (.bin .add (.bin .add (.bin .add (.reg 15) (.const 2)) (.reg 20)) (.reg 21)) ;;
  .call 23 (bP + stepPosIdx)
    [.reg 0, .reg 1, .reg 22, .reg 19, .reg 21, .reg 18, .reg 3, .reg 14, .reg 15, .reg 20] ;;
  .store (.reg 23) (.reg 22) ;;
  .store (.bin .add (.reg 23) (.const 1)) (.reg 19) ;;
  .ret (.bin .add (.reg 23) (.const 2))

def stepPosFullProcs (bH bW bA bP : ℕ) : List Stmt := [dsStepPosFullStmt bH bW bA bP]

def stepPosFullIdx : ℕ := 0

lemma stepPosFullProcs_noRand (bH bW bA bP : ℕ) :
    ∀ s ∈ stepPosFullProcs bH bW bA bP, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · simp [dsStepPosFullStmt, Stmt.NoRand]
  cases hs

/-! ## The model objects of the step -/

/-- The bucket lists of the levels before the step, indexed by `ℕ` (empty above `L`). -/
abbrev stepPosBmid0 {L : ℕ} (x : DynSpannerMeta L) : ℕ → List ℕ :=
  fun i => if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else []

/-- The bucket lists of the levels after `u` is applied: `delErase u` of the old ones. -/
abbrev stepPosBmid {L : ℕ} (u : Update) (x : DynSpannerMeta L) : ℕ → List ℕ :=
  fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])

/-- The total length of the buckets of the levels `j, …, L` after `u` is applied. -/
abbrev stepPosOldSum {L : ℕ} (u : Update) (x : DynSpannerMeta L) (j : ℕ) : ℕ :=
  (bucketsCat (stepPosBmid u x) j (L + 1 - j)).length

/-- The objects of one step of Algorithm 6 at `0 < j`, as functions of the state before it. -/
structure StepPosModel where
  G₀ : MGraph
  impl : SparsifyImpl
  L : ℕ
  q : ℕ
  k : ℕ
  us : List Update
  u : Update

namespace StepPosModel

noncomputable abbrev st (m : StepPosModel) : DynSpannerState m.L :=
  runState (L := m.L) m.G₀ m.q (canonicalSparsify m.impl) m.us m.k

noncomputable abbrev res (m : StepPosModel) : StepOut m.L :=
  step m.st m.u (canonicalSparsify m.impl)

abbrev j (m : StepPosModel) : ℕ := chooseLevel m.L m.q (m.k + 1)

noncomputable abbrev G' (m : StepPosModel) : MGraph := m.st.G.applyUpdate m.u

noncomputable abbrev H_mid (m : StepPosModel) : Fin (m.L + 1) → MGraph :=
  fun i => (m.st.H_level i).applyBatch (restrictUpdate m.u (m.st.H_level i))

noncomputable abbrev inDom_mid (m : StepPosModel) : Fin (m.L + 1) → Finset ℕ :=
  fun i => m.st.inDom i ∩ m.G'.E

noncomputable abbrev S_prev (m : StepPosModel) : Finset ℕ :=
  m.st.S_level ⟨m.j - 1, by
      have : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
      omega⟩ ∪
    touchedVertices m.st.G m.u

noncomputable abbrev H_lt (m : StepPosModel) : MGraph := unionGraphLt m.G' m.H_mid m.j

noncomputable abbrev piLt_mid (m : StepPosModel) : Embedding :=
  piLtFrom m.st.Pi_level m.inDom_mid m.j

noncomputable abbrev E_aff (m : StepPosModel) : Finset ℕ :=
  affectedEdges m.G' m.H_lt m.piLt_mid m.S_prev

noncomputable abbrev J (m : StepPosModel) : MGraph :=
  buildProjGraph m.G' m.H_lt m.piLt_mid m.S_prev m.E_aff

noncomputable abbrev embJH (m : StepPosModel) : Embedding :=
  projWalk m.G' m.H_lt m.piLt_mid m.S_prev

end StepPosModel

/-! ## Heap bounds and cost -/

/-- The end of the heap of the step, with `heapStep` its start and `len` the length of the record
of `u`. It is the bound `hEnd_ltw` of `StepPosCtx`, with the lists of the program replaced by the
model sets they enumerate (`E_aff`, `S_{j-1}`) or by a bound (`|E(G')|` for the candidates). -/
noncomputable def dsStepPosFullEnd (m : StepPosModel) (mMax vCap eCap len : ℕ)
    (x : DynSpannerMeta m.L) (heapStep : ℕ) : ℕ :=
  let oldSum := stepPosOldSum m.u x m.j
  let eAffPtr := heapStep + 5 + len + 4 * m.j + 2 + m.S_prev.card + m.G'.m
  (if 0 < m.E_aff.card then
    dsStepPosNonEmptyEnd m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH m.E_aff.toList
      (eAffPtr + m.E_aff.card) m.G'.m oldSum
   else eAffPtr + m.G'.m + eCap + 1 + 2 * oldSum) + len + 4 * m.res.UH.length + 2

/-- The end of the heap that `dsAffStage` may use (its precondition), with the candidates bounded
by `E(G')`. -/
noncomputable def dsStepPosFullAffEnd (m : StepPosModel) (vCap eCap len heapStep : ℕ) : ℕ :=
  heapStep + 5 + len + 4 * m.j + 2 + vCap + 3 * eCap +
    ∑ e ∈ m.G'.E, (14 * (m.piLt_mid e).length + 15)

/-- The candidates of `dsAffStage` (Algorithm 6, line 71): the edges of `G'` on a reverse list
`x.revLists i v` of a vertex `v ∈ S_{j-1}` at a level `i < j`. -/
noncomputable def stepPosCandSet (m : StepPosModel) (x : DynSpannerMeta m.L) : Finset ℕ :=
  revCandSet m.L m.j x.revLists m.S_prev m.G'

/-- The cost of `dsAffStage` in the step, stated with the set of candidates. -/
noncomputable def dsStepPosFullAffCost (m : StepPosModel) (x : DynSpannerMeta m.L) : ℕ :=
  100 * candRevSum m.L m.j x.revLists m.S_prev.toList + 100 * (m.j * m.S_prev.card) +
    100 * m.S_prev.card + 100 * m.j +
    100 * (∑ e ∈ stepPosCandSet m x, (m.piLt_mid e).length) +
    40 * ((stepPosCandSet m x).card * m.j) + 160 * (stepPosCandSet m x).card +
    m.E_aff.card * (35 * m.j + 60) +
    (∑ e ∈ m.E_aff, (800 * (m.piLt_mid e).length + 2000)) + 1200

/-- The cost of the whole step for `0 < j`: `dsStepHead`, the bucket sum, `dsAffStage`,
`dsStepPos`, and the work of the procedure itself. -/
noncomputable def dsStepPosFullCost (m : StepPosModel) (mMax vCap eCap len : ℕ)
    (x : DynSpannerMeta m.L) : ℕ :=
  (500 * (m.L + 1) + 1320 * len + 1100) + (20 * (m.L + 1 - m.j) + 20) +
    dsStepPosFullAffCost m x +
    dsStepPosCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
      m.E_aff.toList (stepPosOldSum m.u x m.j) m.S_prev.card len m.res.UH.length + 330

/-! ## The contract -/

/-- Contract of `dsStepPosFullStmt` for the update `u = us[k]` when `0 < j`. The pre is the state
before the step (`DynSpannerStateAt`, `SnapInv` up to `k`, `RevHistoryInv` at `k`), the record of
`u` at `updPtr` (after the state block and outside its footprint), zero memory from `heapStep` on,
and the two heap bounds. The post is `StepOutPost`, a bound on the returned pointer, and the bound
`mem' gen ≤ mem gen + j + 3 + |E(G')|` on the generation word (the branch `j = 0` has
`mem' gen ≤ mem gen + 2 + |E(G')|`). -/
noncomputable def dsStepPosFullContract (m : StepPosModel) (mMax w vCap eCap b len : ℕ)
    (x : DynSpannerMeta m.L) : Contract where
  pre args mem := ∃ updPtr heapStep,
    args = [b, m.j, updPtr, heapStep, len] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ m.L ∧ 1 ≤ m.q ∧
    m.G₀.IsValid ∧ m.G₀.m ≤ mMax ∧ (∀ e ∈ m.G₀.E, e < eCap) ∧
    m.G₀.BatchIsValid m.us ∧ (∀ u' ∈ m.us, isDelOrSplit u') ∧ m.us[m.k]? = some m.u ∧
    0 < m.j ∧
    (∀ s ≤ m.k, SnapInv m.G₀ m.L m.q mMax (canonicalSparsifyParams m.impl mMax).absorbTime
      (canonicalSparsify m.impl) m.us s) ∧
    RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x ∧
    DynSpannerStateAt m.L vCap eCap b mem x m.st ∧
    b + dsFixedSize m.L vCap eCap ≤ heapStep ∧
    (∀ a, heapFoot x a → a < heapStep) ∧
    ZeroFrom mem heapStep ∧
    dsStepPosFullEnd m mMax vCap eCap len x heapStep < 2 ^ w ∧
    dsStepPosFullAffEnd m vCap eCap len heapStep < 2 ^ w ∧
    mem (b + dsGenOff) + m.j + 4 + m.G'.m < 2 ^ w ∧
    m.k + 1 < 2 ^ w ∧
    b + dsFixedSize m.L vCap eCap ≤ updPtr ∧ updPtr + len ≤ heapStep ∧
    (∀ i < len, ¬ metaFoot b x (updPtr + i)) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr m.st.G m.u len ∧
    UpdateWithinCaps vCap eCap m.u
  post args mem ret mem' := ∃ updPtr heapStep,
    args = [b, m.j, updPtr, heapStep, len] ∧
    StepReembOutPost m.G₀ m.L m.q vCap eCap b m.k m.impl m.us m.u mem x heapStep mem' ret ∧
    ret ≤ dsStepPosFullEnd m mMax vCap eCap len x heapStep ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + m.j + 3 + m.G'.m ∧
    mem' (heapStep + 2) ≤ len + 4 * m.res.UH.length
  cost _ _ := dsStepPosFullCost m mMax vCap eCap len x

/-! ## The procedure table -/

/-- The bases of the procedures that the whole step calls, besides those of the nonempty branch
(`StepPosNEBases`). -/
structure StepPosFullBases where
  ne : StepPosNEBases
  bAffP : ℕ
  bD : ℕ
  bU : ℕ
  bF : ℕ
  bR : ℕ
  bPref : ℕ
  bHead : ℕ
  bWP : ℕ
  bBP : ℕ
  bProj : ℕ
  bPS : ℕ
  bAS : ℕ
  bSum : ℕ
  bEm : ℕ
  bEp : ℕ
  bPos : ℕ
  bFull : ℕ

/-- Program `p` holds every procedure that `dsStepPosFullStmt` calls, directly or not. -/
structure HasStepPosFullProcs (impl : SparsifyImpl) (p : Program) (bs : StepPosFullBases) :
    Prop where
  hPos : HasStepPosProcs impl p bs.ne bs.bEm bs.bEp bs.bPos
  hAffP : p.HasAt bs.bAffP (affectedProcs bs.ne.bOps)
  hD : p.HasAt bs.bD (levelsDeleteProcs bs.ne.bPhase)
  hU : p.HasAt bs.bU (applyUProcs bs.ne.bBatch bs.bD)
  hF : p.HasAt bs.bF filterCopyProcs
  hR : p.HasAt bs.bR (restrictRecProcs bs.bF)
  hPref : p.HasAt bs.bPref (stepPrefixProcs bs.bR bs.bU)
  hHead : p.HasAt bs.bHead (stepHeadProcs bs.bAffP bs.bPref)
  hWP : p.HasAt bs.bWP walkPtrsProcs
  hProj : p.HasAt bs.bProj (projProcs bs.ne.bEmb)
  hBP : p.HasAt bs.bBP (buildProjProcs bs.ne.bOps bs.ne.bEdge bs.bProj)
  hPS : p.HasAt bs.bPS (projStageProcs bs.bWP bs.bBP)
  hAS : p.HasAt bs.bAS (affStageProcs bs.bAffP bs.bPS)
  hSum : p.HasAt bs.bSum wordSumProcs
  hFull : p.HasAt bs.bFull (stepPosFullProcs bs.bHead bs.bSum bs.bAS bs.bPos)

end

end MinCostFlow.DynSpanner.Program
