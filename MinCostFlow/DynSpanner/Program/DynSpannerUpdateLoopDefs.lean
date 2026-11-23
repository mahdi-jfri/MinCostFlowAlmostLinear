module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepZero
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFull
public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopMath

import Mathlib.Tactic.Ring

/-!
# Definitions, procedures, and contracts for the batch update loop (`DynSpannerUpdateLoopDefs`)

Defines the deterministic Word-RAM procedures and contracts for Algorithm 6's `update` batch loop
(Theorem 8.2, page 64; model `DynSpanner.update` in `MinCostFlow/DynSpanner/Defs.lean`), wiring
together the level-0 restart branch `dsStepZeroStmt` (`DynSpannerStepZero.lean`) and the positive-
level step `dsStepPosFullStmt` (`DynSpannerStepPosFull.lean`):

* `BatchBodyLensAt`: `BatchBodyAt` recording the explicit per-update encoded word lengths `lens`.
* `StepPosFullUHWordsBound`: the `U_H` word-length bound for every run of `dsStepPosFullStmt`
  (proved as `stepPosFullUHWordsBound` in `DynSpannerUpdateLoopAux.lean`).
* Metadata-independent (`x`-free) model bounds `modelOldSum`, `modelCandRevSum`,
  `dsStepPosEndDelta`, `dsStepPosAffDelta`, `dsStepPosSpaceAt`, `dsStepPosCostModel`, and unified
  per-step dispatchers `dsStepSpaceAt`, `dsStepGenAt`, `dsStepCostAt`, `dsStepWordOKAt`.
* `updateLoopProcs` (`0..4`, all deterministic / `NoRand`):
  - `dsStepStmt` (`0`): computes `j := chooseLevel L q (t + 1)` and dispatches to
    `dsStepPosFullStmt` (`[b, j, updPtr, heapStep, len]`) or `dsStepZeroStmt` (`[b, updPtr, heapStep]`).
  - `dsSaveStepOutStmt` (`1`): copies a step's `D` and `U_H` output outside `metaFoot` at `retPtr`
    so `StepOutPost`'s existing frame preserves all prior step outputs across the batch.
  - `dsCollectBatchDStmt` (`2`): linear-time generation-stamped collection of
    `(⋃ r < m, D_r) ∩ H_final.E`.
  - `dsPackBatchUHStmt` (`3`): linear-time concatenation of the per-step `U_H` bodies into a single
    `BatchAt` encoding.
  - `dsUpdateLoopStmt` (`4`): top-level batch loop writing the 5-word batch output header
    `[uhOutPtr, |U_H|, 1 + uhOutWords, dOutPtr, |D|]` at `heapStart`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Per-update encoded lengths (`BatchBodyLensAt`) -/

/-- Sequential concatenation of encoded updates starting at `a`, recording the exact word length
of each encoded update in `lens`. -/
def BatchBodyLensAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : List Update → List ℕ → Prop
  | [], [] => True
  | u :: us, len :: ls =>
    UpdateAt mem a G u len ∧ BatchBodyLensAt mem (a + len) (G.applyUpdate u) us ls
  | _, _ => False

lemma BatchBodyLensAt.length_eq {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {lens : List ℕ} (h : BatchBodyLensAt mem a G U lens) : lens.length = U.length := by
  induction U generalizing a G lens with
  | nil => cases lens with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons u us ih => cases lens with
    | nil => exact h.elim
    | cons len ls => simp only [List.length_cons, ih h.2]

lemma BatchBodyLensAt.toBatchBodyAt {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {lens : List ℕ} (h : BatchBodyLensAt mem a G U lens) :
    BatchBodyAt mem a G U lens.sum := by
  induction U generalizing a G lens with
  | nil => cases lens with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons u us ih => cases lens with
    | nil => exact h.elim
    | cons len ls =>
      refine ⟨len, by simp, h.1, ?_⟩
      simpa [List.sum_cons, Nat.add_sub_cancel_left] using ih h.2

lemma batchBodyAt_exists_lens {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {tot : ℕ}
    (h : BatchBodyAt mem a G U tot) :
    ∃ lens : List ℕ, lens.length = U.length ∧ lens.sum = tot ∧ BatchBodyLensAt mem a G U lens := by
  induction U generalizing a G tot with
  | nil => exact ⟨[], rfl, h.symm, trivial⟩
  | cons u us ih =>
    rcases h with ⟨len, hle, hu, hrest⟩
    obtain ⟨ls, hlen, hsum, hbl⟩ := ih hrest
    exact ⟨len :: ls, by simp [hlen], by simp [List.sum_cons]; omega, hu, hbl⟩

lemma BatchBodyLensAt.of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {lens : List ℕ} (h : BatchBodyLensAt mem₁ a G U lens)
    (hag : ∀ i < lens.sum, mem₂ (a + i) = mem₁ (a + i)) :
    BatchBodyLensAt mem₂ a G U lens := by
  induction U generalizing a G lens with
  | nil => cases lens with
    | nil => trivial
    | cons _ _ => exact h.elim
  | cons u us ih => cases lens with
    | nil => exact h.elim
    | cons len ls =>
      refine ⟨h.1.copy fun i hi => hag i (by simp [List.sum_cons]; omega), ih h.2 fun i hi => ?_⟩
      simpa [Nat.add_assoc] using hag (len + i) (by simp [List.sum_cons]; omega)

lemma BatchBodyLensAt.drop {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {lens : List ℕ}
    (h : BatchBodyLensAt mem a G U lens) :
    ∀ i ≤ U.length, BatchBodyLensAt mem (a + (lens.take i).sum) (G.applyBatch (U.take i))
      (U.drop i) (lens.drop i) := by
  induction U generalizing a G lens with
  | nil =>
    cases lens with
    | nil => intro i hi; cases hi; simpa [MGraph.applyBatch] using h
    | cons _ _ => exact h.elim
  | cons u us ih =>
    cases lens with
    | nil => exact h.elim
    | cons len ls =>
      intro i hi
      cases i with
      | zero => simpa [MGraph.applyBatch] using h
      | succ i' =>
        have hih := ih h.2 i' (Nat.le_of_succ_le_succ hi)
        simpa [List.take_succ_cons, List.drop_succ_cons, List.sum_cons, MGraph.applyBatch,
          List.foldl_cons, Nat.add_assoc] using hih

lemma BatchBodyLensAt.getElem {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {lens : List ℕ}
    (h : BatchBodyLensAt mem a G U lens) (i : ℕ) (hi : i < U.length) :
    UpdateAt mem (a + (lens.take i).sum) (G.applyBatch (U.take i))
      (U[i]'hi) (lens[i]'(h.length_eq.symm ▸ hi)) := by
  have hd := h.drop i (Nat.le_of_lt hi)
  have hU : U.drop i = (U[i]'hi) :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hL : lens.drop i = (lens[i]'(h.length_eq.symm ▸ hi)) :: lens.drop (i + 1) :=
    List.drop_eq_getElem_cons (h.length_eq.symm ▸ hi)
  rw [hU, hL] at hd
  exact hd.1

/-! ## The `U_H` word-length bound of `dsStepPosFullStmt` -/

/-- Output `U_H` word-length upper bound for `dsStepPosFullStmt`: the word count written to
`mem'[heapStep + 2]` is at most `len + 4 * m.res.UH.length` (matching `dsStepPosEpilogue`), for
every model whose sparsifier is `impl`. -/
def StepPosFullUHWordsBound (w vCap eCap b mMax : ℕ) (impl : SparsifyImpl) (p : Program)
    (bFull : ℕ) : Prop :=
  ∀ (m : StepPosModel) (len : ℕ) (x : DynSpannerMeta m.L)
    (updPtr heapStep : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (body : Stmt) (o : Outcome) (st' : State) (c : ℕ),
    m.impl = impl →
    p.procs[bFull + stepPosFullIdx]? = some body →
    (dsStepPosFullContract m mMax w vCap eCap b len x).pre
      [b, m.j, updPtr, heapStep, len] mem →
    Runs w p ω body (startState [b, m.j, updPtr, heapStep, len] mem pos) o st' c →
    st'.mem (heapStep + 2) ≤ len + 4 * m.res.UH.length

/-! ## Metadata-free model bounds for `0 < j` and unified per-step dispatchers -/

/-- Model-only upper bound on `stepPosOldSum m.u x m.j`: sum of `|(st.H_level i).E|` over
levels `j ≤ i ≤ L`. -/
noncomputable def modelOldSum (m : StepPosModel) : ℕ :=
  ∑ i : Fin (m.L + 1), if m.j ≤ i.1 then (m.st.H_level i).m else 0

/-- Exact edge set stored in `x.revLists i v` according to `RevHistoryInv`. -/
noncomputable def modelRevSet (m : StepPosModel) (i : Fin (m.L + 1)) (v : ℕ) : Finset ℕ :=
  let st_lr := runState (L := m.L) m.G₀ m.q (canonicalSparsify m.impl) m.us
    (lastRebuild m.q m.L i.1 m.k)
  (st_lr.inDom i).filter fun e => v ∈ st_lr.H.walkVertices (st_lr.G.tail e) (st_lr.Pi_level i e)

/-- Exact metadata-free value of `candRevSum m.L m.j x.revLists m.S_prev.toList`. -/
noncomputable def modelCandRevSum (m : StepPosModel) : ℕ :=
  ∑ i ∈ Finset.range m.j, ∑ v ∈ m.S_prev,
    if hi : i < m.L + 1 then (modelRevSet m ⟨i, hi⟩ v).card else 0

/-- The candidates of `dsAffStage` as model sets (Algorithm 6, line 71): the edges of `G'` in
`modelRevSet m i v` for a vertex `v ∈ S_{j-1}` and a level `i < j`. Under `RevHistoryInv` it is the
set `stepPosCandSet m x` that the program enumerates (`stepPosCandSet_eq_modelCandSet`). -/
noncomputable def modelCandSet (m : StepPosModel) : Finset ℕ :=
  @Finset.filter _ (fun e => ∃ i : Fin (m.L + 1), ∃ v ∈ m.S_prev, i.1 < m.j ∧ e ∈ modelRevSet m i v)
    (Classical.decPred _) m.G'.E

/-- Metadata-free heap delta bounding `dsStepPosFullEnd m mMax vCap eCap len x heapStep - heapStep`. -/
noncomputable def dsStepPosEndDelta (m : StepPosModel) (mMax vCap eCap len : ℕ) : ℕ :=
  let oldSum := modelOldSum m
  let eAffPtr := 5 + len + 4 * m.j + 2 + m.S_prev.card + m.G'.m
  (if 0 < m.E_aff.card then
    dsStepPosNonEmptyEnd m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH m.E_aff.toList
      (eAffPtr + m.E_aff.card) m.G'.m oldSum
   else eAffPtr + m.G'.m + eCap + 1 + 2 * oldSum) + len + 4 * m.res.UH.length + 2

/-- Metadata-free heap delta for `dsAffStage`: equals `dsStepPosFullAffEnd m vCap eCap len 0`. -/
noncomputable def dsStepPosAffDelta (m : StepPosModel) (vCap eCap len : ℕ) : ℕ :=
  dsStepPosFullAffEnd m vCap eCap len 0

/-- Metadata-free per-step heap space bound for `dsStepPosFullStmt`. -/
noncomputable def dsStepPosSpaceAt (m : StepPosModel) (mMax vCap eCap len : ℕ) : ℕ :=
  max (dsStepPosEndDelta m mMax vCap eCap len) (dsStepPosAffDelta m vCap eCap len)

/-- Metadata-free cost bound for `dsAffStage` in `dsStepPosFullStmt`, with the candidates of
`modelCandSet`. -/
noncomputable def dsStepPosAffCostModel (m : StepPosModel) : ℕ :=
  100 * modelCandRevSum m + 100 * (m.j * m.S_prev.card) +
    100 * m.S_prev.card + 100 * m.j +
    100 * (∑ e ∈ modelCandSet m, (m.piLt_mid e).length) + 40 * ((modelCandSet m).card * m.j) +
    160 * (modelCandSet m).card +
    m.E_aff.card * (35 * m.j + 60) +
    (∑ e ∈ m.E_aff, (800 * (m.piLt_mid e).length + 2000)) + 1200

/-- Metadata-free cost bound for `dsStepPosFullStmt`. -/
noncomputable def dsStepPosCostModel (m : StepPosModel) (mMax vCap eCap len : ℕ) : ℕ :=
  (500 * (m.L + 1) + 1320 * len + 1100) + (20 * (m.L + 1 - m.j) + 20) +
    dsStepPosAffCostModel m +
    dsStepPosCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
      m.E_aff.toList (modelOldSum m) m.S_prev.card len m.res.UH.length + 330

/-- Unified per-step heap space bound (dispatching between `dsStepZeroSpace + 2` and
`dsStepPosSpaceAt`). -/
noncomputable def dsStepSpaceAt (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax L q vCap eCap : ℕ) (us : List Update) (k len : ℕ) : ℕ :=
  match us[k]? with
  | none => 7
  | some u =>
    if chooseLevel L q (k + 1) = 0 then
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len + 2
    else
      dsStepPosSpaceAt ⟨G₀, impl, L, q, k, us, u⟩ mMax vCap eCap len

/-- Unified per-step generation-counter increase bound. -/
noncomputable def dsStepGenAt (G₀ : MGraph) (impl : SparsifyImpl)
    (L q : ℕ) (us : List Update) (k : ℕ) : ℕ :=
  match us[k]? with
  | none => 2
  | some u =>
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    if chooseLevel L q (k + 1) = 0 then 2 + G'.m
    else chooseLevel L q (k + 1) + 4 + G'.m

/-- Unified per-step Word-RAM cost bound (dispatching between `dsStepZeroCost` and
`dsStepPosCostModel`). -/
noncomputable def dsStepCostAt (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax L q vCap eCap : ℕ) (us : List Update) (k len : ℕ) : ℕ :=
  match us[k]? with
  | none => 1500
  | some u =>
    if chooseLevel L q (k + 1) = 0 then
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      dsStepZeroCost impl mMax L G' st.H H₀ len
    else
      dsStepPosCostModel ⟨G₀, impl, L, q, k, us, u⟩ mMax vCap eCap len

/-- Word-width side condition for step `k` (needed by `dsStepZeroContract` when `j = 0`). -/
def dsStepWordOKAt (G₀ : MGraph) (impl : SparsifyImpl)
    (w L q : ℕ) (us : List Update) (k : ℕ) : Prop :=
  match us[k]? with
  | none => True
  | some u =>
    chooseLevel L q (k + 1) = 0 →
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      G'.E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w

/-! ## Procedure indices and deterministic Word-RAM bodies -/

def updateLoopIdxStep : ℕ := 0
def updateLoopIdxSaveStep : ℕ := 1
def updateLoopIdxCollectD : ℕ := 2
def updateLoopIdxPackUH : ℕ := 3
def updateLoopIdxUpdate : ℕ := 4

/-- Unified single-step dispatcher (`args = [b, updPtr, heapStep, len]`): computes
`j := chooseLevel L q (t + 1)` and calls `dsStepPosFullStmt` (`[b, j, updPtr, heapStep, len]`)
when `0 < j` or `dsStepZeroStmt` (`[b, updPtr, heapStep]`) when `j = 0`. -/
def dsStepStmt (bPhase bSZ bPosFull : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsQOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsTOff))) ;;
  .call 7 (bPhase + phaseIdxChooseLevel)
    [.reg 4, .reg 5, .bin .add (.reg 6) (.const 1)] ;;
  .cond (.reg 7)
    (.call 8 (bPosFull + stepPosFullIdx) [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3] ;; .ret (.reg 8))
    (.call 8 (bSZ + stepZeroIdx) [.reg 0, .reg 1, .reg 2] ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
     .assign 11 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
     .assign 12 (.bin .add (.bin .add (.bin .add (.reg 11) (.const 4))
       (.bin .mul (.const 7) (.reg 9))) (.reg 10)) ;;
     .assign 13 (.load (.bin .add (.reg 11) (.const dgMOff))) ;;
     .store (.reg 8) (.reg 12) ;;
     .store (.bin .add (.reg 8) (.const 1)) (.reg 13) ;;
     .ret (.bin .add (.reg 8) (.const 2)))

/-- Copy a step's `D`, `R`, and `U_H` output out of `[stepHdr, retPtr)` into a fresh 7-word saved
descriptor + lists starting at `retPtr` (`args = [stepHdr, retPtr]`), returning
`retPtr + 7 + dLen + rLen + uhWords`. Because `[retPtr, retPtr + 7 + dLen + rLen + uhWords)` lies
outside `metaFoot b x'`, `StepOutPost`'s frame preserves it across all later steps of the batch. -/
def dsSaveStepOutStmt (bAux : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 11 (.load (.bin .sub (.reg 1) (.const 2))) ;;
  .assign 12 (.load (.bin .sub (.reg 1) (.const 1))) ;;
  .assign 7 (.bin .add (.reg 1) (.const 7)) ;;
  .call 8 (bAux + stepAuxIdxCopyWords) [.reg 5, .reg 7, .reg 6] ;;
  .assign 13 (.bin .add (.reg 7) (.reg 6)) ;;
  .call 14 (bAux + stepAuxIdxCopyWords) [.reg 11, .reg 13, .reg 12] ;;
  .assign 9 (.bin .add (.reg 13) (.reg 12)) ;;
  .call 10 (bAux + stepAuxIdxCopyWords) [.reg 2, .reg 9, .reg 4] ;;
  .store (.reg 1) (.reg 9) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 3) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.reg 4) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 7) ;;
  .store (.bin .add (.reg 1) (.const 4)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const 5)) (.reg 13) ;;
  .store (.bin .add (.reg 1) (.const 6)) (.reg 12) ;;
  .ret (.bin .add (.reg 9) (.reg 4))

/-- Setup prefix of `dsCollectBatchDStmt`: reads `(L, vCap, eCap)`, selects either `hPres` (`r4 = 0`,
descriptor offsets `3, 4`) or `gPres` (`r4 ≠ 0`, descriptor offsets `5, 6`) into `(r11, r27, r28)`,
computes `eStamp` (`r15`), increments `mem[b + dsGenOff]` (`r16`), and initializes `cnt := 0` (`r17`). -/
def dsCollectBatchDSetupStmt : Stmt :=
  .assign 26 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 7 (.bin .add (.reg 26) (.const 1)) ;;
  .assign 8 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))) ;;
  .assign 9 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 8)) ;;
  .cond (.reg 4)
    (.assign 11 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
     .assign 27 (.const 5) ;;
     .assign 28 (.const 6))
    (.assign 11 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
     .assign 27 (.const 3) ;;
     .assign 28 (.const 4)) ;;
  .assign 12 (.bin .add (.bin .add (.reg 10) (.reg 8)) (.reg 8)) ;;
  .assign 13 (.bin .add (.reg 12)
    (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.reg 7)))) ;;
  .assign 14 (.bin .add (.reg 13)
    (.bin .add (.reg 7)
      (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 6)))
        (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 5)))))) ;;
  .assign 15 (.bin .add (.reg 14)
    (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 7)) (.bin .mul (.reg 7) (.reg 5)))
      (.bin .mul (.const 2) (.reg 5)))) ;;
  .assign 16 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 16) ;;
  .assign 17 (.const 0)

/-- Collect the deduplicated batch edge set `(⋃ r < m, D_r) ∩ H_final.E` (when `isReemb = 0`)
or `(⋃ r < m, R_r) ∩ G_final.E` (when `isReemb ≠ 0`) (`args = [b, stepHdrsPtr, m, dOutPtr, isReemb]`),
bumping `mem[b + dsGenOff]` by `1` and using `eStamp` for `O(1)` deduplication. Returns `out.length`. -/
def dsCollectBatchDStmt : Stmt :=
  dsCollectBatchDSetupStmt ;;
  forRange 18 (.const 0) (.reg 2)
    (.assign 19 (.load (.bin .add (.reg 1) (.reg 18))) ;;
     .assign 20 (.load (.bin .add (.reg 19) (.reg 27))) ;;
     .assign 21 (.load (.bin .add (.reg 19) (.reg 28))) ;;
     forRange 22 (.const 0) (.reg 21)
       (.assign 23 (.load (.bin .add (.reg 20) (.reg 22))) ;;
        .assign 24 (.load (.bin .add (.reg 11) (.reg 23))) ;;
        .cond (.reg 24)
          (.assign 25 (.load (.bin .add (.reg 15) (.reg 23))) ;;
           .cond (.bin .eq (.reg 25) (.reg 16))
             .nop
             (.store (.bin .add (.reg 15) (.reg 23)) (.reg 16) ;;
              .store (.bin .add (.reg 3) (.reg 17)) (.reg 23) ;;
              .assign 17 (.bin .add (.reg 17) (.const 1))))
          .nop)) ;;
  .ret (.reg 17)

/-- Concatenate the `m` per-step `U_H` bodies into a single `BatchAt` encoding at `uhOutPtr`
(`args = [stepHdrsPtr, m, uhOutPtr]`). Stores `∑ r, |U_{H,r}|` at `uhOutPtr`, copies each body
sequentially starting at `uhOutPtr + 1`, and returns the total body word length `∑ r, uhWords_r`. -/
def dsPackBatchUHStmt (bAux : ℕ) : Stmt :=
  .assign 3 (.const 0) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .assign 7 (.load (.reg 6)) ;;
     .assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
     .assign 9 (.load (.bin .add (.reg 6) (.const 2))) ;;
     .assign 10 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 4)) ;;
     .call 11 (bAux + stepAuxIdxCopyWords) [.reg 7, .reg 10, .reg 9] ;;
     .assign 3 (.bin .add (.reg 3) (.reg 8)) ;;
     .assign 4 (.bin .add (.reg 4) (.reg 9))) ;;
  .store (.reg 2) (.reg 3) ;;
  .ret (.reg 4)

/-- Batch update loop for Algorithm 6 (`args = [b, batchPtr, heapStart]`): executes each update in
the encoded batch at `batchPtr` via `dsStepStmt`, copies each step's `D` and `U_H` out of
`metaFoot` via `dsSaveStepOutStmt`, collects `D = (⋃ r, D_r) ∩ H_final.E` via
`dsCollectBatchDStmt`, packs the concatenated `U_H` batch via `dsPackBatchUHStmt`, writes the
5-word output header `[uhOutPtr, |U_H|, 1 + uhOutWords, dOutPtr, |D|]` at `heapStart`, and returns
the new heap frontier `uhOutPtr + 1 + uhOutWords`. -/
def dsUpdateLoopStmt (bAux bUL : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .assign 4 (.bin .add (.reg 2) (.const 7)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 3)) ;;
  .assign 6 (.bin .add (.reg 1) (.const 1)) ;;
  forRange 7 (.const 0) (.reg 3)
    (.call 8 (bAux + stepAuxIdxUpdateLen) [.reg 6] ;;
     .call 9 (bUL + updateLoopIdxStep) [.reg 0, .reg 6, .reg 5, .reg 8] ;;
     .store (.bin .add (.reg 4) (.reg 7)) (.reg 9) ;;
     .call 5 (bUL + updateLoopIdxSaveStep) [.reg 5, .reg 9] ;;
     .assign 6 (.bin .add (.reg 6) (.reg 8))) ;;
  .assign 9 (.reg 5) ;;
  .call 10 (bUL + updateLoopIdxCollectD) [.reg 0, .reg 4, .reg 3, .reg 9, .const 0] ;;
  .assign 15 (.bin .add (.reg 9) (.reg 10)) ;;
  .call 16 (bUL + updateLoopIdxCollectD) [.reg 0, .reg 4, .reg 3, .reg 15, .const 1] ;;
  .assign 11 (.bin .add (.reg 15) (.reg 16)) ;;
  .call 12 (bUL + updateLoopIdxPackUH) [.reg 4, .reg 3, .reg 11] ;;
  .assign 13 (.load (.reg 11)) ;;
  .assign 14 (.bin .add (.bin .add (.reg 11) (.const 1)) (.reg 12)) ;;
  .store (.reg 2) (.reg 11) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 13) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.bin .add (.reg 12) (.const 1)) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 9) ;;
  .store (.bin .add (.reg 2) (.const 4)) (.reg 10) ;;
  .store (.bin .add (.reg 2) (.const 5)) (.reg 15) ;;
  .store (.bin .add (.reg 2) (.const 6)) (.reg 16) ;;
  .ret (.reg 14)

/-- Procedure bundle for the batch update loop (`0..4`). -/
def updateLoopProcs (bAux bPhase bSZ bPosFull bUL : ℕ) : List Stmt :=
  [dsStepStmt bPhase bSZ bPosFull,
   dsSaveStepOutStmt bAux,
   dsCollectBatchDStmt,
   dsPackBatchUHStmt bAux,
   dsUpdateLoopStmt bAux bUL]

lemma updateLoopProcs_length (bAux bPhase bSZ bPosFull bUL : ℕ) :
    (updateLoopProcs bAux bPhase bSZ bPosFull bUL).length = 5 := rfl

lemma updateLoopProcs_noRand (bAux bPhase bSZ bPosFull bUL : ℕ) :
    ∀ s ∈ updateLoopProcs bAux bPhase bSZ bPosFull bUL, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Base indices for all sub-procedure libraries used by `dsUpdateLoopStmt`. -/
structure UpdateLoopBases where
  sz : StepZeroBases
  pos : StepPosFullBases
  bUL : ℕ

/-- Proof that program `p` contains all procedures needed by `dsUpdateLoopStmt` at `bs`. -/
structure HasUpdateLoopProcs (impl : SparsifyImpl) (p : Program) (bs : UpdateLoopBases) : Prop where
  hpSZ : HasStepZeroProcs impl p bs.sz
  hpPos : HasStepPosFullProcs impl p bs.pos
  hpUL : p.HasAt bs.bUL (updateLoopProcs bs.sz.bAux bs.sz.bPhase bs.sz.bSZ bs.pos.bFull bs.bUL)

/-! ## Sub-procedure contracts -/

/-- Unified single-step contract for `dsStepStmt` (`[b, updPtr, heapStep, len]`), dispatching
between `dsStepZeroStmt` (`j = 0`) and `dsStepPosFullStmt` (`0 < j`). -/
noncomputable def dsStepContract (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax w L q vCap eCap b k : ℕ) (us : List Update) (u : Update) (len : ℕ)
    (x : DynSpannerMeta L) : Contract where
  pre args mem := ∃ updPtr heapStep,
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    args = [b, updPtr, heapStep, len] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ L ∧ 1 ≤ q ∧
    G₀.IsValid ∧ G₀.m ≤ mMax ∧ (∀ e ∈ G₀.E, e < eCap) ∧
    G₀.BatchIsValid us ∧ (∀ u' ∈ us, isDelOrSplit u') ∧ us[k]? = some u ∧
    (∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s) ∧
    DynSpannerStateAt L vCap eCap b mem x st ∧
    RevHistoryInv G₀ q (canonicalSparsify impl) us k x ∧
    b + dsFixedSize L vCap eCap ≤ heapStep ∧
    (∀ a, heapFoot x a → a < heapStep) ∧
    ZeroFrom mem heapStep ∧
    heapStep + dsStepSpaceAt G₀ impl mMax L q vCap eCap us k len < 2 ^ w ∧
    mem (b + dsGenOff) + dsStepGenAt G₀ impl L q us k < 2 ^ w ∧
    k + 1 < 2 ^ w ∧ q < 2 ^ w ∧
    dsStepWordOKAt G₀ impl w L q us k ∧
    b + dsFixedSize L vCap eCap ≤ updPtr ∧ updPtr + len ≤ heapStep ∧
    (∀ i < len, ¬ metaFoot b x (updPtr + i)) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr st.G u len ∧
    UpdateWithinCaps vCap eCap u
  post args mem ret mem' := ∃ updPtr heapStep,
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    args = [b, updPtr, heapStep, len] ∧
    StepReembOutPost G₀ L q vCap eCap b k impl us u mem x heapStep mem' ret ∧
    heapStep + 7 ≤ ret ∧
    ret ≤ heapStep + dsStepSpaceAt G₀ impl mMax L q vCap eCap us k len ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + dsStepGenAt G₀ impl L q us k ∧
    mem' (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length
  cost _ _ := dsStepCostAt G₀ impl mMax L q vCap eCap us k len + 35 * L + 210

/-- Contract for `dsSaveStepOutStmt` (`[stepHdr, retPtr]`): copies `D` (`dLen` words), `R`
(`rLen` words), and `U_H` (`uhWords` words) from a step output (`retPtr = ret0 + 2`) into
`[retPtr, retPtr + 7 + dLen + rLen + uhWords)`. -/
def dsSaveStepOutContract (w stepHdr retPtr uhPtr uhLen uhWords dPtr dLen rPtr rLen : ℕ) :
    Contract where
  pre args mem :=
    args = [stepHdr, retPtr] ∧ 16 ≤ 2 ^ w ∧
    stepHdr + 5 ≤ dPtr ∧ dPtr + dLen ≤ uhPtr ∧ uhPtr + uhWords + 2 = retPtr ∧
    rPtr + rLen + 2 ≤ retPtr ∧
    retPtr + 7 + dLen + rLen + uhWords < 2 ^ w ∧
    mem stepHdr = uhPtr ∧ mem (stepHdr + 1) = uhLen ∧ mem (stepHdr + 2) = uhWords ∧
    mem (stepHdr + 3) = dPtr ∧ mem (stepHdr + 4) = dLen ∧
    mem (retPtr - 2) = rPtr ∧ mem (retPtr - 1) = rLen
  post _ mem ret mem' :=
    ret = retPtr + 7 + dLen + rLen + uhWords ∧
    mem' retPtr = retPtr + 7 + dLen + rLen ∧
    mem' (retPtr + 1) = uhLen ∧
    mem' (retPtr + 2) = uhWords ∧
    mem' (retPtr + 3) = retPtr + 7 ∧
    mem' (retPtr + 4) = dLen ∧
    mem' (retPtr + 5) = retPtr + 7 + dLen ∧
    mem' (retPtr + 6) = rLen ∧
    (∀ i < dLen, mem' (retPtr + 7 + i) = mem (dPtr + i)) ∧
    (∀ i < rLen, mem' (retPtr + 7 + dLen + i) = mem (rPtr + i)) ∧
    (∀ i < uhWords, mem' (retPtr + 7 + dLen + rLen + i) = mem (uhPtr + i)) ∧
    ∀ a, a < retPtr ∨ ret ≤ a → mem' a = mem a
  cost _ _ := 30 * dLen + 30 * rLen + 30 * uhWords + 240

/-- Context bundle for `dsCollectBatchDStmt` (`isReemb = false` collects `D` against `H.E` at
descriptor offsets `3, 4`; `isReemb = true` collects `R` against `G.E` at descriptor offsets `5, 6`). -/
structure CollectDCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  stepHdrsPtr : ℕ
  m : ℕ
  dOutPtr : ℕ
  isReemb : Bool
  H : MGraph
  dLists : Fin m → List ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w
  hgen_w : mem0 (b + dsGenOff) + 1 < 2 ^ w
  hhdrs_w : stepHdrsPtr + m < 2 ^ w
  hdOut_w : dOutPtr + (∑ i : Fin m, (dLists i).length) < 2 ^ w
  hfix_hdrs : b + dsFixedSize L vCap eCap ≤ stepHdrsPtr
  hfix_out : b + dsFixedSize L vCap eCap ≤ dOutPtr
  hhdrs_out : stepHdrsPtr + m ≤ dOutPtr
  hL : mem0 (b + dsLOff) = L
  hvC : mem0 (b + dsVCapOff) = vCap
  heC : mem0 (b + dsECapOff) = eCap
  hH : ∀ e < eCap,
    mem0 (dgEPresBase (if isReemb then dsGPtr b else dsHPtr b vCap eCap) vCap + e) ≠ 0 ↔ e ∈ H.E
  hES : ∀ e < eCap, mem0 (dsEStampBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff)
  hSteps : ∀ i : Fin m,
    let h := mem0 (stepHdrsPtr + i.1)
    let ptrOff := if isReemb then 5 else 3
    let lenOff := if isReemb then 6 else 4
    let dPtr := mem0 (h + ptrOff)
    let dLen := mem0 (h + lenOff)
    b + dsFixedSize L vCap eCap ≤ h ∧ h + 7 ≤ dOutPtr ∧
    b + dsFixedSize L vCap eCap ≤ dPtr ∧ dPtr + dLen ≤ dOutPtr ∧
    dLen = (dLists i).length ∧ ListAt mem0 dPtr (dLists i) ∧
    ∀ e ∈ dLists i, e < eCap

/-- Contract for `dsCollectBatchDStmt` (`[b, stepHdrsPtr, m, dOutPtr, isReemb]`). -/
def dsCollectBatchDContract (c : CollectDCtx) : Contract where
  pre args mem :=
    args = [c.b, c.stepHdrsPtr, c.m, c.dOutPtr, if c.isReemb then 1 else 0] ∧ mem = c.mem0
  post _ _ ret mem' := ∃ dOut : List ℕ,
    ret = dOut.length ∧
    dOut.length ≤ ∑ i : Fin c.m, (c.dLists i).length ∧
    dOut.Nodup ∧
    (∀ e, e ∈ dOut ↔ (∃ i : Fin c.m, e ∈ c.dLists i) ∧ e ∈ c.H.E) ∧
    ListAt mem' c.dOutPtr dOut ∧
    mem' (c.b + dsGenOff) = c.mem0 (c.b + dsGenOff) + 1 ∧
    (∀ e < c.eCap, mem' (dsEStampBase c.b c.L c.vCap c.eCap + e) ≤ mem' (c.b + dsGenOff)) ∧
    ∀ a, a ≠ c.b + dsGenOff →
      (a < dsEStampBase c.b c.L c.vCap c.eCap ∨ dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤ a) →
      (a < c.dOutPtr ∨ c.dOutPtr + dOut.length ≤ a) →
      mem' a = c.mem0 a
  cost _ _ := 60 * (∑ i : Fin c.m, (c.dLists i).length) + 80 * c.m + 280

/-- Context bundle for `dsPackBatchUHStmt`. -/
structure PackUHCtx where
  w : ℕ
  stepHdrsPtr : ℕ
  m : ℕ
  uhOutPtr : ℕ
  Hs : ℕ → MGraph
  uhLists : Fin m → List Update
  uhWords : Fin m → ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hhdrs_w : stepHdrsPtr + m < 2 ^ w
  htotLen_w : (∑ i : Fin m, (uhLists i).length) < 2 ^ w
  htotW_w : uhOutPtr + 1 + (∑ i : Fin m, uhWords i) < 2 ^ w
  hhdrs_out : stepHdrsPtr + m ≤ uhOutPtr
  hstepH : ∀ i : Fin m, Hs (i.1 + 1) = (Hs i.1).applyBatch (uhLists i)
  hSteps : ∀ i : Fin m,
    let h := mem0 (stepHdrsPtr + i.1)
    let uPtr := mem0 h
    h + 5 ≤ uhOutPtr ∧ uPtr + uhWords i ≤ uhOutPtr ∧
    mem0 (h + 1) = (uhLists i).length ∧ mem0 (h + 2) = uhWords i ∧
    BatchBodyAt mem0 uPtr (Hs i.1) (uhLists i) (uhWords i)

/-- Contract for `dsPackBatchUHStmt` (`[stepHdrsPtr, m, uhOutPtr]`). -/
def dsPackBatchUHContract (c : PackUHCtx) : Contract where
  pre args mem := args = [c.stepHdrsPtr, c.m, c.uhOutPtr] ∧ mem = c.mem0
  post _ _ ret mem' :=
    ret = ∑ i : Fin c.m, c.uhWords i ∧
    BatchAt mem' c.uhOutPtr (c.Hs 0) ((List.finRange c.m).flatMap c.uhLists) (1 + ret) ∧
    ∀ a, a < c.uhOutPtr ∨ c.uhOutPtr + 1 + ret ≤ a → mem' a = c.mem0 a
  cost _ _ := 30 * (∑ i : Fin c.m, c.uhWords i) + 80 * c.m + 60

/-! ## Batch update space, generation, cost, and contract -/

/-- Upper bound on total heap words allocated above `heapStart` by `dsUpdateLoopStmt`. -/
noncomputable def dsUpdateLoopSpace (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax L q vCap eCap : ℕ) (us U : List Update) (lens : List ℕ) (k₀ : ℕ) : ℕ :=
  7 + U.length +
  (∑ r ∈ Finset.range U.length,
    (dsStepSpaceAt G₀ impl mMax L q vCap eCap us (k₀ + r) (lens.getD r 0) + 7)) +
  2 * (∑ r ∈ Finset.range U.length,
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).D.card) +
  2 * (∑ r ∈ Finset.range U.length,
    (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).card) +
  1 + 2 * (lens.sum + 4 * ∑ r ∈ Finset.range U.length,
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).UH.length)

/-- Upper bound on the increase in `mem[b + dsGenOff]` across `dsUpdateLoopStmt`. -/
noncomputable def dsUpdateLoopGen (G₀ : MGraph) (impl : SparsifyImpl)
    (L q : ℕ) (us : List Update) (m k₀ : ℕ) : ℕ :=
  (∑ r ∈ Finset.range m, dsStepGenAt G₀ impl L q us (k₀ + r)) + 2

/-- Explicit Word-RAM cost bound for `dsUpdateLoopStmt`: sum of per-step costs (`dsStepZeroCost`
at `j = 0`, `dsStepPosCostModel` at `0 < j`) plus explicit linear `D`, `R`, and `U_H` packing
overhead. -/
noncomputable def dsUpdateLoopCost (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax L q vCap eCap : ℕ) (us U : List Update) (lens : List ℕ) (k₀ : ℕ) : ℕ :=
  (∑ r ∈ Finset.range U.length,
    (dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) (lens.getD r 0) + 35 * L + 520)) +
  90 * (∑ r ∈ Finset.range U.length,
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).D.card) +
  90 * (∑ r ∈ Finset.range U.length,
    (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).card) +
  60 * (lens.sum + 4 * ∑ r ∈ Finset.range U.length,
    (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).UH.length) +
  240 * U.length + 820

/-- Postcondition of the batch update loop `dsUpdateLoopStmt` on slice `U` starting at `k₀`. -/
def BatchUpdateOutPost (G₀ : MGraph) (L q vCap eCap b k₀ : ℕ) (impl : SparsifyImpl)
    (us U : List Update) (mem0 : ℕ → ℕ) (x₀ : DynSpannerMeta L)
    (heapStart : ℕ) (memFinal : ℕ → ℕ) (retFinal : ℕ) : Prop :=
  let st₀ := runState (L := L) G₀ q (canonicalSparsify impl) us k₀
  let out := update st₀ U (canonicalSparsify impl)
  ∃ (uhOutPtr uhOutWords dOutPtr rOutPtr : ℕ) (uhActualAll : List Update)
      (dOut rOut : List ℕ) (x' : DynSpannerMeta L),
    memFinal heapStart = uhOutPtr ∧
    memFinal (heapStart + 1) = uhActualAll.length ∧
    memFinal (heapStart + 2) = 1 + uhOutWords ∧
    memFinal (heapStart + 3) = dOutPtr ∧
    memFinal (heapStart + 4) = dOut.length ∧
    memFinal (heapStart + 5) = rOutPtr ∧
    memFinal (heapStart + 6) = rOut.length ∧
    heapStart + 7 ≤ dOutPtr ∧ dOutPtr + dOut.length = rOutPtr ∧
    rOutPtr + rOut.length = uhOutPtr ∧
    uhOutPtr + 1 + uhOutWords = retFinal ∧
    BatchAt memFinal uhOutPtr st₀.H uhActualAll (1 + uhOutWords) ∧
    uhActualAll.Perm out.UH ∧
    st₀.H.applyBatch uhActualAll = out.state.H ∧
    dOut.Nodup ∧ dOut.toFinset = out.D ∧ ListAt memFinal dOutPtr dOut ∧
    rOut.Nodup ∧ rOut.toFinset = updateReembSet st₀ U (canonicalSparsify impl) ∧
    ListAt memFinal rOutPtr rOut ∧
    ZeroFrom memFinal retFinal ∧
    x'.vCap = vCap ∧ x'.eCap = eCap ∧
    (∀ a, heapFoot x' a → a < retFinal) ∧
    DynSpannerStateAt L vCap eCap b memFinal x' out.state ∧
    RevHistoryInv G₀ q (canonicalSparsify impl) us (k₀ + U.length) x' ∧
    (∀ a < heapStart, ¬ metaFoot b x₀ a → memFinal a = mem0 a) ∧
    (∀ a < heapStart, metaFoot b x' a ↔ metaFoot b x₀ a)

/-- Top-level contract for `dsUpdateLoopStmt` (`[b, batchPtr, heapStart]`) on a batch `U` matching
`us[k₀ .. k₀ + U.length)`. -/
noncomputable def dsUpdateLoopContract (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax w L q vCap eCap b k₀ : ℕ) (us U : List Update) (lens : List ℕ)
    (x₀ : DynSpannerMeta L) : Contract where
  pre args mem := ∃ batchPtr heapStart,
    let st₀ := runState (L := L) G₀ q (canonicalSparsify impl) us k₀
    args = [b, batchPtr, heapStart] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ L ∧ 1 ≤ q ∧
    G₀.IsValid ∧ G₀.m ≤ mMax ∧ (∀ e ∈ G₀.E, e < eCap) ∧
    G₀.BatchIsValid us ∧ (∀ u' ∈ us, isDelOrSplit u') ∧
    (∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) ∧
    (∀ s ≤ k₀, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s) ∧
    DynSpannerStateAt L vCap eCap b mem x₀ st₀ ∧
    RevHistoryInv G₀ q (canonicalSparsify impl) us k₀ x₀ ∧
    b + dsFixedSize L vCap eCap ≤ heapStart ∧
    (∀ a, heapFoot x₀ a → a < heapStart) ∧
    ZeroFrom mem heapStart ∧
    heapStart + dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ < 2 ^ w ∧
    mem (b + dsGenOff) + dsUpdateLoopGen G₀ impl L q us U.length k₀ < 2 ^ w ∧
    k₀ + U.length < 2 ^ w ∧ q < 2 ^ w ∧
    (∀ r < U.length, dsStepWordOKAt G₀ impl w L q us (k₀ + r)) ∧
    b + dsFixedSize L vCap eCap ≤ batchPtr ∧
    batchPtr + 1 + lens.sum ≤ heapStart ∧
    (∀ i < 1 + lens.sum, ¬ metaFoot b x₀ (batchPtr + i)) ∧
    (∀ i < 1 + lens.sum, mem (batchPtr + i) < 2 ^ w) ∧
    mem batchPtr = U.length ∧
    BatchBodyLensAt mem (batchPtr + 1) st₀.G U lens ∧
    BatchWithinCaps vCap eCap U
  post args mem ret mem' := ∃ batchPtr heapStart,
    args = [b, batchPtr, heapStart] ∧
    BatchUpdateOutPost G₀ L q vCap eCap b k₀ impl us U mem x₀ heapStart mem' ret ∧
    heapStart + 7 ≤ ret ∧
    ret ≤ heapStart + dsUpdateLoopSpace G₀ impl mMax L q vCap eCap us U lens k₀ ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + dsUpdateLoopGen G₀ impl L q us U.length k₀
  cost _ _ := dsUpdateLoopCost G₀ impl mMax L q vCap eCap us U lens k₀

end

end MinCostFlow.DynSpanner.Program
