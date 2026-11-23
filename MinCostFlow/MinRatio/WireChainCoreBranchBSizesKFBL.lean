module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopDefsKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic

/-!
# The sizes of the update loop of Branch B (`WireChainCoreBranchBSizesKFBL`)

The loop of Branch B (`wireBranchBLoopKFBL_runs`) takes three cap families `BWc`, `EWc`, `ULc`:
the words of the batch, the words of the edits and the length of the batch that enter each level.
Its premise `UpdateLoopSizeInv` asks the caps to bound what each plain step hands to the next
level. Its cost is charged at these caps, so they must follow the actual steps. Its space is
charged at these caps too, and the post of the core asks a space bound that depends only on the
length of the outer batch. So we need two things:
1. caps that follow the steps (`branchBTraceCaps`), which meet `UpdateLoopSizeInv`
   (`updateLoopSizeInv_of_traceCaps`);
2. a proof that these caps lie below the absolute caps `branchBCapBW`, `branchBCapEW`,
   `branchBCapUL` of `WireChainCoreSpecKFBL` (`branchBTraceCaps_le_abs`).

The second needs facts on the tool: the encoding and the length of the forwarded batch are at
most the change of tool cost of the step, and that change is at most `stepCap j b` when the
batch that enters level `j` has at most `b` updates (`BranchBToolStepKFBL`). These facts are
asked only for the batches that the loop really passes: the graph of the level is valid, the
batch is valid for it, and the graph has at most `levelM j` edges (`BranchBStepBatchOK`, along
the batches `branchBStepBatch` of the steps).

`branchBStepData` lists, level by level, the encoding of the forwarded batch, the change of tool
cost and the length of the forwarded batch, along the same recursion as `UpdateLoopSizeInv`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- One plain step at level `idx`, as in `UpdateLoopSizeInv`: the next chain, the next graph and
the forwarded batch, then the encoding of the forwarded batch (on the old graph of the next
level), the change of tool cost, and the length of the forwarded batch. -/
@[expose] noncomputable def branchBStepNext (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    ChainState cfg.T cfg.P × MGraph × List Update × ℕ × ℕ × ℕ :=
  let Cpartial : TreeChain :=
    { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
  let ℓi := Cpartial.chainLen ℓ' idx
  let gi := Cpartial.chainGrad g' idx
  let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
    (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
      st.scState st.bran idx)
  let sc' := updRes.1
  let nextG := cfg.T.S sc' (st.bran idx)
  let nextU := updRes.2 (st.bran idx)
  let nextEnc := (st.G (idx + 1)).batchEnc nextU
  let fiChanges := diffTreeChanges (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E
    (cfg.T.lsfs sc' (st.bran idx)).F.F.E
  let stNext : ChainState cfg.T cfg.P :=
    { st with
      G := fun j => if j = idx then curG else st.G j
      scState := fun j => if j = idx then sc' else st.scState j
      updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
      recUpdates := fun j =>
        if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
      curFwd := fun j =>
        if j = idx then st.curFwd idx + nextU.length else st.curFwd j
      curEnc := fun j =>
        if j = idx then st.curEnc idx + curEnc
        else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
        else st.curEnc j
      curDecUpdates := fun j =>
        if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
  (stNext, nextG, nextU, (cfg.T.S (st.scState idx) (st.bran idx)).batchEnc nextU,
    cfg.T.cost sc' - cfg.T.cost (st.scState idx), nextU.length)

/-- The data of the plain steps of the update loop, along the recursion of `UpdateLoopSizeInv`:
at level `j`, the last three entries of `branchBStepNext`. Levels with no plain step get
`(0, 0, 0)`. -/
@[expose] noncomputable def branchBStepData (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → ChainState cfg.T cfg.P → MGraph → List Update → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _, _, _, _, _ => (0, 0, 0)
  | rem + 1, idx, st, curG, curU, curEnc, j =>
    if intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length then (0, 0, 0)
    else
      let n := branchBStepNext cfg ℓ' g' idx st curG curU curEnc
      if j = idx then n.2.2.2
      else branchBStepData cfg ℓ' g' rem (idx + 1) n.1 n.2.1 n.2.2.1 0 j

/-- The caps that follow the steps: at level `0` the words of the batch, the words of the edits
and the length of the batch; at level `j + 1` the bounds that `UpdateLoopSizeInv` asks, from the
data `D j` of the step at level `j`. -/
@[expose] def branchBTraceCaps (edMul : ℕ) (logf : ℕ → ℕ) (bW0 eW0 u0 : ℕ)
    (D : ℕ → ℕ × ℕ × ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (bW0, eW0, u0)
  | j + 1 =>
    (5 * (D j).1 + 1,
      edMul * ((D j).2.1 + ((branchBTraceCaps edMul logf bW0 eW0 u0 D j).1 +
        (branchBTraceCaps edMul logf bW0 eW0 u0 D j).2.1 + 1) * logf j),
      (D j).2.2)

/-- The batch that enters level `j` along the plain steps of the update loop, on the same
recursion as `branchBStepData`: `curU` at `j = idx`, and the batch forwarded by level `j - 1`
above it. Levels with no plain step get the empty batch. -/
@[expose] noncomputable def branchBStepBatch (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → ChainState cfg.T cfg.P → MGraph → List Update → ℕ → ℕ → List Update
  | 0, _, _, _, _, _, _ => []
  | rem + 1, idx, st, curG, curU, curEnc, j =>
    if intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length then []
    else if j = idx then curU
    else
      let n := branchBStepNext cfg ℓ' g' idx st curG curU curEnc
      branchBStepBatch cfg ℓ' g' rem (idx + 1) n.1 n.2.1 n.2.2.1 0 j

/-- The facts that the loop has on a batch `U` that enters level `j` of the chain `ch`: the
graph of the level is valid, `U` is a valid batch for it, and the graph has at most
`levelM j` edges. -/
@[expose] def BranchBStepBatchOK (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) (j : ℕ)
    (U : List Update) : Prop :=
  (ch.G j).IsValid ∧ (ch.G j).BatchIsValid U ∧ (ch.G j).m ≤ levelM cfg.TP cfg.P j

/-- The facts on the tool for the plain steps at the levels of the chain `ch`, for each batch
`U` that meets `BranchBStepBatchOK` at its level: the encoding and the length of the forwarded
batch are at most the change of tool cost of the step, and that change is at most `stepCap j b`
when the batch has at most `b` updates. -/
@[expose] def BranchBToolStepKFBL (cfg : Alg2Config) (stepCap : ℕ → ℕ → ℕ)
    (ch : ChainState cfg.T cfg.P) : Prop :=
  ∀ j < cfg.P.d, ∀ (U : List Update) (ℓ g : ℕ → ℝ) (ord : ℕ → List End),
    BranchBStepBatchOK cfg ch j U →
    (cfg.T.S (ch.scState j) (ch.bran j)).batchEnc
        ((cfg.T.updateOrd (ch.scState j) U ℓ g ord).2 (ch.bran j)) ≤
      cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord).1 - cfg.T.cost (ch.scState j) ∧
    ((cfg.T.updateOrd (ch.scState j) U ℓ g ord).2 (ch.bran j)).length ≤
      cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord).1 - cfg.T.cost (ch.scState j) ∧
    ∀ b, U.length ≤ b →
      cfg.T.cost (cfg.T.updateOrd (ch.scState j) U ℓ g ord).1 - cfg.T.cost (ch.scState j) ≤
        stepCap j b

/-- Caps that bound the data of the steps meet `UpdateLoopSizeInv`. The data are those of
`branchBStepData` from the same start, and only the levels `idx ≤ j < idx + rem` are read. -/
theorem updateLoopSizeInv_of_stepData (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (edMul : ℕ)
    (logf BWc EWc ULc : ℕ → ℕ) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ),
      (∀ j, idx ≤ j → j < idx + rem →
        5 * (branchBStepData cfg ℓ' g' rem idx st curG curU curEnc j).1 + 1 ≤ BWc (j + 1) ∧
        edMul * ((branchBStepData cfg ℓ' g' rem idx st curG curU curEnc j).2.1 +
          (BWc j + EWc j + 1) * logf j) ≤ EWc (j + 1) ∧
        (branchBStepData cfg ℓ' g' rem idx st curG curU curEnc j).2.2 ≤ ULc (j + 1)) →
      UpdateLoopSizeInv cfg ℓ' g' edMul logf BWc EWc ULc rem idx st curG curU curEnc := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ _ _; trivial
  | succ rem ih =>
    intro idx st curG curU curEnc h
    unfold UpdateLoopSizeInv
    split_ifs with hT
    have h0 := h idx le_rfl (by omega)
    simp only [branchBStepData, if_neg hT, if_pos rfl] at h0
    refine ⟨h0.1, h0.2.1, h0.2.2, ih _ _ _ _ _ fun j hj1 hj2 => ?_⟩
    have hj := h j (by omega) (by omega)
    have hne : j ≠ idx := by omega
    simp only [branchBStepData, if_neg hT, if_neg hne] at hj
    exact hj

/-- The trace caps meet `UpdateLoopSizeInv` from level `0`. -/
theorem updateLoopSizeInv_of_traceCaps (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (edMul : ℕ)
    (logf : ℕ → ℕ) (rem : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph)
    (curU : List Update) (curEnc bW0 eW0 u0 : ℕ) :
    let D := branchBStepData cfg ℓ' g' rem 0 st curG curU curEnc
    let C := branchBTraceCaps edMul logf bW0 eW0 u0 D
    UpdateLoopSizeInv cfg ℓ' g' edMul logf (fun j => (C j).1) (fun j => (C j).2.1)
      (fun j => (C j).2.2) rem 0 st curG curU curEnc := by
  intro D C
  exact updateLoopSizeInv_of_stepData cfg ℓ' g' edMul logf _ _ _ rem 0 st curG curU curEnc
    fun j _ _ => ⟨le_rfl, le_rfl, le_rfl⟩

/-- The data of each step meet the tool facts: the encoding and the length of the forwarded
batch are at most the change of tool cost, and that change is at most `stepCap j b` when the
batch that enters level `j` has at most `b` updates. That batch is `curU` at `j = idx`, and the
batch forwarded by level `j - 1` above it (`branchBStepBatch`). The chain `ch` holds the tool
states of the levels `j ≥ idx` and the branches, and each batch that enters a level meets
`BranchBStepBatchOK` there (`hV`). -/
theorem branchBStepData_le {cfg : Alg2Config} {stepCap : ℕ → ℕ → ℕ}
    {ch : ChainState cfg.T cfg.P} (hT : BranchBToolStepKFBL cfg stepCap ch) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ),
      idx + rem ≤ cfg.P.d →
      (∀ j, idx ≤ j → st.scState j = ch.scState j) → st.bran = ch.bran →
      (∀ j, idx ≤ j → j < idx + rem →
        BranchBStepBatchOK cfg ch j (branchBStepBatch cfg ℓ' g' rem idx st curG curU curEnc j)) →
      ∀ j,
        let D := branchBStepData cfg ℓ' g' rem idx st curG curU curEnc
        (D j).1 ≤ (D j).2.1 ∧ (D j).2.2 ≤ (D j).2.1 ∧
        ∀ b, (if j = idx then curU.length else (D (j - 1)).2.2) ≤ b → (D j).2.1 ≤ stepCap j b := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEnc _ _ _ _ j
    simp only [branchBStepData]
    exact ⟨le_rfl, le_rfl, fun _ _ => Nat.zero_le _⟩
  | succ rem ih =>
    intro idx st curG curU curEnc hLe hSc hBr hV j
    dsimp only
    by_cases hTh : intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length
    · simp only [branchBStepData, if_pos hTh]
      exact ⟨le_rfl, le_rfl, fun _ _ => Nat.zero_le _⟩
    by_cases hj : j = idx
    · subst hj
      simp only [branchBStepData, if_neg hTh, if_pos rfl, branchBStepNext]
      have hVj := hV j le_rfl (by omega)
      simp only [branchBStepBatch, if_neg hTh, if_pos rfl] at hVj
      rw [hSc j le_rfl, hBr]
      obtain ⟨h1, h2, h3⟩ := hT j (by omega) curU _ _ _ hVj
      exact ⟨h1, h2, fun b hb => h3 b hb⟩
    · set n := branchBStepNext cfg ℓ' g' idx st curG curU curEnc with hn
      have hRec := ih (idx + 1) n.1 n.2.1 n.2.2.1 0 (by omega)
        (fun j' hj' => by
          rw [hn]; simp only [branchBStepNext]
          rw [if_neg (by omega : j' ≠ idx)]
          exact hSc j' (by omega))
        (by rw [hn]; simp only [branchBStepNext]; exact hBr)
        (fun j' hj1 hj2 => by
          have hVj := hV j' (by omega) (by omega)
          simp only [branchBStepBatch, if_neg hTh, if_neg (by omega : j' ≠ idx), ← hn] at hVj
          exact hVj) j
      dsimp only at hRec
      simp only [branchBStepData, if_neg hTh, if_neg hj, ← hn]
      refine ⟨hRec.1, hRec.2.1, fun b hb => hRec.2.2 b ?_⟩
      by_cases hj1 : j = idx + 1
      · rw [if_pos hj1]
        have hEq : j - 1 = idx := by omega
        rw [hEq, if_pos rfl] at hb
        exact hb
      · rw [if_neg hj1]
        have hne : j - 1 ≠ idx := by omega
        rw [if_neg hne] at hb
        exact hb

/-- The trace caps lie below the absolute caps of `WireChainCoreSpecKFBL`, when the data of the
steps meet the tool facts (`branchBStepData_le`) at the log factors of the levels. -/
theorem branchBTraceCaps_le_abs {cfg : Alg2Config} {stepCap : ℕ → ℕ → ℕ} {edMul u : ℕ}
    {bW0 eW0 u0 : ℕ} {D : ℕ → ℕ × ℕ × ℕ}
    (hb0 : bW0 ≤ 4 * u + 1) (he0 : eW0 ≤ 10 * u + 1) (hu0 : u0 ≤ u)
    (hD : ∀ j, (D j).1 ≤ (D j).2.1 ∧ (D j).2.2 ≤ (D j).2.1 ∧
      ∀ b, (if j = 0 then u0 else (D (j - 1)).2.2) ≤ b → (D j).2.1 ≤ stepCap j b) :
    ∀ j,
      let C := branchBTraceCaps edMul
        (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) bW0 eW0 u0 D
      (C j).1 ≤ branchBCapBW stepCap u j ∧ (C j).2.1 ≤ branchBCapEW edMul cfg stepCap u j ∧
        (C j).2.2 ≤ branchBCapUL stepCap u j := by
  intro j
  induction j with
  | zero => exact ⟨hb0, he0, hu0⟩
  | succ j ih =>
    dsimp only at ih ⊢
    obtain ⟨ihB, ihE, ihU⟩ := ih
    have hEnter : (if j = 0 then u0 else (D (j - 1)).2.2) ≤ branchBCapUL stepCap u j := by
      rcases j with _ | j
      · simpa [branchBTraceCaps] using ihU
      · simpa [branchBTraceCaps] using ihU
    have hΔ : (D j).2.1 ≤ branchBCapUL stepCap u (j + 1) := (hD j).2.2 _ hEnter
    refine ⟨?_, ?_, ?_⟩
    · simp only [branchBTraceCaps, branchBCapBW]
      have := (hD j).1
      omega
    · simp only [branchBTraceCaps, branchBCapEW]
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add hΔ (Nat.mul_le_mul_right _ (by omega))
    · simp only [branchBTraceCaps]
      exact (hD j).2.1.trans hΔ

/-- The trace caps meet the step premise of `costTotalBranchB`: the forwarded batch has at most
`Δc j` updates, the next batch words are at most `6 Δc j + 1`, and the next edit words are at
most `edMul (Δc j + (bW j + eW j + 1) B₀)`, when every log factor is at most `B₀`. Here `Δc j` is
the change of tool cost in the data of step `j`. -/
theorem branchBTraceCaps_costPremise {edMul B₀ bW0 eW0 u0 : ℕ} {logf : ℕ → ℕ}
    {D : ℕ → ℕ × ℕ × ℕ} (hlog : ∀ j, logf j ≤ B₀)
    (hD : ∀ j, (D j).1 ≤ (D j).2.1 ∧ (D j).2.2 ≤ (D j).2.1) (j : ℕ) :
    let C := branchBTraceCaps edMul logf bW0 eW0 u0 D
    (C (j + 1)).2.2 ≤ (D j).2.1 ∧ (C (j + 1)).1 ≤ 6 * (D j).2.1 + 1 ∧
      (C (j + 1)).2.1 ≤ edMul * ((D j).2.1 + ((C j).1 + (C j).2.1 + 1) * B₀) := by
  intro C
  refine ⟨(hD j).2, ?_, ?_⟩
  · show 5 * (D j).1 + 1 ≤ 6 * (D j).2.1 + 1
    have := (hD j).1
    omega
  · show edMul * ((D j).2.1 + ((C j).1 + (C j).2.1 + 1) * logf j) ≤ _
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hlog j)) _)

/-- The step space premise of `wireBranchBLoopKFBL_runs` at the trace caps from level `0`, with
`stepSpace j := updStepSpace j u`, from the field `updStepSpaceDom` of `UpdateCoreOpsHypKFBL`
(`hDom`) and the tool facts at the chain `ch` whose tool states and branches the start chain
`st` has. The outer batch has `u` updates, and the level-`0` words are within `4 u + 1` and
`10 u + 1`. -/
theorem branchBLoop_stepSpace {L capExp edMul : ℕ} {cfg : Alg2Config} {stepCap : ℕ → ℕ → ℕ}
    {allocation : ℕ → List ℕ → ℕ} {updStepSpace : ℕ → ℕ → ℕ}
    (hDom : ∀ (idx uLen coreH gB bPtr bW ePtr eW lB h nU uL : ℕ), idx < cfg.P.d →
      bW ≤ branchBCapBW stepCap uLen idx → eW ≤ branchBCapEW edMul cfg stepCap uLen idx →
      nU ≤ branchBCapUL stepCap uLen (idx + 1) → uL ≤ branchBCapUL stepCap uLen idx →
      3 * allocation 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P idx) cfg.N₀) +
        uL + nU ≤ updStepSpace idx uLen)
    {ch : ChainState cfg.T cfg.P} (hT : BranchBToolStepKFBL cfg stepCap ch) (ℓ' g' : ℕ → ℝ)
    {rem : ℕ} (hRem : rem ≤ cfg.P.d) {st : ChainState cfg.T cfg.P} {curG : MGraph}
    {curU : List Update} {curEnc bW0 eW0 u : ℕ}
    (hSc : ∀ j, st.scState j = ch.scState j) (hBr : st.bran = ch.bran)
    (hb0 : bW0 ≤ 4 * u + 1) (he0 : eW0 ≤ 10 * u + 1) (hu0 : curU.length ≤ u)
    (hV : ∀ j < rem,
      BranchBStepBatchOK cfg ch j (branchBStepBatch cfg ℓ' g' rem 0 st curG curU curEnc j)) :
    let C := branchBTraceCaps edMul
      (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) bW0 eW0 curU.length
      (branchBStepData cfg ℓ' g' rem 0 st curG curU curEnc)
    ∀ j < cfg.P.d, ∀ coreH gB bPtr bW ePtr eW lB h nU uL : ℕ, bW ≤ (C j).1 →
      eW ≤ (C j).2.1 → nU ≤ (C (j + 1)).2.2 → uL ≤ (C j).2.2 →
      3 * allocation 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) +
        uL + nU ≤ updStepSpace j u := by
  intro C j hj coreH gB bPtr bW ePtr eW lB h nU uL hbW heW hnU huL
  have hD := branchBStepData_le hT ℓ' g' rem 0 st curG curU curEnc (by omega)
    (fun j _ => hSc j) hBr (fun j _ hj => hV j (by omega))
  have hAbs := branchBTraceCaps_le_abs (cfg := cfg) (stepCap := stepCap) (edMul := edMul)
    (u := u) hb0 he0 hu0 (D := branchBStepData cfg ℓ' g' rem 0 st curG curU curEnc)
    (fun j => hD j)
  exact hDom j u coreH gB bPtr bW ePtr eW lB h nU uL hj (hbW.trans (hAbs j).1)
    (heW.trans (hAbs j).2.1) (hnU.trans (hAbs (j + 1)).2.2) (huL.trans (hAbs j).2.2)

end MinCostFlow.MinRatio
