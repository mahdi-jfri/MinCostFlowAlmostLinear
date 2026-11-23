module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopRunKFBL
import WordRAM.Tactic

/-!
# The invariant of the Branch B loop after one plain pass (`WireChainCoreBranchBLoopInvKFBL`)

After one plain pass at level `idx` (`wireBranchBLoopBodyKFBL_runs_plain`), the invariant
`BranchBLoopInvKFBL` holds at level `idx + 1` for the next model state of
`Chain.Ordered.updateLoop` (`updateLoopNext`). The core of level `idx` gets its new token, its
slot is finished (`BranchBDoneSlots.step`), the forwarded batch and edits become the input of the
next level, and every other word that the invariant reads is kept by the frame of the step.

* `updateLoopNext`: the model state after the plain step at `idx`, as in `UpdateLoopModelInv`.
* `BranchBStaticWord`, `branchBStaticWord_off`: the words of the fixed arrays lie below `selBase`,
  off every core footprint, off every graph and length block and off the update counters.
* `branchBPhiSum`: the sum of the potentials of the cores of the levels `j < d`.
* `branchBLoopInvKFBL_pass`: the invariant at `idx + 1`, the model and size invariants at
  `idx + 1`, and the cost of the pass against the potentials of all cores.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The model state after the plain step of `Chain.Ordered.updateLoop` at level `idx`, as in the
recursion of `UpdateLoopModelInv`. -/
@[expose] noncomputable def updateLoopNext (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    ChainState cfg.T cfg.P :=
  let Cpartial : TreeChain :=
    { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
  let ℓi := Cpartial.chainLen ℓ' idx
  let gi := Cpartial.chainGrad g' idx
  let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
    (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
      st.scState st.bran idx)
  let sc' := updRes.1
  let nextU := updRes.2 (st.bran idx)
  let nextEnc := (st.G (idx + 1)).batchEnc nextU
  let fiChanges := diffTreeChanges (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E
    (cfg.T.lsfs sc' (st.bran idx)).F.F.E
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

theorem updateLoopNext_G (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    (updateLoopNext cfg ℓ' g' idx st curG curU curEnc).G =
      fun j => if j = idx then curG else st.G j := rfl

theorem updateLoopNext_scState (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    (updateLoopNext cfg ℓ' g' idx st curG curU curEnc).scState =
      fun j => if j = idx then
        (cfg.T.updateOrd (st.scState idx) curU
          (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } :
            TreeChain).chainLen ℓ' idx)
          (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } :
            TreeChain).chainGrad g' idx)
          (chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
            st.scState st.bran idx)).1
      else st.scState j := rfl

theorem updateLoopNext_updCount (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    (updateLoopNext cfg ℓ' g' idx st curG curU curEnc).updCount =
      fun j => if j = idx then st.updCount idx + curU.length else st.updCount j := rfl

/-- The words of the fixed arrays of Branch B: the solver header, the threshold table, the
handle and branch arrays (with the cells of the last level), the level-size and level-meta arrays
and the rebuild counters. -/
@[expose] def BranchBStaticWord (d : ℕ) (A : BranchBAddrs) (a : ℕ) : Prop :=
  (A.handle ≤ a ∧ a < A.handle + 18) ∨ (A.table ≤ a ∧ a < A.table + d) ∨
  (A.handleBase ≤ a ∧ a ≤ A.handleBase + d) ∨ (A.branchBase ≤ a ∧ a ≤ A.branchBase + d) ∨
  (A.lvlMTable ≤ a ∧ a < A.lvlMTable + d) ∨ (A.levelMeta ≤ a ∧ a < A.levelMeta + 2 * d) ∨
  (A.rcBase ≤ a ∧ a < A.rcBase + d)

/-- A word of the fixed arrays lies below `selBase`, off every core footprint, off every graph
and length block, and is not an update counter. -/
theorem branchBStaticWord_off {L vCap eCap a : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs} {tok : ℕ → Rcore.τ}
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hst : BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L A.handle A.table A.handleBase
      A.branchBase A.lvlMTable A.levelMeta A.rcBase A.ucBase (fun _ => vCap) (fun _ => eCap)
      A.gPtr0 A.lPtr0 A.coreH tok)
    (ha : BranchBStaticWord cfg.P.d A a) :
    a < A.selBase ∧ (∀ r < cfg.P.d, ¬ Rcore.foot (A.coreH r) (tok r) a) ∧
    (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
      (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) ∧
    (∀ j < cfg.P.d, a ≠ A.ucBase + j) := by
  have h1 := S.handleLt; have h2 := S.tableLt; have h3 := S.hbLt; have h4 := S.bbLt
  have h5 := S.lvlMLt; have h6 := S.metaLt; have h7 := S.rcLt
  refine ⟨by unfold BranchBStaticWord at ha; omega, fun r hr => ?_, fun j hj => ⟨?_, ?_⟩,
    fun j hj => ?_⟩
  · obtain ⟨hH, hT, hHB, hM, _, _⟩ := hst r hr
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ |
      ⟨ha1, ha2⟩
    · exact hH a ha1 ha2
    · obtain ⟨j, rfl⟩ : ∃ j, a = A.table + j := ⟨a - A.table, by omega⟩
      exact hT j (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, a = A.handleBase + j := ⟨a - A.handleBase, by omega⟩
      exact (hHB j (by omega)).1
    · obtain ⟨j, rfl⟩ : ∃ j, a = A.branchBase + j := ⟨a - A.branchBase, by omega⟩
      exact (hHB j (by omega)).2
    · obtain ⟨j, rfl⟩ : ∃ j, a = A.lvlMTable + j := ⟨a - A.lvlMTable, by omega⟩
      exact (hM j (by omega)).1
    · by_cases hlt : a < A.levelMeta + cfg.P.d
      · obtain ⟨j, rfl⟩ : ∃ j, a = A.levelMeta + j := ⟨a - A.levelMeta, by omega⟩
        exact (hM j (by omega)).2.1
      · obtain ⟨j, rfl⟩ : ∃ j, a = A.levelMeta + cfg.P.d + j :=
          ⟨a - A.levelMeta - cfg.P.d, by omega⟩
        exact (hM j (by omega)).2.2.1
    · obtain ⟨j, rfl⟩ : ∃ j, a = A.rcBase + j := ⟨a - A.rcBase, by omega⟩
      exact (hM j (by omega)).2.2.2.2
  · by_contra hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, _, _⟩ :=
      S.gSep j hj a (by omega) (by omega)
    unfold BranchBStaticWord at ha
    omega
  · by_contra hc
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ :=
      S.lSep j hj a (by omega) (by omega)
    unfold BranchBStaticWord at ha
    omega
  · rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ |
      ⟨ha1, ha2⟩
    · rcases S.sepUCH with h | h <;> omega
    · rcases S.sepTabUC with h | h <;> omega
    · rcases S.sepUCHB with h | h <;> omega
    · rcases S.sepUCBB with h | h <;> omega
    · rcases S.sepUCM with h | h <;> omega
    · rcases S.sepUCLM with h | h <;> omega
    · rcases S.sepRCUC with h | h <;> omega

/-- The sum of the potentials of the cores of the levels `j < d`. -/
@[expose] def branchBPhiSum {cfg : Alg2Config} (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (A : BranchBAddrs) (tok : ℕ → Rcore.τ) (mem : ℕ → ℕ) : ℕ :=
  (Finset.range cfg.P.d).sum fun j => Rcore.phi (A.coreH j) (tok j) mem

end MinCostFlow.MinRatio
