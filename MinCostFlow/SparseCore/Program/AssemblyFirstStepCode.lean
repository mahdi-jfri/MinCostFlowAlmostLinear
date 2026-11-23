module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSideInv
public import MinCostFlow.SparseCore.Program.AssemblyCode
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourFacts
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstSpan
public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbCopy
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep

import Mathlib.Tactic

/-!
# First-phase step sub-code and the slot invariants (`AssemblyFirstStepCode`)

Provides three things for the first phase of a branch step:

1. **A step does not keep slot cap zero** (`slotMapOK_empty_zero`, `not_slotMapOK_of_slotCap_zero`,
   `gapS5_slotCap_zero_obstruction`): `SlotMapOK` holds with `slotCap = 0` whenever
   `activePairs tr = ∅`, but no side `xRest` with `xRest.slotCap = 0` meets `AsmBrSideModel` once a
   step activates a component with a nonempty bucket. The post of `AsmBrCoreStepAt.runs` keeps
   `slotCap`, so the step needs an invariant that leaves room for new slots.
2. **Side invariants (`AsmFirstSideSlotInv`, `AsmFirstInactiveCompInv`)**: they give this room, and
   the file proves slot-allocation availability (`asmFirstSideSlotInv_next_free`).
3. **Relocatable deterministic `ScSubCode` (`asmFirstStepSubProcs`, `asmFirstStepSubCode`)**:
   packages all verified deterministic first-phase sub-procedures on `ScFirstEnv` (confirming
   `ScFirstEnv` has every base needed, including `sortProcs` at `env.bBun + bundleOffSort`) and
   lifts `AsmFirstTourRootAt` and `asmFirstTourBlockProcs` directly into `scProg`. P5's new-cost
   step is available via `bunTableHeadroom_step_model_runs_on`
   (`BundleCapHeadroomStep.lean`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## 1. Slot cap zero, and the side invariants -/

public section

/-- When `activePairs tr = ∅`, `slotCap = 0`, `cap = 0`, `slots = []` satisfies `SlotMapOK`. -/
theorem slotMapOK_empty_zero {depth : ℕ} {tr : BundleTreeState depth}
    (hEmpty : activePairs tr = ∅) (slotOf : Finset ℕ × ℤ → ℕ) :
    SlotMapOK tr 0 0 [] slotOf := by
  refine ⟨List.nodup_nil, ?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hEmpty] at hp; cases hp
  · intro s hs; cases hs
  · intro p₁ hp₁; rw [hEmpty] at hp₁; cases hp₁
  · intro s hs; cases hs

/-- Whenever `activePairs tr'` is nonempty, `SlotMapOK` cannot hold with `slotCap = 0`. -/
theorem not_slotMapOK_of_slotCap_zero {depth cap : ℕ} {tr' : BundleTreeState depth}
    {slots : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    (hNe : (activePairs tr').Nonempty) :
    ¬ SlotMapOK tr' 0 cap slots slotOf := by
  intro hOK
  obtain ⟨p, hp⟩ := hNe
  have hs := hOK.2.1 p hp
  exact Nat.not_lt_zero _ (hOK.2.2.2.2 (slotOf p) hs).1

/-- **A step does not keep slot cap zero**:
if `x.xRest.slotCap = 0` (which is permitted by `AsmBrSideModel` whenever `activePairs tr = ∅`) and
`stepBundleTree` activates a component with at least one bucket (so `(activePairs info.state).Nonempty`),
then **no** post-step side `xRest` can simultaneously satisfy `xRest.slotCap = x.xRest.slotCap` and
`AsmBrSideModel ... ⟨info.state, ord', vCap, eCap⟩ xRest` (a required conjunct of
`AsmBrCoreStepAt.runs`, `AssemblyBranchStepIface.lean:134-136`). -/
theorem gapS5_slotCap_zero_obstruction
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul vCap eCap : ℕ}
    {Ψ : BundleTreeState depth → ℕ}
    {tr' : BundleTreeState depth} {ord' : ℕ → List End}
    {xRest : AsmBrSide B5 depth}
    (hNe : (activePairs tr').Nonempty)
    (hCap0 : xRest.slotCap = 0) :
    ¬ AsmBrSideModel impl w depth L capExp limbMul Ψ ⟨tr', ord', vCap, eCap⟩ xRest := by
  intro hM
  have hOK := hM.1
  rw [hCap0] at hOK
  exact not_slotMapOK_of_slotCap_zero hNe hOK

/-- Under `AsmFirstSideSlotInv`, if `activePairs tr` is a strict subset of all pairs of `G₀`
(`q ∉ activePairs tr` with `q.1 ∈ components tr.cs.G₀` and `q.2 ∈ tr.activeBuckets q.1`),
then the next sequential slot `s := y.slots.length` is strictly below both `y.slotCap` and `y.cap`
and is free (`none`) in both `y.bunS` and `y.spanS`. -/
theorem asmFirstSideSlotInv_next_free
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth : ℕ} {tr : BundleTreeState depth} {y : AsmBrSide B5 depth}
    (hOK : SlotMapOK tr y.slotCap y.cap y.slots y.slotOf)
    (hInv : AsmFirstSideSlotInv tr y)
    (hActSub : tr.activeComps ⊆ components tr.cs.G₀)
    {C : Finset ℕ} {b : ℤ}
    (hC : C ∈ components tr.cs.G₀) (hb : b ∈ tr.activeBuckets C)
    (hNotAct : (C, b) ∉ activePairs tr) :
    ∃ (hsB : y.slots.length < y.slotCap) (hsS : y.slots.length < y.cap),
      y.bunS ⟨y.slots.length, hsB⟩ = none ∧ y.spanS ⟨y.slots.length, hsS⟩ = none := by
  obtain ⟨hCapLe, hRange, hBunNone, hSpanNone⟩ := hInv
  have hlen : y.slots.length = tr.activeComps.sum (fun C' => (tr.activeBuckets C').card) :=
    hOK.length_eq
  have hC_not : C ∉ tr.activeComps := fun hCin =>
    hNotAct (Finset.mem_biUnion.mpr ⟨C, hCin, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩)
  have hSubIns : insert C tr.activeComps ⊆ components tr.cs.G₀ :=
    Finset.insert_subset hC hActSub
  have hSumLe : (tr.activeBuckets C).card + y.slots.length ≤
      (components tr.cs.G₀).sum (fun C' => (tr.activeBuckets C').card) := by
    rw [hlen, ← Finset.sum_insert (f := fun C' => (tr.activeBuckets C').card) hC_not]
    exact Finset.sum_le_sum_of_subset hSubIns
  have hPos : 0 < (tr.activeBuckets C).card := Finset.card_pos.mpr ⟨b, hb⟩
  have hltMin : y.slots.length < min y.slotCap y.cap := by omega
  have hsB : y.slots.length < y.slotCap := lt_of_lt_of_le hltMin (min_le_left _ _)
  have hsS : y.slots.length < y.cap := lt_of_lt_of_le hltMin (min_le_right _ _)
  have hNotMem : y.slots.length ∉ y.slots := by
    intro hm
    have hm' : y.slots.length ∈ List.range y.slots.length := by
      have hEq : (y.slots.length ∈ y.slots) = (y.slots.length ∈ List.range y.slots.length) :=
        congrArg (y.slots.length ∈ ·) hRange
      exact hEq ▸ hm
    exact Nat.lt_irrefl _ (List.mem_range.mp hm')
  exact ⟨hsB, hsS, hBunNone ⟨y.slots.length, hsB⟩ hNotMem, hSpanNone ⟨y.slots.length, hsS⟩ hNotMem⟩

end

/-! ## 3. Relocatable deterministic `ScSubCode` for verified first-phase sub-blocks -/

@[expose] public section

/-- Offsets within `asmFirstStepSubProcs env` (placed at `env.bSelf`). -/
def firstStepOffVertRoot : ℕ := 0
def firstStepOffTourBlock : ℕ := 1
def firstStepOffTourMain : ℕ := 3
def firstStepOffSpanUpd : ℕ := 4
def firstStepOffBuildDel : ℕ := 5
def firstStepOffBuildIns : ℕ := 6
def firstStepOffBuildRot : ℕ := 7
def firstStepOffCopyIns : ℕ := 8
def firstStepOffCopySlot : ℕ := 9

/-- Relocatable deterministic block of all verified first-phase step sub-procedures using only
offsets provided by `ScFirstEnv` (`sortProcs` sits at `env.bBun + bundleOffSort`):
* `0`: `asmFirstTourVertRootStmt (tourOp env.bTour 10)`
* `1..3`: `asmFirstTourBlockProcs (env.bSelf + 1) env.bTour env.bOut env.readLib.copy`
* `4`: `asmFirstSpanUpdStmt (env.bSpan + bsIdxOp0 + 1)`
* `5`: `asmFirstBuildDelStmt (env.bBun + bundleOffSort)`
* `6`: `asmFirstBuildInsStmt (env.bBun + bundleOffSort)`
* `7`: `asmFirstBuildRotStmt (env.bBun + bundleOffSort)`
* `8`: `asmFirstCopyInsStmt`
* `9`: `asmFirstCopySlotListStmt env.readLib.copy (env.bSpan + bsOffRead + spanReadIdxPiWalkPtr)` -/
def asmFirstStepSubProcs (env : ScFirstEnv) : List Stmt :=
  [asmFirstTourVertRootStmt (tourOp env.bTour 10)] ++
  asmFirstTourBlockProcs (env.bSelf + firstStepOffTourBlock) env.bTour env.bOut env.readLib.copy ++
  [asmFirstSpanUpdStmt (env.bSpan + bsIdxOp0 + 1),
   asmFirstBuildDelStmt (env.bBun + bundleOffSort),
   asmFirstBuildInsStmt (env.bBun + bundleOffSort),
   asmFirstBuildRotStmt (env.bBun + bundleOffSort),
   asmFirstCopyInsStmt,
   asmFirstCopySlotListStmt env.readLib.copy (env.bSpan + bsOffRead + spanReadIdxPiWalkPtr)]

end

public section

theorem asmFirstStepSubProcs_noRand (env : ScFirstEnv) :
    ∀ s ∈ asmFirstStepSubProcs env, s.NoRand := by
  intro s hs
  unfold asmFirstStepSubProcs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | htb) | (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact asmFirstTourVertRootStmt_noRand _
  · exact asmFirstTourBlockProcs_noRand _ _ _ _ s htb
  · exact asmFirstSpanUpdStmt_noRand _
  · exact asmFirstBuildDelStmt_noRand _
  · exact asmFirstBuildInsStmt_noRand _
  · exact asmFirstBuildRotStmt_noRand _
  · exact asmFirstCopyInsStmt_noRand
  · exact asmFirstCopySlotListStmt_noRand _ _

end

@[expose] public section

/-- `ScSubCode` packaging the verified deterministic first-phase step sub-blocks. -/
def asmFirstStepSubCode : ScSubCode where
  procs := asmFirstStepSubProcs
  hnoRand := asmFirstStepSubProcs_noRand
  offMain := firstStepOffTourMain

end

public section

/-- Inside `scProg impl cf asmFirstStepSubCode firstInit`, `asmFirstTourVertRootStmt` sits at
`L.bFirstS + firstStepOffVertRoot` and satisfies `AsmFirstTourRootAt tourAsmRep`. -/
def scProg_asmFirstTourVertRoot_runs (impl : SparsifyImpl) (cf : ScCompCode)
    (firstInit : ScSubCode) (w : ℕ) :
    let L := scLayout impl cf asmFirstStepSubCode firstInit
    AsmFirstTourRootAt tourAsmRep w (scProg impl cf asmFirstStepSubCode firstInit)
      (L.bFirstS + firstStepOffVertRoot) := by
  dsimp only
  have hp := scProg_hasFirstStep impl cf asmFirstStepSubCode firstInit
  have h0 : (scProg impl cf asmFirstStepSubCode firstInit).procs[
      (scLayout impl cf asmFirstStepSubCode firstInit).bFirstS + firstStepOffVertRoot]? =
      some (asmFirstTourVertRootStmt (tourOp (scLayout impl cf asmFirstStepSubCode firstInit).bTour 10)) := by
    have h := hp 0 (by simp [asmFirstStepSubCode, asmFirstStepSubProcs, asmFirstTourBlockProcs])
    simpa [asmFirstStepSubCode, asmFirstStepSubProcs, firstStepOffVertRoot, scLayout] using h
  exact asmFirstTourVertRoot_runs w (scLayout impl cf asmFirstStepSubCode firstInit).bTour
    ((scLayout impl cf asmFirstStepSubCode firstInit).bFirstS + firstStepOffVertRoot)
    (scProg impl cf asmFirstStepSubCode firstInit)
    (scProg_hasTour impl cf asmFirstStepSubCode firstInit) h0

/-- Inside `scProg impl cf asmFirstStepSubCode firstInit`, `asmFirstTourBlockProcs` sits at
`L.bFirstS + firstStepOffTourBlock`. -/
theorem scProg_hasFirstTourBlockProcs (impl : SparsifyImpl) (cf : ScCompCode)
    (firstInit : ScSubCode) :
    let L := scLayout impl cf asmFirstStepSubCode firstInit
    (scProg impl cf asmFirstStepSubCode firstInit).HasAt (L.bFirstS + firstStepOffTourBlock)
      (asmFirstTourBlockProcs (L.bFirstS + firstStepOffTourBlock) L.bTour L.bOut L.readLib.copy) := by
  intro L i hi
  have hp := scProg_hasFirstStep impl cf asmFirstStepSubCode firstInit
  have hi3 : i < 3 := by simpa [asmFirstTourBlockProcs] using hi
  match i, hi3 with
  | 0, _ =>
    have h := hp 1 (by simp [asmFirstStepSubCode, asmFirstStepSubProcs, asmFirstTourBlockProcs])
    simpa [asmFirstStepSubCode, asmFirstStepSubProcs, firstStepOffTourBlock, scLayout,
      asmFirstTourBlockProcs, L] using h
  | 1, _ =>
    have h := hp 2 (by simp [asmFirstStepSubCode, asmFirstStepSubProcs, asmFirstTourBlockProcs])
    have hidx : L.bFirstS + firstStepOffTourBlock + 1 = L.bFirstS + 2 := by
      simp [firstStepOffTourBlock]
    rw [hidx]
    simpa [asmFirstStepSubCode, asmFirstStepSubProcs, firstStepOffTourBlock, scLayout,
      asmFirstTourBlockProcs, L] using h
  | 2, _ =>
    have h := hp 3 (by simp [asmFirstStepSubCode, asmFirstStepSubProcs, asmFirstTourBlockProcs])
    have hidx : L.bFirstS + firstStepOffTourBlock + 2 = L.bFirstS + 3 := by
      simp [firstStepOffTourBlock]
    rw [hidx]
    simpa [asmFirstStepSubCode, asmFirstStepSubProcs, firstStepOffTourBlock, scLayout,
      asmFirstTourBlockProcs, L] using h

end

end MinCostFlow.SparseCore.Program
