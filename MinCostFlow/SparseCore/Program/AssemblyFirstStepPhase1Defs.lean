module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCode
public import MinCostFlow.SparseCore.Program.AssemblyBranchFull
public import MinCostFlow.SparseCore.BundleTreeCore

import Mathlib.Tactic

/-!
# First-phase step Phase 1 definitions (`AssemblyFirstStepPhase1Defs`)

Defines:
1. `AsmFirstCrossInactiveInv`: inactive components share no edges or endpoints with `cs.crossEdges`,
   proved for init (`asmFirstCrossInactiveInv_init`), step (`asmFirstCrossInactiveInv_step`), and
   restart (`asmFirstCrossInactiveInv_restart`).
2. `AsmFirstSlotsHeadroom`: the headroom predicate for the slot list,
   `[y.slotsPtr, y.slotsPtr + y.slotCap + 1)`.
3. Pure sequential batch-scan state `ScanBatchState`, `scanActivate`, `scanBatchStep`,
   `scanBatchFold`, and `traceOrigVert`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Cross-edge / inactive-component invariant and the slot headroom predicate -/

@[expose] public section

-- `AsmFirstCrossInactiveInv`, `asmFirstCrossInactiveInv_init`, and
-- `asmFirstCrossInactiveInv_restart` live in `AssemblyBranchSideInv.lean` (imported transitively
-- via `AssemblyFirstStepCode`) so `AsmBrSideModel` can carry `AsmFirstCrossInactiveInv`.

/-- **Slot headroom predicate**: `[y.slotsPtr, y.slotsPtr + y.slotCap + 1)` lies below `h` and is
disjoint from all other cells of the branch (`asmSdMapCell`, `asmSdPart 0..2`, and `asmBrPart 0..4`).
Once `AssemblyBranchSide.lean:191,260` changes `y.slots.length + 1` to `y.slotCap + 1`, this follows
immediately from `AsmBrRepAt` and `hfoot`. -/
def AsmFirstSlotsHeadroom {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}
    (b h : ℕ) (x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ) : Prop :=
  let y := x.xRest
  ∀ a, y.slotsPtr ≤ a → a < y.slotsPtr + y.slotCap + 1 →
    a < h ∧
    ¬ asmSdMapCell y a ∧
    (∀ i < 3, ¬ asmSdPart x.restH y i a) ∧
    (∀ i < 5, ¬ asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x i a)

end

public section

lemma compLSFStepSingle_crossInactive {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    (hnt : projCompUpdateG cs.G (cs.compSt C).G u = [])
    (hdisj : Disjoint (cs.compSt C).G.E cs.crossEdges)
    (hends : ∀ e ∈ cs.crossEdges,
      cs.G.tail e ∉ (cs.compSt C).G.V ∧ cs.G.head e ∉ (cs.compSt C).G.V) :
    let cs' := compLSFStepSingle cs u
    Disjoint (cs'.compSt C).G.E cs'.crossEdges ∧
    ∀ e ∈ cs'.crossEdges,
      cs'.G.tail e ∉ (cs'.compSt C).G.V ∧ cs'.G.head e ∉ (cs'.compSt C).G.V := by
  classical
  intro cs'
  have hCst : cs'.compSt C = cs.compSt C := by
    show applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u) = cs.compSt C
    rw [hnt]; rfl
  have hVeq : (cs'.compSt C).G.V = (cs.compSt C).G.V := by rw [hCst]
  have hEeq : (cs'.compSt C).G.E = (cs.compSt C).G.E := by rw [hCst]
  cases u with
  | delete e₀ =>
    have hcr' : cs'.crossEdges = cs.crossEdges.erase e₀ := rfl
    refine ⟨by rw [hEeq, hcr']; exact hdisj.mono_right (Finset.erase_subset _ _), fun e he => ?_⟩
    rw [hcr', Finset.mem_erase] at he; rw [hVeq]; exact hends e he.2
  | insert e₀ a b =>
    have ha_not : a ∉ (cs.compSt C).G.V := fun ha => by
      simp only [projCompUpdateG] at hnt; by_cases hb : b ∈ (cs.compSt C).G.V <;> simp [ha, hb] at hnt
    have hb_not : b ∉ (cs.compSt C).G.V := fun hb => by
      simp only [projCompUpdateG] at hnt; by_cases ha : a ∈ (cs.compSt C).G.V <;> simp [ha, hb] at hnt
    have he₀_not : e₀ ∉ (cs.compSt C).G.E := fun hmem => hu.1 (hI.hCE_sub C hC hmem)
    have hcr_sub : cs'.crossEdges ⊆ insert e₀ cs.crossEdges := fun e he => by
      change e ∈ (if ∃ C' ∈ components cs.G₀, a ∈ (cs.compSt C').G.V ∧ b ∈ (cs.compSt C').G.V
        then cs.crossEdges else insert e₀ cs.crossEdges) at he
      split_ifs at he
      · exact Finset.mem_insert_of_mem he
      · exact he
    refine ⟨?_, ?_⟩
    · rw [hEeq]
      exact Finset.disjoint_right.mpr fun e he =>
        (Finset.mem_insert.mp (hcr_sub he)).elim (fun h => h ▸ he₀_not) (fun h => Finset.disjoint_right.mp hdisj h)
    · intro e he
      rw [hVeq]
      rcases Finset.mem_insert.mp (hcr_sub he) with rfl | he0
      · simp [cs', compLSFStepSingle, MGraph.applyUpdate, ha_not, hb_not]
      · have hne : e ≠ e₀ := fun h => hu.1 (h ▸ hI.hIns_sub (hI.hCross_sub he0))
        simpa [cs', compLSFStepSingle, MGraph.applyUpdate, hne] using hends e he0
  | split v v' St Sh =>
    have hcr' : cs'.crossEdges = cs.crossEdges := rfl
    have hv'_not : v' ∉ (cs.compSt C).G.V := fun hv' =>
      hu.2.1 (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C, hC, hv'⟩)
    refine ⟨by rw [hEeq, hcr']; exact hdisj, fun e he => ?_⟩
    rw [hcr'] at he; rw [hVeq]
    obtain ⟨ht0, hh0⟩ := hends e he
    exact ⟨by change (if e ∈ St ∧ cs.G.tail e = v then v' else cs.G.tail e) ∉ _; split_ifs <;> assumption,
           by change (if e ∈ Sh ∧ cs.G.head e = v then v' else cs.G.head e) ∉ _; split_ifs <;> assumption⟩

/-- `stepBundleTree` preserves `AsmFirstCrossInactiveInv`. -/
theorem asmFirstCrossInactiveInv_step {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hInv : AsmFirstCrossInactiveInv tr) :
    AsmFirstCrossInactiveInv (stepBundleTree sparsify tr U ord ord').state := by
  intro C hC hnotAct'
  have hC0 : C ∈ components tr.cs.G₀ := by simpa [stepBundleTree, compLSFBatch_G₀] using hC
  have hnotAct : C ∉ tr.activeComps := fun h => hnotAct' (Finset.mem_union_left _ h)
  have hnotTouched : C ∉ touchedCompsBatch tr.cs U := fun h =>
    hnotAct' (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hnotAct⟩))
  have hprojNil : projCompBatchG tr.cs.G (tr.cs.compSt C).G U = [] := by
    by_contra hne; exact hnotTouched (Finset.mem_filter.mpr ⟨hC0, hne⟩)
  obtain ⟨hd0, he0⟩ := hInv C hC0 hnotAct
  suffices H : ∀ (U : List Update) (cs : CompLSFState),
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U → C ∈ components cs.G₀ →
      projCompBatchG cs.G (cs.compSt C).G U = [] →
      Disjoint (cs.compSt C).G.E cs.crossEdges →
      (∀ e ∈ cs.crossEdges, cs.G.tail e ∉ (cs.compSt C).G.V ∧ cs.G.head e ∉ (cs.compSt C).G.V) →
      Disjoint ((compLSFBatch cs U).compSt C).G.E (compLSFBatch cs U).crossEdges ∧
      ∀ e ∈ (compLSFBatch cs U).crossEdges,
        (compLSFBatch cs U).G.tail e ∉ ((compLSFBatch cs U).compSt C).G.V ∧
        (compLSFBatch cs U).G.head e ∉ ((compLSFBatch cs U).compSt C).G.V by
    exact H U tr.cs hI hU hC0 hprojNil hd0 he0
  intro U'
  induction U' with
  | nil => intro cs _ _ _ _ hd he; exact ⟨hd, he⟩
  | cons u rest ih =>
    intro cs hIcs hUcs hCcs hpn hd he
    simp only [projCompBatchG, List.append_eq_nil_iff] at hpn
    obtain ⟨hu_nil, hrest_nil⟩ := hpn
    have hCst1 : (compLSFStepSingle cs u).compSt C = cs.compSt C := by
      show applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u) = cs.compSt C
      rw [hu_nil]; rfl
    have hrest_nil' : projCompBatchG (compLSFStepSingle cs u).G
        ((compLSFStepSingle cs u).compSt C).G rest = [] := by
      rw [show (compLSFStepSingle cs u).G = cs.G.applyUpdate u from rfl, hCst1]
      simpa [hu_nil, MGraph.applyBatch] using hrest_nil
    obtain ⟨hd1, he1⟩ := compLSFStepSingle_crossInactive hIcs hUcs.1 hCcs hu_nil hd he
    exact ih _ (compLSFInv_step hIcs hUcs.1) hUcs.2 hCcs hrest_nil' hd1 he1

end

/-! ## 2. Pure sequential batch-scan model -/

@[expose] public section

/-- State maintained while scanning `U` in Phase 1. -/
structure ScanBatchState where
  cmpMap : ℕ → ℕ
  actFlag : ℕ → Bool
  insFlag : ℕ → Bool
  delFlag : ℕ → Bool
  origVert : ℕ → ℕ
  newComps : List (ℕ × ℕ)
  delEdges : List ℕ
  insEdges : List ℕ

/-- Record component `c` with witness vertex `v` if `actFlag c = false`. -/
def scanActivate (st : ScanBatchState) (c v : ℕ) : ScanBatchState :=
  if st.actFlag c then st
  else { st with
    actFlag := Function.update st.actFlag c true
    newComps := st.newComps ++ [(c, v)] }

/-- One update step of the Phase 1 batch scan, reading `G_init` (`tr.cs.G`) for `.delete e` when
`insFlag e = false`. -/
def scanBatchStep (G_init : MGraph) (st : ScanBatchState) : Update → ScanBatchState
  | .insert e a b =>
    let st1 := { st with
      insFlag := Function.update st.insFlag e true
      insEdges := st.insEdges ++ [e] }
    let st2 := scanActivate st1 (st1.cmpMap a) a
    scanActivate st2 (st2.cmpMap b) b
  | .delete e =>
    let st1 := { st with
      delFlag := Function.update st.delFlag e true
      delEdges := st.delEdges ++ [e] }
    if st1.insFlag e then st1
    else
      let u := G_init.tail e
      let v := G_init.head e
      let st2 := scanActivate st1 (st1.cmpMap u) u
      scanActivate st2 (st2.cmpMap v) v
  | .split v v' _ _ =>
    let cv := st.cmpMap v
    let ov := st.origVert v
    let ov' := if ov = 0 then v + 1 else ov
    let st1 := { st with
      cmpMap := Function.update st.cmpMap v' cv
      origVert := Function.update st.origVert v' ov' }
    scanActivate st1 cv v

/-- Fold `scanBatchStep` over an update batch `U`. -/
def scanBatchFold (G_init : MGraph) (st : ScanBatchState) (U : List Update) : ScanBatchState :=
  U.foldl (scanBatchStep G_init) st

/-- Trace `origVert` back to a pre-step vertex (`origVert v = 0` means `v` itself). -/
def traceOrigVert (origVert : ℕ → ℕ) (v : ℕ) : ℕ :=
  if origVert v = 0 then v else origVert v - 1

end

public section

@[simp] lemma scanActivate_cmpMap (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).cmpMap = st.cmpMap := by unfold scanActivate; split_ifs <;> rfl
@[simp] lemma scanActivate_origVert (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).origVert = st.origVert := by unfold scanActivate; split_ifs <;> rfl
@[simp] lemma scanActivate_insFlag (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).insFlag = st.insFlag := by unfold scanActivate; split_ifs <;> rfl
@[simp] lemma scanActivate_delFlag (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).delFlag = st.delFlag := by unfold scanActivate; split_ifs <;> rfl
@[simp] lemma scanActivate_delEdges (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).delEdges = st.delEdges := by unfold scanActivate; split_ifs <;> rfl
@[simp] lemma scanActivate_insEdges (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).insEdges = st.insEdges := by unfold scanActivate; split_ifs <;> rfl

lemma scanActivate_actFlag (st : ScanBatchState) (c v c' : ℕ) :
    (scanActivate st c v).actFlag c' = (st.actFlag c' || decide (c' = c)) := by
  unfold scanActivate
  split_ifs with h
  · by_cases heq : c' = c
    · subst heq; simp [h]
    · simp [heq]
  · by_cases heq : c' = c
    · subst heq; simp
    · simp [heq]

lemma scanActivate_newComps_len (st : ScanBatchState) (c v : ℕ) :
    (scanActivate st c v).newComps.length ≤ st.newComps.length + 1 := by
  unfold scanActivate; split_ifs <;> simp

end

end MinCostFlow.SparseCore.Program
