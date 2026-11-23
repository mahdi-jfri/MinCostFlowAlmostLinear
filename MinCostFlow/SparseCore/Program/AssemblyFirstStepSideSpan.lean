module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideModel

import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4
import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideMaps
import Mathlib.Tactic

/-!
# The spanners after the first step (`AssemblyFirstStepSideSpan`)

Each pair of the new state must have, in the spanners after the tasks of Phase 4, a history
whose state is its spanner in the new state, with the old initial graph and with nonempty batches
of deletions and splits that are valid on it (`AsmFsSideSpanGoal`). This file proves it
(`asmFirstStep_hSpan_of`).

* The slot model of Phase 4 (`P4SlotModel`) holds: Phases 2 and 3 give the slot model on the
  tasks (`asmFirstStep_p4_slotTasks`, as in `AssemblyFirstStepHP4.lean`), and the first four
  posts of Phase 4 give the rest (`P4SlotTasks.model`). So the slot of each pair holds a history
  with the right state (`P4SlotModel.after`).
* The batches of the history are deletions and splits, valid on its initial graph: the
  spanners after Phase 4 hold their histories (the rep of the spanners, post 5 of Phase 4).
* The history is that of Phase 2 or the one with the batch of a task added
  (`p4SpanAfter_cases`). This keeps the initial graph. An added batch is not empty, since the
  first word of a batch is `0` exactly when the batch of the pair is empty.

The last result, `asmFirstStep_hSide_full`, puts the pieces of the side together: `AsmFsSideGoal`
from the first conjunct of `hVerts`, the two word bounds `hWB` and `1 ≤ max impl.p_s impl.p_t`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **A slot after the tasks** keeps its history, or holds the history of the first spanners
`S6` at that slot with the batch of a task on that slot added, when that batch is not empty. -/
theorem p4SpanAfter_cases (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (j : Fin cap) :
    ∀ (ts : List SpanUpdTask) (S : BucketSpannerState cap),
      ts.foldl (p4SpanStep P S6 mem₀) S j = S j ∨
      ∃ t ∈ ts, ∃ d₀ : DSHist, t.slot = j.1 ∧ S6 j = some d₀ ∧ mem₀ t.batchPtr ≠ 0 ∧
        ts.foldl (p4SpanStep P S6 mem₀) S j = some (p4NewHist P mem₀ d₀ t) := by
  intro ts
  induction ts with
  | nil => exact fun S => Or.inl rfl
  | cons t ts ih =>
    intro S
    rw [List.foldl_cons]
    rcases ih (p4SpanStep P S6 mem₀ S t) with h | ⟨t', ht', d₀, h1, h2, h3, h4⟩
    · rw [h]
      unfold p4SpanStep p4OnTask
      by_cases hs : t.slot < cap
      · simp only [hs, ↓reduceDIte]
        rcases hd : S6 ⟨t.slot, hs⟩ with _ | d
        · exact Or.inl rfl
        · by_cases hb : mem₀ t.batchPtr = 0
          · simp only [hb, ↓reduceIte]
            exact Or.inl (by first | rfl | trivial)
          · simp only [hb, ↓reduceIte]
            by_cases hj : j = ⟨t.slot, hs⟩
            · subst hj
              refine Or.inr ⟨t, List.mem_cons_self, d, rfl, hd, hb, ?_⟩
              simp [BucketSpannerState.set]
            · left
              simp [BucketSpannerState.set, Function.update_of_ne hj]
      · simp only [hs, ↓reduceDIte]
        exact Or.inl (by first | rfl | trivial)
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', d₀, h1, h2, h3, h4⟩

/-- **A history held by the spanners has batches of deletions and splits, valid on its initial
graph**: the rep of the slot (`DSRepAt`) says so. -/
theorem bucketSpannerRep_slot_flat {P : DSParams} {cap tbl : ℕ} {S : BucketSpannerState cap}
    {x : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ} (h : (bucketSpannerRep P cap).rep tbl S x mem)
    {j : Fin cap} {d : DSHist} (hj : S j = some d) :
    d.G₀.BatchIsValid d.flat ∧ ∀ u ∈ d.flat, isDelOrSplit u := by
  have hslot := h.1 j
  rw [hj] at hslot
  cases hx : x.slots j with
  | none =>
    rw [hx] at hslot
    exact hslot.elim
  | some bm =>
    rw [hx] at hslot
    obtain ⟨-, ⟨-, hdsRep, -⟩, -⟩ := hslot
    obtain ⟨-, -, -, -, hBV, hds, -⟩ := hdsRep
    exact ⟨hBV, hds⟩

set_option maxHeartbeats 8000000 in
/-- **The spanners after the step** (`AsmFsSideSpanGoal`). -/
theorem asmFirstStep_hSpan_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ} :
    AsmFsSideSpanGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hTx ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -, hBat, hU, -, -, hOB, -, -, -, -, -, -, -, -, -,
    hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨hSMO, -, -, -, -, hk, ⟨C_lsst, ℓ₀, hI, -, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hSlotInvOld, hInact, -, hInactDyn, hPart, hDynGOld, -⟩ := hMod
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hset, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, -, -, -, -, -, -, -, -, -, -, -, hslots', hkeepSlot,
    hSlotN, hMatch, hspanS, hSlotInv, -⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnd3, -, -, hdesc3, hunt3, hnone3, -⟩ := hP3
  obtain ⟨hqs, hqsOK, hns, hnsOK, hRepX', -⟩ := hP4
  have hNew : ∀ C ∈ (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset,
      C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := by
    intro C hC
    rw [hset] at hC
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hC
    exact ⟨touchedCompsBatch_subset _ _ h1, h2⟩
  have hSlot' : SlotMapOK { tr with activeComps := tr.activeComps ∪
      (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G (asmFirstScanStart mem
          xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset } y'.slotCap y'.cap y'.slots
      y'.slotOf := by
    rw [hslc, hcap5]
    exact hSlotN
  have hBReady := asmFirstStep_phase3_ready (ord' := applyOrdEdits ord ed) hI hk hU hOB hPart
    hInact hNew hSlot' hMatch hSlotInv.2.2.1
  have hT := asmFirstStep_p4_slotTasks (P := asmBrSP impl w depth y') hset
    (fun q hq => by
      obtain ⟨hs, d, h1, h2, -⟩ := hspanS q hq
      exact ⟨hs, d, h1, h2⟩)
    hSMO hSlotInvOld.2.1 hSlotN hslots' hkeepSlot hSlot' hMatch hSlotInv.2.2.1 hBReady
    (p4_dynGraphEq (fun _ => canonicalSparsify impl) (U := U) (ord' := applyOrdEdits ord ed)
      hInact hInactDyn hDynGOld)
    hnd3 hdesc3 hunt3 hnone3
  have hSM := hT.model hqs hqsOK hns hnsOK
  intro q hq
  obtain ⟨hs, d, hd, hst⟩ := hSM.after rfl hq
  rw [hqs] at hd
  obtain ⟨hBV, hds⟩ := bucketSpannerRep_slot_flat hRepX' hd
  obtain ⟨hs₀, d₀, hd₀, -, hG₀, -, -, hUs₀⟩ := hspanS q
    (by rw [activePairs_mid_eq (fun _ => canonicalSparsify impl) tr U ord (applyOrdEdits ord ed)
      hset]; exact hq)
  refine ⟨hs, d, hd, hst, ?_, hds, hBV, ?_⟩
  all_goals
    rcases p4SpanAfter_cases (asmBrSP impl w depth y') y'.spanS st₃.mem ⟨y'.slotOf q, hs⟩
      (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) y'.spanS with h1 | ⟨t, ht, d₁, h1, h2, h3, h4⟩
  · -- the slot keeps its history
    have hdd : d = d₀ := by
      have := hd.symm.trans h1
      rw [hd₀] at this
      exact Option.some.inj this
    rw [hdd]
    exact hG₀
  · -- the slot holds the history with a batch added
    have hd₁ : d₁ = d₀ := by
      rw [hd₀] at h2
      exact (Option.some.inj h2).symm
    have hdd : d = p4NewHist (asmBrSP impl w depth y') st₃.mem d₁ t := by
      have := hd.symm.trans h4
      exact (Option.some.inj this)
    rw [hdd, hd₁]
    exact hG₀
  · have hdd : d = d₀ := by
      have := hd.symm.trans h1
      rw [hd₀] at this
      exact Option.some.inj this
    rw [hdd]
    exact hUs₀
  · have hd₁ : d₁ = d₀ := by
      rw [hd₀] at h2
      exact (Option.some.inj h2).symm
    have hdd : d = p4NewHist (asmBrSP impl w depth y') st₃.mem d₁ t := by
      have := hd.symm.trans h4
      exact (Option.some.inj this)
    rw [hdd, hd₁]
    intro B hB
    simp only [p4NewHist, List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hUs₀ B hB
    · -- the batch of the task is that of the pair, and it is not empty
      rw [← hqs] at ht
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp ht
      obtain ⟨p', hp', hsl', hbat⟩ := hSM.htask q' hq'
      have hpp : p' = q := hSM.hinj p' hp' q hq (hsl'.symm.trans h1)
      subst hpp
      have hs' : q'.1.slot < y'.cap := h1 ▸ hs
      have hd₀' : y'.spanS ⟨q'.1.slot, hs'⟩ = some d₀ := by
        rw [show (⟨q'.1.slot, hs'⟩ : Fin y'.cap) = ⟨y'.slotOf p', hs⟩ from Fin.ext h1]
        exact hd₀
      obtain ⟨hdec, hzero⟩ := hbat hs' d₀ hd₀'
      rw [hdec]
      exact fun hnil => h3 (hzero.mpr hnil)
/-- **The bundle side after the step** (`AsmFsSideGoal`, conjunct 6 of `hNC`), from the vertices
of the batch below `vCap` (`hVerts`, the first conjunct of `asmFirstStep_hVerts`), the two word
bounds on the spanner sizes (`hWB`, `asmFirstStep_sideWordBounds_of_spaceStd`), and
`1 ≤ max impl.p_s impl.p_t` (`hp`). -/
theorem asmFirstStep_hSide_full {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ} (hp : 1 ≤ max impl.p_s impl.p_t)
    (hWB : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      A.x.xRest.spV + A.x.xRest.spE + 2 < 2 ^ w ∧
      (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w)
    (hVerts : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      ∀ v ∈ batchVerts A.U, v < A.x.vCap) :
    AsmFsSideGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p hRoot
      bBun bTourStep fDelTriples fBuildGroups K space :=
  asmFirstStep_hSide_of (asmFirstStep_hMaps_of hVerts)
    (asmFirstStep_hModel_of hp hWB asmFirstStep_hSpan_of)
end

end MinCostFlow.SparseCore.Program
