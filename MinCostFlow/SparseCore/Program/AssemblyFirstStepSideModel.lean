module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSide

import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideStep
import Mathlib.Tactic

/-!
# The model facts of the bundle side after the first step (`AssemblyFirstStepSideModel`)

The bundle side after the step (`asmFsSideAfter`) must keep the model facts (`AsmBrSideModel`)
for the new state. `asmBrSideModel_step` gives them from the old facts and from what the phases
give on the new side. This file feeds it (`asmFirstStep_hModel_of`):

* the slot map of Phase 2 is one for the pairs of the new state, since these are the pairs of the
  state of Phase 2 (`activePairs_mid_eq`, with the set of the new components of the scan);
* the bundle table of Phase 3 matches the new state and keeps the restart facts (posts 3, 4);
* the spanners after Phase 4 hold the spanners of the new state (`AsmFsSideSpanGoal`, left as a
  goal);
* the free slots stay free: the bundle table maps only used slots, and the tasks of Phase 4 never
  fill a free slot (`p4SpanAfter_none`);
* the two word bounds on the spanner sizes (`hWB`) come from the room of the call.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The spanners after the step**: each pair of the new state has, in the spanners after the
tasks of Phase 4, a history whose state is its spanner in the new state, with the old initial
graph, and with nonempty batches of deletions and splits that are valid on it. -/
def AsmFsSideSpanGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    ∀ q ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify impl) A.tr A.U A.ord
        (applyOrdEdits A.ord A.ed)).state,
      ∃ (hs : y'.slotOf q < y'.cap) (d : DSHist),
        p4SpanAfter (asmBrSP impl w depth y') y'.spanS st₃.mem
          (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) ⟨y'.slotOf q, hs⟩ = some d ∧
        d.state (asmBrSP impl w depth y') = (stepBundleTree (fun _ => canonicalSparsify impl)
          A.tr A.U A.ord (applyOrdEdits A.ord A.ed)).state.dyn q ∧
        d.G₀ = A.tr.initBunG q ∧ (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧
        (∀ B ∈ d.Us, B ≠ [])

end

public section

/-- **A free slot stays free under the tasks of Phase 4**: a task fills only a slot that held a
history. -/
theorem p4SpanAfter_none (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    {j : Fin cap} (hj : S6 j = none) (ts : List SpanUpdTask) :
    ∀ S : BucketSpannerState cap, S j = none → ts.foldl (p4SpanStep P S6 mem₀) S j = none := by
  induction ts with
  | nil => exact fun S hS => hS
  | cons t ts ih =>
    intro S hS
    rw [List.foldl_cons]
    refine ih _ ?_
    unfold p4SpanStep p4OnTask
    by_cases hs : t.slot < cap
    · simp only [hs, ↓reduceDIte]
      rcases hd : S6 ⟨t.slot, hs⟩ with _ | d
      · exact hS
      · by_cases hb : mem₀ t.batchPtr = 0
        · simp only [hb, ↓reduceIte]
          exact hS
        · have hne : j ≠ ⟨t.slot, hs⟩ := fun h => by
            rw [h, hd] at hj
            cases hj
          simp [hb, BucketSpannerState.set, Function.update_of_ne hne, hS]
    · simp only [hs, ↓reduceDIte]
      exact hS

set_option maxHeartbeats 8000000 in
/-- **The model facts of the bundle side after the step** (`AsmFsSideModelGoal`), from the
spanners after the step (`hSpan`), the two word bounds on the spanner sizes (`hWB`), and
`1 ≤ max impl.p_s impl.p_t` (`hp`). -/
theorem asmFirstStep_hModel_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ} (hp : 1 ≤ max impl.p_s impl.p_t)
    (hWB : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      A.x.xRest.spV + A.x.xRest.spE + 2 < 2 ^ w ∧
      (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w)
    (hSpan : AsmFsSideSpanGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne
      fInitSpan p hRoot bBun bTourStep fDelTriples fBuildGroups K space) :
    AsmFsSideModelGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  obtain ⟨hw, hcw⟩ := hWB A hA
  have hspan := hSpan A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hspan hw hcw hTx ⊢
  obtain ⟨-, -, hL1, -, hw16, -, -, -, hBUB', hR, hFacts, hBat, hU, -, -, hOB, -, -, -, -, -, -,
    -, -, -, hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hfootE : ∀ a, embFoot xRest.eCap5 embH yEmb a → a < h :=
    fun a ha => hfoot a ⟨2, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hdisjES : ∀ a, embFoot xRest.eCap5 embH yEmb a → ¬ asmSdFoot restH xRest a :=
    fun a he hs => hDisj 2 (by decide) 5 (by decide) (by decide) a he hs
  have hdisjET : ∀ a, embFoot xRest.eCap5 embH yEmb a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a he ht => hDisj 2 (by decide) 4 (by decide) (by decide) a he ht
  -- the scan and the post of Phase 2
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hNew, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, hsplB, hspV, hspE, hmMax, -, -, -, -, hkB', -, hlgF,
    -, -, hSlotN, -, -, hSI, -⟩ := hP2
  obtain ⟨-, -, hBRI, hBTM, -⟩ := hP3
  have hAP := activePairs_mid_eq (fun _ => canonicalSparsify impl) tr U ord
    (applyOrdEdits ord ed) hNew
  refine asmBrSideModel_step (n := n) hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hFacts hBUB' hU
    hOB hkB' hsplB hspV hspE hmMax hlgF ?_ hBTM hspan hBRI rfl ?_ hL1 hp hw16 hw hcw
  · show SlotMapOK _ y'.slotCap y'.cap y'.slots y'.slotOf
    unfold SlotMapOK
    rw [← hAP, hslc, hcap5]
    exact hSlotN
  · obtain ⟨s1, s2, s3, s4⟩ := hSI
    refine ⟨?_, s2, fun j hj => ?_, fun j hj => ?_⟩
    · have hG0 : (compLSFBatch tr.cs U).G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
      show (components (compLSFBatch tr.cs U).G₀).sum (fun C => (tr.activeBuckets C).card) ≤
        min (min y'.slotCap y'.cap) y'.slotsCap
      rw [hG0]
      exact s1
    · show Option.map _ (y'.bunS j) = none
      rw [s3 j hj]
      rfl
    · exact p4SpanAfter_none _ _ _ (s4 j hj) _ _ (s4 j hj)

end

end MinCostFlow.SparseCore.Program
