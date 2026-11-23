module

public import MinCostFlow.SparseCore.Program.AssemblyFsOpenWords
public import MinCostFlow.SparseCore.Program.AssemblyFsOpenCaps

import MinCostFlow.SparseCore.Program.AssemblyFirstStepDSPre
import MinCostFlow.SparseCore.Program.AssemblyFirstStepSplitEnds
import Mathlib.Tactic

/-!
# Proof of the premise `hOpen` of `asmFirstStep_hP4` (`AssemblyFsOpen`)

Proves `AsmFsP4Open` (`AssemblyFirstStepHP4Defs.lean`) at the state after Phase 3:
1. `asmFirstStep_hOpen_of_wordBounds`: proves `AsmFsP4Open` under any `space` given the two
   spanner word-size bounds `(36 * (spV + 2 * spE + 1)) ^ impl.cw < 2 ^ w` and
   `10 * (spV + spE + 2) ^ 2 * (depth + 7) < 2 ^ w`:
   * `AsmFirstBunStepOut`: descriptor layout (`p4TasksOf_at`), distinct slots (`touched.Nodup`),
     descriptor range (`asmFirstStep_touched_len`), and per-slot `DSUpdatePre` via
     `dsUpdatePre_of_sideModel` (`AssemblyFirstStepDSPre.lean`) using
     `batchWithinCaps_bundleCompStep`, `batchEnc_le_of_delOrSplit`, and `batchAt_words_lt`.
   * Per-task `P4TaskCaps` via `p4TaskCaps_of_valid`.
   * Post-task new-slot edge bounds `< A.x.eCap` via induction over `p4SpanAfter`.
2. `asmFirstStep_hOpen`: discharges the two word-size bounds via
   `asmFirstStep_wordBounds_of_spaceStd` (`AssemblyFsOpenWords.lean`), giving the **exact**
   statement of `hOpen` in `asmFirstStep_hP4` (`AssemblyFirstStepHP4.lean`) at
   `space := asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

private lemma length_le_m_add_splitCount_open :
    ∀ {G : MGraph} {U : List Update}, G.BatchIsValid U → (∀ u ∈ U, isDelOrSplit u) →
      U.length ≤ G.m + batchSplitCount U
  | _, [], _, _ => by simp [batchSplitCount]
  | G, u :: rest, ⟨hu, hrest⟩, hds => by
    have hu1 := hds u List.mem_cons_self
    have hrest1 : ∀ x ∈ rest, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem u hx)
    have ih := length_le_m_add_splitCount_open hrest hrest1
    cases u with
    | insert _ _ _ => cases hu1
    | delete e =>
      have hm : (G.applyUpdate (.delete e)).m + 1 = G.m := by
        simp only [MGraph.m, MGraph.applyUpdate]
        exact Finset.card_erase_add_one hu
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit] at ih ⊢
      omega
    | split v v' St Sh =>
      have hm : (G.applyUpdate (.split v v' St Sh)).m = G.m := rfl
      simp only [List.length_cons, batchSplitCount, List.countP_cons, isSplit, ↓reduceIte] at ih ⊢
      omega

private lemma dsHist_G_eq_applyBatch {P : DSParams} {d : DSHist}
    (hL : 1 ≤ P.L) (hVG₀ : d.G₀.IsValid) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hbv : d.G₀.BatchIsValid d.flat) (hds : ∀ u ∈ d.flat, isDelOrSplit u) :
    (d.state P).G = d.G₀.applyBatch d.flat := by
  have hq1 : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hI := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
    hbv hds d.flat.length le_rfl).1.G_eq
  simpa [DSHist.state, List.take_length] using hI

private lemma p4SpanStep_preserves_valid (P : DSParams) {cap eCap : ℕ}
    (S6 S : BucketSpannerState cap) (mem : ℕ → ℕ) (t : SpanUpdTask)
    (hS : ∀ (j : Fin cap) (d : DSHist), S j = some d →
      d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
      d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u))
    (ht : ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d → mem t.batchPtr ≠ 0 →
      let U := (decodeBatch mem t.batchPtr (d.state P).G).1
      d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
      d.G₀.BatchIsValid (d.flat ++ U) ∧ (∀ u ∈ d.flat ++ U, isDelOrSplit u)) :
    ∀ (j : Fin cap) (d : DSHist), p4SpanStep P S6 mem S t j = some d →
      d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
      d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u) := by
  intro j d hjd
  unfold p4SpanStep p4OnTask at hjd
  by_cases hs : t.slot < cap
  · simp only [hs, ↓reduceDIte] at hjd
    cases hS6 : S6 ⟨t.slot, hs⟩ with
    | none => simp only [hS6] at hjd; exact hS j d hjd
    | some d0 =>
      simp only [hS6] at hjd
      by_cases hb : mem t.batchPtr = 0
      · simp only [hb, ↓reduceIte] at hjd; exact hS j d hjd
      · simp only [hb, ↓reduceIte] at hjd
        by_cases hj : j = ⟨t.slot, hs⟩
        · subst hj
          simp only [BucketSpannerState.set, Function.update_self, Option.some.injEq] at hjd
          subst hjd
          obtain ⟨hV, hm, hE, hBV, hds⟩ := ht hs d0 hS6 hb
          refine ⟨hV, hm, hE, ?_, ?_⟩
          · simpa [p4NewHist, DSHist.flat] using hBV
          · simpa [p4NewHist, DSHist.flat] using hds
        · simp only [BucketSpannerState.set, Function.update_of_ne hj] at hjd
          exact hS j d hjd
  · simp only [hs, ↓reduceDIte] at hjd; exact hS j d hjd

private lemma p4SpanStep_preserves_some (P : DSParams) {cap : ℕ}
    (S6 S : BucketSpannerState cap) (mem : ℕ → ℕ) (t : SpanUpdTask)
    (j : Fin cap) (hS : ∃ d, S j = some d) :
    ∃ d', p4SpanStep P S6 mem S t j = some d' := by
  unfold p4SpanStep p4OnTask
  by_cases hs : t.slot < cap
  · simp only [hs, ↓reduceDIte]
    cases hS6 : S6 ⟨t.slot, hs⟩ with
    | none => exact hS
    | some d0 =>
      by_cases hb : mem t.batchPtr = 0
      · simp only [hb, ↓reduceIte]; exact hS
      · simp only [hb, ↓reduceIte]
        by_cases hj : j = ⟨t.slot, hs⟩
        · subst hj
          exact ⟨p4NewHist P mem d0 t, by simp [BucketSpannerState.set]⟩
        · simp only [BucketSpannerState.set, Function.update_of_ne hj]; exact hS
  · simp only [hs, ↓reduceDIte]; exact hS

private lemma p4SpanAfter_fold_valid (P : DSParams) {cap eCap : ℕ}
    (S6 : BucketSpannerState cap) (mem : ℕ → ℕ) :
    ∀ (ts : List SpanUpdTask) (S : BucketSpannerState cap),
      (∀ (j : Fin cap) (d : DSHist), S j = some d →
        d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
        d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u)) →
      (∀ t ∈ ts, ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d →
        mem t.batchPtr ≠ 0 →
        let U := (decodeBatch mem t.batchPtr (d.state P).G).1
        d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
        d.G₀.BatchIsValid (d.flat ++ U) ∧ (∀ u ∈ d.flat ++ U, isDelOrSplit u)) →
      (∀ (j : Fin cap) (d : DSHist), ts.foldl (p4SpanStep P S6 mem) S j = some d →
        d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ (∀ e ∈ d.G₀.E, e < eCap) ∧
        d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u)) ∧
      (∀ j : Fin cap, (∃ d, S j = some d) → ∃ d', ts.foldl (p4SpanStep P S6 mem) S j = some d')
  | [], S, hS, _ => ⟨hS, fun _ h => h⟩
  | t :: rest, S, hS, hts => by
    have ht := hts t List.mem_cons_self
    have hrest : ∀ x ∈ rest, _ := fun x hx => hts x (List.mem_cons_of_mem t hx)
    have hS' := p4SpanStep_preserves_valid P S6 S mem t hS ht
    obtain ⟨hV, hSome⟩ := p4SpanAfter_fold_valid P S6 mem rest (p4SpanStep P S6 mem S t) hS' hrest
    exact ⟨hV, fun j hj => hSome j (p4SpanStep_preserves_some P S6 S mem t j hj)⟩

private lemma task_word_bounds_arith {spV spE sb depth m0 n0 mB enc lenU totW W : ℕ}
    (hm0 : m0 ≤ spE) (hsb : sb ≤ spV) (hn0 : n0 + sb ≤ spV)
    (hmB : mB ≤ spE) (hlenU : lenU ≤ spV + spE)
    (henc : enc ≤ lenU * (2 * mB + 1)) (htot : totW ≤ 5 * enc + 1)
    (hSq : 10 * (spV + spE + 2) ^ 2 * (depth + 7) < W) :
    spV < W ∧ spE < W ∧
    3 + m0 + (m0 + sb) * (depth + 6 + m0) < W ∧
    2 * (n0 + sb) + 2 < W ∧
    totW < W := by
  have hS : spV + spE + 2 ≤ (spV + spE + 2) ^ 2 := by nlinarith
  have hspV : spV < W := by nlinarith
  have hspE : spE < W := by nlinarith
  have hWgen : 3 + m0 + (m0 + sb) * (depth + 6 + m0) < W := by
    have ha : m0 + sb ≤ spV + spE + 2 := by omega
    have hb : depth + 6 + m0 ≤ (spV + spE + 2) * (depth + 7) := by nlinarith
    have hc : (m0 + sb) * (depth + 6 + m0) ≤ (spV + spE + 2) ^ 2 * (depth + 7) := by
      calc (m0 + sb) * (depth + 6 + m0)
          ≤ (spV + spE + 2) * ((spV + spE + 2) * (depth + 7)) := Nat.mul_le_mul ha hb
        _ = (spV + spE + 2) ^ 2 * (depth + 7) := by ring
    nlinarith
  have hWq : 2 * (n0 + sb) + 2 < W := by nlinarith
  have htotW : totW < W := by
    have he1 : enc ≤ (spV + spE) * (2 * spE + 1) :=
      henc.trans (Nat.mul_le_mul hlenU (by omega))
    have he2 : 5 * ((spV + spE) * (2 * spE + 1)) + 1 ≤ 10 * (spV + spE + 2) ^ 2 := by nlinarith
    have he3 : 10 * (spV + spE + 2) ^ 2 ≤ 10 * (spV + spE + 2) ^ 2 * (depth + 7) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact ⟨hspV, hspE, hWgen, hWq, htotW⟩

public section

set_option maxHeartbeats 800000 in
/-- **`AsmFsP4Open` under any `space` given the two spanner word-size bounds.**
Proves all three conjuncts of `AsmFsP4Open` (`AsmFirstBunStepOut`, per-task `P4TaskCaps`,
and post-task new-slot edge bounds `< A.x.eCap`) from `AsmFsPre`, `AsmFsQ₃At`, and the two
word-size inequalities `(36 * (spV + 2 * spE + 1)) ^ impl.cw < 2 ^ w` and
`10 * (spV + spE + 2) ^ 2 * (depth + 7) < 2 ^ w`. -/
theorem asmFirstStep_hOpen_of_wordBounds {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (space : ℕ → ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ hEnd₂ : ℕ)
    (y' : AsmBrSide scProgB5 depth)
    (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ)
    (hEnd₃ : ℕ) (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (splitPtr outDescPtr : ℕ) (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End))
    (touched : List ℕ)
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
      tx_pot' splitPtr outDescPtr mk' Mset Ys touched)
    (hWcw : (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w)
    (hWgenSq : 10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) < 2 ^ w) :
    AsmFsP4Open (asmBrSP impl w depth y') y'.spanS A.x.eCap (outDescPtr + 1) hEnd₃
      A.x.xRest.slots.length
      (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
        (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
      (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) st₃.mem := by
  obtain ⟨hScanF, tx₀, hTx, hP2, hP3⟩ := hQ₃
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hWcw hWgenSq ⊢
  obtain ⟨hM0, hN0, hd1, -, hw16, -, -, -, hUB', hR, hFacts, hBat, hU, -, -, hOB, -, -, -, -, -,
    -, -, -, -, hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xTour = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -, -, -,
    hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨-, -, -, hModOld, -, hk, ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, -, -, hSB0, -, -, -, -, -, -,
    hspE_le0, hkB, -, hInact, -, hInactDyn, hPart, hDynGOld, -, hmMax0, hspV_ge0, hspE_ge0⟩ := hMod
  dsimp only at hSB0 hspE_le0 hkB hmMax0 hspV_ge0 hspE_ge0 hInact hInactDyn hPart hDynGOld
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hset, -, -, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, hv5, he5, hcap5, hsplitB5, hspV5, hspE5, hmMax5, -, -, -, -, hkB',
    -, -, hslots', -, hSlotN, hMatch, hspanS, hSlotInv, hRepB, hRepS, -⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h3d, hnd3, hlt3, -, hdesc3, -, hnone3, -⟩ := hP3
  set sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
  set ord' := applyOrdEdits ord ed
  set info := stepBundleTree sp tr U ord ord'
  set SP := asmBrSP impl w depth y'
  set tasks := p4TasksOf st₃.mem (outDescPtr + 1) touched.length
  set newSet : Finset (Finset ℕ) :=
    ((scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps.map
      fun q => xRest.comps.getD q.1 ∅).toFinset
  set tr_mid : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ newSet }
  have hActMid : activePairs tr_mid = activePairs info.state := by
    ext ⟨C, b⟩
    simp only [mem_activePairs, tr_mid, info, stepBundleTree, hset, Finset.mem_union,
      Finset.mem_sdiff]
  have hReadySlot : ∀ j B₀, y'.bunS j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U := by
    have hNewC : ∀ C ∈ newSet, C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := by
      intro C hC
      rw [hset] at hC
      exact ⟨touchedCompsBatch_subset _ _ (Finset.mem_sdiff.mp hC).1, (Finset.mem_sdiff.mp hC).2⟩
    have hSlotN' : SlotMapOK tr_mid y'.slotCap y'.cap y'.slots y'.slotOf := by
      rw [hslc, hcap5]; exact hSlotN
    exact asmFirstStep_phase3_ready hI hk hU hOB hPart hInact hNewC hSlotN' hMatch hSlotInv.2.2.1
  have hDynGEq : ∀ q ∈ activePairs info.state, GraphEq (tr.dyn q).G (tr.bun q).graph :=
    p4_dynGraphEq sp hInact hInactDyn hDynGOld
  have hS6RepValid : ∀ (j : Fin y'.cap) (d : DSHist), y'.spanS j = some d →
      d.G₀.IsValid ∧ d.G₀.m ≤ SP.mMax ∧ (∀ e ∈ d.G₀.E, e < xRest.eCap5) ∧
      d.G₀.BatchIsValid d.flat ∧ (∀ u ∈ d.flat, isDelOrSplit u) := by
    intro j d hjd
    have hslot := hRepS.1 j
    rw [hjd] at hslot
    cases hx : y'.xSpan.slots j with
    | none => rw [hx] at hslot; exact hslot.elim
    | some bm =>
      rw [hx] at hslot
      obtain ⟨-, ⟨-, hdsRep, -⟩, -⟩ := hslot
      obtain ⟨-, hVG₀, hGm₀, hG₀E, hBV, hds, -⟩ := hdsRep
      exact ⟨hVG₀, hGm₀, fun e he => lt_of_lt_of_le (hG₀E e he) (by show y'.spE ≤ xRest.eCap5; omega),
        hBV, hds⟩
  have hmapSlot : tasks.map SpanUpdTask.slot = touched := by
    apply List.ext_getElem (by simp [tasks, p4TasksOf])
    intro i h1 h2
    obtain ⟨-, -, -, hm, -⟩ := hdesc3 i h2
    simpa [tasks, p4TasksOf] using hm
  -- Core per-task facts: every task corresponds to an active pair with valid decoded batch,
  -- `DSUpdatePre`, and `P4TaskCaps`.
  have hTaskCore : ∀ t ∈ tasks, ∃ (hs : t.slot < y'.cap) (d : DSHist),
      y'.spanS ⟨t.slot, hs⟩ = some d ∧
      DSUpdatePre SP d [0, t.batchPtr, t.W, hEnd₃] st₃.mem ∧
      (∀ (hs' : t.slot < y'.cap) (d' : DSHist), y'.spanS ⟨t.slot, hs'⟩ = some d' →
        let U_t := (decodeBatch st₃.mem t.batchPtr (d'.state SP).G).1
        d'.G₀.IsValid ∧ d'.G₀.m ≤ SP.mMax ∧ (∀ e ∈ d'.G₀.E, e < xRest.eCap5) ∧
        d'.G₀.BatchIsValid (d'.flat ++ U_t) ∧ (∀ u ∈ d'.flat ++ U_t, isDelOrSplit u) ∧
        P4TaskCaps SP xRest.eCap5 d' U_t) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := mem_p4TasksOf ht
    obtain ⟨hsB, bp, totW, hts, htb, htw, -, hbp_le, hSmall⟩ := hdesc3 i hi
    have hs_lt_sc : touched[i] < y'.slotCap := hlt3 _ (List.getElem_mem hi)
    cases hS₀ : y'.bunS ⟨touched[i], hs_lt_sc⟩ with
    | none => exact absurd (List.getElem_mem hi) (hnone3 ⟨touched[i], hs_lt_sc⟩ hS₀)
    | some B₀ =>
      have hs_in_slots : touched[i] ∈ y'.slots := by
        by_contra hns
        have hnone := hSlotInv.2.2.1 ⟨touched[i], hs_lt_sc⟩ hns
        rw [hS₀] at hnone; cases hnone
      obtain ⟨q, hq_mid, hqs⟩ := hSlotN.2.2.1 touched[i] hs_in_slots
      have hq : q ∈ activePairs info.state := hActMid ▸ hq_mid
      obtain ⟨hsS, d, hSd, hdst, hdG₀, hdds, hdbv, hdUs⟩ := hspanS q hq_mid
      have hhs : st₃.mem (outDescPtr + 1 + 3 * i) < y'.cap := by omega
      have hSd_t : y'.spanS ⟨st₃.mem (outDescPtr + 1 + 3 * i), hhs⟩ = some d := by
        convert hSd using 2; exact Fin.ext (hts.trans hqs.symm)
      obtain ⟨hsB2, B, hSB, hAg⟩ := hMatch q hq_mid
      have hBB : B = B₀ := by
        have hfin : (⟨y'.slotOf q, hsB2⟩ : Fin y'.slotCap) = ⟨touched[i], hs_lt_sc⟩ := Fin.ext hqs
        rw [hfin, hS₀] at hSB
        exact (Option.some.inj hSB).symm
      rw [hBB] at hAg
      have hReadyB : BundleStepReady tr.cs B₀ tr.k ord ord' U := hReadySlot _ B₀ hS₀
      have hBeq : (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = info.U_B q :=
        (bunAgree_bundleCompStep_eq hAg hReadyB).1
      have hGeq_B : GraphEq B₀.graph (d.state SP).G := by
        rw [hdst]
        exact graphEq_trans (bunAgree_graphEq hAg) (graphEq_symm (hDynGEq q hq))
      have hSmallB : SmallBatchAt st₃.mem bp B₀.graph (info.U_B q) totW := by
        rw [← hBeq]; exact hSmall B₀ (by convert hS₀ using 2)
      have hBatD : BatchAt st₃.mem bp (d.state SP).G (info.U_B q) totW :=
        batchAt_of_graphEq hGeq_B hSmallB.1
      have hEndsD : BatchSplitEndsExact (d.state SP).G (info.U_B q) := by
        rw [← hBeq]
        exact batchSplitEndsExact_congr hGeq_B (bundleCompStep_splitEndsExact _ _ _ _ _ _)
      have hDecEq : (decodeBatch st₃.mem bp (d.state SP).G).1 = info.U_B q :=
        decodeBatch_eq_of_batchAt hBatD hEndsD
      have hSpecB := bundleCompStep_spec hReadyB
      have hU_valid_B : B₀.graph.BatchIsValid (info.U_B q) := hBeq ▸ hSpecB.2.1
      have hU_ds : ∀ u ∈ info.U_B q, isDelOrSplit u := hBeq ▸ hSpecB.2.2.2.1
      have hU_valid : (d.state SP).G.BatchIsValid (info.U_B q) :=
        batchIsValid_of_graphEq hGeq_B hU_valid_B
      obtain ⟨hVG₀, hGm₀, hG₀E_x, hdbv', hdds'⟩ := hS6RepValid _ d hSd_t
      have hG₀E_SP : ∀ e ∈ d.G₀.E, e < SP.eCap :=
        fun e he => lt_of_lt_of_le (hG₀E_x e he) (by show xRest.eCap5 ≤ y'.spE; omega)
      have hC0 : q.1 ∈ components tr.cs.G₀ :=
        hFacts.2.2.1.1 (mem_activePairs.mp hq).1 |> fun h => by
          simpa [info, stepBundleTree, compLSFBatch_G₀] using h
      have hC' : q.1 ∈ components info.state.cs.G₀ := hFacts.2.2.1.1 (mem_activePairs.mp hq).1
      have hG₀_n2m : d.G₀.n ≤ 2 * d.G₀.m := by rw [hdG₀]; exact (hUB'.2 q.1 hC' q.2).2.2.1
      have hG₀_m_le_eCap : d.G₀.m ≤ xRest.eCap5 := by
        calc d.G₀.E.card ≤ (Finset.range xRest.eCap5).card :=
              Finset.card_le_card fun e he => Finset.mem_range.mpr (hG₀E_x e he)
          _ = xRest.eCap5 := Finset.card_range _
      have hG₀_n_le : d.G₀.n + SP.splitBound ≤ SP.vCap := by
        show d.G₀.n + y'.splitB ≤ y'.spV
        omega
      have hGeq_d : (d.state SP).G = d.G₀.applyBatch d.flat :=
        dsHist_G_eq_applyBatch hd1 hVG₀ hGm₀ hdbv hdds
      have hbv_all : d.G₀.BatchIsValid (d.flat ++ info.U_B q) :=
        batchIsValid_append.mpr ⟨hdbv, hGeq_d ▸ hU_valid⟩
      have hds_all : ∀ u ∈ d.flat ++ info.U_B q, isDelOrSplit u := fun u hu => by
        rcases List.mem_append.mp hu with h1 | h2
        · exact hdds u h1
        · exact hU_ds u h2
      have hst' : (⟨d.G₀, d.Us ++ [info.U_B q]⟩ : DSHist).state SP = info.state.dyn q := by
        rw [dsHist_append_state_eq_update, hdst]; rfl
      have hsplit_all : batchSplitCount (d.flat ++ info.U_B q) ≤ SP.splitBound := by
        have hflat_eq : (⟨d.G₀, d.Us ++ [info.U_B q]⟩ : DSHist).flat = d.flat ++ info.U_B q :=
          dsHist_flat_append d (info.U_B q)
        show batchSplitCount (d.flat ++ info.U_B q) ≤ y'.splitB
        rw [hsplitB5, hSB0, ← hflat_eq]
        exact batchSplitCount_le_of_branchUpdatesBelow (P := SP) hUB' hC' hd1 hGm₀ hdG₀ hst'
          (hflat_eq ▸ hds_all) (hflat_eq ▸ hbv_all)
      -- Contiguous vertex range of `B₀` from `BundleTableRepAt` gives `BatchWithinCaps SP.vCap SP.eCap`
      have hRangeB : ∃ nB, B₀.vertices = Finset.range nB := by
        have hslotB := hRepB.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨touched[i], hs_lt_sc⟩
        rw [hS₀] at hslotB
        cases hmB : y'.xBun.slotBlocks ⟨touched[i], hs_lt_sc⟩ with
        | none => rw [hmB] at hslotB; exact hslotB.elim
        | some pc =>
          rw [hmB] at hslotB
          obtain ⟨nB, hVrange, -⟩ := hslotB.2.1
          exact ⟨nB, hVrange⟩
      obtain ⟨nB, hVrange⟩ := hRangeB
      have hnB_eq : nB = d.G₀.n + batchSplitCount d.flat := by
        have hVeq : B₀.vertices = (d.state SP).G.V := hGeq_B.1
        have hc : nB = (d.state SP).G.n := by
          unfold MGraph.n; rw [← hVeq, hVrange, Finset.card_range]
        rw [hc, hGeq_d, n_applyBatch_of_delOrSplit d.flat d.G₀ hdbv hdds]
      have hsc_add : batchSplitCount (d.flat ++ info.U_B q) =
          batchSplitCount d.flat + batchSplitCount (info.U_B q) := by
        simp [batchSplitCount, List.countP_append]
      have hU_caps : BatchWithinCaps SP.vCap SP.eCap (info.U_B q) := by
        rw [← hBeq]
        exact batchWithinCaps_bundleCompStep hReadyB hVrange (by rw [hBeq]; omega)
      -- Word bounds from `hWcw` and `hWgenSq`
      have hEnc := batchEnc_le_of_delOrSplit B₀.graph (info.U_B q) hU_ds
      have hlenU := length_le_m_add_splitCount_open hU_valid_B hU_ds
      have hmB_eq : B₀.graph.m = (d.state SP).G.m := by
        unfold MGraph.m; rw [hGeq_B.2.1]
      have hmB_le : B₀.graph.m ≤ d.G₀.m := by
        rw [hmB_eq, hGeq_d]
        exact Finset.card_le_card (applyBatch_E_subset_of_delOrSplit d.G₀ d.flat hdds)
      have hscU : batchSplitCount (info.U_B q) ≤ SP.splitBound := by omega
      have hsb_le : SP.splitBound ≤ xRest.spV := by show y'.splitB ≤ xRest.spV; omega
      have hcw' : (36 * (SP.vCap + 2 * SP.eCap + 1)) ^ SP.impl.cw < 2 ^ w := by
        simpa [SP, asmBrSP, hspV5, hspE5] using hWcw
      obtain ⟨hspV_lt', hspE_lt', hWgen, hWq, htotW_lt⟩ := task_word_bounds_arith
        (spV := xRest.spV) (spE := xRest.spE) (sb := SP.splitBound) (depth := depth)
        (m0 := d.G₀.m) (n0 := d.G₀.n) (mB := B₀.graph.m) (enc := B₀.graph.batchEnc (info.U_B q))
        (lenU := (info.U_B q).length) (totW := totW) (W := 2 ^ w)
        (by omega) hsb_le (by show d.G₀.n + y'.splitB ≤ xRest.spV; omega)
        (by omega) (by omega) hEnc hSmallB.2 hWgenSq
      have hspV_lt : SP.vCap < 2 ^ w := by show y'.spV < 2 ^ w; omega
      have hspE_lt : SP.eCap < 2 ^ w := by show y'.spE < 2 ^ w; omega
      have hwords_t : ∀ j < totW, st₃.mem (bp + j) < 2 ^ w := by
        have hV_after : ∀ v ∈ ((d.state SP).G.applyBatch (info.U_B q)).V, v < SP.vCap := by
          intro v hv
          have heq_after : GraphEq (B₀.graph.applyBatch (info.U_B q))
              ((d.state SP).G.applyBatch (info.U_B q)) := graphEq_applyBatch hGeq_B (info.U_B q)
          rw [← heq_after.1, ← hBeq, bundleCompStep_eq hReadyB] at hv
          obtain ⟨⟨-, -, hwg, -, -, -, -⟩, -⟩ := bundleRunsStep_spec hReadyB
          rw [← hwg] at hv
          change v ∈ (bundleRunsStep tr.cs B₀ tr.k ord' U).2.vertices at hv
          rw [bundleRunsStep_vertices_range hReadyB hVrange, Finset.mem_range] at hv
          rw [← bundleCompStep_eq hReadyB, hBeq] at hv
          omega
        have hE_before : ∀ e ∈ (d.state SP).G.E, e < SP.eCap := by
          intro e he
          rw [hGeq_d] at he
          exact hG₀E_SP e (applyBatch_E_subset_of_delOrSplit d.G₀ d.flat hdds he)
        have hIns_before : ∀ e a b, Update.insert e a b ∈ info.U_B q → e < SP.eCap :=
          fun e a b hm => False.elim (hU_ds _ hm)
        exact batchAt_words_lt hBatD hU_valid hV_after hE_before hIns_before
          (by omega) hspV_lt hspE_lt htotW_lt
      have hPre : DSUpdatePre SP d [0, bp, totW, hEnd₃] st₃.mem :=
        dsUpdatePre_of_sideModel (P := SP) (tr := tr) (U_glob := U) (ord := ord) (ord' := ord')
          (q := q) (d := d) (batchPtr := bp) (W := totW) (h := hEnd₃) (n := n)
          hd1 hw16 hC0 hUB' (by show y'.splitB = tr.splitBound; omega)
          (by show y'.mMax = tr.m₀; omega) hdG₀ hdst hdds hdbv hdUs hBatD hEndsD hbp_le hwords_t
          hU_valid hU_ds hU_caps hG₀E_SP hG₀_n_le hWgen hWq hcw'
      have hCaps : P4TaskCaps SP xRest.eCap5 d (info.U_B q) :=
        p4TaskCaps_of_valid hd1 hVG₀ hGm₀ hG₀E_x hbv_all hds_all
      refine ⟨hhs, d, hSd_t, by simpa only [htb, htw] using hPre, ?_⟩
      intro hs' d' hSd'
      have hd_eq : d' = d := by
        have h1 : y'.spanS ⟨st₃.mem (outDescPtr + 1 + 3 * i), hs'⟩ = some d := hSd_t
        rw [hSd'] at h1
        exact Option.some.inj h1
      subst hd_eq
      dsimp only
      rw [htb, hDecEq]
      exact ⟨hVG₀, hGm₀, hG₀E_x, hbv_all, hds_all, hCaps⟩
  -- Assemble all 3 conjuncts of `AsmFsP4Open`
  refine ⟨?_, ?_, ?_⟩
  · -- 1. `AsmFirstBunStepOut`
    refine ⟨p4TasksOf_at st₃.mem (outDescPtr + 1) touched.length, by rw [hmapSlot]; exact hnd3, ?_, ?_⟩
    · rw [p4TasksOf_length]
      have htl := asmFirstStep_touched_len hnd3 hlt3
      omega
    · intro t ht
      obtain ⟨hs, d, hSd, hPre, -⟩ := hTaskCore t ht
      exact ⟨hs, d, hSd, hPre⟩
  · -- 2. Per-task `P4TaskCaps`
    intro t ht hs d hSd _
    obtain ⟨-, -, -, -, hF⟩ := hTaskCore t ht
    exact (hF hs d hSd).2.2.2.2.2
  · -- 3. New-slot post-task edges `< xRest.eCap5`
    have hAfter := p4SpanAfter_fold_valid SP (eCap := xRest.eCap5) y'.spanS st₃.mem tasks y'.spanS
      hS6RepValid (fun t ht hs d hSd _ => by
        obtain ⟨-, -, -, -, hF⟩ := hTaskCore t ht
        obtain ⟨h1, h2, h3, h4, h5, -⟩ := hF hs d hSd
        exact ⟨h1, h2, h3, h4, h5⟩)
    intro s _ hs_hi
    have hs_mem : s ∈ y'.slots := by rw [hslots']; exact List.mem_range.mpr hs_hi
    obtain ⟨q, hq_mid, hqs⟩ := hSlotN.2.2.1 s hs_mem
    obtain ⟨hsS, d₀, hSd₀, -⟩ := hspanS q hq_mid
    have hs_cap : s < y'.cap := hqs ▸ hsS
    have hSome₀ : ∃ d, y'.spanS ⟨s, hs_cap⟩ = some d := ⟨d₀, by convert hSd₀ using 2; exact Fin.ext hqs.symm⟩
    obtain ⟨d, hd⟩ := hAfter.2 ⟨s, hs_cap⟩ hSome₀
    obtain ⟨hVG₀, hGm₀, hG₀E, hBV, hds⟩ := hAfter.1 ⟨s, hs_cap⟩ d hd
    refine ⟨hs_cap, d, hd, fun e he => ?_⟩
    rw [dsHist_G_eq_applyBatch hd1 hVG₀ hGm₀ hBV hds] at he
    exact hG₀E e (applyBatch_E_subset_of_delOrSplit d.G₀ d.flat hds he)

/-- **Proof of the premise `hOpen` of `asmFirstStep_hP4`** (`AssemblyFirstStepHP4.lean`)
at the standard step-space function `space := asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`.
Combines `asmFirstStep_wordBounds_of_spaceStd` with `asmFirstStep_hOpen_of_wordBounds`. -/
theorem asmFirstStep_hOpen {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) :
    ∀ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
        Mset Ys touched,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
        tx_pot' splitPtr outDescPtr mk' Mset Ys touched →
      AsmFsP4Open (asmBrSP impl w depth y') y'.spanS A.x.eCap (outDescPtr + 1) hEnd₃
        A.x.xRest.slots.length
        (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
          (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
        (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) st₃.mem := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
    Mset Ys touched hA hQ₃
  obtain ⟨hWcw, hWgenSq⟩ := asmFirstStep_wordBounds_of_spaceStd A hA
  exact asmFirstStep_hOpen_of_wordBounds hRoot (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp)
    A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys
    touched hA hQ₃ hWcw hWgenSq

end

end MinCostFlow.SparseCore.Program
