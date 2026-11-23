module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11

import Mathlib.Tactic

/-!
# Phase 4 in the top proof of the first step (`AssemblyFirstStepHP4`)

The top proof (`asmFirstStep_coreStepAt_of`) asks, as `hP4`, that Phase 4 runs on the arguments
that the driver passes, from the state that Phase 3 leaves (`AsmFsQ₃`), and that a predicate
`Q₄` holds after it. This file proves `hP4` (`asmFirstStep_hP4`) with `Q₄ := AsmFsQ₄`
(`AssemblyFirstStepHP4Defs`). Phase 4 is the selection part (`asmFirstP4Sel_runs`) followed by
the lists, the rotation and the re-embedding (`asmFirstPhase4_runs_post`).

The premises of Phase 4 come from these places.
* The model. The facts of the bundles and the dynamic spanners after the step come from the side
  model (`asmFirstStep_bunEdges`, `asmFirstStep_dynG_new`, `asmFirstStep_hHApply`,
  `asmFirstStep_inactiveBkts`, `p4_hWalkNew`), and the tasks are those of the slots
  (`asmFirstStep_p4_slotTasks`).
* The memory. The spanners and the lazy lists are those of Phase 2, and Phase 3 keeps them, since
  they lie apart from the bundle table and the tour. The tour is that of Phase 3. The inputs, the
  embedding table and the flags of the old output graph are old data, which Phases 1 to 3 keep
  (`asmFirstStep_p4_inputs`, `asmFirstStep_p4_emb_out`).
* The places. Below `h` lie the old parts of the branch and the inputs. Phase 2 adds cells at the
  end of the scan or above, and Phase 3 adds cells at the end of Phase 2 or above. So the parts
  that Phase 4 reads lie apart from one another.

Three more facts are premises of `asmFirstStep_hP4`: the room of Phase 4 (`hSp4`, from the space
bound of the step), the facts of the tasks that the descriptors of Phase 3 do not give (`hOpen`),
and the bounds on the vertices that the rotation names (`hVerts`). The procedures of Phase 4 are
given by `K`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

set_option maxHeartbeats 8000000 in
/-- **`hP4` of the top proof.** On the tour family of `scProg` and its bundle table, with a word
exponent of at least `3 capExp` (`hwe`) and the procedures `K` of Phase 4 in `p`: from `AsmFsQ₃`,
Phase 4 runs on the arguments that the driver passes, and `AsmFsQ₄` holds after it. The premises
`hSp4` (the room), `hOpen` (the tasks) and `hVerts` (the vertices of the rotation) are stated on
the witnesses of `Q₃`. -/
theorem asmFirstStep_hP4 {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (K : AsmFirstP4Code TRc w impl p fVertRoot)
    (hwe : 3 * capExp ≤ wordExp) (space : ℕ → ℕ)
    (hSp4 : ∀ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
        Mset Ys touched,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
        tx_pot' splitPtr outDescPtr mk' Mset Ys touched →
      AsmFsP4Room w (asmBrSP impl w depth y') y'.spanS st₃.mem hEnd₃ A.x.vCap A.x.eCap
        (outDescPtr + 1) touched.length A.x.xRest.slots.length
        (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
          (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
        (canonSplitList A.tr.cs A.U).length A.U.length A.ed.length K.HE.querySpace
        hRoot.querySpace)
    (hOpen : ∀ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
        Mset Ys touched,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
        tx_pot' splitPtr outDescPtr mk' Mset Ys touched →
      AsmFsP4Open (asmBrSP impl w depth y') y'.spanS A.x.eCap (outDescPtr + 1) hEnd₃
        A.x.xRest.slots.length
        (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
          (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
        (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) st₃.mem)
    (hVerts : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      (∀ v ∈ batchVerts A.U, v < A.x.vCap) ∧ (∀ v ∈ ordEditVerts A.ed, v < A.x.vCap) ∧
      ∀ v ∈ asmFirstRotRawSet (fun _ => canonicalSparsify impl) A.tr A.U A.ord A.ed,
        v < A.x.vCap) :
    ∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₃ TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ →
      ∃ o₄ st₄ c₄, Runs w p A.ω K.stmt (startState [A.x.xRest.spanH,
          st₃.mem (o₂.value + 1) + 1, st₃.mem (st₃.mem (o₂.value + 1)), o₃.value, A.x.eCap,
          A.x.gOut + 4 + 7 * A.x.vCap, A.x.embH, A.x.xRest.slots.length,
          st₂.mem (A.x.restH + 3), A.batch, A.chg,
          A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words, st₁.mem (A.h + 6),
          A.x.tourH, A.spPtr, A.edits, A.h] st₃.mem st₃.pos) o₄ st₄ c₄ ∧
        AsmFsQ₄ TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
          bTourStep fDelTriples fBuildGroups K A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄ := by
  intro A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ hA hQ₃
  have hvt := hVerts A hA
  obtain ⟨hScanF, hEnd₂, rfl, tx₀, hTx, y', tx1, lazyE, hP2, hEnd₃, rfl, tx_pot', splitPtr,
    outDescPtr, mk', Mset, Ys, touched, hP3⟩ := hQ₃
  have hQ3At : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
      splitPtr outDescPtr mk' Mset Ys touched :=
    ⟨hScanF, tx₀, hTx, hP2, hP3⟩
  have hsp4 := hSp4 A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched hA hQ3At
  have hop := hOpen A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched hA hQ3At
  unfold AsmFsP4Room at hsp4
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hsp4 hop hvt hTx ⊢
  obtain ⟨hM0, hN0, hd1, -, hw16, hW, -, hUB, hUB', hR, hFacts, hBat, hU, hCaps, hEd, hOB, -, -,
    hChg, hcEx, hSpE, hBin, hEin, hCin, hSin, hfoot, hwords, -, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  have hcells := asmFirstStep_cells_of_rep hR
  obtain ⟨hRA, hv, he, -, -, -, hsl, -⟩ := hR
  dsimp only at hv he hsl hOld hcells
  subst hv he
  obtain ⟨hM, h6, h7, hc₁⟩ := hScanF
  obtain rfl : xTour = tx₀ := (eq_of_heq hTx).symm
  have hP2c := hP2
  have hP3c := hP3
  -- the branch before the step
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hEmbRep, -, -, -, hTourRep, hMk, hSide, -,
    hcap, -, hDisj⟩ := hRA
  dsimp only at hcap hEmbRep
  rw [hM0, hN0] at hcap
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hDG, -⟩ := hcells
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨hSMO, -, -, hModOld, -, hk, ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, -, -, -, -, hBD, -, -, -, -, -,
    hkB, hSlotInvOld, hInact, -, hInactDyn, hPart, hDynGOld, -, -, -, heCapSpE⟩ := hMod
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hfootE : ∀ a, embFoot xRest.eCap5 embH yEmb a → a < h :=
    fun a ha => hfoot a ⟨2, by decide, ha⟩
  have hfootO : ∀ a, (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut a → a < h :=
    fun a ha => hfoot a ⟨3, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hdisjES : ∀ a, embFoot xRest.eCap5 embH yEmb a → ¬ asmSdFoot restH xRest a :=
    fun a he hs => hDisj 2 (by decide) 5 (by decide) (by decide) a he hs
  have hdisjET : ∀ a, embFoot xRest.eCap5 embH yEmb a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a he ht => hDisj 2 (by decide) 4 (by decide) (by decide) a he ht
  have hdisjOS : ∀ a, (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut a →
      ¬ asmSdFoot restH xRest a :=
    fun a ho hs => hDisj 3 (by decide) 5 (by decide) (by decide) a ho hs
  have hdisjOT : ∀ a, (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a ho ht => hDisj 3 (by decide) 4 (by decide) (by decide) a ho ht
  have hdisjOE : ∀ a, (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut a →
      ¬ embFoot xRest.eCap5 embH yEmb a :=
    fun a ho he => hDisj 3 (by decide) 2 (by decide) (by decide) a ho he
  -- the scan and the post of Phase 2
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, hok, -, hset, -, hdel, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, hspanH, -, -, hslc, hv5, he5, hcap5, -, -, hspE5, -, -, -, -, -, hkB', -, -,
    hslots', hkeepSlot, hSlotN, hMatch, hspanS, hSlotInv, -, hRepS, -, -, hnslCell, -, hnslCap,
    -, -, -, -, hdisjSide, hdisj', hlazy, hlen2, -, -, hfootS', hfootT', hfr, -⟩ := hP2
  -- the post of Phase 3
  obtain ⟨-, -, -, -, hRepT3, -, -, -, -, -, -, h3b, h3c, h3d, hnd3, hlt3, hlen3, hdesc3, hunt3,
    hnone3, h3e, -, hZ3, hfootT3, hfr3, -⟩ := hP3
  -- the places: Phase 2 adds cells in `[e₂, hEnd₂)`, Phase 3 in `[hEnd₂ + 2, hEnd₃)`
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 *
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
      U).newComps.length := ⟨_, rfl⟩
  rw [← he₂] at hlen2 hfootS' hfootT'
  have hhE2 : h ≤ hEnd₂ := by omega
  have hhw : h < 2 ^ w := hwords h (by simp)
  have hBunConv : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH y'.xBun a :=
    fun a ha => by rw [hv5, he5, hkB', hkB]; exact ha
  have hBunSd : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → asmSdFoot restH y' a := fun a ha => ⟨1, by decide, hBunConv a ha⟩
  have hBkSd : ∀ a, bucketFoot y'.spanH y'.xSpan a → asmSdFoot restH y' a :=
    fun a ha => ⟨2, by decide, ha⟩
  have hBunBk : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → ¬ bucketFoot y'.spanH y'.xSpan a :=
    fun a hb hk => hdisjSide 1 (by decide) 2 (by decide) (by decide) a (hBunConv a hb) hk
  have hBk : ∀ a, bucketFoot y'.spanH y'.xSpan a →
      (asmSdFoot restH xRest a ∧ a < h) ∨ (e₂ ≤ a ∧ a < hEnd₂) := by
    intro a ha
    rcases hfootS' a (hBkSd a ha) with hs | hr
    · exact Or.inl ⟨hs, hfootSide a hs⟩
    · exact Or.inr hr
  have hBkLt : ∀ a, bucketFoot y'.spanH y'.xSpan a → a < hEnd₂ := fun a ha => by
    rcases hBk a ha with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  have hTf3c : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a →
      (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a ∨
      (e₂ ≤ a ∧ a < hEnd₂ ∧ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx1 a) ∨
      (hEnd₂ + 2 ≤ a ∧ a < hEnd₃) := by
    intro a ha
    rcases hfootT3 a ha with h1 | h1
    · rcases hfootT' a h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl ⟨h2.1, h2.2, h1⟩)
    · exact Or.inr (Or.inr h1)
  -- the old cells below `h` after Phase 3
  have hK2keep := asmFirstStep_phase2_keep (fun q hq => (hok q hq).1) hnslCap hfr
  have hK := asmFirstStep_keep12 hM hK2keep (by omega)
  have hK3 := asmFirstStep_keep123 hK hfr3
    (fun a hb => by
      rcases hfootS' a (hBunSd a hb) with hs | ⟨h1, _⟩
      · exact Or.inl hs
      · exact Or.inr (by omega))
    (fun a ht => by
      rcases hfootT' a ht with ht0 | ⟨h1, _⟩
      · exact Or.inl ht0
      · exact Or.inr (by omega))
    hhE2
  have hout : ∀ a0 n0, InputAt w mem
      ((asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).foot b
        ⟨xRest.vCap5, xRest.eCap5, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour,
          xTour, restH, xRest⟩) a0 n0 h →
      ∀ a, a0 ≤ a → a < a0 + n0 → a < h ∧ ¬ asmSdFoot restH xRest a ∧
        ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a ∧ ¬ embFoot xRest.eCap5 embH yEmb a := by
    intro a0 n0 hin a h1 h2
    have hx := (hin.2 (a - a0) (by omega)).2
    rw [Nat.add_sub_cancel' h1] at hx
    exact ⟨by have := hin.1; omega, fun hs => hx ⟨5, by decide, hs⟩,
      fun ht => hx ⟨4, by decide, ht⟩, fun he => hx ⟨2, by decide, he⟩⟩
  obtain ⟨hBat3, hEd3, hChg3, hSp3⟩ := asmFirstStep_p4_inputs (hK := hK3) (hB := hBat)
    (hBin := hBin) (hE := hEd) (hEin := hEin) (hC := hChg) (hCin := hCin) (hS := hSpE)
    (hSin := hSin) (fun a ha => ⟨5, by decide, ha⟩) (fun a ha => ⟨4, by decide, ha⟩)
  obtain ⟨hEmb3, hOS⟩ := asmFirstStep_p4_emb_out hK3 hEmbRep
    (fun a ha => ⟨hfootE a ha, hdisjES a ha, hdisjET a ha⟩) hDG
    (fun a h1 h2 => ⟨hfootO a (Or.inr ⟨h1, h2⟩), hdisjOS a (Or.inr ⟨h1, h2⟩),
      hdisjOT a (Or.inr ⟨h1, h2⟩)⟩)
  -- the spanners of Phase 2 after Phase 3
  have hS6 : (bucketSpannerRep (asmBrSP impl w depth y') y'.cap).rep y'.spanH y'.spanS y'.xSpan
      st₃.mem :=
    ((bucketSpannerRep_local (asmBrSP impl w depth y') y'.cap) y'.spanH y'.spanS y'.xSpan st₂.mem
      st₃.mem (fun a ha => (hfr3 a (hBkLt a ha) (fun hb => hBunBk a hb ha)
        (fun ht => hdisj' a (hBkSd a ha) ht)).symm)).1 hRepS
  -- the cells that Phase 4 may read
  have hInLow : ∀ a, a < h → ¬ asmSdFoot restH xRest a → ¬ embFoot xRest.eCap5 embH yEmb a →
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a := by
    intro a ha hs he
    refine ⟨by omega, fun hb => ?_, he⟩
    rcases hBk a hb with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hs h1
    · omega
  have hInHigh : ∀ a, h ≤ a → a < hEnd₃ → ¬ bucketFoot y'.spanH y'.xSpan a →
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a :=
    fun a h1 h2 hb => ⟨h2, hb, fun he => by have := hfootE a he; omega⟩
  have hoIn : ∀ e < xRest.eCap5,
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ (gOut + 4 + 7 * xRest.vCap5 + e) :=
    fun e he' => by
      have ho : (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut
          (gOut + 4 + 7 * xRest.vCap5 + e) := Or.inr ⟨by omega, by unfold dynGraphSize; omega⟩
      exact hInLow _ (hfootO _ ho) (hdisjOS _ ho) (hdisjOE _ ho)
  have hoLe : gOut + 4 + 7 * xRest.vCap5 + xRest.eCap5 ≤ hEnd₃ := by
    have ho : (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut
        (gOut + 3 + 7 * xRest.vCap5 + 9 * xRest.eCap5) :=
      Or.inr ⟨by omega, by unfold dynGraphSize; omega⟩
    have := hfootO _ ho
    omega
  have htl : touched.length ≤ y'.slotCap := asmFirstStep_touched_len hnd3 hlt3
  have hdescIn : ∀ a, outDescPtr + 1 ≤ a →
      a < outDescPtr + 1 + 3 * (p4TasksOf st₃.mem (outDescPtr + 1) touched.length).length →
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a := by
    intro a h1 h2
    rw [p4TasksOf_length] at h2
    exact hInHigh a (by omega) (by omega) (fun hb => by have := hBkLt a hb; omega)
  have hcells3 := asmFirstStep_p4_taskCells (mem := st₃.mem) (outDescPtr := outDescPtr)
    (slotCap := y'.slotCap) (hEnd := hEnd₃) (touched := touched) (fun i hi => by
      obtain ⟨_, bp, tw, -, h1, h2, h3, h4, -⟩ := hdesc3 i hi
      exact ⟨bp, tw, h1, h2, h3, h4⟩)
  have hbatchIn : ∀ t ∈ p4TasksOf st₃.mem (outDescPtr + 1) touched.length, ∀ a,
      t.batchPtr ≤ a → a < t.batchPtr + t.W →
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a := by
    intro t ht a h1 h2
    obtain ⟨h3, h4⟩ := hcells3 t ht
    exact hInHigh a (by omega) (by omega) (fun hb => by have := hBkLt a hb; omega)
  -- the words of the caps, and the slots
  obtain ⟨-, -, h4e, hvw, hslW⟩ := asmFirstStep_cap_words hW hcap hwe hsl
  have hslN : xRest.slots.length + newCompsBucketSum tr xRest.comps (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps ≤ xRest.slotCap :=
      by
    have := asmFirstStep_touched_len hSlotN.1 (fun s hs => (hSlotN.2.2.2.2 s hs).1)
    rw [hslots', List.length_range] at this
    exact this
  have heCap : xRest.eCap5 ≤ (asmBrSP impl w depth y').eCap := by
    show xRest.eCap5 ≤ y'.spE
    rw [hspE5]
    exact heCapSpE
  have hBF : ∀ a, bucketFoot y'.spanH y'.xSpan a → a < hEnd₃ :=
    fun a ha => by have := hBkLt a ha; omega
  have hEF : ∀ a, embFoot xRest.eCap5 embH yEmb a → a < hEnd₃ :=
    fun a ha => by have := hfootE a ha; omega
  have hEB : ∀ a, embFoot xRest.eCap5 embH yEmb a → ¬ bucketFoot y'.spanH y'.xSpan a := by
    intro a he hb
    rcases hBk a hb with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hdisjES a he h1
    · have := hfootE a he
      omega
  -- the model
  obtain ⟨hready, hRlt, hEold, hEnew, hDcap⟩ :=
    asmFirstStep_phase3_model (fun _ => canonicalSparsify impl) hOld hFacts hU hOB hCaps hdel
  obtain ⟨-, -, -, -, -, -, -, -, hGE, -⟩ := hOld
  obtain ⟨-, -, hModN, hBDN, -⟩ := hFacts
  have hlazy' : ∀ k (hk : k < (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps
      tr.activeComps) U).newComps.length), (lazyE ⟨k, hk⟩).toFinset =
      compCoreEdges tr (xRest.comps.getD ((scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH
          xRest.comps tr.activeComps) U).newComps.getD k (0, 0)).1 ∅) :=
    fun k hk => (hlazy k hk).2.2.2.1
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
  -- the lazy lists of Phase 2 after Phase 3
  have hkeepMid : ∀ a, h ≤ a → a < e₂ → st₃.mem a = st₂.mem a := by
    intro a h1 h2
    refine hfr3 a (by omega) (fun hb => ?_) (fun ht => ?_)
    · rcases hfootS' a (hBunSd a hb) with hs | ⟨h3, _⟩
      · have := hfootSide a hs
        omega
      · omega
    · rcases hfootT' a ht with ht0 | ⟨h3, _⟩
      · have := hfootT a ht0
        omega
      · omega
  have hLazy : ∀ i : Fin (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps
      tr.activeComps) U).newComps.length, ∃ ptr, st₃.mem (h + 6 + asmFirstScanBatchSpace
      xRest.vCap5 xRest.eCap5 words + 2 * i.1) = ptr ∧
      st₃.mem (h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 * i.1 + 1) =
          (lazyE i).length ∧ ListAt st₃.mem ptr (lazyE i) ∧
      ptr + (lazyE i).length ≤ hEnd₃ ∧ (∀ e ∈ lazyE i, e < xRest.eCap5) ∧
      (∀ a, ptr ≤ a → a < ptr + (lazyE i).length →
        P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a) := by
    rintro ⟨i, hi2⟩
    obtain ⟨hL, hLlen, -, hLset, hLlo, hLhi, hLc⟩ := hlazy i hi2
    dsimp only
    refine ⟨st₂.mem (h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 * i),
        hkeepMid _ (by omega) (by omega), ?_, fun j hj => ?_,
      by omega, fun e he => ?_, fun a h1 h2 => ?_⟩
    · rw [hkeepMid _ (by omega) (by omega)]
      exact hLlen
    · obtain ⟨hb, -, ht⟩ := hLc (st₂.mem (h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5
        words + 2 * i) + j) (by omega) (by omega)
      rw [hfr3 _ (by omega) (fun hb' => hb (hBunConv _ hb')) ht]
      exact hL j hj
    · have hc : e ∈ compCoreEdges tr (xRest.comps.getD ((scanBatchFold tr.cs.G (asmFirstScanStart
        mem xRest.cmpH xRest.comps tr.activeComps) U).newComps.getD i (0, 0)).1 ∅) := by
        rw [← hLset]
        exact List.mem_toFinset.mpr he
      exact hEold e (Finset.mem_filter.mp hc).1
    · obtain ⟨-, hb, -⟩ := hLc a h1 h2
      exact hInHigh a (by omega) (by omega) hb
  have hLazyIn : ∀ a, h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words ≤ a → a < h + 6
      + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 * (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps.length →
      P4InCell y'.spanH y'.xSpan xRest.eCap5 embH yEmb hEnd₃ a :=
    fun a h1 h2 => hInHigh a (by omega) (by omega)
      (fun hb => by rcases hBk a hb with ⟨_, h3⟩ | ⟨h3, _⟩ <;> omega)
  -- the selection part of Phase 4
  obtain ⟨o₁, st₄a, c₄a, hr₁, hpost₁⟩ := asmFirstP4Sel_runs (P := asmBrSP impl w depth y')
    (cap := y'.cap) (lo := xRest.slots.length)
    (hi := xRest.slots.length + newCompsBucketSum tr xRest.comps (scanBatchFold tr.cs.G
        (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps) 
    (lazyPtr := h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words)
    (pos := st₃.pos) (ω := ω) (ord' := applyOrdEdits ord ed) (slotOf := y'.slotOf)
    K.hfFront K.hfSel K.hfEval K.hfSpan K.hfSeed K.hfFlags K.hfSeedB K.hfSeedL K.hfAppend
    K.hfLoop K.hfNewLoop K.hpSpan K.hfTask K.hfAfter K.hfUH K.hfD K.hfR K.hfDl K.hfC K.hfEdge
    K.hfPush K.hfMark K.hfNew K.hfN K.hcopy K.hread
    hw16 hop.1 hS6 hEmb3 hOS hoIn hoLe hdescIn hbatchIn hop.2.1 (by omega)
    (by show _ < 2 ^ w; omega) hop.2.2
    heCap hBF hEF hEB hBat3.1 (asmFirstStep_capsMatch hCaps hdel hDcap)
    (fun a h1 h2 => by
      obtain ⟨q1, q2, -, q4⟩ := hout _ _ hBin a h1 h2
      exact hInLow a q1 q2 q4)
    (by have := hBin.1; omega) hLazy hLazyIn (by omega) hChg3
    (asmFirstStep_fDel_cap hI hcEx hGE)
    (fun a h1 h2 => by
      obtain ⟨q1, q2, -, q4⟩ := hout _ _ hCin a h1 h2
      exact hInLow a q1 q2 q4)
    (by have := hCin.1; omega) hZ3
    (by show _ < 2 ^ w; unfold asmFirstPhase4Room at hsp4; omega) rfl hI hU hModOld hBD hModN
    hBDN
    (asmFirstStep_dynG_new (fun _ => canonicalSparsify impl) hI hU hOB hk hInact hInactDyn hPart
      hDynGOld)
    (asmFirstStep_inactiveBkts hI hρ hInact)
    (asmFirstStep_bunEdges (fun _ => canonicalSparsify impl) hI hk hU hOB hPart hInact)
    (asmFirstStep_hHApply hd1 hUB hModOld hI hk hU hOB hPart hInact hInactDyn hDynGOld)
    (asmFirstStep_dynG_old hDynGOld)
    (fun q hq _ => p4_hWalkNew hd1 hUB' hModN q hq) hT hcEx
    (asmFirstStep_lazy_cover (fun _ => canonicalSparsify impl) hInact hset hlazy')
  -- the rest of Phase 4
  have htourW : tourH < 2 ^ w := by
    have := hfootT tourH (asmTourRepWithPot_foot_self tourAsmRep_handle_foot _ _ _ tourH xTour)
    omega
  obtain ⟨o₄, st₄, c₄, hr₄, hpost₄⟩ := asmFirstPhase4_runs_post
    (avoid₀ := (outGraphRep xRest.vCap5 xRest.eCap5).foot outH gOut) (rec := h) K.HE hRoot hTR_loc
    K.hfSelP K.hfLists K.hfEnds K.hfDel K.hfIns K.hfCopyIns K.hfRot K.hfDirect K.hfBatch
    K.hfEdits K.hfBuild K.hfReemb K.hfCopyStr K.hpSort hr₁ hpost₁ hw16 htourW hvw
    (by show _ < 2 ^ w; omega) hRepT3
    (fun a ha => by
      rcases hTf3c a ha with h1 | ⟨_, h1, _⟩ | ⟨_, h1⟩
      · have := hfootT a h1
        omega
      · omega
      · omega)
    (fun a ha hb => by
      rcases hTf3c a ha with h1 | ⟨_, _, h1⟩ | ⟨h1, _⟩
      · rcases hBk a hb with ⟨h2, _⟩ | ⟨h2, _⟩
        · exact hdisjST a h2 h1
        · have := hfootT a h1
          omega
      · exact hdisj' a (hBkSd a hb) h1
      · have := hBkLt a hb
        omega)
    (fun a ha he => by
      have := hfootE a he
      rcases hTf3c a ha with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hdisjET a he h1
      · omega
      · omega)
    hEF hBF hSp3 hBat3.1 hEd3
    (fun a ha => by
      have hone : ∀ a0 n0, InputAt w mem
          ((asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).foot b
            ⟨xRest.vCap5, xRest.eCap5, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH,
              sTour, xTour, restH, xRest⟩) a0 n0 h → a0 ≤ a → a < a0 + n0 →
          a < hEnd₃ ∧ ¬ bucketFoot y'.spanH y'.xSpan a ∧ ¬ embFoot xRest.eCap5 embH yEmb a ∧
            ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a := by
        intro a0 n0 hin h1 h2
        obtain ⟨q1, q2, q3, q4⟩ := hout _ _ hin a h1 h2
        refine ⟨(hInLow a q1 q2 q4).1, (hInLow a q1 q2 q4).2.1, q4, fun ht => ?_⟩
        rcases hTf3c a ht with h3 | ⟨h3, _⟩ | ⟨h3, _⟩
        · exact q3 h3
        · omega
        · omega
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hone _ _ hSin h1 h2
      · exact hone _ _ hBin h1 h2
      · exact hone _ _ hEin h1 h2)
    (by omega)
    (fun i hi => ⟨fun hb => by rcases hBk _ hb with ⟨_, h1⟩ | ⟨h1, _⟩ <;> omega,
      fun he => by have := hfootE _ he; omega,
      fun ht => by
        rcases hTf3c _ ht with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · have := hfootT _ h1
          omega
        · omega
        · omega⟩)
    (fun a ha => by have := hfootO a ha; omega) hI hU hOB hModN
    (asmFirstStep_lazy_iff (fun _ => canonicalSparsify impl) hI hρ hInact hset hlazy')
    hvt.1 hvt.2.1 hvt.2.2 hsp4
  refine ⟨o₄, st₄, c₄, ?_, hEnd₂, rfl, y', tx1, lazyE, hEnd₃, rfl, tx_pot', splitPtr, outDescPtr,
    mk', Mset, Ys, touched, hQ3At, hpost₄⟩
  have hr := hr₄
  rw [p4TasksOf_length] at hr
  show Runs w p ω (asmFirstPhase4Stmt K.fSelP K.fLists K.fRot K.fReemb)
    (startState [xRest.spanH, st₃.mem (hEnd₂ + 1) + 1, st₃.mem (st₃.mem (hEnd₂ + 1)), hEnd₃,
      xRest.eCap5, gOut + 4 + 7 * xRest.vCap5, embH, xRest.slots.length, st₂.mem (restH + 3),
      batch, chg, h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words, st₁.mem (h + 6),
          tourH, spPtr, edits, h] st₃.mem st₃.pos) o₄ st₄ c₄
  rw [h3b, hlen3, ← hspanH, h6, show st₂.mem (restH + 3) = _ from hnslCell]
  exact hr

end

end MinCostFlow.SparseCore.Program
