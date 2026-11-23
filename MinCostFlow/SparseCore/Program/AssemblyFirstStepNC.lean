module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCDefs

import MinCostFlow.SparseCore.Program.AssemblyFirstStepPostOut
import Mathlib.Tactic

/-!
# The post of the first step without the cost (`AssemblyFirstStepNC`)

This file proves the post of the first step without the cost (`AsmFsNCGoal`, the premise `hNC`
of `asmFirstStep_hPost_of`) from three smaller goals: the bundle side after the step
(`AsmFsSideGoal`), the embedding model (`AsmFsEmbGoal`) and the space (`AsmFsSpaceGoal`), and
for a multiplier of the split lists of at least `4 capExp + 5`. The witnesses are the embedding
table `yE` of Phase 4, the abstract tour with the new core lists and the marks `mk'` of Phase 3,
the split lists `Ys` of Phase 3 and the list `T₀` of Phase 4.

**The places.** The old parts of the branch and the inputs lie below `h`. Phase 1 writes its
scan from `h + 6`, Phase 2 adds cells in `[e₂, hEnd₂)` (`e₂` is the end of the list of the lazy
lists), Phase 3 in `[hEnd₂ + 2, hEnd₃)` and Phase 4 in `[hEnd₃, ov)`. Each new part lies in the
same old part or in these ranges, which gives the feet and, with the disjointness of the parts
after each phase, the disjointness of the new branch (`asmBrDisjoint_afterCore`).

**The cells below `h`.** Phases 1 to 3 keep the cells below `h` outside the old side and the old
tour (`asmFirstStep_keep123`), and Phase 4 keeps those outside its spanners, the old embedding
table and the tour, and outside the record `[h, h + 6)`. The driver writes only `h + 1`. So the
cells below `h` outside the side, the tour and the embedding table keep their values.

**The records.** The records of the output step come from Phase 4 (`asmFsPost_rec`), the split
lists from Phase 3, moved to the final memory by `outSplitListsAt_transfer`: Phase 4 keeps the
cells of Phase 3 that its own cells and the final tour avoid.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

set_option maxHeartbeats 8000000 in
/-- **The post of the first step without the cost** (`AsmFsNCGoal`), from the bundle side after
the step (`hSide`), the embedding model (`hEmb`), the space (`hSp`) and a multiplier
`ysMul ≥ 4 capExp + 5` of the split lists and `T₀`. -/
theorem asmFirstStep_hNC_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {ysMul : ℕ} {space : ℕ → ℕ} (hys : 4 * capExp + 5 ≤ ysMul)
    (hSide : AsmFsSideGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space)
    (hEmb : AsmFsEmbGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space)
    (hSp : AsmFsSpaceGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space) :
    AsmFsNCGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K ysMul space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ xTour hxT
  have hside := hSide A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  have hemb := hEmb A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  have hsp := hSp A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  dsimp only at hemb
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hsp hside hemb hTx hxT ⊢
  obtain ⟨hM0, hN0, -, -, hw16, -, -, -, -, hR, hFacts, hBat, hU, -, hEd, -, -, -, -, -, -, -,
    -, -, -, hfoot, hwords, -, hspace, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he hOld
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain rfl : tx' = xTour := (eq_of_heq hxT).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hEmbRep, -, -, -, hTourRep, -, hSide, -,
    hcap, -, hDisj⟩ := hRA
  dsimp only at hcap hEmbRep
  rw [hM0, hN0] at hcap
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
  obtain ⟨-, -, -, -, -, -, -, -, hok, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, hv5, he5, -, -, -, -, -, -, -, -, -, hkB', -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hnslCap, -, -, -, -, hdisjSide, hdisj', -, hlen2, -, -, hfootS',
    hfootT', hfr, -⟩ := hP2
  -- the post of Phase 3
  obtain ⟨-, -, -, -, -, hkM, hMS, hMk3, hSpl3, hYs3, hsp3, -, -, -, -, -, -, -, -, -, h3e, -, -,
    hfootT3, hfr3, -⟩ := hP3
  -- the post of Phase 4
  have hP4c := hP4
  obtain ⟨-, -, -, -, hRepX', hE4, hTr4, -, -, -, -, -, -, -, hT0nd, hT0lt, hT0cov, hT0raw, -, -,
    -, -, -, -, -, -, -, h4a, -, -, hfr4, hfootX', hfootE', hfootT4, hdEX, hdET, hdXT, -⟩ := hP4c
  -- the places
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 *
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
      U).newComps.length := ⟨_, rfl⟩
  rw [← he₂] at hlen2 hfootS' hfootT'
  have he₂h : h + 6 ≤ e₂ := by omega
  have hhw : h < 2 ^ w := hwords h (by simp)
  have hkB : xRest.kB = tr.k := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkB, -⟩ := hMod
    exact hkB
  have hBunConv : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH y'.xBun a :=
    fun a ha => by rw [hv5, he5, hkB', hkB]; exact ha
  have hBunSd : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → asmSdFoot restH y' a := fun a ha => ⟨1, by decide, hBunConv a ha⟩
  have hBkSd : ∀ a, bucketFoot y'.spanH y'.xSpan a → asmSdFoot restH y' a :=
    fun a ha => ⟨2, by decide, ha⟩
  have hSdLoc : ∀ a, asmSdFoot restH y' a →
      (asmSdFoot restH xRest a ∧ a < h) ∨ (e₂ ≤ a ∧ a < hEnd₂) := by
    intro a ha
    rcases hfootS' a ha with hs | hr
    · exact Or.inl ⟨hs, hfootSide a hs⟩
    · exact Or.inr hr
  have hT3 : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a →
      (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a ∨ (e₂ ≤ a ∧ a < hEnd₃) := by
    intro a ha
    rcases hfootT3 a ha with h1 | h1
    · rcases hfootT' a h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2.1, by omega⟩
    · exact Or.inr ⟨by omega, h1.2⟩
  have hT4 : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH tx' a →
      (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a ∨ (e₂ ≤ a ∧ a < o₄.value) := by
    intro a ha
    rcases hfootT4 a ha with h1 | h1
    · rcases hT3 a h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2.1, by omega⟩
    · exact Or.inr ⟨by omega, h1.2⟩
  -- the cells below `h`
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
    (by omega)
  have hK4 : ∀ a < h, ¬ asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → ¬ embFoot xRest.eCap5 embH yEmb a →
      st₄.mem a = mem a := by
    intro a ha hs ht hem
    have hb : ¬ bucketFoot y'.spanH y'.xSpan a := fun hb => by
      rcases hSdLoc a (hBkSd a hb) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hs h1
      · omega
    have ht3 : ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a := fun h3 => by
      rcases hT3 a h3 with h1 | ⟨h1, _⟩
      · exact ht h1
      · omega
    rw [hfr4 a (by omega) hb hem ht3 (Or.inl ha)]
    exact hK3 a ha hs ht
  have hmem' : ∀ a, a ≠ h + 1 →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = st₄.mem a :=
    fun a ha => Function.update_of_ne ha _ _
  have hKall : ∀ a < h, ¬ asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → ¬ embFoot xRest.eCap5 embH yEmb a →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = mem a := fun a ha hs ht hem => by
    rw [hmem' a (by omega)]
    exact hK4 a ha hs ht hem
  -- the records of Phase 4 in the final memory
  have hrec := asmFsPost_rec hP4 (by omega) (st₃.mem hEnd₂)
  dsimp only at hrec
  obtain ⟨rD, rDF, rI, rIF, rT0n, rT0L, rT0F, rRe, rRe4, rReF, rOv, rZ, rW⟩ := hrec
  have hval : st₃.mem hEnd₂ ≤ hEnd₃ := by
    rw [hsp3]
    exact outSplitListsAt_le_top hSpl3
  have hov : o₄.value < 2 ^ w := lt_of_le_of_lt hsp hspace
  have hST : ASM_ST_DEL = 0 ∧ ASM_ST_SPLIT = 1 ∧ ASM_ST_INS = 2 ∧ ASM_ST_ROT = 3 ∧
      ASM_ST_REEMB = 4 ∧ ASM_ST_REEMBLEN = 5 ∧ ASM_ST_SIZE = 6 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := hST
  refine ⟨yE, ⟨outCoreOrder (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord
    (applyOrdEdits ord ed)).state (applyOrdEdits ord ed), mk'⟩, Ys, T₀, ?_⟩
  unfold AsmFsPostNCAt
  dsimp only
  rw [s0, s1, s2, s3, s4, s5, s6, Nat.add_zero]
  refine ⟨?c1, hemb.1, hemb.2, ?c4, ⟨Mset, hkM, hMS, outMarksOf_cord hMk3⟩, hside, hslc, hv5, he5,
    ?c10, ?c11, ?c12, rT0n, rT0L, rT0F, hT0nd, hT0lt, hT0cov, rRe, rRe4, rReF, rW hov (lt_of_le_of_lt (le_trans hval h4a) hov),
    ?c23, rOv, hsp, rZ, ?c27, ?c28⟩
  case c1 =>
    have hE4' : (embRep xRest.eCap5).rep embH yE.view yE st₄.mem := ⟨rfl, hE4.1 ▸ hE4.2⟩
    refine (embRep_local xRest.eCap5 embH yE.view yE st₄.mem _ fun a ha => ?_).1 hE4'
    refine (hmem' a ?_).symm
    rcases hfootE' a ha with h1 | ⟨h1, _⟩
    · have := hfootE a h1
      omega
    · omega
  case c4 =>
    refine asmFsPost_tourView hFacts.2.1 ?_
    refine ((hTR_loc _ _) tourH _ tx' st₄.mem _ fun a ha => ?_).1 hTr4
    refine (hmem' a ?_).symm
    rcases hT4 a ha with h1 | ⟨h1, _⟩
    · have := hfootT a h1
      omega
    · omega
  case c10 =>
    refine asmBrDisjoint_afterCore (h := h) hDisj (fun i hi a ha => hfoot a ⟨i, hi, ha⟩) ?_ ?_ ?_
      hdET ?_ ?_
    · intro a ha
      rcases hfootE' a ha with h1 | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr (by omega)
    · intro a ha
      rcases hT4 a ha with h1 | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr (by omega)
    · intro a ha
      rcases asmSdFoot_sideAfter ha with ⟨i, hi, -, hia⟩ | hb
      · rcases hSdLoc a ⟨i, hi, hia⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1
        · exact Or.inr (by omega)
      · rcases hfootX' a hb with h1 | ⟨h1, _⟩
        · rcases hSdLoc a (hBkSd a h1) with ⟨h2, _⟩ | ⟨h2, _⟩
          · exact Or.inl h2
          · exact Or.inr (by omega)
        · exact Or.inr (by omega)
    · intro a he hs
      rcases asmSdFoot_sideAfter hs with ⟨i, hi, -, hia⟩ | hb
      · rcases hSdLoc a ⟨i, hi, hia⟩ with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
        · rcases hfootE' a he with h2 | ⟨h2, _⟩
          · exact hdisjES a h2 h1
          · omega
        · rcases hfootE' a he with h2 | ⟨h2, _⟩
          · have := hfootE a h2
            omega
          · omega
      · exact hdEX a he hb
    · intro a ht hs
      rcases asmSdFoot_sideAfter hs with ⟨i, hi, -, hia⟩ | hb
      · have hsd : asmSdFoot restH y' a := ⟨i, hi, hia⟩
        have hlt : a < hEnd₂ := by
          rcases hSdLoc a hsd with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
        rcases hfootT4 a ht with h1 | ⟨h1, _⟩
        · rcases hfootT3 a h1 with h2 | ⟨h2, _⟩
          · exact hdisj' a hsd h2
          · omega
        · omega
      · exact hdXT a hb ht
  case c11 =>
    intro a ha
    rcases ha with h0 | h0 | h0
    · exact hKall a (hfoot a ⟨0, by decide, h0⟩)
        (fun hs => hDisj 0 (by decide) 5 (by decide) (by decide) a h0 hs)
        (fun ht => hDisj 0 (by decide) 4 (by decide) (by decide) a h0 ht)
        (fun he => hDisj 0 (by decide) 2 (by decide) (by decide) a h0 he)
    · exact hKall a (hfoot a ⟨1, by decide, h0⟩)
        (fun hs => hDisj 1 (by decide) 5 (by decide) (by decide) a h0 hs)
        (fun ht => hDisj 1 (by decide) 4 (by decide) (by decide) a h0 ht)
        (fun he => hDisj 1 (by decide) 2 (by decide) (by decide) a h0 he)
    · exact hKall a (hfoot a ⟨3, by decide, h0⟩)
        (fun hs => hDisj 3 (by decide) 5 (by decide) (by decide) a h0 hs)
        (fun ht => hDisj 3 (by decide) 4 (by decide) (by decide) a h0 ht)
        (fun he => hDisj 3 (by decide) 2 (by decide) (by decide) a h0 he)
  case c12 =>
    unfold OutStepInAt
    dsimp only
    rw [Finset.length_sort, Finset.length_sort]
    refine ⟨rD, rDF, ?_, rI, rIF⟩
    have hsp' : Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) (h + 1) = splitPtr := by
      rw [Function.update_self]
      exact hsp3
    rw [hsp']
    refine outSplitListsAt_transfer (top := hEnd₃) ?_ ?_ h4a _ _ _ _ hSpl3
    · intro a ha hn
      obtain ⟨hn1, hn2⟩ := not_or.mp hn
      rw [hmem' a (by omega)]
      refine hfr4 a ha (fun hb => ?_) (fun he => ?_) hn2 (Or.inr (by omega))
      · rcases hSdLoc a (hBkSd a hb) with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
      · have := hfootE a he
        omega
    · intro a ha hav
      rcases hav with ho | ht
      · have := hfoot a ⟨3, by decide, ho⟩
        exact Or.inl (by omega)
      · rcases hfootT4 a ht with h1 | ⟨h1, _⟩
        · exact Or.inr h1
        · omega
  case c23 =>
    have hEcard : tr.S_cur.E.card ≤ xRest.eCap5 := by
      have h10 := hOld.2.2.2.2.2.2.2.2.2
      calc tr.S_cur.E.card ≤ (Finset.range xRest.eCap5).card :=
            Finset.card_le_card fun e he => Finset.mem_range.mpr (h10 e he)
        _ = xRest.eCap5 := Finset.card_range _
    have hed := ordEditsAt_two_len hEd
    exact asmFsNC_ys_rot_le (fun _ => canonicalSparsify impl) tr U ord ed _ _ _ hEcard hcap hYs3
      hT0raw (by omega) (by omega) hys
  case c27 =>
    intro a ha hn
    exact hKall a ha (fun hs => hn ⟨5, by decide, hs⟩) (fun ht => hn ⟨4, by decide, ht⟩)
      (fun he => hn ⟨2, by decide, he⟩)
  case c28 =>
    refine asmBrFoot_afterCore ?_ ?_ ?_
    · intro a ha
      rcases hfootE' a ha with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, h1.2⟩
    · intro a ha
      rcases hT4 a ha with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, h1.2⟩
    · intro a ha
      rcases asmSdFoot_sideAfter ha with ⟨i, hi, -, hia⟩ | hb
      · rcases hfootS' a ⟨i, hi, hia⟩ with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, by omega⟩
      · rcases hfootX' a hb with h1 | h1
        · rcases hfootS' a (hBkSd a h1) with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, h1.2⟩

end

end MinCostFlow.SparseCore.Program
