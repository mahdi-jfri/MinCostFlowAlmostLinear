module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActPrep

import WordRAM.Tactic

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 3b. Nonempty-branch verification (`asmFirstInitOneCompElseStmt`) -/

public section

/-- Cost bound of the nonempty (`len > 0`) branch `asmFirstInitOneCompElseStmt`. -/
@[expose] def newActElseCost (TS : BundleTourSpec) (eCap len m_C r : ℕ) (cord : ℕ → List End) (r_c : ℕ) : ℕ :=
  newActPrepCost len m_C r + bundleInitSlotsCost TS eCap r m_C cord [r_c] + bunPhiMul * (2 * m_C) + 50

set_option maxHeartbeats 600000 in
/-- Verification of the `len > 0` branch `asmFirstInitOneCompElseStmt`: runs
`asmFirstInitOneComp_prep_runs` followed by `bunTableHeadroom_initSlots_runs` on `rList = [r_c]`. -/
theorem asmFirstInitOneComp_else_runs {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w depth slotCap vCap eCap bBun fVertRoot fTourList fTourLen fTourOwner : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun fTourList fTourLen fTourOwner))
    (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (hTB : AsmBrTourBridge TS TR w p fTourList fTourLen fTourOwner)
    {restH tourH c v lazySlotPtr h h1 h2 : ℕ}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState depth} {ord : ℕ → List End} {mk : Finset End}
    {tx tx2 : (TR vCap eCap).τ}
    {bunH slotsPtr bktH ctH nSlots : ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {comps : List (Finset ℕ)} {mem₀ : ℕ → ℕ} {st5 : State}
    (_hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (_hρ : ρ.order = ord)
    (hk1 : 1 ≤ tr.k)
    (hc : c < comps.length) (hC : comps[c] ∈ components tr.cs.G₀)
    (hBktsEq : tr.activeBuckets comps[c] =
      ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]).image tr.origBucket)
    (hCoreInG₀ : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c] → e ∈ tr.cs.G₀.E)
    (hLazyBun : ∀ b ∈ tr.activeBuckets comps[c],
      BunAgree (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket comps[c] b) tr.k)
        (tr.bun (comps[c], b)))
    (heCapG : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hw16 : 16 ≤ 2 ^ w) (hvCapW : vCap < 2 ^ w) (heCapW : 4 * eCap < 2 ^ w)
    (hrc_R : tr.cs.RF.root v ∈ (tr.cs.compSt comps[c]).R)
    (hrc_lt : tr.cs.RF.root v < vCap)
    (hCordIff : ∀ x, x ∈ outCoreOrder tr ord (tr.cs.RF.root v) ↔
      x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c])
    (hCordOnly : ∀ v' x, x ∈ outCoreOrder tr ord v' →
      x.1 ∈ ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]) → v' = tr.cs.RF.root v)
    (hOK_cord : TourCordOK ord tr.cs.RF (outCoreOrder tr ord))
    (hCoreCord : CoreCordOf tr.cs ord (outCoreOrder tr ord))
    (hcord_nd : ∀ u, (outCoreOrder tr ord u).Nodup)
    (hrestH_lt : restH + ASM_SD_SIZE ≤ h)
    (hRec : mem₀ (restH + ASM_SD_BUN) = bunH ∧ mem₀ (restH + ASM_SD_SLOTS) = slotsPtr ∧
      mem₀ (restH + ASM_SD_NSLOTS) = nSlots ∧ mem₀ (restH + ASM_SD_BKT) = bktH ∧
      mem₀ (restH + ASM_SD_CT) = ctH)
    (hbkt_ok : ∀ e ∈ tr.cs.G₀.E, e < eCap ∧ mem₀ (bktH + e) = bucketCode (tr.origBucket e) ∧
      mem₀ (bktH + e) < 2 ^ w)
    (hbkt_lt : eCap = 0 ∨ bktH + eCap ≤ h) (hct_lt : ctH + 3 * comps.length ≤ h)
    (hsl_lt : slotsPtr + nSlots + (tr.activeBuckets comps[c]).card ≤ h) (hlazy_lt : lazySlotPtr + 2 ≤ h)
    (hCapRoom : nSlots + (tr.activeBuckets comps[c]).card ≤ slotCap)
    (hFreeSlots : ∀ s, nSlots ≤ s → ∀ hs : s < slotCap, S₀ ⟨s, hs⟩ = none)
    (hOldEdgeDisj : ∀ j : Fin slotCap, ∀ B, S₀ j = some B →
      ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c] →
        e ∉ B.edges)
    (hrepB : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S₀ m₀ mem₀)
    (hinvB : bunRestartInv vCap eCap S₀ (outCoreOrder tr ord))
    (hrepT2 : (TR vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx2 st5.mem)
    (hfootB : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a → a < h)
    (hfootT : ∀ a, (TR vCap eCap).foot tourH tx a → a < h)
    (hdisjBT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a →
      ¬ (TR vCap eCap).foot tourH tx a)
    (hMutDisj :
      (∀ a, restH ≤ a → a < restH + ASM_SD_SIZE →
        ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∧
        ¬ (TR vCap eCap).foot tourH tx a) ∧
      (∀ a, bktH ≤ a → a < bktH + eCap → ¬ (TR vCap eCap).foot tourH tx a) ∧
      (∀ a, ctH + 3 * c + 1 ≤ a → a < ctH + 3 * c + 3 →
        ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∧
        ¬ (TR vCap eCap).foot tourH tx a ∧
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧
        ¬ (bktH ≤ a ∧ a < bktH + eCap)) ∧
      (∀ a, slotsPtr + nSlots ≤ a → a < slotsPtr + nSlots + (tr.activeBuckets comps[c]).card →
        ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∧
        ¬ (TR vCap eCap).foot tourH tx a ∧
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧
        ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3)) ∧
      (∀ a, lazySlotPtr ≤ a → a < lazySlotPtr + 2 →
        ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∧
        ¬ (TR vCap eCap).foot tourH tx a ∧
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧
        ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) ∧
        ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + (tr.activeBuckets comps[c]).card)))
    (htourW : tourH < 2 ^ w)
    (htblFit : bunH + bundleTableFixedSize slotCap eCap ≤ h)
    (hh_le : h ≤ h1) (hh1_le : h1 + (outCoreOrder tr ord (tr.cs.RF.root v)).length + 1 ≤ h2)
    (hh2_hi : h2 ≤ h + hRoot.querySpace + TS.listSpace (outCoreOrder tr ord (tr.cs.RF.root v)).length)
    (hEndL : EndListAt st5.mem h1 (outCoreOrder tr ord (tr.cs.RF.root v)))
    (hzL : ZeroFrom st5.mem h2)
    (hfr2_lt : ∀ a < h, ¬ (TR vCap eCap).foot tourH tx a → st5.mem a = mem₀ a)
    (hft2 : ∀ a, (TR vCap eCap).foot tourH tx2 a →
      (TR vCap eCap).foot tourH tx a ∨ (h ≤ a ∧ a < h2))
    (hrec5 : ∀ i < ASM_SD_SIZE, st5.mem (restH + i) = mem₀ (restH + i))
    (hregs5 : st5.regs 0 = restH ∧ st5.regs 1 = tourH ∧ st5.regs 2 = c ∧
      st5.regs 4 = lazySlotPtr ∧ st5.regs 6 = h1 ∧ st5.regs 7 = tr.cs.RF.root v ∧
      st5.regs 8 = h2 ∧ st5.regs 9 = (outCoreOrder tr ord (tr.cs.RF.root v)).length ∧
      st5.regs 10 = ctH)
    (hSpace : let cord := outCoreOrder tr ord
      let r_c := tr.cs.RF.root v
      let coreE := (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]
      let r := (tr.activeBuckets comps[c]).card
      h + newActOneSpace TS hRoot.querySpace (cord r_c).length coreE.card r < 2 ^ w) :
    let cord := outCoreOrder tr ord
    let r_c := tr.cs.RF.root v
    let coreE := (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]
    let r := (tr.activeBuckets comps[c]).card
    ∃ hEnd st' cost S' m' tx', ∃ (uniqE uniqB : List ℕ), ∃ cslPtr,
      Runs w p ω (asmFirstInitOneCompElseStmt (bBun + bundleOffSort) (bBun + bundleIdxInitSlots))
        st5 (.returned hEnd) st' cost ∧
      uniqE.Pairwise (· < ·) ∧ uniqE.toFinset = coreE ∧
      uniqB.Pairwise (· < ·) ∧ uniqB.length = r ∧
      (∀ b, b ∈ tr.activeBuckets comps[c] ↔ bucketCode b ∈ uniqB) ∧
      (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S' m' st'.mem ∧
      (TR vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      (∀ j : Fin slotCap, j.1 < nSlots ∨ nSlots + r ≤ j.1 → S' j = S₀ j) ∧
      (∀ bi (hbi : bi < uniqB.length), ∃ (hs : nSlots + bi < slotCap) (B' : BundleState),
        S' ⟨nSlots + bi, hs⟩ = some B' ∧
        BunAgree B' (tr.bun (comps[c], bucketCodeInv (uniqB[bi]'hbi)))) ∧
      st'.mem (restH + ASM_SD_NSLOTS) = nSlots + r ∧
      st'.mem (ctH + 3 * c + 1) = cslPtr ∧ st'.mem (ctH + 3 * c + 2) = r ∧
      (∀ bi (hbi : bi < uniqB.length),
        st'.mem (cslPtr + 2 * bi) = uniqB[bi]'hbi ∧
        st'.mem (cslPtr + 2 * bi + 1) = nSlots + bi) ∧
      (r = 0 ∨ (h ≤ cslPtr ∧ cslPtr + 2 * r ≤ hEnd ∧
        (∀ a, cslPtr ≤ a → a < cslPtr + 2 * r →
          ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a ∧
          ¬ (TR vCap eCap).foot tourH tx' a ∧ st'.mem a < 2 ^ w))) ∧
      (∀ bi < r, st'.mem (slotsPtr + (nSlots + bi)) = nSlots + bi) ∧
      ListAt st'.mem (st'.mem lazySlotPtr) uniqE ∧
      st'.mem (lazySlotPtr + 1) = uniqE.length ∧
      (uniqE.length = 0 ∨ (h ≤ st'.mem lazySlotPtr ∧ st'.mem lazySlotPtr + uniqE.length ≤ hEnd ∧
        (∀ a, st'.mem lazySlotPtr ≤ a → a < st'.mem lazySlotPtr + uniqE.length →
          ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a ∧
          ¬ (TR vCap eCap).foot tourH tx' a))) ∧
      h ≤ hEnd ∧ hEnd ≤ h + newActOneSpace TS hRoot.querySpace (cord r_c).length coreE.card r ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a →
        (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∨ (h ≤ a ∧ a < hEnd)) ∧
      (∀ a, (TR vCap eCap).foot tourH tx' a →
        (TR vCap eCap).foot tourH tx a ∨ (h ≤ a ∧ a < hEnd)) ∧
      (∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a →
        ¬ (TR vCap eCap).foot tourH tx' a) ∧
      (∀ a < h, ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a →
        ¬ (TR vCap eCap).foot tourH tx a →
        a ≠ restH + ASM_SD_NSLOTS →
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) →
        ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + r) →
        ¬ (lazySlotPtr ≤ a ∧ a < lazySlotPtr + 2) →
        st'.mem a = mem₀ a) ∧
      cost + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m' st'.mem +
          (TR vCap eCap).phi tourH tx' st'.mem ≤
        newActElseCost TS eCap (cord r_c).length coreE.card r cord r_c +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m₀ mem₀ +
        (TR vCap eCap).phi tourH tx2 st5.mem := by
  intro cord r_c coreE r
  have hpSort : p.HasAt (bBun + bundleOffSort) (sortProcs (bBun + bundleOffSort)) :=
    (bundleProcs_unpack hpBun).1
  have h1w : 1 < 2 ^ w := by omega
  have hrc_w : r_c < 2 ^ w := lt_trans hrc_lt hvCapW
  rcases hMutDisj with ⟨hMD_rest, hMD_bkt, hMD_ct, hMD_sl, hMD_lazy⟩
  obtain ⟨BT, hBT_rep⟩ := hTB vCap eCap ord tr.cs.RF cord mk
  rcases BT with ⟨rBT, rBT_loc, rBT_list, rBT_len, rBT_own⟩
  dsimp only at hBT_rep; subst hBT_rep
  set BT : BundleTourAt TS w vCap eCap p fTourList fTourLen fTourOwner :=
    ⟨asmTourCordView (TR vCap eCap) ord tr.cs.RF cord mk, rBT_loc, rBT_list, rBT_len, rBT_own⟩
  set len := (cord r_c).length
  have hSpace' := hSpace
  dsimp only [newActOneSpace] at hSpace'
  change h + (hRoot.querySpace + 2 * TS.listSpace len + 3 * len + 30 * coreE.card + 10 * r + 1) < 2 ^ w at hSpace'
  change nSlots + r ≤ slotCap at hCapRoom
  change ∀ a, slotsPtr + nSlots ≤ a → a < slotsPtr + nSlots + r → _ at hMD_sl
  change ∀ a, lazySlotPtr ≤ a → a < lazySlotPtr + 2 →
    ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m₀ a ∧
    ¬ (TR vCap eCap).foot tourH tx a ∧
    ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧
    ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
    ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) ∧
    ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + r) at hMD_lazy
  have hbkt5 : ∀ e ∈ tr.cs.G₀.E, e < eCap ∧ st5.mem (bktH + e) = bucketCode (tr.origBucket e) ∧
      st5.mem (bktH + e) < 2 ^ w := fun e he => by
    have hbk := hbkt_ok e he
    have heq := hfr2_lt (bktH + e) (by omega) (hMD_bkt _ (by omega) (by omega))
    exact ⟨hbk.1, heq.trans hbk.2.1, heq.symm ▸ hbk.2.2⟩
  obtain ⟨st28, cP, uniqE, uniqB, uniqE_ptr, assigns, specs, csl, rPtr, hrunP,
      huniqE_pw, huniqE_toFinset, huniqB_pw, hr_eq, huniqB_iff, huniqB_w,
      huE_lo, huE_hi, hsp_eq, hcsl_eq, hrP_eq, hrP_hi,
      hr1_28, hr15_28, hr20_28, hr22_28, hr24_28, hr26_28, hr29_28,
      hspecs28, hass28, hrPtr_28, huniqE_at28, hnsl28, hct1_28, hct2_28,
      hcsl28, hslots28, hlz0_28, hlz1_28, hz28, hfr28, hcP⟩ :=
    asmFirstInitOneComp_prep_runs (ω := ω) hpSort hc hBktsEq hCoreInG₀ heCapG hw16 heCapW hrc_w
      hCordIff hrestH_lt hRec hbkt5 hbkt_lt hct_lt hsl_lt hlazy_lt hCapRoom
      ⟨fun a h1' h2' => (hMD_ct a h1' h2').2.2,
       fun a h1' h2' => (hMD_sl a h1' h2').2.2,
       fun a h1' h2' => (hMD_lazy a h1' h2').2.2⟩
      hh_le hh1_le hEndL hzL hrec5 hregs5 (by dsimp only [len, cord, r_c, coreE, r] at hh2_hi hSpace' ⊢; omega)
  change uniqE.toFinset = coreE at huniqE_toFinset
  have hmC_eq : uniqE.length = coreE.card := by
    rw [← huniqE_toFinset, List.toFinset_card_of_nodup (huniqE_pw.imp fun h => Nat.ne_of_lt h)]
  change h2 ≤ h + hRoot.querySpace + TS.listSpace len at hh2_hi
  change rPtr + 1 ≤ h2 + 2 * len + 6 * coreE.card + 7 * r + 1 at hrP_hi
  have hloN : restH ≤ restH + ASM_SD_NSLOTS := by unfold ASM_SD_NSLOTS; omega
  have hhiN : restH + ASM_SD_NSLOTS < restH + ASM_SD_SIZE := by unfold ASM_SD_NSLOTS ASM_SD_SIZE; omega
  set hPre := rPtr + 1
  let cntFn : ℕ → ℕ := fun bi => (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (tr.origBucket e)) = bi)).length
  let specsL := (List.range uniqB.length).map fun bi => (nSlots + bi, 4 * cntFn bi)
  let assignsL := uniqE.map fun e => (e, nSlots + uniqB.idxOf (bucketCode (tr.origBucket e)))
  have hBktMem : ∀ e ∈ uniqE, bucketCode (tr.origBucket e) ∈ uniqB := fun e he => by
    have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
    exact (huniqB_iff (tr.origBucket e)).mp (by rw [hBktsEq]; exact Finset.mem_image_of_mem _ heC)
  have hsumCnt : ((List.range uniqB.length).map cntFn).sum = uniqE.length :=
    sum_filter_idxOf_eq_length uniqE (fun e => uniqB.idxOf (bucketCode (tr.origBucket e))) uniqB.length
      (fun e he => List.idxOf_lt_length_of_mem (hBktMem e he))
  have hSBspace : slotBlocksSpace specsL = 3 * uniqB.length + 24 * uniqE.length :=
    slotBlocksSpace_specs_eq hsumCnt
  have hInitSpace : bundleInitSlotsSpace TS specsL cord [r_c] =
      3 * uniqB.length + 24 * uniqE.length + TS.listSpace len := by
    simp [bundleInitSlotsSpace, hSBspace, len]
  have hrepB28_loc := (bunTableHeadroomRep_local slotCap vCap eCap tr.k) bunH S₀ m₀ mem₀ st28.mem fun a ha => by
    have halt := hfootB a ha
    rw [hfr28 a (by omega)
      (fun h => (hMD_rest a (h ▸ hloN) (h ▸ hhiN)).1 ha)
      (fun h => (hMD_ct a h.1 h.2).1 ha)
      (fun h => (hMD_sl a h.1 h.2).1 ha)
      (fun h => (hMD_lazy a h.1 h.2).1 ha)]
    exact (hfr2_lt a halt (hdisjBT a ha)).symm
  have hrepBT28_loc := rBT_loc tourH cord tx2 st5.mem st28.mem fun a ha => by
    rcases hft2 a ha with h0 | ⟨hlo, hhi⟩
    · exact (hfr28 a (by have := hfootT a h0; omega)
        (fun h => (hMD_rest a (h ▸ hloN) (h ▸ hhiN)).2 h0)
        (fun h => (hMD_ct a h.1 h.2).2.1 h0)
        (fun h => (hMD_sl a h.1 h.2).2.1 h0)
        (fun h => (hMD_lazy a h.1 h.2).2.1 h0)).symm
    · exact (hfr28 a hhi (by omega) (by omega) (by omega) (by omega)).symm
  have hrepBT28 : BT.rep.rep tourH cord tx2 st28.mem := hrepBT28_loc.1 ⟨rfl, hOK_cord, hrepT2⟩
  have hspecs_fst : specsL.map Prod.fst = (List.range uniqB.length).map (nSlots + ·) := by
    simp [specsL, List.map_map, Function.comp_def]
  have hspecs_nd : (specsL.map Prod.fst).Nodup := by
    rw [hspecs_fst]; exact List.nodup_range.map fun _ _ h => by omega
  have hspecs_cap4 : ∀ sb ∈ specsL, 4 * (slotEdgesOf assignsL sb.1).card ≤ sb.2 := by
    intro sb hsb; rcases List.mem_map.mp hsb with ⟨bi, hbi, rfl⟩
    have hcnt_eq := list_filter_count_eq_card_slotEdgesOf (uniqB := uniqB) (origB := tr.origBucket) (nSlots := nSlots)
      (bi := bi) (huniqE_pw.imp fun h => Nat.ne_of_lt h)
    dsimp only [cntFn, assignsL] at *; omega
  have hassigns_nd : (assignsL.map Prod.fst).Nodup := by
    have : assignsL.map Prod.fst = uniqE := by simp [assignsL, List.map_map, Function.comp_def]
    rw [this]; exact huniqE_pw.imp fun h => Nat.ne_of_lt h
  have hassigns_fresh : ∀ es ∈ assignsL, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → es.1 ∉ B.edges := by
    intro es hes j B hSj; rcases List.mem_map.mp hes with ⟨e, he, rfl⟩
    have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
    exact hOldEdgeDisj j B hSj e (Finset.mem_filter.mp heC).1 (Finset.mem_filter.mp heC).2
  have hcov_r : ∀ es ∈ assignsL, ∀ side : Bool, ∃ v' ∈ [r_c], (es.1, side) ∈ cord v' := by
    intro es hes side; rcases List.mem_map.mp hes with ⟨e, he, rfl⟩
    exact ⟨r_c, List.mem_cons_self, (hCordIff (e, side)).mpr (by change e ∈ coreE; rw [← huniqE_toFinset]; exact List.mem_toFinset.mpr he)⟩
  obtain ⟨bodyI, hbI, stI, cI, hEnd, tx3, hrunI, hI_lo, hI_hi, hzI, hrepB3, hinvB3, hrepBT3,
      hfootB3, hfootT3, hfrI, hcostI⟩ :=
    bunTableHeadroom_initSlots_runs (TS := TS) (w := w) (slotCap := slotCap) (vCap := vCap)
      (eCap := eCap) (tbl := bunH) (tourH := tourH) (k := tr.k) (nSlots := uniqB.length)
      (slotSpecPtr := specs) (nEdges := uniqE.length) (edgeAssignPtr := assigns)
      (nR := 1) (rPtr := rPtr) (h := hPre) (specs := specsL) (assigns := assignsL)
      (cord := cord) (rList := [r_c]) (S₀ := S₀) (m₀ := m₀) (mem₀ := st28.mem) (pos₀ := st28.pos)
      (tx₀ := tx2) (ω := ω) hpBun BT hw16 hk1 htourW (by omega)
      (fun a ha => by have := hfootB a ha; omega)
      (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
      (by rw [hInitSpace]; omega) (hrepB28_loc.1 hrepB) hinvB hz28 hrepBT28
      (fun a ha => by rcases hft2 a ha with h0 | ⟨_, hhi⟩ <;> [have := hfootT a h0; skip] <;> omega)
      (fun a ha => by
        rcases hft2 a ha with h0 | ⟨hlo, _⟩
        · by_contra hnot; push Not at hnot; exact hdisjBT a (Or.inl hnot) h0
        · right; omega)
      (fun a ha j ptr cB hsb => by
        rcases hft2 a ha with h0 | ⟨hlo, _⟩
        · by_contra hnot; push Not at hnot
          exact hdisjBT a (Or.inr ⟨j, ptr, cB, hsb, hnot.1, hnot.2⟩) h0
        · by_contra hnot; push Not at hnot
          have := hfootB a (Or.inr ⟨j, ptr, cB, hsb, hnot.1, hnot.2⟩); omega)
      (fun a ha => Or.inl (by rcases hft2 a ha with h0 | ⟨_, hhi⟩ <;> [have := hfootT a h0; skip] <;> omega))
      (fun a ha => Or.inl (by rcases hft2 a ha with h0 | ⟨_, hhi⟩ <;> [have := hfootT a h0; skip] <;> omega))
      (by simp [specsL]) hspecs28
      (fun sb hsb => by rcases List.mem_map.mp hsb with ⟨bi, hbi, rfl⟩; have := List.mem_range.mp hbi; omega)
      hspecs_nd
      (fun sb hsb hlt => by rcases List.mem_map.mp hsb with ⟨bi, hbi, rfl⟩; exact hFreeSlots _ (by omega) hlt)
      hspecs_cap4 (by simp [assignsL]) hass28
      (fun es hes => by
        rcases List.mem_map.mp hes with ⟨e, he, rfl⟩
        have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
        refine ⟨heCapG e (Finset.mem_sdiff.mp (Finset.mem_filter.mp heC).1).1, ?_⟩
        rw [hspecs_fst]; exact List.mem_map.mpr ⟨_, List.mem_range.mpr (List.idxOf_lt_length_of_mem (hBktMem e he)), rfl⟩)
      hassigns_nd hassigns_fresh (by omega) rfl
      (fun i hi => by cases i with | zero => simpa using hrPtr_28 | succ k => simp at hi)
      (fun v' hv' => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'; subst hv'; exact ⟨hrc_lt, hrc_w⟩)
      (List.nodup_singleton r_c) (fun v' _ => hcord_nd v') hcov_r
  have hcallI : Runs w p ω (.call 27 (bBun + bundleIdxInitSlots)
      [.reg 29, .reg 1, .reg 20, .reg 24, .reg 15, .reg 22, .const 1, .reg 26, .bin .add (.reg 26) (.const 1)])
      st28 .normal { stI with regs := Function.update st28.regs 27 hEnd } _ :=
    runs_call_iff.mpr ⟨[bunH, tourH, uniqB.length, specs, uniqE.length, assigns, 1, rPtr, hPre],
      bodyI, .returned hEnd, stI, cI,
      by have hltP : rPtr + 1 < 2 ^ w := by omega
         simp [evalArgs, Expr.eval, BinOp.eval, hr29_28, hr1_28, hr20_28, hr24_28, hr15_28, hr22_28, hr26_28, h1w, hltP, hPre],
      hbI, hrunI, rfl, rfl, rfl⟩
  set st29 : State := { stI with regs := Function.update st28.regs 27 hEnd }
  have hret : Runs w p ω (.ret (.reg 27)) st29 (.returned hEnd) st29 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, st29], rfl, rfl, rfl⟩
  have hfull := runs_seq_iff.mpr (Or.inr ⟨st28, _, _, hrunP, runs_seq_iff.mpr (Or.inr ⟨st29, _, _, hcallI, hret, rfl⟩), rfl⟩)
  set S' := tableAfterInitSlots S₀ specsL assignsL cord [r_c] tr.k
  set m' := allocSlotBlocksMeta m₀ specsL hPre
  have hBunNew : ∀ bi (hbi : bi < uniqB.length), ∃ (hs : nSlots + bi < slotCap) (B' : BundleState),
      S' ⟨nSlots + bi, hs⟩ = some B' ∧ BunAgree B' (tr.bun (comps[c], bucketCodeInv (uniqB[bi]'hbi))) := by
    intro bi hbi'; have hs : nSlots + bi < slotCap := by omega
    have hj_in : (⟨nSlots + bi, hs⟩ : Fin slotCap).1 ∈ specsL.map Prod.fst := by
      rw [hspecs_fst]; exact List.mem_map.mpr ⟨bi, List.mem_range.mpr hbi', rfl⟩
    have hEeq_slot := slotEdgesOf_eq_bucketCoreEdges (G_core := coreGraph tr.cs.G tr.cs.lsf)
      (origB := tr.origBucket) (C := comps[c]) (nSlots := nSlots)
      (fun e => by rw [← List.mem_toFinset, huniqE_toFinset]; exact Finset.mem_filter) huniqB_pw hbi'
    have hEsub : slotEdgesOf assignsL (nSlots + bi) ⊆ (coreGraph tr.cs.G tr.cs.lsf).E := by
      rw [hEeq_slot]; exact Finset.filter_subset _ _
    have hcov_one : ∀ v' x, x ∈ cord v' → x.1 ∈ slotEdgesOf assignsL (nSlots + bi) → v' ∈ [r_c] := by
      intro v' x hx hxe; rw [hEeq_slot] at hxe
      exact List.mem_singleton.mpr (hCordOnly v' x hx (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hxe).1, (Finset.mem_filter.mp hxe).2.1⟩))
    obtain ⟨B', hB'eq, hB'ag⟩ := tableAfterInitSlots_bunAgree hk1 hCoreCord (S₀ := S₀)
      (j := ⟨nSlots + bi, hs⟩) hj_in hEsub (List.pairwise_singleton _ _)
      (fun v' hv' => by simp only [List.mem_singleton] at hv'; subst hv'; exact Finset.mem_biUnion.mpr ⟨comps[c], hC, hrc_R⟩) hcov_one
    rw [hEeq_slot] at hB'ag
    have hLz := hLazyBun _ (by rw [huniqB_iff, bucketCodeInv_right]; exact List.getElem_mem hbi')
    exact ⟨hs, B', hB'eq, ⟨hB'ag.1.trans hLz.1, hB'ag.2.1.trans hLz.2.1,
      hB'ag.2.2.1.trans hLz.2.2.1, fun x hx => (hB'ag.2.2.2 x hx).trans (hLz.2.2.2 x (hB'ag.2.1 ▸ hx))⟩⟩
  have hS'_other : ∀ j : Fin slotCap, j.1 < nSlots ∨ nSlots + r ≤ j.1 → S' j = S₀ j := by
    intro j hj; have hnot : j.1 ∉ specsL.map Prod.fst := by
      rw [hspecs_fst, List.mem_map]; rintro ⟨bi, hbi, hEq⟩; have := List.mem_range.mp hbi; omega
    simp [S', tableAfterInitSlots, hnot]
  have hftT3_all : ∀ a, (TR vCap eCap).foot tourH tx3 a → (TR vCap eCap).foot tourH tx a ∨ (h ≤ a ∧ a < hEnd) := fun a ha => by
    rcases hfootT3 a ha with h2' | ⟨hlo, hhi⟩
    · rcases hft2 a h2' with h0 | ⟨hlo0, hhi0⟩; exact Or.inl h0; exact Or.inr ⟨hlo0, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have hdisjBT3 : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a → ¬ (TR vCap eCap).foot tourH tx3 a := fun a haB haT => by
    rcases hfootB3 a haB with hB0 | ⟨hBlo, hBhi⟩
    · rcases hfootT3 a haT with hT2 | ⟨hTlo, _⟩
      · rcases hft2 a hT2 with hT0 | ⟨hTlo0, _⟩; exact hdisjBT a hB0 hT0; have := hfootB a hB0; omega
      · have := hfootB a hB0; omega
    · rcases hfootT3 a haT with hT2 | ⟨hTlo, _⟩
      · rcases hft2 a hT2 with hT0 | ⟨_, hThi0⟩; have := hfootT a hT0; omega; omega
      · omega
  have hnotT2 : ∀ a, h2 ≤ a → ¬ (TR vCap eCap).foot tourH tx2 a := fun a ha hT => by
    rcases hft2 a hT with h0 | ⟨_, hhi⟩ <;> [have := hfootT a h0; skip] <;> omega
  have hlz0 : stI.mem lazySlotPtr = uniqE_ptr :=
    (hfrI _ (by omega) (hMD_lazy _ (by omega) (by omega)).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_lazy _ (by omega) (by omega)).2.1 h0; omega)).trans hlz0_28
  refine ⟨hEnd, st29, _, S', m', tx3, uniqE, uniqB, csl, hfull,
    huniqE_pw, huniqE_toFinset, huniqB_pw, hr_eq, huniqB_iff,
    hrepB3, hrepBT3.2.2, hinvB3, hS'_other, hBunNew, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, by rw [hInitSpace] at hI_hi; dsimp only [newActOneSpace]; omega, hzI,
    fun a ha => (hfootB3 a ha).elim Or.inl (fun h1' => Or.inr ⟨by omega, by omega⟩),
    hftT3_all, hdisjBT3, ?_, ?_⟩
  · exact (hfrI _ (by omega) (hMD_rest _ hloN hhiN).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_rest _ hloN hhiN).2 h0; omega)).trans hnsl28
  · exact (hfrI _ (by omega) (hMD_ct _ (by omega) (by omega)).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_ct _ (by omega) (by omega)).2.1 h0; omega)).trans hct1_28
  · exact (hfrI _ (by omega) (hMD_ct _ (by omega) (by omega)).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_ct _ (by omega) (by omega)).2.1 h0; omega)).trans hct2_28
  · intro bi hbi
    exact ⟨(hfrI _ (by omega) (fun hB => by have := hfootB _ hB; omega) (hnotT2 _ (by omega))).trans (hcsl28 bi hbi).1,
      (hfrI _ (by omega) (fun hB => by have := hfootB _ hB; omega) (hnotT2 _ (by omega))).trans (hcsl28 bi hbi).2⟩
  · right; refine ⟨by omega, by omega, fun a ha1 ha2 => ⟨?_, ?_, ?_⟩⟩
    · intro hB; rcases hfootB3 a hB with hB0 | ⟨hlo, _⟩; have := hfootB a hB0; omega; omega
    · intro hT; rcases hfootT3 a hT with hT2 | ⟨hlo, _⟩; exact hnotT2 a (by omega) hT2; omega
    · have hbi : (a - csl) / 2 < uniqB.length := by omega
      change stI.mem a < 2 ^ w
      rw [hfrI a (by omega) (fun hB => by have := hfootB a hB; omega) (hnotT2 a (by omega))]
      by_cases hev : (a - csl) % 2 = 0
      · rw [show a = csl + 2 * ((a - csl) / 2) by omega, (hcsl28 _ hbi).1]; exact huniqB_w _ (List.getElem_mem hbi)
      · rw [show a = csl + 2 * ((a - csl) / 2) + 1 by omega, (hcsl28 _ hbi).2]; omega
  · intro bi hbi
    exact (hfrI _ (by omega) (hMD_sl _ (by omega) (by omega)).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_sl _ (by omega) (by omega)).2.1 h0; omega)).trans (hslots28 bi hbi)
  · intro i hi; change stI.mem (stI.mem lazySlotPtr + i) = uniqE[i]'hi
    rw [hlz0, hfrI _ (by omega) (fun hB => by have := hfootB _ hB; omega) (hnotT2 _ (by omega))]
    exact huniqE_at28 i hi
  · exact (hfrI _ (by omega) (hMD_lazy _ (by omega) (by omega)).1
      (fun hT => by rcases hft2 _ hT with h0 | ⟨hlo, _⟩; exact (hMD_lazy _ (by omega) (by omega)).2.1 h0; omega)).trans hlz1_28
  · right; change h ≤ stI.mem lazySlotPtr ∧ stI.mem lazySlotPtr + uniqE.length ≤ hEnd ∧ _
    rw [hlz0]; refine ⟨by omega, by omega, fun a ha1 ha2 => ⟨?_, ?_⟩⟩
    · intro hB; rcases hfootB3 a hB with hB0 | ⟨hlo, _⟩; have := hfootB a hB0; omega; omega
    · intro hT; rcases hfootT3 a hT with hT2 | ⟨hlo, _⟩; exact hnotT2 a (by omega) hT2; omega
  · intro a ha hnb hnt hns hct hsl hlz
    change stI.mem a = mem₀ a
    rw [hfrI a (by omega) hnb (fun hT => by rcases hft2 a hT with h0 | ⟨hlo, _⟩; exact hnt h0; omega),
      hfr28 a (by omega) hns hct hsl hlz]
    exact hfr2_lt a ha hnt
  · dsimp only [newActElseCost, argsSize, Expr.size, st29, BT, asmTourCordView, cordRepM, asmTourView] at hcP hcostI ⊢
    change cP ≤ newActPrepCost len coreE.card r at hcP
    rw [← hrepB28_loc.2] at hcostI
    have hphiT : (TR vCap eCap).phi tourH tx2 st5.mem = (TR vCap eCap).phi tourH tx2 st28.mem := hrepBT28_loc.2
    rw [← hphiT, hmC_eq, hr_eq] at hcostI
    linarith [hcP, hcostI]

end

end MinCostFlow.SparseCore.Program
