module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActBody

import WordRAM.Tactic

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 3b. Full verification of `asmFirstInitOneCompStmt` -/

public section

/-- Cost bound of `asmFirstInitOneCompStmt` on a component with `len = (cord r_c).length`,
`m_C` core edges, `r` active buckets, and root `r_c`. -/
@[expose] def newActOneCost (TS : BundleTourSpec) (rMul eCap len m_C r : ℕ) (cord : ℕ → List End) (r_c : ℕ) : ℕ :=
  rMul * ordStoreLog eCap + TS.mul * (len + 1) * ordStoreLog eCap +
    (if len = 0 then 0 else newActElseCost TS eCap len m_C r cord r_c) + 100

set_option maxHeartbeats 800000 in
/-- **Complete verification of `asmFirstInitOneCompStmt`** on one newly active component
`C = comps[c]` (`C ∉ tr.activeComps`) with witness `v ∈ (tr.cs.compSt C).G.V`. -/
theorem asmFirstInitOneComp_runs {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w depth slotCap vCap eCap bBun fVertRoot fTourList fTourLen fTourOwner : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun fTourList fTourLen fTourOwner))
    (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (hTB : AsmBrTourBridge TS TR w p fTourList fTourLen fTourOwner)
    {restH tourH c v lazySlotPtr h pos : ℕ}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState depth} {ord : ℕ → List End} {mk : Finset End}
    {tx : (TR vCap eCap).τ}
    {bunH slotsPtr bktH ctH nSlots : ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {comps : List (Finset ℕ)} {mem₀ : ℕ → ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hCross : AsmFirstCrossInactiveInv tr)
    (hk1 : 1 ≤ tr.k)
    (hc : c < comps.length) (hC : comps[c] ∈ components tr.cs.G₀)
    (hNotAct : comps[c] ∉ tr.activeComps)
    (hR1 : (tr.cs.compSt comps[c]).R.card = 1)
    (hBktsEq : tr.activeBuckets comps[c] =
      ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]).image tr.origBucket)
    (hCoreInG₀ : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c] → e ∈ tr.cs.G₀.E)
    (hLazyBun : ∀ b ∈ tr.activeBuckets comps[c],
      BunAgree (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket comps[c] b) tr.k)
        (tr.bun (comps[c], b)))
    (hv : v ∈ (tr.cs.compSt comps[c]).G.V)
    (hvCapG : ∀ u ∈ tr.cs.G.V, u < vCap) (heCapG : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hw16 : 16 ≤ 2 ^ w) (hvCapW : vCap < 2 ^ w) (heCapW : 4 * eCap < 2 ^ w)
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
    (hrepT : (TR vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx mem₀)
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
    (hargsW : ∀ a ∈ [restH, tourH, c, v, lazySlotPtr, h], a < 2 ^ w)
    (htblFit : bunH + bundleTableFixedSize slotCap eCap ≤ h)
    (hZero : ZeroFrom mem₀ h)
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
      Runs w p ω
        (asmFirstInitOneCompStmt fVertRoot fTourList (bBun + bundleOffSort) (bBun + bundleIdxInitSlots))
        (startState [restH, tourH, c, v, lazySlotPtr, h] mem₀ pos) (.returned hEnd) st' cost ∧
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
      st'.mem (ctH + 3 * c + 1) = cslPtr ∧ cslPtr ≤ hEnd ∧ st'.mem (ctH + 3 * c + 2) = r ∧
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
      h ≤ st'.mem lazySlotPtr ∧ st'.mem lazySlotPtr + uniqE.length ≤ hEnd ∧
      (∀ a, st'.mem lazySlotPtr ≤ a → a < st'.mem lazySlotPtr + uniqE.length →
        ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m' a ∧
        ¬ (TR vCap eCap).foot tourH tx' a) ∧
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
        newActOneCost TS hRoot.mul eCap (cord r_c).length coreE.card r cord r_c +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m₀ mem₀ +
        (TR vCap eCap).phi tourH tx mem₀ := by
  intro cord r_c coreE r
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hrestW, htourW, hcW, hvW, hlazyW, hhW⟩
  obtain ⟨hReq, hrc_C, hrc_R, hroot_all, hroot_only⟩ :=
    inactive_comp_root_unique hI hC hR1 hv
  obtain ⟨hCordIff, hCordOnly, hCoreInC⟩ :=
    inactive_comp_cord_iff hI ρ hρ hC hNotAct hR1 hCross hv
  have hvG : v ∈ tr.cs.G.V := hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨comps[c], hC, hv⟩
  have hrcG : r_c ∈ tr.cs.G.V := (compLSF_RF_isRSF hI).2.2.1 hrc_R
  have hrc_lt : r_c < vCap := hvCapG r_c hrcG
  have hrc_w : r_c < 2 ^ w := lt_trans hrc_lt hvCapW
  have hOK_cord : TourCordOK ord tr.cs.RF cord := by
    classical
    have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ tr.cs) (ρ' : Rotation tr.cs.G),
        ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
    exact ⟨tr.cs, ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.choose,
      hex.choose_spec.choose_spec.choose_spec.choose,
      hex.choose_spec.choose_spec.choose_spec.choose_spec,
      by simp only [cord, outCoreOrder, hex, ↓reduceDIte]⟩, rfl⟩
  have hCoreCord : CoreCordOf tr.cs ord cord := by
    refine ⟨C_lsst, ℓ₀, hI, ρ, hρ, ?_⟩
    funext u
    have hRS_lsf : tr.cs.lsf.F.IsRootedSpanningForestOf tr.cs.G := compLSF_RF_isRSF hI
    rw [tourCordOK_eq_coreTour hOK_cord u, ← hρ]
    exact coreTour_eq_coreRotation (L := tr.cs.lsf) ρ hI.hG_val hRS_lsf u
  have hcord_nd : ∀ u, (cord u).Nodup := fun u => by
    obtain ⟨_, _, hI', ρ', _, hceq⟩ := hCoreCord
    rw [hceq]
    exact (coreRotation (L := tr.cs.lsf) ρ' hI'.hG_val (compLSF_RF_isRSF hI')).nodup u
  have hSpace' := hSpace
  dsimp only [newActOneSpace] at hSpace'
  -- Step 1: fVertRoot [tourH, v, h]
  set st0 := startState [restH, tourH, c, v, lazySlotPtr, h] mem₀ pos
  obtain ⟨bodyR, hbR, oR, stR, cR, tx1, hrunR, hrepT1, hrc_mem, _, hrespR, hcostR⟩ :=
    hRoot.runs vCap eCap tourH v h ⟨ord, tr.cs.RF, mk⟩ tx mem₀ pos ω
      htourW (hvCapG v hvG) hvW hhW hrepT hfootT hZero
      (by omega)
  rcases hrespR with ⟨hR_lo, hR_hi, hzR, hR_fr, hR_ft⟩
  set h1 := oR.value
  have hcallR : Runs w p ω (.call 6 fVertRoot [.reg 1, .reg 3, .reg 5]) st0 .normal
      { stR with regs := Function.update st0.regs 6 h1 }
      (argsSize [.reg 1, .reg 3, .reg 5] + cR + 1) :=
    runs_call_iff.mpr ⟨[tourH, v, h], bodyR, oR, stR, cR,
      by simp [evalArgs, Expr.eval, st0, startState], hbR, hrunR, rfl, rfl, rfl⟩
  set st1 : State := { stR with regs := Function.update st0.regs 6 h1 }
  have ha7 : Runs w p ω (.assign 7 (.load (.reg 5))) st1 .normal
      { st1 with regs := Function.update st1.regs 7 r_c } _ :=
    runs_assign_iff.mpr ⟨r_c, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st1, st0, startState])) hrc_mem,
      rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 7 r_c }
  -- Step 2: fTourList [tourH, r_c, h1]
  obtain ⟨BT, hBT_rep⟩ := hTB vCap eCap ord tr.cs.RF cord mk
  rcases BT with ⟨rBT, rBT_loc, rBT_list, rBT_len, rBT_own⟩
  dsimp only at hBT_rep; subst hBT_rep
  have hrepBT1 : (asmTourCordView (TR vCap eCap) ord tr.cs.RF cord mk).rep tourH cord tx1 st2.mem :=
    ⟨rfl, hOK_cord, hrepT1⟩
  have hfootT1 : ∀ a, (asmTourCordView (TR vCap eCap) ord tr.cs.RF cord mk).foot tourH tx1 a → a < h1 := fun a ha => by
    rcases hR_ft a ha with h0 | ⟨_, hhi⟩
    · have := hfootT a h0; omega
    · exact hhi
  obtain ⟨bodyL, hbL, oL, stL, cL, tx2, hrunL, hrepBT2, hEndL, hL_lo, hrespL, hcostL⟩ :=
    rBT_list tourH r_c h1 cord tx1 st2.mem st2.pos ω htourW hrc_lt hrc_w (by omega)
      hrepBT1 hfootT1 hzR (by dsimp only [cord, r_c]; omega)
  rcases hrespL with ⟨_, hL_hi, hzL, hL_fr, hL_ft⟩
  have hrepT2 : (TR vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx2 stL.mem := hrepBT2.2.2
  set h2 := oL.value
  have hcallL : Runs w p ω (.call 8 fTourList [.reg 1, .reg 7, .reg 6]) st2 .normal
      { stL with regs := Function.update st2.regs 8 h2 }
      (argsSize [.reg 1, .reg 7, .reg 6] + cL + 1) :=
    runs_call_iff.mpr ⟨[tourH, r_c, h1], bodyL, oL, stL, cL,
      by simp [evalArgs, Expr.eval, st2, st1, st0, startState], hbL, hrunL, rfl, rfl, rfl⟩
  set st3 : State := { stL with regs := Function.update st2.regs 8 h2 }
  have hfr2_lt : ∀ a < h, ¬ (TR vCap eCap).foot tourH tx a → st3.mem a = mem₀ a := fun a ha hnt =>
    (hL_fr a (by omega) (fun hf => by
      rcases hR_ft a hf with h0 | ⟨hlo, _⟩
      · exact hnt h0
      · omega)).trans (hR_fr a ha hnt)
  have hft2 : ∀ a, (TR vCap eCap).foot tourH tx2 a → (TR vCap eCap).foot tourH tx a ∨ (h ≤ a ∧ a < h2) := fun a ha => by
    rcases hL_ft a ha with h1' | ⟨hlo, hhi⟩
    · rcases hR_ft a h1' with h0 | ⟨hlo0, hhi0⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hlo0, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have hrec3 : ∀ i < ASM_SD_SIZE, st3.mem (restH + i) = mem₀ (restH + i) := fun i hi =>
    hfr2_lt _ (by omega) (hMutDisj.1 _ (by omega) (by omega)).2
  have ha9 : Runs w p ω (.assign 9 (.load (.reg 6))) st3 .normal
      { st3 with regs := Function.update st3.regs 9 (cord r_c).length } _ :=
    runs_assign_iff.mpr ⟨(cord r_c).length,
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st3, st2, st1])) hEndL.1, rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 9 (cord r_c).length }
  have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_CT)))) st4 .normal
      { st4 with regs := Function.update st4.regs 10 ctH } _ :=
    runs_assign_iff.mpr ⟨ctH,
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]))
        (Expr.eval_const (by unfold ASM_SD_CT; omega)) (by unfold ASM_SD_CT ASM_SD_SIZE at *; omega))
        ((hrec3 ASM_SD_CT (by decide)).trans hRec.2.2.2.2), rfl, rfl, rfl⟩
  set st5 : State := { st4 with regs := Function.update st4.regs 10 ctH }
  have hPreComp : ∀ {s : Stmt} {o st' c}, Runs w p ω s st5 o st' c →
      Runs w p ω (.call 6 fVertRoot [.reg 1, .reg 3, .reg 5] ;;
        .assign 7 (.load (.reg 5)) ;; .call 8 fTourList [.reg 1, .reg 7, .reg 6] ;;
        .assign 9 (.load (.reg 6)) ;; .assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_CT))) ;; s)
        st0 o st'
        (argsSize [.reg 1, .reg 3, .reg 5] + cR + 1 +
          ((Expr.load (.reg 5)).size + 1 +
            (argsSize [.reg 1, .reg 7, .reg 6] + cL + 1 +
              ((Expr.load (.reg 6)).size + 1 +
                ((Expr.load (.bin .add (.reg 0) (.const ASM_SD_CT))).size + 1 + c + 1) + 1) + 1) + 1) + 1) :=
    fun hs => runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hcallR,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha7,
        runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcallL,
          runs_seq_iff.mpr (Or.inr ⟨st4, _, _, ha9,
            runs_seq_iff.mpr (Or.inr ⟨st5, _, _, ha10, hs, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Case split on `(cord r_c).length = 0`
  by_cases hlen0 : (cord r_c).length = 0
  · rcases hMutDisj with ⟨hMD_rest, _, hMD_ct, _, hMD_lazy⟩
    have hcord_nil : cord r_c = [] := List.eq_nil_of_length_eq_zero hlen0
    have hcoreE_emp : coreE = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false]
      intro he; have : (e, true) ∈ cord r_c := (hCordIff (e, true)).mpr he; rw [hcord_nil] at this; cases this
    have hr0 : r = 0 := by show (tr.activeBuckets comps[c]).card = 0; rw [hBktsEq]; change (Finset.image tr.origBucket coreE).card = 0; rw [hcoreE_emp]; simp
    have hcond : (Expr.bin .eq (.reg 9) (.const 0)).eval w st5 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [st5, st4, hlen0])) (Expr.eval_const (by omega)) rfl h1w
    set m1 := Function.update st5.mem (ctH + 3 * c + 1) h2
    set m2 := Function.update m1 (ctH + 3 * c + 2) 0
    set m3 := Function.update m2 lazySlotPtr h2
    set m4 := Function.update m3 (lazySlotPtr + 1) 0
    have hs1 : Runs w p ω (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 1)) (.reg 8))
        st5 .normal ⟨m1, st5.regs, st5.pos⟩ _ :=
      runs_store_iff.mpr ⟨ctH + 3 * c + 1, h2,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5]))
          (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, st0, startState])) (by omega)) (by omega))
          (Expr.eval_const h1w) (by omega),
        Expr.eval_reg_of_eq (by simp [st5, st4, st3]), rfl, rfl, rfl⟩
    have hs2 : Runs w p ω (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 2)) (.const 0))
        ⟨m1, st5.regs, st5.pos⟩ .normal ⟨m2, st5.regs, st5.pos⟩ _ :=
      runs_store_iff.mpr ⟨ctH + 3 * c + 2, 0,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5]))
          (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, st0, startState])) (by omega)) (by omega))
          (Expr.eval_const h2w) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hs3 : Runs w p ω (.store (.reg 4) (.reg 8))
        ⟨m2, st5.regs, st5.pos⟩ .normal ⟨m3, st5.regs, st5.pos⟩ _ :=
      runs_store_iff.mpr ⟨lazySlotPtr, h2,
        Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, st0, startState]),
        Expr.eval_reg_of_eq (by simp [st5, st4, st3]), rfl, rfl, rfl⟩
    have hs4 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.const 0))
        ⟨m3, st5.regs, st5.pos⟩ .normal ⟨m4, st5.regs, st5.pos⟩ _ :=
      runs_store_iff.mpr ⟨lazySlotPtr + 1, 0,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, st0, startState]))
          (Expr.eval_const h1w) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hs5 : Runs w p ω (.ret (.reg 8)) ⟨m4, st5.regs, st5.pos⟩ (.returned h2) ⟨m4, st5.regs, st5.pos⟩ 2 :=
      runs_ret_iff.mpr ⟨h2, Expr.eval_reg_of_eq (by simp [st5, st4, st3]), rfl, rfl, rfl⟩
    have hrBrRet := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs3,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs4, hs5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hm4_of : ∀ a, a ≠ ctH + 3 * c + 1 → a ≠ ctH + 3 * c + 2 → a ≠ lazySlotPtr → a ≠ lazySlotPtr + 1 →
        m4 a = st3.mem a := fun a h1' h2' h3' h4' => by
      simp [m4, m3, m2, m1, Function.update_of_ne h4', Function.update_of_ne h3',
        Function.update_of_ne h2', Function.update_of_ne h1', st5, st4]
    have hrepB_loc := (bunTableHeadroomRep_local slotCap vCap eCap tr.k) bunH S₀ m₀ mem₀ m4 fun a ha => by
      have halt := hfootB a ha
      rw [hm4_of a (fun h => (hMD_ct a (by omega) (by omega)).1 ha)
        (fun h => (hMD_ct a (by omega) (by omega)).1 ha)
        (fun h => (hMD_lazy a (by omega) (by omega)).1 ha)
        (fun h => (hMD_lazy a (by omega) (by omega)).1 ha)]
      exact (hfr2_lt a halt (hdisjBT a ha)).symm
    have hrepBT_loc := rBT_loc tourH cord tx2 st3.mem m4 fun a ha => by
      rcases hft2 a ha with h0 | ⟨hlo, _⟩
      · exact (hm4_of a (fun h => (hMD_ct a (by omega) (by omega)).2.1 h0)
          (fun h => (hMD_ct a (by omega) (by omega)).2.1 h0)
          (fun h => (hMD_lazy a (by omega) (by omega)).2.1 h0)
          (fun h => (hMD_lazy a (by omega) (by omega)).2.1 h0)).symm
      · exact (hm4_of a (by omega) (by omega) (by omega) (by omega)).symm
    have hrepT4 : (TR vCap eCap).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx2 m4 :=
      (hrepBT_loc.1 ⟨rfl, hOK_cord, hrepT2⟩).2.2
    have hphiT4 : (TR vCap eCap).phi tourH tx2 st3.mem = (TR vCap eCap).phi tourH tx2 m4 :=
      hrepBT_loc.2
    have hfull : Runs w p ω
        (asmFirstInitOneCompStmt fVertRoot fTourList (bBun + bundleOffSort) (bBun + bundleIdxInitSlots))
        st0 (.returned h2) ⟨m4, st5.regs, st5.pos⟩ _ :=
      hPreComp (runs_cond_iff.mpr ⟨1, _, hcond, by simpa using hrBrRet, rfl⟩)
    refine ⟨h2, ⟨m4, st5.regs, st5.pos⟩, _, S₀, m₀, tx2, [], [], h2, hfull,
      List.Pairwise.nil, by simp [hcoreE_emp], List.Pairwise.nil, by simp [hr0],
      fun b => by rw [hBktsEq]; change b ∈ Finset.image tr.origBucket coreE ↔ _; rw [hcoreE_emp]; simp,
      hrepB_loc.1 hrepB, hrepT4, hinvB,
      fun _ _ => rfl, fun bi hbi => by simp at hbi, ?_, ?_, le_refl h2, ?_, fun bi hbi => by simp at hbi, Or.inl hr0,
      fun bi hbi => by omega, fun i hi => by simp at hi, by simp [m4], ?_, ?_,
      fun a h1 h2 => absurd (lt_of_le_of_lt h1 h2) (by simp),
      by omega, (by dsimp only [newActOneSpace, cord, r_c] at hL_hi ⊢; omega),
      fun a ha => by change m4 a = 0; rw [hm4_of a (by omega) (by omega) (by omega) (by omega)]; exact hzL a ha,
      fun a ha => Or.inl ha, hft2, fun a haB haT => by
        rcases hft2 a haT with h0 | ⟨hlo, _⟩
        · exact hdisjBT a haB h0
        · have := hfootB a haB; omega,
      fun a ha hnb hnt hns hct hsl hlz => by
        change m4 a = mem₀ a; rw [hm4_of a (by omega) (by omega) (by omega) (by omega)]; exact hfr2_lt a ha hnt, ?_⟩
    · have hloN : restH ≤ restH + ASM_SD_NSLOTS := by unfold ASM_SD_NSLOTS; omega
      have hhiN : restH + ASM_SD_NSLOTS < restH + ASM_SD_SIZE := by unfold ASM_SD_NSLOTS ASM_SD_SIZE; omega
      change m4 (restH + ASM_SD_NSLOTS) = nSlots + r
      rw [hm4_of (restH + ASM_SD_NSLOTS)
        (fun heq => (hMD_ct (ctH + 3 * c + 1) (by omega) (by omega)).2.2.1 ⟨heq ▸ hloN, heq ▸ hhiN⟩)
        (fun heq => (hMD_ct (ctH + 3 * c + 2) (by omega) (by omega)).2.2.1 ⟨heq ▸ hloN, heq ▸ hhiN⟩)
        (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.1 ⟨heq ▸ hloN, heq ▸ hhiN⟩)
        (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.1 ⟨heq ▸ hloN, heq ▸ hhiN⟩),
        hrec3 ASM_SD_NSLOTS (by decide), hRec.2.2.1, hr0]; omega
    · simp [m4, m3, m2, m1,
        Function.update_of_ne (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 1 ≠ lazySlotPtr + 1),
        Function.update_of_ne (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 1 ≠ lazySlotPtr)]
    · simp [m4, m3, m2,
        Function.update_of_ne (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 2 ≠ lazySlotPtr + 1),
        Function.update_of_ne (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 2 ≠ lazySlotPtr), hr0]
    · change h ≤ m4 lazySlotPtr
      have : m4 lazySlotPtr = h2 := by simp [m4, m3]
      rw [this]; omega
    · change m4 lazySlotPtr + 0 ≤ h2
      have : m4 lazySlotPtr = h2 := by simp [m4, m3]
      rw [this]; omega
    · change _ + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m₀ m4 +
          (TR vCap eCap).phi tourH tx2 m4 ≤ _
      rw [← hrepB_loc.2, ← hphiT4]
      dsimp only [asmTourCordView, cordRepM, asmTourView, st2, st1, st3] at hcostR hcostL ⊢
      simp only [newActOneCost, argsSize, Expr.size, hlen0, ↓reduceIte] at hcostL ⊢
      omega
  -- Nonempty case: `len > 0`
  · have hcond0 : (Expr.bin .eq (.reg 9) (.const 0)).eval w st5 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (by simp [st5, st4])) (Expr.eval_const (by omega)) hlen0 (by omega)
    obtain ⟨hEnd, st', cE, S', m', tx3, uniqE, uniqB, csl, hrunE, hE_pw, hE_fin, hB_pw, hB_len,
        hB_iff, hrepB3, hrepT3, hinvB3, hS_oth, hBunN, hnsl, hct1, hct2, hcsl_at, hcsl_rg, hsl_at,
        hlz_at, hlz_len, hlz_rg, hh_lo, hh_hi, hzE, hftB3, hftT3, hdisj3, hfrE, hcostE⟩ :=
      asmFirstInitOneComp_else_runs (ω := ω) (st5 := st5) hpBun hRoot hTB hI ρ hρ hk1 hc hC hBktsEq hCoreInG₀
        hLazyBun heCapG hw16 hvCapW heCapW (by rw [hReq]; exact Finset.mem_singleton_self _) hrc_lt hCordIff hCordOnly hOK_cord hCoreCord
        hcord_nd hrestH_lt hRec hbkt_ok hbkt_lt hct_lt hsl_lt hlazy_lt hCapRoom hFreeSlots
        hOldEdgeDisj hrepB hinvB hrepT2 hfootB hfootT hdisjBT hMutDisj htourW htblFit
        hR_lo (by dsimp only [cord, r_c] at hL_lo; omega) (by dsimp only [cord, r_c] at hL_hi; omega) hEndL hzL hfr2_lt hft2 hrec3
        ⟨by simp [st5, st4, st3, st2, st1, st0, startState],
         by simp [st5, st4, st3, st2, st1, st0, startState],
         by simp [st5, st4, st3, st2, st1, st0, startState],
         by simp [st5, st4, st3, st2, st1, st0, startState],
         by simp [st5, st4, st3, st2, st1],
         by simp [st5, st4, st3, st2, r_c],
         by simp [st5, st4, st3],
         by simp [st5, st4, cord, r_c],
         by simp [st5]⟩
        hSpace
    have hfull : Runs w p ω
        (asmFirstInitOneCompStmt fVertRoot fTourList (bBun + bundleOffSort) (bBun + bundleIdxInitSlots))
        st0 (.returned hEnd) st' _ :=
      hPreComp (runs_cond_iff.mpr ⟨0, _, hcond0, by simpa using hrunE, rfl⟩)
    have hne : ¬ uniqE.length = 0 := fun h0 => by
      obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hlen0)
      have heC : x.1 ∈ uniqE.toFinset := hE_fin ▸ (hCordIff x).mp hx
      rw [List.eq_nil_of_length_eq_zero h0] at heC
      simp at heC
    have hlzR := hlz_rg.resolve_left hne
    refine ⟨hEnd, st', _, S', m', tx3, uniqE, uniqB, csl, hfull,
      hE_pw, hE_fin, hB_pw, hB_len, hB_iff, hrepB3, hrepT3, hinvB3, hS_oth, hBunN,
      hnsl, hct1, ?_, hct2, hcsl_at, hcsl_rg, hsl_at, hlz_at, hlz_len, hlzR.1, hlzR.2.1, hlzR.2.2,
      hh_lo, hh_hi, hzE, hftB3, hftT3, hdisj3, hfrE, ?_⟩
    · rcases hcsl_rg with hr0 | ⟨_, hhi, _⟩
      · exfalso
        have hne : (cord r_c).length > 0 := by omega
        obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hne
        have heC : x.1 ∈ coreE := (hCordIff x).mp hx
        have hpos : 0 < r := Finset.card_pos.mpr ⟨tr.origBucket x.1, by rw [hBktsEq]; exact Finset.mem_image_of_mem _ heC⟩
        omega
      · omega
    dsimp only [newActOneCost, argsSize, Expr.size, asmTourCordView, cordRepM, asmTourView, st2, st1, st3, st4, st5] at hcostR hcostL hcostE ⊢
    simp only [hlen0, ↓reduceIte]
    linarith [hcostR, hcostL, hcostE]

end

end MinCostFlow.SparseCore.Program
