module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitPost
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBoundSpace
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBoundCost
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSideModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitEmbModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitS0Model
import Mathlib.Tactic

/-!
# The build of a branch at its init (`AssemblyFirstInitBuildRun`)

Here we prove `AsmFirstInitBuildAt` for the body `asmFirstInitBuildBody F`, at the init state
`tr₀ = initBundleTreeWithParams …`, for any program that holds the procedures of the body at
their places (`asmFirstInitBuildAt_mk`).

The proof has four steps.
1. **The model facts at `tr₀`.** The run of the body (`asmFirstInitBody_runs`) is general in the
   model state and asks its facts as hypotheses. At `tr₀` most of them hold by the definition of
   `initBundleTreeWithParams`, and the rest come from `AsmBrModelFacts`, from the rotation (the
   forest of the LSF is a spanning forest of `G`), and from the start graphs of the bundles
   (`initTree_spanGraphOK`, which needs `1 ≤ depth` and `1 ≤ max impl.p_s impl.p_t`).
2. **The words.** The hypothesis `h + space.eval X < 2 ^ w` of the interface gives every word bound
   of the body (`asmFiBuildSpace_word_bounds`), and the space of the three parts of the body is at
   most `space.eval X` (`asmFiBuildSpace_le_poly`).
3. **The post** without the space and the cost is `asmFirstInit_post`. The model of the bundle
   side is `asmFiSide_model`. Its inactive components need a valid LSF init, which is a hypothesis
   of the build.
4. **The cost.** The potentials of the post are those of the run of the body
   (`asmFirstInit_post_phi`): the record stores do not touch the tour or P5's table, and the
   potential of P6's spanners is that of their abstract state. Then `asmFiBuildCost_le` bounds the
   sum by `asmFiBuildCostMul capExp limbMul` times the machine cost of `tr₀`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The potentials after the record stores.** The potential of the tour at the end is that
after the back, and the potential of the bundle side `asmFiSide` at the end is P5's potential
after the middle, three times the potential of P6's abstract table, and the walk potential. The
reason is that the record stores and the back do not touch the cells of the tour after the back,
nor those of P5's table. -/
theorem asmFirstInit_post_phi {impl : SparsifyImpl} {w depth L capExp limbMul : ℕ}
    {M k P vCap eCap h o₁ tourH cmpH ctH sH expPtr tblEnd h30 h31 h32 h33 : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    {mem regs : ℕ → ℕ} {st₁ st₂ st₃ st₄ : State}
    {xTour xT' xT'' : (tourAsmRep vCap eCap).τ} {comps : List (Finset ℕ)} {S D : List ℕ}
    {memC : ℕ → ℕ} {specs assigns : List (ℕ × ℕ)} {rList : List ℕ}
    {S5 : Fin eCap → Option BundleState} {m5 : BundleTableMeta eCap}
    {x6 : BucketSpannerMeta depth eCap} {sTour' : OutTourAbs} {yEmb : EmbConc}
    {Ψ : BundleTreeState depth → ℕ} {wp lgFac : ℕ}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH
      xTour cmpH ctH sH comps S D memC st₁)
    (hM : AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
      (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D specs assigns st₁ tourH o₁ rList S5 m5
      tblEnd xT' x6 st₂)
    (hB : AsmFiBackOut (asmFiSP impl w M depth k eCap) tr ord vCap eCap tourH (st₂.regs 29) xT'
      (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
        (List.range D.length)) (List.range D.length) st₂.mem st₂.regs h30 h31 h32 h33 sTour'
      xT'' yEmb st₃)
    (hR : AsmFiRecOut st₃.regs st₃.mem h o₁ st₄.mem) :
    (tourAsmRep vCap eCap).phi tourH xT'' st₄.mem +
      (asmBrSideRep scProgB5 impl w depth L capExp limbMul Ψ).phi o₁
        (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
          D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH
          (o₁ + 16) ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
          (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) wp lgFac)
        st₄.mem =
    (tourAsmRep vCap eCap).phi tourH xT'' st₃.mem +
      ((bunTableHeadroomRep eCap vCap eCap k).phi (st₂.regs 25) m5 st₂.mem +
        320 * (capExp + 1) * lgFac * specPhi (asmFiSP impl w M depth k eCap)
          (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
            (List.range D.length)) + 300 * wp) := by
  -- the layout
  have hT1 := hF.tourH_lo
  have hT2 := hF.tourH_hi
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hcmpE := hF.cmpH_eq
  have hctE := hF.ctH_eq
  have hsHE := hF.sH_eq
  have e20 : st₂.regs 20 = sH + slotListSpace eCap G.m :=
    (hM.regs_lo 20 (by omega)).trans hF.r20
  have e20' : st₁.regs 20 = sH + slotListSpace eCap G.m := hF.r20
  have h25 := hM.r25
  have htl := hM.tbl_lo
  have hte := hM.tblEnd_le
  have h29 := hM.r29_lo
  simp only [ASM_BR_SIZE] at hT1
  -- the record stores keep every cell outside the two records
  have hfr : ∀ a, (h + 16 ≤ a ∧ a < o₁) ∨ o₁ + 16 ≤ a → st₄.mem a = st₃.mem a := by
    intro a ha
    exact hR.frame a (by simp only [ASM_BR_EMB]; omega) (by simp only [ASM_BR_OUT]; omega)
      (by simp only [ASM_BR_REST]; omega) (by simp only [ASM_SD_SIZE]; omega)
  have hTour : (tourAsmRep vCap eCap).phi tourH xT'' st₃.mem =
      (tourAsmRep vCap eCap).phi tourH xT'' st₄.mem :=
    (asmBrTourView_keep tourAsmRep_local ⟨tr, ord, vCap, eCap⟩ (s := sTour')
      (fun c hc => (hfr c (by rcases hM.tour_foot c (hB.tour_foot c hc) with h0 | h0 <;>
        omega)).symm)).2
  have hBun : (bunTableHeadroomRep eCap vCap eCap k).phi (st₂.regs 25) m5 st₂.mem =
      (bunTableHeadroomRep eCap vCap eCap k).phi (st₂.regs 25) m5 st₄.mem := by
    refine ((bunTableHeadroomRep_local eCap vCap eCap k) (st₂.regs 25) S5 m5 st₂.mem st₄.mem
      fun c hc => ?_).2
    have hc' := hM.bun_foot c hc
    rw [hfr c (Or.inr (by omega)), hB.low c (by omega) fun hT => by
      rcases hM.tour_foot c hT with h0 | h0 <;> omega]
  have hSp : bucketPhi (asmFiSP impl w M depth k eCap) x6 =
      specPhi (asmFiSP impl w M depth k eCap)
        (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
          (List.range D.length)) :=
    bucketPhi_eq_specPhi hM.span_rep
  rw [asmBrSideRep_phi, hTour, hBun]
  show _ + (_ + 320 * (capExp + 1) * lgFac * bucketPhi (asmFiSP impl w M depth k eCap) x6 +
      300 * wp) = _
  rw [hSp]
  rfl

/-- **The build of a branch at its init.** If the program holds the body `asmFirstInitBuildBody F`
at `f` and the procedures it calls at their places (the hypotheses of `asmFirstInitBody_runs`),
then it meets `AsmFirstInitBuildAt`, with multiplier `asmFiBuildCostMul capExp limbMul` and space
`asmFiBuildSpacePoly impl.cw Cγ cγ capExp`. The build needs three facts outside its run:
`1 ≤ depth` and `1 ≤ max impl.p_s impl.p_t` (for the start graphs of the bundles), a valid LSF init
for each `j < k` (for the inactive components of the bundle side), and a polynomial bound on the
stretch of `impl` (`hγ`, for the space). -/
noncomputable def asmFirstInitBuildAt_mk {depth P L capExp limbMul wordExp w bT b bSort bSpan
      bExport fExpM fCFRoot bRead bComp fExpD bBack f Cγ cγ : ℕ} {impl : SparsifyImpl}
    {lsfInit : LSFInit} {CFR : DSRep CompFamilyAbs} {p : Program} {RL : ReadLib}
    (F : AsmFirstInitProcs) (hf : p.procs[f]? = some (asmFirstInitBuildBody F))
    -- the procedures of the front
    (hfT : p.procs[F.fTour]? = some (tourBranchInitStmt (tourInit bT)))
    (hpBk : p.HasAt F.fBkt (bucketTableModule F.fBkt))
    (hpC : p.HasAt F.fComp (compMapModule F.fComp))
    (hpS : p.HasAt F.fSlot (slotListModule F.fSlot))
    -- the procedures of the middle
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hfR : p.procs[F.fRoots]? = some (rootsListBody bSort))
    (hpT : HasTourProcs p bT)
    (hpB : p.HasAt b (bundleProcs b (tourOp bT 4) (tourOp bT 12) (tourOp bT 10)))
    (hfB : p.procs[F.fBun]? =
      some (asmFirstInitBunBody (b + bundleIdxTableInit) (b + bundleIdxInitSlots)))
    (hfS : p.procs[F.fSpan]? = some (asmFirstInitSpanBody fExpM (bSpan + bsIdxOp0 + 0)))
    (hfE : p.procs[fExpM]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hpSp : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    -- the procedures of the back
    (hfRT : F.fRootTbl = bBack) (hfS0 : F.fS0 = bBack + 1)
    (hfM : F.fMark = bBack + 7) (hfEm : F.fEmb = bBack + 9)
    (hRL : RL.Has p) (hpRead : p.HasAt bRead (readBranchProcs RL fCFRoot bRead))
    (hpComp : p.HasAt bComp (compMapModule bComp))
    (hfExpD : p.procs[fExpD]? = some asmFirstExportDynGraphStmt)
    (hpBack : p.HasAt bBack (asmFirstInitBackModule RL bRead bSpan bT bComp fExpD bBack))
    -- the facts outside the run
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    AsmFirstInitBuildAt tourAsmRep scProgB5 CFR lsfInit impl depth P L capExp limbMul wordExp w
      walkPot p f where
  mul := asmFiBuildCostMul capExp limbMul
  space := asmFiBuildSpacePoly impl.cw Cγ cγ capExp
  runs := by
    intro cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf mem
      pos ω X tr₀ hk hj hGv _ hGM hGN hnm hPL hcap _ _ hcfs hlen hdg hgraph hord hordh hcWords _
      hexp hexph _ hargs hz hsp hF
    have hk1 : 1 ≤ k := hk
    have hsp' : h + (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval
        (M + N + k + vCap + eCap + L + depth) < 2 ^ w := hsp
    -- the export is that of `tr₀.cs`
    have hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr₀.cs := by
      rw [hcfs] at hexp
      exact hexp
    have hLw := hExp.2.2.2.2.2.2.2.2.1
    -- the words
    obtain ⟨hw10, hw, hMw, hdw, hSPw, hcw2, hBw, hkw⟩ :=
      asmFiBuildSpace_word_bounds (impl := impl) (Cγ := Cγ) (cγ := cγ) (capExp := capExp)
        (w := w) (h := h) (M := M) (N := N) (k := k) (vCap := vCap) (eCap := eCap) (L := L)
        (depth := depth) hk1 hPL hLw hsp'
    have hjW : j < 2 ^ w := hargs j (by simp)
    have hw16 : 16 ≤ 2 ^ w :=
      (show 16 ≤ 2 ^ 10 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) hw10)
    have hcw : (36 * ((asmFiSP impl w M depth k eCap).vCap +
        2 * (asmFiSP impl w M depth k eCap).eCap + 1)) ^ impl.cw < 2 ^ w :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by norm_num)) hcw2
    have hspV : 2 * eCap + bundleSplitBudget k M + 1 < 2 ^ w := by
      have e : (asmFiSP impl w M depth k eCap).vCap = 2 * eCap + bundleSplitBudget k M + 1 := rfl
      omega
    -- the model facts at `tr₀`
    have hScur := scur_size_le_of_facts hF
    have hSn : tr₀.S_cur.n ≤ N := hScur.1.trans hGN
    have hSm : tr₀.S_cur.m ≤ M := hScur.2.trans hGM
    obtain ⟨-, ⟨C₀, ℓ', hI, ρ, hρ⟩, hScurInv, hBD, hScurVal, -, -, hVlt, hElt, -⟩ := id hF
    have hRot : HasRotOrder tr₀ ord := ⟨C₀, ℓ', hI, ρ, hρ⟩
    have hRF := compLSF_RF_isRSF hI
    have hsub : ∀ e ∈ tr₀.cs.lsf.F.F.E, e ∈ tr₀.cs.G.E := fun e he => hRF.2.2.2.2.2.1 he
    have hbktM : ∀ e ∈ G.E, bucketOf (tr₀.cs.lsf.wstr e * ℓ₀ e) = tr₀.origBucket e :=
      fun e he => (initBundleTree_origBucket lsfInit depth _ _ _ k M N G ℓ₀ ord j he).symm
    have hact := mem_activePairs_init lsfInit depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j hRF hGv
    have hGm : G.m ≤ eCap := card_le_of_lt_cap hElt
    have hokAll : ∀ q, SpanGraphOK (asmFiSP impl w M depth k eCap) (tr₀.initBunG q) := fun q =>
      initTree_spanGraphOK (asmFiSP impl w M depth k eCap) lsfInit
        (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl) k M
        N G ℓ₀ ord j hk1 hElt hGM (le_refl _) (le_refl _) hd hp hw16 hSPw hcw q
    have hdyn := initTree_dyn (asmFiSP impl w M depth k eCap) lsfInit
      (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j rfl
    have hSE : tr₀.S_cur.E = (activePairs tr₀).biUnion fun q => (tr₀.dyn q).H.E :=
      (initTree_S_cur_E lsfInit depth _ _ _ k M N G ℓ₀ ord j).trans
        (activePairs_biUnion_H tr₀).symm
    have hGE : ∀ q ∈ activePairs tr₀, (tr₀.dyn q).G.E = (tr₀.bun q).edges := fun q _ =>
      (initTree_dyn_GE_HE (asmFiSP impl w M depth k eCap) lsfInit (canonicalSparsifyParams impl)
        (dsAmortConst impl) k M N G ℓ₀ ord j rfl q (hokAll q)).1
    -- the space of the three parts
    have hspB : ∀ (S5 : Fin eCap → Option BundleState) (n : ℕ), n ≤ eCap →
        (∀ s ∈ List.range n,
          SpanGraphOK (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)) →
        h + asmFiFrontSpace vCap eCap (mem (expPtr + 6)) L +
          asmFiMidSpace (asmFiSP impl w M depth k eCap) vCap eCap +
          asmFiBackSpace (asmFiSP impl w M depth k eCap)
            (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
              (List.range n)) (List.range n) vCap eCap tr₀.S_cur < 2 ^ w := by
      intro S5 n hn hok
      have := asmFiBuildSpace_le_poly (S := tr₀.S_cur) (L := L) (depth := depth) (N := N)
        (k := k) (vCap := vCap) hγ hk1 hLw hSn hSm hn hok
      omega
    -- the run of the body
    obtain ⟨o₁, tourH, xTour, cmpH, ctH, sH, comps, S, D, memC, st₁, hFr, rList, S5, m5, tblEnd,
        xT', x6, st₂, hM, h30, h31, h32, h33, sTour', xT'', yEmb, st₃, hB, st₄, c, -, hR, hrun,
        hc⟩ :=
      asmFirstInitBody_runs (cfH := cfH) (cOrdPtr := cOrdPtr) (cWords := cWords) (graph := graph)
        (lengths := lengths) (j := j) (pos := pos) (P := P) (N := N) F ω hfT hpBk hpC hpS hpSort
        hfR hpT hpB hfB hfS hfE hpExport hpSp hfRT hfS0 hfM hfEm hRL hpRead hpComp hfExpD hpBack
        (tr := tr₀) (G := G) rfl hGv hRot hVlt hElt hk1 hsub hbktM hact (fun _ => rfl) (fun _ => rfl)
        (fun q _ => hokAll q) hdyn hScurInv hScurVal hBD hSE hGE hord hordh hExp hexph hdg hgraph
        hlen hz hw10 hw hBw hkw hMw hdw hjW hspB
    -- the space
    have hDe : D.length ≤ eCap := hFr.slots.D_len.trans (hFr.slots.S_len.trans hGm)
    have hspace := asmFiBuildSpace_le_poly (S := tr₀.S_cur) (L := L) (depth := depth) (N := N)
      (k := k) (vCap := vCap) hγ hk1 hLw hSn hSm hDe hM.span_ok
    have hr20 := hFr.r20_le
    have e20 := hFr.r20
    have h29hi := hM.r29_hi
    have h33s := hB.h33_space
    have ho : h33 ≤ h + (asmFiBuildSpacePoly impl.cw Cγ cγ capExp).eval
        (M + N + k + vCap + eCap + L + depth) := by omega
    -- the model of the bundle side
    obtain ⟨C_lsst, hIV⟩ := hInit k j hj
    have hℓ : ∀ e ∈ G.E, 0 < ℓ₀ e := by
      intro e he
      rw [hlen.2.2]
      exact (hlen.2.1 e he).2.2
    have hnone : ∀ i : Fin eCap, i.1 ∉ List.range D.length → S5 i = none := by
      intro i hi
      rw [hM.S5_eq]
      exact tableAfterInitSlots_none_of_not_mem _ _ _ _ _ (by rw [slotSpecsL_fst]; exact hi)
    have hModel := asmFiSide_model (w := w) (L := L) (capExp := capExp) (limbMul := limbMul)
      (Ψ := walkPot) (bunH := st₂.regs 25) (m5 := m5) (spanH := st₂.regs 26) (x6 := x6)
      (slotsPtr := sH + 2 + eCap + 5 * G.m) (cmpH := cmpH) (bktH := o₁ + 16) (ctH := ctH)
      (comps := comps) (cslPtr := fun c => st₁.mem (ctH + 3 * c + 1))
      (cslL := fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c)
      hF hM.slot_map hM.bun_match hM.bun_inv hnone hokAll hcap hGm hIV hGv hℓ
    -- the post
    have hcode : ∀ e ∈ G.E,
        bucketCode (tr₀.origBucket e) < asmFirstInitKeyBase P (mem (expPtr + 6)) L :=
      fun e he => hbktM e he ▸ asmFi_code_lt hExp rfl hlen e he
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19,
        q20, q21, q22, q23, q24, q25, q26, q27⟩ :=
      asmFirstInit_post hFr hM hB hR rfl rfl rfl hExp rfl rfl hI rfl hGv hVlt hElt hbktM hcode
        hact hBw (by omega) (by omega) hdw hspV hModel
    -- the cost
    have hphi := asmFirstInit_post_phi (Ψ := walkPot) (wp := walkPot tr₀)
      (lgFac := bundleLogFactor M N) (capExp := capExp) (G := G) (limbMul := limbMul) hFr hM hB hR
    have hC := asmFiBuildCost_le hGv hGM hGN hnm hcWords hcap hExp hF hFr.slots.S_len
      hFr.slots.D_len hM.roots_sorted hM.roots_iff hM.slot_map hM.bun_match hM.span_ok
    refine ⟨asmFirstInitBuildBody F, hf, .returned h33, st₄, c,
      asmFiConc vCap eCap (mem (expPtr + 7)) (mem (expPtr + 6)) h32 h30 tourH o₁ yEmb sTour' xT''
        (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
          D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH (o₁ + 16)
          ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
          (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) (walkPot tr₀)
          (bundleLogFactor M N)),
      hrun, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19,
      q20, q21, q22, q23, q24, q25, ho, q26, q27, ?_⟩
    show c + (tourAsmRep vCap eCap).phi tourH xT'' st₄.mem +
        (asmBrSideRep scProgB5 impl w depth L capExp limbMul walkPot).phi o₁
          (asmFiSide k vCap eCap M (st₂.regs 25) S5 m5 (st₂.regs 26) x6 (sH + 2 + eCap + 5 * G.m)
            D.length G.m (slotOfD comps (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D) cmpH
            (o₁ + 16) ctH comps (fun c => st₁.mem (ctH + 3 * c + 1))
            (fun c => cslList D (asmFirstInitKeyBase P (mem (expPtr + 6)) L) c) (walkPot tr₀)
            (bundleLogFactor M N))
          st₄.mem ≤ asmFiBuildCostMul capExp limbMul * tr₀.machCost
    rw [add_assoc, hphi]
    have htr₀ : initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j = tr₀ := rfl
    simp only [htr₀] at hC
    omega

end MinCostFlow.SparseCore.Program
