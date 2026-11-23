module

public import MinCostFlow.MinRatio.InitSolverWordBudget
public import MinCostFlow.MinRatio.InitConcreteLevels
import MinCostFlow.MinRatio.InitDepthLink
import MinCostFlow.Num.ModulePlacement

/-!
# Full certified Init assembly

Composes the fixed-program Init pipeline from the seven-word IPM entry
`[graph, gradient, lengths, limbs, precision, V, heap]` through numeric
parameter computation, packed dynamic graph construction, integer bucket cap,
sparsifier depth and path factors, certified integer rebuild threshold table,
solver header allocation, and all `d` sparse-core levels plus the terminal level
of Algorithm 1 (page 20), under a single uniform `wordSize` multiplier.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- One fixed Init program for all inputs: packs the graph, computes the
integer bucket cap, sparsifier factors, and certified integer threshold table,
allocates the solver header, and runs the level initializer. -/
@[expose] def solverInitFullProgram
    (alpha select quality graphPack threshold b clog lsstConstant
      factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add : ℕ)
    (retry degreeSetup levels inconclusive : Stmt) : Stmt :=
  solverInitWithIntegerBucket alpha select quality graphPack threshold b 4 clog lsstConstant retry
    (initCertifiedThresholdPhase b (b + 1) (b + 6) (b + 3) (b + 2) 4 factorEntry decK thr cDeg
        witnessDen coefficient clog power extend mul shift add retry degreeSetup ;;
      continueSolverInit levels inconclusive)

private theorem solverInitFull_wordMultiplier_split
    {dCursor₁ dL dBucket dm cd factorMult endpointMult c : ℕ}
    (hc : max (max (max dCursor₁ (dL + 9))
        (max (max dCursor₁ (10 + 3 * (cd + 8 * (2 * dm))) + 1) (10 * dBucket)))
      (max factorMult endpointMult) ≤ c) :
    max dCursor₁ (dL + 9) ≤ c ∧
    max dCursor₁ (10 + 3 * (cd + 8 * (2 * dm))) + 1 ≤ c ∧
    10 * dBucket ≤ c ∧
    factorMult ≤ c ∧
    endpointMult ≤ c := by
  have h1 := (le_max_left _ _).trans hc
  have h2 := (le_max_right _ _).trans hc
  have h11 := (le_max_left _ _).trans h1
  have h12 := (le_max_right _ _).trans h1
  exact ⟨h11, (le_max_left _ _).trans h12, (le_max_right _ _).trans h12,
    (le_max_left _ _).trans h2, (le_max_right _ _).trans h2⟩

private theorem table_room_to_header_room {table d m : ℕ}
    (h : table + 3 * (d + 1) + 17 < m) : table + (d + 1) + 17 < m := by omega

private theorem table_room_to_levels_room {table d m : ℕ}
    (h : table + 3 * (d + 1) + 17 < m) :
    table + (d + 1) + 17 + (d + 1) + (d + 1) < m := by omega

private theorem alpha_addr_lt_cursor {heap L d j : ℕ} (hj : j < L) :
    heap + 1 + j < heap + (L + 1) + 6 + d := by omega

private theorem heap_lt_cursor (heap L d : ℕ) :
    heap < heap + (L + 1) + 6 + d := by omega

private theorem lt_heap_to_lt_cursor {x heap L d : ℕ} (hx : x < heap) :
    x < heap + (L + 1) + 6 + d := by omega

private theorem le_heap_to_le_levelTable {u heap L g table d : ℕ}
    (hu : u ≤ heap) (ht : heap + (L + 1) + 6 + g ≤ table) :
    u ≤ table + (d + 1) + 17 := by omega

private theorem lt_heap_to_lt_levelTable {x heap L g table d : ℕ}
    (hx : x < heap) (ht : heap + (L + 1) + 6 + g ≤ table) :
    x < table + (d + 1) + 17 := by omega

private theorem header_chain_addr_lt {table d j : ℕ} (hj : j < 8) :
    table + (d + 1) + 9 + j < table + (d + 1) + 17 := by omega

private theorem header_num_addr_lt {table d j : ℕ} (hj : j < 4) :
    table + (d + 1) + 5 + j < table + (d + 1) + 17 := by omega

private theorem table_entry_lt_levelTable {table d j : ℕ} (hj : j ≤ d) :
    table + j < table + (d + 1) + 17 := by omega

private theorem vec_elem_lt_heap {base e L m heap j : ℕ}
    (he : e < m) (hj : j < L) (hend : base + m * L ≤ heap) :
    base + e * L + j < heap := by
  have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hm
  omega

/-- One uniform `wordSize` multiplier drives the entire Init prefix from the
seven-word IPM entry through certified threshold publication and solver header
allocation, preserving the root graph, input coefficient tables, and alpha block
for level construction. -/
theorem solverInitFullPrefix_runs
    (alpha select quality graphPack threshold b clog lsstConstant
      Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen coefficient
      power extend mul shift add q dh : ℕ)
    (hK : 1 ≤ decK) (hcDeg : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ multiplier, ∀ (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
      {c graph gradient lengths heap pos : ℕ}
      {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
      {qualityExponent qualityCharge : ℕ → ℕ}
      {retry degreeSetup levels inconclusive : Stmt}
      {Post : ℕ → ℕ → State → Prop},
      let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
      let w := wordSize c J.solverWords
      let I := IPM.Machine.solverConnectedAugmented J
      let V := IPM.Machine.solverPenalty J.m
      let G := IPM.namedInstance I
      let k := qualityExponent G.m
      let L := IPM.Machine.ipmQualityLimbs I.m V k
      let P := IPM.Machine.ipmQualityPrecision I.m V k
      let M := max I.m threshold
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) → I.IsValid →
      2 ^ k ≤ (J.n + J.m + 2) ^ q →
      heap ≤ B ^ dh →
      IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w →
      multiplier ≤ c →
      ∀ (hM : 1 ≤ M),
      let C := Chain.concreteChainParams M hM
      let Ψ := IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6
      let den := Expander.maxPhiDenOf decK thr (M ^ 2)
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
      let growth := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
      let epsExp := Num.IPM.alphaExponent I.m V + k + 10
      MeetsContract w p quality (IPM.Machine.solverQualityContract w qualityExponent qualityCharge) →
      MeetsContract w p alpha (Num.IPM.alphaContract w 4) →
      MeetsContract w p select (IPM.Machine.precisionSelectionContract w) →
      MeetsContract w p graphPack
        (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
          ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))) →
      p.HasAt b (initDepthProcedures b 4) →
      p.HasAt clog (Scaling.Machine.clogTwoModule clog) →
      MeetsContract w p factorEntry (initMachinePathFactorsContract w Kγ pathC Kint cw) →
      MeetsContract w p power (initStretchPowerContract w) →
      MeetsContract w p extend (Num.extendCopyContract w 4) →
      MeetsContract w p mul (Num.multiplyContract w 4) →
      MeetsContract w p shift (Num.shiftLeftContract w 4) →
      MeetsContract w p add (Num.addContract w 4) →
      IPM.Machine.GraphAt mem graph G →
      graph + (IPM.Machine.graphWords G).length ≤ heap →
      ZeroFrom mem heap →
      E.L = Expander.chosenL (M ^ 2) →
      (E.P_fn (M ^ 2)).γ_ℓ = growth →
      1 ≤ (E.P_fn (M ^ 2)).K_s →
      (E.P_fn (M ^ 2)).p_s = 1 →
      (E.P_fn (M ^ 2)).K_s = 1 + coefficient / Real.log 2 →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ C.k →
      E.B_fn (M ^ 2) = Chain.concreteBucketCap lsstConstant Ψ C.k C.d (4 * M) →
      (∀ factors,
        factors.regs 22 = M → factors.regs 44 = E.L → factors.regs 47 = E.B_fn (M ^ 2) →
        factors.regs 50 = growth → factors.regs 4 = 1 →
        ∃ capped degCost,
          Runs w p ω degreeSetup factors .normal capped degCost ∧
          capped.regs 48 = E.d_fn (M ^ 2) ∧ capped.mem = factors.mem ∧
          ∀ r ≠ 48, capped.regs r = factors.regs r) →
      (∀ table a header,
        let handle := table + (C.d + 1)
        let levelTable := handle + 17
        header.regs 74 = handle →
        header.regs 77 = levelTable →
        levelTable + (C.d + 1) + (C.d + 1) < 2 ^ w →
        header.regs 83 = table →
        ZeroFrom header.mem levelTable →
        ChainInitParametersAt header.mem handle I.m V C.d C.k Ψ heap k epsExp →
        MinRatioNumericHeaderAt header.mem handle L P
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) →
        (∀ j ≤ C.d, header.mem (table + j) =
            Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
          (header.mem (table + j) : ℝ) ≤
            Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
          Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
            48 * ((header.mem (table + j) : ℝ) + 1)) →
        heap + (L + 1) + 6 + dynGraphSize G.n G.m ≤ table →
        DynGraphAt header.mem (heap + (L + 1) + 6) G.n G.m G →
        header.mem heap = Num.IPM.alphaExponent I.m V →
        Num.Valid header.mem (heap + 1) 4 L →
        Num.fixVal header.mem (heap + 1) 4 L P = Num.IPM.alphaPrime I.m V / 8 →
        (∀ x < heap, header.mem x = mem x) →
        header.regs 67 = L → header.regs 68 = P →
        header.regs 69 = heap + (L + 1) + 6 → header.regs 70 = gradient →
        header.regs 71 = lengths → header.regs 75 = C.d →
        ∃ out cost, Runs w p ω levels header .normal out cost ∧ Post table a out) →
      ∃ out cost table a, Runs w p ω
        (solverInitFullProgram alpha select quality graphPack threshold b clog lsstConstant
          factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add
          retry degreeSetup levels inconclusive)
        (startState [graph, gradient, lengths, L, P, V, heap] mem pos) .normal out cost ∧
        Post table a out := by
  let dL := max 41 q + 7
  let dCursor₁ := max (max dh dL) 2 + 5
  let dm := max 2 (Nat.clog 2 threshold + 1)
  let cd := Nat.clog 2 (4 * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  let dBucket := max (max (dm + 2) (dL + 1)) (Nat.clog 2 (6272 * max 1 lsstConstant))
  let dCursor₂ := max dCursor₁ (10 + 3 * (cd + 8 * dm)) + 1
  let dCursor₃ := max dCursor₂ (10 + 3 * (cd + 8 * (2 * dm))) + 1 + 3
  obtain ⟨factorMult, hfactors⟩ :=
    prepareCertifiedSparsifierFactors_uniform_runs threshold 4 b Kγ pathC Kint cw factorEntry
      decK thr cDeg witnessDen dCursor₂ hK hcDeg hWitness
  let endpointMult := certifiedEndpointMultiplier threshold coefficient 4 dCursor₃
  refine ⟨max (max (max dCursor₁ (dL + 9))
      (max (max dCursor₁ (10 + 3 * (cd + 8 * (2 * dm))) + 1) (10 * dBucket)))
    (max factorMult endpointMult), ?_⟩
  intro J E c graph gradient lengths heap pos p ω mem qualityExponent qualityCharge
    retry degreeSetup levels inconclusive Post B w I V G k L P M
    hJn hJm hcap hIvalid hk hheapPow hqw hcmult hM C Ψ den cap growth epsExp
    hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
    hGraph hGraphBelow hz hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree hLevels
  have hGm : G.m = I.m := IPM.namedInstance_m I
  have hB : 2 ≤ B := Nat.le_add_left 2 _
  have hB1 : 1 ≤ B := le_trans (by decide : 1 ≤ 2) hB
  obtain ⟨hcIn, hcChain, hcBucket, hcFact, hcEnd⟩ := solverInitFull_wordMultiplier_split hcmult
  obtain ⟨hsize, hcover, hwidth, hparamW, hGmW, hVW, hLW, hPW, hscaleW, hpsiW, hepsW,
      hw16, hw14, hCursor₁Pow, hCursor₁W, _, hPsiPow, hDetectW⟩ :=
    initThresholdInputs_wordSize_bounds J hJn hJm hcap hk hheapPow hqw hcIn le_rfl
  obtain ⟨hGvalid, hGvc, hGec⟩ := initNamedInstance_valid_caps I hIvalid
  have hgraphW : graph + 1 < 2 ^ w := by
    have hgw : 1 ≤ (IPM.Machine.graphWords G).length := by
      unfold IPM.Machine.graphWords; simp
    have h1 : graph + 1 ≤ heap := (Nat.add_le_add_left hgw graph).trans hGraphBelow
    exact lt_of_le_of_lt (h1.trans (Nat.le_of_lt (heap_lt_cursor heap L (dynGraphSize G.n G.m))))
      hCursor₁W
  have hroomW : heap + (L + 1) + 6 < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right _ _) hCursor₁W
  obtain ⟨ready, inputCost, hInput, hr0, hr1, hr2, hr3, hr4, hr6, hr7, hr69, hr70, hr71,
      hr72, hr73, _, hr67, hr68, hr98, hr92, _, _, hGdg, hframeReady, hzReady,
      hAlphaExp, hAlphaVal, hAlphaFix, _⟩ :=
    prepareMinRatioSolverThresholdInputs_runs (h := 4) (ω := ω) (pos := pos)
      hqual halpha hselect hGraph hgraphW hGmW hVW hLW hPW hsize hcover hwidth hscaleW hparamW
      hpsiW hz hroomW hepsW hpack hGvalid hGvc hGec hGraphBelow hw16 hCursor₁W
  have hPsiG :
      IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 = Ψ := by
    change IPM.Machine.ipmQualityRangeExponent G.m V k +
      IPM.Machine.slackRangeExponent G.m V + 6 =
      IPM.Machine.ipmQualityRangeExponent I.m V k +
      IPM.Machine.slackRangeExponent I.m V + 6
    rw [hGm]
  have hEpsG : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 = epsExp := by
    change Num.IPM.alphaExponent G.m V + k + 10 = Num.IPM.alphaExponent I.m V + k + 10
    rw [hGm]
  have hpsiBG :
      IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ≤ B ^ dBucket :=
    hPsiPow.trans (Nat.pow_le_pow_right hB1 ((le_max_right _ _).trans (le_max_left _ _)))
  have hconstB : 6272 * max 1 lsstConstant ≤ B ^ dBucket :=
    ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_left hB _)).trans
      (Nat.pow_le_pow_right hB1 (le_max_right _ _))
  have hzReady7 : ZeroFrom ready.mem (heap + (L + 1) + 6 + dynGraphSize G.n G.m) := by
    rw [← hr7]; exact hzReady
  obtain ⟨bucket, bucketCost, ret₁, hBucket, hb47, hb14, hb18, hb99, hb22, hb75, hb76, hb92,
      hb4, hb6, hb98, hb101, hb102, hb103, hb104, hret₁Lo, _, hret₁Space, hzBucket,
      hframeBucket, hregsBucket, _, _⟩ :=
    prepareLinkedIntegerBucket_runs (threshold := threshold) (b := b) (h := 4)
      (a := heap + (L + 1) + 6 + dynGraphSize G.n G.m) (cursorDegree := dCursor₁)
      (c := c) (clog := clog) (lsstConstant := lsstConstant) (bucketDegree := dBucket)
      (retry := retry) J hw14 hdepthProc (by decide) hr0 (hr98.trans hr7) hzReady7 hM
      hr4 hr1 hr2 hr3 hr6 hr92 hclog hCursor₁Pow hcChain
      ((le_max_left _ _).trans (le_max_left _ _)) hcBucket hpsiBG hconstB
  have hret₁Pow : ret₁ ≤ B ^ dCursor₂ :=
    initBucketCursor_power_bound J hCursor₁Pow hret₁Space
  obtain ⟨depthState, factors, depthCost, factorCost, ret₂, hDepthRun, hFactorRun,
      hf44, hf4, hf98, hret₂Lo, hzFact, hret₂Space, hf50, _, _, _, _, hfPos,
      hregsFact, hargsFact, hframeFact⟩ :=
    hfactors J hw14 hdepthProc hfactorImpl hb22 hM (by decide) hb99 hzBucket hb18 hb4
      hret₁Pow hcFact
  have hf47 : factors.regs 47 = E.B_fn (M ^ 2) := by
    rw [hregsFact 47 (by decide) (by decide), hb47, hPsiG, ← hBfn]
  have hf22 : factors.regs 22 = M := (hregsFact 22 (by decide) (by decide)).trans hb22
  obtain ⟨capped, degCost, hDegRun, hc48, hcMem, hcRegs⟩ :=
    hDegree factors hf22 (hf44.trans hEL.symm) hf47 hf50 hf4
  have hcKeep (r : ℕ) (hr : r ≠ 48 := by decide) : capped.regs r = factors.regs r := hcRegs r hr
  have hfKeep (r : ℕ) (hr : r < 98)
      (h1 : r ∉ ([23, 24, 31, 32, 33, 36, 44, 50, 52, 58, 63] : List ℕ))
      (h2 : r ∉ ([4, 14, 15, 16, 17, 18, 22, 46, 47, 57, 75, 76] : List ℕ)) :
      factors.regs r = ready.regs r :=
    (hregsFact r hr h1).trans (hregsBucket r hr h2)
  have hret₂Pow : ret₂ + 4 ≤ B ^ dCursor₃ :=
    certifiedEndpointCursor_power_bound J hCursor₁Pow hret₁Space hret₂Space
  obtain ⟨hbits, hload, hround, _, _⟩ := initDepthProcedures_meetsContracts (by decide) hw14 hdepthProc
  have hpackW := initDepthProcedures_packer_meetsContract (by decide) hw14 hdepthProc
  have hLogMod : p.HasAt (b + 6) (Num.logarithmModule (b + 6) 4) := by
    unfold initDepthProcedures at hdepthProc
    exact Num.hasAt_append_right hdepthProc
  obtain ⟨checked, threshCost, table, a, hThreshRun, hch10, hch83, hch99, htableLo, htableRoom,
      hzChecked, hentries, hframeChecked, hch0, hch6, hch67, hch68, _, hchRegs⟩ :=
    initCertifiedThresholdsWithWorkspace_budgeted_runs J E (threshold := threshold) (h := 4)
      (c := c) (dhEnd := dCursor₃) (power := power) (bits := b) (load := b + 1) (log := b + 6)
      (pack := b + 3) (clog := clog) (coefficient := coefficient) (extend := extend) (mul := mul)
      (shift := shift) (add := add) (roundEntry := b + 2)
      hM hpower hbits hload hpackW hext hmul hshift hadd hround hclog hLogMod hw14 (by decide)
      ((hcKeep 22).trans hf22)
      ((hcKeep 92).trans ((hfKeep 92 (by decide) (by decide) (by decide)).trans hr92))
      ((hcKeep 75).trans ((hregsFact 75 (by decide) (by decide)).trans hb75))
      ((hcKeep 76).trans ((hregsFact 76 (by decide) (by decide)).trans hb76))
      ((hcKeep 44).trans (hf44.trans hEL.symm))
      ((hcKeep 50).trans hf50) ((hcKeep 4).trans hf4)
      hfPos hGrowth hK1 hps1 hCoeff hγM hγk
      ((hcKeep 47).trans hf47) hc48
      ((hcKeep 14).trans ((hregsFact 14 (by decide) (by decide)).trans hb14))
      (by rw [hcMem, hcKeep 98, hf98]; exact hzFact)
      (by rw [hcKeep 98, hf98]; exact hret₂Pow) hcEnd
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 16) hw16
  have hPhase := initCertifiedThresholdPhase_runs (retry := retry) (degreeSetup := degreeSetup)
    hb18 hb99 hw1 hDepthRun hFactorRun hDegRun hThreshRun
  have hchR (r : ℕ) (hr : r ∈ ([69, 70, 71, 72, 73, 75, 76, 101, 102, 103, 104] : List ℕ)) :
      checked.regs r = capped.regs r := hchRegs r hr
  have hc98eq : capped.regs 98 = ret₂ + 4 := (hcKeep 98).trans hf98
  have htableLo' : ret₂ ≤ table := (Nat.le_add_right ret₂ 4).trans (by rw [← hc98eq]; exact htableLo)
  have htableGeA1 : heap + (L + 1) + 6 + dynGraphSize G.n G.m ≤ table :=
    hret₁Lo.trans (hret₂Lo.trans htableLo')
  have hcheckedFrameA1 (x : ℕ) (hx : x < heap + (L + 1) + 6 + dynGraphSize G.n G.m) :
      checked.mem x = ready.mem x := by
    have hx1 : x < capped.regs 98 := by
      rw [hc98eq]
      exact lt_of_lt_of_le hx (hret₁Lo.trans (hret₂Lo.trans (Nat.le_add_right _ _)))
    exact (hframeChecked x hx1).trans ((congrFun hcMem x).trans
      ((hframeFact x (lt_of_lt_of_le hx hret₁Lo)).trans (hframeBucket x hx)))
  obtain ⟨header, hrHeader, h74, h77, hchainH, hnumH, hframeHeader, hzHeader, hregsHeader, htableHeader⟩ :=
    allocateSolverInitHeader_runs (p := p) (ω := ω) hch99
      ((hchR 101 (by decide)).trans ((hcKeep 101).trans ((hargsFact 101 (by decide) (by decide)).trans hb101)))
      (hch0.trans ((hcKeep 0).trans ((hfKeep 0 (by decide) (by decide) (by decide)).trans (hr0.trans hGm))))
      ((hchR 102 (by decide)).trans ((hcKeep 102).trans ((hargsFact 102 (by decide) (by decide)).trans hb102)))
      ((hchR 75 (by decide)).trans ((hcKeep 75).trans ((hregsFact 75 (by decide) (by decide)).trans hb75)))
      ((hchR 76 (by decide)).trans ((hcKeep 76).trans ((hregsFact 76 (by decide) (by decide)).trans hb76)))
      (hch6.trans ((hcKeep 6).trans ((hfKeep 6 (by decide) (by decide) (by decide)).trans (hr6.trans hPsiG))))
      ((hchR 72 (by decide)).trans ((hcKeep 72).trans ((hfKeep 72 (by decide) (by decide) (by decide)).trans hr72)))
      ((hchR 73 (by decide)).trans ((hcKeep 73).trans ((hfKeep 73 (by decide) (by decide) (by decide)).trans (hr73.trans hEpsG))))
      ((hchR 103 (by decide)).trans ((hcKeep 103).trans ((hargsFact 103 (by decide) (by decide)).trans hb103)))
      ((hchR 104 (by decide)).trans ((hcKeep 104).trans ((hargsFact 104 (by decide) (by decide)).trans hb104)))
      hDetectW hzChecked (table_room_to_header_room htableRoom)
  have hkeepA1 (x : ℕ) (hx : x < heap + (L + 1) + 6 + dynGraphSize G.n G.m) :
      header.mem x = ready.mem x :=
    (hframeHeader x (lt_of_lt_of_le hx
      (htableGeA1.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))).trans
      (hcheckedFrameA1 x hx)
  have hGdgH : DynGraphAt header.mem (heap + (L + 1) + 6) G.n G.m G :=
    hGdg.of_agree (fun x _ hx => hkeepA1 x hx)
  have hAlphaValH : Num.Valid header.mem (heap + 1) 4 L := by
    intro j hj
    rw [hkeepA1 (heap + 1 + j) (alpha_addr_lt_cursor hj)]
    exact hAlphaVal j hj
  have hAlphaFixH : Num.fixVal header.mem (heap + 1) 4 L P = Num.IPM.alphaPrime I.m V / 8 := by
    have hfixEq : Num.fixVal header.mem (heap + 1) 4 L P = Num.fixVal ready.mem (heap + 1) 4 L P := by
      unfold Num.fixVal
      rw [Num.intVal_congr (fun j hj => hkeepA1 (heap + 1 + j) (alpha_addr_lt_cursor hj))]
    rw [hfixEq]
    have hAlphaFix' : Num.fixVal ready.mem (heap + 1) 4 L P = Num.IPM.alphaPrime G.m V / 8 := hAlphaFix
    rw [hAlphaFix', hGm]
  have hAlphaExpH : header.mem heap = Num.IPM.alphaExponent I.m V := by
    rw [hkeepA1 heap (heap_lt_cursor heap L (dynGraphSize G.n G.m)), hAlphaExp, hGm]
  have h83H : header.regs 83 = table :=
    (hregsHeader 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hch83
  have hregsH (r : ℕ) (hr : r ∈ ([67, 68, 69, 70, 71, 75] : List ℕ)) :
      header.regs r = checked.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hregsHeader <;> decide
  obtain ⟨out, levelCost, hLevRun, hPost⟩ :=
    hLevels table a header h74 h77 (table_room_to_levels_room htableRoom) h83H hzHeader hchainH hnumH
      (fun j hj => by
        have htj : header.mem (table + j) = checked.mem (table + j) :=
          hframeHeader _ (lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hj) table)
            (Nat.le_add_right _ _))
        have hej := hentries j hj
        refine ⟨htj.trans hej.1, ?_, ?_⟩
        · rw [htj]; exact hej.2.1
        · rw [htj]; exact hej.2.2)
      htableGeA1 hGdgH hAlphaExpH hAlphaValH hAlphaFixH
      (fun x hx => (hkeepA1 x (lt_heap_to_lt_cursor hx)).trans (hframeReady x hx))
      ((hregsH 67 (by decide)).trans (hch67.trans ((hcKeep 67).trans ((hfKeep 67 (by decide) (by decide) (by decide)).trans hr67))))
      ((hregsH 68 (by decide)).trans (hch68.trans ((hcKeep 68).trans ((hfKeep 68 (by decide) (by decide) (by decide)).trans hr68))))
      ((hregsH 69 (by decide)).trans ((hchR 69 (by decide)).trans ((hcKeep 69).trans ((hfKeep 69 (by decide) (by decide) (by decide)).trans hr69))))
      ((hregsH 70 (by decide)).trans ((hchR 70 (by decide)).trans ((hcKeep 70).trans ((hfKeep 70 (by decide) (by decide) (by decide)).trans hr70))))
      ((hregsH 71 (by decide)).trans ((hchR 71 (by decide)).trans ((hcKeep 71).trans ((hfKeep 71 (by decide) (by decide) (by decide)).trans hr71))))
      ((hregsH 75 (by decide)).trans ((hchR 75 (by decide)).trans ((hcKeep 75).trans ((hregsFact 75 (by decide) (by decide)).trans hb75))))
  have hCont := continueSolverInit_certified_runs (inconclusive := inconclusive) hch10 hw1 hrHeader hLevRun
  exact ⟨out, _, table, a, solverInitWithIntegerBucket_runs hInput hBucket
    (runs_seq_iff.mpr (Or.inr ⟨checked, _, _, hPhase, hCont, rfl⟩)), hPost⟩

/-- End-to-end concrete Init run for `sparseCoreRestartTool` and
`fixedPointLastLevelTool`: from the seven-word IPM entry, constructs the
certified integer threshold table, allocates the solver header, builds all `C.d`
sparse cores and the terminal collection matching `algorithm1_initialize`, and
preserves the header, threshold table, alpha block, and caller memory below `heap`. -/
theorem solverInitFullProgram_fixedPoint_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (scDepth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (alpha select quality graphPack threshold b clog lsstConstant
      Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen coefficient
      power extend mul shift add init copy sort entry terminalInit : ℕ)
    (op lastOp : ℕ → ℕ) (q dh : ℕ)
    (hK : 1 ≤ decK) (hcDeg : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ multiplier, ∀ (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
      {R : DSRep (sparseCoreRestartTool oracle C_lsst scDepth sparsify).State}
      {terminal : DSRep (ℕ × (ℕ → LSF))}
      {costs : SparseCoreMachineCosts}
      {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
      {lastMult stretchPrecision : ℕ}
      {Mcap Ncap scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
      {c graph gradient lengths heap pos : ℕ}
      {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
      {qualityExponent qualityCharge : ℕ → ℕ}
      {retry degreeSetup inconclusive : Stmt},
      let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
      let w := wordSize c J.solverWords
      let I := IPM.Machine.solverConnectedAugmented J
      let V := IPM.Machine.solverPenalty J.m
      let G := IPM.namedInstance I
      let k := qualityExponent G.m
      let L := IPM.Machine.ipmQualityLimbs I.m V k
      let P := IPM.Machine.ipmQualityPrecision I.m V k
      let M := max I.m threshold
      let T := sparseCoreRestartTool oracle C_lsst scDepth sparsify
      let lastTool := LastLevelProgram.fixedPointLastLevelTool oracle C_lsst
      let len₀ := IPM.Machine.readVector mem lengths 4 L P I.m
      let grad₀ := IPM.Machine.readVector mem gradient 4 L P I.m
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) → I.IsValid →
      2 ^ k ≤ (J.n + J.m + 2) ^ q →
      heap ≤ B ^ dh →
      ∀ (hqw : IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w),
      multiplier ≤ c →
      ∀ (hM : 1 ≤ M),
      let fmt := (IPM.Machine.ipmQualityMinRatioFormat I.m V k hqw).fmt
      let C := Chain.concreteChainParams M hM
      let chain := (algorithm1_initialize T lastTool C Mcap (Ncap 0) G len₀ grad₀).1
      let Ψ := IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6
      let den := Expander.maxPhiDenOf decK thr (M ^ 2)
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
      let growth := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
      let epsExp := Num.IPM.alphaExponent I.m V + k + 10
      MeetsContract w p quality (IPM.Machine.solverQualityContract w qualityExponent qualityCharge) →
      MeetsContract w p alpha (Num.IPM.alphaContract w 4) →
      MeetsContract w p select (IPM.Machine.precisionSelectionContract w) →
      MeetsContract w p graphPack
        (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
          ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))) →
      p.HasAt b (initDepthProcedures b 4) →
      p.HasAt clog (Scaling.Machine.clogTwoModule clog) →
      MeetsContract w p factorEntry (initMachinePathFactorsContract w Kγ pathC Kint cw) →
      MeetsContract w p power (initStretchPowerContract w) →
      MeetsContract w p extend (Num.extendCopyContract w 4) →
      MeetsContract w p mul (Num.multiplyContract w 4) →
      MeetsContract w p shift (Num.shiftLeftContract w 4) →
      MeetsContract w p add (Num.addContract w 4) →
      MeetsContract w p copy (copyWordsContract w) →
      MeetsContract w p sort (Expander.heapSortContract w) →
      (∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w 4 x y z)) →
      IPM.Machine.GraphAt mem graph G →
      graph + (IPM.Machine.graphWords G).length ≤ heap →
      lengths + G.m * L ≤ heap → gradient + G.m * L ≤ heap →
      (∀ e < I.m, Num.Valid mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L) →
      ZeroFrom mem heap →
      E.L = Expander.chosenL (M ^ 2) →
      (E.P_fn (M ^ 2)).γ_ℓ = growth →
      1 ≤ (E.P_fn (M ^ 2)).K_s →
      (E.P_fn (M ^ 2)).p_s = 1 →
      (E.P_fn (M ^ 2)).K_s = 1 + coefficient / Real.log 2 →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ C.k →
      E.B_fn (M ^ 2) = Chain.concreteBucketCap lsstConstant Ψ C.k C.d (4 * M) →
      (∀ factors,
        factors.regs 22 = M → factors.regs 44 = E.L → factors.regs 47 = E.B_fn (M ^ 2) →
        factors.regs 50 = growth → factors.regs 4 = 1 →
        ∃ capped degCost,
          Runs w p ω degreeSetup factors .normal capped degCost ∧
          capped.regs 48 = E.d_fn (M ^ 2) ∧ capped.mem = factors.mem ∧
          ∀ r ≠ 48, capped.regs r = factors.regs r) →
      R.Local →
      C.d < 2 ^ w → C.k < 2 ^ w →
      (∀ i, i < C.d → Ncap i = Ncap 0) →
      (chain.G C.d).IsValid →
      (∀ i, i < C.d → ∀ vc ec,
        R.Implements w p init op
          (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (allocation i))) →
      (∀ vc ec,
        terminal.Implements w p terminalInit lastOp
          (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vc ec
            lastMult stretchPrecision lastAllocation)) →
      (∀ i, i < C.d →
        let Gi := chain.G i
        let Hi := chain.G (i + 1)
        let leni := chain.toTreeChain.chainLen len₀ i
        let gradi := chain.toTreeChain.chainGrad grad₀ i
        let forest := T.lsfs (chain.scState i) 0
        Gi.m ≤ Mcap i ∧ Gi.n ≤ Ncap i ∧ (∀ e ∈ Gi.E, 0 < leni e) ∧
        forest.T.IsForest ∧ forest.T.E ⊆ Gi.E ∧ Gi.V ⊆ forest.T.V ∧ Hi.E ⊆ Gi.E ∧
        2 * forest.T.n + 2 < 2 ^ w ∧
        P + scanExponent i + 2 ≤ 4 * L ∧
        0 ≤ gradientBound i ∧ (∀ e ∈ Gi.E, |gradi e| ≤ gradientBound i) ∧
        (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
      (∀ (ω' : ℕ → Bool) levelTable i, i < C.d → ∀ vc ec before,
        let Gi := chain.G i
        let Hi := chain.G (i + 1)
        let leni := chain.toTreeChain.chainLen len₀ i
        let forest := T.lsfs (chain.scState i) 0
        RebuildSuffixAt R chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 i vc ec
          4 L P before →
        InitLevelTablesSeparated levelTable C.d (before.regs 6) vc ec (before.regs 8) L →
        levelTable + (C.d + 1) + (C.d + 1) ≤ before.regs 4 →
        before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
        ∀ args,
          Runs w p ω' prepareRebuildGraphArgs
            { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
            .normal args 36 →
          (∀ mid top v e cost,
            Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
            mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e Hi →
            mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
          (∀ mid c fv fe,
            Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
            LSFAt mid.mem (mid.regs 9) fv fe 4 L P Gi.E forest →
            EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1)) 4 L P Gi.E leni) ∧
          (∀ s v e fv fe c,
            Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
            DynGraphAt s.mem (s.regs 6) v e Hi →
            LSFAt s.mem (s.regs 9) fv fe 4 L P Gi.E forest →
            dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
            s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
            s.regs 7 + e * L ≤ s.regs 5 ∧ e ≤ ec ∧
            s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
            s.regs 5 + forest.T.n + fv * L + L + fv + fv +
              3 * L * forest.T.vol forest.T.V + ec * L + 3 * L * Hi.m < 2 ^ w)) →
      (∀ e ∈ (chain.G C.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
        lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen len₀ C.d) e <
          Num.capacity 4 L) →
      (∀ e ∈ (chain.G C.d).E, 0 < chain.toTreeChain.chainLen len₀ C.d e) →
      (∀ levelTable vc ec before,
        RebuildSuffixAt R chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 C.d vc ec
          4 L P before →
        before.regs 4 + lastAllocation 1 [before.regs 6, before.regs 7, L, P, before.regs 4] < 2 ^ w) →
      ∃ out cost table a,
        let handle := table + (C.d + 1)
        let levelTable := handle + 17
        Runs w p ω
          (solverInitFullProgram alpha select quality graphPack threshold b clog lsstConstant
            factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add
            retry degreeSetup
            (buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit) inconclusive)
          (startState [graph, gradient, lengths, L, P, V, heap] mem pos) .normal out cost ∧
        ChainInitParametersAt out.mem handle I.m V C.d C.k Ψ heap k epsExp ∧
        MinRatioNumericHeaderAt out.mem handle L P
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        (∀ j ≤ C.d, out.mem (table + j) =
            Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
          (out.mem (table + j) : ℝ) ≤
            Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
          Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
            48 * ((out.mem (table + j) : ℝ) + 1)) ∧
        RebuiltCoresAt R chain out.mem levelTable (levelTable + (C.d + 1)) 0 C.d (out.regs 4) ∧
        out.mem (levelTable + (C.d + 1) + C.d) = chain.lastBran ∧
        ZeroFrom out.mem (out.regs 4) ∧
        (∃ y : terminal.τ, terminal.rep (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs)
          y out.mem ∧ ∀ addr, terminal.foot (out.mem (levelTable + C.d)) y addr → addr < out.regs 4) ∧
        (∀ x < heap, out.mem x = mem x) := by
  obtain ⟨mult, hprefix⟩ :=
    solverInitFullPrefix_runs alpha select quality graphPack threshold b clog lsstConstant
      Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen coefficient
      power extend mul shift add q dh hK hcDeg hWitness
  refine ⟨mult, ?_⟩
  intro J E R terminal costs allocation lastAllocation lastMult stretchPrecision
    Mcap Ncap scanExponent nextGraphSizeCap gradientBound c graph gradient lengths heap pos
    p ω mem qualityExponent qualityCharge retry degreeSetup inconclusive
    B w I V G k L P M T lastTool len₀ grad₀
    hJn hJm hcap hIvalid hk hheapPow hqw hcmult hM fmt C chain Ψ den cap growth epsExp
    hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
    hcopy hsort hentry hGraph hGraphBelow hLenEnd hGradEnd hVecValid hz
    hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree hlocal hdW hkW hNconst hValidLast
    hcoreImpl htermImpl hmodel hreadout hstretch hposLast hspaceLast
  have hfit := IPM.Machine.ipm_quality_parameter_words_fit I.m V k hqw
  have hw9 : 9 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 9 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hfit.1)
  have hWidth4 : P ≤ 4 * L := by
    dsimp only [L, P, IPM.Machine.ipmQualityLimbs]
    omega
  have hGm : G.m = I.m := IPM.namedInstance_m I
  have hLenMem : EdgeValuesAt mem lengths 4 L P G.E len₀ := by
    intro e he
    have he' : e < I.m := Finset.mem_range.mp he
    refine ⟨(hVecValid e he').1, ?_⟩
    dsimp only [len₀, IPM.Machine.readVector]
    simp only [he', ↓reduceIte]
  have hGradMem : EdgeValuesAt mem gradient 4 L P G.E grad₀ := by
    intro e he
    have he' : e < I.m := Finset.mem_range.mp he
    refine ⟨(hVecValid e he').2, ?_⟩
    dsimp only [grad₀, IPM.Machine.readVector]
    simp only [he', ↓reduceIte]
  let Post (table a : ℕ) (out : State) : Prop :=
    let handle := table + (C.d + 1)
    let levelTable := handle + 17
    ChainInitParametersAt out.mem handle I.m V C.d C.k
      (IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6)
      heap k (Num.IPM.alphaExponent I.m V + k + 10) ∧
    MinRatioNumericHeaderAt out.mem handle L P
      (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
    (∀ j ≤ C.d, out.mem (table + j) =
        Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
      (out.mem (table + j) : ℝ) ≤
        Chain.SparseCoreTool.updateThreshold C.k
          (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
      Chain.SparseCoreTool.updateThreshold C.k
          (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
        48 * ((out.mem (table + j) : ℝ) + 1)) ∧
    RebuiltCoresAt R chain out.mem levelTable (levelTable + (C.d + 1)) 0 C.d (out.regs 4) ∧
    out.mem (levelTable + (C.d + 1) + C.d) = chain.lastBran ∧
    ZeroFrom out.mem (out.regs 4) ∧
    (∃ y : terminal.τ, terminal.rep (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs)
      y out.mem ∧ ∀ addr, terminal.foot (out.mem (levelTable + C.d)) y addr → addr < out.regs 4) ∧
    (∀ x < heap, out.mem x = mem x)
  obtain ⟨out, cost, table, a, hrun, hpost⟩ :=
    hprefix J E (Post := Post) hJn hJm hcap hIvalid hk hheapPow hqw hcmult hM
      hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
      hGraph hGraphBelow hz hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree
      (levels := buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit)
      (inconclusive := inconclusive)
      (fun table a header h74 h77 hroomH h83H hzH hchainH hnumH htableH htableGe hGdgH
          _ _ _ hframeH h67H h68H h69H h70H h71H h75H => by
        have hLenH : EdgeValuesAt header.mem lengths 4 L P G.E len₀ :=
          hLenMem.congr (fun e he j hj =>
            hframeH _ (vec_elem_lt_heap (hGm ▸ Finset.mem_range.mp he) hj hLenEnd))
        have hGradH : EdgeValuesAt header.mem gradient 4 L P G.E grad₀ :=
          hGradMem.congr (fun e he j hj =>
            hframeH _ (vec_elem_lt_heap (hGm ▸ Finset.mem_range.mp he) hj hGradEnd))
        obtain ⟨out, cost, hr, hcores, hbr, hzero, _, ⟨yT, hyT, hfootT⟩, hframeL, _⟩ :=
          buildSolverInitLevels_fixedPoint_runs (fmt := fmt) (ω := ω)
            oracle C_lsst scDepth sparsify (P := C) (R := R) (terminal := terminal)
            G len₀ grad₀ h77 h69H h71H h70H h75H h67H h68H hzH hroomH
            hGdgH hLenH hGradH
            (htableGe.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
            (le_heap_to_le_levelTable hLenEnd htableGe)
            (le_heap_to_le_levelTable hGradEnd htableGe)
            hfit.2.1 hfit.2.2.1 rfl hWidth4 hdW hkW hw9 hlocal hcopy hsort hentry
            hNconst hValidLast hcoreImpl htermImpl hmodel (fun ω' => hreadout ω' (table + (C.d + 1) + 17))
            hstretch hposLast (hspaceLast (table + (C.d + 1) + 17))
        refine ⟨out, cost, hr, ?_, ?_, ?_, hcores, hbr, hzero,
          ⟨yT, hyT, fun addr ha => (hfootT addr ha).2⟩,
          fun x hx => (hframeL x (lt_heap_to_lt_levelTable hx htableGe)).trans (hframeH x hx)⟩
        · intro j hj
          have hj8 : j < 8 := by simpa [List.length] using hj
          have hmemj : out.mem (table + (C.d + 1) + 9 + j) = header.mem (table + (C.d + 1) + 9 + j) :=
            hframeL _ (header_chain_addr_lt hj8)
          rw [hmemj]
          exact hchainH j hj
        · intro j hj
          have hj4 : j < 4 := by simpa [List.length] using hj
          have hmemj : out.mem (table + (C.d + 1) + 5 + j) = header.mem (table + (C.d + 1) + 5 + j) :=
            hframeL _ (header_num_addr_lt hj4)
          rw [hmemj]
          exact hnumH j hj
        · intro j hj
          have hmemj : out.mem (table + j) = header.mem (table + j) :=
            hframeL _ (table_entry_lt_levelTable hj)
          rw [hmemj]
          exact htableH j hj)
  exact ⟨out, cost, table, a, hrun, hpost⟩

end MinCostFlow.MinRatio
