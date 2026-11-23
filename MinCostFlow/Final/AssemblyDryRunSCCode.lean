module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.Final.AssemblyDryRunSCStretch
public import MinCostFlow.SparseCore.Program.AssemblyCodeCarry

/-!
# Single combined sparse-core `SparseCoreCode` for the dry run (`AssemblyDryRunSCCode`)

Wraps the single combined deterministic sparse-core program `scProg` (`AssemblyCode.lean`) into
`SparseCoreCode` (`scSparseCoreCode`, `drySparseCoreCode`) and exports all carried piece facts
(determinism, `HasAsmTopProcs`, `HasAsmBrProcs`, standalone P4 lifting, P2/P5/P6/P7/P10 placement
and contracts, and the uniform bridged top-layer theorem) specialized to `sparsifyImplUsed`,
`dryLSFInitUsed`, and `dryCLsstUsed`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.Bundle SparseCore SparseCore.Program DynSpanner.Program MinRatio
open SparseCore.Program.Restart SparseCore.Program.Read

/-! ## Single combined `SparseCoreCode` -/

/-- The single combined `SparseCoreCode` built from `scProg impl cf firstStep firstInit`, with
`init := asmTopInitIdx L.bTop` and `op := asmTopOpIdx L.bTop`. -/
def scSparseCoreCode (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) : SparseCoreCode where
  prog := scProg impl cf firstStep firstInit
  init := asmTopInitIdx (scLayout impl cf firstStep firstInit).bTop
  op := asmTopOpIdx (scLayout impl cf firstStep firstInit).bTop

/-- The single combined `SparseCoreCode` instantiated on `sparsifyImplUsed` for the dry run. -/
def drySparseCoreCode (cf : ScCompCode) (firstStep firstInit : ScSubCode) : SparseCoreCode :=
  scSparseCoreCode sparsifyImplUsed cf firstStep firstInit

/-! ## Determinism and procedure-placement facts -/

theorem scSparseCoreCode_isDeterministic (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    (scSparseCoreCode impl cf firstStep firstInit).prog.IsDeterministic :=
  scProg_isDeterministic impl cf firstStep firstInit

theorem drySparseCoreCode_isDeterministic (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (drySparseCoreCode cf firstStep firstInit).prog.IsDeterministic :=
  scSparseCoreCode_isDeterministic sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasAsmTopProcs (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    HasAsmTopProcs (drySparseCoreCode cf firstStep firstInit).prog
      L.bTop cf.fInit cf.fBatch cf.fExport L.bp :=
  scProg_hasAsmTopProcs sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasAsmBrProcs (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    HasAsmBrProcs (drySparseCoreCode cf firstStep firstInit).prog
      L.bp sparsifyImplUsed cf.fRoot L.I :=
  scProg_hasAsmBrProcs sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasComp (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (drySparseCoreCode cf firstStep firstInit).prog.HasAt 0 cf.procs :=
  scProg_hasComp sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasRead (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    HasReadProcs (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).bRead cf.fRoot :=
  scProg_hasRead sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasSpan (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    (drySparseCoreCode cf firstStep firstInit).prog.HasAt
      (scLayout sparsifyImplUsed cf firstStep firstInit).bSpan
      (bucketSpannerProcs sparsifyImplUsed
        (scLayout sparsifyImplUsed cf firstStep firstInit).bSpan) :=
  scProg_hasSpan sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasTour (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    HasTourProcs (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).bTour :=
  scProg_hasTour sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasOut (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    OutProcsAt (drySparseCoreCode cf firstStep firstInit).prog
      L.bOut L.I.nm L.I.sm L.I.fm L.I.lm :=
  scProg_hasOut sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasBundle (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    (drySparseCoreCode cf firstStep firstInit).prog.HasAt L.bBun
      (bundleProcs L.bBun (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10)) :=
  scProg_hasBundle sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasFirstStep (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    (drySparseCoreCode cf firstStep firstInit).prog.HasAt L.bFirstS (firstStep.procs L.envStep) :=
  scProg_hasFirstStep sparsifyImplUsed cf firstStep firstInit

theorem drySparseCoreCode_hasFirstInit (cf : ScCompCode) (firstStep firstInit : ScSubCode) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    (drySparseCoreCode cf firstStep firstInit).prog.HasAt L.bFirstI (firstInit.procs L.envInit) :=
  scProg_hasFirstInit sparsifyImplUsed cf firstStep firstInit

/-! ## Carried piece contracts on `drySparseCoreCode` -/

/-- Lifts a standalone P4 `ScCompFamilyHyp` on `⟨cf.procs⟩` directly into `drySparseCoreCode`. -/
theorem drySCCompFamilyHyp_of_standalone {CFS : AsmCompFamilySpec}
    (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hCF : ScCompFamilyHyp CFS dryLSFInitUsed ⟨cf.procs⟩ cf.fInit cf.fBatch cf.fExport cf.fRoot) :
    ScCompFamilyHyp CFS dryLSFInitUsed (drySparseCoreCode cf firstStep firstInit).prog
      cf.fInit cf.fBatch cf.fExport cf.fRoot :=
  scCompFamilyHyp_of_standalone sparsifyImplUsed cf firstStep firstInit hCF

/-- P2's `OutTourAt` holds on `drySparseCoreCode`. -/
def drySparseCoreCode_outTourAt (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w vCap eCap : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    OutTourAt tourOutSpec w vCap eCap (drySparseCoreCode cf firstStep firstInit).prog
      L.I.nm L.I.sm L.I.fm L.I.lm :=
  scProg_outTourAt sparsifyImplUsed cf firstStep firstInit w vCap eCap

/-- P2's `AsmBrTourListAt` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_asmBrTourListAt (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    AsmBrTourListAt tourOutRep w (drySparseCoreCode cf firstStep firstInit).prog L.I.fList tourMul :=
  scProg_asmBrTourListAt sparsifyImplUsed cf firstStep firstInit w

/-- P5's `bundleTableDS` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_bundleTableDS_implements (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w slotCap vCap eCap k : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    (bundleTableRep slotCap vCap eCap k).Implements w
      (drySparseCoreCode cf firstStep firstInit).prog
      (L.bBun + bundleIdxTableInit)
      (fun i => if i = 0 then L.bBun + bundleIdxExportGraph else L.bBun + bundleIdxReadBundleOf)
      (bundleTableDS w slotCap vCap eCap k) :=
  scProg_bundleTableDS_implements sparsifyImplUsed cf firstStep firstInit w slotCap vCap eCap k

/-- P5's `AsmBrBunAt` holds on `drySparseCoreCode` from `AsmBrTourBridge` and linear tour-list space. -/
def drySparseCoreCode_asmBrBunAt {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {w cT : ℕ}
    (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hT : let L := scLayout sparsifyImplUsed cf firstStep firstInit
      AsmBrTourBridge TS TR w (drySparseCoreCode cf firstStep firstInit).prog
        (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10))
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1)) :
    AsmBrBunAt TR (fun k slotCap vCap eCap => bunTableRep slotCap vCap eCap k) w
      (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).I.fBun :=
  scProg_asmBrBunAt sparsifyImplUsed cf firstStep firstInit hT hw hLS

/-- P5's headroom `AsmBrBunAt` on `scProgB5` (`bunTableHeadroomRep`) holds on `drySparseCoreCode`. -/
def drySparseCoreCode_asmBrBunAt_headroom {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w cT : ℕ} (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hT : let L := scLayout sparsifyImplUsed cf firstStep firstInit
      AsmBrTourBridge TS TR w (drySparseCoreCode cf firstStep firstInit).prog
        (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10))
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1)) :
    AsmBrBunAt TR scProgB5 w
      (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).I.fBun :=
  scProg_asmBrBunAt_headroom sparsifyImplUsed cf firstStep firstInit hT hw hLS

/-- P5's headroom `AsmBrBunAt` on `tourAsmRep` and `scProgB5` (`bunTableHeadroomRep`) holds
unconditionally on `drySparseCoreCode` for every `16 ≤ 2 ^ w`. -/
def drySparseCoreCode_asmBrBunAt_headroom_tour {w : ℕ} (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (hw : 16 ≤ 2 ^ w) :
    AsmBrBunAt tourAsmRep scProgB5 w
      (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).I.fBun :=
  scProg_asmBrBunAt_headroom_tour sparsifyImplUsed cf firstStep firstInit hw

/-- P2's `AsmBrOutProj` on `tourAsmRep` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_asmBrOutProj (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    AsmBrOutProj tourOutSpec tourAsmRep w (drySparseCoreCode cf firstStep firstInit).prog
      L.I.nm L.I.sm L.I.fm L.I.lm :=
  scProg_asmBrOutProj sparsifyImplUsed cf firstStep firstInit w

/-- P2's `AsmBrTourListProj` on `tourAsmRep` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_asmBrTourListProj (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    AsmBrTourListProj tourAsmRep w (drySparseCoreCode cf firstStep firstInit).prog
      L.I.fList tourMul :=
  scProg_asmBrTourListProj sparsifyImplUsed cf firstStep firstInit w

/-- P2's `AsmBrTourBridge` on `tourAsmRep` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_asmBrTourBridge (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w : ℕ) :
    let L := scLayout sparsifyImplUsed cf firstStep firstInit
    AsmBrTourBridge tourBundleSpec tourAsmRep w (drySparseCoreCode cf firstStep firstInit).prog
      (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10) :=
  scProg_asmBrTourBridge sparsifyImplUsed cf firstStep firstInit w

/-- P10's `ReadBranchAt` holds on `drySparseCoreCode`. -/
theorem drySparseCoreCode_readBranchAt (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    {w vCap eCap tCap L_w P : ℕ} {SP : DSParams} {cap : ℕ}
    {Q : RootQueryAt w (drySparseCoreCode cf firstStep firstInit).prog cf.fRoot}
    (hSPw : SP.w = w) (hSPe : SP.eCap ≤ eCap) (heT : eCap ≤ tCap)
    (hLw : 1 ≤ L_w) (hw : (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w) :
    ReadBranchAt (readRep vCap eCap tCap L_w P) w vCap eCap tCap L_w P SP cap
      (drySparseCoreCode cf firstStep firstInit).prog
      (scLayout sparsifyImplUsed cf firstStep firstInit).bRead
      readBranchIdx13 cf.fRoot Q readBranchMul :=
  scProg_readBranchAt sparsifyImplUsed cf firstStep firstInit hSPw hSPe heT hLw hw

/-- The library's concrete sparsifier program `sparsifyImplUsed` satisfies `SparsifySubpolyStretch`
directly from `dryImplHyp` (`sparsifyImplHyp_sparsifyImplUsed`). -/
theorem sparsifySubpolyStretch_sparsifyImplUsed : SparsifySubpolyStretch sparsifyImplUsed :=
  ⟨dryCSp, dryImplHyp.1, fun m => (dryImplHyp.2.2.2.2 m).1⟩

/-- Uniform bridged top-layer theorem directly on `drySparseCoreCode` from a standalone P4
`ScCompFamilyHyp` on `⟨cf.procs⟩` and `ScBranchPiecesCodeHyp`. -/
theorem drySparseCoreCode_uniform_bridged_with_wordExp {CFS : AsmCompFamilySpec}
    (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hCF : ScCompFamilyHyp CFS dryLSFInitUsed ⟨cf.procs⟩ cf.fInit cf.fBatch cf.fExport cf.fRoot)
    (hBR : ScBranchPiecesCodeHyp CFS dryLSFInitUsed sparsifyImplUsed cf firstStep firstInit) :
    let sc := drySparseCoreCode cf firstStep firstInit
    ∃ wordExp : ℕ → ℕ,
      wordExp 3 ≤ 39 ∧
      ∀ capExp : ℕ, ∀ limbMul : ℕ,
        ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
          P.wordExp = wordExp capExp ∧
          (∀ sizeParam, SparseCoreInitAllocBound (allocation sizeParam)) ∧
          SparseCoreUpdateRestartAllocBound allocation ∧
          ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
            1 ≤ depth → fmt.precision ≤ 4 * L →
            ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
              ∀ (vCap eCap : ℕ),
                ∃ rep : ℕ → SparseCoreOrdAbs
                    (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                      sparsifyImplUsed) →
                    τ → (ℕ → ℕ) → Prop,
                  let R : DSRep (SparseCoreOrdAbs
                      (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                        sparsifyImplUsed)) :=
                    ⟨τ, rep, phi, foot⟩
                  R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                    fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                    depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                    depth ≤ Expander.chosenL ((M + N) ^ 2) →
                    M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                    (∀ j < k, IsValidLSFInitFor (dryLSFInitUsed L fmt.precision) dryCLsstUsed k j) →
                    G.n ≤ G.m + 1 →
                    CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                    R.Implements w sc.prog sc.init sc.op
                      (sparseCoreOrdMachineContractKFBL fmt L depth
                        (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                          sparsifyImplUsed)
                        G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                    SparseCoreReadoutFootAt fmt L depth
                      (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                        sparsifyImplUsed)
                      G k M N vCap eCap capExp P (allocation sizeParam) R sc.prog sc.op :=
  scCode_uniform_bridged_with_wordExp sparsifySubpolyStretch_sparsifyImplUsed sparsifyImplUsed_γ_t
    (drySCCompFamilyHyp_of_standalone cf firstStep firstInit hCF) hBR

/-- Uniform bridged top-layer theorem directly on `drySparseCoreCode` carrying `KFRBL` with
`progReemb`, `SparseCoreReadoutFootAt`, and `SparseCoreUpdateOutFootAt` (input-independent `edMul`). -/
theorem drySparseCoreCode_uniform_bridged_kfrbl_outFoot {CFS : AsmCompFamilySpec}
    (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hCF : ScCompFamilyHyp CFS dryLSFInitUsed ⟨cf.procs⟩ cf.fInit cf.fBatch cf.fExport cf.fRoot)
    (hBR : ScBranchPiecesCodeHyp CFS dryLSFInitUsed sparsifyImplUsed cf firstStep firstInit) :
    let sc := drySparseCoreCode cf firstStep firstInit
    ∃ wordExp : ℕ → ℕ,
      wordExp 3 ≤ 39 ∧
      ∀ capExp : ℕ, ∀ limbMul : ℕ,
        ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
          P.wordExp = wordExp capExp ∧
          (∀ sizeParam, SparseCoreInitAllocBound (allocation sizeParam)) ∧
          SparseCoreUpdateRestartAllocBound allocation ∧
          ∃ edMul : ℕ,
            ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
              1 ≤ depth → fmt.precision ≤ 4 * L →
              ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
                ∀ (vCap eCap : ℕ),
                  ∃ rep : ℕ → SparseCoreOrdAbs
                      (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                        sparsifyImplUsed) →
                      τ → (ℕ → ℕ) → Prop,
                    let R : DSRep (SparseCoreOrdAbs
                        (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                          sparsifyImplUsed)) :=
                      ⟨τ, rep, phi, foot⟩
                    (R.Local ∧ ∀ b x, R.foot b x b) ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                      fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                      depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                      depth ≤ Expander.chosenL ((M + N) ^ 2) →
                      M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                      (∀ j < k, IsValidLSFInitFor (dryLSFInitUsed L fmt.precision) dryCLsstUsed k j) →
                      G.n ≤ G.m + 1 → k ≤ (M + N + 2) ^ capExp →
                      (CompInitFormatHyp L fmt.precision k G.m →
                        R.Implements w sc.prog sc.init sc.op
                          (sparseCoreOrdMachineContractKFRBL fmt L depth
                            (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                              sparsifyImplUsed)
                            (progReemb (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                              sparsifyImplUsed)
                            G k M N vCap eCap capExp P (allocation sizeParam))) ∧
                      SparseCoreReadoutFootAt fmt L depth
                        (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                          sparsifyImplUsed)
                        G k M N vCap eCap capExp P (allocation sizeParam) R sc.prog sc.op ∧
                      SparseCoreUpdateOutFootAt fmt L depth
                        (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                          sparsifyImplUsed)
                        G k M N vCap eCap capExp P (allocation sizeParam) edMul R sc.prog sc.op ∧
                      SparseCoreReembPlaceAt fmt L depth
                        (sparseCoreProgTool (dryLSFInitUsed L fmt.precision) dryCLsstUsed depth
                          sparsifyImplUsed)
                        G k M N vCap eCap capExp P (allocation sizeParam) R sc.prog sc.op :=
  scCode_uniform_bridged_kfrbl_outFoot sparsifySubpolyStretch_sparsifyImplUsed sparsifyImplUsed_γ_t
    (drySCCompFamilyHyp_of_standalone cf firstStep firstInit hCF) hBR

end MinCostFlow.Final.DryRun

end
