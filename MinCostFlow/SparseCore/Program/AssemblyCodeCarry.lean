module

public import MinCostFlow.SparseCore.Program.AssemblyCode
public import MinCostFlow.SparseCore.Program.AssemblyBridgeBranch
public import MinCostFlow.SparseCore.Program.AssemblyBranchBunValue
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep
public import MinCostFlow.SparseCore.Program.TourAsmBridge
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourPot
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot
public import MinCostFlow.SparseCore.Program.TourOutBridge
public import MinCostFlow.SparseCore.Program.SpanBucket
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepOutLayout
public import MinCostFlow.SparseCore.Program.AssemblyContractLayoutTopOp0
public import MinCostFlow.MinRatio.WireReembModel

/-!
# Carrying every sparse-core piece's facts into `scProg` (`AssemblyCodeCarry`)

Proves that every piece's verification theorems carry over unchanged into the single combined
program `p := scProg impl cf firstStep firstInit`:

1. **Relocation and prefix lifting for P4 (`asmCompFamilyAt_shift`, `scCompFamilyHyp_shift`,
   `scCompFamilyHyp_of_standalone`):** any `AsmCompFamilyAt` / `ScCompFamilyHyp` proved on a
   standalone program `Q` transfers to any host program `p` with
   `p.HasAt b (shiftProgramProcs b Q)` (via `MinRatio.runs_shiftProcIds`), and in particular from
   `⟨cf.procs⟩` to `scProg` at offset `0` with zero relocation.
2. **Concrete piece theorems on `scProg`:**
   - P2 (`tourProcs`): `scProg_outTourAt`, `scProg_asmBrTourListAt`;
   - P5 (`bundleProcs` + `bunRestartStmt`): `scProg_bundleTableDS_implements`,
     `scProg_asmBrBunAt` (discharging all six procedure hypotheses of `asmBrBunAt_of_bunRestart`);
   - P6 (`bucketSpannerProcs`): `scProg_bucketSpannerDS_implements`;
   - P7 (`outProcs`): `scProg_hasOut` (`OutProcsAt`, directly instantiating `sig_out*_runs_outProcs`);
   - P10 (`readBranchProcs`): `scProg_readBranchAt`.
3. **Reduced branch-piece hypothesis and uniform top-layer bridge (`ScBranchPiecesCodeHyp`,
   `scBranchPiecesHyp_of_code`, `scBranchModuleHyp_of_code`, `scCode_uniform_bridged_with_wordExp`):**
   discharges `I`, `HasAsmBrProcs`, `HasAsmTopProcs`, and `IsDeterministic` inside the uniform
   top-layer bridge on `scProg`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Relocation and prefix lifting for P4 (`AsmCompFamilyAt` / `ScCompFamilyHyp`) -/

private theorem shiftProcIds_zero (s : Stmt) : shiftProcIds 0 s = s := by
  induction s with
  | nop | assign _ _ | store _ _ | rand _ | ret _ => rfl
  | seq s t ihs iht => simp [shiftProcIds, ihs, iht]
  | cond e s t ihs iht => simp [shiftProcIds, ihs, iht]
  | loop e body ih => simp [shiftProcIds, ih]
  | call r f args => simp [shiftProcIds]

private theorem shiftProgramProcs_zero (Q : Program) : shiftProgramProcs 0 Q = Q.procs := by
  unfold shiftProgramProcs
  rw [List.map_congr_left (fun s _ => shiftProcIds_zero s)]
  exact List.map_id _

private theorem proc_shift_get {Q p : Program} {offset f : ℕ} {body : Stmt}
    (hp : p.HasAt offset (shiftProgramProcs offset Q)) (hbody : Q.procs[f]? = some body) :
    p.procs[offset + f]? = some (shiftProcIds offset body) := by
  have hlen : f < Q.procs.length := (List.getElem?_eq_some_iff.mp hbody).1
  have hbe : Q.procs[f] = body := (List.getElem?_eq_some_iff.mp hbody).2
  simpa [shiftProgramProcs, hbe] using hp f (by simp [shiftProgramProcs, hlen])

/-- Relocates an `AsmCompFamilyAt` instance from `Q` to any host program `p` satisfying
`p.HasAt offset (shiftProgramProcs offset Q)`. -/
noncomputable def asmCompFamilyAt_shift {S : AsmCompFamilySpec} {lsfInit : LSFInit} {w : ℕ}
    {fmt : Num.Format w} {L capExp limbMul offset : ℕ} {Q p : Program} {fInit fBatch : ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (CF : AsmCompFamilyAt S lsfInit w fmt L capExp limbMul Q fInit fBatch) :
    AsmCompFamilyAt S lsfInit w fmt L capExp limbMul p (offset + fInit) (offset + fBatch) where
  rep := CF.rep
  rep_local := CF.rep_local
  vCapOf := CF.vCapOf
  eCapOf := CF.eCapOf
  fExport := offset + CF.fExport
  fRoot := offset + CF.fRoot
  init_runs := fun graph lengths k M N vCap eCap h G mem pos ω hfmt hk hGv hGne hGm hGn hCFmt hkCap hcap hw
      hG hGle hLle hEv hargs hz hsp => by
    obtain ⟨body, hbody, o, st', c, x, hrun, hrep, hv', he', hresp, hcost⟩ :=
      CF.init_runs graph lengths k M N vCap eCap h G mem pos ω hfmt hk hGv hGne hGm hGn hCFmt hkCap hcap hw
        hG hGle hLle hEv hargs hz hsp
    exact ⟨shiftProcIds offset body, proc_shift_get hp hbody, o, st', c, x,
      runs_shiftProcIds hp hrun, hrep, hv', he', hresp, hcost⟩
  batch_runs := fun cfH batch words k M N vCap eCap h cfs x U mem pos ω hfmt hk hk0 hkCap hG0n hcap hw
      hrep hv he hG hB hBU hBcap hBw hBle hargs hft hz hsp => by
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hv', he', hChg, hresp, hcost⟩ :=
      CF.batch_runs cfH batch words k M N vCap eCap h cfs x U mem pos ω hfmt hk hk0 hkCap hG0n hcap hw
        hrep hv he hG hB hBU hBcap hBw hBle hargs hft hz hsp
    exact ⟨shiftProcIds offset body, proc_shift_get hp hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hv', he', hChg, hresp, hcost⟩
  export_runs := fun cfH j k M N vCap eCap h cfs x mem pos ω hfmt hk hj hk0 hkCap hGm hGn hcap hw hrep hv he hft
      hargs hz hsp => by
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hv', he', hExp, hresp, hcost⟩ :=
      CF.export_runs cfH j k M N vCap eCap h cfs x mem pos ω hfmt hk hj hk0 hkCap hGm hGn hcap hw hrep hv he hft
        hargs hz hsp
    exact ⟨shiftProcIds offset body, proc_shift_get hp hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hv', he', hExp, hresp, hcost⟩
  root_runs := fun cfH j u h k cfs x mem pos ω h1 h2 h3 h4 h5 h6 hk0 h7 h8 h9 h10 h11 => by
    obtain ⟨body, hbody, o, st', c, x', hrun, hr, hrep', hv', he', hlo, hhi, hz', hfr', hft', hcost⟩ :=
      CF.root_runs cfH j u h k cfs x mem pos ω h1 h2 h3 h4 h5 h6 hk0 h7 h8 h9 h10 h11
    exact ⟨shiftProcIds offset body, proc_shift_get hp hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hr, hrep', hv', he', hlo, hhi, hz', hfr', hft', hcost⟩

/-- Relocates `ScCompFamilyHyp` from `Q` to any host program `p` satisfying
`p.HasAt offset (shiftProgramProcs offset Q)`. -/
theorem scCompFamilyHyp_shift {CFS : AsmCompFamilySpec} {lsfInit : ℕ → ℕ → LSFInit}
    {Q p : Program} {offset fInit fBatch fExport fRoot : ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (hCF : ScCompFamilyHyp CFS lsfInit Q fInit fBatch fExport fRoot) :
    ScCompFamilyHyp CFS lsfInit p (offset + fInit) (offset + fBatch)
      (offset + fExport) (offset + fRoot) where
  wordExp_le_39 := hCF.wordExp_le_39
  inst capExp limbMul w fmt L := by
    obtain ⟨CF, hfExp, hfRoot⟩ := hCF.inst capExp limbMul w fmt L
    exact ⟨asmCompFamilyAt_shift hp CF, by simp [asmCompFamilyAt_shift, hfExp],
      by simp [asmCompFamilyAt_shift, hfRoot]⟩

/-- Lifts `ScCompFamilyHyp` from the standalone P4 program `⟨cf.procs⟩` directly into
`scProg impl cf firstStep firstInit` (since `cf.procs` sits at offset `0`). -/
theorem scCompFamilyHyp_of_standalone {CFS : AsmCompFamilySpec} {lsfInit : ℕ → ℕ → LSFInit}
    (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hCF : ScCompFamilyHyp CFS lsfInit ⟨cf.procs⟩ cf.fInit cf.fBatch cf.fExport cf.fRoot) :
    ScCompFamilyHyp CFS lsfInit (scProg impl cf firstStep firstInit)
      cf.fInit cf.fBatch cf.fExport cf.fRoot := by
  have hp0 : (scProg impl cf firstStep firstInit).HasAt 0 (shiftProgramProcs 0 ⟨cf.procs⟩) := by
    rw [shiftProgramProcs_zero]
    exact scProg_hasComp impl cf firstStep firstInit
  simpa using scCompFamilyHyp_shift hp0 hCF

/-! ## Concrete piece facts carried into `scProg` -/

/-- P2's `OutTourAt` (`tourDS_outTourAt`) holds in `scProg` at `L.I.{nm, sm, fm, lm}`. -/
def scProg_outTourAt (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (w vCap eCap : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    OutTourAt tourOutSpec w vCap eCap (scProg impl cf firstStep firstInit)
      L.I.nm L.I.sm L.I.fm L.I.lm :=
  tourDS_outTourAt w vCap eCap _ (scLayout impl cf firstStep firstInit).bTour
    (scProg_hasTour impl cf firstStep firstInit)

/-- P2's `AsmBrTourListAt` (`tourDS_asmBrTourListAt`) holds in `scProg` at `L.I.fList`. -/
theorem scProg_asmBrTourListAt (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    AsmBrTourListAt tourOutRep w (scProg impl cf firstStep firstInit) L.I.fList tourMul :=
  tourDS_asmBrTourListAt w (scLayout impl cf firstStep firstInit).bTour _
    (scProg_hasTour impl cf firstStep firstInit)

/-- P2's branch-view conversion for P7 (`tourDS_asmBrOutProj`) holds in `scProg` at
`L.I.{nm, sm, fm, lm}`. -/
theorem scProg_asmBrOutProj (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    AsmBrOutProj tourOutSpec tourAsmRep w (scProg impl cf firstStep firstInit)
      L.I.nm L.I.sm L.I.fm L.I.lm :=
  tourDS_asmBrOutProj w (scLayout impl cf firstStep firstInit).bTour _
    (scProg_hasTour impl cf firstStep firstInit)

/-- P2's branch-view listing conversion for readout 5 (`tourDS_asmBrTourListProj`) holds in
`scProg` at `L.I.fList`. -/
theorem scProg_asmBrTourListProj (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    AsmBrTourListProj tourAsmRep w (scProg impl cf firstStep firstInit) L.I.fList tourMul :=
  tourDS_asmBrTourListProj w (scLayout impl cf firstStep firstInit).bTour _
    (scProg_hasTour impl cf firstStep firstInit)

/-- P2's branch-view conversion for P5 (`tourDS_asmBrTourBridge`) holds in `scProg`. -/
theorem scProg_asmBrTourBridge (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    AsmBrTourBridge tourBundleSpec tourAsmRep w (scProg impl cf firstStep firstInit)
      (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10) :=
  tourDS_asmBrTourBridge w (scLayout impl cf firstStep firstInit).bTour _
    (scProg_hasTour impl cf firstStep firstInit)

/-- The bundle-table representation family with the headroom invariant used by the branch:
`B5 := fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k`. -/
abbrev scProgB5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState) :=
  fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k

/-- P5's `bundleTableDS` (`bundleTableDS_implements`) holds in `scProg` at `L.bBun`. -/
theorem scProg_bundleTableDS_implements (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (w slotCap vCap eCap k : ℕ) :
    let L := scLayout impl cf firstStep firstInit
    (bundleTableRep slotCap vCap eCap k).Implements w (scProg impl cf firstStep firstInit)
      (L.bBun + bundleIdxTableInit)
      (fun i => if i = 0 then L.bBun + bundleIdxExportGraph else L.bBun + bundleIdxReadBundleOf)
      (bundleTableDS w slotCap vCap eCap k) :=
  bundleTableDS_implements w slotCap vCap eCap k (scProg_hasBundle impl cf firstStep firstInit)

/-- **P5's restart (`AsmBrBunAt`) holds in `scProg` at `L.I.fBun`** directly from the tour bridge
`AsmBrTourBridge` and linear tour-list space, with all six procedure placement hypotheses
(`bunRestartStmt`, `outWalkBody`, `sortProcs`, `bundleInitSlotsStmt`, `bundleDllPushContract`,
`bundleExportGraphStmt`) discharged automatically. -/
def scProg_asmBrBunAt {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {w cT : ℕ}
    (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hT : let L := scLayout impl cf firstStep firstInit
      AsmBrTourBridge TS TR w (scProg impl cf firstStep firstInit)
        (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10))
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1)) :
    AsmBrBunAt TR (fun k slotCap vCap eCap => bunTableRep slotCap vCap eCap k) w
      (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).I.fBun := by
  have hBun := bundleProcs_unpack (scProg_hasBundle impl cf firstStep firstInit)
  have hOut := (scProg_hasOut impl cf firstStep firstInit).main
  exact asmBrBunAt_of_bunRestart hT hw hLS
    (scProg_bunRestartAt impl cf firstStep firstInit)
    hOut.2.2.2.2 hBun.1 hBun.2.2.2.2.2.2.2.1.head
    (fun _ _ _ _ _ _ => bundleDllPush_meetsContract hBun.2.2.1)
    hBun.2.2.2.2.2.2.1

/-- **P5's headroom restart (`AsmBrBunAt` on `scProgB5 := bunTableHeadroomRep`) holds in `scProg`
at `L.I.fBun`** directly from `AsmBrTourBridge` and linear tour-list space, via
`asmBrBunAt_of_bunRestart_headroom`. -/
def scProg_asmBrBunAt_headroom {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {w cT : ℕ}
    (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode)
    (hT : let L := scLayout impl cf firstStep firstInit
      AsmBrTourBridge TS TR w (scProg impl cf firstStep firstInit)
        (tourOp L.bTour 4) (tourOp L.bTour 12) (tourOp L.bTour 10))
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1)) :
    AsmBrBunAt TR scProgB5 w
      (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).I.fBun := by
  have hBun := bundleProcs_unpack (scProg_hasBundle impl cf firstStep firstInit)
  have hOut := (scProg_hasOut impl cf firstStep firstInit).main
  exact asmBrBunAt_of_bunRestart_headroom hT hw hLS
    (scProg_bunRestartAt impl cf firstStep firstInit)
    hOut.2.2.2.2 hBun.1 hBun.2.2.2.2.2.2.2.1.head
    (fun _ _ _ _ _ _ => bundleDllPush_meetsContract hBun.2.2.1)
    hBun.2.2.2.2.2.2.1

/-- **P5's headroom restart on `tourAsmRep` holds unconditionally in `scProg` at `L.I.fBun`**
for every `16 ≤ 2 ^ w`, discharging `AsmBrTourBridge` via `tourDS_asmBrTourBridge` and
`tourBundleSpec_listSpace_le` (`cT = 3`), with `.mul = asmBrBunMul tourBundleSpec 3`. -/
def scProg_asmBrBunAt_headroom_tour {w : ℕ} (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (hw : 16 ≤ 2 ^ w) :
    AsmBrBunAt tourAsmRep scProgB5 w
      (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).I.fBun := by
  have hBun := bundleProcs_unpack (scProg_hasBundle impl cf firstStep firstInit)
  have hOut := (scProg_hasOut impl cf firstStep firstInit).main
  exact asmBrBunAt_headroom_of_bunRestart
    (scProg_asmBrTourBridge impl cf firstStep firstInit w) hw tourBundleSpec_listSpace_le
    (scProg_bunRestartAt impl cf firstStep firstInit)
    hOut.2.2.2.2 hBun.1 hBun.2.2.2.2.2.2.2.1.head
    (fun _ _ _ _ _ _ => bundleDllPush_meetsContract hBun.2.2.1)
    hBun.2.2.2.2.2.2.1

theorem scProg_asmBrBunAt_headroom_tour_mul {w : ℕ} (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (hw : 16 ≤ 2 ^ w) :
    (scProg_asmBrBunAt_headroom_tour impl cf firstStep firstInit hw).mul =
      asmBrBunMul tourBundleSpec 3 := rfl

/-- **P5's headroom restart on `asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)`
holds unconditionally in `scProg` at `L.I.fBun`** for every `16 ≤ 2 ^ w`, with
`.mul = asmBrBunMul tourBundleSpec 3`. -/
noncomputable def scProg_asmBrBunAt_headroom_tourPot {w : ℕ} (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (hw : 16 ≤ 2 ^ w) :
    AsmBrBunAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 w
      (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).I.fBun := by
  have hBun := bundleProcs_unpack (scProg_hasBundle impl cf firstStep firstInit)
  have hOut := (scProg_hasOut impl cf firstStep firstInit).main
  exact asmBrBunAt_headroom_of_bunRestart
    (asmTourRepWithPot_bundleBridge (scProg_asmBrTourBridge impl cf firstStep firstInit w)
      (bundleScanPotMul tourBundleSpec))
    hw tourBundleSpec_listSpace_le
    (scProg_bunRestartAt impl cf firstStep firstInit)
    hOut.2.2.2.2 hBun.1 hBun.2.2.2.2.2.2.2.1.head
    (fun _ _ _ _ _ _ => bundleDllPush_meetsContract hBun.2.2.1)
    hBun.2.2.2.2.2.2.1

theorem scProg_asmBrBunAt_headroom_tourPot_mul {w : ℕ} (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) (hw : 16 ≤ 2 ^ w) :
    (scProg_asmBrBunAt_headroom_tourPot impl cf firstStep firstInit hw).mul =
      asmBrBunMul tourBundleSpec 3 := rfl

/-- P6's `bucketSpannerDS` (`bucketSpannerDS_implements`) holds in `scProg` at `L.bSpan`. -/
theorem scProg_bucketSpannerDS_implements (P : DSParams) (cap : ℕ) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    let L := scLayout P.impl cf firstStep firstInit
    (bucketSpannerRep P cap).Implements P.w (scProg P.impl cf firstStep firstInit)
      (L.bSpan + bsIdxInit) (fun i => L.bSpan + bsIdxOp0 + i)
      (bucketSpannerDS P cap) :=
  bucketSpannerDS_implements P cap (scProg_hasSpan P.impl cf firstStep firstInit)

/-- P10's `ReadBranchAt` (`readBranchAt_readRep`) holds in `scProg` at `L.bRead`. -/
theorem scProg_readBranchAt (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode)
    {w vCap eCap tCap L_w P : ℕ} {SP : DSParams} {cap : ℕ}
    {Q : RootQueryAt w (scProg impl cf firstStep firstInit) cf.fRoot}
    (hSPw : SP.w = w) (hSPe : SP.eCap ≤ eCap) (heT : eCap ≤ tCap)
    (hLw : 1 ≤ L_w) (hw : (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w) :
    ReadBranchAt (readRep vCap eCap tCap L_w P) w vCap eCap tCap L_w P SP cap
      (scProg impl cf firstStep firstInit) (scLayout impl cf firstStep firstInit).bRead
      readBranchIdx13 cf.fRoot Q readBranchMul :=
  readBranchAt_readRep (scProg_hasRead impl cf firstStep firstInit) hSPw hSPe heT hLw hw

/-! ## Reduced branch-piece hypothesis and uniform top-layer bridge on `scProg` -/

/-- Constants of the two first-phase pieces (of the step and of the init): multipliers and
space polynomials of the first phases of step and init, plus the init's word-size exponent. All
other `AsmBrConsts` fields (`OS`, `bunMul`, `listMul`, and stretch `(Cγ, cγ)`) are discharged
automatically on `scProg` using `tourAsmRep`, `scProgB5` (`bunTableHeadroomRep`), and `walkPot`. -/
structure ScFirstConsts where
  stepMul : ℕ → ℕ → ℕ
  stepYs : ℕ → ℕ → ℕ
  stepSpace : ℕ → PolyBound
  initMul : ℕ → ℕ → ℕ
  initSpace : ℕ → PolyBound
  firstWordExp : ℕ → ℕ

/-- Completes `ScFirstConsts` into `AsmBrConsts` with `scProg`'s concrete P2 and P5 constants. -/
def ScFirstConsts.toAsmBrConsts (C : ScFirstConsts) : AsmBrConsts where
  stepMul := C.stepMul
  stepYs := C.stepYs
  stepSpace := C.stepSpace
  initMul := C.initMul
  initSpace := C.initSpace
  firstWordExp := C.firstWordExp
  OS := tourOutSpec
  bunMul := asmBrBunMul tourBundleSpec 3
  listMul := tourMul
  Cγ := 0
  cγ := 0

/-- **Reduced branch-piece hypothesis on `scProg`**: compared to `ScBranchPiecesHyp`, not only `I`
and `HasAsmBrProcs`, but also
`TR := asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)`,
`B5 := scProgB5` (`bunTableHeadroomRep`), `Ψ := walkPot`, their locality/handle-foot/restart-potential
lemmas, P5's restart (`JB`, `JB_mul`), and P2's conversions (`out`, `list`) are all discharged
automatically on `scProg`. Only the first phases of the step (`AsmBrCoreStepAt` at `L.I.fCoreS`)
and of the init (`AsmBrCoreInitAt` at `L.I.fCoreI`) with their
constants `C : ScFirstConsts` (`C.firstWordExp 3 ≤ 39`) are fields. -/
structure ScBranchPiecesCodeHyp (CFS : AsmCompFamilySpec) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl) (cf : ScCompCode) (firstStep firstInit : ScSubCode) : Prop where
  inst :
    let L := scLayout impl cf firstStep firstInit
    let p := scProg impl cf firstStep firstInit
    ∃ C : ScFirstConsts,
      C.firstWordExp 3 ≤ 39 ∧
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt CFS (lsfInit L_in fmt.precision) w fmt L_in capExp limbMul
            p cf.fInit cf.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = cf.fRoot →
          (∃ JS : AsmBrCoreStepAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 impl depth
              fmt.precision L_in capExp limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p
              L.I.fCoreS,
            JS.mul = C.stepMul capExp limbMul ∧
            JS.ysMul = C.stepYs capExp limbMul ∧
            JS.spaceP = C.stepSpace capExp) ∧
          (∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (lsfInit L_in fmt.precision) impl depth fmt.precision L_in capExp limbMul
              (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp)

/-- `ScBranchPiecesCodeHyp` immediately discharges `ScBranchPiecesHyp` on `scProg`, instantiating
`TR := asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)`, `B5 := scProgB5`
(`bunTableHeadroomRep`), `Ψ := walkPot`, P5's headroom restart
(`asmTourRepWithPot_bunAt` of `scProg_asmBrBunAt_headroom_tour`), and P2's tour projections
(`asmTourRepWithPot_outProj` / `asmTourRepWithPot_listProj`). -/
theorem scBranchPiecesHyp_of_code {CFS : AsmCompFamilySpec} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} {cf : ScCompCode} {firstStep firstInit : ScSubCode}
    (hV : ScBranchPiecesCodeHyp CFS lsfInit impl cf firstStep firstInit) :
    let L := scLayout impl cf firstStep firstInit
    ScBranchPiecesHyp CFS lsfInit impl (scProg impl cf firstStep firstInit)
      cf.fInit cf.fBatch cf.fRoot L.bp := by
  refine ⟨?_⟩
  obtain ⟨C, hwe, hDepth⟩ := hV.inst
  refine ⟨C.toAsmBrConsts, (scLayout impl cf firstStep firstInit).I, hwe,
    scProg_hasAsmBrProcs impl cf firstStep firstInit, fun depth hdepth => ?_⟩
  refine ⟨asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec), scProgB5, walkPot,
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec),
    fun k slotCap vCap eCap => bunTableHeadroomRep_local slotCap vCap eCap k,
    asmTourRepWithPot_foot_self tourAsmRep_handle_foot (bundleScanPotMul tourBundleSpec),
    walkPot_restartOK impl depth,
    fun capExp limbMul w fmt L_in CF hPL hfRoot => ?_⟩
  obtain ⟨⟨JS, hJS_mul, hJS_ys, hJS_sp⟩, ⟨JI, hJI_mul, hJI_sp⟩⟩ :=
    hDepth depth hdepth capExp limbMul w fmt L_in CF hPL hfRoot
  exact ⟨{
    JS := JS
    JS_mul := hJS_mul
    JS_ys := hJS_ys
    JS_space := hJS_sp
    JI := JI
    JI_mul := hJI_mul
    JI_space := hJI_sp
    JB := fun h16 => scProg_asmBrBunAt_headroom_tourPot impl cf firstStep firstInit h16
    JB_mul := fun h16 => scProg_asmBrBunAt_headroom_tourPot_mul impl cf firstStep firstInit h16
    out := asmTourRepWithPot_outProj (scProg_asmBrOutProj impl cf firstStep firstInit w)
      (bundleScanPotMul tourBundleSpec)
    list := asmTourRepWithPot_listProj (scProg_asmBrTourListProj impl cf firstStep firstInit w)
      (bundleScanPotMul tourBundleSpec) }⟩

/-- `ScBranchPiecesCodeHyp` immediately discharges `ScBranchModuleHyp` on `scProg`. -/
theorem scBranchModuleHyp_of_code {CFS : AsmCompFamilySpec} {C_lsst : ℝ}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep firstInit : ScSubCode}
    (hV : ScBranchPiecesCodeHyp CFS lsfInit impl cf firstStep firstInit) :
    let L := scLayout impl cf firstStep firstInit
    ScBranchModuleHyp CFS C_lsst lsfInit impl (scProg impl cf firstStep firstInit)
      cf.fInit cf.fBatch cf.fRoot L.bp :=
  scBranchModuleHyp_of_pieces (scBranchPiecesHyp_of_code hV)

/-- **Uniform bridged top-layer theorem on `scProg` with `KFRBL` (`progReemb`) and
`SparseCoreUpdateOutFootAt`**: discharges `HasAsmTopProcs`, `HasAsmBrProcs`, and `IsDeterministic`,
and produces a single capacity-indexed representation meeting `sparseCoreOrdMachineContractKFRBL`
with `progReemb`, `SparseCoreReadoutFootAt`, and `SparseCoreUpdateOutFootAt` with an
input-independent `edMul`. -/
theorem scCode_uniform_bridged_kfrbl_outFoot
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {cf : ScCompCode} {firstStep firstInit : ScSubCode}
    (hγ : SparsifySubpolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit (scProg impl cf firstStep firstInit)
      cf.fInit cf.fBatch cf.fExport cf.fRoot)
    (hBR : ScBranchPiecesCodeHyp CFS lsfInit impl cf firstStep firstInit) :
    let L := scLayout impl cf firstStep firstInit
    let p := scProg impl cf firstStep firstInit
    ∃ wordExp : ℕ → ℕ,
      wordExp 3 ≤ 39 ∧
      ∀ capExp : ℕ, ∀ limbMul : ℕ,
        ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
          P.wordExp = wordExp capExp ∧
          (∀ sizeParam, SparseCoreInitAllocBound (allocation sizeParam)) ∧
          SparseCoreUpdateRestartAllocBound allocation ∧
          ∃ edMul : ℕ,
            ∀ (depth w : ℕ) (fmt : Num.Format w) (L_in : ℕ),
              1 ≤ depth → fmt.precision ≤ 4 * L_in →
              ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
                ∀ (vCap eCap : ℕ),
                  ∃ rep : ℕ → SparseCoreOrdAbs
                      (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl) →
                      τ → (ℕ → ℕ) → Prop,
                    let R : DSRep (SparseCoreOrdAbs
                        (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)) :=
                      ⟨τ, rep, phi, foot⟩
                    (R.Local ∧ ∀ b x, R.foot b x b) ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                      fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L_in M N vCap eCap →
                      depth ≤ M + N + k + L_in → depth ≤ bundleLogFactor M N →
                      depth ≤ Expander.chosenL ((M + N) ^ 2) →
                      M + N + k + vCap + eCap + L_in + depth ≤ sizeParam →
                      (∀ j < k, IsValidLSFInitFor (lsfInit L_in fmt.precision) C_lsst k j) →
                      G.n ≤ G.m + 1 → k ≤ (M + N + 2) ^ capExp →
                      (CompInitFormatHyp L_in fmt.precision k G.m →
                        R.Implements w p (asmTopInitIdx L.bTop) (asmTopOpIdx L.bTop)
                          (sparseCoreOrdMachineContractKFRBL fmt L_in depth
                            (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                            (progReemb (lsfInit L_in fmt.precision) C_lsst depth impl)
                            G k M N vCap eCap capExp P (allocation sizeParam))) ∧
                      SparseCoreReadoutFootAt fmt L_in depth
                        (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                        G k M N vCap eCap capExp P (allocation sizeParam) R p
                        (asmTopOpIdx L.bTop) ∧
                      SparseCoreUpdateOutFootAt fmt L_in depth
                        (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                        G k M N vCap eCap capExp P (allocation sizeParam) edMul R p
                        (asmTopOpIdx L.bTop) ∧
                      SparseCoreReembPlaceAt fmt L_in depth
                        (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                        G k M N vCap eCap capExp P (allocation sizeParam) R p
                        (asmTopOpIdx L.bTop) := by
  obtain ⟨K, I, hwe, hP, hDepth⟩ := (scBranchPiecesHyp_of_code hBR).inst
  have hγp : SparsifyPolyStretch impl := sparsifyPolyStretch_of_subpolyStretch hγ
  let K' := scBranchConstsOfStretch K hγp
  let BRS := asmBrSpec CFS impl K'
  have hBR_we : BRS.wordExp 3 ≤ 39 := asmBrSpec_wordExp_three hwe
  refine ⟨asmTopWordExp CFS BRS, ?_, fun capExp limbMul => ?_⟩
  · unfold asmTopWordExp
    rw [asmP10WordExp_at_3]
    exact max_le (max_le hCF.wordExp_le_39 hBR_we) (by decide)
  · refine ⟨asmTopParams CFS BRS capExp limbMul, asmTopAlloc CFS BRS capExp, rfl,
      asmTopAlloc_initBound CFS BRS capExp, asmTopAlloc_updateRestartBound CFS BRS capExp,
      asmBrEdMul (K'.stepYs capExp limbMul), fun depth w fmt L_in hdepth hPL => ?_⟩
    obtain ⟨CF, hfExp, hfRoot⟩ := hCF.inst capExp limbMul w fmt L_in
    obtain ⟨TR, B5, Ψ, hTR, hB5, hTh, hΨ, hPieces⟩ := hDepth depth hdepth
    obtain ⟨X⟩ := hPieces capExp limbMul w fmt L_in CF hPL hfRoot
    let X' := X.withStretch hγp
    have hP' : HasAsmBrProcs (scProg impl cf firstStep firstInit)
        (scLayout impl cf firstStep firstInit).bp impl CF.fRoot I := by
      rw [hfRoot]; exact hP
    let BR := asmBranchAt_value (K := K') (C_lsst := C_lsst) (CF := CF)
      hTR hB5 hTh hΨ (Classical.choose_spec (Classical.choose_spec hγp))
      (fun _ _ _ _ => rfl) hP' X'
    let hLay := asmBranchAt_value_readoutLayout (K := K') (C_lsst := C_lsst) (CF := CF)
      hTR hB5 hTh hΨ (Classical.choose_spec (Classical.choose_spec hγp))
      (fun _ _ _ _ => rfl) hP' X'
    let hStepLay := asmBranchAt_value_stepOutLayout (K := K') (C_lsst := C_lsst) (CF := CF)
      hTR hB5 hTh hΨ (Classical.choose_spec (Classical.choose_spec hγp))
      (fun _ _ _ _ => rfl) hP' X'
    have hp := scProg_hasAsmTopProcs impl cf firstStep firstInit
    refine ⟨AsmTopMeta CF.rep.τ BR.rep.τ,
      fun _ x mem => asmTopPhi CF.rep BR.rep x mem,
      fun hndl x addr => asmTopFoot CF.rep BR.rep rfl rfl hndl x addr,
      fun vCap eCap => ?_⟩
    refine ⟨(asmTopRepEq (lsfInit := lsfInit L_in fmt.precision) (C_lsst := C_lsst) (impl := impl)
        CF.rep BR.rep CF.vCapOf CF.eCapOf (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L_in
        fmt.precision vCap eCap).rep,
      ⟨asmTopRepEq_local (cfV := CF.vCapOf) (cfE := CF.eCapOf) CF.rep_local BR.rep_local,
        fun _ _ => Or.inl ⟨le_rfl, by unfold ASM_HDR_SIZE; omega⟩⟩,
      fun G k M N sizeParam hfmt hcap hdepth_le hdepth_lg hdepth_ch hsize hInit hGn_le hkCap =>
        ⟨fun hCFmt => asmTop_implements_kfr CF BR hLay hp hfExp.symm G k M N vCap eCap sizeParam
          hfmt hPL hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize (hγt M) hInit hGn_le hCFmt hkCap,
         asmTop_readoutFoot_implements CF BR hLay hp G k M N vCap eCap sizeParam
          hfmt hcap hdepth hInit,
         asmTop_updateOutFoot_reembPlace CF BR hStepLay hp G k M N vCap eCap sizeParam
          hfmt hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize (hγt M) hInit hkCap⟩⟩

/-- **Uniform bridged top-layer theorem on the single combined program `scProg`**: discharges
`HasAsmTopProcs`, `HasAsmBrProcs`, and `IsDeterministic`, requiring only `SparsifyPolyStretch`,
`γ_t = 1`, P4 (`ScCompFamilyHyp`), and the reduced branch pieces (`ScBranchPiecesCodeHyp`). -/
theorem scCode_uniform_bridged_with_wordExp
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {cf : ScCompCode} {firstStep firstInit : ScSubCode}
    (hγ : SparsifySubpolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit (scProg impl cf firstStep firstInit)
      cf.fInit cf.fBatch cf.fExport cf.fRoot)
    (hBR : ScBranchPiecesCodeHyp CFS lsfInit impl cf firstStep firstInit) :
    let L := scLayout impl cf firstStep firstInit
    let p := scProg impl cf firstStep firstInit
    ∃ wordExp : ℕ → ℕ,
      wordExp 3 ≤ 39 ∧
      ∀ capExp : ℕ, ∀ limbMul : ℕ,
        ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
          P.wordExp = wordExp capExp ∧
          (∀ sizeParam, SparseCoreInitAllocBound (allocation sizeParam)) ∧
          SparseCoreUpdateRestartAllocBound allocation ∧
          ∀ (depth w : ℕ) (fmt : Num.Format w) (L_in : ℕ),
            1 ≤ depth → fmt.precision ≤ 4 * L_in →
            ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
              ∀ (vCap eCap : ℕ),
                ∃ rep : ℕ → SparseCoreOrdAbs
                    (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl) →
                    τ → (ℕ → ℕ) → Prop,
                  let R : DSRep (SparseCoreOrdAbs
                      (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)) :=
                    ⟨τ, rep, phi, foot⟩
                  R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                    fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L_in M N vCap eCap →
                    depth ≤ M + N + k + L_in → depth ≤ bundleLogFactor M N →
                    depth ≤ Expander.chosenL ((M + N) ^ 2) →
                    M + N + k + vCap + eCap + L_in + depth ≤ sizeParam →
                    (∀ j < k, IsValidLSFInitFor (lsfInit L_in fmt.precision) C_lsst k j) →
                    G.n ≤ G.m + 1 →
                    CompInitFormatHyp L_in fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                    R.Implements w p (asmTopInitIdx L.bTop) (asmTopOpIdx L.bTop)
                      (sparseCoreOrdMachineContractKFBL fmt L_in depth
                        (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                        G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                    SparseCoreReadoutFootAt fmt L_in depth
                      (sparseCoreProgTool (lsfInit L_in fmt.precision) C_lsst depth impl)
                      G k M N vCap eCap capExp P (allocation sizeParam) R p (asmTopOpIdx L.bTop) :=
  asmTop_uniform_bridged_with_wordExp
    (scProg_hasAsmTopProcs impl cf firstStep firstInit) hγ hγt hCF
    (scBranchModuleHyp_of_code hBR)

end MinCostFlow.SparseCore.Program
