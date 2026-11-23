module

public import MinCostFlow.MinRatio.InitTail
public import MinCostFlow.MinRatio.InitDetectThresholds
public import MinCostFlow.MinRatio.InitPathTreeChain
public import MinCostFlow.MinRatio.ProgramShift
public import MinCostFlow.LinkCut.PathProg.Implements
public import MinCostFlow.LastLevelProgram.RuntimeImplementation
public import MinCostFlow.DynSpanner.Program.DynGraphInit
public import MinCostFlow.Expander.HeapSortProg
public import MinCostFlow.Num.IPM.Alpha
public import MinCostFlow.IPM.Machine.PrecisionSelection
import MinCostFlow.Num.ModulePlacement

/-!
# Concrete module bundle for Algorithm 2 initialization

Packs every concrete Word RAM submodule required by `solverInitCompleteProgram`,
`initDetectThresholdsAndRecords`, and `initLinkChainForests` into one
relocatable list of procedure bodies `initConcreteHelperProcs` at fixed constant
offsets from `base`:
- multiword arithmetic (`copyWords`, `add`, `negate`, `subtract`, `shiftLeft`,
  `extendCopy`, `multiply`, `fixedDivide`, `Num.IPM.alpha`),
- parameter/precision/depth helpers (`precisionSelection`, `initDepthProcedures`,
  `Scaling.Machine.clogTwoModule`, `initMachinePathFactorsProc`, `initStretchPower`),
- graph and sorting helpers (`Expander.heapSort`, `dgOpsProcs`/`dgEdgeProcs`/
  `dgSplitProcs`/`dgBatchProcs`),
- gradient-cell and slot-binding helpers (`detectorRefresh`, `writeCoreGradientCell`,
  `pathSlotBind`),
- the Section 6 link-cut tree (`LinkCut.PathProg.pathTreeBodies 4`), and
- the relocated last-level runtime program (`shiftProgramProcs (base + 352) lastProg`).

Proves `initConcreteHelperProcs_meetsAll`: any host program containing this
bundle at `base` (with `14 ≤ w`) satisfies every concrete `MeetsContract`,
`HasAt`, and `DSRep.Implements` hypothesis simultaneously.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Num DynSpanner.Program

/-- Fixed entry offsets for every concrete submodule packed inside
`initConcreteHelperProcs base Kγ pathC Kint lastProg`. -/
structure InitConcreteLayout where
  copy : ℕ
  add : ℕ
  negate : ℕ
  subtract : ℕ
  shiftLeft : ℕ
  extendCopy : ℕ
  multiply : ℕ
  fixedDivide : ℕ
  alpha : ℕ
  precisionSelect : ℕ
  depth : ℕ
  clog : ℕ
  factors : ℕ
  power : ℕ
  siftDown : ℕ
  heapSort : ℕ
  dgOps : ℕ
  dgEdge : ℕ
  dgSplit : ℕ
  dgBatch : ℕ
  dgInitFromLists : ℕ
  detectorRefresh : ℕ
  writeGradCell : ℕ
  slotBind : ℕ
  pathTree : ℕ
  lastLevel : ℕ

/-- Constant-offset layout matching `initConcreteHelperProcs`. -/
def initConcreteLayout (base : ℕ) : InitConcreteLayout where
  copy := base
  add := base + 1
  negate := base + 3
  subtract := base + 5
  shiftLeft := base + 10
  extendCopy := base + 12
  multiply := base + 13
  fixedDivide := base + 18
  alpha := base + 50
  precisionSelect := base + 53
  depth := base + 58
  clog := base + 265
  factors := base + 266
  power := base + 267
  siftDown := base + 268
  heapSort := base + 269
  dgOps := base + 270
  dgEdge := base + 277
  dgSplit := base + 279
  dgBatch := base + 282
  dgInitFromLists := base + 282 + dgIdxInitFromLists
  detectorRefresh := base + 285
  writeGradCell := base + 286
  slotBind := base + 287
  pathTree := base + 288
  lastLevel := base + 352

/-- Deterministic list of all concrete helper modules starting at `base`. -/
def initConcreteHelperProcs (base Kγ pathC Kint : ℕ) (lastProg : Program) : List Stmt :=
  [copyWords] ++
  (Num.addModule (base + 1) 4 ++
  (Num.negateModule (base + 3) 4 ++
  (Num.subtractModule (base + 5) 4 ++
  (Num.shiftLeftModule (base + 10) 4 ++
  (Num.extendCopyModule (base + 12) ++
  (Num.multiplyModule (base + 13) 4 ++
  (Num.fixedDivideModule (base + 18) 4 ++
  (Num.IPM.alphaModule (base + 50) 4 ++
  (IPM.Machine.precisionSelectionModule (base + 53) ++
  (initDepthProcedures (base + 58) 4 ++
  (Scaling.Machine.clogTwoModule (base + 265) ++
  ([initMachinePathFactorsProc Kγ pathC Kint (base + 58) (base + 58 + 5)] ++
  ([initStretchPowerBody (base + 267)] ++
  ([Expander.siftDownProc, Expander.heapSortProc (base + 268)] ++
  (dgOpsProcs ++
  (dgEdgeProcs (base + 270) ++
  (dgSplitProcs (base + 270) (base + 279) ++
  (dgBatchProcs (base + 270) (base + 277) (base + 279) (base + 282) ++
  ([detectorRefreshBody (base + 5) (base + 1), writeCoreGradientCell (base + 285) base] ++
  ([pathSlotBindBody] ++
  (LinkCut.PathProg.pathTreeBodies 4 (base + 288) ++
  shiftProgramProcs (base + 352) lastProg)))))))))))))))))))))

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Num DynSpanner.Program

private theorem hasAt_peel {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Any program embedding `initConcreteHelperProcs base Kγ pathC Kint lastProg`
at `base` satisfies every concrete numeric, graph, sort, path-factor, slot-bind,
and Section 6 link-cut tree contract, and embeds `shiftProgramProcs (base + 352) lastProg`. -/
theorem initConcreteHelperProcs_meetsAll {w base Kγ pathC Kint cw : ℕ}
    {lastProg p : Program} (hw : 14 ≤ w)
    (hp : p.HasAt base (initConcreteHelperProcs base Kγ pathC Kint lastProg)) :
    let L := initConcreteLayout base
    MeetsContract w p L.copy (copyWordsContract w) ∧
    MeetsContract w p L.add (Num.addContract w 4) ∧
    MeetsContract w p L.negate (Num.negateContract w 4) ∧
    MeetsContract w p L.subtract (Num.subtractContract w 4) ∧
    MeetsContract w p L.shiftLeft (Num.shiftLeftContract w 4) ∧
    MeetsContract w p L.extendCopy (Num.extendCopyContract w 4) ∧
    MeetsContract w p L.multiply (Num.multiplyContract w 4) ∧
    MeetsContract w p L.fixedDivide (Num.fixedDivideContract w 4) ∧
    MeetsContract w p L.alpha (Num.IPM.alphaContract w 4) ∧
    MeetsContract w p L.precisionSelect (IPM.Machine.precisionSelectionContract w) ∧
    p.HasAt L.depth (initDepthProcedures L.depth 4) ∧
    p.HasAt L.clog (Scaling.Machine.clogTwoModule L.clog) ∧
    MeetsContract w p L.factors (initMachinePathFactorsContract w Kγ pathC Kint cw) ∧
    MeetsContract w p L.power (initStretchPowerContract w) ∧
    MeetsContract w p L.heapSort (Expander.heapSortContract w) ∧
    (∀ vCap eCap G vL eEdges,
      MeetsContract w p L.dgInitFromLists (dgInitFromListsContract w vCap eCap G vL eEdges)) ∧
    (∀ x y z, MeetsContract w p L.writeGradCell (writeCoreGradientCellContract w 4 x y z)) ∧
    MeetsContract w p L.slotBind (pathSlotBindContract w) ∧
    (∀ (fmt : Num.Format w) (limbs : ℕ), fmt.limbBits = 4 →
      (LinkCut.PathProg.pathRep 4 limbs LinkCut.PathProg.pathC).Implements w p
        L.pathTree (fun i => L.pathTree + 1 + i)
        (pathTreeMachineContract fmt limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc limbs))) ∧
    p.HasAt L.lastLevel (shiftProgramProcs L.lastLevel lastProg) := by
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hbase4 : Num.base 4 < 2 ^ w := by
    change 2 ^ 4 < 2 ^ w; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hw10 : 2 * 4 + 2 ≤ w := by omega
  have hw14 : 3 * 4 + 2 ≤ w := by omega
  unfold initConcreteHelperProcs at hp
  obtain ⟨hm0, hr1⟩ := hasAt_peel (b' := base + 1) hp (by change base + 1 = base + 1; rfl)
  obtain ⟨hm1, hr2⟩ := hasAt_peel (b' := base + 3) hr1 (by change base + 1 + 2 = base + 3; omega)
  obtain ⟨hm2, hr3⟩ := hasAt_peel (b' := base + 5) hr2 (by change base + 3 + 2 = base + 5; omega)
  obtain ⟨hm3, hr4⟩ := hasAt_peel (b' := base + 10) hr3 (by change base + 5 + 5 = base + 10; omega)
  obtain ⟨hm4, hr5⟩ := hasAt_peel (b' := base + 12) hr4 (by change base + 10 + 2 = base + 12; omega)
  obtain ⟨hm5, hr6⟩ := hasAt_peel (b' := base + 13) hr5 (by change base + 12 + 1 = base + 13; omega)
  obtain ⟨hm6, hr7⟩ := hasAt_peel (b' := base + 18) hr6 (by change base + 13 + 5 = base + 18; omega)
  obtain ⟨hm7, hr8⟩ := hasAt_peel (b' := base + 50) hr7 (by change base + 18 + 32 = base + 50; omega)
  obtain ⟨hm8, hr9⟩ := hasAt_peel (b' := base + 53) hr8 (by change base + 50 + 3 = base + 53; omega)
  obtain ⟨hm9, hr10⟩ := hasAt_peel (b' := base + 58) hr9 (by change base + 53 + 5 = base + 58; omega)
  obtain ⟨hm10, hr11⟩ := hasAt_peel (b' := base + 265) hr10 (by change base + 58 + 207 = base + 265; omega)
  obtain ⟨hm11, hr12⟩ := hasAt_peel (b' := base + 266) hr11 (by change base + 265 + 1 = base + 266; omega)
  obtain ⟨hm12, hr13⟩ := hasAt_peel (b' := base + 267) hr12 (by change base + 266 + 1 = base + 267; omega)
  obtain ⟨hm13, hr14⟩ := hasAt_peel (b' := base + 268) hr13 (by change base + 267 + 1 = base + 268; omega)
  obtain ⟨hm14, hr15⟩ := hasAt_peel (b' := base + 270) hr14 (by change base + 268 + 2 = base + 270; omega)
  obtain ⟨hm15, hr16⟩ := hasAt_peel (b' := base + 277) hr15 (by change base + 270 + 7 = base + 277; omega)
  obtain ⟨hm16, hr17⟩ := hasAt_peel (b' := base + 279) hr16 (by change base + 277 + 2 = base + 279; omega)
  obtain ⟨hm17, hr18⟩ := hasAt_peel (b' := base + 282) hr17 (by change base + 279 + 3 = base + 282; omega)
  obtain ⟨hm18, hr19⟩ := hasAt_peel (b' := base + 285) hr18 (by change base + 282 + 3 = base + 285; omega)
  obtain ⟨hm19, hr20⟩ := hasAt_peel (b' := base + 287) hr19 (by change base + 285 + 2 = base + 287; omega)
  obtain ⟨hm20, hr21⟩ := hasAt_peel (b' := base + 288) hr20 (by change base + 287 + 1 = base + 288; omega)
  obtain ⟨hm21, hm22⟩ := hasAt_peel (b' := base + 352) hr21 (by change base + 288 + 64 = base + 352; omega)
  have hcopy := copyWords_meetsContract (w := w) hm0
  have hadd := Num.add_meetsContract (by decide) hw10 hm1
  have hneg := Num.negate_meetsContract hw1 hbase4 hm2
  have hsub := Num.subtract_meetsContract (by decide) hw10 hm3
  have hshift := Num.shiftLeft_meetsContract (by decide) hw10 hm4
  have hext := Num.extendCopy_meetsContract (h := 4) hw1 hm5
  have hmul := Num.multiply_meetsContract (by decide) hw10 hm6
  have hdiv := Num.fixedDivide_meetsContract (by decide) hw14 hm7
  have halpha := Num.IPM.alpha_meetsContract (by decide) hw10 hm8
  have hsel := IPM.Machine.precisionSelection_meetsContract (w := w) hm9
  have hdepthC := initDepthProcedures_meetsContracts (by decide) hw14 hm10
  have hfac := initMachinePathFactorsProc_meetsContract (w := w) (Kγ := Kγ) (c := pathC) (Kint := Kint) (cw := cw) hm12.head hdepthC.1 hdepthC.2.2.2.1
  have hpow := initStretchPower_meetsContract hw1 hm13
  have hsift : p.HasAt (base + 268) [Expander.siftDownProc] :=
    hasAt_append_left (show p.HasAt (base + 268) ([Expander.siftDownProc] ++ [Expander.heapSortProc (base + 268)]) from hm14)
  have hsortAt : p.HasAt (base + 268 + 1) [Expander.heapSortProc (base + 268)] :=
    hasAt_append_right (show p.HasAt (base + 268) ([Expander.siftDownProc] ++ [Expander.heapSortProc (base + 268)]) from hm14)
  have hsort := Expander.heapSort_spec (w := w) hsift hsortAt
  have hdg : ∀ vCap eCap G vL eEdges,
      MeetsContract w p (base + 282 + dgIdxInitFromLists) (dgInitFromListsContract w vCap eCap G vL eEdges) :=
    fun vCap eCap G vL eEdges => dgInitFromLists_meetsContract (w := w) hm18 hm16 hm15
  have hrefAt : p.HasAt (base + 285) [detectorRefreshBody (base + 5) (base + 1)] :=
    hasAt_append_left (show p.HasAt (base + 285)
      ([detectorRefreshBody (base + 5) (base + 1)] ++ [writeCoreGradientCell (base + 285) base]) from hm19)
  have hgradAt : p.HasAt (base + 285 + 1) [writeCoreGradientCell (base + 285) base] :=
    hasAt_append_right (show p.HasAt (base + 285)
      ([detectorRefreshBody (base + 5) (base + 1)] ++ [writeCoreGradientCell (base + 285) base]) from hm19)
  have hgrad : ∀ x y z, MeetsContract w p (base + 286) (writeCoreGradientCellContract w 4 x y z) := fun x y z =>
    writeCoreGradientCell_meetsContract x y z hgradAt
      (detectorRefresh_meetsContract x y z hrefAt hsub hadd) hcopy
  have hbind := pathSlotBind_meetsContract (w := w) hm20
  have htree : ∀ (fmt : Num.Format w) (limbs : ℕ), fmt.limbBits = 4 →
      (LinkCut.PathProg.pathRep 4 limbs LinkCut.PathProg.pathC).Implements w p
        (base + 288) (fun i => base + 288 + 1 + i)
        (pathTreeMachineContract fmt limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc limbs)) := by
    intro fmt limbs hfmt
    have h := LinkCut.PathProg.pathTree_implements fmt limbs (by omega) (by omega) (hfmt.symm ▸ hm21)
    simpa only [hfmt] using h
  exact ⟨hcopy, hadd, hneg, hsub, hshift, hext, hmul, hdiv, halpha, hsel, hm10, hm11,
    hfac, hpow, hsort, hdg, hgrad, hbind, htree, hm22⟩

end MinCostFlow.MinRatio
