module

public import MinCostFlow.Final.AssemblyDryRunSCSelectRoute
public import MinCostFlow.Final.WireDeepSelectSizes
public import MinCostFlow.Final.WireTermSelectSizes
public import MinCostFlow.Final.WireTermSelectFits
public import MinCostFlow.MinRatio.WireShiftTermSelect
import MinCostFlow.Final.AssemblyDryRunSCInit
import MinCostFlow.Final.AssemblyDryRunSCRem
import MinCostFlow.MinRatio.WireShiftTerm
import MinCostFlow.MinRatio.WireSelectEvalKeyBridge
import MinCostFlow.DynSpanner.Program.DynGraphRefill
import Mathlib.Tactic

/-!
# Concrete `shiftTermChain` select-aware block and dry-run proof (`AssemblyDryRunSCTermCode`)

Packages the deterministic select-aware terminal shift (`WireShiftTermSelect.lean`,
`shiftTermSelectBody`) together with `shiftTermChainBody`, `selectRebuildLevelDBlocksBody`,
`selectRebuildLevelBody`, and their local helper procedures and modules into a relocatable
`SolverInnerSubCode` block `dryTermSelectCode` of length `78`, reusing `solverOpsProcs` for
`copyWords`, `Num.negate`, `Num.multiply`, `Num.signExtend`, `Num.shiftLeft`, `Num.integerDivide`,
`Num.isNegative`, and `LinkCut.PathProg.pathTreeBodies 4`.

Provides:
* `dryTermSelectProcs`, `dryTermSelectCode`: the 78-procedure deterministic `SolverInnerSubCode`.
* `dryInnerCodeSel_hasTermSelect_sel`: extracts all 13 individual procedure placements and all 4
  embedded module placements (`dgRefillModule`, `selectPhiFillModule`, `evalKeyModule`,
  `selectHeapOpsModule`) at `lay.shiftTermChain` inside `dryLinkedProgramSel`.
* `dryTermSelectCode_hTermSel`: proves `ShiftTermChainSyncSpecWExtKFBLSel`
  (`OrdSelSpecs.lean`) for `dryTermSelectCode` inside `dryLinkedProgramSel` with `s.termSpace`,
  `s.termFixed`, `s.toolMul`, and `s.treeMul`, preserving `solverStateRep`, `SolverLevelMetaAt`,
  `SolverLevelCapsAt`, `SolverSelectInv`, `sg'.reembPot = chainReembPot pot model'.chain`, and
  `SolverSelectRegionInv`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete 78-procedure deterministic `SolverInnerSubCode` block for `shiftTermChain` -/

/-- Fixed length (`78`) of `dryTermSelectProcs`. -/
def dryTermSelectCodeLen : ℕ := 78

/-- Concrete deterministic procedure block of length `78` placed at `env.innerBase`, implementing
`shiftTermSelectBody` (at offset `0`) and all its local helpers while reusing `solverOpsProcs`:
* `b + 0`: `shiftTermSelectBody (b + 1) (b + 4) (b + 9)`;
* `b + 1`: `shiftTermChainBody (dryPathTreeOp ops 4/1/0) (b + 2) (b + 3) (ops + 69)`;
* `b + 2`: `pathSlotBindBody`;
* `b + 3`: `wireCanonCopyBody ops (ops + 4)`;
* `b + 4`: `selectRebuildLevelDBlocksBody (b + 6) (b + 25 + 16) (b + 7)`;
* `b + 5`: `dgPackEdgeTriplesBody`;
* `b + 6`: `dgRefillFromDynGraphBody (b + 5) (b + 13 + 11)`;
* `b + 7`: `selCoreLenFillBody (b + 8)`;
* `b + 8`: `selCoreLenEdgeBody (ops + 20) (b + 12)`;
* `b + 9`: `selectRebuildLevelBody (b + 56 + 21) (b + 10)`;
* `b + 10`: `selectProcessListBody (b + 10) (b + 11)`;
* `b + 11`: `selectProcessEdgeBody (b + 42) (b + 56 + 18) (b + 56 + 20)`;
* `b + 12`: `wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops`;
* `b + 13 .. b + 24` (len `12`): `dgRefillModule (b + 13)`;
* `b + 25 .. b + 41` (len `17`): `selectPhiFillModule (b + 25) 4`;
* `b + 42 .. b + 55` (len `14`): `evalKeyModule (b + 42) 4`;
* `b + 56 .. b + 77` (len `22`): `selectHeapOpsModule (b + 56) 4`. -/
def dryTermSelectProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [shiftTermSelectBody (b + 1) (b + 4) (b + 9),
   shiftTermChainBody (dryPathTreeOp ops 4) (dryPathTreeOp ops 1) (dryPathTreeOp ops 0)
     (b + 2) (b + 3) (ops + 69),
   pathSlotBindBody,
   wireCanonCopyBody ops (ops + 4),
   selectRebuildLevelDBlocksBody (b + 6) (b + 25 + 16) (b + 7),
   dgPackEdgeTriplesBody,
   dgRefillFromDynGraphBody (b + 5) (b + 13 + 11),
   selCoreLenFillBody (b + 8),
   selCoreLenEdgeBody (ops + 20) (b + 12),
   selectRebuildLevelBody (b + 56 + 21) (b + 10),
   selectProcessListBody (b + 10) (b + 11),
   selectProcessEdgeBody (b + 42) (b + 56 + 18) (b + 56 + 20),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops] ++
  (dgRefillModule (b + 13) ++
   (selectPhiFillModule (b + 25) 4 ++
    (evalKeyModule (b + 42) 4 ++
     selectHeapOpsModule (b + 56) 4)))

theorem dryTermSelectProcs_length (env : SolverInnerEnv) :
    (dryTermSelectProcs env).length = dryTermSelectCodeLen := by
  simp only [dryTermSelectProcs, dryTermSelectCodeLen, List.length_append, List.length_cons,
    List.length_nil, dgRefillModule_length, selectPhiFillModule_length, evalKeyModule_length,
    selectHeapOpsModule_length]

theorem dryTermSelectProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ dryTermSelectProcs env, s.NoRand := by
  intro s hs
  unfold dryTermSelectProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with hHead | hRef | hPhi | hEval | hHeap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hHead
    rcases hHead with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact shiftTermSelectBody_noRand _ _ _
    · exact shiftTermChainBody_noRand _ _ _ _ _ _
    · simp [pathSlotBindBody, Stmt.NoRand]
    · exact wireCanonCopyBody_noRand _ _
    · exact selectRebuildLevelDBlocksBody_noRand _ _ _
    · exact dgPackEdgeTriplesBody_noRand
    · exact dgRefillFromDynGraphBody_noRand _ _
    · exact selCoreLenFillBody_noRand _
    · exact selCoreLenEdgeBody_noRand _ _
    · exact selectRebuildLevelBody_noRand _ _
    · exact selectProcessListBody_noRand _ _
    · exact selectProcessEdgeBody_noRand _ _ _
    · exact wireCoreLenEdgeBody_noRand _ _ _ _
  · exact dgRefillModule_noRand _ s hRef
  · exact selectPhiFillModule_noRand _ _ s hPhi
  · exact evalKeyModule_noRand _ _ s hEval
  · exact selectHeapOpsModule_noRand _ _ s hHeap

/-- Relocatable `SolverInnerSubCode` for select-aware `shiftTermChain` (`shiftTermSelectBody`). -/
def dryTermSelectCode : SolverInnerSubCode where
  procs := dryTermSelectProcs
  len := dryTermSelectCodeLen
  hlen := dryTermSelectProcs_length
  hnoRand := dryTermSelectProcs_noRand
  off := 0

/-! ## 2. Placement inside `dryLinkedProgramSel` with `dryInnerCodeSel` -/

private theorem hasAt_peel_term {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

private theorem hasAt_dryInnerCodeSel_term {p : Program} {env : SolverInnerEnv}
    (initCode coreCode selectCode deepCode : SolverInnerSubCode)
    (hInner : p.HasAt env.innerBase
      ((dryInnerCodeSel initCode coreCode selectCode dryTermSelectCode deepCode).procs env)) :
    let b := env.innerBase + (1 + initCode.len + coreCode.len + selectCode.len + 0)
    let ops := env.opsBase
    p.procs[b]? = some (shiftTermSelectBody (b + 1) (b + 4) (b + 9)) ∧
    p.procs[b + 1]? = some (shiftTermChainBody (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69)) ∧
    p.procs[b + 2]? = some pathSlotBindBody ∧
    p.procs[b + 3]? = some (wireCanonCopyBody ops (ops + 4)) ∧
    p.procs[b + 4]? = some (selectRebuildLevelDBlocksBody (b + 6) (b + 25 + 16) (b + 7)) ∧
    p.procs[b + 5]? = some dgPackEdgeTriplesBody ∧
    p.procs[b + 6]? = some (dgRefillFromDynGraphBody (b + 5) (b + 13 + 11)) ∧
    p.procs[b + 7]? = some (selCoreLenFillBody (b + 8)) ∧
    p.procs[b + 8]? = some (selCoreLenEdgeBody (ops + 20) (b + 12)) ∧
    p.procs[b + 9]? = some (selectRebuildLevelBody (b + 56 + 21) (b + 10)) ∧
    p.procs[b + 10]? = some (selectProcessListBody (b + 10) (b + 11)) ∧
    p.procs[b + 11]? = some (selectProcessEdgeBody (b + 42) (b + 56 + 18) (b + 56 + 20)) ∧
    p.procs[b + 12]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.HasAt (b + 13) (dgRefillModule (b + 13)) ∧
    p.HasAt (b + 25) (selectPhiFillModule (b + 25) 4) ∧
    p.HasAt (b + 42) (evalKeyModule (b + 42) 4) ∧
    p.HasAt (b + 56) (selectHeapOpsModule (b + 56) 4) := by
  intro b ops
  dsimp only [dryInnerCodeSel] at hInner
  obtain ⟨_, r1⟩ := hasAt_peel_term (b' := env.innerBase + 1) hInner (by simp)
  obtain ⟨_, r2⟩ := hasAt_peel_term (b' := env.innerBase + 1 + initCode.len) r1
    (by simp [initCode.hlen])
  obtain ⟨_, r3⟩ := hasAt_peel_term (b' := env.innerBase + 1 + initCode.len + coreCode.len) r2
    (by simp [coreCode.hlen])
  obtain ⟨_, r4⟩ := hasAt_peel_term
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len) r3
    (by simp [selectCode.hlen])
  obtain ⟨hTermAt, _⟩ := hasAt_peel_term
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + dryTermSelectCode.len)
    r4 (by simp [dryTermSelectCode.hlen])
  have hbEq : env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len = b := by
    dsimp only [b]; omega
  have hTermAt' : p.HasAt b (dryTermSelectProcs { env with innerBase := b }) := by
    have h1 := hTermAt
    change p.HasAt (env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len)
      (dryTermSelectProcs { env with
        innerBase := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len }) at h1
    rw [hbEq] at h1
    exact h1
  unfold dryTermSelectProcs at hTermAt'
  dsimp only at hTermAt'
  obtain ⟨hHead, m1⟩ := hasAt_peel_term (b' := b + 13) hTermAt' (by simp)
  obtain ⟨hRefAt, m2⟩ := hasAt_peel_term (b' := b + 25) m1 (by rw [dgRefillModule_length])
  obtain ⟨hPhiAt, m3⟩ := hasAt_peel_term (b' := b + 42) m2 (by rw [selectPhiFillModule_length])
  obtain ⟨hEvalAt, hHeapAt⟩ := hasAt_peel_term (b' := b + 56) m3 (by rw [evalKeyModule_length])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRefAt, hPhiAt, hEvalAt, hHeapAt⟩
  · have h0 := hHead 0 (by simp); rw [Nat.add_zero] at h0; exact h0
  · exact hHead 1 (by simp)
  · exact hHead 2 (by simp)
  · exact hHead 3 (by simp)
  · exact hHead 4 (by simp)
  · exact hHead 5 (by simp)
  · exact hHead 6 (by simp)
  · exact hHead 7 (by simp)
  · exact hHead 8 (by simp)
  · exact hHead 9 (by simp)
  · exact hHead 10 (by simp)
  · exact hHead 11 (by simp)
  · exact hHead 12 (by simp)

/-- Extracts all 13 individual procedure placements and all 4 embedded module placements of
`dryTermSelectCode` inside `dryLinkedProgramSel` with `dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hasTermSelect_sel (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode selectCode dryTermSelectCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.shiftTermChain
    let ops := mrdsCycleBase
    p.procs[b]? = some (shiftTermSelectBody (b + 1) (b + 4) (b + 9)) ∧
    p.procs[b + 1]? = some (shiftTermChainBody (dryPathTreeOp ops 4) (dryPathTreeOp ops 1)
      (dryPathTreeOp ops 0) (b + 2) (b + 3) (ops + 69)) ∧
    p.procs[b + 2]? = some pathSlotBindBody ∧
    p.procs[b + 3]? = some (wireCanonCopyBody ops (ops + 4)) ∧
    p.procs[b + 4]? = some (selectRebuildLevelDBlocksBody (b + 6) (b + 25 + 16) (b + 7)) ∧
    p.procs[b + 5]? = some dgPackEdgeTriplesBody ∧
    p.procs[b + 6]? = some (dgRefillFromDynGraphBody (b + 5) (b + 13 + 11)) ∧
    p.procs[b + 7]? = some (selCoreLenFillBody (b + 8)) ∧
    p.procs[b + 8]? = some (selCoreLenEdgeBody (ops + 20) (b + 12)) ∧
    p.procs[b + 9]? = some (selectRebuildLevelBody (b + 56 + 21) (b + 10)) ∧
    p.procs[b + 10]? = some (selectProcessListBody (b + 10) (b + 11)) ∧
    p.procs[b + 11]? = some (selectProcessEdgeBody (b + 42) (b + 56 + 18) (b + 56 + 20)) ∧
    p.procs[b + 12]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.HasAt (b + 13) (dgRefillModule (b + 13)) ∧
    p.HasAt (b + 25) (selectPhiFillModule (b + 25) 4) ∧
    p.HasAt (b + 42) (evalKeyModule (b + 42) 4) ∧
    p.HasAt (b + 56) (selectHeapOpsModule (b + 56) 4) := by
  intro inner p lay b ops
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  exact hasAt_dryInnerCodeSel_term initCode coreCode selectCode deepCode hInner

/-! ## 3. Dry-run terminal shift execution theorem (`dryTermSelectCode_hTermSel`) -/

set_option maxHeartbeats 1200000 in
/-- **Dry-run terminal shift spec (`ShiftTermChainSyncSpecWExtKFBLSel`) for `dryTermSelectCode`.**
Discharges every helper contract (using `selectRebuildLevel_meetsContract_noRoom`), fit bound,
level-`d` potential bound (`selectPhiBoundedAt_of_phiFill`), space bound, and step-cost bound
from `dryTermSelectSpace`/`dryTermSelectFixed` (`WireTermSelectSizes.lean`),
`WireSelectDryFits.lean`, and `WireTermSelectFits.lean` inside `dryLinkedProgramSel`. -/
theorem dryTermSelectCode_hTermSel
    (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode deepCode selInitCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz)
    (pot : (source J : Circulation) →
      (concreteCirculationCfgWithLast dryWitnessUsed J).T.State → ℕ)
    (hTermSpLe : ∀ source J, dryTermSelectSpace source J ≤ selSz.termSelectSpace source J)
    (hTermFxLe : ∀ source J, dryTermSelectFixed source J ≤ selSz.termSelectFixed source J) :
    let inner := dryInnerCodeSel initCode coreCode selectCode dryTermSelectCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let coeff := dryAllocCoeffConcrete Psc openSz hOpen selSz hSel
    let deg := dryAllocDegConcrete Psc openSz hOpen selSz hSel
    ForAllDryInputs dryWitnessUsed coeff deg fun source J hw =>
      let W := dryWitnessUsed
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
        (concreteQualityBudgetWithLast W) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast W J
      let G := namedInstance I
      let w := dryWordSize W coeff deg source
      let Rcore := drySCRep Psc coeff deg source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      ShiftTermChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
        dryCapExp (concreteReadout2LimbMul W) (dryCapLimit W J) (2 * levelM cfg.TP cfg.P cfg.P.d)
        G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) F.rangeExponent
        (dryLastStretchP J) (drySlot I.m) cfg G (pot source J)
        (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).shiftTermChain
        s.termSpace s.termFixed s.toolMul s.treeMul := by
  intro inner p coeff deg source J hJn hJm hCost hCap hw
  dsimp only
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let cfg := concreteCirculationCfgWithLast W J
  let G := namedInstance I
  let w := dryWordSize W coeff deg source
  let Rcore := drySCRep Psc coeff deg source J hw
  let Rrep := solverStateRep cfg F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
    (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) Rcore
  let s := dryInnerSizesWithSelect Psc openSz selSz source J
  let lay := dryTailLay Psc.sc inner
  let b := lay.shiftTermChain
  let ops := mrdsCycleBase
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCap1
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw10 : 10 ≤ w := by omega
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hLpos : 0 < F.limbs := by
    change 0 < ipmQualityLimbs I.m V k; unfold ipmQualityLimbs; omega
  have hL4W : 4 * F.limbs + 2 < 2 ^ w := by
    have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
      have hsz := Nat.lt_size_self (ipmQualityParameterBound I.m V k)
      calc 2 ^ 14 * ipmQualityParameterBound I.m V k
          < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
            Nat.mul_lt_mul_of_pos_left hsz (by decide)
        _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    omega
  have hLW : F.limbs < 2 ^ w := by omega
  have hpLast40 : dryLastStretchP J ≤ 40 * F.rangeExponent := by
    have h1 : (1024 * ⌈max 1 lastCanonConst⌉₊).size +
        3 * (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤ 40 * F.rangeExponent :=
      dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap1
    have h2 : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (by omega)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size ≤ 40 * F.rangeExponent
    omega
  have hpLastW : dryLastStretchP J < 2 ^ w := by
    have h4L : F.fmt.precision + 92 * F.rangeExponent + 12 * I.m.size + 1480 ≤ 4 * F.limbs := by
      change ipmQualityPrecision I.m V k + 92 * ipmQualityRangeExponent I.m V k +
        12 * I.m.size + 1480 ≤ 4 * ipmQualityLimbs I.m V k
      unfold ipmQualityLimbs ipmQualityPrecision ipmQualityErrorBits; omega
    omega
  obtain ⟨hSelAt, hTermAt, hBindAt, hCanonAt, hRebDAt, hPackAt, hRefillAt, hFillAt, hEdgeAt,
    hRebLvlAt, hProcListAt, hProcEdgeAt, hWireEdgeAt, hRefMod, hPhiMod, hEvalMod, hHeapMod⟩ :=
    dryInnerCodeSel_hasTermSelect_sel Psc initCode coreCode selectCode deepCode selInitCode
  have hOpsAt := dryLinkedProgramSel_ops_hasAt W Psc.sc inner selInitCode
  have hInitH := solverOpsProcs_initHelpers hw14 hOpsAt
  have hEvalH := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl hOpsAt
  have hBindHasAt : p.HasAt (b + 2) [pathSlotBindBody] := by
    intro idx hidx; have h0 : idx = 0 := by simp at hidx; omega
    subst h0; simpa using hBindAt
  have hTermSpec : ShiftTermChainSyncSpecWExt w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
      dryCapExp (concreteReadout2LimbMul W) (dryCapLimit W J) (2 * levelM cfg.TP cfg.P cfg.P.d)
      cfg Rcore p (b + 1)
      ((2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs))
      (41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320)
      0 (wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2) :=
    shiftTermChainBody_meets_spec hTermAt (drySCRep_local Psc coeff deg source J hw)
      rfl hLpos hL4W hEvalH.2.2.2.2.2 (pathSlotBind_meetsContract hBindHasAt)
      (fun v => wireCanonCopy_meetsContract v hCanonAt hEvalH.1 hEvalH.2.2.1) hEvalH.2.2.2.2.1
  have hCoreLenEdge : MeetsContract w p (b + 8) (selCoreLenEdgeContract w F.fmt.precision) :=
    selCoreLenEdge_meetsContract hEdgeAt hInitH.2.2.2.2.2.1 hWireEdgeAt
      hInitH.2.2.2.2.1 hInitH.2.2.1 hInitH.2.2.2.2.2.2.1 hInitH.1
  refine ⟨_, hSelAt, ?_⟩
  intro root heap pos ω mem0 mem model tok sg B_num R_num
  dsimp only
  set model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
  intro hRep0 hMeta0 hCapsAt0 hLay0 _ hPot0 hSelReg0 hShift0 hGrid0 hMemEq hSched' hNum0 hOff0
    hOffBd0 hCapF hBranLt hLastBranLt hLastKW hLogW hCapT hNewForest hOldSub hNewSub hDisjPref
    hLastCap hBelow hz hRoom
  obtain ⟨⟨B, hSlotEq, hSel0⟩, hPhiBd0, hg0⟩ := hSelReg0
  have hCaps0 : SolverLevelCapsInv F.fmt.precision V G.n (initTargetCap cfg G) model tok mem0 :=
    ⟨hMeta0, hCapsAt0⟩
  have hBd : B.d = cfg.P.d := hSel0.1
  have hBe : B.eCap = initTargetCap cfg G := hSel0.2.2.1
  have hBLk : B.Lk = F.limbs := hSel0.2.2.2.1
  have hCapEq : sg.loc.cap = selectHeapCap cfg G I.m := hSel0.2.2.2.2.1
  have hBlocks0 := hSel0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hShift' : Chain.Ordered.ShiftLoopChainInv cfg model'.chain :=
    hShift0.shift hV cfg.P.d le_rfl
  have hGrid' : DryChainLenGridInv J model'.chain :=
    dryChainLenGridInv_shift J hJn hJm hCap1 hShift0 hGrid0 le_rfl
  have hDy' : DryLastWstrDyadic J model'.chain :=
    dryLastWstrDyadic_of_gridInv J hGrid'
  have hTH' := hShift'.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk
  have hChGeq : ∀ j, model'.chain.G j = model.chain.G j := fun j => by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hChgeq : model'.chain.g = model.chain.g := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hMod' : SelectModelInv model' (model'.chain.G 0)
      (max (cfg.TP.σ cfg.P.k (model'.chain.G 0).n) (cfg.LP.σ_last (model'.chain.G 0).n))
      (max (cfg.σ_mwu (model'.chain.G 0).n) (cfg.LP.σ_mwu (model'.chain.G 0).n))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) := by
    obtain ⟨_, _, _, _, _, hMod0⟩ := hSel0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨hTH'.1, hTH'.2.1, hShift'.1.hBran, fun j hj => ?_, hMod0.2.2.2.2.1, hMod0.2.2.2.2.2⟩
    have hOrdEq : chainLevelOrdAbs model'.chain j = chainLevelOrdAbs model.chain j := by
      simp [chainLevelOrdAbs, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
        ChainState.levelOrd]; rfl
    have hLvlEq : model'.chain.lvlM j = model.chain.lvlM j := by
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
    have hN0Eq : model'.chain.N₀ = model.chain.N₀ := by
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
    rw [hOrdEq, hLvlEq, hN0Eq]
    exact hMod0.2.2.2.1 j hj
  have hg' : ∀ e ∈ (model'.chain.G 0).E, |model'.chain.g e| ≤ (2 : ℝ) ^ F.rangeExponent := by
    simpa [hChGeq 0, hChgeq] using hg0
  have hGdSize : (model.chain.G cfg.P.d).n ≤ levelM cfg.TP cfg.P cfg.P.d + 1 ∧
      (model.chain.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    have hB := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hγM₀ hV.hγk hShift0.1
    have hmd : (model.chain.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
      exact_mod_cast (hB cfg.P.d le_rfl).2.2.1
    have hnd : (model.chain.G cfg.P.d).n ≤ (model.chain.G cfg.P.d).m + 1 :=
      hShift0.levels_n_le hV cfg.P.d le_rfl
    exact ⟨by omega, hmd⟩
  have hGdCapHeap : ∀ e ∈ (model.chain.G cfg.P.d).E, e < sg.loc.cap := fun e he => by
    have h1 : e < initTargetCap cfg G := by
      have := hBlocks0.2.1 cfg.P.d (hBd.symm ▸ le_rfl) e he
      rw [hBe] at this; exact this
    have hGm : G.m = I.m := namedInstance_m I
    rw [hCapEq]; unfold selectHeapCap initTargetCap at *; omega
  have hMle40 : (2 : ℝ) ^ F.rangeExponent ≤ (2 : ℝ) ^ (40 * F.rangeExponent) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hMle80 : (2 : ℝ) ^ F.rangeExponent ≤ (2 : ℝ) ^ (80 * F.rangeExponent) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hPhiFits := dry_phiFillFits_of_shiftLoop J hJn hJm hCap1 hShift'
    (by simpa [hChGeq 0] using hGrid0.2.1) le_rfl (by positivity) hMle80 hg'
    (fun r hr v hv => hPhiBd0 r (Nat.le_of_lt hr) v (by simpa [ChainState.toTreeChain, hChGeq r] using hv))
  have hCandFits : CandidateKeysFit 4 F.fmt.precision (dryLastStretchP J) F.limbs
      model'.chain.toTreeChain model'.chain.g model'.chain.ℓ :=
    dry_candidateKeysFit_of_shiftLoop J hJn hJm hCap1 hShift' hGrid' hpLast40
      (by positivity) hMle40 hg'
  have hCandFitsMloc : CandidateKeysFit 4 F.fmt.precision
      (selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) (dryLastStretchP J)).pLast
      (selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) (dryLastStretchP J)).Lk
      model'.chain.toTreeChain model'.chain.g model'.chain.ℓ := by
    dsimp only [selectMlocOf]; rw [hBLk]; exact hCandFits
  have hEmbBd : ∀ lvl < model'.chain.toTreeChain.d,
      ∀ e ∈ (model'.chain.toTreeChain.activeCore lvl).E \ (model'.chain.toTreeChain.activeS lvl).E,
        (model'.chain.toTreeChain.activeEmb lvl e).length ≤ dryMaxEmbLen I.m :=
    fun lvl hlvl e he =>
      embLen_le_of_holds hTH'.1 (dryWitnessUsed_gammaEll_le_dryMaxEmbLen J hJn hJm hCap1)
        lvl hlvl e (Finset.mem_sdiff.mp he).1
  have hLenFits := dry_levelD_lenFits_of_shiftLoop J hJn hJm hCap1 hShift' hGrid' hDy'
  have hSpTermLe : termSelectSpace cfg.P.d (levelM cfg.TP cfg.P cfg.P.d + 1)
      (levelM cfg.TP cfg.P cfg.P.d) sg.loc.cap F.limbs
      (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs) ≤ selSz.termSelectSpace source J := by
    rw [hCapEq]
    exact (termSelectSpace_le_dryTermSelectSpace source J le_rfl le_rfl).trans (hTermSpLe source J)
  have hFxTermLe : termSelectFixed cfg.P.d (levelM cfg.TP cfg.P cfg.P.d + 1)
      (levelM cfg.TP cfg.P cfg.P.d) sg.loc.cap F.limbs
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) ≤ selSz.termSelectFixed source J := by
    rw [hCapEq]
    exact (termSelectFixed_le_dryTermSelectFixed source J le_rfl le_rfl).trans (hTermFxLe source J)
  have hHeapOps := selectHeapOpsModule_meetsContracts (w := w) (h := 4) (by decide) (by omega)
    hHeapMod sg.loc
  have hFitsE : ∀ e ∈ (model'.chain.lastLSFs model'.chain.lastBran).F.F.E,
      PotGradEvalFits 4 F.limbs F.fmt.precision model'.chain.toTreeChain model'.chain.g sg.φ cfg.P.d e := by
    intro e he
    exact hPhiFits.1 e (by simpa [TreeChain.activeLSF, ChainState.toTreeChain] using he)
  have hFitsW : ForestWalkFits 4 F.limbs F.fmt.precision (model'.chain.lastLSFs model'.chain.lastBran).F.F
      (potGrad model'.chain.toTreeChain model'.chain.g sg.φ cfg.P.d) := by
    have h2 := hPhiFits.2
    dsimp only [TreeChain.activeLSF, ChainState.toTreeChain] at h2
    simp only [lt_irrefl, ↓reduceIte] at h2
    exact h2
  have hRoom' : heap + s.termSpace < 2 ^ w := hRoom
  have hRun := shiftTermSelectBody_runs
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V) (psi := ⌈cfg.Ψ⌉₊)
    (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (drainUnit := detectOffTreeDrainUnit F.limbs) (capExp := dryCapExp)
    (limbMul := concreteReadout2LimbMul W) (capLimit := dryCapLimit W J)
    (lastTreeCap := 2 * levelM cfg.TP cfg.P cfg.P.d) (vCap := G.n) (eCap := initTargetCap cfg G)
    (pLast := dryLastStretchP J)
    (termSpace := (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs))
    (termFixed := 41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320)
    (toolMul := 0) (treeMul := wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2)
    (nD := levelM cfg.TP cfg.P cfg.P.d + 1) (mD := levelM cfg.TP cfg.P cfg.P.d)
    (evalSpace := evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
    (evalCost := evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)
    (shiftTermChainProc := b + 1) (rebuildLevelDProc := b + 4) (refillDGProc := b + 6)
    (phiFillProc := b + 25 + 16) (coreLenFillProc := b + 7) (coreLenEdgeProc := b + 8)
    (rebuildHeapLvlProc := b + 9) (root := root) (heap := heap) (pos := pos)
    (cfg := cfg) (G := G) (Rcore := Rcore) (p := p) (ω := ω) (B := B)
    (model := model) (tok := tok) (sg := sg) (mem0 := mem0) (mem := mem)
    (B_num := B_num) (R_num := R_num)
    (drySCRep_local Psc coeff deg source J hw)
    hTermSpec hRebDAt hFillAt hCoreLenEdge
    (fun vcLast ecLast =>
      dgRefillFromDynGraph_meetsContract hRefillAt
        (dgPackEdgeTriples_meetsContract hPackAt)
        (fun _ _ => dgRefillModule_meetsContract hRefMod))
    (selectPhiFillModule_meetsContract (by decide) (by omega) hPhiMod)
    (fun φ' =>
      selectRebuildLevel_meetsContract_noRoom hRebLvlAt hHeapOps.2.2.2.2.2.2.2.2.2.2
        (fun _ => selectProcessList_meetsContract_noRoom hProcListAt
          (by
            have hPE := selectProcessEdge_meetsContract_evalKey
              (mloc := selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) (dryLastStretchP J))
              (φ := φ') (coreLen := fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
              hProcEdgeAt hEvalMod (by decide) (by omega)
              hTH'.1 hTH'.2.1 hShift'.1.hℓPos hEmbBd hCandFitsMloc
              hHeapOps.2.2.2.2.2.2.2.1 hHeapOps.2.2.2.2.2.2.2.2.2.1
            have hLkEq : (selectMlocOf B sg.loc.metaPtr (solverLevelG tok mem0) (dryLastStretchP J)).Lk = F.limbs :=
              hBLk
            rw [hLkEq] at hPE
            exact hPE)))
    hw16 hw10 hpLastW hLW hRep0 hCaps0 hSel0 hMemEq hSched' hNum0 hOff0 hOffBd0
    hCapF hBranLt hLastBranLt hLastKW hLogW hCapT hNewForest hOldSub hNewSub hDisjPref hLastCap
    hMod' hGdSize hGdCapHeap hFitsE hFitsW hLenFits hBelow hz
    (by
      have hts : s.termSpace = (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs) +
          selSz.termSelectSpace source J := rfl
      omega)
  obtain ⟨nextHeap, cost, out, tok', sg', hRuns, hLo, hHi, hLevEq, hIntCapEq, hTabEq, hRootECapEq,
    hRep', hCaps', hLay', hSelB', hSelI', hOwnEq, hReembSame, hPhiLt', hPhiD', hNum', hOff', hOffBd', hz',
    hFr', hFoot', hCost'⟩ := hRun
  have hReembEq : sg'.reembPot = chainReembPot (pot source J) model'.chain := by
    rw [hReembSame, hPot0]
    exact (termShift_chainReembPot_eq (pot source J) model).symm
  have hPotInv' : SelectPotInv model'.chain.toTreeChain model'.chain.g sg'.φ :=
    hSelB'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hChℓeq : model'.chain.ℓ = model.chain.ℓ := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hPhiBd' := dry_selectPhiBoundedAt_of_termShift (by positivity) (hChℓeq ▸ hTH'.1) hGrid0.2.1 hg0
    (by simpa [hChgeq] using hPotInv') (fun r hr => hPhiBd0 r (Nat.le_of_lt hr))
    hPhiLt' hPhiD'
  have hSelReg' : SolverSelectRegionInv G F.limbs F.fmt.precision I.m F.rangeExponent
      (dryLastStretchP J) (drySlot I.m) G.n (initTargetCap cfg G) model'
      (Rrep.foot root tok') tok' sg' out.mem :=
    ⟨⟨B, hSlotEq, hSelB'⟩, hPhiBd', hg'⟩
  refine ⟨nextHeap, cost, out, tok', sg', hRuns, hLo, ?_, hLevEq, hIntCapEq, hTabEq, hRootECapEq,
    hRep', hCaps'.1, hCaps'.2, hLay' hLay0, hSelI', hReembEq, hSelReg', hNum', hOff', hOffBd', hz',
    fun a ha hnot => hFr' a ha (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h)),
    fun a ha => by
      rcases ha with hf | ho
      · exact (hFoot' a hf).imp Or.inl id
      · exact Or.inl (Or.inr (hOwnEq ▸ ho)), ?_⟩
  · change nextHeap ≤ heap + s.termSpace
    have hts : s.termSpace = (2 * levelM cfg.TP cfg.P cfg.P.d) * (2 + wireTreeSyncEditSpace F.limbs) +
        selSz.termSelectSpace source J := rfl
    omega
  · change cost + Rrep.phi root tok' out.mem + selSz.keyCost source J * sg'.reembPot ≤
      s.termFixed +
        s.toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        s.treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        Rrep.phi root tok mem0 + selSz.keyCost source J * sg.reembPot
    have hCost'' : cost + Rrep.phi root tok' out.mem ≤
        41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 +
          termSelectFixed cfg.P.d (levelM cfg.TP cfg.P cfg.P.d + 1) (levelM cfg.TP cfg.P cfg.P.d)
            sg.loc.cap F.limbs (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) +
          0 * (model'.chain.totalRuntime - model.chain.totalRuntime) +
          (wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2) *
            (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
          Rrep.phi root tok mem0 := hCost'
    have htf : s.termFixed = 41 * (2 * levelM cfg.TP cfg.P cfg.P.d) + 320 +
        selSz.termSelectFixed source J := rfl
    have htmLe : wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤ s.treeMul := by
      change wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 ≤
        wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2 +
          openSz.coreTreeMul source J
      omega
    have htmMul := Nat.mul_le_mul_right (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) htmLe
    rw [hReembEq, hPot0, termShift_chainReembPot_eq (pot source J) model]
    have h0 : 0 * (model'.chain.totalRuntime - model.chain.totalRuntime) = 0 := Nat.zero_mul _
    omega

/-! ## 4. Theorem 1.1 assembly theorem with `dryTermSelectCode` plugged in -/

/-- **Unified Theorem 1.1 (page 2) assembly theorem with `dryTermSelectCode` and `hTermSel`
discharged (alongside `dryDeepSelectCode` and `hDeepSel`).** Instantiates
`theorem_1_1_skeleton_kfbl_sel` with `termCode := dryTermSelectCode` and
`hTermSel := dryTermSelectCode_hTermSel ...`, leaving only the sparse-core first-phase pieces and
`hInitSel`, `hCoreSel`. -/
theorem theorem_1_1_skeleton_kfbl_sel_term
    (firstStep firstInit : ScSubCode)
    (C : ScFirstConsts)
    (hC : C.firstWordExp 3 ≤ 39)
    (hFirstStep :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JS : AsmBrCoreStepAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
              sparsifyImplUsed depth fmt.precision L_in capExp limbMul
              (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreS,
            JS.mul = C.stepMul capExp limbMul ∧
            JS.ysMul = C.stepYs capExp limbMul ∧
            JS.spaceP = C.stepSpace capExp)
    (hFirstInit :
      let L := scLayout sparsifyImplUsed dryCompCode firstStep firstInit
      let p := scProg sparsifyImplUsed dryCompCode firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
            p dryCompCode.fInit dryCompCode.fBatch),
          fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
          ∃ JI : AsmBrCoreInitAt
              (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
              (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
              limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
            JI.mul = C.initMul capExp limbMul ∧
            JI.space = C.initSpace capExp)
    (coreCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (hCoreSel :
      let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
      let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
      let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
      let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc) (dryShiftSelectSizeBounds Psc)
      let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode drySelectRouteCode
        dryTermSelectCode dryDeepSelectCode
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
        let s := dryInnerSizesWithSelect Psc openSz selSz source J
        OrdChainUpdateCoreSpecWKFBLSel
          (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
            (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
          F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs)
          dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J)
          (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
          4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J)
          (DryChainLenGridInv J) Rcore p (dryTailLay Psc.sc inner).ordChainCore
          s.coreSpace s.coreFixed s.toolMul s.treeMul) :
    MinCostFlowStatement := by
  let Psc := mkDrySparseCorePieces firstStep firstInit C hC hFirstStep hFirstInit
  let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
  let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
  let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc) (dryShiftSelectSizeBounds Psc)
  exact theorem_1_1_skeleton_kfbl_sel firstStep firstInit C hC hFirstStep hFirstInit
    coreCode dryTermSelectCode coreSz hCore hCoreSel
    (dryTermSelectCode_hTermSel Psc (dryInitCode (dryParamCode Psc)) coreCode drySelectRouteCode
      dryDeepSelectCode drySelInitCode openSz hOpen selSz hSel (fun _ J => dryPot J)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl))

end MinCostFlow.Final.DryRun

end
