module

public import MinCostFlow.Spanner.ProgWitnessPrepProof
public import MinCostFlow.Spanner.ProgEmbStats
public import MinCostFlow.Spanner.WitnessLift

/-!
# Deterministic Word-RAM Witness Builder Core (`ProgBuildWitness`)

Defines `buildWitnessCoreBody`, the Word-RAM procedure that reads the outputs of `embStats`,
`Decompose`, and `witnessPrep` and constructs the Task 1 witness graph `W`, common-denominator
edge weights `wWNum`, `wSources`, `jSources`, `PathDS` parameter bounds (`phiDsDen`, `γExpInt`,
`γDelInt`, `τ₁_int`, `τ₂_int`), and the extended component table `compExt` in memory.

Also defines `WitnessCoreInput`, the memory layout predicates (`WSourcesAt`, `JSourcesAt`,
`CompExtAt`, `WitnessCoreOut`), and the mathematical constructor `mkWitnessData` used to prove
`WitnessOK` and `MeetsContract` in downstream modules.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. Word-RAM Program `buildWitnessCoreModule` -/

/-- Phase 0 + Phase 1: loads Graph/Stats/Decompose/Prep scalars, computes `M_W, d_J, d_W`, calls
`PathDS.boundsProcs` twice, computes `phiDsDen, γExpInt, γDelInt, τ₁_int, τ₂_int`, stores the
initial `WitnessHdr` fields `0..12, 17..19`, and initializes `r18 = aCompExt`, `r17 = curH`. -/
def buildPhase01Stmt (cePhiNum cePhiDen ceCDegInt boundsBase : ℕ) : Stmt :=
  let dW := (cePhiDen + cePhiNum - 1) / cePhiNum
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.load (.reg 1)) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 9 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 10 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.const 2))) ;;
  .assign 12 (.load (.reg 3)) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .assign 14 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .assign 15 (.load (.bin .add (.reg 3) (.const 3))) ;;
  .assign 16 (.bin .sub (.reg 13) (.load (.bin .add (.reg 3) (.const 5)))) ;;
  .assign 17 (.bin .add (.reg 4) (.const 20)) ;;
  .assign 19 (.bin .add (.bin .div
    (.bin .add (.bin .mul (.const (2 * ceCDegInt)) (.bin .mul (.reg 16) (.reg 11)))
      (.bin .sub (.reg 10) (.const 1)))
    (.reg 10)) (.const 1)) ;;
  .store (.reg 4) (.reg 19) ;;
  .store (.bin .add (.reg 4) (.const 17)) (.reg 10) ;;
  .store (.bin .add (.reg 4) (.const 18)) (.reg 11) ;;
  .store (.bin .add (.reg 4) (.const 19)) (.reg 16) ;;
  .assign 20 (.bin .div (.bin .add (.reg 11) (.bin .sub (.reg 10) (.const 1))) (.reg 10)) ;;
  .assign 21 (.const dW) ;;
  .call 22 boundsBase [.reg 20, .reg 16, .reg 17] ;;
  .assign 23 (.load (.reg 17)) ;;
  .assign 24 (.load (.bin .add (.reg 17) (.const 1))) ;;
  .assign 25 (.load (.bin .add (.reg 17) (.const 2))) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 23) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 24) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.reg 25) ;;
  .assign 17 (.reg 22) ;;
  .call 22 boundsBase [.reg 21, .reg 19, .reg 17] ;;
  .assign 26 (.load (.reg 17)) ;;
  .assign 27 (.load (.bin .add (.reg 17) (.const 1))) ;;
  .assign 28 (.load (.bin .add (.reg 17) (.const 2))) ;;
  .store (.bin .add (.reg 4) (.const 4)) (.reg 26) ;;
  .store (.bin .add (.reg 4) (.const 5)) (.reg 27) ;;
  .store (.bin .add (.reg 4) (.const 6)) (.reg 28) ;;
  .assign 17 (.reg 22) ;;
  .cond (.bin .lt (.reg 23) (.reg 26)) (.assign 23 (.reg 26)) (.assign 23 (.reg 23)) ;;
  .cond (.bin .lt (.reg 24) (.reg 27)) (.assign 24 (.reg 27)) (.assign 24 (.reg 24)) ;;
  .cond (.bin .lt (.reg 25) (.reg 28)) (.assign 25 (.reg 28)) (.assign 25 (.reg 25)) ;;
  .store (.bin .add (.reg 4) (.const 7)) (.reg 23) ;;
  .store (.bin .add (.reg 4) (.const 8)) (.reg 24) ;;
  .store (.bin .add (.reg 4) (.const 9)) (.reg 25) ;;
  .assign 27 (.bin .mul (.bin .mul (.reg 24) (.reg 25)) (.reg 23)) ;;
  .store (.bin .add (.reg 4) (.const 11)) (.reg 27) ;;
  .assign 26 (.bin .mul (.bin .mul (.bin .mul (.const 2) (.reg 27)) (.reg 8))
    (.bin .add (.reg 9) (.reg 7))) ;;
  .store (.bin .add (.reg 4) (.const 10)) (.reg 26) ;;
  .assign 18 (.reg 17) ;;
  .store (.bin .add (.reg 4) (.const 12)) (.reg 18) ;;
  .assign 17 (.bin .add (.reg 17) (.bin .mul (.const 6) (.reg 14)))

/-- Inner weight-vector builder for component `ci` in `buildCeLoopStmt`. -/
def buildWeightFillBody : Stmt :=
  .assign 31 (.load (.bin .add (.reg 27) (.reg 30))) ;;
  .assign 31 (.bin .div
    (.bin .add (.bin .mul (.reg 31) (.reg 11)) (.bin .sub (.reg 29) (.const 1)))
    (.reg 29)) ;;
  .store (.bin .add (.reg 17) (.reg 30)) (.reg 31)

/-- Loop body for component `ci` calling `ConstructExpander(kCard, curH, curH + kCard)` and
recording `compExt[ci] = [wStart, wSubPtr, shift, wWeightNum, kCard, W_sub.m]`. -/
def buildCeBody (ceBase : ℕ) : Stmt :=
  .assign 24 (.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 22))) ;;
  .assign 25 (.load (.reg 24)) ;;
  .assign 26 (.load (.bin .add (.reg 24) (.const 1))) ;;
  .assign 27 (.load (.bin .add (.reg 24) (.const 5))) ;;
  .assign 28 (.bin .shiftLeft (.const 1) (.reg 25)) ;;
  .assign 29 (.bin .mul (.reg 10) (.reg 28)) ;;
  .assign 30 (.const 0) ;;
  forUp 30 (.reg 26) buildWeightFillBody ;;
  .assign 30 (.bin .add (.reg 17) (.reg 26)) ;;
  .call 31 ceBase [.reg 26, .reg 17, .reg 30] ;;
  .assign 32 (.load (.bin .add (.reg 30) (.const 1))) ;;
  .assign 33 (.bin .add (.reg 18) (.bin .mul (.const 6) (.reg 22))) ;;
  .store (.reg 33) (.reg 23) ;;
  .store (.bin .add (.reg 33) (.const 1)) (.reg 30) ;;
  .store (.bin .add (.reg 33) (.const 2)) (.reg 28) ;;
  .store (.bin .add (.reg 33) (.const 3)) (.reg 29) ;;
  .store (.bin .add (.reg 33) (.const 4)) (.reg 26) ;;
  .store (.bin .add (.reg 33) (.const 5)) (.reg 32) ;;
  .assign 23 (.bin .add (.reg 23) (.reg 32)) ;;
  .assign 17 (.reg 31)

/-- Phase 2: constructs every component expander `W_sub` and populates `compExt`. -/
def buildCeLoopStmt (ceBase : ℕ) : Stmt :=
  .assign 23 (.reg 12) ;;
  forRange 22 (.const 0) (.reg 14) (buildCeBody ceBase)

/-- Level-0 loop body assembling `j0Edges` into `W`, `wWNum`, `wSources`, and `jSources`. -/
def buildJ0AsmBody : Stmt :=
  .assign 30 (.load (.bin .add (.reg 13) (.reg 29))) ;;
  .assign 31 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 30))))) ;;
  .assign 32 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 30))))) ;;
  .store (.bin .add (.reg 24) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 29)))) (.reg 31) ;;
  .store (.bin .add (.reg 24) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 29)))) (.reg 32) ;;
  .store (.bin .add (.reg 25) (.reg 29)) (.reg 10) ;;
  .store (.bin .add (.reg 26) (.bin .mul (.const 3) (.reg 29))) (.const 0) ;;
  .store (.bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 29)) (.const 1))) (.reg 30) ;;
  .store (.bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 29)) (.const 2))) (.const 0) ;;
  .store (.bin .add (.reg 27) (.bin .mul (.const 3) (.reg 30))) (.const 1) ;;
  .store (.bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 30)) (.const 1))) (.reg 29) ;;
  .store (.bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 30)) (.const 2))) (.const 0)

/-- Component edge loop body writing `W` edges, `wWNum`, and `wSources` from `W_sub`. -/
def buildCompWEdgesBody : Stmt :=
  .assign 38 (.load (.bin .add (.reg 34) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 37))))) ;;
  .assign 39 (.load (.bin .add (.reg 34) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 37))))) ;;
  .assign 38 (.load (.bin .add (.reg 30) (.reg 38))) ;;
  .assign 39 (.load (.bin .add (.reg 30) (.reg 39))) ;;
  .assign 40 (.bin .add (.reg 33) (.reg 37)) ;;
  .store (.bin .add (.reg 24) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 40)))) (.reg 38) ;;
  .store (.bin .add (.reg 24) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 40)))) (.reg 39) ;;
  .store (.bin .add (.reg 25) (.reg 40)) (.reg 35) ;;
  .store (.bin .add (.reg 26) (.bin .mul (.const 3) (.reg 40))) (.const 1) ;;
  .store (.bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 40)) (.const 1))) (.reg 29) ;;
  .store (.bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 40)) (.const 2))) (.reg 37)

/-- Component original-edge loop body recording `inComp ci jL` into `jSources`. -/
def buildCompJOrigBody : Stmt :=
  .assign 38 (.load (.bin .add (.reg 31) (.reg 37))) ;;
  .store (.bin .add (.reg 27) (.bin .mul (.const 3) (.reg 38))) (.const 2) ;;
  .store (.bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 38)) (.const 1))) (.reg 29) ;;
  .store (.bin .add (.reg 27) (.bin .add (.bin .mul (.const 3) (.reg 38)) (.const 2))) (.reg 37)

/-- Outer component loop body for assembling `W`, `wWNum`, `wSources`, and `jSources`. -/
def buildCompAsmBody : Stmt :=
  .assign 30 (.load (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 7) (.reg 29))))) ;;
  .assign 31 (.load (.bin .add (.reg 15) (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 29))))) ;;
  .assign 32 (.load (.bin .add (.reg 15) (.bin .add (.const 6) (.bin .mul (.const 7) (.reg 29))))) ;;
  .assign 33 (.load (.bin .add (.reg 18) (.bin .mul (.const 6) (.reg 29)))) ;;
  .assign 34 (.load (.bin .add (.reg 18) (.bin .add (.const 1) (.bin .mul (.const 6) (.reg 29))))) ;;
  .assign 35 (.load (.bin .add (.reg 18) (.bin .add (.const 3) (.bin .mul (.const 6) (.reg 29))))) ;;
  .assign 36 (.load (.bin .add (.reg 18) (.bin .add (.const 5) (.bin .mul (.const 6) (.reg 29))))) ;;
  forRange 37 (.const 0) (.reg 36) buildCompWEdgesBody ;;
  forRange 37 (.const 0) (.reg 32) buildCompJOrigBody

/-- Phase 3: allocates and populates `W`, `wWNum`, `wSources`, and `jSources`, updates header
slots `13..16`, and returns `hEnd`. -/
def buildAssembleStmt : Stmt :=
  .assign 24 (.reg 17) ;;
  .assign 25 (.bin .add (.reg 24) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 23)))) ;;
  .assign 26 (.bin .add (.reg 25) (.reg 23)) ;;
  .assign 27 (.bin .add (.reg 26) (.bin .mul (.const 3) (.reg 23))) ;;
  .assign 28 (.bin .add (.reg 27) (.bin .mul (.const 3) (.reg 6))) ;;
  .store (.bin .add (.reg 4) (.const 13)) (.reg 24) ;;
  .store (.bin .add (.reg 4) (.const 14)) (.reg 25) ;;
  .store (.bin .add (.reg 4) (.const 15)) (.reg 26) ;;
  .store (.bin .add (.reg 4) (.const 16)) (.reg 27) ;;
  .store (.reg 24) (.reg 5) ;;
  .store (.bin .add (.reg 24) (.const 1)) (.reg 23) ;;
  forRange 29 (.const 0) (.reg 12) buildJ0AsmBody ;;
  forRange 29 (.const 0) (.reg 14) buildCompAsmBody

/-- Complete procedure body for `buildWitnessCoreModule`, taking arguments
`[jAddr, statsAddr, decAddr, prepAddr, h]`. -/
def buildWitnessCoreBody (cePhiNum cePhiDen ceCDegInt ceBase boundsBase : ℕ) : Stmt :=
  buildPhase01Stmt cePhiNum cePhiDen ceCDegInt boundsBase ;;
  buildCeLoopStmt ceBase ;;
  buildAssembleStmt ;;
  .ret (.reg 28)

/-- Single-procedure module for `buildWitnessCoreBody`. -/
def buildWitnessCoreModule (cePhiNum cePhiDen ceCDegInt ceBase boundsBase : ℕ) : List Stmt :=
  [buildWitnessCoreBody cePhiNum cePhiDen ceCDegInt ceBase boundsBase]

theorem buildWitnessCoreBody_noRand (cePhiNum cePhiDen ceCDegInt ceBase boundsBase : ℕ) :
    (buildWitnessCoreBody cePhiNum cePhiDen ceCDegInt ceBase boundsBase).NoRand := by
  simp [buildWitnessCoreBody, buildPhase01Stmt, buildCeLoopStmt, buildCeBody, buildWeightFillBody,
    buildAssembleStmt, buildJ0AsmBody, buildCompAsmBody, buildCompWEdgesBody, buildCompJOrigBody,
    Stmt.NoRand, WordRAM.forUp, WordRAM.forRange]

theorem buildWitnessCoreModule_noRand (cePhiNum cePhiDen ceCDegInt ceBase boundsBase : ℕ) :
    ∀ s ∈ buildWitnessCoreModule cePhiNum cePhiDen ceCDegInt ceBase boundsBase, s.NoRand := by
  intro s hs
  simp only [buildWitnessCoreModule, List.mem_singleton] at hs
  subst hs
  exact buildWitnessCoreBody_noRand cePhiNum cePhiDen ceCDegInt ceBase boundsBase

/-! ## 2. Memory Layout Predicates & Specification Bundle -/

/-- Three-word record layout for `wSources : List WEdgeSource` at `a`. -/
def WSourcesAt (mem : ℕ → ℕ) (a : ℕ) (ws : List WEdgeSource) : Prop :=
  ∀ i (hi : i < ws.length),
    match ws[i] with
    | .fromJ0 jOrig =>
      mem (a + 3 * i) = 0 ∧ mem (a + 3 * i + 1) = jOrig ∧ mem (a + 3 * i + 2) = 0
    | .fromComp ci eL =>
      mem (a + 3 * i) = 1 ∧ mem (a + 3 * i + 1) = ci ∧ mem (a + 3 * i + 2) = eL

/-- Three-word record layout for `jSources : List JEdgeSource` at `a`. -/
def JSourcesAt (mem : ℕ → ℕ) (a : ℕ) (js : List JEdgeSource) : Prop :=
  ∀ i (hi : i < js.length),
    match js[i] with
    | .isLoop =>
      mem (a + 3 * i) = 0 ∧ mem (a + 3 * i + 1) = 0 ∧ mem (a + 3 * i + 2) = 0
    | .inJ0 eW =>
      mem (a + 3 * i) = 1 ∧ mem (a + 3 * i + 1) = eW ∧ mem (a + 3 * i + 2) = 0
    | .inComp ci jL =>
      mem (a + 3 * i) = 2 ∧ mem (a + 3 * i + 1) = ci ∧ mem (a + 3 * i + 2) = jL

/-- Six-word extended component table `compExt` at `a`, pointing into constructed expanders `W_sub`. -/
def CompExtAt (mem : ℕ → ℕ) (a phiNum_dec wAddr : ℕ) (cs : List CompInfo) : Prop :=
  ∀ ci (hci : ci < cs.length),
    let c := cs[ci]
    let wSubPtr := mem (a + 6 * ci + 1)
    mem (a + 6 * ci) = c.wStart ∧
    mem (a + 6 * ci + 2) = 2 ^ c.level ∧
    mem (a + 6 * ci + 3) = phiNum_dec * 2 ^ c.level ∧
    mem (a + 6 * ci + 4) = c.X.card ∧
    mem (a + 6 * ci + 5) = c.W_sub.m ∧
    GraphAt mem wSubPtr c.W_sub ∧
    a + 6 * cs.length ≤ wSubPtr ∧
    wSubPtr + (2 + 2 * c.W_sub.m) ≤ wAddr

/-- Bundled Word-RAM inputs read by `buildWitnessCoreBody` at `[jAddr, statsAddr, decAddr, prepAddr, h]`. -/
structure WitnessCoreInput where
  H' : Graph
  embJH : ℕ → Walk
  prep : PrepInput
  statsAddr : ℕ
  h : ℕ

namespace WitnessCoreInput

/-- Integer-weight lower bound on `ConstructExpander` vertex count `M_W`. -/
def mwInt (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) : ℕ :=
  (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1) /
    inp.prep.phiNum_dec + 1

def dJInt (inp : WitnessCoreInput) : ℕ :=
  (inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1) / inp.prep.phiNum_dec

def dWInt (ce : ConstructExpanderImpl) : ℕ :=
  (ce.phiDen + ce.phiNum - 1) / ce.phiNum

def phiDsDenInt (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  max (pds.phiOutDen inp.dJInt inp.prep.J0_strip.m) (pds.phiOutDen (dWInt ce) (inp.mwInt ce))

def γExpInt (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  max (pds.gExp inp.dJInt inp.prep.J0_strip.m) (pds.gExp (dWInt ce) (inp.mwInt ce))

def γDelInt (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  max (pds.gDel inp.dJInt inp.prep.J0_strip.m) (pds.gDel (dWInt ce) (inp.mwInt ce))

def tau2Int (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  inp.γExpInt ce pds * inp.γDelInt ce pds * inp.phiDsDenInt ce pds

def tau1Int (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  2 * inp.tau2Int ce pds * length inp.prep.J inp.embJH *
    (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J)

/-- Conservative upper bound on the heap end address reached by `buildWitnessCoreBody`. -/
def maxHeapEnd (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  let m0 := inp.prep.J0_strip.m
  let wMUpper := m0 + 2 * ce.c_deg_int * m0 * inp.prep.phiDen_dec
  inp.h + 20 +
    pds.boundsSpace inp.dJInt m0 +
    pds.boundsSpace (dWInt ce) (inp.mwInt ce) +
    6 * inp.prep.rawComps.length +
    4 * m0 +
    inp.prep.rawComps.length * ce.C_space * (inp.prep.J.n + 4 * m0 * inp.prep.phiDen_dec + 2) ^ ce.c_space +
    (2 + 6 * wMUpper + 3 * inp.prep.J.m)

/-- Conservative word-size upper bound covering every intermediate arithmetic value and pointer. -/
def maxWordBound (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams) : ℕ :=
  let m0 := inp.prep.J0_strip.m
  max (inp.maxHeapEnd ce pds)
    (max (4 * (m0 + 1) * inp.prep.phiDen_dec + 2 * ce.c_deg_int * (m0 + 1) * inp.prep.phiDen_dec +
        2 * ce.phiDen + 2)
      (2 * inp.tau2Int ce pds * (length inp.prep.J inp.embJH + 1) *
        (vcongNat inp.prep.J inp.H' inp.embJH + maxDeg inp.prep.J + 1) + 2))

/-- Validity of memory and parameters at word size `w` before calling `buildWitnessCoreBody`. -/
def Valid (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.H'.IsValid ∧
  IsEmbedding inp.prep.J inp.H' inp.embJH ∧
  inp.prep.StaticValid mem w ∧
  inp.prep.hEnd ≤ inp.h ∧
  inp.statsAddr + 3 ≤ inp.h ∧
  mem inp.statsAddr = maxDeg inp.prep.J ∧
  mem (inp.statsAddr + 1) = length inp.prep.J inp.embJH ∧
  mem (inp.statsAddr + 2) = vcongNat inp.prep.J inp.H' inp.embJH ∧
  PrepStaticState inp.prep mem mem ∧
  CompsDoneUpTo inp.prep mem inp.prep.rawComps.length ∧
  ZeroFrom mem inp.h ∧
  pds.cw * (Nat.log 2 (inp.dJInt + inp.prep.J0_strip.m +
    pds.gExp inp.dJInt inp.prep.J0_strip.m + pds.gDel inp.dJInt inp.prep.J0_strip.m + 2) + 1) ≤ w ∧
  pds.cw * (Nat.log 2 (dWInt ce + inp.mwInt ce +
    pds.gExp (dWInt ce) (inp.mwInt ce) + pds.gDel (dWInt ce) (inp.mwInt ce) + 2) + 1) ≤ w ∧
  ce.cw * (Nat.log 2 (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) + 1) ≤ w ∧
  inp.maxWordBound ce pds < 2 ^ w

/-- Assembles a `CompInfo` list recursively from `rawComps` and concrete expanders `WSubs`. -/
def buildCompsFrom (inp : WitnessCoreInput) :
    ℕ → List (ℕ × List ℕ) → List Graph → List CompInfo
  | _, [], _ => []
  | offset, (lvl, X) :: rest, W :: ws =>
    let d := inp.prep.decomp
    let J_i := d.graphAt inp.prep.J0_strip lvl
    let Xf := X.toFinset
    let verts := vertsOf Xf
    let J_sub := inducedSubgraph J_i Xf
    let jSubOrigEdges := (insideIndices J_i Xf).map fun a =>
      inp.prep.nlIdx.getD ((d.edgesAt inp.prep.J0_strip lvl).getD a 0) 0
    { level := lvl
      X := Xf
      verts := verts
      J_sub := J_sub
      jSubOrigEdges := jSubOrigEdges
      W_sub := W
      wStart := offset } :: buildCompsFrom inp (offset + W.m) rest ws
  | _, _ :: _, [] => []

/-- Builds a full mathematical `WitnessData` record from the concrete `WSubs` returned by `ceBase`. -/
noncomputable def mkWitnessData (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) (WSubs : List Graph) : WitnessData :=
  let J := inp.prep.J
  let J0_strip := inp.prep.J0_strip
  let nlIdx := inp.prep.nlIdx
  let decomp := inp.prep.decomp
  let φ_dec := (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)
  let c_deg := 2 * (ce.c_deg_int : ℝ)
  let φ_Const := ce.φ_Const
  let j0Edges := inp.prep.j0Edges
  let comps := inp.buildCompsFrom j0Edges.length inp.prep.rawComps WSubs
  let wJ0Edges := j0Edges.map fun jOrig => J.edges.getD jOrig (0, 0)
  let wCompEdges := comps.flatMap compWEdges
  let W : Graph := ⟨J.n, wJ0Edges ++ wCompEdges⟩
  let wW := witnessWeight φ_dec j0Edges.length comps
  let wSourcesJ0 := j0Edges.map WEdgeSource.fromJ0
  let wSourcesComps := comps.zipIdx.flatMap fun (c, ci) =>
    (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal
  let wSources := wSourcesJ0 ++ wSourcesComps
  let jSources := (List.range J.m).map fun eJ =>
    if eJ ∈ j0Edges then JEdgeSource.inJ0 (j0Edges.idxOf eJ)
    else match findJCompEdge eJ comps 0 with
      | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
      | none => JEdgeSource.isLoop
  let M_W := inp.mwInt ce
  let φ_J := pds.φ_out (roundPhi φ_dec) J0_strip.m
  let φ_W := pds.φ_out (roundPhi φ_Const) M_W
  let φ_ds := min φ_J φ_W
  let γ_ExpPath := max (pds.γ_ExpPath (roundPhi φ_dec) J0_strip.m)
    (pds.γ_ExpPath (roundPhi φ_Const) M_W)
  let γ_del := max (pds.γ_del (roundPhi φ_dec) J0_strip.m) (pds.γ_del (roundPhi φ_Const) M_W)
  let τ₁ := 2 * γ_ExpPath * (length J inp.embJH : ℝ) * γ_del *
    (vcong J inp.H' (fun _ => 1) inp.embJH + (maxDeg J : ℝ)) / φ_ds
  let τ₂ := γ_ExpPath * γ_del / φ_ds
  { J0_strip := J0_strip
    nlIdx := nlIdx
    decomp := decomp
    φ_dec := φ_dec
    c_deg := c_deg
    φ_Const := φ_Const
    j0Edges := j0Edges
    comps := comps
    W := W
    wW := wW
    wSources := wSources
    jSources := jSources
    M_W := M_W
    φ_ds := φ_ds
    γ_ExpPath := γ_ExpPath
    γ_del := γ_del
    τ₁ := τ₁
    τ₂ := τ₂ }

/-- Exact postcondition on memory at `inp.h` after running `buildWitnessCoreBody`. -/
def OutputAt (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ mem : ℕ → ℕ) (v : ℕ) (wd : WitnessData) : Prop :=
  (∀ x < inp.h, mem x = mem₀ x) ∧
  ZeroFrom mem v ∧
  inp.h ≤ v ∧ v ≤ inp.maxHeapEnd ce pds ∧
  mem inp.h = inp.mwInt ce ∧
  mem (inp.h + 1) = pds.phiOutDen inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 2) = pds.gExp inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 3) = pds.gDel inp.dJInt inp.prep.J0_strip.m ∧
  mem (inp.h + 4) = pds.phiOutDen (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 5) = pds.gExp (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 6) = pds.gDel (dWInt ce) (inp.mwInt ce) ∧
  mem (inp.h + 7) = inp.phiDsDenInt ce pds ∧
  mem (inp.h + 8) = inp.γExpInt ce pds ∧
  mem (inp.h + 9) = inp.γDelInt ce pds ∧
  mem (inp.h + 10) = inp.tau1Int ce pds ∧
  mem (inp.h + 11) = inp.tau2Int ce pds ∧
  mem (inp.h + 17) = inp.prep.phiNum_dec ∧
  mem (inp.h + 18) = inp.prep.phiDen_dec ∧
  mem (inp.h + 19) = inp.prep.J0_strip.m ∧
  let aCompExt := mem (inp.h + 12)
  let wAddr := mem (inp.h + 13)
  let wWNumAddr := mem (inp.h + 14)
  let wSrcAddr := mem (inp.h + 15)
  let jSrcAddr := mem (inp.h + 16)
  inp.h + 20 ≤ aCompExt ∧
  aCompExt + 6 * wd.comps.length ≤ wAddr ∧
  wWNumAddr = wAddr + (2 + 2 * wd.W.m) ∧
  wSrcAddr = wWNumAddr + wd.W.m ∧
  jSrcAddr = wSrcAddr + 3 * wd.W.m ∧
  v = jSrcAddr + 3 * inp.prep.J.m ∧
  CompExtAt mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
  GraphAt mem wAddr wd.W ∧
  (∀ eW < wd.W.m, (mem (wWNumAddr + eW) : ℝ) / (inp.prep.phiDen_dec : ℝ) = wd.wW eW ∧
    1 ≤ mem (wWNumAddr + eW)) ∧
  WSourcesAt mem wSrcAddr wd.wSources ∧
  JSourcesAt mem jSrcAddr wd.jSources

end WitnessCoreInput

end MinCostFlow.Spanner
