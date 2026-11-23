module

public import MinCostFlow.SparseCore.Program.AssemblyTop
public import MinCostFlow.SparseCore.Program.AssemblyStretch
public import MinCostFlow.MinRatio.ProgramShift
import Mathlib.Tactic

/-!
# Bridge from the top-layer sparse-core program to the solver uniform contract (`AssemblyBridge`)

Bridges `asmTop_implements_kfr` / `asmTop_implements_kf` (`AssemblyTop.lean`) to the solver's
`L`-indexed LSF initializer family `lsfInit : ℕ → ℕ → LSFInit`, capacity-indexed representation
`rep` with shared `(τ, phi, foot)`, and the four solver-input hypotheses (`1 ≤ depth`,
`depth ≤ M + N + k + L`, `∀ j < k, IsValidLSFInitFor …`, `G.n ≤ G.m + 1`).

* `SparseCoreOrdProgramUniformReembBridged` and `SparseCoreOrdProgramUniformBridged`: the minimal
  extension of `SparseCoreOrdProgramUniform` (`AssemblyStatement.lean`) that keeps the exact
  quantifier order (`∀ capExp, ∃ wordExp, ∀ limbMul, ∃ P allocation, ∀ depth w fmt L`), keeps
  `(τ, phi, foot)` uniform across all capacities while indexing `rep` by `(vCap, eCap)` (matching
  `LastLevelProgram.lastLevelRepresentation`), and adds the four solver-discharged hypotheses.
* `ScCompFamilyHyp` and `ScBranchModuleHyp`: interface statements for the component-LSF family (P4)
  and branch module (`AsmBranchAt`, built from P2, P5, P6, P7, P8, P10, and the first phase of
  the step), with word exponents bounded by `39` at `capExp = 3`.
* `asmTop_uniform_reemb_bridged`, `asmTop_uniform_bridged`: build the bridged uniform statements
  with explicit `wordExp = asmTopWordExp CFS BRS capExp` and prove `wordExp ≤ 39` at `capExp = 3`.
* `sparseCoreOrdProgramUniformBridged_shift`: relocation into any host program containing `p`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Bridged uniform sparse-core statement -/

/-- Minimal bridged uniform statement for `sparseCoreOrdMachineContractKFR`: preserves the
quantifier order of `SparseCoreOrdProgramUniform` (`∀ capExp, ∃ wordExp, ∀ limbMul, ∃ P alloc,
∀ depth w fmt L`), supports an `L`-indexed initializer `lsfInit : ℕ → ℕ → LSFInit`, keeps
`(τ, phi, foot)` uniform over `(vCap, eCap)` while indexing `rep` by `(vCap, eCap)`, and carries
the four solver-discharged input hypotheses (`1 ≤ depth`, `depth ≤ M + N + k + L`,
`IsValidLSFInitFor`, `G.n ≤ G.m + 1`). -/
def SparseCoreOrdProgramUniformReembBridged (C_lsst : ℝ) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
        1 ≤ depth → fmt.precision ≤ 4 * L →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs
                (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                depth ≤ Expander.chosenL ((M + N) ^ 2) →
                M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                (∀ j < k, IsValidLSFInitFor (lsfInit L fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFRBL fmt L depth
                    (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                    (bundleToolReemb (brReemb depth))
                    G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (allocation sizeParam) R p op

/-- Minimal bridged uniform statement for `sparseCoreOrdMachineContractKFBL` + `SparseCoreReadoutFootAt`. -/
def SparseCoreOrdProgramUniformBridged (C_lsst : ℝ) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
        1 ≤ depth → fmt.precision ≤ 4 * L →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs
                (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                depth ≤ Expander.chosenL ((M + N) ^ 2) →
                M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                (∀ j < k, IsValidLSFInitFor (lsfInit L fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFBL fmt L depth
                    (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                    G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (allocation sizeParam) R p op

/-- `SparseCoreOrdProgramUniformReembBridged` immediately implies
`SparseCoreOrdProgramUniformBridged`. -/
theorem sparseCoreOrdProgramUniformBridged_of_reemb {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReembBridged C_lsst lsfInit impl brReemb p init op) :
    SparseCoreOrdProgramUniformBridged C_lsst lsfInit impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt L hdepth hPL => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt L hdepth hPL
  refine ⟨τ, phi, foot, fun vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ vCap eCap
  exact ⟨rep, hloc, fun G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap =>
    let ⟨h1, h2⟩ := hR G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap
    ⟨dsRep_implements_kfbl_of_kfrbl h1, h2⟩⟩

/-- Relocation of `SparseCoreOrdProgramUniformBridged` into any host program `p` containing
`shiftProgramProcs offset Q` at `offset`. -/
theorem sparseCoreOrdProgramUniformBridged_shift {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} {p Q : Program} {offset init : ℕ} {op : ℕ → ℕ}
    (hHas : p.HasAt offset (shiftProgramProcs offset Q))
    (hU : SparseCoreOrdProgramUniformBridged C_lsst lsfInit impl Q init op) :
    SparseCoreOrdProgramUniformBridged C_lsst lsfInit impl p (offset + init) (fun i => offset + op i) :=
  fun capExp => by
    obtain ⟨wordExp, hw⟩ := hU capExp
    refine ⟨wordExp, fun limbMul => ?_⟩
    obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
    refine ⟨P, allocation, hwe, fun depth w fmt L hdepth hPL => ?_⟩
    obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt L hdepth hPL
    refine ⟨τ, phi, foot, fun vCap eCap => ?_⟩
    obtain ⟨rep, hloc, hR⟩ := hτ vCap eCap
    exact ⟨rep, hloc, fun G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap =>
      let ⟨h1, h2⟩ := hR G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap
      ⟨dsRep_implements_shift hHas h1, sparseCoreReadoutFootAt_shift hHas h2⟩⟩

/-! ## Interface statements for the component-LSF family and the branch module -/

/-- The canonical re-embedded edge list of the bundle tool on `canonicalSparsify impl`, at tree
depth `depth`. -/
noncomputable abbrev scBranchReemb (impl : SparsifyImpl) (depth : ℕ) :
    BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ :=
  stepBundleTree_reembList (fun _ => canonicalSparsify impl)

/-- Interface statement for the component-LSF family (P4) inside program `p`: for every
`(capExp, limbMul, w, fmt, L)`, provides a concrete `AsmCompFamilyAt` at `lsfInit L fmt.precision`
whose export entry is `fCFExport` and whose root-query entry is `fCFRoot`, with
`CFS.wordExp 3 ≤ 39`. -/
structure ScCompFamilyHyp (CFS : AsmCompFamilySpec) (lsfInit : ℕ → ℕ → LSFInit)
    (p : Program) (fCFInit fCFBatch fCFExport fCFRoot : ℕ) : Prop where
  wordExp_le_39 : CFS.wordExp 3 ≤ 39
  inst : ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L : ℕ),
    ∃ CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch,
      CF.fExport = fCFExport ∧ CF.fRoot = fCFRoot

/-- Interface statement for the branch module (`AsmBranchAt`, built from P2, P5, P6, P7, P8, P10, and
the first phase of the step) inside program `p`: given `SparsifySubpolyStretch impl`, supplies a
uniform `BRS : AsmBranchSpec` with `BRS.wordExp 3 ≤ 39` and, for every `(capExp, limbMul, depth,
w, fmt, L)` with `1 ≤ depth` and any `CF : AsmCompFamilyAt` with `CF.fRoot = fCFRoot`, an
`AsmBranchAt` at `bp` with re-embedded list `scBranchReemb impl depth` and readout layout
`AsmBranchReadoutLayout`. -/
structure ScBranchModuleHyp (CFS : AsmCompFamilySpec) (C_lsst : ℝ) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (fCFInit fCFBatch fCFRoot : ℕ) (bp : AsmBranchProcs) :
    Prop where
  inst : SparsifySubpolyStretch impl →
    ∃ BRS : AsmBranchSpec,
      BRS.wordExp 3 ≤ 39 ∧
      ∀ (capExp limbMul depth w : ℕ) (fmt : Num.Format w) (L : ℕ),
        1 ≤ depth → fmt.precision ≤ 4 * L →
        ∀ (CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch),
          CF.fRoot = fCFRoot →
          ∃ BR : AsmBranchAt BRS CFS (lsfInit L fmt.precision) C_lsst depth w fmt L capExp limbMul
              impl (scBranchReemb impl depth) p fCFInit fCFBatch CF bp,
            AsmBranchReadoutLayout BR

/-! ## Init allocation bound predicate and bridge theorems from `asmTop_implements_kfr` / `asmTop_implements_kf` -/

/-- Input-independent polynomial upper bound dominating `asmTopAlloc CFS BRS capExp 6` on any
11-argument init list `[g, l, gr, o, k, M, N, L, P_fp, depth, h]`, evaluated at `k + M + N + L`. -/
def asmTopInitPoly (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec) (capExp : ℕ) : PolyBound :=
  let c := max capExp 1
  let p1 := CFS.initSpace capExp
  let p2 := CFS.exportSpace capExp
  let p3 := BRS.initSpace capExp
  let D := max (max p1.deg (p2.deg + 1)) (p3.deg + 1)
  { coeff := 84 + p1.coeff * 3 ^ p1.deg + p2.coeff * 3 ^ p2.deg + p3.coeff * 5 ^ p3.deg
    deg := c * D }

/-- On op `6` (init), `asmTopAlloc` reads only `(k, M, N, L)` and is independent of `sizeParam`,
the pointer arguments, `P_fp`, and `depth`. -/
theorem asmTopAlloc_init_ptr_indep (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp sizeParam g l gr o k M N L P_fp depth h : ℕ) :
    asmTopAlloc CFS BRS capExp sizeParam 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] =
      asmTopAlloc CFS BRS capExp sizeParam 6 [0, 0, 0, 0, k, M, N, L, 0, 0, 0] := by
  unfold asmTopAlloc; rfl

/-- On op `6` (init), `asmTopAlloc` is bounded by `(asmTopInitPoly CFS BRS capExp).eval (k + M + N + L)`. -/
theorem asmTopAlloc_init_le_poly (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp sizeParam g l gr o k M N L P_fp depth h : ℕ) :
    asmTopAlloc CFS BRS capExp sizeParam 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] ≤
      (asmTopInitPoly CFS BRS capExp).eval (k + M + N + L) := by
  set X := k + M + N + L
  set B := X + 2
  set c := max capExp 1
  set Z := B ^ c
  set p1 := CFS.initSpace capExp
  set p2 := CFS.exportSpace capExp
  set p3 := BRS.initSpace capExp
  set D := max (max p1.deg (p2.deg + 1)) (p3.deg + 1)
  have hc1 : 1 ≤ c := le_max_right _ _
  have hD1 : 1 ≤ D := le_trans (Nat.succ_le_succ (Nat.zero_le _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
  have hB2 : 2 ≤ B := by omega
  have hBZ : B ≤ Z := by
    calc B = B ^ 1 := (Nat.pow_one B).symm
      _ ≤ B ^ c := Nat.pow_le_pow_right (by omega) hc1
  have hZ2 : 2 ≤ Z := le_trans hB2 hBZ
  have hZ1 : 1 ≤ Z := by omega
  have hZD : Z ≤ Z ^ D := by
    calc Z = Z ^ 1 := (Nat.pow_one Z).symm
      _ ≤ Z ^ D := Nat.pow_le_pow_right hZ1 hD1
  have hZpow : Z ^ D = B ^ (c * D) := (Nat.pow_mul B c D).symm
  have hcapB : (M + N + 2) ^ capExp ≤ Z :=
    le_trans (Nat.pow_le_pow_left (by omega : M + N + 2 ≤ B) capExp)
      (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hp1 : p1.eval ((M + N + 2) ^ capExp + L + k) ≤ p1.coeff * 3 ^ p1.deg * Z ^ D := by
    unfold PolyBound.eval
    have harg : (M + N + 2) ^ capExp + L + k + 2 ≤ 3 * Z := by omega
    have hd : p1.deg ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
    calc p1.coeff * ((M + N + 2) ^ capExp + L + k + 2) ^ p1.deg
        ≤ p1.coeff * (3 * Z) ^ p1.deg :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg _)
      _ = p1.coeff * 3 ^ p1.deg * Z ^ p1.deg := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ p1.coeff * 3 ^ p1.deg * Z ^ D :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 hd)
  have hp2 : k * p2.eval (M + N + k + (M + N + 2) ^ capExp + L) ≤
      p2.coeff * 3 ^ p2.deg * Z ^ D := by
    unfold PolyBound.eval
    have harg : M + N + k + (M + N + 2) ^ capExp + L + 2 ≤ 3 * Z := by omega
    have hd : p2.deg + 1 ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
    calc k * (p2.coeff * (M + N + k + (M + N + 2) ^ capExp + L + 2) ^ p2.deg)
        ≤ Z * (p2.coeff * (3 * Z) ^ p2.deg) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg _))
      _ = p2.coeff * 3 ^ p2.deg * Z ^ (p2.deg + 1) := by
          rw [Nat.mul_pow, Nat.pow_succ]; ring
      _ ≤ p2.coeff * 3 ^ p2.deg * Z ^ D :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 hd)
  have hp3 : k * p3.eval (2 * (M + N + k + (M + N + 2) ^ capExp + L)) ≤
      p3.coeff * 5 ^ p3.deg * Z ^ D := by
    unfold PolyBound.eval
    have harg : 2 * (M + N + k + (M + N + 2) ^ capExp + L) + 2 ≤ 5 * Z := by omega
    have hd : p3.deg + 1 ≤ D := le_max_right _ _
    calc k * (p3.coeff * (2 * (M + N + k + (M + N + 2) ^ capExp + L) + 2) ^ p3.deg)
        ≤ Z * (p3.coeff * (5 * Z) ^ p3.deg) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg _))
      _ = p3.coeff * 5 ^ p3.deg * Z ^ (p3.deg + 1) := by
          rw [Nat.mul_pow, Nat.pow_succ]; ring
      _ ≤ p3.coeff * 5 ^ p3.deg * Z ^ D :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 hd)
  have hlin : ASM_HDR_SIZE + (1 + 6 * M) + (16 + 2 * (M + N + 2) ^ capExp + 16 * (M + N + 2) ^ capExp) +
      k + (M + N + k + (M + N + 2) ^ capExp + L + ASM_HDR_SIZE) ≤ 84 * Z ^ D := by
    unfold ASM_HDR_SIZE; omega
  have hgoal : (asmTopInitPoly CFS BRS capExp).eval X =
      (84 + p1.coeff * 3 ^ p1.deg + p2.coeff * 3 ^ p2.deg + p3.coeff * 5 ^ p3.deg) * Z ^ D := by
    unfold asmTopInitPoly PolyBound.eval
    rw [hZpow]
  rw [hgoal]
  unfold asmTopAlloc
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hp1' : (CFS.initSpace capExp).eval ((M + N + 2) ^ capExp + L + k) ≤
      p1.coeff * 3 ^ p1.deg * Z ^ D := hp1
  have hp2' : k * (CFS.exportSpace capExp).eval (M + N + k + (M + N + 2) ^ capExp + L) ≤
      p2.coeff * 3 ^ p2.deg * Z ^ D := hp2
  have hp3' : k * (BRS.initSpace capExp).eval (2 * (M + N + k + (M + N + 2) ^ capExp + L)) ≤
      p3.coeff * 5 ^ p3.deg * Z ^ D := hp3
  simp only [Nat.mul_add, Nat.add_mul] at *
  omega

/-- The init (`op = 6`) allocation of the sparse core depends only on `(k, M, N, L)` (not on pointer
arguments, `P_fp`, or `depth`), and is bounded by an input-independent polynomial
`initPoly.eval (k + M + N + L)`. -/
def SparseCoreInitAllocBound (allocation : ℕ → List ℕ → ℕ) : Prop :=
  (∀ g l gr o k M N L P_fp depth h,
    allocation 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] =
      allocation 6 [0, 0, 0, 0, k, M, N, L, 0, 0, 0]) ∧
  ∃ initPoly : PolyBound, ∀ g l gr o k M N L P_fp depth h,
    allocation 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] ≤ initPoly.eval (k + M + N + L)

/-- `asmTopAlloc` satisfies `SparseCoreInitAllocBound` unconditionally for every `sizeParam`. -/
theorem asmTopAlloc_initBound (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp sizeParam : ℕ) :
    SparseCoreInitAllocBound (asmTopAlloc CFS BRS capExp sizeParam) :=
  ⟨asmTopAlloc_init_ptr_indep CFS BRS capExp sizeParam,
    asmTopInitPoly CFS BRS capExp, asmTopAlloc_init_le_poly CFS BRS capExp sizeParam⟩

/-- Input-independent polynomial upper bound dominating op `0` (`update`) of
`asmTopAlloc CFS BRS capExp sizeParam` as a function of `sizeParam + words + editWords`. -/
def asmTopOp0Poly (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec) (capExp : ℕ) : PolyBound :=
  let p1 := CFS.batchSpace capExp
  let p2 := BRS.stepSpace capExp
  { coeff := 7 + p1.coeff + p2.coeff
    deg := max (max p1.deg (p2.deg + 1)) 1 }

/-- On op `0` (`update`), `asmTopAlloc` is independent of `heap` and all pointer arguments, and is
bounded by `(asmTopOp0Poly CFS BRS capExp).eval (sizeParam + words + editWords)`. -/
theorem asmTopAlloc_op0_le_poly (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp sizeParam hndl g batch words edits editWords l gr h : ℕ) :
    asmTopAlloc CFS BRS capExp sizeParam 0
        [hndl, g, batch, words, edits, editWords, l, gr, h] ≤
      (asmTopOp0Poly CFS BRS capExp).eval (sizeParam + words + editWords) := by
  set X := sizeParam + words + editWords
  set B := X + 2
  set p1 := CFS.batchSpace capExp
  set p2 := BRS.stepSpace capExp
  set D := max (max p1.deg (p2.deg + 1)) 1
  have hB1 : 1 ≤ B := by omega
  have hD1 : 1 ≤ D := le_max_right _ _
  have hBD : B ≤ B ^ D := by
    calc B = B ^ 1 := (Nat.pow_one B).symm
      _ ≤ B ^ D := Nat.pow_le_pow_right hB1 hD1
  have hp1 : p1.eval (sizeParam + words) ≤ p1.coeff * B ^ D := by
    have h1 := p1.eval_mono (show sizeParam + words ≤ X by omega)
    unfold PolyBound.eval at h1 ⊢
    exact h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1
      (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hp2 : sizeParam * p2.eval X ≤ p2.coeff * B ^ D := by
    unfold PolyBound.eval
    have hmul : sizeParam * (p2.coeff * B ^ p2.deg) ≤ B * (p2.coeff * B ^ p2.deg) :=
      Nat.mul_le_mul_right _ (by omega)
    have heq : B * (p2.coeff * B ^ p2.deg) = p2.coeff * B ^ (p2.deg + 1) := by
      rw [Nat.pow_succ]; ring
    have hd : p2.deg + 1 ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
    exact (hmul.trans_eq heq).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 hd))
  unfold asmTopAlloc asmTopOp0Poly PolyBound.eval
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hgoal : (7 + p1.coeff + p2.coeff) * B ^ D =
      7 * B ^ D + p1.coeff * B ^ D + p2.coeff * B ^ D := by ring
  change (4 + 7 * sizeParam) + words + editWords + (3 * editWords + 2) +
      p1.eval (sizeParam + words) + sizeParam * p2.eval X ≤
      (7 + p1.coeff + p2.coeff) * B ^ D
  rw [hgoal]
  omega

/-- On op `1` (`restart`), `asmTopAlloc` is independent of `heap` and bounded by
`(BRS.restartSpace capExp).eval sizeParam`. -/
theorem asmTopAlloc_op1_le_poly (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp sizeParam coreH b h : ℕ) :
    asmTopAlloc CFS BRS capExp sizeParam 1 [coreH, b, h] ≤
      (BRS.restartSpace capExp).eval sizeParam :=
  le_rfl

/-- Polynomial space bounds for a `sizeParam`-indexed sparse-core allocation family:
op `6` (`init`) is independent of `sizeParam`, op `1` (`restart`) is bounded by `P1.eval sizeParam`
(independent of `heap`), and op `0` (`update`) is bounded by `P0.eval (sizeParam + words + editWords)`
(independent of `heap`). -/
def SparseCoreUpdateRestartAllocBound (allocation : ℕ → ℕ → List ℕ → ℕ) : Prop :=
  (∀ s₁ s₂ g l gr o k M N L P_fp depth h,
    allocation s₁ 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h] =
      allocation s₂ 6 [g, l, gr, o, k, M, N, L, P_fp, depth, h]) ∧
  (∃ P1 : PolyBound, ∀ sizeParam coreH b h,
    allocation sizeParam 1 [coreH, b, h] ≤ P1.eval sizeParam) ∧
  (∃ P0 : PolyBound, ∀ sizeParam hndl g batch words edits editWords l gr h,
    allocation sizeParam 0 [hndl, g, batch, words, edits, editWords, l, gr, h] ≤
      P0.eval (sizeParam + words + editWords))

/-- `asmTopAlloc` satisfies `SparseCoreUpdateRestartAllocBound` unconditionally. -/
theorem asmTopAlloc_updateRestartBound (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec)
    (capExp : ℕ) :
    SparseCoreUpdateRestartAllocBound (asmTopAlloc CFS BRS capExp) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
   ⟨BRS.restartSpace capExp, asmTopAlloc_op1_le_poly CFS BRS capExp⟩,
   ⟨asmTopOp0Poly CFS BRS capExp, asmTopAlloc_op0_le_poly CFS BRS capExp⟩⟩

/-- **Explicit bridged uniform theorem for `KFRBL`**: given `HasAsmTopProcs`, `SparsifyPolyStretch`,
unit time stretch `∀ m, impl.γ_t m = 1`, `ScCompFamilyHyp`, and `ScBranchModuleHyp`, produces a
uniform word-size exponent `wordExp` with `wordExp 3 ≤ 39`, parameters `P`, `sizeParam`-indexed
allocation `alloc` satisfying `SparseCoreInitAllocBound` and `SparseCoreUpdateRestartAllocBound`,
and the bridged uniform `Implements` statement for `sparseCoreOrdMachineContractKFRBL` with
re-embedded list `scBranchReemb impl`. -/
theorem asmTop_uniform_reemb_bridged_explicit
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {p : Program} {b fCFInit fCFBatch fCFExport fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifySubpolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit p fCFInit fCFBatch fCFExport fCFRoot)
    (hBR : ScBranchModuleHyp CFS C_lsst lsfInit impl p fCFInit fCFBatch fCFRoot bp) :
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
                    (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl) →
                    τ → (ℕ → ℕ) → Prop,
                  let R : DSRep (SparseCoreOrdAbs
                      (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)) :=
                    ⟨τ, rep, phi, foot⟩
                  R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                    fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                    depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                    depth ≤ Expander.chosenL ((M + N) ^ 2) →
                    M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                    (∀ j < k, IsValidLSFInitFor (lsfInit L fmt.precision) C_lsst k j) →
                    G.n ≤ G.m + 1 →
                    CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                    R.Implements w p (asmTopInitIdx b) (asmTopOpIdx b)
                      (sparseCoreOrdMachineContractKFRBL fmt L depth
                        (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                        (bundleToolReemb (scBranchReemb impl depth))
                        G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                    SparseCoreReadoutFootAt fmt L depth
                      (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                      G k M N vCap eCap capExp P (allocation sizeParam) R p (asmTopOpIdx b) := by
  obtain ⟨BRS, hBR_we, hBR_inst⟩ := hBR.inst hγ
  refine ⟨asmTopWordExp CFS BRS, ?_, fun capExp limbMul => ?_⟩
  · unfold asmTopWordExp
    rw [asmP10WordExp_at_3]
    exact max_le (max_le hCF.wordExp_le_39 hBR_we) (by decide)
  · refine ⟨asmTopParams CFS BRS capExp limbMul, asmTopAlloc CFS BRS capExp, rfl,
      asmTopAlloc_initBound CFS BRS capExp, asmTopAlloc_updateRestartBound CFS BRS capExp,
      fun depth w fmt L hdepth hPL => ?_⟩
    obtain ⟨CF, hfExp, hfRoot⟩ := hCF.inst capExp limbMul w fmt L
    obtain ⟨BR, hLay⟩ := hBR_inst capExp limbMul depth w fmt L hdepth hPL CF hfRoot
    refine ⟨AsmTopMeta CF.rep.τ BR.rep.τ,
      fun _ x mem => asmTopPhi CF.rep BR.rep x mem,
      fun hndl x addr => asmTopFoot CF.rep BR.rep rfl rfl hndl x addr,
      fun vCap eCap => ?_⟩
    refine ⟨(asmTopRepEq (lsfInit := lsfInit L fmt.precision) (C_lsst := C_lsst) (impl := impl)
        CF.rep BR.rep CF.vCapOf CF.eCapOf (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L
        fmt.precision vCap eCap).rep,
      asmTopRepEq_local (cfV := CF.vCapOf) (cfE := CF.eCapOf) CF.rep_local BR.rep_local,
      fun G k M N sizeParam hfmt hcap hdepth_le hdepth_lg hdepth_ch hsize hInit hGn_le hCFmt hkCap =>
        ⟨asmTop_implements_kfr CF BR hLay hp hfExp.symm G k M N vCap eCap sizeParam
          hfmt hPL hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize (hγt M) hInit hGn_le hCFmt hkCap,
         asmTop_readoutFoot_implements CF BR hLay hp G k M N vCap eCap sizeParam hfmt hcap hdepth hInit⟩⟩

/-- **Bridged uniform theorem for `KFBL` + `SparseCoreReadoutFootAt` with `wordExp 3 ≤ 39`**:
combines `B1` (`∀ L`), `B2` (capacity-indexed `rep` with uniform `(τ, phi, foot)`), `B3` (four
solver-input hypotheses), `B4` (`wordExp 3 ≤ 39`), `SparseCoreInitAllocBound`,
`SparseCoreUpdateRestartAllocBound`, and readout layout postconditions. -/
theorem asmTop_uniform_bridged_with_wordExp
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {p : Program} {b fCFInit fCFBatch fCFExport fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifySubpolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit p fCFInit fCFBatch fCFExport fCFRoot)
    (hBR : ScBranchModuleHyp CFS C_lsst lsfInit impl p fCFInit fCFBatch fCFRoot bp) :
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
                    (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl) →
                    τ → (ℕ → ℕ) → Prop,
                  let R : DSRep (SparseCoreOrdAbs
                      (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)) :=
                    ⟨τ, rep, phi, foot⟩
                  R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                    fmt.limbBits = 4 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                    depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                    depth ≤ Expander.chosenL ((M + N) ^ 2) →
                    M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                    (∀ j < k, IsValidLSFInitFor (lsfInit L fmt.precision) C_lsst k j) →
                    G.n ≤ G.m + 1 →
                    CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                    R.Implements w p (asmTopInitIdx b) (asmTopOpIdx b)
                      (sparseCoreOrdMachineContractKFBL fmt L depth
                        (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                        G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                    SparseCoreReadoutFootAt fmt L depth
                      (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                      G k M N vCap eCap capExp P (allocation sizeParam) R p (asmTopOpIdx b) := by
  obtain ⟨wordExp, hwe3, hall⟩ := asmTop_uniform_reemb_bridged_explicit hp hγ hγt hCF hBR
  refine ⟨wordExp, hwe3, fun capExp limbMul => ?_⟩
  obtain ⟨P, alloc, hwe, hinitB, hurB, hP⟩ := hall capExp limbMul
  refine ⟨P, alloc, hwe, hinitB, hurB, fun depth w fmt L hdepth hPL => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt L hdepth hPL
  refine ⟨τ, phi, foot, fun vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ vCap eCap
  exact ⟨rep, hloc, fun G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap =>
    let ⟨h1, h2⟩ := hR G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap
    ⟨dsRep_implements_kfbl_of_kfrbl h1, h2⟩⟩

/-- Corollary: `SparseCoreOrdProgramUniformBridged` holds directly. -/
theorem asmTop_uniform_bridged
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {p : Program} {b fCFInit fCFBatch fCFExport fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifySubpolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit p fCFInit fCFBatch fCFExport fCFRoot)
    (hBR : ScBranchModuleHyp CFS C_lsst lsfInit impl p fCFInit fCFBatch fCFRoot bp) :
    SparseCoreOrdProgramUniformBridged C_lsst lsfInit impl p (asmTopInitIdx b) (asmTopOpIdx b) := by
  obtain ⟨wordExp, -, hall⟩ := asmTop_uniform_bridged_with_wordExp hp hγ hγt hCF hBR
  exact fun capExp => ⟨wordExp capExp, fun limbMul =>
    let ⟨P, alloc, hwe, _, _, hP⟩ := hall capExp limbMul
    ⟨P, alloc, hwe, hP⟩⟩

end MinCostFlow.SparseCore.Program
