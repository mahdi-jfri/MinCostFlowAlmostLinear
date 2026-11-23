module

public import MinCostFlow.SparseCore.Program.AssemblyBridge
public import MinCostFlow.SparseCore.Program.AssemblyBranchReadLayout

/-!
# Bridging the branch value `asmBranchAt_value` into the top-layer bridge (`AssemblyBridgeBranch`)

Connects `asmBranchAt_value` (`AssemblyBranchValue.lean`) and `asmBranchAt_value_readoutLayout`
(`AssemblyBranchReadLayout.lean`) directly to `ScBranchModuleHyp` and the top-layer bridge
(`AssemblyBridge.lean`), for every balancing depth `depth ≥ 1` on a single finite program `p`:

1. **Inhabitedness and depth-independence of `HasAsmBrProcs` (`hasAsmBrProcs_inhabited`):**
   Since P8 (`restartBranchStmt`) takes `depth` as a run-time argument loaded by
   `asmBrRestartStmt` from `s + ASM_SD_SPL`, `HasAsmBrProcs p bp impl fRoot I` does not depend on
   `depth`. For any `impl` and `fRoot`, a single finite program `p` with fixed `(bp, I)` satisfies
   `HasAsmBrProcs p bp impl fRoot I`.
2. **Uniform `ScBranchModuleHyp` from `AsmBrPieces` (`ScBranchPiecesHyp`,
   `scBranchModuleHyp_of_pieces`):**
   Given fixed constants `K` (`K.firstWordExp 3 ≤ 39`), fixed procedures
   `HasAsmBrProcs p bp impl fCFRoot I`, and per-depth `AsmBrPieces` (with local `TR`, `B5`, and
   restart-compatible walk potential `Ψ`), constructs `ScBranchModuleHyp` directly via
   `asmBranchAt_value` and `asmBranchAt_value_readoutLayout`, with no readout-layout hypothesis.
3. **Per-depth helpers (`ScBranchValueAtDepth`, `scBranchAt_of_value`,
   `scBranchAt_of_value_readoutLayout`, `asmTop_bridged_reemb_at_depth_of_branchValue`,
   `asmTop_bridged_at_depth_of_branchValue`):**
   Explicit fixed-depth specialization of the same bridge.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Inhabitedness (non-vacuity) of depth-free `HasAsmBrProcs` -/

private theorem getElem?_append_left_of_some {xs ys : List Stmt} {k : ℕ} {s : Stmt}
    (h : xs[k]? = some s) : (xs ++ ys)[k]? = some s := by
  have hlt : k < xs.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hlt]; exact h

private theorem hasAt_append_extra {p0 : Program} {extra : List Stmt} {b : ℕ} {cs : List Stmt}
    (h : p0.HasAt b cs) : ({ procs := p0.procs ++ extra } : Program).HasAt b cs :=
  fun i hi => getElem?_append_left_of_some (h i hi)

private theorem hasAt_of_append_mid (a b c : List Stmt) :
    ({ procs := a ++ b ++ c } : Program).HasAt a.length b := by
  intro i hi
  have h1 : (a ++ b ++ c)[a.length + i]? = (a ++ b)[a.length + i]? :=
    List.getElem?_append_left (by simp; omega)
  rw [h1, List.getElem?_append_right (Nat.le_add_right a.length i)]
  simp [hi]

/-- **Non-vacuity of `HasAsmBrProcs`**: for every `impl` and `fRoot`, there exists a single finite
program `p` and fixed `(bp, I)` satisfying `HasAsmBrProcs p bp impl fRoot I` (which has no
`depth` parameter, and therefore serves every balancing depth `depth ≥ 1` simultaneously). -/
theorem hasAsmBrProcs_inhabited (impl : SparsifyImpl) (fRoot : ℕ) :
    ∃ (p : Program) (bp : AsmBranchProcs) (I : AsmBrProcIdx),
      HasAsmBrProcs p bp impl fRoot I := by
  obtain ⟨p0, bRead, L, hL, hR⟩ := hasReadProcs_inhabited fRoot
  let bSpan := p0.procs.length
  let spanCs := bucketSpannerProcs impl bSpan
  let bOut := bSpan + spanCs.length
  let outCs := outProcs bOut 0 0 0 0
  let tailBase := bOut + outCs.length
  let I : AsmBrProcIdx :=
    { fCoreI := 0, fCoreS := 0, bOut := bOut, nm := 0, sm := 0, fm := 0, lm := 0,
      f8 := tailBase + 3, fEmb := tailBase + 4, bSpan := bSpan, bCopy := L.copy,
      bRead := bRead, fBun := 0, fRL := tailBase + 6, fRS := tailBase + 8,
      fRE := tailBase + 10, fList := 0 }
  let bp : AsmBranchProcs :=
    { fInit := tailBase + 0, fStep := tailBase + 1, fRestart := tailBase + 2,
      fReadLSF := tailBase + 5, fReadS := tailBase + 7, fReadEmb := tailBase + 9,
      fReadOrd := tailBase + 11 }
  let tailCs : List Stmt :=
    [ asmBrInitStmt I.fCoreI (I.bRead + readBranchIdx13 4),
      asmBrStepStmt I.fCoreS (outIdxStep I.bOut) (I.bRead + readBranchIdx13 2),
      asmBrRestartStmt I.f8 (outIdxReset I.bOut) I.fEmb,
      restartBranchStmt I.fBun (I.bSpan + bsIdxOp0 + 0) (I.bRead + readBranchIdx13 3),
      embRefreshStmt I.bCopy (I.bSpan + bsOffRead + spanReadIdxPiWalkPtr),
      asmBrReadStmt I.fRL ASM_BR_READ,
      readLSFStmt,
      asmBrReadStmt I.fRS ASM_BR_READ,
      readSStmt,
      asmBrReadStmt I.fRE ASM_BR_EMB,
      embReadStmt,
      asmBrReadOrdStmt I.fList ]
  let p : Program := ⟨p0.procs ++ (spanCs ++ outCs ++ tailCs)⟩
  have hTail : p.HasAt tailBase tailCs := by
    have hEq : p = ⟨(p0.procs ++ spanCs ++ outCs) ++ tailCs ++ []⟩ := by
      simp [p, List.append_assoc]
    have hLen : (p0.procs ++ spanCs ++ outCs).length = tailBase := by
      simp [tailBase, bOut, bSpan, Nat.add_assoc]
    rw [hEq, ← hLen]
    exact hasAt_of_append_mid (p0.procs ++ spanCs ++ outCs) tailCs []
  have hTailLen : tailCs.length = 12 := rfl
  have hTailAt : ∀ i (hi : i < 12), p.procs[tailBase + i]? = some (tailCs[i]'(by rw [hTailLen]; exact hi)) :=
    fun i hi => hTail i (by rw [hTailLen]; exact hi)
  refine ⟨p, bp, I, ?_⟩
  refine
    { init := hTailAt 0 (by decide)
      step := hTailAt 1 (by decide)
      restart := hTailAt 2 (by decide)
      span := by
        have hEq : p = ⟨p0.procs ++ spanCs ++ (outCs ++ tailCs)⟩ := by simp [p, List.append_assoc]
        dsimp only [I]; rw [hEq]; exact hasAt_of_append_mid p0.procs spanCs (outCs ++ tailCs)
      out := by
        have hEq : p = ⟨(p0.procs ++ spanCs) ++ outCs ++ tailCs⟩ := by simp [p, List.append_assoc]
        have hLen : (p0.procs ++ spanCs).length = bOut := by simp [bOut, bSpan]
        dsimp only [I]; rw [OutProcsAt, hEq]
        simpa [outCs, hLen] using hasAt_of_append_mid (p0.procs ++ spanCs) outCs tailCs
      p8 := hTailAt 3 (by decide)
      emb := hTailAt 4 (by decide)
      copy := hasAt_append_extra hL.2.2.2.2.2.1
      read := ⟨L, ⟨hasAt_append_extra hL.1, hasAt_append_extra hL.2.1,
        hasAt_append_extra hL.2.2.1, hasAt_append_extra hL.2.2.2.1,
        getElem?_append_left_of_some hL.2.2.2.2.1, hasAt_append_extra hL.2.2.2.2.2.1,
        getElem?_append_left_of_some hL.2.2.2.2.2.2.1,
        hasAt_append_extra hL.2.2.2.2.2.2.2⟩, hasAt_append_extra hR⟩
      readLSF := hTailAt 5 (by decide)
      readLSFBody := hTailAt 6 (by decide)
      readS := hTailAt 7 (by decide)
      readSBody := hTailAt 8 (by decide)
      readEmb := hTailAt 9 (by decide)
      readEmbBody := hTailAt 10 (by decide)
      readOrd := hTailAt 11 (by decide) }

/-! ## Uniform `ScBranchModuleHyp` from `asmBranchAt_value` and `AsmBrPieces` -/

/-- Adjusts the stretch constants `(Cγ, cγ)` of `K : AsmBrConsts` to those of
`hγ : SparsifyPolyStretch impl`. All fields read by `AsmBrPieces` (`stepMul`, `stepYs`,
`stepSpace`, `initMul`, `initSpace`, `firstWordExp`, `OS`, `bunMul`, `listMul`) are unchanged. -/
noncomputable def scBranchConstsOfStretch (K : AsmBrConsts) {impl : SparsifyImpl}
    (hγ : SparsifyPolyStretch impl) : AsmBrConsts :=
  { K with
    Cγ := Classical.choose hγ
    cγ := Classical.choose (Classical.choose_spec hγ) }

/-- Re-indexes `AsmBrPieces K …` at `scBranchConstsOfStretch K hγ` (every field of `AsmBrPieces`
is independent of `K.Cγ` and `K.cγ`). -/
noncomputable def AsmBrPieces.withStretch {K : AsmBrConsts} {lsfInit : LSFInit} {depth w : ℕ}
    {fmt : Num.Format w} {L capExp limbMul : ℕ} {impl : SparsifyImpl} {p : Program}
    {I : AsmBrProcIdx} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {Ψ : BundleTreeState depth → ℕ} {CFR : DSRep CompFamilyAbs}
    (X : AsmBrPieces K lsfInit depth w fmt L capExp limbMul impl p I TR B5 Ψ CFR)
    (hγ : SparsifyPolyStretch impl) :
    AsmBrPieces (scBranchConstsOfStretch K hγ) lsfInit depth w fmt L capExp limbMul impl p I TR B5
      Ψ CFR :=
  ⟨X.JS, X.JS_mul, X.JS_ys, X.JS_space, X.JI, X.JI_mul, X.JI_space, X.JB, X.JB_mul, X.out, X.list⟩

/-- **Uniform branch-piece hypothesis on one program `p`** for every balancing depth `depth ≥ 1`:
fixed piece constants `K` with `K.firstWordExp 3 ≤ 39`, fixed procedure indices `I` and fixed
`depth`-free branch procedures `HasAsmBrProcs p bp impl fCFRoot I`, and for every `depth ≥ 1`,
local tour/bundle representations `TR`, `B5`, restart-compatible walk potential `Ψ`, and
`AsmBrPieces K (lsfInit L fmt.precision) depth w fmt L capExp limbMul impl p I TR B5 Ψ CF.rep`
for every `(capExp, limbMul, w, fmt, L)` and component-LSF family `CF` with `CF.fRoot = fCFRoot`. -/
structure ScBranchPiecesHyp (CFS : AsmCompFamilySpec) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (fCFInit fCFBatch fCFRoot : ℕ)
    (bp : AsmBranchProcs) : Prop where
  inst : ∃ (K : AsmBrConsts) (I : AsmBrProcIdx),
    K.firstWordExp 3 ≤ 39 ∧
    HasAsmBrProcs p bp impl fCFRoot I ∧
    ∀ depth : ℕ, 1 ≤ depth →
      ∃ (TR : ℕ → ℕ → DSRep AsmTourAbs)
        (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
        (Ψ : BundleTreeState depth → ℕ),
        (∀ vCap eCap, (TR vCap eCap).Local) ∧
        (∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local) ∧
        (∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH) ∧
        AsmWalkPotRestartOK impl depth Ψ ∧
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L : ℕ)
          (CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch),
          fmt.precision ≤ 4 * L → CF.fRoot = fCFRoot →
          Nonempty (AsmBrPieces K (lsfInit L fmt.precision) depth w fmt L capExp limbMul impl p I
            TR B5 Ψ CF.rep)

/-- **Uniform derivation of `ScBranchModuleHyp` from `asmBranchAt_value`,
`asmBranchAt_value_readoutLayout`, and `AsmBrPieces`** on one fixed program `p` for every
balancing depth `depth ≥ 1`. -/
theorem scBranchModuleHyp_of_pieces {CFS : AsmCompFamilySpec} {C_lsst : ℝ}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {p : Program}
    {fCFInit fCFBatch fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hV : ScBranchPiecesHyp CFS lsfInit impl p fCFInit fCFBatch fCFRoot bp) :
    ScBranchModuleHyp CFS C_lsst lsfInit impl p fCFInit fCFBatch fCFRoot bp := by
  refine ⟨fun hγs => ?_⟩
  have hγ : SparsifyPolyStretch impl := sparsifyPolyStretch_of_subpolyStretch hγs
  obtain ⟨K, I, hwe, hP, hDepth⟩ := hV.inst
  refine ⟨asmBrSpec CFS impl (scBranchConstsOfStretch K hγ), asmBrSpec_wordExp_three hwe,
    fun capExp limbMul depth w fmt L hd hPL CF hfRoot => ?_⟩
  obtain ⟨TR, B5, Ψ, hTR, hB5, hTh, hΨ, hPieces⟩ := hDepth depth hd
  obtain ⟨X⟩ := hPieces capExp limbMul w fmt L CF hPL hfRoot
  let X' := X.withStretch hγ
  have hP' : HasAsmBrProcs p bp impl CF.fRoot I := by rw [hfRoot]; exact hP
  exact ⟨asmBranchAt_value (K := scBranchConstsOfStretch K hγ) (C_lsst := C_lsst) (CF := CF)
      hTR hB5 hTh hΨ (Classical.choose_spec (Classical.choose_spec hγ)) (fun _ _ _ _ => rfl) hP' X',
    asmBranchAt_value_readoutLayout (K := scBranchConstsOfStretch K hγ) (C_lsst := C_lsst)
      (CF := CF) hTR hB5 hTh hΨ (Classical.choose_spec (Classical.choose_spec hγ))
      (fun _ _ _ _ => rfl) hP' X'⟩

/-! ## Per-depth bridge from `asmBranchAt_value` and `AsmBrPieces` -/

/-- The pieces needed to instantiate `asmBranchAt_value` and `asmBranchAt_value_readoutLayout` at
a fixed tree depth `depth`: fixed piece constants `K` (with `K.firstWordExp 3 ≤ 39`), fixed
depth-free procedures `HasAsmBrProcs p bp impl fCFRoot I`, tour/bundle representations `TR`, `B5`,
walk potential `Ψ`, and `AsmBrPieces` for every `(capExp, limbMul, w, fmt, L)` and `CF`. -/
structure ScBranchValueAtDepth (CFS : AsmCompFamilySpec) (lsfInit : ℕ → ℕ → LSFInit)
    (impl : SparsifyImpl) (depth : ℕ) (p : Program) (fCFInit fCFBatch fCFRoot : ℕ)
    (bp : AsmBranchProcs) where
  K : AsmBrConsts
  hfirstWordExp : K.firstWordExp 3 ≤ 39
  I : AsmBrProcIdx
  TR : ℕ → ℕ → DSRep AsmTourAbs
  B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)
  Ψ : BundleTreeState depth → ℕ
  hTR : ∀ vCap eCap, (TR vCap eCap).Local
  hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local
  hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH
  hΨ : AsmWalkPotRestartOK impl depth Ψ
  hP : HasAsmBrProcs p bp impl fCFRoot I
  pieces : ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L : ℕ)
      (CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch),
      fmt.precision ≤ 4 * L → CF.fRoot = fCFRoot →
      AsmBrPieces K (lsfInit L fmt.precision) depth w fmt L capExp limbMul impl p I TR B5 Ψ CF.rep

/-- The `AsmBranchSpec` induced by `V : ScBranchValueAtDepth` and `hγ : SparsifyPolyStretch impl`. -/
noncomputable def ScBranchValueAtDepth.spec {CFS : AsmCompFamilySpec}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {depth : ℕ} {p : Program}
    {fCFInit fCFBatch fCFRoot : ℕ} {bp : AsmBranchProcs}
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp)
    (hγ : SparsifyPolyStretch impl) : AsmBranchSpec :=
  asmBrSpec CFS impl (scBranchConstsOfStretch V.K hγ)

theorem ScBranchValueAtDepth.spec_wordExp_le_39 {CFS : AsmCompFamilySpec}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {depth : ℕ} {p : Program}
    {fCFInit fCFBatch fCFRoot : ℕ} {bp : AsmBranchProcs}
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp)
    (hγ : SparsifyPolyStretch impl) :
    (V.spec hγ).wordExp 3 ≤ 39 :=
  asmBrSpec_wordExp_three V.hfirstWordExp

/-- Builds `AsmBranchAt` and `AsmBranchReadoutLayout` at `depth` directly from `asmBranchAt_value`
and `asmBranchAt_value_readoutLayout`, with no readout-layout hypothesis. -/
noncomputable def scBranchAt_of_value {CFS : AsmCompFamilySpec} {C_lsst : ℝ}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {depth : ℕ} {p : Program}
    {fCFInit fCFBatch fCFRoot : ℕ} {bp : AsmBranchProcs}
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp)
    (hγ : SparsifyPolyStretch impl)
    {capExp limbMul w : ℕ} {fmt : Num.Format w} {L : ℕ}
    (CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch)
    (hPL : fmt.precision ≤ 4 * L) (hfRoot : CF.fRoot = fCFRoot) :
    AsmBranchAt (V.spec hγ) CFS (lsfInit L fmt.precision) C_lsst depth w fmt L capExp limbMul
      impl (scBranchReemb impl depth) p fCFInit fCFBatch CF bp :=
  asmBranchAt_value (K := scBranchConstsOfStretch V.K hγ) (C_lsst := C_lsst) (CF := CF)
    V.hTR V.hB5 V.hTh V.hΨ (Classical.choose_spec (Classical.choose_spec hγ))
    (fun _ _ _ _ => rfl) (by rw [hfRoot]; exact V.hP)
    ((V.pieces capExp limbMul w fmt L CF hPL hfRoot).withStretch hγ)

theorem scBranchAt_of_value_readoutLayout {CFS : AsmCompFamilySpec} {C_lsst : ℝ}
    {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl} {depth : ℕ} {p : Program}
    {fCFInit fCFBatch fCFRoot : ℕ} {bp : AsmBranchProcs}
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp)
    (hγ : SparsifyPolyStretch impl)
    {capExp limbMul w : ℕ} {fmt : Num.Format w} {L : ℕ}
    (CF : AsmCompFamilyAt CFS (lsfInit L fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch)
    (hPL : fmt.precision ≤ 4 * L) (hfRoot : CF.fRoot = fCFRoot) :
    AsmBranchReadoutLayout (scBranchAt_of_value (C_lsst := C_lsst) V hγ CF hPL hfRoot) :=
  asmBranchAt_value_readoutLayout (K := scBranchConstsOfStretch V.K hγ) (C_lsst := C_lsst)
    (CF := CF) V.hTR V.hB5 V.hTh V.hΨ (Classical.choose_spec (Classical.choose_spec hγ))
    (fun _ _ _ _ => rfl) (by rw [hfRoot]; exact V.hP)
    ((V.pieces capExp limbMul w fmt L CF hPL hfRoot).withStretch hγ)

/-- **Top-layer bridged theorem for `KFRBL` + `SparseCoreReadoutFootAt` at fixed `depth ≥ 1`**
directly from `asmBranchAt_value`, `asmBranchAt_value_readoutLayout`, and `AsmBrPieces`. -/
theorem asmTop_bridged_reemb_at_depth_of_branchValue
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {depth : ℕ} {p : Program} {b fCFInit fCFBatch fCFExport fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hdepth : 1 ≤ depth)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifyPolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit p fCFInit fCFBatch fCFExport fCFRoot)
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp) :
    let BRS := V.spec hγ
    asmTopWordExp CFS BRS 3 ≤ 39 ∧
    ∀ capExp limbMul : ℕ,
      let P := asmTopParams CFS BRS capExp limbMul
      let alloc := asmTopAlloc CFS BRS capExp
      P.wordExp = asmTopWordExp CFS BRS capExp ∧
      ∀ (w : ℕ) (fmt : Num.Format w) (L : ℕ),
        fmt.precision ≤ 4 * L →
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
                    G k M N vCap eCap capExp P (alloc sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (alloc sizeParam) R p (asmTopOpIdx b) := by
  intro BRS
  refine ⟨?_, fun capExp limbMul => ⟨rfl, fun w fmt L hPL => ?_⟩⟩
  · unfold asmTopWordExp
    rw [asmP10WordExp_at_3]
    exact max_le (max_le hCF.wordExp_le_39 (V.spec_wordExp_le_39 hγ)) (by decide)
  · obtain ⟨CF, hfExp, hfRoot⟩ := hCF.inst capExp limbMul w fmt L
    let BR := scBranchAt_of_value (C_lsst := C_lsst) V hγ CF hPL hfRoot
    have hLay : AsmBranchReadoutLayout BR :=
      scBranchAt_of_value_readoutLayout (C_lsst := C_lsst) V hγ CF hPL hfRoot
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

/-- **Top-layer bridged theorem for `KFBL` + `SparseCoreReadoutFootAt` at fixed `depth ≥ 1`**
directly from `asmBranchAt_value`, `asmBranchAt_value_readoutLayout`, and `AsmBrPieces`. -/
theorem asmTop_bridged_at_depth_of_branchValue
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit} {impl : SparsifyImpl}
    {depth : ℕ} {p : Program} {b fCFInit fCFBatch fCFExport fCFRoot : ℕ} {bp : AsmBranchProcs}
    (hdepth : 1 ≤ depth)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifyPolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hCF : ScCompFamilyHyp CFS lsfInit p fCFInit fCFBatch fCFExport fCFRoot)
    (V : ScBranchValueAtDepth CFS lsfInit impl depth p fCFInit fCFBatch fCFRoot bp) :
    let BRS := V.spec hγ
    asmTopWordExp CFS BRS 3 ≤ 39 ∧
    ∀ capExp limbMul : ℕ,
      let P := asmTopParams CFS BRS capExp limbMul
      let alloc := asmTopAlloc CFS BRS capExp
      P.wordExp = asmTopWordExp CFS BRS capExp ∧
      ∀ (w : ℕ) (fmt : Num.Format w) (L : ℕ),
        fmt.precision ≤ 4 * L →
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
                    G k M N vCap eCap capExp P (alloc sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInit L fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (alloc sizeParam) R p (asmTopOpIdx b) := by
  intro BRS
  obtain ⟨hwe3, hall⟩ :=
    asmTop_bridged_reemb_at_depth_of_branchValue (C_lsst := C_lsst) hdepth hp hγ hγt hCF V
  refine ⟨hwe3, fun capExp limbMul => ?_⟩
  obtain ⟨hwe, hP⟩ := hall capExp limbMul
  refine ⟨hwe, fun w fmt L hPL => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP w fmt L hPL
  refine ⟨τ, phi, foot, fun vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ vCap eCap
  exact ⟨rep, hloc, fun G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap =>
    let ⟨h1, h2⟩ := hR G k M N sizeParam hfmt hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap
    ⟨dsRep_implements_kfbl_of_kfrbl h1, h2⟩⟩

end MinCostFlow.SparseCore.Program
