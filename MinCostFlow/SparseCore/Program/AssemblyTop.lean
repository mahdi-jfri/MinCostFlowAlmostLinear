module

public import MinCostFlow.SparseCore.Program.AssemblyTopOps
public import MinCostFlow.SparseCore.Program.AssemblyContractLayoutTop

/-!
# Full top-layer implementation of the sparse-core contract (`AssemblyTop`)

Combines `asmTop_init_runs`, `asmTop_update_runs`, `asmTop_restart_runs`, and the four readout
operations (`op 2`..`op 5`, with layout/footprint lemmas in `AssemblyContractLayoutTop.lean`) into:
* `asmTop_implements_kfr`: full `DSRep.Implements` against `sparseCoreOrdMachineContractKFRBL`
  (including per-branch `reembList` on `op 0`, block-aligned input edits, and readout layouts on
  ops `2`, `3`, `5`).
* `asmTop_implements_kf`: corollary for `sparseCoreOrdMachineContractKFBL`.
* `asmTop_uniform_reemb_cap` and `asmTop_uniform_cap`: uniform top-layer statements with
  level-independent `(τ, phi, foot)` and `R` quantified before `L`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Full `DSRep.Implements` for the top layer -/

/-- **Top-layer `DSRep.Implements` against `sparseCoreOrdMachineContractKFRBL`** (including `reembList`
on `op 0`, block-aligned input edits `OrdEditsForBatch`, readout layout postconditions on ops
`2`, `3`, `5`, real P1 `ordStore_implements_cap`, linear-time order compactor, and empty-graph
dispatch). -/
theorem asmTop_implements_kfr
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hfExp : fCFExport = CF.fExport)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hfmt : fmt.limbBits = 4) (hPL : fmt.precision ≤ 4 * L) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (hdepth_le : depth ≤ M + N + k + L) (hdepth_lg : depth ≤ bundleLogFactor M N)
    (hdepth_ch : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hsize : M + N + k + vCap + eCap + L + depth ≤ sizeParam)
    (hγt : impl.γ_t M = 1)
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j)
    (hGn_le : G.n ≤ G.m + 1)
    (hCFmt : CompInitFormatHyp L fmt.precision k G.m)
    (hkCap : k ≤ (M + N + 2) ^ capExp) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap).Implements w p (asmTopInitIdx b) (asmTopOpIdx b)
      (sparseCoreOrdMachineContractKFRBL fmt L depth T (bundleToolReemb brReemb) G k M N vCap eCap capExp P alloc) := by
  intro T P alloc
  let D := sparseCoreOrdMachineContractKFRBL fmt L depth T (bundleToolReemb brReemb) G k M N vCap eCap capExp P alloc
  let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
    CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
  refine ⟨asmTopRepEq_local CF.rep_local BR.rep_local,
    asmTop_init_runs (sizeParam := sizeParam) CF BR hp hfExp hfmt hPL hcap hdepth hdepth_le hγt hInit hGn_le hCFmt hkCap,
    fun i hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp => ?_⟩
  match i with
  | 0 => exact asmTop_update_runs CF BR hp hfmt hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize hγt hInit hkCap hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  | 1 => exact asmTop_restart_runs (G₀ := G) CF BR hp hfmt hcap hdepth hdepth_le hsize hγt hInit hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  | 2 =>
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨fv, fe, hLw, hLSF, hfEnd, _, hStDesc, hNum, hDen, _⟩, hresp, hcost⟩ :=
      asmTop_op2_runs CF BR hLay hp G k M N vCap eCap sizeParam hfmt hcap hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
    exact ⟨body, hbody, o, st', c, hrun, a, x', hrep',
      ⟨rfl, fv, fe, hLw, hLSF, hfEnd, hStDesc, fun e he => (hNum e he).1, fun e he => (hDen e he).1⟩, hresp, hcost⟩
  | 3 =>
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨gv, ge, hDG, hgv, hge, hEnd, _⟩, hresp, hcost⟩ :=
      asmTop_op3_runs CF BR hLay hp G k M N vCap eCap sizeParam hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
    exact ⟨body, hbody, o, st', c, hrun, a, x', hrep', ⟨rfl, gv, ge, hDG, hgv, hge, hEnd⟩, hresp, hcost⟩
  | 4 =>
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨hEmbRd, hBd, hCapLe, hW, _, _⟩, hresp, hcost⟩ :=
      asmTop_op4_runs CF BR hLay hp G k M N vCap eCap sizeParam hdepth hInit hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
    exact ⟨body, hbody, o, st', c, hrun, a, x', hrep', ⟨rfl, hEmbRd, hBd, hCapLe, hW⟩, hresp, hcost⟩
  | 5 =>
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨words, hOrd, hLe, hPtr, _, hW⟩, hresp, hcost⟩ :=
      asmTop_op5_runs CF BR hLay hp G k M N vCap eCap sizeParam hcap hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
    exact ⟨body, hbody, o, st', c, hrun, a, x', hrep', ⟨rfl, words, hOrd, hLe, hPtr, hW⟩, hresp, hcost⟩
  | i + 6 => exact False.elim hpre

/-- **Top-layer `DSRep.Implements` against `sparseCoreOrdMachineContractKFBL`**: immediate corollary
of `asmTop_implements_kfr` via `dsRep_implements_kfbl_of_kfrbl`. -/
theorem asmTop_implements_kf
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hfExp : fCFExport = CF.fExport)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hfmt : fmt.limbBits = 4) (hPL : fmt.precision ≤ 4 * L) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (hdepth_le : depth ≤ M + N + k + L) (hdepth_lg : depth ≤ bundleLogFactor M N)
    (hdepth_ch : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hsize : M + N + k + vCap + eCap + L + depth ≤ sizeParam)
    (hγt : impl.γ_t M = 1)
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j)
    (hGn_le : G.n ≤ G.m + 1)
    (hCFmt : CompInitFormatHyp L fmt.precision k G.m)
    (hkCap : k ≤ (M + N + 2) ^ capExp) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap).Implements w p (asmTopInitIdx b) (asmTopOpIdx b)
      (sparseCoreOrdMachineContractKFBL fmt L depth T G k M N vCap eCap capExp P alloc) :=
  dsRep_implements_kfbl_of_kfrbl
    (asmTop_implements_kfr CF BR hLay hp hfExp G k M N vCap eCap sizeParam hfmt hPL hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize hγt hInit hGn_le hCFmt hkCap)

/-- **Uniform top-layer theorem (`SparseCoreOrdProgramUniformReembCapLayout`)**: given a polynomial
stretch bound `SparsifyPolyStretch impl`, unit time stretch `∀ m, impl.γ_t m = 1`, and any uniform
P4 family and branch module family with `L`-independent concrete representations `R_CF`, `R_BR`
and readout layouts `AsmBranchReadoutLayout BR`, the relocated top-layer program `p` meets
`SparseCoreOrdProgramUniformReembCapLayout` (and `SparseCoreOrdProgramUniformCapLayout`). -/
theorem asmTop_uniform_reemb_cap
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifyPolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hModules : SparsifyPolyStretch impl →
      ∃ BRS : AsmBranchSpec,
        ∀ capExp limbMul depth w (fmt : Num.Format w),
          1 ≤ depth →
          ∃ (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth)),
            R_CF.Local ∧ R_BR.Local ∧
            ∀ L, ∃ (CF : AsmCompFamilyAt CFS (lsfInitAuto fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch),
              CF.rep = R_CF ∧ CF.fExport = fCFExport ∧
              ∃ (BR : AsmBranchAt BRS CFS (lsfInitAuto fmt.precision) C_lsst depth w fmt L capExp limbMul impl
                (brReemb depth) p fCFInit fCFBatch CF bp), BR.rep = R_BR ∧ AsmBranchReadoutLayout BR) :
    SparseCoreOrdProgramUniformReembCapLayout C_lsst lsfInitAuto impl brReemb p
      (asmTopInitIdx b) (asmTopOpIdx b) := by
  obtain ⟨BRS, hMod⟩ := hModules hγ
  intro capExp
  refine ⟨asmTopWordExp CFS BRS capExp, fun limbMul =>
    ⟨asmTopParams CFS BRS capExp limbMul, asmTopAlloc CFS BRS capExp, rfl, fun depth w fmt hdepth => ?_⟩⟩
  obtain ⟨R_CF, R_BR, hCF_loc, hBR_loc, hInst⟩ := hMod capExp limbMul depth w fmt hdepth
  refine ⟨AsmTopMeta R_CF.τ R_BR.τ,
    fun _ x mem => asmTopPhi R_CF R_BR x mem,
    fun hndl x addr => asmTopFoot R_CF R_BR rfl rfl hndl x addr,
    fun L vCap eCap => ?_⟩
  obtain ⟨CF, hCF_eq, hfExp_eq, BR, hBR_eq, hLay⟩ := hInst L
  refine ⟨(asmTopRepEq (lsfInit := lsfInitAuto fmt.precision) (C_lsst := C_lsst) (impl := impl)
      R_CF R_BR (fun x => CF.vCapOf (hCF_eq.symm ▸ x)) (fun x => CF.eCapOf (hCF_eq.symm ▸ x))
      (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).rep,
    asmTopRepEq_local (cfV := fun x => CF.vCapOf (hCF_eq.symm ▸ x))
      (cfE := fun x => CF.eCapOf (hCF_eq.symm ▸ x)) hCF_loc hBR_loc,
    fun G k M N sizeParam hfmt hPL hcap hdepth_le hdepth_lg hdepth_ch hsize hInit hGn_le hCFmt hkCap => ?_⟩
  have himpl := asmTop_implements_kfr CF BR hLay hp hfExp_eq.symm G k M N vCap eCap sizeParam
    hfmt hPL hcap hdepth hdepth_le hdepth_lg hdepth_ch hsize (hγt M) hInit hGn_le hCFmt hkCap
  have hfoot := asmTop_readoutFoot_implements CF BR hLay hp G k M N vCap eCap sizeParam hfmt hcap hdepth hInit
  cases hCF_eq; cases hBR_eq
  exact ⟨himpl, hfoot⟩

/-- Uniform top-layer theorem for `sparseCoreOrdMachineContractKFBL` + `SparseCoreReadoutFootAt`. -/
theorem asmTop_uniform_cap
    {CFS : AsmCompFamilySpec} {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hγ : SparsifyPolyStretch impl)
    (hγt : ∀ m, impl.γ_t m = 1)
    (hModules : SparsifyPolyStretch impl →
      ∃ BRS : AsmBranchSpec,
        ∀ capExp limbMul depth w (fmt : Num.Format w),
          1 ≤ depth →
          ∃ (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth)),
            R_CF.Local ∧ R_BR.Local ∧
            ∀ L, ∃ (CF : AsmCompFamilyAt CFS (lsfInitAuto fmt.precision) w fmt L capExp limbMul p fCFInit fCFBatch),
              CF.rep = R_CF ∧ CF.fExport = fCFExport ∧
              ∃ (BR : AsmBranchAt BRS CFS (lsfInitAuto fmt.precision) C_lsst depth w fmt L capExp limbMul impl
                (brReemb depth) p fCFInit fCFBatch CF bp), BR.rep = R_BR ∧ AsmBranchReadoutLayout BR) :
    SparseCoreOrdProgramUniformCapLayout C_lsst lsfInitAuto impl p (asmTopInitIdx b) (asmTopOpIdx b) :=
  sparseCoreOrdProgramUniformCapLayout_of_reemb (asmTop_uniform_reemb_cap hp hγ hγt hModules)

end MinCostFlow.SparseCore.Program
