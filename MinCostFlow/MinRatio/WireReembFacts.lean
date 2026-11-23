module

public import MinCostFlow.MinRatio.WireReembModel
public import MinCostFlow.SparseCore.ReembFactsLazy
public import MinCostFlow.SparseCore.ReembFactsCost
public import MinCostFlow.SparseCore.ReembFactsStep

import MinCostFlow.SparseCore.LSFInsertNonTree
import MinCostFlow.SparseCore.Program.RestartModelCost
import MinCostFlow.DynSpanner.Program.CanonicalSparsify

/-!
# The three sparse-core re-embedding facts for `sparseCoreProgTool` (`WireReembFacts`)

Specializes the three reached-state facts of `SparseCore/ReembFactsLazy.lean`,
`SparseCore/ReembFactsCost.lean`, and `SparseCore/ReembFactsStep.lean` to the sparse-core program
tool `sparseCoreProgTool lsfInit C_lsst depth impl`, in the exact forms taken by
`progReemb_amortized` and `reembCovers_of_progTool` (`WireReembModel.lean`):

* `progTool_branchLazyCovers`: `BranchLazyCovers` on every step from a reached nonempty state.
* `progTool_branchCostLeMach`: `BranchCostLeMach` (`tr.cost ≤ tr.machCost`) on every reached state
  (for `1 ≤ depth` and `impl.γ_t M = 1`).
* `progTool_branchReembFacts`: `BranchReembFacts` on every valid ordered step from a reached
  nonempty state, for every surviving off-spanner core edge `e`.
* `progReemb_length_le_cost_of_input`, `progReemb_amortized_of_input`,
  `progReemb_amortized_of_update`: the length and amortized bounds of `WireReembModel.lean` with
  `BranchLazyCovers` and `BranchCostLeMach` discharged from `SparseCoreOrdInput`.
* `reembCovers_of_progTool_of_input`: `ReembCovers C C' i (progReemb ...)` with `BranchReembFacts`
  discharged from `SparseCoreOrdInput`, `G.BatchIsValid U`, and `OrderedBatch G U ord ord'`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program
open MinCostFlow.SparseCore.Program.Restart

section Facts

variable {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}

/-- **`BranchLazyCovers` on `sparseCoreProgTool`.** On every step from a nonempty state reached
under `SparseCoreOrdInput`, the lazy initialization cost of every newly activated component covers
the edges of its buckets. -/
theorem progTool_branchLazyCovers {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (U : List Update) (ord' : ℕ → List End) :
    BranchLazyCovers (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord' :=
  sparseCoreOrdInput_lazyCovers hk hinp hne hInit U st.ord ord'

/-- **`BranchCostLeMach` on `sparseCoreProgTool`.** On every state reached under
`SparseCoreOrdInput` (with `0 < k`, `1 ≤ depth`, and `impl.γ_t M = 1`), every valid branch `j`
satisfies `(st.trees j).cost ≤ (st.trees j).machCost`. -/
theorem progTool_branchCostLeMach {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hdepth : 1 ≤ depth) (hγt : impl.γ_t M = 1)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    BranchCostLeMach (st.trees j) :=
  sparseCoreOrdInput_cost_le_machCost hk hdepth (one_le_dsAmortConst impl)
    (canonicalSparsify_spec impl M hγt) hinp hInit

/-- **`BranchReembFacts` on `sparseCoreProgTool`.** On every valid ordered step `(U, ord')` from
a nonempty state reached under `SparseCoreOrdInput` (with `0 < k` and `1 ≤ depth`), every edge `e`
in the new core graph and outside the new sparsified core satisfies all five hypotheses of
`mem_stepBundleTree_reembList_of_emb_ne`. -/
theorem progTool_branchReembFacts {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k) (hdepth : 1 ≤ depth)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    (U : List Update) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) {e : ℕ}
    (heCore' : e ∈ (coreGraph
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord').state.cs.G
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord').state.cs.lsf).E)
    (heOff' : e ∉ (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U
      st.ord ord').state.S_cur.E) :
    BranchReembFacts (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord' e :=
  sparseCoreOrdInput_reembFacts hk hdepth (canonicalSparsify_spec_absorb impl M) hinp hne U ord'
    hBV hOrdB hInit heCore' heOff'

/-! ## Discharged wrappers for `WireReembModel` -/

/-- **The length against the model cost on a reached state** (discharges `BranchLazyCovers` from
`progReemb_length_le_cost`). -/
theorem progReemb_length_le_cost_of_input {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    (st.trees j).cost + (progReemb lsfInit C_lsst depth impl st U ord' j).length ≤
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.trees j).cost :=
  progReemb_length_le_cost st hne U ℓ g ord' j
    (progTool_branchLazyCovers hk hinp hne hInit U ord')

/-- **The length against the machine cost, amortized, on reached states** (discharges
`BranchLazyCovers` and both `BranchCostLeMach` hypotheses of `progReemb_amortized` from
`SparseCoreOrdInput` before and after the update). -/
theorem progReemb_amortized_of_input {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G G' : MGraph} {ord ord'' : ℕ → List End} {n n' : ℕ}
    (hdepth : 1 ≤ depth) (hγt : impl.γ_t M = 1)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (hinp' : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1 G' ord'' n')
    {j : ℕ} (hj : j < st.k) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let st' := (T.updateOrd st U ℓ g ord').1
    (progReemb lsfInit C_lsst depth impl st U ord' j).length +
        ((st'.trees j).machCost - (st'.trees j).cost) ≤
      (T.cost st' - T.cost st) + ((st.trees j).machCost - (st.trees j).cost) := by
  have hk : 0 < k := by
    have hk_eq : st.k = k := (asm_input_inv _ _ _ _ _ _ hinp).1
    omega
  exact progReemb_amortized st hne U ℓ g ord' hj
    (progTool_branchLazyCovers hk hinp hne hInit U ord')
    (progTool_branchCostLeMach hk hdepth hγt hinp hInit)
    (progTool_branchCostLeMach hk hdepth hγt hinp' hInit)

/-- **The length against the machine cost, amortized, from update preconditions** (constructs
`SparseCoreOrdInput` after the update via `SparseCoreOrdInput.update`). -/
theorem progReemb_amortized_of_update {k M N : ℕ} {st : SparseCoreBundleState depth}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hdepth : 1 ≤ depth) (hγt : impl.γ_t M = 1)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hPos : ∀ e ∈ (G.applyBatch U).E, 0 < ℓ e)
    (hOrdB : OrderedBatch G U ord ord')
    (hThr : ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N)
    {j : ℕ} (hj : j < st.k) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let st' := (T.updateOrd st U ℓ g ord').1
    (progReemb lsfInit C_lsst depth impl st U ord' j).length +
        ((st'.trees j).machCost - (st'.trees j).cost) ≤
      (T.cost st' - T.cost st) + ((st.trees j).machCost - (st.trees j).cost) :=
  progReemb_amortized_of_input hdepth hγt hinp hne U ℓ g ord'
    (SparseCoreOrdInput.update hinp U ℓ g ord' hBV hPos hOrdB hThr) hj hInit

/-- **`ReembCovers` at a level on reached states** (discharges `BranchReembFacts` from
`reembCovers_of_progTool`). -/
theorem reembCovers_of_progTool_of_input {C C' : TreeChain} {i k M N : ℕ}
    (hi : i < C.d) (hi' : i < C'.d) (hbran : C'.bran i = C.bran i)
    (hk : 0 < k) (hdepth : 1 ≤ depth)
    (st : SparseCoreBundleState depth) {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    (hne : st.isNonempty = true)
    (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (hBV : G.BatchIsValid U) (hOrdB : OrderedBatch G U ord ord')
    (hInit : IsValidLSFInitFor lsfInit C_lsst k (C.bran i))
    (hG' : C'.G i = G.applyBatch U)
    (hlsf' : C'.lsfs i = (sparseCoreProgTool lsfInit C_lsst depth impl).lsfs
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1)
    (hS' : C'.S i = (sparseCoreProgTool lsfInit C_lsst depth impl).S
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1)
    (hemb : C.emb i = (sparseCoreProgTool lsfInit C_lsst depth impl).emb st)
    (hemb' : C'.emb i = (sparseCoreProgTool lsfInit C_lsst depth impl).emb
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1) :
    ReembCovers C C' i (progReemb lsfInit C_lsst depth impl st U ord' (C.bran i)) := by
  have hup := progTool_updateOrd_of_nonempty (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    st hne U ℓ g ord'
  have hne' : ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.isNonempty =
      true := by
    rw [hup]; exact hne
  refine reembCovers_of_progTool hi hi' hbran st hne U ℓ g ord' hS' hemb hemb' fun e _ he' => ?_
  obtain ⟨heCore_C', heOff_C'⟩ := Finset.mem_sdiff.mp he'
  have hS'i : C'.activeS i =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord').state.S_cur := by
    simp only [TreeChain.activeS, hi', ↓reduceIte]
    rw [hS', hbran, progTool_S_of_nonempty _ hne', hup]
  have hlsf'i : C'.activeLSF i =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord').state.cs.lsf := by
    simp only [TreeChain.activeLSF, hi', ↓reduceIte, hlsf', hbran]
    change (if ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.isNonempty
        then (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.trees
          (C.bran i)).cs.lsf
        else emptyLSF) = _
    simp only [hup, hne, ↓reduceIte]
  have hG'i : C'.G i =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord').state.cs.G := by
    have hcompG : ∀ (cs : CompLSFState) (V : List Update),
        (compLSFBatch cs V).G = cs.G.applyBatch V := by
      intro cs V
      induction V generalizing cs with
      | nil => rfl
      | cons u rest ih => exact ih (compLSFStepSingle cs u)
    rw [hG']
    change G.applyBatch U = (compLSFBatch (st.trees (C.bran i)).cs U).G
    rw [hcompG, sparseCoreOrdInput_cs_G_eq hinp hne (C.bran i)]
  have heCore' : e ∈ (coreGraph
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord').state.cs.G
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord').state.cs.lsf).E := by
    unfold TreeChain.activeCore at heCore_C'
    rwa [hG'i, hlsf'i] at heCore_C'
  have heOff' : e ∉ (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U
      st.ord ord').state.S_cur.E := by
    rwa [hS'i] at heOff_C'
  exact progTool_branchReembFacts hk hdepth hinp hne U ord' hBV hOrdB hInit heCore' heOff'

end Facts

end MinCostFlow.MinRatio
