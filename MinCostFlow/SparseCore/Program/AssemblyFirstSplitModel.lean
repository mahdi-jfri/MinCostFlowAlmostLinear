module

public import MinCostFlow.SparseCore.Program.AssemblyFirstSplitLists
public import MinCostFlow.SparseCore.Program.OutStepJoinModel
import MinCostFlow.SparseCore.CanonCoreSpec
import MinCostFlow.SparseCore.Program.OutFlags

/-!
# The split lists of a branch step

This file puts the bound of `AssemblyFirstSplitLists.lean` on one step of a branch. The core
graph is `coreGraph st.cs.G st.cs.lsf`, the core batch is `U_core` (the canonical core batch
`canonCoreBatch`), the output graph is the old output graph after the deletions of the leaving
edges, and the kept edges are `outKeep`. The marked edges `M` may be any set between the kept
edges and the old output edges. For instance, the tour may drop the marks of the edges that the
input batch deletes before the cuts.

* `outCutLens_sum_le`: the lengths of the split lists of the step sum to at most `Enc(U_S)` plus
  `4 ⌊log₂ (2 |E(S_cur)| + 1)⌋` per leaving edge.
* `outCutLens_sum_le_enc`: the same bound as a multiple of `Enc(U_S)`, since each leaving edge is
  a deletion of `U_S` and costs one.

The hypotheses are those of an output step (`OutStepReady`). They give what the bound needs:
- the core graph is valid, and the core batch is valid on it (`orderedCore_canonCoreBatch`);
- the old output graph is a subgraph of the core graph, so the kept edges have the same ends in
  both;
- the core batch deletes only edges that the input batch deletes, and no kept edge is one.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-- Deletions do not move the ends of the other edges. -/
theorem applyBatch_dels_ends (G : MGraph) : ∀ l : List ℕ,
    (G.applyBatch (l.map Update.delete)).tail = G.tail ∧
      (G.applyBatch (l.map Update.delete)).head = G.head
  | [] => ⟨rfl, rfl⟩
  | e :: l => applyBatch_dels_ends (G.applyUpdate (.delete e)) l

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- **The split lists of a branch step.** The marked edges `M` lie between the kept edges and
the old output edges. Then the lengths of the split lists of the core batch sum to at most the
encoding size of the output batch plus `4 ⌊log₂ (2 |E(S_cur)| + 1)⌋` per leaving edge. -/
theorem outCutLens_sum_le (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') {M : Finset ℕ}
    (hkM : outKeep sparsify st U ord ord' ⊆ M) (hM : M ⊆ st.S_cur.E) :
    (cutLens M (coreGraph st.cs.G st.cs.lsf) (stepBundleTree sparsify st U ord ord').U_core).sum ≤
      st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S +
        (outDelList sparsify st U ord ord').length * (4 * Nat.log 2 (2 * st.S_cur.E.card + 1)) := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, -, -, hS_sub, -⟩ := hready
  obtain ⟨_he, _hI', hOCB, -, -, hdelSub⟩ :=
    orderedCore_canonCoreBatch (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot (Nat.le_refl 2) hBU st.cs rfl hI
  have hUC : (stepBundleTree sparsify st U ord ord').U_core = canonCoreBatch st.cs U := rfl
  set keep := outKeep sparsify st U ord ord' with hkeep
  set delL := outDelList sparsify st U ord ord' with hdelL
  -- the core graph and the core batch are valid
  have hC : (coreGraph st.cs.G st.cs.lsf).IsValid := coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
  have hB : (coreGraph st.cs.G st.cs.lsf).BatchIsValid (canonCoreBatch st.cs U) := hOCB.1
  -- the output graph after the deletions has the kept edges, with the ends of the core graph
  have hE₁ : (st.S_cur.applyBatch (delL.map Update.delete)).E = keep :=
    outStep_G₁_E sparsify st U ord ord'
  have hends : ∀ e ∈ keep, (st.S_cur.applyBatch (delL.map Update.delete)).tail e =
        (coreGraph st.cs.G st.cs.lsf).tail e ∧
      (st.S_cur.applyBatch (delL.map Update.delete)).head e =
        (coreGraph st.cs.G st.cs.lsf).head e := by
    intro e he
    rw [(applyBatch_dels_ends st.S_cur delL).1, (applyBatch_dels_ends st.S_cur delL).2]
    exact hS_sub.2.2 e ((outKeep_subset sparsify st U ord ord').1 he)
  -- the core batch deletes no kept edge
  have hdel : ∀ e ∈ keep, Update.delete e ∉ canonCoreBatch st.cs U := by
    intro e he hmem
    have h₁ : e ∈ batchDeletes U :=
      hdelSub ((mem_batchDeletes_iff _ e).mpr ⟨_, hmem, rfl⟩)
    exact (Finset.mem_sdiff.mp (outKeep_subset_sdiff_batchDeletes sparsify st U ord ord' he)).2 h₁
  have hbound := cutLens_sum_le_log keep (canonCoreBatch st.cs U) M (coreGraph st.cs.G st.cs.lsf)
    (st.S_cur.applyBatch (delL.map Update.delete)) hC hB (hM.trans hS_sub.2.1) hkM hE₁ hends hdel
  -- the encoding size of the output batch holds that of the restricted splits
  have hBE : st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S =
      delL.length + (st.S_cur.applyBatch (delL.map Update.delete)).batchEnc
          (outSplitBatch sparsify st U ord ord') +
        (st.S_cur.applyBatch (delL.map Update.delete ++ outSplitBatch sparsify st U ord ord')).batchEnc
          (outInsBatch sparsify st U ord ord') := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
  have hsplits : outSplitBatch sparsify st U ord ord' = restrictSplits keep (canonCoreBatch st.cs U) :=
    rfl
  -- the marked edges that leave are leaving edges, and there are at most `|E(S_cur)|` marked edges
  have hlen : (M \ keep).card ≤ delL.length := by
    rw [hdelL, outDelList, Finset.length_sort]
    exact Finset.card_le_card (Finset.sdiff_subset_sdiff hM le_rfl)
  have hlog : Nat.log 2 (2 * M.card + 1) ≤ Nat.log 2 (2 * st.S_cur.E.card + 1) :=
    Nat.log_mono_right (by have := Finset.card_le_card hM; omega)
  have h₁ := Nat.mul_le_mul hlen (Nat.mul_le_mul_left 4 hlog)
  rw [hUC, hBE, hsplits]
  omega

/-- **The split lists of a branch step, as a multiple of `Enc(U_S)`.** Each leaving edge is a
deletion of the output batch, so there are at most `Enc(U_S)` of them. -/
theorem outCutLens_sum_le_enc (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') {M : Finset ℕ}
    (hkM : outKeep sparsify st U ord ord' ⊆ M) (hM : M ⊆ st.S_cur.E) :
    (cutLens M (coreGraph st.cs.G st.cs.lsf) (stepBundleTree sparsify st U ord ord').U_core).sum ≤
      st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S *
        (1 + 4 * Nat.log 2 (2 * st.S_cur.E.card + 1)) := by
  have h := outCutLens_sum_le sparsify st U ord ord' hready hkM hM
  have hBE : (outDelList sparsify st U ord ord').length ≤
      st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
    omega
  have := Nat.mul_le_mul_right (4 * Nat.log 2 (2 * st.S_cur.E.card + 1)) hBE
  rw [Nat.mul_add, Nat.mul_one]
  omega

end MinCostFlow.SparseCore.Program
