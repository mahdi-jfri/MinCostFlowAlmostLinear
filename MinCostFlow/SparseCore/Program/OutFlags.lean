module

public import MinCostFlow.SparseCore.Program.OutStepSpecSmall
import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.Chain.CoreGraph

/-!
# The flags of the leaving edges

The restated output step takes `OutFlagsOk`: an end of an old output edge that is still an edge
of the graph after the step (`cs'.G.E`) is in a new core list, and an end of one that is not in
the new graph is in none. This file proves it from the model (`outFlagsOk_of`), without forbidding
the input batch from deleting an edge and inserting it again.

An old output edge is a core edge, so it is not a forest edge. The forest only loses edges in a
batch (`compLSFBatch_decremental`). So an old output edge that lies in the graph after the batch
is a core edge after the batch, and its ends are in the new core lists. An edge not in the graph
after the batch is not a core edge, so its ends are in no new core list.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

theorem mem_applyBatch_of_not_delete {e : ℕ} :
    ∀ (G : MGraph) (U : List Update), e ∈ G.E → (∀ u ∈ U, u ≠ .delete e) →
      e ∈ (G.applyBatch U).E
  | _, [], he, _ => he
  | G, u :: U, he, hU => by
    have he' : e ∈ (G.applyUpdate u).E := by
      cases u with
      | insert f a b => exact Finset.mem_insert_of_mem he
      | delete f =>
        have hf : f ≠ e := fun h => hU _ List.mem_cons_self (by rw [h])
        exact Finset.mem_erase.mpr ⟨hf.symm, he⟩
      | split v v' St Sh => exact he
    exact mem_applyBatch_of_not_delete (G.applyUpdate u) U he'
      (fun u' hu' => hU u' (List.mem_cons_of_mem _ hu'))

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- **The flags of the leaving edges are right.** -/
theorem outFlagsOk_of {vCap : ℕ} (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord')
    (hR : ∀ v ∈ (stepBundleTree sparsify st U ord ord').state.cs.RF.R, v < vCap) :
    OutFlagsOk sparsify st U ord ord' vCap := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, hS_val, hS_V, hS_sub, hS_sub'⟩ := hready
  have hI' := compLSFBatch_inv hI hBU
  have hG_eq := compLSFBatch_G st.cs U
  have hcast : (hG_eq.symm ▸ σ : Rotation (compLSFBatch st.cs U).G).order = ord' := by
    have : ∀ {G H : MGraph} (h : G = H) (σ : Rotation G), (h ▸ σ).order = σ.order := by
      intro G H h σ; subst h; rfl
    exact (this hG_eq.symm σ).trans hσ
  have hcs : (stepBundleTree sparsify st U ord ord').state.cs = compLSFBatch st.cs U := rfl
  have hex : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ)
      (_ : CompLSFInv C_lsst ℓ₀ (stepBundleTree sparsify st U ord ord').state.cs)
      (ρ : Rotation (stepBundleTree sparsify st U ord ord').state.cs.G), ρ.order = ord' := by
    rw [hcs]; exact ⟨C_lsst, ℓ₀, hI', _, hcast⟩
  -- membership in the new core lists
  have hmemiff : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify st U ord ord').state ord' v ↔
      x.1 ∈ (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).E ∧
        (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).src x = v := by
    intro v x
    unfold outCoreOrder
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    exact Rotation.mem_order _ v x
  have hcoreV := coreGraph_isValid (L := (compLSFBatch st.cs U).lsf) hI'.hG_val (compLSF_RF_isRSF hI')
  intro e he b
  have heCore : e ∈ st.cs.G.E ∧ e ∉ st.cs.RF.F.E := Finset.mem_sdiff.mp (hS_sub.2.1 he)
  constructor
  · intro heG'
    have heF' : e ∉ (compLSFBatch st.cs U).RF.F.E := fun h =>
      heCore.2 ((compLSFBatch_decremental hI hBU).1 h)
    have heC : e ∈ (coreGraph (compLSFBatch st.cs U).G (compLSFBatch st.cs U).lsf).E :=
      Finset.mem_sdiff.mpr ⟨heG', heF'⟩
    refine ⟨_, ?_, (hmemiff _ (e, b)).mpr ⟨heC, rfl⟩⟩
    apply hR
    rw [hcs]
    have hv := hcoreV e heC
    cases b
    · exact hv.2
    · exact hv.1
  · intro hnotG' v hv
    exact hnotG' (Finset.mem_sdiff.mp ((hmemiff v (e, b)).mp hv).1).1

/-- Kept edges are old output edges that the input batch does not delete. This lets a caller
instantiate the entry-mark hypothesis of `sig_outStepSmall_runs` with `E₀ = st.S_cur.E \ batchDeletes U`
(the edges whose marks remain after `tourApplyEdits` drops `batchDeletes U`). -/
theorem outKeep_subset_sdiff_batchDeletes (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) :
    outKeep sparsify st U ord ord' ⊆ st.S_cur.E \ batchDeletes U := by
  intro e he
  simp only [outKeep, Finset.mem_sdiff, Finset.mem_inter] at he ⊢
  exact ⟨he.1.1.1, he.1.2⟩

end MinCostFlow.SparseCore.Program
