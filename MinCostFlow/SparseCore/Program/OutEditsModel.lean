module

public import MinCostFlow.SparseCore.Program.OutSpec
public import MinCostFlow.SparseCore.Program.OutEditsBatch
public import MinCostFlow.SparseCore.BundleOutOrder
import MinCostFlow.SparseCore.BundleOutBatchSpec

/-!
# The order edits of one output step

At each step a branch changes its output graph by `U_S = buildUSOrd …`, which is the deletions of
the leaving edges, the core splits restricted to the kept edges, and the insertions of the
entering edges, in this order (`stepBundleTree_U_S_split`). The output order changes along `U_S`
by an ordered batch (`stepBundleTree_outOrder`).

This file names the edits that the output step writes (`outStepEdits`): `dropEdge` for each
leaving edge, `moveEnds` for each split, two `insertBefore` for each entering edge (each end goes
before the next end after it, in the new output list, that is already present), and `rotateTo` at
the vertices of a list `T`. The main result, `stepBundleTree_outStepEdits`, says that under the
hypotheses of the step (`OutStepReady`) these edits turn the old output order `st.outOrder ord`
into the new one, as soon as `T` holds every vertex whose new output list is not empty. The list
of all new roots is such a list (`outOrder_eq_nil_of_not_mem`), so `BranchOutAt`'s order clause
can always be met (`stepBundleTree_outStepEdits_roots`). A program that pays only for the batch
must use a shorter list, of the roots whose list start moves.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The leaving output edges of a step, in increasing order. -/
noncomputable def outDelList (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    List ℕ :=
  (st.S_cur.E \ outKeep sparsify st U ord ord').sort (· ≤ ·)

/-- The entering output edges of a step, in increasing order. -/
noncomputable def outInsList (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    List ℕ :=
  ((stepBundleTree sparsify st U ord ord').state.S_cur.E \ outKeep sparsify st U ord ord').sort
    (· ≤ ·)

/-- The deletions and splits of the output batch. -/
noncomputable def outPrefixBatch (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) : List Update :=
  (outDelList sparsify st U ord ord').map Update.delete ++
    restrictSplits (outKeep sparsify st U ord ord') (stepBundleTree sparsify st U ord ord').U_core

/-- The insertions of the output batch, between the new roots of the endpoints. -/
noncomputable def outInsBatch (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) : List Update :=
  let cs' := (stepBundleTree sparsify st U ord ord').state.cs
  (outInsList sparsify st U ord ord').map fun e =>
    Update.insert e (cs'.RF.root (cs'.G.tail e)) (cs'.RF.root (cs'.G.head e))

/-- The output batch is its deletions and splits, then its insertions. -/
theorem stepBundleTree_U_S_split (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) :
    (stepBundleTree sparsify st U ord ord').U_S =
      outPrefixBatch sparsify st U ord ord' ++ outInsBatch sparsify st U ord ord' := by
  rw [stepBundleTree_U_S_eq]
  rfl

/-- The edits of an output step, with `rotateTo` at the vertices of `T`. -/
noncomputable def outStepEdits (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T : List ℕ) : List OrdEdit :=
  let st' := (stepBundleTree sparsify st U ord ord').state
  outPrefixEdits (outPrefixBatch sparsify st U ord ord') ++
    outInsertEdits (st'.outOrder ord') st'.S_cur.src (outInsBatch sparsify st U ord ord') ++
    outRotateEdits (st'.outOrder ord') T

private theorem restrictSplits_notInsert (keep : Finset ℕ) :
    ∀ (UC : List Update), ∀ u ∈ restrictSplits keep UC, Update.NotInsert u
  | [] => by simp [restrictSplits]
  | .split v v' St Sh :: UC => by
    intro u hu
    simp only [restrictSplits, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact trivial
    · exact restrictSplits_notInsert keep UC u hu
  | .insert .. :: UC => restrictSplits_notInsert keep UC
  | .delete _ :: UC => restrictSplits_notInsert keep UC

private theorem insertedEdges_map_insert (t h : ℕ → ℕ) :
    ∀ (l : List ℕ), insertedEdges (l.map fun e => Update.insert e (t e) (h e)) = l
  | [] => rfl
  | e :: l => by simp only [List.map_cons, insertedEdges, insertedEdges_map_insert t h l]

private theorem rotation_cast_order {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ).order = σ.order := by
  subst h; rfl

private theorem outEdits_eq_of_eq {β : ℕ} (src : End → ℕ) (P I W : List Update) (hW : W = P ++ I)
    {G : MGraph} (ρ : Rotation G) (σ : Rotation (G.applyBatch W)) (A : ℕ → List End)
    (h : RotationBatch β W ρ σ) (hval : G.BatchIsValid W)
    (hP : ∀ u ∈ P, Update.NotInsert u) (hI : ∀ u ∈ I, Update.IsInsert u)
    (hnd : (insertedEdges I).Nodup)
    (hsrc : ∀ e ∈ insertedEdges I, (e, true) ∈ σ.order (src (e, true)) ∧
      (e, false) ∈ σ.order (src (e, false)))
    (hA : ∀ v, (A v).IsRotated (ρ.order v)) (T : List ℕ) (hT : ∀ v, σ.order v ≠ [] → v ∈ T) :
    applyOrdEdits A (outPrefixEdits P ++ outInsertEdits σ.order src I ++ outRotateEdits σ.order T) =
      σ.order := by
  subst hW
  exact outEdits_eq src P I ρ σ A h hval hP hI hnd hsrc hA T hT

/-- **The edits of an output step give the new output order.** Under the hypotheses of the step,
the edits `outStepEdits … T` turn the old output order `st.outOrder ord` into the new output order,
when `T` holds every vertex at which the new output order is not empty. -/
theorem stepBundleTree_outStepEdits (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') (T : List ℕ)
    (hT : ∀ v, (stepBundleTree sparsify st U ord ord').state.outOrder ord' v ≠ [] → v ∈ T) :
    applyOrdEdits (st.outOrder ord) (outStepEdits sparsify st U ord ord' T) =
      (stepBundleTree sparsify st U ord ord').state.outOrder ord' := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, hS_val, hS_V, hS_sub, hS_sub'⟩ := hready
  have hout := stepBundleTree_outOrder sparsify st U ord ord' hI hBU ρ σ hρ hσ hrot hS_val hS_V
    hS_sub hS_sub'
  set info := stepBundleTree sparsify st U ord ord' with hinfo
  have hI' := compLSFBatch_inv hI hBU
  have hG_eq := compLSFBatch_G st.cs U
  -- the old and new output orders are the restricted core rotations
  have hold : st.outOrder ord =
      ((coreRotation (L := st.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict hS_sub).order :=
    BundleTreeState.outOrder_eq_restrict st ord hI ρ hρ hS_sub
  have hnew : info.state.outOrder ord' =
      ((coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
        (compLSF_RF_isRSF hI')).restrict hS_sub').order :=
    BundleTreeState.outOrder_eq_restrict info.state ord' hI' (hG_eq.symm ▸ σ)
      ((rotation_cast_order hG_eq.symm σ).trans hσ) hS_sub'
  -- the output batch is valid on the old output graph
  have hBV : st.S_cur.BatchIsValid info.U_S := by
    have hspec := buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hS_sub'.2.1
      info.D_total
    rw [stepBundleTree_U_S_eq]
    exact hspec.1
  set σS := (coreRotation (L := info.state.cs.lsf) (hG_eq.symm ▸ σ) hI'.hG_val
    (compLSF_RF_isRSF hI')).restrict hS_sub' with hσS
  have hcast := outEdits_eq_of_eq (β := 2) info.state.S_cur.src (outPrefixBatch sparsify st U ord ord')
    (outInsBatch sparsify st U ord ord') info.U_S (stepBundleTree_U_S_split sparsify st U ord ord')
    _ σS (st.outOrder ord) hout.2 hBV ?_ ?_ ?_ ?_ (fun v => hold ▸ List.IsRotated.refl _) T
    (fun v hv => hT v (hnew ▸ hv))
  · dsimp only [outStepEdits]
    rw [hnew]
    exact hcast
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
      exact trivial
    · exact restrictSplits_notInsert _ _ u hu
  · intro u hu
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
    exact trivial
  · rw [outInsBatch, insertedEdges_map_insert]
    exact Finset.sort_nodup _ _
  · intro e he
    rw [outInsBatch, insertedEdges_map_insert, outInsList, Finset.mem_sort] at he
    have heE : e ∈ info.state.S_cur.E := (Finset.mem_sdiff.mp he).1
    exact ⟨(σS.mem_order _ _).mpr ⟨heE, rfl⟩, (σS.mem_order _ _).mpr ⟨heE, rfl⟩⟩

/-- The output order is empty at every vertex that is not a root. -/
theorem outOrder_eq_nil_of_not_mem (st : BundleTreeState L) (ord : ℕ → List End) {v : ℕ}
    (hv : v ∉ st.cs.RF.R) : st.outOrder ord v = [] := by
  rw [outOrder_eq_filter]
  unfold outCoreOrder
  split
  · have hv' : v ∉ st.cs.lsf.F.R := hv
    simp only [coreRotation, hv', ↓reduceIte, List.filter_nil]
  · rfl

/-- With `rotateTo` at every new root, the edits of an output step give the new output order. -/
theorem stepBundleTree_outStepEdits_roots (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') :
    applyOrdEdits (st.outOrder ord) (outStepEdits sparsify st U ord ord'
        (((stepBundleTree sparsify st U ord ord').state.cs.RF.R).sort (· ≤ ·))) =
      (stepBundleTree sparsify st U ord ord').state.outOrder ord' :=
  stepBundleTree_outStepEdits sparsify st U ord ord' hready _ fun v hv => by
    rw [Finset.mem_sort]
    by_contra hvR
    exact hv (outOrder_eq_nil_of_not_mem _ ord' hvR)

end MinCostFlow.SparseCore.Program
