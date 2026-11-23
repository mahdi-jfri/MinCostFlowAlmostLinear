module

public import MinCostFlow.SparseCore.Program.AssemblyFirstRotGraph
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotEdits
public import MinCostFlow.SparseCore.Program.AssemblyFirstRotForest
public import MinCostFlow.SparseCore.BundleOutBatchSpec
public import MinCostFlow.Bundle.CoreCongr

/-!
# The list `T₀` of a branch step, and its size

P7's output step applies the edits of the output batch, then a `rotateTo` edit at each vertex of
a list `T₀`. The list must hold every vertex at which the edits before the rotations do not
already give the new output list (`OutRotCover`). The post of the first phase
(`AsmBrCoreStepAt`) asks for such a list, with `|T₀|` paid by the step. This file gives the list
and proves both facts.

**The list.** A vertex `v` is in `T₀` (`asmFirstRotSet`) when
* an edit of the output batch before the rotations names `v`, or the output batch names `v`; or
* `v` is the new root of a vertex that the step touches (`asmFirstTouched`): a vertex that the
  input batch names, an endpoint of a forest edge that the step removes, or a vertex that the
  input edits name.

**Why it covers** (`asmFirstRotSet_cover`). Take `v` outside the list. If `v` is not a new root,
both lists are empty. Otherwise, no vertex of the new tree `C` of `v` is touched. Then the old
tree of `v` is `C` too, with the same edges (`TreeKept`), and `v` is an old root. On `C`, the new
order is the old order without the edges that the input edits drop. So the two tours at `v` agree
on the ends that both keep (`TreeKept.tour_filter_eq`). The edits of the output batch do not name
`v`, so they only drop the leaving output edges there. Last, an output edge at `v` that the
output batch inserts would name `v`. So both lists hold the same ends of the same output edges,
in the same order.

**Its size** (`asmFirstRotSet_card_le`). The edits of the output batch name at most four vertices
per update, the output batch at most two, the input batch at most two, and an input edit at most
two. The forest edges that the step removes are at most the core splits, and the output batch has
every core split. So `|T₀| ≤ 8 Enc(U_S) + 2 |U| + 2 |ed|`.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

private theorem updVerts_subset_batchVerts : ∀ {U : List Update} {u : Update}, u ∈ U →
    updVerts u ⊆ batchVerts U
  | u' :: U, u, hu => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact Finset.subset_union_left
    · exact (updVerts_subset_batchVerts hu).trans Finset.subset_union_right

private theorem filter_filter_of_imp {l : List End} {p r : End → Bool}
    (h : ∀ x ∈ l, r x = true → p x = true) : (l.filter p).filter r = l.filter r := by
  rw [List.filter_filter]
  refine List.filter_congr fun x hx => ?_
  cases hr : r x
  · simp
  · simp [h x hx hr]

private theorem filter_eq_filter_filter {l : List End} {r q s : End → Bool}
    (h : ∀ x ∈ l, r x = true ↔ (q x = true ∧ s x = true)) : l.filter r = (l.filter q).filter s := by
  rw [List.filter_filter]
  refine List.filter_congr fun x hx => ?_
  have := h x hx
  cases hr : r x <;> cases hq : q x <;> cases hs : s x <;> simp_all

/-- The output list at an old root is the tour of its tree, restricted to the output edges. -/
theorem outOrder_eq_tour_filter {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (st : BundleTreeState L)
    (ord : ℕ → List End) (hI : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G)
    (hρ : ρ.order = ord) {v : ℕ} (hv : v ∈ st.cs.RF.R) :
    st.outOrder ord v =
      (tour ρ (compLSF_RF_isRSF hI).1 v).filter fun x => decide (x.1 ∈ st.S_cur.E) := by
  classical
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ st.cs) (ρ' : Rotation st.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold BundleTreeState.outOrder
  rw [dite_eq_left hex]
  have hρ_eq : hex.choose_spec.choose_spec.choose_spec.choose = ρ :=
    Rotation.ext_order (hex.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm)
  change (((coreRotation (L := st.cs.lsf) hex.choose_spec.choose_spec.choose_spec.choose
      hex.choose_spec.choose_spec.choose.hG_val
      (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).order v).filter
      fun x => decide (x.1 ∈ st.S_cur.E)) = _
  rw [hρ_eq]
  change (if v ∈ st.cs.RF.R then _ else []).filter _ = _
  simp only [hv, ↓reduceIte]
  rfl

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The endpoints, in the old graph, of the forest edges that a batch removes. -/
@[expose] noncomputable def cutVerts (cs : CompLSFState) (U : List Update) : Finset ℕ :=
  (cs.RF.F.E \ (compLSFBatch cs U).RF.F.E).biUnion fun e => {cs.G.tail e, cs.G.head e}

/-- The vertices that a step touches: those that the input batch names, the endpoints of the
forest edges that it removes, and those that the input edits name. -/
@[expose] noncomputable def asmFirstTouched (cs : CompLSFState) (U : List Update) (ed : List OrdEdit) :
    Finset ℕ :=
  batchVerts U ∪ cutVerts cs U ∪ ordEditVerts ed

/-- **The vertices of `T₀`**: those that the edits of the output batch before the rotations name,
those that the output batch names, and the new roots of the vertices that the step touches. -/
@[expose] noncomputable def asmFirstRotSet (st : BundleTreeState L) (U : List Update) (ord : ℕ → List End)
    (ed : List OrdEdit) : Finset ℕ :=
  ordEditVerts (outBaseEdits sparsify st U ord (applyOrdEdits ord ed)) ∪
    batchVerts (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S ∪
    (asmFirstTouched st.cs U ed).image (compLSFBatch st.cs U).RF.root

/-- **`T₀` covers the step.** Under the invariant of the LSF, for a valid batch, and for
rotations with the old and the new orders, every list that holds `asmFirstRotSet` meets
`OutRotCover`. -/
theorem asmFirstRotSet_cover {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (st : BundleTreeState L)
    (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (hI : CompLSFInv C_lsst ℓ₀ st.cs) (hU : st.cs.G.BatchIsValid U)
    (ρ : Rotation st.cs.G) (hρ : ρ.order = ord)
    (σ : Rotation (compLSFBatch st.cs U).G) (hσ : σ.order = applyOrdEdits ord ed)
    (T₀ : List ℕ) (hT : ∀ v ∈ asmFirstRotSet sparsify st U ord ed, v ∈ T₀) :
    OutRotCover sparsify st U ord (applyOrdEdits ord ed) T₀ := by
  intro v hvT
  have hv : v ∉ asmFirstRotSet sparsify st U ord ed := fun h => hvT (hT v h)
  simp only [asmFirstRotSet, Finset.mem_union, Finset.mem_image, not_or, not_exists,
    not_and] at hv
  obtain ⟨⟨hv₁, hv₂⟩, hv₃⟩ := hv
  have hI' : CompLSFInv C_lsst ℓ₀ (compLSFBatch st.cs U) := compLSFBatch_inv hI hU
  have hRF := compLSF_RF_isRSF hI
  have hRF' := compLSF_RF_isRSF hI'
  obtain ⟨hFE, hRR⟩ := compLSFBatch_decremental hI hU
  have hG' : (compLSFBatch st.cs U).G = st.cs.G.applyBatch U := compLSFBatch_G st.cs U
  rw [outBaseOrder_of_not_mem sparsify st U ord _ hv₁]
  by_cases hvR' : v ∈ (compLSFBatch st.cs U).RF.R
  swap
  · -- `v` is not a new root, so not an old root, and both lists are empty
    have hvR : v ∉ st.cs.RF.R := fun h => hvR' (hRR h)
    rw [outOrder_eq_nil_of_not_mem st ord hvR, outOrder_eq_nil_of_not_mem
      (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state (applyOrdEdits ord ed)
      (show v ∉ (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state.cs.RF.R from hvR')]
    rfl
  -- the new tree of `v`: its vertices have the new root `v`, and none of them is touched
  have hvV' : v ∈ (compLSFBatch st.cs U).G.V := hRF'.2.2.1 hvR'
  have hCV : ∀ w, (compLSFBatch st.cs U).RF.F.Connected v w → w ∈ (compLSFBatch st.cs U).G.V := by
    rintro w ⟨P, hP⟩
    have h := (IsWalk_vertices_mem hRF'.1.1 (hRF'.2.1 ▸ hvV') hP).1
    rwa [hRF'.2.1] at h
  have hCroot : ∀ w, (compLSFBatch st.cs U).RF.F.Connected v w →
      (compLSFBatch st.cs U).RF.root w = v := fun w hw =>
    rootedForest_root_eq_of_mem hRF' (hCV w hw) hvR' (connected_symm hw)
  have hCt : ∀ w, (compLSFBatch st.cs U).RF.F.Connected v w → w ∉ asmFirstTouched st.cs U ed :=
    fun w hw ht => hv₃ w ht (hCroot w hw)
  -- so the step keeps the tree of `v`
  have hK : TreeKept st.cs.G (compLSFBatch st.cs U).G st.cs.RF.F (compLSFBatch st.cs U).RF.F
      (batchVerts U) v := by
    refine ⟨hRF.2.2.2.2, hRF'.2.2.2.2, hFE, fun x hx => ?_, fun w hw hB => ?_, fun x hx hc => ?_⟩
    · -- a final forest edge is not deleted, so the batch moves its ends only at named vertices
      have hxG : x.1 ∈ st.cs.G.E := hRF.2.2.2.2.2.1 (hFE hx)
      have hm := (applyBatch_src_moves st.cs.G U hU x hxG
        (compLSFBatch_RF_E_not_deleted U hI hU x.1 hx)).2
      rwa [← hG'] at hm
    · exact hCt w hw (by simp [asmFirstTouched, hB])
    · -- an old forest edge that starts in the tree and is removed would touch the tree
      by_contra hx'
      apply hCt _ hc
      have hcut : st.cs.G.src x ∈ cutVerts st.cs U := by
        refine Finset.mem_biUnion.mpr ⟨x.1, Finset.mem_sdiff.mpr ⟨hx, hx'⟩, ?_⟩
        obtain ⟨e, b⟩ := x
        cases b <;> simp [MGraph.src]
      simp [asmFirstTouched, hcut]
  -- `v` is an old root: the old root of its tree is in the new tree, and is a new root
  have hvB : v ∉ batchVerts U := hK.named v (connected_refl _ _)
  have hvV : v ∈ st.cs.G.V := by
    rcases Finset.mem_union.mp (applyBatch_V_subset st.cs.G U (hG' ▸ hvV')) with h | h
    · exact h
    · exact absurd h hvB
  have hvR : v ∈ st.cs.RF.R := by
    obtain ⟨hrR, hrC⟩ := root_mem_R hRF hvV
    have h₁ := rootedForest_root_eq_of_mem hRF' hvV' (hRR hrR) (hK.connected hrC)
    have h₂ := rootedForest_root_self hRF' hvR'
    exact (h₁.symm.trans h₂) ▸ hrR
  -- on the tree, the new order is the old order without the edges that the input edits drop
  have hord : ∀ w, (compLSFBatch st.cs U).RF.F.Connected v w →
      σ.order w = (ρ.order w).filter fun x => decide (x.1 ∉ ordEditDrops ed) := by
    intro w hw
    have hwe : w ∉ ordEditVerts ed := fun h => hCt w hw (by simp [asmFirstTouched, h])
    rw [hσ, applyOrdEdits_of_not_mem _ _ hwe, hρ]
  -- the filter of the ends that both tours keep
  let q : End → Bool := fun x => decide (x.1 ∉ ordEditDrops ed) &&
    decide (x.1 ∈ st.cs.RF.F.E ↔ x.1 ∈ (compLSFBatch st.cs U).RF.F.E)
  have hqf : ∀ w, (compLSFBatch st.cs U).RF.F.Connected v w →
      (ρ.order w).filter q = (σ.order w).filter q := by
    intro w hw
    rw [hord w hw, List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    by_cases hd : x.1 ∈ ordEditDrops ed <;> simp [q, hd]
  have htour := hK.tour_filter_eq ρ σ hRF.1 hRF'.1 hRF.2.1 hRF'.2.1 q
    (fun x hx => by
      simp only [q, Bool.and_eq_true, decide_eq_true_eq] at hx
      exact hx.2)
    (fun x hx hc => by
      have hxσ : x ∈ σ.order ((compLSFBatch st.cs U).G.src x) :=
        (σ.mem_order _ _).mpr ⟨hRF'.2.2.2.2.2.1 hx, rfl⟩
      rw [hord _ hc, List.mem_filter] at hxσ
      simp only [q, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨of_decide_eq_true hxσ.2, iff_of_true (hFE hx) hx⟩)
    (fun w hw => by rw [hqf w hw])
    (hqf v (connected_refl _ _))
  -- every end of the new tour passes `q`
  have hP₂ : ∀ x ∈ tour σ hRF'.1 v, q x = true := by
    intro x hx
    obtain ⟨hxE, hxF, hxc⟩ := ((tour_spec σ hI'.hG_val hRF'.1 hRF'.2.2.2.2 hRF'.2.1 v).2 x).mp hx
    have hxσ : x ∈ σ.order ((compLSFBatch st.cs U).G.src x) := (σ.mem_order _ _).mpr ⟨hxE, rfl⟩
    rw [hord _ hxc, List.mem_filter] at hxσ
    have hxρ := (ρ.mem_order _ _).mp hxσ.1
    have hxc' : (compLSFBatch st.cs U).RF.F.Connected v (st.cs.G.src x) := by
      rw [hxρ.2]
      exact hxc
    have hxF₀ : x.1 ∉ st.cs.RF.F.E := fun h => hxF (hK.cut x h hxc')
    simp only [q, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨of_decide_eq_true hxσ.2, iff_of_false hxF₀ hxF⟩
  -- the output edges that stay
  have hkeep : ∀ e, e ∈ outKeep sparsify st U ord (applyOrdEdits ord ed) →
      e ∈ st.S_cur.E ∧ e ∈ (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state.S_cur.E ∧
        e ∉ batchDeletes U := by
    intro e he
    simp only [outKeep, Finset.mem_sdiff, Finset.mem_inter] at he
    exact ⟨he.1.1.1, he.1.1.2, he.1.2⟩
  -- an end of the old tour is in an output edge that stays exactly when it passes `q` and is in
  -- a new output edge
  have hP₁ : ∀ x ∈ tour ρ hRF.1 v,
      decide (x.1 ∈ outKeep sparsify st U ord (applyOrdEdits ord ed)) = true ↔
        (q x = true ∧ decide (x.1 ∈
          (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state.S_cur.E) = true) := by
    intro x hx
    obtain ⟨hxE, hxF, hxc⟩ := ((tour_spec ρ hI.hG_val hRF.1 hRF.2.2.2.2 hRF.2.1 v).2 x).mp hx
    have hwc := hK.connected hxc
    have hxρ : x ∈ ρ.order (st.cs.G.src x) := (ρ.mem_order _ _).mpr ⟨hxE, rfl⟩
    simp only [decide_eq_true_eq]
    by_cases hd : x.1 ∈ ordEditDrops ed
    · -- the input edits drop the edge, so it is deleted, and it does not stay
      have hq : q x = false := by simp [q, hd]
      rw [hq]
      simp only [Bool.false_eq_true, false_and, iff_false]
      intro hk
      have hnd := (hkeep _ hk).2.2
      have hm := applyBatch_src_moves st.cs.G U hU x hxE
        (fun u hu heq => hnd ((mem_batchDeletes_iff U x.1).mpr ⟨u, hu, heq⟩))
      rw [← hG'] at hm
      have hs : (compLSFBatch st.cs U).G.src x = st.cs.G.src x :=
        hm.2.resolve_right fun hb => hK.named _ hwc hb.1
      have hxσ : x ∈ σ.order (st.cs.G.src x) := (σ.mem_order _ _).mpr ⟨hm.1, hs⟩
      rw [hord _ hwc, List.mem_filter] at hxσ
      exact of_decide_eq_true hxσ.2 hd
    · -- the end stays at the same vertex of the tree
      have hxσ : x ∈ σ.order (st.cs.G.src x) := by
        rw [hord _ hwc, List.mem_filter]
        exact ⟨hxρ, decide_eq_true hd⟩
      obtain ⟨-, hs⟩ := (σ.mem_order _ _).mp hxσ
      have hq : q x = true := by
        simp only [q, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hd, iff_of_false hxF fun h => hxF (hFE h)⟩
      rw [hq]
      simp only [true_and]
      refine ⟨fun hk => (hkeep _ hk).2.1, fun hS' => ?_⟩
      by_contra hk
      -- an entering output edge: the output batch inserts it at the new root `v`
      have hins : x.1 ∈ outInsList sparsify st U ord (applyOrdEdits ord ed) :=
        (Finset.mem_sort _).mpr (Finset.mem_sdiff.mpr ⟨hS', hk⟩)
      have hu : Update.insert x.1
          ((compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.tail x.1))
          ((compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.head x.1)) ∈
          (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S := by
        rw [stepBundleTree_U_S_split]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨x.1, hins, rfl⟩)
      have hroot : (compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.src x) = v :=
        hCroot _ (hs ▸ hwc)
      have hmem : (compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.src x) ∈
          updVerts (Update.insert x.1
            ((compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.tail x.1))
            ((compLSFBatch st.cs U).RF.root ((compLSFBatch st.cs U).G.head x.1))) := by
        obtain ⟨e, b⟩ := x
        cases b <;> simp [updVerts, MGraph.src]
      rw [hroot] at hmem
      exact hv₂ (updVerts_subset_batchVerts hu hmem)
  -- the two lists
  have hold := outOrder_eq_tour_filter st ord hI ρ hρ hvR
  have hnew : (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state.outOrder
      (applyOrdEdits ord ed) v = (tour σ hRF'.1 v).filter fun x => decide
        (x.1 ∈ (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state.S_cur.E) :=
    outOrder_eq_tour_filter (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).state
      (applyOrdEdits ord ed) hI' σ hσ hvR'
  rw [hold, hnew, filter_filter_of_imp fun x _ hk =>
      decide_eq_true (hkeep _ (of_decide_eq_true hk)).1,
    filter_eq_filter_filter hP₁, htour, List.filter_eq_self.mpr hP₂]

/-- The forest edges that a step removes are at most the updates of its output batch, since the
output batch has every split of the canonical core batch. -/
theorem card_RF_E_sdiff_le_U_S (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) :
    (st.cs.RF.F.E \ (compLSFBatch st.cs U).RF.F.E).card ≤
      (stepBundleTree sparsify st U ord ord').U_S.length := by
  refine (card_RF_E_sdiff_le_canon U st.cs).trans ?_
  have hUC : (stepBundleTree sparsify st U ord ord').U_core = canonCoreBatch st.cs U := by
    rw [← coreBatchOf_eq st.cs ord ord' U]
    rfl
  rw [← restrictSplits_length (outKeep sparsify st U ord ord'), stepBundleTree_U_S_split,
    outPrefixBatch, hUC]
  simp only [List.length_append]
  omega

/-- **The size of `T₀`.** At most `8 Enc(U_S) + 2 |U| + 2 |ed|`. -/
theorem asmFirstRotSet_card_le (st : BundleTreeState L) (U : List Update) (ord : ℕ → List End)
    (ed : List OrdEdit) :
    (asmFirstRotSet sparsify st U ord ed).card ≤
      8 * st.S_cur.batchEnc (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S +
        2 * U.length + 2 * ed.length := by
  have h₁ := ordEditVerts_outBaseEdits_card_le sparsify st U ord (applyOrdEdits ord ed)
  have h₂ := batchVerts_card_le (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S
  have h₃ := batchVerts_card_le U
  have h₄ := ordEditVerts_card_le ed
  have h₅ := card_RF_E_sdiff_le_U_S sparsify st U ord (applyOrdEdits ord ed)
  have h₆ := length_le_batchEnc st.S_cur (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S
  have hcut : (cutVerts st.cs U).card ≤ (st.cs.RF.F.E \ (compLSFBatch st.cs U).RF.F.E).card * 2 :=
    Finset.card_biUnion_le_card_mul _ _ _ fun e _ => (Finset.card_insert_le _ _).trans (by simp)
  have hT : (asmFirstTouched st.cs U ed).card ≤
      (batchVerts U).card + (cutVerts st.cs U).card + (ordEditVerts ed).card := by
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_union_le (batchVerts U) (cutVerts st.cs U)
    omega
  have hI := Finset.card_image_le (s := asmFirstTouched st.cs U ed)
    (f := (compLSFBatch st.cs U).RF.root)
  have hS := Finset.card_union_le
    (ordEditVerts (outBaseEdits sparsify st U ord (applyOrdEdits ord ed)))
    (batchVerts (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S)
  unfold asmFirstRotSet
  refine (Finset.card_union_le _ _).trans ?_
  omega

/-- **The size of `T₀` in the words of the input.** The records of the batch and of the edits
take at least two words per update and per edit (`BatchBodyAt`, `EditsBody.length_le`). So
`|T₀| ≤ 8 (Enc(U_S) + words + editWords + 1)`, the form of the bound in `AsmBrCoreStepAt`. -/
theorem asmFirstRotSet_card_le_words (st : BundleTreeState L) (U : List Update)
    (ord : ℕ → List End) (ed : List OrdEdit) {words editWords : ℕ}
    (hU : 2 * U.length ≤ words) (hed : 2 * ed.length ≤ editWords) :
    (asmFirstRotSet sparsify st U ord ed).card ≤
      8 * (st.S_cur.batchEnc (stepBundleTree sparsify st U ord (applyOrdEdits ord ed)).U_S +
        words + editWords + 1) := by
  have h := asmFirstRotSet_card_le sparsify st U ord ed
  omega

end MinCostFlow.SparseCore.Program
