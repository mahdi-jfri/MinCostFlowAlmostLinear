module

public import MinCostFlow.SparseCore.Program.OutStepSpec
public import MinCostFlow.SparseCore.Program.OutEditsSmall
import MinCostFlow.SparseCore.BundleOutBatchSpec

/-!
# The order edits that the output step writes

The output step writes, for each update of its batch `U_S`, the edits of the output order: a
`dropEdge` per leaving edge, a `moveEnds` of the smaller side per split (`outSplitEdit`), two
`insertBefore` per entering edge, and then `rotateTo` at the vertices of a list `T₀`
(`outStepEditsSmall`). This file proves what the step needs about them.

* `stepBundleTree_outStepEditsSmall`: when `T₀` covers every vertex at which the edits without
  `rotateTo` do not give the new list (`OutRotCover`), the edits turn the old output order into
  the new one. The deletions and splits move the same ends as the edits `outPrefixEdits`
  (`applyOrdEdits_outPrefixEditsOn`), and the rest is `stepBundleTree_outStepEdits`'s argument.
* `ordEditsEnc_outStepEditsSmall_le`: their encoding size is at most twice the encoding size of
  `U_S` plus the length of `T₀`.
* `outRotCover_of_untouched`: a vertex that the batch does not name
  (`OutTouched`) and whose core list did not change keeps its output list exactly. So `T₀` can be
  the vertices that the batch names together with the roots whose core list changed. The edits do
  not touch the list of such a vertex, and its new output list has the same ends, since an end
  that enters or leaves the output graph at that vertex is named by an insertion or a deletion.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

variable {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- The edits of an output step with the splits written by their smaller sides, and `rotateTo` at
the vertices of `T₀`. -/
noncomputable def outStepEditsSmall (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (T₀ : List ℕ) : List OrdEdit :=
  let st' := (stepBundleTree sparsify st U ord ord').state
  outPrefixEditsOn st.S_cur (outPrefixBatch sparsify st U ord ord') ++
    outInsertEdits (st'.outOrder ord') st'.S_cur.src (outInsBatch sparsify st U ord ord') ++
    outRotateEdits (st'.outOrder ord') T₀

/-! ## Small facts -/

theorem applyOrdEdits_append' (A : ℕ → List End) (ds ds' : List OrdEdit) :
    applyOrdEdits A (ds ++ ds') = applyOrdEdits (applyOrdEdits A ds) ds' := by
  simp [applyOrdEdits, List.foldl_append]

theorem ordEditsEnc_append (ds ds' : List OrdEdit) :
    ordEditsEnc (ds ++ ds') = ordEditsEnc ds + ordEditsEnc ds' := by
  simp [ordEditsEnc]

theorem notInsert_prefix (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) : ∀ u ∈ outPrefixBatch sparsify st U ord ord', Update.NotInsert u := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
    exact trivial
  · revert hu
    generalize (stepBundleTree sparsify st U ord ord').U_core = UC
    induction UC with
    | nil => simp [restrictSplits]
    | cons u' UC ih =>
      intro hu
      cases u' with
      | split v v' St Sh =>
        simp only [restrictSplits, List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact trivial
        · exact ih hu
      | insert e a b => exact ih hu
      | delete e => exact ih hu

theorem insertedEdges_map_insert' (t h : ℕ → ℕ) :
    ∀ (l : List ℕ), insertedEdges (l.map fun e => Update.insert e (t e) (h e)) = l
  | [] => rfl
  | e :: l => by simp only [List.map_cons, insertedEdges, insertedEdges_map_insert' t h l]

/-- The ends of `outCoreOrder` at `v` are ends of the core graph at `v`. -/
theorem mem_outCoreOrder {st : BundleTreeState L} {ord : ℕ → List End}
    (h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ st.cs) (ρ : Rotation st.cs.G),
      ρ.order = ord) {v : ℕ} {x : End} (hx : x ∈ outCoreOrder st ord v) :
    x.1 ∈ (coreGraph st.cs.G st.cs.lsf).E ∧ (coreGraph st.cs.G st.cs.lsf).src x = v := by
  unfold outCoreOrder at hx
  rw [dite_eq_left_of_eq_true (eq_true h)] at hx
  exact (Rotation.mem_order _ v x).mp hx

/-! ## The model facts of a step -/

/-- The rotations of the old and new output graphs whose orders are the output orders, and the
ordered batch `U_S` between them. -/
theorem outStep_rotations (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') :
    ∃ (ρS : Rotation st.S_cur) (σS : Rotation (stepBundleTree sparsify st U ord ord').state.S_cur),
      ρS.order = st.outOrder ord ∧
      σS.order = (stepBundleTree sparsify st U ord ord').state.outOrder ord' ∧
      RotationBatch 2 (stepBundleTree sparsify st U ord ord').U_S ρS σS ∧
      st.S_cur.BatchIsValid (stepBundleTree sparsify st U ord ord').U_S := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, hS_val, hS_V, hS_sub, hS_sub'⟩ := hready
  have hout := stepBundleTree_outOrder sparsify st U ord ord' hI hBU ρ σ hρ hσ hrot hS_val hS_V
    hS_sub hS_sub'
  set info := stepBundleTree sparsify st U ord ord' with hinfo
  have hI' := compLSFBatch_inv hI hBU
  have hG_eq := compLSFBatch_G st.cs U
  have hcast : (hG_eq.symm ▸ σ : Rotation (compLSFBatch st.cs U).G).order = ord' := by
    have : ∀ {G H : MGraph} (h : G = H) (σ : Rotation G), (h ▸ σ).order = σ.order := by
      intro G H h σ; subst h; rfl
    exact (this hG_eq.symm σ).trans hσ
  refine ⟨_, _, (BundleTreeState.outOrder_eq_restrict st ord hI ρ hρ hS_sub).symm,
    (BundleTreeState.outOrder_eq_restrict info.state ord' hI' (hG_eq.symm ▸ σ) hcast hS_sub').symm,
    hout.2, ?_⟩
  have hspec := buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hS_sub'.2.1 info.D_total
  rw [stepBundleTree_U_S_eq]
  exact hspec.1

/-- The output order holds exactly the ends of the output graph at their vertices. -/
theorem ordMemOf_outOrder (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') :
    OrdMemOf (st.outOrder ord) st.S_cur ∧
      OrdMemOf ((stepBundleTree sparsify st U ord ord').state.outOrder ord')
        (stepBundleTree sparsify st U ord ord').state.S_cur := by
  obtain ⟨ρS, σS, hρ, hσ, -, -⟩ := outStep_rotations sparsify st U ord ord' hready
  exact ⟨fun v x => hρ ▸ ρS.mem_order v x, fun v x => hσ ▸ σS.mem_order v x⟩

/-- The edits of the deletions, splits and insertions, without `rotateTo`, make each list a
rotation of the new list. -/
private theorem base_isRotated_of_eq (S : MGraph) (ρS : Rotation S) (src : End → ℕ)
    (W P I : List Update) (hW : W = P ++ I) (σ : Rotation (S.applyBatch W)) (A : ℕ → List End)
    (hA : ρS.order = A) (hrot : RotationBatch 2 W ρS σ) (hBV : S.BatchIsValid W)
    (hP : ∀ u ∈ P, Update.NotInsert u) (hI : ∀ u ∈ I, Update.IsInsert u)
    (hnd : (insertedEdges I).Nodup)
    (hsrc : ∀ e ∈ insertedEdges I, (e, true) ∈ σ.order (src (e, true)) ∧
      (e, false) ∈ σ.order (src (e, false))) (v : ℕ) :
    (applyOrdEdits A (outPrefixEdits P ++ outInsertEdits σ.order src I) v).IsRotated
      (σ.order v) := by
  subst hW
  exact outBaseEdits_isRotated src P I ρS σ A hrot hBV hP hI hnd hsrc
    (fun w => hA ▸ List.IsRotated.refl _) v

theorem outBaseOrder_isRotated (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify st U ord ord') (v : ℕ) :
    (outBaseOrder sparsify st U ord ord' v).IsRotated
      ((stepBundleTree sparsify st U ord ord').state.outOrder ord' v) := by
  obtain ⟨ρS, σS, hρ, hσ, hrot, hBV⟩ := outStep_rotations sparsify st U ord ord' hready
  have h := base_isRotated_of_eq st.S_cur ρS
    (stepBundleTree sparsify st U ord ord').state.S_cur.src (stepBundleTree sparsify st U ord ord').U_S
    (outPrefixBatch sparsify st U ord ord') (outInsBatch sparsify st U ord ord')
    (stepBundleTree_U_S_split sparsify st U ord ord') σS (st.outOrder ord) hρ hrot hBV
    (notInsert_prefix sparsify st U ord ord') ?_ ?_ ?_ v
  · unfold outBaseOrder
    rw [hσ] at h
    exact h
  · intro u hu
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hu
    exact trivial
  · rw [outInsBatch, insertedEdges_map_insert']
    exact Finset.sort_nodup _ _
  · intro e he
    rw [outInsBatch, insertedEdges_map_insert', outInsList, Finset.mem_sort] at he
    have heE := (Finset.mem_sdiff.mp he).1
    exact ⟨(σS.mem_order _ _).mpr ⟨heE, rfl⟩, (σS.mem_order _ _).mpr ⟨heE, rfl⟩⟩

/-! ## The edits give the new order -/

/-- The deletions, splits and insertions written by the smaller sides give `outBaseOrder`. -/
theorem applyOrdEdits_small_base (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') :
    let st' := (stepBundleTree sparsify st U ord ord').state
    applyOrdEdits (st.outOrder ord)
        (outPrefixEditsOn st.S_cur (outPrefixBatch sparsify st U ord ord') ++
          outInsertEdits (st'.outOrder ord') st'.S_cur.src (outInsBatch sparsify st U ord ord')) =
      outBaseOrder sparsify st U ord ord' := by
  intro st'
  have hmem := (ordMemOf_outOrder sparsify st U ord ord' hready).1
  obtain ⟨-, -, -, -, -, hBV⟩ := outStep_rotations sparsify st U ord ord' hready
  obtain ⟨-, -, -, -, -, hS_val, -⟩ := hready
  rw [stepBundleTree_U_S_split, batchIsValid_append] at hBV
  unfold outBaseOrder
  rw [applyOrdEdits_append', applyOrdEdits_append',
    applyOrdEdits_outPrefixEditsOn _ st.S_cur _ hmem hS_val hBV.1
      (notInsert_prefix sparsify st U ord ord')]

/-- **The edits of an output step give the new output order** when `T₀` covers the vertices at
which the edits without `rotateTo` do not give the new list. -/
theorem stepBundleTree_outStepEditsSmall (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') (T₀ : List ℕ)
    (hcov : OutRotCover sparsify st U ord ord' T₀) :
    applyOrdEdits (st.outOrder ord) (outStepEditsSmall sparsify st U ord ord' T₀) =
      (stepBundleTree sparsify st U ord ord').state.outOrder ord' := by
  have hbase := applyOrdEdits_small_base sparsify st U ord ord' hready
  obtain ⟨-, σS, -, hσ, -, -⟩ := outStep_rotations sparsify st U ord ord' hready
  have hnd : ∀ v, ((stepBundleTree sparsify st U ord ord').state.outOrder ord' v).Nodup :=
    fun v => hσ ▸ σS.nodup v
  unfold outStepEditsSmall
  rw [applyOrdEdits_append', hbase]
  funext v
  rw [outRotateEdits_apply hnd T₀ _ (outBaseOrder_isRotated sparsify st U ord ord' hready) v]
  split
  · rfl
  · exact hcov v (by assumption)

/-! ## The encoding size -/

private theorem ordEditsEnc_outInsertEdits_le (t : ℕ → List End) (src : End → ℕ) :
    ∀ I : List Update, ordEditsEnc (outInsertEdits t src I) ≤ 2 * I.length
  | [] => by simp [outInsertEdits, ordEditsEnc]
  | .insert e a b :: I => by
    have h := ordEditsEnc_outInsertEdits_le t src I
    simp only [outInsertEdits, ordEditsEnc, List.map_cons, List.sum_cons, OrdEdit.enc,
      List.length_cons] at h ⊢
    omega
  | .delete _ :: I => by
    have h := ordEditsEnc_outInsertEdits_le t src I
    simp only [outInsertEdits, List.length_cons]; omega
  | .split .. :: I => by
    have h := ordEditsEnc_outInsertEdits_le t src I
    simp only [outInsertEdits, List.length_cons]; omega

private theorem ordEditsEnc_outRotateEdits_le (t : ℕ → List End) :
    ∀ T : List ℕ, ordEditsEnc (outRotateEdits t T) ≤ T.length
  | [] => by simp [outRotateEdits, ordEditsEnc]
  | v :: T => by
    have h := ordEditsEnc_outRotateEdits_le t T
    simp only [outRotateEdits, ordEditsEnc_append, List.length_cons]
    split
    · simp only [ordEditsEnc, List.map_nil, List.sum_nil] at h ⊢; omega
    · simp only [ordEditsEnc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        OrdEdit.enc] at h ⊢; omega

private theorem length_le_batchEnc : ∀ (G : MGraph) (I : List Update), I.length ≤ G.batchEnc I
  | _, [] => le_refl _
  | G, u :: I => by
    have h := length_le_batchEnc (G.applyUpdate u) I
    have hu : 1 ≤ G.updateEnc u := by
      cases u <;> simp [MGraph.updateEnc]
    simp only [List.length_cons, MGraph.batchEnc]
    omega

private theorem batchEnc_append' :
    ∀ (U₁ U₂ : List Update) (G : MGraph),
      G.batchEnc (U₁ ++ U₂) = G.batchEnc U₁ + (G.applyBatch U₁).batchEnc U₂
  | [], _, _ => by simp [MGraph.batchEnc, MGraph.applyBatch]
  | u :: U₁, U₂, G => by
    have ih := batchEnc_append' U₁ U₂ (G.applyUpdate u)
    have hstep : G.applyBatch (u :: U₁) = (G.applyUpdate u).applyBatch U₁ := rfl
    simp only [List.cons_append, MGraph.batchEnc]
    rw [ih, hstep, Nat.add_assoc]

/-- **The encoding size of the edits** is at most twice the encoding size of `U_S` plus the
length of `T₀`. -/
theorem ordEditsEnc_outStepEditsSmall_le (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') (T₀ : List ℕ) :
    ordEditsEnc (outStepEditsSmall sparsify st U ord ord' T₀) ≤
      2 * st.S_cur.batchEnc (stepBundleTree sparsify st U ord ord').U_S + T₀.length := by
  obtain ⟨-, -, -, -, -, hBV⟩ := outStep_rotations sparsify st U ord ord' hready
  obtain ⟨-, -, -, -, -, hS_val, -⟩ := hready
  rw [stepBundleTree_U_S_split, batchIsValid_append] at hBV
  have h1 := ordEditsEnc_outPrefixEditsOn_le _ _ hS_val hBV.1
  have h2 := ordEditsEnc_outInsertEdits_le
    ((stepBundleTree sparsify st U ord ord').state.outOrder ord')
    (stepBundleTree sparsify st U ord ord').state.S_cur.src (outInsBatch sparsify st U ord ord')
  have h3 := ordEditsEnc_outRotateEdits_le
    ((stepBundleTree sparsify st U ord ord').state.outOrder ord') T₀
  have h4 := length_le_batchEnc (st.S_cur.applyBatch (outPrefixBatch sparsify st U ord ord'))
    (outInsBatch sparsify st U ord ord')
  unfold outStepEditsSmall
  rw [stepBundleTree_U_S_split, batchEnc_append', ordEditsEnc_append, ordEditsEnc_append]
  omega

/-! ## The vertices that keep their lists -/

/-- The vertices that the output batch names: both ends of each leaving edge in the old output
graph, both vertices of each split, and both ends of each entering edge in the new output graph. -/
def OutTouched (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (v : ℕ) :
    Prop :=
  (∃ e ∈ outDelList sparsify st U ord ord', st.S_cur.tail e = v ∨ st.S_cur.head e = v) ∨
  (∃ v₁ v₂ St Sh, Update.split v₁ v₂ St Sh ∈
      restrictSplits (outKeep sparsify st U ord ord') (stepBundleTree sparsify st U ord ord').U_core ∧
      (v = v₁ ∨ v = v₂)) ∨
  (∃ e ∈ outInsList sparsify st U ord ord',
    (stepBundleTree sparsify st U ord ord').state.S_cur.tail e = v ∨
      (stepBundleTree sparsify st U ord ord').state.S_cur.head e = v)

/-- The edits `outPrefixEdits` of the deletions and splits keep the list at a vertex `v` that no split
names and that holds no end of a deleted edge. -/
theorem applyOrdEdits_outPrefixEdits_of_not_named (v : ℕ) :
    ∀ (Q : List Update) (A : ℕ → List End),
      (∀ v₁ v₂ St Sh, Update.split v₁ v₂ St Sh ∈ Q → v ≠ v₁ ∧ v ≠ v₂) →
      (∀ e, Update.delete e ∈ Q → ∀ x ∈ A v, x.1 ≠ e) →
      applyOrdEdits A (outPrefixEdits Q) v = A v
  | [], _, _, _ => rfl
  | .delete e :: Q, A, hs, hd => by
    have hAv : applyOrdEdit A (.dropEdge e) v = A v := by
      simp only [applyOrdEdit]
      apply List.filter_eq_self.mpr
      intro x hx
      simpa using hd e List.mem_cons_self x hx
    show applyOrdEdits (applyOrdEdit A (.dropEdge e)) (outPrefixEdits Q) v = A v
    rw [applyOrdEdits_outPrefixEdits_of_not_named v Q _
      (fun v₁ v₂ St Sh h => hs v₁ v₂ St Sh (List.mem_cons_of_mem _ h))
      (fun e' he' x hx => hd e' (List.mem_cons_of_mem _ he') x (hAv ▸ hx)), hAv]
  | .split v₁ v₂ St Sh :: Q, A, hs, hd => by
    obtain ⟨h1, h2⟩ := hs v₁ v₂ St Sh List.mem_cons_self
    have hAv : applyOrdEdit A (.moveEnds v₁ v₂ (splitSel St Sh) false) v = A v := by
      simp [applyOrdEdit, h1, h2]
    show applyOrdEdits (applyOrdEdit A (.moveEnds v₁ v₂ (splitSel St Sh) false))
      (outPrefixEdits Q) v = A v
    rw [applyOrdEdits_outPrefixEdits_of_not_named v Q _
      (fun v₁ v₂ St Sh h => hs v₁ v₂ St Sh (List.mem_cons_of_mem _ h))
      (fun e' he' x hx => hd e' (List.mem_cons_of_mem _ he') x (hAv ▸ hx)), hAv]
  | .insert e a b :: Q, A, hs, hd => by
    simp only [outPrefixEdits]
    exact applyOrdEdits_outPrefixEdits_of_not_named v Q A
      (fun v₁ v₂ St Sh h => hs v₁ v₂ St Sh (List.mem_cons_of_mem _ h))
      (fun e' he' => hd e' (List.mem_cons_of_mem _ he'))

/-- The insertion edits keep the list at a vertex that is not the vertex of an inserted end. -/
theorem applyOrdEdits_outInsertEdits_of_ne (t : ℕ → List End) (src : End → ℕ) (v : ℕ) :
    ∀ (I : List Update) (A : ℕ → List End),
      (∀ e, e ∈ insertedEdges I → src (e, true) ≠ v ∧ src (e, false) ≠ v) →
      applyOrdEdits A (outInsertEdits t src I) v = A v
  | [], _, _ => rfl
  | .insert e a b :: I, A, h => by
    obtain ⟨h1, h2⟩ := h e (by simp [insertedEdges])
    show applyOrdEdits (applyOrdEdit (applyOrdEdit A (.insertBefore (src (e, true)) (e, true) _))
      (.insertBefore (src (e, false)) (e, false) _)) (outInsertEdits t src I) v = A v
    rw [applyOrdEdits_outInsertEdits_of_ne t src v I _
      (fun e' he' => h e' (by simp [insertedEdges, he']))]
    simp only [applyOrdEdit]
    rw [Function.update_of_ne (Ne.symm h2), Function.update_of_ne (Ne.symm h1)]
  | .delete _ :: I, A, h => by
    simp only [outInsertEdits]
    exact applyOrdEdits_outInsertEdits_of_ne t src v I A
      (fun e' he' => h e' (by simpa [insertedEdges] using he'))
  | .split .. :: I, A, h => by
    simp only [outInsertEdits]
    exact applyOrdEdits_outInsertEdits_of_ne t src v I A
      (fun e' he' => h e' (by simpa [insertedEdges] using he'))

/-- **Vertices that keep their output lists.** If every vertex outside `T₀` is not named
by the output batch and keeps its core list, then `T₀` covers the step (`OutRotCover`). -/
theorem outRotCover_of_untouched (st : BundleTreeState L) (U : List Update)
    (ord ord' : ℕ → List End) (hready : OutStepReady sparsify st U ord ord') (T₀ : List ℕ)
    (h : ∀ v, v ∉ T₀ → ¬ OutTouched sparsify st U ord ord' v ∧
      outCoreOrder (stepBundleTree sparsify st U ord ord').state ord' v = outCoreOrder st ord v) :
    OutRotCover sparsify st U ord ord' T₀ := by
  intro v hv
  obtain ⟨hnt, hcore⟩ := h v hv
  set info := stepBundleTree sparsify st U ord ord' with hinfo
  have hmem := ordMemOf_outOrder sparsify st U ord ord' hready
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, -⟩, -, -, hS_sub, hS_sub'⟩ := hready
  have hkeep : outKeep sparsify st U ord ord' ⊆ info.state.S_cur.E := by
    intro e he
    unfold outKeep at he
    simp only [Finset.mem_sdiff, Finset.mem_inter] at he
    exact he.1.1.2
  -- the edits do not touch the list at `v`
  have hbase : outBaseOrder sparsify st U ord ord' v = st.outOrder ord v := by
    unfold outBaseOrder
    rw [applyOrdEdits_append', applyOrdEdits_outInsertEdits_of_ne _ _ v _ _ ?_]
    · apply applyOrdEdits_outPrefixEdits_of_not_named v
      · intro v₁ v₂ St Sh hmem'
        rcases List.mem_append.mp hmem' with hd | hs
        · obtain ⟨e, -, he⟩ := List.mem_map.mp hd
          cases he
        · constructor
          · rintro rfl; exact hnt (Or.inr (Or.inl ⟨v, v₂, St, Sh, hs, Or.inl rfl⟩))
          · rintro rfl; exact hnt (Or.inr (Or.inl ⟨v₁, v, St, Sh, hs, Or.inr rfl⟩))
      · intro e hd x hx
        rintro rfl
        obtain ⟨hxE, hxv⟩ := (hmem.1 v x).mp hx
        have he : x.1 ∈ outDelList sparsify st U ord ord' := by
          rcases List.mem_append.mp hd with hd | hd
          · obtain ⟨e', he', hee⟩ := List.mem_map.mp hd
            cases hee; exact he'
          · exfalso
            revert hd
            generalize info.U_core = UC
            induction UC with
            | nil => simp [restrictSplits]
            | cons u UC ih =>
              cases u with
              | split v₁ v₂ St Sh =>
                simp only [restrictSplits, List.mem_cons, reduceCtorEq, false_or]; exact ih
              | insert e' a b => exact ih
              | delete e' => exact ih
        obtain ⟨e, b⟩ := x
        cases b
        · exact hnt (Or.inl ⟨e, he, Or.inr hxv⟩)
        · exact hnt (Or.inl ⟨e, he, Or.inl hxv⟩)
    · intro e he
      rw [outInsBatch, insertedEdges_map_insert'] at he
      constructor
      · intro h'; exact hnt (Or.inr (Or.inr ⟨e, he, Or.inl h'⟩))
      · intro h'; exact hnt (Or.inr (Or.inr ⟨e, he, Or.inr h'⟩))
  rw [hbase, outOrder_eq_filter, outOrder_eq_filter, hcore]
  -- the new list has the same ends
  apply List.filter_congr
  intro x hx
  have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ st.cs) (ρ' : Rotation st.cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  obtain ⟨hxC, hxv⟩ := mem_outCoreOrder hex hx
  have hI' := compLSFBatch_inv hI hBU
  have hG_eq := compLSFBatch_G st.cs U
  have hex' : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ info.state.cs)
      (ρ' : Rotation info.state.cs.G), ρ'.order = ord' := by
    refine ⟨C_lsst, ℓ₀, hI', hG_eq.symm ▸ σ, ?_⟩
    have : ∀ {G H : MGraph} (h : G = H) (σ : Rotation G), (h ▸ σ).order = σ.order := by
      intro G H h σ; subst h; rfl
    exact (this hG_eq.symm σ).trans hσ
  have hx' : x ∈ outCoreOrder info.state ord' v := hcore ▸ hx
  obtain ⟨hxC', hxv'⟩ := mem_outCoreOrder hex' hx'
  simp only [decide_eq_decide]
  constructor
  · intro hxS
    by_contra hxS'
    have he : x.1 ∈ outDelList sparsify st U ord ord' := by
      rw [outDelList, Finset.mem_sort, Finset.mem_sdiff]
      exact ⟨hxS, fun hk => hxS' (hkeep hk)⟩
    have hsrc : st.S_cur.src x = v := by
      have hsub := hS_sub.2.2 x.1 hxS
      obtain ⟨e, b⟩ := x
      cases b
      · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hxv ⊢
        exact hsub.2.trans hxv
      · simp only [MGraph.src, ↓reduceIte] at hxv ⊢
        exact hsub.1.trans hxv
    obtain ⟨e, b⟩ := x
    cases b
    · exact hnt (Or.inl ⟨e, he, Or.inr hsrc⟩)
    · exact hnt (Or.inl ⟨e, he, Or.inl hsrc⟩)
  · intro hxS'
    by_contra hxS
    have he : x.1 ∈ outInsList sparsify st U ord ord' := by
      rw [outInsList, Finset.mem_sort, Finset.mem_sdiff]
      exact ⟨hxS', fun hk => hxS (by
        unfold outKeep at hk
        simp only [Finset.mem_sdiff, Finset.mem_inter] at hk
        exact hk.1.1.1)⟩
    have hsrc : info.state.S_cur.src x = v := by
      have hsub := hS_sub'.2.2 x.1 hxS'
      obtain ⟨e, b⟩ := x
      cases b
      · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hxv' ⊢
        exact hsub.2.trans hxv'
      · simp only [MGraph.src, ↓reduceIte] at hxv' ⊢
        exact hsub.1.trans hxv'
    obtain ⟨e, b⟩ := x
    cases b
    · exact hnt (Or.inr (Or.inr ⟨e, he, Or.inr hsrc⟩))
    · exact hnt (Or.inr (Or.inr ⟨e, he, Or.inl hsrc⟩))

end MinCostFlow.SparseCore.Program
