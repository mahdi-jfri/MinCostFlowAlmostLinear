module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Rot
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Sel
public import MinCostFlow.SparseCore.Program.OutStepJoinModel
public import MinCostFlow.SparseCore.Program.RestartModelState

/-!
# The model facts of Phase 4 (`AssemblyFirstStepP4Model`)

The pieces of Phase 4 (`AssemblyFirstStepP4Lists`, `AssemblyFirstStepP4Rot`,
`AssemblyFirstStepP4Reemb`) are stated on abstract lists. This file proves the facts of the
model that turn their results into the forms of the step of a branch:
1. `ordSrc_rotation`: in the order of a rotation, the vertex of an end of an edge is the vertex
   where the end starts.
2. `p4_ins_ord`: an entering edge of the output step is an edge of the graph after the batch, so
   both its ends are in the new order, at the tail and at the head of the edge.
3. `outInsAt_congr`: `OutInsAt` only reads the ends of the listed edges.
4. `p4_rot_cover`: the sorted distinct entries of the raw list of `asmFirstP4RotStmt`, with the
   ends of the entering edges at the new roots, cover the step (`OutRotCover`).
5. `p4_reemb_eq`: the list `Lr` of the front with the leaving edges gives the sorted list of the
   re-embedded edges of the step, when the lazy lists hold exactly the edges of the bundles of
   the newly active components.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

/-- In the order of a rotation, the vertex of an end of an edge of the graph is the vertex where
the end starts. -/
theorem ordSrc_rotation {G : MGraph} (σ : Rotation G) {x : End} (hx : x.1 ∈ G.E) :
    ordSrc σ.order x = G.src x := by
  classical
  have hex : ∃ v, x ∈ σ.order v := ⟨G.src x, (σ.mem_order _ x).mpr ⟨hx, rfl⟩⟩
  simp only [ordSrc, hex, ↓reduceDIte]
  exact ((σ.mem_order _ x).mp hex.choose_spec).2.symm

/-- An entering edge of the output step is an edge of the graph after the batch: it lies in the
new output graph, which lies in the new core graph (`RestartScurModelInv` of the new state). -/
theorem outInsSet_subset_G {depth : ℕ} (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End)
    (hModN : RestartScurModelInv (stepBundleTree sp tr U ord ord').state) :
    ∀ e ∈ outInsSet sp tr U ord ord', e ∈ (compLSFBatch tr.cs U).G.E := by
  intro e he
  have hS : e ∈ (stepBundleTree sp tr U ord ord').state.S_cur.E := (Finset.mem_sdiff.mp he).1
  exact (Finset.mem_sdiff.mp (hModN.2.2.2.1.2.1 hS)).1

/-- **The ends of the entering edges in the new order.** Both ends of an entering edge are in
the new order, the tail end at the tail of the edge in the graph after the batch and the head end
at its head. -/
theorem p4_ins_ord {depth : ℕ} (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord ord' : ℕ → List End)
    (hOB : OrderedBatch tr.cs.G U ord ord')
    (hModN : RestartScurModelInv (stepBundleTree sp tr U ord ord').state) :
    ∀ e ∈ outInsSet sp tr U ord ord',
      ((∃ u, (e, true) ∈ ord' u) ∧ (∃ u, (e, false) ∈ ord' u)) ∧
      ordSrc ord' (e, true) = (compLSFBatch tr.cs U).G.tail e ∧
      ordSrc ord' (e, false) = (compLSFBatch tr.cs U).G.head e := by
  intro e he
  obtain ⟨_, σ, -, hσ, -⟩ := hOB
  have hG : (compLSFBatch tr.cs U).G = tr.cs.G.applyBatch U := compLSFBatch_G tr.cs U
  have heG : e ∈ (tr.cs.G.applyBatch U).E := hG ▸ outInsSet_subset_G sp tr U ord ord' hModN e he
  subst hσ
  refine ⟨⟨⟨_, (σ.mem_order _ (e, true)).mpr ⟨heG, rfl⟩⟩,
    ⟨_, (σ.mem_order _ (e, false)).mpr ⟨heG, rfl⟩⟩⟩, ?_, ?_⟩
  · rw [ordSrc_rotation σ heG, hG]
    simp [MGraph.src]
  · rw [ordSrc_rotation σ heG, hG]
    simp [MGraph.src]

/-- `OutInsAt` only reads the ends of the listed edges. -/
theorem outInsAt_congr {mem : ℕ → ℕ} {a : ℕ} {insL : List ℕ} {tl hd tl' hd' : ℕ → ℕ}
    (hI : OutInsAt mem a insL tl hd) (h : ∀ e ∈ insL, tl e = tl' e ∧ hd e = hd' e) :
    OutInsAt mem a insL tl' hd' := by
  refine ⟨hI.1, fun i hi => ?_⟩
  have hmem : insL.getD i 0 ∈ insL := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  obtain ⟨h1, h2, h3⟩ := hI.2 i hi
  exact ⟨h1, h2.trans (h _ hmem).1, h3.trans (h _ hmem).2⟩

/-- **`T₀` covers the step.** Take the raw list of `asmFirstP4RotStmt` for the split list of the
step, a list `insL` of the entering edges, the new roots of the ends of the entering edges, and
the new roots. Its sorted distinct entries meet `OutRotCover`, under the invariant of the LSF,
for a valid ordered batch, when the new output graph meets `RestartScurModelInv`. -/
theorem p4_rot_cover {depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord (applyOrdEdits ord ed)) {insL : List ℕ}
    (hins : insL.toFinset = outInsSet sp tr U ord (applyOrdEdits ord ed)) :
    OutRotCover sp tr U ord (applyOrdEdits ord ed)
      ((p4RotRaw (canonSplitList tr.cs U) insL
        (fun e => (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.tail e))
        (fun e => (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.head e))
        (compLSFBatch tr.cs U).RF.root U ed).toFinset.sort (· ≤ ·)) := by
  obtain ⟨ρ, σ, hρ, hσ, -⟩ := hOB
  have hG : (compLSFBatch tr.cs U).G = tr.cs.G.applyBatch U := compLSFBatch_G tr.cs U
  let σ' : Rotation (compLSFBatch tr.cs U).G :=
    { order := σ.order, nodup := σ.nodup, mem_order := by rw [hG]; exact σ.mem_order }
  have hends : ∀ e ∈ outInsSet sp tr U ord (applyOrdEdits ord ed),
      (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state.S_cur.tail e =
        (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.tail e) ∧
      (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state.S_cur.head e =
        (compLSFBatch tr.cs U).RF.root ((compLSFBatch tr.cs U).G.head e) := fun e he =>
    outStep_ins_ends sp tr U ord (applyOrdEdits ord ed) e (by
      simp only [outInsList, Finset.mem_sort]
      exact he)
  have hsub := asmFirstRotSet_subset_raw sp tr U ord ed hI hU hends
  have hraw := rotAll_toFinset_eq_rawSet sp tr U ord ed hins
  refine asmFirstRotSet_cover sp tr U ord ed hI hU ρ hρ σ' hσ _ fun v hv => ?_
  rw [Finset.mem_sort]
  have hv' := hsub hv
  rw [← hraw] at hv'
  exact hv'

/-- **The re-embedded list of the step.** The list `Lr` holds `p4ReembSet` and the lazy lists,
and the lazy lists hold exactly the edges of the bundles of the newly active components. Then
the sorted distinct entries of `Lr` and the leaving edges are `stepBundleTree_reembList`. -/
theorem p4_reemb_eq (P : DSParams) (tr : BundleTreeState P.L) (U : List Update)
    (ord ord' : ℕ → List End) {nNew : ℕ} (lazyE : Fin nNew → List ℕ) {Lr : List ℕ}
    (hLr : ∀ e, e ∈ Lr ↔ e ∈ p4ReembSet P tr
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord') ∨
      ∃ i : Fin nNew, e ∈ lazyE i)
    (hLazy : ∀ e, (∃ i : Fin nNew, e ∈ lazyE i) ↔
      e ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').newlyActive.biUnion
        fun C => (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges) :
    (Lr ++ (outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord').sort (· ≤ ·)).toFinset.sort
        (· ≤ ·) =
      stepBundleTree_reembList (fun _ => canonicalSparsify P.impl) tr U ord ord' := by
  unfold stepBundleTree_reembList
  congr 1
  ext e
  rw [stepBundleTree_reembSet_eq_sup]
  simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, Finset.mem_sort, hLr,
    ← hLazy, p4ReembSet]
  tauto

end

end MinCostFlow.SparseCore.Program
