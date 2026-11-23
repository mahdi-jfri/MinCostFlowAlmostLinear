module

public import MinCostFlow.LinkCut.PathTree.NumExpose
public import MinCostFlow.LinkCut.Gen.Link
public import MinCostFlow.LinkCut.Gen.Cut

/-!
# The numbers of reroot, path summary, path update, and link fit

Each operation is a short chain of exposes and reroots, so the forest bounds carry from step to
step (`NumExpose`). A reroot adds a reversal at the root of the exposed tree: values only change
sign and no charge changes (`reroot_num`). The last steps of the operations use one node of the
exposed tree, which meets the node bound (`node_bound`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState
  MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

/-- A reversal changes no charge: parents stay, and tag sizes stay. -/
theorem charge_revNode (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (v k y : ℕ) :
    charge (s.revNode pathPayload v) k y = charge s k y := by
  unfold charge
  rw [chainList_congr (par_revNode pathPayload s v) k y]
  exact pathTagRouteMagnitude_revNode s v _

/-- Every node of a bounded forest meets the node bound. -/
theorem node_bound {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {y : ℕ}
    (hy : y ∈ trees.flatMap AuxTree.toList) :
    PathNodeBound ((2 * st.n + 1 : ℕ) * (V + 2 * R)) (st.splay.nodes y) := by
  obtain ⟨t, ht, hyt⟩ := List.mem_flatMap.mp hy
  exact treeB_bound (forestB_treeB W hB ht) C.hV C.hR C.hk y hyt

/-- The charge of an active node is at most `R`. -/
theorem ForestB.chg' {st : PathTreeState} {trees : List AuxTree} {V R : ℤ}
    (hB : ForestB st trees V R) {y : ℕ} (hy : y ∈ trees.flatMap AuxTree.toList) :
    charge st.splay (2 * st.n + 1) y ≤ R := by
  obtain ⟨t, ht, hyt⟩ := List.mem_flatMap.mp hy
  exact hB.chg t ht y hyt

/-- A reroot at a vertex: its numbers fit, and the forest keeps its bounds. -/
theorem reroot_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {v : ℕ}
    (hvv : isVertex st.n v) :
    RerootOk (pathOk h K) pathPayload st v ∧
    ∃ trees' d', LctInvWith pathPayload (lctReroot pathPayload st v) trees' fl d' ∧
      ForestB (lctReroot pathPayload st v) trees' V R := by
  have hv := isVertex_mem_active W hvv
  obtain ⟨hEok, trees_e, W_e, hB_e, hact_e⟩ := expose_num W hB C hv
  refine ⟨⟨hEok, fun _ => revOk_of_bound (node_bound W_e hB_e C (hact_e v hv)) C.room⟩, ?_⟩
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨trees', L, d', -, W', hperm, -, -, -, -, -, -, hsplit, hfp, -⟩ :=
    lctReroot_spec pathPayload_laws W htv hvt hvv
  refine ⟨trees', d', W', ⟨fun p hp => ?_, fun c hc y hy => ?_⟩⟩
  · have hp' := hfp.mem_iff.mp hp
    rcases List.mem_append.mp hp' with hp' | hp'
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp')
      exact valB_rev.mpr (hB.val q (hsplit.mem_iff.mp (List.mem_append_left _ hq)))
    · exact hB.val p (hsplit.mem_iff.mp (List.mem_append_right _ hp'))
  · have hy' : y ∈ trees.flatMap AuxTree.toList :=
      hperm.mem_iff.mp (List.mem_flatMap.mpr ⟨c, hc, hy⟩)
    change charge (SplayState.revNode pathPayload (lctExpose pathPayload st v).splay v)
      (2 * st.n + 1) y ≤ R
    rw [charge_revNode]
    exact hB_e.chg' (hact_e y hy')

/-- A reroot at `u` and an expose of `v`, as in a path summary. -/
theorem rerootExpose_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {u v : ℕ}
    (hu : isVertex st.n u) (hv : isVertex st.n v) :
    RerootExposeOk (pathOk h K) pathPayload st u v ∧
    PathNodeBound ((2 * st.n + 1 : ℕ) * (V + 2 * R))
      ((lctExpose pathPayload (lctReroot pathPayload st u) v).splay.nodes v) := by
  obtain ⟨hR, trees', d', W', hB'⟩ := reroot_num W hB C hu
  have hv' := isVertex_mem_active W' hv
  obtain ⟨hE, trees'', W'', hB'', hact⟩ := expose_num W' hB' C hv'
  exact ⟨⟨hR, hE⟩, node_bound W'' hB'' C (hact v hv')⟩

/-- A path update. The tag fits when it is at most the value bound. -/
theorem pathApply_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {u v : ℕ}
    (hu : isVertex st.n u) (hv : isVertex st.n v) {t : PathTag} (htf : |t.flow| ≤ V)
    (htd : |t.detector| ≤ V) : PathApplyOk (pathOk h K) pathPayload st u v t := by
  obtain ⟨hRE, hb⟩ := rerootExpose_num W hB C hu hv
  have hle : V ≤ (2 * st.n + 1 : ℕ) * (V + 2 * R) := by
    have := C.hR; have := C.hV
    have hk : (1 : ℤ) ≤ (2 * st.n + 1 : ℕ) := by exact_mod_cast C.hk
    nlinarith
  exact ⟨hRE, fun _ => actOk_of_bound hb (htf.trans hle) (htd.trans hle) C.room⟩

/-- A link. The new value fits when its numbers are at most the value bound. -/
theorem link_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {u v : ℕ}
    (hu : isVertex st.n u) (hv : isVertex st.n v) {e : Option PathEdgeValue} (he : ValB V e) :
    LinkOk (pathOk h K) pathPayload st u v e := by
  obtain ⟨hR1, trees', d', W', hB'⟩ := reroot_num W hB C hv
  obtain ⟨hR2, -⟩ := reroot_num W' hB' C hu
  refine ⟨hR1, hR2, ?_⟩
  have hle : V ≤ (2 * st.n + 1 : ℕ) * (V + 2 * R) := by
    have := C.hR; have := C.hV
    have hk : (1 : ℤ) ≤ (2 * st.n + 1 : ℕ) := by exact_mod_cast C.hk
    nlinarith
  have hV := C.hV
  have f {z : ℤ} (hz : |z| ≤ V) : Num.Fits h K z :=
    fits_of_abs (by linarith) C.room
  change PathSummaryFits h K (PathSummary.single e)
  cases e with
  | none =>
    refine ⟨f ?_, f ?_, trivial⟩ <;>
      simp only [PathSummary.single, PathSummary.empty, abs_zero] <;> linarith
  | some e =>
    obtain ⟨h1, h2, -, h4⟩ := he e rfl
    exact ⟨f h1, f h2, f h4⟩

end MinCostFlow.LinkCut.PathTree
