module

public import MinCostFlow.MinRatio.PathAccountNumericBounds
public import MinCostFlow.MinRatio.PathCutNumericBounds
import MinCostFlow.Num.WordBounds

/-!
# Fixed-point ranges over path tree operations

The bounds for Section 6 (pages 29–30) track evaluated accounts, lazy
route charges, and inactive edge records. Together they give the
signed range needed by the fixed-point tree interface.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut

/-- Numeric state invariant for the path tree. The free records still
occupy the machine layout and must fit even though they are inactive. -/
@[expose] def PathTreeNumericInv (st : PathTreeState)
    (trees : List AuxTree) (account tag : ℤ) : Prop :=
  0 ≤ account ∧ 0 ≤ tag ∧
  (∀ t ∈ trees, ∀ x ∈ t.toList, pathTagRouteMagnitude st.splay (t.pathTo x) ≤ tag) ∧
  (∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
    |val.gradient| ≤ account ∧ |val.length| ≤ account ∧ |val.flow| ≤ account ∧
      |val.detector| ≤ account) ∧
  (∀ i ≤ 2 * st.n, i ∉ trees.flatMap AuxTree.toList →
    PathNodeBound account (st.splay.nodes i))

private theorem nodeBound_mono {s : SplayNode (Option PathEdgeValue) PathSummary PathTag}
    {B C : ℤ} (hb : PathNodeBound B s) (hBC : B ≤ C) : PathNodeBound C s := by
  obtain ⟨hv, hg, hl, hd, hf, ht⟩ := hb
  refine ⟨?_, hg.trans hBC, hl.trans hBC, fun z hz => (hd z hz).trans hBC,
    hf.trans hBC, ht.trans hBC⟩
  intro v hval
  obtain ⟨hg, hl, hf, hd⟩ := hv v hval
  exact ⟨hg.trans hBC, hl.trans hBC, hf.trans hBC, hd.trans hBC⟩

/-- The zero forest has empty accounts and a zero tag budget. -/
theorem pathTreeNumericInv_init (n : ℕ) {B : ℤ} (hB : 0 ≤ B) :
    let init := lctInit pathPayload n none
    let trees := (List.range n).map (fun i => AuxTree.node (vid i) .leaf .leaf)
    let free := (List.range (n - 1)).map (fun i => n + 1 + i)
    LctInvWith pathPayload init trees free (fun _ => 1) ∧ PathTreeNumericInv init trees B 0 := by
  dsimp only
  obtain ⟨W, htag⟩ := lctInit_route_bound n
  refine ⟨W, hB, le_rfl, htag, ?_, fun i _ _ => nodeBound_mono (lctInit_pathNodeBound n i) hB⟩
  intro i val h
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  have hnode := (lctInit_spec pathPayload_laws n none).2.2.2.1 j (List.mem_range.mp hj)
  rw [hnode] at hm
  simp at hm

/-- A machine capacity that covers the budget yields the path tree range premise. -/
theorem PathTreeNumericInv.fits
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    {h L : ℕ} {B R : ℤ} (W : LctInvWith pathPayload st trees free depth)
    (hn : PathTreeNumericInv st trees B R)
    (hroom : 2 * ((2 * st.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity h L : ℤ)) :
    pathTreeFits h L st := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  refine pathTreeFits_of_evaluatedAccounts W hB hR routes
    (fun t ht i v hv => accounts i v (List.mem_flatMap.mpr ⟨_, ht, hv⟩)) ?_ hroom
  intro i hi hoff
  have hsize : (1 : ℤ) ≤ ((2 * st.n + 1 : ℕ) : ℤ) := by omega
  have hm := mul_le_mul_of_nonneg_right hsize (add_nonneg hB hR)
  rw [one_mul] at hm
  exact nodeBound_mono (inactive i hi hoff) ((le_add_of_nonneg_right hR).trans hm)

private theorem inactive_same_free
    {st next : PathTreeState} {trees trees' : List AuxTree} {free : List ℕ}
    {d d' : ℕ → ℕ} {B C : ℤ}
    (W : LctInvWith pathPayload st trees free d)
    (W' : LctInvWith pathPayload next trees' free d')
    (hn : next.n = st.n) (hBC : B ≤ C)
    (frame : ∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z)
    (hb : ∀ z ≤ 2 * st.n, z ∉ trees.flatMap AuxTree.toList → PathNodeBound B (st.splay.nodes z)) :
    ∀ z ≤ 2 * next.n, z ∉ trees'.flatMap AuxTree.toList → PathNodeBound C (next.splay.nodes z) := by
  intro z hz hs
  have hinactive : z ∉ trees.flatMap AuxTree.toList := fun hm =>
    hs (lct_active_mem_of_same_freeList W' W hn.symm hm)
  rw [frame z hinactive]
  exact nodeBound_mono (hb z (hn ▸ hz) hinactive) hBC

/-- Exposing a node preserves both budgets, including inactive records. -/
theorem pathTreeNumericInv_expose
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees free d) (hn : PathTreeNumericInv st trees B R)
    {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) :
    ∃ ts, LctInvWith pathPayload (lctExpose pathPayload st x) ts free d ∧
      PathTreeNumericInv (lctExpose pathPayload st x) ts B R := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨ts, W', route, frame⟩ := lctExpose_route_bound_and_frame W ht hx routes
  exact ⟨ts, W', hB, hR, route, pathForestAccounts_expose_bound W ht hx W' accounts,
    inactive_same_free W W' rfl le_rfl frame inactive⟩

/-- Reading a path summary preserves both budgets and all inactive records. -/
theorem pathTreeNumericInv_summary
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees free d) (hn : PathTreeNumericInv st trees B R)
    {t : AuxTree} {u v : ℕ} (ht : t ∈ trees) (hu : u ∈ t.toList)
    (huv : isVertex st.n u) (hvv : isVertex st.n v) :
    let next := (lctPathSummary pathPayload st u v).1
    ∃ ts d', LctInvWith pathPayload next ts free d' ∧ PathTreeNumericInv next ts B R := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨ts, d', W', route, frame⟩ := lctPathSummary_route_bound W ht hu huv hvv routes
  exact ⟨ts, d', W', hB, hR, route, pathForestAccounts_summary_bound W ht hu huv hvv W' accounts,
    inactive_same_free W W' rfl le_rfl frame inactive⟩

/-- Replacing a point account by a bounded value preserves both budgets. -/
theorem pathTreeNumericInv_write
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees free d) (hn : PathTreeNumericInv st trees B R)
    {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) {value : Option PathEdgeValue}
    (hvalue : ∀ val, value = some val →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    let next := pathTreeWrite st x value
    ∃ ts, LctInvWith pathPayload next ts free d ∧ PathTreeNumericInv next ts B R := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨ts, W', route, frame⟩ := pathTreeWrite_route_bound W ht hx routes value
  exact ⟨ts, W', hB, hR, route, pathForestAccounts_write_bound W ht hx W' hvalue accounts,
    inactive_same_free W W' rfl le_rfl frame inactive⟩

/-- Path application charges one tag magnitude to each budget. -/
theorem pathTreeNumericInv_apply
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees free d) (hn : PathTreeNumericInv st trees B R)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList) (huv : isVertex st.n u)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList) (hvv : isVertex st.n v)
    (hconn : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    (tag : PathTag) :
    let next := lctPathApply pathPayload st u v tag
    ∃ ts d', LctInvWith pathPayload next ts free d' ∧
      PathTreeNumericInv next ts (B + pathTagMagnitude tag) (R + pathTagMagnitude tag) := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨ts, d', W', route, frame⟩ := lctPathApply_route_bound W htu hu huv htv hv hvv hconn routes tag
  have htag : 0 ≤ pathTagMagnitude tag := add_nonneg (abs_nonneg _) (abs_nonneg _)
  exact ⟨ts, d', W', add_nonneg hB htag, add_nonneg hR htag, route,
    pathForestAccounts_apply_bound W htu hu huv htv hv hvv hconn W' accounts,
    inactive_same_free W W' rfl (le_add_of_nonneg_right htag) frame inactive⟩

private theorem link_vertexCount (st : PathTreeState) (u v : ℕ) (value : Option PathEdgeValue) :
    (lctLink pathPayload st u v value).n = st.n := by
  unfold lctLink lctLinkCost
  split
  · rfl
  · dsimp only
    split <;> rfl

private theorem cut_vertexCount (st : PathTreeState) (u v : ℕ) :
    (lctCut pathPayload st u v).n = st.n := by
  unfold lctCut lctCutCost
  split
  · rfl
  · dsimp only
    split
    · rfl
    · split <;> first | rfl | (split <;> rfl)

/-- Link preserves both budgets and the bounds on all unallocated slots. -/
theorem pathTreeNumericInv_link
    {st : PathTreeState} {trees : List AuxTree} {edge : ℕ} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees (edge :: free) d)
    (hn : PathTreeNumericInv st trees B R)
    {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v)
    (hdisc : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u ≠
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    {value : Option PathEdgeValue}
    (hvalue : ∀ val, value = some val →
      |val.gradient| ≤ B ∧ |val.length| ≤ B ∧ |val.flow| ≤ B ∧ |val.detector| ≤ B) :
    let next := lctLink pathPayload st u v value
    ∃ ts d', LctInvWith pathPayload next ts free d' ∧ PathTreeNumericInv next ts B R := by
  intro next
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨ts, d', W', route, frame⟩ := lctLink_route_bound W hu hv hdisc hR routes value
  refine ⟨ts, d', W', hB, hR, route, pathForestAccounts_link_bound W hu hv hdisc W' hvalue accounts, ?_⟩
  have hn' : next.n = st.n := link_vertexCount st u v value
  intro z hz hmiss
  have he : z ≠ edge := by
    intro he
    subst z
    have hes := W.freeValid edge List.mem_cons_self
    exact hmiss ((W'.partitionSlots edge (hn'.symm ▸ hes)).mpr (List.nodup_cons.mp W.freeNodup).1)
  have hold : z ∉ trees.flatMap AuxTree.toList := by
    intro hact
    have ha := W.activeValid z hact
    by_cases hv : z ≤ st.n
    · exact hmiss (pathVertex_mem_active W' (hn'.symm ▸ (show isVertex st.n z from ⟨ha.1, hv⟩)))
    · have hez : isEdgeSlot st.n z := ⟨by omega, ha.2⟩
      exact hmiss ((W'.partitionSlots z (hn'.symm ▸ hez)).mpr
        fun hf => (W.partitionSlots z hez).mp hact (List.mem_cons_of_mem _ hf))
  rw [frame z hold he]
  exact inactive z (hn' ▸ hz) hold

/-- Cutting an existing edge preserves both budgets, including the freed record. -/
theorem pathTreeNumericInv_cut
    {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {B R : ℤ} (W : LctInvWith pathPayload st trees free d)
    (hn : PathTreeNumericInv st trees B R)
    {u v : ℕ} (hu : isVertex st.n u) (hv : isVertex st.n v) (huv : u ≠ v)
    (hadj : let par := inducedSubPar pathPayload st.splay trees
      ∃ edge ∈ trees.flatMap AuxTree.toList, (par v = edge ∧ par edge = u) ∨
        (par u = edge ∧ par edge = v)) :
    let next := lctCut pathPayload st u v
    ∃ edge ts d', LctInvWith pathPayload next ts (edge :: free) d' ∧
      PathTreeNumericInv next ts B R := by
  intro next
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := hn
  obtain ⟨edge, ts, d', W', route, frame, bound⟩ := lctCut_route_bound W hu hv huv hadj routes
  obtain ⟨freed, pairs⟩ := bound B hB accounts
  exact ⟨edge, ts, d', W', hB, hR, route, pairs,
    lctCut_inactive_nodeBound W W' (cut_vertexCount st u v) frame freed inactive⟩

/-- Increasing either budget preserves the numeric invariant. -/
theorem PathTreeNumericInv.mono {st : PathTreeState} {trees : List AuxTree} {B R C S : ℤ}
    (h : PathTreeNumericInv st trees B R) (hBC : B ≤ C) (hRS : R ≤ S) :
    PathTreeNumericInv st trees C S := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := h
  refine ⟨hB.trans hBC, hR.trans hRS, fun c hc x hx => (routes c hc x hx).trans hRS, ?_,
    fun i hi hm => nodeBound_mono (inactive i hi hm) hBC⟩
  intro i v hv
  obtain ⟨hg, hl, hf, hd⟩ := accounts i v hv
  exact ⟨hg.trans hBC, hl.trans hBC, hf.trans hBC, hd.trans hBC⟩

/-- The numeric invariant holds for any presentation of the same forest
with the same free slots. -/
theorem PathTreeNumericInv.relabel
    {st : PathTreeState} {trees trees' : List AuxTree} {free : List ℕ}
    {d d' : ℕ → ℕ} {B R : ℤ}
    (h : PathTreeNumericInv st trees B R)
    (W : LctInvWith pathPayload st trees free d) (W' : LctInvWith pathPayload st trees' free d') :
    PathTreeNumericInv st trees' B R := by
  obtain ⟨hB, hR, routes, accounts, inactive⟩ := h
  refine ⟨hB, hR, lct_route_bound_of_same_state W W' routes, ?_,
    inactive_same_free W W' rfl le_rfl (fun _ _ => rfl) inactive⟩
  intro i v hv
  obtain ⟨t, ht, hm⟩ := List.mem_flatMap.mp hv
  have hmem := lct_tree_mem_of_same_pointers W W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ht
  exact accounts i v (List.mem_flatMap.mpr ⟨_, hmem, hm⟩)

/-- A history of the Section 6 path tree operations, recording the total
magnitude of the tags that have been applied. New point and link values
are bounded by the base account budget. -/
inductive PathTreeRangeHistory (n : ℕ) (B : ℤ) :
    PathTreeState → List AuxTree → List ℕ → (ℕ → ℕ) → ℤ → Prop
  | init : PathTreeRangeHistory n B (lctInit pathPayload n none)
      ((List.range n).map (fun i => AuxTree.node (vid i) .leaf .leaf))
      ((List.range (n - 1)).map (fun i => n + 1 + i)) (fun _ => 1) 0
  | relabel {st trees free d q ts d'} :
      PathTreeRangeHistory n B st trees free d q →
      LctInvWith pathPayload st ts free d' →
      PathTreeRangeHistory n B st ts free d' q
  | expose {st trees free d q t x ts d'} :
      PathTreeRangeHistory n B st trees free d q →
      t ∈ trees → x ∈ t.toList →
      LctInvWith pathPayload (lctExpose pathPayload st x) ts free d' →
      PathTreeRangeHistory n B (lctExpose pathPayload st x) ts free d' q
  | summary {st trees free d q t u v ts d'} :
      PathTreeRangeHistory n B st trees free d q →
      t ∈ trees → u ∈ t.toList → isVertex st.n u → isVertex st.n v →
      LctInvWith pathPayload (lctPathSummary pathPayload st u v).1 ts free d' →
      PathTreeRangeHistory n B (lctPathSummary pathPayload st u v).1 ts free d' q
  | write {st trees free d q t x value ts d'} :
      PathTreeRangeHistory n B st trees free d q →
      t ∈ trees → x ∈ t.toList →
      (∀ v, value = some v →
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) →
      LctInvWith pathPayload (pathTreeWrite st x value) ts free d' →
      PathTreeRangeHistory n B (pathTreeWrite st x value) ts free d' q
  | apply {st trees free d q tu tv u v tag ts d'} :
      PathTreeRangeHistory n B st trees free d q →
      tu ∈ trees → u ∈ tu.toList → isVertex st.n u →
      tv ∈ trees → v ∈ tv.toList → isVertex st.n v →
      (subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u =
        subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v) →
      LctInvWith pathPayload (lctPathApply pathPayload st u v tag) ts free d' →
      PathTreeRangeHistory n B (lctPathApply pathPayload st u v tag) ts free d'
        (q + pathTagMagnitude tag)
  | link {st trees edge free d q u v value ts d'} :
      PathTreeRangeHistory n B st trees (edge :: free) d q →
      isVertex st.n u → isVertex st.n v →
      (subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u ≠
        subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v) →
      (∀ v, value = some v →
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) →
      LctInvWith pathPayload (lctLink pathPayload st u v value) ts free d' →
      PathTreeRangeHistory n B (lctLink pathPayload st u v value) ts free d' q
  | cut {st trees free d q u v ts edge d'} :
      PathTreeRangeHistory n B st trees free d q →
      isVertex st.n u → isVertex st.n v → u ≠ v →
      (let par := inducedSubPar pathPayload st.splay trees
        ∃ e ∈ trees.flatMap AuxTree.toList, (par v = e ∧ par e = u) ∨
          (par u = e ∧ par e = v)) →
      LctInvWith pathPayload (lctCut pathPayload st u v) ts (edge :: free) d' →
      PathTreeRangeHistory n B (lctCut pathPayload st u v) ts (edge :: free) d' q

private theorem boundedValue_mono {value : Option PathEdgeValue} {B C : ℤ}
    (hv : ∀ v, value = some v →
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B)
    (h : B ≤ C) :
    ∀ v, value = some v →
      |v.gradient| ≤ C ∧ |v.length| ≤ C ∧ |v.flow| ≤ C ∧ |v.detector| ≤ C := by
  intro v he
  obtain ⟨hg, hl, hf, hd⟩ := hv v he
  exact ⟨hg.trans h, hl.trans h, hf.trans h, hd.trans h⟩

/-- The account budget grows by the total tag magnitude and the route
budget starts at zero and grows by the same total. -/
theorem PathTreeRangeHistory.numeric
    {n : ℕ} {B q : ℤ} {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    (history : PathTreeRangeHistory n B st trees free d q) (hB : 0 ≤ B) :
    st.n = n ∧ LctInvWith pathPayload st trees free d ∧ PathTreeNumericInv st trees (B + q) q := by
  induction history with
  | init => exact ⟨rfl, by simpa only [add_zero] using pathTreeNumericInv_init n hB⟩
  | relabel _ W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    exact ⟨hn, W', hb.relabel W W'⟩
  | expose _ ht hx W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    obtain ⟨_, W₀, h₀⟩ := pathTreeNumericInv_expose W hb ht hx
    exact ⟨hn, W', h₀.relabel W₀ W'⟩
  | summary _ ht hx huv hvv W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    obtain ⟨_, _, W₀, h₀⟩ := pathTreeNumericInv_summary W hb ht hx huv hvv
    exact ⟨hn, W', h₀.relabel W₀ W'⟩
  | write _ ht hx hvalue W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    have bounded := boundedValue_mono hvalue (le_add_of_nonneg_right hb.2.1)
    obtain ⟨_, W₀, h₀⟩ := pathTreeNumericInv_write W hb ht hx bounded
    exact ⟨hn, W', h₀.relabel W₀ W'⟩
  | apply _ ht hu huv hv hvm hvv hconn W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    obtain ⟨_, _, W₀, h₀⟩ := pathTreeNumericInv_apply W hb ht hu huv hv hvm hvv hconn _
    exact ⟨hn, W', by simpa only [add_assoc] using h₀.relabel W₀ W'⟩
  | link _ hu hv hdisc hvalue W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    have bounded := boundedValue_mono hvalue (le_add_of_nonneg_right hb.2.1)
    obtain ⟨_, _, W₀, h₀⟩ := pathTreeNumericInv_link W hb hu hv hdisc bounded
    exact ⟨(link_vertexCount _ _ _ _).trans hn, W', h₀.relabel W₀ W'⟩
  | cut _ hu hv huv hadj W' ih =>
    obtain ⟨hn, W, hb⟩ := ih
    obtain ⟨edge₀, _, _, W₀, h₀⟩ := pathTreeNumericInv_cut W hb hu hv huv hadj
    have he := W₀.freeListInv.2.1.symm.trans W'.freeListInv.2.1
    cases he
    exact ⟨(cut_vertexCount _ _ _).trans hn, W', h₀.relabel W₀ W'⟩

/-- A single signed width suffices at every history endpoint whose tag
total is at most the supplied bound. -/
theorem PathTreeRangeHistory.fits
    {n : ℕ} {B q Q : ℤ} {st : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ}
    {h L : ℕ} (history : PathTreeRangeHistory n B st trees free d q)
    (hB : 0 ≤ B) (hq : q ≤ Q)
    (hcapacity : 2 * ((2 * n + 1 : ℕ) : ℤ) * (B + Q + Q) < (Num.capacity h L : ℤ)) :
    pathTreeFits h L st := by
  obtain ⟨hn, W, hb⟩ := history.numeric hB
  exact (hb.mono (add_le_add_right hq B) hq).fits W (by rwa [hn])

/-- An explicit logarithmic limb count for a tree with a bounded tag total.
The same count works for any positive limb size. -/
def pathTreeHistoryLimbs (n B Q : ℕ) : ℕ :=
  Nat.clog 2 (max (2 * n + 2) (2 * (2 * n + 1) * (B + Q + Q) + 1))

/-- The selected limb count also covers the tree contract's rank arithmetic. -/
theorem pathTreeHistoryLimbs_log_le (n B Q h : ℕ) (hh : 0 < h) :
    Nat.log 2 (2 * n + 1) ≤ h * pathTreeHistoryLimbs n B Q := by
  let L := pathTreeHistoryLimbs n B Q
  have h₁ : 2 * n + 2 ≤ 2 ^ L :=
    (Nat.le_max_left _ _).trans (Nat.le_pow_clog (by decide) _)
  have h₂ : Nat.log 2 (2 * n + 1) < L :=
    Nat.log_lt_of_lt_pow (by omega) (by omega)
  exact h₂.le.trans (by simpa using Nat.mul_le_mul_right L hh)

/-- The logarithmic limb count fits every endpoint of a bounded tree history. -/
theorem PathTreeRangeHistory.fits_historyLimbs
    {n B Q : ℕ} {q : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {d : ℕ → ℕ} {h : ℕ}
    (history : PathTreeRangeHistory n (B : ℤ) st trees free d q)
    (hq : q ≤ (Q : ℤ)) (hh : 0 < h) :
    pathTreeFits h (pathTreeHistoryLimbs n B Q) st := by
  refine history.fits (Int.natCast_nonneg B) hq ?_
  rw [Num.capacity_eq_two_pow]
  let size := 2 * (2 * n + 1) * (B + Q + Q)
  let L := pathTreeHistoryLimbs n B Q
  have h₁ : size + 1 ≤ 2 ^ L :=
    (Nat.le_max_right (2 * n + 2) (size + 1)).trans (Nat.le_pow_clog (by decide) _)
  have h₂ : L ≤ h * L := by
    simpa using Nat.mul_le_mul_right L hh
  have h₃ : size < 2 ^ (h * L) :=
    (Nat.lt_of_succ_le h₁).trans_le (Nat.pow_le_pow_right (by decide) h₂)
  exact_mod_cast h₃

/-- A physical path tree determines its list of free slots. -/
theorem freeListInv_unique
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {head : ℕ} {left right : List ℕ}
    (h₁ : FreeListInv s head left) (h₂ : FreeListInv s head right) :
    left = right := by
  induction left generalizing right head with
  | nil =>
    cases right with
    | nil => rfl
    | cons x xs => exact (h₂.1 h₁).elim
  | cons x xs ih =>
    cases right with
    | nil => exact (h₁.1 h₂).elim
    | cons y ys =>
      have he : x = y := h₁.2.1.symm.trans h₂.2.1
      rw [he, ih h₁.2.2 h₂.2.2]

/-- The same fixed width suffices after exposing any active node, including
the slot chosen by FindReady. -/
theorem PathTreeRangeHistory.expose_fits_historyLimbs
    {n B Q : ℕ} {q : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {d : ℕ → ℕ} {h x : ℕ}
    (history : PathTreeRangeHistory n (B : ℤ) st trees free d q)
    (hq : q ≤ (Q : ℤ)) (hh : 0 < h) (hx : pathTreeActive st x) :
    pathTreeFits h (pathTreeHistoryLimbs n B Q) (lctExpose pathPayload st x) := by
  have ⟨_, W, numeric⟩ := history.numeric (Int.natCast_nonneg B)
  obtain ⟨ts, fs, d', WA, hm⟩ := hx
  have he := freeListInv_unique WA.freeListInv W.freeListInv
  subst fs
  have hactive := lct_active_mem_of_same_freeList W WA rfl hm
  obtain ⟨t, ht, htMem⟩ := List.mem_flatMap.mp hactive
  obtain ⟨us, WE, _⟩ := pathTreeNumericInv_expose W numeric ht htMem
  exact (history.expose ht htMem WE).fits_historyLimbs hq hh

/-- The quantified numeric precondition of FindReady follows from the
history range and does not require picking a ready slot in advance. -/
theorem PathTreeRangeHistory.ready_fits_historyLimbs
    {n B Q : ℕ} {q : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {d : ℕ → ℕ} {h : ℕ}
    (history : PathTreeRangeHistory n (B : ℤ) st trees free d q)
    (hq : q ≤ (Q : ℤ)) (hh : 0 < h) :
    ∀ x, pathTreeReady st x →
      pathTreeFits h (pathTreeHistoryLimbs n B Q) (lctExpose pathPayload st x) :=
  fun _ hx => history.expose_fits_historyLimbs hq hh hx.2.1

/-- A flow adjustment charges its absolute amount once for each of the
flow and detector coordinates. -/
theorem pathTagMagnitude_ofFlow (delta : ℤ) :
    pathTagMagnitude (PathTag.ofFlow delta) = 2 * |delta| := by
  simp [pathTagMagnitude, PathTag.ofFlow, abs_abs, two_mul]

/-- For signed path adjustments bounded by a common amount, the total tag
budget is at most twice that amount times the number of adjustments. -/
theorem pathFlowTagTotal_le (changes : List ℤ) {bound : ℤ}
    (h : ∀ delta ∈ changes, |delta| ≤ bound) :
    (changes.map (fun delta => pathTagMagnitude (PathTag.ofFlow delta))).sum ≤
      2 * (changes.length : ℤ) * bound := by
  induction changes with
  | nil => simp
  | cons delta rest ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h delta List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      pathTagMagnitude_ofFlow] at *
    rw [mul_add, add_mul, mul_one]
    omega

end MinCostFlow.MinRatio
