module

public import MinCostFlow.MinRatio.TreeEditLoop
public import MinCostFlow.MinRatio.FreshRecordInput
import MinCostFlow.MinRatio.FreshBatchCompact
public import MinCostFlow.Chain.Algorithm2
import MinCostFlow.LSF.Walks
import MinCostFlow.MinRatio.TreeEditPayloadSave
public import MinCostFlow.MinRatio.PathTreeExpose

/-!
# Running the concrete tree edit fold

The proof of Theorem 5.1 (pages 29–30) charges the tree operations
to the change list. The fold uses the verified Cut and Link iterations
and tracks both the heap reserve and the tree potential.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut DynSpanner.Program

/-- Memory readiness carried by the concrete edit fold. The input registers
retain their initial values, while the heap and unread suffix can change. -/
@[expose] def TreeEditFoldReady (R : DSRep PathTreeState) (handle h L : ℕ)
    (initial : State) (oldBase newBase vc oldCap newCap slots names edgeCap slotCap : ℕ) (oldG newG : MGraph)
    (record : ℕ → ℕ) (value : ℕ → PathEdgeValue) (edits : List TreeChange)
    (x : R.τ) (st : State) : Prop :=
  (∀ r, TreeEditInputReg r → st.regs r = initial.regs r) ∧
    TreeEditHeap R handle x st ∧
    TreeEditSlotStorage R handle slots names edgeCap slotCap x (st.regs 3) ∧
    TreeEditGraphs R handle x st oldBase newBase vc oldCap newCap oldG newG edits ∧
    TreeEditPayloads R handle h L x st edits record value

theorem treeEditHeapBudget_step {heap ret space cap remaining limit : ℕ}
    (hbudget : heap + (remaining + 1) * cap < limit)
    (hspace : space ≤ cap) (hret : ret ≤ heap + space) :
    heap + space < limit ∧ ret + remaining * cap < limit := by
  rw [Nat.add_mul, Nat.one_mul] at hbudget
  omega

theorem treeEditFreeHead_lt {t : PathTreeState}
    (hi : LctInv pathPayload t) (hn : t.freeHead ≠ 0) : t.freeHead < 2 * t.n := by
  obtain ⟨trees, free, depth, hInv⟩ := hi
  cases free with
  | nil => exact (hn hInv.freeListInv).elim
  | cons slot rest =>
    rw [hInv.freeListInv.2.1]
    exact (hInv.freeValid slot List.mem_cons_self).2

/-- The abstract tree is the result of precisely the edits before the cursor. -/
def TreeEditPrefix (oldG newG : MGraph) (value : ℕ → PathEdgeValue)
    (initial : PathTreeState) (remaining : List TreeChange) (current : PathTreeState) : Prop :=
  ∃ processed, diffTreeChanges oldG.E newG.E = processed ++ remaining ∧
    current = processed.foldl (treeEditApply oldG newG value) initial

/-- The prefix before the first edit is empty. -/
theorem TreeEditPrefix.start (oldG newG : MGraph) (value : ℕ → PathEdgeValue)
    (initial : PathTreeState) :
    TreeEditPrefix oldG newG value initial (diffTreeChanges oldG.E newG.E) initial :=
  ⟨[], rfl, rfl⟩

/-- The abstract iteration extends the processed prefix by one edit. -/
theorem TreeEditPrefix.advance {oldG newG : MGraph} {value : ℕ → PathEdgeValue}
    {initial current : PathTreeState} {edit : TreeChange} {remaining : List TreeChange}
    (hp : TreeEditPrefix oldG newG value initial (edit :: remaining) current) :
    TreeEditPrefix oldG newG value initial remaining
      (treeEditApply oldG newG value current edit) := by
  obtain ⟨processed, hcursor, htree⟩ := hp
  exact ⟨processed ++ [edit], by simpa only [List.append_assoc, List.singleton_append] using hcursor,
    by rw [List.foldl_append, ← htree]; rfl⟩

/-- The terminal state is the fold over the full model change list. -/
theorem TreeEditPrefix.finish {oldG newG : MGraph} {value : ℕ → PathEdgeValue}
    {initial current : PathTreeState}
    (hp : TreeEditPrefix oldG newG value initial [] current) :
    current = (diffTreeChanges oldG.E newG.E).foldl (treeEditApply oldG newG value) initial := by
  obtain ⟨processed, hcursor, htree⟩ := hp
  rw [hcursor, List.append_nil]
  exact htree

/-- The prefix invariant reduces the Link precondition to connectivity
correspondence for the forest after the processed edits. -/
theorem TreeEditPrefix.link_conditions {oldG newG : MGraph} {value : ℕ → PathEdgeValue}
    {initial current : PathTreeState} {e : ℕ} {remaining : List TreeChange}
    (hp : TreeEditPrefix oldG newG value initial (.insert e :: remaining) current)
    (hforest : newG.IsForest) (hi : LctInv pathPayload current)
    (hu : newG.tail e < current.n) (hv : newG.head e < current.n)
    (hconn : ∀ processed, diffTreeChanges oldG.E newG.E = processed ++ .insert e :: remaining →
      current = processed.foldl (treeEditApply oldG newG value) initial →
      pathTreeConnected current (vid (newG.tail e)) (vid (newG.head e)) →
      ({ newG with E := applyTreeChanges oldG.E processed } : MGraph).Connected
        (newG.tail e) (newG.head e)) :
    ¬ pathTreeConnected current (vid (newG.tail e)) (vid (newG.head e)) ∧ current.freeHead ≠ 0 := by
  obtain ⟨processed, hcursor, htree⟩ := hp
  exact treeEdit_diff_cursor_link_conditions hforest hcursor hi hu hv (hconn processed hcursor htree)

/-- Cutting a named edge restricts the live slot relation to the
surviving graph, with the same name and slot functions. -/
theorem TreeEditNamedSlots.cut {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {e : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (he : e ∈ G.E) (hne : G.tail e ≠ G.head e) :
    let next := lctCut pathPayload s (vid (G.tail e)) (vid (G.head e))
    ∃ nextTrees nextDepth, LctInvWith pathPayload next nextTrees (slot e :: free) nextDepth ∧
      TreeEditNamedSlots next nextTrees { G with E := G.E.erase e } slot name := by
  dsimp only
  have hvertex (v : ℕ) (hb : v < s.n) : isVertex s.n (vid v) := by unfold isVertex vid; omega
  have ht := hvertex _ (hv e he).1
  have hh := hvertex _ (hv e he).2
  have hdiff : vid (G.tail e) ≠ vid (G.head e) := by
    unfold vid
    omega
  obtain ⟨nextTrees, nextDepth, hnext, _, hremoved, hperm, _, _, hstay⟩ :=
    treeEdit_cut_parent_slot hi ht hh hdiff (hn.forward e he).1 (hn.endpoints e he).symm
  have hnSize : (lctCut pathPayload s (vid (G.tail e)) (vid (G.head e))).n = s.n :=
    treeEditCut_n s _ _
  refine ⟨nextTrees, nextDepth, hnext, ⟨?_, ?_, ?_⟩⟩
  · intro f hf
    obtain ⟨hfNe, hfMem⟩ := Finset.mem_erase.mp hf
    obtain ⟨hactive, hs, hname⟩ := hn.forward f hfMem
    have hsNe : slot f ≠ slot e := by
      intro eq
      exact hfNe (hname.symm.trans ((congrArg name eq).trans (hn.forward e he).2.2))
    have hm := hperm.mem_iff.mpr hactive
    exact ⟨(List.mem_cons.mp hm).resolve_left hsNe, hnSize.symm ▸ hs, hname⟩
  · intro k hk hs
    have hactive := hperm.mem_iff.mp (List.mem_cons_of_mem _ hk)
    obtain ⟨hmem, heq⟩ := hn.inverse k hactive (hnSize ▸ hs)
    have hne' : name k ≠ e := fun h => hremoved ((heq.symm.trans (congrArg slot h)) ▸ hk)
    exact ⟨Finset.mem_erase.mpr ⟨hne', hmem⟩, heq⟩
  · intro f hf
    obtain ⟨hfNe, hfMem⟩ := Finset.mem_erase.mp hf
    obtain ⟨hactive, hs, hname⟩ := hn.forward f hfMem
    have hsNe : slot f ≠ slot e := fun eq =>
      hfNe (hname.symm.trans ((congrArg name eq).trans (hn.forward e he).2.2))
    have htail := hvertex _ (hv f hfMem).1
    have hhead := hvertex _ (hv f hfMem).2
    rcases hn.endpoints f hfMem with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
    · exact hstay _ hactive hs hsNe _ _ htail hhead hpa hpb
    · exact (hstay _ hactive hs hsNe _ _ hhead htail hpb hpa).symm

/-- The account read before Cut leaves the name map and incidences
unchanged. Cutting the exposed state therefore removes the same name
and retains the relation on the surviving forest. -/
theorem TreeEditNamedSlots.cut_exposed {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {e : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (he : e ∈ G.E) (hne : G.tail e ≠ G.head e) :
    let exposed := lctExpose pathPayload s (slot e)
    let next := lctCut pathPayload exposed (vid (G.tail e)) (vid (G.head e))
    ∃ nextTrees nextDepth, LctInvWith pathPayload next nextTrees (slot e :: free) nextDepth ∧
      TreeEditNamedSlots next nextTrees { G with E := G.E.erase e } slot name := by
  dsimp only
  obtain ⟨ts, hInv, hNamed, _⟩ := hn.expose hi he
  exact hNamed.cut hInv hv he hne

/-- Linking a fresh edge extends the live relation by binding its name
to the free-head slot. All existing name bindings remain valid. -/
theorem TreeEditNamedSlots.link_oriented {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {e : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (he : e ∉ G.E) (ht : G.tail e < s.n) (hh : G.head e < s.n)
    (hd : ¬ pathTreeConnected s (vid (G.tail e)) (vid (G.head e))) (value : PathEdgeValue) (forward : Bool) :
    let u := if forward then G.tail e else G.head e
    let v := if forward then G.head e else G.tail e
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ nextTrees nextFree nextDepth, LctInvWith pathPayload next nextTrees nextFree nextDepth ∧
      TreeEditNamedSlots next nextTrees { G with E := insert e G.E }
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) := by
  intro u v next
  have hu : u < s.n := by
    cases forward <;> assumption
  have hv' : v < s.n := by
    cases forward <;> assumption
  have hswap : ¬ pathTreeConnected s (vid (G.head e)) (vid (G.tail e)) := by
    intro hc
    exact hd ((pathTreeConnected_iff_induced_roots hi ht hh).mpr
      ((pathTreeConnected_iff_induced_roots hi hh ht).mp hc).symm)
  have hd' : ¬ pathTreeConnected s (vid u) (vid v) := by
    cases forward
    · exact hswap
    · exact hd
  have hvertex (v : ℕ) (hb : v < s.n) : isVertex s.n (vid v) := by unfold isVertex vid; omega
  have hfreeNZ := treeEdit_freeHead_of_disconnected ⟨trees, free, depth, hi⟩ ht hh hd
  have hfree : s.freeHead ∈ free := by
    cases free with
    | nil => exact (hfreeNZ hi.freeListInv).elim
    | cons k rest => rw [hi.freeListInv.2.1]; exact List.mem_cons_self
  have hfreeSlot := hi.freeValid _ hfree
  have hfreeInactive : s.freeHead ∉ trees.flatMap AuxTree.toList :=
    fun hm => ((hi.partitionSlots _ hfreeSlot).mp hm) hfree
  obtain ⟨nextTrees, nextFree, nextDepth, hnext, hp, hhead, htail, hstay⟩ :=
    treeEdit_link_preserves_endpoints hi hu hv' hd' value
  have hnSize : next.n = s.n := by
    cases forward
    · exact treeEditApply_n G { G with tail := G.head, head := G.tail } (fun _ => value) s (.insert e)
    · exact treeEditApply_n G G (fun _ => value) s (.insert e)
  refine ⟨nextTrees, nextFree, nextDepth, hnext, ⟨?_, ?_, ?_⟩⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [Function.update_self, Function.update_self]
      exact ⟨hp.mem_iff.mpr List.mem_cons_self, hnSize.symm ▸ hfreeSlot, rfl⟩
    · obtain ⟨hactive, hs, hname⟩ := hn.forward f hf
      have hne : slot f ≠ s.freeHead := fun eq => hfreeInactive (eq ▸ hactive)
      have hfne : f ≠ e := fun eq => he (eq ▸ hf)
      rw [Function.update_of_ne hfne, Function.update_of_ne hne]
      exact ⟨hp.mem_iff.mpr (List.mem_cons_of_mem _ hactive), hnSize.symm ▸ hs, hname⟩
  · intro k hk hs
    rcases List.mem_cons.mp (hp.mem_iff.mp hk) with rfl | hkOld
    · simp
    · obtain ⟨hmem, hslot⟩ := hn.inverse k hkOld (hnSize ▸ hs)
      have hne : k ≠ s.freeHead := fun eq => hfreeInactive (eq ▸ hkOld)
      have hnameNe : name k ≠ e := fun eq => he (eq ▸ hmem)
      rw [Function.update_of_ne hne, Function.update_of_ne hnameNe]
      exact ⟨Finset.mem_insert.mpr (Or.inr hmem), hslot⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · cases forward
      · exact Or.inl ⟨by simpa [u, v, next] using hhead, by simpa [u, v, next] using htail⟩
      · exact Or.inr ⟨by simpa [u, v, next] using hhead, by simpa [u, v, next] using htail⟩
    · obtain ⟨ha, hs, _⟩ := hn.forward f hf
      have hne : f ≠ e := fun eq => he (eq ▸ hf)
      have ht' := hvertex _ (hv f hf).1
      have hh' := hvertex _ (hv f hf).2
      rcases hn.endpoints f hf with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
      · simpa only [Function.update_of_ne hne] using hstay _ ha hs _ _ ht' hh' hpa hpb
      · simpa only [Function.update_of_ne hne] using (hstay _ ha hs _ _ hh' ht' hpb hpa).symm

/-- Link in the fixed tail-to-head order. -/
theorem TreeEditNamedSlots.link {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {e : ℕ}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (he : e ∉ G.E) (ht : G.tail e < s.n) (hh : G.head e < s.n)
    (hd : ¬ pathTreeConnected s (vid (G.tail e)) (vid (G.head e))) (value : PathEdgeValue) :
    let next := lctLink pathPayload s (vid (G.tail e)) (vid (G.head e)) (some value)
    ∃ nextTrees nextFree nextDepth, LctInvWith pathPayload next nextTrees nextFree nextDepth ∧
      TreeEditNamedSlots next nextTrees { G with E := insert e G.E }
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) :=
  hn.link_oriented hi hv he ht hh hd value true

/-- The named relation depends only on live edge names and their endpoints. -/
theorem TreeEditNamedSlots.congrGraph {s : PathTreeState} {trees : List AuxTree}
    {G H : MGraph} {slot name : ℕ → ℕ} (hn : TreeEditNamedSlots s trees G slot name)
    (hE : H.E = G.E) (hends : ∀ f ∈ H.E, H.tail f = G.tail f ∧ H.head f = G.head f) :
    TreeEditNamedSlots s trees H slot name := by
  refine ⟨fun e he => hn.forward e (hE ▸ he), ?_, ?_⟩
  · intro k hk hs
    obtain ⟨hm, hf⟩ := hn.inverse k hk hs
    exact ⟨hE.symm ▸ hm, hf⟩
  · intro e he
    obtain ⟨ht, hh⟩ := hends e he
    simpa only [ht, hh] using hn.endpoints e (hE ▸ he)

/-- A level-zero batch retains the endpoints of any name that it
neither inserts nor moves by a split. -/
theorem treeEdit_batch_preserves_endpoints (G : MGraph) (U : List Update) (e : ℕ)
    (h : ∀ u ∈ U, match u with
      | .insert f _ _ => e ≠ f
      | .delete _ => True
      | .split _ _ _ _ => False) :
    (G.applyBatch U).tail e = G.tail e ∧ (G.applyBatch U).head e = G.head e := by
  induction U generalizing G with
  | nil => exact ⟨rfl, rfl⟩
  | cons u rest ih =>
    have hrest := ih (G.applyUpdate u) (fun f hf => h f (List.mem_cons_of_mem u hf))
    have hu := h u List.mem_cons_self
    change ((G.applyUpdate u).applyBatch rest).tail e = G.tail e ∧
      ((G.applyUpdate u).applyBatch rest).head e = G.head e
    cases u with
    | delete f => exact hrest
    | insert f a b =>
      change e ≠ f at hu
      simpa only [MGraph.applyUpdate, Function.update_of_ne hu] using hrest
    | split v v' St Sh => exact hu.elim

/-- Forests of the old and new level-zero graphs agree at shared
names if the batch has no splits and all its insertions are fresh. -/
theorem treeEdit_subgraphs_batch_endpoints {G F F' : MGraph} {U : List Update}
    (hOld : G.IsSubgraph F) (hNew : (G.applyBatch U).IsSubgraph F')
    (h : ∀ u ∈ U, match u with
      | .insert f _ _ => f ∉ G.E
      | .delete _ => True
      | .split _ _ _ _ => False) :
    ∀ e ∈ F.E, e ∈ F'.E → F.tail e = F'.tail e ∧ F.head e = F'.head e := by
  intro e he he'
  have hroot := hOld.2.1 he
  have heOld := hOld.2.2 e he
  have heNew := hNew.2.2 e he'
  obtain ⟨ht, hh⟩ := treeEdit_batch_preserves_endpoints G U e (by
    intro u hu
    have hkind := h u hu
    cases u with
    | insert f a b => exact fun heq => hkind (heq ▸ hroot)
    | delete f => trivial
    | split v v' St Sh => exact hkind)
  exact ⟨heOld.1.trans (ht.symm.trans heNew.1.symm),
    heOld.2.trans (hh.symm.trans heNew.2.symm)⟩

/-- The translated IPM refresh preserves common edge names in the
old and new chain trees. Freshness rules out replacement by an
insertion, and splits occur only at higher levels. -/
theorem treeEdit_translated_refresh_endpoints {extG intG F F' : MGraph}
    {f g : ℕ → ℕ} {next extCap : ℕ} {U : List Update}
    (hfresh : FreshInv extG intG f g next) (hValid : extG.BatchIsValid U)
    (hRecords : ∀ u ∈ U, FreshRecordFits extCap u)
    (hOld : intG.IsSubgraph F)
    (hNew : (intG.applyBatch (translateBatch extG f g next U).2.2.2.2).IsSubgraph F') :
    ∀ e ∈ F.E, e ∈ F'.E → F.tail e = F'.tail e ∧ F.head e = F'.head e := by
  have hpres := translateBatch_preserves U extG intG f g next hfresh hValid
  have hnoSplit := translateBatch_fixed_records U hRecords extG f g next
  generalize hEq : translateBatch extG f g next U = output at hpres hnoSplit hNew
  rcases output with ⟨ext', f', g', next', U'⟩
  have hno := hpres.2.2.2.1
  apply treeEdit_subgraphs_batch_endpoints hOld hNew
  intro u hu
  cases u with
  | insert e a b => exact fun he => hno e he _ hu (by constructor)
  | delete e => trivial
  | split v v' St Sh => exact hnoSplit v v' St Sh hu

/-- Rebuilding a suffix keeps its starting graph and all earlier graphs. -/
theorem treeEdit_rebuildSuffix_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (len grad : ℕ → ℝ) (rem idx : ℕ)
    (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd enc dec fwd : ℕ → ℕ)
    (j : ℕ) (hj : j ≤ idx) :
    (rebuildSuffix T L P lvlM N₀ len grad rem idx G sc bran upd enc dec fwd).1 j = G j := by
  induction rem generalizing idx G sc bran upd enc dec fwd with
  | zero => rfl
  | succ rem ih =>
    rw [rebuildSuffix]
    rw [ih _ _ _ _ _ _ _ _ (hj.trans (Nat.le_succ _))]
    simp [show j ≠ idx + 1 by omega]

private theorem treeEdit_rebuild_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i j : ℕ) (hi : i ≤ P.d) (hj : j ≤ i)
    (Gnew : MGraph) (enc : ℕ) :
    (algorithm1_rebuild T L P st i Gnew enc).1.G j = if j = i then Gnew else st.G j := by
  unfold algorithm1_rebuild
  split
  · dsimp only
    rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj]
  · have he : i = P.d := by omega
    simp [he]

/-- Algorithm 1's Rebuild changes level zero only when rebuilding
it from a new input graph (page 20). -/
theorem treeEdit_rebuild_base (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i ≤ P.d)
    (Gnew : MGraph) (enc : ℕ) :
    (algorithm1_rebuild T L P st i Gnew enc).1.G 0 = if 0 = i then Gnew else st.G 0 :=
  treeEdit_rebuild_prefix T L P st i 0 hi (Nat.zero_le i) Gnew enc

/-- Algorithm 1's Shift retains the original level-zero graph,
even if the restarted spanner changes its output (page 20). -/
theorem treeEdit_shift_base (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) :
    (algorithm1_shift T L P st i).1.G 0 = st.G 0 := by
  unfold algorithm1_shift
  split
  · dsimp only
    rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.zero_le _)]
    simp
  · rfl

/-- The prefix of Algorithm 1 Shift (page 20) retains the graphs
through the shifted level and supplies the restarted sparsifier as
the next graph. Deeper rebuilds preserve this input graph. -/
theorem algorithm1_shift_graph_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i j : ℕ) (hi : i < P.d) (hj : j ≤ i + 1) :
    let branch := (st.bran i + 1) % P.k
    (algorithm1_shift T L P st i).1.G j =
      if j = i + 1 then T.S (T.restart (st.scState i) branch) branch else st.G j := by
  simp only [algorithm1_shift, hi, dite_true]
  rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj]

/-- A suffix rebuild leaves earlier sparse-core states in place. -/
theorem rebuildSuffix_state_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (len grad : ℕ → ℝ) (rem idx : ℕ)
    (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd enc dec fwd : ℕ → ℕ)
    (j : ℕ) (hj : j < idx) :
    (rebuildSuffix T L P lvlM N₀ len grad rem idx G sc bran upd enc dec fwd).2.1 j = sc j := by
  induction rem generalizing idx G sc bran upd enc dec fwd with
  | zero => rfl
  | succ rem ih =>
    rw [rebuildSuffix]
    rw [ih _ _ _ _ _ _ _ _ (hj.trans (Nat.lt_succ_self _))]
    simp [Nat.ne_of_lt hj]

/-- The suffix rebuild in Algorithm 1 Shift (page 20) preserves the
restarted core at the shifted level and all earlier sparse-core states. -/
theorem algorithm1_shift_core_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i j : ℕ) (hi : i < P.d) (hj : j ≤ i) :
    let branch := (st.bran i + 1) % P.k
    (algorithm1_shift T L P st i).1.scState j =
      if j = i then T.restart (st.scState i) branch else st.scState j := by
  simp only [algorithm1_shift, hi, dite_true]
  rw [rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.lt_succ_of_le hj)]

private theorem treeEdit_updateLoop_prefix (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N : ℕ) (len grad : ℕ → ℝ) (rem idx : ℕ)
    (st : ChainState T P) (G : MGraph) (U : List Update) (enc j : ℕ)
    (hlevels : idx + rem = P.d) (hj : j ≤ idx) :
    (updateLoop T L TP P N len grad rem idx st G U enc).1.G j =
      if j = idx then G else st.G j := by
  induction rem generalizing idx st G U enc with
  | zero =>
    have he : idx = P.d := by simpa using hlevels
    subst idx
    rw [updateLoop]
    split <;> rfl
  | succ rem ih =>
    rw [updateLoop]
    split
    · exact treeEdit_rebuild_prefix T L P _ idx j (by omega) hj G enc
    · dsimp only
      rw [ih _ _ _ _ _ (by omega) (by omega)]
      simp [show j ≠ idx + 1 by omega]

/-- Algorithm 1's Update applies the incoming batch at level zero.
The higher-level propagation and rebuilds retain that graph (page 21). -/
theorem treeEdit_update_base (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N : ℕ) (st : ChainState T P)
    (U : List Update) (grad len : ℕ → ℝ) :
    (algorithm1_update T L TP P N st U grad len).1.G 0 = (st.G 0).applyBatch U := by
  unfold algorithm1_update
  dsimp only
  rw [treeEdit_updateLoop_prefix T L TP P N _ _ _ _ _ _ _ _ _ (by simp) (Nat.zero_le _)]
  simp

/-- The old and new chain trees of an Algorithm 1 update agree on
shared edge endpoints for a translated IPM refresh (page 21). -/
theorem treeEdit_refresh_chain_endpoints (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N : ℕ) (st : ChainState T P)
    {extG : MGraph} {f g : ℕ → ℕ} {next extCap : ℕ} {U : List Update}
    (grad len : ℕ → ℝ)
    (hfresh : FreshInv extG (st.G 0) f g next) (hValid : extG.BatchIsValid U)
    (hRecords : ∀ u ∈ U, FreshRecordFits extCap u)
    (hOld : (st.G 0).IsSubgraph st.toTreeChain.chainTree)
    (hNew : let after := (algorithm1_update T L TP P N st
        (translateBatch extG f g next U).2.2.2.2 grad len).1
      (after.G 0).IsSubgraph after.toTreeChain.chainTree) :
    let after := (algorithm1_update T L TP P N st
      (translateBatch extG f g next U).2.2.2.2 grad len).1
    ∀ e ∈ st.toTreeChain.chainTree.E, e ∈ after.toTreeChain.chainTree.E →
      st.toTreeChain.chainTree.tail e = after.toTreeChain.chainTree.tail e ∧
      st.toTreeChain.chainTree.head e = after.toTreeChain.chainTree.head e := by
  dsimp only at hNew ⊢
  rw [treeEdit_update_base] at hNew
  exact treeEdit_translated_refresh_endpoints hfresh hValid hRecords hOld hNew

/-- Definition 5.8 (page 20) takes all chain-tree endpoints from
level zero, so a transition that retains that graph retains endpoints. -/
theorem treeEdit_chain_endpoints_of_base {T : SparseCoreRestartTool} {P : ChainParams}
    {before after : ChainState T P} (hbase : after.G 0 = before.G 0) (e : ℕ) :
    before.toTreeChain.chainTree.tail e = after.toTreeChain.chainTree.tail e ∧
    before.toTreeChain.chainTree.head e = after.toTreeChain.chainTree.head e := by
  simp [TreeChain.chainTree, ChainState.toTreeChain, hbase]

/-- Shift returns exactly the symmetric difference of its chain trees,
whose endpoints agree because Shift retains level zero (page 20). -/
theorem treeEdit_shift_diff (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) :
    let result := algorithm1_shift T L P st i
    result.2 = diffTreeChanges st.toTreeChain.chainTree.E result.1.toTreeChain.chainTree.E ∧
    ∀ e, st.toTreeChain.chainTree.tail e = result.1.toTreeChain.chainTree.tail e ∧
      st.toTreeChain.chainTree.head e = result.1.toTreeChain.chainTree.head e := by
  dsimp only
  refine ⟨?_, treeEdit_chain_endpoints_of_base (treeEdit_shift_base T L P st i)⟩
  unfold algorithm1_shift
  split <;> rfl

/-- A Rebuild above level zero returns exactly the symmetric difference
of its chain trees and preserves their endpoint assignment (page 20). -/
theorem treeEdit_rebuild_diff (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i ≤ P.d)
    (Gnew : MGraph) (enc : ℕ) (hbase : i ≠ 0 ∨ Gnew = st.G 0) :
    let result := algorithm1_rebuild T L P st i Gnew enc
    result.2 = diffTreeChanges st.toTreeChain.chainTree.E result.1.toTreeChain.chainTree.E ∧
    ∀ e, st.toTreeChain.chainTree.tail e = result.1.toTreeChain.chainTree.tail e ∧
      st.toTreeChain.chainTree.head e = result.1.toTreeChain.chainTree.head e := by
  dsimp only
  have hG := treeEdit_rebuild_base T L P st i hi Gnew enc
  have he : (algorithm1_rebuild T L P st i Gnew enc).1.G 0 = st.G 0 := by
    rw [hG]
    rcases hbase with hn | hsame
    · exact ite_eq_right (Ne.symm hn)
    · simp [hsame]
  refine ⟨?_, treeEdit_chain_endpoints_of_base he⟩
  unfold algorithm1_rebuild
  split <;> rfl

/-- Update returns the exact symmetric difference after its last
propagation or rebuild step (Algorithm 1, page 21). -/
theorem treeEdit_update_diff (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N : ℕ) (st : ChainState T P)
    (U : List Update) (grad len : ℕ → ℝ) :
    let result := algorithm1_update T L TP P N st U grad len
    result.2 = diffTreeChanges st.toTreeChain.chainTree.E result.1.toTreeChain.chainTree.E := by
  rfl

/-- A shared endpoint assignment exists exactly when common live
names agree. It uses the old assignment on old names and the new
assignment on newly inserted names. -/
theorem treeEdit_shared_endpoints_iff (oldG newG : MGraph) :
    (∃ ambient : MGraph,
      (∀ e ∈ oldG.E, ambient.tail e = oldG.tail e ∧ ambient.head e = oldG.head e) ∧
      (∀ e ∈ newG.E, ambient.tail e = newG.tail e ∧ ambient.head e = newG.head e)) ↔
    (∀ e ∈ oldG.E, e ∈ newG.E → oldG.tail e = newG.tail e ∧ oldG.head e = newG.head e) := by
  constructor
  · rintro ⟨_, ho, hn⟩ e heOld heNew
    exact ⟨(ho e heOld).1.symm.trans (hn e heNew).1,
      (ho e heOld).2.symm.trans (hn e heNew).2⟩
  · intro hs
    let ambient : MGraph :=
      { V := oldG.V ∪ newG.V, E := oldG.E ∪ newG.E
        tail := fun e => if e ∈ oldG.E then oldG.tail e else newG.tail e
        head := fun e => if e ∈ oldG.E then oldG.head e else newG.head e }
    refine ⟨ambient, ?_, ?_⟩
    · intro e he
      simp [ambient, he]
    · intro e he
      by_cases heOld : e ∈ oldG.E
      · simpa [ambient, heOld] using hs e heOld he
      · simp [ambient, heOld]

/-- The named intermediate state of the ordered edit fold. The graph
supplies endpoints for both the original edge names and the new ones. -/
@[expose] def TreeEditNamedPrefix (current : PathTreeState) (oldG newG ambient : MGraph)
    (remaining : List TreeChange) (slot name : ℕ → ℕ) : Prop :=
  ∃ processed trees free depth,
    TreeEditDifference oldG.E newG.E (processed ++ remaining) ∧
    LctInvWith pathPayload current trees free depth ∧
    TreeEditNamedSlots current trees { ambient with E := applyTreeChanges oldG.E processed } slot name ∧
    ∀ f ∈ applyTreeChanges oldG.E processed, ambient.tail f < current.n ∧ ambient.head f < current.n

/-- The named intermediate forest includes a structural link-cut witness. -/
theorem TreeEditNamedPrefix.lctInv {current : PathTreeState} {oldG newG ambient : MGraph}
    {edits : List TreeChange} {slot name : ℕ → ℕ}
    (hp : TreeEditNamedPrefix current oldG newG ambient edits slot name) :
    LctInv pathPayload current := by
  obtain ⟨_, trees, free, depth, _, hi, _, _⟩ := hp
  exact ⟨trees, free, depth, hi⟩

/-- Before the first edit, the named relation represents exactly the old graph. -/
theorem TreeEditNamedPrefix.start {oldG newG ambient : MGraph} {initial : PathTreeState}
    {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ} {slot name : ℕ → ℕ}
    (hi : LctInvWith pathPayload initial trees free depth)
    (hn : TreeEditNamedSlots initial trees oldG slot name)
    (hOld : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f)
    (hv : ∀ f ∈ oldG.E, ambient.tail f < initial.n ∧ ambient.head f < initial.n) :
    TreeEditNamedPrefix initial oldG newG ambient
      (diffTreeChanges oldG.E newG.E) slot name :=
  ⟨[], trees, free, depth, treeEditDifference_model _ _, hi, hn.congrGraph rfl hOld, hv⟩

/-- The ordered edit fold can start from two forests that agree on
their common edge names. Their endpoint bounds transfer to the
shared assignment used by the intermediate forest. -/
theorem TreeEditNamedPrefix.start_shared {oldG newG : MGraph} {initial : PathTreeState}
    {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ} {slot name : ℕ → ℕ}
    (changes : List TreeChange)
    (hchanges : TreeEditDifference oldG.E newG.E changes)
    (hi : LctInvWith pathPayload initial trees free depth)
    (hn : TreeEditNamedSlots initial trees oldG slot name)
    (hCommon : ∀ e ∈ oldG.E, e ∈ newG.E → oldG.tail e = newG.tail e ∧ oldG.head e = newG.head e)
    (hvOld : ∀ f ∈ oldG.E, oldG.tail f < initial.n ∧ oldG.head f < initial.n)
    (hvNew : ∀ f ∈ newG.E, newG.tail f < initial.n ∧ newG.head f < initial.n) :
    ∃ ambient : MGraph,
      (∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f) ∧
      (∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f) ∧
      (∀ f ∈ newG.E, ambient.tail f < initial.n ∧ ambient.head f < initial.n) ∧
      TreeEditNamedPrefix initial oldG newG ambient changes slot name := by
  obtain ⟨ambient, ho, hnew⟩ := (treeEdit_shared_endpoints_iff oldG newG).mpr hCommon
  have holdBound : ∀ f ∈ oldG.E, ambient.tail f < initial.n ∧ ambient.head f < initial.n := by
    intro f hf
    rw [(ho f hf).1, (ho f hf).2]
    exact hvOld f hf
  have hnewBound : ∀ f ∈ newG.E, ambient.tail f < initial.n ∧ ambient.head f < initial.n := by
    intro f hf
    rw [(hnew f hf).1, (hnew f hf).2]
    exact hvNew f hf
  refine ⟨ambient, ho, hnew, hnewBound, ?_⟩
  exact ⟨[], trees, free, depth, hchanges, hi, hn.congrGraph rfl ho, holdBound⟩

/-- Extend the named relation over one change. Deletions use the old
endpoints. At an insertion the processed graph is a subforest of the
target, so the slot relation makes the two endpoints disconnected. -/
theorem TreeEditNamedPrefix.advance_oriented {oldG newG ambient : MGraph}
    {current : PathTreeState} {value : ℕ → PathEdgeValue}
    {edit : TreeChange} {remaining : List TreeChange} {slot name : ℕ → ℕ}
    (forward : ℕ → Bool)
    (hp : TreeEditNamedPrefix current oldG newG ambient (edit :: remaining) slot name)
    (hOldForest : oldG.IsForest) (hNewForest : newG.IsForest)
    (hOld : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f)
    (hNew : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (hvb : ∀ f ∈ newG.E, ambient.tail f < current.n ∧ ambient.head f < current.n) :
    let oriented := { newG with
      tail := fun e => if forward e then newG.tail e else newG.head e
      head := fun e => if forward e then newG.head e else newG.tail e }
    TreeEditNamedPrefix (treeEditApply oldG oriented value current edit)
      oldG newG ambient remaining
      (match edit with | .delete _ => slot | .insert e => Function.update slot e current.freeHead)
      (match edit with | .delete _ => name | .insert e => Function.update name current.freeHead e) := by
  intro oriented
  obtain ⟨done, trees, free, depth, hd, hi, hn, hv⟩ := hp
  have hsplit : TreeEditDifference oldG.E newG.E ((done ++ [edit]) ++ remaining) := by
    simpa only [List.append_assoc, List.singleton_append] using hd
  have hsize := treeEditApply_n oldG oriented value current edit
  have hchange : edit ∈ diffTreeChanges oldG.E newG.E := hd.perm.mem_iff.mp (by simp)
  cases edit with
  | delete e =>
    have hOldMem := (Finset.mem_sdiff.mp (treeEdit_delete_mem_diff.mp hchange)).1
    have he := hd.delete_live rfl
    obtain ⟨ht, hh⟩ := hOld e hOldMem
    have hne := LSF.isForest_no_selfLoop hOldForest hOldMem
    obtain ⟨ts, ds, hInv, hNamed⟩ := hn.cut hi hv he (by simpa only [ht, hh] using hne)
    simp only [ht, hh] at hInv hNamed
    have hset : applyTreeChanges oldG.E (done ++ [.delete e]) =
        (applyTreeChanges oldG.E done).erase e := by
      unfold applyTreeChanges
      rw [List.foldl_append]
      rfl
    refine ⟨done ++ [.delete e], ts, slot e :: free, ds, hsplit, hInv, ?_, ?_⟩
    · simpa only [hset, treeEditApply, vid, oriented] using hNamed
    · intro f hf
      rw [hset] at hf
      rw [hsize]
      exact hv f (Finset.mem_erase.mp hf).2
  | insert e =>
    have hNewMem := (Finset.mem_sdiff.mp (treeEdit_insert_mem_diff.mp hchange)).1
    obtain ⟨ht, hh⟩ := hNew e hNewMem
    obtain ⟨hvt, hvh⟩ := hvb e hNewMem
    obtain ⟨hsub, he, _⟩ := hd.insert_cursor rfl
    let part := { newG with E := applyTreeChanges oldG.E done }
    have hRel : TreeEditNamedSlots current trees part slot name :=
      hn.congrGraph rfl (fun f hf => ⟨(hNew f (hsub hf)).1.symm, (hNew f (hsub hf)).2.symm⟩)
    have hvPart : ∀ f ∈ part.E, part.tail f < current.n ∧ part.head f < current.n := by
      intro f hf
      obtain ⟨ha, hb⟩ := hNew f (hsub hf)
      simpa only [ha, hb] using hv f hf
    have ht' : newG.tail e < current.n := ht ▸ hvt
    have hh' : newG.head e < current.n := hh ▸ hvh
    have hdGraph : ¬ part.Connected (newG.tail e) (newG.head e) :=
      treeEdit_link_disconnected hNewForest ⟨fun _ h => h, hsub, fun _ _ => ⟨rfl, rfl⟩⟩ hNewMem he
    have hdisc : ¬ pathTreeConnected current (vid (newG.tail e)) (vid (newG.head e)) :=
      fun hc => hdGraph (pathTreeConnected_to_namedGraph hi ht' hh' (hRel.parent_edge hi hvPart) hc)
    obtain ⟨ts, fs, ds, hInv, hNamed⟩ :=
      hn.link_oriented hi hv he hvt hvh (by simpa only [ht, hh] using hdisc) (value e) (forward e)
    simp only [ht, hh] at hInv hNamed
    have hset : applyTreeChanges oldG.E (done ++ [.insert e]) =
        insert e (applyTreeChanges oldG.E done) := by
      unfold applyTreeChanges
      rw [List.foldl_append]
      rfl
    refine ⟨done ++ [.insert e], ts, fs, ds, hsplit, hInv, ?_, ?_⟩
    · simpa only [hset, treeEditApply, vid, oriented] using hNamed
    · intro f hf
      rw [hset] at hf
      rw [hsize]
      exact (Finset.mem_insert.mp hf).elim (fun h => h.symm ▸ hvb e hNewMem) (hv f)

/-- Advance in the fixed tail-to-head order. -/
theorem TreeEditNamedPrefix.advance {oldG newG ambient : MGraph}
    {current : PathTreeState} {value : ℕ → PathEdgeValue}
    {edit : TreeChange} {remaining : List TreeChange} {slot name : ℕ → ℕ}
    (hp : TreeEditNamedPrefix current oldG newG ambient (edit :: remaining) slot name)
    (hOldForest : oldG.IsForest) (hNewForest : newG.IsForest)
    (hOld : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f)
    (hNew : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (hvb : ∀ f ∈ newG.E, ambient.tail f < current.n ∧ ambient.head f < current.n) :
    TreeEditNamedPrefix (treeEditApply oldG newG value current edit)
      oldG newG ambient remaining
      (match edit with | .delete _ => slot | .insert e => Function.update slot e current.freeHead)
      (match edit with | .delete _ => name | .insert e => Function.update name current.freeHead e) :=
  hp.advance_oriented (value := value) (fun _ => true) hOldForest hNewForest hOld hNew hvb

/-- A pending insertion joins two different trees in the represented forest. -/
theorem TreeEditNamedPrefix.insert_disconnected {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.insert e :: rest) slot name)
    (hforest : newG.IsForest)
    (hEnds : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (htail : newG.tail e < current.n) (hhead : newG.head e < current.n) :
    ¬ pathTreeConnected current (vid (newG.tail e)) (vid (newG.head e)) := by
  obtain ⟨done, ts, fs, ds, hsplit, hstruct, hnamed, hbounds⟩ := hp
  obtain ⟨hsub, hmissing, htarget⟩ := hsplit.insert_cursor rfl
  let part := { newG with E := applyTreeChanges oldG.E done }
  have hRel : TreeEditNamedSlots current ts part slot name :=
    hnamed.congrGraph rfl fun f hf =>
      ⟨(hEnds f (hsub hf)).1.symm, (hEnds f (hsub hf)).2.symm⟩
  have hvPart : ∀ f ∈ part.E, part.tail f < current.n ∧ part.head f < current.n := by
    intro f hf
    obtain ⟨ha, hb⟩ := hEnds f (hsub hf)
    simpa only [ha, hb] using hbounds f hf
  have hdisjoint : ¬ part.Connected (newG.tail e) (newG.head e) :=
    treeEdit_link_disconnected hforest ⟨fun _ h => h, hsub, fun _ _ => ⟨rfl, rfl⟩⟩ htarget hmissing
  exact fun hc => hdisjoint (pathTreeConnected_to_namedGraph hstruct htail hhead
    (hRel.parent_edge hstruct hvPart) hc)

/-- The deletion cursor names an active edge slot, so its account can be exposed. -/
theorem TreeEditNamedPrefix.delete_slot_active {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name) :
    pathTreeActive current (slot e) ∧ isEdgeSlot current.n (slot e) := by
  obtain ⟨done, trees, free, depth, hd, hi, hn, _⟩ := hp
  obtain ⟨hmem, hslot, _⟩ := hn.forward e (hd.delete_live rfl)
  exact ⟨⟨trees, free, depth, hi, hmem⟩, hslot⟩

/-- An evaluated account for the old-only name determines the value copied by Cut.
The account is in the current tree orientation, as returned by Expose. -/
theorem TreeEditNamedPrefix.delete_expose_value {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    {value : PathEdgeValue}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name)
    (hAccount : ∀ ts fs ds, LctInvWith pathPayload current ts fs ds →
      (slot e, some value) ∈ forestPairs pathPayload current.splay ts) :
    ((lctExpose pathPayload current (slot e)).splay.nodes (slot e)).val = some value := by
  obtain ⟨_, ts, fs, ds, _, hi, _, _⟩ := hp
  exact pathTreeExpose_value_of_forestPair hi (hAccount ts fs ds hi)

/-- The current deletion uses an old-only name. -/
theorem TreeEditNamedPrefix.delete_old_only {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name) :
    e ∈ oldG.E \ newG.E := by
  obtain ⟨_, _, _, _, hd, _⟩ := hp
  exact hd.delete_mem_sdiff (by simp)

/-- No pending insertion uses the name at the deletion cursor. -/
theorem TreeEditNamedPrefix.insert_ne_delete {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e j : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name)
    (hj : TreeChange.insert j ∈ rest) : j ≠ e := by
  have hOld := (Finset.mem_sdiff.mp hp.delete_old_only).1
  obtain ⟨done, _, _, _, hd, _⟩ := hp
  have hj' := hd.insert_mem_sdiff (List.mem_append_right done (List.mem_cons_of_mem _ hj))
  exact fun he => (Finset.mem_sdiff.mp hj').2 (he.symm ▸ hOld)

/-- The deletion cursor is distinct from all deletion names in its suffix. -/
theorem TreeEditNamedPrefix.delete_ne_pending {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e j : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name)
    (hj : TreeChange.delete j ∈ rest) : j ≠ e := by
  obtain ⟨done, _, _, _, hd, _⟩ := hp
  have hnd := hd.perm.nodup_iff.mpr (treeEdit_diff_nodup oldG.E newG.E).1
  exact fun h => (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (h ▸ hj)

/-- Once an insertion reaches the cursor, no deletion remains. -/
theorem TreeEditNamedPrefix.no_delete_after_insert {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e j : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.insert e :: rest) slot name) :
    TreeChange.delete j ∉ rest := by
  obtain ⟨_, _, _, _, hd, _⟩ := hp
  exact hd.no_delete_after_insert

/-- Insertion leaves forward bindings for deletion names unchanged. -/
theorem TreeEditNamedPrefix.keep_delete_slots {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name initial : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.insert e :: rest) slot name)
    (hs : ∀ f ∈ oldG.E \ newG.E, slot f = initial f) :
    ∀ f ∈ oldG.E \ newG.E, Function.update slot e current.freeHead f = initial f := by
  obtain ⟨_, _, _, _, hd, _⟩ := hp
  exact hd.update_slot_of_insert (by simp) hs

/-- The named deletion cursor makes exactly its edge account newly saved. -/
theorem TreeEditNamedPrefix.savedNames_delete {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {rest : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name) :
    treeEditSavedNames oldG.E newG.E rest =
      insert e (treeEditSavedNames oldG.E newG.E (.delete e :: rest)) := by
  obtain ⟨_, _, _, _, hd, _⟩ := hp
  exact hd.savedNames_delete

/-- Reading an account before deleting its edge preserves the current
prefix relation and keeps the pending deletion at the cursor. -/
theorem TreeEditNamedPrefix.expose_before_delete {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ} {e : ℕ} {remaining : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: remaining) slot name) :
    TreeEditNamedPrefix (lctExpose pathPayload current (slot e)) oldG newG ambient
      (.delete e :: remaining) slot name := by
  obtain ⟨done, trees, free, depth, hd, hi, hn, hv⟩ := hp
  have he := hd.delete_live rfl
  obtain ⟨ts, hInv, hNamed, _⟩ := hn.expose hi he
  exact ⟨done, ts, free, depth, hd, hInv, hNamed, hv⟩

/-- The named forest supplies the structural precondition for reading a deleted account.
Fixed-point fit is supplied for both the current tree and the exposed tree. -/
theorem TreeEditNamedPrefix.delete_read_pre {w L constant handle heap : ℕ}
    {oldG newG ambient : MGraph} {current : PathTreeState} {slot name : ℕ → ℕ}
    {e : ℕ} {rest : List TreeChange} {fmt : Num.Format w}
    {mem : ℕ → ℕ} {allocation : ℕ → ℕ → List ℕ → ℕ}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name)
    (hf : pathTreeFits fmt.limbBits L current)
    (hw : 2 * current.n + 1 < 2 ^ w)
    (hwidth : Nat.log 2 (2 * current.n + 1) ≤ fmt.limbBits * L)
    (he : pathTreeFits fmt.limbBits L (lctExpose pathPayload current (slot e))) :
    (pathTreeMachineContract fmt L constant allocation).pre 4 current
      [handle, slot e, heap] mem :=
  ⟨hp.lctInv, hf, hw, hwidth, handle, slot e, heap, rfl, hp.delete_slot_active.1, he⟩

/-- Expose retains the named forest needed by Cut, and the endpoint word
checks are independent of the memory changes made while saving the account. -/
theorem TreeEditNamedPrefix.delete_cut_pre {w L constant handle base vc ec : ℕ}
    {oldG newG ambient : MGraph} {current : PathTreeState} {slot name : ℕ → ℕ}
    {e : ℕ} {rest : List TreeChange} {fmt : Num.Format w}
    {mem : ℕ → ℕ} {allocation : ℕ → ℕ → List ℕ → ℕ}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: rest) slot name)
    (hend : TreeEditEndpointAt mem base vc ec oldG e)
    (hvc : vc ≤ current.n) (hw : 2 * current.n + 1 < 2 ^ w)
    (hwidth : Nat.log 2 (2 * current.n + 1) ≤ fmt.limbBits * L)
    (he : pathTreeFits fmt.limbBits L (lctExpose pathPayload current (slot e)))
    (hc : pathTreeFits fmt.limbBits L (lctCut pathPayload (lctExpose pathPayload current (slot e))
      (oldG.tail e + 1) (oldG.head e + 1))) :
    ∀ ret after, (pathTreeMachineContract fmt L constant allocation).pre 1
      (lctExpose pathPayload current (slot e))
      [handle, oldG.tail e + 1, oldG.head e + 1, ret] after := by
  intro ret after
  have hu := hend.tailNameBound.trans_le hvc
  have hv := hend.headNameBound.trans_le hvc
  have hsize : (lctExpose pathPayload current (slot e)).n = current.n := rfl
  exact ⟨hp.expose_before_delete.lctInv, he, hw, hwidth, handle, oldG.tail e + 1,
    oldG.head e + 1, ret, rfl, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hc⟩

/-- The payload-saving Cut advances the named prefix by one edit.
Its preliminary Expose does not change which edge the deletion removes. -/
theorem TreeEditNamedPrefix.advance_exposed {oldG newG ambient : MGraph}
    {current : PathTreeState} {value : ℕ → PathEdgeValue} {slot name : ℕ → ℕ}
    {e : ℕ} {remaining : List TreeChange}
    (hp : TreeEditNamedPrefix current oldG newG ambient (.delete e :: remaining) slot name)
    (ho : oldG.IsForest) (hn : newG.IsForest)
    (hOld : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f)
    (hNew : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (hBound : ∀ f ∈ newG.E, ambient.tail f < current.n ∧ ambient.head f < current.n) :
    TreeEditNamedPrefix
      (treeEditApply oldG newG value (lctExpose pathPayload current (slot e)) (.delete e))
      oldG newG ambient remaining slot name :=
  hp.expose_before_delete.advance (value := value) ho hn hOld hNew hBound

/-- At the end of the list, the live slot relation represents the target forest. -/
theorem TreeEditNamedPrefix.finish {oldG newG ambient : MGraph}
    {current : PathTreeState} {slot name : ℕ → ℕ}
    (hp : TreeEditNamedPrefix current oldG newG ambient [] slot name)
    (hNew : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f) :
    ∃ trees free depth, LctInvWith pathPayload current trees free depth ∧
      TreeEditNamedSlots current trees newG slot name := by
  obtain ⟨done, trees, free, depth, hdone, hi, hn, _⟩ := hp
  rw [List.append_nil] at hdone
  have hE := hdone.result.2
  exact ⟨trees, free, depth, hi,
    hn.congrGraph hE.symm (fun f hf => ⟨(hNew f hf).1.symm, (hNew f hf).2.symm⟩)⟩

/-- Set up the edit loop from the old and new graph allocations and
the packed symmetric difference. Both graph layouts supply their
vertex bounds, and the input slot tables record the initial forest. -/
theorem treeEditFold_start {R : DSRep PathTreeState} {handle h L oldBase newBase vc oldCap newCap
    slots names edgeCap slotCap : ℕ} {x : R.τ} {st : State} {oldG newG : MGraph}
    {tree : PathTreeState} {ts : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    {slot name record : ℕ → ℕ} {value : ℕ → PathEdgeValue} {changes : List TreeChange}
    (hchanges : TreeEditDifference oldG.E newG.E changes)
    (hCommon : ∀ e ∈ oldG.E, e ∈ newG.E → oldG.tail e = newG.tail e ∧ oldG.head e = newG.head e)
    (hvc : vc ≤ tree.n)
    (hOld : DynGraphAt st.mem oldBase vc oldCap oldG)
    (hNew : DynGraphAt st.mem newBase vc newCap newG)
    (hOldBelow : oldBase + dynGraphSize vc oldCap ≤ st.regs 3)
    (hNewBelow : newBase + dynGraphSize vc newCap ≤ st.regs 3)
    (hOldOutside : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize vc oldCap → ¬ R.foot handle x a)
    (hNewOutside : ∀ a, newBase ≤ a → a < newBase + dynGraphSize vc newCap → ¬ R.foot handle x a)
    (hi : LctInvWith pathPayload tree ts free depth)
    (hn : TreeEditNamedSlots tree ts oldG slot name)
    (hTables : PathSlotTablesAt st.mem slots names edgeCap slotCap slot name)
    (hStorage : TreeEditSlotStorage R handle slots names edgeCap slotCap x (st.regs 3))
    (hHeap : TreeEditHeap R handle x st)
    (hPayload : TreeEditPayloads R handle h L x st changes record value)
    (hcount : st.regs 18 = (oldG.E \ newG.E).card + (newG.E \ oldG.E).card)
    (hrecords : TreeEditsAt st.mem (st.regs 6) changes)
    (hbelow : st.regs 6 + 2 * ((oldG.E \ newG.E).card + (newG.E \ oldG.E).card) ≤ st.regs 3)
    (houtside : ∀ a, st.regs 6 ≤ a →
      a < st.regs 6 + 2 * ((oldG.E \ newG.E).card + (newG.E \ oldG.E).card) →
      ¬ R.foot handle x a) :
    TreeEditBuffer R handle x st changes ∧
    TreeEditFoldReady R handle h L st oldBase newBase vc oldCap newCap
      slots names edgeCap slotCap oldG newG record value changes x st ∧
    ∃ ambient : MGraph,
      (∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f) ∧
      (∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f) ∧
      (∀ f ∈ newG.E, ambient.tail f < tree.n ∧ ambient.head f < tree.n) ∧
      ∃ f g, TreeEditNamedPrefix tree oldG newG ambient changes f g ∧
        PathSlotTablesAt st.mem slots names edgeCap slotCap f g := by
  have hvOld e (he : e ∈ oldG.E) : oldG.tail e < tree.n ∧ oldG.head e < tree.n := ⟨(hOld.2.1 _ (hOld.1 e he).1).trans_le hvc,
    (hOld.2.1 _ (hOld.1 e he).2).trans_le hvc⟩
  have hvNew e (he : e ∈ newG.E) : newG.tail e < tree.n ∧ newG.head e < tree.n := ⟨(hNew.2.1 _ (hNew.1 e he).1).trans_le hvc,
    (hNew.2.1 _ (hNew.1 e he).2).trans_le hvc⟩
  obtain ⟨ambient, ho, he, hv, hp⟩ :=
    TreeEditNamedPrefix.start_shared changes hchanges hi hn hCommon hvOld hvNew
  have hcountEq := hchanges.result.1
  have hwords := treeEditWords_length changes
  have hb : TreeEditBuffer R handle x st changes := ⟨hcount.trans hcountEq.symm, hrecords,
    by rw [hwords, hcountEq]; exact hbelow,
    by rw [hwords, hcountEq]; exact houtside⟩
  have hlook := TreeEditEndpointSuffix.of_diff hOld hNew
  have hg : TreeEditGraphs R handle x st oldBase newBase vc oldCap newCap oldG newG changes :=
    ⟨fun edit he => hlook edit (hchanges.perm.mem_iff.mp he),
      hOldBelow, hNewBelow, hOldOutside, hNewOutside⟩
  exact ⟨hb, ⟨fun _ _ => rfl, hHeap, hStorage, hg, hPayload⟩,
    ambient, ho, he, hv, slot, name, hp, hTables⟩

/-- Packing into a separate allocated buffer leaves the tree, its
potential, and the inverse slot tables ready for the edit fold. -/
theorem treeEditFold_frame_packed {R : DSRep PathTreeState}
    {handle slots names edgeCap slotCap : ℕ} {x : R.τ} {before after : State}
    {tree : PathTreeState} {slot name : ℕ → ℕ} {edits : List TreeChange}
    (hLocal : R.Local) (hRep : R.rep handle tree x before.mem)
    (hHeap : TreeEditHeap R handle x before)
    (hStorage : TreeEditSlotStorage R handle slots names edgeCap slotCap x (before.regs 3))
    (hTables : PathSlotTablesAt before.mem slots names edgeCap slotCap slot name)
    (hcount : after.regs 18 = edits.length)
    (hwords : TreeEditsAt after.mem (after.regs 6) edits)
    (hHeapReg : after.regs 3 = before.regs 3)
    (hbelow : after.regs 6 + 2 * edits.length ≤ before.regs 3)
    (houtside : ∀ a, after.regs 6 ≤ a → a < after.regs 6 + 2 * edits.length → ¬ R.foot handle x a)
    (hSlotsSep : ∀ e < edgeCap,
      slots + e < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ slots + e)
    (hNamesSep : ∀ k < slotCap,
      names + k < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ names + k)
    (hframe : ∀ a, a < after.regs 6 ∨ after.regs 6 + 2 * edits.length ≤ a →
      after.mem a = before.mem a) :
    TreeEditBuffer R handle x after edits ∧ TreeEditHeap R handle x after ∧
    TreeEditSlotStorage R handle slots names edgeCap slotCap x (after.regs 3) ∧
    R.rep handle tree x after.mem ∧ R.phi handle x after.mem = R.phi handle x before.mem ∧
    PathSlotTablesAt after.mem slots names edgeCap slotCap slot name := by
  have hkeep a (ha : R.foot handle x a) : before.mem a = after.mem a := by
    symm
    apply hframe
    by_cases h : a < after.regs 6
    · exact Or.inl h
    · exact Or.inr (Nat.le_of_not_gt fun hi => houtside a (by omega) hi ha)
  obtain ⟨hRep', hphi⟩ := hLocal handle tree x before.mem after.mem hkeep
  have hb : TreeEditBuffer R handle x after edits := ⟨hcount, hwords,
    by rwa [treeEditWords_length, hHeapReg], by rwa [treeEditWords_length]⟩
  have hh : TreeEditHeap R handle x after := by
    refine ⟨by rw [hHeapReg]; exact hHeap.below, ?_⟩
    intro a ha
    rw [hHeapReg] at ha
    rw [hframe a (Or.inr (hbelow.trans ha))]
    exact hHeap.zero a ha
  exact ⟨hb, hh, hHeapReg.symm ▸ hStorage, hRep' hRep, hphi.symm,
    hTables.congr (fun e he => hframe _ (hSlotsSep e he)) (fun k hk => hframe _ (hNamesSep k hk))⟩

end MinCostFlow.MinRatio
