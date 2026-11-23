module

public import MinCostFlow.MinRatio.PathTreeCall
public import MinCostFlow.MinRatio.TreeEditEndpoints
public import MinCostFlow.MinRatio.PathSlotBind
import MinCostFlow.LinkCut.ForestModelSplice
import MinCostFlow.LSF.Walks
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.DynSpanner.Walks

/-!
# Applying a tree edge edit after a chain change

The proof of Theorem 5.1 (pages 29–30) applies the tree changes of
Lemma 5.11 (page 20) to link-cut trees. A deletion cuts the resolved
edge. An insertion links the supplied edge record. Both adopt the
returned heap.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LinkCut DynSpanner.Program

/-- The handle, endpoints, and live heap occupy registers 0 through 3. -/
@[expose] def treeEditCut (entry : ℕ) : Stmt :=
  .call 3 entry [.reg 0, .reg 1, .reg 2, .reg 3]

/-- A resolved deletion cuts the model tree, preserves other caller
registers, and adds five steps to the amortized tree cost. -/
theorem treeEditCut_runs {w L constant init handle u v heap : ℕ}
    {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hregs : st.regs 0 = handle ∧ st.regs 1 = u ∧ st.regs 2 = v ∧ st.regs 3 = heap)
    (hwords : ∀ a ∈ [handle, u, v, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 1 s
      [handle, u, v, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 s.n [handle, u, v, heap] < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditCut (op 1)) st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → out.regs r = st.regs r) ∧
      R.rep handle (lctCut pathPayload s u v) y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 s.n [handle, u, v, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 5 := by
  obtain ⟨h0, h1, h2, h3⟩ := hregs
  obtain ⟨next, cost, after, y, ret, hrun, hrep', hp, hf, hc⟩ :=
    pathTree_runs_call (i := 1) (reg := 3) (st := st) (ω := ω)
      (args := [.reg 0, .reg 1, .reg 2, .reg 3]) himpl
      (by simp [evalArgs, Expr.eval, h0, h1, h2, h3]) hwords rfl hrep hpre hfoot hz hroom
  have heq : next = lctCut pathPayload s u v := hp
  subst next
  refine ⟨_, ret, cost, y, hrun, by simp, ?_, hrep', hf, ?_⟩
  · intro r hr
    simp [Function.update_of_ne hr]
  · simpa [argsSize, Expr.size, Nat.add_assoc] using hc

/-- Register 4 holds the replacement edge record. Register 3 remains the heap. -/
@[expose] def treeEditLink (entry : ℕ) : Stmt :=
  .call 3 entry [.reg 0, .reg 1, .reg 2, .reg 4, .reg 3]

/-- A resolved insertion links the supplied edge record, preserves other caller
registers, and adds six steps to the amortized tree cost. -/
theorem treeEditLink_runs {w L constant init handle u v record heap : ℕ}
    {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hregs : st.regs 0 = handle ∧ st.regs 1 = u ∧ st.regs 2 = v ∧ st.regs 3 = heap ∧ st.regs 4 = record)
    (hwords : ∀ a ∈ [handle, u, v, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, u, v, record, heap] st.mem)
    (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, u, v, record, heap] < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditLink (op 0)) st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 3 → out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧ out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 6 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hregs
  obtain ⟨next, cost, after, y, ret, hrun, hrep', hp, hf, hc⟩ :=
    pathTree_runs_call (i := 0) (reg := 3) (st := st) (ω := ω)
      (args := [.reg 0, .reg 1, .reg 2, .reg 4, .reg 3]) himpl
      (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4]) hwords rfl hrep hpre hfoot hz hroom
  have heq : next = lctLink pathPayload s u v (some value) := by
    have h := hp.1
    change next = lctLink pathPayload s u v (readPathEdge st.mem record fmt.limbBits L) at h
    simpa only [readPathEdge_eq hrecord] using h
  subst next
  refine ⟨_, ret, cost, y, hrun, by simp, ?_, hrep', hp.2, hf, ?_⟩
  · intro r hr
    simp [Function.update_of_ne hr]
  · simpa [argsSize, Expr.size, Nat.add_assoc] using hc

/-- A valid named graph and a sufficiently large tree vertex arena
supply the Cut endpoint conditions. Numeric fit is needed for both
the initial tree and the result of the cut. -/
theorem treeEditCut_named_pre {w L constant handle heap base vc ec e : ℕ}
    {G : MGraph} {fmt : Num.Format w} {mem : ℕ → ℕ} {s : PathTreeState}
    {allocation : ℕ → ℕ → List ℕ → ℕ}
    (he : TreeEditEndpointAt mem base vc ec G e) (hvc : vc ≤ s.n)
    (hi : LctInv pathPayload s) (hf : pathTreeFits fmt.limbBits L s)
    (hw : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hn : pathTreeFits fmt.limbBits L
      (lctCut pathPayload s (G.tail e + 1) (G.head e + 1))) :
    (pathTreeMachineContract fmt L constant allocation).pre 1 s
      [handle, G.tail e + 1, G.head e + 1, heap] mem := by
  have hu := he.tailNameBound.trans_le hvc
  have hv := he.headNameBound.trans_le hvc
  exact ⟨hi, hf, hw, hwidth, handle, G.tail e + 1, G.head e + 1, heap, rfl,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hn⟩

/-- During the insertion phase, the partial target forest cannot
already connect the endpoints of an as-yet absent target edge. -/
theorem treeEdit_link_disconnected {F H : MGraph} {e : ℕ}
    (hF : F.IsForest) (hsub : F.IsSubgraph H)
    (he : e ∈ F.E) (hmissing : e ∉ H.E) :
    ¬ H.Connected (F.tail e) (F.head e) := by
  have hp : F.IsPath (F.tail e) (F.head e) [(e, true)] := by
    refine ⟨.cons he rfl (.nil (F.head e)), ?_⟩
    simp [MGraph.walkVertices, MGraph.dst, LSF.isForest_no_selfLoop hF he]
  have hef : e ∈ walkEdges (F.forestPath (F.tail e) (F.head e)) := by
    rw [LSF.forestPath_eq_of_isPath hF hp]
    exact LSF.mem_walkEdges_of_mem List.mem_cons_self
  have hremoved : ({ F with E := F.E.erase e } : MGraph).IsSubgraph H :=
    ⟨hsub.1, fun f hf => Finset.mem_erase.mpr ⟨fun eq => hmissing (eq ▸ hf), hsub.2.1 hf⟩,
      hsub.2.2⟩
  exact fun hc => LSF.not_connected_erase_of_mem_forestPath hF hef
    (MGraph.connected_of_isSubgraph hremoved hc)

/-- The edge-set invariant for an insertion prefix gives the graph
connectivity check when the partial tree carries the target endpoints. -/
theorem treeEdit_insert_prefix_disconnected {F H : MGraph} {oldE : Finset ℕ}
    {done todo : List ℕ} {e : ℕ}
    (hF : F.IsForest) (hs : (F.E \ oldE).toList = done ++ e :: todo)
    (hE : H.E = Chain.applyTreeChanges oldE
      ((oldE \ F.E).toList.map Chain.TreeChange.delete ++ done.map Chain.TreeChange.insert))
    (hV : H.V ⊆ F.V)
    (hends : ∀ f ∈ H.E, H.tail f = F.tail f ∧ H.head f = F.head f) :
    ¬ H.Connected (F.tail e) (F.head e) := by
  obtain ⟨hsub, hmissing, he⟩ := treeEdit_insert_prefix hs
  exact treeEdit_link_disconnected hF ⟨hV, hE.symm ▸ hsub, hends⟩ he (hE.symm ▸ hmissing)

/-- The machine-facing connectivity test is equality of roots in
the parent map induced by a structural forest witness. -/
theorem pathTreeConnected_iff_induced_roots {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth) (hu : u < s.n) (hv : v < s.n) :
    pathTreeConnected s (vid u) (vid v) ↔
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid u) =
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid v) := by
  obtain ⟨tu, htu, hu'⟩ := List.mem_flatMap.mp (hi.verticesActive u hu)
  obtain ⟨tv, htv, hv'⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
  obtain ⟨_, _, _, _, _, hconn, _, _⟩ :=
    lctConnected_spec pathPayload_laws hi htu hu' htv hv'
  exact hconn

/-- When each occupied parent edge slot names an edge of the graph
with those endpoints, vertices in the same link-cut component are
connected in the graph. Follow the parent map two steps per edge to
reach the common root. -/
theorem pathTreeConnected_to_namedGraph {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth) (hu : u < s.n) (hv : v < s.n)
    (hedge : ∀ a < s.n,
      let par := inducedSubPar pathPayload s.splay trees
      par (vid a) ≠ 0 →
      ∃ e ∈ G.E, (G.tail e = a ∧ G.head e = par (par (vid a)) - 1) ∨
        (G.head e = a ∧ G.tail e = par (par (vid a)) - 1))
    (hconn : pathTreeConnected s (vid u) (vid v)) : G.Connected u v := by
  let par := inducedSubPar pathPayload s.splay trees
  let active := trees.flatMap AuxTree.toList
  have hjoin {a b c : ℕ} (hab : G.Connected a b) (hbc : G.Connected b c) :
      G.Connected a c := by
    obtain ⟨P, hp⟩ := hab
    obtain ⟨Q, hq⟩ := hbc
    exact ⟨P ++ Q, DynSpanner.IsWalk.append hp hq⟩
  have hwalk : ∀ k a, a < s.n → par (subRoot par k (vid a)) = 0 →
      G.Connected a (subRoot par k (vid a) - 1) ∧
      G.Connected (subRoot par k (vid a) - 1) a := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro a ha hroot
      by_cases hzero : par (vid a) = 0
      · have heq : subRoot par k (vid a) = vid a := by cases k <;> simp [subRoot, hzero]
        rw [heq]
        simpa [vid] using (show G.Connected a a ∧ G.Connected a a from
          ⟨⟨[], .nil _⟩, ⟨[], .nil _⟩⟩)
      · let slot := par (vid a)
        let parent := par slot
        have haVertex : isVertex s.n (vid a) := by unfold isVertex vid; omega
        have hslot := hi.vertexParEdge (vid a) haVertex hzero
        have hsActive := hi.subPar_mem_active (hi.verticesActive a ha) hzero
        obtain ⟨hpNZ, hpVertex⟩ := hi.edgeParVertex slot hsActive hslot
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := by
          cases k with
          | zero => exact (hzero hroot).elim
          | succ k =>
            cases k with
            | zero =>
              have hr : subRoot par 1 (vid a) = slot := by simp [subRoot, hzero, slot]
              exact (hpNZ (hr ▸ hroot)).elim
            | succ j => exact ⟨j, rfl⟩
        have hr : subRoot par (j + 2) (vid a) = subRoot par j parent := by
          change (if par (vid a) = 0 then vid a else subRoot par (j + 1) slot) = _
          rw [ite_eq_right hzero]
          change (if par slot = 0 then slot else subRoot par j parent) = _
          rw [ite_eq_right hpNZ]
        rw [hr] at hroot ⊢
        have hpid : vid (parent - 1) = parent := by
          have hpos : 1 ≤ parent := hpVertex.1
          unfold vid
          omega
        have hpLt : parent - 1 < s.n := by have hcap : parent ≤ s.n := hpVertex.2; have hpos : 1 ≤ parent := hpVertex.1; omega
        obtain ⟨hup, hdown⟩ := ih j (by omega) (parent - 1) hpLt (by rwa [hpid])
        rw [hpid] at hup hdown
        obtain ⟨e, he, hc⟩ := hedge a ha hzero
        have hstep : G.Connected a (parent - 1) ∧ G.Connected (parent - 1) a := by
          have hforward : G.IsWalk (G.tail e) (G.head e) [(e, true)] := .cons he rfl (.nil _)
          have hback : G.IsWalk (G.head e) (G.tail e) [(e, false)] := .cons he rfl (.nil _)
          change (G.tail e = a ∧ G.head e = parent - 1) ∨
            (G.head e = a ∧ G.tail e = parent - 1) at hc
          rcases hc with ⟨ht, hh⟩ | ⟨hh, ht⟩
          · exact ⟨⟨_, by rwa [ht, hh] at hforward⟩, ⟨_, by rwa [ht, hh] at hback⟩⟩
          · exact ⟨⟨_, by rwa [ht, hh] at hback⟩, ⟨_, by rwa [ht, hh] at hforward⟩⟩
        exact ⟨hjoin hstep.1 hup, hjoin hdown hstep.2⟩
  have hr := (pathTreeConnected_iff_induced_roots hi hu hv).mp hconn
  have huRoot := (hi.subRoot_isRoot (hi.verticesActive u hu)).2.1
  have hvRoot := (hi.subRoot_isRoot (hi.verticesActive v hv)).2.1
  have hcu := (hwalk active.length u hu huRoot).1
  have hcv := (hwalk active.length v hv hvRoot).2
  rw [hr] at hcu
  exact hjoin hcu hcv

/-- Structural witnesses for the same link-cut state have identical
parent maps and the same active nodes. This allows the reroot and
splice specifications to use their own auxiliary tree witnesses. -/
theorem treeEdit_witness_agreement {s : PathTreeState} {ts us : List AuxTree}
    {fs gs : List ℕ} {d e : ℕ → ℕ}
    (ht : LctInvWith pathPayload s ts fs d) (hu : LctInvWith pathPayload s us gs e) :
    (ts.flatMap AuxTree.toList).Perm (us.flatMap AuxTree.toList) ∧
    inducedSubPar pathPayload s.splay ts = inducedSubPar pathPayload s.splay us := by
  have hp := (LctInvWith_canon_perm ht).2.2.2.symm.trans (LctInvWith_canon_perm hu).2.2.2
  exact ⟨hp.flatMap (fun _ _ => List.Perm.refl _),
    funext (inducedSubPar_perm hp ht.activeNodup)⟩

/-- Rerooting keeps each nonzero parent arc as an undirected arc
between the same two nodes. The arc reverses exactly when both
nodes lie on the rerooted path. -/
theorem treeEdit_reroot_parent_arcs {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth) (hv : v < s.n) :
    let next := (lctRerootCost pathPayload s (vid v)).1
    ∃ nextTrees nextDepth, LctInvWith pathPayload next nextTrees free nextDepth ∧
      (nextTrees.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      ∀ x y, y ≠ 0 → inducedSubPar pathPayload s.splay trees x = y →
        inducedSubPar pathPayload next.splay nextTrees x = y ∨
        inducedSubPar pathPayload next.splay nextTrees y = x := by
  dsimp only
  obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
  have hv' : isVertex s.n (vid v) := by unfold isVertex vid; omega
  obtain ⟨nextTrees, L, nextDepth, _, hinext, hperm, _, _, hpath, hout, hswap, _⟩ :=
    lctReroot_spec pathPayload_laws hi ht hvt hv'
  refine ⟨nextTrees, nextDepth, hinext, hperm, ?_⟩
  intro x y hy hxy
  by_cases hx : x ∈ (AuxTree.node (vid v) .leaf L).toList
  · have hreach : reaches (inducedSubPar pathPayload s.splay trees)
        (trees.flatMap AuxTree.toList).length y (vid v) = true := by
      apply reaches_trans hi.activeNodup
        (fun z hz hp => hi.subPar_mem_active hz hp) hi.acyclic ((hpath x).mp hx)
      · have hstep : reaches (inducedSubPar pathPayload s.splay trees) 1 y x = true := by
          by_cases hEq : x = y
          · rw [hEq]
            exact reaches_self _ _ _
          · rw [reaches_succ_of_ne hEq (by rwa [hxy]), hxy]
            exact reaches_self _ _ _
        exact reaches_mono (by
          have := List.length_pos_of_mem (hi.verticesActive v hv)
          omega) hstep
      · exact hi.verticesActive v hv
    exact Or.inr ((hswap y ((hpath y).mpr hreach) x hx).mpr hxy)
  · exact Or.inl ((hout x hx).trans hxy)

private theorem treeEdit_child_ne_parent {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot u : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hs : slot ∈ trees.flatMap AuxTree.toList)
    (hu : u ∈ trees.flatMap AuxTree.toList)
    (hslot : isEdgeSlot s.n slot) (huv : isVertex s.n u)
    (hchild : inducedSubPar pathPayload s.splay trees u = slot) :
    u ≠ inducedSubPar pathPayload s.splay trees slot := by
  intro heq
  have h1 := hi.acyclic u hu (by rw [hchild]; have := hslot.1; omega)
  have h2 := hi.acyclic slot hs (by rw [← heq]; have := huv.1; omega)
  rw [hchild] at h1
  rw [← heq] at h2
  exact (Nat.lt_asymm h1 h2)

/-- Live edge names and active edge slots are inverse, and each named
slot joins the graph edge's endpoints in one of the two orientations. -/
structure TreeEditNamedSlots (s : PathTreeState) (trees : List AuxTree) (G : MGraph)
    (slot name : ℕ → ℕ) : Prop where
  forward : ∀ e ∈ G.E, slot e ∈ trees.flatMap AuxTree.toList ∧
    isEdgeSlot s.n (slot e) ∧ name (slot e) = e
  inverse : ∀ k ∈ trees.flatMap AuxTree.toList, isEdgeSlot s.n k →
    name k ∈ G.E ∧ slot (name k) = k
  endpoints : ∀ e ∈ G.E,
    let par := inducedSubPar pathPayload s.splay trees
    (par (vid (G.tail e)) = slot e ∧ par (slot e) = vid (G.head e)) ∨
    (par (vid (G.head e)) = slot e ∧ par (slot e) = vid (G.tail e))

/-- Reading a nonroot vertex's parent slot gives the graph edge
required by the parent-map connectivity proof. -/
theorem TreeEditNamedSlots.parent_edge {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ}
    (hn : TreeEditNamedSlots s trees G slot name) (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ e ∈ G.E, G.tail e < s.n ∧ G.head e < s.n)
    (a : ℕ) (ha : a < s.n) :
    let par := inducedSubPar pathPayload s.splay trees
    par (vid a) ≠ 0 →
    ∃ e ∈ G.E, (G.tail e = a ∧ G.head e = par (par (vid a)) - 1) ∨
      (G.head e = a ∧ G.tail e = par (par (vid a)) - 1) := by
  dsimp only
  intro hp
  let par := inducedSubPar pathPayload s.splay trees
  let k := par (vid a)
  have haV : isVertex s.n (vid a) := by unfold isVertex vid; omega
  have hk := hi.vertexParEdge (vid a) haV hp
  have hkActive := hi.subPar_mem_active (hi.verticesActive a ha) hp
  obtain ⟨he, hslot⟩ := hn.inverse k hkActive hk
  obtain ⟨_, _, huniq⟩ := hi.edgeUniqueChild k hkActive hk
  have hka : par (vid a) = k := rfl
  have hu := huniq (vid a) ⟨hi.verticesActive a ha, hka, haV,
    treeEdit_child_ne_parent hi hkActive (hi.verticesActive a ha) hk haV hka⟩
  have hidentify (b : ℕ) (hb : b < s.n) (hbk : par (vid b) = k) : b = a := by
    have hbV : isVertex s.n (vid b) := by unfold isVertex vid; omega
    have hbActive := hi.verticesActive b hb
    have h := huniq (vid b) ⟨hbActive, hbk, hbV,
      treeEdit_child_ne_parent hi hkActive hbActive hk hbV hbk⟩
    have hEq := h.trans hu.symm
    unfold vid at hEq
    omega
  have hends := hn.endpoints (name k) he
  dsimp only at hends
  rw [hslot] at hends
  refine ⟨name k, he, ?_⟩
  rcases hends with ⟨ht, hh⟩ | ⟨hh, ht⟩
  · exact Or.inl ⟨hidentify _ (hv _ he).1 ht, by change par k = _ at hh; change _ = par k - 1; rw [hh]; simp [vid]⟩
  · exact Or.inr ⟨hidentify _ (hv _ he).2 hh, by change par k = _ at ht; change _ = par k - 1; rw [ht]; simp [vid]⟩

/-- The two arcs incident to an edge slot keep the same unordered
endpoints under rerooting. Each slot has a unique child and parent. -/
theorem treeEdit_reroot_edge_endpoints {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth) (hv : v < s.n) :
    let next := (lctRerootCost pathPayload s (vid v)).1
    ∃ nextTrees nextDepth, LctInvWith pathPayload next nextTrees free nextDepth ∧
      (nextTrees.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      ∀ slot ∈ trees.flatMap AuxTree.toList, isEdgeSlot s.n slot → ∀ a b,
        isVertex s.n a → isVertex s.n b →
        inducedSubPar pathPayload s.splay trees a = slot →
        inducedSubPar pathPayload s.splay trees slot = b →
        (inducedSubPar pathPayload next.splay nextTrees a = slot ∧
          inducedSubPar pathPayload next.splay nextTrees slot = b) ∨
        (inducedSubPar pathPayload next.splay nextTrees b = slot ∧
          inducedSubPar pathPayload next.splay nextTrees slot = a) := by
  dsimp only
  obtain ⟨nextTrees, nextDepth, hn, hperm, harc⟩ := treeEdit_reroot_parent_arcs hi hv
  refine ⟨nextTrees, nextDepth, hn, hperm, ?_⟩
  intro slot hs hslot a b ha hb haSlot hSlotB
  have hnode (u : ℕ) (hu : isVertex s.n u) : u ∈ trees.flatMap AuxTree.toList := by
    have hid : vid (u - 1) = u := by unfold vid; have := hu.1; omega
    rw [← hid]
    exact hi.verticesActive _ (by have := hu.1; have := hu.2; omega)
  have haActive := hnode a ha
  have hbActive := hnode b hb
  have hab : a ≠ b := by
    have hne := treeEdit_child_ne_parent hi hs haActive hslot ha haSlot
    rwa [hSlotB] at hne
  have hsa : slot ≠ 0 := by have := hslot.1; omega
  have hbNZ : b ≠ 0 := by have := hb.1; omega
  rcases harc a slot hsa haSlot with ha' | ha' <;>
    rcases harc slot b hbNZ hSlotB with hb' | hb'
  · exact Or.inl ⟨ha', hb'⟩
  · have hs' := hperm.mem_iff.mpr hs
    have haa := hperm.mem_iff.mpr haActive
    have hba := hperm.mem_iff.mpr hbActive
    obtain ⟨child, _, huniq⟩ := hn.edgeUniqueChild slot hs' hslot
    have hca := huniq a ⟨haa, ha', ha, treeEdit_child_ne_parent hn hs' haa hslot ha ha'⟩
    have hcb := huniq b ⟨hba, hb', hb, treeEdit_child_ne_parent hn hs' hba hslot hb hb'⟩
    exact (hab (hca.trans hcb.symm)).elim
  · exact (hab (ha'.symm.trans hb')).elim
  · exact Or.inr ⟨hb', ha'⟩

/-- A disconnected pair of vertices has an available edge slot,
by the link-cut forest invariant. -/
theorem treeEdit_freeHead_of_disconnected {s : PathTreeState} {u v : ℕ}
    (hi : LctInv pathPayload s) (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) : s.freeHead ≠ 0 := by
  obtain ⟨trees, free, depth, hInv⟩ := hi
  have hconn := pathTreeConnected_iff_induced_roots hInv hu hv
  exact (hInv.freeHead_ne_zero_of_two_roots hu hv (fun h => hd (hconn.mpr h))).2

/-- A successful Link installs the original free-head slot between
the two vertex indices in the induced parent map. -/
theorem treeEdit_link_parent_slot {s : PathTreeState} {u v : ℕ}
    (hi : LctInv pathPayload s) (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) (value : PathEdgeValue) :
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ trees free depth, LctInvWith pathPayload next trees free depth ∧
      s.freeHead ∈ trees.flatMap AuxTree.toList ∧
      inducedSubPar pathPayload next.splay trees (vid v) = s.freeHead ∧
      inducedSubPar pathPayload next.splay trees s.freeHead = vid u := by
  dsimp only
  obtain ⟨trees, free, depth, hInv⟩ := hi
  have hroot := pathTreeConnected_iff_induced_roots hInv hu hv
  have hdisc := fun h => hd (hroot.mpr h)
  have hnonempty := (hInv.freeHead_ne_zero_of_two_roots hu hv hdisc).1
  cases free with
  | nil => exact (hnonempty rfl).elim
  | cons slot rest =>
    have hslot : s.freeHead = slot := hInv.freeListInv.2.1
    have hu' : isVertex s.n (vid u) := ⟨by unfold vid; omega, by unfold vid; omega⟩
    have hv' : isVertex s.n (vid v) := ⟨by unfold vid; omega, by unfold vid; omega⟩
    obtain ⟨_, _, nextTrees, nextDepth, _, hnext, _, hperm, hpv, hpu, _⟩ :=
      lctLink_spec pathPayload_laws hInv rfl hu' hv' hdisc (some value)
    exact ⟨nextTrees, rest, nextDepth, hnext,
      hperm.mem_iff.mpr (by simp [hslot]), hslot.symm ▸ hpv, hslot.symm ▸ hpu⟩

/-- Linking distinct components inserts the free-head slot and
preserves the unordered endpoints of every previously active edge slot. -/
theorem treeEdit_link_preserves_endpoints {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) (value : PathEdgeValue) :
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ nextTrees nextFree nextDepth, LctInvWith pathPayload next nextTrees nextFree nextDepth ∧
      (nextTrees.flatMap AuxTree.toList).Perm (s.freeHead :: trees.flatMap AuxTree.toList) ∧
      inducedSubPar pathPayload next.splay nextTrees (vid v) = s.freeHead ∧
      inducedSubPar pathPayload next.splay nextTrees s.freeHead = vid u ∧
      ∀ slot ∈ trees.flatMap AuxTree.toList, isEdgeSlot s.n slot → ∀ a b,
        isVertex s.n a → isVertex s.n b →
        inducedSubPar pathPayload s.splay trees a = slot →
        inducedSubPar pathPayload s.splay trees slot = b →
        (inducedSubPar pathPayload next.splay nextTrees a = slot ∧
          inducedSubPar pathPayload next.splay nextTrees slot = b) ∨
        (inducedSubPar pathPayload next.splay nextTrees b = slot ∧
          inducedSubPar pathPayload next.splay nextTrees slot = a) := by
  dsimp only
  have hdisc := fun h => hd ((pathTreeConnected_iff_induced_roots hi hu hv).mpr h)
  have hnonempty := (hi.freeHead_ne_zero_of_two_roots hu hv hdisc).1
  cases free with
  | nil => exact (hnonempty rfl).elim
  | cons fresh rest =>
    have hfresh : s.freeHead = fresh := hi.freeListInv.2.1
    have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
    have hvV : isVertex s.n (vid v) := by unfold isVertex vid; omega
    obtain ⟨ts, ds, nextTrees, nextDepth, hts, hnext, hperm0, hperm1, hpv, hpf, hstay, _⟩ :=
      lctLink_spec pathPayload_laws hi rfl huV hvV hdisc (some value)
    let first := (lctRerootCost pathPayload s (vid v)).1
    let second := (lctRerootCost pathPayload first (vid u)).1
    obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
    obtain ⟨vs, _, dv, _, hvInv, hvPerm, _, hvRoot, _, _, _, _, _, _, _, _, _, hroots, _⟩ :=
      lctReroot_spec pathPayload_laws hi htv hvMem hvV
    obtain ⟨vs', _, hvInv', _, hvEnds⟩ := treeEdit_reroot_edge_endpoints hi hv
    obtain ⟨_, hvAgree⟩ := treeEdit_witness_agreement hvInv' hvInv
    have huFirst : u < first.n := hu
    have huFirstV : isVertex first.n (vid u) := huV
    have huActive := hvInv.verticesActive u huFirst
    have hvActive := hvInv.verticesActive v (show v < first.n from hv)
    obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp huActive
    obtain ⟨us, L, du, _, huInv, _, _, _, huPath, huOff, _⟩ :=
      lctReroot_spec pathPayload_laws hvInv htu huMem huFirstV
    obtain ⟨us', _, huInv', _, huEnds⟩ := treeEdit_reroot_edge_endpoints hvInv huFirst
    obtain ⟨_, huAgree⟩ := treeEdit_witness_agreement huInv' hts
    obtain ⟨_, huRootAgree⟩ := treeEdit_witness_agreement huInv hts
    have hvOff : vid v ∉ (AuxTree.node (vid u) .leaf L).toList := by
      intro hm
      have hru := (subRoot_eq_iff_reaches_zero hvInv huActive hvRoot).mpr ((huPath (vid v)).mp hm)
      have hrv := subRoot_eq_self_of_zero hvInv hvActive hvRoot
      have hr := hru.trans hrv.symm
      exact hdisc ((hroots (vid u) (hi.verticesActive u hu) (vid v) (hi.verticesActive v hv)).mp hr)
    have hvZero : inducedSubPar pathPayload second.splay ts (vid v) = 0 := by
      rw [← huRootAgree]
      exact (huOff _ hvOff).trans hvRoot
    refine ⟨nextTrees, rest, nextDepth, hnext, ?_, hfresh.symm ▸ hpv, hfresh.symm ▸ hpf, ?_⟩
    · rw [hfresh]
      exact hperm1.trans (hperm0.cons fresh)
    · intro slot hs hsSlot a b ha hb haSlot hSlotB
      have hsFirst := hvPerm.mem_iff.mpr hs
      have hfFree : fresh ∈ fresh :: rest := List.mem_cons_self
      have hsNe : slot ≠ fresh := fun he =>
        ((hi.partitionSlots slot hsSlot).mp hs) (he.symm ▸ hfFree)
      have hstable x (hx : inducedSubPar pathPayload second.splay ts x = slot)
          (hxFresh : x ≠ fresh) :
          inducedSubPar pathPayload (lctLink pathPayload s (vid u) (vid v) (some value)).splay
            nextTrees x = slot := by
        have hne : x ≠ vid v := fun he => by
          rw [he, hvZero] at hx
          have := hsSlot.1
          omega
        exact (hstay x hne hxFresh).trans hx
      have hsStay : inducedSubPar pathPayload
          (lctLink pathPayload s (vid u) (vid v) (some value)).splay nextTrees slot =
          inducedSubPar pathPayload second.splay ts slot :=
        hstay slot (fun he => not_vertex_and_edge ⟨hvV, he ▸ hsSlot⟩) hsNe
      have haNe : a ≠ fresh := fun he => not_vertex_and_edge ⟨ha, he.symm ▸ hi.freeValid _ hfFree⟩
      have hbNe : b ≠ fresh := fun he => not_vertex_and_edge ⟨hb, he.symm ▸ hi.freeValid _ hfFree⟩
      have hfirst := hvEnds slot hs hsSlot a b ha hb haSlot hSlotB
      rw [hvAgree] at hfirst
      have hsecond :
          (inducedSubPar pathPayload second.splay ts a = slot ∧
            inducedSubPar pathPayload second.splay ts slot = b) ∨
          (inducedSubPar pathPayload second.splay ts b = slot ∧
            inducedSubPar pathPayload second.splay ts slot = a) := by
        rcases hfirst with ⟨ha', hb'⟩ | ⟨hb', ha'⟩
        · simpa only [huAgree] using huEnds slot hsFirst hsSlot a b ha hb ha' hb'
        · have hh := huEnds slot hsFirst hsSlot b a hb ha hb' ha'
          rw [huAgree] at hh
          exact hh.symm
      exact hsecond.elim
        (fun h => Or.inl ⟨hstable a h.1 haNe, hsStay.trans h.2⟩)
        (fun h => Or.inr ⟨hstable b h.1 hbNe, hsStay.trans h.2⟩)

/-- Cutting adjacent vertices removes their intervening edge slot
from the active forest and returns that slot to the free list. -/
theorem treeEdit_cut_parent_slot {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v slot : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : isVertex s.n u) (hv : isVertex s.n v) (hne : u ≠ v)
    (hactive : slot ∈ trees.flatMap AuxTree.toList)
    (hAdj : (inducedSubPar pathPayload s.splay trees v = slot ∧
        inducedSubPar pathPayload s.splay trees slot = u) ∨
      (inducedSubPar pathPayload s.splay trees u = slot ∧
        inducedSubPar pathPayload s.splay trees slot = v)) :
    let next := lctCut pathPayload s u v
    ∃ nextTrees nextDepth,
      LctInvWith pathPayload next nextTrees (slot :: free) nextDepth ∧
      next.freeHead = slot ∧ slot ∉ nextTrees.flatMap AuxTree.toList ∧
      (slot :: nextTrees.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      inducedSubPar pathPayload next.splay nextTrees u = 0 ∧
      inducedSubPar pathPayload next.splay nextTrees v = 0 ∧
      ∀ e ∈ trees.flatMap AuxTree.toList, isEdgeSlot s.n e → e ≠ slot → ∀ a b,
        isVertex s.n a → isVertex s.n b →
        inducedSubPar pathPayload s.splay trees a = e →
        inducedSubPar pathPayload s.splay trees e = b →
        (inducedSubPar pathPayload next.splay nextTrees a = e ∧
          inducedSubPar pathPayload next.splay nextTrees e = b) ∨
        (inducedSubPar pathPayload next.splay nextTrees b = e ∧
          inducedSubPar pathPayload next.splay nextTrees e = a) := by
  dsimp only
  have h := (lctCut_spec pathPayload_laws hi u v).2.2
  rw [dite_eq_left ⟨hu, hv, hne, slot, hactive, hAdj⟩] at h
  obtain ⟨ts, ds, removed, _, nextTrees, nextDepth, hts, hnext, hrSlot, hrActive, hpair, hvr, _, hur, _,
    hperm, hpU, hpV, hstay, _⟩ := h
  let par := inducedSubPar pathPayload s.splay trees
  have horder {a b x : ℕ} (ha : a ∈ trees.flatMap AuxTree.toList)
      (hx : x ∈ trees.flatMap AuxTree.toList) (hb : 1 ≤ b)
      (hax : par a = x) (hxb : par x = b) : depth b < depth a := by
    dsimp only [par] at hax hxb
    have hxpos := (hi.activeValid x hx).1
    have h₁ := hi.acyclic a ha (by rw [hax]; omega)
    have h₂ := hi.acyclic x hx (by rw [hxb]; omega)
    rw [hax] at h₁
    rw [hxb] at h₂
    exact h₂.trans h₁
  have huActive : u ∈ trees.flatMap AuxTree.toList := by
    have heq : vid (u - 1) = u := by unfold vid; have := hu.1; omega
    rw [← heq]
    exact hi.verticesActive _ (by have := hu.1; have := hu.2; omega)
  have hvActive : v ∈ trees.flatMap AuxTree.toList := by
    have heq : vid (v - 1) = v := by unfold vid; have := hv.1; omega
    rw [← heq]
    exact hi.verticesActive _ (by have := hv.1; have := hv.2; omega)
  have heq : removed = slot := by
    rcases hpair with ⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩ <;>
      rcases hAdj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
    · exact hr₁.symm.trans hs₁
    · exact (Nat.lt_asymm (horder hvActive hrActive hu.1 hr₁ hr₂)
        (horder huActive hactive hv.1 hs₁ hs₂)).elim
    · exact (Nat.lt_asymm (horder huActive hrActive hv.1 hr₁ hr₂)
        (horder hvActive hactive hu.1 hs₁ hs₂)).elim
    · exact hr₁.symm.trans hs₁
  rw [heq] at hnext hperm hvr hstay hrSlot
  have hfree : (lctCut pathPayload s u v).freeHead = slot := hnext.freeListInv.2.1
  have hn := hperm.nodup_iff.mpr hi.activeNodup
  refine ⟨nextTrees, nextDepth, hnext, hfree, (List.nodup_cons.mp hn).1, hperm, hpU, hpV, ?_⟩
  have huName : u - 1 < s.n := by have := hu.1; have := hu.2; omega
  have huId : vid (u - 1) = u := by unfold vid; have := hu.1; omega
  obtain ⟨us, _, huInv, _, huEnds⟩ := treeEdit_reroot_edge_endpoints hi huName
  rw [huId] at huInv huEnds
  obtain ⟨_, hagree⟩ := treeEdit_witness_agreement huInv hts
  intro e he heSlot heNe a b ha hb hap heb
  let mid := (lctRerootCost pathPayload s u).1
  have hchild x (hx : isVertex s.n x) (hpar : inducedSubPar pathPayload mid.splay ts x = e) :
      inducedSubPar pathPayload (lctCut pathPayload s u v).splay nextTrees x = e := by
    apply (hstay x ?_).trans hpar
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | heq | rfl)
    · rw [hur] at hpar
      have := heSlot.1
      omega
    · exact not_vertex_and_edge ⟨hx, heq.symm ▸ hrSlot⟩
    · exact heNe (hpar.symm.trans hvr)
  have hslotStay := hstay e (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (heq | heq | heq)
    · exact not_vertex_and_edge ⟨hu, heq ▸ heSlot⟩
    · exact heNe heq
    · exact not_vertex_and_edge ⟨hv, heq ▸ heSlot⟩)
  have hmid := huEnds e he heSlot a b ha hb hap heb
  rw [hagree] at hmid
  exact hmid.elim (fun h => Or.inl ⟨hchild a ha h.1, hslotStay.trans h.2⟩)
    (fun h => Or.inr ⟨hchild b hb h.1, hslotStay.trans h.2⟩)

/-- Once the partial graph and the link-cut state agree on
connectivity, the insertion prefix supplies both Link conditions. -/
theorem treeEdit_insert_prefix_link_conditions {F H : MGraph} {oldE : Finset ℕ}
    {done todo : List ℕ} {e : ℕ} {tree : PathTreeState}
    (hF : F.IsForest) (hs : (F.E \ oldE).toList = done ++ e :: todo)
    (hE : H.E = Chain.applyTreeChanges oldE
      ((oldE \ F.E).toList.map Chain.TreeChange.delete ++ done.map Chain.TreeChange.insert))
    (hV : H.V ⊆ F.V)
    (hends : ∀ f ∈ H.E, H.tail f = F.tail f ∧ H.head f = F.head f)
    (hi : LctInv pathPayload tree) (hu : F.tail e < tree.n) (hv : F.head e < tree.n)
    (hconn : pathTreeConnected tree (vid (F.tail e)) (vid (F.head e)) →
      H.Connected (F.tail e) (F.head e)) :
    ¬ pathTreeConnected tree (vid (F.tail e)) (vid (F.head e)) ∧ tree.freeHead ≠ 0 := by
  have hd := treeEdit_insert_prefix_disconnected hF hs hE hV hends
  have hnot : ¬ pathTreeConnected tree (vid (F.tail e)) (vid (F.head e)) :=
    fun hc => hd (hconn hc)
  exact ⟨hnot, treeEdit_freeHead_of_disconnected hi hu hv hnot⟩

/-- At an insertion cursor, restrict the target graph to the edges
already present. If the tree's connectivity implies connectivity in
this partial graph, the named Link is legal. -/
theorem treeEdit_diff_cursor_link_conditions {oldE : Finset ℕ} {F : MGraph}
    {processed remaining : List Chain.TreeChange} {e : ℕ} {tree : PathTreeState}
    (hF : F.IsForest)
    (hs : Chain.diffTreeChanges oldE F.E = processed ++ .insert e :: remaining)
    (hi : LctInv pathPayload tree) (hu : F.tail e < tree.n) (hv : F.head e < tree.n)
    (hconn : pathTreeConnected tree (vid (F.tail e)) (vid (F.head e)) →
      ({ F with E := Chain.applyTreeChanges oldE processed } : MGraph).Connected (F.tail e) (F.head e)) :
    ¬ pathTreeConnected tree (vid (F.tail e)) (vid (F.head e)) ∧ tree.freeHead ≠ 0 := by
  obtain ⟨done, todo, hcursor, hprocessed, _⟩ := treeEdit_diff_insertion_cursor hs
  exact treeEdit_insert_prefix_link_conditions (H := { F with E := Chain.applyTreeChanges oldE processed })
    hF hcursor (by rw [hprocessed]) (fun _ h => h) (fun _ _ => ⟨rfl, rfl⟩) hi hu hv hconn

/-- A cut keeps the table cells unchanged and removes the edge and
its freed slot from the domains on which the tables are inverse. -/
theorem treeEdit_cut_tables {R : DSRep PathTreeState} {old new : R.τ}
    {mem mem' : ℕ → ℕ} {handle heap ret space slots names edgeCap slotCap edge : ℕ}
    {liveEdges liveSlots : Finset ℕ} {f g : ℕ → ℕ}
    (ht : PathSlotTablesAt mem slots names edgeCap slotCap f g)
    (hframe : R.Respects (R.foot handle old) heap space mem ret handle new mem')
    (hslots : ∀ e < edgeCap, slots + e < heap ∧ ¬ R.foot handle old (slots + e))
    (hnames : ∀ s < slotCap, names + s < heap ∧ ¬ R.foot handle old (names + s))
    (he : edge ∈ liveEdges)
    (hf : ∀ e ∈ liveEdges, f e ∈ liveSlots ∧ g (f e) = e)
    (hg : ∀ s ∈ liveSlots, g s ∈ liveEdges ∧ f (g s) = s) :
    PathSlotTablesAt mem' slots names edgeCap slotCap f g ∧
      (∀ e ∈ liveEdges.erase edge, f e ∈ liveSlots.erase (f edge) ∧ g (f e) = e) ∧
      (∀ s ∈ liveSlots.erase (f edge), g s ∈ liveEdges.erase edge ∧ f (g s) = s) := by
  refine ⟨ht.congr ?_ ?_, pathSlotCut_inverse liveEdges liveSlots f g he hf hg⟩
  · intro e h
    exact hframe.2.2.2.1 _ (hslots e h).1 (hslots e h).2
  · intro s h
    exact hframe.2.2.2.1 _ (hnames s h).1 (hnames s h).2

/-- Linking and binding preserve the inverse relationship, extending
it by the new edge and the slot returned by Link. -/
theorem treeEdit_link_tables {w : ℕ} {R : DSRep PathTreeState} {old new : R.τ}
    {mem mid out : ℕ → ℕ} {handle heap ret space slots names edgeCap slotCap edge slot : ℕ}
    {liveEdges liveSlots : Finset ℕ} {f g : ℕ → ℕ}
    (ht : PathSlotTablesAt mem slots names edgeCap slotCap f g)
    (hframe : R.Respects (R.foot handle old) heap space mem ret handle new mid)
    (hslots : ∀ e < edgeCap, slots + e < heap ∧ ¬ R.foot handle old (slots + e))
    (hnames : ∀ s < slotCap, names + s < heap ∧ ¬ R.foot handle old (names + s))
    (hsep : slots + edgeCap ≤ names ∨ names + slotCap ≤ slots)
    (he : edge < edgeCap) (hs : slot < slotCap)
    (heNew : edge ∉ liveEdges) (hsNew : slot ∉ liveSlots)
    (hf : ∀ e ∈ liveEdges, f e ∈ liveSlots ∧ g (f e) = e)
    (hg : ∀ s ∈ liveSlots, g s ∈ liveEdges ∧ f (g s) = s)
    (hbind : (pathSlotBindContract w).post [slots, names, edge, slot, ret] mid ret out) :
    let f' := Function.update f edge slot
    let g' := Function.update g slot edge
    PathSlotTablesAt out slots names edgeCap slotCap f' g' ∧
      (∀ e ∈ insert edge liveEdges, f' e ∈ insert slot liveSlots ∧ g' (f' e) = e) ∧
      (∀ s ∈ insert slot liveSlots, g' s ∈ insert edge liveEdges ∧ f' (g' s) = s) := by
  have ht' : PathSlotTablesAt mid slots names edgeCap slotCap f g :=
    ht.congr (fun e h => hframe.2.2.2.1 _ (hslots e h).1 (hslots e h).2)
      (fun s h => hframe.2.2.2.1 _ (hnames s h).1 (hnames s h).2)
  exact ⟨pathSlotBind_tables ht' he hs hsep hbind,
    pathSlotBind_inverse liveEdges liveSlots f g heNew hsNew hf hg⟩

/-- A tree Link followed by its slot bind respects the combined old
footprint of the tree and the two edited table cells. -/
theorem treeEdit_link_bind_respects {w : ℕ} {R : DSRep PathTreeState} {old new : R.τ}
    {mem mid out : ℕ → ℕ} {handle heap ret space slots names edge slot : ℕ}
    (htree : R.Respects (R.foot handle old) heap space mem ret handle new mid)
    (hbind : (pathSlotBindContract w).post [slots, names, edge, slot, ret] mid ret out) :
    R.Respects (fun a => R.foot handle old a ∨ a = slots + edge ∨ a = names + slot)
      heap space mem ret handle new out := by
  obtain ⟨hlo, hhi, _, hframe, hfoot⟩ := htree
  have hm : out = Function.update (Function.update mid (slots + edge) slot)
      (names + slot) edge := hbind.2.1
  refine ⟨hlo, hhi, hbind.2.2, ?_, ?_⟩
  · intro a ha houtside
    have hs : a ≠ slots + edge := fun he => houtside (Or.inr (Or.inl he))
    have hn : a ≠ names + slot := fun he => houtside (Or.inr (Or.inr he))
    rw [hm, Function.update_of_ne hn, Function.update_of_ne hs]
    exact hframe a ha (fun hf => houtside (Or.inl hf))
  · intro a ha
    exact (hfoot a ha).imp_left Or.inl

/-- The represented insertion record and the graph's endpoint
bounds supply the Link layout preconditions. The caller supplies
connectivity and numeric fit. -/
theorem treeEditLink_named_pre {w L constant handle heap record base vc ec e : ℕ}
    {G : MGraph} {fmt : Num.Format w} {mem : ℕ → ℕ} {s : PathTreeState}
    {value : PathEdgeValue} {allocation : ℕ → ℕ → List ℕ → ℕ}
    (he : TreeEditEndpointAt mem base vc ec G e) (hvc : vc ≤ s.n)
    (hi : LctInv pathPayload s) (hf : pathTreeFits fmt.limbBits L s)
    (hw : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hc : ¬ pathTreeConnected s (G.tail e + 1) (G.head e + 1))
    (hb : record + (2 + 4 * L) ≤ heap)
    (hr : PathEdgeAt mem record fmt.limbBits L (some value))
    (hn : pathTreeFits fmt.limbBits L
      (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some value))) :
    (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, G.tail e + 1, G.head e + 1, record, heap] mem := by
  have hu := he.tailNameBound.trans_le hvc
  have hv := he.headNameBound.trans_le hvc
  have hfree := treeEdit_freeHead_of_disconnected hi hu hv hc
  have hread := readPathEdge_eq hr
  refine ⟨hi, hf, hw, hwidth, handle, G.tail e + 1, G.head e + 1, record, heap, rfl,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hc, hfree, hb, ?_, ?_, ?_⟩
  · rwa [hread]
  · rw [hread]
    rfl
  · rwa [hread]

/-- Resolve the named edge and apply its link using the shared
graph and tree contracts. -/
theorem treeEditLink_named_runs {w L constant init handle heap base vc ec e record : ℕ}
    {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h8 : st.regs 8 = e) (h9 : st.regs 9 = dgETailSlotBase base vc ec)
    (h10 : st.regs 10 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 11 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (h4 : st.regs 4 = record) (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, G.tail e + 1, G.head e + 1, record, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, G.tail e + 1, G.head e + 1, record, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω ((treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink (op 0))
        st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 34 := by
  dsimp only
  obtain ⟨mid, hresolve, hu, hv, _, _, hmem, hreg⟩ :=
    treeEditResolve_runs (p := p) (ω := ω) he hgraphRoom hvc hn h8 h9 h10 h11
  obtain ⟨out, ret, c, y, hr, hret, hsave, hrep', hslot, hframe, hc⟩ :=
    treeEditLink_runs (ω := ω) himpl
      ⟨(hreg 0 (by decide) (by decide)).trans h0, hu, hv,
        (hreg 3 (by decide) (by decide)).trans h3, (hreg 4 (by decide) (by decide)).trans h4⟩
      hwords (by rwa [hmem]) (by rwa [hmem]) (by rwa [hmem]) hfoot (by rwa [hmem]) hroom
  rw [hmem] at hframe hc
  exact ⟨out, ret, 27 + c + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 27, c, hresolve, hr, rfl⟩),
    hret, (fun r h1 h2 h3 => (hsave r h3).trans (hreg r h1 h2)), hrep', hslot, hframe, by omega⟩

/-- Resolve the named edge and apply its cut using the shared
graph and tree contracts. -/
theorem treeEditCut_named_runs {w L constant init handle heap base vc ec e : ℕ}
    {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h8 : st.regs 8 = e) (h9 : st.regs 9 = dgETailSlotBase base vc ec)
    (h10 : st.regs 10 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 11 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 1 s
      [handle, G.tail e + 1, G.head e + 1, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 s.n [handle, G.tail e + 1, G.head e + 1, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω ((treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditCut (op 1))
        st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → out.regs r = st.regs r) ∧
      R.rep handle (lctCut pathPayload s u v) y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 s.n [handle, u, v, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 33 := by
  dsimp only
  obtain ⟨mid, hresolve, hu, hv, _, _, hmem, hreg⟩ :=
    treeEditResolve_runs (p := p) (ω := ω) he hgraphRoom hvc hn h8 h9 h10 h11
  obtain ⟨out, ret, c, y, hr, hret, hsave, hrep', hframe, hc⟩ :=
    treeEditCut_runs (ω := ω) himpl
      ⟨(hreg 0 (by decide) (by decide)).trans h0, hu, hv,
        (hreg 3 (by decide) (by decide)).trans h3⟩
      hwords (by rwa [hmem]) (by rwa [hmem]) hfoot (by rwa [hmem]) hroom
  rw [hmem] at hframe hc
  exact ⟨out, ret, 27 + c + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 27, c, hresolve, hr, rfl⟩),
    hret, (fun r h1 h2 h3 => (hsave r h3).trans (hreg r h1 h2)), hrep', hframe, by omega⟩

/-- Bind the internal edge name in register 8 to the slot returned
at the saved Link output address in register 21. -/
@[expose] def treeEditBindSlot (bind : ℕ) : Stmt :=
  .call 3 bind [.reg 19, .reg 20, .reg 8, .load (.reg 21), .reg 3]

/-- The returned slot can be bound without modifying the linked tree
or its potential. The two table cells must be outside the tree. -/
theorem treeEditBindSlot_runs {w bind slots names edge slot response heap handle : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {R : DSRep PathTreeState}
    {x : R.τ} {tree : PathTreeState}
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hlocal : R.Local) (hrep : R.rep handle tree x st.mem)
    (hregs : st.regs 19 = slots ∧ st.regs 20 = names ∧ st.regs 8 = edge ∧
      st.regs 21 = response ∧ st.regs 3 = heap)
    (hslot : st.mem response = slot)
    (hs : slots + edge < heap) (hn : names + slot < heap) (hsep : slots + edge ≠ names + slot)
    (hsf : ¬ R.foot handle x (slots + edge)) (hnf : ¬ R.foot handle x (names + slot))
    (hh : heap < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω (treeEditBindSlot bind) st .normal out cost ∧
      out.regs 3 = heap ∧ (∀ r, r ≠ 3 → out.regs r = st.regs r) ∧
      (pathSlotBindContract w).post [slots, names, edge, slot, heap] st.mem heap out.mem ∧
      R.rep handle tree x out.mem ∧ R.phi handle x out.mem = R.phi handle x st.mem ∧
      cost ≤ 23 := by
  obtain ⟨h19, h20, h8, h21, h3⟩ := hregs
  have hargs : evalArgs w st [.reg 19, .reg 20, .reg 8, .load (.reg 21), .reg 3] =
      some [slots, names, edge, slot, heap] := by
    simp [evalArgs, Expr.eval, h19, h20, h8, h21, h3, hslot]
  have hwords : ∀ a ∈ [slots, names, edge, slot, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, result, after, cost, hr, hpost, hc⟩ :=
    hbind [slots, names, edge, slot, heap] st.mem st.pos ω hwords
      ⟨slots, names, edge, slot, heap, rfl, hs, hn, hsep, hh, hz⟩
  have hret : result.value = heap := hpost.1
  let out := { after with regs := Function.update st.regs 3 heap }
  have hrun : Runs w p ω (treeEditBindSlot bind) st .normal out (6 + cost + 1) :=
    runs_call_iff.mpr ⟨_, body, result, after, cost, hargs, hbody, hr,
      rfl, by simp [out, hret], rfl⟩
  have hmem : after.mem = Function.update (Function.update st.mem (slots + edge) slot)
      (names + slot) edge := hpost.2.1
  have hframe : ∀ a, R.foot handle x a → st.mem a = after.mem a := by
    intro a ha
    have hsne : a ≠ slots + edge := fun eq => hsf (eq ▸ ha)
    have hnne : a ≠ names + slot := fun eq => hnf (eq ▸ ha)
    simp [hmem, Function.update_of_ne hsne, Function.update_of_ne hnne]
  have hloc := hlocal handle tree x st.mem after.mem hframe
  change cost ≤ 16 at hc
  exact ⟨out, 6 + cost + 1, hrun, by simp [out], fun r h => by simp [out, Function.update_of_ne h], hret ▸ hpost,
    hloc.1 hrep, hloc.2.symm, by omega⟩

end MinCostFlow.MinRatio
