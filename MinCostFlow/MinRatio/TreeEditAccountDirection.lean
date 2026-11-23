module

public import MinCostFlow.MinRatio.TreeEdit
import MinCostFlow.MinRatio.TreeEditLoop
import MinCostFlow.MinRatio.PathTreeExpose
import MinCostFlow.MinRatio.TreeEditPayloadSave
public import MinCostFlow.MinRatio.TreeEditFold

/-!
# Directions of accounts in the link-cut forest

The tree operations in Section 6 (pages 29–30) use directional
gradient and flow accounts. On a rerooted path, the slot's parent
arc and its evaluated account reverse together.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut Chain

/-- Rerooting reverses a slot's evaluated account precisely on the branch
where it reverses the slot's original parent arc. -/
theorem treeEdit_reroot_account_parent {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {v slot parent : ℕ} {value : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth) (hv : v < s.n)
    (hp : inducedSubPar pathPayload s.splay trees slot = parent) (hn : parent ≠ 0)
    (ha : (slot, some value) ∈ forestPairs pathPayload s.splay trees) :
    let next := (lctRerootCost pathPayload s (vid v)).1
    ∃ ts ds, LctInvWith pathPayload next ts free ds ∧
      ((inducedSubPar pathPayload next.splay ts slot = parent ∧
          (slot, some value) ∈ forestPairs pathPayload next.splay ts) ∨
        (inducedSubPar pathPayload next.splay ts parent = slot ∧
          (slot, some value.reverse) ∈ forestPairs pathPayload next.splay ts)) := by
  dsimp only
  obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
  have hv' : isVertex s.n (vid v) := by unfold isVertex vid; omega
  obtain ⟨ts, L, ds, _, hi', _, _, _, hpath, hoff, hswap, _, hsplit, hresult, hout, hin, _⟩ :=
    lctReroot_spec pathPayload_laws hi ht hvt hv'
  let path := (AuxTree.node (vid v) .leaf L).toList
  refine ⟨ts, ds, hi', ?_⟩
  have hm := List.mem_append.mp (hsplit.mem_iff.mpr ha)
  by_cases hslot : slot ∈ path
  · have hparent : parent ∈ path := by
      apply (hpath parent).mpr
      apply reaches_trans hi.activeNodup
        (fun z hz hp => hi.subPar_mem_active hz hp) hi.acyclic ((hpath slot).mp hslot)
      · have hstep : reaches (inducedSubPar pathPayload s.splay trees) 1 parent slot = true := by
          by_cases heq : slot = parent
          · rw [heq]
            exact reaches_self _ _ _
          · rw [reaches_succ_of_ne heq (by rwa [hp]), hp]
            exact reaches_self _ _ _
        exact reaches_mono (by
          have := List.length_pos_of_mem (hi.verticesActive v hv)
          omega) hstep
      · exact hi.verticesActive v hv
    have hm' := hm.resolve_right (fun h => hout _ h hslot)
    refine Or.inr ⟨(hswap parent hparent slot hslot).mpr hp, hresult.mem_iff.mpr ?_⟩
    apply List.mem_append_left
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨(slot, some value), hm', rfl⟩
  · have hm' := hm.resolve_left (fun h => hslot (hin _ h))
    exact Or.inl ⟨(hoff slot hslot).trans hp, hresult.mem_iff.mpr (List.mem_append_right _ hm')⟩

/-- An edge's flow and detector account follow the two possible endpoint
orders after rerooting. Swapping the endpoints reverses the account. -/
theorem treeEdit_reroot_account_endpoints {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {v slot child parent : ℕ} {value : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth) (hv : v < s.n)
    (hs : slot ∈ trees.flatMap AuxTree.toList) (hslot : isEdgeSlot s.n slot)
    (hc : isVertex s.n child) (hp : isVertex s.n parent) (hne : child ≠ parent)
    (hchild : inducedSubPar pathPayload s.splay trees child = slot)
    (hparent : inducedSubPar pathPayload s.splay trees slot = parent)
    (ha : (slot, some value) ∈ forestPairs pathPayload s.splay trees) :
    let next := (lctRerootCost pathPayload s (vid v)).1
    ∃ ts ds, LctInvWith pathPayload next ts free ds ∧
      ((inducedSubPar pathPayload next.splay ts child = slot ∧
        inducedSubPar pathPayload next.splay ts slot = parent ∧
        (slot, some value) ∈ forestPairs pathPayload next.splay ts) ∨
      (inducedSubPar pathPayload next.splay ts parent = slot ∧
        inducedSubPar pathPayload next.splay ts slot = child ∧
        (slot, some value.reverse) ∈ forestPairs pathPayload next.splay ts)) := by
  dsimp only
  obtain ⟨ts, ds, hn, haccount⟩ := treeEdit_reroot_account_parent hi hv hparent
    (by have := hp.1; omega) ha
  obtain ⟨us, du, hu, hperm, hends⟩ := treeEdit_reroot_edge_endpoints hi hv
  obtain ⟨hag, hpar⟩ := treeEdit_witness_agreement hu hn
  have he := hends slot hs hslot child parent hc hp hchild hparent
  rw [hpar] at he
  refine ⟨ts, ds, hn, ?_⟩
  rcases haccount with ⟨hstay, ha'⟩ | ⟨hback, ha'⟩
  · rcases he with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact Or.inl ⟨h1, h2, ha'⟩
    · exact (hne (h2.symm.trans hstay)).elim
  · rcases he with ⟨_, h2⟩ | ⟨h1, h2⟩
    · have hslotActive := hag.mem_iff.mp (hperm.mem_iff.mpr hs)
      have hparNZ : inducedSubPar pathPayload (lctRerootCost pathPayload s (vid v)).1.splay ts slot ≠ 0 :=
        fun hz => by rw [h2] at hz; have := hp.1; omega
      have hparActive := hn.subPar_mem_active hslotActive hparNZ
      rw [h2] at hparActive
      have h1 := hn.acyclic slot hslotActive hparNZ
      have h2' := hn.acyclic parent hparActive (by rw [hback]; have := hslot.1; omega)
      rw [h2] at h1
      rw [hback] at h2'
      exact (Nat.lt_asymm h1 h2').elim
    · exact Or.inr ⟨h1, h2, ha'⟩

/-- Both structural witnesses of a fixed state evaluate the same accounts. -/
theorem treeEdit_account_witness_agreement {s : PathTreeState}
    {ts us : List AuxTree} {fs gs : List ℕ} {d e : ℕ → ℕ}
    (ht : LctInvWith pathPayload s ts fs d) (hu : LctInvWith pathPayload s us gs e) :
    (forestPairs pathPayload s.splay ts).Perm (forestPairs pathPayload s.splay us) :=
  ((LctInvWith_canon_perm ht).2.2.2.symm.trans (LctInvWith_canon_perm hu).2.2.2).flatMap
    (fun _ _ => List.Perm.refl _)

/-- Link installs the supplied evaluated account at the free-head slot.
Its parent and child match the two endpoint arguments, in that order. -/
theorem treeEdit_link_new_account {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) (value : PathEdgeValue) :
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ ts fs ds, LctInvWith pathPayload next ts fs ds ∧
      inducedSubPar pathPayload next.splay ts (vid v) = s.freeHead ∧
      inducedSubPar pathPayload next.splay ts s.freeHead = vid u ∧
      (s.freeHead, some value) ∈ forestPairs pathPayload next.splay ts := by
  dsimp only
  have hdisc := fun h => hd ((pathTreeConnected_iff_induced_roots hi hu hv).mpr h)
  have hnonempty := (hi.freeHead_ne_zero_of_two_roots hu hv hdisc).1
  cases free with
  | nil => exact (hnonempty rfl).elim
  | cons fresh rest =>
    have hfresh : s.freeHead = fresh := hi.freeListInv.2.1
    have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
    have hvV : isVertex s.n (vid v) := by unfold isVertex vid; omega
    obtain ⟨_, _, ts, ds, _, hnext, _, _, hpv, hpf, _, haccounts, _⟩ :=
      lctLink_spec pathPayload_laws hi rfl huV hvV hdisc (some value)
    refine ⟨ts, rest, ds, hnext, hfresh.symm ▸ hpv, hfresh.symm ▸ hpf, ?_⟩
    rw [hfresh]
    exact haccounts.mem_iff.mpr List.mem_cons_self

/-- After Cut's reroot, the splice retains every evaluated account except
that of the removed slot. -/
theorem treeEdit_cut_surviving_accounts {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v slot : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : isVertex s.n u) (hv : isVertex s.n v) (hne : u ≠ v)
    (hactive : slot ∈ trees.flatMap AuxTree.toList)
    (hAdj : (inducedSubPar pathPayload s.splay trees v = slot ∧
        inducedSubPar pathPayload s.splay trees slot = u) ∨
      (inducedSubPar pathPayload s.splay trees u = slot ∧
        inducedSubPar pathPayload s.splay trees slot = v)) :
    let mid := (lctRerootCost pathPayload s u).1
    let next := lctCut pathPayload s u v
    ∃ ms md ts ds, LctInvWith pathPayload mid ms free md ∧
      LctInvWith pathPayload next ts (slot :: free) ds ∧
      (∀ k ≠ slot, ∀ account,
        (k, account) ∈ forestPairs pathPayload next.splay ts ↔
        (k, account) ∈ forestPairs pathPayload mid.splay ms) ∧
      (∀ k ∉ [u, slot, v], inducedSubPar pathPayload next.splay ts k =
        inducedSubPar pathPayload mid.splay ms k) ∧
      inducedSubPar pathPayload mid.splay ms u = 0 ∧
      inducedSubPar pathPayload mid.splay ms v = slot := by
  dsimp only
  have h := (lctCut_spec pathPayload_laws hi u v).2.2
  rw [dite_eq_left ⟨hu, hv, hne, slot, hactive, hAdj⟩] at h
  obtain ⟨ms, md, removed, value, ts, ds, hm, ht, _, _, _, hparent, _, hroot, _, _, _, _, hstay, hperm⟩ := h
  obtain ⟨_, _, _, hfree, _⟩ := treeEdit_cut_parent_slot hi hu hv hne hactive hAdj
  have heq : removed = slot := ht.freeListInv.2.1.symm.trans hfree
  rw [heq] at ht hperm hstay hparent
  refine ⟨ms, md, ts, ds, hm, ht, (fun k hk account => ?_), hstay, hroot, hparent⟩
  constructor
  · intro ha
    exact hperm.mem_iff.mp (List.mem_cons_of_mem _ ha)
  · intro ha
    exact (List.mem_cons.mp (hperm.mem_iff.mpr ha)).resolve_left
      (fun he => hk (congrArg Prod.fst he))

/-- Cut preserves a surviving edge's evaluated account, reversing it
only when the edge's parent and child are exchanged. -/
theorem treeEdit_cut_account_endpoints {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v removed slot child parent : ℕ}
    {value : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n) (hne : u ≠ v)
    (hr : removed ∈ trees.flatMap AuxTree.toList)
    (hAdj : (inducedSubPar pathPayload s.splay trees (vid v) = removed ∧
        inducedSubPar pathPayload s.splay trees removed = vid u) ∨
      (inducedSubPar pathPayload s.splay trees (vid u) = removed ∧
        inducedSubPar pathPayload s.splay trees removed = vid v))
    (hs : slot ∈ trees.flatMap AuxTree.toList) (hslot : isEdgeSlot s.n slot)
    (hother : slot ≠ removed) (hc : isVertex s.n child) (hp : isVertex s.n parent)
    (hneq : child ≠ parent)
    (hchild : inducedSubPar pathPayload s.splay trees child = slot)
    (hparent : inducedSubPar pathPayload s.splay trees slot = parent)
    (ha : (slot, some value) ∈ forestPairs pathPayload s.splay trees) :
    let next := lctCut pathPayload s (vid u) (vid v)
    ∃ ts ds, LctInvWith pathPayload next ts (removed :: free) ds ∧
      ((inducedSubPar pathPayload next.splay ts child = slot ∧
        inducedSubPar pathPayload next.splay ts slot = parent ∧
        (slot, some value) ∈ forestPairs pathPayload next.splay ts) ∨
      (inducedSubPar pathPayload next.splay ts parent = slot ∧
        inducedSubPar pathPayload next.splay ts slot = child ∧
        (slot, some value.reverse) ∈ forestPairs pathPayload next.splay ts)) := by
  dsimp only
  have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
  have hvV : isVertex s.n (vid v) := by unfold isVertex vid; omega
  obtain ⟨ms, md, ts, ds, hm, ht, haccounts, hstay, hroot, hcutParent⟩ :=
    treeEdit_cut_surviving_accounts hi huV hvV (by unfold vid; omega) hr hAdj
  obtain ⟨rs, rd, hri, hcases⟩ :=
    treeEdit_reroot_account_endpoints hi hu hs hslot hc hp hneq hchild hparent ha
  obtain ⟨_, hpar⟩ := treeEdit_witness_agreement hri hm
  have hpair := treeEdit_account_witness_agreement hri hm
  have hslotNZ : slot ≠ 0 := by have := hslot.1; omega
  have hslotStay := hstay slot (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => h.elim (fun he => not_vertex_and_edge ⟨huV, he ▸ hslot⟩)
      (fun h => h.elim hother (fun he => not_vertex_and_edge ⟨hvV, he ▸ hslot⟩)))
  have hrslot : isEdgeSlot s.n removed := by
    rw [← treeEditCut_n s (vid u) (vid v)]
    exact ht.freeValid _ List.mem_cons_self
  have hchildStay a (hvtx : isVertex s.n a)
      (ha : inducedSubPar pathPayload (lctRerootCost pathPayload s (vid u)).1.splay ms a = slot) :
      inducedSubPar pathPayload (lctCut pathPayload s (vid u) (vid v)).splay ts a = slot := by
    apply (hstay a ?_).trans ha
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl)
    · exact hslotNZ (ha.symm.trans hroot)
    · exact not_vertex_and_edge ⟨hvtx, hrslot⟩
    · exact hother (ha.symm.trans hcutParent)
  rw [hpar] at hcases
  refine ⟨ts, ds, ht, ?_⟩
  rcases hcases with ⟨hc', hp', ha'⟩ | ⟨hp', hc', ha'⟩
  · exact Or.inl ⟨hchildStay _ hc hc', hslotStay.trans hp',
      (haccounts _ hother _).mpr (hpair.mem_iff.mp ha')⟩
  · exact Or.inr ⟨hchildStay _ hp hp', hslotStay.trans hc',
      (haccounts _ hother _).mpr (hpair.mem_iff.mp ha')⟩

/-- Link preserves the account of an existing edge. The account reverses
if the two reroots exchange that edge's parent and child. -/
theorem treeEdit_link_account_endpoints {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v slot child parent : ℕ}
    {value : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) (inserted : PathEdgeValue)
    (hs : slot ∈ trees.flatMap AuxTree.toList) (hslot : isEdgeSlot s.n slot)
    (hc : isVertex s.n child) (hp : isVertex s.n parent) (hne : child ≠ parent)
    (hchild : inducedSubPar pathPayload s.splay trees child = slot)
    (hparent : inducedSubPar pathPayload s.splay trees slot = parent)
    (ha : (slot, some value) ∈ forestPairs pathPayload s.splay trees) :
    let next := lctLink pathPayload s (vid u) (vid v) (some inserted)
    ∃ ts fs ds, LctInvWith pathPayload next ts fs ds ∧
      ((inducedSubPar pathPayload next.splay ts child = slot ∧
        inducedSubPar pathPayload next.splay ts slot = parent ∧
        (slot, some value) ∈ forestPairs pathPayload next.splay ts) ∨
      (inducedSubPar pathPayload next.splay ts parent = slot ∧
        inducedSubPar pathPayload next.splay ts slot = child ∧
        (slot, some value.reverse) ∈ forestPairs pathPayload next.splay ts)) := by
  dsimp only
  have hdisc := fun h => hd ((pathTreeConnected_iff_induced_roots hi hu hv).mpr h)
  have hnonempty := (hi.freeHead_ne_zero_of_two_roots hu hv hdisc).1
  cases free with
  | nil => exact (hnonempty rfl).elim
  | cons fresh rest =>
    have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
    have hvV : isVertex s.n (vid v) := by unfold isVertex vid; omega
    obtain ⟨ts, ds, nextTrees, nextDepth, hts, hnext, _, _, _, _, hstay, haccounts, _⟩ :=
      lctLink_spec pathPayload_laws hi rfl huV hvV hdisc (some inserted)
    let first := (lctRerootCost pathPayload s (vid v)).1
    let second := (lctRerootCost pathPayload first (vid u)).1
    obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
    obtain ⟨vs, _, dv, _, hvInv, hvPerm, _, hvRoot, _, _, _, _, _, _, _, _, _, hroots, _⟩ :=
      lctReroot_spec pathPayload_laws hi htv hvMem hvV
    have huFirst : u < first.n := hu
    have huFirstV : isVertex first.n (vid u) := huV
    have huActive := hvInv.verticesActive u huFirst
    have hvActive := hvInv.verticesActive v (show v < first.n from hv)
    obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp huActive
    obtain ⟨us, L, du, _, huInv, _, _, _, huPath, huOff, _⟩ :=
      lctReroot_spec pathPayload_laws hvInv htu huMem huFirstV
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
    obtain ⟨as, ad, hai, hfirst⟩ :=
      treeEdit_reroot_account_endpoints hi hv hs hslot hc hp hne hchild hparent ha
    obtain ⟨_, hap⟩ := treeEdit_witness_agreement hai hvInv
    have hab := treeEdit_account_witness_agreement hai hvInv
    rw [hap] at hfirst
    have hsFirst := hvPerm.mem_iff.mpr hs
    have hstayAccount a b (ha : isVertex s.n a)
        (hc' : inducedSubPar pathPayload second.splay ts a = slot)
        (hp' : inducedSubPar pathPayload second.splay ts slot = b)
        (val : PathEdgeValue) (hval : (slot, some val) ∈ forestPairs pathPayload second.splay ts) :
        inducedSubPar pathPayload (lctLink pathPayload s (vid u) (vid v) (some inserted)).splay
            nextTrees a = slot ∧
          inducedSubPar pathPayload (lctLink pathPayload s (vid u) (vid v) (some inserted)).splay
            nextTrees slot = b ∧
          (slot, some val) ∈ forestPairs pathPayload
            (lctLink pathPayload s (vid u) (vid v) (some inserted)).splay nextTrees := by
      have hfFree : fresh ∈ fresh :: rest := List.mem_cons_self
      have hsNe : slot ≠ fresh := fun he =>
        ((hi.partitionSlots slot hslot).mp hs) (he.symm ▸ hfFree)
      have haNe : a ≠ fresh := fun he => not_vertex_and_edge ⟨ha, he.symm ▸ hi.freeValid _ hfFree⟩
      have hvNe : a ≠ vid v := fun he => by
        rw [he, hvZero] at hc'
        have := hslot.1
        omega
      exact ⟨(hstay a hvNe haNe).trans hc',
        (hstay slot (fun he => not_vertex_and_edge ⟨hvV, he ▸ hslot⟩) hsNe).trans hp',
        haccounts.mem_iff.mpr (List.mem_cons_of_mem _ hval)⟩
    refine ⟨nextTrees, rest, nextDepth, hnext, ?_⟩
    rcases hfirst with ⟨hc', hp', hv'⟩ | ⟨hp', hc', hv'⟩
    · obtain ⟨bs, bd, hbi, hsecond⟩ :=
        treeEdit_reroot_account_endpoints hvInv huFirst hsFirst hslot hc hp hne hc' hp'
          (hab.mem_iff.mp hv')
      obtain ⟨_, hpairs⟩ := treeEdit_witness_agreement hbi hts
      have hvals := treeEdit_account_witness_agreement hbi hts
      rw [hpairs] at hsecond
      rcases hsecond with ⟨ha, hb, hv⟩ | ⟨hb, ha, hv⟩
      · exact Or.inl (hstayAccount _ _ hc ha hb _ (hvals.mem_iff.mp hv))
      · exact Or.inr (hstayAccount _ _ hp hb ha _ (hvals.mem_iff.mp hv))
    · obtain ⟨bs, bd, hbi, hsecond⟩ :=
        treeEdit_reroot_account_endpoints hvInv huFirst hsFirst hslot hp hc hne.symm hp' hc'
          (hab.mem_iff.mp hv')
      obtain ⟨_, hpairs⟩ := treeEdit_witness_agreement hbi hts
      have hvals := treeEdit_account_witness_agreement hbi hts
      rw [hpairs] at hsecond
      rcases hsecond with ⟨hb, ha, hv⟩ | ⟨ha, hb, hv⟩
      · exact Or.inr (hstayAccount _ _ hp hb ha _ (hvals.mem_iff.mp hv))
      · exact Or.inl (hstayAccount _ _ hc ha hb _ (hvals.mem_iff.mp (by simpa only [PathEdgeValue.reverse_reverse] using hv)))


/-- An account is expressed in the graph's tail-to-head direction.
The evaluated tree slot uses its reversal when the parent is the head. -/
@[expose] def TreeEditDirectedAccount (s : PathTreeState) (trees : List AuxTree)
    (slot tail head : ℕ) (account : PathEdgeValue) : Prop :=
  let par := inducedSubPar pathPayload s.splay trees
  (par head = slot ∧ par slot = tail ∧
      (slot, some account) ∈ forestPairs pathPayload s.splay trees) ∨
    (par tail = slot ∧ par slot = head ∧
      (slot, some account.reverse) ∈ forestPairs pathPayload s.splay trees)

/-- A change of structural witness preserves the directed account relation. -/
theorem TreeEditDirectedAccount.congr_witness {s : PathTreeState}
    {ts us : List AuxTree} {fs gs : List ℕ} {d e : ℕ → ℕ}
    {slot tail head : ℕ} {account : PathEdgeValue}
    (ht : LctInvWith pathPayload s ts fs d) (hu : LctInvWith pathPayload s us gs e)
    (ha : TreeEditDirectedAccount s ts slot tail head account) :
    TreeEditDirectedAccount s us slot tail head account := by
  obtain ⟨_, hpar⟩ := treeEdit_witness_agreement ht hu
  have hpair := treeEdit_account_witness_agreement ht hu
  unfold TreeEditDirectedAccount at *
  rw [hpar] at ha
  exact ha.imp (fun h => ⟨h.1, h.2.1, hpair.mem_iff.mp h.2.2⟩)
    (fun h => ⟨h.1, h.2.1, hpair.mem_iff.mp h.2.2⟩)

/-- Existing directed accounts survive a Link. -/
theorem TreeEditDirectedAccount.link {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v slot tail head : ℕ}
    {account : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n)
    (hd : ¬ pathTreeConnected s (vid u) (vid v)) (inserted : PathEdgeValue)
    (hs : slot ∈ trees.flatMap AuxTree.toList) (hslot : isEdgeSlot s.n slot)
    (ht : isVertex s.n tail) (hh : isVertex s.n head) (hne : tail ≠ head)
    (ha : TreeEditDirectedAccount s trees slot tail head account) :
    let next := lctLink pathPayload s (vid u) (vid v) (some inserted)
    ∃ ts fs ds, LctInvWith pathPayload next ts fs ds ∧
      TreeEditDirectedAccount next ts slot tail head account := by
  rcases ha with ⟨hc, hp, ha⟩ | ⟨hc, hp, ha⟩
  · exact treeEdit_link_account_endpoints hi hu hv hd inserted hs hslot hh ht hne.symm hc hp ha
  · obtain ⟨ts, fs, ds, hinv, ha⟩ :=
      treeEdit_link_account_endpoints hi hu hv hd inserted hs hslot ht hh hne hc hp ha
    exact ⟨ts, fs, ds, hinv, by simpa only [TreeEditDirectedAccount,
      PathEdgeValue.reverse_reverse, or_comm] using ha⟩

/-- A surviving edge retains its directed account through Cut. -/
theorem TreeEditDirectedAccount.cut {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {u v removed slot tail head : ℕ}
    {account : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (hu : u < s.n) (hv : v < s.n) (hne : u ≠ v)
    (hr : removed ∈ trees.flatMap AuxTree.toList)
    (hAdj : (inducedSubPar pathPayload s.splay trees (vid v) = removed ∧
        inducedSubPar pathPayload s.splay trees removed = vid u) ∨
      (inducedSubPar pathPayload s.splay trees (vid u) = removed ∧
        inducedSubPar pathPayload s.splay trees removed = vid v))
    (hs : slot ∈ trees.flatMap AuxTree.toList) (hslot : isEdgeSlot s.n slot)
    (hother : slot ≠ removed)
    (ht : isVertex s.n tail) (hh : isVertex s.n head) (hne' : tail ≠ head)
    (ha : TreeEditDirectedAccount s trees slot tail head account) :
    let next := lctCut pathPayload s (vid u) (vid v)
    ∃ ts ds, LctInvWith pathPayload next ts (removed :: free) ds ∧
      TreeEditDirectedAccount next ts slot tail head account := by
  rcases ha with ⟨hc, hp, ha⟩ | ⟨hc, hp, ha⟩
  · exact treeEdit_cut_account_endpoints hi hu hv hne hr hAdj hs hslot hother hh ht hne'.symm hc hp ha
  · obtain ⟨ts, ds, hinv, ha⟩ :=
      treeEdit_cut_account_endpoints hi hu hv hne hr hAdj hs hslot hother ht hh hne' hc hp ha
    exact ⟨ts, ds, hinv, by simpa only [TreeEditDirectedAccount,
      PathEdgeValue.reverse_reverse, or_comm] using ha⟩

/-- Reading the slot of a directed account returns the stored value in its
current tree direction. Either representation has the same graph flow. -/
theorem TreeEditDirectedAccount.expose_value {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot tail head : ℕ} {account : PathEdgeValue}
    (hi : LctInvWith pathPayload s trees free depth)
    (ha : TreeEditDirectedAccount s trees slot tail head account) :
    ∃ value, ((lctExpose pathPayload s slot).splay.nodes slot).val = some value ∧
      (value = account ∨ value = account.reverse) ∧ value.originalFlow = account.originalFlow := by
  rcases ha with ⟨_, _, hval⟩ | ⟨_, _, hval⟩
  · exact ⟨account, pathTreeExpose_value_of_forestPair hi hval, Or.inl rfl, rfl⟩
  · exact ⟨account.reverse, pathTreeExpose_value_of_forestPair hi hval, Or.inr rfl,
      account.originalFlow_reverse⟩

/-- A newly linked account denotes the same graph-directed value whether
its off-tree representation was forward or reversed. -/
theorem treeEdit_link_new_directed_account {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {tail head : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (ht : tail < s.n) (hh : head < s.n)
    (hd : ¬ pathTreeConnected s (vid tail) (vid head)) (value : PathEdgeValue) :
    let u := if value.forward then tail else head
    let v := if value.forward then head else tail
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ ts fs ds, LctInvWith pathPayload next ts fs ds ∧
      TreeEditDirectedAccount next ts s.freeHead (vid tail) (vid head)
        (if value.forward then value else value.reverse) := by
  dsimp only
  cases h : value.forward
  · have hd' : ¬ pathTreeConnected s (vid head) (vid tail) := by
      intro hc
      exact hd ((pathTreeConnected_iff_induced_roots hi ht hh).mpr
        ((pathTreeConnected_iff_induced_roots hi hh ht).mp hc).symm)
    obtain ⟨ts, fs, ds, hi', hc, hp, ha⟩ := treeEdit_link_new_account hi hh ht hd' value
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨ts, fs, ds, hi', Or.inr ⟨hc, hp, by simpa only [PathEdgeValue.reverse_reverse] using ha⟩⟩
  · obtain ⟨ts, fs, ds, hi', hc, hp, ha⟩ := treeEdit_link_new_account hi ht hh hd value
    simp only [ite_true]
    exact ⟨ts, fs, ds, hi', Or.inl ⟨hc, hp, ha⟩⟩

/-- Every live edge in the named forest has its graph-directed account. -/
@[expose] def TreeEditLiveAccounts (s : PathTreeState) (trees : List AuxTree)
    (G : MGraph) (slot : ℕ → ℕ) (account : ℕ → PathEdgeValue) : Prop :=
  ∀ e ∈ G.E, TreeEditDirectedAccount s trees (slot e) (vid (G.tail e)) (vid (G.head e)) (account e)

/-- Exposing any named edge preserves the directed accounts of all live edges. -/
theorem TreeEditLiveAccounts.expose {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ}
    {e : ℕ} {account : ℕ → PathEdgeValue}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth) (he : e ∈ G.E)
    (ha : TreeEditLiveAccounts s trees G slot account) :
    let next := lctExpose pathPayload s (slot e)
    ∃ ts, LctInvWith pathPayload next ts free depth ∧
      TreeEditNamedSlots next ts G slot name ∧ TreeEditLiveAccounts next ts G slot account := by
  dsimp only
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.mp (hn.forward e he).1
  obtain ⟨ts, _, _, hi', _, hpar, hperm, _⟩ :=
    lctExpose_spec pathPayload_laws hi ht hs
  obtain ⟨us, hu, hn', _⟩ := hn.expose hi he
  refine ⟨us, hu, hn', fun f hf => ?_⟩
  apply TreeEditDirectedAccount.congr_witness hi' hu
  have h := ha f hf
  unfold TreeEditDirectedAccount at *
  dsimp only
  simp only [hpar]
  exact h.imp (fun h => ⟨h.1, h.2.1, hperm.mem_iff.mpr h.2.2⟩)
    (fun h => ⟨h.1, h.2.1, hperm.mem_iff.mpr h.2.2⟩)

/-- Expose and Cut retain the graph-directed account of each surviving name. -/
theorem TreeEditLiveAccounts.cut_exposed {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ}
    {e : ℕ} {account : ℕ → PathEdgeValue}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (hne : ∀ f ∈ G.E, G.tail f ≠ G.head f)
    (he : e ∈ G.E) (ha : TreeEditLiveAccounts s trees G slot account) :
    let exposed := lctExpose pathPayload s (slot e)
    let next := lctCut pathPayload exposed (vid (G.tail e)) (vid (G.head e))
    ∃ ts ds, LctInvWith pathPayload next ts (slot e :: free) ds ∧
      TreeEditNamedSlots next ts { G with E := G.E.erase e } slot name ∧
      TreeEditLiveAccounts next ts { G with E := G.E.erase e } slot account := by
  dsimp only
  obtain ⟨xs, hx, hnames, haccounts⟩ := ha.expose hn hi he
  obtain ⟨ts, ds, ht, hnamed⟩ := hnames.cut hx hv he (hne e he)
  refine ⟨ts, ds, ht, hnamed, fun f hf => ?_⟩
  obtain ⟨hfe, hf⟩ := Finset.mem_erase.mp hf
  have hslot : slot f ≠ slot e := fun h =>
    hfe ((hn.forward f hf).2.2.symm.trans ((congrArg name h).trans (hn.forward e he).2.2))
  have hvertex n (h : n < s.n) : isVertex s.n (vid n) := by unfold vid isVertex; omega
  have hfne : vid (G.tail f) ≠ vid (G.head f) := fun h => (hne f hf) (Nat.add_right_cancel h)
  obtain ⟨us, ud, hu, ha'⟩ := (haccounts f hf).cut hx (hv e he).1 (hv e he).2 (hne e he)
    (hnames.forward e he).1 (hnames.endpoints e he).symm
    (hnames.forward f hf).1 (hnames.forward f hf).2.1 hslot
    (hvertex _ (hv f hf).1) (hvertex _ (hv f hf).2) hfne
  exact ha'.congr_witness hu ht

/-- Oriented Link retains the old accounts and adds the new graph-directed account. -/
theorem TreeEditLiveAccounts.link {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ}
    {e : ℕ} {account : ℕ → PathEdgeValue}
    (hn : TreeEditNamedSlots s trees G slot name)
    (hi : LctInvWith pathPayload s trees free depth)
    (hv : ∀ f ∈ G.E, G.tail f < s.n ∧ G.head f < s.n)
    (hne : ∀ f ∈ G.E, G.tail f ≠ G.head f)
    (he : e ∉ G.E) (ht : G.tail e < s.n) (hh : G.head e < s.n)
    (hd : ¬ pathTreeConnected s (vid (G.tail e)) (vid (G.head e)))
    (ha : TreeEditLiveAccounts s trees G slot account) (value : PathEdgeValue) :
    let u := if value.forward then G.tail e else G.head e
    let v := if value.forward then G.head e else G.tail e
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    ∃ ts fs ds, LctInvWith pathPayload next ts fs ds ∧
      TreeEditNamedSlots next ts { G with E := insert e G.E }
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) ∧
      TreeEditLiveAccounts next ts { G with E := insert e G.E }
        (Function.update slot e s.freeHead) (Function.update account e
          (if value.forward then value else value.reverse)) := by
  dsimp only
  obtain ⟨ts, fs, ds, hi', hn'⟩ := hn.link_oriented hi hv he ht hh hd value value.forward
  refine ⟨ts, fs, ds, hi', hn', fun f hf => ?_⟩
  rcases Finset.mem_insert.mp hf with rfl | hf
  · obtain ⟨us, uf, ud, hu, hnew⟩ := treeEdit_link_new_directed_account hi ht hh hd value
    simpa only [Function.update_self] using hnew.congr_witness hu hi'
  · have hfe : f ≠ e := fun h => he (h ▸ hf)
    have hvertex n (h : n < s.n) : isVertex s.n (vid n) := by unfold vid isVertex; omega
    have hfne : vid (G.tail f) ≠ vid (G.head f) := fun h => (hne f hf) (Nat.add_right_cancel h)
    have hs := hn.forward f hf
    have hbounds := hv f hf
    have hrel := ha f hf
    have hswap : ¬ pathTreeConnected s (vid (G.head e)) (vid (G.tail e)) := by
      intro hc
      exact hd ((pathTreeConnected_iff_induced_roots hi ht hh).mpr
        ((pathTreeConnected_iff_induced_roots hi hh ht).mp hc).symm)
    cases h : value.forward
    · have ht' := hi'
      simp only [h, Bool.false_eq_true, ite_false] at ht' ⊢
      obtain ⟨us, uf, ud, hu, hval⟩ := hrel.link hi hh ht hswap value hs.1 hs.2.1
        (hvertex _ hbounds.1) (hvertex _ hbounds.2) hfne
      simpa only [Function.update_of_ne hfe] using hval.congr_witness hu ht'
    · have ht' := hi'
      simp only [h, ite_true] at ht' ⊢
      obtain ⟨us, uf, ud, hu, hval⟩ := hrel.link hi ht hh hd value hs.1 hs.2.1
        (hvertex _ hbounds.1) (hvertex _ hbounds.2) hfne
      simpa only [Function.update_of_ne hfe] using hval.congr_witness hu ht'

/-- The live edges after the processed edits carry graph-directed accounts. -/
@[expose] def TreeEditAccountPrefix (current : PathTreeState) (oldG newG ambient : MGraph)
    (remaining : List TreeChange) (slot name : ℕ → ℕ) (account : ℕ → PathEdgeValue) : Prop :=
  ∃ processed trees free depth,
    TreeEditDifference oldG.E newG.E (processed ++ remaining) ∧
    LctInvWith pathPayload current trees free depth ∧
    TreeEditNamedSlots current trees { ambient with E := applyTreeChanges oldG.E processed } slot name ∧
    (∀ f ∈ applyTreeChanges oldG.E processed, ambient.tail f < current.n ∧ ambient.head f < current.n) ∧
    TreeEditLiveAccounts current trees { ambient with E := applyTreeChanges oldG.E processed } slot account

/-- Forgetting accounts gives the named structural cursor. -/
theorem TreeEditAccountPrefix.to_named {s : PathTreeState} {oldG newG ambient : MGraph}
    {rest : List TreeChange} {slot name : ℕ → ℕ} {account : ℕ → PathEdgeValue}
    (hp : TreeEditAccountPrefix s oldG newG ambient rest slot name account) :
    TreeEditNamedPrefix s oldG newG ambient rest slot name := by
  obtain ⟨done, ts, fs, ds, hd, hi, hn, hb, _⟩ := hp
  exact ⟨done, ts, fs, ds, hd, hi, hn, hb⟩

/-- The pending deletion's slot yields a copy of its graph-directed account. -/
theorem TreeEditAccountPrefix.delete_value {s : PathTreeState} {oldG newG ambient : MGraph}
    {e : ℕ} {rest : List TreeChange} {slot name : ℕ → ℕ} {account : ℕ → PathEdgeValue}
    (hp : TreeEditAccountPrefix s oldG newG ambient (.delete e :: rest) slot name account) :
    ∃ value, ((lctExpose pathPayload s (slot e)).splay.nodes (slot e)).val = some value ∧
      (value = account e ∨ value = (account e).reverse) ∧
      value.originalFlow = (account e).originalFlow := by
  obtain ⟨_, _, _, _, hd, hi, _, _, ha⟩ := hp
  exact (ha e (hd.delete_live rfl)).expose_value hi

/-- Live incidences cannot form a loop through an active edge slot. -/
theorem named_account_endpoints_ne {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {G : MGraph} {slot name : ℕ → ℕ} {f : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees G slot name) (hf : f ∈ G.E)
    (hb : G.tail f < s.n) : G.tail f ≠ G.head f := by
  intro he
  have h := hn.endpoints f hf
  simp only [← he, or_self] at h
  obtain ⟨hchild, hparent⟩ := h
  have hs := hn.forward f hf
  have h1 := hi.acyclic (vid (G.tail f)) (hi.verticesActive _ hb)
    (by rw [hchild]; have := hs.2.1.1; omega)
  have h2 := hi.acyclic (slot f) hs.1 (by rw [hparent]; simp [vid])
  rw [hchild] at h1
  rw [hparent] at h2
  exact Nat.lt_asymm h1 h2

/-- Advancing the deletion cursor retains all surviving live accounts. -/
theorem TreeEditAccountPrefix.advance_delete {s : PathTreeState} {oldG newG ambient : MGraph}
    {e : ℕ} {rest : List TreeChange} {slot name : ℕ → ℕ} {account : ℕ → PathEdgeValue}
    (hp : TreeEditAccountPrefix s oldG newG ambient (.delete e :: rest) slot name account)
    (hOld : ∀ f ∈ oldG.E, ambient.tail f = oldG.tail f ∧ ambient.head f = oldG.head f) :
    TreeEditAccountPrefix
      (lctCut pathPayload (lctExpose pathPayload s (slot e)) (vid (oldG.tail e)) (vid (oldG.head e)))
      oldG newG ambient rest slot name account := by
  obtain ⟨done, ts, fs, ds, hd, hi, hn, hb, ha⟩ := hp
  have he := hd.delete_live rfl
  obtain ⟨htail, hhead⟩ := hOld e (Finset.mem_sdiff.mp (hd.delete_mem_sdiff (by simp))).1
  obtain ⟨us, ud, hu, hnamed, haccounts⟩ :=
    ha.cut_exposed hn hi hb (fun f hf => named_account_endpoints_ne hi hn hf (hb f hf).1) he
  have hset : applyTreeChanges oldG.E (done ++ [.delete e]) =
      (applyTreeChanges oldG.E done).erase e := by
    unfold applyTreeChanges
    rw [List.foldl_append]
    rfl
  have hnsize : (lctCut pathPayload (lctExpose pathPayload s (slot e))
      (vid (oldG.tail e)) (vid (oldG.head e))).n = s.n :=
    (treeEditCut_n _ _ _).trans rfl
  simp only [htail, hhead] at hu hnamed haccounts
  refine ⟨done ++ [.delete e], us, slot e :: fs, ud,
    by simpa only [List.append_assoc, List.singleton_append] using hd,
    hu, by simpa only [hset] using hnamed, ?_, by simpa only [hset] using haccounts⟩
  intro f hf
  rw [hset] at hf
  rw [hnsize]
  exact hb f (Finset.mem_erase.mp hf).2

/-- Advancing the insertion cursor assigns the new account and retains the
graph-directed accounts of all names already present. -/
theorem TreeEditAccountPrefix.advance_insert {s : PathTreeState} {oldG newG ambient : MGraph}
    {e : ℕ} {rest : List TreeChange} {slot name : ℕ → ℕ} {account : ℕ → PathEdgeValue}
    (hp : TreeEditAccountPrefix s oldG newG ambient (.insert e :: rest) slot name account)
    (hforest : newG.IsForest)
    (hEnds : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f)
    (hBound : ∀ f ∈ newG.E, ambient.tail f < s.n ∧ ambient.head f < s.n)
    (value : PathEdgeValue) :
    let u := if value.forward then newG.tail e else newG.head e
    let v := if value.forward then newG.head e else newG.tail e
    let next := lctLink pathPayload s (vid u) (vid v) (some value)
    TreeEditAccountPrefix next oldG newG ambient rest
      (Function.update slot e s.freeHead) (Function.update name s.freeHead e)
      (Function.update account e (if value.forward then value else value.reverse)) := by
  dsimp only
  have hNamed := hp.to_named
  obtain ⟨done, ts, fs, ds, hd, hi, hn, hb, ha⟩ := hp
  obtain ⟨hsub, he, hem⟩ := hd.insert_cursor rfl
  have hends f (hf : f ∈ newG.E) := hEnds f hf
  have hBound' f (hf : f ∈ newG.E) : newG.tail f < s.n ∧ newG.head f < s.n := by
    obtain ⟨ht, hh⟩ := hends f hf
    simpa only [ht, hh] using hBound f hf
  let part := { newG with E := applyTreeChanges oldG.E done }
  have hnames : TreeEditNamedSlots s ts part slot name :=
    hn.congrGraph rfl (fun f hf => ⟨(hends f (hsub hf)).1.symm, (hends f (hsub hf)).2.symm⟩)
  have hlive : TreeEditLiveAccounts s ts part slot account := by
    intro f hf
    obtain ⟨ht, hh⟩ := hends f (hsub hf)
    simpa only [ht, hh] using ha f hf
  have hpartBound : ∀ f ∈ part.E, part.tail f < s.n ∧ part.head f < s.n :=
    fun f hf => hBound' f (hsub hf)
  have hconn := hNamed.insert_disconnected hforest hEnds (hBound' e hem).1 (hBound' e hem).2
  obtain ⟨us, uf, ud, hi', hn', ha'⟩ := hlive.link hnames hi hpartBound
    (fun f hf => named_account_endpoints_ne hi hnames hf (hpartBound f hf).1)
    he (hBound' e hem).1 (hBound' e hem).2 hconn value
  have hset : applyTreeChanges oldG.E (done ++ [.insert e]) =
      insert e (applyTreeChanges oldG.E done) := by
    unfold applyTreeChanges
    rw [List.foldl_append]
    rfl
  have hMem f (hf : f ∈ applyTreeChanges oldG.E (done ++ [.insert e])) : f ∈ newG.E := by
    rw [hset] at hf
    exact (Finset.mem_insert.mp hf).elim (fun h => h.symm ▸ hem) (fun h => hsub h)
  have hsize : (lctLink pathPayload s
      (vid (if value.forward then newG.tail e else newG.head e))
      (vid (if value.forward then newG.head e else newG.tail e)) (some value)).n = s.n :=
    treeEditApply_n oldG { newG with
      tail := fun _ => if value.forward then newG.tail e else newG.head e
      head := fun _ => if value.forward then newG.head e else newG.tail e } (fun _ => value) s (.insert e)
  refine ⟨done ++ [.insert e], us, uf, ud,
    by simpa only [List.append_assoc, List.singleton_append] using hd, hi',
    hn'.congrGraph hset (fun f hf => hEnds f (hMem f hf)), ?_, ?_⟩
  · intro f hf
    rw [hsize]
    exact hBound f (hMem f hf)
  · intro f hf
    obtain ⟨ht, hh⟩ := hEnds f (hMem f hf)
    rw [ht, hh]
    exact ha' f (hset ▸ hf)

/-- When the cursor is exhausted, the target forest carries all its live accounts. -/
theorem TreeEditAccountPrefix.finish {s : PathTreeState} {oldG newG ambient : MGraph}
    {slot name : ℕ → ℕ} {account : ℕ → PathEdgeValue}
    (hp : TreeEditAccountPrefix s oldG newG ambient [] slot name account)
    (hEnds : ∀ f ∈ newG.E, ambient.tail f = newG.tail f ∧ ambient.head f = newG.head f) :
    ∃ ts fs ds, LctInvWith pathPayload s ts fs ds ∧ TreeEditNamedSlots s ts newG slot name ∧
      TreeEditLiveAccounts s ts newG slot account := by
  obtain ⟨done, ts, fs, ds, hd, hi, hn, _, ha⟩ := hp
  rw [List.append_nil] at hd
  have hE := hd.result.2
  refine ⟨ts, fs, ds, hi,
    hn.congrGraph hE.symm (fun f hf => ⟨(hEnds f hf).1.symm, (hEnds f hf).2.symm⟩), ?_⟩
  intro f hf
  simpa only [(hEnds f hf).1, (hEnds f hf).2] using ha f (hE.symm ▸ hf)

end MinCostFlow.MinRatio
