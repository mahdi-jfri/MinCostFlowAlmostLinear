module

public import MinCostFlow.MinRatio.TreeEditAccountDirection
public import MinCostFlow.MinRatio.PathNumericHistory
public import MinCostFlow.MinRatio.SparseCoreContract
public import MinCostFlow.MinRatio.LastLevelContract
public import MinCostFlow.Chain.TreeChain
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.LSF.Walks
import Mathlib.Tactic.Ring

/-!
# Inserting the initial spanning forest into the Section 6 path tree

At the end of Init in Theorem 5.1 (pages 29–30), the active spanning forest
`T = chain.toTreeChain.chainTree` is the disjoint union of the level forests
`(chain.toTreeChain.activeLSF i).F.F` for `0 ≤ i ≤ d`. Starting from the empty
link-cut forest `lctInit pathPayload G.n none`, this module links every edge of
each level forest using its root endpoints from `G` and its pre-built initial
`PathEdgeAt` record, binds `slots[e]` and `names[slot]` via `pathSlotBindContract`,
and copies `edgeThresholds[e]` into `slotThresholds[slot]`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- State invariant while inserting a subset `inserted ⊆ T.E` of the initial
spanning forest `T` (a subgraph forest of `G`) into the Section 6 path tree. -/
@[expose] def InitPathTreeInv (R : DSRep PathTreeState) (treeHandle : ℕ)
    (G T : MGraph) (val : ℕ → PathEdgeValue) (B : ℤ)
    (slots names slotThresholds m : ℕ) (thPtr : ℕ → ℕ)
    (inserted : Finset ℕ) (s : PathTreeState) (x : R.τ) (slot name : ℕ → ℕ)
    (heap : ℕ) (mem : ℕ → ℕ) : Prop :=
  s.n = G.n ∧
  inserted ⊆ T.E ∧
  R.rep treeHandle s x mem ∧
  (∀ a, R.foot treeHandle x a → a < heap) ∧
  PathSlotTablesAt mem slots names m (2 * G.n) slot name ∧
  (∃ ts fs ds,
    LctInvWith pathPayload s ts fs ds ∧
    PathTreeNumericInv s ts B 0 ∧
    TreeEditNamedSlots s ts { T with E := inserted } slot name ∧
    TreeEditLiveAccounts s ts { T with E := inserted } slot val) ∧
  (∀ e ∈ inserted, mem (slotThresholds + slot e) = thPtr e) ∧
  (∀ e < m, e ∉ inserted → slot e = 0)

/-- The empty link-cut forest `lctInit pathPayload G.n none` with zeroed slot
tables satisfies `InitPathTreeInv` for `inserted = ∅`. -/
theorem initPathTreeInv_empty {R : DSRep PathTreeState} {treeHandle slots names slotThresholds m heap : ℕ}
    {G T : MGraph} {val : ℕ → PathEdgeValue} {B : ℤ} {thPtr : ℕ → ℕ}
    {x : R.τ} {mem : ℕ → ℕ}
    (hB : 0 ≤ B)
    (hrep : R.rep treeHandle (lctInit pathPayload G.n none) x mem)
    (hfoot : ∀ a, R.foot treeHandle x a → a < heap)
    (hslotsZ : ∀ e < m, mem (slots + e) = 0)
    (hnamesZ : ∀ k < 2 * G.n, mem (names + k) = 0) :
    InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
      ∅ (lctInit pathPayload G.n none) x (fun _ => 0) (fun _ => 0) heap mem := by
  obtain ⟨W, hnum⟩ := pathTreeNumericInv_init G.n hB
  refine ⟨rfl, Finset.empty_subset _, hrep, hfoot, ⟨hslotsZ, hnamesZ⟩,
    ⟨_, _, _, W, hnum, ?_, ?_⟩, fun _ he => (Finset.notMem_empty _ he).elim, fun _ _ _ => rfl⟩
  · refine ⟨fun _ he => (Finset.notMem_empty _ he).elim, ?_, fun _ he => (Finset.notMem_empty _ he).elim⟩
    intro k hk hkEdge
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hk
    obtain ⟨_, ⟨i, hi, rfl⟩, hki⟩ := hk
    simp only [AuxTree.toList, List.nil_append, List.append_nil, List.mem_singleton] at hki
    have hge : G.n + 1 ≤ k := hkEdge.1
    subst hki; unfold vid at hge; omega
  · intro e he; exact (Finset.notMem_empty _ he).elim

/-- Link one edge at index `regs 26` of the edge list in `regs 28`, bind its
forward and inverse slots, and record its Detect threshold pointer in
`slotThresholds[slot]`.
Registers: `0 = treeHandle`, `3 = heap`, `9/10/11 = root graph endpoint bases`,
`19 = slots`, `20 = names`, `22 = edgeRecords`, `23 = edgeThresholds`,
`24 = slotThresholds`, `26 = edge index`, `28 = forest edge list base`. -/
@[expose] def initLinkSingleEdge (linkOp bind : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 28) (.reg 26))) ;;
  .assign 4 (.load (.bin .add (.reg 22) (.reg 8))) ;;
  .assign 21 (.reg 3) ;;
  ((treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink linkOp) ;;
  treeEditBindSlot bind ;;
  .store (.bin .add (.reg 24) (.load (.reg 21))) (.load (.bin .add (.reg 23) (.reg 8)))

theorem initLinkSingleEdge_noRand (linkOp bind : ℕ) : (initLinkSingleEdge linkOp bind).NoRand := by
  simp [initLinkSingleEdge, treeEditEndpoints, treeEditVertexIndices, treeEditLink,
    treeEditBindSlot, Stmt.NoRand]

/-- Link every edge of the dynamic graph pointed to by `regs 25` into the
Section 6 path tree. -/
@[expose] def initLinkForestEdges (linkOp bind : ℕ) : Stmt :=
  .assign 27 (.load (.bin .add (.reg 25) (.const 3))) ;;
  .assign 28 (.bin .add (.bin .add (.bin .add (.reg 25) (.const 4))
    (.bin .mul (.const 7) (.load (.reg 25))))
    (.load (.bin .add (.reg 25) (.const 1)))) ;;
  .assign 26 (.const 0) ;;
  .loop (.bin .lt (.reg 26) (.reg 27))
    (initLinkSingleEdge linkOp bind ;; .assign 26 (.bin .add (.reg 26) (.const 1)))

theorem initLinkForestEdges_noRand (linkOp bind : ℕ) : (initLinkForestEdges linkOp bind).NoRand := by
  simp [initLinkForestEdges, initLinkSingleEdge_noRand, Stmt.NoRand]

/-- Iterate over all levels `0 .. d` of the initialized chain: read each level's
active forest via `readCore` (`op_core 2`) and advance the level graph via
`readGraph` (`op_core 3`), then read the terminal forest via `readLast`
(`op_last 0`), linking every active forest edge into the Section 6 path tree.
Additional registers: `29 = levelTable`, `30 = branchTable`, `31 = d`,
`34 = current level graph pointer` (initially `rootBase`). -/
@[expose] def initLinkChainForests (readCore readGraph readLast linkOp bind : ℕ) : Stmt :=
  .assign 32 (.const 0) ;;
  .loop (.bin .lt (.reg 32) (.reg 31)) (
    .assign 33 (.reg 3) ;;
    .call 3 readCore [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 34, .reg 3] ;;
    .assign 25 (.load (.bin .add (.reg 33) (.const 1))) ;;
    initLinkForestEdges linkOp bind ;;
    .assign 33 (.reg 3) ;;
    .call 3 readGraph [.load (.bin .add (.reg 29) (.reg 32)),
      .load (.bin .add (.reg 30) (.reg 32)), .reg 3] ;;
    .assign 34 (.load (.reg 33)) ;;
    .assign 32 (.bin .add (.reg 32) (.const 1))
  ) ;;
  .assign 33 (.reg 3) ;;
  .call 3 readLast [.load (.bin .add (.reg 29) (.reg 31)),
    .load (.bin .add (.reg 30) (.reg 31)), .reg 3] ;;
  .assign 25 (.load (.bin .add (.reg 33) (.const 1))) ;;
  initLinkForestEdges linkOp bind

theorem initLinkChainForests_noRand (readCore readGraph readLast linkOp bind : ℕ) :
    (initLinkChainForests readCore readGraph readLast linkOp bind).NoRand := by
  simp [initLinkChainForests, initLinkForestEdges_noRand, Stmt.NoRand]

/-- Region disjointness from the three slot tables written during initial path
tree edge insertion (`slots`, `names`, `slotThresholds`). -/
@[expose] def OutsideInitSlotTables (slots names slotThresholds m n a : ℕ) : Prop :=
  (a < slots ∨ slots + m ≤ a) ∧
  (a < names ∨ names + 2 * n ≤ a) ∧
  (a < slotThresholds ∨ slotThresholds + 2 * n ≤ a)

private theorem lctLink_vertexCount (s : PathTreeState) (u v : ℕ) (value : Option PathEdgeValue) :
    (lctLink pathPayload s u v value).n = s.n := by
  unfold lctLink lctLinkCost
  split
  · rfl
  · dsimp only
    split <;> rfl

private theorem namedSlots_congr_witness {s : PathTreeState}
    {ts us : List AuxTree} {fs gs : List ℕ} {d e : ℕ → ℕ}
    {G : MGraph} {slot name : ℕ → ℕ}
    (ht : LctInvWith pathPayload s ts fs d) (hu : LctInvWith pathPayload s us gs e)
    (hn : TreeEditNamedSlots s ts G slot name) : TreeEditNamedSlots s us G slot name := by
  obtain ⟨hperm, hpar⟩ := treeEdit_witness_agreement ht hu
  refine ⟨fun f hf => ?_, fun k hk hkE => hn.inverse k (hperm.mem_iff.mpr hk) hkE, fun f hf => ?_⟩
  · obtain ⟨ha, hs, hname⟩ := hn.forward f hf
    exact ⟨hperm.mem_iff.mp ha, hs, hname⟩
  · have he := hn.endpoints f hf
    dsimp only at he ⊢
    rwa [← hpar]

private theorem initLinkSingleEdge_runs {w L constant init bind treeHandle rootBase ec m
    slots names slotThresholds edgeRecords edgeThresholds eListBase idx e heap linkSpace : ℕ}
    {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState} {op : ℕ → ℕ}
    {G T : MGraph} {val : ℕ → PathEdgeValue} {B : ℤ} {recPtr thPtr : ℕ → ℕ}
    {inserted : Finset ℕ} {s : PathTreeState} {x : R.τ} {slot name : ℕ → ℕ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hTForest : T.IsForest)
    (hTEnds : ∀ f ∈ T.E, T.tail f = G.tail f ∧ T.head f = G.head f)
    (hG : DynGraphAt st.mem rootBase G.n ec G)
    (hTG : T.E ⊆ G.E) (hELt : ∀ e ∈ G.E, e < m)
    (heT : e ∈ T.E) (heNot : e ∉ inserted)
    (hinv : InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
      inserted s x slot name heap st.mem)
    (hvalFwd : (val e).forward = true)
    (hvalB : |((val e).gradient)| ≤ B ∧ |((val e).length)| ≤ B ∧
      |((val e).flow)| ≤ B ∧ |((val e).detector)| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity fmt.limbBits L : ℤ))
    (h0 : st.regs 0 = treeHandle) (h3 : st.regs 3 = heap)
    (h9 : st.regs 9 = dgETailSlotBase rootBase G.n ec)
    (h10 : st.regs 10 = dgEHeadSlotBase rootBase G.n ec)
    (h11 : st.regs 11 = dgIntToExtBase rootBase G.n)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (h22 : st.regs 22 = edgeRecords) (h23 : st.regs 23 = edgeThresholds)
    (h24 : st.regs 24 = slotThresholds)
    (h26 : st.regs 26 = idx) (h28 : st.regs 28 = eListBase)
    (heAt : st.mem (eListBase + idx) = e)
    (heListW : eListBase + idx < 2 ^ w)
    (hrecPtr : st.mem (edgeRecords + e) = recPtr e)
    (hrecAt : PathEdgeAt st.mem (recPtr e) fmt.limbBits L (some (val e)))
    (hthPtrAt : st.mem (edgeThresholds + e) = thPtr e)
    (hrecBelow : recPtr e + (2 + 4 * L) ≤ heap)
    (hrecPtrW : edgeRecords + e < 2 ^ w)
    (hthPtrW : edgeThresholds + e < 2 ^ w)
    (hrootRoom : rootBase + dynGraphSize G.n ec ≤ 2 ^ w)
    (hslotsBelow : slots + m ≤ heap) (hnamesBelow : names + 2 * G.n ≤ heap)
    (hstBelow : slotThresholds + 2 * G.n ≤ heap)
    (hdisjSN : slots + m ≤ names ∨ names + 2 * G.n ≤ slots)
    (hdisjST : slots + m ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ slots)
    (hdisjNT : names + 2 * G.n ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ names)
    (hfootOut : ∀ a, R.foot treeHandle x a → OutsideInitSlotTables slots names slotThresholds m G.n a)
    (hthOut : OutsideInitSlotTables slots names slotThresholds m G.n (edgeThresholds + e))
    (hthFoot : ¬ R.foot treeHandle x (edgeThresholds + e))
    (hthBelow : edgeThresholds + e < heap)
    (hthValW : thPtr e < 2 ^ w)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ fmt.limbBits * L)
    (hhandleW : treeHandle < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hspace : allocation 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, heap] ≤ linkSpace)
    (hroom : heap + linkSpace < 2 ^ w) :
    let next := lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e))
    ∃ out ret cost y,
      Runs w p ω (initLinkSingleEdge (op 0) bind) st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 8 → r ≠ 21 → out.regs r = st.regs r) ∧
      InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
        (insert e inserted) next y
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) ret out.mem ∧
      (∀ a, R.foot treeHandle y a → OutsideInitSlotTables slots names slotThresholds m G.n a) ∧
      R.Respects (fun a => R.foot treeHandle x a ∨
        ¬ OutsideInitSlotTables slots names slotThresholds m G.n a)
        heap linkSpace st.mem ret treeHandle y out.mem ∧
      cost + R.phi treeHandle y out.mem ≤
        pathTreeBudget constant L G.n + R.phi treeHandle x st.mem + 85 := by
  dsimp only
  obtain ⟨hsn, hinsSub, hrep, hfoot, htab, ⟨ts, fs, ds, hW, hnum, hnamed, hlive⟩, hstTab, hzeroSlot⟩ := hinv
  have heG : e ∈ G.E := hTG heT
  have heCap : e < m := hELt e heG
  have hep : TreeEditEndpointAt st.mem rootBase G.n ec G e := TreeEditEndpointAt.of_graph hG heG
  have hTe : T.tail e = G.tail e ∧ T.head e = G.head e := hTEnds e heT
  have hpartEnds : ∀ f ∈ ({ T with E := inserted } : MGraph).E,
      ({ T with E := inserted } : MGraph).tail f < s.n ∧
      ({ T with E := inserted } : MGraph).head f < s.n := by
    intro f hf
    have hfT := hinsSub hf
    have hfG := hTG hfT
    have hfE := hTEnds f hfT
    have hft := (TreeEditEndpointAt.of_graph hG hfG).tailNameBound
    have hfh := (TreeEditEndpointAt.of_graph hG hfG).headNameBound
    change T.tail f < s.n ∧ T.head f < s.n
    rw [hfE.1, hfE.2, hsn]; exact ⟨hft, hfh⟩
  have hpartNe : ∀ f ∈ ({ T with E := inserted } : MGraph).E,
      ({ T with E := inserted } : MGraph).tail f ≠ ({ T with E := inserted } : MGraph).head f :=
    fun f hf => LSF.isForest_no_selfLoop hTForest (hinsSub hf)
  have hnotConnGraph : ¬ ({ T with E := inserted } : MGraph).Connected (T.tail e) (T.head e) :=
    treeEdit_link_disconnected hTForest ⟨Finset.Subset.rfl, hinsSub, fun _ _ => ⟨rfl, rfl⟩⟩ heT heNot
  have hnotConn : ¬ pathTreeConnected s (vid (G.tail e)) (vid (G.head e)) := by
    intro hc
    rw [← hTe.1, ← hTe.2] at hc
    exact hnotConnGraph (pathTreeConnected_to_namedGraph hW
      (by rw [hTe.1, hsn]; exact hep.tailNameBound)
      (by rw [hTe.2, hsn]; exact hep.headNameBound)
      (hnamed.parent_edge hW hpartEnds) hc)
  have hfreeNe : s.freeHead ≠ 0 :=
    treeEdit_freeHead_of_disconnected ⟨ts, fs, ds, hW⟩
      (by rw [hsn]; exact hep.tailNameBound) (by rw [hsn]; exact hep.headNameBound) hnotConn
  cases fs with
  | nil => exact (hfreeNe hW.freeListInv).elim
  | cons fresh rest =>
    have hfreshEq : s.freeHead = fresh := hW.freeListInv.2.1
    have hfreshSlot : isEdgeSlot G.n s.freeHead := by
      rw [hfreshEq, ← hsn]; exact hW.freeValid fresh List.mem_cons_self
    have hdisc : subRoot (inducedSubPar pathPayload s.splay ts) (ts.flatMap AuxTree.toList).length
        (vid (G.tail e)) ≠
        subRoot (inducedSubPar pathPayload s.splay ts) (ts.flatMap AuxTree.toList).length
          (vid (G.head e)) := fun h => hnotConn ((pathTreeConnected_iff_induced_roots hW
      (by rw [hsn]; exact hep.tailNameBound) (by rw [hsn]; exact hep.headNameBound)).mpr h)
    have hfitPre : pathTreeFits fmt.limbBits L s := hnum.fits hW (hsn.symm ▸ hcapB)
    have hvalB' : ∀ v, some (val e) = some v →
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B := by
      rintro v hv; cases hv; exact hvalB
    obtain ⟨tsN, dsN, hWN, hnumN⟩ := pathTreeNumericInv_link hW hnum
      (vid_isVertex (by rw [hsn]; exact hep.tailNameBound))
      (vid_isVertex (by rw [hsn]; exact hep.headNameBound)) hdisc hvalB'
    have hnextN : (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e))).n = G.n :=
      (lctLink_vertexCount s _ _ _).trans hsn
    have hfitPost : pathTreeFits fmt.limbBits L
        (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e))) :=
      hnumN.fits hWN (by rw [hnextN]; exact hcapB)
    have hlinkPre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
        [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, heap] st.mem :=
      treeEditLink_named_pre hep (by omega) ⟨ts, fresh :: rest, ds, hW⟩ hfitPre
        (by omega) (by rw [hsn]; exact hwidth) hnotConn hrecBelow hrecAt hfitPost
    have hlinkAlloc : allocation 0 s.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, heap] ≤ linkSpace :=
      hsn.symm ▸ hspace
    let s1 := { st with regs := Function.update st.regs 8 e }
    let s2 := { s1 with regs := Function.update s1.regs 4 (recPtr e) }
    let s3 := { s2 with regs := Function.update s2.regs 21 heap }
    have hr1 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 28) (.reg 26)))) st .normal s1 5 :=
      runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, h28, h26, heListW, heAt], rfl, rfl, rfl⟩
    have hr2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 22) (.reg 8)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨recPtr e, by simp [Expr.eval, BinOp.eval, s1, h22, hrecPtrW, hrecPtr], rfl, rfl, rfl⟩
    have hr3 : Runs w p ω (.assign 21 (.reg 3)) s2 .normal s3 2 :=
      runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s2, s1, h3], rfl, rfl, rfl⟩
    have hwordsL : ∀ a ∈ [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, heap], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      have htn := hep.tailNameBound; have hhn := hep.headNameBound
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨s4, ret, cLink, y, hr4, hret4, hregs4, hrep4, hslotMem, hresp4, hcLink⟩ :=
      treeEditLink_named_runs (ω := ω) (st := s3) himpl hep hrootRoom (by omega) (by omega)
        (by simp [s3, s2, s1]) (by simp [s3, s2, s1, h9]) (by simp [s3, s2, s1, h10])
        (by simp [s3, s2, s1, h11]) (by simp [s3, s2, s1, h0]) (by simp [s3, s2, s1, h3])
        (by simp [s3, s2, s1]) hrecAt hwordsL hrep hlinkPre hfoot hz (by omega)
    have hretLo : heap ≤ ret := hresp4.1
    have hretHi : ret ≤ heap + linkSpace := hresp4.2.1.trans (Nat.add_le_add_left hlinkAlloc heap)
    have hretW : ret < 2 ^ w := by omega
    have hfootYOut : ∀ a, R.foot treeHandle y a → OutsideInitSlotTables slots names slotThresholds m G.n a := by
      intro a ha
      rcases hresp4.2.2.2.2 a ha with hold | ⟨hlo, _⟩
      · exact hfootOut a hold
      · exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
    have hfootYBelow : ∀ a, R.foot treeHandle y a → a < ret := by
      intro a ha
      rcases hresp4.2.2.2.2 a ha with hold | ⟨_, hhi⟩
      · exact (hfoot a hold).trans_le hretLo
      · exact hhi
    have hslotLt : s.freeHead < 2 * G.n := hfreshSlot.2
    have hhsf : ¬ R.foot treeHandle y (slots + e) := fun hf =>
      (hfootYOut _ hf).1.elim (by omega) (by omega)
    have hhnf : ¬ R.foot treeHandle y (names + s.freeHead) := fun hf =>
      (hfootYOut _ hf).2.1.elim (by omega) (by omega)
    have hhstf : ¬ R.foot treeHandle y (slotThresholds + s.freeHead) := fun hf =>
      (hfootYOut _ hf).2.2.elim (by omega) (by omega)
    have h19_4 : s4.regs 19 = slots := (hregs4 19 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1, h19])
    have h20_4 : s4.regs 20 = names := (hregs4 20 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1, h20])
    have h8_4 : s4.regs 8 = e := (hregs4 8 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1])
    have h21_4 : s4.regs 21 = heap := (hregs4 21 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1])
    have h23_4 : s4.regs 23 = edgeThresholds := (hregs4 23 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1, h23])
    have h24_4 : s4.regs 24 = slotThresholds := (hregs4 24 (by decide) (by decide) (by decide)).trans (by simp [s3, s2, s1, h24])
    obtain ⟨s5, cBind, hr5, hret5, hregs5, hbindPost, hrep5, hphi5, hcBind⟩ :=
      treeEditBindSlot_runs (ω := ω) (st := s4) hbind himpl.1 hrep4
        ⟨h19_4, h20_4, h8_4, h21_4, hret4⟩ hslotMem (by omega) (by omega)
        (by rcases hdisjSN with h | h <;> omega) hhsf hhnf hretW hresp4.2.2.1
    have hbindMem : s5.mem = Function.update (Function.update s4.mem (slots + e) s.freeHead)
        (names + s.freeHead) e := hbindPost.2.1
    have hslotMem5 : s5.mem heap = s.freeHead := by
      rw [hbindMem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hslotMem
    have hthMem5 : s5.mem (edgeThresholds + e) = thPtr e := by
      rw [hbindMem,
        Function.update_of_ne (by rcases hthOut.2.1 with h | h <;> omega),
        Function.update_of_ne (by rcases hthOut.1 with h | h <;> omega),
        hresp4.2.2.2.1 _ hthBelow hthFoot, hthPtrAt]
    let out := { s5 with mem := Function.update s5.mem (slotThresholds + s.freeHead) (thPtr e) }
    have hr6 : Runs w p ω
        (.store (.bin .add (.reg 24) (.load (.reg 21))) (.load (.bin .add (.reg 23) (.reg 8))))
        s5 .normal out 9 := by
      refine runs_store_iff.mpr ⟨slotThresholds + s.freeHead, thPtr e, ?_, ?_, rfl, rfl, rfl⟩
      · simp [Expr.eval, BinOp.eval, hregs5 24 (by decide), h24_4, hregs5 21 (by decide), h21_4,
          hslotMem5, show slotThresholds + s.freeHead < 2 ^ w by omega]
      · simp [Expr.eval, BinOp.eval, hregs5 23 (by decide), h23_4, hregs5 8 (by decide), h8_4,
          hthPtrW, hthMem5]
    have hloc6 := himpl.1 treeHandle (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e)))
      y s5.mem out.mem (fun a ha => by
        have hne : a ≠ slotThresholds + s.freeHead := fun h => hhstf (h ▸ ha)
        simp [out, Function.update_of_ne hne])
    have hrepOut : R.rep treeHandle _ y out.mem := hloc6.1 hrep5
    have hphiOut : R.phi treeHandle y out.mem = R.phi treeHandle y s4.mem :=
      hloc6.2.symm.trans hphi5
    have htab4 : PathSlotTablesAt s4.mem slots names m (2 * G.n) slot name :=
      htab.congr (fun j hj => hresp4.2.2.2.1 _ (by omega) (fun hf => (hfootOut _ hf).1.elim (by omega) (by omega)))
        (fun j hj => hresp4.2.2.2.1 _ (by omega) (fun hf => (hfootOut _ hf).2.1.elim (by omega) (by omega)))
    have htab5 : PathSlotTablesAt s5.mem slots names m (2 * G.n)
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) :=
      pathSlotBind_tables htab4 heCap hslotLt hdisjSN hbindPost
    have htabOut : PathSlotTablesAt out.mem slots names m (2 * G.n)
        (Function.update slot e s.freeHead) (Function.update name s.freeHead e) :=
      htab5.congr (fun j hj => by simp only [out]; exact Function.update_of_ne (by rcases hdisjST with h | h <;> omega) _ _)
        (fun j hj => by simp only [out]; exact Function.update_of_ne (by rcases hdisjNT with h | h <;> omega) _ _)
    obtain ⟨tsL, fsL, dsL, hWL, hnamedL, hliveL⟩ :=
      hlive.link hnamed hW hpartEnds hpartNe heNot
        (by rw [hTe.1, hsn]; exact hep.tailNameBound)
        (by rw [hTe.2, hsn]; exact hep.headNameBound)
        (by rw [hTe.1, hTe.2]; exact hnotConn) (val e)
    simp only [hvalFwd, ite_true, Function.update_eq_self] at hWL hnamedL hliveL
    have hTe' : vid (T.tail e) = G.tail e + 1 ∧ vid (T.head e) = G.head e + 1 := by
      simp [vid, hTe.1, hTe.2]
    rw [hTe'.1, hTe'.2] at hWL hnamedL hliveL
    have hnamedN : TreeEditNamedSlots (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e)))
        tsN { T with E := insert e inserted } (Function.update slot e s.freeHead)
        (Function.update name s.freeHead e) :=
      namedSlots_congr_witness hWL hWN hnamedL
    have hliveN : TreeEditLiveAccounts (lctLink pathPayload s (G.tail e + 1) (G.head e + 1) (some (val e)))
        tsN { T with E := insert e inserted } (Function.update slot e s.freeHead) val :=
      fun f hf => (hliveL f hf).congr_witness hWL hWN
    have hstOut : ∀ f ∈ insert e inserted,
        out.mem (slotThresholds + Function.update slot e s.freeHead f) = thPtr f := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hfOld
      · simp [out]
      · have hfe : f ≠ e := fun h => heNot (h ▸ hfOld)
        rw [Function.update_of_ne hfe]
        have hfActive := (hnamed.forward f hfOld).1
        have hfNeFresh : slot f ≠ s.freeHead := by
          intro heq
          rw [hfreshEq] at heq
          have hpart := (hW.partitionSlots (slot f) (hnamed.forward f hfOld).2.1).mp hfActive
          exact hpart (heq ▸ List.mem_cons_self)
        have hsfLt : slot f < 2 * G.n := (hsn ▸ (hnamed.forward f hfOld).2.1).2
        simp only [out, Function.update_of_ne (by omega : slotThresholds + slot f ≠ slotThresholds + s.freeHead)]
        rw [hbindMem,
          Function.update_of_ne (by rcases hdisjNT with h | h <;> omega),
          Function.update_of_ne (by rcases hdisjST with h | h <;> omega),
          hresp4.2.2.2.1 _ (by omega) (fun hft => (hfootOut _ hft).2.2.elim (by omega) (by omega))]
        exact hstTab f hfOld
    have hzeroOut : ∀ f < m, f ∉ insert e inserted → Function.update slot e s.freeHead f = 0 := by
      intro f hfm hfNot
      have hfe : f ≠ e := fun h => hfNot (h ▸ Finset.mem_insert_self _ _)
      have hfOld : f ∉ inserted := fun h => hfNot (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hfe]
      exact hzeroSlot f hfm hfOld
    have hzeroMemOut : ZeroFrom out.mem ret := by
      intro a ha
      simp only [out, Function.update_of_ne (by omega : a ≠ slotThresholds + s.freeHead)]
      exact hbindPost.2.2 a ha
    have hframeOut : ∀ a < heap, ¬ (R.foot treeHandle x a ∨
        ¬ OutsideInitSlotTables slots names slotThresholds m G.n a) → out.mem a = st.mem a := by
      intro a ha hguard
      push Not at hguard
      obtain ⟨hfx, hOut⟩ := hguard
      simp only [out]
      rw [Function.update_of_ne (by rcases hOut.2.2 with h | h <;> omega), hbindMem,
        Function.update_of_ne (by rcases hOut.2.1 with h | h <;> omega),
        Function.update_of_ne (by rcases hOut.1 with h | h <;> omega),
        hresp4.2.2.2.1 a ha hfx]
    refine ⟨out, ret, 5 + (5 + (2 + (cLink + (cBind + 9 + 1) + 1) + 1) + 1) + 1, y,
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hr1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hr2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, hr3,
            runs_seq_iff.mpr (Or.inr ⟨s4, cLink, _, hr4,
              runs_seq_iff.mpr (Or.inr ⟨s5, cBind, 9, hr5, hr6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      hret5, fun r h1 h2 h3' h4 h8 h21 => by
        simp only [out]
        rw [hregs5 r h3', hregs4 r h1 h2 h3']
        simp [s3, s2, s1, Function.update_of_ne h21, Function.update_of_ne h4, Function.update_of_ne h8],
      ⟨hnextN, Finset.insert_subset_iff.mpr ⟨heT, hinsSub⟩, hrepOut, hfootYBelow, htabOut,
        ⟨tsN, rest, dsN, hWN, hnumN, hnamedN, hliveN⟩, hstOut, hzeroOut⟩,
      hfootYOut,
      ⟨hretLo, hretHi, hzeroMemOut, hframeOut, fun a ha => (hresp4.2.2.2.2 a ha).imp_left Or.inl⟩,
      ?_⟩
    rw [hphiOut]
    rw [hsn] at hcLink
    dsimp only [s3, s2, s1] at hcLink
    omega

private theorem insert_union_take {α : Type*} [DecidableEq α] (s : Finset α) (l : List α)
    {i : ℕ} (hi : i < l.length) :
    insert l[i] (s ∪ (l.take i).toFinset) = s ∪ (l.take (i + 1)).toFinset := by
  rw [List.take_succ_eq_append_getElem hi, List.toFinset_append, List.toFinset_cons,
    List.toFinset_nil, LawfulSingleton.insert_empty_eq]
  ext z
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  tauto

/-- Run `initLinkForestEdges (op 0) bind` to link every edge of a dynamic forest
`F` (`F.E ⊆ T.E`, disjoint from `inserted`) into the Section 6 path tree,
binding `slots`, `names`, and `slotThresholds` for each linked edge. -/
theorem initLinkForestEdges_runs {w L constant init bind treeHandle rootBase forestBase ec fv fe m
    slots names slotThresholds edgeRecords edgeThresholds heap linkSpace : ℕ}
    {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState} {op : ℕ → ℕ}
    {G T F : MGraph} {val : ℕ → PathEdgeValue} {B : ℤ} {recPtr thPtr : ℕ → ℕ}
    {inserted : Finset ℕ} {s : PathTreeState} {x : R.τ} {slot name : ℕ → ℕ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hTForest : T.IsForest)
    (hTEnds : ∀ f ∈ T.E, T.tail f = G.tail f ∧ T.head f = G.head f)
    (hG : DynGraphAt st.mem rootBase G.n ec G)
    (hF : DynGraphAt st.mem forestBase fv fe F)
    (hTG : T.E ⊆ G.E) (hELt : ∀ e ∈ G.E, e < m)
    (hFT : F.E ⊆ T.E) (hdisjF : Disjoint inserted F.E)
    (hinv : InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
      inserted s x slot name heap st.mem)
    (hvalFwd : ∀ e ∈ F.E, (val e).forward = true)
    (hvalB : ∀ e ∈ F.E, |((val e).gradient)| ≤ B ∧ |((val e).length)| ≤ B ∧
      |((val e).flow)| ≤ B ∧ |((val e).detector)| ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity fmt.limbBits L : ℤ))
    (h0 : st.regs 0 = treeHandle) (h3 : st.regs 3 = heap)
    (h9 : st.regs 9 = dgETailSlotBase rootBase G.n ec)
    (h10 : st.regs 10 = dgEHeadSlotBase rootBase G.n ec)
    (h11 : st.regs 11 = dgIntToExtBase rootBase G.n)
    (h19 : st.regs 19 = slots) (h20 : st.regs 20 = names)
    (h22 : st.regs 22 = edgeRecords) (h23 : st.regs 23 = edgeThresholds)
    (h24 : st.regs 24 = slotThresholds) (h25 : st.regs 25 = forestBase)
    (hrecPtr : ∀ e ∈ F.E, st.mem (edgeRecords + e) = recPtr e)
    (hrecAt : ∀ e ∈ F.E, PathEdgeAt st.mem (recPtr e) fmt.limbBits L (some (val e)))
    (hthPtrAt : ∀ e ∈ F.E, st.mem (edgeThresholds + e) = thPtr e)
    (hrecBelow : ∀ e ∈ F.E, recPtr e + (2 + 4 * L) ≤ heap)
    (hrecPtrBelow : ∀ e ∈ F.E, edgeRecords + e < heap)
    (hthPtrBelow : ∀ e ∈ F.E, edgeThresholds + e < heap)
    (hthValW : ∀ e ∈ F.E, thPtr e < 2 ^ w)
    (hrootBelow : rootBase + dynGraphSize G.n ec ≤ heap)
    (hforestBelow : forestBase + dynGraphSize fv fe ≤ heap)
    (hslotsBelow : slots + m ≤ heap) (hnamesBelow : names + 2 * G.n ≤ heap)
    (hstBelow : slotThresholds + 2 * G.n ≤ heap)
    (hdisjSN : slots + m ≤ names ∨ names + 2 * G.n ≤ slots)
    (hdisjST : slots + m ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ slots)
    (hdisjNT : names + 2 * G.n ≤ slotThresholds ∨ slotThresholds + 2 * G.n ≤ names)
    (hfootOut : ∀ a, R.foot treeHandle x a → OutsideInitSlotTables slots names slotThresholds m G.n a)
    (hrootOut : ∀ a, rootBase ≤ a → a < rootBase + dynGraphSize G.n ec →
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ R.foot treeHandle x a)
    (hforestOut : ∀ a, forestBase ≤ a → a < forestBase + dynGraphSize fv fe →
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ R.foot treeHandle x a)
    (hrecPtrOut : ∀ e ∈ F.E, OutsideInitSlotTables slots names slotThresholds m G.n (edgeRecords + e) ∧
      ¬ R.foot treeHandle x (edgeRecords + e))
    (hrecOut : ∀ e ∈ F.E, ∀ a, recPtr e ≤ a → a < recPtr e + (2 + 4 * L) →
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧ ¬ R.foot treeHandle x a)
    (hthPtrOut : ∀ e ∈ F.E, OutsideInitSlotTables slots names slotThresholds m G.n (edgeThresholds + e) ∧
      ¬ R.foot treeHandle x (edgeThresholds + e))
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ fmt.limbBits * L)
    (hhandleW : treeHandle < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hspace : ∀ e ∈ F.E, ∀ cur, heap ≤ cur → cur ≤ heap + F.m * linkSpace →
      allocation 0 G.n [treeHandle, G.tail e + 1, G.head e + 1, recPtr e, cur] ≤ linkSpace)
    (hroom : heap + F.m * linkSpace < 2 ^ w) :
    ∃ out ret cost sFinal y slotFinal nameFinal,
      Runs w p ω (initLinkForestEdges (op 0) bind) st .normal out cost ∧
      out.regs 3 = ret ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 8 → r ≠ 21 →
        r ≠ 26 → r ≠ 27 → r ≠ 28 → out.regs r = st.regs r) ∧
      InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
        (inserted ∪ F.E) sFinal y slotFinal nameFinal ret out.mem ∧
      (∀ a, R.foot treeHandle y a → OutsideInitSlotTables slots names slotThresholds m G.n a) ∧
      R.Respects (fun a => R.foot treeHandle x a ∨
        ¬ OutsideInitSlotTables slots names slotThresholds m G.n a)
        heap (F.m * linkSpace) st.mem ret treeHandle y out.mem ∧
      cost + R.phi treeHandle y out.mem ≤
        F.m * (pathTreeBudget constant L G.n + 96) + R.phi treeHandle x st.mem + 30 := by
  obtain ⟨eL, heLen, heNodup, heMem, heListAt, _⟩ := hF.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hheapW : heap < 2 ^ w := by omega
  have hfv : st.mem forestBase = fv := hF.2.2.2.1
  have hfe : st.mem (forestBase + 1) = fe := hF.2.2.2.2.1
  have hfm : st.mem (forestBase + 3) = F.m := hF.2.2.2.2.2.2.1
  have hfgSize : dynGraphSize fv fe = 4 + 7 * fv + 9 * fe := rfl
  have heListBaseEq : dgEListBase forestBase fv fe = forestBase + 4 + 7 * fv + fe := rfl
  let s1 := { st with regs := Function.update st.regs 27 F.m }
  let s2 := { s1 with regs := Function.update s1.regs 28 (dgEListBase forestBase fv fe) }
  let s3 := { s2 with regs := Function.update s2.regs 26 0 }
  have hr1 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 25) (.const 3)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨F.m, by
      simp [Expr.eval, BinOp.eval, h25, show 3 < 2 ^ w by omega,
        show forestBase + 3 < 2 ^ w by omega, hfm], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 28 (.bin .add (.bin .add (.bin .add (.reg 25) (.const 4))
      (.bin .mul (.const 7) (.load (.reg 25))))
      (.load (.bin .add (.reg 25) (.const 1))))) s1 .normal s2 14 :=
    runs_assign_iff.mpr ⟨dgEListBase forestBase fv fe, by
      simp [Expr.eval, BinOp.eval, s1, h25, hfv, hfe, heListBaseEq, hw7,
        show 1 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
        show forestBase + 1 < 2 ^ w by omega, show forestBase + 4 < 2 ^ w by omega,
        show 7 * fv < 2 ^ w by omega, show forestBase + 4 + 7 * fv < 2 ^ w by omega,
        show forestBase + 4 + 7 * fv + fe < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 26 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Inductive loop invariant over `k = F.m - idx` remaining edges
  have hloop : ∀ (rem idx : ℕ), idx + rem = F.m →
      ∀ (curSt : State) (curHeap : ℕ) (curS : PathTreeState) (curX : R.τ) (curSlot curName : ℕ → ℕ),
        curSt.regs 26 = idx → curSt.regs 27 = F.m → curSt.regs 28 = dgEListBase forestBase fv fe →
        curSt.regs 0 = treeHandle → curSt.regs 3 = curHeap →
        curSt.regs 9 = dgETailSlotBase rootBase G.n ec →
        curSt.regs 10 = dgEHeadSlotBase rootBase G.n ec →
        curSt.regs 11 = dgIntToExtBase rootBase G.n →
        curSt.regs 19 = slots → curSt.regs 20 = names →
        curSt.regs 22 = edgeRecords → curSt.regs 23 = edgeThresholds →
        curSt.regs 24 = slotThresholds →
        heap ≤ curHeap → curHeap ≤ heap + idx * linkSpace →
        InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
          (inserted ∪ (eL.take idx).toFinset) curS curX curSlot curName curHeap curSt.mem →
        (∀ a, R.foot treeHandle curX a → OutsideInitSlotTables slots names slotThresholds m G.n a) →
        R.Respects (fun a => R.foot treeHandle x a ∨
          ¬ OutsideInitSlotTables slots names slotThresholds m G.n a)
          heap (idx * linkSpace) st.mem curHeap treeHandle curX curSt.mem →
        ∃ out ret cost sFin yFin slotFin nameFin,
          Runs w p ω (.loop (.bin .lt (.reg 26) (.reg 27))
            (initLinkSingleEdge (op 0) bind ;; .assign 26 (.bin .add (.reg 26) (.const 1))))
            curSt .normal out cost ∧
          out.regs 3 = ret ∧
          (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 8 → r ≠ 21 → r ≠ 26 → out.regs r = curSt.regs r) ∧
          InitPathTreeInv R treeHandle G T val B slots names slotThresholds m thPtr
            (inserted ∪ F.E) sFin yFin slotFin nameFin ret out.mem ∧
          (∀ a, R.foot treeHandle yFin a → OutsideInitSlotTables slots names slotThresholds m G.n a) ∧
          R.Respects (fun a => R.foot treeHandle x a ∨
            ¬ OutsideInitSlotTables slots names slotThresholds m G.n a)
            heap (F.m * linkSpace) st.mem ret treeHandle yFin out.mem ∧
          cost + R.phi treeHandle yFin out.mem ≤
            rem * (pathTreeBudget constant L G.n + 96) + R.phi treeHandle curX curSt.mem + 5 := by
    intro rem
    induction rem with
    | zero =>
      intro idx hidx curSt curHeap curS curX curSlot curName
        h26 h27 _ _ h3c _ _ _ _ _ _ _ _ hlo hhi hinvC hfootOutC hrespC
      have hidxEq : idx = F.m := by omega
      subst hidxEq
      have htake : (eL.take F.m).toFinset = F.E := by
        rw [← heLen, List.take_length]
        ext e; simp [heMem]
      rw [htake] at hinvC
      refine ⟨curSt, curHeap, 4, curS, curX, curSlot, curName,
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h26, h27], rfl, rfl, rfl⟩),
        h3c, fun _ _ _ _ _ _ _ _ => rfl, hinvC, hfootOutC, hrespC, by omega⟩
    | succ rem ih =>
      intro idx hidx curSt curHeap curS curX curSlot curName
        h26 h27 h28 h0c h3c h9c h10c h11c h19c h20c h22c h23c h24c hlo hhi hinvC hfootOutC hrespC
      have hidxLt : idx < F.m := by omega
      have hidxEL : idx < eL.length := heLen.symm ▸ hidxLt
      let e := eL[idx]
      have heInEL : e ∈ eL := List.getElem_mem hidxEL
      have heF : e ∈ F.E := (heMem e).mp heInEL
      have heT : e ∈ T.E := hFT heF
      have heNotIns : e ∉ inserted := Finset.disjoint_right.mp hdisjF heF
      have heNotTake : e ∉ (eL.take idx).toFinset := by
        intro hm
        have hmemTake := List.mem_toFinset.mp hm
        obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hmemTake
        have hjLt : j < idx := by
          have := List.length_take_le idx eL; omega
        have hget : eL[j]'(lt_trans hjLt hidxEL) = eL[idx] := by
          simpa [List.getElem_take] using hje
        exact (by omega : j ≠ idx) ((List.Nodup.getElem_inj_iff heNodup).mp hget)
      have heNot : e ∉ inserted ∪ (eL.take idx).toFinset := by
        simp [heNotIns, heNotTake]
      have hframeC (a : ℕ) (ha : a < heap) (hOut : OutsideInitSlotTables slots names slotThresholds m G.n a)
          (hfx : ¬ R.foot treeHandle x a) : curSt.mem a = st.mem a :=
        hrespC.2.2.2.1 a ha (fun h => h.elim hfx (fun hn => hn hOut))
      have hGc : DynGraphAt curSt.mem rootBase G.n ec G :=
        DynGraphAt.of_agree hG (fun a haLo haHi => by
          have hro := hrootOut a haLo haHi
          exact hframeC a (lt_of_lt_of_le haHi hrootBelow) hro.1 hro.2)
      have hfootCurOfOld : ∀ a, R.foot treeHandle curX a → a < heap → R.foot treeHandle x a := by
        intro a ha hlt
        rcases hrespC.2.2.2.2 a ha with h | ⟨hge, _⟩
        · exact h.elim id (fun hnot => (hnot (hfootOutC a ha)).elim)
        · omega
      have heAtC : curSt.mem (dgEListBase forestBase fv fe + idx) = e := by
        have haLo : forestBase ≤ dgEListBase forestBase fv fe + idx := by
          unfold dgEListBase; omega
        have haHi : dgEListBase forestBase fv fe + idx < forestBase + dynGraphSize fv fe := by
          have : idx < fe := lt_of_lt_of_le hidxLt (by
            have h1 := hF.2.2.1
            have h2 : F.E.card ≤ fe := by
              have hsub : F.E ⊆ Finset.range fe := fun z hz => Finset.mem_range.mpr (h1 z hz)
              simpa [Finset.card_range] using Finset.card_le_card hsub
            exact h2)
          unfold dgEListBase dynGraphSize; omega
        have hfo := hforestOut _ haLo haHi
        rw [hframeC _ (lt_of_lt_of_le haHi hforestBelow) hfo.1 hfo.2]
        exact heListAt idx hidxEL
      have hrecPtrC : curSt.mem (edgeRecords + e) = recPtr e := by
        have ho := hrecPtrOut e heF
        rw [hframeC _ (hrecPtrBelow e heF) ho.1 ho.2, hrecPtr e heF]
      have hrecAtC : PathEdgeAt curSt.mem (recPtr e) fmt.limbBits L (some (val e)) :=
        (hrecAt e heF).congr (fun a hloA hhiA => by
          have hhiA' : a < recPtr e + (2 + 4 * L) := by omega
          have ho := hrecOut e heF a hloA hhiA'
          exact hframeC a (lt_of_lt_of_le hhiA' (hrecBelow e heF)) ho.1 ho.2)
      have hthPtrC : curSt.mem (edgeThresholds + e) = thPtr e := by
        have ho := hthPtrOut e heF
        rw [hframeC _ (hthPtrBelow e heF) ho.1 ho.2, hthPtrAt e heF]
      have hcurAddLe : curHeap + linkSpace ≤ heap + (idx + 1) * linkSpace := by
        have : (idx + 1) * linkSpace = idx * linkSpace + linkSpace := by ring
        omega
      have hidx1Le : (idx + 1) * linkSpace ≤ F.m * linkSpace :=
        Nat.mul_le_mul_right linkSpace (show idx + 1 ≤ F.m by omega)
      have hcurLeEnd : curHeap ≤ heap + F.m * linkSpace :=
        hhi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right linkSpace (by omega)) heap)
      have heListW : dgEListBase forestBase fv fe + idx < 2 ^ w := by
        have : idx < fe := by
          have hsub : F.E ⊆ Finset.range fe := fun z hz => Finset.mem_range.mpr (hF.2.2.1 z hz)
          have := Finset.card_le_card hsub; rw [Finset.card_range] at this; exact lt_of_lt_of_le hidxLt this
        unfold dgEListBase dynGraphSize at *; omega
      obtain ⟨mid, ret1, cStep, y1, hrStep, hret1, hregsStep, hinv1, hfootOut1, hresp1, hcStep⟩ :=
        initLinkSingleEdge_runs (ω := ω) (st := curSt) himpl hbind hTForest hTEnds hGc hTG hELt
          heT heNot hinvC (hvalFwd e heF) (hvalB e heF) hcapB
          h0c h3c h9c h10c h11c h19c h20c h22c h23c h24c h26 h28
          heAtC heListW hrecPtrC hrecAtC hthPtrC
          ((hrecBelow e heF).trans hlo) (by have := hrecPtrBelow e heF; omega)
          (by have := hthPtrBelow e heF; omega) (by omega)
          (hslotsBelow.trans hlo) (hnamesBelow.trans hlo) (hstBelow.trans hlo)
          hdisjSN hdisjST hdisjNT hfootOutC (hthPtrOut e heF).1
          (fun hft => (hthPtrOut e heF).2 (hfootCurOfOld _ hft (hthPtrBelow e heF)))
          ((hthPtrBelow e heF).trans_le hlo) (hthValW e heF) hvw hwidth hhandleW
          hrespC.2.2.1 (hspace e heF curHeap hlo hcurLeEnd) (by omega)
      let after := { mid with regs := Function.update mid.regs 26 (idx + 1) }
      have h26mid : mid.regs 26 = idx :=
        (hregsStep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
      have hrInc : Runs w p ω (.assign 26 (.bin .add (.reg 26) (.const 1))) mid .normal after 4 :=
        runs_assign_iff.mpr ⟨idx + 1, by
          simp [Expr.eval, BinOp.eval, h26mid, show 1 < 2 ^ w by omega,
            show idx + 1 < 2 ^ w by
              have hsub : F.E ⊆ Finset.range fe := fun z hz => Finset.mem_range.mpr (hF.2.2.1 z hz)
              have := Finset.card_le_card hsub; rw [Finset.card_range] at this
              unfold dynGraphSize at hforestBelow; omega], rfl, rfl, rfl⟩
      have htakeSucc : insert e (inserted ∪ (eL.take idx).toFinset) =
          inserted ∪ (eL.take (idx + 1)).toFinset :=
        insert_union_take inserted eL hidxEL
      rw [htakeSucc] at hinv1
      have hrespNext : R.Respects (fun a => R.foot treeHandle x a ∨
          ¬ OutsideInitSlotTables slots names slotThresholds m G.n a)
          heap ((idx + 1) * linkSpace) st.mem ret1 treeHandle y1 after.mem := by
        refine ⟨hlo.trans hresp1.1, hresp1.2.1.trans hcurAddLe, hresp1.2.2.1, ?_, ?_⟩
        · intro a ha hnot
          have hfx1 : ¬ (R.foot treeHandle curX a ∨
              ¬ OutsideInitSlotTables slots names slotThresholds m G.n a) := by
            push Not at hnot ⊢
            exact ⟨fun hft => hnot.1 (hfootCurOfOld a hft ha), hnot.2⟩
          exact (hresp1.2.2.2.1 a (ha.trans_le hlo) hfx1).trans (hrespC.2.2.2.1 a ha hnot)
        · intro a ha
          rcases hresp1.2.2.2.2 a ha with h | ⟨hlo1, hhi1⟩
          · rcases h with hfx1 | hnotOut
            · rcases hrespC.2.2.2.2 a hfx1 with hold | ⟨hlo0, hhi0⟩
              · exact Or.inl hold
              · exact Or.inr ⟨hlo0, hhi0.trans_le hresp1.1⟩
            · exact Or.inl (Or.inr hnotOut)
          · exact Or.inr ⟨hlo.trans hlo1, hhi1⟩
      have hregAfter (r : ℕ) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3' : r ≠ 3) (h4 : r ≠ 4)
          (h8 : r ≠ 8) (h21 : r ≠ 21) (h26' : r ≠ 26) : after.regs r = curSt.regs r :=
        (Function.update_of_ne h26' _ _).trans (hregsStep r h1 h2 h3' h4 h8 h21)
      obtain ⟨out, ret, cRest, sFin, yFin, slotFin, nameFin, hrRest, hretOut, hregsRest,
          hinvFin, hfootOutFin, hrespFin, hcRest⟩ :=
        ih (idx + 1) (by omega) after ret1 _ y1 _ _
          (Function.update_self 26 (idx + 1) mid.regs)
          ((hregAfter 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27)
          ((hregAfter 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28)
          ((hregAfter 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0c)
          ((Function.update_of_ne (by decide : 3 ≠ 26) (idx + 1) mid.regs).trans hret1)
          ((hregAfter 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9c)
          ((hregAfter 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10c)
          ((hregAfter 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11c)
          ((hregAfter 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19c)
          ((hregAfter 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20c)
          ((hregAfter 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22c)
          ((hregAfter 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23c)
          ((hregAfter 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24c)
          (hlo.trans hresp1.1) (hresp1.2.1.trans hcurAddLe) hinv1 hfootOut1 hrespNext
      have hrBody : Runs w p ω (initLinkSingleEdge (op 0) bind ;; .assign 26 (.bin .add (.reg 26) (.const 1)))
          curSt .normal after (cStep + 4 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨mid, cStep, 4, hrStep, hrInc, rfl⟩)
      have hrWhile : Runs w p ω (.loop (.bin .lt (.reg 26) (.reg 27))
          (initLinkSingleEdge (op 0) bind ;; .assign 26 (.bin .add (.reg 26) (.const 1))))
          curSt .normal out (3 + (cStep + 4 + 1) + cRest + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, after, cStep + 4 + 1, cRest,
          by simp [Expr.eval, BinOp.eval, h26, h27, hidxLt, show 1 < 2 ^ w by omega],
          by decide, hrBody, hrRest, rfl⟩))
      refine ⟨out, ret, 3 + (cStep + 4 + 1) + cRest + 1, sFin, yFin, slotFin, nameFin,
        hrWhile, hretOut, fun r h1 h2 h3' h4 h8 h21 h26' => ?_,
        hinvFin, hfootOutFin, hrespFin, ?_⟩
      · rw [hregsRest r h1 h2 h3' h4 h8 h21 h26']
        simp only [after, Function.update_of_ne h26']
        exact hregsStep r h1 h2 h3' h4 h8 h21
      · have hmul : (rem + 1) * (pathTreeBudget constant L G.n + 96) =
            rem * (pathTreeBudget constant L G.n + 96) + (pathTreeBudget constant L G.n + 96) := by ring
        dsimp only [after] at hcRest
        omega
  obtain ⟨out, ret, cLoop, sFin, yFin, slotFin, nameFin, hrLoop, hretOut, hregsLoop,
      hinvFin, hfootOutFin, hrespFin, hcLoop⟩ :=
    hloop F.m 0 (Nat.zero_add F.m) s3 heap s x slot name
      (by simp [s3]) (by simp [s3, s2, s1]) (by simp [s3, s2])
      (by simp [s3, s2, s1, h0]) (by simp [s3, s2, s1, h3])
      (by simp [s3, s2, s1, h9]) (by simp [s3, s2, s1, h10]) (by simp [s3, s2, s1, h11])
      (by simp [s3, s2, s1, h19]) (by simp [s3, s2, s1, h20])
      (by simp [s3, s2, s1, h22]) (by simp [s3, s2, s1, h23]) (by simp [s3, s2, s1, h24])
      le_rfl (by simp)
      (by simpa [List.take_zero] using hinv) hfootOut
      ⟨le_rfl, by simp, hz, fun _ _ _ => rfl, fun a ha => Or.inl (Or.inl ha)⟩
  refine ⟨out, ret, 5 + (14 + (2 + cLoop + 1) + 1) + 1, sFin, yFin, slotFin, nameFin,
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 14, _, hr2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, cLoop, hr3, hrLoop, rfl⟩), rfl⟩), rfl⟩),
    hretOut, fun r h1 h2 h3' h4 h8 h21 h26' h27' h28' => by
      rw [hregsLoop r h1 h2 h3' h4 h8 h21 h26']
      simp [s3, s2, s1, Function.update_of_ne h26', Function.update_of_ne h28', Function.update_of_ne h27'],
    hinvFin, hfootOutFin, hrespFin, by dsimp only [s3, s2, s1] at hcLoop; omega⟩

end MinCostFlow.MinRatio
