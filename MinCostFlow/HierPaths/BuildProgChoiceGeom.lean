module

public import MinCostFlow.HierPaths.BuildProgChoiceRows
public import MinCostFlow.HierPaths.BuildProgGameSlots
public import MinCostFlow.HierPaths.BuildProgGameSetup

/-!
# Word layout bounds for certified game rounds

The original child reservations do not depend on the replies. The current
graph of an active child and the graph after appending its matching both
fit that child's reservation.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The fixed fields of the known layout, with the current child states
supplied by the trace of the certified game. -/
def ChoiceLoopData.geometry (D : ChoiceLoopData) : BuildGameSchedule :=
  ⟨D.base,D.addrs,D.count,D.first,D.childAddr,D.saved,D.directory,D.L'⟩

/-- Inputs of the game and of the matching calls within one parent. -/
structure ChoiceGameHyp (D : ChoiceLoopData) (β : ℝ) (bh : ℕ) : Prop where
  router : IsMatchingPlayer D.base.route D.base.routeCost
  valid : D.base.host.IsValid
  host : HostPre D.base.host D.base.verts D.base.Δ D.base.L
  positive : 0 < β
  expansion : D.base.host.IsExpansionExpanderOn D.base.verts β
  denominator : max 2 (2/β) ≤ (bh:ℝ)
  children : IsChildren D.base.verts (fun c => shiftSet (D.offset c) (Finset.range D.base.childSize))
    D.count D.base.childSize
  even : D.base.childSize % 2 = 0
  coreSize : D.base.childSize ≤ (NOf D.base.M D.base.r)^D.base.r
  rankLe : D.base.r ≤ ell D.base.M
  degree : 49*D.L' ≤ deltaParam D.base.M
  sizeLog : D.base.childSize < 2^D.L'
  path : routePathLen D.base.Δ bh D.base.L ≤ D.base.pathBound

/-- The initial and intermediate graph blocks, active tables, and arena end. -/
structure ChoiceGameMemory (D : ChoiceLoopData) (heap : ℕ) (sts : ℕ → ChildState)
    (mem : ℕ → ℕ) : Prop where
  host : GraphAt mem D.addrs.host D.base.host
  verts : ListAt mem D.addrs.verts (finsetWords D.base.verts)
  graphs : ListAt mem D.addrs.graphs (tabList (D.round sts).jobs.count (D.round sts).jobs.addr)
  offsets : ListAt mem D.addrs.offsets (tabList (D.round sts).jobs.count (D.round sts).jobs.offset)
  children : ∀ c < D.count, GraphAt mem (D.childAddr c) (gameGraph D.base.childSize (sts c))
  zero : ZeroFrom mem heap
  heap : D.addrs.heap ≤ heap

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The scan's positions are distinct original children. -/
theorem ChoiceLoopData.active_inj (D : ChoiceLoopData) (sts : ℕ → ChildState) {i j : ℕ}
    (hi : i < (D.round sts).jobs.count) (hj : j < (D.round sts).jobs.count)
    (he : D.active sts i = D.active sts j) : i = j := by
  let ls := activeChildren D.count sts
  have hN : ls.Nodup := List.nodup_range.filter _
  have hi' : i < ls.length := hi
  have hj' : j < ls.length := hj
  change ls.getD i 0 = ls.getD j 0 at he
  rw [List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hj'] at he
  exact (hN.getElem_inj_iff).mp he

/-- There are at most as many active entries as original children. -/
theorem ChoiceLoopData.active_le (D : ChoiceLoopData) (sts : ℕ → ChildState) :
    (D.round sts).jobs.count ≤ D.count := by
  change (activeChildren D.count sts).length ≤ D.count
  simpa [activeChildren] using
    List.length_filter_le (fun c => (sts c).saved.isNone) (List.range D.count)

/-- A nonempty active table fits the step's fixed memory geometry. -/
theorem choiceLoop_stepLayout {w heap : ℕ} {D : ChoiceLoopData} {sts : ℕ → ChildState}
    (hL : GameFixedLayout w D.geometry) (hh : D.addrs.heap ≤ heap)
    (hn : 0 < (D.round sts).jobs.count) :
    GameStepLayout w (D.round sts) (D.atHeap heap) D.first D.saved (D.active sts) := by
  have hN := D.active_le sts
  refine ⟨hn,Nat.lt_of_lt_of_le (by decide) hL.size,fun _ hi _ hj => D.active_inj sts hi hj,
    fun _ _ => rfl,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hW := hL.offsetWords _ (D.active_mem hi).1
    exact (Nat.le_add_right _ _).trans_lt hW
  · intro i hi
    have hc := (D.active_mem hi).1
    have hs := hL.saved
    change D.saved + D.count ≤ D.addrs.graphs at hs
    change D.saved + D.active sts i < D.addrs.graphs
    omega
  · exact (Nat.add_le_add_left hN _).trans hL.graphs
  · exact (Nat.add_le_add_left hN _).trans hL.offsets
  · have hr := hL.replies
    change D.addrs.replies + D.count + 1 ≤ D.addrs.heap at hr
    change D.addrs.replies + (D.round sts).jobs.count + 1 ≤ heap
    omega

/-- The valid certified history gives the facts needed for a core call,
including its degree bound before the final round. -/
theorem ChoiceGameHyp.jobFacts {D : ChoiceLoopData} {β : ℝ} {bh w t heap i : ℕ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hM : ChoiceGameMemory D heap sts mem) (ht : t < D.limit)
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) (hi : i < (D.round sts).jobs.count) :
    (D.round sts).jobs.ChildFits w D.base.M D.base.r (D.round sts).q D.addrs.replies mem i := by
  let B := D.round sts
  let c := D.active sts i
  have hc : c < D.count := (D.active_mem hi).1
  obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion h.denominator
    h.children h.even (coreLevel_le h.coreSize)
  obtain ⟨hv,hl,hLen,hDeg⟩ := gameGraph_bounds_of_inv (hInv c hc)
  have ht' : t ≤ 49*D.L' := by change t < 49*D.L'+1 at ht; omega
  have hWords : (B.jobs.graph i).encode.length ≤ D.geometry.slotWords :=
    hLen.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by
      change t ≤ D.limit + 1
      omega)) _)
  exact ⟨hM.children c hc,(Nat.add_le_add_left hWords _).trans (hL.slots c hc).2,
    hv,hl,le_pow_coreLevel _ _ _,fun v hv => (hDeg v hv).trans (ht'.trans h.degree),
    hL.size,hL.offsetWords c hc⟩

/-- The setup output supplies the graph and active-table fields of the initial
certified state. As the parent inputs precede the tables, the setup keeps them. -/
theorem choiceGameMemory_init {w v : ℕ} {D : ChoiceLoopData} {mem after : ℕ → ℕ}
    {slot : ℕ} (hL : GameFixedLayout w D.geometry)
    (hHost : GraphAt mem D.addrs.host D.base.host)
    (hVerts : ListAt mem D.addrs.verts (finsetWords D.base.verts))
    (hSlot : ∀ i, D.childAddr i = slot+i*D.geometry.slotWords)
    (hEnd : slot+D.count*D.geometry.slotWords ≤ D.addrs.heap)
    (hPost : (buildGameSetupContract w).post
      [D.addrs.graphs,D.addrs.offsets,slot,D.first,D.base.childSize,D.count,D.geometry.slotWords]
      mem v after) :
    ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) after := by
  obtain ⟨graphs,offsets,slots,first,s,k,span,he,hSetup,hG,hO,hChildren,hZero⟩ := hPost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
  have hDir := hL.directory
  have hSaved := hL.saved
  have hOG := hL.graphs
  have hFirst (a : ℕ) (ha : a < D.directory) : after a = mem a := by
    have hd : a < D.addrs.graphs := by
      change D.directory + D.limit ≤ D.saved at hDir
      change D.saved + D.count ≤ D.addrs.graphs at hSaved
      omega
    refine hSetup.2 a (Or.inl hd) (Or.inl (hd.trans_le (Nat.le_of_add_right_le hOG))) ?_
    intro i hi
    have hh := (hL.slots i hi).1
    rw [← hSlot]
    change D.addrs.offsets + D.count ≤ D.childAddr i at hh
    change D.addrs.graphs + D.count ≤ D.addrs.offsets at hOG
    omega
  have hActive : activeChildren D.count (fun _ => ChildState.init) = List.range D.count := by
    simp [activeChildren,ChildState.init]
  refine ⟨WordRAM.ListAt.congr hHost fun a _ ha => hFirst a (ha.trans_le hL.host),
    WordRAM.ListAt.congr hVerts fun a _ ha => hFirst a (ha.trans_le hL.verts),?_,?_,?_,
    fun a ha => hZero a (hEnd.trans ha),le_rfl⟩
  · change ListAt after D.addrs.graphs
      (tabList (activeChildren D.count (fun _ => ChildState.init)).length
        (fun i => D.childAddr ((activeChildren D.count (fun _ => ChildState.init)).getD i 0)))
    rw [hActive,List.length_range]
    intro i hi
    have hk : i < D.count := by simpa using hi
    have he : (List.range D.count).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_range]
    simpa [tabList,List.getElem_range,he,hSlot,List.getElem?_eq_getElem (by simpa using hk :
      i < (List.range D.count).length)] using hG i (by simpa using hi)
  · change ListAt after D.addrs.offsets
      (tabList (activeChildren D.count (fun _ => ChildState.init)).length
        (fun i => D.offset ((activeChildren D.count (fun _ => ChildState.init)).getD i 0)))
    rw [hActive,List.length_range]
    intro i hi
    have hk : i < D.count := by simpa using hi
    have he : (List.range D.count).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getElem_range]
    simpa [tabList,List.getElem_range,he,ChoiceLoopData.offset,
      List.getElem?_eq_getElem (by simpa using hk : i < (List.range D.count).length)] using
      hO i (by simpa using hi)
  · intro c hc
    rw [hSlot]
    exact hChildren c hc

end MinCostFlow.HierPaths
