module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotModel
public import MinCostFlow.SparseCore.Program.BundleInitProcs
public import MinCostFlow.SparseCore.Program.BunRestartModel
import Mathlib.Tactic

/-!
# The slot lists as the input of P5's init of the slots (`AssemblyFirstInitSlotP5`)

P5's `initSlots` (`bunTableHeadroom_initSlots_runs`) reads two lists of pairs of words
(`bundleReadPairs`): the specs `(slot, cap)` of the new slots, and the assignments
`(edge, slot)` of the edges to the slots. The slot-list procedure (`slotList_runs`) writes both.
This file names them (`slotSpecsL`, `slotAssignsL`), reads them back from the memory
(`slotListOut_specs_read`, `slotListOut_assigns_read`), and proves the facts on them that
`initSlots` asks: the slots are distinct and below the number of keys, the cap of a slot is four
times the number of its edges, and each edge is assigned once, to a slot with a spec.

The main model fact is `slotEdgesOf_slotOfD`. The edges that the assignments give to the slot of an
active pair `(C, b)` are the core edges with tail in `C` and bucket `b` (`bucketCoreEdges`). These
are the edges of the bundle state of the pair at the init, so P5's init of that slot agrees with the
model (`tableAfterInitSlots_bunAgree`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.Bundle
open MinCostFlow.DynSpanner MinCostFlow.SparseCore.Program.Restart

/-- The specs of the new slots: slot `s` below `|D|` with cap four times the number of selected
edges with slot `s`. -/
noncomputable def slotSpecsL (mem : ℕ → ℕ) (cmpH bktH B : ℕ) (G : MGraph) (S D : List ℕ) :
    List (ℕ × ℕ) :=
  (List.range D.length).map fun s =>
    (s, 4 * (S.filter fun e => D.idxOf (slotKeyOf mem cmpH bktH B G e) = s).length)

/-- The assignments: each selected edge with the index of its key in `D`. -/
noncomputable def slotAssignsL (mem : ℕ → ℕ) (cmpH bktH B : ℕ) (G : MGraph) (S D : List ℕ) :
    List (ℕ × ℕ) :=
  S.map fun e => (e, D.idxOf (slotKeyOf mem cmpH bktH B G e))

section Read

variable {mem mem' : ℕ → ℕ} {G : MGraph} {fe : List ℕ}
  {cmpH bktH nComp k B ctH heap eCap : ℕ} {S D : List ℕ}

/-- **The specs in the memory.** -/
theorem slotListOut_specs_read
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) :
    bundleReadPairs mem' (heap + 3 + eCap + 6 * G.m) D.length =
      slotSpecsL mem cmpH bktH B G S D := by
  unfold bundleReadPairs slotSpecsL
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨h1, h2⟩ := hO.specs s (List.mem_range.mp hs)
  rw [h1, h2]

/-- **The assignments in the memory.** -/
theorem slotListOut_assigns_read
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) :
    bundleReadPairs mem' (heap + 3 + eCap + 8 * G.m) S.length =
      slotAssignsL mem cmpH bktH B G S D := by
  apply List.ext_getElem (by simp [bundleReadPairs, slotAssignsL])
  intro i h1 _
  have hi : i < S.length := by simpa [bundleReadPairs] using h1
  obtain ⟨a1, a2⟩ := hO.asg i hi
  simp only [bundleReadPairs, slotAssignsL, List.getElem_map, List.getElem_range]
  rw [a1, a2]

end Read

section Facts

variable {mem : ℕ → ℕ} {G : MGraph} {cmpH bktH B : ℕ} {S D : List ℕ}

theorem slotSpecsL_length : (slotSpecsL mem cmpH bktH B G S D).length = D.length := by
  simp [slotSpecsL]

theorem slotSpecsL_fst : (slotSpecsL mem cmpH bktH B G S D).map Prod.fst = List.range D.length := by
  simp [slotSpecsL, List.map_map, Function.comp_def]

theorem slotAssignsL_length : (slotAssignsL mem cmpH bktH B G S D).length = S.length := by
  simp [slotAssignsL]

theorem slotAssignsL_fst : (slotAssignsL mem cmpH bktH B G S D).map Prod.fst = S := by
  simp [slotAssignsL, List.map_map, Function.comp_def]

/-- The slots of the specs are below the number of keys, so below any cap at least `|D|`. -/
theorem slotSpecsL_lt {slotCap : ℕ} (hcap : D.length ≤ slotCap) :
    ∀ sb ∈ slotSpecsL mem cmpH bktH B G S D, sb.1 < slotCap := by
  intro sb hsb
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsb
  have := List.mem_range.mp hs
  exact lt_of_lt_of_le this hcap

/-- The slots of the specs are distinct. -/
theorem slotSpecsL_nodup : ((slotSpecsL mem cmpH bktH B G S D).map Prod.fst).Nodup := by
  rw [slotSpecsL_fst]
  exact List.nodup_range

/-- An edge has slot `s` in the assignments exactly when it is selected and its key has index
`s`. -/
theorem mem_slotEdgesOf_iff (s e : ℕ) :
    e ∈ slotEdgesOf (slotAssignsL mem cmpH bktH B G S D) s ↔
      e ∈ S ∧ D.idxOf (slotKeyOf mem cmpH bktH B G e) = s := by
  unfold slotEdgesOf slotAssignsL
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, t⟩, ⟨⟨x, hx, hxe⟩, ht⟩, rfl⟩
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl⟩ := hxe
    exact ⟨hx, ht⟩
  · rintro ⟨he, hs⟩
    exact ⟨(e, D.idxOf (slotKeyOf mem cmpH bktH B G e)), ⟨⟨e, he, rfl⟩, hs⟩, rfl⟩

/-- **The cap of a slot is four times the number of its edges** (at least). -/
theorem slotSpecsL_cap4 :
    ∀ sb ∈ slotSpecsL mem cmpH bktH B G S D,
      4 * (slotEdgesOf (slotAssignsL mem cmpH bktH B G S D) sb.1).card ≤ sb.2 := by
  intro sb hsb
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hsb
  refine Nat.mul_le_mul_left 4 ?_
  unfold slotEdgesOf slotAssignsL
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  rw [List.filter_map, List.map_map, List.length_map]
  congr 1

end Facts

section Assigns

variable {mem mem' : ℕ → ℕ} {G : MGraph} {fe : List ℕ}
  {cmpH bktH nComp k B ctH heap eCap : ℕ} {S D : List ℕ}

/-- The key of a selected edge is in `D`, so its slot is below `|D|`. -/
theorem slotListOut_idxOf_lt
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) {e : ℕ}
    (he : e ∈ S) : D.idxOf (slotKeyOf mem cmpH bktH B G e) < D.length :=
  List.idxOf_lt_length_of_mem ((hO.D_mem _).mpr ⟨e, he, rfl⟩)

/-- **Each assignment is an edge below `eCap` with a slot that has a spec.** -/
theorem slotListOut_assigns_in
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hE : ∀ e ∈ G.E, e < eCap) :
    ∀ es ∈ slotAssignsL mem cmpH bktH B G S D,
      es.1 < eCap ∧ es.2 ∈ (slotSpecsL mem cmpH bktH B G S D).map Prod.fst := by
  intro es hes
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hes
  refine ⟨hE e ((hO.S_mem e).mp he).1, ?_⟩
  rw [slotSpecsL_fst]
  exact List.mem_range.mpr (slotListOut_idxOf_lt hO he)

/-- Each edge is assigned once. -/
theorem slotListOut_assigns_nodup
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D) :
    ((slotAssignsL mem cmpH bktH B G S D).map Prod.fst).Nodup := by
  rw [slotAssignsL_fst]
  exact hO.S_nodup

end Assigns

/-! ## The edges of the slot of an active pair -/

section Model

variable {depth : ℕ} {tr : BundleTreeState depth} {comps : List (Finset ℕ)} {G : MGraph}
  {Fe : Finset ℕ} {k B : ℕ} {eL : List ℕ} {mem mem' : ℕ → ℕ} {fe : List ℕ}
  {cmpH bktH nComp ctH heap eCap : ℕ} {S D : List ℕ}

/-- The key of an edge of `G` is the key of its pair: the component of its tail and its bucket. -/
theorem slotKeyOf_eq_pairKey (H : SlotKeyHyps tr comps G Fe k B eL)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hbk : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (tr.origBucket e)) {e : ℕ} (he : e ∈ G.E) :
    slotKeyOf mem cmpH bktH B G e = pairKey comps B (compOf G (G.tail e), tr.origBucket e) := by
  unfold slotKeyOf pairKey
  rw [slotCOf_eq H hcmp he, hbk e he]
  rfl

/-- In a list without repeats, two members have the same index only when they are equal. -/
theorem idxOf_inj_of_mem {D : List ℕ} {x y : ℕ} (hx : x ∈ D) (hy : y ∈ D)
    (h : D.idxOf x = D.idxOf y) : x = y := by
  have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
  have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
  simp only [h] at e1
  exact e1.symm.trans e2

/-- **The edges of the slot of an active pair** `p` are the core edges with tail in `p.1` and
bucket `p.2`. Here `C₀` is a graph whose edges are the edges of `G` outside `Fe` and whose tails lie
in the same components as the tails in `G` (the core graph at the init). -/
theorem slotEdgesOf_slotOfD (H : SlotKeyHyps tr comps G Fe k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hbk : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (tr.origBucket e))
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ Fe) {C₀ : MGraph}
    (hCE : ∀ e, e ∈ C₀.E ↔ e ∈ G.E ∧ e ∉ Fe)
    (hCt : ∀ e ∈ G.E, ∀ C ∈ components G, C₀.tail e ∈ C ↔ G.tail e ∈ C)
    {p : Finset ℕ × ℤ} (hp : p ∈ activePairs tr) :
    slotEdgesOf (slotAssignsL mem cmpH bktH B G S D) (slotOfD comps B D p) =
      bucketCoreEdges C₀ tr.origBucket p.1 p.2 := by
  classical
  obtain ⟨hl, -⟩ := (H.act_iff p).mp hp
  have hpc : p.1 ∈ components G := (Finset.mem_filter.mp hl).1
  obtain ⟨hp1, hp2⟩ := H.of_active hp
  have hpD : pairKey comps B p ∈ D :=
    (slotListOut_mem_D H hO hcmp hbk hfe _).mpr ((mem_slotKeys_iff H _).mpr ⟨p, hp, rfl⟩)
  ext e
  rw [mem_slotEdgesOf_iff]
  unfold bucketCoreEdges slotOfD
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨heS, hidx⟩
    obtain ⟨he, hsel⟩ := (hO.S_mem e).mp heS
    obtain ⟨hF, -⟩ := (slotSel_iff H hcmp hfe he).mp hsel
    have heD : slotKeyOf mem cmpH bktH B G e ∈ D := (hO.D_mem _).mpr ⟨e, heS, rfl⟩
    have hkey := idxOf_inj_of_mem heD hpD hidx
    rw [slotKeyOf_eq_pairKey H hcmp hbk he] at hkey
    have hpair := pairKey_inj (H.tail_comp he) hp1 (H.code_lt e he) hp2 hkey
    have htV : G.tail e ∈ G.V := (H.valid e he).1
    have htp : G.tail e ∈ p.1 := by rw [← hpair]; exact self_mem_compOf htV
    exact ⟨(hCE e).mpr ⟨he, hF⟩, (hCt e he p.1 hpc).mpr htp, by rw [← hpair]⟩
  · rintro ⟨heC, htC, hb⟩
    obtain ⟨he, hF⟩ := (hCE e).mp heC
    have htp : G.tail e ∈ p.1 := (hCt e he p.1 hpc).mp htC
    have hcp : p.1 = compOf G (G.tail e) := comp_eq_compOf hpc htp
    have hsel : slotSel mem cmpH G fe k e = true :=
      (slotSel_iff H hcmp hfe he).mpr ⟨hF, hcp ▸ hl⟩
    refine ⟨(hO.S_mem e).mpr ⟨he, hsel⟩, ?_⟩
    rw [slotKeyOf_eq_pairKey H hcmp hbk he, ← hcp, hb]

/-- At the init, the core graph has the two properties that `slotEdgesOf_slotOfD` asks of `C₀`:
its edges are the edges of `G` outside the forest, and the root of a vertex lies in the same
components as the vertex (`root_mem_comp_iff`). -/
theorem coreGraph_tail_mem_iff {L : LSF} (hRF : L.F.IsRootedSpanningForestOf G)
    (hG : G.IsValid) : ∀ e ∈ G.E, ∀ C ∈ components G,
      (coreGraph G L).tail e ∈ C ↔ G.tail e ∈ C :=
  fun e he _ hC => root_mem_comp_iff hRF (hG e he).1 hC

theorem coreGraph_mem_E_iff (L : LSF) (e : ℕ) :
    e ∈ (coreGraph G L).E ↔ e ∈ G.E ∧ e ∉ L.F.F.E :=
  Finset.mem_sdiff

/-- **P5's init of the slots matches the bundles of the model.** Take the specs and the assignments
of the slot lists, with the forest of the LSF as `Fe`. Let the bundle of each pair be
`initBundleFor` of its core edges (as at the init), let `cord` be the core rotation (`CoreCordOf`),
and let `rList` be increasing, made of core vertices, and hold every vertex whose list in `cord` has
an end of a core edge. Then the table after `initSlots` holds, at the slot of each active pair, a
bundle state that agrees with the bundle of the pair (`BunTableMatches`). -/
theorem bunTableMatches_slotOfD {ord cord : ℕ → List End}
    (H : SlotKeyHyps tr comps G tr.cs.lsf.F.F.E k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hbk : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (tr.origBucket e))
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ tr.cs.lsf.F.F.E)
    (hGG : tr.cs.G = G) (hRF : tr.cs.lsf.F.IsRootedSpanningForestOf G)
    (hbun : ∀ p, tr.bun p = initBundleFor tr.cs ord
      (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket p.1 p.2) k)
    (hk : 1 ≤ k) (hC : CoreCordOf tr.cs ord cord) {slotCap : ℕ} (hcap : D.length ≤ slotCap)
    {S₀ : BundleTableState slotCap} {rList : List ℕ} (hr : rList.Pairwise (· < ·))
    (hrsub : ∀ v ∈ rList, v ∈ (coreGraph tr.cs.G tr.cs.lsf).V)
    (hcov : ∀ v x, x ∈ cord v → x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E → v ∈ rList) :
    BunTableMatches tr (slotOfD comps B D)
      (tableAfterInitSlots S₀ (slotSpecsL mem cmpH bktH B G S D)
        (slotAssignsL mem cmpH bktH B G S D) cord rList k) := by
  intro p hp
  have hpD : pairKey comps B p ∈ D :=
    (slotListOut_mem_D H hO hcmp hbk hfe _).mpr ((mem_slotKeys_iff H _).mpr ⟨p, hp, rfl⟩)
  have hs : slotOfD comps B D p < D.length := List.idxOf_lt_length_of_mem hpD
  have hCE : ∀ e, e ∈ (coreGraph tr.cs.G tr.cs.lsf).E ↔ e ∈ G.E ∧ e ∉ tr.cs.lsf.F.F.E := by
    intro e
    rw [hGG]
    exact Finset.mem_sdiff
  have hCt : ∀ e ∈ G.E, ∀ C ∈ components G,
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C ↔ G.tail e ∈ C := by
    intro e he C hC
    rw [hGG]
    exact root_mem_comp_iff hRF (H.valid e he).1 hC
  have hEeq := slotEdgesOf_slotOfD H hO hcmp hbk hfe hCE hCt hp
  have hj : (⟨slotOfD comps B D p, lt_of_lt_of_le hs hcap⟩ : Fin slotCap).1 ∈
      (slotSpecsL mem cmpH bktH B G S D).map Prod.fst := by
    rw [slotSpecsL_fst]
    exact List.mem_range.mpr hs
  have hsub : slotEdgesOf (slotAssignsL mem cmpH bktH B G S D) (slotOfD comps B D p) ⊆
      (coreGraph tr.cs.G tr.cs.lsf).E := by
    rw [hEeq]
    unfold bucketCoreEdges
    exact Finset.filter_subset _ _
  obtain ⟨B', hB', hag⟩ := tableAfterInitSlots_bunAgree (S₀ := S₀) hk hC hj hsub hr hrsub
    fun v x hx hxE => hcov v x hx (hsub hxE)
  refine ⟨lt_of_lt_of_le hs hcap, B', hB', ?_⟩
  rw [hbun p]
  simp only at hag
  rw [hEeq] at hag
  exact hag

end Model

/-! ## The list of vertices that `initSlots` walks -/

/-- A vertex whose list in the core rotation has an end is a core vertex: the core rotation gives
the empty list at every other vertex. -/
theorem coreCord_mem_V {cs : CompLSFState} {ord cord : ℕ → List End} (hC : CoreCordOf cs ord cord)
    {v : ℕ} {x : End} (hx : x ∈ cord v) : v ∈ (coreGraph cs.G cs.lsf).V := by
  obtain ⟨_, _, hI, ρ, -, rfl⟩ := hC
  unfold coreRotation at hx
  dsimp only at hx
  split_ifs at hx with h
  · exact h
  · simp at hx

/-- **The roots of the forest serve as `rList`.** If the members of `rList` are the roots
(`rootsList_runs` on the roots of P4's export), then `rList` is made of core vertices and holds every
vertex whose list in the core rotation has an end. -/
theorem rList_of_roots {cs : CompLSFState} {ord cord : ℕ → List End}
    (hC : CoreCordOf cs ord cord) {roots rList : List ℕ} (hroots : roots.toFinset = cs.lsf.F.R)
    (hmem : ∀ x, x ∈ rList ↔ x ∈ roots) :
    (∀ v ∈ rList, v ∈ (coreGraph cs.G cs.lsf).V) ∧
      (∀ v x, x ∈ cord v → x.1 ∈ (coreGraph cs.G cs.lsf).E → v ∈ rList) := by
  have hV : ∀ v, v ∈ (coreGraph cs.G cs.lsf).V ↔ v ∈ rList := by
    intro v
    rw [hmem, ← List.mem_toFinset, hroots]
    exact Iff.rfl
  exact ⟨fun v hv => (hV v).mpr hv, fun v x hx _ => (hV v).mp (coreCord_mem_V hC hx)⟩

end MinCostFlow.SparseCore.Program
