module

public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotP5

/-!
# The build of a branch at its init: P5's bundle table (`AssemblyFirstInitBun`)

The bundle side of a branch holds P5's bundle table (`AssemblyBranchSide.lean`). At the init it
must hold the bundles of the model state, one slot for each active pair, in the representation
`bunTableHeadroomRep` (the table with the headroom invariant). This file builds that table, as a
procedure `asmFirstInitBunBody` of the build. It makes two calls into P5.
1. **The empty table.** P5's `bundleTableInit` (`bundleTableInit_meetsContract`) writes the
   header of an empty table at the heap pointer, with the bundle cap `k` in its word.
2. **The slots.** P5's `initSlots` (`bunTableHeadroom_initSlots_runs`) reads the specs
   `(slot, cap)` and the assignments `(edge, slot)` from the memory, walks the tour lists of the
   vertices of `rList` and cuts them into bundles of at most `k` ends. The slot-list procedure
   writes the specs and the assignments (`AssemblyFirstInitSlotP5.lean`), and the sorted roots are
   `rList` (`AssemblyFirstInitRoots.lean`).

The run lemma is `asmFirstInitBun_runs`. The empty table has no slot, so the hypotheses of
`initSlots` about the old slots hold at once, and its potential is `0`. The table after the run is
`tableAfterInitSlots` of the empty table. `asmFirstInitBun_model` then ties it to the model state
of the init: at the slot of each active pair it holds the bundles of the pair (`BunTableMatches`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- **P5's table at the init**, `[slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges, asgPtr,
nR, rPtr, heap]`.
1. call the table init `fTbl` on `[slotCap, vCap, eCap, k, heap]`, into register `12` (the end of
   the header);
2. call `initSlots` `fInit` on the table at `heap`, the tour at `tourH`, the `nSlots` specs at
   `specPtr`, the `nEdges` assignments at `asgPtr` and the `nR` vertices at `rPtr`, with heap
   pointer the end of the header, into register `13`;
3. return the end of the new slot blocks. -/
def asmFirstInitBunBody (fTbl fInit : ℕ) : Stmt :=
  .call 12 fTbl [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11] ;;
  .call 13 fInit [.reg 11, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 12] ;;
  .ret (.reg 13)

/-- The procedure never reads random bits. -/
theorem asmFirstInitBunBody_noRand (fTbl fInit : ℕ) : (asmFirstInitBunBody fTbl fInit).NoRand := by
  simp [asmFirstInitBunBody, Stmt.NoRand]

end

public section

/-- `bundleReadPairs` reads only the `2 n` cells from `base`. -/
theorem bundleReadPairs_congr {mem mem' : ℕ → ℕ} {base n : ℕ}
    (h : ∀ a, base ≤ a → a < base + 2 * n → mem' a = mem a) :
    bundleReadPairs mem' base n = bundleReadPairs mem base n := by
  unfold bundleReadPairs
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [h _ (by omega) (by omega), h _ (by omega) (by omega)]

/-- The empty table has potential `0`. -/
theorem bunTableHeadroomRep_phi_empty {slotCap vCap eCap k tbl : ℕ} (mem : ℕ → ℕ) :
    (bunTableHeadroomRep slotCap vCap eCap k).phi tbl ⟨fun _ => none⟩ mem = 0 := by
  simp [bunTableHeadroomRep, bunBlockNB]

/-- The footprint of the empty table is its header. -/
theorem bundleTableFoot_empty {slotCap eCap tbl a : ℕ}
    (h : bundleTableFoot eCap tbl (⟨fun _ => none⟩ : BundleTableMeta slotCap) a) :
    tbl ≤ a ∧ a < tbl + bundleTableFixedSize slotCap eCap := by
  rcases h with h | ⟨j, p, c, hj, -⟩
  · exact h
  · simp at hj

/-- **The core lists as `initSlots` reads them.** Let `cord` be the core rotation of `cs`
(`CoreCordOf`), with the vertices of `cs.G` below `vCap` and its edges below `eCap`. Then each end
lies in at most one list, each list sits at a vertex below `vCap` and holds ends of edges below
`eCap`, the lists have no repeats, and both ends of each core edge lie in the list of their source
in the core graph. These are the facts on `cord` that `asmFirstInitBun_runs` asks. -/
theorem coreCord_initSlots_facts {cs : CompLSFState} {ord cord : ℕ → List End}
    (hC : CoreCordOf cs ord cord) {vCap eCap : ℕ} (hV : ∀ v ∈ cs.G.V, v < vCap)
    (hE : ∀ e ∈ cs.G.E, e < eCap) :
    (∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) ∧
      (∀ v x, x ∈ cord v → v < vCap ∧ x.1 < eCap) ∧ (∀ v, (cord v).Nodup) ∧
      (∀ e ∈ (coreGraph cs.G cs.lsf).E, ∀ side : Bool,
        (e, side) ∈ cord ((coreGraph cs.G cs.lsf).src (e, side))) := by
  obtain ⟨hnd, hmem, hV', -⟩ := coreCord_facts hC
  have hR : cs.lsf.F.R ⊆ cs.G.V := by
    obtain ⟨_, _, hI, -, -, -⟩ := hC
    exact (compLSF_RF_isRSF hI).2.2.1
  refine ⟨fun v₁ v₂ x h₁ h₂ => ((hmem v₁ x).mp h₁).2.symm.trans ((hmem v₂ x).mp h₂).2,
    fun v x hx => ⟨hV v (hR (hV' v x hx)), ?_⟩, hnd, fun e he side => (hmem _ _).mpr ⟨he, rfl⟩⟩
  exact hE x.1 (Finset.mem_sdiff.mp ((hmem v x).mp hx).1).1

/-- **The assigned edges are covered.** Each edge that the slot lists assign is a core edge, so
both of its ends lie in the core list of their source. That source lies in `rList` when `rList`
holds every vertex whose list has an end of a core edge (`rList_of_roots`). This is the hypothesis
`hcov` of `asmFirstInitBun_runs`. -/
theorem slotAssignsL_cov {depth : ℕ} {tr : BundleTreeState depth} {comps : List (Finset ℕ)}
    {G : MGraph} {k B : ℕ} {eL : List ℕ} {mem mem' : ℕ → ℕ} {fe : List ℕ}
    {cmpH bktH nComp ctH heap eCap : ℕ} {S D : List ℕ} {ord cord : ℕ → List End}
    {rList : List ℕ}
    (H : SlotKeyHyps tr comps G tr.cs.lsf.F.F.E k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ tr.cs.lsf.F.F.E) (hGG : tr.cs.G = G)
    (hC : CoreCordOf tr.cs ord cord)
    (hcov : ∀ v x, x ∈ cord v → x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E → v ∈ rList) :
    ∀ es ∈ slotAssignsL mem cmpH bktH B G S D, ∀ side : Bool,
      ∃ v ∈ rList, (es.1, side) ∈ cord v := by
  intro es hes side
  obtain ⟨e, heS, rfl⟩ := List.mem_map.mp hes
  obtain ⟨he, hsel⟩ := (hO.S_mem e).mp heS
  have hF := ((slotSel_iff H hcmp hfe he).mp hsel).1
  have he' : e ∈ tr.cs.G.E := hGG ▸ he
  have hcore : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E := Finset.mem_sdiff.mpr ⟨he', hF⟩
  have hx : (e, side) ∈ cord ((coreGraph tr.cs.G tr.cs.lsf).src (e, side)) :=
    ((coreCord_facts hC).2.1 _ _).mpr ⟨hcore, rfl⟩
  exact ⟨_, hcov _ _ hx hcore, hx⟩

/-- **The run of P5's table at the init.** Let the memory hold the `nSlots` specs at `specPtr`,
the `nEdges` assignments at `asgPtr`, the list `rList` at `rPtr` and the tour at `tourH` with the
core lists `cord`, all below `heap`, with fresh memory from `heap`. Let the specs, the assignments
and `rList` meet the hypotheses of `initSlots`, and let each end of `cord` lie in one list, at a
vertex below `vCap`, with its edge below `eCap`. Then the procedure returns `hEnd` and leaves:
the table `tableAfterInitSlots` of the empty table at `heap` with the headroom invariant, P5's
invariant with `cord`, the tour, the table in `[heap, h₁ + slotBlocksSpace specs)` with
`h₁ = heap + bundleTableFixedSize slotCap eCap`, the new cells of the tour in `[h₁, hEnd)`, the
memory below `heap` outside the tour unchanged, and the cost of `initSlots` plus `220`. -/
theorem asmFirstInitBun_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap k tourH nSlots specPtr nEdges asgPtr nR rPtr heap : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner f : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    (hf : p.procs[f]? =
      some (asmFirstInitBunBody (b + bundleIdxTableInit) (b + bundleIdxInitSlots)))
    {mem : ℕ → ℕ} {pos : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hargs : ∀ a ∈ [slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges, asgPtr, nR, rPtr,
      heap], a < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k)
    (hspec_h : specPtr + 2 * nSlots ≤ heap) (hassign_h : asgPtr + 2 * nEdges ≤ heap)
    (hrPtr_h : rPtr + nR ≤ heap)
    (hspace_w : heap + bundleTableFixedSize slotCap eCap +
      bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hz : ZeroFrom mem heap)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < heap)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < specPtr ∨ specPtr + 2 * nSlots ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + nR ≤ a)
    (hcordU : ∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂)
    (hcordB : ∀ v x, x ∈ cord v → v < vCap ∧ x.1 < eCap)
    (hnSlots : specs.length = nSlots) (hspecs_mem : bundleReadPairs mem specPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap) (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_cap4 : ∀ sb ∈ specs, 4 * (slotEdgesOf assigns sb.1).card ≤ sb.2)
    (hnEdges : assigns.length = nEdges)
    (hassigns_mem : bundleReadPairs mem asgPtr nEdges = assigns)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hnR : rList.length = nR) (hrList_mem : ListAt mem rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w) (hrList_nd : rList.Nodup)
    (hcord_nd : ∀ v ∈ rList, (cord v).Nodup)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v) :
    let h₁ := heap + bundleTableFixedSize slotCap eCap
    let S' := tableAfterInitSlots (fun _ => none) specs assigns cord rList k
    let m' := allocSlotBlocksMeta (⟨fun _ => none⟩ : BundleTableMeta slotCap) specs h₁
    ∃ body, p.procs[f]? = some body ∧ ∃ st' c hEnd tx',
      Runs w p ω body (startState [slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges,
        asgPtr, nR, rPtr, heap] mem pos) (.returned hEnd) st' c ∧
      h₁ + slotBlocksSpace specs ≤ hEnd ∧ hEnd ≤ h₁ + bundleInitSlotsSpace TS specs cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep heap S' m' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, bundleTableFoot eCap heap m' a → heap ≤ a ∧ a < h₁ + slotBlocksSpace specs) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h₁ + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ a < heap, ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem a) ∧
      c + (bunTableHeadroomRep slotCap vCap eCap k).phi heap m' st'.mem +
          htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + bunPhiMul * (2 * nEdges) +
          htour.rep.phi tourH tx₀ mem + 220 := by
  intro h₁ S' m'
  have hu := bundleProcs_unpack hp
  have hW : ∀ a ∈ [slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges, asgPtr, nR, rPtr,
      heap], a < 2 ^ w := hargs
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  obtain ⟨wS, wV, wE, wK, wT, wN, wSp, wNE, wA, wNR, wR, wH⟩ := hW
  have hfixW : h₁ < 2 ^ w := by
    have : h₁ ≤ h₁ + bundleInitSlotsSpace TS specs cord rList := Nat.le_add_right _ _
    omega
  -- 1. the empty table
  set st0 := startState [slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges, asgPtr, nR,
    rPtr, heap] mem pos with hst0
  have hT := bundleTableInit_meetsContract (w := w) (slotCap := slotCap) (vCap := vCap)
    (eCap := eCap) (k := k) (h := heap) hu.2.1 [slotCap, vCap, eCap, k, heap] mem pos ω
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro a (rfl | rfl | rfl | rfl | rfl)
        <;> assumption)
    ⟨rfl, hw16, wV, wK, hfixW, hz⟩
  obtain ⟨bodyT, hbT, oT, stT, cT, hrunT, ⟨hret, hzT, hlowT, hrepT, hkT⟩, hcT⟩ := hT
  have hbT' : p.procs[b + bundleIdxTableInit]? = some bundleTableInitStmt := hu.2.1.head
  rw [hbT'] at hbT
  cases hbT
  have hargsT : evalArgs w st0 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11] =
      some [slotCap, vCap, eCap, k, heap] := by
    simp [evalArgs, Expr.eval, hst0, startState]
  set s1 : State := { stT with regs := Function.update st0.regs 12 oT.value } with hs1
  have hcallT : Runs w p ω (.call 12 (b + bundleIdxTableInit) [.reg 0, .reg 1, .reg 2, .reg 3,
      .reg 11]) st0 .normal s1 (argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11] + cT + 1) :=
    runs_call_iff.mpr ⟨_, _, oT, stT, cT, hargsT, hbT', hrunT, rfl, rfl, rfl⟩
  -- the memory after the table init
  set mem₀ := stT.mem with hmem₀
  have hlow : ∀ a < heap, mem₀ a = mem a := hlowT
  have hzero0 : ZeroFrom mem₀ h₁ := fun a ha => hzT a (by rw [hret]; exact ha)
  have hspecs_mem₀ : bundleReadPairs mem₀ specPtr nSlots = specs := by
    rw [bundleReadPairs_congr fun a _ ha => hlow a (by omega)]; exact hspecs_mem
  have hassigns_mem₀ : bundleReadPairs mem₀ asgPtr nEdges = assigns := by
    rw [bundleReadPairs_congr fun a _ ha => hlow a (by omega)]; exact hassigns_mem
  have hrList_mem₀ : ListAt mem₀ rPtr rList := fun i hi => by
    rw [hlow _ (by rw [hnR] at hi; omega)]; exact hrList_mem i hi
  have htloc := htour.rep_local tourH cord tx₀ mem mem₀
    (fun a ha => (hlow a (htour_foot_lt a ha)).symm)
  have htour_rep₀ : htour.rep.rep tourH cord tx₀ mem₀ := htloc.1 htour_rep
  -- 2. the slots
  have hrep0 : (bunTableHeadroomRep slotCap vCap eCap k).rep heap (fun _ => none)
      ⟨fun _ => none⟩ mem₀ :=
    ⟨hrepT, hkT, fun j B _ _ hS _ => by simp at hS⟩
  have hinv0 : bunRestartInv vCap eCap (fun _ => none : Fin slotCap → Option BundleState) cord :=
    ⟨⟨hcordU, fun j B hS => by simp at hS⟩, hcordB⟩
  obtain ⟨bodyI, hbI, st', c, hEnd, tx', hrunI, hhLo, hhHi, hzf, hrep', hinv', htr', hfootB',
      hfootT', hfr, hc⟩ :=
    bunTableHeadroom_initSlots_runs (S₀ := (fun _ => none)) (m₀ := ⟨fun _ => none⟩)
      (mem₀ := mem₀) (pos₀ := stT.pos) (tx₀ := tx₀) (ω := ω) (specs := specs)
      (assigns := assigns) (cord := cord) (rList := rList) (h := h₁) (tbl := heap)
      (tourH := tourH) (nSlots := nSlots) (slotSpecPtr := specPtr) (nEdges := nEdges)
      (edgeAssignPtr := asgPtr) (nR := nR) (rPtr := rPtr)
      hp htour hw16 hk1 wT (le_refl _)
      (fun a ha => by have := (bundleTableFoot_empty ha).2; omega)
      (by omega) (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (by omega)
      (Or.inl (by omega)) hspace_w hrep0 hinv0 hzero0 htour_rep₀
      (fun a ha => by have := htour_foot_lt a ha; omega)
      (fun a ha => Or.inl (htour_foot_lt a ha))
      (fun a _ j ptr c hj => by simp at hj)
      htour_foot_disj_spec htour_foot_disj_r hnSlots hspecs_mem₀ hspecs_lt hspecs_nd
      (fun sb _ hlt => rfl) hspecs_cap4 hnEdges hassigns_mem₀ hassigns_in hassigns_nd
      (fun es _ j B hB => by simp at hB) (by omega) hnR hrList_mem₀ hrList_lt hrList_nd
      hcord_nd hcov
  have hbI' : p.procs[b + bundleIdxInitSlots]? =
      some (bundleInitSlotsStmt (b + bundleIdxDllPush) bTourList) := hu.2.2.2.2.2.2.2.1.head
  have hr0 : ∀ i, i < 12 → s1.regs i =
      [slotCap, vCap, eCap, k, tourH, nSlots, specPtr, nEdges, asgPtr, nR, rPtr, heap].getD i 0 :=
    fun i hi => by simp [hs1, hst0, startState, Function.update_of_ne (show i ≠ 12 by omega)]
  have hr12 : s1.regs 12 = h₁ := by rw [hs1]; simp only [Function.update_self]; exact hret
  have hargsI : evalArgs w s1 [.reg 11, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
      .reg 12] = some [heap, tourH, nSlots, specPtr, nEdges, asgPtr, nR, rPtr, h₁] := by
    simp only [evalArgs, Expr.eval, hr0 11 (by decide), hr0 4 (by decide), hr0 5 (by decide),
      hr0 6 (by decide), hr0 7 (by decide), hr0 8 (by decide), hr0 9 (by decide),
      hr0 10 (by decide), hr12]
    rfl
  set s2 : State := { st' with regs := Function.update s1.regs 13 hEnd } with hs2
  have hcallI : Runs w p ω (.call 13 (b + bundleIdxInitSlots) [.reg 11, .reg 4, .reg 5, .reg 6,
      .reg 7, .reg 8, .reg 9, .reg 10, .reg 12]) s1 .normal s2
      (argsSize [.reg 11, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 12] +
        c + 1) := by
    rw [hbI'] at hbI
    cases hbI
    exact runs_call_iff.mpr ⟨_, _, .returned hEnd, st', c, hargsI, hbI', hrunI, rfl, rfl, rfl⟩
  have hret' : Runs w p ω (.ret (.reg 13)) s2 (.returned hEnd) s2 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, hs2], rfl, rfl, rfl⟩
  have hrun := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallT,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallI, hret', rfl⟩), rfl⟩)
  refine ⟨_, hf, s2, _, hEnd, tx', hrun, hhLo, hhHi, hzf, hrep', hinv', htr', ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hfootB' a ha with ha0 | ⟨ha1, ha2⟩
    · have := bundleTableFoot_empty ha0; omega
    · omega
  · intro a ha
    rcases hfootT' a ha with h0 | h1'
    · exact Or.inl h0
    · exact Or.inr h1'
  · intro a ha hnt
    show st'.mem a = mem a
    rw [hfr a (by omega) (fun h0 => by have := (bundleTableFoot_empty h0).1; omega) hnt]
    exact hlow a ha
  · have hphi0 := bunTableHeadroomRep_phi_empty (slotCap := slotCap) (vCap := vCap)
      (eCap := eCap) (k := k) (tbl := heap) mem₀
    rw [hphi0, ← htloc.2] at hc
    have e2 : s2.mem = st'.mem := rfl
    rw [e2]
    simp only [bundleTableInitContract] at hcT
    have hc' : c + (bunTableHeadroomRep slotCap vCap eCap k).phi heap m' st'.mem +
        htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + bunPhiMul * (2 * nEdges) + 0 +
          htour.rep.phi tourH tx₀ mem := hc
    simp only [argsSize, Expr.size]
    omega

end

end MinCostFlow.SparseCore.Program
