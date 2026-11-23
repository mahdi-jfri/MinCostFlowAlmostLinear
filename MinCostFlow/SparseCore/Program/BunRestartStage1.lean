module

public import MinCostFlow.SparseCore.Program.BunRestartCore

/-!
# The restart of the bundles: the setting and phases A to C (`BunRestartStage1`)

`BRCtx` collects the hypotheses of a run of the restart that do not change along the run: the
table and the tour before the run, P5's invariant, the core rotation, the listed slots, and the
word size. `BRCtx.keys_ok` and the other lemmas derive the facts that the phases need from it.

`brStage1_runs` chains phases A, B and C. After them, the specs, the pairs and the owners are in
memory, and the tour still holds `cord`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}

/-- **The setting of a run of the restart.** -/
structure BRCtx (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    (slotCap tbl tourH slotsPtr h : ℕ) (slots : List ℕ) (S : Fin slotCap → Option BundleState)
    (m : BundleTableMeta slotCap) (cord : ℕ → List End) (tx₀ : htour.rep.τ)
    (cs : CompLSFState) (ord : ℕ → List End) (mem : ℕ → ℕ) : Prop where
  hw : 16 ≤ 2 ^ w
  eCap_lt : 2 * eCap < 2 ^ w
  vCap_le : vCap ≤ 2 ^ w
  tourH_lt : tourH < 2 ^ w
  rep : BundleTableRepAt slotCap vCap eCap tbl S m mem
  inv : bunRestartInv vCap eCap S cord
  core : CoreCordOf cs ord cord
  tourRep : htour.rep.rep tourH cord tx₀ mem
  footT : ∀ a, bundleTableFoot eCap tbl m a → a < h
  footR : ∀ a, htour.rep.foot tourH tx₀ a → a < h
  disj : ∀ a, bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx₀ a
  act : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
    B.edges ⊆ (coreGraph cs.G cs.lsf).E
  nd : slots.Nodup
  list : ListAt mem slotsPtr slots
  sl : slotsPtr + slots.length ≤ h
  zero : ZeroFrom mem h

namespace BRCtx

variable {htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner}
  {slotCap tbl tourH slotsPtr h : ℕ} {slots : List ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {cord : ℕ → List End} {tx₀ : htour.rep.τ}
  {cs : CompLSFState} {ord : ℕ → List End} {mem : ℕ → ℕ}

theorem act' (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) :
    ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B := fun s hs => by
  obtain ⟨hsc, B, hB, -⟩ := C.act s hs
  exact ⟨hsc, B, hB⟩

/-- The edges of a listed slot are core edges below `eCap`. -/
theorem edge_facts (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {s : ℕ} (hs : s ∈ slots) {e : ℕ} (he : e ∈ (slotB S s).edges) :
    e < eCap ∧ e ∈ (coreGraph cs.G cs.lsf).E := by
  obtain ⟨hsc, B, hB, hsub⟩ := C.act s hs
  rw [slotB_eq hsc hB] at he
  obtain ⟨-, -, ⟨nB, -, -, hE, -⟩, -⟩ := slot_facts C.rep hsc hB
  exact ⟨hE e he, hsub he⟩

theorem edgeTot_le_m (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) :
    edgeTot S slots ≤ cs.G.m :=
  (edgeTot_le_card C.nd (fun _ h₁ _ h₂ hne => slotB_edges_disjoint C.rep C.act' h₁ h₂ hne)
    (U := (coreGraph cs.G cs.lsf).E) fun _ hs _ he => (C.edge_facts hs he).2).trans
    (coreGraph_m_le cs.G cs.lsf)

theorem edgeTot_le_eCap
    (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) :
    edgeTot S slots ≤ eCap := by
  have := edgeTot_le_card C.nd (fun _ h₁ _ h₂ hne => slotB_edges_disjoint C.rep C.act' h₁ h₂ hne)
    (U := Finset.range eCap) fun s hs e he => Finset.mem_range.mpr (C.edge_facts hs he).1
  simpa using this

/-- The facts on the keys that phase C needs: each key is below `2 eCap`, and its end lies in the
tour list of its owner, which is below `vCap`, and in no other. -/
theorem keys_ok (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) :
    ∀ k ∈ allKeys eCap tbl S m mem slots, k < 2 * eCap ∧ brOwn cs k < vCap ∧
      endOfKey k ∈ cord (brOwn cs k) ∧ ∀ v', endOfKey k ∈ cord v' → v' = brOwn cs k := by
  intro k hk
  obtain ⟨s, hs, hks⟩ := (mem_allKeys C.rep C.act').mp hk
  obtain ⟨h1, h2⟩ := brOwn_spec C.core (C.edge_facts hs hks).2
  exact ⟨allKeys_lt C.rep C.act' hk, (C.inv.2 _ _ h1).1, h1, h2⟩

end BRCtx

variable {htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner}
  {slotCap tbl tourH slotsPtr h : ℕ} {slots : List ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {cord : ℕ → List End} {tx₀ : htour.rep.τ}
  {cs : CompLSFState} {ord : ℕ → List End} {mem : ℕ → ℕ}

/-- **Phases A to C.** With `n` slots and `E` edges, after phases A, B and C the registers hold
the layout, the heap pointer `r19` lies in `[h1, h1 + 2 E q)` with `h1 = h + 6 n + 10 E`, the
specs, the pairs (`allPairs`) and the owners of the keys are in memory, and the tour holds `cord`
in a new concrete state. Memory below `h` outside the footprint of the tour is kept. The cost is
paid as in the three phases. -/
theorem brStage1_runs (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {bWalk : ℕ} (hpWalk : p.procs[bWalk]? = some outWalkBody)
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots +
      2 * edgeTot S slots * TS.querySpace < 2 ^ w)
    {st : State} (h0 : st.regs 0 = tbl) (h1 : st.regs 1 = tourH)
    (h2 : st.regs 2 = slots.length) (h3 : st.regs 3 = slotsPtr) (h4 : st.regs 4 = h)
    (hmem : st.mem = mem) :
    ∃ stA stB stC cA cB cC txC, Runs w p ω brPhaseA st .normal stA cA ∧
      Runs w p ω (brPhaseB bWalk) stA .normal stB cB ∧
      Runs w p ω (brPhaseC bOwner) stB .normal stC cC ∧
      BRRegs stC.regs tbl tourH slots.length slotsPtr h slotCap eCap ∧
      BRRegsL stC.regs h slots.length (edgeTot S slots) ∧
      h + 6 * slots.length + 10 * edgeTot S slots ≤ stC.regs 19 ∧
      stC.regs 19 ≤ h + 6 * slots.length + 10 * edgeTot S slots +
        2 * edgeTot S slots * TS.querySpace ∧
      ZeroFrom stC.mem (stC.regs 19) ∧
      bundleReadPairs stC.mem (h + 4 * slots.length) slots.length = brSpecs S slots ∧
      bundleReadPairs stC.mem (h + 6 * slots.length + 2 * edgeTot S slots) (edgeTot S slots) =
        allPairs eCap tbl S m mem slots ∧
      ListAt stC.mem (h + 6 * slots.length + 4 * edgeTot S slots)
        ((allKeys eCap tbl S m mem slots).map (brOwn cs)) ∧
      htour.rep.rep tourH cord txC stC.mem ∧
      (∀ a, htour.rep.foot tourH txC a → htour.rep.foot tourH tx₀ a ∨
        (h + 6 * slots.length + 10 * edgeTot S slots ≤ a ∧ a < stC.regs 19)) ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx₀ a → stC.mem a = mem a) ∧
      cA + cB + cC + htour.rep.phi tourH txC stC.mem ≤
        (60 * slots.length + 120) + (60 * edgeTot S slots +
          60 * (slots.map fun s => (slotB S s).vertices.card).sum + 50 * slots.length + 10) +
        (2 * edgeTot S slots * (TS.mul * ordStoreLog eCap + 140) + 20) +
        htour.rep.phi tourH tx₀ mem := by
  set n := slots.length with hn
  set E := edgeTot S slots with hE
  have hw := C.hw
  obtain ⟨stA, cA, hrA, hRA, hLA, h19A, h20A, hspecA, hfrA, hcA⟩ :=
    brPhaseA_runs (p := p) (ω := ω) C.rep C.footT C.act' C.list C.sl hw (by omega) h0 h1 h2 h3
      h4 hmem
  have hlowA : ∀ a < h, stA.mem a = mem a := fun a ha => (hfrA a (Or.inl (by omega)))
  obtain ⟨stB, cB, hrB, hRB, hLB, h19B, hkeysB, hfrB, hcB⟩ :=
    brPhaseB_runs (p := p) (ω := ω) hpWalk C.rep C.footT C.act' hw (by omega) hRA hLA h20A
      (fun i hi => (hspecA i hi).1) hlowA
  have hlowB : ∀ a < h, stB.mem a = mem a := fun a ha =>
    (hfrB a (Or.inl (by omega))).trans (hlowA a ha)
  have hhiB : ∀ a, h + 6 * n + 10 * E ≤ a → stB.mem a = mem a := fun a ha =>
    (hfrB a (Or.inr (by omega))).trans (hfrA a (Or.inr (by omega)))
  have hrepB : htour.rep.rep tourH cord tx₀ stB.mem :=
    (htour.rep_local tourH cord tx₀ mem stB.mem fun a ha =>
      (hlowB a (C.footR a ha)).symm).1 C.tourRep
  have hphiB : htour.rep.phi tourH tx₀ mem = htour.rep.phi tourH tx₀ stB.mem :=
    (htour.rep_local tourH cord tx₀ mem stB.mem fun a ha => (hlowB a (C.footR a ha)).symm).2
  have hkeysLen : (allKeys eCap tbl S m mem slots).length = 2 * E := allKeys_length C.rep C.act'
  have heC : ∀ s ∈ slots, ∀ e ∈ (slotB S s).edges, e < eCap :=
    fun s hs e he => (C.edge_facts hs he).1
  have hM : ∀ e < eCap, stB.mem (btEdgeSlotBase tbl slotCap + e) =
      mem (btEdgeSlotBase tbl slotCap + e) := fun e he =>
    hlowB _ (C.footT _ (btEdgeSlot_in_foot he))
  have hpairs := brPairsOf_eq_allPairs C.rep C.act' heC hM
  have hpairsLen : (allPairs eCap tbl S m mem slots).length = E := allPairs_length C.rep C.act'
  have H : BrCHyps htour tbl tourH n h slotCap E (h + 6 * n + 10 * E) stB.mem
      (allKeys eCap tbl S m mem slots) (brOwn cs) cord tx₀ := by
    refine ⟨hw, hkeysLen, rfl, hfit, C.tourH_lt, C.eCap_lt, C.keys_ok, fun k hk _ => ?_, ?_,
      C.footR, hkeysB⟩
    · obtain ⟨s, hs, hks⟩ := (mem_allKeys C.rep C.act').mp hk
      have he := (C.edge_facts hs hks).1
      have hfoot := btEdgeSlot_in_foot (m := m) (tbl := tbl) he
      refine ⟨C.footT _ hfoot, C.disj _ hfoot, ?_⟩
      obtain ⟨hsc, B, hB, -⟩ := C.act s hs
      rw [hM _ he, edgeSlot_of_mem C.rep hsc hB (slotB_eq hsc hB ▸ hks) he]
      omega
    · have := congrArg List.length hpairs
      unfold brPairsOf at this
      rw [List.length_map] at this
      omega
  obtain ⟨stC, cC, txC, hrC, hRC, hLC, h19lo, h19hi, hzC, hownC, hpairsC, hrepC, hfootC, hlowC,
      hmidC, hcC⟩ :=
    brPhaseC_runs (ω := ω) htour H hrepB (fun a ha => (hhiB a ha).trans (C.zero a (by omega))) rfl
      hRB hLB (h19B.trans h19A)
  refine ⟨stA, stB, stC, cA, cB, cC, txC, hrA, hrB, hrC, hRC, hLC, h19lo, h19hi, hzC, ?_, ?_,
    hownC, hrepC, hfootC, fun a ha hna => (hlowC a ha hna).trans (hlowB a ha), ?_⟩
  · have hlen : (brSpecs S slots).length = n := by simp [brSpecs, hn]
    have key := readPairs_eq_of (mem := stC.mem) (a := h + 4 * n) (L := brSpecs S slots)
      fun j hj => by
        rw [hlen] at hj
        have hjn : j < slots.length := hj
        obtain ⟨e1, e2⟩ := hspecA j hjn
        have hgd : (brSpecs S slots).getD j (0, 0) =
            (slots[j], 4 * (slotB S slots[j]).edges.card) := by
          rw [List.getD_eq_getElem _ _ (by simp [brSpecs]; omega)]
          simp [brSpecs]
        rw [hgd, hmidC _ (by omega) (by omega) (by omega),
          hmidC _ (by omega) (by omega) (by omega),
          hfrB _ (Or.inl (by omega)), hfrB _ (Or.inl (by omega))]
        exact ⟨e1, e2⟩
    rwa [hlen] at key
  · rw [hpairs] at hpairsC
    have key := readPairs_eq_of hpairsC
    rwa [hpairsLen] at key
  · rw [hphiB]
    omega

end

end MinCostFlow.SparseCore.Program.Restart
