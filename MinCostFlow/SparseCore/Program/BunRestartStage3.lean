module

public import MinCostFlow.SparseCore.Program.BunRestartStage2

/-!
# The restart of the bundles: the call of P5's initialization (`BunRestartStage3`)

`brStage3_runs` calls P5's initialization of slots (`bundleInitSlots_runs`) on the cleared table,
the specs `brSpecs`, the pairs `allPairs` and `rList`, and discharges its hypotheses from the
state after the sort. The new table is `brNewTable`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The table after the restart: P5's initialization of the listed slots of the cleared table. -/
noncomputable def brNewTable {slotCap : ℕ} (eCap tbl : ℕ) (S : Fin slotCap → Option BundleState)
    (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) (slots : List ℕ) (cord : ℕ → List End)
    (rList : List ℕ) (k : ℕ) : Fin slotCap → Option BundleState :=
  tableAfterInitSlots (clearS S slots) (brSpecs S slots) (allPairs eCap tbl S m mem slots) cord
    rList k

end

public section

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}
  {htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner}
  {slotCap tbl tourH slotsPtr h : ℕ} {slots : List ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {cord : ℕ → List End} {tx₀ : htour.rep.τ}
  {cs : CompLSFState} {ord : ℕ → List End} {mem : ℕ → ℕ}

/-- The fixed part of the table lies below `h`. -/
theorem BRCtx.tbl_le (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) :
    tbl + bundleTableFixedSize slotCap eCap ≤ h := by
  have := C.footT (tbl + (bundleTableFixedSize slotCap eCap - 1))
    (Or.inl ⟨Nat.le_add_right _ _, by unfold bundleTableFixedSize; omega⟩)
  unfold bundleTableFixedSize at *
  omega

/-- The blocks of the table lie below `h`. -/
theorem BRCtx.block_le (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {j : Fin slotCap} {q c : ℕ} (hm : m.slotBlocks j = some (q, c)) :
    q + bundleSlotBlockSize c ≤ h := by
  have := C.footT (q + (bundleSlotBlockSize c - 1))
    (Or.inr ⟨j, q, c, hm, Nat.le_add_right _ _, by unfold bundleSlotBlockSize; omega⟩)
  unfold bundleSlotBlockSize at *
  omega

/-- **The call of P5's initialization.** From the state after the sort, with the heap pointer `hc`
in register `19`, the call ends with the new table `brNewTable` in the blocks
`allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) hc`, the tour holding `cord` in a new
concrete state, and the new heap pointer `hEnd` in register `19`. It keeps the memory below `hc`
outside the footprints of the cleared table and of the tour. -/
theorem brStage3_runs (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {k bInit bDllPush : ℕ}
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ prevBase nextBase headAddr key L,
      MeetsContract w p bDllPush
        (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hk1 : 1 ≤ k)
    {stS : State} {txC : htour.rep.τ} {rList : List ℕ}
    (hk_mem : stS.mem (btBunCapAddr tbl slotCap eCap) = k)
    (hR : BRRegs stS.regs tbl tourH slots.length slotsPtr h slotCap eCap)
    (hL : BRRegsL stS.regs h slots.length (edgeTot S slots))
    (h26 : stS.regs 26 = rList.length)
    (h19 : h + 6 * slots.length + 10 * edgeTot S slots ≤ stS.regs 19)
    (hfit : stS.regs 19 + bundleInitSlotsSpace TS (brSpecs S slots) cord rList < 2 ^ w)
    (hlt : rList.Pairwise (· < ·))
    (hmemR : ∀ v, v ∈ rList ↔ v ∈ (allKeys eCap tbl S m mem slots).map (brOwn cs))
    (hlenR : rList.length ≤ 2 * edgeTot S slots)
    (hlistR : ListAt stS.mem (h + 6 * slots.length + 8 * edgeTot S slots) rList)
    (htab : BundleTableRepAt slotCap vCap eCap tbl (clearS S slots) (clearM m slots) stS.mem)
    (hrepT : htour.rep.rep tourH cord txC stS.mem)
    (hfootT : ∀ a, htour.rep.foot tourH txC a → htour.rep.foot tourH tx₀ a ∨
      (h + 6 * slots.length + 10 * edgeTot S slots ≤ a ∧ a < stS.regs 19))
    (hspecs : bundleReadPairs stS.mem (h + 4 * slots.length) slots.length = brSpecs S slots)
    (hpairs : bundleReadPairs stS.mem (h + 6 * slots.length + 2 * edgeTot S slots) (edgeTot S slots) =
      allPairs eCap tbl S m mem slots)
    (hz : ZeroFrom stS.mem (stS.regs 19)) :
    ∃ stI cI hEnd tx', Runs w p ω (brInitStmt bInit) stS .normal stI cI ∧
      stI.regs = Function.update stS.regs 19 hEnd ∧
      BundleTableRepAt slotCap vCap eCap tbl (brNewTable eCap tbl S m mem slots cord rList k)
        (allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) (stS.regs 19)) stI.mem ∧
      stI.mem (btBunCapAddr tbl slotCap eCap) = k ∧
      BundleTableCordMatch vCap (brNewTable eCap tbl S m mem slots cord rList k) cord ∧
      htour.rep.rep tourH cord tx' stI.mem ∧
      stS.regs 19 + slotBlocksSpace (brSpecs S slots) ≤ hEnd ∧
      hEnd ≤ stS.regs 19 + bundleInitSlotsSpace TS (brSpecs S slots) cord rList ∧
      ZeroFrom stI.mem hEnd ∧
      (∀ a, bundleTableFoot eCap tbl
          (allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) (stS.regs 19)) a →
        bundleTableFoot eCap tbl (clearM m slots) a ∨
          (stS.regs 19 ≤ a ∧ a < stS.regs 19 + slotBlocksSpace (brSpecs S slots))) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH txC a ∨
        (stS.regs 19 + slotBlocksSpace (brSpecs S slots) ≤ a ∧ a < hEnd)) ∧
      (∀ a < stS.regs 19, ¬ bundleTableFoot eCap tbl (clearM m slots) a →
        ¬ htour.rep.foot tourH txC a → stI.mem a = stS.mem a) ∧
      cI + htour.rep.phi tourH tx' stI.mem ≤
        bundleInitSlotsCost TS eCap slots.length (edgeTot S slots) cord rList + 10 +
          htour.rep.phi tourH txC stS.mem := by
  set n := slots.length with hn
  set E := edgeTot S slots with hE
  set hc := stS.regs 19 with hhc
  have hw := C.hw
  have htbl := C.tbl_le
  have hspl : (brSpecs S slots).length = n := by simp [brSpecs, hn]
  have hspf : (brSpecs S slots).map Prod.fst = slots := by
    simp only [brSpecs, List.map_map]
    exact List.map_id'' (fun _ => rfl) slots
  have hPlen : (allPairs eCap tbl S m mem slots).length = E := allPairs_length C.rep C.act'
  have hcf := coreCord_facts C.core
  have hrnd : rList.Nodup := hlt.imp fun h' => Nat.ne_of_lt h'
  have hfit' : hc < 2 ^ w := by unfold bundleInitSlotsSpace at hfit; omega
  -- The footprint of the tour lies apart from the table.
  have htf : ∀ a, htour.rep.foot tourH txC a →
      (a < h ∧ htour.rep.foot tourH tx₀ a) ∨ (h + 6 * n + 10 * E ≤ a ∧ a < hc) := by
    intro a ha
    rcases hfootT a ha with h0 | h0
    · exact Or.inl ⟨C.footR a h0, h0⟩
    · exact Or.inr h0
  have hcover : ∀ es ∈ allPairs eCap tbl S m mem slots, ∀ side : Bool,
      ∃ v ∈ rList, (es.1, side) ∈ cord v := by
    intro es hes side
    obtain ⟨hs, he⟩ := (mem_allPairs C.rep C.act').mp hes
    have hkey : endKey (es.1, side) / 2 = es.1 := by
      unfold endKey; split_ifs <;> omega
    have hk : endKey (es.1, side) ∈ allKeys eCap tbl S m mem slots :=
      (mem_allKeys C.rep C.act').mpr ⟨es.2, hs, by rw [hkey]; exact he⟩
    refine ⟨brOwn cs (endKey (es.1, side)), (hmemR _).mpr (List.mem_map_of_mem hk), ?_⟩
    have := (C.keys_ok _ hk).2.2.1
    rwa [bundle_endOfKey_endKey] at this
  obtain ⟨st', c, hEnd, tx', hrun, hlo, hhi, hzI, hrepI, hkI, hcmI, hrepTI, hfootTab, hfootTour, hfrI,
      hcI⟩ := bundleInitSlots_runs (TS := TS) (w := w) (slotCap := slotCap) (vCap := vCap)
    (eCap := eCap) (tbl := tbl) (tourH := tourH) (k := k) (nSlots := n)
    (slotSpecPtr := h + 4 * n) (nEdges := E) (edgeAssignPtr := h + 6 * n + 2 * E)
    (nR := rList.length) (rPtr := h + 6 * n + 8 * E) (h := hc) (pProg := p)
    (bDllPush := bDllPush) (bTourList := bTourList) (bTourLen := bTourLen)
    (bTourOwner := bOwner) (htour := htour) (S₀ := clearS S slots) (m₀ := clearM m slots)
    (mem₀ := stS.mem) (pos₀ := stS.pos) (tx₀ := txC) (ω := ω) (specs := brSpecs S slots)
    (assigns := allPairs eCap tbl S m mem slots) (cord := cord) (rList := rList)
    hbPush hw hk1 hk_mem C.tourH_lt (by omega) (fun a ha => by
      have := C.footT a (clearM_foot ha); omega) (by omega) (Or.inr (by omega)) (by omega)
    (Or.inr (by omega)) (by omega) (Or.inr (by omega)) hfit htab
    ⟨C.inv.1.1, fun j B hB => C.inv.1.2 j B (clearS_some hB).2⟩ hz hrepT
    (fun a ha => by rcases htf a ha with h0 | h0 <;> omega)
    (fun a ha => by
      rcases htf a ha with ⟨h1, h2⟩ | h0
      · by_contra hc'
        exact C.disj a (Or.inl ⟨by omega, by omega⟩) h2
      · omega)
    (fun a ha j q c hm => by
      have hm' : m.slotBlocks j = some (q, c) := by
        unfold clearM at hm
        by_cases hj : j.1 ∈ slots
        · simp [hj] at hm
        · simpa [hj] using hm
      have := C.block_le hm'
      rcases htf a ha with ⟨h1, h2⟩ | h0
      · by_contra hc'
        exact C.disj a (Or.inr ⟨j, q, c, hm', by omega, by omega⟩) h2
      · omega)
    (fun a ha => by rcases htf a ha with h0 | h0 <;> omega)
    (fun a ha => by rcases htf a ha with h0 | h0 <;> omega)
    hspl hspecs
    (fun sb hsb => by
      simp only [brSpecs, List.mem_map] at hsb
      obtain ⟨s, hs, rfl⟩ := hsb
      exact (C.act' s hs).1)
    (by rw [hspf]; exact C.nd)
    (fun sb hsb hlt' => by
      simp only [brSpecs, List.mem_map] at hsb
      obtain ⟨s, hs, rfl⟩ := hsb
      simp [clearS, hs])
    (fun sb hsb => by
      simp only [brSpecs, List.mem_map] at hsb
      obtain ⟨s, hs, rfl⟩ := hsb
      rw [slotEdgesOf_allPairs C.rep C.act' hs]
      exact (initPrefixSlots_length_le hk1 hrnd (fun v _ => hcf.1 v) C.inv.1.1).trans (by omega))
    hPlen hpairs
    (fun es hes => by
      obtain ⟨hs, he⟩ := (mem_allPairs C.rep C.act').mp hes
      exact ⟨(C.edge_facts hs he).1, by rw [hspf]; exact hs⟩)
    (allPairs_fst_nodup C.rep C.act' C.nd)
    (fun es hes j B hB hin => by
      obtain ⟨hs, he⟩ := (mem_allPairs C.rep C.act').mp hes
      obtain ⟨hjn, hSj⟩ := clearS_some hB
      obtain ⟨hsc, B₂, hB₂⟩ := C.act' es.2 hs
      rw [slotB_eq hsc hB₂] at he
      have hne : j ≠ ⟨es.2, hsc⟩ := fun h' => hjn (h' ▸ hs)
      exact Finset.disjoint_left.mp (edges_disjoint C.rep j.2 hsc
        (fun h' => hne (Fin.ext h')) hSj hB₂) hin he)
    (by have := C.edgeTot_le_eCap; have := C.eCap_lt; omega) rfl hlistR
    (fun v hv => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ((hmemR v).mp hv)
      have h1 := (C.keys_ok k' hk').2.1
      have h2 := C.vCap_le
      exact ⟨h1, by omega⟩)
    hrnd (fun v _ => hcf.1 v) (fun v _ x hx => (C.inv.2 v x hx).2) hcover
  have h0 := hR.r0
  have h1 := hR.r1
  have h2 := hR.r2
  have h8 := hR.r8
  have h9 := hL.r9
  have h14 := hL.r14
  have h17 := hL.r17
  have hargs : evalArgs w stS [.reg 0, .reg 1, .reg 2, .reg 8, .reg 9, .reg 14, .reg 26,
      .reg 17, .reg 19] = some [tbl, tourH, n, h + 4 * n, E, h + 6 * n + 2 * E, rList.length,
      h + 6 * n + 8 * E, hc] := by
    eval_expr
  refine ⟨{ st' with regs := Function.update stS.regs 19 hEnd }, _, hEnd, tx',
    runs_call_iff.mpr ⟨_, _, .returned hEnd, st', c, hargs, hpInit, hrun, rfl, rfl, rfl⟩, rfl,
    hrepI, hkI, hcmI, hrepTI, hlo, hhi, hzI, hfootTab, hfootTour, hfrI, ?_⟩
  simp only [argsSize_cons, argsSize_nil, Expr.size]
  omega

end

end MinCostFlow.SparseCore.Program.Restart
