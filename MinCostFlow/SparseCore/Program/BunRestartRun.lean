module

public import MinCostFlow.SparseCore.Program.BunRestartNew
public import MinCostFlow.SparseCore.Program.BunRestartPhaseE
import MinCostFlow.SparseCore.Program.BundleCapHeadroom

/-!
# The restart of the bundles: the whole run (`BunRestartRun`)

`brRun` chains the stages of `bunRestartStmt` (phases A to C, phase D and the sort, the call of
P5's initialization, phase E and the return) and proves every post of `BunRestartAtK` on P5's
representation. The heap space is at most `brSpaceC TS cT slotCap · (m + n + 1)` words when the
tour list query of the tour takes at most `cT · (len + 1)` words. The cost is at most
`brMul TS · (m + n + 1) · ordStoreLog eCap`, paid with the potentials of the table and the tour.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The space constant of the restart. -/
def brSpaceC (TS : BundleTourSpec) (cT : ℕ) : ℕ :=
  39 + 2 * TS.querySpace + 4 * cT

/-- The cost constant of the restart. -/
def brMul (TS : BundleTourSpec) : ℕ := 4000 + 6 * TS.mul

end

public section

/-- The arithmetic of the space bound. -/
theorem brSpace_arith {n E M qS cT : ℕ} (hEM : E ≤ M) :
    6 * n + 10 * E + 2 * E * qS + ((3 * n + 24 * E) + cT * (2 * M + 2 * E)) +
      (4 * n + 5 * E) ≤ (39 + 2 * qS + 4 * cT) * (M + n + 1) := by
  have h1 : qS * E ≤ qS * M := Nat.mul_le_mul_left qS hEM
  have h2 : cT * E ≤ cT * M := Nat.mul_le_mul_left cT hEM
  nlinarith [Nat.zero_le (qS * n), Nat.zero_le (cT * n), Nat.zero_le qS, Nat.zero_le cT]

/-- The arithmetic of the cost bound. The table pays `bunPhiMul` per bundle of a listed slot
before the restart, which pays for the walk of these bundles (`60 nB`), and receives at most
`bunPhiMul · 2 E` for the new bundles. -/
theorem brCost_arith {n E M L lg Mu R Q cA cB cC cD cS cI cE φ0 φC φS φI φE sS sT nB nB' X : ℕ}
    (hEM : E ≤ M) (hL : 1 ≤ L) (hlg : lg + 1 ≤ 2 * L) (hR : R ≤ 2 * E) (hQ : Q ≤ 2 * M)
    (h1 : cA + cB + cC + φC ≤ (60 * n + 120) + (60 * E + 60 * nB + 50 * n + 10) +
      (2 * E * (Mu * L + 140) + 20) + φ0)
    (h2 : φS = φC) (h3 : cD ≤ 30 * E + 30 * n + 20)
    (h4 : cS ≤ 400 * E * (lg + 1) + 90 * E + 100)
    (h5 : cI + φI ≤ (125 * n + 70 * E + 50 * R + (Mu * L + 220) * (Q + R) + 180) + 10 + φS)
    (h6 : cE ≤ X + 80 * n + 10) (h7 : X ≤ 100 * n + 200 * E) (h8 : φE = φI)
    (h9 : sT + nB = sS + nB') (h10 : nB' ≤ 2 * E) :
    cA + (cB + (cC + (cD + (cS + (cI + (cE + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1 +
        bunPhiMul * sT + φE ≤
      (4000 + 6 * Mu) * (M + n + 1) * L + bunPhiMul * sS + φ0 := by
  unfold bunPhiMul
  have e1 : E * (lg + 1) ≤ E * (2 * L) := Nat.mul_le_mul_left E hlg
  have e2 : E * L ≤ M * L := Nat.mul_le_mul_right L hEM
  have e3 : Mu * (E * L) ≤ Mu * (M * L) := Nat.mul_le_mul_left Mu e2
  have e4 : (Mu * L) * (Q + R) ≤ (Mu * L) * (4 * M) := Nat.mul_le_mul_left (Mu * L) (by omega)
  have e5 : M ≤ M * L := Nat.le_mul_of_pos_right M hL
  have e6 : n ≤ n * L := Nat.le_mul_of_pos_right n hL
  nlinarith [Nat.zero_le (Mu * n * L), Nat.zero_le (Mu * L), Nat.zero_le (Mu * M * L)]

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}
  {htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner}
  {slotCap tbl tourH slotsPtr h : ℕ} {slots : List ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {cord : ℕ → List End} {tx₀ : htour.rep.τ}
  {cs : CompLSFState} {ord : ℕ → List End} {mem : ℕ → ℕ}

/-- **A listed slot of the new table agrees with `initBundleFor`.** The list `rList` holds the
owners of the keys of the listed slots, so it holds every vertex whose tour list has an end of an
edge of the slot (`tableAfterInitSlots_bunAgree`). -/
theorem brNew_bunAgree
    (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem) {k : ℕ}
    (hk : 1 ≤ k) {rList : List ℕ} (hlt : rList.Pairwise (· < ·))
    (hmemR : ∀ v, v ∈ rList ↔ v ∈ (allKeys eCap tbl S m mem slots).map (brOwn cs))
    {s : ℕ} (hs : s ∈ slots) (hsc : s < slotCap) :
    ∃ B', brNewTable eCap tbl S m mem slots cord rList k ⟨s, hsc⟩ = some B' ∧
      BunAgree B' (initBundleFor cs ord (slotB S s).edges k) := by
  have hE := slotEdgesOf_allPairs (eCap := eCap) (tbl := tbl) (m := m) (mem := mem) C.rep
    C.act' hs
  have key := tableAfterInitSlots_bunAgree (S₀ := clearS S slots) (specs := brSpecs S slots)
    (assigns := allPairs eCap tbl S m mem slots) (rList := rList) (j := ⟨s, hsc⟩) hk C.core
    (by rw [brSpecs_fst]; exact hs) (by rw [hE]; exact fun e he => (C.edge_facts hs he).2) hlt
    (fun v hv => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ((hmemR v).mp hv)
      exact (coreCord_facts C.core).2.2.1 _ _ (C.keys_ok k' hk').2.2.1)
    (fun v x hx hxE => by
      rw [hE] at hxE
      have hkey : endKey x / 2 = x.1 := by unfold endKey; split_ifs <;> omega
      have hk' : endKey x ∈ allKeys eCap tbl S m mem slots :=
        (mem_allKeys C.rep C.act').mpr ⟨s, hs, by rw [hkey]; exact hxE⟩
      have hv := (C.keys_ok _ hk').2.2.2 v (by rw [bundle_endOfKey_endKey]; exact hx)
      rw [hmemR v, hv]
      exact List.mem_map_of_mem hk')
  rw [hE] at key
  exact key

/-- **The run of the restart.** From the setting `C`, the restart ends with the new table
`T'` in blocks `M'`, the tour holding `cord`, P5's invariant, the unlisted slots kept, the new
listed slots agreeing with `initBundleFor` and exported at `h + 4 i`, and the heap pointer `v`
returned. The space and the cost are bounded as in `BunRestartAtK`. -/
theorem brRun (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {k bWalk bSort bInit bDllPush bExport cT : ℕ}
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hk1 : 1 ≤ k) (hk_mem : mem (btBunCapAddr tbl slotCap eCap) = k)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hfit : h + brSpaceC TS cT * (cs.G.m + slots.length + 1) < 2 ^ w) (pos : ℕ) :
    ∃ v st' c T' M' tx', Runs w p ω (bunRestartStmt bWalk bOwner bSort bInit bExport)
        (startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) (.returned v) st' c ∧
      BundleTableRepAt slotCap vCap eCap tbl T' M' st'.mem ∧
      st'.mem (btBunCapAddr tbl slotCap eCap) = k ∧
      (bunTableHeadroomInv S m → bunTableHeadroomInv T' M') ∧
      htour.rep.rep tourH cord tx' st'.mem ∧ bunRestartInv vCap eCap T' cord ∧
      (∀ j : Fin slotCap, j.1 ∉ slots → T' j = S j) ∧
      (∀ i (hi : i < slots.length), ∃ (hs : slots[i] < slotCap) (B B' : BundleState),
        S ⟨slots[i], hs⟩ = some B ∧ T' ⟨slots[i], hs⟩ = some B' ∧
        BunAgree B' (initBundleFor cs ord B.edges k) ∧
        ExportAt st'.mem (h + 4 * i) v B'.graph) ∧
      h + 4 * slots.length ≤ v ∧
      v ≤ h + brSpaceC TS cT * (cs.G.m + slots.length + 1) ∧
      ZeroFrom st'.mem v ∧
      (∀ a < h, ¬ bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx₀ a →
        st'.mem a = mem a) ∧
      (∀ a, bundleTableFoot eCap tbl M' a → bundleTableFoot eCap tbl m a ∨ (h ≤ a ∧ a < v)) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h ≤ a ∧ a < v)) ∧
      (∀ a, bundleTableFoot eCap tbl M' a → ¬ htour.rep.foot tourH tx' a) ∧
      c + bunPhiMul * ∑ j, bunSlotNB T' j + htour.rep.phi tourH tx' st'.mem ≤
        brMul TS * (cs.G.m + slots.length + 1) * ordStoreLog eCap +
          bunPhiMul * ∑ j, bunSlotNB S j + htour.rep.phi tourH tx₀ mem := by
  have hw := C.hw
  have hEM : edgeTot S slots ≤ cs.G.m := C.edgeTot_le_m
  have hEe : edgeTot S slots ≤ eCap := C.edgeTot_le_eCap
  have hcf := coreCord_facts C.core
  have hK : 6 * slots.length + 10 * edgeTot S slots + 2 * edgeTot S slots * TS.querySpace +
      ((3 * slots.length + 24 * edgeTot S slots) +
        cT * (2 * cs.G.m + 2 * edgeTot S slots)) + (4 * slots.length + 5 * edgeTot S slots) ≤
      brSpaceC TS cT * (cs.G.m + slots.length + 1) := by
    unfold brSpaceC; exact brSpace_arith hEM
  -- Phases A to C.
  obtain ⟨stA, stB, stC, cA, cB, cC, txC, hrA, hrB, hrC, hRC, hLC, h19lo, h19hi, hzC, hspecsC,
      hpairsC, hownC, hrepC, hfootC, hlowC, hc1⟩ :=
    brStage1_runs (ω := ω) (st := startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) C
      hpWalk (by omega) rfl rfl rfl rfl rfl rfl
  -- Phase D and the sort.
  obtain ⟨stD, stS, cD, cS, rList, hrD, hrS, hRS, hLS', h19S, h26, hltR, hmemR, hlenR, hlistR,
      htabS, hrepS, hphiS, hspecsS, hpairsS, hzS, hlowS, hkS, hcD, hcS⟩ :=
    brStage2_runs (ω := ω) C hpSort (by omega) hRC hLC h19lo hzC hspecsC hpairsC hownC hrepC
      hfootC hlowC
  have hrnd : rList.Nodup := hltR.imp fun h' => Nat.ne_of_lt h'
  have hQ : (rList.map fun v => (cord v).length).sum ≤ 2 * cs.G.m := hcf.2.2.2 rList hrnd
  have hsbs : slotBlocksSpace (brSpecs S slots) =
      3 * slots.length + 24 * edgeTot S slots := by
    have h1 := brSum_affine slots 3 24 (fun s => (slotB S s).edges.card)
    unfold edgeTot
    rw [← h1]
    unfold slotBlocksSpace brSpecs bundleSlotBlockSize
    simp only [List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left fun s _ => by omega
  have hls : (rList.map fun v => TS.listSpace (cord v).length).sum ≤
      cT * (2 * cs.G.m + 2 * edgeTot S slots) := by
    refine (brSum_le (g := fun v => cT * ((cord v).length + 1)) fun v _ => hLS _).trans ?_
    rw [brSum_mul_succ]
    exact Nat.mul_le_mul_left cT (by omega)
  have hinitSp : bundleInitSlotsSpace TS (brSpecs S slots) cord rList ≤
      (3 * slots.length + 24 * edgeTot S slots) +
        cT * (2 * cs.G.m + 2 * edgeTot S slots) := by
    unfold bundleInitSlotsSpace; omega
  -- The call of P5's initialization.
  obtain ⟨stI, cI, hEnd, tx', hrI, hregI, htabI, hkI, hcmI, hrepI, hEndlo, hEndhi, hzI, hftabI,
      hftourI, hfrI, hcI⟩ :=
    brStage3_runs (ω := ω) (k := k) C hpInit hbPush hk1 (hkS.trans hk_mem) hRS hLS' h26 (by omega)
      (by omega) hltR hmemR hlenR hlistR htabS hrepS
      (fun a ha => by rw [h19S]; exact hfootC a ha) hspecsS hpairsS hzS
  -- Where the footprints lie.
  have hnotTab : ∀ a, h ≤ a → ¬ bundleTableFoot eCap tbl (clearM m slots) a := fun a ha hf => by
    have := C.footT a (clearM_foot hf); omega
  have hnotTour : ∀ a, h ≤ a → a < h + 6 * slots.length + 10 * edgeTot S slots →
      ¬ htour.rep.foot tourH txC a := fun a h1 h2 hf => by
    rcases hfootC a hf with h' | h'
    · have := C.footR a h'; omega
    · omega
  have htabLoc : ∀ a, bundleTableFoot eCap tbl
      (allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) (stS.regs 19)) a →
      (a < h ∧ bundleTableFoot eCap tbl m a) ∨
        (stS.regs 19 ≤ a ∧ a < stS.regs 19 + slotBlocksSpace (brSpecs S slots)) := by
    intro a ha
    rcases hftabI a ha with h1 | h1
    · have := clearM_foot h1; exact Or.inl ⟨C.footT a this, this⟩
    · exact Or.inr h1
  have htourLoc : ∀ a, htour.rep.foot tourH tx' a → (a < h ∧ htour.rep.foot tourH tx₀ a) ∨
      (h + 6 * slots.length + 10 * edgeTot S slots ≤ a ∧ a < stS.regs 19) ∨
      (stS.regs 19 + slotBlocksSpace (brSpecs S slots) ≤ a ∧ a < hEnd) := by
    intro a ha
    rcases hftourI a ha with h1 | h1
    · rcases hfootC a h1 with h2 | h2
      · exact Or.inl ⟨C.footR a h2, h2⟩
      · exact Or.inr (Or.inl (by rw [h19S]; exact h2))
    · exact Or.inr (Or.inr h1)
  -- The new slots.
  have hslotB : ∀ s ∈ slots, slotB (brNewTable eCap tbl S m mem slots cord rList k) s =
      brNewB S cord rList k s := fun s hs => slotB_brNewTable C.rep C.act' hs
  have hspE : (slots.map fun s =>
      bundleExportSpace (slotB (brNewTable eCap tbl S m mem slots cord rList k) s)).sum ≤
      4 * slots.length + 5 * edgeTot S slots := by
    rw [List.map_congr_left fun s hs => by rw [hslotB s hs]]
    exact brNew_space_sum hk1 hrnd hcf.1 C.inv.1.1
  have hcoE : (slots.map fun s =>
      bundleExportCost (slotB (brNewTable eCap tbl S m mem slots cord rList k) s)).sum ≤
      100 * slots.length + 200 * edgeTot S slots := by
    rw [List.map_congr_left fun s hs => by rw [hslotB s hs]]
    exact brNew_cost_sum hk1 hrnd hcf.1 C.inv.1.1
  -- Phase E.
  have hRI : BRRegs stI.regs tbl tourH slots.length slotsPtr h slotCap eCap := by
    rw [hregI]; exact hRS.upd (by omega)
  have h19I : stI.regs 19 = hEnd := by rw [hregI]; simp
  obtain ⟨stE, cE, hrE, h19E, hzE, htabE, hexE, hfrE, hcE⟩ := brPhaseE_runs (ω := ω) hpExport
    hw hRI h19I (fun s hs => ⟨(C.act' s hs).1, _, brNewTable_listed C.rep C.act' hs _⟩)
    (fun i hi => by
      have e := (readPairs_getD hspecsS hi).1
      rw [hfrI _ (by omega) (hnotTab _ (by omega)) (hnotTour _ (by omega) (by omega)), e,
        List.getD_eq_getElem _ _ (by simp [brSpecs]; omega), List.getD_eq_getElem _ _ hi]
      simp [brSpecs])
    htabI
    (fun a ha => by rcases htabLoc a ha with h1 | h1 <;> omega)
    hzI (by omega) (by omega) (by have := C.tbl_le; omega)
  have hret : Runs w p ω (.ret (.reg 19)) stE (.returned (stE.regs 19)) stE 2 :=
    runs_ret_iff.mpr ⟨_, Expr.eval_reg_of_eq rfl, rfl, rfl, by simp [Expr.size]⟩
  have hlocE := htour.rep_local tourH cord tx' stI.mem stE.mem fun a ha => by
    refine (hfrE a ?_ ?_).symm <;> rcases htourLoc a ha with h1 | h1 | h1 <;> omega
  have hkE : stE.mem (btBunCapAddr tbl slotCap eCap) = k := by
    have hbc_lt := C.footT _ (btBunCap_in_foot (tbl := tbl) (slotCap := slotCap) (eCap := eCap) (m := m))
    rw [hfrE (btBunCapAddr tbl slotCap eCap) (by omega) (by omega)]
    exact hkI
  have hheadroom : bunTableHeadroomInv S m →
      bunTableHeadroomInv (brNewTable eCap tbl S m mem slots cord rList k)
        (allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) (stS.regs 19)) := by
    intro hH₀
    have hHclear : bunTableHeadroomInv (clearS S slots) (clearM m slots) := by
      intro j B p bunCap hSj hmj
      obtain ⟨hnot, hSj₀⟩ := clearS_some hSj
      unfold clearM at hmj
      simp only [hnot, ↓reduceIte] at hmj
      exact hH₀ j B p bunCap hSj₀ hmj
    have hcover : ∀ es ∈ allPairs eCap tbl S m mem slots, ∀ side : Bool,
        ∃ v ∈ rList, (es.1, side) ∈ cord v := by
      intro es hes side
      obtain ⟨hs, he⟩ := (mem_allPairs C.rep C.act').mp hes
      have hkey : endKey (es.1, side) / 2 = es.1 := by unfold endKey; split_ifs <;> omega
      have hk' : endKey (es.1, side) ∈ allKeys eCap tbl S m mem slots :=
        (mem_allKeys C.rep C.act').mpr ⟨es.2, hs, by rw [hkey]; exact he⟩
      refine ⟨brOwn cs (endKey (es.1, side)), (hmemR _).mpr (List.mem_map_of_mem hk'), ?_⟩
      have := (C.keys_ok _ hk').2.2.1
      rwa [bundle_endOfKey_endKey] at this
    refine bunTableHeadroomInv_initSlots hHclear hk1 (by rw [brSpecs_fst]; exact C.nd) hrnd
      (fun v _ => hcf.1 v) C.inv.1.1 hcover ?_
    intro sb hsb
    simp only [brSpecs, List.mem_map] at hsb
    obtain ⟨s, hs, rfl⟩ := hsb
    rw [slotEdgesOf_allPairs C.rep C.act' hs]
  refine ⟨stE.regs 19, stE, _, brNewTable eCap tbl S m mem slots cord rList k,
    allocSlotBlocksMeta (clearM m slots) (brSpecs S slots) (stS.regs 19), tx',
    runs_seq_normal hrA (runs_seq_normal hrB (runs_seq_normal hrC (runs_seq_normal hrD
      (runs_seq_normal hrS (runs_seq_normal hrI (runs_seq_normal hrE hret)))))),
    htabE, hkE, hheadroom, hlocE.1 hrepI, ⟨hcmI, C.inv.2⟩, fun j hj => brNewTable_unlisted hj, ?_,
    by omega, by omega, hzE, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hsc, B, hB⟩ := C.act' _ (List.getElem_mem hi)
    obtain ⟨B', hB', hag⟩ := brNew_bunAgree C hk1 hltR hmemR (List.getElem_mem hi) hsc
    refine ⟨hsc, B, B', hB, hB', by rwa [slotB_eq hsc hB] at hag, ?_⟩
    have := hexE i hi
    rwa [slotB_eq hsc hB'] at this
  · intro a ha hnf hnt
    rw [hfrE a (by omega) (by omega), hfrI a (by omega) (fun hf => hnf (clearM_foot hf))
      (fun hf => by
        rcases hfootC a hf with h' | h'
        · exact hnt h'
        · omega)]
    exact hlowS a ha hnf hnt
  · intro a ha
    rcases htabLoc a ha with h1 | h1
    · exact Or.inl h1.2
    · exact Or.inr (by omega)
  · intro a ha
    rcases htourLoc a ha with h1 | h1 | h1
    · exact Or.inl h1.2
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  · intro a ha hb
    rcases htabLoc a ha with h1 | h1 <;> rcases htourLoc a hb with h2 | h2 | h2
    · exact C.disj a h1.2 h2.2
    all_goals omega
  · -- The cost.
    have hinitC : bundleInitSlotsCost TS eCap slots.length (edgeTot S slots) cord rList =
        125 * slots.length + 70 * edgeTot S slots + 50 * rList.length +
          (TS.mul * ordStoreLog eCap + 220) * ((rList.map fun v => (cord v).length).sum + rList.length) + 180 := by
      unfold bundleInitSlotsCost
      rw [brSum_mul_succ]
    have hlt : ∀ s ∈ slots, s < slotCap := fun s hs => (C.act' s hs).1
    have h9 := bunSlotNB_restart C.nd hlt
      (T := brNewTable eCap tbl S m mem slots cord rList k) fun j hj => brNewTable_unlisted hj
    have hnbS : (slots.map (slotNB S)).sum =
        (slots.map fun s => (slotB S s).vertices.card).sum := by
      congr 1
      refine List.map_congr_left fun s hs => ?_
      obtain ⟨hsc, B, hB⟩ := C.act' s hs
      exact slotNB_eq_slotB hsc hB
    have hnbT : (slots.map (slotNB (brNewTable eCap tbl S m mem slots cord rList k))).sum ≤
        2 * edgeTot S slots := by
      refine le_trans (le_of_eq ?_) (brNew_nb_sum hk1 hrnd hcf.1 C.inv.1.1)
      congr 1
      refine List.map_congr_left fun s hs => ?_
      have hsc := (C.act' s hs).1
      rw [slotNB_eq_slotB hsc (brNewTable_listed C.rep C.act' hs hsc), hslotB s hs]
    rw [hnbS] at h9
    unfold brMul
    exact brCost_arith hEM (ordStoreLog_one_le eCap) (log_sort_le hEe) hlenR hQ hc1 hphiS hcD
      hcS (hcI.trans (by rw [hinitC])) hcE hcoE hlocE.2.symm h9 hnbT

end

end MinCostFlow.SparseCore.Program.Restart
