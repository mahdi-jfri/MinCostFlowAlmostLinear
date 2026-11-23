module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotRun
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the model (`AssemblyFirstInitSlotModel`)

`slotList_runs` speaks of words: the component word of the tail of an edge, the bucket word of an
edge, and the forest edges of P4's export. This file reads its result `SlotListOut` in the model of
the bundle side.

The inputs are tied to the model as follows. The words at `cmpH` are the indices of the components
in a list `comps` of the components of `G` (as `compMap_runs` writes them). The words at `bktH` are
the bucket codes of the edges (as `bucketTable_runs` writes them). The forest edges of the export
are the edges of the forest `Fe`. Then:
* the component word of an edge is `tailComp comps G e` (`slotCOf_eq`);
* the count of component `c` is the number of edges of its graph (`slotCnt_eq`), so the flag of `c`
  is on exactly for the large components (`slotListOut_flag`);
* an edge is selected exactly when it is a core edge with its tail in a large component, and its key
  is the key of its pair, so `D` has the members of `slotKeys` (`slotListOut_mem_D`);
* the slot map `slotOfD` is good (`slotListOut_slotMapOK`), and the list of each component at its
  address is `cslList D B c` (`slotListOut_csl`), which holds the active pairs of the component with
  their slots (`mem_cslList_iff`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.Bundle
open MinCostFlow.DynSpanner MinCostFlow.SparseCore.Program.Restart WordRAM

variable {depth : ℕ} {tr : BundleTreeState depth} {comps : List (Finset ℕ)} {G : MGraph}
  {Fe : Finset ℕ} {k B : ℕ} {eL : List ℕ} {mem : ℕ → ℕ} {cmpH : ℕ}

/-- The index of the component of a vertex `v` of `G` in `comps`. -/
theorem comps_idxOf_compOf (H : SlotKeyHyps tr comps G Fe k B eL) {v : ℕ} (hv : v ∈ G.V) :
    comps.idxOf (compOf G v) < comps.length ∧ comps[comps.idxOf (compOf G v)]? = some (compOf G v) := by
  have hm : compOf G v ∈ comps := (H.comps_iff _).mpr (compOf_mem_components hv)
  exact ⟨List.idxOf_lt_length_of_mem hm, List.getElem?_idxOf hm⟩

/-- **The component word of an edge** is the index of the component of its tail. -/
theorem slotCOf_eq (H : SlotKeyHyps tr comps G Fe k B eL)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    {e : ℕ} (he : e ∈ G.E) : slotCOf mem cmpH G e = tailComp comps G e := by
  have htV : G.tail e ∈ G.V := (H.valid e he).1
  have hm : compOf G (G.tail e) ∈ comps := (H.comps_iff _).mpr (compOf_mem_components htV)
  have hlt := List.idxOf_lt_length_of_mem hm
  have hget : comps[comps.idxOf (compOf G (G.tail e))] = compOf G (G.tail e) :=
    List.getElem_idxOf hlt
  unfold slotCOf tailComp
  exact hcmp _ hlt _ (by rw [hget]; exact self_mem_compOf htV)

/-- An edge of `G` has its tail in the component `comps[c]` exactly when its component index is
`c`. -/
theorem tailComp_eq_iff (H : SlotKeyHyps tr comps G Fe k B eL) {e : ℕ} (he : e ∈ G.E) {c : ℕ}
    (hc : c < comps.length) : tailComp comps G e = c ↔ G.tail e ∈ comps[c] := by
  have htV : G.tail e ∈ G.V := (H.valid e he).1
  have hm : compOf G (G.tail e) ∈ comps := (H.comps_iff _).mpr (compOf_mem_components htV)
  have hcC : comps[c] ∈ components G := (H.comps_iff _).mp (List.getElem_mem hc)
  unfold tailComp
  constructor
  · intro h
    have hget : comps[comps.idxOf (compOf G (G.tail e))] = compOf G (G.tail e) :=
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
    simp only [h] at hget
    rw [hget]
    exact self_mem_compOf htV
  · intro h
    rw [← comp_eq_compOf hcC h]
    exact List.Nodup.idxOf_getElem H.nodup c hc

/-- **The count of a component** is the number of edges of its graph. -/
theorem slotCnt_eq (H : SlotKeyHyps tr comps G Fe k B eL)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    {c : ℕ} (hc : c < comps.length) :
    slotCnt G (slotCOf mem cmpH G) c = (compGraph G comps[c]).m := by
  classical
  unfold slotCnt MGraph.m compGraph compEdgeSet
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, h⟩
    rw [slotCOf_eq H hcmp he] at h
    exact ⟨he, (tailComp_eq_iff H he hc).mp h⟩
  · rintro ⟨he, h⟩
    rw [slotCOf_eq H hcmp he]
    exact ⟨he, (tailComp_eq_iff H he hc).mpr h⟩

/-- The flag of component `c` is on exactly when `comps[c]` is a large component. -/
theorem slotFlagOn_iff (H : SlotKeyHyps tr comps G Fe k B eL)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    {c : ℕ} (hc : c < comps.length) :
    SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) c) ↔ comps[c] ∈ largeComps k G := by
  classical
  rw [slotCnt_eq H hcmp hc]
  unfold largeComps
  rw [Finset.mem_filter]
  have hcC : comps[c] ∈ components G := (H.comps_iff _).mp (List.getElem_mem hc)
  exact ⟨fun h => ⟨hcC, h⟩, fun h => h.2⟩

section Out

variable {mem' : ℕ → ℕ} {fe : List ℕ} {bktH nComp ctH heap eCap : ℕ} {S D : List ℕ}

/-- **The flags** in the table of the components mark the large components. -/
theorem slotListOut_flag (H : SlotKeyHyps tr comps G Fe k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hn : nComp = comps.length)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (c : ℕ) (hc : c < comps.length) :
    mem' (ctH + 3 * c) = if comps[c] ∈ largeComps k G then 1 else 0 := by
  rw [hO.flag c (hn ▸ hc)]
  by_cases h : comps[c] ∈ largeComps k G
  · rw [ite_eq_left ((slotFlagOn_iff H hcmp hc).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((slotFlagOn_iff H hcmp hc).mp h')), ite_eq_right h]

/-- An edge is selected exactly when it is a core edge with its tail in a large component. -/
theorem slotSel_iff (H : SlotKeyHyps tr comps G Fe k B eL)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ Fe) {e : ℕ} (he : e ∈ G.E) :
    slotSel mem cmpH G fe k e = true ↔ SlotCoreAct G Fe k e := by
  have htV : G.tail e ∈ G.V := (H.valid e he).1
  have hm : compOf G (G.tail e) ∈ comps := (H.comps_iff _).mpr (compOf_mem_components htV)
  have hlt := List.idxOf_lt_length_of_mem hm
  have hget : comps[comps.idxOf (compOf G (G.tail e))] = compOf G (G.tail e) :=
    List.getElem_idxOf hlt
  have hfl := slotFlagOn_iff H hcmp hlt
  rw [hget] at hfl
  unfold slotSel SlotCoreAct
  rw [decide_eq_true_iff, slotCOf_eq H hcmp he]
  unfold tailComp
  rw [hfl, hfe e he]

/-- **The members of `D`** are the keys of the active pairs (`slotKeys`). -/
theorem slotListOut_mem_D (H : SlotKeyHyps tr comps G Fe k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hbk : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (tr.origBucket e))
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ Fe) (x : ℕ) :
    x ∈ D ↔ x ∈ slotKeys comps G Fe k B tr.origBucket eL := by
  classical
  rw [hO.D_mem]
  unfold slotKeys
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, heS, rfl⟩
    obtain ⟨he, hsel⟩ := (hO.S_mem e).mp heS
    refine ⟨e, ⟨(H.eL_iff e).mpr he, (slotSel_iff H hcmp hfe he).mp hsel⟩, ?_⟩
    unfold slotKeyOf
    rw [slotCOf_eq H hcmp he, hbk e he]
  · rintro ⟨e, ⟨heL, hact⟩, rfl⟩
    have he := (H.eL_iff e).mp heL
    refine ⟨e, (hO.S_mem e).mpr ⟨he, (slotSel_iff H hcmp hfe he).mpr hact⟩, ?_⟩
    unfold slotKeyOf
    rw [slotCOf_eq H hcmp he, hbk e he]

/-- **The slot map** `slotOfD` of the result is good, with slots `0, …, |D| - 1`. -/
theorem slotListOut_slotMapOK (H : SlotKeyHyps tr comps G Fe k B eL)
    (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    (hcmp : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem (cmpH + v) = c)
    (hbk : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (tr.origBucket e))
    (hfe : ∀ e ∈ G.E, e ∈ fe ↔ e ∈ Fe) {slotCap cap : ℕ} (hcap : D.length ≤ slotCap)
    (hcap' : D.length ≤ cap) :
    SlotMapOK tr slotCap cap (List.range D.length) (slotOfD comps B D) :=
  slotMapOK_slotOfD H (hO.D_sorted.imp fun h => Nat.ne_of_lt h)
    (slotListOut_mem_D H hO hcmp hbk hfe) hcap hcap'

/-- **The list of each component** at its address: its length is in the table, and its `i`-th
pair is the `i`-th member of `cslList D B c`, as a bucket code and a slot. -/
theorem slotListOut_csl (hO : SlotListOut mem mem' G fe cmpH bktH nComp k B ctH heap eCap S D)
    {c : ℕ} (hc : c < nComp) :
    mem' (ctH + 3 * c + 2) = (cslList D B c).length ∧
      ∀ i (hi : i < (cslList D B c).length),
        mem' (mem' (ctH + 3 * c + 1) + 2 * i) = bucketCode (cslList D B c)[i].1 ∧
        mem' (mem' (ctH + 3 * c + 1) + 2 * i + 1) = (cslList D B c)[i].2 := by
  refine ⟨by rw [hO.len c hc, cslList_length], fun i hi => ?_⟩
  have hlen := cslList_length D B c
  have hpos : 0 < slotSegLen D B c := by omega
  have hle := slotSeg_le D B c
  have hj : slotSegStart D B c + i < D.length := by omega
  rw [hO.ptr c hc, ite_eq_left hpos, cslList_getElem hO.D_sorted B c i hi]
  have hgj : D.getD (slotSegStart D B c + i) 0 = D[slotSegStart D B c + i] := by
    simp [List.getElem?_eq_getElem hj]
  obtain ⟨h1, h2⟩ := hO.pairs _ hj
  refine ⟨?_, ?_⟩
  · rw [bucketCode_bucketDecode, hgj, ← h1]
    congr 1
    ring
  · rw [← h2]
    congr 1
    ring

end Out

end MinCostFlow.SparseCore.Program
