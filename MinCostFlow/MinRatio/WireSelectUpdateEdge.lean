module

public import MinCostFlow.MinRatio.WireSelectUpdate
import WordRAM.Tactic

/-!
# Verification of `selectProcessEdgeBody` and `selectProcessListBody`

Establishes:
1. `SelectHeapLevelOk` and the exact decomposition `selectHeapMatchesChain_of_levelOk` /
   `selectHeapLevelOk_of_matchesChain`.
2. `selectProcessEdge_meetsContract`: verifies `selectProcessEdgeBody` in
   `selectProcessEdgeCost loc.cap loc.Lk evalCost` steps (`O(evalCost + log(cap+1) · Lk^2)`).
3. `selectProcessList_meetsContract`: verifies `selectProcessListBody` over any edge list `L`
   in `selectProcessListCost L.length loc.cap loc.Lk evalCost` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Per-level semantic invariant `SelectHeapLevelOk` and metadata framing -/

/-- Semantic agreement between the select-heap at `loc` and level `i` of `(C, g, ℓ)`:
an edge `e < loc.cap` is stored in the heap at level `i` iff `e ∈ (C.activeCore i).E \ (C.activeS i).E`,
with key `(readNum, readDen)` representing `(walkInner, wlenAt)` up to a positive common scale
(`SelectKeyRepresents`). -/
def SelectHeapLevelOk (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h _P : ℕ)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (i : ℕ) : Prop :=
  (∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = i →
    e ∈ (C.activeCore i).E \ (C.activeS i).E) ∧
  (∀ e ∈ (C.activeCore i).E \ (C.activeS i).E,
    e < loc.cap ∧ mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = i ∧
    SelectKeyRepresents (loc.readNum mem h e) (loc.readDen mem h e)
      (walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e)) (C.wlenAt ℓ i e))

/-- The value tables and the embedding table of `mloc` end below `hi`: `g` on `G_0`, and at
every level `φ_j`, the core lengths and the embedding pointers. -/
def SelectMetaTablesBelow (mloc : SelectLevelMetaLoc) (hi : ℕ) : Prop :=
  mloc.g0Ptr + mloc.eCap 0 * mloc.Lk ≤ hi ∧
  ∀ j ≤ mloc.d,
    mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ hi ∧
    mloc.coreLenPtr j + mloc.eCap j * mloc.Lk ≤ hi ∧
    mloc.embPtr j + mloc.eCap j ≤ hi

/-- Memory-region bound for `SelectLevelMetaLoc`: metadata tables and dynamic graphs reside
strictly below `hi` and disjoint from `[loc.hb, loc.endAddr)`, and the value tables and the
embedding table end below `hi` (`SelectMetaTablesBelow`). -/
def SelectMetaDisjoint (mloc : SelectLevelMetaLoc) (loc : SelectHeapLoc) (hi : ℕ) : Prop :=
  mloc.Lk = loc.Lk ∧
  mloc.metaBase + selectLevelMetaSize mloc.d ≤ hi ∧
  (mloc.metaBase + selectLevelMetaSize mloc.d ≤ loc.hb ∨ loc.endAddr ≤ mloc.metaBase) ∧
  (∀ j ≤ mloc.d,
    mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
    (mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ loc.hb ∨ loc.endAddr ≤ mloc.GPtr j) ∧
    mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
    (mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ loc.hb ∨ loc.endAddr ≤ mloc.fPtr j) ∧
    (j < mloc.d →
      mloc.sPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
      (mloc.sPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ loc.hb ∨ loc.endAddr ≤ mloc.sPtr j))) ∧
  SelectMetaTablesBelow mloc hi

theorem SelectMetaTablesBelow.mono {mloc : SelectLevelMetaLoc} {hi hi' : ℕ}
    (h : SelectMetaTablesBelow mloc hi) (hle : hi ≤ hi') : SelectMetaTablesBelow mloc hi' :=
  ⟨le_trans h.1 hle, fun j hj =>
    ⟨le_trans (h.2 j hj).1 hle, le_trans (h.2 j hj).2.1 hle, le_trans (h.2 j hj).2.2 hle⟩⟩

/-- Frame condition saying memory outside `[loc.hb, loc.endAddr)` below `scratch` is preserved
and `SelectLevelMetaAt` is preserved across heap updates. -/
def SelectMetaFrame (mem mem' : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (loc : SelectHeapLoc)
    (h P scratch : ℕ) (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ) : Prop :=
  SelectLevelMetaAt mem' mloc h P C g ℓ φ coreLen ∧
  ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem' a = mem a

/-! ## 2. Contracts for `selectProcessEdge` and `selectProcessList` -/

/-- Contract for `selectProcessEdgeBody` (`[hb, metaBase, lvl, e, scratch]`):
updates `e`'s membership/key at level `lvl` of `C`, leaving every `e' ≠ e` and every edge at
another level untouched. -/
def selectProcessEdgeContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl e scratch size,
      args = [loc.hb, mloc.metaBase, lvl, e, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧ e < loc.cap ∧ e < mloc.eCap lvl ∧
      (mem (loc.posPtr + e) = 0 → e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E → size < loc.cap) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectProcessEdgeSpace loc.cap loc.Lk evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 2 0
    let e := args.getD 3 0
    let scratch := args.getD 4 0
    scratch ≤ ret ∧ ret ≤ scratch + selectProcessEdgeSpace loc.cap loc.Lk evalSpace ∧
    (∃ size', SelectHeapAt mem' loc h size') ∧
    SelectMetaFrame mem mem' mloc loc h P scratch C g ℓ φ coreLen ∧
    ZeroFrom mem' ret ∧
    (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
      mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl ∧
      SelectKeyRepresents (loc.readNum mem' h e) (loc.readDen mem' h e)
        (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
    (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
      ¬ (mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl) ∧
      (mem (loc.posPtr + e) = 0 → mem' (loc.posPtr + e) = 0) ∧
      (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) ≠ lvl →
        mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
        loc.readNum mem' h e = loc.readNum mem h e ∧
        loc.readDen mem' h e = loc.readDen mem h e) ∧
      (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = lvl →
        mem' (loc.posPtr + e) = 0)) ∧
    (∀ e' < loc.cap, e' ≠ e →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e')
  cost _ _ := selectProcessEdgeCost loc.cap loc.Lk evalCost

/-- Contract for `selectProcessListBody` (`[hb, metaBase, lvl, listPtr, len, idx, scratch]`):
processes `L.drop idx` at level `lvl`, establishing exact candidate membership/key for every
edge in `L.drop idx` while leaving every edge outside `L.drop idx` untouched. -/
def selectProcessListContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (L : List ℕ) (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl listPtr idx scratch size,
      args = [loc.hb, mloc.metaBase, lvl, listPtr, L.length, idx, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧ idx ≤ L.length ∧
      listPtr + L.length ≤ scratch ∧
      (listPtr + L.length ≤ loc.hb ∨ loc.endAddr ≤ listPtr) ∧
      ListAt mem listPtr L ∧
      (∀ e ∈ L, e < loc.cap ∧ e < mloc.eCap lvl) ∧
      size + (L.length - idx) ≤ loc.cap ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectProcessListSpace (L.length - idx) loc.cap loc.Lk evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 2 0
    let idx := args.getD 5 0
    let scratch := args.getD 6 0
    scratch ≤ ret ∧ ret ≤ scratch + selectProcessListSpace (L.length - idx) loc.cap loc.Lk evalSpace ∧
    (∃ size', SelectHeapAt mem' loc h size' ∧ size' ≤ mem loc.hb + (L.length - idx)) ∧
    SelectMetaFrame mem mem' mloc loc h P scratch C g ℓ φ coreLen ∧
    ZeroFrom mem' ret ∧
    (∀ e ∈ L.drop idx,
      (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
        mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl ∧
        SelectKeyRepresents (loc.readNum mem' h e) (loc.readDen mem' h e)
          (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
      (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
        ¬ (mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl) ∧
        (mem (loc.posPtr + e) = 0 → mem' (loc.posPtr + e) = 0) ∧
        (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) ≠ lvl →
          mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
          loc.readNum mem' h e = loc.readNum mem h e ∧
          loc.readDen mem' h e = loc.readDen mem h e) ∧
        (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = lvl →
          mem' (loc.posPtr + e) = 0))) ∧
    (∀ e' < loc.cap, e' ∉ L.drop idx →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e')
  cost args _ := selectProcessListCost (L.length - args.getD 5 0) loc.cap loc.Lk evalCost

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Equivalence `SelectHeapMatchesChain ↔ ∀ i ≤ C.d, SelectHeapLevelOk` -/

/-- If `SelectHeapAt` holds with `loc.d = C.d` and `SelectHeapLevelOk` holds at every level `0..C.d`,
then `SelectHeapMatchesChain` holds. -/
theorem selectHeapMatchesChain_of_levelOk {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hat : SelectHeapAt mem loc h size)
    (hd : loc.d = C.d)
    (hlvl : ∀ i ≤ C.d, SelectHeapLevelOk mem loc h P C g ℓ i) :
    SelectHeapMatchesChain mem loc h P C g ℓ size := by
  refine ⟨hat, hd, fun e => ⟨?_, ?_⟩, fun e he => ?_⟩
  · rintro ⟨heCap, hnz⟩
    have hi : mem (loc.lvlPtr + e) ≤ C.d := hd ▸ (hat.2.2.1 e heCap hnz).1
    have hmem := (hlvl _ hi).1 e heCap hnz rfl
    have hG0 : e ∈ (C.G 0).E :=
      C.G_E_subset_of_le hH (Nat.zero_le _) hi (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hmem).1).1
    have hNotT : e ∉ C.chainTree.E := by
      intro ht
      simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion,
        Finset.mem_range] at ht
      obtain ⟨j, hj, hje⟩ := ht
      have hjle : j ≤ C.d := Nat.lt_succ_iff.mp hj
      have hCore := (Finset.mem_sdiff.mp hmem).1
      rcases lt_trichotomy j (mem (loc.lvlPtr + e)) with hlt | rfl | hgt
      · have hGj : e ∈ (C.G (j + 1)).E :=
          C.G_E_subset_of_le hH (Nat.succ_le_of_lt hlt) hi (Finset.mem_sdiff.mp hCore).1
        exact (Finset.mem_sdiff.mp (C.G_succ_E_subset hH (by omega) hGj)).2 hje
      · exact (Finset.mem_sdiff.mp hCore).2 hje
      · have hnotS := (Finset.mem_sdiff.mp hmem).2
        have hGj : e ∈ (C.G j).E := ((C.activeLSF_holds hH hjle).2.1.2.2.2.2).2.1 hje
        have hGi1 : e ∈ (C.G (mem (loc.lvlPtr + e) + 1)).E :=
          C.G_E_subset_of_le hH (Nat.succ_le_of_lt hgt) hjle hGj
        rw [← C.activeS_eq_G_succ hH (by omega)] at hGi1
        exact hnotS hGi1
    exact Finset.mem_sdiff.mpr ⟨hG0, hNotT⟩
  · intro he
    obtain ⟨hi, hmem⟩ := C.mem_activeCore_diff_edgeLevel hH he
    obtain ⟨heCap, hnz, _⟩ := (hlvl _ hi).2 e hmem
    exact ⟨heCap, hnz⟩
  · obtain ⟨hi, hmem⟩ := C.mem_activeCore_diff_edgeLevel hH he
    obtain ⟨_, _, hl, hrep⟩ := (hlvl _ hi).2 e hmem
    exact ⟨hl, hrep⟩

/-- Converse: `SelectHeapMatchesChain` implies `SelectHeapLevelOk` at every level `i ≤ C.d`. -/
theorem selectHeapLevelOk_of_matchesChain {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hm : SelectHeapMatchesChain mem loc h P C g ℓ size) {i : ℕ} (hi : i ≤ C.d) :
    SelectHeapLevelOk mem loc h P C g ℓ i := by
  obtain ⟨_, _, hiff, hkey⟩ := hm
  refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
  · have heS : e ∈ (C.G 0).E \ C.chainTree.E := (hiff e).mp ⟨heCap, hnz⟩
    obtain ⟨_, hmem⟩ := C.mem_activeCore_diff_edgeLevel hH heS
    have hEq := (hkey e heS).1
    rw [hl] at hEq
    exact hEq ▸ hmem
  · have heLvl : C.edgeLevel e = i := C.edgeLevel_eq_of_mem hH hi he
    have hG0 : e ∈ (C.G 0).E :=
      C.G_E_subset_of_le hH (Nat.zero_le _) hi (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
    have hNotT : e ∉ C.chainTree.E := by
      intro ht
      simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion,
        Finset.mem_range] at ht
      obtain ⟨j, hj, hje⟩ := ht
      have hjle : j ≤ C.d := Nat.lt_succ_iff.mp hj
      have hCore := (Finset.mem_sdiff.mp he).1
      rcases lt_trichotomy j i with hlt | rfl | hgt
      · have hGj : e ∈ (C.G (j + 1)).E :=
          C.G_E_subset_of_le hH (Nat.succ_le_of_lt hlt) hi (Finset.mem_sdiff.mp hCore).1
        exact (Finset.mem_sdiff.mp (C.G_succ_E_subset hH (by omega) hGj)).2 hje
      · exact (Finset.mem_sdiff.mp hCore).2 hje
      · have hnotS := (Finset.mem_sdiff.mp he).2
        have hGj : e ∈ (C.G j).E := ((C.activeLSF_holds hH hjle).2.1.2.2.2.2).2.1 hje
        have hGi1 : e ∈ (C.G (i + 1)).E := C.G_E_subset_of_le hH (Nat.succ_le_of_lt hgt) hjle hGj
        rw [← C.activeS_eq_G_succ hH (by omega)] at hGi1
        exact hnotS hGi1
    have heS : e ∈ (C.G 0).E \ C.chainTree.E := Finset.mem_sdiff.mpr ⟨hG0, hNotT⟩
    obtain ⟨heCap, hnz⟩ := (hiff e).mpr heS
    obtain ⟨hl, hrep⟩ := hkey e heS
    rw [heLvl] at hl
    refine ⟨heCap, hnz, hl, ?_⟩
    simpa [TreeChain.wlen, heLvl] using hrep

/-! ## 4. Verification of `selectProcessEdgeBody` -/

private lemma selectProcessEdgeSpace_ge_rebal (cap Lk evalSpace : ℕ) :
    heapRebalanceSpace cap Lk ≤ selectProcessEdgeSpace cap Lk evalSpace := by
  unfold selectProcessEdgeSpace; omega

private lemma selectProcessEdgeCost_ge_delIf (cap Lk evalCost : ℕ) :
    heapDeleteIfLevelCost cap Lk + 120 ≤ selectProcessEdgeCost cap Lk evalCost := by
  unfold selectProcessEdgeCost heapUpsertCost heapDeleteIfLevelCost heapDeleteCost; omega

/-- `SelectLevelMetaBounded` holds for every larger bound. -/
theorem SelectLevelMetaBounded.mono {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {C : TreeChain}
    {hi hi' : ℕ} (h : SelectLevelMetaBounded mem mloc C hi) (hle : hi ≤ hi') :
    SelectLevelMetaBounded mem mloc C hi' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨le_trans h1 hle, le_trans h2 hle, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h3 j hj
    exact ⟨le_trans a1 hle, le_trans a2 hle, le_trans a3 hle⟩
  · obtain ⟨a1, a2, a3⟩ := h4 j hj
    refine ⟨a1, le_trans a2 hle, fun e he => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := a3 e he
    exact ⟨b1, b2, le_trans b3 hle, b4⟩

/-- **The data that key evaluation reads lies below `hi`.** The metadata block, the graphs and the
value tables end below `hi` by `SelectMetaDisjoint`. Each walk of the embedding table also ends
below `hi`. Suppose a word of the walk of `e` at level `j` were at an address `a ≥ hi`. Change the
word at `a` and nothing else. The new memory agrees with `mem` below `hi`, so it still satisfies
`SelectLevelMetaAt` by the frame hypothesis `hfr`. Its pointer to the walk of `e` is unchanged,
since the pointer lies below `hi`. So the walk is read at the same address in both memories, and
the two memories must agree at `a`, which they do not. -/
theorem selectLevelMetaBounded_of_frame {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {loc : SelectHeapLoc} {h P hi : ℕ} {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hdisj : SelectMetaDisjoint mloc loc hi)
    (hm : SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen)
    (hfr : ∀ m', (∀ a < hi, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
      SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) :
    SelectLevelMetaBounded mem mloc C hi := by
  have hd : mloc.d = C.d := hm.1
  obtain ⟨hg0, htabs⟩ := hdisj.2.2.2.2
  refine ⟨hdisj.2.1, hg0, fun j hj => ?_, fun j hj => ?_⟩
  · have hjm : j ≤ mloc.d := by omega
    exact ⟨(hdisj.2.2.2.1 j hjm).1, (htabs j hjm).1, (htabs j hjm).2.1⟩
  · have hjm : j ≤ mloc.d := by omega
    have hembHi := (htabs j hjm).2.2
    refine ⟨Nat.zero_le _, hembHi, fun e he => ?_⟩
    obtain ⟨heCap, hwalk⟩ := hm.2.2.2.2.2.2.2.2.1 j hj e he
    refine ⟨heCap, Nat.zero_le _, ?_, hwalk⟩
    have hlen : 0 < (mWalkEncode (C.activeEmb j e)).length := by simp [mWalkEncode]
    by_contra hlt
    -- The word at `a = p + (hi - p)` lies at or above `hi` and inside the walk.
    have hi_lt : hi - mem (mloc.embPtr j + e) < (mWalkEncode (C.activeEmb j e)).length := by
      omega
    have hpi : hi ≤ mem (mloc.embPtr j + e) + (hi - mem (mloc.embPtr j + e)) := by omega
    have hfar : ∀ a < hi, a ≠ mem (mloc.embPtr j + e) + (hi - mem (mloc.embPtr j + e)) :=
      fun a ha => by omega
    have hm' := hfr (Function.update mem (mem (mloc.embPtr j + e) + (hi - mem (mloc.embPtr j + e)))
      (mem (mem (mloc.embPtr j + e) + (hi - mem (mloc.embPtr j + e))) + 1))
      (fun a ha _ => Function.update_of_ne (hfar a ha) _ _)
    have hwalk' := (hm'.2.2.2.2.2.2.2.2.1 j hj e he).2
    rw [Function.update_of_ne (hfar _ (by omega))] at hwalk'
    have h1 := hwalk' _ hi_lt
    have h2 := hwalk _ hi_lt
    rw [Function.update_self] at h1
    omega

/-- `selectProcessEdgeBody` meets `selectProcessEdgeContract` in `O(evalCost + log(cap+1) · Lk^2)` steps. -/
theorem selectProcessEdge_meetsContract {w h P proc evalKey upsert delIf : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selectProcessEdgeBody evalKey upsert delIf))
    (heval : MeetsContract w p evalKey (evalCandKeyContract w h P mloc C g ℓ φ coreLen evalSpace evalCost))
    (hups : ∀ size, MeetsContract w p upsert (heapUpsertContract w h loc size))
    (hdelIf : ∀ size, MeetsContract w p delIf (heapDeleteIfLevelContract w h loc size)) :
    MeetsContract w p proc (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, e, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, heCap, heEcap, hszCap,
    hat, hmeta0, hdisj, hmetaFr, hz, hroom⟩ := hpre
  have hmetaKeep := hmeta0
  have hbounded := selectLevelMetaBounded_of_frame hdisj hmeta0 hmetaFr
  obtain ⟨hmd, hmG0, hmD, hmTab, _, hGAt, _, _, _, hFAt, hSAt, _, _⟩ := hmeta0
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hDdisj := hdisj.2.2.2.1 lvl (by omega)
  have hmSize : mloc.metaBase + (2 + 8 * (mloc.d + 1)) ≤ scratch := hdisj.2.1
  have htabL := hmTab lvl hlvlD
  have hdW : mloc.d + 1 < 2 ^ w := by omega
  have hGP : mem (mloc.metaBase + 2 + lvl) = mloc.GPtr lvl := by
    simpa [smEntryAddr, smTableOff] using htabL.1
  have hvC : mem (mloc.metaBase + 2 + ((mloc.d + 1) + lvl)) = mloc.vCap lvl := by
    simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htabL.2.1
  have hfP : mem (mloc.metaBase + 2 + (6 * (mloc.d + 1) + lvl)) = mloc.fPtr lvl := by
    simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htabL.2.2.2.2.2.2.1
  have hGsz : dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) = 4 + 7 * mloc.vCap lvl + 9 * mloc.eCap lvl := rfl
  have hinG_eq : mem (mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + e) = if e ∈ (C.G lvl).E then 1 else 0 :=
    (hGAt lvl hlvlD).2.2.2.2.2.2.2.2.2.2.2.1 e heEcap
  have hinF_eq : mem (mloc.fPtr lvl + 4 + 7 * mloc.vCap lvl + e) = if e ∈ (C.activeLSF lvl).F.F.E then 1 else 0 :=
    (hFAt lvl hlvlD).2.2.2.2.2.2.2.2.2.2.2.1 e heEcap
  have hinGW : mem (mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + e) < 2 ^ w := by rw [hinG_eq]; split <;> omega
  have hinFW : mem (mloc.fPtr lvl + 4 + 7 * mloc.vCap lvl + e) < 2 ^ w := by rw [hinF_eq]; split <;> omega
  have hspRebal := selectProcessEdgeSpace_ge_rebal loc.cap loc.Lk evalSpace
  have hdelCost := selectProcessEdgeCost_ge_delIf loc.cap loc.Lk evalCost
  have hLkHdr : mem (loc.hb + 3) = loc.Lk := by simpa using hat.1 3 (by simp)
  have hhb3W : loc.hb + 3 < 2 ^ w := by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
  have hLkW : loc.Lk < 2 ^ w := by unfold selectProcessEdgeSpace at hroom; omega
  -- Helper for the non-candidate branch (`delIf [hb, e, lvl, scratch]`)
  have hcallDel : ∀ (regs1 : ℕ → ℕ) (k0 : ℕ),
      regs1 0 = loc.hb → regs1 2 = lvl → regs1 3 = e → regs1 4 = scratch →
      e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
      k0 + heapDeleteIfLevelCost loc.cap loc.Lk + 20 ≤ selectProcessEdgeCost loc.cap loc.Lk evalCost →
      ∃ o st' c, Runs w p ω (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))
        ⟨mem, regs1, pos⟩ o st' c ∧
        (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).post
          [loc.hb, mloc.metaBase, lvl, e, scratch] mem o.value st'.mem ∧
        k0 + c ≤ (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).cost
          [loc.hb, mloc.metaBase, lvl, e, scratch] mem := by
    intro regs1 k0 hr0 hr2 hr3 hr4 hnotC hk0
    refine runs_seq_call_flat (hdelIf size) (vs := [loc.hb, e, lvl, scratch])
      (by simp [evalArgs, Expr.eval, hr0, hr2, hr3, hr4]) (by wram_words) ?_ ?_
    · exact ⟨e, lvl, scratch, rfl, hw16, hendLe, heCap, by omega, hat, hz, by omega⟩
    · intro ret mem1 pos1 hp1
      obtain ⟨hlo1, hhi1, hat1, hz1, hhit1, hnhit1, hoth1, hfr1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo1 hhi1 hat1 hhit1 hnhit1 hoth1 hfr1
      have hretw : ret < 2 ^ w := by omega
      have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem1 a = mem a := fun a ha hout => by
        have hnumLe : loc.numBase ≤ loc.endAddr := by
          unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase; omega
        exact hfr1 a ha (by omega)
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [selectProcessEdgeContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        refine ⟨hlo1, by omega, ⟨_, hat1⟩, ⟨hmetaFr mem1 hfrOut, hfrOut⟩, hz1,
          fun h => (hnotC h).elim, fun _ => ⟨?_, ?_, ?_, ?_⟩, hoth1⟩
        · rintro ⟨hnz1, hl1⟩
          by_cases hhit : mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl
          · exact hnz1 (hhit1 hhit)
          · obtain ⟨hpE, hlE, _, _⟩ := hnhit1 hhit
            exact hhit ⟨hpE ▸ hnz1, hlE ▸ hl1⟩
        · intro h0
          have hnot : ¬ (mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl) := fun h => h.1 h0
          exact (hnhit1 hnot).1.trans h0
        · intro hnz hne
          have hnot : ¬ (mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl) := fun h => hne h.2
          obtain ⟨hpE, hlE, hnE, hdE⟩ := hnhit1 hnot
          exact ⟨hpE.symm ▸ hnz, hlE, hnE, hdE⟩
        · intro hnz hl
          exact hhit1 ⟨hnz, hl⟩
      · simp only [selectProcessEdgeContract, heapDeleteIfLevelContract, Expr.size, argsSize]; omega
  apply runs_start_le
  dsimp only [startState]
  unfold selectProcessEdgeBody
  simp only [smDOff, smTableOff, shLkOff]
  refine runs_seq_assign_flat (v := mloc.d) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.d + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.GPtr lvl) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.vCap lvl) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.fPtr lvl) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mem (mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + e)) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mem (mloc.fPtr lvl + 4 + 7 * mloc.vCap lvl + e)) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := 0) (by eval_expr) ?_
  let inSVal : ℕ := if e ∈ (C.activeS lvl).E then 1 else 0
  have hinSW : inSVal < 2 ^ w := by dsimp only [inSVal]; split <;> omega
  have hcontAfterS : ∀ (regs1 : ℕ → ℕ) (k0 : ℕ),
      regs1 0 = loc.hb → regs1 1 = mloc.metaBase → regs1 2 = lvl → regs1 3 = e → regs1 4 = scratch →
      regs1 10 = (if e ∈ (C.G lvl).E then 1 else 0) →
      regs1 11 = (if e ∈ (C.activeLSF lvl).F.F.E then 1 else 0) →
      regs1 12 = inSVal →
      k0 + evalCost + heapUpsertCost loc.cap loc.Lk + 60 ≤ selectProcessEdgeCost loc.cap loc.Lk evalCost →
      k0 + heapDeleteIfLevelCost loc.cap loc.Lk + 40 ≤ selectProcessEdgeCost loc.cap loc.Lk evalCost →
      ∃ o st' c, Runs w p ω
        (.cond (.reg 10)
          (.cond (.reg 11)
            (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))
            (.cond (.reg 12)
              (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))
              (.assign 15 (.load (.bin .add (.reg 0) (.const 3))) ;;
               .assign 16 (.bin .add (.reg 4) (.reg 15)) ;;
               .assign 17 (.bin .add (.reg 16) (.reg 15)) ;;
               .call 18 evalKey [.reg 1, .reg 2, .reg 3, .reg 4, .reg 16, .reg 15, .reg 17] ;;
               .call 19 upsert [.reg 0, .reg 3, .reg 2, .reg 4, .reg 16, .reg 18] ;;
               .ret (.reg 19))))
          (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14)))
        ⟨mem, regs1, pos⟩ o st' c ∧
        (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).post
          [loc.hb, mloc.metaBase, lvl, e, scratch] mem o.value st'.mem ∧
        k0 + c ≤ (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).cost
          [loc.hb, mloc.metaBase, lvl, e, scratch] mem := by
    intro regs1 k0 hr0 hr1 hr2 hr3 hr4 hr10 hr11 hr12 hkUps hkDel
    by_cases heG : e ∈ (C.G lvl).E
    · refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, hr10, heG]) ?_ (fun h => absurd h (by decide))
      intro _
      by_cases heF : e ∈ (C.activeLSF lvl).F.F.E
      · refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, hr11, heF]) ?_ (fun h => absurd h (by decide))
        intro _
        have hnotC : e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E := by
          simp [TreeChain.activeCore, coreGraph, heF]
        apply hcallDel regs1 _ hr0 hr2 hr3 hr4 hnotC (by simp [Expr.size]; omega)
      · refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, hr11, heF]) (fun h => absurd rfl h) ?_
        intro _
        by_cases heS : e ∈ (C.activeS lvl).E
        · refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, hr12, inSVal, heS])
            ?_ (fun h => absurd h (by decide))
          intro _
          have hnotC : e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E := by simp [heS]
          apply hcallDel regs1 _ hr0 hr2 hr3 hr4 hnotC (by simp [Expr.size]; omega)
        · refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, hr12, inSVal, heS])
            (fun h => absurd rfl h) ?_
          intro _
          have heCand : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E := by
            simp [TreeChain.activeCore, coreGraph, heG, heF, heS]
          have hscLk1 : scratch + loc.Lk < 2 ^ w := by unfold selectProcessEdgeSpace at hroom; omega
          have hscLk2 : scratch + loc.Lk + loc.Lk < 2 ^ w := by unfold selectProcessEdgeSpace at hroom; omega
          refine runs_seq_assign_flat (v := loc.Lk)
            (by simp [Expr.eval, BinOp.eval, hr0, show 3 < 2 ^ w by omega, hhb3W, hLkHdr]) ?_
          refine runs_seq_assign_flat (v := scratch + loc.Lk)
            (by simp [Expr.eval, BinOp.eval, hr4, hscLk1]) ?_
          refine runs_seq_assign_flat (v := scratch + loc.Lk + loc.Lk)
            (by simp [Expr.eval, BinOp.eval, hscLk2]) ?_
          refine runs_seq_call_flat heval
            (vs := [mloc.metaBase, lvl, e, scratch, scratch + loc.Lk, loc.Lk, scratch + loc.Lk + loc.Lk])
            (by simp [evalArgs, Expr.eval, hr1, hr2, hr3, hr4]) (by wram_words) ?_ ?_
          · exact ⟨lvl, e, scratch, scratch + loc.Lk, scratch + loc.Lk + loc.Lk, by rw [hLkEq], hw16,
              hpLastW, hlvlD, heCand, by omega, by omega, hmetaKeep,
              hbounded.mono (by omega),
              fun a ha => hz a (by omega), by unfold selectProcessEdgeSpace at hroom; omega⟩
          · intro sc1 mem1 pos1 hp1
            obtain ⟨hlo1, hhi1, hvn1, hvd1, hnw1, hdw1, hfixN1, hfixD1, hdPos1, hz1, hfr1⟩ := hp1
            simp only [List.getD_cons_zero, List.getD_cons_succ, hLkEq] at hlo1 hhi1 hvn1 hvd1 hnw1 hdw1 hfixN1 hfixD1 hdPos1 hfr1
            have hmem1_lt (a : ℕ) (ha : a < scratch) : mem1 a = mem a :=
              hfr1 a (by omega) (Or.inl ha) (Or.inl (by omega))
            have hat1 : SelectHeapAt mem1 loc h size := hat.of_agree fun a _ ha2 => hmem1_lt a (by omega)
            have hsc1W : sc1 < 2 ^ w := by unfold selectProcessEdgeSpace at hroom; omega
            refine runs_seq_call_flat (hups size) (vs := [loc.hb, e, lvl, scratch, scratch + loc.Lk, sc1])
              (by simp [evalArgs, Expr.eval, hr0, hr2, hr3, hr4]) (by wram_words) ?_ ?_
            · refine ⟨e, lvl, scratch, scratch + loc.Lk, sc1, rfl, hw16, by omega, heCap, by omega,
                fun h0 => hszCap (by rwa [hmem1_lt _ (by have := loc.endAddr_eq; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega)] at h0) heCand,
                by omega, by omega, Or.inr (by omega), Or.inr (by omega),
                hvn1, hvd1, hnw1, hdw1, hdPos1, hat1, hz1, by unfold selectProcessEdgeSpace at hroom; omega⟩
            · intro ret mem2 pos2 hp2
              obtain ⟨hlo2, hhi2, hat2, hz2, hpos2, hlvl2, hnum2, hden2, hoth2, hfr2⟩ := hp2
              simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo2 hhi2 hat2 hpos2 hlvl2 hnum2 hden2 hoth2 hfr2
              have hretw : ret < 2 ^ w := by unfold selectProcessEdgeSpace at hroom; omega
              have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
                fun a ha hout => (hfr2 a (by omega) hout).trans (hmem1_lt a ha)
              refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
              · dsimp only [selectProcessEdgeContract]
                simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
                refine ⟨by omega, by unfold selectProcessEdgeSpace; omega, ⟨_, hat2⟩,
                  ⟨hmetaFr mem2 hfrOut, hfrOut⟩, hz2, fun _ => ⟨hpos2, hlvl2, ?_⟩,
                  fun h => (h heCand).elim, fun e' he' hne => ?_⟩
                · rw [hnum2, hden2]
                  exact SelectKeyRepresents.of_fixVal hfixN1 hfixD1
                · obtain ⟨g1, g2, g3, g4⟩ := hoth2 e' he' hne
                  have heLk : e' * loc.Lk + loc.Lk ≤ loc.cap * loc.Lk := by
                    simpa [Nat.succ_mul] using Nat.mul_le_mul_right loc.Lk (Nat.succ_le_of_lt he')
                  have hlay : loc.posPtr + e' < scratch ∧ loc.lvlPtr + e' < scratch ∧
                      loc.numBase + e' * loc.Lk + loc.Lk ≤ scratch ∧
                      loc.denBase + e' * loc.Lk + loc.Lk ≤ scratch := by
                    have hend := loc.endAddr_eq
                    unfold selectHeapSize shHdrSize at hend
                    unfold SelectHeapLoc.denBase SelectHeapLoc.numBase
                      SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
                      SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize
                    omega
                  exact ⟨g1.trans (by rw [hmem1_lt _ hlay.1]),
                    g2.trans (hmem1_lt _ hlay.2.1),
                    g3.trans (Num.intVal_congr fun j hj => hmem1_lt _ (by omega)),
                    g4.trans (Num.intVal_congr fun j hj => hmem1_lt _ (by omega))⟩
              · simp only [selectProcessEdgeContract, evalCandKeyContract, heapUpsertContract,
                  Expr.size, argsSize]; omega
    · refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, hr10, heG]) (fun h => absurd rfl h) ?_
      intro _
      have hnotC : e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E := by
        simp [TreeChain.activeCore, coreGraph, heG]
      apply hcallDel regs1 _ hr0 hr2 hr3 hr4 hnotC (by simp [Expr.size]; omega)
  by_cases hlvlLt : lvl < C.d
  · have hsB := hDdisj.2.2.2.2 (by omega)
    have hsP : mem (mloc.metaBase + 2 + (7 * (mloc.d + 1) + lvl)) = mloc.sPtr lvl := by
      simpa [smEntryAddr, smTableOff, Nat.add_assoc] using htabL.2.2.2.2.2.2.2
    have hinS_eq : mem (mloc.sPtr lvl + 4 + 7 * mloc.vCap lvl + e) = inSVal :=
      (hSAt lvl hlvlLt).2.2.2.2.2.2.2.2.2.2.2.1 e heEcap
    refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hmd, hlvlLt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_flat (v := mloc.sPtr lvl) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := inSVal) (by eval_expr) ?_
    apply hcontAfterS _ _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [hinG_eq]) (by simp [hinF_eq]) (by simp)
      (by simp [selectProcessEdgeCost, Expr.size]; omega)
      (by simp [selectProcessEdgeCost, heapDeleteIfLevelCost, heapUpsertCost, heapDeleteCost, Expr.size]; omega)
  · have hlvlEqD : lvl = C.d := by omega
    have hinS0 : inSVal = 0 := by
      dsimp only [inSVal]; rw [hlvlEqD]; simp [TreeChain.activeS]
    refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hmd, hlvlLt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_nop_le ?_
    apply hcontAfterS _ _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [hinG_eq]) (by simp [hinF_eq]) (by simp [hinS0])
      (by simp [selectProcessEdgeCost, Expr.size]; omega)
      (by simp [selectProcessEdgeCost, heapDeleteIfLevelCost, heapUpsertCost, heapDeleteCost, Expr.size]; omega)

/-! ## 5. Verification of `selectProcessListBody` -/

/-- `selectProcessListBody` meets `selectProcessListContract` in `O(|L| · (evalCost + log · Lk^2))` steps. -/
theorem selectProcessList_meetsContract {w h P self procEdge : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {L : List ℕ} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[self]? = some (selectProcessListBody self procEdge))
    (hEdge : MeetsContract w p procEdge
      (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost)) :
    MeetsContract w p self
      (selectProcessListContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost) := by
  apply meetsContract_of_rec (fun args _ => L.length - args.getD 5 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨lvl, listPtr, idx, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, hidxLe,
    hlpSc, hlpDisj, hListAt, hLbd, hszRoom, hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  change L.length - idx = rem at hremEq
  subst hremEq
  have hhdSize : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hlpw : listPtr < 2 ^ w := hwords listPtr (by simp)
  have hlenw : L.length < 2 ^ w := hwords L.length (by simp)
  have hidxw : idx < 2 ^ w := hwords idx (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold selectProcessListBody
  by_cases hlt : idx < L.length
  · have heMem : L[idx] ∈ L := List.getElem_mem hlt
    obtain ⟨heCap, heEcap⟩ := hLbd L[idx] heMem
    have hread : mem (listPtr + idx) = L[idx] := hListAt idx hlt
    have heW : L[idx] < 2 ^ w := by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
    have hspSplit : selectProcessEdgeSpace loc.cap loc.Lk evalSpace +
        selectProcessListSpace (L.length - (idx + 1)) loc.cap loc.Lk evalSpace =
        selectProcessListSpace (L.length - idx) loc.cap loc.Lk evalSpace := by
      unfold selectProcessListSpace
      have h1 : L.length - idx = (L.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcostSplit : selectProcessEdgeCost loc.cap loc.Lk evalCost + 40 +
        selectProcessListCost (L.length - (idx + 1)) loc.cap loc.Lk evalCost =
        selectProcessListCost (L.length - idx) loc.cap loc.Lk evalCost := by
      unfold selectProcessListCost
      have h1 : L.length - idx = (L.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul]
      omega
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := L[idx]) (by eval_expr) ?_
    refine runs_seq_call_flat hEdge (vs := [loc.hb, mloc.metaBase, lvl, L[idx], scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨lvl, L[idx], scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, heCap, heEcap,
        fun _ _ => by omega, hat, hmeta, hdisj, hmetaFr, hz, by omega⟩
    · intro sc1 mem1 pos1 hp1
      obtain ⟨hlo1, hhi1, ⟨size1, hat1⟩, ⟨hmeta1, hfr1⟩, hz1, hcand1, hncand1, hoth1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo1 hhi1 hcand1 hncand1 hoth1 hfr1
      have hsc1W : sc1 < 2 ^ w := by omega
      have hhd1 : mem1 loc.hb = size1 := by simpa using hat1.1 0 (by simp)
      have hsz1Le : size1 ≤ size + 1 := by
        have hsub : (Finset.range size1).image (fun p => mem1 (loc.arrPtr + p)) ⊆
            insert L[idx] ((Finset.range size).image (fun p => mem (loc.arrPtr + p))) := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert] at hx ⊢
          obtain ⟨p, hp1', rfl⟩ := hx
          have hxCap : mem1 (loc.arrPtr + p) < loc.cap := hat1.2.1.2.1 p hp1'
          have hnz1 : mem1 (loc.posPtr + mem1 (loc.arrPtr + p)) ≠ 0 := hat1.2.1.pos_arr_ne_zero hp1'
          by_cases hxeq : mem1 (loc.arrPtr + p) = L[idx]
          · exact Or.inl hxeq
          · right
            have hnz0 : mem (loc.posPtr + mem1 (loc.arrPtr + p)) ≠ 0 := (hoth1 _ hxCap hxeq).1.mp hnz1
            rcases hat.2.1.2.2.2 _ hxCap with h0 | ⟨hle, harr⟩
            · exact (hnz0 h0).elim
            · exact ⟨mem (loc.posPtr + mem1 (loc.arrPtr + p)) - 1, by omega, harr⟩
        have hcard1 : ((Finset.range size1).image (fun p => mem1 (loc.arrPtr + p))).card = size1 := by
          rw [Finset.card_image_of_injOn]
          · simp
          · intro p1 hp1' p2 hp2' hEq
            exact hat1.2.1.arr_inj (Finset.mem_range.mp hp1') (Finset.mem_range.mp hp2') hEq
        have hcard0 : (insert L[idx] ((Finset.range size).image (fun p => mem (loc.arrPtr + p)))).card ≤ size + 1 :=
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_image_le.trans (by simp)) 1)
        exact hcard1 ▸ (Finset.card_le_card hsub).trans hcard0
      have hListAt1 : ListAt mem1 listPtr L := fun j hj =>
        (hfr1 (listPtr + j) (by omega) (by omega)).trans (hListAt j hj)
      have hdisj1 : SelectMetaDisjoint mloc loc sc1 :=
        ⟨hdisj.1, le_trans hdisj.2.1 hlo1, hdisj.2.2.1, fun j hj => by
          obtain ⟨a1, a2, a3, a4, a5⟩ := hdisj.2.2.2.1 j hj
          exact ⟨le_trans a1 hlo1, a2, le_trans a3 hlo1, a4, fun hjlt => ⟨le_trans (a5 hjlt).1 hlo1, (a5 hjlt).2⟩⟩,
          hdisj.2.2.2.2.mono hlo1⟩
      have hmetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem1 a) →
          SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
        fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1 a ha hout)
      refine runs_seq_call_flat ih
        (vs := [loc.hb, mloc.metaBase, lvl, listPtr, L.length, idx + 1, sc1])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨lvl, listPtr, idx + 1, sc1, size1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD, by omega,
          by omega, hlpDisj, hListAt1, hLbd, by omega, hat1, hmeta1, hdisj1,
          hmetaFr1, hz1, by omega⟩, by change L.length - (idx + 1) < L.length - idx; omega⟩
      · intro ret mem2 pos2 hp2
        obtain ⟨hlo2, hhi2, ⟨size2, hat2, hsz2Le⟩, ⟨hmeta2, hfr2⟩, hz2, hdrop2, hnotdrop2⟩ := hp2
        simp only [List.getD_cons_zero, List.getD_cons_succ, hhd1] at hlo2 hhi2 hsz2Le hdrop2 hnotdrop2 hfr2
        have hretw : ret < 2 ^ w := by omega
        have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
          fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
        refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · dsimp only [selectProcessListContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhdSize]
          refine ⟨by omega, by omega, ⟨size2, hat2, by omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
          · intro e heDrop
            rw [List.drop_eq_getElem_cons hlt, List.mem_cons] at heDrop
            rcases heDrop with rfl | heTail
            · by_cases hinTail : L[idx] ∈ L.drop (idx + 1)
              · exact ⟨(hdrop2 _ hinTail).1, fun hnc => ⟨((hdrop2 _ hinTail).2 hnc).1,
                  fun h0 => ((hdrop2 _ hinTail).2 hnc).2.1 ((hncand1 hnc).2.1 h0),
                  fun hnz hne => by
                    obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                    obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 _ hinTail).2 hnc).2.2.1 g1 (g2.symm ▸ hne)
                    exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩,
                  fun hnz hl => ((hdrop2 _ hinTail).2 hnc).2.1 ((hncand1 hnc).2.2.2 hnz hl)⟩⟩
              · obtain ⟨k1, k2, k3, k4⟩ := hnotdrop2 L[idx] heCap hinTail
                refine ⟨fun hc => ?_, fun hnc => ⟨?_, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
                · obtain ⟨g1, g2, g3⟩ := hcand1 hc
                  exact ⟨k1.mpr g1, k2.trans g2, by rw [k3, k4]; exact g3⟩
                · rintro ⟨hnz2, hl2⟩
                  exact (hncand1 hnc).1 ⟨k1.mp hnz2, k2.symm.trans hl2⟩
                · by_contra hnz2; exact (k1.mp hnz2) ((hncand1 hnc).2.1 h0)
                · obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                  exact ⟨k1.mpr g1, k2.trans g2, k3.trans g3, k4.trans g4⟩
                · by_contra hnz2; exact (k1.mp hnz2) ((hncand1 hnc).2.2.2 hnz hl)
            · refine ⟨(hdrop2 e heTail).1, fun hnc => ⟨((hdrop2 e heTail).2 hnc).1, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
              · by_cases heq : e = L[idx]
                · subst e; exact ((hdrop2 _ heTail).2 hnc).2.1 ((hncand1 hnc).2.1 h0)
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  have h01 : mem1 (loc.posPtr + e) = 0 := by
                    by_contra hnz1; exact ((hoth1 e heC heq).1.mp hnz1) h0
                  exact ((hdrop2 e heTail).2 hnc).2.1 h01
              · by_cases heq : e = L[idx]
                · subst e
                  obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                  obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 _ heTail).2 hnc).2.2.1 g1 (g2.symm ▸ hne)
                  exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  obtain ⟨g1, g2, g3, g4⟩ := hoth1 e heC heq
                  obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 e heTail).2 hnc).2.2.1 (g1.mpr hnz) (g2.symm ▸ hne)
                  exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
              · by_cases heq : e = L[idx]
                · subst e; exact ((hdrop2 _ heTail).2 hnc).2.1 ((hncand1 hnc).2.2.2 hnz hl)
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  obtain ⟨g1, g2, _, _⟩ := hoth1 e heC heq
                  exact ((hdrop2 e heTail).2 hnc).2.2.2 (g1.mpr hnz) (g2.trans hl)
          · intro e' he' hnotD
            rw [List.drop_eq_getElem_cons hlt, List.mem_cons, not_or] at hnotD
            obtain ⟨g1, g2, g3, g4⟩ := hoth1 e' he' hnotD.1
            obtain ⟨k1, k2, k3, k4⟩ := hnotdrop2 e' he' hnotD.2
            exact ⟨k1.trans g1, k2.trans g2, k3.trans g3, k4.trans g4⟩
        · simp only [Contract.below, selectProcessListContract, selectProcessEdgeContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega
  · have hdropNil : L.drop idx = [] := List.drop_eq_nil_of_le (by omega)
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hlt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [selectProcessListContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hdropNil, hhdSize]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨size, hat, Nat.le_add_right _ _⟩,
        ⟨hmeta, fun _ _ _ => rfl⟩, hz,
        fun _ h => (List.not_mem_nil h).elim, fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩⟩
    · simp only [selectProcessListContract, selectProcessListCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]; omega

end MinCostFlow.MinRatio
