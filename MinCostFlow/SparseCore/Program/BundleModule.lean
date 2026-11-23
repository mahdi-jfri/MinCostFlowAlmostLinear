module

public import MinCostFlow.SparseCore.Program.BundleInitMain
public import MinCostFlow.SparseCore.Program.BundleExportProcs
public import MinCostFlow.SparseCore.Program.BundleStepMain
public import MinCostFlow.SparseCore.Program.BundleStepScanAmort
public import MinCostFlow.DynSpanner.Program.MergeSort

/-!
# Relocatable deterministic Word-RAM bundle module (`BundleModule`)

Assembles all bundle manager procedures into a single relocatable deterministic procedure list
`bundleProcs b bTourList bTourLen bTourOwner` (length `15`, every procedure `Stmt.NoRand`) and
verifies:

1. `bundleProcs_length`, `bundleProcs_noRand`, `bundleProcs_unpack`.
2. `bundleTableRep`, `bundleTableRep_local`, `bundleTableDS`, and `bundleTableDS_implements`:
   `WordRAM.DSRep.Implements` for table initialization (`init`), bundle-graph export (`op 0`,
   producing the exact `DSInitPre` format of `bucketSpannerDS` op `0`), and `bundleOf` lookup
   (`op 1`).
3. `bundleModule_readParent_runs`, `bundleModule_initSlots_runs`, and `bundleModule_step_runs`:
   module-level entry points taking only `p.HasAt b (bundleProcs ...)` and `htour : BundleTourAt`.
4. `bundleModule_step_amortized_eq_bundleRunsStep`: full end-to-end model and potential bridge,
   showing that under `BundleStepReady` and split-group hypotheses, `bundleStepStmt` produces the
   exact batches and bundle states of `bundleRunsStep`, `bundleCompStep`, and `stepBundleTree`,
   with the smaller-side scan work telescoping into `bundleScanPotMul TS * tourPot`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedure offsets and relocatable table `bundleProcs` -/

def bundleOffSort : ℕ := 0
def bundleOffBase : ℕ := 4

def bundleIdxMergeSort : ℕ := bundleOffSort + sortIdxMergeSort
def bundleIdxTableInit : ℕ := bundleOffBase + bundleBaseIdxInit
def bundleIdxDllPush : ℕ := bundleOffBase + bundleBaseIdxDllPush
def bundleIdxDllErase : ℕ := bundleOffBase + bundleBaseIdxDllErase
def bundleIdxReadBundleOf : ℕ := bundleOffBase + bundleBaseIdxReadBundleOf
def bundleIdxReadParent : ℕ := bundleOffBase + bundleBaseIdxReadParent
def bundleIdxExportGraph : ℕ := 9
def bundleIdxInitSlots : ℕ := 10
def bundleIdxStepDel : ℕ := 11
def bundleIdxStepScan : ℕ := 12
def bundleIdxStepEmitSlot : ℕ := 13
def bundleIdxStep : ℕ := 14

/-- Complete relocatable deterministic procedure table for the bundle manager anchored at `b`,
calling external core-tour procedures at `bTourList`, `bTourLen`, `bTourOwner`. -/
def bundleProcs (b bTourList bTourLen bTourOwner : ℕ) : List Stmt :=
  sortProcs (b + bundleOffSort) ++
  bundleBaseProcs bTourOwner ++
  [bundleExportGraphStmt,
   bundleInitSlotsStmt (b + bundleIdxDllPush) bTourList,
   bundleStepDelStmt (b + bundleIdxDllErase),
   bundleStepScanStmt bTourLen bTourList,
   bundleStepEmitSlotStmt (b + bundleIdxDllPush) (b + bundleIdxDllErase)
     (b + bundleIdxMergeSort) bTourOwner,
   bundleStepStmt (b + bundleIdxStepDel) (b + bundleIdxStepScan) (b + bundleIdxStepEmitSlot)]

/-! ## 2. `WordRAM.DataStructure` specification for the standalone table operations -/

/-- `DSRep` for `BundleTableState slotCap` using `BundleTableRepAt`, bundle cap `k` at
`btBunCapAddr`, and footprint `bundleTableFoot eCap`. -/
def bundleTableRep (slotCap vCap eCap k : ℕ) : DSRep (BundleTableState slotCap) where
  τ := BundleTableMeta slotCap
  rep tbl S m mem := BundleTableRepAt slotCap vCap eCap tbl S m mem ∧
    mem (btBunCapAddr tbl slotCap eCap) = k
  phi _ _ _ := 0
  foot := bundleTableFoot eCap

/-- Precondition of `bundleTableDS` `init`: `args = [slotCap, vCap, eCap, k, h]`. -/
def BundleTableInitPre (w slotCap vCap eCap k : ℕ) (args : List ℕ) (_mem : ℕ → ℕ) : Prop :=
  ∃ h, args = [slotCap, vCap, eCap, k, h] ∧ 16 ≤ 2 ^ w ∧ vCap < 2 ^ w ∧ k < 2 ^ w

/-- Precondition of `bundleTableDS` op `0` (export `B.graph` for `bucketSpannerDS` op `0`):
`args = [tbl, j.1, h]`. -/
def BundleExportPre (w slotCap eCap : ℕ) (S : BundleTableState slotCap)
    (args : List ℕ) (_mem : ℕ → ℕ) : Prop :=
  ∃ (tbl : ℕ) (j : Fin slotCap) (B : BundleState) (h : ℕ),
    args = [tbl, j.1, h] ∧ 16 ≤ 2 ^ w ∧
    tbl + bundleTableFixedSize slotCap eCap < 2 ^ w ∧ S j = some B

/-- Postcondition of `bundleTableDS` op `0`: state unchanged, header `[nV, vPtr, nE, ePtr]` at `h`,
vertex list `[0..nV-1]` at `vPtr`, and edge triples representing `B.graph` at `ePtr`. -/
def BundleExportPost (slotCap : ℕ) (S : BundleTableState slotCap)
    (args : List ℕ) (_mem : ℕ → ℕ) (S' : BundleTableState slotCap) (mem' : ℕ → ℕ) : Prop :=
  S' = S ∧
  ∀ (hs : args.getD 1 0 < slotCap) B, S ⟨args.getD 1 0, hs⟩ = some B →
    let h := heapArg args
    let nV := B.vertices.card
    let nE := B.edges.card
    let vPtr := h + 4
    let ePtr := h + 4 + nV
    let vL := readList mem' vPtr nV
    let eT := readTriples mem' ePtr nE
    mem' h = nV ∧ mem' (h + 1) = vPtr ∧ mem' (h + 2) = nE ∧ mem' (h + 3) = ePtr ∧
    vL = List.range nV ∧
    (eT.map Prod.fst).Nodup ∧
    (∀ e, e ∈ eT.map Prod.fst ↔ e ∈ B.edges) ∧
    (∀ t ∈ eT, t.1 ∈ B.edges ∧ t.2.1 = B.graph.tail t.1 ∧ t.2.2 = B.graph.head t.1) ∧
    GraphEq (graphOfLists vL eT) B.graph

/-- Precondition of `bundleTableDS` op `1` (read `bundleOf` for a live end key):
`args = [tbl, key, h]`. -/
def BundleReadBundleOfPre (w slotCap eCap : ℕ) (S : BundleTableState slotCap)
    (args : List ℕ) (_mem : ℕ → ℕ) : Prop :=
  ∃ (tbl key : ℕ) (j : Fin slotCap) (B : BundleState) (h : ℕ),
    args = [tbl, key, h] ∧ 16 ≤ 2 ^ w ∧
    tbl + bundleTableFixedSize slotCap eCap < 2 ^ w ∧
    S j = some B ∧ (endOfKey key).1 ∈ B.edges

/-- Postcondition of `bundleTableDS` op `1`: state unchanged and `mem'[h] = B.bundleOf (endOfKey key)`. -/
def BundleReadBundleOfPost (slotCap : ℕ) (S : BundleTableState slotCap)
    (args : List ℕ) (_mem : ℕ → ℕ) (S' : BundleTableState slotCap) (mem' : ℕ → ℕ) : Prop :=
  S' = S ∧
  ∀ (j : Fin slotCap) B, S j = some B → (endOfKey (args.getD 1 0)).1 ∈ B.edges →
    mem' (heapArg args) = B.bundleOf (endOfKey (args.getD 1 0))

/-- Standalone `WordRAM.DataStructure` packaging `bundleTableInit` (`init`),
`bundleExportGraph` (`op 0`), and `bundleReadBundleOf` (`op 1`). -/
def bundleTableDS (w slotCap vCap eCap k : ℕ) : DataStructure (BundleTableState slotCap) where
  initPre := BundleTableInitPre w slotCap vCap eCap k
  initPost _ _ S' _ := S' = fun _ => none
  initCost _ _ := 180
  initSpace _ _ := bundleTableFixedSize slotCap eCap
  pre i S args mem :=
    if i = 0 then BundleExportPre w slotCap eCap S args mem
    else if i = 1 then BundleReadBundleOfPre w slotCap eCap S args mem
    else False
  post i S args mem S' mem' :=
    if i = 0 then BundleExportPost slotCap S args mem S' mem'
    else if i = 1 then BundleReadBundleOfPost slotCap S args mem S' mem'
    else False
  cost i S args _ :=
    if i = 0 then
      if hs : args.getD 1 0 < slotCap then
        match S ⟨args.getD 1 0, hs⟩ with
        | some B => bundleExportCost B
        | none => 0
      else 0
    else if i = 1 then 30
    else 0
  space i S args _ :=
    if i = 0 then
      if hs : args.getD 1 0 < slotCap then
        match S ⟨args.getD 1 0, hs⟩ with
        | some B => bundleExportSpace B
        | none => 0
      else 0
    else if i = 1 then 1
    else 0

end

public section

/-! ## 3. Length, determinism, and unpacking of `bundleProcs` -/

private lemma hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := by
  intro i hi
  have h1 := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at h1

private lemma hasAt_append_right {p : Program} {b n : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : xs.length = n) : p.HasAt (b + n) ys := by
  intro i hi
  have h1 := h (n + i) (by rw [List.length_append, hlen]; omega)
  rw [Nat.add_assoc]
  rw [List.getElem_append_right (by omega)] at h1
  simpa [hlen] using h1

private lemma hasAt_singleton {p : Program} {b i : ℕ} {xs : List Stmt} {s : Stmt}
    (h : p.HasAt b xs) (hi : i < xs.length) (hs : xs[i] = s) : p.HasAt (b + i) [s] := by
  intro j hj
  simp only [List.length_singleton, Nat.lt_one_iff] at hj
  subst hj; simp only [Nat.add_zero, List.getElem_singleton]
  simpa [hs] using h i hi

private lemma noRand_append {xs ys : List Stmt}
    (hx : ∀ s ∈ xs, s.NoRand) (hy : ∀ s ∈ ys, s.NoRand) :
    ∀ s ∈ xs ++ ys, s.NoRand := fun s hs =>
  (List.mem_append.mp hs).elim (hx s) (hy s)

theorem bundleProcs_length (b bTourList bTourLen bTourOwner : ℕ) :
    (bundleProcs b bTourList bTourLen bTourOwner).length = 15 := by
  unfold bundleProcs
  simp only [List.length_append, sortProcs_length, bundleBaseProcs_length, List.length_cons,
    List.length_nil]

/-- Every procedure in `bundleProcs` is deterministic (`Stmt.NoRand`). -/
theorem bundleProcs_noRand (b bTourList bTourLen bTourOwner : ℕ) :
    ∀ s ∈ bundleProcs b bTourList bTourLen bTourOwner, s.NoRand := by
  unfold bundleProcs
  refine noRand_append (noRand_append (sortProcs_noRand _) (bundleBaseProcs_noRand _)) ?_
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleExportGraphStmt_noRand
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleInitSlotsStmt_noRand _ _
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleStepDelStmt_noRand _
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleStepScanStmt_noRand _ _
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleStepEmitSlotStmt_noRand _ _ _ _
  rcases List.mem_cons.mp hs with rfl | hs; · exact bundleStepStmt_noRand _ _ _
  cases hs

/-- Unpacks `p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner)` into `HasAt` witnesses for
every sub-procedure of the bundle module. -/
theorem bundleProcs_unpack {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner)) :
    p.HasAt (b + bundleOffSort) (sortProcs (b + bundleOffSort)) ∧
    p.HasAt (b + bundleIdxTableInit) [bundleTableInitStmt] ∧
    p.HasAt (b + bundleIdxDllPush) [bundleDllPushStmt] ∧
    p.HasAt (b + bundleIdxDllErase) [bundleDllEraseStmt] ∧
    p.HasAt (b + bundleIdxReadBundleOf) [bundleReadBundleOfStmt] ∧
    p.HasAt (b + bundleIdxReadParent) [bundleReadParentStmt bTourOwner] ∧
    p.HasAt (b + bundleIdxExportGraph) [bundleExportGraphStmt] ∧
    p.HasAt (b + bundleIdxInitSlots) [bundleInitSlotsStmt (b + bundleIdxDllPush) bTourList] ∧
    p.HasAt (b + bundleIdxStepDel) [bundleStepDelStmt (b + bundleIdxDllErase)] ∧
    p.HasAt (b + bundleIdxStepScan) [bundleStepScanStmt bTourLen bTourList] ∧
    p.HasAt (b + bundleIdxStepEmitSlot)
      [bundleStepEmitSlotStmt (b + bundleIdxDllPush) (b + bundleIdxDllErase)
        (b + bundleIdxMergeSort) bTourOwner] ∧
    p.HasAt (b + bundleIdxStep)
      [bundleStepStmt (b + bundleIdxStepDel) (b + bundleIdxStepScan) (b + bundleIdxStepEmitSlot)] := by
  unfold bundleProcs at hp
  have h12 := hasAt_append_left hp
  have hRest := hasAt_append_right (n := 9) hp (by simp [sortProcs_length, bundleBaseProcs_length])
  have hSort : p.HasAt (b + bundleOffSort) (sortProcs (b + bundleOffSort)) := by
    simpa [bundleOffSort] using hasAt_append_left h12
  have hBase : p.HasAt (b + bundleOffBase) (bundleBaseProcs bTourOwner) :=
    hasAt_append_right h12 (sortProcs_length _)
  refine ⟨hSort, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [bundleIdxTableInit, bundleOffBase, bundleBaseIdxInit, bundleBaseProcs] using
      hasAt_singleton hBase (i := 0) (by simp [bundleBaseProcs_length]) rfl
  · simpa [bundleIdxDllPush, bundleOffBase, bundleBaseIdxDllPush, bundleBaseProcs, Nat.add_assoc] using
      hasAt_singleton hBase (i := 1) (by simp [bundleBaseProcs_length]) rfl
  · simpa [bundleIdxDllErase, bundleOffBase, bundleBaseIdxDllErase, bundleBaseProcs, Nat.add_assoc] using
      hasAt_singleton hBase (i := 2) (by simp [bundleBaseProcs_length]) rfl
  · simpa [bundleIdxReadBundleOf, bundleOffBase, bundleBaseIdxReadBundleOf, bundleBaseProcs, Nat.add_assoc] using
      hasAt_singleton hBase (i := 3) (by simp [bundleBaseProcs_length]) rfl
  · simpa [bundleIdxReadParent, bundleOffBase, bundleBaseIdxReadParent, bundleBaseProcs, Nat.add_assoc] using
      hasAt_singleton hBase (i := 4) (by simp [bundleBaseProcs_length]) rfl
  · simpa [bundleIdxExportGraph, Nat.add_assoc] using hasAt_singleton hRest (i := 0) (by simp) rfl
  · simpa [bundleIdxInitSlots, Nat.add_assoc] using hasAt_singleton hRest (i := 1) (by simp) rfl
  · simpa [bundleIdxStepDel, Nat.add_assoc] using hasAt_singleton hRest (i := 2) (by simp) rfl
  · simpa [bundleIdxStepScan, Nat.add_assoc] using hasAt_singleton hRest (i := 3) (by simp) rfl
  · simpa [bundleIdxStepEmitSlot, Nat.add_assoc] using hasAt_singleton hRest (i := 4) (by simp) rfl
  · simpa [bundleIdxStep, Nat.add_assoc] using hasAt_singleton hRest (i := 5) (by simp) rfl

/-! ## 4. Locality and `DSRep.Implements` for `bundleTableDS` -/

theorem bundleTableRep_local (slotCap vCap eCap k : ℕ) :
    (bundleTableRep slotCap vCap eCap k).Local := by
  intro tbl S m mem mem' hag
  exact ⟨fun ⟨h, hk⟩ => ⟨h.of_agree fun a ha => hag a ha,
    (hag _ (btBunCap_in_foot (m := m))).symm.trans hk⟩, rfl⟩

/-- `bundleProcs` implements `bundleTableDS` (`init = bundleTableInit`, `op 0 = bundleExportGraph`,
`op 1 = bundleReadBundleOf`). -/
theorem bundleTableDS_implements (w slotCap vCap eCap k : ℕ) {p : Program}
    {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner)) :
    (bundleTableRep slotCap vCap eCap k).Implements w p (b + bundleIdxTableInit)
      (fun i => if i = 0 then b + bundleIdxExportGraph else b + bundleIdxReadBundleOf)
      (bundleTableDS w slotCap vCap eCap k) := by
  obtain ⟨_, hpInit, _, _, hpReadB, _, hpExp, _, _, _, _, _⟩ := bundleProcs_unpack hp
  refine ⟨bundleTableRep_local slotCap vCap eCap k, ?_, ?_⟩
  · -- `init`
    intro args mem pos ω hW hpre hzero hspace
    rcases hpre with ⟨h, rfl, hw16, hvCap, hk_w⟩
    have hheap : heapArg [slotCap, vCap, eCap, k, h] = h := rfl
    rw [hheap] at hzero hspace ⊢
    have hmc := bundleTableInit_meetsContract (w := w) (slotCap := slotCap) (vCap := vCap)
      (eCap := eCap) (k := k) (h := h) hpInit
    obtain ⟨body, hbody, o, st', c, hrun, hpost, hc⟩ :=
      hmc [slotCap, vCap, eCap, k, h] mem pos ω hW ⟨rfl, hw16, hvCap, hk_w, hspace, hzero⟩
    rcases hpost with ⟨hret, hzf, hfr, hrep', hk'⟩
    refine ⟨body, hbody, o, st', c, hrun, fun _ => none, ⟨fun _ => none⟩, ⟨hrep', hk'⟩, rfl,
      ⟨by omega, by simpa [bundleTableDS] using le_of_eq hret, hret ▸ hzf, fun a ha _ => hfr a ha, fun a ha => ?_⟩,
      by simpa [bundleTableRep, bundleTableDS, bundleTableInitContract] using hc⟩
    rcases ha with ⟨h1, h2⟩ | ⟨_, _, _, hm, _, _⟩
    · exact Or.inr ⟨h1, by omega⟩
    · cases hm
  · -- `op i`
    intro i tbl S m args mem pos ω hW hhead hrep hpre hfoot hzero hspace
    by_cases hi0 : i = 0
    · subst hi0
      simp only [bundleTableDS, ↓reduceIte] at hpre hspace ⊢
      rcases hpre with ⟨tbl', j, B, h, rfl, hw16, htblFit, hSj⟩
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hheap : heapArg [tbl', j.1, h] = h := rfl
      rw [hheap] at hfoot hzero hspace ⊢
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        j.2, ↓reduceDIte] at hspace ⊢
      change h + (match S j with | some B => bundleExportSpace B | none => 0) < 2 ^ w at hspace
      rw [hSj] at hspace
      have hmc := bundleExportGraph_meetsContract (w := w) (slotCap := slotCap) (vCap := vCap)
        (eCap := eCap) (tbl := tbl') (h := h) (S := S) (m := m) (j := j) (B := B) hpExp
      obtain ⟨body, hbody, o, st', c, hrun, hpost, hc⟩ :=
        hmc [tbl', j.1, h] mem pos ω hW ⟨rfl, hw16, htblFit, hspace, hzero, hfoot, hrep.1, hSj⟩
      rcases hpost with ⟨hret, hzf, hfr, h0, h1, h2, h3, hvL, hnd, hmem, hsp, hgeq⟩
      refine ⟨body, hbody, o, st', c, hrun, S, m,
        ⟨hrep.1.of_agree fun a ha => (hfr a (hfoot a ha)).symm,
         (hfr _ (hfoot _ (btBunCap_in_foot (m := m)))).trans hrep.2⟩, ⟨rfl, fun hs B' hSB' => ?_⟩,
        ⟨by omega, by change o.value ≤ h + (match S j with | some B => bundleExportSpace B | none => 0); rw [hSj]; dsimp only; omega,
         hret ▸ hzf, fun a ha _ => hfr a ha, fun a ha => Or.inl ha⟩, ?_⟩
      · simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hSB'
        have hj_eq : (⟨j.1, hs⟩ : Fin slotCap) = j := Fin.ext rfl
        rw [hj_eq, hSj] at hSB'; cases hSB'
        exact ⟨h0, h1, h2, h3, hvL, hnd, hmem, hsp, hgeq⟩
      · change c + 0 ≤ (match S j with | some B => bundleExportCost B | none => 0) + 0
        rw [hSj]; simpa [bundleExportGraphContract] using hc
    · by_cases hi1 : i = 1
      · subst hi1
        simp only [bundleTableDS, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at hpre hspace ⊢
        rcases hpre with ⟨tbl', key, j, B, h, rfl, hw16, htblFit, hSj, heB⟩
        simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
        have hheap : heapArg [tbl', key, h] = h := rfl
        rw [hheap] at hfoot hzero hspace ⊢
        have hmc := bundleReadBundleOf_meetsContract (w := w) (slotCap := slotCap) (vCap := vCap)
          (eCap := eCap) (tbl := tbl') (key := key) (h := h) (S := S) (m := m) (j := j) (B := B) hpReadB
        obtain ⟨body, hbody, o, st', c, hrun, hpost, hc⟩ :=
          hmc [tbl', key, h] mem pos ω hW ⟨rfl, hw16, htblFit, hspace, hzero, hfoot, hrep.1, hSj, heB⟩
        rcases hpost with ⟨hret, hzf, hval, hfr⟩
        refine ⟨body, hbody, o, st', c, hrun, S, m,
          ⟨hrep.1.of_agree fun a ha => (hfr a (hfoot a ha)).symm,
           (hfr _ (hfoot _ (btBunCap_in_foot (m := m)))).trans hrep.2⟩, ⟨rfl, fun j' B' hSj' heB' => ?_⟩,
          ⟨by omega, by omega, hret ▸ hzf, fun a ha _ => hfr a ha, fun a ha => Or.inl ha⟩,
          by simpa [bundleTableRep, bundleReadBundleOfContract] using hc⟩
        simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at heB' ⊢
        have hj_eq : j' = j := by
          by_contra hne
          exact Finset.disjoint_left.mp (hrep.1.2.2.2.2.2.2.2.2.2.2.2.2.1 j' j hne B' B hSj' hSj) heB' heB
        subst hj_eq; rw [hSj] at hSj'; cases hSj'; exact hval
      · simp only [bundleTableDS, hi0, hi1, ↓reduceIte] at hpre

/-! ## 5. Module-level entry points for `readParent`, `initSlots`, and `step` -/

/-- Module-level `readParent` entry point at `b + bundleIdxReadParent`. -/
theorem bundleModule_readParent_runs {TS : BundleTourSpec} {w slotCap vCap eCap : ℕ} {p : Program}
    {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tbl tourH bun h : ℕ} {j : Fin slotCap} {S : BundleTableState slotCap}
    {m : BundleTableMeta slotCap} {B : BundleState} {cord : ℕ → List End}
    {tx : htour.rep.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hvCap : vCap < 2 ^ w)
    (htblFit : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) (htourH : tourH < 2 ^ w)
    (hhSpace : h + TS.querySpace < 2 ^ w) (hzero : ZeroFrom mem h)
    (hfootB : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    (hfootT : ∀ a, htour.rep.foot tourH tx a → a < h)
    (hdisjBT : ∀ a, bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx a)
    (hrepB : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hrepT : htour.rep.rep tourH cord tx mem)
    (hmatch : BundleTableCordMatch vCap S cord)
    (hSj : S j = some B) (hbun : bun ∈ B.vertices) :
    ∃ body, p.procs[b + bundleIdxReadParent]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
      BundleTableRepAt slotCap vCap eCap tbl S m st'.mem ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      st'.mem h = B.parent bun ∧
      h + 1 ≤ o.value ∧ o.value ≤ h + TS.querySpace ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        TS.mul * ordStoreLog eCap + 60 + htour.rep.phi tourH tx mem :=
  bundleReadParent_runs htour (bundleProcs_unpack hp).2.2.2.2.2.1 hw16 hvCap htblFit htourH
    hhSpace hzero hfootB hfootT hdisjBT hrepB hrepT hmatch hSj hbun

/-- Module-level `initSlots` entry point at `b + bundleIdxInitSlots`. -/
theorem bundleModule_initSlots_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k nSlots
    slotSpecPtr nEdges edgeAssignPtr nR rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k)
    (hk_mem : mem₀ (btBunCapAddr tbl slotCap eCap) = k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, bundleTableFoot eCap tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 * nSlots ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * nEdges ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * nEdges ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + nR ≤ h)
    (hrPtr_disj_tbl : rPtr + nR ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m₀ mem₀)
    (hcm0 : BundleTableCordMatch vCap S₀ cord)
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 * nSlots ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + nR ≤ a)
    (hnSlots : specs.length = nSlots) (hspecs_mem : bundleReadPairs mem₀ slotSpecPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap) (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_empty : ∀ sb ∈ specs, ∀ hlt : sb.1 < slotCap, S₀ ⟨sb.1, hlt⟩ = none)
    (hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2)
    (hnEdges : assigns.length = nEdges) (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr nEdges = assigns)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hassigns_fresh : ∀ es ∈ assigns, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → es.1 ∉ B.edges)
    (hnEdges_w : nEdges < 2 ^ w) (hnR : rList.length = nR) (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w) (hrList_nd : rList.Nodup)
    (hcord_nd : ∀ v ∈ rList, (cord v).Nodup) (hcord_lt : ∀ v ∈ rList, ∀ x ∈ cord v, x.1 < eCap)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v) :
    let S' := tableAfterInitSlots S₀ specs assigns cord rList k
    let m' := allocSlotBlocksMeta m₀ specs h
    let args := [tbl, tourH, nSlots, slotSpecPtr, nEdges, edgeAssignPtr, nR, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx',
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      h + slotBlocksSpace specs ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS specs cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      BundleTableRepAt slotCap vCap eCap tbl S' m' st'.mem ∧
      st'.mem (btBunCapAddr tbl slotCap eCap) = k ∧
      BundleTableCordMatch vCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, bundleTableFoot eCap tbl m' a →
        bundleTableFoot eCap tbl m₀ a ∨ (h ≤ a ∧ a < h + slotBlocksSpace specs)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ bundleTableFoot eCap tbl m₀ a → ¬ htour.rep.foot tourH tx₀ a →
        st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + htour.rep.phi tourH tx₀ mem₀ := by
  obtain ⟨_, _, hpPush, _, _, _, _, hpInitS, _, _, _, _⟩ := bundleProcs_unpack hp
  refine ⟨bundleInitSlotsStmt (b + bundleIdxDllPush) bTourList, hpInitS.head, ?_⟩
  exact bundleInitSlots_runs (htour := htour)
    (fun _ _ _ _ _ => bundleDllPush_meetsContract hpPush)
    hw16 hk1 hk_mem htourH_w htbl_h hfoot0_lt hspec_h hspec_disj_tbl hassign_h hassign_disj_tbl
    hrPtr_h hrPtr_disj_tbl hspace_w hrep0 hcm0 hzero0 htour_rep htour_foot_lt htour_foot_disj_tbl
    htour_foot_disj_blocks htour_foot_disj_spec htour_foot_disj_r hnSlots hspecs_mem hspecs_lt
    hspecs_nd hspecs_empty hspecs_cap hnEdges hassigns_mem hassigns_in hassigns_nd hassigns_fresh
    hnEdges_w hnR hrList_mem hrList_lt hrList_nd hcord_nd hcord_lt hcov

/-- Module-level `bundleStep` entry point at `b + bundleIdxStep`. -/
theorem bundleModule_step_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)}
    {cord' : ℕ → List End} {src' : End → ℕ} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount → ¬ bundleTableFoot eCap tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs → ¬ bundleTableFoot eCap tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a → ¬ bundleTableFoot eCap tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ tr ∈ dels, tr.1 < eCap ∧ tr.2.1 < 2 ^ w ∧ tr.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nodup : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hgs_ends_lt : ∀ G ∈ gs, ∀ v ∈ G, ∀ x ∈ cord' v, x.1 < eCap)
    (hgs_nd : ∀ G ∈ gs, ∀ v ∈ G, (cord' v).Nodup)
    (hsrc_lt : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), src' x < vCap)
    (hsrc_mem : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), x ∈ cord' (src' x))
    (hsrc_uniq : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), ∀ v', x ∈ cord' v' → v' = src' x)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) src' bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) bun,
            src' x ∈ gs[gi].toFinset)
    (hcap_ok : ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs j ≤ bunCap)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let candSet := addCandsForGroups (tableDelEdges S₀ (dels.map Prod.fst).toFinset)
        cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (dels.map Prod.fst).toFinset candSet scanLen cord' gs touched < 2 ^ w) :
    let D := (dels.map Prod.fst).toFinset
    let S_del := tableDelEdges S₀ D
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
      let S_final := tableAfterStep S₀ D src' candSet
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      maxIdxs.length = gs.length ∧
      (∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
        ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length) ∧
      touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
      (∀ j : Fin slotCap, match S₀ j with
        | none => j.1 ∉ touched
        | some B₀ => j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candSet j).Nonempty) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ D candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      BundleTableRepAt slotCap vCap eCap tbl S_final m st'.mem ∧
      st'.mem (btBunCapAddr tbl slotCap eCap) = mem₀ (btBunCapAddr tbl slotCap eCap) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) totalWords ∧
            ∃ lens, lens.length = (slotBatchOf S₀ D src' candSet ⟨s, hs⟩).length ∧
              lens.sum = totalWords - 1 ∧
              BatchBodyLensAt st'.mem (batchPtr + 1) B₀.graph
                (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) lens) ∧
      (∀ a < h₀, ¬ bundleTableFoot eCap tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs +
        htour.rep.phi tourH tx₀ mem₀ := by
  obtain ⟨hpSort, _, hpPush, hpErase, _, _, _, _, hpDel, hpScan, hpEmit, hpStep⟩ := bundleProcs_unpack hp
  have hMS : ∀ L : List ℕ, MeetsContract w p (b + bundleIdxMergeSort) (mergeSortContract w L) := by
    intro L
    have h1 := mergeSort_meetsContract (w := w) (p := p) (b := b + bundleOffSort)
      (bSort := b + bundleOffSort) (L := L) hpSort hpSort
    simpa [bundleIdxMergeSort, bundleOffSort, Nat.add_assoc] using h1
  refine ⟨_, hpStep.head, ?_⟩
  exact bundleStep_runs htour hpPush hpErase hMS hpDel hpScan hpEmit hw16 htourH_w hpk_w
    htbl_w hblks_w hdel_w hgrp_w hout_w hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot
    hgrp_disj_foot hout_disj_foot htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out
    hzero htrep hrep0 hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nodup hgs_disj
    hgs_ends_lt hgs_nd hsrc_lt hsrc_mem hsrc_uniq hbundle_in_group hcap_ok hh_sp

/-- Any nonempty batch emitted by `bundleModule_step_runs` has word length `W ≤ 6 * Enc(U_B)`. -/
theorem bundleStep_batchWords_le_enc {mem : ℕ → ℕ} {batchPtr totalWords : ℕ}
    {G : MGraph} {U_B : List Update}
    (h : SmallBatchAt mem batchPtr G U_B totalWords) (hne : U_B ≠ []) :
    totalWords ≤ 6 * G.batchEnc U_B :=
  smallBatchAt_words_le_of_nonempty h hne

/-- Any batch emitted by `bundleModule_step_runs` has word length `W ≤ 6 * X` whenever
`Enc(U_B) ≤ X` and `1 ≤ X` (matching `bucketUpdateCost_le_of_words` with `c_W = 6`). -/
theorem bundleStep_batchWords_le_charge {mem : ℕ → ℕ} {batchPtr totalWords X : ℕ}
    {G : MGraph} {U_B : List Update}
    (h : SmallBatchAt mem batchPtr G U_B totalWords)
    (hEnc : G.batchEnc U_B ≤ X) (hX : 1 ≤ X) :
    totalWords ≤ 6 * X :=
  smallBatchAt_words_le_charge h hEnc hX

/-! ## 6. End-to-end model equivalence & `tourPot` telescoping bridge -/

/-- Combines `bundleModule_step_runs`, `scanCands_eq_exactSplitCands`,
`scanNonMaxSum_le_tourPot_drop`, and `bundleStepEmitSlot_eq_bundleRunsStep` into a single
amortized model-bridge theorem:
* Every active slot `j` satisfies exact agreement between the program's emitted batch / updated
  state and `bundleRunsStep` / `bundleCompStep` (and hence `(stepBundleTree ...).U_B` and
  `.state.bun`).
* The total cost telescopes `bundleScanPotMul TS * totalNonMaxLen` into the drop of
  `bundleScanPotMul TS * tourPot`. -/
theorem bundleModule_step_amortized_eq_bundleRunsStep {TS : BundleTourSpec}
    {eCap slotCap : ℕ} {S₀ : BundleTableState slotCap} {cs : CompLSFState} {k : ℕ}
    {ord ord' cord cord' : ℕ → List End} {U : List Update}
    {R_old R_new : Finset ℕ} {gs : List (List ℕ)} {oldRoots maxIdxs : List ℕ}
    {c baseCost phi₀ phi₁ : ℕ}
    (hD_eq : ∀ j B₀, S₀ j = some B₀ → BundleStepReady cs B₀ k ord ord' U)
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hcord_nd : ∀ G ∈ gs, ∀ v ∈ G, (cord' v).Nodup)
    (hmax_spec : ∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
      ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length)
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ v ∈ gs[gi].toFinset, (cord' v).length) ≤ (cord (oldRoots[gi]'(by omega))).length)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧ (cord' r).length ≤ (cord r).length)
    (hsrc_iff : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ batchDeletes U), ∀ v,
        x ∈ cord' v ↔ (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x = v)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) b,
            (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src x ∈ gs[gi].toFinset)
    (hcost : c + phi₁ ≤ baseCost + bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs + phi₀) :
    let D := batchDeletes U
    let src' := (Chain.coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src
    let candSet := addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length
    let S_final := tableAfterStep S₀ D src' candSet
    (∀ j B₀, S₀ j = some B₀ →
      let res := bundleCompStep cs B₀ k ord ord' U
      ∃ B_new, S_final j = some B_new ∧
        res.1 = slotBatchOf S₀ D src' candSet j ∧
        res.2.vertices = B_new.vertices ∧
        res.2.edges = B_new.edges ∧
        res.2.bundleOf = B_new.bundleOf) ∧
    c + bundleScanPotMul TS eCap * tourPot R_new cord' + phi₁ ≤
      baseCost + bundleScanPotMul TS eCap * tourPot R_old cord + phi₀ := by
  intro D src' candSet S_final
  constructor
  · intro j B₀ hS₀j
    have hready := hD_eq j B₀ hS₀j
    have hcand : candSet j = (exactSplitCands B₀ (B₀.edges \ D) src').toFinset :=
      scanCands_eq_exactSplitCands hS₀j hgs_nd hcord_nd
        (fun gi hgi => (hmax_spec gi hgi).1) (hsrc_iff j B₀ hS₀j) (hbundle_in_group j B₀ hS₀j)
    have heq := bundleStepEmitSlot_eq_bundleRunsStep hready hcand
    rw [← bundleCompStep_eq hready] at heq
    refine ⟨(byRootSplitFold B₀ (B₀.edges \ D) src'
      (((B₀.edges ∩ D).sort (· ≤ ·)).map Update.delete) ((candSet j).sort (· ≤ ·))).2,
      by simp [S_final, tableAfterStep, hS₀j], ?_, heq.2.1, heq.2.2.1, heq.2.2.2⟩
    simpa [slotBatchOf, hS₀j] using heq.1
  · have hdrop := scanNonMaxSum_le_tourPot_drop hold_len hold_nd hold_sub hgs_nd hgs_sub hgs_disj
      hmax_spec hgroup_sum_le hrest_le
    have hmul := Nat.mul_le_mul_left (bundleScanPotMul TS eCap) hdrop
    rw [Nat.mul_add] at hmul
    omega

end

end MinCostFlow.SparseCore.Program
