module

public import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
public import MinCostFlow.MinRatio.WireChainCoreReembPlaceKFBL
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepModel
public import MinCostFlow.SparseCore.CanonCoreSpec
public import MinCostFlow.SparseCore.BundleOutBatchSpec
import MinCostFlow.SparseCore.Program.OutStepJoinModel
import Mathlib.Tactic

/-!
# Auxiliary lemmas for `SparseCoreUpdateOutFootAt` (`AssemblyUpdateOutAux`)

Provides the pure structural lemmas needed to establish `SparseCoreUpdateOutFootAt`
(`MinRatio/WireChainCoreOp0KFBL.lean`) at the top layer of the sparse-core assembly:

1. `BatchSplitEndsExact` and `decodeBatch_eq_of_batchAt`: when every `.split v v' St Sh` in a
   batch names only tail ends at `v` in `St` and head ends at `v` in `Sh` at the intermediate
   graph, `BatchAt mem a G U W` implies `(decodeBatch mem a G).1 = U`.
2. `stepBundleTree_U_S_splitEndsExact`: every output batch `info.U_S = buildUSOrd ...` produced
   by `stepBundleTree` satisfies `BatchSplitEndsExact tr.S_cur info.U_S` (via `refineSplit` and
   `restrictSplits`).
3. `batchAt_words_lt` and `stepBundleTree_U_S_insert_lt`: every word in a `BatchAt` buffer
   representing a valid batch whose vertices and edges stay below `(vCap, eCap)` is strictly below
   `B` (in particular `< 2 ^ w`).
4. `sparseCoreUpdateOutFootAt_shift`: relocation of `SparseCoreUpdateOutFootAt` across
   `shiftProgramProcs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio

/-! ## 1. Exact split ends and `decodeBatch` inversion -/

/-- Every `.split v v' St Sh` in a batch contains only live edges whose tail (for `St`) or head
(for `Sh`) is `v` in the intermediate graph at that step. -/
def BatchSplitEndsExact : MGraph → List Update → Prop
  | _, [] => True
  | G, .split v v' St Sh :: U =>
      (∀ e ∈ St, e ∈ G.E ∧ G.tail e = v) ∧
      (∀ e ∈ Sh, e ∈ G.E ∧ G.head e = v) ∧
      BatchSplitEndsExact (G.applyUpdate (.split v v' St Sh)) U
  | G, u :: U => BatchSplitEndsExact (G.applyUpdate u) U

theorem batchSplitEndsExact_append {G : MGraph} {U₁ U₂ : List Update}
    (h₁ : BatchSplitEndsExact G U₁) (h₂ : BatchSplitEndsExact (G.applyBatch U₁) U₂) :
    BatchSplitEndsExact G (U₁ ++ U₂) := by
  induction U₁ generalizing G with
  | nil => exact h₂
  | cons u rest ih =>
    cases u with
    | insert e a b => exact ih h₁ h₂
    | delete e => exact ih h₁ h₂
    | split v v' St Sh => exact ⟨h₁.1, h₁.2.1, ih h₁.2.2 h₂⟩

theorem batchSplitEndsExact_congr {G H : MGraph} (heq : GraphEq G H) {U : List Update}
    (h : BatchSplitEndsExact G U) : BatchSplitEndsExact H U := by
  induction U generalizing G H with
  | nil => trivial
  | cons u rest ih =>
    have heq' := graphEq_applyUpdate heq u
    cases u with
    | insert e a b => exact ih heq' h
    | delete e => exact ih heq' h
    | split v v' St Sh =>
      refine ⟨fun e he => ?_, fun e he => ?_, ih heq' h.2.2⟩
      · obtain ⟨heG, ht⟩ := h.1 e he
        exact ⟨heq.2.1 ▸ heG, (heq.2.2 e heG).1.symm.trans ht⟩
      · obtain ⟨heG, hh⟩ := h.2.1 e he
        exact ⟨heq.2.1 ▸ heG, (heq.2.2 e heG).2.symm.trans hh⟩

theorem batchSplitEndsExact_of_noSplit {G : MGraph} {U : List Update}
    (h : ∀ u ∈ U, match u with | .split _ _ _ _ => False | _ => True) :
    BatchSplitEndsExact G U := by
  induction U generalizing G with
  | nil => trivial
  | cons u rest ih =>
    cases u with
    | insert e a b => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | delete e => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | split v v' St Sh => exact False.elim (h _ List.mem_cons_self)

private theorem readList_eq_of_listAt {mem : ℕ → ℕ} {a : ℕ} {L : List ℕ}
    (h : ListAt mem a L) : readList mem a L.length = L := by
  apply List.ext_getElem
  · simp [readList]
  · intro i hi1 hi2
    simp only [readList, List.getElem_map, List.getElem_range]
    exact h i hi2

private theorem listAt_shift {mem : ℕ → ℕ} {a : ℕ} {L₁ L₂ : List ℕ}
    (h : ListAt mem a (L₁ ++ L₂)) : ListAt mem a L₁ ∧ ListAt mem (a + L₁.length) L₂ := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := h i (by simp; omega)
    simpa [List.getElem_append_left hi] using h1
  · have h1 := h (L₁.length + i) (by simp; omega)
    rw [show a + (L₁.length + i) = a + L₁.length + i by omega] at h1
    simpa [List.getElem_append_right (Nat.le_add_right L₁.length i)] using h1

/-- Single-update split-end exactness predicate. -/
def UpdateSplitEndsExact (G : MGraph) : Update → Prop
  | .split v _ St Sh => (∀ e ∈ St, e ∈ G.E ∧ G.tail e = v) ∧ (∀ e ∈ Sh, e ∈ G.E ∧ G.head e = v)
  | _ => True

/-- Decoding a single `UpdateAt` record recovers `(u, len)` whenever a split's `St`/`Sh` sets
contain only live tail/head ends at `v`. -/
theorem decodeUpdate_eq_of_updateAt {mem : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update}
    (hAt : UpdateAt mem a G u len) (hEnds : UpdateSplitEndsExact G u) :
    decodeUpdate mem a G = (u, len) := by
  cases u with
  | insert e x y =>
    rcases hAt with ⟨rfl, hL⟩
    have h0 : mem a = 0 := by simpa using hL 0 (by simp)
    have h1 : mem (a + 1) = e := hL 1 (by simp)
    have h2 : mem (a + 2) = x := hL 2 (by simp)
    have h3 : mem (a + 3) = y := hL 3 (by simp)
    simp [decodeUpdate, h0, h1, h2, h3]
  | delete e =>
    rcases hAt with ⟨rfl, hL⟩
    have h0 : mem a = 1 := by simpa using hL 0 (by simp)
    have h1 : mem (a + 1) = e := hL 1 (by simp)
    simp [decodeUpdate, h0, h1]
  | split v v' St Sh =>
    obtain ⟨hStE, hShE⟩ := hEnds
    rcases hAt with ⟨Lt, Lh, -, -, hLt, hLh, rfl, hL⟩ | ⟨Lt, Lh, -, -, hLt, hLh, rfl, hL⟩
    · have ⟨hHdr, hLhAt⟩ := listAt_shift hL
      have ⟨hPre, hLtAt⟩ := listAt_shift hHdr
      have h0 : mem a = 2 := by simpa using hPre 0 (by simp)
      have h1 : mem (a + 1) = v := hPre 1 (by simp)
      have h2 : mem (a + 2) = v' := hPre 2 (by simp)
      have h3 : mem (a + 3) = Lt.length := hPre 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := hPre 4 (by simp)
      have hrLt : readList mem (a + 5) Lt.length = Lt :=
        readList_eq_of_listAt (by simpa using hLtAt)
      have hrLh : readList mem (a + 5 + Lt.length) Lh.length = Lh := by
        rw [show a + 5 + Lt.length = a + ([2, v, v', Lt.length, Lh.length] ++ Lt).length by
          simp; omega]
        exact readList_eq_of_listAt hLhAt
      have hStEq : Lt.toFinset = St := by
        ext e; rw [List.mem_toFinset, hLt]
        exact ⟨fun h => h.2.2, fun h => ⟨(hStE e h).1, (hStE e h).2, h⟩⟩
      have hShEq : Lh.toFinset = Sh := by
        ext e; rw [List.mem_toFinset, hLh]
        exact ⟨fun h => h.2.2, fun h => ⟨(hShE e h).1, (hShE e h).2, h⟩⟩
      simp [decodeUpdate, h0, h1, h2, h3, h4, hrLt, hrLh, hStEq, hShEq]
    · have ⟨hHdr, hLhAt⟩ := listAt_shift hL
      have ⟨hPre, hLtAt⟩ := listAt_shift hHdr
      have h0 : mem a = 3 := by simpa using hPre 0 (by simp)
      have h1 : mem (a + 1) = v := hPre 1 (by simp)
      have h2 : mem (a + 2) = v' := hPre 2 (by simp)
      have h3 : mem (a + 3) = Lt.length := hPre 3 (by simp)
      have h4 : mem (a + 4) = Lh.length := hPre 4 (by simp)
      have hrLt : readList mem (a + 5) Lt.length = Lt :=
        readList_eq_of_listAt (by simpa using hLtAt)
      have hrLh : readList mem (a + 5 + Lt.length) Lh.length = Lh := by
        rw [show a + 5 + Lt.length = a + ([3, v, v', Lt.length, Lh.length] ++ Lt).length by
          simp; omega]
        exact readList_eq_of_listAt hLhAt
      have hStEq : G.E.filter (fun e => G.tail e = v) \ Lt.toFinset = St := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset, hLt]
        constructor
        · rintro ⟨⟨he, ht⟩, hnot⟩
          by_contra hns; exact hnot ⟨he, ht, hns⟩
        · intro h
          exact ⟨⟨(hStE e h).1, (hStE e h).2⟩, fun h' => h'.2.2 h⟩
      have hShEq : G.E.filter (fun e => G.head e = v) \ Lh.toFinset = Sh := by
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_filter, List.mem_toFinset, hLh]
        constructor
        · rintro ⟨⟨he, hh⟩, hnot⟩
          by_contra hns; exact hnot ⟨he, hh, hns⟩
        · intro h
          exact ⟨⟨(hShE e h).1, (hShE e h).2⟩, fun h' => h'.2.2 h⟩
      simp [decodeUpdate, h0, h1, h2, h3, h4, hrLt, hrLh, hStEq, hShEq]

private theorem decodeBatchBody_eq_of_batchBodyAt {mem : ℕ → ℕ} :
    ∀ {a W : ℕ} {G : MGraph} {U : List Update},
      BatchBodyAt mem a G U W → BatchSplitEndsExact G U →
      (decodeBatchBody mem U.length a G).1 = U
  | _, _, _, [], _, _ => rfl
  | a, W, G, u :: rest, ⟨len, _, hu, hrest⟩, hEnds => by
    have hEndsU : UpdateSplitEndsExact G u := by
      cases u with
      | insert => trivial
      | delete => trivial
      | split => exact ⟨hEnds.1, hEnds.2.1⟩
    have hEndsR : BatchSplitEndsExact (G.applyUpdate u) rest := by
      cases u with
      | insert => exact hEnds
      | delete => exact hEnds
      | split => exact hEnds.2.2
    have hdu := decodeUpdate_eq_of_updateAt hu hEndsU
    simp only [List.length_cons, decodeBatchBody, hdu]
    exact congrArg (u :: ·) (decodeBatchBody_eq_of_batchBodyAt hrest hEndsR)

/-- `decodeBatch` recovers `U` from `BatchAt mem a G U W` whenever every split in `U` names only
live tail/head ends at its split vertex. -/
theorem decodeBatch_eq_of_batchAt {mem : ℕ → ℕ} {a W : ℕ} {G : MGraph} {U : List Update}
    (hAt : BatchAt mem a G U W) (hEnds : BatchSplitEndsExact G U) :
    (decodeBatch mem a G).1 = U := by
  unfold decodeBatch
  rw [hAt.2.1]
  exact decodeBatchBody_eq_of_batchBodyAt hAt.2.2 hEnds

/-! ## 2. `BatchSplitEndsExact` for `canonCoreBatch`, `restrictSplits`, and `stepBundleTree` -/

private theorem refineSplit_splitEndsExact {C C' : MGraph} {r fresh : ℕ}
    (hC : C.IsValid) (hfresh : fresh ∉ C.V)
    (hEq : GraphEq C' (C.applyUpdate (refineSplit C C' r fresh))) :
    BatchSplitEndsExact C [refineSplit C C' r fresh] := by
  refine ⟨fun e he => ?_, fun e he => ?_, trivial⟩
  · have hmem := Finset.mem_filter.mp he
    refine ⟨hmem.1, ?_⟩
    have heC' : e ∈ C'.E := hEq.2.1.symm ▸ hmem.1
    have htail := (hEq.2.2 e heC').1
    rw [hmem.2] at htail
    simp only [refineSplit, MGraph.applyUpdate, Finset.mem_filter, hmem.1, hmem.2, and_self] at htail
    by_contra hne
    simp [hne] at htail
    exact hfresh (htail ▸ (hC e hmem.1).1)
  · have hmem := Finset.mem_filter.mp he
    refine ⟨hmem.1, ?_⟩
    have heC' : e ∈ C'.E := hEq.2.1.symm ▸ hmem.1
    have hhead := (hEq.2.2 e heC').2
    rw [hmem.2] at hhead
    simp only [refineSplit, MGraph.applyUpdate, Finset.mem_filter, hmem.1, hmem.2, and_self] at hhead
    by_contra hne
    simp [hne] at hhead
    exact hfresh (hhead ▸ (hC e hmem.1).2)

private theorem releasesBatch_splitEndsExact {G : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    {L L' : LSF} (cuts : List ℕ) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (hR : L.F.R ⊆ L'.F.R)
    (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) :
    BatchSplitEndsExact (coreGraph G L) (releasesBatch G L'.F.R L cuts) := by
  induction cuts generalizing L with
  | nil => trivial
  | cons e cuts ih =>
    let K := eraseForestEdge L.F.F e
    have he := hMem e List.mem_cons_self
    have hKn := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = L'.F.F := hCut
    have hFinalK : K.IsSubgraph L'.F.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ a ∈ L.F.R, ∀ b ∈ L.F.R, K.Connected a b → a = b := fun a ha b hb hConn => by
      have hr := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hr
    obtain ⟨hIncl, hSub, hMid⟩ := canonRoots_spec hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R L'.F.R⟩, L.wstr⟩
    have hRc : (canonRoots K L.F.R L'.F.R).card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact forest_eraseEdge_components_card hF.1 he
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    have hnew : newRoot Lmid.F.R L.F.R = fresh := newRoot_eq heq hf
    have hH : (G.applyUpdate (.delete e)).IsValid := fun f hf => hG f (Finset.mem_of_mem_erase hf)
    have heF' : e ∉ Lmid.F.F.E := Finset.notMem_erase _ _
    have hFH : Lmid.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)) :=
      ⟨hMid.1, hMid.2.1, hMid.2.2.1, hMid.2.2.2.1, hMid.2.2.2.2.1,
        fun f hh => Finset.mem_erase.mpr ⟨fun heq => heF' (heq ▸ hh), hMid.2.2.2.2.2.1 hh⟩,
        hMid.2.2.2.2.2.2⟩
    have hSubG : G.IsSubgraph (G.applyUpdate (.delete e)) :=
      ⟨Finset.Subset.rfl, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩
    have hDel : RotationStep 2 (.delete e) ρ (ρ.restrict hSubG) := fun w => by
      have hres : ((ρ.restrict hSubG).order w) = (ρ.order w).filter (fun x => x.1 != e) := by
        apply List.filter_congr
        intro x hx
        apply Bool.eq_iff_iff.mpr
        simp only [MGraph.applyUpdate, decide_eq_true_eq, Finset.mem_erase, bne_iff_ne]
        exact ⟨And.left, fun h => ⟨h, ((ρ.mem_order _ _).mp hx).1⟩⟩
      rw [hres]
    have hCutOCB := orderedCore_delete_forest_canon (L' := Lmid) ρ (ρ.restrict hSubG) hG hH hF hFH
      he rfl heq hf hDel (le_refl 2)
    have hRelOCB := orderedCore_release_canon (L' := Lmid) ρ hG hF hMid he rfl heq hf (le_refl 2)
    have hCoreVal : (coreGraph G L).IsValid := coreGraph_isValid hG hF
    have hSpExact := refineSplit_splitEndsExact hCoreVal hf hCutOCB.2.choose
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := fun f hf =>
      Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf),
        hMem f (List.mem_cons_of_mem _ hf)⟩
    have hRestExact := ih (L := Lmid) hMid hSub hCut hMemRest (List.nodup_cons.mp hn).2
    have hConsEq : releasesBatch G L'.F.R L (e :: cuts) =
        [refineSplit (coreGraph G L) (coreGraph (G.applyUpdate (.delete e)) Lmid)
            (L.F.root (L.F.F.tail e)) fresh,
          .insert e (Lmid.F.root (G.tail e)) (Lmid.F.root (G.head e))] ++
          releasesBatch G L'.F.R Lmid cuts := by
      simp [releasesBatch, Lmid, K, hnew]
    rw [hConsEq]
    refine batchSplitEndsExact_append ?_ (batchSplitEndsExact_congr hRelOCB.2.choose hRestExact)
    exact ⟨hSpExact.1, hSpExact.2.1, trivial⟩

private theorem inputCoreBatch_splitEndsExact {cs : CompLSFState} {u : Update} {last : LSF}
    (ρ : Rotation cs.G) (σ : Rotation (cs.G.applyUpdate u))
    (hG : cs.G.IsValid) (hH : (cs.G.applyUpdate u).IsValid)
    (hF : cs.lsf.F.IsRootedSpanningForestOf cs.G)
    (hlast : last.F.IsRootedSpanningForestOf (cs.G.applyUpdate u))
    (hlastR : last.F.R = (compLSFStepSingle cs u).RF.R)
    (hu : cs.G.UpdateIsValid u) (hs : RotationStep 2 u ρ σ)
    (hR : cs.lsf.F.R ⊆ last.F.R)
    (hK : (forestAfterInput cs.lsf.F.F u).IsForest)
    (hKG : (cs.G.applyUpdate u).IsSubgraph (forestAfterInput cs.lsf.F.F u))
    (hsub : (forestAfterInput cs.lsf.F.F u).IsSubgraph last.F.F) :
    BatchSplitEndsExact (coreGraph cs.G cs.lsf) (inputCoreBatch cs u) := by
  obtain ⟨_, _, _, _, hOCB, _, _⟩ :=
    orderedCore_inputCoreBatch ρ σ hG hH hF hlast hlastR hu hs (le_refl 2) hR hK hKG hsub
  have hCoreVal : (coreGraph cs.G cs.lsf).IsValid := coreGraph_isValid hG hF
  cases u with
  | insert e a b => trivial
  | delete e =>
    by_cases he : e ∈ cs.RF.F.E
    · simp only [inputCoreBatch, he, ↓reduceIte] at hOCB ⊢
      exact refineSplit_splitEndsExact hCoreVal hOCB.1.1.2.1 hOCB.2.choose
    · simp [inputCoreBatch, he, BatchSplitEndsExact]
  | split v v' St Sh =>
    simp only [inputCoreBatch] at hOCB ⊢
    exact refineSplit_splitEndsExact hCoreVal hOCB.1.1.2.1 hOCB.2.choose

private theorem canonStepCore_splitEndsExact {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} {ρ : Rotation cs.G} {σ : Rotation (cs.G.applyUpdate u)}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) (hr : RotationStep 2 u ρ σ) :
    BatchSplitEndsExact (coreGraph cs.G cs.lsf) (canonStepCore cs u) := by
  let cs' := compLSFStepSingle cs u
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hH : (cs.G.applyUpdate u).IsValid := hI'.hG_val
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  have hdec := compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩
  have hFE : cs'.RF.F.E ⊆ cs.RF.F.E := hdec.1
  have hFG : cs.RF.F.E ⊆ cs.G.E := hF.2.2.2.2.2.1
  have hFG' : cs'.RF.F.E ⊆ cs'.G.E := hF'.2.2.2.2.2.1
  have hFV : cs.RF.F.V = cs.G.V := hF.2.1
  have hFV' : cs'.RF.F.V = cs'.G.V := hF'.2.1
  let K := forestAfterInput cs.RF.F u
  have hK : K.IsForest := by
    cases u with
    | insert => exact hF.1
    | delete e => exact isForest_eraseEdge hF.1 e
    | split v v' St Sh => exact applyUpdate_split_isForest hF.1 (hFV ▸ hu.1) (hFV ▸ hu.2.1) St Sh
  have hKG : (cs.G.applyUpdate u).IsSubgraph K := by
    cases u with
    | insert e a b =>
      refine ⟨hFV.le, hFG.trans (Finset.subset_insert _ _), fun f hf => ?_⟩
      have hfe : f ≠ e := fun h => hu.1 (h ▸ hFG hf)
      have h0 := hF.2.2.2.2.2.2 f hf
      simp [MGraph.applyUpdate, Function.update_of_ne hfe, K, forestAfterInput, h0.1, h0.2]
    | delete e => exact ⟨hFV.le, Finset.erase_subset_erase e hFG, fun _ _ => ⟨rfl, rfl⟩⟩
    | split v v' St Sh =>
      refine ⟨?_, hFG, fun _ _ => ⟨rfl, rfl⟩⟩
      change insert v' cs.RF.F.V ⊆ insert v' cs.G.V; rw [hFV]
  have hKV : K.V = cs'.RF.F.V := by
    rw [hFV']; cases u with
    | insert => exact hFV
    | delete => exact hFV
    | split v v' St Sh => change insert v' cs.RF.F.V = insert v' cs.G.V; rw [hFV]
  have hKE : cs'.RF.F.E ⊆ K.E := by
    cases u with
    | insert => exact hFE
    | split => exact hFE
    | delete e =>
      intro f hf
      refine Finset.mem_erase.mpr ⟨?_, hFE hf⟩
      rintro rfl
      have := hFG' hf; change f ∈ cs.G.E.erase f at this; simp at this
  have hsub : K.IsSubgraph cs'.RF.F :=
    ⟨hKV.symm.le, hKE, fun f hf => let h := hKG.2.2 f (hKE hf); ⟨h.1.symm, h.2.symm⟩⟩
  let cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
  let Fc := cuts.foldl eraseForestEdge K
  have hFcE : Fc.E = cs'.RF.F.E := by
    simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
    exact Finset.sdiff_sdiff_eq_self hsub.2.1
  have hFcK : K.IsSubgraph Fc :=
    ⟨by simp [Fc, foldl_eraseForestEdge], by simp [Fc, foldl_eraseForestEdge],
      fun _ _ => by simp [Fc, foldl_eraseForestEdge]⟩
  have hEqF : GraphEq Fc cs'.RF.F :=
    ⟨by simp [Fc, foldl_eraseForestEdge]; exact hKV, hFcE, fun f hf => by
      have hsub' := hsub.2.2 f (hFcE ▸ hf)
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨hsub'.1.symm, hsub'.2.symm⟩⟩
  let L'' : LSF := ⟨cs'.lsf.T, ⟨Fc, cs'.RF.R⟩, cs'.lsf.wstr⟩
  have hL'' : L''.F.IsRootedSpanningForestOf (cs.G.applyUpdate u) :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  obtain ⟨hm, hmidF, _, hmR, h₀, _, _⟩ :=
    orderedCore_inputCoreBatch (last := L'') ρ σ hI.hG_val hH hF hL'' rfl hu hr (le_refl 2) hR hK
      hKG hFcK
  have hInEx := inputCoreBatch_splitEndsExact (last := L'') ρ σ hI.hG_val hH hF hL'' rfl hu hr hR
    hK hKG hFcK
  have hCut : cuts.foldl eraseForestEdge (inputMid cs u).F.F = L''.F.F := by rw [hmidF]; rfl
  have hMem : ∀ e ∈ cuts, e ∈ (inputMid cs u).F.F.E := fun e he => by
    rw [hmidF]; exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
  have hRelEx := releasesBatch_splitEndsExact σ hH cuts hm hL'' hmR hCut hMem
    (Finset.sort_nodup _ _)
  exact batchSplitEndsExact_append hInEx (batchSplitEndsExact_congr h₀.2.choose hRelEx)

/-- `canonCoreBatch cs U` satisfies `BatchSplitEndsExact` on `coreGraph cs.G cs.lsf`. -/
theorem canonCoreBatch_splitEndsExact {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {G : MGraph} {U : List Update}
    {ρ : Rotation G} {σ : Rotation (G.applyBatch U)} (hrot : RotationBatch 2 U ρ σ)
    (hU : G.BatchIsValid U) (cs : CompLSFState) (hS : cs.G = G)
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    BatchSplitEndsExact (coreGraph cs.G cs.lsf) (canonCoreBatch cs U) := by
  induction hrot generalizing cs with
  | nil => trivial
  | @cons G u rest ρ ρ' σ hs _ ih =>
    subst G
    obtain ⟨hI₀, h₀, _, _, _⟩ := orderedCore_canonStepCore hI hU.1 hs (le_refl 2)
    have hStepEx := canonStepCore_splitEndsExact hI hU.1 hs
    have hRestEx := ih hU.2 (compLSFStepSingle cs u) rfl hI₀
    exact batchSplitEndsExact_append hStepEx (batchSplitEndsExact_congr h₀.2.choose hRestEx)

/-- Restricting splits of a `BatchSplitEndsExact` core batch to a subgraph preserves
`BatchSplitEndsExact`. -/
theorem restrictSplits_splitEndsExact {C S : MGraph} {keep : Finset ℕ} {UC : List Update}
    (hCV : C.BatchIsValid UC) (hCEx : BatchSplitEndsExact C UC)
    (hSub : C.IsSubgraph S) (hV : S.V = C.V) (hE : S.E = keep)
    (hDisj : Disjoint keep (batchDeletes UC)) :
    BatchSplitEndsExact S (restrictSplits keep UC) := by
  induction UC generalizing C S with
  | nil => trivial
  | cons u rest ih =>
    have hcons : batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
      ext e; simp [mem_batchDeletes_iff]
    rw [hcons, Finset.disjoint_union_right] at hDisj
    obtain ⟨hDisj_u, hDisj_rest⟩ := hDisj
    cases u with
    | insert f a b =>
      have hSub' : (C.applyUpdate (.insert f a b)).IsSubgraph S := by
        refine ⟨hSub.1, hSub.2.1.trans (Finset.subset_insert f C.E), fun e he => ?_⟩
        have hne : e ≠ f := fun h => hCV.1.1 (h ▸ hSub.2.1 he)
        obtain ⟨ht, hh⟩ := hSub.2.2 e he
        exact ⟨ht.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne]),
          hh.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne])⟩
      exact ih hCV.2 hCEx hSub' hV hE hDisj_rest
    | delete f =>
      have hfNotKeep : f ∉ keep :=
        Finset.disjoint_right.mp hDisj_u ((mem_batchDeletes_iff [.delete f] f).mpr ⟨_, List.mem_cons_self, rfl⟩)
      have hSub' : (C.applyUpdate (.delete f)).IsSubgraph S :=
        ⟨hSub.1, fun e he => Finset.mem_erase.mpr ⟨fun h => hfNotKeep (h ▸ hE ▸ he), hSub.2.1 he⟩,
          fun e he => hSub.2.2 e he⟩
      exact ih hCV.2 hCEx hSub' hV hE hDisj_rest
    | split v v' St Sh =>
      refine ⟨fun e he => ?_, fun e he => ?_, ?_⟩
      · obtain ⟨heSt, heK⟩ := Finset.mem_inter.mp he
        have heS : e ∈ S.E := hE.symm ▸ heK
        exact ⟨heS, (hSub.2.2 e heS).1.trans (hCEx.1 e heSt).2⟩
      · obtain ⟨heSh, heK⟩ := Finset.mem_inter.mp he
        have heS : e ∈ S.E := hE.symm ▸ heK
        exact ⟨heS, (hSub.2.2 e heS).2.trans (hCEx.2.1 e heSh).2⟩
      · let uS := Update.split v v' (St ∩ keep) (Sh ∩ keep)
        have hS₁_V : (S.applyUpdate uS).V = (C.applyUpdate (.split v v' St Sh)).V := by
          change insert v' S.V = insert v' C.V; rw [hV]
        have hSub₁ : (C.applyUpdate (.split v v' St Sh)).IsSubgraph (S.applyUpdate uS) := by
          refine ⟨hS₁_V.le, hSub.2.1, fun e he => ?_⟩
          have heK : e ∈ keep := hE ▸ he
          obtain ⟨ht, hh⟩ := hSub.2.2 e he
          simp [uS, MGraph.applyUpdate, ht, hh, heK]
        exact ih hCV.2 hCEx.2.2 hSub₁ hS₁_V hE hDisj_rest

private theorem cast_rot_order_eq {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h; rfl

/-- Every output batch `info.U_S` of `stepBundleTree` satisfies `BatchSplitEndsExact`. -/
theorem stepBundleTree_U_S_splitEndsExact {depth vCap eCap : ℕ} {impl : SparsifyImpl}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hold : AsmBrModelFacts impl vCap eCap tr ord)
    (hBU : tr.cs.G.BatchIsValid U) (hord : OrderedBatch tr.cs.G U ord ord') :
    BatchSplitEndsExact tr.S_cur
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').U_S := by
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, hS, -, hSval, -⟩ := hold
  obtain ⟨ρ, σ, hρ, hσ, hrot⟩ := hord
  let cs_new := compLSFBatch tr.cs U
  let UC := canonCoreBatch tr.cs U
  have hUC_spec := canonCoreBatch_spec hI ρ σ hρ hσ hrot hBU
  have hUC_ex := canonCoreBatch_splitEndsExact hrot hBU tr.cs rfl hI
  have hI_new := compLSFBatch_inv hI hBU
  have hcsG : cs_new.G = tr.cs.G.applyBatch U := compLSFBatch_G tr.cs U
  have hOCB := hUC_spec.1 ρ (hcsG.symm ▸ σ) hI.hG_val (compLSF_RF_isRSF hI)
    hI_new.hG_val (compLSF_RF_isRSF hI_new) hρ (by rw [cast_rot_order_eq, hσ])
  set info := stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord'
  change BatchSplitEndsExact tr.S_cur (buildUSOrd UC U cs_new tr.S_cur _ _)
  unfold buildUSOrd
  set keepSet := ((tr.S_cur.E ∩ _) \ batchDeletes U) \ _
  set delList := ((tr.S_cur.E \ keepSet).sort (· ≤ ·)).map Update.delete
  set splitList := restrictSplits keepSet UC
  set insList := ((_ \ keepSet).sort (· ≤ ·)).map fun e =>
    Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e))
  have hDel_spec := applyUpdate_delete_list_spec hSval (Finset.sort_nodup (tr.S_cur.E \ keepSet) (· ≤ ·))
    (fun e he => Finset.sdiff_subset ((Finset.mem_sort (· ≤ ·)).mp he))
  have hS1_E : (tr.S_cur.applyBatch delList).E = keepSet := by
    rw [hDel_spec.2.2.1]; ext e
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_sort]
    constructor
    · rintro ⟨he, hnot⟩; by_contra hnk; exact hnot ⟨he, hnk⟩
    · intro heK
      have heP : e ∈ tr.S_cur.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).1
      exact ⟨heP, fun h => h.2 heK⟩
  have hS1_V : (tr.S_cur.applyBatch delList).V = (coreGraph tr.cs.G tr.cs.lsf).V :=
    hDel_spec.2.1.trans hS.2.1
  have hS1_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph (tr.S_cur.applyBatch delList) := by
    refine ⟨hS1_V.le, fun e he => ?_, fun e he => ?_⟩
    · have heP : e ∈ tr.S_cur.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hS1_E ▸ he)).1).1).1
      exact hS.2.2.2.1.2.1 heP
    · have heP : e ∈ tr.S_cur.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hS1_E ▸ he)).1).1).1
      have h1 := hDel_spec.2.2.2.1 e he
      have h2 := hS.2.2.2.1.2.2 e heP
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hDisj : Disjoint keepSet (batchDeletes UC) :=
    Finset.disjoint_left.mpr fun e heK heDel =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).2 (hUC_spec.2.2.2 heDel)
  have hDelEx : BatchSplitEndsExact tr.S_cur delList := batchSplitEndsExact_of_noSplit fun u hu => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu; trivial
  have hSpEx : BatchSplitEndsExact (tr.S_cur.applyBatch delList) splitList :=
    restrictSplits_splitEndsExact hOCB.1 hUC_ex hS1_sub hS1_V hS1_E hDisj
  have hInsEx : BatchSplitEndsExact ((tr.S_cur.applyBatch delList).applyBatch splitList) insList :=
    batchSplitEndsExact_of_noSplit fun u hu => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu; trivial
  exact batchSplitEndsExact_append (batchSplitEndsExact_append hDelEx hSpEx)
    (by rw [applyBatch_append]; exact hInsEx)

/-! ## 3. Word bounds for `BatchAt` buffers -/

private theorem vertices_subset_applyUpdate (G : MGraph) (u : Update) :
    G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert => exact Finset.Subset.rfl
  | delete => exact Finset.Subset.rfl
  | split v v' St Sh => exact Finset.subset_insert v' G.V

private theorem vertices_subset_applyBatch (G : MGraph) (U : List Update) :
    G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih => exact (vertices_subset_applyUpdate G u).trans (ih (G.applyUpdate u))

private theorem updateAt_len_ge_two {mem : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update}
    (h : UpdateAt mem a G u len) : 2 ≤ len := by
  cases u with
  | insert => rcases h with ⟨rfl, _⟩; omega
  | delete => rcases h with ⟨rfl, _⟩; omega
  | split => rcases h with ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ <;> omega

private theorem batchBodyAt_length_le_words {mem : ℕ → ℕ} :
    ∀ {a W : ℕ} {G : MGraph} {U : List Update}, BatchBodyAt mem a G U W → U.length ≤ W
  | _, _, _, [], _ => Nat.zero_le _
  | _, _, _, _ :: _, ⟨_, hle, hu, hrest⟩ => by
    have h2 := updateAt_len_ge_two hu
    have hr := batchBodyAt_length_le_words hrest
    simp only [List.length_cons]; omega

private def UpdateInsertLt (eCap : ℕ) : Update → Prop
  | .insert e _ _ => e < eCap
  | _ => True

private theorem updateAt_words_lt {mem : ℕ → ℕ} {a len vCap eCap B : ℕ} {G : MGraph} {u : Update}
    (hAt : UpdateAt mem a G u len) (hVal : G.UpdateIsValid u)
    (hV : ∀ v ∈ (G.applyUpdate u).V, v < vCap)
    (hE : ∀ e ∈ G.E, e < eCap)
    (hIns : UpdateInsertLt eCap u)
    (h4 : 4 < B) (hVc : vCap < B) (hEc : eCap < B) (hlen : len < B) :
    ∀ t < len, mem (a + t) < B := by
  cases u with
  | insert e x y =>
    rcases hAt with ⟨rfl, hL⟩
    have hx : x < vCap := hV x hVal.2.1
    have hy : y < vCap := hV y hVal.2.2
    have he : e < eCap := hIns
    intro t ht
    have hm := hL t ht
    interval_cases t <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm <;> omega
  | delete e =>
    rcases hAt with ⟨rfl, hL⟩
    have he : e < eCap := hE e hVal
    intro t ht
    have hm := hL t ht
    interval_cases t <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm <;> omega
  | split v v' St Sh =>
    have hv : v < vCap := hV v (Finset.mem_insert_of_mem hVal.1)
    have hv' : v' < vCap := hV v' (Finset.mem_insert_self v' G.V)
    rcases hAt with ⟨Lt, Lh, -, -, hLt, hLh, rfl, hL⟩ | ⟨Lt, Lh, -, -, hLt, hLh, rfl, hL⟩
    · intro t ht
      have hm := hL t (by simp; omega)
      by_cases ht5 : t < 5
      · interval_cases t <;>
          simp only [List.cons_append, List.nil_append,
            List.getElem_cons_zero, List.getElem_cons_succ] at hm <;> omega
      · by_cases htL : t < 5 + Lt.length
        · have hi : t - 5 < Lt.length := by omega
          have heq : ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[t]'(by simp; omega) = Lt[t - 5] := by
            rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
            simp
          rw [heq] at hm
          have he : Lt[t - 5] ∈ G.E := ((hLt _).mp (List.getElem_mem hi)).1
          have := hE _ he; omega
        · have hi : t - (5 + Lt.length) < Lh.length := by omega
          have heq : ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[t]'(by simp; omega) =
              Lh[t - (5 + Lt.length)] := by
            rw [List.getElem_append_right (by simp; omega)]
            congr 1; simp; omega
          rw [heq] at hm
          have he : Lh[t - (5 + Lt.length)] ∈ G.E := ((hLh _).mp (List.getElem_mem hi)).1
          have := hE _ he; omega
    · intro t ht
      have hm := hL t (by simp; omega)
      by_cases ht5 : t < 5
      · interval_cases t <;>
          simp only [List.cons_append, List.nil_append,
            List.getElem_cons_zero, List.getElem_cons_succ] at hm <;> omega
      · by_cases htL : t < 5 + Lt.length
        · have hi : t - 5 < Lt.length := by omega
          have heq : ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[t]'(by simp; omega) = Lt[t - 5] := by
            rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
            simp
          rw [heq] at hm
          have he : Lt[t - 5] ∈ G.E := ((hLt _).mp (List.getElem_mem hi)).1
          have := hE _ he; omega
        · have hi : t - (5 + Lt.length) < Lh.length := by omega
          have heq : ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[t]'(by simp; omega) =
              Lh[t - (5 + Lt.length)] := by
            rw [List.getElem_append_right (by simp; omega)]
            congr 1; simp; omega
          rw [heq] at hm
          have he : Lh[t - (5 + Lt.length)] ∈ G.E := ((hLh _).mp (List.getElem_mem hi)).1
          have := hE _ he; omega

private theorem batchBodyAt_words_lt {mem : ℕ → ℕ} {vCap eCap B : ℕ} :
    ∀ {a W : ℕ} {G : MGraph} {U : List Update},
      BatchBodyAt mem a G U W → G.BatchIsValid U →
      (∀ v ∈ (G.applyBatch U).V, v < vCap) →
      (∀ e ∈ G.E, e < eCap) →
      (∀ e x y, Update.insert e x y ∈ U → e < eCap) →
      4 < B → vCap < B → eCap < B → W < B →
      ∀ t < W, mem (a + t) < B
  | _, _, _, [], hW, _, _, _, _, _, _, _, _, t, ht => by rw [hW] at ht; omega
  | a, W, G, u :: rest, ⟨len, hle, hu, hrest⟩, ⟨hValU, hValR⟩, hV, hE, hIns, h4, hVc, hEc, hW, t, ht => by
    have hVu : ∀ v ∈ (G.applyUpdate u).V, v < vCap := fun v hv =>
      hV v (vertices_subset_applyBatch (G.applyUpdate u) rest hv)
    have hInsU : UpdateInsertLt eCap u := by
      cases u with
      | insert e x y => exact hIns e x y List.mem_cons_self
      | delete => trivial
      | split => trivial
    by_cases ht1 : t < len
    · exact updateAt_words_lt hu hValU hVu hE hInsU h4 hVc hEc (by omega) t ht1
    · have hE' : ∀ e ∈ (G.applyUpdate u).E, e < eCap := by
        intro e he; cases u with
        | insert f x y =>
          rcases Finset.mem_insert.mp he with rfl | heG
          · exact hIns e x y List.mem_cons_self
          · exact hE e heG
        | delete f => exact hE e (Finset.mem_of_mem_erase he)
        | split => exact hE e he
      have ih := batchBodyAt_words_lt hrest hValR hV hE'
        (fun e x y hm => hIns e x y (List.mem_cons_of_mem _ hm)) h4 hVc hEc (by omega)
        (t - len) (by omega)
      rwa [show a + len + (t - len) = a + t by omega] at ih

/-- Every word in a `BatchAt` buffer representing a valid batch whose vertices and edges stay
below `(vCap, eCap)` is strictly below `B`. -/
theorem batchAt_words_lt {mem : ℕ → ℕ} {a W vCap eCap B : ℕ} {G : MGraph} {U : List Update}
    (hAt : BatchAt mem a G U W) (hVal : G.BatchIsValid U)
    (hV : ∀ v ∈ (G.applyBatch U).V, v < vCap)
    (hE : ∀ e ∈ G.E, e < eCap)
    (hIns : ∀ e x y, Update.insert e x y ∈ U → e < eCap)
    (h4 : 4 < B) (hVc : vCap < B) (hEc : eCap < B) (hW : W < B) :
    ∀ t < W, mem (a + t) < B := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    have hlen := batchBodyAt_length_le_words hAt.2.2
    rw [Nat.add_zero, hAt.2.1]; omega
  · have hlt := batchBodyAt_words_lt hAt.2.2 hVal hV hE hIns h4 hVc hEc (by omega) (t - 1) (by omega)
    rwa [show a + 1 + (t - 1) = a + t by omega] at hlt

/-- Every `.insert e x y` in `(stepBundleTree ...).U_S` has `e < eCap` under `AsmBrModelFacts`. -/
theorem stepBundleTree_U_S_insert_lt {depth vCap eCap : ℕ} {impl : SparsifyImpl}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (_hold : AsmBrModelFacts impl vCap eCap tr ord)
    (hnew : AsmBrModelFacts impl vCap eCap
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state ord')
    (_hBU : tr.cs.G.BatchIsValid U) (_hord : OrderedBatch tr.cs.G U ord ord')
    {e x y : ℕ} (hmem : Update.insert e x y ∈
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').U_S) :
    e < eCap := by
  have hE' := asmBr_newOut_lt (fun _ => canonicalSparsify impl) hnew
  have hbeq := outStep_batch_eq (fun _ => canonicalSparsify impl) tr U ord ord'
  rw [hbeq] at hmem
  unfold outInsBatch at hmem
  simp only [List.mem_append, List.mem_map] at hmem
  rcases hmem with (⟨_, _, h⟩ | hsp) | ⟨e', he', h⟩
  · cases h
  · exact False.elim (restrictSplits_not_inserts hsp e rfl)
  · cases h
    have heNew : e ∈ (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state.S_cur.E :=
      (outStep_newE (fun _ => canonicalSparsify impl) tr U ord ord' e).mpr (Or.inr he')
    exact hE' e heNew

/-! ## 4. Relocation of `SparseCoreUpdateOutFootAt` across `shiftProgramProcs` -/

/-- Relocation of `SparseCoreUpdateOutFootAt` across `shiftProgramProcs`. -/
theorem sparseCoreUpdateOutFootAt_shift {w L depth k M N vCap eCap capExp edMul offset : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {Q p : Program} {op : ℕ → ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (h : SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R Q op) :
    SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p (fun i => offset + op i) := by
  refine ⟨?_⟩
  dsimp only
  intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hpost, hfchg, hplace, hresp, hcost⟩ :=
    h.op0_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  have hlen : op 0 < Q.procs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
  have hbe : Q.procs[op 0] = body := by
    rw [List.getElem?_eq_getElem hlen] at hbody
    exact Option.some.inj hbody
  have hproc : p.procs[offset + op 0]? = some (shiftProcIds offset body) := by
    simpa [shiftProgramProcs, hbe] using hp (op 0) (by simp [shiftProgramProcs, hlen])
  exact ⟨shiftProcIds offset body, hproc, o, st', c, x',
    runs_shiftProcIds hp hrun, hrep', hpost, hfchg, hplace, hresp, hcost⟩

/-- Relocation of `SparseCoreReembPlaceAt` across `shiftProgramProcs`. -/
theorem sparseCoreReembPlaceAt_shift {w L depth k M N vCap eCap capExp offset : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {Q p : Program} {op : ℕ → ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (h : SparseCoreReembPlaceAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R Q op) :
    SparseCoreReembPlaceAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p (fun i => offset + op i) := by
  refine ⟨?_⟩
  dsimp only
  intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  obtain ⟨body, hbody, o, st', c, hrun, hplace⟩ :=
    h.op0_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  have hlen : op 0 < Q.procs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
  have hbe : Q.procs[op 0] = body := by
    rw [List.getElem?_eq_getElem hlen] at hbody
    exact Option.some.inj hbody
  have hproc : p.procs[offset + op 0]? = some (shiftProcIds offset body) := by
    simpa [shiftProgramProcs, hbe] using hp (op 0) (by simp [shiftProgramProcs, hlen])
  exact ⟨shiftProcIds offset body, hproc, o, st', c, runs_shiftProcIds hp hrun, hplace⟩

end MinCostFlow.SparseCore.Program
