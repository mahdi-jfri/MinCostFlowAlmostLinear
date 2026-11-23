module

public import MinCostFlow.SparseCore.CanonCoreSpec
import Mathlib.Tactic.Linarith

/-!
# Canonical Split List Model and Memory Layout (`CompSplitListModel`)

Defines the exact per-branch split list `canonSplitList cs U` matching `canonCoreBatch cs U`
(`SparseCore/CanonCoreDefs.lean`), its Word-RAM memory predicate `CompSplitListAt` (parallel to
`CompFamilyChgAt` in `AssemblyTopIface.lean`), and the mathematical foundation for computing it in
`O((|D| + 1) log n)` time per update via reverse Union-Find:

1. `CompSplitEntry` (`isRelease`, `edge`, `kept`, `fresh`), `canonStepSplits`, `canonSplitList`,
   and `canonSplitList_eq_coreSplits` proving exact 1-to-1 correspondence with the `.split`
   entries of `canonCoreBatch cs U`.
2. `SplitEntriesAt`, `CompSplitListAt`, and `compSplitListAt_congr` (frame/locality).
3. `canonRoots_step_eq`: proves that iterating `canonRoots` along any sequence of forest-edge
   cuts is history-independent (`R_i = canonRoots F_i old final`), and `canonCutPair_eq_mergePair`:
   proves that each cut's `(kept, fresh)` pair is determined solely by `(oldRoot, minFinal)` of
   its two child components `A_i, B_i` in the forest `F_i` after the cut.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Abstract canonical split list matching `canonCoreBatch` -/

/-- One split entry in the canonical core batch of a branch:
* `isRelease = false`: the input update's own split (`edge = 0`, for a deleted forest edge or a
  vertex split);
* `isRelease = true`: the core split for releasing forest edge `edge`.
`kept` is the root keeping its name and `fresh` is the canonical new root (`canonPick`). -/
structure CompSplitEntry where
  isRelease : Bool
  edge : ℕ
  kept : ℕ
  fresh : ℕ
  deriving DecidableEq

/-- Input-edit split entry (at most one) corresponding to `inputCoreBatch cs u`. -/
noncomputable def inputSplitEntries (cs : CompLSFState) (u : Update) : List CompSplitEntry :=
  let M := inputMid cs u
  match u with
  | .insert _ _ _ => []
  | .delete e =>
    if e ∈ cs.RF.F.E then
      [⟨false, 0, cs.RF.root (cs.RF.F.tail e), newRoot M.F.R cs.RF.R⟩]
    else []
  | .split v _ _ _ =>
    [⟨false, 0, cs.RF.root v, newRoot M.F.R cs.RF.R⟩]

/-- Release split entries corresponding to `releasesBatch G final L cuts`. -/
noncomputable def releasesSplitEntries (final : Finset ℕ) (L : LSF) :
    List ℕ → List CompSplitEntry
  | [] => []
  | e :: cuts =>
    let K := eraseForestEdge L.F.F e
    let L' : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R final⟩, L.wstr⟩
    ⟨true, e, L.F.root (L.F.F.tail e), newRoot L'.F.R L.F.R⟩ ::
      releasesSplitEntries final L' cuts

/-- Canonical split list for a single input update `u` on `cs`. -/
noncomputable def canonStepSplits (cs : CompLSFState) (u : Update) : List CompSplitEntry :=
  inputSplitEntries cs u ++
    releasesSplitEntries (compLSFStepSingle cs u).RF.R (inputMid cs u)
      (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))

/-- Canonical split list for a batch `U` on `cs`, in exact `canonCoreBatch cs U` order. -/
noncomputable def canonSplitList : CompLSFState → List Update → List CompSplitEntry
  | _, [] => []
  | cs, u :: U => canonStepSplits cs u ++ canonSplitList (compLSFStepSingle cs u) U

/-- Extract the `(kept, fresh)` pairs of all `.split` updates in a core batch. -/
def coreBatchSplitPairs (U : List Update) : List (ℕ × ℕ) :=
  U.filterMap fun
    | .split v v' _ _ => some (v, v')
    | _ => none

lemma coreBatchSplitPairs_append (U₁ U₂ : List Update) :
    coreBatchSplitPairs (U₁ ++ U₂) = coreBatchSplitPairs U₁ ++ coreBatchSplitPairs U₂ :=
  List.filterMap_append

lemma releasesSplitEntries_eq_coreSplits (G : MGraph) (final : Finset ℕ) (L : LSF)
    (cuts : List ℕ) :
    coreBatchSplitPairs (releasesBatch G final L cuts) =
      (releasesSplitEntries final L cuts).map fun s => (s.kept, s.fresh) := by
  induction cuts generalizing L with
  | nil => rfl
  | cons e rest ih =>
    simp only [releasesBatch, releasesSplitEntries, coreBatchSplitPairs, refineSplit,
      List.filterMap_cons, List.map_cons]
    exact congrArg (List.cons _) (ih _)

lemma inputSplitEntries_eq_coreSplits (cs : CompLSFState) (u : Update) :
    coreBatchSplitPairs (inputCoreBatch cs u) =
      (inputSplitEntries cs u).map fun s => (s.kept, s.fresh) := by
  cases u with
  | insert e a b => rfl
  | delete e =>
    by_cases h : e ∈ cs.RF.F.E <;>
      simp [inputCoreBatch, inputSplitEntries, coreBatchSplitPairs, refineSplit, h]
  | split v v' At Ah =>
    simp [inputCoreBatch, inputSplitEntries, coreBatchSplitPairs, refineSplit]

/-- **Exact correspondence with `canonCoreBatch`**: the `(kept, fresh)` pairs in
`canonSplitList cs U` are identically the `.split` updates of `canonCoreBatch cs U` in order. -/
theorem canonSplitList_eq_coreSplits (cs : CompLSFState) (U : List Update) :
    coreBatchSplitPairs (canonCoreBatch cs U) =
      (canonSplitList cs U).map fun s => (s.kept, s.fresh) := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    simp only [canonCoreBatch, canonStepCore, canonSplitList, canonStepSplits,
      coreBatchSplitPairs_append, List.map_append, inputSplitEntries_eq_coreSplits,
      releasesSplitEntries_eq_coreSplits, ih]

lemma releasesSplitEntries_edges (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    (releasesSplitEntries final L cuts).map CompSplitEntry.edge = cuts ∧
    ∀ s ∈ releasesSplitEntries final L cuts, s.isRelease = true := by
  induction cuts generalizing L with
  | nil => exact ⟨rfl, fun _ h => by simp [releasesSplitEntries] at h⟩
  | cons e rest ih =>
    let F' := eraseForestEdge L.F.F e
    obtain ⟨h1, h2⟩ := ih
      { T := L.T, F := { F := F', R := canonRoots F' L.F.R final }, wstr := L.wstr }
    refine ⟨by simp [releasesSplitEntries, F', h1], fun s hs => ?_⟩
    simp only [releasesSplitEntries, List.mem_cons] at hs
    rcases hs with rfl | hs
    · rfl
    · exact h2 s hs

lemma releasesSplitEntries_length (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    (releasesSplitEntries final L cuts).length = cuts.length := by
  induction cuts generalizing L with
  | nil => rfl
  | cons e rest ih => simp [releasesSplitEntries, ih]

/-- For each update `u`, the `isRelease = true` entries of `canonStepSplits cs u` list the
released forest edges `(forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E` in
strictly increasing order. -/
theorem canonStepSplits_releases_edges (cs : CompLSFState) (u : Update) :
    ((canonStepSplits cs u).filter CompSplitEntry.isRelease).map CompSplitEntry.edge =
      ((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·) := by
  have h1 : (inputSplitEntries cs u).filter CompSplitEntry.isRelease = [] := by
    cases u with
    | insert _ _ _ => rfl
    | delete e => by_cases h : e ∈ cs.RF.F.E <;> simp [inputSplitEntries, h]
    | split _ _ _ _ => rfl
  obtain ⟨he, hrel⟩ := releasesSplitEntries_edges (compLSFStepSingle cs u).RF.R (inputMid cs u)
    (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))
  simp only [canonStepSplits, List.filter_append, h1, List.nil_append]
  rw [List.filter_eq_self.mpr hrel, he]

/-! ## 2. Concrete Word-RAM memory layout `CompSplitListAt` -/

/-- Word length of a single branch's encoded split list `L`: `1` count word plus `4` words per
split entry `[isRelease, edge, kept, fresh]`. -/
def splitEntriesWords (L : List CompSplitEntry) : ℕ := 1 + 4 * L.length

/-- Concrete layout of one branch's split list `L` at address `p`:
* `mem p = L.length`
* for `i < L.length`, `[p + 1 + 4 * i .. p + 1 + 4 * i + 3]` stores
  `[if L[i].isRelease then 1 else 0, L[i].edge, L[i].kept, L[i].fresh]`. -/
def SplitEntriesAt (mem : ℕ → ℕ) (p : ℕ) (L : List CompSplitEntry) : Prop :=
  mem p = L.length ∧
  ∀ i (hi : i < L.length),
    mem (p + 1 + 4 * i) = (if L[i].isRelease then 1 else 0) ∧
    mem (p + 1 + 4 * i + 1) = L[i].edge ∧
    mem (p + 1 + 4 * i + 2) = L[i].kept ∧
    mem (p + 1 + 4 * i + 3) = L[i].fresh

/-- Concrete memory layout of P4's per-branch canonical split lists (parallel to
`CompFamilyChgAt` in `AssemblyTopIface.lean`):
* `[fSplitPtr, fSplitPtr + k)` is a table of `k` pointers `spPtr_j = mem (fSplitPtr + j)`;
* for each `j < k`, `spPtr_j` holds `SplitEntriesAt mem spPtr_j (canonSplitList (cfs j) U)`;
* the pointer table and every branch's split list lie inside `[fSplitPtr, fSplitEnd)` and every
  word in `[fSplitPtr, fSplitEnd)` is `< 2 ^ w`. -/
def CompSplitListAt (w k : ℕ) (mem : ℕ → ℕ) (fSplitPtr fSplitEnd : ℕ)
    (cfs : ℕ → CompLSFState) (U : List Update) : Prop :=
  fSplitPtr + k ≤ fSplitEnd ∧
  (∀ a, fSplitPtr ≤ a → a < fSplitEnd → mem a < 2 ^ w) ∧
  ∀ j < k,
    let spPtr := mem (fSplitPtr + j)
    let L := canonSplitList (cfs j) U
    SplitEntriesAt mem spPtr L ∧
    fSplitPtr + k ≤ spPtr ∧
    spPtr + splitEntriesWords L ≤ fSplitEnd

/-- `CompSplitListAt` depends only on memory inside `[fSplitPtr, fSplitEnd)`. -/
theorem compSplitListAt_congr {w k : ℕ} {mem₁ mem₂ : ℕ → ℕ} {fSplitPtr fSplitEnd : ℕ}
    {cfs : ℕ → CompLSFState} {U : List Update}
    (hag : ∀ a, fSplitPtr ≤ a → a < fSplitEnd → mem₁ a = mem₂ a)
    (h : CompSplitListAt w k mem₁ fSplitPtr fSplitEnd cfs U) :
    CompSplitListAt w k mem₂ fSplitPtr fSplitEnd cfs U := by
  rcases h with ⟨hlo, hlt, hbr⟩
  refine ⟨hlo, fun a ha1 ha2 => by rw [← hag a ha1 ha2]; exact hlt a ha1 ha2, fun j hj => ?_⟩
  obtain ⟨⟨hlen, hent⟩, hptrLo, hptrHi⟩ := hbr j hj
  have hptr_eq : mem₂ (fSplitPtr + j) = mem₁ (fSplitPtr + j) :=
    (hag (fSplitPtr + j) (by omega) (by omega)).symm
  dsimp only
  rw [hptr_eq]
  set p := mem₁ (fSplitPtr + j)
  set L := canonSplitList (cfs j) U
  have hw_def : splitEntriesWords L = 1 + 4 * L.length := rfl
  refine ⟨⟨(hag p (by omega) (by omega)).symm.trans hlen, fun i hi => ?_⟩, hptrLo, hptrHi⟩
  obtain ⟨e0, e1, e2, e3⟩ := hent i hi
  exact ⟨(hag (p + 1 + 4 * i) (by omega) (by omega)).symm.trans e0,
    (hag (p + 1 + 4 * i + 1) (by omega) (by omega)).symm.trans e1,
    (hag (p + 1 + 4 * i + 2) (by omega) (by omega)).symm.trans e2,
    (hag (p + 1 + 4 * i + 3) (by omega) (by omega)).symm.trans e3⟩

/-! ## 3. History-independence of `canonRoots` and reverse-merge characterization -/

/-- The canonical root choice on a component `A` depends only on `old` and `final`:
if `F₁` is a spanning subforest of `F₀` (e.g. after cutting one forest edge) and `F₀` has
canonical roots `R₀ = canonRoots F₀ old final`, then `canonRoots F₁ R₀ final = canonRoots F₁ old final`. -/
theorem canonRoots_idem_of_subgraph {G F₀ F₁ : MGraph} {final : RootedForest} {old : Finset ℕ}
    (hF₀ : F₀.IsForest) (hV₀ : F₀.V = G.V) (hF₀G : G.IsSubgraph F₀)
    (_hF₁ : F₁.IsForest) (hV₁ : F₁.V = G.V) (_hF₁G : G.IsSubgraph F₁)
    (hsub01 : F₀.IsSubgraph F₁) (hsub1f : F₁.IsSubgraph final.F)
    (hfinal : final.IsRootedSpanningForestOf G)
    (hOld : old ⊆ final.R)
    (hSep₀ : ∀ r ∈ old, ∀ s ∈ old, F₀.Connected r s → r = s) :
    canonRoots F₁ (canonRoots F₀ old final.R) final.R = canonRoots F₁ old final.R := by
  have hsub0f : F₀.IsSubgraph final.F := by
    refine ⟨hsub1f.1.trans hsub01.1, hsub1f.2.1.trans hsub01.2.1, fun e he => ?_⟩
    have h1 := hsub1f.2.2 e he
    have h0 := hsub01.2.2 e (hsub1f.2.1 he)
    exact ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩
  have hAvail : ∀ F : MGraph, F.V = G.V → F.IsSubgraph final.F →
      ∀ A ∈ components F, (A ∩ final.R).Nonempty := by
    intro F hVF hFf A hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 v (hVF ▸ hv)
    exact ⟨r, Finset.mem_inter.mpr
      ⟨mem_compOf_iff.mpr ⟨hVF.symm ▸ hfinal.2.2.1 hr, connected_of_subgraph hFf hc⟩, hr⟩⟩
  set R₀ := canonRoots F₀ old final.R
  obtain ⟨hOld_R₀, hR₀_fin, hRF₀⟩ := canonRoots_spec hF₀ hV₀ hF₀G hfinal hsub0f hOld hSep₀
  -- Every component `A` of `F₁` is contained in a unique component `P` of `F₀`, and
  -- `canonPick R₀ final.R A = canonPick old final.R A`.
  have hpick_eq : ∀ A ∈ components F₁, canonPick R₀ final.R A = canonPick old final.R A := by
    intro A hA
    obtain ⟨v, hvF₁, rfl⟩ := Finset.mem_image.mp hA
    have hvG : v ∈ G.V := hV₁ ▸ hvF₁
    have hvF₀ : v ∈ F₀.V := hV₀.symm ▸ hvG
    set P := compOf F₀ v
    have hP_mem : P ∈ components F₀ := compOf_mem_components hvF₀
    have hAP : compOf F₁ v ⊆ P := fun u hu => by
      obtain ⟨huF₁, hc1⟩ := mem_compOf_iff.mp hu
      exact mem_compOf_iff.mpr ⟨hV₀.symm ▸ hV₁ ▸ huF₁, connected_of_subgraph hsub01 hc1⟩
    -- `P ∩ R₀` has the unique element `rP := canonPick old final.R P`
    set rP := canonPick old final.R P
    have hrP_mem : rP ∈ R₀ := Finset.mem_image_of_mem _ hP_mem
    have hrP_P : rP ∈ P := by
      by_cases ho : (P ∩ old).Nonempty
      · simp only [rP, canonPick, ho, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ ho)).1
      · have hf := hAvail F₀ hV₀ hsub0f P hP_mem
        simp only [rP, canonPick, ho, hf, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ hf)).1
    have hPR₀ : ∀ r ∈ P ∩ R₀, r = rP := fun r hr => by
      obtain ⟨hrP, hrR₀⟩ := Finset.mem_inter.mp hr
      obtain ⟨r_u, _, huniq⟩ := hRF₀.2.2.2.1 v hvG
      have h1 : r = r_u := huniq r ⟨hrR₀, (mem_compOf_iff.mp hrP).2⟩
      have h2 : rP = r_u := huniq rP ⟨hrP_mem, (mem_compOf_iff.mp hrP_P).2⟩
      exact h1.trans h2.symm
    have hAf : (compOf F₁ v ∩ final.R).Nonempty := hAvail F₁ hV₁ hsub1f _ hA
    by_cases hAo : (compOf F₁ v ∩ old).Nonempty
    · -- `A` contains an old root `r₀`: then `r₀ ∈ P ∩ old`, so `rP = r₀`, and `A ∩ R₀ = {r₀} = A ∩ old`.
      have hr₀_ex := hAo
      obtain ⟨r₀, hr₀⟩ := hr₀_ex
      obtain ⟨hr₀A, hr₀old⟩ := Finset.mem_inter.mp hr₀
      have hPo : (P ∩ old).Nonempty := ⟨r₀, Finset.mem_inter.mpr ⟨hAP hr₀A, hr₀old⟩⟩
      have hrP_eq : rP = r₀ := by
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hPo)
        have hc : F₀.Connected ((P ∩ old).min' hPo) r₀ :=
          connected_trans (connected_symm (mem_compOf_iff.mp hm.1).2)
            (mem_compOf_iff.mp (hAP hr₀A)).2
        simpa only [rP, canonPick, hPo, ↓reduceDIte] using hSep₀ _ hm.2 r₀ hr₀old hc
      have hAR₀ : (compOf F₁ v ∩ R₀).Nonempty :=
        ⟨r₀, Finset.mem_inter.mpr ⟨hr₀A, hOld_R₀ hr₀old⟩⟩
      have hmin1 : (compOf F₁ v ∩ R₀).min' hAR₀ = r₀ := by
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hAR₀)
        exact (hPR₀ _ (Finset.mem_inter.mpr ⟨hAP hm.1, hm.2⟩)).trans hrP_eq
      have hmin2 : (compOf F₁ v ∩ old).min' hAo = r₀ := by
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hAo)
        have hc : F₀.Connected ((compOf F₁ v ∩ old).min' hAo) r₀ :=
          connected_trans (connected_symm (mem_compOf_iff.mp (hAP hm.1)).2)
            (mem_compOf_iff.mp (hAP hr₀A)).2
        exact hSep₀ _ hm.2 r₀ hr₀old hc
      simp only [canonPick, hAR₀, hAo, ↓reduceDIte, hmin1, hmin2]
    · -- `A` contains no old root.
      by_cases hAR₀ : (compOf F₁ v ∩ R₀).Nonempty
      · -- `rP ∈ A`: then `P` cannot contain any old root (otherwise `rP ∈ old ∩ A`), so `rP = min(P ∩ final.R)`,
        -- and since `rP ∈ A ⊆ P`, `rP = min(A ∩ final.R)`!
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hAR₀)
        have hmin1 : (compOf F₁ v ∩ R₀).min' hAR₀ = rP :=
          hPR₀ _ (Finset.mem_inter.mpr ⟨hAP hm.1, hm.2⟩)
        have hrP_A : rP ∈ compOf F₁ v := hmin1 ▸ hm.1
        have hPo_empty : ¬ (P ∩ old).Nonempty := by
          intro hPo
          have hmP := Finset.mem_inter.mp (Finset.min'_mem _ hPo)
          have hrP_old : rP ∈ old := by simpa only [rP, canonPick, hPo, ↓reduceDIte] using hmP.2
          exact hAo ⟨rP, Finset.mem_inter.mpr ⟨hrP_A, hrP_old⟩⟩
        have hPf : (P ∩ final.R).Nonempty := hAvail F₀ hV₀ hsub0f P hP_mem
        have hrP_minP : rP = (P ∩ final.R).min' hPf := by
          simp only [rP, canonPick, hPo_empty, hPf, ↓reduceDIte]
        have hle1 : (compOf F₁ v ∩ final.R).min' hAf ≤ rP :=
          Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hrP_A, hR₀_fin hrP_mem⟩)
        have hle2 : rP ≤ (compOf F₁ v ∩ final.R).min' hAf := by
          rw [hrP_minP]
          have hmA := Finset.mem_inter.mp (Finset.min'_mem _ hAf)
          exact Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hAP hmA.1, hmA.2⟩)
        have heq : rP = (compOf F₁ v ∩ final.R).min' hAf := le_antisymm hle2 hle1
        simp only [canonPick, hAR₀, hAo, hAf, ↓reduceDIte, hmin1, heq]
      · simp only [canonPick, hAR₀, hAo, hAf, ↓reduceDIte]
  unfold canonRoots
  exact Finset.image_congr hpick_eq

/-- Algebraic 4-case merge rule computing `(kept, fresh)` from `(oldA, minA)` and `(oldB, minB)`
of the two child components `A, B` formed by cutting a forest edge:
`oldA = some r` means `r` is the unique old root in `A`, and `minA = min(A ∩ final)`. -/
def mergeSplitPair (oldA : Option ℕ) (minA : ℕ) (oldB : Option ℕ) (minB : ℕ) : ℕ × ℕ :=
  match oldA, oldB with
  | some r, _ => (r, minB)
  | none, some r => (r, minA)
  | none, none => if minA ≤ minB then (minA, minB) else (minB, minA)

/-- **Reverse-merge pair theorem**: when cutting a forest edge splits a component `P = A ∪ B`
(disjoint union of two components `A, B` of the cut forest `F₁`, with at most one old root in
`P` and `A ∩ final, B ∩ final` both nonempty), the canonical kept root `canonPick old final P`
and the canonical new root `newRoot (canonRoots F₁ (canonRoots F₀ old final) final) (canonRoots F₀ old final)`
are given verbatim by `mergeSplitPair` on `(oldRoot A, min(A ∩ final))` and `(oldRoot B, min(B ∩ final))`. -/
theorem mergeSplitPair_eq_canon {A B old final : Finset ℕ}
    (hDisj : Disjoint A B)
    (hAf : (A ∩ final).Nonempty) (hBf : (B ∩ final).Nonempty)
    (_hOldSub : old ⊆ final)
    (hAtMostOne : ∀ r ∈ (A ∪ B) ∩ old, ∀ s ∈ (A ∪ B) ∩ old, r = s) :
    let oldA : Option ℕ := open Classical in if h : (A ∩ old).Nonempty then some ((A ∩ old).min' h) else none
    let oldB : Option ℕ := open Classical in if h : (B ∩ old).Nonempty then some ((B ∩ old).min' h) else none
    let minA := (A ∩ final).min' hAf
    let minB := (B ∩ final).min' hBf
    let pA := canonPick old final A
    let pB := canonPick old final B
    let pP := canonPick old final (A ∪ B)
    mergeSplitPair oldA minA oldB minB =
      (pP, if pA = pP then pB else pA) := by
  classical
  intro oldA oldB minA minB pA pB pP
  have hmin_ne : minA ≠ minB := fun h => by
    dsimp only [minA, minB] at h
    exact Finset.disjoint_left.mp hDisj (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1
      (h ▸ (Finset.mem_inter.mp (Finset.min'_mem _ hBf)).1)
  have hPf : ((A ∪ B) ∩ final).Nonempty :=
    ⟨minA, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1,
      (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).2⟩⟩
  by_cases hAo : (A ∩ old).Nonempty
  · have hBo : ¬ (B ∩ old).Nonempty := fun hBo => by
      obtain ⟨rA, hrA⟩ := hAo; obtain ⟨rB, hrB⟩ := hBo
      have hrA' : rA ∈ (A ∪ B) ∩ old := Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hrA).1, (Finset.mem_inter.mp hrA).2⟩
      have hrB' : rB ∈ (A ∪ B) ∩ old := Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hrB).1, (Finset.mem_inter.mp hrB).2⟩
      have heq := hAtMostOne rA hrA' rB hrB'
      exact Finset.disjoint_left.mp hDisj (Finset.mem_inter.mp hrA).1 (heq ▸ (Finset.mem_inter.mp hrB).1)
    have hPo : ((A ∪ B) ∩ old).Nonempty := by
      obtain ⟨rA, hrA⟩ := hAo
      exact ⟨rA, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hrA).1,
        (Finset.mem_inter.mp hrA).2⟩⟩
    have hmin_eq : ((A ∪ B) ∩ old).min' hPo = (A ∩ old).min' hAo := by
      have hm1 := Finset.min'_mem _ hPo
      have hm2 := Finset.mem_inter.mp (Finset.min'_mem _ hAo)
      exact hAtMostOne _ hm1 _ (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hm2.1, hm2.2⟩)
    simp only [oldA, oldB, minB, pA, pB, pP, canonPick, hAo, hBo, hPo, hBf, ↓reduceDIte,
      hmin_eq, mergeSplitPair, ↓reduceIte]
  · by_cases hBo : (B ∩ old).Nonempty
    · have hPo : ((A ∪ B) ∩ old).Nonempty := by
        obtain ⟨rB, hrB⟩ := hBo
        exact ⟨rB, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hrB).1,
          (Finset.mem_inter.mp hrB).2⟩⟩
      have hmin_eq : ((A ∪ B) ∩ old).min' hPo = (B ∩ old).min' hBo := by
        have hm1 := Finset.min'_mem _ hPo
        have hm2 := Finset.mem_inter.mp (Finset.min'_mem _ hBo)
        exact hAtMostOne _ hm1 _ (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hm2.1, hm2.2⟩)
      have hne_AB : (A ∩ final).min' hAf ≠ (B ∩ old).min' hBo := fun h =>
        Finset.disjoint_left.mp hDisj (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1
          (h ▸ (Finset.mem_inter.mp (Finset.min'_mem _ hBo)).1)
      simp only [oldA, oldB, minA, pA, pB, pP, canonPick, hAo, hBo, hPo, hAf, ↓reduceDIte,
        hmin_eq, mergeSplitPair, hne_AB, ↓reduceIte]
    · have hPo : ¬ ((A ∪ B) ∩ old).Nonempty := by
        rintro ⟨r, hr⟩
        obtain ⟨hrU, hro⟩ := Finset.mem_inter.mp hr
        rcases Finset.mem_union.mp hrU with hA | hB
        · exact hAo ⟨r, Finset.mem_inter.mpr ⟨hA, hro⟩⟩
        · exact hBo ⟨r, Finset.mem_inter.mpr ⟨hB, hro⟩⟩
      have hminP : ((A ∪ B) ∩ final).min' hPf = min ((A ∩ final).min' hAf) ((B ∩ final).min' hBf) := by
        apply le_antisymm
        · refine le_min ?_ ?_
          · have hm := Finset.mem_inter.mp (Finset.min'_mem _ hAf)
            exact Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hm.1, hm.2⟩)
          · have hm := Finset.mem_inter.mp (Finset.min'_mem _ hBf)
            exact Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hm.1, hm.2⟩)
        · have hm := Finset.mem_inter.mp (Finset.min'_mem _ hPf)
          rcases Finset.mem_union.mp hm.1 with hA | hB
          · exact le_trans (min_le_left _ _) (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hA, hm.2⟩))
          · exact le_trans (min_le_right _ _) (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hB, hm.2⟩))
      simp only [oldA, oldB, minA, minB, pA, pB, pP, canonPick, hAo, hBo, hPo, hAf, hBf, hPf,
        ↓reduceDIte, hminP, mergeSplitPair]
      by_cases hle : (A ∩ final).min' hAf ≤ (B ∩ final).min' hBf
      · simp [hle]
      · have hlt : (B ∩ final).min' hBf ≤ (A ∩ final).min' hAf := by omega
        have hne : (A ∩ final).min' hAf ≠ (B ∩ final).min' hBf := hmin_ne
        simp [hle, min_eq_right hlt, hne]

end

end MinCostFlow.SparseCore.Program
