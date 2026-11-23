module

public import WordRAM.Contract
public import MinCostFlow.ExpanderDecomp.DecompModel
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.ProgCloud
public import MinCostFlow.ExpanderDecomp.ProgRelabel
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Memory Layouts and Slice Lemmas for `OneShot` and `Core` Programs

Defines the shared memory representations used by the Word-RAM implementations of `OneShot`
(`OneShotProg*.lean`) and `Core` (`CoreProg*.lean`), reusing `CoreOutAt`, `RouteOutAt`,
`routeOrCutContract`, `outerCoreContract`, and `readGraph` from `OuterProgContracts.lean`:

* `CoreParamsAt` / `coreParamsSize`: read-only table storing `(N, L, Δ, r)`, `P(0..r)`,
  `D(0..r)`, and `N^0..N^r`.
* `VertsAt`: sorted vertex list `X.sort (· ≤ ·)` of length `|X|` in contiguous memory, with
  zero-copy slice lemmas for `blockSet`, `fullVerts`, and `leftoverVerts` (`vertsAt_blockSet`,
  `vertsAt_fullVerts`, `vertsAt_leftoverVerts`) and filter-preserves-sort lemmas
  (`filter_sort_eq_sort_sdiff`, `filter_sort_eq_sort_inter`, `sort_range_eq_list_range`).
* `NodupVertsAt`: duplicate-free vertex list layout, matching `CoreOutAt` (`OuterProgContracts`).
* `isCloudExpander_progCloud`: bridges `ProgCloud.cloud` directly to `IsCloudExpander`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Memory Layouts -/

/-- Read-only parameter table for `CoreParams` up to level `r`:
* `pAddr + 0..3`: `N, L, Δ, r`;
* `pAddr + 4 + j` (`j ≤ r`): `cp.P j`;
* `pAddr + 5 + r + j` (`j ≤ r`): `cp.D j`;
* `pAddr + 6 + 2 * r + j` (`j ≤ r`): `cp.N ^ j`. -/
def CoreParamsAt (mem : ℕ → ℕ) (pAddr : ℕ) (cp : CoreParams) (r : ℕ) : Prop :=
  mem pAddr = cp.N ∧
  mem (pAddr + 1) = cp.L ∧
  mem (pAddr + 2) = cp.Δ ∧
  mem (pAddr + 3) = r ∧
  (∀ j ≤ r, mem (pAddr + 4 + j) = cp.P j) ∧
  (∀ j ≤ r, mem (pAddr + 5 + r + j) = cp.D j) ∧
  (∀ j ≤ r, mem (pAddr + 6 + 2 * r + j) = cp.N ^ j)

/-- Size in words of a `CoreParamsAt` table for maximum recursion depth `r`. -/
def coreParamsSize (r : ℕ) : ℕ := 7 + 3 * r

/-- A finite vertex set `X` stored in sorted order `X.sort (· ≤ ·)` of length `k` at `xAddr`. -/
def VertsAt (mem : ℕ → ℕ) (xAddr k : ℕ) (X : Finset ℕ) : Prop :=
  k = X.card ∧ ListAt mem xAddr (X.sort (· ≤ ·))

/-- A vertex set `X` stored as any duplicate-free list of length `k` at `xAddr`. -/
def NodupVertsAt (mem : ℕ → ℕ) (xAddr k : ℕ) (X : Finset ℕ) : Prop :=
  let ls := readList mem xAddr k
  ls.Nodup ∧ ls.toFinset = X

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Bridging `ProgCloud.cloud`, `CoreOutAt`, and `VertsAt` Slice / Filter Lemmas -/

/-- `ProgCloud.cloud` satisfies `IsCloudExpander` at `1 / ParamConfig.default.a₀ = 1 / 12`. -/
theorem isCloudExpander_progCloud :
    IsCloudExpander cloud (1 / (ParamConfig.default.a₀ : ℝ)) where
  n_eq s hs := by rw [cloud_eq_explicitGraph hs]; exact isCloudExpander_explicitGraph_default.n_eq s hs
  isValid s hs := by rw [cloud_eq_explicitGraph hs]; exact isCloudExpander_explicitGraph_default.isValid s hs
  deg_le s hs := by rw [cloud_eq_explicitGraph hs]; exact isCloudExpander_explicitGraph_default.deg_le s hs
  expansion s hs := by rw [cloud_eq_explicitGraph hs]; exact isCloudExpander_explicitGraph_default.expansion s hs

/-- `VertsAt` implies `NodupVertsAt`. -/
theorem VertsAt.toNodupVertsAt {mem : ℕ → ℕ} {xAddr k : ℕ} {X : Finset ℕ}
    (h : VertsAt mem xAddr k X) : NodupVertsAt mem xAddr k X := by
  have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← h.1]
  have hr : readList mem xAddr k = X.sort (· ≤ ·) := by
    rw [← hlen]; exact readList_eq_of_listAt h.2
  unfold NodupVertsAt
  dsimp only
  rw [hr]
  exact ⟨Finset.sort_nodup X (· ≤ ·), by ext v; simp⟩

/-- Equivalence between `NodupVertsAt` and the existential list representation used in
`OuterProgContracts.CoreOutAt`. -/
theorem nodupVertsAt_iff_exists_listAt {mem : ℕ → ℕ} {xAddr k : ℕ} {X : Finset ℕ} :
    NodupVertsAt mem xAddr k X ↔
      ∃ ls : List ℕ, ls.Nodup ∧ ls.toFinset = X ∧ k = ls.length ∧ ListAt mem xAddr ls := by
  constructor
  · rintro ⟨hnd, hfin⟩
    exact ⟨readList mem xAddr k, hnd, hfin, (readList_length mem xAddr k).symm,
      listAt_readList mem xAddr k⟩
  · rintro ⟨ls, hnd, hfin, rfl, hlat⟩
    unfold NodupVertsAt
    dsimp only
    rw [readList_eq_of_listAt hlat]
    exact ⟨hnd, hfin⟩

/-- A sorted list without duplicates equals `l.toFinset.sort (· ≤ ·)`. -/
theorem eq_sort_of_pairwise_lt {l : List ℕ} (hs : l.Pairwise (· < ·)) :
    l = l.toFinset.sort (· ≤ ·) := by
  have hnd : l.Nodup := hs.imp fun h => ne_of_lt h
  have hle : l.Pairwise (· ≤ ·) := hs.imp fun h => le_of_lt h
  have hperm : l.Perm (l.toFinset.sort (· ≤ ·)) := by
    refine (List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup _ _)).mpr fun x => ?_
    simp
  exact hperm.eq_of_pairwise' hle (Finset.pairwise_sort _ _)

/-- `X.sort (· ≤ ·)` is strictly increasing. -/
theorem pairwise_lt_sort (X : Finset ℕ) : (X.sort (· ≤ ·)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  have hle := List.pairwise_iff_getElem.mp (Finset.pairwise_sort X (· ≤ ·))
  have hnd := List.pairwise_iff_getElem.mp (Finset.sort_nodup X (· ≤ ·))
  intro i j hi hj hij
  exact lt_of_le_of_ne (hle i j hi hj hij) (hnd i j hi hj hij)

/-- Any sublist of `X.sort (· ≤ ·)` equals `sub.toFinset.sort (· ≤ ·)`. -/
theorem sublist_sort_eq_sort {X : Finset ℕ} {sub : List ℕ}
    (hsub : sub.Sublist (X.sort (· ≤ ·))) :
    sub = sub.toFinset.sort (· ≤ ·) :=
  eq_sort_of_pairwise_lt ((pairwise_lt_sort X).sublist hsub)

/-- Filtering `X.sort (· ≤ ·)` by `v ∉ U` yields `(X \ U).sort (· ≤ ·)`. -/
theorem filter_sort_eq_sort_sdiff (X U : Finset ℕ) :
    (X.sort (· ≤ ·)).filter (fun v => decide (v ∉ U)) = (X \ U).sort (· ≤ ·) := by
  have hsub := sublist_sort_eq_sort (List.filter_sublist (l := X.sort (· ≤ ·))
    (p := fun v => decide (v ∉ U)))
  have hfin : ((X.sort (· ≤ ·)).filter (fun v => decide (v ∉ U))).toFinset = X \ U := by
    ext v; simp
  rw [hfin] at hsub
  exact hsub

/-- Filtering `X.sort (· ≤ ·)` by `v ∈ S` yields `(X ∩ S).sort (· ≤ ·)`. -/
theorem filter_sort_eq_sort_inter (X S : Finset ℕ) :
    (X.sort (· ≤ ·)).filter (fun v => decide (v ∈ S)) = (X ∩ S).sort (· ≤ ·) := by
  have hsub := sublist_sort_eq_sort (List.filter_sublist (l := X.sort (· ≤ ·))
    (p := fun v => decide (v ∈ S)))
  have hfin : ((X.sort (· ≤ ·)).filter (fun v => decide (v ∈ S))).toFinset = X ∩ S := by
    ext v; simp
  rw [hfin] at hsub
  exact hsub

/-- `(Finset.range n).sort (· ≤ ·) = List.range n`. -/
theorem sort_range_eq_list_range (n : ℕ) :
    (Finset.range n).sort (· ≤ ·) = List.range n := by
  have h := eq_sort_of_pairwise_lt (List.pairwise_lt_range (n := n))
  have hfin : (List.range n).toFinset = Finset.range n := by ext v; simp
  rw [hfin] at h
  exact h.symm

/-- Sublist slice of `ListAt`: `l.drop start |>.take len` lives at `addr + start`. -/
theorem listAt_take_drop {mem : ℕ → ℕ} {addr : ℕ} {l : List ℕ}
    (h : ListAt mem addr l) (start len : ℕ) :
    ListAt mem (addr + start) ((l.drop start).take len) := by
  intro i hi
  have hlt1 : i < len := by simp [List.length_take] at hi; exact hi.1
  have hlt2 : start + i < l.length := by simp [List.length_take, List.length_drop] at hi; omega
  rw [List.getElem_take, List.getElem_drop, Nat.add_assoc]
  exact h (start + i) hlt2

/-- Zero-copy slice lemma for Step A: block `i < numFullBlocks vs b` sits at `xAddr + i * b` of
length `b` in sorted order. -/
theorem vertsAt_blockSet {mem : ℕ → ℕ} {xAddr k b i : ℕ} {X : Finset ℕ}
    (h : VertsAt mem xAddr k X) (hi : i < numFullBlocks (X.sort (· ≤ ·)) b) :
    VertsAt mem (xAddr + i * b) b (blockSet (X.sort (· ≤ ·)) b i) := by
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hsub : (blockList vs b i).Sublist vs :=
    List.take_sublist _ _ |>.trans (List.drop_sublist _ _)
  have hsort : blockList vs b i = (blockSet vs b i).sort (· ≤ ·) := by
    unfold blockSet
    exact sublist_sort_eq_sort hsub
  refine ⟨(card_blockSet hnd hi).symm, ?_⟩
  rw [← hsort]
  exact listAt_take_drop h.2 (i * b) b

/-- Zero-copy prefix lemma for Step C: `fullVerts` sits at `xAddr` of length `numFullBlocks * b`. -/
theorem vertsAt_fullVerts {mem : ℕ → ℕ} {xAddr k b : ℕ} {X : Finset ℕ}
    (h : VertsAt mem xAddr k X) :
    let m := numFullBlocks (X.sort (· ≤ ·)) b
    VertsAt mem xAddr (m * b) (fullVerts (X.sort (· ≤ ·)) b) := by
  set vs := X.sort (· ≤ ·)
  set m := numFullBlocks vs b
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hle : m * b ≤ vs.length := by
    unfold m numFullBlocks
    exact Nat.div_mul_le_self vs.length b
  have hsub : (vs.take (m * b)).Sublist vs := List.take_sublist _ _
  have hsort : vs.take (m * b) = (fullVerts vs b).sort (· ≤ ·) := by
    unfold fullVerts fullPrefix
    exact sublist_sort_eq_sort hsub
  have hcard : (fullVerts vs b).card = m * b := by
    unfold fullVerts fullPrefix
    rw [List.toFinset_card_of_nodup (hnd.sublist hsub), List.length_take, Nat.min_eq_left hle]
  refine ⟨hcard.symm, ?_⟩
  rw [← hsort]
  simpa using listAt_take_drop h.2 0 (m * b)

/-- Zero-copy suffix lemma for Step C: `leftoverVerts` sits at `xAddr + m * b` of length
`k - m * b`. -/
theorem vertsAt_leftoverVerts {mem : ℕ → ℕ} {xAddr k b : ℕ} {X : Finset ℕ}
    (h : VertsAt mem xAddr k X) :
    let m := numFullBlocks (X.sort (· ≤ ·)) b
    VertsAt mem (xAddr + m * b) (k - m * b) (leftoverVerts (X.sort (· ≤ ·)) b) := by
  set vs := X.sort (· ≤ ·)
  set m := numFullBlocks vs b
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvlen : vs.length = k := by rw [Finset.length_sort, ← h.1]
  have hsub : (vs.drop (m * b)).Sublist vs := List.drop_sublist _ _
  have hsort : vs.drop (m * b) = (leftoverVerts vs b).sort (· ≤ ·) := by
    unfold leftoverVerts leftoverList
    exact sublist_sort_eq_sort hsub
  have hcard : (leftoverVerts vs b).card = k - m * b := by
    unfold leftoverVerts leftoverList
    rw [List.toFinset_card_of_nodup (hnd.sublist hsub), List.length_drop, hvlen]
  refine ⟨hcard.symm, ?_⟩
  rw [← hsort]
  have htake : (vs.drop (m * b)).take (k - m * b) = vs.drop (m * b) := by
    rw [List.take_of_length_le]; rw [List.length_drop, hvlen]
  rw [← htake]
  exact listAt_take_drop h.2 (m * b) (k - m * b)

end MinCostFlow.ExpanderDecomp
