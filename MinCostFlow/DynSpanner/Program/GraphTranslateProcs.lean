module

public import MinCostFlow.DynSpanner.Program.MergeSort
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.Spanner.Layouts

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Log

/-!
# Part 1 of `GraphTranslate`

The first part of `GraphTranslate.lean`, split off to keep files short. See `GraphTranslate.lean` for the
overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

def gtIdxSortDedup : ℕ := 0
def gtIdxSortedDiff : ℕ := 1
def gtIdxLookupHVert : ℕ := 2
def gtIdxCollectRawEs : ℕ := 3
def gtIdxCollectRawVs : ℕ := 4

/-! ## Pure list & translation helpers -/

/-- Pure two-pointer difference on strictly increasing lists `us` and `js`. -/
def sortedDiff : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | us, [] => us
  | u :: us, v :: js =>
    if u < v then u :: sortedDiff us (v :: js)
    else if v < u then sortedDiff (u :: us) js
    else sortedDiff us js

@[simp] lemma sortedDiff_nil_left (js : List ℕ) : sortedDiff [] js = [] := by
  cases js <;> simp [sortedDiff]

@[simp] lemma sortedDiff_nil_right (us : List ℕ) : sortedDiff us [] = us := by
  cases us <;> simp [sortedDiff]

lemma sortedDiff_cons_lt {u v : ℕ} {us js : List ℕ} (h : u < v) :
    sortedDiff (u :: us) (v :: js) = u :: sortedDiff us (v :: js) := by
  simp [sortedDiff, h]

lemma sortedDiff_cons_gt {u v : ℕ} {us js : List ℕ} (h : v < u) :
    sortedDiff (u :: us) (v :: js) = sortedDiff (u :: us) js := by
  have h1 : ¬ u < v := by omega
  simp [sortedDiff, h1, h]

lemma sortedDiff_cons_eq {u : ℕ} {us js : List ℕ} :
    sortedDiff (u :: us) (u :: js) = sortedDiff us js := by
  simp [sortedDiff]

/-- Any strictly increasing list `L` enumerating `X : Finset ℕ` equals `vertsOf X`. -/
lemma vertsOf_eq_of_pairwise_lt {L : List ℕ} {X : Finset ℕ}
    (hp : L.Pairwise (· < ·)) (hmem : ∀ x, x ∈ L ↔ x ∈ X) : L = vertsOf X := by
  have hX : L.toFinset = X := by ext x; simp [hmem]
  rw [← hX, vertsOf_toFinset_of_pairwise_lt hp]

/-- Deduplicating a sorted list `L` enumerating `X` yields `vertsOf X`. -/
lemma sortedDedup_eq_vertsOf {L : List ℕ} {X : Finset ℕ}
    (hp : L.Pairwise (· ≤ ·)) (hmem : ∀ x, x ∈ L ↔ x ∈ X) :
    sortedDedup L = vertsOf X := by
  refine vertsOf_eq_of_pairwise_lt (sortedDedup_pairwise hp) fun x => ?_
  rw [sortedDedup_mem hp, hmem]

lemma sortedDiff_mem : ∀ {us js : List ℕ},
    us.Pairwise (· < ·) → js.Pairwise (· < ·) →
    ∀ x, x ∈ sortedDiff us js ↔ x ∈ us ∧ x ∉ js
  | [], _, _, _, x => by simp
  | u :: us, [], _, _, x => by simp
  | u :: us, v :: js, hus, hjs, x => by
    have hus' := (List.pairwise_cons.mp hus).2
    have hjs' := (List.pairwise_cons.mp hjs).2
    have hu_lt := (List.pairwise_cons.mp hus).1
    have hv_lt := (List.pairwise_cons.mp hjs).1
    by_cases huv : u < v
    · rw [sortedDiff_cons_lt huv]
      simp only [List.mem_cons, sortedDiff_mem hus' hjs]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · refine ⟨Or.inl rfl, ?_⟩
          rintro (rfl | hmem)
          · exact Nat.lt_irrefl _ huv
          · exact absurd (lt_trans huv (hv_lt _ hmem)) (Nat.lt_irrefl _)
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | hx, hnx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hnx⟩
    · by_cases hvu : v < u
      · rw [sortedDiff_cons_gt hvu]
        simp only [sortedDiff_mem hus hjs', List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rintro (rfl | hm)
          · rcases h1 with rfl | hm1
            · exact Nat.lt_irrefl _ hvu
            · exact absurd (lt_trans hvu (hu_lt _ hm1)) (Nat.lt_irrefl _)
          · exact h2 hm
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hm => h2 (Or.inr hm)⟩
      · have heq : u = v := Nat.le_antisymm (Nat.le_of_not_lt hvu) (Nat.le_of_not_lt huv)
        subst heq
        rw [sortedDiff_cons_eq]
        simp only [sortedDiff_mem hus' hjs', List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨Or.inr h1, ?_⟩
          rintro (rfl | hm)
          · exact absurd (hu_lt _ h1) (Nat.lt_irrefl _)
          · exact h2 hm
        · rintro ⟨rfl | h1, h2⟩
          · exact absurd (Or.inl rfl) h2
          · exact ⟨h1, fun hm => h2 (Or.inr hm)⟩

lemma sortedDiff_pairwise : ∀ {us js : List ℕ},
    us.Pairwise (· < ·) → js.Pairwise (· < ·) → (sortedDiff us js).Pairwise (· < ·)
  | [], _, _, _ => by simp
  | _ :: _, [], hus, _ => by simpa using hus
  | u :: us, v :: js, hus, hjs => by
    have hus' := (List.pairwise_cons.mp hus).2
    have hjs' := (List.pairwise_cons.mp hjs).2
    have hu_lt := (List.pairwise_cons.mp hus).1
    by_cases huv : u < v
    · rw [sortedDiff_cons_lt huv, List.pairwise_cons]
      refine ⟨fun y hy => ?_, sortedDiff_pairwise hus' hjs⟩
      exact hu_lt y ((sortedDiff_mem hus' hjs y).mp hy).1
    · by_cases hvu : v < u
      · rw [sortedDiff_cons_gt hvu]
        exact sortedDiff_pairwise hus hjs'
      · have heq : u = v := Nat.le_antisymm (Nat.le_of_not_lt hvu) (Nat.le_of_not_lt huv)
        subst heq
        rw [sortedDiff_cons_eq]
        exact sortedDiff_pairwise hus' hjs'

lemma sortedDiff_length_le : ∀ (us js : List ℕ), (sortedDiff us js).length ≤ us.length
  | [], _ => by simp
  | u :: us, [] => by simp
  | u :: us, v :: js => by
    by_cases huv : u < v
    · rw [sortedDiff_cons_lt huv, List.length_cons, List.length_cons]
      have := sortedDiff_length_le us (v :: js); omega
    · by_cases hvu : v < u
      · rw [sortedDiff_cons_gt hvu]
        exact sortedDiff_length_le (u :: us) js
      · have heq : u = v := Nat.le_antisymm (Nat.le_of_not_lt hvu) (Nat.le_of_not_lt huv)
        subst heq
        rw [sortedDiff_cons_eq, List.length_cons]
        have := sortedDiff_length_le us js; omega

lemma sortedDiff_eq_vertsOf_sdiff {us js : List ℕ} {U J : Finset ℕ}
    (hus : us.Pairwise (· < ·)) (hjs : js.Pairwise (· < ·))
    (hu : ∀ x, x ∈ us ↔ x ∈ U) (hj : ∀ x, x ∈ js ↔ x ∈ J) :
    sortedDiff us js = vertsOf (U \ J) := by
  refine vertsOf_eq_of_pairwise_lt (sortedDiff_pairwise hus hjs) fun x => ?_
  rw [sortedDiff_mem hus hjs, hu, hj, Finset.mem_sdiff]

/-- Flattened list of edge IDs visited by `emb` across `jEs`. -/
def collectRawEsFun (jEs : List ℕ) (emb : MinCostFlow.Embedding) : List ℕ :=
  jEs.flatMap fun e => (emb e).map Prod.fst

/-- Flattened list of vertices visited by `emb` across `(jEs, jTails)` in `H'`. -/
def collectRawVsFun (H' : MGraph) (jEs jTails : List ℕ) (emb : MinCostFlow.Embedding) : List ℕ :=
  (List.range jEs.length).flatMap fun j => H'.walkVertices (jTails.getD j 0) (emb (jEs.getD j 0))

lemma collectRawEsFun_mem {J : MGraph} {jEs : List ℕ} {emb : MinCostFlow.Embedding}
    (hjE : ∀ e, e ∈ jEs ↔ e ∈ J.E) (x : ℕ) :
    x ∈ collectRawEsFun jEs emb ↔ x ∈ usedHEdges J emb := by
  simp only [collectRawEsFun, List.mem_flatMap, List.mem_map, usedHEdges, Finset.mem_biUnion,
    MinCostFlow.walkEdges, List.mem_toFinset]
  constructor
  · rintro ⟨e, he, ⟨y, hy, rfl⟩⟩
    exact ⟨e, (hjE e).mp he, y, hy, rfl⟩
  · rintro ⟨e, he, ⟨y, hy, rfl⟩⟩
    exact ⟨e, (hjE e).mpr he, y, hy, rfl⟩

lemma collectRawVsFun_mem {H' J : MGraph} {jEs jTails : List ℕ} {emb : MinCostFlow.Embedding}
    (hLen : jTails.length = jEs.length)
    (hjE : ∀ e, e ∈ jEs ↔ e ∈ J.E)
    (htail : ∀ j (hj : j < jEs.length), jTails[j]'(by omega) = J.tail (jEs[j]'hj))
    (x : ℕ) :
    x ∈ collectRawVsFun H' jEs jTails emb ∨ x ∈ J.V ↔ x ∈ usedHVerts H' J emb := by
  simp only [collectRawVsFun, List.mem_flatMap, List.mem_range, usedHVerts, Finset.mem_union,
    Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro (⟨j, hj, hx⟩ | hxV)
    · right
      have heJ : jEs[j]'hj ∈ J.E := (hjE _).mp (List.getElem_mem hj)
      refine ⟨jEs[j]'hj, heJ, ?_⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem (by omega : j < jTails.length), Option.getD_some, htail j hj] at hx
      exact hx
    · exact Or.inl hxV
  · rintro (hxV | ⟨e, heJ, hx⟩)
    · exact Or.inr hxV
    · left
      have he_mem : e ∈ jEs := (hjE e).mpr heJ
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he_mem
      refine ⟨j, hj, ?_⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem (by omega : j < jTails.length), Option.getD_some, htail j hj]
      exact hx

/-! ## Procedure definitions -/

/-- Generalized contract for `binSearchStmt` (`[a, L.length, key]`) without assuming `key ∈ L`. -/
def binSearchOptContract (w : ℕ) (L : List ℕ) (key : ℕ) : Contract where
  pre args mem := ∃ a,
    args = [a, L.length, key] ∧ 16 ≤ 2 ^ w ∧
    a + L.length < 2 ^ w ∧ key < 2 ^ w ∧
    L.Pairwise (· < ·) ∧ ListAt mem a L ∧ (∀ x ∈ L, x < 2 ^ w)
  post args mem ret mem' := ∃ a,
    args = [a, L.length, key] ∧ mem' = mem ∧
    (L = [] → ret = 0) ∧
    (0 < L.length → ret < L.length ∧ (key ∈ L ↔ L[ret]? = some key) ∧
      (key ∈ L → ret = L.idxOf key))
  cost _ _ := 45 * (Nat.log 2 (L.length + 1) + 1) + 20

/-- Sort `[src, src + len)` in place using `scratch`, deduplicate into `[dst, dst + outLen)`,
and return `outLen` (`[src, len, dst, scratch]`). -/
def gtSortDedupStmt (bSort : ℕ) : Stmt :=
  .call 4 (bSort + sortIdxMergeSort) [.reg 0, .reg 1, .reg 3] ;;
  .call 4 (bSort + sortIdxDedup) [.reg 0, .reg 1, .reg 2] ;;
  .ret (.reg 4)

/-- Compute `sortedDiff` of strictly increasing `[aU, aU + nU)` and `[aJ, aJ + nJ)` into
`[dst, dst + outLen)`, returning `outLen` (`[aU, nU, aJ, nJ, dst]`). -/
def gtSortedDiffStmt : Stmt :=
  .assign 5 (.const 0) ;;
  .assign 6 (.const 0) ;;
  .assign 7 (.const 0) ;;
  .loop (.bin .lt (.reg 5) (.reg 1))
    (.cond (.bin .lt (.reg 6) (.reg 3))
      (.assign 8 (.load (.bin .add (.reg 0) (.reg 5))) ;;
       .assign 9 (.load (.bin .add (.reg 2) (.reg 6))) ;;
       .cond (.bin .lt (.reg 8) (.reg 9))
         (.store (.bin .add (.reg 4) (.reg 7)) (.reg 8) ;;
          .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
          .assign 5 (.bin .add (.reg 5) (.const 1)))
         (.cond (.bin .lt (.reg 9) (.reg 8))
            (.assign 6 (.bin .add (.reg 6) (.const 1)))
            (.assign 5 (.bin .add (.reg 5) (.const 1)) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1)))))
      (.assign 8 (.load (.bin .add (.reg 0) (.reg 5))) ;;
       .store (.bin .add (.reg 4) (.reg 7)) (.reg 8) ;;
       .assign 7 (.bin .add (.reg 7) (.const 1)) ;;
       .assign 5 (.bin .add (.reg 5) (.const 1)))) ;;
  .ret (.reg 7)

/-- Look up index of `key` in `jVs ++ exVs` where both arrays are strictly increasing and disjoint
(`[jVsPtr, nJ, exVsPtr, nEx, key]`). -/
def gtLookupHVertStmt (bSort : ℕ) : Stmt :=
  .cond (.bin .lt (.const 0) (.reg 1))
    (.call 5 (bSort + sortIdxBinSearch) [.reg 0, .reg 1, .reg 4] ;;
     .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .cond (.bin .eq (.reg 6) (.reg 4))
       (.ret (.reg 5))
       (.call 7 (bSort + sortIdxBinSearch) [.reg 2, .reg 3, .reg 4] ;;
        .ret (.bin .add (.reg 1) (.reg 7))))
    (.call 7 (bSort + sortIdxBinSearch) [.reg 2, .reg 3, .reg 4] ;;
     .ret (.reg 7))

/-- Flatten all edge IDs appearing on `emb (jEs[j])` (`j < mJ`) into `rawEsPtr`, returning the
total number of edge steps (`[mJ, jEsPtr, mEmbPtr, rawEsPtr]`). -/
def gtCollectRawEsStmt : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 0)
    (.assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .assign 7 (.load (.bin .add (.reg 2) (.reg 6))) ;;
     .assign 8 (.load (.reg 7)) ;;
     forRange 9 (.const 0) (.reg 8)
       (.assign 10 (.load (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 9))))) ;;
        .store (.bin .add (.reg 3) (.reg 4)) (.reg 10) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)))) ;;
  .ret (.reg 4)

/-- Flatten all vertices of `H'.walkVertices (jTails[j]) (emb (jEs[j]))` (`j < mJ`) into
`rawVsPtr`, returning total count (`[hPtr, mJ, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr]`). -/
def gtCollectRawVsStmt (bOps : ℕ) : Stmt :=
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1)
    (.assign 8 (.load (.bin .add (.reg 3) (.reg 7))) ;;
     .store (.bin .add (.reg 5) (.reg 6)) (.reg 8) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
     .assign 8 (.load (.bin .add (.reg 2) (.reg 7))) ;;
     .assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
     .assign 10 (.load (.reg 9)) ;;
     forRange 11 (.const 0) (.reg 10)
       (.assign 12 (.load (.bin .add (.reg 9) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 11))))) ;;
        .assign 13 (.load (.bin .add (.reg 9) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 11))))) ;;
        .cond (.bin .eq (.reg 13) (.const 1))
          (.call 14 (bOps + dgIdxGetHead) [.reg 0, .reg 12])
          (.call 14 (bOps + dgIdxGetTail) [.reg 0, .reg 12]) ;;
        .store (.bin .add (.reg 5) (.reg 6)) (.reg 14) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1)))) ;;
  .ret (.reg 6)

def gtProcs (bSort bOps : ℕ) : List Stmt :=
  [gtSortDedupStmt bSort, gtSortedDiffStmt, gtLookupHVertStmt bSort,
   gtCollectRawEsStmt, gtCollectRawVsStmt bOps]

lemma gtProcs_length (bSort bOps : ℕ) : (gtProcs bSort bOps).length = 5 := rfl

lemma gtProcs_noRand (bSort bOps : ℕ) : ∀ s ∈ gtProcs bSort bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts for `gtProcs` -/

def gtSortDedupContract (w : ℕ) (L : List ℕ) (X : Finset ℕ) : Contract where
  pre args mem := ∃ src dst scratch,
    args = [src, L.length, dst, scratch] ∧ 16 ≤ 2 ^ w ∧
    src + L.length < 2 ^ w ∧ dst + L.length < 2 ^ w ∧ scratch + L.length < 2 ^ w ∧
    (src + L.length ≤ scratch ∨ scratch + L.length ≤ src) ∧
    (src + L.length ≤ dst ∨ dst + L.length ≤ src) ∧
    ListAt mem src L ∧ (∀ x ∈ L, x < 2 ^ w) ∧ (∀ x, x ∈ L ↔ x ∈ X)
  post args mem ret mem' := ∃ src dst scratch,
    args = [src, L.length, dst, scratch] ∧
    ret = (vertsOf X).length ∧
    ListAt mem' dst (vertsOf X) ∧
    ∀ addr, (addr < src ∨ src + L.length ≤ addr) →
      (addr < scratch ∨ scratch + L.length ≤ addr) →
      (addr < dst ∨ dst + (vertsOf X).length ≤ addr) → mem' addr = mem addr
  cost _ _ := 250 * L.length * (Nat.log 2 (L.length + 1) + 1) + 120

def gtSortedDiffContract (w : ℕ) (us js : List ℕ) (U J : Finset ℕ) : Contract where
  pre args mem := ∃ aU aJ dst,
    args = [aU, us.length, aJ, js.length, dst] ∧ 16 ≤ 2 ^ w ∧
    aU + us.length < 2 ^ w ∧ aJ + js.length < 2 ^ w ∧ dst + us.length < 2 ^ w ∧
    (∀ i < us.length, aU + i < dst ∨ dst + us.length ≤ aU + i) ∧
    (∀ i < js.length, aJ + i < dst ∨ dst + us.length ≤ aJ + i) ∧
    us.Pairwise (· < ·) ∧ js.Pairwise (· < ·) ∧
    (∀ x, x ∈ us ↔ x ∈ U) ∧ (∀ x, x ∈ js ↔ x ∈ J) ∧
    ListAt mem aU us ∧ ListAt mem aJ js ∧
    (∀ x ∈ us, x < 2 ^ w) ∧ (∀ x ∈ js, x < 2 ^ w)
  post args mem ret mem' := ∃ aU aJ dst,
    args = [aU, us.length, aJ, js.length, dst] ∧
    ret = (vertsOf (U \ J)).length ∧
    ListAt mem' dst (vertsOf (U \ J)) ∧
    ∀ addr, addr < dst ∨ dst + (vertsOf (U \ J)).length ≤ addr → mem' addr = mem addr
  cost _ _ := 50 * (us.length + js.length) + 40

def gtLookupHVertContract (w : ℕ) (jVs exVs : List ℕ) (key : ℕ) : Contract where
  pre args mem := ∃ jVsPtr exVsPtr,
    args = [jVsPtr, jVs.length, exVsPtr, exVs.length, key] ∧ 16 ≤ 2 ^ w ∧
    jVsPtr + jVs.length < 2 ^ w ∧ exVsPtr + exVs.length < 2 ^ w ∧
    key < 2 ^ w ∧ jVs.length + exVs.length < 2 ^ w ∧
    jVs.Pairwise (· < ·) ∧ exVs.Pairwise (· < ·) ∧
    (∀ x, x ∈ jVs → x ∉ exVs) ∧ key ∈ jVs ++ exVs ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem exVsPtr exVs ∧
    (∀ x ∈ jVs, x < 2 ^ w) ∧ (∀ x ∈ exVs, x < 2 ^ w)
  post args mem ret mem' := ∃ jVsPtr exVsPtr,
    args = [jVsPtr, jVs.length, exVsPtr, exVs.length, key] ∧
    mem' = mem ∧ ret = (jVs ++ exVs).idxOf key ∧ ret < jVs.length + exVs.length
  cost _ _ := 90 * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) + 80

def gtCollectRawEsContract (w eCap : ℕ) (J : MGraph) (jEs : List ℕ)
    (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ jEsPtr mEmbPtr rawEsPtr,
    args = [jEs.length, jEsPtr, mEmbPtr, rawEsPtr] ∧ 16 ≤ 2 ^ w ∧
    jEsPtr + jEs.length < 2 ^ w ∧ mEmbPtr + eCap < 2 ^ w ∧
    rawEsPtr + (collectRawEsFun jEs emb).length < 2 ^ w ∧
    (∀ i < jEs.length, jEsPtr + i < rawEsPtr ∨ rawEsPtr + (collectRawEsFun jEs emb).length ≤ jEsPtr + i) ∧
    (∀ e ∈ J.E, mEmbPtr + e < rawEsPtr ∨ rawEsPtr + (collectRawEsFun jEs emb).length ≤ mEmbPtr + e) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
      mem (mEmbPtr + e) + k < rawEsPtr ∨
      rawEsPtr + (collectRawEsFun jEs emb).length ≤ mem (mEmbPtr + e) + k) ∧
    (∀ e, e ∈ jEs ↔ e ∈ J.E) ∧
    MEmbAt mem mEmbPtr J.E eCap emb ∧ ListAt mem jEsPtr jEs ∧
    (∀ e ∈ J.E, ∀ x ∈ emb e, x.1 < 2 ^ w) ∧
    (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
  post args mem ret mem' := ∃ jEsPtr mEmbPtr rawEsPtr,
    args = [jEs.length, jEsPtr, mEmbPtr, rawEsPtr] ∧
    ret = (collectRawEsFun jEs emb).length ∧
    ListAt mem' rawEsPtr (collectRawEsFun jEs emb) ∧
    ∀ addr, addr < rawEsPtr ∨ rawEsPtr + (collectRawEsFun jEs emb).length ≤ addr → mem' addr = mem addr
  cost _ _ := 35 * ((collectRawEsFun jEs emb).length + jEs.length) + 30

def gtCollectRawVsContract (w vCap eCap : ℕ) (H' J : MGraph) (jEs jTails : List ℕ)
    (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ hPtr jEsPtr jTailsPtr mEmbPtr rawVsPtr,
    args = [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr] ∧ 16 ≤ 2 ^ w ∧
    hPtr + dynGraphSize vCap eCap < 2 ^ w ∧ jEsPtr + jEs.length < 2 ^ w ∧
    jTailsPtr + jEs.length < 2 ^ w ∧ mEmbPtr + eCap < 2 ^ w ∧
    rawVsPtr + (collectRawVsFun H' jEs jTails emb).length < 2 ^ w ∧
    (∀ i < dynGraphSize vCap eCap,
      hPtr + i < rawVsPtr ∨ rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ hPtr + i) ∧
    (∀ i < jEs.length, jEsPtr + i < rawVsPtr ∨ rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ jEsPtr + i) ∧
    (∀ i < jEs.length, jTailsPtr + i < rawVsPtr ∨ rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ jTailsPtr + i) ∧
    (∀ e ∈ J.E, mEmbPtr + e < rawVsPtr ∨ rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ mEmbPtr + e) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
      mem (mEmbPtr + e) + k < rawVsPtr ∨
      rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ mem (mEmbPtr + e) + k) ∧
    DynGraphAt mem hPtr vCap eCap H' ∧
    jTails.length = jEs.length ∧ (∀ e, e ∈ jEs ↔ e ∈ J.E) ∧
    (∀ j (hj : j < jEs.length), jTails.getD j 0 = J.tail (jEs[j]'hj) ∧ J.tail (jEs[j]'hj) < 2 ^ w) ∧
    MEmbAt mem mEmbPtr J.E eCap emb ∧ ListAt mem jEsPtr jEs ∧ ListAt mem jTailsPtr jTails ∧
    (∀ e ∈ J.E, ∀ x ∈ emb e, x.1 ∈ H'.E ∧ x.1 < 2 ^ w) ∧
    (∀ v ∈ H'.V, v < 2 ^ w) ∧
    (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
  post args mem ret mem' := ∃ hPtr jEsPtr jTailsPtr mEmbPtr rawVsPtr,
    args = [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr] ∧
    ret = (collectRawVsFun H' jEs jTails emb).length ∧
    ListAt mem' rawVsPtr (collectRawVsFun H' jEs jTails emb) ∧
    ∀ addr, addr < rawVsPtr ∨ rawVsPtr + (collectRawVsFun H' jEs jTails emb).length ≤ addr → mem' addr = mem addr
  cost _ _ := 115 * (collectRawVsFun H' jEs jTails emb).length + 30

end

/-! ## Helpers shared with `GraphTranslateCollect` -/

private lemma logBound_halve {d d' : ℕ} (_hd : 2 ≤ d) (hdiv : d' - 1 ≤ (d - 1) / 2) :
    (if d' ≤ 1 then 0 else Nat.log 2 (d' - 1) + 1) + 1 ≤ Nat.log 2 (d - 1) + 1 := by
  by_cases hd'1 : d' ≤ 1
  · simp [hd'1]
  · simp only [hd'1, ↓reduceIte, Nat.add_le_add_iff_right]
    have hd'pos : 1 ≤ d' - 1 := by omega
    have hpow : 2 ^ (Nat.log 2 (d' - 1) + 1) ≤ d - 1 := by
      have hp := Nat.pow_log_le_self 2 (by omega : d' - 1 ≠ 0)
      rw [Nat.pow_succ]
      omega
    exact Nat.le_log_of_pow_le (by omega) hpow

public theorem runs_cond_le_gt {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hq, by omega⟩
  · rcases hT hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hq, by omega⟩

/-! ## Verification proofs -/

public section

theorem binSearchOpt_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ}
    {L : List ℕ} {key : ℕ} (hp : p.HasAt b (sortProcs bSort)) :
    MeetsContract w p (b + sortIdxBinSearch) (binSearchOptContract w L key) := by
  refine meetsContract_of_runs (hp.get (i := sortIdxBinSearch) (by simp [sortProcs, sortIdxBinSearch]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨a, rfl, hw16, haB, hlt_key, hLpair, hLat, hLw⟩
  have hlt_a : a < 2 ^ w := hargs a (by simp)
  have hlt_len : L.length < 2 ^ w := hargs L.length (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [sortProcs, sortIdxBinSearch, List.getElem_cons_succ, List.getElem_cons_zero,
    binSearchStmt]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := L.length) (by eval_expr) ?_
  by_cases hLnil : L = []
  · subst hLnil
    simp only [List.length_nil]
    let st0 : State := { (startState [a, 0, key] mem pos) with
      regs := Function.update (Function.update (startState [a, 0, key] mem pos).regs 3 0) 4 0 }
    refine ⟨.returned 0, st0, 6 + 2 + 1, runs_seq_iff.mpr (Or.inr ⟨st0, 6, 2,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, Function.update_of_ne, h1_lt, h0_lt],
        rfl, rfl, by simp [Expr.size]⟩),
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, st0], rfl, rfl, by simp [Expr.size]⟩, rfl⟩),
      ⟨a, rfl, rfl, fun _ => rfl, fun h => by simp at h⟩, ?_⟩
    dsimp only [binSearchOptContract, Expr.size]; simp
  · have hLpos : 0 < L.length := List.length_pos_of_ne_nil hLnil
    let logB : ℕ → ℕ := fun d => if d ≤ 1 then 0 else Nat.log 2 (d - 1) + 1
    let Inv : State → Prop := fun st =>
      st.regs 0 = a ∧ st.regs 2 = key ∧ st.mem = mem ∧
      st.regs 3 < st.regs 4 ∧ st.regs 4 ≤ L.length ∧
      ∀ j (hj : j < L.length), L[j] = key → st.regs 3 ≤ j ∧ j < st.regs 4
    let condExpr : Expr := .bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4)
    let bodyStmt : Stmt :=
      .assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))) ;;
      .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
      .cond (.bin .lt (.reg 2) (.reg 6))
        (.assign 4 (.reg 5))
        (.assign 3 (.reg 5))
    let mFn : State → ℕ := fun st => st.regs 4 - st.regs 3
    let remFn : State → ℕ := fun st => 45 * logB (st.regs 4 - st.regs 3) + 10
    let condFn : State → ℕ := fun st => if st.regs 3 + 1 < st.regs 4 then 1 else 0
    have hloop : Triple w p Inv (.loop condExpr bodyStmt)
        (normalPost fun st =>
          st.mem = mem ∧ st.regs 3 < L.length ∧
          (∀ j (hj : j < L.length), L[j] = key → j = st.regs 3)) remFn := by
      refine Triple.loop_measure (condVal := condFn) (m := mFn) (rem := remFn)
        (fun st hInv => by
          rcases hInv with ⟨_, _, _, hlo, hhi, _⟩
          have hlo1 : st.regs 3 + 1 < 2 ^ w := by omega
          dsimp only [condExpr, condFn]
          split_ifs with hlt <;> simp [Expr.eval, BinOp.eval, h1_lt, hlo1, h0_lt, hlt])
        (fun st hInv hv => by
          rcases hInv with ⟨_, _, hmem, hlo, hhi, hRng⟩
          dsimp only [condFn] at hv
          have hnot : ¬ (st.regs 3 + 1 < st.regs 4) := by by_contra hc; simp [hc] at hv
          refine ⟨⟨hmem, by omega, fun j hj hLj => by have := hRng j hj hLj; omega⟩,
            by dsimp only [condExpr, Expr.size, remFn]; omega⟩)
        (fun st hInv hv => by
          rcases hInv with ⟨hr0, hr2, hmem, hlo_hi, hhi_len, hRng⟩
          dsimp only [condFn] at hv
          have hlo1_hi : st.regs 3 + 1 < st.regs 4 := by by_contra hc; simp [hc] at hv
          let lo := st.regs 3
          let hi := st.regs 4
          let mid := lo + (hi - lo) / 2
          have hmid_lo : lo < mid := by dsimp only [mid]; omega
          have hmid_hi : mid < hi := by dsimp only [mid]; omega
          have hmid_len : mid < L.length := lt_of_lt_of_le hmid_hi hhi_len
          have hamid_lt : a + mid < 2 ^ w := by omega
          have hval_lt : L[mid] < 2 ^ w := hLw L[mid] (List.getElem_mem hmid_len)
          have hval_mem : st.mem (a + mid) = L[mid] := by rw [hmem]; exact hLat mid hmid_len
          refine ⟨35, ?_⟩
          intro s ω' hs_eq
          subst s
          suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
              (match o with
                | .returned u => normalPost (fun st => st.mem = mem ∧ st.regs 3 < L.length ∧
                    (∀ j (hj : j < L.length), L[j] = key → j = st.regs 3)) (.returned u) s' ∧
                    condExpr.size + 35 + 1 ≤ remFn st
                | .normal => Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 35 + remFn s' + 1 ≤ remFn st) ∧
              0 + c ≤ 35 by
            rcases h with ⟨o, s', c, hr, hq, hc⟩
            exact ⟨o, s', c, hr, hq, by simpa using hc⟩
          dsimp only [bodyStmt]
          refine runs_seq_assign_le (v := mid)
            (by simp [Expr.eval, BinOp.eval, h2_lt,
              show hi - lo < 2 ^ w by omega, show (hi - lo) / 2 < 2 ^ w by omega,
              show mid < 2 ^ w by omega, lo, hi, mid]) ?_
          refine runs_seq_assign_le
            (Expr.eval_load_of_eq (v := L[mid]) (by simp [Expr.eval, BinOp.eval, hr0, hamid_lt]) hval_mem) ?_
          by_cases hlt_k : key < L[mid]
          · refine runs_cond_le_gt (v := 1)
              (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hlt_k, h1_lt]) ?_ ?_
            · intro _
              refine runs_assign_le (v := mid) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
              refine ⟨⟨by simp [hr0], by simp [hr2], hmem, by simpa [lo] using hmid_lo, by simp; omega,
                fun j hj hLj => ?_⟩, (by dsimp only [mFn]; simp; omega), ?_⟩
              · obtain ⟨hl, _⟩ := hRng j hj hLj
                refine ⟨by simpa using hl, ?_⟩
                simp only [Function.update_self]
                by_contra hge
                have hle : mid ≤ j := Nat.le_of_not_lt hge
                rcases lt_or_eq_of_le hle with hlt' | rfl
                · have hpw := (List.pairwise_iff_getElem.mp hLpair) mid j hmid_len hj hlt'
                  omega
                · omega
              · have hnot1 : ¬ (st.regs 4 - st.regs 3 ≤ 1) := by dsimp only [lo, hi] at *; omega
                dsimp only [condExpr, Expr.size, remFn, logB, lo, hi]
                simp only [hnot1, ↓reduceIte, Function.update_self,
                  Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
                  Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
                  Function.update_of_ne (by decide : (3 : ℕ) ≠ 5)]
                have hlog := logBound_halve (d := st.regs 4 - st.regs 3) (d' := mid - st.regs 3)
                  (by dsimp only [lo, hi] at *; omega)
                  (by dsimp only [mid, lo, hi] at *; omega)
                have h45 := Nat.mul_le_mul_left 45 hlog
                dsimp only [mid, lo, hi] at h45 ⊢
                omega
            · intro hc; cases hc
          · refine runs_cond_le_gt (v := 0)
              (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hlt_k, h0_lt]) ?_ ?_
            · intro hc; exact absurd rfl hc
            · intro _
              refine runs_assign_le (v := mid) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
              refine ⟨⟨by simp [hr0], by simp [hr2], hmem, by simp [hi, hmid_hi], by simpa [hi] using hhi_len,
                fun j hj hLj => ?_⟩, (by dsimp only [mFn]; simp; omega), ?_⟩
              · obtain ⟨_, hh⟩ := hRng j hj hLj
                refine ⟨?_, by simpa using hh⟩
                simp only [Function.update_self]
                by_contra hlt'
                have hpw := (List.pairwise_iff_getElem.mp hLpair) j mid hj hmid_len (Nat.lt_of_not_le hlt')
                omega
              · have hnot1 : ¬ (st.regs 4 - st.regs 3 ≤ 1) := by dsimp only [lo, hi] at *; omega
                dsimp only [condExpr, Expr.size, remFn, logB, lo, hi]
                simp only [hnot1, ↓reduceIte, Function.update_self,
                  Function.update_of_ne (by decide : (4 : ℕ) ≠ 3),
                  Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
                  Function.update_of_ne (by decide : (4 : ℕ) ≠ 5)]
                have hlog := logBound_halve (d := st.regs 4 - st.regs 3) (d' := st.regs 4 - mid)
                  (by dsimp only [lo, hi] at *; omega)
                  (by dsimp only [mid, lo, hi] at *; omega)
                have h45 := Nat.mul_le_mul_left 45 hlog
                dsimp only [mid, lo, hi] at h45 ⊢
                omega)
    refine runs_seq_triple_le hloop
      ⟨by simp [startState], by simp [startState], rfl, hLpos, le_refl _,
       fun j hj _ => ⟨Nat.zero_le _, by simp [startState, hj]⟩⟩ ?_
    intro st' ⟨hmem, h3lt, hEqj⟩
    refine runs_ret_le (by eval_expr) ⟨a, rfl, hmem, fun hn => absurd hn hLnil, fun _ => ?_⟩ ?_
    · dsimp only [Outcome.value]
      refine ⟨h3lt, ?_, fun hkm => ?_⟩
      · constructor
        · intro hkm
          have hidx_lt : L.idxOf key < L.length := List.idxOf_lt_length_iff.mpr hkm
          have hEq := hEqj (L.idxOf key) hidx_lt (List.getElem_idxOf hidx_lt)
          have hval : L[st'.regs 3]'h3lt = key := by
            simpa only [← hEq] using List.getElem_idxOf hidx_lt
          rw [List.getElem?_eq_getElem h3lt, hval]
        · intro hget
          have hLk : L[st'.regs 3]'h3lt = key := by
            rw [List.getElem?_eq_getElem h3lt, Option.some.injEq] at hget; exact hget
          exact hLk ▸ List.getElem_mem h3lt
      · have hidx_lt : L.idxOf key < L.length := List.idxOf_lt_length_iff.mpr hkm
        exact (hEqj (L.idxOf key) hidx_lt (List.getElem_idxOf hidx_lt)).symm
    · dsimp only [binSearchOptContract, remFn, logB, Expr.size]
      simp only [startState, Function.update_self, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
        Nat.sub_zero]
      by_cases hl1 : L.length ≤ 1
      · simp [hl1]
      · simp only [hl1, ↓reduceIte]
        have hlog : Nat.log 2 (L.length - 1) ≤ Nat.log 2 (L.length + 1) :=
          Nat.log_mono_right (by omega)
        omega

theorem gtSortDedup_meetsContract {w : ℕ} {p : Program} {b bSort bOps : ℕ}
    {L : List ℕ} {X : Finset ℕ}
    (hp : p.HasAt b (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + gtIdxSortDedup) (gtSortDedupContract w L X) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxSortDedup) (by simp [gtProcs, gtIdxSortDedup]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨src, dst, scratch, rfl, hw16, hsrcB, hdstB, hscrB, hdisjS, hdisjD,
    hLat, hLw, hmemX⟩
  have hlt_src : src < 2 ^ w := hargs src (by simp)
  have hlt_len : L.length < 2 ^ w := hargs L.length (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have hlt_scr : scratch < 2 ^ w := hargs scratch (by simp)
  refine runs_start_le ?_
  dsimp only [gtProcs, gtIdxSortDedup, List.getElem_cons_zero, gtSortDedupStmt]
  have hwords_sort : ∀ v ∈ [src, L.length, scratch], v < 2 ^ w := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_src
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_len
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_scr
    cases hv
  have hpre_sort : (mergeSortContract w L).pre [src, L.length, scratch] mem :=
    ⟨src, scratch, rfl, hw16, hsrcB, hscrB, hdisjS, hLat, hLw⟩
  refine runs_seq_call_le (mergeSort_meetsContract hpSort hpSort) (by eval_expr)
    hwords_sort hpre_sort ?_
  rintro ret1 mem1 _ ⟨src1, sc1, L', heq1, _, hperm, hpair, hLat1, hfr1⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨rfl, _, rfl⟩
  have hlen' : L'.length = L.length := hperm.length_eq
  have hLw' : ∀ x ∈ L', x < 2 ^ w := fun x hx => hLw x (hperm.subset hx)
  have hdedup_eq : sortedDedup L' = vertsOf X :=
    sortedDedup_eq_vertsOf hpair fun x => by rw [hperm.mem_iff, hmemX]
  have hwords_dedup : ∀ v ∈ [src, L'.length, dst], v < 2 ^ w := by
    intro v hv
    rw [hlen'] at hv
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_src
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_len
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_dst
    cases hv
  have hpre_dedup : (dedupContract w L').pre [src, L'.length, dst] mem1 :=
    ⟨src, dst, rfl, hw16, by omega, by omega, by omega, hpair, hLat1, hLw'⟩
  refine runs_seq_call_le (dedup_meetsContract hpSort)
    (by simp [evalArgs, Expr.eval, Function.update_of_ne, hlen', startState])
    hwords_dedup hpre_dedup ?_
  rintro ret2 mem2 _ ⟨src2, dst2, heq2, hret2, _, _, hLat2, hfr2⟩
  simp only [List.cons.injEq, and_true] at heq2
  rcases heq2 with ⟨_, _, rfl⟩
  refine runs_ret_le (by eval_expr) ⟨src, dst, scratch, rfl, ?_, ?_, fun addr has hsc had => ?_⟩ ?_
  · dsimp only [Outcome.value]; rw [hdedup_eq]
  · exact hdedup_eq ▸ hLat2
  · have had' : addr < dst ∨ dst + (sortedDedup L').length ≤ addr := by rwa [hdedup_eq]
    dsimp only
    rw [hfr2 addr had']
    dsimp only
    rw [hfr1 addr has hsc]
    rfl
  · dsimp only [gtSortDedupContract, mergeSortContract, dedupContract, argsSize, Expr.size]
    simp only [hlen']
    have hlog_pos : 1 ≤ Nat.log 2 (L.length + 1) + 1 := Nat.succ_pos _
    have h1 : 45 * L.length ≤ 45 * L.length * (Nat.log 2 (L.length + 1) + 1) := by
      simpa using Nat.mul_le_mul_left (45 * L.length) hlog_pos
    have hsum_mul : 200 * L.length * (Nat.log 2 (L.length + 1) + 1) +
        45 * L.length * (Nat.log 2 (L.length + 1) + 1) ≤
        250 * L.length * (Nat.log 2 (L.length + 1) + 1) := by
      rw [Nat.mul_assoc 200, Nat.mul_assoc 45, Nat.mul_assoc 250, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

end

end MinCostFlow.DynSpanner.Program
