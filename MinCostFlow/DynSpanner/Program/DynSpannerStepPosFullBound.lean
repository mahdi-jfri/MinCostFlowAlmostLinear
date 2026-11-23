module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullDefs
import MinCostFlow.DynSpanner.Program.DynSpannerAffStage

/-!
# The bounds of the whole step for `0 < j` do not depend on the order of the lists

The heap bound `dsStepPosNonEmptyEnd` and the cost `dsStepPosCost` of the last part of the step
take the list of affected edges that the program writes. Its order depends on the run, but the
bounds only use sums over the list and its length. So they are the same for every list that
enumerates `E_aff` without repeats (`dsStepPosNonEmptyEnd_perm`, `dsStepPosCost_perm`), and the
contract of the whole step can state them with `E_aff.toList`. The same holds for the sum
`candRevSum` over the list of `S_{j-1}` (`candRevSum_perm`). The heap bound also grows with the
start of its area and the number of candidates (`dsStepPosNonEmptyEnd_mono`), so the contract
may bound the candidates by `|E(G')|`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

private lemma map_sum_perm {l l' : List ℕ} (hp : l.Perm l') (f : ℕ → ℕ) :
    (l.map f).sum = (l'.map f).sum :=
  (hp.map f).sum_eq

/-- Two lists that enumerate the same set without repeats are permutations of each other. -/
lemma perm_of_nodup_iff {l l' : List ℕ} (hnd : l.Nodup) (hnd' : l'.Nodup)
    (hiff : ∀ e, e ∈ l ↔ e ∈ l') : l.Perm l' :=
  (List.perm_ext_iff_of_nodup hnd hnd').mpr hiff

/-- A list that enumerates a finite set without repeats is a permutation of `S.toList`. -/
lemma perm_toList_of_nodup_iff {l : List ℕ} {S : Finset ℕ} (hnd : l.Nodup)
    (hiff : ∀ e, e ∈ l ↔ e ∈ S) : l.Perm S.toList :=
  perm_of_nodup_iff hnd S.nodup_toList fun e => by rw [hiff, Finset.mem_toList]

lemma dsStepPosNonEmptyEnd_perm (impl : SparsifyImpl) (mMax vCap eCap : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) {l l' : List ℕ} (hp : l.Perm l')
    (wpPtr candLen oldBucketsSum : ℕ) :
    dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH l wpPtr candLen oldBucketsSum =
      dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH l' wpPtr candLen
        oldBucketsSum := by
  simp only [dsStepPosNonEmptyEnd, dsShortcutHeapSpace, reembStageNeed, compHeapNeed,
    reembHeapNeed, map_sum_perm hp, hp.length_eq]

lemma dsStepPosNonEmptyEnd_mono (impl : SparsifyImpl) (mMax vCap eCap : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (l : List ℕ)
    {wpPtr wpPtr' candLen candLen' : ℕ} (oldBucketsSum : ℕ)
    (hwp : wpPtr ≤ wpPtr') (hc : candLen ≤ candLen') :
    dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH l wpPtr candLen oldBucketsSum ≤
      dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH l wpPtr' candLen'
        oldBucketsSum := by
  simp only [dsStepPosNonEmptyEnd, spOutBound]
  omega

lemma dsStepPosCost_perm (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (S_prev : Finset ℕ) {l l' : List ℕ}
    (hp : l.Perm l') (oldBucketsSum sPrevLen prefWords uhLen : ℕ) :
    dsStepPosCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev l oldBucketsSum sPrevLen
        prefWords uhLen =
      dsStepPosCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev l' oldBucketsSum sPrevLen
        prefWords uhLen := by
  simp only [dsStepPosCost, dsStepPosNonEmptyCost, dsSparsifyStageContract, compAllCost,
    reembedAllCost, map_sum_perm hp, hp.length_eq]

lemma dsStepPosCost_mono (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (S_prev : Finset ℕ) (l : List ℕ)
    (oldBucketsSum sPrevLen uhLen : ℕ) {prefWords len : ℕ} (hle : prefWords ≤ len) :
    dsStepPosCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev l oldBucketsSum sPrevLen
        prefWords uhLen ≤
      dsStepPosCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev l oldBucketsSum sPrevLen
        len uhLen := by
  simp only [dsStepPosCost, dsStepPosEpilogueCost]
  omega

lemma candRevSum_perm (L j : ℕ) (revLists : Fin (L + 1) → ℕ → List ℕ) {l l' : List ℕ}
    (hp : l.Perm l') : candRevSum L j revLists l = candRevSum L j revLists l' := by
  simp only [candRevSum, map_sum_perm hp]

/-- The bound `hEnd_ltw` of `StepPosCtx`, for any lists that the program may write, is at most
`dsStepPosFullEnd`. -/
lemma stepPosFull_end_le (m : StepPosModel) (mMax vCap eCap len : ℕ) (x : DynSpannerMeta m.L)
    (heapStep : ℕ) {sPrevList cand eAff : List ℕ} {prefWords : ℕ}
    (hnd : eAff.Nodup) (hiff : ∀ e, e ∈ eAff ↔ e ∈ m.E_aff) (hc : cand.length ≤ m.G'.m)
    (hs : sPrevList.length = m.S_prev.card) (hpw : prefWords ≤ len) :
    (if 0 < eAff.length then
      dsStepPosNonEmptyEnd m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH eAff
        (heapStep + 5 + len + 4 * m.j + 2 + sPrevList.length + cand.length + eAff.length)
        cand.length (stepPosOldSum m.u x m.j)
     else heapStep + 5 + len + 4 * m.j + 2 + sPrevList.length + cand.length + cand.length +
       eCap + 1 + 2 * stepPosOldSum m.u x m.j) + prefWords + 4 * m.res.UH.length + 2 ≤
      dsStepPosFullEnd m mMax vCap eCap len x heapStep := by
  have hcard : eAff.length = m.E_aff.card := list_length_eq_card hnd hiff
  have hp := perm_toList_of_nodup_iff hnd hiff
  simp only [dsStepPosFullEnd]
  rw [← hcard]
  split_ifs with h
  · rw [dsStepPosNonEmptyEnd_perm m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH hp]
    have := dsStepPosNonEmptyEnd_mono m.impl mMax vCap eCap m.G' m.J m.piLt_mid m.embJH
      m.E_aff.toList (stepPosOldSum m.u x m.j)
      (wpPtr := heapStep + 5 + len + 4 * m.j + 2 + sPrevList.length + cand.length + eAff.length)
      (wpPtr' := heapStep + 5 + len + 4 * m.j + 2 + m.S_prev.card + m.G'.m + eAff.length)
      (by omega) hc
    omega
  · omega

/-- The total length of the old buckets of the levels `j, …, L` is below the end of the heap. -/
lemma stepPosOldSum_le_end (m : StepPosModel) (mMax vCap eCap len : ℕ) (x : DynSpannerMeta m.L)
    (heapStep : ℕ) : stepPosOldSum m.u x m.j ≤ dsStepPosFullEnd m mMax vCap eCap len x heapStep := by
  simp only [dsStepPosFullEnd]
  split_ifs
  · simp only [dsStepPosNonEmptyEnd]; omega
  · omega

end

end MinCostFlow.DynSpanner.Program
