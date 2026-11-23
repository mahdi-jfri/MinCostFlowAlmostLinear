module

public import MinCostFlow.HierPaths.BuildProgBatchSpec
import MinCostFlow.HierPaths.InitLayout

/-!
# Layout of a batched injection

A pair takes one child's worth of terminal words, with an explicit
offset for the boundary between its two sides.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The injection has fixed row sizes and a variable source size. -/
def InjectWritten (mem : ℕ → ℕ) (out s : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  mem (out + 2*pairs.length) = pairs.length*s ∧
  ∀ i < pairs.length,
    mem (out+2*i) = i*s ∧ mem (out+2*i+1) = i*s+(pairs.getD i (∅,∅)).1.card ∧
    ListAt mem (out+2*pairs.length+1+i*s) (buildBatchRow pairs i)

private theorem inject_get_sections (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ)
    (hi : i < pairs.length) :
    let bs := pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]
    let p := pairs.getD i (∅, ∅)
    bs.getD (2 * i) [] = finsetWords p.1 ∧ bs.getD (2 * i + 1) [] = finsetWords p.2 := by
  induction pairs generalizing i with
  | nil => simp at hi
  | cons p pairs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hx : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      simpa only [hx, List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ]
        using ih i (by simp only [List.length_cons] at hi; omega)

/-- The complete pair block ends immediately after its final terminal. -/
theorem injectPairsWords_length {s : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hs : ∀ i < pairs.length, (buildBatchRow pairs i).length = s) :
    (pairsWords pairs).length = 2*pairs.length+1+pairs.length*s := by
  have hSum : ((pairs.flatMap fun p => [finsetWords p.1,finsetWords p.2]).map List.length).sum =
      pairs.length*s := by
    induction pairs with
    | nil => simp
    | cons a l ih =>
      have hHead := hs 0 (by simp)
      change ((finsetWords a.1) ++ (finsetWords a.2)).length = s at hHead
      rw [List.length_append] at hHead
      have hTail := ih (fun i hi => hs (i+1) (by simp; omega))
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,
        List.sum_cons,List.length_cons,Nat.succ_mul]
      omega
  rw [pairsWords,length_layoutList,batch_sections_length,hSum]

/-- The injection table is a router input, even with unequal side sizes. -/
theorem InjectWritten.pairsAt {mem : ℕ → ℕ} {out s : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hAt : InjectWritten mem out s pairs)
    (hSizes : ∀ i < pairs.length, (buildBatchRow pairs i).length = s) :
    ListAt mem out (pairsWords pairs) := by
  obtain ⟨hLast,hRows⟩ := hAt
  let bs := pairs.flatMap fun p => [finsetWords p.1,finsetWords p.2]
  have hLen : bs.length = 2*pairs.length := batch_sections_length pairs
  let left := fun i => (pairs.getD i (∅,∅)).1.card
  let right := fun i => (pairs.getD i (∅,∅)).2.card
  let e := fun j => (j/2)*s + if j%2 = 0 then 0 else left (j/2)
  have hL (i : ℕ) : e (2*i) = i*s := by
    have hD : (2*i)/2 = i := by omega
    have hM : (2*i)%2 = 0 := by omega
    simp [e,hD,hM]
  have hR (i : ℕ) : e (2*i+1) = i*s+left i := by
    have hD : (2*i+1)/2 = i := by omega
    simp [e,hD]
  have hSec (i : ℕ) (hi : i < pairs.length) :
      (bs.getD (2*i) []).length = left i ∧ (bs.getD (2*i+1) []).length = right i := by
    obtain ⟨hl,hr⟩ := inject_get_sections pairs i hi
    change bs.getD (2*i) [] = _ at hl
    change bs.getD (2*i+1) [] = _ at hr
    rw [hl,hr]
    simp [left,right,finsetWords]
  have hSum (i : ℕ) (hi : i < pairs.length) : left i + right i = s := by
    simpa [buildBatchRow,finsetWords,left,right] using hSizes i hi
  have hSplit (j : ℕ) : j = 2*(j/2) ∨ j = 2*(j/2)+1 := by omega
  change ListAt mem out (layoutList bs)
  refine listAt_layoutList_of_starts (e := e) (by simpa using hL 0) ?_ ?_ ?_
  · intro j hj
    let i := j/2
    have hi : i < pairs.length := by dsimp [i]; omega
    obtain ⟨hl,hr⟩ := hSec i hi
    rcases hSplit j with he | he
    · have hEq : j = 2*i := he
      rw [hEq,hR,hL,hl]
    · have hEq : j = 2*i+1 := he
      rw [hEq,show 2*i+1+1 = 2*(i+1) by omega,hL,hR,hr,Nat.succ_mul]
      have hh := hSum i hi
      omega
  · intro j hj
    by_cases he : j = bs.length
    · rw [he,hLen,hL]
      exact hLast
    have hi : j/2 < pairs.length := by omega
    obtain ⟨hl,hr,_⟩ := hRows _ hi
    rcases hSplit j with he | he
    · calc mem (out+j) = mem (out+2*(j/2)) := by rw [← he]
          _ = (j/2)*s := hl
          _ = e j := ((congrArg e he).trans (hL _)).symm
    · calc mem (out+j) = mem (out+2*(j/2)+1) := by rw [Nat.add_assoc,← he]
          _ = (j/2)*s+left (j/2) := hr
          _ = e j := ((congrArg e he).trans (hR _)).symm
  · intro j hj
    have hi : j/2 < pairs.length := by omega
    obtain ⟨_,_,hRow⟩ := hRows _ hi
    obtain ⟨hl,hr⟩ := inject_get_sections pairs (j/2) hi
    change bs.getD (2*(j/2)) [] = _ at hl
    change bs.getD (2*(j/2)+1) [] = _ at hr
    obtain ⟨ha,hb⟩ := listAt_append.mp hRow
    rcases hSplit j with he | he
    · have hj' : bs.getD j [] = _ := he.symm ▸ hl
      rw [hLen, (congrArg e he).trans (hL _), hj']
      exact ha
    · have hj' : bs.getD j [] = _ := he.symm ▸ hr
      rw [hLen, (congrArg e he).trans (hR _), hj']
      simpa [buildBatchRow,left,finsetWords,Nat.add_assoc] using hb

end MinCostFlow.HierPaths
