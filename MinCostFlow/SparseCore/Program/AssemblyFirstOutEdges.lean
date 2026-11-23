module

public import MinCostFlow.SparseCore.Program.OutSpec
public import MinCostFlow.DynSpanner.Program.MergeSort
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop

/-!
# Choosing and formatting the leaving and entering output edges (`AssemblyFirstOutEdges`)

The output step of a branch (`OutStepInAt`, `OutSpec.lean`) takes two sorted, duplicate-free edge
lists:
* `delL = (tr.S_cur.E \ outKeep ...).sort (· ≤ ·)` formatted as `OutDelAt` (`[|delL|, e₀, flag₀, …]`
  where `flag_i = 1` iff `e_i ∈ cs'.G.E`), and
* `insL = (tr'.S_cur.E \ outKeep ...).sort (· ≤ ·)` formatted as `OutInsAt` (`[|insL|, e₀, tl₀, hd₀,
  …]` where `tl_i, hd_i` are the new roots of `e_i`'s endpoints).

This file provides:
1. Pure model characterizations `outDelSet`, `outInsSet`, `mem_outDelSet_iff`, `mem_outInsSet_iff`,
   and the sort/dedup uniqueness theorem `sortedDedup_perm_eq_finset_sort`: sorting and
   deduplicating any list whose elements form a finset `S` produces `S.sort (· ≤ ·)`.
2. Named memory interfaces `OutSelFlagsAt`, `OutDelFlagsAt`, and `OutInsEndsAt` for the `O(1)`
   membership and endpoint arrays supplied by P4, P5, P6, and the branch's maps.
3. Shared deterministic Word-RAM filter-sort-dedup block `asmFirstFilterSortDedupStmt bSort`
   (calling `sortProcs bSort`'s `mergeSortStmt` and `dedupStmt`), and the two verified builders:
   * `asmFirstBuildDelStmt bSort` (`[supPtr, m, selPtr, inE'Ptr, h]`), writing `delPtr` at `h`,
     `OutDelAt` at `delPtr`, and returning `h' ≤ h + 2 + 5 * m`;
   * `asmFirstBuildInsStmt bSort` (`[supPtr, m, selPtr, tlPtr, hdPtr, h]`), writing `insPtr` at `h`,
     `OutInsAt` at `insPtr`, and returning `h' ≤ h + 2 + 6 * m`.
   Both are deterministic (`NoRand`), allocate linear heap space (free of `limbMul`), satisfy
   `OutCellsFree`, `ZeroFrom`, and frame below `h`, and run in
   `O((m + 1) * (Nat.log 2 (m + 1) + 1))` time.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Model sets and named table interfaces -/

@[expose] public section

/-- The set of leaving output edges of a branch step: `tr.S_cur.E \ outKeep`. -/
noncomputable def outDelSet {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Finset ℕ :=
  tr.S_cur.E \ outKeep sparsify tr U ord ord'

/-- The set of entering output edges of a branch step: `tr'.S_cur.E \ outKeep`. -/
noncomputable def outInsSet {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Finset ℕ :=
  (stepBundleTree sparsify tr U ord ord').state.S_cur.E \ outKeep sparsify tr U ord ord'

/-- Named interface for an `O(1)` membership-flag array `[selPtr, selPtr + eCap)` deciding `S`. -/
def OutSelFlagsAt (mem : ℕ → ℕ) (selPtr eCap : ℕ) (S : Finset ℕ) : Prop :=
  ∀ e < eCap, mem (selPtr + e) = if e ∈ S then 1 else 0

/-- Named interface for the `O(1)` new-graph edge-membership array `[inE'Ptr, inE'Ptr + eCap)`
needed by `OutDelAt`. -/
def OutDelFlagsAt (mem : ℕ → ℕ) (inE'Ptr eCap : ℕ) (E' : Finset ℕ) : Prop :=
  ∀ e < eCap, mem (inE'Ptr + e) = if e ∈ E' then 1 else 0

/-- Named interface for the `O(1)` new-root endpoint arrays `[tlPtr, tlPtr + eCap)` and
`[hdPtr, hdPtr + eCap)` needed by `OutInsAt`. -/
def OutInsEndsAt (mem : ℕ → ℕ) (tlPtr hdPtr eCap : ℕ) (tl hd : ℕ → ℕ) : Prop :=
  ∀ e < eCap, mem (tlPtr + e) = tl e ∧ mem (hdPtr + e) = hd e

/-! ## Word-RAM procedures -/

/-- Shared filter-sort-dedup block used by both builders.
Expects `reg 0 = supPtr`, `reg 1 = m`, `reg 2 = selPtr`, `reg 5 = h + 1`.
Filters `supPtr[0..m)` by `mem[selPtr + e] ≠ 0` into `[h + 1, h + 1 + c)`, merge-sorts it using
scratch `[h + 1 + c, h + 1 + 2*c)`, and deduplicates it into `[h + 1 + 2*c, h + 1 + 2*c + k)`.
Leaves `reg 6 = c`, `reg 9 = h + 1 + 2*c`, `reg 10 = k`. -/
def asmFirstFilterSortDedupStmt (bSort : ℕ) : Stmt :=
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1)
    (.assign 13 (.load (.bin .add (.reg 0) (.reg 7))) ;;
     .assign 14 (.load (.bin .add (.reg 2) (.reg 13))) ;;
     .cond (.reg 14)
       (.store (.bin .add (.reg 5) (.reg 6)) (.reg 13) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1)))
       .nop) ;;
  .assign 8 (.bin .add (.reg 5) (.reg 6)) ;;
  .call 15 (bSort + sortIdxMergeSort) [.reg 5, .reg 6, .reg 8] ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .call 10 (bSort + sortIdxDedup) [.reg 5, .reg 6, .reg 9]

/-- **Builder for `OutDelAt`**, `[supPtr, m, selPtr, inE'Ptr, h]`.
Filters `supPtr[0..m)` by `selPtr`, sorts and deduplicates into `delL`, writes `delPtr` at `h`
and `OutDelAt` (`[|delL|, e₀, flag₀, …]`) at `delPtr`, and returns `h' = delPtr + 1 + 2 * |delL|`. -/
def asmFirstBuildDelStmt (bSort : ℕ) : Stmt :=
  .assign 5 (.bin .add (.reg 4) (.const 1)) ;;
  asmFirstFilterSortDedupStmt bSort ;;
  .assign 11 (.bin .add (.reg 9) (.reg 10)) ;;
  .store (.reg 4) (.reg 11) ;;
  .store (.reg 11) (.reg 10) ;;
  forRange 12 (.const 0) (.reg 10)
    (.assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 2) (.reg 12))) (.reg 13) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 2) (.reg 12))) (.reg 14)) ;;
  .ret (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 2) (.reg 10)))

/-- **Builder for `OutInsAt`**, `[supPtr, m, selPtr, tlPtr, hdPtr, h]`.
Filters `supPtr[0..m)` by `selPtr`, sorts and deduplicates into `insL`, writes `insPtr` at `h`
and `OutInsAt` (`[|insL|, e₀, tl₀, hd₀, …]`) at `insPtr`, and returns
`h' = insPtr + 1 + 3 * |insL|`. -/
def asmFirstBuildInsStmt (bSort : ℕ) : Stmt :=
  .assign 5 (.bin .add (.reg 5) (.const 1)) ;;
  asmFirstFilterSortDedupStmt bSort ;;
  .assign 11 (.bin .add (.reg 9) (.reg 10)) ;;
  .store (.bin .sub (.reg 5) (.const 1)) (.reg 11) ;;
  .store (.reg 11) (.reg 10) ;;
  forRange 12 (.const 0) (.reg 10)
    (.assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
     .assign 15 (.load (.bin .add (.reg 4) (.reg 13))) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 3) (.reg 12))) (.reg 13) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 3) (.reg 12))) (.reg 14) ;;
     .store (.bin .add (.bin .add (.reg 11) (.const 3)) (.bin .mul (.const 3) (.reg 12))) (.reg 15)) ;;
  .ret (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 3) (.reg 10)))

/-- Cost bound of `asmFirstBuildDelStmt` and `asmFirstBuildInsStmt` on a superset of length `m`. -/
def outBuildCost (m : ℕ) : ℕ :=
  380 * (m + 1) * (Nat.log 2 (m + 1) + 1) + 250

end

/-! ## Determinism and pure model lemmas -/

public section

theorem asmFirstBuildDelStmt_noRand (bSort : ℕ) : (asmFirstBuildDelStmt bSort).NoRand := by
  simp [asmFirstBuildDelStmt, asmFirstFilterSortDedupStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstBuildInsStmt_noRand (bSort : ℕ) : (asmFirstBuildInsStmt bSort).NoRand := by
  simp [asmFirstBuildInsStmt, asmFirstFilterSortDedupStmt, forRange, forUp, Stmt.NoRand]

/-- Exact membership characterization of `outDelSet`. -/
theorem mem_outDelSet_iff {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (e : ℕ) :
    e ∈ outDelSet sparsify tr U ord ord' ↔
      e ∈ tr.S_cur.E ∧
        (e ∉ (stepBundleTree sparsify tr U ord ord').state.S_cur.E ∨
          e ∈ batchDeletes U ∨ e ∈ (stepBundleTree sparsify tr U ord ord').D_total) := by
  simp only [outDelSet, outKeep, Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- Exact membership characterization of `outInsSet`. -/
theorem mem_outInsSet_iff {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (e : ℕ) :
    e ∈ outInsSet sparsify tr U ord ord' ↔
      e ∈ (stepBundleTree sparsify tr U ord ord').state.S_cur.E ∧
        (e ∉ tr.S_cur.E ∨ e ∈ batchDeletes U ∨
          e ∈ (stepBundleTree sparsify tr U ord ord').D_total) := by
  simp only [outInsSet, outKeep, Finset.mem_sdiff, Finset.mem_inter]
  tauto

/-- Filtering any superset `supL` of `S` by membership in `S` gives a list whose elements are
exactly those of `S`. -/
theorem filter_superset_mem_iff {supL : List ℕ} {S : Finset ℕ}
    (hsup : ∀ e ∈ S, e ∈ supL) (e : ℕ) :
    e ∈ supL.filter (fun x => decide (x ∈ S)) ↔ e ∈ S := by
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hsup e h, h⟩⟩

/-- Two `≤`-sorted lists of natural numbers that are permutations of each other are equal. -/
private lemma eq_of_perm_of_pairwise_le :
    ∀ {l₁ l₂ : List ℕ}, l₁.Perm l₂ → l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, hp, _, _ => absurd hp.length_eq (by simp)
  | _ :: _, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: as, b :: bs, hp, h1, h2 => by
    simp only [List.pairwise_cons] at h1 h2
    have ha_mem : a ∈ b :: bs := hp.subset List.mem_cons_self
    have hb_mem : b ∈ a :: as := hp.symm.subset List.mem_cons_self
    have hab : a ≤ b := by
      rcases List.mem_cons.mp hb_mem with rfl | hb'
      · exact le_rfl
      · exact h1.1 b hb'
    have hba : b ≤ a := by
      rcases List.mem_cons.mp ha_mem with rfl | ha'
      · exact le_rfl
      · exact h2.1 a ha'
    have hEq : a = b := Nat.le_antisymm hab hba
    subst hEq
    exact congrArg (a :: ·) (eq_of_perm_of_pairwise_le ((List.perm_cons a).mp hp) h1.2 h2.2)

/-- **Sort-and-dedup bridge theorem**: sorting any list `L` whose elements are exactly those of
`S : Finset ℕ` (`L'.Perm L`, `L'.Pairwise (· ≤ ·)`) and then applying `sortedDedup` yields
`S.sort (· ≤ ·)`. -/
theorem sortedDedup_perm_eq_finset_sort {L L' : List ℕ} {S : Finset ℕ}
    (hperm : L'.Perm L) (hpair : L'.Pairwise (· ≤ ·)) (hmem : ∀ x, x ∈ L ↔ x ∈ S) :
    sortedDedup L' = S.sort (· ≤ ·) := by
  have hlt : (sortedDedup L').Pairwise (· < ·) := sortedDedup_pairwise hpair
  have hle : (sortedDedup L').Pairwise (· ≤ ·) := hlt.imp fun h => Nat.le_of_lt h
  have hnd : (sortedDedup L').Nodup := hlt.imp fun h => Nat.ne_of_lt h
  have hmemD : ∀ x, x ∈ sortedDedup L' ↔ x ∈ S.sort (· ≤ ·) := fun x => by
    rw [sortedDedup_mem hpair, hperm.mem_iff, hmem, Finset.mem_sort]
  have hpermS : (sortedDedup L').Perm (S.sort (· ≤ ·)) :=
    (List.perm_ext_iff_of_nodup hnd (S.sort_nodup (· ≤ ·))).mpr hmemD
  exact eq_of_perm_of_pairwise_le hpermS hle (S.pairwise_sort (· ≤ ·))

end

/-! ## Shared filter-sort-dedup verification -/

private lemma sortedDedup_length_le : ∀ (L : List ℕ), (sortedDedup L).length ≤ L.length := by
  have haux : ∀ (prev : ℕ) (xs : List ℕ), (sortedDedupAux prev xs).length ≤ xs.length := by
    intro prev xs
    induction xs generalizing prev with
    | nil => simp [sortedDedupAux]
    | cons x xs ih =>
      unfold sortedDedupAux
      split_ifs
      · exact le_trans (ih prev) (Nat.le_succ _)
      · simp only [List.length_cons]; exact Nat.succ_le_succ (ih x)
  intro L
  cases L with
  | nil => simp [sortedDedup]
  | cons x xs => simp only [sortedDedup, List.length_cons]; exact Nat.succ_le_succ (haux x xs)

private def filterInv (supPtr selPtr base : ℕ) (supL : List ℕ) (S : Finset ℕ) (mem₀ : ℕ → ℕ)
    (r3 r4 : ℕ) (i : ℕ) (st : State) : Prop :=
  let flt := (supL.take i).filter (fun e => decide (e ∈ S))
  st.regs 0 = supPtr ∧ st.regs 1 = supL.length ∧ st.regs 2 = selPtr ∧
  st.regs 3 = r3 ∧ st.regs 4 = r4 ∧ st.regs 5 = base ∧
  st.regs 6 = flt.length ∧ st.regs 7 = i ∧
  ListAt st.mem base flt ∧
  (∀ a, a < base ∨ base + flt.length ≤ a → st.mem a = mem₀ a)

public theorem filterSortDedup_runs {w : ℕ} {p : Program} {bSort : ℕ}
    (hp : p.HasAt bSort (sortProcs bSort))
    {supPtr selPtr eCap h r3 r4 pos : ℕ} {supL : List ℕ} {S : Finset ℕ}
    {mem₀ : ℕ → ℕ} {regs₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hr0 : regs₀ 0 = supPtr) (hr1 : regs₀ 1 = supL.length) (hr2 : regs₀ 2 = selPtr)
    (hr3 : regs₀ 3 = r3) (hr4 : regs₀ 4 = r4) (hr5 : regs₀ 5 = h + 1)
    (hsup : ListAt mem₀ supPtr supL) (hsup_lt : supPtr + supL.length ≤ h)
    (hsup_cap : ∀ e ∈ supL, e < eCap) (hsup_cov : ∀ e ∈ S, e ∈ supL)
    (hsel : OutSelFlagsAt mem₀ selPtr eCap S) (hsel_lt : selPtr + eCap ≤ h)
    (heCap_w : eCap < 2 ^ w)
    (hspace : h + 1 + 3 * supL.length < 2 ^ w) :
    let outL := S.sort (· ≤ ·)
    let fltLen := (supL.filter (fun e => decide (e ∈ S))).length
    ∃ st' c,
      Runs w p ω (asmFirstFilterSortDedupStmt bSort) ⟨mem₀, regs₀, pos⟩ .normal st' c ∧
      st'.regs 0 = supPtr ∧ st'.regs 1 = supL.length ∧ st'.regs 2 = selPtr ∧
      st'.regs 3 = r3 ∧ st'.regs 4 = r4 ∧ st'.regs 5 = h + 1 ∧
      st'.regs 6 = fltLen ∧ st'.regs 9 = h + 1 + 2 * fltLen ∧ st'.regs 10 = outL.length ∧
      fltLen ≤ supL.length ∧ outL.length ≤ fltLen ∧
      ListAt st'.mem (h + 1 + 2 * fltLen) outL ∧
      (∀ a, a < h + 1 ∨ h + 1 + 2 * fltLen + outL.length ≤ a → st'.mem a = mem₀ a) ∧
      c ≤ 280 * supL.length * (Nat.log 2 (supL.length + 1) + 1) + 140 := by
  intro outL fltLen
  have hflt_le : fltLen ≤ supL.length := List.length_filter_le _ _
  have hw1 : 1 < 2 ^ w := by omega
  have hmlt : supL.length < 2 ^ w := by omega
  -- 1. Filter loop.
  have hbody : ∀ i < supL.length,
      Triple w p (filterInv supPtr selPtr (h + 1) supL S mem₀ r3 r4 i)
        (.assign 13 (.load (.bin .add (.reg 0) (.reg 7))) ;;
         .assign 14 (.load (.bin .add (.reg 2) (.reg 13))) ;;
         .cond (.reg 14)
           (.store (.bin .add (.reg 5) (.reg 6)) (.reg 13) ;;
            .assign 6 (.bin .add (.reg 6) (.const 1)))
           .nop)
        (normalPost fun st₁ =>
          filterInv supPtr selPtr (h + 1) supL S mem₀ r3 r4 (i + 1)
            { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧ st₁.regs 7 = i)
        (fun _ => 25) := by
    intro i hi st ω' hInv
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlat, hfr⟩ := hInv
    set flt := (supL.take i).filter (fun e => decide (e ∈ S))
    set e := supL[i]'hi
    have he_cap : e < eCap := hsup_cap e (List.getElem_mem hi)
    have hflt_len_le : flt.length ≤ i := le_trans (List.length_filter_le _ _) (by simp)
    have hmem_e : st.mem (supPtr + i) = e := by
      rw [hfr (supPtr + i) (Or.inl (by omega))]; exact hsup i hi
    have hmem_f : st.mem (selPtr + e) = if e ∈ S then 1 else 0 := by
      rw [hfr (selPtr + e) (Or.inl (by omega))]; exact hsel e he_cap
    have he13 : (Expr.load (.bin .add (.reg 0) (.reg 7))).eval w st = some e :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0) (Expr.eval_reg_of_eq h7)
        (by omega)) hmem_e
    set rA := Function.update st.regs 13 e
    have he14 : (Expr.load (.bin .add (.reg 2) (.reg 13))).eval w ⟨st.mem, rA, st.pos⟩ =
        some (if e ∈ S then 1 else 0) :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, h2]))
        (Expr.eval_reg_of_eq (by simp [rA])) (by omega)) hmem_f
    set rB := Function.update rA 14 (if e ∈ S then 1 else 0)
    have htake_f : (supL.take (i + 1)).filter (fun x => decide (x ∈ S)) =
        if e ∈ S then flt ++ [e] else flt := by
      rw [List.take_succ_eq_append_getElem hi, List.filter_append]
      by_cases heS : e ∈ S <;> simp [flt, e, heS]
    have hr_a13 : Runs w p ω' (.assign 13 (.load (.bin .add (.reg 0) (.reg 7))))
        st .normal ⟨st.mem, rA, st.pos⟩
        ((Expr.load (.bin .add (.reg 0) (.reg 7))).size + 1) :=
      runs_assign_iff.mpr ⟨e, he13, rfl, rfl, rfl⟩
    have hr_a14 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 2) (.reg 13))))
        ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩
        ((Expr.load (.bin .add (.reg 2) (.reg 13))).size + 1) :=
      runs_assign_iff.mpr ⟨if e ∈ S then 1 else 0, he14, rfl, rfl, rfl⟩
    by_cases heS : e ∈ S
    · have heCond : (Expr.reg 14).eval w ⟨st.mem, rB, st.pos⟩ = some 1 :=
        Expr.eval_reg_of_eq (by simp [rB, heS])
      have heAddr : (Expr.bin .add (.reg 5) (.reg 6)).eval w ⟨st.mem, rB, st.pos⟩ =
          some (h + 1 + flt.length) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, h5]))
          (Expr.eval_reg_of_eq (by simp [rB, rA, h6])) (by omega)
      have heVal : (Expr.reg 13).eval w ⟨st.mem, rB, st.pos⟩ = some e :=
        Expr.eval_reg_of_eq (by simp [rB, rA])
      set mem₁ := Function.update st.mem (h + 1 + flt.length) e
      have heInc : (Expr.bin .add (.reg 6) (.const 1)).eval w ⟨mem₁, rB, st.pos⟩ =
          some (flt.length + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, h6])) (Expr.eval_const (by omega))
          (by omega)
      set rC := Function.update rB 6 (flt.length + 1)
      have hr_st : Runs w p ω' (.store (.bin .add (.reg 5) (.reg 6)) (.reg 13))
          ⟨st.mem, rB, st.pos⟩ .normal ⟨mem₁, rB, st.pos⟩
          ((Expr.bin .add (.reg 5) (.reg 6)).size + (Expr.reg 13).size + 1) :=
        runs_store_iff.mpr ⟨h + 1 + flt.length, e, heAddr, heVal, rfl, rfl, rfl⟩
      have hr_inc : Runs w p ω' (.assign 6 (.bin .add (.reg 6) (.const 1)))
          ⟨mem₁, rB, st.pos⟩ .normal ⟨mem₁, rC, st.pos⟩
          ((Expr.bin .add (.reg 6) (.const 1)).size + 1) :=
        runs_assign_iff.mpr ⟨flt.length + 1, heInc, rfl, rfl, rfl⟩
      have hr_cond : Runs w p ω' (.cond (.reg 14) _ .nop) ⟨st.mem, rB, st.pos⟩
          .normal ⟨mem₁, rC, st.pos⟩ _ :=
        runs_cond_iff.mpr ⟨1, _, heCond,
          by simp; exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_st, hr_inc, rfl⟩), rfl⟩
      have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a13,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a14, hr_cond, rfl⟩), rfl⟩)
      refine ⟨.normal, _, _, hr_all, ⟨⟨by simp [rC, rB, rA, h0], by simp [rC, rB, rA, h1],
        by simp [rC, rB, rA, h2], by simp [rC, rB, rA, h3], by simp [rC, rB, rA, h4],
        by simp [rC, rB, rA, h5], by simp [htake_f, heS, rC], by simp, ?_, ?_⟩,
        by simp [rC, rB, rA, h7]⟩, by simp [Expr.size]⟩
      · rw [htake_f]; simp only [heS, ↓reduceIte]
        intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjl | rfl
        · rw [List.getElem_append_left hjl]
          simp only [mem₁, Function.update_of_ne (show h + 1 + j ≠ h + 1 + flt.length by omega)]
          exact hlat j hjl
        · simp [mem₁]
      · rw [htake_f]; simp only [heS, ↓reduceIte]
        intro a ha
        simp only [List.length_append, List.length_singleton] at ha
        simp only [mem₁, Function.update_of_ne (show a ≠ h + 1 + flt.length by omega)]
        exact hfr a (by omega)
    · have heCond : (Expr.reg 14).eval w ⟨st.mem, rB, st.pos⟩ = some 0 :=
        Expr.eval_reg_of_eq (by simp [rB, heS])
      have hr_cond : Runs w p ω'
          (.cond (.reg 14)
            (.store (.bin .add (.reg 5) (.reg 6)) (.reg 13) ;;
             .assign 6 (.bin .add (.reg 6) (.const 1))) .nop)
          ⟨st.mem, rB, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩
          ((Expr.reg 14).size + 1 + 1) :=
        runs_cond_iff.mpr ⟨0, 1, heCond, by simp [runs_nop_iff], rfl⟩
      have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a13,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a14, hr_cond, rfl⟩), rfl⟩)
      refine ⟨.normal, _, _, hr_all, ⟨⟨by simp [rB, rA, h0], by simp [rB, rA, h1],
        by simp [rB, rA, h2], by simp [rB, rA, h3], by simp [rB, rA, h4],
        by simp [rB, rA, h5], by simp [htake_f, heS, rB, rA, h6], by simp,
        by rw [htake_f]; simp only [heS, ↓reduceIte]; exact hlat,
        by rw [htake_f]; simp only [heS, ↓reduceIte]; exact hfr⟩,
        by simp [rB, rA, h7]⟩, by simp [Expr.size]⟩
  have hloop := Triple.forRange_le
    (P := fun st => st.mem = mem₀ ∧ st.regs 0 = supPtr ∧ st.regs 1 = supL.length ∧
      st.regs 2 = selPtr ∧ st.regs 3 = r3 ∧ st.regs 4 = r4 ∧ st.regs 5 = h + 1 ∧ st.regs 6 = 0)
    (fun _ => 25) 0 supL.length (Nat.zero_le _) hw1 (fun _ => hmlt)
    (fun st ⟨hm, h0, h1, h2, h3, h4, h5, h6⟩ =>
      ⟨Expr.eval_const (by omega), by simp [filterInv, h0, h1, h2, h3, h4, h5, h6, hm]⟩)
    (fun i st _ _ hInv => hInv.2.2.2.2.2.2.2.1)
    (fun i st _ _ hInv => Expr.eval_reg_of_eq hInv.2.1)
    (fun i _ hi => hbody i hi)
  set r0' := Function.update regs₀ 6 0
  have hr_a6 : Runs w p ω (.assign 6 (.const 0)) ⟨mem₀, regs₀, pos⟩ .normal ⟨mem₀, r0', pos⟩
      ((Expr.const 0).size + 1) :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  obtain ⟨oL, st1, c1, hr_loop, hpost1, hc1⟩ := hloop ⟨mem₀, r0', pos⟩ ω
    ⟨rfl, by simp [r0', hr0], by simp [r0', hr1], by simp [r0', hr2], by simp [r0', hr3],
     by simp [r0', hr4], by simp [r0', hr5], by simp [r0']⟩
  cases oL with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨h10, h11, h12, h13, h14, h15, h16, -, hlat1, hfr1⟩ := hpost1
  rw [List.take_length] at h16 hlat1 hfr1
  set fltL := supL.filter (fun e => decide (e ∈ S))
  have hfltL_len : fltL.length = fltLen := rfl
  have hfltL_w : ∀ x ∈ fltL, x < 2 ^ w := fun x hx =>
    lt_trans (hsup_cap x (List.mem_of_mem_filter hx)) heCap_w
  -- 2. `reg 8 := reg 5 + reg 6`, call `mergeSort [reg 5, reg 6, reg 8]`.
  set r2 := Function.update st1.regs 8 (h + 1 + fltLen)
  have hr_a8 : Runs w p ω (.assign 8 (.bin .add (.reg 5) (.reg 6))) st1 .normal
      ⟨st1.mem, r2, st1.pos⟩ ((Expr.bin .add (.reg 5) (.reg 6)).size + 1) :=
    runs_assign_iff.mpr ⟨h + 1 + fltLen,
      Expr.eval_add (Expr.eval_reg_of_eq h15) (Expr.eval_reg_of_eq h16) (by omega), rfl, rfl, rfl⟩
  have hms := mergeSort_meetsContract (w := w) (L := fltL) hp hp
    [h + 1, fltLen, h + 1 + fltLen] st1.mem st1.pos ω
    (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
    ⟨h + 1, h + 1 + fltLen, rfl, hw16, by omega, by omega, Or.inl (by omega), hlat1, hfltL_w⟩
  obtain ⟨bdMS, hbdMS, oMS, st2, cMS, hrunMS, hpostMS, hcMS⟩ := hms
  obtain ⟨_, _, sortedL, heqMS, _, hperm, hpair, hlat2, hfrMS⟩ := hpostMS
  simp only [List.cons.injEq, and_true] at heqMS
  rcases heqMS with ⟨rfl, -, rfl⟩
  have hsorted_len : sortedL.length = fltLen := hperm.length_eq
  have hsorted_w : ∀ x ∈ sortedL, x < 2 ^ w := fun x hx => hfltL_w x (hperm.subset hx)
  set r3' := Function.update r2 15 oMS.value
  have heArgsMS : evalArgs w ⟨st1.mem, r2, st1.pos⟩ [.reg 5, .reg 6, .reg 8] =
      some [h + 1, fltLen, h + 1 + fltLen] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, h15])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, h16, hfltL_len])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2])) <| evalArgs_nil _ _
  have hr_ms : Runs w p ω (.call 15 (bSort + sortIdxMergeSort) [.reg 5, .reg 6, .reg 8])
      ⟨st1.mem, r2, st1.pos⟩ .normal ⟨st2.mem, r3', st2.pos⟩
      (argsSize [.reg 5, .reg 6, .reg 8] + cMS + 1) :=
    runs_call_iff.mpr ⟨_, bdMS, oMS, st2, cMS, heArgsMS, hbdMS, hrunMS, rfl, rfl, rfl⟩
  -- 3. `reg 9 := reg 8 + reg 6`, call `dedup [reg 5, reg 6, reg 9]`.
  set r4' := Function.update r3' 9 (h + 1 + 2 * fltLen)
  have hr_a9 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 6))) ⟨st2.mem, r3', st2.pos⟩
      .normal ⟨st2.mem, r4', st2.pos⟩ ((Expr.bin .add (.reg 8) (.reg 6)).size + 1) := by
    have hsum9 : (h + 1 + fltLen) + fltLen = h + 1 + 2 * fltLen := by omega
    refine runs_assign_iff.mpr ⟨h + 1 + 2 * fltLen, ?_, rfl, rfl, rfl⟩
    rw [← hsum9]
    exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3', r2]))
      (Expr.eval_reg_of_eq (by simp [r3', r2, h16, hfltL_len])) (by omega)
  have hdd := dedup_meetsContract (w := w) (L := sortedL) hp
    [h + 1, sortedL.length, h + 1 + 2 * fltLen] st2.mem st2.pos ω
    (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
    ⟨h + 1, h + 1 + 2 * fltLen, rfl, hw16, by omega, by omega, Or.inl (by omega),
      hpair, hlat2, hsorted_w⟩
  obtain ⟨bdDD, hbdDD, oDD, st3, cDD, hrunDD, hpostDD, hcDD⟩ := hdd
  obtain ⟨_, _, heqDD, hretDD, -, -, hlat3, hfrDD⟩ := hpostDD
  simp only [List.cons.injEq, and_true] at heqDD
  rcases heqDD with ⟨rfl, -, rfl⟩
  have hout_eq : sortedDedup sortedL = outL :=
    sortedDedup_perm_eq_finset_sort hperm hpair (filter_superset_mem_iff hsup_cov)
  have hout_len_le : outL.length ≤ fltLen := by
    rw [← hout_eq, ← hsorted_len]; exact sortedDedup_length_le sortedL
  set r5' := Function.update r4' 10 oDD.value
  have heArgsDD : evalArgs w ⟨st2.mem, r4', st2.pos⟩ [.reg 5, .reg 6, .reg 9] =
      some [h + 1, sortedL.length, h + 1 + 2 * fltLen] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4', r3', r2, h15])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4', r3', r2, h16, hfltL_len, hsorted_len])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4'])) <| evalArgs_nil _ _
  have hr_dd : Runs w p ω (.call 10 (bSort + sortIdxDedup) [.reg 5, .reg 6, .reg 9])
      ⟨st2.mem, r4', st2.pos⟩ .normal ⟨st3.mem, r5', st3.pos⟩
      (argsSize [.reg 5, .reg 6, .reg 9] + cDD + 1) :=
    runs_call_iff.mpr ⟨_, bdDD, oDD, st3, cDD, heArgsDD, hbdDD, hrunDD, rfl, rfl, rfl⟩
  have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a6,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_loop,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a8,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_ms,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a9, hr_dd, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨⟨st3.mem, r5', st3.pos⟩, _, hr_all,
    by simp [r5', r4', r3', r2, h10], by simp [r5', r4', r3', r2, h11],
    by simp [r5', r4', r3', r2, h12], by simp [r5', r4', r3', r2, h13],
    by simp [r5', r4', r3', r2, h14], by simp [r5', r4', r3', r2, h15],
    by simp [r5', r4', r3', r2, h16, hfltL_len], by simp [r5', r4'],
    by simp [r5', hretDD, hout_eq], hflt_le, hout_len_le,
    by rw [← hout_eq]; exact hlat3, ?_, ?_⟩
  · intro a ha
    rw [hfrDD a (by rw [hout_eq]; rcases ha with hlt | hge <;> [exact Or.inl (by omega); exact Or.inr hge])]
    rw [hfrMS a (by rcases ha with hlt | hge <;> [exact Or.inl hlt; exact Or.inr (by omega)])
      (by rcases ha with hlt | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
    exact hfr1 a (by rcases ha with hlt | hge <;> [exact Or.inl hlt; exact Or.inr (by omega)])
  · have hrc1 : rangeCost (fun _ => 25) 0 supL.length = 25 * supL.length := by
      simp [rangeCost, Nat.mul_comm]
    dsimp only at hc1
    dsimp only [mergeSortContract, dedupContract] at hcMS hcDD
    simp only [Expr.size, argsSize, Nat.sub_zero, hrc1, hsorted_len, hfltL_len] at hc1 hcMS hcDD ⊢
    have hlog : Nat.log 2 (fltLen + 1) ≤ Nat.log 2 (supL.length + 1) :=
      Nat.log_mono_right (by omega)
    have hmul : 200 * fltLen * (Nat.log 2 (fltLen + 1) + 1) ≤
        200 * supL.length * (Nat.log 2 (supL.length + 1) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 200 hflt_le) (Nat.succ_le_succ hlog)
    have hlin : 80 * supL.length ≤ 80 * supL.length * (Nat.log 2 (supL.length + 1) + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hdist : 200 * supL.length * (Nat.log 2 (supL.length + 1) + 1) +
        80 * supL.length * (Nat.log 2 (supL.length + 1) + 1) =
        280 * supL.length * (Nat.log 2 (supL.length + 1) + 1) := by
      rw [← Nat.add_mul, ← Nat.add_mul]
    omega

/-! ## Verification of `asmFirstBuildDelStmt` and `asmFirstBuildInsStmt` -/

public section

/-- **Verification of `asmFirstBuildDelStmt bSort` (`OutDelAt`)**: given any superset `supL` of
`S` (such as `outDelSet sparsify tr U ord ord'`) and `O(1)` membership tables `OutSelFlagsAt` and
`OutDelFlagsAt`, writes `delPtr` at `h`, writes `OutDelAt st'.mem delPtr (S.sort (· ≤ ·)) E'` with
`OutCellsFree` against any `avoid` lying below `h`, preserves memory below `h`, maintains
`ZeroFrom`, uses at most `2 + 5 * supL.length` words of heap, and runs in
`O((supL.length + 1) * (Nat.log 2 (supL.length + 1) + 1))` time. -/
theorem asmFirstBuildDel_runs {w : ℕ} {p : Program} {bSort : ℕ}
    (hp : p.HasAt bSort (sortProcs bSort))
    {supPtr selPtr inE'Ptr eCap h pos : ℕ} {supL : List ℕ} {S E' : Finset ℕ}
    {avoid : ℕ → Prop} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hsup : ListAt mem₀ supPtr supL) (hsup_lt : supPtr + supL.length ≤ h)
    (hsup_cap : ∀ e ∈ supL, e < eCap) (hsup_cov : ∀ e ∈ S, e ∈ supL)
    (hsel : OutSelFlagsAt mem₀ selPtr eCap S) (hsel_lt : selPtr + eCap ≤ h)
    (hdelF : OutDelFlagsAt mem₀ inE'Ptr eCap E') (hdelF_lt : inE'Ptr + eCap ≤ h)
    (havoid : ∀ a, avoid a → a < h)
    (heCap_w : eCap < 2 ^ w)
    (hz : ZeroFrom mem₀ h)
    (hspace : h + 2 + 5 * supL.length < 2 ^ w) :
    let delL := S.sort (· ≤ ·)
    ∃ o st' c,
      Runs w p ω (asmFirstBuildDelStmt bSort)
        (startState [supPtr, supL.length, selPtr, inE'Ptr, h] mem₀ pos) o st' c ∧
      OutDelAt st'.mem (st'.mem h) delL E' ∧
      OutCellsFree (st'.mem h) (1 + 2 * delL.length) o.value avoid ∧
      h + 1 ≤ st'.mem h ∧ st'.mem h < o.value ∧
      h + 2 ≤ o.value ∧ o.value ≤ h + 2 + 5 * supL.length ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ outBuildCost supL.length := by
  intro delL
  have hw1 : 1 < 2 ^ w := by omega
  set st0 := startState [supPtr, supL.length, selPtr, inE'Ptr, h] mem₀ pos
  set r0 := Function.update st0.regs 5 (h + 1)
  have hr_a5 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.const 1))) st0 .normal
      ⟨mem₀, r0, pos⟩ ((Expr.bin .add (.reg 4) (.const 1)).size + 1) :=
    runs_assign_iff.mpr ⟨h + 1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  obtain ⟨st1, c1, hr_fsd, h10, h11, h12, h13, h14, h15, h16, h19, h110,
      hflt_le, hdel_le, hlat1, hfr1, hc1⟩ :=
    filterSortDedup_runs (r3 := inE'Ptr) (r4 := h) (regs₀ := r0) (pos := pos) (ω := ω) hp hw16
      (by simp [r0, st0, startState]) (by simp [r0, st0, startState])
      (by simp [r0, st0, startState]) (by simp [r0, st0, startState])
      (by simp [r0, st0, startState]) (by simp [r0])
      hsup hsup_lt hsup_cap hsup_cov hsel hsel_lt heCap_w (by omega)
  set fltLen := (supL.filter (fun e => decide (e ∈ S))).length
  have hdl_le : delL.length ≤ fltLen := hdel_le
  set outPtr := h + 1 + 2 * fltLen
  set delPtr := outPtr + delL.length
  have hdp_eq : delPtr = h + 1 + 2 * fltLen + delL.length := rfl
  set r1 := Function.update st1.regs 11 delPtr
  have hr_a11 : Runs w p ω (.assign 11 (.bin .add (.reg 9) (.reg 10))) st1 .normal
      ⟨st1.mem, r1, st1.pos⟩ ((Expr.bin .add (.reg 9) (.reg 10)).size + 1) :=
    runs_assign_iff.mpr ⟨delPtr,
      Expr.eval_add (Expr.eval_reg_of_eq h19) (Expr.eval_reg_of_eq h110) (by omega), rfl, rfl, rfl⟩
  set mem2 := Function.update st1.mem h delPtr
  have hr_sh : Runs w p ω (.store (.reg 4) (.reg 11)) ⟨st1.mem, r1, st1.pos⟩ .normal
      ⟨mem2, r1, st1.pos⟩ ((Expr.reg 4).size + (Expr.reg 11).size + 1) :=
    runs_store_iff.mpr ⟨h, delPtr,
      Expr.eval_reg_of_eq (by simp [r1, h14]), Expr.eval_reg_of_eq (by simp [r1]), rfl, rfl, rfl⟩
  set mem3 := Function.update mem2 delPtr delL.length
  have hr_sd : Runs w p ω (.store (.reg 11) (.reg 10)) ⟨mem2, r1, st1.pos⟩ .normal
      ⟨mem3, r1, st1.pos⟩ ((Expr.reg 11).size + (Expr.reg 10).size + 1) :=
    runs_store_iff.mpr ⟨delPtr, delL.length,
      Expr.eval_reg_of_eq (by simp [r1]),
      Expr.eval_reg_of_eq (by simp only [r1, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), h110]; rfl),
      rfl, rfl, rfl⟩
  -- Write loop over `j = 0 .. delL.length - 1`.
  let WInv : ℕ → State → Prop := fun j st =>
    st.regs 3 = inE'Ptr ∧ st.regs 9 = outPtr ∧ st.regs 10 = delL.length ∧
    st.regs 11 = delPtr ∧ st.regs 12 = j ∧
    st.mem h = delPtr ∧ st.mem delPtr = delL.length ∧
    (∀ i < j, st.mem (delPtr + 1 + 2 * i) = delL.getD i 0 ∧
      st.mem (delPtr + 2 + 2 * i) = if delL.getD i 0 ∈ E' then 1 else 0) ∧
    (∀ a, a < delPtr + 1 ∨ delPtr + 1 + 2 * j ≤ a → st.mem a = mem3 a)
  have hWbody : ∀ j < delL.length,
      Triple w p (WInv j)
        (.assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
         .assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
         .store (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 2) (.reg 12))) (.reg 13) ;;
         .store (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 2) (.reg 12))) (.reg 14))
        (normalPost fun st₁ =>
          WInv (j + 1) { st₁ with regs := Function.update st₁.regs 12 (j + 1) } ∧ st₁.regs 12 = j)
        (fun _ => 45) := by
    intro j hj st ω' ⟨hr3, hr9, hr10, hr11, hr12, hmh, hmd, hout, hfrW⟩
    set e := delL[j]'hj
    have he_S : e ∈ S := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hj)
    have he_cap : e < eCap := hsup_cap e (hsup_cov e he_S)
    have hme : st.mem (outPtr + j) = e := by
      rw [hfrW (outPtr + j) (Or.inl (by omega))]
      simp only [mem3, mem2, Function.update_of_ne (show outPtr + j ≠ delPtr by omega),
        Function.update_of_ne (show outPtr + j ≠ h by omega)]
      exact hlat1 j hj
    have hmf : st.mem (inE'Ptr + e) = if e ∈ E' then 1 else 0 := by
      rw [hfrW (inE'Ptr + e) (Or.inl (by omega))]
      simp only [mem3, mem2, Function.update_of_ne (show inE'Ptr + e ≠ delPtr by omega),
        Function.update_of_ne (show inE'Ptr + e ≠ h by omega)]
      rw [hfr1 (inE'Ptr + e) (Or.inl (by omega))]
      exact hdelF e he_cap
    have he13 : (Expr.load (.bin .add (.reg 9) (.reg 12))).eval w st = some e :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_reg_of_eq hr12)
        (by omega)) hme
    set rA := Function.update st.regs 13 e
    have he14 : (Expr.load (.bin .add (.reg 3) (.reg 13))).eval w ⟨st.mem, rA, st.pos⟩ =
        some (if e ∈ E' then 1 else 0) :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr3]))
        (Expr.eval_reg_of_eq (by simp [rA])) (by omega)) hmf
    set rB := Function.update rA 14 (if e ∈ E' then 1 else 0)
    have heA1 : (Expr.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 2) (.reg 12))).eval w
        ⟨st.mem, rB, st.pos⟩ = some (delPtr + 1 + 2 * j) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr11]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rB, rA, hr12]))
          (by omega)) (by omega)
    set mA := Function.update st.mem (delPtr + 1 + 2 * j) e
    have heA2 : (Expr.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 2) (.reg 12))).eval w
        ⟨mA, rB, st.pos⟩ = some (delPtr + 2 + 2 * j) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr11]))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rB, rA, hr12]))
          (by omega)) (by omega)
    set mB := Function.update mA (delPtr + 2 + 2 * j) (if e ∈ E' then 1 else 0)
    have hr13 : Runs w p ω' (.assign 13 _) st .normal ⟨st.mem, rA, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨e, he13, rfl, rfl, rfl⟩
    have hr14 : Runs w p ω' (.assign 14 _) ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨_, he14, rfl, rfl, rfl⟩
    have hrS1 : Runs w p ω' (.store _ (.reg 13)) ⟨st.mem, rB, st.pos⟩ .normal ⟨mA, rB, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨_, e, heA1, Expr.eval_reg_of_eq (by simp [rB, rA]), rfl, rfl, rfl⟩
    have hrS2 : Runs w p ω' (.store _ (.reg 14)) ⟨mA, rB, st.pos⟩ .normal ⟨mB, rB, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨_, _, heA2, Expr.eval_reg_of_eq (by simp [rB]), rfl, rfl, rfl⟩
    have hrAll := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr13,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr14,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS1, hrS2, rfl⟩), rfl⟩), rfl⟩)
    refine ⟨.normal, _, _, hrAll, ⟨⟨by simp [rB, rA, hr3], by simp [rB, rA, hr9],
      by simp [rB, rA, hr10], by simp [rB, rA, hr11], by simp,
      by simp [mB, mA, Function.update_of_ne (show h ≠ delPtr + 2 + 2 * j by omega),
          Function.update_of_ne (show h ≠ delPtr + 1 + 2 * j by omega), hmh],
      by simp [mB, mA, Function.update_of_ne (show delPtr ≠ delPtr + 2 + 2 * j by omega),
          Function.update_of_ne (show delPtr ≠ delPtr + 1 + 2 * j by omega), hmd],
      ?_, ?_⟩, by simp [rB, rA, hr12]⟩, by simp [Expr.size]⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hij | heq
      · simp only [mB, mA, Function.update_of_ne (show delPtr + 1 + 2 * i ≠ delPtr + 2 + 2 * j by omega),
          Function.update_of_ne (show delPtr + 1 + 2 * i ≠ delPtr + 1 + 2 * j by omega),
          Function.update_of_ne (show delPtr + 2 + 2 * i ≠ delPtr + 2 + 2 * j by omega),
          Function.update_of_ne (show delPtr + 2 + 2 * i ≠ delPtr + 1 + 2 * j by omega)]
        exact hout i hij
      · subst heq
        have hgetD : delL.getD i 0 = e := List.getD_eq_getElem _ _ hj
        rw [hgetD]
        simp [mB, mA]
    · intro a ha
      simp only [mB, mA, Function.update_of_ne (show a ≠ delPtr + 2 + 2 * j by omega),
        Function.update_of_ne (show a ≠ delPtr + 1 + 2 * j by omega)]
      exact hfrW a (by omega)
  have hWloop := Triple.forRange_le
    (P := fun st => st.mem = mem3 ∧ st.regs 3 = inE'Ptr ∧ st.regs 9 = outPtr ∧
      st.regs 10 = delL.length ∧ st.regs 11 = delPtr)
    (fun _ => 45) 0 delL.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hm, hr3, hr9, hr10, hr11⟩ =>
      ⟨Expr.eval_const (by omega),
       ⟨by simp [hr3], by simp [hr9], by simp [hr10], by simp [hr11], by simp,
        by simp [hm, mem3, mem2, Function.update_of_ne (show h ≠ delPtr by omega)],
        by simp [hm, mem3], fun i hi => absurd hi (Nat.not_lt_zero _),
        fun a _ => by rw [hm]⟩⟩)
    (fun j st _ _ hI => hI.2.2.2.2.1)
    (fun j st _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun j _ hj => hWbody j hj)
  obtain ⟨oW, stW, cW, hrW, hpostW, hcW⟩ := hWloop ⟨mem3, r1, st1.pos⟩ ω
    ⟨rfl, by simp [r1, h13], by simp [r1, h19],
     by simp only [r1, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), h110]; rfl, by simp [r1]⟩
  cases oW with
  | returned _ => cases hpostW
  | normal =>
  obtain ⟨-, -, hr10W, hr11W, -, hmhW, hmdW, houtW, hfrW⟩ := hpostW
  have hdl_le : delL.length ≤ fltLen := hdel_le
  have hdp_eq : delPtr = h + 1 + 2 * fltLen + delL.length := rfl
  set hEnd := delPtr + 1 + 2 * delL.length
  have hend_eq : hEnd = delPtr + 1 + 2 * delL.length := rfl
  have heRet : (Expr.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .mul (.const 2) (.reg 10))).eval w stW =
      some hEnd :=
    Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr11W) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr10W) (by omega)) (by omega)
  have hr_ret : Runs w p ω (.ret _) stW (.returned hEnd) stW _ :=
    runs_ret_iff.mpr ⟨hEnd, heRet, rfl, rfl, rfl⟩
  have hr_full := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a5,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_fsd,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a11,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_sh,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_sd,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrW, hr_ret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned hEnd, stW, _, hr_full, ?_, ?_, by rw [hmhW]; omega,
    by simp only [Outcome.value]; rw [hmhW]; omega,
    by simp only [Outcome.value]; omega, by simp only [Outcome.value]; omega, ?_, ?_, ?_⟩
  · rw [hmhW]; exact ⟨hmdW, houtW⟩
  · rw [hmhW]
    exact ⟨by simp only [Outcome.value]; omega, fun i _ ha => by have := havoid _ ha; omega⟩
  · intro a ha
    change hEnd ≤ a at ha
    rw [hfrW a (Or.inr ha)]
    simp only [mem3, mem2, Function.update_of_ne (show a ≠ delPtr by omega),
      Function.update_of_ne (show a ≠ h by omega)]
    rw [hfr1 a (Or.inr (by omega))]
    exact hz a (by omega)
  · intro a ha
    rw [hfrW a (Or.inl (by omega))]
    simp only [mem3, mem2, Function.update_of_ne (show a ≠ delPtr by omega),
      Function.update_of_ne (show a ≠ h by omega)]
    exact hfr1 a (Or.inl (by omega))
  · have hrcW : rangeCost (fun _ => 45) 0 delL.length = 45 * delL.length := by
      simp [rangeCost, Nat.mul_comm]
    dsimp only at hcW
    simp only [outBuildCost, Expr.size, Nat.sub_zero, hrcW] at hcW ⊢
    have hdl : delL.length ≤ supL.length := le_trans hdel_le hflt_le
    set L := Nat.log 2 (supL.length + 1) + 1
    have hL1 : 1 ≤ L := Nat.succ_pos _
    have h100 : 100 * supL.length ≤ 100 * supL.length * L := Nat.le_mul_of_pos_right _ hL1
    have hdist : 280 * supL.length * L + 100 * supL.length * L ≤ 380 * (supL.length + 1) * L := by
      have : 280 * supL.length * L + 100 * supL.length * L = 380 * supL.length * L := by
        rw [← Nat.add_mul, ← Nat.add_mul]
      rw [this]
      exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left 380 (Nat.le_succ _))
    clear hmdW hmhW
    omega

end

end MinCostFlow.SparseCore.Program
