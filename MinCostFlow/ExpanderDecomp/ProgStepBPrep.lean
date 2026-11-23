module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBPrim
public import MinCostFlow.ExpanderDecomp.ProgStepCLeftoverBase

import Mathlib.Tactic.Linarith

/-!
# Step B Per-Block Subroutines (`ProgStepBPrep`)

Implements and verifies two local (`NoRand`, zero scan of `range G.n`, restoring `locAddr` to
all zeros) per-block building blocks for Step B:
- `sbSaveExpStmt` / `sbSaveExp_triple`: given an expander subset `S` returned by `bSubCore`,
  partitions `blockList vs b i` into sorted `S` and `B \ S` directly into `savDst` / `cmpDst`.
- `sbPadBisectStmt` / `sbPadBisect_triple`: given a cut `U` returned by `bSubCore`, computes
  `C' = padToHalf B (smallerSide B U)` and `B \ C'` as sorted lists of length `b / 2` and writes
  `[b / 2, C'..., b / 2, (B \ C')...]` at `pPtr`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Expander

/-! ## 1. Save Expander Subset (`sbSaveExpStmt`) -/

/-- Mark `S` (`r30`, len `r31`) in `locAddr` (`r8`), partition `blockList` (`r28`, len `r4`) into
`savDst` (`r32`) and `cmpDst` (`r33`), and unmark `S`. Outputs `r34 = |S|`, `r35 = |B \ S|`.
Modifies only `r34..r38`. -/
def sbSaveExpStmt : Stmt :=
  seqStmts [
    .assign 36 (.const 1),
    sbMarkListStmt 30 31 8 36 37 38,
    sbPartitionStmt 28 4 8 32 33 34 35 37 38,
    .assign 36 (.const 0),
    sbMarkListStmt 30 31 8 36 37 38
  ]

theorem sbSaveExpStmt_noRand : sbSaveExpStmt.NoRand := by
  simp [sbSaveExpStmt, sbMarkListStmt, sbPartitionStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Triple for `sbSaveExpStmt`: writes sorted `S` at `savDst` and sorted `B \ S` at `cmpDst`,
restores `locAddr` to all zeros, and runs in at most `96 * b + 110` steps. -/
theorem sbSaveExp_triple {w n b blkA sA sLen locA savDst cmpDst : ℕ}
    {p : Program} {mem : ℕ → ℕ} {B_l S_l : List ℕ} {S : Finset ℕ} {st₀ : State}
    (hB_len : B_l.length = b) (hB_lt : B_l.Pairwise (· < ·))
    (hB_sub : ∀ u ∈ B_l, u < n) (hB_at : ListAt mem blkA B_l)
    (hS_len : S_l.length = sLen) (hS_le : sLen ≤ b)
    (hS_fin : S_l.toFinset = S) (hS_sub : S ⊆ B_l.toFinset)
    (hS_at : ListAt mem sA S_l)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hd_loc_blk : DisjointRange locA n blkA b)
    (hd_loc_s : DisjointRange locA n sA sLen)
    (hd_sav_blk : DisjointRange savDst b blkA b)
    (hd_sav_loc : DisjointRange savDst b locA n)
    (hd_sav_s : DisjointRange savDst b sA sLen)
    (hd_cmp_blk : DisjointRange cmpDst b blkA b)
    (hd_cmp_loc : DisjointRange cmpDst b locA n)
    (hd_cmp_s : DisjointRange cmpDst b sA sLen)
    (hd_sav_cmp : DisjointRange savDst b cmpDst b)
    (hblk_w : blkA + b < 2 ^ w) (hs_w : sA + sLen < 2 ^ w)
    (hloc_w : locA + n < 2 ^ w) (hsav_w : savDst + b < 2 ^ w)
    (hcmp_w : cmpDst + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA)
    (hr28 : st₀.regs 28 = blkA) (hr30 : st₀.regs 30 = sA) (hr31 : st₀.regs 31 = sLen)
    (hr32 : st₀.regs 32 = savDst) (hr33 : st₀.regs 33 = cmpDst)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbSaveExpStmt
      (normalPost fun st' =>
        st'.regs 34 = S.card ∧
        st'.regs 35 = (B_l.toFinset \ S).card ∧
        (∀ r < 34, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < savDst ∨ savDst + b ≤ a) →
          (a < cmpDst ∨ cmpDst + b ≤ a) → st'.mem a = mem a) ∧
        ListAt st'.mem savDst (S.sort (· ≤ ·)) ∧
        ListAt st'.mem cmpDst ((B_l.toFinset \ S).sort (· ≤ ·)))
      (fun _ => 96 * b + 110) := by
  have hS_lt : ∀ u ∈ S_l, u < n := fun u hu =>
    hB_sub u (List.mem_toFinset.mp (hS_sub (hS_fin ▸ List.mem_toFinset.mpr hu)))
  have hpart := filter_blockList_inter_sdiff hB_lt hS_sub
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbSaveExpStmt, seqStmts]
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (w := w) (by omega)) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 36 1, pos := st₀.pos }
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := sLen) (sa := sA) (la := locA) (val := 1)
      (rSrc := 30) (rLen := 31) (rLoc := 8) (rVal := 36) (rI := 37) (rU := 38)
      (by decide) p mem S_l st1 hS_len hS_at hS_lt hd_loc_s hs_w hloc_w hw16
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hr30])
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hr31])
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), hr8])
      (by dsimp only [st1]; rw [Function.update_self]) hmem) rfl ?_
  intro st2 ⟨hoth2, hpos2, hfr2, hloc2⟩
  have hB_at2 : ListAt st2.mem blkA B_l := fun j hj => by
    have hdisj : blkA + j < locA ∨ locA + n ≤ blkA + j := by
      rcases hd_loc_blk with h | h <;> [right; left] <;> omega
    rw [hfr2 _ hdisj]; exact hB_at j hj
  have hloc2_iff : ∀ u < n, (st2.mem (locA + u) = 0 ↔ u ∉ S) := fun u hu => by
    rw [hloc2 u hu, hS_fin, hloc0 u hu]; by_cases h : u ∈ S <;> simp [h]
  refine runs_seq_triple_le
    (sbPartition_triple (w := w) (n := n) (len := b) (sa := blkA) (la := locA)
      (inA := savDst) (outA := cmpDst) (rSrc := 28) (rLen := 4) (rLoc := 8)
      (rInDst := 32) (rOutDst := 33) (rInCnt := 34) (rOutCnt := 35) (rI := 37) (rU := 38)
      (by decide) p st2.mem B_l S st2 hB_len hB_at2 hB_sub hloc2_iff
      hd_sav_blk hd_sav_loc hd_cmp_blk hd_cmp_loc hd_sav_cmp
      hblk_w hloc_w hsav_w hcmp_w hw16
      (by rw [hoth2 28 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr28])
      (by rw [hoth2 4 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr4])
      (by rw [hoth2 8 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr8])
      (by rw [hoth2 32 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr32])
      (by rw [hoth2 33 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr33])
      rfl) rfl ?_
  intro st3 ⟨hcntI3, hcntO3, hoth3, hpos3, hfr3, hin3, hout3⟩
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
  let st4 : State := { mem := st3.mem, regs := Function.update st3.regs 36 0, pos := st3.pos }
  have hS_at3 : ListAt st3.mem sA S_l := fun j hj => by
    have h1 : sA + j < savDst ∨ savDst + b ≤ sA + j := by rcases hd_sav_s with h | h <;> [right; left] <;> omega
    have h2 : sA + j < cmpDst ∨ cmpDst + b ≤ sA + j := by rcases hd_cmp_s with h | h <;> [right; left] <;> omega
    have h3 : sA + j < locA ∨ locA + n ≤ sA + j := by rcases hd_loc_s with h | h <;> [right; left] <;> omega
    rw [hfr3 _ h1 h2, hfr2 _ h3]; exact hS_at j hj
  refine runs_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := sLen) (sa := sA) (la := locA) (val := 0)
      (rSrc := 30) (rLen := 31) (rLoc := 8) (rVal := 36) (rI := 37) (rU := 38)
      (by decide) p st3.mem S_l st4 hS_len hS_at3 hS_lt hd_loc_s hs_w hloc_w hw16
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 30 (by decide) (by decide) (by decide) (by decide),
            hoth2 30 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr30])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 31 (by decide) (by decide) (by decide) (by decide),
            hoth2 31 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr31])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 8 (by decide) (by decide) (by decide) (by decide),
            hoth2 8 (by decide) (by decide)]; dsimp only [st1]; rw [Function.update_of_ne (by decide), hr8])
      (by dsimp only [st4]; rw [Function.update_self]) rfl) rfl ?_
    (by simp only [Expr.size]; omega)
  rintro (_ | _) st5 h5
  · rcases h5 with ⟨hoth5, hpos5, hfr5, hloc5⟩
    have hr34_5 : st5.regs 34 = S.card := by
      rw [hoth5 34 (by decide) (by decide)]
      dsimp only [st4]; rw [Function.update_of_ne (by decide), hcntI3, hpart.1, Finset.length_sort]
    have hr35_5 : st5.regs 35 = (B_l.toFinset \ S).card := by
      rw [hoth5 35 (by decide) (by decide)]
      dsimp only [st4]; rw [Function.update_of_ne (by decide), hcntO3, hpart.2, Finset.length_sort]
    refine ⟨hr34_5, hr35_5, fun r hr => ?_, by rw [hpos5, hpos3, hpos2], ?_, ?_, ?_, ?_⟩
    · rw [hoth5 r (by omega) (by omega)]
      dsimp only [st4]; rw [Function.update_of_ne (by omega),
        hoth3 r (by omega) (by omega) (by omega) (by omega), hoth2 r (by omega) (by omega)]
      dsimp only [st1]; rw [Function.update_of_ne (by omega)]
    · intro u hu
      rw [hloc5 u hu]
      by_cases hmemS : u ∈ S_l.toFinset
      · simp [hmemS]
      · simp only [hmemS, ↓reduceIte]
        have h1 : locA + u < savDst ∨ savDst + b ≤ locA + u := by rcases hd_sav_loc with h | h <;> [right; left] <;> omega
        have h2 : locA + u < cmpDst ∨ cmpDst + b ≤ locA + u := by rcases hd_cmp_loc with h | h <;> [right; left] <;> omega
        rw [hfr3 _ h1 h2, hloc2 u hu]; simp [hmemS, hloc0 u hu]
    · intro a ha_loc ha_sav ha_cmp
      rw [hfr5 a ha_loc, hfr3 a ha_sav ha_cmp, hfr2 a ha_loc]
    · rw [← hpart.1]; intro j hj
      have hj_lt : j < b := by have := List.length_filter_le (fun u => decide (u ∈ S)) B_l; omega
      have hdisj : savDst + j < locA ∨ locA + n ≤ savDst + j := by rcases hd_sav_loc with h | h <;> [left; right] <;> omega
      rw [hfr5 _ hdisj]; exact hin3 j hj
    · rw [← hpart.2]; intro j hj
      have hj_lt : j < b := by have := List.length_filter_le (fun u => decide (u ∉ S)) B_l; omega
      have hdisj : cmpDst + j < locA ∨ locA + n ≤ cmpDst + j := by rcases hd_cmp_loc with h | h <;> [left; right] <;> omega
      rw [hfr5 _ hdisj]; exact hout3 j hj
  · exact False.elim h5

/-! ## 2. Smaller-Side + Pad-to-Half Bisection (`sbPadBisectStmt`) -/

/-- Given `blockList` at `r28` (len `r4 = b`), cut `U` at `r30` (len `r31`), zeroed `locAddr` (`r8`),
scratch `tmpA = r24`, `tmpB = tmpA + b`, `tmpC = tmpA + 2*b`, `tmpD = tmpA + 3*b`, and pair output
pointer `pPtr = r26`: computes sorted `C' = padToHalf B (smallerSide B U)` and `B \ C'` (each of
length `b / 2`), writes `[b / 2, C'..., b / 2, (B \ C')...]` at `pPtr`, and restores `locAddr` to
all zeros. Modifies only `r32..r44`. -/
def sbPadBisectStmt : Stmt :=
  seqStmts [
    .assign 32 (.bin .add (.reg 24) (.reg 4)),
    .assign 33 (.bin .add (.reg 32) (.reg 4)),
    .assign 34 (.bin .add (.reg 33) (.reg 4)),
    -- 1. Partition B by U into tmpA (r24, cnt r35) and tmpB (r32, cnt r36)
    .assign 41 (.const 1),
    sbMarkListStmt 30 31 8 41 42 43,
    sbPartitionStmt 28 4 8 24 32 35 36 42 43,
    .assign 41 (.const 0),
    sbMarkListStmt 30 31 8 41 42 43,
    -- 2. Pick smaller side C (r37, len r38) and remainder rem (r39), padLen r40 = b/2 - r38
    .cond (.bin .lt (.reg 36) (.reg 35))
      (seqStmts [.assign 37 (.reg 32), .assign 38 (.reg 36), .assign 39 (.reg 24)])
      (seqStmts [.assign 37 (.reg 24), .assign 38 (.reg 35), .assign 39 (.reg 32)]),
    .assign 44 (.bin .div (.reg 4) (.const 2)),
    .assign 40 (.bin .sub (.reg 44) (.reg 38)),
    -- 3. Mark C and rem[0..padLen-1], partition B into tmpC (r33) and tmpD (r34), unmark
    .assign 41 (.const 1),
    sbMarkListStmt 37 38 8 41 42 43,
    sbMarkListStmt 39 40 8 41 42 43,
    sbPartitionStmt 28 4 8 33 34 35 36 42 43,
    .assign 41 (.const 0),
    sbMarkListStmt 37 38 8 41 42 43,
    sbMarkListStmt 39 40 8 41 42 43,
    -- 4. Write [halfB, C'..., halfB, comp...] at pPtr (r26)
    .store (.reg 26) (.reg 44),
    .assign 41 (.bin .add (.reg 26) (.const 1)),
    scCopySliceStmt 33 41 44 42 43,
    .store (.bin .add (.reg 41) (.reg 44)) (.reg 44),
    .assign 41 (.bin .add (.bin .add (.reg 41) (.reg 44)) (.const 1)),
    scCopySliceStmt 34 41 44 42 43
  ]

theorem sbPadBisectStmt_noRand : sbPadBisectStmt.NoRand := by
  simp [sbPadBisectStmt, sbMarkListStmt, sbPartitionStmt, scCopySliceStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-- Second half of `sbPadBisectStmt` (steps 3–4): marks `C_list` and `pad_list` in `locAddr`,
partitions `B_l` into `(tmpC, tmpD)`, unmarks `C_list` and `pad_list`, and copies the two halves
into `[b/2, C'..., b/2, (B \ C')...]` at `pPtr`. -/
private def sbPadBisectTailStmt : Stmt :=
  seqStmts [
    .assign 44 (.bin .div (.reg 4) (.const 2)),
    .assign 40 (.bin .sub (.reg 44) (.reg 38)),
    .assign 41 (.const 1),
    sbMarkListStmt 37 38 8 41 42 43,
    sbMarkListStmt 39 40 8 41 42 43,
    sbPartitionStmt 28 4 8 33 34 35 36 42 43,
    .assign 41 (.const 0),
    sbMarkListStmt 37 38 8 41 42 43,
    sbMarkListStmt 39 40 8 41 42 43,
    .store (.reg 26) (.reg 44),
    .assign 41 (.bin .add (.reg 26) (.const 1)),
    scCopySliceStmt 33 41 44 42 43,
    .store (.bin .add (.reg 41) (.reg 44)) (.reg 44),
    .assign 41 (.bin .add (.bin .add (.reg 41) (.reg 44)) (.const 1)),
    scCopySliceStmt 34 41 44 42 43
  ]

private lemma sbPadBisect_tail {w n b blkA locA tmpA pPtr cA remA : ℕ}
    {p : Program} {mem5 : ℕ → ℕ} {B_l C_list pad_list : List ℕ} {C' : Finset ℕ} {st6 : State} {ω : ℕ → Bool}
    (hb_even : Even b) (hB_len : B_l.length = b) (hB_sub : ∀ u ∈ B_l, u < n)
    (hB_at5 : ListAt mem5 blkA B_l)
    (hC_le : C_list.length ≤ b / 2) (hpad_len : pad_list.length = b / 2 - C_list.length)
    (hC_lt : ∀ u ∈ C_list, u < n) (hpad_lt : ∀ u ∈ pad_list, u < n)
    (hC_at5 : ListAt mem5 cA C_list) (hpad_at5 : ListAt mem5 remA pad_list)
    (hC'_union : C' = C_list.toFinset ∪ pad_list.toFinset)
    (hC'_sort_eq : B_l.filter (fun u => decide (u ∈ C')) = C'.sort (· ≤ ·))
    (hcomp_sort_eq : B_l.filter (fun u => decide (u ∉ C')) = (B_l.toFinset \ C').sort (· ≤ ·))
    (hC'_sort_len : (C'.sort (· ≤ ·)).length = b / 2)
    (hcomp_sort_len : ((B_l.toFinset \ C').sort (· ≤ ·)).length = b / 2)
    (hloc0_5 : ∀ u < n, mem5 (locA + u) = 0)
    (hd_loc_blk : DisjointRange locA n blkA b)
    (hd_loc_tmp : DisjointRange locA n tmpA (4 * b))
    (hd_loc_p : DisjointRange locA n pPtr (2 + b))
    (hd_tmp_blk : DisjointRange tmpA (4 * b) blkA b)
    (hd_tmp_p : DisjointRange tmpA (4 * b) pPtr (2 + b))
    (hcA_in_tmp : tmpA ≤ cA ∧ cA + C_list.length ≤ tmpA + 2 * b)
    (hremA_in_tmp : tmpA ≤ remA ∧ remA + pad_list.length ≤ tmpA + 2 * b)
    (hblk_w : blkA + b < 2 ^ w) (hloc_w : locA + n < 2 ^ w)
    (htmp_w : tmpA + 4 * b < 2 ^ w) (hp_w : pPtr + 2 + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st6.regs 4 = b) (hr8 : st6.regs 8 = locA)
    (hr26 : st6.regs 26 = pPtr) (hr28 : st6.regs 28 = blkA)
    (hr33 : st6.regs 33 = tmpA + 2 * b) (hr34 : st6.regs 34 = tmpA + 3 * b)
    (hr37 : st6.regs 37 = cA) (hr38 : st6.regs 38 = C_list.length) (hr39 : st6.regs 39 = remA)
    (hmem6 : st6.mem = mem5) :
    ∃ o st' c',
      Runs w p ω sbPadBisectTailStmt st6 o st' c' ∧
      (normalPost fun st' =>
        (∀ r < 32, st'.regs r = st6.regs r) ∧
        st'.pos = st6.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA + 2 * b ∨ tmpA + 4 * b ≤ a) →
          (a < pPtr ∨ pPtr + 2 + b ≤ a) → st'.mem a = mem5 a) ∧
        st'.mem pPtr = b / 2 ∧
        ListAt st'.mem (pPtr + 1) (C'.sort (· ≤ ·)) ∧
        st'.mem (pPtr + 1 + b / 2) = b / 2 ∧
        ListAt st'.mem (pPtr + 2 + b / 2) ((B_l.toFinset \ C').sort (· ≤ ·))) o st' ∧
      0 + c' ≤ 170 * b + 230 := by
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  set pad_len := b / 2 - C_list.length
  dsimp only [sbPadBisectTailStmt, seqStmts]
  refine runs_seq_assign_le (v := b / 2)
    (Expr.eval_div (Expr.eval_reg_of_eq hr4) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := pad_len)
    (Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr38])) (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (w := w) (by omega)) ?_
  let st7 : State :=
    { mem := st6.mem,
      regs := Function.update (Function.update (Function.update st6.regs 44 (b / 2)) 40 pad_len) 41 1,
      pos := st6.pos }
  have hd_loc_cA : DisjointRange locA n cA C_list.length := by
    rcases hd_loc_tmp with h | h <;> [left; right] <;> omega
  have hd_loc_remA : DisjointRange locA n remA pad_len := by
    rcases hd_loc_tmp with h | h <;> [left; right] <;> omega
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := C_list.length) (sa := cA) (la := locA) (val := 1)
      (rSrc := 37) (rLen := 38) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p mem5 C_list st7 rfl hC_at5 hC_lt hd_loc_cA (by omega) hloc_w hw16
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr37])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr38])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by dsimp only [st7]; rw [Function.update_self]) hmem6) rfl ?_
  intro st8 ⟨hoth8, hpos8, hfr8, hloc8⟩
  have hpad_at8 : ListAt st8.mem remA pad_list := fun j hj => by
    rw [hfr8 _ (by rcases hd_loc_remA with h | h <;> [right; left] <;> omega)]; exact hpad_at5 j hj
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := pad_len) (sa := remA) (la := locA) (val := 1)
      (rSrc := 39) (rLen := 40) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p st8.mem pad_list st8 hpad_len hpad_at8 hpad_lt hd_loc_remA (by omega) hloc_w hw16
      (by rw [hoth8 39 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr39])
      (by rw [hoth8 40 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by rw [hoth8 8 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by rw [hoth8 41 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_self]) rfl) rfl ?_
  intro st9 ⟨hoth9, hpos9, hfr9, hloc9⟩
  have hB_at9 : ListAt st9.mem blkA B_l := fun j hj => by
    have h1 : blkA + j < locA ∨ locA + n ≤ blkA + j := by rcases hd_loc_blk with h | h <;> [right; left] <;> omega
    rw [hfr9 _ h1, hfr8 _ h1]; exact hB_at5 j hj
  have hloc9_iff : ∀ u < n, (st9.mem (locA + u) = 0 ↔ u ∉ C') := fun u hu => by
    rw [hloc9 u hu, hloc8 u hu, hloc0_5 u hu, hC'_union]
    by_cases h1 : u ∈ pad_list.toFinset <;> by_cases h2 : u ∈ C_list.toFinset <;> simp [h1, h2]
  have hd_tC_blk : DisjointRange (tmpA + 2 * b) b blkA b := by rcases hd_tmp_blk with h | h <;> [left; right] <;> omega
  have hd_tC_loc : DisjointRange (tmpA + 2 * b) b locA n := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
  have hd_tD_blk : DisjointRange (tmpA + 3 * b) b blkA b := by rcases hd_tmp_blk with h | h <;> [left; right] <;> omega
  have hd_tD_loc : DisjointRange (tmpA + 3 * b) b locA n := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
  refine runs_seq_triple_le
    (sbPartition_triple (w := w) (n := n) (len := b) (sa := blkA) (la := locA)
      (inA := tmpA + 2 * b) (outA := tmpA + 3 * b) (rSrc := 28) (rLen := 4) (rLoc := 8)
      (rInDst := 33) (rOutDst := 34) (rInCnt := 35) (rOutCnt := 36) (rI := 42) (rU := 43)
      (by decide) p st9.mem B_l C' st9 hB_len hB_at9 hB_sub hloc9_iff
      hd_tC_blk hd_tC_loc hd_tD_blk hd_tD_loc (Or.inl (by omega))
      hblk_w hloc_w (by omega) (by omega) hw16
      (by rw [hoth9 28 (by decide) (by decide), hoth8 28 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr28])
      (by rw [hoth9 4 (by decide) (by decide), hoth8 4 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4])
      (by rw [hoth9 8 (by decide) (by decide), hoth8 8 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by rw [hoth9 33 (by decide) (by decide), hoth8 33 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr33])
      (by rw [hoth9 34 (by decide) (by decide), hoth8 34 (by decide) (by decide)]; dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr34])
      rfl) rfl ?_
  intro st10 ⟨_, _, hoth10, hpos10, hfr10, hC'10, hcomp10⟩
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
  let st11 : State := { mem := st10.mem, regs := Function.update st10.regs 41 0, pos := st10.pos }
  have hC_at10 : ListAt st10.mem cA C_list := fun j hj => by
    have h2 : cA + j < locA ∨ locA + n ≤ cA + j := by rcases hd_loc_cA with h | h <;> [right; left] <;> omega
    rw [hfr10 _ (Or.inl (by omega)) (Or.inl (by omega)), hfr9 _ h2, hfr8 _ h2]; exact hC_at5 j hj
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := C_list.length) (sa := cA) (la := locA) (val := 0)
      (rSrc := 37) (rLen := 38) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p st10.mem C_list st11 rfl hC_at10 hC_lt hd_loc_cA (by omega) hloc_w hw16
      (by dsimp only [st11]; rw [Function.update_of_ne (by decide), hoth10 37 (by decide) (by decide) (by decide) (by decide),
            hoth9 37 (by decide) (by decide), hoth8 37 (by decide) (by decide)]; dsimp only [st7]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr37])
      (by dsimp only [st11]; rw [Function.update_of_ne (by decide), hoth10 38 (by decide) (by decide) (by decide) (by decide),
            hoth9 38 (by decide) (by decide), hoth8 38 (by decide) (by decide)]; dsimp only [st7]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr38])
      (by dsimp only [st11]; rw [Function.update_of_ne (by decide), hoth10 8 (by decide) (by decide) (by decide) (by decide),
            hoth9 8 (by decide) (by decide), hoth8 8 (by decide) (by decide)]; dsimp only [st7]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by dsimp only [st11]; rw [Function.update_self]) rfl) rfl ?_
  intro st12 ⟨hoth12, hpos12, hfr12, hloc12⟩
  have hpad_at12 : ListAt st12.mem remA pad_list := fun j hj => by
    have h2 : remA + j < locA ∨ locA + n ≤ remA + j := by rcases hd_loc_remA with h | h <;> [right; left] <;> omega
    rw [hfr12 _ h2, hfr10 _ (Or.inl (by omega)) (Or.inl (by omega)), hfr9 _ h2, hfr8 _ h2]; exact hpad_at5 j hj
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := pad_len) (sa := remA) (la := locA) (val := 0)
      (rSrc := 39) (rLen := 40) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p st12.mem pad_list st12 hpad_len hpad_at12 hpad_lt hd_loc_remA (by omega) hloc_w hw16
      (by rw [hoth12 39 (by decide) (by decide)]; dsimp only [st11]; rw [Function.update_of_ne (by decide),
            hoth10 39 (by decide) (by decide) (by decide) (by decide), hoth9 39 (by decide) (by decide), hoth8 39 (by decide) (by decide)]
          dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr39])
      (by rw [hoth12 40 (by decide) (by decide)]; dsimp only [st11]; rw [Function.update_of_ne (by decide),
            hoth10 40 (by decide) (by decide) (by decide) (by decide), hoth9 40 (by decide) (by decide), hoth8 40 (by decide) (by decide)]
          dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by rw [hoth12 8 (by decide) (by decide)]; dsimp only [st11]; rw [Function.update_of_ne (by decide),
            hoth10 8 (by decide) (by decide) (by decide) (by decide), hoth9 8 (by decide) (by decide), hoth8 8 (by decide) (by decide)]
          dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8])
      (by rw [hoth12 41 (by decide) (by decide)]; dsimp only [st11]; rw [Function.update_self]) rfl) rfl ?_
  intro st13 ⟨hoth13, hpos13, hfr13, hloc13⟩
  have hloc0_13 : ∀ u < n, st13.mem (locA + u) = 0 := fun u hu => by
    rw [hloc13 u hu]; by_cases hp : u ∈ pad_list.toFinset
    · simp [hp]
    · simp only [hp, ↓reduceIte]; rw [hloc12 u hu]; by_cases hc : u ∈ C_list.toFinset
      · simp [hc]
      · simp only [hc, ↓reduceIte]
        have h1 : locA + u < tmpA + 2 * b ∨ tmpA + 2 * b + b ≤ locA + u := by rcases hd_loc_tmp with h | h <;> [left; right] <;> omega
        have h2 : locA + u < tmpA + 3 * b ∨ tmpA + 3 * b + b ≤ locA + u := by rcases hd_loc_tmp with h | h <;> [left; right] <;> omega
        rw [hfr10 _ h1 h2, hloc9 u hu, hloc8 u hu]; simp [hp, hc, hloc0_5 u hu]
  have hst13_lt32 : ∀ r < 32, st13.regs r = st6.regs r := fun r hr => by
    rw [hoth13 r (by omega) (by omega), hoth12 r (by omega) (by omega)]; dsimp only [st11]
    rw [Function.update_of_ne (by omega), hoth10 r (by omega) (by omega) (by omega) (by omega),
      hoth9 r (by omega) (by omega), hoth8 r (by omega) (by omega)]; dsimp only [st7]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hr33_13 : st13.regs 33 = tmpA + 2 * b := by
    rw [hoth13 33 (by decide) (by decide), hoth12 33 (by decide) (by decide)]; dsimp only [st11]
    rw [Function.update_of_ne (by decide), hoth10 33 (by decide) (by decide) (by decide) (by decide),
      hoth9 33 (by decide) (by decide), hoth8 33 (by decide) (by decide)]; dsimp only [st7]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr33]
  have hr34_13 : st13.regs 34 = tmpA + 3 * b := by
    rw [hoth13 34 (by decide) (by decide), hoth12 34 (by decide) (by decide)]; dsimp only [st11]
    rw [Function.update_of_ne (by decide), hoth10 34 (by decide) (by decide) (by decide) (by decide),
      hoth9 34 (by decide) (by decide), hoth8 34 (by decide) (by decide)]; dsimp only [st7]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr34]
  have hr44_13 : st13.regs 44 = b / 2 := by
    rw [hoth13 44 (by decide) (by decide), hoth12 44 (by decide) (by decide)]; dsimp only [st11]
    rw [Function.update_of_ne (by decide), hoth10 44 (by decide) (by decide) (by decide) (by decide),
      hoth9 44 (by decide) (by decide), hoth8 44 (by decide) (by decide)]; dsimp only [st7]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  refine runs_seq_store_le (x := pPtr) (v := b / 2)
    (Expr.eval_reg_of_eq ((hst13_lt32 26 (by decide)).trans hr26)) (Expr.eval_reg_of_eq hr44_13) ?_
  refine runs_seq_assign_le (v := pPtr + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hst13_lt32 26 (by decide)).trans hr26)) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  let mem14 := Function.update st13.mem pPtr (b / 2)
  let st14 : State := { mem := mem14, regs := Function.update st13.regs 41 (pPtr + 1), pos := st13.pos }
  have hC'_at14 : ListAt mem14 (tmpA + 2 * b) (C'.sort (· ≤ ·)) := fun j hj => by
    have hj_b : j < b := by omega
    have hne : tmpA + 2 * b + j ≠ pPtr := by rcases hd_tmp_p with h | h <;> omega
    have hloc_disj : tmpA + 2 * b + j < locA ∨ locA + n ≤ tmpA + 2 * b + j := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
    simp only [mem14, Function.update_of_ne hne]
    rw [hfr13 _ hloc_disj, hfr12 _ hloc_disj]
    have := hC'10 j (hC'_sort_eq.symm ▸ hj); simpa only [hC'_sort_eq] using this
  refine runs_seq_triple_le
    (scCopySlice_triple (srcA := tmpA + 2 * b) (dstA := pPtr + 1) (len := b / 2)
      (rSrc := 33) (rDst := 41) (rLen := 44) (rI := 42) (rTmp := 43) (by decide) p mem14
      (C'.sort (· ≤ ·)) st14 hC'_sort_len hC'_at14
      (by rcases hd_tmp_p with h | h <;> [right; left] <;> omega) (by omega) (by omega) hw16
      (by dsimp only [st14]; rw [Function.update_of_ne (by decide), hr33_13])
      (by dsimp only [st14]; rw [Function.update_self])
      (by dsimp only [st14]; rw [Function.update_of_ne (by decide), hr44_13]) rfl) rfl ?_
  intro st15 ⟨hoth15, hpos15, hfr15, hC'_dst⟩
  refine runs_seq_store_le (x := pPtr + 1 + b / 2) (v := b / 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hoth15 41 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_self]))
      (Expr.eval_reg_of_eq (by rw [hoth15 44 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_of_ne (by decide), hr44_13]))
      (by omega))
    (Expr.eval_reg_of_eq (by rw [hoth15 44 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_of_ne (by decide), hr44_13])) ?_
  refine runs_seq_assign_le (v := pPtr + 2 + b / 2)
    (by have heq : pPtr + 1 + b / 2 + 1 = pPtr + 2 + b / 2 := by omega
        exact heq ▸ Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (by rw [hoth15 41 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_self]))
          (Expr.eval_reg_of_eq (by rw [hoth15 44 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_of_ne (by decide), hr44_13]))
          (by omega)) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  let mem16 := Function.update st15.mem (pPtr + 1 + b / 2) (b / 2)
  let st16 : State := { mem := mem16, regs := Function.update st15.regs 41 (pPtr + 2 + b / 2), pos := st15.pos }
  have hcomp_at16 : ListAt mem16 (tmpA + 3 * b) ((B_l.toFinset \ C').sort (· ≤ ·)) := fun j hj => by
    have hj_b : j < b := by omega
    have hne1 : tmpA + 3 * b + j ≠ pPtr + 1 + b / 2 := by rcases hd_tmp_p with h | h <;> omega
    have hne2 : tmpA + 3 * b + j ≠ pPtr := by rcases hd_tmp_p with h | h <;> omega
    have hp_disj : tmpA + 3 * b + j < pPtr + 1 ∨ pPtr + 1 + b / 2 ≤ tmpA + 3 * b + j := by rcases hd_tmp_p with h | h <;> [left; right] <;> omega
    have hloc_disj : tmpA + 3 * b + j < locA ∨ locA + n ≤ tmpA + 3 * b + j := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
    simp only [mem16, Function.update_of_ne hne1]
    rw [hfr15 _ hp_disj]
    simp only [mem14, Function.update_of_ne hne2]
    rw [hfr13 _ hloc_disj, hfr12 _ hloc_disj]
    have := hcomp10 j (hcomp_sort_eq.symm ▸ hj); simpa only [hcomp_sort_eq] using this
  refine runs_triple_le
    (scCopySlice_triple (srcA := tmpA + 3 * b) (dstA := pPtr + 2 + b / 2) (len := b / 2)
      (rSrc := 34) (rDst := 41) (rLen := 44) (rI := 42) (rTmp := 43) (by decide) p mem16
      ((B_l.toFinset \ C').sort (· ≤ ·)) st16 hcomp_sort_len hcomp_at16
      (by rcases hd_tmp_p with h | h <;> [right; left] <;> omega) (by omega) (by omega) hw16
      (by dsimp only [st16]; rw [Function.update_of_ne (by decide), hoth15 34 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_of_ne (by decide), hr34_13])
      (by dsimp only [st16]; rw [Function.update_self])
      (by dsimp only [st16]; rw [Function.update_of_ne (by decide), hoth15 44 (by decide) (by decide)]; dsimp only [st14]; rw [Function.update_of_ne (by decide), hr44_13]) rfl) rfl ?_
    (by simp only [Expr.size]; omega)
  rintro (_ | _) st17 h17
  · rcases h17 with ⟨hoth17, hpos17, hfr17, hcomp_dst⟩
    refine ⟨fun r hr => ?_, by rw [hpos17, hpos15, hpos13, hpos12, hpos10, hpos9, hpos8], ?_, ?_, ?_, ?_, ?_, hcomp_dst⟩
    · rw [hoth17 r (by omega) (by omega)]; dsimp only [st16]
      rw [Function.update_of_ne (by omega), hoth15 r (by omega) (by omega)]; dsimp only [st14]
      rw [Function.update_of_ne (by omega), hst13_lt32 r hr]
    · intro u hu
      have hp1 : locA + u < pPtr + 2 + b / 2 ∨ pPtr + 2 + b / 2 + b / 2 ≤ locA + u := by rcases hd_loc_p with h | h <;> [left; right] <;> omega
      have hp2 : locA + u ≠ pPtr + 1 + b / 2 := by rcases hd_loc_p with h | h <;> omega
      have hp3 : locA + u < pPtr + 1 ∨ pPtr + 1 + b / 2 ≤ locA + u := by rcases hd_loc_p with h | h <;> [left; right] <;> omega
      have hp4 : locA + u ≠ pPtr := by rcases hd_loc_p with h | h <;> omega
      rw [hfr17 _ hp1]; simp only [mem16, Function.update_of_ne hp2]
      rw [hfr15 _ hp3]; simp only [mem14, Function.update_of_ne hp4]
      exact hloc0_13 u hu
    · intro a ha_loc ha_tmp2 ha_p
      rw [hfr17 a (by omega)]; simp only [mem16, Function.update_of_ne (by omega : a ≠ pPtr + 1 + b / 2)]
      rw [hfr15 a (by omega)]; simp only [mem14, Function.update_of_ne (by omega : a ≠ pPtr)]
      rw [hfr13 a ha_loc, hfr12 a ha_loc, hfr10 a (by omega) (by omega), hfr9 a ha_loc, hfr8 a ha_loc]
    · rw [hfr17 pPtr (Or.inl (by omega))]
      simp only [mem16, Function.update_of_ne (by omega : pPtr ≠ pPtr + 1 + b / 2)]
      rw [hfr15 pPtr (Or.inl (by omega))]; simp [mem14]
    · intro j hj
      rw [hfr17 _ (Or.inl (by omega))]
      simp only [mem16, Function.update_of_ne (by omega : pPtr + 1 + j ≠ pPtr + 1 + b / 2)]
      exact hC'_dst j hj
    · rw [hfr17 _ (Or.inl (by omega))]; simp [mem16]
  · exact False.elim h17

/-- Triple for `sbPadBisectStmt`: writes `encodePair (C'_sorted, comp_sorted)` (length `2 + b`)
at `pPtr`, restores `locAddr` to all zeros, preserves `r < 32`, and runs in `≤ 270 * b + 280` steps. -/
theorem sbPadBisect_triple {w n b blkA uA uLen locA tmpA pPtr : ℕ}
    {p : Program} {mem : ℕ → ℕ} {B_l U_l : List ℕ} {U : Finset ℕ} {st₀ : State}
    (hb_even : Even b) (hB_len : B_l.length = b) (hB_lt : B_l.Pairwise (· < ·))
    (hB_sub : ∀ u ∈ B_l, u < n) (hB_at : ListAt mem blkA B_l)
    (hU_len : U_l.length = uLen) (hU_le : uLen ≤ b)
    (hU_fin : U_l.toFinset = U) (hU_sub : U ⊆ B_l.toFinset)
    (hU_at : ListAt mem uA U_l)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hd_loc_blk : DisjointRange locA n blkA b)
    (hd_loc_u : DisjointRange locA n uA uLen)
    (hd_loc_tmp : DisjointRange locA n tmpA (4 * b))
    (hd_loc_p : DisjointRange locA n pPtr (2 + b))
    (hd_tmp_blk : DisjointRange tmpA (4 * b) blkA b)
    (hd_tmp_u : DisjointRange tmpA (4 * b) uA uLen)
    (hd_tmp_p : DisjointRange tmpA (4 * b) pPtr (2 + b))
    (_hd_p_blk : DisjointRange pPtr (2 + b) blkA b)
    (_hd_p_u : DisjointRange pPtr (2 + b) uA uLen)
    (hblk_w : blkA + b < 2 ^ w) (hu_w : uA + uLen < 2 ^ w)
    (hloc_w : locA + n < 2 ^ w) (htmp_w : tmpA + 4 * b < 2 ^ w)
    (hp_w : pPtr + 2 + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA)
    (hr24 : st₀.regs 24 = tmpA) (hr26 : st₀.regs 26 = pPtr)
    (hr28 : st₀.regs 28 = blkA) (hr30 : st₀.regs 30 = uA) (hr31 : st₀.regs 31 = uLen)
    (hmem : st₀.mem = mem) :
    let B := B_l.toFinset
    let C' := padToHalf B (smallerSide B U)
    Triple w p (fun st => st = st₀) sbPadBisectStmt
      (normalPost fun st' =>
        (∀ r < 32, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA ∨ tmpA + 4 * b ≤ a) →
          (a < pPtr ∨ pPtr + 2 + b ≤ a) → st'.mem a = mem a) ∧
        st'.mem pPtr = b / 2 ∧
        ListAt st'.mem (pPtr + 1) (C'.sort (· ≤ ·)) ∧
        st'.mem (pPtr + 1 + b / 2) = b / 2 ∧
        ListAt st'.mem (pPtr + 2 + b / 2) ((B \ C').sort (· ≤ ·)))
      (fun _ => 270 * b + 360) := by
  intro B C'
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  have hU_lt : ∀ u ∈ U_l, u < n := fun u hu =>
    hB_sub u (List.mem_toFinset.mp (hU_sub (hU_fin ▸ List.mem_toFinset.mpr hu)))
  have hpad_lists := smallerSide_padToHalf_lists hB_lt hU_sub (hB_len.symm ▸ hb_even)
  set inU := B_l.filter (fun u => decide (u ∈ U))
  set notU := B_l.filter (fun u => decide (u ∉ U))
  set C_list := if inU.length ≤ notU.length then inU else notU
  set rem_list := if inU.length ≤ notU.length then notU else inU
  set pad_len := b / 2 - C_list.length
  set pad_list := rem_list.take pad_len
  have hC'_union : C' = C_list.toFinset ∪ pad_list.toFinset := by
    have h := hpad_lists.1
    rw [List.toFinset_append, hB_len] at h
    exact h.symm
  have hC'_sort_eq : B_l.filter (fun u => decide (u ∈ C')) = C'.sort (· ≤ ·) := by
    have h := hpad_lists.2.1; rw [hpad_lists.1] at h; exact h
  have hcomp_sort_eq : B_l.filter (fun u => decide (u ∉ C')) = (B \ C').sort (· ≤ ·) := by
    have h := hpad_lists.2.2.1; rw [hpad_lists.1] at h; exact h
  have hC'_sort_len : (C'.sort (· ≤ ·)).length = b / 2 := by
    rw [← hC'_sort_eq]; have h := hpad_lists.2.2.2.1; rw [hpad_lists.1, hB_len] at h; exact h
  have hcomp_sort_len : ((B \ C').sort (· ≤ ·)).length = b / 2 := by
    rw [← hcomp_sort_eq]; have h := hpad_lists.2.2.2.2; rw [hpad_lists.1, hB_len] at h; exact h
  clear hpad_lists
  have hinU_le : inU.length ≤ b := (List.length_filter_le _ _).trans (le_of_eq hB_len)
  have hnotU_le : notU.length ≤ b := (List.length_filter_le _ _).trans (le_of_eq hB_len)
  have hsum_in_out : inU.length + notU.length = b := by
    have h1 := filter_blockList_inter_sdiff hB_lt hU_sub
    have h2 : inU.length = U.card := by rw [show inU = U.sort (· ≤ ·) from h1.1, Finset.length_sort]
    have h3 : notU.length = (B \ U).card := by rw [show notU = (B \ U).sort (· ≤ ·) from h1.2, Finset.length_sort]
    have h4 : (B \ U).card + U.card = B.card := Finset.card_sdiff_add_card_eq_card hU_sub
    have h5 : B.card = b := by rw [List.toFinset_card_of_nodup (hB_lt.imp fun h => Nat.ne_of_lt h), hB_len]
    omega
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbPadBisectStmt, seqStmts]
  refine runs_seq_assign_le (v := tmpA + b)
    (Expr.eval_add (Expr.eval_reg_of_eq hr24) (Expr.eval_reg_of_eq hr4) (by omega)) ?_
  refine runs_seq_assign_le (v := tmpA + 2 * b)
    (by have heq : tmpA + b + b = tmpA + 2 * b := by omega
        exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr4])) (by omega)) ?_
  refine runs_seq_assign_le (v := tmpA + 3 * b)
    (by have heq : tmpA + 2 * b + b = tmpA + 3 * b := by omega
        exact heq ▸ Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4]))
          (by omega)) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const (w := w) (by omega)) ?_
  -- Step 1: mark U, partition B into tmpA (inU) and tmpB (notU), unmark U
  let st1 : State :=
    { mem := st₀.mem,
      regs := Function.update (Function.update (Function.update (Function.update st₀.regs
        32 (tmpA + b)) 33 (tmpA + 2 * b)) 34 (tmpA + 3 * b)) 41 1,
      pos := st₀.pos }
  have hst1_lt32 : ∀ r < 32, st1.regs r = st₀.regs r := fun r hr => by
    dsimp only [st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := uLen) (sa := uA) (la := locA) (val := 1)
      (rSrc := 30) (rLen := 31) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p mem U_l st1 hU_len hU_at hU_lt hd_loc_u hu_w hloc_w hw16
      ((hst1_lt32 30 (by decide)).trans hr30) ((hst1_lt32 31 (by decide)).trans hr31)
      ((hst1_lt32 8 (by decide)).trans hr8) (by dsimp only [st1]; rw [Function.update_self]) hmem) rfl ?_
  intro st2 ⟨hoth2, hpos2, hfr2, hloc2⟩
  have hB_at2 : ListAt st2.mem blkA B_l := fun j hj => by
    rw [hfr2 _ (by rcases hd_loc_blk with h | h <;> [right; left] <;> omega)]; exact hB_at j hj
  have hloc2_iff : ∀ u < n, (st2.mem (locA + u) = 0 ↔ u ∉ U) := fun u hu => by
    rw [hloc2 u hu, hU_fin, hloc0 u hu]; by_cases h : u ∈ U <;> simp [h]
  have hd_tA_blk : DisjointRange tmpA b blkA b := by rcases hd_tmp_blk with h | h <;> [left; right] <;> omega
  have hd_tA_loc : DisjointRange tmpA b locA n := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
  have hd_tB_blk : DisjointRange (tmpA + b) b blkA b := by rcases hd_tmp_blk with h | h <;> [left; right] <;> omega
  have hd_tB_loc : DisjointRange (tmpA + b) b locA n := by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega
  refine runs_seq_triple_le
    (sbPartition_triple (w := w) (n := n) (len := b) (sa := blkA) (la := locA)
      (inA := tmpA) (outA := tmpA + b) (rSrc := 28) (rLen := 4) (rLoc := 8)
      (rInDst := 24) (rOutDst := 32) (rInCnt := 35) (rOutCnt := 36) (rI := 42) (rU := 43)
      (by decide) p st2.mem B_l U st2 hB_len hB_at2 hB_sub hloc2_iff
      hd_tA_blk hd_tA_loc hd_tB_blk hd_tB_loc (Or.inl le_rfl)
      hblk_w hloc_w (by omega) (by omega) hw16
      ((hoth2 28 (by decide) (by decide)).trans ((hst1_lt32 28 (by decide)).trans hr28))
      ((hoth2 4 (by decide) (by decide)).trans ((hst1_lt32 4 (by decide)).trans hr4))
      ((hoth2 8 (by decide) (by decide)).trans ((hst1_lt32 8 (by decide)).trans hr8))
      ((hoth2 24 (by decide) (by decide)).trans ((hst1_lt32 24 (by decide)).trans hr24))
      ((hoth2 32 (by decide) (by decide)).trans (by dsimp only [st1]; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]))
      rfl) rfl ?_
  intro st3 ⟨hcntIn3, hcntOut3, hoth3, hpos3, hfr3, hinU3, hnotU3⟩
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (w := w) (by omega)) ?_
  let st4 : State := { mem := st3.mem, regs := Function.update st3.regs 41 0, pos := st3.pos }
  have hU_at3 : ListAt st3.mem uA U_l := fun j hj => by
    have h1 : uA + j < tmpA ∨ tmpA + b ≤ uA + j := by rcases hd_tmp_u with h | h <;> [right; left] <;> omega
    have h2 : uA + j < tmpA + b ∨ tmpA + b + b ≤ uA + j := by rcases hd_tmp_u with h | h <;> [right; left] <;> omega
    have h3 : uA + j < locA ∨ locA + n ≤ uA + j := by rcases hd_loc_u with h | h <;> [right; left] <;> omega
    rw [hfr3 _ h1 h2, hfr2 _ h3]; exact hU_at j hj
  refine runs_seq_triple_le
    (sbMarkList_triple (w := w) (n := n) (len := uLen) (sa := uA) (la := locA) (val := 0)
      (rSrc := 30) (rLen := 31) (rLoc := 8) (rVal := 41) (rI := 42) (rU := 43)
      (by decide) p st3.mem U_l st4 hU_len hU_at3 hU_lt hd_loc_u hu_w hloc_w hw16
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 30 (by decide) (by decide) (by decide) (by decide),
            hoth2 30 (by decide) (by decide), hst1_lt32 30 (by decide), hr30])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 31 (by decide) (by decide) (by decide) (by decide),
            hoth2 31 (by decide) (by decide), hst1_lt32 31 (by decide), hr31])
      (by dsimp only [st4]; rw [Function.update_of_ne (by decide), hoth3 8 (by decide) (by decide) (by decide) (by decide),
            hoth2 8 (by decide) (by decide), hst1_lt32 8 (by decide), hr8])
      (by dsimp only [st4]; rw [Function.update_self]) rfl) rfl ?_
  intro st5 ⟨hoth5, hpos5, hfr5, hloc5⟩
  have hloc0_5 : ∀ u < n, st5.mem (locA + u) = 0 := fun u hu => by
    rw [hloc5 u hu]; by_cases hm : u ∈ U_l.toFinset
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      rw [hfr3 _ (by rcases hd_loc_tmp with h | h <;> [left; right] <;> omega)
            (by rcases hd_loc_tmp with h | h <;> [left; right] <;> omega), hloc2 u hu]
      simp [hm, hloc0 u hu]
  have hinU5 : ListAt st5.mem tmpA inU := fun j hj => by
    rw [hfr5 _ (by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega)]; exact hinU3 j hj
  have hnotU5 : ListAt st5.mem (tmpA + b) notU := fun j hj => by
    rw [hfr5 _ (by rcases hd_loc_tmp with h | h <;> [right; left] <;> omega)]; exact hnotU3 j hj
  have hfr5_all : ∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA ∨ tmpA + 2 * b ≤ a) → st5.mem a = mem a := fun a hl ht => by
    rw [hfr5 a hl, hfr3 a (by omega) (by omega), hfr2 a hl]
  have hst5_lt32 : ∀ r < 32, st5.regs r = st₀.regs r := fun r hr => by
    rw [hoth5 r (by omega) (by omega)]; dsimp only [st4]
    rw [Function.update_of_ne (by omega), hoth3 r (by omega) (by omega) (by omega) (by omega),
      hoth2 r (by omega) (by omega), hst1_lt32 r hr]
  have hr32_5 : st5.regs 32 = tmpA + b := by
    rw [hoth5 32 (by decide) (by decide)]; dsimp only [st4]
    rw [Function.update_of_ne (by decide), hoth3 32 (by decide) (by decide) (by decide) (by decide),
      hoth2 32 (by decide) (by decide)]; dsimp only [st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hr33_5 : st5.regs 33 = tmpA + 2 * b := by
    rw [hoth5 33 (by decide) (by decide)]; dsimp only [st4]
    rw [Function.update_of_ne (by decide), hoth3 33 (by decide) (by decide) (by decide) (by decide),
      hoth2 33 (by decide) (by decide)]; dsimp only [st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have hr34_5 : st5.regs 34 = tmpA + 3 * b := by
    rw [hoth5 34 (by decide) (by decide)]; dsimp only [st4]
    rw [Function.update_of_ne (by decide), hoth3 34 (by decide) (by decide) (by decide) (by decide),
      hoth2 34 (by decide) (by decide)]; dsimp only [st1]
    rw [Function.update_of_ne (by decide), Function.update_self]
  have hr35_5 : st5.regs 35 = inU.length := by
    rw [hoth5 35 (by decide) (by decide)]; dsimp only [st4]; rw [Function.update_of_ne (by decide), hcntIn3]
  have hr36_5 : st5.regs 36 = notU.length := by
    rw [hoth5 36 (by decide) (by decide)]; dsimp only [st4]; rw [Function.update_of_ne (by decide), hcntOut3]
  -- Step 2: branch on `notU.length < inU.length` to set (C_list, rem_list)
  set cA := if inU.length ≤ notU.length then tmpA else tmpA + b
  set remA := if inU.length ≤ notU.length then tmpA + b else tmpA
  have hC_len_le : C_list.length ≤ b / 2 := by dsimp only [C_list]; split_ifs <;> omega
  have hpad_le_rem : pad_len ≤ rem_list.length := by dsimp only [pad_len, C_list, rem_list]; split_ifs <;> omega
  have hpad_len : pad_list.length = pad_len := by rw [List.length_take, Nat.min_eq_left hpad_le_rem]
  have hC_at5 : ListAt st5.mem cA C_list := by dsimp only [cA, C_list]; split_ifs; exact hinU5; exact hnotU5
  have hpad_at5 : ListAt st5.mem remA pad_list := fun j hj => by
    have hj_rem : j < rem_list.length := by omega
    have hget : pad_list[j]'hj = rem_list[j]'hj_rem := List.getElem_take
    rw [hget]
    dsimp only [remA, rem_list] at hj_rem ⊢; split_ifs with hle
    · exact hnotU5 j (by simpa [hle] using hj_rem)
    · exact hinU5 j (by simpa [hle] using hj_rem)
  have hC_lt : ∀ u ∈ C_list, u < n := fun u hu => by
    have : u ∈ B_l := by dsimp only [C_list] at hu; split_ifs at hu <;> exact (List.mem_filter.mp hu).1
    exact hB_sub u this
  have hpad_lt : ∀ u ∈ pad_list, u < n := fun u hu => by
    have h1 : u ∈ rem_list := List.mem_of_mem_take hu
    have : u ∈ B_l := by dsimp only [rem_list] at h1; split_ifs at h1 <;> exact (List.mem_filter.mp h1).1
    exact hB_sub u this
  -- Factor the tail after the `cond` so both branches share one proof
  suffices htail : ∀ (st6 : State),
      st6.mem = st5.mem → st6.pos = st5.pos →
      (∀ r < 32, st6.regs r = st₀.regs r) →
      st6.regs 33 = tmpA + 2 * b → st6.regs 34 = tmpA + 3 * b →
      st6.regs 37 = cA → st6.regs 38 = C_list.length → st6.regs 39 = remA →
      ∃ o st' c',
        Runs w p ω (seqStmts [
          .assign 44 (.bin .div (.reg 4) (.const 2)),
          .assign 40 (.bin .sub (.reg 44) (.reg 38)),
          .assign 41 (.const 1),
          sbMarkListStmt 37 38 8 41 42 43,
          sbMarkListStmt 39 40 8 41 42 43,
          sbPartitionStmt 28 4 8 33 34 35 36 42 43,
          .assign 41 (.const 0),
          sbMarkListStmt 37 38 8 41 42 43,
          sbMarkListStmt 39 40 8 41 42 43,
          .store (.reg 26) (.reg 44),
          .assign 41 (.bin .add (.reg 26) (.const 1)),
          scCopySliceStmt 33 41 44 42 43,
          .store (.bin .add (.reg 41) (.reg 44)) (.reg 44),
          .assign 41 (.bin .add (.bin .add (.reg 41) (.reg 44)) (.const 1)),
          scCopySliceStmt 34 41 44 42 43]) st6 o st' c' ∧
        (normalPost fun st' =>
          (∀ r < 32, st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
          (∀ u < n, st'.mem (locA + u) = 0) ∧
          (∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA ∨ tmpA + 4 * b ≤ a) →
            (a < pPtr ∨ pPtr + 2 + b ≤ a) → st'.mem a = mem a) ∧
          st'.mem pPtr = b / 2 ∧
          ListAt st'.mem (pPtr + 1) (C'.sort (· ≤ ·)) ∧
          st'.mem (pPtr + 1 + b / 2) = b / 2 ∧
          ListAt st'.mem (pPtr + 2 + b / 2) ((B \ C').sort (· ≤ ·))) o st' ∧
        0 + c' ≤ 170 * b + 230 by
    by_cases hle : inU.length ≤ notU.length
    · refine runs_seq_cond_le (v := 0)
        (Expr.eval_lt_false (Expr.eval_reg_of_eq hr36_5) (Expr.eval_reg_of_eq hr35_5) (by omega) (by omega))
        (fun h => absurd rfl h) (fun _ => ?_)
      refine runs_seq_assoc_le ?_; refine runs_seq_assign_le (v := tmpA)
        (Expr.eval_reg_of_eq ((hst5_lt32 24 (by decide)).trans hr24)) ?_
      refine runs_seq_assoc_le ?_; refine runs_seq_assign_le (v := inU.length)
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr35_5])) ?_
      refine runs_seq_assign_le (v := tmpA + b)
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr32_5])) ?_
      let st6 : State :=
        { mem := st5.mem,
          regs := Function.update (Function.update (Function.update st5.regs 37 tmpA) 38 inU.length) 39 (tmpA + b),
          pos := st5.pos }
      obtain ⟨o, st', c', hr, hp, hc⟩ := htail st6 rfl rfl
        (fun r hr => by dsimp only [st6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst5_lt32 r hr])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr33_5])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr34_5])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]; simp [cA, hle])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_self]; simp [C_list, hle])
        (by dsimp only [st6]; rw [Function.update_self]; simp [remA, hle])
      exact ⟨o, st', c', hr, hp, by simp only [Expr.size]; omega⟩
    · refine runs_seq_cond_le (v := 1)
        (Expr.eval_lt_true (Expr.eval_reg_of_eq hr36_5) (Expr.eval_reg_of_eq hr35_5) (by omega) (by omega))
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine runs_seq_assoc_le ?_; refine runs_seq_assign_le (v := tmpA + b)
        (Expr.eval_reg_of_eq hr32_5) ?_
      refine runs_seq_assoc_le ?_; refine runs_seq_assign_le (v := notU.length)
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr36_5])) ?_
      refine runs_seq_assign_le (v := tmpA)
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst5_lt32 24 (by decide), hr24])) ?_
      let st6 : State :=
        { mem := st5.mem,
          regs := Function.update (Function.update (Function.update st5.regs 37 (tmpA + b)) 38 notU.length) 39 tmpA,
          pos := st5.pos }
      obtain ⟨o, st', c', hr, hp, hc⟩ := htail st6 rfl rfl
        (fun r hr => by dsimp only [st6]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst5_lt32 r hr])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr33_5])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr34_5])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]; simp [cA, hle])
        (by dsimp only [st6]; rw [Function.update_of_ne (by decide), Function.update_self]; simp [C_list, hle])
        (by dsimp only [st6]; rw [Function.update_self]; simp [remA, hle])
      exact ⟨o, st', c', hr, hp, by simp only [Expr.size]; omega⟩
  -- Prove `htail` via `sbPadBisect_tail`
  intro st6 hmem6 hpos6 hst6_lt32 hr33_6 hr34_6 hr37_6 hr38_6 hr39_6
  have hB_at5 : ListAt st5.mem blkA B_l := fun j hj => by
    rw [hfr5_all _ (by rcases hd_loc_blk with h | h <;> [right; left] <;> omega)
          (by rcases hd_tmp_blk with h | h <;> [right; left] <;> omega)]
    exact hB_at j hj
  have hcA_in_tmp : tmpA ≤ cA ∧ cA + C_list.length ≤ tmpA + 2 * b := by
    dsimp only [cA, C_list]; split_ifs <;> omega
  have hremA_in_tmp : tmpA ≤ remA ∧ remA + pad_list.length ≤ tmpA + 2 * b := by
    dsimp only [remA]; rw [hpad_len]; split_ifs <;> omega
  obtain ⟨o, st', c', hr, hp, hc⟩ := sbPadBisect_tail hb_even hB_len hB_sub hB_at5 hC_len_le hpad_len
    hC_lt hpad_lt hC_at5 hpad_at5 hC'_union hC'_sort_eq hcomp_sort_eq hC'_sort_len hcomp_sort_len
    hloc0_5 hd_loc_blk hd_loc_tmp hd_loc_p hd_tmp_blk hd_tmp_p hcA_in_tmp hremA_in_tmp
    hblk_w hloc_w htmp_w hp_w hw16
    ((hst6_lt32 4 (by decide)).trans hr4) ((hst6_lt32 8 (by decide)).trans hr8)
    ((hst6_lt32 26 (by decide)).trans hr26) ((hst6_lt32 28 (by decide)).trans hr28)
    hr33_6 hr34_6 hr37_6 hr38_6 hr39_6 hmem6
  refine ⟨o, st', c', hr, ?_, hc⟩
  cases o with
  | returned _ => exact hp
  | normal =>
    rcases hp with ⟨hoth', hpos', hloc', hfr', hp0, hpC', hpMid, hpComp⟩
    refine ⟨fun r hr => (hoth' r hr).trans (hst6_lt32 r hr),
      hpos'.trans (hpos6.trans (hpos5.trans (hpos3.trans hpos2))), hloc',
      fun a ha_loc ha_tmp ha_p => (hfr' a ha_loc (by omega) ha_p).trans (hfr5_all a ha_loc (by omega)),
      hp0, hpC', hpMid, hpComp⟩

end MinCostFlow.ExpanderDecomp
