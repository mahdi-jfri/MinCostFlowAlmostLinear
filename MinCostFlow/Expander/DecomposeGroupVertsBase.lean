module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.GraphCompression
public import MinCostFlow.Expander.HeapSortProg
public import MinCostFlow.Expander.ActiveSortProg
public import MinCostFlow.Expander.CsrBfsProg

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grouping Vertices by Expander-Decomposition Labels (`groupVertsProc`)

Given a graph vertex count `n ≥ 1`, an array of twin-graph component labels `label[0..2n-1]` at
`lblAddr`, and a grouping buffer `bufAddr` of `9 * n + 1` words (`groupBufSize n m = 12 * n + 2 * m + 2`),
`groupVertsProc`:
1. Computes `sameTwin[v] := (label[2v] == label[2v+1])` at `grpSameTwin`;
2. Sorts and deduplicates `{label[2v] | v < n}` into `uniq[0..k-1]` (`1 ≤ k ≤ n`) at `grpUniqLbl`;
3. Computes `partId[v] := uniq.idxOf label[2v]` at `grpPartId` and counts `partCnt[p]` at `grpPartCnt`;
4. Prefix-sums `partOff[0..k]` at `grpPartOff` (`partOff k = n`);
5. Scatters ascending vertex lists `partVerts[partOff p .. partOff (p+1))` at `grpPartVerts` and
   within-part local vertex indices `localId[v]` at `grpLocalId`;
6. Returns `k = numParts` (`1 ≤ k ≤ n`) in `O(n log n + n)` Word-RAM time.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited

/-! ## 1. Grouping Buffer Layout -/

abbrev grpSameTwin (bufAddr _n : ℕ) : ℕ := bufAddr
abbrev grpSortBuf (bufAddr n : ℕ) : ℕ := bufAddr + n
abbrev grpUniqLbl (bufAddr n : ℕ) : ℕ := bufAddr + 2 * n
abbrev grpPartId (bufAddr n : ℕ) : ℕ := bufAddr + 3 * n
abbrev grpPartCnt (bufAddr n : ℕ) : ℕ := bufAddr + 4 * n
abbrev grpPartOff (bufAddr n : ℕ) : ℕ := bufAddr + 5 * n
abbrev grpPartCur (bufAddr n : ℕ) : ℕ := bufAddr + 6 * n + 1
abbrev grpPartVerts (bufAddr n : ℕ) : ℕ := bufAddr + 7 * n + 1
abbrev grpLocalId (bufAddr n : ℕ) : ℕ := bufAddr + 8 * n + 1
abbrev grpEdgeCnt (bufAddr n : ℕ) : ℕ := bufAddr + 9 * n + 1
abbrev grpEdgeOff (bufAddr n : ℕ) : ℕ := bufAddr + 10 * n + 1
abbrev grpEdgeCur (bufAddr n : ℕ) : ℕ := bufAddr + 11 * n + 2
abbrev grpPartEdges (bufAddr n : ℕ) : ℕ := bufAddr + 12 * n + 2

/-- Total words reserved at `bufAddr` for both vertex and edge grouping. -/
def groupBufSize (n m : ℕ) : ℕ :=
  12 * n + 2 * m + 2

/-! ## 2. `groupVertsProc` Program and Cost -/

def groupVertsSetupStmt : Stmt :=
  seqStmts
    [ .assign 4 (.bin .add (.reg 2) (.reg 0))
    , .assign 5 (.bin .add (.reg 4) (.reg 0))
    , .assign 6 (.bin .add (.reg 5) (.reg 0))
    , .assign 7 (.bin .add (.reg 6) (.reg 0))
    , .assign 8 (.bin .add (.reg 7) (.reg 0))
    , .assign 9 (.bin .add (.bin .add (.reg 8) (.reg 0)) (.const 1))
    , .assign 10 (.bin .add (.reg 9) (.reg 0))
    , .assign 11 (.bin .add (.reg 10) (.reg 0)) ]

def groupVertsCopyStmt : Stmt :=
  forRange 12 (.const 0) (.reg 0)
    (seqStmts
      [ .assign 13 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 12))))
      , .assign 14 (.load (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1))))
      , .store (.bin .add (.reg 2) (.reg 12)) (.bin .eq (.reg 13) (.reg 14))
      , .store (.bin .add (.reg 4) (.reg 12)) (.reg 13) ])

def groupVertsCountStmt (b_bs : ℕ) : Stmt :=
  seqStmts
    [ forRange 12 (.const 0) (.reg 3)
        (.store (.bin .add (.reg 7) (.reg 12)) (.const 0))
    , forRange 12 (.const 0) (.reg 0)
        (seqStmts
          [ .assign 13 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 12))))
          , .call 14 b_bs [.reg 5, .reg 3, .reg 13]
          , .store (.bin .add (.reg 6) (.reg 12)) (.reg 14)
          , .assign 15 (.load (.bin .add (.reg 7) (.reg 14)))
          , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 15) (.const 1)) ]) ]

def groupVertsPrefixStmt : Stmt :=
  seqStmts
    [ .store (.reg 8) (.const 0)
    , .assign 13 (.const 0)
    , forRange 12 (.const 0) (.reg 3)
        (seqStmts
          [ .assign 14 (.load (.bin .add (.reg 7) (.reg 12)))
          , .store (.bin .add (.reg 9) (.reg 12)) (.reg 13)
          , .assign 13 (.bin .add (.reg 13) (.reg 14))
          , .store (.bin .add (.reg 8) (.bin .add (.reg 12) (.const 1))) (.reg 13) ]) ]

def groupVertsScatterStmt : Stmt :=
  forRange 12 (.const 0) (.reg 0)
    (seqStmts
      [ .assign 13 (.load (.bin .add (.reg 6) (.reg 12)))
      , .assign 14 (.load (.bin .add (.reg 9) (.reg 13)))
      , .store (.bin .add (.reg 10) (.reg 14)) (.reg 12)
      , .assign 15 (.load (.bin .add (.reg 8) (.reg 13)))
      , .store (.bin .add (.reg 11) (.reg 12)) (.bin .sub (.reg 14) (.reg 15))
      , .store (.bin .add (.reg 9) (.reg 13)) (.bin .add (.reg 14) (.const 1)) ])

/-- `groupVertsProc`: args `[n, lblAddr, bufAddr]`. Groups `0..n-1` by `label[2v]` into
`grpPartVerts`, returning `k = numParts` (`1 ≤ k ≤ n`). -/
def groupVertsProc (b_sort b_dedup b_bs : ℕ) : Stmt :=
  seqStmts
    [ groupVertsSetupStmt
    , groupVertsCopyStmt
    , .call 12 b_sort [.reg 4, .reg 0]
    , .call 3 b_dedup [.reg 4, .reg 0, .reg 5]
    , groupVertsCountStmt b_bs
    , groupVertsPrefixStmt
    , groupVertsScatterStmt
    , .ret (.reg 3) ]

lemma groupVertsProc_noRand (b_sort b_dedup b_bs : ℕ) :
    (groupVertsProc b_sort b_dedup b_bs).NoRand := by
  simp [groupVertsProc, groupVertsSetupStmt, groupVertsCopyStmt, groupVertsCountStmt,
    groupVertsPrefixStmt, groupVertsScatterStmt, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

/-- Contract for `groupVertsProc`: args `[n, lblAddr, bufAddr]`. -/
def groupVertsContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ n lblAddr bufAddr label, args = [n, lblAddr, bufAddr] ∧
      1 ≤ n ∧
      ListAt mem lblAddr label ∧
      label.length = 2 * n ∧
      (∀ i < 2 * n, mem (lblAddr + i) < 2 ^ w) ∧
      lblAddr + 2 * n ≤ bufAddr ∧
      bufAddr + 9 * n + 3 < 2 ^ w ∧
      16 ≤ 2 ^ w
  post args mem v mem' :=
    let n := args.getD 0 0
    let lblAddr := args.getD 1 0
    let bufAddr := args.getD 2 0
    let uniq := tab v fun p => mem' (grpUniqLbl bufAddr n + p)
    1 ≤ v ∧ v ≤ n ∧
    uniq.Pairwise (· < ·) ∧
    (∀ u < n,
      (mem' (grpSameTwin bufAddr n + u) ≠ 0 ↔ mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u + 1)) ∧
      mem (lblAddr + 2 * u) ∈ uniq ∧
      mem' (grpPartId bufAddr n + u) = uniq.idxOf (mem (lblAddr + 2 * u)) ∧
      mem' (grpPartId bufAddr n + u) < v) ∧
    (∀ p ∈ uniq, ∃ u < n, mem (lblAddr + 2 * u) = p) ∧
    mem' (grpPartOff bufAddr n) = 0 ∧
    mem' (grpPartOff bufAddr n + v) = n ∧
    (∀ p < v, mem' (grpPartOff bufAddr n + (p + 1)) =
      mem' (grpPartOff bufAddr n + p) + mem' (grpPartCnt bufAddr n + p)) ∧
    (∀ p < v,
      let cnt := mem' (grpPartCnt bufAddr n + p)
      let off := mem' (grpPartOff bufAddr n + p)
      let verts := tab cnt fun t => mem' (grpPartVerts bufAddr n + off + t)
      verts.Pairwise (· < ·) ∧
      off + cnt ≤ n ∧
      (∀ u, u ∈ verts ↔ u < n ∧ mem' (grpPartId bufAddr n + u) = p)) ∧
    (∀ u < n,
      let p := mem' (grpPartId bufAddr n + u)
      let off := mem' (grpPartOff bufAddr n + p)
      let lid := mem' (grpLocalId bufAddr n + u)
      lid < mem' (grpPartCnt bufAddr n + p) ∧
      mem' (grpPartVerts bufAddr n + off + lid) = u) ∧
    MemFrame mem mem' bufAddr (bufAddr + 9 * n + 1)
  cost args _ :=
    let n := args.getD 0 0
    1000 * (n * (2 * Nat.log 2 (n + 2) + 1) + 1)

/-! ## 3. Pure Helpers & Per-Stage Triple Proofs -/

lemma bucketVerts_append (f : ℕ → ℕ) (p v : ℕ) :
    ((List.range (v + 1)).filter fun u => decide (f u = p)) =
      ((List.range v).filter fun u => decide (f u = p)) ++
        if f v = p then [v] else [] := by
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : f v = p <;> simp [h]

lemma bucketVerts_length_eq_card (f : ℕ → ℕ) (p v : ℕ) :
    ((List.range v).filter fun u => decide (f u = p)).length =
      ((Finset.range v).filter fun u => f u = p).card := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [bucketVerts_append, List.length_append, Finset.range_add_one, Finset.filter_insert, ih]
    by_cases h : f v = p
    · have hmem : v ∉ (Finset.range v).filter fun u => f u = p := by simp
      simp [h, Finset.card_insert_of_notMem hmem]
    · simp [h]

lemma sum_fibers_eq_n (f : ℕ → ℕ) (n k : ℕ) (hf : ∀ u < n, f u < k) :
    ((List.range k).map fun p => ((Finset.range n).filter fun u => f u = p).card).sum = n := by
  have h1 : ∀ m, ((List.range m).map fun p => ((Finset.range n).filter fun u => f u = p).card).sum =
      ∑ p ∈ Finset.range m, ((Finset.range n).filter fun u => f u = p).card := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
        Finset.sum_range_succ, ih]
  rw [h1 k]
  have hfib := Finset.card_eq_sum_card_fiberwise (s := Finset.range n) (t := Finset.range k)
    (f := f) fun u hu => Finset.mem_range.mpr (hf u (Finset.mem_range.mp hu))
  simpa [Finset.card_range] using hfib.symm

lemma groupVertsSetup_triple {w n lblAddr bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hb : bufAddr + 9 * n + 3 < 2 ^ w) :
    Triple w p
      (fun st => st = startState [n, lblAddr, bufAddr] mem pos)
      groupVertsSetupStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      (fun _ => 45) := by
  intro st ω hst
  subst hst
  dsimp only [groupVertsSetupStmt, seqStmts]
  refine runs_start_le ?_
  wram_run
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      simp [startState, grpSortBuf, grpUniqLbl, grpPartId, grpPartCnt, grpPartOff,
        grpPartCur, grpPartVerts, grpLocalId] <;> omega
  · wram_cost

lemma groupVertsCopy_triple {w n lblAddr bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ)
    (hmem_lt : ∀ i < 2 * n, mem (lblAddr + i) < 2 ^ w)
    (hlb : lblAddr + 2 * n ≤ bufAddr) (hb : bufAddr + 9 * n + 3 < 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      groupVertsCopyStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        (∀ u < n,
          (st.mem (grpSameTwin bufAddr n + u) ≠ 0 ↔ mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u + 1)) ∧
          st.mem (grpSortBuf bufAddr n + u) = mem (lblAddr + 2 * u) ∧
          st.mem (grpSortBuf bufAddr n + u) < 2 ^ w) ∧
        MemFrame mem st.mem bufAddr (bufAddr + 2 * n))
      (fun _ => 45 * n + 10) := by
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun v st =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 12 = v ∧
    (∀ u < v,
      (st.mem (grpSameTwin bufAddr n + u) ≠ 0 ↔ mem (lblAddr + 2 * u) = mem (lblAddr + 2 * u + 1)) ∧
      st.mem (grpSortBuf bufAddr n + u) = mem (lblAddr + 2 * u) ∧
      st.mem (grpSortBuf bufAddr n + u) < 2 ^ w) ∧
    MemFrame mem st.mem bufAddr (bufAddr + 2 * n)
  have hloop := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 13 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 12))))
      , .assign 14 (.load (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1))))
      , .store (.bin .add (.reg 2) (.reg 12)) (.bin .eq (.reg 13) (.reg 14))
      , .store (.bin .add (.reg 4) (.reg 12)) (.reg 13) ])
    (P := fun st =>
      st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧
      st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
      st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
      st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
      st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
      st.mem = mem)
    (Inv := Inv)
    34 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st hP => by
      rcases hP with ⟨h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩
      refine ⟨by eval_expr, by simp [Inv, h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, hm,
        memFrame_refl]⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.1; eval_expr)
    (fun v _ hvlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, hinv, hframe⟩
      have hl0_eq : st.mem (lblAddr + 2 * v) = mem (lblAddr + 2 * v) :=
        hframe (lblAddr + 2 * v) (Or.inl (by omega))
      have hl1_eq : st.mem (lblAddr + (2 * v + 1)) = mem (lblAddr + 2 * v + 1) :=
        hframe (lblAddr + (2 * v + 1)) (Or.inl (by omega))
      have hl0_lt : mem (lblAddr + 2 * v) < 2 ^ w := hmem_lt (2 * v) (by omega)
      have hl1_lt : mem (lblAddr + 2 * v + 1) < 2 ^ w := hmem_lt (2 * v + 1) (by omega)
      have hfm0 : bufAddr ≤ bufAddr + v := by omega
      have hfm1 : bufAddr + v < bufAddr + 2 * n := by omega
      have hfm2 : bufAddr ≤ bufAddr + n + v := by omega
      have hfm3 : bufAddr + n + v < bufAddr + 2 * n := by omega
      dsimp only [grpSameTwin, grpSortBuf] at h4 hinv hframe ⊢
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_run
      · dsimp only [Inv, grpSameTwin, grpSortBuf]
        simp only [h1, h2, h4, h12]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h4], by simp [h5],
          by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10], by simp [h11],
          by simp, fun u hu => ?_, ?_⟩, by simp [h12]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu' | hu_eq
          · have hpu := hinv u hu'
            have hne1 : bufAddr + u ≠ bufAddr + n + v := by omega
            have hne2 : bufAddr + u ≠ bufAddr + v := by omega
            have hne3 : bufAddr + n + u ≠ bufAddr + n + v := by omega
            have hne4 : bufAddr + n + u ≠ bufAddr + v := by omega
            simpa [Function.update_of_ne hne1, Function.update_of_ne hne2,
              Function.update_of_ne hne3, Function.update_of_ne hne4] using hpu
          · subst u
            have hne_sb : bufAddr + v ≠ bufAddr + n + v := by omega
            simp only [Function.update_of_ne hne_sb, Function.update_self]
            refine ⟨?_, ?_, ?_⟩
            · by_cases heq : mem (lblAddr + 2 * v) = mem (lblAddr + 2 * v + 1)
              · simp [hl0_eq, hl1_eq, heq]
              · simp [hl0_eq, hl1_eq, heq]
            · simp [hl0_eq]
            · simpa [hl0_eq] using hl0_lt
        · exact memFrame_trans hframe
            (memFrame_trans (memFrame_update hfm0 hfm1) (memFrame_update hfm2 hfm3))
      · wram_cost)
  refine hloop.conseq (T' := fun _ => 45 * n + 10) (fun _ h => h) ?_
    (fun _ _ => by simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, _, hinv, hframe⟩
    exact ⟨h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, hinv, hframe⟩

lemma groupVertsCount_triple {w n k lblAddr bufAddr b_bs : ℕ} {p : Program}
    (hbs : MeetsContract w p b_bs (binSearchContract w))
    (mem : ℕ → ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hb : bufAddr + 9 * n + 3 < 2 ^ w)
    (huniq_nd : (tab k fun q => mem (grpUniqLbl bufAddr n + q)).Pairwise (· < ·))
    (huniq_lt : ∀ q < k, mem (grpUniqLbl bufAddr n + q) < 2 ^ w)
    (hlbl_mem : ∀ u < n, mem (lblAddr + 2 * u) ∈ tab k fun q => mem (grpUniqLbl bufAddr n + q))
    (hlbl_lt : ∀ u < n, mem (lblAddr + 2 * u) < 2 ^ w)
    (hlb : lblAddr + 2 * n ≤ bufAddr) :
    Triple w p
      (fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      (groupVertsCountStmt b_bs)
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        (∀ u < n,
          st.mem (grpPartId bufAddr n + u) =
            (tab k fun q => mem (grpUniqLbl bufAddr n + q)).idxOf (mem (lblAddr + 2 * u)) ∧
          st.mem (grpPartId bufAddr n + u) < k) ∧
        (∀ q < k, st.mem (grpPartCnt bufAddr n + q) =
          ((Finset.range n).filter fun u =>
            (tab k fun j => mem (grpUniqLbl bufAddr n + j)).idxOf (mem (lblAddr + 2 * u)) = q).card) ∧
        MemFrame mem st.mem (grpPartId bufAddr n) (grpPartOff bufAddr n))
      (fun _ => n * (35 * (Nat.log 2 (n + 2) + 2) + 55) + 20 * n + 40) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hw4 : 4 ≤ 2 ^ w := by omega
  let ys := tab k fun q => mem (grpUniqLbl bufAddr n + q)
  let partFn : ℕ → ℕ := fun u => ys.idxOf (mem (lblAddr + 2 * u))
  -- Zero `partCnt[0..k-1]`
  let InvZero : ℕ → State → Prop := fun q st =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 12 = q ∧
    (∀ j < q, st.mem (grpPartCnt bufAddr n + j) = 0) ∧
    MemFrame mem st.mem (grpPartCnt bufAddr n) (grpPartOff bufAddr n)
  have hzero := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 3)
    (body := .store (.bin .add (.reg 7) (.reg 12)) (.const 0))
    (P := fun st =>
      st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
      st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
      st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
      st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
      st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
      st.mem = mem)
    (Inv := InvZero)
    6 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hP => by
      rcases hP with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩
      refine ⟨by eval_expr, by simp [InvZero, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm,
        memFrame_refl]⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.1; eval_expr)
    (fun q _ hqlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hzq, hfr⟩
      have hfz0 : grpPartCnt bufAddr n ≤ bufAddr + 4 * n + q := by dsimp only [grpPartCnt]; omega
      have hfz1 : bufAddr + 4 * n + q < grpPartOff bufAddr n := by dsimp only [grpPartOff]; omega
      dsimp only [grpPartCnt, grpPartOff] at h7 h8 hzq hfr ⊢
      refine runs_start_le ?_
      wram_run
      · dsimp only [InvZero, grpPartCnt]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp [h11], by simp, fun j hj => ?_, ?_⟩, by simp [h12]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
          · simp only [Function.update_of_ne (by omega : bufAddr + 4 * n + j ≠ bufAddr + 4 * n + q)]
            exact hzq j hj'
          · subst j; simp
        · exact memFrame_trans hfr (memFrame_update hfz0 hfz1)
      · wram_cost)
  -- Loop 2: `binSearch` each vertex, write `partId`, increment `partCnt`
  let InvCount : ℕ → State → Prop := fun v st =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 12 = v ∧
    (∀ u < v, st.mem (grpPartId bufAddr n + u) = partFn u ∧ st.mem (grpPartId bufAddr n + u) < k) ∧
    (∀ q < k, st.mem (grpPartCnt bufAddr n + q) =
      ((Finset.range v).filter fun u => partFn u = q).card) ∧
    MemFrame mem st.mem (grpPartId bufAddr n) (grpPartOff bufAddr n)
  have hlog_k : Nat.log 2 (k + 2) ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  have hcount := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 13 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 12))))
      , .call 14 b_bs [.reg 5, .reg 3, .reg 13]
      , .store (.bin .add (.reg 6) (.reg 12)) (.reg 14)
      , .assign 15 (.load (.bin .add (.reg 7) (.reg 14)))
      , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 15) (.const 1)) ])
    (P := InvZero k) (Inv := InvCount)
    (35 * (Nat.log 2 (n + 2) + 2) + 45) 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st hZ => by
      rcases hZ with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, hzq, hfr⟩
      dsimp only [grpPartId, grpPartCnt, grpPartOff] at h6 h7 h8 hfr ⊢
      exact ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by simp,
        fun _ hu => by omega, fun q hqk => by simpa using hzq q hqk,
        fun addr ha => hfr addr (by
          dsimp only [grpPartId, grpPartOff] at ha
          rcases ha with h | h
          · left; omega
          · right; omega)⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.1; eval_expr)
    (fun v _ hvlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hpid, hcnt, hfr⟩
      dsimp only [grpUniqLbl, grpPartId, grpPartCnt, grpPartOff] at h5 h6 h7 h8 hpid hcnt hfr ⊢
      have hl_eq : st.mem (lblAddr + 2 * v) = mem (lblAddr + 2 * v) :=
        hfr (lblAddr + 2 * v) (Or.inl (by omega))
      have hl_lt : mem (lblAddr + 2 * v) < 2 ^ w := hlbl_lt v hvlt
      have huniq_eq : ∀ q < k, st.mem (bufAddr + 2 * n + q) = mem (bufAddr + 2 * n + q) :=
        fun q hqk => hfr (bufAddr + 2 * n + q) (Or.inl (by omega))
      have htab_eq : tab k (fun q => st.mem (bufAddr + 2 * n + q)) = ys := by
        refine List.ext_getElem (by simp [ys, tab]) fun q hq1 _ => ?_
        simp only [ys, tab, grpUniqLbl, List.getElem_map, List.getElem_range]
        exact huniq_eq q (by simpa [tab] using hq1)
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_step
      · refine runs_seq_call_le hbs (vs := [bufAddr + 2 * n, k, mem (lblAddr + 2 * v)])
          (by simp [evalArgs, Expr.eval, h5, h3, hl_eq])
          ?_ ?_ ?_
        · intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> first | exact hl_lt | omega
        · refine ⟨bufAddr + 2 * n, k, mem (lblAddr + 2 * v), rfl, by omega, hw4, ?_, ?_, ?_⟩
          · intro q hqk; rw [huniq_eq q hqk]; exact huniq_lt q hqk
          · rw [htab_eq]; exact huniq_nd
          · rw [htab_eq]; exact hlbl_mem v hvlt
        · intro q' mem' pos' ⟨hm'_eq, hqk', hidx', _⟩
          subst hm'_eq
          have hqk'' : q' < k := by simpa using hqk'
          have hidx'' : q' = ys.idxOf (mem (lblAddr + 2 * v)) := by
            dsimp at hidx'
            simpa [htab_eq] using hidx'
          have hq' : q' = partFn v := hidx''
          have hpc_eq : st.mem (bufAddr + 4 * n + q') =
              ((Finset.range v).filter fun u => partFn u = q').card := hcnt q' hqk''
          have hpc_le : st.mem (bufAddr + 4 * n + q') ≤ v := by
            rw [hpc_eq]
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          have hr6 : Function.update (Function.update st.regs 13 (st.mem (lblAddr + 2 * v))) 14 q' 6 =
              bufAddr + 3 * n := by simp [h6]
          have hr7 : Function.update (Function.update st.regs 13 (st.mem (lblAddr + 2 * v))) 14 q' 7 =
              bufAddr + 4 * n := by simp [h7]
          have hr12 : Function.update (Function.update st.regs 13 (st.mem (lblAddr + 2 * v))) 14 q' 12 =
              v := by simp [h12]
          have hr14 : Function.update (Function.update st.regs 13 (st.mem (lblAddr + 2 * v))) 14 q' 14 =
              q' := Function.update_self ..
          have hp0 : grpPartId bufAddr n ≤ bufAddr + 3 * n + v := by dsimp only [grpPartId]; omega
          have hp1 : bufAddr + 3 * n + v < grpPartOff bufAddr n := by dsimp only [grpPartOff]; omega
          have hc0 : grpPartId bufAddr n ≤ bufAddr + 4 * n + q' := by dsimp only [grpPartId]; omega
          have hc1 : bufAddr + 4 * n + q' < grpPartOff bufAddr n := by dsimp only [grpPartOff]; omega
          wram_step
          wram_step
          refine runs_store_le (by eval_expr) (by eval_expr; try (split_ifs <;> omega)) ?_ ?_
          · dsimp only [InvCount, grpPartId, grpPartCnt]
            refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
              by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
              by simp [h11], by simp,
              fun u hu => ?_, fun j hj => ?_, ?_⟩, by simp [h12]⟩
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu' | hu_eq
              · have hne1 : bufAddr + 3 * n + u ≠ bufAddr + 4 * n + q' := by omega
                have hne2 : bufAddr + 3 * n + u ≠ bufAddr + 3 * n + v := by omega
                simpa [Function.update_of_ne hne1, Function.update_of_ne hne2] using hpid u hu'
              · subst u
                have hne1 : bufAddr + 3 * n + v ≠ bufAddr + 4 * n + q' := by omega
                simp only [Function.update_of_ne hne1, Function.update_self]
                exact ⟨hq', hqk''⟩
            · rw [Finset.range_add_one, Finset.filter_insert]
              have hnot_mem : v ∉ (Finset.range v).filter fun u => partFn u = j := by simp
              have hne_pc : bufAddr + 4 * n + q' ≠ bufAddr + 3 * n + v := by omega
              by_cases hqj : partFn v = j
              · have hj_eq : j = q' := hqj.symm.trans hq'.symm
                subst hj_eq
                simp [hqj, Finset.card_insert_of_notMem hnot_mem, hpc_eq, ite_eq_right_iff.mpr
                  (fun hc => absurd hc hne_pc)]
              · have hjne : bufAddr + 4 * n + j ≠ bufAddr + 4 * n + q' := by omega
                have hjne2 : bufAddr + 4 * n + j ≠ bufAddr + 3 * n + v := by omega
                simp [Function.update_of_ne hjne, Function.update_of_ne hjne2, hcnt j hj, hqj]
            · exact memFrame_trans hfr
                (memFrame_trans (memFrame_update hp0 hp1) (memFrame_update hc0 hc1))
          · have hmul : 35 * (Nat.log 2 (k + 2) + 2) ≤ 35 * (Nat.log 2 (n + 2) + 2) :=
              Nat.mul_le_mul_left 35 (by omega)
            simp [argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_const,
              Expr.size_load, Expr.size_bin, binSearchContract]
            omega)
  refine (Triple.seq_normal hzero hcount
    (T := fun _ => n * (35 * (Nat.log 2 (n + 2) + 2) + 55) + 20 * n + 40) fun _ _ _ _ => by
    have hmul : k * 15 ≤ n * 15 := Nat.mul_le_mul_right 15 hkn
    have hzero_le : (k - 0) * (6 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5) ≤ 15 * n + 7 := by
      simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega
    have hcnt_eq : (n - 0) * (35 * (Nat.log 2 (n + 2) + 2) + 45 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5) =
        n * (35 * (Nat.log 2 (n + 2) + 2) + 54) + 7 := by
      simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]
    have hdiff : n * (35 * (Nat.log 2 (n + 2) + 2) + 54) + n =
        n * (35 * (Nat.log 2 (n + 2) + 2) + 55) := by ring
    omega).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, hpid, hcnt, hfr⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hpid, hcnt, hfr⟩

lemma groupVertsPrefix_triple {w n k lblAddr bufAddr : ℕ} (p : Program) (mem : ℕ → ℕ)
    (_hk : 1 ≤ k) (hkn : k ≤ n) (hb : bufAddr + 9 * n + 3 < 2 ^ w)
    (_hcnt : ∀ q < k, mem (grpPartCnt bufAddr n + q) ≤ n)
    (hsum : ((List.range k).map fun q => mem (grpPartCnt bufAddr n + q)).sum = n) :
    Triple w p
      (fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      groupVertsPrefixStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem (grpPartOff bufAddr n) = 0 ∧
        st.mem (grpPartOff bufAddr n + k) = n ∧
        (∀ q < k,
          st.mem (grpPartCur bufAddr n + q) = st.mem (grpPartOff bufAddr n + q) ∧
          st.mem (grpPartOff bufAddr n + (q + 1)) =
            st.mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q) ∧
          st.mem (grpPartOff bufAddr n + q) + mem (grpPartCnt bufAddr n + q) ≤ n) ∧
        MemFrame mem st.mem (grpPartOff bufAddr n) (grpPartVerts bufAddr n))
      (fun _ => 35 * n + 35) := by
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun q st =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 12 = q ∧
    st.regs 13 = ((List.range q).map fun j => mem (grpPartCnt bufAddr n + j)).sum ∧
    st.mem (grpPartOff bufAddr n) = 0 ∧
    st.mem (grpPartOff bufAddr n + q) = st.regs 13 ∧
    (∀ j < q,
      st.mem (grpPartCur bufAddr n + j) = st.mem (grpPartOff bufAddr n + j) ∧
      st.mem (grpPartOff bufAddr n + (j + 1)) =
        st.mem (grpPartOff bufAddr n + j) + mem (grpPartCnt bufAddr n + j) ∧
      st.mem (grpPartOff bufAddr n + j) + mem (grpPartCnt bufAddr n + j) ≤ n) ∧
    MemFrame mem st.mem (grpPartOff bufAddr n) (grpPartVerts bufAddr n)
  let PreAssign := fun st : State =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.mem (grpPartOff bufAddr n) = 0 ∧
    MemFrame mem st.mem (grpPartOff bufAddr n) (grpPartVerts bufAddr n)
  let PreLoop := fun st : State =>
    st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
    st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
    st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
    st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
    st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
    st.regs 13 = 0 ∧ st.mem (grpPartOff bufAddr n) = 0 ∧
    MemFrame mem st.mem (grpPartOff bufAddr n) (grpPartVerts bufAddr n)
  have hstore : Triple w p
      (fun st =>
        st.regs 0 = n ∧ st.regs 1 = lblAddr ∧ st.regs 2 = bufAddr ∧ st.regs 3 = k ∧
        st.regs 4 = grpSortBuf bufAddr n ∧ st.regs 5 = grpUniqLbl bufAddr n ∧
        st.regs 6 = grpPartId bufAddr n ∧ st.regs 7 = grpPartCnt bufAddr n ∧
        st.regs 8 = grpPartOff bufAddr n ∧ st.regs 9 = grpPartCur bufAddr n ∧
        st.regs 10 = grpPartVerts bufAddr n ∧ st.regs 11 = grpLocalId bufAddr n ∧
        st.mem = mem)
      (.store (.reg 8) (.const 0)) (normalPost PreAssign) (fun _ => 3) := by
    intro st ω ⟨h0, h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩
    have hlo : grpPartOff bufAddr n ≤ bufAddr + 5 * n := by dsimp only [grpPartOff]; omega
    have hhi : bufAddr + 5 * n < grpPartVerts bufAddr n := by dsimp only [grpPartVerts]; omega
    dsimp only [grpPartOff, grpPartVerts] at h8 ⊢
    refine runs_start_le ?_
    wram_run
    · dsimp only [PreAssign, grpPartOff]
      exact ⟨by simp [h0], by simp [h1'], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
        by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10], by simp [h11],
        Function.update_self .., by subst hm; exact memFrame_update hlo hhi⟩
    · wram_cost
  have hassign : Triple w p PreAssign (.assign 13 (.const 0)) (normalPost PreLoop) (fun _ => 2) := by
    intro st ω ⟨h0, h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hz, hfr⟩
    refine runs_start_le ?_
    wram_run
    · exact ⟨by simp [h0], by simp [h1'], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
        by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10], by simp [h11],
        by simp, hz, hfr⟩
    · wram_cost
  have hpref_sum_le : ∀ m ≤ k,
      ((List.range m).map fun j => mem (grpPartCnt bufAddr n + j)).sum ≤ n := by
    intro m hm
    have hsplit : List.range k = List.range m ++ (List.range (k - m)).map (fun x => m + x) := by
      have hr : List.range (m + (k - m)) = List.range m ++ (List.range (k - m)).map (fun x => m + x) :=
        List.range_add
      rwa [show m + (k - m) = k by omega] at hr
    have hsum' := hsum
    rw [hsplit, List.map_append, List.sum_append] at hsum'
    omega
  have hloop := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 3)
    (body := seqStmts
      [ .assign 14 (.load (.bin .add (.reg 7) (.reg 12)))
      , .store (.bin .add (.reg 9) (.reg 12)) (.reg 13)
      , .assign 13 (.bin .add (.reg 13) (.reg 14))
      , .store (.bin .add (.reg 8) (.bin .add (.reg 12) (.const 1))) (.reg 13) ])
    (P := PreLoop)
    (Inv := Inv) 24 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, hzero, hfr⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by simp,
        by simp [h13], by simpa using hzero, by simpa [h13] using hzero, fun j hj => by omega,
        hfr⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.1; eval_expr)
    (fun q _ hqlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hz, hqoff, hp, hfr⟩
      dsimp only [grpPartCnt, grpPartOff, grpPartCur, grpPartVerts] at h7 h8 h9 h10 hz hqoff hp hfr ⊢
      have hcnt_eq : st.mem (bufAddr + 4 * n + q) = mem (bufAddr + 4 * n + q) :=
        hfr (bufAddr + 4 * n + q) (Or.inl (by omega))
      have hsum_q1 : ((List.range (q + 1)).map fun j => mem (grpPartCnt bufAddr n + j)).sum ≤ n :=
        hpref_sum_le (q + 1) hqlt
      have hsum_step : ((List.range (q + 1)).map fun j => mem (grpPartCnt bufAddr n + j)).sum =
          st.regs 13 + mem (grpPartCnt bufAddr n + q) := by
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton, h13]
      have h13_le : st.regs 13 + mem (grpPartCnt bufAddr n + q) ≤ n := by rw [← hsum_step]; exact hsum_q1
      dsimp only [grpPartCnt] at hsum_step h13_le
      have h8lo : grpPartOff bufAddr n ≤ bufAddr + 5 * n + (q + 1) := by dsimp only [grpPartOff]; omega
      have h8hi : bufAddr + 5 * n + (q + 1) < grpPartVerts bufAddr n := by
        dsimp only [grpPartVerts]; omega
      have h9lo : grpPartOff bufAddr n ≤ bufAddr + 6 * n + 1 + q := by dsimp only [grpPartOff]; omega
      have h9hi : bufAddr + 6 * n + 1 + q < grpPartVerts bufAddr n := by
        dsimp only [grpPartVerts]; omega
      refine runs_start_le ?_
      dsimp only [seqStmts]
      wram_run
      · dsimp only [Inv, grpPartCnt, grpPartOff, grpPartCur]
        simp only [h8, h9, h12, h13]
        refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
          by simp [h5], by simp [h6], by simp [h7], by simp [h8], by simp [h9], by simp [h10],
          by simp [h11], by simp,
          ?_, ?_, ?_, fun j hj => ?_, ?_⟩, by simp [h12]⟩
        · dsimp only [grpPartCnt]; simp [hcnt_eq, List.range_succ]
        · simp only [Function.update_of_ne (by omega : bufAddr + 5 * n ≠ bufAddr + 5 * n + (q + 1)),
            Function.update_of_ne (by omega : bufAddr + 5 * n ≠ bufAddr + 6 * n + 1 + q)]
          exact hz
        · simp [hcnt_eq]
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj_eq
          · have hpj := hp j hj'
            have h1e : bufAddr + 6 * n + 1 + j ≠ bufAddr + 5 * n + (q + 1) := by omega
            have h2e : bufAddr + 6 * n + 1 + j ≠ bufAddr + 6 * n + 1 + q := by omega
            have h3e : bufAddr + 5 * n + j ≠ bufAddr + 5 * n + (q + 1) := by omega
            have h4e : bufAddr + 5 * n + j ≠ bufAddr + 6 * n + 1 + q := by omega
            have h5e : bufAddr + 5 * n + (j + 1) ≠ bufAddr + 5 * n + (q + 1) := by omega
            have h6e : bufAddr + 5 * n + (j + 1) ≠ bufAddr + 6 * n + 1 + q := by omega
            simpa [Function.update_of_ne h1e, Function.update_of_ne h2e,
              Function.update_of_ne h3e, Function.update_of_ne h4e,
              Function.update_of_ne h5e, Function.update_of_ne h6e] using hpj
          · subst j
            have hne1 : bufAddr + 6 * n + 1 + q ≠ bufAddr + 5 * n + (q + 1) := by omega
            have hne2 : bufAddr + 5 * n + q ≠ bufAddr + 5 * n + (q + 1) := by omega
            have hne3 : bufAddr + 5 * n + q ≠ bufAddr + 6 * n + 1 + q := by omega
            simp only [Function.update_of_ne hne1, Function.update_self,
              Function.update_of_ne hne2, Function.update_of_ne hne3, hqoff]
            exact ⟨h13.symm, by simp [h13, hcnt_eq], h13_le⟩
        · exact memFrame_trans hfr (memFrame_trans (memFrame_update h9lo h9hi) (memFrame_update h8lo h8hi))
      · wram_cost)
  have htail := Triple.seq_normal hassign hloop (T := fun _ => 35 * n + 25)
    (fun _ _ _ _ => by simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega)
  refine (Triple.seq_normal hstore htail (T := fun _ => 35 * n + 35)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _, h13, hz, hqoff, hp, hfr⟩
    refine ⟨h0, h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hz, ?_, ?_, hfr⟩
    · simpa [h13, hsum] using hqoff
    · intro q hqk
      have hq := hp q hqk
      exact ⟨hq.1, hq.2.1, hq.2.2⟩

end MinCostFlow.Expander
