module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase
import Mathlib.Tactic.Linarith

/-!
# Vertex-Array Word-RAM Primitives for `OneShot` and `Core`

Implements and verifies four deterministic (`NoRand`), strictly local Word-RAM helper procedures
used throughout `OneShot` and `Core`:

* `copyWordsProc`: copies `len` consecutive words from `src` to `dst` in `O(len + 1)` time.
* `initRangeProc`: writes `[0, 1, ..., n - 1]` (giving `VertsAt mem' dst n (Finset.range n)`)
  in `O(n + 1)` time.
* `filterSetProc (keepMarked : Bool)`: unified 3-loop local filter over a sorted vertex array
  `X` (`VertsAt`) and a subset array `S` (`NodupVertsAt`), using a reusable zero-initialized
  marker buffer `locAddr` of length `n` (never scanning `range n`, restoring `locAddr` to all
  zeros on exit):
  - `filterDiffProc = filterSetProc false`: writes `(X \ S).sort (· ≤ ·)` (`VertsAt`) and returns
    `|X \ S|` in `O(|X| + |S| + 1)` time.
  - `filterInterProc = filterSetProc true`: writes `(X ∩ S).sort (· ≤ ·)` (`VertsAt`) and returns
    `|X ∩ S|` in `O(|X| + |S| + 1)` time.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `copyWordsProc` -/

/-- Copy `len = r0` words from `src = r1` to `dst = r2`, returning `0`. -/
def copyWordsProc : Stmt :=
  seqStmts
    [ forRange 3 (.const 0) (.reg 0)
        (seqStmts
          [ .assign 4 (.load (.bin .add (.reg 1) (.reg 3)))
          , .store (.bin .add (.reg 2) (.reg 3)) (.reg 4) ])
    , .ret (.const 0) ]

def copyWordsCost (len : ℕ) : ℕ := 30 * len + 30

def copyWordsContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ len src dst : ℕ,
      args = [len, src, dst] ∧
      src + len < 2 ^ w ∧ dst + len < 2 ^ w ∧ len + 1 < 2 ^ w ∧ 4 < 2 ^ w ∧
      DisjointRange dst len src len ∧
      (∀ i < len, mem (src + i) < 2 ^ w)
  post args mem v mem' :=
    let len := args.getD 0 0
    let src := args.getD 1 0
    let dst := args.getD 2 0
    v = 0 ∧
    (∀ i < len, mem' (dst + i) = mem (src + i)) ∧
    MemFrame mem mem' dst (dst + len)
  cost args _ := copyWordsCost (args.getD 0 0)

/-! ## 2. `initRangeProc` -/

/-- Write `[0, 1, ..., n - 1]` (`n = r0`) at `dst = r1`, returning `0`. -/
def initRangeProc : Stmt :=
  seqStmts
    [ forRange 2 (.const 0) (.reg 0)
        (.store (.bin .add (.reg 1) (.reg 2)) (.reg 2))
    , .ret (.const 0) ]

def initRangeCost (n : ℕ) : ℕ := 25 * n + 30

def initRangeContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ n dst : ℕ,
      args = [n, dst] ∧
      dst + n < 2 ^ w ∧ n + 1 < 2 ^ w ∧ 4 < 2 ^ w
  post args mem v mem' :=
    let n := args.getD 0 0
    let dst := args.getD 1 0
    v = 0 ∧
    VertsAt mem' dst n (Finset.range n) ∧
    MemFrame mem mem' dst (dst + n)
  cost args _ := initRangeCost (args.getD 0 0)

/-! ## 3. `filterSetProc` (`filterDiffProc` and `filterInterProc`) -/

/-- Unified local vertex-set filter (`args = [k, xAddr, lenS, sAddr, locAddr, outAddr]`):
marks `locAddr[sAddr[j]] := 1` for `j < lenS`, scans `i < k` keeping `xAddr[i]` iff its mark
matches `keepMarked`, clears `locAddr[sAddr[j]] := 0`, and returns the output length `cnt`. -/
def filterSetProc (keepMarked : Bool) : Stmt :=
  let condExpr : Expr :=
    if keepMarked then .bin .lt (.const 0) (.reg 9) else .bin .eq (.reg 9) (.const 0)
  seqStmts
    [ forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const 1) ])
    , .assign 7 (.const 0)
    , forRange 6 (.const 0) (.reg 0)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 1) (.reg 6)))
          , .assign 9 (.load (.bin .add (.reg 4) (.reg 8)))
          , .cond condExpr
              (seqStmts
                [ .store (.bin .add (.reg 5) (.reg 7)) (.reg 8)
                , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
              .nop ])
    , forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const 0) ])
    , .ret (.reg 7) ]

/-- Filter sorted `X` removing elements of `S`: writes `(X \ S).sort (· ≤ ·)`. -/
def filterDiffProc : Stmt := filterSetProc false

/-- Filter sorted `X` keeping elements of `S`: writes `(X ∩ S).sort (· ≤ ·)`. -/
def filterInterProc : Stmt := filterSetProc true

def filterSetCost (k lenS : ℕ) : ℕ := 60 * k + 70 * lenS + 100

def FilterSetWordBound (w n k lenS xAddr sAddr locAddr outAddr : ℕ) : Prop :=
  xAddr + k < 2 ^ w ∧
  sAddr + lenS < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outAddr + k < 2 ^ w ∧
  k + 1 < 2 ^ w ∧
  lenS + 1 < 2 ^ w ∧
  16 < 2 ^ w

def FilterSetDisjoint (n k lenS xAddr sAddr locAddr outAddr : ℕ) : Prop :=
  DisjointRange locAddr n xAddr k ∧
  DisjointRange locAddr n sAddr lenS ∧
  DisjointRange locAddr n outAddr k ∧
  DisjointRange outAddr k xAddr k ∧
  DisjointRange outAddr k sAddr lenS

/-- Contract for `filterSetProc keepMarked`: writes `(X ∩ S).sort` if `keepMarked = true` or
`(X \ S).sort` if `keepMarked = false` at `outAddr`, returns its cardinality, restores `locAddr`
to all zeros, and preserves memory outside `[outAddr, outAddr + k)`. -/
def filterSetContract (w : ℕ) (keepMarked : Bool) : Contract where
  pre args mem :=
    ∃ (n k xAddr lenS sAddr locAddr outAddr : ℕ) (X S : Finset ℕ),
      args = [k, xAddr, lenS, sAddr, locAddr, outAddr] ∧
      VertsAt mem xAddr k X ∧
      NodupVertsAt mem sAddr lenS S ∧
      X ⊆ Finset.range n ∧ S ⊆ Finset.range n ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      FilterSetWordBound w n k lenS xAddr sAddr locAddr outAddr ∧
      FilterSetDisjoint n k lenS xAddr sAddr locAddr outAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let xAddr := args.getD 1 0
    let lenS := args.getD 2 0
    let sAddr := args.getD 3 0
    let outAddr := args.getD 5 0
    let X := (readList mem xAddr k).toFinset
    let S := (readList mem sAddr lenS).toFinset
    let Y := if keepMarked then X ∩ S else X \ S
    v ≤ k ∧
    VertsAt mem' outAddr v Y ∧
    MemFrame mem mem' outAddr (outAddr + k)
  cost args _ := filterSetCost (args.getD 0 0) (args.getD 2 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 4. `NoRand` Proofs -/

theorem copyWordsProc_noRand : copyWordsProc.NoRand := by
  simp [copyWordsProc, seqStmts, forRange, forUp, Stmt.NoRand]

theorem initRangeProc_noRand : initRangeProc.NoRand := by
  simp [initRangeProc, seqStmts, forRange, forUp, Stmt.NoRand]

theorem filterSetProc_noRand (keepMarked : Bool) : (filterSetProc keepMarked).NoRand := by
  cases keepMarked <;> simp [filterSetProc, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 5. Verification of `copyWordsProc` -/

theorem copyWordsProc_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hb : p.procs[b]? = some copyWordsProc) :
    MeetsContract w p b (copyWordsContract w) := by
  refine meetsContract_of_runs hb fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨len, src, dst, rfl, hsrc_w, hdst_w, hlen1_w, hw4, hdisj, hval_w⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = len ∧ st.regs 1 = src ∧ st.regs 2 = dst ∧ st.regs 3 = i ∧
    (∀ j < i, st.mem (dst + j) = mem (src + j)) ∧
    MemFrame mem st.mem dst (dst + len)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 4 (.load (.bin .add (.reg 1) (.reg 3)))
      , .store (.bin .add (.reg 2) (.reg 3)) (.reg 4) ])
    (P := fun st => st = startState [len, src, dst] mem pos) (Inv := Inv)
    16 0 len (Nat.zero_le len) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        by simp [startState], by simp [startState], by simp [startState], by simp,
        fun j hj => by omega, fun a _ => rfl⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1)
    (fun i _ hilt => by
      intro st ω' ⟨hr0, hr1, hr2, hr3, hcop, hfr⟩
      have hsrc_i : st.mem (src + i) = mem (src + i) :=
        hfr (src + i) (disjointRange_outside hdisj (by omega) (by omega))
      have hvi_w : mem (src + i) < 2 ^ w := hval_w i hilt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := mem (src + i))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr3) (by omega))
          hsrc_i) ?_
      refine runs_store_le (x := dst + i) (v := mem (src + i))
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) (by simp [hr2]))
          (Expr.eval_reg_of_eq (v := i) (by simp [hr3])) (by omega))
        (Expr.eval_reg_of_eq (v := mem (src + i)) (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp, ?_, ?_⟩, by simp [hr3]⟩
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne (by omega)]; exact hcop j (by omega)
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by rcases ha with h | h <;> omega)]
        exact hfr a ha)
  obtain ⟨o₁, st₁, c₁, hrun₁, hInv₁, hc₁⟩ := hloop.runs ω rfl
  cases o₁ with
  | returned _ => exact False.elim hInv₁
  | normal =>
    have hret : Runs w p ω (.ret (.const 0)) st₁ (.returned 0) st₁ 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned 0, st₁, c₁ + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, 2, hrun₁, hret, rfl⟩), ?_, ?_⟩
    · dsimp only [copyWordsContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Outcome.value]
      exact ⟨trivial, hInv₁.2.2.2.2.1, hInv₁.2.2.2.2.2⟩
    · dsimp only [copyWordsContract, copyWordsCost, Expr.size] at hc₁ ⊢
      simp only [List.getD_cons_zero]
      omega

/-! ## 6. Verification of `initRangeProc` -/

theorem initRangeProc_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hb : p.procs[b]? = some initRangeProc) :
    MeetsContract w p b (initRangeContract w) := by
  refine meetsContract_of_runs hb fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, dst, rfl, hdst_w, hn1_w, hw4⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = n ∧ st.regs 1 = dst ∧ st.regs 2 = i ∧
    (∀ j < i, st.mem (dst + j) = j) ∧
    MemFrame mem st.mem dst (dst + n)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 2) (lo := .const 0) (hi := .reg 0)
    (body := .store (.bin .add (.reg 1) (.reg 2)) (.reg 2))
    (P := fun st => st = startState [n, dst] mem pos) (Inv := Inv)
    12 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        by simp [startState], by simp [startState], by simp,
        fun j hj => by omega, fun a _ => rfl⟩)
    (fun _ st _ _ hInv => hInv.2.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1)
    (fun i _ hilt => by
      intro st ω' ⟨hr0, hr1, hr2, hvals, hfr⟩
      refine runs_start_le ?_
      refine runs_store_le (x := dst + i) (v := i)
        (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr2) (by omega))
        (Expr.eval_reg_of_eq hr2) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [hr0], by simp [hr1], by simp, ?_, ?_⟩, by simp [hr2]⟩
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne (by omega)]; exact hvals j (by omega)
      · intro a ha
        dsimp only
        have hne : a ≠ dst + i := by rcases ha with h | h <;> omega
        rw [Function.update_of_ne hne]
        exact hfr a ha)
  obtain ⟨o₁, st₁, c₁, hrun₁, hInv₁, hc₁⟩ := hloop.runs ω rfl
  cases o₁ with
  | returned _ => exact False.elim hInv₁
  | normal =>
    have hret : Runs w p ω (.ret (.const 0)) st₁ (.returned 0) st₁ 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned 0, st₁, c₁ + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, 2, hrun₁, hret, rfl⟩), ?_, ?_⟩
    · dsimp only [initRangeContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Outcome.value]
      refine ⟨trivial, ⟨by simp, ?_⟩, hInv₁.2.2.2.2⟩
      rw [sort_range_eq_list_range]
      intro i hi
      simp only [List.length_range] at hi
      rw [List.getElem_range]
      exact hInv₁.2.2.2.1 i hi
    · dsimp only [initRangeContract, initRangeCost, Expr.size] at hc₁ ⊢
      simp only [List.getD_cons_zero]
      omega

/-! ## 7. Verification of `filterSetProc` -/

private structure FilterRegs (k xAddr lenS sAddr locAddr outAddr : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = k
  r1 : st.regs 1 = xAddr
  r2 : st.regs 2 = lenS
  r3 : st.regs 3 = sAddr
  r4 : st.regs 4 = locAddr
  r5 : st.regs 5 = outAddr

private lemma filterRegs_update_ge {k xAddr lenS sAddr locAddr outAddr : ℕ}
    {st : State} {r v : ℕ} (hr : 6 ≤ r)
    (h : FilterRegs k xAddr lenS sAddr locAddr outAddr st) :
    FilterRegs k xAddr lenS sAddr locAddr outAddr { st with regs := Function.update st.regs r v } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r0,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r1,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r2,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r3,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r4,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact h.r5⟩

private lemma filterRegs_update_mem {k xAddr lenS sAddr locAddr outAddr : ℕ}
    {st : State} {mem' : ℕ → ℕ}
    (h : FilterRegs k xAddr lenS sAddr locAddr outAddr st) :
    FilterRegs k xAddr lenS sAddr locAddr outAddr { st with mem := mem' } :=
  ⟨h.r0, h.r1, h.r2, h.r3, h.r4, h.r5⟩

/-- Loop 1 & Loop 3 helper: writes a constant `val` (`0` or `1`) to `locAddr[sList[j]]` for every
`j < lenS`. -/
private lemma filterMarkLoop_triple {w n k xAddr lenS sAddr locAddr outAddr val : ℕ}
    (p : Program) (mem₀ : ℕ → ℕ) (sList : List ℕ) (st₀ : State)
    (hslen : sList.length = lenS) (hs_lt : ∀ u ∈ sList, u < n)
    (hs_at : ListAt st₀.mem sAddr sList)
    (hdisj_ls : DisjointRange locAddr n sAddr lenS)
    (_hdisj_lo : DisjointRange locAddr n outAddr k)
    (hpr0 : PreservedOutside2 mem₀ st₀.mem locAddr (locAddr + n) outAddr (outAddr + k))
    (hval_w : val < 2 ^ w)
    (hw : FilterSetWordBound w n k lenS xAddr sAddr locAddr outAddr)
    (hregs : FilterRegs k xAddr lenS sAddr locAddr outAddr st₀) :
    Triple w p (fun st => st = st₀)
      (forRange 6 (.const 0) (.reg 2)
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
          , .store (.bin .add (.reg 4) (.reg 8)) (.const val) ]))
      (normalPost fun st' =>
        FilterRegs k xAddr lenS sAddr locAddr outAddr st' ∧
        st'.regs 7 = st₀.regs 7 ∧
        PreservedOutside2 mem₀ st'.mem locAddr (locAddr + n) outAddr (outAddr + k) ∧
        (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st'.mem a = st₀.mem a) ∧
        (∀ u < n, st'.mem (locAddr + u) = if u ∈ sList then val else st₀.mem (locAddr + u)))
      (fun _ => 30 * lenS + 25) := by
  rcases hw with ⟨_, hs_w, hloc_w, _, _, hlenS1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    FilterRegs k xAddr lenS sAddr locAddr outAddr st ∧
    st.regs 6 = j ∧ st.regs 7 = st₀.regs 7 ∧
    PreservedOutside2 mem₀ st.mem locAddr (locAddr + n) outAddr (outAddr + k) ∧
    (∀ a, (a < locAddr ∨ locAddr + n ≤ a) → st.mem a = st₀.mem a) ∧
    (∀ u < n, st.mem (locAddr + u) = if u ∈ sList.take j then val else st₀.mem (locAddr + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body := seqStmts
      [ .assign 8 (.load (.bin .add (.reg 3) (.reg 6)))
      , .store (.bin .add (.reg 4) (.reg 8)) (.const val) ])
    (P := fun st => st = st₀) (Inv := Inv) 16 0 lenS (Nat.zero_le lenS) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        filterRegs_update_ge (r := 6) (by decide) hregs, by simp, by simp,
        hpr0, fun _ _ => rfl, fun u _ => by simp⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r2)
    (fun j _ hjlt => by
      intro st ω' ⟨hr, hj, hr7, hpr, hloc_fr, hmap⟩
      have hj_lt : j < sList.length := hslen ▸ hjlt
      have hu_lt : sList[j]'hj_lt < n := hs_lt _ (List.getElem_mem hj_lt)
      have hmem_s : st.mem (sAddr + j) = sList[j]'hj_lt := by
        rw [hloc_fr (sAddr + j) (disjointRange_outside hdisj_ls (by omega) (by omega))]
        exact hs_at j hj_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := sList[j]'hj_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r3) (Expr.eval_reg_of_eq hj) (by omega))
          hmem_s) ?_
      refine runs_store_le (x := locAddr + sList[j]'hj_lt) (v := val)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r4]))
          (Expr.eval_reg_of_eq (v := sList[j]'hj_lt) (by simp)) (by omega))
        (Expr.eval_const hval_w) ?_ (by simp [Expr.size])
      refine ⟨⟨filterRegs_update_ge (r := 6) (by decide)
          (filterRegs_update_mem (filterRegs_update_ge (r := 8) (by decide) hr)),
        by simp, by simp [hr7], ?_, ?_, ?_⟩, by simp [hj]⟩
      · intro a hal hao
        dsimp only
        rw [Function.update_of_ne (by rcases hal with h | h <;> omega)]
        exact hpr a hal hao
      · intro a hal
        dsimp only
        rw [Function.update_of_ne (by rcases hal with h | h <;> omega)]
        exact hloc_fr a hal
      · intro u hu
        dsimp only
        rw [List.take_succ_eq_append_getElem hj_lt]
        by_cases huv : u = sList[j]'hj_lt
        · subst huv
          simp only [Function.update_self, List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
        · rw [Function.update_of_ne (by omega)]
          simp only [List.mem_append, List.mem_singleton, huv, or_false]
          exact hmap u hu)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro o st' hpost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hr, _, hr7, hpr, hloc_fr, hmap⟩
    refine ⟨hr, hr7, hpr, hloc_fr, fun u hu => ?_⟩
    have ht := hmap u hu
    rw [← hslen, List.take_length] at ht
    exact ht

theorem filterSetProc_meetsContract {w : ℕ} {p : Program} {b : ℕ} (keepMarked : Bool)
    (hb : p.procs[b]? = some (filterSetProc keepMarked)) :
    MeetsContract w p b (filterSetContract w keepMarked) := by
  refine meetsContract_of_runs hb fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, k, xAddr, lenS, sAddr, locAddr, outAddr, X, S, rfl,
    hXat, hSat, hXn, hSn, hloc0, hw, hdisj⟩
  have hXlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← hXat.1]
  have hXread : readList mem xAddr k = X.sort (· ≤ ·) := by
    rw [← hXlen]; exact readList_eq_of_listAt hXat.2
  have hXfin : (readList mem xAddr k).toFinset = X := by rw [hXread]; ext v; simp
  set sList := readList mem sAddr lenS
  have hsLen : sList.length = lenS := by simp [sList, readList]
  have hsAt : ListAt mem sAddr sList := fun i hi => by
    simp only [sList, readList, List.getElem_map, List.getElem_range]
  have hsFin : sList.toFinset = S := hSat.2
  have hs_lt : ∀ u ∈ sList, u < n := fun u hu =>
    Finset.mem_range.mp (hSn (hsFin ▸ List.mem_toFinset.mpr hu))
  have hx_lt : ∀ u ∈ X.sort (· ≤ ·), u < n := fun u hu =>
    Finset.mem_range.mp (hXn ((Finset.mem_sort _).mp hu))
  rcases hdisj with ⟨hd_lx, hd_ls, hd_lo, hd_ox, hd_os⟩
  rcases hw with ⟨hx_w, hs_w, hloc_w, hout_w, hk1_w, hlenS1_w, hw16⟩
  have hw2 : 1 < 2 ^ w := by omega
  have hregs0 : FilterRegs k xAddr lenS sAddr locAddr outAddr
      (startState [k, xAddr, lenS, sAddr, locAddr, outAddr] mem pos) :=
    ⟨by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState]⟩
  -- Loop 1: mark `S` in `locAddr`.
  have hL1 := filterMarkLoop_triple (val := 1) p mem sList
    (startState [k, xAddr, lenS, sAddr, locAddr, outAddr] mem pos)
    hsLen hs_lt hsAt hd_ls hd_lo (fun _ _ _ => rfl) hw2
    ⟨hx_w, hs_w, hloc_w, hout_w, hk1_w, hlenS1_w, hw16⟩ hregs0
  obtain ⟨o₁, st₁, c₁, hrun₁, hInv₁, hc₁⟩ := hL1.runs ω rfl
  cases o₁ with
  | returned _ => exact False.elim hInv₁
  | normal =>
  rcases hInv₁ with ⟨hr₁, _, hpr₁, hloc_fr₁, hmap₁⟩
  -- Assign `r7 := 0`.
  set st₂ : State := { st₁ with regs := Function.update st₁.regs 7 0 }
  have hrun₂ : Runs w p ω (.assign 7 (.const 0)) st₁ .normal st₂ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  -- Loop 2: scan sorted `X` and write kept elements to `outAddr`.
  let pred : ℕ → Bool := fun v => if keepMarked then decide (v ∈ S) else decide (v ∉ S)
  let condExpr : Expr :=
    if keepMarked then .bin .lt (.const 0) (.reg 9) else .bin .eq (.reg 9) (.const 0)
  let Inv2 : ℕ → State → Prop := fun i st =>
    let pref := ((X.sort (· ≤ ·)).take i).filter pred
    FilterRegs k xAddr lenS sAddr locAddr outAddr st ∧
    st.regs 6 = i ∧ st.regs 7 = pref.length ∧
    PreservedOutside2 mem st.mem locAddr (locAddr + n) outAddr (outAddr + k) ∧
    (∀ a, (a < outAddr ∨ outAddr + k ≤ a) → st.mem a = st₁.mem a) ∧
    ListAt st.mem outAddr pref
  have hL2 := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := seqStmts
      [ .assign 8 (.load (.bin .add (.reg 1) (.reg 6)))
      , .assign 9 (.load (.bin .add (.reg 4) (.reg 8)))
      , .cond condExpr
          (seqStmts
            [ .store (.bin .add (.reg 5) (.reg 7)) (.reg 8)
            , .assign 7 (.bin .add (.reg 7) (.const 1)) ])
          .nop ])
    (P := fun st => st = st₂) (Inv := Inv2) 45 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega),
        filterRegs_update_ge (r := 6) (by decide) (filterRegs_update_ge (r := 7) (by decide) hr₁),
        by simp, by simp [st₂], hpr₁, fun _ _ => rfl, fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r0)
    (fun i _ hilt => by
      intro st ω' ⟨hr, hi, hcnt, hpr, hout_fr, hlist⟩
      have hi_lt : i < (X.sort (· ≤ ·)).length := hXlen ▸ hilt
      set u := (X.sort (· ≤ ·))[i]'hi_lt
      have hu_lt : u < n := hx_lt u (List.getElem_mem hi_lt)
      have hmem_x : st.mem (xAddr + i) = u := by
        rw [hpr (xAddr + i)
          (disjointRange_outside hd_lx (by omega) (by omega))
          (disjointRange_outside hd_ox (by omega) (by omega))]
        exact hXat.2 i hi_lt
      have hmem_loc : st.mem (locAddr + u) = if u ∈ S then 1 else 0 := by
        rw [hout_fr (locAddr + u) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
          hmap₁ u hu_lt]
        dsimp only [startState]
        rw [hloc0 u hu_lt]
        have hmiff : u ∈ sList ↔ u ∈ S := by rw [← hsFin, List.mem_toFinset]
        simp only [hmiff]
      have hcnt_le : ((X.sort (· ≤ ·)).take i |>.filter pred).length ≤ i := by
        calc _ ≤ ((X.sort (· ≤ ·)).take i).length := List.length_filter_le _ _
          _ ≤ i := by rw [List.length_take]; exact Nat.min_le_left _ _
      set markVal : ℕ := if u ∈ S then 1 else 0
      have hcond_eval : condExpr.eval w
          { mem := st.mem, regs := Function.update (Function.update st.regs 8 u) 9 markVal, pos := st.pos } =
          some (if pred u then 1 else 0) := by
        cases keepMarked <;> by_cases huS : u ∈ S <;>
          simp [condExpr, pred, markVal, huS, Expr.eval, BinOp.eval, hw2]
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r1) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_x) ?_
      refine runs_seq_assign_le (v := markVal)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r4]))
            (Expr.eval_reg_of_eq (v := u) (by simp)) (by omega))
          hmem_loc) ?_
      refine runs_cond_le hcond_eval ?_ ?_
      · intro hpred_ne
        have hpu : pred u = true := by by_cases h : pred u <;> simp_all
        dsimp only [seqStmts]
        refine runs_seq_store_le (x := outAddr + ((X.sort (· ≤ ·)).take i |>.filter pred).length)
          (v := u)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := outAddr) (by simp [hr.r5]))
            (Expr.eval_reg_of_eq (v := ((X.sort (· ≤ ·)).take i |>.filter pred).length)
              (by simp [hcnt])) (by omega))
          (Expr.eval_reg_of_eq (v := u) (by simp)) ?_
        refine runs_assign_le (v := ((X.sort (· ≤ ·)).take i |>.filter pred).length + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := ((X.sort (· ≤ ·)).take i |>.filter pred).length)
              (by simp [hcnt]))
            (Expr.eval_const hw2) (by omega)) ?_ (by cases keepMarked <;> simp [condExpr, Expr.size])
        have htake : ((X.sort (· ≤ ·)).take (i + 1)).filter pred =
            ((X.sort (· ≤ ·)).take i).filter pred ++ [u] := by
          rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
            List.filter_nil, hpu]; simp [u]
        refine ⟨⟨filterRegs_update_ge (r := 6) (by decide)
            (filterRegs_update_ge (r := 7) (by decide)
              (filterRegs_update_mem (filterRegs_update_ge (r := 9) (by decide)
                (filterRegs_update_ge (r := 8) (by decide) hr)))),
          by simp, by rw [htake, List.length_append, List.length_singleton]; simp,
          ?_, ?_, ?_⟩, by simp [hi]⟩
        · intro a hal hao
          dsimp only
          rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
          exact hpr a hal hao
        · intro a hao
          dsimp only
          rw [Function.update_of_ne (by rcases hao with h | h <;> omega)]
          exact hout_fr a hao
        · intro j hj
          dsimp only
          revert hj
          rw [htake]
          intro hj
          rw [List.length_append, List.length_singleton] at hj
          by_cases hjeq : j = ((X.sort (· ≤ ·)).take i |>.filter pred).length
          · subst hjeq; simp
          · have hjlt' : j < ((X.sort (· ≤ ·)).take i |>.filter pred).length := by omega
            rw [Function.update_of_ne (by omega), List.getElem_append_left hjlt']
            exact hlist j hjlt'
      · intro hpred_eq
        have hpu : pred u = false := by by_cases h : pred u <;> simp_all
        refine runs_nop_le ?_ (by cases keepMarked <;> simp [condExpr, Expr.size])
        have htake : ((X.sort (· ≤ ·)).take (i + 1)).filter pred =
            ((X.sort (· ≤ ·)).take i).filter pred := by
          rw [List.take_succ_eq_append_getElem hi_lt, List.filter_append, List.filter_cons,
            List.filter_nil, hpu]; simp
        refine ⟨⟨filterRegs_update_ge (r := 6) (by decide)
            (filterRegs_update_ge (r := 9) (by decide) (filterRegs_update_ge (r := 8) (by decide) hr)),
          by simp, by rw [htake]; simp [hcnt], hpr, hout_fr, by rw [htake]; exact hlist⟩,
          by simp [hi]⟩)
  obtain ⟨o₃, st₃, c₃, hrun₃, hInv₃, hc₃⟩ := hL2.runs ω rfl
  cases o₃ with
  | returned _ => exact False.elim hInv₃
  | normal =>
  rcases hInv₃ with ⟨hr₃, _, hcnt₃, hpr₃, hout_fr₃, hlist₃⟩
  -- Loop 3: clear `S` in `locAddr`.
  have hsAt₃ : ListAt st₃.mem sAddr sList := fun i hi => by
    rw [hpr₃ (sAddr + i)
      (disjointRange_outside hd_ls (by omega) (by omega))
      (disjointRange_outside hd_os (by omega) (by omega))]
    exact hsAt i hi
  have hL3 := filterMarkLoop_triple (val := 0) p mem sList st₃
    hsLen hs_lt hsAt₃ hd_ls hd_lo hpr₃ (by omega)
    ⟨hx_w, hs_w, hloc_w, hout_w, hk1_w, hlenS1_w, hw16⟩ hr₃
  obtain ⟨o₄, st₄, c₄, hrun₄, hInv₄, hc₄⟩ := hL3.runs ω rfl
  cases o₄ with
  | returned _ => exact False.elim hInv₄
  | normal =>
  rcases hInv₄ with ⟨_, hr7₄, hpr₄, hloc_fr₄, hmap₄⟩
  -- Return `r7`.
  set finalList := (X.sort (· ≤ ·)).filter pred
  have hfinal_eq : ((X.sort (· ≤ ·)).take k).filter pred = finalList := by
    rw [← hXlen, List.take_length]
  rw [hfinal_eq] at hcnt₃ hlist₃
  have hret_eval : (Expr.reg 7).eval w st₄ = some finalList.length := by
    rw [Expr.eval_reg_of_eq (hr7₄.trans hcnt₃)]
  have hret : Runs w p ω (.ret (.reg 7)) st₄ (.returned finalList.length) st₄ 2 :=
    runs_ret_iff.mpr ⟨finalList.length, hret_eval, rfl, rfl, rfl⟩
  -- Chain the 5 stages.
  have hrun_full : Runs w p ω (filterSetProc keepMarked)
      (startState [k, xAddr, lenS, sAddr, locAddr, outAddr] mem pos)
      (.returned finalList.length) st₄ (c₁ + (2 + (c₃ + (c₄ + 2 + 1) + 1) + 1) + 1) := by
    unfold filterSetProc seqStmts
    exact runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, _, hrun₁,
      runs_seq_iff.mpr (Or.inr ⟨st₂, 2, _, hrun₂,
        runs_seq_iff.mpr (Or.inr ⟨st₃, c₃, _, hrun₃,
          runs_seq_iff.mpr (Or.inr ⟨st₄, c₄, 2, hrun₄, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨.returned finalList.length, st₄, _, hrun_full, ?_, ?_⟩
  · dsimp only [filterSetContract]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Outcome.value]
    rw [hXfin, hsFin]
    have hsortY : finalList = (if keepMarked then X ∩ S else X \ S).sort (· ≤ ·) := by
      cases keepMarked
      · simp only [finalList, pred, Bool.false_eq_true, ↓reduceIte]
        exact filter_sort_eq_sort_sdiff X S
      · simp only [finalList, pred, ↓reduceIte]
        exact filter_sort_eq_sort_inter X S
    have hle_k : finalList.length ≤ k := by
      rw [← hXlen]; exact List.length_filter_le _ _
    refine ⟨hle_k, ⟨by rw [hsortY, Finset.length_sort], ?_⟩, ?_⟩
    · rw [← hsortY]
      intro i hi
      rw [hloc_fr₄ (outAddr + i) (disjointRange_outside hd_lo (by omega) (by omega))]
      exact hlist₃ i hi
    · intro a ha
      by_cases hloc : locAddr ≤ a ∧ a < locAddr + n
      · obtain ⟨hlo, hhi⟩ := hloc
        have heq : a = locAddr + (a - locAddr) := by omega
        rw [heq, hmap₄ (a - locAddr) (by omega)]
        by_cases hm : a - locAddr ∈ sList
        · simp only [hm, ↓reduceIte, hloc0 (a - locAddr) (by omega)]
        · simp only [hm, ↓reduceIte]
          rw [hout_fr₃ (locAddr + (a - locAddr)) (disjointRange_outside hd_lo.symm (by omega) (by omega)),
            hmap₁ (a - locAddr) (by omega)]
          simp only [hm, ↓reduceIte]
          rfl
      · exact hpr₄ a (by omega) ha
  · dsimp only [filterSetContract, filterSetCost, Expr.size] at hc₁ hc₃ hc₄ ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega

end MinCostFlow.ExpanderDecomp
