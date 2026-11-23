module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCBase
public import MinCostFlow.ExpanderDecomp.ProgStepCLeftoverBase
public import MinCostFlow.ExpanderDecomp.ProgStepBMath

import Mathlib.Tactic.Linarith

/-!
# Step B Reusable Word-RAM Primitives (`ProgStepBPrim`)

Implements and verifies four deterministic (`NoRand`), strictly local Word-RAM loop primitives
used by Step B (`ProgStepB*.lean`), with zero scans of `range G.n`:

* `sbMarkListStmt` / `sbMarkList_triple`: sets `mem[loc + u] := val` for every vertex `u` in a
  contiguous list at `src` (`O(|xs|)`).
* `sbPartitionStmt` / `sbPartition_triple`: partitions a contiguous list `xs` into two lists
  `inDst` (`mem[loc + u] ≠ 0`) and `outDst` (`mem[loc + u] = 0`) preserving original order
  (`O(|xs|)`).
* `sbCopyCutZeroStmt` / `sbCopyCutZero_triple`: copies a router cut `[1, lenU, u_0, ...]` into
  `CoreOutAt` format `[0, lenU, u_0, ...]` at `dst` (`O(lenU)`).
* `sbZipDualStmt` / `sbZipDual_triple`: zips `min (cntA, cntB)` unmatched vertex pairs into both
  `fAddr + 2 * fakeM` and `wEdgesAddr + 2 * wm`, advancing both edge counts (`O(min cntA cntB)`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Statements (`NoRand`) -/

/-- Set `mem[rLoc + u] := rVal` for `rLen` vertices stored at `rSrc`. -/
def sbMarkListStmt (rSrc rLen rLoc rVal rI rU : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rLen) (
    seqStmts [
      .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
      .store (.bin .add (.reg rLoc) (.reg rU)) (.reg rVal)
    ]
  )

theorem sbMarkListStmt_noRand (rSrc rLen rLoc rVal rI rU : ℕ) :
    (sbMarkListStmt rSrc rLen rLoc rVal rI rU).NoRand := by
  simp [sbMarkListStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Partition `rLen` vertices at `rSrc` into `rInDst` (where `mem[rLoc + u] ≠ 0`, count `rInCnt`)
and `rOutDst` (where `mem[rLoc + u] = 0`, count `rOutCnt`), preserving relative order. -/
def sbPartitionStmt (rSrc rLen rLoc rInDst rOutDst rInCnt rOutCnt rI rU : ℕ) : Stmt :=
  seqStmts [
    .assign rInCnt (.const 0),
    .assign rOutCnt (.const 0),
    forRange rI (.const 0) (.reg rLen) (
      seqStmts [
        .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
        .cond (.bin .eq (.load (.bin .add (.reg rLoc) (.reg rU))) (.const 0))
          (seqStmts [
            .store (.bin .add (.reg rOutDst) (.reg rOutCnt)) (.reg rU),
            .assign rOutCnt (.bin .add (.reg rOutCnt) (.const 1))
          ])
          (seqStmts [
            .store (.bin .add (.reg rInDst) (.reg rInCnt)) (.reg rU),
            .assign rInCnt (.bin .add (.reg rInCnt) (.const 1))
          ])
      ]
    )
  ]

theorem sbPartitionStmt_noRand (rSrc rLen rLoc rInDst rOutDst rInCnt rOutCnt rI rU : ℕ) :
    (sbPartitionStmt rSrc rLen rLoc rInDst rOutDst rInCnt rOutCnt rI rU).NoRand := by
  simp [sbPartitionStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Copy a router cut `[1, lenU, u_0, ...]` from `rSrc` to `rDst` in `CoreOutAt` format
`[0, lenU, u_0, ...]`. -/
def sbCopyCutZeroStmt (rSrc rDst rLen rI rU : ℕ) : Stmt :=
  seqStmts [
    .assign rLen (.load (.bin .add (.reg rSrc) (.const 1))),
    .store (.reg rDst) (.const 0),
    .store (.bin .add (.reg rDst) (.const 1)) (.reg rLen),
    forRange rI (.const 0) (.reg rLen) (
      seqStmts [
        .assign rU (.load (.bin .add (.bin .add (.reg rSrc) (.const 2)) (.reg rI))),
        .store (.bin .add (.bin .add (.reg rDst) (.const 2)) (.reg rI)) (.reg rU)
      ]
    )
  ]

theorem sbCopyCutZeroStmt_noRand (rSrc rDst rLen rI rU : ℕ) :
    (sbCopyCutZeroStmt rSrc rDst rLen rI rU).NoRand := by
  simp [sbCopyCutZeroStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Zip `min (rCntA, rCntB)` pairs from `(rUnmA, rUnmB)` into BOTH `rFAddr + 2 * rFakeM` and
`rWEdges + 2 * rWM`, incrementing both `rFakeM` and `rWM`. -/
def sbZipDualStmt (rUnmA rCntA rUnmB rCntB rFAddr rFakeM rWEdges rWM rLim rI rU rV : ℕ) : Stmt :=
  seqStmts [
    .cond (.bin .lt (.reg rCntA) (.reg rCntB))
      (.assign rLim (.reg rCntA))
      (.assign rLim (.reg rCntB)),
    forRange rI (.const 0) (.reg rLim) (
      seqStmts [
        .assign rU (.load (.bin .add (.reg rUnmA) (.reg rI))),
        .assign rV (.load (.bin .add (.reg rUnmB) (.reg rI))),
        .store (.bin .add (.reg rFAddr) (.bin .mul (.const 2) (.reg rFakeM))) (.reg rU),
        .store (.bin .add (.bin .add (.reg rFAddr) (.bin .mul (.const 2) (.reg rFakeM))) (.const 1)) (.reg rV),
        .assign rFakeM (.bin .add (.reg rFakeM) (.const 1)),
        .store (.bin .add (.reg rWEdges) (.bin .mul (.const 2) (.reg rWM))) (.reg rU),
        .store (.bin .add (.bin .add (.reg rWEdges) (.bin .mul (.const 2) (.reg rWM))) (.const 1)) (.reg rV),
        .assign rWM (.bin .add (.reg rWM) (.const 1))
      ]
    )
  ]

theorem sbZipDualStmt_noRand (rUnmA rCntA rUnmB rCntB rFAddr rFakeM rWEdges rWM rLim rI rU rV : ℕ) :
    (sbZipDualStmt rUnmA rCntA rUnmB rCntB rFAddr rFakeM rWEdges rWM rLim rI rU rV).NoRand := by
  simp [sbZipDualStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. Verified Triples -/

/-- Triple for `sbMarkListStmt`: sets `mem[la + u] := val` for every `u ∈ xs`, preserving all
memory outside `[la, la + n)` and all registers other than `rI, rU`. -/
lemma sbMarkList_triple {w n len sa la val rSrc rLen rLoc rVal rI rU : ℕ}
    (hd_regs : [rSrc, rLen, rLoc, rVal, rI, rU].Nodup)
    (p : Program) (mem : ℕ → ℕ) (xs : List ℕ) (st₀ : State)
    (hlen : xs.length = len) (hxs_at : ListAt mem sa xs)
    (hxs_lt : ∀ u ∈ xs, u < n)
    (hdisj : DisjointRange la n sa len)
    (hsa_w : sa + len < 2 ^ w) (hla_w : la + n < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrS : st₀.regs rSrc = sa) (hrL : st₀.regs rLen = len)
    (hrLoc : st₀.regs rLoc = la) (hrVal : st₀.regs rVal = val)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) (sbMarkListStmt rSrc rLen rLoc rVal rI rU)
      (normalPost fun st' =>
        (∀ r, r ≠ rI → r ≠ rU → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem la (la + n) ∧
        (∀ u < n, st'.mem (la + u) = if u ∈ xs.toFinset then val else mem (la + u)))
      (fun _ => 24 * len + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, _, hS_I, hS_U⟩, ⟨_, _, hL_I, hL_U⟩, ⟨_, hLoc_I, hLoc_U⟩,
    ⟨hV_I, hV_U⟩, hI_U, _⟩
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    (∀ r, r ≠ rI → r ≠ rU → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem la (la + n) ∧
    (∀ u < n, st.mem (la + u) = if u ∈ (xs.take j).toFinset then val else mem (la + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
      .store (.bin .add (.reg rLoc) (.reg rU)) (.reg rVal)])
    (P := fun st => st = st₀) (Inv := Inv) 15 0 len (Nat.zero_le len) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r h1 _ => by dsimp only; rw [Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun u _ => by simp [hmem]⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := len) (by rw [hInv.2.1 rLen hL_I hL_U, hrL]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hoth, hpos, hfr, hloc⟩
      have hj_len : j < xs.length := hlen.symm ▸ hjlt
      set u := xs[j]'hj_len
      have hu_lt : u < n := hxs_lt u (List.getElem_mem hj_len)
      have hrS' : st.regs rSrc = sa := (hoth rSrc hS_I hS_U).trans hrS
      have hrLoc' : st.regs rLoc = la := (hoth rLoc hLoc_I hLoc_U).trans hrLoc
      have hrVal' : st.regs rVal = val := (hoth rVal hV_I hV_U).trans hrVal
      have hsrc_u : st.mem (sa + j) = u := by
        have hout : sa + j < la ∨ la + n ≤ sa + j := by rcases hdisj with h | h <;> [right; left] <;> omega
        rw [hfr _ hout]; exact hxs_at j hj_len
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrS') (Expr.eval_reg_of_eq hj) (by omega)) hsrc_u) ?_
      refine runs_store_le (x := la + u) (v := val)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hLoc_U, hrLoc']))
          (Expr.eval_reg_of_eq (by simp)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hV_U, hrVal'])) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r h1 h2 => by
          dsimp only; rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hoth r h1 h2,
        hpos, fun a ha => by
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha, ?_⟩,
        by dsimp only; rw [Function.update_of_ne hI_U, hj]⟩
      intro v hv
      have htake : (xs.take (j + 1)).toFinset = insert u (xs.take j).toFinset := by
        have ht : xs.take (j + 1) = xs.take j ++ [u] := List.take_succ_eq_append_getElem hj_len
        rw [ht]
        ext x
        simp [or_comm]
      rw [htake]; dsimp only
      by_cases hvu : v = u
      · subst hvu; simp [Function.update_self]
      · rw [Function.update_of_ne (by omega), hloc v hv]
        simp [hvu])
  dsimp only [sbMarkListStmt]
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size, Nat.sub_zero]; omega)
  rintro (_ | _) st' hInv
  · rcases hInv with ⟨_, hoth, hpos, hfr, hloc⟩
    rw [← hlen, List.take_length] at hloc
    exact ⟨hoth, hpos, hfr, hloc⟩
  · exact hInv.elim

/-- Triple for `sbPartitionStmt`: partitions `xs` (`xs.length = len`) by `u ∈ S` (marked nonzero
in `locAddr`) into `inDst` (`xs.filter (· ∈ S)`) and `outDst` (`xs.filter (· ∉ S)`). -/
lemma sbPartition_triple {w n len sa la inA outA rSrc rLen rLoc rInDst rOutDst rInCnt rOutCnt rI rU : ℕ}
    (hd_regs : [rSrc, rLen, rLoc, rInDst, rOutDst, rInCnt, rOutCnt, rI, rU].Nodup)
    (p : Program) (mem : ℕ → ℕ) (xs : List ℕ) (S : Finset ℕ) (st₀ : State)
    (hlen : xs.length = len) (hxs_at : ListAt mem sa xs)
    (hxs_lt : ∀ u ∈ xs, u < n)
    (hloc : ∀ u < n, (mem (la + u) = 0 ↔ u ∉ S))
    (hd_in_sa : DisjointRange inA len sa len)
    (hd_in_la : DisjointRange inA len la n)
    (hd_out_sa : DisjointRange outA len sa len)
    (hd_out_la : DisjointRange outA len la n)
    (hd_in_out : DisjointRange inA len outA len)
    (hsa_w : sa + len < 2 ^ w) (hla_w : la + n < 2 ^ w)
    (hin_w : inA + len < 2 ^ w) (hout_w : outA + len < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrS : st₀.regs rSrc = sa) (hrL : st₀.regs rLen = len) (hrLoc : st₀.regs rLoc = la)
    (hrIn : st₀.regs rInDst = inA) (hrOut : st₀.regs rOutDst = outA)
    (hmem : st₀.mem = mem) :
    let inL := xs.filter (fun u => decide (u ∈ S))
    let outL := xs.filter (fun u => decide (u ∉ S))
    Triple w p (fun st => st = st₀)
      (sbPartitionStmt rSrc rLen rLoc rInDst rOutDst rInCnt rOutCnt rI rU)
      (normalPost fun st' =>
        st'.regs rInCnt = inL.length ∧
        st'.regs rOutCnt = outL.length ∧
        (∀ r, r ≠ rInCnt → r ≠ rOutCnt → r ≠ rI → r ≠ rU → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ a, (a < inA ∨ inA + len ≤ a) → (a < outA ∨ outA + len ≤ a) → st'.mem a = mem a) ∧
        ListAt st'.mem inA inL ∧
        ListAt st'.mem outA outL)
      (fun _ => 44 * len + 35) := by
  intro inL outL
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, _, _, hS_IC, hS_OC, hS_I, hS_U⟩,
    ⟨_, _, _, hL_IC, hL_OC, hL_I, hL_U⟩, ⟨_, _, hLoc_IC, hLoc_OC, hLoc_I, hLoc_U⟩,
    ⟨_, hIn_IC, hIn_OC, hIn_I, hIn_U⟩, ⟨hOut_IC, hOut_OC, hOut_I, hOut_U⟩,
    ⟨hIC_OC, hIC_I, hIC_U⟩, ⟨hOC_I, hOC_U⟩, hI_U, _⟩
  let st1 : State :=
    { mem := st₀.mem, regs := Function.update (Function.update st₀.regs rInCnt 0) rOutCnt 0, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    st.regs rInCnt = ((xs.take j).filter (fun u => decide (u ∈ S))).length ∧
    st.regs rOutCnt = ((xs.take j).filter (fun u => decide (u ∉ S))).length ∧
    (∀ r, r ≠ rInCnt → r ≠ rOutCnt → r ≠ rI → r ≠ rU → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    (∀ a, (a < inA ∨ inA + len ≤ a) → (a < outA ∨ outA + len ≤ a) → st.mem a = mem a) ∧
    ListAt st.mem inA ((xs.take j).filter (fun u => decide (u ∈ S))) ∧
    ListAt st.mem outA ((xs.take j).filter (fun u => decide (u ∉ S)))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
      .cond (.bin .eq (.load (.bin .add (.reg rLoc) (.reg rU))) (.const 0))
        (seqStmts [
          .store (.bin .add (.reg rOutDst) (.reg rOutCnt)) (.reg rU),
          .assign rOutCnt (.bin .add (.reg rOutCnt) (.const 1))])
        (seqStmts [
          .store (.bin .add (.reg rInDst) (.reg rInCnt)) (.reg rU),
          .assign rInCnt (.bin .add (.reg rInCnt) (.const 1))])])
    (P := fun st => st = st1) (Inv := Inv) 34 0 len (Nat.zero_le len) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne hIC_I, Function.update_of_ne hIC_OC, Function.update_self]; simp,
        by dsimp only [st1]; rw [Function.update_of_ne hOC_I, Function.update_self]; simp,
        fun r h1 h2 h3 _ => by
          dsimp only [st1]; rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1],
        rfl, fun a _ _ => congrFun hmem a, fun i hi => by simp at hi, fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := len) (by rw [hInv.2.2.2.1 rLen hL_IC hL_OC hL_I hL_U, hrL]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hic, hoc, hoth, hpos, hfr, hin_at, hout_at⟩
      have hj_len : j < xs.length := hlen.symm ▸ hjlt
      set u := xs[j]'hj_len
      have hu_lt : u < n := hxs_lt u (List.getElem_mem hj_len)
      have hic_le : ((xs.take j).filter (fun u => decide (u ∈ S))).length ≤ j :=
        (List.length_filter_le _ _).trans (List.length_take_le j xs)
      have hoc_le : ((xs.take j).filter (fun u => decide (u ∉ S))).length ≤ j :=
        (List.length_filter_le _ _).trans (List.length_take_le j xs)
      have hsrc_u : st.mem (sa + j) = u := by
        have h1 : sa + j < inA ∨ inA + len ≤ sa + j := by rcases hd_in_sa with h | h <;> [right; left] <;> omega
        have h2 : sa + j < outA ∨ outA + len ≤ sa + j := by rcases hd_out_sa with h | h <;> [right; left] <;> omega
        rw [hfr _ h1 h2]; exact hxs_at j hj_len
      have hloc_u : st.mem (la + u) = mem (la + u) := by
        have h1 : la + u < inA ∨ inA + len ≤ la + u := by rcases hd_in_la with h | h <;> [right; left] <;> omega
        have h2 : la + u < outA ∨ outA + len ≤ la + u := by rcases hd_out_la with h | h <;> [right; left] <;> omega
        exact hfr _ h1 h2
      have htake_s : xs.take (j + 1) = xs.take j ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj_len, Option.toList_some]
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth rSrc hS_IC hS_OC hS_I hS_U).trans hrS))
          (Expr.eval_reg_of_eq hj) (by omega)) hsrc_u) ?_
      refine runs_cond_le (v := if mem (la + u) = 0 then 1 else 0)
        (Expr.eval_eq_op
          (Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hLoc_U, hoth rLoc hLoc_IC hLoc_OC hLoc_I hLoc_U, hrLoc]))
            (Expr.eval_reg_of_eq (by simp)) (by omega)) hloc_u)
          (Expr.eval_const (by omega)) (by omega))
        (fun hzero => ?_) (fun hnz => ?_)
      · -- `mem (la + u) = 0`, so `u ∉ S` -> append to `outDst`
        have hm0 : mem (la + u) = 0 := by by_contra h; simp [h] at hzero
        have hu_notin : u ∉ S := (hloc u hu_lt).mp hm0
        set curO := ((xs.take j).filter (fun u => decide (u ∉ S))).length
        refine runs_seq_store_le (x := outA + curO) (v := u)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hOut_U, hoth rOutDst hOut_IC hOut_OC hOut_I hOut_U, hrOut]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hOC_U, hoc])) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_assign_le (v := curO + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hOC_U, hoc]))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        have hfin_in : (xs.take (j + 1)).filter (fun v => decide (v ∈ S)) =
            (xs.take j).filter (fun v => decide (v ∈ S)) := by
          rw [htake_s, List.filter_append]; simp [hu_notin]
        have hfin_out : (xs.take (j + 1)).filter (fun v => decide (v ∉ S)) =
            (xs.take j).filter (fun v => decide (v ∉ S)) ++ [u] := by
          rw [htake_s, List.filter_append]; simp [hu_notin]
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne hIC_I, Function.update_of_ne hIC_OC,
              Function.update_of_ne hIC_U, hic, hfin_in],
          by dsimp only; rw [Function.update_of_ne hOC_I, Function.update_self, hfin_out,
              List.length_append, List.length_singleton],
          fun r h1 h2 h3 h4 => by
            dsimp only; rw [Function.update_of_ne h3, Function.update_of_ne h2,
              Function.update_of_ne h4]; exact hoth r h1 h2 h3 h4,
          hpos, fun a ha_in ha_out => by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha_in ha_out,
          ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (Ne.symm hOC_I), Function.update_of_ne hI_U, hj]⟩
        · rw [hfin_in]; intro t ht
          have hne : inA + t ≠ outA + curO := by rcases hd_in_out with h | h <;> omega
          dsimp only; rw [Function.update_of_ne hne]; exact hin_at t ht
        · rw [hfin_out]; intro t ht
          rw [List.length_append, List.length_singleton] at ht
          dsimp only
          by_cases htq : t = curO
          · subst htq; rw [Function.update_self, List.getElem_append_right (le_refl _)]; simp
          · rw [Function.update_of_ne (by omega), List.getElem_append_left (by omega)]
            exact hout_at t (by omega)
      · -- `mem (la + u) ≠ 0`, so `u ∈ S` -> append to `inDst`
        have hmnz : mem (la + u) ≠ 0 := fun h => by simp [h] at hnz
        have hu_in : u ∈ S := by by_contra h; exact hmnz ((hloc u hu_lt).mpr h)
        set curI := ((xs.take j).filter (fun u => decide (u ∈ S))).length
        refine runs_seq_store_le (x := inA + curI) (v := u)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hIn_U, hoth rInDst hIn_IC hIn_OC hIn_I hIn_U, hrIn]))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hIC_U, hic])) (by omega))
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_assign_le (v := curI + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hIC_U, hic]))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        have hfin_in : (xs.take (j + 1)).filter (fun v => decide (v ∈ S)) =
            (xs.take j).filter (fun v => decide (v ∈ S)) ++ [u] := by
          rw [htake_s, List.filter_append]; simp [hu_in]
        have hfin_out : (xs.take (j + 1)).filter (fun v => decide (v ∉ S)) =
            (xs.take j).filter (fun v => decide (v ∉ S)) := by
          rw [htake_s, List.filter_append]; simp [hu_in]
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne hIC_I, Function.update_self, hfin_in,
              List.length_append, List.length_singleton],
          by dsimp only; rw [Function.update_of_ne hOC_I, Function.update_of_ne (Ne.symm hIC_OC),
              Function.update_of_ne hOC_U, hoc, hfin_out],
          fun r h1 h2 h3 h4 => by
            dsimp only; rw [Function.update_of_ne h3, Function.update_of_ne h1,
              Function.update_of_ne h4]; exact hoth r h1 h2 h3 h4,
          hpos, fun a ha_in ha_out => by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha_in ha_out,
          ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (Ne.symm hIC_I), Function.update_of_ne hI_U, hj]⟩
        · rw [hfin_in]; intro t ht
          rw [List.length_append, List.length_singleton] at ht
          dsimp only
          by_cases htq : t = curI
          · subst htq; rw [Function.update_self, List.getElem_append_right (le_refl _)]; simp
          · rw [Function.update_of_ne (by omega), List.getElem_append_left (by omega)]
            exact hin_at t (by omega)
        · rw [hfin_out]; intro t ht
          have hne : outA + t ≠ inA + curI := by rcases hd_in_out with h | h <;> omega
          dsimp only; rw [Function.update_of_ne hne]; exact hout_at t ht)
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [sbPartitionStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_triple_le hloop rfl ?_ (by simp only [Expr.size, Nat.sub_zero]; omega)
  rintro (_ | _) st' hInv
  · rcases hInv with ⟨_, hic', hoc', hoth', hpos', hfr', hin', hout'⟩
    rw [← hlen, List.take_length] at hic' hoc' hin' hout'
    exact ⟨hic', hoc', hoth', hpos', hfr', hin', hout'⟩
  · exact False.elim hInv

/-- Triple for `sbCopyCutZeroStmt`: writes `CoreOutAt` cut `[0, U_list.length, U_list...]` at
`dstA` from `[1, U_list.length, U_list...]` at `srcA`. -/
lemma sbCopyCutZero_triple {w cap srcA dstA rSrc rDst rLen rI rU : ℕ}
    (hd_regs : [rSrc, rDst, rLen, rI, rU].Nodup)
    (p : Program) (mem : ℕ → ℕ) (U_list : List ℕ) (st₀ : State)
    (hlen : mem (srcA + 1) = U_list.length)
    (hU_at : ListAt mem (srcA + 2) U_list)
    (hcap : 2 + U_list.length ≤ cap)
    (hdisj : DisjointRange dstA cap srcA (2 + U_list.length))
    (hsrc_w : srcA + 2 + U_list.length < 2 ^ w) (hdst_w : dstA + cap < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hrSrc : st₀.regs rSrc = srcA) (hrDst : st₀.regs rDst = dstA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) (sbCopyCutZeroStmt rSrc rDst rLen rI rU)
      (normalPost fun st' =>
        (∀ r, r ≠ rLen → r ≠ rI → r ≠ rU → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem dstA (dstA + cap) ∧
        st'.mem dstA = 0 ∧
        st'.mem (dstA + 1) = U_list.length ∧
        ListAt st'.mem (dstA + 2) U_list)
      (fun _ => 30 * U_list.length + 40) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, hS_L, hS_I, hS_U⟩, ⟨hD_L, hD_I, hD_U⟩, ⟨hL_I, hL_U⟩, hI_U, _⟩
  let mem1 := Function.update (Function.update mem dstA 0) (dstA + 1) U_list.length
  let st1 : State := { mem := mem1, regs := Function.update st₀.regs rLen U_list.length, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    (∀ r, r ≠ rLen → r ≠ rI → r ≠ rU → st.regs r = st₀.regs r) ∧
    st.regs rLen = U_list.length ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem dstA (dstA + cap) ∧
    st.mem dstA = 0 ∧
    st.mem (dstA + 1) = U_list.length ∧
    ListAt st.mem (dstA + 2) (U_list.take j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.bin .add (.reg rSrc) (.const 2)) (.reg rI))),
      .store (.bin .add (.bin .add (.reg rDst) (.const 2)) (.reg rI)) (.reg rU)])
    (P := fun st => st = st1) (Inv := Inv) 20 0 U_list.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r h1 h2 _ => by dsimp only [st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
        by dsimp only [st1]; rw [Function.update_of_ne hL_I, Function.update_self],
        rfl, fun a ha => by
          dsimp only [st1, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        by simp [st1, mem1], by simp [st1, mem1], fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hj, hoth, hrl, hpos, hfr, hm0, hm1, hlat⟩
      set u := U_list[j]'hjlt
      have hrS' : st.regs rSrc = srcA := (hoth rSrc hS_L hS_I hS_U).trans hrSrc
      have hrD' : st.regs rDst = dstA := (hoth rDst hD_L hD_I hD_U).trans hrDst
      have hsrc_u : st.mem (srcA + 2 + j) = u := by
        have hout : srcA + 2 + j < dstA ∨ dstA + cap ≤ srcA + 2 + j := by
          rcases hdisj with h | h <;> [right; left] <;> omega
        rw [hfr _ hout]; exact hU_at j hjlt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hrS') (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq hj) (by omega)) hsrc_u) ?_
      refine runs_store_le (x := dstA + 2 + j) (v := u)
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hD_U, hrD']))
          (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hI_U, hj])) (by omega))
        (Expr.eval_reg_of_eq (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r h1 h2 h3 => by
          dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h3]; exact hoth r h1 h2 h3,
        by dsimp only; rw [Function.update_of_ne hL_I, Function.update_of_ne hL_U, hrl],
        hpos, fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha,
        by dsimp only; rw [Function.update_of_ne (by omega), hm0],
        by dsimp only; rw [Function.update_of_ne (by omega), hm1], ?_⟩,
        by dsimp only; rw [Function.update_of_ne hI_U, hj]⟩
      intro t ht
      have hlen_t : (U_list.take (j + 1)).length = j + 1 := by simp [List.length_take]; omega
      rw [hlen_t] at ht
      have hget : (U_list.take (j + 1))[t]'(by omega) = U_list[t]'(by omega) := List.getElem_take
      rw [hget]; dsimp only
      by_cases htj : t = j
      · subst htj; rw [Function.update_self]
      · rw [Function.update_of_ne (by omega)]
        have ht' : t < (U_list.take j).length := by simp [List.length_take]; omega
        simpa [List.getElem_take] using hlat t ht')
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [sbCopyCutZeroStmt, seqStmts]
  refine runs_seq_assign_le (v := U_list.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrSrc) (Expr.eval_const (by omega)) (by omega))
      (hmem ▸ hlen)) ?_
  refine runs_seq_store_le (x := dstA) (v := 0)
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hD_L, hrDst])) (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := dstA + 1) (v := U_list.length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hD_L, hrDst]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_triple_le hloop (by simp [st1, mem1, hmem]) ?_ (by simp only [Expr.size, Nat.sub_zero]; omega)
  rintro (_ | _) st' hInv
  · rcases hInv with ⟨_, hoth, _, hpos, hfr, hm0, hm1, hlat⟩
    rw [List.take_length] at hlat
    exact ⟨hoth, hpos, hfr, hm0, hm1, hlat⟩
  · exact False.elim hInv

/-- Triple for `sbZipDualStmt`: zips `A_l.zip B_l` into BOTH `fA + 2 * prevF` and `wEA + 2 * prevW`,
advancing `rFakeM` and `rWM` by `min cntA cntB`. -/
lemma sbZipDual_triple {w cntA cntB prevF capF prevW capW fA wEA ua ub
    rUnmA rCntA rUnmB rCntB rFAddr rFakeM rWEdges rWM rLim rI rU rV : ℕ}
    (hd_regs : [rUnmA, rCntA, rUnmB, rCntB, rFAddr, rFakeM, rWEdges, rWM, rLim, rI, rU, rV].Nodup)
    (p : Program) (mem : ℕ → ℕ) (A_l B_l : List ℕ) (prevFEs prevWEs : List (ℕ × ℕ)) (st₀ : State)
    (hAlen : A_l.length = cntA) (hBlen : B_l.length = cntB)
    (hFlen : prevFEs.length = prevF) (hWlen : prevWEs.length = prevW)
    (hA_at : ListAt mem ua A_l) (hB_at : ListAt mem ub B_l)
    (hF_at : EdgesAt mem fA prevFEs) (hW_at : EdgesAt mem wEA prevWEs)
    (hcapF : prevF + min cntA cntB ≤ capF) (hcapW : prevW + min cntA cntB ≤ capW)
    (hd_F_A : DisjointRange fA (2 * capF) ua cntA) (hd_F_B : DisjointRange fA (2 * capF) ub cntB)
    (hd_W_A : DisjointRange wEA (2 * capW) ua cntA) (hd_W_B : DisjointRange wEA (2 * capW) ub cntB)
    (hd_F_W : DisjointRange fA (2 * capF) wEA (2 * capW))
    (hua_w : ua + cntA < 2 ^ w) (hub_w : ub + cntB < 2 ^ w)
    (hf_w : fA + 2 * capF < 2 ^ w) (hw_w : wEA + 2 * capW < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrUA : st₀.regs rUnmA = ua) (hrCA : st₀.regs rCntA = cntA)
    (hrUB : st₀.regs rUnmB = ub) (hrCB : st₀.regs rCntB = cntB)
    (hrFA : st₀.regs rFAddr = fA) (hrFM : st₀.regs rFakeM = prevF)
    (hrWE : st₀.regs rWEdges = wEA) (hrWM : st₀.regs rWM = prevW)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀)
      (sbZipDualStmt rUnmA rCntA rUnmB rCntB rFAddr rFakeM rWEdges rWM rLim rI rU rV)
      (normalPost fun st' =>
        st'.regs rFakeM = prevF + min cntA cntB ∧
        st'.regs rWM = prevW + min cntA cntB ∧
        (∀ r, r ≠ rFakeM → r ≠ rWM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ a, (a < fA ∨ fA + 2 * capF ≤ a) → (a < wEA ∨ wEA + 2 * capW ≤ a) → st'.mem a = mem a) ∧
        EdgesAt st'.mem fA (prevFEs ++ A_l.zip B_l) ∧
        EdgesAt st'.mem wEA (prevWEs ++ A_l.zip B_l))
      (fun _ => 96 * min cntA cntB + 45) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, _, _, hUA_FM, _, hUA_WM, hUA_Lim, hUA_I, hUA_U, hUA_V⟩,
    ⟨_, _, _, _, _, _, _, _, _, _⟩,
    ⟨_, _, hUB_FM, _, hUB_WM, hUB_Lim, hUB_I, hUB_U, hUB_V⟩,
    ⟨_, _, _, _, _, _, _, _⟩,
    ⟨hFA_FM, _, hFA_WM, hFA_Lim, hFA_I, hFA_U, hFA_V⟩,
    ⟨hFM_WE, hFM_WM, hFM_Lim, hFM_I, hFM_U, hFM_V⟩,
    ⟨hWE_WM, hWE_Lim, hWE_I, hWE_U, hWE_V⟩,
    ⟨hWM_Lim, hWM_I, hWM_U, hWM_V⟩, ⟨hLim_I, hLim_U, hLim_V⟩, ⟨hI_U, hI_V⟩, hU_V, _⟩
  set lim := min cntA cntB
  have hzip_len : (A_l.zip B_l).length = lim := by rw [List.length_zip, hAlen, hBlen]
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs rLim lim, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    st.regs rFakeM = prevF + j ∧
    st.regs rWM = prevW + j ∧
    st.regs rLim = lim ∧
    (∀ r, r ≠ rFakeM → r ≠ rWM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    (∀ a, (a < fA ∨ fA + 2 * capF ≤ a) → (a < wEA ∨ wEA + 2 * capW ≤ a) → st.mem a = mem a) ∧
    EdgesAt st.mem fA (prevFEs ++ (A_l.zip B_l).take j) ∧
    EdgesAt st.mem wEA (prevWEs ++ (A_l.zip B_l).take j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLim)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.reg rUnmA) (.reg rI))),
      .assign rV (.load (.bin .add (.reg rUnmB) (.reg rI))),
      .store (.bin .add (.reg rFAddr) (.bin .mul (.const 2) (.reg rFakeM))) (.reg rU),
      .store (.bin .add (.bin .add (.reg rFAddr) (.bin .mul (.const 2) (.reg rFakeM))) (.const 1)) (.reg rV),
      .assign rFakeM (.bin .add (.reg rFakeM) (.const 1)),
      .store (.bin .add (.reg rWEdges) (.bin .mul (.const 2) (.reg rWM))) (.reg rU),
      .store (.bin .add (.bin .add (.reg rWEdges) (.bin .mul (.const 2) (.reg rWM))) (.const 1)) (.reg rV),
      .assign rWM (.bin .add (.reg rWM) (.const 1))])
    (P := fun st => st = st1) (Inv := Inv) 84 0 lim (Nat.zero_le lim) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne hFM_I, Function.update_of_ne hFM_Lim, hrFM]; omega,
        by dsimp only [st1]; rw [Function.update_of_ne hWM_I, Function.update_of_ne hWM_Lim, hrWM]; omega,
        by dsimp only [st1]; rw [Function.update_of_ne hLim_I, Function.update_self],
        fun r _ _ h3 h4 _ _ => by dsimp only [st1]; rw [Function.update_of_ne h4, Function.update_of_ne h3],
        rfl, fun a _ _ => congrFun hmem a,
        by dsimp only [st1]; rw [hmem]; simpa using hF_at,
        by dsimp only [st1]; rw [hmem]; simpa using hW_at⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hj, hfm, hwm, hlim, hoth, hpos, hfr, hEF, hEW⟩
      have hjA : j < A_l.length := by omega
      have hjB : j < B_l.length := by omega
      set u := A_l[j]'hjA
      set v := B_l[j]'hjB
      have hsrcA : st.mem (ua + j) = u := by
        have h1 : ua + j < fA ∨ fA + 2 * capF ≤ ua + j := by rcases hd_F_A with h | h <;> [right; left] <;> omega
        have h2 : ua + j < wEA ∨ wEA + 2 * capW ≤ ua + j := by rcases hd_W_A with h | h <;> [right; left] <;> omega
        rw [hfr _ h1 h2]; exact hA_at j hjA
      have hsrcB : st.mem (ub + j) = v := by
        have h1 : ub + j < fA ∨ fA + 2 * capF ≤ ub + j := by rcases hd_F_B with h | h <;> [right; left] <;> omega
        have h2 : ub + j < wEA ∨ wEA + 2 * capW ≤ ub + j := by rcases hd_W_B with h | h <;> [right; left] <;> omega
        rw [hfr _ h1 h2]; exact hB_at j hjB
      have hrFA' : st.regs rFAddr = fA := (hoth rFAddr hFA_FM hFA_WM hFA_Lim hFA_I hFA_U hFA_V).trans hrFA
      have hrWE' : st.regs rWEdges = wEA := (hoth rWEdges (Ne.symm hFM_WE) hWE_WM hWE_Lim hWE_I hWE_U hWE_V).trans hrWE
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq ((hoth rUnmA hUA_FM hUA_WM hUA_Lim hUA_I hUA_U hUA_V).trans hrUA))
          (Expr.eval_reg_of_eq hj) (by omega)) hsrcA) ?_
      refine runs_seq_assign_le (v := v)
        (Expr.eval_load_of_eq (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hUB_U, hoth rUnmB hUB_FM hUB_WM hUB_Lim hUB_I hUB_U hUB_V, hrUB]))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hI_U, hj])) (by omega)) hsrcB) ?_
      refine runs_seq_store_le (x := fA + 2 * (prevF + j)) (v := u)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hFA_V, Function.update_of_ne hFA_U, hrFA']))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hFM_V, Function.update_of_ne hFM_U, hfm]))
            (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hU_V, Function.update_self])) ?_
      refine runs_seq_store_le (x := fA + 2 * (prevF + j) + 1) (v := v)
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hFA_V, Function.update_of_ne hFA_U, hrFA']))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hFM_V, Function.update_of_ne hFM_U, hfm]))
            (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by simp)) ?_
      refine runs_seq_assign_le (v := prevF + j + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hFM_V, Function.update_of_ne hFM_U, hfm]))
          (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_store_le (x := wEA + 2 * (prevW + j)) (v := u)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_WE), Function.update_of_ne hWE_V, Function.update_of_ne hWE_U, hrWE']))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_WM), Function.update_of_ne hWM_V, Function.update_of_ne hWM_U, hwm]))
            (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_U), Function.update_of_ne hU_V, Function.update_self])) ?_
      refine runs_seq_store_le (x := wEA + 2 * (prevW + j) + 1) (v := v)
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_WE), Function.update_of_ne hWE_V, Function.update_of_ne hWE_U, hrWE']))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_WM), Function.update_of_ne hWM_V, Function.update_of_ne hWM_U, hwm]))
            (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_V), Function.update_self])) ?_
      refine runs_assign_le (v := prevW + j + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (Ne.symm hFM_WM), Function.update_of_ne hWM_V, Function.update_of_ne hWM_U, hwm]))
          (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
      have htake_zip : (A_l.zip B_l).take (j + 1) = (A_l.zip B_l).take j ++ [(u, v)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]; simp [u, v]
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne hFM_I, Function.update_of_ne hFM_WM, Function.update_self]; omega,
        by dsimp only; rw [Function.update_of_ne hWM_I, Function.update_self]; omega,
        by dsimp only; rw [Function.update_of_ne hLim_I, Function.update_of_ne (Ne.symm hWM_Lim),
            Function.update_of_ne (Ne.symm hFM_Lim), Function.update_of_ne hLim_V, Function.update_of_ne hLim_U, hlim],
        fun r h1 h2 h3 h4 h5 h6 => by
          dsimp only; rw [Function.update_of_ne h4, Function.update_of_ne h2, Function.update_of_ne h1,
            Function.update_of_ne h6, Function.update_of_ne h5]; exact hoth r h1 h2 h3 h4 h5 h6,
        hpos, fun a haF haW => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a haF haW, ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (Ne.symm hWM_I), Function.update_of_ne (Ne.symm hFM_I),
            Function.update_of_ne hI_V, Function.update_of_ne hI_U, hj]⟩
      · rw [htake_zip, ← List.append_assoc]; intro t ht
        have hlt_len : (prevFEs ++ (A_l.zip B_l).take j).length = prevF + j := by
          rw [List.length_append, hFlen, List.length_take]; omega
        rw [List.length_append, hlt_len, List.length_singleton] at ht
        have hneW1 : fA + 2 * t ≠ wEA + 2 * (prevW + j) + 1 := by rcases hd_F_W with h | h <;> omega
        have hneW2 : fA + 2 * t ≠ wEA + 2 * (prevW + j) := by rcases hd_F_W with h | h <;> omega
        have hneW3 : fA + 2 * t + 1 ≠ wEA + 2 * (prevW + j) + 1 := by rcases hd_F_W with h | h <;> omega
        have hneW4 : fA + 2 * t + 1 ≠ wEA + 2 * (prevW + j) := by rcases hd_F_W with h | h <;> omega
        dsimp only
        rw [Function.update_of_ne hneW1, Function.update_of_ne hneW2,
          Function.update_of_ne hneW3, Function.update_of_ne hneW4]
        by_cases htq : t = prevF + j
        · subst htq
          rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self,
            List.getElem_append_right (by omega)]
          simp [hlt_len]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            List.getElem_append_left (by omega)]
          exact hEF t (by omega)
      · rw [htake_zip, ← List.append_assoc]; intro t ht
        have hlt_len : (prevWEs ++ (A_l.zip B_l).take j).length = prevW + j := by
          rw [List.length_append, hWlen, List.length_take]; omega
        rw [List.length_append, hlt_len, List.length_singleton] at ht
        dsimp only
        by_cases htq : t = prevW + j
        · subst htq
          rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self,
            List.getElem_append_right (by omega)]
          simp [hlt_len]
        · have hneF1 : wEA + 2 * t ≠ fA + 2 * (prevF + j) + 1 := by rcases hd_F_W with h | h <;> omega
          have hneF2 : wEA + 2 * t ≠ fA + 2 * (prevF + j) := by rcases hd_F_W with h | h <;> omega
          have hneF3 : wEA + 2 * t + 1 ≠ fA + 2 * (prevF + j) + 1 := by rcases hd_F_W with h | h <;> omega
          have hneF4 : wEA + 2 * t + 1 ≠ fA + 2 * (prevF + j) := by rcases hd_F_W with h | h <;> omega
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hneF1, Function.update_of_ne hneF2,
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hneF3, Function.update_of_ne hneF4,
            List.getElem_append_left (by omega)]
          exact hEW t (by omega))
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [sbZipDualStmt, seqStmts]
  by_cases hAB : cntA < cntB
  · have hlim_eq : cntA = lim := by omega
    refine runs_seq_cond_le (v := 1)
      (Expr.eval_lt_true (Expr.eval_reg_of_eq hrCA) (Expr.eval_reg_of_eq hrCB) hAB (by omega))
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine runs_seq_assign_le (v := lim) (hlim_eq ▸ Expr.eval_reg_of_eq hrCA) ?_
    refine runs_triple_le hloop rfl ?_ (by simp only [Expr.size, Nat.sub_zero]; omega)
    rintro (_ | _) st'' hInv
    · rcases hInv with ⟨_, hfm', hwm', _, hoth', hpos', hfr', hEF', hEW'⟩
      rw [← hzip_len, List.take_length] at hEF' hEW'
      exact ⟨hfm', hwm', hoth', hpos', hfr', hEF', hEW'⟩
    · exact False.elim hInv
  · have hlim_eq : cntB = lim := by omega
    refine runs_seq_cond_le (v := 0)
      (Expr.eval_lt_false (Expr.eval_reg_of_eq hrCA) (Expr.eval_reg_of_eq hrCB) (by omega) (by omega))
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_assign_le (v := lim) (hlim_eq ▸ Expr.eval_reg_of_eq hrCB) ?_
    refine runs_triple_le hloop rfl ?_ (by simp only [Expr.size, Nat.sub_zero]; omega)
    rintro (_ | _) st'' hInv
    · rcases hInv with ⟨_, hfm', hwm', _, hoth', hpos', hfr', hEF', hEW'⟩
      rw [← hzip_len, List.take_length] at hEF' hEW'
      exact ⟨hfm', hwm', hoth', hpos', hfr', hEF', hEW'⟩
    · exact False.elim hInv

end MinCostFlow.ExpanderDecomp
