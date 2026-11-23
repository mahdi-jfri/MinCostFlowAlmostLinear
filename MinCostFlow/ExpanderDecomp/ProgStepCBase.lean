module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCMath

import Mathlib.Tactic.Linarith

/-!
# Step C and Step B Reusable Word-RAM Loop Primitives (`ProgStepCBase`)

Implements and verifies four deterministic (`NoRand`), strictly local Word-RAM loop primitives
shared by Step C (`ProgStepC*.lean`) and Step B (`ProgStepB*.lean`), with zero scans of `range n`:

- `scSetMatchedStmt` / `scSetMatched_triple`: marks or unmarks all endpoints of an edge list in `locAddr`.
- `scCollectUnmatchedStmt` / `scCollectUnmatched_triple`: filters a vertex slice by `locAddr[u] = 0`.
- `scZipAppendStmt` / `scZipAppend_triple`: zips two unmatched vertex lists and appends the pairs.
- `scCopyCutStmt` / `scCopyCut_triple`: copies a router cut `[1, lenU, u_0, ...]` to `outAddr`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Reusable Word-RAM Loop Primitives (`NoRand`) -/

/-- Mark `mem[rLoc + u] := val` and `mem[rLoc + v] := val` for `rM` flat edges at `rEdges`. -/
def scSetMatchedStmt (rM rEdges rLoc rI rU rV val : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rM) (
    seqStmts [
      .assign rU (.load (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI)))),
      .assign rV (.load (.bin .add (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI))) (.const 1))),
      .store (.bin .add (.reg rLoc) (.reg rU)) (.const val),
      .store (.bin .add (.reg rLoc) (.reg rV)) (.const val)
    ]
  )

theorem scSetMatchedStmt_noRand (rM rEdges rLoc rI rU rV val : ℕ) :
    (scSetMatchedStmt rM rEdges rLoc rI rU rV val).NoRand := by
  simp [scSetMatchedStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Scan `rLen` vertices at `rSrc` and write those with `mem[rLoc + u] = 0` into `rDst`,
leaving the count written in `rCnt`. -/
def scCollectUnmatchedStmt (rSrc rLen rLoc rDst rCnt rI rU : ℕ) : Stmt :=
  seqStmts [
    .assign rCnt (.const 0),
    forRange rI (.const 0) (.reg rLen) (
      seqStmts [
        .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
        .cond (.bin .eq (.load (.bin .add (.reg rLoc) (.reg rU))) (.const 0))
          (seqStmts [
            .store (.bin .add (.reg rDst) (.reg rCnt)) (.reg rU),
            .assign rCnt (.bin .add (.reg rCnt) (.const 1))
          ])
          .nop
      ]
    )
  ]

theorem scCollectUnmatchedStmt_noRand (rSrc rLen rLoc rDst rCnt rI rU : ℕ) :
    (scCollectUnmatchedStmt rSrc rLen rLoc rDst rCnt rI rU).NoRand := by
  simp [scCollectUnmatchedStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Zip `min (rCntA, rCntB)` pairs from `rUnmA, rUnmB` into `rOutEdges + 2 * rOutM`,
incrementing `rOutM` by `min (rCntA, rCntB)`. -/
def scZipAppendStmt (rUnmA rCntA rUnmB rCntB rOutEdges rOutM rLim rI rU rV : ℕ) : Stmt :=
  seqStmts [
    .cond (.bin .lt (.reg rCntA) (.reg rCntB))
      (.assign rLim (.reg rCntA))
      (.assign rLim (.reg rCntB)),
    forRange rI (.const 0) (.reg rLim) (
      seqStmts [
        .assign rU (.load (.bin .add (.reg rUnmA) (.reg rI))),
        .assign rV (.load (.bin .add (.reg rUnmB) (.reg rI))),
        .store (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.reg rU),
        .store (.bin .add (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.const 1)) (.reg rV),
        .assign rOutM (.bin .add (.reg rOutM) (.const 1))
      ]
    )
  ]

theorem scZipAppendStmt_noRand (rUnmA rCntA rUnmB rCntB rOutEdges rOutM rLim rI rU rV : ℕ) :
    (scZipAppendStmt rUnmA rCntA rUnmB rCntB rOutEdges rOutM rLim rI rU rV).NoRand := by
  simp [scZipAppendStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Copy a cut `[1, lenU, u_0, ...]` from `rSrc` to `rDst`. -/
def scCopyCutStmt (rSrc rDst rLen rI rU : ℕ) : Stmt :=
  seqStmts [
    .assign rLen (.load (.bin .add (.reg rSrc) (.const 1))),
    .store (.reg rDst) (.const 1),
    .store (.bin .add (.reg rDst) (.const 1)) (.reg rLen),
    forRange rI (.const 0) (.reg rLen) (
      seqStmts [
        .assign rU (.load (.bin .add (.bin .add (.reg rSrc) (.const 2)) (.reg rI))),
        .store (.bin .add (.bin .add (.reg rDst) (.const 2)) (.reg rI)) (.reg rU)
      ]
    )
  ]

theorem scCopyCutStmt_noRand (rSrc rDst rLen rI rU : ℕ) :
    (scCopyCutStmt rSrc rDst rLen rI rU).NoRand := by
  simp [scCopyCutStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 3. Triples for the Reusable Loop Primitives -/

/-- Triple for `scSetMatchedStmt`: sets `loc[u] := val` and `loc[v] := val` for all endpoints of
`es` (`es.length = mE`, all endpoints `< n`), preserving all memory outside `[la, la + n)`. -/
lemma scSetMatched_triple {w n mE ea la rM rEdges rLoc rI rU rV val : ℕ}
    (hd_regs : [rM, rEdges, rLoc, rI, rU, rV].Nodup)
    (p : Program) (mem : ℕ → ℕ) (es : List (ℕ × ℕ)) (st₀ : State)
    (hlen : es.length = mE)
    (hE_at : EdgesAt mem ea es)
    (hE_lt : ∀ e ∈ es, e.1 < n ∧ e.2 < n)
    (hdisj : DisjointRange la n ea (2 * mE))
    (hea_w : ea + 2 * mE < 2 ^ w) (hla_w : la + n < 2 ^ w)
    (hval_w : val < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrM : st₀.regs rM = mE) (hrE : st₀.regs rEdges = ea) (hrL : st₀.regs rLoc = la)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) (scSetMatchedStmt rM rEdges rLoc rI rU rV val)
      (normalPost fun st' =>
        (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem la (la + n) ∧
        (∀ u < n, st'.mem (la + u) = if u ∈ matchedVerts es then val else mem (la + u)))
      (fun _ => 54 * mE + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, hM_I, hM_U, hM_V⟩, ⟨_, hE_I, hE_U, hE_V⟩,
    ⟨hL_I, hL_U, hL_V⟩, ⟨hI_U, hI_V⟩, hU_V, _⟩
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem la (la + n) ∧
    (∀ u < n, st.mem (la + u) = if u ∈ matchedVerts (es.take j) then val else mem (la + u))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rM)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI)))),
      .assign rV (.load (.bin .add (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI))) (.const 1))),
      .store (.bin .add (.reg rLoc) (.reg rU)) (.const val),
      .store (.bin .add (.reg rLoc) (.reg rV)) (.const val)])
    (P := fun st => st = st₀) (Inv := Inv) 42 0 mE (Nat.zero_le mE) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r h1 _ _ => by dsimp only; rw [Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun u _ => by simp [hmem, matchedVerts]⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := mE) (by rw [hInv.2.1 rM hM_I hM_U hM_V, hrM]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hoth, hpos, hfr, hloc⟩
      have hj_len : j < es.length := hlen.symm ▸ hjlt
      set ed := es[j]'hj_len
      have hed_lt := hE_lt ed (List.getElem_mem hj_len)
      have hrE' : st.regs rEdges = ea := (hoth rEdges hE_I hE_U hE_V).trans hrE
      have hrL' : st.regs rLoc = la := (hoth rLoc hL_I hL_U hL_V).trans hrL
      have hmem1 : st.mem (ea + 2 * j) = ed.1 := by
        rw [hfr (ea + 2 * j) (disjointRange_outside hdisj (by omega) (by omega))]
        exact (hE_at j hj_len).1
      have hmem2 : st.mem (ea + 2 * j + 1) = ed.2 := by
        rw [hfr (ea + 2 * j + 1) (disjointRange_outside hdisj (by omega) (by omega))]
        exact (hE_at j hj_len).2
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hrE')
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega))
            (by omega)) hmem1) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ea) (by dsimp only; rw [Function.update_of_ne hE_U, hrE']))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne hI_U, hj]))
                (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem2) ?_
      refine runs_seq_store_le (x := la + ed.1) (v := val)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := la)
            (by dsimp only; rw [Function.update_of_ne hL_V, Function.update_of_ne hL_U, hrL']))
          (Expr.eval_reg_of_eq (v := ed.1)
            (by dsimp only; rw [Function.update_of_ne hU_V, Function.update_self])) (by omega))
        (Expr.eval_const hval_w) ?_
      refine runs_store_le (x := la + ed.2) (v := val)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := la)
            (by dsimp only; rw [Function.update_of_ne hL_V, Function.update_of_ne hL_U, hrL']))
          (Expr.eval_reg_of_eq (v := ed.2) (by simp)) (by omega))
        (Expr.eval_const hval_w) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp,
        fun r h1 h2 h3 => by
          dsimp only
          rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2]
          exact hoth r h1 h2 h3,
        hpos,
        memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_update (by omega) (by omega))), ?_⟩,
        by dsimp only; rw [Function.update_of_ne hI_V, Function.update_of_ne hI_U, hj]⟩
      intro u hu
      dsimp only
      have htake : matchedVerts (es.take (j + 1)) = insert ed.1 (insert ed.2 (matchedVerts (es.take j))) := by
        ext x
        rw [List.take_succ_eq_append_getElem hj_len]
        simp only [matchedVerts, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
        tauto
      rw [htake]
      by_cases hu2 : u = ed.2
      · subst hu2; simp [Function.update_self]
      · rw [Function.update_of_ne (by omega)]
        by_cases hu1 : u = ed.1
        · subst hu1; simp [Function.update_self]
        · rw [Function.update_of_ne (by omega), hloc u hu]
          simp [hu1, hu2])
  dsimp only [scSetMatchedStmt]
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro (_ | v) st' hInv
  · rcases hInv with ⟨_, hoth, hpos, hfr, hloc⟩
    refine ⟨hoth, hpos, hfr, fun u hu => ?_⟩
    simpa [← hlen, List.take_length] using hloc u hu
  · exact hInv.elim

/-- Triple for `scCollectUnmatchedStmt`: filters `l` at `sa` by `mem[la + u] = 0` (`u ∉ S`),
writing `l.filter (fun u => decide (u ∉ S))` at `da` and leaving its length in `rCnt`. -/
lemma scCollectUnmatched_triple {w n len sa la da rSrc rLen rLoc rDst rCnt rI rU : ℕ}
    (hd_regs : [rSrc, rLen, rLoc, rDst, rCnt, rI, rU].Nodup)
    (p : Program) (mem : ℕ → ℕ) (l : List ℕ) (S : Finset ℕ) (st₀ : State)
    (hlen : l.length = len)
    (hl_at : ListAt mem sa l)
    (hl_lt : ∀ u ∈ l, u < n)
    (hloc : ∀ u < n, mem (la + u) = if u ∈ S then 1 else 0)
    (hdisj_s : DisjointRange da len sa len)
    (hdisj_l : DisjointRange da len la n)
    (hsa_w : sa + len < 2 ^ w) (hla_w : la + n < 2 ^ w) (hda_w : da + len < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hrSrc : st₀.regs rSrc = sa) (hrLen : st₀.regs rLen = len)
    (hrLoc : st₀.regs rLoc = la) (hrDst : st₀.regs rDst = da)
    (hmem : st₀.mem = mem) :
    let out := l.filter fun u => decide (u ∉ S)
    Triple w p (fun st => st = st₀) (scCollectUnmatchedStmt rSrc rLen rLoc rDst rCnt rI rU)
      (normalPost fun st' =>
        st'.regs rCnt = out.length ∧
        (∀ r, r ≠ rCnt → r ≠ rI → r ≠ rU → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem da (da + len) ∧
        ListAt st'.mem da out)
      (fun _ => 38 * len + 30) := by
  intro out
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, _, hS_C, hS_I, hS_U⟩, ⟨_, _, hL_C, hL_I, hL_U⟩,
    ⟨_, hO_C, hO_I, hO_U⟩, ⟨hD_C, hD_I, hD_U⟩, ⟨hC_I, hC_U⟩, hI_U, _⟩
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [scCollectUnmatchedStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs rCnt 0, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    st.regs rCnt = ((l.take j).filter fun u => decide (u ∉ S)).length ∧
    (∀ r, r ≠ rCnt → r ≠ rI → r ≠ rU → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem da (da + len) ∧
    ListAt st.mem da ((l.take j).filter fun u => decide (u ∉ S))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.reg rSrc) (.reg rI))),
      .cond (.bin .eq (.load (.bin .add (.reg rLoc) (.reg rU))) (.const 0))
        (seqStmts [
          .store (.bin .add (.reg rDst) (.reg rCnt)) (.reg rU),
          .assign rCnt (.bin .add (.reg rCnt) (.const 1))
        ])
        .nop])
    (P := fun st => st = st1) (Inv := Inv) 26 0 len (Nat.zero_le len) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne hC_I, Function.update_self]; simp,
        fun r h1 h2 _ => by dsimp only [st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := len) (by rw [hInv.2.2.1 rLen hL_C hL_I hL_U, hrLen]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hcnt, hoth, hpos, hfr, hlist⟩
      have hj_len : j < l.length := hlen.symm ▸ hjlt
      set u := l[j]'hj_len
      have hu_lt : u < n := hl_lt u (List.getElem_mem hj_len)
      have hrS' : st.regs rSrc = sa := (hoth rSrc hS_C hS_I hS_U).trans hrSrc
      have hrO' : st.regs rLoc = la := (hoth rLoc hO_C hO_I hO_U).trans hrLoc
      have hrD' : st.regs rDst = da := (hoth rDst hD_C hD_I hD_U).trans hrDst
      have hcnt_le : ((l.take j).filter fun x => decide (x ∉ S)).length ≤ j :=
        le_trans (List.length_filter_le _ _) (by simp [List.length_take])
      have hmem_u : st.mem (sa + j) = u := by
        rw [hfr (sa + j) (disjointRange_outside hdisj_s (by omega) (by omega))]
        exact hl_at j hj_len
      have hmem_loc : st.mem (la + u) = if u ∈ S then 1 else 0 := by
        rw [hfr (la + u) (disjointRange_outside hdisj_l (by omega) (by omega))]
        exact hloc u hu_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hrS') (Expr.eval_reg_of_eq hj) (by omega)) hmem_u) ?_
      refine runs_cond_le (v := if (if u ∈ S then 1 else 0) = 0 then 1 else 0)
        (Expr.eval_eq_op
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := la) (by dsimp only; rw [Function.update_of_ne hO_U, hrO']))
              (Expr.eval_reg_of_eq (v := u) (by simp)) (by omega))
            hmem_loc)
          (Expr.eval_const (by omega)) (by omega))
        (fun hne => ?_) (fun h0 => ?_)
      · have hu_not : u ∉ S := by by_contra hmem; simp [hmem] at hne
        have htake_f : (l.take (j + 1)).filter (fun x => decide (x ∉ S)) =
            (l.take j).filter (fun x => decide (x ∉ S)) ++ [u] := by
          rw [List.take_succ_eq_append_getElem hj_len, List.filter_append, List.filter_cons]
          simp [u, hu_not]
        set cur := ((l.take j).filter fun x => decide (x ∉ S)).length
        refine runs_seq_store_le (x := da + cur) (v := u)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := da) (by dsimp only; rw [Function.update_of_ne hD_U, hrD']))
            (Expr.eval_reg_of_eq (v := cur) (by dsimp only; rw [Function.update_of_ne hC_U, hcnt]))
            (by omega))
          (Expr.eval_reg_of_eq (v := u) (by simp)) ?_
        refine runs_assign_le (v := cur + 1)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := cur) (by dsimp only; rw [Function.update_of_ne hC_U, hcnt]))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne hC_I, Function.update_self, htake_f,
            List.length_append, List.length_singleton],
          fun r h1 h2 h3 => by
            dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h3]
            exact hoth r h1 h2 h3,
          hpos,
          memFrame_trans hfr (memFrame_update (by omega) (by omega)), ?_⟩,
          by dsimp only; rw [Function.update_of_ne (Ne.symm hC_I), Function.update_of_ne hI_U, hj]⟩
        intro t ht
        dsimp only
        have ht' : t < cur + 1 := by
          rw [htake_f, List.length_append, List.length_singleton] at ht; exact ht
        by_cases hteq : t = cur
        · subst hteq
          have hget : ((l.take (j + 1)).filter fun x => decide (x ∉ S))[cur]'ht = u := by
            simp only [htake_f]; rw [List.getElem_append_right (by omega)]; simp [cur]
          rw [hget, Function.update_self]
        · have htlt : t < cur := by omega
          have hget : ((l.take (j + 1)).filter fun x => decide (x ∉ S))[t]'ht =
              ((l.take j).filter fun x => decide (x ∉ S))[t]'htlt := by
            simp only [htake_f]; exact List.getElem_append_left htlt
          rw [hget, Function.update_of_ne (by omega)]
          exact hlist t htlt
      · have hu_in : u ∈ S := by by_contra hmem; simp [hmem] at h0
        have htake_f : (l.take (j + 1)).filter (fun x => decide (x ∉ S)) =
            (l.take j).filter (fun x => decide (x ∉ S)) := by
          rw [List.take_succ_eq_append_getElem hj_len, List.filter_append, List.filter_cons]
          simp [u, hu_in]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne hC_I, Function.update_of_ne hC_U, hcnt, htake_f],
          fun r h1 h2 h3 => by
            dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h3]
            exact hoth r h1 h2 h3,
          hpos, hfr, htake_f.symm ▸ hlist⟩,
          by dsimp only; rw [Function.update_of_ne hI_U, hj]⟩)
  obtain ⟨o, st', c, hr, hq, hc⟩ := hloop st1 ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨_, hcnt', hoth', hpos', hfr', hlist'⟩
    have hfull : (l.take len).filter (fun u => decide (u ∉ S)) = out := by
      rw [← hlen, List.take_length]
    rw [hfull] at hcnt' hlist'
    exact ⟨.normal, st', c, hr, ⟨hcnt', hoth', hpos', hfr', hlist'⟩, by simp [Expr.size] at hc ⊢; omega⟩

/-- Triple for `scZipAppendStmt`: appends `A_l.zip B_l` after `prevEdges` at `outEdgesAddr`. -/
lemma scZipAppend_triple {w cntA cntB prevM cap outA ua ub rUnmA rCntA rUnmB rCntB rOutEdges
    rOutM rLim rI rU rV : ℕ}
    (hd_regs : [rUnmA, rCntA, rUnmB, rCntB, rOutEdges, rOutM, rLim, rI, rU, rV].Nodup)
    (p : Program) (mem : ℕ → ℕ) (A_l B_l : List ℕ) (prevEdges : List (ℕ × ℕ)) (st₀ : State)
    (hAlen : A_l.length = cntA) (hBlen : B_l.length = cntB) (hplen : prevEdges.length = prevM)
    (hA_at : ListAt mem ua A_l) (hB_at : ListAt mem ub B_l) (hP_at : EdgesAt mem outA prevEdges)
    (hcap : prevM + min cntA cntB ≤ cap)
    (hdisjA : DisjointRange outA (2 * cap) ua cntA)
    (hdisjB : DisjointRange outA (2 * cap) ub cntB)
    (hua_w : ua + cntA < 2 ^ w) (hub_w : ub + cntB < 2 ^ w)
    (hout_w : outA + 2 * cap < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrUA : st₀.regs rUnmA = ua) (hrCA : st₀.regs rCntA = cntA)
    (hrUB : st₀.regs rUnmB = ub) (hrCB : st₀.regs rCntB = cntB)
    (hrOE : st₀.regs rOutEdges = outA) (hrOM : st₀.regs rOutM = prevM)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀)
      (scZipAppendStmt rUnmA rCntA rUnmB rCntB rOutEdges rOutM rLim rI rU rV)
      (normalPost fun st' =>
        st'.regs rOutM = prevM + min cntA cntB ∧
        (∀ r, r ≠ rOutM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem outA (outA + 2 * cap) ∧
        EdgesAt st'.mem outA (prevEdges ++ A_l.zip B_l))
      (fun _ => 56 * min cntA cntB + 35) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, _, _, _, hUA_L, hUA_I, hUA_U, hUA_V⟩,
    ⟨_, _, _, _, hCA_L, hCA_I, hCA_U, hCA_V⟩,
    ⟨_, _, _, hUB_L, hUB_I, hUB_U, hUB_V⟩,
    ⟨_, _, hCB_L, hCB_I, hCB_U, hCB_V⟩,
    ⟨_, hOE_L, hOE_I, hOE_U, hOE_V⟩,
    ⟨hOM_L, hOM_I, hOM_U, hOM_V⟩,
    ⟨hL_I, hL_U, hL_V⟩, ⟨hI_U, hI_V⟩, hU_V, _⟩
  set lim := min cntA cntB with hlim_def
  have hlim_le_A : lim ≤ cntA := Nat.min_le_left _ _
  have hlim_le_B : lim ≤ cntB := Nat.min_le_right _ _
  have hzip_len : (A_l.zip B_l).length = lim := by rw [List.length_zip, hAlen, hBlen]
  -- Helper for the inner loop once `rLim = lim`
  have hinner : ∀ (st1 : State),
      st1.regs rLim = lim →
      st1.regs rOutM = prevM →
      (∀ r, r ≠ rOutM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st1.regs r = st₀.regs r) →
      st1.mem = mem → st1.pos = st₀.pos →
      Triple w p (fun st => st = st1)
        (forRange rI (.const 0) (.reg rLim) (
          seqStmts [
            .assign rU (.load (.bin .add (.reg rUnmA) (.reg rI))),
            .assign rV (.load (.bin .add (.reg rUnmB) (.reg rI))),
            .store (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.reg rU),
            .store (.bin .add (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.const 1)) (.reg rV),
            .assign rOutM (.bin .add (.reg rOutM) (.const 1))
          ]))
        (normalPost fun st' =>
          st'.regs rOutM = prevM + lim ∧
          (∀ r, r ≠ rOutM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
          MemFrame mem st'.mem outA (outA + 2 * cap) ∧
          EdgesAt st'.mem outA (prevEdges ++ A_l.zip B_l))
        (fun _ => 56 * lim + 20) := by
    intro st1 hrLim1 hrOM1 hoth1 hmem1 hpos1
    let Inv : ℕ → State → Prop := fun j st =>
      st.regs rI = j ∧
      st.regs rLim = lim ∧
      st.regs rOutM = prevM + j ∧
      (∀ r, r ≠ rOutM → r ≠ rLim → r ≠ rI → r ≠ rU → r ≠ rV → st.regs r = st₀.regs r) ∧
      st.pos = st₀.pos ∧
      MemFrame mem st.mem outA (outA + 2 * cap) ∧
      EdgesAt st.mem outA (prevEdges ++ (A_l.zip B_l).take j)
    have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLim)
      (body := seqStmts [
        .assign rU (.load (.bin .add (.reg rUnmA) (.reg rI))),
        .assign rV (.load (.bin .add (.reg rUnmB) (.reg rI))),
        .store (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.reg rU),
        .store (.bin .add (.bin .add (.reg rOutEdges) (.bin .mul (.const 2) (.reg rOutM))) (.const 1)) (.reg rV),
        .assign rOutM (.bin .add (.reg rOutM) (.const 1))])
      (P := fun st => st = st1) (Inv := Inv) 44 0 lim (Nat.zero_le lim) (by omega) (fun _ => by omega)
      (fun st hs => by
        subst hs
        refine ⟨Expr.eval_const (by omega), by simp,
          by dsimp only; rw [Function.update_of_ne hL_I, hrLim1],
          by dsimp only; rw [Function.update_of_ne hOM_I, hrOM1]; omega,
          fun r h1 h2 h3 _ _ => by dsimp only; rw [Function.update_of_ne h3]; exact hoth1 r h1 h2 h3 (by omega) (by omega),
          hpos1, hmem1 ▸ memFrame_refl _ _ _, by simpa [hmem1] using hP_at⟩)
      (fun _ st _ _ hInv => hInv.1)
      (fun _ st _ _ hInv => Expr.eval_reg_of_eq (v := lim) hInv.2.1)
      (fun j _ hjlt => by
        intro st ω ⟨hj, hlim', hom', hoth, hpos, hfr, hE⟩
        have hjA : j < A_l.length := by omega
        have hjB : j < B_l.length := by omega
        set u := A_l[j]'hjA
        set v := B_l[j]'hjB
        have hrUA' : st.regs rUnmA = ua :=
          (hoth rUnmA (by omega) hUA_L hUA_I hUA_U hUA_V).trans hrUA
        have hrUB' : st.regs rUnmB = ub :=
          (hoth rUnmB (by omega) hUB_L hUB_I hUB_U hUB_V).trans hrUB
        have hrOE' : st.regs rOutEdges = outA :=
          (hoth rOutEdges (by omega) hOE_L hOE_I hOE_U hOE_V).trans hrOE
        have hmem_u : st.mem (ua + j) = u := by
          rw [hfr (ua + j) (disjointRange_outside hdisjA (by omega) (by omega))]
          exact hA_at j hjA
        have hmem_v : st.mem (ub + j) = v := by
          rw [hfr (ub + j) (disjointRange_outside hdisjB (by omega) (by omega))]
          exact hB_at j hjB
        refine runs_start_le ?_
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := u)
          (Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hrUA') (Expr.eval_reg_of_eq hj) (by omega)) hmem_u) ?_
        refine runs_seq_assign_le (v := v)
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ub) (by dsimp only; rw [Function.update_of_ne hUB_U, hrUB']))
              (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne hI_U, hj]))
              (by omega)) hmem_v) ?_
        refine runs_seq_store_le (x := outA + 2 * (prevM + j)) (v := u)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := outA)
              (by dsimp only; rw [Function.update_of_ne hOE_V, Function.update_of_ne hOE_U, hrOE']))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := prevM + j)
                (by dsimp only; rw [Function.update_of_ne hOM_V, Function.update_of_ne hOM_U, hom']))
              (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := u)
            (by dsimp only; rw [Function.update_of_ne hU_V, Function.update_self])) ?_
        refine runs_seq_store_le (x := outA + 2 * (prevM + j) + 1) (v := v)
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := outA)
                (by dsimp only; rw [Function.update_of_ne hOE_V, Function.update_of_ne hOE_U, hrOE']))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := prevM + j)
                  (by dsimp only; rw [Function.update_of_ne hOM_V, Function.update_of_ne hOM_U, hom']))
                (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := v) (by simp)) ?_
        refine runs_assign_le (v := prevM + j + 1)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := prevM + j)
              (by dsimp only; rw [Function.update_of_ne hOM_V, Function.update_of_ne hOM_U, hom']))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne hL_I, Function.update_of_ne (Ne.symm hOM_L),
            Function.update_of_ne hL_V, Function.update_of_ne hL_U, hlim'],
          by dsimp only; rw [Function.update_of_ne hOM_I, Function.update_self]; omega,
          fun r h1 h2 h3 h4 h5 => by
            dsimp only; rw [Function.update_of_ne h3, Function.update_of_ne h1,
              Function.update_of_ne h5, Function.update_of_ne h4]
            exact hoth r h1 h2 h3 h4 h5,
          hpos,
          memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega))), ?_⟩,
          by dsimp only; rw [Function.update_of_ne (Ne.symm hOM_I),
            Function.update_of_ne hI_V, Function.update_of_ne hI_U, hj]⟩
        intro t ht
        dsimp only
        have htake_s : (A_l.zip B_l).take (j + 1) = (A_l.zip B_l).take j ++ [(u, v)] := by
          rw [List.take_succ_eq_append_getElem (by omega)]
          simp [u, v, List.getElem_zip]
        have hpre_len : (prevEdges ++ (A_l.zip B_l).take j).length = prevM + j := by
          rw [List.length_append, hplen, List.length_take, hzip_len]; omega
        have ht' : t < prevM + j + 1 := by
          rw [htake_s, ← List.append_assoc, List.length_append, hpre_len, List.length_singleton] at ht
          exact ht
        by_cases hteq : t = prevM + j
        · subst hteq
          have hget : (prevEdges ++ (A_l.zip B_l).take (j + 1))[prevM + j]'ht = (u, v) := by
            have h1 : prevEdges ++ (A_l.zip B_l).take (j + 1) =
                (prevEdges ++ (A_l.zip B_l).take j) ++ [(u, v)] := by
              rw [htake_s, List.append_assoc]
            simp only [h1]; rw [List.getElem_append_right (by omega)]; simp [hpre_len]
          rw [hget]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
            by rw [Function.update_self]⟩
        · have htlt : t < (prevEdges ++ (A_l.zip B_l).take j).length := by omega
          have hget : (prevEdges ++ (A_l.zip B_l).take (j + 1))[t]'ht =
              (prevEdges ++ (A_l.zip B_l).take j)[t]'htlt := by
            have h1 : prevEdges ++ (A_l.zip B_l).take (j + 1) =
                (prevEdges ++ (A_l.zip B_l).take j) ++ [(u, v)] := by
              rw [htake_s, List.append_assoc]
            simp only [h1]; exact List.getElem_append_left htlt
          rw [hget]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                    exact (hE t htlt).1,
            by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
               exact (hE t htlt).2⟩)
    refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
    rintro (_ | v) st' hInv
    · rcases hInv with ⟨_, _, hom', hoth', hpos', hfr', hE'⟩
      refine ⟨hom', hoth', hpos', hfr', ?_⟩
      rw [← hzip_len, List.take_length] at hE'
      exact hE'
    · exact hInv.elim
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [scZipAppendStmt, seqStmts]
  refine runs_seq_cond_le (v := if cntA < cntB then 1 else 0)
    (Expr.eval_bin (op := .lt) (Expr.eval_reg_of_eq hrCA) (Expr.eval_reg_of_eq hrCB)
      (by simp; split_ifs <;> omega))
    (fun hlt_ne => ?_) (fun hlt_0 => ?_)
  · have hlt : cntA < cntB := by by_contra h; simp [h] at hlt_ne
    have hlim_eq : cntA = lim := by rw [hlim_def]; omega
    refine runs_seq_assign_le (v := cntA) (Expr.eval_reg_of_eq hrCA) ?_
    let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs rLim cntA, pos := st₀.pos }
    obtain ⟨o, st', c, hr, hq, hc⟩ := hinner st1
      (by dsimp only [st1]; rw [Function.update_self]; exact hlim_eq)
      (by dsimp only [st1]; rw [Function.update_of_ne hOM_L, hrOM])
      (fun r _ h2 _ _ _ => by dsimp only [st1]; rw [Function.update_of_ne h2]) hmem rfl st1 ω rfl
    exact ⟨o, st', c, hr, hq, by simp [Expr.size] at hc ⊢; omega⟩
  · have hge : cntB ≤ cntA := by by_contra h; simp [Nat.not_le.mp h] at hlt_0
    have hlim_eq : cntB = lim := by rw [hlim_def]; omega
    refine runs_seq_assign_le (v := cntB) (Expr.eval_reg_of_eq hrCB) ?_
    let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs rLim cntB, pos := st₀.pos }
    obtain ⟨o, st', c, hr, hq, hc⟩ := hinner st1
      (by dsimp only [st1]; rw [Function.update_self]; exact hlim_eq)
      (by dsimp only [st1]; rw [Function.update_of_ne hOM_L, hrOM])
      (fun r _ h2 _ _ _ => by dsimp only [st1]; rw [Function.update_of_ne h2]) hmem rfl st1 ω rfl
    exact ⟨o, st', c, hr, hq, by simp [Expr.size] at hc ⊢; omega⟩

/-- Triple for `scCopyCutStmt`: copies `[1, U_list.length, u_0, ...]` from `srcA` to `dstA`. -/
lemma scCopyCut_triple {w cap srcA dstA rSrc rDst rLen rI rU : ℕ}
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
    Triple w p (fun st => st = st₀) (scCopyCutStmt rSrc rDst rLen rI rU)
      (normalPost fun st' =>
        (∀ r, r ≠ rLen → r ≠ rI → r ≠ rU → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem dstA (dstA + cap) ∧
        st'.mem dstA = 1 ∧
        st'.mem (dstA + 1) = U_list.length ∧
        ListAt st'.mem (dstA + 2) U_list)
      (fun _ => 30 * U_list.length + 40) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, hS_L, hS_I, hS_U⟩, ⟨hD_L, hD_I, hD_U⟩, ⟨hL_I, hL_U⟩, hI_U, _⟩
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [scCopyCutStmt, seqStmts]
  refine runs_seq_assign_le (v := U_list.length)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hrSrc) (Expr.eval_const (by omega)) (by omega))
      (hmem ▸ hlen)) ?_
  refine runs_seq_store_le (x := dstA) (v := 1)
    (Expr.eval_reg_of_eq (v := dstA) (by dsimp only; rw [Function.update_of_ne hD_L, hrDst]))
    (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := dstA + 1) (v := U_list.length)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := dstA) (by dsimp only; rw [Function.update_of_ne hD_L, hrDst]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := U_list.length) (by simp)) ?_
  let mem1 := Function.update (Function.update mem dstA 1) (dstA + 1) U_list.length
  let st1 : State := { mem := mem1, regs := Function.update st₀.regs rLen U_list.length, pos := st₀.pos }
  have hfr1 : MemFrame mem mem1 dstA (dstA + cap) :=
    memFrame_trans (memFrame_update (by omega) (by omega)) (memFrame_update (by omega) (by omega))
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    st.regs rLen = U_list.length ∧
    (∀ r, r ≠ rLen → r ≠ rI → r ≠ rU → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem dstA (dstA + cap) ∧
    st.mem dstA = 1 ∧
    st.mem (dstA + 1) = U_list.length ∧
    ∀ t (ht : t < j) (htU : t < U_list.length), st.mem (dstA + 2 + t) = U_list[t]'htU
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rU (.load (.bin .add (.bin .add (.reg rSrc) (.const 2)) (.reg rI))),
      .store (.bin .add (.bin .add (.reg rDst) (.const 2)) (.reg rI)) (.reg rU)])
    (P := fun st => st = st1) (Inv := Inv) 18 0 U_list.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne hL_I, Function.update_self],
        fun r h1 h2 _ => by dsimp only [st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
        rfl, hfr1,
        by dsimp only [st1, mem1]; rw [Function.update_of_ne (by omega), Function.update_self],
        by dsimp only [st1, mem1]; rw [Function.update_self],
        fun t ht _ => by omega⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq (v := U_list.length) hInv.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hj, hlen', hoth, hpos, hfr, hm0, hm1, hdone⟩
      have hrS' : st.regs rSrc = srcA := (hoth rSrc hS_L hS_I hS_U).trans hrSrc
      have hrD' : st.regs rDst = dstA := (hoth rDst hD_L hD_I hD_U).trans hrDst
      have hsrc : st.mem (srcA + 2 + j) = U_list[j]'hjlt := by
        rw [hfr (srcA + 2 + j) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hU_at j hjlt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := U_list[j]'hjlt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hrS') (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq hj) (by omega)) hsrc) ?_
      refine runs_store_le (x := dstA + 2 + j) (v := U_list[j]'hjlt)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := dstA) (by dsimp only; rw [Function.update_of_ne hD_U, hrD']))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne hI_U, hj])) (by omega))
        (Expr.eval_reg_of_eq (v := U_list[j]'hjlt) (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne hL_I, Function.update_of_ne hL_U, hlen'],
        fun r h1 h2 h3 => by
          dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h3]
          exact hoth r h1 h2 h3,
        hpos,
        memFrame_trans hfr (memFrame_update (by omega) (by omega)),
        by dsimp only; rw [Function.update_of_ne (by omega), hm0],
        by dsimp only; rw [Function.update_of_ne (by omega), hm1], ?_⟩,
        by dsimp only; rw [Function.update_of_ne hI_U, hj]⟩
      intro t ht htU
      dsimp only
      by_cases htj : t = j
      · subst t; rw [Function.update_self]
      · rw [Function.update_of_ne (by omega)]; exact hdone t (by omega) htU)
  obtain ⟨o, st', c, hr, hq, hc⟩ := hloop st1 ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨_, _, hoth', hpos', hfr', hm0', hm1', hdone'⟩
    refine ⟨.normal, st', c, ?_, ⟨hoth', hpos', hfr', hm0', hm1', fun t ht => hdone' t ht ht⟩,
      by simp [Expr.size] at hc ⊢; omega⟩
    dsimp only [seqStmts] at hr ⊢
    convert hr using 1
    simp [st1, mem1, hmem]

end MinCostFlow.ExpanderDecomp
