module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCBase

import Mathlib.Tactic.Linarith

/-!
# Step C Colour Extraction and Pair Encoding (`ProgStepCExtract`)

Implements and verifies the three inner loops executed for each colour class `c ∈ {0, …, 16}` of
`stepCMacro` (`OneShot.lean`):

1. `scExtractColorStmt` / `scExtractColor_triple`: scans `colM` coloured triples at `colAddr` and
   writes `Ec = colorClass colored c` into `ecAddr`, leaving `Ec.length` in `r17`.
2. `scBuildPairsStmt` / `scBuildPairs_triple`: writes the flat multi-pair layout
   `encodePairs (Ec.map fun e => (blockList vs b e.1, blockList vs b e.2))` starting at `pairsAddr`,
   leaving the end pointer `pairsAddr + 1 + Ec.length * (2 * b + 2)` in `r19`.
3. `scCompleteFakeLoopStmt` / `scCompleteFakeLoop_triple`: given `locAddr` marking
   `matchedVerts matchings.flatten`, appends `completeBatchFake pairs matchings` to
   `outAddr + 2 + 2 * fakeM` in `O(|X| + |Ec| + 1)` time using `scCollectUnmatchedStmt` and
   `scZipAppendStmt` (`ProgStepCBase.lean`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Prefix Helpers for Colour Extraction and Pair Encoding -/

lemma colorClass_take_succ {colored : List ((ℕ × ℕ) × ℕ)} {c j : ℕ} (hj : j < colored.length) :
    colorClass (colored.take (j + 1)) c =
      colorClass (colored.take j) c ++
        if (colored[j]'hj).2 = c then [(colored[j]'hj).1] else [] := by
  unfold colorClass
  rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.filter_cons, List.filter_nil,
    List.map_append]
  by_cases h : (colored[j]'hj).2 = c <;> simp [h]

lemma encodePairs_blocks_length {vs : List ℕ} {b : ℕ} {Ec : List (ℕ × ℕ)}
    (hvalid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b) :
    (encodePairs (Ec.map fun e => (blockList vs b e.1, blockList vs b e.2))).length =
      1 + Ec.length * (2 * b + 2) := by
  unfold encodePairs
  simp only [List.length_cons, List.length_map]
  suffices h : ((Ec.map fun e => (blockList vs b e.1, blockList vs b e.2)).flatMap encodePair).length =
      Ec.length * (2 * b + 2) by omega
  induction Ec with
  | nil => simp
  | cons e rest ih =>
    have hv := hvalid e List.mem_cons_self
    have hrest : ∀ e' ∈ rest, e'.1 < numFullBlocks vs b ∧ e'.2 < numFullBlocks vs b :=
      fun e' he' => hvalid e' (List.mem_cons_of_mem _ he')
    simp only [List.map_cons, List.flatMap_cons, List.length_append, encodePair_length,
      blockList_length hv.1, blockList_length hv.2, List.length_cons, ih hrest]
    ring

lemma encodePairs_blocks_take_succ {vs : List ℕ} {b j : ℕ} {Ec : List (ℕ × ℕ)}
    (hj : j < Ec.length) :
    ((Ec.take (j + 1)).map fun e => (blockList vs b e.1, blockList vs b e.2)).flatMap encodePair =
      (((Ec.take j).map fun e => (blockList vs b e.1, blockList vs b e.2)).flatMap encodePair) ++
        encodePair (blockList vs b (Ec[j]'hj).1, blockList vs b (Ec[j]'hj).2) := by
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma completeBatchFake_take_succ {pairs : List (Finset ℕ × Finset ℕ)}
    {matchings : List (List (ℕ × ℕ))} {j : ℕ}
    (hj : j < pairs.length) (hmlen : matchings.length = pairs.length) :
    completeBatchFake (pairs.take (j + 1)) (matchings.take (j + 1)) =
      completeBatchFake (pairs.take j) (matchings.take j) ++
        completeMatchingFake (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings[j]'(by omega)) := by
  unfold completeBatchFake
  have hlen_t : (pairs.take j).length = (matchings.take j).length := by
    simp [List.length_take, hmlen]
  rw [List.take_succ_eq_append_getElem hj, List.take_succ_eq_append_getElem (by omega : j < matchings.length),
    List.zipWith_append hlen_t, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]

/-! ## 2. Statements (`NoRand`) -/

/-- Scan `r7` (`colM`) coloured triples at `r8` (`colAddr`), extracting all edges with colour `r15`
into `r16` (`ecAddr`) and storing the extracted count in `r17` (`ecM`). Scratch: `r20..r23`. -/
def scExtractColorStmt : Stmt :=
  seqStmts [
    .assign 17 (.const 0),
    forRange 20 (.const 0) (.reg 7) (
      seqStmts [
        .assign 21 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20))) (.const 2))),
        .cond (.bin .eq (.reg 21) (.reg 15))
          (seqStmts [
            .assign 22 (.load (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20)))),
            .assign 23 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20))) (.const 1))),
            .store (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))) (.reg 22),
            .store (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))) (.const 1)) (.reg 23),
            .assign 17 (.bin .add (.reg 17) (.const 1))
          ])
          .nop
      ]
    )
  ]

theorem scExtractColorStmt_noRand : scExtractColorStmt.NoRand := by
  simp [scExtractColorStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Build `encodePairs (Ec.map fun e => (blockList vs b e.1, blockList vs b e.2))` starting at
`r18` (`pairsAddr`), reading `r17` (`ecM`) pairs at `r16` (`ecAddr`), `vs` at `r1 + 1`, block size
`r2` (`b`), leaving the end pointer `pairsAddr + 1 + ecM * (2 * b + 2)` in `r19`.
Scratch: `r20..r25`. -/
def scBuildPairsStmt : Stmt :=
  seqStmts [
    .store (.reg 18) (.reg 17),
    .assign 19 (.bin .add (.reg 18) (.const 1)),
    forRange 20 (.const 0) (.reg 17) (
      seqStmts [
        .assign 21 (.load (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 20)))),
        .assign 22 (.load (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 20))) (.const 1))),
        .store (.reg 19) (.reg 2),
        .assign 19 (.bin .add (.reg 19) (.const 1)),
        .assign 23 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 21) (.reg 2))),
        forRange 24 (.const 0) (.reg 2) (
          seqStmts [
            .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
            .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)
          ]
        ),
        .assign 19 (.bin .add (.reg 19) (.reg 2)),
        .store (.reg 19) (.reg 2),
        .assign 19 (.bin .add (.reg 19) (.const 1)),
        .assign 23 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 22) (.reg 2))),
        forRange 24 (.const 0) (.reg 2) (
          seqStmts [
            .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
            .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)
          ]
        ),
        .assign 19 (.bin .add (.reg 19) (.reg 2))
      ]
    )
  ]

theorem scBuildPairsStmt_noRand : scBuildPairsStmt.NoRand := by
  simp [scBuildPairsStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Complete all fake edges of colour class `Ec` (`r17` pairs at `r16`), using `locAddr` (`r9`)
marking `matchedVerts matchings.flatten`, temp buffers `unmA` (`r18`), `unmB` (`r19`), output edge
start `r20 = outAddr + 2`, and current output edge count `r14` (`fakeM`). Scratch: `r21..r29`. -/
def scCompleteFakeLoopStmt : Stmt :=
  forRange 21 (.const 0) (.reg 17) (
    seqStmts [
      .assign 22 (.load (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 21)))),
      .assign 23 (.load (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 21))) (.const 1))),
      .assign 24 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 22) (.reg 2))),
      scCollectUnmatchedStmt 24 2 9 18 25 27 28,
      .assign 24 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 23) (.reg 2))),
      scCollectUnmatchedStmt 24 2 9 19 26 27 28,
      scZipAppendStmt 18 25 19 26 20 14 27 28 24 29
    ]
  )

theorem scCompleteFakeLoopStmt_noRand : scCompleteFakeLoopStmt.NoRand := by
  simp [scCompleteFakeLoopStmt, scCollectUnmatchedStmt, scZipAppendStmt, seqStmts, forRange, forUp,
    Stmt.NoRand]

/-! ## 3. Triples for the Three Sub-Loops -/

/-- Triple for `scExtractColorStmt`. -/
lemma scExtractColor_triple {w colM colA ecA c : ℕ}
    (p : Program) (mem : ℕ → ℕ) (colored : List ((ℕ × ℕ) × ℕ)) (st₀ : State)
    (hlen : colored.length = colM)
    (hcol_at : ColoredEdgesAt mem colA colored)
    (hdisj : DisjointRange ecA (2 * colM) colA (3 * colM))
    (hcol_w : colA + 3 * colM < 2 ^ w) (hec_w : ecA + 2 * colM < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr7 : st₀.regs 7 = colM) (hr8 : st₀.regs 8 = colA)
    (hr15 : st₀.regs 15 = c) (hr16 : st₀.regs 16 = ecA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) scExtractColorStmt
      (normalPost fun st' =>
        st'.regs 17 = (colorClass colored c).length ∧
        (∀ r, r ≠ 17 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem ecA (ecA + 2 * (colorClass colored c).length) ∧
        EdgesAt st'.mem ecA (colorClass colored c))
      (fun _ => 76 * colM + 30) := by
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [scExtractColorStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 17 0, pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 20 = j ∧
    st.regs 17 = (colorClass (colored.take j) c).length ∧
    (∀ r, r ≠ 17 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem ecA (ecA + 2 * (colorClass (colored.take j) c).length) ∧
    EdgesAt st.mem ecA (colorClass (colored.take j) c)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 7)
    (body := seqStmts [
      .assign 21 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20))) (.const 2))),
      .cond (.bin .eq (.reg 21) (.reg 15))
        (seqStmts [
          .assign 22 (.load (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20)))),
          .assign 23 (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 20))) (.const 1))),
          .store (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))) (.reg 22),
          .store (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 17))) (.const 1)) (.reg 23),
          .assign 17 (.bin .add (.reg 17) (.const 1))
        ])
        .nop])
    (P := fun st => st = st1) (Inv := Inv) 64 0 colM (Nat.zero_le colM) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]; simp [colorClass],
        fun r h1 h2 _ _ _ => by dsimp only [st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun j hj => by simp [colorClass] at hj⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := colM)
        (by rw [hInv.2.2.1 7 (by decide) (by decide) (by decide) (by decide) (by decide), hr7]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hcnt, hoth, hpos, hfr, hE⟩
      have hj_len : j < colored.length := hlen.symm ▸ hjlt
      set ec := colored[j]'hj_len
      have hr8' : st.regs 8 = colA :=
        (hoth 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr8
      have hr15' : st.regs 15 = c :=
        (hoth 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr15
      have hr16' : st.regs 16 = ecA :=
        (hoth 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr16
      have hcnt_le : (colorClass (colored.take j) c).length ≤ j := by
        unfold colorClass
        rw [List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp [List.length_take])
      have hout_col : ∀ off < 3, colA + 3 * j + off < ecA ∨
          ecA + 2 * (colorClass (colored.take j) c).length ≤ colA + 3 * j + off := by
        intro off hoff
        rcases hdisj with h1 | h1 <;> [right; left] <;> omega
      have hmem_c : st.mem (colA + 3 * j + 2) = ec.2 := by
        rw [hfr _ (hout_col 2 (by omega))]; exact (hcol_at j hj_len).2.2
      have hmem_u : st.mem (colA + 3 * j) = ec.1.1 := by
        rw [hfr _ (by simpa using hout_col 0 (by omega))]; exact (hcol_at j hj_len).1
      have hmem_v : st.mem (colA + 3 * j + 1) = ec.1.2 := by
        rw [hfr _ (hout_col 1 (by omega))]; exact (hcol_at j hj_len).2.1
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ec.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq hr8')
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem_c) ?_
      refine runs_cond_le (v := if ec.2 = c then 1 else 0)
        (Expr.eval_eq_op (Expr.eval_reg_of_eq (v := ec.2) (by simp))
          (Expr.eval_reg_of_eq (v := c) (by dsimp only; rw [Function.update_of_ne (by decide), hr15']))
          (by omega))
        (fun hne => ?_) (fun h0 => ?_)
      · have heq_c : ec.2 = c := by by_contra h; simp [h] at hne
        have htake_s : colorClass (colored.take (j + 1)) c =
            colorClass (colored.take j) c ++ [ec.1] := by
          rw [colorClass_take_succ hj_len]; simp [ec, heq_c]
        set cur := (colorClass (colored.take j) c).length
        refine runs_seq_assign_le (v := ec.1.1)
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := colA) (by dsimp only; rw [Function.update_of_ne (by decide), hr8']))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj]))
                (by omega)) (by omega)) hmem_u) ?_
        refine runs_seq_assign_le (v := ec.1.2)
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := colA)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr8']))
                (Expr.eval_mul (Expr.eval_const (by omega))
                  (Expr.eval_reg_of_eq (v := j)
                    (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]))
                  (by omega)) (by omega))
              (Expr.eval_const (by omega)) (by omega)) hmem_v) ?_
        refine runs_seq_store_le (x := ecA + 2 * cur) (v := ec.1.1)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := ecA)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr16']))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := cur)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                  Function.update_of_ne (by decide), hcnt])) (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := ec.1.1)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self])) ?_
        refine runs_seq_store_le (x := ecA + 2 * cur + 1) (v := ec.1.2)
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ecA)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                  Function.update_of_ne (by decide), hr16']))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := cur)
                  (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                    Function.update_of_ne (by decide), hcnt])) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq (v := ec.1.2) (by simp)) ?_
        refine runs_assign_le (v := cur + 1)
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := cur)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hcnt]))
            (Expr.eval_const (by omega)) (by omega)) ?_ (by simp [Expr.size])
        have hlen_s : (colorClass (colored.take (j + 1)) c).length = cur + 1 := by
          rw [htake_s, List.length_append, List.length_singleton]
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self, hlen_s],
          fun r h1 h2 h3 h4 h5 => by
            dsimp only
            rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h5,
              Function.update_of_ne h4, Function.update_of_ne h3]
            exact hoth r h1 h2 h3 h4 h5,
          hpos, ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
        · rw [hlen_s]
          have hfr_w : MemFrame mem st.mem ecA (ecA + 2 * (cur + 1)) :=
            fun a ha => hfr a (by rcases ha with h1 | h2 <;> [left; right] <;> omega)
          exact memFrame_trans hfr_w (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega)))
        · intro t ht
          dsimp only
          have ht' : t < cur + 1 := hlen_s ▸ ht
          by_cases hteq : t = cur
          · subst hteq
            have hget : (colorClass (colored.take (j + 1)) c)[cur]'ht = ec.1 := by
              simp only [htake_s]; rw [List.getElem_append_right (by omega)]; simp [cur]
            rw [hget]
            exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
              by rw [Function.update_self]⟩
          · have htlt : t < cur := by omega
            have hget : (colorClass (colored.take (j + 1)) c)[t]'ht =
                (colorClass (colored.take j) c)[t]'htlt := by
              simp only [htake_s]; exact List.getElem_append_left htlt
            rw [hget]
            exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                      exact (hE t htlt).1,
              by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                 exact (hE t htlt).2⟩
      · have hne_c : ec.2 ≠ c := fun h => by simp [h] at h0
        have htake_s : colorClass (colored.take (j + 1)) c = colorClass (colored.take j) c := by
          rw [colorClass_take_succ hj_len]; simp [ec, hne_c]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            hcnt, htake_s],
          fun r h1 h2 h3 h4 h5 => by
            dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h3]
            exact hoth r h1 h2 h3 h4 h5,
          hpos, htake_s.symm ▸ hfr, htake_s.symm ▸ hE⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), hj]⟩)
  obtain ⟨o, st', c', hr, hq, hc⟩ := hloop st1 ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨_, hcnt', hoth', hpos', hfr', hE'⟩
    have hfull : colored.take colM = colored := by rw [← hlen, List.take_length]
    rw [hfull] at hcnt' hfr' hE'
    exact ⟨.normal, st', c', hr, ⟨hcnt', hoth', hpos', hfr', hE'⟩, by simp [Expr.size] at hc ⊢; omega⟩

/-- Helper triple copying `b` elements from `mem[srcA + t]` to `mem[dstA + t]`. -/
private lemma scCopyBlock_triple {w b srcA dstA : ℕ}
    (p : Program) (mem : ℕ → ℕ) (blk : List ℕ) (st₀ : State)
    (hlen : blk.length = b) (hblk_at : ListAt mem srcA blk)
    (hdisj : DisjointRange dstA b srcA b)
    (hsrc_w : srcA + b < 2 ^ w) (hdst_w : dstA + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr2 : st₀.regs 2 = b) (hr19 : st₀.regs 19 = dstA) (hr23 : st₀.regs 23 = srcA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀)
      (forRange 24 (.const 0) (.reg 2) (
        seqStmts [
          .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
          .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)
        ]))
      (normalPost fun st' =>
        (∀ r, r ≠ 24 → r ≠ 25 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem dstA (dstA + b) ∧
        ListAt st'.mem dstA blk)
      (fun _ => 26 * b + 20) := by
  let Inv : ℕ → State → Prop := fun t st =>
    st.regs 24 = t ∧
    (∀ r, r ≠ 24 → r ≠ 25 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem dstA (dstA + b) ∧
    ∀ q (hq : q < t) (hqb : q < b), st.mem (dstA + q) = blk[q]'(by omega)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 24) (lo := .const 0) (hi := .reg 2)
    (body := seqStmts [
      .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
      .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)])
    (P := fun st => st = st₀) (Inv := Inv) 16 0 b (Nat.zero_le b) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r h1 _ => by dsimp only; rw [Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun q hq _ => by omega⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq (v := b) (by rw [hInv.2.1 2 (by decide) (by decide), hr2]))
    (fun t _ htlt => by
      intro st ω ⟨ht, hoth, hpos, hfr, hdone⟩
      have hr19' : st.regs 19 = dstA := (hoth 19 (by decide) (by decide)).trans hr19
      have hr23' : st.regs 23 = srcA := (hoth 23 (by decide) (by decide)).trans hr23
      have hsrc : st.mem (srcA + t) = blk[t]'(by omega) := by
        rw [hfr (srcA + t) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hblk_at t (by omega)
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := blk[t]'(by omega))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr23') (Expr.eval_reg_of_eq ht) (by omega)) hsrc) ?_
      refine runs_store_le (x := dstA + t) (v := blk[t]'(by omega))
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := dstA) (by dsimp only; rw [Function.update_of_ne (by decide), hr19']))
          (Expr.eval_reg_of_eq (v := t) (by dsimp only; rw [Function.update_of_ne (by decide), ht]))
          (by omega))
        (Expr.eval_reg_of_eq (v := blk[t]'(by omega)) (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp,
        fun r h1 h2 => by dsimp only; rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hoth r h1 h2,
        hpos, memFrame_trans hfr (memFrame_update (by omega) (by omega)), ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), ht]⟩
      intro q hq hqb
      dsimp only
      by_cases hqt : q = t
      · subst q; rw [Function.update_self]
      · rw [Function.update_of_ne (by omega)]; exact hdone q (by omega) hqb)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro (_ | v) st' hInv
  · rcases hInv with ⟨_, hoth, hpos, hfr, hdone⟩
    exact ⟨hoth, hpos, hfr, fun q hq => hdone q (by omega) (by omega)⟩
  · exact hInv.elim

/-- Triple for `scBuildPairsStmt`: encodes all `ecM` block pairs at `pairsAddr`. -/
lemma scBuildPairs_triple {w xA b ecM ecA pA : ℕ}
    (p : Program) (mem : ℕ → ℕ) (vs : List ℕ) (Ec : List (ℕ × ℕ)) (st₀ : State)
    (hvs_at : LenListAt mem xA vs)
    (hEc_len : Ec.length = ecM) (hEc_at : EdgesAt mem ecA Ec)
    (hEc_valid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b)
    (hdisj_vs : DisjointRange pA (1 + ecM * (2 * b + 2)) (xA + 1) vs.length)
    (hdisj_ec : DisjointRange pA (1 + ecM * (2 * b + 2)) ecA (2 * ecM))
    (hx_w : xA + 1 + vs.length < 2 ^ w) (hec_w : ecA + 2 * ecM < 2 ^ w)
    (hp_w : pA + 1 + ecM * (2 * b + 2) < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr1 : st₀.regs 1 = xA) (hr2 : st₀.regs 2 = b)
    (hr16 : st₀.regs 16 = ecA) (hr17 : st₀.regs 17 = ecM) (hr18 : st₀.regs 18 = pA)
    (hmem : st₀.mem = mem) :
    let pairLists := Ec.map fun e => (blockList vs b e.1, blockList vs b e.2)
    Triple w p (fun st => st = st₀) scBuildPairsStmt
      (normalPost fun st' =>
        st'.regs 19 = pA + 1 + ecM * (2 * b + 2) ∧
        (∀ r, r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem pA (pA + 1 + ecM * (2 * b + 2)) ∧
        MultiPairsAt st'.mem pA pairLists)
      (fun _ => 52 * (ecM * b) + 120 * ecM + 40) := by
  intro pairLists
  have hblk_at : ∀ i < numFullBlocks vs b, ListAt mem (xA + 1 + i * b) (blockList vs b i) := by
    intro i hi t ht
    rw [blockList_length hi] at ht
    have hidx : i * b + t < vs.length := by
      have hmul : numFullBlocks vs b * b ≤ vs.length := Nat.div_mul_le_self vs.length b
      have h1 : (i + 1) * b ≤ numFullBlocks vs b * b := Nat.mul_le_mul_right b hi
      have h2 : (i + 1) * b = i * b + b := by ring
      omega
    have hget : (blockList vs b i)[t]'(by rw [blockList_length hi]; exact ht) = vs[i * b + t]'hidx := by
      simp [blockList]
    rw [hget]
    have hshift : xA + 1 + i * b + t = (xA + 1) + (i * b + t) := by omega
    rw [hshift]
    exact hvs_at.2 (i * b + t) hidx
  intro st ω hst
  subst st
  refine runs_start_le ?_
  dsimp only [scBuildPairsStmt, seqStmts]
  refine runs_seq_store_le (x := pA) (v := ecM) (Expr.eval_reg_of_eq hr18) (Expr.eval_reg_of_eq hr17) ?_
  refine runs_seq_assign_le (v := pA + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq hr18) (Expr.eval_const (by omega)) (by omega)) ?_
  let mem1 := Function.update mem pA ecM
  let st1 : State := { mem := mem1, regs := Function.update st₀.regs 19 (pA + 1), pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 20 = j ∧
    st.regs 19 = pA + 1 + j * (2 * b + 2) ∧
    (∀ r, r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem pA (pA + 1 + ecM * (2 * b + 2)) ∧
    st.mem pA = ecM ∧
    ListAt st.mem (pA + 1)
      (((Ec.take j).map fun e => (blockList vs b e.1, blockList vs b e.2)).flatMap encodePair)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 17)
    (body := seqStmts [
      .assign 21 (.load (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 20)))),
      .assign 22 (.load (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 20))) (.const 1))),
      .store (.reg 19) (.reg 2),
      .assign 19 (.bin .add (.reg 19) (.const 1)),
      .assign 23 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 21) (.reg 2))),
      forRange 24 (.const 0) (.reg 2) (
        seqStmts [
          .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
          .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)
        ]),
      .assign 19 (.bin .add (.reg 19) (.reg 2)),
      .store (.reg 19) (.reg 2),
      .assign 19 (.bin .add (.reg 19) (.const 1)),
      .assign 23 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 22) (.reg 2))),
      forRange 24 (.const 0) (.reg 2) (
        seqStmts [
          .assign 25 (.load (.bin .add (.reg 23) (.reg 24))),
          .store (.bin .add (.reg 19) (.reg 24)) (.reg 25)
        ]),
      .assign 19 (.bin .add (.reg 19) (.reg 2))])
    (P := fun st => st = st1) (Inv := Inv) (52 * b + 110) 0 ecM (Nat.zero_le ecM) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]; omega,
        fun r h1 h2 _ _ _ _ _ => by dsimp only [st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
        rfl, memFrame_update (by omega) (by omega),
        by dsimp only [st1, mem1]; rw [Function.update_self],
        fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := ecM)
        (by rw [hInv.2.2.1 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hcur, hoth, hpos, hfr, hmp0, hprev⟩
      have hj_len : j < Ec.length := hEc_len.symm ▸ hjlt
      set ed := Ec[j]'hj_len
      have hed_v := hEc_valid ed (List.getElem_mem hj_len)
      have hib1_le : ed.1 * b + b ≤ vs.length := by
        have hmul : numFullBlocks vs b * b ≤ vs.length := Nat.div_mul_le_self vs.length b
        have h1 : (ed.1 + 1) * b ≤ numFullBlocks vs b * b := Nat.mul_le_mul_right b hed_v.1
        have h2 : (ed.1 + 1) * b = ed.1 * b + b := by ring
        omega
      have hib2_le : ed.2 * b + b ≤ vs.length := by
        have hmul : numFullBlocks vs b * b ≤ vs.length := Nat.div_mul_le_self vs.length b
        have h1 : (ed.2 + 1) * b ≤ numFullBlocks vs b * b := Nat.mul_le_mul_right b hed_v.2
        have h2 : (ed.2 + 1) * b = ed.2 * b + b := by ring
        omega
      have hstep_le : (j + 1) * (2 * b + 2) ≤ ecM * (2 * b + 2) := Nat.mul_le_mul_right _ hjlt
      have hstep_eq : (j + 1) * (2 * b + 2) = j * (2 * b + 2) + (2 * b + 2) := by ring
      set off := pA + 1 + j * (2 * b + 2)
      have hr1' : st.regs 1 = xA :=
        (hoth 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr1
      have hr2' : st.regs 2 = b :=
        (hoth 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr2
      have hr16' : st.regs 16 = ecA :=
        (hoth 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr16
      have hmem_e1 : st.mem (ecA + 2 * j) = ed.1 := by
        have hout : ecA + 2 * j < pA ∨ pA + 1 + ecM * (2 * b + 2) ≤ ecA + 2 * j := by
          rcases hdisj_ec with h1 | h1 <;> [right; left] <;> omega
        rw [hfr _ hout]; exact (hEc_at j hj_len).1
      have hmem_e2 : st.mem (ecA + 2 * j + 1) = ed.2 := by
        have hout : ecA + 2 * j + 1 < pA ∨ pA + 1 + ecM * (2 * b + 2) ≤ ecA + 2 * j + 1 := by
          rcases hdisj_ec with h1 | h1 <;> [right; left] <;> omega
        rw [hfr _ hout]; exact (hEc_at j hj_len).2
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := ed.1)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr16')
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega))
          hmem_e1) ?_
      refine runs_seq_assign_le (v := ed.2)
        (Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := ecA) (by dsimp only; rw [Function.update_of_ne (by decide), hr16']))
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj]))
                (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega)) hmem_e2) ?_
      refine runs_seq_store_le (x := off) (v := b)
        (Expr.eval_reg_of_eq (v := off)
          (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcur]))
        (Expr.eval_reg_of_eq (v := b)
          (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2'])) ?_
      refine runs_seq_assign_le (v := off + 1)
        (Expr.eval_add
          (Expr.eval_reg_of_eq (v := off)
            (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcur]))
          (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := xA + 1 + ed.1 * b)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := xA)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr1']))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul
            (Expr.eval_reg_of_eq (v := ed.1)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_self]))
            (Expr.eval_reg_of_eq (v := b)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr2'])) (by omega)) (by omega)) ?_
      let memA0 := Function.update st.mem off b
      let stA0 : State :=
        { mem := memA0,
          regs := Function.update (Function.update (Function.update (Function.update st.regs 21 ed.1) 22 ed.2)
            19 (off + 1)) 23 (xA + 1 + ed.1 * b),
          pos := st.pos }
      have hfrA0 : MemFrame mem memA0 pA (pA + 1 + ecM * (2 * b + 2)) :=
        memFrame_trans hfr (memFrame_update (by omega) (by omega))
      have hblk1_at : ListAt memA0 (xA + 1 + ed.1 * b) (blockList vs b ed.1) := by
        intro t ht
        rw [blockList_length hed_v.1] at ht
        have hout : xA + 1 + ed.1 * b + t < pA ∨ pA + 1 + ecM * (2 * b + 2) ≤ xA + 1 + ed.1 * b + t := by
          rcases hdisj_vs with h1 | h1 <;> [right; left] <;> omega
        rw [hfrA0 _ hout]
        exact hblk_at ed.1 hed_v.1 t (by rw [blockList_length hed_v.1]; exact ht)
      have hdisjA1 : DisjointRange (off + 1) b (xA + 1 + ed.1 * b) b := by
        rcases hdisj_vs with h1 | h1 <;> [left; right] <;> omega
      refine runs_seq_triple_le
        (scCopyBlock_triple p memA0 (blockList vs b ed.1) stA0 (blockList_length hed_v.1)
          hblk1_at hdisjA1 (by omega) (by omega) hw16
          (by dsimp only [stA0]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2'])
          (by dsimp only [stA0]; rw [Function.update_of_ne (by decide), Function.update_self])
          (by dsimp only [stA0]; rw [Function.update_self]) rfl) rfl ?_
      intro stA1 ⟨hothA1, hposA1, hfrA1, hlistA1⟩
      have hr2_A1 : stA1.regs 2 = b := by
        rw [hothA1 2 (by decide) (by decide)]; dsimp only [stA0]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2']
      have hr19_A1 : stA1.regs 19 = off + 1 := by
        rw [hothA1 19 (by decide) (by decide)]; dsimp only [stA0]
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hr1_A1 : stA1.regs 1 = xA := by
        rw [hothA1 1 (by decide) (by decide)]; dsimp only [stA0]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr1']
      have hr22_A1 : stA1.regs 22 = ed.2 := by
        rw [hothA1 22 (by decide) (by decide)]; dsimp only [stA0]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
      refine runs_seq_assign_le (v := off + 1 + b)
        (Expr.eval_add (Expr.eval_reg_of_eq hr19_A1) (Expr.eval_reg_of_eq hr2_A1) (by omega)) ?_
      refine runs_seq_store_le (x := off + 1 + b) (v := b)
        (Expr.eval_reg_of_eq (v := off + 1 + b) (by simp))
        (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), hr2_A1])) ?_
      refine runs_seq_assign_le (v := off + 1 + b + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := off + 1 + b) (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := xA + 1 + ed.2 * b)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := xA)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr1_A1]))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul
            (Expr.eval_reg_of_eq (v := ed.2)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr22_A1]))
            (Expr.eval_reg_of_eq (v := b)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_A1]))
            (by omega)) (by omega)) ?_
      let memB0 := Function.update stA1.mem (off + 1 + b) b
      let stB0 : State :=
        { mem := memB0,
          regs := Function.update (Function.update (Function.update stA1.regs 19 (off + 1 + b))
            19 (off + 1 + b + 1)) 23 (xA + 1 + ed.2 * b),
          pos := stA1.pos }
      have hfrA1_big : MemFrame mem stA1.mem pA (pA + 1 + ecM * (2 * b + 2)) :=
        memFrame_trans hfrA0 (fun a ha => hfrA1 a (by rcases ha with h1 | h2 <;> [left; right] <;> omega))
      have hfrB0 : MemFrame mem memB0 pA (pA + 1 + ecM * (2 * b + 2)) :=
        memFrame_trans hfrA1_big (memFrame_update (by omega) (by omega))
      have hblk2_at : ListAt memB0 (xA + 1 + ed.2 * b) (blockList vs b ed.2) := by
        intro t ht
        rw [blockList_length hed_v.2] at ht
        have hout : xA + 1 + ed.2 * b + t < pA ∨ pA + 1 + ecM * (2 * b + 2) ≤ xA + 1 + ed.2 * b + t := by
          rcases hdisj_vs with h1 | h1 <;> [right; left] <;> omega
        rw [hfrB0 _ hout]
        exact hblk_at ed.2 hed_v.2 t (by rw [blockList_length hed_v.2]; exact ht)
      have hdisjB1 : DisjointRange (off + 2 + b) b (xA + 1 + ed.2 * b) b := by
        rcases hdisj_vs with h1 | h1 <;> [left; right] <;> omega
      refine runs_seq_triple_le
        (scCopyBlock_triple p memB0 (blockList vs b ed.2) stB0 (blockList_length hed_v.2)
          hblk2_at hdisjB1 (by omega) (by omega) hw16
          (by dsimp only [stB0]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr2_A1])
          (by dsimp only [stB0]; rw [Function.update_of_ne (by decide), Function.update_self]; omega)
          (by dsimp only [stB0]; rw [Function.update_self]) rfl) rfl ?_
      intro stB1 ⟨hothB1, hposB1, hfrB1, hlistB1⟩
      have hr2_B1 : stB1.regs 2 = b := by
        rw [hothB1 2 (by decide) (by decide)]; dsimp only [stB0]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr2_A1]
      have hr19_B1 : stB1.regs 19 = off + 2 + b := by
        rw [hothB1 19 (by decide) (by decide)]; dsimp only [stB0]
        rw [Function.update_of_ne (by decide), Function.update_self]; omega
      refine runs_assign_le (v := off + 2 + b + b)
        (Expr.eval_add (Expr.eval_reg_of_eq hr19_B1) (Expr.eval_reg_of_eq hr2_B1) (by omega)) ?_
        (by simp [Expr.size]; omega)
      have hfr_fin : MemFrame mem stB1.mem pA (pA + 1 + ecM * (2 * b + 2)) :=
        memFrame_trans hfrB0 (fun a ha => hfrB1 a (by rcases ha with h1 | h2 <;> [left; right] <;> omega))
      have hfr_after_off : MemFrame st.mem stB1.mem off (off + 2 * b + 2) := by
        have h1 : MemFrame st.mem memA0 off (off + 2 * b + 2) := memFrame_update (by omega) (by omega)
        have h2 : MemFrame memA0 stA1.mem off (off + 2 * b + 2) :=
          fun a ha => hfrA1 a (by rcases ha with h1 | h2 <;> [left; right] <;> omega)
        have h3 : MemFrame stA1.mem memB0 off (off + 2 * b + 2) := memFrame_update (by omega) (by omega)
        have h4 : MemFrame memB0 stB1.mem off (off + 2 * b + 2) :=
          fun a ha => hfrB1 a (by rcases ha with h1 | h2 <;> [left; right] <;> omega)
        exact memFrame_trans h1 (memFrame_trans h2 (memFrame_trans h3 h4))
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; omega,
        fun r h1 h2 h3 h4 h5 h6 h7 => by
          dsimp only; rw [Function.update_of_ne h2, Function.update_of_ne h1, hothB1 r h6 h7]
          dsimp only [stB0]
          rw [Function.update_of_ne h5, Function.update_of_ne h1, Function.update_of_ne h1, hothA1 r h6 h7]
          dsimp only [stA0]
          rw [Function.update_of_ne h5, Function.update_of_ne h1, Function.update_of_ne h4,
            Function.update_of_ne h3]
          exact hoth r h1 h2 h3 h4 h5 h6 h7,
        by rw [hposB1]; exact hposA1.trans hpos, hfr_fin,
        by rw [hfr_after_off pA (Or.inl (by omega))]; exact hmp0, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), hothB1 20 (by decide) (by decide)]
           dsimp only [stB0]
           rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hothA1 20 (by decide) (by decide)]
           dsimp only [stA0]
           rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
      rw [encodePairs_blocks_take_succ hj_len, listAt_append]
      have hlen_prev :
          (((Ec.take j).map fun e => (blockList vs b e.1, blockList vs b e.2)).flatMap encodePair).length =
            j * (2 * b + 2) := by
        have hv_t : ∀ e ∈ Ec.take j, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b :=
          fun e he => hEc_valid e (List.mem_of_mem_take he)
        have hlen_ep := encodePairs_blocks_length hv_t
        unfold encodePairs at hlen_ep
        simp only [List.length_cons, List.length_take, hEc_len] at hlen_ep
        have hmin : min j ecM = j := Nat.min_eq_left (by omega)
        rw [hmin] at hlen_ep
        omega
      refine ⟨?_, ?_⟩
      · intro t ht
        rw [hfr_after_off (pA + 1 + t) (Or.inl (by omega))]
        exact hprev t ht
      · rw [hlen_prev]
        unfold encodePair
        rw [List.cons_append, listAt_cons]
        refine ⟨?_, ?_⟩
        · have h1 : stB1.mem off = memB0 off := hfrB1 off (Or.inl (by omega))
          have h2 : memB0 off = stA1.mem off := Function.update_of_ne (by omega) _ _
          have h3 : stA1.mem off = memA0 off := hfrA1 off (Or.inl (by omega))
          have h4 : memA0 off = b := Function.update_self _ _ _
          have hbl : (blockList vs b ed.1).length = b := blockList_length hed_v.1
          change stB1.mem off = (blockList vs b ed.1).length
          rw [h1, h2, h3, h4, hbl]
        · rw [listAt_append]
          refine ⟨?_, ?_⟩
          · intro t ht
            rw [blockList_length hed_v.1] at ht
            have h1 : stB1.mem (off + 1 + t) = memB0 (off + 1 + t) := hfrB1 _ (Or.inl (by omega))
            have h2 : memB0 (off + 1 + t) = stA1.mem (off + 1 + t) := Function.update_of_ne (by omega) _ _
            change stB1.mem (off + 1 + t) = (blockList vs b ed.1)[t]'(by rw [blockList_length hed_v.1]; exact ht)
            rw [h1, h2]
            exact hlistA1 t (by rw [blockList_length hed_v.1]; exact ht)
          · have hbl1 : (blockList vs b ed.1).length = b := blockList_length hed_v.1
            have hbl2 : (blockList vs b ed.2).length = b := blockList_length hed_v.2
            have hshift : pA + 1 + j * (2 * b + 2) + 1 + (blockList vs b ed.1).length = off + 1 + b := by
              rw [hbl1]
            rw [hshift, listAt_cons]
            refine ⟨?_, ?_⟩
            · rw [hfrB1 (off + 1 + b) (Or.inl (by omega))]
              dsimp only [memB0]
              rw [Function.update_self, hbl2]
            · have hshift2 : off + 1 + b + 1 = off + 2 + b := by omega
              rw [hshift2]; exact hlistB1)
  obtain ⟨o, st', c', hr, hq, hc⟩ := hloop st1 ω rfl
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨_, hcur', hoth', hpos', hfr', hmp0', hlist'⟩
    have hfull : Ec.take ecM = Ec := by rw [← hEc_len, List.take_length]
    rw [hfull] at hlist'
    refine ⟨.normal, st', c', ?_, ⟨hcur', hoth', hpos', hfr', ?_⟩, ?_⟩
    · dsimp only [seqStmts] at hr ⊢
      convert hr using 1
      simp [st1, mem1, hmem]
    · unfold MultiPairsAt encodePairs
      rw [listAt_cons]
      exact ⟨by simp [pairLists, hEc_len, hmp0'], hlist'⟩
    · simp only [Expr.size, Nat.sub_zero] at hc ⊢
      have hmul : ecM * (52 * b + 110 + 1 + 8) = 52 * (ecM * b) + 119 * ecM := by ring
      omega


end MinCostFlow.ExpanderDecomp
