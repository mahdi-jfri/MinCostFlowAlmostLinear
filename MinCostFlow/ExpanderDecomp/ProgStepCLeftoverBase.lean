module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCBase
public import MinCostFlow.ExpanderDecomp.ProgStepCSpec

import Mathlib.Tactic.Linarith

/-!
# Step C Leftover-Injection Helpers and Matched Branch (`ProgStepCLeftoverBase`)

Provides the reusable slice-copy primitive `scCopySliceStmt` / `scCopySlice_triple`, the pure
leftover-pair and space-headroom lemmas (`leftover_validTerminalPairs`,
`stepCLeftoverSpace_headroom`), and the post-router matched-branch statement and execution lemma
(`scLeftoverMatchedStmt` / `scLeftoverMatched_run`) used by `ProgStepCLeftover.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Reusable Slice-Copy Primitive and Matched-Branch Statement (`NoRand`) -/

/-- Copy `rLen` consecutive words from `rSrc` to `rDst` using loop index `rI` and temp `rTmp`. -/
def scCopySliceStmt (rSrc rDst rLen rI rTmp : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rLen) (
    seqStmts [
      .assign rTmp (.load (.bin .add (.reg rSrc) (.reg rI))),
      .store (.bin .add (.reg rDst) (.reg rI)) (.reg rTmp)
    ]
  )

theorem scCopySliceStmt_noRand (rSrc rDst rLen rI rTmp : ℕ) :
    (scCopySliceStmt rSrc rDst rLen rI rTmp).NoRand := by
  simp [scCopySliceStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Post-router matched branch of `stepCLeftoverProc`: marks `matchings.flatten` in `locAddr`,
collects unmatched vertices from `leftoverList` and `fullPrefix`, zips fake edges into `outAddr + 2`,
unmarks `locAddr`, writes `[0, fakeM]` at `outAddr`, and returns `hAfterRt + xLen`. -/
def scLeftoverMatchedStmt : Stmt :=
  seqStmts [
    .assign 17 (.load (.bin .add (.reg 13) (.const 1))),
    .assign 18 (.bin .add (.reg 13) (.const 2)),
    scSetMatchedStmt 17 18 6 19 20 21 1,
    .assign 19 (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 11)),
    .assign 20 (.reg 16),
    scCollectUnmatchedStmt 19 12 6 20 22 23 24,
    .assign 19 (.bin .add (.reg 1) (.const 1)),
    .assign 21 (.bin .add (.reg 16) (.reg 12)),
    scCollectUnmatchedStmt 19 11 6 21 25 23 24,
    .assign 26 (.bin .add (.reg 7) (.const 2)),
    .assign 27 (.const 0),
    scZipAppendStmt 20 22 21 25 26 27 28 29 23 24,
    scSetMatchedStmt 17 18 6 19 20 21 0,
    .store (.reg 7) (.const 0),
    .store (.bin .add (.reg 7) (.const 1)) (.reg 27),
    .ret (.bin .add (.reg 16) (.reg 9))
  ]

theorem scLeftoverMatchedStmt_noRand : scLeftoverMatchedStmt.NoRand := by
  simp [scLeftoverMatchedStmt, scSetMatchedStmt, scCollectUnmatchedStmt, scZipAppendStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 2. Slice-Copy Triple (`scCopySlice_triple`) -/

/-- Triple for `scCopySliceStmt`: copies `xs` (`xs.length = len`) from `srcA` to `dstA`,
preserving memory outside `[dstA, dstA + len)` and registers other than `rI, rTmp`. -/
lemma scCopySlice_triple {w srcA dstA len rSrc rDst rLen rI rTmp : ℕ}
    (hd_regs : [rSrc, rDst, rLen, rI, rTmp].Nodup)
    (p : Program) (mem : ℕ → ℕ) (xs : List ℕ) (st₀ : State)
    (hlen : xs.length = len) (hxs_at : ListAt mem srcA xs)
    (hdisj : DisjointRange dstA len srcA len)
    (hsrc_w : srcA + len < 2 ^ w) (hdst_w : dstA + len < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hrSrc : st₀.regs rSrc = srcA) (hrDst : st₀.regs rDst = dstA) (hrLen : st₀.regs rLen = len)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) (scCopySliceStmt rSrc rDst rLen rI rTmp)
      (normalPost fun st' =>
        (∀ r, r ≠ rI → r ≠ rTmp → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem dstA (dstA + len) ∧
        ListAt st'.mem dstA xs)
      (fun _ => 24 * len + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd_regs
  rcases hd_regs with ⟨⟨_, _, hS_I, hS_T⟩, ⟨_, hD_I, hD_T⟩, ⟨hL_I, hL_T⟩, hI_T, _⟩
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs rI = j ∧
    (∀ r, r ≠ rI → r ≠ rTmp → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame mem st.mem dstA (dstA + len) ∧
    ListAt st.mem dstA (xs.take j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := seqStmts [
      .assign rTmp (.load (.bin .add (.reg rSrc) (.reg rI))),
      .store (.bin .add (.reg rDst) (.reg rI)) (.reg rTmp)])
    (P := fun st => st = st₀) (Inv := Inv) 15 0 len (Nat.zero_le len) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        fun r h1 _ => by dsimp only; rw [Function.update_of_ne h1],
        rfl, hmem ▸ memFrame_refl _ _ _, fun i hi => by simp at hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := len) (by rw [hInv.2.1 rLen hL_I hL_T, hrLen]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hoth, hpos, hfr, hlat⟩
      have hj_len : j < xs.length := hlen.symm ▸ hjlt
      set v := xs[j]'hj_len
      have hrS' : st.regs rSrc = srcA := (hoth rSrc hS_I hS_T).trans hrSrc
      have hrD' : st.regs rDst = dstA := (hoth rDst hD_I hD_T).trans hrDst
      have hsrc_v : st.mem (srcA + j) = v := by
        have hout : srcA + j < dstA ∨ dstA + len ≤ srcA + j := by
          rcases hdisj with h | h <;> [right; left] <;> omega
        rw [hfr _ hout]; exact hxs_at j hj_len
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := v)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrS') (Expr.eval_reg_of_eq hj) (by omega)) hsrc_v) ?_
      refine runs_store_le (x := dstA + j) (v := v)
        (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hD_T, hrD']))
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hI_T, hj])) (by omega))
        (Expr.eval_reg_of_eq (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r h1 h2 => by
          dsimp only; rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hoth r h1 h2,
        hpos, fun a ha => by
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha, ?_⟩,
        by dsimp only; rw [Function.update_of_ne hI_T, hj]⟩
      intro t ht
      have hlen_t : (xs.take (j + 1)).length = j + 1 := by simp [List.length_take]; omega
      rw [hlen_t] at ht
      have hget : (xs.take (j + 1))[t]'(by omega) = xs[t]'(by omega) := List.getElem_take
      rw [hget]; dsimp only
      by_cases htj : t = j
      · subst htj; rw [Function.update_self]
      · rw [Function.update_of_ne (by omega)]
        have ht' : t < (xs.take j).length := by simp [List.length_take]; omega
        simpa [List.getElem_take] using hlat t ht')
  dsimp only [scCopySliceStmt]
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size, Nat.sub_zero]; omega)
  rintro (_ | _) st' hInv
  · rcases hInv with ⟨_, hoth, hpos, hfr, hlat⟩
    rw [← hlen, List.take_length] at hlat
    exact ⟨hoth, hpos, hfr, hlat⟩
  · exact hInv.elim

/-! ## 3. Pure Leftover-Pair Helpers and Matched-Branch Execution -/

lemma leftover_validTerminalPairs {vs : List ℕ} {b : ℕ}
    (hvs_nd : vs.Nodup) (hb : 0 < b) (hmod_pos : 0 < vs.length % b) (hb_le : b ≤ vs.length) :
    ValidTerminalPairs vs.toFinset [(leftoverVerts vs b, fullVerts vs b)] := by
  have hq_pos : 1 ≤ vs.length / b := (Nat.le_div_iff_mul_le hb).mpr (by omega)
  have hfull_len : (fullPrefix vs b).length = (vs.length / b) * b := by
    unfold fullPrefix numFullBlocks
    rw [List.length_take, Nat.min_eq_left (Nat.div_mul_le_self vs.length b)]
  have hleft_len : (leftoverList vs b).length = vs.length % b := by
    unfold leftoverList numFullBlocks
    rw [List.length_drop]
    have hdiv := Nat.div_add_mod vs.length b
    have hmul : (vs.length / b) * b = b * (vs.length / b) := Nat.mul_comm _ _
    omega
  have hleft_nd : (leftoverList vs b).Nodup := hvs_nd.sublist (List.drop_sublist _ _)
  have hfull_nd : (fullPrefix vs b).Nodup := hvs_nd.sublist (List.take_sublist _ _)
  have hleft_card : (leftoverVerts vs b).card = vs.length % b := by
    unfold leftoverVerts; rw [List.toFinset_card_of_nodup hleft_nd, hleft_len]
  have hfull_card : (fullVerts vs b).card = (vs.length / b) * b := by
    unfold fullVerts; rw [List.toFinset_card_of_nodup hfull_nd, hfull_len]
  have hlt_b : vs.length % b < b := Nat.mod_lt _ hb
  have hb_le_full : b ≤ (vs.length / b) * b := by
    have := Nat.mul_le_mul_right b hq_pos; omega
  have hdisj : Disjoint (leftoverVerts vs b) (fullVerts vs b) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    unfold leftoverVerts leftoverList at hv1
    unfold fullVerts fullPrefix at hv2
    rw [List.mem_toFinset] at hv1 hv2
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv2
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hv1
    rw [List.length_take] at hi
    rw [List.length_drop] at hj
    rw [List.getElem_take] at heq
    rw [List.getElem_drop] at heq
    have hnodup := List.pairwise_iff_getElem.mp hvs_nd
    have hmul_le : numFullBlocks vs b * b ≤ vs.length := Nat.div_mul_le_self vs.length b
    have hi1 : i < numFullBlocks vs b * b := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have h1 : i < numFullBlocks vs b * b + j := by omega
    exact hnodup i (numFullBlocks vs b * b + j) (by omega) (by omega) h1 heq.symm
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp
    refine ⟨?_, ?_, by rw [hleft_card, hfull_card]; omega⟩
    · intro v hv; exact List.mem_toFinset.mpr ((List.drop_sublist _ _).subset (List.mem_toFinset.mp hv))
    · intro v hv; exact List.mem_toFinset.mpr ((List.take_sublist _ _).subset (List.mem_toFinset.mp hv))
  · simp [List.pairwise_cons, hdisj]

lemma stepCLeftoverSpace_headroom (C_sp n xLen rcost : ℕ) :
    (3 + xLen) + (2 + 2 * n) + outerRouterSpace C_sp n rcost + xLen ≤
      stepCLeftoverSpace C_sp n xLen (rcost + (xLen + 1)) := by
  unfold outerRouterSpace stepCLeftoverSpace
  have hpow : (n + 3) ^ 4 = n ^ 4 + 12 * n ^ 3 + 54 * n ^ 2 + 108 * n + 81 := by ring
  have h1 : 2 * n + 5 ≤ (n + 3) ^ 4 := by omega
  have h2 : 1 ≤ (n + 3) ^ 4 := by omega
  have h3 : C_sp * (rcost + (n + 3) ^ 4 + 1) ≤
      C_sp * (rcost + (xLen + 1) + 2 * (n + 3) ^ 4 + 20 * (xLen + 1)) :=
    Nat.mul_le_mul_left C_sp (by omega)
  have h4 : (C_sp + 1) * (rcost + (xLen + 1) + 2 * (n + 3) ^ 4 + 20 * (xLen + 1)) =
      C_sp * (rcost + (xLen + 1) + 2 * (n + 3) ^ 4 + 20 * (xLen + 1)) +
      (rcost + (xLen + 1) + 2 * (n + 3) ^ 4 + 20 * (xLen + 1)) := by ring
  omega

/-- Matched-branch execution lemma for `scLeftoverMatchedStmt`. -/
lemma scLeftoverMatched_run {w n xA b locA outA h0 rtOut hAfterRt : ℕ}
    {p : Program} {mem : ℕ → ℕ} {vs : List ℕ} {matchings : List (List (ℕ × ℕ))}
    {st : State} {ω : ℕ → Bool}
    (hvs_at : LenListAt mem xA vs) (hvs_s : vs.Pairwise (· < ·))
    (hvs_sub : vs.toFinset ⊆ Finset.range n) (hb : 0 < b)
    (hmod_pos : 0 < vs.length % b) (hb_le : b ≤ vs.length)
    (hvtp : ValidTerminalPairs vs.toFinset [(leftoverVerts vs b, fullVerts vs b)])
    (hmlen : matchings.length = 1)
    (hpm : IsPartialMatching (leftoverVerts vs b) (fullVerts vs b) (matchings.getD 0 []))
    (hmLen : mem (rtOut + 1) = matchings.flatten.length)
    (hmAt : EdgesAt mem (rtOut + 2) matchings.flatten)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hzf : ZeroFrom mem hAfterRt)
    (hx_h : xA + 1 + vs.length ≤ h0) (hloc_h : locA + n ≤ h0)
    (hout_h : outA + 2 + 2 * vs.length ≤ h0)
    (hd_lx : DisjointRange locA n xA (1 + vs.length))
    (hd_lo : DisjointRange locA n outA (2 + 2 * vs.length))
    (hh_rt : h0 ≤ rtOut) (hrt_after : rtOut + 2 + 2 * n ≤ hAfterRt)
    (hh_w : hAfterRt + vs.length < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr1 : st.regs 1 = xA) (hr6 : st.regs 6 = locA) (hr7 : st.regs 7 = outA)
    (hr9 : st.regs 9 = vs.length) (hr11 : st.regs 11 = (vs.length / b) * b)
    (hr12 : st.regs 12 = vs.length % b) (hr13 : st.regs 13 = rtOut) (hr16 : st.regs 16 = hAfterRt)
    (hmem : st.mem = mem) :
    let fakes := completeBatchFake [(leftoverVerts vs b, fullVerts vs b)] matchings
    ∃ st' cost,
      Runs w p ω scLeftoverMatchedStmt st (.returned (hAfterRt + vs.length)) st' cost ∧
      st'.mem outA = 0 ∧
      st'.mem (outA + 1) = fakes.length ∧
      EdgesAt st'.mem (outA + 2) fakes ∧
      (∀ u < n, st'.mem (locA + u) = 0) ∧
      ZeroFrom st'.mem (hAfterRt + vs.length) ∧
      (∀ a < h0, (a < locA ∨ locA + n ≤ a) → (a < outA ∨ outA + 2 + 2 * vs.length ≤ a) →
        st'.mem a = mem a) ∧
      cost ≤ 240 * vs.length + 220 := by
  intro fakes
  have hvs_nd : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  have hvs_card : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hvs_nd
  have hvs_lt : ∀ u ∈ vs, u < n := fun u hu => Finset.mem_range.mp (hvs_sub (List.mem_toFinset.mpr hu))
  have hfull_len : (fullPrefix vs b).length = (vs.length / b) * b := by
    unfold fullPrefix numFullBlocks
    rw [List.length_take, Nat.min_eq_left (Nat.div_mul_le_self vs.length b)]
  have hleft_len : (leftoverList vs b).length = vs.length % b := by
    unfold leftoverList numFullBlocks
    rw [List.length_drop]
    have := Nat.div_add_mod vs.length b; have := Nat.mul_comm (vs.length / b) b; omega
  have hsum_len : (vs.length / b) * b + vs.length % b = vs.length := by
    have := Nat.div_add_mod vs.length b; have := Nat.mul_comm (vs.length / b) b; omega
  have hpm_all : ∀ j (hj : j < [(leftoverVerts vs b, fullVerts vs b)].length),
      IsPartialMatching ([(leftoverVerts vs b, fullVerts vs b)][j]'hj).1
        ([(leftoverVerts vs b, fullVerts vs b)][j]'hj).2 (matchings.getD j []) := by
    intro j hj; have hj0 : j = 0 := by simp at hj; omega
    subst hj0; exact hpm
  have hflat_b := matched_flatten_bounds hvtp (by simpa using hmlen) hpm_all
  have hflat_len : matchings.flatten.length ≤ vs.length := by have := hflat_b.2; omega
  have hflat_lt : ∀ e ∈ matchings.flatten, e.1 < n ∧ e.2 < n := fun e he =>
    ⟨Finset.mem_range.mp (hvs_sub (hflat_b.1 e he).1),
     Finset.mem_range.mp (hvs_sub (hflat_b.1 e he).2)⟩
  have hflat_le_n : matchings.flatten.length ≤ n := by
    have : vs.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card hvs_sub
    rw [Finset.card_range] at this; omega
  set mE := matchings.flatten.length
  set fullLen := (vs.length / b) * b
  set leftLen := vs.length % b
  suffices h : ∃ o st' cost, Runs w p ω scLeftoverMatchedStmt st o st' cost ∧
      (o = .returned (hAfterRt + vs.length) ∧
        st'.mem outA = 0 ∧ st'.mem (outA + 1) = fakes.length ∧ EdgesAt st'.mem (outA + 2) fakes ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧ ZeroFrom st'.mem (hAfterRt + vs.length) ∧
        (∀ a < h0, (a < locA ∨ locA + n ≤ a) → (a < outA ∨ outA + 2 + 2 * vs.length ≤ a) →
          st'.mem a = mem a)) ∧
      cost ≤ 240 * vs.length + 220 by
    rcases h with ⟨o, st', cost, hr, ⟨rfl, h1, h2, h3, h4, h5, h6⟩, hc⟩
    exact ⟨st', cost, hr, h1, h2, h3, h4, h5, h6, hc⟩
  refine runs_start_le ?_
  dsimp only [scLeftoverMatchedStmt, seqStmts]
  refine runs_seq_assign_le (v := mE)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr13) (Expr.eval_const (by omega)) (by omega))
      (hmem ▸ hmLen)) ?_
  refine runs_seq_assign_le (v := rtOut + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr13]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  let st1 : State :=
    { mem := st.mem, regs := Function.update (Function.update st.regs 17 mE) 18 (rtOut + 2), pos := st.pos }
  refine runs_seq_triple_le
    (scSetMatched_triple (la := locA) (rM := 17) (rEdges := 18) (rLoc := 6) (rI := 19) (rU := 20)
      (rV := 21) (val := 1) (by decide) p mem matchings.flatten st1 rfl hmAt hflat_lt
      (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st1]; rw [Function.update_self])
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr6])
      hmem) rfl ?_
  intro st2 ⟨hoth2, _, hfr2, hloc2⟩
  have hst2_lt17 : ∀ r < 17, st2.regs r = st.regs r := fun r hr => by
    rw [hoth2 r (by omega) (by omega) (by omega)]
    dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hr17_2 : st2.regs 17 = mE := by
    rw [hoth2 17 (by decide) (by decide) (by decide)]
    dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr18_2 : st2.regs 18 = rtOut + 2 := by
    rw [hoth2 18 (by decide) (by decide) (by decide)]
    dsimp only [st1]; rw [Function.update_self]
  have hloc2_ex : ∀ u < n, st2.mem (locA + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 :=
    fun u hu => by rw [hloc2 u hu, hloc0 u hu]
  have hleft_at2 : ListAt st2.mem (xA + 1 + fullLen) (leftoverList vs b) := fun i hi => by
    have hdisj : xA + 1 + fullLen + i < locA ∨ locA + n ≤ xA + 1 + fullLen + i := by
      rcases hd_lx with h | h <;> [right; left] <;> omega
    rw [hfr2 _ hdisj]
    have hshift : xA + 1 + fullLen + i = (xA + 1) + (fullLen + i) := by omega
    rw [hshift]
    have hget : (leftoverList vs b)[i]'hi = vs[fullLen + i]'(by omega) := by
      simp [leftoverList, numFullBlocks, fullLen]
    rw [hget]; exact hvs_at.2 (fullLen + i) (by omega)
  have hfull_at2 : ListAt st2.mem (xA + 1) (fullPrefix vs b) := fun i hi => by
    have hdisj : xA + 1 + i < locA ∨ locA + n ≤ xA + 1 + i := by
      rcases hd_lx with h | h <;> [right; left] <;> omega
    rw [hfr2 _ hdisj]
    have hget : (fullPrefix vs b)[i]'hi = vs[i]'(by omega) := by simp [fullPrefix, numFullBlocks]
    rw [hget]; exact hvs_at.2 i (by omega)
  refine runs_seq_assign_le (v := xA + 1 + fullLen)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hst2_lt17 1 (by decide)).trans hr1))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq ((hst2_lt17 11 (by decide)).trans hr11)) (by omega)) ?_
  refine runs_seq_assign_le (v := hAfterRt)
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst2_lt17 16 (by decide), hr16])) ?_
  let st3 : State :=
    { mem := st2.mem, regs := Function.update (Function.update st2.regs 19 (xA + 1 + fullLen)) 20 hAfterRt, pos := st2.pos }
  refine runs_seq_triple_le
    (scCollectUnmatched_triple (sa := xA + 1 + fullLen) (len := leftLen) (la := locA) (da := hAfterRt)
      (rSrc := 19) (rLen := 12) (rLoc := 6) (rDst := 20) (rCnt := 22) (rI := 23) (rU := 24)
      (by decide) p st2.mem (leftoverList vs b) (matchedVerts matchings.flatten) st3
      hleft_len hleft_at2 (fun u hu => hvs_lt u ((List.drop_sublist _ _).subset hu)) hloc2_ex
      (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt17 12 (by decide), hr12])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt17 6 (by decide), hr6])
      (by dsimp only [st3]; rw [Function.update_self]) rfl) rfl ?_
  intro st4 ⟨hcntA, hoth4, _, hfr4, hunmA_at⟩
  set unmA := (leftoverList vs b).filter (fun u => decide (u ∉ matchedVerts matchings.flatten))
  have hunmA_le : unmA.length ≤ leftLen := le_trans (List.length_filter_le _ _) hleft_len.le
  have hst4_lt19 : ∀ r < 19, st4.regs r = st2.regs r := fun r hr => by
    rw [hoth4 r (by omega) (by omega) (by omega)]
    dsimp only [st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hr20_4 : st4.regs 20 = hAfterRt := by
    rw [hoth4 20 (by decide) (by decide) (by decide)]; dsimp only [st3]; rw [Function.update_self]
  refine runs_seq_assign_le (v := xA + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hst4_lt19 1 (by decide)).trans ((hst2_lt17 1 (by decide)).trans hr1)))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := hAfterRt + leftLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst4_lt19 16 (by decide), hst2_lt17 16 (by decide), hr16]))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst4_lt19 12 (by decide), hst2_lt17 12 (by decide), hr12]))
      (by omega)) ?_
  let st5 : State :=
    { mem := st4.mem, regs := Function.update (Function.update st4.regs 19 (xA + 1)) 21 (hAfterRt + leftLen), pos := st4.pos }
  have hfull_at4 : ListAt st4.mem (xA + 1) (fullPrefix vs b) := fun i hi => by
    rw [hfr4 _ (Or.inl (by omega))]; exact hfull_at2 i hi
  have hloc4_ex : ∀ u < n, st4.mem (locA + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 :=
    fun u hu => by rw [hfr4 _ (Or.inl (by omega))]; exact hloc2_ex u hu
  refine runs_seq_triple_le
    (scCollectUnmatched_triple (sa := xA + 1) (len := fullLen) (la := locA) (da := hAfterRt + leftLen)
      (rSrc := 19) (rLen := 11) (rLoc := 6) (rDst := 21) (rCnt := 25) (rI := 23) (rU := 24)
      (by decide) p st4.mem (fullPrefix vs b) (matchedVerts matchings.flatten) st5
      hfull_len hfull_at4 (fun u hu => hvs_lt u ((List.take_sublist _ _).subset hu)) hloc4_ex
      (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst4_lt19 11 (by decide), hst2_lt17 11 (by decide), hr11])
      (by dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst4_lt19 6 (by decide), hst2_lt17 6 (by decide), hr6])
      (by dsimp only [st5]; rw [Function.update_self]) rfl) rfl ?_
  intro st6 ⟨hcntB, hoth6, _, hfr6, hunmB_at⟩
  set unmB := (fullPrefix vs b).filter (fun u => decide (u ∉ matchedVerts matchings.flatten))
  have hunmB_le : unmB.length ≤ fullLen := le_trans (List.length_filter_le _ _) hfull_len.le
  have hst6_lt19 : ∀ r < 19, st6.regs r = st2.regs r := fun r hr => by
    rw [hoth6 r (by omega) (by omega) (by omega)]
    dsimp only [st5]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst4_lt19 r hr]
  have hr20_6 : st6.regs 20 = hAfterRt := by
    rw [hoth6 20 (by decide) (by decide) (by decide)]
    dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr20_4]
  have hr21_6 : st6.regs 21 = hAfterRt + leftLen := by
    rw [hoth6 21 (by decide) (by decide) (by decide)]; dsimp only [st5]; rw [Function.update_self]
  have hr22_6 : st6.regs 22 = unmA.length := by
    rw [hoth6 22 (by decide) (by decide) (by decide)]
    dsimp only [st5]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcntA]
  refine runs_seq_assign_le (v := outA + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hst6_lt19 7 (by decide)).trans ((hst2_lt17 7 (by decide)).trans hr7)))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st7 : State :=
    { mem := st6.mem, regs := Function.update (Function.update st6.regs 26 (outA + 2)) 27 0, pos := st6.pos }
  have hunmA_at6 : ListAt st6.mem hAfterRt unmA := fun i hi => by
    rw [hfr6 _ (Or.inl (by omega))]; exact hunmA_at i hi
  refine runs_seq_triple_le
    (scZipAppend_triple (ua := hAfterRt) (ub := hAfterRt + leftLen) (outA := outA + 2) (prevM := 0)
      (cap := vs.length) (rUnmA := 20) (rCntA := 22) (rUnmB := 21) (rCntB := 25) (rOutEdges := 26)
      (rOutM := 27) (rLim := 28) (rI := 29) (rU := 23) (rV := 24)
      (by decide) p st6.mem unmA unmB [] st7 rfl rfl rfl hunmA_at6 hunmB_at
      (fun j hj => by simp at hj) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr20_6])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr22_6])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr21_6])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcntB])
      (by dsimp only [st7]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st7]; rw [Function.update_self]) rfl) rfl ?_
  intro st8 ⟨hr27_8, hoth8, _, hfr8, hE8⟩
  have hcmf_eq : fakes = unmA.zip unmB := by
    have h1 := completeMatchingFake_eq_of_flat (X := vs.toFinset) hvtp (by simpa using hmlen) hpm_all
      (j := 0) (by simp) (pairwise_lt_leftoverList hvs_s b) (pairwise_lt_fullPrefix hvs_s b) rfl rfl
    cases matchings with
    | nil => simp at hmlen
    | cons m0 ms =>
      have hms : ms = [] := by simpa using hmlen
      subst hms
      simpa [fakes, completeBatchFake, unmA, unmB] using h1
  have hst8_lt19 : ∀ r < 19, st8.regs r = st2.regs r := fun r hr => by
    rw [hoth8 r (by omega) (by omega) (by omega) (by omega) (by omega)]
    dsimp only [st7]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst6_lt19 r hr]
  have hmAt_8 : EdgesAt st8.mem (rtOut + 2) matchings.flatten := fun j hj => by
    have h1 : st8.mem (rtOut + 2 + 2 * j) = mem (rtOut + 2 + 2 * j) := by
      rw [hfr8 _ (Or.inr (by omega)), hfr6 _ (Or.inl (by omega)), hfr4 _ (Or.inl (by omega)),
        hfr2 _ (Or.inr (by omega))]
    have h2 : st8.mem (rtOut + 2 + 2 * j + 1) = mem (rtOut + 2 + 2 * j + 1) := by
      rw [hfr8 _ (Or.inr (by omega)), hfr6 _ (Or.inl (by omega)), hfr4 _ (Or.inl (by omega)),
        hfr2 _ (Or.inr (by omega))]
    rw [h1, h2]; exact hmAt j hj
  refine runs_seq_triple_le
    (scSetMatched_triple (la := locA) (rM := 17) (rEdges := 18) (rLoc := 6) (rI := 19) (rU := 20)
      (rV := 21) (val := 0) (by decide) p st8.mem matchings.flatten st8 rfl hmAt_8 hflat_lt
      (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      ((hst8_lt19 17 (by decide)).trans hr17_2) ((hst8_lt19 18 (by decide)).trans hr18_2)
      ((hst8_lt19 6 (by decide)).trans ((hst2_lt17 6 (by decide)).trans hr6)) rfl) rfl ?_
  intro st9 ⟨hoth9, _, hfr9, hloc9⟩
  have hr7_9 : st9.regs 7 = outA :=
    (hoth9 7 (by decide) (by decide) (by decide)).trans ((hst8_lt19 7 (by decide)).trans ((hst2_lt17 7 (by decide)).trans hr7))
  have hr9_9 : st9.regs 9 = vs.length :=
    (hoth9 9 (by decide) (by decide) (by decide)).trans ((hst8_lt19 9 (by decide)).trans ((hst2_lt17 9 (by decide)).trans hr9))
  have hr16_9 : st9.regs 16 = hAfterRt :=
    (hoth9 16 (by decide) (by decide) (by decide)).trans ((hst8_lt19 16 (by decide)).trans ((hst2_lt17 16 (by decide)).trans hr16))
  have hr27_9 : st9.regs 27 = fakes.length := by
    rw [hoth9 27 (by decide) (by decide) (by decide), hr27_8, hcmf_eq, List.length_zip]; omega
  refine runs_seq_store_le (x := outA) (v := 0)
    (Expr.eval_reg_of_eq hr7_9) (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := outA + 1) (v := fakes.length)
    (Expr.eval_add (Expr.eval_reg_of_eq hr7_9) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq hr27_9) ?_
  refine runs_ret_le (v := hAfterRt + vs.length)
    (Expr.eval_add (Expr.eval_reg_of_eq hr16_9) (Expr.eval_reg_of_eq hr9_9) (by omega)) ?_
    (by have hmin : min unmA.length unmB.length ≤ leftLen := le_trans (Nat.min_le_left _ _) hunmA_le
        simp only [Expr.size]; omega)
  refine ⟨rfl, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj_len : j < vs.length := by
      have : fakes.length ≤ leftLen := by rw [hcmf_eq, List.length_zip]; omega
      omega
    have hdisj1 : outA + 2 + 2 * j < locA ∨ locA + n ≤ outA + 2 + 2 * j := by
      rcases hd_lo with h | h <;> [right; left] <;> omega
    have hdisj2 : outA + 2 + 2 * j + 1 < locA ∨ locA + n ≤ outA + 2 + 2 * j + 1 := by
      rcases hd_lo with h | h <;> [right; left] <;> omega
    have hne1 : outA + 2 + 2 * j ≠ outA + 1 := by omega
    have hne2 : outA + 2 + 2 * j ≠ outA := by omega
    have hne3 : outA + 2 + 2 * j + 1 ≠ outA + 1 := by omega
    have hne4 : outA + 2 + 2 * j + 1 ≠ outA := by omega
    dsimp only
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2, hfr9 _ hdisj1,
      Function.update_of_ne hne3, Function.update_of_ne hne4, hfr9 _ hdisj2]
    simp only [List.nil_append] at hE8
    rw [← hcmf_eq] at hE8
    exact hE8 j hj
  · intro u hu
    have hne1 : locA + u ≠ outA + 1 := by rcases hd_lo with h | h <;> omega
    have hne2 : locA + u ≠ outA := by rcases hd_lo with h | h <;> omega
    dsimp only; rw [Function.update_of_ne hne1, Function.update_of_ne hne2, hloc9 u hu]
    split_ifs with hm
    · rfl
    · have hdisj_lo : locA + u < outA + 2 ∨ outA + 2 + 2 * vs.length ≤ locA + u := by
        rcases hd_lo with h | h <;> [left; right] <;> omega
      rw [hfr8 _ hdisj_lo, hfr6 _ (Or.inl (by omega)), hfr4 _ (Or.inl (by omega)), hloc2_ex u hu]
      simp [hm]
  · intro a ha
    have hne1 : a ≠ outA + 1 := by omega
    have hne2 : a ≠ outA := by omega
    dsimp only
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
      hfr9 a (Or.inr (by omega)), hfr8 a (Or.inr (by omega)),
      hfr6 a (Or.inr (by omega)), hfr4 a (Or.inr (by omega)), hfr2 a (Or.inr (by omega))]
    exact hzf a (by omega)
  · intro a ha_h ha_loc ha_out
    have hne1 : a ≠ outA + 1 := by rcases ha_out with h | h <;> omega
    have hne2 : a ≠ outA := by rcases ha_out with h | h <;> omega
    have ha_out2 : a < outA + 2 ∨ outA + 2 + 2 * vs.length ≤ a := by rcases ha_out with h | h <;> [left; right] <;> omega
    dsimp only
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
      hfr9 a ha_loc, hfr8 a ha_out2, hfr6 a (Or.inl (by omega)), hfr4 a (Or.inl (by omega)), hfr2 a ha_loc]

end MinCostFlow.ExpanderDecomp
