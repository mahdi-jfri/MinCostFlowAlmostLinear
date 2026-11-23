module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBPost

import Mathlib.Tactic.Linarith

/-!
# Step B Matched-Branch Combined Post-Handler (`ProgStepBMatched`)

Combines `sbScatterStmt` (`ProgStepBScatter.lean`), `scSetMatchedStmt` (`ProgStepCBase.lean`),
and `sbCompleteCutLoopStmt` (`ProgStepBPost.lean`) into `sbMatchedPostStmt`, restoring `locAddr`
to all zeros on exit.

Main results:
- `sbMatchedPostStmt`, `sbMatchedPostStmt_noRand`
- `sbMatchedPost_triple`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Full Matched-Branch Post-Processing (`sbMatchedPostStmt`) -/

/-- Full matched-branch handler for one Step B round: scatters `matchings.flatten` into `W_i`,
marks `matchings.flatten` in `locAddr`, completes fake edges into both `fAddr` and `W_i`, and
unmarks `locAddr` back to all zeros. Modifies only `r14` and `r30..r45`. -/
def sbMatchedPostStmt : Stmt :=
  seqStmts [
    sbScatterStmt,
    .assign 44 (.load (.bin .add (.reg 27) (.const 1))),
    .assign 45 (.bin .add (.reg 27) (.const 2)),
    scSetMatchedStmt 44 45 8 41 42 43 1,
    sbCompleteCutLoopStmt,
    scSetMatchedStmt 44 45 8 41 42 43 0
  ]

theorem sbMatchedPostStmt_noRand : sbMatchedPostStmt.NoRand := by
  simp [sbMatchedPostStmt, sbScatterStmt, sbMarkListStmt, scSetMatchedStmt,
    sbCompleteCutLoopStmt, scCollectUnmatchedStmt, sbZipDualStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Combined triple for `sbMatchedPostStmt`. -/
theorem sbMatchedPost_triple
    {w n b t k locA fA prevF cutRecsA tmpA rtOutA wBaseA wStride nBlocks maxR : ℕ}
    {p : Program} {mem : ℕ → ℕ} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {matchings : List (List (ℕ × ℕ))}
    {cutIds : List ℕ} {cPrimeAddrs compAddrs : List ℕ}
    {cPrimeLists compLists : List (List ℕ)}
    {prevFEs : List (ℕ × ℕ)} {prevEdges : ℕ → List (ℕ × ℕ)} {st₀ : State}
    (ht_len : pairs.length = t) (hcut_len : cutIds.length = t)
    (hcpa_len : cPrimeAddrs.length = t) (hcoa_len : compAddrs.length = t)
    (hcpl_len : cPrimeLists.length = t) (hcol_len : compLists.length = t)
    (hcut_nd : cutIds.Nodup) (hcut_lt : ∀ i ∈ cutIds, i < nBlocks)
    (hX_sub : X ⊆ Finset.range n) (hvtp : ValidTerminalPairs X pairs)
    (hmlen : matchings.length = t)
    (hpm : ∀ idx (hidx : idx < t),
      IsPartialMatching (pairs[idx]'(ht_len.symm ▸ hidx)).1
        (pairs[idx]'(ht_len.symm ▸ hidx)).2 (matchings.getD idx []))
    (hrec_w : ∀ idx (hidx : idx < t),
      mem (cutRecsA + 3 * idx) = wBaseA + (cutIds[idx]'(hcut_len.symm ▸ hidx)) * wStride)
    (hrec_c : ∀ idx (hidx : idx < t),
      mem (cutRecsA + 3 * idx + 1) = cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx))
    (hrec_o : ∀ idx (hidx : idx < t),
      mem (cutRecsA + 3 * idx + 2) = compAddrs[idx]'(hcoa_len.symm ▸ hidx))
    (hlists_spec : ∀ idx (hidx : idx < t),
      let cL := cPrimeLists[idx]'(hcpl_len.symm ▸ hidx)
      let oL := compLists[idx]'(hcol_len.symm ▸ hidx)
      let cA := cPrimeAddrs[idx]'(hcpa_len.symm ▸ hidx)
      let oA := compAddrs[idx]'(hcoa_len.symm ▸ hidx)
      cL.length = b / 2 ∧ cL.Pairwise (· < ·) ∧ cL.toFinset = (pairs[idx]'(ht_len.symm ▸ hidx)).1 ∧
      ListAt mem cA cL ∧ DisjointRange locA n cA (b / 2) ∧ DisjointRange tmpA (2 * b) cA (b / 2) ∧
      DisjointRange fA (2 * k) cA (b / 2) ∧ DisjointRange wBaseA (nBlocks * wStride) cA (b / 2) ∧
      cA + b / 2 < 2 ^ w ∧
      oL.length = b / 2 ∧ oL.Pairwise (· < ·) ∧ oL.toFinset = (pairs[idx]'(ht_len.symm ▸ hidx)).2 ∧
      ListAt mem oA oL ∧ DisjointRange locA n oA (b / 2) ∧ DisjointRange tmpA (2 * b) oA (b / 2) ∧
      DisjointRange fA (2 * k) oA (b / 2) ∧ DisjointRange wBaseA (nBlocks * wStride) oA (b / 2) ∧
      oA + b / 2 < 2 ^ w)
    (hFlen : prevFEs.length = prevF) (hF_at : EdgesAt mem fA prevFEs)
    (hF_cap : prevF + (completeBatchFake pairs matchings).length ≤ k)
    (hwStride_eq : wStride = 2 + 2 * maxR * (b / 2))
    (hprev_W : ∀ i < nBlocks, GraphAt mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i)))
    (hprev_len_all : ∀ i < nBlocks, (prevEdges i).length ≤ maxR * (b / 2))
    (hprev_cap : ∀ idx (hidx : idx < t),
      let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
      let p_i := pairs[idx]'(ht_len.symm ▸ hidx)
      (prevEdges i).length + (matchings.getD idx []).length +
        (completeMatchingFake p_i.1 p_i.2 (matchings.getD idx [])).length ≤ maxR * (b / 2))
    (hmLen : mem (rtOutA + 1) = matchings.flatten.length)
    (hmAt : EdgesAt mem (rtOutA + 2) matchings.flatten)
    (hloc0 : ∀ u < n, mem (locA + u) = 0)
    (hd_loc_rec : DisjointRange locA n cutRecsA (3 * t))
    (hd_loc_rt : DisjointRange locA n rtOutA (2 + 2 * matchings.flatten.length))
    (hd_loc_w : DisjointRange locA n wBaseA (nBlocks * wStride))
    (hd_loc_tmp : DisjointRange locA n tmpA (2 * b))
    (hd_loc_f : DisjointRange locA n fA (2 * k))
    (hd_w_rec : DisjointRange wBaseA (nBlocks * wStride) cutRecsA (3 * t))
    (hd_w_rt : DisjointRange wBaseA (nBlocks * wStride) rtOutA (2 + 2 * matchings.flatten.length))
    (hd_w_tmp : DisjointRange wBaseA (nBlocks * wStride) tmpA (2 * b))
    (hd_w_f : DisjointRange wBaseA (nBlocks * wStride) fA (2 * k))
    (hd_tmp_rec : DisjointRange tmpA (2 * b) cutRecsA (3 * t))
    (hd_tmp_rt : DisjointRange tmpA (2 * b) rtOutA (2 + 2 * matchings.flatten.length))
    (hd_tmp_f : DisjointRange tmpA (2 * b) fA (2 * k))
    (hd_f_rec : DisjointRange fA (2 * k) cutRecsA (3 * t))
    (hd_f_rt : DisjointRange fA (2 * k) rtOutA (2 + 2 * matchings.flatten.length))
    (hloc_w : locA + n < 2 ^ w) (hrec_w_bnd : cutRecsA + 3 * t < 2 ^ w)
    (hrt_w : rtOutA + 2 + 2 * matchings.flatten.length < 2 ^ w)
    (htmp_w : tmpA + 2 * b < 2 ^ w) (hf_w : fA + 2 * k < 2 ^ w)
    (hw_w : wBaseA + nBlocks * wStride < 2 ^ w) (ht_w : t + 1 < 2 ^ w)
    (hb_w : b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA) (hr9 : st₀.regs 9 = fA)
    (hr14 : st₀.regs 14 = prevF) (hr22 : st₀.regs 22 = cutRecsA)
    (hr24 : st₀.regs 24 = tmpA) (hr25 : st₀.regs 25 = t) (hr27 : st₀.regs 27 = rtOutA)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbMatchedPostStmt
      (normalPost fun st' =>
        st'.regs 14 = prevF + (completeBatchFake pairs matchings).length ∧
        (∀ r < 30, r ≠ 14 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA ∨ tmpA + 2 * b ≤ a) →
          (a < fA ∨ fA + 2 * k ≤ a) → (a < wBaseA ∨ wBaseA + nBlocks * wStride ≤ a) →
          st'.mem a = mem a) ∧
        EdgesAt st'.mem fA (prevFEs ++ completeBatchFake pairs matchings) ∧
        (∀ idx (hidx : idx < t),
          let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
          let p_i := pairs[idx]'(ht_len.symm ▸ hidx)
          GraphAt st'.mem (wBaseA + i * wStride)
            (Graph.mk n (prevEdges i ++ (matchings.getD idx [] ++ completeMatchingFake p_i.1 p_i.2 (matchings.getD idx []))))) ∧
        (∀ i < nBlocks, i ∉ cutIds →
          GraphAt st'.mem (wBaseA + i * wStride) (Graph.mk n (prevEdges i))))
      (fun _ => 220 * t * (b / 2) + 350 * t + 220 * matchings.flatten.length + 260) := by
  have hwS2 : wStride = 2 + 2 * (maxR * (b / 2)) := by rw [hwStride_eq]; ring
  have hslot_lt : ∀ i < nBlocks, ∀ off < wStride, wBaseA + i * wStride + off < wBaseA + nBlocks * wStride := by
    intro i hi off hoff
    have h1 : (i + 1) * wStride ≤ nBlocks * wStride := Nat.mul_le_mul_right wStride hi
    have h2 : (i + 1) * wStride = i * wStride + wStride := by ring
    omega
  have hflat_lt : ∀ e ∈ matchings.flatten, e.1 < n ∧ e.2 < n := by
    have hb := matched_flatten_bounds hvtp (hmlen.trans ht_len.symm) (fun idx hidx => hpm idx (ht_len ▸ hidx))
    intro e he
    exact ⟨Finset.mem_range.mp (hX_sub (hb.1 e he).1), Finset.mem_range.mp (hX_sub (hb.1 e he).2)⟩
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbMatchedPostStmt, seqStmts]
  refine runs_seq_triple_le
    (sbScatter_triple ht_len hcut_len hcpa_len hcpl_len hcut_nd hcut_lt hX_sub hvtp hmlen hpm
      hrec_w hrec_c (fun idx hidx => by
        have h := hlists_spec idx hidx
        exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩)
      hwStride_eq hprev_W hprev_len_all (fun idx hidx => by have := hprev_cap idx hidx; omega)
      hmLen hmAt hloc0 hd_loc_rec hd_loc_rt hd_loc_w hd_w_rec hd_w_rt
      hloc_w hrec_w_bnd hrt_w hw_w ht_w hb_w hw16 hr4 hr8 hr22 hr25 hr27 hmem) rfl ?_
  intro st1 ⟨hoth1, hpos1, hloc0_1, hfr1, hWcut1, hWnon1⟩
  have hmLen1 : st1.mem (rtOutA + 1) = matchings.flatten.length := by
    rw [hfr1 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)
      (by rcases hd_w_rt with h | h <;> [right; left] <;> omega)]; exact hmLen
  have hmAt1 : EdgesAt st1.mem (rtOutA + 2) matchings.flatten := fun q hq => by
    rw [hfr1 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_w_rt with h | h <;> [right; left] <;> omega),
      hfr1 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_w_rt with h | h <;> [right; left] <;> omega)]
    exact hmAt q hq
  refine runs_seq_assign_le (v := matchings.flatten.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth1 27 (by decide)).trans hr27))
      (Expr.eval_const (w := w) (by omega)) (by omega)) hmLen1) ?_
  refine runs_seq_assign_le (v := rtOutA + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth1 27 (by decide), hr27]))
      (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  let st2 : State :=
    { mem := st1.mem,
      regs := Function.update (Function.update st1.regs 44 matchings.flatten.length) 45 (rtOutA + 2),
      pos := st1.pos }
  refine runs_seq_triple_le
    (scSetMatched_triple (w := w) (n := n) (mE := matchings.flatten.length) (ea := rtOutA + 2) (la := locA)
      (rM := 44) (rEdges := 45) (rLoc := 8) (rI := 41) (rU := 42) (rV := 43) (val := 1)
      (by decide) p st1.mem matchings.flatten st2 rfl hmAt1 hflat_lt
      (by rcases hd_loc_rt with h | h <;> [left; right] <;> omega) (by omega) hloc_w (by omega) hw16
      (by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st2]; rw [Function.update_self])
      (by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth1 8 (by decide), hr8])
      rfl) rfl ?_
  intro st3 ⟨hoth3, hpos3, hfr3, hloc3⟩
  -- Define `curWEdges` after scatter
  let curWEdges : ℕ → List (ℕ × ℕ) := fun i =>
    match cutIds.findIdx? (fun j => decide (j = i)) with
    | none => prevEdges i
    | some idx => prevEdges i ++ matchings.getD idx []
  have hfind_cut : ∀ idx (hidx : idx < t), cutIds.findIdx? (fun j => decide (j = cutIds[idx]'(hcut_len.symm ▸ hidx))) = some idx := by
    intro idx hidx
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hcut_len.symm ▸ hidx, by simp, fun q hq => ?_⟩
    simp only [decide_eq_true_eq]
    intro heq
    exact Nat.ne_of_lt hq ((List.Nodup.getElem_inj_iff hcut_nd).mp heq)
  have hcur_cut : ∀ idx (hidx : idx < t),
      curWEdges (cutIds[idx]'(hcut_len.symm ▸ hidx)) = prevEdges (cutIds[idx]'(hcut_len.symm ▸ hidx)) ++ matchings.getD idx [] := by
    intro idx hidx; dsimp only [curWEdges]; rw [hfind_cut idx hidx]
  have hcur_non : ∀ i, i ∉ cutIds → curWEdges i = prevEdges i := by
    intro i hnotin; dsimp only [curWEdges]
    cases h : cutIds.findIdx? (fun j => decide (j = i)) with
    | none => rfl
    | some idx =>
      have hget := (List.findIdx?_eq_some_iff_getElem.mp h).2.1
      simp only [decide_eq_true_eq] at hget
      exact absurd (hget ▸ List.getElem_mem (List.findIdx?_eq_some_iff_getElem.mp h).1) hnotin
  have hW_len_cur : ∀ i < nBlocks, (curWEdges i).length ≤ maxR * (b / 2) := by
    intro i hi
    by_cases hmem_i : i ∈ cutIds
    · obtain ⟨idx, hidx_c, rfl⟩ := List.mem_iff_getElem.mp hmem_i
      have hidx : idx < t := hcut_len ▸ hidx_c
      rw [hcur_cut idx hidx, List.length_append]
      have := hprev_cap idx hidx; omega
    · rw [hcur_non i hmem_i]; exact hprev_len_all i hi
  have hW_at3 : ∀ i < nBlocks, GraphAt st3.mem (wBaseA + i * wStride) (Graph.mk n (curWEdges i)) := by
    intro i hi
    have hW1 : GraphAt st1.mem (wBaseA + i * wStride) (Graph.mk n (curWEdges i)) := by
      by_cases hmem_i : i ∈ cutIds
      · obtain ⟨idx, hidx_c, rfl⟩ := List.mem_iff_getElem.mp hmem_i
        have hidx : idx < t := hcut_len ▸ hidx_c
        rw [hcur_cut idx hidx]; exact hWcut1 idx hidx
      · rw [hcur_non i hmem_i]; exact hWnon1 i hi hmem_i
    have hWg := graphAt_mk_iff.mp hW1
    have hlen_i := hW_len_cur i hi
    refine graphAt_mk_iff.mpr ⟨by rw [hfr3 _ (by have := hslot_lt i hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.1,
      by rw [hfr3 _ (by have := hslot_lt i hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.2.1,
      fun q hq => by
        have h1 := hslot_lt i hi (2 + 2 * q) (by omega)
        have h2 := hslot_lt i hi (2 + 2 * q + 1) (by omega)
        rw [hfr3 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
          hfr3 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
        exact hWg.2.2 q hq⟩
  have hst3_lt30 : ∀ r < 30, st3.regs r = st₀.regs r := fun r hr => by
    rw [hoth3 r (by omega) (by omega) (by omega)]; dsimp only [st2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth1 r hr]
  have hfr3_all : ∀ a, (a < locA ∨ locA + n ≤ a) → (a < wBaseA ∨ wBaseA + nBlocks * wStride ≤ a) → st3.mem a = mem a :=
    fun a hl hw => (hfr3 a hl).trans (hfr1 a hl hw)
  refine runs_seq_triple_le
    (sbCompleteCutLoop_triple ht_len hcut_len hcpa_len hcoa_len hcpl_len hcol_len hcut_nd hcut_lt
      hX_sub hvtp hmlen hpm
      (fun idx hidx => by rw [hfr3_all _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega) (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]; exact hrec_w idx hidx)
      (fun idx hidx => by rw [hfr3_all _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega) (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]; exact hrec_c idx hidx)
      (fun idx hidx => by rw [hfr3_all _ (by rcases hd_loc_rec with h | h <;> [right; left] <;> omega) (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]; exact hrec_o idx hidx)
      (fun idx hidx => by
        have h := hlists_spec idx hidx
        refine ⟨h.1, h.2.1, h.2.2.1, fun q hq => by
            rw [hfr3_all _ (by rcases h.2.2.2.2.1 with hh | hh <;> [right; left] <;> omega)
              (by rcases h.2.2.2.2.2.2.2.1 with hh | hh <;> [right; left] <;> omega)]
            exact h.2.2.2.1 q hq,
          h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, fun q hq => by
            rw [hfr3_all _ (by rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hh | hh <;> [right; left] <;> omega)
              (by rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hh | hh <;> [right; left] <;> omega)]
            exact h.2.2.2.2.2.2.2.2.2.2.2.2.1 q hq,
          h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
      hFlen (fun q hq => by
        rw [hfr3_all _ (by rcases hd_loc_f with h | h <;> [right; left] <;> omega) (by rcases hd_w_f with h | h <;> [right; left] <;> omega),
          hfr3_all _ (by rcases hd_loc_f with h | h <;> [right; left] <;> omega) (by rcases hd_w_f with h | h <;> [right; left] <;> omega)]
        exact hF_at q hq)
      hF_cap hwStride_eq hW_at3 hW_len_cur
      (fun idx hidx => by dsimp only; rw [hcur_cut idx hidx, List.length_append]; exact hprev_cap idx hidx)
      (fun u hu => by rw [hloc3 u hu, hloc0_1 u hu])
      (Or.symm hd_loc_tmp) hd_tmp_rec hd_tmp_f (Or.symm hd_w_tmp)
      (Or.symm hd_loc_f) hd_f_rec (Or.symm hd_w_f)
      (Or.symm hd_loc_w) hd_w_rec
      hloc_w hrec_w_bnd htmp_w hf_w hw_w ht_w hb_w hw16
      ((hst3_lt30 4 (by decide)).trans hr4) ((hst3_lt30 8 (by decide)).trans hr8)
      ((hst3_lt30 9 (by decide)).trans hr9) ((hst3_lt30 14 (by decide)).trans hr14)
      ((hst3_lt30 22 (by decide)).trans hr22) ((hst3_lt30 24 (by decide)).trans hr24)
      ((hst3_lt30 25 (by decide)).trans hr25) rfl) rfl ?_
  intro st4 ⟨hfm4, hoth4, hpos4, hfr4, hEF4, hWcut4, hWnon4⟩
  have hmAt4 : EdgesAt st4.mem (rtOutA + 2) matchings.flatten := fun q hq => by
    rw [hfr4 _ (by rcases hd_tmp_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_f_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_w_rt with h | h <;> [right; left] <;> omega),
      hfr4 _ (by rcases hd_tmp_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_f_rt with h | h <;> [right; left] <;> omega)
        (by rcases hd_w_rt with h | h <;> [right; left] <;> omega),
      hfr3 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega),
      hfr3 _ (by rcases hd_loc_rt with h | h <;> [right; left] <;> omega)]
    exact hmAt1 q hq
  refine runs_triple_le
    (scSetMatched_triple (w := w) (n := n) (mE := matchings.flatten.length) (ea := rtOutA + 2) (la := locA)
      (rM := 44) (rEdges := 45) (rLoc := 8) (rI := 41) (rU := 42) (rV := 43) (val := 0)
      (by decide) p st4.mem matchings.flatten st4 rfl hmAt4 hflat_lt
      (by rcases hd_loc_rt with h | h <;> [left; right] <;> omega) (by omega) hloc_w (by omega) hw16
      (by rw [hoth4 44 (Or.inr (by decide)) (by decide), hoth3 44 (by decide) (by decide) (by decide)]
          dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by rw [hoth4 45 (Or.inr (by decide)) (by decide), hoth3 45 (by decide) (by decide) (by decide)]
          dsimp only [st2]; rw [Function.update_self])
      (by rw [hoth4 8 (Or.inl (by decide)) (by decide), hst3_lt30 8 (by decide), hr8])
      rfl) rfl ?_ (by simp only [Expr.size]
                      have h1 : 48 * t * (b / 2) = 48 * (t * (b / 2)) := by ring
                      have h2 : 172 * t * (b / 2) = 172 * (t * (b / 2)) := by ring
                      have h3 : 220 * t * (b / 2) = 220 * (t * (b / 2)) := by ring
                      rw [h1, h2, h3]; omega)
  rintro (_ | _) st5 h5
  · rcases h5 with ⟨hoth5, hpos5, hfr5, hloc5⟩
    refine ⟨(hoth5 14 (by decide) (by decide) (by decide)).trans hfm4,
      fun r hr hne => (hoth5 r (by omega) (by omega) (by omega)).trans ((hoth4 r (Or.inl hr) hne).trans (hst3_lt30 r hr)),
      by rw [hpos5, hpos4, hpos3, hpos1],
      fun u hu => by
        rw [hloc5 u hu]; by_cases hm : u ∈ matchedVerts matchings.flatten
        · simp [hm]
        · simp only [hm, ↓reduceIte]
          rw [hfr4 _ (by rcases hd_loc_tmp with h | h <;> [left; right] <;> omega)
            (by rcases hd_loc_f with h | h <;> [left; right] <;> omega)
            (by rcases hd_loc_w with h | h <;> [left; right] <;> omega), hloc3 u hu]
          simp [hm, hloc0_1 u hu],
      fun a ha_loc ha_tmp ha_f ha_w => (hfr5 a ha_loc).trans ((hfr4 a ha_tmp ha_f ha_w).trans (hfr3_all a ha_loc ha_w)),
      fun q hq => by
        have hq_k : q < k := by rw [List.length_append, hFlen] at hq; omega
        rw [hfr5 _ (by rcases hd_loc_f with h | h <;> [right; left] <;> omega),
          hfr5 _ (by rcases hd_loc_f with h | h <;> [right; left] <;> omega)]
        exact hEF4 q hq,
      fun idx hidx => by
        have hW := hWcut4 idx hidx
        dsimp only at hW
        rw [hcur_cut idx hidx, List.append_assoc] at hW
        have hWg := graphAt_mk_iff.mp hW
        have hi := hcut_lt _ (List.getElem_mem (hcut_len.symm ▸ hidx))
        have hcap := hprev_cap idx hidx
        refine graphAt_mk_iff.mpr ⟨by rw [hfr5 _ (by have := hslot_lt _ hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.1,
          by rw [hfr5 _ (by have := hslot_lt _ hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.2.1,
          fun q hq => by
            rw [List.length_append, List.length_append] at hq
            have h1 := hslot_lt _ hi (2 + 2 * q) (by omega)
            have h2 := hslot_lt _ hi (2 + 2 * q + 1) (by omega)
            rw [hfr5 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
              hfr5 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
            exact hWg.2.2 q (by rw [List.length_append, List.length_append]; exact hq)⟩,
      fun i hi hnotin => by
        have hW := hWnon4 i hi hnotin
        rw [hcur_non i hnotin] at hW
        have hWg := graphAt_mk_iff.mp hW
        have hlen_i := hprev_len_all i hi
        refine graphAt_mk_iff.mpr ⟨by rw [hfr5 _ (by have := hslot_lt i hi 0 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.1,
          by rw [hfr5 _ (by have := hslot_lt i hi 1 (by omega); rcases hd_loc_w with h | h <;> [right; left] <;> omega)]; exact hWg.2.1,
          fun q hq => by
            have h1 := hslot_lt i hi (2 + 2 * q) (by omega)
            have h2 := hslot_lt i hi (2 + 2 * q + 1) (by omega)
            rw [hfr5 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega),
              hfr5 _ (by rcases hd_loc_w with h | h <;> [right; left] <;> omega)]
            exact hWg.2.2 q hq⟩⟩
  · exact False.elim h5

end MinCostFlow.ExpanderDecomp
