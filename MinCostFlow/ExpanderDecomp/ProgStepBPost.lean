module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBScatter
public import MinCostFlow.ExpanderDecomp.ProgStepCBase

import Mathlib.Tactic.Linarith

/-!
# Step B Dual-Zip Fake-Edge Completion Loop (`ProgStepBPost`)

Implements and verifies `sbCompleteCutLoopStmt`: with `locAddr` marking `matchedVerts matchings.flatten`,
collects unmatched vertices from each active cut pair `(C'_idx, comp_idx)` and dual-zips fake edges
simultaneously into `fAddr` and the owning witness graph `W_i`.

Main results:
- `sbCompleteCutLoopStmt`, `sbCompleteCutLoop_triple`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma sb_slot_disj_range {wBaseA wStride i₁ i₂ off : ℕ} (hne : i₁ ≠ i₂) (hoff : off < wStride) :
    wBaseA + i₁ * wStride + off < wBaseA + i₂ * wStride ∨
      wBaseA + i₂ * wStride + wStride ≤ wBaseA + i₁ * wStride + off := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left
    have h1 : (i₁ + 1) * wStride ≤ i₂ * wStride := Nat.mul_le_mul_right wStride hlt
    have h2 : (i₁ + 1) * wStride = i₁ * wStride + wStride := by ring
    omega
  · right
    have h1 : (i₂ + 1) * wStride ≤ i₁ * wStride := Nat.mul_le_mul_right wStride hgt
    have h2 : (i₂ + 1) * wStride = i₂ * wStride + wStride := by ring
    omega

private lemma sb_graphAt_of_mem_eq {mem mem' : ℕ → ℕ} {a n wStride : ℕ} {E : List (ℕ × ℕ)}
    (hG : GraphAt mem a (Graph.mk n E)) (hbound : 2 + 2 * E.length ≤ wStride)
    (heq : ∀ off < wStride, mem' (a + off) = mem (a + off)) :
    GraphAt mem' a (Graph.mk n E) := by
  have h := graphAt_mk_iff.mp hG
  refine graphAt_mk_iff.mpr ⟨by simpa only [Nat.add_zero] using (heq 0 (by omega)).trans h.1,
    (heq 1 (by omega)).trans h.2.1, fun q hq => ?_⟩
  have h1 := heq (2 + 2 * q) (by omega)
  have h2 := heq (2 + 2 * q + 1) (by omega)
  have ha1 : a + (2 + 2 * q) = a + 2 + 2 * q := by omega
  have ha2 : a + (2 + 2 * q + 1) = a + 2 + 2 * q + 1 := by omega
  rw [ha1] at h1; rw [ha2] at h2
  exact ⟨h1.trans (h.2.2 q hq).1, h2.trans (h.2.2 q hq).2⟩

/-! ## 1. Dual-Zip Fake-Edge Completion Loop (`sbCompleteCutLoopStmt`) -/

/-- With `locAddr` (`r8`) marking `matchedVerts matchings.flatten`, loops `idx = 0..t-1` over the
cut records at `r22` (`[wAddr, cPrimeA, compA]`), collects unmatched vertices into `tmpA` (`r24`)
and `tmpB` (`r24 + b`), dual-zips fake edges into `fAddr` (`r9`, count `r14`) and `W_i`, and
updates `mem[wAddr + 1]`. Modifies only `r14` and `r30..r43`. -/
def sbCompleteCutLoopStmt : Stmt :=
  seqStmts [
    .assign 30 (.bin .div (.reg 4) (.const 2)),
    .assign 36 (.bin .add (.reg 24) (.reg 4)),
    forRange 31 (.const 0) (.reg 25) (seqStmts [
      .assign 32 (.load (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31)))),
      .assign 33 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      .assign 34 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 2))),
      scCollectUnmatchedStmt 33 30 8 24 35 41 42,
      scCollectUnmatchedStmt 34 30 8 36 37 41 42,
      .assign 38 (.bin .add (.reg 32) (.const 2)),
      .assign 39 (.load (.bin .add (.reg 32) (.const 1))),
      sbZipDualStmt 24 35 36 37 9 14 38 39 40 41 42 43,
      .store (.bin .add (.reg 32) (.const 1)) (.reg 39)
    ])
  ]

/-- Triple for `sbCompleteCutLoopStmt`. -/
theorem sbCompleteCutLoop_triple
    {w n b t k locA fA prevF cutRecsA tmpA wBaseA wStride nBlocks maxR : ℕ}
    {p : Program} {mem : ℕ → ℕ} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {matchings : List (List (ℕ × ℕ))}
    {cutIds : List ℕ} {cPrimeAddrs compAddrs : List ℕ}
    {cPrimeLists compLists : List (List ℕ)}
    {prevFEs : List (ℕ × ℕ)} {curWEdges : ℕ → List (ℕ × ℕ)} {st₀ : State}
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
      ListAt mem cA cL ∧ DisjointRange tmpA (2 * b) cA (b / 2) ∧
      DisjointRange fA (2 * k) cA (b / 2) ∧ DisjointRange wBaseA (nBlocks * wStride) cA (b / 2) ∧
      cA + b / 2 < 2 ^ w ∧
      oL.length = b / 2 ∧ oL.Pairwise (· < ·) ∧ oL.toFinset = (pairs[idx]'(ht_len.symm ▸ hidx)).2 ∧
      ListAt mem oA oL ∧ DisjointRange tmpA (2 * b) oA (b / 2) ∧
      DisjointRange fA (2 * k) oA (b / 2) ∧ DisjointRange wBaseA (nBlocks * wStride) oA (b / 2) ∧
      oA + b / 2 < 2 ^ w)
    (hFlen : prevFEs.length = prevF) (hF_at : EdgesAt mem fA prevFEs)
    (hF_cap : prevF + (completeBatchFake pairs matchings).length ≤ k)
    (hwStride_eq : wStride = 2 + 2 * maxR * (b / 2))
    (hW_at : ∀ i < nBlocks, GraphAt mem (wBaseA + i * wStride) (Graph.mk n (curWEdges i)))
    (hW_len_all : ∀ i < nBlocks, (curWEdges i).length ≤ maxR * (b / 2))
    (hW_cap : ∀ idx (hidx : idx < t),
      let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
      let p_i := pairs[idx]'(ht_len.symm ▸ hidx)
      (curWEdges i).length + (completeMatchingFake p_i.1 p_i.2 (matchings.getD idx [])).length ≤ maxR * (b / 2))
    (hloc : ∀ u < n, mem (locA + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0)
    (hd_tmp_loc : DisjointRange tmpA (2 * b) locA n)
    (hd_tmp_rec : DisjointRange tmpA (2 * b) cutRecsA (3 * t))
    (hd_tmp_f : DisjointRange tmpA (2 * b) fA (2 * k))
    (hd_tmp_w : DisjointRange tmpA (2 * b) wBaseA (nBlocks * wStride))
    (hd_f_loc : DisjointRange fA (2 * k) locA n)
    (hd_f_rec : DisjointRange fA (2 * k) cutRecsA (3 * t))
    (hd_f_w : DisjointRange fA (2 * k) wBaseA (nBlocks * wStride))
    (hd_w_loc : DisjointRange wBaseA (nBlocks * wStride) locA n)
    (hd_w_rec : DisjointRange wBaseA (nBlocks * wStride) cutRecsA (3 * t))
    (hloc_w : locA + n < 2 ^ w) (hrec_w_bnd : cutRecsA + 3 * t < 2 ^ w)
    (htmp_w : tmpA + 2 * b < 2 ^ w) (hf_w : fA + 2 * k < 2 ^ w)
    (hw_w : wBaseA + nBlocks * wStride < 2 ^ w) (ht_w : t + 1 < 2 ^ w)
    (hb_w : b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st₀.regs 4 = b) (hr8 : st₀.regs 8 = locA) (hr9 : st₀.regs 9 = fA)
    (hr14 : st₀.regs 14 = prevF) (hr22 : st₀.regs 22 = cutRecsA)
    (hr24 : st₀.regs 24 = tmpA) (hr25 : st₀.regs 25 = t)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) sbCompleteCutLoopStmt
      (normalPost fun st' =>
        st'.regs 14 = prevF + (completeBatchFake pairs matchings).length ∧
        (∀ r, (r < 30 ∨ 44 ≤ r) → r ≠ 14 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ a, (a < tmpA ∨ tmpA + 2 * b ≤ a) → (a < fA ∨ fA + 2 * k ≤ a) →
          (a < wBaseA ∨ wBaseA + nBlocks * wStride ≤ a) → st'.mem a = mem a) ∧
        EdgesAt st'.mem fA (prevFEs ++ completeBatchFake pairs matchings) ∧
        (∀ idx (hidx : idx < t),
          let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
          let p_i := pairs[idx]'(ht_len.symm ▸ hidx)
          GraphAt st'.mem (wBaseA + i * wStride)
            (Graph.mk n (curWEdges i ++ completeMatchingFake p_i.1 p_i.2 (matchings.getD idx [])))) ∧
        (∀ i < nBlocks, i ∉ cutIds →
          GraphAt st'.mem (wBaseA + i * wStride) (Graph.mk n (curWEdges i))))
      (fun _ => 172 * t * (b / 2) + 230 * t + 30) := by
  have hwS2 : wStride = 2 + 2 * (maxR * (b / 2)) := by rw [hwStride_eq]; ring
  have hslot_lt : ∀ i < nBlocks, ∀ off < wStride, wBaseA + i * wStride + off < wBaseA + nBlocks * wStride := by
    intro i hi off hoff
    have h1 : (i + 1) * wStride ≤ nBlocks * wStride := Nat.mul_le_mul_right wStride hi
    have h2 : (i + 1) * wStride = i * wStride + wStride := by ring
    omega
  have hslot_disj : ∀ i₁ i₂, i₁ ≠ i₂ → ∀ off₁ < wStride, ∀ off₂ < wStride,
      wBaseA + i₁ * wStride + off₁ ≠ wBaseA + i₂ * wStride + off₂ := by
    intro i₁ i₂ hne off₁ h1 off₂ h2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have : (i₁ + 1) * wStride ≤ i₂ * wStride := Nat.mul_le_mul_right wStride hlt
      have : (i₁ + 1) * wStride = i₁ * wStride + wStride := by ring
      omega
    · have : (i₂ + 1) * wStride ≤ i₁ * wStride := Nat.mul_le_mul_right wStride hgt
      have : (i₂ + 1) * wStride = i₂ * wStride + wStride := by ring
      omega
  set zipList := List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings
  have hzip_len : zipList.length = t := by simp [zipList, ht_len, hmlen]
  have hzip_get : ∀ idx (hidx : idx < t),
      zipList[idx]'(hzip_len.symm ▸ hidx) =
        completeMatchingFake (pairs[idx]'(ht_len.symm ▸ hidx)).1
          (pairs[idx]'(ht_len.symm ▸ hidx)).2 (matchings.getD idx []) := by
    intro idx hidx
    dsimp only [zipList]
    rw [List.getElem_zipWith, List.getD_eq_getElem _ _ (hmlen.symm ▸ hidx)]
  have hbatch_eq : completeBatchFake pairs matchings = zipList.flatten := rfl
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [sbCompleteCutLoopStmt, seqStmts]
  refine runs_seq_assign_le (v := b / 2)
    (Expr.eval_div (Expr.eval_reg_of_eq hr4) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := tmpA + b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr24]))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr4])) (by omega)) ?_
  let st1 : State :=
    { mem := st₀.mem,
      regs := Function.update (Function.update st₀.regs 30 (b / 2)) 36 (tmpA + b),
      pos := st₀.pos }
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 31 = j ∧
    st.regs 30 = b / 2 ∧
    st.regs 36 = tmpA + b ∧
    st.regs 14 = prevF + (zipList.take j).flatten.length ∧
    (∀ r, (r < 30 ∨ 44 ≤ r) → r ≠ 14 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    (∀ a, (a < tmpA ∨ tmpA + 2 * b ≤ a) → (a < fA ∨ fA + 2 * k ≤ a) →
      (a < wBaseA ∨ wBaseA + nBlocks * wStride ≤ a) → st.mem a = mem a) ∧
    EdgesAt st.mem fA (prevFEs ++ (zipList.take j).flatten) ∧
    (∀ idx (hidx : idx < t),
      let i := cutIds[idx]'(hcut_len.symm ▸ hidx)
      let p_i := pairs[idx]'(ht_len.symm ▸ hidx)
      GraphAt st.mem (wBaseA + i * wStride)
        (Graph.mk n (if idx < j then curWEdges i ++ completeMatchingFake p_i.1 p_i.2 (matchings.getD idx [])
          else curWEdges i))) ∧
    (∀ i < nBlocks, i ∉ cutIds → GraphAt st.mem (wBaseA + i * wStride) (Graph.mk n (curWEdges i)))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 31) (lo := .const 0) (hi := .reg 25)
    (body := seqStmts [
      .assign 32 (.load (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31)))),
      .assign 33 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 1))),
      .assign 34 (.load (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 3) (.reg 31))) (.const 2))),
      scCollectUnmatchedStmt 33 30 8 24 35 41 42,
      scCollectUnmatchedStmt 34 30 8 36 37 41 42,
      .assign 38 (.bin .add (.reg 32) (.const 2)),
      .assign 39 (.load (.bin .add (.reg 32) (.const 1))),
      sbZipDualStmt 24 35 36 37 9 14 38 39 40 41 42 43,
      .store (.bin .add (.reg 32) (.const 1)) (.reg 39)])
    (P := fun st => st = st1) (Inv := Inv) (172 * (b / 2) + 215) 0 t (Nat.zero_le t) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (w := w) (by omega), by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self],
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self],
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr14]; simp,
        fun r hr hne => by dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        rfl, fun a _ _ _ => congrFun hmem a, by simpa [st1, hmem] using hF_at,
        fun idx hidx => by simp only [Nat.not_lt_zero, ↓reduceIte, st1, hmem]; exact hW_at _ (hcut_lt _ (List.getElem_mem (hcut_len.symm ▸ hidx))),
        fun i hi _ => by simp only [st1, hmem]; exact hW_at i hi⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq ((hInv.2.2.2.2.1 25 (Or.inl (by decide)) (by decide)).trans hr25))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hr30, hr36, hr14_j, hoth, hpos, hfr, hEF, hWcut, hWnon⟩
      have hspec := hlists_spec j hjlt
      rcases hspec with ⟨hcL_len, hcL_lt, hcL_fin, hcL_at, hd_tmp_c, hd_f_c, hd_w_c, hcA_w,
        hoL_len, hoL_lt, hoL_fin, hoL_at, hd_tmp_o, hd_f_o, hd_w_o, hoA_w⟩
      set i0 := cutIds[j]'(hcut_len.symm ▸ hjlt)
      have hi0 : i0 < nBlocks := hcut_lt i0 (List.getElem_mem (hcut_len.symm ▸ hjlt))
      set wA0 := wBaseA + i0 * wStride
      set cA0 := cPrimeAddrs[j]'(hcpa_len.symm ▸ hjlt)
      set oA0 := compAddrs[j]'(hcoa_len.symm ▸ hjlt)
      set cL0 := cPrimeLists[j]'(hcpl_len.symm ▸ hjlt)
      set oL0 := compLists[j]'(hcol_len.symm ▸ hjlt)
      set S_m := matchedVerts matchings.flatten
      set unmA := cL0.filter (fun u => decide (u ∉ S_m))
      set unmB := oL0.filter (fun u => decide (u ∉ S_m))
      have hfk_eq : completeMatchingFake (pairs[j]'(ht_len.symm ▸ hjlt)).1 (pairs[j]'(ht_len.symm ▸ hjlt)).2
          (matchings.getD j []) = unmA.zip unmB := by
        rw [List.getD_eq_getElem _ _ (hmlen.symm ▸ hjlt)]
        exact completeMatchingFake_eq_of_flat hvtp (hmlen.trans ht_len.symm)
          (fun idx hidx => hpm idx (ht_len ▸ hidx)) (ht_len.symm ▸ hjlt) hcL_lt hoL_lt hcL_fin hoL_fin
      have htake_z : (zipList.take (j + 1)).flatten = (zipList.take j).flatten ++ unmA.zip unmB := by
        rw [List.take_succ_eq_append_getElem (hzip_len.symm ▸ hjlt), List.flatten_append,
          List.flatten_singleton, hzip_get j hjlt, hfk_eq]
      have hsub_fk : (zipList.take (j + 1)).flatten.length ≤ (completeBatchFake pairs matchings).length := by
        rw [hbatch_eq]; exact (List.take_sublist _ _).flatten.length_le
      have hfk_cap_j : (prevFEs ++ (zipList.take j).flatten).length + min unmA.length unmB.length ≤ k := by
        rw [List.length_append, hFlen]
        have hlen_z : (unmA.zip unmB).length = min unmA.length unmB.length := List.length_zip
        rw [htake_z, List.length_append, hlen_z] at hsub_fk
        omega
      have hW_cap_j : (curWEdges i0).length + min unmA.length unmB.length ≤ maxR * (b / 2) := by
        have h1 := hW_cap j hjlt; dsimp only at h1; rw [hfk_eq, List.length_zip] at h1; exact h1
      have hW0_g : GraphAt st.mem wA0 (Graph.mk n (curWEdges i0)) := by
        have h := hWcut j hjlt; simp only [lt_irrefl, ↓reduceIte] at h; exact h
      have hW0 := graphAt_mk_iff.mp hW0_g
      have hcL_sub_n : ∀ u ∈ cL0, u < n := fun u hu =>
        Finset.mem_range.mp (hX_sub ((hvtp.1 _ (List.getElem_mem (ht_len.symm ▸ hjlt))).1 (hcL_fin ▸ List.mem_toFinset.mpr hu)))
      have hoL_sub_n : ∀ u ∈ oL0, u < n := fun u hu =>
        Finset.mem_range.mp (hX_sub ((hvtp.1 _ (List.getElem_mem (ht_len.symm ▸ hjlt))).2.1 (hoL_fin ▸ List.mem_toFinset.mpr hu)))
      have hrec_w_j : st.mem (cutRecsA + 3 * j) = wA0 := by
        rw [hfr _ (by rcases hd_tmp_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]
        exact hrec_w j hjlt
      have hrec_c_j : st.mem (cutRecsA + 3 * j + 1) = cA0 := by
        rw [hfr _ (by rcases hd_tmp_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]
        exact hrec_c j hjlt
      have hrec_o_j : st.mem (cutRecsA + 3 * j + 2) = oA0 := by
        rw [hfr _ (by rcases hd_tmp_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_rec with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_rec with h | h <;> [right; left] <;> omega)]
        exact hrec_o j hjlt
      have hloc_st : ∀ u < n, st.mem (locA + u) = if u ∈ S_m then 1 else 0 := fun u hu => by
        rw [hfr _ (by rcases hd_tmp_loc with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_loc with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_loc with h | h <;> [right; left] <;> omega)]
        exact hloc u hu
      have hcL_at_st : ListAt st.mem cA0 cL0 := fun q hq => by
        rw [hfr _ (by rcases hd_tmp_c with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_c with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_c with h | h <;> [right; left] <;> omega)]
        exact hcL_at q hq
      have hoL_at_st : ListAt st.mem oA0 oL0 := fun q hq => by
        rw [hfr _ (by rcases hd_tmp_o with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_o with h | h <;> [right; left] <;> omega)
          (by rcases hd_w_o with h | h <;> [right; left] <;> omega)]
        exact hoL_at q hq
      have hslot0_w : wA0 + 2 + 2 * (maxR * (b / 2)) ≤ wBaseA + nBlocks * wStride := by
        have h1 : (i0 + 1) * wStride ≤ nBlocks * wStride := Nat.mul_le_mul_right wStride hi0
        have h2 : (i0 + 1) * wStride = i0 * wStride + wStride := by ring
        omega
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wA0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ((hoth 22 (Or.inl (by decide)) (by decide)).trans hr22))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq hj) (by omega)) (by omega)) hrec_w_j) ?_
      refine runs_seq_assign_le (v := cA0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hoth 22 (Or.inl (by decide)) (by decide), hr22]))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hj])) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega)) hrec_c_j) ?_
      refine runs_seq_assign_le (v := oA0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 22 (Or.inl (by decide)) (by decide), hr22]))
          (Expr.eval_mul (Expr.eval_const (w := w) (by omega)) (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj])) (by omega)) (by omega))
          (Expr.eval_const (w := w) (by omega)) (by omega)) hrec_o_j) ?_
      let stA : State :=
        { mem := st.mem,
          regs := Function.update (Function.update (Function.update st.regs 32 wA0) 33 cA0) 34 oA0,
          pos := st.pos }
      refine runs_seq_triple_le
        (scCollectUnmatched_triple (w := w) (n := n) (len := b / 2) (sa := cA0) (la := locA) (da := tmpA)
          (rSrc := 33) (rLen := 30) (rLoc := 8) (rDst := 24) (rCnt := 35) (rI := 41) (rU := 42)
          (by decide) p st.mem cL0 S_m stA hcL_len hcL_at_st hcL_sub_n hloc_st
          (by rcases hd_tmp_c with h | h <;> [left; right] <;> omega)
          (by rcases hd_tmp_loc with h | h <;> [left; right] <;> omega)
          hcA_w hloc_w (by omega) hw16
          (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_self])
          (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30])
          (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 8 (Or.inl (by decide)) (by decide), hr8])
          (by dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 24 (Or.inl (by decide)) (by decide), hr24])
          rfl) rfl ?_
      intro stB ⟨hcntA_B, hothB, hposB, hfrB, hunmA_B⟩
      have hoL_at_B : ListAt stB.mem oA0 oL0 := fun q hq => by
        rw [hfrB _ (by rcases hd_tmp_o with h | h <;> [right; left] <;> omega)]; exact hoL_at_st q hq
      have hloc_B : ∀ u < n, stB.mem (locA + u) = if u ∈ S_m then 1 else 0 := fun u hu => by
        rw [hfrB _ (by rcases hd_tmp_loc with h | h <;> [right; left] <;> omega)]; exact hloc_st u hu
      refine runs_seq_triple_le
        (scCollectUnmatched_triple (w := w) (n := n) (len := b / 2) (sa := oA0) (la := locA) (da := tmpA + b)
          (rSrc := 34) (rLen := 30) (rLoc := 8) (rDst := 36) (rCnt := 37) (rI := 41) (rU := 42)
          (by decide) p stB.mem oL0 S_m stB hoL_len hoL_at_B hoL_sub_n hloc_B
          (by rcases hd_tmp_o with h | h <;> [left; right] <;> omega)
          (by rcases hd_tmp_loc with h | h <;> [left; right] <;> omega)
          hoA_w hloc_w (by omega) hw16
          (by rw [hothB 34 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_self])
          (by rw [hothB 30 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30])
          (by rw [hothB 8 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hoth 8 (Or.inl (by decide)) (by decide), hr8])
          (by rw [hothB 36 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr36])
          rfl) rfl ?_
      intro stC ⟨hcntB_C, hothC, hposC, hfrC, hunmB_C⟩
      have hstC_lt30 : ∀ r, (r < 30 ∨ 44 ≤ r) → r ≠ 14 → stC.regs r = st₀.regs r := fun r hr hne => by
        rw [hothC r (by omega) (by omega) (by omega), hothB r (by omega) (by omega) (by omega)]
        dsimp only [stA]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hoth r hr hne]
      have hr32_C : stC.regs 32 = wA0 := by
        rw [hothC 32 (by decide) (by decide) (by decide), hothB 32 (by decide) (by decide) (by decide)]
        dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
      have hwm0_C : stC.mem (wA0 + 1) = (curWEdges i0).length := by
        have h1 := hslot_lt i0 hi0 1 (by omega)
        rw [hfrC _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega),
          hfrB _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)]
        exact hW0.2.1
      refine runs_seq_assign_le (v := wA0 + 2)
        (Expr.eval_add (Expr.eval_reg_of_eq hr32_C) (Expr.eval_const (w := w) (by omega)) (by omega)) ?_
      refine runs_seq_assign_le (v := (curWEdges i0).length)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr32_C]))
          (Expr.eval_const (w := w) (by omega)) (by omega)) hwm0_C) ?_
      let stD : State :=
        { mem := stC.mem,
          regs := Function.update (Function.update stC.regs 38 (wA0 + 2)) 39 (curWEdges i0).length,
          pos := stC.pos }
      have hunmA_C : ListAt stC.mem tmpA unmA := fun q hq => by
        have hq_b : q < b / 2 := lt_of_lt_of_le hq ((List.length_filter_le _ _).trans (le_of_eq hcL_len))
        rw [hfrC _ (Or.inl (by omega))]; exact hunmA_B q hq
      have hEF_C : EdgesAt stC.mem fA (prevFEs ++ (zipList.take j).flatten) := fun q hq => by
        have hq_k : q < k := by
          have : (prevFEs ++ (zipList.take j).flatten).length ≤ k := by omega
          omega
        rw [hfrC _ (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega),
          hfrB _ (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega),
          hfrC _ (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega),
          hfrB _ (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega)]
        exact hEF q hq
      have hEW_C : EdgesAt stC.mem (wA0 + 2) (curWEdges i0) := fun q hq => by
        have hq_m : q < maxR * (b / 2) := lt_of_lt_of_le hq (hW_len_all i0 hi0)
        have h1 := hslot_lt i0 hi0 (2 + 2 * q) (by omega)
        have h2 := hslot_lt i0 hi0 (2 + 2 * q + 1) (by omega)
        rw [hfrC _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega),
          hfrB _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega),
          hfrC _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega),
          hfrB _ (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)]
        exact hW0.2.2 q hq
      have hunmA_le : unmA.length ≤ b / 2 := (List.length_filter_le _ _).trans (le_of_eq hcL_len)
      have hunmB_le : unmB.length ≤ b / 2 := (List.length_filter_le _ _).trans (le_of_eq hoL_len)
      refine runs_seq_triple_le
        (sbZipDual_triple (w := w) (cntA := unmA.length) (cntB := unmB.length)
          (prevF := prevF + (zipList.take j).flatten.length) (capF := k)
          (prevW := (curWEdges i0).length) (capW := maxR * (b / 2))
          (fA := fA) (wEA := wA0 + 2) (ua := tmpA) (ub := tmpA + b)
          (rUnmA := 24) (rCntA := 35) (rUnmB := 36) (rCntB := 37) (rFAddr := 9) (rFakeM := 14)
          (rWEdges := 38) (rWM := 39) (rLim := 40) (rI := 41) (rU := 42) (rV := 43)
          (by decide) p stC.mem unmA unmB (prevFEs ++ (zipList.take j).flatten) (curWEdges i0) stD
          rfl rfl (by rw [List.length_append, hFlen]) rfl hunmA_C hunmB_C hEF_C hEW_C
          (by rw [List.length_append, hFlen] at hfk_cap_j; omega) (by omega)
          (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega)
          (by rcases hd_tmp_f with h | h <;> [right; left] <;> omega)
          (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)
          (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)
          (by rcases hd_f_w with h | h <;> [left; right] <;> omega)
          (by omega) (by omega) hf_w (by omega) hw16
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstC_lt30 24 (Or.inl (by decide)) (by decide), hr24])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 35 (by decide) (by decide) (by decide), hcntA_B])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 36 (by decide) (by decide) (by decide), hothB 36 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr36])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hcntB_C])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hstC_lt30 9 (Or.inl (by decide)) (by decide), hr9])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 14 (by decide) (by decide) (by decide), hothB 14 (by decide) (by decide) (by decide)]; dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr14_j])
          (by dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_self])
          (by dsimp only [stD]; rw [Function.update_self]) rfl) rfl ?_
      intro stE ⟨hfmE, hwmE, hothE, hposE, hfrE, hEF_E, hEW_E⟩
      have hr32_E : stE.regs 32 = wA0 := by
        rw [hothE 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr32_C]
      refine runs_store_le (x := wA0 + 1) (v := (curWEdges i0).length + min unmA.length unmB.length)
        (Expr.eval_add (Expr.eval_reg_of_eq hr32_E) (Expr.eval_const (w := w) (by omega)) (by omega))
        (Expr.eval_reg_of_eq hwmE) ?_ (by simp only [Expr.size]; omega)
      have hlen_zip_min : (unmA.zip unmB).length = min unmA.length unmB.length := List.length_zip
      have hW_mem_fr : ∀ a, (a < fA ∨ fA + 2 * k ≤ a) →
          (a < wA0 ∨ wA0 + wStride ≤ a) → (a < tmpA ∨ tmpA + 2 * b ≤ a) → stE.mem a = st.mem a := by
        intro a haF haW0 haT
        rw [hfrE a haF (by omega), hfrC a (by omega), hfrB a (by omega)]
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hothE 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
           dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 30 (by decide) (by decide) (by decide), hothB 30 (by decide) (by decide) (by decide)]
           dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30],
        by dsimp only; rw [Function.update_of_ne (by decide), hothE 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
           dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 36 (by decide) (by decide) (by decide), hothB 36 (by decide) (by decide) (by decide)]
           dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr36],
        by dsimp only; rw [Function.update_of_ne (by decide), hfmE, htake_z, List.length_append, hlen_zip_min]; omega,
        fun r hr hne => by
          dsimp only; rw [Function.update_of_ne (by omega), hothE r hne (by omega) (by omega) (by omega) (by omega) (by omega)]
          dsimp only [stD]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hstC_lt30 r hr hne],
        by rw [hposE, hposC, hposB, hpos],
        fun a haT haF haW => by
          have hne_w1 : a ≠ wA0 + 1 := by have := hslot_lt i0 hi0 1 (by omega); omega
          dsimp only; rw [Function.update_of_ne hne_w1]
          rw [hfrE a haF (by omega), hfrC a (by omega), hfrB a (by omega)]
          exact hfr a haT haF haW,
        ?_, ?_, ?_⟩,
        by rw [hothE 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
           dsimp only [stD]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hothC 31 (by decide) (by decide) (by decide), hothB 31 (by decide) (by decide) (by decide)]
           dsimp only [stA]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hj]⟩
      · rw [htake_z, ← List.append_assoc]; intro q hq
        have hq_k : q < k := by
          rw [List.length_append, hlen_zip_min] at hq
          omega
        have hne1 : fA + 2 * q ≠ wA0 + 1 := by have := hslot_lt i0 hi0 1 (by omega); rcases hd_f_w with h | h <;> omega
        have hne2 : fA + 2 * q + 1 ≠ wA0 + 1 := by have := hslot_lt i0 hi0 1 (by omega); rcases hd_f_w with h | h <;> omega
        dsimp only; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]; exact hEF_E q hq
      · intro idx hidx
        by_cases hjeq : idx = j
        · subst hjeq
          simp only [Nat.lt_succ_self, ↓reduceIte, hfk_eq]
          have hw0_eq : Function.update stE.mem (wA0 + 1) ((curWEdges i0).length + min unmA.length unmB.length) wA0 = n := by
            have h1 := hslot_lt i0 hi0 0 (by omega)
            rw [Function.update_of_ne (by omega),
              hfrE wA0 (by rcases hd_f_w with h | h <;> [right; left] <;> omega) (Or.inl (by omega)),
              hfrC wA0 (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega),
              hfrB wA0 (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)]
            exact hW0.1
          refine graphAt_mk_iff.mpr ⟨hw0_eq, by dsimp only [wA0, i0]; rw [Function.update_self, List.length_append, hlen_zip_min], ?_⟩
          intro q hq
          dsimp only [wA0, i0]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hEW_E q hq
        · have hlt_iff : (idx < j + 1) ↔ (idx < j) := by omega
          simp only [hlt_iff]
          have hne_id : cutIds[idx]'(hcut_len.symm ▸ hidx) ≠ i0 := fun h => hjeq ((List.Nodup.getElem_inj_iff hcut_nd).mp h)
          have hi_idx := hcut_lt _ (List.getElem_mem (hcut_len.symm ▸ hidx))
          have hlen_idx : (if idx < j then curWEdges (cutIds[idx]'(hcut_len.symm ▸ hidx)) ++
              completeMatchingFake (pairs[idx]'(ht_len.symm ▸ hidx)).1 (pairs[idx]'(ht_len.symm ▸ hidx)).2 (matchings.getD idx [])
              else curWEdges (cutIds[idx]'(hcut_len.symm ▸ hidx))).length ≤ maxR * (b / 2) := by
            split_ifs
            · rw [List.length_append]; exact hW_cap idx hidx
            · exact hW_len_all _ hi_idx
          refine sb_graphAt_of_mem_eq (wStride := wStride) (hWcut idx hidx) (by omega) fun off hoff => ?_
          have hdisj := sb_slot_disj_range (wBaseA := wBaseA) (wStride := wStride) hne_id hoff
          have hs := hslot_lt _ hi_idx off hoff
          dsimp only [wA0] at hdisj ⊢
          rw [Function.update_of_ne (by omega)]
          exact hW_mem_fr _ (by rcases hd_f_w with h | h <;> [right; left] <;> omega) (by dsimp only [wA0]; omega)
            (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega)
      · intro i hi hnotin
        have hne_id : i ≠ i0 := fun h => hnotin (h ▸ List.getElem_mem (hcut_len.symm ▸ hjlt))
        have hlen_i := hW_len_all i hi
        refine sb_graphAt_of_mem_eq (wStride := wStride) (hWnon i hi hnotin) (by omega) fun off hoff => ?_
        have hdisj := sb_slot_disj_range (wBaseA := wBaseA) (wStride := wStride) hne_id hoff
        have hs := hslot_lt i hi off hoff
        dsimp only [wA0] at hdisj ⊢
        rw [Function.update_of_ne (by omega)]
        exact hW_mem_fr _ (by rcases hd_f_w with h | h <;> [right; left] <;> omega) (by dsimp only [wA0]; omega)
          (by rcases hd_tmp_w with h | h <;> [right; left] <;> omega))
  refine runs_triple_le hloop rfl ?_
    (by simp only [Expr.size, Nat.sub_zero]
        have h1 : t * (172 * (b / 2) + 215 + 1 + 8) = 172 * t * (b / 2) + 224 * t := by ring
        rw [h1]; omega)
  rintro (_ | _) stF hF
  · rcases hF with ⟨_, _, _, hfmF, hothF, hposF, hfrF, hEFF, hWcutF, hWnonF⟩
    rw [← hzip_len, List.take_length] at hfmF hEFF
    refine ⟨hfmF, hothF, hposF, hfrF, hEFF, fun idx hidx => ?_, hWnonF⟩
    have h := hWcutF idx hidx; simp only [hidx, ↓reduceIte] at h; exact h
  · exact False.elim hF

end MinCostFlow.ExpanderDecomp
