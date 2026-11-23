module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepCExtract

import Mathlib.Tactic.Linarith

/-!
# Step C Fake-Edge Completion Loop (`ProgStepCColor`)

Verifies `scCompleteFakeLoopStmt` (defined in `ProgStepCExtract.lean`): given `locAddr` marking
`matchedVerts matchings.flatten`, appends `completeBatchFake pairs matchings` to
`outAddr + 2 + 2 * prevM` in `O(|X| + |Ec| + 1)` time.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Triple for `scCompleteFakeLoopStmt`: appends `completeBatchFake pairs matchings` at
`outAddr + 2 + 2 * prevM`, advancing `r14` to `prevM + (completeBatchFake pairs matchings).length`. -/
lemma scCompleteFakeLoop_triple {w n xA b ecM ecA la ua ub outEA prevM cap : ℕ}
    (p : Program) (mem : ℕ → ℕ) (vs : List ℕ) (Ec : List (ℕ × ℕ))
    (matchings : List (List (ℕ × ℕ))) (prevFakes : List (ℕ × ℕ)) (st₀ : State)
    (hvs_at : LenListAt mem xA vs) (hvs_s : vs.Pairwise (· < ·))
    (hvs_lt : ∀ u ∈ vs, u < n)
    (hEc_len : Ec.length = ecM) (hEc_at : EdgesAt mem ecA Ec)
    (hEc_valid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b)
    (hEc_nd : (Ec.flatMap fun e => [e.1, e.2]).Nodup) (hb_pos : 0 < b)
    (hmlen : matchings.length = ecM)
    (hpm : ∀ j (hj : j < ecM),
      IsPartialMatching (blockSet vs b (Ec[j]'(by omega)).1)
        (blockSet vs b (Ec[j]'(by omega)).2) (matchings.getD j []))
    (hloc : ∀ u < n, mem (la + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0)
    (hprev_len : prevFakes.length = prevM) (hprev_at : EdgesAt mem outEA prevFakes)
    (hcap : prevM + ecM * b ≤ cap)
    (hd_out_vs : DisjointRange outEA (2 * cap) (xA + 1) vs.length)
    (hd_out_ec : DisjointRange outEA (2 * cap) ecA (2 * ecM))
    (hd_out_loc : DisjointRange outEA (2 * cap) la n)
    (hd_out_ua : DisjointRange outEA (2 * cap) ua b)
    (hd_out_ub : DisjointRange outEA (2 * cap) ub b)
    (hd_ua_vs : DisjointRange ua b (xA + 1) vs.length)
    (hd_ua_ec : DisjointRange ua b ecA (2 * ecM))
    (hd_ua_loc : DisjointRange ua b la n)
    (hd_ua_ub : DisjointRange ua b ub b)
    (hd_ub_vs : DisjointRange ub b (xA + 1) vs.length)
    (hd_ub_ec : DisjointRange ub b ecA (2 * ecM))
    (hd_ub_loc : DisjointRange ub b la n)
    (hx_w : xA + 1 + vs.length < 2 ^ w) (hec_w : ecA + 2 * ecM < 2 ^ w)
    (hla_w : la + n < 2 ^ w) (hua_w : ua + b < 2 ^ w) (hub_w : ub + b < 2 ^ w)
    (hout_w : outEA + 2 * cap < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr1 : st₀.regs 1 = xA) (hr2 : st₀.regs 2 = b) (hr9 : st₀.regs 9 = la)
    (hr14 : st₀.regs 14 = prevM) (hr16 : st₀.regs 16 = ecA) (hr17 : st₀.regs 17 = ecM)
    (hr18 : st₀.regs 18 = ua) (hr19 : st₀.regs 19 = ub) (hr20 : st₀.regs 20 = outEA)
    (hmem : st₀.mem = mem) :
    let pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
    let fakes := completeBatchFake pairs matchings
    Triple w p (fun st => st = st₀) scCompleteFakeLoopStmt
      (normalPost fun st' =>
        st'.regs 14 = prevM + fakes.length ∧
        (∀ r, r ≠ 14 → (r < 21 ∨ 30 ≤ r) → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ a, (a < outEA ∨ outEA + 2 * cap ≤ a) → (a < ua ∨ ua + b ≤ a) → (a < ub ∨ ub + b ≤ a) →
          st'.mem a = mem a) ∧
        EdgesAt st'.mem outEA (prevFakes ++ fakes))
      (fun _ => 140 * (ecM * b) + 150 * ecM + 30) := by
  intro pairs fakes
  have hnd_vs : vs.Nodup := hvs_s.imp fun h => Nat.ne_of_lt h
  have hvtp : ValidTerminalPairs vs.toFinset pairs :=
    validTerminalPairs_of_matching_edges hnd_vs hb_pos hEc_valid hEc_nd
  have hp_len : pairs.length = ecM := by simp [pairs, hEc_len]
  have hpm_p : ∀ j (hj : j < pairs.length),
      IsPartialMatching (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings.getD j []) := by
    intro j hj
    have hj' : j < ecM := by omega
    simpa [pairs] using hpm j hj'
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
  have hfk_le : ∀ j ≤ ecM, (completeBatchFake (pairs.take j) (matchings.take j)).length ≤ j * b := by
    intro j hj
    induction j with
    | zero => simp [completeBatchFake]
    | succ j' ih =>
      have hj' : j' < pairs.length := by omega
      rw [completeBatchFake_take_succ hj' (by omega), List.length_append]
      have h1 : (completeMatchingFake (pairs[j']'hj').1 (pairs[j']'hj').2 (matchings[j']'(by omega))).length ≤ b := by
        unfold completeMatchingFake unmatchedFst
        rw [List.length_zip]
        refine le_trans (Nat.min_le_left _ _) ?_
        rw [Finset.length_sort]
        have he_v := hEc_valid (Ec[j']'(by omega)) (List.getElem_mem _)
        have hcard : (pairs[j']'hj').1.card = b := by
          simpa [pairs] using card_blockSet hnd_vs he_v.1
        exact le_trans (Finset.card_le_card Finset.sdiff_subset) hcard.le
      have h2 := ih (by omega)
      have h3 : (j' + 1) * b = j' * b + b := by ring
      omega
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 21 = j ∧
    st.regs 14 = prevM + (completeBatchFake (pairs.take j) (matchings.take j)).length ∧
    (∀ r, r ≠ 14 → (r < 21 ∨ 30 ≤ r) → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    (∀ a, (a < outEA ∨ outEA + 2 * cap ≤ a) → (a < ua ∨ ua + b ≤ a) → (a < ub ∨ ub + b ≤ a) →
      st.mem a = mem a) ∧
    EdgesAt st.mem outEA (prevFakes ++ completeBatchFake (pairs.take j) (matchings.take j))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 21) (lo := .const 0) (hi := .reg 17)
    (body := seqStmts [
      .assign 22 (.load (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 21)))),
      .assign 23 (.load (.bin .add (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 21))) (.const 1))),
      .assign 24 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 22) (.reg 2))),
      scCollectUnmatchedStmt 24 2 9 18 25 27 28,
      .assign 24 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.reg 23) (.reg 2))),
      scCollectUnmatchedStmt 24 2 9 19 26 27 28,
      scZipAppendStmt 18 25 19 26 20 14 27 28 24 29])
    (P := fun st => st = st₀) (Inv := Inv) (140 * b + 140) 0 ecM (Nat.zero_le ecM) (by omega)
    (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hr14]; simp [completeBatchFake],
        fun r _ hlt => by dsimp only; rw [Function.update_of_ne (by omega)],
        rfl, fun a _ _ _ => congrFun hmem a, by simpa [completeBatchFake, hmem] using hprev_at⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv =>
      Expr.eval_reg_of_eq (v := ecM) (by rw [hInv.2.2.1 17 (by decide) (Or.inl (by decide)), hr17]))
    (fun j _ hjlt => by
      intro st ω ⟨hj, hcur, hoth, hpos, hfr, hE⟩
      have hj_len : j < Ec.length := hEc_len.symm ▸ hjlt
      have hj_p : j < pairs.length := by omega
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
      have hr1' : st.regs 1 = xA := (hoth 1 (by decide) (Or.inl (by decide))).trans hr1
      have hr2' : st.regs 2 = b := (hoth 2 (by decide) (Or.inl (by decide))).trans hr2
      have hr9' : st.regs 9 = la := (hoth 9 (by decide) (Or.inl (by decide))).trans hr9
      have hr16' : st.regs 16 = ecA := (hoth 16 (by decide) (Or.inl (by decide))).trans hr16
      have hr18' : st.regs 18 = ua := (hoth 18 (by decide) (Or.inl (by decide))).trans hr18
      have hr19' : st.regs 19 = ub := (hoth 19 (by decide) (Or.inl (by decide))).trans hr19
      have hr20' : st.regs 20 = outEA := (hoth 20 (by decide) (Or.inl (by decide))).trans hr20
      have hmem_e1 : st.mem (ecA + 2 * j) = ed.1 := by
        rw [hfr _ (disjointRange_outside hd_out_ec (by omega) (by omega))
          (disjointRange_outside hd_ua_ec (by omega) (by omega))
          (disjointRange_outside hd_ub_ec (by omega) (by omega))]
        exact (hEc_at j hj_len).1
      have hmem_e2 : st.mem (ecA + 2 * j + 1) = ed.2 := by
        rw [hfr _ (disjointRange_outside hd_out_ec (by omega) (by omega))
          (disjointRange_outside hd_ua_ec (by omega) (by omega))
          (disjointRange_outside hd_ub_ec (by omega) (by omega))]
        exact (hEc_at j hj_len).2
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
      refine runs_seq_assign_le (v := xA + 1 + ed.1 * b)
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_reg_of_eq (v := xA)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr1']))
            (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul
            (Expr.eval_reg_of_eq (v := ed.1)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
            (Expr.eval_reg_of_eq (v := b)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2']))
            (by omega)) (by omega)) ?_
      let stC1 : State :=
        { mem := st.mem,
          regs := Function.update (Function.update (Function.update st.regs 22 ed.1) 23 ed.2)
            24 (xA + 1 + ed.1 * b),
          pos := st.pos }
      have hblk1_st : ListAt st.mem (xA + 1 + ed.1 * b) (blockList vs b ed.1) := by
        intro t ht
        rw [blockList_length hed_v.1] at ht
        rw [hfr _ (disjointRange_outside hd_out_vs (by omega) (by omega))
          (disjointRange_outside hd_ua_vs (by omega) (by omega))
          (disjointRange_outside hd_ub_vs (by omega) (by omega))]
        exact hblk_at ed.1 hed_v.1 t (by rw [blockList_length hed_v.1]; exact ht)
      have hloc_st : ∀ u < n, st.mem (la + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 := by
        intro u hu
        rw [hfr _ (disjointRange_outside hd_out_loc (by omega) (by omega))
          (disjointRange_outside hd_ua_loc (by omega) (by omega))
          (disjointRange_outside hd_ub_loc (by omega) (by omega))]
        exact hloc u hu
      have hblk1_lt : ∀ u ∈ blockList vs b ed.1, u < n := fun u hu =>
        hvs_lt u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
      have hblk2_lt : ∀ u ∈ blockList vs b ed.2, u < n := fun u hu =>
        hvs_lt u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
      have hd_ua_b1 : DisjointRange ua b (xA + 1 + ed.1 * b) b := by
        rcases hd_ua_vs with h1 | h1 <;> [left; right] <;> omega
      refine runs_seq_triple_le
        (scCollectUnmatched_triple (by decide) p st.mem (blockList vs b ed.1)
          (matchedVerts matchings.flatten) stC1 (blockList_length hed_v.1) hblk1_st hblk1_lt
          hloc_st hd_ua_b1 hd_ua_loc (by omega) hla_w hua_w hw16
          (by dsimp only [stC1]; rw [Function.update_self])
          (by dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr2'])
          (by dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr9'])
          (by dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hr18'])
          rfl) rfl ?_
      intro stC2 ⟨hcntA, hothC2, hposC2, hfrC2, hlistA⟩
      set unmA := (blockList vs b ed.1).filter fun u => decide (u ∉ matchedVerts matchings.flatten)
      have hunmA_le : unmA.length ≤ b :=
        le_trans (List.length_filter_le _ _) (blockList_length hed_v.1).le
      have hr1_C2 : stC2.regs 1 = xA := by
        rw [hothC2 1 (by decide) (by decide) (by decide)]; dsimp only [stC1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr1']
      have hr2_C2 : stC2.regs 2 = b := by
        rw [hothC2 2 (by decide) (by decide) (by decide)]; dsimp only [stC1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr2']
      have hr9_C2 : stC2.regs 9 = la := by
        rw [hothC2 9 (by decide) (by decide) (by decide)]; dsimp only [stC1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr9']
      have hr19_C2 : stC2.regs 19 = ub := by
        rw [hothC2 19 (by decide) (by decide) (by decide)]; dsimp only [stC1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hr19']
      have hr23_C2 : stC2.regs 23 = ed.2 := by
        rw [hothC2 23 (by decide) (by decide) (by decide)]; dsimp only [stC1]
        rw [Function.update_of_ne (by decide), Function.update_self]
      refine runs_seq_assign_le (v := xA + 1 + ed.2 * b)
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq hr1_C2) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_reg_of_eq hr23_C2) (Expr.eval_reg_of_eq hr2_C2) (by omega))
          (by omega)) ?_
      let stC3 : State :=
        { mem := stC2.mem, regs := Function.update stC2.regs 24 (xA + 1 + ed.2 * b), pos := stC2.pos }
      have hblk2_C2 : ListAt stC2.mem (xA + 1 + ed.2 * b) (blockList vs b ed.2) := by
        intro t ht
        rw [blockList_length hed_v.2] at ht
        rw [hfrC2 _ (disjointRange_outside hd_ua_vs (by omega) (by omega))]
        rw [hfr _ (disjointRange_outside hd_out_vs (by omega) (by omega))
          (disjointRange_outside hd_ua_vs (by omega) (by omega))
          (disjointRange_outside hd_ub_vs (by omega) (by omega))]
        exact hblk_at ed.2 hed_v.2 t (by rw [blockList_length hed_v.2]; exact ht)
      have hloc_C2 : ∀ u < n, stC2.mem (la + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 := by
        intro u hu
        rw [hfrC2 _ (disjointRange_outside hd_ua_loc (by omega) (by omega))]
        exact hloc_st u hu
      have hd_ub_b2 : DisjointRange ub b (xA + 1 + ed.2 * b) b := by
        rcases hd_ub_vs with h1 | h1 <;> [left; right] <;> omega
      refine runs_seq_triple_le
        (scCollectUnmatched_triple (by decide) p stC2.mem (blockList vs b ed.2)
          (matchedVerts matchings.flatten) stC3 (blockList_length hed_v.2) hblk2_C2 hblk2_lt
          hloc_C2 hd_ub_b2 hd_ub_loc (by omega) hla_w hub_w hw16
          (by dsimp only [stC3]; rw [Function.update_self])
          (by dsimp only [stC3]; rw [Function.update_of_ne (by decide), hr2_C2])
          (by dsimp only [stC3]; rw [Function.update_of_ne (by decide), hr9_C2])
          (by dsimp only [stC3]; rw [Function.update_of_ne (by decide), hr19_C2])
          rfl) rfl ?_
      intro stC4 ⟨hcntB, hothC4, hposC4, hfrC4, hlistB⟩
      set unmB := (blockList vs b ed.2).filter fun u => decide (u ∉ matchedVerts matchings.flatten)
      have hunmB_le : unmB.length ≤ b :=
        le_trans (List.length_filter_le _ _) (blockList_length hed_v.2).le
      have hlistA_C4 : ListAt stC4.mem ua unmA := by
        intro t ht
        have hout : ua + t < ub ∨ ub + b ≤ ua + t := by
          rcases hd_ua_ub with h1 | h1 <;> [left; right] <;> omega
        rw [hfrC4 _ hout]
        exact hlistA t ht
      have hE_C4 : EdgesAt stC4.mem outEA
          (prevFakes ++ completeBatchFake (pairs.take j) (matchings.take j)) := by
        have hlen_c := hfk_le j (by omega)
        have hlen_p : (prevFakes ++ completeBatchFake (pairs.take j) (matchings.take j)).length =
            prevM + (completeBatchFake (pairs.take j) (matchings.take j)).length := by
          rw [List.length_append, hprev_len]
        intro t ht
        have ht_cap : t < cap := by
          have : j * b ≤ ecM * b := Nat.mul_le_mul_right b (by omega)
          omega
        have hout_b0 : outEA + 2 * t < ub ∨ ub + b ≤ outEA + 2 * t := by
          rcases hd_out_ub with h1 | h1 <;> [left; right] <;> omega
        have hout_a0 : outEA + 2 * t < ua ∨ ua + b ≤ outEA + 2 * t := by
          rcases hd_out_ua with h1 | h1 <;> [left; right] <;> omega
        have hout_b1 : outEA + 2 * t + 1 < ub ∨ ub + b ≤ outEA + 2 * t + 1 := by
          rcases hd_out_ub with h1 | h1 <;> [left; right] <;> omega
        have hout_a1 : outEA + 2 * t + 1 < ua ∨ ua + b ≤ outEA + 2 * t + 1 := by
          rcases hd_out_ua with h1 | h1 <;> [left; right] <;> omega
        have h1 : stC4.mem (outEA + 2 * t) = st.mem (outEA + 2 * t) := by
          rw [hfrC4 _ hout_b0, hfrC2 _ hout_a0]
        have h2 : stC4.mem (outEA + 2 * t + 1) = st.mem (outEA + 2 * t + 1) := by
          rw [hfrC4 _ hout_b1, hfrC2 _ hout_a1]
        rw [h1, h2]
        exact hE t ht
      have hcap_j : prevM + (completeBatchFake (pairs.take j) (matchings.take j)).length +
          min unmA.length unmB.length ≤ cap := by
        have h1 := hfk_le j (by omega)
        have h2 : (j + 1) * b ≤ ecM * b := Nat.mul_le_mul_right b hjlt
        have h3 : (j + 1) * b = j * b + b := by ring
        have h4 : min unmA.length unmB.length ≤ b := le_trans (Nat.min_le_left _ _) hunmA_le
        omega
      have hd_out_ua' : DisjointRange outEA (2 * cap) ua unmA.length := by
        rcases hd_out_ua with h1 | h1 <;> [left; right] <;> omega
      have hd_out_ub' : DisjointRange outEA (2 * cap) ub unmB.length := by
        rcases hd_out_ub with h1 | h1 <;> [left; right] <;> omega
      have hzip_tr := scZipAppend_triple
        (rUnmA := 18) (rCntA := 25) (rUnmB := 19) (rCntB := 26) (rOutEdges := 20)
        (rOutM := 14) (rLim := 27) (rI := 28) (rU := 24) (rV := 29) (by decide) p stC4.mem unmA unmB
        (prevFakes ++ completeBatchFake (pairs.take j) (matchings.take j)) stC4 rfl rfl
        (by rw [List.length_append, hprev_len]) hlistA_C4 hlistB hE_C4 hcap_j hd_out_ua' hd_out_ub'
        (by omega) (by omega) hout_w hw16
        (by rw [hothC4 18 (by decide) (by decide) (by decide)]; dsimp only [stC3]
            rw [Function.update_of_ne (by decide), hothC2 18 (by decide) (by decide) (by decide)]
            dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), hr18'])
        (by rw [hothC4 25 (by decide) (by decide) (by decide)]; dsimp only [stC3]
            rw [Function.update_of_ne (by decide), hcntA])
        (by rw [hothC4 19 (by decide) (by decide) (by decide)]; dsimp only [stC3]
            rw [Function.update_of_ne (by decide), hr19_C2])
        hcntB
        (by rw [hothC4 20 (by decide) (by decide) (by decide)]; dsimp only [stC3]
            rw [Function.update_of_ne (by decide), hothC2 20 (by decide) (by decide) (by decide)]
            dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), hr20'])
        (by rw [hothC4 14 (by decide) (by decide) (by decide)]; dsimp only [stC3]
            rw [Function.update_of_ne (by decide), hothC2 14 (by decide) (by decide) (by decide)]
            dsimp only [stC1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), hcur])
        rfl
      obtain ⟨o, stZ, cZ, hrZ, hqZ, hcZ⟩ := hzip_tr stC4 ω rfl
      cases o with
      | returned _ => exact False.elim hqZ
      | normal =>
        rcases hqZ with ⟨hr14_Z, hothZ, hposZ, hfrZ, hEZ⟩
        have hcmf_eq : completeMatchingFake (pairs[j]'hj_p).1 (pairs[j]'hj_p).2 (matchings[j]'(by omega)) =
            unmA.zip unmB :=
          completeMatchingFake_eq_of_flat hvtp (by omega) hpm_p hj_p
            (pairwise_lt_blockList hvs_s b ed.1) (pairwise_lt_blockList hvs_s b ed.2)
            (by simp [pairs, blockSet, ed]) (by simp [pairs, blockSet, ed])
        have htake_eq : completeBatchFake (pairs.take (j + 1)) (matchings.take (j + 1)) =
            completeBatchFake (pairs.take j) (matchings.take j) ++ unmA.zip unmB := by
          rw [completeBatchFake_take_succ hj_p (by omega), hcmf_eq]
        refine ⟨.normal, stZ, cZ, hrZ, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · simp
        · dsimp only
          rw [Function.update_of_ne (by decide), hr14_Z, htake_eq, List.length_append,
            List.length_zip]
          omega
        · intro r hne14 hlt21
          dsimp only
          rw [Function.update_of_ne (by omega),
            hothZ r hne14 (by omega) (by omega) (by omega) (by omega),
            hothC4 r (by omega) (by omega) (by omega)]
          dsimp only [stC3]
          rw [Function.update_of_ne (by omega), hothC2 r (by omega) (by omega) (by omega)]
          dsimp only [stC1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hoth r hne14 hlt21
        · rw [hposZ, hposC4]; exact hposC2.trans hpos
        · intro a ha_o ha_a ha_b
          rw [hfrZ a ha_o, hfrC4 a ha_b, hfrC2 a ha_a, hfr a ha_o ha_a ha_b]
        · rwa [htake_eq, ← List.append_assoc]
        · rw [hothZ 21 (by decide) (by decide) (by decide) (by decide) (by decide),
            hothC4 21 (by decide) (by decide) (by decide)]
          dsimp only [stC3]
          rw [Function.update_of_ne (by decide), hothC2 21 (by decide) (by decide) (by decide)]
          dsimp only [stC1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hj]
        · have hmin_le : min unmA.length unmB.length ≤ b := le_trans (Nat.min_le_left _ _) hunmA_le
          simp only [Expr.size] at hcZ ⊢
          omega)
  dsimp only [scCompleteFakeLoopStmt]
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => ?_)
  · rintro (_ | v) st' hInv
    · rcases hInv with ⟨_, hr14', hoth', hpos', hfr', hE'⟩
      have hp_t : pairs.take ecM = pairs := by rw [← hp_len, List.take_length]
      have hm_t : matchings.take ecM = matchings := by rw [← hmlen, List.take_length]
      rw [hp_t, hm_t] at hr14' hE'
      exact ⟨hr14', hoth', hpos', hfr', hE'⟩
    · exact hInv.elim
  · simp only [Expr.size, Nat.sub_zero]
    have hmul : ecM * (140 * b + 140 + 1 + 8) = 140 * (ecM * b) + 149 * ecM := by ring
    omega

/-- Post-router matched branch of `scOneColorStmt`: marks all endpoints of `matchings.flatten`
in `locAddr`, allocates scratch arrays `ua = hAfterRt`, `ub = hAfterRt + b`, advances `r12` to
`hAfterRt + 2 * b`, runs `scCompleteFakeLoopStmt`, and unmarks `locAddr` back to `0`. -/
def scMatchedPostStmt : Stmt :=
  seqStmts [
    .assign 30 (.load (.bin .add (.reg 19) (.const 1))),
    .assign 31 (.bin .add (.reg 19) (.const 2)),
    scSetMatchedStmt 30 31 9 24 25 26 1,
    .assign 18 (.reg 12),
    .assign 19 (.bin .add (.reg 12) (.reg 2)),
    .assign 20 (.bin .add (.reg 10) (.const 2)),
    .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 2))),
    scCompleteFakeLoopStmt,
    scSetMatchedStmt 30 31 9 24 25 26 0
  ]

theorem scMatchedPostStmt_noRand : scMatchedPostStmt.NoRand := by
  simp [scMatchedPostStmt, scSetMatchedStmt, scCompleteFakeLoopStmt,
    scCollectUnmatchedStmt, scZipAppendStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Triple for `scMatchedPostStmt`: marks `matchings.flatten` in `locAddr`, appends
`completeBatchFake pairs matchings` to `outA + 2 + 2 * prevM`, restores `locAddr` to all zeros,
and advances `r12` to `hAfterRt + 2 * b`. -/
lemma scMatchedPost_triple {w n xA b ecM ecA la outA hAfterRt pEnd prevM cap : ℕ}
    (p : Program) (mem : ℕ → ℕ) (vs : List ℕ) (Ec : List (ℕ × ℕ))
    (matchings : List (List (ℕ × ℕ))) (prevFakes : List (ℕ × ℕ)) (st₀ : State)
    (hvs_at : LenListAt mem xA vs) (hvs_s : vs.Pairwise (· < ·))
    (hvs_lt : ∀ u ∈ vs, u < n)
    (hEc_len : Ec.length = ecM) (hEc_at : EdgesAt mem ecA Ec)
    (hEc_valid : ∀ e ∈ Ec, e.1 < numFullBlocks vs b ∧ e.2 < numFullBlocks vs b)
    (hEc_nd : (Ec.flatMap fun e => [e.1, e.2]).Nodup) (hb_pos : 0 < b)
    (hmlen : matchings.length = ecM)
    (hpm : ∀ j (hj : j < ecM),
      IsPartialMatching (blockSet vs b (Ec[j]'(by omega)).1)
        (blockSet vs b (Ec[j]'(by omega)).2) (matchings.getD j []))
    (hmLen : mem (pEnd + 1) = matchings.flatten.length)
    (hmAt : EdgesAt mem (pEnd + 2) matchings.flatten)
    (hflat_lt : ∀ e ∈ matchings.flatten, e.1 < n ∧ e.2 < n)
    (hloc0 : ∀ u < n, mem (la + u) = 0)
    (hprev_len : prevFakes.length = prevM) (hprev_at : EdgesAt mem (outA + 2) prevFakes)
    (hcap : prevM + ecM * b ≤ cap)
    (hcap_fk : prevM + (completeBatchFake (Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)) matchings).length ≤ cap)
    (hla_pEnd : la + n ≤ pEnd)
    (hpEnd_h : pEnd + 2 + 2 * matchings.flatten.length ≤ hAfterRt)
    (hx_h : xA + 1 + vs.length ≤ hAfterRt)
    (hec_h : ecA + 2 * ecM ≤ hAfterRt)
    (hla_h : la + n ≤ hAfterRt)
    (hout_pEnd : outA + 2 + 2 * cap ≤ pEnd)
    (hout_ec : outA + 2 + 2 * cap ≤ ecA)
    (hd_out_vs : DisjointRange (outA + 2) (2 * cap) (xA + 1) vs.length)
    (hd_out_loc : DisjointRange (outA + 2) (2 * cap) la n)
    (hd_loc_vs : DisjointRange la n xA (1 + vs.length))
    (hd_loc_ec : DisjointRange la n ecA (2 * ecM))
    (hh_w : hAfterRt + 2 * b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr1 : st₀.regs 1 = xA) (hr2 : st₀.regs 2 = b) (hr9 : st₀.regs 9 = la)
    (hr10 : st₀.regs 10 = outA) (hr12 : st₀.regs 12 = hAfterRt)
    (hr14 : st₀.regs 14 = prevM) (hr16 : st₀.regs 16 = ecA)
    (hr17 : st₀.regs 17 = ecM) (hr19 : st₀.regs 19 = pEnd)
    (hmem : st₀.mem = mem) :
    let pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
    let fakes := completeBatchFake pairs matchings
    Triple w p (fun st => st = st₀) scMatchedPostStmt
      (normalPost fun st' =>
        st'.regs 12 = hAfterRt + 2 * b ∧
        st'.regs 14 = prevM + fakes.length ∧
        (∀ r, r ≠ 12 → r ≠ 14 → r < 18 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        (∀ u < n, st'.mem (la + u) = 0) ∧
        (∀ a, (a < la ∨ la + n ≤ a) → (a < outA + 2 ∨ outA + 2 + 2 * cap ≤ a) →
          (a < hAfterRt ∨ hAfterRt + 2 * b ≤ a) → st'.mem a = mem a) ∧
        EdgesAt st'.mem (outA + 2) (prevFakes ++ fakes))
      (fun _ => 108 * matchings.flatten.length + 140 * (ecM * b) + 150 * ecM + 120) := by
  intro pairs fakes st ω hst
  subst st
  set mE := matchings.flatten.length
  refine runs_start_le ?_
  dsimp only [scMatchedPostStmt, seqStmts]
  refine runs_seq_assign_le (v := mE)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr19) (Expr.eval_const (by omega)) (by omega))
      (hmem ▸ hmLen)) ?_
  refine runs_seq_assign_le (v := pEnd + 2)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := pEnd) (by dsimp only; rw [Function.update_of_ne (by decide), hr19]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  let st1 : State :=
    { mem := st₀.mem, regs := Function.update (Function.update st₀.regs 30 mE) 31 (pEnd + 2), pos := st₀.pos }
  refine runs_seq_triple_le
    (scSetMatched_triple (la := la) (rM := 30) (rEdges := 31) (rLoc := 9) (rI := 24) (rU := 25) (rV := 26)
      (val := 1) (by decide) p mem matchings.flatten st1 rfl hmAt hflat_lt
      (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st1]; rw [Function.update_self])
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr9])
      hmem) rfl ?_
  intro st2 ⟨hoth2, hpos2, hfr2, hloc2⟩
  have hst2_lt18 : ∀ r < 18, st2.regs r = st₀.regs r := fun r hr => by
    rw [hoth2 r (by omega) (by omega) (by omega)]
    dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hr30_2 : st2.regs 30 = mE := by
    rw [hoth2 30 (by decide) (by decide) (by decide)]
    dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr31_2 : st2.regs 31 = pEnd + 2 := by
    rw [hoth2 31 (by decide) (by decide) (by decide)]
    dsimp only [st1]; rw [Function.update_self]
  have hr2_2 : st2.regs 2 = b := (hst2_lt18 2 (by decide)).trans hr2
  have hr10_2 : st2.regs 10 = outA := (hst2_lt18 10 (by decide)).trans hr10
  have hr12_2 : st2.regs 12 = hAfterRt := (hst2_lt18 12 (by decide)).trans hr12
  refine runs_seq_assign_le (v := hAfterRt) (Expr.eval_reg_of_eq hr12_2) ?_
  refine runs_seq_assign_le (v := hAfterRt + b)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := hAfterRt) (by dsimp only; rw [Function.update_of_ne (by decide), hr12_2]))
      (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide), hr2_2]))
      (by omega)) ?_
  refine runs_seq_assign_le (v := outA + 2)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := outA) (by dsimp only; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hr10_2]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := hAfterRt + 2 * b)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := hAfterRt) (by dsimp only; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr12_2]))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (v := b) (by dsimp only; rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_2]))
        (by omega))
      (by omega)) ?_
  let st3 : State :=
    { mem := st2.mem,
      regs := Function.update (Function.update (Function.update (Function.update st2.regs 18 hAfterRt)
        19 (hAfterRt + b)) 20 (outA + 2)) 12 (hAfterRt + 2 * b),
      pos := st2.pos }
  have hvs_2 : LenListAt st2.mem xA vs := by
    refine ⟨?_, fun i hi => ?_⟩
    · have hdisj : xA < la ∨ la + n ≤ xA := by
        rcases hd_loc_vs with h | h <;> [right; left] <;> omega
      rw [hfr2 _ hdisj]; exact hvs_at.1
    · have hdisj : xA + 1 + i < la ∨ la + n ≤ xA + 1 + i := by
        rcases hd_loc_vs with h | h <;> [right; left] <;> omega
      rw [hfr2 _ hdisj]; exact hvs_at.2 i hi
  have hEc_2 : EdgesAt st2.mem ecA Ec := fun j hj => by
    have h1 : ecA + 2 * j < la ∨ la + n ≤ ecA + 2 * j := by
      rcases hd_loc_ec with h | h <;> [right; left] <;> omega
    have h2 : ecA + 2 * j + 1 < la ∨ la + n ≤ ecA + 2 * j + 1 := by
      rcases hd_loc_ec with h | h <;> [right; left] <;> omega
    rw [hfr2 _ h1, hfr2 _ h2]; exact hEc_at j hj
  have hloc_2_exact : ∀ u < n, st2.mem (la + u) = if u ∈ matchedVerts matchings.flatten then 1 else 0 :=
    fun u hu => by rw [hloc2 u hu, hloc0 u hu]
  have hprev_2 : EdgesAt st2.mem (outA + 2) prevFakes := fun j hj => by
    have h1 : outA + 2 + 2 * j < la ∨ la + n ≤ outA + 2 + 2 * j := by
      rcases hd_out_loc with h | h <;> [left; right] <;> omega
    have h2 : outA + 2 + 2 * j + 1 < la ∨ la + n ≤ outA + 2 + 2 * j + 1 := by
      rcases hd_out_loc with h | h <;> [left; right] <;> omega
    rw [hfr2 _ h1, hfr2 _ h2]; exact hprev_at j hj
  refine runs_seq_triple_le
    (scCompleteFakeLoop_triple (cap := cap) p st2.mem vs Ec matchings prevFakes st3
      hvs_2 hvs_s hvs_lt hEc_len hEc_2 hEc_valid hEc_nd hb_pos hmlen hpm hloc_2_exact
      hprev_len hprev_2 hcap hd_out_vs (Or.inl hout_ec) hd_out_loc
      (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inr hx_h) (Or.inr hec_h) (Or.inr hla_h) (Or.inl le_rfl)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hw16
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 1 (by decide), hr1])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_2])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 9 (by decide), hr9])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 14 (by decide), hr14])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 16 (by decide), hr16])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 17 (by decide), hr17])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self])
      (by dsimp only [st3]; rw [Function.update_of_ne (by decide), Function.update_self])
      rfl) rfl ?_
  intro st4 ⟨hr14_4, hoth4, hpos4, hfr4, hE4⟩
  have hmAt_4 : EdgesAt st4.mem (pEnd + 2) matchings.flatten := fun j hj => by
    have h1 := hfr4 (pEnd + 2 + 2 * j) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have h2 := hfr4 (pEnd + 2 + 2 * j + 1) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have h3 := hfr2 (pEnd + 2 + 2 * j) (Or.inr (by omega))
    have h4 := hfr2 (pEnd + 2 + 2 * j + 1) (Or.inr (by omega))
    rw [h1, h2, h3, h4]; exact hmAt j hj
  refine runs_triple_le
    (scSetMatched_triple (la := la) (rM := 30) (rEdges := 31) (rLoc := 9) (rI := 24) (rU := 25) (rV := 26)
      (val := 0) (by decide) p st4.mem matchings.flatten st4 rfl hmAt_4 hflat_lt
      (Or.inl (by omega)) (by omega) (by omega) (by omega) hw16
      (by rw [hoth4 30 (by decide) (Or.inr (by decide))]
          dsimp only [st3]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr30_2])
      (by rw [hoth4 31 (by decide) (Or.inr (by decide))]
          dsimp only [st3]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr31_2])
      (by rw [hoth4 9 (by decide) (Or.inl (by decide))]
          dsimp only [st3]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst2_lt18 9 (by decide), hr9])
      rfl)
    rfl ?_ (by simp only [Expr.size]; omega)
  rintro (_ | _) st5 hq
  · rcases hq with ⟨hoth5, hpos5, hfr5, hloc5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hoth5 12 (by decide) (by decide) (by decide), hoth4 12 (by decide) (Or.inl (by decide))]
      dsimp only [st3]; rw [Function.update_self]
    · rw [hoth5 14 (by decide) (by decide) (by decide), hr14_4]
    · intro r h12 h14 h18
      rw [hoth5 r (by omega) (by omega) (by omega), hoth4 r h14 (Or.inl (by omega))]
      dsimp only [st3]
      rw [Function.update_of_ne h12, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hst2_lt18 r h18
    · exact hpos5.trans (hpos4.trans hpos2)
    · intro u hu
      rw [hloc5 u hu]
      split_ifs with hm
      · rfl
      · have hdisj_lo : la + u < outA + 2 ∨ outA + 2 + 2 * cap ≤ la + u := by
          rcases hd_out_loc with h | h <;> [right; left] <;> omega
        rw [hfr4 (la + u) hdisj_lo (Or.inl (by omega)) (Or.inl (by omega)), hloc_2_exact u hu]
        simp [hm]
    · intro a ha_l ha_o ha_h
      rw [hfr5 a ha_l, hfr4 a ha_o (by rcases ha_h with h | h <;> [left; right] <;> omega)
        (by rcases ha_h with h | h <;> [left; right] <;> omega), hfr2 a ha_l]
    · intro j hj
      have hj_len : j < cap := by
        rw [List.length_append, hprev_len] at hj
        have hfk_c : prevM + fakes.length ≤ cap := hcap_fk
        omega
      have h1 : outA + 2 + 2 * j < la ∨ la + n ≤ outA + 2 + 2 * j := by
        rcases hd_out_loc with h | h <;> [left; right] <;> omega
      have h2 : outA + 2 + 2 * j + 1 < la ∨ la + n ≤ outA + 2 + 2 * j + 1 := by
        rcases hd_out_loc with h | h <;> [left; right] <;> omega
      rw [hfr5 _ h1, hfr5 _ h2]; exact hE4 j hj
  · exact False.elim hq

end MinCostFlow.ExpanderDecomp
