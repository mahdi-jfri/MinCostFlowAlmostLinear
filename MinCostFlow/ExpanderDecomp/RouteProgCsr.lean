module

public import MinCostFlow.ExpanderDecomp.RouteProgCsrBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Compact Local Induced-Subgraph CSR Builder (`buildLocalCsr_meetsContract`)

Verifies Pass 2 (`csrFillAdjStmt`) and assembles the full deterministic Word-RAM contract
`buildLocalCsr_meetsContract` for `buildLocalCsrProc bSort`: from `GraphAt mem gAddr G`,
`VertSetAt mem xAddr X`, and `ZeroFrom mem workAddr`, produces `ListAt _ origVert (sortedX X)`,
local-ID map `locId[u] = if u ∈ X then locOf X u + 1 else 0`, and
`AdjCsrAt _ offAddr nbAddr edgeAddr X (adjOf G X)` in
`O(|X| · (log(|X| + 2) + 1) + G.m + 1)` time without scanning `range G.n`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma csrFillAdj_triple {w : ℕ} {p : Program}
    {gAddr xAddr workAddr : ℕ} {G : Graph} {X : Finset ℕ}
    {mem4 : ℕ → ℕ} {st4 : State}
    (hG : GraphAt mem4 gAddr G) (hG_val : G.IsValid)
    (hg_disj : gAddr + G.encode.length ≤ workAddr)
    (hloc : ∀ u < G.n, mem4 (csrLocIdAddr workAddr X.card G.m + u) =
      if u ∈ X then locOf X u + 1 else 0)
    (hoff : ∀ i ≤ X.card, mem4 (csrOffAddr workAddr X.card + i) = adjCsrOff X (adjOf G X) i)
    (hwcur : ∀ i < X.card, mem4 (csrWCurAddr workAddr X.card + i) = adjCsrOff X (adjOf G X) i)
    (hw : workAddr + localCsrSpace G.n G.m X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs : ∀ r ≤ 10, st4.regs r =
      match r with
      | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
      | 6 => csrOffAddr workAddr X.card
      | 7 => csrWCurAddr workAddr X.card
      | 8 => csrNbAddr workAddr X.card
      | 9 => csrEdgeAddr workAddr X.card G.m
      | _ => csrLocIdAddr workAddr X.card G.m)
    (hmem4 : st4.mem = mem4) :
    Triple w p
      (fun st => st = st4)
      csrFillAdjStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st4.regs r) ∧
        AdjCsrAt st'.mem (csrOffAddr workAddr X.card) (csrNbAddr workAddr X.card)
          (csrEdgeAddr workAddr X.card G.m) X (adjOf G X) ∧
        (∀ a, (a < csrWCurAddr workAddr X.card ∨
               csrLocIdAddr workAddr X.card G.m ≤ a) → st'.mem a = mem4 a))
      (fun _ => 130 * G.m + 20) := by
  wram_enter
  · subst st
    dsimp only [csrFillAdjStmt, seqStmts]
    wram_step
    let offBase := csrOffAddr workAddr X.card
    let wcurBase := csrWCurAddr workAddr X.card
    let nbBase := csrNbAddr workAddr X.card
    let edgeBase := csrEdgeAddr workAddr X.card G.m
    let locBase := csrLocIdAddr workAddr X.card G.m
    have htotal_le : adjCsrOff X (adjOf G X) X.card ≤ 2 * G.m := by
      rw [adjCsrOff_adjOf_card]
      have : (G.inside X).length ≤ G.m := List.length_filter_le _ _
      omega
    have hsp :
        offBase + X.card + 1 = wcurBase ∧
        wcurBase + X.card = nbBase ∧
        nbBase + 2 * G.m = edgeBase ∧
        edgeBase + 2 * G.m = locBase ∧
        locBase + G.n = workAddr + localCsrSpace G.n G.m X.card := by
      dsimp only [offBase, wcurBase, nbBase, edgeBase, locBase,
        csrOffAddr, csrWCurAddr, csrNbAddr, csrEdgeAddr, csrLocIdAddr, localCsrSpace]
      omega
    have hloop :
        Triple w p
          (fun st =>
            (∀ r ≤ 10, st.regs r = st4.regs r) ∧
            st.regs 11 ≤ G.m ∧
            (∀ i < X.card, st.mem (wcurBase + i) =
              adjCsrOff X (adjOf G X) i + (adjOfTake G X (st.regs 11) (origOf X i)).length) ∧
            (∀ i < X.card, ∀ r (hr : r < (adjOfTake G X (st.regs 11) (origOf X i)).length),
              st.mem (nbBase + adjCsrOff X (adjOf G X) i + r) =
                locOf X ((adjOfTake G X (st.regs 11) (origOf X i))[r]'hr).1 ∧
              st.mem (edgeBase + adjCsrOff X (adjOf G X) i + r) =
                ((adjOfTake G X (st.regs 11) (origOf X i))[r]'hr).2) ∧
            (∀ a, (a < wcurBase ∨ locBase ≤ a) → st.mem a = mem4 a))
          (.loop (.bin .lt (.reg 11) (.reg 4))
            (seqStmts
              [ .assign 12 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
                  (.bin .mul (.const 2) (.reg 11))))
              , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 3))
                  (.bin .mul (.const 2) (.reg 11))))
              , .assign 14 (.load (.bin .add (.reg 10) (.reg 12)))
              , .assign 15 (.load (.bin .add (.reg 10) (.reg 13)))
              , .cond (.reg 14)
                  (.cond (.reg 15)
                    (seqStmts
                      [ .assign 14 (.bin .sub (.reg 14) (.const 1))
                      , .assign 15 (.bin .sub (.reg 15) (.const 1))
                      , .assign 12 (.load (.bin .add (.reg 7) (.reg 14)))
                      , .store (.bin .add (.reg 8) (.reg 12)) (.reg 15)
                      , .store (.bin .add (.reg 9) (.reg 12)) (.reg 11)
                      , .store (.bin .add (.reg 7) (.reg 14)) (.bin .add (.reg 12) (.const 1))
                      , .assign 13 (.load (.bin .add (.reg 7) (.reg 15)))
                      , .store (.bin .add (.reg 8) (.reg 13)) (.reg 14)
                      , .store (.bin .add (.reg 9) (.reg 13)) (.reg 11)
                      , .store (.bin .add (.reg 7) (.reg 15)) (.bin .add (.reg 13) (.const 1)) ])
                    .nop)
                  .nop
              , .assign 11 (.bin .add (.reg 11) (.const 1)) ]))
          (normalPost fun st' =>
            (∀ r ≤ 10, st'.regs r = st4.regs r) ∧
            st'.regs 11 = G.m ∧
            (∀ i < X.card, ∀ r (hr : r < (adjOf G X (origOf X i)).length),
              st'.mem (nbBase + adjCsrOff X (adjOf G X) i + r) =
                locOf X ((adjOf G X (origOf X i))[r]'hr).1 ∧
              st'.mem (edgeBase + adjCsrOff X (adjOf G X) i + r) =
                ((adjOf G X (origOf X i))[r]'hr).2) ∧
            (∀ a, (a < wcurBase ∨ locBase ≤ a) → st'.mem a = mem4 a))
          (fun st => ((Expr.bin .lt (.reg 11) (.reg 4)).size + 120 + 1) * (G.m - st.regs 11) +
            (Expr.bin .lt (.reg 11) (.reg 4)).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => G.m - st.regs 11)
        (condVal := fun st => if st.regs 11 < G.m then 1 else 0)
        (bodyBound := 120) ?_ ?_ ?_
      · intro stL ⟨hr, _, _, _, _⟩
        have hr4 : stL.regs 4 = G.m := by rw [hr 4 (by decide)]; exact hregs 4 (by decide)
        eval_expr
      · intro stL ⟨hr, _, _, hadj, hframe⟩ hv
        have heq : stL.regs 11 = G.m := by split_ifs at hv; omega
        refine ⟨hr, heq, ?_, hframe⟩
        intro i hi r hr_r
        have hEq := adjOfTake_m G X (origOf X i)
        have hr' : r < (adjOfTake G X (stL.regs 11) (origOf X i)).length := by rw [heq, hEq]; exact hr_r
        have hget : (adjOfTake G X (stL.regs 11) (origOf X i))[r]'hr' =
            (adjOf G X (origOf X i))[r]'hr_r := by
          revert hr'; rw [heq, hEq]; intro _; rfl
        have h := hadj i hi r hr'
        rwa [hget] at h
      · intro stL ⟨hr, hle, hwc, hadj, hframe⟩ hv
        have hr0 : stL.regs 0 = gAddr := by rw [hr 0 (by decide)]; exact hregs 0 (by decide)
        have hr4 : stL.regs 4 = G.m := by rw [hr 4 (by decide)]; exact hregs 4 (by decide)
        have hr7 : stL.regs 7 = wcurBase := by rw [hr 7 (by decide)]; exact hregs 7 (by decide)
        have hr8 : stL.regs 8 = nbBase := by rw [hr 8 (by decide)]; exact hregs 8 (by decide)
        have hr9 : stL.regs 9 = edgeBase := by rw [hr 9 (by decide)]; exact hregs 9 (by decide)
        have hr10 : stL.regs 10 = locBase := by rw [hr 10 (by decide)]; exact hregs 10 (by decide)
        have hlt : stL.regs 11 < G.m := by split_ifs at hv <;> omega
        set j := stL.regs 11 with hj_def
        set e := G.edges[j]'hlt with he_def
        have he_val : e.1 < G.n ∧ e.2 < G.n := hG_val e (List.getElem_mem hlt)
        have hgl : G.encode.length = 2 + 2 * G.m := graph_encode_length G
        have ha_mem : stL.mem (gAddr + 2 + 2 * j) = e.1 := by
          rw [hframe _ (Or.inl (by dsimp only [wcurBase, csrWCurAddr]; omega))]
          exact graphAt_edge_fst hG hlt
        have hb_mem : stL.mem (gAddr + 3 + 2 * j) = e.2 := by
          rw [hframe _ (Or.inl (by dsimp only [wcurBase, csrWCurAddr]; omega))]
          exact graphAt_edge_snd hG hlt
        have hla_mem : stL.mem (locBase + e.1) = if e.1 ∈ X then locOf X e.1 + 1 else 0 := by
          rw [hframe _ (Or.inr (by omega))]; exact hloc e.1 he_val.1
        have hlb_mem : stL.mem (locBase + e.2) = if e.2 ∈ X then locOf X e.2 + 1 else 0 := by
          rw [hframe _ (Or.inr (by omega))]; exact hloc e.2 he_val.2
        wram_enter
        · subst st
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := e.1) (by rw [← ha_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := e.2) (by rw [← hb_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := if e.1 ∈ X then locOf X e.1 + 1 else 0)
            (by rw [← hla_mem]; eval_expr) ?_
          refine runs_seq_assign_le (v := if e.2 ∈ X then locOf X e.2 + 1 else 0)
            (by rw [← hlb_mem]; eval_expr) ?_
          by_cases he1 : e.1 ∈ X
          · have hia_lt : locOf X e.1 < X.card := locOf_lt he1
            refine runs_seq_cond_le (v := locOf X e.1 + 1) (by simp only [he1, ↓reduceIte]; eval_expr)
              (fun _ => ?_) (fun h0 => absurd h0 (Nat.succ_ne_zero _))
            by_cases he2 : e.2 ∈ X
            · have hib_lt : locOf X e.2 < X.card := locOf_lt he2
              refine runs_seq_cond_le (v := locOf X e.2 + 1) (by simp only [he2, ↓reduceIte]; eval_expr)
                (fun _ => ?_) (fun h0 => absurd h0 (Nat.succ_ne_zero _))
              set ia := locOf X e.1
              set ib := locOf X e.2
              have h_orig_ia : origOf X ia = e.1 := origOf_locOf he1
              have h_orig_ib : origOf X ib = e.2 := origOf_locOf he2
              have hlen_a_succ : (adjOfTake G X (j + 1) e.1).length ≤ (adjOf G X e.1).length :=
                adjOfTake_length_le G X (Nat.succ_le_of_lt hlt) e.1
              have hlen_b_succ : (adjOfTake G X (j + 1) e.2).length ≤ (adjOf G X e.2).length :=
                adjOfTake_length_le G X (Nat.succ_le_of_lt hlt) e.2
              have htake_a := adjOfTake_succ G X hlt e.1
              have htake_b := adjOfTake_succ G X hlt e.2
              set p1 := adjCsrOff X (adjOf G X) ia + (adjOfTake G X j e.1).length
              set p2 := adjCsrOff X (adjOf G X) ib + (adjOfTake G X j e.2).length +
                (if ia = ib then 1 else 0)
              have hp1_eq : stL.mem (wcurBase + ia) = p1 := by
                rw [hwc ia hia_lt, h_orig_ia]
              have hp1_lt_off : p1 < adjCsrOff X (adjOf G X) (ia + 1) := by
                rw [adjCsrOff_succ, h_orig_ia]
                dsimp only [p1]
                rw [← he_def] at htake_a
                have : (adjOfTake G X j e.1).length + 1 ≤ (adjOfTake G X (j + 1) e.1).length := by
                  rw [htake_a]; simp [he1, he2]
                omega
              have hp1_lt_2m : p1 < 2 * G.m := by
                have hmono := adjCsrOff_mono X (adjOf G X) (by omega : ia + 1 ≤ X.card)
                omega
              have hp2_lt_off : p2 < adjCsrOff X (adjOf G X) (ib + 1) := by
                rw [adjCsrOff_succ, h_orig_ib]
                dsimp only [p2]
                rw [← he_def] at htake_b
                by_cases hab : ia = ib
                · have heq12 : e.1 = e.2 := by
                    rw [← h_orig_ia, ← h_orig_ib, hab]
                  have : (adjOfTake G X j e.2).length + 2 ≤ (adjOfTake G X (j + 1) e.2).length := by
                    rw [htake_b]; simp [he2, heq12]
                  simp [hab]; omega
                · have : (adjOfTake G X j e.2).length + 1 ≤ (adjOfTake G X (j + 1) e.2).length := by
                    rw [htake_b]; simp [he1, he2]
                  simp [hab]; omega
              have hp2_lt_2m : p2 < 2 * G.m := by
                have hmono := adjCsrOff_mono X (adjOf G X) (by omega : ib + 1 ≤ X.card)
                omega
              have hp2_mem :
                  Function.update
                    (Function.update
                      (Function.update stL.mem (nbBase + p1) ib)
                      (edgeBase + p1) j)
                    (wcurBase + ia) (p1 + 1)
                    (wcurBase + ib) = p2 := by
                by_cases hab : ia = ib
                · rw [hab, Function.update_self]
                  have heq12 : e.1 = e.2 := by rw [← h_orig_ia, ← h_orig_ib, hab]
                  dsimp only [p1, p2]; rw [hab, heq12]; simp
                · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), hwc ib hib_lt, h_orig_ib]
                  dsimp only [p2]; simp [hab]
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := ia)
                (by (conv_rhs => rw [← Nat.add_sub_cancel ia 1]); simp only [he1, ↓reduceIte]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := ib)
                (by (conv_rhs => rw [← Nat.add_sub_cancel ib 1]); simp only [he2, ↓reduceIte]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := p1) (by rw [← hp1_eq]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := nbBase + p1) (v := ib) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := edgeBase + p1) (v := j) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := wcurBase + ia) (v := p1 + 1) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_assign_le (v := p2) (by rw [← hp2_mem]; eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := nbBase + p2) (v := ia) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_assoc_le ?_
              refine runs_seq_store_le (x := edgeBase + p2) (v := j) (by eval_expr) (by eval_expr) ?_
              refine runs_seq_store_le (x := wcurBase + ib) (v := p2 + 1) (by eval_expr) (by eval_expr) ?_
              wram_step
              · dsimp only [normalPost]
                refine ⟨⟨fun r hr' => by
                    simp only [Function.update_of_ne (by omega : r ≠ 11),
                      Function.update_of_ne (by omega : r ≠ 12),
                      Function.update_of_ne (by omega : r ≠ 13),
                      Function.update_of_ne (by omega : r ≠ 14),
                      Function.update_of_ne (by omega : r ≠ 15)]
                    exact hr r hr',
                  by simp [← hj_def]; omega, ?_, ?_, ?_⟩, by simp [← hj_def]; omega⟩
                · intro i hi
                  simp only [Function.update_self, ← hj_def]
                  rw [adjOfTake_succ G X hlt (origOf X i), ← he_def]
                  simp only [he1, he2, and_self, ↓reduceIte, List.length_append]
                  have hia_iff : e.1 = origOf X i ↔ i = ia :=
                    ⟨fun h => by dsimp only [ia]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, origOf_locOf he1]⟩
                  have hib_iff : e.2 = origOf X i ↔ i = ib :=
                    ⟨fun h => by dsimp only [ib]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, origOf_locOf he2]⟩
                  have h1_eq : (if e.1 = origOf X i then [(e.2, j)] else []).length =
                      if i = ia then 1 else 0 := by simp only [hia_iff]; split_ifs <;> simp
                  have h2_eq : (if e.2 = origOf X i then [(e.1, j)] else []).length =
                      if i = ib then 1 else 0 := by simp only [hib_iff]; split_ifs <;> simp
                  rw [h1_eq, h2_eq]
                  by_cases hi2 : i = ib
                  · subst hi2
                    rw [Function.update_self]
                    by_cases hi1 : ib = ia
                    · have heq12 : e.1 = e.2 := by rw [← h_orig_ia, ← h_orig_ib, hi1]
                      dsimp only [p2]; rw [hi1]; simp [h_orig_ia, heq12]; omega
                    · dsimp only [p2]; simp [hi1, Ne.symm hi1, h_orig_ib]; omega
                  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                      Function.update_of_ne (by omega)]
                    by_cases hi1 : i = ia
                    · subst hi1
                      rw [Function.update_self]
                      dsimp only [p1]; simp [hi2, h_orig_ia]; omega
                    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                        Function.update_of_ne (by omega), hwc i hi]
                      simp [hi1, hi2]
                · intro i hi r hr_r
                  simp only [Function.update_self, ← hj_def] at hr_r ⊢
                  have h_off_r_lt : adjCsrOff X (adjOf G X) i + r < adjCsrOff X (adjOf G X) (i + 1) := by
                    rw [adjCsrOff_succ]
                    have := adjOfTake_length_le G X (by omega : j + 1 ≤ G.m) (origOf X i)
                    omega
                  have h_off_r_2m : adjCsrOff X (adjOf G X) i + r < 2 * G.m := by
                    have := adjCsrOff_mono X (adjOf G X) (by omega : i + 1 ≤ X.card)
                    omega
                  have hne_idx : ∀ k < X.card, ∀ q < (adjOf G X (origOf X k)).length,
                      i ≠ k → adjCsrOff X (adjOf G X) i + r ≠ adjCsrOff X (adjOf G X) k + q := by
                    intro k hk q hq hik
                    rcases lt_or_gt_of_ne hik with hlt' | hgt'
                    · have hm := adjCsrOff_mono X (adjOf G X) (by omega : i + 1 ≤ k)
                      omega
                    · have hm := adjCsrOff_mono X (adjOf G X) (by omega : k + 1 ≤ i)
                      have hs := adjCsrOff_succ X (adjOf G X) k
                      omega
                  have htake_i : adjOfTake G X (j + 1) (origOf X i) =
                      adjOfTake G X j (origOf X i) ++
                        ((if e.1 = origOf X i then [(e.2, j)] else []) ++
                         (if e.2 = origOf X i then [(e.1, j)] else [])) := by
                    have h := adjOfTake_succ G X hlt (origOf X i)
                    dsimp only at h
                    rw [← he_def] at h
                    simpa only [he1, he2, and_self, ↓reduceIte] using h
                  have hia_iff : e.1 = origOf X i ↔ i = ia :=
                    ⟨fun h => by dsimp only [ia]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, h_orig_ia]⟩
                  have hib_iff : e.2 = origOf X i ↔ i = ib :=
                    ⟨fun h => by dsimp only [ib]; rw [h, locOf_origOf hi],
                     fun h => by rw [h, h_orig_ib]⟩
                  by_cases hr_old : r < (adjOfTake G X j (origOf X i)).length
                  · have hget_old : (adjOfTake G X (j + 1) (origOf X i))[r]'hr_r =
                        (adjOfTake G X j (origOf X i))[r]'hr_old := by
                      rw [adjOfTake_getElem_eq G X (Nat.succ_le_of_lt hlt) hr_r,
                          adjOfTake_getElem_eq G X (Nat.le_of_lt hlt) hr_old]
                    have hne_p1 : adjCsrOff X (adjOf G X) i + r ≠ p1 := by
                      by_cases hi1 : i = ia
                      · subst hi1; dsimp only [p1]; rw [h_orig_ia] at hr_old; omega
                      · dsimp only [p1]
                        have hq : (adjOfTake G X j e.1).length < (adjOf G X (origOf X ia)).length := by
                          rw [adjCsrOff_succ] at hp1_lt_off; omega
                        exact hne_idx ia hia_lt _ hq hi1
                    have hne_p2 : adjCsrOff X (adjOf G X) i + r ≠ p2 := by
                      by_cases hi2 : i = ib
                      · subst hi2; dsimp only [p2]; rw [h_orig_ib] at hr_old; omega
                      · dsimp only [p2]
                        have hq : (adjOfTake G X j e.2).length + (if ia = ib then 1 else 0) <
                            (adjOf G X (origOf X ib)).length := by
                          rw [adjCsrOff_succ] at hp2_lt_off; omega
                        rw [Nat.add_assoc]
                        exact hne_idx ib hib_lt _ hq hi2
                    rw [hget_old]
                    constructor
                    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                      exact (hadj i hi r hr_old).1
                    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                      exact (hadj i hi r hr_old).2
                  · have hr_ge : (adjOfTake G X j (origOf X i)).length ≤ r := Nat.le_of_not_lt hr_old
                    have htail_lt : r - (adjOfTake G X j (origOf X i)).length <
                        ((if e.1 = origOf X i then [(e.2, j)] else []) ++
                         (if e.2 = origOf X i then [(e.1, j)] else [])).length := by
                      rw [htake_i, List.length_append] at hr_r; omega
                    have hget_tail :
                        (adjOfTake G X (j + 1) (origOf X i))[r]'hr_r =
                          (((if e.1 = origOf X i then [(e.2, j)] else []) ++
                            (if e.2 = origOf X i then [(e.1, j)] else []))[r - (adjOfTake G X j (origOf X i)).length]'htail_lt) := by
                      have hopt : (adjOfTake G X (j + 1) (origOf X i))[r]? =
                          (((if e.1 = origOf X i then [(e.2, j)] else []) ++
                            (if e.2 = origOf X i then [(e.1, j)] else []))[r - (adjOfTake G X j (origOf X i)).length]?) := by
                        rw [htake_i, List.getElem?_append_right hr_ge]
                      rw [List.getElem?_eq_getElem hr_r, List.getElem?_eq_getElem htail_lt] at hopt
                      exact Option.some.inj hopt
                    rw [hget_tail]
                    by_cases hi1 : i = ia
                    · subst hi1
                      by_cases hi2 : ia = ib
                      · have h1t : e.1 = origOf X ia := hia_iff.mpr rfl
                        have h2t : e.2 = origOf X ia := hib_iff.mpr hi2
                        have hr_cases : r = (adjOfTake G X j (origOf X ia)).length ∨
                            r = (adjOfTake G X j (origOf X ia)).length + 1 := by
                          rw [htake_i] at hr_r
                          simp only [h1t, h2t, ↓reduceIte, List.length_append,
                            List.length_cons, List.length_nil] at hr_r
                          omega
                        rcases hr_cases with hr0 | hr1'
                        · have haddr_p1 : adjCsrOff X (adjOf G X) ia + r = p1 := by
                            dsimp only [p1]; rw [hr0, h_orig_ia]
                          have hne_p12 : p1 ≠ p2 := by
                            dsimp only [p1, p2]; rw [← hi2, h1t, h2t]; simp
                          constructor
                          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                              Function.update_of_ne (by omega),
                              show nbBase + adjCsrOff X (adjOf G X) ia + r = nbBase + p1 by omega,
                              Function.update_self]
                            simp [h1t, h2t, hr0, ib]
                          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                              show edgeBase + adjCsrOff X (adjOf G X) ia + r = edgeBase + p1 by omega,
                              Function.update_self]
                            simp [h1t, h2t, hr0]
                        · have haddr_p2 : adjCsrOff X (adjOf G X) ia + r = p2 := by
                            dsimp only [p2]; rw [hr1', ← hi2, h2t]; simp [h_orig_ia]; omega
                          have hsub1 : r - (adjOfTake G X j (origOf X ia)).length = 1 := by omega
                          constructor
                          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                              show nbBase + adjCsrOff X (adjOf G X) ia + r = nbBase + p2 by omega,
                              Function.update_self]
                            simp only [h1t, h2t, ↓reduceIte, hsub1, List.cons_append, List.nil_append,
                              List.getElem_cons_succ, List.getElem_cons_zero]
                            exact (locOf_origOf hi).symm
                          · rw [Function.update_of_ne (by omega),
                              show edgeBase + adjCsrOff X (adjOf G X) ia + r = edgeBase + p2 by omega,
                              Function.update_self]
                            simp only [h1t, h2t, ↓reduceIte, hsub1, List.cons_append, List.nil_append,
                              List.getElem_cons_succ, List.getElem_cons_zero]
                      · have h1t : e.1 = origOf X ia := hia_iff.mpr rfl
                        have h2f : e.2 ≠ origOf X ia := fun h => hi2 (hib_iff.mp h)
                        have hr0 : r = (adjOfTake G X j (origOf X ia)).length := by
                          rw [htake_i] at hr_r
                          simp only [h1t, h2f, ↓reduceIte, List.length_append,
                            List.length_cons, List.length_nil] at hr_r
                          omega
                        have haddr_p1 : adjCsrOff X (adjOf G X) ia + r = p1 := by
                          dsimp only [p1]; rw [hr0, h_orig_ia]
                        have hne_p12 : p1 ≠ p2 := by
                          dsimp only [p2]; rw [← haddr_p1]
                          have hq : (adjOfTake G X j e.2).length + (if ia = ib then 1 else 0) <
                              (adjOf G X (origOf X ib)).length := by
                            rw [adjCsrOff_succ] at hp2_lt_off; omega
                          rw [Nat.add_assoc]
                          exact hne_idx ib hib_lt _ hq hi2
                        constructor
                        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                            Function.update_of_ne (by omega),
                            show nbBase + adjCsrOff X (adjOf G X) ia + r = nbBase + p1 by omega,
                            Function.update_self]
                          simp [h1t, h2f, hr0, ib]
                        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                            show edgeBase + adjCsrOff X (adjOf G X) ia + r = edgeBase + p1 by omega,
                            Function.update_self]
                          simp [h1t, h2f, hr0]
                    · by_cases hi2 : i = ib
                      · subst hi2
                        have h1f : e.1 ≠ origOf X ib := fun h => hi1 (hia_iff.mp h)
                        have h2t : e.2 = origOf X ib := hib_iff.mpr rfl
                        have hr0 : r = (adjOfTake G X j (origOf X ib)).length := by
                          rw [htake_i] at hr_r
                          simp only [h1f, h2t, ↓reduceIte, List.length_append,
                            List.length_cons, List.length_nil] at hr_r
                          omega
                        have haddr_p2 : adjCsrOff X (adjOf G X) ib + r = p2 := by
                          dsimp only [p2]; rw [hr0, h_orig_ib]; simp [Ne.symm hi1]
                        constructor
                        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                            show nbBase + adjCsrOff X (adjOf G X) ib + r = nbBase + p2 by omega,
                            Function.update_self]
                          simp [h1f, h2t, hr0, ia]
                        · rw [Function.update_of_ne (by omega),
                            show edgeBase + adjCsrOff X (adjOf G X) ib + r = edgeBase + p2 by omega,
                            Function.update_self]
                          simp [h1f, h2t, hr0]
                      · exfalso
                        have h1f : e.1 ≠ origOf X i := fun h => hi1 (hia_iff.mp h)
                        have h2f : e.2 ≠ origOf X i := fun h => hi2 (hib_iff.mp h)
                        rw [htake_i] at hr_r
                        simp only [h1f, h2f, ↓reduceIte, List.length_append, List.length_nil] at hr_r
                        omega
                · intro a ha
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                  exact hframe a ha
              · wram_cost
            · refine runs_seq_cond_le (v := 0) (by simp only [he2, ↓reduceIte]; eval_expr)
                (fun h0 => absurd rfl h0) (fun _ => ?_)
              wram_run
              · dsimp only [normalPost]
                refine ⟨⟨fun r hr' => by
                    simp only [Function.update_of_ne (by omega : r ≠ 11),
                      Function.update_of_ne (by omega : r ≠ 12),
                      Function.update_of_ne (by omega : r ≠ 13),
                      Function.update_of_ne (by omega : r ≠ 14),
                      Function.update_of_ne (by omega : r ≠ 15)]
                    exact hr r hr',
                  by simp [← hj_def]; omega, ?_, ?_, hframe⟩, by simp [← hj_def]; omega⟩
                · intro i hi
                  simp only [Function.update_self, ← hj_def]
                  rw [adjOfTake_succ G X hlt (origOf X i), ← he_def]
                  simp [he2, hwc i hi]
                · intro i hi r hr_r
                  simp only [Function.update_self, ← hj_def] at hr_r ⊢
                  have hEq : adjOfTake G X (j + 1) (origOf X i) = adjOfTake G X j (origOf X i) := by
                    rw [adjOfTake_succ G X hlt (origOf X i), ← he_def]; simp [he2]
                  have hr_old : r < (adjOfTake G X j (origOf X i)).length := by rwa [← hEq]
                  have hget : (adjOfTake G X (j + 1) (origOf X i))[r]'hr_r =
                      (adjOfTake G X j (origOf X i))[r]'hr_old := by
                    revert hr_r; rw [hEq]; intro _; rfl
                  rw [hget]; exact hadj i hi r hr_old
              · wram_cost
          · refine runs_seq_cond_le (v := 0) (by simp only [he1, ↓reduceIte]; eval_expr)
              (fun h0 => absurd rfl h0) (fun _ => ?_)
            wram_run
            · dsimp only [normalPost]
              refine ⟨⟨fun r hr' => by
                  simp only [Function.update_of_ne (by omega : r ≠ 11),
                    Function.update_of_ne (by omega : r ≠ 12),
                    Function.update_of_ne (by omega : r ≠ 13),
                    Function.update_of_ne (by omega : r ≠ 14),
                    Function.update_of_ne (by omega : r ≠ 15)]
                  exact hr r hr',
                by simp [← hj_def]; omega, ?_, ?_, hframe⟩, by simp [← hj_def]; omega⟩
              · intro i hi
                simp only [Function.update_self, ← hj_def]
                rw [adjOfTake_succ G X hlt (origOf X i), ← he_def]
                simp [he1, hwc i hi]
              · intro i hi r hr_r
                simp only [Function.update_self, ← hj_def] at hr_r ⊢
                have hEq : adjOfTake G X (j + 1) (origOf X i) = adjOfTake G X j (origOf X i) := by
                  rw [adjOfTake_succ G X hlt (origOf X i), ← he_def]; simp [he1]
                have hr_old : r < (adjOfTake G X j (origOf X i)).length := by rwa [← hEq]
                have hget : (adjOfTake G X (j + 1) (origOf X i))[r]'hr_r =
                    (adjOfTake G X j (origOf X i))[r]'hr_old := by
                  revert hr_r; rw [hEq]; intro _; rfl
                rw [hget]; exact hadj i hi r hr_old
            · wram_cost
    have hinit :
        (∀ r ≤ 10, ({ st4 with regs := Function.update st4.regs 11 0 }).regs r = st4.regs r) ∧
        ({ st4 with regs := Function.update st4.regs 11 0 }).regs 11 ≤ G.m ∧
        (∀ i < X.card, ({ st4 with regs := Function.update st4.regs 11 0 }).mem (wcurBase + i) =
          adjCsrOff X (adjOf G X) i +
            (adjOfTake G X (({ st4 with regs := Function.update st4.regs 11 0 }).regs 11)
              (origOf X i)).length) ∧
        (∀ i < X.card,
          ∀ r (hr : r < (adjOfTake G X (({ st4 with regs := Function.update st4.regs 11 0 }).regs 11)
              (origOf X i)).length),
            ({ st4 with regs := Function.update st4.regs 11 0 }).mem
              (nbBase + adjCsrOff X (adjOf G X) i + r) =
              locOf X ((adjOfTake G X (({ st4 with regs := Function.update st4.regs 11 0 }).regs 11)
                (origOf X i))[r]'hr).1 ∧
            ({ st4 with regs := Function.update st4.regs 11 0 }).mem
              (edgeBase + adjCsrOff X (adjOf G X) i + r) =
              ((adjOfTake G X (({ st4 with regs := Function.update st4.regs 11 0 }).regs 11)
                (origOf X i))[r]'hr).2) ∧
        (∀ a, (a < wcurBase ∨ locBase ≤ a) →
          ({ st4 with regs := Function.update st4.regs 11 0 }).mem a = mem4 a) := by
      refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp,
        fun i hi => by
          dsimp only
          simp only [Function.update_self, hmem4, adjOfTake_zero, List.length_nil, Nat.add_zero]
          exact hwcur i hi,
        fun i _ _ hr => by
          dsimp only at hr
          simp only [Function.update_self, adjOfTake_zero, List.length_nil] at hr
          exact absurd hr (Nat.not_lt_zero _),
        fun _ _ => hmem4 ▸ rfl⟩
    obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop _ ω hinit
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      rcases hpost with ⟨hr', _, hadj', hframe'⟩
      refine ⟨.normal, st', c, hrun, ⟨hr', ⟨⟨?_, fun i hi r hr => (hadj' i hi r hr).1⟩,
        fun i hi r hr => (hadj' i hi r hr).2⟩, hframe'⟩, by
        simp only [Function.update_self, Nat.sub_zero, Expr.size_bin, Expr.size_reg,
          Expr.size_const] at hcost ⊢
        omega⟩
      intro i hi
      rw [hframe' _ (Or.inl (by omega))]
      exact hoff i hi

/-! ## Full `buildLocalCsrProc` Contract -/

theorem buildLocalCsr_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ}
    (hp : p.HasAt b [buildLocalCsrProc bSort])
    (hsort : MeetsContract w p bSort (heapSortContract w)) :
    MeetsContract w p b (buildLocalCsrContract w) := by
  intro args mem pos ω hwords hpre
  dsimp only [buildLocalCsrContract] at hpre ⊢
  rcases hpre with ⟨gAddr, xAddr, workAddr, G, X, rfl, hG, hG_val, hX, hX_sub,
    hg_disj, hx_disj, hzero, hw, hw4⟩
  have hproc : p.procs[b]? = some (buildLocalCsrProc bSort) := hp 0 (by simp)
  rcases hX with ⟨xs, hxs_nd, hxs_fin, hxs_seq⟩
  have hxs_len : xs.length = X.card := by rw [← hxs_fin, List.toFinset_card_of_nodup hxs_nd]
  have hn_mem : mem gAddr = G.n := graphAt_n hG
  have hm_mem : mem (gAddr + 1) = G.m := graphAt_m hG
  have hx_mem : mem xAddr = X.card := by rw [hxs_seq.1, hxs_len]
  have hxs_lt : ∀ i < X.card, mem (xAddr + 1 + i) < 2 ^ w := by
    intro i hi
    have hi' : i < xs.length := by omega
    rw [show xAddr + 1 + i = (xAddr + 1) + i by omega, hxs_seq.2 i hi']
    have hmemX : xs[i]'hi' ∈ X := by rw [← hxs_fin, List.mem_toFinset]; exact List.getElem_mem hi'
    have hlt_n : xs[i]'hi' < G.n := Finset.mem_range.mp (hX_sub hmemX)
    dsimp only [localCsrSpace] at hw
    omega
  have hsp_eq :
      workAddr + localCsrSpace G.n G.m X.card =
        csrLocIdAddr workAddr X.card G.m + G.n := by
    dsimp only [localCsrSpace, csrLocIdAddr]; omega
  have htriple :
      Triple w p
        (fun st => st = startState [gAddr, xAddr, workAddr] mem pos)
        (buildLocalCsrProc bSort)
        (fun o st' =>
          o.value = 2 * (G.inside X).length ∧
          ListAt st'.mem (csrOrigAddr workAddr) (sortedX X) ∧
          (∀ u < G.n, st'.mem (csrLocIdAddr workAddr X.card G.m + u) =
            if u ∈ X then locOf X u + 1 else 0) ∧
          AdjCsrAt st'.mem (csrOffAddr workAddr X.card) (csrNbAddr workAddr X.card)
            (csrEdgeAddr workAddr X.card G.m) X (adjOf G X) ∧
          (∀ a < workAddr, st'.mem a = mem a) ∧
          ZeroFrom st'.mem (workAddr + localCsrSpace G.n G.m X.card))
        (fun _ => buildLocalCsrCost G.m X.card) := by
    wram_enter
    · subst st
      dsimp only [buildLocalCsrProc, seqStmts]
      have hg_lt : gAddr < 2 ^ w := hwords gAddr (by simp)
      have hx_lt : xAddr < 2 ^ w := hwords xAddr (by simp)
      have hw_lt : workAddr < 2 ^ w := hwords workAddr (by simp)
      have hsp_lt : workAddr + 3 * X.card + 1 + 4 * G.m + G.n + 4 < 2 ^ w := by
        dsimp only [localCsrSpace] at hw; omega
      refine runs_seq_assign_le (v := G.n) (by rw [← hn_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := G.m) (by rw [← hm_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := X.card) (by rw [← hx_mem]; eval_expr) ?_
      have h_off_def : csrOffAddr workAddr X.card = workAddr + X.card := rfl
      have h_wcur_def : csrWCurAddr workAddr X.card = csrOffAddr workAddr X.card + X.card + 1 := by
        dsimp only [csrOffAddr, csrWCurAddr]; omega
      have h_nb_def : csrNbAddr workAddr X.card = csrWCurAddr workAddr X.card + X.card := by
        dsimp only [csrWCurAddr, csrNbAddr]; omega
      have h_edge_def : csrEdgeAddr workAddr X.card G.m = csrNbAddr workAddr X.card + 2 * G.m := rfl
      have h_loc_def : csrLocIdAddr workAddr X.card G.m =
          csrEdgeAddr workAddr X.card G.m + 2 * G.m := by
        dsimp only [csrEdgeAddr, csrLocIdAddr]; omega
      refine runs_seq_assign_le (v := csrOffAddr workAddr X.card)
        (by (conv_rhs => rw [h_off_def]); eval_expr) ?_
      refine runs_seq_assign_le (v := csrWCurAddr workAddr X.card)
        (by (conv_rhs => rw [h_wcur_def]); eval_expr) ?_
      refine runs_seq_assign_le (v := csrNbAddr workAddr X.card)
        (by (conv_rhs => rw [h_nb_def]); eval_expr) ?_
      refine runs_seq_assign_le (v := csrEdgeAddr workAddr X.card G.m)
        (by (conv_rhs => rw [h_edge_def]); eval_expr) ?_
      refine runs_seq_assign_le (v := csrLocIdAddr workAddr X.card G.m)
        (by (conv_rhs => rw [h_loc_def]); eval_expr) ?_
      -- Stage 1: copy X to origVertAddr
      refine runs_seq_triple_le
        (csrCopyX_triple (gAddr := gAddr) (xAddr := xAddr) (workAddr := workAddr)
          (G := G) (X := X) (xs := xs) hxs_len hxs_seq hx_disj hw hw4 hxs_lt
          (fun r hr => by
            interval_cases r <;> simp [startState])
          rfl)
        rfl (fun st1 hst1 => ?_)
      rcases hst1 with ⟨hr1, horig1, hframe1⟩
      -- Stage 2: heapSort origVert[0 .. X.card - 1]
      have hsort_args : evalArgs w st1 [.reg 2, .reg 5] = some [workAddr, X.card] := by
        have hr2 : st1.regs 2 = workAddr := by rw [hr1 2 (by decide)]; simp [startState]
        have hr5 : st1.regs 5 = X.card := by rw [hr1 5 (by decide)]; simp [startState]
        eval_expr
      refine runs_seq_call_le hsort hsort_args (by wram_words) ?_ (fun v2 mem2 pos2 hpost2 => ?_)
      · refine ⟨workAddr, X.card, rfl, by omega, by omega, hw4, fun i hi => ?_⟩
        rw [horig1 i (by omega)]
        have hi' : i < xs.length := by omega
        have hmemX : xs[i]'hi' ∈ X := by rw [← hxs_fin, List.mem_toFinset]; exact List.getElem_mem hi'
        have := Finset.mem_range.mp (hX_sub hmemX)
        omega
      · dsimp only [heapSortContract] at hpost2
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hpost2
        rcases hpost2 with ⟨_, hperm2, hle2, _, hmf2⟩
        have htab1 : (tab X.card fun i => st1.mem (workAddr + i)) = xs := by
          apply List.ext_getElem (by simp [tab, hxs_len])
          intro i hi _
          simp only [tab, List.getElem_map, List.getElem_range]
          exact horig1 i (by simp [tab] at hi; omega)
        rw [htab1] at hperm2
        have hnd2 : (tab X.card fun i => mem2 (workAddr + i)).Nodup := hperm2.nodup_iff.mpr hxs_nd
        have hfin2 : (tab X.card fun i => mem2 (workAddr + i)).toFinset = X := by
          have h : (tab X.card fun i => mem2 (workAddr + i)).toFinset = xs.toFinset := by
            ext u; simp only [List.mem_toFinset]; exact hperm2.mem_iff
          rw [h, hxs_fin]
        have hlt2 : (tab X.card fun i => mem2 (workAddr + i)).Pairwise (· < ·) :=
          (hle2.and (List.nodup_iff_pairwise_ne.mp hnd2)).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
        have hsorted2 : (tab X.card fun i => mem2 (workAddr + i)) = sortedX X :=
          sortedX_eq_of_pairwise_lt hlt2 hfin2
        have horig2 : ListAt mem2 workAddr (sortedX X) := by
          intro i hi
          rw [sortedX_length] at hi
          have h := congr_arg (fun l => l[i]?) hsorted2
          simp only [tab, List.getElem?_map, List.getElem?_range hi, Option.map_some,
            List.getElem?_eq_getElem (by rw [sortedX_length]; exact hi), Option.some.injEq] at h
          exact h
        have hframe2 : ∀ a, (a < workAddr ∨ workAddr + X.card ≤ a) → mem2 a = mem a := by
          intro a ha
          rw [hmf2 a ha, hframe1 a ha]
        have hregs2 : ∀ r ≤ 10, (Function.update st1.regs 12 v2) r =
            match r with
            | 0 => gAddr | 1 => xAddr | 2 => workAddr | 3 => G.n | 4 => G.m | 5 => X.card
            | 6 => csrOffAddr workAddr X.card
            | 7 => csrWCurAddr workAddr X.card
            | 8 => csrNbAddr workAddr X.card
            | 9 => csrEdgeAddr workAddr X.card G.m
            | _ => csrLocIdAddr workAddr X.card G.m := by
          intro r hr
          rw [Function.update_of_ne (by omega), hr1 r hr]
          interval_cases r <;> simp [startState]
        -- Stage 3: fill locId
        refine runs_seq_triple_le
          (csrFillLoc_triple hX_sub horig2
            (fun u _ => by
              rw [hframe2 _ (Or.inr (by dsimp only [csrLocIdAddr]; omega))]
              exact hzero _ (by dsimp only [csrLocIdAddr]; omega))
            hw hw4 hregs2 rfl)
          rfl (fun st3 hst3 => ?_)
        rcases hst3 with ⟨hr3, hloc3, hframe3⟩
        have hregs3 : ∀ r ≤ 10, st3.regs r = _ := fun r hr => (hr3 r hr).trans (hregs2 r hr)
        have hG3 : GraphAt st3.mem gAddr G :=
          GraphAt.of_agree_below hG hg_disj (fun k hk => by
            rw [hframe3 k (Or.inl (by dsimp only [csrLocIdAddr]; omega)),
                hframe2 k (Or.inl (by omega))])
        -- Stage 4: count degrees
        refine runs_seq_triple_le
          (csrCountDeg_triple hG3 hG_val hg_disj hloc3
            (fun i hi => by
              rw [hframe3 _ (Or.inl (by dsimp only [csrOffAddr, csrLocIdAddr]; omega)),
                  hframe2 _ (Or.inr (by dsimp only [csrOffAddr]; omega))]
              exact hzero _ (by dsimp only [csrOffAddr]; omega))
            hw hw4 hregs3 rfl)
          rfl (fun st4 hst4 => ?_)
        rcases hst4 with ⟨hr4, hdeg4, hframe4⟩
        have hregs4 : ∀ r ≤ 10, st4.regs r = _ := fun r hr => (hr4 r hr).trans (hregs3 r hr)
        -- Stage 5: prefix sums
        refine runs_seq_triple_le
          (csrPrefixSum_triple
            (by
              rw [hframe4 _ (Or.inl (by omega)),
                  hframe3 _ (Or.inl (by dsimp only [csrOffAddr, csrLocIdAddr]; omega)),
                  hframe2 _ (Or.inr (by dsimp only [csrOffAddr]; omega))]
              exact hzero _ (by dsimp only [csrOffAddr]; omega))
            hdeg4 hw hw4 hregs4 rfl)
          rfl (fun st5 hst5 => ?_)
        rcases hst5 with ⟨hr5, hoff5, hwcur5, hframe5⟩
        have hregs5 : ∀ r ≤ 10, st5.regs r = _ := fun r hr => (hr5 r hr).trans (hregs4 r hr)
        have hG5 : GraphAt st5.mem gAddr G :=
          GraphAt.of_agree_below hG3 hg_disj (fun k hk => by
            rw [hframe5 k (Or.inl (by dsimp only [csrOffAddr]; omega)),
                hframe4 k (Or.inl (by dsimp only [csrOffAddr]; omega))])
        have hloc5 : ∀ u < G.n, st5.mem (csrLocIdAddr workAddr X.card G.m + u) =
            if u ∈ X then locOf X u + 1 else 0 := by
          intro u hu
          rw [hframe5 _ (Or.inr (by dsimp only [csrWCurAddr, csrLocIdAddr]; omega)),
              hframe4 _ (Or.inr (by dsimp only [csrOffAddr, csrLocIdAddr]; omega))]
          exact hloc3 u hu
        -- Stage 6: fill adjacency arrays
        refine runs_seq_triple_le
          (csrFillAdj_triple hG5 hG_val hg_disj hloc5 hoff5 hwcur5 hw hw4 hregs5 rfl)
          rfl (fun st6 hst6 => ?_)
        rcases hst6 with ⟨hr6, hcsr6, hframe6⟩
        have hr6_6 : st6.regs 6 = csrOffAddr workAddr X.card := by
          rw [hr6 6 (by decide)]; exact hregs5 6 (by decide)
        have hr6_5 : st6.regs 5 = X.card := by
          rw [hr6 5 (by decide)]; exact hregs5 5 (by decide)
        have hoff_end : st6.mem (csrOffAddr workAddr X.card + X.card) = 2 * (G.inside X).length := by
          rw [hcsr6.1.1 X.card le_rfl, adjCsrOff_adjOf_card]
        have h_ret_addr : csrOffAddr workAddr X.card + X.card < 2 ^ w := by omega
        refine runs_ret_le (v := 2 * (G.inside X).length) (by rw [← hoff_end]; eval_expr) ?_ ?_
        · refine ⟨rfl, ?_, ?_, hcsr6, ?_, ?_⟩
          · intro i hi
            rw [sortedX_length] at hi
            rw [csrOrigAddr,
                hframe6 _ (Or.inl (by dsimp only [csrWCurAddr]; omega)),
                hframe5 _ (Or.inl (by dsimp only [csrOffAddr]; omega)),
                hframe4 _ (Or.inl (by dsimp only [csrOffAddr]; omega)),
                hframe3 _ (Or.inl (by dsimp only [csrLocIdAddr]; omega))]
            exact horig2 i (by rw [sortedX_length]; exact hi)
          · intro u hu
            rw [hframe6 _ (Or.inr (by omega))]
            exact hloc5 u hu
          · intro a ha
            rw [hframe6 a (Or.inl (by dsimp only [csrWCurAddr]; omega)),
                hframe5 a (Or.inl (by dsimp only [csrOffAddr]; omega)),
                hframe4 a (Or.inl (by dsimp only [csrOffAddr]; omega)),
                hframe3 a (Or.inl (by dsimp only [csrLocIdAddr]; omega)),
                hframe2 a (Or.inl ha)]
          · intro a ha
            have ha' : workAddr + 3 * X.card + 1 + 4 * G.m + G.n ≤ a := by
              dsimp only [localCsrSpace] at ha; omega
            rw [hframe6 a (Or.inr (by omega)),
                hframe5 a (Or.inr (by dsimp only [csrWCurAddr]; omega)),
                hframe4 a (Or.inr (by dsimp only [csrOffAddr]; omega)),
                hframe3 a (Or.inr (by omega)),
                hframe2 a (Or.inr (by omega))]
            exact hzero a (by omega)
        · dsimp only [heapSortContract, buildLocalCsrCost, argsSize, Expr.size]
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          omega
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ :=
    htriple (startState [gAddr, xAddr, workAddr] mem pos) ω rfl
  refine ⟨buildLocalCsrProc bSort, hproc, o, st', c, hrun, ?_, ?_⟩
  · intro G' X' hG' _ hX' _
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hG' hX' ⊢
    have hGe : G' = G := by
      have h1 : G'.n = G.n := by rw [← graphAt_n hG', graphAt_n hG]
      have h2 : G'.m = G.m := by rw [← graphAt_m hG', graphAt_m hG]
      cases G' with | mk n' es' =>
      cases G with | mk n es =>
      dsimp only [Graph.m] at h1 h2; subst h1
      congr 1
      apply List.ext_getElem h2
      intro j hj _
      have hj' : j < ({ n := n', edges := es' } : Graph).m := hj
      have hj0 : j < ({ n := n', edges := es } : Graph).m := by
        dsimp only [Graph.m]; omega
      exact Prod.ext
        ((graphAt_edge_fst hG' hj').symm.trans (graphAt_edge_fst hG hj0))
        ((graphAt_edge_snd hG' hj').symm.trans (graphAt_edge_snd hG hj0))
    have hXe : X' = X := by
      rcases hX' with ⟨xs', _, hfin', hseq'⟩
      have hlen' : xs'.length = xs.length := by rw [← hseq'.1, hxs_seq.1]
      have hlist : xs' = xs := by
        apply List.ext_getElem hlen'
        intro i hi _
        rw [← hseq'.2 i hi, hxs_seq.2 i (hlen' ▸ hi)]
      rw [← hfin', hlist, hxs_fin]
    subst hGe; subst hXe
    exact hpost
  · simpa [hm_mem, hx_mem] using hcost

end MinCostFlow.ExpanderDecomp
