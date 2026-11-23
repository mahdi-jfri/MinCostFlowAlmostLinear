module

public import MinCostFlow.SparseCore.Program.TourOpsMoveSplay
import Mathlib.Tactic

/-!
# Amortized run theorem for `tourMoveSplitLoopBody`

Verifies `tourMoveSplitLoopBody_runs`, iteratively partitioning a block-decomposed splay tree
`t` (`t.toList = xs.flatMap f`) along a sorted sublist `A` of `xs` into `(tA?, tB?)` stored at
`outHeap` and `outHeap + 1` in `O((m + 1) * log (cap + 2))` amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Full amortized run theorem for `tourMoveSplitLoopBody [nb, tRem, pairsPtr, nxtPtr, m, fuel, outHeap]`:
partitions a block-decomposed tree `t` (`t.toList = xs.flatMap f`) along sorted sublist `A` of `xs`
into `(tA?, tB?)` stored at `outHeap` and `outHeap + 1`. -/
theorem tourMoveSplitLoopBody_runs {w nb cap pairsPtr nxtPtr m fuel outHeap pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    {xs A : List ℕ} {f : ℕ → List ℕ}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hxs_nd : xs.Nodup) (ht_flat : t.toList = xs.flatMap f)
    (hhd : ∀ a ∈ xs, (f a).head? = some a)
    (hA_eq : A = xs.filter fun z => decide (z ∈ A)) (hA_len : A.length = m)
    (hmem_A : ∀ i (hi : i < m), mem (pairsPtr + (2 * i + 1)) = A[i]'(by omega))
    (hmem_W : ∀ i (hi : i < m),
      let idx := xs.idxOf (A[i]'(by omega))
      mem (nxtPtr + i) = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0)
    (hpairs_lt : pairsPtr + 2 * m ≤ outHeap) (hnxt_lt : nxtPtr + m ≤ outHeap)
    (hpairs_out : ∀ a, pairsPtr ≤ a → a < pairsPtr + 2 * m → ¬tourLayout.InRecords nb cap a)
    (hnxt_out : ∀ a, nxtPtr ≤ a → a < nxtPtr + m → ¬tourLayout.InRecords nb cap a)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap outHeap 4 mem) :
    ∃ tA? tB? s' o st' c,
      Runs w p ω (tourMoveSplitLoopBody C.splay.splay C.detachLeft C.join)
        (startState [nb, t.rootId, pairsPtr, nxtPtr, m, fuel, outHeap] mem pos) o st' c ∧
      st'.mem outHeap = optRoot tA? ∧ st'.mem (outHeap + 1) = optRoot tB? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      ZeroFrom st'.mem (outHeap + 2) ∧
      (∀ a < outHeap, ¬tourLayout.InRecords nb cap a → st'.mem a = mem a) ∧
      TourForestInv cap s' (optTrees tA? ++ optTrees tB? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList tA? = (xs.filter fun z => decide (z ∈ A)).flatMap f ∧
      optList tB? = (xs.filter fun z => decide (z ∉ A)).flatMap f ∧
      (∀ z ≤ cap, (s'.nodes z).val = (st.nodes z).val) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees tA? ++ optTrees tB? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) +
          (m + 1) * TOUR_MOVE_STEP_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  have hout2_lt : outHeap + 2 < 2 ^ w := by have := hheap.room; omega
  have hpairs_w : pairsPtr + 2 * m < 2 ^ w := by omega
  have hnxt_w : nxtPtr + m < 2 ^ w := by omega
  have hrec2 : tourLayout.nodeAddr nb (cap + 1) ≤ outHeap + 2 := le_trans hheap.rec_le (by omega)
  have hloop : ∀ (k : ℕ) (i : ℕ) (tA? tB? tRem? : Option AuxTree)
      (sC : SplayState TourVal TourSum Unit) (stC : State) (rem_xs : List ℕ) (pref_xs : List ℕ),
      i + k = m → xs = pref_xs ++ rem_xs →
      A.drop i = rem_xs.filter (fun z => decide (z ∈ A)) →
      optList tA? = (pref_xs.filter (fun z => decide (z ∈ A))).flatMap f →
      optList tB? = (pref_xs.filter (fun z => decide (z ∉ A))).flatMap f →
      optList tRem? = rem_xs.flatMap f →
      stC.regs 0 = nb → stC.regs 1 = optRoot tRem? → stC.regs 2 = pairsPtr →
      stC.regs 3 = nxtPtr → stC.regs 4 = m → stC.regs 5 = fuel →
      stC.regs 6 = outHeap → stC.regs 7 = optRoot tA? → stC.regs 8 = optRoot tB? →
      stC.regs 9 = i → stC.regs 10 = outHeap + 2 →
      tourLayout.NodesAt stC.mem nb cap sC →
      TreeFrame tourLayout nb cap (outHeap + 2) mem stC.mem →
      TourForestInv cap sC (optTrees tA? ++ optTrees tB? ++ optTrees tRem? ++ rest) →
      TourValsOk w cap sC →
      (∀ z ≤ cap, (sC.nodes z).val = (st.nodes z).val) →
      ∃ tA'? tB'? tRem'? sF stF cL,
        Runs w p ω (.loop (.bin .lt (.reg 9) (.reg 4))
          (.assign 11 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 9) (.reg 9)) (.const 1)))) ;;
           .assign 12 (.load (.bin .add (.reg 3) (.reg 9))) ;;
           .call 13 C.splay.splay [.reg 0, .reg 11, .reg 5, .reg 10] ;;
           .call 13 C.detachLeft [.reg 0, .reg 11, .reg 10] ;;
           .call 8 C.join [.reg 0, .reg 8, .reg 13, .reg 5, .reg 10] ;;
           .assign 1 (.reg 11) ;;
           .cond (.bin .eq (.reg 12) (.const 0))
             (.call 7 C.join [.reg 0, .reg 7, .reg 1, .reg 5, .reg 10] ;;
              .assign 1 (.const 0))
             (.call 13 C.splay.splay [.reg 0, .reg 12, .reg 5, .reg 10] ;;
              .call 13 C.detachLeft [.reg 0, .reg 12, .reg 10] ;;
              .call 7 C.join [.reg 0, .reg 7, .reg 13, .reg 5, .reg 10] ;;
              .assign 1 (.reg 12)) ;;
           .assign 9 (.bin .add (.reg 9) (.const 1)))) stC .normal stF cL ∧
        stF.regs 0 = nb ∧ stF.regs 1 = optRoot tRem'? ∧ stF.regs 5 = fuel ∧
        stF.regs 6 = outHeap ∧ stF.regs 7 = optRoot tA'? ∧ stF.regs 8 = optRoot tB'? ∧
        stF.regs 10 = outHeap + 2 ∧
        tourLayout.NodesAt stF.mem nb cap sF ∧
        TreeFrame tourLayout nb cap (outHeap + 2) mem stF.mem ∧
        TourForestInv cap sF (optTrees tA'? ++ optTrees tB'? ++ optTrees tRem'? ++ rest) ∧
        TourValsOk w cap sF ∧
        optList tA'? = (xs.filter fun z => decide (z ∈ A)).flatMap f ∧
        optList tB'? ++ optList tRem'? = (xs.filter fun z => decide (z ∉ A)).flatMap f ∧
        (∀ z ≤ cap, (sF.nodes z).val = (st.nodes z).val) ∧
        cL + TOUR_PHI_MULT * forestPhi (optTrees tA'? ++ optTrees tB'? ++ optTrees tRem'? ++ rest) ≤
          TOUR_PHI_MULT * forestPhi (optTrees tA? ++ optTrees tB? ++ optTrees tRem? ++ rest) +
            k * (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) * (Nat.log 2 (cap + 2) + 1) + 20 := by
    intro k
    induction k with
    | zero =>
      intro i tA? tB? tRem? sC stC rem_xs pref_xs hik hxs_eq hdrop hA_l hB_l hR_l
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hnC hfrC hinvC hvalsC hvalC
      have him : i = m := by omega
      have hrem_noA : ∀ z ∈ rem_xs, z ∉ A := fun z hz hzm => by
        have : z ∈ rem_xs.filter (fun z => decide (z ∈ A)) := List.mem_filter.mpr ⟨hz, decide_eq_true hzm⟩
        rw [← hdrop, him, ← hA_len, List.drop_length] at this; simp at this
      have hfiltA_rem : rem_xs.filter (fun z => decide (z ∈ A)) = [] :=
        List.filter_eq_nil_iff.mpr fun z hz => by simp [hrem_noA z hz]
      have hfiltB_rem : rem_xs.filter (fun z => decide (z ∉ A)) = rem_xs :=
        List.filter_eq_self.mpr fun z hz => by simp [hrem_noA z hz]
      have hcond : (Expr.bin .lt (.reg 9) (.reg 4)).eval w stC = some 0 := by
        simp [Expr.eval, hr9, hr4, him, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨tA?, tB?, tRem?, sC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr0, hr1, hr5, hr6, hr7, hr8, hr10, hnC, hfrC, hinvC, hvalsC,
        by rw [hA_l, hxs_eq, List.filter_append, hfiltA_rem, List.append_nil],
        by rw [hB_l, hR_l, hxs_eq, List.filter_append, hfiltB_rem, List.flatMap_append], hvalC, ?_⟩
      simp only [Expr.size]; omega
    | succ k ih =>
      intro i tA? tB? tRem? sC stC rem_xs pref_xs hik hxs_eq hdrop hA_l hB_l hR_l
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hnC hfrC hinvC hvalsC hvalC
      have hi_lt : i < m := by omega
      set u := A[i]'(by omega)
      have hdrop_c : A.drop i = u :: A.drop (i + 1) := by rw [List.drop_eq_getElem_cons (by omega)]
      have hu_rem : u ∈ rem_xs := by
        have : u ∈ rem_xs.filter (fun z => decide (z ∈ A)) := by rw [← hdrop, hdrop_c]; simp
        exact (List.mem_filter.mp this).1
      obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hu_rem
      have hP_noA : ∀ z ∈ P, z ∉ A := by
        intro z hz hzm
        have hz_f : z ∈ P.filter (fun w => decide (w ∈ A)) := List.mem_filter.mpr ⟨hz, decide_eq_true hzm⟩
        obtain ⟨p0, ps, hp⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hz_f)
        have h1 : A.drop i = p0 :: (ps ++ (u :: Q).filter (fun w => decide (w ∈ A))) := by
          rw [hdrop, hPQ, List.filter_append, hp]; rfl
        rw [hdrop_c] at h1
        have hp0 : p0 = u := (List.cons.inj h1).1.symm
        have hp0_mem : p0 ∈ P.filter (fun w => decide (w ∈ A)) := by rw [hp]; simp
        have hu_P : u ∈ P := (List.mem_filter.mp (hp0 ▸ hp0_mem)).1
        have hnd_rem : rem_xs.Nodup := (List.nodup_append.mp (hxs_eq ▸ hxs_nd)).2.1
        exact (List.nodup_append.mp (hPQ ▸ hnd_rem)).2.2 u hu_P u (by simp) rfl
      have hfiltA_P : P.filter (fun z => decide (z ∈ A)) = [] :=
        List.filter_eq_nil_iff.mpr fun z hz => by simp [hP_noA z hz]
      have hfiltB_P : P.filter (fun z => decide (z ∉ A)) = P :=
        List.filter_eq_self.mpr fun z hz => by simp [hP_noA z hz]
      have hdrop_next : A.drop (i + 1) = Q.filter (fun z => decide (z ∈ A)) := by
        have h1 : u :: A.drop (i + 1) = u :: Q.filter (fun z => decide (z ∈ A)) := by
          rw [← hdrop_c, hdrop, hPQ, List.filter_append, hfiltA_P, List.nil_append, List.filter_cons]
          have huA : u ∈ A := List.getElem_mem _
          simp [huA]
        exact (List.cons.inj h1).2
      have hu_xs : u ∈ xs := by rw [hxs_eq, hPQ]; simp
      have hhd_u : (f u).head? = some u := hhd u hu_xs
      set wNxt := mem (nxtPtr + i)
      have hw_spec : NextBlockSpec f wNxt Q := by
        have h1 := hmem_W i hi_lt
        dsimp only at h1
        have hxs2 : xs = (pref_xs ++ P) ++ u :: Q := by simpa [List.append_assoc, hPQ] using hxs_eq
        have hidx : xs.idxOf u = (pref_xs ++ P).length := by
          rw [hxs2]; exact idxOf_left_append_cons (hxs2 ▸ hxs_nd)
        have hlen_xs : xs.length = (pref_xs ++ P).length + 1 + Q.length := by
          rw [hxs2]; simp; omega
        have hQ_helper : ∀ Q0 : List ℕ, xs = (pref_xs ++ P) ++ u :: Q0 →
            xs.length = (pref_xs ++ P).length + 1 + Q0.length → NextBlockSpec f wNxt Q0 := by
          intro Q0 hxsQ hlenQ
          cases Q0 with
          | nil =>
            simp only [List.length_nil] at hlenQ
            have hnot : ¬(xs.idxOf u + 1 < xs.length) := by omega
            simpa [NextBlockSpec, wNxt, u, hnot] using h1
          | cons q0 Q' =>
            simp only [List.length_cons] at hlenQ
            have hlt : xs.idxOf u + 1 < xs.length := by omega
            have hget : xs[xs.idxOf u + 1]'hlt = q0 := by
              have hget2 : ((pref_xs ++ P) ++ u :: q0 :: Q')[(pref_xs ++ P).length + 1]'(by simp; omega) = q0 := by
                rw [List.getElem_append_right (by omega)]; simp
              have haux : ∀ ys (hy : ys = (pref_xs ++ P) ++ u :: q0 :: Q') (hl : ys.idxOf u + 1 < ys.length),
                  ys.idxOf u = (pref_xs ++ P).length → ys[ys.idxOf u + 1]'hl = q0 := by
                rintro _ rfl hl hi; simp only [hi]; exact hget2
              exact haux xs hxsQ hlt hidx
            have hq0_xs : q0 ∈ xs := by rw [hxsQ]; simp
            exact ⟨by simpa [wNxt, u, hlt, hget] using h1, hhd q0 hq0_xs⟩
        exact hQ_helper Q hxs2 hlen_xs
      have hmC_u : stC.mem (pairsPtr + (i + i + 1)) = u := by
        have hi2 : i + i = 2 * i := by omega
        rw [hi2, hfrC.2 _ (by omega) (hpairs_out _ (by omega) (by omega))]; exact hmem_A i hi_lt
      have hmC_w : stC.mem (nxtPtr + i) = wNxt :=
        hfrC.2 _ (by omega) (hnxt_out _ (by omega) (by omega))
      have hcond : (Expr.bin .lt (.reg 9) (.reg 4)).eval w stC = some 1 := by
        simp [Expr.eval, hr9, hr4, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set r1 := Function.update stC.regs 11 u
      set r2 := Function.update r1 12 wNxt
      have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 2) (.bin .add (.bin .add (.reg 9) (.reg 9)) (.const 1)))))
          stC .normal { stC with regs := r1 } 9 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, hr2, hr9, BinOp.eval, (by omega : 1 < 2 ^ w),
            (by omega : i + i < 2 ^ w), (by omega : i + i + 1 < 2 ^ w),
            (by omega : pairsPtr + (i + i + 1) < 2 ^ w), hmC_u], rfl, rfl, rfl⟩
      have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 3) (.reg 9))))
          { stC with regs := r1 } .normal { stC with regs := r2 } 5 :=
        runs_assign_iff.mpr ⟨wNxt, by
          simp [Expr.eval, r1, hr3, hr9, BinOp.eval, (by omega : nxtPtr + i < 2 ^ w), hmC_w], rfl, rfl, rfl⟩
      obtain ⟨tA1?, tB1?, tRem1?, s1, st1, cS, hrunS, hrS_oth, hrS1, hrS7, hrS8, hn1, hfr1, hinv1, hvals1,
        hA1_l, hB1_l, hR1_l, hval1, hcS⟩ :=
        tourMoveSplit_step (r := r2) (pos := stC.pos) C ω hnC hinvC hvalsC (hR_l.trans (by rw [hPQ])) hhd_u hw_spec
          hfuel hfuelW ⟨hrec2, by have := hheap.room; omega, hfrC.1, hheap.wide⟩
          (by simp [r2, r1, hr0]) (by simp [r2, r1, hr1]) (by simp [r2, r1, hr5])
          (by simp [r2, r1, hr7]) (by simp [r2, r1, hr8]) (by simp [r2, r1, hr10])
          (by simp [r2, r1]) (by simp [r2])
      set r3 := Function.update st1.regs 9 (i + 1)
      have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) st1 .normal { st1 with regs := r3 } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp only [Expr.eval, hrS_oth 9 (by decide) (by decide) (by decide) (by decide)]
          simp [r2, r1, hr9, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha11 (tour_runs_seq_normal ha12 (runs_seqAppend hrunS ha9))
      have hA1_new : optList tA1? = ((pref_xs ++ P ++ [u]).filter (fun z => decide (z ∈ A))).flatMap f := by
        have huA : u ∈ A := List.getElem_mem _
        rw [hA1_l, hA_l]; simp [List.filter_append, hfiltA_P, huA, List.flatMap_append]
      have hB1_new : optList tB1? = ((pref_xs ++ P ++ [u]).filter (fun z => decide (z ∉ A))).flatMap f := by
        have huA : u ∈ A := List.getElem_mem _
        have hP_f : P.filter (fun z => !decide (z ∈ A)) = P :=
          List.filter_eq_self.mpr fun z hz => by simp [hP_noA z hz]
        rw [hB1_l, hB_l]; simp [List.filter_append, hP_f, huA, List.flatMap_append]
      obtain ⟨tA'?, tB'?, tRem'?, sF, stF, cL, hrunL, hF0, hF1, hF5, hF6, hF7, hF8, hF10,
        hnF, hfrF, hinvF, hvalsF, hAF, hBF, hvalF, hcL⟩ :=
        ih (i + 1) tA1? tB1? tRem1? s1 { st1 with regs := r3 } Q (pref_xs ++ P ++ [u])
          (by omega) (by simpa [List.append_assoc, hPQ] using hxs_eq) hdrop_next hA1_new hB1_new hR1_l
          (by dsimp only; rw [show r3 0 = st1.regs 0 by simp [r3], hrS_oth 0 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr0])
          (by simp [r3, hrS1])
          (by dsimp only; rw [show r3 2 = st1.regs 2 by simp [r3], hrS_oth 2 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr2])
          (by dsimp only; rw [show r3 3 = st1.regs 3 by simp [r3], hrS_oth 3 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr3])
          (by dsimp only; rw [show r3 4 = st1.regs 4 by simp [r3], hrS_oth 4 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr4])
          (by dsimp only; rw [show r3 5 = st1.regs 5 by simp [r3], hrS_oth 5 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr5])
          (by dsimp only; rw [show r3 6 = st1.regs 6 by simp [r3], hrS_oth 6 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr6])
          (by simp [r3, hrS7]) (by simp [r3, hrS8]) (by simp [r3])
          (by dsimp only; rw [show r3 10 = st1.regs 10 by simp [r3], hrS_oth 10 (by decide) (by decide) (by decide) (by decide)]; simp [r2, r1, hr10])
          hn1 (hfrC.trans hfr1) hinv1 hvals1 (fun z hz => (hval1 z hz).trans (hvalC z hz))
      refine ⟨tA'?, tB'?, tRem'?, sF, stF, _,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunL, rfl⟩)),
        hF0, hF1, hF5, hF6, hF7, hF8, hF10, hnF, hfrF, hinvF, hvalsF, hAF, hBF, hvalF, ?_⟩
      have hmul : (k + 1) * (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) * (Nat.log 2 (cap + 2) + 1) =
          k * (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) * (Nat.log 2 (cap + 2) + 1) +
          (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) * (Nat.log 2 (cap + 2) + 1) := by ring
      have hlog1 : 1 ≤ Nat.log 2 (cap + 2) + 1 := by omega
      have hstep_le : (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3000) * (Nat.log 2 (cap + 2) + 1) + 50 ≤
          (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) * (Nat.log 2 (cap + 2) + 1) := by
        clear * - hlog1; simp only [TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT]; omega
      clear * - hcS hcL hmul hstep_le
      simp only [Expr.size]; linarith
  -- Initialize registers and run the loop
  set s0 : State := startState [nb, t.rootId, pairsPtr, nxtPtr, m, fuel, outHeap] mem pos
  set r1 := Function.update s0.regs 7 0
  set r2 := Function.update r1 8 0
  set r3 := Function.update r2 9 0
  set r4 := Function.update r3 10 (outHeap + 2)
  have ha7 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 7) (val := 0) (st := s0) (by omega)
  have ha8 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 8) (val := 0) (st := ⟨mem, r1, pos⟩) (by omega)
  have ha9 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 9) (val := 0) (st := ⟨mem, r2, pos⟩) (by omega)
  have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 6) (.const 2))) ⟨mem, r3, pos⟩ .normal ⟨mem, r4, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨outHeap + 2, by
      simp [Expr.eval, r3, r2, r1, s0, startState, BinOp.eval, (by omega : 2 < 2 ^ w), hout2_lt], rfl, rfl, rfl⟩
  have hzero2 : ZeroFrom mem (outHeap + 2) := fun a ha => hheap.zero a (by omega)
  obtain ⟨tA?, tB1?, tRem?, sL, stL, cL, hrunL, hL0, hL1, hL5, hL6, hL7, hL8, hL10,
    hnL, hfrL, hinvL, hvalsL, hAL, hBL, hvalL, hcL⟩ :=
    hloop m 0 none none (some t) st ⟨mem, r4, pos⟩ xs [] (by omega) rfl (by simpa using hA_eq)
      (by simp [optList]) (by simp [optList]) (by simpa [optList] using ht_flat)
      (by simp [r4, r3, r2, r1, s0, startState]) (by simp [r4, r3, r2, r1, s0, startState, optRoot])
      (by simp [r4, r3, r2, r1, s0, startState]) (by simp [r4, r3, r2, r1, s0, startState])
      (by simp [r4, r3, r2, r1, s0, startState]) (by simp [r4, r3, r2, r1, s0, startState])
      (by simp [r4, r3, r2, r1, s0, startState]) (by simp [r4, r3, r2, r1, optRoot])
      (by simp [r4, r3, r2, optRoot]) (by simp [r4, r3]) (by simp [r4])
      hnodes (TreeFrame.refl hzero2) (by simpa [optTrees] using hf) hvals (fun _ _ => rfl)
  -- Final join: `tB? := join(tB1?, tRem?)`
  have hpermL : (optTrees tA? ++ optTrees tB1? ++ optTrees tRem? ++ rest).Perm
      (optTrees tB1? ++ optTrees tRem? ++ (optTrees tA? ++ rest)) := by
    have hp1 : (optTrees tA? ++ (optTrees tB1? ++ optTrees tRem?)).Perm ((optTrees tB1? ++ optTrees tRem?) ++ optTrees tA?) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hp1.append_right rest
  have hinvL' : TourForestInv cap sL (optTrees tB1? ++ optTrees tRem? ++ (optTrees tA? ++ rest)) :=
    (hinvL.perm hpermL).1
  obtain ⟨tB?, sF, oJ, stJ, cJ, hrunJ, hvJ, hnJ, hfrJ, hinvJ, hvalsJ, hlistJ, hvalJ, _, hcostJ⟩ :=
    tourJoinBody_runs (pos := stL.pos) C ω hnL hinvL' hvalsL hfuel hfuelW
      ⟨hrec2, by have := hheap.room; omega, hfrL.1, hheap.wide⟩
  have hcJ := runs_call_regs5 8 0 8 1 5 10 (st := stL) C.join_body hL0 hL8 hL1 hL5 hL10 hrunJ
  set rJ := Function.update stL.regs 8 oJ.value
  set mem1 := Function.update stJ.mem outHeap (optRoot tA?)
  set mem2 := Function.update mem1 (outHeap + 1) (optRoot tB?)
  have hst1 : Runs w p ω (.store (.reg 6) (.reg 7)) { stJ with regs := rJ } .normal { stJ with mem := mem1, regs := rJ } 3 :=
    runs_store_iff.mpr ⟨outHeap, optRoot tA?, by simp [Expr.eval, rJ, hL6], by simp [Expr.eval, rJ, hL7], rfl, rfl, rfl⟩
  have hst2 : Runs w p ω (.store (.bin .add (.reg 6) (.const 1)) (.reg 8))
      { stJ with mem := mem1, regs := rJ } .normal { stJ with mem := mem2, regs := rJ } 5 :=
    runs_store_iff.mpr ⟨outHeap + 1, optRoot tB?,
      by simp [Expr.eval, rJ, hL6, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : outHeap + 1 < 2 ^ w)],
      by simp [Expr.eval, rJ, hvJ], rfl, rfl, rfl⟩
  have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := { stJ with mem := mem2, regs := rJ }) (v := 0) (by omega)
  have hpermF : (optTrees tB? ++ (optTrees tA? ++ rest)).Perm (optTrees tA? ++ optTrees tB? ++ rest) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tB?) (l₂ := optTrees tA?)).append_right rest
  have hfr_all := hfrL.trans hfrJ
  have hn_fin : tourLayout.NodesAt mem2 nb cap sF :=
    NodesAt.congr tourLayout hnJ fun a ha => by
      have hlt : a < outHeap := lt_of_lt_of_le ha.2 hheap.rec_le
      dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨tA?, tB?, sF, .returned 0, { stJ with mem := mem2, regs := rJ }, _,
    tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10
      (tour_runs_seq_normal hrunL (tour_runs_seq_normal hcJ (tour_runs_seq_normal hst1 (tour_runs_seq_normal hst2 hret))))))),
    by simp [mem2, mem1], by simp [mem2], hn_fin,
    fun a ha => by dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr_all.1 a ha,
    fun a ha hnr => by
      dsimp only [mem2, mem1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr_all.2 a (by omega) hnr,
    (hinvJ.perm hpermF).1, hvalsJ, hAL, by rw [hlistJ, hBL],
    fun z hz => (hvalJ z hz).trans (hvalL z hz), ?_⟩
  have hpeqL := forestPhi_perm hpermL
  have hpeqF := forestPhi_perm hpermF
  have hpeq0 : forestPhi (optTrees none ++ optTrees none ++ optTrees (some t) ++ rest) = forestPhi (t :: rest) := by
    simp [optTrees]
  rw [← hpeqF]; rw [← hpeqL] at hcostJ; rw [hpeq0] at hcL
  have hlog1 : 1 ≤ Nat.log 2 (cap + 2) + 1 := by omega
  have hm1 : m * (2 * TOUR_SPLAY_AMORT + 2 * TOUR_JOIN_AMORT + 3200) ≤ m * TOUR_MOVE_STEP_AMORT :=
    Nat.mul_le_mul_left m (by unfold TOUR_SPLAY_AMORT TOUR_JOIN_AMORT TOUR_MOVE_STEP_AMORT; omega)
  have hm2 := Nat.mul_le_mul_right (Nat.log 2 (cap + 2) + 1) hm1
  have h1 : (m + 1) * TOUR_MOVE_STEP_AMORT * (Nat.log 2 (cap + 2) + 1) =
      m * TOUR_MOVE_STEP_AMORT * (Nat.log 2 (cap + 2) + 1) + TOUR_MOVE_STEP_AMORT * (Nat.log 2 (cap + 2) + 1) := by ring
  clear * - hcL hcostJ hm2 h1 hlog1
  simp only [TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT, TOUR_MOVE_STEP_AMORT] at hcL hcostJ hm2 h1 ⊢
  nlinarith

end MinCostFlow.SparseCore.Program
