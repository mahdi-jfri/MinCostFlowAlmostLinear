module

public import MinCostFlow.ExpanderDecomp.RouteProgBFSStep

import Mathlib.Tactic.Linarith

/-!
# Layered BFS Program: Main Layer-Loop Verification

Verifies `bfsMainLoopStmt` against `bfsLoop` by structural induction on the remaining layer
budget `rem`, matching exact layers, visited set, distance map, termination flags, and
cost `≤ 140 * res.cost + 5`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Helper Lemmas on Reversed Layer Lists -/

lemma sum_map_length_take_append (ls : List (List ℕ)) (L : List ℕ) {r : ℕ} (hr : r ≤ ls.length) :
    (((ls ++ [L]).take r).map List.length).sum = ((ls.take r).map List.length).sum := by
  rw [List.take_append_of_le_length hr]

lemma sum_map_length_append_singleton (ls : List (List ℕ)) (L : List ℕ) :
    ((ls ++ [L]).map List.length).sum = (ls.map List.length).sum + L.length := by
  simp [List.map_append, List.sum_append]

lemma length_le_sum_map_length (ls : List (List ℕ)) (h : ∀ L ∈ ls, 0 < L.length) :
    ls.length ≤ (ls.map List.length).sum := by
  induction ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := h L List.mem_cons_self
    have h2 := ih (fun M hM => h M (List.mem_cons_of_mem _ hM))
    omega

lemma bfsLoop_fields_add (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ)
    (rem curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
    (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost delta : ℕ) :
    let A := bfsLoop adj V stopSet rem curDist frontier revLayers vis dist (cost + delta)
    let B := bfsLoop adj V stopSet rem curDist frontier revLayers vis dist cost
    A.layers = B.layers ∧ A.visited = B.visited ∧ A.dist = B.dist ∧
    A.maxReached = B.maxReached ∧ A.hitStop = B.hitStop ∧ A.exhausted = B.exhausted := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero => simp [bfsLoop]
  | succ rem ih =>
    simp only [bfsLoop]
    set rr := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
    split_ifs
    · simp
    · simp
    · have h := ih (curDist + 1) rr.1 (rr.1 :: revLayers) rr.2.1 rr.2.2.1
        (cost + rr.2.2.2 + 1 + rr.1.length)
      have heq : cost + delta + rr.2.2.2 + 1 + rr.1.length =
        cost + rr.2.2.2 + 1 + rr.1.length + delta := by omega
      rw [heq]; exact h

lemma bfsMainLoop_triple {w : ℕ} {p : Program}
    {X V stopSet : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : BfsCfg} {cfgAddr m2 : ℕ} {mem0 : ℕ → ℕ}
    (hVX : V ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hcsr0 : NbCsrAt mem0 cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hmask0 : ∀ v < X.card, mem0 (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hstop : cfg.hasStop = 0 → stopSet = ∅)
    (hstop0 : cfg.hasStop ≠ 0 →
      ∀ v < X.card, mem0 (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet) :
    ∀ (rem curDist layerStart : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
      (vis : Finset ℕ) (dist : ℕ → Option ℕ) (st0 : State),
      rem < 2 ^ w →
      vis ⊆ V →
      (∀ L ∈ revLayers, 0 < L.length ∧ ∀ x ∈ L, x ∈ vis) →
      (hrevLen : revLayers.length = curDist + 1) →
      (∀ x ∈ frontier, x ∈ vis) →
      0 < frontier.length →
      layerStart + frontier.length = vis.card →
      ((revLayers.reverse).map List.length).sum = vis.card →
      (∀ r ≤ curDist + 1,
        st0.mem (cfg.layerOffAddr + r) = (((revLayers.reverse).take r).map List.length).sum) →
      (∀ r (hr : r < curDist + 1),
        ListAt st0.mem
          (cfg.layerDataAddr + (((revLayers.reverse).take r).map List.length).sum)
          (((revLayers.reverse)[r]'(by simp [hrevLen, hr])).map (locOf X))) →
      ListAt st0.mem (cfg.layerDataAddr + layerStart) (frontier.map (locOf X)) →
      (∀ v < X.card, st0.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ vis) →
      (∀ v < X.card, origOf X v ∉ vis →
        st0.mem (cfg.visStampAddr + v) = mem0 (cfg.visStampAddr + v)) →
      (∀ v < X.card, origOf X v ∈ vis →
        dist (origOf X v) = some (st0.mem (cfg.distAddr + v))) →
      (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st0.mem a = mem0 a) →
      (∀ r ≤ 19, st0.regs r =
        match r with
        | 0 => cfgAddr | 1 => cfg.offAddr | 2 => cfg.nbAddr
        | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
        | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
        | 8 => cfg.visStampAddr | 9 => cfg.distAddr
        | 10 => cfg.layerOffAddr | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
        | 13 => cfg.bfsGen | 14 => rem
        | 17 => curDist | 18 => layerStart | 19 => vis.card
        | r => st0.regs r) →
      ∀ ω,
        let res := bfsLoop adj V stopSet rem curDist frontier revLayers vis dist 0
        ∃ o st' c,
          Runs w p ω bfsMainLoopStmt st0 o st' c ∧
          (match o with
           | .returned v =>
             v = res.visited.card ∧
             BfsOutAt st'.mem X cfg cfgAddr res ∧
             (∀ v < X.card, origOf X v ∉ res.visited →
               st'.mem (cfg.visStampAddr + v) = mem0 (cfg.visStampAddr + v)) ∧
             (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st'.mem a = mem0 a)
           | .normal =>
             res.hitStop = false ∧ res.exhausted = false ∧
             st'.regs 0 = cfgAddr ∧
             st'.regs 17 = res.maxReached ∧
             st'.regs 19 = res.visited.card ∧
             res.layers.length = res.maxReached + 1 ∧
             res.visited.card ≤ X.card ∧
             res.maxReached + 1 ≤ X.card ∧
             ((res.layers).map List.length).sum = res.visited.card ∧
             (∀ r ≤ res.layers.length,
               st'.mem (cfg.layerOffAddr + r) = ((res.layers.take r).map List.length).sum) ∧
             (∀ r (hr : r < res.layers.length),
               ListAt st'.mem (cfg.layerDataAddr + ((res.layers.take r).map List.length).sum)
                 ((res.layers[r]'hr).map (locOf X))) ∧
             (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.visited) ∧
             (∀ v < X.card, origOf X v ∉ res.visited →
               st'.mem (cfg.visStampAddr + v) = mem0 (cfg.visStampAddr + v)) ∧
             (∀ v < X.card, origOf X v ∈ res.visited →
               res.dist (origOf X v) = some (st'.mem (cfg.distAddr + v))) ∧
             (∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st'.mem a = mem0 a)) ∧
          c ≤ 140 * res.cost + 5 := by
  rcases hdisj with ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
    hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
    hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
    hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
    hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  have hdisj' : BfsDisj w X.card m2 cfg cfgAddr :=
    ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
      hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
      hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
      hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
      hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  intro rem
  induction rem with
  | zero =>
    intro curDist layerStart frontier revLayers vis dist st0
      _ hvisV hrev_mem hrevLen _ _ _ hsum_len hoff hld _ hvis hvis_out hdist hfr hregs ω
    have hvis_le_nX : vis.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hvisV hVX)
    have hcur_le_nX : curDist + 1 ≤ X.card := by
      have h1 := length_le_sum_map_length revLayers.reverse
        (fun L hL => (hrev_mem L (List.mem_reverse.mp hL)).1)
      simp only [List.length_reverse] at h1
      omega
    have hr0 : st0.regs 0 = cfgAddr := hregs 0 (by decide)
    have hr14 : st0.regs 14 = 0 := hregs 14 (by decide)
    have hr17 : st0.regs 17 = curDist := hregs 17 (by decide)
    have hr19 : st0.regs 19 = vis.card := hregs 19 (by decide)
    refine ⟨.normal, st0, 2,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr14], rfl, rfl, rfl⟩), ?_, ?_⟩
    · simp only [bfsLoop, List.length_reverse, hrevLen]
      exact ⟨trivial, trivial, hr0, hr17, hr19, trivial, hvis_le_nX, hcur_le_nX, hsum_len,
        hoff, hld, hvis, hvis_out, hdist, hfr⟩
    · simp [bfsLoop]
  | succ rem ih =>
    intro curDist layerStart frontier revLayers vis dist st0
      hrem_lt hvisV hrev_mem hrevLen hfront_vis hfront_pos hstart_end hsum_len
      hoff hld hfront_at hvis hvis_out hdist hfr hregs ω
    have hvis_le_nX : vis.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hvisV hVX)
    have hcur_le_vis : curDist + 1 ≤ vis.card := by
      have h1 := length_le_sum_map_length revLayers.reverse
        (fun L hL => (hrev_mem L (List.mem_reverse.mp hL)).1)
      simp only [List.length_reverse] at h1
      omega
    have hcur_lt_nX : curDist + 1 ≤ X.card := le_trans hcur_le_vis hvis_le_nX
    have hfront_sub_X : ∀ u ∈ frontier, u ∈ X := fun u hu => hVX (hvisV (hfront_vis u hu))
    have hcsr_st0 : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj := by
      refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
      · rw [hfr _ (hr_off _ ⟨by omega, by omega⟩)]; exact hcsr0.1 i hi
      · have hbnd : adjCsrOff X adj i + j < m2 := by
          have h1 : adjCsrOff X adj (i + 1) = adjCsrOff X adj i + (adj (origOf X i)).length := by
            simp [adjCsrOff, Finset.sum_range_succ]
          have h2 := adjCsrOff_mono X adj (by omega : i + 1 ≤ X.card)
          omega
        rw [hfr _ (hr_nb _ ⟨by omega, by omega⟩)]; exact hcsr0.2 i hi j hj
    have hmask_st0 : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V := by
      intro v hv'; rw [hfr _ (hr_mask _ ⟨by omega, by omega⟩)]; exact hmask0 v hv'
    -- Run bfsExpandStmt
    have hexp := bfsExpand_triple (p := p) (st0 := st0) hVX hadj_X hvisV hfront_sub_X (by omega) hcur_lt_nX
      hcsr_st0 hm2 hdisj' hmask_st0 hvis hdist hfront_at
      (by
        intro r hr_le
        have := hregs r hr_le
        interval_cases r <;> first | exact this | (simp only at this ⊢; omega) | rfl)
      st0 ω rfl
    rcases hexp with ⟨o1, st1, c1, hrun1, hpost1, hc1⟩
    cases o1 with
    | returned _ => exact hpost1.elim
    | normal =>
      rcases hpost1 with ⟨hr1, hr1_20, hvis1, hvis1_out, hdist1, htmp1, hfr1⟩
      set r := bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist
      have hr_sub := bfsExpandFrontier_subset_V adj V (curDist + 1) frontier [] vis dist
        hvisV (fun _ h => by cases h)
      have hr_len : (r.1.length - ([] : List ℕ).length) + vis.card = r.2.1.card ∧
          ([] : List ℕ).length ≤ r.1.length :=
        bfsExpandFrontier_length_card adj V (curDist + 1) frontier [] vis dist
      simp only [List.length_nil, Nat.sub_zero] at hr_len
      have hr_card_le : r.2.1.card ≤ X.card :=
        Finset.card_le_card (Finset.Subset.trans hr_sub.2.1 hVX)
      have hst1_vis_out : ∀ v < X.card, origOf X v ∉ r.2.1 →
          st1.mem (cfg.visStampAddr + v) = mem0 (cfg.visStampAddr + v) := by
        intro v hv' hnot
        rw [hvis1_out v hv' hnot, hvis_out v hv' (fun hm => hnot (hr_sub.1 hm))]
      have hst1_fr : ∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st1.mem a = mem0 a := by
        intro a ha
        rw [hfr1 a (fun h => ha (bfsScanWriteSet_sub h)), hfr a ha]
      have hst1_lo : ∀ idx ≤ curDist + 1,
          st1.mem (cfg.layerOffAddr + idx) = (((revLayers.reverse).take idx).map List.length).sum := by
        intro idx hidx
        have hnot : ¬ BfsScanWriteSet X.card cfg (cfg.layerOffAddr + idx) := by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
          · rcases hd_vlo with h | h <;> omega
          · rcases hd_dlo with h | h <;> omega
          · rcases hd_lot with h | h <;> omega
        rw [hfr1 _ hnot]; exact hoff idx hidx
      have hst1_ld : ∀ idx (hidx : idx < curDist + 1),
          ListAt st1.mem
            (cfg.layerDataAddr + (((revLayers.reverse).take idx).map List.length).sum)
            (((revLayers.reverse)[idx]'(by simp [hrevLen, hidx])).map (locOf X)) := by
        intro idx hidx j hj
        have hj_bnd : (((revLayers.reverse).take idx).map List.length).sum + j < X.card := by
          have hle_sum : (((revLayers.reverse).take idx).map List.length).sum +
              ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx])).length ≤
              ((revLayers.reverse).map List.length).sum := by
            have h1 : (((revLayers.reverse).take (idx + 1)).map List.length).sum =
                (((revLayers.reverse).take idx).map List.length).sum +
                ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx])).length := by
              rw [List.take_succ_eq_append_getElem (by simp [hrevLen, hidx]), List.map_append,
                List.sum_append, List.map_singleton, List.sum_singleton]
            rw [← h1]
            have h2 := List.take_append_drop (idx + 1) revLayers.reverse
            have h3 := congr_arg (fun ls => (ls.map List.length).sum) h2
            simp only [List.map_append, List.sum_append] at h3
            omega
          simp only [List.length_map] at hj
          omega
        have hnot : ¬ BfsScanWriteSet X.card cfg
            (cfg.layerDataAddr + (((revLayers.reverse).take idx).map List.length).sum + j) := by
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
          · rcases hd_vld with h | h <;> omega
          · rcases hd_dld with h | h <;> omega
          · rcases hd_ldt with h | h <;> omega
        rw [hfr1 _ hnot]; exact hld idx hidx j hj
      have hr1_0 : st1.regs 0 = cfgAddr := (hr1 0 (by decide)).trans (hregs 0 (by decide))
      have hr1_14 : st1.regs 14 = rem + 1 := (hr1 14 (by decide)).trans (hregs 14 (by decide))
      have hr1_17 : st1.regs 17 = curDist := (hr1 17 (by decide)).trans (hregs 17 (by decide))
      have hr1_19 : st1.regs 19 = vis.card := (hr1 19 (by decide)).trans (hregs 19 (by decide))
      have hr14_0 : st0.regs 14 = rem + 1 := hregs 14 (by decide)
      by_cases hnxt_empty : r.1.isEmpty
      · -- Exhausted branch: r.1 = [], so r.2.1 = vis, write outputs and return
        have hnxt_empty' : (bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist).1.isEmpty = true :=
          hnxt_empty
        have hnxt_len0 : r.1.length = 0 := by simp [List.isEmpty_iff] at hnxt_empty; simp [hnxt_empty]
        have hvis_eq : r.2.1 = vis := by
          have hcard : r.2.1.card ≤ vis.card := by
            have := hr_len.1; omega
          exact (Finset.eq_of_subset_of_card_le hr_sub.1 hcard).symm
        have hwr := bfsWriteRet_triple (p := p) (st0 := st1) hr1_0 hw_cfg
          (vNumL := curDist + 1) (vTotV := vis.card) (vMaxR := curDist) (vHit := 0) (vExh := 1)
          (eNumL := .bin .add (.reg 17) (.const 1)) (eTotV := .reg 19) (eMaxR := .reg 17)
          (eHit := .const 0) (eExh := .const 1)
          (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr)
          (by intro e he m; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl)
          st1 ω rfl
        rcases hwr with ⟨o2, st2, c2, hrun2, hpost2, hc2⟩
        cases o2 with
        | normal => exact hpost2.elim
        | returned v =>
          rcases hpost2 with ⟨hv_eq, h16, h17, h18, h19, h20, hfr2⟩
          have hbody_run : Runs w p ω
              (seqStmts
                [ bfsExpandStmt
                , .cond (.reg 20)
                    (seqStmts
                      [ bfsRevCopyStmt
                      , .assign 18 (.reg 19)
                      , .assign 19 (.bin .add (.reg 19) (.reg 20))
                      , .assign 17 (.bin .add (.reg 17) (.const 1))
                      , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
                      , .cond (.reg 21)
                          (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                            (.const 1) (.const 0))
                          (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
                    (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                      (.const 0) (.const 1)) ])
              st0 (.returned v) st2 (c1 + ((Expr.reg 20).size + c2 + 1) + 1) := by
            dsimp only [seqStmts]
            refine runs_seq_iff.mpr (Or.inr ⟨st1, c1, (Expr.reg 20).size + c2 + 1, hrun1, ?_, rfl⟩)
            refine runs_cond_iff.mpr ⟨0, c2, by simp [Expr.eval, hr1_20, hnxt_len0], ?_, rfl⟩
            simpa using hrun2
          refine ⟨.returned v, st2, (Expr.reg 14).size + (c1 + ((Expr.reg 20).size + c2 + 1) + 1) + 1,
            runs_loop_iff.mpr (Or.inr (Or.inl ⟨rem + 1, v, _,
              by simp [Expr.eval, hr14_0], Nat.succ_ne_zero _, hbody_run, rfl, rfl⟩)), ?_, ?_⟩
          · dsimp only
            simp only [bfsLoop, hnxt_empty', ↓reduceIte]
            refine ⟨by rw [hv_eq, hvis_eq], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
            · intro idx hidx
              simp only [List.length_reverse, hrevLen] at hidx
              have hne : cfg.layerOffAddr + idx < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + idx := by
                rcases hd_loc with h | h <;> omega
              rw [hfr2 _ hne]; exact hst1_lo idx hidx
            · intro idx hidx j hj
              simp only [List.length_reverse, hrevLen] at hidx
              have hj_lt : (((revLayers.reverse).take idx).map List.length).sum + j < X.card := by
                have hle_sum : (((revLayers.reverse).take idx).map List.length).sum +
                    ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx])).length ≤
                    ((revLayers.reverse).map List.length).sum := by
                  have h1 : (((revLayers.reverse).take (idx + 1)).map List.length).sum =
                      (((revLayers.reverse).take idx).map List.length).sum +
                      ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx])).length := by
                    rw [List.take_succ_eq_append_getElem (by simp [hrevLen, hidx]), List.map_append,
                      List.sum_append, List.map_singleton, List.sum_singleton]
                  rw [← h1]
                  have h2 := List.take_append_drop (idx + 1) revLayers.reverse
                  have h3 := congr_arg (fun ls => (ls.map List.length).sum) h2
                  simp only [List.map_append, List.sum_append] at h3
                  omega
                simp only [List.length_map] at hj
                omega
              have hne : cfg.layerDataAddr + (((revLayers.reverse).take idx).map List.length).sum + j < cfgAddr + 16 ∨
                  cfgAddr + 21 ≤ cfg.layerDataAddr + (((revLayers.reverse).take idx).map List.length).sum + j := by
                rcases hd_ldc with h | h <;> omega
              rw [hfr2 _ hne]; exact hst1_ld idx hidx j hj
            · intro u hu
              have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                rcases hd_vc with h | h <;> omega
              rw [hfr2 _ hne]; exact hvis1 u hu
            · intro u hu hm
              have hne : cfg.distAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.distAddr + u := by
                rcases hd_dc with h | h <;> omega
              rw [hfr2 _ hne]; exact hdist1 u hu hm
            · simp [h16, hrevLen]
            · rw [h17, hvis_eq]
            · exact h18
            · exact h19
            · exact h20
            · intro u hu hnot
              have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                rcases hd_vc with h | h <;> omega
              rw [hfr2 _ hne]; exact hst1_vis_out u hu hnot
            · intro a ha
              have hne : a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a := by
                by_contra hc; push Not at hc
                exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
              rw [hfr2 a hne]; exact hst1_fr a ha
          · simp only [bfsLoop, hnxt_empty', ↓reduceIte, Expr.size] at hc1 hc2 ⊢
            dsimp only [r] at *
            omega
      · -- Non-empty next layer: r.1.length > 0
        have hnxt_empty' : (bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist).1.isEmpty = false :=
          Bool.eq_false_iff.mpr hnxt_empty
        have hnxt_pos : 0 < r.1.length := by
          cases h : r.1 with
          | nil => simp [h] at hnxt_empty
          | cons _ _ => simp
        have hnxt_sub_X : ∀ x ∈ r.1, x ∈ X := fun x hx => hVX (hr_sub.2.1 (hr_sub.2.2 x hx))
        have hstop_st1 : cfg.hasStop ≠ 0 →
            ∀ v < X.card, st1.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet := by
          intro hhs v hv'
          rw [hst1_fr _ (hr_stop hhs _ ⟨by omega, by omega⟩)]
          exact hstop0 hhs v hv'
        -- Run bfsRevCopyStmt
        have hrev := bfsRevCopy_triple (p := p) (st0 := st1) (nxt := r.1) (layerEnd := vis.card)
          hnxt_sub_X hdisj' (by omega) htmp1 hstop hstop_st1
          (by
            intro r' hr'
            interval_cases r' <;> first
              | rfl
              | exact (hr1 _ (by decide)).trans (hregs _ (by decide))
              | exact hr1_20)
          st1 ω rfl
        rcases hrev with ⟨o2, st2, c2, hrun2, hpost2, hc2⟩
        cases o2 with
        | returned _ => exact hpost2.elim
        | normal =>
          rcases hpost2 with ⟨hr2, hr2_21, hld2_new, hfr2⟩
          -- After bfsRevCopyStmt: run 4 statements (r18 := r19; r19 := r19 + r20; r17 := r17 + 1; layerOff[r17+1] := r19)
          set newEnd := vis.card + r.1.length
          have hnewEnd_eq : newEnd = r.2.1.card := by omega
          have hnewDist_le : curDist + 1 + 1 ≤ X.card := by
            have : curDist + 1 + 1 ≤ r.2.1.card := by omega
            omega
          have hr2_0 : st2.regs 0 = cfgAddr := (hr2 0 (by decide)).trans hr1_0
          have hr2_10 : st2.regs 10 = cfg.layerOffAddr :=
            (hr2 10 (by decide)).trans ((hr1 10 (by decide)).trans (hregs 10 (by decide)))
          have hr2_14 : st2.regs 14 = rem + 1 := (hr2 14 (by decide)).trans hr1_14
          have hr2_17 : st2.regs 17 = curDist := (hr2 17 (by decide)).trans hr1_17
          have hr2_19 : st2.regs 19 = vis.card := (hr2 19 (by decide)).trans hr1_19
          have hr2_20 : st2.regs 20 = r.1.length := (hr2 20 (by decide)).trans hr1_20
          set regs3 := Function.update (Function.update (Function.update st2.regs 18 vis.card)
            19 newEnd) 17 (curDist + 1)
          set mem3 := Function.update st2.mem (cfg.layerOffAddr + (curDist + 1 + 1)) newEnd
          set st3 : State := { mem := mem3, regs := regs3, pos := st2.pos }
          have hmid_run : ∃ c3,
              Runs w p ω
                (seqStmts
                  [ .assign 18 (.reg 19)
                  , .assign 19 (.bin .add (.reg 19) (.reg 20))
                  , .assign 17 (.bin .add (.reg 17) (.const 1))
                  , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19) ])
                st2 .normal st3 c3 ∧ c3 ≤ 30 := by
            have htr : Triple w p (fun st => st = st2)
                (seqStmts
                  [ .assign 18 (.reg 19)
                  , .assign 19 (.bin .add (.reg 19) (.reg 20))
                  , .assign 17 (.bin .add (.reg 17) (.const 1))
                  , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19) ])
                (normalPost fun st' => st' = st3) (fun _ => 30) := by
              wram_enter; subst st; dsimp only [seqStmts]
              refine runs_seq_assign_le (v := vis.card) (by eval_expr) ?_
              refine runs_seq_assign_le (v := newEnd) (by eval_expr) ?_
              refine runs_seq_assign_le (v := curDist + 1) (by eval_expr) ?_
              refine runs_store_le (x := cfg.layerOffAddr + (curDist + 1 + 1)) (v := newEnd)
                (by eval_expr) (by eval_expr) ?_ ?_
              · rfl
              · wram_cost
            obtain ⟨o3, st3', c3, hr3, hp3, hc3⟩ := htr st2 ω rfl
            cases o3 with
            | returned _ => exact hp3.elim
            | normal => subst hp3; exact ⟨c3, hr3, hc3⟩
          rcases hmid_run with ⟨c3, hrun3, hc3⟩
          -- Prove shared memory invariants on st3 for `(r.1 :: revLayers).reverse = revLayers.reverse ++ [r.1]`
          have hrev_app : (r.1 :: revLayers).reverse = revLayers.reverse ++ [r.1] := List.reverse_cons
          have hsum_new : (((r.1 :: revLayers).reverse).map List.length).sum = r.2.1.card := by
            rw [hrev_app, sum_map_length_append_singleton, hsum_len]; omega
          have hst3_lo : ∀ idx ≤ curDist + 1 + 1,
              st3.mem (cfg.layerOffAddr + idx) =
                ((((r.1 :: revLayers).reverse).take idx).map List.length).sum := by
            intro idx hidx
            dsimp only [st3, mem3]
            by_cases hlast : idx = curDist + 1 + 1
            · subst hlast
              rw [Function.update_self, List.take_of_length_le (by simp [hrevLen]), hsum_new, hnewEnd_eq]
            · rw [Function.update_of_ne (by omega)]
              have hne : cfg.layerOffAddr + idx < cfg.layerDataAddr + vis.card ∨
                  cfg.layerDataAddr + vis.card + r.1.length ≤ cfg.layerOffAddr + idx := by
                rcases hd_lold with h | h <;> omega
              rw [hfr2 _ hne, hst1_lo idx (by omega), hrev_app,
                sum_map_length_take_append revLayers.reverse r.1 (by simp [hrevLen]; omega)]
          have hst3_ld : ∀ idx (hidx : idx < curDist + 1 + 1),
              ListAt st3.mem
                (cfg.layerDataAddr + ((((r.1 :: revLayers).reverse).take idx).map List.length).sum)
                ((((r.1 :: revLayers).reverse)[idx]'(by simp [hrevLen, hidx])).map (locOf X)) := by
            intro idx hidx j hj
            dsimp only [st3, mem3]
            by_cases hlast : idx = curDist + 1
            · subst hlast
              have htake_eq : (((r.1 :: revLayers).reverse).take (curDist + 1)).map List.length =
                  (revLayers.reverse).map List.length := by
                rw [hrev_app, List.take_append_of_le_length (by simp [hrevLen]),
                  List.take_of_length_le (by simp [hrevLen])]
              have hget_eq : ((r.1 :: revLayers).reverse)[curDist + 1]'(by simp [hrevLen]) = r.1 := by
                simp only [hrev_app]
                rw [List.getElem_append_right (by simp [hrevLen])]
                simp [hrevLen]
              simp only [htake_eq, hsum_len, hget_eq] at hj ⊢
              have hne_lo : cfg.layerDataAddr + vis.card + j ≠ cfg.layerOffAddr + (curDist + 1 + 1) := by
                simp only [List.length_map] at hj
                rcases hd_lold with h | h <;> omega
              rw [Function.update_of_ne hne_lo]
              exact hld2_new j hj
            · have hidx_old : idx < curDist + 1 := by omega
              have htake_eq : ((((r.1 :: revLayers).reverse).take idx).map List.length).sum =
                  (((revLayers.reverse).take idx).map List.length).sum := by
                rw [hrev_app, sum_map_length_take_append revLayers.reverse r.1 (by simp [hrevLen]; omega)]
              have hget_eq : ((r.1 :: revLayers).reverse)[idx]'(by simp [hrevLen, hidx]) =
                  (revLayers.reverse)[idx]'(by simp [hrevLen, hidx_old]) := by
                simp only [hrev_app]
                rw [List.getElem_append_left (by simp [hrevLen, hidx_old])]
              simp only [htake_eq, hget_eq] at hj ⊢
              have hj_lt_vis : (((revLayers.reverse).take idx).map List.length).sum + j < vis.card := by
                have hle_sum : (((revLayers.reverse).take idx).map List.length).sum +
                    ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx_old])).length ≤
                    ((revLayers.reverse).map List.length).sum := by
                  have h1 : (((revLayers.reverse).take (idx + 1)).map List.length).sum =
                      (((revLayers.reverse).take idx).map List.length).sum +
                      ((revLayers.reverse)[idx]'(by simp [hrevLen, hidx_old])).length := by
                    rw [List.take_succ_eq_append_getElem (by simp [hrevLen, hidx_old]),
                      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
                  rw [← h1]
                  have h2 := List.take_append_drop (idx + 1) revLayers.reverse
                  have h3 := congr_arg (fun ls => (ls.map List.length).sum) h2
                  simp only [List.map_append, List.sum_append] at h3
                  omega
                simp only [List.length_map] at hj
                omega
              have hne_lo : cfg.layerDataAddr + (((revLayers.reverse).take idx).map List.length).sum + j ≠
                  cfg.layerOffAddr + (curDist + 1 + 1) := by
                rcases hd_lold with h | h <;> omega
              rw [Function.update_of_ne hne_lo, hfr2 _ (Or.inl (by omega))]
              exact hst1_ld idx hidx_old j hj
          have hst3_vis : ∀ v < X.card, st3.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ r.2.1 := by
            intro v hv'
            dsimp only [st3, mem3]
            have h1 : cfg.visStampAddr + v ≠ cfg.layerOffAddr + (curDist + 1 + 1) :=
              disjRange_ne hd_vlo hv' (by omega)
            have h2 : cfg.visStampAddr + v < cfg.layerDataAddr + vis.card ∨
                cfg.layerDataAddr + vis.card + r.1.length ≤ cfg.visStampAddr + v := by
              rcases hd_vld with h | h <;> omega
            rw [Function.update_of_ne h1, hfr2 _ h2]; exact hvis1 v hv'
          have hst3_vis_out : ∀ v < X.card, origOf X v ∉ r.2.1 →
              st3.mem (cfg.visStampAddr + v) = mem0 (cfg.visStampAddr + v) := by
            intro v hv' hnot
            dsimp only [st3, mem3]
            have h1 : cfg.visStampAddr + v ≠ cfg.layerOffAddr + (curDist + 1 + 1) :=
              disjRange_ne hd_vlo hv' (by omega)
            have h2 : cfg.visStampAddr + v < cfg.layerDataAddr + vis.card ∨
                cfg.layerDataAddr + vis.card + r.1.length ≤ cfg.visStampAddr + v := by
              rcases hd_vld with h | h <;> omega
            rw [Function.update_of_ne h1, hfr2 _ h2]; exact hst1_vis_out v hv' hnot
          have hst3_dist : ∀ v < X.card, origOf X v ∈ r.2.1 →
              r.2.2.1 (origOf X v) = some (st3.mem (cfg.distAddr + v)) := by
            intro v hv' hm
            dsimp only [st3, mem3]
            have h1 : cfg.distAddr + v ≠ cfg.layerOffAddr + (curDist + 1 + 1) :=
              disjRange_ne hd_dlo hv' (by omega)
            have h2 : cfg.distAddr + v < cfg.layerDataAddr + vis.card ∨
                cfg.layerDataAddr + vis.card + r.1.length ≤ cfg.distAddr + v := by
              rcases hd_dld with h | h <;> omega
            rw [Function.update_of_ne h1, hfr2 _ h2]; exact hdist1 v hv' hm
          have hst3_fr : ∀ a, ¬ BfsWriteSet X.card cfg cfgAddr a → st3.mem a = mem0 a := by
            intro a ha
            dsimp only [st3, mem3]
            have h1 : a ≠ cfg.layerOffAddr + (curDist + 1 + 1) := fun h =>
              ha (Or.inr (Or.inr (Or.inl (by omega))))
            have h2 : a < cfg.layerDataAddr + vis.card ∨ cfg.layerDataAddr + vis.card + r.1.length ≤ a := by
              by_contra hc; push Not at hc
              exact ha (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
            rw [Function.update_of_ne h1, hfr2 a h2]; exact hst1_fr a ha
          have hr3_0 : st3.regs 0 = cfgAddr := by simp [st3, regs3, hr2_0]
          have hr3_17 : st3.regs 17 = curDist + 1 := by simp [st3, regs3]
          have hr3_19 : st3.regs 19 = newEnd := by simp [st3, regs3]
          have hr3_21 : st3.regs 21 = (if r.1.any (fun v => decide (v ∈ stopSet)) then 1 else 0) := by
            simp [st3, regs3, hr2_21]
          by_cases hhit : r.1.any (fun v => decide (v ∈ stopSet))
          · -- Hit stopSet: write outputs and return
            have hhit' : ((bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist).1.any
                fun v => decide (v ∈ stopSet)) = true := hhit
            have hwr := bfsWriteRet_triple (p := p) (st0 := st3) hr3_0 hw_cfg
              (vNumL := curDist + 1 + 1) (vTotV := newEnd) (vMaxR := curDist + 1) (vHit := 1) (vExh := 0)
              (eNumL := .bin .add (.reg 17) (.const 1)) (eTotV := .reg 19) (eMaxR := .reg 17)
              (eHit := .const 1) (eExh := .const 0)
              (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr) (by eval_expr)
              (by intro e he m; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                  rcases he with rfl | rfl | rfl | rfl | rfl <;> rfl)
              st3 ω rfl
            rcases hwr with ⟨o4, st4, c4, hrun4, hpost4, hc4⟩
            cases o4 with
            | normal => exact hpost4.elim
            | returned v =>
              rcases hpost4 with ⟨hv_eq, h16, h17, h18, h19, h20, hfr4⟩
              have hcond21 : Runs w p ω
                  (.cond (.reg 21)
                    (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                      (.const 1) (.const 0))
                    (.assign 14 (.bin .sub (.reg 14) (.const 1))))
                  st3 (.returned v) st4 ((Expr.reg 21).size + c4 + 1) :=
                runs_cond_iff.mpr ⟨1, c4, by simp [Expr.eval, hr3_21, hhit], by simpa using hrun4, rfl⟩
              have htrue_run : ∃ cT,
                  Runs w p ω
                    (seqStmts
                      [ bfsRevCopyStmt
                      , .assign 18 (.reg 19)
                      , .assign 19 (.bin .add (.reg 19) (.reg 20))
                      , .assign 17 (.bin .add (.reg 17) (.const 1))
                      , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
                      , .cond (.reg 21)
                          (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                            (.const 1) (.const 0))
                          (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
                    st1 (.returned v) st4 cT ∧ cT ≤ c2 + c3 + c4 + 10 := by
                rcases runs_seq_iff.mp hrun3 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
                · cases h
                rcases runs_seq_iff.mp hrb with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩
                · cases h
                rcases runs_seq_iff.mp hrb2 with ⟨_, _, _, h, _⟩ | ⟨sc, cc1, cc2, hrc1, hrc2, rfl⟩
                · cases h
                refine ⟨c2 + (ca + (cb1 + (cc1 + (cc2 + ((Expr.reg 21).size + c4 + 1) + 1) + 1) + 1) + 1) + 1, ?_, ?_⟩
                · dsimp only [seqStmts]
                  exact runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
                    runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
                      runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
                        runs_seq_iff.mpr (Or.inr ⟨sc, cc1, _, hrc1,
                          runs_seq_iff.mpr (Or.inr ⟨st3, cc2, _, hrc2, hcond21, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
                · simp only [Expr.size]; omega
              rcases htrue_run with ⟨cT, hrunT, hcT⟩
              have hbody_run : Runs w p ω
                  (seqStmts
                    [ bfsExpandStmt
                    , .cond (.reg 20)
                        (seqStmts
                          [ bfsRevCopyStmt
                          , .assign 18 (.reg 19)
                          , .assign 19 (.bin .add (.reg 19) (.reg 20))
                          , .assign 17 (.bin .add (.reg 17) (.const 1))
                          , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
                          , .cond (.reg 21)
                              (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                                (.const 1) (.const 0))
                              (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
                        (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                          (.const 0) (.const 1)) ])
                  st0 (.returned v) st4 (c1 + ((Expr.reg 20).size + cT + 1) + 1) := by
                dsimp only [seqStmts]
                refine runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, ?_, rfl⟩)
                refine runs_cond_iff.mpr ⟨r.1.length, cT, by simp [Expr.eval, hr1_20], ?_, rfl⟩
                simpa [Nat.ne_of_gt hnxt_pos] using hrunT
              refine ⟨.returned v, st4, _,
                runs_loop_iff.mpr (Or.inr (Or.inl ⟨rem + 1, v, _,
                  by simp [Expr.eval, hr14_0], Nat.succ_ne_zero _, hbody_run, rfl, rfl⟩)), ?_, ?_⟩
              · dsimp only
                simp only [bfsLoop, hnxt_empty', Bool.false_eq_true, ↓reduceIte, hhit']
                refine ⟨by rw [hv_eq, hnewEnd_eq], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
                · intro idx hidx
                  simp only [List.length_reverse, List.length_cons, hrevLen] at hidx
                  have hne : cfg.layerOffAddr + idx < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.layerOffAddr + idx := by
                    rcases hd_loc with h | h <;> omega
                  rw [hfr4 _ hne]; exact hst3_lo idx hidx
                · intro idx hidx j hj
                  simp only [List.length_reverse, List.length_cons, hrevLen] at hidx
                  have hj_lt : ((((r.1 :: revLayers).reverse).take idx).map List.length).sum + j < X.card := by
                    have hle_sum : ((((r.1 :: revLayers).reverse).take idx).map List.length).sum +
                        (((r.1 :: revLayers).reverse)[idx]'(by simp [hrevLen, hidx])).length ≤
                        (((r.1 :: revLayers).reverse).map List.length).sum := by
                      have h1 : ((((r.1 :: revLayers).reverse).take (idx + 1)).map List.length).sum =
                          ((((r.1 :: revLayers).reverse).take idx).map List.length).sum +
                          (((r.1 :: revLayers).reverse)[idx]'(by simp [hrevLen, hidx])).length := by
                        rw [List.take_succ_eq_append_getElem (by simp [hrevLen, hidx]),
                          List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
                      rw [← h1]
                      have h2 := List.take_append_drop (idx + 1) (r.1 :: revLayers).reverse
                      have h3 := congr_arg (fun ls => (ls.map List.length).sum) h2
                      simp only [List.map_append, List.sum_append] at h3
                      omega
                    have hr_le : r.2.1.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans hr_sub.2.1 hVX)
                    simp only [List.length_map] at hj
                    dsimp only [r] at hle_sum hsum_new hr_le ⊢
                    omega
                  have hne : cfg.layerDataAddr + ((((r.1 :: revLayers).reverse).take idx).map List.length).sum + j < cfgAddr + 16 ∨
                      cfgAddr + 21 ≤ cfg.layerDataAddr + ((((r.1 :: revLayers).reverse).take idx).map List.length).sum + j := by
                    rcases hd_ldc with h | h <;> omega
                  rw [hfr4 _ hne]; exact hst3_ld idx hidx j hj
                · intro u hu
                  have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                    rcases hd_vc with h | h <;> omega
                  rw [hfr4 _ hne]; exact hst3_vis u hu
                · intro u hu hm
                  have hne : cfg.distAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.distAddr + u := by
                    rcases hd_dc with h | h <;> omega
                  rw [hfr4 _ hne]; exact hst3_dist u hu hm
                · simp [h16, hrevLen]
                · rw [h17, hnewEnd_eq]
                · exact h18
                · exact h19
                · exact h20
                · intro u hu hnot
                  have hne : cfg.visStampAddr + u < cfgAddr + 16 ∨ cfgAddr + 21 ≤ cfg.visStampAddr + u := by
                    rcases hd_vc with h | h <;> omega
                  rw [hfr4 _ hne]; exact hst3_vis_out u hu hnot
                · intro a ha
                  have hne : a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a := by
                    by_contra hc; push Not at hc
                    exact ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
                  rw [hfr4 a hne]; exact hst3_fr a ha
              · simp only [bfsLoop, hnxt_empty', Bool.false_eq_true, ↓reduceIte, hhit', Expr.size] at hc1 hc2 hc4 ⊢
                dsimp only [r] at *
                omega
          · -- Did not hit stopSet: decrement rem and invoke IH!
            have hhit' : ((bfsExpandFrontier adj V (curDist + 1) frontier [] vis dist).1.any
                fun v => decide (v ∈ stopSet)) = false :=
              Bool.eq_false_iff.mpr hhit
            set st4 : State := { st3 with regs := Function.update st3.regs 14 rem }
            have hr3_14 : st3.regs 14 = rem + 1 := by simp [st3, regs3, hr2_14]
            have hdec_run : Runs w p ω
                (.cond (.reg 21)
                  (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                    (.const 1) (.const 0))
                  (.assign 14 (.bin .sub (.reg 14) (.const 1))))
                st3 .normal st4 ((Expr.reg 21).size + ((Expr.bin .sub (.reg 14) (.const 1)).size + 1) + 1) := by
              refine runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, hr3_21, hhit], ?_, rfl⟩
              simp only [↓reduceIte]
              refine runs_assign_iff.mpr ⟨rem, ?_, rfl, rfl, rfl⟩
              simp [Expr.eval, BinOp.eval, hr3_14, show 1 < 2 ^ w by omega, show rem < 2 ^ w by omega]
            have htrue_run : ∃ cT,
                Runs w p ω
                  (seqStmts
                    [ bfsRevCopyStmt
                    , .assign 18 (.reg 19)
                    , .assign 19 (.bin .add (.reg 19) (.reg 20))
                    , .assign 17 (.bin .add (.reg 17) (.const 1))
                    , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
                    , .cond (.reg 21)
                        (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                          (.const 1) (.const 0))
                        (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
                  st1 .normal st4 cT ∧ cT ≤ c2 + c3 + 16 := by
              rcases runs_seq_iff.mp hrun3 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
              · cases h
              rcases runs_seq_iff.mp hrb with ⟨_, _, _, h, _⟩ | ⟨sb, cb1, cb2, hrb1, hrb2, rfl⟩
              · cases h
              rcases runs_seq_iff.mp hrb2 with ⟨_, _, _, h, _⟩ | ⟨sc, cc1, cc2, hrc1, hrc2, rfl⟩
              · cases h
              refine ⟨c2 + (ca + (cb1 + (cc1 + (cc2 + ((Expr.reg 21).size + ((Expr.bin .sub (.reg 14) (.const 1)).size + 1) + 1) + 1) + 1) + 1) + 1) + 1, ?_, ?_⟩
              · dsimp only [seqStmts]
                exact runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
                  runs_seq_iff.mpr (Or.inr ⟨sa, ca, _, hra,
                    runs_seq_iff.mpr (Or.inr ⟨sb, cb1, _, hrb1,
                      runs_seq_iff.mpr (Or.inr ⟨sc, cc1, _, hrc1,
                        runs_seq_iff.mpr (Or.inr ⟨st3, cc2, _, hrc2, hdec_run, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
              · simp only [Expr.size]; omega
            rcases htrue_run with ⟨cT, hrunT, hcT⟩
            have hbody_run : Runs w p ω
                (seqStmts
                  [ bfsExpandStmt
                  , .cond (.reg 20)
                      (seqStmts
                        [ bfsRevCopyStmt
                        , .assign 18 (.reg 19)
                        , .assign 19 (.bin .add (.reg 19) (.reg 20))
                        , .assign 17 (.bin .add (.reg 17) (.const 1))
                        , .store (.bin .add (.reg 10) (.bin .add (.reg 17) (.const 1))) (.reg 19)
                        , .cond (.reg 21)
                            (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                              (.const 1) (.const 0))
                            (.assign 14 (.bin .sub (.reg 14) (.const 1))) ])
                      (bfsWriteRetStmt (.bin .add (.reg 17) (.const 1)) (.reg 19) (.reg 17)
                        (.const 0) (.const 1)) ])
                st0 .normal st4 (c1 + ((Expr.reg 20).size + cT + 1) + 1) := by
              dsimp only [seqStmts]
              refine runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, ?_, rfl⟩)
              refine runs_cond_iff.mpr ⟨r.1.length, cT, by simp [Expr.eval, hr1_20], ?_, rfl⟩
              simpa [Nat.ne_of_gt hnxt_pos] using hrunT
            have hst4_front : ListAt st4.mem (cfg.layerDataAddr + vis.card) (r.1.map (locOf X)) := by
              have h := hst3_ld (curDist + 1) (by omega)
              have htake_eq : (((r.1 :: revLayers).reverse).take (curDist + 1)).map List.length =
                  (revLayers.reverse).map List.length := by
                rw [hrev_app, List.take_append_of_le_length (by simp [hrevLen]),
                  List.take_of_length_le (by simp [hrevLen])]
              have hget_eq : ((r.1 :: revLayers).reverse)[curDist + 1]'(by simp [hrevLen]) = r.1 := by
                simp only [hrev_app]; rw [List.getElem_append_right (by simp [hrevLen])]; simp [hrevLen]
              simpa only [htake_eq, hsum_len, hget_eq, st4] using h
            have hst4_regs : ∀ r' ≤ 19, st4.regs r' =
                match r' with
                | 0 => cfgAddr | 1 => cfg.offAddr | 2 => cfg.nbAddr
                | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
                | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
                | 8 => cfg.visStampAddr | 9 => cfg.distAddr
                | 10 => cfg.layerOffAddr | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
                | 13 => cfg.bfsGen | 14 => rem
                | 17 => curDist + 1 | 18 => vis.card | 19 => r.2.1.card
                | r' => st4.regs r' := by
              intro r' hr'
              interval_cases r' <;> first
                | rfl
                | (simp [st4, st3, regs3, hnewEnd_eq]
                   try exact (hr2 _ (by decide)).trans ((hr1 _ (by decide)).trans (hregs _ (by decide))))
            have hih := ih (curDist + 1) vis.card r.1 (r.1 :: revLayers) r.2.1 r.2.2.1 st4
              (by omega) hr_sub.2.1
              (fun L hL => by
                rcases List.mem_cons.mp hL with rfl | hL
                · exact ⟨hnxt_pos, hr_sub.2.2⟩
                · exact ⟨(hrev_mem L hL).1, fun x hx => hr_sub.1 ((hrev_mem L hL).2 x hx)⟩)
              (by simp [hrevLen]) hr_sub.2.2 hnxt_pos (by omega) hsum_new
              hst3_lo hst3_ld hst4_front hst3_vis hst3_vis_out hst3_dist hst3_fr hst4_regs ω
            rcases hih with ⟨o5, st5, c5, hrun5, hpost5, hc5⟩
            have hloop_eq :
                bfsLoop adj V stopSet (rem + 1) curDist frontier revLayers vis dist 0 =
                  { bfsLoop adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1 0 with
                    cost := (bfsLoop adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1 0).cost +
                      (r.2.2.2 + 1 + r.1.length) } := by
              have hcost_add := bfsLoop_cost_add adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers)
                r.2.1 r.2.2.1 0 (r.2.2.2 + 1 + r.1.length)
              have hf := bfsLoop_fields_add adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers)
                r.2.1 r.2.2.1 0 (r.2.2.2 + 1 + r.1.length)
              simp only [bfsLoop, hnxt_empty', Bool.false_eq_true, ↓reduceIte, hhit']
              cases hA : bfsLoop adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1
                (0 + r.2.2.2 + 1 + r.1.length) with
              | mk lA vA dA mA hA' eA cA =>
              cases hB : bfsLoop adj V stopSet rem (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1 0 with
              | mk lB vB dB mB hB' eB cB =>
              simp only [Nat.zero_add] at hcost_add hf hA
              rw [hA, hB] at hf hcost_add
              dsimp only at hf hcost_add
              rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              simp only [hcost_add]
            refine ⟨o5, st5, _,
              runs_loop_iff.mpr (Or.inr (Or.inr ⟨rem + 1, st4, _, c5,
                by simp [Expr.eval, hr14_0], Nat.succ_ne_zero _, hbody_run, hrun5, rfl⟩)), ?_, ?_⟩
            · rw [hloop_eq]
              cases o5 with
              | returned v => exact hpost5
              | normal => exact hpost5
            · rw [hloop_eq]
              simp only [Expr.size] at hc1 hc2 hc5 ⊢
              dsimp only [r] at *
              omega

end MinCostFlow.ExpanderDecomp
