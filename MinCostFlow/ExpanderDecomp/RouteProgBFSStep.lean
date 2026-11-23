module

public import MinCostFlow.ExpanderDecomp.RouteProgBFSBase

import Mathlib.Tactic.Linarith

/-!
# Layered BFS Program: Reverse-Copy, Inner Scan, and Frontier-Expansion Stages

Verifies the three core inner stages of `bfsLayersProc`:
* `bfsWriteRet_triple`: storing the 5 output words at `cfgAddr + 16 .. cfgAddr + 20` and returning.
* `bfsRevCopy_triple`: reverse-copying `tmpNxt` into `layerData[layerEnd ..]` while checking `stopSet`.
* `bfsScanInner_triple`: scanning one vertex's CSR adjacency list against `bfsScanAdj`.
* `bfsExpand_triple`: expanding an entire frontier layer against `bfsExpandFrontier`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Output Write-and-Return Helper (`bfsWriteRetStmt`) -/

lemma bfsWriteRet_triple {w : ℕ} {p : Program}
    {cfgAddr vNumL vTotV vMaxR vHit vExh : ℕ} {eNumL eTotV eMaxR eHit eExh : Expr}
    {st0 : State}
    (hr0 : st0.regs 0 = cfgAddr)
    (hw_cfg : cfgAddr + 25 < 2 ^ w)
    (heNumL : eNumL.eval w st0 = some vNumL)
    (heTotV : eTotV.eval w st0 = some vTotV)
    (heMaxR : eMaxR.eval w st0 = some vMaxR)
    (heHit : eHit.eval w st0 = some vHit)
    (heExh : eExh.eval w st0 = some vExh)
    (hnomem : ∀ e ∈ [eNumL, eTotV, eMaxR, eHit, eExh],
      ∀ mem', e.eval w { st0 with mem := mem' } = e.eval w st0) :
    Triple w p (fun st => st = st0)
      (bfsWriteRetStmt eNumL eTotV eMaxR eHit eExh)
      (retPost fun v st' =>
        v = vTotV ∧
        st'.mem (cfgAddr + 16) = vNumL ∧
        st'.mem (cfgAddr + 17) = vTotV ∧
        st'.mem (cfgAddr + 18) = vMaxR ∧
        st'.mem (cfgAddr + 19) = vHit ∧
        st'.mem (cfgAddr + 20) = vExh ∧
        (∀ a, (a < cfgAddr + 16 ∨ cfgAddr + 21 ≤ a) → st'.mem a = st0.mem a))
      (fun _ => eNumL.size + 2 * eTotV.size + eMaxR.size + eHit.size + eExh.size + 32) := by
  wram_enter
  subst st
  unfold bfsWriteRetStmt
  dsimp only [seqStmts]
  have h1 : ∀ m, eNumL.eval w { st0 with mem := m } = some vNumL := fun m =>
    (hnomem eNumL (by simp) m).trans heNumL
  have h2 : ∀ m, eTotV.eval w { st0 with mem := m } = some vTotV := fun m =>
    (hnomem eTotV (by simp) m).trans heTotV
  have h3 : ∀ m, eMaxR.eval w { st0 with mem := m } = some vMaxR := fun m =>
    (hnomem eMaxR (by simp) m).trans heMaxR
  have h4 : ∀ m, eHit.eval w { st0 with mem := m } = some vHit := fun m =>
    (hnomem eHit (by simp) m).trans heHit
  have h5 : ∀ m, eExh.eval w { st0 with mem := m } = some vExh := fun m =>
    (hnomem eExh (by simp) m).trans heExh
  refine runs_seq_store_le (x := cfgAddr + 16) (v := vNumL) (by eval_expr) (h1 _) ?_
  refine runs_seq_store_le (x := cfgAddr + 17) (v := vTotV) (by eval_expr) (h2 _) ?_
  refine runs_seq_store_le (x := cfgAddr + 18) (v := vMaxR) (by eval_expr) (h3 _) ?_
  refine runs_seq_store_le (x := cfgAddr + 19) (v := vHit) (by eval_expr) (h4 _) ?_
  refine runs_seq_store_le (x := cfgAddr + 20) (v := vExh) (by eval_expr) (h5 _) ?_
  refine runs_ret_le (v := vTotV) (h2 _) ?_ ?_
  · dsimp only [retPost]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_self]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · simp only [Expr.size]
    omega

/-! ## 2. Reverse-Copy + Stop-Check Stage (`bfsRevCopyStmt`) -/

lemma bfsRevCopy_triple {w : ℕ} {p : Program}
    {X stopSet : Finset ℕ} {nxt : List ℕ} {cfg : BfsCfg} {cfgAddr m2 layerEnd : ℕ} {st0 : State}
    (hnxt_sub : ∀ x ∈ nxt, x ∈ X)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hlen_le : layerEnd + nxt.length ≤ X.card)
    (htmp : ListAt st0.mem cfg.tmpNxtAddr (nxt.reverse.map (locOf X)))
    (hstop : cfg.hasStop = 0 → stopSet = ∅)
    (hstop_mem : cfg.hasStop ≠ 0 →
      ∀ v < X.card, st0.mem (cfg.stopArrAddr + v) = cfg.stopVal ↔ origOf X v ∈ stopSet)
    (hregs0 : ∀ r ≤ 20, st0.regs r =
      match r with
      | 5 => cfg.hasStop | 6 => cfg.stopArrAddr | 7 => cfg.stopVal
      | 11 => cfg.layerDataAddr | 12 => cfg.tmpNxtAddr
      | 19 => layerEnd | 20 => nxt.length
      | r => st0.regs r) :
    Triple w p (fun st => st = st0) bfsRevCopyStmt
      (normalPost fun st' =>
        (∀ r ≤ 20, st'.regs r = st0.regs r) ∧
        st'.regs 21 = (if nxt.any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
        ListAt st'.mem (cfg.layerDataAddr + layerEnd) (nxt.map (locOf X)) ∧
        (∀ a, (a < cfg.layerDataAddr + layerEnd ∨ cfg.layerDataAddr + layerEnd + nxt.length ≤ a) →
          st'.mem a = st0.mem a))
      (fun _ => 55 * nxt.length + 18) := by
  rcases hdisj with ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
    hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
    hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
    hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
    hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  let I : State → Prop := fun st =>
    (∀ r ≤ 20, st.regs r = st0.regs r) ∧
    st.regs 22 ≤ nxt.length ∧
    st.regs 21 = (if (nxt.take (st.regs 22)).any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
    (∀ j < st.regs 22, st.mem (cfg.layerDataAddr + (layerEnd + j)) = locOf X (nxt.getD j 0)) ∧
    (∀ a, (a < cfg.layerDataAddr + layerEnd ∨ cfg.layerDataAddr + layerEnd + nxt.length ≤ a) →
      st.mem a = st0.mem a)
  have hloop :
      Triple w p I
        (.loop (.bin .lt (.reg 22) (.reg 20))
          (seqStmts
            [ .assign 26 (.load (.bin .add (.reg 12)
                (.bin .sub (.bin .sub (.reg 20) (.const 1)) (.reg 22))))
            , .store (.bin .add (.reg 11) (.bin .add (.reg 19) (.reg 22))) (.reg 26)
            , .cond (.reg 5)
                (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 26))) (.reg 7))
                  (.assign 21 (.const 1))
                  .nop)
                .nop
            , .assign 22 (.bin .add (.reg 22) (.const 1)) ]))
        (normalPost fun st' =>
          (∀ r ≤ 20, st'.regs r = st0.regs r) ∧
          st'.regs 21 = (if nxt.any (fun v => decide (v ∈ stopSet)) then 1 else 0) ∧
          ListAt st'.mem (cfg.layerDataAddr + layerEnd) (nxt.map (locOf X)) ∧
          (∀ a, (a < cfg.layerDataAddr + layerEnd ∨ cfg.layerDataAddr + layerEnd + nxt.length ≤ a) →
            st'.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 22) (.reg 20)).size + 46 + 1) * (nxt.length - st.regs 22) +
          (Expr.bin .lt (.reg 22) (.reg 20)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => nxt.length - st.regs 22)
      (condVal := fun st => if st.regs 22 < nxt.length then 1 else 0)
      (bodyBound := 46) ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _, _⟩
      have hr20 : stL.regs 20 = nxt.length := (hregs 20 (by decide)).trans (hregs0 20 (by decide))
      eval_expr
    · intro stL ⟨hregs, hq_le, hhit, hld, hfr⟩ hv
      have hq_eq : stL.regs 22 = nxt.length := by split_ifs at hv; omega
      rw [hq_eq, List.take_length] at hhit
      refine ⟨hregs, hhit, ?_, hfr⟩
      intro j hj
      simp only [List.length_map] at hj
      rw [Nat.add_assoc, hld j (by omega), List.getElem_map, List.getD_eq_getElem _ 0 hj]
    · intro stL ⟨hregs, hq_le, hhit, hld, hfr⟩ hv
      have hr5 : stL.regs 5 = cfg.hasStop := (hregs 5 (by decide)).trans (hregs0 5 (by decide))
      have hr6 : stL.regs 6 = cfg.stopArrAddr := (hregs 6 (by decide)).trans (hregs0 6 (by decide))
      have hr7 : stL.regs 7 = cfg.stopVal := (hregs 7 (by decide)).trans (hregs0 7 (by decide))
      have hr11 : stL.regs 11 = cfg.layerDataAddr := (hregs 11 (by decide)).trans (hregs0 11 (by decide))
      have hr12 : stL.regs 12 = cfg.tmpNxtAddr := (hregs 12 (by decide)).trans (hregs0 12 (by decide))
      have hr19 : stL.regs 19 = layerEnd := (hregs 19 (by decide)).trans (hregs0 19 (by decide))
      have hr20 : stL.regs 20 = nxt.length := (hregs 20 (by decide)).trans (hregs0 20 (by decide))
      have hq_lt : stL.regs 22 < nxt.length := by split_ifs at hv <;> omega
      set q := stL.regs 22
      set u := nxt[q]'hq_lt
      have hu_X : u ∈ X := hnxt_sub u (List.getElem_mem hq_lt)
      set wLoc := locOf X u
      have hwLoc_lt : wLoc < X.card := locOf_lt hu_X
      set revIdx := nxt.length - 1 - q
      have hrevIdx_lt : revIdx < nxt.length := by omega
      have htmp_disj : cfg.tmpNxtAddr + revIdx < cfg.layerDataAddr + layerEnd ∨
          cfg.layerDataAddr + layerEnd + nxt.length ≤ cfg.tmpNxtAddr + revIdx := by
        rcases hd_ldt with h | h <;> omega
      have hrev_val : stL.mem (cfg.tmpNxtAddr + revIdx) = wLoc := by
        rw [hfr _ htmp_disj]
        have h := htmp revIdx (by simp [hrevIdx_lt])
        rw [List.getElem_map, List.getElem_reverse] at h
        have hidx : nxt.length - 1 - revIdx = q := by omega
        simpa [u, wLoc, hidx] using h
      wram_enter
      subst st
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wLoc)
        (by
          have hsub : nxt.length - 1 - q = revIdx := rfl
          conv_rhs => rw [← hrev_val, ← hsub]
          eval_expr) ?_
      refine runs_seq_store_le (x := cfg.layerDataAddr + (layerEnd + q)) (v := wLoc)
        (by eval_expr) (by eval_expr) ?_
      set mem1 := Function.update stL.mem (cfg.layerDataAddr + (layerEnd + q)) wLoc
      have hmem1_ld : ∀ j < q + 1, mem1 (cfg.layerDataAddr + (layerEnd + j)) = locOf X (nxt.getD j 0) := by
        intro j hj
        by_cases hjq : j = q
        · subst hjq
          simp only [mem1, Function.update_self, List.getD_eq_getElem _ 0 hq_lt, u, wLoc]
        · dsimp only [mem1]
          rw [Function.update_of_ne (by omega)]
          exact hld j (by omega)
      have hmem1_fr : ∀ a,
          (a < cfg.layerDataAddr + layerEnd ∨ cfg.layerDataAddr + layerEnd + nxt.length ≤ a) →
          mem1 a = st0.mem a := by
        intro a ha
        dsimp only [mem1]
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      have hany_succ :
          (nxt.take (q + 1)).any (fun v => decide (v ∈ stopSet)) =
            ((nxt.take q).any (fun v => decide (v ∈ stopSet)) || decide (u ∈ stopSet)) := by
        rw [List.take_succ_eq_append_getElem hq_lt, List.any_append]
        simp [u]
      refine runs_seq_cond_le (v := cfg.hasStop) (by eval_expr)
        (fun hhs_ne => ?_) (fun hhs_zero => ?_)
      · have hstop_w_lt : cfg.stopArrAddr + wLoc < 2 ^ w := by have := hw_stop hhs_ne; omega
        have hstop_not_ws := hr_stop hhs_ne (cfg.stopArrAddr + wLoc) ⟨by omega, by omega⟩
        have hstop_out : cfg.stopArrAddr + wLoc < cfg.layerDataAddr + layerEnd ∨
            cfg.layerDataAddr + layerEnd + nxt.length ≤ cfg.stopArrAddr + wLoc := by
          by_contra h
          push Not at h
          exact hstop_not_ws (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
        have hstop_w_mem : mem1 (cfg.stopArrAddr + wLoc) = st0.mem (cfg.stopArrAddr + wLoc) :=
          hmem1_fr _ hstop_out
        have hu_stop_iff : st0.mem (cfg.stopArrAddr + wLoc) = cfg.stopVal ↔ u ∈ stopSet := by
          have := hstop_mem hhs_ne wLoc hwLoc_lt
          rwa [origOf_locOf hu_X] at this
        by_cases hu_stop : u ∈ stopSet
        · have heq_sv : mem1 (cfg.stopArrAddr + wLoc) = cfg.stopVal :=
            hstop_w_mem.trans (hu_stop_iff.mpr hu_stop)
          refine runs_seq_cond_le (v := 1)
            (by
              change Expr.eval w { mem := mem1, regs := Function.update stL.regs 26 wLoc, pos := stL.pos } _ = _
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (6 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (7 : ℕ) ≠ 26), Function.update_self,
                hr6, hr7, hstop_w_lt, ↓reduceIte, Option.map_some, heq_sv,
                show 1 < 2 ^ w by omega])
            (fun _ => ?_) (fun h0 => absurd h0 (by decide))
          refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
          refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost]
            refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_fr⟩, by simp; omega⟩
            · intro r hr_le
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hregs r hr_le
            · simp only [Function.update_self, Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
                hany_succ, decide_eq_true hu_stop, Bool.or_true, ↓reduceIte]
          · wram_cost
        · have hne_sv : mem1 (cfg.stopArrAddr + wLoc) ≠ cfg.stopVal := fun h =>
            hu_stop (hu_stop_iff.mp (hstop_w_mem.symm.trans h))
          refine runs_seq_cond_le (v := 0)
            (by
              change Expr.eval w { mem := mem1, regs := Function.update stL.regs 26 wLoc, pos := stL.pos } _ = _
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (6 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (7 : ℕ) ≠ 26), Function.update_self,
                hr6, hr7, hstop_w_lt, ↓reduceIte, Option.map_some, hne_sv,
                show 0 < 2 ^ w by omega])
            (fun h0 => absurd rfl h0) (fun _ => ?_)
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost]
            refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_fr⟩, by simp; omega⟩
            · intro r hr_le
              dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hregs r hr_le
            · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
                Function.update_of_ne (by decide : (21 : ℕ) ≠ 26), Function.update_self,
                hany_succ, decide_eq_false hu_stop, Bool.or_false, hhit]
          · wram_cost
      · refine runs_seq_nop_le ?_
        refine runs_assign_le (v := q + 1) (by eval_expr) ?_ ?_
        · dsimp only [normalPost]
          have hstop_empty : stopSet = ∅ := hstop hhs_zero
          refine ⟨⟨?_, by simp; omega, ?_, hmem1_ld, hmem1_fr⟩, by simp; omega⟩
          · intro r hr_le
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr_le
          · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 22),
              Function.update_of_ne (by decide : (21 : ℕ) ≠ 26), Function.update_self]
            rw [hany_succ]
            simp only [hstop_empty, Finset.notMem_empty, decide_false, Bool.or_false, hhit]
        · wram_cost
  wram_enter
  subst st
  unfold bfsRevCopyStmt
  dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set stInit : State := { st0 with regs := Function.update (Function.update st0.regs 21 0) 22 0 }
  have hinit : I stInit := by
    refine ⟨?_, by simp [stInit], by simp [stInit],
      fun j hj => by simp [stInit] at hj, fun _ _ => rfl⟩
    intro r hr_le
    simp only [stInit, Function.update_of_ne (by omega : r ≠ 22),
      Function.update_of_ne (by omega : r ≠ 21)]
  refine runs_triple_le hloop hinit (fun _ _ h => h) ?_
  have hsz : (Expr.bin .lt (.reg 22) (.reg 20)).size = 3 := rfl
  simp only [stInit, Function.update_self, Nat.sub_zero, hsz]
  wram_cost

/-! ## 3. Inner Neighbor Scan (`bfsScanInnerStmt`) -/

/-- Set of addresses writable by `bfsScanInnerStmt` / `bfsExpandStmt`: `visStamp`, `dist`, `tmpNxt`. -/
def BfsScanWriteSet (nX : ℕ) (cfg : BfsCfg) (a : ℕ) : Prop :=
  (cfg.visStampAddr ≤ a ∧ a < cfg.visStampAddr + nX) ∨
  (cfg.distAddr ≤ a ∧ a < cfg.distAddr + nX) ∨
  (cfg.tmpNxtAddr ≤ a ∧ a < cfg.tmpNxtAddr + nX)

lemma bfsScanWriteSet_sub {nX : ℕ} {cfg : BfsCfg} {cfgAddr a : ℕ}
    (h : BfsScanWriteSet nX cfg a) : BfsWriteSet nX cfg cfgAddr a := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

lemma bfsScanInner_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {uLoc curDist m2 cfgAddr : ℕ}
    {nxt0 : List ℕ} {vis0 : Finset ℕ} {dist0 : ℕ → Option ℕ}
    {cfg : BfsCfg} {st0 : State}
    (hu_lt : uLoc < X.card)
    (hVX : V ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hvis0_V : vis0 ⊆ V)
    (hnxt0_sub : ∀ x ∈ nxt0, x ∈ vis0)
    (hnxt0_le : nxt0.length ≤ vis0.card)
    (hdist_le : curDist + 1 ≤ X.card)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hvis_mem : ∀ v < X.card, st0.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ vis0)
    (hdist_mem : ∀ v < X.card, origOf X v ∈ vis0 →
      dist0 (origOf X v) = some (st0.mem (cfg.distAddr + v)))
    (htmp_mem : ListAt st0.mem cfg.tmpNxtAddr (nxt0.reverse.map (locOf X)))
    (hregs0 : ∀ r ≤ 25, st0.regs r =
      match r with
      | 2 => cfg.nbAddr | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
      | 8 => cfg.visStampAddr | 9 => cfg.distAddr | 12 => cfg.tmpNxtAddr
      | 13 => cfg.bfsGen | 17 => curDist | 20 => nxt0.length
      | 24 => adjCsrOff X adj uLoc
      | 25 => adjCsrOff X adj uLoc + (adj (origOf X uLoc)).length
      | r => st0.regs r) :
    let res := bfsScanAdj V (curDist + 1) (adj (origOf X uLoc)) nxt0 vis0 dist0
    Triple w p (fun st => st = st0) bfsScanInnerStmt
      (normalPost fun st' =>
        (∀ r ≤ 23, r ≠ 20 → st'.regs r = st0.regs r) ∧
        st'.regs 20 = res.1.length ∧
        (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.2.1) ∧
        (∀ v < X.card, origOf X v ∉ res.2.1 →
          st'.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
        (∀ v < X.card, origOf X v ∈ res.2.1 →
          res.2.2.1 (origOf X v) = some (st'.mem (cfg.distAddr + v))) ∧
        ListAt st'.mem cfg.tmpNxtAddr (res.1.reverse.map (locOf X)) ∧
        (∀ a, ¬ BfsScanWriteSet X.card cfg a → st'.mem a = st0.mem a))
      (fun _ => 65 * (adj (origOf X uLoc)).length + 5) := by
  set u := origOf X uLoc
  set l := adj u
  set eStart := adjCsrOff X adj uLoc
  set eEnd := eStart + l.length
  have heEnd_le : eEnd ≤ m2 := by
    have h1 : adjCsrOff X adj (uLoc + 1) = eEnd := by
      simp only [eEnd, eStart, l, u, adjCsrOff, Finset.sum_range_succ]
    have h2 := adjCsrOff_mono X adj (by omega : uLoc + 1 ≤ X.card)
    omega
  rcases hdisj with ⟨hd_vd, hd_vlo, hd_vld, hd_vt, hd_vc, hd_dlo, hd_dld, hd_dt, hd_dc,
    hd_lold, hd_lot, hd_loc, hd_ldt, hd_ldc, hd_tc,
    hr_cfg, hr_off, hr_nb, hr_mask, hr_stop, hr_init,
    hw_cfg, hw_off, hw_nb, hw_mask, hw_stop, hw_vis, hw_dist, hw_lo, hw_ld, hw_tmp, hw_init,
    hw_mb, hw_hs, hw_sv, hw_gen, hw_md, hw_m2, hw_nX, hw4⟩
  let I : State → Prop := fun st =>
    (∀ r ≤ 23, r ≠ 20 → st.regs r = st0.regs r) ∧
    st.regs 25 = eEnd ∧
    eStart ≤ st.regs 24 ∧ st.regs 24 ≤ eEnd ∧
    let rj := bfsScanAdj V (curDist + 1) (l.take (st.regs 24 - eStart)) nxt0 vis0 dist0
    st.regs 20 = rj.1.length ∧
    (∀ v < X.card, st.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ rj.2.1) ∧
    (∀ v < X.card, origOf X v ∉ rj.2.1 →
      st.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
    (∀ v < X.card, origOf X v ∈ rj.2.1 →
      rj.2.2.1 (origOf X v) = some (st.mem (cfg.distAddr + v))) ∧
    ListAt st.mem cfg.tmpNxtAddr (rj.1.reverse.map (locOf X)) ∧
    (∀ a, ¬ BfsScanWriteSet X.card cfg a → st.mem a = st0.mem a)
  have hloop :
      Triple w p I bfsScanInnerStmt
        (normalPost fun st' =>
          let res := bfsScanAdj V (curDist + 1) l nxt0 vis0 dist0
          (∀ r ≤ 23, r ≠ 20 → st'.regs r = st0.regs r) ∧
          st'.regs 20 = res.1.length ∧
          (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.2.1) ∧
          (∀ v < X.card, origOf X v ∉ res.2.1 →
            st'.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
          (∀ v < X.card, origOf X v ∈ res.2.1 →
            res.2.2.1 (origOf X v) = some (st'.mem (cfg.distAddr + v))) ∧
          ListAt st'.mem cfg.tmpNxtAddr (res.1.reverse.map (locOf X)) ∧
          (∀ a, ¬ BfsScanWriteSet X.card cfg a → st'.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 24) (.reg 25)).size + 60 + 1) * (eEnd - st.regs 24) +
          (Expr.bin .lt (.reg 24) (.reg 25)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => eEnd - st.regs 24)
      (condVal := fun st => if st.regs 24 < eEnd then 1 else 0)
      (bodyBound := 60) ?_ ?_ ?_
    · intro stL ⟨_, hr25, _, _, _, _, _, _, _, _⟩
      eval_expr
    · intro stL ⟨hregs, hr25, hge, hle, hr20, hvis, hvis_out, hdist, htmp, hfr⟩ hv
      have heq : stL.regs 24 = eEnd := by split_ifs at hv; omega
      have htake : l.take (stL.regs 24 - eStart) = l := by
        rw [show stL.regs 24 - eStart = l.length by omega, List.take_length]
      rw [htake] at hr20 hvis hvis_out hdist htmp
      exact ⟨hregs, hr20, hvis, hvis_out, hdist, htmp, hfr⟩
    · intro stL ⟨hregs, hr25, hge, hle, hr20, hvis, hvis_out, hdist, htmp, hfr⟩ hv
      have hr2 : stL.regs 2 = cfg.nbAddr := (hregs 2 (by decide) (by decide)).trans (hregs0 2 (by decide))
      have hr3 : stL.regs 3 = cfg.maskArrAddr := (hregs 3 (by decide) (by decide)).trans (hregs0 3 (by decide))
      have hr4 : stL.regs 4 = cfg.maskBadVal := (hregs 4 (by decide) (by decide)).trans (hregs0 4 (by decide))
      have hr8 : stL.regs 8 = cfg.visStampAddr := (hregs 8 (by decide) (by decide)).trans (hregs0 8 (by decide))
      have hr9 : stL.regs 9 = cfg.distAddr := (hregs 9 (by decide) (by decide)).trans (hregs0 9 (by decide))
      have hr12 : stL.regs 12 = cfg.tmpNxtAddr := (hregs 12 (by decide) (by decide)).trans (hregs0 12 (by decide))
      have hr13 : stL.regs 13 = cfg.bfsGen := (hregs 13 (by decide) (by decide)).trans (hregs0 13 (by decide))
      have hr17 : stL.regs 17 = curDist := (hregs 17 (by decide) (by decide)).trans (hregs0 17 (by decide))
      have hlt : stL.regs 24 < eEnd := by split_ifs at hv <;> omega
      set eCur := stL.regs 24
      set j := eCur - eStart
      have hj_lt : j < l.length := by omega
      set wVert := (l[j]'hj_lt).1
      have hwVert_X : wVert ∈ X := hadj_X u (origOf_mem hu_lt) _ (List.getElem_mem hj_lt)
      set wLoc := locOf X wVert
      have hwLoc_lt : wLoc < X.card := locOf_lt hwVert_X
      set rj := bfsScanAdj V (curDist + 1) (l.take j) nxt0 vis0 dist0
      change stL.regs 20 = rj.1.length at hr20
      change ∀ v < X.card, stL.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ rj.2.1 at hvis
      change ∀ v < X.card, origOf X v ∉ rj.2.1 →
        stL.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v) at hvis_out
      change ∀ v < X.card, origOf X v ∈ rj.2.1 →
        rj.2.2.1 (origOf X v) = some (stL.mem (cfg.distAddr + v)) at hdist
      change ListAt stL.mem cfg.tmpNxtAddr (rj.1.reverse.map (locOf X)) at htmp
      have hrj_sub := bfsScanAdj_subset_V V (curDist + 1) (l.take j) nxt0 vis0 dist0 hvis0_V hnxt0_sub
      have hrj_len : (rj.1.length - nxt0.length) + vis0.card = rj.2.1.card ∧ nxt0.length ≤ rj.1.length :=
        bfsScanAdj_length_le_card V (curDist + 1) (l.take j) nxt0 vis0 dist0
      have hrj_card_le : rj.2.1.card ≤ X.card :=
        Finset.card_le_card (Finset.Subset.trans hrj_sub.2.1 hVX)
      have hrj_len_le : rj.1.length ≤ rj.2.1.card := by omega
      have hsucc : bfsScanAdj V (curDist + 1) (l.take (j + 1)) nxt0 vis0 dist0 =
          if wVert ∈ V ∧ wVert ∉ rj.2.1 then
            (wVert :: rj.1, insert wVert rj.2.1, Function.update rj.2.2.1 wVert (some (curDist + 1)), rj.2.2.2 + 1)
          else
            (rj.1, rj.2.1, rj.2.2.1, rj.2.2.2 + 1) :=
        bfsScanAdj_take_succ V (curDist + 1) l hj_lt nxt0 vis0 dist0
      have hnb_mem : stL.mem (cfg.nbAddr + eCur) = wLoc := by
        rw [hfr _ (fun h => hr_nb _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))]
        have h := hcsr.2 uLoc hu_lt j hj_lt
        rw [show cfg.nbAddr + eCur = cfg.nbAddr + eStart + j by omega]
        exact h
      have hmask_mem : stL.mem (cfg.maskArrAddr + wLoc) = st0.mem (cfg.maskArrAddr + wLoc) :=
        hfr _ (fun h => hr_mask _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))
      have hwVert_V_iff : stL.mem (cfg.maskArrAddr + wLoc) ≠ cfg.maskBadVal ↔ wVert ∈ V := by
        rw [hmask_mem]; have := hmask wLoc hwLoc_lt; rwa [origOf_locOf hwVert_X] at this
      have hwVert_vis_iff : stL.mem (cfg.visStampAddr + wLoc) = cfg.bfsGen ↔ wVert ∈ rj.2.1 := by
        have := hvis wLoc hwLoc_lt; rwa [origOf_locOf hwVert_X] at this
      have hidx_succ : eCur + 1 - eStart = j + 1 := by omega
      wram_enter
      subst st
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := wLoc) (by rw [← hnb_mem]; eval_expr) ?_
      by_cases hwV : wVert ∈ V
      · have hmask_ne : stL.mem (cfg.maskArrAddr + wLoc) ≠ cfg.maskBadVal := hwVert_V_iff.mpr hwV
        refine runs_seq_cond_le (v := 0)
          (by
            simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (3 : ℕ) ≠ 26),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 26), Function.update_self,
              hr3, hr4, show cfg.maskArrAddr + wLoc < 2 ^ w by omega, ↓reduceIte,
              Option.map_some, hmask_ne, show 0 < 2 ^ w by omega])
          (fun h0 => absurd rfl h0) (fun _ => ?_)
        by_cases hwVis : wVert ∈ rj.2.1
        · have hvis_eq : stL.mem (cfg.visStampAddr + wLoc) = cfg.bfsGen := hwVert_vis_iff.mpr hwVis
          refine runs_seq_cond_le (v := 1)
            (by
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (8 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (13 : ℕ) ≠ 26), Function.update_self,
                hr8, hr13, show cfg.visStampAddr + wLoc < 2 ^ w by omega, ↓reduceIte,
                Option.map_some, hvis_eq, show 1 < 2 ^ w by omega])
            (fun _ => ?_) (fun h0 => absurd h0 (by decide))
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := eCur + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost, I]
            have hcond_f : ¬ (wVert ∈ V ∧ wVert ∉ rj.2.1) := fun h => h.2 hwVis
            simp only [Function.update_self, hidx_succ, hsucc, hcond_f, ↓reduceIte]
            refine ⟨⟨?_, by simp [hr25], by omega, by omega,
              by simp [hr20], hvis, hvis_out, hdist, htmp, hfr⟩, by omega⟩
            intro r hr_le hr_ne
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr_le hr_ne
          · wram_cost
        · have hvis_ne : stL.mem (cfg.visStampAddr + wLoc) ≠ cfg.bfsGen := fun h =>
            hwVis (hwVert_vis_iff.mp h)
          have hcond_t : wVert ∈ V ∧ wVert ∉ rj.2.1 := ⟨hwV, hwVis⟩
          have hrj_len_lt_nX : rj.1.length < X.card := by
            have h1 : insert wVert rj.2.1 ⊆ V := Finset.insert_subset hwV hrj_sub.2.1
            have h2 : (insert wVert rj.2.1).card ≤ X.card :=
              Finset.card_le_card (Finset.Subset.trans h1 hVX)
            rw [Finset.card_insert_of_notMem hwVis] at h2
            omega
          refine runs_seq_cond_le (v := 0)
            (by
              simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (8 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (13 : ℕ) ≠ 26), Function.update_self,
                hr8, hr13, show cfg.visStampAddr + wLoc < 2 ^ w by omega, ↓reduceIte,
                Option.map_some, hvis_ne, show 0 < 2 ^ w by omega])
            (fun h0 => absurd rfl h0) (fun _ => ?_)
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_le (x := cfg.visStampAddr + wLoc) (v := cfg.bfsGen)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_le (x := cfg.distAddr + wLoc) (v := curDist + 1)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assoc_le ?_
          refine runs_seq_store_le (x := cfg.tmpNxtAddr + rj.1.length) (v := wLoc)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := rj.1.length + 1) (by eval_expr) ?_
          refine runs_assign_le (v := eCur + 1) (by eval_expr) ?_ ?_
          · dsimp only [normalPost, I]
            simp only [Function.update_self, hidx_succ, hsucc, hcond_t, not_false_eq_true,
              and_self, ↓reduceIte]
            refine ⟨⟨?_, by simp [hr25], by omega, by omega,
              by rw [Function.update_of_ne (by decide), Function.update_self]; simp,
              ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
            · intro r hr_le hr_ne
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hregs r hr_le hr_ne
            · intro v hv'
              have h1 : cfg.visStampAddr + v ≠ cfg.tmpNxtAddr + rj.1.length :=
                disjRange_ne hd_vt hv' hrj_len_lt_nX
              have h2 : cfg.visStampAddr + v ≠ cfg.distAddr + wLoc :=
                disjRange_ne hd_vd hv' hwLoc_lt
              rw [Function.update_of_ne h1, Function.update_of_ne h2]
              by_cases hvw : v = wLoc
              · subst hvw
                rw [Function.update_self, origOf_locOf hwVert_X]
                exact iff_of_true rfl (Finset.mem_insert_self _ _)
              · have hne_w : origOf X v ≠ wVert := fun h => hvw (by rw [← locOf_origOf hv', h])
                rw [Function.update_of_ne (by omega), hvis v hv', Finset.mem_insert]
                exact ⟨Or.inr, fun h => h.resolve_left hne_w⟩
            · intro v hv' hnot
              have h1 : cfg.visStampAddr + v ≠ cfg.tmpNxtAddr + rj.1.length :=
                disjRange_ne hd_vt hv' hrj_len_lt_nX
              have h2 : cfg.visStampAddr + v ≠ cfg.distAddr + wLoc :=
                disjRange_ne hd_vd hv' hwLoc_lt
              have hne_w : origOf X v ≠ wVert := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
              have hvw : v ≠ wLoc := fun h => hne_w (by rw [h, origOf_locOf hwVert_X])
              rw [Function.update_of_ne h1, Function.update_of_ne h2,
                Function.update_of_ne (by omega)]
              exact hvis_out v hv' (fun hm => hnot (Finset.mem_insert_of_mem hm))
            · intro v hv' hmem
              have h1 : cfg.distAddr + v ≠ cfg.tmpNxtAddr + rj.1.length :=
                disjRange_ne hd_dt hv' hrj_len_lt_nX
              rw [Function.update_of_ne h1]
              by_cases hvw : v = wLoc
              · subst hvw
                rw [Function.update_self, origOf_locOf hwVert_X, Function.update_self]
              · have hne_w : origOf X v ≠ wVert := fun h => hvw (by rw [← locOf_origOf hv', h])
                have h2 : cfg.distAddr + v ≠ cfg.visStampAddr + wLoc :=
                  (disjRange_ne hd_vd hwLoc_lt hv').symm
                rw [Function.update_of_ne hne_w,
                  Function.update_of_ne (by omega : cfg.distAddr + v ≠ cfg.distAddr + wLoc),
                  Function.update_of_ne h2]
                exact hdist v hv' ((Finset.mem_insert.mp hmem).resolve_left hne_w)
            · intro idx hidx
              simp only [List.reverse_cons, List.map_append, List.map_singleton,
                List.length_append, List.length_map, List.length_reverse,
                List.length_singleton] at hidx ⊢
              by_cases hlast : idx = rj.1.length
              · subst hlast
                rw [Function.update_self, List.getElem_append_right (by simp)]
                simp [wLoc]
              · have hidx_old : idx < (rj.1.reverse.map (locOf X)).length := by simp; omega
                have h1 : cfg.tmpNxtAddr + idx ≠ cfg.distAddr + wLoc :=
                  (disjRange_ne hd_dt hwLoc_lt (by omega : idx < X.card)).symm
                have h2 : cfg.tmpNxtAddr + idx ≠ cfg.visStampAddr + wLoc :=
                  (disjRange_ne hd_vt hwLoc_lt (by omega : idx < X.card)).symm
                rw [Function.update_of_ne (by omega), Function.update_of_ne h1,
                  Function.update_of_ne h2, List.getElem_append_left hidx_old]
                exact htmp idx hidx_old
            · intro a ha
              have h1 : a ≠ cfg.tmpNxtAddr + rj.1.length := fun h =>
                ha (Or.inr (Or.inr (by omega)))
              have h2 : a ≠ cfg.distAddr + wLoc := fun h => ha (Or.inr (Or.inl (by omega)))
              have h3 : a ≠ cfg.visStampAddr + wLoc := fun h => ha (Or.inl (by omega))
              rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
              exact hfr a ha
          · wram_cost
      · have hmask_eq : stL.mem (cfg.maskArrAddr + wLoc) = cfg.maskBadVal := by
          by_contra hne; exact hwV (hwVert_V_iff.mp hne)
        refine runs_seq_cond_le (v := 1)
          (by
            simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (3 : ℕ) ≠ 26),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 26), Function.update_self,
              hr3, hr4, show cfg.maskArrAddr + wLoc < 2 ^ w by omega, ↓reduceIte,
              Option.map_some, hmask_eq, show 1 < 2 ^ w by omega])
          (fun _ => ?_) (fun h0 => absurd h0 (by decide))
        refine runs_seq_nop_le ?_
        refine runs_assign_le (v := eCur + 1) (by eval_expr) ?_ ?_
        · dsimp only [normalPost, I]
          have hcond_f : ¬ (wVert ∈ V ∧ wVert ∉ rj.2.1) := fun h => hwV h.1
          simp only [Function.update_self, hidx_succ, hsucc, hcond_f, ↓reduceIte]
          refine ⟨⟨?_, by simp [hr25], by omega, by omega,
            by simp [hr20], hvis, hvis_out, hdist, htmp, hfr⟩, by omega⟩
          intro r hr_le hr_ne
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hregs r hr_le hr_ne
        · wram_cost
  dsimp only
  wram_enter
  subst st
  have hinit : I st0 := by
    have hr24 : st0.regs 24 = eStart := hregs0 24 (by decide)
    have hr25 : st0.regs 25 = eEnd := hregs0 25 (by decide)
    have hr20 : st0.regs 20 = nxt0.length := hregs0 20 (by decide)
    refine ⟨fun _ _ _ => rfl, hr25, by omega, by omega, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · simp [hr24, bfsScanAdj, hr20]
    · simp only [hr24, Nat.sub_self, List.take_zero, bfsScanAdj]; exact hvis_mem
    · simp [hr24, bfsScanAdj]
    · simp only [hr24, Nat.sub_self, List.take_zero, bfsScanAdj]; exact hdist_mem
    · simp only [hr24, Nat.sub_self, List.take_zero, bfsScanAdj]; exact htmp_mem
  refine runs_triple_le hloop hinit (fun _ _ h => h) ?_
  have hr24 : st0.regs 24 = eStart := hregs0 24 (by decide)
  have hsz : (Expr.bin .lt (.reg 24) (.reg 25)).size = 3 := rfl
  rw [hr24, hsz]
  dsimp only [eEnd]
  omega

/-! ## 4. Frontier Expansion Stage (`bfsExpandStmt`) -/

lemma bfsScanAdj_cost_eq (V : Finset ℕ) (nextDist : ℕ) (l : List (ℕ × ℕ))
    (nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    (bfsScanAdj V nextDist l nxt vis dist).2.2.2 = l.length := by
  induction l generalizing nxt vis dist with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [bfsScanAdj, List.length_cons]
    split_ifs <;> simp [ih]

lemma bfsExpandFrontier_cost_eq (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (nextDist : ℕ)
    (frontier nxt : List ℕ) (vis : Finset ℕ) (dist : ℕ → Option ℕ) :
    (bfsExpandFrontier adj V nextDist frontier nxt vis dist).2.2.2 =
      frontier.length + (frontier.map fun u => (adj u).length).sum := by
  induction frontier generalizing nxt vis dist with
  | nil => rfl
  | cons u rest ih =>
    simp only [bfsExpandFrontier, List.length_cons, List.map_cons, List.sum_cons,
      bfsScanAdj_cost_eq, ih]
    omega

lemma bfsExpand_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {frontier : List ℕ}
    {vis0 : Finset ℕ} {dist0 : ℕ → Option ℕ}
    {cfg : BfsCfg} {cfgAddr m2 curDist layerStart : ℕ} {st0 : State}
    (hVX : V ⊆ X)
    (hadj_X : ∀ u ∈ X, ∀ e ∈ adj u, e.1 ∈ X)
    (hvis0_V : vis0 ⊆ V)
    (hfront_sub : ∀ u ∈ frontier, u ∈ X)
    (hfront_le : layerStart + frontier.length ≤ X.card)
    (hdist_le : curDist + 1 ≤ X.card)
    (hcsr : NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hdisj : BfsDisj w X.card m2 cfg cfgAddr)
    (hmask : ∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V)
    (hvis_mem : ∀ v < X.card, st0.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ vis0)
    (hdist_mem : ∀ v < X.card, origOf X v ∈ vis0 →
      dist0 (origOf X v) = some (st0.mem (cfg.distAddr + v)))
    (hfront_mem : ListAt st0.mem (cfg.layerDataAddr + layerStart) (frontier.map (locOf X)))
    (hregs0 : ∀ r ≤ 19, st0.regs r =
      match r with
      | 1 => cfg.offAddr | 2 => cfg.nbAddr | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
      | 8 => cfg.visStampAddr | 9 => cfg.distAddr | 11 => cfg.layerDataAddr
      | 12 => cfg.tmpNxtAddr | 13 => cfg.bfsGen | 17 => curDist
      | 18 => layerStart | 19 => layerStart + frontier.length
      | r => st0.regs r) :
    let res := bfsExpandFrontier adj V (curDist + 1) frontier [] vis0 dist0
    Triple w p (fun st => st = st0) bfsExpandStmt
      (normalPost fun st' =>
        (∀ r ≤ 19, st'.regs r = st0.regs r) ∧
        st'.regs 20 = res.1.length ∧
        (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.2.1) ∧
        (∀ v < X.card, origOf X v ∉ res.2.1 →
          st'.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
        (∀ v < X.card, origOf X v ∈ res.2.1 →
          res.2.2.1 (origOf X v) = some (st'.mem (cfg.distAddr + v))) ∧
        ListAt st'.mem cfg.tmpNxtAddr (res.1.reverse.map (locOf X)) ∧
        (∀ a, ¬ BfsScanWriteSet X.card cfg a → st'.mem a = st0.mem a))
      (fun _ => 70 * (bfsExpandFrontier adj V (curDist + 1) frontier [] vis0 dist0).2.2.2 + 20) := by
  set layerEnd := layerStart + frontier.length
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
  let remCost : ℕ → ℕ := fun q =>
    (frontier.drop q).length + ((frontier.drop q).map fun u => (adj u).length).sum
  have hrem_zero : remCost 0 =
      (bfsExpandFrontier adj V (curDist + 1) frontier [] vis0 dist0).2.2.2 := by
    simp [remCost, bfsExpandFrontier_cost_eq]
  have hrem_succ : ∀ q (hq : q < frontier.length),
      remCost q = 1 + (adj (frontier[q]'hq)).length + remCost (q + 1) := by
    intro q hq
    simp only [remCost]
    rw [List.drop_eq_getElem_cons hq, List.length_cons, List.map_cons, List.sum_cons]
    omega
  let I : State → Prop := fun st =>
    (∀ r ≤ 19, st.regs r = st0.regs r) ∧
    layerStart ≤ st.regs 22 ∧ st.regs 22 ≤ layerEnd ∧
    let rq := bfsExpandFrontier adj V (curDist + 1) (frontier.take (st.regs 22 - layerStart)) [] vis0 dist0
    st.regs 20 = rq.1.length ∧
    (∀ v < X.card, st.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ rq.2.1) ∧
    (∀ v < X.card, origOf X v ∉ rq.2.1 →
      st.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
    (∀ v < X.card, origOf X v ∈ rq.2.1 →
      rq.2.2.1 (origOf X v) = some (st.mem (cfg.distAddr + v))) ∧
    ListAt st.mem cfg.tmpNxtAddr (rq.1.reverse.map (locOf X)) ∧
    (∀ a, ¬ BfsScanWriteSet X.card cfg a → st.mem a = st0.mem a)
  have hloop :
      Triple w p I
        (.loop (.bin .lt (.reg 22) (.reg 19))
          (seqStmts
            [ .assign 23 (.load (.bin .add (.reg 11) (.reg 22)))
            , .assign 24 (.load (.bin .add (.reg 1) (.reg 23)))
            , .assign 25 (.load (.bin .add (.bin .add (.reg 1) (.reg 23)) (.const 1)))
            , bfsScanInnerStmt
            , .assign 22 (.bin .add (.reg 22) (.const 1)) ]))
        (normalPost fun st' =>
          let res := bfsExpandFrontier adj V (curDist + 1) frontier [] vis0 dist0
          (∀ r ≤ 19, st'.regs r = st0.regs r) ∧
          st'.regs 20 = res.1.length ∧
          (∀ v < X.card, st'.mem (cfg.visStampAddr + v) = cfg.bfsGen ↔ origOf X v ∈ res.2.1) ∧
          (∀ v < X.card, origOf X v ∉ res.2.1 →
            st'.mem (cfg.visStampAddr + v) = st0.mem (cfg.visStampAddr + v)) ∧
          (∀ v < X.card, origOf X v ∈ res.2.1 →
            res.2.2.1 (origOf X v) = some (st'.mem (cfg.distAddr + v))) ∧
          ListAt st'.mem cfg.tmpNxtAddr (res.1.reverse.map (locOf X)) ∧
          (∀ a, ¬ BfsScanWriteSet X.card cfg a → st'.mem a = st0.mem a))
        (fun st => 70 * remCost (st.regs 22 - layerStart) + 10) := by
    refine Triple.loop_measure
      (m := fun st => layerEnd - st.regs 22)
      (rem := fun st => 70 * remCost (st.regs 22 - layerStart) + 10)
      (condVal := fun st => if st.regs 22 < layerEnd then 1 else 0)
      ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _, _, _, _, _, _⟩
      have hr19 : stL.regs 19 = layerEnd := (hregs 19 (by decide)).trans (hregs0 19 (by decide))
      eval_expr
    · intro stL ⟨hregs, hge, hle, hr20, hvis, hvis_out, hdist, htmp, hfr⟩ hv
      have heq : stL.regs 22 = layerEnd := by split_ifs at hv; omega
      have htake : frontier.take (stL.regs 22 - layerStart) = frontier := by
        rw [show stL.regs 22 - layerStart = frontier.length by omega, List.take_length]
      rw [htake] at hr20 hvis hvis_out hdist htmp
      have hsz : (Expr.bin .lt (.reg 22) (.reg 19)).size = 3 := rfl
      exact ⟨⟨hregs, hr20, hvis, hvis_out, hdist, htmp, hfr⟩, by rw [hsz]; omega⟩
    · intro stL ⟨hregs, hge, hle, hr20, hvis, hvis_out, hdist, htmp, hfr⟩ hv
      have hr : ∀ r ≤ 19, stL.regs r = _ := fun r hr => (hregs r hr).trans (hregs0 r hr)
      have hr1 : stL.regs 1 = cfg.offAddr := hr 1 (by decide)
      have hr2 : stL.regs 2 = cfg.nbAddr := hr 2 (by decide)
      have hr3 : stL.regs 3 = cfg.maskArrAddr := hr 3 (by decide)
      have hr4 : stL.regs 4 = cfg.maskBadVal := hr 4 (by decide)
      have hr8 : stL.regs 8 = cfg.visStampAddr := hr 8 (by decide)
      have hr9 : stL.regs 9 = cfg.distAddr := hr 9 (by decide)
      have hr11 : stL.regs 11 = cfg.layerDataAddr := hr 11 (by decide)
      have hr12 : stL.regs 12 = cfg.tmpNxtAddr := hr 12 (by decide)
      have hr13 : stL.regs 13 = cfg.bfsGen := hr 13 (by decide)
      have hr17 : stL.regs 17 = curDist := hr 17 (by decide)
      have hr19 : stL.regs 19 = layerEnd := hr 19 (by decide)
      have hlt : stL.regs 22 < layerEnd := by split_ifs at hv <;> omega
      set qIdx := stL.regs 22
      set q := qIdx - layerStart
      have hq_lt : q < frontier.length := by omega
      set u := frontier[q]'hq_lt
      have hu_X : u ∈ X := hfront_sub u (List.getElem_mem hq_lt)
      set uLoc := locOf X u
      have huLoc_lt : uLoc < X.card := locOf_lt hu_X
      have horig_u : origOf X uLoc = u := origOf_locOf hu_X
      set rq := bfsExpandFrontier adj V (curDist + 1) (frontier.take q) [] vis0 dist0
      have hrq_sub := bfsExpandFrontier_subset_V adj V (curDist + 1) (frontier.take q) [] vis0 dist0
        hvis0_V (fun _ h => by cases h)
      have hrq_len : (rq.1.length - ([] : List ℕ).length) + vis0.card = rq.2.1.card ∧
          ([] : List ℕ).length ≤ rq.1.length :=
        bfsExpandFrontier_length_card adj V (curDist + 1) (frontier.take q) [] vis0 dist0
      have hrq_len_le : rq.1.length ≤ rq.2.1.card := by simp only [List.length_nil, Nat.sub_zero] at hrq_len; omega
      have hsucc := bfsExpandFrontier_take_succ adj V (curDist + 1) frontier hq_lt [] vis0 dist0
      have hu_not_scan : ¬ BfsScanWriteSet X.card cfg (cfg.layerDataAddr + qIdx) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases hd_vld with h | h <;> omega
        · rcases hd_dld with h | h <;> omega
        · rcases hd_ldt with h | h <;> omega
      have hmem_u : stL.mem (cfg.layerDataAddr + qIdx) = uLoc := by
        rw [hfr _ hu_not_scan, show cfg.layerDataAddr + qIdx = cfg.layerDataAddr + layerStart + q by omega]
        have h := hfront_mem q (by simp [hq_lt])
        simpa [u, uLoc] using h
      have hmem_eStart : stL.mem (cfg.offAddr + uLoc) = adjCsrOff X adj uLoc := by
        rw [hfr _ (fun h => hr_off _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))]
        exact hcsr.1 uLoc (le_of_lt huLoc_lt)
      have hmem_eEnd : stL.mem (cfg.offAddr + uLoc + 1) = adjCsrOff X adj uLoc + (adj u).length := by
        rw [show cfg.offAddr + uLoc + 1 = cfg.offAddr + (uLoc + 1) by omega,
          hfr _ (fun h => hr_off _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h)),
          hcsr.1 (uLoc + 1) huLoc_lt]
        simp only [adjCsrOff, Finset.sum_range_succ, horig_u]
      have hcsrL : NbCsrAt stL.mem cfg.offAddr cfg.nbAddr X adj := by
        refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
        · rw [hfr _ (fun h => hr_off _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))]; exact hcsr.1 i hi
        · have hbound : adjCsrOff X adj i + j < m2 := by
            have h1 : adjCsrOff X adj (i + 1) = adjCsrOff X adj i + (adj (origOf X i)).length := by
              simp [adjCsrOff, Finset.sum_range_succ]
            have h2 := adjCsrOff_mono X adj (by omega : i + 1 ≤ X.card)
            omega
          rw [hfr _ (fun h => hr_nb _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))]; exact hcsr.2 i hi j hj
      have hmaskL : ∀ v < X.card, stL.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V := by
        intro v hv'
        rw [hfr _ (fun h => hr_mask _ ⟨by omega, by omega⟩ (bfsScanWriteSet_sub h))]
        exact hmask v hv'
      refine ⟨65 * (adj u).length + 45, ?_⟩
      wram_enter
      subst st
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := uLoc) (by rw [← hmem_u]; eval_expr) ?_
      refine runs_seq_assign_le (v := adjCsrOff X adj uLoc)
        (by rw [← hmem_eStart]; eval_expr) ?_
      refine runs_seq_assign_le (v := adjCsrOff X adj uLoc + (adj u).length)
        (by rw [← hmem_eEnd]; eval_expr) ?_
      set stS0 : State :=
        { stL with regs := Function.update (Function.update (Function.update stL.regs 23 uLoc)
            24 (adjCsrOff X adj uLoc)) 25 (adjCsrOff X adj uLoc + (adj u).length) }
      have hregsS0 : ∀ r ≤ 25, stS0.regs r =
          match r with
          | 2 => cfg.nbAddr | 3 => cfg.maskArrAddr | 4 => cfg.maskBadVal
          | 8 => cfg.visStampAddr | 9 => cfg.distAddr | 12 => cfg.tmpNxtAddr
          | 13 => cfg.bfsGen | 17 => curDist | 20 => rq.1.length
          | 24 => adjCsrOff X adj uLoc
          | 25 => adjCsrOff X adj uLoc + (adj (origOf X uLoc)).length
          | r => stS0.regs r := by
        intro r hr_le
        dsimp only [stS0]
        interval_cases r <;> simp [hr2, hr3, hr4, hr8, hr9, hr12, hr13, hr17, hr20, horig_u]
      refine runs_seq_triple_le
        (bfsScanInner_triple (uLoc := uLoc) (curDist := curDist) (nxt0 := rq.1)
          (vis0 := rq.2.1) (dist0 := rq.2.2.1) (st0 := stS0)
          huLoc_lt hVX hadj_X hrq_sub.2.1 hrq_sub.2.2 hrq_len_le hdist_le
          hcsrL hm2 hdisj' hmaskL hvis hdist htmp hregsS0)
        rfl (fun st1 hst1 => ?_)
      rcases hst1 with ⟨hr1', hr1_20, hvis1, hvis1_out, hdist1, htmp1, hfr1⟩
      have hr1_22 : st1.regs 22 = qIdx := by
        rw [hr1' 22 (by decide) (by decide)]
        simp [stS0, qIdx]
      refine runs_assign_le (v := qIdx + 1) (by eval_expr) ?_ ?_
      · have hidx_succ : qIdx + 1 - layerStart = q + 1 := by omega
        have hsucc' : bfsExpandFrontier adj V (curDist + 1) (frontier.take (q + 1)) [] vis0 dist0 =
            (let s := bfsScanAdj V (curDist + 1) (adj (origOf X uLoc)) rq.1 rq.2.1 rq.2.2.1
             (s.1, s.2.1, s.2.2.1, rq.2.2.2 + s.2.2.2 + 1)) := by
          simpa only [horig_u, rq, u] using hsucc
        refine ⟨⟨?_, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp; omega, ?_⟩
        · intro r hr_le
          dsimp only
          rw [Function.update_of_ne (by omega), hr1' r (by omega) (by omega)]
          simp only [stS0, Function.update_of_ne (by omega : r ≠ 25),
            Function.update_of_ne (by omega : r ≠ 24),
            Function.update_of_ne (by omega : r ≠ 23)]
          exact hregs r hr_le
        · simp only [Function.update_of_ne (by decide : (20 : ℕ) ≠ 22), Function.update_self,
            hidx_succ, hsucc', hr1_20]
        · intro v hv'
          simp only [Function.update_self, hidx_succ, hsucc']
          exact hvis1 v hv'
        · intro v hv' hnot
          simp only [Function.update_self, hidx_succ, hsucc'] at hnot ⊢
          have hsub_s := (bfsScanAdj_subset_V V (curDist + 1) (adj (origOf X uLoc)) rq.1 rq.2.1 rq.2.2.1
            hrq_sub.2.1 hrq_sub.2.2).1
          rw [hvis1_out v hv' hnot]
          exact hvis_out v hv' (fun hm => hnot (hsub_s hm))
        · intro v hv' hmem
          simp only [Function.update_self, hidx_succ, hsucc'] at hmem ⊢
          exact hdist1 v hv' hmem
        · simp only [Function.update_self, hidx_succ, hsucc']
          exact htmp1
        · intro a ha
          rw [hfr1 a ha]
          exact hfr a ha
        · have hsz : (Expr.bin .lt (.reg 22) (.reg 19)).size = 3 := rfl
          have hrc := hrem_succ q hq_lt
          simp only [Function.update_self, hidx_succ, hsz]
          dsimp only [u] at *
          omega
      · rw [horig_u]; wram_cost
  dsimp only
  wram_enter
  subst st
  unfold bfsExpandStmt
  dsimp only [seqStmts]
  have hr18_0 : st0.regs 18 = layerStart := hregs0 18 (by decide)
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := layerStart) (by eval_expr) ?_
  set stInit : State :=
    { st0 with regs := Function.update (Function.update st0.regs 20 0) 22 layerStart }
  have hinit : I stInit := by
    refine ⟨?_, by simp [stInit], by simp [stInit]; omega, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
    · intro r hr_le
      simp only [stInit, Function.update_of_ne (by omega : r ≠ 22),
        Function.update_of_ne (by omega : r ≠ 20)]
    · simp [stInit, bfsExpandFrontier]
    · simp only [stInit, Function.update_self, Nat.sub_self, List.take_zero, bfsExpandFrontier]
      exact hvis_mem
    · simp [stInit, bfsExpandFrontier]
    · simp only [stInit, Function.update_self, Nat.sub_self, List.take_zero, bfsExpandFrontier]
      exact hdist_mem
    · intro idx hidx; simp [stInit, bfsExpandFrontier] at hidx
  refine runs_triple_le hloop hinit (fun _ _ h => h) ?_
  simp only [stInit, Function.update_self, Nat.sub_self, hrem_zero]
  wram_cost

end MinCostFlow.ExpanderDecomp

