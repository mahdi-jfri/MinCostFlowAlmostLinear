module

public import MinCostFlow.SparseCore.Program.OrdStoreUnlink
public import MinCostFlow.SparseCore.Program.OrdStoreMoveScan
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Passes 5–6: Unlinking into a Left Spine and Zeroing Scratch

This file implements and verifies Passes 5 and 6 of `ordMoveEndsBody`:
* Pass 5 (`ordMoveUnlinkLoop`): iterates `i = 0 .. out - 1` over the sorted selected node IDs
  `selNodes` in `scratch[0 .. 2*out - 1]`, unlinks each node `u` from `v`'s tree via `ordUnlink`,
  and links `u` onto the left-leaning spine `leftSpine (selNodes.take (i + 1))`.
* Pass 6 (`ordMoveZeroLoop`): zeros `scratch[0 .. 2*cnt - 1]`, restoring `ZeroFrom mem scratch`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Helper lemmas on `leftSpine` and `List.erase` -/

theorem leftSpineGo_append_singleton (acc : AuxTree) (xs : List ℕ) (u : ℕ) :
    leftSpine.leftSpineGo acc (xs ++ [u]) = .node u (leftSpine.leftSpineGo acc xs) .leaf := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a tl ih => simp [leftSpine.leftSpineGo, ih]

theorem leftSpine_append_singleton (xs : List ℕ) (u : ℕ) :
    leftSpine (xs ++ [u]) = .node u (leftSpine xs) .leaf := by
  cases xs with
  | nil => rfl
  | cons a tl => exact leftSpineGo_append_singleton (.node a .leaf .leaf) tl u

private theorem filter_not_mem_append_singleton {L xs : List ℕ} {u : ℕ} (hnd : L.Nodup) :
    (L.filter (fun z => decide (z ∉ xs))).erase u =
      L.filter (fun z => decide (z ∉ xs ++ [u])) := by
  have hnd' : (L.filter (fun z => decide (z ∉ xs))).Nodup := hnd.filter _
  have h1 : ∀ {l : List ℕ}, l.Nodup → l.erase u = l.filter (· != u) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a tl ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, htl⟩
      by_cases h : a = u
      · subst h
        simp only [List.erase_cons_head, List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact (List.filter_eq_self.mpr fun b hb => bne_iff_ne.mpr (fun hba => ha (by rw [← hba]; exact hb))).symm
      · simp only [List.erase_cons, beq_eq_false_iff_ne.mpr h, List.filter_cons, bne_iff_ne.mpr h, ↓reduceIte]
        exact congrArg (a :: ·) (ih htl)
  rw [h1 hnd', List.filter_filter]
  apply List.filter_congr
  intro z _
  apply Bool.eq_iff_iff.mpr
  simp [List.mem_append, List.mem_singleton, not_or, and_comm]

/-! ### Pass 5: `ordMoveUnlinkLoop` -/

/-- Pass 5 of `moveEnds`: unlinks each of the `out` sorted nodes of vertex `v` from `v`'s tree
and links them into a left-leaning spine rooted at register `13`. -/
def ordMoveUnlinkLoop (unlinkProc : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 12))
    (.assign 14 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1))) ;;
     .call 15 unlinkProc [.reg 0, .reg 14] ;;
     .assign 16 (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 14))) ;;
     .store (.reg 16) (.reg 13) ;;
     .store (.bin .add (.reg 16) (.const 4)) (.bin .add (.reg 10) (.const 1)) ;;
     .cond (.reg 13)
       (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 14))
       .nop ;;
     .assign 13 (.reg 14) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

theorem ordMoveUnlinkLoop_noRand (uP : ℕ) : (ordMoveUnlinkLoop uP).NoRand := by
  simp [ordMoveUnlinkLoop, Stmt.NoRand]

theorem ordMoveUnlinkLoop_runs
    {w b v scratch rotProc stepProc splayProc walkProc joinProc unlinkProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hunlink : p.procs[unlinkProc]? = some (ordUnlinkBody splayProc joinProc)) (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {selNodes : List ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S st0.mem) (hv : v < S.vCap)
    (hnd_sel : selNodes.Nodup) (hsub_sel : ∀ u ∈ selNodes, u ∈ (S.trees v).toList)
    (hscr : ∀ i < selNodes.length, st0.mem (scratch + 2 * i + 1) = selNodes.getD i 0)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch + 2 * selNodes.length < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = b) (hr6 : st0.regs 6 = scratch)
    (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr10 : st0.regs 10 = 0) (hr12 : st0.regs 12 = selNodes.length) (hr13 : st0.regs 13 = 0) :
    ∃ st' c, ∃ sp' : SplayState ℕ Unit Unit, ∃ tRem : AuxTree,
      Runs w p ω (ordMoveUnlinkLoop unlinkProc) st0 .normal st' c ∧
      (∀ r, r ≠ 10 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st0.regs r) ∧
      st'.regs 13 = (leftSpine selNodes).rootId ∧
      OrdNodesAt st'.mem (ordNodesBase b S.vCap S.eCap) S.nextNode sp' S.nextFree ∧
      st'.mem (ordVRootBase b + v) = tRem.rootId ∧
      (∀ a, ¬ InOrdNodes (ordNodesBase b S.vCap S.eCap) S.nextNode a →
            a ≠ ordVRootBase b + v → st'.mem a = st0.mem a) ∧
      OrdTreeOk S.nextNode sp' tRem ∧
      (tRem ≠ .leaf → (sp'.nodes tRem.rootId).ppar = v + 1) ∧
      tRem.toList = (S.trees v).toList.filter (fun z => decide (z ∉ selNodes)) ∧
      OrdTreeOk S.nextNode sp' (leftSpine selNodes) ∧
      (leftSpine selNodes ≠ .leaf → (sp'.nodes (leftSpine selNodes).rootId).ppar = 0) ∧
      (∀ x ∉ (S.trees v).toList, sp'.nodes x = S.splay.nodes x) ∧
      (∀ x ∈ (S.trees v).toList, (sp'.nodes x).val = (S.splay.nodes x).val) ∧
      c + ORD_PHI_WEIGHT * tRem.treePhi (fun _ => 0) ≤
        ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) +
          (ORD_UNLINK_AMORT + 120) * selNodes.length * ordStoreLog S.eCap + 30 := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ scratch := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb]; omega
  have hnb_w : nb + 8 * (S.nextNode + 1) < 2 ^ w := by omega
  have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S.nextNode a := fun a ha h => by unfold InOrdNodes at h; omega
  have hloop : ∀ rem (i : ℕ) (st : State) (sp : SplayState ℕ Unit Unit) (tRem : AuxTree),
      i + rem = selNodes.length →
      st.regs 0 = b → st.regs 6 = scratch → st.regs 9 = nb →
      st.regs 10 = i → st.regs 12 = selNodes.length →
      st.regs 13 = (leftSpine (selNodes.take i)).rootId →
      OrdNodesAt st.mem nb S.nextNode sp S.nextFree →
      st.mem (ordVRootBase b + v) = tRem.rootId →
      (∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ ordVRootBase b + v → st.mem a = st0.mem a) →
      OrdTreeOk S.nextNode sp tRem →
      (tRem ≠ .leaf → (sp.nodes tRem.rootId).ppar = v + 1) →
      tRem.toList = (S.trees v).toList.filter (fun z => decide (z ∉ selNodes.take i)) →
      OrdTreeOk S.nextNode sp (leftSpine (selNodes.take i)) →
      (leftSpine (selNodes.take i) ≠ .leaf → (sp.nodes (leftSpine (selNodes.take i)).rootId).ppar = 0) →
      (∀ x ∉ (S.trees v).toList, sp.nodes x = S.splay.nodes x) →
      (∀ x ∈ (S.trees v).toList, (sp.nodes x).val = (S.splay.nodes x).val) →
      ∃ st' c, ∃ sp' : SplayState ℕ Unit Unit, ∃ tRem' : AuxTree,
        Runs w p ω (ordMoveUnlinkLoop unlinkProc) st .normal st' c ∧
        (∀ r, r ≠ 10 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → st'.regs r = st.regs r) ∧
        st'.regs 13 = (leftSpine selNodes).rootId ∧
        OrdNodesAt st'.mem nb S.nextNode sp' S.nextFree ∧
        st'.mem (ordVRootBase b + v) = tRem'.rootId ∧
        (∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ ordVRootBase b + v → st'.mem a = st0.mem a) ∧
        OrdTreeOk S.nextNode sp' tRem' ∧
        (tRem' ≠ .leaf → (sp'.nodes tRem'.rootId).ppar = v + 1) ∧
        tRem'.toList = (S.trees v).toList.filter (fun z => decide (z ∉ selNodes)) ∧
        OrdTreeOk S.nextNode sp' (leftSpine selNodes) ∧
        (leftSpine selNodes ≠ .leaf → (sp'.nodes (leftSpine selNodes).rootId).ppar = 0) ∧
        (∀ x ∉ (S.trees v).toList, sp'.nodes x = S.splay.nodes x) ∧
        (∀ x ∈ (S.trees v).toList, (sp'.nodes x).val = (S.splay.nodes x).val) ∧
        c + ORD_PHI_WEIGHT * tRem'.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * tRem.treePhi (fun _ => 0) +
            (ORD_UNLINK_AMORT + 120) * rem * ordStoreLog S.eCap + 30 := by
    intro rem
    induction rem with
    | zero =>
      intro i st sp tRem hi r0 r6 r9 r10 r12 r13 hn hvr hfr hokR hppR hlistR hokS hppS houtS hvalS
      have hi_eq : i = selNodes.length := by omega
      subst hi_eq
      have hcond : (Expr.bin .lt (.reg 10) (.reg 12)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r12) (by omega) (by omega)
      rw [List.take_length] at r13 hlistR hokS hppS
      refine ⟨st, _, sp, tRem, ord_runs_loop_false hcond, fun _ _ _ _ _ _ => rfl, r13,
        hn, hvr, hfr, hokR, hppR, hlistR, hokS, hppS, houtS, hvalS, by simp [Expr.size_bin, Expr.size_reg]; omega⟩
    | succ rem ih =>
      intro i st sp tRem hi r0 r6 r9 r10 r12 r13 hn hvr hfr hokR hppR hlistR hokS hppS houtS hvalS
      have hi_lt : i < selNodes.length := by omega
      have hcond : (Expr.bin .lt (.reg 10) (.reg 12)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r12) hi_lt (by omega)
      set u := selNodes.getD i 0 with hu_def
      have hu_eq : selNodes[i]'hi_lt = u := by simp [hu_def, List.getD_eq_getElem?_getD, hi_lt]
      have hu_mem_sel : u ∈ selNodes := hu_eq ▸ List.getElem_mem hi_lt
      have hu_mem_tv : u ∈ (S.trees v).toList := hsub_sel u hu_mem_sel
      have hu_ntake : u ∉ selNodes.take i := by
        intro hm
        have hsp := List.take_append_drop i selNodes
        rw [List.drop_eq_getElem_cons hi_lt, hu_eq] at hsp
        have hnd' := hnd_sel; rw [← hsp, List.nodup_append] at hnd'
        exact hnd'.2.2 u hm u List.mem_cons_self rfl
      have htake_succ : selNodes.take (i + 1) = selNodes.take i ++ [u] := by
        rw [List.take_succ_eq_append_getElem hi_lt, hu_eq]
      have hu_mem_rem : u ∈ tRem.toList := by
        rw [hlistR, List.mem_filter]; exact ⟨hu_mem_tv, decide_eq_true hu_ntake⟩
      have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero hokR.inv.sub hu_mem_rem
      have hu_le : u ≤ S.nextNode := hokR.mem_le u hu_mem_rem
      have hm_scr_i : st.mem (scratch + 2 * i + 1) = u := by
        rw [hfr _ (fun h => by unfold InOrdNodes at h; omega) (by unfold ordVRootBase; omega)]
        exact hscr i hi_lt
      have ha14 : Runs w p ω
          (.assign 14 (.load (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)))) st .normal
          { st with regs := Function.update st.regs 14 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_load_of_eq (by
          have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)).eval w st =
              some (scratch + (i + i) + 1) :=
            Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r6)
              (Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r10) (by omega)) (by omega))
              (Expr.eval_const (by omega)) (by omega)
          rwa [show scratch + (i + i) + 1 = scratch + 2 * i + 1 by omega] at he) hm_scr_i, rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 14 u }
      have hst_hdr2 : st.mem (b + 2) = ordVRootBase b :=
        (hfr (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega)) (by unfold ordVRootBase; omega)).trans harena.hdr_vRoot
      have hst_hdr4 : st.mem (b + 4) = nb :=
        (hfr (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega)) (by unfold ordVRootBase; omega)).trans harena.hdr_nodes
      have hpp_rem : (sp.nodes tRem.rootId).ppar = v + 1 :=
        hppR (by intro h; rw [h] at hu_mem_rem; exact List.not_mem_nil hu_mem_rem)
      obtain ⟨oU, stU, cU, hrunU, spU, tRem1, hoU, hnU, hvrU, hfrU, hokR1, hlistU, hcntU, hppU,
        hu_iso, hvalU, houtU, hphiU⟩ :=
        ordUnlinkBody_runs hrot hstep hsplay hwalk hjoin ω hst_hdr2 hst_hdr4 hn hokR hv hu_mem_rem
          hpp_rem hinv.next_le (by omega) hwide (pos := st1.pos)
      have hcallU : Runs w p ω (.call 15 unlinkProc [.reg 0, .reg 14]) st1 .normal
          { stU with regs := Function.update st1.regs 15 oU.value } (argsSize [.reg 0, .reg 14] + cU + 1) :=
        runs_call_iff.mpr ⟨[b, u], ordUnlinkBody splayProc joinProc, oU, stU, cU,
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1, r0]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st1])) (evalArgs_nil _ _)),
          hunlink, hrunU, rfl, rfl, rfl⟩
      set st2 : State := { stU with regs := Function.update st1.regs 15 oU.value }
      set tSel : AuxTree := leftSpine (selNodes.take i)
      have htSel_disj_rem : ∀ x ∈ tSel.toList, x ∉ tRem.toList := fun x hx hxr => by
        rw [leftSpine_toList] at hx; rw [hlistR, List.mem_filter] at hxr
        exact (of_decide_eq_true hxr.2) hx
      have htSel_le : tSel.rootId ≤ S.nextNode := by
        cases hts : tSel with
        | leaf => simp [AuxTree.rootId]
        | node sid sl sr => exact hokS.mem_le sid (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp))
      have hu_ne_tSel : u ≠ tSel.rootId := by
        cases hts : tSel with
        | leaf => simp [AuxTree.rootId]; exact hu_nz
        | node sid sl sr =>
          intro h; simp only [AuxTree.rootId] at h
          exact htSel_disj_rem sid (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)) (h ▸ hu_mem_rem)
      have hu_ntRem1 : u ∉ tRem1.toList := by
        rw [hlistU, hlistR, filter_not_mem_append_singleton (hinv.tree_inv v hv).nodup, List.mem_filter]
        intro h; exact (of_decide_eq_true h.2) (by simp)
      have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 14)))) st2 .normal
          { st2 with regs := Function.update st2.regs 16 (nb + 8 * u) } _ :=
        runs_assign_iff.mpr ⟨nb + 8 * u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, r9]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2, st1])) (by omega)) (by omega),
          rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 16 (nb + 8 * u) }
      have hs1 : Runs w p ω (.store (.reg 16) (.reg 13)) st3 .normal
          { st3 with mem := Function.update stU.mem (nb + 8 * u) tSel.rootId } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u, tSel.rootId, Expr.eval_reg_of_eq (by simp [st3]),
          Expr.eval_reg_of_eq (by simp [st3, st2, st1, r13]), rfl, rfl, rfl⟩
      set m1 := Function.update stU.mem (nb + 8 * u) tSel.rootId
      set st4 : State := { st3 with mem := m1 }
      have hs2 : Runs w p ω (.store (.bin .add (.reg 16) (.const 4)) (.bin .add (.reg 10) (.const 1))) st4 .normal
          { st4 with mem := Function.update m1 (nb + 8 * u + 4) (i + 1) } _ :=
        runs_store_iff.mpr ⟨nb + 8 * u + 4, i + 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3])) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, r10])) (Expr.eval_const (by omega)) (by omega),
          rfl, rfl, rfl⟩
      set m2 := Function.update m1 (nb + 8 * u + 4) (i + 1)
      set st5 : State := { st4 with mem := m2 }
      obtain ⟨spA, hspA⟩ : ∃ s, s = (spU.setLeft u tSel.rootId).updateNode u fun nd => { nd with sz := i + 1 } := ⟨_, rfl⟩
      have hnA : OrdNodesAt m2 nb S.nextNode spA S.nextFree := by
        rw [hspA]
        have h1 : OrdNodesAt m1 nb S.nextNode (spU.setLeft u tSel.rootId) S.nextFree := by
          simpa [ordNodeAddr] using hnU.setLeft hu_le (v := tSel.rootId)
        exact h1.setSz hu_le
      obtain ⟨sp1, hsp1⟩ : ∃ s, s = (if tSel.rootId = 0 then spA else spA.setPar tSel.rootId u) := ⟨_, rfl⟩
      have hcondS : ∃ m3 cS,
          Runs w p ω (.cond (.reg 13)
            (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 14)) .nop)
            st5 .normal { st5 with mem := m3 } cS ∧
          OrdNodesAt m3 nb S.nextNode sp1 S.nextFree ∧
          (∀ a, ¬ InOrdNodes nb S.nextNode a → m3 a = m2 a) ∧ cS ≤ 30 := by
        by_cases hS0 : tSel.rootId = 0
        · have hc : (Expr.reg 13).eval w st5 = some 0 := Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r13, hS0])
          refine ⟨m2, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
            by rw [hsp1]; simpa [hS0] using hnA, fun _ _ => rfl, by simp [Expr.size_reg]⟩
        · have hc : (Expr.reg 13).eval w st5 = some tSel.rootId := Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r13])
          have hst : Runs w p ω
              (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 2)) (.reg 14))
              st5 .normal { st5 with mem := Function.update m2 (nb + 8 * tSel.rootId + 2) u } _ :=
            runs_store_iff.mpr ⟨nb + 8 * tSel.rootId + 2, u,
              Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r9]))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, r13])) (by omega)) (by omega))
                (Expr.eval_const (by omega)) (by omega),
              Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1]), rfl, rfl, rfl⟩
          refine ⟨_, _, ord_runs_cond_true hc hS0 hst,
            by rw [hsp1]; simp only [hS0, ite_false]; exact hnA.setPar htSel_le (v := u),
            fun a ha => Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _,
            by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
      obtain ⟨m3, cS, hrunS, hn1, hfrS, hcS⟩ := hcondS
      set st6 : State := { st5 with mem := m3 }
      have ha13 : Runs w p ω (.assign 13 (.reg 14)) st6 .normal
          { st6 with regs := Function.update st6.regs 13 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, st1]), rfl, rfl, rfl⟩
      set st7 : State := { st6 with regs := Function.update st6.regs 13 u }
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st7 .normal
          { st7 with regs := Function.update st7.regs 10 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2, st1, r10]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st8 : State := { st7 with regs := Function.update st7.regs 10 (i + 1) }
      -- Verify sp1 preserves tRem1 and builds leftSpine (selNodes.take (i + 1)) = .node u tSel .leaf
      have hsp1_out : ∀ x, x ≠ u → x ≠ tSel.rootId → sp1.nodes x = spU.nodes x := fun x h1 h2 => by
        rw [hsp1, hspA]
        split_ifs <;> simp [SplayState.setPar, SplayState.setLeft, SplayState.nodes_updateNode, h1, h2]
      have hsp1_u : sp1.nodes u = { (spU.nodes u) with left := tSel.rootId, sz := i + 1 } := by
        rw [hsp1, hspA]
        split_ifs <;> simp [SplayState.setPar, SplayState.setLeft, SplayState.nodes_updateNode, hu_ne_tSel]
      have hsp1_tSel : tSel.rootId ≠ 0 → sp1.nodes tSel.rootId = { (sp.nodes tSel.rootId) with par := u } := fun hS0 => by
        rw [hsp1, hspA]
        have hmem_s : tSel.rootId ∈ tSel.toList := by
          cases hts : tSel with
          | leaf => simp [hts, AuxTree.rootId] at hS0
          | node sid sl sr => exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)
        have hnot_rem : tSel.rootId ∉ tRem.toList := htSel_disj_rem _ hmem_s
        simp [hS0, SplayState.setPar, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hu_ne_tSel, houtU _ hnot_rem]
      have h0_sp1 : sp1.nodes 0 = ordNullNode := by
        by_cases hS0 : tSel.rootId = 0
        · rw [hsp1, hspA]; simp [hS0, SplayState.setLeft, SplayState.nodes_updateNode, Ne.symm hu_nz, hokR1.null_node]
        · rw [hsp1_out 0 (Ne.symm hu_nz) (Ne.symm hS0)]; exact hokR1.null_node
      have hcl_sp1 : ∀ x, (sp1.nodes x).rev = false := fun x => by
        by_cases h1 : x = u
        · rw [h1, hsp1_u]; exact hokR1.clean u
        · by_cases h2 : x = tSel.rootId
          · by_cases hS0 : tSel.rootId = 0
            · rw [h2, hS0, h0_sp1]; rfl
            · rw [h2, hsp1_tSel hS0]; exact hokS.clean tSel.rootId
          · rw [hsp1_out x h1 h2]; exact hokR1.clean x
      have htRem1_list : tRem1.toList = (S.trees v).toList.filter (fun z => decide (z ∉ selNodes.take (i + 1))) := by
        rw [hlistU, hlistR, htake_succ]; exact filter_not_mem_append_singleton (hinv.tree_inv v hv).nodup
      have hokR1' : OrdTreeOk S.nextNode sp1 tRem1 :=
        { null_node := h0_sp1
          clean := hcl_sp1
          inv := ⟨hokR1.inv.nodup, SplayState.SubtreeInv_agree hokR1.inv.sub fun x hx =>
            (hsp1_out x (fun h => hu_ntRem1 (by rw [← h]; exact hx)) (fun h => by
              cases hts : tSel with
              | leaf => rw [hts, AuxTree.rootId] at h; exact SplayState.SubtreeInv_nonZero hokR1.inv.sub hx h
              | node sid sl sr =>
                rw [hts, AuxTree.rootId] at h
                have hms : sid ∈ tSel.toList := by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)
                have hmr : sid ∈ tRem.toList := by
                  rw [hlistU] at hx; rw [← h]; exact List.mem_of_mem_erase hx
                exact htSel_disj_rem sid hms hmr)).symm⟩
          mem_le := hokR1.mem_le
          count_le := hokR1.count_le }
      have hppR1' : tRem1 ≠ .leaf → (sp1.nodes tRem1.rootId).ppar = v + 1 := fun hne => by
        have hr := AuxTree.rootId_mem hne
        rw [hsp1_out _ (fun h => hu_ntRem1 (by rw [← h]; exact hr)) (fun h => by
          cases hts : tSel with
          | leaf => rw [hts, AuxTree.rootId] at h; exact SplayState.SubtreeInv_nonZero hokR1.inv.sub hr h
          | node sid sl sr =>
            rw [hts, AuxTree.rootId] at h
            exact htSel_disj_rem sid (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp))
              (by rw [hlistU] at hr; rw [← h]; exact List.mem_of_mem_erase hr))]
        exact hppU hne
      have htSel1_eq : leftSpine (selNodes.take (i + 1)) = .node u tSel .leaf := by
        rw [htake_succ, leftSpine_append_singleton]
      have hsub_tSel' : SplayState.SubtreeInv ordPayload sp1 u tSel := by
        cases hts : tSel with
        | leaf => trivial
        | node sid sl sr =>
          have hsub_s := hts ▸ hokS.inv.sub
          rcases hsub_s with ⟨hsid_nz, hsl, hsr, -, -, hssz, -, hsub_sl, hsub_sr⟩
          rcases AuxTree.nodup_node_unfold (hts ▸ hokS.inv.nodup) with ⟨_, hsid_nsl, _, hsid_nsr, _⟩
          have hnd_s := hsp1_tSel (by rw [hts, AuxTree.rootId]; exact hsid_nz)
          simp only [hts, AuxTree.rootId] at hnd_s
          refine ⟨hsid_nz, by rw [hnd_s]; exact hsl, by rw [hnd_s]; exact hsr,
            by rw [hnd_s], fun _ => by
              rw [hnd_s]
              have hpp_ts := hppS (by rw [hts]; simp)
              simpa [hts, AuxTree.rootId] using hpp_ts,
            by rw [hnd_s]; exact hssz, rfl,
            SplayState.SubtreeInv_agree hsub_sl fun x hx => by
              have hms : x ∈ tSel.toList := by rw [hts]; exact List.mem_append_left _ (List.mem_append_left _ hx)
              have hx_nrem : x ∉ tRem.toList := htSel_disj_rem x hms
              have hx_nu : x ≠ u := fun h => hx_nrem (by rw [h]; exact hu_mem_rem)
              have hx_nsid : x ≠ tSel.rootId := by simp only [hts, AuxTree.rootId]; exact fun h => hsid_nsl (by rw [← h]; exact hx)
              exact ((hsp1_out x hx_nu hx_nsid).trans (houtU x hx_nrem)).symm,
            SplayState.SubtreeInv_agree hsub_sr fun x hx => by
              have hms : x ∈ tSel.toList := by rw [hts]; exact List.mem_append_right _ hx
              have hx_nrem : x ∉ tRem.toList := htSel_disj_rem x hms
              have hx_nu : x ≠ u := fun h => hx_nrem (by rw [h]; exact hu_mem_rem)
              have hx_nsid : x ≠ tSel.rootId := by simp only [hts, AuxTree.rootId]; exact fun h => hsid_nsr (by rw [← h]; exact hx)
              exact ((hsp1_out x hx_nu hx_nsid).trans (houtU x hx_nrem)).symm⟩
      have hokS1 : OrdTreeOk S.nextNode sp1 (leftSpine (selNodes.take (i + 1))) := by
        rw [htSel1_eq]
        refine
          { null_node := h0_sp1
            clean := hcl_sp1
            inv := ⟨by
              rw [← htSel1_eq, leftSpine_toList]
              exact hnd_sel.take,
              ⟨hu_nz, by rw [hsp1_u], by simp [hsp1_u, hu_iso, AuxTree.rootId], by simp [hsp1_u, hu_iso],
               fun h => absurd rfl h,
               by simp [hsp1_u, AuxTree.countNodes, tSel, leftSpine_countNodes, List.length_take, Nat.min_eq_left (by omega : i ≤ selNodes.length)]; omega,
               rfl, hsub_tSel', trivial⟩⟩
            mem_le := fun x hx => by
              rw [← htSel1_eq, leftSpine_toList] at hx
              exact (hinv.live_le_nextNode hv (hsub_sel x (List.mem_of_mem_take hx))).2
            count_le := by
              rw [← htSel1_eq, leftSpine_countNodes, List.length_take, Nat.min_eq_left (by omega : i + 1 ≤ selNodes.length)]
              have hsub : selNodes.toFinset ⊆ (S.trees v).toList.toFinset := fun x hx => by
                rw [List.mem_toFinset] at hx ⊢; exact hsub_sel x hx
              have hcard := Finset.card_le_card hsub
              rw [List.toFinset_card_of_nodup hnd_sel, List.toFinset_card_of_nodup (hinv.tree_inv v hv).nodup,
                AuxTree.length_toList] at hcard
              have := (hinv.ordTreeOk hv).count_le; omega }
      have hm3_out : ∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ ordVRootBase b + v → m3 a = st0.mem a := fun a h1 h2 => by
        rw [hfrS a h1]; dsimp only [m2, m1]
        rw [Function.update_of_ne (fun h => h1 ⟨by omega, by omega⟩),
            Function.update_of_ne (fun h => h1 ⟨by omega, by omega⟩),
            hfrU a h1 h2, hfr a h1 h2]
      have hm3_vr : m3 (ordVRootBase b + v) = tRem1.rootId := by
        have hnot_vr : ¬ InOrdNodes nb S.nextNode (ordVRootBase b + v) :=
          hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)
        rw [hfrS _ hnot_vr]; dsimp only [m2, m1]
        rw [Function.update_of_ne (by unfold ordVRootBase; rw [hnb]; unfold ordNodesBase; omega),
            Function.update_of_ne (by unfold ordVRootBase; rw [hnb]; unfold ordNodesBase; omega), hvrU]
      have houtS1 : ∀ x ∉ (S.trees v).toList, sp1.nodes x = S.splay.nodes x := fun x hx => by
        by_cases hx0 : x = 0
        · rw [hx0, h0_sp1, hinv.null_node]
        · have hx_nu : x ≠ u := fun h => hx (h ▸ hu_mem_tv)
          have hx_ntSel : x ≠ tSel.rootId := by
            cases hts : tSel with
            | leaf => simp [AuxTree.rootId]; exact hx0
            | node sid sl sr =>
              intro h; simp only [AuxTree.rootId] at h
              have hms : sid ∈ selNodes.take i := by
                rw [← leftSpine_toList (selNodes.take i)]
                change sid ∈ tSel.toList; rw [hts]
                exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)
              exact hx (h ▸ hsub_sel sid (List.mem_of_mem_take hms))
          have hx_nrem : x ∉ tRem.toList := fun hm => hx (by rw [hlistR, List.mem_filter] at hm; exact hm.1)
          rw [hsp1_out x hx_nu hx_ntSel, houtU x hx_nrem, houtS x hx]
      have hppS1 : leftSpine (selNodes.take (i + 1)) ≠ .leaf →
          (sp1.nodes (leftSpine (selNodes.take (i + 1))).rootId).ppar = 0 := fun _ => by
        rw [htSel1_eq, AuxTree.rootId, hsp1_u, hu_iso]
      have hvalS1 : ∀ x ∈ (S.trees v).toList, (sp1.nodes x).val = (S.splay.nodes x).val := fun x hx => by
        by_cases h1 : x = u
        · rw [h1, hsp1_u, hu_iso]; exact hvalS u hu_mem_tv
        · by_cases h2 : x = tSel.rootId
          · by_cases hS0 : tSel.rootId = 0
            · exfalso; rw [h2, hS0] at hx; exact SplayState.SubtreeInv_nonZero (hinv.tree_inv v hv).sub hx rfl
            · rw [h2, hsp1_tSel hS0]; exact hvalS tSel.rootId (h2 ▸ hx)
          · rw [hsp1_out x h1 h2]
            by_cases hxr : x ∈ tRem1.toList
            · exact (hvalU x hxr).trans (hvalS x hx)
            · have hnr : x ∉ tRem.toList := fun hm => hxr (by
                rw [hlistU, hlistR, filter_not_mem_append_singleton (hinv.tree_inv v hv).nodup, List.mem_filter]
                rw [hlistR, List.mem_filter] at hm
                exact ⟨hm.1, decide_eq_true (by simp [List.mem_append, List.mem_singleton, h1, of_decide_eq_true hm.2])⟩)
              rw [houtU x hnr]; exact hvalS x hx
      obtain ⟨stF, cF, spF, tRemF, hrunF, hregF, r13F, hnF, hvrF, hfrF, hokRF, hppRF, hlistRF, hokSF, hppSF, houtSF, hvalSF, hphiF⟩ :=
        ih (i + 1) st8 sp1 tRem1 (by omega)
          (by simp [st8, st7, st6, st5, st4, st3, st2, st1, r0])
          (by simp [st8, st7, st6, st5, st4, st3, st2, st1, r6])
          (by simp [st8, st7, st6, st5, st4, st3, st2, st1, r9])
          (by simp [st8])
          (by simp [st8, st7, st6, st5, st4, st3, st2, st1, r12])
          (by simp [st8, st7, htSel1_eq, AuxTree.rootId])
          hn1 hm3_vr hm3_out hokR1' hppR1' htRem1_list hokS1 hppS1 houtS1 hvalS1
      refine ⟨stF, _, spF, tRemF,
        ord_runs_loop_true hcond Nat.one_ne_zero
          (ord_runs_seq_normal ha14 (ord_runs_seq_normal hcallU (ord_runs_seq_normal ha16
            (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 (ord_runs_seq_normal hrunS
              (ord_runs_seq_normal ha13 ha10))))))) hrunF,
        fun r h10 h13 h14 h15 h16 => by
          rw [hregF r h10 h13 h14 h15 h16]; simp [st8, st7, st6, st5, st4, st3, st2, st1, h10, h13, h14, h15, h16],
        r13F, hnF, hvrF, hfrF, hokRF, hppRF, hlistRF, hokSF, hppSF, houtSF, hvalSF, ?_⟩
      have hmul : (ORD_UNLINK_AMORT + 120) * (rem + 1) * ordStoreLog S.eCap =
          (ORD_UNLINK_AMORT + 120) * rem * ordStoreLog S.eCap +
            ORD_UNLINK_AMORT * ordStoreLog S.eCap + 120 * ordStoreLog S.eCap := by ring
      have h120 : 120 ≤ 120 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 120 hlog
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
        argsSize_cons, argsSize_nil] at *
      omega
  exact hloop selNodes.length 0 st0 S.splay (S.trees v) (by omega) hr0 hr6 hr9 hr10 hr12
    (by simpa [leftSpine, AuxTree.rootId] using hr13)
    harena.nodes_at (by rw [← hinv.vRoot_eq v hv]; exact harena.vRoot_at v hv) (fun _ _ _ => rfl)
    (hinv.ordTreeOk hv) (hinv.root_ppar v hv) (by simp)
    { null_node := hinv.null_node, clean := hinv.clean, inv := ⟨List.nodup_nil, trivial⟩,
      mem_le := fun _ h => absurd h List.not_mem_nil, count_le := by simp [leftSpine, AuxTree.countNodes] }
    (fun h => absurd rfl h)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-! ### Pass 6: `ordMoveZeroLoop` -/

/-- Pass 6 of `moveEnds`: zeros `scratch[0 .. 2*cnt - 1]`. -/
def ordMoveZeroLoop : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 11))
    (.store (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 0) ;;
     .store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)) (.const 0) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

theorem ordMoveZeroLoop_noRand : ordMoveZeroLoop.NoRand := by
  simp [ordMoveZeroLoop, Stmt.NoRand]

theorem ordMoveZeroLoop_runs
    {w scratch cnt : ℕ} {p : Program} (ω : ℕ → Bool) {st0 : State}
    (hz : ZeroFrom st0.mem (scratch + 2 * cnt))
    (hscr_w : scratch + 2 * cnt < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr6 : st0.regs 6 = scratch) (hr10 : st0.regs 10 = 0) (hr11 : st0.regs 11 = cnt) :
    ∃ st' c,
      Runs w p ω ordMoveZeroLoop st0 .normal st' c ∧
      (∀ r, r ≠ 10 → st'.regs r = st0.regs r) ∧
      ZeroFrom st'.mem scratch ∧
      (∀ a < scratch, st'.mem a = st0.mem a) ∧
      c ≤ 35 * cnt + 15 := by
  have hloop : ∀ rem (i : ℕ) (st : State),
      i + rem = cnt →
      st.regs 6 = scratch → st.regs 10 = i → st.regs 11 = cnt →
      (∀ a, scratch ≤ a → a < scratch + 2 * i → st.mem a = 0) →
      ZeroFrom st.mem (scratch + 2 * cnt) →
      (∀ a < scratch, st.mem a = st0.mem a) →
      ∃ st' c,
        Runs w p ω ordMoveZeroLoop st .normal st' c ∧
        (∀ r, r ≠ 10 → st'.regs r = st.regs r) ∧
        ZeroFrom st'.mem scratch ∧
        (∀ a < scratch, st'.mem a = st0.mem a) ∧
        c ≤ 35 * rem + 15 := by
    intro rem
    induction rem with
    | zero =>
      intro i st hi r6 r10 r11 hpre hpost hlt
      have hi_eq : i = cnt := by omega
      subst hi_eq
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) (by omega) (by omega)
      refine ⟨st, _, ord_runs_loop_false hcond, fun _ _ => rfl,
        fun a ha => by by_cases h : a < scratch + 2 * i; exact hpre a ha h; exact hpost a (by omega),
        hlt, by simp [Expr.size_bin, Expr.size_reg]⟩
    | succ rem ih =>
      intro i st hi r6 r10 r11 hpre hpost hlt
      have hcond : (Expr.bin .lt (.reg 10) (.reg 11)).eval w st = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r11) (by omega) (by omega)
      have hs1 : Runs w p ω (.store (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 0)) st .normal
          { st with mem := Function.update st.mem (scratch + 2 * i) 0 } _ :=
        runs_store_iff.mpr ⟨scratch + 2 * i, 0,
          by
            have he : (Expr.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))).eval w st = some (scratch + (i + i)) :=
              Expr.eval_add (Expr.eval_reg_of_eq r6)
                (Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r10) (by omega)) (by omega)
            rwa [show scratch + (i + i) = scratch + 2 * i by omega] at he,
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      set m1 := Function.update st.mem (scratch + 2 * i) 0
      set st1 : State := { st with mem := m1 }
      have hs2 : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)) (.const 0)) st1 .normal
          { st1 with mem := Function.update m1 (scratch + 2 * i + 1) 0 } _ :=
        runs_store_iff.mpr ⟨scratch + 2 * i + 1, 0,
          by
            have he : (Expr.bin .add (.bin .add (.reg 6) (.bin .add (.reg 10) (.reg 10))) (.const 1)).eval w st1 =
                some (scratch + (i + i) + 1) :=
              Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, r6]))
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, r10]))
                  (Expr.eval_reg_of_eq (by simp [st1, r10])) (by omega)) (by omega))
                (Expr.eval_const (by omega)) (by omega)
            rwa [show scratch + (i + i) + 1 = scratch + 2 * i + 1 by omega] at he,
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      set m2 := Function.update m1 (scratch + 2 * i + 1) 0
      set st2 : State := { st1 with mem := m2 }
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) st2 .normal
          { st2 with regs := Function.update st2.regs 10 (i + 1) } _ :=
        runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, r10]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 10 (i + 1) }
      obtain ⟨stF, cF, hrunF, hregF, hzF, hltF, hcF⟩ :=
        ih (i + 1) st3 (by omega) (by simp [st3, st2, st1, r6]) (by simp [st3]) (by simp [st3, st2, st1, r11])
          (fun a ha1 ha2 => by
            dsimp only [st3, st2, m2, m1]
            by_cases h1 : a = scratch + 2 * i + 1
            · rw [h1, Function.update_self]
            · rw [Function.update_of_ne h1]
              by_cases h2 : a = scratch + 2 * i
              · rw [h2, Function.update_self]
              · rw [Function.update_of_ne h2]; exact hpre a ha1 (by omega))
          (fun a ha => by
            dsimp only [st3, st2, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hpost a ha)
          (fun a ha => by
            dsimp only [st3, st2, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hlt a ha)
      refine ⟨stF, _, ord_runs_loop_true hcond Nat.one_ne_zero
        (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2 ha10)) hrunF,
        fun r h10 => by rw [hregF r h10]; simp [st3, st2, st1, h10], hzF, hltF, ?_⟩
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *
      omega
  exact hloop cnt 0 st0 (by omega) hr6 hr10 hr11 (fun _ ha1 ha2 => by omega) hz (fun _ _ => rfl)

end MinCostFlow.SparseCore.Program
