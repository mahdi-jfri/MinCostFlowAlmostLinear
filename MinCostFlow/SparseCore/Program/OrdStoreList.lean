module

public import MinCostFlow.SparseCore.Program.OrdStoreWalkJoin
import Mathlib.Tactic

/-!
# Order Store `list` Query Procedure (`op 1`)

This file implements and verifies `ordStoreListBody` (`op 1`, `[b, v, heap]`): it writes
`EndListAt mem' heap (ord v)` using a zero-scratch parent-pointer in-order traversal of
`S.trees v` in `O(|ord v| + 1)` worst-case time and returns `heap + 1 + |ord v|`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_LIST_MUL : ℕ := 300

/-! ### Operation `1`: `list` (`[b, v, heap]`) -/

/-- Parent-pointer in-order traversal loop for `ordStoreList`.
Registers: `r2 = heap`, `r4 = nb`, `r5 = cur`, `r7 = from` (`0/1/2`), `r8 = out`. -/
def ordListLoop : Stmt :=
  .loop (.reg 5)
    (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5))) ;;
     .cond (.bin .eq (.reg 7) (.const 0))
       (.assign 10 (.load (.reg 9)) ;;
        .cond (.reg 10) (.assign 5 (.reg 10)) (.assign 7 (.const 1)))
       (.cond (.bin .eq (.reg 7) (.const 1))
         (.assign 10 (.load (.bin .add (.reg 9) (.const 5))) ;;
          .store (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)) (.reg 10) ;;
          .assign 8 (.bin .add (.reg 8) (.const 1)) ;;
          .assign 11 (.load (.bin .add (.reg 9) (.const 1))) ;;
          .cond (.reg 11) (.assign 5 (.reg 11) ;; .assign 7 (.const 0)) (.assign 7 (.const 2)))
         (.assign 10 (.load (.bin .add (.reg 9) (.const 2))) ;;
          .cond (.bin .eq (.reg 10) (.const 0))
            (.assign 5 (.const 0))
            (.assign 11 (.load (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 10)))) ;;
             .cond (.bin .eq (.reg 11) (.reg 5)) (.assign 7 (.const 1)) (.assign 7 (.const 2)) ;;
             .assign 5 (.reg 10)))))

/-- `ordStoreList` (`op 1`) on `[b, v, heap]`. -/
def ordStoreListBody : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 5 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .cond (.bin .eq (.reg 5) (.const 0))
    (.store (.reg 2) (.const 0) ;;
     .ret (.bin .add (.reg 2) (.const 1)))
    (.assign 6 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5))) (.const 4))) ;;
     .store (.reg 2) (.reg 6) ;;
     .assign 7 (.const 0) ;;
     .assign 8 (.const 0) ;;
     ordListLoop ;;
     .ret (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 6)))

theorem ordStoreListBody_noRand : ordStoreListBody.NoRand := by
  simp [ordStoreListBody, ordListLoop, Stmt.NoRand]

/-- CPS structural induction for `ordListLoop`: traversing a non-empty subtree `t` from
`(cur = t.rootId, from = 0, out = k)` reaches `(cur = t.rootId, from = 2, out = k + t.countNodes)`
after writing `t.toList.map (fun u => (sp.nodes u).val)` into `mem[heap + 1 + k ..]`, and
continues with any post-subtree run of `ordListLoop`. -/
private theorem ordListLoop_cps
    {w nb cap heap : ℕ} {p : Program} (ω : ℕ → Bool)
    {sp : SplayState ℕ Unit Unit} {nf : ℕ → ℕ}
    (hnb_lt : nb + 8 * (cap + 1) ≤ heap) (hwide : 16 ≤ 2 ^ w) :
    ∀ (t : AuxTree) (par : ℕ), t ≠ .leaf →
      t.toList.Nodup → SplayState.SubtreeInv ordPayload sp par t →
      (∀ u ∈ t.toList, u ≤ cap) →
      ∀ (k : ℕ) (st : State) (Q : State → Prop) (cQ : ℕ),
        heap + 1 + k + t.countNodes < 2 ^ w →
        st.regs 2 = heap → st.regs 4 = nb → st.regs 5 = t.rootId →
        st.regs 7 = 0 → st.regs 8 = k →
        OrdNodesAt st.mem nb cap sp nf →
        (∀ (st2 : State),
          st2.regs 2 = heap → st2.regs 4 = nb → st2.regs 5 = t.rootId →
          st2.regs 7 = 2 → st2.regs 8 = k + t.countNodes →
          (∀ r, r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → st2.regs r = st.regs r) →
          (∀ i < t.countNodes, st2.mem (heap + 1 + (k + i)) = (sp.nodes (t.toList.getD i 0)).val) →
          (∀ a, ¬ (heap + 1 + k ≤ a ∧ a < heap + 1 + k + t.countNodes) → st2.mem a = st.mem a) →
          ∃ stF cF, Runs w p ω ordListLoop st2 .normal stF cF ∧ Q stF ∧ cF ≤ cQ) →
        ∃ stF cF, Runs w p ω ordListLoop st .normal stF cF ∧ Q stF ∧
          cF ≤ cQ + 240 * t.countNodes := by
  intro t
  induction t with
  | leaf => intro _ hne; exact absurd rfl hne
  | node id l r ihl ihr =>
    intro par _ hnd hsub hle k st Q cQ hw_k r2 r4 r5 r7 r8 hn hcont
    rcases hsub with ⟨hid_nz, hidL, hidR, hidP, -, -, -, hsubL, hsubR⟩
    rcases AuxTree.nodup_node_unfold hnd with ⟨hLnd, hid_nL, hRnd, hid_nR, hLR⟩
    have hid_c : id ≤ cap := hle id (AuxTree.rootId_mem (t := .node id l r) (by simp))
    have hnb_w : nb + 8 * (cap + 1) < 2 ^ w := by omega
    simp only [AuxTree.rootId] at r5
    -- Helper: execute from (cur = id, from = 1, out = k + l.countNodes) to finish `node id l r`
    have hfrom1 : ∀ (st1 : State),
        st1.regs 2 = heap → st1.regs 4 = nb → st1.regs 5 = id →
        st1.regs 7 = 1 → st1.regs 8 = k + l.countNodes →
        (∀ r, r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → st1.regs r = st.regs r) →
        (∀ i < l.countNodes, st1.mem (heap + 1 + (k + i)) = (sp.nodes (l.toList.getD i 0)).val) →
        (∀ a, ¬ (heap + 1 + k ≤ a ∧ a < heap + 1 + k + l.countNodes) → st1.mem a = st.mem a) →
        ∃ stF cF, Runs w p ω ordListLoop st1 .normal stF cF ∧ Q stF ∧
          cF ≤ cQ + 240 * r.countNodes + 120 := by
      intro st1 s2 s4 s5 s7 s8 sreg sl_mem sl_out
      have hn1 : OrdNodesAt st1.mem nb cap sp nf :=
        hn.congr fun a ha => sl_out a (by unfold InOrdNodes at ha; omega)
      have hc5 : (Expr.reg 5).eval w st1 = some id := Expr.eval_reg_of_eq s5
      have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5)))) st1 .normal
          { st1 with regs := Function.update st1.regs 9 (nb + 8 * id) } _ :=
        runs_assign_iff.mpr ⟨nb + 8 * id, Expr.eval_add (Expr.eval_reg_of_eq s4)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq s5) (by omega)) (by omega), rfl, rfl, rfl⟩
      set u1 : State := { st1 with regs := Function.update st1.regs 9 (nb + 8 * id) }
      have hc7_0 : (Expr.bin .eq (.reg 7) (.const 0)).eval w u1 = some 0 :=
        Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 1) (by simp [u1, s7])) (Expr.eval_const (by omega)) (by omega) (by omega)
      have hc7_1 : (Expr.bin .eq (.reg 7) (.const 1)).eval w u1 = some 1 :=
        Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 1) (by simp [u1, s7])) (Expr.eval_const (by omega)) rfl (by omega)
      have hu1_9 : u1.regs 9 = nb + 8 * id := by simp [u1]
      have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 5)))) u1 .normal
          { u1 with regs := Function.update u1.regs 10 (sp.nodes id).val } _ :=
        runs_assign_iff.mpr ⟨(sp.nodes id).val, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hu1_9)
          (Expr.eval_const (by omega)) (by omega)) (by simpa [ordNodeAddr] using (hn1 id hid_c).2.2.2.2.2.1), rfl, rfl, rfl⟩
      set u2 : State := { u1 with regs := Function.update u1.regs 10 (sp.nodes id).val }
      have hs_val : Runs w p ω (.store (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)) (.reg 10)) u2 .normal
          { u2 with mem := Function.update st1.mem (heap + 1 + (k + l.countNodes)) (sp.nodes id).val } _ :=
        runs_store_iff.mpr ⟨heap + 1 + (k + l.countNodes), (sp.nodes id).val,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [u2, u1, s2])) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_reg_of_eq (by simp [u2, u1, s8])) (by simp [AuxTree.countNodes] at hw_k; omega),
          Expr.eval_reg_of_eq (by simp [u2]), rfl, rfl, rfl⟩
      set m_id := Function.update st1.mem (heap + 1 + (k + l.countNodes)) (sp.nodes id).val
      set u3 : State := { u2 with mem := m_id }
      have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) u3 .normal
          { u3 with regs := Function.update u3.regs 8 (k + l.countNodes + 1) } _ :=
        runs_assign_iff.mpr ⟨k + l.countNodes + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [u3, u2, u1, s8]))
          (Expr.eval_const (by omega)) (by simp [AuxTree.countNodes] at hw_k; omega), rfl, rfl, rfl⟩
      set u4 : State := { u3 with regs := Function.update u3.regs 8 (k + l.countNodes + 1) }
      have hm_idR : m_id (nb + 8 * id + 1) = r.rootId := by
        dsimp only [m_id]; rw [Function.update_of_ne (by omega), ← hidR]; exact (hn1 id hid_c).2.1
      have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 9) (.const 1)))) u4 .normal
          { u4 with regs := Function.update u4.regs 11 r.rootId } _ :=
        runs_assign_iff.mpr ⟨r.rootId, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [u4, u3, u2, u1]))
          (Expr.eval_const (by omega)) (by omega)) hm_idR, rfl, rfl, rfl⟩
      set u5 : State := { u4 with regs := Function.update u4.regs 11 r.rootId }
      cases hr_eq : r with
      | leaf =>
        have hc11 : (Expr.reg 11).eval w u5 = some 0 := Expr.eval_reg_of_eq (by simp [u5, hr_eq, AuxTree.rootId])
        have ha7 : Runs w p ω (.assign 7 (.const 2)) u5 .normal { u5 with regs := Function.update u5.regs 7 2 } _ :=
          runs_assign_iff.mpr ⟨2, Expr.eval_const (by omega), rfl, rfl, rfl⟩
        set u6 : State := { u5 with regs := Function.update u5.regs 7 2 }
        obtain ⟨stF, cF, hrunF, hQF, hcF⟩ := hcont u6
          (by simp [u6, u5, u4, u3, u2, u1, s2]) (by simp [u6, u5, u4, u3, u2, u1, s4])
          (by simp [u6, u5, u4, u3, u2, u1, s5, AuxTree.rootId]) (by simp [u6])
          (by simp [u6, u5, u4, hr_eq, AuxTree.countNodes]; omega)
          (fun r' h5 h7 h8 h9 h10 h11 => by simp [u6, u5, u4, u3, u2, u1, h5, h7, h8, h9, h10, h11]; exact sreg r' h5 h7 h8 h9 h10 h11)
          (fun i hi => by
            dsimp only [u6, u5, u4, u3, m_id]
            simp only [hr_eq, AuxTree.countNodes] at hi
            by_cases hil : i < l.countNodes
            · rw [Function.update_of_ne (by omega), sl_mem i hil]
              have hgd : (AuxTree.node id l .leaf).toList.getD i 0 = l.toList.getD i 0 := by
                simp only [AuxTree.toList, List.append_nil, List.getD_eq_getElem?_getD,
                  List.getElem?_append_left (by rw [AuxTree.length_toList]; exact hil)]
              rw [hr_eq, hgd]
            · have hieq : i = l.countNodes := by omega
              subst hieq; rw [Function.update_self]
              have hgd : (AuxTree.node id l .leaf).toList.getD l.countNodes 0 = id := by
                simp only [AuxTree.toList, List.append_nil]
                rw [List.getD_eq_getElem?_getD,
                  List.getElem?_append_right (by rw [AuxTree.length_toList]),
                  AuxTree.length_toList, Nat.sub_self]
                rfl
              rw [hr_eq, hgd])
          (fun a ha => by
            dsimp only [u6, u5, u4, u3, m_id]
            rw [Function.update_of_ne (by simp [hr_eq, AuxTree.countNodes] at ha; omega)]
            exact sl_out a (by simp [hr_eq, AuxTree.countNodes] at ha; omega))
        refine ⟨stF, _, ord_runs_loop_true hc5 hid_nz (ord_runs_seq_normal ha9 (ord_runs_cond_false hc7_0
          (ord_runs_cond_true hc7_1 Nat.one_ne_zero (ord_runs_seq_normal ha10 (ord_runs_seq_normal hs_val
            (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha11 (ord_runs_cond_false hc11 ha7)))))))) hrunF, hQF, ?_⟩
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, hr_eq, AuxTree.countNodes] at *
        omega
      | node rid rl rr =>
        have hrid_nz : rid ≠ 0 := (hr_eq ▸ hsubR).1
        have hrid_c : rid ≤ cap := hle rid (by rw [hr_eq]; exact List.mem_append_right _ (AuxTree.rootId_mem (t := .node rid rl rr) (by simp)))
        have hc11 : (Expr.reg 11).eval w u5 = some rid := Expr.eval_reg_of_eq (by simp [u5, hr_eq, AuxTree.rootId])
        have ha5r : Runs w p ω (.assign 5 (.reg 11)) u5 .normal { u5 with regs := Function.update u5.regs 5 rid } _ :=
          runs_assign_iff.mpr ⟨rid, Expr.eval_reg_of_eq (by simp [u5, hr_eq, AuxTree.rootId]), rfl, rfl, rfl⟩
        set u6 : State := { u5 with regs := Function.update u5.regs 5 rid }
        have ha7r : Runs w p ω (.assign 7 (.const 0)) u6 .normal { u6 with regs := Function.update u6.regs 7 0 } _ :=
          runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
        set u7 : State := { u6 with regs := Function.update u6.regs 7 0 }
        have hnu7 : OrdNodesAt u7.mem nb cap sp nf :=
          hn1.congr fun a ha => by dsimp only [u7, u6, u5, u4, u3, m_id]; rw [Function.update_of_ne (by unfold InOrdNodes at ha; omega)]
        obtain ⟨stF, cF, hrunR, hQF, hcR⟩ := ihr id (by rw [hr_eq]; simp) hRnd hsubR
          (fun x hx => hle x (List.mem_append_right _ hx)) (k + l.countNodes + 1) u7 Q (cQ + 60)
          (by simp [AuxTree.countNodes] at hw_k ⊢; omega)
          (by simp [u7, u6, u5, u4, u3, u2, u1, s2]) (by simp [u7, u6, u5, u4, u3, u2, u1, s4])
          (by simp [u7, u6, hr_eq, AuxTree.rootId]) (by simp [u7]) (by simp [u7, u6, u5, u4]) hnu7
          (fun stR r2R r4R r5R r7R r8R sregR sr_mem sr_out => by
            -- One exit iteration from (cur = rid, from = 2) up to (cur = id, from = 2)
            simp only [hr_eq, AuxTree.rootId] at r5R
            have hnR : OrdNodesAt stR.mem nb cap sp nf :=
              hnu7.congr fun a ha => sr_out a (by unfold InOrdNodes at ha; omega)
            have hc5R : (Expr.reg 5).eval w stR = some rid := Expr.eval_reg_of_eq r5R
            have ha9R : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5)))) stR .normal
                { stR with regs := Function.update stR.regs 9 (nb + 8 * rid) } _ :=
              runs_assign_iff.mpr ⟨nb + 8 * rid, Expr.eval_add (Expr.eval_reg_of_eq r4R)
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r5R) (by omega)) (by omega), rfl, rfl, rfl⟩
            set v1 : State := { stR with regs := Function.update stR.regs 9 (nb + 8 * rid) }
            have hc7R0 : (Expr.bin .eq (.reg 7) (.const 0)).eval w v1 = some 0 :=
              Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [v1, r7R])) (Expr.eval_const (by omega)) (by omega) (by omega)
            have hc7R1 : (Expr.bin .eq (.reg 7) (.const 1)).eval w v1 = some 0 :=
              Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [v1, r7R])) (Expr.eval_const (by omega)) (by omega) (by omega)
            have hrid_par : (sp.nodes rid).par = id := (hr_eq ▸ hsubR).2.2.2.1
            have hv1_9 : v1.regs 9 = nb + 8 * rid := by simp [v1]
            have ha10R : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 2)))) v1 .normal
                { v1 with regs := Function.update v1.regs 10 id } _ :=
              runs_assign_iff.mpr ⟨id, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hv1_9)
                (Expr.eval_const (by omega)) (by omega)) (by rw [← hrid_par]; simpa [ordNodeAddr] using (hnR rid hrid_c).2.2.1), rfl, rfl, rfl⟩
            set v2 : State := { v1 with regs := Function.update v1.regs 10 id }
            have hc10R : (Expr.bin .eq (.reg 10) (.const 0)).eval w v2 = some 0 :=
              Expr.eval_eq_false (Expr.eval_reg_of_eq (v := id) (by simp [v2])) (Expr.eval_const (by omega)) hid_nz (by omega)
            have hv2_4 : v2.regs 4 = nb := by simp [v2, v1, r4R]
            have hv2_10 : v2.regs 10 = id := by simp [v2]
            have ha11R : Runs w p ω (.assign 11 (.load (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 10))))) v2 .normal
                { v2 with regs := Function.update v2.regs 11 l.rootId } _ :=
              runs_assign_iff.mpr ⟨l.rootId, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hv2_4)
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hv2_10) (by omega)) (by omega))
                (by rw [← hidL]; simpa [ordNodeAddr] using (hnR id hid_c).1), rfl, rfl, rfl⟩
            set v3 : State := { v2 with regs := Function.update v2.regs 11 l.rootId }
            have hl_ne_rid : l.rootId ≠ rid := by
              cases hl' : l with
              | leaf => simp [AuxTree.rootId]; exact Ne.symm hrid_nz
              | node lid ll lr =>
                intro h; simp only [AuxTree.rootId] at h
                exact hLR lid (by rw [hl']; exact AuxTree.rootId_mem (t := .node lid ll lr) (by simp))
                  (by rw [h, hr_eq]; exact AuxTree.rootId_mem (t := .node rid rl rr) (by simp))
            have hc11R : (Expr.bin .eq (.reg 11) (.reg 5)).eval w v3 = some 0 :=
              Expr.eval_eq_false (Expr.eval_reg_of_eq (v := l.rootId) (by simp [v3]))
                (Expr.eval_reg_of_eq (v := rid) (by simp [v3, v2, v1, r5R])) hl_ne_rid (by omega)
            have ha7R' : Runs w p ω (.assign 7 (.const 2)) v3 .normal { v3 with regs := Function.update v3.regs 7 2 } _ :=
              runs_assign_iff.mpr ⟨2, Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set v4 : State := { v3 with regs := Function.update v3.regs 7 2 }
            have ha5R' : Runs w p ω (.assign 5 (.reg 10)) v4 .normal { v4 with regs := Function.update v4.regs 5 id } _ :=
              runs_assign_iff.mpr ⟨id, Expr.eval_reg_of_eq (by simp [v4, v3, v2]), rfl, rfl, rfl⟩
            set v5 : State := { v4 with regs := Function.update v4.regs 5 id }
            obtain ⟨stF, cF, hrunF, hQF, hcF⟩ := hcont v5
              (by simp [v5, v4, v3, v2, v1, r2R]) (by simp [v5, v4, v3, v2, v1, r4R])
              (by simp [v5, AuxTree.rootId]) (by simp [v5, v4])
              (by simp [v5, v4, v3, v2, v1, r8R, AuxTree.countNodes]; omega)
              (fun r' h5 h7 h8 h9 h10 h11 => by
                simp only [v5, v4, v3, v2, v1, Function.update_of_ne h5, Function.update_of_ne h7,
                  Function.update_of_ne h11, Function.update_of_ne h10, Function.update_of_ne h9]
                rw [sregR r' h5 h7 h8 h9 h10 h11]; simp [u7, u6, u5, u4, u3, u2, u1, h5, h7, h8, h9, h10, h11]
                exact sreg r' h5 h7 h8 h9 h10 h11)
              (fun i hi => by
                dsimp only [v5, v4, v3, v2, v1]
                simp only [AuxTree.countNodes] at hi
                by_cases hil : i < l.countNodes
                · rw [sr_out _ (by omega)]; dsimp only [u7, u6, u5, u4, u3, m_id]
                  rw [Function.update_of_ne (by omega), sl_mem i hil]
                  have hgd : (AuxTree.node id l r).toList.getD i 0 = l.toList.getD i 0 := by
                    simp only [AuxTree.toList, List.append_assoc, List.getD_eq_getElem?_getD,
                      List.getElem?_append_left (by rw [AuxTree.length_toList]; exact hil)]
                  rw [hgd]
                · by_cases hieq : i = l.countNodes
                  · subst hieq; rw [sr_out _ (by omega)]; dsimp only [u7, u6, u5, u4, u3, m_id]; rw [Function.update_self]
                    have hgd : (AuxTree.node id l r).toList.getD l.countNodes 0 = id := by
                      rw [AuxTree.toList, List.append_assoc, List.getD_eq_getElem?_getD,
                        List.getElem?_append_right (by rw [AuxTree.length_toList]),
                        AuxTree.length_toList, Nat.sub_self]
                      rfl
                    rw [hgd]
                  · have hir : i - (l.countNodes + 1) < r.countNodes := by omega
                    have hmem_r := sr_mem (i - (l.countNodes + 1)) hir
                    rw [show heap + 1 + (k + i) = heap + 1 + (k + l.countNodes + 1 + (i - (l.countNodes + 1))) by omega, hmem_r]
                    have hgd : (AuxTree.node id l r).toList.getD i 0 = r.toList.getD (i - (l.countNodes + 1)) 0 := by
                      rw [AuxTree.toList, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                        List.getElem?_append_right (by simp [AuxTree.length_toList]; omega)]
                      simp [AuxTree.length_toList]
                    rw [hgd])
              (fun a ha => by
                dsimp only [v5, v4, v3, v2, v1]
                simp only [AuxTree.countNodes] at ha
                rw [sr_out a (by omega)]; dsimp only [u7, u6, u5, u4, u3, m_id]
                rw [Function.update_of_ne (by omega)]; exact sl_out a (by omega))
            refine ⟨stF, _, ord_runs_loop_true hc5R hrid_nz (ord_runs_seq_normal ha9R (ord_runs_cond_false hc7R0
              (ord_runs_cond_false hc7R1 (ord_runs_seq_normal ha10R (ord_runs_cond_false hc10R
                (ord_runs_seq_normal ha11R (ord_runs_seq_normal (ord_runs_cond_false hc11R ha7R') ha5R'))))))) hrunF, hQF, ?_⟩
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
            omega)
        refine ⟨stF, _, ord_runs_loop_true hc5 hid_nz (ord_runs_seq_normal ha9 (ord_runs_cond_false hc7_0
          (ord_runs_cond_true hc7_1 Nat.one_ne_zero (ord_runs_seq_normal ha10 (ord_runs_seq_normal hs_val
            (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha11 (ord_runs_cond_true hc11 hrid_nz
              (ord_runs_seq_normal ha5r ha7r))))))))) hrunR, hQF, ?_⟩
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, hr_eq] at *
        omega
    -- Step 1: Enter from (cur = id, from = 0, out = k)
    have hc5 : (Expr.reg 5).eval w st = some id := Expr.eval_reg_of_eq r5
    have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5)))) st .normal
        { st with regs := Function.update st.regs 9 (nb + 8 * id) } _ :=
      runs_assign_iff.mpr ⟨nb + 8 * id, Expr.eval_add (Expr.eval_reg_of_eq r4)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r5) (by omega)) (by omega), rfl, rfl, rfl⟩
    set w1 : State := { st with regs := Function.update st.regs 9 (nb + 8 * id) }
    have hc7 : (Expr.bin .eq (.reg 7) (.const 0)).eval w w1 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [w1, r7])) (Expr.eval_const (by omega)) rfl (by omega)
    have hw1_9 : w1.regs 9 = nb + 8 * id := by simp [w1]
    have ha10 : Runs w p ω (.assign 10 (.load (.reg 9))) w1 .normal
        { w1 with regs := Function.update w1.regs 10 l.rootId } _ :=
      runs_assign_iff.mpr ⟨l.rootId, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hw1_9)
        (by rw [← hidL]; simpa [ordNodeAddr] using (hn id hid_c).1), rfl, rfl, rfl⟩
    set w2 : State := { w1 with regs := Function.update w1.regs 10 l.rootId }
    cases hl_eq : l with
    | leaf =>
      have hc10 : (Expr.reg 10).eval w w2 = some 0 := Expr.eval_reg_of_eq (by simp [w2, hl_eq, AuxTree.rootId])
      have ha7 : Runs w p ω (.assign 7 (.const 1)) w2 .normal { w2 with regs := Function.update w2.regs 7 1 } _ :=
        runs_assign_iff.mpr ⟨1, Expr.eval_const (by omega), rfl, rfl, rfl⟩
      set w3 : State := { w2 with regs := Function.update w2.regs 7 1 }
      obtain ⟨stF, cF, hrun1, hQF, hc1⟩ := hfrom1 w3
        (by simp [w3, w2, w1, r2]) (by simp [w3, w2, w1, r4]) (by simp [w3, w2, w1, r5])
        (by simp [w3]) (by simp [w3, w2, w1, r8, hl_eq, AuxTree.countNodes])
        (fun r' h5 h7 h8 h9 h10 h11 => by simp [w3, w2, w1, h5, h7, h8, h9, h10, h11])
        (fun i hi => by simp [hl_eq, AuxTree.countNodes] at hi) (fun _ _ => rfl)
      refine ⟨stF, _, ord_runs_loop_true hc5 hid_nz (ord_runs_seq_normal ha9
        (ord_runs_cond_true hc7 Nat.one_ne_zero (ord_runs_seq_normal ha10 (ord_runs_cond_false hc10 ha7)))) hrun1, hQF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, hl_eq, AuxTree.countNodes] at *
      omega
    | node lid ll lr =>
      have hlid_nz : lid ≠ 0 := (hl_eq ▸ hsubL).1
      have hlid_c : lid ≤ cap := hle lid (by rw [hl_eq]; exact List.mem_append_left _ (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp))))
      have hc10 : (Expr.reg 10).eval w w2 = some lid := Expr.eval_reg_of_eq (by simp [w2, hl_eq, AuxTree.rootId])
      have ha5 : Runs w p ω (.assign 5 (.reg 10)) w2 .normal { w2 with regs := Function.update w2.regs 5 lid } _ :=
        runs_assign_iff.mpr ⟨lid, Expr.eval_reg_of_eq (by simp [w2, hl_eq, AuxTree.rootId]), rfl, rfl, rfl⟩
      set w3 : State := { w2 with regs := Function.update w2.regs 5 lid }
      obtain ⟨stF, cF, hrunL, hQF, hcL⟩ := ihl id (by rw [hl_eq]; simp) hLnd hsubL
        (fun x hx => hle x (List.mem_append_left _ (List.mem_append_left _ hx))) k w3 Q (cQ + 240 * r.countNodes + 180)
        (by simp [AuxTree.countNodes] at hw_k ⊢; omega)
        (by simp [w3, w2, w1, r2]) (by simp [w3, w2, w1, r4]) (by simp [w3, hl_eq, AuxTree.rootId])
        (by simp [w3, w2, w1, r7]) (by simp [w3, w2, w1, r8]) hn
        (fun stL r2L r4L r5L r7L r8L sregL sl_mem sl_out => by
          -- One exit iteration from (cur = lid, from = 2) up to (cur = id, from = 1)
          simp only [hl_eq, AuxTree.rootId] at r5L
          have hnL : OrdNodesAt stL.mem nb cap sp nf :=
            hn.congr fun a ha => sl_out a (by unfold InOrdNodes at ha; omega)
          have hc5L : (Expr.reg 5).eval w stL = some lid := Expr.eval_reg_of_eq r5L
          have ha9L : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5)))) stL .normal
              { stL with regs := Function.update stL.regs 9 (nb + 8 * lid) } _ :=
            runs_assign_iff.mpr ⟨nb + 8 * lid, Expr.eval_add (Expr.eval_reg_of_eq r4L)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r5L) (by omega)) (by omega), rfl, rfl, rfl⟩
          set q1 : State := { stL with regs := Function.update stL.regs 9 (nb + 8 * lid) }
          have hc7L0 : (Expr.bin .eq (.reg 7) (.const 0)).eval w q1 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [q1, r7L])) (Expr.eval_const (by omega)) (by omega) (by omega)
          have hc7L1 : (Expr.bin .eq (.reg 7) (.const 1)).eval w q1 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [q1, r7L])) (Expr.eval_const (by omega)) (by omega) (by omega)
          have hlid_par : (sp.nodes lid).par = id := (hl_eq ▸ hsubL).2.2.2.1
          have hq1_9 : q1.regs 9 = nb + 8 * lid := by simp [q1]
          have ha10L : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 2)))) q1 .normal
              { q1 with regs := Function.update q1.regs 10 id } _ :=
            runs_assign_iff.mpr ⟨id, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hq1_9)
              (Expr.eval_const (by omega)) (by omega)) (by rw [← hlid_par]; simpa [ordNodeAddr] using (hnL lid hlid_c).2.2.1), rfl, rfl, rfl⟩
          set q2 : State := { q1 with regs := Function.update q1.regs 10 id }
          have hc10L : (Expr.bin .eq (.reg 10) (.const 0)).eval w q2 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := id) (by simp [q2])) (Expr.eval_const (by omega)) hid_nz (by omega)
          have hq2_4 : q2.regs 4 = nb := by simp [q2, q1, r4L]
          have hq2_10 : q2.regs 10 = id := by simp [q2]
          have ha11L : Runs w p ω (.assign 11 (.load (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 10))))) q2 .normal
              { q2 with regs := Function.update q2.regs 11 lid } _ :=
            runs_assign_iff.mpr ⟨lid, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hq2_4)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hq2_10) (by omega)) (by omega))
              (by simp only [hl_eq, AuxTree.rootId] at hidL; rw [← hidL]; simpa [ordNodeAddr] using (hnL id hid_c).1), rfl, rfl, rfl⟩
          set q3 : State := { q2 with regs := Function.update q2.regs 11 lid }
          have hc11L : (Expr.bin .eq (.reg 11) (.reg 5)).eval w q3 = some 1 :=
            Expr.eval_eq_true (Expr.eval_reg_of_eq (v := lid) (by simp [q3]))
              (Expr.eval_reg_of_eq (v := lid) (by simp [q3, q2, q1, r5L])) rfl (by omega)
          have ha7L' : Runs w p ω (.assign 7 (.const 1)) q3 .normal { q3 with regs := Function.update q3.regs 7 1 } _ :=
            runs_assign_iff.mpr ⟨1, Expr.eval_const (by omega), rfl, rfl, rfl⟩
          set q4 : State := { q3 with regs := Function.update q3.regs 7 1 }
          have ha5L' : Runs w p ω (.assign 5 (.reg 10)) q4 .normal { q4 with regs := Function.update q4.regs 5 id } _ :=
            runs_assign_iff.mpr ⟨id, Expr.eval_reg_of_eq (by simp [q4, q3, q2]), rfl, rfl, rfl⟩
          set q5 : State := { q4 with regs := Function.update q4.regs 5 id }
          obtain ⟨stF, cF, hrun1, hQF, hc1⟩ := hfrom1 q5
            (by simp [q5, q4, q3, q2, q1, r2L]) (by simp [q5, q4, q3, q2, q1, r4L]) (by simp [q5])
            (by simp [q5, q4]) (by simp [q5, q4, q3, q2, q1, r8L])
            (fun r' h5 h7 h8 h9 h10 h11 => by
              simp only [q5, q4, q3, q2, q1, Function.update_of_ne h5, Function.update_of_ne h7,
                Function.update_of_ne h11, Function.update_of_ne h10, Function.update_of_ne h9]
              rw [sregL r' h5 h7 h8 h9 h10 h11]; simp [w3, w2, w1, h5, h7, h8, h9, h10, h11])
            sl_mem sl_out
          refine ⟨stF, _, ord_runs_loop_true hc5L hlid_nz (ord_runs_seq_normal ha9L (ord_runs_cond_false hc7L0
            (ord_runs_cond_false hc7L1 (ord_runs_seq_normal ha10L (ord_runs_cond_false hc10L
              (ord_runs_seq_normal ha11L (ord_runs_seq_normal (ord_runs_cond_true hc11L Nat.one_ne_zero ha7L') ha5L'))))))) hrun1, hQF, ?_⟩
          simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
          omega)
      refine ⟨stF, _, ord_runs_loop_true hc5 hid_nz (ord_runs_seq_normal ha9
        (ord_runs_cond_true hc7 Nat.one_ne_zero (ord_runs_seq_normal ha10 (ord_runs_cond_true hc10 hlid_nz ha5)))) hrunL, hQF, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, AuxTree.countNodes, hl_eq] at *
      omega

theorem ordStoreListBody_runs
    {w b v heap pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem) (hv : v < S.vCap)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap + (1 + (ord v).length) < 2 ^ w) :
    ∃ o st' c, Runs w p ω ordStoreListBody (startState [b, v, heap] mem pos) o st' c ∧
      o.value = heap + 1 + (ord v).length ∧
      OrdArenaAt b S st'.mem ∧
      EndListAt st'.mem heap (ord v) ∧
      ZeroFrom st'.mem (heap + 1 + (ord v).length) ∧
      (∀ a < heap, st'.mem a = mem a) ∧
      c ≤ ORD_LIST_MUL * ((ord v).length + 1) := by
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  have hwide : 16 ≤ 2 ^ w := by omega
  set vr := ordVRootBase b with hvr_def
  set nb := ordNodesBase b S.vCap S.eCap with hnb_def
  have hnb_le : nb + 8 * (S.nextNode + 1) ≤ heap := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb_def]; omega
  have hlen_eq : (S.trees v).countNodes = (ord v).length := by
    rw [← hinv.list_eq v hv, List.length_map, AuxTree.length_toList]
  set st0 : State := startState [b, v, heap] mem pos
  have ha3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 2)))) st0 .normal
      { st0 with regs := Function.update st0.regs 3 vr } _ :=
    runs_assign_iff.mpr ⟨vr, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_vRoot, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 vr }
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 4)))) st1 .normal
      { st1 with regs := Function.update st1.regs 4 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_nodes, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 4 nb }
  have hm_vr : mem (vr + v) = (S.trees v).rootId := by
    rw [← hinv.vRoot_eq v hv]; exact harena.vRoot_at v hv
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 3) (.reg 1)))) st2 .normal
      { st2 with regs := Function.update st2.regs 5 (S.trees v).rootId } _ :=
    runs_assign_iff.mpr ⟨(S.trees v).rootId, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st2, st1])) (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]))
      (by rw [hvr_def]; unfold ordVRootBase; omega)) hm_vr, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 5 (S.trees v).rootId }
  cases htv : S.trees v with
  | leaf =>
    have hord_nil : ord v = [] := by have := hinv.list_eq v hv; rw [htv] at this; exact this.symm
    have hc : (Expr.bin .eq (.reg 5) (.const 0)).eval w st3 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [st3, htv, AuxTree.rootId]))
        (Expr.eval_const (by omega)) rfl (by omega)
    have hs0 : Runs w p ω (.store (.reg 2) (.const 0)) st3 .normal
        { st3 with mem := Function.update mem heap 0 } _ :=
      runs_store_iff.mpr ⟨heap, 0, Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set st4 : State := { st3 with mem := Function.update mem heap 0 }
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) st4 (.returned (heap + 1)) st4 _ :=
      runs_ret_iff.mpr ⟨heap + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned (heap + 1), st4, _,
      ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_seq_normal ha5
        (ord_runs_cond_true hc Nat.one_ne_zero (ord_runs_seq_normal hs0 hret)))),
      by simp [Outcome.value, hord_nil],
      harena.congr hinv.next_le (fun a ha => by dsimp only [st4]; exact Function.update_of_ne (by unfold ordFoot at ha; omega) _ _),
      ⟨by dsimp only [st4]; rw [Function.update_self, hord_nil]; rfl, fun i hi => by simp [hord_nil] at hi⟩,
      fun a ha => by dsimp only [st4]; rw [Function.update_of_ne (by simp [hord_nil] at ha; omega)]; exact hz a (by omega),
      fun a ha => by dsimp only [st4]; exact Function.update_of_ne (by omega) _ _, ?_⟩
    unfold ORD_LIST_MUL; simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, hord_nil, List.length_nil] at *; omega
  | node rid l r =>
    have htv_inv : TreeInv ordPayload S.splay (.node rid l r) := htv ▸ hinv.tree_inv v hv
    have hrid_nz : rid ≠ 0 := htv_inv.sub.1
    have hrid_c : rid ≤ S.nextNode := (hinv.live_le_nextNode hv (by rw [htv]; exact AuxTree.rootId_mem (t := .node rid l r) (by simp))).2
    have hrid_sz : (S.splay.nodes rid).sz = (ord v).length := by
      rw [← hlen_eq, htv]; exact htv_inv.sub.2.2.2.2.2.1
    have hc : (Expr.bin .eq (.reg 5) (.const 0)).eval w st3 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (v := rid) (by simp [st3, htv, AuxTree.rootId]))
        (Expr.eval_const (by omega)) hrid_nz (by omega)
    have hst3_4 : st3.regs 4 = nb := by simp [st3, st2]
    have hst3_5 : st3.regs 5 = rid := by simp [st3, htv, AuxTree.rootId]
    have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5))) (.const 4)))) st3 .normal
        { st3 with regs := Function.update st3.regs 6 (ord v).length } _ :=
      runs_assign_iff.mpr ⟨(ord v).length, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq hst3_4)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hst3_5) (by omega)) (by omega))
        (Expr.eval_const (by omega)) (by omega)) (by dsimp only [st3, st2, st1, st0, startState]; rw [← hrid_sz, hnb_def]; simpa [ordNodeAddr] using (harena.nodes_at rid hrid_c).2.2.2.2.1), rfl, rfl, rfl⟩
    set st4 : State := { st3 with regs := Function.update st3.regs 6 (ord v).length }
    have hs_len : Runs w p ω (.store (.reg 2) (.reg 6)) st4 .normal
        { st4 with mem := Function.update mem heap (ord v).length } _ :=
      runs_store_iff.mpr ⟨heap, (ord v).length, Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]),
        Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
    set st5 : State := { st4 with mem := Function.update mem heap (ord v).length }
    have ha7 : Runs w p ω (.assign 7 (.const 0)) st5 .normal { st5 with regs := Function.update st5.regs 7 0 } _ :=
      runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set st6 : State := { st5 with regs := Function.update st5.regs 7 0 }
    have ha8 : Runs w p ω (.assign 8 (.const 0)) st6 .normal { st6 with regs := Function.update st6.regs 8 0 } _ :=
      runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set st7 : State := { st6 with regs := Function.update st6.regs 8 0 }
    have hn7 : OrdNodesAt st7.mem nb S.nextNode S.splay S.nextFree :=
      OrdNodesAt.congr harena.nodes_at fun a ha => by dsimp only [st7, st6, st5]; rw [Function.update_of_ne (by unfold InOrdNodes at ha; omega)]
    let Q : State → Prop := fun stF =>
      stF.regs 2 = heap ∧ stF.regs 6 = (ord v).length ∧
      EndListAt stF.mem heap (ord v) ∧
      ZeroFrom stF.mem (heap + 1 + (ord v).length) ∧
      (∀ a < heap, stF.mem a = mem a)
    obtain ⟨stF, cL, hrunL, hQF, hcL⟩ :=
      ordListLoop_cps (p := p) ω hnb_le hwide (.node rid l r) 0 (by simp) htv_inv.nodup htv_inv.sub
        (fun u hu => (hinv.live_le_nextNode hv (htv ▸ hu)).2) 0 st7 Q 45
        (by rw [← htv, hlen_eq]; omega)
        (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState])
        (by simp [st7, st6, st5, st4, st3, st2]) (by simp [st7, st6, st5, st4, st3, htv, AuxTree.rootId])
        (by simp [st7, st6]) (by simp [st7]) hn7
        (fun stE e2 e4 e5 e7 _ sregE emem eout => by
          -- Final exit iteration at root: par = 0 → cur := 0 → loop exits
          simp only [AuxTree.rootId] at e5
          have hnE : OrdNodesAt stE.mem nb S.nextNode S.splay S.nextFree :=
            hn7.congr fun a ha => eout a (by unfold InOrdNodes at ha; omega)
          have hc5E : (Expr.reg 5).eval w stE = some rid := Expr.eval_reg_of_eq e5
          have ha9E : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.bin .mul (.const 8) (.reg 5)))) stE .normal
              { stE with regs := Function.update stE.regs 9 (nb + 8 * rid) } _ :=
            runs_assign_iff.mpr ⟨nb + 8 * rid, Expr.eval_add (Expr.eval_reg_of_eq e4)
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq e5) (by omega)) (by omega), rfl, rfl, rfl⟩
          set z1 : State := { stE with regs := Function.update stE.regs 9 (nb + 8 * rid) }
          have hc7E0 : (Expr.bin .eq (.reg 7) (.const 0)).eval w z1 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [z1, e7])) (Expr.eval_const (by omega)) (by omega) (by omega)
          have hc7E1 : (Expr.bin .eq (.reg 7) (.const 1)).eval w z1 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 2) (by simp [z1, e7])) (Expr.eval_const (by omega)) (by omega) (by omega)
          have hrid_par : (S.splay.nodes rid).par = 0 := htv_inv.sub.2.2.2.1
          have hz1_9 : z1.regs 9 = nb + 8 * rid := by simp [z1]
          have ha10E : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 2)))) z1 .normal
              { z1 with regs := Function.update z1.regs 10 0 } _ :=
            runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hz1_9)
              (Expr.eval_const (by omega)) (by omega)) (by rw [← hrid_par]; simpa [ordNodeAddr] using (hnE rid hrid_c).2.2.1), rfl, rfl, rfl⟩
          set z2 : State := { z1 with regs := Function.update z1.regs 10 0 }
          have hc10E : (Expr.bin .eq (.reg 10) (.const 0)).eval w z2 = some 1 :=
            Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [z2])) (Expr.eval_const (by omega)) rfl (by omega)
          have ha5E : Runs w p ω (.assign 5 (.const 0)) z2 .normal { z2 with regs := Function.update z2.regs 5 0 } _ :=
            runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
          set z3 : State := { z2 with regs := Function.update z2.regs 5 0 }
          have hexit : Runs w p ω ordListLoop z3 .normal z3 _ :=
            ord_runs_loop_false (Expr.eval_reg_of_eq (v := 0) (by simp [z3]))
          refine ⟨z3, _, ord_runs_loop_true hc5E hrid_nz (ord_runs_seq_normal ha9E (ord_runs_cond_false hc7E0
            (ord_runs_cond_false hc7E1 (ord_runs_seq_normal ha10E (ord_runs_cond_true hc10E Nat.one_ne_zero ha5E))))) hexit,
            ⟨by simp [z3, z2, z1, e2],
             by simp only [z3, z2, z1, Function.update_of_ne (by decide : (6 : ℕ) ≠ 5), Function.update_of_ne (by decide : (6 : ℕ) ≠ 10),
                  Function.update_of_ne (by decide : (6 : ℕ) ≠ 9)]
                rw [sregE 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [st7, st6, st5, st4],
             ⟨by dsimp only [z3, z2, z1]; rw [eout heap (by omega)]; simp [st7, st6, st5],
              fun i hi => by
                dsimp only [z3, z2, z1]
                have hi_c : i < (AuxTree.node rid l r).countNodes := by rw [← htv, hlen_eq]; exact hi
                have hm_i := emem i hi_c
                rw [show heap + 1 + (0 + i) = heap + 1 + i by omega] at hm_i
                rw [hm_i]
                have hle_eq := hinv.list_eq v hv
                rw [htv] at hle_eq
                have hgd : (ord v).getD i (0, true) = endOfKey (S.splay.nodes ((AuxTree.node rid l r).toList.getD i 0)).val := by
                  rw [← hle_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
                    List.getElem?_eq_getElem (by rw [AuxTree.length_toList]; exact hi_c), Option.map_some, Option.getD_some,
                    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [AuxTree.length_toList]; exact hi_c), Option.getD_some]
                rw [hgd, endKey_endOfKey]⟩,
             fun a ha => by
               dsimp only [z3, z2, z1]
               rw [eout a (by rw [← htv, hlen_eq]; omega)]; dsimp only [st7, st6, st5]
               rw [Function.update_of_ne (by omega)]; exact hz a (by omega),
             fun a ha => by
               dsimp only [z3, z2, z1]
               rw [eout a (by omega)]; dsimp only [st7, st6, st5]; exact Function.update_of_ne (by omega) _ _⟩, ?_⟩
          simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
          omega)
    have hret : Runs w p ω (.ret (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 6))) stF
        (.returned (heap + 1 + (ord v).length)) stF _ :=
      runs_ret_iff.mpr ⟨heap + 1 + (ord v).length,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hQF.1) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq hQF.2.1) (by omega), rfl, rfl, rfl⟩
    refine ⟨.returned (heap + 1 + (ord v).length), stF, _,
      ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_seq_normal ha5
        (ord_runs_cond_false hc (ord_runs_seq_normal ha6 (ord_runs_seq_normal hs_len
          (ord_runs_seq_normal ha7 (ord_runs_seq_normal ha8 (ord_runs_seq_normal hrunL hret)))))))),
      rfl,
      harena.congr hinv.next_le (fun a ha => hQF.2.2.2.2 a (by unfold ordFoot at ha; omega)),
      hQF.2.2.1, hQF.2.2.2.1, hQF.2.2.2.2, ?_⟩
    rw [← htv, hlen_eq] at hcL
    unfold ORD_LIST_MUL; simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega


end MinCostFlow.SparseCore.Program
