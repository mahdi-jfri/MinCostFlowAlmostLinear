module

public import MinCostFlow.SparseCore.Program.OrdStoreInsertBack
import Mathlib.Tactic

/-!
# Order Store `insertBefore` Helpers: Direct Splice

This file verifies `insertSplice_runs`, which allocates a fresh node `nx` via `ordAlloc` and
splices it directly before a splayed root `uy` in vertex `v`'s tree.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-- Execution half of the direct splice: links `nx` between `L` and `uy` in memory. -/
private theorem insertSplice_exec
    {w b v keyX uy nb : ℕ} {p : Program} (ω : ℕ → Bool)
    {st1 : State} {S2 : OrdStoreState} {L R : AuxTree} {nx : ℕ}
    (hnb : nb = ordNodesBase b S2.vCap S2.eCap)
    (hvr2 : st1.mem (b + 2) = ordVRootBase b)
    (hn2 : OrdNodesAt st1.mem nb S2.nextNode S2.splay S2.nextFree)
    (hv : v < S2.vCap) (hnx_nn : nx ≤ S2.nextNode) (huy_c2 : uy ≤ S2.nextNode)
    (hL_c2 : L.rootId ≤ S2.nextNode)
    (hnx_ne_uy : nx ≠ uy) (hnx_ne_L : nx ≠ L.rootId) (huy_ne_L : uy ≠ L.rootId)
    (huyL : (S2.splay.nodes uy).left = L.rootId)
    (huysz : (S2.splay.nodes uy).sz = (AuxTree.node uy L R).countNodes)
    (hLsz : (S2.splay.nodes L.rootId).sz = L.countNodes)
    (hcnt_le2 : (AuxTree.node uy L R).countNodes + 1 ≤ S2.nextNode)
    (hr0 : st1.regs 0 = b) (hr1 : st1.regs 1 = v) (hr4 : st1.regs 4 = nx)
    (hr5 : st1.regs 5 = nb) (hr10 : st1.regs 10 = uy) (hr11 : st1.regs 11 = v + 1)
    (hnb_w : nb + 8 * (S2.nextNode + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ st' c m9 spF,
      Runs w p ω
        (.assign 12 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 4))) ;;
         .assign 13 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 10))) ;;
         .assign 14 (.load (.reg 13)) ;;
         .store (.reg 12) (.reg 14) ;;
         .cond (.reg 14)
           (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4))
           .nop ;;
         .store (.bin .add (.reg 12) (.const 1)) (.reg 10) ;;
         .store (.bin .add (.reg 12) (.const 3)) (.reg 11) ;;
         .assign 15 (.load (.bin .add (.reg 13) (.const 4))) ;;
         .store (.bin .add (.reg 12) (.const 4)) (.bin .add (.reg 15) (.const 1)) ;;
         .store (.reg 13) (.const 0) ;;
         .store (.bin .add (.reg 13) (.const 2)) (.reg 4) ;;
         .store (.bin .add (.reg 13) (.const 3)) (.const 0) ;;
         .assign 16 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 4))) ;;
         .store (.bin .add (.reg 13) (.const 4)) (.bin .sub (.reg 15) (.reg 16)) ;;
         .assign 17 (.load (.bin .add (.reg 0) (.const 2))) ;;
         .store (.bin .add (.reg 17) (.reg 1)) (.reg 4) ;;
         .assign 7 (.const 1)) st1 .normal st' c ∧
      st'.regs 7 = 1 ∧
      st'.mem = Function.update m9 (ordVRootBase b + v) nx ∧
      OrdNodesAt m9 nb S2.nextNode spF S2.nextFree ∧
      (∀ a, ¬ InOrdNodes nb S2.nextNode a → m9 a = st1.mem a) ∧
      (∀ x, x ≠ nx → x ≠ uy → x ≠ L.rootId → spF.nodes x = S2.splay.nodes x) ∧
      spF.nodes nx =
        { (S2.splay.nodes nx) with
          left := L.rootId
          right := uy
          ppar := v + 1
          sz := (AuxTree.node uy L R).countNodes + 1 } ∧
      spF.nodes uy =
        { (S2.splay.nodes uy) with
          left := 0
          par := nx
          ppar := 0
          sz := (AuxTree.node uy .leaf R).countNodes } ∧
      (L.rootId ≠ 0 → spF.nodes L.rootId = { (S2.splay.nodes L.rootId) with par := nx }) ∧
      (L.rootId = 0 → spF.nodes 0 = S2.splay.nodes 0) ∧
      c ≤ 260 := by
  have hb_w : b + 2 < 2 ^ w := by rw [hnb] at hnb_w; unfold ordNodesBase at hnb_w; omega
  have hvr_w : ordVRootBase b + v < 2 ^ w := by rw [hnb] at hnb_w; unfold ordNodesBase at hnb_w; unfold ordVRootBase; omega
  have hsub_cnt : (AuxTree.node uy L R).countNodes - L.countNodes = (AuxTree.node uy .leaf R).countNodes := by
    simp [AuxTree.countNodes]; omega
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 4)))) st1 .normal
      { st1 with regs := Function.update st1.regs 12 (nb + 8 * nx) } _ :=
    runs_assign_iff.mpr ⟨nb + 8 * nx, Expr.eval_add (Expr.eval_reg_of_eq hr5)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr4) (by omega)) (by omega), rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 12 (nb + 8 * nx) }
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 10)))) st2 .normal
      { st2 with regs := Function.update st2.regs 13 (nb + 8 * uy) } _ :=
    runs_assign_iff.mpr ⟨nb + 8 * uy, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, hr5]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st2, hr10])) (by omega)) (by omega), rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 13 (nb + 8 * uy) }
  have hm_uyL : st1.mem (nb + 8 * uy) = L.rootId := by
    simpa [ordNodeAddr, huyL] using (hn2 uy huy_c2).1
  have ha14 : Runs w p ω (.assign 14 (.load (.reg 13))) st3 .normal
      { st3 with regs := Function.update st3.regs 14 L.rootId } _ :=
    runs_assign_iff.mpr ⟨L.rootId, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st3])) hm_uyL, rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 14 L.rootId }
  have hs1 : Runs w p ω (.store (.reg 12) (.reg 14)) st4 .normal
      { st4 with mem := Function.update st1.mem (nb + 8 * nx) L.rootId } _ :=
    runs_store_iff.mpr ⟨nb + 8 * nx, L.rootId, Expr.eval_reg_of_eq (by simp [st4, st3, st2]),
      Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
  set m1 := Function.update st1.mem (nb + 8 * nx) L.rootId
  set st5 : State := { st4 with mem := m1 }
  obtain ⟨spA, hspA⟩ : ∃ s, s = S2.splay.setLeft nx L.rootId := ⟨_, rfl⟩
  have hnA : OrdNodesAt m1 nb S2.nextNode spA S2.nextFree := by
    rw [hspA]; simpa [ordNodeAddr] using hn2.setLeft hnx_nn (v := L.rootId)
  obtain ⟨spB, hspB⟩ : ∃ s, s = (if L.rootId = 0 then spA else spA.setPar L.rootId nx) := ⟨_, rfl⟩
  have hcondL : ∃ m2 cL,
      Runs w p ω (.cond (.reg 14)
        (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4)) .nop)
        st5 .normal { st5 with mem := m2 } cL ∧
      OrdNodesAt m2 nb S2.nextNode spB S2.nextFree ∧
      (∀ a, ¬ InOrdNodes nb S2.nextNode a → m2 a = m1 a) ∧ cL ≤ 30 := by
    by_cases hL0 : L.rootId = 0
    · have hc : (Expr.reg 14).eval w st5 = some 0 := Expr.eval_reg_of_eq (by simp [st5, st4, hL0])
      refine ⟨m1, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        by rw [hspB]; simpa [hL0] using hnA, fun _ _ => rfl, by simp [Expr.size_reg]⟩
    · have hc : (Expr.reg 14).eval w st5 = some L.rootId := Expr.eval_reg_of_eq (by simp [st5, st4])
      have hst : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4))
          st5 .normal { st5 with mem := Function.update m1 (nb + 8 * L.rootId + 2) nx } _ :=
        runs_store_iff.mpr ⟨nb + 8 * L.rootId + 2, nx,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, hr5]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st5, st4])) (by omega)) (by omega))
            (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, hr4]), rfl, rfl, rfl⟩
      refine ⟨_, _, ord_runs_cond_true hc hL0 hst,
        by rw [hspB]; simp only [hL0, ite_false]; exact hnA.setPar hL_c2 (v := nx),
        fun a ha => Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _,
        by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
  obtain ⟨m2, cL, hrunL, hnB, hfrB, hcL⟩ := hcondL
  set st6 : State := { st5 with mem := m2 }
  have hs2 : Runs w p ω (.store (.bin .add (.reg 12) (.const 1)) (.reg 10)) st6 .normal
      { st6 with mem := Function.update m2 (nb + 8 * nx + 1) uy } _ :=
    runs_store_iff.mpr ⟨nb + 8 * nx + 1, uy, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2, hr10]), rfl, rfl, rfl⟩
  set m3 := Function.update m2 (nb + 8 * nx + 1) uy
  set st7 : State := { st6 with mem := m3 }
  have hs3 : Runs w p ω (.store (.bin .add (.reg 12) (.const 3)) (.reg 11)) st7 .normal
      { st7 with mem := Function.update m3 (nb + 8 * nx + 3) (v + 1) } _ :=
    runs_store_iff.mpr ⟨nb + 8 * nx + 3, v + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3, st2, hr11]), rfl, rfl, rfl⟩
  set m4 := Function.update m3 (nb + 8 * nx + 3) (v + 1)
  set st8 : State := { st7 with mem := m4 }
  obtain ⟨spC, hspC⟩ : ∃ s, s = (spB.setRight nx uy).setPpar nx (v + 1) := ⟨_, rfl⟩
  have hnC : OrdNodesAt m4 nb S2.nextNode spC S2.nextFree := by
    rw [hspC]; exact (hnB.setRight hnx_nn (v := uy)).setPpar hnx_nn (v := v + 1)
  have hspC_uysz : (spC.nodes uy).sz = (AuxTree.node uy L R).countNodes := by
    rw [hspC, hspB, hspA]
    split_ifs <;> simp [SplayState.setPpar, SplayState.setRight, SplayState.setPar, SplayState.setLeft,
      Ne.symm hnx_ne_uy, huy_ne_L, huysz]
  have hm4_uysz : m4 (nb + 8 * uy + 4) = (AuxTree.node uy L R).countNodes := by
    rw [← hspC_uysz]; simpa [ordNodeAddr] using (hnC uy huy_c2).2.2.2.2.1
  have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 13) (.const 4)))) st8 .normal
      { st8 with regs := Function.update st8.regs 15 (AuxTree.node uy L R).countNodes } _ :=
    runs_assign_iff.mpr ⟨(AuxTree.node uy L R).countNodes, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st8, st7, st6, st5, st4, st3])) (Expr.eval_const (by omega)) (by omega))
      hm4_uysz, rfl, rfl, rfl⟩
  set st9 : State := { st8 with regs := Function.update st8.regs 15 (AuxTree.node uy L R).countNodes }
  have hs4 : Runs w p ω (.store (.bin .add (.reg 12) (.const 4)) (.bin .add (.reg 15) (.const 1))) st9 .normal
      { st9 with mem := Function.update m4 (nb + 8 * nx + 4) ((AuxTree.node uy L R).countNodes + 1) } _ :=
    runs_store_iff.mpr ⟨nb + 8 * nx + 4, (AuxTree.node uy L R).countNodes + 1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st9, st8, st7, st6, st5, st4, st3, st2])) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st9])) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set m5 := Function.update m4 (nb + 8 * nx + 4) ((AuxTree.node uy L R).countNodes + 1)
  set st10 : State := { st9 with mem := m5 }
  have hs5 : Runs w p ω (.store (.reg 13) (.const 0)) st10 .normal
      { st10 with mem := Function.update m5 (nb + 8 * uy) 0 } _ :=
    runs_store_iff.mpr ⟨nb + 8 * uy, 0, Expr.eval_reg_of_eq (by simp [st10, st9, st8, st7, st6, st5, st4, st3]),
      Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set m6 := Function.update m5 (nb + 8 * uy) 0
  set st11 : State := { st10 with mem := m6 }
  have hs6 : Runs w p ω (.store (.bin .add (.reg 13) (.const 2)) (.reg 4)) st11 .normal
      { st11 with mem := Function.update m6 (nb + 8 * uy + 2) nx } _ :=
    runs_store_iff.mpr ⟨nb + 8 * uy + 2, nx, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st11, st10, st9, st8, st7, st6, st5, st4, st3]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hr4]), rfl, rfl, rfl⟩
  set m7 := Function.update m6 (nb + 8 * uy + 2) nx
  set st12 : State := { st11 with mem := m7 }
  have hs7 : Runs w p ω (.store (.bin .add (.reg 13) (.const 3)) (.const 0)) st12 .normal
      { st12 with mem := Function.update m7 (nb + 8 * uy + 3) 0 } _ :=
    runs_store_iff.mpr ⟨nb + 8 * uy + 3, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set m8 := Function.update m7 (nb + 8 * uy + 3) 0
  set st13 : State := { st12 with mem := m8 }
  obtain ⟨spD, hspD⟩ : ∃ s, s = ((((spC.updateNode nx fun nd => { nd with sz := (AuxTree.node uy L R).countNodes + 1 }).setLeft uy 0).setPar uy nx).setPpar uy 0) := ⟨_, rfl⟩
  have hnD : OrdNodesAt m8 nb S2.nextNode spD S2.nextFree := by
    rw [hspD]
    have h1 := hnC.setSz hnx_nn (v := (AuxTree.node uy L R).countNodes + 1)
    have h2 : OrdNodesAt m6 nb S2.nextNode ((spC.updateNode nx fun nd => { nd with sz := (AuxTree.node uy L R).countNodes + 1 }).setLeft uy 0) S2.nextFree := by
      simpa [ordNodeAddr] using h1.setLeft huy_c2 (v := 0)
    exact (h2.setPar huy_c2 (v := nx)).setPpar huy_c2 (v := 0)
  have hspD_Lsz : (spD.nodes L.rootId).sz = L.countNodes := by
    rw [hspD, hspC, hspB, hspA]
    split_ifs <;> simp [SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight,
      Ne.symm hnx_ne_L, Ne.symm huy_ne_L, hLsz]
  have hm8_Lsz : m8 (nb + 8 * L.rootId + 4) = L.countNodes := by
    rw [← hspD_Lsz]; simpa [ordNodeAddr] using (hnD L.rootId hL_c2).2.2.2.2.1
  have ha16 : Runs w p ω (.assign 16 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 4)))) st13 .normal
      { st13 with regs := Function.update st13.regs 16 L.countNodes } _ :=
    runs_assign_iff.mpr ⟨L.countNodes, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hr5]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st9, st8, st7, st6, st5, st4])) (by omega)) (by omega))
      (Expr.eval_const (by omega)) (by omega)) hm8_Lsz, rfl, rfl, rfl⟩
  set st14 : State := { st13 with regs := Function.update st13.regs 16 L.countNodes }
  have hs8 : Runs w p ω (.store (.bin .add (.reg 13) (.const 4)) (.bin .sub (.reg 15) (.reg 16))) st14 .normal
      { st14 with mem := Function.update m8 (nb + 8 * uy + 4) ((AuxTree.node uy L R).countNodes - L.countNodes) } _ :=
    runs_store_iff.mpr ⟨nb + 8 * uy + 4, (AuxTree.node uy L R).countNodes - L.countNodes,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3])) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_sub (Expr.eval_reg_of_eq (v := (AuxTree.node uy L R).countNodes) (by simp [st14, st13, st12, st11, st10, st9]))
        (Expr.eval_reg_of_eq (v := L.countNodes) (by simp [st14])) (by omega), rfl, rfl, rfl⟩
  set m9 := Function.update m8 (nb + 8 * uy + 4) ((AuxTree.node uy L R).countNodes - L.countNodes)
  set st15 : State := { st14 with mem := m9 }
  obtain ⟨spF, hspF⟩ : ∃ s, s = spD.updateNode uy fun nd => { nd with sz := (AuxTree.node uy L R).countNodes - L.countNodes } := ⟨_, rfl⟩
  have hnF : OrdNodesAt m9 nb S2.nextNode spF S2.nextFree := by rw [hspF]; exact hnD.setSz huy_c2
  have hm9_out : ∀ a, ¬ InOrdNodes nb S2.nextNode a → m9 a = st1.mem a := fun a ha => by
    dsimp only [m9, m8, m7, m6, m5, m4, m3]
    repeat (rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)])
    rw [hfrB a ha]; dsimp only [m1]
    rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
  have hm9_vr : m9 (b + 2) = ordVRootBase b :=
    (hm9_out (b + 2) (fun h => by unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega)).trans hvr2
  have ha17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 0) (.const 2)))) st15 .normal
      { st15 with regs := Function.update st15.regs 17 (ordVRootBase b) } _ :=
    runs_assign_iff.mpr ⟨ordVRootBase b, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := b) (by simp [st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hr0]))
      (Expr.eval_const (by omega)) (by omega)) hm9_vr, rfl, rfl, rfl⟩
  set st16 : State := { st15 with regs := Function.update st15.regs 17 (ordVRootBase b) }
  have hs9 : Runs w p ω (.store (.bin .add (.reg 17) (.reg 1)) (.reg 4)) st16 .normal
      { st16 with mem := Function.update m9 (ordVRootBase b + v) nx } _ :=
    runs_store_iff.mpr ⟨ordVRootBase b + v, nx,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st16]))
        (Expr.eval_reg_of_eq (by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hr1]))
        hvr_w,
      Expr.eval_reg_of_eq (by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hr4]),
      rfl, rfl, rfl⟩
  set st17 : State := { st16 with mem := Function.update m9 (ordVRootBase b + v) nx }
  have ha7 : Runs w p ω (.assign 7 (.const 1)) st17 .normal
      { st17 with regs := Function.update st17.regs 7 1 } _ :=
    runs_assign_iff.mpr ⟨1, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  refine ⟨{ st17 with regs := Function.update st17.regs 7 1 }, _, m9, spF,
    ord_runs_seq_normal ha12 (ord_runs_seq_normal ha13 (ord_runs_seq_normal ha14
      (ord_runs_seq_normal hs1 (ord_runs_seq_normal hrunL (ord_runs_seq_normal hs2
        (ord_runs_seq_normal hs3 (ord_runs_seq_normal ha15 (ord_runs_seq_normal hs4
          (ord_runs_seq_normal hs5 (ord_runs_seq_normal hs6 (ord_runs_seq_normal hs7
            (ord_runs_seq_normal ha16 (ord_runs_seq_normal hs8
              (ord_runs_seq_normal ha17 (ord_runs_seq_normal hs9 ha7))))))))))))))),
    by simp, rfl, hnF, hm9_out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2 h3
    rw [hspF, hspD, hspC, hspB, hspA]
    split_ifs <;> simp [SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight, h1, h2, h3]
  · rw [hspF, hspD, hspC, hspB, hspA]
    split_ifs <;> simp [SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight, hnx_ne_uy, hnx_ne_L]
  · rw [hspF, hspD, hspC, hspB, hspA, hsub_cnt]
    split_ifs <;> simp [SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight, Ne.symm hnx_ne_uy, huy_ne_L]
  · intro hL0
    rw [hspF, hspD, hspC, hspB, hspA]
    simp [hL0, SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight, Ne.symm hnx_ne_L, Ne.symm huy_ne_L]
  · intro hL0
    have h0_nx : (0 : ℕ) ≠ nx := by rw [← hL0]; exact Ne.symm hnx_ne_L
    have h0_uy : (0 : ℕ) ≠ uy := by rw [← hL0]; exact Ne.symm huy_ne_L
    rw [hspF, hspD, hspC, hspB, hspA]
    simp [hL0, SplayState.setPpar, SplayState.setPar, SplayState.setLeft, SplayState.setRight, h0_nx, h0_uy]
  · simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- Invariant preservation for the direct splice: splicing `nx` before root `uy` preserves `OrdInv`. -/
private theorem insertSplice_inv
    {v keyX keyY uy nx : ℕ} {ord : ℕ → List End} {S1 S2 : OrdStoreState}
    {L R : AuxTree} {spF : SplayState ℕ Unit Unit}
    (hinv1 : OrdInv ord S1) (hv : v < S1.vCap) (hkX : keyX < 2 * S1.eCap)
    (htv_eq : S1.trees v = .node uy L R) (huy_mem : uy ∈ (S1.trees v).toList)
    (huy_val : (S1.splay.nodes uy).val = keyY)
    (huniq' : OrdUniqueWithin S1.vCap S1.eCap
      (applyOrdEdit ord (.insertBefore v (endOfKey keyX) (some (endOfKey keyY)))))
    (hnx1 : 1 ≤ nx) (hnx_nn : nx ≤ S2.nextNode) (hnn_ge : S1.nextNode ≤ S2.nextNode)
    (hnn_le : S2.nextNode ≤ 2 * S1.eCap) (hv2 : S2.vCap = S1.vCap) (he2 : S2.eCap = S1.eCap)
    (hen2 : S2.eNode = Function.update S1.eNode keyX nx)
    (hnx_nlive : ∀ w < S1.vCap, nx ∉ (S1.trees w).toList)
    (hnx_nfl : nx ∉ S2.freeList) (hflnd2 : S2.freeList.Nodup)
    (hfc2 : FreeChain S2.freeHead S2.nextFree S2.freeList)
    (hfl_le2 : ∀ x ∈ S2.freeList, 1 ≤ x ∧ x ≤ S2.nextNode)
    (hlive_fl2 : ∀ w < S1.vCap, ∀ x ∈ (S1.trees w).toList, x ∉ S2.freeList)
    (hpart2 : ∀ x, 1 ≤ x → x ≤ S2.nextNode →
      x = nx ∨ (∃ w < S1.vCap, x ∈ (S1.trees w).toList) ∨ x ∈ S2.freeList)
    (hspF_out : ∀ x, x ≠ nx → x ≠ uy → x ≠ L.rootId → spF.nodes x = S1.splay.nodes x)
    (hspF_nx : spF.nodes nx =
      { (ordFreshNode keyX) with left := L.rootId, right := uy, ppar := v + 1, sz := (AuxTree.node uy L R).countNodes + 1 })
    (hspF_uy : spF.nodes uy =
      { (S1.splay.nodes uy) with left := 0, par := nx, ppar := 0, sz := (AuxTree.node uy .leaf R).countNodes })
    (hspF_L : L.rootId ≠ 0 → spF.nodes L.rootId = { (S1.splay.nodes L.rootId) with par := nx })
    (hspF_0 : spF.nodes 0 = ordNullNode) :
    OrdInv (applyOrdEdit ord (.insertBefore v (endOfKey keyX) (some (endOfKey keyY))))
      { S2 with
        splay := spF
        vRoot := Function.update S1.vRoot v nx
        trees := Function.update S1.trees v (.node nx L (.node uy .leaf R)) } := by
  have htv_inv : TreeInv ordPayload S1.splay (.node uy L R) := htv_eq ▸ hinv1.tree_inv v hv
  rcases htv_inv.sub with ⟨huy_nz, -, huyR, -, -, -, -, hsubL, hsubR⟩
  rcases AuxTree.nodup_node_unfold htv_inv.nodup with ⟨hLnd, huy_nL, hRnd, huy_nR, hLR_disj⟩
  have hnx_ne_uy : nx ≠ uy := fun h => hnx_nlive v hv (h ▸ huy_mem)
  have hnx_nL : nx ∉ L.toList := fun h => hnx_nlive v hv (by rw [htv_eq]; exact List.mem_append_left _ (List.mem_append_left _ h))
  have hnx_nR : nx ∉ R.toList := fun h => hnx_nlive v hv (by rw [htv_eq]; exact List.mem_append_right _ h)
  have hspF_val : ∀ x, x ≠ nx → (spF.nodes x).val = (S1.splay.nodes x).val := fun x h1 => by
    by_cases h2 : x = uy
    · rw [h2, hspF_uy]
    · by_cases h3 : x = L.rootId
      · by_cases hL0 : L.rootId = 0
        · rw [h3, hL0, hspF_0, hinv1.null_node]
        · rw [h3, hspF_L hL0]
      · rw [hspF_out x h1 h2 h3]
  let t' : AuxTree := .node nx L (.node uy .leaf R)
  have hsubL' : SplayState.SubtreeInv ordPayload spF nx L := by
    cases L with
    | leaf => trivial
    | node lid ll lr =>
      rcases hsubL with ⟨hlid_nz, hll, hlr, -, hlpp, hlsz, -, hsubll, hsublr⟩
      rcases AuxTree.nodup_node_unfold hLnd with ⟨_, hlid_nll, _, hlid_nlr, _⟩
      have hnd_L := hspF_L (by simp [AuxTree.rootId]; exact hlid_nz)
      simp only [AuxTree.rootId] at hnd_L
      refine ⟨hlid_nz, by rw [hnd_L]; exact hll, by rw [hnd_L]; exact hlr,
        by rw [hnd_L], fun _ => by rw [hnd_L]; exact hlpp huy_nz, by rw [hnd_L]; exact hlsz, rfl,
        SplayState.SubtreeInv_agree hsubll fun x hx => (hspF_out x
          (fun h => hnx_nL (by rw [← h]; exact List.mem_append_left _ (List.mem_append_left _ hx)))
          (fun h => huy_nL (by rw [← h]; exact List.mem_append_left _ (List.mem_append_left _ hx)))
          (fun h => hlid_nll (by simp only [AuxTree.rootId] at h; rw [← h]; exact hx))).symm,
        SplayState.SubtreeInv_agree hsublr fun x hx => (hspF_out x
          (fun h => hnx_nL (by rw [← h]; exact List.mem_append_right _ hx))
          (fun h => huy_nL (by rw [← h]; exact List.mem_append_right _ hx))
          (fun h => hlid_nlr (by simp only [AuxTree.rootId] at h; rw [← h]; exact hx))).symm⟩
  have hsubR' : SplayState.SubtreeInv ordPayload spF uy R :=
    SplayState.SubtreeInv_agree hsubR fun x hx => (hspF_out x (fun h => hnx_nR (by rw [← h]; exact hx))
      (fun h => huy_nR (by rw [← h]; exact hx)) (fun h => by
        cases L with
        | leaf => simp [AuxTree.rootId] at h; exact SplayState.SubtreeInv_nonZero hsubR hx h
        | node lid ll lr =>
          simp only [AuxTree.rootId] at h
          exact hLR_disj lid (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)) (by rw [← h]; exact hx))).symm
  have ht'_inv : TreeInv ordPayload spF t' :=
    ⟨by
      simp only [t', AuxTree.toList, List.nil_append, List.singleton_append, List.append_assoc]
      rw [List.nodup_append, List.nodup_cons, List.nodup_cons]
      refine ⟨hLnd, ⟨by simp [hnx_ne_uy, hnx_nR], huy_nR, hRnd⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hbr
      · exact fun h => hnx_nL (by rw [← h]; exact ha)
      · exact fun h => huy_nL (by rw [← h]; exact ha)
      · exact fun h => hLR_disj a ha (by rw [h]; exact hbr),
     ⟨by omega, by rw [hspF_nx], by rw [hspF_nx]; rfl, by rw [hspF_nx]; rfl, fun h => absurd rfl h,
      by rw [hspF_nx]; simp [AuxTree.countNodes]; omega, rfl, hsubL',
      ⟨huy_nz, by rw [hspF_uy]; rfl, by rw [hspF_uy]; exact huyR, by rw [hspF_uy],
       fun _ => by rw [hspF_uy], by rw [hspF_uy], rfl, trivial, hsubR'⟩⟩⟩
  have ht'_list : t'.toList = L.toList ++ [nx, uy] ++ R.toList := by
    simp [t', AuxTree.toList, List.append_assoc]
  have hlist_v' : t'.toList.map (fun x => endOfKey (spF.nodes x).val) =
      insertBeforeList (endOfKey keyX) (some (endOfKey keyY)) (ord v) := by
    have hord_v : ord v = L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) ++
        [endOfKey keyY] ++ R.toList.map (fun x => endOfKey (S1.splay.nodes x).val) := by
      rw [← hinv1.list_eq v hv, htv_eq]; simp [AuxTree.toList, huy_val]
    have hidx : (ord v).idxOf (endOfKey keyY) = L.toList.length := by
      have hnd := hinv1.ord_unique.nodup v
      rw [hord_v, List.append_assoc, List.singleton_append] at hnd ⊢
      have hnm : endOfKey keyY ∉ L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) := fun h =>
        (List.nodup_append.mp hnd).2.2 _ h _ List.mem_cons_self rfl
      rw [idxOf_append_cons_of_not_mem hnm, List.length_map]
    have hlen : (L.toList.map fun x => endOfKey (S1.splay.nodes x).val).length = L.toList.length := List.length_map _
    simp only [insertBeforeList, hidx]
    rw [hord_v, List.append_assoc, List.singleton_append,
        List.take_append_of_le_length (le_of_eq hlen.symm), List.drop_append_of_le_length (le_of_eq hlen.symm),
        ← hlen, List.take_length, List.drop_length, List.nil_append,
        ht'_list, List.map_append, List.map_append]
    have hLmap : L.toList.map (fun x => endOfKey (spF.nodes x).val) =
        L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) :=
      List.map_congr_left fun x hx => by rw [hspF_val x (fun h => hnx_nL (by rw [← h]; exact hx))]
    have hRmap : R.toList.map (fun x => endOfKey (spF.nodes x).val) =
        R.toList.map (fun x => endOfKey (S1.splay.nodes x).val) :=
      List.map_congr_left fun x hx => by rw [hspF_val x (fun h => hnx_nR (by rw [← h]; exact hx))]
    rw [hLmap, hRmap]
    simp only [List.map_cons, List.map_nil, hspF_nx, hspF_uy, ordFreshNode, huy_val,
      List.append_assoc, List.cons_append, List.nil_append]
  have ht'_mem_iff : ∀ x, x ∈ t'.toList ↔ x = nx ∨ x ∈ (S1.trees v).toList := fun x => by
    rw [ht'_list, htv_eq]; simp [AuxTree.toList]; tauto
  exact
    { ord_unique := by dsimp only; rw [hv2, he2]; exact huniq'
      next_le := by dsimp only; rw [he2]; exact hnn_le
      clean := fun x => by
        by_cases h1 : x = nx
        · rw [h1, hspF_nx]; rfl
        · by_cases h2 : x = uy
          · rw [h2, hspF_uy]; exact hinv1.clean uy
          · by_cases h3 : x = L.rootId
            · by_cases hL0 : L.rootId = 0
              · rw [h3, hL0, hspF_0]; rfl
              · rw [h3, hspF_L hL0]; exact hinv1.clean L.rootId
            · rw [hspF_out x h1 h2 h3]; exact hinv1.clean x
      null_node := hspF_0
      tree_inv := fun u hu => by
        dsimp only at hu ⊢; rw [hv2] at hu
        by_cases h : u = v
        · subst h; simpa using ht'_inv
        · simp only [Function.update_of_ne h]
          exact ⟨(hinv1.tree_inv u hu).nodup, SplayState.SubtreeInv_agree (hinv1.tree_inv u hu).sub fun x hx =>
            (hspF_out x (fun he => hnx_nlive u hu (by rw [← he]; exact hx))
              (fun he => hinv1.disj_trees u v h x hx (by rw [he]; exact huy_mem))
              (fun he => by
                cases L with
                | leaf => simp [AuxTree.rootId] at he; exact SplayState.SubtreeInv_nonZero (hinv1.tree_inv u hu).sub hx he
                | node lid ll lr =>
                  simp only [AuxTree.rootId] at he
                  exact hinv1.disj_trees u v h x hx (by rw [htv_eq, he]; exact List.mem_append_left _ (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)))))).symm⟩
      tree_out := fun u hu => by
        dsimp only at hu ⊢; rw [hv2] at hu
        rw [Function.update_of_ne (by omega)]; exact hinv1.tree_out u hu
      vRoot_eq := fun u hu => by
        dsimp only at hu ⊢; rw [hv2] at hu
        by_cases h : u = v <;> simp [h, AuxTree.rootId, hinv1.vRoot_eq u hu]
      root_ppar := fun u hu hne => by
        dsimp only at hu hne ⊢; rw [hv2] at hu
        by_cases h : u = v
        · subst h; simp only [Function.update_self, AuxTree.rootId, hspF_nx]
        · simp only [Function.update_of_ne h] at hne ⊢
          have hr := AuxTree.rootId_mem hne
          rw [hspF_out _ (fun he => hnx_nlive u hu (by rw [← he]; exact hr))
            (fun he => hinv1.disj_trees u v h _ hr (by rw [he]; exact huy_mem))
            (fun he => by
              cases L with
              | leaf => simp [AuxTree.rootId] at he; exact SplayState.SubtreeInv_nonZero (hinv1.tree_inv u hu).sub hr he
              | node lid ll lr =>
                change (S1.trees u).rootId = lid at he
                exact hinv1.disj_trees u v h (S1.trees u).rootId hr (by
                  rw [htv_eq, he]
                  exact List.mem_append_left _
                    (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)))))]
          exact hinv1.root_ppar u hu hne
      list_eq := fun u hu => by
        dsimp only [applyOrdEdit] at hu ⊢; rw [hv2] at hu
        by_cases h : u = v
        · subst h; simpa using hlist_v'
        · simp only [Function.update_of_ne h]
          rw [← hinv1.list_eq u hu]
          exact List.map_congr_left fun x hx => by rw [hspF_val x (fun he => hnx_nlive u hu (by rw [← he]; exact hx))]
      disj_trees := fun u1 u2 hne x h1 h2 => by
        dsimp only at h1 h2
        by_cases h1v : u1 = v
        · subst h1v; simp only [Function.update_self] at h1; rw [ht'_mem_iff] at h1
          simp only [Function.update_of_ne (Ne.symm hne)] at h2
          rcases h1 with rfl | htv
          · by_cases hu2 : u2 < S1.vCap
            · exact hnx_nlive u2 hu2 h2
            · rw [hinv1.tree_out u2 (by omega)] at h2; exact List.not_mem_nil h2
          · exact hinv1.disj_trees u1 u2 hne x htv h2
        · by_cases h2v : u2 = v
          · subst h2v; simp only [Function.update_of_ne h1v] at h1
            simp only [Function.update_self] at h2; rw [ht'_mem_iff] at h2
            rcases h2 with rfl | htv
            · by_cases hu1 : u1 < S1.vCap
              · exact hnx_nlive u1 hu1 h1
              · rw [hinv1.tree_out u1 (by omega)] at h1; exact List.not_mem_nil h1
            · exact hinv1.disj_trees u1 u2 h1v x h1 htv
          · simp only [Function.update_of_ne h1v] at h1; simp only [Function.update_of_ne h2v] at h2
            exact hinv1.disj_trees u1 u2 hne x h1 h2
      free_nodup := hflnd2
      free_disj := fun u hu x hxf hxt => by
        dsimp only at hu hxt; rw [hv2] at hu
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hxt; rw [ht'_mem_iff] at hxt
          rcases hxt with rfl | htv
          · exact hnx_nfl hxf
          · exact hlive_fl2 u hv x htv hxf
        · simp only [Function.update_of_ne h] at hxt; exact hlive_fl2 u hu x hxt hxf
      free_chain := hfc2
      nodes_range := fun x => by
        dsimp only; rw [hv2]
        constructor
        · rintro (hfl | ⟨u, hu, hxu⟩)
          · exact hfl_le2 x hfl
          · by_cases h : u = v
            · subst h; simp only [Function.update_self] at hxu; rw [ht'_mem_iff] at hxu
              rcases hxu with rfl | htv
              · exact ⟨hnx1, hnx_nn⟩
              · have := hinv1.live_le_nextNode hv htv; omega
            · simp only [Function.update_of_ne h] at hxu
              have := hinv1.live_le_nextNode hu hxu; omega
        · rintro ⟨hx1, hxnn⟩
          rcases hpart2 x hx1 hxnn with rfl | ⟨u, hu, hxu⟩ | hfl
          · exact Or.inr ⟨v, hv, by simp only [Function.update_self]; exact (ht'_mem_iff x).mpr (Or.inl rfl)⟩
          · by_cases h : u = v
            · subst h; exact Or.inr ⟨u, hv, by simp only [Function.update_self]; exact (ht'_mem_iff x).mpr (Or.inr hxu)⟩
            · exact Or.inr ⟨u, hu, by simpa [h] using hxu⟩
          · exact Or.inl hfl
      key_lt := fun u hu x hxu => by
        dsimp only at hu hxu ⊢; rw [hv2] at hu; rw [he2]
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hxu; rw [ht'_mem_iff] at hxu
          rcases hxu with rfl | htv
          · simp [hspF_nx, ordFreshNode, hkX]
          · rw [hspF_val x (fun he => hnx_nlive u hv (by rw [← he]; exact htv))]; exact hinv1.key_lt u hv x htv
        · simp only [Function.update_of_ne h] at hxu
          rw [hspF_val x (fun he => hnx_nlive u hu (by rw [← he]; exact hxu))]; exact hinv1.key_lt u hu x hxu
      eNode_spec := fun j hj => by
        dsimp only at hj ⊢; rw [he2] at hj; rw [hv2, hen2]
        by_cases hjk : j = keyX
        · subst hjk; right; refine ⟨v, hv, by simp only [Function.update_self]; exact (ht'_mem_iff nx).mpr (Or.inl rfl),
            by simp [hspF_nx, ordFreshNode]⟩
        · simp only [Function.update_of_ne hjk]
          rcases hinv1.eNode_spec j hj with ⟨h0, hnone'⟩ | ⟨u, hu, hmem', hval'⟩
          · left; refine ⟨h0, fun u hu x hxu heq => ?_⟩
            by_cases h : u = v
            · subst h; simp only [Function.update_self] at hxu; rw [ht'_mem_iff] at hxu
              rcases hxu with rfl | htv
              · simp [hspF_nx, ordFreshNode] at heq; exact hjk heq.symm
              · rw [hspF_val x (fun he => hnx_nlive u hv (by rw [← he]; exact htv))] at heq; exact hnone' u hv x htv heq
            · simp only [Function.update_of_ne h] at hxu
              rw [hspF_val x (fun he => hnx_nlive u hu (by rw [← he]; exact hxu))] at heq; exact hnone' u hu x hxu heq
          · right; refine ⟨u, hu, ?_, ?_⟩
            · by_cases h : u = v
              · subst h; simp only [Function.update_self]; exact (ht'_mem_iff _).mpr (Or.inr hmem')
              · simpa [h] using hmem'
            · rw [hspF_val _ (fun he => hnx_nlive u hu (by rw [← he]; exact hmem'))]; exact hval' }

theorem insertSplice_runs
    {w b v keyX keyY uy allocProc : ℕ} {p : Program}
    (halloc : p.procs[allocProc]? = some ordAllocBody) (ω : ℕ → Bool)
    {stM : State} {ord : ℕ → List End} {S1 : OrdStoreState} {heap : ℕ}
    (hinv1 : OrdInv ord S1) (harena1 : OrdArenaAt b S1 stM.mem)
    (hv : v < S1.vCap) (hkX : keyX < 2 * S1.eCap) (hunused : S1.eNode keyX = 0)
    (hrt : (S1.trees v).rootId = uy) (huy_mem : uy ∈ (S1.trees v).toList)
    (huy_val : (S1.splay.nodes uy).val = keyY)
    (huniq' : OrdUniqueWithin S1.vCap S1.eCap
      (applyOrdEdit ord (.insertBefore v (endOfKey keyX) (some (endOfKey keyY)))))
    (hr0 : stM.regs 0 = b) (hr1 : stM.regs 1 = v) (hr2 : stM.regs 2 = keyX)
    (hr5 : stM.regs 5 = ordNodesBase b S1.vCap S1.eCap) (hr10 : stM.regs 10 = uy)
    (hr11 : stM.regs 11 = v + 1)
    (hfoot : b + ordArenaSize S1.vCap S1.eCap ≤ heap)
    (hz : ZeroFrom stM.mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ st' c, Runs w p ω
        (.call 4 allocProc [.reg 0, .reg 2] ;;
         .assign 12 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 4))) ;;
         .assign 13 (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 10))) ;;
         .assign 14 (.load (.reg 13)) ;;
         .store (.reg 12) (.reg 14) ;;
         .cond (.reg 14)
           (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 2)) (.reg 4))
           .nop ;;
         .store (.bin .add (.reg 12) (.const 1)) (.reg 10) ;;
         .store (.bin .add (.reg 12) (.const 3)) (.reg 11) ;;
         .assign 15 (.load (.bin .add (.reg 13) (.const 4))) ;;
         .store (.bin .add (.reg 12) (.const 4)) (.bin .add (.reg 15) (.const 1)) ;;
         .store (.reg 13) (.const 0) ;;
         .store (.bin .add (.reg 13) (.const 2)) (.reg 4) ;;
         .store (.bin .add (.reg 13) (.const 3)) (.const 0) ;;
         .assign 16 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 14))) (.const 4))) ;;
         .store (.bin .add (.reg 13) (.const 4)) (.bin .sub (.reg 15) (.reg 16)) ;;
         .assign 17 (.load (.bin .add (.reg 0) (.const 2))) ;;
         .store (.bin .add (.reg 17) (.reg 1)) (.reg 4) ;;
         .assign 7 (.const 1)) stM .normal st' c ∧
      st'.regs 7 = 1 ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdit ord (.insertBefore v (endOfKey keyX) (some (endOfKey keyY)))) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S1.vCap S1.eCap heap stM.mem st'.mem ∧
        S'.vCap = S1.vCap ∧ S'.eCap = S1.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 + 2000 * ordStoreLog S1.eCap) := by
  have hlog : 1 ≤ ordStoreLog S1.eCap := ordStoreLog_pos S1.eCap
  have hfoot' : b + (16 + S1.vCap + 18 * S1.eCap) ≤ heap := hfoot
  set nb := ordNodesBase b S1.vCap S1.eCap with hnb
  obtain ⟨L, R, htv_eq⟩ : ∃ L R, S1.trees v = .node uy L R := by
    cases htv : S1.trees v with
    | leaf => exfalso; rw [htv] at huy_mem; exact List.not_mem_nil huy_mem
    | node id l r => simp only [htv, AuxTree.rootId] at hrt; exact ⟨l, r, by rw [hrt]⟩
  have htv_inv : TreeInv ordPayload S1.splay (.node uy L R) := htv_eq ▸ hinv1.tree_inv v hv
  rcases htv_inv.sub with ⟨huy_nz, huyL, huyR, -, -, huysz, -, hsubL, hsubR⟩
  rcases AuxTree.nodup_node_unfold htv_inv.nodup with ⟨hLnd, huy_nL, hRnd, huy_nR, hLR_disj⟩
  obtain ⟨oA, stA, cA, hrunA, ⟨nx, S2, hoA, hnx1, hnx_nn, hnn_ge, hnn_le, hv2, he2, hvr2, htr2,
    hen2, hsp2, hnx_nlive, hnx_nfl, hflnd2, hfc2, hfl_le2, hlive_fl2, hpart2, harena2, hfr2⟩, hcA⟩ :=
    ordAllocBody_runs ω hinv1 harena1 hkX hunused hfoot hz hw hwide (pos := stM.pos)
  have hcallA : Runs w p ω (.call 4 allocProc [.reg 0, .reg 2]) stM .normal
      { stA with regs := Function.update stM.regs 4 nx } (argsSize [.reg 0, .reg 2] + cA + 1) :=
    runs_call_iff.mpr ⟨[b, keyX], ordAllocBody, oA, stA, cA,
      evalArgs_cons (Expr.eval_reg_of_eq hr0) (evalArgs_cons (Expr.eval_reg_of_eq hr2) (evalArgs_nil _ _)),
      halloc, hrunA, rfl, by simp [hoA], rfl⟩
  set st1 : State := { stA with regs := Function.update stM.regs 4 nx }
  have hnx_ne_uy : nx ≠ uy := fun h => hnx_nlive v hv (h ▸ huy_mem)
  have hnx_nL : nx ∉ L.toList := fun h => hnx_nlive v hv (by rw [htv_eq]; exact List.mem_append_left _ (List.mem_append_left _ h))
  have hnx_nR : nx ∉ R.toList := fun h => hnx_nlive v hv (by rw [htv_eq]; exact List.mem_append_right _ h)
  have hnx_ne_L : nx ≠ L.rootId := by
    cases L with
    | leaf => simp [AuxTree.rootId]; omega
    | node lid ll lr => intro h; simp only [AuxTree.rootId] at h; exact hnx_nL (by rw [h]; exact AuxTree.rootId_mem (t := .node lid ll lr) (by simp))
  have huy_ne_L : uy ≠ L.rootId := by
    cases L with
    | leaf => simp [AuxTree.rootId]; exact huy_nz
    | node lid ll lr => intro h; simp only [AuxTree.rootId] at h; exact huy_nL (by rw [h]; exact AuxTree.rootId_mem (t := .node lid ll lr) (by simp))
  have huy_c2 : uy ≤ S2.nextNode := by have := (hinv1.live_le_nextNode hv huy_mem).2; omega
  have hL_c2 : L.rootId ≤ S2.nextNode := by
    cases L with
    | leaf => simp [AuxTree.rootId]
    | node lid ll lr =>
      have hmem : lid ∈ (S1.trees v).toList := by
        rw [htv_eq]; exact List.mem_append_left _ (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)))
      have := (hinv1.live_le_nextNode hv hmem).2; simp only [AuxTree.rootId]; omega
  have hnb_w : nb + 8 * (S2.nextNode + 1) < 2 ^ w := by have := ordNodesBase_end b S1.vCap S1.eCap; omega
  have hn2 : OrdNodesAt st1.mem nb S2.nextNode S2.splay S2.nextFree := fun x hx => by
    have h := harena2.nodes_at x hx; rw [hv2, he2, ← hnb] at h; exact h
  have hcnt_le2 : (AuxTree.node uy L R).countNodes + 1 ≤ S2.nextNode := by
    have hsub : ((S1.trees v).toList.toFinset ∪ {nx}) ⊆ Finset.Icc 1 S2.nextNode := by
      intro z hz
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_singleton, Finset.mem_Icc] at hz ⊢
      rcases hz with hzt | rfl
      · have := hinv1.live_le_nextNode hv hzt; omega
      · exact ⟨hnx1, hnx_nn⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (by simp [hnx_nlive v hv]),
      List.toFinset_card_of_nodup (hinv1.tree_inv v hv).nodup,
      AuxTree.length_toList, Finset.card_singleton, Nat.card_Icc, htv_eq] at hcard
    omega
  have hLsz2 : (S2.splay.nodes L.rootId).sz = L.countNodes := by
    rw [hsp2, SplayState.nodes_updateNode_ne _ (Ne.symm hnx_ne_L)]
    cases L with
    | leaf => simp [AuxTree.rootId, AuxTree.countNodes, hinv1.null_node, ordNullNode]
    | node lid ll lr => exact hsubL.2.2.2.2.2.1
  obtain ⟨stE, cE, m9, spF, hrunE, hr7E, hmemE, hnF, hm9_out, hspF_out2, hspF_nx2, hspF_uy2, hspF_L2, hspF_02, hcE⟩ :=
    insertSplice_exec (p := p) (keyX := keyX) (L := L) (R := R) (st1 := st1) ω
      (by rw [hv2, he2]) harena2.hdr_vRoot hn2 (by rw [hv2]; exact hv) hnx_nn huy_c2 hL_c2
      hnx_ne_uy hnx_ne_L huy_ne_L
      (by rw [hsp2, SplayState.nodes_updateNode_ne _ (Ne.symm hnx_ne_uy)]; exact huyL)
      (by rw [hsp2, SplayState.nodes_updateNode_ne _ (Ne.symm hnx_ne_uy)]; exact huysz)
      hLsz2 hcnt_le2 (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1])
      (by simp [st1, hr5]) (by simp [st1, hr10]) (by simp [st1, hr11]) hnb_w hwide
  have hspF_out : ∀ x, x ≠ nx → x ≠ uy → x ≠ L.rootId → spF.nodes x = S1.splay.nodes x := fun x h1 h2 h3 => by
    rw [hspF_out2 x h1 h2 h3, hsp2, SplayState.nodes_updateNode_ne _ h1]
  have hspF_nx : spF.nodes nx =
      { (ordFreshNode keyX) with left := L.rootId, right := uy, ppar := v + 1, sz := (AuxTree.node uy L R).countNodes + 1 } := by
    rw [hspF_nx2, hsp2, SplayState.nodes_updateNode]; simp
  have hspF_uy : spF.nodes uy =
      { (S1.splay.nodes uy) with left := 0, par := nx, ppar := 0, sz := (AuxTree.node uy .leaf R).countNodes } := by
    rw [hspF_uy2, hsp2, SplayState.nodes_updateNode_ne _ (Ne.symm hnx_ne_uy)]
  have hspF_L : L.rootId ≠ 0 → spF.nodes L.rootId = { (S1.splay.nodes L.rootId) with par := nx } := fun hL0 => by
    rw [hspF_L2 hL0, hsp2, SplayState.nodes_updateNode_ne _ (Ne.symm hnx_ne_L)]
  have hspF_0 : spF.nodes 0 = ordNullNode := by
    by_cases hL0 : L.rootId = 0
    · rw [hspF_02 hL0, hsp2, SplayState.nodes_updateNode_ne _ (by omega)]; exact hinv1.null_node
    · rw [hspF_out 0 (by omega) (Ne.symm huy_nz) (Ne.symm hL0)]; exact hinv1.null_node
  let t' : AuxTree := .node nx L (.node uy .leaf R)
  let S' : OrdStoreState :=
    { S2 with
      splay := spF
      vRoot := Function.update S1.vRoot v nx
      trees := Function.update S1.trees v t' }
  have hinv' : OrdInv (applyOrdEdit ord (.insertBefore v (endOfKey keyX) (some (endOfKey keyY)))) S' :=
    insertSplice_inv hinv1 hv hkX htv_eq huy_mem huy_val huniq' hnx1 hnx_nn hnn_ge hnn_le
      hv2 he2 hen2 hnx_nlive hnx_nfl hflnd2 hfc2 hfl_le2 hlive_fl2 hpart2
      hspF_out hspF_nx hspF_uy hspF_L hspF_0
  have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S2.nextNode a := fun a ha h => by unfold InOrdNodes at h; omega
  have hnot_vr : ¬ InOrdNodes nb S2.nextNode (ordVRootBase b + v) :=
    hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)
  have hfr3 : OrdFrame b S1.vCap S1.eCap heap stA.mem stE.mem := by
    have h1 : ∀ a, ¬ ordFoot b S1.vCap S1.eCap a → stE.mem a = stA.mem a := fun a ha => by
      have hnot1 : ¬ InOrdNodes nb S2.nextNode a := fun h =>
        ha ⟨by unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega,
            by unfold InOrdNodes at h; have := ordNodesBase_end b S1.vCap S1.eCap; rw [hnb] at h; omega⟩
      rw [hmemE, Function.update_of_ne (fun h => ha (by rw [h]; exact ordFoot_vRoot hv)), hm9_out a hnot1]
    exact ⟨fun a ha => (h1 a (fun hf => by unfold ordFoot at hf; omega)).trans (hfr2.1 a ha),
           fun a _ hnf => h1 a hnf⟩
  have harena' : OrdArenaAt b S' stE.mem := by
    have hhdr : ∀ j < 7, stE.mem (b + j) = stA.mem (b + j) := fun j hj => by
      rw [hmemE, Function.update_of_ne (by unfold ordVRootBase; omega),
          hm9_out _ (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))]
    exact
      { hdr_vCap := (hhdr 0 (by omega)).trans harena2.hdr_vCap
        hdr_eCap := (hhdr 1 (by omega)).trans harena2.hdr_eCap
        hdr_vRoot := (hhdr 2 (by omega)).trans harena2.hdr_vRoot
        hdr_eNode := (hhdr 3 (by omega)).trans harena2.hdr_eNode
        hdr_nodes := (hhdr 4 (by omega)).trans harena2.hdr_nodes
        hdr_next := (hhdr 5 (by omega)).trans harena2.hdr_next
        hdr_free := (hhdr 6 (by omega)).trans harena2.hdr_free
        vRoot_at := fun u hu => by
          dsimp only [S'] at hu ⊢; rw [hv2] at hu; rw [hmemE]
          by_cases h : u = v
          · subst h; simp
          · rw [Function.update_of_ne (by omega), Function.update_of_ne h,
                hm9_out _ (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)), ← hvr2]
            exact harena2.vRoot_at u (by rw [hv2]; exact hu)
        eNode_at := fun j hj => by
          dsimp only [S'] at hj ⊢; rw [he2] at hj; rw [hv2, hmemE]
          rw [Function.update_of_ne (by unfold ordVRootBase ordENodeBase; omega),
              hm9_out _ (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))]
          have h := harena2.eNode_at j (by rw [he2]; exact hj); rwa [hv2] at h
        nodes_at := by
          dsimp only [S']; rw [hv2, he2, hmemE]
          exact hnF.congr fun a ha => Function.update_of_ne (fun (h : a = ordVRootBase b + v) => hnot_vr (h ▸ ha)) _ _ }
  have hphi_t' : t'.treePhi (fun _ => 0) ≤ (S1.trees v).treePhi (fun _ => 0) + ordStoreLog S1.eCap := by
    rw [htv_eq]
    have hrk1 : (AuxTree.node nx L (.node uy .leaf R)).rank (fun _ => 0) ≤ ordStoreLog S1.eCap :=
      rank_zero_le_ordStoreLog (by simp only [AuxTree.countNodes] at hcnt_le2 ⊢; omega)
    have hrk2 : (AuxTree.node uy .leaf R).rank (fun _ => 0) ≤ (AuxTree.node uy L R).rank (fun _ => 0) := by
      unfold AuxTree.rank; rw [treeSize_zero_eq_countNodes, treeSize_zero_eq_countNodes]
      exact Nat.log_mono_right (by simp [AuxTree.countNodes])
    simp only [t', AuxTree.treePhi]; omega
  have hphi_upd : sumTreePhi S' + (S1.trees v).treePhi (fun _ => 0) =
      sumTreePhi S1 + t'.treePhi (fun _ => 0) := by
    have h := sumTreePhi_update (S := S1) (S' := S') hv hv2 (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = t' from Function.update_self v t' S1.trees] at h; exact h
  have hcnt_upd : sumCountNodes S' = sumCountNodes S1 + 1 := by
    have h1 := sumCountNodes_update (S := S1) (S' := S') hv hv2 (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = t' from Function.update_self v t' S1.trees] at h1
    have h2 : t'.countNodes = (S1.trees v).countNodes + 1 := by rw [htv_eq]; simp [t', AuxTree.countNodes]; omega
    omega
  refine ⟨stE, _, ord_runs_seq_normal hcallA hrunE, hr7E, S', hinv', harena', hfr2.trans hfr3, hv2, he2, ?_⟩
  unfold ORD_ALLOC_COST at hcA
  unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT at ⊢
  have hmul_upd : 1000 * sumTreePhi S' + 1000 * (S1.trees v).treePhi (fun _ => 0) =
      1000 * sumTreePhi S1 + 1000 * t'.treePhi (fun _ => 0) := by
    have := congrArg (1000 * ·) hphi_upd; ring_nf at this ⊢; exact this
  have hmul_t' : 1000 * t'.treePhi (fun _ => 0) ≤
      1000 * (S1.trees v).treePhi (fun _ => 0) + 1000 * ordStoreLog S1.eCap := by
    have := Nat.mul_le_mul_left 1000 hphi_t'; ring_nf at this ⊢; omega
  have hmul_cnt : 300 * sumCountNodes S' = 300 * sumCountNodes S1 + 300 := by
    rw [hcnt_upd]; ring
  simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
  omega

end MinCostFlow.SparseCore.Program
