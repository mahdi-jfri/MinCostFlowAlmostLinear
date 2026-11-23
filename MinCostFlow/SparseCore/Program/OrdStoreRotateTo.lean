module

public import MinCostFlow.SparseCore.Program.OrdStoreFreeTree
public import MinCostFlow.SparseCore.Program.OrdStoreInsertBack
import Mathlib.Tactic

/-!
# Order Store `rotateTo` Procedure

This file implements and verifies `ordRotateToBody` on `[b, v, keyY]`: if `v < vCap`,
`keyY < 2 * eCap`, `uy = eNode[keyY] ≠ 0`, and `ordSplayRoot [b, uy]` returns `v + 1`, it detaches
`uy.left` and joins `uy` with `uy.left` to rotate `ord v` to start at `endOfKey keyY`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_ROT_AMORT : ℕ := 12000

/-- `ordRotateTo` on `[b, v, keyY]`: rotates `ord v` to start at `endOfKey keyY` if present. -/
def ordRotateToBody (splayRootProc joinProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 0))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .cond (.bin .lt (.reg 1) (.reg 3))
    (.cond (.bin .lt (.reg 2) (.bin .add (.reg 4) (.reg 4)))
      (.assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
       .assign 6 (.load (.bin .add (.reg 5) (.reg 2))) ;;
       .cond (.reg 6)
         (.call 7 splayRootProc [.reg 0, .reg 6] ;;
          .cond (.bin .eq (.reg 7) (.bin .add (.reg 1) (.const 1)))
            (.assign 8 (.load (.bin .add (.reg 0) (.const 4))) ;;
             .assign 9 (.bin .add (.reg 8) (.bin .mul (.const 8) (.reg 6))) ;;
             .assign 10 (.load (.reg 9)) ;;
             .cond (.reg 10)
               (.store (.reg 9) (.const 0) ;;
                .assign 11 (.bin .add (.reg 8) (.bin .mul (.const 8) (.reg 10))) ;;
                .store (.bin .add (.reg 11) (.const 2)) (.const 0) ;;
                .assign 12 (.load (.bin .add (.reg 9) (.const 4))) ;;
                .assign 13 (.load (.bin .add (.reg 11) (.const 4))) ;;
                .store (.bin .add (.reg 9) (.const 4)) (.bin .sub (.reg 12) (.reg 13)) ;;
                .call 14 joinProc [.reg 8, .reg 6, .reg 10, .reg 7] ;;
                .assign 15 (.load (.bin .add (.reg 0) (.const 2))) ;;
                .store (.bin .add (.reg 15) (.reg 1)) (.reg 14) ;;
                .ret (.const 0))
               (.ret (.const 0)))
            (.ret (.const 0)))
         (.ret (.const 0)))
      (.ret (.const 0)))
    (.ret (.const 0))

theorem ordRotateToBody_noRand (srP jP : ℕ) : (ordRotateToBody srP jP).NoRand := by
  simp [ordRotateToBody, Stmt.NoRand]

theorem ordRotateToBody_runs
    {w b v keyY pos rotProc stepProc splayProc splayRootProc walkProc joinProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem)
    (hv_w : v < 2 ^ w) (hk_w : keyY < 2 ^ w)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordRotateToBody splayRootProc joinProc)
        (startState [b, v, keyY] mem pos) o st' c ∧
      (∃ S' : OrdStoreState,
        OrdInv (applyOrdEdit ord (.rotateTo v (endOfKey keyY))) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_ROT_AMORT * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  set st0 : State := startState [b, v, keyY] mem pos
  have ha3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 0)))) st0 .normal
      { st0 with regs := Function.update st0.regs 3 S.vCap } _ :=
    runs_assign_iff.mpr ⟨S.vCap, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_vCap, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 S.vCap }
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 1)))) st1 .normal
      { st1 with regs := Function.update st1.regs 4 S.eCap } _ :=
    runs_assign_iff.mpr ⟨S.eCap, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_eCap, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 4 S.eCap }
  have hnoop_eq : endOfKey keyY ∉ ord v → applyOrdEdit ord (.rotateTo v (endOfKey keyY)) = ord := fun hnm => by
    funext u; simp only [applyOrdEdit]
    by_cases h : u = v
    · subst h; simp [rotateToList, hnm]
    · simp [h]
  unfold ordRotateToBody
  by_cases hv : v < S.vCap
  · have hc1 : (Expr.bin .lt (.reg 1) (.reg 3)).eval w st2 = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]))
        (Expr.eval_reg_of_eq (by simp [st2, st1])) hv (by omega)
    by_cases hk : keyY < S.eCap + S.eCap
    · have hk2 : keyY < 2 * S.eCap := by omega
      have hc2 : (Expr.bin .lt (.reg 2) (.bin .add (.reg 4) (.reg 4))).eval w st2 = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]))
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2])) (Expr.eval_reg_of_eq (by simp [st2])) (by omega))
          hk (by omega)
      set en := ordENodeBase b S.vCap with hen
      set nb := ordNodesBase b S.vCap S.eCap with hnb
      have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 3)))) st2 .normal
          { st2 with regs := Function.update st2.regs 5 en } _ :=
        runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) (by omega)) harena.hdr_eNode, rfl, rfl, rfl⟩
      set st3 : State := { st2 with regs := Function.update st2.regs 5 en }
      have hm_ek : mem (en + keyY) = S.eNode keyY := harena.eNode_at keyY hk2
      have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 2)))) st3 .normal
          { st3 with regs := Function.update st3.regs 6 (S.eNode keyY) } _ :=
        runs_assign_iff.mpr ⟨S.eNode keyY, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st3]))
          (Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState])) (by unfold ordENodeBase at hen; omega)) hm_ek,
          rfl, rfl, rfl⟩
      set st4 : State := { st3 with regs := Function.update st3.regs 6 (S.eNode keyY) }
      rcases hinv.eNode_spec keyY hk2 with ⟨he0, hnone⟩ | ⟨w0, hw0, hu_mem, hu_val⟩
      · -- keyY absent
        have hc3 : (Expr.reg 6).eval w st4 = some 0 := Expr.eval_reg_of_eq (by simp [st4, he0])
        have hret : Runs w p ω (.ret (.const 0)) st4 (.returned 0) st4 _ :=
          runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
        have hnm : endOfKey keyY ∉ ord v := by
          rw [← hinv.list_eq v hv]; rintro h
          rcases List.mem_map.mp h with ⟨x, hx, hxe⟩
          exact hnone v hv x hx (endOfKey_injective hxe)
        refine ⟨.returned 0, st4, _,
          ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_true hc1 Nat.one_ne_zero
            (ord_runs_cond_true hc2 Nat.one_ne_zero (ord_runs_seq_normal ha5
              (ord_runs_seq_normal ha6 (ord_runs_cond_false hc3 hret)))))),
          S, by rwa [hnoop_eq hnm], harena, OrdFrame.refl hz, rfl, rfl, ?_⟩
        unfold ORD_ROT_AMORT
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
      · -- keyY live at u = S.eNode keyY in vertex w0
        set u := S.eNode keyY with hu_def
        have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero (hinv.tree_inv w0 hw0).sub hu_mem
        have hc3 : (Expr.reg 6).eval w st4 = some u := Expr.eval_reg_of_eq (by simp [st4, hu_def])
        obtain ⟨oSR, stSR, cSR, hrunSR, ⟨S1, hoSR, hinv1, harena1, hfr1, hv1, he1, hrt1, hlist1, -, hcnt1, hphi1⟩, hcSR⟩ :=
          ordSplayRootBody_runs hrot hstep hsplay ω hinv harena hw0 hu_mem hfoot hz hw hwide (pos := st4.pos)
        have hcallSR : Runs w p ω (.call 7 splayRootProc [.reg 0, .reg 6]) st4 .normal
            { stSR with regs := Function.update st4.regs 7 (w0 + 1) }
            (argsSize [.reg 0, .reg 6] + cSR + 1) :=
          runs_call_iff.mpr ⟨[b, u], ordSplayRootBody splayProc, oSR, stSR, cSR,
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]))
              (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st4, hu_def])) (evalArgs_nil _ _)),
            hsplayRoot, hrunSR, rfl, by simp [hoSR], rfl⟩
        set st5 : State := { stSR with regs := Function.update st4.regs 7 (w0 + 1) }
        have hphi1_mul : cSR + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
            ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 4000 * ordStoreLog S.eCap := by
          unfold ordPhi; rw [hcnt1]
          have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi1
          have h2 : ORD_PHI_WEIGHT * (sumTreePhi S1 + (S.trees w0).depthOf u / 2) =
              ORD_PHI_WEIGHT * sumTreePhi S1 + ORD_PHI_WEIGHT * ((S.trees w0).depthOf u / 2) := by ring
          have h3 : ORD_PHI_WEIGHT * (sumTreePhi S + 3 * ordStoreLog S.eCap) =
              ORD_PHI_WEIGHT * sumTreePhi S + 3 * ORD_PHI_WEIGHT * ordStoreLog S.eCap := by ring
          unfold ORD_PHI_WEIGHT at h1 h2 h3 ⊢; unfold ORD_SPLAY_RATE at hcSR
          have h650 : ((S.trees w0).depthOf u / 2) * 650 ≤ 1000 * ((S.trees w0).depthOf u / 2) := by omega
          omega
        by_cases hwv : v = w0
        · subst hwv
          have hc4 : (Expr.bin .eq (.reg 7) (.bin .add (.reg 1) (.const 1))).eval w st5 = some 1 :=
            Expr.eval_eq_true (Expr.eval_reg_of_eq (v := v + 1) (by simp [st5]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st5, st4, st3, st2, st1, st0, startState]))
                (Expr.eval_const (by omega)) (by omega)) rfl (by omega)
          have hnb1 : stSR.mem (b + 4) = nb := by rw [hnb, ← hv1, ← he1]; exact harena1.hdr_nodes
          have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 4)))) st5 .normal
              { st5 with regs := Function.update st5.regs 8 nb } _ :=
            runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1, st0, startState]))
              (Expr.eval_const (by omega)) (by omega)) hnb1, rfl, rfl, rfl⟩
          set st6 : State := { st5 with regs := Function.update st5.regs 8 nb }
          have hu_c1 : u ≤ S1.nextNode := (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (hlist1 ▸ hu_mem)).2
          have hnb_w : nb + 8 * (S1.nextNode + 1) < 2 ^ w := by
            have := ordNodesBase_end b S.vCap S.eCap; have := hinv1.next_le; rw [he1] at this; omega
          have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.bin .mul (.const 8) (.reg 6)))) st6 .normal
              { st6 with regs := Function.update st6.regs 9 (nb + 8 * u) } _ :=
            runs_assign_iff.mpr ⟨nb + 8 * u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6]))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st6, st5, st4, hu_def])) (by omega)) (by omega),
              rfl, rfl, rfl⟩
          set st7 : State := { st6 with regs := Function.update st6.regs 9 (nb + 8 * u) }
          obtain ⟨L, R, htv_eq⟩ : ∃ L R, S1.trees v = .node u L R := by
            cases htv : S1.trees v with
            | leaf => exfalso; rw [htv] at hlist1; exact List.not_mem_nil (hlist1 ▸ hu_mem)
            | node id l r => simp only [htv, AuxTree.rootId] at hrt1; exact ⟨l, r, by rw [hrt1]⟩
          have htv_inv : TreeInv ordPayload S1.splay (.node u L R) := htv_eq ▸ hinv1.tree_inv v (by rw [hv1]; exact hv)
          rcases htv_inv.sub with ⟨-, huL, huR, hupar, -, husz, -, hsubL, hsubR⟩
          rcases AuxTree.nodup_node_unfold htv_inv.nodup with ⟨hLnd, hu_nL, hRnd, hu_nR, hLR_disj⟩
          have hm1_uL : stSR.mem (nb + 8 * u) = L.rootId := by
            rw [← huL]; have h := (harena1.nodes_at u hu_c1).1
            rw [hv1, he1] at h; simpa [ordNodeAddr, hnb] using h
          have ha10 : Runs w p ω (.assign 10 (.load (.reg 9))) st7 .normal
              { st7 with regs := Function.update st7.regs 10 L.rootId } _ :=
            runs_assign_iff.mpr ⟨L.rootId, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st7])) hm1_uL,
              rfl, rfl, rfl⟩
          set st8 : State := { st7 with regs := Function.update st7.regs 10 L.rootId }
          have hval_u1 : (S1.splay.nodes u).val = keyY := by
            have h1 := hinv1.list_eq v (by rw [hv1]; exact hv)
            have h2 := hinv.list_eq v hv
            rw [hlist1] at h1
            rcases List.getElem_of_mem hu_mem with ⟨i, hi, hgi⟩
            rw [← h1] at h2
            have hm := congrArg (fun l => l[i]?) h2
            simp [hi, hgi, hu_val] at hm
            exact (endOfKey_injective hm).symm
          have hord_v_eq : ord v = L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) ++
              [endOfKey keyY] ++ R.toList.map (fun x => endOfKey (S1.splay.nodes x).val) := by
            rw [← hinv1.list_eq v (by rw [hv1]; exact hv), htv_eq]
            simp [AuxTree.toList, hval_u1]
          have hidx_y : (ord v).idxOf (endOfKey keyY) = L.toList.length := by
            have hnd_v : (ord v).Nodup := hinv.ord_unique.nodup v
            rw [hord_v_eq, List.append_assoc, List.singleton_append] at hnd_v ⊢
            have hnmL : endOfKey keyY ∉ L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) := by
              intro h; exact (List.nodup_append.mp hnd_v).2.2 _ h _ List.mem_cons_self rfl
            rw [idxOf_append_cons_of_not_mem hnmL, List.length_map]
          cases L with
          | leaf =>
            have hc5 : (Expr.reg 10).eval w st8 = some 0 := Expr.eval_reg_of_eq (by simp [st8, AuxTree.rootId])
            have hret : Runs w p ω (.ret (.const 0)) st8 (.returned 0) st8 _ :=
              runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
            have hrot_id : applyOrdEdit ord (.rotateTo v (endOfKey keyY)) = ord := by
              funext w; simp only [applyOrdEdit]
              by_cases h : w = v
              · subst h; simp [rotateToList, hidx_y, AuxTree.toList]
              · simp [h]
            refine ⟨.returned 0, st8, _,
              ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_true hc1 Nat.one_ne_zero
                (ord_runs_cond_true hc2 Nat.one_ne_zero (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6
                  (ord_runs_cond_true hc3 hu_nz (ord_runs_seq_normal hcallSR
                    (ord_runs_cond_true hc4 Nat.one_ne_zero
                      (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9
                        (ord_runs_seq_normal ha10 (ord_runs_cond_false hc5 hret)))))))))))),
              S1, by rwa [hrot_id], harena1, hfr1, hv1, he1, ?_⟩
            unfold ORD_ROT_AMORT
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
              argsSize_cons, argsSize_nil] at *
            omega
          | node lid ll lr =>
            set Lt : AuxTree := .node lid ll lr
            have hL_ne : Lt ≠ .leaf := by simp [Lt]
            have hL_nz : lid ≠ 0 := SplayState.SubtreeInv_nonZero hsubL (AuxTree.rootId_mem hL_ne)
            have hL_c : lid ≤ S1.nextNode :=
              (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (by rw [htv_eq]; simp [Lt, AuxTree.toList])).2
            have hc5 : (Expr.reg 10).eval w st8 = some lid := Expr.eval_reg_of_eq (by simp [st8, AuxTree.rootId])
            have hL_sz : (S1.splay.nodes lid).sz = Lt.countNodes := hsubL.2.2.2.2.2.1
            have hu_sz_eq : (S1.splay.nodes u).sz = (AuxTree.node u Lt R).countNodes := husz
            have hsz_sub : (S1.splay.nodes u).sz - (S1.splay.nodes lid).sz = (AuxTree.node u .leaf R).countNodes := by
              rw [hu_sz_eq, hL_sz]; simp [AuxTree.countNodes]; omega
            have hs1 : Runs w p ω (.store (.reg 9) (.const 0)) st8 .normal
                { st8 with mem := Function.update stSR.mem (nb + 8 * u) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * u, 0, Expr.eval_reg_of_eq (by simp [st8, st7]),
                Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m1 := Function.update stSR.mem (nb + 8 * u) 0
            set st9 : State := { st8 with mem := m1 }
            have ha11 : Runs w p ω (.assign 11 (.bin .add (.reg 8) (.bin .mul (.const 8) (.reg 10)))) st9 .normal
                { st9 with regs := Function.update st9.regs 11 (nb + 8 * lid) } _ :=
              runs_assign_iff.mpr ⟨nb + 8 * lid, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st9, st8, st7, st6]))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st9, st8, AuxTree.rootId])) (by omega)) (by omega),
                rfl, rfl, rfl⟩
            set st10 : State := { st9 with regs := Function.update st9.regs 11 (nb + 8 * lid) }
            have hs2 : Runs w p ω (.store (.bin .add (.reg 11) (.const 2)) (.const 0)) st10 .normal
                { st10 with mem := Function.update m1 (nb + 8 * lid + 2) 0 } _ :=
              runs_store_iff.mpr ⟨nb + 8 * lid + 2, 0, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st10]))
                (Expr.eval_const (by omega)) (by omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩
            set m2 := Function.update m1 (nb + 8 * lid + 2) 0
            set st11 : State := { st10 with mem := m2 }
            have hu_ne_lid : u ≠ lid := fun h => hu_nL (by rw [h]; exact AuxTree.rootId_mem (t := .node lid ll lr) (by simp))
            have hm2_usz : m2 (nb + 8 * u + 4) = (S1.splay.nodes u).sz := by
              dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              have h := (harena1.nodes_at u hu_c1).2.2.2.2.1; rw [hv1, he1] at h; simpa [ordNodeAddr, hnb] using h
            have hm2_lsz : m2 (nb + 8 * lid + 4) = (S1.splay.nodes lid).sz := by
              dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              have h := (harena1.nodes_at lid hL_c).2.2.2.2.1; rw [hv1, he1] at h; simpa [ordNodeAddr, hnb] using h
            have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 9) (.const 4)))) st11 .normal
                { st11 with regs := Function.update st11.regs 12 (S1.splay.nodes u).sz } _ :=
              runs_assign_iff.mpr ⟨(S1.splay.nodes u).sz, Expr.eval_load_of_eq (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [st11, st10, st9, st8, st7])) (Expr.eval_const (by omega)) (by omega))
                hm2_usz, rfl, rfl, rfl⟩
            set st12 : State := { st11 with regs := Function.update st11.regs 12 (S1.splay.nodes u).sz }
            have ha13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 11) (.const 4)))) st12 .normal
                { st12 with regs := Function.update st12.regs 13 (S1.splay.nodes lid).sz } _ :=
              runs_assign_iff.mpr ⟨(S1.splay.nodes lid).sz, Expr.eval_load_of_eq (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [st12, st11, st10])) (Expr.eval_const (by omega)) (by omega))
                hm2_lsz, rfl, rfl, rfl⟩
            set st13 : State := { st12 with regs := Function.update st12.regs 13 (S1.splay.nodes lid).sz }
            have hs3 : Runs w p ω (.store (.bin .add (.reg 9) (.const 4)) (.bin .sub (.reg 12) (.reg 13))) st13 .normal
                { st13 with mem := Function.update m2 (nb + 8 * u + 4) ((S1.splay.nodes u).sz - (S1.splay.nodes lid).sz) } _ :=
              runs_store_iff.mpr ⟨nb + 8 * u + 4, (S1.splay.nodes u).sz - (S1.splay.nodes lid).sz,
                Expr.eval_add (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st9, st8, st7]))
                  (Expr.eval_const (by omega)) (by omega),
                Expr.eval_sub (Expr.eval_reg_of_eq (v := (S1.splay.nodes u).sz) (by simp [st13, st12]))
                  (Expr.eval_reg_of_eq (v := (S1.splay.nodes lid).sz) (by simp [st13]))
                  (by
                    have hcnt := (hinv1.ordTreeOk (by rw [hv1]; exact hv)).count_le
                    rw [htv_eq] at hcnt; rw [hu_sz_eq]; omega),
                rfl, rfl, rfl⟩
            set m3 := Function.update m2 (nb + 8 * u + 4) ((S1.splay.nodes u).sz - (S1.splay.nodes lid).sz)
            set st14 : State := { st13 with mem := m3 }
            set spD := ((S1.splay.setLeft u 0).setPar lid 0).updateNode u fun nd =>
              { nd with sz := (S1.splay.nodes u).sz - (S1.splay.nodes lid).sz }
            have hnD : OrdNodesAt m3 nb S1.nextNode spD S1.nextFree := by
              have hn1 : OrdNodesAt stSR.mem nb S1.nextNode S1.splay S1.nextFree := fun x hx => by
                have h := harena1.nodes_at x hx; rw [hv1, he1, ← hnb] at h; exact h
              have hna : OrdNodesAt m1 nb S1.nextNode (S1.splay.setLeft u 0) S1.nextFree := by
                simpa [ordNodeAddr] using hn1.setLeft hu_c1 (v := 0)
              exact (hna.setPar hL_c (v := 0)).setSz hu_c1
            have h0_spD : spD.nodes 0 = ordNullNode := by
              simp only [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode,
                Ne.symm hu_nz, Ne.symm hL_nz, ite_false]
              exact hinv1.null_node
            have hcl_spD : ∀ x, (spD.nodes x).rev = false := fun x => by
              by_cases h1 : x = u
              · rw [h1]; simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hu_ne_lid, hinv1.clean]
              · by_cases h2 : x = lid
                · rw [h2]; simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid, hinv1.clean]
                · simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, h1, h2, hinv1.clean]
            have hokR' : OrdTreeOk S1.nextNode spD (.node u .leaf R) :=
              { null_node := h0_spD
                clean := hcl_spD
                inv := ⟨by
                  simp only [AuxTree.toList, List.nil_append, List.singleton_append]
                  exact List.nodup_cons.mpr ⟨hu_nR, hRnd⟩,
                  ⟨hu_nz, by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hu_ne_lid, AuxTree.rootId],
                    by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hu_ne_lid, huR],
                    by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hu_ne_lid, hupar],
                    fun h => absurd rfl h,
                    by simp [spD, SplayState.nodes_updateNode, hsz_sub],
                    rfl, trivial,
                    SplayState.SubtreeInv_agree hsubR fun x hx => by
                      have h1 : x ≠ u := fun h => hu_nR (by rw [← h]; exact hx)
                      have h2 : x ≠ lid := fun h => hLR_disj lid (AuxTree.rootId_mem (t := .node lid ll lr) (by simp)) (by rw [← h]; exact hx)
                      simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, h1, h2]⟩⟩
                mem_le := fun x hx => (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (by
                  rw [htv_eq]
                  simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons] at hx
                  rcases hx with rfl | hxr
                  · simp [AuxTree.toList]
                  · simp [AuxTree.toList, hxr])).2
                count_le := by
                  have h1 := (hinv1.ordTreeOk (by rw [hv1]; exact hv)).count_le
                  rw [htv_eq] at h1; simp [AuxTree.countNodes] at h1 ⊢; omega }
            have hokL' : OrdTreeOk S1.nextNode spD Lt := by
              rcases hsubL with ⟨-, hll, hlr, -, -, hlsz, -, hsubll, hsublr⟩
              rcases AuxTree.nodup_node_unfold hLnd with ⟨_, hlid_nll, _, hlid_nlr, _⟩
              have hinvL' : SplayState.SubtreeInv ordPayload spD 0 Lt :=
                ⟨hL_nz,
                  by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid, hll],
                  by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid, hlr],
                  by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid],
                  fun h => absurd rfl h,
                  by simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid, hlsz],
                  rfl,
                  SplayState.SubtreeInv_agree hsubll fun x hx => by
                    have hxu : x ≠ u := fun h => hu_nL (by rw [← h]; exact List.mem_append_left _ (List.mem_append_left _ hx))
                    have hxl : x ≠ lid := fun h => hlid_nll (by rw [← h]; exact hx)
                    simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hxu, hxl],
                  SplayState.SubtreeInv_agree hsublr fun x hx => by
                    have hxu : x ≠ u := fun h => hu_nL (by rw [← h]; exact List.mem_append_right _ hx)
                    have hxl : x ≠ lid := fun h => hlid_nlr (by rw [← h]; exact hx)
                    simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hxu, hxl]⟩
              exact
                { null_node := h0_spD
                  clean := hcl_spD
                  inv := ⟨hLnd, hinvL'⟩
                  mem_le := fun x hx => (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (by
                    rw [htv_eq]; simp [AuxTree.toList, hx])).2
                  count_le := by
                    have h1 := (hinv1.ordTreeOk (by rw [hv1]; exact hv)).count_le
                    rw [htv_eq] at h1; simp [AuxTree.countNodes] at h1 ⊢; omega }
            have hdisj_RL : ∀ x ∈ (AuxTree.node u .leaf R).toList, x ∉ Lt.toList := by
              intro x hx hxl
              simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons] at hx
              rcases hx with rfl | hxr
              · exact hu_nL hxl
              · exact hLR_disj x hxl hxr
            have hsum_RL : (AuxTree.node u .leaf R).countNodes + Lt.countNodes ≤ S1.nextNode := by
              have h1 := (hinv1.ordTreeOk (by rw [hv1]; exact hv)).count_le
              rw [htv_eq] at h1; simp [AuxTree.countNodes] at h1 ⊢; omega
            obtain ⟨oJ, stJ, cJ, hrunJ, spJ, tJ, hoJ, hnJ, hfrJ, hokJ, hlistJ, hcntJ, hppJ, hvalJ, houtJ, hphiJ⟩ :=
              ordJoinBody_runs hrot hstep hsplay hwalk ω hnD hokR' hokL' rfl rfl hdisj_RL hsum_RL
                (eCap := S.eCap) (by rw [← he1]; exact hinv1.next_le) (owner := v + 1) (by omega) hnb_w hwide (pos := st14.pos)
            have hcallJ : Runs w p ω (.call 14 joinProc [.reg 8, .reg 6, .reg 10, .reg 7]) st14 .normal
                { stJ with regs := Function.update st14.regs 14 tJ.rootId }
                (argsSize [.reg 8, .reg 6, .reg 10, .reg 7] + cJ + 1) :=
              runs_call_iff.mpr ⟨[nb, u, lid, v + 1], ordJoinBody walkProc, oJ, stJ, cJ,
                evalArgs_cons (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, st8, st7, st6]))
                  (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, hu_def]))
                    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, st8, AuxTree.rootId]))
                      (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, st8, st7, st6, st5]))
                        (evalArgs_nil _ _)))),
                hjoin, hrunJ, rfl, by simp [hoJ], rfl⟩
            set st15 : State := { stJ with regs := Function.update st14.regs 14 tJ.rootId }
            have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S1.nextNode a := fun a ha h => by
              unfold InOrdNodes at h; omega
            have hm3_out : ∀ a, ¬ InOrdNodes nb S1.nextNode a → m3 a = stSR.mem a := fun a ha => by
              dsimp only [m3, m2, m1]
              rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
                  Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
            have hstJ_vr : stJ.mem (b + 2) = ordVRootBase b :=
              (hfrJ (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
                ((hm3_out _ (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans harena1.hdr_vRoot)
            have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const 2)))) st15 .normal
                { st15 with regs := Function.update st15.regs 15 (ordVRootBase b) } _ :=
              runs_assign_iff.mpr ⟨ordVRootBase b, Expr.eval_load_of_eq (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState]))
                (Expr.eval_const (by omega)) (by omega)) hstJ_vr, rfl, rfl, rfl⟩
            set st16 : State := { st15 with regs := Function.update st15.regs 15 (ordVRootBase b) }
            have hst_vr : Runs w p ω (.store (.bin .add (.reg 15) (.reg 1)) (.reg 14)) st16 .normal
                { st16 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId } _ :=
              runs_store_iff.mpr ⟨ordVRootBase b + v, tJ.rootId,
                Expr.eval_add (Expr.eval_reg_of_eq (by simp [st16]))
                  (Expr.eval_reg_of_eq (by simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState]))
                  (by unfold ordVRootBase; omega),
                Expr.eval_reg_of_eq (by simp [st16, st15]), rfl, rfl, rfl⟩
            set st17 : State := { st16 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId }
            have hret : Runs w p ω (.ret (.const 0)) st17 (.returned 0) st17 _ :=
              runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
            have hrot_branch := ord_runs_seq_normal hs1 (ord_runs_seq_normal ha11 (ord_runs_seq_normal hs2
              (ord_runs_seq_normal ha12 (ord_runs_seq_normal ha13 (ord_runs_seq_normal hs3
                (ord_runs_seq_normal hcallJ (ord_runs_seq_normal ha15 (ord_runs_seq_normal hst_vr hret))))))))
            let S2 : OrdStoreState :=
              { S1 with
                splay := spJ
                vRoot := Function.update S1.vRoot v tJ.rootId
                trees := Function.update S1.trees v tJ }
            have hpermJ : tJ.toList.Perm (S1.trees v).toList := by
              rw [hlistJ, htv_eq]; simp only [AuxTree.toList, List.nil_append, List.singleton_append]
              rw [List.append_assoc]; exact List.perm_append_comm
            have hspD_val : ∀ x, (spD.nodes x).val = (S1.splay.nodes x).val := fun x => by
              by_cases h1 : x = u
              · rw [h1]; simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hu_ne_lid]
              · by_cases h2 : x = lid
                · rw [h2]; simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, Ne.symm hu_ne_lid]
                · simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, h1, h2]
            have hspJ_out : ∀ x ∉ (S1.trees v).toList, spJ.nodes x = S1.splay.nodes x := fun x hx => by
              rw [htv_eq] at hx
              have hx1 : x ∉ (AuxTree.node u .leaf R).toList := fun h => hx (by
                simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_cons] at h
                rcases h with rfl | h'
                · simp [AuxTree.toList]
                · simp [AuxTree.toList, h'])
              have hx2 : x ∉ Lt.toList := fun h => hx (by simp [AuxTree.toList, h])
              rw [houtJ x hx1 hx2]
              have hxu : x ≠ u := fun h => hx (by simp [AuxTree.toList, h])
              have hxl : x ≠ lid := fun h => hx2 (by rw [h]; exact AuxTree.rootId_mem (t := .node lid ll lr) (by simp))
              simp [spD, SplayState.setLeft, SplayState.setPar, SplayState.nodes_updateNode, hxu, hxl]
            have hlist_rot : tJ.toList.map (fun x => endOfKey (spJ.nodes x).val) =
                rotateToList (endOfKey keyY) (ord v) := by
              have h1 : tJ.toList.map (fun x => endOfKey (spJ.nodes x).val) =
                  tJ.toList.map (fun x => endOfKey (S1.splay.nodes x).val) :=
                List.map_congr_left fun x hx => by rw [hvalJ x hx, hspD_val x]
              rw [h1, hlistJ]
              have hmem_y : endOfKey keyY ∈ ord v := by rw [hord_v_eq]; simp
              simp only [rotateToList, hmem_y, ↓reduceIte, hidx_y]
              rw [hord_v_eq, List.append_assoc, List.singleton_append]
              have hlen : (Lt.toList.map fun x => endOfKey (S1.splay.nodes x).val).length = Lt.toList.length :=
                List.length_map _
              rw [List.drop_append_of_le_length (le_of_eq hlen.symm), List.take_append_of_le_length (le_of_eq hlen.symm),
                ← hlen, List.drop_length, List.take_length, List.nil_append]
              simp [AuxTree.toList, hval_u1]
            have hinv2 : OrdInv (applyOrdEdit ord (.rotateTo v (endOfKey keyY))) S2 :=
              { ord_unique :=
                  ⟨⟨fun w => by
                      simp only [applyOrdEdit]
                      by_cases h : w = v
                      · subst h; simp only [Function.update_self, ← hlist_rot]
                        have hnd1 := hinv1.ord_unique.nodup w
                        rw [← hinv1.list_eq w (by rw [hv1]; exact hv)] at hnd1
                        have hp : (tJ.toList.map fun x => endOfKey (spJ.nodes x).val).Perm
                            ((S1.trees w).toList.map fun x => endOfKey (S1.splay.nodes x).val) := by
                          rw [List.map_congr_left fun x hx => by rw [hvalJ x hx, hspD_val x]]
                          exact hpermJ.map _
                        exact hp.nodup_iff.mpr hnd1
                      · simp only [Function.update_of_ne h]; exact hinv.ord_unique.nodup w,
                    fun w hw => by
                      dsimp only [S2] at hw
                      simp only [applyOrdEdit, Function.update_of_ne (by omega : w ≠ v)]
                      exact hinv.ord_unique.eq_nil_of_ge (by omega),
                    fun w x hx => by
                      dsimp only [S2]
                      simp only [applyOrdEdit] at hx
                      by_cases h : w = v
                      · subst h; simp only [Function.update_self] at hx
                        rw [← hlist_rot] at hx
                        rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
                        rw [hvalJ z hz, hspD_val z]
                        have hzm : z ∈ (S1.trees w).toList := hpermJ.mem_iff.mp hz
                        have := hinv1.key_lt w (by rw [hv1]; exact hv) z hzm
                        simp [endOfKey]; omega
                      · simp only [Function.update_of_ne h] at hx
                        rw [he1]; exact hinv.ord_unique.edge_lt hx⟩,
                   fun w1 w2 x h1 h2 => by
                     have hmem_ord : ∀ w, x ∈ applyOrdEdit ord (.rotateTo v (endOfKey keyY)) w → x ∈ ord w := fun w hw => by
                       simp only [applyOrdEdit] at hw
                       by_cases h : w = v
                       · subst h; simp only [Function.update_self, ← hlist_rot] at hw
                         rcases List.mem_map.mp hw with ⟨z, hz, rfl⟩
                         rw [hvalJ z hz, hspD_val z, ← hinv1.list_eq w (by rw [hv1]; exact hv)]
                         exact List.mem_map.mpr ⟨z, hpermJ.mem_iff.mp hz, rfl⟩
                       · simpa [h] using hw
                     exact hinv.ord_unique.unique_v (hmem_ord w1 h1) (hmem_ord w2 h2)⟩
                next_le := hinv1.next_le
                clean := hokJ.clean
                null_node := hokJ.null_node
                tree_inv := fun w hw => by
                  dsimp only [S2] at hw ⊢
                  by_cases h : w = v
                  · subst h; simpa using hokJ.inv
                  · simp only [Function.update_of_ne h]
                    exact ⟨(hinv1.tree_inv w hw).nodup, SplayState.SubtreeInv_agree (hinv1.tree_inv w hw).sub fun x hx =>
                      (hspJ_out x (hinv1.disj_trees w v h x hx)).symm⟩
                tree_out := fun w hw => by
                  dsimp only [S2] at hw ⊢
                  rw [Function.update_of_ne (by omega)]; exact hinv1.tree_out w hw
                vRoot_eq := fun w hw => by dsimp only [S2] at hw ⊢; by_cases h : w = v <;> simp [h, hinv1.vRoot_eq w hw]
                root_ppar := fun w hw hne => by
                  dsimp only [S2] at hw hne ⊢
                  by_cases h : w = v
                  · subst h; simp only [Function.update_self] at hne ⊢; exact hppJ hne
                  · simp only [Function.update_of_ne h] at hne ⊢
                    rw [hspJ_out _ (hinv1.disj_trees w v h _ (AuxTree.rootId_mem hne))]
                    exact hinv1.root_ppar w hw hne
                list_eq := fun w hw => by
                  dsimp only [S2, applyOrdEdit] at hw ⊢
                  by_cases h : w = v
                  · subst h; simpa using hlist_rot
                  · simp only [Function.update_of_ne h]
                    rw [← hinv1.list_eq w hw]
                    exact List.map_congr_left fun x hx => by rw [hspJ_out x (hinv1.disj_trees w v h x hx)]
                disj_trees := fun w1 w2 hne x h1 h2 => by
                  dsimp only [S2] at h1 h2
                  have h1' : x ∈ (S1.trees w1).toList := by
                    by_cases h : w1 = v
                    · subst h; simp only [Function.update_self] at h1; exact hpermJ.mem_iff.mp h1
                    · simpa [h] using h1
                  have h2' : x ∈ (S1.trees w2).toList := by
                    by_cases h : w2 = v
                    · subst h; simp only [Function.update_self] at h2; exact hpermJ.mem_iff.mp h2
                    · simpa [h] using h2
                  exact hinv1.disj_trees w1 w2 hne x h1' h2'
                free_nodup := hinv1.free_nodup
                free_disj := fun w hw x hxf hxt => by
                  dsimp only [S2] at hw hxf hxt
                  by_cases h : w = v
                  · subst h; simp only [Function.update_self] at hxt
                    exact hinv1.free_disj w hw x hxf (hpermJ.mem_iff.mp hxt)
                  · simp only [Function.update_of_ne h] at hxt; exact hinv1.free_disj w hw x hxf hxt
                free_chain := hinv1.free_chain
                nodes_range := fun x => by
                  dsimp only [S2]; rw [← hinv1.nodes_range x]
                  constructor <;> rintro (hfl | ⟨w, hw, hxw⟩)
                  · exact Or.inl hfl
                  · by_cases h : w = v
                    · subst h; simp only [Function.update_self] at hxw
                      exact Or.inr ⟨w, hw, hpermJ.mem_iff.mp hxw⟩
                    · simp only [Function.update_of_ne h] at hxw; exact Or.inr ⟨w, hw, hxw⟩
                  · exact Or.inl hfl
                  · by_cases h : w = v
                    · subst h; exact Or.inr ⟨w, hw, by simp only [Function.update_self]; exact hpermJ.mem_iff.mpr hxw⟩
                    · exact Or.inr ⟨w, hw, by simpa [h] using hxw⟩
                key_lt := fun w hw x hxw => by
                  dsimp only [S2] at hw hxw
                  by_cases h : w = v
                  · subst h; simp only [Function.update_self] at hxw
                    rw [hvalJ x hxw, hspD_val x]; exact hinv1.key_lt w hw x (hpermJ.mem_iff.mp hxw)
                  · simp only [Function.update_of_ne h] at hxw
                    rw [hspJ_out x (hinv1.disj_trees w v h x hxw)]; exact hinv1.key_lt w hw x hxw
                eNode_spec := fun j hj => by
                  dsimp only [S2] at hj ⊢
                  rcases hinv1.eNode_spec j hj with ⟨h0, hnone'⟩ | ⟨w, hw, hmem', hval'⟩
                  · left; refine ⟨h0, fun w hw x hxw heq => ?_⟩
                    by_cases h : w = v
                    · subst h; simp only [Function.update_self] at hxw
                      rw [hvalJ x hxw, hspD_val x] at heq
                      exact hnone' w hw x (hpermJ.mem_iff.mp hxw) heq
                    · simp only [Function.update_of_ne h] at hxw
                      rw [hspJ_out x (hinv1.disj_trees w v h x hxw)] at heq
                      exact hnone' w hw x hxw heq
                  · right; refine ⟨w, hw, ?_, ?_⟩
                    · by_cases h : w = v
                      · subst h; simp only [Function.update_self]; exact hpermJ.mem_iff.mpr hmem'
                      · simpa [h] using hmem'
                    · by_cases h : w = v
                      · subst h; rw [hvalJ _ (hpermJ.mem_iff.mpr hmem'), hspD_val _]; exact hval'
                      · rw [hspJ_out _ (hinv1.disj_trees w v h _ hmem')]; exact hval' }
            have hfr2 : OrdFrame b S.vCap S.eCap heap stSR.mem st17.mem := by
              have h1 : ∀ a, ¬ ordFoot b S.vCap S.eCap a → st17.mem a = stSR.mem a := fun a ha => by
                have hnot1 : ¬ InOrdNodes nb S1.nextNode a := fun h =>
                  ha ⟨by unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega,
                      by unfold InOrdNodes at h; have := ordNodesBase_end b S.vCap S.eCap; have := hinv1.next_le; rw [he1] at this; rw [hnb] at h; omega⟩
                have hne_vr : a ≠ ordVRootBase b + v := fun h => ha (h ▸ ordFoot_vRoot hv)
                dsimp only [st17]
                rw [Function.update_of_ne hne_vr, hfrJ a hnot1, hm3_out a hnot1]
              exact ⟨fun a ha => (h1 a (fun hf => by unfold ordFoot at hf; omega)).trans (hfr1.1 a ha),
                     fun a _ hnf => h1 a hnf⟩
            have harena2 : OrdArenaAt b S2 st17.mem := by
              have hnot_vr : ¬ InOrdNodes nb S1.nextNode (ordVRootBase b + v) :=
                hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)
              have hhdr : ∀ j < 7, st17.mem (b + j) = stSR.mem (b + j) := fun j hj => by
                dsimp only [st17]
                rw [Function.update_of_ne (by unfold ordVRootBase; omega),
                    hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega)),
                    hm3_out _ (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))]
              exact
                { hdr_vCap := (hhdr 0 (by omega)).trans harena1.hdr_vCap
                  hdr_eCap := (hhdr 1 (by omega)).trans harena1.hdr_eCap
                  hdr_vRoot := (hhdr 2 (by omega)).trans harena1.hdr_vRoot
                  hdr_eNode := (hhdr 3 (by omega)).trans harena1.hdr_eNode
                  hdr_nodes := (hhdr 4 (by omega)).trans harena1.hdr_nodes
                  hdr_next := (hhdr 5 (by omega)).trans harena1.hdr_next
                  hdr_free := (hhdr 6 (by omega)).trans harena1.hdr_free
                  vRoot_at := fun w hw => by
                    dsimp only [S2, st17] at hw ⊢
                    by_cases h : w = v
                    · subst h; simp
                    · rw [Function.update_of_ne (by omega), Function.update_of_ne h,
                          hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)),
                          hm3_out _ (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))]
                      exact harena1.vRoot_at w hw
                  eNode_at := fun j hj => by
                    dsimp only [S2, st17] at hj ⊢
                    rw [Function.update_of_ne (by unfold ordVRootBase ordENodeBase; omega),
                        hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega)),
                        hm3_out _ (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))]
                    exact harena1.eNode_at j hj
                  nodes_at := by
                    dsimp only [S2, st17]; rw [hv1, he1]
                    exact hnJ.congr fun a ha => Function.update_of_ne (fun (h : a = ordVRootBase b + v) => hnot_vr (h ▸ ha)) _ _ }
            have hphi_det : (AuxTree.node u .leaf R).treePhi (fun _ => 0) + Lt.treePhi (fun _ => 0) ≤
                (S1.trees v).treePhi (fun _ => 0) := by
              rw [htv_eq]
              have hrk_le : (AuxTree.node u .leaf R).rank (fun _ => 0) ≤
                  (AuxTree.node u Lt R).rank (fun _ => 0) := by
                unfold AuxTree.rank
                rw [treeSize_zero_eq_countNodes, treeSize_zero_eq_countNodes]
                exact Nat.log_mono_right (by simp [AuxTree.countNodes])
              simp only [AuxTree.treePhi]; omega
            have hphi2_upd : sumTreePhi S2 + (S1.trees v).treePhi (fun _ => 0) =
                sumTreePhi S1 + tJ.treePhi (fun _ => 0) := by
              have h := sumTreePhi_update (S := S1) (S' := S2) (by rw [hv1]; exact hv) rfl
                (fun u _ huv => Function.update_of_ne huv _ _)
              rw [show S2.trees v = tJ from Function.update_self v tJ S1.trees] at h; exact h
            have hcnt2_upd : sumCountNodes S2 = sumCountNodes S1 := by
              have h1 := sumCountNodes_update (S := S1) (S' := S2) (by rw [hv1]; exact hv) rfl
                (fun u _ huv => Function.update_of_ne huv _ _)
              rw [show S2.trees v = tJ from Function.update_self v tJ S1.trees] at h1
              have h2 : tJ.countNodes = (S1.trees v).countNodes := by
                rw [hcntJ, htv_eq]; simp [AuxTree.countNodes]; omega
              omega
            refine ⟨.returned 0, st17, _,
              ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_true hc1 Nat.one_ne_zero
                (ord_runs_cond_true hc2 Nat.one_ne_zero (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6
                  (ord_runs_cond_true hc3 hu_nz (ord_runs_seq_normal hcallSR
                    (ord_runs_cond_true hc4 Nat.one_ne_zero
                      (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9
                        (ord_runs_seq_normal ha10 (ord_runs_cond_true hc5 hL_nz hrot_branch)))))))))))),
              S2, hinv2, harena2, hfr1.trans hfr2, hv1, he1, ?_⟩
            have hphi2_mul : cJ + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S2 ≤
                ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 + ORD_JOIN_AMORT * ordStoreLog S.eCap := by
              unfold ordPhi; rw [hcnt2_upd]
              have h1 : ORD_PHI_WEIGHT * sumTreePhi S2 + ORD_PHI_WEIGHT * (S1.trees v).treePhi (fun _ => 0) =
                  ORD_PHI_WEIGHT * sumTreePhi S1 + ORD_PHI_WEIGHT * tJ.treePhi (fun _ => 0) := by
                have := congrArg (ORD_PHI_WEIGHT * ·) hphi2_upd; ring_nf at this ⊢; exact this
              have h2 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi_det
              omega
            unfold ORD_JOIN_AMORT at hphi2_mul
            unfold ORD_ROT_AMORT at ⊢
            simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
              argsSize_cons, argsSize_nil] at *
            omega
        · -- u is in a different vertex w0 ≠ v: no-op
          have hc4 : (Expr.bin .eq (.reg 7) (.bin .add (.reg 1) (.const 1))).eval w st5 = some 0 :=
            Expr.eval_eq_false (Expr.eval_reg_of_eq (v := w0 + 1) (by simp [st5]))
              (Expr.eval_add (Expr.eval_reg_of_eq (v := v) (by simp [st5, st4, st3, st2, st1, st0, startState]))
                (Expr.eval_const (by omega)) (by omega)) (by omega) (by omega)
          have hret : Runs w p ω (.ret (.const 0)) st5 (.returned 0) st5 _ :=
            runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
          have hnm : endOfKey keyY ∉ ord v := fun h => by
            have hw0_m : endOfKey keyY ∈ ord w0 := by
              rw [← hinv.list_eq w0 hw0]; exact List.mem_map.mpr ⟨u, hu_mem, by rw [hu_val]⟩
            exact hwv (hinv.ord_unique.unique_v h hw0_m)
          refine ⟨.returned 0, st5, _,
            ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_true hc1 Nat.one_ne_zero
              (ord_runs_cond_true hc2 Nat.one_ne_zero (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6
                (ord_runs_cond_true hc3 hu_nz (ord_runs_seq_normal hcallSR
                  (ord_runs_cond_false hc4 hret)))))))),
            S1, by rwa [hnoop_eq hnm], harena1, hfr1, hv1, he1, ?_⟩
          unfold ORD_ROT_AMORT
          simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
            argsSize_cons, argsSize_nil] at *
          omega
    · -- keyY ≥ 2 * eCap: no-op
      have hc2 : (Expr.bin .lt (.reg 2) (.bin .add (.reg 4) (.reg 4))).eval w st2 = some 0 :=
        Expr.eval_lt_false (Expr.eval_reg_of_eq (v := keyY) (by simp [st2, st1, st0, startState]))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st2]))
            (Expr.eval_reg_of_eq (v := S.eCap) (by simp [st2])) (by omega))
          (by omega) (by omega)
      have hret : Runs w p ω (.ret (.const 0)) st2 (.returned 0) st2 _ :=
        runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
      have hnm : endOfKey keyY ∉ ord v := fun h => by
        have := hinv.ord_unique.edge_lt h; simp [endOfKey] at this; omega
      refine ⟨.returned 0, st2, _,
        ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_true hc1 Nat.one_ne_zero
          (ord_runs_cond_false hc2 hret))),
        S, by rwa [hnoop_eq hnm], harena, OrdFrame.refl hz, rfl, rfl, ?_⟩
      unfold ORD_ROT_AMORT
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  · -- v ≥ vCap: no-op
    have hc1 : (Expr.bin .lt (.reg 1) (.reg 3)).eval w st2 = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq (v := v) (by simp [st2, st1, st0, startState]))
        (Expr.eval_reg_of_eq (v := S.vCap) (by simp [st2, st1])) (by omega) (by omega)
    have hret : Runs w p ω (.ret (.const 0)) st2 (.returned 0) st2 _ :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hnm : endOfKey keyY ∉ ord v := by
      rw [hinv.ord_unique.eq_nil_of_ge (by omega)]; exact List.not_mem_nil
    refine ⟨.returned 0, st2, _,
      ord_runs_seq_normal ha3 (ord_runs_seq_normal ha4 (ord_runs_cond_false hc1 hret)),
      S, by rwa [hnoop_eq hnm], harena, OrdFrame.refl hz, rfl, rfl, ?_⟩
    unfold ORD_ROT_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.SparseCore.Program
