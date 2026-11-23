module

public import MinCostFlow.SparseCore.Program.OrdStoreMoveSame
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Pass 7: Full Reassembly (`v ≠ v'` branch and dispatch)

This file verifies the `v ≠ v'` branch (`ordMoveFinishDiffBody`) and combines it with
`ordMoveFinishSameBody` into `ordMoveFinishBody` and `ordMoveFinishBody_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-- The `v ≠ v'` branch of Pass 7 of `moveEnds`. -/
def ordMoveFinishDiffBody (joinProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 0))
    (.cond (.reg 13)
      (.assign 15 (.load (.bin .add (.reg 14) (.reg 2))) ;;
       .call 16 joinProc [.reg 9, .reg 15, .reg 13, .bin .add (.reg 2) (.const 1)] ;;
       .store (.bin .add (.reg 14) (.reg 2)) (.reg 16))
      .nop)
    (.assign 15 (.load (.bin .add (.reg 14) (.reg 1))) ;;
     .store (.bin .add (.reg 14) (.reg 1)) (.reg 13) ;;
     .cond (.reg 13)
       (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 3))
         (.bin .add (.reg 1) (.const 1)))
       .nop ;;
     .cond (.reg 15)
       (.assign 16 (.load (.bin .add (.reg 14) (.reg 2))) ;;
        .call 17 joinProc [.reg 9, .reg 16, .reg 15, .bin .add (.reg 2) (.const 1)] ;;
        .store (.bin .add (.reg 14) (.reg 2)) (.reg 17))
       .nop)

/-- Pass 7 of `moveEnds`: reassembles `tRem` and `tSel` across the four `(v = v', comp)` cases. -/
def ordMoveFinishBody (joinProc freeTreeProc : ℕ) : Stmt :=
  .assign 14 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .cond (.bin .eq (.reg 1) (.reg 2))
    (ordMoveFinishSameBody freeTreeProc)
    (ordMoveFinishDiffBody joinProc)

theorem ordMoveFinishDiffBody_noRand (jP : ℕ) : (ordMoveFinishDiffBody jP).NoRand := by
  simp [ordMoveFinishDiffBody, Stmt.NoRand]

theorem ordMoveFinishBody_noRand (jP ftP : ℕ) : (ordMoveFinishBody jP ftP).NoRand := by
  simp [ordMoveFinishBody, Stmt.NoRand, ordMoveFinishSameBody_noRand, ordMoveFinishDiffBody_noRand]

private theorem ordMoveFinishDiff_runs
    {w b v v' scratch rotProc stepProc splayProc walkProc joinProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc)) (ω : ℕ → Bool)
    {st1 : State} {ord : ℕ → List End} {S : OrdStoreState} {sel : Finset End} {comp : Bool}
    {sp : SplayState ℕ Unit Unit} {tRem : AuxTree} {selNodes : List ℕ}
    (hinv : OrdInv ord S) (hv : v < S.vCap) (hv' : v' < S.vCap) (hvv : v ≠ v')
    (huniq' : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit ord (.moveEnds v v' sel comp)))
    (hpart_v : ∀ x, x ∈ (S.trees v).toList ↔ x ∈ tRem.toList ∨ x ∈ (leftSpine selNodes).toList)
    (hdisj_rs : ∀ x ∈ tRem.toList, x ∉ (leftSpine selNodes).toList)
    (hcnt_part : tRem.countNodes + (leftSpine selNodes).countNodes = (S.trees v).countNodes)
    (hmap_sel : (leftSpine selNodes).toList.map (fun x => endOfKey (sp.nodes x).val) =
      (ord v).filter (fun e => decide (e ∈ sel)))
    (hmap_rem : tRem.toList.map (fun x => endOfKey (sp.nodes x).val) =
      (ord v).filter (fun e => !decide (e ∈ sel)))
    (htSel_phi : (leftSpine selNodes).treePhi (fun _ => 0) ≤ selNodes.length * ordStoreLog S.eCap)
    (hokR : OrdTreeOk S.nextNode sp tRem)
    (hppR : tRem ≠ .leaf → (sp.nodes tRem.rootId).ppar = v + 1)
    (hokS : OrdTreeOk S.nextNode sp (leftSpine selNodes))
    (hout_v : ∀ x ∉ (S.trees v).toList, sp.nodes x = S.splay.nodes x)
    (hval_v : ∀ x ∈ (S.trees v).toList, (sp.nodes x).val = (S.splay.nodes x).val)
    (hhdr : st1.mem b = S.vCap ∧ st1.mem (b + 1) = S.eCap ∧ st1.mem (b + 2) = ordVRootBase b ∧
            st1.mem (b + 3) = ordENodeBase b S.vCap ∧ st1.mem (b + 4) = ordNodesBase b S.vCap S.eCap ∧
            st1.mem (b + 5) = S.nextNode ∧ st1.mem (b + 6) = S.freeHead)
    (hvr_at : ∀ u < S.vCap, st1.mem (ordVRootBase b + u) = if u = v then tRem.rootId else S.vRoot u)
    (hen_at : ∀ k < 2 * S.eCap, st1.mem (ordENodeBase b S.vCap + k) = S.eNode k)
    (hnodes : OrdNodesAt st1.mem (ordNodesBase b S.vCap S.eCap) S.nextNode sp S.nextFree)
    (hz : ZeroFrom st1.mem scratch)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr1 : st1.regs 1 = v) (hr2 : st1.regs 2 = v')
    (hr3 : st1.regs 3 = if comp then 1 else 0)
    (hr9 : st1.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr13 : st1.regs 13 = (leftSpine selNodes).rootId)
    (hr14 : st1.regs 14 = ordVRootBase b) :
    ∃ st' c, ∃ S' : OrdStoreState,
      Runs w p ω (ordMoveFinishDiffBody joinProc) st1 .normal st' c ∧
      OrdInv (applyOrdEdit ord (.moveEnds v v' sel comp)) S' ∧
      OrdArenaAt b S' st'.mem ∧
      OrdFrame b S.vCap S.eCap scratch st1.mem st'.mem ∧
      S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
      c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' + ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_PHI_WEIGHT * tRem.treePhi (fun _ => 0) +
          (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  set vr := ordVRootBase b with hvr_def
  set tSel : AuxTree := leftSpine selNodes with htSel_def
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ scratch := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb]; omega
  have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S.nextNode a := fun a ha h => by unfold InOrdNodes at h; omega
  have hnd_in_foot : ∀ a, InOrdNodes nb S.nextNode a → ordFoot b S.vCap S.eCap a := fun a h => by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le
    unfold InOrdNodes at h; unfold ordFoot; rw [hnb] at h; unfold ordNodesBase at h; unfold ordArenaSize at *; omega
  have hvr_in_foot : ∀ u < S.vCap, ordFoot b S.vCap S.eCap (vr + u) := fun u hu => by
    unfold ordFoot; rw [hvr_def]; unfold ordVRootBase ordArenaSize; omega
  have hok_v' : OrdTreeOk S.nextNode sp (S.trees v') :=
    { null_node := hokR.null_node
      clean := hokR.clean
      inv := ⟨(hinv.tree_inv v' hv').nodup, SplayState.SubtreeInv_agree (hinv.tree_inv v' hv').sub fun x hx =>
        (hout_v x (fun hxv => hinv.disj_trees v' v (Ne.symm hvv) x hx hxv)).symm⟩
      mem_le := fun x hx => (hinv.live_le_nextNode hv' hx).2
      count_le := (hinv.ordTreeOk hv').count_le }
  have hm_vr_v' : st1.mem (vr + v') = (S.trees v').rootId := by
    have h := hvr_at v' hv'; simp only [Ne.symm hvv, ↓reduceIte] at h
    rw [← hinv.vRoot_eq v' hv']; exact h
  cases comp with
  | false =>
    have hcc : (Expr.bin .eq (.reg 3) (.const 0)).eval w st1 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [hr3]))
        (Expr.eval_const (by omega)) rfl (by omega)
    have hjoin_b3 : ∃ stF cF spF tJ,
        Runs w p ω
          (.cond (.reg 13)
            (.assign 15 (.load (.bin .add (.reg 14) (.reg 2))) ;;
             .call 16 joinProc [.reg 9, .reg 15, .reg 13, .bin .add (.reg 2) (.const 1)] ;;
             .store (.bin .add (.reg 14) (.reg 2)) (.reg 16)) .nop) st1 .normal stF cF ∧
        OrdNodesAt stF.mem nb S.nextNode spF S.nextFree ∧
        stF.mem (vr + v') = tJ.rootId ∧
        (∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ vr + v' → stF.mem a = st1.mem a) ∧
        OrdTreeOk S.nextNode spF tJ ∧
        tJ.toList = (S.trees v').toList ++ tSel.toList ∧
        tJ.countNodes = (S.trees v').countNodes + tSel.countNodes ∧
        (tJ ≠ .leaf → (spF.nodes tJ.rootId).ppar = v' + 1) ∧
        (∀ x ∈ tJ.toList, (spF.nodes x).val = (sp.nodes x).val) ∧
        (∀ x, x ∉ (S.trees v').toList → x ∉ tSel.toList → spF.nodes x = sp.nodes x) ∧
        cF + ORD_PHI_WEIGHT * tJ.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * ((S.trees v').treePhi (fun _ => 0) + tSel.treePhi (fun _ => 0)) +
            ORD_JOIN_AMORT * ordStoreLog S.eCap + 50 := by
      by_cases hS0 : tSel.rootId = 0
      · have htSel_leaf : tSel = .leaf := by
          cases hts : tSel with
          | leaf => rfl
          | node sid sl sr =>
            exfalso; simp only [hts, AuxTree.rootId] at hS0
            exact SplayState.SubtreeInv_nonZero hokS.inv.sub (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)) hS0
        have hc : (Expr.reg 13).eval w st1 = some 0 := Expr.eval_reg_of_eq (hr13.trans hS0)
        refine ⟨st1, _, sp, S.trees v', ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          hnodes, hm_vr_v', fun _ _ _ => rfl, hok_v', by simp [htSel_leaf, AuxTree.toList],
          by simp [htSel_leaf, AuxTree.countNodes],
          fun hne => by
            rw [hout_v _ (fun hxv => hinv.disj_trees v' v (Ne.symm hvv) _ (AuxTree.rootId_mem hne) hxv)]
            exact hinv.root_ppar v' hv' hne,
          fun _ _ => rfl, fun _ _ _ => rfl, by simp [Expr.size_reg, htSel_leaf, AuxTree.treePhi]; omega⟩
      · have hc : (Expr.reg 13).eval w st1 = some tSel.rootId := Expr.eval_reg_of_eq hr13
        have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 14) (.reg 2)))) st1 .normal
            { st1 with regs := Function.update st1.regs 15 (S.trees v').rootId } _ :=
          runs_assign_iff.mpr ⟨(S.trees v').rootId, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq hr14) (Expr.eval_reg_of_eq hr2)
            (by rw [hvr_def]; unfold ordVRootBase; omega)) hm_vr_v', rfl, rfl, rfl⟩
        set st2 : State := { st1 with regs := Function.update st1.regs 15 (S.trees v').rootId }
        have hdisj_v's : ∀ x ∈ (S.trees v').toList, x ∉ tSel.toList := fun x hx hs =>
          hinv.disj_trees v' v (Ne.symm hvv) x hx ((hpart_v x).mpr (Or.inr hs))
        have hsum_le : (S.trees v').countNodes + tSel.countNodes ≤ S.nextNode :=
          card_disj_le_nextNode (hinv.tree_inv v' hv').nodup hokS.inv.nodup hdisj_v's
            (fun x hx => hinv.live_le_nextNode hv' hx)
            (fun x hx => hinv.live_le_nextNode hv ((hpart_v x).mpr (Or.inr hx)))
        obtain ⟨oJ, stJ, cJ, hrunJ, spJ, tJ, hoJ, hnJ, hfrJ, hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, hphiJ⟩ :=
          ordJoinBody_runs hrot hstep hsplay hwalk ω hnodes hok_v' hokS rfl rfl hdisj_v's hsum_le
            hinv.next_le (by omega) (by omega) hwide (owner := v' + 1) (pos := st2.pos)
        have hcallJ : Runs w p ω (.call 16 joinProc [.reg 9, .reg 15, .reg 13, .bin .add (.reg 2) (.const 1)]) st2 .normal
            { stJ with regs := Function.update st2.regs 16 tJ.rootId }
            (argsSize [.reg 9, .reg 15, .reg 13, .bin .add (.reg 2) (.const 1)] + cJ + 1) :=
          runs_call_iff.mpr ⟨[nb, (S.trees v').rootId, tSel.rootId, v' + 1], ordJoinBody walkProc, oJ, stJ, cJ,
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2, hr9]))
              (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2]))
                (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2, hr13]))
                  (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, hr2]))
                    (Expr.eval_const (by omega)) (by omega)) (evalArgs_nil _ _)))),
            hjoin, hrunJ, rfl, by simp [hoJ], rfl⟩
        set st3 : State := { stJ with regs := Function.update st2.regs 16 tJ.rootId }
        have hs_v' : Runs w p ω (.store (.bin .add (.reg 14) (.reg 2)) (.reg 16)) st3 .normal
            { st3 with mem := Function.update stJ.mem (vr + v') tJ.rootId } _ :=
          runs_store_iff.mpr ⟨vr + v', tJ.rootId, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st3, st2, hr14]))
            (Expr.eval_reg_of_eq (by simp [st3, st2, hr2])) (by rw [hvr_def]; unfold ordVRootBase; omega),
            Expr.eval_reg_of_eq (by simp [st3]), rfl, rfl, rfl⟩
        have hnot_vrv' : ¬ InOrdNodes nb S.nextNode (vr + v') :=
          hnot_nd _ (by rw [hvr_def, hnb]; unfold ordVRootBase ordNodesBase; omega)
        refine ⟨_, _, spJ, tJ, ord_runs_cond_true hc hS0 (ord_runs_seq_normal ha15 (ord_runs_seq_normal hcallJ hs_v')),
          hnJ.congr (fun a ha => Function.update_of_ne (fun (h : a = vr + v') => hnot_vrv' (h ▸ ha)) _ _),
          by simp, fun a h1 h2 => (Function.update_of_ne h2 _ _).trans (hfrJ a h1),
          hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, ?_⟩
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
          argsSize_cons, argsSize_nil] at *
        omega
    obtain ⟨stF, cF, spF, tJ, hrunF, hnF, hvrF, hfrF, hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, hphiF⟩ := hjoin_b3
    have hokR_F : OrdTreeOk S.nextNode spF tRem :=
      { null_node := hokJ.null_node
        clean := hokJ.clean
        inv := ⟨hokR.inv.nodup, SplayState.SubtreeInv_agree hokR.inv.sub fun x hx =>
          (houtJ x (fun hv' => hinv.disj_trees v v' hvv x ((hpart_v x).mpr (Or.inl hx)) hv') (hdisj_rs x hx)).symm⟩
        mem_le := hokR.mem_le
        count_le := hokR.count_le }
    set S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := S.freeHead,
        vRoot := Function.update (Function.update S.vRoot v tRem.rootId) v' tJ.rootId,
        eNode := S.eNode, splay := spF, nextFree := S.nextFree,
        trees := Function.update (Function.update S.trees v tRem) v' tJ, freeList := S.freeList }
    have hinv' : OrdInv (applyOrdEdit ord (.moveEnds v v' sel false)) S' :=
      moveFinish_diff_inv hinv hv hv' hvv huniq' hpart_v hdisj_rs hokR_F
        (fun hne => by
          have hr := AuxTree.rootId_mem hne
          rw [houtJ _ (fun hv' => hinv.disj_trees v v' hvv _ ((hpart_v _).mpr (Or.inl hr)) hv') (hdisj_rs _ hr)]
          exact hppR hne)
        (by
          have h1 : tRem.toList.map (fun x => endOfKey (spF.nodes x).val) =
              tRem.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by
              rw [houtJ x (fun hv' => hinv.disj_trees v v' hvv x ((hpart_v x).mpr (Or.inl hx)) hv') (hdisj_rs x hx)]
          rw [h1, hmap_rem]; rfl)
        hokJ hppJ htJ_list
        (by
          have h1 : tSel.toList.map (fun x => endOfKey (spF.nodes x).val) =
              tSel.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_right _ hx)]
          rw [h1, hmap_sel]; rfl)
        (fun x hxv hxv' => (houtJ x hxv' (fun hs => hxv ((hpart_v x).mpr (Or.inr hs)))).trans (hout_v x hxv))
        (fun x hx => by
          rcases hx with hxv | hxv'
          · rcases (hpart_v x).mp hxv with hr | hs
            · rw [houtJ x (fun h => hinv.disj_trees v v' hvv x hxv h) (hdisj_rs x hr)]; exact hval_v x hxv
            · rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_right _ hs)]; exact hval_v x hxv
          · rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_left _ hxv'),
              hout_v x (fun h => hinv.disj_trees v' v (Ne.symm hvv) x hxv' h)])
    have harena' : OrdArenaAt b S' stF.mem :=
      { hdr_vCap := (hfrF b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.1
        hdr_eCap := (hfrF (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.1
        hdr_vRoot := (hfrF (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.1
        hdr_eNode := (hfrF (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.1
        hdr_nodes := (hfrF (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.1
        hdr_next := (hfrF (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.2.1
        hdr_free := (hfrF (b + 6) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.2.2
        vRoot_at := fun u hu => by
          dsimp only [S'] at hu
          by_cases h1 : u = v'
          · subst h1; simpa [S', hvr_def] using hvrF
          · rw [hfrF (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
              (by rw [hvr_def]; omega), hvr_at u hu]
            by_cases h2 : u = v
            · subst h2; simp [S', Function.update_of_ne h1]
            · simp [S', h2, Function.update_of_ne h1, Function.update_of_ne h2]
        eNode_at := fun k hk => by
          dsimp only [S'] at hk
          exact (hfrF (ordENodeBase b S.vCap + k)
            (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase ordENodeBase; omega)).trans (hen_at k hk)
        nodes_at := hnF }
    have hframe' : OrdFrame b S.vCap S.eCap scratch st1.mem stF.mem :=
      ⟨fun a ha => (hfrF a (fun h => by unfold InOrdNodes at h; omega)
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans (hz a ha),
       fun a _ hnf => hfrF a (fun h => hnf (hnd_in_foot a h)) (fun h => hnf (by rw [h]; exact hvr_in_foot v' hv'))⟩
    have hphi_upd := sumTreePhi_update2 (S := S) (S' := S') hv hv' hvv rfl
      (fun u _ h1 h2 => by simp [S', Function.update_of_ne h1, Function.update_of_ne h2])
    rw [show S'.trees v = tRem by simp [S', Function.update_of_ne hvv],
        show S'.trees v' = tJ by simp [S']] at hphi_upd
    have hcnt_upd := sumCountNodes_update2 (S := S) (S' := S') hv hv' hvv rfl
      (fun u _ h1 h2 => by simp [S', Function.update_of_ne h1, Function.update_of_ne h2])
    rw [show S'.trees v = tRem by simp [S', Function.update_of_ne hvv],
        show S'.trees v' = tJ by simp [S']] at hcnt_upd
    refine ⟨stF, _, S', ord_runs_cond_true hcc Nat.one_ne_zero hrunF, hinv', harena', hframe', rfl, rfl, ?_⟩
    have hmul_sel := Nat.mul_le_mul_left 1000 htSel_phi
    have h160 : 160 ≤ 160 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 160 hlog
    have hsplit : (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap =
        1000 * (selNodes.length * ordStoreLog S.eCap) + ORD_JOIN_AMORT * ordStoreLog S.eCap + 160 * ordStoreLog S.eCap := by ring
    unfold ORD_PHI_WEIGHT at hphiF
    unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega
  | true =>
    have hcc : (Expr.bin .eq (.reg 3) (.const 0)).eval w st1 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (v := 1) (by simp [hr3]))
        (Expr.eval_const (by omega)) (by omega) (by omega)
    have hm_vr_v : st1.mem (vr + v) = tRem.rootId := by simpa [hvr_def] using hvr_at v hv
    have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 14) (.reg 1)))) st1 .normal
        { st1 with regs := Function.update st1.regs 15 tRem.rootId } _ :=
      runs_assign_iff.mpr ⟨tRem.rootId, Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq hr14) (Expr.eval_reg_of_eq hr1)
        (by rw [hvr_def]; unfold ordVRootBase; omega)) hm_vr_v, rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 15 tRem.rootId }
    have hs_v : Runs w p ω (.store (.bin .add (.reg 14) (.reg 1)) (.reg 13)) st2 .normal
        { st2 with mem := Function.update st1.mem (vr + v) tSel.rootId } _ :=
      runs_store_iff.mpr ⟨vr + v, tSel.rootId, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, hr14]))
        (Expr.eval_reg_of_eq (by simp [st2, hr1])) (by rw [hvr_def]; unfold ordVRootBase; omega),
        Expr.eval_reg_of_eq (by simp [st2, hr13]), rfl, rfl, rfl⟩
    set st3 : State := { st2 with mem := Function.update st1.mem (vr + v) tSel.rootId }
    have hnot_vrv : ¬ InOrdNodes nb S.nextNode (vr + v) :=
      hnot_nd _ (by rw [hvr_def, hnb]; unfold ordVRootBase ordNodesBase; omega)
    have hn3 : OrdNodesAt st3.mem nb S.nextNode sp S.nextFree :=
      hnodes.congr fun a ha => Function.update_of_ne (fun (h : a = vr + v) => hnot_vrv (h ▸ ha)) _ _
    obtain ⟨stP, cP, hrunP, hregsP, hnP, hfrP, hokS_P, hppS_P, hspP_out, hspP_val, hcP⟩ :=
      ordMoveFinish_setPpar (p := p) (nb := nb) (v := v) ω (stM := st3) (by simp [st3, st2, hr1])
        (by simp [st3, st2, hr9, hnb]) (by simp [st3, st2, hr13, htSel_def]) hn3 hokS (by omega) (by omega) hwide
    set spP := if tSel.rootId = 0 then sp else sp.setPpar tSel.rootId (v + 1)
    have hspP_agree_notS : ∀ x, x ∉ tSel.toList → spP.nodes x = sp.nodes x := fun x hx => by
      by_cases hx0 : x = 0
      · rw [hx0, hokS_P.null_node, hokS.null_node]
      · refine hspP_out x ?_
        cases hts : tSel with
        | leaf => simp [hts, AuxTree.rootId]; exact hx0
        | node sid sl sr =>
          intro h; simp only [hts, AuxTree.rootId] at h
          exact hx (by rw [h, hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp))
    have hokR_P : OrdTreeOk S.nextNode spP tRem :=
      { null_node := hokS_P.null_node
        clean := hokS_P.clean
        inv := ⟨hokR.inv.nodup, SplayState.SubtreeInv_agree hokR.inv.sub fun x hx =>
          (hspP_agree_notS x (hdisj_rs x hx)).symm⟩
        mem_le := hokR.mem_le
        count_le := hokR.count_le }
    have hok_v'_P : OrdTreeOk S.nextNode spP (S.trees v') :=
      { null_node := hokS_P.null_node
        clean := hokS_P.clean
        inv := ⟨hok_v'.inv.nodup, SplayState.SubtreeInv_agree hok_v'.inv.sub fun x hx =>
          (hspP_agree_notS x (fun hs => hinv.disj_trees v' v (Ne.symm hvv) x hx ((hpart_v x).mpr (Or.inr hs)))).symm⟩
        mem_le := hok_v'.mem_le
        count_le := hok_v'.count_le }
    have hmP_vrv' : stP.mem (vr + v') = (S.trees v').rootId := by
      rw [hfrP _ (hnot_nd _ (by rw [hvr_def, hnb]; unfold ordVRootBase ordNodesBase; omega))]
      dsimp only [st3]
      rw [Function.update_of_ne (by omega)]
      exact hm_vr_v'
    have hjoin_b4 : ∃ stF cF spF tJ,
        Runs w p ω
          (.cond (.reg 15)
            (.assign 16 (.load (.bin .add (.reg 14) (.reg 2))) ;;
             .call 17 joinProc [.reg 9, .reg 16, .reg 15, .bin .add (.reg 2) (.const 1)] ;;
             .store (.bin .add (.reg 14) (.reg 2)) (.reg 17)) .nop) stP .normal stF cF ∧
        OrdNodesAt stF.mem nb S.nextNode spF S.nextFree ∧
        stF.mem (vr + v') = tJ.rootId ∧
        (∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ vr + v' → stF.mem a = stP.mem a) ∧
        OrdTreeOk S.nextNode spF tJ ∧
        tJ.toList = (S.trees v').toList ++ tRem.toList ∧
        tJ.countNodes = (S.trees v').countNodes + tRem.countNodes ∧
        (tJ ≠ .leaf → (spF.nodes tJ.rootId).ppar = v' + 1) ∧
        (∀ x ∈ tJ.toList, (spF.nodes x).val = (spP.nodes x).val) ∧
        (∀ x, x ∉ (S.trees v').toList → x ∉ tRem.toList → spF.nodes x = spP.nodes x) ∧
        cF + ORD_PHI_WEIGHT * tJ.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * ((S.trees v').treePhi (fun _ => 0) + tRem.treePhi (fun _ => 0)) +
            ORD_JOIN_AMORT * ordStoreLog S.eCap + 50 := by
      by_cases hR0 : tRem.rootId = 0
      · have htRem_leaf : tRem = .leaf := by
          cases htr : tRem with
          | leaf => rfl
          | node rid rl rr =>
            exfalso; simp only [htr, AuxTree.rootId] at hR0
            exact SplayState.SubtreeInv_nonZero hokR.inv.sub (by rw [htr]; exact AuxTree.rootId_mem (t := .node rid rl rr) (by simp)) hR0
        have hc : (Expr.reg 15).eval w stP = some 0 := Expr.eval_reg_of_eq (by rw [hregsP]; simp [st3, st2, hR0])
        refine ⟨stP, _, spP, S.trees v', ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          hnP, hmP_vrv', fun _ _ _ => rfl, hok_v'_P, by simp [htRem_leaf, AuxTree.toList],
          by simp [htRem_leaf, AuxTree.countNodes],
          fun hne => by
            have hr := AuxTree.rootId_mem hne
            rw [hspP_agree_notS _ (fun hs => hinv.disj_trees v' v (Ne.symm hvv) _ hr ((hpart_v _).mpr (Or.inr hs))),
              hout_v _ (fun hxv => hinv.disj_trees v' v (Ne.symm hvv) _ hr hxv)]
            exact hinv.root_ppar v' hv' hne,
          fun _ _ => rfl, fun _ _ _ => rfl, by simp [Expr.size_reg, htRem_leaf, AuxTree.treePhi]; omega⟩
      · have hc : (Expr.reg 15).eval w stP = some tRem.rootId := Expr.eval_reg_of_eq (by rw [hregsP]; simp [st3, st2])
        have ha16 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 14) (.reg 2)))) stP .normal
            { stP with regs := Function.update stP.regs 16 (S.trees v').rootId } _ :=
          runs_assign_iff.mpr ⟨(S.trees v').rootId, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by rw [hregsP]; simp [st3, st2, hr14]))
            (Expr.eval_reg_of_eq (by rw [hregsP]; simp [st3, st2, hr2]))
            (by rw [hvr_def]; unfold ordVRootBase; omega)) hmP_vrv', rfl, rfl, rfl⟩
        set st4 : State := { stP with regs := Function.update stP.regs 16 (S.trees v').rootId }
        have hdisj_v'r : ∀ x ∈ (S.trees v').toList, x ∉ tRem.toList := fun x hx hr =>
          hinv.disj_trees v' v (Ne.symm hvv) x hx ((hpart_v x).mpr (Or.inl hr))
        have hsum_le : (S.trees v').countNodes + tRem.countNodes ≤ S.nextNode :=
          card_disj_le_nextNode (hinv.tree_inv v' hv').nodup hokR.inv.nodup hdisj_v'r
            (fun x hx => hinv.live_le_nextNode hv' hx)
            (fun x hx => hinv.live_le_nextNode hv ((hpart_v x).mpr (Or.inl hx)))
        obtain ⟨oJ, stJ, cJ, hrunJ, spJ, tJ, hoJ, hnJ, hfrJ, hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, hphiJ⟩ :=
          ordJoinBody_runs hrot hstep hsplay hwalk ω hnP hok_v'_P hokR_P rfl rfl hdisj_v'r hsum_le
            hinv.next_le (by omega) (by omega) hwide (owner := v' + 1) (pos := st4.pos)
        have hcallJ : Runs w p ω (.call 17 joinProc [.reg 9, .reg 16, .reg 15, .bin .add (.reg 2) (.const 1)]) st4 .normal
            { stJ with regs := Function.update st4.regs 17 tJ.rootId }
            (argsSize [.reg 9, .reg 16, .reg 15, .bin .add (.reg 2) (.const 1)] + cJ + 1) :=
          runs_call_iff.mpr ⟨[nb, (S.trees v').rootId, tRem.rootId, v' + 1], ordJoinBody walkProc, oJ, stJ, cJ,
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [st4, hregsP, st3, st2, hr9]))
              (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st4]))
                (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st4, hregsP, st3, st2]))
                  (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, hregsP, st3, st2, hr2]))
                    (Expr.eval_const (by omega)) (by omega)) (evalArgs_nil _ _)))),
            hjoin, hrunJ, rfl, by simp [hoJ], rfl⟩
        set st5 : State := { stJ with regs := Function.update st4.regs 17 tJ.rootId }
        have hs_v' : Runs w p ω (.store (.bin .add (.reg 14) (.reg 2)) (.reg 17)) st5 .normal
            { st5 with mem := Function.update stJ.mem (vr + v') tJ.rootId } _ :=
          runs_store_iff.mpr ⟨vr + v', tJ.rootId,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [st5, st4, hregsP, st3, st2, hr14]))
              (Expr.eval_reg_of_eq (by simp [st5, st4, hregsP, st3, st2, hr2]))
              (by rw [hvr_def]; unfold ordVRootBase; omega),
            Expr.eval_reg_of_eq (by simp [st5]), rfl, rfl, rfl⟩
        have hnot_vrv' : ¬ InOrdNodes nb S.nextNode (vr + v') :=
          hnot_nd _ (by rw [hvr_def, hnb]; unfold ordVRootBase ordNodesBase; omega)
        refine ⟨_, _, spJ, tJ, ord_runs_cond_true hc hR0 (ord_runs_seq_normal ha16 (ord_runs_seq_normal hcallJ hs_v')),
          hnJ.congr (fun a ha => Function.update_of_ne (fun (h : a = vr + v') => hnot_vrv' (h ▸ ha)) _ _),
          by simp, fun a h1 h2 => (Function.update_of_ne h2 _ _).trans (hfrJ a h1),
          hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, ?_⟩
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
          argsSize_cons, argsSize_nil] at *
        omega
    obtain ⟨stF, cF, spF, tJ, hrunF, hnF, hvrF, hfrF, hokJ, htJ_list, htJ_cnt, hppJ, hvalJ, houtJ, hphiF⟩ := hjoin_b4
    have hokS_F : OrdTreeOk S.nextNode spF tSel :=
      { null_node := hokJ.null_node
        clean := hokJ.clean
        inv := ⟨hokS_P.inv.nodup, SplayState.SubtreeInv_agree hokS_P.inv.sub fun x hx =>
          (houtJ x (fun hv' => hinv.disj_trees v v' hvv x ((hpart_v x).mpr (Or.inr hx)) hv')
            (fun hr => hdisj_rs x hr hx)).symm⟩
        mem_le := hokS_P.mem_le
        count_le := hokS_P.count_le }
    set S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := S.freeHead,
        vRoot := Function.update (Function.update S.vRoot v tSel.rootId) v' tJ.rootId,
        eNode := S.eNode, splay := spF, nextFree := S.nextFree,
        trees := Function.update (Function.update S.trees v tSel) v' tJ, freeList := S.freeList }
    have hinv' : OrdInv (applyOrdEdit ord (.moveEnds v v' sel true)) S' :=
      moveFinish_diff_inv hinv hv hv' hvv huniq'
        (fun x => by rw [hpart_v]; tauto) (fun x hs hr => hdisj_rs x hr hs) hokS_F
        (fun hne => by
          have hr := AuxTree.rootId_mem hne
          rw [houtJ _ (fun hv' => hinv.disj_trees v v' hvv _ ((hpart_v _).mpr (Or.inr hr)) hv')
            (fun hrm => hdisj_rs _ hrm hr)]
          exact hppS_P hne)
        (by
          have h1 : tSel.toList.map (fun x => endOfKey (spF.nodes x).val) =
              tSel.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by
              rw [houtJ x (fun hv' => hinv.disj_trees v v' hvv x ((hpart_v x).mpr (Or.inr hx)) hv')
                (fun hr => hdisj_rs x hr hx), hspP_val x]
          rw [h1, hmap_sel]; simp [movedBy])
        hokJ hppJ htJ_list
        (by
          have h1 : tRem.toList.map (fun x => endOfKey (spF.nodes x).val) =
              tRem.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by
              rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_right _ hx), hspP_val x]
          rw [h1, hmap_rem]; rfl)
        (fun x hxv hxv' =>
          (houtJ x hxv' (fun hr => hxv ((hpart_v x).mpr (Or.inl hr)))).trans
            ((hspP_agree_notS x (fun hs => hxv ((hpart_v x).mpr (Or.inr hs)))).trans (hout_v x hxv)))
        (fun x hx => by
          rcases hx with hxv | hxv'
          · rcases (hpart_v x).mp hxv with hr | hs
            · rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_right _ hr), hspP_val x]; exact hval_v x hxv
            · rw [houtJ x (fun h => hinv.disj_trees v v' hvv x hxv h) (fun hr => hdisj_rs x hr hs), hspP_val x]
              exact hval_v x hxv
          · rw [hvalJ x (by rw [htJ_list]; exact List.mem_append_left _ hxv'), hspP_val x,
              hout_v x (fun h => hinv.disj_trees v' v (Ne.symm hvv) x hxv' h)])
    have hstP_out : ∀ a, ¬ InOrdNodes nb S.nextNode a → a ≠ vr + v → stP.mem a = st1.mem a := fun a h1 h2 =>
      (hfrP a h1).trans (Function.update_of_ne h2 _ _)
    have harena' : OrdArenaAt b S' stF.mem :=
      { hdr_vCap := (hfrF b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.1)
        hdr_eCap := (hfrF (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.1)
        hdr_vRoot := (hfrF (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.1)
        hdr_eNode := (hfrF (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.1)
        hdr_nodes := (hfrF (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.1)
        hdr_next := (hfrF (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.2.1)
        hdr_free := (hfrF (b + 6) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out (b + 6) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans hhdr.2.2.2.2.2.2)
        vRoot_at := fun u hu => by
          dsimp only [S'] at hu
          by_cases h1 : u = v'
          · subst h1; simpa [S', hvr_def] using hvrF
          · rw [hfrF (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
              (by rw [hvr_def]; omega)]
            by_cases h2 : u = v
            · subst h2
              rw [hfrP (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))]
              simp [S', st3, hvr_def, Function.update_of_ne hvv]
            · rw [hstP_out (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
                (by rw [hvr_def]; omega), hvr_at u hu]
              simp [S', h1, h2]
        eNode_at := fun k hk => by
          dsimp only [S'] at hk
          exact (hfrF (ordENodeBase b S.vCap + k)
            (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))
            (by rw [hvr_def]; unfold ordVRootBase ordENodeBase; omega)).trans
            ((hstP_out (ordENodeBase b S.vCap + k) (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))
              (by rw [hvr_def]; unfold ordVRootBase ordENodeBase; omega)).trans (hen_at k hk))
        nodes_at := hnF }
    have hframe' : OrdFrame b S.vCap S.eCap scratch st1.mem stF.mem :=
      ⟨fun a ha => (hfrF a (fun h => by unfold InOrdNodes at h; omega)
          (by rw [hvr_def]; unfold ordVRootBase; omega)).trans
          ((hstP_out a (fun h => by unfold InOrdNodes at h; omega)
            (by rw [hvr_def]; unfold ordVRootBase; omega)).trans (hz a ha)),
       fun a _ hnf => (hfrF a (fun h => hnf (hnd_in_foot a h)) (fun h => hnf (by rw [h]; exact hvr_in_foot v' hv'))).trans
          (hstP_out a (fun h => hnf (hnd_in_foot a h)) (fun h => hnf (by rw [h]; exact hvr_in_foot v hv)))⟩
    have hphi_upd := sumTreePhi_update2 (S := S) (S' := S') hv hv' hvv rfl
      (fun u _ h1 h2 => by simp [S', Function.update_of_ne h1, Function.update_of_ne h2])
    rw [show S'.trees v = tSel by simp [S', Function.update_of_ne hvv],
        show S'.trees v' = tJ by simp [S']] at hphi_upd
    have hcnt_upd := sumCountNodes_update2 (S := S) (S' := S') hv hv' hvv rfl
      (fun u _ h1 h2 => by simp [S', Function.update_of_ne h1, Function.update_of_ne h2])
    rw [show S'.trees v = tSel by simp [S', Function.update_of_ne hvv],
        show S'.trees v' = tJ by simp [S']] at hcnt_upd
    refine ⟨stF, _, S',
      ord_runs_cond_false hcc (ord_runs_seq_normal ha15 (ord_runs_seq_normal hs_v (ord_runs_seq_normal hrunP hrunF))),
      hinv', harena', hframe', rfl, rfl, ?_⟩
    have hmul_sel := Nat.mul_le_mul_left 1000 htSel_phi
    have h160 : 160 ≤ 160 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 160 hlog
    have hsplit : (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap =
        1000 * (selNodes.length * ordStoreLog S.eCap) + ORD_JOIN_AMORT * ordStoreLog S.eCap + 160 * ordStoreLog S.eCap := by ring
    unfold ORD_PHI_WEIGHT at hphiF
    unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

theorem ordMoveFinishBody_runs
    {w b v v' scratch rotProc stepProc splayProc walkProc joinProc freeTreeProc : ℕ}
    {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody) (ω : ℕ → Bool)
    {st0 : State} {ord : ℕ → List End} {S : OrdStoreState} {sel : Finset End} {comp : Bool}
    {sp : SplayState ℕ Unit Unit} {tRem : AuxTree} {selNodes : List ℕ}
    (hinv : OrdInv ord S) (hv : v < S.vCap) (hv' : v' < S.vCap)
    (huniq' : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit ord (.moveEnds v v' sel comp)))
    (hsel_def : selNodes = (S.trees v).toList.filter (fun u => decide (endOfKey (S.splay.nodes u).val ∈ sel)))
    (hrem_list : tRem.toList = (S.trees v).toList.filter (fun z => decide (z ∉ selNodes)))
    (hokR : OrdTreeOk S.nextNode sp tRem)
    (hppR : tRem ≠ .leaf → (sp.nodes tRem.rootId).ppar = v + 1)
    (hokS : OrdTreeOk S.nextNode sp (leftSpine selNodes))
    (hout_v : ∀ x ∉ (S.trees v).toList, sp.nodes x = S.splay.nodes x)
    (hval_v : ∀ x ∈ (S.trees v).toList, (sp.nodes x).val = (S.splay.nodes x).val)
    (hhdr : st0.mem b = S.vCap ∧ st0.mem (b + 1) = S.eCap ∧ st0.mem (b + 2) = ordVRootBase b ∧
            st0.mem (b + 3) = ordENodeBase b S.vCap ∧ st0.mem (b + 4) = ordNodesBase b S.vCap S.eCap ∧
            st0.mem (b + 5) = S.nextNode ∧ st0.mem (b + 6) = S.freeHead)
    (hvr_at : ∀ u < S.vCap, st0.mem (ordVRootBase b + u) = if u = v then tRem.rootId else S.vRoot u)
    (hen_at : ∀ k < 2 * S.eCap, st0.mem (ordENodeBase b S.vCap + k) = S.eNode k)
    (hnodes : OrdNodesAt st0.mem (ordNodesBase b S.vCap S.eCap) S.nextNode sp S.nextFree)
    (hz : ZeroFrom st0.mem scratch)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ scratch)
    (hscr_w : scratch < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hr0 : st0.regs 0 = b) (hr1 : st0.regs 1 = v) (hr2 : st0.regs 2 = v')
    (hr3 : st0.regs 3 = if comp then 1 else 0)
    (hr9 : st0.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr13 : st0.regs 13 = (leftSpine selNodes).rootId) :
    ∃ st' c, ∃ S' : OrdStoreState,
      Runs w p ω (ordMoveFinishBody joinProc freeTreeProc) st0 .normal st' c ∧
      OrdInv (applyOrdEdit ord (.moveEnds v v' sel comp)) S' ∧
      OrdArenaAt b S' st'.mem ∧
      OrdFrame b S.vCap S.eCap scratch st0.mem st'.mem ∧
      S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
      c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' + ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_PHI_WEIGHT * tRem.treePhi (fun _ => 0) +
          (1000 * selNodes.length + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have htSel_list : (leftSpine selNodes).toList = selNodes := leftSpine_toList selNodes
  have hpart_v : ∀ x, x ∈ (S.trees v).toList ↔ x ∈ tRem.toList ∨ x ∈ (leftSpine selNodes).toList := fun x => by
    rw [hrem_list, htSel_list, List.mem_filter]
    constructor
    · intro hx; by_cases hs : x ∈ selNodes; exact Or.inr hs; exact Or.inl ⟨hx, decide_eq_true hs⟩
    · rintro (⟨hx, _⟩ | hs); exact hx; rw [hsel_def, List.mem_filter] at hs; exact hs.1
  have hdisj_rs : ∀ x ∈ tRem.toList, x ∉ (leftSpine selNodes).toList := fun x hr hs => by
    rw [hrem_list, List.mem_filter] at hr; rw [htSel_list] at hs
    exact (of_decide_eq_true hr.2) hs
  have hcnt_part : tRem.countNodes + (leftSpine selNodes).countNodes = (S.trees v).countNodes := by
    have hnd_rs : (tRem.toList ++ (leftSpine selNodes).toList).Nodup :=
      List.nodup_append.mpr ⟨hokR.inv.nodup, hokS.inv.nodup, fun a ha b hb h => hdisj_rs a ha (h ▸ hb)⟩
    have hset : (tRem.toList ++ (leftSpine selNodes).toList).toFinset = (S.trees v).toList.toFinset := by
      ext x; simp [List.mem_toFinset, hpart_v]
    have hcard := congrArg Finset.card hset
    rw [List.toFinset_card_of_nodup hnd_rs, List.toFinset_card_of_nodup (hinv.tree_inv v hv).nodup,
      List.length_append, AuxTree.length_toList, AuxTree.length_toList, AuxTree.length_toList] at hcard
    exact hcard
  have hmap_sel : (leftSpine selNodes).toList.map (fun x => endOfKey (sp.nodes x).val) =
      (ord v).filter (fun e => decide (e ∈ sel)) := by
    rw [htSel_list]
    have hcongr : selNodes.map (fun x => endOfKey (sp.nodes x).val) =
        selNodes.map (fun x => endOfKey (S.splay.nodes x).val) :=
      List.map_congr_left fun x hx => by
        rw [hsel_def, List.mem_filter] at hx; rw [hval_v x hx.1]
    rw [hcongr, hsel_def,
      map_filter_eq_filter_map (fun x => endOfKey (S.splay.nodes x).val) (fun e => decide (e ∈ sel)),
      hinv.list_eq v hv]
  have hmap_rem : tRem.toList.map (fun x => endOfKey (sp.nodes x).val) =
      (ord v).filter (fun e => !decide (e ∈ sel)) := by
    have hcongr : tRem.toList.map (fun x => endOfKey (sp.nodes x).val) =
        tRem.toList.map (fun x => endOfKey (S.splay.nodes x).val) :=
      List.map_congr_left fun x hx => by
        rw [hrem_list, List.mem_filter] at hx; rw [hval_v x hx.1]
    have hfilt : tRem.toList = (S.trees v).toList.filter (fun x => !decide (endOfKey (S.splay.nodes x).val ∈ sel)) := by
      rw [hrem_list]
      refine List.filter_congr fun x hx => ?_
      apply Bool.eq_iff_iff.mpr
      simp [hsel_def, List.mem_filter, hx]
    rw [hcongr, hfilt,
      map_filter_eq_filter_map (fun x => endOfKey (S.splay.nodes x).val) (fun e => !decide (e ∈ sel)),
      hinv.list_eq v hv]
  have htSel_phi : (leftSpine selNodes).treePhi (fun _ => 0) ≤ selNodes.length * ordStoreLog S.eCap :=
    leftSpine_treePhi_le (eCap := S.eCap) selNodes (by
      have hcnt : selNodes.length ≤ (S.trees v).countNodes := by
        rw [← leftSpine_countNodes selNodes]; omega
      have hv_le : (S.trees v).countNodes ≤ sumCountNodes S :=
        Finset.single_le_sum (f := fun u => (S.trees u).countNodes) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
      have := hinv.sumCountNodes_le; omega)
  have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 0) (.const 2)))) st0 .normal
      { st0 with regs := Function.update st0.regs 14 (ordVRootBase b) } _ :=
    runs_assign_iff.mpr ⟨ordVRootBase b, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by omega)) (by omega)) hhdr.2.2.1, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 14 (ordVRootBase b) }
  by_cases hvv : v = v'
  · subst hvv
    have hcvv : (Expr.bin .eq (.reg 1) (.reg 2)).eval w st1 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := v) (by simp [st1, hr1]))
        (Expr.eval_reg_of_eq (v := v) (by simp [st1, hr2])) rfl (by omega)
    obtain ⟨st', c', S', hrun', hinv', harena', hfr', hv', he', hphi'⟩ :=
      ordMoveFinishSame_runs hfree ω (st1 := st1) hinv hv huniq' hpart_v hdisj_rs hcnt_part
        hmap_sel hmap_rem htSel_phi hokR hppR hokS hout_v hval_v hhdr hvr_at hen_at hnodes hz hfoot hscr_w hwide
        (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr3]) (by simp [st1, hr9])
        (by simp [st1, hr13]) (by simp [st1])
    refine ⟨st', _, S', ord_runs_seq_normal ha14 (ord_runs_cond_true hcvv Nat.one_ne_zero hrun'),
      hinv', harena', hfr', hv', he', ?_⟩
    have h40 : 40 ≤ 40 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 40 hlog
    have hsp : (1000 * selNodes.length + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap =
        (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap + 40 * ordStoreLog S.eCap := by ring
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega
  · have hcvv : (Expr.bin .eq (.reg 1) (.reg 2)).eval w st1 = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (v := v) (by simp [st1, hr1]))
        (Expr.eval_reg_of_eq (v := v') (by simp [st1, hr2])) hvv (by omega)
    obtain ⟨st', c', S', hrun', hinv', harena', hfr', hv', he', hphi'⟩ :=
      ordMoveFinishDiff_runs hrot hstep hsplay hwalk hjoin ω (st1 := st1) hinv hv hv' hvv huniq'
        hpart_v hdisj_rs hcnt_part hmap_sel hmap_rem htSel_phi hokR hppR hokS hout_v hval_v
        hhdr hvr_at hen_at hnodes hz hfoot hscr_w hwide
        (by simp [st1, hr1]) (by simp [st1, hr2]) (by simp [st1, hr3]) (by simp [st1, hr9])
        (by simp [st1, hr13]) (by simp [st1])
    refine ⟨st', _, S', ord_runs_seq_normal ha14 (ord_runs_cond_false hcvv hrun'),
      hinv', harena', hfr', hv', he', ?_⟩
    have h40 : 40 ≤ 40 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 40 hlog
    have hsp : (1000 * selNodes.length + ORD_JOIN_AMORT + 200) * ordStoreLog S.eCap =
        (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap + 40 * ordStoreLog S.eCap := by ring
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

end MinCostFlow.SparseCore.Program
