module

public import MinCostFlow.SparseCore.Program.OrdStoreWalkJoin
import Mathlib.Tactic

/-!
# Order Store Unlink Procedure

This file implements and verifies `ordUnlinkBody` on `[b, u]`: splays a live node `u` to the root
of its vertex tree, detaches its left and right subtrees, resets `u` to an isolated singleton,
joins the two subtrees back into `vRoot[owner - 1]`, and returns `owner = v + 1`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_UNLINK_AMORT : ℕ := 9800

/-- `ordUnlink` on `[b, u]`: splays live node `u` to the root of its vertex tree, detaches `L` and
`R`, resets `u` to an isolated singleton, joins `L` and `R` into `vRoot[owner - 1]`, and returns
`owner = u.ppar`. -/
def ordUnlinkBody (splayProc joinProc : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .call 3 splayProc [.reg 2, .reg 1] ;;
  .assign 4 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.const 3))) ;;
  .assign 6 (.load (.reg 4)) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.const 1))) ;;
  .cond (.reg 6)
    (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 6))) (.const 2)) (.const 0)) .nop ;;
  .cond (.reg 7)
    (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7))) (.const 2)) (.const 0)) .nop ;;
  .store (.reg 4) (.const 0) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
  .store (.bin .add (.reg 4) (.const 4)) (.const 1) ;;
  .call 8 joinProc [.reg 2, .reg 6, .reg 7, .reg 5] ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .store (.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))) (.reg 8) ;;
  .ret (.reg 5)

theorem ordUnlinkBody_noRand (splayProc joinProc : ℕ) :
    (ordUnlinkBody splayProc joinProc).NoRand := by
  simp [ordUnlinkBody, Stmt.NoRand]

theorem ordUnlinkBody_runs
    {w b vCap eCap cap v u pos rotProc stepProc splayProc walkProc joinProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t : AuxTree}
    (hvr : mem (b + 2) = ordVRootBase b)
    (hnb_hdr : mem (b + 4) = ordNodesBase b vCap eCap)
    (hnodes : OrdNodesAt mem (ordNodesBase b vCap eCap) cap st nf)
    (hok : OrdTreeOk cap st t)
    (hv : v < vCap) (hu : u ∈ t.toList)
    (hpp : (st.nodes t.rootId).ppar = v + 1)
    (hcap : cap ≤ 2 * eCap)
    (hw : b + ordArenaSize vCap eCap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordUnlinkBody splayProc joinProc) (startState [b, u] mem pos) o st' c ∧
      (∃ (sp' : SplayState ℕ Unit Unit) (t' : AuxTree),
        o.value = v + 1 ∧
        OrdNodesAt st'.mem (ordNodesBase b vCap eCap) cap sp' nf ∧
        st'.mem (ordVRootBase b + v) = t'.rootId ∧
        (∀ a, ¬ InOrdNodes (ordNodesBase b vCap eCap) cap a → a ≠ ordVRootBase b + v → st'.mem a = mem a) ∧
        OrdTreeOk cap sp' t' ∧
        t'.toList = t.toList.erase u ∧
        t'.countNodes + 1 = t.countNodes ∧
        (t' ≠ .leaf → (sp'.nodes t'.rootId).ppar = v + 1) ∧
        sp'.nodes u = { (st.nodes u) with left := 0, right := 0, par := 0, ppar := 0, sz := 1 } ∧
        (∀ x ∈ t'.toList, (sp'.nodes x).val = (st.nodes x).val) ∧
        (∀ x ∉ t.toList, sp'.nodes x = st.nodes x) ∧
        c + ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) ≤
          ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + ORD_UNLINK_AMORT * ordStoreLog eCap) := by
  set nb := ordNodesBase b vCap eCap with hnb_def
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  have hw' : b + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  have hnb_w : nb + 8 * (cap + 1) < 2 ^ w := by
    have := ordNodesBase_end b vCap eCap; unfold ordArenaSize at this; omega
  have hvr_w : ordVRootBase b + v < 2 ^ w := by unfold ordVRootBase; omega
  have hu_nz : u ≠ 0 := SplayState.SubtreeInv_nonZero hok.inv.sub hu
  have hu_c : u ≤ cap := hok.mem_le u hu
  have hfuel : t.depthOf u < t.countNodes := depthOf_lt_countNodes hu
  obtain ⟨ts, hts_inv, hts_ne, hts_root, hts_list, hclean_s, hval_s, hpp_s, hout_s, hcnt_s, hphi_s⟩ :=
    ord_splay_spec hok.inv hok.clean hu hfuel
  set sp1 := SplayState.splayLoop ordPayload st t.countNodes u
  have h0_nmem : 0 ∉ t.toList := fun h0 => SplayState.SubtreeInv_nonZero hok.inv.sub h0 rfl
  obtain ⟨L, R, hts_eq⟩ : ∃ L R, ts = .node u L R := by
    cases ts with
    | leaf => exact absurd rfl hts_ne
    | node id l r => simp only [AuxTree.rootId] at hts_root; exact ⟨l, r, by rw [hts_root]⟩
  have hts_inv' : TreeInv ordPayload sp1 (.node u L R) := hts_eq ▸ hts_inv
  rcases hts_inv'.sub with ⟨-, huL, huR, -, -, -, -, hsubL, hsubR⟩
  rcases AuxTree.nodup_node_unfold hts_inv'.nodup with ⟨hL_nd, hu_nL, hR_nd, hu_nR, hLR_disj⟩
  have hL_le : L.rootId ≤ cap := by
    cases L with
    | leaf => exact Nat.zero_le _
    | node lid ll lr => exact hok.mem_le lid (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList])
  have hR_le : R.rootId ≤ cap := by
    cases R with
    | leaf => exact Nat.zero_le _
    | node rid rl rr => exact hok.mem_le rid (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList])
  obtain ⟨hinvL, hinvR, hphiLR⟩ := detach_root_treeInv hts_inv'
  set sp2 := if L.rootId = 0 then sp1 else sp1.setPar L.rootId 0
  set sp3 := if R.rootId = 0 then sp2 else sp2.setPar R.rootId 0
  set sp4 := sp3.updateNode u fun nd => { nd with left := 0, right := 0, par := 0, ppar := 0, sz := 1 }
  have hokL : OrdTreeOk cap sp4 L :=
    { null_node := by
        have h1 : sp2.nodes 0 = ordNullNode := by
          dsimp only [sp2]; split_ifs with hL0
          · exact (hout_s 0 h0_nmem).trans hok.null_node
          · rw [SplayState.setPar, SplayState.nodes_updateNode_ne _ (Ne.symm hL0)]
            exact (hout_s 0 h0_nmem).trans hok.null_node
        have h2 : sp3.nodes 0 = ordNullNode := by
          dsimp only [sp3]; split_ifs with hR0
          · exact h1
          · rw [SplayState.setPar, SplayState.nodes_updateNode_ne _ (Ne.symm hR0)]; exact h1
        rw [SplayState.nodes_updateNode_ne _ (Ne.symm hu_nz)]; exact h2
      clean := fun x => by
        have h2 : (sp2.nodes x).rev = false := by
          dsimp only [sp2]; split_ifs; exact hclean_s x
          by_cases h : x = L.rootId
          · subst h; simp [SplayState.setPar, SplayState.nodes_updateNode, hclean_s]
          · simp [SplayState.setPar, SplayState.nodes_updateNode, h, hclean_s x]
        have h3 : (sp3.nodes x).rev = false := by
          dsimp only [sp3]; split_ifs; exact h2
          by_cases h : x = R.rootId
          · subst h; simp [SplayState.setPar, SplayState.nodes_updateNode, h2]
          · simp [SplayState.setPar, SplayState.nodes_updateNode, h, h2]
        by_cases h : x = u
        · subst h; simp [sp4, SplayState.nodes_updateNode, h3]
        · simp [sp4, SplayState.nodes_updateNode, h, h3]
      inv := ⟨hinvL.nodup, SplayState.SubtreeInv_agree hinvL.sub fun x hx => by
        have hxu : x ≠ u := fun h => hu_nL (h ▸ hx)
        simp [sp4, SplayState.nodes_updateNode, hxu]⟩
      mem_le := fun x hx => hok.mem_le x (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList, hx])
      count_le := by
        have hc : (AuxTree.node u L R).countNodes = t.countNodes := hts_eq ▸ hcnt_s
        have := hok.count_le; simp [AuxTree.countNodes] at hc; omega }
  have hokR : OrdTreeOk cap sp4 R :=
    { null_node := hokL.null_node
      clean := hokL.clean
      inv := ⟨hinvR.nodup, SplayState.SubtreeInv_agree hinvR.sub fun x hx => by
        have hxu : x ≠ u := fun h => hu_nR (h ▸ hx)
        simp [sp4, SplayState.nodes_updateNode, hxu]⟩
      mem_le := fun x hx => hok.mem_le x (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList, hx])
      count_le := by
        have hc : (AuxTree.node u L R).countNodes = t.countNodes := hts_eq ▸ hcnt_s
        have := hok.count_le; simp [AuxTree.countNodes] at hc; omega }
  -- Step 1: load nb, call splayProc [nb, u]
  obtain ⟨oS, stS, cS, hrunS, ⟨hnS, hfrS⟩, hcS⟩ :=
    ordSplayBody_runs hrot hstep ω hnodes hok hu hnb_w hwide (pos := pos)
  set st0 : State := startState [b, u] mem pos
  have hload_nb : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const 4)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) hnb_hdr, rfl, rfl, rfl⟩
  have hcall_s : Runs w p ω (.call 3 splayProc [.reg 2, .reg 1])
      { st0 with regs := Function.update st0.regs 2 nb } .normal
      { stS with regs := Function.update (Function.update st0.regs 2 nb) 3 oS.value }
      (argsSize [.reg 2, .reg 1] + cS + 1) :=
    runs_call_iff.mpr ⟨[nb, u], ordSplayBody stepProc, oS, stS, cS,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp))
        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st0, startState])) (evalArgs_nil _ _)),
      hsplay, hrunS, rfl, rfl, rfl⟩
  set stA : State := { stS with regs := Function.update (Function.update st0.regs 2 nb) 3 oS.value }
  have hpp_u : (sp1.nodes u).ppar = v + 1 := hpp_s.trans hpp
  have hmS_pp : stS.mem (nb + 8 * u + 3) = v + 1 := by rw [← hpp_u]; exact (hnS u hu_c).2.2.2.1
  have hmS_L : stS.mem (nb + 8 * u) = L.rootId := by rw [← huL]; exact (hnS u hu_c).1
  have hmS_R : stS.mem (nb + 8 * u + 1) = R.rootId := by rw [← huR]; exact (hnS u hu_c).2.1
  -- Continuation from stM representing sp4
  have hafter4 : ∀ (stM : State),
      OrdNodesAt stM.mem nb cap sp4 nf →
      (∀ a, ¬ InOrdNodes nb cap a → stM.mem a = mem a) →
      stM.regs 0 = b → stM.regs 2 = nb → stM.regs 5 = v + 1 →
      stM.regs 6 = L.rootId → stM.regs 7 = R.rootId →
      ∃ o st' c, Runs w p ω
        (.call 8 joinProc [.reg 2, .reg 6, .reg 7, .reg 5] ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const 2))) ;;
         .store (.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))) (.reg 8) ;;
         .ret (.reg 5)) stM o st' c ∧
        (∃ (sp' : SplayState ℕ Unit Unit) (t' : AuxTree),
          o.value = v + 1 ∧
          OrdNodesAt st'.mem nb cap sp' nf ∧
          st'.mem (ordVRootBase b + v) = t'.rootId ∧
          (∀ a, ¬ InOrdNodes nb cap a → a ≠ ordVRootBase b + v → st'.mem a = mem a) ∧
          OrdTreeOk cap sp' t' ∧
          t'.toList = t.toList.erase u ∧
          t'.countNodes + 1 = t.countNodes ∧
          (t' ≠ .leaf → (sp'.nodes t'.rootId).ppar = v + 1) ∧
          sp'.nodes u = { (st.nodes u) with left := 0, right := 0, par := 0, ppar := 0, sz := 1 } ∧
          (∀ x ∈ t'.toList, (sp'.nodes x).val = (st.nodes x).val) ∧
          (∀ x ∉ t.toList, sp'.nodes x = st.nodes x) ∧
          c + ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) ≤
            ORD_PHI_WEIGHT * (L.treePhi (fun _ => 0) + R.treePhi (fun _ => 0)) +
              (ORD_JOIN_AMORT + 100) * ordStoreLog eCap) := by
    intro stM hn4 hfr4 r0 r2 r5 r6 r7
    have hsumLR : L.countNodes + R.countNodes ≤ cap := by
      have hc : (AuxTree.node u L R).countNodes = t.countNodes := hts_eq ▸ hcnt_s
      have := hok.count_le; simp [AuxTree.countNodes] at hc; omega
    obtain ⟨oJ, stJ, cJ, hrunJ, spJ, tJ, hoJ, hnJ, hfrJ, hokJ, hlistJ, hcntJ, hppJ, hvalJ, houtJ, hphiJ⟩ :=
      ordJoinBody_runs hrot hstep hsplay hwalk ω hn4 hokL hokR rfl rfl hLR_disj hsumLR hcap
        (owner := v + 1) (by omega) hnb_w hwide (pos := stM.pos)
    have hcallJ : Runs w p ω (.call 8 joinProc [.reg 2, .reg 6, .reg 7, .reg 5]) stM .normal
        { stJ with regs := Function.update stM.regs 8 tJ.rootId }
        (argsSize [.reg 2, .reg 6, .reg 7, .reg 5] + cJ + 1) :=
      runs_call_iff.mpr ⟨[nb, L.rootId, R.rootId, v + 1], ordJoinBody walkProc, oJ, stJ, cJ,
        evalArgs_cons (Expr.eval_reg_of_eq r2)
          (evalArgs_cons (Expr.eval_reg_of_eq r6)
            (evalArgs_cons (Expr.eval_reg_of_eq r7)
              (evalArgs_cons (Expr.eval_reg_of_eq r5) (evalArgs_nil _ _)))),
        hjoin, hrunJ, rfl, by simp [hoJ], rfl⟩
    have hmJ_vr : stJ.mem (b + 2) = ordVRootBase b := by
      have hnot : ¬ InOrdNodes nb cap (b + 2) := fun h => by
        unfold InOrdNodes at h; rw [hnb_def] at h; unfold ordNodesBase at h; omega
      rw [hfrJ (b + 2) hnot, hfr4 (b + 2) hnot, hvr]
    set stJ1 : State := { stJ with regs := Function.update stM.regs 8 tJ.rootId }
    have hld9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 2)))) stJ1 .normal
        { stJ1 with regs := Function.update stJ1.regs 9 (ordVRootBase b) } _ :=
      runs_assign_iff.mpr ⟨ordVRootBase b, Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (v := b) (by simp [stJ1, r0])) (Expr.eval_const (by omega))
        (by omega)) hmJ_vr, rfl, rfl, rfl⟩
    set stJ2 : State := { stJ1 with regs := Function.update stJ1.regs 9 (ordVRootBase b) }
    have haddr_vr : (Expr.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))).eval w stJ2 =
        some (ordVRootBase b + v) := by
      have h1 : (Expr.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))).eval w stJ2 =
          some (ordVRootBase b + (v + 1 - 1)) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [stJ2]))
          (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [stJ2, stJ1, r5]))
            (Expr.eval_const (by omega)) (by omega))
          (by simp only [Nat.add_sub_cancel]; omega)
      simpa only [Nat.add_sub_cancel] using h1
    have hst_vr : Runs w p ω (.store (.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))) (.reg 8)) stJ2 .normal
        { stJ2 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId } _ :=
      runs_store_iff.mpr ⟨ordVRootBase b + v, tJ.rootId, haddr_vr,
        Expr.eval_reg_of_eq (v := tJ.rootId) (by simp [stJ2, stJ1]), rfl, rfl, rfl⟩
    set stJ3 : State := { stJ2 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId }
    have hret : Runs w p ω (.ret (.reg 5)) stJ3 (.returned (v + 1)) stJ3 _ :=
      runs_ret_iff.mpr ⟨v + 1, Expr.eval_reg_of_eq (by simp [stJ3, stJ2, stJ1, r5]), rfl, rfl, rfl⟩
    have hseq := ord_runs_seq_normal hcallJ (ord_runs_seq_normal hld9 (ord_runs_seq_normal hst_vr hret))
    have hvr_notin : ¬ InOrdNodes nb cap (ordVRootBase b + v) := fun h => by
      unfold InOrdNodes ordVRootBase at h; rw [hnb_def] at h; unfold ordNodesBase at h; omega
    have hnJ' : OrdNodesAt (Function.update stJ.mem (ordVRootBase b + v) tJ.rootId) nb cap spJ nf :=
      hnJ.congr fun a ha => Function.update_of_ne (fun (heq : a = ordVRootBase b + v) => hvr_notin (heq ▸ ha)) _ _
    have hlist_er : tJ.toList = t.toList.erase u := by
      rw [hlistJ, ← hts_list, hts_eq]
      exact (erase_append_singleton_append hts_inv'.nodup).symm
    have hcnt_er : tJ.countNodes + 1 = t.countNodes := by
      have hc : (AuxTree.node u L R).countNodes = t.countNodes := hts_eq ▸ hcnt_s
      simp [AuxTree.countNodes] at hc; omega
    have hu_iso : spJ.nodes u = { (st.nodes u) with left := 0, right := 0, par := 0, ppar := 0, sz := 1 } := by
      rw [houtJ u hu_nL hu_nR]
      have h1 : (sp4.nodes u) = { (sp3.nodes u) with left := 0, right := 0, par := 0, ppar := 0, sz := 1 } := by
        simp [sp4, SplayState.nodes_updateNode]
      have hval_u : (sp3.nodes u).val = (st.nodes u).val := by
        have h2 : (sp2.nodes u).val = (sp1.nodes u).val := by
          dsimp only [sp2]; split_ifs; rfl
          by_cases h : u = L.rootId <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]
        have h3 : (sp3.nodes u).val = (sp2.nodes u).val := by
          dsimp only [sp3]; split_ifs; rfl
          by_cases h : u = R.rootId <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]
        rw [h3, h2, hval_s u hu]
      have hrev_u : (sp3.nodes u).rev = (st.nodes u).rev := by
        have h2 : (sp2.nodes u).rev = false := by
          dsimp only [sp2]; split_ifs; exact hclean_s u
          by_cases h : u = L.rootId
          · subst h; simp [SplayState.setPar, SplayState.nodes_updateNode, hclean_s]
          · simp [SplayState.setPar, SplayState.nodes_updateNode, h, hclean_s u]
        have h3 : (sp3.nodes u).rev = false := by
          dsimp only [sp3]; split_ifs; exact h2
          by_cases h : u = R.rootId
          · subst h; simp [SplayState.setPar, SplayState.nodes_updateNode, h2]
          · simp [SplayState.setPar, SplayState.nodes_updateNode, h, h2]
        rw [h3, hok.clean u]
      rw [h1]
      cases hsp3 : sp3.nodes u
      cases hst : st.nodes u
      simp only [hsp3, hst] at hval_u hrev_u ⊢
      simp [hval_u, hrev_u]
    have hout_all : ∀ x ∉ t.toList, spJ.nodes x = st.nodes x := fun x hx => by
      have hxL : x ∉ L.toList := fun h => hx (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList, h])
      have hxR : x ∉ R.toList := fun h => hx (hts_list ▸ hts_eq ▸ by simp [AuxTree.toList, h])
      have hxu : x ≠ u := fun h => hx (h ▸ hu)
      rw [houtJ x hxL hxR]
      simp only [sp4, SplayState.nodes_updateNode, hxu, ite_false]
      have h3 : sp3.nodes x = sp2.nodes x := by
        dsimp only [sp3]; split_ifs with hR0; rfl
        have hxr : x ≠ R.rootId := by
          cases R with
          | leaf => exact absurd rfl hR0
          | node rid rl rr => intro heq; exact hxR (heq ▸ AuxTree.rootId_mem (by simp))
        simp [SplayState.setPar, SplayState.nodes_updateNode, hxr]
      have h2 : sp2.nodes x = sp1.nodes x := by
        dsimp only [sp2]; split_ifs with hL0; rfl
        have hxl : x ≠ L.rootId := by
          cases L with
          | leaf => exact absurd rfl hL0
          | node lid ll lr => intro heq; exact hxL (heq ▸ AuxTree.rootId_mem (by simp))
        simp [SplayState.setPar, SplayState.nodes_updateNode, hxl]
      rw [h3, h2, hout_s x hx]
    have hval_all : ∀ x ∈ tJ.toList, (spJ.nodes x).val = (st.nodes x).val := fun x hx => by
      rw [hvalJ x hx]
      have hxt : x ∈ t.toList := by
        rw [hlistJ, List.mem_append] at hx
        rw [← hts_list, hts_eq]; rcases hx with h | h <;> simp [AuxTree.toList, h]
      have hxu : x ≠ u := by
        rw [hlistJ, List.mem_append] at hx
        rintro rfl; rcases hx with h | h; exact hu_nL h; exact hu_nR h
      simp only [sp4, SplayState.nodes_updateNode, hxu, ite_false]
      have h3 : (sp3.nodes x).val = (sp2.nodes x).val := by
        dsimp only [sp3]; split_ifs; rfl
        by_cases h : x = R.rootId <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]
      have h2 : (sp2.nodes x).val = (sp1.nodes x).val := by
        dsimp only [sp2]; split_ifs; rfl
        by_cases h : x = L.rootId <;> simp [SplayState.setPar, SplayState.nodes_updateNode, h]
      rw [h3, h2, hval_s x hxt]
    refine ⟨.returned (v + 1), stJ3, _, hseq, spJ, tJ, rfl, hnJ', by simp [stJ3],
      fun a ha hne => by dsimp only [stJ3]; rw [Function.update_of_ne hne, hfrJ a ha, hfr4 a ha],
      hokJ, hlist_er, hcnt_er, hppJ, hu_iso, hval_all, hout_all, ?_⟩
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    have h100 : (ORD_JOIN_AMORT + 100) * ordStoreLog eCap =
        ORD_JOIN_AMORT * ordStoreLog eCap + 100 * ordStoreLog eCap := by ring
    omega
  -- Continuation from stM representing sp3 (reset u's 5 fields then call hafter4)
  have hafter3 : ∀ (stM : State),
      OrdNodesAt stM.mem nb cap sp3 nf →
      (∀ a, ¬ InOrdNodes nb cap a → stM.mem a = mem a) →
      stM.regs 0 = b → stM.regs 2 = nb → stM.regs 4 = nb + 8 * u →
      stM.regs 5 = v + 1 → stM.regs 6 = L.rootId → stM.regs 7 = R.rootId →
      ∃ o st' c, Runs w p ω
        (.store (.reg 4) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 2)) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 4)) (.const 1) ;;
         .call 8 joinProc [.reg 2, .reg 6, .reg 7, .reg 5] ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const 2))) ;;
         .store (.bin .add (.reg 9) (.bin .sub (.reg 5) (.const 1))) (.reg 8) ;;
         .ret (.reg 5)) stM o st' c ∧
        (∃ (sp' : SplayState ℕ Unit Unit) (t' : AuxTree),
          o.value = v + 1 ∧
          OrdNodesAt st'.mem nb cap sp' nf ∧
          st'.mem (ordVRootBase b + v) = t'.rootId ∧
          (∀ a, ¬ InOrdNodes nb cap a → a ≠ ordVRootBase b + v → st'.mem a = mem a) ∧
          OrdTreeOk cap sp' t' ∧
          t'.toList = t.toList.erase u ∧
          t'.countNodes + 1 = t.countNodes ∧
          (t' ≠ .leaf → (sp'.nodes t'.rootId).ppar = v + 1) ∧
          sp'.nodes u = { (st.nodes u) with left := 0, right := 0, par := 0, ppar := 0, sz := 1 } ∧
          (∀ x ∈ t'.toList, (sp'.nodes x).val = (st.nodes x).val) ∧
          (∀ x ∉ t.toList, sp'.nodes x = st.nodes x) ∧
          c + ORD_PHI_WEIGHT * t'.treePhi (fun _ => 0) ≤
            ORD_PHI_WEIGHT * (L.treePhi (fun _ => 0) + R.treePhi (fun _ => 0)) +
              (ORD_JOIN_AMORT + 160) * ordStoreLog eCap) := by
    intro stM hn3 hfr3 r0 r2 r4 r5 r6 r7
    have hst1 : Runs w p ω (.store (.reg 4) (.const 0)) stM .normal
        { stM with mem := Function.update stM.mem (nb + 8 * u) 0 } _ :=
      runs_store_iff.mpr ⟨nb + 8 * u, 0, Expr.eval_reg_of_eq r4, Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set m1 := Function.update stM.mem (nb + 8 * u) 0
    have hst2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.const 0)) { stM with mem := m1 } .normal
        { stM with mem := Function.update m1 (nb + 8 * u + 1) 0 } _ :=
      runs_store_iff.mpr ⟨nb + 8 * u + 1, 0, Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set m2 := Function.update m1 (nb + 8 * u + 1) 0
    have hst3 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.const 0)) { stM with mem := m2 } .normal
        { stM with mem := Function.update m2 (nb + 8 * u + 2) 0 } _ :=
      runs_store_iff.mpr ⟨nb + 8 * u + 2, 0, Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set m3 := Function.update m2 (nb + 8 * u + 2) 0
    have hst4 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.const 0)) { stM with mem := m3 } .normal
        { stM with mem := Function.update m3 (nb + 8 * u + 3) 0 } _ :=
      runs_store_iff.mpr ⟨nb + 8 * u + 3, 0, Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set m4 := Function.update m3 (nb + 8 * u + 3) 0
    have hst5 : Runs w p ω (.store (.bin .add (.reg 4) (.const 4)) (.const 1)) { stM with mem := m4 } .normal
        { stM with mem := Function.update m4 (nb + 8 * u + 4) 1 } _ :=
      runs_store_iff.mpr ⟨nb + 8 * u + 4, 1, Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    set m5 := Function.update m4 (nb + 8 * u + 4) 1
    have hn4 : OrdNodesAt m5 nb cap sp4 nf := by
      have hn3a : OrdNodesAt m1 nb cap (sp3.setLeft u 0) nf := by
        simpa [ordNodeAddr] using hn3.setLeft hu_c (v := 0)
      have hstep := (((hn3a.setRight hu_c (v := 0)).setPar hu_c (v := 0)).setPpar hu_c (v := 0)).setSz hu_c (v := 1)
      have hsp_eq : ((((sp3.setLeft u 0).setRight u 0).setPar u 0).setPpar u 0 |>.updateNode u
          fun nd => { nd with sz := 1 }) = sp4 := by
        have hfun : ∀ x, ((((sp3.setLeft u 0).setRight u 0).setPar u 0).setPpar u 0 |>.updateNode u
            fun nd => { nd with sz := 1 }).nodes x = sp4.nodes x := by
          intro x; by_cases h : x = u
          · subst h; simp [sp4, SplayState.setLeft, SplayState.setRight, SplayState.setPar, SplayState.setPpar, SplayState.nodes_updateNode]
          · simp [sp4, SplayState.setLeft, SplayState.setRight, SplayState.setPar, SplayState.setPpar, SplayState.nodes_updateNode, h]
        cases h1 : ((((sp3.setLeft u 0).setRight u 0).setPar u 0).setPpar u 0 |>.updateNode u fun nd => { nd with sz := 1 })
        cases h2 : sp4
        congr 1; funext x; have := hfun x; rwa [h1, h2] at this
      rw [← hsp_eq]; exact hstep
    have hfr4 : ∀ a, ¬ InOrdNodes nb cap a → m5 a = mem a := fun a ha => by
      dsimp only [m5, m4, m3, m2, m1]
      rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
          Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
          Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
          Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩),
          Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
      exact hfr3 a ha
    obtain ⟨o, st', c, hr, sp', t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hphi⟩ :=
      hafter4 { stM with mem := m5 } hn4 hfr4 r0 r2 r5 r6 r7
    refine ⟨o, st', _, ord_runs_seq_normal hst1 (ord_runs_seq_normal hst2
      (ord_runs_seq_normal hst3 (ord_runs_seq_normal hst4 (ord_runs_seq_normal hst5 hr)))),
      sp', t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    have h60 : (ORD_JOIN_AMORT + 160) * ordStoreLog eCap =
        (ORD_JOIN_AMORT + 100) * ordStoreLog eCap + 60 * ordStoreLog eCap := by ring
    omega
  -- Run from stA: load addr(u), owner, L, R; detach L; detach R; hafter3
  have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 1)))) stA .normal
      { stA with regs := Function.update stA.regs 4 (nb + 8 * u) } _ :=
    runs_assign_iff.mpr ⟨nb + 8 * u, Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stA, st0, startState])) (by omega)) (by omega),
      rfl, rfl, rfl⟩
  set stB1 : State := { stA with regs := Function.update stA.regs 4 (nb + 8 * u) }
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.const 3)))) stB1 .normal
      { stB1 with regs := Function.update stB1.regs 5 (v + 1) } _ :=
    runs_assign_iff.mpr ⟨v + 1, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stB1]))
      (Expr.eval_const (by omega)) (by omega)) hmS_pp, rfl, rfl, rfl⟩
  set stB2 : State := { stB1 with regs := Function.update stB1.regs 5 (v + 1) }
  have ha6 : Runs w p ω (.assign 6 (.load (.reg 4))) stB2 .normal
      { stB2 with regs := Function.update stB2.regs 6 L.rootId } _ :=
    runs_assign_iff.mpr ⟨L.rootId, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [stB2, stB1])) hmS_L,
      rfl, rfl, rfl⟩
  set stB3 : State := { stB2 with regs := Function.update stB2.regs 6 L.rootId }
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 4) (.const 1)))) stB3 .normal
      { stB3 with regs := Function.update stB3.regs 7 R.rootId } _ :=
    runs_assign_iff.mpr ⟨R.rootId, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stB3, stB2, stB1]))
      (Expr.eval_const (by omega)) (by omega)) hmS_R, rfl, rfl, rfl⟩
  set stB4 : State := { stB3 with regs := Function.update stB3.regs 7 R.rootId }
  have hdetL : ∃ stC cC, Runs w p ω
      (.cond (.reg 6) (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 6))) (.const 2)) (.const 0)) .nop)
      stB4 .normal stC cC ∧
      OrdNodesAt stC.mem nb cap sp2 nf ∧
      (∀ a, ¬ InOrdNodes nb cap a → stC.mem a = mem a) ∧
      stC.regs = stB4.regs ∧ cC ≤ 20 := by
    by_cases hL0 : L.rootId = 0
    · have hc : (Expr.reg 6).eval w stB4 = some 0 := Expr.eval_reg_of_eq (by simp [stB4, stB3, hL0])
      refine ⟨stB4, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        by simpa [sp2, hL0] using hnS, hfrS, rfl, by simp [Expr.size_reg]⟩
    · have hc : (Expr.reg 6).eval w stB4 = some L.rootId := Expr.eval_reg_of_eq (by simp [stB4, stB3])
      have hstL : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 6))) (.const 2)) (.const 0))
          stB4 .normal { stB4 with mem := Function.update stS.mem (nb + 8 * L.rootId + 2) 0 } _ :=
        runs_store_iff.mpr ⟨nb + 8 * L.rootId + 2, 0,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stB4, stB3, stB2, stB1, stA]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stB4, stB3])) (by omega))
            (by omega)) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      refine ⟨_, _, ord_runs_cond_true hc hL0 hstL,
        by dsimp only; rw [show sp2 = sp1.setPar L.rootId 0 by simp [sp2, hL0]]; exact hnS.setPar hL_le (v := 0),
        fun a ha => by dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]; exact hfrS a ha,
        rfl, by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
  obtain ⟨stC, cC, hrunC, hnC, hfrC, hregsC, hcC⟩ := hdetL
  have hdetR : ∃ stD cD, Runs w p ω
      (.cond (.reg 7) (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7))) (.const 2)) (.const 0)) .nop)
      stC .normal stD cD ∧
      OrdNodesAt stD.mem nb cap sp3 nf ∧
      (∀ a, ¬ InOrdNodes nb cap a → stD.mem a = mem a) ∧
      stD.regs = stB4.regs ∧ cD ≤ 20 := by
    by_cases hR0 : R.rootId = 0
    · have hc : (Expr.reg 7).eval w stC = some 0 := Expr.eval_reg_of_eq (by simp [hregsC, stB4, hR0])
      refine ⟨stC, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
        by simpa [sp3, hR0] using hnC, hfrC, hregsC, by simp [Expr.size_reg]⟩
    · have hc : (Expr.reg 7).eval w stC = some R.rootId := Expr.eval_reg_of_eq (by simp [hregsC, stB4])
      have hstR : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 7))) (.const 2)) (.const 0))
          stC .normal { stC with mem := Function.update stC.mem (nb + 8 * R.rootId + 2) 0 } _ :=
        runs_store_iff.mpr ⟨nb + 8 * R.rootId + 2, 0,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hregsC, stB4, stB3, stB2, stB1, stA]))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hregsC, stB4])) (by omega))
            (by omega)) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_const (by omega), rfl, rfl, rfl⟩
      refine ⟨_, _, ord_runs_cond_true hc hR0 hstR,
        by dsimp only; rw [show sp3 = sp2.setPar R.rootId 0 by simp [sp3, hR0]]; exact hnC.setPar hR_le (v := 0),
        fun a ha => by dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]; exact hfrC a ha,
        hregsC, by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩
  obtain ⟨stD, cD, hrunD, hnD, hfrD, hregsD, hcD⟩ := hdetR
  obtain ⟨oF, stF, cF, hrunF, sp', t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hphiF⟩ :=
    hafter3 stD hnD hfrD
      (by simp [hregsD, stB4, stB3, stB2, stB1, stA, st0, startState])
      (by simp [hregsD, stB4, stB3, stB2, stB1, stA])
      (by simp [hregsD, stB4, stB3, stB2, stB1])
      (by simp [hregsD, stB4, stB3, stB2])
      (by simp [hregsD, stB4, stB3])
      (by simp [hregsD, stB4])
  have hfull := ord_runs_seq_normal hload_nb (ord_runs_seq_normal hcall_s (ord_runs_seq_normal ha4
    (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6 (ord_runs_seq_normal ha7
      (ord_runs_seq_normal hrunC (ord_runs_seq_normal hrunD hrunF)))))))
  refine ⟨oF, stF, _, hfull, sp', t', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
  have hrk_s : ts.rank (fun _ => 0) ≤ ordStoreLog eCap :=
    rank_zero_le_ordStoreLog (by have := hok.count_le; omega)
  have hphi_s_mul : ORD_PHI_WEIGHT * ts.treePhi (fun _ => 0) + ORD_PHI_WEIGHT * (t.depthOf u / 2) ≤
      ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + 3 * ORD_PHI_WEIGHT * ordStoreLog eCap := by
    have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi_s
    have h2 : ORD_PHI_WEIGHT * (ts.treePhi (fun _ => 0) + t.depthOf u / 2) =
        ORD_PHI_WEIGHT * ts.treePhi (fun _ => 0) + ORD_PHI_WEIGHT * (t.depthOf u / 2) := by ring
    have h3 : ORD_PHI_WEIGHT * (t.treePhi (fun _ => 0) + 3 * ts.rank (fun _ => 0)) =
        ORD_PHI_WEIGHT * t.treePhi (fun _ => 0) + 3 * ORD_PHI_WEIGHT * ts.rank (fun _ => 0) := by ring
    have h4 := Nat.mul_le_mul_left (3 * ORD_PHI_WEIGHT) hrk_s
    omega
  have hphiLR_mul : ORD_PHI_WEIGHT * (L.treePhi (fun _ => 0) + R.treePhi (fun _ => 0)) ≤
      ORD_PHI_WEIGHT * ts.treePhi (fun _ => 0) := by
    rw [hts_eq]; exact Nat.mul_le_mul_left ORD_PHI_WEIGHT hphiLR
  have hsz_pref : (Expr.load (.bin .add (.reg 0) (.const 4))).size + argsSize [.reg 2, .reg 1] +
      (Expr.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 1))).size +
      (Expr.load (.bin .add (.reg 4) (.const 3))).size + (Expr.load (.reg 4)).size +
      (Expr.load (.bin .add (.reg 4) (.const 1))).size ≤ 40 := by
    simp [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
  unfold ORD_PHI_WEIGHT at hphiF hphi_s_mul hphiLR_mul ⊢
  unfold ORD_JOIN_AMORT at hphiF; unfold ORD_UNLINK_AMORT
  unfold ORD_SPLAY_RATE at hcS
  have h650 : (t.depthOf u / 2) * 650 ≤ 1000 * (t.depthOf u / 2) := by omega
  omega

end MinCostFlow.SparseCore.Program
