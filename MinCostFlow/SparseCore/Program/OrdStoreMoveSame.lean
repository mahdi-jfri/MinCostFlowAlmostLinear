module

public import MinCostFlow.SparseCore.Program.OrdStoreMoveInv
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Pass 7 (`v = v'` branch)

This file verifies the `v = v'` branch of Pass 7 of `ordMoveEndsBody`, freeing the discarded
subtree (`tSel` when `comp = false`, `tRem` when `comp = true`) via `ordFreeTreeBody`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-- The `v = v'` branch of Pass 7 of `moveEnds`. -/
def ordMoveFinishSameBody (freeTreeProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 0))
    (.cond (.reg 13) (.call 15 freeTreeProc [.reg 0, .reg 13]) .nop)
    (.assign 15 (.load (.bin .add (.reg 14) (.reg 1))) ;;
     .cond (.reg 15) (.call 16 freeTreeProc [.reg 0, .reg 15]) .nop ;;
     .store (.bin .add (.reg 14) (.reg 1)) (.reg 13) ;;
     .cond (.reg 13)
       (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 3))
         (.bin .add (.reg 1) (.const 1)))
       .nop)

theorem ordMoveFinishSameBody_noRand (ftP : ℕ) : (ordMoveFinishSameBody ftP).NoRand := by
  simp [ordMoveFinishSameBody, Stmt.NoRand]

theorem ordMoveFinishSame_runs
    {w b v scratch freeTreeProc : ℕ} {p : Program}
    (hfree : p.procs[freeTreeProc]? = some ordFreeTreeBody) (ω : ℕ → Bool)
    {st1 : State} {ord : ℕ → List End} {S : OrdStoreState} {sel : Finset End} {comp : Bool}
    {sp : SplayState ℕ Unit Unit} {tRem : AuxTree} {selNodes : List ℕ}
    (hinv : OrdInv ord S) (hv : v < S.vCap)
    (huniq' : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit ord (.moveEnds v v sel comp)))
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
    (hr0 : st1.regs 0 = b) (hr1 : st1.regs 1 = v)
    (hr3 : st1.regs 3 = if comp then 1 else 0)
    (hr9 : st1.regs 9 = ordNodesBase b S.vCap S.eCap)
    (hr13 : st1.regs 13 = (leftSpine selNodes).rootId)
    (hr14 : st1.regs 14 = ordVRootBase b) :
    ∃ st' c, ∃ S' : OrdStoreState,
      Runs w p ω (ordMoveFinishSameBody freeTreeProc) st1 .normal st' c ∧
      OrdInv (applyOrdEdit ord (.moveEnds v v sel comp)) S' ∧
      OrdArenaAt b S' st'.mem ∧
      OrdFrame b S.vCap S.eCap scratch st1.mem st'.mem ∧
      S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
      c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' + ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_PHI_WEIGHT * tRem.treePhi (fun _ => 0) +
          (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  set en := ordENodeBase b S.vCap with hen
  set vr := ordVRootBase b with hvr_def
  set tSel : AuxTree := leftSpine selNodes with htSel_def
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ scratch := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ scratch := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le; rw [hnb]; omega
  have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S.nextNode a := fun a ha h => by unfold InOrdNodes at h; omega
  have hnd_in_foot : ∀ a, InOrdNodes nb S.nextNode a → ordFoot b S.vCap S.eCap a := fun a h => by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv.next_le
    unfold InOrdNodes at h; unfold ordFoot; rw [hnb] at h; unfold ordNodesBase at h; unfold ordArenaSize at *; omega
  have hen_in_foot : ∀ a, en ≤ a → a < en + 2 * S.eCap → ordFoot b S.vCap S.eCap a := fun a h1 h2 => by
    unfold ordFoot; rw [hen] at h1 h2; unfold ordENodeBase at h1 h2; unfold ordArenaSize; omega
  have hvr_in_foot : ∀ u < S.vCap, ordFoot b S.vCap S.eCap (vr + u) := fun u hu => by
    unfold ordFoot; rw [hvr_def]; unfold ordVRootBase ordArenaSize; omega
  have h6_in_foot : ordFoot b S.vCap S.eCap (b + 6) := by unfold ordFoot ordArenaSize; omega
  cases comp with
  | false =>
    have hcc : (Expr.bin .eq (.reg 3) (.const 0)).eval w st1 = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (v := 0) (by simp [hr3]))
        (Expr.eval_const (by omega)) rfl (by omega)
    have hfree_b1 : ∃ stF cF fhF flF spF, ∃ nfF eNF : ℕ → ℕ,
        Runs w p ω (.cond (.reg 13) (.call 15 freeTreeProc [.reg 0, .reg 13]) .nop) st1 .normal stF cF ∧
        stF.mem (b + 6) = fhF ∧
        OrdNodesAt stF.mem nb S.nextNode spF nfF ∧
        (∀ k < 2 * S.eCap, stF.mem (en + k) = eNF k) ∧
        (∀ a, ¬ InOrdNodes nb S.nextNode a → ¬ (en ≤ a ∧ a < en + 2 * S.eCap) → a ≠ b + 6 → stF.mem a = st1.mem a) ∧
        flF.Perm (tSel.toList ++ S.freeList) ∧ flF.Nodup ∧ FreeChain fhF nfF flF ∧
        (∀ u, (spF.nodes u).rev = (sp.nodes u).rev) ∧
        (∀ u ∉ tSel.toList, spF.nodes u = sp.nodes u ∧ nfF u = S.nextFree u) ∧
        (∀ k < 2 * S.eCap, eNF k = if (∃ u ∈ tSel.toList, (sp.nodes u).val = k) then 0 else S.eNode k) ∧
        cF ≤ ORD_FREE_PER_NODE * tSel.countNodes + 110 := by
      by_cases hS0 : tSel.rootId = 0
      · have htSel_leaf : tSel = .leaf := by
          cases hts : tSel with
          | leaf => rfl
          | node sid sl sr =>
            exfalso; simp only [hts, AuxTree.rootId] at hS0
            exact SplayState.SubtreeInv_nonZero hokS.inv.sub (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)) hS0
        have hc : (Expr.reg 13).eval w st1 = some 0 := Expr.eval_reg_of_eq (hr13.trans hS0)
        refine ⟨st1, _, S.freeHead, S.freeList, sp, S.nextFree, S.eNode,
          ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), hhdr.2.2.2.2.2.2,
          hnodes, hen_at, fun _ _ _ _ => rfl, by simp [htSel_leaf, AuxTree.toList],
          hinv.free_nodup, hinv.free_chain, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
          fun k _ => by simp [htSel_leaf, AuxTree.toList], by simp [Expr.size_reg]⟩
      · have hc : (Expr.reg 13).eval w st1 = some tSel.rootId := Expr.eval_reg_of_eq hr13
        obtain ⟨oF, stF, cF, hrunF, ⟨fhF, flF, spF, nfF, eNF, h6F, hnF, heNF_m, hfrF,
          hpermF, hndF, hfcF, hrevF, houtF, heNF⟩, hcF⟩ :=
          ordFreeTreeBody_runs ω (st := sp) (nf := S.nextFree) (eNode := S.eNode)
            (fh := S.freeHead) (fl := S.freeList) (t := tSel)
            hhdr.2.2.2.2.1 hhdr.2.2.2.1 hhdr.2.2.2.2.2.2 hen_at hnodes
            hokS.inv.nodup (TreeInv.freeTreeShape hokS.inv) rfl
            (fun u hu => hinv.live_le_nextNode hv ((hpart_v u).mpr (Or.inr hu)))
            (fun u hu => by rw [hval_v u ((hpart_v u).mpr (Or.inr hu))]; exact hinv.key_lt v hv u ((hpart_v u).mpr (Or.inr hu)))
            (fun u hu hfl => hinv.free_disj v hv u hfl ((hpart_v u).mpr (Or.inr hu)))
            hinv.free_nodup hinv.free_chain hinv.next_le (by omega) hwide (pos := st1.pos)
        have hcallF : Runs w p ω (.call 15 freeTreeProc [.reg 0, .reg 13]) st1 .normal
            { stF with regs := Function.update st1.regs 15 oF.value } (argsSize [.reg 0, .reg 13] + cF + 1) :=
          runs_call_iff.mpr ⟨[b, tSel.rootId], ordFreeTreeBody, oF, stF, cF,
            evalArgs_cons (Expr.eval_reg_of_eq hr0) (evalArgs_cons (Expr.eval_reg_of_eq hr13) (evalArgs_nil _ _)),
            hfree, hrunF, rfl, rfl, rfl⟩
        refine ⟨_, _, fhF, flF, spF, nfF, eNF, ord_runs_cond_true hc hS0 hcallF,
          h6F, hnF, heNF_m, hfrF, hpermF, hndF, hfcF, hrevF, houtF, heNF, ?_⟩
        simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
        omega
    obtain ⟨stF, cF, fhF, flF, spF, nfF, eNF, hrunF, h6F, hnF, heNF_m, hfrF,
      hpermF, hndF, hfcF, hrevF, houtF, heNF, hcF⟩ := hfree_b1
    have hokR_F : OrdTreeOk S.nextNode spF tRem :=
      { null_node := by
          have h0_ns : (0 : ℕ) ∉ tSel.toList := fun h => SplayState.SubtreeInv_nonZero hokS.inv.sub h rfl
          rw [(houtF 0 h0_ns).1]; exact hokR.null_node
        clean := fun u => by rw [hrevF u]; exact hokR.clean u
        inv := ⟨hokR.inv.nodup, SplayState.SubtreeInv_agree hokR.inv.sub fun x hx =>
          (houtF x (hdisj_rs x hx)).1.symm⟩
        mem_le := hokR.mem_le
        count_le := hokR.count_le }
    set S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := fhF,
        vRoot := Function.update S.vRoot v tRem.rootId, eNode := eNF,
        splay := spF, nextFree := nfF, trees := Function.update S.trees v tRem, freeList := flF }
    have hinv' : OrdInv (applyOrdEdit ord (.moveEnds v v sel false)) S' :=
      moveFinish_same_inv hinv hv huniq' hpart_v hdisj_rs hokR_F
        (fun hne => by rw [(houtF _ (hdisj_rs _ (AuxTree.rootId_mem hne))).1]; exact hppR hne)
        (by
          have h1 : tRem.toList.map (fun x => endOfKey (spF.nodes x).val) =
              tRem.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by rw [(houtF x (hdisj_rs x hx)).1]
          rw [h1, hmap_rem]; rfl)
        (fun x hx => by
          have hx_ns : x ∉ tSel.toList := fun hs => hx ((hpart_v x).mpr (Or.inr hs))
          exact ⟨(houtF x hx_ns).1.trans (hout_v x hx), (houtF x hx_ns).2⟩)
        (fun x hx => by rw [(houtF x (hdisj_rs x hx)).1]; exact hval_v x ((hpart_v x).mpr (Or.inl hx)))
        hpermF hndF hfcF
        (fun k hk => by
          rw [heNF k hk]
          refine if_congr ⟨fun ⟨u, hu, hv1⟩ => ⟨u, hu, (hval_v u ((hpart_v u).mpr (Or.inr hu))).symm.trans hv1⟩,
            fun ⟨u, hu, hv1⟩ => ⟨u, hu, (hval_v u ((hpart_v u).mpr (Or.inr hu))).trans hv1⟩⟩ rfl rfl)
    have harena' : OrdArenaAt b S' stF.mem :=
      { hdr_vCap := (hfrF b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.1
        hdr_eCap := (hfrF (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.1
        hdr_vRoot := (hfrF (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.1
        hdr_eNode := (hfrF (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.1
        hdr_nodes := (hfrF (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.2.1
        hdr_next := (hfrF (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.2.2.1
        hdr_free := h6F
        vRoot_at := fun u hu => by
          dsimp only [S'] at hu
          rw [hfrF (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
            (by rw [hen]; unfold ordVRootBase ordENodeBase; omega) (by unfold ordVRootBase; omega),
            hvr_at u hu]
          by_cases huv : u = v <;> simp [S', huv]
        eNode_at := heNF_m
        nodes_at := hnF }
    have hframe' : OrdFrame b S.vCap S.eCap scratch st1.mem stF.mem :=
      ⟨fun a ha => (hfrF a (fun h => by unfold InOrdNodes at h; omega)
          (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans (hz a ha),
       fun a _ hnf => hfrF a (fun h => hnf (hnd_in_foot a h))
          (fun ⟨h1, h2⟩ => hnf (hen_in_foot a h1 h2)) (fun h => hnf (by rw [h]; exact h6_in_foot))⟩
    have hphi_upd := sumTreePhi_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tRem from Function.update_self v tRem S.trees] at hphi_upd
    have hcnt_upd := sumCountNodes_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tRem from Function.update_self v tRem S.trees] at hcnt_upd
    refine ⟨stF, _, S', ord_runs_cond_true hcc Nat.one_ne_zero hrunF, hinv', harena', hframe', rfl, rfl, ?_⟩
    have h160 : 160 ≤ 160 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 160 hlog
    have hsp : (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap =
        1000 * selNodes.length * ordStoreLog S.eCap + ORD_JOIN_AMORT * ordStoreLog S.eCap + 160 * ordStoreLog S.eCap := by ring
    unfold ORD_FREE_PER_NODE at hcF; unfold ORD_JOIN_AMORT at hsp
    unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT ORD_JOIN_AMORT
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
    have hfree_b2 : ∃ stF cF fhF flF spF, ∃ nfF eNF : ℕ → ℕ,
        Runs w p ω (.cond (.reg 15) (.call 16 freeTreeProc [.reg 0, .reg 15]) .nop) st2 .normal stF cF ∧
        stF.regs 1 = v ∧ stF.regs 9 = nb ∧ stF.regs 13 = tSel.rootId ∧ stF.regs 14 = vr ∧
        stF.mem (b + 6) = fhF ∧
        OrdNodesAt stF.mem nb S.nextNode spF nfF ∧
        (∀ k < 2 * S.eCap, stF.mem (en + k) = eNF k) ∧
        (∀ a, ¬ InOrdNodes nb S.nextNode a → ¬ (en ≤ a ∧ a < en + 2 * S.eCap) → a ≠ b + 6 → stF.mem a = st1.mem a) ∧
        flF.Perm (tRem.toList ++ S.freeList) ∧ flF.Nodup ∧ FreeChain fhF nfF flF ∧
        (∀ u, (spF.nodes u).rev = (sp.nodes u).rev) ∧
        (∀ u ∉ tRem.toList, spF.nodes u = sp.nodes u ∧ nfF u = S.nextFree u) ∧
        (∀ k < 2 * S.eCap, eNF k = if (∃ u ∈ tRem.toList, (sp.nodes u).val = k) then 0 else S.eNode k) ∧
        cF ≤ ORD_FREE_PER_NODE * tRem.countNodes + 110 := by
      by_cases hR0 : tRem.rootId = 0
      · have htRem_leaf : tRem = .leaf := by
          cases htr : tRem with
          | leaf => rfl
          | node rid rl rr =>
            exfalso; simp only [htr, AuxTree.rootId] at hR0
            exact SplayState.SubtreeInv_nonZero hokR.inv.sub (by rw [htr]; exact AuxTree.rootId_mem (t := .node rid rl rr) (by simp)) hR0
        have hc : (Expr.reg 15).eval w st2 = some 0 := Expr.eval_reg_of_eq (by simp [st2, hR0])
        refine ⟨st2, _, S.freeHead, S.freeList, sp, S.nextFree, S.eNode,
          ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          by simp [st2, hr1], by simp [st2, hr9], by simp [st2, hr13], by simp [st2, hr14],
          hhdr.2.2.2.2.2.2, hnodes, hen_at, fun _ _ _ _ => rfl, by simp [htRem_leaf, AuxTree.toList],
          hinv.free_nodup, hinv.free_chain, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
          fun k _ => by simp [htRem_leaf, AuxTree.toList], by simp [Expr.size_reg]⟩
      · have hc : (Expr.reg 15).eval w st2 = some tRem.rootId := Expr.eval_reg_of_eq (by simp [st2])
        obtain ⟨oF, stF, cF, hrunF, ⟨fhF, flF, spF, nfF, eNF, h6F, hnF, heNF_m, hfrF,
          hpermF, hndF, hfcF, hrevF, houtF, heNF⟩, hcF⟩ :=
          ordFreeTreeBody_runs ω (st := sp) (nf := S.nextFree) (eNode := S.eNode)
            (fh := S.freeHead) (fl := S.freeList) (t := tRem)
            hhdr.2.2.2.2.1 hhdr.2.2.2.1 hhdr.2.2.2.2.2.2 hen_at hnodes
            hokR.inv.nodup (TreeInv.freeTreeShape hokR.inv) rfl
            (fun u hu => hinv.live_le_nextNode hv ((hpart_v u).mpr (Or.inl hu)))
            (fun u hu => by rw [hval_v u ((hpart_v u).mpr (Or.inl hu))]; exact hinv.key_lt v hv u ((hpart_v u).mpr (Or.inl hu)))
            (fun u hu hfl => hinv.free_disj v hv u hfl ((hpart_v u).mpr (Or.inl hu)))
            hinv.free_nodup hinv.free_chain hinv.next_le (by omega) hwide (pos := st2.pos)
        have hcallF : Runs w p ω (.call 16 freeTreeProc [.reg 0, .reg 15]) st2 .normal
            { stF with regs := Function.update st2.regs 16 oF.value } (argsSize [.reg 0, .reg 15] + cF + 1) :=
          runs_call_iff.mpr ⟨[b, tRem.rootId], ordFreeTreeBody, oF, stF, cF,
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2, hr0]))
              (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st2])) (evalArgs_nil _ _)),
            hfree, hrunF, rfl, rfl, rfl⟩
        refine ⟨_, _, fhF, flF, spF, nfF, eNF, ord_runs_cond_true hc hR0 hcallF,
          by simp [st2, hr1], by simp [st2, hr9], by simp [st2, hr13], by simp [st2, hr14],
          h6F, hnF, heNF_m, hfrF, hpermF, hndF, hfcF, hrevF, houtF, heNF, ?_⟩
        simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
        omega
    obtain ⟨stF, cF, fhF, flF, spF, nfF, eNF, hrunF, f1, f9, f13, f14, h6F, hnF, heNF_m, hfrF,
      hpermF, hndF, hfcF, hrevF, houtF, heNF, hcF⟩ := hfree_b2
    have hs_vr : Runs w p ω (.store (.bin .add (.reg 14) (.reg 1)) (.reg 13)) stF .normal
        { stF with mem := Function.update stF.mem (vr + v) tSel.rootId } _ :=
      runs_store_iff.mpr ⟨vr + v, tSel.rootId, Expr.eval_add (Expr.eval_reg_of_eq f14) (Expr.eval_reg_of_eq f1)
        (by rw [hvr_def]; unfold ordVRootBase; omega), Expr.eval_reg_of_eq f13, rfl, rfl, rfl⟩
    set st3 : State := { stF with mem := Function.update stF.mem (vr + v) tSel.rootId }
    have hnot_vrv : ¬ InOrdNodes nb S.nextNode (vr + v) :=
      hnot_nd _ (by rw [hvr_def, hnb]; unfold ordVRootBase ordNodesBase; omega)
    have hn3 : OrdNodesAt st3.mem nb S.nextNode spF nfF :=
      hnF.congr fun a ha => Function.update_of_ne (fun (h : a = vr + v) => hnot_vrv (h ▸ ha)) _ _
    have hokS_F : OrdTreeOk S.nextNode spF tSel :=
      { null_node := by
          have h0_nr : (0 : ℕ) ∉ tRem.toList := fun h => SplayState.SubtreeInv_nonZero hokR.inv.sub h rfl
          rw [(houtF 0 h0_nr).1]; exact hokS.null_node
        clean := fun u => by rw [hrevF u]; exact hokS.clean u
        inv := ⟨hokS.inv.nodup, SplayState.SubtreeInv_agree hokS.inv.sub fun x hx =>
          (houtF x (fun hr => hdisj_rs x hr hx)).1.symm⟩
        mem_le := hokS.mem_le
        count_le := hokS.count_le }
    obtain ⟨stP, cP, hrunP, -, hnP, hfrP, hokS_P, hppS_P, hspP_out, hspP_val, hcP⟩ :=
      ordMoveFinish_setPpar (p := p) ω (stM := st3) f1 f9 f13 hn3 hokS_F (by omega) (by omega) hwide
    set spP := if tSel.rootId = 0 then spF else spF.setPpar tSel.rootId (v + 1)
    set S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := fhF,
        vRoot := Function.update S.vRoot v tSel.rootId, eNode := eNF,
        splay := spP, nextFree := nfF, trees := Function.update S.trees v tSel, freeList := flF }
    have hinv' : OrdInv (applyOrdEdit ord (.moveEnds v v sel true)) S' :=
      moveFinish_same_inv hinv hv huniq'
        (fun x => by rw [hpart_v]; tauto) (fun x hs hr => hdisj_rs x hr hs) hokS_P hppS_P
        (by
          have h1 : tSel.toList.map (fun x => endOfKey (spP.nodes x).val) =
              tSel.toList.map (fun x => endOfKey (sp.nodes x).val) :=
            List.map_congr_left fun x hx => by
              rw [hspP_val x, (houtF x (fun hr => hdisj_rs x hr hx)).1]
          rw [h1, hmap_sel]; simp [movedBy])
        (fun x hx => by
          have hx_nr : x ∉ tRem.toList := fun hr => hx ((hpart_v x).mpr (Or.inl hr))
          by_cases hx0 : x = 0
          · exact ⟨by rw [hx0, hokS_P.null_node, hinv.null_node], (houtF x hx_nr).2⟩
          · have hx_ntS : x ≠ tSel.rootId := by
              cases hts : tSel with
              | leaf => simp [hts, AuxTree.rootId]; exact hx0
              | node sid sl sr =>
                intro h; simp only [hts, AuxTree.rootId] at h
                exact hx ((hpart_v x).mpr (Or.inr (by rw [h, hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp))))
            exact ⟨(hspP_out x hx_ntS).trans ((houtF x hx_nr).1.trans (hout_v x hx)), (houtF x hx_nr).2⟩)
        (fun x hx => by rw [hspP_val x, (houtF x (fun hr => hdisj_rs x hr hx)).1]; exact hval_v x ((hpart_v x).mpr (Or.inr hx)))
        hpermF hndF hfcF
        (fun k hk => by
          rw [heNF k hk]
          refine if_congr ⟨fun ⟨u, hu, hv1⟩ => ⟨u, hu, (hval_v u ((hpart_v u).mpr (Or.inl hu))).symm.trans hv1⟩,
            fun ⟨u, hu, hv1⟩ => ⟨u, hu, (hval_v u ((hpart_v u).mpr (Or.inl hu))).trans hv1⟩⟩ rfl rfl)
    have harena' : OrdArenaAt b S' stP.mem :=
      { hdr_vCap := (hfrP b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF b (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.1))
        hdr_eCap := (hfrP (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF (b + 1) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.1))
        hdr_vRoot := (hfrP (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF (b + 2) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.1))
        hdr_eNode := (hfrP (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF (b + 3) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.1))
        hdr_nodes := (hfrP (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF (b + 4) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.2.1))
        hdr_next := (hfrP (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF (b + 5) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans hhdr.2.2.2.2.2.1))
        hdr_free := (hfrP (b + 6) (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans h6F)
        vRoot_at := fun u hu => by
          dsimp only [S'] at hu
          rw [hfrP (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))]
          dsimp only [st3]
          by_cases huv : u = v
          · subst huv; simp [S', hvr_def]
          · rw [Function.update_of_ne (by rw [hvr_def]; omega),
              hfrF (ordVRootBase b + u) (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))
                (by rw [hen]; unfold ordVRootBase ordENodeBase; omega) (by unfold ordVRootBase; omega),
              hvr_at u hu]
            simp [S', huv]
        eNode_at := fun k hk => by
          dsimp only [S'] at hk
          rw [hfrP (ordENodeBase b S.vCap + k) (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))]
          dsimp only [st3]
          rw [Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase ordENodeBase; omega)]
          exact heNF_m k hk
        nodes_at := hnP }
    have hframe' : OrdFrame b S.vCap S.eCap scratch st1.mem stP.mem :=
      ⟨fun a ha => (hfrP a (fun h => by unfold InOrdNodes at h; omega)).trans
          ((Function.update_of_ne (by rw [hvr_def]; unfold ordVRootBase; omega) _ _).trans
            ((hfrF a (fun h => by unfold InOrdNodes at h; omega)
              (by rw [hen]; unfold ordENodeBase; omega) (by omega)).trans (hz a ha))),
       fun a _ hnf => (hfrP a (fun h => hnf (hnd_in_foot a h))).trans
          ((Function.update_of_ne (fun h => hnf (by rw [h]; exact hvr_in_foot v hv)) _ _).trans
            (hfrF a (fun h => hnf (hnd_in_foot a h))
              (fun ⟨h1, h2⟩ => hnf (hen_in_foot a h1 h2)) (fun h => hnf (by rw [h]; exact h6_in_foot))))⟩
    have hphi_upd := sumTreePhi_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tSel from Function.update_self v tSel S.trees] at hphi_upd
    have hcnt_upd := sumCountNodes_update (S := S) (S' := S') hv rfl (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tSel from Function.update_self v tSel S.trees] at hcnt_upd
    refine ⟨stP, _, S',
      ord_runs_cond_false hcc (ord_runs_seq_normal ha15 (ord_runs_seq_normal hrunF (ord_runs_seq_normal hs_vr hrunP))),
      hinv', harena', hframe', rfl, rfl, ?_⟩
    have hmul_sel := Nat.mul_le_mul_left 1000 htSel_phi
    have h160 : 160 ≤ 160 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 160 hlog
    have hsplit : (1000 * selNodes.length + ORD_JOIN_AMORT + 160) * ordStoreLog S.eCap =
        1000 * (selNodes.length * ordStoreLog S.eCap) + ORD_JOIN_AMORT * ordStoreLog S.eCap + 160 * ordStoreLog S.eCap := by ring
    unfold ORD_FREE_PER_NODE at hcF; unfold ORD_JOIN_AMORT at hsplit
    unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT ORD_JOIN_AMORT
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

end MinCostFlow.SparseCore.Program
