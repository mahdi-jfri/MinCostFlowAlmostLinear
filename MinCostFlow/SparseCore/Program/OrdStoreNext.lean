module

public import MinCostFlow.SparseCore.Program.OrdStoreSplayRuns
public import MinCostFlow.SparseCore.Program.OrdStoreInsertBack
import Mathlib.Tactic

/-!
# Order Store `next` Query Procedure (`op 2`)

This file implements and verifies `ordStoreNextBody` (`op 2`, `[b, v, key, heap]`): it splays
`eNode[key]` to the root of `S.trees v`, walks to the cyclic successor `w`, splays `w` to
amortize the walk, writes `w.val` at `heap`, and returns `heap + 1` in `O(ordStoreLog eCap)`
amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

def ORD_NEXT_MUL : ℕ := 8500

/-! ### Operation `2`: `next` (`[b, v, key, heap]`) -/

/-- `ordStoreNext` (`op 2`) on `[b, v, key, heap]`. -/
def ordStoreNextBody (splayRootProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .call 7 splayRootProc [.reg 0, .reg 6] ;;
  .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 6))) (.const 1))) ;;
  .cond (.reg 8) (.assign 9 (.reg 8)) (.assign 9 (.reg 6)) ;;
  .assign 10 (.load (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9)))) ;;
  .loop (.reg 10)
    (.assign 9 (.reg 10) ;;
     .assign 10 (.load (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))))) ;;
  .call 11 splayRootProc [.reg 0, .reg 9] ;;
  .assign 12 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))) (.const 5))) ;;
  .store (.reg 3) (.reg 12) ;;
  .ret (.bin .add (.reg 3) (.const 1))

theorem ordStoreNextBody_noRand (srP : ℕ) : (ordStoreNextBody srP).NoRand := by
  simp [ordStoreNextBody, Stmt.NoRand]

/-- Walking down left pointers from `t.rootId` reaches `leftmostId t` in `≤ 25 * leftSpineLen t + 10` steps. -/
private theorem ordLeftWalk_runs
    {w nb cap : ℕ} {p : Program} (ω : ℕ → Bool)
    {sp : SplayState ℕ Unit Unit} {nf : ℕ → ℕ}
    (hnb_w : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∀ (t : AuxTree) (par : ℕ), t ≠ .leaf →
      SplayState.SubtreeInv ordPayload sp par t → (∀ u ∈ t.toList, u ≤ cap) →
      ∀ (st : State), st.regs 5 = nb → st.regs 9 = t.rootId →
        st.regs 10 = (sp.nodes t.rootId).left → OrdNodesAt st.mem nb cap sp nf →
        ∃ st' c, Runs w p ω
          (.loop (.reg 10) (.assign 9 (.reg 10) ;; .assign 10 (.load (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))))))
          st .normal st' c ∧
          st'.mem = st.mem ∧
          (∀ r, r ≠ 9 → r ≠ 10 → st'.regs r = st.regs r) ∧
          st'.regs 9 = leftmostId t ∧
          c ≤ 25 * leftSpineLen t + 10 := by
  intro t
  induction t with
  | leaf => intro _ hne; exact absurd rfl hne
  | node id l r ihl _ =>
    intro par _ hsub hle st r5 r9 r10 hn
    rcases hsub with ⟨hid_nz, hidL, -, -, -, -, -, hsubL, -⟩
    simp only [AuxTree.rootId] at r9 r10
    cases hl : l with
    | leaf =>
      have hc : (Expr.reg 10).eval w st = some 0 := Expr.eval_reg_of_eq (by rw [r10, hidL, hl]; rfl)
      refine ⟨st, _, ord_runs_loop_false hc, rfl, fun _ _ _ => rfl, by simp [r9, hl, leftmostId],
        by simp [Expr.size_reg, leftSpineLen]⟩
    | node lid ll lr =>
      have hlid_nz : lid ≠ 0 := (hl ▸ hsubL).1
      have hlid_c : lid ≤ cap := hle lid (by rw [hl]; exact List.mem_append_left _ (List.mem_append_left _ (AuxTree.rootId_mem (t := .node lid ll lr) (by simp))))
      have hc : (Expr.reg 10).eval w st = some lid := Expr.eval_reg_of_eq (by rw [r10, hidL, hl]; rfl)
      have ha9 : Runs w p ω (.assign 9 (.reg 10)) st .normal { st with regs := Function.update st.regs 9 lid } _ :=
        runs_assign_iff.mpr ⟨lid, Expr.eval_reg_of_eq (by rw [r10, hidL, hl]; rfl), rfl, rfl, rfl⟩
      set st1 : State := { st with regs := Function.update st.regs 9 lid }
      have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))))) st1 .normal
          { st1 with regs := Function.update st1.regs 10 (sp.nodes lid).left } _ :=
        runs_assign_iff.mpr ⟨(sp.nodes lid).left, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, r5]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st1])) (by omega)) (by omega))
          (hn lid hlid_c).1, rfl, rfl, rfl⟩
      set st2 : State := { st1 with regs := Function.update st1.regs 10 (sp.nodes lid).left }
      obtain ⟨stF, cF, hrunF, hmemF, hregF, r9F, hcF⟩ :=
        ihl id (by rw [hl]; simp) hsubL (fun x hx => hle x (List.mem_append_left _ (List.mem_append_left _ hx)))
          st2 (by simp [st2, st1, r5]) (by simp [st2, st1, hl, AuxTree.rootId]) (by simp [st2, hl, AuxTree.rootId]) hn
      refine ⟨stF, _, ord_runs_loop_true hc hlid_nz (ord_runs_seq_normal ha9 ha10) hrunF, hmemF,
        fun r h9 h10 => by rw [hregF r h9 h10]; simp [st2, st1, h9, h10],
        by simpa [leftmostId, hl] using r9F, ?_⟩
      simp only [leftSpineLen, hl, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at hcF ⊢
      omega

private theorem leftmostId_getElem_zero {t : AuxTree} (ht : t ≠ .leaf) :
    t.toList.getD 0 0 = leftmostId t := by
  induction t with
  | leaf => exact absurd rfl ht
  | node id l r ihl _ =>
    cases l with
    | leaf => simp [leftmostId, AuxTree.toList]
    | node lid ll lr =>
      have hpos : 0 < (AuxTree.node lid ll lr).toList.length := by
        rw [AuxTree.length_toList]; simp [AuxTree.countNodes]
      have h1 : (AuxTree.node id (.node lid ll lr) r).toList.getD 0 0 =
          (AuxTree.node lid ll lr).toList.getD 0 0 := by
        rw [AuxTree.toList, List.append_assoc, List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_append_left hpos]
      rw [h1, ihl (by simp)]; simp [leftmostId]

theorem ordStoreNextBody_runs
    {w b v key heap pos rotProc stepProc splayProc splayRootProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hsplayRoot : p.procs[splayRootProc]? = some (ordSplayRootBody splayProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem) (hv : v < S.vCap)
    (hkey_mem : endOfKey key ∈ ord v)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap + 1 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordStoreNextBody splayRootProc) (startState [b, v, key, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      (∃ S' : OrdStoreState,
        OrdInv ord S' ∧ OrdArenaAt b S' st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        st'.mem heap =
          endKey ((ord v).getD (((ord v).idxOf (endOfKey key) + 1) % (ord v).length) (0, true)) ∧
        ZeroFrom st'.mem (heap + 1) ∧
        (∀ a < heap, ¬ ordFoot b S.vCap S.eCap a → st'.mem a = mem a) ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + ORD_NEXT_MUL * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  have hwide : 16 ≤ 2 ^ w := by omega
  have hkey_lt : key < 2 * S.eCap := by simpa [endKey_endOfKey] using hinv.ord_unique.key_lt hkey_mem
  have hu_spec : S.eNode key ∈ (S.trees v).toList ∧ (S.splay.nodes (S.eNode key)).val = key := by
    rcases hinv.eNode_spec key hkey_lt with ⟨_, hnone⟩ | ⟨w0, hw0, hmem0, hval0⟩
    · exfalso
      rw [← hinv.list_eq v hv, List.mem_map] at hkey_mem
      rcases hkey_mem with ⟨x, hx, hxe⟩
      exact hnone v hv x hx (endOfKey_injective hxe)
    · have hw_mem : endOfKey key ∈ ord w0 := by
        rw [← hinv.list_eq w0 hw0]; exact List.mem_map.mpr ⟨_, hmem0, by rw [hval0]⟩
      have hwv : w0 = v := hinv.ord_unique.unique_v hw_mem hkey_mem
      subst hwv; exact ⟨hmem0, hval0⟩
  set u := S.eNode key with hu_def
  set en := ordENodeBase b S.vCap with hen_def
  set nb := ordNodesBase b S.vCap S.eCap with hnb_def
  set st0 : State := startState [b, v, key, heap] mem pos
  have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 3)))) st0 .normal
      { st0 with regs := Function.update st0.regs 4 en } _ :=
    runs_assign_iff.mpr ⟨en, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_eNode, rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 4 en }
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 4)))) st1 .normal
      { st1 with regs := Function.update st1.regs 5 nb } _ :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega)) harena.hdr_nodes, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 5 nb }
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 4) (.reg 2)))) st2 .normal
      { st2 with regs := Function.update st2.regs 6 u } _ :=
    runs_assign_iff.mpr ⟨u, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := en) (by simp [st2, st1]))
      (Expr.eval_reg_of_eq (v := key) (by simp [st2, st1, st0, startState]))
      (by rw [hen_def]; unfold ordENodeBase; omega))
      (by rw [hen_def]; exact harena.eNode_at key hkey_lt), rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 6 u }
  -- Splay 1: bring u to root of S1.trees v
  obtain ⟨oS1, stS1, cS1, hrunS1, ⟨S1, -, hinv1, harena1, hfr1, hv1, he1, hrt1, hlist1, -, hcnt1, hphi1⟩, hcS1⟩ :=
    ordSplayRootBody_runs hrot hstep hsplay ω hinv harena hv hu_spec.1 hfoot hz (by omega) hwide (pos := st3.pos)
  have hcall1 : Runs w p ω (.call 7 splayRootProc [.reg 0, .reg 6]) st3 .normal
      { stS1 with regs := Function.update st3.regs 7 oS1.value } (argsSize [.reg 0, .reg 6] + cS1 + 1) :=
    runs_call_iff.mpr ⟨[b, u], ordSplayRootBody splayProc, oS1, stS1, cS1,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]))
        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3])) (evalArgs_nil _ _)),
      hsplayRoot, hrunS1, rfl, rfl, rfl⟩
  set st4 : State := { stS1 with regs := Function.update st3.regs 7 oS1.value }
  obtain ⟨L, R, htv1⟩ : ∃ L R, S1.trees v = .node u L R := by
    cases htv : S1.trees v with
    | leaf => exfalso; have h1 := hlist1; rw [htv] at h1; exact List.not_mem_nil (h1 ▸ hu_spec.1)
    | node id l r => simp only [htv, AuxTree.rootId] at hrt1; exact ⟨l, r, by rw [hrt1]⟩
  have htv1_inv : TreeInv ordPayload S1.splay (.node u L R) := htv1 ▸ hinv1.tree_inv v (by rw [hv1]; exact hv)
  rcases htv1_inv.sub with ⟨hu_nz, huL, huR, -, -, -, -, hsubL, hsubR⟩
  rcases AuxTree.nodup_node_unfold htv1_inv.nodup with ⟨hLnd, hu_nL, hRnd, hu_nR, hLR⟩
  have hnb1 : ordNodesBase b S1.vCap S1.eCap = nb := by rw [hv1, he1]
  have hnb1_w : nb + 8 * (S1.nextNode + 1) < 2 ^ w := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv1.next_le; rw [he1] at this; rw [hnb_def]; omega
  have hu_c1 : u ≤ S1.nextNode := (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (by rw [hlist1]; exact hu_spec.1)).2
  have hm_uR : stS1.mem (nb + 8 * u + 1) = R.rootId := by
    have h := (harena1.nodes_at u hu_c1).2.1; rw [hnb1] at h; simpa [ordNodeAddr, huR] using h
  have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 6))) (.const 1)))) st4 .normal
      { st4 with regs := Function.update st4.regs 8 R.rootId } _ :=
    runs_assign_iff.mpr ⟨R.rootId, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st4, st3, st2]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [st4, st3])) (by omega)) (by omega))
      (Expr.eval_const (by omega)) (by omega)) hm_uR, rfl, rfl, rfl⟩
  set st5 : State := { st4 with regs := Function.update st4.regs 8 R.rootId }
  -- Target subtree for left-walk: R if R ≠ leaf, else (.node u L .leaf)
  set tWalk : AuxTree := if R = .leaf then .node u L .leaf else R with htWalk_def
  set wNode : ℕ := leftmostId tWalk with hwNode_def
  have htWalk_ne : tWalk ≠ .leaf := by by_cases hR : R = .leaf <;> simp [htWalk_def, hR]
  have hcond_r9 : ∃ st6 c6,
      Runs w p ω (.cond (.reg 8) (.assign 9 (.reg 8)) (.assign 9 (.reg 6))) st5 .normal st6 c6 ∧
      st6.mem = stS1.mem ∧ st6.regs 0 = b ∧ st6.regs 3 = heap ∧ st6.regs 5 = nb ∧
      st6.regs 9 = tWalk.rootId ∧ c6 ≤ 10 := by
    by_cases hR : R = .leaf
    · have hc : (Expr.reg 8).eval w st5 = some 0 := Expr.eval_reg_of_eq (by simp [st5, hR, AuxTree.rootId])
      have ha9 : Runs w p ω (.assign 9 (.reg 6)) st5 .normal { st5 with regs := Function.update st5.regs 9 u } _ :=
        runs_assign_iff.mpr ⟨u, Expr.eval_reg_of_eq (by simp [st5, st4, st3]), rfl, rfl, rfl⟩
      refine ⟨_, _, ord_runs_cond_false hc ha9, rfl, by simp [st5, st4, st3, st2, st1, st0, startState],
        by simp [st5, st4, st3, st2, st1, st0, startState], by simp [st5, st4, st3, st2],
        by simp [htWalk_def, hR, AuxTree.rootId], by simp [Expr.size_reg]⟩
    · have hR_nz : R.rootId ≠ 0 := by
        cases hR' : R with
        | leaf => exact absurd hR' hR
        | node rid rl rr => exact (hR' ▸ hsubR).1
      have hc : (Expr.reg 8).eval w st5 = some R.rootId := Expr.eval_reg_of_eq (by simp [st5])
      have ha9 : Runs w p ω (.assign 9 (.reg 8)) st5 .normal { st5 with regs := Function.update st5.regs 9 R.rootId } _ :=
        runs_assign_iff.mpr ⟨R.rootId, Expr.eval_reg_of_eq (by simp [st5]), rfl, rfl, rfl⟩
      refine ⟨_, _, ord_runs_cond_true hc hR_nz ha9, rfl, by simp [st5, st4, st3, st2, st1, st0, startState],
        by simp [st5, st4, st3, st2, st1, st0, startState], by simp [st5, st4, st3, st2],
        by simp [htWalk_def, hR], by simp [Expr.size_reg]⟩
  obtain ⟨st6, c6, hrun6, hmem6, r0_6, r3_6, r5_6, r9_6, hc6⟩ := hcond_r9
  have htWalk_sub : SplayState.SubtreeInv ordPayload S1.splay (if R = .leaf then 0 else u) tWalk ∧
      (∀ x ∈ tWalk.toList, x ∈ (S1.trees v).toList) ∧ tWalk.toList.Nodup := by
    by_cases hR : R = .leaf
    · subst hR; simp only [htWalk_def, ↓reduceIte]
      exact ⟨htv1_inv.sub, fun x hx => by rw [htv1]; exact hx, htv1_inv.nodup⟩
    · simp only [htWalk_def, hR, ite_false]
      exact ⟨hsubR, fun x hx => by rw [htv1]; exact List.mem_append_right _ hx, hRnd⟩
  have htWalk_root_c : tWalk.rootId ≤ S1.nextNode :=
    (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (htWalk_sub.2.1 _ (AuxTree.rootId_mem htWalk_ne))).2
  have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))))) st6 .normal
      { st6 with regs := Function.update st6.regs 10 (S1.splay.nodes tWalk.rootId).left } _ :=
    runs_assign_iff.mpr ⟨(S1.splay.nodes tWalk.rootId).left, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r5_6)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r9_6) (by omega)) (by omega))
      (by rw [hmem6]; have h := (harena1.nodes_at tWalk.rootId htWalk_root_c).1; rwa [hnb1] at h), rfl, rfl, rfl⟩
  set st7 : State := { st6 with regs := Function.update st6.regs 10 (S1.splay.nodes tWalk.rootId).left }
  obtain ⟨stW, cW, hrunW, hmemW, hregW, r9W, hcW⟩ :=
    ordLeftWalk_runs (p := p) ω hnb1_w hwide tWalk (if R = .leaf then 0 else u) htWalk_ne htWalk_sub.1
      (fun x hx => (hinv1.live_le_nextNode (by rw [hv1]; exact hv) (htWalk_sub.2.1 x hx)).2)
      st7 (by simp [st7, r5_6]) (by simp [st7, r9_6]) (by simp [st7]) (by dsimp only [st7]; rw [hmem6, ← hnb1]; exact harena1.nodes_at)
  have hwNode_mem_walk : wNode ∈ tWalk.toList := by
    have hpos : 0 < tWalk.toList.length := by
      cases htw : tWalk with
      | leaf => exact absurd htw htWalk_ne
      | node _ _ _ => rw [AuxTree.length_toList]; simp [AuxTree.countNodes]
    have hgd := leftmostId_getElem_zero htWalk_ne
    rw [List.getD_eq_getElem _ _ hpos] at hgd; rw [hwNode_def, ← hgd]; exact List.getElem_mem hpos
  have hwNode_mem_v : wNode ∈ (S1.trees v).toList := htWalk_sub.2.1 wNode hwNode_mem_walk
  have hdepth_ge : leftSpineLen tWalk ≤ (S1.trees v).depthOf wNode := by
    have hd_w := depthOf_leftmostId htWalk_sub.2.2 htWalk_ne
    rw [← hwNode_def] at hd_w
    by_cases hR : R = .leaf
    · rw [htv1, hR]; simpa [htWalk_def, hR] using Nat.le_of_eq hd_w.symm
    · simp only [htWalk_def, hR, ite_false] at hd_w hwNode_mem_walk ⊢
      have hw_ne_u : wNode ≠ u := fun h => hu_nR (h ▸ hwNode_mem_walk)
      have hw_nL : wNode ∉ L.toList := fun h => hLR wNode h hwNode_mem_walk
      rw [htv1]; simp [AuxTree.depthOf, hw_ne_u, hw_nL, hwNode_mem_walk, hd_w]
  -- Splay 2: splay wNode to root of S2.trees v
  have hmemW_eq : stW.mem = stS1.mem := hmemW.trans hmem6
  have harenaW : OrdArenaAt b S1 stW.mem := by rw [hmemW_eq]; exact harena1
  have hzW : ZeroFrom stW.mem heap := by rw [hmemW_eq]; exact hfr1.1
  obtain ⟨oS2, stS2, cS2, hrunS2, ⟨S2, -, hinv2, harena2, hfr2, hv2, he2, -, hlist2, -, hcnt2, hphi2⟩, hcS2⟩ :=
    ordSplayRootBody_runs hrot hstep hsplay ω hinv1 harenaW
      (by rw [hv1]; exact hv) hwNode_mem_v (by rw [hv1, he1]; exact hfoot) hzW
      (by omega) hwide (pos := stW.pos)
  have hcall2 : Runs w p ω (.call 11 splayRootProc [.reg 0, .reg 9]) stW .normal
      { stS2 with regs := Function.update stW.regs 11 oS2.value } (argsSize [.reg 0, .reg 9] + cS2 + 1) :=
    runs_call_iff.mpr ⟨[b, wNode], ordSplayRootBody splayProc, oS2, stS2, cS2,
      evalArgs_cons (Expr.eval_reg_of_eq (by rw [hregW 0 (by decide) (by decide)]; simp [st7, r0_6]))
        (evalArgs_cons (Expr.eval_reg_of_eq r9W) (evalArgs_nil _ _)),
      hsplayRoot, hrunS2, rfl, rfl, rfl⟩
  set st8 : State := { stS2 with regs := Function.update stW.regs 11 oS2.value }
  have hnb2 : ordNodesBase b S2.vCap S2.eCap = nb := by rw [hv2, he2, hv1, he1]
  have hwNode_c2 : wNode ≤ S2.nextNode := (hinv2.live_le_nextNode (by rw [hv2, hv1]; exact hv) (by rw [hlist2]; exact hwNode_mem_v)).2
  have hnb2_w : nb + 8 * (S2.nextNode + 1) < 2 ^ w := by
    have := ordNodesBase_end b S.vCap S.eCap; have := hinv2.next_le; rw [he2, he1] at this; rw [hnb_def]; omega
  have hr5_8 : st8.regs 5 = nb := by
    dsimp only [st8]; rw [Function.update_of_ne (by decide), hregW 5 (by decide) (by decide)]; simp [st7, r5_6]
  have hr9_8 : st8.regs 9 = wNode := by
    dsimp only [st8]; rw [Function.update_of_ne (by decide), r9W]
  have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 8) (.reg 9))) (.const 5)))) st8 .normal
      { st8 with regs := Function.update st8.regs 12 (S2.splay.nodes wNode).val } _ :=
    runs_assign_iff.mpr ⟨(S2.splay.nodes wNode).val, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq hr5_8)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr9_8) (by omega)) (by omega))
      (Expr.eval_const (by omega)) (by omega))
      (by have h := (harena2.nodes_at wNode hwNode_c2).2.2.2.2.2.1; rw [hnb2] at h; simpa [ordNodeAddr] using h), rfl, rfl, rfl⟩
  set st9 : State := { st8 with regs := Function.update st8.regs 12 (S2.splay.nodes wNode).val }
  have hs_out : Runs w p ω (.store (.reg 3) (.reg 12)) st9 .normal
      { st9 with mem := Function.update stS2.mem heap (S2.splay.nodes wNode).val } _ :=
    runs_store_iff.mpr ⟨heap, (S2.splay.nodes wNode).val,
      Expr.eval_reg_of_eq (by simp only [st9, st8, Function.update_of_ne (by decide : (3 : ℕ) ≠ 12), Function.update_of_ne (by decide : (3 : ℕ) ≠ 11)]; rw [hregW 3 (by decide) (by decide)]; simp [st7, r3_6]),
      Expr.eval_reg_of_eq (by simp [st9]), rfl, rfl, rfl⟩
  set st10 : State := { st9 with mem := Function.update stS2.mem heap (S2.splay.nodes wNode).val }
  have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.const 1))) st10 (.returned (heap + 1)) st10 _ :=
    runs_ret_iff.mpr ⟨heap + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp only [st10, st9, st8, Function.update_of_ne (by decide : (3 : ℕ) ≠ 12), Function.update_of_ne (by decide : (3 : ℕ) ≠ 11)]; rw [hregW 3 (by decide) (by decide)]; simp [st7, r3_6]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  -- Prove (S2.splay.nodes wNode).val = endKey ((ord v).getD ((idxOf + 1) % length) _)
  have hw_val_eq : (S2.splay.nodes wNode).val =
      endKey ((ord v).getD (((ord v).idxOf (endOfKey key) + 1) % (ord v).length) (0, true)) := by
    have hval12 : ∀ x ∈ (S1.trees v).toList, (S2.splay.nodes x).val = (S1.splay.nodes x).val := fun x hx => by
      have h1 := hinv2.list_eq v (by rw [hv2, hv1]; exact hv)
      have h2 := hinv1.list_eq v (by rw [hv1]; exact hv)
      rw [hlist2] at h1; rw [← h1] at h2
      rcases List.getElem_of_mem hx with ⟨i, hi, hgi⟩
      have hm := congrArg (fun l => l[i]?) h2
      simp [hi, hgi] at hm; exact (endOfKey_injective hm).symm
    have hu_val1 : (S1.splay.nodes u).val = key := by
      have h1 := hinv1.list_eq v (by rw [hv1]; exact hv)
      have h2 := hinv.list_eq v hv
      rw [hlist1] at h1; rw [← h1] at h2
      rcases List.getElem_of_mem hu_spec.1 with ⟨i, hi, hgi⟩
      have hm := congrArg (fun l => l[i]?) h2
      simp [hi, hgi, hu_spec.2] at hm; exact endOfKey_injective hm.symm
    have hord_split : ord v = L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) ++
        endOfKey key :: R.toList.map (fun x => endOfKey (S1.splay.nodes x).val) := by
      have := hinv1.list_eq v (by rw [hv1]; exact hv)
      rw [htv1] at this; rw [← this]; simp [AuxTree.toList, hu_val1]
    have hnd_ord : (ord v).Nodup := hinv.ord_unique.nodup v
    rw [hord_split] at hnd_ord
    have hx_nL : endOfKey key ∉ L.toList.map (fun x => endOfKey (S1.splay.nodes x).val) :=
      fun h => (List.nodup_append.mp hnd_ord).2.2 _ h _ List.mem_cons_self rfl
    have hidx : (ord v).idxOf (endOfKey key) = L.countNodes := by
      rw [hord_split, idxOf_append_cons_of_not_mem hx_nL, List.length_map, AuxTree.length_toList]
    have hlen_ord : (ord v).length = L.countNodes + 1 + R.countNodes := by
      rw [hord_split]; simp [AuxTree.length_toList]; omega
    rw [hval12 wNode hwNode_mem_v, hidx, hlen_ord]
    by_cases hR : R = .leaf
    · subst hR; simp only [AuxTree.countNodes, Nat.add_zero, Nat.mod_self]
      have hgd : (ord v).getD 0 (0, true) = endOfKey (S1.splay.nodes wNode).val := by
        have h1 := hinv1.list_eq v (by rw [hv1]; exact hv)
        rw [← h1, htv1]
        have hpos : 0 < (AuxTree.node u L .leaf).toList.length := by rw [AuxTree.length_toList]; simp [AuxTree.countNodes]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hpos, Option.map_some, Option.getD_some]
        have hlm := leftmostId_getElem_zero (t := .node u L .leaf) (by simp)
        rw [List.getD_eq_getElem _ _ hpos] at hlm
        simp only [hwNode_def, htWalk_def, ↓reduceIte]; rw [hlm]
      rw [hgd, endKey_endOfKey]
    · have hR_pos : 0 < R.countNodes := by
        cases hR' : R with
        | leaf => exact absurd hR' hR
        | node _ _ _ => simp [AuxTree.countNodes]
      rw [Nat.mod_eq_of_lt (by omega : L.countNodes + 1 < L.countNodes + 1 + R.countNodes)]
      have hgd : (ord v).getD (L.countNodes + 1) (0, true) = endOfKey (S1.splay.nodes wNode).val := by
        rw [hord_split, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [List.length_map, AuxTree.length_toList]; omega),
          List.length_map, AuxTree.length_toList, show L.countNodes + 1 - L.countNodes = 1 by omega,
          List.getElem?_cons_succ, List.getElem?_map]
        have hpos : 0 < R.toList.length := by rw [AuxTree.length_toList]; exact hR_pos
        rw [List.getElem?_eq_getElem hpos, Option.map_some, Option.getD_some]
        have hlm := leftmostId_getElem_zero (t := R) hR
        rw [List.getD_eq_getElem _ _ hpos] at hlm
        simp only [hwNode_def, htWalk_def, hR, ite_false]; rw [hlm]
      rw [hgd, endKey_endOfKey]
  have hfull := ord_runs_seq_normal ha4 (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6
    (ord_runs_seq_normal hcall1 (ord_runs_seq_normal ha8 (ord_runs_seq_normal hrun6
      (ord_runs_seq_normal ha10 (ord_runs_seq_normal hrunW (ord_runs_seq_normal hcall2
        (ord_runs_seq_normal ha12 (ord_runs_seq_normal hs_out hret))))))))))
  refine ⟨.returned (heap + 1), st10, _, hfull, rfl, S2, hinv2,
    harena2.congr hinv2.next_le (fun a ha => by
      dsimp only [st10]
      have hne : a ≠ heap := by rw [hv2, he2, hv1, he1] at ha; unfold ordFoot at ha; omega
      exact Function.update_of_ne hne _ _),
    hv2.trans hv1, he2.trans he1, by dsimp only [st10]; rw [Function.update_self, hw_val_eq],
    fun a ha => by dsimp only [st10]; rw [Function.update_of_ne (by omega)]; exact hfr2.1 a (by omega),
    fun a ha hnf => by
      dsimp only [st10]
      rw [Function.update_of_ne (by omega), hfr2.2 a ha (by rw [hv1, he1]; exact hnf), hmemW_eq]
      exact hfr1.2 a ha hnf, ?_⟩
  have hphi_s1 : cS1 + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
      ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 3800 * ordStoreLog S.eCap := by
    unfold ordPhi; rw [hcnt1]
    have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi1
    have h2 : ORD_PHI_WEIGHT * (sumTreePhi S1 + (S.trees v).depthOf u / 2) =
        ORD_PHI_WEIGHT * sumTreePhi S1 + ORD_PHI_WEIGHT * ((S.trees v).depthOf u / 2) := by ring
    have h3 : ORD_PHI_WEIGHT * (sumTreePhi S + 3 * ordStoreLog S.eCap) =
        ORD_PHI_WEIGHT * sumTreePhi S + 3000 * ordStoreLog S.eCap := by unfold ORD_PHI_WEIGHT; ring
    unfold ORD_PHI_WEIGHT at h1 h2 ⊢; unfold ORD_SPLAY_RATE at hcS1
    have h650 : ((S.trees v).depthOf u / 2 + 1) * 650 ≤ 1000 * ((S.trees v).depthOf u / 2) + 650 := by omega
    have h800 : 800 ≤ 800 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 800 hlog
    omega
  have hphi_s2 : cW + cS2 + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S2 ≤
      ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 + 3900 * ordStoreLog S.eCap := by
    unfold ordPhi; rw [hcnt2]; rw [he1] at hphi2
    have h1 := Nat.mul_le_mul_left ORD_PHI_WEIGHT hphi2
    have h2 : ORD_PHI_WEIGHT * (sumTreePhi S2 + (S1.trees v).depthOf wNode / 2) =
        ORD_PHI_WEIGHT * sumTreePhi S2 + ORD_PHI_WEIGHT * ((S1.trees v).depthOf wNode / 2) := by ring
    have h3 : ORD_PHI_WEIGHT * (sumTreePhi S1 + 3 * ordStoreLog S.eCap) =
        ORD_PHI_WEIGHT * sumTreePhi S1 + 3000 * ordStoreLog S.eCap := by unfold ORD_PHI_WEIGHT; ring
    unfold ORD_PHI_WEIGHT at h1 h2 ⊢; unfold ORD_SPLAY_RATE at hcS2
    have h700 : 25 * leftSpineLen tWalk + ((S1.trees v).depthOf wNode / 2 + 1) * 650 ≤
        1000 * ((S1.trees v).depthOf wNode / 2) + 700 := by omega
    have h900 : 900 ≤ 900 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 900 hlog
    omega
  have h800 : 800 ≤ 800 * ordStoreLog S.eCap := Nat.le_mul_of_pos_right 800 hlog
  unfold ORD_NEXT_MUL
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
  omega

end MinCostFlow.SparseCore.Program
