module

public import MinCostFlow.SparseCore.Program.OrdStoreAlloc
public import MinCostFlow.SparseCore.Program.OrdStoreFreeTree
import Mathlib.Tactic

/-!
# Order Store `insertBefore` Helpers: Back Insertion

This file proves helper lemmas on `insertBeforeList` / `OrdUniqueWithin` and verifies
`insertBack_runs`, which allocates a fresh node via `ordAlloc` and appends it to the back of
`vRoot[v]` via `ordJoin`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

theorem insertBefore_pre_facts {vCap eCap v keyX : ℕ} {y : Option End} {ord : ℕ → List End}
    (h2 : OrdUniqueWithin vCap eCap (applyOrdEdit ord (.insertBefore v (endOfKey keyX) y))) :
    v < vCap ∧ keyX < 2 * eCap ∧ ∀ w, endOfKey keyX ∉ ord w := by
  have hx_mem : endOfKey keyX ∈ applyOrdEdit ord (.insertBefore v (endOfKey keyX) y) v := by
    simp only [applyOrdEdit, Function.update_self, insertBeforeList]
    cases y <;> simp
  have hv : v < vCap := h2.v_lt_of_mem hx_mem
  have hk : keyX < 2 * eCap := by
    have := h2.edge_lt hx_mem; simp [endOfKey] at this; omega
  refine ⟨hv, hk, fun w hw => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    have hnd := h2.nodup w
    simp only [applyOrdEdit, Function.update_self, insertBeforeList] at hnd
    cases y with
    | none =>
      rw [List.nodup_append] at hnd; exact hnd.2.2 _ hw _ (List.mem_singleton.mpr rfl) rfl
    | some y0 =>
      have hsp := List.take_append_drop ((ord w).idxOf y0) (ord w)
      rw [← hsp, List.mem_append] at hw
      rw [List.nodup_append, List.nodup_cons] at hnd
      rcases hw with hL | hR
      · exact hnd.2.2 _ hL _ List.mem_cons_self rfl
      · exact hnd.2.1.1 hR
  · have hmw : endOfKey keyX ∈ applyOrdEdit ord (.insertBefore v (endOfKey keyX) y) w := by
      simp only [applyOrdEdit, Function.update_of_ne hwv]; exact hw
    exact hwv (h2.unique_v hmw hx_mem)

theorem insertBeforeList_not_mem {x : End} {y : Option End} {xs : List End}
    (h : ∀ y0, y = some y0 → y0 ∉ xs) :
    insertBeforeList x y xs = xs ++ [x] := by
  cases y with
  | none => rfl
  | some y0 =>
    have hnm := h y0 rfl
    have hidx : xs.idxOf y0 = xs.length := by
      clear h
      induction xs with
      | nil => rfl
      | cons a tl ih =>
        have hne : a ≠ y0 := fun heq => hnm (heq ▸ List.mem_cons_self)
        have htl : y0 ∉ tl := fun hm => hnm (List.mem_cons_of_mem a hm)
        simp [List.idxOf_cons, beq_eq_false_iff_ne.mpr hne, ih htl]
    simp [insertBeforeList, hidx]

theorem idxOf_append_cons_of_not_mem {α : Type*} [BEq α] [LawfulBEq α]
    {a : α} {l1 l2 : List α} (h : a ∉ l1) :
    (l1 ++ a :: l2).idxOf a = l1.length := by
  induction l1 with
  | nil => simp
  | cons b tl ih =>
    have hne : b ≠ a := fun heq => h (heq ▸ List.mem_cons_self)
    have htl : a ∉ tl := fun hm => h (List.mem_cons_of_mem b hm)
    simp [List.idxOf_cons, beq_eq_false_iff_ne.mpr hne, ih htl]

/-- Appends a fresh node `keyX` to the back of `ord v` via `allocProc` + `joinProc`. -/
theorem insertBack_runs
    {w b v keyX rotProc stepProc splayProc walkProc joinProc allocProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc))
    (hwalk : p.procs[walkProc]? = some (ordWalkExtremeBody splayProc))
    (hjoin : p.procs[joinProc]? = some (ordJoinBody walkProc))
    (halloc : p.procs[allocProc]? = some ordAllocBody) (ω : ℕ → Bool)
    {stM : State} {ord : ℕ → List End} {S : OrdStoreState} {heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S stM.mem)
    (hv : v < S.vCap) (hkX : keyX < 2 * S.eCap) (hunused : S.eNode keyX = 0)
    (huniq' : OrdUniqueWithin S.vCap S.eCap (Function.update ord v (ord v ++ [endOfKey keyX])))
    (hr0 : stM.regs 0 = b) (hr1 : stM.regs 1 = v) (hr2 : stM.regs 2 = keyX)
    (hr5 : stM.regs 5 = ordNodesBase b S.vCap S.eCap)
    (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom stM.mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ st' c, Runs w p ω
        (.call 4 allocProc [.reg 0, .reg 2] ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const 2))) ;;
         .assign 9 (.load (.bin .add (.reg 8) (.reg 1))) ;;
         .call 10 joinProc [.reg 5, .reg 9, .reg 4, .bin .add (.reg 1) (.const 1)] ;;
         .store (.bin .add (.reg 8) (.reg 1)) (.reg 10)) stM .normal st' c ∧
      (∃ S' : OrdStoreState,
        OrdInv (Function.update ord v (ord v ++ [endOfKey keyX])) S' ∧
        OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap stM.mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + 7000 * ordStoreLog S.eCap) := by
  have hlog : 1 ≤ ordStoreLog S.eCap := ordStoreLog_pos S.eCap
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  obtain ⟨oA, stA, cA, hrunA, ⟨nx, S1, hoA, hnx1, hnx_nn, hnn_ge, hnn_le, hv1, he1, hvr1, htr1,
    hen1, hsp1, hnx_nlive, hnx_nfl, hflnd1, hfc1, hfl_le1, hlive_fl1, hpart1, harena1, hfr1⟩, hcA⟩ :=
    ordAllocBody_runs ω hinv harena hkX hunused hfoot hz hw hwide (pos := stM.pos)
  have hcallA : Runs w p ω (.call 4 allocProc [.reg 0, .reg 2]) stM .normal
      { stA with regs := Function.update stM.regs 4 nx } (argsSize [.reg 0, .reg 2] + cA + 1) :=
    runs_call_iff.mpr ⟨[b, keyX], ordAllocBody, oA, stA, cA,
      evalArgs_cons (Expr.eval_reg_of_eq hr0) (evalArgs_cons (Expr.eval_reg_of_eq hr2) (evalArgs_nil _ _)),
      halloc, hrunA, rfl, by simp [hoA], rfl⟩
  set st1 : State := { stA with regs := Function.update stM.regs 4 nx }
  have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 2)))) st1 .normal
      { st1 with regs := Function.update st1.regs 8 (ordVRootBase b) } _ :=
    runs_assign_iff.mpr ⟨ordVRootBase b, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1, hr0])) (Expr.eval_const (by omega)) (by omega))
      harena1.hdr_vRoot, rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 8 (ordVRootBase b) }
  have hmA_rv : stA.mem (ordVRootBase b + v) = (S.trees v).rootId := by
    rw [← hinv.vRoot_eq v hv, ← hvr1]; exact harena1.vRoot_at v (by rw [hv1]; exact hv)
  have ha9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 8) (.reg 1)))) st2 .normal
      { st2 with regs := Function.update st2.regs 9 (S.trees v).rootId } _ :=
    runs_assign_iff.mpr ⟨(S.trees v).rootId, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st2])) (Expr.eval_reg_of_eq (by simp [st2, st1, hr1]))
      (by unfold ordVRootBase; omega)) hmA_rv, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 9 (S.trees v).rootId }
  have hnb_w : nb + 8 * (S1.nextNode + 1) < 2 ^ w := by
    have := ordNodesBase_end b S.vCap S.eCap; omega
  have h0_sp1 : S1.splay.nodes 0 = ordNullNode := by
    rw [hsp1, SplayState.nodes_updateNode_ne _ (by omega)]; exact hinv.null_node
  have hcl_sp1 : ∀ u, (S1.splay.nodes u).rev = false := fun u => by
    rw [hsp1]; by_cases h : u = nx
    · rw [h]; simp [SplayState.nodes_updateNode, ordFreshNode]
    · rw [SplayState.nodes_updateNode_ne _ h]; exact hinv.clean u
  have hcnt_le_nn : (S.trees v).countNodes + 1 ≤ S1.nextNode := by
    have hsub : ((S.trees v).toList.toFinset ∪ {nx}) ⊆ Finset.Icc 1 S1.nextNode := by
      intro z hz
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_singleton, Finset.mem_Icc] at hz ⊢
      rcases hz with hzt | rfl
      · have := hinv.live_le_nextNode hv hzt; omega
      · exact ⟨hnx1, hnx_nn⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (by simp [hnx_nlive v hv]),
      List.toFinset_card_of_nodup (hinv.tree_inv v hv).nodup,
      AuxTree.length_toList, Finset.card_singleton, Nat.card_Icc] at hcard
    omega
  have hok_tv : OrdTreeOk S1.nextNode S1.splay (S.trees v) :=
    { null_node := h0_sp1
      clean := hcl_sp1
      inv := ⟨(hinv.tree_inv v hv).nodup, SplayState.SubtreeInv_agree (hinv.tree_inv v hv).sub fun u hu => by
        rw [hsp1, SplayState.nodes_updateNode_ne _ (fun h => hnx_nlive v hv (by rw [← h]; exact hu))]⟩
      mem_le := fun u hu => by have := (hinv.live_le_nextNode hv hu).2; omega
      count_le := by omega }
  have hok_nx : OrdTreeOk S1.nextNode S1.splay (.node nx .leaf .leaf) :=
    { null_node := h0_sp1
      clean := hcl_sp1
      inv := ⟨by simp [AuxTree.toList],
        ⟨by omega, by simp [hsp1, SplayState.nodes_updateNode, ordFreshNode, AuxTree.rootId],
          by simp [hsp1, SplayState.nodes_updateNode, ordFreshNode, AuxTree.rootId],
          by simp [hsp1, SplayState.nodes_updateNode, ordFreshNode],
          fun h => absurd rfl h,
          by simp [hsp1, SplayState.nodes_updateNode, ordFreshNode, AuxTree.countNodes],
          rfl, trivial, trivial⟩⟩
      mem_le := fun u hu => by
        simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hu
        rw [hu]; exact hnx_nn
      count_le := by simp [AuxTree.countNodes]; omega }
  have hn1 : OrdNodesAt stA.mem nb S1.nextNode S1.splay S1.nextFree := fun x hx => by
    have h := harena1.nodes_at x hx; rw [hv1, he1, ← hnb] at h; exact h
  have hdisj_nx : ∀ u ∈ (S.trees v).toList, u ∉ (AuxTree.node nx .leaf .leaf).toList := by
    intro u hu hnx'
    simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hnx'
    exact hnx_nlive v hv (hnx' ▸ hu)
  obtain ⟨oJ, stJ, cJ, hrunJ, spJ, tJ, hoJ, hnJ, hfrJ, hokJ, hlistJ, hcntJ, hppJ, hvalJ, houtJ, hphiJ⟩ :=
    ordJoinBody_runs hrot hstep hsplay hwalk ω hn1 hok_tv hok_nx rfl rfl hdisj_nx
      (by simp [AuxTree.countNodes]; omega) hnn_le (owner := v + 1) (by omega) hnb_w hwide (pos := st3.pos)
  have hcallJ : Runs w p ω (.call 10 joinProc [.reg 5, .reg 9, .reg 4, .bin .add (.reg 1) (.const 1)]) st3 .normal
      { stJ with regs := Function.update st3.regs 10 tJ.rootId }
      (argsSize [.reg 5, .reg 9, .reg 4, .bin .add (.reg 1) (.const 1)] + cJ + 1) :=
    runs_call_iff.mpr ⟨[nb, (S.trees v).rootId, nx, v + 1], ordJoinBody walkProc, oJ, stJ, cJ,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3, st2, st1, hr5]))
        (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3]))
          (evalArgs_cons (Expr.eval_reg_of_eq (by simp [st3, st2, st1]))
            (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st3, st2, st1, hr1]))
              (Expr.eval_const (by omega)) (by omega)) (evalArgs_nil _ _)))),
      hjoin, hrunJ, rfl, by simp [hoJ], rfl⟩
  set st4 : State := { stJ with regs := Function.update st3.regs 10 tJ.rootId }
  have hst_vr : Runs w p ω (.store (.bin .add (.reg 8) (.reg 1)) (.reg 10)) st4 .normal
      { st4 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId } _ :=
    runs_store_iff.mpr ⟨ordVRootBase b + v, tJ.rootId,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2]))
        (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, hr1])) (by unfold ordVRootBase; omega),
      Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
  set st5 : State := { st4 with mem := Function.update stJ.mem (ordVRootBase b + v) tJ.rootId }
  let S' : OrdStoreState :=
    { S1 with
      splay := spJ
      vRoot := Function.update S.vRoot v tJ.rootId
      trees := Function.update S.trees v tJ }
  have hspJ_out : ∀ u, u ∉ (S.trees v).toList → u ≠ nx → spJ.nodes u = S.splay.nodes u := fun u hu hne => by
    rw [houtJ u hu (by simp [AuxTree.toList, hne]), hsp1, SplayState.nodes_updateNode_ne _ hne]
  have hlist_v' : tJ.toList.map (fun u => endOfKey (spJ.nodes u).val) = ord v ++ [endOfKey keyX] := by
    have h1 : tJ.toList.map (fun u => endOfKey (spJ.nodes u).val) =
        tJ.toList.map (fun u => endOfKey (S1.splay.nodes u).val) :=
      List.map_congr_left fun u hu => by rw [hvalJ u hu]
    rw [h1, hlistJ]; simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.map_append, List.map_singleton]
    have h2 : (S.trees v).toList.map (fun u => endOfKey (S1.splay.nodes u).val) = ord v := by
      rw [← hinv.list_eq v hv]
      exact List.map_congr_left fun u hu => by
        rw [hsp1, SplayState.nodes_updateNode_ne _ (fun h => hnx_nlive v hv (by rw [← h]; exact hu))]
    rw [h2, hsp1, SplayState.nodes_updateNode]; simp [ordFreshNode]
  have hinv' : OrdInv (Function.update ord v (ord v ++ [endOfKey keyX])) S' :=
    { ord_unique := by dsimp only [S']; rw [hv1, he1]; exact huniq'
      next_le := by dsimp only [S']; rw [he1]; exact hnn_le
      clean := hokJ.clean
      null_node := hokJ.null_node
      tree_inv := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [hv1] at hu
        by_cases h : u = v
        · subst h; simpa using hokJ.inv
        · simp only [Function.update_of_ne h]
          exact ⟨(hinv.tree_inv u hu).nodup, SplayState.SubtreeInv_agree (hinv.tree_inv u hu).sub fun x hx =>
            (hspJ_out x (hinv.disj_trees u v h x hx) (fun heq => hnx_nlive u hu (heq ▸ hx))).symm⟩
      tree_out := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [hv1] at hu
        rw [Function.update_of_ne (by omega)]; exact hinv.tree_out u hu
      vRoot_eq := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [hv1] at hu
        by_cases h : u = v <;> simp [h, hinv.vRoot_eq u hu]
      root_ppar := fun u hu hne => by
        dsimp only [S'] at hu hne ⊢; rw [hv1] at hu
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hne ⊢; exact hppJ hne
        · simp only [Function.update_of_ne h] at hne ⊢
          rw [hspJ_out _ (hinv.disj_trees u v h _ (AuxTree.rootId_mem hne))
            (fun heq => hnx_nlive u hu (heq ▸ AuxTree.rootId_mem hne))]
          exact hinv.root_ppar u hu hne
      list_eq := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [hv1] at hu
        by_cases h : u = v
        · subst h; simpa using hlist_v'
        · simp only [Function.update_of_ne h]
          rw [← hinv.list_eq u hu]
          exact List.map_congr_left fun x hx => by
            rw [hspJ_out x (hinv.disj_trees u v h x hx) (fun heq => hnx_nlive u hu (heq ▸ hx))]
      disj_trees := fun u1 u2 hne x h1 h2 => by
        dsimp only [S'] at h1 h2
        by_cases h1v : u1 = v
        · subst h1v; simp only [Function.update_self] at h1; simp only [Function.update_of_ne (Ne.symm hne)] at h2
          rw [hlistJ, List.mem_append] at h1
          simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at h1
          rcases h1 with htv | rfl
          · exact hinv.disj_trees u1 u2 hne x htv h2
          · by_cases hu2 : u2 < S.vCap
            · exact hnx_nlive u2 hu2 h2
            · rw [hinv.tree_out u2 (by omega)] at h2; exact List.not_mem_nil h2
        · by_cases h2v : u2 = v
          · subst h2v; simp only [Function.update_of_ne h1v] at h1; simp only [Function.update_self] at h2
            rw [hlistJ, List.mem_append] at h2
            simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at h2
            rcases h2 with htv | rfl
            · exact hinv.disj_trees u1 u2 h1v x h1 htv
            · by_cases hu1 : u1 < S.vCap
              · exact hnx_nlive u1 hu1 h1
              · rw [hinv.tree_out u1 (by omega)] at h1; exact List.not_mem_nil h1
          · simp only [Function.update_of_ne h1v] at h1; simp only [Function.update_of_ne h2v] at h2
            exact hinv.disj_trees u1 u2 hne x h1 h2
      free_nodup := hflnd1
      free_disj := fun u hu x hxf hxt => by
        dsimp only [S'] at hu hxt; rw [hv1] at hu
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hxt
          rw [hlistJ, List.mem_append] at hxt
          simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hxt
          rcases hxt with htv | rfl
          · exact hlive_fl1 u hv x htv hxf
          · exact hnx_nfl hxf
        · simp only [Function.update_of_ne h] at hxt; exact hlive_fl1 u hu x hxt hxf
      free_chain := hfc1
      nodes_range := fun x => by
        dsimp only [S']; rw [hv1]
        constructor
        · rintro (hfl | ⟨u, hu, hxu⟩)
          · exact hfl_le1 x hfl
          · by_cases h : u = v
            · subst h; simp only [Function.update_self] at hxu
              rw [hlistJ, List.mem_append] at hxu
              simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hxu
              rcases hxu with htv | rfl
              · have := hinv.live_le_nextNode hv htv; omega
              · exact ⟨hnx1, hnx_nn⟩
            · simp only [Function.update_of_ne h] at hxu
              have := hinv.live_le_nextNode hu hxu; omega
        · rintro ⟨hx1, hxnn⟩
          rcases hpart1 x hx1 hxnn with rfl | ⟨u, hu, hxu⟩ | hfl
          · exact Or.inr ⟨v, hv, by simp [hlistJ, AuxTree.toList]⟩
          · by_cases h : u = v
            · subst h; exact Or.inr ⟨u, hv, by simp [hlistJ, hxu]⟩
            · exact Or.inr ⟨u, hu, by simpa [h] using hxu⟩
          · exact Or.inl hfl
      key_lt := fun u hu x hxu => by
        dsimp only [S'] at hu hxu ⊢; rw [hv1] at hu; rw [he1]
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hxu
          rw [hvalJ x hxu, hsp1]
          rw [hlistJ, List.mem_append] at hxu
          simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hxu
          rcases hxu with htv | rfl
          · rw [SplayState.nodes_updateNode_ne _ (fun heq => hnx_nlive u hv (by rw [← heq]; exact htv))]
            exact hinv.key_lt u hv x htv
          · simp [SplayState.nodes_updateNode, ordFreshNode, hkX]
        · simp only [Function.update_of_ne h] at hxu
          rw [hspJ_out x (hinv.disj_trees u v h x hxu) (fun heq => hnx_nlive u hu (by rw [← heq]; exact hxu))]
          exact hinv.key_lt u hu x hxu
      eNode_spec := fun j hj => by
        dsimp only [S'] at hj ⊢; rw [he1] at hj; rw [hv1, hen1]
        by_cases hjk : j = keyX
        · subst hjk; right; refine ⟨v, hv, ?_, ?_⟩
          · simp [hlistJ, AuxTree.toList]
          · simp only [Function.update_self]
            rw [hvalJ nx (by simp [hlistJ, AuxTree.toList]), hsp1, SplayState.nodes_updateNode]
            simp [ordFreshNode]
        · simp only [Function.update_of_ne hjk]
          rcases hinv.eNode_spec j hj with ⟨h0, hnone'⟩ | ⟨u, hu, hmem', hval'⟩
          · left; refine ⟨h0, fun u hu x hxu heq => ?_⟩
            by_cases h : u = v
            · subst h; simp only [Function.update_self] at hxu
              rw [hvalJ x hxu, hsp1] at heq
              rw [hlistJ, List.mem_append] at hxu
              simp only [AuxTree.toList, List.nil_append, List.singleton_append, List.mem_singleton] at hxu
              rcases hxu with htv | rfl
              · rw [SplayState.nodes_updateNode_ne _ (fun he => hnx_nlive u hv (by rw [← he]; exact htv))] at heq
                exact hnone' u hv x htv heq
              · simp [SplayState.nodes_updateNode, ordFreshNode] at heq; exact hjk heq.symm
            · simp only [Function.update_of_ne h] at hxu
              rw [hspJ_out x (hinv.disj_trees u v h x hxu) (fun he => hnx_nlive u hu (by rw [← he]; exact hxu))] at heq
              exact hnone' u hu x hxu heq
          · right; refine ⟨u, hu, ?_, ?_⟩
            · by_cases h : u = v
              · subst h; simp [hlistJ, hmem']
              · simpa [h] using hmem'
            · by_cases h : u = v
              · subst h
                rw [hvalJ _ (by simp [hlistJ, hmem']), hsp1,
                  SplayState.nodes_updateNode_ne _ (fun he => hnx_nlive u hv (by rw [← he]; exact hmem'))]
                exact hval'
              · rw [hspJ_out _ (hinv.disj_trees u v h _ hmem') (fun he => hnx_nlive u hu (by rw [← he]; exact hmem'))]
                exact hval' }
  have hnot_nd : ∀ a < nb, ¬ InOrdNodes nb S1.nextNode a := fun a ha h => by
    unfold InOrdNodes at h; omega
  have hnot_vr : ¬ InOrdNodes nb S1.nextNode (ordVRootBase b + v) :=
    hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega)
  have hfr2 : OrdFrame b S.vCap S.eCap heap stA.mem st5.mem := by
    have h1 : ∀ a, ¬ ordFoot b S.vCap S.eCap a → st5.mem a = stA.mem a := fun a ha => by
      have hnot1 : ¬ InOrdNodes nb S1.nextNode a := fun h =>
        ha ⟨by unfold InOrdNodes at h; rw [hnb] at h; unfold ordNodesBase at h; omega,
            by unfold InOrdNodes at h; have := ordNodesBase_end b S.vCap S.eCap; rw [hnb] at h; omega⟩
      dsimp only [st5]
      rw [Function.update_of_ne (fun h => ha (by rw [h]; exact ordFoot_vRoot hv)), hfrJ a hnot1]
    exact ⟨fun a ha => (h1 a (fun hf => by unfold ordFoot at hf; omega)).trans (hfr1.1 a ha),
           fun a _ hnf => h1 a hnf⟩
  have harena' : OrdArenaAt b S' st5.mem := by
    have hhdr : ∀ j < 7, st5.mem (b + j) = stA.mem (b + j) := fun j hj => by
      dsimp only [st5]
      rw [Function.update_of_ne (by unfold ordVRootBase; omega),
          hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordNodesBase; omega))]
    exact
      { hdr_vCap := (hhdr 0 (by omega)).trans harena1.hdr_vCap
        hdr_eCap := (hhdr 1 (by omega)).trans harena1.hdr_eCap
        hdr_vRoot := (hhdr 2 (by omega)).trans harena1.hdr_vRoot
        hdr_eNode := (hhdr 3 (by omega)).trans harena1.hdr_eNode
        hdr_nodes := (hhdr 4 (by omega)).trans harena1.hdr_nodes
        hdr_next := (hhdr 5 (by omega)).trans harena1.hdr_next
        hdr_free := (hhdr 6 (by omega)).trans harena1.hdr_free
        vRoot_at := fun u hu => by
          dsimp only [S', st5] at hu ⊢; rw [hv1] at hu
          by_cases h : u = v
          · subst h; simp
          · rw [Function.update_of_ne (by omega), Function.update_of_ne h,
                hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordVRootBase ordNodesBase; omega))]
            rw [← hvr1]; exact harena1.vRoot_at u (by rw [hv1]; exact hu)
        eNode_at := fun j hj => by
          dsimp only [S', st5] at hj ⊢; rw [he1] at hj; rw [hv1]
          rw [Function.update_of_ne (by unfold ordVRootBase ordENodeBase; omega),
              hfrJ _ (hnot_nd _ (by rw [hnb]; unfold ordENodeBase ordNodesBase; omega))]
          have h := harena1.eNode_at j (by rw [he1]; exact hj)
          rwa [hv1] at h
        nodes_at := by
          dsimp only [S', st5]; rw [hv1, he1]
          exact hnJ.congr fun a ha => Function.update_of_ne (fun (h : a = ordVRootBase b + v) => hnot_vr (h ▸ ha)) _ _ }
  have hphi_upd : sumTreePhi S' + (S.trees v).treePhi (fun _ => 0) =
      sumTreePhi S + tJ.treePhi (fun _ => 0) := by
    have h := sumTreePhi_update (S := S) (S' := S') hv hv1 (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tJ from Function.update_self v tJ S.trees] at h; exact h
  have hcnt_upd : sumCountNodes S' = sumCountNodes S + 1 := by
    have h1 := sumCountNodes_update (S := S) (S' := S') hv hv1 (fun u _ huv => Function.update_of_ne huv _ _)
    rw [show S'.trees v = tJ from Function.update_self v tJ S.trees] at h1
    have h3 : tJ.countNodes = (S.trees v).countNodes + 1 := by rw [hcntJ]; simp [AuxTree.countNodes]
    omega
  refine ⟨st5, _,
    ord_runs_seq_normal hcallA (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9
      (ord_runs_seq_normal hcallJ hst_vr))),
    S', hinv', harena', hfr1.trans hfr2, hv1, he1, ?_⟩
  unfold ordPhi
  have hphi_nx : (AuxTree.node nx .leaf .leaf).treePhi (fun _ => 0) = 0 := by
    simp [AuxTree.treePhi, AuxTree.rank, treeSize_zero_eq_countNodes, AuxTree.countNodes]
  rw [hphi_nx, Nat.add_zero] at hphiJ
  have hmul_phi : ORD_PHI_WEIGHT * sumTreePhi S' + ORD_PHI_WEIGHT * (S.trees v).treePhi (fun _ => 0) =
      ORD_PHI_WEIGHT * sumTreePhi S + ORD_PHI_WEIGHT * tJ.treePhi (fun _ => 0) := by
    have := congrArg (ORD_PHI_WEIGHT * ·) hphi_upd; ring_nf at this ⊢; exact this
  have hmul_cnt : ORD_DEL_WEIGHT * sumCountNodes S' =
      ORD_DEL_WEIGHT * sumCountNodes S + ORD_DEL_WEIGHT := by
    rw [hcnt_upd]; ring
  unfold ORD_ALLOC_COST at hcA
  unfold ORD_JOIN_AMORT at hphiJ
  unfold ORD_PHI_WEIGHT at hphiJ hmul_phi ⊢
  unfold ORD_DEL_WEIGHT at hmul_cnt ⊢
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
    argsSize_cons, argsSize_nil] at *
  omega

end MinCostFlow.SparseCore.Program
