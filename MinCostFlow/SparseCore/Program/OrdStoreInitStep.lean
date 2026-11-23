module

public import MinCostFlow.SparseCore.Program.OrdStoreInitInner
import Mathlib.Tactic

/-!
# Order Store Initialization: Per-Record `OrdInv` Preservation

This file provides `ordInitRecord_inv`, which builds `OrdInv (Function.update curOrd v xs) S1`
after `ordInitInnerLoop` constructs a left-leaning spine for vertex `v` in fresh sequential slots
`S.nextNode + 1 .. S.nextNode + len`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

theorem ordInitRecord_inv
    {vCap eCap v len ptr : ℕ} {mem : ℕ → ℕ} {ordAll curOrd : ℕ → List End} {S : OrdStoreState}
    {spI : SplayState ℕ Unit Unit} {eNI : ℕ → ℕ}
    (hinv : OrdInv curOrd S) (hvS : S.vCap = vCap) (heS : S.eCap = eCap) (hflS : S.freeList = [])
    (huniq : OrdUniqueWithin vCap eCap ordAll)
    (hv_lt : v < vCap) (hlen_pos : 0 < len) (hnn_le : S.nextNode + len ≤ 2 * eCap)
    (hcur_v : curOrd v = [])
    (hxs_def : ∀ j < len, mem (ptr + 2 + j) < 2 * eCap)
    (hcomb : ∀ u, curOrd u ≠ [] → curOrd u = ordAll u)
    (hord_v : ordAll v = (readList mem (ptr + 2) len).map endOfKey)
    (hokI : OrdTreeOk (S.nextNode + len) spI (leftSpine ((List.range len).map (fun j => S.nextNode + 1 + j))))
    (houtI : ∀ u ≤ S.nextNode, spI.nodes u = S.splay.nodes u)
    (hvalI : ∀ j < len, (spI.nodes (S.nextNode + 1 + j)).val = mem (ptr + 2 + j))
    (henfI : ∀ k < 2 * eCap,
      eNI k = match (List.range len).find? (fun j => mem (ptr + 2 + j) == k) with
              | some j => S.nextNode + 1 + j
              | none => S.eNode k) :
    let ids := (List.range len).map (fun j => S.nextNode + 1 + j)
    let tNew := leftSpine ids
    let spD := spI.setPpar tNew.rootId (v + 1)
    let S1 : OrdStoreState :=
      { vCap := vCap, eCap := eCap, nextNode := S.nextNode + len, freeHead := 0,
        vRoot := Function.update S.vRoot v tNew.rootId, eNode := eNI,
        splay := spD, nextFree := fun _ => 0, trees := Function.update S.trees v tNew, freeList := [] }
    OrdInv (Function.update curOrd v ((readList mem (ptr + 2) len).map endOfKey)) S1 := by
  intro ids tNew spD S1
  set xs := (readList mem (ptr + 2) len).map endOfKey with hxs_eq
  have htNew_ne : tNew ≠ .leaf := by
    intro h; have := congrArg AuxTree.countNodes h
    simp [tNew, ids, leftSpine_countNodes, AuxTree.countNodes] at this; omega
  have htNew_root_gt : S.nextNode < tNew.rootId := by
    have hm := AuxTree.rootId_mem htNew_ne
    rw [leftSpine_toList, List.mem_map] at hm; rcases hm with ⟨j, _, hje⟩; omega
  have hrt_nz : tNew.rootId ≠ 0 := SplayState.SubtreeInv_nonZero hokI.inv.sub (AuxTree.rootId_mem htNew_ne)
  have hsubI : SplayState.SubtreeInv ordPayload spI 0 tNew := hokI.inv.sub
  have hndI : tNew.toList.Nodup := hokI.inv.nodup
  have hokD : OrdTreeOk (S.nextNode + len) spD tNew := by
    refine
      { null_node := by simp [spD, SplayState.setPpar, Ne.symm hrt_nz, hokI.null_node]
        clean := fun x => by
          by_cases hx : x = tNew.rootId
          · subst hx; simp [spD, SplayState.setPpar, hokI.clean]
          · simp [spD, SplayState.setPpar, hx, hokI.clean]
        inv := ⟨hokI.inv.nodup, ?_⟩
        mem_le := hokI.mem_le
        count_le := hokI.count_le }
    cases htn : tNew with
    | leaf => exact absurd htn htNew_ne
    | node rid rl rr =>
      rcases htn ▸ hsubI with ⟨h1, h2, h3, h4, -, h6, h7, h8, h9⟩
      rcases AuxTree.nodup_node_unfold (htn ▸ hndI) with ⟨_, hrid_l, _, hrid_r, _⟩
      refine ⟨h1, by simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId, h2],
        by simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId, h3],
        by simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId, h4],
        fun h => absurd rfl h,
        by simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId, h6],
        by simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId, h7],
        SplayState.SubtreeInv_agree h8 (fun x hx => by
          simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId,
            show x ≠ rid from fun h => hrid_l (h ▸ hx)]),
        SplayState.SubtreeInv_agree h9 (fun x hx => by
          simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, htn, AuxTree.rootId,
            show x ≠ rid from fun h => hrid_r (h ▸ hx)])⟩
  have hcur1_sub : ∀ u, Function.update curOrd v xs u = [] ∨ Function.update curOrd v xs u = ordAll u := fun u => by
    by_cases huv : u = v
    · subst huv; simp [hord_v]
    · simp only [Function.update_of_ne huv]
      by_cases h : curOrd u = []; exact Or.inl h; exact Or.inr (hcomb u h)
  have huniq1 : OrdUniqueWithin vCap eCap (Function.update curOrd v xs) := by
    refine ⟨⟨fun u => ?_, fun u hu => ?_, fun u x hx => ?_⟩, fun u1 u2 x h1 h2 => ?_⟩
    · rcases hcur1_sub u with h | h; rw [h]; exact List.nodup_nil; rw [h]; exact huniq.nodup u
    · rcases hcur1_sub u with h | h; exact h; rw [h]; exact huniq.eq_nil_of_ge hu
    · rcases hcur1_sub u with h | h; rw [h] at hx; exact absurd hx List.not_mem_nil; rw [h] at hx; exact huniq.edge_lt hx
    · have h1' : x ∈ ordAll u1 := by
        rcases hcur1_sub u1 with h | h; rw [h] at h1; exact absurd h1 List.not_mem_nil; rwa [← h]
      have h2' : x ∈ ordAll u2 := by
        rcases hcur1_sub u2 with h | h; rw [h] at h2; exact absurd h2 List.not_mem_nil; rwa [← h]
      exact huniq.unique_v h1' h2'
  have hspD_old : ∀ x ≤ S.nextNode, spD.nodes x = S.splay.nodes x := fun x hx => by
    simp only [spD, SplayState.setPpar, SplayState.nodes_updateNode, show x ≠ tNew.rootId by omega, ite_false]
    exact houtI x hx
  have hspD_val : ∀ x, (spD.nodes x).val = (spI.nodes x).val := fun x => by
    by_cases hx : x = tNew.rootId
    · subst hx; simp [spD, SplayState.setPpar, SplayState.nodes_updateNode]
    · simp [spD, SplayState.setPpar, SplayState.nodes_updateNode, hx]
  have hlist_v1 : tNew.toList.map (fun x => endOfKey (spD.nodes x).val) = xs := by
    rw [leftSpine_toList]
    apply List.ext_getElem (by simp [ids, hxs_eq, readList_length])
    intro j hj _
    have hj_lt : j < len := by simp [ids] at hj; exact hj
    simp only [ids, hxs_eq, List.getElem_map, List.getElem_range]
    rw [hspD_val, hvalI j hj_lt, readList_getElem mem (ptr + 2) len j (by rw [readList_length]; exact hj_lt)]
  exact
    { ord_unique := huniq1
      next_le := by omega
      clean := hokD.clean
      null_node := hokD.null_node
      tree_inv := fun u hu => by
        dsimp only [S1] at hu ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self]; exact hokD.inv
        · simp only [Function.update_of_ne h]
          have hu' : u < S.vCap := by omega
          exact ⟨(hinv.tree_inv u hu').nodup, SplayState.SubtreeInv_agree (hinv.tree_inv u hu').sub fun x hx =>
            (hspD_old x (hinv.live_le_nextNode hu' hx).2).symm⟩
      tree_out := fun u hu => by
        dsimp only [S1] at hu ⊢; rw [Function.update_of_ne (by omega)]; exact hinv.tree_out u (by omega)
      vRoot_eq := fun u hu => by
        dsimp only [S1] at hu ⊢
        by_cases h : u = v <;> simp [h, hinv.vRoot_eq u (by omega)]
      root_ppar := fun u hu hne => by
        dsimp only [S1] at hu hne ⊢
        by_cases h : u = v
        · subst h; simp [spD, SplayState.setPpar, SplayState.nodes_updateNode]
        · simp only [Function.update_of_ne h] at hne ⊢
          have hu' : u < S.vCap := by omega
          rw [hspD_old _ (hinv.live_le_nextNode hu' (AuxTree.rootId_mem hne)).2]
          exact hinv.root_ppar u hu' hne
      list_eq := fun u hu => by
        dsimp only [S1] at hu ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self]; exact hlist_v1
        · simp only [Function.update_of_ne h]
          have hu' : u < S.vCap := by omega
          rw [← hinv.list_eq u hu']
          exact List.map_congr_left fun x hx => by rw [hspD_old x (hinv.live_le_nextNode hu' hx).2]
      disj_trees := fun u1 u2 hne x h1 h2 => by
        dsimp only [S1] at h1 h2
        have hnew_gt : ∀ z ∈ tNew.toList, S.nextNode < z := fun z hz => by
          rw [leftSpine_toList, List.mem_map] at hz; rcases hz with ⟨j, _, rfl⟩; omega
        have hold_le : ∀ w0, w0 ≠ v → ∀ z ∈ (S.trees w0).toList, z ≤ S.nextNode := fun w0 _ z hz => by
          by_cases hw0 : w0 < S.vCap
          · exact (hinv.live_le_nextNode hw0 hz).2
          · rw [hinv.tree_out w0 (Nat.le_of_not_lt hw0)] at hz; exact absurd hz List.not_mem_nil
        by_cases h1v : u1 = v
        · subst h1v; simp only [Function.update_self] at h1; simp only [Function.update_of_ne (Ne.symm hne)] at h2
          have := hnew_gt x h1; have := hold_le u2 (Ne.symm hne) x h2; omega
        · simp only [Function.update_of_ne h1v] at h1
          by_cases h2v : u2 = v
          · subst h2v; simp only [Function.update_self] at h2
            have := hnew_gt x h2; have := hold_le u1 h1v x h1; omega
          · simp only [Function.update_of_ne h2v] at h2
            exact hinv.disj_trees u1 u2 hne x h1 h2
      free_nodup := List.nodup_nil
      free_disj := fun _ _ _ h => absurd h List.not_mem_nil
      free_chain := rfl
      nodes_range := fun x => by
        dsimp only [S1]; simp only [List.not_mem_nil, false_or]
        constructor
        · rintro ⟨u, hu, hxu⟩
          by_cases h : u = v
          · subst h; simp only [Function.update_self, tNew, ids, leftSpine_toList, List.mem_map] at hxu
            rcases hxu with ⟨j, hj, rfl⟩; rw [List.mem_range] at hj; omega
          · simp only [Function.update_of_ne h] at hxu
            have := hinv.live_le_nextNode (by omega : u < S.vCap) hxu; omega
        · rintro ⟨hx1, hx2⟩
          by_cases hle : x ≤ S.nextNode
          · rcases (hinv.nodes_range x).mpr ⟨hx1, hle⟩ with hfl | ⟨u, hu, hxu⟩
            · rw [hflS] at hfl; exact absurd hfl List.not_mem_nil
            · have huv : u ≠ v := fun h => by
                subst h
                have hnil : (S.trees u).toList = [] := by
                  have := hinv.list_eq u hu; rw [hcur_v] at this; exact List.map_eq_nil_iff.mp this
                rw [hnil] at hxu; exact List.not_mem_nil hxu
              exact ⟨u, by omega, by simp [Function.update_of_ne huv, hxu]⟩
          · refine ⟨v, hv_lt, ?_⟩
            simp only [Function.update_self, tNew, ids, leftSpine_toList, List.mem_map]
            exact ⟨x - S.nextNode - 1, List.mem_range.mpr (by omega), by omega⟩
      key_lt := fun u hu x hx => by
        dsimp only [S1] at hu hx ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self, tNew, ids, leftSpine_toList, List.mem_map] at hx
          rcases hx with ⟨j, hj, rfl⟩; rw [List.mem_range] at hj
          rw [hspD_val, hvalI j hj]; exact hxs_def j hj
        · simp only [Function.update_of_ne h] at hx
          have hu' : u < S.vCap := by omega
          rw [hspD_old x (hinv.live_le_nextNode hu' hx).2]
          have := hinv.key_lt u hu' x hx; omega
      eNode_spec := fun k hk => by
        dsimp only [S1] at hk ⊢
        rw [henfI k hk]
        cases hf : (List.range len).find? (fun j => mem (ptr + 2 + j) == k) with
        | some j =>
          have hj_lt := List.mem_range.mp (List.mem_of_find?_eq_some hf)
          have hj_eq : mem (ptr + 2 + j) = k := by simpa using List.find?_some hf
          refine Or.inr ⟨v, hv_lt, ?_, ?_⟩
          · simp only [Function.update_self, tNew, ids, leftSpine_toList, List.mem_map]
            exact ⟨j, List.mem_range.mpr hj_lt, rfl⟩
          · rw [hspD_val, hvalI j hj_lt]; exact hj_eq
        | none =>
          have hnone_new : ∀ j < len, mem (ptr + 2 + j) ≠ k := fun j hj heq => by
            have := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
            exact this (beq_iff_eq.mpr heq)
          rcases hinv.eNode_spec k (by omega) with ⟨h0, hnone_old⟩ | ⟨w0, hw0, hmem0, hval0⟩
          · refine Or.inl ⟨h0, fun u hu x hx hval => ?_⟩
            by_cases h : u = v
            · subst h; simp only [Function.update_self, tNew, ids, leftSpine_toList, List.mem_map] at hx
              rcases hx with ⟨j, hj, rfl⟩; rw [List.mem_range] at hj
              rw [hspD_val, hvalI j hj] at hval; exact hnone_new j hj hval
            · simp only [Function.update_of_ne h] at hx
              have hu' : u < S.vCap := by omega
              rw [hspD_old x (hinv.live_le_nextNode hu' hx).2] at hval
              exact hnone_old u hu' x hx hval
          · have hwv : w0 ≠ v := fun h => by
              subst h
              have hnil : (S.trees w0).toList = [] := by
                have := hinv.list_eq w0 hw0; rw [hcur_v] at this; exact List.map_eq_nil_iff.mp this
              rw [hnil] at hmem0; exact List.not_mem_nil hmem0
            refine Or.inr ⟨w0, by omega, by simp [Function.update_of_ne hwv, hmem0], ?_⟩
            rw [hspD_old _ (hinv.live_le_nextNode hw0 hmem0).2]; exact hval0 }

/-- Execution of the non-empty record branch (`len > 0`) inside `ordInitOuterLoop`. -/
theorem ordInitNonEmpty_runs
    {w vCap eCap ordPtr heap ptr v len i : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {stC : State} {S : OrdStoreState} {curOrd : ℕ → List End} {tlRecs : List (ℕ × List End)}
    (huniq : OrdUniqueWithin vCap eCap (readOrd mem ordPtr))
    (hw : heap + ordArenaSize vCap eCap < 2 ^ w)
    (hlen_pos : 0 < len) (hptr_le : ptr + 2 + len ≤ heap) (hnn_le : S.nextNode + len ≤ 2 * eCap)
    (hcur_v : curOrd v = []) (hord_tl_v : ordOfRecords tlRecs v = [])
    (hread_v : readOrd mem ordPtr v = (readList mem (ptr + 2) len).map endOfKey)
    (hdisj_ne : ∀ u, u ≠ v → curOrd u = [] ∨ ordOfRecords tlRecs u = [])
    (hcomb_ne : ∀ u, u ≠ v → (if curOrd u ≠ [] then curOrd u else ordOfRecords tlRecs u) = readOrd mem ordPtr u)
    (hcomb_all : ∀ u, curOrd u ≠ [] → curOrd u = readOrd mem ordPtr u)
    (hinv : OrdInv curOrd S) (hvS : S.vCap = vCap) (heS : S.eCap = eCap)
    (hfhS : S.freeHead = 0) (hflS : S.freeList = [])
    (r1 : stC.regs 1 = eCap) (r3 : stC.regs 3 = heap) (r4 : stC.regs 4 = ordVRootBase heap)
    (r5 : stC.regs 5 = ordENodeBase heap vCap) (r6 : stC.regs 6 = ordNodesBase heap vCap eCap)
    (r7 : stC.regs 7 = mem ordPtr) (r8 : stC.regs 8 = ptr + 2) (r9 : stC.regs 9 = S.nextNode)
    (r10 : stC.regs 10 = i) (r11 : stC.regs 11 = v) (r12 : stC.regs 12 = len)
    (hhdr : stC.mem heap = vCap ∧ stC.mem (heap + 1) = eCap ∧ stC.mem (heap + 2) = ordVRootBase heap ∧
      stC.mem (heap + 3) = ordENodeBase heap vCap ∧ stC.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
      stC.mem (heap + 6) = 0)
    (hvr : ∀ u < vCap, stC.mem (ordVRootBase heap + u) = S.vRoot u)
    (hen : ∀ k < 2 * eCap, stC.mem (ordENodeBase heap vCap + k) = S.eNode k)
    (hn : OrdNodesAt stC.mem (ordNodesBase heap vCap eCap) S.nextNode S.splay (fun _ => 0))
    (hznd : ∀ u, S.nextNode < u → u ≤ 2 * eCap → ∀ o < 8, stC.mem (ordNodesBase heap vCap eCap + 8 * u + o) = 0)
    (hzout : ZeroFrom stC.mem (heap + ordArenaSize vCap eCap))
    (hlt : ∀ a < heap, stC.mem a = mem a) :
    ∃ stD cD, ∃ S1 : OrdStoreState, ∃ curOrd1 : ℕ → List End,
      Runs w p ω
        (.assign 13 (.const 0) ;;
         .assign 14 (.const 0) ;;
         ordInitInnerLoop ;;
         .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 3))
           (.bin .add (.reg 11) (.const 1)) ;;
         .store (.bin .add (.reg 4) (.reg 11)) (.reg 13)) stC .normal stD cD ∧
      stD.regs 1 = eCap ∧ stD.regs 3 = heap ∧ stD.regs 4 = ordVRootBase heap ∧
      stD.regs 5 = ordENodeBase heap vCap ∧ stD.regs 6 = ordNodesBase heap vCap eCap ∧
      stD.regs 7 = mem ordPtr ∧ stD.regs 8 = ptr + 2 ∧ stD.regs 9 = S1.nextNode ∧
      stD.regs 10 = i ∧ stD.regs 12 = len ∧
      S1.nextNode = S.nextNode + len ∧
      (∀ u, curOrd1 u = [] ∨ ordOfRecords tlRecs u = []) ∧
      (∀ u, (if curOrd1 u ≠ [] then curOrd1 u else ordOfRecords tlRecs u) = readOrd mem ordPtr u) ∧
      OrdInv curOrd1 S1 ∧ S1.vCap = vCap ∧ S1.eCap = eCap ∧ S1.freeHead = 0 ∧ S1.freeList = [] ∧
      (∀ x, S1.nextFree x = 0) ∧
      stD.mem heap = vCap ∧ stD.mem (heap + 1) = eCap ∧ stD.mem (heap + 2) = ordVRootBase heap ∧
        stD.mem (heap + 3) = ordENodeBase heap vCap ∧ stD.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
        stD.mem (heap + 6) = 0 ∧
      (∀ u < vCap, stD.mem (ordVRootBase heap + u) = S1.vRoot u) ∧
      (∀ k < 2 * eCap, stD.mem (ordENodeBase heap vCap + k) = S1.eNode k) ∧
      OrdNodesAt stD.mem (ordNodesBase heap vCap eCap) S1.nextNode S1.splay (fun _ => 0) ∧
      (∀ u, S1.nextNode < u → u ≤ 2 * eCap → ∀ o < 8, stD.mem (ordNodesBase heap vCap eCap + 8 * u + o) = 0) ∧
      ZeroFrom stD.mem (heap + ordArenaSize vCap eCap) ∧
      (∀ a < heap, stD.mem a = mem a) ∧
      cD + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
        ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + (1450 * len + 80) * ordStoreLog eCap := by
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  have hw' : heap + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  set vr := ordVRootBase heap with hvr_def
  set en := ordENodeBase heap vCap with hen_def
  set nb := ordNodesBase heap vCap eCap with hnb_def
  have hvr_eq : vr = heap + 8 := rfl
  have hen_eq : en = heap + 8 + vCap := by rw [hen_def]; unfold ordENodeBase; omega
  have hnb_eq : nb = heap + 8 + vCap + 2 * eCap := by rw [hnb_def]; unfold ordNodesBase; omega
  have hnb_end : nb + 8 * (2 * eCap + 1) ≤ heap + ordArenaSize vCap eCap := by
    rw [hnb_def]; have := ordNodesBase_end heap vCap eCap; omega
  set xs := (readList mem (ptr + 2) len).map endOfKey with hxs_def
  have hxs_ne : xs ≠ [] := by intro h; have := congrArg List.length h; simp [hxs_def, readList_length] at this; omega
  have hv_lt : v < vCap := by
    have hx0 : xs[0]'(by simp [hxs_def, readList_length]; exact hlen_pos) ∈ readOrd mem ordPtr v := by
      rw [hread_v]; exact List.getElem_mem _
    exact huniq.v_lt_of_mem hx0
  have hkeys_lt_mem : ∀ j < len, mem (ptr + 2 + j) < 2 * eCap := fun j hj => by
    have hm : endOfKey (mem (ptr + 2 + j)) ∈ readOrd mem ordPtr v := by
      rw [hread_v, List.mem_map]
      refine ⟨mem (ptr + 2 + j), ?_, rfl⟩
      have h1 := readList_getElem mem (ptr + 2) len j (by rw [readList_length]; exact hj)
      rw [← h1]; exact List.getElem_mem (by rw [readList_length]; exact hj)
    simpa [endKey_endOfKey] using huniq.key_lt hm
  have hkeys_lt : ∀ j < len, stC.mem (ptr + 2 + j) < 2 * eCap := fun j hj => by
    rw [hlt (ptr + 2 + j) (by omega)]; exact hkeys_lt_mem j hj
  have hrl_eq : readList stC.mem (ptr + 2) len = readList mem (ptr + 2) len := by
    apply List.ext_getElem (by simp [readList_length])
    intro j hj _
    rw [readList_getElem, readList_getElem]
    exact hlt (ptr + 2 + j) (by rw [readList_length] at hj; omega)
  have hkeys_nd : (readList stC.mem (ptr + 2) len).Nodup := by
    rw [hrl_eq]; exact List.Nodup.of_map endOfKey (by rw [← hxs_def, ← hread_v]; exact huniq.nodup v)
  have ha13 : Runs w p ω (.assign 13 (.const 0)) stC .normal
      { stC with regs := Function.update stC.regs 13 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stC1 : State := { stC with regs := Function.update stC.regs 13 0 }
  have ha14 : Runs w p ω (.assign 14 (.const 0)) stC1 .normal
      { stC1 with regs := Function.update stC1.regs 14 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set stC2 : State := { stC1 with regs := Function.update stC1.regs 14 0 }
  obtain ⟨stI, cI, spI, eNI, hrunI, hregI, r9I, r13I, hnI, henI, hfrI, hokI, houtI, hvalI, henfI, hcI⟩ :=
    ordInitInnerLoop_runs (p := p) ω (st0 := stC2) (sp0 := S.splay) (eN0 := S.eNode)
      (ptr := ptr + 2) (base := S.nextNode) (len := len)
      hlen_pos hnn_le (by omega) hkeys_lt hkeys_nd hn
      (fun u hu1 hu2 o ho => hznd u hu1 (by omega) o ho) hen hinv.clean hinv.null_node hw
      (by simp [stC2, stC1, r5, hen_def]) (by simp [stC2, stC1, r6, hnb_def]) (by simp [stC2, stC1, r8])
      (by simp [stC2, stC1, r9]) (by simp [stC2, stC1, r12]) (by simp [stC2, stC1]) (by simp [stC2])
  set ids := (List.range len).map (fun j => S.nextNode + 1 + j)
  set tNew := leftSpine ids
  have htNew_ne : tNew ≠ .leaf := by
    intro h; have := congrArg AuxTree.countNodes h
    simp [tNew, ids, leftSpine_countNodes, AuxTree.countNodes] at this; omega
  have htNew_root_le : tNew.rootId ≤ S.nextNode + len := hokI.mem_le _ (AuxTree.rootId_mem htNew_ne)
  have htNew_root_gt : S.nextNode < tNew.rootId := by
    have hm := AuxTree.rootId_mem htNew_ne
    rw [leftSpine_toList, List.mem_map] at hm; rcases hm with ⟨j, _, hje⟩; omega
  have h8_w : 8 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hrt_mul_w : 8 * tNew.rootId < 2 ^ w := by
    have : 8 * tNew.rootId ≤ 8 * (2 * eCap) := Nat.mul_le_mul_left 8 (Nat.le_trans htNew_root_le hnn_le)
    omega
  have hrt_nb_w : nb + 8 * tNew.rootId < 2 ^ w := by
    have : 8 * tNew.rootId ≤ 8 * (2 * eCap) := Nat.mul_le_mul_left 8 (Nat.le_trans htNew_root_le hnn_le)
    omega
  have hrt_pp_w : nb + 8 * tNew.rootId + 3 < 2 ^ w := by
    have : 8 * tNew.rootId ≤ 8 * (2 * eCap) := Nat.mul_le_mul_left 8 (Nat.le_trans htNew_root_le hnn_le)
    omega
  have hv1_w : v + 1 < 2 ^ w := by omega
  have hvrv_w : vr + v < 2 ^ w := by omega
  have hstI_6 : stI.regs 6 = nb := by
    rw [hregI 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r6, hnb_def]
  have hstI_11 : stI.regs 11 = v := by
    rw [hregI 11 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r11]
  have r13I' : stI.regs 13 = tNew.rootId := r13I
  have hs_pp : Runs w p ω
      (.store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 3))
        (.bin .add (.reg 11) (.const 1))) stI .normal
      { stI with mem := Function.update stI.mem (nb + 8 * tNew.rootId + 3) (v + 1) } _ :=
    runs_store_iff.mpr ⟨nb + 8 * tNew.rootId + 3, v + 1,
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hstI_6)
        (Expr.eval_mul (Expr.eval_const h8_w) (Expr.eval_reg_of_eq r13I') hrt_mul_w) hrt_nb_w)
        (Expr.eval_const h3_w) hrt_pp_w,
      Expr.eval_add (Expr.eval_reg_of_eq hstI_11) (Expr.eval_const h1_w) hv1_w, rfl, rfl, rfl⟩
  set stI1 : State := { stI with mem := Function.update stI.mem (nb + 8 * tNew.rootId + 3) (v + 1) }
  have hstI1_4 : stI1.regs 4 = vr := by
    dsimp only [stI1]; rw [hregI 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r4, hvr_def]
  have hstI1_11 : stI1.regs 11 = v := by dsimp only [stI1]; exact hstI_11
  have hs_vr : Runs w p ω (.store (.bin .add (.reg 4) (.reg 11)) (.reg 13)) stI1 .normal
      { stI1 with mem := Function.update stI1.mem (vr + v) tNew.rootId } _ :=
    runs_store_iff.mpr ⟨vr + v, tNew.rootId,
      Expr.eval_add (Expr.eval_reg_of_eq hstI1_4) (Expr.eval_reg_of_eq hstI1_11) hvrv_w,
      Expr.eval_reg_of_eq (by dsimp only [stI1]; exact r13I'), rfl, rfl, rfl⟩
  set stD : State := { stI1 with mem := Function.update stI1.mem (vr + v) tNew.rootId }
  set spD := spI.setPpar tNew.rootId (v + 1)
  set S1 : OrdStoreState :=
    { vCap := vCap, eCap := eCap, nextNode := S.nextNode + len, freeHead := 0,
      vRoot := Function.update S.vRoot v tNew.rootId, eNode := eNI,
      splay := spD, nextFree := fun _ => 0, trees := Function.update S.trees v tNew, freeList := [] }
  set curOrd1 := Function.update curOrd v xs
  have hinv1 : OrdInv curOrd1 S1 :=
    ordInitRecord_inv hinv hvS heS hflS huniq hv_lt hlen_pos hnn_le hcur_v hkeys_lt_mem
      hcomb_all hread_v hokI houtI
      (fun j hj => (hvalI j hj).trans (hlt (ptr + 2 + j) (by omega)))
      (fun k hk => by
        rw [henfI k hk]
        have hfind : ∀ l : List ℕ,
            (∀ j ∈ l, (stC2.mem (ptr + 2 + j) == k) = (mem (ptr + 2 + j) == k)) →
            l.find? (fun j => stC2.mem (ptr + 2 + j) == k) = l.find? (fun j => mem (ptr + 2 + j) == k) := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons a tl iht =>
            intro h1
            simp only [List.find?_cons, h1 a List.mem_cons_self]
            cases hb : (mem (ptr + 2 + a) == k)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact iht fun j hj => h1 j (List.mem_cons_of_mem a hj)
            · simp only [↓reduceIte]
        rw [hfind (List.range len) (fun j hj => by
          rw [List.mem_range] at hj; dsimp only [stC2, stC1]; rw [hlt (ptr + 2 + j) (by omega)])]; rfl)
  have htree_v_leaf : S.trees v = .leaf := by
    cases htv : S.trees v with
    | leaf => rfl
    | node id l r =>
      exfalso; have := hinv.list_eq v (by omega); rw [htv, hcur_v] at this
      have := congrArg List.length this; simp [AuxTree.toList] at this
  have hphi_upd := sumTreePhi_update (S := S) (S' := S1) (by omega) (by rw [hvS])
    (fun u _ huv => Function.update_of_ne huv _ _)
  rw [show S1.trees v = tNew from Function.update_self v tNew S.trees, htree_v_leaf, AuxTree.treePhi] at hphi_upd
  have hcnt_upd := sumCountNodes_update (S := S) (S' := S1) (by omega) (by rw [hvS])
    (fun u _ huv => Function.update_of_ne huv _ _)
  rw [show S1.trees v = tNew from Function.update_self v tNew S.trees, htree_v_leaf, AuxTree.countNodes] at hcnt_upd
  have htNew_phi : tNew.treePhi (fun _ => 0) ≤ len * ordStoreLog eCap := by
    simpa [ids] using leftSpine_treePhi_le (eCap := eCap) ids (by simp [ids]; omega)
  have htNew_cnt : tNew.countNodes = len := by simp [tNew, ids, leftSpine_countNodes]
  rw [htNew_cnt] at hcnt_upd
  have hstD_out : ∀ a, a ≠ vr + v → a ≠ nb + 8 * tNew.rootId + 3 →
      ¬ (nb + 8 * (S.nextNode + 1) ≤ a ∧ a < nb + 8 * (S.nextNode + len + 1)) →
      ¬ (en ≤ a ∧ a < en + 2 * eCap) → stD.mem a = stC.mem a := fun a h1 h2 h3 h4 => by
    dsimp only [stD, stI1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]
    exact hfrI a h3 h4
  have hrt_lo : nb + 8 * (S.nextNode + 1) ≤ nb + 8 * tNew.rootId + 3 := by
    have : S.nextNode + 1 ≤ tNew.rootId := htNew_root_gt; omega
  have hrt_hi : nb + 8 * tNew.rootId + 3 < nb + 8 * (S.nextNode + len + 1) := by
    have : tNew.rootId ≤ S.nextNode + len := htNew_root_le; omega
  refine ⟨stD, _, S1, curOrd1,
    ord_runs_seq_normal ha13 (ord_runs_seq_normal ha14
      (ord_runs_seq_normal hrunI (ord_runs_seq_normal hs_pp hs_vr))),
    by dsimp only [stD, stI1]; rw [hregI 1 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r1],
    by dsimp only [stD, stI1]; rw [hregI 3 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r3],
    by dsimp only [stD, stI1]; rw [hregI 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r4],
    by dsimp only [stD, stI1]; rw [hregI 5 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r5],
    by dsimp only [stD, stI1]; rw [hregI 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r6],
    by dsimp only [stD, stI1]; rw [hregI 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r7],
    by dsimp only [stD, stI1]; rw [hregI 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r8],
    by dsimp only [stD, stI1]; exact r9I,
    by dsimp only [stD, stI1]; rw [hregI 10 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r10],
    by dsimp only [stD, stI1]; rw [hregI 12 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [stC2, stC1, r12],
    rfl,
    fun u => by
      by_cases huv : u = v
      · subst huv; exact Or.inr hord_tl_v
      · simp only [curOrd1, Function.update_of_ne huv]; exact hdisj_ne u huv,
    fun u => by
      by_cases huv : u = v
      · subst huv; simp [curOrd1, hxs_ne, hread_v]
      · simp only [curOrd1, Function.update_of_ne huv]; exact hcomb_ne u huv,
    hinv1, rfl, rfl, rfl, rfl, fun _ => rfl,
    (hstD_out heap (by omega) (by omega) (by omega) (by omega)).trans hhdr.1,
    (hstD_out (heap + 1) (by omega) (by omega) (by omega) (by omega)).trans hhdr.2.1,
    (hstD_out (heap + 2) (by omega) (by omega) (by omega) (by omega)).trans hhdr.2.2.1,
    (hstD_out (heap + 3) (by omega) (by omega) (by omega) (by omega)).trans hhdr.2.2.2.1,
    (hstD_out (heap + 4) (by omega) (by omega) (by omega) (by omega)).trans hhdr.2.2.2.2.1,
    (hstD_out (heap + 6) (by omega) (by omega) (by omega) (by omega)).trans hhdr.2.2.2.2.2,
    fun u hu => by
      by_cases huv : u = v
      · subst huv; simp [stD, S1, hvr_def]
      · exact (hstD_out (vr + u) (by omega) (by omega) (by omega) (by omega)).trans (by simp [S1, huv, hvr u hu]),
    fun k hk => by
      dsimp only [stD, stI1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact henI k hk,
    OrdNodesAt.congr (hnI.setPpar htNew_root_le (v := v + 1)) (fun a ha => by
      dsimp only [stD]; exact Function.update_of_ne (by unfold InOrdNodes at ha; omega) _ _),
    fun u hu1 hu2 o ho => by
      dsimp only [S1] at hu1
      exact (hstD_out (nb + 8 * u + o) (by omega) (by omega) (by omega) (by omega)).trans
        (hznd u (by omega) hu2 o ho),
    fun a ha => (hstD_out a (by unfold ordArenaSize at ha; omega) (by omega) (by omega)
      (by unfold ordArenaSize at ha; omega)).trans (hzout a ha),
    fun a ha => (hstD_out a (by omega) (by omega) (by omega) (by omega)).trans (hlt a ha), ?_⟩
  have hmul_phi := Nat.mul_le_mul_left 1000 htNew_phi
  have hlen_l : len ≤ len * ordStoreLog eCap := Nat.le_mul_of_pos_right len hlog
  have h80_l : 80 ≤ 80 * ordStoreLog eCap := Nat.le_mul_of_pos_right 80 hlog
  have hsp_rhs : (1450 * len + 80) * ordStoreLog eCap =
      1450 * (len * ordStoreLog eCap) + 80 * ordStoreLog eCap := by ring
  unfold ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT
  dsimp only [S1] at hphi_upd hcnt_upd ⊢
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
  omega

end MinCostFlow.SparseCore.Program
