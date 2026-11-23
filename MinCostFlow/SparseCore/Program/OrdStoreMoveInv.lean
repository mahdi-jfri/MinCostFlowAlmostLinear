module

public import MinCostFlow.SparseCore.Program.OrdStoreMoveUnlink
public import MinCostFlow.SparseCore.Program.OrdStoreFreeTree
import Mathlib.Tactic

/-!
# Order Store `moveEnds` Pass 7: Reassembly Invariant Builders

This file provides shared helper lemmas and `OrdInv` constructors (`moveFinish_same_inv`,
`moveFinish_diff_inv`, `ordMoveFinish_setPpar`) used by Pass 7 of `ordMoveEndsBody`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

theorem card_disj_le_nextNode {cap : ℕ} {t1 t2 : AuxTree}
    (hnd1 : t1.toList.Nodup) (hnd2 : t2.toList.Nodup)
    (hdisj : ∀ x ∈ t1.toList, x ∉ t2.toList)
    (hle1 : ∀ x ∈ t1.toList, 1 ≤ x ∧ x ≤ cap) (hle2 : ∀ x ∈ t2.toList, 1 ≤ x ∧ x ≤ cap) :
    t1.countNodes + t2.countNodes ≤ cap := by
  have hnd : (t1.toList ++ t2.toList).Nodup :=
    List.nodup_append.mpr ⟨hnd1, hnd2, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  have hsub : (t1.toList ++ t2.toList).toFinset ⊆ Finset.Icc 1 cap := by
    intro x hx
    rw [List.mem_toFinset, List.mem_append] at hx
    rw [Finset.mem_Icc]
    rcases hx with h1 | h2
    · exact hle1 x h1
    · exact hle2 x h2
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_append, AuxTree.length_toList,
    AuxTree.length_toList, Nat.card_Icc] at hcard
  omega

theorem map_filter_eq_filter_map {α β : Type*} (f : α → β) (p : β → Bool) (l : List α) :
    (l.filter (fun x => p (f x))).map f = (l.map f).filter p := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.filter_cons, List.map_cons]
    cases p (f a) <;> simp [ih]

/-- Build `OrdInv` for the `v = v'` case after keeping `tKeep` at `v` and freeing `tFree`. -/
theorem moveFinish_same_inv
    {ord : ℕ → List End} {S : OrdStoreState} {v : ℕ} {sel : Finset End} {comp : Bool}
    (hinv : OrdInv ord S) (hv : v < S.vCap)
    (huniq' : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit ord (.moveEnds v v sel comp)))
    {spF : SplayState ℕ Unit Unit} {nfF eNF : ℕ → ℕ} {fhF : ℕ} {flF : List ℕ}
    {tKeep tFree : AuxTree}
    (hpart_v : ∀ x, x ∈ (S.trees v).toList ↔ x ∈ tKeep.toList ∨ x ∈ tFree.toList)
    (hdisj_kf : ∀ x ∈ tKeep.toList, x ∉ tFree.toList)
    (hokK : OrdTreeOk S.nextNode spF tKeep)
    (hppK : tKeep ≠ .leaf → (spF.nodes tKeep.rootId).ppar = v + 1)
    (hlistK : tKeep.toList.map (fun x => endOfKey (spF.nodes x).val) =
      (ord v).filter (fun e => !movedBy sel comp e))
    (hout_v : ∀ x ∉ (S.trees v).toList, spF.nodes x = S.splay.nodes x ∧ nfF x = S.nextFree x)
    (hval_in : ∀ x ∈ tKeep.toList, (spF.nodes x).val = (S.splay.nodes x).val)
    (hfl_perm : flF.Perm (tFree.toList ++ S.freeList)) (hfl_nd : flF.Nodup)
    (hfcF : FreeChain fhF nfF flF)
    (heNF : ∀ k < 2 * S.eCap, eNF k = if (∃ u ∈ tFree.toList, (S.splay.nodes u).val = k) then 0 else S.eNode k) :
    let S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := fhF,
        vRoot := Function.update S.vRoot v tKeep.rootId, eNode := eNF,
        splay := spF, nextFree := nfF, trees := Function.update S.trees v tKeep, freeList := flF }
    OrdInv (applyOrdEdit ord (.moveEnds v v sel comp)) S' := by
  intro S'
  have hmem_fl : ∀ x, x ∈ flF ↔ x ∈ tFree.toList ∨ x ∈ S.freeList := fun x => by
    rw [hfl_perm.mem_iff, List.mem_append]
  have hkeep_sub : ∀ x ∈ tKeep.toList, x ∈ (S.trees v).toList := fun x hx => (hpart_v x).mpr (Or.inl hx)
  have hfree_sub : ∀ x ∈ tFree.toList, x ∈ (S.trees v).toList := fun x hx => (hpart_v x).mpr (Or.inr hx)
  refine
    { ord_unique := huniq'
      next_le := hinv.next_le
      clean := hokK.clean
      null_node := hokK.null_node
      tree_inv := fun u hu => by
        dsimp only [S'] at hu ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self]; exact hokK.inv
        · simp only [Function.update_of_ne h]
          exact ⟨(hinv.tree_inv u hu).nodup, SplayState.SubtreeInv_agree (hinv.tree_inv u hu).sub fun x hx =>
            (hout_v x (fun hxv => hinv.disj_trees u v h x hx hxv)).1.symm⟩
      tree_out := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [Function.update_of_ne (by omega)]; exact hinv.tree_out u hu
      vRoot_eq := fun u hu => by
        dsimp only [S'] at hu ⊢
        by_cases h : u = v <;> simp [h, hinv.vRoot_eq u hu]
      root_ppar := fun u hu hne => by
        dsimp only [S'] at hu hne ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hne ⊢; exact hppK hne
        · simp only [Function.update_of_ne h] at hne ⊢
          have hr := AuxTree.rootId_mem hne
          rw [(hout_v _ (fun hxv => hinv.disj_trees u v h _ hr hxv)).1]
          exact hinv.root_ppar u hu hne
      list_eq := fun u hu => by
        dsimp only [S', applyOrdEdit] at hu ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self, ↓reduceIte]; exact hlistK
        · simp only [Function.update_of_ne h, h, ↓reduceIte]
          rw [← hinv.list_eq u hu]
          exact List.map_congr_left fun x hx => by rw [(hout_v x (fun hxv => hinv.disj_trees u v h x hx hxv)).1]
      disj_trees := fun u1 u2 hne x h1 h2 => by
        dsimp only [S'] at h1 h2
        by_cases h1v : u1 = v
        · subst h1v; simp only [Function.update_self] at h1
          simp only [Function.update_of_ne (Ne.symm hne)] at h2
          exact hinv.disj_trees u1 u2 hne x (hkeep_sub x h1) h2
        · simp only [Function.update_of_ne h1v] at h1
          by_cases h2v : u2 = v
          · subst h2v; simp only [Function.update_self] at h2
            exact hinv.disj_trees u1 u2 hne x h1 (hkeep_sub x h2)
          · simp only [Function.update_of_ne h2v] at h2
            exact hinv.disj_trees u1 u2 hne x h1 h2
      free_nodup := hfl_nd
      free_disj := fun u hu x hxf hxu => by
        dsimp only [S'] at hu hxu; rw [hmem_fl] at hxf
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hxu
          rcases hxf with h1 | h2
          · exact hdisj_kf x hxu h1
          · exact hinv.free_disj u hu x h2 (hkeep_sub x hxu)
        · simp only [Function.update_of_ne h] at hxu
          rcases hxf with h1 | h2
          · exact hinv.disj_trees u v h x hxu (hfree_sub x h1)
          · exact hinv.free_disj u hu x h2 hxu
      free_chain := hfcF
      nodes_range := fun x => by
        dsimp only [S']; rw [← hinv.nodes_range x, hmem_fl]
        constructor
        · rintro ((hf | hfl) | ⟨u, hu, hxu⟩)
          · exact Or.inr ⟨v, hv, hfree_sub x hf⟩
          · exact Or.inl hfl
          · by_cases h : u = v
            · subst h; simp only [Function.update_self] at hxu; exact Or.inr ⟨u, hu, hkeep_sub x hxu⟩
            · simp only [Function.update_of_ne h] at hxu; exact Or.inr ⟨u, hu, hxu⟩
        · rintro (hfl | ⟨u, hu, hxu⟩)
          · exact Or.inl (Or.inr hfl)
          · by_cases h : u = v
            · subst h
              rcases (hpart_v x).mp hxu with hk | hf
              · exact Or.inr ⟨u, hu, by simp [hk]⟩
              · exact Or.inl (Or.inl hf)
            · exact Or.inr ⟨u, hu, by simp [Function.update_of_ne h, hxu]⟩
      key_lt := fun u hu x hx => by
        dsimp only [S'] at hu hx ⊢
        by_cases h : u = v
        · subst h; simp only [Function.update_self] at hx
          rw [hval_in x hx]; exact hinv.key_lt u hu x (hkeep_sub x hx)
        · simp only [Function.update_of_ne h] at hx
          rw [(hout_v x (fun hxv => hinv.disj_trees u v h x hx hxv)).1]
          exact hinv.key_lt u hu x hx
      eNode_spec := fun k hk => by
        dsimp only [S'] at hk ⊢
        rw [heNF k hk]
        by_cases hex : ∃ u ∈ tFree.toList, (S.splay.nodes u).val = k
        · rw [if_pos hex]
          refine Or.inl ⟨rfl, fun u hu x hx hval => ?_⟩
          rcases hex with ⟨z, hz, hzval⟩
          by_cases huv : u = v
          · subst huv; simp only [Function.update_self] at hx
            have hxk : (S.splay.nodes x).val = k := (hval_in x hx).symm.trans hval
            have hx_eq : S.eNode k = x := by rw [← hxk]; exact hinv.eNode_eq_of_mem hu (hkeep_sub x hx)
            have hz_eq : S.eNode k = z := by rw [← hzval]; exact hinv.eNode_eq_of_mem hu (hfree_sub z hz)
            exact hdisj_kf x hx (hx_eq.symm.trans hz_eq ▸ hz)
          · simp only [Function.update_of_ne huv] at hx
            have hxk : (S.splay.nodes x).val = k := by
              rw [← (hout_v x (fun hxv => hinv.disj_trees u v huv x hx hxv)).1]; exact hval
            have hx_eq : S.eNode k = x := by rw [← hxk]; exact hinv.eNode_eq_of_mem hu hx
            have hz_eq : S.eNode k = z := by rw [← hzval]; exact hinv.eNode_eq_of_mem hv (hfree_sub z hz)
            exact hinv.disj_trees u v huv x hx (hx_eq.symm.trans hz_eq ▸ hfree_sub z hz)
        · rw [if_neg hex]
          rcases hinv.eNode_spec k hk with ⟨h0, hnone⟩ | ⟨w0, hw0, hmem0, hval0⟩
          · refine Or.inl ⟨h0, fun u hu x hx hval => ?_⟩
            by_cases huv : u = v
            · subst huv; simp only [Function.update_self] at hx
              exact hnone u hu x (hkeep_sub x hx) ((hval_in x hx).symm.trans hval)
            · simp only [Function.update_of_ne huv] at hx
              have hxv := fun h => hinv.disj_trees u v huv x hx h
              exact hnone u hu x hx (by rw [← (hout_v x hxv).1]; exact hval)
          · by_cases hwv : w0 = v
            · subst hwv
              rcases (hpart_v (S.eNode k)).mp hmem0 with hkeep | hfree
              · refine Or.inr ⟨w0, hw0, by simp [hkeep], (hval_in _ hkeep).trans hval0⟩
              · exfalso; exact hex ⟨S.eNode k, hfree, hval0⟩
            · refine Or.inr ⟨w0, hw0, by simp [Function.update_of_ne hwv, hmem0], ?_⟩
              rw [(hout_v _ (fun hxv => hinv.disj_trees w0 v hwv _ hmem0 hxv)).1]; exact hval0 }

/-- Build `OrdInv` for the `v ≠ v'` case after keeping `tKeep` at `v` and placing the joined tree
`tJ` (with `tJ.toList = (S.trees v').toList ++ tMove.toList`) at `v'`. -/
theorem moveFinish_diff_inv
    {ord : ℕ → List End} {S : OrdStoreState} {v v' : ℕ} {sel : Finset End} {comp : Bool}
    (hinv : OrdInv ord S) (hv : v < S.vCap) (hv' : v' < S.vCap) (hvv' : v ≠ v')
    (huniq' : OrdUniqueWithin S.vCap S.eCap (applyOrdEdit ord (.moveEnds v v' sel comp)))
    {spF : SplayState ℕ Unit Unit} {tKeep tMove tJ : AuxTree}
    (hpart_v : ∀ x, x ∈ (S.trees v).toList ↔ x ∈ tKeep.toList ∨ x ∈ tMove.toList)
    (hdisj_km : ∀ x ∈ tKeep.toList, x ∉ tMove.toList)
    (hokK : OrdTreeOk S.nextNode spF tKeep)
    (hppK : tKeep ≠ .leaf → (spF.nodes tKeep.rootId).ppar = v + 1)
    (hlistK : tKeep.toList.map (fun x => endOfKey (spF.nodes x).val) =
      (ord v).filter (fun e => !movedBy sel comp e))
    (hokJ : OrdTreeOk S.nextNode spF tJ)
    (hppJ : tJ ≠ .leaf → (spF.nodes tJ.rootId).ppar = v' + 1)
    (htJ_list : tJ.toList = (S.trees v').toList ++ tMove.toList)
    (hlistM : tMove.toList.map (fun x => endOfKey (spF.nodes x).val) =
      (ord v).filter (movedBy sel comp))
    (hout_vv' : ∀ x, x ∉ (S.trees v).toList → x ∉ (S.trees v').toList → spF.nodes x = S.splay.nodes x)
    (hval_all : ∀ x, (x ∈ (S.trees v).toList ∨ x ∈ (S.trees v').toList) → (spF.nodes x).val = (S.splay.nodes x).val) :
    let trees' := Function.update (Function.update S.trees v tKeep) v' tJ
    let vRoot' := Function.update (Function.update S.vRoot v tKeep.rootId) v' tJ.rootId
    let S' : OrdStoreState :=
      { vCap := S.vCap, eCap := S.eCap, nextNode := S.nextNode, freeHead := S.freeHead,
        vRoot := vRoot', eNode := S.eNode, splay := spF, nextFree := S.nextFree,
        trees := trees', freeList := S.freeList }
    OrdInv (applyOrdEdit ord (.moveEnds v v' sel comp)) S' := by
  intro trees' vRoot' S'
  have hkeep_sub : ∀ x ∈ tKeep.toList, x ∈ (S.trees v).toList := fun x hx => (hpart_v x).mpr (Or.inl hx)
  have hmove_sub : ∀ x ∈ tMove.toList, x ∈ (S.trees v).toList := fun x hx => (hpart_v x).mpr (Or.inr hx)
  have hlistJ : tJ.toList.map (fun x => endOfKey (spF.nodes x).val) =
      ord v' ++ (ord v).filter (movedBy sel comp) := by
    rw [htJ_list, List.map_append, hlistM, ← hinv.list_eq v' hv']
    congr 1
    exact List.map_congr_left fun x hx => by rw [hval_all x (Or.inr hx)]
  have htrees_v : trees' v = tKeep := by simp [trees', Function.update_of_ne hvv']
  have htrees_v' : trees' v' = tJ := by simp [trees']
  have htrees_out : ∀ u, u ≠ v → u ≠ v' → trees' u = S.trees u := fun u h1 h2 => by
    simp [trees', Function.update_of_ne h1, Function.update_of_ne h2]
  have hmem_J : ∀ x, x ∈ tJ.toList ↔ x ∈ (S.trees v').toList ∨ x ∈ tMove.toList := fun x => by
    rw [htJ_list, List.mem_append]
  refine
    { ord_unique := huniq'
      next_le := hinv.next_le
      clean := hokJ.clean
      null_node := hokJ.null_node
      tree_inv := fun u hu => by
        dsimp only [S'] at hu ⊢
        by_cases h1 : u = v'
        · subst h1; rw [htrees_v']; exact hokJ.inv
        · by_cases h2 : u = v
          · subst h2; rw [htrees_v]; exact hokK.inv
          · rw [htrees_out u h2 h1]
            exact ⟨(hinv.tree_inv u hu).nodup, SplayState.SubtreeInv_agree (hinv.tree_inv u hu).sub fun x hx =>
              (hout_vv' x (fun hxv => hinv.disj_trees u v h2 x hx hxv)
                (fun hxv' => hinv.disj_trees u v' h1 x hx hxv')).symm⟩
      tree_out := fun u hu => by
        dsimp only [S'] at hu ⊢; rw [htrees_out u (by omega) (by omega)]; exact hinv.tree_out u hu
      vRoot_eq := fun u hu => by
        dsimp only [S'] at hu ⊢
        by_cases h1 : u = v'
        · subst h1; simp [vRoot', trees']
        · by_cases h2 : u = v
          · subst h2; simp [vRoot', trees', Function.update_of_ne hvv']
          · simp [vRoot', trees', Function.update_of_ne h1, Function.update_of_ne h2, hinv.vRoot_eq u hu]
      root_ppar := fun u hu hne => by
        dsimp only [S'] at hu hne ⊢
        by_cases h1 : u = v'
        · subst h1; rw [htrees_v'] at hne ⊢; exact hppJ hne
        · by_cases h2 : u = v
          · subst h2; rw [htrees_v] at hne ⊢; exact hppK hne
          · rw [htrees_out u h2 h1] at hne ⊢
            have hr := AuxTree.rootId_mem hne
            rw [hout_vv' _ (fun hxv => hinv.disj_trees u v h2 _ hr hxv)
              (fun hxv' => hinv.disj_trees u v' h1 _ hr hxv')]
            exact hinv.root_ppar u hu hne
      list_eq := fun u hu => by
        dsimp only [S', applyOrdEdit] at hu ⊢
        by_cases h2 : u = v
        · subst h2; rw [htrees_v]; simp only [↓reduceIte]; exact hlistK
        · by_cases h1 : u = v'
          · subst h1; rw [htrees_v']; simp only [h2, ↓reduceIte]; exact hlistJ
          · rw [htrees_out u h2 h1]; simp only [h2, h1, ↓reduceIte]
            rw [← hinv.list_eq u hu]
            exact List.map_congr_left fun x hx => by
              rw [hout_vv' x (fun hxv => hinv.disj_trees u v h2 x hx hxv)
                (fun hxv' => hinv.disj_trees u v' h1 x hx hxv')]
      disj_trees := fun u1 u2 hne x h1 h2 => by
        dsimp only [S'] at h1 h2
        have hbel : ∀ u, x ∈ (trees' u).toList → (u = v ∧ x ∈ tKeep.toList) ∨
            (u = v' ∧ (x ∈ (S.trees v').toList ∨ x ∈ tMove.toList)) ∨
            (u ≠ v ∧ u ≠ v' ∧ x ∈ (S.trees u).toList) := fun u hu => by
          by_cases huv' : u = v'
          · subst huv'; rw [htrees_v', hmem_J] at hu; exact Or.inr (Or.inl ⟨rfl, hu⟩)
          · by_cases huv : u = v
            · subst huv; rw [htrees_v] at hu; exact Or.inl ⟨rfl, hu⟩
            · rw [htrees_out u huv huv'] at hu; exact Or.inr (Or.inr ⟨huv, huv', hu⟩)
        rcases hbel u1 h1 with ⟨rfl, hk1⟩ | ⟨rfl, hv'1 | hm1⟩ | ⟨h1v, h1v', ho1⟩ <;>
        rcases hbel u2 h2 with ⟨rfl, hk2⟩ | ⟨rfl, hv'2 | hm2⟩ | ⟨h2v, h2v', ho2⟩
        · exact hne rfl
        · exact hinv.disj_trees u1 u2 hne x (hkeep_sub x hk1) hv'2
        · exact hdisj_km x hk1 hm2
        · exact hinv.disj_trees u1 u2 hne x (hkeep_sub x hk1) ho2
        · exact hinv.disj_trees u2 u1 (Ne.symm hne) x (hkeep_sub x hk2) hv'1
        · exact hne rfl
        · exact hne rfl
        · exact hinv.disj_trees u1 u2 hne x hv'1 ho2
        · exact hdisj_km x hk2 hm1
        · exact hne rfl
        · exact hne rfl
        · exact hinv.disj_trees v u2 h2v.symm x (hmove_sub x hm1) ho2
        · exact hinv.disj_trees u1 u2 hne x ho1 (hkeep_sub x hk2)
        · exact hinv.disj_trees u1 u2 hne x ho1 hv'2
        · exact hinv.disj_trees u1 v h1v x ho1 (hmove_sub x hm2)
        · exact hinv.disj_trees u1 u2 hne x ho1 ho2
      free_nodup := hinv.free_nodup
      free_disj := fun u hu x hxf hxu => by
        dsimp only [S'] at hu hxu
        by_cases h1 : u = v'
        · subst h1; rw [htrees_v', hmem_J] at hxu
          rcases hxu with h | h
          · exact hinv.free_disj u hu x hxf h
          · exact hinv.free_disj v hv x hxf (hmove_sub x h)
        · by_cases h2 : u = v
          · subst h2; rw [htrees_v] at hxu; exact hinv.free_disj u hu x hxf (hkeep_sub x hxu)
          · rw [htrees_out u h2 h1] at hxu; exact hinv.free_disj u hu x hxf hxu
      free_chain := hinv.free_chain
      nodes_range := fun x => by
        dsimp only [S']; rw [← hinv.nodes_range x]
        constructor
        · rintro (hfl | ⟨u, hu, hxu⟩)
          · exact Or.inl hfl
          · by_cases h1 : u = v'
            · subst h1; rw [htrees_v', hmem_J] at hxu
              rcases hxu with h | h
              · exact Or.inr ⟨u, hu, h⟩
              · exact Or.inr ⟨v, hv, hmove_sub x h⟩
            · by_cases h2 : u = v
              · subst h2; rw [htrees_v] at hxu; exact Or.inr ⟨u, hu, hkeep_sub x hxu⟩
              · rw [htrees_out u h2 h1] at hxu; exact Or.inr ⟨u, hu, hxu⟩
        · rintro (hfl | ⟨u, hu, hxu⟩)
          · exact Or.inl hfl
          · by_cases h1 : u = v'
            · subst h1; exact Or.inr ⟨u, hu, by rw [htrees_v', hmem_J]; exact Or.inl hxu⟩
            · by_cases h2 : u = v
              · subst h2
                rcases (hpart_v x).mp hxu with hk | hm
                · exact Or.inr ⟨u, hu, by rw [htrees_v]; exact hk⟩
                · exact Or.inr ⟨v', hv', by rw [htrees_v', hmem_J]; exact Or.inr hm⟩
              · exact Or.inr ⟨u, hu, by rw [htrees_out u h2 h1]; exact hxu⟩
      key_lt := fun u hu x hx => by
        dsimp only [S'] at hu hx ⊢
        by_cases h1 : u = v'
        · subst h1; rw [htrees_v', hmem_J] at hx
          rcases hx with h | h
          · rw [hval_all x (Or.inr h)]; exact hinv.key_lt u hu x h
          · rw [hval_all x (Or.inl (hmove_sub x h))]; exact hinv.key_lt v hv x (hmove_sub x h)
        · by_cases h2 : u = v
          · subst h2; rw [htrees_v] at hx
            rw [hval_all x (Or.inl (hkeep_sub x hx))]; exact hinv.key_lt u hu x (hkeep_sub x hx)
          · rw [htrees_out u h2 h1] at hx
            rw [hout_vv' x (fun hxv => hinv.disj_trees u v h2 x hx hxv)
              (fun hxv' => hinv.disj_trees u v' h1 x hx hxv')]
            exact hinv.key_lt u hu x hx
      eNode_spec := fun k hk => by
        dsimp only [S'] at hk ⊢
        rcases hinv.eNode_spec k hk with ⟨h0, hnone⟩ | ⟨w0, hw0, hmem0, hval0⟩
        · refine Or.inl ⟨h0, fun u hu x hx hval => ?_⟩
          by_cases h1 : u = v'
          · subst h1; rw [htrees_v', hmem_J] at hx
            rcases hx with h | h
            · exact hnone u hu x h ((hval_all x (Or.inr h)).symm.trans hval)
            · exact hnone v hv x (hmove_sub x h) ((hval_all x (Or.inl (hmove_sub x h))).symm.trans hval)
          · by_cases h2 : u = v
            · subst h2; rw [htrees_v] at hx
              exact hnone u hu x (hkeep_sub x hx) ((hval_all x (Or.inl (hkeep_sub x hx))).symm.trans hval)
            · rw [htrees_out u h2 h1] at hx
              exact hnone u hu x hx
                (by rw [← hout_vv' x (fun hxv => hinv.disj_trees u v h2 x hx hxv)
                  (fun hxv' => hinv.disj_trees u v' h1 x hx hxv')]; exact hval)
        · by_cases h1 : w0 = v'
          · subst h1
            exact Or.inr ⟨w0, hw0, by rw [htrees_v', hmem_J]; exact Or.inl hmem0,
              (hval_all _ (Or.inr hmem0)).trans hval0⟩
          · by_cases h2 : w0 = v
            · subst h2
              rcases (hpart_v (S.eNode k)).mp hmem0 with hk0 | hm0
              · exact Or.inr ⟨w0, hw0, by rw [htrees_v]; exact hk0, (hval_all _ (Or.inl hmem0)).trans hval0⟩
              · exact Or.inr ⟨v', hv', by rw [htrees_v', hmem_J]; exact Or.inr hm0,
                  (hval_all _ (Or.inl hmem0)).trans hval0⟩
            · refine Or.inr ⟨w0, hw0, by rw [htrees_out w0 h2 h1]; exact hmem0, ?_⟩
              rw [hout_vv' _ (fun hxv => hinv.disj_trees w0 v h2 _ hmem0 hxv)
                (fun hxv' => hinv.disj_trees w0 v' h1 _ hmem0 hxv')]; exact hval0 }

/-- Conditionally set `tSel.rootId.ppar := v + 1` when `tSel.rootId ≠ 0`. -/
theorem ordMoveFinish_setPpar
    {w nb cap v : ℕ} {p : Program} (ω : ℕ → Bool)
    {stM : State} {spM : SplayState ℕ Unit Unit} {nfM : ℕ → ℕ} {tSel : AuxTree}
    (m1 : stM.regs 1 = v) (m9 : stM.regs 9 = nb) (m13 : stM.regs 13 = tSel.rootId)
    (hnM : OrdNodesAt stM.mem nb cap spM nfM) (hokM : OrdTreeOk cap spM tSel)
    (hnb_w : nb + 8 * (cap + 1) < 2 ^ w) (hv_w : v + 1 < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ stP cP, Runs w p ω
        (.cond (.reg 13)
          (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 3))
            (.bin .add (.reg 1) (.const 1))) .nop) stM .normal stP cP ∧
      let spP := if tSel.rootId = 0 then spM else spM.setPpar tSel.rootId (v + 1)
      stP.regs = stM.regs ∧
      OrdNodesAt stP.mem nb cap spP nfM ∧
      (∀ a, ¬ InOrdNodes nb cap a → stP.mem a = stM.mem a) ∧
      OrdTreeOk cap spP tSel ∧
      (tSel ≠ .leaf → (spP.nodes tSel.rootId).ppar = v + 1) ∧
      (∀ x, x ≠ tSel.rootId → spP.nodes x = spM.nodes x) ∧
      (∀ x, (spP.nodes x).val = (spM.nodes x).val) ∧ cP ≤ 30 := by
  by_cases hS0 : tSel.rootId = 0
  · have hc : (Expr.reg 13).eval w stM = some 0 := Expr.eval_reg_of_eq (by rw [m13, hS0])
    refine ⟨stM, _, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), rfl,
      by simp [hS0, hnM], fun _ _ => rfl, by simp [hS0, hokM],
      fun hne => by
        cases hts : tSel with
        | leaf => exact absurd hts hne
        | node sid sl sr =>
          exfalso; simp only [hts, AuxTree.rootId] at hS0
          exact SplayState.SubtreeInv_nonZero hokM.inv.sub (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp)) hS0,
      fun _ _ => by simp [hS0], fun _ => by simp [hS0], by simp [Expr.size_reg]⟩
  · have hc : (Expr.reg 13).eval w stM = some tSel.rootId := Expr.eval_reg_of_eq m13
    have hS_le : tSel.rootId ≤ cap := by
      cases hts : tSel with
      | leaf => simp [hts, AuxTree.rootId] at hS0
      | node sid sl sr => exact hokM.mem_le sid (by rw [hts]; exact AuxTree.rootId_mem (t := .node sid sl sr) (by simp))
    have hst : Runs w p ω
        (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 8) (.reg 13))) (.const 3))
          (.bin .add (.reg 1) (.const 1))) stM .normal
        { stM with mem := Function.update stM.mem (nb + 8 * tSel.rootId + 3) (v + 1) } _ :=
      runs_store_iff.mpr ⟨nb + 8 * tSel.rootId + 3, v + 1,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq m9)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq m13) (by omega)) (by omega))
          (Expr.eval_const (by omega)) (by omega),
        Expr.eval_add (Expr.eval_reg_of_eq m1) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    refine ⟨_, _, ord_runs_cond_true hc hS0 hst, rfl,
      by simp only [hS0, ite_false]; exact hnM.setPpar hS_le (v := v + 1),
      fun a ha => Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _,
      by
        simp only [hS0, ite_false]
        refine
          { null_node := by simp [SplayState.setPpar, SplayState.nodes_updateNode, Ne.symm hS0, hokM.null_node]
            clean := fun x => by
              by_cases hx : x = tSel.rootId
              · subst hx; simp [SplayState.setPpar, SplayState.nodes_updateNode, hokM.clean]
              · simp [SplayState.setPpar, SplayState.nodes_updateNode, hx, hokM.clean]
            inv := ⟨hokM.inv.nodup, ?_⟩
            mem_le := hokM.mem_le
            count_le := hokM.count_le }
        cases hts : tSel with
        | leaf => trivial
        | node sid sl sr =>
          rcases hts ▸ hokM.inv.sub with ⟨h1, h2, h3, h4, -, h6, h7, h8, h9⟩
          rcases AuxTree.nodup_node_unfold (hts ▸ hokM.inv.nodup) with ⟨_, hsid_l, _, hsid_r, _⟩
          refine ⟨h1, by simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId, h2],
            by simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId, h3],
            by simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId, h4],
            fun h => absurd rfl h,
            by simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId, h6],
            by simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId, h7],
            SplayState.SubtreeInv_agree h8 (fun x hx => by
              simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId,
                show x ≠ sid from fun h => hsid_l (h ▸ hx)]),
            SplayState.SubtreeInv_agree h9 (fun x hx => by
              simp [SplayState.setPpar, SplayState.nodes_updateNode, hts, AuxTree.rootId,
                show x ≠ sid from fun h => hsid_r (h ▸ hx)])⟩,
      fun _ => by simp [hS0, SplayState.setPpar, SplayState.nodes_updateNode],
      fun x hx => by simp [hS0, SplayState.setPpar, SplayState.nodes_updateNode, hx],
      fun x => by
        by_cases hx : x = tSel.rootId
        · subst hx; simp [hS0, SplayState.setPpar, SplayState.nodes_updateNode]
        · simp [hS0, SplayState.setPpar, SplayState.nodes_updateNode, hx],
      by simp [Expr.size_bin, Expr.size_reg, Expr.size_const]⟩

end MinCostFlow.SparseCore.Program
