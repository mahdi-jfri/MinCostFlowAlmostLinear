module

public import MinCostFlow.LSF.Program.DecompClosureMath

/-!
# Subtree sizes, bottom-up

The size pass walks the top-down order `Q` from the back. At an index `x` all children are done
and `acc x` is the sum of their sizes; the pass stores `sz x = acc x + 1` and adds it to
`acc (par x)`. `SizeState` is the loop invariant. Its last part says that the sum of `acc` over
the indices not yet done is the number of indices done, which bounds every value by `n`.
`size_bridge` shows that `sz` is the size of the subtree on the vertices of `T₀`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

/-- The loop invariant of the size pass, after the positions `j, j + 1, …` of `Q`. -/
def SizeState (Q : List ℕ) (par : ℕ → ℕ) (n : ℕ) (acc sz : ℕ → ℕ) (j : ℕ) : Prop :=
  (∀ u < n, acc u = (((Q.drop j).filter (fun c => decide (par c = u))).map sz).sum) ∧
  (∀ x ∈ Q.drop j, sz x = acc x + 1) ∧
  ((Q.take j).map acc).sum + j = n

lemma list_sum_map_update {l : List ℕ} (hnd : l.Nodup) {f : ℕ → ℕ} {p v : ℕ} (hp : p ∈ l) :
    (l.map (Function.update f p v)).sum + f p = (l.map f).sum + v := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [Function.update_self]
      have : (l.map (Function.update f p v)) = l.map f :=
        List.map_congr_left (fun x hx => Function.update_of_ne (fun h => hnd.1 (by rw [← h]; exact hx)) _ _)
      rw [this]; omega
    · have hap : a ≠ p := fun h => hnd.1 (h ▸ hp')
      rw [Function.update_of_ne hap]
      have := ih hnd.2 hp'
      omega

lemma sizeState_init (hQ : TopDownOrder n r par Q) (sz : ℕ → ℕ) :
    SizeState Q par n (fun _ => 0) sz n := by
  refine ⟨fun u _ => ?_, fun x hx => ?_, ?_⟩
  · rw [← hQ.len, List.drop_length]; rfl
  · rw [← hQ.len, List.drop_length] at hx; simp at hx
  · simp

lemma sizeState_congr (hQ : TopDownOrder n r par Q) {acc sz acc' sz' : ℕ → ℕ} {j : ℕ}
    (hj : j ≤ n) (ha : ∀ u < n, acc u = acc' u) (hs : ∀ u < n, sz u = sz' u)
    (hI : SizeState Q par n acc sz j) : SizeState Q par n acc' sz' j := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨fun u hu => ?_, fun x hx => ?_, ?_⟩
  · rw [← ha u hu, h1 u hu]
    congr 1
    refine List.map_congr_left (fun c hc => hs c ?_)
    exact hQ.lt c (List.mem_of_mem_drop (List.mem_filter.mp hc).1)
  · have hxn := hQ.lt x (List.mem_of_mem_drop hx)
    rw [← ha x hxn, ← hs x hxn]; exact h2 x hx
  · rw [← h3]
    congr 2
    exact List.map_congr_left (fun c hc => (ha c (hQ.lt c (List.mem_of_mem_take hc))).symm)

/-- Before the step at `Q[j - 1]`, the counts are at most `n - j`. -/
lemma sizeState_acc_le (hQ : TopDownOrder n r par Q) {acc sz : ℕ → ℕ} {j : ℕ}
    (hI : SizeState Q par n acc sz j) {u : ℕ} (hu : u ∈ Q.take j) : acc u + j ≤ n := by
  have h := hI.2.2
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := acc) hu)
  omega

/-- One step of the size pass, at `x = Q[j - 1]` with parent `p`. -/
theorem sizeState_step (hQ : TopDownOrder n r par Q) {acc sz : ℕ → ℕ} {j : ℕ}
    (hj : 2 ≤ j) (hjn : j ≤ n) (hI : SizeState Q par n acc sz j) :
    let x := Q[j - 1]'(by rw [hQ.len]; omega)
    let p := par x
    SizeState Q par n (Function.update acc p (acc p + (acc x + 1)))
      (Function.update sz x (acc x + 1)) (j - 1) := by
  classical
  intro x p
  obtain ⟨hacc, hval, hsum⟩ := hI
  have hjQ : j ≤ Q.length := by rw [hQ.len]; exact hjn
  have hxr : x ≠ r := by
    intro h
    have h0 := hQ.head_eq (by omega)
    have := (hQ.nodup.getElem_inj_iff (hi := by omega) (hj := by rw [hQ.len]; omega)).mp
      (h.trans h0.symm)
    omega
  have hpQ : p ∈ Q.take (j - 1) := hQ.after (j - 1) (by omega) hxr
  have hx_not : x ∉ Q.drop j := by
    intro h
    have hnd := hQ.nodup
    rw [← List.take_append_drop (j - 1) Q, drop_pred_eq (by omega) hjQ] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h
  have hp_not : p ∉ Q.drop (j - 1) := by
    intro h
    have hnd := hQ.nodup
    rw [← List.take_append_drop (j - 1) Q] at hnd
    exact (List.nodup_append.mp hnd).2.2 p hpQ p h rfl
  have hpx : p ≠ x := by
    intro h
    apply hp_not
    rw [h, drop_pred_eq (by omega) hjQ]
    exact List.mem_cons_self
  have htake : Q.take j = Q.take (j - 1) ++ [x] := by
    rw [show j = j - 1 + 1 by omega, List.take_succ_eq_append_getElem (by omega)]
    simp only [show j - 1 + 1 - 1 = j - 1 by omega]
    rfl
  refine ⟨fun u hu => ?_, fun y hy => ?_, ?_⟩
  · rw [drop_pred_eq (by omega) hjQ, List.filter_cons]
    have hrest : ((Q.drop j).filter (fun c => decide (par c = u))).map
        (Function.update sz x (acc x + 1)) =
        ((Q.drop j).filter (fun c => decide (par c = u))).map sz :=
      List.map_congr_left (fun c hc => Function.update_of_ne
        (fun h => hx_not (by rw [← h]; exact (List.mem_filter.mp hc).1)) _ _)
    by_cases hpu : p = u
    · subst hpu
      rw [ite_eq_left (by simp only [decide_eq_true_eq]; rfl), List.map_cons, List.sum_cons, hrest,
        Function.update_self, Function.update_self, hacc p hu]
      omega
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact hpu), hrest,
        Function.update_of_ne (Ne.symm hpu), hacc u hu]
  · rw [drop_pred_eq (by omega) hjQ, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [Function.update_self, Function.update_of_ne (Ne.symm hpx)]
    · have hyx : y ≠ x := fun h => hx_not (h ▸ hy)
      have hyp : y ≠ p := by
        intro h; apply hp_not; rw [drop_pred_eq (by omega) hjQ, ← h]
        exact List.mem_cons_of_mem _ hy
      rw [Function.update_of_ne hyx, Function.update_of_ne hyp]
      exact hval y hy
  · have hnd : (Q.take (j - 1)).Nodup := hQ.nodup.sublist (List.take_sublist _ _)
    have h1 := list_sum_map_update hnd (f := acc) (v := acc p + (acc x + 1)) hpQ
    rw [htake, List.map_append, List.sum_append] at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    omega

/-- The size pass gives the subtree sizes. The root is done after the loop by the same rule
(`hroot`). -/
theorem size_bridge {T₀ : MGraph} {vList : List ℕ} {tM : ℕ}
    {fid tl hd pe dep : ℕ → ℕ} {acc sz : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hS : SizeState Q par vList.length acc sz 1) (hroot : sz r = acc r + 1) :
    ∀ x < vList.length, sz x = (subtree T₀ (vList.getD r 0) (vList.getD x 0)).card := by
  classical
  set n := vList.length with hn_def
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hn : 0 < n := by omega
  have hparent : ∀ x < n, x ≠ r → parent T₀ (g r) (g x) = g (par x) := fun x hx hxr =>
    ((t0Rooted_spec hT.isForest hA hnd hR hr hx).2 hxr).1
  have hgV : ∀ x < n, g x ∈ T₀.V := fun x hx =>
    (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < n ∧ g (vList.idxOf v) = v := fun v hv =>
    ⟨List.idxOf_lt_length_of_mem ((hV v).mp hv), getD_idxOf ((hV v).mp hv)⟩
  have hchild : ∀ x < n, ∀ y < n, g y ∈ childSet T₀ (g r) (g x) ↔ y ≠ r ∧ par y = x := by
    intro x hx y hy
    rw [mem_childSet_iff hT]
    constructor
    · rintro ⟨-, hyr, hp⟩
      have hyr' : y ≠ r := fun h => hyr (by rw [h])
      refine ⟨hyr', ?_⟩
      rw [hparent y hy hyr'] at hp
      exact getD_inj hnd (hR.par_lt y hy) hx hp
    · rintro ⟨hyr, rfl⟩
      exact ⟨hgV y hy, fun h => hyr (getD_inj hnd hy hr h), hparent y hy hyr⟩
  -- `acc x` is the sum of `sz` over the children of `g x`
  have hacc : ∀ x < n, acc x = ∑ c ∈ childSet T₀ (g r) (g x), sz (vList.idxOf c) := by
    intro x hx
    set l := (Q.drop 1).filter (fun c => decide (par c = x)) with hl
    have hlnd : l.Nodup := (hQ.nodup.sublist (List.drop_sublist _ _)).filter _
    have hlt : ∀ y ∈ l, y < n := fun y hy =>
      hQ.lt y (List.mem_of_mem_drop (List.mem_filter.mp hy).1)
    rw [hS.1 x hx, ← hl]
    have hmap : (l.map g).Nodup :=
      List.Nodup.map_on (fun a ha b hb hab => getD_inj hnd (hlt a ha) (hlt b hb) hab) hlnd
    have hset : childSet T₀ (g r) (g x) = (l.map g).toFinset := by
      ext c
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · intro hc
        obtain ⟨hcV, -⟩ := childSet_facts hT hc
        obtain ⟨hyn, hgy⟩ := hidx c hcV
        rw [← hgy] at hc
        obtain ⟨hyr, hpy⟩ := (hchild x hx _ hyn).mp hc
        refine ⟨_, List.mem_filter.mpr ⟨(hQ.mem_drop_one hn).mpr ⟨hyn, hyr⟩, ?_⟩, hgy⟩
        rw [decide_eq_true_iff]; exact hpy
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨hyQ, hyd⟩ := List.mem_filter.mp hy
        rw [decide_eq_true_iff] at hyd
        exact (hchild x hx y (hlt y hy)).mpr ⟨((hQ.mem_drop_one hn).mp hyQ).2, hyd⟩
    rw [hset, List.sum_toFinset _ hmap, List.map_map]
    congr 1
    refine List.map_congr_left (fun y hy => ?_)
    simp only [Function.comp, hg, idxOf_getD hnd (hlt y hy)]
  have hval : ∀ x < n, sz x = acc x + 1 := by
    intro x hx
    by_cases hxr : x = r
    · rw [hxr]; exact hroot
    · exact hS.2.1 x ((hQ.mem_drop_one hn).mpr ⟨hx, hxr⟩)
  -- induction on the subtree size
  have key : ∀ k, ∀ v ∈ T₀.V, (subtree T₀ (g r) v).card ≤ k →
      sz (vList.idxOf v) = (subtree T₀ (g r) v).card := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      have := Finset.card_pos.mpr ⟨v, mem_subtree_iff.mpr ⟨hv, isAncestor_refl T₀ (g r) v⟩⟩
      omega
    | succ k ih =>
      intro v hv hk
      obtain ⟨hxn, hgx⟩ := hidx v hv
      rw [hval _ hxn, hacc _ hxn, hgx]
      have hsplit := subtree_eq_insert_biUnion hT hv
      have hcs : (subtree T₀ (g r) v \ {v}).filter (fun c => parent T₀ (g r) c = v) =
          childSet T₀ (g r) v := by
        ext c; rw [mem_childSet]
      rw [hcs] at hsplit
      have hnotin : v ∉ (childSet T₀ (g r) v).biUnion (subtree T₀ (g r)) := by
        rw [Finset.mem_biUnion]
        rintro ⟨c, hc, hvc⟩
        obtain ⟨hcV, -, -, hcv, -, hvc'⟩ := childSet_facts hT hc
        exact hcv (isAncestor_antisymm hT hcV hv (mem_subtree_iff.mp hvc).2 hvc')
      have hdisj : (childSet T₀ (g r) v : Set ℕ).PairwiseDisjoint (subtree T₀ (g r)) := by
        intro c₁ hc₁ c₂ hc₂ hne
        obtain ⟨h1V, h1r, h1p, -⟩ := childSet_facts hT (show c₁ ∈ childSet T₀ (g r) v from hc₁)
        obtain ⟨h2V, h2r, h2p, -⟩ := childSet_facts hT (show c₂ ∈ childSet T₀ (g r) v from hc₂)
        exact children_subtree_disjoint hT h1V h2V h1r h2r h1p h2p hne
      rw [hsplit, Finset.card_insert_of_notMem hnotin, Finset.card_biUnion hdisj]
      congr 1
      refine Finset.sum_congr rfl (fun c hc => ?_)
      obtain ⟨hcV, -⟩ := childSet_facts hT hc
      exact ih c hcV (by have := card_subtree_child_lt (r := g r) hT hc; omega)
  intro x hx
  have := key _ (g x) (hgV x hx) le_rfl
  rwa [idxOf_getD hnd hx] at this

end MinCostFlow.LSF.Program

end
