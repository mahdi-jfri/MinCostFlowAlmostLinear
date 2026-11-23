module

public import MinCostFlow.LSF.Program.DecompLcaClosure
public import MinCostFlow.LSF.Program.DecompBridge

/-!
# The closure pass over the vertex indices

The boundary of the decomposition is an LCA closure (`b7Props_of_good`). The closure pass finds
it bottom-up. It walks the top-down order `Q` from the back. At an index `x` all children of `x`
are done, and `cnt x` is the number of children `c` with `has c = 1`. The pass stores
* `has x = [0 < S x + cnt x]`: some marked index lies below `x`;
* `inR x = [0 < S x + [1 < cnt x]]`: `x` is marked, or two children have a marked index below;
and adds `has x` to `cnt (par x)`.

`ClosureState` is the loop invariant and `closureState_step` is one step. `closure_bridge` reads
the result on the vertices of `T₀`: by `mem_lcaClosure_iff_children`, `inR` marks exactly the
LCA closure of the marked vertices.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

/-- The two values the pass stores at an index, from its mark and its count. -/
def closureHas (s c : ℕ) : ℕ := if 0 < s + c then 1 else 0

/-- See `closureHas`. -/
def closureIn (s c : ℕ) : ℕ := if 0 < s + (if 1 < c then 1 else 0) then 1 else 0

/-- The loop invariant of the closure pass, after the positions `j, j + 1, …` of `Q`. -/
def ClosureState (Q : List ℕ) (par : ℕ → ℕ) (n : ℕ) (S cnt has inR : ℕ → ℕ) (j : ℕ) : Prop :=
  (∀ u < n, cnt u = ((Q.drop j).filter (fun c => decide (par c = u ∧ has c = 1))).length) ∧
  (∀ x ∈ Q.drop j, has x = closureHas (S x) (cnt x) ∧ inR x = closureIn (S x) (cnt x))

lemma closureHas_le (s c : ℕ) : closureHas s c ≤ 1 := by unfold closureHas; split_ifs <;> omega

lemma closureState_init (hQ : TopDownOrder n r par Q) (S has inR : ℕ → ℕ) :
    ClosureState Q par n S (fun _ => 0) has inR n := by
  refine ⟨fun u _ => ?_, fun x hx => ?_⟩
  · rw [← hQ.len, List.drop_length]; rfl
  · rw [← hQ.len, List.drop_length] at hx; simp at hx

lemma closureState_congr (hQ : TopDownOrder n r par Q) {S cnt has inR cnt' has' inR' : ℕ → ℕ}
    {j : ℕ} (hc : ∀ u < n, cnt u = cnt' u) (hh : ∀ u < n, has u = has' u)
    (hi : ∀ u < n, inR u = inR' u) (hI : ClosureState Q par n S cnt has inR j) :
    ClosureState Q par n S cnt' has' inR' j := by
  obtain ⟨h1, h2⟩ := hI
  refine ⟨fun u hu => ?_, fun x hx => ?_⟩
  · rw [← hc u hu, h1 u hu]
    congr 1
    refine List.filter_congr (fun c hc' => ?_)
    rw [hh c (hQ.lt c (List.mem_of_mem_drop hc'))]
  · have hxn := hQ.lt x (List.mem_of_mem_drop hx)
    rw [← hc x hxn, ← hh x hxn, ← hi x hxn]
    exact h2 x hx

/-- One step of the closure pass, at `x = Q[j - 1]` with parent `p`. -/
theorem closureState_step (hQ : TopDownOrder n r par Q) {S cnt has inR : ℕ → ℕ} {j : ℕ}
    (hj : 2 ≤ j) (hjn : j ≤ n) (hI : ClosureState Q par n S cnt has inR j) :
    let x := Q[j - 1]'(by rw [hQ.len]; omega)
    let p := par x
    ClosureState Q par n S
      (Function.update cnt p (cnt p + closureHas (S x) (cnt x)))
      (Function.update has x (closureHas (S x) (cnt x)))
      (Function.update inR x (closureIn (S x) (cnt x))) (j - 1) := by
  classical
  intro x p
  obtain ⟨hcnt, hval⟩ := hI
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
  set hx := closureHas (S x) (cnt x) with hhx
  have hrest : ∀ u, (Q.drop j).filter (fun c => decide (par c = u ∧
      Function.update has x hx c = 1)) =
      (Q.drop j).filter (fun c => decide (par c = u ∧ has c = 1)) := by
    intro u
    refine List.filter_congr (fun c hc => ?_)
    have hcx : c ≠ x := fun h => hx_not (h ▸ hc)
    rw [Function.update_of_ne hcx]
  refine ⟨fun u hu => ?_, fun y hy => ?_⟩
  · rw [drop_pred_eq (by omega) hjQ, List.filter_cons, hrest u, Function.update_self]
    by_cases hpu : p = u
    · subst hpu
      rw [Function.update_self, hcnt p hu]
      have hle := closureHas_le (S x) (cnt x)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
      · rw [← hhx] at *; simp [h]
      · rw [← hhx] at *; simp only [h, Bool.decide_and]
        rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨rfl, trivial⟩),
          List.length_cons]
    · rw [Function.update_of_ne (Ne.symm hpu), hcnt u hu]
      simp only [Bool.decide_and]
      rw [ite_eq_right (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact fun h => hpu h.1)]
  · rw [drop_pred_eq (by omega) hjQ, List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [Function.update_self, Function.update_self, Function.update_of_ne (Ne.symm hpx)]
      exact ⟨rfl, rfl⟩
    · have hyx : y ≠ x := fun h => hx_not (h ▸ hy)
      have hyp : y ≠ p := by
        intro h; apply hp_not; rw [drop_pred_eq (by omega) hjQ, ← h]
        exact List.mem_cons_of_mem _ hy
      rw [Function.update_of_ne hyx, Function.update_of_ne hyx, Function.update_of_ne hyp]
      exact hval y hy

lemma closureHas_eq_one {s c : ℕ} : closureHas s c = 1 ↔ 0 < s ∨ 1 ≤ c := by
  unfold closureHas; split_ifs with h <;> simp <;> omega

lemma closureIn_eq_one {s c : ℕ} : closureIn s c = 1 ↔ 0 < s ∨ 2 ≤ c := by
  unfold closureIn; split_ifs with h1 h2 <;> simp <;> omega

lemma mem_subtree_iff_child {T : MGraph} {r v y : ℕ} (hT : IsRootedTree T r) (hv : v ∈ T.V) :
    y ∈ subtree T r v ↔ y = v ∨ ∃ c ∈ childSet T r v, y ∈ subtree T r c := by
  constructor
  · intro hy
    by_cases hyv : y = v
    · exact Or.inl hyv
    · obtain ⟨c, ⟨hc, hyc⟩, -⟩ := mem_subtree_children_iff hT hv hy hyv
      exact Or.inr ⟨c, mem_childSet.mpr hc, hyc⟩
  · rintro (rfl | ⟨c, hc, hyc⟩)
    · exact mem_subtree_iff.mpr ⟨hv, isAncestor_refl T r y⟩
    · obtain ⟨-, -, -, -, -, hvc⟩ := childSet_facts hT hc
      have hy := mem_subtree_iff.mp hyc
      exact mem_subtree_iff.mpr ⟨hy.1, isAncestor_trans hT hy.1 hvc hy.2⟩

lemma card_subtree_child_lt {T : MGraph} {r v c : ℕ} (hT : IsRootedTree T r)
    (hc : c ∈ childSet T r v) : (subtree T r c).card < (subtree T r v).card := by
  obtain ⟨-, -, -, hcv, hv, -⟩ := childSet_facts hT hc
  have hsub := subtree_child_subset hT (mem_childSet.mp hc)
  have hv_mem : v ∈ subtree T r v := mem_subtree_iff.mpr ⟨hv, isAncestor_refl T r v⟩
  refine Finset.card_lt_card ⟨fun x hx => Finset.sdiff_subset (hsub hx), fun h => ?_⟩
  have := hsub (h hv_mem)
  simp at this

/-- The closure pass marks the LCA closure of the marked vertices. The root `r` is done after
the loop, with the same rule (`hroot`). -/
theorem closure_bridge {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {Q : List ℕ} {S cnt has inR : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hC : ClosureState Q par vList.length S cnt has inR 1)
    (hroot : inR r = closureIn (S r) (cnt r)) :
    ∀ v ∈ T₀.V, vtxFun vList inR v = 1 ↔
      v ∈ lcaClosure T₀ (vList.getD r 0) (T₀.V.filter (fun v => 0 < vtxFun vList S v)) := by
  classical
  set n := vList.length with hn_def
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  set Sset := T₀.V.filter (fun v => 0 < vtxFun vList S v) with hSset
  have hn : 0 < n := by omega
  have hparent : ∀ x < n, x ≠ r → parent T₀ (g r) (g x) = g (par x) := fun x hx hxr =>
    ((t0Rooted_spec hT.isForest hA hnd hR hr hx).2 hxr).1
  have hgV : ∀ x < n, g x ∈ T₀.V := fun x hx =>
    (hV _).mpr (by simp only [hg]; rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < n ∧ g (vList.idxOf v) = v := fun v hv =>
    ⟨List.idxOf_lt_length_of_mem ((hV v).mp hv), getD_idxOf ((hV v).mp hv)⟩
  -- the children of `g x` are the `g y` with `par y = x`
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
  -- `cnt` counts the children with `has = 1`
  have hcnt : ∀ v ∈ T₀.V, cnt (vList.idxOf v) =
      ((childSet T₀ (g r) v).filter (fun c => has (vList.idxOf c) = 1)).card := by
    intro v hv
    obtain ⟨hxn, hgx⟩ := hidx v hv
    set x := vList.idxOf v
    set l := (Q.drop 1).filter (fun c => decide (par c = x ∧ has c = 1)) with hl
    have hlnd : l.Nodup := (hQ.nodup.sublist (List.drop_sublist _ _)).filter _
    have hlt : ∀ y ∈ l, y < n := fun y hy =>
      hQ.lt y (List.mem_of_mem_drop (List.mem_filter.mp hy).1)
    rw [hC.1 x hxn, ← hl]
    have hmap : (l.map g).Nodup :=
      List.Nodup.map_on (fun a ha b hb hab => getD_inj hnd (hlt a ha) (hlt b hb) hab) hlnd
    rw [← List.length_map (f := g), ← List.toFinset_card_of_nodup hmap]
    congr 1
    ext c
    rw [List.mem_toFinset, List.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyn := hlt y hy
      obtain ⟨hyQ, hyd⟩ := List.mem_filter.mp hy
      rw [decide_eq_true_iff] at hyd
      have hyr := ((hQ.mem_drop_one hn).mp hyQ).2
      refine ⟨?_, by rw [idxOf_getD hnd hyn]; exact hyd.2⟩
      rw [← hgx]
      exact (hchild x hxn y hyn).mpr ⟨hyr, hyd.1⟩
    · rintro ⟨hc, hhas⟩
      obtain ⟨hcV, -⟩ := childSet_facts hT hc
      obtain ⟨hyn, hgy⟩ := hidx c hcV
      rw [← hgy, ← hgx] at hc
      obtain ⟨hyr, hpy⟩ := (hchild x hxn _ hyn).mp hc
      refine ⟨_, List.mem_filter.mpr ⟨(hQ.mem_drop_one hn).mpr ⟨hyn, hyr⟩, ?_⟩, hgy⟩
      rw [decide_eq_true_iff]
      exact ⟨hpy, hhas⟩
  have hidx_r : ∀ v ∈ T₀.V, vList.idxOf v ≠ r ↔ v ≠ g r := by
    intro v hv
    obtain ⟨hxn, hgx⟩ := hidx v hv
    constructor
    · intro h h'; exact h (getD_inj hnd hxn hr (hgx.trans h'))
    · intro h h'; exact h (by rw [← hgx, h'])
  -- `has` marks the vertices with a marked vertex below
  have hhas : ∀ k, ∀ v ∈ T₀.V, (subtree T₀ (g r) v).card ≤ k → v ≠ g r →
      (has (vList.idxOf v) = 1 ↔ ∃ y ∈ Sset, y ∈ subtree T₀ (g r) v) := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      have := Finset.card_pos.mpr ⟨v, mem_subtree_iff.mpr ⟨hv, isAncestor_refl T₀ (g r) v⟩⟩
      omega
    | succ k ih =>
      intro v hv hk hvr
      obtain ⟨hxn, hgx⟩ := hidx v hv
      have hxQ : vList.idxOf v ∈ Q.drop 1 := (hQ.mem_drop_one hn).mpr ⟨hxn, (hidx_r v hv).mpr hvr⟩
      rw [(hC.2 _ hxQ).1, closureHas_eq_one, hcnt v hv, Nat.one_le_iff_ne_zero, Ne,
        Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
      constructor
      · rintro (hS | ⟨c, hc⟩)
        · exact ⟨v, Finset.mem_filter.mpr ⟨hv, hS⟩, mem_subtree_iff.mpr ⟨hv, isAncestor_refl _ _ _⟩⟩
        · obtain ⟨hc, hhc⟩ := Finset.mem_filter.mp hc
          obtain ⟨hcV, hcr, -⟩ := childSet_facts hT hc
          obtain ⟨y, hy, hyc⟩ := (ih c hcV (by have := card_subtree_child_lt (r := g r) hT hc; omega) hcr).mp hhc
          exact ⟨y, hy, (mem_subtree_iff_child hT hv).mpr (Or.inr ⟨c, hc, hyc⟩)⟩
      · rintro ⟨y, hy, hyv⟩
        rcases (mem_subtree_iff_child hT hv).mp hyv with rfl | ⟨c, hc, hyc⟩
        · exact Or.inl (Finset.mem_filter.mp hy).2
        · obtain ⟨hcV, hcr, -⟩ := childSet_facts hT hc
          refine Or.inr ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩⟩
          exact (ih c hcV (by have := card_subtree_child_lt (r := g r) hT hc; omega) hcr).mpr ⟨y, hy, hyc⟩
  intro v hv
  obtain ⟨hxn, hgx⟩ := hidx v hv
  have hin : inR (vList.idxOf v) = closureIn (S (vList.idxOf v)) (cnt (vList.idxOf v)) := by
    by_cases hxr : vList.idxOf v = r
    · rw [hxr]; exact hroot
    · exact (hC.2 _ ((hQ.mem_drop_one hn).mpr ⟨hxn, hxr⟩)).2
  have hhasc : ∀ c ∈ childSet T₀ (g r) v,
      (has (vList.idxOf c) = 1 ↔ ∃ y ∈ Sset, y ∈ subtree T₀ (g r) c) := by
    intro c hc
    obtain ⟨hcV, hcr, -⟩ := childSet_facts hT hc
    exact hhas _ c hcV le_rfl hcr
  rw [vtxFun, hin, closureIn_eq_one, hcnt v hv, mem_lcaClosure_iff_children hT
    (Finset.filter_subset _ _) hv]
  have hvS : v ∈ Sset ↔ 0 < S (vList.idxOf v) := by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  rw [hvS]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    obtain ⟨ha, hha⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hhb⟩ := Finset.mem_filter.mp hb
    exact ⟨a, ha, b, hb, hab, (hhasc a ha).mp hha, (hhasc b hb).mp hhb⟩
  · rintro ⟨a, ha, b, hb, hab, hSa, hSb⟩
    exact Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, (hhasc a ha).mpr hSa⟩, b,
      Finset.mem_filter.mpr ⟨hb, (hhasc b hb).mpr hSb⟩, hab⟩

end MinCostFlow.LSF.Program

end
