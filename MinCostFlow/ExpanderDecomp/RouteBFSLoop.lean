module

public import MinCostFlow.ExpanderDecomp.RouteBFSBase
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith

/-!
# Invariants and main specification of local multi-source layered BFS

This file proves the layer-by-layer invariant (`BFSInv`), loop specification (`bfsLoop_spec`),
and main specification (`bfsLayers_spec`) for the local multi-source layered BFS defined in
`RouteBFSBase.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Invariants and specification of `bfsLoop` and `bfsLayers` -/

/-- State invariant maintained across layers of `bfsLoop`. -/
private structure BFSInv (G : Graph) (X V S stopSet : Finset ℕ)
    (curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
    (vis : Finset ℕ) (dist : ℕ → Option ℕ) : Prop where
  vis_sub : vis ⊆ V
  frontier_nd : frontier.Nodup
  frontier_ne : frontier ≠ []
  revLayers_len : revLayers.length = curDist + 1
  revLayers_head : revLayers.head? = some frontier
  layers_nd : ∀ L ∈ revLayers, L.Nodup
  layers_mem : ∀ r (hr : r < revLayers.length) v,
    v ∈ revLayers.reverse[r]'(by simp [hr]) ↔ dist v = some r
  dist_vis : ∀ v, v ∈ vis ↔ ∃ r ≤ curDist, dist v = some r
  dist_none : ∀ v, v ∉ vis → dist v = none
  dist_zero : ∀ v, dist v = some 0 ↔ v ∈ S ∩ V
  dist_walk : ∀ v r, dist v = some r → ∃ s ∈ S ∩ V, ∃ es, es.length = r ∧ IsEdgeWalkIn G V s v es
  closed_lt : ∀ u w e r, r < curDist → dist u = some r → (w, e) ∈ adjOf G X u → w ∈ V →
    ∃ r' ≤ r + 1, dist w = some r'
  no_stop : ∀ v ∈ vis, v ∉ stopSet

private lemma revLayers_reverse_getElem_last (revLayers : List (List ℕ)) (frontier : List ℕ)
    (curDist : ℕ) (hlen : revLayers.length = curDist + 1) (hhead : revLayers.head? = some frontier) :
    revLayers.reverse[curDist]'(by simp [hlen]) = frontier := by
  cases revLayers with
  | nil => simp at hhead
  | cons hd tl =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.reverse_cons]
    rw [List.getElem_append_right (by simp [hlen])]
    simp [hlen]

private lemma bfsInv_frontier_iff {G : Graph} {X V S stopSet : Finset ℕ}
    {curDist : ℕ} {frontier : List ℕ} {revLayers : List (List ℕ)}
    {vis : Finset ℕ} {dist : ℕ → Option ℕ}
    (hinv : BFSInv G X V S stopSet curDist frontier revLayers vis dist) (v : ℕ) :
    v ∈ frontier ↔ dist v = some curDist := by
  have hlen := hinv.revLayers_len
  have hlast := revLayers_reverse_getElem_last revLayers frontier curDist
    hlen hinv.revLayers_head
  have hm := hinv.layers_mem curDist (by omega) v
  rw [hlast] at hm
  exact hm

/-- Specification of `bfsLoop` given `BFSInv`. -/
private theorem bfsLoop_spec (G : Graph) (X V S stopSet : Finset ℕ) (_hVX : V ⊆ X)
    (rem curDist : ℕ) (frontier : List ℕ) (revLayers : List (List ℕ))
    (vis : Finset ℕ) (dist : ℕ → Option ℕ) (cost : ℕ)
    (hinv : BFSInv G X V S stopSet curDist frontier revLayers vis dist) :
    let res := bfsLoop (adjOf G X) V stopSet rem curDist frontier revLayers vis dist cost
    res.visited ⊆ V ∧
    res.layers.length = res.maxReached + 1 ∧
    curDist ≤ res.maxReached ∧ res.maxReached ≤ curDist + rem ∧
    (∀ L ∈ res.layers, L.Nodup) ∧
    (∀ r (hr : r < res.layers.length) v, v ∈ res.layers[r]'hr ↔ res.dist v = some r) ∧
    (∀ v, v ∈ res.visited ↔ ∃ r ≤ res.maxReached, res.dist v = some r) ∧
    (∀ v, v ∉ res.visited → res.dist v = none) ∧
    (∀ v, res.dist v = some 0 ↔ v ∈ S ∩ V) ∧
    (∀ v r, res.dist v = some r → ∃ s ∈ S ∩ V, ∃ es, es.length = r ∧ IsEdgeWalkIn G V s v es) ∧
    (∀ u w e r, r < res.maxReached → res.dist u = some r → (w, e) ∈ adjOf G X u → w ∈ V →
      ∃ r' ≤ r + 1, res.dist w = some r') ∧
    (res.exhausted = true → ∀ u ∈ res.visited, ∀ w e, (w, e) ∈ adjOf G X u → w ∈ V →
      w ∈ res.visited) ∧
    (res.hitStop = true → res.exhausted = false ∧
      (∃ t ∈ stopSet ∩ V, res.dist t = some res.maxReached) ∧
      (∀ t ∈ stopSet ∩ V, ∀ r < res.maxReached, res.dist t ≠ some r)) ∧
    (res.hitStop = false →
      (∀ t ∈ stopSet ∩ V, t ∉ res.visited) ∧
      (res.exhausted = true ∨ res.maxReached = curDist + rem)) ∧
    res.cost ≤ cost + (frontier.length + (∑ u ∈ frontier.toFinset, (adjOf G X u).length) + 1) +
      3 * (V.card - vis.card) + (∑ u ∈ V \ vis, (adjOf G X u).length) := by
  induction rem generalizing curDist frontier revLayers vis dist cost with
  | zero =>
    simp only [bfsLoop, Nat.add_zero]
    refine ⟨hinv.vis_sub, by simp [hinv.revLayers_len], le_refl _, le_refl _,
      fun L hL => hinv.layers_nd L (List.mem_reverse.mp hL),
      fun r hr v => hinv.layers_mem r (by simpa using hr) v,
      hinv.dist_vis, hinv.dist_none, hinv.dist_zero, hinv.dist_walk, hinv.closed_lt,
      by simp, by simp, ?_, by omega⟩
    exact fun _ => ⟨fun t ht hvis => hinv.no_stop t hvis (Finset.mem_inter.mp ht).1, Or.inr trivial⟩
  | succ rem ih =>
    simp only [bfsLoop]
    have hnd0 : ([] : List ℕ).Nodup := List.nodup_nil
    have hsub0 : ∀ x ∈ ([] : List ℕ), x ∈ vis := by simp
    have hdist_vis : ∀ x ∈ vis, dist x ≠ none := by
      intro x hx
      obtain ⟨r, _, hr⟩ := (hinv.dist_vis x).mp hx
      simp [hr]
    have hdist_nxt0 : ∀ x ∈ ([] : List ℕ), dist x = some (curDist + 1) := by simp
    have hexp := bfsExpandFrontier_spec (adjOf G X) V (curDist + 1) frontier [] vis dist
      hinv.vis_sub hnd0 hsub0 hdist_vis hinv.dist_none hdist_nxt0
    set r := bfsExpandFrontier (adjOf G X) V (curDist + 1) frontier [] vis dist with hr_def
    rcases hexp with ⟨hcexp, hvis_sub', hvis'V, hnxt_nd, hnxt_mem, hdist_eq, hdist_new, hdist_none',
      hnxt_from, hnxt_cov⟩
    have hsum_front : (frontier.map fun u => (adjOf G X u).length).sum =
        ∑ u ∈ frontier.toFinset, (adjOf G X u).length := by
      rw [← List.sum_toFinset _ hinv.frontier_nd]
    have hcexp' : r.2.2.2 = frontier.length + ∑ u ∈ frontier.toFinset, (adjOf G X u).length := by
      rw [hcexp, hsum_front]
    -- Case 1: next frontier is empty -> exhausted!
    by_cases hempty : r.1.isEmpty = true
    · simp only [← hr_def, hempty, ↓reduceIte]
      have hnxt_nil : r.1 = [] := List.isEmpty_iff.mp hempty
      have hvis_eq : r.2.1 = vis := by
        ext x
        constructor
        · intro hx
          by_contra hxnot
          have hxmem : x ∈ r.1 := (hnxt_mem x).mpr (Or.inr ⟨hx, hxnot⟩)
          rw [hnxt_nil] at hxmem
          exact List.not_mem_nil hxmem
        · intro hx; exact hvis_sub' hx
      have hdist_all : r.2.2.1 = dist := by
        funext x
        by_cases hx : x ∈ vis
        · exact hdist_eq x hx
        · rw [hdist_none' x (hvis_eq ▸ hx), hinv.dist_none x hx]
      have hdist_pt : ∀ v, r.2.2.1 v = dist v := fun v => congrFun hdist_all v
      refine ⟨hvis'V, by simp [hinv.revLayers_len], le_refl _, by omega,
        fun L hL => hinv.layers_nd L (List.mem_reverse.mp hL),
        fun r' hr' v => by rw [hdist_pt v]; exact hinv.layers_mem r' (by simpa using hr') v,
        fun v => by rw [hvis_eq, hdist_pt v]; exact hinv.dist_vis v,
        fun v hv => by rw [hdist_pt v]; exact hinv.dist_none v (by rwa [← hvis_eq]),
        fun v => by rw [hdist_pt v]; exact hinv.dist_zero v,
        fun v r' h => by rw [hdist_pt v] at h; exact hinv.dist_walk v r' h,
        fun u w e r' hr' h => by
          rw [hdist_pt u] at h
          simp_rw [hdist_pt w]
          exact hinv.closed_lt u w e r' hr' h,
        ?_, (fun h => by cases h), ?_, ?_⟩
      · intro _ u hu w e he hwV
        rw [hvis_eq] at hu ⊢
        obtain ⟨ru, hru_le, hru⟩ := (hinv.dist_vis u).mp hu
        by_cases hlt : ru < curDist
        · obtain ⟨rw', hrw'_le, hrw'⟩ := hinv.closed_lt u w e ru hlt hru he hwV
          exact (hinv.dist_vis w).mpr ⟨rw', by omega, hrw'⟩
        · have hru_eq : ru = curDist := by omega
          have hu_front : u ∈ frontier := (bfsInv_frontier_iff hinv u).mpr (hru_eq ▸ hru)
          have hw_vis' : w ∈ r.2.1 := hnxt_cov u hu_front w e he hwV
          exact hvis_eq ▸ hw_vis'
      · exact fun _ => ⟨fun t ht hvis => hinv.no_stop t (by rwa [← hvis_eq]) (Finset.mem_inter.mp ht).1,
          Or.inl trivial⟩
      · rw [hcexp']; omega
    · -- Case 2: next frontier is nonempty!
      simp only [← hr_def, hempty, Bool.false_eq_true, ↓reduceIte]
      have hnxt_ne : r.1 ≠ [] := fun h => hempty (List.isEmpty_iff.mpr h)
      have hnxt_pos : 1 ≤ r.1.length := List.length_pos_iff.mpr hnxt_ne
      have hnxt_disj : Disjoint vis r.1.toFinset := by
        rw [Finset.disjoint_left]
        intro x hxvis hxnxt
        rw [List.mem_toFinset] at hxnxt
        rcases (hnxt_mem x).mp hxnxt with hnil | ⟨_, hxnot⟩
        · exact List.not_mem_nil hnil
        · exact hxnot hxvis
      have hvis'_eq : r.2.1 = vis ∪ r.1.toFinset := by
        ext x
        simp only [Finset.mem_union, List.mem_toFinset, hnxt_mem x, List.not_mem_nil, false_or]
        constructor
        · intro hx
          by_cases hv : x ∈ vis
          · exact Or.inl hv
          · exact Or.inr ⟨hx, hv⟩
        · rintro (hv | ⟨hx, _⟩)
          · exact hvis_sub' hv
          · exact hx
      have hcard_vis' : r.2.1.card = vis.card + r.1.length := by
        rw [hvis'_eq, Finset.card_union_of_disjoint hnxt_disj, List.toFinset_card_of_nodup hnxt_nd]
      have hcard_le : r.2.1.card ≤ V.card := Finset.card_le_card hvis'V
      have hsum_sdiff : ∑ u ∈ V \ vis, (adjOf G X u).length =
          ∑ u ∈ V \ r.2.1, (adjOf G X u).length + ∑ u ∈ r.1.toFinset, (adjOf G X u).length := by
        have hpart : V \ vis = (V \ r.2.1) ∪ r.1.toFinset := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union, hvis'_eq, not_or]
          constructor
          · rintro ⟨hxV, hxnot⟩
            by_cases hx1 : x ∈ r.1.toFinset
            · exact Or.inr hx1
            · exact Or.inl ⟨hxV, hxnot, hx1⟩
          · rintro (⟨hxV, hxnot, _⟩ | hx1)
            · exact ⟨hxV, hxnot⟩
            · exact ⟨hvis'V (hvis'_eq ▸ Finset.mem_union_right _ hx1),
                Finset.disjoint_right.mp hnxt_disj hx1⟩
        have hd : Disjoint (V \ r.2.1) r.1.toFinset := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rw [Finset.mem_sdiff] at hx1
          exact hx1.2 (hvis'_eq ▸ Finset.mem_union_right _ hx2)
        rw [hpart, Finset.sum_union hd]
      -- Build the shared facts about `(r.1 :: revLayers)`, `r.2.1`, `r.2.2.1`:
      have hlayers_mem' : ∀ r' (hr' : r' < (r.1 :: revLayers).length) v,
          v ∈ (r.1 :: revLayers).reverse[r']'(by simpa using hr') ↔ r.2.2.1 v = some r' := by
        intro r' hr' v
        have hlen_rev : revLayers.length = curDist + 1 := hinv.revLayers_len
        have hr'_lt : r' < curDist + 2 := by simp only [List.length_cons, hlen_rev] at hr'; omega
        simp only [List.reverse_cons]
        by_cases hlt : r' < curDist + 1
        · rw [List.getElem_append_left (by simp [hlen_rev]; omega)]
          rw [hinv.layers_mem r' (by omega) v]
          constructor
          · intro hdv
            have hvvis : v ∈ vis := (hinv.dist_vis v).mpr ⟨r', by omega, hdv⟩
            rw [hdist_eq v hvvis, hdv]
          · intro hdv'
            by_cases hvvis : v ∈ vis
            · rwa [hdist_eq v hvvis] at hdv'
            · by_cases hvvis' : v ∈ r.2.1
              · rw [hdist_new v hvvis' hvvis] at hdv'
                have : curDist + 1 = r' := Option.some.inj hdv'
                omega
              · rw [hdist_none' v hvvis'] at hdv'
                cases hdv'
        · have hr'_eq : r' = curDist + 1 := by omega
          subst hr'_eq
          rw [List.getElem_append_right (by simp [hlen_rev])]
          simp only [List.length_reverse, hlen_rev, Nat.sub_self, List.getElem_cons_zero]
          rw [hnxt_mem v]
          simp only [List.not_mem_nil, false_or]
          constructor
          · rintro ⟨hv1, hv2⟩
            exact hdist_new v hv1 hv2
          · intro hdv'
            by_cases hvvis : v ∈ vis
            · rw [hdist_eq v hvvis] at hdv'
              obtain ⟨r0, hr0, hdv0⟩ := (hinv.dist_vis v).mp hvvis
              rw [hdv0] at hdv'
              have : r0 = curDist + 1 := Option.some.inj hdv'
              omega
            · by_cases hvvis' : v ∈ r.2.1
              · exact ⟨hvvis', hvvis⟩
              · rw [hdist_none' v hvvis'] at hdv'
                cases hdv'
      have hdist_vis' : ∀ v, v ∈ r.2.1 ↔ ∃ r' ≤ curDist + 1, r.2.2.1 v = some r' := by
        intro v
        constructor
        · intro hv
          by_cases hv0 : v ∈ vis
          · obtain ⟨r0, hr0, hdv0⟩ := (hinv.dist_vis v).mp hv0
            exact ⟨r0, by omega, by rw [hdist_eq v hv0, hdv0]⟩
          · exact ⟨curDist + 1, le_refl _, hdist_new v hv hv0⟩
        · rintro ⟨r', _, hdv'⟩
          by_contra hvnot
          rw [hdist_none' v hvnot] at hdv'
          cases hdv'
      have hdist_zero' : ∀ v, r.2.2.1 v = some 0 ↔ v ∈ S ∩ V := by
        intro v
        rw [← hinv.dist_zero v]
        constructor
        · intro hdv'
          by_cases hv0 : v ∈ vis
          · rwa [hdist_eq v hv0] at hdv'
          · by_cases hv1 : v ∈ r.2.1
            · rw [hdist_new v hv1 hv0] at hdv'
              have : curDist + 1 = 0 := Option.some.inj hdv'
              omega
            · rw [hdist_none' v hv1] at hdv'
              cases hdv'
        · intro hdv
          have hv0 : v ∈ vis := (hinv.dist_vis v).mpr ⟨0, Nat.zero_le _, hdv⟩
          rw [hdist_eq v hv0, hdv]
      have hdist_walk' : ∀ v r', r.2.2.1 v = some r' →
          ∃ s ∈ S ∩ V, ∃ es, es.length = r' ∧ IsEdgeWalkIn G V s v es := by
        intro v r' hdv'
        by_cases hv0 : v ∈ vis
        · rw [hdist_eq v hv0] at hdv'
          exact hinv.dist_walk v r' hdv'
        · have hv1 : v ∈ r.2.1 := by
            by_contra hvnot
            rw [hdist_none' v hvnot] at hdv'
            cases hdv'
          rw [hdist_new v hv1 hv0] at hdv'
          have hr'_eq : curDist + 1 = r' := Option.some.inj hdv'
          subst hr'_eq
          obtain ⟨u, hu_front, e, he⟩ := hnxt_from v hv1 hv0
          have hu_dist : dist u = some curDist := (bfsInv_frontier_iff hinv u).mp hu_front
          obtain ⟨s, hs, es, hlen, hwalk⟩ := hinv.dist_walk u curDist hu_dist
          have huV : u ∈ V := hinv.vis_sub ((hinv.dist_vis u).mpr ⟨curDist, le_refl _, hu_dist⟩)
          have hvV : v ∈ V := hvis'V hv1
          have hstep : IsEdgeWalkIn G V u v [e] :=
            IsEdgeWalkIn.cons_of_adj he huV hvV (IsEdgeWalkIn.nil G V v)
          exact ⟨s, hs, es ++ [e], by simp [hlen], hwalk.append hstep⟩
      have hclosed_lt' : ∀ u w e r', r' < curDist + 1 → r.2.2.1 u = some r' →
          (w, e) ∈ adjOf G X u → w ∈ V → ∃ r'' ≤ r' + 1, r.2.2.1 w = some r'' := by
        intro u w e r' hr' hdu' he hwV
        have hu0 : u ∈ vis := by
          by_contra hunot
          by_cases hu1 : u ∈ r.2.1
          · rw [hdist_new u hu1 hunot] at hdu'
            have : curDist + 1 = r' := Option.some.inj hdu'
            omega
          · rw [hdist_none' u hu1] at hdu'
            cases hdu'
        rw [hdist_eq u hu0] at hdu'
        by_cases hlt : r' < curDist
        · obtain ⟨r'', hr''_le, hdw⟩ := hinv.closed_lt u w e r' hlt hdu' he hwV
          have hw0 : w ∈ vis := (hinv.dist_vis w).mpr ⟨r'', by omega, hdw⟩
          exact ⟨r'', hr''_le, by rw [hdist_eq w hw0, hdw]⟩
        · have hr'_eq : r' = curDist := by omega
          subst hr'_eq
          have hu_front : u ∈ frontier := (bfsInv_frontier_iff hinv u).mpr hdu'
          have hw1 : w ∈ r.2.1 := hnxt_cov u hu_front w e he hwV
          obtain ⟨r'', hr''_le, hdw'⟩ := (hdist_vis' w).mp hw1
          exact ⟨r'', hr''_le, hdw'⟩
      -- Split on whether `nxt` hit `stopSet`:
      by_cases hhit : (r.1.any fun v => decide (v ∈ stopSet)) = true
      · -- Case 2a: hit `stopSet` at `curDist + 1`!
        simp only [hhit, ↓reduceIte]
        refine ⟨hvis'V, by simp [hinv.revLayers_len], by omega, by omega, ?_, ?_, hdist_vis',
          hdist_none', hdist_zero', hdist_walk', hclosed_lt', (fun h => by cases h), ?_,
          (fun h => by cases h), ?_⟩
        · intro L hL
          rw [List.mem_reverse] at hL
          rcases List.mem_cons.mp hL with rfl | hL
          · exact hnxt_nd
          · exact hinv.layers_nd L hL
        · intro r' hr' v
          exact hlayers_mem' r' (by simpa using hr') v
        · intro _
          refine ⟨trivial, ?_, ?_⟩
          · rw [List.any_eq_true] at hhit
            obtain ⟨t, ht_nxt, ht_stop⟩ := hhit
            rw [decide_eq_true_eq] at ht_stop
            rcases (hnxt_mem t).mp ht_nxt with hnil | ⟨ht1, ht2⟩
            · exact absurd hnil (List.not_mem_nil)
            · exact ⟨t, Finset.mem_inter.mpr ⟨ht_stop, hvis'V ht1⟩, hdist_new t ht1 ht2⟩
          · intro t ht r' hr' hdt'
            have ht0 : t ∈ vis := by
              by_contra htnot
              by_cases ht1 : t ∈ r.2.1
              · rw [hdist_new t ht1 htnot] at hdt'
                have : curDist + 1 = r' := Option.some.inj hdt'
                omega
              · rw [hdist_none' t ht1] at hdt'
                cases hdt'
            exact hinv.no_stop t ht0 (Finset.mem_inter.mp ht).1
        · rw [hcexp']
          omega
      · -- Case 2b: did not hit `stopSet`; recurse!
        simp only [hhit, Bool.false_eq_true, ↓reduceIte]
        have hno_stop' : ∀ v ∈ r.2.1, v ∉ stopSet := by
          intro v hv hvstop
          by_cases hv0 : v ∈ vis
          · exact hinv.no_stop v hv0 hvstop
          · have hvnxt : v ∈ r.1 := (hnxt_mem v).mpr (Or.inr ⟨hv, hv0⟩)
            have htrue : (r.1.any fun x => decide (x ∈ stopSet)) = true :=
              List.any_eq_true.mpr ⟨v, hvnxt, decide_eq_true_eq.mpr hvstop⟩
            exact hhit htrue
        have hinv' : BFSInv G X V S stopSet (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1 :=
          { vis_sub := hvis'V
            frontier_nd := hnxt_nd
            frontier_ne := hnxt_ne
            revLayers_len := by simp [hinv.revLayers_len]
            revLayers_head := rfl
            layers_nd := fun L hL => by
              rcases List.mem_cons.mp hL with rfl | hL
              · exact hnxt_nd
              · exact hinv.layers_nd L hL
            layers_mem := hlayers_mem'
            dist_vis := hdist_vis'
            dist_none := hdist_none'
            dist_zero := hdist_zero'
            dist_walk := hdist_walk'
            closed_lt := hclosed_lt'
            no_stop := hno_stop' }
        have hrec := ih (curDist + 1) r.1 (r.1 :: revLayers) r.2.1 r.2.2.1
          (cost + r.2.2.2 + 1 + r.1.length) hinv'
        rcases hrec with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hcost⟩
        refine ⟨h1, h2, by omega, by omega, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_, ?_⟩
        · intro hf
          obtain ⟨ha, hb⟩ := h14 hf
          refine ⟨ha, ?_⟩
          rcases hb with hb | hb
          · exact Or.inl hb
          · exact Or.inr (by omega)
        · omega

/-- Complete specification of `bfsLayers` on `G[V]` (`V ⊆ X`). -/
theorem bfsLayers_spec (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ) :
    let res := bfsLayers (adjOf G X) V S maxDist stopSet
    res.visited ⊆ V ∧
    res.maxReached ≤ maxDist ∧
    (∀ L ∈ res.layers, L.Nodup) ∧
    (∀ r (hr : r < res.layers.length) v, v ∈ res.layers[r]'hr ↔ res.dist v = some r) ∧
    (∀ v, v ∈ res.visited ↔ ∃ r ≤ res.maxReached, res.dist v = some r) ∧
    (∀ v, v ∉ res.visited → res.dist v = none) ∧
    (∀ v, res.dist v = some 0 ↔ v ∈ S ∩ V) ∧
    (∀ v r, res.dist v = some r → ∃ s ∈ S ∩ V, ∃ es, es.length = r ∧ IsEdgeWalkIn G V s v es) ∧
    (∀ u w e r, r < res.maxReached → res.dist u = some r → (w, e) ∈ adjOf G X u → w ∈ V →
      ∃ r' ≤ r + 1, res.dist w = some r') ∧
    (res.exhausted = true → ∀ u ∈ res.visited, ∀ w e, (w, e) ∈ adjOf G X u → w ∈ V →
      w ∈ res.visited) ∧
    ((S ∩ V).Nonempty → res.layers.length = res.maxReached + 1) ∧
    (res.hitStop = true → res.exhausted = false ∧
      (∃ t ∈ stopSet ∩ V, res.dist t = some res.maxReached) ∧
      (∀ t ∈ stopSet ∩ V, ∀ r < res.maxReached, res.dist t ≠ some r)) ∧
    (res.hitStop = false →
      (∀ t ∈ stopSet ∩ V, t ∉ res.visited) ∧
      (res.exhausted = true ∨ res.maxReached = maxDist)) ∧
    res.cost ≤ 3 * X.card + 2 * (G.inside X).length + 2 := by
  unfold bfsLayers
  dsimp only
  set S0 := S ∩ V
  set initLayer := S0.sort (· ≤ ·)
  have hS0V : S0 ⊆ V := Finset.inter_subset_right
  have hS0_len : initLayer.length = S0.card := Finset.length_sort _
  have hS0_nd : initLayer.Nodup := Finset.sort_nodup _ _
  have hS0_mem : ∀ v, v ∈ initLayer ↔ v ∈ S0 := fun v => Finset.mem_sort _
  by_cases hempty : initLayer.isEmpty = true
  · simp only [hempty, ↓reduceIte]
    have hnil : initLayer = [] := List.isEmpty_iff.mp hempty
    have hS0_empty : S0 = ∅ := by
      ext v
      rw [← hS0_mem v, hnil]
      simp
    refine ⟨Finset.empty_subset _, Nat.zero_le _, by simp, by simp, by simp, by simp,
      by simp [hS0_empty], by simp, by simp, by simp,
      fun hne => absurd (hS0_empty ▸ hne) Finset.not_nonempty_empty,
      by simp, fun _ => ⟨by simp, Or.inl trivial⟩, by omega⟩
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte]
    by_cases hhit0 : (initLayer.any fun v => decide (v ∈ stopSet)) = true
    · simp only [hhit0, ↓reduceIte]
      have hS0_le : S0.card ≤ X.card := Finset.card_le_card (le_trans hS0V hVX)
      refine ⟨hS0V, Nat.zero_le _,
        fun L hL => by rw [List.mem_singleton] at hL; exact hL ▸ hS0_nd,
        ?_, ?_, ?_, ?_, ?_, by omega, by simp, fun _ => rfl, ?_, by simp, ?_⟩
      · intro r hr v
        simp only [List.length_singleton, Nat.lt_one_iff] at hr
        subst hr
        simp [hS0_mem v]
      · intro v
        by_cases hv : v ∈ S0 <;> simp [hv]
      · intro v hv; simp [hv]
      · intro v; by_cases hv : v ∈ S0 <;> simp [hv, S0]
      · intro v r hr
        by_cases hv : v ∈ S0
        · simp only [hv, ↓reduceIte, Option.some.injEq] at hr
          subst hr
          exact ⟨v, hv, [], rfl, IsEdgeWalkIn.nil G V v⟩
        · simp [hv] at hr
      · intro _
        refine ⟨trivial, ?_, by omega⟩
        rw [List.any_eq_true] at hhit0
        obtain ⟨t, ht_in, ht_stop⟩ := hhit0
        rw [decide_eq_true_eq] at ht_stop
        rw [hS0_mem] at ht_in
        exact ⟨t, Finset.mem_inter.mpr ⟨ht_stop, hS0V ht_in⟩, by simp [ht_in]⟩
      · rw [hS0_len]; omega
    · simp only [hhit0, Bool.false_eq_true, ↓reduceIte]
      have hne : initLayer ≠ [] := fun h => hempty (List.isEmpty_iff.mpr h)
      have hinv0 : BFSInv G X V S stopSet 0 initLayer [initLayer] S0
          (fun v => if v ∈ S0 then some 0 else none) :=
        { vis_sub := hS0V
          frontier_nd := hS0_nd
          frontier_ne := hne
          revLayers_len := rfl
          revLayers_head := rfl
          layers_nd := fun L hL => by
            simp only [List.mem_singleton] at hL
            exact hL ▸ hS0_nd
          layers_mem := fun r hr v => by
            simp only [List.length_singleton, Nat.lt_one_iff] at hr
            subst hr
            simp [hS0_mem v]
          dist_vis := fun v => by by_cases hv : v ∈ S0 <;> simp [hv]
          dist_none := fun v hv => by simp [hv]
          dist_zero := fun v => by by_cases hv : v ∈ S0 <;> simp [hv, S0]
          dist_walk := fun v r hr => by
            by_cases hv : v ∈ S0
            · simp only [hv, ↓reduceIte, Option.some.injEq] at hr
              subst hr
              exact ⟨v, hv, [], rfl, IsEdgeWalkIn.nil G V v⟩
            · simp [hv] at hr
          closed_lt := fun _ _ _ _ hlt => by omega
          no_stop := fun v hv hvstop => by
            have htrue : (initLayer.any fun x => decide (x ∈ stopSet)) = true :=
              List.any_eq_true.mpr ⟨v, (hS0_mem v).mpr hv, decide_eq_true_eq.mpr hvstop⟩
            exact hhit0 htrue }
      have hloop := bfsLoop_spec G X V S stopSet hVX maxDist 0 initLayer [initLayer] S0
        (fun v => if v ∈ S0 then some 0 else none) (initLayer.length + initLayer.length + 1) hinv0
      rcases hloop with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hcost⟩
      have htoFinset : initLayer.toFinset = S0 := by
        ext v; simp [hS0_mem]
      have hsum_V : ∑ u ∈ S0, (adjOf G X u).length + ∑ u ∈ V \ S0, (adjOf G X u).length =
          ∑ u ∈ V, (adjOf G X u).length := by
        rw [← Finset.sum_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hS0V]
      have hsum_le : ∑ u ∈ V, (adjOf G X u).length ≤ 2 * (G.inside X).length :=
        sum_adjOf_length_le G hVX
      have hV_le : V.card ≤ X.card := Finset.card_le_card hVX
      have hS0_le : S0.card ≤ V.card := Finset.card_le_card hS0V
      rw [htoFinset] at hcost
      refine ⟨h1, by omega, h5, h6, h7, h8, h9, h10, h11, h12, fun _ => h2, h13, ?_, ?_⟩
      · intro hf
        obtain ⟨ha, hb⟩ := h14 hf
        refine ⟨ha, ?_⟩
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr (by omega)
      · omega


end MinCostFlow.ExpanderDecomp
