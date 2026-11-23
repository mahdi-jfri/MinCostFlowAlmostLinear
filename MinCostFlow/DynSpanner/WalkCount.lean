module

public import MinCostFlow.DynSpanner.Correctness

import Mathlib.Tactic.Linarith

/-!
# Edge-occurrence monotonicity (`D40`) for Dynamic Spanner re-embedding

Notice that while `walkEdges` (Item 3 in `reembed_step_spec` / `reembed_batch_spec`) only tracks
the set of edges occurring along `piTotal`, passing length upper bounds `w^𝒮` via occurrence counts
(`walkCount`, `D40`) requires the stronger **multiplicity** monotonicity along non-re-embedded
edges: across a single `DynSpanner.step` or batch `DynSpanner.update`, for every surviving graph edge
`eG ∈ res.state.G.E` and every spanner edge `eH ∉ res.D`, the number of times `eH` occurs along
`piTotal res.state eG` is at most the number of times it occurred along `piTotal st eG`.

Why it holds:
* When `chooseLevel = 0`, `res.D = res.state.H.E`, so `eH ∉ res.D` implies `eH` occurs `0` times.
* When `chooseLevel = j > 0` and `eG ∉ E_aff`, `piTotal res.state eG = pi_r eG` is a prefix of
  `piTotal st eG` by `prefix_suffix_preserve_backward`.
* When `chooseLevel = j > 0` and `eG ∈ E_aff`, `piTotal res.state eG = p₁ ++ embMid eG ++ walkRev q₂`,
  where `embMid eG` uses only edges in `res.D` (so `0` occurrences of `eH`), while `p₁ <+: piTotal st eG`,
  `q₂ <+: walkRev (piTotal st eG)`, and the first-hit stopping vertices of `p₁` and `q₂` prevent
  `p₁` and `walkRev q₂` from overlapping inside `piTotal st eG` (`p₁.length + q₂.length ≤ (piTotal st eG).length`).
-/

namespace MinCostFlow.DynSpanner

section WalkCountMono

@[expose] public section

private lemma countP_walkRev (P : List (ℕ × Bool)) (eH : ℕ) :
    (walkRev P).countP (fun x => decide (x.1 = eH)) =
      P.countP (fun x => decide (x.1 = eH)) := by
  simp [walkRev, List.countP_reverse, List.countP_map, Function.comp_def]

private lemma countP_eq_zero_of_not_mem_walkEdges {P : List (ℕ × Bool)} {eH : ℕ}
    (h : eH ∉ walkEdges P) : P.countP (fun x => decide (x.1 = eH)) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx hdec
  apply h
  rw [mem_walkEdges_iff]
  exact ⟨x, hx, of_decide_eq_true hdec⟩

private lemma walkRev_prefix_to_suffix {q P : List (ℕ × Bool)}
    (hq : q <+: walkRev P) : walkRev q <:+ P := by
  obtain ⟨t, ht⟩ := hq
  have hrev := congrArg walkRev ht
  rw [walkRev_walkRev, walkRev_append] at hrev
  exact ⟨walkRev t, hrev⟩

private lemma countP_prefix_append_suffix_le {α : Type*} (p q mid L : List α) (f : α → Bool)
    (hp : p <+: L) (hq : q <:+ L) (hlen : p.length + q.length ≤ L.length)
    (hmid : mid.countP f = 0) :
    (p ++ mid ++ q).countP f ≤ L.countP f := by
  obtain ⟨rest, hrest⟩ := hp
  have hrest_len : p.length + rest.length = L.length := by
    simpa [List.length_append] using congrArg List.length hrest
  have hq_rest : q <:+ rest := by
    obtain ⟨t, ht⟩ := hq
    have ht_len : t.length + q.length = L.length := by
      simpa [List.length_append] using congrArg List.length ht
    have hq_le : q.length ≤ rest.length := by omega
    have hdrop : L.drop (p.length + (rest.length - q.length)) = q := by
      have hlen' : t.length = p.length + (rest.length - q.length) := by omega
      rw [← ht, ← hlen']
      exact List.drop_left
    rw [← hrest, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
      List.nil_append, Nat.add_sub_cancel_left] at hdrop
    have hta := List.take_append_drop (rest.length - q.length) rest
    rw [hdrop] at hta
    exact ⟨rest.take (rest.length - q.length), hta⟩
  obtain ⟨u, hu⟩ := hq_rest
  rw [← hrest, ← hu]
  simp only [List.countP_append, hmid]
  omega

private lemma prefixWalk_pair_eq_of_disjoint (H : MGraph) (S : Finset ℕ) :
    ∀ {a b : ℕ} (w : List (ℕ × Bool)), H.IsWalk a b w →
      Disjoint (H.walkVertices a w).toFinset S →
      prefixWalk H a w S = (b, w)
  | a, _, [], .nil _, hdisj => by
    have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
    simp [prefixWalk, haS]
  | a, _, x :: w', .cons _ _ hrest, hdisj => by
    have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
    have hdisj' : Disjoint (H.walkVertices (H.dst x) w').toFinset S := by
      rw [Finset.disjoint_left]
      intro z hz
      have hz' : z ∈ H.walkVertices (H.dst x) w' := List.mem_toFinset.mp hz
      have hz_mem : z ∈ H.walkVertices a (x :: w') := by
        simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
        exact Or.inr (by simpa [MGraph.walkVertices] using hz')
      exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr hz_mem)
    have ih := prefixWalk_pair_eq_of_disjoint H S w' hrest hdisj'
    simp [prefixWalk, haS, ih]

private lemma prefixWalk_dropLast_not_mem (H : MGraph) (S : Finset ℕ) :
    ∀ (a : ℕ) (w : List (ℕ × Bool)),
      ∀ z ∈ (H.walkVertices a (prefixWalk H a w S).2).dropLast, z ∉ S
  | a, w => by
    unfold prefixWalk
    split_ifs with ha
    · simp [MGraph.walkVertices]
    · cases w with
      | nil => simp [MGraph.walkVertices]
      | cons x w' =>
        simp only [MGraph.walkVertices, List.map_cons,
          List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.mem_cons]
        rintro z (rfl | hz)
        · exact ha
        · exact prefixWalk_dropLast_not_mem H S (H.dst x) w' z
            (by simpa [MGraph.walkVertices] using hz)

private lemma isWalk_dst_getLast {H : MGraph} :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)} (hne : P ≠ []),
      H.IsWalk a b P → H.dst (P.getLast hne) = b
  | _, _, [], hne, _ => absurd rfl hne
  | _, _, [_], _, .cons _ _ (.nil _) => rfl
  | _, _, _ :: y :: ys, _, .cons _ _ hrest => isWalk_dst_getLast (List.cons_ne_nil y ys) hrest

private lemma isWalk_prefix_dst_eq_aux {H : MGraph} :
    ∀ {a : ℕ} (p rest : List (ℕ × Bool)) (hp_ne : p ≠ []),
      (H.walkVertices a (p ++ rest))[p.length]'(by simp [MGraph.walkVertices]) =
        H.dst (p.getLast hp_ne)
  | _, [], _, hp_ne => absurd rfl hp_ne
  | _, [_], _, _ => by simp [MGraph.walkVertices]
  | a, x :: y :: ys, rest, _ => by
    simpa [MGraph.walkVertices] using
      isWalk_prefix_dst_eq_aux (H := H) (a := H.dst x) (y :: ys) rest (List.cons_ne_nil y ys)

private lemma isWalk_prefix_dst_eq {H : MGraph} {a : ℕ} {p P : List (ℕ × Bool)}
    (hp : p <+: P) (hp_ne : p ≠ []) :
    (H.walkVertices a P)[p.length]'(by simp [MGraph.walkVertices]; exact hp.length_le) =
      H.dst (p.getLast hp_ne) := by
  obtain ⟨rest, rfl⟩ := hp
  exact isWalk_prefix_dst_eq_aux p rest hp_ne

private lemma prefix_suffix_disjoint_of_step_drop {Gk G' H_lt stH : MGraph} {S_prev : Finset ℕ}
    {u : Update} (hGk : Gk.IsValid) (hu : Gk.UpdateIsValid u) (hdu : isDelOrSplit u)
    (hG'_eq : G' = Gk.applyUpdate u)
    (hSub_lt : G'.IsSubgraph H_lt) (hH_sub : Gk.IsSubgraph stH)
    (hTouch : touchedVertices Gk u ⊆ S_prev)
    {eG : ℕ} (heG' : eG ∈ G'.E)
    {p₁ q₂ P_k : List (ℕ × Bool)} {x₁ : ℕ}
    (hx₁S : x₁ ∈ S_prev) (hx₁V : x₁ ∈ G'.V)
    (hp₁_lt : H_lt.IsWalk (G'.tail eG) x₁ p₁)
    (hq₂_lt : ∀ z ∈ (H_lt.walkVertices (G'.head eG) q₂).dropLast, z ∉ S_prev)
    (hq₂_edges : ∀ x ∈ q₂, x.1 ∈ H_lt.E)
    (hp₁_k : p₁ <+: P_k) (hq₂_k : q₂ <+: walkRev P_k)
    (hPk : stH.IsWalk (Gk.tail eG) (Gk.head eG) P_k) :
    p₁.length + q₂.length ≤ P_k.length := by
  by_contra hlt
  have hp₁_ne : p₁ ≠ [] := by
    intro hnil
    have hq_le := hq₂_k.length_le
    rw [length_walkRev] at hq_le
    simp [hnil] at hlt
    omega
  have hm_lt : P_k.length - p₁.length < q₂.length := by
    have hp_le := hp₁_k.length_le
    omega
  set m := P_k.length - p₁.length
  have hG'_app : G' = Gk.applyBatch [u] := by simpa [MGraph.applyBatch] using hG'_eq
  have hBV_u : Gk.BatchIsValid [u] := ⟨hu, True.intro⟩
  have hds_u : ∀ x ∈ [u], isDelOrSplit x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact hdu
  have hinv_u := batch_delOrSplit_invariants [u] Gk hGk hBV_u hds_u
  have heGk : eG ∈ Gk.E := hinv_u.2.1 (hG'_app ▸ heG')
  have hTouch_u : allTouched Gk [u] ⊆ S_prev := by
    simpa [allTouched, Finset.union_empty] using hTouch
  let y := p₁.getLast hp₁_ne
  have hy_mem : y ∈ p₁ := List.getLast_mem hp₁_ne
  have hy_Hlt : y.1 ∈ H_lt.E := IsWalk.mem_edge hp₁_lt y hy_mem
  have hy_G' : y.1 ∈ G'.E := hSub_lt.2.1 hy_Hlt
  have hy_stH : y.1 ∈ stH.E := IsWalk.mem_edge hPk y (hp₁_k.subset hy_mem)
  have hHlt_dst_y : H_lt.dst y = x₁ := isWalk_dst_getLast hp₁_ne hp₁_lt
  have hPk_idx :
      (stH.walkVertices (Gk.tail eG) P_k)[p₁.length]'(by
          simp [MGraph.walkVertices]; exact hp₁_k.length_le) =
        stH.dst y :=
    isWalk_prefix_dst_eq hp₁_k hp₁_ne
  have hstH_dst_y : stH.dst y = batchAnc [u] x₁ := by
    have hsub1 := hH_sub.2.2 y.1 hy_stH
    have hsub2 := hSub_lt.2.2 y.1 hy_Hlt
    have hanc := hinv_u.2.2.2.2.2.2 y.1 (hinv_u.2.1 (hG'_app ▸ hy_G'))
    rw [← hG'_app] at hanc
    rw [← hHlt_dst_y]
    cases hyb : y.2 <;> simp [MGraph.dst, hyb, hsub1.1, hsub1.2, hsub2.1, hsub2.2, hanc.1, hanc.2]
  have hb_in_S : batchAnc [u] x₁ ∈ S_prev :=
    mem_S_of_anc_mem_S hGk hBV_u hds_u hTouch_u (hG'_app ▸ hx₁V) hx₁S
  have hRev_idx :
      (stH.walkVertices (Gk.head eG) (walkRev P_k))[m]'(by
          simp [MGraph.walkVertices, length_walkRev]; omega) =
        batchAnc [u] x₁ := by
    have hrev_get := congrArg (·[m]?) (walkVertices_walkRev hPk)
    have hm_wv : m < (stH.walkVertices (Gk.tail eG) P_k).length := by
      simp [MGraph.walkVertices]; omega
    have hidx_eq : (stH.walkVertices (Gk.tail eG) P_k).length - 1 - m = p₁.length := by
      simp [MGraph.walkVertices]
      have hp_le := hp₁_k.length_le
      omega
    rw [List.getElem?_eq_getElem (by simp [MGraph.walkVertices, length_walkRev]; omega),
      List.getElem?_eq_getElem (by simpa [List.length_reverse] using hm_wv),
      List.getElem_reverse (by simpa [List.length_reverse] using hm_wv)] at hrev_get
    have hidx_congr :
        (stH.walkVertices (Gk.tail eG) P_k)[(stH.walkVertices (Gk.tail eG) P_k).length - 1 - m] =
          (stH.walkVertices (Gk.tail eG) P_k)[p₁.length]'(by
            simp [MGraph.walkVertices]; exact hp₁_k.length_le) := by
      congr 1
    rw [Option.some.inj hrev_get, hidx_congr, hPk_idx, hstH_dst_y]
  have hq_idx_notS :
      (H_lt.walkVertices (G'.head eG) q₂)[m]'(by
          simp [MGraph.walkVertices]; omega) ∉ S_prev := by
    have hdl_len : m < (H_lt.walkVertices (G'.head eG) q₂).dropLast.length := by
      simp [MGraph.walkVertices]; exact hm_lt
    have heq := List.getElem_dropLast hdl_len
    rw [← heq]
    exact hq₂_lt _ (List.getElem_mem hdl_len)
  have hq_eq_m :
      (stH.walkVertices (Gk.head eG) (walkRev P_k))[m]'(by
          simp [MGraph.walkVertices, length_walkRev]; omega) =
        (H_lt.walkVertices (G'.head eG) q₂)[m]'(by simp [MGraph.walkVertices]; omega) := by
    obtain ⟨t, ht⟩ := hq₂_k
    have h_app := congrArg (fun w => (stH.walkVertices (Gk.head eG) w)[m]?) ht.symm
    have hlen_qt : m < (stH.walkVertices (Gk.head eG) (q₂ ++ t)).length := by
      simp [MGraph.walkVertices]; omega
    rw [List.getElem?_eq_getElem (by simp [MGraph.walkVertices, length_walkRev]; omega),
      List.getElem?_eq_getElem hlen_qt] at h_app
    trans (stH.walkVertices (Gk.head eG) (q₂ ++ t))[m]'hlen_qt
    · exact Option.some.inj h_app
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hlen_qt,
      ← List.getElem?_eq_getElem (by simp [MGraph.walkVertices]; omega)]
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · have hG'h_eq : (H_lt.walkVertices (G'.head eG) q₂)[m]'(by simp [MGraph.walkVertices]; omega) =
          G'.head eG := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem, hm0]
        simp [MGraph.walkVertices]
      have hG'h_notS : G'.head eG ∉ S_prev := hG'h_eq ▸ hq_idx_notS
      rw [hm0]
      simp only [MGraph.walkVertices, List.getElem?_cons_zero, Option.some.injEq]
      have hnt := not_mem_allTouched_invariants [u] Gk hGk hBV_u hds_u (G'.head eG)
        (fun h => hG'h_notS (hTouch_u h))
      have hanc_h := (hinv_u.2.2.2.2.2.2 eG heGk).2
      rw [← hG'_app] at hanc_h
      have hG'V : G'.IsValid := hG'_app ▸ hinv_u.1
      have hhV := (hG'V eG heG').2
      rw [← hanc_h, hnt.2.1 (hnt.1 (hG'_app ▸ hhV))]
    · obtain ⟨t', ht'_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
      have ht'_q : t' < q₂.length := by omega
      have hq_dst_eq : (H_lt.walkVertices (G'.head eG) q₂)[m]'(by simp [MGraph.walkVertices]; omega) =
          H_lt.dst (q₂[t']'ht'_q) := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem, ht'_eq]
        simp [MGraph.walkVertices, List.getElem?_eq_getElem ht'_q]
      have hnotS' : H_lt.dst (q₂[t']'ht'_q) ∉ S_prev := hq_dst_eq ▸ hq_idx_notS
      rw [ht'_eq]
      have hy'_Hlt : (q₂[t']'ht'_q).1 ∈ H_lt.E := hq₂_edges _ (List.getElem_mem ht'_q)
      have hy'_G' : (q₂[t']'ht'_q).1 ∈ G'.E := hSub_lt.2.1 hy'_Hlt
      have hy'_Gk : (q₂[t']'ht'_q).1 ∈ Gk.E := hinv_u.2.1 (hG'_app ▸ hy'_G')
      have hy'_stH : (q₂[t']'ht'_q).1 ∈ stH.E := by
        have hx_rev : q₂[t']'ht'_q ∈ walkRev P_k := ht ▸ List.mem_append_left t (List.getElem_mem ht'_q)
        exact IsWalk.mem_edge (isWalk_walkRev hPk) _ hx_rev
      have hsub1 := hH_sub.2.2 (q₂[t']'ht'_q).1 hy'_stH
      have hsub2 := hSub_lt.2.2 (q₂[t']'ht'_q).1 hy'_Hlt
      have hG'V : G'.IsValid := hG'_app ▸ hinv_u.1
      have hdstV : H_lt.dst (q₂[t']'ht'_q) ∈ G'.V := by
        cases hqb : (q₂[t']'ht'_q).2 <;>
          simp [MGraph.dst, hqb, hsub2.1, hsub2.2, (hG'V _ hy'_G').1, (hG'V _ hy'_G').2]
      have hnt := not_mem_allTouched_invariants [u] Gk hGk hBV_u hds_u
        (H_lt.dst (q₂[t']'ht'_q)) (fun h => hnotS' (hTouch_u h))
      have hanc := hinv_u.2.2.2.2.2.2 (q₂[t']'ht'_q).1 hy'_Gk
      rw [← hG'_app] at hanc
      have hst_eq : stH.dst (q₂[t']'ht'_q) = H_lt.dst (q₂[t']'ht'_q) := by
        have hdst_anc : batchAnc [u] (H_lt.dst (q₂[t']'ht'_q)) = stH.dst (q₂[t']'ht'_q) := by
          cases hqb : (q₂[t']'ht'_q).2 <;>
            simp [MGraph.dst, hqb, hsub1.1, hsub1.2, hsub2.1, hsub2.2, hanc.1, hanc.2]
        rw [← hdst_anc, hnt.2.1 (hnt.1 (hG'_app ▸ hdstV))]
      simp only [MGraph.walkVertices, List.getElem?_cons_succ, List.map_append]
      rw [List.getElem?_append_left (by simp only [List.length_map]; exact ht'_q),
        List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem ht'_q]
      simp [hst_eq]
  rw [hRev_idx] at hq_eq_m
  exact hq_idx_notS (hq_eq_m ▸ hb_in_S)

/-- **D40 single-step `countP` (multiplicity) monotonicity**:
across one `DynSpanner.step` starting from `runState ... k`, for every surviving edge
`eG ∈ res.state.G.E` and every spanner edge `eH ∉ res.D`, `eH` occurs no more times on
`piTotal res.state eG` than on `piTotal st eG`. -/
theorem reembed_step_walkCount_le {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (u : Update) (hu_some : us[k]? = some u) :
    let st := runState (L := L) G₀ q sparsify us k
    let res := step st u sparsify
    ∀ eG ∈ res.state.G.E, ∀ eH, eH ∉ res.D →
      (piTotal res.state eG).countP (fun x => decide (x.1 = eH)) ≤
        (piTotal st eG).countP (fun x => decide (x.1 = eH)) := by
  intro st res eG heG' eH heH_notD
  have hres_eq : res = runStepOut (L := L) G₀ q sparsify us k := by
    simp [res, st, runStepOut, hu_some]
  have hst'_eq : res.state = runState (L := L) G₀ q sparsify us (k + 1) := by
    simp [res, st, runState, hu_some]
  have hInv := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk)
  have hk1_inv := hInv.1
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)).1
  have hRec := hInv.2 k (Nat.lt_succ_self k) u hu_some
  by_cases hj0 : chooseLevel L q (k + 1) = 0
  · obtain ⟨_, _, hD_card, _⟩ := hRec.restart_bounds hj0
    rw [← hres_eq] at hD_card
    have hD_card_nat : res.D.card = res.state.H.E.card := by exact_mod_cast hD_card
    have hD_sub : res.D ⊆ res.state.H.E := by
      rw [hst'_eq, hres_eq]
      exact hRec.D_sub
    have hD_eq : res.D = res.state.H.E :=
      Finset.eq_of_subset_of_card_le hD_sub hD_card_nat.ge
    have hemb' := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := k + 1) (Nat.succ_le_of_lt hk)).2
    have hw' := hemb'.2 eG (hk1_inv.G_eq ▸ hst'_eq ▸ heG')
    rw [← hst'_eq] at hw'
    have hnotW : eH ∉ walkEdges (piTotal res.state eG) := fun hm => by
      rw [mem_walkEdges_iff] at hm
      rcases hm with ⟨x, hx, rfl⟩
      exact heH_notD (hD_eq ▸ IsWalk.mem_edge hw' x hx)
    rw [countP_eq_zero_of_not_mem_walkEdges hnotW]
    exact Nat.zero_le _
  · set j := chooseLevel L q (k + 1)
    have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
    have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
    have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
    have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
    obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
    obtain ⟨hBV_k, hds_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
    obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
    have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
    have hinv_k := batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k
    have hVGk : (G₀.applyBatch (us.take k)).IsValid := hinv_k.1
    set Gk := G₀.applyBatch (us.take k)
    set G' := G₀.applyBatch (us.take (k + 1))
    have hG'_eq : G' = Gk.applyUpdate u := by simp [G', Gk, htake_succ, MGraph.applyBatch]
    have hinv_k1 := batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBV_k1 hds_k1
    have hVG' : G'.IsValid := hinv_k1.1
    have hG'E_sub : G'.E ⊆ Gk.E := by
      have h1 := (batch_delOrSplit_invariants [u] Gk hVGk
        ⟨hu_valid, True.intro⟩ (fun x hx => by simp at hx; rwa [hx])).2.1
      simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
      rwa [← hG'_eq] at h1
    set r := lastRebuild q L (j - 1) (k + 1)
    have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ k + 1 := fun hdvd =>
      by have := (chooseLevel_le_iff_dvd hq (le_trans (Nat.sub_le j 1) hj_le)).mpr hdvd; omega
    have hr_eq_k : r = lastRebuild q L (j - 1) k :=
      lastRebuild_eq_of_not_dvd (q := q) (L := L) (i := j - 1) hr_not_dvd
    have hr_le_k : r ≤ k := by rw [hr_eq_k]; exact lastRebuild_le q L (j - 1) k
    have hInv_r := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le_k hk.le)).1
    have hr_ch : chooseLevel L q r ≤ j - 1 :=
      lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
    set st_r := runState (L := L) G₀ q sparsify us r
    set G_r := G₀.applyBatch (us.take r)
    set delta := (us.take (k + 1)).drop r
    have htake_k1 : us.take (k + 1) = us.take r ++ delta := by
      have h1 : (us.take (k + 1)).take r = us.take r := by
        rw [List.take_take, min_eq_left (le_trans hr_le_k (Nat.le_succ k))]
      rw [← h1]; exact (List.take_append_drop r (us.take (k + 1))).symm
    have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (htake_k1 ▸ hBV_k1)
    have hBV_d : G_r.BatchIsValid delta := hBV_split.2
    have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_right _ hx)
    have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
      hds_k1 x (by rw [htake_k1]; exact List.mem_append_left _ hx)
    have hinv_r_d := batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_split.1 hds_r
    have hVG_r : G_r.IsValid := hinv_r_d.1
    have hG_r_m : G_r.m ≤ mMax := le_trans (Finset.card_le_card hinv_r_d.2.1) hGm₀
    have hG'_delta : G' = G_r.applyBatch delta := by dsimp only [G', G_r]; rw [htake_k1, applyBatch_append]
    have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
    have hrk_eq_lt : ∀ {m : ℕ}, m < j →
        lastRebuild q L m (k + 1) = lastRebuild q L m k ∧
        lastRebuild q L m r = lastRebuild q L m k := fun {m} hm => by
      have hm_le : m ≤ j - 1 := Nat.le_pred_of_lt hm
      have h1 : lastRebuild q L m (k + 1) = lastRebuild q L m k :=
        lastRebuild_eq_of_not_dvd fun hdvd =>
          hr_not_dvd (dvd_trans (phasePeriod_dvd_of_le hm_le (le_trans (Nat.sub_le j 1) hj_le)) hdvd)
      have hmr_le : lastRebuild q L m k ≤ r :=
        hr_eq_k ▸ lastRebuild_mono_level hq hm_le (le_trans (Nat.sub_le j 1) hj_le)
      exact ⟨h1, lastRebuild_idempotent_le hq hmr_le hr_le_k⟩
    set H_mid : Fin (L + 1) → MGraph :=
      fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    have hH_mid_props : ∀ i : Fin (L + 1),
        G'.IsSubgraph (H_mid i) ∧ (H_mid i).V = G'.V ∧ (H_mid i).E = (st.H_level i).E ∩ G'.E :=
      fun i => by
        obtain ⟨_, h1, h2, h3, _, _⟩ :=
          isSubgraph_restrictUpdate (hk_inv.H_level_sub i) (hk_inv.H_level_V i) hu_valid hdu
        exact ⟨hG'_eq ▸ h1, hG'_eq ▸ h2, hG'_eq ▸ h3⟩
    set H_lt := unionGraphLt G' H_mid j
    set H_lt_r := unionGraphLt G_r st_r.H_level j
    have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
      refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      intro e he
      simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] at he
      rcases he with ⟨i, _, hei⟩
      exact (hInv_r.H_level_sub i).2.1 hei
    have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
      ext e
      simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hij, hei⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2] at hei
        have hei' := Finset.mem_inter.mp hei
        have hei1 := Finset.mem_inter.mp hei'.1
        exact ⟨⟨i, hij, hInv_r.H_level_E i ▸ Finset.mem_inter.mpr ⟨hei1.1, hinv_d.2.1 (hG'_delta ▸ hei'.2)⟩⟩, hei'.2⟩
      · rintro ⟨⟨i, hij, hei_r⟩, heG'⟩
        refine ⟨i, hij, ?_⟩
        rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2]
        rw [hInv_r.H_level_E i, Finset.mem_inter] at hei_r
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hei_r.1, hG'E_sub heG'⟩, heG'⟩
    have hSub_lt : G'.IsSubgraph H_lt :=
      ⟨Finset.Subset.rfl, hHLt_E ▸ Finset.inter_subset_right, fun _ _ => ⟨rfl, rfl⟩⟩
    set inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    set piLt_mid : Embedding := piLtFrom st.Pi_level inDom_mid j
    set S_prev : Finset ℕ := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
    have hS_prev_eq : S_prev = allTouched G_r delta := by
      dsimp only [S_prev]
      rw [hk_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_k]
      have hdrop_app : (us.take (k + 1)).drop r = (us.take k).drop r ++ [u] := by
        rw [htake_succ, List.drop_append_of_le_length]
        rw [List.length_take]; exact le_trans hr_le_k (Nat.le_min.mpr ⟨le_rfl, hk.le⟩)
      have hGapp : G_r.applyBatch ((us.take k).drop r) = Gk := by
        have htk : us.take k = us.take r ++ (us.take k).drop r := by
          have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_k]
          rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
        dsimp only [Gk, G_r]
        conv_rhs => rw [htk]
        exact (applyBatch_append _ _ _).symm
      dsimp only [delta]
      rw [hdrop_app, allTouched_append, hGapp]; dsimp only [Gk, G_r]; rw [hk_inv.G_eq]; simp [allTouched]
    have hpi_eq : ∀ e ∈ G'.E, piLt_mid e = piLe st_r (j - 1) e := fun e heG'' => by
      change piLtFrom st.Pi_level inDom_mid j e = piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e
      have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
      rw [hsub1]
      have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
        dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]; exact ⟨hG'E_sub heG'', heG''⟩
      have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ :=
        hInv_r.inDom0 ▸ hinv_d.2.1 (hG'_delta ▸ heG'')
      have hcongr_in : ∀ m : Fin (L + 1), m.1 < j → (e ∈ inDom_mid m ↔ e ∈ st_r.inDom m) := fun m hm => by
        have h1 := hk_inv.inDom_eq m; have h2 := hInv_r.inDom_eq m
        rw [← (hrk_eq_lt hm).2] at h1
        have heGk : e ∈ Gk.E := hG'E_sub heG''
        have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heG'')
        constructor <;> intro h
        · rw [Finset.mem_inter] at h; rw [h1, Finset.mem_inter] at h
          rw [h2]; exact Finset.mem_inter.mpr ⟨h.1.1, heGr⟩
        · rw [h2, Finset.mem_inter] at h
          refine Finset.mem_inter.mpr ⟨?_, heG''⟩
          rw [h1]; exact Finset.mem_inter.mpr ⟨h.1, heGk⟩
      obtain ⟨m₁, hm₁j, hm₁d, hm₁none, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
      obtain ⟨m₂, hm₂j, hm₂d, hm₂none, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
      have hm_eq : m₁ = m₂ := by
        by_contra hne
        rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
        · exact hm₁none m₂ hlt hm₂j ((hcongr_in m₂ hm₂j).mpr hm₂d)
        · exact hm₂none m₁ hlt hm₁j ((hcongr_in m₁ hm₁j).mp hm₁d)
      rw [heq₁, heq₂, hm_eq, hk_inv.Pi_level_eq m₂, ← (hrk_eq_lt hm₂j).2, hInv_r.Pi_level_eq m₂]
    have hj1_succ : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
    have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
    have hLenr := hInv_r.len_at ⟨j - 1, by omega⟩ hr_ch
    have hVcr := hInv_r.vcong_at ⟨j - 1, by omega⟩ hr_ch
    dsimp only at hEmbr hLenr hVcr; rw [hj1_succ] at hEmbr hVcr
    have hPW := projWalk_spec hSpec hVG_r hBV_d hds_d hG_r_m hSub_lt_r hEmbr hLenr hVcr
      (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1))
      (vcongBound_step P.hγ_c P.hγ_ℓ G₀.maxDeg (j - 1))
      (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
      (by simp [H_lt, unionGraphLt, hG'_delta]) (by simp [H_lt, unionGraphLt, hG'_delta])
      (hG'_delta ▸ hSub_lt) hS_prev_eq.symm.subset (fun e he => hpi_eq e (hG'_delta ▸ he))
    dsimp only at hPW; rw [← hG'_delta] at hPW
    rcases hPW with ⟨_, _, _, hOut_aff, _, _, _, _, _, _, _, _, _, _, _, hOut_emb, -⟩
    set E_aff := affectedEdges G' H_lt piLt_mid S_prev
    set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
    set out := if E_aff.Nonempty then sparsify (buildAuxHost G' H_lt E_aff) J embJH else ⟨J, idEmb, 0⟩
    set outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    set embMid : Embedding := Embedding.comp embJH outEmb
    set Pi_j : Embedding := reembedWalk G' H_lt piLt_mid embMid S_prev
    have hD_eq : res.D = out.Jtilde.E.biUnion fun e => walkEdges (embJH e) := by
      rw [show res = step st u sparsify from rfl]; dsimp only [step]
      have hst_eq : st.q = q ∧ st.t = k ∧ st.G = Gk := ⟨hk_inv.q_eq, hk_inv.t_eq, hk_inv.G_eq⟩
      simp only [show ¬ chooseLevel L st.q (st.t + 1) = 0 by rw [hst_eq.1, hst_eq.2.1]; exact hj0,
        ↓reduceDIte]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hst_eq.1, hst_eq.2.1]
      have hstG' : st.G.applyUpdate u = G' := by rw [hst_eq.2.2, ← hG'_eq]
      simp only [hch_j, hstG', H_mid, H_lt, inDom_mid, piLt_mid, E_aff, J, embJH, out, S_prev, st]
    have hres_st_Pi : ∀ l : Fin (L + 1), res.state.Pi_level l =
        if l.1 < j then st.Pi_level l else if l.1 = j then Pi_j else fun _ => [] := fun l => by
      dsimp only [res, step]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
      have hch_ne : ¬ chooseLevel L st.q (st.t + 1) = 0 := by rw [hch_j]; exact hj0
      simp only [hch_ne, ↓reduceDIte]
      have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_eq]
      simp only [hch_j, hstG', Pi_j, embMid, outEmb, embJH, out, J, E_aff, S_prev, piLt_mid,
        inDom_mid, H_lt, H_mid, st]
    have hres_st_inDom : ∀ l : Fin (L + 1), res.state.inDom l =
        if l.1 < j then inDom_mid l else if l.1 = j then E_aff else ∅ := fun l => by
      dsimp only [res, step]
      have hch_j : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
      have hch_ne : ¬ chooseLevel L st.q (st.t + 1) = 0 := by rw [hch_j]; exact hj0
      simp only [hch_ne, ↓reduceDIte]
      have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_eq]
      simp only [hch_j, hstG', E_aff, S_prev, piLt_mid, inDom_mid, H_lt, H_mid, st]
    have heG'_E : eG ∈ G'.E := by
      dsimp only [G']
      rw [← hk1_inv.G_eq, ← hst'_eq]
      exact heG'
    have he0' : eG ∈ res.state.inDom ⟨0, Nat.zero_lt_succ L⟩ :=
      hst'_eq ▸ hk1_inv.inDom0 ▸ heG'_E
    have hpiTot' : piTotal res.state eG = if eG ∈ E_aff then Pi_j eG else piLt_mid eG := by
      have hlt_L := piLtFrom_eq_of_lt res.state.Pi_level res.state.inDom
        (Nat.succ_pos j) (Nat.succ_le_succ hj_le) he0' fun l hl1 _ => by
          rw [hres_st_inDom l]
          simp [Nat.not_lt.mpr (Nat.le_of_succ_le hl1),
            Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hl1)]
      change piLtFrom res.state.Pi_level res.state.inDom (L + 1) eG = _
      rw [hlt_L]
      by_cases heAff : eG ∈ E_aff
      · have hj_dom : eG ∈ res.state.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
          rw [hres_st_inDom]; simp [heAff]
        obtain ⟨m, hmj, _, hm_none, heqm⟩ :=
          piLtFrom_eq res.state.Pi_level res.state.inDom (Nat.succ_pos j) he0'
        have hm_eq : m.1 = j := by
          apply le_antisymm (Nat.lt_succ_iff.mp hmj)
          by_contra hlt
          exact hm_none ⟨j, Nat.lt_succ_of_le hj_le⟩ (Nat.lt_of_not_le hlt) (Nat.lt_succ_self j) hj_dom
        rw [heqm, show m = ⟨j, Nat.lt_succ_of_le hj_le⟩ from Fin.ext hm_eq, hres_st_Pi]
        simp [heAff]
      · have hj_not : eG ∉ res.state.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
          rw [hres_st_inDom]; simp [heAff]
        have hprev := piLtFrom_eq_prev_of_not_mem res.state.Pi_level res.state.inDom
          (j := ⟨j, Nat.lt_succ_of_le hj_le⟩) hj_pos he0' hj_not
        rw [hprev]
        have hcongr_mid : piLtFrom res.state.Pi_level res.state.inDom j eG = piLt_mid eG := by
          have h0_mid : eG ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
            dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]; exact ⟨hG'E_sub heG'_E, heG'_E⟩
          obtain ⟨m, hmj, hmd, hm_none, heqm⟩ :=
            piLtFrom_eq res.state.Pi_level res.state.inDom hj_pos he0'
          obtain ⟨m', hm'j, hm'd, hm'_none, heqm'⟩ :=
            piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
          have hmm' : m = m' := by
            by_contra hne
            rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
            · exact hm_none m' hlt hm'j ((hres_st_inDom m') ▸ by simp [hm'j, hm'd])
            · exact hm'_none m hlt hmj (by
                have h1 := hres_st_inDom m; simp [hmj] at h1; rwa [← h1])
          dsimp only [piLt_mid]
          rw [heqm, heqm', hmm', hres_st_Pi]
          simp [hm'j]
        simpa [heAff] using hcongr_mid
    have hemb_k : Embedding.IsEmbedding (piTotal st) Gk st.H := by
      have h1 := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds hk.le).2
      simpa [st, hk_inv.G_eq] using h1
    have hGk_H_sub : Gk.IsSubgraph st.H := by simpa [st] using hk_inv.H_sub
    have heGk : eG ∈ Gk.E := hG'E_sub heG'_E
    have hPk_walk : st.H.IsWalk (Gk.tail eG) (Gk.head eG) (piTotal st eG) := hemb_k.2 eG heGk
    have hEnds_lt : ∀ e ∈ H_lt_r.E, H_lt.tail e = G'.tail e ∧ H_lt.head e = G'.head e :=
      fun _ _ => ⟨rfl, rfl⟩
    have hVH_lt_r : H_lt_r.IsValid := fun e he => by
      obtain ⟨ht, hh⟩ := hSub_lt_r.2.2 e he
      obtain ⟨htG, hhG⟩ := hVG_r e (hSub_lt_r.2.1 he)
      exact ⟨hEmbr.1 (ht ▸ htG), hEmbr.1 (hh ▸ hhG)⟩
    have hw_r := hEmbr.2 eG (hinv_d.2.1 (hG'_delta ▸ heG'_E))
    obtain ⟨ht0_V, hh0_V⟩ := hVG_r eG (hinv_d.2.1 (hG'_delta ▸ heG'_E))
    obtain ⟨ht_V, hh_V⟩ := hVG' eG heG'_E
    obtain ⟨hanc_t, hanc_h⟩ := hinv_d.2.2.2.2.2.2 eG (hinv_d.2.1 (hG'_delta ▸ heG'_E))
    have hanc_t' : batchAnc delta (G'.tail eG) = G_r.tail eG := by simpa [hG'_delta] using hanc_t
    have hanc_h' : batchAnc delta (G'.head eG) = G_r.head eG := by simpa [hG'_delta] using hanc_h
    have hTouch_d : allTouched G_r delta ⊆ S_prev := hS_prev_eq.symm.subset
    rw [hpiTot']
    by_cases heAff : eG ∈ E_aff
    · simp only [heAff, ↓reduceIte]
      have hhit1 : ∃ z ∈ H_lt.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG), z ∈ S_prev := by
        simpa [E_aff, affectedEdges, decide_eq_true_eq, hpi_eq eG heG'_E] using
          (Finset.mem_filter.mp heAff).2
      have hV_wr : ∀ z ∈ H_lt.walkVertices (G'.head eG) (walkRev (piLe st_r (j - 1) eG)), z ∈ G'.V := by
        simpa [← hG'_delta] using
          walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hEnds_lt)
            (IsWalk.mem_edge (isWalk_walkRev hw_r)) (hG'_delta ▸ hh_V)
      have hV_w : ∀ z ∈ H_lt.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG), z ∈ G'.V := by
        simpa [← hG'_delta] using
          walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hEnds_lt)
            (IsWalk.mem_edge hw_r) (hG'_delta ▸ ht_V)
      have h1_anc := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hEnds_lt) hTouch_d
        (IsWalk.mem_edge hw_r) (hG'_delta ▸ ht_V) hanc_t'
        (by simpa [hG'_delta] using hV_w)).mp hhit1
      have h2_anc : ∃ z₀ ∈ H_lt_r.walkVertices (G_r.head eG) (walkRev (piLe st_r (j - 1) eG)),
          z₀ ∈ S_prev := by
        obtain ⟨z₀, hz₀, hz₀S⟩ := h1_anc
        exact ⟨z₀, (mem_walkVertices_walkRev hw_r z₀).mpr hz₀, hz₀S⟩
      have hhit2 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hEnds_lt) hTouch_d
        (IsWalk.mem_edge (isWalk_walkRev hw_r)) (hG'_delta ▸ hh_V) hanc_h'
        (by simpa [hG'_delta] using hV_wr)).mpr h2_anc
      have hp1_sp := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hSub_lt)
        (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E) (hG'_delta ▸ hEnds_lt) hTouch_d
        (piLe st_r (j - 1) eG) (G_r.tail eG) (G_r.head eG) (G'.tail eG)
        ht0_V hh0_V hw_r (hG'_delta ▸ ht_V) hanc_t').2 (by simpa [hG'_delta] using hhit1)
      have hq2_sp := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hSub_lt)
        (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E) (hG'_delta ▸ hEnds_lt) hTouch_d
        (walkRev (piLe st_r (j - 1) eG)) (G_r.head eG) (G_r.tail eG) (G'.head eG)
        hh0_V ht0_V (isWalk_walkRev hw_r) (hG'_delta ▸ hh_V) hanc_h').2
        (by simpa [hG'_delta] using hhit2)
      dsimp only at hp1_sp hq2_sp
      set p₁ := (prefixWalk H_lt (G'.tail eG) (piLe st_r (j - 1) eG) S_prev).2
      set q₂ := (prefixWalk H_lt (G'.head eG) (walkRev (piLe st_r (j - 1) eG)) S_prev).2
      set x₁ := (prefixWalk H_lt (G'.tail eG) (piLe st_r (j - 1) eG) S_prev).1
      have hp1_drop_G' : ∀ z ∈ (G'.walkVertices (G'.tail eG) p₁).dropLast,
          z ∉ allTouched G_r delta := fun z hz => by
        have hlt_eq : G'.walkVertices (G'.tail eG) p₁ = H_lt.walkVertices (G'.tail eG) p₁ := rfl
        rw [hlt_eq] at hz
        have hns := (prefixWalk_dropLast_not_mem H_lt S_prev (G'.tail eG) (piLe st_r (j - 1) eG) z hz)
        exact fun h => hns (hS_prev_eq ▸ h)
      have hq2_drop_G' : ∀ z ∈ (G'.walkVertices (G'.head eG) q₂).dropLast,
          z ∉ allTouched G_r delta := fun z hz => by
        have hlt_eq : G'.walkVertices (G'.head eG) q₂ = H_lt.walkVertices (G'.head eG) q₂ := rfl
        rw [hlt_eq] at hz
        have hns := (prefixWalk_dropLast_not_mem H_lt S_prev (G'.head eG)
          (walkRev (piLe st_r (j - 1) eG)) z hz)
        exact fun h => hns (hS_prev_eq ▸ h)
      have hu_eq : us[k]'(hk) = u := by
        simpa using (List.getElem?_eq_some_iff.mp hu_some).2
      have hLHS_lt : unionGraphLt (G₀.applyBatch (us.take (k + 1)))
          (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j =
          H_lt := by
        rw [hu_eq]
      have htail_eq : (G₀.applyBatch (us.take (k + 1))).tail eG = G'.tail eG := rfl
      have hhead_eq : (G₀.applyBatch (us.take (k + 1))).head eG = G'.head eG := rfl
      have hx1_eq : (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
          ((G₀.applyBatch (us.take (k + 1))).tail eG) (piLe st_r (j - 1) eG)
          (allTouched G_r delta)).1 = x₁ := by
        rw [hLHS_lt, htail_eq, ← hS_prev_eq]
      have hx2_eq : (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
          ((G₀.applyBatch (us.take (k + 1))).head eG) (walkRev (piLe st_r (j - 1) eG))
          (allTouched G_r delta)).1 =
          (prefixWalk H_lt (G'.head eG) (walkRev (piLe st_r (j - 1) eG)) S_prev).1 := by
        rw [hLHS_lt, hhead_eq, ← hS_prev_eq]
      have hW1_pres : G'.IsWalk ((G₀.applyBatch (us.take (k + 1))).tail eG)
          (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
            ((G₀.applyBatch (us.take (k + 1))).tail eG) (piLe st_r (j - 1) eG)
            (allTouched G_r delta)).1 p₁ := by
        rw [hx1_eq]
        exact IsWalk.of_isSubgraph hSub_lt hp1_sp.2.2.1
      have hW2_pres : G'.IsWalk ((G₀.applyBatch (us.take (k + 1))).head eG)
          (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
            ((G₀.applyBatch (us.take (k + 1))).head eG) (walkRev (piLe st_r (j - 1) eG))
            (allTouched G_r delta)).1 q₂ := by
        rw [hx2_eq]
        exact IsWalk.of_isSubgraph hSub_lt hq2_sp.2.2.1
      have hPres := prefix_suffix_preserve_backward hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le rfl
        heG'_E hp1_sp.2.2.2.1 hq2_sp.2.2.2.1 hW1_pres hW2_pres
        hp1_drop_G' hq2_drop_G' k hr_le_k le_rfl ⟨L, Nat.lt_succ_self L⟩ (by dsimp; omega)
      have hp1_k : p₁ <+: piTotal st eG := hPres.1
      have hq2_k : q₂ <+: walkRev (piTotal st eG) := hPres.2
      have hTouch_u : touchedVertices Gk u ⊆ S_prev := by
        dsimp only [S_prev]
        rw [hk_inv.G_eq]
        exact Finset.subset_union_right
      have hsum_len : p₁.length + q₂.length ≤ (piTotal st eG).length :=
        prefix_suffix_disjoint_of_step_drop hVGk hu_valid hdu hG'_eq hSub_lt hGk_H_sub hTouch_u
          heG'_E hp1_sp.1 (hG'_delta ▸ hp1_sp.2.1) hp1_sp.2.2.1
          (prefixWalk_dropLast_not_mem H_lt S_prev (G'.head eG) (walkRev (piLe st_r (j - 1) eG)))
          (IsWalk.mem_edge hq2_sp.2.2.1) hp1_k hq2_k hPk_walk
      have hmid_zero : (embMid eG).countP (fun x => decide (x.1 = eH)) = 0 := by
        rw [List.countP_eq_zero]
        intro z hz hdec
        obtain ⟨y, hy, hyz⟩ := List.mem_flatMap.mp hz
        have hy_J : y.1 ∈ out.Jtilde.E := IsWalk.mem_edge (hOut_emb.2 eG heAff) y hy
        have hz_edge : z.1 ∈ walkEdges (embJH y.1) := by
          cases hy2 : y.2 with
          | true =>
            simp only [hy2, ↓reduceIte] at hyz
            rw [mem_walkEdges_iff]
            exact ⟨z, hyz, rfl⟩
          | false =>
            simp only [hy2, Bool.false_eq_true, ↓reduceIte] at hyz
            rw [← walkEdges_walkRev, mem_walkEdges_iff]
            exact ⟨z, hyz, rfl⟩
        apply heH_notD
        rw [hD_eq, Finset.mem_biUnion]
        exact ⟨y.1, hy_J, of_decide_eq_true hdec ▸ hz_edge⟩
      have hrew : Pi_j eG = p₁ ++ embMid eG ++ walkRev q₂ := by
        simp only [Pi_j, reembedWalk, p₁, q₂, hpi_eq eG heG'_E]
      rw [hrew]
      exact countP_prefix_append_suffix_le p₁ (walkRev q₂) (embMid eG) (piTotal st eG)
        (fun x => decide (x.1 = eH)) hp1_k (walkRev_prefix_to_suffix hq2_k)
        (by simpa [length_walkRev] using hsum_len) hmid_zero
    · simp only [heAff, ↓reduceIte]
      have hDisj1 : Disjoint (H_lt.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG)).toFinset S_prev := by
        rw [Finset.disjoint_left]
        intro z hz
        simp only [List.mem_toFinset] at hz
        intro hzS
        apply heAff
        simpa [E_aff, affectedEdges, decide_eq_true_eq, hpi_eq eG heG'_E] using
          ⟨heG'_E, z, hz, hzS⟩
      have hsp1 := (prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r (hG'_delta ▸ hSub_lt)
        (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E) (hG'_delta ▸ hEnds_lt) hTouch_d
        (piLe st_r (j - 1) eG) (G_r.tail eG) (G_r.head eG) (G'.tail eG)
        ht0_V hh0_V hw_r (hG'_delta ▸ ht_V) hanc_t').1 (by simpa [hG'_delta] using hDisj1)
      have hHead_notS : G_r.head eG ∉ S_prev := by
        intro hmem
        apply (Finset.disjoint_left.mp hDisj1)
        · simp only [List.mem_toFinset, hsp1.2.2]
          exact IsWalk.end_mem_walkVertices hw_r
        · exact hmem
      have hHead_eq : G'.head eG = G_r.head eG := by
        by_contra hne
        have hne' : batchAnc delta (G'.head eG) ≠ G'.head eG := by
          rw [hanc_h']; exact Ne.symm hne
        have hmem_at := batchAnc_mem_allTouched_of_ne delta G_r hVG_r hBV_d hds_d (G'.head eG)
          (hG'_delta ▸ hh_V) hne'
        rw [hanc_h'] at hmem_at
        exact hHead_notS (hTouch_d hmem_at)
      have hDisj2 : Disjoint (H_lt.walkVertices (G'.head eG)
          (walkRev (piLe st_r (j - 1) eG))).toFinset S_prev := by
        rw [hHead_eq, walkVertices_walkRev hsp1.2.1, List.toFinset_reverse]
        exact hDisj1
      have hp1_pair : prefixWalk H_lt (G'.tail eG) (piLe st_r (j - 1) eG) S_prev =
          (G_r.head eG, piLe st_r (j - 1) eG) :=
        prefixWalk_pair_eq_of_disjoint H_lt S_prev (piLe st_r (j - 1) eG) hsp1.2.1 hDisj1
      have hq2_pair : prefixWalk H_lt (G'.head eG) (walkRev (piLe st_r (j - 1) eG)) S_prev =
          (G'.tail eG, walkRev (piLe st_r (j - 1) eG)) :=
        prefixWalk_pair_eq_of_disjoint H_lt S_prev (walkRev (piLe st_r (j - 1) eG))
          (hHead_eq ▸ isWalk_walkRev hsp1.2.1) hDisj2
      have hWalk_G' : G'.IsWalk (G'.tail eG) (G'.head eG) (piLe st_r (j - 1) eG) :=
        hHead_eq ▸ IsWalk.of_isSubgraph hSub_lt hsp1.2.1
      have hdrop1 : ∀ z ∈ (G'.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG)).dropLast,
          z ∉ allTouched G_r delta := fun z hz => by
        have hlt_eq : G'.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG) =
            H_lt.walkVertices (G'.tail eG) (piLe st_r (j - 1) eG) := rfl
        rw [hlt_eq] at hz
        exact fun h => (Finset.disjoint_left.mp hDisj1)
          (List.mem_toFinset.mpr (List.mem_of_mem_dropLast hz)) (hS_prev_eq ▸ h)
      have hdrop2 : ∀ z ∈ (G'.walkVertices (G'.head eG)
          (walkRev (piLe st_r (j - 1) eG))).dropLast, z ∉ allTouched G_r delta := fun z hz => by
        have hlt_eq : G'.walkVertices (G'.head eG) (walkRev (piLe st_r (j - 1) eG)) =
            H_lt.walkVertices (G'.head eG) (walkRev (piLe st_r (j - 1) eG)) := rfl
        rw [hlt_eq] at hz
        exact fun h => (Finset.disjoint_left.mp hDisj2)
          (List.mem_toFinset.mpr (List.mem_of_mem_dropLast hz)) (hS_prev_eq ▸ h)
      have hu_eq : us[k]'(hk) = u := by
        simpa using (List.getElem?_eq_some_iff.mp hu_some).2
      have hLHS_lt : unionGraphLt (G₀.applyBatch (us.take (k + 1)))
          (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j =
          H_lt := by
        rw [hu_eq]
      have htail_eq : (G₀.applyBatch (us.take (k + 1))).tail eG = G'.tail eG := rfl
      have hhead_eq : (G₀.applyBatch (us.take (k + 1))).head eG = G'.head eG := rfl
      have hp1_pair' : (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
          ((G₀.applyBatch (us.take (k + 1))).tail eG) (piLe st_r (j - 1) eG)
          (allTouched G_r delta)).1 = G_r.head eG := by
        rw [hLHS_lt, htail_eq, ← hS_prev_eq]
        exact congrArg Prod.fst hp1_pair
      have hq2_pair' : (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
          ((G₀.applyBatch (us.take (k + 1))).head eG) (walkRev (piLe st_r (j - 1) eG))
          (allTouched G_r delta)).1 = G'.tail eG := by
        rw [hLHS_lt, hhead_eq, ← hS_prev_eq]
        exact congrArg Prod.fst hq2_pair
      have hW1_pres : G'.IsWalk ((G₀.applyBatch (us.take (k + 1))).tail eG)
          (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
            ((G₀.applyBatch (us.take (k + 1))).tail eG) (piLe st_r (j - 1) eG)
            (allTouched G_r delta)).1 (piLe st_r (j - 1) eG) := by
        rw [hp1_pair']
        exact hHead_eq.symm ▸ hWalk_G'
      have hW2_pres : G'.IsWalk ((G₀.applyBatch (us.take (k + 1))).head eG)
          (prefixWalk (unionGraphLt (G₀.applyBatch (us.take (k + 1)))
            (fun i => (st.H_level i).applyBatch (restrictUpdate (us[k]'hk) (st.H_level i))) j)
            ((G₀.applyBatch (us.take (k + 1))).head eG) (walkRev (piLe st_r (j - 1) eG))
            (allTouched G_r delta)).1 (walkRev (piLe st_r (j - 1) eG)) := by
        rw [hq2_pair']
        exact isWalk_walkRev hWalk_G'
      have hPres := prefix_suffix_preserve_backward hVG₀ hL hq hGm₀ hSpec hBV hds hk j hj_pos hj_le rfl
        heG'_E (List.prefix_refl _) (List.prefix_refl _) hW1_pres hW2_pres
        hdrop1 hdrop2 k hr_le_k le_rfl ⟨L, Nat.lt_succ_self L⟩ (by dsimp; omega)
      rw [hpi_eq eG heG'_E]
      exact List.Sublist.countP_le hPres.1.sublist

/-- **D40 batch `countP` (multiplicity) monotonicity**:
across `DynSpanner.update st U sparsify`, for every surviving edge `eG ∈ res.state.G.E`
and every `eH ∉ res.D`, the occurrence multiplicity of `eH` on `piTotal res.state eG`
is at most on `piTotal st eG`. -/
theorem reembed_batch_walkCount_le {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k₀ : ℕ} {U : List Update}
    (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let st := runState (L := L) G₀ q sparsify us k₀
    let res := update st U sparsify
    ∀ eG ∈ res.state.G.E, ∀ eH, eH ∉ res.D →
      (piTotal res.state eG).countP (fun x => decide (x.1 = eH)) ≤
        (piTotal st eG).countP (fun x => decide (x.1 = eH)) := by
  intro st res eG heG_res eH heH_notD
  have hrun := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ [] ∅ 0 hlen hmatch
  have hst' : res.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) := by
    dsimp only [res, update]; rw [hrun]
  have hinv_end := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + U.length) hlen).1
  have heG_end : eG ∈ (G₀.applyBatch (us.take (k₀ + U.length))).E := by
    rw [← hinv_end.G_eq, ← hst']; exact heG_res
  have hemb_end := (lemma_5_6 hVG₀ hL hq hGm₀ hSpec hBV hds (k := k₀ + U.length) hlen).2
  have hw_end := hemb_end.2 eG heG_end
  rw [← hst'] at hw_end
  by_cases heH_H' : eH ∈ res.state.H.E
  · have hD_eq : res.D = ((Finset.range U.length).biUnion fun i =>
        (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D) ∩ res.state.H.E := by
      dsimp only [res, update]; rw [hrun]; simp
    have heH_not_step : ∀ i < U.length,
        eH ∉ (runStepOut (L := L) G₀ q sparsify us (k₀ + i)).D := fun i hi hmem =>
      heH_notD (hD_eq ▸ Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hmem⟩, heH_H'⟩)
    have hback : ∀ r ≤ U.length,
        (piTotal (runState (L := L) G₀ q sparsify us (k₀ + U.length)) eG).countP
            (fun x => decide (x.1 = eH)) ≤
          (piTotal (runState (L := L) G₀ q sparsify us (k₀ + (U.length - r))) eG).countP
            (fun x => decide (x.1 = eH)) := by
      intro r
      induction r with
      | zero => intro _; exact le_rfl
      | succ r ih =>
        intro hr
        set p := U.length - (r + 1)
        have hp_lt : p < U.length := by omega
        have hsucc : U.length - r = p + 1 := by omega
        have ih' := ih (by omega)
        rw [hsucc, ← Nat.add_assoc] at ih'
        have heG_p1 : eG ∈ (G₀.applyBatch (us.take (k₀ + p + 1))).E := by
          obtain ⟨hBV_end, hds_end, _⟩ := batchIsValid_take us G₀ (k₀ + U.length) hBV hds
          have htake_eq : us.take (k₀ + U.length) =
              us.take (k₀ + p + 1) ++ (us.take (k₀ + U.length)).drop (k₀ + p + 1) := by
            have h1 : (us.take (k₀ + U.length)).take (k₀ + p + 1) = us.take (k₀ + p + 1) := by
              rw [List.take_take, min_eq_left (by omega)]
            rw [← h1]; exact (List.take_append_drop _ _).symm
          have hBV_split := (batchIsValid_append G₀ (us.take (k₀ + p + 1)) _).mp (htake_eq ▸ hBV_end)
          have hds1 : ∀ x ∈ us.take (k₀ + p + 1), isDelOrSplit x := fun x hx =>
            hds_end x (by rw [htake_eq]; exact List.mem_append_left _ hx)
          have hds2 : ∀ x ∈ (us.take (k₀ + U.length)).drop (k₀ + p + 1), isDelOrSplit x := fun x hx =>
            hds_end x (by rw [htake_eq]; exact List.mem_append_right _ hx)
          have hV1 := (batch_delOrSplit_invariants _ G₀ hVG₀ hBV_split.1 hds1).1
          have hSub := (batch_delOrSplit_invariants _ _ hV1 hBV_split.2 hds2).2.1
          rw [← applyBatch_append, ← htake_eq] at hSub
          exact hSub heG_end
        have hinv_p1 := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + p + 1) (by omega)).1
        have hu_p := hmatch p hp_lt
        have hstep_res : (step (runState (L := L) G₀ q sparsify us (k₀ + p)) (U[p]'hp_lt) sparsify).state =
            runState (L := L) G₀ q sparsify us (k₀ + p + 1) := by
          simp [runState, hu_p]
        have hstep_D : (step (runState (L := L) G₀ q sparsify us (k₀ + p)) (U[p]'hp_lt) sparsify).D =
            (runStepOut (L := L) G₀ q sparsify us (k₀ + p)).D := by
          simp [runStepOut, hu_p]
        have hle_step := reembed_step_walkCount_le hVG₀ hL hq hGm₀ hSpec hBV hds (k := k₀ + p)
          (by omega) (U[p]'hp_lt) hu_p eG (by rw [hstep_res, hinv_p1.G_eq]; exact heG_p1) eH
          (by rw [hstep_D]; exact heH_not_step p hp_lt)
        rw [hstep_res] at hle_step
        exact le_trans ih' (by simpa [Nat.add_assoc] using hle_step)
    simpa [hst'] using hback U.length le_rfl
  · have hnotW : eH ∉ walkEdges (piTotal res.state eG) := fun hm => by
      rw [mem_walkEdges_iff] at hm
      rcases hm with ⟨x, hx, rfl⟩
      exact heH_H' (IsWalk.mem_edge hw_end x hx)
    rw [countP_eq_zero_of_not_mem_walkEdges hnotW]
    exact Nat.zero_le _

/-- **D40 batch-trace `countP` (multiplicity) monotonicity**:
in `batchTrace_spec` form, for every step `t < Us.length` with `Us[t]? = some U`,
`eG ∈ res.state.G.E`, and `eH ∉ res.D`, `eH` occurs no more times on `piTotal res.state eG`
than on `piTotal st eG`. -/
theorem batchTrace_walkCount_le {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {Us : List (List Update)}
    (hBV : G₀.BatchIsValid Us.flatten) (hds : ∀ u ∈ Us.flatten, isDelOrSplit u) :
    ∀ t < Us.length, ∀ U, Us[t]? = some U →
      let st := runBatchState (L := L) G₀ q sparsify Us t
      let res := runBatchStepOut (L := L) G₀ q sparsify Us t
      ∀ eG ∈ res.state.G.E, ∀ eH, eH ∉ res.D →
        (piTotal res.state eG).countP (fun x => decide (x.1 = eH)) ≤
          (piTotal st eG).countP (fun x => decide (x.1 = eH)) := by
  intro t ht U ht_some st res eG heG eH hnotD
  have hbt := (batchTrace_spec hVG₀ hL hq hGm₀ hSpec hBV hds).1 t ht.le
  have hbt_step := (batchTrace_spec hVG₀ hL hq hGm₀ hSpec hBV hds).2 t ht U ht_some
  dsimp only [st, res] at hbt_step ⊢
  rw [hbt.1]
  dsimp only [res] at heG hnotD ⊢
  rw [hbt_step.1] at heG hnotD ⊢
  have htake : Us = Us.take (t + 1) ++ Us.drop (t + 1) := (List.take_append_drop (t + 1) Us).symm
  have htake1 : Us.take (t + 1) = Us.take t ++ [U] := by
    rw [List.take_add_one, ht_some]
    simp
  have hflat_pre : batchPrefixLen Us t + U.length ≤ Us.flatten.length := by
    have h1 : batchPrefixLen Us t + U.length = (Us.take (t + 1)).flatten.length := by
      simp [batchPrefixLen, htake1, List.flatten_append, List.length_flatten]
    rw [h1]
    conv_rhs => rw [htake, List.flatten_append, List.length_append]
    exact Nat.le_add_right _ _
  have hmatch : ∀ (i : ℕ) (hi : i < U.length),
      Us.flatten[batchPrefixLen Us t + i]? = some (U[i]'hi) := by
    intro i hi
    have hflat : Us.flatten = (Us.take t).flatten ++ U ++ (Us.drop (t + 1)).flatten := by
      conv_lhs => rw [htake, htake1, List.flatten_append, List.flatten_append]
      simp [List.append_assoc]
    rw [hflat, List.append_assoc]
    have hpref : (Us.take t).flatten.length ≤ batchPrefixLen Us t + i := by simp [batchPrefixLen]
    rw [List.getElem?_append_right hpref]
    have hidx : batchPrefixLen Us t + i - (Us.take t).flatten.length = i := by simp [batchPrefixLen]
    rw [hidx, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  exact reembed_batch_walkCount_le hVG₀ hL hq hGm₀ hSpec hBV hds hflat_pre hmatch eG heG eH hnotD

end

end WalkCountMono

end MinCostFlow.DynSpanner
