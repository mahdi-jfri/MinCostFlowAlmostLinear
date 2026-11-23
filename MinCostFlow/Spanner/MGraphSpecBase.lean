module

public import MinCostFlow.Basic.Graph
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Runtime
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.DynSpanner.Tools

import MinCostFlow.Spanner.Embedding
import MinCostFlow.Spanner.Subgraph
import MinCostFlow.Spanner.Algorithm
import MinCostFlow.Spanner.Theorem81
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Walks, Lengths and Congestion for `sparsifyMG`

This file holds the first part of the material of `MGraphSpec.lean`, split off to keep files
small. `MGraphSpec.lean` gives the overview.
-/

public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Exact length equality for `embToCited` -/

lemma length_embToCited_eq (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    length (toCitedJ J) (embToCited H' J embJH) = embJH.length J := by
  refine le_antisymm (length_embToCited_le H' J embJH) ?_
  unfold Embedding.length
  by_cases hE : J.E.Nonempty
  · obtain ⟨eMax, heMax, hsup⟩ := Finset.exists_mem_eq_sup J.E hE fun e => (embJH e).length
    rw [hsup]
    have hj_lt : (vertsOf J.E).idxOf eMax < (toCitedJ J).m := by
      rw [toCitedJ_m]
      exact idxOf_lt_card heMax
    have he_eq : (vertsOf J.E).getD ((vertsOf J.E).idxOf eMax) 0 = eMax :=
      getD_vertsOf_idxOf heMax
    have hstep : (embToCited H' J embJH ((vertsOf J.E).idxOf eMax)).edges.length =
        (embJH eMax).length := by
      unfold embToCited walkToCited
      dsimp only
      rw [he_eq]
      split_ifs with hnil
      · simp [List.isEmpty_iff.mp hnil, Walk.empty]
      · simp
    rw [← hstep]
    exact edges_length_le_length _ hj_lt
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE]
    simp

/-! ## Reverse walk, length, and congestion lemmas for `citedEmbToMGraph` -/

private lemma citedWalkSteps_isWalk_aux (J : MGraph) (hJ : J.IsValid)
    (G : Cited.Graph) (kept : List ℕ) (hkept : ∀ k ∈ kept, k < J.m)
    (hG_edges : G.edges = kept.map fun k => (toCitedJ J).edges.getD k (0, 0))
    {v_c : ℕ} :
    ∀ (cs vs : List ℕ) (u_c : ℕ),
      u_c < J.V.card →
      vs.length = cs.length + 1 →
      vs.head? = some u_c →
      vs.getLast? = some v_c →
      (∀ c ∈ cs, c < G.m) →
      (∀ i < cs.length,
        Walk.EdgeMatches (G.edges.getD (cs.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      (outJtilde J kept).IsWalk ((vertsOf J.V).getD u_c 0) ((vertsOf J.V).getD v_c 0)
        (citedWalkSteps (vertsOf J.E) G kept vs cs) := by
  intro cs
  induction cs with
  | nil =>
    intro vs u_c _ hlen hhead hlast _ _
    rcases List.length_eq_one_iff.mp hlen with ⟨w, hw⟩
    rw [hw] at hhead hlast
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    rw [← hhead, hlast, hw]
    exact .nil _
  | cons c cs ih =>
    intro vs u_c _ hlen hhead hlast hedges hmatch
    rcases List.length_eq_succ_iff.mp (show vs.length = (cs.length + 1) + 1 from hlen) with
      ⟨u, vs', rfl, hlen_sub⟩
    rcases List.length_eq_succ_iff.mp hlen_sub with ⟨w, vs'', rfl, hlen_tail⟩
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst u
    have hc_lt : c < kept.length := by
      have hc1 := hedges c List.mem_cons_self
      simpa [Graph.m, hG_edges] using hc1
    have hk_mem : kept.getD c 0 ∈ kept := by
      rw [List.getD_eq_getElem _ _ hc_lt]
      exact List.getElem_mem hc_lt
    have hk_lt : kept.getD c 0 < J.m := hkept _ hk_mem
    set eOrig := (vertsOf J.E).getD (kept.getD c 0) 0
    have heOrig_J : eOrig ∈ J.E := getD_vertsOf_mem hk_lt
    have heOrig_sub : eOrig ∈ (outJtilde J kept).E := by
      unfold outJtilde
      dsimp only
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨kept.getD c 0, hk_mem, rfl⟩)
    have heG_eq : G.edges.getD c (0, 0) =
        ((vertsOf J.V).idxOf (J.tail eOrig), (vertsOf J.V).idxOf (J.head eOrig)) := by
      have hk' : kept[c]'hc_lt < (vertsOf J.E).length := by
        rw [vertsOf_length, ← List.getD_eq_getElem _ 0 hc_lt]
        exact hk_lt
      have heO : eOrig = (vertsOf J.E)[kept[c]'hc_lt]'hk' := by
        dsimp only [eOrig]
        rw [List.getD_eq_getElem _ 0 hc_lt, List.getD_eq_getElem _ 0 hk']
      simp only [List.getD_eq_getElem?_getD, hG_edges, List.getElem?_map,
        List.getElem?_eq_getElem hc_lt, Option.map_some, Option.getD_some, toCitedJ,
        List.getElem?_eq_getElem hk', heO]
    have hm0 := hmatch 0 (by simp)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      zero_add, List.getElem?_cons_succ] at hm0
    rw [← List.getD_eq_getElem?_getD, heG_eq] at hm0
    have hw_lt : w < J.V.card := by
      rcases hm0 with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [← h2]; exact idxOf_lt_card (hJ eOrig heOrig_J).2
      · rw [← h2]; exact idxOf_lt_card (hJ eOrig heOrig_J).1
    let eG := G.edges.getD c (0, 0)
    let dir := decide (eG.1 = u_c ∧ eG.2 = w)
    have hsrc : (outJtilde J kept).src (eOrig, dir) = (vertsOf J.V).getD u_c 0 := by
      change (if dir = true then J.tail eOrig else J.head eOrig) = (vertsOf J.V).getD u_c 0
      by_cases hdir : eG.1 = u_c ∧ eG.2 = w
      · have hd : dir = true := decide_eq_true hdir
        simp only [hd, ↓reduceIte]
        have he1 : (vertsOf J.V).idxOf (J.tail eOrig) = u_c := by
          have := hdir.1; simp only [eG, heG_eq] at this; exact this
        rw [← he1, getD_vertsOf_idxOf (hJ eOrig heOrig_J).1]
      · have hd : dir = false := decide_eq_false hdir
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases hm0 with hfwd | hrev
        · rw [← heG_eq] at hfwd; exact (hdir hfwd).elim
        · rw [← hrev.1, getD_vertsOf_idxOf (hJ eOrig heOrig_J).2]
    have hdst : (outJtilde J kept).dst (eOrig, dir) = (vertsOf J.V).getD w 0 := by
      change (if dir = true then J.head eOrig else J.tail eOrig) = (vertsOf J.V).getD w 0
      by_cases hdir : eG.1 = u_c ∧ eG.2 = w
      · have hd : dir = true := decide_eq_true hdir
        simp only [hd, ↓reduceIte]
        have he2 : (vertsOf J.V).idxOf (J.head eOrig) = w := by
          have := hdir.2; simp only [eG, heG_eq] at this; exact this
        rw [← he2, getD_vertsOf_idxOf (hJ eOrig heOrig_J).2]
      · have hd : dir = false := decide_eq_false hdir
        simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases hm0 with hfwd | hrev
        · rw [← heG_eq] at hfwd; exact (hdir hfwd).elim
        · rw [← hrev.2, getD_vertsOf_idxOf (hJ eOrig heOrig_J).1]
    have hrest_last : (w :: vs'').getLast? = some v_c := by
      have hlast1 : (u_c :: w :: vs'').getLast? = (w :: vs'').getLast? := by
        cases vs'' <;> rfl
      rwa [← hlast1]
    have htail_walk : (outJtilde J kept).IsWalk ((vertsOf J.V).getD w 0) ((vertsOf J.V).getD v_c 0)
        (citedWalkSteps (vertsOf J.E) G kept (w :: vs'') cs) :=
      ih (w :: vs'') w hw_lt (by simpa [Nat.succ_eq_add_one] using hlen_tail) rfl hrest_last
        (fun c' hc' => hedges c' (List.mem_cons_of_mem _ hc'))
        (fun i hi => by simpa using hmatch (i + 1) (Nat.succ_lt_succ hi))
    change (outJtilde J kept).IsWalk ((vertsOf J.V).getD u_c 0) ((vertsOf J.V).getD v_c 0)
      ((eOrig, dir) :: citedWalkSteps (vertsOf J.E) G kept (w :: vs'') cs)
    exact .cons heOrig_sub hsrc (hdst ▸ htail_walk)

private lemma citedWalkSteps_isWalk (J : MGraph) (hJ : J.IsValid)
    (G : Cited.Graph) (kept : List ℕ) (hkept : ∀ k ∈ kept, k < J.m)
    (hG_n : G.n = J.n)
    (hG_edges : G.edges = kept.map fun k => (toCitedJ J).edges.getD k (0, 0)) :
    ∀ {u_c v_c : ℕ} {P : Walk},
      P.IsWalk G u_c v_c →
      (outJtilde J kept).IsWalk ((vertsOf J.V).getD u_c 0) ((vertsOf J.V).getD v_c 0)
        (citedWalkSteps (vertsOf J.E) G kept P.verts P.edges) := by
  intro u_c v_c P hP
  rcases hP with ⟨hu_n, hv_n, ⟨hPv, hPe, huv⟩ | ⟨_, hlen, hhead, hlast, hedges, hmatch⟩⟩
  · rw [hPv, hPe, huv]
    exact .nil _
  · have hu_c : u_c < J.V.card := by simpa [hG_n, MGraph.n] using hu_n
    exact citedWalkSteps_isWalk_aux J hJ G kept hkept hG_edges
      P.edges P.verts u_c hu_c hlen hhead hlast hedges hmatch

lemma citedEmbToMGraph_isEmbedding {J : MGraph} (hJ : J.IsValid)
    {G : Cited.Graph} {kept : List ℕ} {emb : ℕ → Walk}
    (hkept : ∀ k ∈ kept, k < J.m)
    (hG_n : G.n = J.n)
    (hG_edges : G.edges = kept.map fun k => (toCitedJ J).edges.getD k (0, 0))
    (hemb : IsEmbedding (toCitedJ J) G emb) :
    (citedEmbToMGraph J G kept emb).IsEmbedding J (outJtilde J kept) := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro e he
  unfold citedEmbToMGraph
  simp only [he, ↓reduceIte]
  have hj_lt : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
    rw [toCitedJ_m]; exact idxOf_lt_card he
  have hw := hemb.2 ((vertsOf J.E).idxOf e) hj_lt
  have h1 : (toCitedJ J).edges[(vertsOf J.E).idxOf e]'hj_lt =
      ((vertsOf J.V).idxOf (J.tail e), (vertsOf J.V).idxOf (J.head e)) := by
    have hj_len : (vertsOf J.E).idxOf e < (vertsOf J.E).length := by
      rw [vertsOf_length]; exact idxOf_lt_card he
    rw [← List.getD_eq_getElem _ (0, 0) hj_lt]
    dsimp only [toCitedJ]
    rw [List.getD_eq_getElem _ (0, 0) (by simpa using hj_len), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hj_len, getD_vertsOf_idxOf he]
  rw [h1] at hw
  have hw_mg := citedWalkSteps_isWalk J hJ G kept hkept hG_n hG_edges hw
  rwa [getD_vertsOf_idxOf (hJ e he).1, getD_vertsOf_idxOf (hJ e he).2] at hw_mg

private lemma citedWalkSteps_length (jEs : List ℕ) (G : Cited.Graph) (kept : List ℕ) :
    ∀ (vs cs : List ℕ), (citedWalkSteps jEs G kept vs cs).length ≤ cs.length
  | _ :: _ :: vs, _ :: cs => by
    simp only [citedWalkSteps, List.length_cons]
    exact Nat.succ_le_succ (citedWalkSteps_length jEs G kept (_ :: vs) cs)
  | [], _ => Nat.zero_le _
  | [_], _ => Nat.zero_le _
  | _ :: _ :: _, [] => Nat.zero_le _

lemma length_comp_mgraph_le {J : MGraph} {embJH : MinCostFlow.Embedding}
    {G : Cited.Graph} {kept : List ℕ} {emb : ℕ → Walk}
    (hkept : ∀ k ∈ kept, k < J.m)
    (hemb_mg : (citedEmbToMGraph J G kept emb).IsEmbedding J (outJtilde J kept)) :
    (MinCostFlow.Embedding.comp embJH (citedEmbToMGraph J G kept emb)).length J ≤
      length (toCitedJ J) emb * embJH.length J := by
  unfold MinCostFlow.Embedding.length
  apply Finset.sup_le
  intro e he
  unfold MinCostFlow.Embedding.comp
  have hsteps_len : (citedEmbToMGraph J G kept emb e).length ≤ length (toCitedJ J) emb := by
    unfold citedEmbToMGraph
    simp only [he, ↓reduceIte]
    have hj_lt : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
      rw [toCitedJ_m]; exact idxOf_lt_card he
    exact le_trans (citedWalkSteps_length _ _ _ _ _) (edges_length_le_length emb hj_lt)
  have hwalk := hemb_mg.2 e he
  have hbound : ∀ P : List (ℕ × Bool), ∀ u v, (outJtilde J kept).IsWalk u v P →
      (P.flatMap fun x => if x.2 then embJH x.1 else walkRev (embJH x.1)).length ≤
        P.length * embJH.length J := by
    intro P
    induction P with
    | nil => intro _ _ _; simp
    | cons x xs ih =>
      intro u v hw
      cases hw with
      | cons hx _ hxs =>
        have hxJ : x.1 ∈ J.E := (outJtilde_isSubgraph J kept hkept).2.1 hx
        have hstep_len : (if x.2 then embJH x.1 else walkRev (embJH x.1)).length ≤ embJH.length J := by
          have hle : (embJH x.1).length ≤ embJH.length J :=
            Finset.le_sup (f := fun e => (embJH e).length) hxJ
          cases x.2 <;> simpa [walkRev] using hle
        have hrest := ih _ _ hxs
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith only [hstep_len, hrest]
  exact le_trans (hbound _ _ _ hwalk) (Nat.mul_le_mul_right _ hsteps_len)

/-! ## Vertex preservation for `Cited.compose` and congestion transfer back to `MGraph` -/

lemma mem_verts_composeAux_of_mem {B C : Graph} {embBC : ℕ → Walk}
    (hB : B.IsValid) (hBC : IsEmbedding B C embBC) :
    ∀ (js vs : List ℕ) (u v : ℕ),
      vs.length = js.length + 1 →
      vs.head? = some u →
      vs.getLast? = some v →
      (∀ j ∈ js, j < B.m) →
      (∀ i : ℕ, i < js.length →
        Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      v < B.n →
      ∀ j ∈ js, ∀ {x : ℕ}, x ∈ (embBC j).verts → x ∈ (composeAux B embBC vs js).verts := by
  intro js
  induction js with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hj; simp at hj
  | cons j js ih =>
    intro vs u v hlen hhead hlast hedges hmatch hv_lt j' hj' x hx
    rcases List.length_eq_succ_iff.mp (show vs.length = (js.length + 1) + 1 from hlen) with
      ⟨u₀, vs', rfl, hlen1⟩
    rcases List.length_eq_succ_iff.mp hlen1 with ⟨w, vs'', rfl, hlen2⟩
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst u₀
    have hj_lt : j < B.m := hedges j List.mem_cons_self
    have hm0 := hmatch 0 (by simp)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      zero_add, List.getElem?_cons_succ] at hm0
    rw [← List.getD_eq_getElem?_getD] at hm0
    have hw_lt : w < B.n := by
      rw [List.getD_eq_getElem _ _ hj_lt] at hm0
      have hb := hB _ (List.getElem_mem hj_lt)
      rcases hm0 with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2 ▸ hb.2
      · exact h2 ▸ hb.1
    let e := B.edges.getD j (0, 0)
    let step := if e.1 = u ∧ e.2 = w then embBC j else (embBC j).reverse
    let rest := composeAux B embBC (w :: vs'') js
    have hstep_walk : step.IsWalk C u w := by
      have he_raw := hBC.2 j hj_lt
      rw [← List.getD_eq_getElem _ (0, 0) hj_lt] at he_raw
      by_cases hf : e.1 = u ∧ e.2 = w
      · simp only [step, hf]
        exact hf.1 ▸ hf.2 ▸ he_raw
      · simp only [step, hf, ↓reduceIte]
        rcases hm0 with hf0 | hr0
        · exact (hf hf0).elim
        · exact Walk.isWalk_reverse (hr0.1 ▸ hr0.2 ▸ he_raw)
    have hrest_last : (w :: vs'').getLast? = some v := by
      have h1 : (u :: w :: vs'').getLast? = (w :: vs'').getLast? := by
        cases vs'' <;> rfl
      rwa [← h1]
    have hrest_edges : ∀ j'' ∈ js, j'' < B.m := fun j'' h => hedges j'' (List.mem_cons_of_mem _ h)
    have hrest_match : ∀ i < js.length,
        Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0))
          ((w :: vs'').getD i 0) ((w :: vs'').getD (i + 1) 0) := by
      intro i hi
      simpa using hmatch (i + 1) (Nat.succ_lt_succ hi)
    have hrest_walk : rest.IsWalk C w v :=
      composeAux_isWalk hBC js (w :: vs'') w v (by simpa [Nat.succ_eq_add_one] using hlen2)
        rfl hrest_last hrest_edges hrest_match hv_lt
    have hcomp_eq : composeAux B embBC (u :: w :: vs'') (j :: js) = step.append rest := rfl
    rw [hcomp_eq, Walk.mem_verts_append_iff hstep_walk hrest_walk x]
    rcases List.mem_cons.mp hj' with rfl | hj''
    · left
      by_cases hf : e.1 = u ∧ e.2 = w
      · simp only [step, hf]; exact hx
      · simp only [step, hf, ↓reduceIte]; simpa [Walk.reverse] using hx
    · right
      exact ih (w :: vs'') w v (by simpa [Nat.succ_eq_add_one] using hlen2)
        rfl hrest_last hrest_edges hrest_match hv_lt j' hj'' hx

lemma mem_verts_compose_of_mem {A B C : Graph} {embBC embAB : ℕ → Walk}
    (hB : B.IsValid) (hBC : IsEmbedding B C embBC) (hAB : IsEmbedding A B embAB)
    {jA : ℕ} (hjA : jA < A.m) {jB : ℕ} (hjB : jB ∈ (embAB jA).edges)
    {x : ℕ} (hx : x ∈ (embBC jB).verts) :
    x ∈ (compose B embBC embAB jA).verts := by
  have hw := hAB.2 jA hjA
  rcases hw.2.2 with ⟨_, hPe, _⟩ | ⟨_, hlen, hhead, hlast, hedges, hmatch⟩
  · simp [hPe] at hjB
  · exact mem_verts_composeAux_of_mem hB hBC (embAB jA).edges (embAB jA).verts _ _
      hlen hhead hlast hedges hmatch hw.2.1 jB hjB hx

private lemma mgraph_comp_mem_step_of_nonempty {J H' outJ : MGraph}
    (hsub : J.IsSubgraph outJ) (embJH : MinCostFlow.Embedding) (hJH : embJH.IsEmbedding J H') :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, outJ.IsWalk u v P →
      let Q := P.flatMap fun x => if x.2 then embJH x.1 else walkRev (embJH x.1)
      Q ≠ [] → ∀ z ∈ H'.walkVertices u Q,
        ∃ y ∈ P, embJH y.1 ≠ [] ∧ z ∈ H'.walkVertices (J.tail y.1) (embJH y.1)
  | _, _, [], .nil _, hQne, _, _ => by simp at hQne
  | u, v, x :: xs, .cons hx hsrc hP, hQne, z, hz => by
    let s := if x.2 then embJH x.1 else walkRev (embJH x.1)
    let rest := xs.flatMap fun x => if x.2 then embJH x.1 else walkRev (embJH x.1)
    have hxJ : x.1 ∈ J.E := hsub.2.1 hx
    have hth := hsub.2.2 x.1 hx
    have hs_walk : H'.IsWalk u (outJ.dst x) s := by
      have hw := hJH.2 x.1 hxJ
      cases hxb : x.2
      · have hu : u = J.head x.1 := by simpa [MGraph.src, hxb, hth.2] using hsrc.symm
        have hd : outJ.dst x = J.tail x.1 := by simp [MGraph.dst, hxb, hth.1]
        simp only [s, hxb, Bool.false_eq_true, ↓reduceIte, hu, hd]
        exact mgraph_isWalk_walkRev hw
      · have hu : u = J.tail x.1 := by simpa [MGraph.src, hxb, hth.1] using hsrc.symm
        have hd : outJ.dst x = J.head x.1 := by simp [MGraph.dst, hxb, hth.2]
        simp only [s, hxb, ↓reduceIte, hu, hd]
        exact hw
    have hsplit : z ∈ H'.walkVertices u s ∨ z ∈ H'.walkVertices (outJ.dst x) rest := by
      have h1 := (mgraph_walkVertices_append hs_walk z (Q := rest)).mp
      exact h1 (by simpa [List.flatMap_cons, s, rest] using hz)
    by_cases hsne : s ≠ []
    · have hxne : embJH x.1 ≠ [] := by
        intro h0
        dsimp only [s] at hsne
        cases x.2 <;> simp [h0, walkRev] at hsne
      by_cases hzs : z ∈ H'.walkVertices u s
      · refine ⟨x, List.mem_cons_self, hxne, ?_⟩
        cases hxb : x.2
        · have hu : u = J.head x.1 := by simpa [MGraph.src, hxb, hth.2] using hsrc.symm
          simp only [s, hxb, Bool.false_eq_true, ↓reduceIte, hu] at hzs
          exact (mgraph_walkVertices_walkRev (hJH.2 x.1 hxJ) z).mp hzs
        · have hu : u = J.tail x.1 := by simpa [MGraph.src, hxb, hth.1] using hsrc.symm
          simp only [s, hxb, ↓reduceIte, hu] at hzs
          exact hzs
      · have hz_rest : z ∈ H'.walkVertices (outJ.dst x) rest := by
          rcases hsplit with h1 | h2
          · exact (hzs h1).elim
          · exact h2
        have hrest_ne : rest ≠ [] := by
          intro h0
          rw [h0] at hz_rest
          simp only [MGraph.walkVertices, List.map_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hz_rest
          subst hz_rest
          exact hzs (mgraph_walkVertices_last_of_isWalk hs_walk)
        obtain ⟨y, hy_mem, hyne, hyz⟩ :=
          mgraph_comp_mem_step_of_nonempty hsub embJH hJH hP hrest_ne z hz_rest
        exact ⟨y, List.mem_cons_of_mem _ hy_mem, hyne, hyz⟩
    · have hs0 : s = [] := Classical.not_not.mp hsne
      have hrest_ne : rest ≠ [] := by
        simpa [List.flatMap_cons, s, rest, hs0] using hQne
      have huw : u = outJ.dst x := by
        rw [hs0] at hs_walk
        exact isWalk_dst_eq_of_nil hs_walk
      have hz_rest : z ∈ H'.walkVertices (outJ.dst x) rest := by
        have hrew : s ++ rest = rest := by simp [hs0]
        simpa [← huw, List.flatMap_cons, s, rest, hrew] using hz
      obtain ⟨y, hy_mem, hyne, hyz⟩ :=
        mgraph_comp_mem_step_of_nonempty hsub embJH hJH hP hrest_ne z hz_rest
      exact ⟨y, List.mem_cons_of_mem _ hy_mem, hyne, hyz⟩

private lemma citedWalkSteps_mem_step (J : MGraph) (hJ : J.IsValid)
    (G : Cited.Graph) (kept : List ℕ) (hkept : ∀ k ∈ kept, k < J.m) :
    ∀ (vs cs : List ℕ) {y : ℕ × Bool},
      y ∈ citedWalkSteps (vertsOf J.E) G kept vs cs →
      ∃ c ∈ cs, y.1 = (vertsOf J.E).getD (kept.getD c 0) 0
  | _ :: _ :: vs, c :: cs, y, hy => by
    simp only [citedWalkSteps, List.mem_cons] at hy
    rcases hy with rfl | hy'
    · exact ⟨c, List.mem_cons_self, rfl⟩
    · obtain ⟨c', hc', heq⟩ := citedWalkSteps_mem_step J hJ G kept hkept (_ :: vs) cs hy'
      exact ⟨c', List.mem_cons_of_mem _ hc', heq⟩
  | [], _, _, hy => by simp [citedWalkSteps] at hy
  | [_], _, _, hy => by simp [citedWalkSteps] at hy
  | _ :: _ :: _, [], _, hy => by simp [citedWalkSteps] at hy

lemma vcong_comp_mgraph_le {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (_hH' : H'.IsValid) (hJ : J.IsValid) (hembJH : embJH.IsEmbedding J H')
    {G : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hG_valid : G.IsValid) (hkept : ∀ k ∈ kept, k < J.m)
    (hG_n : G.n = J.n)
    (hG_edges : G.edges = kept.map fun k => (toCitedJ J).edges.getD k (0, 0))
    (hemb_J : IsEmbedding (toCitedJ J) G embJJtilde)
    (hemb_G : IsEmbedding G (toCitedH H' J embJH) (restrictEmb (embToCited H' J embJH) kept)) :
    (MinCostFlow.Embedding.comp embJH (citedEmbToMGraph J G kept embJJtilde)).vcong J H' (fun _ => 1) ≤
      (J.maxDeg : ℝ) + vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1)
        (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) := by
  let outEmb := citedEmbToMGraph J G kept embJJtilde
  have hsub := outJtilde_isSubgraph J kept hkept
  have hemb_mg : outEmb.IsEmbedding J (outJtilde J kept) :=
    citedEmbToMGraph_isEmbedding hJ hkept hG_n hG_edges hemb_J
  have hcit_nn : 0 ≤ vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1)
      (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) :=
    vcong_nonneg _ _ _ _
  unfold MinCostFlow.Embedding.vcong
  split_ifs with hHV
  · apply Finset.sup'_le hHV
    intro vH hvH
    by_cases hvUsed : vH ∈ usedHVerts H' J embJH
    · let v_cit := (hVerts H' J embJH).idxOf vH
      have hv_lt : v_cit < (toCitedH H' J embJH).n := hVerts_idxOf_lt hvUsed
      let S_all := J.E.filter fun eJ =>
        vH ∈ H'.walkVertices (J.tail eJ) (MinCostFlow.Embedding.comp embJH outEmb eJ)
      let S_empty := J.E.filter fun eJ =>
        MinCostFlow.Embedding.comp embJH outEmb eJ = [] ∧ vH = J.tail eJ
      let S_ne := J.E.filter fun eJ =>
        MinCostFlow.Embedding.comp embJH outEmb eJ ≠ [] ∧
          vH ∈ H'.walkVertices (J.tail eJ) (MinCostFlow.Embedding.comp embJH outEmb eJ)
      have hS_sub : S_all ⊆ S_empty ∪ S_ne := by
        intro eJ heJ
        rcases Finset.mem_filter.mp heJ with ⟨heJE, hve⟩
        by_cases h0 : MinCostFlow.Embedding.comp embJH outEmb eJ = []
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heJE, h0, by
            rw [h0] at hve; simpa [MGraph.walkVertices] using hve⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heJE, h0, hve⟩)
      have hcard_empty : S_empty.card ≤ J.maxDeg := by
        by_cases hvJ : vH ∈ J.V
        · have hsub1 : S_empty ⊆ J.E.filter fun e => J.tail e = vH := by
            intro e he
            rcases Finset.mem_filter.mp he with ⟨heE, _, htv⟩
            exact Finset.mem_filter.mpr ⟨heE, htv.symm⟩
          have h1 : S_empty.card ≤ (J.E.filter fun e => J.tail e = vH).card :=
            Finset.card_le_card hsub1
          have h2 : (J.E.filter fun e => J.tail e = vH).card ≤ J.deg vH :=
            Nat.le_add_right _ _
          exact le_trans (le_trans h1 h2) (Finset.le_sup (f := J.deg) hvJ)
        · have h0 : S_empty = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro e he
            rcases Finset.mem_filter.mp he with ⟨heE, _, htv⟩
            exact hvJ (htv ▸ (hJ e heE).1)
          rw [h0, Finset.card_empty]
          exact Nat.zero_le _
      have hcard_ne : S_ne.card ≤ ((Finset.range (toCitedJ J).m).filter fun j =>
          v_cit ∈ (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde j).verts).card := by
        refine Finset.card_le_card_of_injOn (fun e => (vertsOf J.E).idxOf e) ?_ ?_
        · intro e he
          rw [Finset.mem_coe, Finset.mem_filter] at he
          rcases he with ⟨heE, hcomp_ne, hmem_v⟩
          have hj_lt : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
            rw [toCitedJ_m]; exact idxOf_lt_card heE
          have hP_walk := (citedEmbToMGraph_isEmbedding hJ hkept hG_n hG_edges hemb_J).2 e heE
          have hP_sub : (outJtilde J kept).IsWalk (J.tail e) (J.head e) (outEmb e) := hP_walk
          have hcomp_eq : (outEmb e).flatMap (fun x => if x.2 then embJH x.1 else walkRev (embJH x.1)) =
              MinCostFlow.Embedding.comp embJH outEmb e := rfl
          obtain ⟨y, hy_mem, hyne, hyz⟩ :=
            mgraph_comp_mem_step_of_nonempty hsub embJH hembJH hP_sub
              (hcomp_eq ▸ hcomp_ne) vH hmem_v
          have hy_steps : y ∈ citedWalkSteps (vertsOf J.E) G kept
              (embJJtilde ((vertsOf J.E).idxOf e)).verts
              (embJJtilde ((vertsOf J.E).idxOf e)).edges := by
            simpa [outEmb, citedEmbToMGraph, heE] using hy_mem
          obtain ⟨c, hc_edges, hy1⟩ :=
            citedWalkSteps_mem_step J hJ G kept hkept _ _ hy_steps
          have hc_lt : c < G.m := by
            have hwalk_J := hemb_J.2 ((vertsOf J.E).idxOf e) hj_lt
            rcases hwalk_J.2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩
            · simp [hPe] at hc_edges
            · exact hedges c hc_edges
          have hk_lt : kept.getD c 0 < J.m := by
            have hc_kept : c < kept.length := by simpa [Graph.m, hG_edges] using hc_lt
            exact hkept _ (List.getD_eq_getElem _ 0 hc_kept ▸ List.getElem_mem hc_kept)
          have hve_cit : v_cit ∈ ((restrictEmb (embToCited H' J embJH) kept) c).verts := by
            change v_cit ∈ (embToCited H' J embJH (kept.getD c 0)).verts
            unfold embToCited walkToCited
            dsimp only
            rw [← hy1]
            split_ifs with hnil
            · exfalso; exact hyne (List.isEmpty_iff.mp hnil)
            · exact List.mem_map.mpr ⟨vH, hyz, rfl⟩
          have hmem_comp :=
            mem_verts_compose_of_mem hG_valid hemb_G hemb_J hj_lt hc_edges hve_cit
          exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hmem_comp⟩)
        · intro e₁ he₁ e₂ he₂ heq
          have he₁E := (Finset.mem_filter.mp (Finset.mem_coe.mp he₁)).1
          have he₂E := (Finset.mem_filter.mp (Finset.mem_coe.mp he₂)).1
          have h1 := getD_vertsOf_idxOf he₁E
          have h2 := getD_vertsOf_idxOf he₂E
          dsimp only at heq
          rw [heq] at h1
          exact h1.symm.trans h2
      have hv_mg : (MinCostFlow.Embedding.comp embJH outEmb).vcongAt J H' (fun _ => 1) vH =
          (S_all.card : ℝ) := by
        unfold MinCostFlow.Embedding.vcongAt
        simp [S_all]
      have hv_cit : vcongAt (toCitedJ J) (fun _ => 1)
          (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) v_cit =
          (((Finset.range (toCitedJ J).m).filter fun j =>
            v_cit ∈ (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde j).verts).card : ℝ) := by
        unfold vcongAt
        simp
      have htot_card : S_all.card ≤ J.maxDeg +
          ((Finset.range (toCitedJ J).m).filter fun j =>
            v_cit ∈ (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde j).verts).card :=
        le_trans (Finset.card_le_card hS_sub)
          (le_trans (Finset.card_union_le S_empty S_ne) (Nat.add_le_add hcard_empty hcard_ne))
      have hle_at : (MinCostFlow.Embedding.comp embJH outEmb).vcongAt J H' (fun _ => 1) vH ≤
          (J.maxDeg : ℝ) + vcongAt (toCitedJ J) (fun _ => 1)
            (compose G (restrictEmb (embToCited H' J embJH) kept) embJJtilde) v_cit := by
        rw [hv_mg, hv_cit]
        exact_mod_cast htot_card
      exact le_trans hle_at (add_le_add le_rfl (vcongAt_le_vcong _ _ hv_lt))
    · have hv_zero : (MinCostFlow.Embedding.comp embJH outEmb).vcongAt J H' (fun _ => 1) vH = 0 := by
        unfold MinCostFlow.Embedding.vcongAt
        have hemp : (J.E.filter fun eJ =>
            vH ∈ H'.walkVertices (J.tail eJ) (MinCostFlow.Embedding.comp embJH outEmb eJ)) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro eJ heJ
          rcases Finset.mem_filter.mp heJ with ⟨heJE, hv_mem⟩
          have ht_used : J.tail eJ ∈ usedHVerts H' J embJH :=
            Finset.mem_union_left _ (hJ eJ heJE).1
          by_cases hcomp0 : MinCostFlow.Embedding.comp embJH outEmb eJ = []
          · rw [hcomp0] at hv_mem
            simp only [MGraph.walkVertices, List.map_nil, List.mem_cons, List.not_mem_nil,
              or_false] at hv_mem
            exact hvUsed (hv_mem ▸ ht_used)
          · have hP_walk := hemb_mg.2 eJ heJE
            have hcomp_eq : (outEmb eJ).flatMap
                (fun x => if x.2 then embJH x.1 else walkRev (embJH x.1)) =
                MinCostFlow.Embedding.comp embJH outEmb eJ := rfl
            obtain ⟨y, hy_mem, _, hyz⟩ :=
              mgraph_comp_mem_step_of_nonempty hsub embJH hembJH hP_walk
                (hcomp_eq ▸ hcomp0) vH hv_mem
            have hyJ : y.1 ∈ J.E := hsub.2.1 (mgraph_mem_walkVertices_src_dst hP_walk y hy_mem).1
            exact hvUsed (Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨y.1, hyJ, List.mem_toFinset.mpr hyz⟩))
        rw [hemp]
        simp
      rw [hv_zero]
      exact add_nonneg (Nat.cast_nonneg _) hcit_nn
  · exact add_nonneg (Nat.cast_nonneg _) hcit_nn

end MinCostFlow.Spanner
