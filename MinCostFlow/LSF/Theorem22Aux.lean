module

public import MinCostFlow.LSF.Tools
public import MinCostFlow.LSF.Model
public import MinCostFlow.Statement.Cited.AbrahamNeiman
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Auxiliary Graph, Forest, Cut-Edge, and Bridge Constructions for Theorem 2.2

This file provides the structural graph-theoretic pieces used by `MinCostFlow.LSF.Theorem22` to
derive `HasLSSTSpec` from `Cited.LowStretchSpanningTree` (`[AN19]`):

1. Logarithm bounds (`logLogFactor_bounds`, `one_le_log_add_two_sq`).
2. Cut-parity lemmas (`walk_mem_cut_iff`, `isPath_no_unique_cut_edge`) showing a simple path whose
   endpoints lie on the same side of a cut cannot traverse the cut's unique crossing edge.
3. Degree-1 leaf cycle exclusion (`no_cycle_using_leaf`) and `attachVerts` (attaching remaining
   vertices to a spanning tree preserves spanning-tree structure without changing paths inside the
   original vertex set).
4. `connected_card_ge` and `isForest_of_connected_card_le` (a connected graph on `n ≥ 1` vertices
   with at most `n - 1` edges is a forest).
5. `bridgeVerts` and `gvWithBridges` connecting the components of `G_v` on its non-loop active
   vertex set using fewer than `|E(G_v)|` cut-edges.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Logarithm bounds -/

lemma one_lt_log_add_two {n : ℕ} (hn : 1 ≤ n) : 1 < Real.log ((n : ℝ) + 2) := by
  have h16 : (5 / 6 : ℝ) ≤ Real.exp (-(1 / 6 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 6 : ℝ))]
  have hexp16 : Real.exp (1 / 6 : ℝ) ≤ 6 / 5 := by
    have hinv : Real.exp (1 / 6 : ℝ) = (Real.exp (-(1 / 6 : ℝ)))⁻¹ := by
      rw [← Real.exp_neg, neg_neg]
    rw [hinv]
    calc (Real.exp (-(1 / 6 : ℝ)))⁻¹ ≤ (5 / 6 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h16
      _ = 6 / 5 := by norm_num
  have hexp1 : Real.exp 1 < 3 := by
    have hpow : (Real.exp (1 / 6 : ℝ)) ^ 6 ≤ (6 / 5 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hexp16 6
    have hexp_pow : Real.exp 1 = (Real.exp (1 / 6 : ℝ)) ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hexp_pow]
    linarith [hpow, show (6 / 5 : ℝ) ^ 6 < 3 by norm_num]
  have hexp : Real.exp 1 < (n : ℝ) + 2 := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc (1 : ℝ)
      = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log ((n : ℝ) + 2) := Real.log_lt_log (Real.exp_pos 1) hexp

lemma one_le_log_add_two_sq {n : ℕ} (hn : 1 ≤ n) : 1 ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := by
  have h1 := one_lt_log_add_two hn
  nlinarith

lemma logLogFactor_bounds {n₀ n : ℕ} (hn₀ : 2 ≤ n₀) (hle : n₀ ≤ n) :
    0 ≤ Cited.logLogFactor n₀ ∧ Cited.logLogFactor n₀ ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := by
  have h1 : 1 < Real.log ((n₀ : ℝ) + 2) := one_lt_log_add_two (by omega)
  have hlog_pos : 0 < Real.log ((n₀ : ℝ) + 2) := by linarith
  have hll_pos : 0 ≤ Real.log (Real.log ((n₀ : ℝ) + 2)) := (Real.log_pos h1).le
  have hll_le : Real.log (Real.log ((n₀ : ℝ) + 2)) ≤ Real.log ((n₀ : ℝ) + 2) := by
    linarith [Real.log_le_sub_one_of_pos hlog_pos]
  have hmono : Real.log ((n₀ : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    have : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    linarith
  refine ⟨mul_nonneg hlog_pos.le hll_pos, ?_⟩
  calc Cited.logLogFactor n₀
      = Real.log ((n₀ : ℝ) + 2) * Real.log (Real.log ((n₀ : ℝ) + 2)) := rfl
    _ ≤ Real.log ((n₀ : ℝ) + 2) * Real.log ((n₀ : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hll_le hlog_pos.le
    _ = (Real.log ((n₀ : ℝ) + 2)) ^ 2 := (sq _).symm
    _ ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hlog_pos.le hmono 2

/-! ## Cut-parity for walks and simple paths -/

lemma walk_mem_cut_iff {H : MGraph} {S : Finset ℕ} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : H.IsWalk u v P)
    (hno : ∀ f ∈ walkEdges P, (H.tail f ∈ S ↔ H.head f ∈ S)) :
    u ∈ S ↔ v ∈ S := by
  induction hP with
  | nil _ => exact Iff.rfl
  | @cons u₀ _ x₀ xs _ hsrc _ ih =>
    have hx_edge : x₀.1 ∈ walkEdges (x₀ :: xs) :=
      mem_walkEdges_iff.mpr ⟨x₀.2, List.mem_cons_self⟩
    have hiff_x : H.src x₀ ∈ S ↔ H.dst x₀ ∈ S := by
      have hsame := hno x₀.1 hx_edge
      cases hx2 : x₀.2
      · simp [MGraph.src, MGraph.dst, hx2]; exact hsame.symm
      · simp [MGraph.src, MGraph.dst, hx2]; exact hsame
    have hrest : ∀ f ∈ walkEdges xs, (H.tail f ∈ S ↔ H.head f ∈ S) := fun f hf =>
      hno f (by rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr hf)
    exact (hsrc ▸ hiff_x).trans (ih hrest)

lemma isPath_no_unique_cut_edge {H : MGraph} {S : Finset ℕ} {e_cut : ℕ}
    {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : H.IsPath u v P)
    (hsame : u ∈ S ↔ v ∈ S)
    (hother : ∀ f ∈ walkEdges P, f ≠ e_cut → (H.tail f ∈ S ↔ H.head f ∈ S))
    (hcross : ¬ (H.tail e_cut ∈ S ↔ H.head e_cut ∈ S)) :
    e_cut ∉ walkEdges P := by
  intro he
  obtain ⟨b, hb⟩ := mem_walkEdges_iff.mp he
  obtain ⟨P₁, P₂, hEq, hP₁, hP₂⟩ := IsWalk_mem_split_edge hP.1 hb
  have hnd : (P.map Prod.fst).Nodup := isPath_nodup_edges hP
  rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hnd
  have he_nP1 : e_cut ∉ walkEdges P₁ := by
    intro hmem
    obtain ⟨b₁, hb₁⟩ := mem_walkEdges_iff.mp hmem
    exact hnd.2.2 e_cut (List.mem_map.mpr ⟨(e_cut, b₁), hb₁, rfl⟩) e_cut List.mem_cons_self rfl
  have he_nP2 : e_cut ∉ walkEdges P₂ := by
    intro hmem
    obtain ⟨b₂, hb₂⟩ := mem_walkEdges_iff.mp hmem
    exact (List.nodup_cons.mp hnd.2.1).1 (List.mem_map.mpr ⟨(e_cut, b₂), hb₂, rfl⟩)
  have hside1 : u ∈ S ↔ H.src (e_cut, b) ∈ S := by
    refine walk_mem_cut_iff hP₁ (fun f hf => hother f ?_ (fun h => he_nP1 (h ▸ hf)))
    rw [hEq, walkEdges_append, Finset.mem_union]
    exact Or.inl hf
  have hside2 : H.dst (e_cut, b) ∈ S ↔ v ∈ S := by
    refine walk_mem_cut_iff hP₂ (fun f hf => hother f ?_ (fun h => he_nP2 (h ▸ hf)))
    rw [hEq, walkEdges_append, walkEdges_cons, Finset.mem_union, Finset.mem_insert]
    exact Or.inr (Or.inr hf)
  have hiff_step : H.src (e_cut, b) ∈ S ↔ H.dst (e_cut, b) ∈ S :=
    hside1.symm.trans (hsame.trans hside2.symm)
  cases b
  · simp [MGraph.src, MGraph.dst] at hiff_step
    exact hcross hiff_step.symm
  · simp [MGraph.src, MGraph.dst] at hiff_step
    exact hcross hiff_step

/-! ## Degree-1 leaf edges cannot lie on cycles, and `attachVerts` -/

lemma no_cycle_using_leaf {H : MGraph} {f w : ℕ}
    (hne : H.tail f ≠ H.head f)
    (hw_end : w = H.tail f ∨ w = H.head f)
    (huniq : ∀ g ∈ H.E, (H.tail g = w ∨ H.head g = w) → g = f)
    {C : List (ℕ × Bool)} (hC : H.IsCycle C) :
    ∀ x ∈ C, x.1 ≠ f := by
  intro x hx hxf
  rcases hC with ⟨_, hCnd, u, hW⟩
  obtain ⟨C₁, C₂, hC_eq, hW1, hW2⟩ := IsWalk_mem_split_edge hW hx
  have hnd_C : ((C₁ ++ x :: C₂).map Prod.fst).Nodup := hC_eq ▸ hCnd
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd_C
  have hC₁_nf : f ∉ C₁.map Prod.fst := fun hm =>
    hnd_C.2.2 f hm f (by simp [hxf]) rfl
  have hC₂_nf : f ∉ C₂.map Prod.fst := by
    have h2 := (List.nodup_cons.mp hnd_C.2.1).1
    rwa [← hxf]
  have hsrc_ne_dst : H.src x ≠ H.dst x := by
    cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, hxf, hne, Ne.symm hne]
  have hw_is : w = H.src x ∨ w = H.dst x := by
    cases hx2 : x.2
    · simp only [MGraph.src, MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte, hxf]
      exact hw_end.symm
    · simp only [MGraph.src, MGraph.dst, hx2, ↓reduceIte, hxf]
      exact hw_end
  have hstep_at_w : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
      H.IsWalk a b P → a = w → P ≠ [] → f ∈ P.map Prod.fst := by
    intro a b P hWP ha hPne
    cases hWP with
    | nil _ => exact absurd rfl hPne
    | @cons _ _ y _ hyE hsy _ =>
      have hyw : H.tail y.1 = w ∨ H.head y.1 = w := by
        cases hy2 : y.2
        · simp [MGraph.src, hy2] at hsy; exact Or.inr (hsy.trans ha)
        · simp [MGraph.src, hy2] at hsy; exact Or.inl (hsy.trans ha)
      rw [List.map_cons, List.mem_cons]
      exact Or.inl (huniq y.1 hyE hyw).symm
  have hstep_into_w : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
      H.IsWalk a b P → b = w → P ≠ [] → f ∈ P.map Prod.fst := by
    intro a b P hWP hb hPne
    have hrev := IsWalk_walkRev hWP
    have hf_rev := hstep_at_w hrev hb (fun h => hPne (by simp [walkRev] at h; exact h))
    simp only [walkRev, List.map_reverse, List.map_map, Function.comp_def, List.mem_reverse,
      List.mem_map] at hf_rev
    obtain ⟨z, hzP, hzf⟩ := hf_rev
    exact List.mem_map.mpr ⟨z, hzP, hzf⟩
  have hnil_eq : ∀ {a b : ℕ}, H.IsWalk a b [] → a = b := fun h => by cases h; rfl
  rcases hw_is with hw_src | hw_dst
  · cases C₁ with
    | nil =>
      have hu1 := hnil_eq hW1
      have hC₂_ne : C₂ ≠ [] := by
        rintro rfl
        exact hsrc_ne_dst (hu1.symm.trans (hnil_eq hW2).symm)
      exact hC₂_nf (hstep_into_w hW2 (hu1.trans hw_src.symm) hC₂_ne)
    | cons c1 C1' =>
      exact hC₁_nf (hstep_into_w hW1 hw_src.symm (List.cons_ne_nil c1 C1'))
  · cases C₂ with
    | nil =>
      have hu2 := hnil_eq hW2
      have hC₁_ne : C₁ ≠ [] := by
        rintro rfl
        exact hsrc_ne_dst ((hu2.trans (hnil_eq hW1)).symm)
      exact hC₁_nf (hstep_at_w hW1 (hu2.symm.trans hw_dst.symm) hC₁_ne)
    | cons c2 C2' =>
      exact hC₂_nf (hstep_at_w hW2 hw_dst.symm (List.cons_ne_nil c2 C2'))

/-- Attach isolated vertices `V \ T₀.V` to a vertex `r₀ ∈ T₀.V` using fresh edge identifiers
`base + w` (`base > max T₀.E`). -/
def attachVerts (T₀ : MGraph) (r₀ : ℕ) (V : Finset ℕ) (base : ℕ) : MGraph :=
  { V := V
    E := T₀.E ∪ (V \ T₀.V).image (fun w => base + w)
    tail := fun f => if f ∈ T₀.E then T₀.tail f else r₀
    head := fun f => if f ∈ T₀.E then T₀.head f else f - base }

lemma attachVerts_isSpanningTreeOn {T₀ : MGraph} {V₀ V : Finset ℕ} {r₀ base : ℕ}
    (hT₀ : T₀.IsSpanningTreeOn V₀) (hr₀ : r₀ ∈ V₀) (hV₀_sub : V₀ ⊆ V)
    (hbase : ∀ f ∈ T₀.E, f < base) :
    (attachVerts T₀ r₀ V base).IsSpanningTreeOn V := by
  classical
  let T := attachVerts T₀ r₀ V base
  have hTV : T₀.V = V₀ := hT₀.2.1
  have hT_V : T.V = V := rfl
  have hnot_old : ∀ w ∈ V \ T₀.V, base + w ∉ T₀.E := fun w _ h =>
    Nat.not_lt_of_ge (Nat.le_add_right base w) (hbase _ h)
  have htail_new : ∀ w ∈ V \ T₀.V, T.tail (base + w) = r₀ := fun w hw => by
    dsimp only [T, attachVerts]; exact ite_eq_right (hnot_old w hw)
  have hhead_new : ∀ w ∈ V \ T₀.V, T.head (base + w) = w := fun w hw => by
    dsimp only [T, attachVerts]
    rw [ite_eq_right (hnot_old w hw), Nat.add_sub_cancel_left]
  have hsub_T₀ : T.IsSubgraph T₀ :=
    ⟨hTV ▸ hV₀_sub, Finset.subset_union_left, fun f hf => by
      dsimp only [T, attachVerts]
      exact ⟨(ite_eq_left hf).symm, (ite_eq_left hf).symm⟩⟩
  have hT_val : T.IsValid := by
    intro f hf
    dsimp only [T, attachVerts] at hf ⊢
    rw [Finset.mem_union] at hf
    rcases hf with hf0 | hfw
    · rw [ite_eq_left hf0, ite_eq_left hf0]
      have h0 := hT₀.1.1 f hf0
      exact ⟨hV₀_sub (hTV ▸ h0.1), hV₀_sub (hTV ▸ h0.2)⟩
    · rw [Finset.mem_image] at hfw
      obtain ⟨w, hw, rfl⟩ := hfw
      rw [ite_eq_right (hnot_old w hw), ite_eq_right (hnot_old w hw), Nat.add_sub_cancel_left]
      exact ⟨hV₀_sub hr₀, (Finset.mem_sdiff.mp hw).1⟩
  have hT_forest : T.IsForest := by
    refine ⟨hT_val, fun C hC => ?_⟩
    have hC_old : ∀ x ∈ C, x.1 ∈ T₀.E := by
      intro x hx
      have hxE : x.1 ∈ T.E := IsWalk_edges_mem hC.2.2.choose_spec hx
      dsimp only [T, attachVerts] at hxE
      rw [Finset.mem_union] at hxE
      rcases hxE with hx0 | hxw
      · exact hx0
      · exfalso
        rw [Finset.mem_image] at hxw
        obtain ⟨w, hw, hxw_eq⟩ := hxw
        have hw_nV0 : w ∉ T₀.V := (Finset.mem_sdiff.mp hw).2
        have hr₀_V0 : r₀ ∈ T₀.V := hTV ▸ hr₀
        have hne : T.tail (base + w) ≠ T.head (base + w) := by
          rw [htail_new w hw, hhead_new w hw]
          exact fun h => hw_nV0 (h ▸ hr₀_V0)
        have huniq : ∀ g ∈ T.E, (T.tail g = w ∨ T.head g = w) → g = base + w := by
          intro g hg hgw
          dsimp only [T, attachVerts] at hg hgw
          rw [Finset.mem_union] at hg
          rcases hg with hg0 | hgw'
          · exfalso
            rw [ite_eq_left hg0, ite_eq_left hg0] at hgw
            rcases hgw with ht | hh
            · exact hw_nV0 (ht ▸ (hT₀.1.1 g hg0).1)
            · exact hw_nV0 (hh ▸ (hT₀.1.1 g hg0).2)
          · rw [Finset.mem_image] at hgw'
            obtain ⟨w', hw', rfl⟩ := hgw'
            rw [ite_eq_right (hnot_old w' hw'), ite_eq_right (hnot_old w' hw'),
              Nat.add_sub_cancel_left] at hgw
            rcases hgw with ht | hh
            · exact absurd ht (fun h => hw_nV0 (h ▸ hr₀_V0))
            · rw [hh]
        exact no_cycle_using_leaf hne (Or.inr (hhead_new w hw).symm) huniq hC x hx hxw_eq.symm
    have hC_in_T₀ : T₀.IsCycle C := by
      refine ⟨hC.1, hC.2.1, hC.2.2.choose, ?_⟩
      have hsrc : ∀ y ∈ C, T₀.src y = T.src y := fun y hy => by
        have hy0 := hC_old y hy
        cases y.2 <;> simp [MGraph.src, T, attachVerts, ite_eq_left hy0]
      have hdst : ∀ y ∈ C, T₀.dst y = T.dst y := fun y hy => by
        have hy0 := hC_old y hy
        cases y.2 <;> simp [MGraph.dst, T, attachVerts, ite_eq_left hy0]
      have hlift : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
          T.IsWalk a b P → (∀ y ∈ P, y.1 ∈ T₀.E) → T₀.IsWalk a b P := by
        intro a b P hWP hPE
        induction hWP with
        | nil s => exact .nil s
        | @cons s _ y ys _ hsy hrest ih =>
          have hy0 := hPE y List.mem_cons_self
          have hsrc_y : T₀.src y = T.src y := by
            cases y.2 <;> simp [MGraph.src, T, attachVerts, ite_eq_left hy0]
          have hdst_y : T₀.dst y = T.dst y := by
            cases y.2 <;> simp [MGraph.dst, T, attachVerts, ite_eq_left hy0]
          exact .cons hy0 (hsrc_y.trans hsy)
            (hdst_y ▸ ih (fun z hz => hPE z (List.mem_cons_of_mem _ hz)))
      exact hlift hC.2.2.choose_spec hC_old
    exact hT₀.1.2 C hC_in_T₀
  have hT_conn_r : ∀ u ∈ V, T.Connected r₀ u := by
    intro u hu
    by_cases hu0 : u ∈ V₀
    · exact connected_of_subgraph hsub_T₀ (hT₀.2.2 r₀ hr₀ u hu0)
    · have hu_diff : u ∈ V \ T₀.V := Finset.mem_sdiff.mpr ⟨hu, by rwa [hTV]⟩
      have he_mem : base + u ∈ T.E := by
        dsimp only [T, attachVerts]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu_diff)
      refine ⟨[(base + u, true)], .cons he_mem ?_ ?_⟩
      · simp [MGraph.src, htail_new u hu_diff]
      · simp [MGraph.dst, hhead_new u hu_diff]; exact .nil u
  refine ⟨hT_forest, rfl, fun u hu v hv =>
    connected_trans (connected_symm (hT_conn_r u hu)) (hT_conn_r v hv)⟩

/-! ## Connected graphs with at most `n - 1` edges are forests -/

private lemma induced_isWalk_of_isWalk {H : MGraph} {W : Finset ℕ}
    {H_sub : MGraph} (_hV : H_sub.V = W)
    (hE : H_sub.E = H.E.filter (fun f => H.tail f ∈ W ∧ H.head f ∈ W))
    (ht : H_sub.tail = H.tail) (hh : H_sub.head = H.head)
    {u v : ℕ} {P : List (ℕ × Bool)} (hP : H.IsWalk u v P)
    (hverts : ∀ z ∈ H.walkVertices u P, z ∈ W) :
    H_sub.IsWalk u v P := by
  have hsrc : H_sub.src = H.src := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.src, ht, hh]
  have hdst : H_sub.dst = H.dst := by
    funext ⟨e, b⟩; cases b <;> simp [MGraph.dst, ht, hh]
  induction hP with
  | nil s => exact .nil s
  | @cons s _ x xs hxE hsx hrest ih =>
    have hsW : s ∈ W := hverts s (by rw [walkVertices_cons]; exact List.mem_cons_self)
    have hdstW : H.dst x ∈ W :=
      hverts (H.dst x) (by rw [walkVertices_cons]; exact List.mem_cons_of_mem _ (IsWalk_start_mem_walkVertices H _ xs))
    have hsrcW : H.src x ∈ W := hsx.symm ▸ hsW
    have hx_sub : x.1 ∈ H_sub.E := by
      rw [hE, Finset.mem_filter]
      refine ⟨hxE, ?_⟩
      cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2] at hsrcW hdstW
      · exact ⟨hdstW, hsrcW⟩
      · exact ⟨hsrcW, hdstW⟩
    have hrest_v : ∀ z ∈ H.walkVertices (H.dst x) xs, z ∈ W := fun z hz =>
      hverts z (by rw [walkVertices_cons]; exact List.mem_cons_of_mem _ hz)
    exact .cons hx_sub (hsrc ▸ hsx) (hdst ▸ ih hrest_v)

lemma connected_card_ge :
    ∀ (m : ℕ) (H : MGraph), H.E.card ≤ m → H.IsValid → H.V.Nonempty →
      (∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v) → H.V.card ≤ H.E.card + 1
  | 0, H, hm, _, ⟨u, hu⟩, hconn => by
    have hE0 : H.E = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hm)
    have hsub : H.V ⊆ {u} := by
      intro v hv
      obtain ⟨P, hW⟩ := hconn u hu v hv
      cases hW with
      | nil => exact Finset.mem_singleton_self u
      | cons hxE _ _ => exact absurd (hE0 ▸ hxE) (Finset.notMem_empty _)
    have hcard : H.V.card ≤ ({u} : Finset ℕ).card := Finset.card_le_card hsub
    simp at hcard
    omega
  | m + 1, H, hm, hval, hVne, hconn => by
    classical
    by_cases hm_le : H.E.card ≤ m
    · exact connected_card_ge m H hm_le hval hVne hconn
    · have hE_eq : H.E.card = m + 1 := by omega
      have hE_ne : H.E.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e, he⟩ := hE_ne
      let Hdel : MGraph := { H with E := H.E.erase e }
      have hdel_card : Hdel.E.card = m := by
        dsimp only [Hdel]; rw [Finset.card_erase_of_mem he, hE_eq]; omega
      have hdel_val : Hdel.IsValid := fun f hf => hval f (Finset.erase_subset _ _ hf)
      by_cases hdel_conn : ∀ u ∈ H.V, ∀ v ∈ H.V, Hdel.Connected u v
      · have ih := connected_card_ge m Hdel hdel_card.le hdel_val hVne hdel_conn
        change H.V.card ≤ Hdel.E.card + 1 at ih
        omega
      · simp only [not_forall] at hdel_conn
        obtain ⟨u₀, hu₀, v₀, hv₀, hnuv⟩ := hdel_conn
        let V₁ : Finset ℕ := H.V.filter (fun w => Hdel.Connected u₀ w)
        let V₂ : Finset ℕ := H.V \ V₁
        have hu₀₁ : u₀ ∈ V₁ := Finset.mem_filter.mpr ⟨hu₀, connected_refl Hdel u₀⟩
        have hv₀₂ : v₀ ∈ V₂ := Finset.mem_sdiff.mpr ⟨hv₀, fun h => hnuv (Finset.mem_filter.mp h).2⟩
        have hstep_del : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
            Hdel.IsWalk a b P → a ∈ V₁ → ∀ z ∈ Hdel.walkVertices a P, z ∈ V₁ := by
          intro a b P hWP ha
          induction hWP with
          | nil s =>
            intro z hz
            simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz
            exact hz ▸ ha
          | @cons s _ x xs hxE hsx hrest ih =>
            have hconn_s : Hdel.Connected u₀ s := (Finset.mem_filter.mp ha).2
            have hconn_dst : Hdel.Connected u₀ (Hdel.dst x) :=
              connected_trans hconn_s ⟨[x], .cons hxE hsx (.nil _)⟩
            have hdstV : Hdel.dst x ∈ H.V := by
              have hxv := hdel_val x.1 hxE
              cases hx2 : x.2
              · simpa [MGraph.dst, hx2] using hxv.1
              · simpa [MGraph.dst, hx2] using hxv.2
            have hdst₁ : H.dst x ∈ V₁ := Finset.mem_filter.mpr ⟨hdstV, hconn_dst⟩
            intro z hz
            rw [walkVertices_cons, List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact ha
            · exact ih hdst₁ z hz
        let E₁ := Hdel.E.filter (fun f => H.tail f ∈ V₁ ∧ H.head f ∈ V₁)
        let E₂ := Hdel.E.filter (fun f => H.tail f ∈ V₂ ∧ H.head f ∈ V₂)
        let H₁ : MGraph := { V := V₁, E := E₁, tail := H.tail, head := H.head }
        let H₂ : MGraph := { V := V₂, E := E₂, tail := H.tail, head := H.head }
        have hE_disj : Disjoint E₁ E₂ := by
          rw [Finset.disjoint_left]
          intro f hf1 hf2
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hf2).2.1).2
            (Finset.mem_filter.mp hf1).2.1
        have hE_sub : E₁ ∪ E₂ ⊆ Hdel.E :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hcard_sum : E₁.card + E₂.card ≤ m := by
          rw [← Finset.card_union_of_disjoint hE_disj, ← hdel_card]
          exact Finset.card_le_card hE_sub
        have h1_val : H₁.IsValid := fun f hf =>
          ⟨(Finset.mem_filter.mp hf).2.1, (Finset.mem_filter.mp hf).2.2⟩
        have h2_val : H₂.IsValid := fun f hf =>
          ⟨(Finset.mem_filter.mp hf).2.1, (Finset.mem_filter.mp hf).2.2⟩
        have h1_conn : ∀ x ∈ V₁, ∀ y ∈ V₁, H₁.Connected x y := by
          have hto_u₀ : ∀ w ∈ V₁, H₁.Connected u₀ w := by
            intro w hw
            obtain ⟨P, hWP⟩ := (Finset.mem_filter.mp hw).2
            refine ⟨P, induced_isWalk_of_isWalk (H := Hdel) (H_sub := H₁) rfl rfl rfl rfl hWP
              (hstep_del hWP hu₀₁)⟩
          intro x hx y hy
          exact connected_trans (connected_symm (hto_u₀ x hx)) (hto_u₀ y hy)
        have hwalk_lift : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
            Hdel.IsWalk a b P → H.IsWalk a b P := by
          intro a b P hWP
          induction hWP with
          | nil s => exact .nil s
          | cons hxE hsx _ ih => exact .cons (Finset.erase_subset _ _ hxE) hsx ih
        have hpath_split_e : ∀ {w : ℕ}, w ∈ V₂ →
            ∃ x : ℕ × Bool, x.1 = e ∧ H.src x ∈ V₁ ∧ Hdel.Connected (H.dst x) w := by
          intro w hw
          obtain ⟨P, hP⟩ := connected_isPath (hconn u₀ hu₀ w (Finset.mem_sdiff.mp hw).1)
          have he_in_P : e ∈ walkEdges P := by
            by_contra he_nP
            have hP_del : Hdel.IsWalk u₀ w P := by
              have haux : ∀ {a b : ℕ} {Q : List (ℕ × Bool)},
                  H.IsWalk a b Q → e ∉ walkEdges Q → Hdel.IsWalk a b Q := by
                intro a b Q hWQ hQne
                induction hWQ with
                | nil s => exact .nil s
                | @cons s _ y ys hyE hsy _ ih =>
                  have hy_ne : y.1 ≠ e := fun h => hQne (by
                    rw [walkEdges_cons, Finset.mem_insert]; exact Or.inl h.symm)
                  have hys_ne : e ∉ walkEdges ys := fun h => hQne (by
                    rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr h)
                  exact .cons (Finset.mem_erase.mpr ⟨hy_ne, hyE⟩) hsy (ih hys_ne)
              exact haux hP.1 he_nP
            exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mpr
              ⟨(Finset.mem_sdiff.mp hw).1, ⟨P, hP_del⟩⟩)
          obtain ⟨b, hb⟩ := mem_walkEdges_iff.mp he_in_P
          obtain ⟨A, B, hEq, hA, hB⟩ := IsWalk_mem_split_edge hP.1 hb
          have hnd := isPath_nodup_edges hP
          rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hnd
          have hA_ne : e ∉ walkEdges A := fun hm => by
            obtain ⟨ba, hba⟩ := mem_walkEdges_iff.mp hm
            exact hnd.2.2 e (List.mem_map.mpr ⟨(e, ba), hba, rfl⟩) e List.mem_cons_self rfl
          have hB_ne : e ∉ walkEdges B := fun hm => by
            obtain ⟨bb, hbb⟩ := mem_walkEdges_iff.mp hm
            exact (List.nodup_cons.mp hnd.2.1).1 (List.mem_map.mpr ⟨(e, bb), hbb, rfl⟩)
          have hwalk_unlift : ∀ {a c : ℕ} {Q : List (ℕ × Bool)},
              H.IsWalk a c Q → e ∉ walkEdges Q → Hdel.IsWalk a c Q := by
            intro a c Q hWQ hQne
            induction hWQ with
            | nil s => exact .nil s
            | @cons s _ y ys hyE hsy _ ih =>
              have hy_ne : y.1 ≠ e := fun h => hQne (by
                rw [walkEdges_cons, Finset.mem_insert]; exact Or.inl h.symm)
              have hys_ne : e ∉ walkEdges ys := fun h => hQne (by
                rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr h)
              exact .cons (Finset.mem_erase.mpr ⟨hy_ne, hyE⟩) hsy (ih hys_ne)
          have hsrcV : H.src (e, b) ∈ H.V := by
            have hev := hval e he
            cases b <;> simp [MGraph.src] <;> [exact hev.2; exact hev.1]
          exact ⟨(e, b), rfl, Finset.mem_filter.mpr ⟨hsrcV, ⟨A, hwalk_unlift hA hA_ne⟩⟩,
            ⟨B, hwalk_unlift hB hB_ne⟩⟩
        obtain ⟨x₀, hx₀e, hx₀_src₁, hx₀_conn⟩ := hpath_split_e hv₀₂
        have hx₀_dst₂ : H.dst x₀ ∉ V₁ := by
          intro hmem
          have hc := connected_trans (Finset.mem_filter.mp hmem).2 hx₀_conn
          exact (Finset.mem_sdiff.mp hv₀₂).2 (Finset.mem_filter.mpr ⟨hv₀, hc⟩)
        have h2_conn : ∀ x ∈ V₂, ∀ y ∈ V₂, H₂.Connected x y := by
          have hs₂V : H.dst x₀ ∈ V₂ := by
            have hxv := hval x₀.1 (hx₀e ▸ he)
            have hmemV : H.dst x₀ ∈ H.V := by
              cases hx2 : x₀.2
              · simpa [MGraph.dst, hx2] using hxv.1
              · simpa [MGraph.dst, hx2] using hxv.2
            exact Finset.mem_sdiff.mpr ⟨hmemV, hx₀_dst₂⟩
          have hfrom_s₂ : ∀ w ∈ V₂, H₂.Connected (H.dst x₀) w := by
            intro w hw
            obtain ⟨y, hye, hy_src₁, hy_conn⟩ := hpath_split_e hw
            have hy_eq : y = x₀ := by
              by_contra hne_y
              have hb_ne : y.2 ≠ x₀.2 := fun hb => hne_y (Prod.ext (hye.trans hx₀e.symm) hb)
              have hdst_eq : H.src y = H.dst x₀ := by
                cases hy2 : y.2 <;> cases hx2 : x₀.2 <;>
                  simp [MGraph.src, MGraph.dst, hy2, hx2, hye, hx₀e] at hb_ne ⊢
              exact hx₀_dst₂ (hdst_eq ▸ hy_src₁)
            obtain ⟨Q, hQ⟩ := hy_conn
            rw [hy_eq] at hQ
            have hQ_verts : ∀ z ∈ Hdel.walkVertices (H.dst x₀) Q, z ∈ V₂ := by
              intro z hz
              obtain ⟨Q₁, Q₂, hQ_eq, _, hQ₂⟩ := walkVertices_mem_split hQ hz
              have hzV : z ∈ H.V := by
                cases hQ₂ with
                | nil _ => exact (Finset.mem_sdiff.mp hw).1
                | @cons _ _ step _ hstepE hss _ =>
                  have hsv := hdel_val step.1 hstepE
                  rw [← hss]
                  cases hs2 : step.2
                  · simpa [MGraph.src, hs2] using hsv.2
                  · simpa [MGraph.src, hs2] using hsv.1
              refine Finset.mem_sdiff.mpr ⟨hzV, fun hz₁ => ?_⟩
              have hc : Hdel.Connected u₀ w :=
                connected_trans (Finset.mem_filter.mp hz₁).2 ⟨Q₂, hQ₂⟩
              exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw).1, hc⟩)
            exact ⟨Q, induced_isWalk_of_isWalk (H := Hdel) (H_sub := H₂) rfl rfl rfl rfl hQ hQ_verts⟩
          intro x hx y hy
          exact connected_trans (connected_symm (hfrom_s₂ x hx)) (hfrom_s₂ y hy)
        have ih1 := connected_card_ge m H₁ (by change E₁.card ≤ m; omega) h1_val ⟨u₀, hu₀₁⟩ h1_conn
        have ih2 := connected_card_ge m H₂ (by change E₂.card ≤ m; omega) h2_val ⟨v₀, hv₀₂⟩ h2_conn
        change V₁.card ≤ E₁.card + 1 at ih1
        change V₂.card ≤ E₂.card + 1 at ih2
        have hV_union : V₁ ∪ V₂ = H.V :=
          Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
        have hV_disj : Disjoint V₁ V₂ :=
          Finset.disjoint_left.mpr (fun _ hz1 hz2 => (Finset.mem_sdiff.mp hz2).2 hz1)
        have hV_card : H.V.card = V₁.card + V₂.card := by
          rw [← Finset.card_union_of_disjoint hV_disj, hV_union]
        omega

lemma isForest_of_connected_card_le {H : MGraph} (hval : H.IsValid) (hV : H.V.Nonempty)
    (hconn : ∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v) (hcard : H.E.card ≤ H.V.card - 1) :
    H.IsForest := by
  classical
  refine ⟨hval, fun C hC => ?_⟩
  rcases hC with ⟨hCne, hCnd, u, hW⟩
  rcases C with _ | ⟨x₀, xs⟩
  · exact absurd rfl hCne
  · cases hW with
      | @cons _ _ _ _ hxE hsrc_x hrest =>
        let Hdel : MGraph := { H with E := H.E.erase x₀.1 }
        have hx_nxs : x₀.1 ∉ xs.map Prod.fst := (List.nodup_cons.mp (by simpa using hCnd)).1
        have hwalk_xs : Hdel.IsWalk (H.dst x₀) (H.src x₀) xs := by
          have haux : ∀ {a b : ℕ} {Q : List (ℕ × Bool)},
              H.IsWalk a b Q → x₀.1 ∉ Q.map Prod.fst → Hdel.IsWalk a b Q := by
            intro a b Q hWQ hQn
            induction hWQ with
            | nil s => exact .nil s
            | @cons s _ y ys hyE hsy _ ih =>
              rw [List.map_cons, List.mem_cons] at hQn
              exact .cons (Finset.mem_erase.mpr ⟨Ne.symm (fun h => hQn (Or.inl h)), hyE⟩) hsy
                (ih (fun h => hQn (Or.inr h)))
          exact hsrc_x ▸ haux hrest hx_nxs
        have hconn_end : Hdel.Connected (H.src x₀) (H.dst x₀) := connected_symm ⟨xs, hwalk_xs⟩
        have hdel_conn : ∀ a ∈ H.V, ∀ b ∈ H.V, Hdel.Connected a b := by
          have hstep : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
              H.IsWalk a b P → Hdel.Connected a b := by
            intro a b P hWP
            induction hWP with
            | nil s => exact connected_refl Hdel s
            | @cons s _ y ys hyE hsy _ ih =>
              have hy_conn : Hdel.Connected (H.src y) (H.dst y) := by
                by_cases hyx : y.1 = x₀.1
                · cases hy2 : y.2 <;> cases hx2 : x₀.2 <;>
                    simp [MGraph.src, MGraph.dst, hy2, hx2, hyx] at hconn_end ⊢ <;>
                    first | exact hconn_end | exact connected_symm hconn_end
                · exact ⟨[y], .cons (Finset.mem_erase.mpr ⟨hyx, hyE⟩) rfl (.nil _)⟩
              exact hsy ▸ connected_trans hy_conn ih
          intro a ha b hb
          obtain ⟨P, hWP⟩ := hconn a ha b hb
          exact hstep hWP
        have hdel_val : Hdel.IsValid := fun f hf => hval f (Finset.erase_subset _ _ hf)
        have hge := connected_card_ge Hdel.E.card Hdel le_rfl hdel_val hV hdel_conn
        have hdel_card : Hdel.E.card = H.E.card - 1 := by
          dsimp only [Hdel]; exact Finset.card_erase_of_mem hxE
        have hVpos : 1 ≤ H.V.card := Finset.card_pos.mpr hV
        have hEpos : 1 ≤ H.E.card := Finset.card_pos.mpr ⟨x₀.1, hxE⟩
        change H.V.card ≤ Hdel.E.card + 1 at hge
        omega

/-! ## Bridging connected components of `G_v` on `V_act` -/

/-- The multigraph obtained by adding star bridges from `r₀` to each vertex `b ∈ B`, with edge
identifiers `copyMod G_v + b` strictly outside `G_v.E`. -/
def gvWithBridges (G_v : MGraph) (V_act : Finset ℕ) (r₀ : ℕ) (B : List ℕ) : MGraph :=
  { V := V_act
    E := G_v.E ∪ B.toFinset.image (fun b => copyMod G_v + b)
    tail := fun f => if f ∈ G_v.E then G_v.tail f else r₀
    head := fun f => if f ∈ G_v.E then G_v.head f else f - copyMod G_v }

/-- Greedily selects one vertex per non-root connected component of `G_v` along `rest`. -/
noncomputable def bridgeVerts (G_v : MGraph) (V_act : Finset ℕ) (r₀ : ℕ) : List ℕ → List ℕ
  | [] => []
  | u :: rest =>
    open Classical in
    let B := bridgeVerts G_v V_act r₀ rest
    if (gvWithBridges G_v V_act r₀ B).Connected r₀ u then B else u :: B

private lemma gvWithBridges_mono {G_v : MGraph} {V_act : Finset ℕ} {r₀ : ℕ}
    {B₁ B₂ : List ℕ} (hsub : ∀ b ∈ B₁, b ∈ B₂) :
    (gvWithBridges G_v V_act r₀ B₂).IsSubgraph (gvWithBridges G_v V_act r₀ B₁) := by
  refine ⟨Finset.Subset.refl _, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  refine Finset.union_subset Finset.subset_union_left ?_
  intro f hf
  rw [Finset.mem_image] at hf
  obtain ⟨b, hb, rfl⟩ := hf
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr
    (hsub b (List.mem_toFinset.mp hb))))

private lemma gv_connected_in_gvWithBridges {G_v : MGraph} {V_act : Finset ℕ} {r₀ : ℕ}
    (B : List ℕ) {a b : ℕ} (h : G_v.Connected a b) :
    (gvWithBridges G_v V_act r₀ B).Connected a b := by
  let H := gvWithBridges G_v V_act r₀ B
  obtain ⟨P, hWP⟩ := h
  refine ⟨P, ?_⟩
  induction hWP with
  | nil s => exact .nil s
  | @cons s _ x xs hxE hsx _ ih =>
    have hsrc : H.src x = G_v.src x := by
      cases hx2 : x.2 <;> simp [H, gvWithBridges, MGraph.src, hx2, ite_eq_left hxE]
    have hdst : H.dst x = G_v.dst x := by
      cases hx2 : x.2 <;> simp [H, gvWithBridges, MGraph.dst, hx2, ite_eq_left hxE]
    exact .cons (Finset.mem_union_left _ hxE) (hsrc.trans hsx) (hdst ▸ ih)

private lemma gvWithBridges_step_bridge {G_v : MGraph} {V_act : Finset ℕ} {r₀ u : ℕ}
    {B : List ℕ} (hu : u ∈ B) :
    (gvWithBridges G_v V_act r₀ B).Connected r₀ u := by
  let H := gvWithBridges G_v V_act r₀ B
  have he_nG : copyMod G_v + u ∉ G_v.E := fun h =>
    Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
  have he_mem : copyMod G_v + u ∈ H.E :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hu))
  refine ⟨[(copyMod G_v + u, true)], .cons he_mem ?_ ?_⟩
  · simp [gvWithBridges, MGraph.src, ite_eq_right he_nG]
  · simp [gvWithBridges, MGraph.dst, ite_eq_right he_nG]; exact .nil u

lemma bridgeVerts_props (G_v : MGraph) (V_act : Finset ℕ) (r₀ : ℕ) :
    ∀ rest : List ℕ, r₀ ∉ rest → rest.Nodup →
      let B := bridgeVerts G_v V_act r₀ rest
      B.Nodup ∧ (∀ b ∈ B, b ∈ rest) ∧ r₀ ∉ B ∧
      (∀ x ∈ rest, (gvWithBridges G_v V_act r₀ B).Connected r₀ x) ∧
      (∀ a ∈ r₀ :: B, ∀ b ∈ r₀ :: B, a ≠ b → ¬ G_v.Connected a b) := by
  intro rest
  induction rest with
  | nil =>
    intro _ _
    refine ⟨List.nodup_nil, fun _ h => absurd h (List.not_mem_nil), List.not_mem_nil,
      fun _ h => absurd h (List.not_mem_nil), fun a ha b hb hne => ?_⟩
    dsimp only [bridgeVerts] at ha hb
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hne
  | cons u rest ih =>
    intro hr₀ hnd
    have hr₀_u : r₀ ≠ u := fun h => hr₀ (h ▸ List.mem_cons_self)
    have hr₀_rest : r₀ ∉ rest := fun h => hr₀ (List.mem_cons_of_mem _ h)
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hu_nrest : u ∉ rest := (List.nodup_cons.mp hnd).1
    obtain ⟨hBnd, hB_sub, hr₀_nB, hconn_rest, hcomp_disj⟩ := ih hr₀_rest hnd_rest
    dsimp only [bridgeVerts]
    split_ifs with hconn_u
    · refine ⟨hBnd, fun b hb => List.mem_cons_of_mem _ (hB_sub b hb), hr₀_nB, ?_, hcomp_disj⟩
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hconn_u
      · exact hconn_rest x hx
    · refine ⟨List.nodup_cons.mpr ⟨fun huB => hu_nrest (hB_sub u huB), hBnd⟩, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rw [List.mem_cons] at hb
        exact hb.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem _ (hB_sub b h))
      · intro hr
        rw [List.mem_cons] at hr
        exact hr.elim hr₀_u hr₀_nB
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact gvWithBridges_step_bridge List.mem_cons_self
        · exact connected_of_subgraph
            (gvWithBridges_mono (fun b hb => List.mem_cons_of_mem u hb))
            (hconn_rest x hx)
      · have hconn_B : ∀ a ∈ r₀ :: bridgeVerts G_v V_act r₀ rest,
            (gvWithBridges G_v V_act r₀ (bridgeVerts G_v V_act r₀ rest)).Connected r₀ a := by
          intro a ha
          rw [List.mem_cons] at ha
          rcases ha with ha_r | ha
          · rw [ha_r]; exact connected_refl _ r₀
          · exact gvWithBridges_step_bridge ha
        intro a ha b hb hne hGv
        rw [List.mem_cons] at ha hb
        rcases ha with ha_r | ha <;> rcases hb with hb_r | hb
        · exact absurd (ha_r.trans hb_r.symm) hne
        · rw [List.mem_cons] at hb
          rcases hb with hb_u | hb
          · rw [ha_r, hb_u] at hGv
            exact hconn_u (gv_connected_in_gvWithBridges _ hGv)
          · rw [ha_r] at hGv hne
            exact hcomp_disj r₀ List.mem_cons_self b (List.mem_cons_of_mem _ hb) hne hGv
        · rw [List.mem_cons] at ha
          rcases ha with ha_u | ha
          · rw [ha_u, hb_r] at hGv
            exact hconn_u (gv_connected_in_gvWithBridges _ (connected_symm hGv))
          · rw [hb_r] at hGv hne
            exact hcomp_disj a (List.mem_cons_of_mem _ ha) r₀ List.mem_cons_self hne hGv
        · rw [List.mem_cons] at ha hb
          rcases ha with ha_u | ha <;> rcases hb with hb_u | hb
          · exact absurd (ha_u.trans hb_u.symm) hne
          · rw [ha_u] at hGv
            exact hconn_u (connected_trans (hconn_B b (List.mem_cons_of_mem _ hb))
              (gv_connected_in_gvWithBridges _ (connected_symm hGv)))
          · rw [hb_u] at hGv
            exact hconn_u (connected_trans (hconn_B a (List.mem_cons_of_mem _ ha))
              (gv_connected_in_gvWithBridges _ hGv))
          · exact hcomp_disj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hne hGv

lemma bridgeVerts_length_le {G_v : MGraph} {V_act : Finset ℕ} {r₀ : ℕ} {B : List ℕ}
    (hnd : (r₀ :: B).Nodup)
    (hsub : ∀ x ∈ r₀ :: B, x ∈ V_act)
    (hinc : ∀ x ∈ V_act, ∃ e' ∈ G_v.E, G_v.tail e' = x ∨ G_v.head e' = x)
    (hdisj : ∀ a ∈ r₀ :: B, ∀ b ∈ r₀ :: B, a ≠ b → ¬ G_v.Connected a b) :
    B.length + 1 ≤ G_v.E.card := by
  classical
  let witness : ℕ → ℕ := fun x =>
    if h : ∃ e' ∈ G_v.E, G_v.tail e' = x ∨ G_v.head e' = x then Classical.choose h else 0
  have hwit_spec : ∀ x ∈ V_act, witness x ∈ G_v.E ∧
      (G_v.tail (witness x) = x ∨ G_v.head (witness x) = x) := fun x hx => by
    have hex := hinc x hx
    dsimp only [witness]
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    exact Classical.choose_spec hex
  have hinj : ∀ a ∈ (r₀ :: B).toFinset, ∀ b ∈ (r₀ :: B).toFinset,
      witness a = witness b → a = b := by
    intro a ha b hb hEq
    rw [List.mem_toFinset] at ha hb
    by_contra hne
    have hsa := hwit_spec a (hsub a ha)
    have hsb := hwit_spec b (hsub b hb)
    rw [hEq] at hsa
    have hconn_end : G_v.Connected (G_v.tail (witness b)) (G_v.head (witness b)) :=
      ⟨[(witness b, true)], .cons hsb.1 rfl (.nil _)⟩
    have hconn_ab : G_v.Connected a b := by
      rcases hsa.2 with ht_a | hh_a <;> rcases hsb.2 with ht_b | hh_b
      · exact (ht_a.symm.trans ht_b) ▸ connected_refl G_v a
      · have hc := hconn_end; rw [ht_a, hh_b] at hc; exact hc
      · have hc := connected_symm hconn_end; rw [hh_a, ht_b] at hc; exact hc
      · exact (hh_a.symm.trans hh_b) ▸ connected_refl G_v a
    exact hdisj a ha b hb hne hconn_ab
  have hmap : (r₀ :: B).toFinset.image witness ⊆ G_v.E := by
    intro e' he'
    rw [Finset.mem_image] at he'
    obtain ⟨x, hx, rfl⟩ := he'
    exact (hwit_spec x (hsub x (List.mem_toFinset.mp hx))).1
  have hcard1 : ((r₀ :: B).toFinset.image witness).card = (r₀ :: B).toFinset.card :=
    Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h)
  have hcard2 : (r₀ :: B).toFinset.card = B.length + 1 := by
    rw [List.toFinset_card_of_nodup hnd, List.length_cons]
  calc B.length + 1
      = ((r₀ :: B).toFinset.image witness).card := by rw [hcard1, hcard2]
    _ ≤ G_v.E.card := Finset.card_le_card hmap

lemma finset_sum_le_list_sum_of_nonneg (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∀ (es : List ℕ), ∑ j ∈ es.toFinset, w j ≤ (es.map w).sum
  | [] => by simp
  | a :: es => by
    classical
    have ih := finset_sum_le_list_sum_of_nonneg w hw es
    rw [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ es.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      linarith [hw a]
    · rw [Finset.sum_insert ha]
      linarith

end MinCostFlow.LSF
