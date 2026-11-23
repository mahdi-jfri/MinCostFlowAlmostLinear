module

public import MinCostFlow.LSF.Tools
public import MinCostFlow.Statement.Cited.AbrahamNeiman
import all MinCostFlow.LSF.Theorem22
import MinCostFlow.LSF.Theorem22Aux
import MinCostFlow.LSF.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stretch-Only LSST Extraction from `[AN19]` (`LSFWindowLSST`)

Extracts static low-stretch spanning trees (`IsLSST` with overhead
`(4 * max K_AN 1 + 5) * log^2(G.n + 2)`) from a stretch-only `[AN19]` specification on
`Cited.WGraph` without requiring a running-time bound or `1 ≤ c_AN`.

This supports the fallback branch of `canonicalLSFInit` so that `canonicalLSFInit_spec` needs only the
stretch-only `[AN19]` hypothesis, while sharing the exact constant
`4 * max K_AN 1 + 5` with `lemma55Module`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF

/-- Existential stretch-only `[AN19]` specification on weighted simple graphs (`Cited.WGraph`). -/
def WGraphLSSTSpec (K_AN : ℝ) : Prop :=
  ∀ G : Cited.WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
    (∀ e ∈ G.edges, 1 ≤ e.2.2) →
    ∃ out, G.IsSpanningTree out ∧
      G.totalStretch out ≤ K_AN * G.m * Cited.logLogFactor G.n

/-- Stretch-only Word-RAM `[AN19]` specification matching `sig_canonicalLSFInit_spec`. -/
def StretchOnlyAN19Spec (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : Prop :=
  ∀ G_a : Cited.WGraph, G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
    (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
    ∃ out cost,
      RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
        G_a.IsSpanningTree out ∧
        G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n

/-- Full Word-RAM `[AN19]` specification with `1 ≤ c_AN` and cost bound required by
`lemma55Program_runs`. -/
def FullAN19Spec (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : Prop :=
  1 ≤ c_AN ∧
  ∀ G_a : Cited.WGraph, G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
    (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
    ∃ out cost,
      RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
        G_a.IsSpanningTree out ∧
        G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
        (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
          (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight)

lemma stretchOnlyAN19_to_wgraphLSST {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : StretchOnlyAN19Spec Q_AN c_AN K_AN) : WGraphLSSTSpec K_AN := by
  intro G hval hloop hconn hw
  obtain ⟨out, _, _, hst, hstr⟩ := hQ G hval hloop hconn hw
  exact ⟨out, hst, hstr⟩

lemma fullAN19_to_stretchOnly {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN) : StretchOnlyAN19Spec Q_AN c_AN K_AN := by
  intro G hval hloop hconn hw
  obtain ⟨out, cost, hrun, hst, hstr, _⟩ := hQ.2 G hval hloop hconn hw
  exact ⟨out, cost, hrun, hst, hstr⟩

/-- Static LSST existence with overhead `(4 * max K_AN 1 + 5) * log²(G.n + 2)` from the
stretch-only `[AN19]` property `WGraphLSSTSpec K_AN`. -/
lemma exists_lsst_of_wgraph_spec {K_AN : ℝ} (hAN : WGraphLSSTSpec K_AN)
    {G : MGraph} (hG : G.IsValid) (hV : G.V.Nonempty)
    {ℓ v : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (hv : ∀ e ∈ G.E, 0 < v e) :
    ∃ T, IsLSST G ℓ v ((4 * max K_AN 1 + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T := by
  classical
  rw [max_comm K_AN 1]
  let K₁ : ℝ := max 1 K_AN
  have hK₁_ge1 : 1 ≤ K₁ := le_max_left _ _
  have hKAN_le : K_AN ≤ K₁ := le_max_right _ _
  let E_noloop := G.E.filter (fun e => G.tail e ≠ G.head e)
  by_cases hE_nl : E_noloop.Nonempty
  · let G_nl : MGraph := { G with E := E_noloop }
    have hG_nl_val : G_nl.IsValid := fun e he => hG e (Finset.mem_filter.mp he).1
    have hℓ_nl : ∀ e ∈ G_nl.E, 0 < ℓ e := fun e he => hℓ e (Finset.mem_filter.mp he).1
    have hv_nl : ∀ e ∈ G_nl.E, 0 < v e := fun e he => hv e (Finset.mem_filter.mp he).1
    have hnl_ne : ∀ e ∈ G_nl.E, G_nl.tail e ≠ G_nl.head e := fun e he =>
      (Finset.mem_filter.mp he).2
    let V_act : Finset ℕ := E_noloop.biUnion (fun e => {G.tail e, G.head e})
    have hV_act_sub : V_act ⊆ G.V := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have heG := hG e (Finset.mem_filter.mp he).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      exact hxe.elim (· ▸ heG.1) (· ▸ heG.2)
    have hV_act_ge2 : 2 ≤ V_act.card := by
      obtain ⟨e₀, he₀⟩ := hE_nl
      have hne₀ : G.tail e₀ ≠ G.head e₀ := (Finset.mem_filter.mp he₀).2
      have hsub2 : {G.tail e₀, G.head e₀} ⊆ V_act :=
        Finset.subset_biUnion_of_mem (fun e => {G.tail e, G.head e}) he₀
      have hcard2 : ({G.tail e₀, G.head e₀} : Finset ℕ).card = 2 := Finset.card_pair hne₀
      exact hcard2 ▸ Finset.card_le_card hsub2
    have hV_act_le_n : V_act.card ≤ G.n := Finset.card_le_card hV_act_sub
    let G_v := weightedCopyGraph G_nl v
    have hG_v_val : G_v.IsValid := weightedCopyGraph_isValid hG_nl_val v
    have hG_v_orig : ∀ e' ∈ G_v.E, origEdge (copyMod G_nl) e' ∈ E_noloop ∧
        G_v.tail e' = G.tail (origEdge (copyMod G_nl) e') ∧
        G_v.head e' = G.head (origEdge (copyMod G_nl) e') ∧
        G_v.tail e' ≠ G_v.head e' ∧ G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act := by
      intro e' he'
      have hm := weightedCopyGraph_origEdge_mem hE_nl he'
      have htl : G_v.tail e' ∈ V_act := Finset.mem_biUnion.mpr
        ⟨origEdge (copyMod G_nl) e', hm.1, by rw [hm.2.1]; exact Finset.mem_insert_self _ _⟩
      have hhd : G_v.head e' ∈ V_act := Finset.mem_biUnion.mpr
        ⟨origEdge (copyMod G_nl) e', hm.1,
          by rw [hm.2.2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      have hne : G_v.tail e' ≠ G_v.head e' := by
        rw [hm.2.1, hm.2.2]; exact hnl_ne _ hm.1
      exact ⟨hm.1, hm.2.1, hm.2.2, hne, htl, hhd⟩
    have hV_act_inc : ∀ x ∈ V_act, ∃ e' ∈ G_v.E, G_v.tail e' = x ∨ G_v.head e' = x := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have h0_mem : copyId (copyMod G_nl) e 0 ∈ G_v.E :=
        (mem_weightedCopyGraph_E_iff hE_nl).mpr ⟨e, he, 0, edgeMult_pos hE_nl hv_nl he, rfl⟩
      have ht0 : G_v.tail (copyId (copyMod G_nl) e 0) = G.tail e :=
        weightedCopyGraph_tail_copyId hE_nl he
      have hh0 : G_v.head (copyId (copyMod G_nl) e 0) = G.head e :=
        weightedCopyGraph_head_copyId hE_nl he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      exact ⟨copyId (copyMod G_nl) e 0, h0_mem,
        hxe.elim (fun h => Or.inl (ht0.trans h.symm)) (fun h => Or.inr (hh0.trans h.symm))⟩
    let V_list : List ℕ := V_act.sort (· ≤ ·)
    have hV_len : V_list.length = V_act.card := V_act.length_sort (· ≤ ·)
    have hV_nd : V_list.Nodup := V_act.sort_nodup (· ≤ ·)
    have hV_mem : ∀ x, x ∈ V_list ↔ x ∈ V_act := fun x => V_act.mem_sort (· ≤ ·)
    have hV_ne : V_list ≠ [] := by intro h; simp [h] at hV_len; omega
    let r₀ : ℕ := V_list[0]'(by omega)
    let rest : List ℕ := V_list.tail
    have hV_cons : V_list = r₀ :: rest := by
      cases hVl : V_list with
      | nil => exact absurd hVl hV_ne
      | cons a l => simp [r₀, rest, hVl]
    have hr₀_Vact : r₀ ∈ V_act := (hV_mem r₀).mp (hV_cons ▸ List.mem_cons_self)
    have hr₀_nrest : r₀ ∉ rest := by
      have := hV_nd; rw [hV_cons] at this; exact (List.nodup_cons.mp this).1
    have hrest_nd : rest.Nodup := by
      have := hV_nd; rw [hV_cons] at this; exact (List.nodup_cons.mp this).2
    let B : List ℕ := bridgeVerts G_v V_act r₀ rest
    obtain ⟨hB_nd, hB_rest, hr₀_nB, hB_conn, hB_disj⟩ :=
      bridgeVerts_props G_v V_act r₀ rest hr₀_nrest hrest_nd
    have hB_Vlist : ∀ b ∈ B, b ∈ V_list := fun b hb =>
      hV_cons ▸ List.mem_cons_of_mem _ (hB_rest b hb)
    have hB_Vact : ∀ b ∈ B, b ∈ V_act := fun b hb => (hV_mem b).mp (hB_Vlist b hb)
    have hr₀B_nd : (r₀ :: B).Nodup := List.nodup_cons.mpr ⟨hr₀_nB, hB_nd⟩
    have hB_len_lt : B.length + 1 ≤ G_v.E.card := bridgeVerts_length_le hr₀B_nd
      (fun x hx => by
        rw [List.mem_cons] at hx
        exact hx.elim (fun h => h ▸ hr₀_Vact) (fun h => hB_Vact x h))
      hV_act_inc hB_disj
    let E_list : List ℕ := G_v.E.sort (· ≤ ·)
    have hE_len : E_list.length = G_v.E.card := G_v.E.length_sort (· ≤ ·)
    have hE_nd : E_list.Nodup := G_v.E.sort_nodup (· ≤ ·)
    have hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E := fun e' => G_v.E.mem_sort (· ≤ ·)
    let m₁ : ℕ := E_list.length
    -- Scaled positive integer weights ≥ 4
    let ℓ_imgs := E_noloop.image ℓ
    have hℓ_imgs_ne : ℓ_imgs.Nonempty := Finset.image_nonempty.mpr hE_nl
    let ℓ_min : ℝ := ℓ_imgs.min' hℓ_imgs_ne
    have hℓ_min_pos : 0 < ℓ_min := by
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (Finset.min'_mem ℓ_imgs hℓ_imgs_ne)
      dsimp only [ℓ_min]; rw [← heq]; exact hℓ_nl e he
    have hℓ_min_le : ∀ e ∈ E_noloop, ℓ_min ≤ ℓ e := fun e he =>
      Finset.min'_le ℓ_imgs (ℓ e) (Finset.mem_image_of_mem _ he)
    let δ : ℝ := ℓ_min / (2 * (V_act.card : ℝ))
    have hV_act_pos_r : (0 : ℝ) < (V_act.card : ℝ) := by
      have : 0 < V_act.card := by omega
      exact_mod_cast this
    have hδ_pos : 0 < δ := div_pos hℓ_min_pos (mul_pos (by norm_num) hV_act_pos_r)
    let w_int : ℕ → ℕ := fun e' => Nat.floor (ℓ (origEdge (copyMod G_nl) e') / δ)
    have hw_int_ge : ∀ e' ∈ G_v.E, 4 ≤ w_int e' := by
      intro e' he'
      have hle_min := hℓ_min_le _ (hG_v_orig e' he').1
      have hVa4 : (4 : ℝ) ≤ 2 * (V_act.card : ℝ) := by
        have : (2 : ℝ) ≤ (V_act.card : ℝ) := by exact_mod_cast hV_act_ge2
        linarith
      have hdiv_ge : (4 : ℝ) ≤ ℓ (origEdge (copyMod G_nl) e') / δ := by
        calc (4 : ℝ) ≤ 2 * (V_act.card : ℝ) := hVa4
          _ = ℓ_min / δ := by
              have h2Va_ne : 2 * (V_act.card : ℝ) ≠ 0 := (mul_pos (by norm_num) hV_act_pos_r).ne'
              rw [eq_div_iff hδ_pos.ne']
              dsimp only [δ]
              exact mul_div_cancel₀ _ h2Va_ne
          _ ≤ ℓ (origEdge (copyMod G_nl) e') / δ := div_le_div_of_nonneg_right hle_min hδ_pos.le
      exact Nat.le_floor hdiv_ge
    let G_aug : Cited.WGraph :=
      { n := V_list.length
        edges :=
          E_list.map (fun e' => (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e')) ++
          B.map (fun b => (0, V_list.idxOf b, 1)) }
    have hG_aug_m : G_aug.m = m₁ + B.length := by
      simp [G_aug, Cited.WGraph.m, m₁]
    have hG_aug_val : G_aug.graph.IsValid := by
      intro ed hed
      dsimp only [Cited.WGraph.graph, G_aug] at hed
      rw [List.mem_map] at hed
      obtain ⟨w, hw, rfl⟩ := hed
      rw [List.mem_append] at hw
      rcases hw with hw | hw <;> rw [List.mem_map] at hw
      · obtain ⟨e', he', rfl⟩ := hw
        have ho := hG_v_orig e' ((hE_mem e').mp he')
        exact ⟨List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2.2.2.2.1),
               List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2.2.2.2.2)⟩
      · obtain ⟨b, hb, rfl⟩ := hw
        exact ⟨by dsimp only [Cited.WGraph.graph, G_aug]; omega, List.idxOf_lt_length_of_mem (hB_Vlist b hb)⟩
    have hG_aug_loopless : G_aug.graph.IsLoopless := by
      intro ed hed
      dsimp only [Cited.WGraph.graph, G_aug] at hed
      rw [List.mem_map] at hed
      obtain ⟨w, hw, rfl⟩ := hed
      rw [List.mem_append] at hw
      rcases hw with hw | hw <;> rw [List.mem_map] at hw
      · obtain ⟨e', he', rfl⟩ := hw
        have ho := hG_v_orig e' ((hE_mem e').mp he')
        intro hEq
        exact ho.2.2.2.1 (MinCostFlow.LSF.idxOf_inj_of_mem
          ((hV_mem _).mpr ho.2.2.2.2.1) ((hV_mem _).mpr ho.2.2.2.2.2) hEq)
      · obtain ⟨b, hb, rfl⟩ := hw
        dsimp only
        have hb_ne : r₀ ≠ b := fun h => by rw [← h] at hb; exact hr₀_nB hb
        intro hEq
        have h0 : V_list.idxOf r₀ = 0 := by rw [hV_cons, List.idxOf_cons_self]
        exact hb_ne (MinCostFlow.LSF.idxOf_inj_of_mem
          ((hV_mem _).mpr hr₀_Vact) (hB_Vlist b hb) (h0.trans hEq))
    have hG_aug_weights : ∀ ed ∈ G_aug.edges, 1 ≤ ed.2.2 := by
      intro ed hed
      dsimp only [G_aug] at hed
      rw [List.mem_append] at hed
      rcases hed with hed | hed <;> rw [List.mem_map] at hed
      · obtain ⟨e', he', rfl⟩ := hed
        exact Nat.le_trans (by decide) (hw_int_ge e' ((hE_mem e').mp he'))
      · obtain ⟨b, _, rfl⟩ := hed
        exact le_rfl
    have hG_aug_edge_E : ∀ (j : ℕ) (hj : j < m₁),
        G_aug.edges[j]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
          (V_list.idxOf (G_v.tail (E_list[j]'hj)),
           V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)) := by
      intro j hj
      dsimp only [G_aug]
      rw [List.getElem_append_left (by simp [m₁, hj]), List.getElem_map]
    have hG_aug_edge_B : ∀ (k : ℕ) (hk : k < B.length),
        G_aug.edges[m₁ + k]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
          (0, V_list.idxOf (B[k]'hk), 1) := by
      intro k hk
      dsimp only [G_aug]
      have hlen1 : (E_list.map (fun e' =>
          (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e'))).length = m₁ := by
        simp [m₁]
      rw [List.getElem_append_right (by omega)]
      simp only [hlen1, Nat.add_sub_cancel_left, List.getElem_map]
    let H_br := gvWithBridges G_v V_act r₀ B
    have hH_br_conn : ∀ x ∈ V_act, H_br.Connected r₀ x := by
      intro x hx
      have hxV : x ∈ r₀ :: rest := hV_cons ▸ (hV_mem x).mpr hx
      rw [List.mem_cons] at hxV
      exact hxV.elim (fun h => h ▸ connected_refl H_br r₀) (fun h => hB_conn x h)
    have hH_br_lift_walk : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
        H_br.IsWalk a b P → a ∈ V_act →
        ∃ es : List ℕ, G_aug.IsWalkIn (List.range G_aug.m) (V_list.idxOf a) (V_list.idxOf b) es := by
      intro a b P hWP ha
      induction hWP with
      | nil s => exact ⟨[], .nil _⟩
      | @cons s _ x xs hxE hsx hrest ih =>
        have hx_edge : (x.1 ∈ G_v.E ∧ H_br.tail x.1 = G_v.tail x.1 ∧ H_br.head x.1 = G_v.head x.1) ∨
            (∃ b' ∈ B, x.1 = copyMod G_v + b' ∧ H_br.tail x.1 = r₀ ∧ H_br.head x.1 = b') := by
          dsimp only [H_br, gvWithBridges] at hxE ⊢
          rw [Finset.mem_union] at hxE
          rcases hxE with hxG | hxb
          · left; exact ⟨hxG, ite_eq_left hxG, ite_eq_left hxG⟩
          · right
            rw [Finset.mem_image] at hxb
            obtain ⟨b', hb', hbeq⟩ := hxb
            have hb'_mem := List.mem_toFinset.mp hb'
            have hnG : copyMod G_v + b' ∉ G_v.E := fun h =>
              Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
            refine ⟨b', hb'_mem, hbeq.symm, ?_, ?_⟩
            · rw [← hbeq]; exact ite_eq_right hnG
            · rw [← hbeq, ite_eq_right hnG, Nat.add_sub_cancel_left]
        have hdst_Vact : H_br.dst x ∈ V_act := by
          rcases hx_edge with ⟨hxG, ht, hh⟩ | ⟨b', hb', _, ht, hh⟩
          · have ho := hG_v_orig x.1 hxG
            cases hx2 : x.2
            · simp [MGraph.dst, hx2, ht]; exact ho.2.2.2.2.1
            · simp [MGraph.dst, hx2, hh]; exact ho.2.2.2.2.2
          · cases hx2 : x.2
            · simp [MGraph.dst, hx2, ht]; exact hr₀_Vact
            · simp [MGraph.dst, hx2, hh]; exact hB_Vact b' hb'
        obtain ⟨es, hes⟩ := ih hdst_Vact
        rcases hx_edge with ⟨hxG, ht, hh⟩ | ⟨b', hb', _, ht, hh⟩
        · let j := E_list.idxOf x.1
          have hj_lt : j < m₁ := List.idxOf_lt_length_of_mem ((hE_mem _).mpr hxG)
          have hj_len : j < G_aug.edges.length := by change j < G_aug.m; rw [hG_aug_m]; omega
          have hj_m : j < G_aug.m := hj_len
          have hj_rng : j ∈ List.range G_aug.m := List.mem_range.mpr hj_m
          have hj_get : E_list[j]'hj_lt = x.1 := List.getElem_idxOf hj_lt
          have hged : G_aug.edges[j]'hj_len =
              (V_list.idxOf (G_v.tail x.1), V_list.idxOf (G_v.head x.1), w_int x.1) := by
            rw [hG_aug_edge_E j hj_lt, hj_get]
          have hend : (G_aug.edges[j]'hj_len).1 = V_list.idxOf s ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf (H_br.dst x) ∨
              (G_aug.edges[j]'hj_len).1 = V_list.idxOf (H_br.dst x) ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf s := by
            rw [hged, ← hsx]
            cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, ht, hh]
          exact ⟨j :: es, .cons hj_rng hj_m hend hes⟩
        · let k := B.idxOf b'
          have hk_lt : k < B.length := List.idxOf_lt_length_of_mem hb'
          let j := m₁ + k
          have hj_len : j < G_aug.edges.length := by change j < G_aug.m; rw [hG_aug_m]; omega
          have hj_m : j < G_aug.m := hj_len
          have hj_rng : j ∈ List.range G_aug.m := List.mem_range.mpr hj_m
          have hk_get : B[k]'hk_lt = b' := List.getElem_idxOf hk_lt
          have hged : G_aug.edges[j]'hj_len = (0, V_list.idxOf b', 1) := by
            dsimp only [j]
            rw [hG_aug_edge_B k hk_lt, hk_get]
          have h0_eq : (0 : ℕ) = V_list.idxOf r₀ := by
            rw [hV_cons, List.idxOf_cons_self]
          have hend : (G_aug.edges[j]'hj_len).1 = V_list.idxOf s ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf (H_br.dst x) ∨
              (G_aug.edges[j]'hj_len).1 = V_list.idxOf (H_br.dst x) ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf s := by
            rw [hged, h0_eq, ← hsx]
            cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, ht, hh]
          exact ⟨j :: es, .cons hj_rng hj_m hend hes⟩
    have hG_aug_conn : G_aug.IsConnected := by
      refine ⟨by dsimp only [G_aug]; rw [hV_len]; omega, fun u hu v hv => ?_⟩
      have hu_Vact : V_list[u]'hu ∈ V_act := (hV_mem _).mp (List.getElem_mem hu)
      have hv_Vact : V_list[v]'hv ∈ V_act := (hV_mem _).mp (List.getElem_mem hv)
      have hconn_uv := connected_trans (connected_symm (hH_br_conn _ hu_Vact)) (hH_br_conn _ hv_Vact)
      obtain ⟨P, hWP⟩ := hconn_uv
      obtain ⟨es, hes⟩ := hH_br_lift_walk hWP hu_Vact
      rw [MinCostFlow.LSF.idxOf_getElem_of_nodup hV_nd hu,
          MinCostFlow.LSF.idxOf_getElem_of_nodup hV_nd hv] at hes
      exact ⟨es, hes⟩
    obtain ⟨out, hT_st_out, htot_st⟩ :=
      hAN G_aug hG_aug_val hG_aug_loopless hG_aug_conn hG_aug_weights
    rcases hT_st_out with ⟨hout_nd, hout_lt, hout_len, hout_conn⟩
    let bridgeBase : ℕ := max (copyMod G) (copyMod G_v)
    let edgeIdGv : ℕ → ℕ := fun j =>
      if h : j < m₁ then E_list[j]'h else bridgeBase + B[j - m₁]?.getD 0
    have hedgeId_ge : ∀ j, m₁ ≤ j → bridgeBase ≤ edgeIdGv j := fun j hj => by
      dsimp only [edgeIdGv]
      rw [dite_eq_right_of_eq_false (eq_false (Nat.not_lt_of_ge hj))]
      exact Nat.le_add_right _ _
    have hedgeId_lt : ∀ j, (h : j < m₁) → edgeIdGv j ∈ G_v.E := fun j hj => by
      dsimp only [edgeIdGv]
      rw [dite_eq_left_of_eq_true (eq_true hj)]
      exact (hE_mem _).mp (List.getElem_mem hj)
    have hedgeId_inj : ∀ j₁ < G_aug.m, ∀ j₂ < G_aug.m,
        edgeIdGv j₁ = edgeIdGv j₂ → j₁ = j₂ := by
      intro j₁ hj₁ j₂ hj₂ hEq
      by_cases h1 : j₁ < m₁ <;> by_cases h2 : j₂ < m₁
      · dsimp only [edgeIdGv] at hEq
        rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)] at hEq
        exact (List.Nodup.getElem_inj hE_nd).mp hEq
      · exfalso
        have hlt := lt_copyMod (hedgeId_lt j₁ h1)
        have hge := (le_max_right (copyMod G) (copyMod G_v)).trans (hedgeId_ge j₂ (Nat.le_of_not_lt h2))
        omega
      · exfalso
        have hlt := lt_copyMod (hedgeId_lt j₂ h2)
        have hge := (le_max_right (copyMod G) (copyMod G_v)).trans (hedgeId_ge j₁ (Nat.le_of_not_lt h1))
        omega
      · dsimp only [edgeIdGv] at hEq
        rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2)] at hEq
        have hk1 : j₁ - m₁ < B.length := by rw [hG_aug_m] at hj₁; omega
        have hk2 : j₂ - m₁ < B.length := by rw [hG_aug_m] at hj₂; omega
        have hB_eq : B[j₁ - m₁]'hk1 = B[j₂ - m₁]'hk2 := by
          simp only [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2, Option.getD_some] at hEq
          omega
        have := (List.Nodup.getElem_inj hB_nd).mp hB_eq
        omega
    let idxGv : Finset ℕ := out.toFinset
    let T_gv : MGraph :=
      { V := V_act
        E := idxGv.image edgeIdGv
        tail := fun f => if f ∈ G_v.E then G_v.tail f else r₀
        head := fun f => if f ∈ G_v.E then G_v.head f else f - bridgeBase }
    have hT_gv_E_card : T_gv.E.card = V_act.card - 1 := by
      dsimp only [T_gv, idxGv]
      rw [Finset.card_image_of_injOn (fun a ha b hb h =>
        hedgeId_inj a (hout_lt a (List.mem_toFinset.mp ha))
          b (hout_lt b (List.mem_toFinset.mp hb)) h)]
      rw [List.toFinset_card_of_nodup hout_nd, hout_len]
      dsimp only [G_aug]
      rw [hV_len]
    have hT_gv_edge_B : ∀ j (hj : j ∈ out) (hnj : ¬ j < m₁),
        let b := B[j - m₁]'(by have := hout_lt j hj; rw [hG_aug_m] at this; omega)
        edgeIdGv j = bridgeBase + b ∧
        edgeIdGv j ∉ G_v.E ∧
        T_gv.tail (edgeIdGv j) = r₀ ∧ T_gv.head (edgeIdGv j) = b := by
      intro j hj hnj
      have hjm := hout_lt j hj
      have hk : j - m₁ < B.length := by rw [hG_aug_m] at hjm; omega
      have hnG : edgeIdGv j ∉ G_v.E := fun h =>
        Nat.not_lt_of_ge ((le_max_right (copyMod G) (copyMod G_v)).trans
          (hedgeId_ge j (Nat.le_of_not_lt hnj))) (lt_copyMod h)
      have heq_id : edgeIdGv j = bridgeBase + B[j - m₁]'hk := by
        dsimp only [edgeIdGv]
        rw [dite_eq_right_of_eq_false (eq_false hnj), List.getElem?_eq_getElem hk, Option.getD_some]
      refine ⟨heq_id, hnG, ?_, ?_⟩
      · dsimp only [T_gv]; exact ite_eq_right hnG
      · dsimp only [T_gv]; rw [ite_eq_right hnG, heq_id, Nat.add_sub_cancel_left]
    have hT_gv_val : T_gv.IsValid := by
      intro f hf
      dsimp only [T_gv] at hf ⊢
      rw [Finset.mem_image] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hj_out := List.mem_toFinset.mp hj
      by_cases hjm : j < m₁
      · have hfG := hedgeId_lt j hjm
        rw [ite_eq_left hfG, ite_eq_left hfG]
        have ho := hG_v_orig _ hfG
        exact ⟨ho.2.2.2.2.1, ho.2.2.2.2.2⟩
      · obtain ⟨heq_id, hnG, _, _⟩ := hT_gv_edge_B j hj_out hjm
        have hb_mem : B[j - m₁]'(by have := hout_lt j hj_out; rw [hG_aug_m] at this; omega) ∈ B :=
          List.getElem_mem _
        rw [ite_eq_right hnG, ite_eq_right hnG, heq_id, Nat.add_sub_cancel_left]
        exact ⟨hr₀_Vact, hB_Vact _ hb_mem⟩
    have hT_gv_lift : ∀ {a b : ℕ} {es : List ℕ},
        G_aug.IsWalkIn out a b es →
        ∀ u ∈ V_act, ∀ v ∈ V_act,
        V_list.idxOf u = a → V_list.idxOf v = b →
        ∃ P : List (ℕ × Bool), T_gv.IsWalk u v P ∧ P.map Prod.fst = es.map edgeIdGv := by
      intro a b es hes
      induction hes with
      | nil s =>
        intro u hu v hv hua hvb
        have huv : u = v := MinCostFlow.LSF.idxOf_inj_of_mem
          ((hV_mem _).mpr hu) ((hV_mem _).mpr hv) (hua.trans hvb.symm)
        subst huv; exact ⟨[], .nil u, rfl⟩
      | @cons a_cur x_next b_fin j es' hj_out hj_m hend hrest ih =>
        intro u hu v hv hua hvb
        have hx_lt : x_next < V_list.length := by
          rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
          · rw [← h2]; exact (hG_aug_val _ (List.mem_map.mpr ⟨_, List.getElem_mem hj_m, rfl⟩)).2
          · rw [← h1]; exact (hG_aug_val _ (List.mem_map.mpr ⟨_, List.getElem_mem hj_m, rfl⟩)).1
        let w := V_list[x_next]'hx_lt
        have hw_Vact : w ∈ V_act := (hV_mem w).mp (List.getElem_mem hx_lt)
        have hwx : V_list.idxOf w = x_next := MinCostFlow.LSF.idxOf_getElem_of_nodup hV_nd hx_lt
        obtain ⟨P, hWP, hP_map⟩ := ih w hw_Vact v hv hwx hvb
        have hf_mem : edgeIdGv j ∈ T_gv.E :=
          Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hj_out)
        have hj_len : j < G_aug.edges.length := by rw [← Cited.WGraph.m]; exact hj_m
        have hends_j : V_list.idxOf (T_gv.tail (edgeIdGv j)) = (G_aug.edges[j]'hj_len).1 ∧
            V_list.idxOf (T_gv.head (edgeIdGv j)) = (G_aug.edges[j]'hj_len).2.1 ∧
            T_gv.tail (edgeIdGv j) ∈ V_act ∧ T_gv.head (edgeIdGv j) ∈ V_act := by
          by_cases hjm1 : j < m₁
          · have hfG := hedgeId_lt j hjm1
            have hget : E_list[j]'hjm1 = edgeIdGv j := by
              dsimp only [edgeIdGv]
              exact (dite_eq_left_of_eq_true (eq_true hjm1)).symm
            have hged : G_aug.edges[j]'hj_len =
                (V_list.idxOf (G_v.tail (edgeIdGv j)), V_list.idxOf (G_v.head (edgeIdGv j)),
                  w_int (edgeIdGv j)) := by
              simpa only [hget] using hG_aug_edge_E j hjm1
            have ht_eq : T_gv.tail (edgeIdGv j) = G_v.tail (edgeIdGv j) := by
              dsimp only [T_gv]; exact ite_eq_left hfG
            have hh_eq : T_gv.head (edgeIdGv j) = G_v.head (edgeIdGv j) := by
              dsimp only [T_gv]; exact ite_eq_left hfG
            have ho := hG_v_orig _ hfG
            rw [hged, ht_eq, hh_eq]
            exact ⟨rfl, rfl, ho.2.2.2.2.1, ho.2.2.2.2.2⟩
          · have hk : j - m₁ < B.length := by rw [hG_aug_m] at hj_m; omega
            obtain ⟨_, _, ht_eq, hh_eq⟩ := hT_gv_edge_B j hj_out hjm1
            have hm1k : m₁ + (j - m₁) = j := by omega
            have hged : G_aug.edges[j]'hj_len = (0, V_list.idxOf (B[j - m₁]'hk), 1) := by
              have hB' := hG_aug_edge_B (j - m₁) hk
              simpa only [hm1k] using hB'
            have h0_eq : V_list.idxOf r₀ = 0 := by rw [hV_cons, List.idxOf_cons_self]
            rw [hged, ht_eq, hh_eq, h0_eq]
            exact ⟨rfl, rfl, hr₀_Vact, hB_Vact _ (List.getElem_mem hk)⟩
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hu_eq : T_gv.tail (edgeIdGv j) = u := MinCostFlow.LSF.idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.1) ((hV_mem _).mpr hu) (hends_j.1.trans (h1.trans hua.symm))
          have hw_eq : T_gv.head (edgeIdGv j) = w := MinCostFlow.LSF.idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.2) ((hV_mem _).mpr hw_Vact) (hends_j.2.1.trans (h2.trans hwx.symm))
          refine ⟨(edgeIdGv j, true) :: P, .cons hf_mem (by simp [MGraph.src, hu_eq])
            (by simpa [MGraph.dst, hw_eq] using hWP), by simp [hP_map]⟩
        · have hu_eq : T_gv.head (edgeIdGv j) = u := MinCostFlow.LSF.idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.2) ((hV_mem _).mpr hu) (hends_j.2.1.trans (h2.trans hua.symm))
          have hw_eq : T_gv.tail (edgeIdGv j) = w := MinCostFlow.LSF.idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.1) ((hV_mem _).mpr hw_Vact) (hends_j.1.trans (h1.trans hwx.symm))
          refine ⟨(edgeIdGv j, false) :: P, .cons hf_mem (by simp [MGraph.src, hu_eq])
            (by simpa [MGraph.dst, hw_eq] using hWP), by simp [hP_map]⟩
    have hT_gv_conn : ∀ u ∈ V_act, ∀ v ∈ V_act, T_gv.Connected u v := by
      intro u hu v hv
      obtain ⟨es, hes⟩ := hout_conn (V_list.idxOf u) (List.idxOf_lt_length_of_mem ((hV_mem _).mpr hu))
        (V_list.idxOf v) (List.idxOf_lt_length_of_mem ((hV_mem _).mpr hv))
      obtain ⟨P, hWP, _⟩ := hT_gv_lift hes u hu v hv rfl rfl
      exact ⟨P, hWP⟩
    have hT_gv_st : T_gv.IsSpanningTreeOn V_act :=
      ⟨isForest_of_connected_card_le hT_gv_val ⟨r₀, hr₀_Vact⟩ hT_gv_conn (by rw [hT_gv_E_card]),
        rfl, hT_gv_conn⟩
    have hT_gv_no_bridges : ∀ e' ∈ G_v.E,
        walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E := by
      intro e' he' f hf
      have ho := hG_v_orig e' he'
      have hP := forestPath_isPath hT_gv_st.1 (hT_gv_conn _ ho.2.2.2.2.1 _ ho.2.2.2.2.2)
      obtain ⟨bf, hbf⟩ := mem_walkEdges_iff.mp hf
      have hfT : f ∈ T_gv.E := IsWalk_edges_mem hP.1 hbf
      dsimp only [T_gv, idxGv] at hfT
      rw [Finset.mem_image] at hfT
      obtain ⟨j, hj, rfl⟩ := hfT
      have hj_out := List.mem_toFinset.mp hj
      by_cases hjm : j < m₁
      · exact hedgeId_lt j hjm
      · exfalso
        have hjm_aug := hout_lt j hj_out
        have hk : j - m₁ < B.length := by rw [hG_aug_m] at hjm_aug; omega
        let b := B[j - m₁]'hk
        have hb_mem : b ∈ B := List.getElem_mem hk
        obtain ⟨hj_id, _, htf, hhf⟩ := hT_gv_edge_B j hj_out hjm
        let S_b := V_act.filter (fun w => G_v.Connected b w)
        have hb_Sb : b ∈ S_b := Finset.mem_filter.mpr ⟨hB_Vact b hb_mem, connected_refl G_v b⟩
        have hr₀_Sb : r₀ ∉ S_b := fun h => hB_disj r₀ List.mem_cons_self b
          (List.mem_cons_of_mem _ hb_mem) (fun heq => by
            have hb_mem' : b ∈ B := hb_mem
            rw [← heq] at hb_mem'
            exact hr₀_nB hb_mem')
          (connected_symm (Finset.mem_filter.mp h).2)
        have hsame_e' : G_v.tail e' ∈ S_b ↔ G_v.head e' ∈ S_b := by
          have hc : G_v.Connected (G_v.tail e') (G_v.head e') :=
            ⟨[(e', true)], .cons he' rfl (.nil _)⟩
          constructor <;> intro hmem
          · exact Finset.mem_filter.mpr ⟨ho.2.2.2.2.2,
              connected_trans (Finset.mem_filter.mp hmem).2 hc⟩
          · exact Finset.mem_filter.mpr ⟨ho.2.2.2.2.1,
              connected_trans (Finset.mem_filter.mp hmem).2 (connected_symm hc)⟩
        have hother : ∀ g ∈ walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')),
            g ≠ edgeIdGv j → (T_gv.tail g ∈ S_b ↔ T_gv.head g ∈ S_b) := by
          intro g hg hne
          obtain ⟨bg, hbg⟩ := mem_walkEdges_iff.mp hg
          have hgT : g ∈ T_gv.E := IsWalk_edges_mem hP.1 hbg
          dsimp only [T_gv, idxGv] at hgT
          rw [Finset.mem_image] at hgT
          obtain ⟨j', hj', rfl⟩ := hgT
          have hj'_out := List.mem_toFinset.mp hj'
          by_cases hj'm : j' < m₁
          · have hgG := hedgeId_lt j' hj'm
            have hgo := hG_v_orig _ hgG
            have hgt : T_gv.tail (edgeIdGv j') = G_v.tail (edgeIdGv j') := by
              dsimp only [T_gv]; exact ite_eq_left hgG
            have hgh : T_gv.head (edgeIdGv j') = G_v.head (edgeIdGv j') := by
              dsimp only [T_gv]; exact ite_eq_left hgG
            rw [hgt, hgh]
            have hgc : G_v.Connected (G_v.tail (edgeIdGv j')) (G_v.head (edgeIdGv j')) :=
              ⟨[(edgeIdGv j', true)], .cons hgG rfl (.nil _)⟩
            constructor <;> intro hmem
            · exact Finset.mem_filter.mpr ⟨hgo.2.2.2.2.2,
                connected_trans (Finset.mem_filter.mp hmem).2 hgc⟩
            · exact Finset.mem_filter.mpr ⟨hgo.2.2.2.2.1,
                connected_trans (Finset.mem_filter.mp hmem).2 (connected_symm hgc)⟩
          · have hk' : j' - m₁ < B.length := by
              have := hout_lt j' hj'_out; rw [hG_aug_m] at this; omega
            let b' := B[j' - m₁]'hk'
            have hb'_mem : b' ∈ B := List.getElem_mem hk'
            obtain ⟨hj'_id, _, hgt, hgh⟩ := hT_gv_edge_B j' hj'_out hj'm
            have hbb' : b ≠ b' := by
              intro hEq
              exact hne (hj'_id.trans ((congrArg (bridgeBase + ·) hEq.symm).trans hj_id.symm))
            have hb'_nSb : b' ∉ S_b := fun h => hB_disj b (List.mem_cons_of_mem _ hb_mem)
              b' (List.mem_cons_of_mem _ hb'_mem) hbb' (Finset.mem_filter.mp h).2
            rw [hgt, hgh]
            exact ⟨fun h => absurd h hr₀_Sb, fun h => absurd h hb'_nSb⟩
        have hcross : ¬ (T_gv.tail (edgeIdGv j) ∈ S_b ↔ T_gv.head (edgeIdGv j) ∈ S_b) := by
          rw [htf, hhf]; exact fun h => hr₀_Sb (h.mpr hb_Sb)
        exact isPath_no_unique_cut_edge hP hsame_e' hother hcross hf
    let base := max bridgeBase (T_gv.E.sup id + 1)
    let T_raw := attachVerts T_gv r₀ G.V base
    have hT_raw_st : T_raw.IsSpanningTreeOn G_v.V := by
      rw [weightedCopyGraph_V]
      exact attachVerts_isSpanningTreeOn hT_gv_st hr₀_Vact hV_act_sub
        (fun f hf => Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hf))
          (le_max_right _ _))
    have hT_raw_sub : T_raw.IsSubgraph T_gv :=
      ⟨hV_act_sub, Finset.subset_union_left, fun f hf => by
        dsimp only [T_raw, attachVerts]; exact ⟨(ite_eq_left hf).symm, (ite_eq_left hf).symm⟩⟩
    have hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G ≤ f := by
      intro f hf hf_nG
      dsimp only [T_raw, attachVerts] at hf
      rw [Finset.mem_union] at hf
      rcases hf with hf_gv | hf_att
      · dsimp only [T_gv, idxGv] at hf_gv
        rw [Finset.mem_image] at hf_gv
        obtain ⟨j, _, rfl⟩ := hf_gv
        by_cases hjm : j < m₁
        · exact absurd (hedgeId_lt j hjm) hf_nG
        · exact (le_max_left (copyMod G) (copyMod G_v)).trans (hedgeId_ge j (Nat.le_of_not_lt hjm))
      · rw [Finset.mem_image] at hf_att
        obtain ⟨w, _, rfl⟩ := hf_att
        exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
    have hT_raw_Gv_edges : ∀ f ∈ T_raw.E, f ∈ G_v.E →
        T_raw.tail f = G_v.tail f ∧ T_raw.head f = G_v.head f := by
      intro f hf hfG
      dsimp only [T_raw, attachVerts] at hf ⊢
      have hf_gv : f ∈ T_gv.E := by
        rw [Finset.mem_union] at hf
        rcases hf with h | h
        · exact h
        · exfalso
          rw [Finset.mem_image] at h
          obtain ⟨w, _, rfl⟩ := h
          have hlt := lt_copyMod hfG
          have hge : copyMod G_v ≤ base + w :=
            le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
          omega
      rw [ite_eq_left hf_gv, ite_eq_left hf_gv]
      dsimp only [T_gv]
      exact ⟨ite_eq_left hfG, ite_eq_left hfG⟩
    have hT_raw_path_eq : ∀ e' ∈ G_v.E,
        T_raw.forestPath (G_v.tail e') (G_v.head e') =
          T_gv.forestPath (G_v.tail e') (G_v.head e') := by
      intro e' he'
      have ho := hG_v_orig e' he'
      exact (forestPath_subgraph hT_raw_st.1 hT_raw_sub (hT_gv_conn _ ho.2.2.2.2.1 _ ho.2.2.2.2.2)).symm
    have hsum_raw : ∑ e' ∈ G_v.E, treeStretch G_v T_raw (weightedCopyLen G_nl ℓ) e' ≤
        (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_v.norm1 (fun _ => 1)) := by
      refine MinCostFlow.LSF.an19_stretch_sum_bound (Finset.card_pos.mpr hV) hV_act_ge2 hV_act_le_n
        hV_len hV_mem
        (fun e' he' => let ho := hG_v_orig e' he'; ⟨ho.2.2.2.2.1, ho.2.2.2.2.2⟩)
        hB_len_lt hE_len hE_nd hE_mem hδ_pos hw_int_ge
        (fun e' he' => weightedCopyLen_pos hE_nl hℓ_nl he')
        (fun f _ => by
          dsimp only [weightedCopyLen, w_int]
          have hlt := Nat.lt_floor_add_one (ℓ (origEdge (copyMod G_nl) f) / δ)
          have hmul := mul_le_mul_of_nonneg_left hlt.le hδ_pos.le
          have heq : δ * (ℓ (origEdge (copyMod G_nl) f) / δ) = ℓ (origEdge (copyMod G_nl) f) :=
            mul_div_cancel₀ _ hδ_pos.ne'
          linarith)
        (fun e' he' => by
          have ho := hG_v_orig e' he'
          dsimp only [weightedCopyLen, w_int]
          have hfl := Nat.floor_le (div_nonneg (hℓ_nl _ ho.1).le hδ_pos.le)
          have hmul := mul_le_mul_of_nonneg_left hfl hδ_pos.le
          have heq : δ * (ℓ (origEdge (copyMod G_nl) e') / δ) = ℓ (origEdge (copyMod G_nl) e') :=
            mul_div_cancel₀ _ hδ_pos.ne'
          linarith)
        (fun e' he' => by
          have ho := hG_v_orig e' he'
          have hVa_ne : (V_act.card : ℝ) ≠ 0 := by
            have : 0 < V_act.card := by omega
            exact_mod_cast this.ne'
          have heq : δ * (V_act.card : ℝ) = ℓ_min / 2 := by
            dsimp only [δ]
            calc (ℓ_min / (2 * (V_act.card : ℝ))) * (V_act.card : ℝ)
                = (ℓ_min / 2) * ((V_act.card : ℝ) / (V_act.card : ℝ)) := by ring
              _ = ℓ_min / 2 := by rw [div_self hVa_ne, mul_one]
          rw [heq]
          exact div_le_div_of_nonneg_right (hℓ_min_le _ ho.1) (by norm_num))
        rfl hG_aug_m hG_aug_edge_E hG_aug_edge_B hout_conn htot_st hK₁_ge1 hKAN_le
        hedgeId_lt
        (fun j hj => by dsimp only [edgeIdGv]; exact dite_eq_left_of_eq_true (eq_true hj))
        (fun k hk hnk => (hT_gv_edge_B k hk hnk).2.1)
        rfl hT_gv_val hT_gv_st hT_gv_conn hT_gv_lift hT_gv_no_bridges hT_raw_path_eq
    have hlsst_raw : IsLSST G_v (weightedCopyLen G_nl ℓ) (fun _ => 1)
        ((2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T_raw := by
      refine ⟨hT_raw_st, hT_raw_Gv_edges, fun e' he' f hf => ?_, ?_⟩
      · rw [hT_raw_path_eq e' he'] at hf
        exact hT_gv_no_bridges e' he' hf
      · simpa only [one_mul] using hsum_raw
    exact ⟨projectTree G_nl v T_raw,
      MinCostFlow.LSF.lsst_of_projectTree (G_nl := G_nl) (G_v := G_v) (T_raw := T_raw)
        hG hV hK₁_ge1 rfl rfl hE_nl hℓ hv hT_raw_nonGv hlsst_raw⟩
  · exact MinCostFlow.LSF.exists_lsst_when_no_nonloop hG hV hv
      (fun e he => by
        by_contra hne
        exact hE_nl ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩⟩) hK₁_ge1

end MinCostFlow.SparseCore.Program
