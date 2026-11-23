module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Basic.Graph
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.Runtime
public import MinCostFlow.Spanner.Theorem81
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.Spanner.MGraphSpec

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import MinCostFlow.Spanner.VacuityReach

/-!
# Non-Vacuity Witnesses for Theorem 8.1

This file discharges the requirement **"Show that hypotheses can hold"** by constructing explicit
instances of all algorithm-parameter structures in `MinCostFlow.Spanner`:

1. `exists_boundedConstructExpanderTool`: explicit cycle + self-loops expander construction for all
   `(N_max, W_max)`.
2. `exists_decomposeTool`: explicit global `DecomposeTool` over arbitrary valid loopless multigraphs
   with `φ_dec G = 1 / (2 · G.m + 2)` and all edges at level `i₀ = ⌊log₂(m + 1)⌋ + 1`.
3. `exists_pathDSTool`: explicit global `PathDSTool` answering `getPath` via minimum-length simple
   walks and setting `V̂ := V(G)` upon any deletion (`γ_del = 2 M + 1`).
4. `exists_localSpannerTools` and `theorem_8_1_nonvacuous`: proves that `theorem_8_1_local` holds
   non-vacuously on all valid `(H', J, embJH)`, verified on a concrete 3-vertex triangle graph.
5. Round-2 runtime and `MGraph` witnesses: `exists_spannerToolCosts`, `exists_decomposeMonotone`,
   `exists_pathDSMonotone`, `exists_sparsifyMG_witness`, `triangleMGraph_local_example`, and
   `triangleMGraph_sparsifyMG_example`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

private noncomputable def decompFn (G : Graph) : DecomposeOutput :=
  if G.m = 0 then ⟨0, fun _ => 0, fun _ => []⟩
  else
    let i₀ := Nat.log 2 (G.m + 1) + 1
    { ℓ := i₀
      level := fun _ => i₀
      comps := fun i =>
        if i = i₀ then
          ((List.range G.n).filterMap fun u =>
            if 1 ≤ G.deg u then some (compOf G u) else none).dedup
        else [] }

private theorem map_range_getD_eq {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
        List.map_singleton]
    have hpref : (List.range xs.length).map (fun j => (xs ++ [x]).getD j d) =
        (List.range xs.length).map (fun j => xs.getD j d) := by
      refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.mp hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
    rw [hpref, ih]
    simp [List.getD_eq_getElem?_getD]

private noncomputable def decompToolImpl : DecomposeTool := by
  refine ⟨1, fun G => 1 / (2 * (G.m : ℝ) + 2), decompFn, le_rfl, ?_, ?_, ?_⟩
  · intro _ _ _; positivity
  · intro G _ _
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) G.m]
  · intro G hG hL
    dsimp only [decompFn]
    by_cases hm0 : G.m = 0
    · simp only [hm0, ↓reduceIte]
      have hlog0 : ((0 : ℕ) : ℝ) ≤ 1 * ((Nat.log 2 (0 + 2) : ℝ) + 1) := by
        rw [Nat.cast_zero]; positivity
      refine ⟨hlog0, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi => ?_, fun i hpos hle => by omega⟩
      have hi0 : i = 0 := by omega
      subst hi0
      have hm_at : (DecomposeOutput.graphAt G ⟨0, fun _ => 0, fun _ => []⟩ 0).m = 0 := by
        have hlen : G.edges.length = 0 := hm0
        simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, Graph.m, List.length_map]
        rw [hlen]
        simp only [List.range_zero, List.filter_nil, List.length_nil]
      exact Nat.le_trans (Nat.le_of_eq hm_at) (Nat.zero_le _)
    · simp only [hm0, ↓reduceIte]
      have hm_pos : 0 < G.m := Nat.pos_of_ne_zero hm0
      let i₀ := Nat.log 2 (G.m + 1) + 1
      have hi₀_pos : 0 < i₀ := Nat.succ_pos _
      have hℓ : (i₀ : ℝ) ≤ 1 * ((Nat.log 2 (G.m + 2) : ℝ) + 1) := by
        rw [one_mul]
        have hmono : Nat.log 2 (G.m + 1) ≤ Nat.log 2 (G.m + 2) := Nat.log_mono_right (by omega)
        exact_mod_cast Nat.add_le_add_right hmono 1
      let compsFn : ℕ → List (Finset ℕ) := fun i =>
        if i = i₀ then ((List.range G.n).filterMap fun u =>
          if 1 ≤ G.deg u then some (compOf G u) else none).dedup else []
      have hg0 : DecomposeOutput.graphAt G
          { ℓ := i₀, level := fun _ => i₀, comps := compsFn } i₀ = G := by
        cases G with
        | mk n edges =>
          dsimp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, Graph.m]
          simp only [decide_true, List.filter_true]
          congr 1
          exact map_range_getD_eq edges (0, 0)
      have hGm_lt : G.m < 2 ^ i₀ := by
        have h1 := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (G.m + 1)
        exact Nat.lt_of_succ_lt h1
      have hGn_ge2 : 2 ≤ G.n := by
        have he0 : G.edges[0]'hm_pos ∈ G.edges := List.getElem_mem hm_pos
        have hval := hG _ he0
        have hneq := hL _ he0
        omega
      have hgm_le : ∀ i ≤ i₀, (DecomposeOutput.graphAt G
          { ℓ := i₀, level := fun _ => i₀, comps := compsFn } i).m ≤ 2 ^ i * G.n := by
        intro i hi
        by_cases hie : i = i₀
        · subst hie
          rw [hg0]
          calc G.m ≤ 2 ^ i₀ := hGm_lt.le
            _ = 2 ^ i₀ * 1 := (Nat.mul_one _).symm
            _ ≤ 2 ^ i₀ * G.n := Nat.mul_le_mul_left _ (by omega)
        · dsimp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt]
          have hfil : (List.range G.m).filter (fun j => decide (i₀ = i)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro j _
            simp [Ne.symm hie]
          rw [hfil, List.map_nil]
          simp only [Graph.m, List.length_nil]
          exact Nat.zero_le _
      refine ⟨hℓ, fun j _ => le_rfl, hgm_le, fun i hi_pos hi_le => ?_⟩
      by_cases hie : i = i₀
      swap
      · have hcomps_empty : (if i = Nat.log 2 (G.m + 1) + 1 then
            ((List.range G.n).filterMap fun u =>
              if 1 ≤ G.deg u then some (compOf G u) else none).dedup else []) = [] :=
          ite_eq_right_iff.mpr fun h => absurd h hie
        refine ⟨?_, ?_, ?_⟩
        · rw [hcomps_empty]; exact List.Pairwise.nil
        · intro X hX; rw [hcomps_empty] at hX; cases hX
        · intro e he
          dsimp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt] at he
          have hne_i : Nat.log 2 (G.m + 1) + 1 ≠ i := fun h => hie h.symm
          have hfil : (List.range G.m).filter (fun j => decide (Nat.log 2 (G.m + 1) + 1 = i)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro j _
            simp [hne_i]
          rw [hfil, List.map_nil] at he
          cases he
      · have hcmps : (if i = Nat.log 2 (G.m + 1) + 1 then
            ((List.range G.n).filterMap fun u =>
              if 1 ≤ G.deg u then some (compOf G u) else none).dedup else []) =
            ((List.range G.n).filterMap fun u =>
              if 1 ≤ G.deg u then some (compOf G u) else none).dedup :=
          ite_eq_left_iff.mpr fun h => absurd hie h
        have hg_raw : DecomposeOutput.graphAt G
            { ℓ := Nat.log 2 (G.m + 1) + 1, level := fun _ => Nat.log 2 (G.m + 1) + 1,
              comps := fun i => if i = Nat.log 2 (G.m + 1) + 1 then
                ((List.range G.n).filterMap fun u =>
                  if 1 ≤ G.deg u then some (compOf G u) else none).dedup else [] } i = G := by
          rw [hie]; exact hg0
        rw [hcmps, hg_raw]
        let rawComps := ((List.range G.n).filterMap fun u =>
          if 1 ≤ G.deg u then some (compOf G u) else none).dedup
        have hX_prop : ∀ X ∈ rawComps,
            ∃ u < G.n, 1 ≤ G.deg u ∧ X = compOf G u := by
          intro X hX
          rw [List.mem_dedup, List.mem_filterMap] at hX
          rcases hX with ⟨u, hu_r, hif⟩
          split_ifs at hif with hdeg
          · simp only [Option.some.injEq] at hif
            exact ⟨u, List.mem_range.mp hu_r, hdeg, hif.symm⟩
        have hdisj : rawComps.Pairwise Disjoint := by
          have hnodup : rawComps.Nodup := List.nodup_dedup _
          rw [List.pairwise_iff_getElem]
          intro p q hp hq hpq
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          obtain ⟨u, hu, _, hXp⟩ := hX_prop _ (List.getElem_mem hp)
          obtain ⟨v, hv, _, hXq⟩ := hX_prop _ (List.getElem_mem hq)
          rw [hXp] at hz1
          rw [hXq] at hz2
          have hz_n : z < G.n := Finset.mem_range.mp (iter_stepReach_subset_verts hG
            (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hu)) G.n hz1)
          have hz1' := compOf_eq_of_mem hG hu hz_n hz1
          have hz2' := compOf_eq_of_mem hG hv hz_n hz2
          have hpeq : rawComps[p]'hp = rawComps[q]'hq := by rw [hXp, hXq, ← hz1', hz2']
          exact absurd ((List.Nodup.getElem_inj_iff hnodup).mp hpeq) hpq.ne
        have hmem_deg : ∀ X ∈ rawComps, ∀ x ∈ X, ∃ e ∈ G.edges, e.1 = x ∨ e.2 = x := by
          intro X hX x hx
          obtain ⟨u, hu, hdeg_u, rfl⟩ := hX_prop X hX
          by_cases hxu : x = u
          · subst hxu
            have hdeg_pos : 0 < G.deg x := hdeg_u
            rw [deg_eq_filter_edges hG x] at hdeg_pos
            by_cases h1 : 0 < (G.edges.filter fun e => decide (e.1 = x)).length
            · obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp h1
              rw [List.mem_filter, decide_eq_true_eq] at he
              exact ⟨e, he.1, Or.inl he.2⟩
            · have h2 : 0 < (G.edges.filter fun e => decide (e.2 = x)).length := by omega
              obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp h2
              rw [List.mem_filter, decide_eq_true_eq] at he
              exact ⟨e, he.1, Or.inr he.2⟩
          · obtain ⟨P, hP⟩ := (mem_compOf_iff_walk hG hu).mp hx
            rcases hP with ⟨_, _, ⟨_, _, hux⟩ | ⟨hne, hlen, _, hlast, hedges, hstep⟩⟩
            · exact absurd hux.symm hxu
            · have hpos : 0 < P.edges.length := List.length_pos_of_ne_nil hne
              let j := P.edges.getD (P.edges.length - 1) 0
              have hj_lt : P.edges.length - 1 < P.edges.length := Nat.sub_lt hpos zero_lt_one
              have hj_mem : j ∈ P.edges := by
                dsimp only [j]
                rw [List.getD_eq_getElem _ _ hj_lt]
                exact List.getElem_mem hj_lt
              have hj_m : j < G.m := hedges j hj_mem
              have he_mem : G.edges.getD j (0, 0) ∈ G.edges := by
                rw [List.getD_eq_getElem _ _ hj_m]; exact List.getElem_mem hj_m
              have hmatch : Walk.EdgeMatches (G.edges.getD j (0, 0))
                  (P.verts.getD (P.edges.length - 1) 0)
                  (P.verts.getD (P.edges.length - 1 + 1) 0) :=
                hstep (P.edges.length - 1) hj_lt
              have hv_last : P.verts.getD (P.edges.length - 1 + 1) 0 = x := by
                have hl := List.getLast?_eq_getElem? (l := P.verts)
                rw [hlast, hlen, Nat.add_sub_cancel] at hl
                have heq : P.edges.length - 1 + 1 = P.edges.length := by omega
                rw [heq, List.getD_eq_getElem?_getD, ← hl]
                rfl
              rw [hv_last] at hmatch
              rcases hmatch with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact ⟨G.edges.getD j (0, 0), he_mem, Or.inr h2⟩
              · exact ⟨G.edges.getD j (0, 0), he_mem, Or.inl h2⟩
        refine ⟨hdisj, fun X hX => ?_, fun e he => ?_⟩
        · obtain ⟨u, hu, hdeg_u, rfl⟩ := hX_prop X hX
          have hsub : compOf G u ⊆ G.verts := iter_stepReach_subset_verts hG
            (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hu)) G.n
          have hclosed := compOf_edge_closed hG hu
          have hcard2 : 2 ≤ (compOf G u).card := by
            obtain ⟨e, he, hor⟩ := hmem_deg (compOf G u) hX u (mem_compOf_self u)
            have hne := hL e he
            have he1 : e.1 ∈ compOf G u := by
              rcases hor with rfl | rfl
              · exact mem_compOf_self _
              · exact (hclosed e he).mpr (mem_compOf_self _)
            have he2 : e.2 ∈ compOf G u := (hclosed e he).mp he1
            have hpair : {e.1, e.2} ⊆ compOf G u := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl <;> assumption
            have hpc : ({e.1, e.2} : Finset ℕ).card = 2 := Finset.card_pair hne
            exact hpc ▸ Finset.card_le_card hpair
          have hexp : G.IsConductanceExpanderOn (compOf G u) (1 / (2 * (G.m : ℝ) + 2)) := by
            intro S hS hneS hneqS
            have hcut := cut_pos_of_mem_compOf hG hu hS hneS hneqS
            have hvol_le : (G.volIn (compOf G u) S : ℝ) ≤ 2 * (G.m : ℝ) := by
              have h1 : G.volIn (compOf G u) S ≤ G.volIn (compOf G u) (compOf G u) :=
                volIn_subset_le hS
              have h2 : G.volIn (compOf G u) (compOf G u) = 2 * (G.inside (compOf G u)).length :=
                volIn_self_eq_two_mul_inside G (compOf G u)
              have h3 : (G.inside (compOf G u)).length ≤ G.m :=
                List.Sublist.length_le (List.filter_sublist)
              exact_mod_cast le_trans h1 (by rw [h2]; omega)
            have hmin_le : min (G.volIn (compOf G u) S : ℝ)
                (G.volIn (compOf G u) (compOf G u \ S) : ℝ) ≤ 2 * (G.m : ℝ) :=
              le_trans (min_le_left _ _) hvol_le
            have hmin_nn : 0 ≤ min (G.volIn (compOf G u) S : ℝ)
                (G.volIn (compOf G u) (compOf G u \ S) : ℝ) := by positivity
            have hφ_pos : (0 : ℝ) ≤ 1 / (2 * (G.m : ℝ) + 2) := by positivity
            calc (1 / (2 * (G.m : ℝ) + 2)) * min (G.volIn (compOf G u) S : ℝ)
                  (G.volIn (compOf G u) (compOf G u \ S) : ℝ)
                ≤ (1 / (2 * (G.m : ℝ) + 2)) * (2 * (G.m : ℝ)) :=
                  mul_le_mul_of_nonneg_left hmin_le hφ_pos
              _ ≤ 1 := by rw [one_div_mul_eq_div, div_le_one (by positivity)]; linarith
              _ ≤ (G.cutIn (compOf G u) S : ℝ) := by exact_mod_cast hcut
          have hdeg_ge : ∀ x ∈ compOf G u, 1 / (2 * (G.m : ℝ) + 2) * (2 ^ i₀ : ℝ) ≤
              (G.degIn (compOf G u) x : ℝ) := by
            intro x hx
            obtain ⟨e, he, hor⟩ := hmem_deg (compOf G u) hX x hx
            have hdeg_x_pos : 1 ≤ G.deg x := by
              rw [deg_eq_filter_edges hG x]
              rcases hor with rfl | rfl
              · have h1 : 0 < (G.edges.filter fun a => decide (a.1 = e.1)).length := by
                  rw [List.length_pos_iff_exists_mem]
                  exact ⟨e, List.mem_filter.mpr ⟨he, by simp⟩⟩
                omega
              · have h2 : 0 < (G.edges.filter fun a => decide (a.2 = e.2)).length := by
                  rw [List.length_pos_iff_exists_mem]
                  exact ⟨e, List.mem_filter.mpr ⟨he, by simp⟩⟩
                omega
            have hdegIn_eq : G.degIn (compOf G u) x = G.deg x :=
              degIn_eq_deg_of_closed hG hclosed hx
            have hpow_le : (2 ^ i₀ : ℕ) ≤ 2 * G.m + 2 := by
              have hlog := Nat.pow_log_le_self 2 (by omega : G.m + 1 ≠ 0)
              dsimp only [i₀]
              rw [pow_succ']
              omega
            have hpow_r : (2 ^ i₀ : ℝ) ≤ 2 * (G.m : ℝ) + 2 := by exact_mod_cast hpow_le
            have hprod_le : 1 / (2 * (G.m : ℝ) + 2) * (2 ^ i₀ : ℝ) ≤ 1 := by
              rw [one_div_mul_eq_div, div_le_one (by positivity)]
              exact hpow_r
            exact le_trans hprod_le (by exact_mod_cast (hdegIn_eq ▸ hdeg_x_pos))
          have hdeg_ge' : ∀ x ∈ compOf G u, 1 / (2 * (G.m : ℝ) + 2) * (2 ^ i : ℝ) ≤
              (G.degIn (compOf G u) x : ℝ) := by
            intro x hx; rw [hie]; exact hdeg_ge x hx
          exact ⟨hsub, hcard2, hexp, hdeg_ge', hclosed⟩
        · have he1_n : e.1 < G.n := (hG e he).1
          have hdeg_e1 : 1 ≤ G.deg e.1 := by
            rw [deg_eq_filter_edges hG e.1]
            have h1 : 0 < (G.edges.filter fun a => decide (a.1 = e.1)).length := by
              rw [List.length_pos_iff_exists_mem]
              exact ⟨e, List.mem_filter.mpr ⟨he, by simp⟩⟩
            omega
          refine ⟨compOf G e.1, ?_, mem_compOf_self e.1, ?_⟩
          · rw [List.mem_dedup, List.mem_filterMap]
            exact ⟨e.1, List.mem_range.mpr he1_n, by simp [hdeg_e1]⟩
          · exact (compOf_edge_closed hG he1_n e he).mp (mem_compOf_self e.1)

/-- Explicit global `DecomposeTool` witnessing that `DecomposeTool`'s axioms can hold for all
valid loopless graphs. -/
theorem exists_decomposeTool : Nonempty DecomposeTool := ⟨decompToolImpl⟩

/-- Explicit global `PathDSTool` witnessing that `PathDSTool`'s interface can be satisfied:
answers `GetPath` via shortest simple walks while `deleted = ∅` and sets `V̂ := V(G)` after any
edge deletion (`γ_del = 2 M + 1`). -/
private noncomputable def pdsToolImpl : PathDSTool := by
  classical
  let pickWalk : (Finset ℕ × Graph) → ℕ → ℕ → Walk := fun st u v =>
    if h : ∃ P : Walk, P.IsWalk st.2 u v ∧ P.verts.Nodup then Classical.choose h else Walk.empty
  refine ⟨Finset ℕ × Graph,
    fun φ_in _ => min φ_in (1 / 2),
    fun φ_in M => 1 / min φ_in (1 / 2) + 2 * (M : ℝ),
    fun φ_in M => 1 / min φ_in (1 / 2) + 2 * (M : ℝ),
    fun _ M => 2 * (M : ℝ) + 1,
    fun _ _ G => (∅, G),
    fun s => if s.1.Nonempty then s.2.verts else ∅,
    fun s => s.1,
    fun s e => ((insert e s.1, s.2), if s.1.Nonempty then ∅ else s.2.verts),
    pickWalk,
    fun _ _ G s => s.2 = G ∧ s.1 ⊆ Finset.range G.m,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ_in _ hφ; exact lt_min hφ (by norm_num)
  · intro _ _ _; exact min_le_left _ _
  · intro _ _ _; exact min_le_right _ _
  · intro φ_in M hφ
    have : 0 ≤ 2 * (M : ℝ) := by positivity
    linarith
  · intro _ _ _; exact le_rfl
  · intro _ M _
    have : 0 ≤ 2 * (M : ℝ) := by positivity
    linarith
  · intro _ _ G _ _ _ _ _ _ _; exact ⟨rfl, Finset.empty_subset _⟩
  · intro _ _ G _ _ _ _ _ _ _; simp
  · intro _ _ G _ _ _ _ _ _ _; rfl
  · intro φ_in M G s e hφ hle hG hm_pos hm_le hdeg hexp ⟨hsG, hs_sub⟩ he_m he_notdel
    dsimp only
    have hVhat_sub : (if s.1.Nonempty then s.2.verts else ∅) ⊆
        (if (insert e s.1).Nonempty then s.2.verts else ∅) := by
      simp only [Finset.insert_nonempty, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact Finset.empty_subset _
    have hVtop : (if (insert e s.1).Nonempty then s.2.verts else ∅) ⊆ G.verts := by
      simp [hsG]
    have hdiff : (if s.1.Nonempty then ∅ else s.2.verts) =
        (if (insert e s.1).Nonempty then s.2.verts else ∅) \
          (if s.1.Nonempty then s.2.verts else ∅) := by
      simp only [Finset.insert_nonempty, ↓reduceIte]
      by_cases hne : s.1.Nonempty
      · simp [hne]
      · simp [hne]
    have hvol_le : (G.vol (if (insert e s.1).Nonempty then s.2.verts else ∅) : ℝ) ≤
        (2 * (M : ℝ) + 1) * ((insert e s.1).card : ℝ) / min φ_in (1 / 2) := by
      simp only [Finset.insert_nonempty, ↓reduceIte, hsG, vol_verts_eq_two_mul_m hG]
      have hcard_ge : (1 : ℝ) ≤ ((insert e s.1).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (Finset.insert_nonempty _ _)
      have hφ_pos : 0 < min φ_in (1 / 2) := lt_min hφ (by norm_num)
      have hφ_half : min φ_in (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have h2m : ((2 * G.m : ℕ) : ℝ) ≤ 2 * (M : ℝ) + 1 := by
        exact_mod_cast (by omega : 2 * G.m ≤ 2 * M + 1)
      have h1 : ((2 * G.m : ℕ) : ℝ) ≤ (2 * (M : ℝ) + 1) * ((insert e s.1).card : ℝ) :=
        le_trans h2m (le_mul_of_one_le_right (by positivity) hcard_ge)
      have h2 : (2 * (M : ℝ) + 1) * ((insert e s.1).card : ℝ) ≤
          (2 * (M : ℝ) + 1) * ((insert e s.1).card : ℝ) / min φ_in (1 / 2) := by
        rw [le_div_iff₀ hφ_pos]
        exact mul_le_of_le_one_right (by positivity) (le_trans hφ_half (by norm_num))
      exact le_trans h1 h2
    refine ⟨⟨hsG, Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr he_m, hs_sub⟩⟩,
      rfl, hVhat_sub, hVtop, hdiff, hvol_le⟩
  · intro φ_in M G s u v hφ _ hG _ hm_le hdeg hexp ⟨hsG, _⟩ hu_V hv_V
    have hs_empty : s.1 = ∅ := by
      by_contra hne
      have hne' : s.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rw [Finset.mem_sdiff] at hu_V
      apply hu_V.2
      simp only [hne', ↓reduceIte, hsG]
      exact hu_V.1
    have hu_n : u < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hu_V).1
    have hv_n : v < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hv_V).1
    have hcomp_full : compOf G u = G.verts := by
      by_contra hneq
      have hsub : compOf G u ⊆ G.verts := iter_stepReach_subset_verts hG
        (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hu_n)) G.n
      have hne : (compOf G u).Nonempty := ⟨u, mem_compOf_self u⟩
      have hcut0 : G.cutIn G.verts (compOf G u) = 0 := by
        unfold Graph.cutIn
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro e he
        have he_G : e ∈ G.edges := inside_verts_eq_edges hG ▸ he
        have hcl := compOf_edge_closed hG hu_n e he_G
        simp [hcl]
      have hexp_cut := hexp (compOf G u) hsub hne hneq
      rw [hcut0, Nat.cast_zero] at hexp_cut
      have hv1 : 1 ≤ G.volIn G.verts (compOf G u) := by
        calc 1 ≤ G.deg u := hdeg u hu_n
          _ = G.degIn G.verts u := rfl
          _ ≤ ∑ x ∈ compOf G u, G.degIn G.verts x :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_compOf_self u)
      obtain ⟨w, hw_V, hwnC⟩ : ∃ w ∈ G.verts \ compOf G u, True := by
        by_contra hnone
        push Not at hnone
        have hsub2 : G.verts ⊆ compOf G u := fun w hw => by
          by_contra hnc; exact hnone w (Finset.mem_sdiff.mpr ⟨hw, hnc⟩)
        exact hneq (Finset.Subset.antisymm hsub hsub2)
      have hv2 : 1 ≤ G.volIn G.verts (G.verts \ compOf G u) := by
        have hw_n : w < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hw_V).1
        calc 1 ≤ G.deg w := hdeg w hw_n
          _ = G.degIn G.verts w := rfl
          _ ≤ ∑ x ∈ G.verts \ compOf G u, G.degIn G.verts x :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw_V
      have hmin_ge : (1 : ℝ) ≤ min (G.volIn G.verts (compOf G u) : ℝ)
          (G.volIn G.verts (G.verts \ compOf G u) : ℝ) :=
        le_min (by exact_mod_cast hv1) (by exact_mod_cast hv2)
      linarith [mul_le_mul_of_nonneg_left hmin_ge hφ.le]
    have hex_simple : ∃ P : Walk, P.IsWalk s.2 u v ∧ P.verts.Nodup := by
      rw [hsG]
      obtain ⟨P, hP⟩ := (mem_compOf_iff_walk hG hu_n).mp
        (by rw [hcomp_full]; exact Finset.mem_range.mpr hv_n)
      exact exists_simple_walk_of_walk hP
    dsimp only [pickWalk]
    simp only [hex_simple, ↓reduceDIte]
    set P := Classical.choose hex_simple
    have hP_spec : P.IsWalk s.2 u v ∧ P.verts.Nodup := Classical.choose_spec hex_simple
    have hP_walk : P.IsWalk G u v := hsG ▸ hP_spec.1
    have hlen_le_n : P.edges.length ≤ G.n := walk_nodup_length_le hG hP_walk hP_spec.2
    have hn_le_2m : G.n ≤ 2 * G.m := by
      calc G.n = ∑ _v ∈ Finset.range G.n, 1 := by simp
        _ ≤ ∑ v ∈ Finset.range G.n, G.deg v :=
            Finset.sum_le_sum fun v hv => hdeg v (Finset.mem_range.mp hv)
        _ = G.vol G.verts := rfl
        _ = 2 * G.m := vol_verts_eq_two_mul_m hG
    have hlen_real : (P.edges.length : ℝ) ≤ 1 / min φ_in (1 / 2) + 2 * (M : ℝ) := by
      have hnat : P.edges.length ≤ 2 * M := le_trans hlen_le_n (le_trans hn_le_2m (by omega))
      have hpos : 0 < 1 / min φ_in (1 / 2) := div_pos one_pos (lt_min hφ (by norm_num))
      have hle_2M : (P.edges.length : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hnat
      linarith
    refine ⟨hP_walk, hP_spec.2, fun e _ => by simp [hs_empty], fun x _ => by simp [hs_empty], hlen_real⟩

/-- Explicit global `PathDSTool` witnessing that `PathDSTool`'s interface can be satisfied:
answers `GetPath` via shortest simple walks while `deleted = ∅` and sets `V̂ := V(G)` after any
edge deletion (`γ_del = 2 M + 1`). -/
theorem exists_pathDSTool : Nonempty PathDSTool := ⟨pdsToolImpl⟩

private noncomputable def decompMonotoneImpl : DecomposeMonotone decompToolImpl := by
  refine ⟨fun m => 1 / (2 * (m : ℝ) + 2), ?_, ?_, ?_, ?_⟩
  · intro m; positivity
  · intro m
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  · intro m₁ m₂ hm
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  · intro G _ _; exact le_rfl

/-- Explicit `DecomposeMonotone` instance for `decompToolImpl` (`φ_lb m = 1 / (2 · m + 2)`). -/
theorem exists_decomposeMonotone : ∃ (dec : DecomposeTool), Nonempty (DecomposeMonotone dec) :=
  ⟨decompToolImpl, ⟨decompMonotoneImpl⟩⟩

private theorem pdsMonotoneImpl : PathDSMonotone pdsToolImpl := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ₁ φ₂ _ _ _ hφ12 _ _
    exact min_le_min hφ12 le_rfl
  · intro φ₁ φ₂ M₁ M₂ hφ1 hφ12 _ hM
    have hdiv : 1 / min φ₂ (1 / 2) ≤ 1 / min φ₁ (1 / 2) :=
      one_div_le_one_div_of_le (lt_min hφ1 (by norm_num)) (min_le_min hφ12 le_rfl)
    have hM' : (M₁ : ℝ) ≤ (M₂ : ℝ) := Nat.cast_le.mpr hM
    dsimp only [pdsToolImpl]
    linarith
  · intro φ₁ φ₂ M₁ M₂ hφ1 hφ12 _ hM
    have hdiv : 1 / min φ₂ (1 / 2) ≤ 1 / min φ₁ (1 / 2) :=
      one_div_le_one_div_of_le (lt_min hφ1 (by norm_num)) (min_le_min hφ12 le_rfl)
    have hM' : (M₁ : ℝ) ≤ (M₂ : ℝ) := Nat.cast_le.mpr hM
    dsimp only [pdsToolImpl]
    linarith
  · intro _ _ M₁ M₂ _ _ _ hM
    have hM' : (M₁ : ℝ) ≤ (M₂ : ℝ) := Nat.cast_le.mpr hM
    dsimp only [pdsToolImpl]
    linarith

/-- Explicit `PathDSMonotone` instance for `pdsToolImpl`. -/
theorem exists_pathDSMonotone : ∃ (pds : PathDSTool), Nonempty (PathDSMonotone pds) :=
  ⟨pdsToolImpl, ⟨pdsMonotoneImpl⟩⟩

/-- Concrete `SpannerToolCosts` witness with unit leading constants (`K = 1`, `decFactor = 1`). -/
def unitSpannerToolCosts : SpannerToolCosts :=
  { constructExpander := ⟨1, zero_le_one⟩
    decompose := ⟨1, fun _ => 1, zero_le_one, fun _ => le_rfl, fun _ _ _ => le_rfl⟩
    pathDS := ⟨1, 1, zero_le_one, zero_le_one⟩ }

/-- Non-vacuity witness for `SpannerToolCosts`. -/
theorem exists_spannerToolCosts : Nonempty SpannerToolCosts := ⟨unitSpannerToolCosts⟩

/-! ## Section 3: Non-Vacuity for `theorem_8_1_local` and Concrete Triangle Example -/

/-- Package all three non-axiomatic tool constructions into a `LocalSpannerTools N_max W_max`. -/
theorem exists_localSpannerTools (N_max : ℕ) (W_max : ℝ) :
    Nonempty (LocalSpannerTools N_max W_max) := by
  obtain ⟨c⟩ := exists_boundedConstructExpanderTool N_max W_max
  obtain ⟨d⟩ := exists_decomposeTool
  obtain ⟨p⟩ := exists_pathDSTool
  exact ⟨⟨c, d, p⟩⟩

/-- **Non-vacuity of Theorem 8.1**: for EVERY valid `(H', J, embJH)` with `embJH : J → H'`,
there exist concrete `LocalSpannerTools N_max W_max` (without any external cited hypotheses)
satisfying all preconditions and conclusions of `theorem_8_1_local`. -/
theorem theorem_8_1_nonvacuous (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH) :
    ∃ (tools : LocalSpannerTools J.n (2 * (J.m : ℝ) * (2 * (J.m : ℝ) + 2))),
      let out := sparsifyLocal tools H' J embJH
      out.keptEdges.Nodup ∧
      (∀ j ∈ out.keptEdges, j < J.m) ∧
      out.Jtilde.IsValid ∧
      IsEmbedding J out.Jtilde out.embJJtilde ∧
      IsEmbedding out.Jtilde H' (restrictEmb embJH out.keptEdges) ∧
      vcong J H' (fun _ => 1) (compose out.Jtilde (restrictEmb embJH out.keptEdges) out.embJJtilde) ≤
        (((eta1Bound out.wd J : ℝ) + 1 / 2) * ((eta2Bound J : ℝ) + 1 / 2)) *
          out.wd.τ₁ * out.wd.τ₂ := by
  classical
  let dec := decompToolImpl
  let pds := Classical.choice exists_pathDSTool
  let ce := Classical.choice
    (exists_boundedConstructExpanderTool J.n (2 * (J.m : ℝ) * (2 * (J.m : ℝ) + 2)))
  let tools : LocalSpannerTools J.n (2 * (J.m : ℝ) * (2 * (J.m : ℝ) + 2)) := ⟨ce, dec, pds⟩
  have hWmax : 2 * (J.m : ℝ) / dec.φ_dec (stripLoops J) ≤
      2 * (J.m : ℝ) * (2 * (J.m : ℝ) + 2) := by
    change 2 * (J.m : ℝ) / (1 / (2 * ((stripLoops J).m : ℝ) + 2)) ≤ _
    rw [one_div, div_inv_eq_mul]
    have hm_le : ((stripLoops J).m : ℝ) ≤ (J.m : ℝ) := by exact_mod_cast stripLoops_m_le J
    have hnn : 0 ≤ 2 * (J.m : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hnn
  have ht := theorem_8_1_local tools H' J embJH hJ hembJH le_rfl hWmax
  exact ⟨tools, ht.1, ht.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
    ht.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Concrete 3-vertex triangle graph `K_3` used to verify non-vacuity on an explicit instance. -/
def triangleGraph : Graph := ⟨3, [(0, 1), (1, 2), (2, 0)]⟩

theorem triangleGraph_isValid : triangleGraph.IsValid := by
  intro e he
  dsimp only [triangleGraph] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

/-- Explicit identity embedding `triangleGraph → triangleGraph`. -/
def triangleIdEmb (j : ℕ) : Walk :=
  let e := triangleGraph.edges.getD j (0, 0)
  Walk.single e.1 e.2 j

theorem isEmbedding_triangleIdEmb :
    IsEmbedding triangleGraph triangleGraph triangleIdEmb := by
  refine ⟨le_rfl, fun j hj => ?_⟩
  dsimp only [triangleIdEmb]
  have he_mem : triangleGraph.edges[j]'hj ∈ triangleGraph.edges := List.getElem_mem hj
  have hval := triangleGraph_isValid _ he_mem
  simp only [List.getD_eq_getElem triangleGraph.edges (0, 0) hj]
  refine Walk.isWalk_single hval.1 hval.2 hj ?_
  rw [List.getD_eq_getElem triangleGraph.edges (0, 0) hj]
  exact Or.inl ⟨rfl, rfl⟩

/-- Concrete runnable instantiation of `theorem_8_1_nonvacuous` on `triangleGraph`. -/
theorem triangleGraph_example :
    ∃ (tools : LocalSpannerTools triangleGraph.n
        (2 * (triangleGraph.m : ℝ) * (2 * (triangleGraph.m : ℝ) + 2))),
      let out := sparsifyLocal tools triangleGraph triangleGraph triangleIdEmb
      out.Jtilde.IsValid ∧ IsEmbedding triangleGraph out.Jtilde out.embJJtilde := by
  obtain ⟨tools, _, _, hval, hemb, _⟩ :=
    theorem_8_1_nonvacuous triangleGraph triangleGraph triangleIdEmb
      triangleGraph_isValid isEmbedding_triangleIdEmb
  exact ⟨tools, hval, hemb⟩

/-! ## Section 4: Non-Vacuity for `sparsifyMG_spec` and `MGraph` Triangle Example -/

/-- For any expander constructor `ce : ConstructExpanderTool` and edge-count cap `mMax`, the concrete
constructions `decompToolImpl`, `pdsToolImpl`, and `unitSpannerToolCosts` satisfy all hypotheses and
conclusions of both `sparsifyMG_spec` and `sparsifyMG_spec_of_dec_le`. -/
theorem exists_sparsifyMG_witness (ce : ConstructExpanderTool) (mMax : ℕ) :
    ∃ (tools : SpannerTools) (costs : SpannerToolCosts)
      (hdec : DecomposeMonotone tools.decompose) (_ : PathDSMonotone tools.pathDS),
      DynSpanner.SparsifySpec mMax
        (sparsifyMGParams tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax)
        (sparsifyMG tools costs) ∧
      costs.decompose.decFactor mMax ≤
        1 * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
          tools.pathDS (hdec.φ_lb mMax) mMax) ^ 2 ∧
      DynSpanner.SparsifySpec mMax
        (sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax 1 zero_le_one)
        (sparsifyMG tools costs) := by
  let tools : SpannerTools := ⟨ce, decompToolImpl, pdsToolImpl⟩
  have hγq : ∀ φ M, 0 < φ → tools.pathDS.γ_query φ M = tools.pathDS.γ_ExpPath φ M :=
    fun _ _ _ => rfl
  have hγ_ge4 : 4 ≤ capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
      tools.pathDS (decompMonotoneImpl.φ_lb mMax) mMax :=
    four_le_capGammaL tools.constructExpander.hφ_pos (decompMonotoneImpl.hφ_lb_pos mMax) mMax
  have hdec_le : unitSpannerToolCosts.decompose.decFactor mMax ≤
      1 * (capGammaL tools.constructExpander.c_deg tools.constructExpander.φ_Const
        tools.pathDS (decompMonotoneImpl.φ_lb mMax) mMax) ^ 2 := by
    change (1 : ℝ) ≤ _
    nlinarith only [hγ_ge4]
  exact ⟨tools, unitSpannerToolCosts, decompMonotoneImpl, pdsMonotoneImpl,
    sparsifyMG_spec tools unitSpannerToolCosts decompMonotoneImpl pdsMonotoneImpl mMax hγq,
    hdec_le,
    sparsifyMG_spec_of_dec_le tools unitSpannerToolCosts decompMonotoneImpl pdsMonotoneImpl mMax
      zero_le_one hdec_le hγq⟩

/-- Concrete 3-vertex triangle `MGraph` (`0 → 1 → 2 → 0`). -/
def triangleMGraph : MGraph :=
  { V := {0, 1, 2}
    E := {0, 1, 2}
    tail := id
    head := fun e => (e + 1) % 3 }

theorem triangleMGraph_isValid : triangleMGraph.IsValid := by
  intro e he
  simp only [triangleMGraph, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with rfl | rfl | rfl <;> decide

/-- Identity single-edge embedding `triangleMGraph → triangleMGraph`. -/
def triangleMIdEmb : MinCostFlow.Embedding :=
  fun e => [(e, true)]

theorem isEmbedding_triangleMIdEmb :
    triangleMIdEmb.IsEmbedding triangleMGraph triangleMGraph := by
  refine ⟨Finset.Subset.rfl, fun e he => ?_⟩
  exact .cons he (by simp [MGraph.src, triangleMGraph]) (by simp [MGraph.dst, triangleMGraph]; exact .nil _)

theorem triangleMIdEmb_len_ge_one :
    triangleMGraph.E.Nonempty → 1 ≤ triangleMIdEmb.length triangleMGraph := by
  intro _
  exact le_trans (by decide : 1 ≤ (triangleMIdEmb 0).length)
    (Finset.le_sup (f := fun e => (triangleMIdEmb e).length) (by decide : 0 ∈ triangleMGraph.E))

/-- Unconditional concrete `MGraph` triangle instantiation via `theorem_8_1_local` +
`MGraphTranslate` / `MGraphSpec` (without external axioms or `ConstructExpanderTool` hypothesis). -/
theorem triangleMGraph_local_example :
    let cH := toCitedH triangleMGraph triangleMGraph triangleMIdEmb
    let cJ := toCitedJ triangleMGraph
    let cEmb := embToCited triangleMGraph triangleMGraph triangleMIdEmb
    ∃ (tools : LocalSpannerTools cJ.n (2 * (cJ.m : ℝ) * (2 * (cJ.m : ℝ) + 2))),
      let cOut := sparsifyLocal tools cH cJ cEmb
      triangleMGraph.IsSubgraph (outJtilde triangleMGraph cOut.keptEdges) ∧
      (citedEmbToMGraph triangleMGraph cOut.Jtilde cOut.keptEdges cOut.embJJtilde).IsEmbedding
        triangleMGraph (outJtilde triangleMGraph cOut.keptEdges) := by
  intro cH cJ cEmb
  have hcJ_valid : cJ.IsValid := toCitedJ_isValid triangleMGraph_isValid
  have hcEmb : IsEmbedding cJ cH cEmb := embToCited_isEmbedding triangleMGraph_isValid isEmbedding_triangleMIdEmb
  let ce := Classical.choice
    (exists_boundedConstructExpanderTool cJ.n (2 * (cJ.m : ℝ) * (2 * (cJ.m : ℝ) + 2)))
  let tools : LocalSpannerTools cJ.n (2 * (cJ.m : ℝ) * (2 * (cJ.m : ℝ) + 2)) :=
    ⟨ce, decompToolImpl, pdsToolImpl⟩
  have hWmax : 2 * (cJ.m : ℝ) / tools.decompose.φ_dec (stripLoops cJ) ≤
      2 * (cJ.m : ℝ) * (2 * (cJ.m : ℝ) + 2) := by
    change 2 * (cJ.m : ℝ) / (1 / (2 * ((stripLoops cJ).m : ℝ) + 2)) ≤ _
    rw [one_div, div_inv_eq_mul]
    have hm_le : ((stripLoops cJ).m : ℝ) ≤ (cJ.m : ℝ) := by exact_mod_cast stripLoops_m_le cJ
    have hnn : 0 ≤ 2 * (cJ.m : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hnn
  have ht := theorem_8_1_local tools cH cJ cEmb hcJ_valid hcEmb le_rfl hWmax
  rcases ht with ⟨_, hkept_lt, hcOut_n, _, _, _, _, _, hembJJ, _⟩
  let cOut := sparsifyLocal tools cH cJ cEmb
  have hkept : ∀ k ∈ cOut.keptEdges, k < triangleMGraph.m :=
    fun k hk => (toCitedJ_m triangleMGraph) ▸ hkept_lt k hk
  have hcOut_n' : cOut.Jtilde.n = triangleMGraph.n :=
    hcOut_n.trans (by dsimp only [cJ, toCitedJ]; exact vertsOf_length triangleMGraph.V)
  have hcOut_edges : cOut.Jtilde.edges =
      cOut.keptEdges.map fun k => (toCitedJ triangleMGraph).edges.getD k (0, 0) := by
    dsimp only [cOut, sparsifyLocal]
  exact ⟨tools, outJtilde_isSubgraph triangleMGraph cOut.keptEdges hkept,
    citedEmbToMGraph_isEmbedding triangleMGraph_isValid hkept hcOut_n' hcOut_edges hembJJ⟩

/-- Concrete `triangleMGraph` instantiation of `DynSpanner.SparsifySpec` via `sparsifyMG`. -/
theorem triangleMGraph_sparsifyMG_example (ce : ConstructExpanderTool) :
    ∃ (tools : SpannerTools) (costs : SpannerToolCosts)
      (hdec : DecomposeMonotone tools.decompose) (_ : PathDSMonotone tools.pathDS),
      let P := sparsifyMGParams tools costs (hdec.φ_lb 3) (hdec.hφ_lb_pos 3) 3
      let out := sparsifyMG tools costs triangleMGraph triangleMGraph triangleMIdEmb
      triangleMGraph.IsSubgraph out.Jtilde ∧
      out.emb.IsEmbedding triangleMGraph out.Jtilde ∧
      (out.cost : ℝ) ≤
        P.K_t * ((triangleMGraph.n : ℝ) +
          (triangleMGraph.m : ℝ) * P.γ_ℓ ^ 2 * (triangleMIdEmb.length triangleMGraph : ℝ)) *
          (1 + Real.log ((triangleMGraph.n : ℝ) + (triangleMGraph.m : ℝ) + 2)) ^ P.p_t := by
  obtain ⟨tools, costs, hdec, hpds, hspec, _, _⟩ := exists_sparsifyMG_witness ce 3
  have hm3 : triangleMGraph.m ≤ 3 := by decide
  have hs := hspec triangleMGraph triangleMGraph triangleMIdEmb
    triangleMGraph_isValid triangleMGraph_isValid hm3 triangleMIdEmb_len_ge_one isEmbedding_triangleMIdEmb
  exact ⟨tools, costs, hdec, hpds, hs.1, hs.2.1, hs.2.2.2.2.2⟩

end MinCostFlow.Spanner
