module

public import MinCostFlow.ExpanderDecomp.RouteDFS
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Static blocking of short paths (`ShortPathBlock`)

Given disjoint terminal sets `S, T ⊆ X`, active vertex set `V ⊆ X`, and length bound `d`,
`shortPathBlock` repeatedly runs layered BFS (`RouteBFS.lean`) and the iterative cursor-based
DFS blocking pass (`RouteDFS.lean`), isolating accepted path vertices until no `S`-to-`T` walk
of length at most `d` remains.

Because each nonterminal phase destroys all shortest paths of length `j` and raises the minimum
distance strictly, at most `d + 1` phases run, costing at most
`7 * (|X| + (G.inside X).length + 1) * (d + 1)` steps (`shortPathBlock_spec`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Output of `shortPathBlock`. -/
structure ShortPathResult where
  /-- Pairwise vertex-disjoint simple paths of length `≤ d` from `S` to `T`. -/
  paths : List ((ℕ × ℕ) × List ℕ)
  /-- Remaining unisolated vertices `V \ routedVerts G paths`. -/
  remVerts : Finset ℕ
  /-- Exact operation count of `shortPathBlock`. -/
  cost : ℕ

/-- Repeated blocking phases (at most `remPhases` phases). -/
def shortPathBlockLoop (adj : ℕ → List (ℕ × ℕ)) (S T : Finset ℕ) (d : ℕ) :
    ℕ → Finset ℕ → List ((ℕ × ℕ) × List ℕ) → ℕ → ShortPathResult
  | 0, V, acc, cost =>
    { paths := acc, remVerts := V, cost := cost }
  | rem + 1, V, acc, cost =>
    let bfs := bfsLayers adj V S d T
    let cost1 := cost + bfs.cost + 1
    if bfs.hitStop then
      let dfs := dfsBlock adj V S T bfs.dist bfs.maxReached
      shortPathBlockLoop adj S T d rem (V \ dfs.used) (dfs.paths ++ acc) (cost1 + dfs.cost)
    else
      { paths := acc, remVerts := V, cost := cost1 }

/-- `ShortPathBlock`: finds a maximal blocking family of vertex-disjoint simple
paths of length at most `d` between `S` and `T` in `G[V]`, isolating their vertices. -/
def shortPathBlock (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (d : ℕ) : ShortPathResult :=
  shortPathBlockLoop adj S T d (d + 1) V [] 0

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited


/-! ### Layered-walk elimination lemma -/

/-- No layered walk from `dead` to `T ∩ V` avoids `used`. -/
private lemma no_layered_walk_from_dead {G : Graph} {X V T : Finset ℕ} (hVX : V ⊆ X)
    {dist : ℕ → Option ℕ} {j : ℕ} {used dead : Finset ℕ}
    (hdc : DeadClosed G X V T dist j used dead)
    {u t : ℕ} {es : List ℕ} {r : ℕ}
    (hw : IsEdgeWalkIn G (V \ used) u t es)
    (hu_dead : u ∈ dead) (ht : t ∈ T)
    (hlayer : ∀ k ≤ es.length, dist ((walkVerts G.edges u es).getD k 0) = some (r + k))
    (hr_len : r + es.length = j) :
    False := by
  rcases hw with ⟨hw, hin⟩
  induction hw generalizing r with
  | nil u =>
    exact (hdc u hu_dead).1 ht
  | @cons u' x' v' e' es' hj_lt hend hrest ih =>
    have hin0 : insideB (V \ used) (edgeAt G.edges e') = true := hin e' List.mem_cons_self
    unfold insideB at hin0
    simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff] at hin0
    have hinX : insideB X (edgeAt G.edges e') = true := by
      unfold insideB
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hVX hin0.1.1, hVX hin0.2.1⟩
    have hadj : (x', e') ∈ adjOf G X u' :=
      (mem_adjOf_iff G X u' x' e').mpr ⟨hj_lt, hinX, hend⟩
    have hx_sdiff : x' ∈ V \ used := by
      rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Finset.mem_sdiff.mpr (h2 ▸ hin0.2)
      · exact Finset.mem_sdiff.mpr (h1 ▸ hin0.1)
    have hdu : dist u' = some r := by
      have h0 := hlayer 0 (Nat.zero_le _)
      simpa [walkVerts] using h0
    have hdx : dist x' = some (r + 1) := by
      have h1 := hlayer 1 (by simp)
      simp only [walkVerts, walkStep_of_hend hend, List.getD_cons_succ] at h1
      have hw0 : (walkVerts G.edges x' es').getD 0 0 = x' := by cases es' <;> rfl
      rwa [hw0] at h1
    have hr_lt : r < j := by simp at hr_len; omega
    have hx_in : x' ∈ used ∪ dead :=
      (hdc u' hu_dead).2 (x', e') hadj (Finset.mem_sdiff.mp hx_sdiff).1 r hr_lt hdu hdx
    have hx_dead : x' ∈ dead := by
      rcases Finset.mem_union.mp hx_in with hxU | hxD
      · exact absurd hxU (Finset.mem_sdiff.mp hx_sdiff).2
      · exact hxD
    have hlayer' : ∀ k ≤ es'.length, dist ((walkVerts G.edges x' es').getD k 0) = some ((r + 1) + k) := by
      intro k hk
      have hk' := hlayer (k + 1) (by simp; omega)
      simp only [walkVerts, walkStep_of_hend hend, List.getD_cons_succ] at hk'
      rw [hk']
      congr 1
      omega
    exact ih (r := r + 1) hx_dead ht hlayer' (by simp at hr_len; omega)
      (fun i hi => hin i (List.mem_cons_of_mem _ hi))

/-- After one BFS + DFS blocking pass at distance `j`, no `S`-to-`T` walk of length `≤ j`
remains in `G[V \ dfs.used]`. -/
private lemma dfsBlock_raises_dist (G : Graph) {X V S T : Finset ℕ} (hVX : V ⊆ X)
    (d : ℕ) (hhit : (bfsLayers (adjOf G X) V S d T).hitStop = true) :
    let bfs := bfsLayers (adjOf G X) V S d T
    let dfs := dfsBlock (adjOf G X) V S T bfs.dist bfs.maxReached
    DFSInv G X V S T bfs.dist bfs.maxReached dfs ∧
    dfs.cost ≤ 4 * X.card + 2 * (G.inside X).length ∧
    (∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn G (V \ dfs.used) s t es →
      s ∈ V \ dfs.used → t ∈ V \ dfs.used → bfs.maxReached < es.length) := by
  set bfs := bfsLayers (adjOf G X) V S d T with hbfs_def
  have hbfs := bfsLayers_spec G hVX S d T
  rcases hbfs with ⟨_, _, _, _, _, _, hdist_zero, hdist_walk, _, _, _, hhit_spec, _, _⟩
  obtain ⟨_, _, hno_early_T⟩ := hhit_spec hhit
  set init : DFSState := { used := ∅, dead := ∅, cursor := adjOf G X, paths := [], cost := 0 }
  have hinv0 : DFSInv G X V S T bfs.dist bfs.maxReached init :=
    { used_sub := Finset.empty_subset _
      dead_sub := Finset.empty_subset _
      dead_closed := fun _ h => absurd h (Finset.notMem_empty _)
      cursor_inv := fun _ _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
      used_eq := rfl
      paths_valid := fun _ h => absurd h List.not_mem_nil
      paths_disj := List.Pairwise.nil }
  have hsources_sub : ∀ s ∈ (S ∩ V).sort (· ≤ ·), s ∈ S ∩ V :=
    fun s hs => (Finset.mem_sort _).mp hs
  have hres := dfsSources_spec G X V S T bfs.dist bfs.maxReached (dfsPot V init + 1)
    hdist_zero hno_early_T ((S ∩ V).sort (· ≤ ·)) hsources_sub init (Nat.lt_succ_self _) hinv0
  set dfs := dfsBlock (adjOf G X) V S T bfs.dist bfs.maxReached
  rcases hres with ⟨hinv_end, _, _, hall_src, hcost⟩
  change dfs.cost + dfsPot V dfs + 2 * (V.card - dfs.used.card) ≤ _ at hcost
  refine ⟨hinv_end, ?_, ?_⟩
  · have hlen_src : ((S ∩ V).sort (· ≤ ·)).length ≤ V.card := by
      rw [Finset.length_sort]; exact Finset.card_le_card Finset.inter_subset_right
    have hpot0 : dfsPot V init = (∑ v ∈ V, (adjOf G X v).length) + V.card := by
      simp [dfsPot, init]
    have hsum_le : ∑ v ∈ V, (adjOf G X v).length ≤ 2 * (G.inside X).length :=
      sum_adjOf_length_le G hVX
    have hV_le : V.card ≤ X.card := Finset.card_le_card hVX
    have hinit_cost : init.cost = 0 := rfl
    have hinit_card : init.used.card = 0 := rfl
    rw [hpot0, hinit_cost, hinit_card] at hcost
    change dfs.cost ≤ 4 * X.card + 2 * (G.inside X).length
    omega
  · intro s hs t ht es hw hsV' htV'
    by_contra hle
    push Not at hle
    have hsV : s ∈ V := (Finset.mem_sdiff.mp hsV').1
    have htV : t ∈ V := (Finset.mem_sdiff.mp htV').1
    have hwV : IsEdgeWalkIn G V s t es := hw.mono Finset.sdiff_subset
    have hge : bfs.maxReached ≤ es.length := bfsLayers_min_dist_of_hitStop_true G hVX S d T hhit
      (Finset.mem_inter.mpr ⟨hs, hsV⟩) (Finset.mem_inter.mpr ⟨ht, htV⟩) hwV
    have hlen_eq : es.length = bfs.maxReached := le_antisymm hle hge
    -- Every vertex at position `k` on `es` has `bfs.dist = some k`!
    have hlayer : ∀ k ≤ es.length, bfs.dist ((walkVerts G.edges s es).getD k 0) = some (0 + k) := by
      intro k hk
      simp only [Nat.zero_add]
      obtain ⟨x, hx_eq, hpre, hsuf⟩ := hwV.split_at hk
      rw [hx_eq]
      have hpre_len : (es.take k).length = k := List.length_take_of_le hk
      have hsuf_len : (es.drop k).length = es.length - k := List.length_drop
      have hdist_le : ∃ r ≤ (es.take k).length, bfs.dist x = some r :=
        (bfsLayers_dist_le_of_walk G hVX S d T (Finset.mem_inter.mpr ⟨hs, hsV⟩) hpre).1
          (by rw [← hbfs_def]; omega)
      obtain ⟨rk, hrk_le, hdx⟩ := hdist_le
      have hrk_eq : rk = k := by
        by_contra hne
        have hrk_lt : rk < k := lt_of_le_of_ne (by omega) hne
        obtain ⟨s', hs', es_short, hlen_short, hw_short⟩ := hdist_walk x rk hdx
        have hcomb : IsEdgeWalkIn G V s' t (es_short ++ es.drop k) := hw_short.append hsuf
        have hge' : bfs.maxReached ≤ (es_short ++ es.drop k).length :=
          bfsLayers_min_dist_of_hitStop_true G hVX S d T hhit hs'
            (Finset.mem_inter.mpr ⟨ht, htV⟩) hcomb
        simp only [List.length_append, hlen_short, hsuf_len] at hge'
        omega
      exact hrk_eq ▸ hdx
    have hs_in : s ∈ dfs.used ∪ dfs.dead :=
      hall_src s ((Finset.mem_sort _).mpr (Finset.mem_inter.mpr ⟨hs, hsV⟩))
    have hs_dead : s ∈ dfs.dead := by
      rcases Finset.mem_union.mp hs_in with hsU | hsD
      · exact absurd hsU (Finset.mem_sdiff.mp hsV').2
      · exact hsD
    exact no_layered_walk_from_dead hVX hinv_end.dead_closed hw hs_dead ht hlayer (by omega)

/-! ### Main loop and `shortPathBlock_spec` -/

private lemma shortPathBlockLoop_spec (G : Graph) {X : Finset ℕ} (S T : Finset ℕ) (d : ℕ)
    (_hdisj : Disjoint S T)
    (rem : ℕ) (V : Finset ℕ) (hVX : V ⊆ X)
    (acc : List ((ℕ × ℕ) × List ℕ)) (cost : ℕ) (minDist : ℕ)
    (hmin_pos : 1 ≤ minDist)
    (hrem : d + 1 ≤ rem + minDist)
    (hno_lt : ∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn G V s t es →
      s ∈ V → t ∈ V → minDist ≤ es.length)
    (hacc_valid : ∀ p ∈ acc,
      p.1.1 ∈ S ∩ X ∧ p.1.2 ∈ T ∩ X ∧ p.2.length ≤ d ∧ IsSimpleWalkIn G X p.1.1 p.1.2 p.2)
    (hacc_disj : acc.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset)
    (hacc_out : Disjoint (routedVerts G acc) V) :
    let res := shortPathBlockLoop (adjOf G X) S T d rem V acc cost
    res.remVerts ⊆ V ∧
    (∃ newPaths, res.paths = newPaths ++ acc ∧
      res.remVerts = V \ routedVerts G newPaths ∧
      routedVerts G newPaths ⊆ V) ∧
    (∀ p ∈ res.paths,
      p.1.1 ∈ S ∩ X ∧ p.1.2 ∈ T ∩ X ∧ p.2.length ≤ d ∧ IsSimpleWalkIn G X p.1.1 p.1.2 p.2) ∧
    (res.paths.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) ∧
    (∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn G res.remVerts s t es →
      s ∈ res.remVerts → t ∈ res.remVerts → d < es.length) ∧
    res.cost ≤ cost + rem * (7 * X.card + 4 * (G.inside X).length + 3) := by
  induction rem generalizing V acc cost minDist with
  | zero =>
    simp only [shortPathBlockLoop, Nat.zero_mul, Nat.add_zero]
    refine ⟨Finset.Subset.refl _, ⟨[], rfl, by simp [routedVerts], by simp [routedVerts]⟩,
      hacc_valid, hacc_disj, ?_, le_refl _⟩
    intro s hs t ht es hw hsV htV
    have hge := hno_lt s hs t ht es hw hsV htV
    omega
  | succ rem ih =>
    simp only [shortPathBlockLoop]
    set bfs := bfsLayers (adjOf G X) V S d T with hbfs_def
    have hbfs := bfsLayers_spec G hVX S d T
    rcases hbfs with ⟨_, hmax_le, _, _, _, _, _, hdist_walk, _, _, _, hhit_spec, _, hbfs_cost⟩
    change bfs.maxReached ≤ d at hmax_le
    change bfs.cost ≤ 3 * X.card + 2 * (G.inside X).length + 2 at hbfs_cost
    by_cases hhit : bfs.hitStop = true
    · simp only [hhit, ↓reduceIte]
      have hblock := dfsBlock_raises_dist G hVX d hhit
      set dfs := dfsBlock (adjOf G X) V S T bfs.dist bfs.maxReached with hdfs_def
      rcases hblock with ⟨hinv_dfs, hdfs_cost, hraised⟩
      change dfs.cost ≤ 4 * X.card + 2 * (G.inside X).length at hdfs_cost
      -- Show `minDist ≤ bfs.maxReached`
      obtain ⟨_, ⟨t0, ht0, hdt0⟩, _⟩ := hhit_spec hhit
      obtain ⟨s0, hs0, es0, hlen0, hw0⟩ := hdist_walk t0 bfs.maxReached hdt0
      have hmin_le : minDist ≤ bfs.maxReached := by
        rw [← hlen0]
        exact hno_lt s0 (Finset.mem_inter.mp hs0).1 t0 (Finset.mem_inter.mp ht0).1 es0 hw0
          (Finset.mem_inter.mp hs0).2 (Finset.mem_inter.mp ht0).2
      have hV'_sub : V \ dfs.used ⊆ X := le_trans Finset.sdiff_subset hVX
      have hacc'_valid : ∀ p ∈ dfs.paths ++ acc,
          p.1.1 ∈ S ∩ X ∧ p.1.2 ∈ T ∩ X ∧ p.2.length ≤ d ∧ IsSimpleWalkIn G X p.1.1 p.1.2 p.2 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨hpS, hpT, hpLen, hpW, hpNd⟩ := hinv_dfs.paths_valid p hp
          exact ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpS).1, hVX (Finset.mem_inter.mp hpS).2⟩,
            Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpT).1, hVX (Finset.mem_inter.mp hpT).2⟩,
            hpLen ▸ hmax_le, hpW.mono hVX, hpNd⟩
        · exact hacc_valid p hp
      have hacc'_disj : (dfs.paths ++ acc).Pairwise fun p q =>
          Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset := by
        rw [List.pairwise_append]
        refine ⟨hinv_dfs.paths_disj, hacc_disj, fun p hp q hq => ?_⟩
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        have hvUsed : v ∈ dfs.used := by
          rw [hinv_dfs.used_eq, mem_routedVerts_iff]
          exact ⟨p, hp, List.mem_toFinset.mp hv1⟩
        have hvAcc : v ∈ routedVerts G acc :=
          (mem_routedVerts_iff G acc v).mpr ⟨q, hq, List.mem_toFinset.mp hv2⟩
        exact Finset.disjoint_left.mp hacc_out hvAcc (hinv_dfs.used_sub hvUsed)
      have hacc'_out : Disjoint (routedVerts G (dfs.paths ++ acc)) (V \ dfs.used) := by
        rw [routedVerts_append, ← hinv_dfs.used_eq, Finset.disjoint_union_left]
        exact ⟨disjoint_sdiff_self_right, Disjoint.mono_right Finset.sdiff_subset hacc_out⟩
      have hrec := ih (V \ dfs.used) hV'_sub (dfs.paths ++ acc) (cost + bfs.cost + 1 + dfs.cost)
        (bfs.maxReached + 1) (by omega) (by omega)
        (fun s hs t ht es hw hsV' htV' => hraised s hs t ht es hw hsV' htV')
        hacc'_valid hacc'_disj hacc'_out
      rcases hrec with ⟨hrem_sub, ⟨np, hnp_eq, hnp_rem, hnp_sub⟩, hval, hdisj_end, hno_short, hcost_end⟩
      have hnew_eq : (np ++ dfs.paths) ++ acc = np ++ (dfs.paths ++ acc) := List.append_assoc _ _ _
      have hrem_eq : V \ routedVerts G (np ++ dfs.paths) = (V \ dfs.used) \ routedVerts G np := by
        rw [routedVerts_append, ← hinv_dfs.used_eq]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
      refine ⟨le_trans hrem_sub Finset.sdiff_subset, ?_, hval, hdisj_end, hno_short, ?_⟩
      · refine ⟨np ++ dfs.paths, by rw [hnp_eq, hnew_eq], by rw [hrem_eq, hnp_rem], ?_⟩
        rw [routedVerts_append, ← hinv_dfs.used_eq]
        exact Finset.union_subset (le_trans hnp_sub Finset.sdiff_subset) hinv_dfs.used_sub
      · have hmul : (rem + 1) * (7 * X.card + 4 * (G.inside X).length + 3) =
            rem * (7 * X.card + 4 * (G.inside X).length + 3) +
              (7 * X.card + 4 * (G.inside X).length + 3) := by ring
        omega
    · simp only [hhit, Bool.false_eq_true, ↓reduceIte]
      have hmul : (rem + 1) * (7 * X.card + 4 * (G.inside X).length + 3) =
          rem * (7 * X.card + 4 * (G.inside X).length + 3) +
            (7 * X.card + 4 * (G.inside X).length + 3) := by ring
      refine ⟨Finset.Subset.refl _, ⟨[], rfl, by simp [routedVerts], by simp [routedVerts]⟩,
        hacc_valid, hacc_disj, ?_, by omega⟩
      intro s hs t ht es hw hsV htV
      exact bfsLayers_no_short_walk_of_hitStop_false G hVX S d T (Bool.eq_false_iff.mpr hhit)
        (Finset.mem_inter.mpr ⟨hs, hsV⟩) (Finset.mem_inter.mpr ⟨ht, htV⟩) hw

/-- **`ShortPathBlock` specification.**
Given disjoint terminal sets `S, T` and active vertices `V ⊆ X`, `shortPathBlock` returns
pairwise vertex-disjoint simple walks in `G[V]` of length `≤ d` from `S` to `T`, isolates all
vertices on those walks (`remVerts = V \ routedVerts G paths`), leaves no `S`-to-`T` walk of
length `≤ d` in `G[remVerts]`, and runs in at most
`7 * (|X| + (G.inside X).length + 1) * (d + 1)` steps. -/
theorem shortPathBlock_spec (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S T : Finset ℕ) (hdisj : Disjoint S T) (d : ℕ) :
    let res := shortPathBlock (adjOf G X) V S T d
    res.remVerts ⊆ V ∧
    res.remVerts = V \ routedVerts G res.paths ∧
    routedVerts G res.paths ⊆ V ∧
    (∀ p ∈ res.paths,
      p.1.1 ∈ S ∩ V ∧ p.1.2 ∈ T ∩ V ∧ p.2.length ≤ d ∧ IsSimpleWalkIn G V p.1.1 p.1.2 p.2) ∧
    (res.paths.Pairwise fun p q =>
      Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset) ∧
    (∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn G res.remVerts s t es →
      s ∈ res.remVerts → t ∈ res.remVerts → d < es.length) ∧
    res.cost ≤ 7 * (X.card + (G.inside X).length + 1) * (d + 1) := by
  have hno1 : ∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn G V s t es → s ∈ V → t ∈ V → 1 ≤ es.length := by
    intro s hs t ht es hw _ _
    cases es with
    | nil =>
      cases hw.1
      exact absurd hs (Finset.disjoint_right.mp hdisj ht)
    | cons _ _ => simp
  have hloop := shortPathBlockLoop_spec G S T d hdisj (d + 1) V hVX [] 0 1 (le_refl _) (by omega)
    hno1 (by simp) List.Pairwise.nil (by simp [routedVerts])
  rcases hloop with ⟨h1, ⟨np, hnp_eq, hnp_rem, hnp_sub⟩, hval, hdisj_end, hno_short, hcost⟩
  simp only [List.append_nil] at hnp_eq
  rw [← hnp_eq] at hnp_rem hnp_sub
  refine ⟨h1, hnp_rem, hnp_sub, ?_, hdisj_end, hno_short, ?_⟩
  · intro p hp
    obtain ⟨hpS, hpT, hpLen, hpW, hpNd⟩ := hval p hp
    have hverts_subV : ∀ w ∈ walkVerts G.edges p.1.1 p.2, w ∈ V :=
      fun w hw => hnp_sub ((mem_routedVerts_iff G _ w).mpr ⟨p, hp, hw⟩)
    have hp1V : p.1.1 ∈ V := hverts_subV p.1.1 (mem_walkVerts_start _ _ _)
    have hp2V : p.1.2 ∈ V := hverts_subV p.1.2 hpW.1.mem_walkVerts_end
    have hpWV : IsEdgeWalkIn G V p.1.1 p.1.2 p.2 := by
      refine ⟨hpW.1, fun i hi => ?_⟩
      obtain ⟨he1, he2⟩ := hpW.1.edge_endpoints_mem_walkVerts hi
      unfold insideB
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hverts_subV _ he1, hverts_subV _ he2⟩
    exact ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpS).1, hp1V⟩,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpT).1, hp2V⟩, hpLen, hpWV, hpNd⟩
  · have hbound : 7 * X.card + 4 * (G.inside X).length + 3 ≤
        7 * (X.card + (G.inside X).length + 1) := by omega
    have hmul : (d + 1) * (7 * X.card + 4 * (G.inside X).length + 3) ≤
        (d + 1) * (7 * (X.card + (G.inside X).length + 1)) :=
      Nat.mul_le_mul_left (d + 1) hbound
    calc
      (shortPathBlock (adjOf G X) V S T d).cost
          ≤ 0 + (d + 1) * (7 * X.card + 4 * (G.inside X).length + 3) := hcost
      _ = (d + 1) * (7 * X.card + 4 * (G.inside X).length + 3) := Nat.zero_add _
      _ ≤ (d + 1) * (7 * (X.card + (G.inside X).length + 1)) := hmul
      _ = 7 * (X.card + (G.inside X).length + 1) * (d + 1) := by ring

end MinCostFlow.ExpanderDecomp
