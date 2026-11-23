module

public import MinCostFlow.HierPaths.BuildProgLevelSpec
import MinCostFlow.HierPaths.BuildHierValid
import MinCostFlow.HierPaths.BuildHierAux
import MinCostFlow.HierPaths.BuildChildHost

/-!
# The output model of one parent

The child graph edges and their walks share one list order. Shift the
graph endpoints to the parent terminal numbers and keep the walks in
that order. Each increasing pair of children contributes the connectors
from its fully routed matching.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Assemble the level model from the list of walks of each local child host. -/
def levelDataOfFamily (route : RouterFn) (G : Graph) (start s k Δ L : ℕ)
    (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : BuildLevelData where
  host c := ⟨G.n,shiftEdges (start+c*s) ((F c).map Prod.fst)⟩
  emb c e := ((F c).getD e ((0,0),[])).2
  conn c c' := if c < c' then
    (siblingConns route G (buildLevelVerts start s k) Δ L (buildLevelChild start s) c c').map
      (fun en => (en.1.1,en.1.2,en.2)) else []

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- A parent's consecutive child intervals form legitimate router groups. -/
theorem buildLevel_isChildren {start s k : ℕ} (hs : 1 ≤ s) :
    IsChildren (buildLevelVerts start s k) (buildLevelChild start s) k s := by
  refine ⟨hs,fun c hc => ⟨?_,by simp [buildLevelChild,card_shiftSet]⟩,?_⟩
  · intro v hv
    obtain ⟨hLo,hHi⟩ := mem_shiftSet_iff.mp hv
    have hNext : (c+1)*s ≤ k*s := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at hNext
    have hV := Finset.mem_range.mp hHi
    exact Finset.mem_Ico.mpr ⟨(Nat.le_add_right ..).trans hLo,by omega⟩
  · intro c _ c' _ hne
    apply Finset.disjoint_left.mpr
    intro v hvc hvc'
    obtain ⟨ha,hua⟩ := mem_shiftSet_iff.mp hvc
    obtain ⟨hb,hub⟩ := mem_shiftSet_iff.mp hvc'
    have hVa := Finset.mem_range.mp hua
    have hVb := Finset.mem_range.mp hub
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : (c+1)*s ≤ c'*s := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at hsep
      omega
    · have hsep : (c'+1)*s ≤ c*s := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at hsep
      omega

private theorem level_count_family (F : List ((ℕ × ℕ) × List ℕ)) (e : ℕ) :
    ∑ j ∈ Finset.range F.length, (((F.getD j ((0,0),[])).2).count e) =
      occLoad (walkFamily F) e := by
  unfold occLoad walkFamily
  rw [List.map_map, sum_map_eq_sum_range_getD _ _ ((0,0),[])]
  rfl

/-- A family of local child hosts with the final-game guarantees gives
the level contract's complete mathematical output. -/
theorem levelDataOfFamily_good {route : RouterFn} {routeCost : RouterCostFn} {G : Graph}
    {start s k M r Δ L L' bh : ℕ} {β : ℝ} {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hRouter : IsMatchingPlayer route routeCost) (hPos : 0 < β)
    (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hH : HostPre G (buildLevelVerts start s k) Δ L) (hs : 1 ≤ s)
    (hBh : max 2 (2/β) ≤ (bh : ℝ))
    (hF : ∀ c < k,
      let J : Graph := ⟨s,(F c).map Prod.fst⟩
      J.IsValid ∧ J.IsLoopless ∧ (∀ u, J.deg u ≤ buildLevelDegree L') ∧
      (s=1 → F c = []) ∧
      (1<s → J.IsExpansionExpanderOn (Finset.range s) (1/(2*(PParam ParamConfig.default M r:ℝ)))) ∧
      ∀ en ∈ F c, EntryOK G (buildLevelVerts start s k) (start+c*s) (routePathLen Δ bh L) en)
    (hLoad : ∀ e < G.m, ∑ c ∈ Finset.range k, occLoad (walkFamily (F c)) e ≤
      buildLevelDegree L' * routeCong Δ bh L) :
    (levelDataOfFamily route G start s k Δ L F).Good G start s k M r Δ L L' bh := by
  let D := levelDataOfFamily route G start s k Δ L F
  let X := buildLevelVerts start s k
  let ch := buildLevelChild start s
  have hch := buildLevel_isChildren (start := start) (k := k) hs
  have hm (c : ℕ) : (D.host c).m = (F c).length := by simp [D,levelDataOfFamily,Graph.m,shiftEdges]
  have hEnds (c : ℕ) (hc : c < k) (e : ℕ × ℕ) (he : e ∈ (D.host c).edges) :
      e.1 ∈ ch c ∧ e.2 ∈ ch c := by
    change e ∈ shiftEdges (start+c*s) ((F c).map Prod.fst) at he
    obtain ⟨loc,hLocal,rfl⟩ := List.mem_map.mp he
    obtain ⟨h1,h2⟩ := (hF c hc).1 loc hLocal
    exact ⟨mem_shiftSet.mpr (Finset.mem_range.mpr h1),mem_shiftSet.mpr (Finset.mem_range.mpr h2)⟩
  have hEntries (c : ℕ) (hc : c < k) (e : ℕ) (he : e < (D.host c).m) :
      IsEdgeWalk G.edges (edgeAt (D.host c).edges e).1 (edgeAt (D.host c).edges e).2 (D.emb c e) ∧
        (∀ i ∈ D.emb c e, insideB X (edgeAt G.edges i) = true) ∧
        (D.emb c e).length ≤ routePathLen Δ bh L := by
    have he' : e < (F c).length := hm c ▸ he
    have he'' : e < ((F c).map Prod.fst).length := by simpa using he'
    have hef : edgeAt ((F c).map Prod.fst) e = (F c)[e].1 := by
      unfold edgeAt
      rw [List.getD_eq_getElem _ _ he'',List.getElem_map]
    change _ ∧ _ ∧ (D.emb c e).length ≤ _
    have hh := (hF c hc).2.2.2.2.2 _ (List.getElem_mem he')
    change _ ∧ _ ∧ _ at hh
    simpa only [D,levelDataOfFamily,edgeAt_shiftEdges he'',hef,List.getD_eq_getElem _ _ he'] using hh
  refine ⟨?_,fun c hc e he _ => ⟨(hEntries c hc e he).1,(hEntries c hc e he).2.1⟩,
    fun c hc e he => (hEntries c hc e he).2.2,?_,?_,?_,?_,?_⟩
  · intro c hc
    obtain ⟨hValid,hLoop,hDeg,hSingle,hExpansion,_⟩ := hF c hc
    have hSub : ch c ⊆ Finset.range G.n := (hch.2.1 c hc).1.trans hH.1
    have hValid' : (D.host c).IsValid := fun e he => by
      obtain ⟨ha,hb⟩ := hEnds c hc e he
      exact ⟨Finset.mem_range.mp (hSub ha),Finset.mem_range.mp (hSub hb)⟩
    refine ⟨rfl,hValid',?_,hEnds c hc,?_,?_,?_⟩
    · intro e he
      change e ∈ shiftEdges (start+c*s) ((F c).map Prod.fst) at he
      obtain ⟨loc,hLocal,rfl⟩ := List.mem_map.mp he
      exact fun heq => hLoop loc hLocal (Nat.add_left_cancel heq)
    · intro v hv
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
      let J : Graph := ⟨s,(F c).map Prod.fst⟩
      have hAll : (D.host c).inside (D.host c).verts = (D.host c).edges := by
        apply List.filter_eq_self.mpr
        intro e he
        obtain ⟨ha,hb⟩ := hValid' e he
        simp [Graph.verts,ha,hb]
      have hInside : (D.host c).inside (ch c) = (D.host c).edges := by
        apply List.filter_eq_self.mpr
        intro e he
        obtain ⟨ha,hb⟩ := hEnds c hc e he
        simp [ha,hb]
      have hEq : (D.host c).deg ((start+c*s)+u) = (D.host c).degIn (ch c) ((start+c*s)+u) := by
        simp only [Graph.deg,Graph.degIn,hAll,hInside]
      rw [hEq]
      change (Graph.mk G.n (shiftEdges (start+c*s) (F c |>.map Prod.fst))).degIn
        (shiftSet (start+c*s) (Finset.range s)) _ ≤ _
      rw [degIn_shift _ s]
      exact hDeg u
    · intro h
      simp [levelDataOfFamily,shiftEdges,hSingle h]
    · intro h
      exact isExpansionExpanderOn_shift (hExpansion h)
  · intro e he
    change (∑ c ∈ Finset.range k, ∑ j ∈ Finset.range (D.host c).m, (D.emb c j).count e) ≤ _
    have hh (c : ℕ) : (∑ j ∈ Finset.range (D.host c).m, (D.emb c j).count e) =
        occLoad (walkFamily (F c)) e := by
      rw [hm]
      exact level_count_family _ _
    simpa only [hh] using hLoad e he
  · intro c _ c' _ hle
    simp [levelDataOfFamily,not_lt_of_ge hle]
  · intro c hc c' hc' hlt
    obtain ⟨_,h1,h2,h3,h4⟩ := siblingConns_perfect hRouter hH hch hPos hExp hBh hc hc' hlt.ne
    simpa only [D,levelDataOfFamily,hlt,ite_true,List.map_map,Function.comp_def] using And.intro h1 (And.intro h2 (And.intro h3 h4))
  · intro c hc c' hc' hlt en hen
    simp only [levelDataOfFamily,hlt,ite_true] at hen
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hen
    have hw := siblingConns_walk hRouter hH hch hPos hExp hBh hc hc' hlt.ne v hv
    exact ⟨hw.1,hw.2.2⟩
  · intro c hc c' hc' hlt e he
    have hl := occLoad_siblingConns_le_cong hRouter hH hch hPos hExp hBh hc hc' hlt.ne he
    simpa only [D,levelDataOfFamily,hlt,ite_true,occLoad,List.map_map,Function.comp_def] using hl

end MinCostFlow.HierPaths
