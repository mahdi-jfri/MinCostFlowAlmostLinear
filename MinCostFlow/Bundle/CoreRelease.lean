module

public import MinCostFlow.Bundle.CoreBatch
public import MinCostFlow.DynSpanner.Walks

/-!
# Ordered release of a forest edge

A released edge first leaves the forest. Contracting the two new
components gives the split of the old core vertex. The released edge then
enters the core in its new position.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

/-- The root set of a refinement with one additional root is an insertion. -/
theorem roots_insert_of_card {R R' : Finset ℕ} (h : R ⊆ R')
    (hc : R'.card = R.card + 1) : ∃ r, r ∉ R ∧ R' = insert r R := by
  have hd := Finset.card_sdiff_of_subset h
  rw [hc, Nat.add_sub_cancel_left] at hd
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hd
  have hr' := Finset.mem_sdiff.mp (hr.symm ▸ Finset.mem_singleton_self r)
  refine ⟨r, hr'.2, ?_⟩
  ext t
  simp only [Finset.mem_insert]
  constructor
  · intro ht
    by_cases hm : t ∈ R
    · exact Or.inr hm
    · exact Or.inl (Finset.mem_singleton.mp (hr ▸ Finset.mem_sdiff.mpr ⟨ht, hm⟩))
  · rintro (rfl | ht)
    · exact hr'.1
    · exact h ht

private theorem roots_cut_pair {G H : MGraph} {L L' : LSF} {e fresh : ℕ}
    (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf H)
    (hV : H.V = G.V) (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) :
    ∃ x : End, x.1 = e ∧
      L'.F.F.Connected (L.F.F.src x) (L.F.root (L.F.F.tail e)) ∧
      L'.F.F.Connected (L.F.F.dst x) fresh := by
  let F := L.F.F
  let a := F.tail e
  let b := F.head e
  let r := L.F.root a
  have hev := hF.1.1 e he
  rw [hF.2.1] at hev
  have ha : a ∈ G.V := hev.1
  have hb : b ∈ G.V := hev.2
  have hsub : F.IsSubgraph L'.F.F := by rw [hCut]; exact eraseForestEdge_subgraph _ _
  have hRoot (y : ℕ) (hy : y ∈ G.V) (heq : L.F.root y = r) :
      L'.F.root y = r ∨ L'.F.root y = fresh := by
    obtain ⟨hm, hc⟩ := root_mem_R hF' (hV.symm ▸ hy)
    rw [hRoots] at hm
    rcases Finset.mem_insert.mp hm with hu | hu
    · exact Or.inr hu
    · have hh := root_eq_of_connected hF hy (hF.2.2.1 hu) (connected_of_subgraph hsub hc)
      rw [heq, root_eq_of_mem_R hF hu] at hh
      exact Or.inl hh.symm
  have hab : F.Connected a b := connected_of_edge he
  have hne : L'.F.root a ≠ L'.F.root b := by
    intro hh
    have hc := connected_of_root_eq hF' (hV.symm ▸ ha) (hV.symm ▸ hb) hh
    rw [hCut] at hc
    exact not_connected_eraseForestEdge hF.1 (x := (e, true)) he hc
  rcases hRoot a ha rfl with h₁ | h₁ <;>
    rcases hRoot b hb (root_eq_of_connected hF ha hb hab).symm with h₂ | h₂
  · exact (hne (h₁.trans h₂.symm)).elim
  · refine ⟨(e, true), rfl, ?_, ?_⟩
    · change L'.F.F.Connected a r
      exact h₁ ▸ (root_mem_R hF' (hV.symm ▸ ha)).2
    · change L'.F.F.Connected b fresh
      exact h₂ ▸ (root_mem_R hF' (hV.symm ▸ hb)).2
  · refine ⟨(e, false), rfl, ?_, ?_⟩
    · change L'.F.F.Connected b r
      exact h₂ ▸ (root_mem_R hF' (hV.symm ▸ hb)).2
    · change L'.F.F.Connected a fresh
      exact h₁ ▸ (root_mem_R hF' (hV.symm ▸ ha)).2
  · exact (hne (h₁.trans h₂.symm)).elim

private theorem delete_subgraph (G : MGraph) (e : ℕ) : G.IsSubgraph (G.applyUpdate (.delete e)) :=
  ⟨Finset.Subset.rfl, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem restrict_deleted_order {G : MGraph} (ρ : Rotation G) (e w : ℕ) :
    (ρ.restrict (delete_subgraph G e)).order w = (ρ.order w).filter (fun x => x.1 != e) := by
  apply List.filter_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  simp only [MGraph.applyUpdate, decide_eq_true_eq, Finset.mem_erase, bne_iff_ne]
  exact ⟨And.left, fun h => ⟨h, ((ρ.mem_order _ _).mp hx).1⟩⟩

/-- Deleting an input forest edge is a single ordered core split. -/
theorem orderedCore_delete_forest {G : MGraph} {L L' : LSF} {e fresh β : ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.delete e)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.delete e)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)))
    (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hs : RotationStep β (.delete e) ρ σ) (hβ : 2 ≤ β) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 := by
  obtain ⟨⟨f, side⟩, hf', hk, hm⟩ := roots_cut_pair hF hF' rfl he hCut hRoots
  change f = e at hf'
  subst f
  have hr := (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
  obtain ⟨hu, hg, hstep⟩ := coreRotation_cut ρ σ hG hH hF hF' he hCut hRoots hr hf hk hm hs hβ
  exact ⟨_, OrderedCoreBatch.singleton hu hg hstep, rfl, rfl⟩

/-- Releasing one forest edge produces an ordered core split followed by
an insertion. -/
theorem orderedCore_release {G : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    {L L' : LSF} (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf G)
    {e fresh β : ℕ} (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R) (hβ : 2 ≤ β) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 := by
  let H := G.applyUpdate (.delete e)
  let σ := ρ.restrict (delete_subgraph G e)
  have hH := graphEq_isValid (graphEq_refl H) (by
    intro f hf
    exact hG f (Finset.mem_of_mem_erase hf))
  have heF' : e ∉ L'.F.F.E := by rw [hCut]; exact Finset.notMem_erase _ _
  have hFH : L'.F.IsRootedSpanningForestOf H := by
    refine ⟨hF'.1, hF'.2.1, hF'.2.2.1, hF'.2.2.2.1, hF'.2.2.2.2.1, ?_, ?_⟩
    · intro f hh
      exact Finset.mem_erase.mpr ⟨fun heq => heF' (heq ▸ hh), hF'.2.2.2.2.2.1 hh⟩
    · exact hF'.2.2.2.2.2.2
  obtain ⟨x, hx, hk, hm⟩ := roots_cut_pair hF hF' rfl he hCut hRoots
  have hDel : RotationStep β (.delete x.1) ρ (show Rotation (G.applyUpdate (.delete x.1)) from
      hx.symm ▸ σ) := by
    have h (f : ℕ) (hf : f = e) :
        RotationStep β (.delete f) ρ (hf.symm ▸ σ) := by
      subst f
      intro w
      rw [restrict_deleted_order]
    exact h _ hx
  have hr := (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
  have hCutStep : ∃ u : Update, OrderedCoreBatch β (coreRotation ρ hG hF)
      (coreRotation σ hH hFH) [u] ∧ isSplit u := by
    obtain ⟨a, side⟩ := x
    change a = e at hx
    subst a
    obtain ⟨hu, hg, hs⟩ := coreRotation_cut ρ σ hG hH hF hFH he hCut hRoots hr hf hk hm hDel hβ
    exact ⟨_, OrderedCoreBatch.singleton hu hg hs, rfl⟩
  let ins := Update.insert e (L'.F.root (G.tail e)) (L'.F.root (G.head e))
  let C := coreGraph H L'
  let C' := coreGraph G L'
  have heAbsent : e ∉ C.E := fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
  have heG := hF.2.2.2.2.2.1 he
  have hEnds := hG e heG
  have hiV : C.UpdateIsValid ins :=
    ⟨heAbsent, (root_mem_R hF' hEnds.1).1, (root_mem_R hF' hEnds.2).1⟩
  have hEq : GraphEq C' (C.applyUpdate ins) := by
    refine ⟨rfl, ?_, ?_⟩
    · change G.E \ L'.F.F.E = insert e (G.E.erase e \ L'.F.F.E)
      ext f
      by_cases h : f = e
      · subst f; simp [heG, heF']
      · simp [h]
    · intro f _
      change L'.F.root (G.tail f) = Function.update (fun f => L'.F.root (G.tail f)) e
        (L'.F.root (G.tail e)) f ∧ L'.F.root (G.head f) =
        Function.update (fun f => L'.F.root (G.head f)) e (L'.F.root (G.head e)) f
      by_cases hf : f = e
      · subst f; simp
      · simp [Function.update_of_ne hf]
  have hIns : RotationStep β ins (coreRotation σ hH hFH) ((coreRotation ρ hG hF').congrGraph hEq) := by
    intro w
    have hOrd (z : ℕ) : ((ρ.order z).filter fun x => x.1 != e).IsRotated
        ((σ.order z).filter fun x => x.1 != e) := by
      have heH : e ∉ H.E := Finset.notMem_erase _ _
      rw [filter_avoid_edge σ heH, restrict_deleted_order]
    have hh := core_filter_open ρ σ hG hH hF' hFH heF' hOrd w
    rw [filter_avoid_edge (coreRotation σ hH hFH) heAbsent] at hh
    exact hh
  obtain ⟨u, hU, hu⟩ := hCutStep
  refine ⟨[u] ++ [ins], hU.append (OrderedCoreBatch.singleton hiV hEq hIns), ?_, ?_⟩
  · have ht : isSplit ins = false := rfl
    simp [batchSplitCount, hu, ht]
  · have htag : deleteTag u = false := by
      cases u <;> simp_all [deleteTag, isSplit]
    have hiTag : deleteTag ins = false := rfl
    simp [htag, hiTag]

end MinCostFlow.Bundle
