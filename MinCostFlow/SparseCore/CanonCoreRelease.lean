module

public import MinCostFlow.SparseCore.CanonCoreDefs
public import MinCostFlow.Bundle.CoreReleases
public import MinCostFlow.DynSpanner.Walks

/-!
# The canonical roots meet the refinement conditions, and releases are ordered

The proof that a batch of the LSF changes the core by an ordered batch names the components of
each intermediate forest by final roots (`exists_roots_refinement`). This file shows that the
canonical choice `canonRoots` (an old root where there is one, and otherwise the least final
root) meets the same conditions (`canonRoots_spec`). The argument is the one of
`exists_roots_refinement`, with the least root in place of a chosen one.

Then it proves that releasing forest edges in a given order changes the core by the explicit
batch `releasesBatch`: for each edge one core split, which moves the ends of the new tree part
to its new root, followed by the insertion of the released edge (`orderedCore_releasesBatch`).
The proof is that of `orderedCore_release` and `orderedCore_releases`, with the batch written
out instead of shown to exist.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- The canonical roots of an intermediate forest keep the old roots, are final roots, and root
the forest. The hypotheses are those of `exists_roots_refinement`. -/
theorem canonRoots_spec {G F : MGraph} {final : RootedForest} {old : Finset ℕ}
    (hF : F.IsForest) (hV : F.V = G.V) (hFG : G.IsSubgraph F)
    (hfinal : final.IsRootedSpanningForestOf G) (hsub : F.IsSubgraph final.F)
    (hOld : old ⊆ final.R)
    (hSep : ∀ r ∈ old, ∀ s ∈ old, F.Connected r s → r = s) :
    old ⊆ canonRoots F old final.R ∧ canonRoots F old final.R ⊆ final.R ∧
      (RootedForest.mk F (canonRoots F old final.R)).IsRootedSpanningForestOf G := by
  have hAvail : ∀ A ∈ components F, (A ∩ final.R).Nonempty := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
    have hvG : v ∈ G.V := hV ▸ hv
    obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 v hvG
    have hrF : r ∈ F.V := hV.symm ▸ hfinal.2.2.1 hr
    exact ⟨r, Finset.mem_inter.mpr
      ⟨mem_compOf_iff.mpr ⟨hrF, connected_of_subgraph hsub hc⟩, hr⟩⟩
  let pick := canonPick old final.R
  have hPick (A : Finset ℕ) (hA : A ∈ components F) : pick A ∈ A ∧ pick A ∈ final.R := by
    by_cases h : (A ∩ old).Nonempty
    · have hm := Finset.mem_inter.mp (Finset.min'_mem _ h)
      have hp : pick A = (A ∩ old).min' h := by simp only [pick, canonPick, h, ↓reduceDIte]
      rw [hp]
      exact ⟨hm.1, hOld hm.2⟩
    · have ha := hAvail A hA
      have hm := Finset.mem_inter.mp (Finset.min'_mem _ ha)
      have hp : pick A = (A ∩ final.R).min' ha := by
        simp only [pick, canonPick, h, ha, ↓reduceDIte]
      rw [hp]
      exact hm
  let R := (components F).image pick
  have hR : R ⊆ final.R := by
    intro r hr
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hr
    exact (hPick A hA).2
  refine ⟨?_, hR, hF, hV, fun _ hr => hfinal.2.2.1 (hR hr), ?_, hFG⟩
  · intro r hr
    have hrF : r ∈ F.V := hV.symm ▸ hfinal.2.2.1 (hOld hr)
    let A := compOf F r
    have ha : (A ∩ old).Nonempty := ⟨r, Finset.mem_inter.mpr ⟨self_mem_compOf hrF, hr⟩⟩
    have hc := Finset.mem_inter.mp (Finset.min'_mem _ ha)
    have hp : pick A = r := by
      have hconn := (mem_compOf_iff.mp hc.1).2
      have he := hSep _ hc.2 r hr (connected_symm hconn)
      simpa only [pick, canonPick, ha, ↓reduceDIte] using he
    exact hp ▸ Finset.mem_image_of_mem pick (compOf_mem_components hrF)
  · intro v hv
    have hvF : v ∈ F.V := hV.symm ▸ hv
    let A := compOf F v
    have ha : A ∈ components F := compOf_mem_components hvF
    exact ⟨pick A, ⟨Finset.mem_image_of_mem pick ha, (mem_compOf_iff.mp (hPick A ha).1).2⟩,
      fun w hw => by
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hw.1
        obtain ⟨u, huV, rfl⟩ := Finset.mem_image.mp hT
        have hu := (mem_compOf_iff.mp (hPick (compOf F u) (compOf_mem_components huV)).1).2
        exact congrArg pick (compOf_eq_of_connected (connected_trans hu (connected_symm hw.2)))⟩

/-- When a refinement adds one root `r`, `newRoot` is `r`. -/
theorem newRoot_eq {R old : Finset ℕ} {r : ℕ} (h : R = insert r old) (hr : r ∉ old) :
    newRoot R old = r := by
  have hs : R \ old = {r} := by
    rw [h]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h₁ | h₁, h₂⟩
      · exact h₁
      · exact absurd h₁ h₂
    · rintro rfl
      exact ⟨Or.inl rfl, hr⟩
  simp [newRoot, hs]

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

private theorem delete_subgraph (G : MGraph) (e : ℕ) :
    G.IsSubgraph (G.applyUpdate (.delete e)) :=
  ⟨Finset.Subset.rfl, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem restrict_deleted_order {G : MGraph} (ρ : Rotation G) (e w : ℕ) :
    (ρ.restrict (delete_subgraph G e)).order w = (ρ.order w).filter (fun x => x.1 != e) := by
  apply List.filter_congr
  intro x hx
  apply Bool.eq_iff_iff.mpr
  simp only [MGraph.applyUpdate, decide_eq_true_eq, Finset.mem_erase, bne_iff_ne]
  exact ⟨And.left, fun h => ⟨h, ((ρ.mem_order _ _).mp hx).1⟩⟩

/-- Deleting an input forest edge is the core split `refineSplit`.
This is `orderedCore_delete_forest` with the batch written out. -/
theorem orderedCore_delete_forest_canon {G : MGraph} {L L' : LSF} {e fresh β : ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.delete e)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.delete e)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)))
    (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hs : RotationStep β (.delete e) ρ σ) (hβ : 2 ≤ β) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF')
      [refineSplit (coreGraph G L) (coreGraph (G.applyUpdate (.delete e)) L')
        (L.F.root (L.F.F.tail e)) fresh] := by
  obtain ⟨⟨f, side⟩, hf', hk, hm⟩ := roots_cut_pair hF hF' rfl he hCut hRoots
  change f = e at hf'
  subst f
  have hr := (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
  obtain ⟨hu, hg, hstep⟩ := coreRotation_cut ρ σ hG hH hF hF' he hCut hRoots hr hf hk hm hs hβ
  exact OrderedCoreBatch.singleton hu hg hstep

/-- Releasing one forest edge is a core split followed by the insertion of the edge. This is
`orderedCore_release` with the batch written out. -/
theorem orderedCore_release_canon {G : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    {L L' : LSF} (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf G)
    {e fresh β : ℕ} (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R) (hβ : 2 ≤ β) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF')
      [refineSplit (coreGraph G L) (coreGraph (G.applyUpdate (.delete e)) L')
          (L.F.root (L.F.F.tail e)) fresh,
        .insert e (L'.F.root (G.tail e)) (L'.F.root (G.head e))] := by
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
  have hDel : RotationStep β (.delete e) ρ σ := by
    intro w
    rw [restrict_deleted_order]
  have hU := orderedCore_delete_forest_canon ρ σ hG hH hF hFH he hCut hRoots hf hDel hβ
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
  have hIns : RotationStep β ins (coreRotation σ hH hFH)
      ((coreRotation ρ hG hF').congrGraph hEq) := by
    intro w
    have hOrd (z : ℕ) : ((ρ.order z).filter fun x => x.1 != e).IsRotated
        ((σ.order z).filter fun x => x.1 != e) := by
      have heH : e ∉ H.E := Finset.notMem_erase _ _
      rw [filter_avoid_edge σ heH, restrict_deleted_order]
    have hh := core_filter_open ρ σ hG hH hF' hFH heF' hOrd w
    rw [filter_avoid_edge (coreRotation σ hH hFH) heAbsent] at hh
    exact hh
  exact hU.append (OrderedCoreBatch.singleton hiV hEq hIns)

private theorem ordered_core_nil {G : MGraph} {L L' : LSF} {β : ℕ}
    (ρ : Rotation G) (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (h : L.F = L'.F) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') [] := by
  obtain ⟨T, F, w⟩ := L
  obtain ⟨T', F', w'⟩ := L'
  change F = F' at h
  subst F'
  exact ⟨trivial, graphEq_refl _, .refl _⟩

/-- Releasing distinct forest edges in the given order changes the core by `releasesBatch`. This is
`orderedCore_releases` with the canonical roots and the batch written out. -/
theorem orderedCore_releasesBatch {G : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    {L L' : LSF} (cuts : List ℕ) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (hR : L.F.R ⊆ L'.F.R)
    (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) {β : ℕ} (hβ : 2 ≤ β) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF')
      (releasesBatch G L'.F.R L cuts) := by
  induction cuts generalizing L with
  | nil =>
    have hFE : L.F.F = L'.F.F := hCut
    have hRC : L.F.R.card = L'.F.R.card := by
      rw [← rootedForest_components_card hF, ← rootedForest_components_card hF', hFE]
    have hRE := Finset.eq_of_subset_of_card_le hR hRC.ge
    have hRF' (A B : RootedForest) (hf : A.F = B.F) (hr : A.R = B.R) : A = B := by
      cases A
      cases B
      exact congrArg₂ RootedForest.mk hf hr
    exact ordered_core_nil ρ hG hF hF' (hRF' L.F L'.F hFE hRE)
  | cons e cuts ih =>
    let K := eraseForestEdge L.F.F e
    have he := hMem e List.mem_cons_self
    have hKn := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = L'.F.F := hCut
    have hFinalK : K.IsSubgraph L'.F.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ a ∈ L.F.R, ∀ b ∈ L.F.R, K.Connected a b → a = b := by
      intro a ha b hb hConn
      have hr := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hr
    obtain ⟨hIncl, hSub, hMid⟩ := canonRoots_spec hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R L'.F.R⟩, L.wstr⟩
    have hComp := forest_eraseEdge_components_card hF.1 he
    change (components K).card = _ at hComp
    have hRc : (canonRoots K L.F.R L'.F.R).card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact hComp
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    have hnew : newRoot Lmid.F.R L.F.R = fresh := newRoot_eq heq hf
    have h₀ := orderedCore_release_canon (L' := Lmid) ρ hG hF hMid he rfl heq hf hβ
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := by
      intro f hf
      exact Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf),
        hMem f (List.mem_cons_of_mem _ hf)⟩
    have h₁ := ih (L := Lmid) hMid hSub hrest hMemRest (List.nodup_cons.mp hn).2
    have hb := h₀.append h₁
    rw [← hnew] at hb
    exact hb

/-- Each release adds one core split. -/
theorem releasesBatch_splitCount (G : MGraph) (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    batchSplitCount (releasesBatch G final L cuts) = cuts.length := by
  induction cuts generalizing L with
  | nil => rfl
  | cons e cuts ih =>
    simp only [releasesBatch, batchSplitCount, refineSplit, List.countP_cons, isSplit,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] at ih ⊢
    rw [ih]

/-- A release deletes no core edge. -/
theorem releasesBatch_countP_delete (G : MGraph) (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    (releasesBatch G final L cuts).countP deleteTag = 0 := by
  induction cuts generalizing L with
  | nil => rfl
  | cons e cuts ih =>
    simp only [releasesBatch, refineSplit, List.countP_cons, deleteTag, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero]
    exact ih _

end MinCostFlow.SparseCore
