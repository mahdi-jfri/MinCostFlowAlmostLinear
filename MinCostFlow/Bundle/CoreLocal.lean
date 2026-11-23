module

public import MinCostFlow.Bundle.CoreInput
import MinCostFlow.SparseCore.CoreModel
import MinCostFlow.LSF.Walks

/-!
# Ordered core batches stay inside the components of a forest

The ordered core batches of `CoreInput.lean` and `CoreReleases.lean` split a core vertex `r`
into `r` and a fresh root. Both lie in the same tree of the forest before the step: the fresh
root takes a part of the tree of `r`. This file records that fact. Give each vertex a label so
that the two ends of every forest edge have the same label. Then every split of the ordered
core batch splits a vertex into two vertices with the same label. Later the label is the
component of the initial graph, so that a core split never moves ends between components.

The batches are the ones of `orderedCore_input` and `orderedCore_releases`, built again here
with this extra conclusion. A core deletion also comes only from a deletion of the input.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

/-- The two ends of every edge of `F` have the same label. -/
@[expose] def ForestLabeled {α : Type*} (lab : ℕ → α) (F : MGraph) : Prop :=
  ∀ e ∈ F.E, lab (F.tail e) = lab (F.head e)

/-- Every split of the batch splits a vertex into two vertices with the same label. -/
@[expose] def SplitsLabeled {α : Type*} (lab : ℕ → α) (U : List Update) : Prop :=
  ∀ op ∈ U, ∀ v v' St Sh, op = .split v v' St Sh → lab v = lab v'

/-- Every deletion of the batch deletes the edge that `u` deletes. -/
@[expose] def DeletesOf (U : List Update) (u : Update) : Prop :=
  ∀ op ∈ U, ∀ e, op = .delete e → u = .delete e

theorem ForestLabeled.walk {α : Type*} {lab : ℕ → α} {F : MGraph} (h : ForestLabeled lab F) :
    ∀ {u v : ℕ} {P : List End}, F.IsWalk u v P → lab u = lab v
  | _, _, _, .nil _ => rfl
  | _, _, x :: _, .cons hx hs hrest => by
    have hx' : lab (F.src x) = lab (F.dst x) := by
      obtain ⟨e, b⟩ := x
      cases b
      · exact (h e hx).symm
      · exact h e hx
    rw [← hs, hx']
    exact ForestLabeled.walk h hrest

/-- Vertices connected in a labeled forest have the same label. -/
theorem ForestLabeled.connected {α : Type*} {lab : ℕ → α} {F : MGraph} (h : ForestLabeled lab F)
    {u v : ℕ} (hc : F.Connected u v) : lab u = lab v := by
  obtain ⟨P, hP⟩ := hc
  exact h.walk hP

/-- A subgraph of a labeled forest is labeled. -/
theorem ForestLabeled.subgraph {α : Type*} {lab : ℕ → α} {F H : MGraph} (h : ForestLabeled lab F)
    (hs : F.IsSubgraph H) : ForestLabeled lab H := by
  intro e he
  obtain ⟨ht, hh⟩ := hs.2.2 e he
  rw [ht, hh]
  exact h e (hs.2.1 he)

/-- A vertex split keeps a labeled forest labeled when the two vertices have the same label. -/
theorem ForestLabeled.split {α : Type*} {lab : ℕ → α} {F : MGraph} (h : ForestLabeled lab F)
    {v v' : ℕ} (St Sh : Finset ℕ) (hv : lab v = lab v') :
    ForestLabeled lab (F.applyUpdate (.split v v' St Sh)) := by
  intro e he
  have he' : e ∈ F.E := he
  have ht : lab ((F.applyUpdate (.split v v' St Sh)).tail e) = lab (F.tail e) := by
    change lab (if e ∈ St ∧ F.tail e = v then v' else F.tail e) = _
    split_ifs with hc
    · rw [hc.2, hv]
    · rfl
  have hh : lab ((F.applyUpdate (.split v v' St Sh)).head e) = lab (F.head e) := by
    change lab (if e ∈ Sh ∧ F.head e = v then v' else F.head e) = _
    split_ifs with hc
    · rw [hc.2, hv]
    · rfl
  rw [ht, hh]
  exact h e he'

/-- The forest after the input edit is labeled when the old forest is and an input split keeps
the label. -/
theorem ForestLabeled.forestAfterInput {α : Type*} {lab : ℕ → α} {F : MGraph}
    (h : ForestLabeled lab F) {u : Update}
    (hu : ∀ v v' St Sh, u = .split v v' St Sh → lab v = lab v') :
    ForestLabeled lab (forestAfterInput F u) := by
  cases u with
  | insert => exact h
  | delete e => exact h.subgraph (eraseForestEdge_subgraph F e)
  | split v v' St Sh => exact h.split St Sh (hu v v' St Sh rfl)

/-- The two parts of a cut forest edge get the same label. -/
private theorem label_of_cut {α : Type*} {lab : ℕ → α} {F F' : MGraph}
    (h : ForestLabeled lab F) (hs : F.IsSubgraph F') {x : End} (hx : x.1 ∈ F.E) {r fresh : ℕ}
    (hk : F'.Connected (F.src x) r) (hm : F'.Connected (F.dst x) fresh) : lab r = lab fresh := by
  have h' := h.subgraph hs
  have hx' : lab (F.src x) = lab (F.dst x) := by
    obtain ⟨e, b⟩ := x
    cases b
    · exact (h e hx).symm
    · exact h e hx
  rw [← h'.connected hk, hx', h'.connected hm]

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

/-- Deleting an input forest edge is a single ordered core split, of a vertex into two vertices
with the same label (`orderedCore_delete_forest`). -/
theorem orderedCore_delete_forest_labeled {α : Type*} {lab : ℕ → α} {G : MGraph} {L L' : LSF}
    {e fresh β : ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.delete e)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.delete e)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)))
    (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hs : RotationStep β (.delete e) ρ σ) (hβ : 2 ≤ β) (hlab : ForestLabeled lab L.F.F) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 ∧ SplitsLabeled lab U := by
  obtain ⟨⟨f, side⟩, hf', hk, hm⟩ := roots_cut_pair hF hF' rfl he hCut hRoots
  change f = e at hf'
  subst f
  have hr := (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
  have hsub : L.F.F.IsSubgraph L'.F.F := by rw [hCut]; exact eraseForestEdge_subgraph _ _
  have hl := label_of_cut hlab hsub (x := (e, side)) he hk hm
  obtain ⟨hu, hg, hstep⟩ := coreRotation_cut ρ σ hG hH hF hF' he hCut hRoots hr hf hk hm hs hβ
  refine ⟨_, OrderedCoreBatch.singleton hu hg hstep, rfl, rfl, ?_⟩
  intro op hop v v' St Sh hop'
  rw [List.mem_singleton.mp hop] at hop'
  obtain ⟨rfl, rfl, -, -⟩ := Update.split.inj hop'
  exact hl

/-- Releasing one forest edge gives an ordered core split, of a vertex into two vertices with the
same label, followed by an insertion (`orderedCore_release`). -/
theorem orderedCore_release_labeled {α : Type*} {lab : ℕ → α} {G : MGraph} (ρ : Rotation G)
    (hG : G.IsValid)
    {L L' : LSF} (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf G)
    {e fresh β : ℕ} (he : e ∈ L.F.F.E) (hCut : L'.F.F = eraseForestEdge L.F.F e)
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R) (hβ : 2 ≤ β)
    (hlab : ForestLabeled lab L.F.F) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 ∧ SplitsLabeled lab U := by
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
  have hsub : L.F.F.IsSubgraph L'.F.F := by rw [hCut]; exact eraseForestEdge_subgraph _ _
  have hCutStep : ∃ u : Update, OrderedCoreBatch β (coreRotation ρ hG hF)
      (coreRotation σ hH hFH) [u] ∧ isSplit u ∧
      ∀ v v' St Sh, u = .split v v' St Sh → lab v = lab v' := by
    obtain ⟨a, side⟩ := x
    change a = e at hx
    subst a
    have hl := label_of_cut hlab hsub (x := (e, side)) he hk hm
    obtain ⟨hu, hg, hs⟩ := coreRotation_cut ρ σ hG hH hF hFH he hCut hRoots hr hf hk hm hDel hβ
    refine ⟨_, OrderedCoreBatch.singleton hu hg hs, rfl, ?_⟩
    intro v v' St Sh hop'
    obtain ⟨rfl, rfl, -, -⟩ := Update.split.inj hop'
    exact hl
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
  obtain ⟨u, hU, hu, hul⟩ := hCutStep
  refine ⟨[u] ++ [ins], hU.append (OrderedCoreBatch.singleton hiV hEq hIns), ?_, ?_, ?_⟩
  · have ht : isSplit ins = false := rfl
    simp [batchSplitCount, hu, ht]
  · have htag : deleteTag u = false := by
      cases u <;> simp_all [deleteTag, isSplit]
    have hiTag : deleteTag ins = false := rfl
    simp [htag, hiTag]
  · intro op hop v v' St Sh hop'
    rcases List.mem_append.mp hop with h | h
    · rw [List.mem_singleton.mp h] at hop'
      exact hul v v' St Sh hop'
    · rw [List.mem_singleton.mp h] at hop'
      exact Update.noConfusion hop'

private theorem ordered_core_nil {G : MGraph} {L L' : LSF} {β : ℕ}
    (ρ : Rotation G) (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (h : L.F = L'.F) :
    OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') [] := by
  obtain ⟨T, F, w⟩ := L
  obtain ⟨T', F', w'⟩ := L'
  change F = F' at h
  subst F'
  exact ⟨trivial, graphEq_refl _, .refl _⟩

/-- Releasing distinct forest edges in succession gives an ordered batch with one split per cut,
and every split keeps the label (`orderedCore_releases`). -/
theorem orderedCore_releases_labeled {α : Type*} {lab : ℕ → α} {G : MGraph} (ρ : Rotation G)
    (hG : G.IsValid)
    {L L' : LSF} (cuts : List ℕ) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (hR : L.F.R ⊆ L'.F.R)
    (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) {β : ℕ} (hβ : 2 ≤ β)
    (hlab : ForestLabeled lab L.F.F) :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation ρ hG hF') U ∧
      batchSplitCount U = cuts.length ∧ U.countP deleteTag = 0 ∧ SplitsLabeled lab U := by
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
    have hRF := hRF' L.F L'.F hFE hRE
    exact ⟨[], ordered_core_nil ρ hG hF hF' hRF, rfl, rfl, by simp [SplitsLabeled]⟩
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
    obtain ⟨R, hIncl, hSub, hMid⟩ := exists_roots_refinement hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, R⟩, L.wstr⟩
    have hComp := forest_eraseEdge_components_card hF.1 he
    change (components K).card = _ at hComp
    have hRc : R.card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact hComp
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    obtain ⟨U₀, h₀, hcount₀, hd₀, hl₀⟩ :=
      orderedCore_release_labeled (L' := Lmid) ρ hG hF hMid he rfl heq hf hβ hlab
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := by
      intro f hf
      exact Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf),
        hMem f (List.mem_cons_of_mem _ hf)⟩
    obtain ⟨U₁, h₁, hcount₁, hd₁, hl₁⟩ := ih (L := Lmid) hMid hSub hrest hMemRest
      (List.nodup_cons.mp hn).2 (hlab.subgraph hKsub)
    refine ⟨U₀ ++ U₁, h₀.append h₁, ?_, ?_, ?_⟩
    · rw [batchSplitCount_append, hcount₀, hcount₁, List.length_cons, Nat.add_comm]
    · simp [List.countP_append, hd₀, hd₁]
    · intro op hop
      rcases List.mem_append.mp hop with h | h
      · exact hl₀ op h
      · exact hl₁ op h

private theorem orderedCore_split_named_labeled {α : Type*} {lab : ℕ → α} {G : MGraph}
    {L L' : LSF} {v v' fresh β : ℕ} {At Ah : Finset ℕ}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate (.split v v' At Ah)))
    (hG : G.IsValid) (hH : (G.applyUpdate (.split v v' At Ah)).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf (G.applyUpdate (.split v v' At Ah)))
    (hForest : L'.F.F = L.F.F.applyUpdate (.split v v' At Ah))
    (hRoots : L'.F.R = insert fresh L.F.R) (hf : fresh ∉ L.F.R)
    (hu : G.UpdateIsValid (.split v v' At Ah)) (hs : RotationStep β (.split v v' At Ah) ρ σ)
    (hlab : ForestLabeled lab L.F.F) (hvv : lab v = lab v') :
    ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hF') U ∧
      batchSplitCount U = 1 ∧ U.countP deleteTag = 0 ∧ SplitsLabeled lab U := by
  let H := G.applyUpdate (.split v v' At Ah)
  let P : ℕ → ℕ := fun w => if w = v' then v else w
  let r := L.F.root v
  have hvf : v' ∉ L.F.F.V := fun h => hu.2.1 (hF.2.1 ▸ h)
  have hvG : v ∈ H.V := Finset.mem_insert_of_mem hu.1
  have hvG' : v' ∈ H.V := Finset.mem_insert_self _ _
  have hn : L'.F.root v ≠ L'.F.root v' := by
    intro he
    have hc := connected_of_root_eq hF' hvG hvG' he
    rw [hForest] at hc
    exact applySplit_separates hF.1 (hF.2.1.symm ▸ hu.1) hvf At Ah hc
  have hr (w : ℕ) (hw : w ∈ H.V) (he : P w = v) :
      L'.F.root w = r ∨ L'.F.root w = fresh := by
    obtain ⟨hwR, hc⟩ := root_mem_R hF' hw
    rw [hRoots] at hwR
    rcases Finset.mem_insert.mp hwR with hFresh | hOld
    · exact Or.inr hFresh
    · have htG := hF.2.2.1 hOld
      have hp : P (L'.F.root w) = L'.F.root w := by
        have hne : L'.F.root w ≠ v' := fun h => hu.2.1 (h ▸ htG)
        simp [P, hne]
      rw [hForest] at hc
      have hproj := connected_applySplit_proj hF.1.1 hvf At Ah hc
      change L.F.F.Connected (P w) (P (L'.F.root w)) at hproj
      rw [he, hp] at hproj
      exact Or.inl ((root_eq_of_mem_R hF hOld).symm.trans
        (root_eq_of_connected hF hu.1 htG hproj).symm)
  obtain ⟨side, hk, hm⟩ : ∃ side : Bool,
      L'.F.F.Connected (if side then v else v') r ∧
      L'.F.F.Connected (if side then v' else v) fresh := by
    rcases hr v hvG (by simp [P]) with h₁ | h₁ <;> rcases hr v' hvG' (by simp [P]) with h₂ | h₂
    · exact (hn (h₁.trans h₂.symm)).elim
    · refine ⟨true, ?_, ?_⟩
      · change L'.F.F.Connected v r
        exact h₁ ▸ (root_mem_R hF' hvG).2
      · change L'.F.F.Connected v' fresh
        exact h₂ ▸ (root_mem_R hF' hvG').2
    · refine ⟨false, ?_, ?_⟩
      · change L'.F.F.Connected v' r
        exact h₂ ▸ (root_mem_R hF' hvG').2
      · change L'.F.F.Connected v fresh
        exact h₁ ▸ (root_mem_R hF' hvG).2
    · exact (hn (h₁.trans h₂.symm)).elim
  have hlab' : ForestLabeled lab L'.F.F := hForest ▸ hlab.split At Ah hvv
  have hl : lab r = lab fresh := by
    have h₁ := hlab'.connected hk
    have h₂ := hlab'.connected hm
    have hs₁ : lab (if side then v else v') = lab v := by cases side <;> simp [hvv]
    have hs₂ : lab (if side then v' else v) = lab v := by cases side <;> simp [hvv]
    rw [← h₁, ← h₂, hs₁, hs₂]
  obtain ⟨hv, he, ho⟩ := coreRotation_vertexSplit side ρ σ hG hH hF hF' hForest
    hRoots hf hk hm hu hs
  refine ⟨_, OrderedCoreBatch.singleton hv he ho, rfl, rfl, ?_⟩
  intro op hop w w' St Sh hop'
  rw [List.mem_singleton.mp hop] at hop'
  obtain ⟨rfl, rfl, -, -⟩ := Update.split.inj hop'
  exact hl

/-- The input edit has an ordered core batch before the additional forest releases
(`orderedCore_input`). Its splits keep the label, and its deletion is the input deletion. An input
deletion of an edge outside the forest is a core deletion. -/
theorem orderedCore_input_labeled {α : Type*} {lab : ℕ → α} {G : MGraph} {L last : LSF}
    {β : ℕ} {u : Update}
    (ρ : Rotation G) (σ : Rotation (G.applyUpdate u))
    (hG : G.IsValid) (hH : (G.applyUpdate u).IsValid)
    (hF : L.F.IsRootedSpanningForestOf G)
    (hlast : last.F.IsRootedSpanningForestOf (G.applyUpdate u))
    (hu : G.UpdateIsValid u) (hs : RotationStep β u ρ σ) (hβ : 2 ≤ β)
    (hR : L.F.R ⊆ last.F.R)
    (hK : (forestAfterInput L.F.F u).IsForest)
    (hKG : (G.applyUpdate u).IsSubgraph (forestAfterInput L.F.F u))
    (hsub : (forestAfterInput L.F.F u).IsSubgraph last.F.F)
    (hlab : ForestLabeled lab L.F.F)
    (hsplit : ∀ v v' St Sh, u = .split v v' St Sh → lab v = lab v') :
    ∃ mid : LSF, ∃ hm : mid.F.IsRootedSpanningForestOf (G.applyUpdate u),
      mid.F.F = forestAfterInput L.F.F u ∧ L.F.R ⊆ mid.F.R ∧ mid.F.R ⊆ last.F.R ∧
      ∃ U, OrderedCoreBatch β (coreRotation ρ hG hF) (coreRotation σ hH hm) U ∧
        batchSplitCount U = updateSplitTag u + forestDeleteTag L.F.F u ∧
        U.countP deleteTag ≤ 1 ∧ SplitsLabeled lab U ∧ DeletesOf U u ∧
        ∀ e, u = .delete e → e ∉ L.F.F.E → Update.delete e ∈ U := by
  have hIntermediate := exists_roots_refinement hK
    (by
      cases u with
      | insert => exact hF.2.1
      | delete => exact hF.2.1
      | split => simp [forestAfterInput, MGraph.applyUpdate, hF.2.1])
    hKG hlast hsub hR
    (fun a ha b hb hc => by
      have hconn : L.F.F.Connected a b := by
        cases u with
        | insert => exact hc
        | delete e => exact connected_of_subgraph (eraseForestEdge_subgraph _ e) hc
        | split v v' St Sh =>
          have hvf : v' ∉ L.F.F.V := fun he => hu.2.1 (hF.2.1 ▸ he)
          have ha' : a ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 ha)
          have hb' : b ≠ v' := fun he => hu.2.1 (he ▸ hF.2.2.1 hb)
          exact by simpa [ha', hb'] using connected_applySplit_proj hF.1.1 hvf St Sh hc
      have hEq := root_eq_of_connected hF (hF.2.2.1 ha) (hF.2.2.1 hb) hconn
      rwa [root_eq_of_mem_R hF ha, root_eq_of_mem_R hF hb] at hEq)
  cases u with
  | insert e a b =>
    have hm : L.F.IsRootedSpanningForestOf (G.applyUpdate (.insert e a b)) :=
      ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hKG⟩
    obtain ⟨he, ho⟩ := coreRotation_insert ρ σ hG hH hF hm hu hs
    let op := Update.insert e (L.F.root a) (L.F.root b)
    have hv : (coreGraph G L).UpdateIsValid op :=
      ⟨fun h => hu.1 (Finset.mem_sdiff.mp h).1, (root_mem_R hF hu.2.1).1,
        (root_mem_R hF hu.2.2).1⟩
    refine ⟨L, hm, rfl, Finset.Subset.rfl, hR, [op], OrderedCoreBatch.singleton hv he ho, rfl,
      by simp [op, deleteTag], ?_, ?_, ?_⟩
    · intro o ho' v v' St Sh h
      rw [List.mem_singleton.mp ho'] at h
      exact Update.noConfusion h
    · intro o ho' f h
      rw [List.mem_singleton.mp ho'] at h
      exact Update.noConfusion h
    · intro f h
      exact Update.noConfusion h
  | delete e =>
    by_cases he : e ∈ L.F.F.E
    · obtain ⟨R, hRo, hRf, hm⟩ := hIntermediate
      let mid : LSF := ⟨L.T, ⟨forestAfterInput L.F.F (.delete e), R⟩, L.wstr⟩
      have hcount : R.card = L.F.R.card + 1 := by
        rw [← rootedForest_components_card hm, ← rootedForest_components_card hF]
        exact forest_eraseEdge_components_card hF.1 he
      obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
      obtain ⟨U, ho, hC, hd, hl⟩ :=
        orderedCore_delete_forest_labeled (L' := mid) ρ σ hG hH hF hm he rfl hR' hnew hs hβ hlab
      refine ⟨mid, hm, rfl, hRo, hRf, U, ho, ?_, ?_, hl, ?_, ?_⟩
      · simpa [updateSplitTag, forestDeleteTag, he] using hC
      · simp [hd]
      · intro o ho' f h
        have hz := List.countP_eq_zero.mp hd o ho'
        rw [h] at hz
        exact absurd rfl hz
      · intro f hf hfF
        obtain rfl := Update.delete.inj hf
        exact absurd he hfF
    · have hK_eq : forestAfterInput L.F.F (.delete e) = L.F.F := by
        change { L.F.F with E := L.F.F.E.erase e } = L.F.F
        rw [Finset.erase_eq_of_notMem he]
      have hHG : (G.applyUpdate (.delete e)).IsSubgraph L.F.F := hK_eq ▸ hKG
      have hm : L.F.IsRootedSpanningForestOf (G.applyUpdate (.delete e)) :=
        ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hHG⟩
      obtain ⟨hEq, ho⟩ := coreRotation_delete ρ σ hG hH hF hm he hs
      have hv : (coreGraph G L).UpdateIsValid (.delete e) := Finset.mem_sdiff.mpr ⟨hu, he⟩
      refine ⟨L, hm, hK_eq.symm, Finset.Subset.rfl, hR, [.delete e],
        OrderedCoreBatch.singleton hv hEq ho, ?_, ?_, ?_, ?_, ?_⟩
      · simp [batchSplitCount, updateSplitTag, forestDeleteTag, he, isSplit]
      · simp [deleteTag]
      · intro o ho' v v' St Sh h
        rw [List.mem_singleton.mp ho'] at h
        exact Update.noConfusion h
      · intro o ho' f h
        rw [← List.mem_singleton.mp ho', h]
      · intro f hf _
        obtain rfl := Update.delete.inj hf
        exact List.mem_singleton_self _
  | split v v' St Sh =>
    obtain ⟨R, hRo, hRf, hm⟩ := hIntermediate
    let mid : LSF := ⟨L.T, ⟨forestAfterInput L.F.F (.split v v' St Sh), R⟩, L.wstr⟩
    have hcount : R.card = L.F.R.card + 1 := by
      have ho := rootedForest_R_add_edges hF
      have hn := rootedForest_R_add_edges hm
      have hv : (G.applyUpdate (.split v v' St Sh)).V.card = G.V.card + 1 :=
        Finset.card_insert_of_notMem hu.2.1
      change R.card + L.F.F.E.card = (G.applyUpdate (.split v v' St Sh)).V.card at hn
      omega
    obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
    obtain ⟨U, ho, hC, hd, hl⟩ := orderedCore_split_named_labeled (L' := mid) ρ σ hG hH hF hm rfl
      hR' hnew hu hs hlab (hsplit v v' St Sh rfl)
    refine ⟨mid, hm, rfl, hRo, hRf, U, ho, hC, hd ▸ Nat.zero_le _, hl, ?_, ?_⟩
    · intro o ho' f h
      have hz := List.countP_eq_zero.mp hd o ho'
      rw [h] at hz
      exact absurd rfl hz
    · intro f hf
      exact Update.noConfusion hf

end MinCostFlow.Bundle
