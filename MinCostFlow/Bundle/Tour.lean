module

public import MinCostFlow.Bundle.Cyclic
public import MinCostFlow.LSF.Components

/-!
# Forest tours

A forest dart leads to the component on its far side. Expand the blocks of a
vertex rotation by entering those components, starting after the return dart.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.LSF

/-- A rotation system lists each vertex's ends once. -/
structure Rotation (G : MGraph) where
  /-- A linear representative of the rotation at each vertex. -/
  order : ℕ → List End
  /-- Each representative has no repeated end. -/
  nodup : ∀ v, (order v).Nodup
  /-- Source vertices of darts give the vertices of their corresponding ends. -/
  mem_order : ∀ v x, x ∈ order v ↔ x.1 ∈ G.E ∧ G.src x = v

/-- The end at the other side of the edge. -/
def End.flip (x : End) : End := (x.1, !x.2)

/-- List the ends starting after the specified end, leaving that end out. -/
def afterEnd (x : End) (xs : List End) : List End :=
  let before := xs.takeWhile (· != x)
  xs.drop (before.length + 1) ++ before

/-- Remove a forest edge while retaining its vertices. -/
abbrev eraseForestEdge (F : MGraph) (e : ℕ) : MGraph := { F with E := F.E.erase e }

theorem eraseForestEdge_subgraph (F : MGraph) (e : ℕ) :
    F.IsSubgraph (eraseForestEdge F e) :=
  ⟨Finset.Subset.rfl, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩

theorem not_connected_eraseForestEdge {F : MGraph} (hF : F.IsForest) {x : End}
    (hx : x.1 ∈ F.E) : ¬ (eraseForestEdge F x.1).Connected (F.src x) (F.dst x) := by
  have hp : F.IsPath (F.src x) (F.dst x) [x] := by
    refine ⟨.cons hx rfl (.nil _), ?_⟩
    obtain ⟨e, b⟩ := x
    have h := isForest_no_selfLoop hF hx
    cases b <;> simp [MGraph.walkVertices, MGraph.src, MGraph.dst, h, Ne.symm h]
  change ¬ ({ F with E := F.E.erase x.1 } : MGraph).Connected (F.src x) (F.dst x)
  apply not_connected_erase_of_mem_forestPath hF
  rw [forestPath_eq_of_isPath hF hp]
  exact mem_walkEdges_of_mem List.mem_cons_self

/-- The branch beyond a forest end has fewer vertices than the current component. -/
theorem branch_card_lt {F : MGraph} (hF : F.IsForest) {x : End} (hx : x.1 ∈ F.E) :
    (compOf (eraseForestEdge F x.1) (F.dst x)).card < (compOf F (F.src x)).card := by
  have hconn : F.Connected (F.src x) (F.dst x) := ⟨[x], .cons hx rfl (.nil _)⟩
  have hsrc : F.src x ∈ F.V := by
    obtain ⟨e, b⟩ := x
    have h := hF.1 e hx
    cases b
    · exact h.2
    · exact h.1
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨hvV, hvconn⟩ := mem_compOf_iff.mp hv
    exact mem_compOf_iff.mpr ⟨hvV, connected_trans hconn
      (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hvconn)⟩
  · intro he
    have hm : F.src x ∈ compOf (eraseForestEdge F x.1) (F.dst x) :=
      he ▸ self_mem_compOf hsrc
    exact not_connected_eraseForestEdge hF hx (connected_symm (mem_compOf_iff.mp hm).2)

/-- Expand the given ends at `v` into blocks.
`F₀` determines which ends are open. `F` is the forest left after cutting the
edges crossed on the way into this branch. Its component at `v` is the
current branch. -/
noncomputable def tourBlocks (G F₀ : MGraph) (ρ : Rotation G)
    (F : MGraph) (hF : F.IsForest) (v : ℕ) (xs : List End) : List End :=
  xs.flatMap fun x =>
    if x.1 ∉ F₀.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      tourBlocks G F₀ ρ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (ρ.order (F.dst x)))
    else []
termination_by (compOf F v).card
decreasing_by
  rw [← _h.2]
  exact branch_card_lt hF _h.1

/-- Tour of the component containing `v`, with its rotation as start. -/
noncomputable def tour {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest) (v : ℕ) : List End :=
  tourBlocks G F ρ F hF v (ρ.order v)

/-- The linear block behind a forest end. -/
noncomputable def branch {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest) (x : End) : List End :=
  tourBlocks G F ρ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
    (afterEnd x.flip (ρ.order (F.dst x)))

private theorem afterEnd_of_append (x : End) (before rest : List End)
    (h : x ∉ before) : afterEnd x (before ++ x :: rest) = rest ++ before := by
  have hp : ∀ y ∈ before, y != x := by
    intro y hy
    exact bne_iff_ne.mpr (fun he => h (he ▸ hy))
  simp [afterEnd, List.takeWhile_append_of_pos hp, List.drop_append]

theorem afterEnd_perm_erase {x : End} {xs : List End} (h : x ∈ xs) (hn : xs.Nodup) :
    (afterEnd x xs).Perm (xs.erase x) := by
  obtain ⟨before, rest, rfl⟩ := List.mem_iff_append.mp h
  have hnot : x ∉ before := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 x hm x (by simp) rfl
  rw [afterEnd_of_append x before rest hnot, List.erase_append_right _ hnot]
  simp only [List.erase_cons_head]
  exact List.perm_append_comm

private theorem path_from_branch {F : MGraph} (hF : F.IsForest)
    {x : End} (hx : x.1 ∈ F.E) {w : ℕ}
    (hw : (eraseForestEdge F x.1).Connected (F.dst x) w) :
    ∃ P, F.IsPath (F.src x) w (x :: P) := by
  obtain ⟨P, hp⟩ := connected_isPath hw
  have hh := (isWalk_of_subgraph (eraseForestEdge_subgraph F x.1) hp.1).1
  refine ⟨P, .cons hx rfl hh, ?_⟩
  rw [walkVertices_cons, List.nodup_cons]
  refine ⟨?_, hp.2⟩
  intro hm
  obtain ⟨L, _, _, hL, _⟩ := walkVertices_mem_split hp.1 hm
  exact not_connected_eraseForestEdge hF hx (connected_symm ⟨L, hL⟩)

private theorem exists_branch_of_connected {F : MGraph} {v w : ℕ}
    (hvw : F.Connected v w) (hne : v ≠ w) :
    ∃ x : End, x.1 ∈ F.E ∧ F.src x = v ∧
      (eraseForestEdge F x.1).Connected (F.dst x) w := by
  obtain ⟨P, hp⟩ := connected_isPath hvw
  cases P with
  | nil => cases hp.1; exact (hne rfl).elim
  | cons x P =>
    cases hp.1 with
    | cons he hs hP =>
      refine ⟨x, he, hs, P, isWalk_eraseEdge_of_not_mem hP ?_⟩
      have hn := (List.nodup_cons.mp (isPath_nodup_edges hp)).1
      simpa [walkEdges] using hn

private theorem branch_unique {F : MGraph} (hF : F.IsForest) {x y : End} {w : ℕ}
    (hx : x.1 ∈ F.E) (hy : y.1 ∈ F.E) (hs : F.src x = F.src y)
    (hwx : (eraseForestEdge F x.1).Connected (F.dst x) w)
    (hwy : (eraseForestEdge F y.1).Connected (F.dst y) w) : x = y := by
  obtain ⟨P, hp⟩ := path_from_branch hF hx hwx
  obtain ⟨Q, hq⟩ := path_from_branch hF hy hwy
  exact (List.cons.inj (isPath_unique hF hp (hs.symm ▸ hq))).1


private theorem src_flip (G : MGraph) (x : End) : G.src x.flip = G.dst x := by
  cases x with
  | mk e b => cases b <;> rfl

private theorem src_eq_of_subgraph {F G : MGraph} (h : G.IsSubgraph F) {x : End}
    (hx : x.1 ∈ F.E) : F.src x = G.src x := by
  obtain ⟨e, b⟩ := x
  have hs := h.2.2 e hx
  cases b
  · exact hs.2
  · exact hs.1

private theorem dst_mem_vertices {F : MGraph} (hF : F.IsValid) {x : End} (hx : x.1 ∈ F.E) :
    F.dst x ∈ F.V := by
  rw [← src_flip]
  obtain ⟨e, b⟩ := x
  have h := hF e hx
  cases b
  · exact h.1
  · exact h.2

private theorem src_mem_vertices {F : MGraph} (hF : F.IsValid) {x : End} (hx : x.1 ∈ F.E) :
    F.src x ∈ F.V := by
  obtain ⟨e, b⟩ := x
  have h := hF e hx
  cases b
  · exact h.2
  · exact h.1

private theorem tourBlocks_spec (G F₀ : MGraph) (ρ : Rotation G) (hG : G.IsValid)
    (F : MGraph) (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V)
    (hE : F.E ⊆ F₀.E) (v : ℕ) (xs : List End)
    (hnd : xs.Nodup) (hs : xs ⊆ ρ.order v)
    (hc : ∀ x ∈ ρ.order v, x.1 ∉ F₀.E ∨ x.1 ∈ F.E → x ∈ xs) :
    (tourBlocks G F₀ ρ F hF v xs).Nodup ∧
    ∀ z, z ∈ tourBlocks G F₀ ρ F hF v xs ↔
      z.1 ∈ G.E ∧ z.1 ∉ F₀.E ∧ F.Connected v (G.src z) := by
  let block (x : End) :=
    if x.1 ∉ F₀.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      tourBlocks G F₀ ρ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (ρ.order (F.dst x)))
    else []
  have heq : tourBlocks G F₀ ρ F hF v xs = xs.flatMap block := by
    rw [tourBlocks]
  have hblock : ∀ x ∈ xs, (block x).Nodup ∧ ∀ z, z ∈ block x ↔
      (x.1 ∉ F₀.E ∧ z = x) ∨
      (x.1 ∈ F.E ∧ F.src x = v ∧ z.1 ∈ G.E ∧ z.1 ∉ F₀.E ∧
        (eraseForestEdge F x.1).Connected (F.dst x) (G.src z)) := by
    intro x hx
    by_cases hxe : x.1 ∈ F.E
    · have hx₀ := hE hxe
      have hxv := (src_eq_of_subgraph hsub hxe).trans ((ρ.mem_order v x).mp (hs hx)).2
      have hflip : x.flip ∈ ρ.order (F.dst x) := by
        apply (ρ.mem_order _ _).mpr
        exact ⟨hsub.2.1 hxe, (src_eq_of_subgraph (x := x.flip) hsub hxe).symm.trans
          (src_flip F x)⟩
      have hperm := afterEnd_perm_erase hflip (ρ.nodup _)
      have hcover : ∀ y ∈ ρ.order (F.dst x),
          y.1 ∉ F₀.E ∨ y.1 ∈ (eraseForestEdge F x.1).E →
            y ∈ afterEnd x.flip (ρ.order (F.dst x)) := by
        intro y hy hyE
        have hn : y ≠ x.flip := by
          intro he
          subst y
          rcases hyE with hn | hm
          · exact hn hx₀
          · exact (Finset.mem_erase.mp hm).1 rfl
        exact hperm.mem_iff.mpr (List.mem_erase_of_ne hn |>.mpr hy)
      have hsub' : G.IsSubgraph (eraseForestEdge F x.1) :=
        ⟨hsub.1, fun _ he => hsub.2.1 ((Finset.mem_erase.mp he).2),
          fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
      have hrec := tourBlocks_spec G F₀ ρ hG (eraseForestEdge F x.1)
        (isForest_eraseEdge hF x.1) hsub' hV
        (fun _ he => hE (Finset.mem_erase.mp he).2) (F.dst x)
        (afterEnd x.flip (ρ.order (F.dst x)))
        (hperm.nodup_iff.mpr ((ρ.nodup _).erase _))
        (fun _ hz => List.mem_of_mem_erase (hperm.mem_iff.mp hz)) hcover
      simpa [block, hxe, hxv, hx₀] using hrec
    · by_cases hx₀ : x.1 ∈ F₀.E
      · simp [block, hxe, hx₀]
      · simp [block, hxe, hx₀, eq_comm]
  rw [heq]
  constructor
  · apply List.nodup_flatMap.mpr
    refine ⟨fun x hx => (hblock x hx).1, ?_⟩
    apply List.Pairwise.imp_of_mem (l := xs) _ hnd
    intro x y hx hy hne
    apply List.disjoint_left.mpr
    intro z hzx hzy
    rcases (hblock x hx).2 z |>.mp hzx with ⟨_, hzEq⟩ | ⟨hxe, hxv, _, _, hzx⟩
    · subst z
      rcases (hblock y hy).2 x |>.mp hzy with ⟨_, hxy⟩ | ⟨hye, hyv, _, _, hzy⟩
      · exact hne hxy
      · have hsrc := ((ρ.mem_order _ _).mp (hs hx)).2
        exact not_connected_eraseForestEdge hF hye (connected_symm (by simpa only [hyv, hsrc] using hzy))
    · rcases (hblock y hy).2 z |>.mp hzy with ⟨_, hzEq⟩ | ⟨hye, hyv, _, _, hzy⟩
      · subst z
        have hsrc := ((ρ.mem_order _ _).mp (hs hy)).2
        exact not_connected_eraseForestEdge hF hxe (connected_symm (by simpa only [hxv, hsrc] using hzx))
      · exact hne (branch_unique hF hxe hye (hxv.trans hyv.symm) hzx hzy)
  · intro z
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hz⟩
      rcases (hblock x hx).2 z |>.mp hz with ⟨hopen, hzEq⟩ | ⟨hxe, hxv, hze, hopen, hconn⟩
      · subst z
        obtain ⟨he, hs'⟩ := (ρ.mem_order _ _).mp (hs hx)
        exact ⟨he, hopen, hs' ▸ connected_refl F v⟩
      · have hstep : F.Connected v (F.dst x) := ⟨[x], .cons hxe hxv (.nil _)⟩
        exact ⟨hze, hopen, connected_trans hstep
          (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hconn)⟩
    · rintro ⟨he, hopen, hconn⟩
      by_cases hvz : v = G.src z
      · have hz := hc z ((ρ.mem_order _ _).mpr ⟨he, hvz.symm⟩) (Or.inl hopen)
        exact ⟨z, hz, ((hblock z hz).2 z).mpr (Or.inl ⟨hopen, rfl⟩)⟩
      · obtain ⟨x, hxe, hxv, hbranch⟩ := exists_branch_of_connected hconn hvz
        have hx := hc x ((ρ.mem_order _ _).mpr ⟨hsub.2.1 hxe,
          (src_eq_of_subgraph hsub hxe).symm.trans hxv⟩) (Or.inr hxe)
        exact ⟨x, hx, ((hblock x hx).2 z).mpr (Or.inr ⟨hxe, hxv, he, hopen, hbranch⟩)⟩
termination_by (compOf F v).card
decreasing_by
  rw [← hxv]
  exact branch_card_lt hF hxe

/-- The tour lists every open end of the component exactly once. -/
theorem tour_spec {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V) (v : ℕ) :
    (tour ρ hF v).Nodup ∧ ∀ z, z ∈ tour ρ hF v ↔
      z.1 ∈ G.E ∧ z.1 ∉ F.E ∧ F.Connected v (G.src z) :=
  tourBlocks_spec G F ρ hG F hF hsub hV Finset.Subset.rfl v (ρ.order v) (ρ.nodup v)
    (fun _ h => h) (fun _ h _ => h)


/-- The branch block lists every open end behind that forest edge exactly once. -/
theorem branch_spec {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V) {x : End} (hx : x.1 ∈ F.E) :
    (branch ρ hF x).Nodup ∧ ∀ z, z ∈ branch ρ hF x ↔
      z.1 ∈ G.E ∧ z.1 ∉ F.E ∧ (eraseForestEdge F x.1).Connected (F.dst x) (G.src z) := by
  have hflip : x.flip ∈ ρ.order (F.dst x) :=
    (ρ.mem_order _ _).mpr ⟨hsub.2.1 hx,
      (src_eq_of_subgraph (x := x.flip) hsub hx).symm.trans (src_flip F x)⟩
  have hperm := afterEnd_perm_erase hflip (ρ.nodup _)
  have hsub' : G.IsSubgraph (eraseForestEdge F x.1) :=
    ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
      fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
  apply tourBlocks_spec G F ρ hG _ _ hsub' hV (Finset.erase_subset _ _) _ _
    (hperm.nodup_iff.mpr ((ρ.nodup _).erase _))
    (fun _ hz => List.mem_of_mem_erase (hperm.mem_iff.mp hz))
  intro z hz hactive
  have hn : z ≠ x.flip := by
    intro he
    subst z
    rcases hactive with hn | he
    · exact hn hx
    · exact (Finset.mem_erase.mp he).1 rfl
  exact hperm.mem_iff.mpr ((List.mem_erase_of_ne hn).mpr hz)

private theorem dst_eq_of_subgraph {F G : MGraph} (h : G.IsSubgraph F) {x : End}
    (hx : x.1 ∈ F.E) : F.dst x = G.dst x := by
  rw [← src_flip, ← src_flip]
  exact src_eq_of_subgraph (x := x.flip) h hx

private theorem eraseForestEdge_mono {F H : MGraph} (hsub : F.IsSubgraph H) (e : ℕ) :
    (eraseForestEdge F e).IsSubgraph (eraseForestEdge H e) :=
  ⟨hsub.1, fun _ he => let hh := Finset.mem_erase.mp he
    Finset.mem_erase.mpr ⟨hh.1, hsub.2.1 hh.2⟩,
    fun f hf => hsub.2.2 f (Finset.mem_erase.mp hf).2⟩

private theorem tourBlocks_prune (G F₀ : MGraph) (ρ : Rotation G)
    (F H : MGraph) (hF : F.IsForest) (hH : H.IsForest) (hsub : F.IsSubgraph H)
    (v : ℕ) (xs : List End)
    (hkeep : ∀ x : End, x.1 ∈ F.E → F.Connected v (F.src x) → x.1 ∈ H.E) :
    tourBlocks G F₀ ρ F hF v xs = tourBlocks G F₀ ρ H hH v xs := by
  rw [tourBlocks.eq_def G F₀ ρ F, tourBlocks.eq_def G F₀ ρ H]
  apply List.flatMap_congr
  intro x _
  by_cases hopen : x.1 ∉ F₀.E
  · simp [hopen]
  by_cases ha : x.1 ∈ F.E ∧ F.src x = v
  · have hxH := hkeep x ha.1 (ha.2 ▸ connected_refl F v)
    have hsx : H.src x = v := (src_eq_of_subgraph hsub hxH).trans ha.2
    have hd := dst_eq_of_subgraph hsub hxH
    simp only [hopen, ↓reduceIte, ha, hsx, hxH, and_self, hd]
    apply tourBlocks_prune G F₀ ρ _ _ _ _ (eraseForestEdge_mono hsub x.1)
    intro y hy hc
    have hyF := (Finset.mem_erase.mp hy).2
    have hpath : F.Connected (F.dst x) (F.src y) :=
      connected_of_subgraph (eraseForestEdge_subgraph F x.1) hc
    have hxstep : F.Connected v (F.dst x) := ⟨[x], .cons ha.1 ha.2 (.nil _)⟩
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,
      hkeep y hyF (connected_trans hxstep hpath)⟩
  · have hb : ¬ (x.1 ∈ H.E ∧ H.src x = v) := by
      intro h
      exact ha ⟨hsub.2.1 h.1, (src_eq_of_subgraph hsub h.1).symm.trans h.2⟩
    simp [hopen, ha, hb]
termination_by (compOf F v).card
decreasing_by
  rw [← ha.2]
  exact branch_card_lt hF ha.1

private theorem same_edge_at_source {F : MGraph} (hF : F.IsForest) {x y : End}
    (hx : x.1 ∈ F.E) (he : x.1 = y.1) (hs : F.src x = F.src y) : x = y := by
  obtain ⟨e, b⟩ := x
  obtain ⟨f, c⟩ := y
  change e = f at he
  subst f
  have hn := isForest_no_selfLoop hF hx
  cases b <;> cases c <;> simp_all [MGraph.src]

private theorem erase_afterEnd_eq {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (hsub : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    tourBlocks G F ρ F hF (F.src x) (afterEnd x (ρ.order (F.src x))) =
    tourBlocks G F ρ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.src x)
      (afterEnd x (ρ.order (F.src x))) := by
  have hxρ : x ∈ ρ.order (F.src x) :=
    (ρ.mem_order _ _).mpr ⟨hsub.2.1 hx, (src_eq_of_subgraph hsub hx).symm⟩
  have hperm := afterEnd_perm_erase hxρ (ρ.nodup _)
  rw [tourBlocks.eq_def G F ρ F, tourBlocks.eq_def G F ρ (eraseForestEdge F x.1)]
  apply List.flatMap_congr
  intro y hy
  have hyx : y ≠ x := by
    intro he
    subst y
    exact (ρ.nodup _).not_mem_erase (hperm.mem_iff.mp hy)
  by_cases hyF : y.1 ∈ F.E
  · have hys := (src_eq_of_subgraph hsub hyF).trans
      ((ρ.mem_order _ _).mp (List.mem_of_mem_erase (hperm.mem_iff.mp hy))).2
    have hye : y.1 ≠ x.1 := fun he => hyx (same_edge_at_source hF hyF he hys)
    have hyF' : y.1 ∈ (eraseForestEdge F x.1).E := Finset.mem_erase.mpr ⟨hye, hyF⟩
    have hykeep : (eraseForestEdge F x.1).src y = F.src x := hys
    have hdst : (eraseForestEdge F x.1).dst y = F.dst y := rfl
    simp only [hyF, hyF', hys, hykeep, hdst, not_true_eq_false, ↓reduceIte, and_self]
    have hss : (eraseForestEdge F y.1).IsSubgraph
        (eraseForestEdge (eraseForestEdge F x.1) y.1) :=
      eraseForestEdge_mono (eraseForestEdge_subgraph F x.1) _
    apply tourBlocks_prune G F ρ _ _ _ _ hss
    intro z hz hc
    obtain ⟨hzy, hzF⟩ := Finset.mem_erase.mp hz
    refine Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨?_, hzF⟩⟩
    intro hzx
    have hzends : F.src z = F.src x ∨ F.src z = F.dst x := by
      obtain ⟨e, b⟩ := z
      obtain ⟨f, c⟩ := x
      change e = f at hzx
      subst f
      cases b <;> cases c <;> simp [MGraph.src, MGraph.dst]
    change (eraseForestEdge F y.1).Connected (F.dst y) (F.src z) at hc
    rcases hzends with hs | hs
    · exact not_connected_eraseForestEdge hF hyF
        (connected_symm (by simpa only [hs, hys] using hc))
    · have hbranch : (eraseForestEdge F y.1).Connected (F.dst y) (F.dst x) := by
        simpa only [hs] using hc
      exact hyx (branch_unique hF hyF hx hys hbranch
        (connected_refl (eraseForestEdge F x.1) (F.dst x)))
  · have hyF' : y.1 ∉ (eraseForestEdge F x.1).E :=
      fun h => hyF (Finset.mem_erase.mp h).2
    simp [hyF]

/-- Expanding blocks takes rotations of the index list to rotations of the concatenation. -/
theorem isRotated_flatMap {α β : Type*} {xs ys : List α} (h : xs.IsRotated ys)
    (f : α → List β) : (xs.flatMap f).IsRotated (ys.flatMap f) := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn, List.flatMap_append]
  have he : xs.flatMap f = (xs.take n).flatMap f ++ (xs.drop n).flatMap f := by
    rw [← List.flatMap_append, List.take_append_drop]
  conv_lhs => rw [he]
  exact List.isRotated_append

private theorem tourBlocks_rotate (G F₀ : MGraph) (ρ : Rotation G) (F : MGraph)
    (hF : F.IsForest) (v : ℕ) {xs ys : List End} (h : xs.IsRotated ys) :
    (tourBlocks G F₀ ρ F hF v xs).IsRotated (tourBlocks G F₀ ρ F hF v ys) := by
  rw [tourBlocks.eq_def G F₀ ρ F hF v xs, tourBlocks.eq_def G F₀ ρ F hF v ys]
  exact isRotated_flatMap h _

private theorem dst_flip (F : MGraph) (x : End) : F.dst x.flip = F.src x := by
  cases x with
  | mk e b => cases b <;> rfl

/-- Starting at a forest end separates the tour into the two branch blocks. -/
theorem tour_at_forest_end {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (hsub : G.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    (tour ρ hF (F.src x)).IsRotated (branch ρ hF x ++ branch ρ hF x.flip) := by
  have hxρ : x ∈ ρ.order (F.src x) :=
    (ρ.mem_order _ _).mpr ⟨hsub.2.1 hx, (src_eq_of_subgraph hsub hx).symm⟩
  have hrot : (ρ.order (F.src x)).IsRotated (x :: afterEnd x (ρ.order (F.src x))) := by
    have hn := ρ.nodup (F.src x)
    obtain ⟨pre, rest, h⟩ := List.mem_iff_append.mp hxρ
    rw [h] at hn ⊢
    have hnot : x ∉ pre := by
      intro hm
      exact (List.nodup_append.mp hn).2.2 x hm x (by simp) rfl
    rw [afterEnd_of_append x pre rest hnot]
    exact List.isRotated_append (l := pre) (l' := x :: rest)
  have hstep := tourBlocks_rotate G F ρ F hF (F.src x) hrot
  refine hstep.trans ?_
  rw [tourBlocks.eq_def G F ρ F hF (F.src x) (x :: _)]
  simp only [List.flatMap_cons, hx, not_true_eq_false, ↓reduceIte, eq_self, and_self]
  rw [← tourBlocks.eq_def G F ρ F hF (F.src x) (afterEnd x (ρ.order (F.src x))),
    erase_afterEnd_eq ρ hF hsub hx]
  have hf : End.flip (End.flip x) = x := by
    obtain ⟨e, b⟩ := x
    cases b <;> rfl
  simp only [branch, dst_flip, hf]
  exact List.IsRotated.refl _

/-- Moving the start across a forest edge swaps the two branch blocks.
Following a forest walk proves start independence. -/
theorem tour_isRotated_of_connected {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (hsub : G.IsSubgraph F) {u v : ℕ} (h : F.Connected u v) :
    (tour ρ hF u).IsRotated (tour ρ hF v) := by
  obtain ⟨P, hp⟩ := h
  induction hp with
  | nil u => exact List.IsRotated.refl _
  | @cons u v x P hx hs _ ih =>
    have ha := tour_at_forest_end ρ hF hsub hx
    have hb := tour_at_forest_end ρ hF hsub (x := End.flip x) hx
    have hf : End.flip (End.flip x) = x := by
      obtain ⟨e, b⟩ := x
      cases b <;> rfl
    rw [hs] at ha
    rw [src_flip, hf] at hb
    exact ha.trans (List.isRotated_append.trans (hb.symm.trans ih))


/-- The old open ends on the far side of a forest cut form an arc. -/
theorem cut_old_arc {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V)
    {u : ℕ} {x : End} (hx : x.1 ∈ F.E) (hu : F.Connected u (F.src x)) :
    IsArc (fun z => (branch ρ hF x).contains z) (tour ρ hF u) := by
  have hrot := (tour_isRotated_of_connected ρ hF hsub hu).trans
    (tour_at_forest_end ρ hF hsub hx)
  refine ⟨branch ρ hF x, branch ρ hF x.flip, hrot, ?_, ?_⟩
  · intro z hz
    exact List.contains_iff_mem.mpr hz
  · intro z hz
    have hfar := ((branch_spec ρ hG hF hsub hV (x := x.flip) hx).2 z).mp hz
    rw [dst_flip] at hfar
    have hn : z ∉ branch ρ hF x := by
      intro hm
      have hnear := ((branch_spec ρ hG hF hsub hV hx).2 z).mp hm
      exact not_connected_eraseForestEdge hF hx
        (connected_trans hfar.2.2 (connected_symm hnear.2.2))
    exact Bool.eq_false_iff.mpr (fun h => hn (List.contains_iff_mem.mp h))


private theorem afterEnd_anchor {x : End} {xs : List End} (h : x ∈ xs) (hn : xs.Nodup) :
    xs.IsRotated (x :: afterEnd x xs) := by
  obtain ⟨pre, rest, rfl⟩ := List.mem_iff_append.mp h
  have hnot : x ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 x hm x (by simp) rfl
  rw [afterEnd_of_append x pre rest hnot]
  exact List.isRotated_append (l := pre) (l' := x :: rest)

private theorem anchored_isRotated_eq {x : End} {xs ys : List End}
    (h : (x :: xs).IsRotated (x :: ys)) (hn : (x :: xs).Nodup) : xs = ys := by
  obtain ⟨n, hrot⟩ := h
  have hpos : 0 < (x :: xs).length := by simp
  rw [← List.rotate_mod] at hrot
  let i := n % (x :: xs).length
  have hi : i < (x :: xs).length := Nat.mod_lt _ hpos
  have hh := congrArg List.head? hrot
  rw [List.head?_rotate hi, List.getElem?_eq_getElem hi] at hh
  have he : (x :: xs)[i] = (x :: xs)[0] := Option.some.inj hh
  have hi0 := hn.getElem_inj_iff.mp he
  change (x :: xs).rotate i = x :: ys at hrot
  rw [hi0, List.rotate_zero] at hrot
  exact (List.cons.inj hrot).2

private theorem afterEnd_filter_eq {x : End} {xs ys : List End} (q : End → Bool)
    (hx : x ∈ xs) (hy : x ∈ ys) (hxs : xs.Nodup) (hys : ys.Nodup)
    (hq : q x = true) (h : (xs.filter q).IsRotated (ys.filter q)) :
    (afterEnd x xs).filter q = (afterEnd x ys).filter q := by
  have ha := isRotated_filter q (afterEnd_anchor hx hxs)
  have hb := isRotated_filter q (afterEnd_anchor hy hys)
  rw [List.filter_cons_of_pos hq] at ha hb
  exact anchored_isRotated_eq (ha.symm.trans (h.trans hb))
    (ha.perm.nodup_iff.mp (hxs.filter q))

private theorem filter_flatMap_eq {α β : Type*} (p : α → Bool) (q : β → Bool)
    (f : α → List β) (xs : List α) (h : ∀ x, p x = false → (f x).filter q = []) :
    (xs.flatMap f).filter q = (xs.filter p).flatMap (fun x => (f x).filter q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp [List.flatMap_cons, hx, h, ih]

private theorem tourBlocks_filter_isRotated {G H F₀ F₁ : MGraph}
    (ρ : Rotation G) (σ : Rotation H) (q : End → Bool)
    (hbase : ∀ x : End, q x = true → (x.1 ∈ F₀.E ↔ x.1 ∈ F₁.E))
    (F : MGraph) (hF : F.IsForest) (hG : G.IsSubgraph F) (hH : H.IsSubgraph F)
    (h₀ : F.E ⊆ F₀.E) (h₁ : F.E ⊆ F₁.E)
    (hq : ∀ x : End, x.1 ∈ F.E → q x = true)
    (v : ℕ) (xs ys : List End)
    (horder : ∀ w, F.Connected v w → ((ρ.order w).filter q).IsRotated ((σ.order w).filter q)) :
    ∃ f : End → List End,
      (tourBlocks G F₀ ρ F hF v xs).filter q = (xs.filter q).flatMap f ∧
      (tourBlocks H F₁ σ F hF v ys).filter q = (ys.filter q).flatMap f := by
  let block (J B : MGraph) (τ : Rotation J) (x : End) :=
    if x.1 ∉ B.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      tourBlocks J B τ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (τ.order (F.dst x)))
    else []
  have heq (J B : MGraph) (τ : Rotation J) (zs : List End) :
      (tourBlocks J B τ F hF v zs).filter q =
        (zs.filter q).flatMap (fun x => (block J B τ x).filter q) := by
    rw [tourBlocks.eq_def J B τ F hF v zs]
    apply filter_flatMap_eq q q (block J B τ) zs
    intro x hx
    have hn : x.1 ∉ F.E := by
      intro he
      rw [hq x he] at hx
      contradiction
    by_cases hxB : x.1 ∈ B.E <;> simp [block, hn, hx, hxB]
  refine ⟨fun x => (block G F₀ ρ x).filter q, heq G F₀ ρ xs, ?_⟩
  rw [heq H F₁ σ]
  apply List.flatMap_congr
  intro x hx
  by_cases ha : x.1 ∈ F.E ∧ F.src x = v
  · have hsd : F.src x.flip = F.dst x := src_flip F x
    have hxρ : x.flip ∈ ρ.order (F.dst x) :=
      (ρ.mem_order _ _).mpr ⟨hG.2.1 ha.1, (src_eq_of_subgraph (x := x.flip) hG ha.1).symm.trans hsd⟩
    have hxσ : x.flip ∈ σ.order (F.dst x) :=
      (σ.mem_order _ _).mpr ⟨hH.2.1 ha.1, (src_eq_of_subgraph (x := x.flip) hH ha.1).symm.trans hsd⟩
    have hstep : F.Connected v (F.dst x) := ⟨[x], .cons ha.1 ha.2 (.nil _)⟩
    have hr := afterEnd_filter_eq q hxρ hxσ (ρ.nodup _) (σ.nodup _) (hq x.flip ha.1)
      (horder _ hstep)
    have hsub' (J : MGraph) (hsub : J.IsSubgraph F) : J.IsSubgraph (eraseForestEdge F x.1) :=
      ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
        fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
    obtain ⟨f, hf₁, hf₂⟩ := tourBlocks_filter_isRotated ρ σ q hbase _
      (isForest_eraseEdge hF x.1) (hsub' G hG) (hsub' H hH)
      (fun _ hz => h₀ (Finset.mem_erase.mp hz).2) (fun _ hz => h₁ (Finset.mem_erase.mp hz).2)
      (fun z hz => hq z (Finset.mem_erase.mp hz).2)
      (F.dst x) (afterEnd x.flip (ρ.order (F.dst x))) (afterEnd x.flip (σ.order (F.dst x)))
      (fun w hw => horder w (connected_trans hstep
        (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hw)))
    simp only [block, h₀ ha.1, h₁ ha.1, ha, not_true_eq_false, and_self, ↓reduceIte, ↓reduceDIte]
    rw [hf₁, hf₂, hr]
  · have hh := hbase x (List.mem_filter.mp hx).2
    simp [block, ha, hh]
termination_by (compOf F v).card
decreasing_by
  rw [← ha.2]
  exact branch_card_lt hF ha.1

/-- Insertion or deletion of open ends preserves the tour on surviving
ends. The restriction retains every forest end
at the vertices even though the tours themselves skip those ends. -/
theorem tour_filter_isRotated {G H F : MGraph} (ρ : Rotation G) (σ : Rotation H)
    (hF : F.IsForest) (hG : G.IsSubgraph F) (hH : H.IsSubgraph F)
    (q : End → Bool) (hq : ∀ x : End, x.1 ∈ F.E → q x = true)
    (horder : ∀ v, ((ρ.order v).filter q).IsRotated ((σ.order v).filter q)) (v : ℕ) :
    ((tour ρ hF v).filter q).IsRotated ((tour σ hF v).filter q) := by
  obtain ⟨f, h₁, h₂⟩ := tourBlocks_filter_isRotated (F₀ := F) (F₁ := F)
    ρ σ q (fun _ _ => Iff.rfl) F hF hG hH Finset.Subset.rfl Finset.Subset.rfl hq
    v (ρ.order v) (σ.order v) (fun w _ => horder w)
  unfold tour
  rw [h₁, h₂]
  exact isRotated_flatMap (horder v) f


/-- After cutting a forest edge, the tour on its far side, with the cut
edge omitted, is the restriction of the old tour to the branch's open ends.
Apply this with either end of the cut edge. -/
theorem tour_cut_restrict {G H F : MGraph} (ρ : Rotation G) (σ : Rotation H)
    (hG : G.IsValid) (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V)
    {u : ℕ} {x : End} (hx : x.1 ∈ F.E) (hu : F.Connected u (F.src x))
    (hsub' : H.IsSubgraph (eraseForestEdge F x.1))
    (horder : ∀ v, ((ρ.order v).filter fun z => z.1 != x.1).IsRotated
      ((σ.order v).filter fun z => z.1 != x.1)) :
    ((tour σ (isForest_eraseEdge hF x.1) (F.dst x)).filter fun z => z.1 != x.1).IsRotated
      ((tour ρ hF u).filter fun z => (branch ρ hF x).contains z) := by
  let C := eraseForestEdge F x.1
  let q : End → Bool := fun z => z.1 != x.1
  have hGC : G.IsSubgraph C :=
    ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
      fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
  have hkeep : ∀ z : End, z.1 ∈ C.E → q z = true :=
    fun _ hz => bne_iff_ne.mpr (Finset.mem_erase.mp hz).1
  have hbase : ∀ z : End, q z = true → (z.1 ∈ F.E ↔ z.1 ∈ C.E) := by
    intro z hz
    exact ⟨fun he => Finset.mem_erase.mpr ⟨bne_iff_ne.mp hz, he⟩, fun he => (Finset.mem_erase.mp he).2⟩
  have hflip : x.flip ∈ ρ.order (F.dst x) :=
    (ρ.mem_order _ _).mpr ⟨hsub.2.1 hx,
      (src_eq_of_subgraph (x := x.flip) hsub hx).symm.trans (src_flip F x)⟩
  have ha := isRotated_filter q (afterEnd_anchor hflip (ρ.nodup _))
  rw [List.filter_cons_of_neg (show ¬ q x.flip = true from by simp [q, End.flip])] at ha
  obtain ⟨f, hf₁, hf₂⟩ := tourBlocks_filter_isRotated (F₀ := F) (F₁ := C)
    ρ σ q hbase C (isForest_eraseEdge hF x.1) hGC hsub'
    (Finset.erase_subset _ _) Finset.Subset.rfl hkeep (F.dst x)
    (afterEnd x.flip (ρ.order (F.dst x))) (σ.order (F.dst x)) (fun w _ => horder w)
  have hc : (branch ρ hF x).filter q = branch ρ hF x := by
    apply List.filter_eq_self.mpr
    intro z hz
    have hopen := ((branch_spec ρ hG hF hsub hV hx).2 z |>.mp hz).2.1
    exact bne_iff_ne.mpr fun he => hopen (he.symm ▸ hx)
  have hbranch : ((tour σ (isForest_eraseEdge hF x.1) (F.dst x)).filter q).IsRotated
      (branch ρ hF x) := by
    change ((tourBlocks H C σ C _ (F.dst x) (σ.order (F.dst x))).filter q).IsRotated _
    rw [hf₂, ← hc]
    change _ ~r (tourBlocks G F ρ C _ (F.dst x) (afterEnd x.flip (ρ.order (F.dst x)))).filter q
    rw [hf₁]
    exact isRotated_flatMap ((horder _).symm.trans ha) f
  have hparts := (tour_isRotated_of_connected ρ hF hsub hu).trans
    (tour_at_forest_end ρ hF hsub hx)
  let p : End → Bool := fun z => (branch ρ hF x).contains z
  have hp := isRotated_filter p hparts
  have hp₁ : (branch ρ hF x).filter p = branch ρ hF x :=
    List.filter_eq_self.mpr fun _ hz => List.contains_iff_mem.mpr hz
  have hp₂ : (branch ρ hF x.flip).filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro z hz hpz
    have ho := ((branch_spec ρ hG hF hsub hV (x := x.flip) hx).2 z).mp hz
    rw [dst_flip] at ho
    have hm := ((branch_spec ρ hG hF hsub hV hx).2 z).mp (List.contains_iff_mem.mp hpz)
    exact not_connected_eraseForestEdge hF hx
      (connected_trans ho.2.2 (connected_symm hm.2.2))
  rw [List.filter_append, hp₁, hp₂, List.append_nil] at hp
  exact hbranch.trans hp.symm


/-- The block of an incident end is either the end itself or the branch
behind it. -/
noncomputable def tourBlock {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest) (x : End) :
    List End := if x.1 ∈ F.E then branch ρ hF x else [x]

theorem tour_eq_flatMap {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (hsub : G.IsSubgraph F) (v : ℕ) :
    tour ρ hF v = (ρ.order v).flatMap (tourBlock ρ hF) := by
  rw [tour, tourBlocks.eq_def]
  apply List.flatMap_congr
  intro x hx
  by_cases he : x.1 ∈ F.E
  · have hs := (src_eq_of_subgraph hsub he).trans ((ρ.mem_order v x).mp hx).2
    simp [tourBlock, branch, he, hs]
  · simp [tourBlock, he]

/-- The open ends moved by choosing whole tour blocks. -/
noncomputable def movedTourEnds {G F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (v : ℕ) (moved : End → Bool) : List End :=
  ((ρ.order v).filter moved).flatMap (tourBlock ρ hF)

private theorem block_side {α β : Type*} [BEq β] [LawfulBEq β]
    (p : α → Bool) (block : α → List β) (xs : List α)
    (hn : (xs.flatMap block).Nodup) :
    ∀ i ∈ xs, ∀ z ∈ block i, ((xs.filter p).flatMap block).contains z = p i := by
  have hp := (List.nodup_flatMap.mp hn).2
  let r : α → α → Prop := fun i j => i ≠ j → List.Disjoint (block i) (block j)
  let : Std.Symm r := ⟨fun _ _ h hij => (h hij.symm).symm⟩
  have hs : xs.Pairwise r := by
    apply hp.imp
    intro i j h _
    exact h
  have hd := hs.forall_of_forall (fun _ _ hn => (hn rfl).elim)
  intro i hi z hz
  cases hm : p i
  · apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨j, hj, hzj⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp hh)
    obtain ⟨hjs, hjp⟩ := List.mem_filter.mp hj
    have hne : i ≠ j := by
      intro he
      rw [← he, hm] at hjp
      contradiction
    exact List.disjoint_left.mp (hd hi hjs hne) hz hzj
  · exact List.contains_iff_mem.mpr (List.mem_flatMap_of_mem (List.mem_filter.mpr ⟨hi, hm⟩) hz)

/-- Moving whole blocks increases the boundary count by at most the number
of changes at the split vertex. -/
theorem tour_split_boundary_le {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V) (v : ℕ)
    (moved : End → Bool) :
    cycBdry (fun z => (movedTourEnds ρ hF v moved).contains z) (tour ρ hF v) ≤
      cycBdry moved (ρ.order v) := by
  have hnodup := (tour_spec ρ hG hF hsub hV v).1
  rw [tour_eq_flatMap ρ hF hsub] at hnodup ⊢
  exact cycBdry_blocks moved _ (tourBlock ρ hF) _ (block_side moved (tourBlock ρ hF) _ hnodup)

/-- Restricting the tour to one side keeps the concatenation of that side's
blocks in rotation order. -/
theorem tour_split_filter {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V) (v : ℕ)
    (moved : End → Bool) :
    (tour ρ hF v).filter (fun z => (movedTourEnds ρ hF v moved).contains z) =
      movedTourEnds ρ hF v moved := by
  have hn := (tour_spec ρ hG hF hsub hV v).1
  rw [tour_eq_flatMap ρ hF hsub] at hn ⊢
  let p : End → Bool := fun z => (movedTourEnds ρ hF v moved).contains z
  have hp := block_side moved (tourBlock ρ hF) (ρ.order v) hn
  have h (xs : List End) (hs : xs ⊆ ρ.order v) :
      ((xs.flatMap (tourBlock ρ hF)).filter p) =
        (xs.filter moved).flatMap (tourBlock ρ hF) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx := hp x (hs List.mem_cons_self)
      have hxs : xs ⊆ ρ.order v := fun _ hz => hs (List.mem_cons_of_mem x hz)
      rw [List.flatMap_cons, List.filter_append, ih hxs]
      cases hm : moved x
      · have hnil : (tourBlock ρ hF x).filter p = [] :=
          List.filter_eq_nil_iff.mpr fun z hz => by simp [show p z = false from (hx z hz).trans hm]
        simp [hnil, hm]
      · have hself : (tourBlock ρ hF x).filter p = tourBlock ρ hF x :=
          List.filter_eq_self.mpr fun z hz => (hx z hz).trans hm
        simp [hself, hm]
  exact h _ (fun _ hz => hz)


/-- A branch block depends on the reachable forest edges and the rotations
there. Edges outside the branch may change. -/
theorem branch_eq_of_common {G H F F' J : MGraph}
    (ρ : Rotation G) (σ : Rotation H) (hF : F.IsForest) (hF' : F'.IsForest)
    (hJ : J.IsForest) (hG : G.IsSubgraph F) (hH : H.IsSubgraph F')
    (hGJ : G.IsSubgraph J) (hHJ : H.IsSubgraph J) {x : End}
    (hx : x.1 ∈ F.E) (hE : F'.E = F.E) (hd : F'.dst x = F.dst x)
    (hsub : (eraseForestEdge F x.1).IsSubgraph J)
    (hsub' : (eraseForestEdge F' x.1).IsSubgraph J)
    (hkeep : ∀ y : End, y.1 ∈ (eraseForestEdge F x.1).E →
      (eraseForestEdge F x.1).Connected (F.dst x) (F.src y) → y.1 ∈ J.E)
    (hkeep' : ∀ y : End, y.1 ∈ (eraseForestEdge F' x.1).E →
      (eraseForestEdge F' x.1).Connected (F'.dst x) (F'.src y) → y.1 ∈ J.E)
    (horder : ∀ v, J.Connected (F.dst x) v → (ρ.order v).IsRotated (σ.order v)) :
    branch ρ hF x = branch σ hF' x := by
  have hx' : x.1 ∈ F'.E := hE ▸ hx
  have hxρ : x.flip ∈ ρ.order (F.dst x) :=
    (ρ.mem_order _ _).mpr ⟨hG.2.1 hx, (src_eq_of_subgraph (x := x.flip) hG hx).symm.trans
      (src_flip F x)⟩
  have hxσ : x.flip ∈ σ.order (F.dst x) :=
    (σ.mem_order _ _).mpr ⟨hH.2.1 hx', (src_eq_of_subgraph (x := x.flip) hH hx').symm.trans
      ((src_flip F' x).trans hd)⟩
  let yes : End → Bool := fun _ => true
  have hor : ∀ v, J.Connected (F.dst x) v →
      ((ρ.order v).filter yes).IsRotated ((σ.order v).filter yes) := by
    intro v hv
    simpa [yes] using horder v hv
  have ha := afterEnd_filter_eq yes hxρ hxσ (ρ.nodup _) (σ.nodup _) rfl
    (hor _ (connected_refl _ _))
  obtain ⟨f, hleft, hright⟩ := tourBlocks_filter_isRotated (F₀ := F) (F₁ := F') ρ σ
    yes (fun _ _ => by rw [hE]) J hJ hGJ hHJ
    (fun _ he => (Finset.mem_erase.mp (hsub.2.1 he)).2)
    (fun _ he => (Finset.mem_erase.mp (hsub'.2.1 he)).2)
    (fun _ _ => rfl) (F.dst x) (afterEnd x.flip (ρ.order (F.dst x)))
    (afterEnd x.flip (σ.order (F.dst x))) hor
  have hp := tourBlocks_prune G F ρ _ _ (isForest_eraseEdge hF x.1) hJ hsub _
    (afterEnd x.flip (ρ.order (F.dst x))) hkeep
  have hp' := tourBlocks_prune H F' σ _ _ (isForest_eraseEdge hF' x.1) hJ hsub' _
    (afterEnd x.flip (σ.order (F'.dst x))) hkeep'
  unfold branch
  rw [hp, hp', hd]
  rw [ha] at hleft
  have hh := hleft.trans hright.symm
  simpa [yes] using hh


/-- Cutting a forest edge outside a component preserves that component's
tour. The rotations are compared after discarding
the cut edge. -/
theorem tour_cut_untouched {G H F : MGraph} (ρ : Rotation G) (σ : Rotation H)
    (hG : G.IsValid) (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V)
    {u : ℕ} {x : End} (hx : x.1 ∈ F.E) (hu : ¬ F.Connected u (F.src x))
    (hsub' : H.IsSubgraph (eraseForestEdge F x.1))
    (horder : ∀ v, ((ρ.order v).filter fun z => z.1 != x.1).IsRotated
      ((σ.order v).filter fun z => z.1 != x.1)) :
    ((tour σ (isForest_eraseEdge hF x.1) u).filter fun z => z.1 != x.1).IsRotated (tour ρ hF u) := by
  let C := eraseForestEdge F x.1
  let q : End → Bool := fun z => z.1 != x.1
  have hGC : G.IsSubgraph C :=
    ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
      fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
  have hkeep : ∀ z : End, z.1 ∈ C.E → q z = true :=
    fun _ hz => bne_iff_ne.mpr (Finset.mem_erase.mp hz).1
  have hbase : ∀ z : End, q z = true → (z.1 ∈ F.E ↔ z.1 ∈ C.E) :=
    fun _ hz => ⟨fun he => Finset.mem_erase.mpr ⟨bne_iff_ne.mp hz, he⟩,
      fun he => (Finset.mem_erase.mp he).2⟩
  have hp : tour ρ hF u = tourBlocks G F ρ C (isForest_eraseEdge hF x.1) u (ρ.order u) := by
    apply tourBlocks_prune G F ρ F C hF _ (eraseForestEdge_subgraph F x.1)
    intro y hy hconn
    refine Finset.mem_erase.mpr ⟨?_, hy⟩
    intro he
    have hh : F.src y = F.src x ∨ F.src y = F.dst x := by
      obtain ⟨e, b⟩ := x
      obtain ⟨f, c⟩ := y
      change f = e at he
      subst f
      cases b <;> cases c <;> simp [MGraph.src, MGraph.dst]
    rcases hh with hh | hh
    · exact hu (hh ▸ hconn)
    · have hstep : F.Connected (F.src x) (F.dst x) := ⟨[x], .cons hx rfl (.nil _)⟩
      exact hu (connected_trans (hh ▸ hconn) (connected_symm hstep))
  have hfilter : (tour ρ hF u).filter q = tour ρ hF u := by
    apply List.filter_eq_self.mpr
    intro z hz
    have hn := ((tour_spec ρ hG hF hsub hV u).2 z |>.mp hz).2.1
    exact bne_iff_ne.mpr fun he => hn (he.symm ▸ hx)
  obtain ⟨f, hf₁, hf₂⟩ := tourBlocks_filter_isRotated (F₀ := F) (F₁ := C)
    ρ σ q hbase C (isForest_eraseEdge hF x.1) hGC hsub' (Finset.erase_subset _ _)
    Finset.Subset.rfl hkeep u (ρ.order u) (σ.order u) (fun w _ => horder w)
  rw [← hfilter, hp, hf₁]
  change ((tourBlocks H C σ C _ u (σ.order u)).filter q).IsRotated _
  rw [hf₂]
  exact isRotated_flatMap (horder u).symm f


/-- Within the original tour, the two branch blocks of a cut are
complements. -/
theorem cut_branch_complement {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V)
    {u : ℕ} {x : End} (hx : x.1 ∈ F.E) (hu : F.Connected u (F.src x))
    {z : End} (hz : z ∈ tour ρ hF u) :
    (branch ρ hF x.flip).contains z = !(branch ρ hF x).contains z := by
  have hrot := (tour_isRotated_of_connected ρ hF hsub hu).trans
    (tour_at_forest_end ρ hF hsub hx)
  have hn := (List.nodup_append.mp (hrot.perm.nodup_iff.mp (tour_spec ρ hG hF hsub hV u).1)).2.2
  have hdisj : ¬ (z ∈ branch ρ hF x ∧ z ∈ branch ρ hF x.flip) :=
    fun h => hn z h.1 z h.2 rfl
  have hmem := List.mem_append.mp (hrot.perm.mem_iff.mp hz)
  by_cases h : z ∈ branch ρ hF x
  · have hm : (branch ρ hF x).contains z = true := List.contains_iff_mem.mpr h
    have hn' : (branch ρ hF x.flip).contains z = false :=
      Bool.eq_false_iff.mpr fun hc => hdisj ⟨h, List.contains_iff_mem.mp hc⟩
    simp only [hm, hn', Bool.not_true]
  · have hm : (branch ρ hF x).contains z = false :=
      Bool.eq_false_iff.mpr fun hc => h (List.contains_iff_mem.mp hc)
    have hh : (branch ρ hF x.flip).contains z = true :=
      List.contains_iff_mem.mpr (hmem.resolve_left h)
    simp only [hm, hh, Bool.not_false]


/-- Equal forest graphs give the same tour. -/
theorem tour_congr_forest {G F H : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (hH : H.IsForest) (h : F = H) (v : ℕ) : tour ρ hF v = tour ρ hH v := by
  subst H
  rfl


/-- Tours agree if their reachable forest edges and rotations agree. -/
theorem tour_isRotated_of_common {G H F F' J : MGraph}
    (ρ : Rotation G) (σ : Rotation H) (hF : F.IsForest) (hF' : F'.IsForest)
    (hJ : J.IsForest) (hGJ : G.IsSubgraph J) (hHJ : H.IsSubgraph J)
    (hE : F'.E = F.E) (hsub : F.IsSubgraph J) (hsub' : F'.IsSubgraph J) (v : ℕ)
    (hkeep : ∀ y : End, y.1 ∈ F.E → F.Connected v (F.src y) → y.1 ∈ J.E)
    (hkeep' : ∀ y : End, y.1 ∈ F'.E → F'.Connected v (F'.src y) → y.1 ∈ J.E)
    (horder : ∀ w, J.Connected v w → (ρ.order w).IsRotated (σ.order w)) :
    (tour ρ hF v).IsRotated (tour σ hF' v) := by
  let yes : End → Bool := fun _ => true
  have ho : ∀ w, J.Connected v w →
      ((ρ.order w).filter yes).IsRotated ((σ.order w).filter yes) := by
    intro w hw
    simpa [yes] using horder w hw
  obtain ⟨f, h₁, h₂⟩ := tourBlocks_filter_isRotated (F₀ := F) (F₁ := F') ρ σ
    yes (fun _ _ => by rw [hE]) J hJ hGJ hHJ hsub.2.1 hsub'.2.1 (fun _ _ => rfl)
    v (ρ.order v) (σ.order v) ho
  have hr := isRotated_flatMap (ho v (connected_refl _ _)) f
  rw [← h₁, ← h₂] at hr
  have hp := tourBlocks_prune G F ρ _ _ hF hJ hsub v (ρ.order v) hkeep
  have hp' := tourBlocks_prune H F' σ _ _ hF' hJ hsub' v (σ.order v) hkeep'
  rw [← hp, ← hp'] at hr
  simpa [yes, tour] using hr

/-- The kept and moved block unions are complements in the original tour. -/
theorem movedTourEnds_complement {G F : MGraph} (ρ : Rotation G) (hG : G.IsValid)
    (hF : F.IsForest) (hsub : G.IsSubgraph F) (hV : F.V = G.V) {v : ℕ}
    (p : End → Bool) {z : End} (hz : z ∈ tour ρ hF v) :
    (movedTourEnds ρ hF v (fun x => !(p x))).contains z = !(movedTourEnds ρ hF v p).contains z := by
  have hn := (tour_spec ρ hG hF hsub hV v).1
  rw [tour_eq_flatMap ρ hF hsub] at hn hz
  obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hz
  exact (block_side (fun x => !(p x)) (tourBlock ρ hF) (ρ.order v) hn x hx z hz).trans
    (congrArg Bool.not (block_side p (tourBlock ρ hF) (ρ.order v) hn x hx z hz)).symm

end MinCostFlow.Bundle
