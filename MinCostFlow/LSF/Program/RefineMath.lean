module

public import MinCostFlow.LSF.Program.FForestMath
public import MinCostFlow.LSF.Components

/-!
# The pieces of `refineDecomp` on vertex indices

`refineDecomp W_T F₀` keeps the sets `W ∩ C` (`W ∈ W_T`, `C` a component of `F₀`) that hold an
edge of `F₀`. This file describes these pieces through the tree-edge indices.

A non-root index `x` is *kept* when its parent edge is an edge of `F₀` (`own (pe x) = 0`). Its
*key* is the pair of its label `lab x` (which names the piece of `W_T` that holds its parent
edge) and its root `rt x` (which names its component of `F₀`).

* `cut_step`: two vertices of `W ∩ C` are joined inside `W ∩ C` by the tree path, so each vertex
  of `W ∩ C` with another vertex in it is an end of an edge of `F₀` inside `W ∩ C`. The reason is
  that both sets are path convex in `T₀`: `W` by assumption, `C` because an `F₀` path is the
  `T₀` path.
* `refine_char`: the pieces of `refineDecomp W_T F₀` are exactly the sets `keyPiece x` (the ends
  of the parent edges of the kept indices with the key of `x`), two kept indices give the same
  piece exactly when their keys are equal, and the `F₀` edges inside `keyPiece x` are the parent
  edges of these indices.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

/-! ## A vertex-level step -/

/-- A vertex `v` of `W ∩ C` with another vertex `b` of `W ∩ C` is an end of an edge of `F` whose
two ends lie in `W ∩ C`. Here `F` is `T` without the edges `D` and `C` is a component of `F`. -/
lemma cut_step {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) {D W : Finset ℕ} {u₀ v b : ℕ}
    (hW : PathConvex T W) (hvW : v ∈ W) (hbW : b ∈ W)
    (hv : v ∈ compOf ({ T with E := T.E \ D } : MGraph) u₀)
    (hb : b ∈ compOf ({ T with E := T.E \ D } : MGraph) u₀) (hvb : v ≠ b) :
    ∃ e ∈ ({ T with E := T.E \ D } : MGraph).E, (T.tail e = v ∨ T.head e = v) ∧
      T.tail e ∈ W ∧ T.head e ∈ W ∧
      T.tail e ∈ compOf ({ T with E := T.E \ D } : MGraph) u₀ ∧
      T.head e ∈ compOf ({ T with E := T.E \ D } : MGraph) u₀ := by
  set F : MGraph := { T with E := T.E \ D } with hF
  obtain ⟨hvV, hu₀v⟩ := mem_compOf_iff.mp hv
  obtain ⟨hbV, hu₀b⟩ := mem_compOf_iff.mp hb
  have hconnT : T.Connected v b := hT.connected hvV hbV
  have hFvb : F.Connected v b := connected_trans (connected_symm hu₀v) hu₀b
  have hdisj := (connected_sdiff_iff_disjoint hT.isForest hconnT).mp hFvb
  have hP := forestPath_isPath hT.isForest hconnT
  obtain ⟨hwalk, -⟩ := hP
  cases hP' : T.forestPath v b with
  | nil =>
    rw [hP'] at hwalk
    cases hwalk
    exact absurd rfl hvb
  | cons x rest =>
    rw [hP'] at hwalk hdisj
    obtain ⟨⟩ | ⟨hxE, hsrc, hrest⟩ := hwalk
    have hxD : x.1 ∉ D := fun hx =>
      Finset.disjoint_left.mp hdisj (by rw [walkEdges_cons]; exact Finset.mem_insert_self _ _) hx
    have hxF : x.1 ∈ F.E := Finset.mem_sdiff.mpr ⟨hxE, hxD⟩
    have hwW : T.dst x ∈ W := hW.2.2 v hvW b hbW _ (by
      rw [hP', walkVertices_cons]
      exact List.mem_cons_of_mem _ (IsWalk_start_mem_walkVertices T _ _))
    have hwV : T.dst x ∈ T.V := hW.2.1 hwW
    -- the two ends of `x.1` are `v` and the next vertex
    have hFends : F.Connected v (T.dst x) := by
      have h1 := connected_of_edge hxF
      rcases x with ⟨e, _ | _⟩
      · simp only [MGraph.src, MGraph.dst, Bool.false_eq_true, if_false] at hsrc ⊢
        rw [← hsrc]; exact connected_symm h1
      · simp only [MGraph.src, MGraph.dst, if_true] at hsrc ⊢
        rw [← hsrc]; exact h1
    have hwC : T.dst x ∈ compOf F u₀ :=
      mem_compOf_iff.mpr ⟨hwV, connected_trans hu₀v hFends⟩
    refine ⟨x.1, hxF, ?_⟩
    rcases x with ⟨e, _ | _⟩
    · simp only [MGraph.src, MGraph.dst, Bool.false_eq_true, if_false] at hsrc hwW hwC ⊢
      exact ⟨Or.inr hsrc, hwW, hsrc ▸ hvW, hwC, hsrc ▸ hv⟩
    · simp only [MGraph.src, MGraph.dst, if_true] at hsrc hwW hwC ⊢
      exact ⟨Or.inl hsrc, hsrc ▸ hvW, hwW, hsrc ▸ hv, hwC⟩

/-! ## The pieces through the kept indices -/

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}
  {R : Finset ℕ} {π inR piv mp own rt : ℕ → ℕ}

/-- The facts about `W_T` and the labels that the refinement uses. -/
structure WLabels (T₀ : MGraph) (vList : List ℕ) (r : ℕ) (W_T : Finset (Finset ℕ))
    (lab : ℕ → ℕ × ℕ) : Prop where
  hconv : ∀ W ∈ W_T, PathConvex T₀ W
  hdisj : ∀ W₁ ∈ W_T, ∀ W₂ ∈ W_T, W₁ ≠ W₂ →
    Disjoint (inducedEdges T₀ W₁) (inducedEdges T₀ W₂)
  hcov : W_T.biUnion (inducedEdges T₀) = T₀.E
  hlab : ∀ x < vList.length, x ≠ r → ∀ x' < vList.length, x' ≠ r →
    (lab x = lab x' ↔ ∃ P ∈ W_T,
      parentEdge T₀ (vList.getD r 0) (vList.getD x 0) ∈ inducedEdges T₀ P ∧
      parentEdge T₀ (vList.getD r 0) (vList.getD x' 0) ∈ inducedEdges T₀ P)

open Classical in
/-- The kept indices with the key of `x`. -/
noncomputable def keyClass (n r : ℕ) (own pe rt : ℕ → ℕ) (lab : ℕ → ℕ × ℕ) (x : ℕ) :
    Finset ℕ :=
  (Finset.range n).filter (fun y => y ≠ r ∧ own (pe y) = 0 ∧ lab y = lab x ∧ rt y = rt x)

/-- The ends of the parent edges of the kept indices with the key of `x`. -/
noncomputable def keyPiece (vList : List ℕ) (r : ℕ) (own pe rt par : ℕ → ℕ)
    (lab : ℕ → ℕ × ℕ) (x : ℕ) : Finset ℕ :=
  (keyClass vList.length r own pe rt lab x).image (fun y => vList.getD y 0) ∪
    (keyClass vList.length r own pe rt lab x).image (fun y => vList.getD (par y) 0)

/-- The two ends of a parent edge, as membership in a set. -/
lemma parentEdge_ends_mem {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V)
    (hne : u ≠ r) (S : Finset ℕ) :
    (T.tail (parentEdge T r u) ∈ S ∧ T.head (parentEdge T r u) ∈ S) ↔
      (u ∈ S ∧ parent T r u ∈ S) := by
  have h := parentEdge_endpoints hT hu hne
  rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact and_comm

/-- An edge of `T₀` is the parent edge of the index of its lower end. -/
lemma edge_child_idx (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {e : ℕ} (he : e ∈ T₀.E) :
    ∃ y < vList.length, y ≠ r ∧ fid (pe y) = e ∧
      ((T₀.tail e = vList.getD y 0 ∧ T₀.head e = vList.getD (par y) 0) ∨
        (T₀.head e = vList.getD y 0 ∧ T₀.tail e = vList.getD (par y) 0)) := by
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < vList.length ∧ vList.getD (vList.idxOf v) 0 = v :=
    fun v hv => ⟨List.idxOf_lt_length_of_mem ((hI.hV v).mp hv), getD_idxOf ((hI.hV v).mp hv)⟩
  have hval := hI.hT.isForest.1 e he
  rcases edge_parent_orientation hI.hT he with ⟨hp, hpe, hne⟩ | ⟨hp, hpe, hne⟩
  · obtain ⟨hyl, hgy⟩ := hidx _ hval.1
    have hyr : vList.idxOf (T₀.tail e) ≠ r := fun h => hne (by rw [← hgy, h])
    obtain ⟨-, -, -, hpar, hpeq⟩ := hI.step hyl hyr
    refine ⟨_, hyl, hyr, ?_, Or.inl ⟨hgy.symm, ?_⟩⟩
    · rw [← hpeq, hgy, hpe]
    · rw [← hpar, hgy, hp]
  · obtain ⟨hyl, hgy⟩ := hidx _ hval.2
    have hyr : vList.idxOf (T₀.head e) ≠ r := fun h => hne (by rw [← hgy, h])
    obtain ⟨-, -, -, hpar, hpeq⟩ := hI.step hyl hyr
    refine ⟨_, hyl, hyr, ?_, Or.inr ⟨hgy.symm, ?_⟩⟩
    · rw [← hpeq, hgy, hpe]
    · rw [← hpar, hgy, hp]

/-! ## The key of an edge -/

section Key

variable (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
  (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt)
include hI h

/-- The parent edge of a kept index is an edge of `F₀`. -/
lemma kept_edge {y : ℕ} (hy : y < vList.length) (hyr : y ≠ r) (ho : own (pe y) = 0) :
    fid (pe y) ∈ (forestGivenRoots T₀ (vList.getD r 0) R π).E ∧
      parentEdge T₀ (vList.getD r 0) (vList.getD y 0) = fid (pe y) ∧
      parent T₀ (vList.getD r 0) (vList.getD y 0) = vList.getD (par y) 0 := by
  obtain ⟨-, hpe, -, hpar, hpeq⟩ := hI.step hy hyr
  refine ⟨?_, hpeq, hpar⟩
  rw [forest_E_eq hI h]
  exact Finset.mem_image.mpr ⟨pe y, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpe, ho⟩, rfl⟩

/-- The ends of the parent edge of a non-root index. -/
lemma kept_ends {y : ℕ} (hy : y < vList.length) (hyr : y ≠ r) (S : Finset ℕ) :
    (T₀.tail (fid (pe y)) ∈ S ∧ T₀.head (fid (pe y)) ∈ S) ↔
      (vList.getD y 0 ∈ S ∧ vList.getD (par y) 0 ∈ S) := by
  obtain ⟨-, -, -, hpar, hpeq⟩ := hI.step hy hyr
  have hne : vList.getD y 0 ≠ vList.getD r 0 := fun he => hyr (hI.getD_inj hy hI.hr he)
  rw [← hpeq, ← hpar]
  exact parentEdge_ends_mem hI.hT (hI.getD_mem hy) hne S

/-- Equal roots is the same component of `F₀`. -/
lemma rt_iff_comp {x y : ℕ} (hx : x < vList.length) (hy : y < vList.length) :
    rt y = rt x ↔
      vList.getD y 0 ∈ compOf (forestGivenRoots T₀ (vList.getD r 0) R π) (vList.getD x 0) := by
  have hB := rt_bridge hI h.hS h.hmp h.hown h.hrt_r h.hrule
  obtain ⟨hrl, hrR, hconn⟩ := hB x hx
  rw [mem_compOf_iff, ← connected_iff_rt hI h hy hrl hrR]
  constructor
  · intro hc
    exact ⟨hI.getD_mem hy, connected_trans hconn (connected_symm hc)⟩
  · rintro ⟨-, hc⟩
    exact connected_trans (connected_symm hc) hconn

end Key

/-- Equal labels is the same piece of `W_T`. -/
lemma lab_iff_ind (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {W_T : Finset (Finset ℕ)}
    {lab : ℕ → ℕ × ℕ} (hW : WLabels T₀ vList r W_T lab) {x y : ℕ} (hx : x < vList.length)
    (hxr : x ≠ r) (hy : y < vList.length) (hyr : y ≠ r) {W : Finset ℕ} (hWm : W ∈ W_T)
    (hxW : fid (pe x) ∈ inducedEdges T₀ W) :
    lab y = lab x ↔ fid (pe y) ∈ inducedEdges T₀ W := by
  obtain ⟨-, -, -, -, hpx⟩ := hI.step hx hxr
  obtain ⟨-, -, -, -, hpy⟩ := hI.step hy hyr
  rw [hW.hlab y hy hyr x hx hxr, hpx, hpy]
  constructor
  · rintro ⟨P, hP, hyP, hxP⟩
    by_cases hPW : P = W
    · rwa [← hPW]
    · exact absurd hxW (Finset.disjoint_left.mp (hW.hdisj P hP W hWm hPW) hxP)
  · intro hyW
    exact ⟨W, hWm, hyW, hxW⟩

/-- A component is closed under the edges of the graph. -/
lemma comp_ends_iff {G : MGraph} (hG : G.IsValid) {e u : ℕ} (he : e ∈ G.E) :
    G.tail e ∈ compOf G u ↔ G.head e ∈ compOf G u := by
  have hc := connected_of_edge he
  rw [mem_compOf_iff, mem_compOf_iff]
  exact ⟨fun ⟨_, h⟩ => ⟨(hG e he).2, connected_trans h hc⟩,
    fun ⟨_, h⟩ => ⟨(hG e he).1, connected_trans h (connected_symm hc)⟩⟩

/-! ## The characterization -/

section Char

variable {W_T : Finset (Finset ℕ)} {lab : ℕ → ℕ × ℕ}
  (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
  (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt)
  (hW : WLabels T₀ vList r W_T lab)
include hI h

/-- The forest `F₀` is a valid graph. -/
lemma forest_valid : (forestGivenRoots T₀ (vList.getD r 0) R π).IsValid := fun e he =>
  hI.hT.isForest.1 e (Finset.mem_sdiff.mp he).1

/-- The two ends of the parent edge of a kept index are in the same component. -/
lemma kept_comp_iff {y : ℕ} (hy : y < vList.length) (hyr : y ≠ r) (ho : own (pe y) = 0) (u : ℕ) :
    vList.getD y 0 ∈ compOf (forestGivenRoots T₀ (vList.getD r 0) R π) u ↔
      vList.getD (par y) 0 ∈ compOf (forestGivenRoots T₀ (vList.getD r 0) R π) u := by
  obtain ⟨hF, hpe, hpar⟩ := kept_edge hI h hy hyr ho
  have hne : vList.getD y 0 ≠ vList.getD r 0 := fun he => hyr (hI.getD_inj hy hI.hr he)
  have hends := parentEdge_endpoints hI.hT (hI.getD_mem hy) hne
  rw [hpe, hpar] at hends
  have := comp_ends_iff (forest_valid hI h) (u := u) hF
  rcases Set.pair_eq_pair_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact this
  · rw [← h1, ← h2]; exact this.symm

/-- An edge of `F₀` is the parent edge of a kept index. -/
lemma forest_edge_kept {e : ℕ} (he : e ∈ (forestGivenRoots T₀ (vList.getD r 0) R π).E) :
    ∃ y < vList.length, y ≠ r ∧ own (pe y) = 0 ∧ fid (pe y) = e ∧
      ((T₀.tail e = vList.getD y 0 ∧ T₀.head e = vList.getD (par y) 0) ∨
        (T₀.head e = vList.getD y 0 ∧ T₀.tail e = vList.getD (par y) 0)) := by
  have heT : e ∈ T₀.E := (Finset.mem_sdiff.mp he).1
  obtain ⟨y, hy, hyr, hfe, hends⟩ := edge_child_idx hI heT
  refine ⟨y, hy, hyr, ?_, hfe, hends⟩
  rw [forest_E_eq hI h] at he
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp he
  obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hi
  obtain ⟨-, hpe, -⟩ := hI.step hy hyr
  rw [hI.hA.fid_inj _ hpe _ (Finset.mem_range.mp hi) (hfe.trans hie.symm)]
  exact ho

include hW

/-- The piece of a kept index is `W ∩ C`, for the piece `W` of `W_T` that holds its parent edge
and its component `C` in `F₀`. -/
theorem keyPiece_eq {x : ℕ} (hx : x < vList.length) (hxr : x ≠ r) (hxo : own (pe x) = 0)
    {W : Finset ℕ} (hWm : W ∈ W_T) (hxW : fid (pe x) ∈ inducedEdges T₀ W) :
    keyPiece vList r own pe rt par lab x =
      W ∩ compOf (forestGivenRoots T₀ (vList.getD r 0) R π) (vList.getD x 0) := by
  classical
  set F := forestGivenRoots T₀ (vList.getD r 0) R π with hF
  have hxF := Finset.mem_filter.mp hxW
  have hxWe := (kept_ends hI h hx hxr W).mp hxF.2
  have hxC : vList.getD x 0 ∈ compOf F (vList.getD x 0) := self_mem_compOf (hI.getD_mem hx)
  have hpxC := (kept_comp_iff hI h hx hxr hxo _).mp hxC
  ext v
  simp only [keyPiece, Finset.mem_union, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro (⟨y, hyc, rfl⟩ | ⟨y, hyc, rfl⟩) <;>
    · simp only [keyClass, Finset.mem_filter, Finset.mem_range] at hyc
      obtain ⟨hy, hyr, hyo, hyl, hyt⟩ := hyc
      have hyW := (lab_iff_ind hI hW hx hxr hy hyr hWm hxW).mp hyl
      have hyWe := (kept_ends hI h hy hyr W).mp (Finset.mem_filter.mp hyW).2
      have hyC := (rt_iff_comp hI h hx hy).mp hyt
      first
      | exact ⟨hyWe.1, hyC⟩
      | exact ⟨hyWe.2, (kept_comp_iff hI h hy hyr hyo _).mp hyC⟩
  · rintro ⟨hvW, hvC⟩
    -- another vertex of `W ∩ C`
    obtain ⟨-, -, -, hpar, -⟩ := hI.step hx hxr
    have hne : vList.getD x 0 ≠ vList.getD r 0 := fun he => hxr (hI.getD_inj hx hI.hr he)
    have hxp : vList.getD x 0 ≠ vList.getD (par x) 0 := by
      rw [← hpar]; exact (parent_ne_self hI.hT (hI.getD_mem hx) hne).symm
    obtain ⟨b, hbW, hbC, hvb⟩ : ∃ b ∈ W, b ∈ compOf F (vList.getD x 0) ∧ v ≠ b := by
      by_cases hvx : v = vList.getD x 0
      · exact ⟨_, hxWe.2, hpxC, by rw [hvx]; exact hxp⟩
      · exact ⟨_, hxWe.1, hxC, hvx⟩
    obtain ⟨e, heF, hev, htW, hhW, htC, hhC⟩ :=
      cut_step (D := deletedEdges T₀ (vList.getD r 0) R π) hI.hT (hW.hconv W hWm) hvW hbW hvC
        hbC hvb
    obtain ⟨y, hy, hyr, hyo, hfe, hends⟩ := forest_edge_kept hI h heF
    have heT : e ∈ T₀.E := (Finset.mem_sdiff.mp heF).1
    have hyl : lab y = lab x := (lab_iff_ind hI hW hx hxr hy hyr hWm hxW).mpr
      (by rw [hfe]; exact Finset.mem_filter.mpr ⟨heT, htW, hhW⟩)
    have hyC : vList.getD y 0 ∈ compOf F (vList.getD x 0) := by
      rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← h1]; exact htC
      · rw [← h1]; exact hhC
    have hyt : rt y = rt x := (rt_iff_comp hI h hx hy).mpr hyC
    have hyc : y ∈ keyClass vList.length r own pe rt lab x := by
      simp only [keyClass, Finset.mem_filter, Finset.mem_range]
      exact ⟨hy, hyr, hyo, hyl, hyt⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hev with hv | hv
    · exact Or.inl ⟨y, hyc, by rw [← h1, hv]⟩
    · exact Or.inr ⟨y, hyc, by rw [← h2, hv]⟩
    · exact Or.inr ⟨y, hyc, by rw [← h2, hv]⟩
    · exact Or.inl ⟨y, hyc, by rw [← h1, hv]⟩

/-- Each kept index has a piece of `W_T` holding its parent edge. -/
lemma exists_piece {x : ℕ} (hx : x < vList.length) (hxr : x ≠ r) :
    ∃ W ∈ W_T, fid (pe x) ∈ inducedEdges T₀ W := by
  obtain ⟨-, -, -, -, hpeq⟩ := hI.step hx hxr
  have hne : vList.getD x 0 ≠ vList.getD r 0 := fun he => hxr (hI.getD_inj hx hI.hr he)
  have he : fid (pe x) ∈ T₀.E := hpeq ▸ parentEdge_mem hI.hT (hI.getD_mem hx) hne
  rw [← hW.hcov] at he
  obtain ⟨W, hWm, hW'⟩ := Finset.mem_biUnion.mp he
  exact ⟨W, hWm, hW'⟩

/-- The edges of `F₀` inside the piece of `x` are the parent edges of its key class. -/
theorem ind_keyPiece {x : ℕ} (hx : x < vList.length) (hxr : x ≠ r) (hxo : own (pe x) = 0) :
    inducedEdges (forestGivenRoots T₀ (vList.getD r 0) R π)
        (keyPiece vList r own pe rt par lab x) =
      (keyClass vList.length r own pe rt lab x).image (fun y => fid (pe y)) := by
  classical
  obtain ⟨W, hWm, hxW⟩ := exists_piece hI h hW hx hxr
  have hpc := keyPiece_eq hI h hW hx hxr hxo hWm hxW
  ext e
  constructor
  · intro he
    obtain ⟨heF, ht, hh⟩ := Finset.mem_filter.mp he
    change T₀.tail e ∈ _ at ht
    change T₀.head e ∈ _ at hh
    rw [hpc, Finset.mem_inter] at ht hh
    obtain ⟨y, hy, hyr, hyo, hfe, hends⟩ := forest_edge_kept hI h heF
    have heT : e ∈ T₀.E := (Finset.mem_sdiff.mp heF).1
    have hyl : lab y = lab x := (lab_iff_ind hI hW hx hxr hy hyr hWm hxW).mpr
      (by rw [hfe]; exact Finset.mem_filter.mpr ⟨heT, ht.1, hh.1⟩)
    have hyC : vList.getD y 0 ∈ compOf (forestGivenRoots T₀ (vList.getD r 0) R π)
        (vList.getD x 0) := by
      rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← h1]; exact ht.2
      · rw [← h1]; exact hh.2
    refine Finset.mem_image.mpr ⟨y, ?_, hfe⟩
    simp only [keyClass, Finset.mem_filter, Finset.mem_range]
    exact ⟨hy, hyr, hyo, hyl, (rt_iff_comp hI h hx hy).mpr hyC⟩
  · intro he
    obtain ⟨y, hyc, rfl⟩ := Finset.mem_image.mp he
    have hyc' := hyc
    simp only [keyClass, Finset.mem_filter, Finset.mem_range] at hyc'
    obtain ⟨hy, hyr, hyo, -, -⟩ := hyc'
    refine Finset.mem_filter.mpr ⟨(kept_edge hI h hy hyr hyo).1, ?_⟩
    refine (kept_ends hI h hy hyr _).mpr ⟨?_, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hyc, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hyc, rfl⟩)

/-- The pieces of `refineDecomp W_T F₀` are the pieces of the kept indices. -/
theorem refine_mem_iff (P : Finset ℕ) :
    P ∈ refineDecomp W_T (forestGivenRoots T₀ (vList.getD r 0) R π) ↔
      ∃ x < vList.length, x ≠ r ∧ own (pe x) = 0 ∧ P = keyPiece vList r own pe rt par lab x := by
  classical
  set F := forestGivenRoots T₀ (vList.getD r 0) R π with hF
  unfold refineDecomp
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨W, C⟩, hWC, rfl⟩, ⟨e, he⟩⟩
    obtain ⟨hWm, hC⟩ := Finset.mem_product.mp hWC
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨heF, ht, hh⟩ := Finset.mem_filter.mp he
    change T₀.tail e ∈ W ∩ compOf F u at ht
    change T₀.head e ∈ W ∩ compOf F u at hh
    rw [Finset.mem_inter] at ht hh
    obtain ⟨y, hy, hyr, hyo, hfe, hends⟩ := forest_edge_kept hI h heF
    have heT : e ∈ T₀.E := (Finset.mem_sdiff.mp heF).1
    have hyW : fid (pe y) ∈ inducedEdges T₀ W := by
      rw [hfe]; exact Finset.mem_filter.mpr ⟨heT, ht.1, hh.1⟩
    have hyC : vList.getD y 0 ∈ compOf F u := by
      rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [← h1]; exact ht.2
      · rw [← h1]; exact hh.2
    refine ⟨y, hy, hyr, hyo, ?_⟩
    rw [keyPiece_eq hI h hW hy hyr hyo hWm hyW,
      compOf_eq_of_connected (mem_compOf_iff.mp hyC).2]
  · rintro ⟨x, hx, hxr, hxo, rfl⟩
    obtain ⟨W, hWm, hxW⟩ := exists_piece hI h hW hx hxr
    refine ⟨⟨⟨W, compOf F (vList.getD x 0)⟩, Finset.mem_product.mpr ⟨hWm,
      Finset.mem_image.mpr ⟨_, hI.getD_mem hx, rfl⟩⟩,
      (keyPiece_eq hI h hW hx hxr hxo hWm hxW).symm⟩, ?_⟩
    rw [ind_keyPiece hI h hW hx hxr hxo]
    refine ⟨fid (pe x), Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
    simp only [keyClass, Finset.mem_filter, Finset.mem_range]
    exact ⟨hx, hxr, hxo, trivial, trivial⟩

/-- Two kept indices have the same piece exactly when they have the same key. -/
theorem keyPiece_eq_iff {x x' : ℕ} (hx : x < vList.length) (hxr : x ≠ r) (hxo : own (pe x) = 0)
    (hx' : x' < vList.length) (hxr' : x' ≠ r) (hxo' : own (pe x') = 0) :
    keyPiece vList r own pe rt par lab x = keyPiece vList r own pe rt par lab x' ↔
      (lab x = lab x' ∧ rt x = rt x') := by
  classical
  constructor
  · intro heq
    have h1 := ind_keyPiece hI h hW hx hxr hxo
    have h2 := ind_keyPiece hI h hW hx' hxr' hxo'
    rw [heq, h2] at h1
    have hmem : fid (pe x') ∈ (keyClass vList.length r own pe rt lab x').image
        (fun y => fid (pe y)) := Finset.mem_image.mpr ⟨x', by
      simp only [keyClass, Finset.mem_filter, Finset.mem_range]
      exact ⟨hx', hxr', hxo', trivial, trivial⟩, rfl⟩
    rw [h1] at hmem
    obtain ⟨y, hyc, hye⟩ := Finset.mem_image.mp hmem
    simp only [keyClass, Finset.mem_filter, Finset.mem_range] at hyc
    obtain ⟨hy, hyr, -, hyl, hyt⟩ := hyc
    obtain ⟨-, hpy, -⟩ := hI.step hy hyr
    obtain ⟨-, hpx', -⟩ := hI.step hx' hxr'
    have hpp := hI.hA.fid_inj _ hpy _ hpx' hye
    have hyx : y = x' := by
      obtain ⟨-, -, -, -, h1⟩ := hI.step hy hyr
      obtain ⟨-, -, -, -, h2⟩ := hI.step hx' hxr'
      have hne1 : vList.getD y 0 ≠ vList.getD r 0 := fun he => hyr (hI.getD_inj hy hI.hr he)
      have hne2 : vList.getD x' 0 ≠ vList.getD r 0 := fun he => hxr' (hI.getD_inj hx' hI.hr he)
      exact hI.getD_inj hy hx' (parentEdge_inj hI.hT (hI.getD_mem hy) (hI.getD_mem hx') hne1
        hne2 (by rw [h1, h2, hpp]))
    subst hyx
    exact ⟨hyl.symm, hyt.symm⟩
  · rintro ⟨hl, ht⟩
    simp only [keyPiece, keyClass, hl, ht]

end Char

end MinCostFlow.LSF.Program

end
