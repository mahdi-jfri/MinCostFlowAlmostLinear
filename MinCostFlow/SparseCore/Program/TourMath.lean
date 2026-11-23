module

public import MinCostFlow.SparseCore.Program.TourCycle

/-!
# Euler-tour characterization of core rotations

The core rotation at a root `r ∈ F.R` (`Bundle.coreRotation`) is the forest tour `tour ρ hF r`,
which lists the open ends of `r`'s component in depth-first rotation order. Including the forest
ends themselves gives the full Euler dart sequence `fullTour ord F hF r`:

* Filtering `fullTour` to open ends (`x.1 ∉ F.E`) recovers `coreTour ord rf r`, which equals
  `(coreRotation ρ hG hF).order r` exactly (`fullTour_filter_open`, `coreTour_eq_coreRotation`).
* Under `OrdForestCompat ord F`, `fullTour ord F hF v` is a single `Nodup` cycle of `eulerSucc ord F`
  (`fullTour_spec`, `fullTour_cycNext`).
* Rotating any cyclic rotation of `fullTour` to start at `(ord r)[0]` recovers `fullTour`
  identically (`rotateToList_fullTour_of_isRotated`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

/-! ## Order-forest compatibility and order-driven tours -/

/-- The unique vertex whose order list contains `x` (or `0` if none). -/
noncomputable def ordSrc (ord : ℕ → List End) (x : End) : ℕ :=
  open Classical in
  if h : ∃ v, x ∈ ord v then h.choose else 0

/-- Compatibility of an end order `ord` with a forest `F`: each vertex list is `Nodup`, each end
belongs to at most one vertex, `F` is a forest whose vertex set contains every vertex with a
nonempty order, and every forest edge has both its tail and head ends in `ord` at its endpoints in
`F`. Open ends are not required to be paired, so single-end edits (`insertBefore`) preserve this
invariant. -/
structure OrdForestCompat (ord : ℕ → List End) (F : MGraph) : Prop where
  nodup : ∀ v, (ord v).Nodup
  unique : ∀ u v x, x ∈ ord u → x ∈ ord v → u = v
  forest : F.IsForest
  vert : ∀ v, ord v ≠ [] → v ∈ F.V
  forestEnd : ∀ e ∈ F.E, (e, true) ∈ ord (F.tail e) ∧ (e, false) ∈ ord (F.head e)

theorem OrdForestCompat.ordSrc_eq {ord : ℕ → List End} {F : MGraph}
    (hc : OrdForestCompat ord F) {v : ℕ} {x : End} (hx : x ∈ ord v) :
    ordSrc ord x = v := by
  classical
  have hex : ∃ u, x ∈ ord u := ⟨v, hx⟩
  simp only [ordSrc, hex, ↓reduceDIte]
  exact hc.unique _ v x hex.choose_spec hx

theorem OrdForestCompat.mem_ord_of_forest {ord : ℕ → List End} {F : MGraph}
    (hc : OrdForestCompat ord F) {x : End} (hx : x.1 ∈ F.E) :
    x ∈ ord (F.src x) := by
  obtain ⟨e, b⟩ := x
  cases b
  · exact (hc.forestEnd e hx).2
  · exact (hc.forestEnd e hx).1

theorem OrdForestCompat.ordSrc_of_forest {ord : ℕ → List End} {F : MGraph}
    (hc : OrdForestCompat ord F) {x : End} (hx : x.1 ∈ F.E) :
    ordSrc ord x = F.src x :=
  hc.ordSrc_eq (hc.mem_ord_of_forest hx)

/-- Every rotation of a valid graph with a rooted spanning forest is compatible with its forest. -/
theorem ordForestCompat_of_rotation {G : MGraph} {rf : RootedForest} (ρ : Rotation G)
    (hG : G.IsValid) (hF : rf.IsRootedSpanningForestOf G) :
    OrdForestCompat ρ.order rf.F where
  nodup := ρ.nodup
  unique u v x hu hv := ((ρ.mem_order u x).mp hu).2.symm.trans ((ρ.mem_order v x).mp hv).2
  forest := hF.1
  vert v hne := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨he, hs⟩ := (ρ.mem_order v x).mp hx
    rw [hF.2.1, ← hs]
    obtain ⟨e, b⟩ := x
    cases b
    · exact (hG e he).2
    · exact (hG e he).1
  forestEnd e he := by
    have hsub := hF.2.2.2.2
    have hends := hsub.2.2 e he
    exact ⟨(ρ.mem_order _ _).mpr ⟨hsub.2.1 he, hends.1.symm⟩,
      (ρ.mem_order _ _).mpr ⟨hsub.2.1 he, hends.2.symm⟩⟩

/-- Expand ends at `v` into open-end blocks directly from an order `ord`. -/
noncomputable def ordTourBlocks (ord : ℕ → List End) (F₀ F : MGraph) (hF : F.IsForest)
    (v : ℕ) (xs : List End) : List End :=
  xs.flatMap fun x =>
    if x.1 ∉ F₀.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      ordTourBlocks ord F₀ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (ord (F.dst x)))
    else []
termination_by (compOf F v).card
decreasing_by
  rw [← _h.2]
  exact branch_card_lt hF _h.1

/-- The core rotation list at `r`, defined directly from `(ord, rf)`. -/
noncomputable def coreTour (ord : ℕ → List End) (rf : RootedForest) (r : ℕ) : List End :=
  open Classical in
  if hF : rf.F.IsForest then
    if r ∈ rf.R then ordTourBlocks ord rf.F rf.F hF r (ord r) else []
  else []

theorem ordTourBlocks_eq_tourBlocks {G F₀ F : MGraph} (ρ : Rotation G) (hF : F.IsForest)
    (v : ℕ) (xs : List End) :
    ordTourBlocks ρ.order F₀ F hF v xs = tourBlocks G F₀ ρ F hF v xs := by
  rw [ordTourBlocks.eq_def, tourBlocks.eq_def]
  apply List.flatMap_congr
  intro x _
  by_cases h1 : x.1 ∉ F₀.E
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : x.1 ∈ F.E ∧ F.src x = v
    · simp only [h2, and_self, ↓reduceDIte]
      exact ordTourBlocks_eq_tourBlocks ρ (isForest_eraseEdge hF x.1) (F.dst x) _
    · simp [h2]
termination_by (compOf F v).card
decreasing_by
  rw [← h2.2]
  exact branch_card_lt hF h2.1

/-- `coreTour` agrees identically with `(coreRotation ρ hG hF).order`. -/
theorem coreTour_eq_coreRotation {G : MGraph} {L : LSF} (ρ : Rotation G)
    (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G) (r : ℕ) :
    coreTour ρ.order L.F r = (coreRotation ρ hG hF).order r := by
  classical
  simp only [coreTour, coreRotation, hF.1, ↓reduceDIte]
  split_ifs with hr
  · exact ordTourBlocks_eq_tourBlocks ρ hF.1 r (ρ.order r)
  · rfl

/-- Full Euler dart blocks at `v`: open ends contribute `[x]` and forest ends contribute
`x :: (subtree darts) ++ [x.flip]`. -/
noncomputable def fullTourBlocks (ord : ℕ → List End) (F₀ F : MGraph) (hF : F.IsForest)
    (v : ℕ) (xs : List End) : List End :=
  xs.flatMap fun x =>
    if x.1 ∉ F₀.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      x :: fullTourBlocks ord F₀ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (ord (F.dst x))) ++ [x.flip]
    else []
termination_by (compOf F v).card
decreasing_by
  rw [← _h.2]
  exact branch_card_lt hF _h.1

/-- Full Euler dart sequence of the forest component of `v`, starting from `ord v`. -/
noncomputable def fullTour (ord : ℕ → List End) (F : MGraph) (hF : F.IsForest) (v : ℕ) : List End :=
  fullTourBlocks ord F F hF v (ord v)

/-- Restricting `fullTourBlocks` to open ends (`x.1 ∉ F₀.E`) gives `ordTourBlocks` identically. -/
theorem fullTourBlocks_filter_open (ord : ℕ → List End) (F₀ F : MGraph) (hF : F.IsForest)
    (v : ℕ) (xs : List End) :
    (fullTourBlocks ord F₀ F hF v xs).filter (fun x => decide (x.1 ∉ F₀.E)) =
      ordTourBlocks ord F₀ F hF v xs := by
  rw [fullTourBlocks.eq_def, ordTourBlocks.eq_def, List.filter_flatMap]
  apply List.flatMap_congr
  intro x _
  by_cases hopen : x.1 ∉ F₀.E
  · simp [hopen]
  · simp only [hopen, ↓reduceIte]
    by_cases hfe : x.1 ∈ F.E ∧ F.src x = v
    · simp only [hfe, and_self, ↓reduceDIte, List.cons_append, List.filter_cons, List.filter_append,
        decide_eq_true_eq, hopen, ↓reduceIte, End.flip, List.filter_nil, List.append_nil]
      exact fullTourBlocks_filter_open ord F₀ (eraseForestEdge F x.1)
        (isForest_eraseEdge hF x.1) (F.dst x) (afterEnd x.flip (ord (F.dst x)))
    · simp [hfe]
termination_by (compOf F v).card
decreasing_by
  rw [← hfe.2]
  exact branch_card_lt hF hfe.1

/-- Restricting `fullTour` at a root `r ∈ rf.R` to open ends gives `coreTour` identically. -/
theorem fullTour_filter_open (ord : ℕ → List End) {rf : RootedForest} (hF : rf.F.IsForest)
    {r : ℕ} (hr : r ∈ rf.R) :
    (fullTour ord rf.F hF r).filter (fun x => decide (x.1 ∉ rf.F.E)) = coreTour ord rf r := by
  classical
  simp only [fullTour, coreTour, hF, hr, ↓reduceDIte, ↓reduceIte]
  exact fullTourBlocks_filter_open ord rf.F rf.F hF r (ord r)

/-! ## Combinatorial-map successor `eulerSucc` -/

/-- The forest involution: flips forest ends and fixes open ends. -/
noncomputable def forestAlpha (F : MGraph) (x : End) : End :=
  open Classical in
  if x.1 ∈ F.E then x.flip else x

/-- The combinatorial-map successor `σ_ord ∘ α_F` on ends. -/
noncomputable def eulerSucc (ord : ℕ → List End) (F : MGraph) (x : End) : End :=
  open Classical in
  if x.1 ∈ F.E then cycNext (ord (F.dst x)) x.flip else cycNext (ord (ordSrc ord x)) x

theorem flip_flip (x : End) : x.flip.flip = x := by
  cases x with | mk e b => cases b <;> rfl

theorem flip_ne_self (x : End) : x.flip ≠ x := by
  cases x with | mk e b => cases b <;> simp [End.flip]

theorem src_flip_eq (F : MGraph) (x : End) : F.src x.flip = F.dst x := by
  cases x with | mk e b => cases b <;> rfl

theorem dst_flip_eq (F : MGraph) (x : End) : F.dst x.flip = F.src x := by
  cases x with | mk e b => cases b <;> rfl

theorem eulerSucc_forestAlpha {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v : ℕ} {x : End} (hx : x ∈ ord v) :
    eulerSucc ord F (forestAlpha F x) = cycNext (ord v) x := by
  unfold eulerSucc forestAlpha
  split_ifs with h1 h2
  · rw [flip_flip, dst_flip_eq, ← hc.ordSrc_of_forest h1, hc.ordSrc_eq hx]
  · exfalso; apply h2; simpa [End.flip] using h1
  · rw [hc.ordSrc_eq hx]

private theorem src_eq_sub {F₀ F : MGraph} (hsub : F₀.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    F.src x = F₀.src x := by
  obtain ⟨e, b⟩ := x
  have h := hsub.2.2 e hx
  cases b
  · exact h.2
  · exact h.1

private theorem dst_eq_sub {F₀ F : MGraph} (hsub : F₀.IsSubgraph F) {x : End} (hx : x.1 ∈ F.E) :
    F.dst x = F₀.dst x := by
  obtain ⟨e, b⟩ := x
  have h := hsub.2.2 e hx
  cases b
  · exact h.1
  · exact h.2

private theorem afterEnd_of_append' {x : End} {pre suf : List End} (h : x ∉ pre) :
    afterEnd x (pre ++ x :: suf) = suf ++ pre := by
  have hp : ∀ y ∈ pre, y != x := fun y hy => bne_iff_ne.mpr fun he => h (he ▸ hy)
  simp [afterEnd, List.takeWhile_append_of_pos hp, List.drop_append]

private theorem afterEnd_cycNext_spec {xs : List End} {x : End}
    (hnd : xs.Nodup) (hx : x ∈ xs) :
    IsSuccChain (cycNext xs) (x :: afterEnd x xs) ∧
    (afterEnd x xs = [] → cycNext xs x = x) ∧
    (∀ y, (afterEnd x xs).getLast? = some y → cycNext xs y = x) := by
  obtain ⟨pre, suf, rfl⟩ := List.mem_iff_append.mp hx
  have hnot : x ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 x hm x (by simp) rfl
  rw [afterEnd_of_append' hnot]
  have hrot : (pre ++ x :: suf).IsRotated (x :: (suf ++ pre)) := by
    have := List.isRotated_append (l := pre) (l' := x :: suf)
    simpa [List.cons_append, List.append_assoc] using this
  have hnd' : (x :: (suf ++ pre)).Nodup := hrot.perm.nodup_iff.mp hnd
  have hc : IsCycleOf (cycNext (pre ++ x :: suf)) (x :: (suf ++ pre)) :=
    (isCycleOf_iff_cycNext hnd').mpr fun z hz =>
      cycNext_isRotated hnd hrot (hrot.perm.mem_iff.mpr hz)
  refine ⟨hc.1, ?_, ?_⟩
  · intro he; rw [he] at hc; exact hc.2 x x rfl rfl
  · intro y hy
    apply hc.2 x y rfl
    cases h : suf ++ pre with
    | nil => rw [h] at hy; simp at hy
    | cons u rest => rw [h] at hy; simpa [List.getLast?_cons_cons] using hy

private theorem exists_branch_of_connected' {F : MGraph} {v w : ℕ}
    (hvw : F.Connected v w) (hne : v ≠ w) :
    ∃ x : End, x.1 ∈ F.E ∧ F.src x = v ∧ (eraseForestEdge F x.1).Connected (F.dst x) w := by
  obtain ⟨P, hp⟩ := connected_isPath hvw
  cases P with
  | nil => cases hp.1; exact (hne rfl).elim
  | cons x P =>
    cases hp.1 with
    | cons he hs hP =>
      refine ⟨x, he, hs, P, isWalk_eraseEdge_of_not_mem hP ?_⟩
      have hn := (List.nodup_cons.mp (isPath_nodup_edges hp)).1
      simpa [walkEdges] using hn

private theorem path_from_branch' {F : MGraph} (hF : F.IsForest) {x : End} (hx : x.1 ∈ F.E)
    {w : ℕ} (hw : (eraseForestEdge F x.1).Connected (F.dst x) w) :
    ∃ P, F.IsPath (F.src x) w (x :: P) := by
  obtain ⟨P, hp⟩ := connected_isPath hw
  have hh := (isWalk_of_subgraph (eraseForestEdge_subgraph F x.1) hp.1).1
  refine ⟨P, .cons hx rfl hh, ?_⟩
  rw [walkVertices_cons, List.nodup_cons]
  refine ⟨?_, hp.2⟩
  intro hm
  obtain ⟨L, _, _, hL, _⟩ := walkVertices_mem_split hp.1 hm
  exact not_connected_eraseForestEdge hF hx (connected_symm ⟨L, hL⟩)

private theorem branch_unique' {F : MGraph} (hF : F.IsForest) {x y : End} {w : ℕ}
    (hx : x.1 ∈ F.E) (hy : y.1 ∈ F.E) (hs : F.src x = F.src y)
    (hwx : (eraseForestEdge F x.1).Connected (F.dst x) w)
    (hwy : (eraseForestEdge F y.1).Connected (F.dst y) w) : x = y := by
  obtain ⟨P, hp⟩ := path_from_branch' hF hx hwx
  obtain ⟨Q, hq⟩ := path_from_branch' hF hy hwy
  exact (List.cons.inj (isPath_unique hF hp (hs.symm ▸ hq))).1

private theorem flatMap_head?_getLast?_chain {f g h : End → End}
    {block : End → List End} {xs : List End}
    (hchain : IsSuccChain g xs)
    (hhead : ∀ x ∈ xs, (block x).head? = some x)
    (hlast : ∀ x ∈ xs, (block x).getLast? = some (f x))
    (hstep : ∀ x ∈ xs, IsSuccChain h (block x))
    (hlink : ∀ x y, x ∈ xs → g x = y → h (f x) = y) :
    (∀ a, xs.head? = some a → (xs.flatMap block).head? = some a) ∧
    (∀ b, xs.getLast? = some b → (xs.flatMap block).getLast? = some (f b)) ∧
    IsSuccChain h (xs.flatMap block) := by
  induction xs with
  | nil => simp [IsSuccChain]
  | cons x rest ih =>
    have hne_x : block x ≠ [] := by
      intro h0; have := hhead x List.mem_cons_self; rw [h0] at this; simp at this
    cases rest with
    | nil =>
      refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
      · have hxa : x = a := Option.some.inj ha
        subst hxa
        simpa [List.flatMap_cons] using hhead x List.mem_cons_self
      · have hxb : x = b := Option.some.inj hb
        subst hxb
        simpa [List.flatMap_cons] using hlast x List.mem_cons_self
      · simpa [List.flatMap_cons] using hstep x List.mem_cons_self
    | cons y ys =>
      have hrest := ih hchain.2
        (fun z hz => hhead z (List.mem_cons_of_mem x hz))
        (fun z hz => hlast z (List.mem_cons_of_mem x hz))
        (fun z hz => hstep z (List.mem_cons_of_mem x hz))
        (fun u v hu => hlink u v (List.mem_cons_of_mem x hu))
      have hne_rest : (y :: ys).flatMap block ≠ [] := by
        intro h0
        have := hrest.1 y rfl
        rw [h0] at this; simp at this
      refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
      · have hxa : x = a := Option.some.inj ha
        subst hxa
        rw [List.flatMap_cons, List.head?_append_of_ne_nil _ hne_x]
        exact hhead x List.mem_cons_self
      · rw [List.flatMap_cons, List.getLast?_append_of_ne_nil _ hne_rest]
        exact hrest.2.1 b (by simpa [List.getLast?_cons_cons] using hb)
      · rw [List.flatMap_cons]
        refine isSuccChain_append (hstep x List.mem_cons_self) hrest.2.2 fun a b ha hb => ?_
        have ha' : a = f x := Option.some.inj (ha.symm.trans (hlast x List.mem_cons_self))
        have hb' : b = y := Option.some.inj (hb.symm.trans (hrest.1 y rfl))
        rw [ha', hb']
        exact hlink x y List.mem_cons_self hchain.1

private theorem fullTourBlocks_props (ord : ℕ → List End) (F₀ : MGraph)
    (hcomp : OrdForestCompat ord F₀)
    (F : MGraph) (hF : F.IsForest) (hsub : F₀.IsSubgraph F)
    (v : ℕ) (xs : List End)
    (hnd : xs.Nodup) (hs : xs ⊆ ord v)
    (hcover : ∀ x ∈ ord v, x.1 ∉ F₀.E ∨ x.1 ∈ F.E → x ∈ xs)
    (hcut : ∀ y : End, y.1 ∈ F₀.E → F.Connected v (F₀.src y) → y.1 ∉ F.E → F₀.src y = v ∧ y ∉ xs)
    (hchain : IsSuccChain (cycNext (ord v)) xs) :
    let L := fullTourBlocks ord F₀ F hF v xs
    L.Nodup ∧
    (∀ z, z ∈ L ↔ (∃ u, z ∈ ord u ∧ F.Connected v u) ∧ (z.1 ∉ F₀.E ∨ z.1 ∈ F.E)) ∧
    (∀ a, xs.head? = some a → L.head? = some a) ∧
    (∀ b, xs.getLast? = some b → L.getLast? = some (forestAlpha F₀ b)) ∧
    IsSuccChain (eulerSucc ord F₀) L := by
  let block (x : End) :=
    if x.1 ∉ F₀.E then [x]
    else if _h : x.1 ∈ F.E ∧ F.src x = v then
      x :: fullTourBlocks ord F₀ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1) (F.dst x)
        (afterEnd x.flip (ord (F.dst x))) ++ [x.flip]
    else []
  have heq : fullTourBlocks ord F₀ F hF v xs = xs.flatMap block := by
    rw [fullTourBlocks.eq_def]
  have hact : ∀ x ∈ xs, x.1 ∉ F₀.E ∨ x.1 ∈ F.E := by
    intro x hx
    by_cases h0 : x.1 ∈ F₀.E
    · right
      by_contra hne
      have hsrc : F₀.src x = v := (hcomp.ordSrc_of_forest h0).symm.trans (hcomp.ordSrc_eq (hs hx))
      exact (hcut x h0 (hsrc ▸ connected_refl F v) hne).2 hx
    · exact Or.inl h0
  have hblock : ∀ x ∈ xs,
      (block x).Nodup ∧
      (∀ z, z ∈ block x ↔
        (x.1 ∉ F₀.E ∧ z = x) ∨
        (x.1 ∈ F.E ∧ F.src x = v ∧
          (z = x ∨ z = x.flip ∨
            ((∃ u, z ∈ ord u ∧ (eraseForestEdge F x.1).Connected (F.dst x) u) ∧
              (z.1 ∉ F₀.E ∨ z.1 ∈ (eraseForestEdge F x.1).E))))) ∧
      (block x).head? = some x ∧
      (block x).getLast? = some (forestAlpha F₀ x) ∧
      IsSuccChain (eulerSucc ord F₀) (block x) := by
    intro x hx
    rcases hact x hx with hopen | hxe
    · have hbx : block x = [x] := by simp [block, hopen]
      have hxF : x.1 ∉ F.E := fun h => hopen (hsub.2.1 h)
      rw [hbx]
      refine ⟨List.nodup_singleton x, ?_, rfl, ?_, trivial⟩
      · intro z; simp [hopen, hxF]
      · simp [forestAlpha, hopen]
    · have hx₀ : x.1 ∈ F₀.E := hsub.2.1 hxe
      have hxv₀ : F₀.src x = v := (hcomp.ordSrc_of_forest hx₀).symm.trans (hcomp.ordSrc_eq (hs hx))
      have hxv : F.src x = v := (src_eq_sub hsub hxe).trans hxv₀
      have hdw : F.dst x = F₀.dst x := dst_eq_sub hsub hxe
      have hflip_mem : x.flip ∈ ord (F.dst x) := by
        rw [hdw, ← src_flip_eq F₀ x]
        exact hcomp.mem_ord_of_forest (x := x.flip) hx₀
      have hperm := afterEnd_perm_erase hflip_mem (hcomp.nodup _)
      have hsub' : F₀.IsSubgraph (eraseForestEdge F x.1) :=
        ⟨hsub.1, fun _ he => hsub.2.1 (Finset.mem_erase.mp he).2,
          fun e he => hsub.2.2 e (Finset.mem_erase.mp he).2⟩
      have hcov' : ∀ y ∈ ord (F.dst x),
          y.1 ∉ F₀.E ∨ y.1 ∈ (eraseForestEdge F x.1).E →
            y ∈ afterEnd x.flip (ord (F.dst x)) := by
        intro y hy hyE
        have hn : y ≠ x.flip := by
          intro h; subst y
          rcases hyE with h1 | h2
          · exact h1 hx₀
          · exact (Finset.mem_erase.mp h2).1 rfl
        exact hperm.mem_iff.mpr ((List.mem_erase_of_ne hn).mpr hy)
      have hcut' : ∀ y : End, y.1 ∈ F₀.E →
          (eraseForestEdge F x.1).Connected (F.dst x) (F₀.src y) →
          y.1 ∉ (eraseForestEdge F x.1).E →
          F₀.src y = F.dst x ∧ y ∉ afterEnd x.flip (ord (F.dst x)) := by
        intro y hy₀ hcy hny
        by_cases hye : y.1 = x.1
        · have hy_ends : F₀.src y = F₀.src x ∨ F₀.src y = F₀.dst x := by
            obtain ⟨e, b⟩ := x; obtain ⟨f, c⟩ := y
            change f = e at hye; subst f
            cases b <;> cases c <;> simp [MGraph.src, MGraph.dst]
          rcases hy_ends with hs' | hs'
          · exfalso
            rw [hs', hxv₀, ← hxv] at hcy
            exact not_connected_eraseForestEdge hF hxe (connected_symm hcy)
          · have hyflip : y = x.flip := by
              obtain ⟨e, b⟩ := x; obtain ⟨f, c⟩ := y
              change f = e at hye; subst f
              have hnloop := isForest_no_selfLoop hcomp.forest hx₀
              cases b <;> cases c <;> simp_all [End.flip, MGraph.src, MGraph.dst]
            subst hyflip
            exact ⟨hs'.trans hdw.symm, fun hm => (hcomp.nodup _).not_mem_erase (hperm.mem_iff.mp hm)⟩
        · exfalso
          have hnyF : y.1 ∉ F.E := fun hm => hny (Finset.mem_erase.mpr ⟨hye, hm⟩)
          have hstep : F.Connected v (F.dst x) := ⟨[x], .cons hxe hxv (.nil _)⟩
          have hcv : F.Connected v (F₀.src y) :=
            connected_trans hstep (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hcy)
          have hsrc_v := (hcut y hy₀ hcv hnyF).1
          rw [hsrc_v, ← hxv] at hcy
          exact not_connected_eraseForestEdge hF hxe (connected_symm hcy)
      have hafter_spec := afterEnd_cycNext_spec (hcomp.nodup (F.dst x)) hflip_mem
      have hchain' : IsSuccChain (cycNext (ord (F.dst x))) (afterEnd x.flip (ord (F.dst x))) := by
        cases h : afterEnd x.flip (ord (F.dst x)) with
        | nil => trivial
        | cons _ _ => exact (h ▸ hafter_spec.1).2
      have hrec := fullTourBlocks_props ord F₀ hcomp (eraseForestEdge F x.1)
        (isForest_eraseEdge hF x.1) hsub' (F.dst x) (afterEnd x.flip (ord (F.dst x)))
        (hperm.nodup_iff.mpr ((hcomp.nodup _).erase _))
        (fun _ hz => List.mem_of_mem_erase (hperm.mem_iff.mp hz))
        hcov' hcut' hchain'
      set inner := fullTourBlocks ord F₀ (eraseForestEdge F x.1) (isForest_eraseEdge hF x.1)
        (F.dst x) (afterEnd x.flip (ord (F.dst x)))
      have hblock_eq : block x = x :: inner ++ [x.flip] := by
        simp [block, hx₀, hxe, hxv, inner]
      have hx_ni : x ∉ inner := by
        intro hm
        obtain ⟨⟨u, hxu, hcu⟩, _⟩ := (hrec.2.1 x).mp hm
        have huv : u = v := (hcomp.ordSrc_eq hxu).symm.trans (hcomp.ordSrc_eq (hs hx))
        rw [huv, ← hxv] at hcu
        exact not_connected_eraseForestEdge hF hxe (connected_symm hcu)
      have hflip_ni : x.flip ∉ inner := by
        intro hm
        obtain ⟨_, h1 | h2⟩ := (hrec.2.1 x.flip).mp hm
        · exact h1 hx₀
        · exact (Finset.mem_erase.mp h2).1 rfl
      have hnodup_b : (block x).Nodup := by
        rw [hblock_eq, List.cons_append, List.nodup_cons]
        refine ⟨?_, ?_⟩
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hx_ni, (flip_ne_self x).symm⟩
        · exact List.nodup_append.mpr ⟨hrec.1, List.nodup_singleton _,
            fun a ha b hb h => by
              simp only [List.mem_singleton] at hb; subst hb; subst h; exact hflip_ni ha⟩
      have hchain_b : IsSuccChain (eulerSucc ord F₀) (block x) := by
        rw [hblock_eq]
        have hsucc_x : eulerSucc ord F₀ x = cycNext (ord (F.dst x)) x.flip := by
          simp [eulerSucc, hx₀, hdw]
        cases hae : afterEnd x.flip (ord (F.dst x)) with
        | nil =>
          have hinner_nil : inner = [] := by
            simp only [inner]; rw [fullTourBlocks.eq_def, hae]; rfl
          rw [hinner_nil]
          simp only [List.cons_append, List.nil_append, IsSuccChain, and_true]
          exact hsucc_x.trans (hafter_spec.2.1 hae)
        | cons y ys =>
          have hhead_i : inner.head? = some y := hrec.2.2.1 y (by rw [hae]; rfl)
          obtain ⟨b, hb_last⟩ : ∃ b, (afterEnd x.flip (ord (F.dst x))).getLast? = some b := by
            rw [hae]; exact Option.isSome_iff_exists.mp (by simp)
          have hlast_i : inner.getLast? = some (forestAlpha F₀ b) := hrec.2.2.2.1 b hb_last
          have hb_ord : b ∈ ord (F.dst x) :=
            List.mem_of_mem_erase (hperm.mem_iff.mp (List.mem_of_getLast? hb_last))
          have hhead_succ : eulerSucc ord F₀ x = y := by
            rw [hsucc_x]
            have h1 := hafter_spec.1
            rw [hae] at h1
            exact h1.1
          have hlast_succ : eulerSucc ord F₀ (forestAlpha F₀ b) = x.flip :=
            (eulerSucc_forestAlpha hcomp hb_ord).trans (hafter_spec.2.2 b hb_last)
          have hstep1 : IsSuccChain (eulerSucc ord F₀) (x :: inner) := by
            cases hi : inner with
            | nil => rw [hi] at hhead_i; simp at hhead_i
            | cons a rest =>
              rw [hi] at hhead_i
              have hay : a = y := Option.some.inj hhead_i
              subst hay
              exact ⟨hhead_succ, hi ▸ hrec.2.2.2.2⟩
          rw [List.cons_append]
          refine isSuccChain_append hstep1 trivial fun a c ha hc => ?_
          have hcf : c = x.flip := (Option.some.inj hc).symm
          subst hcf
          have hne_i : inner ≠ [] := by intro h0; rw [h0] at hhead_i; simp at hhead_i
          have ha' : a = forestAlpha F₀ b := by
            rw [List.getLast?_cons_of_ne_nil hne_i] at ha
            exact Option.some.inj (ha.symm.trans hlast_i)
          rw [ha']
          exact hlast_succ
      refine ⟨hnodup_b, ?_, ?_, ?_, hchain_b⟩
      · intro z
        rw [hblock_eq]
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
          hrec.2.1, hx₀, not_true_eq_false, false_and, false_or, hxe, hxv, true_and]
        exact ⟨fun h => by rcases h with h | h | h; exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h),
          fun h => by rcases h with h | h | h; exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h)⟩
      · rw [hblock_eq]; rfl
      · rw [hblock_eq, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
        simp [forestAlpha, hx₀]
  rw [heq]
  have hflat := flatMap_head?_getLast?_chain (h := eulerSucc ord F₀) (f := forestAlpha F₀)
    (g := cycNext (ord v)) hchain
    (fun x hx => (hblock x hx).2.2.1) (fun x hx => (hblock x hx).2.2.2.1)
    (fun x hx => (hblock x hx).2.2.2.2)
    (fun x y hx hxy => (eulerSucc_forestAlpha hcomp (hs hx)).trans hxy)
  refine ⟨?_, ?_, hflat.1, hflat.2.1, hflat.2.2⟩
  · apply List.nodup_flatMap.mpr
    refine ⟨fun x hx => (hblock x hx).1, ?_⟩
    apply List.Pairwise.imp_of_mem (l := xs) _ hnd
    intro x y hx hy hne
    apply List.disjoint_left.mpr
    intro z hzx hzy
    have hzx' := (hblock x hx).2.1 z |>.mp hzx
    have hzy' := (hblock y hy).2.1 z |>.mp hzy
    rcases hzx' with ⟨hxopen, rfl⟩ | ⟨hxe, hxv, hzx1 | hzx2 | ⟨⟨u, hzu, hcu⟩, _⟩⟩
    · rcases hzy' with ⟨_, hxy⟩ | ⟨hye, hyv, hxy | hxf | ⟨⟨u, hzu, hcu⟩, _⟩⟩
      · exact hne hxy
      · exact hne hxy
      · exact hxopen (hxf ▸ hsub.2.1 hye)
      · have huv : u = v := (hcomp.ordSrc_eq hzu).symm.trans (hcomp.ordSrc_eq (hs hx))
        rw [huv, ← hyv] at hcu
        exact not_connected_eraseForestEdge hF hye (connected_symm hcu)
    · subst z
      rcases hzy' with ⟨_, hxy⟩ | ⟨hye, hyv, hxy | hxf | ⟨⟨u, hzu, hcu⟩, _⟩⟩
      · exact hne hxy
      · exact hne hxy
      · have hflip_v : F₀.src y.flip = v :=
          (hcomp.ordSrc_of_forest (x := y.flip) (hsub.2.1 hye)).symm.trans (hcomp.ordSrc_eq (hxf ▸ hs hx))
        have hd_y : F.dst y = v := (dst_eq_sub hsub hye).trans (src_flip_eq F₀ y ▸ hflip_v)
        exact isForest_no_selfLoop hF hye (by
          obtain ⟨e, b⟩ := y; cases b <;> simp_all [MGraph.src, MGraph.dst])
      · have huv : u = v := (hcomp.ordSrc_eq hzu).symm.trans (hcomp.ordSrc_eq (hs hx))
        rw [huv, ← hyv] at hcu
        exact not_connected_eraseForestEdge hF hye (connected_symm hcu)
    · subst z
      rcases hzy' with ⟨hyopen, hxy⟩ | ⟨hye, hyv, hxy | hxf | ⟨⟨u, hzu, hcu⟩, _⟩⟩
      · exact hyopen (hxy ▸ hsub.2.1 hxe)
      · have hd_x : F.dst x = v :=
          (dst_eq_sub hsub hxe).trans ((src_flip_eq F₀ x).symm.trans
            ((hcomp.ordSrc_of_forest (x := x.flip) (hsub.2.1 hxe)).symm.trans (hcomp.ordSrc_eq (hxy ▸ hs hy))))
        exact isForest_no_selfLoop hF hxe (by
          obtain ⟨e, b⟩ := x; cases b <;> simp_all [MGraph.src, MGraph.dst])
      · exact hne (by have := congrArg End.flip hxf; simpa [flip_flip] using this)
      · have hu : u = F.dst x := by
          have h1 := hcomp.ordSrc_eq hzu
          have h2 := hcomp.ordSrc_of_forest (x := x.flip) (hsub.2.1 hxe)
          rw [src_flip_eq, ← dst_eq_sub hsub hxe] at h2
          exact h1.symm.trans h2
        rw [hu] at hcu
        exact hne (branch_unique' hF hxe hye (hxv.trans hyv.symm)
          (connected_refl (eraseForestEdge F x.1) (F.dst x)) hcu)
    · rcases hzy' with ⟨_, rfl⟩ | ⟨hye, hyv, rfl | rfl | ⟨⟨u', hzu', hcu'⟩, _⟩⟩
      · have huv : u = v := (hcomp.ordSrc_eq hzu).symm.trans (hcomp.ordSrc_eq (hs hy))
        rw [huv, ← hxv] at hcu
        exact not_connected_eraseForestEdge hF hxe (connected_symm hcu)
      · have huv : u = v := (hcomp.ordSrc_eq hzu).symm.trans (hcomp.ordSrc_eq (hs hy))
        rw [huv, ← hxv] at hcu
        exact not_connected_eraseForestEdge hF hxe (connected_symm hcu)
      · have hu : u = F.dst y := by
          have h1 := hcomp.ordSrc_eq hzu
          have h2 := hcomp.ordSrc_of_forest (x := y.flip) (hsub.2.1 hye)
          rw [src_flip_eq, ← dst_eq_sub hsub hye] at h2
          exact h1.symm.trans h2
        rw [hu] at hcu
        exact hne (branch_unique' hF hxe hye (hxv.trans hyv.symm) hcu
          (connected_refl (eraseForestEdge F y.1) (F.dst y)))
      · have huu' : u = u' := hcomp.unique u u' z hzu hzu'
        subst huu'
        exact hne (branch_unique' hF hxe hye (hxv.trans hyv.symm) hcu hcu')
  · intro z
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hz⟩
      rcases (hblock x hx).2.1 z |>.mp hz with
        ⟨hopen, rfl⟩ | ⟨hxe, hxv, rfl | rfl | ⟨⟨u, hzu, hcu⟩, hzE⟩⟩
      · exact ⟨⟨v, hs hx, connected_refl F v⟩, Or.inl hopen⟩
      · exact ⟨⟨v, hs hx, connected_refl F v⟩, Or.inr hxe⟩
      · have hstep : F.Connected v (F.dst x) := ⟨[x], .cons hxe hxv (.nil _)⟩
        have hfl : x.flip ∈ ord (F.dst x) := by
          rw [dst_eq_sub hsub hxe, ← src_flip_eq F₀ x]
          exact hcomp.mem_ord_of_forest (x := x.flip) (hsub.2.1 hxe)
        exact ⟨⟨F.dst x, hfl, hstep⟩, Or.inr hxe⟩
      · have hstep : F.Connected v (F.dst x) := ⟨[x], .cons hxe hxv (.nil _)⟩
        refine ⟨⟨u, hzu, connected_trans hstep
          (connected_of_subgraph (eraseForestEdge_subgraph F x.1) hcu)⟩, ?_⟩
        rcases hzE with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Finset.mem_erase.mp h2).2
    · rintro ⟨⟨u, hzu, hcu⟩, hzE⟩
      by_cases hvu : v = u
      · subst hvu
        have hzxs := hcover z hzu hzE
        refine ⟨z, hzxs, ((hblock z hzxs).2.1 z).mpr ?_⟩
        rcases hzE with hopen | hze
        · exact Or.inl ⟨hopen, rfl⟩
        · have hzv : F.src z = v :=
            (src_eq_sub hsub hze).trans ((hcomp.ordSrc_of_forest (hsub.2.1 hze)).symm.trans
              (hcomp.ordSrc_eq hzu))
          exact Or.inr ⟨hze, hzv, Or.inl rfl⟩
      · obtain ⟨x, hxe, hxv, hbx⟩ := exists_branch_of_connected' hcu hvu
        have hxord : x ∈ ord v := by
          rw [← hxv, src_eq_sub hsub hxe]
          exact hcomp.mem_ord_of_forest (hsub.2.1 hxe)
        have hxxs := hcover x hxord (Or.inr hxe)
        refine ⟨x, hxxs, ((hblock x hxxs).2.1 z).mpr (Or.inr ⟨hxe, hxv, ?_⟩)⟩
        by_cases hzx : z.1 = x.1
        · have hzflip : z = x.flip := by
            have hze : z.1 ∈ F.E := hzx ▸ hxe
            have hzs : F.src z = u :=
              (src_eq_sub hsub hze).trans ((hcomp.ordSrc_of_forest (hsub.2.1 hze)).symm.trans
                (hcomp.ordSrc_eq hzu))
            have hne_sv : F.src z ≠ F.src x := by rw [hzs, hxv]; exact Ne.symm hvu
            obtain ⟨e, b⟩ := x; obtain ⟨f, c⟩ := z
            change f = e at hzx; subst f
            cases b <;> cases c <;> simp [End.flip, MGraph.src] at hne_sv ⊢
          exact Or.inr (Or.inl hzflip)
        · refine Or.inr (Or.inr ⟨⟨u, hzu, hbx⟩, ?_⟩)
          rcases hzE with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Finset.mem_erase.mpr ⟨hzx, h2⟩)
termination_by (compOf F v).card
decreasing_by
  rw [← hxv]
  exact branch_card_lt hF hxe

/-- `fullTour` is `Nodup` and lists every end of `ord` whose vertex is connected to `v` in `F`. -/
theorem fullTour_spec {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F) (v : ℕ) :
    (fullTour ord F hc.forest v).Nodup ∧
    ∀ z, z ∈ fullTour ord F hc.forest v ↔ ∃ u, z ∈ ord u ∧ F.Connected v u := by
  have hchain : IsSuccChain (cycNext (ord v)) (ord v) :=
    ((isCycleOf_iff_cycNext (hc.nodup v)).mpr fun _ _ => rfl).1
  have hp := fullTourBlocks_props ord F hc F hc.forest
    ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩ v (ord v)
    (hc.nodup v) (fun _ h => h) (fun _ h _ => h) (fun _ h1 _ h2 => absurd h1 h2) hchain
  refine ⟨hp.1, fun z => ?_⟩
  rw [fullTour, hp.2.1]
  tauto

/-- `fullTour` starts with the head of `ord v`. -/
theorem fullTour_head? {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F) (v : ℕ)
    {a : End} (ha : (ord v).head? = some a) :
    (fullTour ord F hc.forest v).head? = some a := by
  have hchain : IsSuccChain (cycNext (ord v)) (ord v) :=
    ((isCycleOf_iff_cycNext (hc.nodup v)).mpr fun _ _ => rfl).1
  have hp := fullTourBlocks_props ord F hc F hc.forest
    ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩ v (ord v)
    (hc.nodup v) (fun _ h => h) (fun _ h _ => h) (fun _ h1 _ h2 => absurd h1 h2) hchain
  exact hp.2.2.1 a ha

/-- `fullTour` is empty iff `ord v` is empty. -/
theorem fullTour_eq_nil_iff {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F) (v : ℕ) :
    fullTour ord F hc.forest v = [] ↔ ord v = [] := by
  constructor
  · intro h
    cases ho : ord v with
    | nil => rfl
    | cons a rest =>
      have := fullTour_head? hc v (by rw [ho]; rfl)
      rw [h] at this; simp at this
  · intro h
    unfold fullTour
    rw [fullTourBlocks.eq_def, h]
    rfl

/-- `fullTour` is a cycle of `eulerSucc ord F`: every element's cyclic successor in `fullTour` is
`eulerSucc ord F`. -/
theorem fullTour_cycNext {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F) (v : ℕ) :
    ∀ z ∈ fullTour ord F hc.forest v,
      cycNext (fullTour ord F hc.forest v) z = eulerSucc ord F z := by
  have hcyc_v : IsCycleOf (cycNext (ord v)) (ord v) :=
    (isCycleOf_iff_cycNext (hc.nodup v)).mpr fun _ _ => rfl
  have hp := fullTourBlocks_props ord F hc F hc.forest
    ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩ v (ord v)
    (hc.nodup v) (fun _ h => h) (fun _ h _ => h) (fun _ h1 _ h2 => absurd h1 h2) hcyc_v.1
  apply (isCycleOf_iff_cycNext hp.1).mp
  refine ⟨hp.2.2.2.2, fun a b ha hb => ?_⟩
  cases ho : ord v with
  | nil =>
    have hnil : fullTour ord F hc.forest v = [] := (fullTour_eq_nil_iff hc v).mpr ho
    rw [fullTour] at hnil; rw [hnil] at ha; simp at ha
  | cons x rest =>
    obtain ⟨y, hy⟩ : ∃ y, (x :: rest).getLast? = some y :=
      Option.isSome_iff_exists.mp (by simp)
    have ha' : a = x := Option.some.inj (ha.symm.trans (hp.2.2.1 x (by rw [ho]; rfl)))
    have hb' : b = forestAlpha F y :=
      Option.some.inj (hb.symm.trans (hp.2.2.2.1 y (by rw [ho]; exact hy)))
    rw [ha', hb']
    have hy_ord : y ∈ ord v := by rw [ho]; exact List.mem_of_getLast? hy
    rw [eulerSucc_forestAlpha hc hy_ord]
    exact hcyc_v.2 x y (by rw [ho]; rfl) (by rw [ho]; exact hy)

/-- Rotating any cyclic rotation of `fullTour` at `r` to start at `(ord r)[0]` recovers
`fullTour` identically. -/
theorem rotateToList_fullTour_of_isRotated {ord : ℕ → List End} {F : MGraph}
    (hc : OrdForestCompat ord F) {r : ℕ} {a : End} {L : List End}
    (ha : (ord r).head? = some a) (hrot : L.IsRotated (fullTour ord F hc.forest r)) :
    rotateToList a L = fullTour ord F hc.forest r :=
  tour_rotateToList_eq_of_isRotated (fullTour_spec hc r).1 hrot (fullTour_head? hc r ha)

/-- Two vertices in the same forest component have rotated `fullTour`s. -/
theorem fullTour_isRotated_of_connected {ord : ℕ → List End} {F : MGraph}
    (hc : OrdForestCompat ord F) {u v : ℕ} (huv : F.Connected u v) :
    (fullTour ord F hc.forest u).IsRotated (fullTour ord F hc.forest v) := by
  cases ho : ord u with
  | nil =>
    have hnil : fullTour ord F hc.forest u = [] := (fullTour_eq_nil_iff hc u).mpr ho
    have hnil' : fullTour ord F hc.forest v = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      obtain ⟨w, hzw, hvw⟩ := (fullTour_spec hc v).2 z |>.mp hz
      have hzu := ((fullTour_spec hc u).2 z).mpr ⟨w, hzw, connected_trans huv hvw⟩
      rw [hnil] at hzu; simp at hzu
    rw [hnil, hnil']
  | cons a rest =>
    have hau : a ∈ fullTour ord F hc.forest u :=
      ((fullTour_spec hc u).2 a).mpr ⟨u, by rw [ho]; exact List.mem_cons_self, connected_refl F u⟩
    have hav : a ∈ fullTour ord F hc.forest v :=
      ((fullTour_spec hc v).2 a).mpr ⟨u, by rw [ho]; exact List.mem_cons_self, connected_symm huv⟩
    exact isRotated_of_cycNext_eq (fullTour_spec hc u).1 (fullTour_spec hc v).1 hau hav
      (fullTour_cycNext hc u) (fullTour_cycNext hc v)

/-- Adding a forest edge `e` between `u` and `v` in `F`. -/
def addForestEdge (F : MGraph) (e u v : ℕ) : MGraph where
  V := F.V
  E := insert e F.E
  tail := Function.update F.tail e u
  head := Function.update F.head e v

end MinCostFlow.SparseCore.Program
