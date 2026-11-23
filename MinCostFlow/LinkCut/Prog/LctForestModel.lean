module

public import MinCostFlow.LinkCut.Prog.LctForestComp

/-!
# A forest model that remembers roots

The solver's contract (`forestMachineContract`) asks `findRoot` to return `D.findRoot s v`, a
function of the abstract state. The link-cut tree answers the root of the rooted tree that its
memory represents, and this root moves under `link` and `cut`. So the abstract state here is a
forest together with a root map, `MathForest × (ℕ → ℕ)`, and the operations move the roots the
same way the program does:

* `link e` gives every vertex in the tree of `e.u` the root of `e.v`;
* `cut x y` with `x, y < n` makes `x` the root of its tree; if an edge `{x, y}` is removed,
  the part of `y` gets root `y`;
* `pathAdd` keeps the roots.

`RootsOk F r` says that `r` is zero outside the vertices and picks, in each tree, one vertex of
that tree. The main result is `lctForestModel_isSpec`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open MinCostFlow.Rounding ForestComp Classical

noncomputable section

/-- The root map `r` is zero outside the vertices, and inside it picks one vertex of each tree. -/
def RootsOk (F : MathForest) (r : ℕ → ℕ) : Prop :=
  (∀ z, F.n ≤ z → r z = 0) ∧
  ∀ v < F.n, r v < F.n ∧ F.SameComp v (r v) ∧ ∀ u < F.n, (r u = r v ↔ F.SameComp u v)

/-- Keep a root map only on the vertices `0 .. n - 1`. -/
def rootsOn (n : ℕ) (r : ℕ → ℕ) : ℕ → ℕ := fun z => if z < n then r z else 0

/-- The roots after `link e`. -/
def lctLinkRoots (F : MathForest) (r : ℕ → ℕ) (e : ForestEdge) : ℕ → ℕ :=
  rootsOn F.n fun z => if r z = r e.u then r e.v else r z

/-- The roots after `cut x y`. -/
def lctCutRoots (F : MathForest) (r : ℕ → ℕ) (x y : ℕ) : ℕ → ℕ :=
  rootsOn F.n fun z =>
    if x < F.n ∧ y < F.n then
      if F.cut x y = F then (if r z = r x then x else r z)
      else if (F.cut x y).SameComp z y then y
      else if (F.cut x y).SameComp z x then x
      else r z
    else r z

/-- The dynamic forest with a root map, matching the link-cut program. -/
def lctForestModel : DynForest where
  State := MathForest × (ℕ → ℕ)
  Inv s := s.1.Valid ∧ RootsOk s.1 s.2
  toForest s := s.1
  init n := (MathForest.empty n, rootsOn n id)
  findRoot s v := s.2 v
  link s e := (s.1.link e, lctLinkRoots s.1 s.2 e)
  cut s x y := (s.1.cut x y, lctCutRoots s.1 s.2 x y)
  pathAdd s u v δ := (s.1.pathAdd u v δ, s.2)
  pathMin s u v := s.1.pathMin u v
  pathSum s u v := s.1.pathSum u v

theorem rootsOn_eq_self {F : MathForest} {r : ℕ → ℕ} (h : RootsOk F r) : rootsOn F.n r = r := by
  funext z
  unfold rootsOn
  split_ifs with hz
  · rfl
  · exact (h.1 z (by omega)).symm

/-- A vertex is in the tree of its root. -/
theorem RootsOk.root_root {F : MathForest} {r : ℕ → ℕ} (h : RootsOk F r) {v : ℕ} (hv : v < F.n) :
    r (r v) = r v :=
  ((h.2 v hv).2.2 (r v) (h.2 v hv).1).2 (h.2 v hv).2.1.symm

/-- If `r a` is the vertex `c`, then `a` is in the tree of `c`. -/
theorem RootsOk.sameComp_of_eq {F : MathForest} {r : ℕ → ℕ} (h : RootsOk F r) {a c : ℕ}
    (ha : a < F.n) (hc : r a = c) : F.SameComp a c :=
  hc ▸ (h.2 a ha).2.1

theorem rootsOk_init (n : ℕ) : RootsOk (MathForest.empty n) (rootsOn n id) := by
  refine ⟨fun z hz => by simp [rootsOn, MathForest.empty] at hz ⊢; omega, fun v hv => ?_⟩
  simp only [MathForest.empty] at hv ⊢
  refine ⟨by simp [rootsOn, hv], by simp [rootsOn, hv]; exact MathForest.SameComp.refl _ _,
    fun u hu => ?_⟩
  simp only [rootsOn, hu, hv, ↓reduceIte, id]
  exact ⟨fun h => h ▸ MathForest.SameComp.refl _ _, empty_sameComp⟩

theorem rootsOk_link {F : MathForest} {r : ℕ → ℕ} (h : RootsOk F r) (e : ForestEdge)
    (hu : e.u < F.n) (hv : e.v < F.n) : RootsOk (F.link e) (lctLinkRoots F r e) := by
  have hn : (F.link e).n = F.n := rfl
  have hval : ∀ z < F.n, lctLinkRoots F r e z = if r z = r e.u then r e.v else r z :=
    fun z hz => by simp [lctLinkRoots, rootsOn, hz]
  have hcu : ∀ z < F.n, (r z = r e.u ↔ F.SameComp z e.u) := fun z hz => (h.2 e.u hu).2.2 z hz
  refine ⟨fun z hz => by simp [lctLinkRoots, rootsOn]; omega, fun v hv' => ?_⟩
  rw [hn] at hv'
  refine ⟨?_, ?_, fun u hu' => ?_⟩
  · rw [hval v hv']; split_ifs
    · exact (h.2 e.v hv).1
    · exact (h.2 v hv').1
  · rw [hval v hv', link_sameComp_iff]
    split_ifs with hvu
    · exact Or.inr (Or.inl ⟨(hcu v hv').1 hvu, (h.2 e.v hv).2.1.symm⟩)
    · exact Or.inl (h.2 v hv').2.1
  · rw [hn] at hu'
    rw [hval u hu', hval v hv', link_sameComp_iff]
    have hiff := (h.2 v hv').2.2 u hu'
    have hvv := (h.2 e.v hv).2.2
    by_cases hu1 : F.SameComp u e.u <;> by_cases hv1 : F.SameComp v e.u
    · simp only [(hcu u hu').2 hu1, (hcu v hv').2 hv1, ↓reduceIte, true_iff]
      exact Or.inl (hu1.trans hv1.symm)
    · simp only [(hcu u hu').2 hu1, show ¬ r v = r e.u from fun h' => hv1 ((hcu v hv').1 h'),
        ↓reduceIte]
      rw [eq_comm, hvv v hv']
      constructor
      · intro hve; exact Or.inr (Or.inl ⟨hu1, hve⟩)
      · rintro (h' | ⟨_, h'⟩ | ⟨_, h'⟩)
        · exact absurd (h'.symm.trans hu1) hv1
        · exact h'
        · exact absurd h' hv1
    · simp only [(hcu v hv').2 hv1, show ¬ r u = r e.u from fun h' => hu1 ((hcu u hu').1 h'),
        ↓reduceIte]
      rw [hvv u hu']
      constructor
      · intro hue; exact Or.inr (Or.inr ⟨hue, hv1⟩)
      · rintro (h' | ⟨h', _⟩ | ⟨h', _⟩)
        · exact absurd (h'.trans hv1) hu1
        · exact absurd h' hu1
        · exact h'
    · simp only [show ¬ r u = r e.u from fun h' => hu1 ((hcu u hu').1 h'),
        show ¬ r v = r e.u from fun h' => hv1 ((hcu v hv').1 h'), ↓reduceIte]
      rw [hiff]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h', _⟩ | ⟨_, h'⟩)
        · exact h'
        · exact absurd h' hu1
        · exact absurd h' hv1

/-- The roots after a cut that changes nothing but the root of the tree of `x`. -/
theorem rootsOk_reroot {F : MathForest} {r : ℕ → ℕ} (h : RootsOk F r) {x : ℕ} (hx : x < F.n) :
    RootsOk F (rootsOn F.n fun z => if r z = r x then x else r z) := by
  have hval : ∀ z < F.n, (rootsOn F.n fun z => if r z = r x then x else r z) z =
      if r z = r x then x else r z := fun z hz => by simp [rootsOn, hz]
  have hcx : ∀ z < F.n, (r z = r x ↔ F.SameComp z x) := fun z hz => (h.2 x hx).2.2 z hz
  refine ⟨fun z hz => by simp [rootsOn]; omega, fun v hv => ?_⟩
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · rw [hval v hv]; split_ifs
    · exact hx
    · exact (h.2 v hv).1
  · rw [hval v hv]; split_ifs with hvx
    · exact (hcx v hv).1 hvx
    · exact (h.2 v hv).2.1
  · rw [hval u hu, hval v hv, ← (h.2 v hv).2.2 u hu]
    by_cases hu1 : r u = r x <;> by_cases hv1 : r v = r x
    · simp only [hu1, hv1, ↓reduceIte]
    · simp only [hu1, hv1, ↓reduceIte]
      constructor
      · intro hxv
        have : r v = r x := by
          calc r v = r (r v) := (h.root_root hv).symm
            _ = r x := by rw [← hxv]
        exact absurd this hv1
      · intro huv; exact absurd huv.symm hv1
    · simp only [hu1, hv1, ↓reduceIte]
      constructor
      · intro hux
        have : r u = r x := by
          calc r u = r (r u) := (h.root_root hu).symm
            _ = r x := by rw [hux]
        exact absurd this hu1
      · intro huv; exact huv.elim
    · simp only [hu1, hv1, ↓reduceIte]

theorem rootsOk_cut {F : MathForest} {r : ℕ → ℕ} (hV : F.Valid) (h : RootsOk F r) (x y : ℕ) :
    RootsOk (F.cut x y) (lctCutRoots F r x y) := by
  have hn : (F.cut x y).n = F.n := rfl
  by_cases hgood : x < F.n ∧ y < F.n
  swap
  · have hcut : F.cut x y = F := cut_eq_self_of_bad_args hV (by omega)
    have hr : lctCutRoots F r x y = r := by
      unfold lctCutRoots
      simp only [hgood, ↓reduceIte]
      exact rootsOn_eq_self h
    rw [hr, hcut]
    exact h
  by_cases hcut : F.cut x y = F
  · have hr : lctCutRoots F r x y = rootsOn F.n fun z => if r z = r x then x else r z := by
      unfold lctCutRoots
      simp only [hgood, hcut, and_self, ↓reduceIte]
    rw [hr, hcut]
    exact rootsOk_reroot h hgood.1
  -- an edge `{x, y}` is removed
  obtain ⟨hx, hy⟩ := hgood
  set F' := F.cut x y with hF'
  have hxy : F.SameComp x y := sameComp_of_cut_ne hcut
  have hval : ∀ z < F.n, lctCutRoots F r x y z =
      if F'.SameComp z y then y else if F'.SameComp z x then x else r z := fun z hz => by
    simp [lctCutRoots, rootsOn, hz, hx, hy, hcut, F']
  -- a vertex in neither part is outside the old tree of `x`
  have hout : ∀ a, ¬ F'.SameComp a y → ¬ F'.SameComp a x → ¬ F.SameComp a x := fun a hny hnx hax =>
    (cut_sameComp_split hax).elim hnx hny
  have hpres : ∀ a b, ¬ F.SameComp a x → (F.SameComp a b ↔ F'.SameComp a b) := fun a b hnx =>
    ⟨fun ⟨_, hw⟩ => cut_sameComp_of_not hnx (MathForest.SameComp.refl _ _) hw,
      cut_sameComp_mono⟩
  have hrx : ∀ a < F.n, r a = x → F.SameComp a x := fun a ha hra => h.sameComp_of_eq ha hra
  have hry : ∀ a < F.n, r a = y → F.SameComp a x := fun a ha hra =>
    (h.sameComp_of_eq ha hra).trans hxy.symm
  have hxney : x ≠ y := fun he => by
    apply hcut
    exact cut_eq_self_of_bad_args hV (Or.inr (Or.inr he))
  refine ⟨fun z hz => by simp [lctCutRoots, rootsOn]; omega, fun v hv' => ?_⟩
  rw [hn] at hv'
  refine ⟨?_, ?_, fun u hu' => ?_⟩
  · rw [hval v hv']; split_ifs
    · exact hy
    · exact hx
    · exact (h.2 v hv').1
  · rw [hval v hv']; split_ifs with h1 h2
    · exact h1
    · exact h2
    · exact (hpres v (r v) (hout v h1 h2)).1 (h.2 v hv').2.1
  · rw [hn] at hu'
    rw [hval u hu', hval v hv']
    by_cases hu1 : F'.SameComp u y <;> by_cases hv1 : F'.SameComp v y
    · simp only [hu1, hv1, ↓reduceIte, true_iff]; exact hu1.trans hv1.symm
    · simp only [hu1, hv1, ↓reduceIte]
      constructor
      · intro hyv
        split_ifs at hyv with hv2
        · exact absurd hyv.symm hxney
        · exact absurd (hry v hv' hyv.symm) (hout v hv1 hv2)
      · intro huv; exact absurd (huv.symm.trans hu1) hv1
    · simp only [hu1, hv1, ↓reduceIte]
      constructor
      · intro hyu
        split_ifs at hyu with hu2
        · exact absurd hyu hxney
        · exact absurd (hry u hu' hyu) (hout u hu1 hu2)
      · intro huv; exact absurd (huv.trans hv1) hu1
    · simp only [hu1, hv1, ↓reduceIte]
      by_cases hu2 : F'.SameComp u x <;> by_cases hv2 : F'.SameComp v x
      · simp only [hu2, hv2, ↓reduceIte, true_iff]; exact hu2.trans hv2.symm
      · simp only [hu2, hv2, ↓reduceIte]
        constructor
        · intro hxv; exact absurd (hrx v hv' hxv.symm) (hout v hv1 hv2)
        · intro huv; exact absurd (huv.symm.trans hu2) hv2
      · simp only [hu2, hv2, ↓reduceIte]
        constructor
        · intro hux; exact absurd (hrx u hu' hux) (hout u hu1 hu2)
        · intro huv; exact absurd (huv.trans hv2) hu2
      · simp only [hu2, hv2, ↓reduceIte]
        rw [(h.2 v hv').2.2 u hu']
        exact hpres u v (hout u hu1 hu2)

/-- The forest model with roots meets `DynForest.IsSpec`. -/
theorem lctForestModel_isSpec : lctForestModel.IsSpec := by
  refine ⟨fun n => ⟨⟨MathForest.empty_valid n, rootsOk_init n⟩, MathForest.SameState.refl _⟩,
    fun st hst => hst.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st v hst hv
    exact ⟨(hst.2.2 v hv).1, fun u hu => (hst.2.2 v hv).2.2 u hu⟩
  · intro st e hst hu hv hdisc heid
    exact ⟨⟨MathForest.link_valid hst.1 hu hv hdisc heid, rootsOk_link hst.2 e hu hv⟩,
      MathForest.SameState.refl _⟩
  · intro st x y hst
    exact ⟨⟨MathForest.cut_valid hst.1 x y, rootsOk_cut hst.1 hst.2 x y⟩,
      MathForest.SameState.refl _⟩
  · intro st u v δ hst _
    refine ⟨⟨MathForest.pathAdd_valid hst.1 u v δ, ?_⟩, MathForest.SameState.refl _⟩
    show RootsOk (st.1.pathAdd u v δ) st.2
    have hn : (st.1.pathAdd u v δ).n = st.1.n := by
      unfold MathForest.pathAdd; split <;> rfl
    obtain ⟨h1, h2⟩ := hst.2
    refine ⟨fun z hz => h1 z (by rw [← hn]; exact hz), fun w hw => ?_⟩
    rw [hn] at hw
    obtain ⟨a1, a2, a3⟩ := h2 w hw
    refine ⟨by rw [hn]; exact a1, (MathForest.pathAdd_sameComp _ _ _ _ _ _).2 a2,
      fun u' hu' => ?_⟩
    rw [hn] at hu'
    rw [a3 u' hu', MathForest.pathAdd_sameComp]
  · intro st u v _ _; rfl
  · intro st u v _ _; rfl

end

end MinCostFlow.LinkCut.Prog
