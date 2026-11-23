module

public import MinCostFlow.LinkCut.Prog.MathForestCutInvs

/-!
# Components after `link` and `cut`

Facts about `MathForest.SameComp` that the forest model with roots (`LctForestModel.lean`)
needs. Adding an edge `{u, v}` joins the trees of `u` and `v` and nothing else
(`link_sameComp_iff`). Removing the edges `{x, y}` keeps every tree that does not contain `x`
(`cut_sameComp_of_not`), and splits the tree of `x` into the part of `x` and the part of `y`
(`cut_sameComp_split`). The empty forest has only one-vertex trees (`empty_sameComp`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open MinCostFlow.Rounding

namespace ForestComp

theorem empty_sameComp {n a b : ℕ} (h : (MathForest.empty n).SameComp a b) : a = b := by
  obtain ⟨es, hw⟩ := h
  cases hw with
  | nil _ => rfl
  | cons he _ _ => simp [MathForest.empty, MathForest.rawEdges] at he

/-- One edge of the forest joins its two ends. -/
theorem sameComp_of_edge {F : MathForest} {e : ForestEdge} (he : e ∈ F.edges) :
    F.SameComp e.u e.v :=
  ⟨[e.toRaw], .cons (List.mem_map.2 ⟨e, he, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (.nil _)⟩

/-- A walk in `F.link e` stays in the tree of its start, or crosses to the tree on the other
side of `e`. -/
theorem link_walk {F : MathForest} {e : ForestEdge} {a : ℕ} :
    ∀ {c b es}, IsWalk (F.link e).rawEdges c b es →
      (F.SameComp a c ∨ (F.SameComp a e.u ∧ F.SameComp c e.v) ∨
        (F.SameComp a e.v ∧ F.SameComp c e.u)) →
      (F.SameComp a b ∨ (F.SameComp a e.u ∧ F.SameComp b e.v) ∨
        (F.SameComp a e.v ∧ F.SameComp b e.u)) := by
  intro c b es hw
  induction hw with
  | nil _ => exact id
  | @cons c d b re es hre hcon _ ih =>
      intro hc
      apply ih
      simp only [MathForest.link, MathForest.rawEdges, List.map_cons, List.mem_cons] at hre
      rcases hre with rfl | hre
      · -- the new edge
        rcases hcon with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          simp only [ForestEdge.toRaw] at h1 h2 <;> subst h1 <;> subst h2
        · rcases hc with h | ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inr (Or.inl ⟨h, MathForest.SameComp.refl _ _⟩)
          · exact Or.inr (Or.inl ⟨h, MathForest.SameComp.refl _ _⟩)
          · exact Or.inl h
        · rcases hc with h | ⟨h, _⟩ | ⟨h, _⟩
          · exact Or.inr (Or.inr ⟨h, MathForest.SameComp.refl _ _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h, MathForest.SameComp.refl _ _⟩)
      · have hcd : F.SameComp c d :=
          ⟨[re], .cons hre hcon (.nil _)⟩
        rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans hcd)
        · exact Or.inr (Or.inl ⟨h1, hcd.symm.trans h2⟩)
        · exact Or.inr (Or.inr ⟨h1, hcd.symm.trans h2⟩)

/-- The trees of `F.link e`: two vertices are joined when they were joined in `F`, or when one
is in the tree of `e.u` and the other in the tree of `e.v`. -/
theorem link_sameComp_iff (F : MathForest) (e : ForestEdge) (a b : ℕ) :
    (F.link e).SameComp a b ↔ F.SameComp a b ∨ (F.SameComp a e.u ∧ F.SameComp b e.v) ∨
      (F.SameComp a e.v ∧ F.SameComp b e.u) := by
  have hsub : ∀ c d, F.SameComp c d → (F.link e).SameComp c d := fun c d ⟨es, hw⟩ =>
    ⟨es, hw.mono fun z hz => by
      simp only [MathForest.link, MathForest.rawEdges, List.map_cons, List.mem_cons]
      exact Or.inr hz⟩
  have hedge : (F.link e).SameComp e.u e.v :=
    sameComp_of_edge (F := F.link e) (by simp [MathForest.link])
  constructor
  · rintro ⟨es, hw⟩
    exact link_walk hw (Or.inl (MathForest.SameComp.refl _ _))
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hsub _ _ h
    · exact ((hsub _ _ h1).trans hedge).trans (hsub _ _ h2).symm
    · exact ((hsub _ _ h1).trans hedge.symm).trans (hsub _ _ h2).symm

/-- An edge of `F` that `cut x y` keeps. -/
theorem cut_mem_raw {F : MathForest} {x y : ℕ} {re : RawEdge} (hre : re ∈ F.rawEdges)
    (hkeep : ¬ ((re.u = x ∧ re.v = y) ∨ (re.u = y ∧ re.v = x))) : re ∈ (F.cut x y).rawEdges := by
  simp only [MathForest.rawEdges, List.mem_map] at hre ⊢
  obtain ⟨e, he, rfl⟩ := hre
  refine ⟨e, ?_, rfl⟩
  simp only [MathForest.cut, List.mem_filter, he, true_and]
  simp only [ForestEdge.toRaw] at hkeep
  by_cases h1 : e.u = x <;> by_cases h2 : e.v = y <;> by_cases h3 : e.u = y <;>
    by_cases h4 : e.v = x <;> simp_all

theorem cut_sameComp_mono {F : MathForest} {x y a b : ℕ} (h : (F.cut x y).SameComp a b) :
    F.SameComp a b := by
  obtain ⟨es, hw⟩ := h
  refine ⟨es, hw.mono fun z hz => ?_⟩
  simp only [MathForest.cut, MathForest.rawEdges, List.mem_map, List.mem_filter] at hz ⊢
  obtain ⟨e, ⟨he, _⟩, rfl⟩ := hz
  exact ⟨e, he, rfl⟩

/-- A walk of `F` from a vertex `c` is, after the cut, still a walk from `c`, or it reaches the
part of `x` or the part of `y`. -/
theorem cut_walk_split {F : MathForest} {x y : ℕ} :
    ∀ {c b es}, IsWalk F.rawEdges c b es →
      (F.cut x y).SameComp c b ∨ (F.cut x y).SameComp c x ∨ (F.cut x y).SameComp c y := by
  intro c b es hw
  induction hw with
  | nil a => exact Or.inl (MathForest.SameComp.refl _ _)
  | @cons c d b re es hre hcon _ ih =>
      by_cases hkeep : (re.u = x ∧ re.v = y) ∨ (re.u = y ∧ re.v = x)
      · -- the step uses a removed edge, so `c` is `x` or `y`
        have hc : c = x ∨ c = y := by
          rcases hcon with ⟨h1, _⟩ | ⟨_, h2⟩ <;> rcases hkeep with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
        rcases hc with rfl | rfl
        · exact Or.inr (Or.inl (MathForest.SameComp.refl _ _))
        · exact Or.inr (Or.inr (MathForest.SameComp.refl _ _))
      · have hcd : (F.cut x y).SameComp c d := ⟨[re], .cons (cut_mem_raw hre hkeep) hcon (.nil _)⟩
        rcases ih with h | h | h
        · exact Or.inl (hcd.trans h)
        · exact Or.inr (Or.inl (hcd.trans h))
        · exact Or.inr (Or.inr (hcd.trans h))

/-- After the cut, every vertex of the old tree of `x` is in the part of `x` or of `y`. -/
theorem cut_sameComp_split {F : MathForest} {x y a : ℕ} (h : F.SameComp a x) :
    (F.cut x y).SameComp a x ∨ (F.cut x y).SameComp a y := by
  obtain ⟨es, hw⟩ := h
  rcases cut_walk_split (x := x) (y := y) hw with h | h | h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

/-- A tree without `x` loses no edge. -/
theorem cut_sameComp_of_not {F : MathForest} {x y a : ℕ} (hnx : ¬ F.SameComp a x) :
    ∀ {c b es}, F.SameComp a c → IsWalk F.rawEdges c b es → (F.cut x y).SameComp c b := by
  intro c b es hac hw
  induction hw with
  | nil a => exact MathForest.SameComp.refl _ _
  | @cons c d b re es hre hcon _ ih =>
      have hcd : F.SameComp c d := ⟨[re], .cons hre hcon (.nil _)⟩
      have hkeep : ¬ ((re.u = x ∧ re.v = y) ∨ (re.u = y ∧ re.v = x)) := by
        intro hk
        have hxy : F.SameComp x y := by
          rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1 ▸ h2 ▸ ⟨[re], .cons hre (Or.inl ⟨rfl, rfl⟩) (.nil _)⟩
          · exact h1 ▸ h2 ▸ MathForest.SameComp.symm
              (⟨[re], .cons hre (Or.inl ⟨rfl, rfl⟩) (.nil _)⟩ : F.SameComp re.u re.v)
        have hc : c = x ∨ c = y := by
          rcases hcon with ⟨h1, _⟩ | ⟨_, h2⟩ <;> rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
        rcases hc with rfl | rfl
        · exact hnx hac
        · exact hnx (hac.trans hxy.symm)
      exact MathForest.SameComp.trans
        (⟨[re], .cons (cut_mem_raw hre hkeep) hcon (.nil _)⟩ : (F.cut x y).SameComp c d)
        (ih (hac.trans hcd))

/-- If `cut x y` changes the forest, some edge joins `x` and `y`. -/
theorem sameComp_of_cut_ne {F : MathForest} {x y : ℕ} (h : F.cut x y ≠ F) : F.SameComp x y := by
  by_contra hno
  apply h
  have hfil : F.edges.filter
      (fun e => !((e.u == x && e.v == y) || (e.u == y && e.v == x))) = F.edges := by
    rw [List.filter_eq_self]
    intro e he
    have hs := sameComp_of_edge he
    by_cases h1 : e.u = x ∧ e.v = y
    · rw [h1.1, h1.2] at hs; exact absurd hs hno
    by_cases h2 : e.u = y ∧ e.v = x
    · rw [h2.1, h2.2] at hs; exact absurd hs.symm hno
    have h1' : (e.u == x && e.v == y) = false := by
      by_cases ha : e.u = x
      · have hb : e.v ≠ y := fun hb => h1 ⟨ha, hb⟩
        simp [hb]
      · simp [ha]
    have h2' : (e.u == y && e.v == x) = false := by
      by_cases ha : e.u = y
      · have hb : e.v ≠ x := fun hb => h2 ⟨ha, hb⟩
        simp [hb]
      · simp [ha]
    simp [h1', h2']
  cases F
  simp only [MathForest.cut] at hfil ⊢
  rw [hfil]

end ForestComp

end MinCostFlow.LinkCut.Prog
