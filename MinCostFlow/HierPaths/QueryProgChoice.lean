module

public import MinCostFlow.HierPaths.QueryProgPick

/-!
# Agreement of connector choices in the routing recursion

Each recursive call stays within one group and uses surviving terminals. Thus the
connector read from the pair cursor agrees with the model at every call.
-/

public section

namespace MinCostFlow.HierPaths

namespace HierConcrete

/-- At a split of a group containing surviving terminals, the table returns the model's entry. -/
theorem tablePick_for_eq (X : HierConcrete) {ξ κ : ℕ}
    (hA : X.H.A.Spec X.ms.abs.G ξ κ) (hP : X.H.A.PairSpec X.H.pairIdx) {i a b : ℕ}
    (hi : i < X.depth) (ha : a ∈ X.H.A.surv X.ms.st) (hb : b ∈ X.H.A.surv X.ms.st)
    (hgroup : groupOf X.H.A.x X.H.A.b i a = groupOf X.H.A.x X.H.A.b i b)
    (hne : groupOf X.H.A.x X.H.A.b (i + 1) a ≠ groupOf X.H.A.x X.H.A.b (i + 1) b) :
    pickFor (groupOf X.H.A.x X.H.A.b) X.tablePick i a b =
      pickFor (groupOf X.H.A.x X.H.A.b) (X.H.A.pick X.H.pairIdx X.ms.st) i a b := by
  apply X.tablePick_eq_pick hi _ hne _ _ hP
  · simpa only [parentGroup, groupOf_succ_div] using hgroup
  · apply groupOf_lt_numGroups
    rw [← hA.numTerm_eq]
    exact ((X.H.A.mem_surv).mp ha).1
  · apply groupOf_lt_numGroups
    rw [← hA.numTerm_eq]
    exact ((X.H.A.mem_surv).mp hb).1

/-- The table gives an eligible connector on each split visited by the query. -/
theorem tablePick_isConnectorChoice (X : HierConcrete) {ξ κ : ℕ}
    (hA : X.H.A.Spec X.ms.abs.G ξ κ) (hP : X.H.A.PairSpec X.H.pairIdx)
    (hinv : X.H.A.DelInv X.ms.abs.G X.ms.st) :
    X.H.A.C.IsConnectorChoice (groupOf X.H.A.x X.H.A.b) X.tablePick (X.H.A.surv X.ms.st) := by
  intro i u v hu hv hgroup hne
  have hi : i < X.depth := by
    by_contra! hd
    have h₀ := groupSize_eq_one hA.b_pos hd
    have h₁ := groupSize_eq_one hA.b_pos (hd.trans (Nat.le_succ i))
    simp only [groupOf, h₀, Nat.div_one] at hgroup
    simp only [groupOf, h₁, Nat.div_one] at hne
    exact hne hgroup
  have h := X.H.A.C.isConnectorChoice_of_sibling (X.H.A.isSiblingChoice_pick hA hP hinv)
    i u v hu hv hgroup hne
  have he := X.tablePick_for_eq hA hP hi hu hv hgroup hne
  unfold pickFor at he
  rw [he]
  exact h

/-- The pair tables give the model's route and operation count on surviving terminals. -/
theorem tablePick_route_eq (X : HierConcrete) {ξ κ : ℕ}
    (hA : X.H.A.Spec X.ms.abs.G ξ κ) (hP : X.H.A.PairSpec X.H.pairIdx)
    (hinv : X.H.A.DelInv X.ms.abs.G X.ms.st)
    (k j u v : ℕ) (hd : j + k ≤ X.depth)
    (hu : u ∈ X.H.A.surv X.ms.st) (hv : v ∈ X.H.A.surv X.ms.st)
    (hg : groupOf X.H.A.x X.H.A.b j u = groupOf X.H.A.x X.H.A.b j v) :
    let group := groupOf X.H.A.x X.H.A.b
    let pick := X.H.A.pick X.H.pairIdx X.ms.st
    X.H.A.C.route group X.tablePick k j u v = X.H.A.C.route group pick k j u v ∧
      X.H.A.C.routeOps group X.tablePick k j u v = X.H.A.C.routeOps group pick k j u v := by
  dsimp only
  apply X.H.A.C.route_congr_choice hA.fits
    (X.H.A.C.isConnectorChoice_of_sibling (X.H.A.isSiblingChoice_pick hA hP hinv)) _ k j u v hd hu hv hg
  intro i u v hi hu hv hg hne
  exact X.tablePick_for_eq hA hP hi hu hv hg hne

end HierConcrete

end MinCostFlow.HierPaths
