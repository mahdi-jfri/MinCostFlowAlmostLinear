module

public import MinCostFlow.SparseCore.Program.CompSplitListModel
public import MinCostFlow.Bundle.ForestStep
import MinCostFlow.LSF.Lemma54Split
import MinCostFlow.SparseCore.CompLSFBridge
import Mathlib.Tactic.Linarith

/-!
# Reverse Union-Find Model and Exact Equivalence to `canonStepSplits` (`CompSplitListUF`)

Proves the pure mathematical correctness of computing `canonStepSplits cs u` by processing the
sorted released forest edges `D = (F_mid.E \ F'.E).sort (· ≤ ·)` in reverse order
`i = t - 1, ..., 0` with a union-by-size disjoint-set forest over the final roots `R_fin`:

1. Forest-cut component partition lemmas (`eraseForestEdge_compOf_split`,
   `applySplit_compOf_split`) and canonical pair extraction (`canonCut_pair_eq`,
   `canonInputSplit_pair_eq`).
2. `RevUFState` (`par`, `sz`, `minF`, `oldR`), lazy singleton initialization `ufInitOne`,
   bounded-depth parent walk `ufFindFuel`, union-by-size `ufUnion`, pair query `ufPair`,
   and the representation invariant `RevUFInv`.
3. `revUF_releases_eq` and `revUF_input_eq`: starting from all-zero `RevUFState.zero` on `F'`,
   adding `D[t-1], ..., D[0]` in reverse order computes every release entry
   `(releasesSplitEntries R_fin (inputMid cs u) D)[i]` exactly, and the final query on `(x0, y0)`
   computes `inputSplitEntries cs u` exactly.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Forest cut and vertex-split component partition lemmas -/

/-- A walk in `F` that avoids edge `e` is a walk in `eraseForestEdge F e`. -/
lemma isWalk_eraseForestEdge_of_notMem {F : MGraph} {e u v : ℕ} {P : List (ℕ × Bool)}
    (hW : F.IsWalk u v P) (hno : ∀ x ∈ P, x.1 ≠ e) :
    (eraseForestEdge F e).IsWalk u v P := by
  induction hW with
  | nil s => exact .nil s
  | @cons a b x xs he hsrc hrest ih =>
    have hne : x.1 ≠ e := hno x (List.mem_cons_self ..)
    exact .cons (Finset.mem_erase.mpr ⟨hne, he⟩) hsrc
      (ih fun y hy => hno y (List.mem_cons_of_mem _ hy))

/-- In a forest `F`, cutting edge `e ∈ F.E` splits `compOf F (F.tail e)` into the disjoint union
`compOf (eraseForestEdge F e) (F.tail e) ∪ compOf (eraseForestEdge F e) (F.head e)`, leaving all
other components unchanged. -/
theorem eraseForestEdge_compOf_split {F : MGraph} (hF : F.IsForest) {e : ℕ} (he : e ∈ F.E) :
    let F' := eraseForestEdge F e
    let a := F.tail e
    let b := F.head e
    let A := compOf F' a
    let B := compOf F' b
    Disjoint A B ∧
    compOf F a = A ∪ B ∧
    ∀ x ∈ F.V, x ∉ A ∪ B → compOf F x = compOf F' x := by
  intro F' a b A B
  have hsub : F.IsSubgraph F' := eraseForestEdge_subgraph F e
  have hF'v : F'.V = F.V := rfl
  have habV : a ∈ F.V ∧ b ∈ F.V := hF.1 e he
  have hnotab : ¬ F'.Connected a b := not_connected_eraseForestEdge hF (x := (e, true)) he
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hnotab (connected_trans (mem_compOf_iff.mp hxA).2 (connected_symm (mem_compOf_iff.mp hxB).2))
  -- Any walk in `F` either avoids `e` (so lives in `F'`) or crosses `e` (connecting endpoints to `{a, b}`).
  have hsplit_conn : ∀ x y, F.Connected x y →
      F'.Connected x y ∨ (F'.Connected x a ∧ F'.Connected b y) ∨ (F'.Connected x b ∧ F'.Connected a y) := by
    intro x y ⟨P, hW⟩
    induction hW with
    | nil s => exact Or.inl (connected_refl F' s)
    | @cons u1 vEnd z rest hzE hsrc hrest ih =>
      by_cases hze : z.1 = e
      · rcases z with ⟨f, dir⟩
        change f = e at hze; subst hze
        cases dir
        · -- `(e, false)`: `src = head e = b`, `dst = tail e = a`
          simp only [MGraph.src, MGraph.dst] at hsrc ih
          rw [← hsrc]
          rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
          · exact Or.inr (Or.inr ⟨connected_refl F' b, h⟩)
          · exact Or.inl h2
          · exact Or.inr (Or.inr ⟨connected_refl F' b, h2⟩)
        · -- `(e, true)`: `src = tail e = a`, `dst = head e = b`
          simp only [MGraph.src, MGraph.dst] at hsrc ih
          rw [← hsrc]
          rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
          · exact Or.inr (Or.inl ⟨connected_refl F' a, h⟩)
          · exact Or.inr (Or.inl ⟨connected_refl F' a, h2⟩)
          · exact Or.inl h2
      · have hstep : F'.Connected u1 (F.dst z) :=
          ⟨[z], .cons (Finset.mem_erase.mpr ⟨hze, hzE⟩) hsrc (.nil _)⟩
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (connected_trans hstep h)
        · exact Or.inr (Or.inl ⟨connected_trans hstep h1, h2⟩)
        · exact Or.inr (Or.inr ⟨connected_trans hstep h1, h2⟩)
  have hcomp_eq : compOf F a = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_union, mem_compOf_iff, hF'v]
    constructor
    · rintro ⟨hxV, hax⟩
      rcases hsplit_conn a x hax with h | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inl ⟨hxV, h⟩
      · exact Or.inr ⟨hxV, h2⟩
      · exact absurd h1 hnotab
    · rintro (⟨hxV, h⟩ | ⟨hxV, h⟩)
      · exact ⟨hxV, connected_of_subgraph hsub h⟩
      · exact ⟨hxV, connected_trans (connected_of_edge he) (connected_of_subgraph hsub h)⟩
  refine ⟨hdisj, hcomp_eq, fun x hxV hxnot => ?_⟩
  ext y
  simp only [mem_compOf_iff, hF'v]
  constructor
  · rintro ⟨hyV, hxy⟩
    refine ⟨hyV, ?_⟩
    have hxF' : x ∈ F'.V := hF'v.symm ▸ hxV
    rcases hsplit_conn x y hxy with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd (Finset.mem_union_left _ (mem_compOf_iff (G := F').mpr ⟨hxF', connected_symm h1⟩)) hxnot
    · exact absurd (Finset.mem_union_right _ (mem_compOf_iff (G := F').mpr ⟨hxF', connected_symm h1⟩)) hxnot
  · rintro ⟨hyV, hxy⟩
    exact ⟨hyV, connected_of_subgraph hsub hxy⟩

/-- Splitting vertex `v ∈ F.V` into `(v, v')` (`v' ∉ F.V`) in a forest `F` splits `compOf F v`
into two disjoint components `A = compOf F' v` and `B = compOf F' v'` of
`F' = F.applyUpdate (.split v v' St Sh)`, with `∀ r ∈ F.V, r ∈ A ∪ B ↔ r ∈ compOf F v`. -/
theorem applySplit_compOf_split {F : MGraph} (hF : F.IsForest) {v v' : ℕ}
    (hv : v ∈ F.V) (hv' : v' ∉ F.V) (St Sh : Finset ℕ) :
    let F' := F.applyUpdate (.split v v' St Sh)
    let A := compOf F' v
    let B := compOf F' v'
    Disjoint A B ∧
    (∀ r ∈ F.V, r ∈ A ∪ B ↔ r ∈ compOf F v) ∧
    (∀ x ∈ F.V, x ∉ A ∪ B → compOf F x = compOf F' x) := by
  intro F' A B
  have hF'V : F'.V = insert v' F.V := rfl
  let proj : ℕ → ℕ := fun x => if x = v' then v else x
  have hproj_e : ∀ e ∈ F'.E, e ∈ F.E ∧ proj (F'.tail e) = F.tail e ∧ proj (F'.head e) = F.head e := by
    intro e he
    have heF := hF.1 e he
    have htn : F.tail e ≠ v' := fun h => hv' (h ▸ heF.1)
    have hhn : F.head e ≠ v' := fun h => hv' (h ▸ heF.2)
    refine ⟨he, ?_, ?_⟩
    · by_cases ht : e ∈ St ∧ F.tail e = v <;> simp [F', MGraph.applyUpdate, proj, ht, htn]
    · by_cases hh : e ∈ Sh ∧ F.head e = v <;> simp [F', MGraph.applyUpdate, proj, hh, hhn]
  have hnotvv' : ¬ F'.Connected v v' := applySplit_separates hF hv hv' St Sh
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hnotvv' (connected_trans (mem_compOf_iff.mp hxA).2 (connected_symm (mem_compOf_iff.mp hxB).2))
  -- Lifting any walk in `F` to `F'`: each step either stays in `F'` or passes through `{v, v'}`.
  have hlift : ∀ x y, F.Connected x y →
      F'.Connected x y ∨
      (F'.Connected x v ∧ F'.Connected v' y) ∨
      (F'.Connected x v' ∧ F'.Connected v y) := by
    intro x y ⟨P, hW⟩
    induction hW with
    | nil s => exact Or.inl (connected_refl F' s)
    | @cons a vEnd z rest hzE hsrc hrest ih =>
      set mid := F.dst z
      have hedge : F'.Connected (F'.src z) (F'.dst z) :=
        ⟨[z], .cons hzE rfl (.nil _)⟩
      have hsrc_cases : F'.src z = a ∨ (a = v ∧ F'.src z = v') := by
        rcases z with ⟨e, dir⟩
        cases dir <;> simp only [MGraph.src, F', MGraph.applyUpdate] at hsrc ⊢
        · by_cases h : e ∈ Sh ∧ F.head e = v
          · right; exact ⟨hsrc.symm.trans h.2, by simp [h]⟩
          · left; simp [h]; exact hsrc
        · by_cases h : e ∈ St ∧ F.tail e = v
          · right; exact ⟨hsrc.symm.trans h.2, by simp [h]⟩
          · left; simp [h]; exact hsrc
      have hdst_cases : F'.dst z = mid ∨ (mid = v ∧ F'.dst z = v') := by
        rcases z with ⟨e, dir⟩
        cases dir <;> simp only [mid, MGraph.dst, F', MGraph.applyUpdate]
        · by_cases h : e ∈ St ∧ F.tail e = v
          · right; exact ⟨h.2, by simp [h]⟩
          · left; simp [h]
        · by_cases h : e ∈ Sh ∧ F.head e = v
          · right; exact ⟨h.2, by simp [h]⟩
          · left; simp [h]
      rcases hsrc_cases with hs1 | ⟨ha_v, hs2⟩ <;> rcases hdst_cases with hd1 | ⟨hm_v, hd2⟩
      · have ham' : F'.Connected a mid := hs1 ▸ hd1 ▸ hedge
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (connected_trans ham' h)
        · exact Or.inr (Or.inl ⟨connected_trans ham' h1, h2⟩)
        · exact Or.inr (Or.inr ⟨connected_trans ham' h1, h2⟩)
      · have hav' : F'.Connected a v' := hs1 ▸ hd2 ▸ hedge
        rw [hm_v] at ih
        rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inr ⟨hav', h⟩)
        · exact Or.inl (connected_trans hav' h2)
        · exact Or.inr (Or.inr ⟨hav', h2⟩)
      · have hv'm : F'.Connected v' mid := hs2 ▸ hd1 ▸ hedge
        rw [ha_v]
        rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inl ⟨connected_refl F' v, connected_trans hv'm h⟩)
        · exact Or.inr (Or.inl ⟨connected_refl F' v, h2⟩)
        · exact Or.inl (connected_trans (connected_refl F' v) h2)
      · rw [ha_v]; rw [hm_v] at ih
        rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨connected_refl F' v, h2⟩)
        · exact Or.inl h2
  have hmem_iff : ∀ r ∈ F.V, r ∈ A ∪ B ↔ r ∈ compOf F v := by
    intro r hrF
    have hrv' : r ≠ v' := fun h => hv' (h ▸ hrF)
    simp only [A, B, Finset.mem_union, mem_compOf_iff, hF'V, Finset.mem_insert, hrv', false_or, hrF, true_and]
    constructor
    · rintro (h | h)
      · obtain ⟨P, hW⟩ := h
        have hP := proj_isWalk hproj_e hW
        simp only [proj, hrv', ↓reduceIte, show v ≠ v' from fun h => hv' (h ▸ hv)] at hP
        exact ⟨P, hP⟩
      · obtain ⟨P, hW⟩ := h
        have hP := proj_isWalk hproj_e hW
        simp only [proj, hrv', ↓reduceIte] at hP
        exact ⟨P, hP⟩
    · intro hvr
      rcases hlift v r hvr with h | ⟨_, h2⟩ | ⟨h1, _⟩
      · exact Or.inl h
      · exact Or.inr h2
      · exact absurd h1 hnotvv'
  refine ⟨hdisj, hmem_iff, fun x hxF hxnot => ?_⟩
  ext y
  have hxv' : x ≠ v' := fun h => hv' (h ▸ hxF)
  have hxF' : x ∈ F'.V := hF'V ▸ Finset.mem_insert_of_mem hxF
  simp only [mem_compOf_iff, hF'V, Finset.mem_insert]
  constructor
  · rintro ⟨hyF, hxy⟩
    refine ⟨Or.inr hyF, ?_⟩
    rcases hlift x y hxy with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h
    · exact absurd (Finset.mem_union_left _ (mem_compOf_iff.mpr ⟨hxF', connected_symm h1⟩)) hxnot
    · exact absurd (Finset.mem_union_right _ (mem_compOf_iff.mpr ⟨hxF', connected_symm h1⟩)) hxnot
  · rintro ⟨rfl | hyF, hxy⟩
    · exact absurd (Finset.mem_union_right _ (mem_compOf_iff.mpr ⟨hxF', connected_symm hxy⟩)) hxnot
    · refine ⟨hyF, ?_⟩
      obtain ⟨P, hW⟩ := hxy
      have hP := proj_isWalk hproj_e hW
      have hyv' : y ≠ v' := fun h => hv' (h ▸ hyF)
      simp only [proj, hxv', hyv', ↓reduceIte] at hP
      exact ⟨P, hP⟩

/-! ## 2. Canonical root pair of a single cut or input split -/

/-- Under `canonRoots F old final`, the root of any vertex `x ∈ F.V` is `canonPick old final (compOf F x)`. -/
lemma canonRoots_root_eq {G F : MGraph} {final : RootedForest} {old : Finset ℕ}
    (hF : F.IsForest) (hV : F.V = G.V) (hFG : G.IsSubgraph F)
    (hfinal : final.IsRootedSpanningForestOf G) (hsub : F.IsSubgraph final.F)
    (hOld : old ⊆ final.R) (hSep : ∀ r ∈ old, ∀ s ∈ old, F.Connected r s → r = s)
    {x : ℕ} (hx : x ∈ G.V) :
    (RootedForest.mk F (canonRoots F old final.R)).root x = canonPick old final.R (compOf F x) := by
  obtain ⟨_, _, hRF⟩ := canonRoots_spec hF hV hFG hfinal hsub hOld hSep
  have hxF : x ∈ F.V := hV.symm ▸ hx
  have hA : compOf F x ∈ components F := compOf_mem_components hxF
  have hpick_R : canonPick old final.R (compOf F x) ∈ canonRoots F old final.R :=
    Finset.mem_image_of_mem _ hA
  have hpick_in : canonPick old final.R (compOf F x) ∈ compOf F x := by
    by_cases ho : (compOf F x ∩ old).Nonempty
    · simp only [canonPick, ho, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ ho)).1
    · obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 x hx
      have hf : (compOf F x ∩ final.R).Nonempty :=
        ⟨r, Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hV.symm ▸ hfinal.2.2.1 hr,
          connected_of_subgraph hsub hc⟩, hr⟩⟩
      simp only [canonPick, ho, hf, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ hf)).1
  have hconn := (mem_compOf_iff.mp hpick_in).2
  have hru := root_eq_of_mem_R hRF hpick_R
  exact (root_eq_of_connected hRF hx (hRF.2.2.1 hpick_R) hconn).trans hru

/-- Cutting edge `e ∈ F₀.E` in `F₀` with `R₀ = canonRoots F₀ old final.R` and
`R₁ = canonRoots F₁ R₀ final.R` produces `(kept, fresh) = mergeSplitPair ...` on the two child
components `A = compOf F₁ (F₀.tail e)` and `B = compOf F₁ (F₀.head e)`. -/
theorem canonCut_pair_eq {G F₀ : MGraph} {final : RootedForest} {old : Finset ℕ} {e : ℕ}
    (hF₀ : F₀.IsForest) (hV₀ : F₀.V = G.V) (hF₀G : G.IsSubgraph F₀)
    (he : e ∈ F₀.E) (hF₁sub : (eraseForestEdge F₀ e).IsSubgraph final.F)
    (hfinal : final.IsRootedSpanningForestOf G)
    (hOld : old ⊆ final.R)
    (hSep₀ : ∀ r ∈ old, ∀ s ∈ old, F₀.Connected r s → r = s) :
    let F₁ := eraseForestEdge F₀ e
    let R₀ := canonRoots F₀ old final.R
    let R₁ := canonRoots F₁ R₀ final.R
    let A := compOf F₁ (F₀.tail e)
    let B := compOf F₁ (F₀.head e)
    have hAf : (A ∩ final.R).Nonempty := by
      have haG : F₀.tail e ∈ G.V := hV₀ ▸ (hF₀.1 e he).1
      obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 _ haG
      exact ⟨r, Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hV₀.symm ▸ hfinal.2.2.1 hr,
        connected_of_subgraph hF₁sub hc⟩, hr⟩⟩
    have hBf : (B ∩ final.R).Nonempty := by
      have hbG : F₀.head e ∈ G.V := hV₀ ▸ (hF₀.1 e he).2
      obtain ⟨r, ⟨hr, hc⟩, _⟩ := hfinal.2.2.2.1 _ hbG
      exact ⟨r, Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hV₀.symm ▸ hfinal.2.2.1 hr,
        connected_of_subgraph hF₁sub hc⟩, hr⟩⟩
    let oldA : Option ℕ := open Classical in if h : (A ∩ old).Nonempty then some ((A ∩ old).min' h) else none
    let oldB : Option ℕ := open Classical in if h : (B ∩ old).Nonempty then some ((B ∩ old).min' h) else none
    ((RootedForest.mk F₀ R₀).root (F₀.tail e), newRoot R₁ R₀) =
      mergeSplitPair oldA ((A ∩ final.R).min' hAf) oldB ((B ∩ final.R).min' hBf) := by
  classical
  intro F₁ R₀ R₁ A B hAf hBf oldA oldB
  have hF₁ : F₁.IsForest := isForest_eraseEdge hF₀ e
  have hsub01 : F₀.IsSubgraph F₁ := eraseForestEdge_subgraph F₀ e
  have hF₁G : G.IsSubgraph F₁ := by
    refine ⟨hsub01.1.trans hF₀G.1, hsub01.2.1.trans hF₀G.2.1, fun f hf => ?_⟩
    have h1 := hsub01.2.2 f hf; have h0 := hF₀G.2.2 f (hsub01.2.1 hf)
    exact ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩
  have hsub0f : F₀.IsSubgraph final.F := by
    refine ⟨hF₁sub.1.trans hsub01.1, hF₁sub.2.1.trans hsub01.2.1, fun f hf => ?_⟩
    have h1 := hF₁sub.2.2 f hf; have h0 := hsub01.2.2 f (hF₁sub.2.1 hf)
    exact ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩
  have hR₁_eq : R₁ = canonRoots F₁ old final.R :=
    canonRoots_idem_of_subgraph hF₀ hV₀ hF₀G hF₁ hV₀ hF₁G hsub01 hF₁sub hfinal hOld hSep₀
  obtain ⟨hDisj, hP_eq, hOther⟩ := eraseForestEdge_compOf_split hF₀ he
  have hAtMostOne : ∀ r ∈ (A ∪ B) ∩ old, ∀ s ∈ (A ∪ B) ∩ old, r = s := fun r hr s hs => by
    rw [← hP_eq] at hr hs
    exact hSep₀ r (Finset.mem_inter.mp hr).2 s (Finset.mem_inter.mp hs).2
      (connected_trans (connected_symm (mem_compOf_iff.mp (Finset.mem_inter.mp hr).1).2)
        (mem_compOf_iff.mp (Finset.mem_inter.mp hs).1).2)
  have hmsp := mergeSplitPair_eq_canon hDisj hAf hBf hOld hAtMostOne
  dsimp only at hmsp
  rw [hmsp]
  set pA := canonPick old final.R A
  set pB := canonPick old final.R B
  set pP := canonPick old final.R (A ∪ B)
  have hkept : (RootedForest.mk F₀ R₀).root (F₀.tail e) = pP := by
    rw [canonRoots_root_eq hF₀ hV₀ hF₀G hfinal hsub0f hOld hSep₀ (hV₀ ▸ (hF₀.1 e he).1), hP_eq]
  -- Show `R₁ = insert (if pA = pP then pB else pA) R₀` with `(if pA = pP then pB else pA) ∉ R₀`
  have hpP_mem_R₀ : pP ∈ R₀ := by
    dsimp only [pP, R₀, canonRoots]
    rw [← hP_eq]
    exact Finset.mem_image_of_mem _ (compOf_mem_components (hF₀.1 e he).1)
  have hpA_in_A : pA ∈ A := by
    by_cases h : (A ∩ old).Nonempty
    · simp only [pA, canonPick, h, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h)).1
    · simp only [pA, canonPick, h, hAf, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1
  have hpB_in_B : pB ∈ B := by
    by_cases h : (B ∩ old).Nonempty
    · simp only [pB, canonPick, h, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ h)).1
    · simp only [pB, canonPick, h, hBf, ↓reduceDIte]; exact (Finset.mem_inter.mp (Finset.min'_mem _ hBf)).1
  have hpP_eq_or : pA = pP ∨ pB = pP := by
    by_cases hAo : (A ∩ old).Nonempty
    · left
      have hPo : ((A ∪ B) ∩ old).Nonempty := by
        obtain ⟨r, hr⟩ := hAo; exact ⟨r, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩⟩
      simp only [pA, pP, canonPick, hAo, hPo, ↓reduceDIte]
      have h1 := Finset.mem_inter.mp (Finset.min'_mem _ hAo)
      exact hAtMostOne _ (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h1.1, h1.2⟩) _ (Finset.min'_mem _ hPo)
    · by_cases hBo : (B ∩ old).Nonempty
      · right
        have hPo : ((A ∪ B) ∩ old).Nonempty := by
          obtain ⟨r, hr⟩ := hBo; exact ⟨r, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩⟩
        simp only [pB, pP, canonPick, hBo, hPo, ↓reduceDIte]
        have h1 := Finset.mem_inter.mp (Finset.min'_mem _ hBo)
        exact hAtMostOne _ (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ h1.1, h1.2⟩) _ (Finset.min'_mem _ hPo)
      · have hPo : ¬ ((A ∪ B) ∩ old).Nonempty := by
          rintro ⟨r, hr⟩; rcases Finset.mem_union.mp (Finset.mem_inter.mp hr).1 with hA | hB
          · exact hAo ⟨r, Finset.mem_inter.mpr ⟨hA, (Finset.mem_inter.mp hr).2⟩⟩
          · exact hBo ⟨r, Finset.mem_inter.mpr ⟨hB, (Finset.mem_inter.mp hr).2⟩⟩
        have hPf : ((A ∪ B) ∩ final.R).Nonempty := by
          obtain ⟨r, hr⟩ := hAf; exact ⟨r, Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩⟩
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hPf)
        rcases Finset.mem_union.mp hm.1 with hA | hB
        · left; simp only [pA, pP, canonPick, hAo, hPo, hAf, hPf, ↓reduceDIte]
          exact le_antisymm (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hA, hm.2⟩))
            (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1,
              (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).2⟩))
        · right; simp only [pB, pP, canonPick, hBo, hPo, hBf, hPf, ↓reduceDIte]
          exact le_antisymm (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨hB, hm.2⟩))
            (Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp (Finset.min'_mem _ hBf)).1,
              (Finset.mem_inter.mp (Finset.min'_mem _ hBf)).2⟩))
  have hpAB_ne : pA ≠ pB := fun h => Finset.disjoint_left.mp hDisj hpA_in_A (h ▸ hpB_in_B)
  set fresh := if pA = pP then pB else pA
  have hfresh_ne : fresh ≠ pP := by
    by_cases h : pA = pP
    · simp only [fresh, h, ↓reduceIte]; exact h ▸ hpAB_ne.symm
    · simp only [fresh, h, ↓reduceIte]; exact h
  have hfresh_in_P : fresh ∈ compOf F₀ (F₀.tail e) := by
    rw [hP_eq]; by_cases h : pA = pP
    · simp only [fresh, h, ↓reduceIte]; exact Finset.mem_union_right _ hpB_in_B
    · simp only [fresh, h, ↓reduceIte]; exact Finset.mem_union_left _ hpA_in_A
  have hfresh_not_R₀ : fresh ∉ R₀ := by
    intro hmem
    obtain ⟨_, _, hRF₀⟩ := canonRoots_spec hF₀ hV₀ hF₀G hfinal hsub0f hOld hSep₀
    have h1 := root_eq_of_mem_R hRF₀ hmem
    have h2 := root_eq_of_connected hRF₀ (hV₀ ▸ (hF₀.1 e he).1) (hRF₀.2.2.1 hmem) (mem_compOf_iff.mp hfresh_in_P).2
    exact hfresh_ne (h1.symm.trans (h2.symm.trans hkept))
  have hR₁_ins : R₁ = insert fresh R₀ := by
    rw [hR₁_eq]
    ext r
    simp only [R₀, canonRoots, Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hC
      by_cases hxP : x ∈ A ∪ B
      · rcases Finset.mem_union.mp hxP with hxA | hxB
        · have hce : compOf F₁ x = A := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hxA).2)
          rw [hce]; by_cases h : pA = pP
          · right; exact ⟨compOf F₀ (F₀.tail e), compOf_mem_components (hF₀.1 e he).1, by rw [hP_eq]; exact h.symm⟩
          · left; simp [fresh, h, pA]
        · have hce : compOf F₁ x = B := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hxB).2)
          rw [hce]; by_cases h : pA = pP
          · left; simp [fresh, h, pB]
          · right; exact ⟨compOf F₀ (F₀.tail e), compOf_mem_components (hF₀.1 e he).1,
              by rw [hP_eq]; exact (hpP_eq_or.resolve_left h).symm⟩
      · right; rw [← hOther x hxF hxP]; exact ⟨compOf F₀ x, compOf_mem_components hxF, rfl⟩
    · rintro (rfl | ⟨C, hC, rfl⟩)
      · by_cases h : pA = pP
        · exact ⟨B, compOf_mem_components (hF₀.1 e he).2, by simp [fresh, h, pB]⟩
        · exact ⟨A, compOf_mem_components (hF₀.1 e he).1, by simp [fresh, h, pA]⟩
      · obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hC
        by_cases hxP : x ∈ A ∪ B
        · have hce : compOf F₀ x = A ∪ B :=
            (compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp (hP_eq.symm ▸ hxP)).2)).trans hP_eq
          rw [hce]
          rcases hpP_eq_or with h | h
          · exact ⟨A, compOf_mem_components (hF₀.1 e he).1, h⟩
          · exact ⟨B, compOf_mem_components (hF₀.1 e he).2, h⟩
        · exact ⟨compOf F₁ x, compOf_mem_components hxF, by rw [← hOther x hxF hxP]⟩
  exact Prod.ext hkept (newRoot_eq hR₁_ins hfresh_not_R₀)


end

end MinCostFlow.SparseCore.Program
