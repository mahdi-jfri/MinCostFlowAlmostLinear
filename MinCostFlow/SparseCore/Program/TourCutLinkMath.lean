module

public import MinCostFlow.SparseCore.Program.TourOpsChangeRoot
public import MinCostFlow.SparseCore.Program.TourSurgeryCutLink
import Mathlib.Tactic

/-!
# Graph-theoretic invariants for forest `cut` and `link` operations

Proves the pure graph-theoretic validity and component-partition lemmas shared by `TourOpsCut`
and `TourOpsLink`:
- `tourValid_cut`, `cut_component_partition`,
- `addForestEdge_subgraph`, `connected_addForestEdge_iff`, `tourValid_link`,
- `foldr_max_eq_of_unique_pos`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

theorem tourValid_cut {vCap eCap e newRoot : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (_he : e ∈ s.rf.F.E) (hnewV : newRoot ∈ s.rf.F.V)
    (huniq' : ∀ v ∈ s.rf.F.V, ∃! r, r ∈ insert newRoot s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r) :
    TourValid vCap eCap (tourCut s e newRoot) where
  ordWithin := hv.ordWithin
  compat := ⟨hv.compat.nodup, hv.compat.unique, isForest_eraseEdge hv.compat.forest e,
    hv.compat.vert, fun f hf => hv.compat.forestEnd f (Finset.mem_erase.mp hf).2⟩
  roots_sub := fun r hr => by
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact hnewV
    · exact hv.roots_sub hr'
  verts_lt := hv.verts_lt
  unique_root := huniq'
  marked_open := fun z hz => ⟨(hv.marked_open z hz).1, fun hm => (hv.marked_open z hz).2 (Finset.mem_erase.mp hm).2⟩

/-- After cutting forest edge `e` (in component `oldRoot`), every vertex of `oldRoot`'s component
connects in `F'` to either `oldRoot` or `newRoot`, and the two endpoints `tail e, head e` connect
to `{oldRoot, newRoot}` in opposite order. -/
theorem cut_component_partition {vCap eCap e newRoot : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (he : e ∈ s.rf.F.E) (hnewV : newRoot ∈ s.rf.F.V)
    (hnewNotR : newRoot ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V, ∃! r, r ∈ insert newRoot s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r) :
    let u := s.rf.F.tail e
    let v := s.rf.F.head e
    let F' := eraseForestEdge s.rf.F e
    let oldRoot := s.rf.root u
    s.rf.root v = oldRoot ∧ oldRoot ∈ s.rf.R ∧ oldRoot ≠ newRoot ∧
    s.rf.F.Connected oldRoot newRoot ∧
    ((F'.Connected u oldRoot ∧ F'.Connected v newRoot) ∨
     (F'.Connected u newRoot ∧ F'.Connected v oldRoot)) := by
  intro u v F' oldRoot
  have huV : u ∈ s.rf.F.V := (hv.compat.forest.1 e he).1
  have hvV : v ∈ s.rf.F.V := (hv.compat.forest.1 e he).2
  have huv : s.rf.F.Connected u v := ⟨[(e, true)], .cons he rfl (.nil _)⟩
  have hold_spec := hv.root_spec huV
  have hrv : s.rf.root v = oldRoot :=
    hv.root_eq_of_mem hvV hold_spec.1 (connected_trans (connected_symm huv) hold_spec.2)
  have hne_or : oldRoot ≠ newRoot := fun heq => hnewNotR (heq ▸ hold_spec.1)
  have hconn_on : s.rf.F.Connected oldRoot newRoot := by
    by_contra hnc
    have hrn := hv.root_spec hnewV
    set r0 := s.rf.root newRoot
    obtain ⟨P, hP⟩ := connected_isPath hrn.2
    have he_not_P : e ∉ walkEdges P := by
      intro hm
      have hmemP : ∃ z ∈ P, z.1 = e := List.mem_map.mp (List.mem_toFinset.mp hm)
      obtain ⟨z, hzP, hze⟩ := hmemP
      obtain ⟨P₁, _, _, hP₁, _⟩ := walkVertices_mem_split hP.1 (by
        have hsub : ∀ (a b : ℕ) (Q : List End), s.rf.F.IsWalk a b Q → z ∈ Q → s.rf.F.src z ∈ s.rf.F.walkVertices a Q := by
          intro a b Q hQ
          induction hQ with
          | nil => intro h; simp at h
          | cons _ hs _ ih =>
            intro h; rw [walkVertices_cons]
            rcases List.mem_cons.mp h with rfl | ht
            · simp [hs]
            · exact List.mem_cons_of_mem _ (ih ht)
        exact hsub _ _ P hP.1 hzP)
      have hconn_src : s.rf.F.Connected newRoot (s.rf.F.src z) := ⟨P₁, hP₁⟩
      have hsrc_u : s.rf.F.Connected (s.rf.F.src z) u := by
        obtain ⟨f, b⟩ := z; change f = e at hze; subst f
        cases b
        · exact connected_symm huv
        · exact connected_refl _ u
      exact hnc (connected_trans (connected_symm hold_spec.2) (connected_symm (connected_trans hconn_src hsrc_u)))
    have hc_r0 : F'.Connected newRoot r0 := ⟨P, isWalk_eraseEdge_of_not_mem hP.1 he_not_P⟩
    have hc_new : F'.Connected newRoot newRoot := connected_refl F' newRoot
    obtain ⟨_, _, hU⟩ := huniq' newRoot hnewV
    have h1 := hU r0 ⟨Finset.mem_insert_of_mem hrn.1, hc_r0⟩
    have h2 := hU newRoot ⟨Finset.mem_insert_self _ _, hc_new⟩
    exact hnewNotR ((h1.trans h2.symm) ▸ hrn.1)
  have hmem_pair : ∀ w ∈ s.rf.F.V, s.rf.F.Connected w oldRoot →
      ∃ r ∈ insert newRoot s.rf.R, F'.Connected w r ∧ (r = oldRoot ∨ r = newRoot) := by
    intro w hwV hwo
    obtain ⟨r, ⟨hrR', hwr'⟩, _⟩ := huniq' w hwV
    refine ⟨r, hrR', hwr', ?_⟩
    rcases Finset.mem_insert.mp hrR' with rfl | hrR
    · exact Or.inr rfl
    · left
      have hwr := connected_of_subgraph (eraseForestEdge_subgraph s.rf.F e) hwr'
      exact (hv.root_eq_of_mem hwV hrR hwr).symm.trans (hv.root_eq_of_mem hwV hold_spec.1 hwo)
  obtain ⟨ru, _, hcu, hru⟩ := hmem_pair u huV hold_spec.2
  obtain ⟨rv, _, hcv, hrv'⟩ := hmem_pair v hvV (connected_trans (connected_symm huv) hold_spec.2)
  have hnc_uv : ¬ F'.Connected u v := not_connected_eraseForestEdge hv.compat.forest (x := (e, true)) he
  have hru_ne_rv : ru ≠ rv := fun heq => hnc_uv (connected_trans hcu (heq ▸ connected_symm hcv))
  refine ⟨hrv, hold_spec.1, hne_or, hconn_on, ?_⟩
  rcases hru with rfl | rfl <;> rcases hrv' with rfl | rfl
  · exact absurd rfl hru_ne_rv
  · exact Or.inl ⟨hcu, hcv⟩
  · exact Or.inr ⟨hcu, hcv⟩
  · exact absurd rfl hru_ne_rv

theorem addForestEdge_subgraph {F : MGraph} {e u v : ℕ} (he : e ∉ F.E) :
    (addForestEdge F e u v).IsSubgraph F :=
  ⟨Finset.Subset.rfl, Finset.subset_insert e F.E, fun f hf => by
    have hne : f ≠ e := fun h => he (h ▸ hf)
    simp [addForestEdge, Function.update_of_ne hne]⟩

theorem connected_addForestEdge_iff {F : MGraph} {e u v a b : ℕ} (he : e ∉ F.E) :
    (addForestEdge F e u v).Connected a b ↔
      F.Connected a b ∨ (F.Connected a u ∧ F.Connected v b) ∨ (F.Connected a v ∧ F.Connected u b) := by
  have hsub := addForestEdge_subgraph (u := u) (v := v) he
  constructor
  · rintro ⟨P, hP⟩
    have hback : ∀ (x y : ℕ) (Q : List End), (addForestEdge F e u v).IsWalk x y Q →
        e ∉ Q.map Prod.fst → F.IsWalk x y Q := by
      intro x y Q hQ hne
      induction hQ with
      | nil w => exact .nil w
      | @cons x y z rest hzE hzS _ ih =>
        have hze : z.1 ≠ e := fun h => hne (List.mem_map.mpr ⟨z, List.mem_cons_self, h⟩)
        have hzF : z.1 ∈ F.E := (Finset.mem_insert.mp hzE).resolve_left hze
        have hsr : F.src z = x := by
          obtain ⟨f, side⟩ := z; cases side <;> simpa [MGraph.src, addForestEdge, Function.update_of_ne hze] using hzS
        have hds : F.dst z = (addForestEdge F e u v).dst z := by
          obtain ⟨f, side⟩ := z; cases side <;> simp [MGraph.dst, addForestEdge, Function.update_of_ne hze]
        exact .cons hzF hsr (hds ▸ ih fun hm => hne (List.mem_cons_of_mem _ hm))
    obtain ⟨Q, hQ⟩ := connected_isPath ⟨P, hP⟩
    by_cases heQ : e ∈ Q.map Prod.fst
    · obtain ⟨z, hzQ, hze⟩ := List.mem_map.mp heQ
      obtain ⟨Q₁, Q₂, rfl⟩ := List.mem_iff_append.mp hzQ
      have hnd : (Q₁ ++ z :: Q₂).map Prod.fst |>.Nodup := by
        simpa [walkEdges] using isPath_nodup_edges hQ
      have hne1 : e ∉ Q₁.map Prod.fst := by
        intro hm; rw [List.map_append, List.map_cons, hze] at hnd
        exact (List.nodup_append.mp hnd).2.2 e hm e List.mem_cons_self rfl
      have hne2 : e ∉ Q₂.map Prod.fst := by
        intro hm; rw [List.map_append, List.map_cons, hze] at hnd
        exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hm
      have hsplit : ∀ (x y : ℕ) (L₁ L₂ : List End), (addForestEdge F e u v).IsWalk x y (L₁ ++ z :: L₂) →
          (addForestEdge F e u v).IsWalk x ((addForestEdge F e u v).src z) L₁ ∧
          (addForestEdge F e u v).IsWalk ((addForestEdge F e u v).dst z) y L₂ := by
        intro x y L₁ L₂ hw
        induction L₁ generalizing x with
        | nil => cases hw with | cons _ hs hr => exact ⟨hs ▸ .nil _, hr⟩
        | cons w ws ih => cases hw with | cons he' hs' hr' =>
            obtain ⟨h1, h2⟩ := ih _ hr'; exact ⟨.cons he' hs' h1, h2⟩
      obtain ⟨hw1, hw2⟩ := hsplit a b Q₁ Q₂ hQ.1
      have hc1 : F.Connected a ((addForestEdge F e u v).src z) := ⟨Q₁, hback _ _ Q₁ hw1 hne1⟩
      have hc2 : F.Connected ((addForestEdge F e u v).dst z) b := ⟨Q₂, hback _ _ Q₂ hw2 hne2⟩
      obtain ⟨f, side⟩ := z; change f = e at hze; subst f
      cases side
      · right; right; exact ⟨by simpa [MGraph.src, Bool.false_eq_true, addForestEdge] using hc1,
          by simpa [MGraph.dst, Bool.false_eq_true, addForestEdge] using hc2⟩
      · right; left; exact ⟨by simpa [MGraph.src, addForestEdge] using hc1,
          by simpa [MGraph.dst, addForestEdge] using hc2⟩
    · exact Or.inl ⟨Q, hback a b Q hQ.1 heQ⟩
  · rintro (hc | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact connected_of_subgraph hsub hc
    · have huv : (addForestEdge F e u v).Connected u v :=
        ⟨[(e, true)], .cons (Finset.mem_insert_self _ _) (by simp [MGraph.src, addForestEdge])
          (by rw [show (addForestEdge F e u v).dst (e, true) = v by simp [MGraph.dst, addForestEdge]]; exact .nil v)⟩
      exact connected_trans (connected_of_subgraph hsub h1) (connected_trans huv (connected_of_subgraph hsub h2))
    · have hvu : (addForestEdge F e u v).Connected v u :=
        ⟨[(e, false)], .cons (Finset.mem_insert_self _ _) (by simp [MGraph.src, Bool.false_eq_true, addForestEdge])
          (by rw [show (addForestEdge F e u v).dst (e, false) = u by simp [MGraph.dst, Bool.false_eq_true, addForestEdge]]; exact .nil u)⟩
      exact connected_trans (connected_of_subgraph hsub h1) (connected_trans hvu (connected_of_subgraph hsub h2))

theorem tourValid_link {vCap eCap e dropRoot u v : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (he : e ∉ s.rf.F.E)
    (hxu : (e, true) ∈ s.ord u) (hyv : (e, false) ∈ s.ord v)
    (hnc : ¬ s.rf.F.Connected u v)
    (hdrop : dropRoot = s.rf.root u ∨ dropRoot = s.rf.root v) :
    TourValid vCap eCap (tourLink s e dropRoot) := by
  have huSrc : ordSrc s.ord (e, true) = u := hv.compat.ordSrc_eq hxu
  have hvSrc : ordSrc s.ord (e, false) = v := hv.compat.ordSrc_eq hyv
  have huV : u ∈ s.rf.F.V := hv.compat.vert u (List.ne_nil_of_mem hxu)
  have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hyv)
  have hru := hv.root_spec huV
  have hrv := hv.root_spec hvV
  have hru_ne_rv : s.rf.root u ≠ s.rf.root v := fun heq =>
    hnc (connected_trans hru.2 (heq ▸ connected_symm hrv.2))
  set keepRoot := if dropRoot = s.rf.root u then s.rf.root v else s.rf.root u
  have hkeepR : keepRoot ∈ s.rf.R.erase dropRoot := by
    rcases hdrop with rfl | rfl
    · simp [keepRoot, Finset.mem_erase, hru_ne_rv.symm, hrv.1]
    · simp [keepRoot, Finset.mem_erase, hru_ne_rv.symm, hru_ne_rv, hru.1]
  have hF_eq : (tourLink s e dropRoot).rf.F = addForestEdge s.rf.F e u v := by
    simp [tourLink, huSrc, hvSrc]
  refine ⟨hv.ordWithin, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF_eq]
    exact ⟨hv.compat.nodup, hv.compat.unique, isForest_addForestEdge hv.compat.forest he huV hvV hnc,
      hv.compat.vert, fun f hf => by
        rcases Finset.mem_insert.mp hf with rfl | hfF
        · simpa [tourLink, addForestEdge] using ⟨hxu, hyv⟩
        · have hne : f ≠ e := fun h => he (h ▸ hfF)
          simpa [tourLink, addForestEdge, Function.update_of_ne hne] using hv.compat.forestEnd f hfF⟩
  · rw [hF_eq]; exact fun r hr => hv.roots_sub (Finset.mem_of_mem_erase hr)
  · rw [hF_eq]; exact hv.verts_lt
  · intro w hwV
    rw [hF_eq] at hwV ⊢
    obtain ⟨r, ⟨hrR, hwr⟩, huniq⟩ := hv.unique_root w hwV
    have hconn_k : ∀ z, (s.rf.F.Connected z u ∨ s.rf.F.Connected z v) → (addForestEdge s.rf.F e u v).Connected z keepRoot := by
      intro z hz
      rw [connected_addForestEdge_iff he]
      rcases hdrop with rfl | rfl
      · simp only [keepRoot, ↓reduceIte]
        rcases hz with hzu | hzv
        · exact Or.inr (Or.inl ⟨hzu, hrv.2⟩)
        · exact Or.inl (connected_trans hzv hrv.2)
      · simp only [keepRoot, hru_ne_rv.symm, ↓reduceIte]
        rcases hz with hzu | hzv
        · exact Or.inl (connected_trans hzu hru.2)
        · exact Or.inr (Or.inr ⟨hzv, hru.2⟩)
    by_cases hcomp : r = s.rf.root u ∨ r = s.rf.root v
    · have hw_uv : s.rf.F.Connected w u ∨ s.rf.F.Connected w v := by
        rcases hcomp with rfl | rfl
        · exact Or.inl (connected_trans hwr (connected_symm hru.2))
        · exact Or.inr (connected_trans hwr (connected_symm hrv.2))
      refine ⟨keepRoot, ⟨hkeepR, hconn_k w hw_uv⟩, fun r' ⟨hr'R, hwr'⟩ => ?_⟩
      have hr'S : r' ∈ s.rf.R := Finset.mem_of_mem_erase hr'R
      have hr'ne : r' ≠ dropRoot := (Finset.mem_erase.mp hr'R).1
      rw [connected_addForestEdge_iff he] at hwr'
      have hr'_in : r' = s.rf.root u ∨ r' = s.rf.root v := by
        rcases hwr' with hF' | ⟨_, h2⟩ | ⟨_, h2⟩
        · have heq : r' = r := huniq r' ⟨hr'S, hF'⟩
          exact heq ▸ hcomp
        · exact Or.inr (hv.root_eq_of_mem hvV hr'S h2).symm
        · exact Or.inl (hv.root_eq_of_mem huV hr'S h2).symm
      rcases hdrop with rfl | rfl
      · simp only [keepRoot, ↓reduceIte]; exact hr'_in.resolve_left hr'ne
      · simp only [keepRoot, hru_ne_rv.symm, ↓reduceIte]; exact hr'_in.resolve_right hr'ne
    · push Not at hcomp
      have hr_ne_drop : r ≠ dropRoot := by rcases hdrop with rfl | rfl <;> tauto
      refine ⟨r, ⟨Finset.mem_erase.mpr ⟨hr_ne_drop, hrR⟩, connected_of_subgraph (addForestEdge_subgraph he) hwr⟩,
        fun r' ⟨hr'R, hwr'⟩ => ?_⟩
      have hr'S : r' ∈ s.rf.R := Finset.mem_of_mem_erase hr'R
      rw [connected_addForestEdge_iff he] at hwr'
      rcases hwr' with hF' | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact huniq r' ⟨hr'S, hF'⟩
      · exfalso; exact hcomp.1 (huniq (s.rf.root u) ⟨hru.1, connected_trans h1 hru.2⟩).symm
      · exfalso; exact hcomp.2 (huniq (s.rf.root v) ⟨hrv.1, connected_trans h1 hrv.2⟩).symm
  · intro z hz
    rw [hF_eq]
    have hz' := Finset.mem_filter.mp hz
    have hmo := hv.marked_open z hz'.1
    have hzne : z.1 ≠ e := bne_iff_ne.mp hz'.2
    exact ⟨hmo.1, fun hm => by rcases Finset.mem_insert.mp hm with heq | hmF; exact hzne heq; exact hmo.2 hmF⟩

theorem foldr_max_eq_of_unique_pos {L : List ℕ} {f : ℕ → ℕ} {a v : ℕ}
    (ha : a ∈ L) (hfa : f a = v) (hzero : ∀ u ∈ L, u ≠ a → f u = 0) :
    (L.map f).foldr max 0 = v := by
  have hle : ∀ z ∈ L.map f, z ≤ v := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    by_cases hua : u = a
    · subst u; exact le_of_eq hfa
    · rw [hzero u hu hua]; exact Nat.zero_le v
  have hmem : v ∈ L.map f := List.mem_map.mpr ⟨a, ha, hfa⟩
  have h1 : ∀ ls : List ℕ, (∀ z ∈ ls, z ≤ v) → ls.foldr max 0 ≤ v := by
    intro ls; induction ls with
    | nil => intro _; exact Nat.zero_le v
    | cons z zs ih => intro h; exact max_le (h z (by simp)) (ih fun w hw => h w (by simp [hw]))
  have h2 : ∀ ls : List ℕ, v ∈ ls → v ≤ ls.foldr max 0 := by
    intro ls; induction ls with
    | nil => intro h; simp at h
    | cons z zs ih =>
      intro h; rcases List.mem_cons.mp h with rfl | ht
      · exact le_max_left _ _
      · exact le_trans (ih ht) (le_max_right _ _)
  exact le_antisymm (h1 _ hle) (h2 _ hmem)

end MinCostFlow.SparseCore.Program
