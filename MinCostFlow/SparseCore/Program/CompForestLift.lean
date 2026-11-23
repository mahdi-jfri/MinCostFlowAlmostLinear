module

public import MinCostFlow.SparseCore.Program.CompCutLogBase
public import MinCostFlow.SparseCore.Program.CompModel
public import MinCostFlow.SparseCore.Program.ReadSpec
import Mathlib.Tactic.Linarith

/-!
# Global Forest-Cut Lifting and `LSFChange.Exact` Assembly (`CompForestLift`)

Pure graph-theoretic lemmas connecting per-component cut logs to the global rooted spanning
forest `CompLSFState.RF` and P10's `Read.LSFChange`:

* `compForestCutsValid_disjoint_union`: lifting a valid cut sequence on one connected component
  `C` of `CompLSFState` to the global disjoint-union forest `cs.RF`.
* `compForestCutsValid_of_splitRoot`: pulling back a valid cut sequence across a root vertex
  split `v → (v, v')` (when `v ∈ R`), showing that cuts performed after a split remain valid on
  the pre-split forest.
* `compForestCuts_to_lsfChange`: combining the ordered cut sequence `cuts` and the split-created
  vertices `splitVerts` into `chg : Read.LSFChange` satisfying `chg.Exact cs.lsf cs'.lsf`,
  `List.zip chg.fDel chg.roots = cuts`, and `CompForestCutsValid`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. Basic `compApplyForestCut` and `List.zip` identities -/

lemma compApplyForestCut_foldl_V (RF : RootedForest) (cuts : List (ℕ × ℕ)) :
    (cuts.foldl compApplyForestCut RF).F.V = RF.F.V := by
  induction cuts generalizing RF with
  | nil => rfl
  | cons p tl ih => exact ih _

lemma compApplyForestCut_foldl_tail (RF : RootedForest) (cuts : List (ℕ × ℕ)) :
    (cuts.foldl compApplyForestCut RF).F.tail = RF.F.tail := by
  induction cuts generalizing RF with
  | nil => rfl
  | cons p tl ih => exact ih _

lemma compApplyForestCut_foldl_head (RF : RootedForest) (cuts : List (ℕ × ℕ)) :
    (cuts.foldl compApplyForestCut RF).F.head = RF.F.head := by
  induction cuts generalizing RF with
  | nil => rfl
  | cons p tl ih => exact ih _

lemma compApplyForestCut_foldl_E (RF : RootedForest) (cuts : List (ℕ × ℕ)) :
    (cuts.foldl compApplyForestCut RF).F.E = RF.F.E \ (cuts.map Prod.fst).toFinset := by
  induction cuts generalizing RF with
  | nil => simp
  | cons p tl ih =>
    simp only [List.foldl_cons, compApplyForestCut, List.map_cons, List.toFinset_cons]
    rw [ih]
    ext e; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto

lemma compApplyForestCut_foldl_R (RF : RootedForest) (cuts : List (ℕ × ℕ)) :
    (cuts.foldl compApplyForestCut RF).R = RF.R ∪ (cuts.map Prod.snd).toFinset := by
  induction cuts generalizing RF with
  | nil => simp
  | cons p tl ih =>
    simp only [List.foldl_cons, compApplyForestCut, List.map_cons, List.toFinset_cons]
    rw [ih]
    ext r; simp only [Finset.mem_union, Finset.mem_insert]; tauto

lemma list_zip_map_append {α β : Type*} (l : List (α × β)) (extra : List β) :
    List.zip (l.map Prod.fst) (l.map Prod.snd ++ extra) = l := by
  induction l with
  | nil => simp
  | cons p tl ih =>
    rcases p with ⟨a, b⟩
    simp [ih]

/-! ## 2. Disjoint-union lifting of `CompForestCutsValid` -/

/-- A walk in `G` whose edges are disjoint from `F₁`'s edges stays outside `F₁.V` if it starts
outside `F₁.V`, and stays inside `F₁.V` (using only edges of `F₁`) if it starts inside `F₁.V`. -/
private lemma walk_stay_in_part {G F₁ : MGraph}
    (_hsub : F₁.V ⊆ G.V) (_hEsub : F₁.E ⊆ G.E)
    (ht : ∀ e ∈ F₁.E, F₁.tail e = G.tail e) (hh : ∀ e ∈ F₁.E, F₁.head e = G.head e)
    (hF₁_val : F₁.IsValid)
    (hsep : ∀ e ∈ G.E, e ∉ F₁.E → G.tail e ∉ F₁.V ∧ G.head e ∉ F₁.V) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      (u ∈ F₁.V → v ∈ F₁.V ∧ F₁.IsWalk u v P) ∧
      (u ∉ F₁.V → v ∉ F₁.V ∧ ∀ x ∈ P, x.1 ∉ F₁.E) := by
  intro u v P hW
  induction hW with
  | nil x => exact ⟨fun hx => ⟨hx, .nil x⟩, fun hx => ⟨hx, fun _ h => by cases h⟩⟩
  | @cons x y z rest hzE hsrc hW ih =>
    rcases z with ⟨e, dir⟩
    by_cases he1 : e ∈ F₁.E
    · have hsrc1 : F₁.src (e, dir) = x := by
        cases dir <;> simp [MGraph.src] at hsrc ⊢
        · rw [hh e he1]; exact hsrc
        · rw [ht e he1]; exact hsrc
      have hdst1 : F₁.dst (e, dir) = G.dst (e, dir) := by
        cases dir <;> simp [MGraph.dst, ht e he1, hh e he1]
      have hx1 : x ∈ F₁.V := by
        cases dir <;> simp [MGraph.src] at hsrc1
        · rw [← hsrc1]; exact (hF₁_val e he1).2
        · rw [← hsrc1]; exact (hF₁_val e he1).1
      have hdstV : G.dst (e, dir) ∈ F₁.V := by
        rw [← hdst1]; cases dir <;> simp [MGraph.dst, (hF₁_val e he1).1, (hF₁_val e he1).2]
      exact ⟨fun _ => let ⟨hv, hw1⟩ := ih.1 hdstV; ⟨hv, .cons he1 hsrc1 (hdst1 ▸ hw1)⟩,
        fun hnx => absurd hx1 hnx⟩
    · have ⟨hnt, hnh⟩ := hsep e hzE he1
      have hnx : x ∉ F₁.V := by cases dir <;> simp [MGraph.src] at hsrc <;> rw [← hsrc] <;> assumption
      have hndst : G.dst (e, dir) ∉ F₁.V := by cases dir <;> simp [MGraph.dst] <;> assumption
      exact ⟨fun hx => absurd hx hnx, fun _ =>
        let ⟨hv, hrest⟩ := ih.2 hndst
        ⟨hv, fun q hq => by rcases List.mem_cons.mp hq with rfl | hq'; exact he1; exact hrest q hq'⟩⟩

private lemma walk_lift_part {G F₁ : MGraph}
    (hEsub : F₁.E ⊆ G.E) (ht : ∀ e ∈ F₁.E, F₁.tail e = G.tail e) (hh : ∀ e ∈ F₁.E, F₁.head e = G.head e) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, F₁.IsWalk u v P → G.IsWalk u v P := by
  intro u v P hW
  induction hW with
  | nil x => exact .nil x
  | @cons x y z rest hzE hsrc _ ih =>
    rcases z with ⟨e, dir⟩
    have hsrcG : G.src (e, dir) = x := by
      cases dir <;> simp [MGraph.src] at hsrc ⊢
      · rw [← hh e hzE]; exact hsrc
      · rw [← ht e hzE]; exact hsrc
    have hdstG : G.dst (e, dir) = F₁.dst (e, dir) := by
      cases dir <;> simp [MGraph.dst, ht e hzE, hh e hzE]
    exact .cons (hEsub hzE) hsrcG (hdstG ▸ ih)

/-- Lifting a valid cut sequence on an isolated part `RF₁` of a global rooted forest `RF` (where
no edge crosses between `RF₁.F.V` and `RF.F.V \ RF₁.F.V`) to the full forest `RF`. -/
lemma compForestCutsValid_part_to_global {vCap : ℕ} :
    ∀ (cuts : List (ℕ × ℕ)) (RF RF₁ : RootedForest),
      RF₁.F.V ⊆ RF.F.V → RF₁.F.E ⊆ RF.F.E → RF₁.R ⊆ RF.R →
      (∀ r ∈ RF.R, r ∈ RF₁.F.V → r ∈ RF₁.R) →
      (∀ e ∈ RF₁.F.E, RF₁.F.tail e = RF.F.tail e ∧ RF₁.F.head e = RF.F.head e) →
      RF₁.F.IsValid →
      (∀ e ∈ RF.F.E, e ∉ RF₁.F.E → RF.F.tail e ∉ RF₁.F.V ∧ RF.F.head e ∉ RF₁.F.V) →
      (∀ v ∈ RF.F.V, v ∉ RF₁.F.V → ∃! r, r ∈ RF.R ∧ RF.F.Connected v r) →
      CompForestCutsValid vCap RF₁ cuts →
      CompForestCutsValid vCap RF cuts
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | (e, r) :: rest, RF, RF₁, hVsub, hEsub, hRsub, hRpart, hends, hF₁val, hsep, hrest_uniq, hvalid => by
    rcases hvalid with ⟨he1, hrCap, hrV1, hrNotR1, huniq1, hvalid_rest⟩
    have heG : e ∈ RF.F.E := hEsub he1
    have hrV : r ∈ RF.F.V := hVsub hrV1
    have hrNotR : r ∉ RF.R := fun h => hrNotR1 (hRpart r h hrV1)
    let F' : MGraph := { RF.F with E := RF.F.E.erase e }
    let F₁' : MGraph := { RF₁.F with E := RF₁.F.E.erase e }
    have hEsub' : F₁'.E ⊆ F'.E := Finset.erase_subset_erase e hEsub
    have hF₁'val : F₁'.IsValid := fun f hf => hF₁val f (Finset.mem_of_mem_erase hf)
    have hsep' : ∀ f ∈ F'.E, f ∉ F₁'.E → F'.tail f ∉ F₁'.V ∧ F'.head f ∉ F₁'.V := by
      intro f hf hnf
      have hfG : f ∈ RF.F.E := Finset.mem_of_mem_erase hf
      have hne : f ≠ e := (Finset.mem_erase.mp hf).1
      have hnf1 : f ∉ RF₁.F.E := fun h => hnf (Finset.mem_erase.mpr ⟨hne, h⟩)
      exact hsep f hfG hnf1
    have ht' : ∀ f ∈ F₁'.E, F₁'.tail f = F'.tail f := fun f hf => (hends f (Finset.mem_of_mem_erase hf)).1
    have hh' : ∀ f ∈ F₁'.E, F₁'.head f = F'.head f := fun f hf => (hends f (Finset.mem_of_mem_erase hf)).2
    have huniq_all : ∀ v ∈ RF.F.V, ∃! rt, rt ∈ insert r RF.R ∧ F'.Connected v rt := by
      intro v hv
      by_cases hv1 : v ∈ RF₁.F.V
      · obtain ⟨rt0, ⟨hrt0_R, hrt0_c⟩, hrt0_u⟩ := huniq1 v hv1
        refine ⟨rt0, ⟨?_, ?_⟩, ?_⟩
        · rcases Finset.mem_insert.mp hrt0_R with rfl | h
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hRsub h)
        · obtain ⟨P, hP⟩ := hrt0_c
          exact ⟨P, walk_lift_part hEsub' ht' hh' hP⟩
        · intro rt ⟨hrt_R, ⟨P, hP⟩⟩
          have ⟨hrtV1, hP1⟩ := (walk_stay_in_part (G := F') (F₁ := F₁') hVsub hEsub' ht' hh' hF₁'val hsep' hP).1 hv1
          have hrt_R1 : rt ∈ insert r RF₁.R := by
            rcases Finset.mem_insert.mp hrt_R with rfl | h
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (hRpart rt h hrtV1)
          exact hrt0_u rt ⟨hrt_R1, ⟨P, hP1⟩⟩
      · obtain ⟨rt0, ⟨hrt0_R, ⟨P, hP⟩⟩, hrt0_u⟩ := hrest_uniq v hv hv1
        have ⟨hrt0_nv1, hP_not1⟩ := (walk_stay_in_part hVsub hEsub (fun f hf => (hends f hf).1)
          (fun f hf => (hends f hf).2) hF₁val hsep hP).2 hv1
        have hP' : F'.IsWalk v rt0 P := by
          have hwalk_sub : ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, RF.F.IsWalk a b Q →
              (∀ x ∈ Q, x.1 ∉ RF₁.F.E) → F'.IsWalk a b Q := by
            intro a b Q hQ
            induction hQ with
            | nil x => intro _; exact .nil x
            | @cons x y z rest hzE hsrc _ ih =>
              intro hnot
              have hne : z.1 ≠ e := fun h => hnot z List.mem_cons_self (h ▸ he1)
              exact .cons (Finset.mem_erase.mpr ⟨hne, hzE⟩) hsrc
                (ih fun q hq => hnot q (List.mem_cons_of_mem _ hq))
          exact hwalk_sub hP hP_not1
        refine ⟨rt0, ⟨Finset.mem_insert_of_mem hrt0_R, ⟨P, hP'⟩⟩, ?_⟩
        intro rt ⟨hrt_R, ⟨Q, hQ⟩⟩
        have ⟨hrt_nv1, _⟩ := (walk_stay_in_part (G := F') (F₁ := F₁') hVsub hEsub' ht' hh' hF₁'val hsep' hQ).2 hv1
        have hrt_in_R : rt ∈ RF.R := by
          rcases Finset.mem_insert.mp hrt_R with rfl | h
          · exact absurd hrV1 hrt_nv1
          · exact h
        have hQ_RF : RF.F.IsWalk v rt Q :=
          walk_lift_part (G := RF.F) (F₁ := F') (Finset.erase_subset e RF.F.E)
            (fun _ _ => rfl) (fun _ _ => rfl) hQ
        exact hrt0_u rt ⟨hrt_in_R, ⟨Q, hQ_RF⟩⟩
    refine ⟨heG, hrCap, hrV, hrNotR, huniq_all,
      compForestCutsValid_part_to_global rest (compApplyForestCut RF (e, r))
        (compApplyForestCut RF₁ (e, r)) hVsub hEsub' (Finset.insert_subset_insert r hRsub)
        (fun rt hrt hrt1 => by
          rcases Finset.mem_insert.mp hrt with rfl | h
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hRpart rt h hrt1))
        (fun f hf => hends f (Finset.mem_of_mem_erase hf)) hF₁'val hsep'
        (fun v hv hnv1 => huniq_all v hv) hvalid_rest⟩

/-! ## 3. Pulling back `CompForestCutsValid` across a root vertex split -/

/-- Contracting `v'` back into `v` via `φ(x) = if x = v' then v else x`. -/
def unsplitMap (v v' x : ℕ) : ℕ := if x = v' then v else x

private lemma walk_contract {F₀ F₁ : MGraph} {v v' : ℕ}
    (hE : F₁.E = F₀.E)
    (ht : ∀ e ∈ F₀.E, unsplitMap v v' (F₁.tail e) = F₀.tail e)
    (hh : ∀ e ∈ F₀.E, unsplitMap v v' (F₁.head e) = F₀.head e) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, F₁.IsWalk a b P →
      F₀.IsWalk (unsplitMap v v' a) (unsplitMap v v' b) P := by
  intro a b P hW
  induction hW with
  | nil x => exact .nil _
  | @cons x y z rest hzE hsrc _ ih =>
    rcases z with ⟨e, dir⟩
    have he0 : e ∈ F₀.E := hE ▸ hzE
    have hsrc0 : F₀.src (e, dir) = unsplitMap v v' x := by
      cases dir <;> simp [MGraph.src] at hsrc ⊢
      · rw [← hh e he0, hsrc]
      · rw [← ht e he0, hsrc]
    have hdst0 : F₀.dst (e, dir) = unsplitMap v v' (F₁.dst (e, dir)) := by
      cases dir <;> simp [MGraph.dst, ht e he0, hh e he0]
    exact .cons he0 hsrc0 (hdst0 ▸ ih)

/-- Any walk in `F₀` that avoids visiting `v` lifts identically to `F₁`, and any walk in `F₀`
starting at `a` either lifts to `F₁` or reaches `v` (hence in `F₁` reaches `v` or `v'`). -/
private lemma walk_lift_split {F₀ F₁ : MGraph} {v v' : ℕ}
    (hE : F₁.E = F₀.E)
    (ht : ∀ e ∈ F₀.E, unsplitMap v v' (F₁.tail e) = F₀.tail e)
    (hh : ∀ e ∈ F₀.E, unsplitMap v v' (F₁.head e) = F₀.head e)
    (hF₀_nv' : ∀ e ∈ F₀.E, F₀.tail e ≠ v' ∧ F₀.head e ≠ v') :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, F₀.IsWalk a b P → a ≠ v' → b ≠ v' →
      F₁.Connected a b ∨ (F₁.Connected a v ∨ F₁.Connected a v') := by
  intro a b P hW
  induction hW with
  | nil x => intro _ _; exact Or.inl ⟨[], .nil x⟩
  | @cons x y z rest hzE hsrc _ ih =>
    intro hxv hbv
    rcases z with ⟨e, dir⟩
    have he1 : e ∈ F₁.E := hE.symm ▸ hzE
    have hsrc_map : unsplitMap v v' (F₁.src (e, dir)) = x := by
      cases dir <;> simp [MGraph.src] at hsrc ⊢
      · rw [hh e hzE]; exact hsrc
      · rw [ht e hzE]; exact hsrc
    have hdst_map : unsplitMap v v' (F₁.dst (e, dir)) = F₀.dst (e, dir) := by
      cases dir <;> simp [MGraph.dst, ht e hzE, hh e hzE]
    have hdst_nv' : F₀.dst (e, dir) ≠ v' := by
      cases dir <;> simp [MGraph.dst, (hF₀_nv' e hzE).1, (hF₀_nv' e hzE).2]
    by_cases hx_eq : x = v
    · subst hx_eq; exact Or.inr (Or.inl ⟨[], .nil x⟩)
    · have hsrc1 : F₁.src (e, dir) = x := by
        unfold unsplitMap at hsrc_map; split_ifs at hsrc_map with h1
        · exact absurd hsrc_map.symm hx_eq
        · exact hsrc_map
      have hstep : F₁.Connected x (F₁.dst (e, dir)) := ⟨[(e, dir)], .cons he1 hsrc1 (.nil _)⟩
      by_cases hdst_v' : F₁.dst (e, dir) = v'
      · exact Or.inr (Or.inr (hdst_v' ▸ hstep))
      · have hdst1 : F₁.dst (e, dir) = F₀.dst (e, dir) := by
          unfold unsplitMap at hdst_map; rwa [ite_eq_right hdst_v'] at hdst_map
        rw [hdst1] at hstep
        rcases ih hdst_nv' hbv with h1 | h2 | h3
        · exact Or.inl (connected_trans hstep h1)
        · exact Or.inr (Or.inl (connected_trans hstep h2))
        · exact Or.inr (Or.inr (connected_trans hstep h3))

/-- Pulling back `CompForestCutsValid` across a root split `v → (v, v')` (`v ∈ RF₀.R`, `v ∈ RF₀.F.V`,
`v' ∉ RF₀.F.V`, `RF₁.R = insert v' RF₀.R`, `RF₁.F.V = insert v' RF₀.F.V`, `RF₁.F.E = RF₀.F.E`, and
every edge of `RF₁` maps to `RF₀` under `unsplitMap v v'`). -/
lemma compForestCutsValid_of_splitRoot {vCap v v' : ℕ} :
    ∀ (cuts : List (ℕ × ℕ)) (RF₀ RF₁ : RootedForest),
      RF₀.F.IsValid →
      v ∈ RF₀.R → v ∈ RF₀.F.V → v' ∉ RF₀.F.V →
      RF₁.F.V = insert v' RF₀.F.V →
      RF₁.F.E = RF₀.F.E →
      RF₁.R = insert v' RF₀.R →
      (∀ e ∈ RF₀.F.E, unsplitMap v v' (RF₁.F.tail e) = RF₀.F.tail e ∧
        unsplitMap v v' (RF₁.F.head e) = RF₀.F.head e) →
      (∀ p ∈ cuts, p.2 ≠ v') →
      CompForestCutsValid vCap RF₁ cuts →
      CompForestCutsValid vCap RF₀ cuts
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | (e, r) :: rest, RF₀, RF₁, hVal₀, hvR₀, hvV₀, hv'NotV₀, hV₁, hE₁, hR₁, hends, hne_v', hvalid => by
    rcases hvalid with ⟨he1, hrCap, hrV1, hrNotR1, huniq1, hvalid_rest⟩
    have hv_ne_v' : v ≠ v' := fun h => hv'NotV₀ (h ▸ hvV₀)
    have hr_ne_v' : r ≠ v' := hne_v' (e, r) List.mem_cons_self
    have he0 : e ∈ RF₀.F.E := hE₁ ▸ he1
    have hrV0 : r ∈ RF₀.F.V := by
      rw [hV₁, Finset.mem_insert] at hrV1; exact hrV1.resolve_left hr_ne_v'
    have hrNotR0 : r ∉ RF₀.R := fun h => hrNotR1 (hR₁ ▸ Finset.mem_insert_of_mem h)
    let F₀' : MGraph := { RF₀.F with E := RF₀.F.E.erase e }
    let F₁' : MGraph := { RF₁.F with E := RF₁.F.E.erase e }
    have hE₁' : F₁'.E = F₀'.E := by simp [F₁', F₀', hE₁]
    have ht' : ∀ f ∈ F₀'.E, unsplitMap v v' (F₁'.tail f) = F₀'.tail f :=
      fun f hf => (hends f (Finset.mem_of_mem_erase hf)).1
    have hh' : ∀ f ∈ F₀'.E, unsplitMap v v' (F₁'.head f) = F₀'.head f :=
      fun f hf => (hends f (Finset.mem_of_mem_erase hf)).2
    have hF₀'_nv' : ∀ f ∈ F₀'.E, F₀'.tail f ≠ v' ∧ F₀'.head f ≠ v' := fun f hf =>
      let ⟨h1, h2⟩ := hVal₀ f (Finset.mem_of_mem_erase hf)
      ⟨fun heq => hv'NotV₀ (heq ▸ h1), fun heq => hv'NotV₀ (heq ▸ h2)⟩
    have hv_R1 : v ∈ insert r RF₁.R := Finset.mem_insert_of_mem (hR₁ ▸ Finset.mem_insert_of_mem hvR₀)
    have hv'_R1 : v' ∈ insert r RF₁.R := Finset.mem_insert_of_mem (hR₁ ▸ Finset.mem_insert_self _ _)
    have huniq0 : ∀ u ∈ RF₀.F.V, ∃! rt, rt ∈ insert r RF₀.R ∧ F₀'.Connected u rt := by
      intro u hu0
      have hu_ne_v' : u ≠ v' := fun h => hv'NotV₀ (h ▸ hu0)
      have hu1 : u ∈ RF₁.F.V := hV₁ ▸ Finset.mem_insert_of_mem hu0
      obtain ⟨rt1, ⟨hrt1_R, ⟨P1, hP1⟩⟩, hrt1_u⟩ := huniq1 u hu1
      set rt0 := unsplitMap v v' rt1
      have hrt0_R : rt0 ∈ insert r RF₀.R := by
        dsimp only [rt0, unsplitMap]
        split_ifs with h1
        · exact Finset.mem_insert_of_mem hvR₀
        · rw [hR₁] at hrt1_R
          rcases Finset.mem_insert.mp hrt1_R with rfl | h
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp h).resolve_left h1)
      have hconn0 : F₀'.Connected u rt0 := by
        have hc := walk_contract hE₁' ht' hh' hP1
        have hu_map : unsplitMap v v' u = u := by simp [unsplitMap, hu_ne_v']
        rw [hu_map] at hc
        exact ⟨P1, hc⟩
      refine ⟨rt0, ⟨hrt0_R, hconn0⟩, ?_⟩
      intro rt ⟨hrt_R, ⟨Q, hQ⟩⟩
      have hrt_ne_v' : rt ≠ v' := by
        intro h_eq
        cases hQ with
        | nil => exact hu_ne_v' h_eq
        | cons hzE hsrc hrest =>
          have hwalk_end : ∀ {a b : ℕ} {W : List (ℕ × Bool)}, F₀'.IsWalk a b W → W ≠ [] → b ≠ v' := by
            intro a b W hW'
            induction hW' with
            | nil _ => intro h; exact absurd rfl h
            | @cons x y z rest' hzE' _ hW'' ih'' =>
              intro _
              cases rest' with
              | nil =>
                cases hW''
                rcases z with ⟨f, dir⟩
                cases dir
                · exact (hF₀'_nv' f hzE').1
                · exact (hF₀'_nv' f hzE').2
              | cons _ _ => exact ih'' (List.cons_ne_nil _ _)
          exact hwalk_end (.cons hzE hsrc hrest) (List.cons_ne_nil _ _) h_eq
      have hrt_R1 : rt ∈ insert r RF₁.R := by
        rcases Finset.mem_insert.mp hrt_R with rfl | h
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hR₁ ▸ Finset.mem_insert_of_mem h)
      have hrt_V0 : rt ∈ RF₀.F.V := by
        cases hQ with
        | nil => exact hu0
        | cons hzE hsrc hrest =>
          have hwalk_endV : ∀ {a b : ℕ} {W : List (ℕ × Bool)}, F₀'.IsWalk a b W → W ≠ [] → b ∈ RF₀.F.V := by
            intro a b W hW'
            induction hW' with
            | nil _ => intro h; exact absurd rfl h
            | @cons x y z rest' hzE' _ hW'' ih'' =>
              intro _
              cases rest' with
              | nil =>
                cases hW''
                rcases z with ⟨f, dir⟩
                cases dir
                · exact (hVal₀ f (Finset.mem_of_mem_erase hzE')).1
                · exact (hVal₀ f (Finset.mem_of_mem_erase hzE')).2
              | cons _ _ => exact ih'' (List.cons_ne_nil _ _)
          exact hwalk_endV (.cons hzE hsrc hrest) (List.cons_ne_nil _ _)
      have hrt_eq_v_of_vv' : F₁'.Connected rt v ∨ F₁'.Connected rt v' → rt = v := by
        intro hc
        obtain ⟨r_rt, ⟨_, _⟩, hr_u⟩ := huniq1 rt (hV₁ ▸ Finset.mem_insert_of_mem hrt_V0)
        rcases hc with hc1 | hc2
        · exact (hr_u rt ⟨hrt_R1, ⟨[], .nil rt⟩⟩).trans (hr_u v ⟨hv_R1, hc1⟩).symm
        · exact absurd ((hr_u rt ⟨hrt_R1, ⟨[], .nil rt⟩⟩).trans (hr_u v' ⟨hv'_R1, hc2⟩).symm) hrt_ne_v'
      have hrt0_eq_v_of_vv' : F₁'.Connected u v ∨ F₁'.Connected u v' → rt0 = v := by
        intro hc
        rcases hc with hc1 | hc2
        · have heq := hrt1_u v ⟨hv_R1, hc1⟩
          dsimp only [rt0, unsplitMap]; rw [← heq, ite_eq_right hv_ne_v']
        · have heq := hrt1_u v' ⟨hv'_R1, hc2⟩
          dsimp only [rt0, unsplitMap]; rw [← heq, ite_eq_left rfl]
      rcases walk_lift_split hE₁' ht' hh' hF₀'_nv' hQ hu_ne_v' hrt_ne_v' with h1 | h2
      · have heq := hrt1_u rt ⟨hrt_R1, h1⟩
        dsimp only [rt0, unsplitMap]; rw [← heq, ite_eq_right hrt_ne_v']
      · have ⟨Qrev, hQrev⟩ := connected_symm ⟨Q, hQ⟩
        rcases walk_lift_split hE₁' ht' hh' hF₀'_nv' hQrev hrt_ne_v' hu_ne_v' with h1' | h2'
        · have heq := hrt1_u rt ⟨hrt_R1, connected_symm h1'⟩
          dsimp only [rt0, unsplitMap]; rw [← heq, ite_eq_right hrt_ne_v']
        · rw [hrt_eq_v_of_vv' h2', hrt0_eq_v_of_vv' h2]
    refine ⟨he0, hrCap, hrV0, hrNotR0, huniq0,
      compForestCutsValid_of_splitRoot rest (compApplyForestCut RF₀ (e, r))
        (compApplyForestCut RF₁ (e, r)) (fun f hf => hVal₀ f (Finset.mem_of_mem_erase hf))
        (Finset.mem_insert_of_mem hvR₀) hvV₀ hv'NotV₀ hV₁ hE₁'
        (by simp [compApplyForestCut, hR₁, Finset.insert_comm])
        (fun f hf => hends f (Finset.mem_of_mem_erase hf))
        (fun p hp => hne_v' p (List.mem_cons_of_mem _ hp)) hvalid_rest⟩

/-! ## 4. Assembly of `Read.LSFChange` from cuts and split vertices -/

/-- Build `Read.LSFChange` from the ordered cut sequence `cuts` and the split-created vertices
`splitVerts`, simultaneously giving P10's `LSFChange.Exact` and P2/P9's `CompForestCutsValid`. -/
lemma compForestCuts_to_lsfChange {vCap : ℕ} {cs cs' : CompLSFState}
    {cuts : List (ℕ × ℕ)} {splitVerts : List ℕ}
    (hvalid : CompForestCutsValid vCap cs.RF cuts)
    (hndE : (cuts.map Prod.fst).Nodup)
    (hsE : (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs'.RF.F.E)
    (hEsub : cs'.RF.F.E ⊆ cs.RF.F.E)
    (hndR : (cuts.map Prod.snd).Nodup)
    (hndS : splitVerts.Nodup)
    (hdisj : ∀ r ∈ cuts.map Prod.snd, r ∉ splitVerts)
    (hsR : (cuts.map Prod.snd).toFinset ∪ splitVerts.toFinset = cs'.RF.R \ cs.RF.R) :
    let chg : Read.LSFChange := ⟨cuts.map Prod.snd ++ splitVerts, cuts.map Prod.fst⟩
    chg.Exact cs.lsf cs'.lsf ∧
    chg.fDel.length ≤ chg.roots.length ∧
    List.zip chg.fDel chg.roots = cuts ∧
    CompForestCutsValid vCap cs.RF (List.zip chg.fDel chg.roots) ∧
    ((List.zip chg.fDel chg.roots).foldl compApplyForestCut cs.RF).F.E = cs'.RF.F.E := by
  intro chg
  have hzip : List.zip chg.fDel chg.roots = cuts := list_zip_map_append cuts splitVerts
  refine ⟨⟨List.nodup_append.mpr ⟨hndR, hndS, fun a ha b hb heq => hdisj a ha (heq ▸ hb)⟩,
      by simp [chg, List.toFinset_append, hsR, CompLSFState.lsf],
      hndE, by simpa [chg, CompLSFState.lsf] using hsE⟩,
    by simp [chg], hzip, hzip.symm ▸ hvalid, ?_⟩
  rw [hzip, compApplyForestCut_foldl_E, hsE]
  ext e; simp only [Finset.mem_sdiff]; constructor
  · rintro ⟨h1, h2⟩; by_contra hc; exact h2 ⟨h1, hc⟩
  · intro h; exact ⟨hEsub h, fun h' => h'.2 h⟩

end

end MinCostFlow.SparseCore.Program
