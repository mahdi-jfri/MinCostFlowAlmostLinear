module

public import MinCostFlow.LSF.Program.BatchAddRootMath
import Mathlib.Tactic.Linarith

/-!
# Single-Update Transition Math for LSF Batch Updates (`BatchSplitMath`)

Connects `applyLSFUpdate S u` to the step-by-step Word-RAM updates executed by `lsfApplyUpdateProc`:

* `applyLSFUpdate_insert_eq` and `applyLSFUpdate_delete_eq`: factoring `R₀_base` root insertions
  ahead of graph/T-block/stretch updates so `addOrigRoot_call_runs` applies directly to intermediate
  valid `LSFState`s.
* `applyLSFUpdate_split_step`: after adding `S.origVert v` as a root (`S₁`), splitting `v` into
  `(v, v')` in `S₁.RF.F` yields `S'.RF.F`, preserves `S'.R = insert v' S₁.R`, and partitions `v`'s
  component of `S₁.RF.F` into two disjoint components of `S'.RF.F` rooted at `v` and `v'` whose
  cardinalities sum to `oldSize + 1`, matching all hypotheses of `fancAt_after_splitCompBFS` and
  `phi_drop_split`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Insert and delete transition factoring -/

/-- Factoring `.insert e u v`: inserting `u` and `v` (when in `S.T₀.V`) into `R₀_base` first
produces the exact same `R_orig`, `R`, and `RF` as `applyLSFUpdate S (.insert e u v)`. -/
lemma applyLSFUpdate_insert_eq {S : LSFState} (hInv : LSFStructInv S) {e u v : ℕ}
    (hu : S.G.UpdateIsValid (.insert e u v)) :
    let S₁ : LSFState := if u ∈ S.T₀.V then { S with R₀_base := insert u S.R₀_base } else S
    let S₂ : LSFState := if v ∈ S.T₀.V then { S₁ with R₀_base := insert v S₁.R₀_base } else S₁
    let S' : LSFState := applyLSFUpdate S (.insert e u v)
    LSFStructInv S₁ ∧ LSFStructInv S₂ ∧ LSFStructInv S' ∧
    S'.R₀_base = S₂.R₀_base ∧ S'.R_orig = S₂.R_orig ∧ S'.R = S₂.R ∧ S'.RF = S₂.RF := by
  classical
  intro S₁ S₂ S'
  have hInv₁ : LSFStructInv S₁ := by
    dsimp only [S₁]; split_ifs with huT
    · exact (hInv.addOrigRoot_inv huT).1
    · exact hInv
  have hT₀₁ : S₁.T₀ = S.T₀ := by dsimp only [S₁]; split_ifs <;> rfl
  have hInv₂ : LSFStructInv S₂ := by
    dsimp only [S₂]; split_ifs with hvT
    · exact (hInv₁.addOrigRoot_inv (hT₀₁.symm ▸ hvT)).1
    · exact hInv₁
  have hInv' : LSFStructInv S' := applyLSFUpdate_structInv hInv hu
  have hR0 : S'.R₀_base = S₂.R₀_base := by
    ext x
    dsimp only [S', S₂, S₁, applyLSFUpdate]
    by_cases huT : u ∈ S.T₀.V <;> by_cases hvT : v ∈ S.T₀.V <;>
      simp only [huT, hvT, ↓reduceIte, Finset.mem_union, Finset.mem_filter,
        Finset.mem_insert, Finset.mem_singleton] <;>
      constructor <;> intro h
    · rcases h with h | ⟨rfl | rfl, _⟩ <;> tauto
    · rcases h with rfl | rfl | h <;> tauto
    · rcases h with h | ⟨rfl | rfl, hxT⟩
      · exact Or.inr h
      · exact Or.inl rfl
      · exact absurd hxT hvT
    · rcases h with rfl | h
      · exact Or.inr ⟨Or.inl rfl, huT⟩
      · exact Or.inl h
    · rcases h with h | ⟨rfl | rfl, hxT⟩
      · exact Or.inr h
      · exact absurd hxT huT
      · exact Or.inl rfl
    · rcases h with rfl | h
      · exact Or.inr ⟨Or.inr rfl, hvT⟩
      · exact Or.inl h
    · rcases h with h | ⟨rfl | rfl, hxT⟩
      · exact h
      · exact absurd hxT huT
      · exact absurd hxT hvT
    · exact Or.inl h
  have hT₀₂ : S₂.T₀ = S.T₀ := by dsimp only [S₂, S₁]; split_ifs <;> rfl
  have hr₀₂ : S₂.r₀ = S.r₀ := by dsimp only [S₂, S₁]; split_ifs <;> rfl
  have hπ₂ : S₂.π = S.π := by dsimp only [S₂, S₁]; split_ifs <;> rfl
  have hTcur₂ : S₂.T_cur = S.T_cur := by dsimp only [S₂, S₁]; split_ifs <;> rfl
  have hiso₂ : S₂.isolatedVerts = S.isolatedVerts := by dsimp only [S₂, S₁]; split_ifs <;> rfl
  have hRorig : S'.R_orig = S₂.R_orig := by
    simp only [LSFState.R_orig, LSFState.TH, hR0, hT₀₂, hr₀₂]; rfl
  have hR : S'.R = S₂.R := by simp only [LSFState.R, hRorig, hiso₂]; rfl
  have hRF : S'.RF = S₂.RF := by
    simp only [LSFState.RF, hTcur₂, hT₀₂, hr₀₂, hRorig, hπ₂, hR]; rfl
  exact ⟨hInv₁, hInv₂, hInv', hR0, hRorig, hR, hRF⟩

/-- Factoring `.delete e`: inserting `origVert (G.tail e)` and `origVert (G.head e)` into `R₀_base`
first produces the exact same `R_orig`, `R`, and `RF` as `applyLSFUpdate S (.delete e)`. -/
lemma applyLSFUpdate_delete_eq {S : LSFState} (hInv : LSFStructInv S) {e : ℕ}
    (he : e ∈ S.G.E) :
    let uOrig := S.origVert (S.G.tail e)
    let vOrig := S.origVert (S.G.head e)
    let S₁ : LSFState := { S with R₀_base := insert uOrig S.R₀_base }
    let S₂ : LSFState := { S₁ with R₀_base := insert vOrig S₁.R₀_base }
    let S' : LSFState := applyLSFUpdate S (.delete e)
    uOrig ∈ S.T₀.V ∧ vOrig ∈ S.T₀.V ∧
    LSFStructInv S₁ ∧ LSFStructInv S₂ ∧ LSFStructInv S' ∧
    S'.R₀_base = S₂.R₀_base ∧ S'.R_orig = S₂.R_orig ∧ S'.R = S₂.R ∧ S'.RF = S₂.RF := by
  classical
  intro uOrig vOrig S₁ S₂ S'
  have huT : uOrig ∈ S.T₀.V := hInv.origVert_mem_TV (hInv.hG_val e he).1
  have hvT : vOrig ∈ S.T₀.V := hInv.origVert_mem_TV (hInv.hG_val e he).2
  have hInv₁ : LSFStructInv S₁ := (hInv.addOrigRoot_inv huT).1
  have hInv₂ : LSFStructInv S₂ := (hInv₁.addOrigRoot_inv hvT).1
  have hInv' : LSFStructInv S' := applyLSFUpdate_structInv hInv he
  have hR0 : S'.R₀_base = S₂.R₀_base := by
    ext x
    simp only [S', S₂, S₁, applyLSFUpdate, Finset.mem_union, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | ⟨rfl | rfl, _⟩) <;> tauto
    · rintro (rfl | rfl | h)
      · exact Or.inr ⟨Or.inr rfl, hvT⟩
      · exact Or.inr ⟨Or.inl rfl, huT⟩
      · exact Or.inl h
  have hRorig : S'.R_orig = S₂.R_orig := by simp only [LSFState.R_orig, LSFState.TH, hR0]; rfl
  have hR : S'.R = S₂.R := by simp only [LSFState.R, hRorig]; rfl
  have hRF : S'.RF = S₂.RF := by simp only [LSFState.RF, hRorig, hR]; rfl
  exact ⟨huT, hvT, hInv₁, hInv₂, hInv', hR0, hRorig, hR, hRF⟩

/-! ## Pure forest-split component partition lemmas -/

private lemma forest_split_walk_proj {F : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (hF : F.IsValid) (hv' : v' ∉ F.V)
    {a b : ℕ} {P : List (ℕ × Bool)}
    (hW : (F.applyUpdate (.split v v' St Sh)).IsWalk a b P) :
    let proj : ℕ → ℕ := fun x => if x = v' then v else x
    F.IsWalk (proj a) (proj b) P := by
  intro proj
  refine proj_isWalk (H := F.applyUpdate (.split v v' St Sh)) (K := F) (proj := proj) (fun e he => ?_) hW
  have heF := hF e he
  have ht_ne : F.tail e ≠ v' := fun h => hv' (h ▸ heF.1)
  have hh_ne : F.head e ≠ v' := fun h => hv' (h ▸ heF.2)
  refine ⟨he, ?_, ?_⟩
  · by_cases ht : e ∈ St ∧ F.tail e = v <;> simp [MGraph.applyUpdate, proj, ht, ht_ne]
  · by_cases hh : e ∈ Sh ∧ F.head e = v <;> simp [MGraph.applyUpdate, proj, hh, hh_ne]

private lemma forest_split_not_connected_vv' {F : MGraph} (hF : F.IsForest)
    {v v' : ℕ} (hv : v ∈ F.V) (hv' : v' ∉ F.V) (St Sh : Finset ℕ) :
    ¬ (F.applyUpdate (.split v v' St Sh)).Connected v v' := by
  let F' := F.applyUpdate (.split v v' St Sh)
  intro hconn
  have hF' : F'.IsForest := applyUpdate_split_isForest hF hv hv' St Sh
  have hP := forestPath_isPath hF' hconn
  have hne_nil : F'.forestPath v v' ≠ [] := by
    intro hnil
    have hw := hP.1; rw [hnil] at hw
    cases hw; exact hv' hv
  have hproj := forest_split_walk_proj hF.1 hv' hP.1
  have hv_ne : v ≠ v' := fun h => hv' (h ▸ hv)
  simp only [hv_ne, ↓reduceIte] at hproj
  exact hF.2 (F'.forestPath v v') ⟨hne_nil, isPath_nodup_edges hP, v, hproj⟩

private lemma forest_split_lift_walk {F : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (_hF : F.IsValid) (_hv' : v' ∉ F.V)
    {a b : ℕ} {P : List (ℕ × Bool)} (hW : F.IsWalk a b P)
    (hno_v : ∀ x ∈ F.walkVertices a P, x ≠ v) :
    (F.applyUpdate (.split v v' St Sh)).IsWalk a b P := by
  induction hW with
  | nil s => exact .nil s
  | @cons u w x xs hxE hsrc hrest ih =>
    have hu_ne : u ≠ v := hno_v u (by rw [walkVertices_cons]; exact List.mem_cons_self)
    have hrest_no : ∀ y ∈ F.walkVertices (F.dst x) xs, y ≠ v := fun y hy =>
      hno_v y (by rw [walkVertices_cons]; exact List.mem_cons_of_mem u hy)
    have hdst_ne : F.dst x ≠ v := hrest_no (F.dst x) (by simp [MGraph.walkVertices])
    have hsrc' : (F.applyUpdate (.split v v' St Sh)).src x = u := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.src, MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      · rw [hsrc, ite_eq_right (fun h => hu_ne h.2)]
      · rw [hsrc, ite_eq_right (fun h => hu_ne h.2)]
    have hdst' : (F.applyUpdate (.split v v' St Sh)).dst x = F.dst x := by
      rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] at hdst_ne ⊢
      · rw [ite_eq_right (fun h => hdst_ne h.2)]
      · rw [ite_eq_right (fun h => hdst_ne h.2)]
    exact .cons hxE hsrc' (hdst' ▸ ih hrest_no)

private lemma isWalk_mem_walkVertices_connected' {G : MGraph} {a b x : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk a b P) (hx : x ∈ G.walkVertices a P) : G.Connected a x := by
  induction hW with
  | nil s =>
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hx
    exact hx ▸ connected_refl G s
  | @cons u w e es he hsrc hrest ih =>
    rw [walkVertices_cons, List.mem_cons] at hx
    rcases hx with hxu | hx
    · exact hxu ▸ connected_refl G u
    · exact connected_trans ⟨[e], .cons he hsrc (.nil _)⟩ (ih hx)

/-- Lifting an `F`-walk from `a` to `v` into `F' = F.applyUpdate (.split v v' St Sh)`: every vertex
connected to `v` in `F` is connected to either `v` or `v'` in `F'`. -/
private lemma forest_split_connected_to_v_or_v' {F : MGraph}
    {v v' : ℕ} (St Sh : Finset ℕ) {a : ℕ} {P : List (ℕ × Bool)}
    (hW : F.IsWalk a v P) :
    (F.applyUpdate (.split v v' St Sh)).Connected a v ∨
    (F.applyUpdate (.split v v' St Sh)).Connected a v' := by
  let F' := F.applyUpdate (.split v v' St Sh)
  induction P generalizing a with
  | nil =>
    cases hW; exact Or.inl (connected_refl F' v)
  | cons x xs ih =>
    cases hW with
    | cons hxE hsrc hrest =>
      by_cases hav : a = v
      · rw [hav]; exact Or.inl (connected_refl F' v)
      · have hsrc' : F'.src x = a := by
          rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.src, F', MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
          · rw [hsrc, ite_eq_right (fun h => hav h.2)]
          · rw [hsrc, ite_eq_right (fun h => hav h.2)]
        by_cases hdv : F.dst x = v
        · have hdst_or : F'.dst x = v ∨ F'.dst x = v' := by
            rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, F', MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] at hdv ⊢
            · by_cases h : f ∈ St ∧ F.tail f = v
              · exact Or.inr (by simp [h])
              · exact Or.inl (by rw [ite_eq_right h]; exact hdv)
            · by_cases h : f ∈ Sh ∧ F.head f = v
              · exact Or.inr (by simp [h])
              · exact Or.inl (by rw [ite_eq_right h]; exact hdv)
          rcases hdst_or with hd | hd
          · exact Or.inl ⟨[x], .cons hxE hsrc' (by rw [hd]; exact .nil _)⟩
          · exact Or.inr ⟨[x], .cons hxE hsrc' (by rw [hd]; exact .nil _)⟩
        · have hdst' : F'.dst x = F.dst x := by
            rcases x with ⟨f, _ | _⟩ <;> simp only [MGraph.dst, F', MGraph.applyUpdate, Bool.false_eq_true, ↓reduceIte] at hdv ⊢
            · rw [ite_eq_right (fun h => hdv h.2)]
            · rw [ite_eq_right (fun h => hdv h.2)]
          have hstep : F'.Connected a (F.dst x) := ⟨[x], .cons hxE hsrc' (hdst' ▸ .nil _)⟩
          rcases ih hrest with h1 | h2
          · exact Or.inl (connected_trans hstep h1)
          · exact Or.inr (connected_trans hstep h2)

/-! ## Full split transition lemma for `LSFState` -/

open Classical in
/-- Single-step `.split v v' St Sh` transition lemma connecting `S` → `S₁` (after `addOrigRoot` on
`S.origVert v`) → `S' = applyLSFUpdate S (.split v v' St Sh)`. Supplies every graph/connectivity
and cardinality hypothesis required by `DynGraphAt.congr_ends`, `fancAt_after_splitCompBFS`,
`splitCompBFSContract`, and `phi_drop_split`. -/
lemma applyLSFUpdate_split_step {S : LSFState} (hInv : LSFStructInv S)
    {v v' : ℕ} {St Sh : Finset ℕ} (hu : S.G.UpdateIsValid (.split v v' St Sh)) :
    let vOrig := S.origVert v
    let S₁ : LSFState := { S with R₀_base := insert vOrig S.R₀_base }
    let S' : LSFState := applyLSFUpdate S (.split v v' St Sh)
    let F_res := S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))
    vOrig ∈ S.T₀.V ∧
    LSFStructInv S₁ ∧ LSFStructInv S' ∧
    S'.R_orig = S₁.R_orig ∧
    v ∈ S₁.R ∧ v' ∉ S₁.R ∧ S'.R = insert v' S₁.R ∧
    (F_res.V = S'.RF.F.V ∧ F_res.E = S'.RF.F.E ∧
      ∀ e ∈ F_res.E, F_res.tail e = S'.RF.F.tail e ∧ F_res.head e = S'.RF.F.head e) ∧
    v ∈ S'.RF.F.V ∧ v' ∈ S'.RF.F.V ∧ ¬ S'.RF.F.Connected v v' ∧
    (∀ u ∈ S'.RF.F.V, (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') ↔
      (u = v' ∨ (u ∈ S₁.RF.F.V ∧ S₁.RF.F.Connected u v))) ∧
    (∀ u ∈ S'.RF.F.V, ¬ S'.RF.F.Connected u v → ¬ S'.RF.F.Connected u v' →
      u ∈ S₁.RF.F.V ∧ ∀ w ∈ S₁.RF.F.V, S'.RF.F.Connected u w ↔ S₁.RF.F.Connected u w) ∧
    (∀ u ∈ S'.RF.F.V, ∀ w ∈ S'.RF.F.V,
      (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') →
      ¬ S'.RF.F.Connected w v → ¬ S'.RF.F.Connected w v' →
      ¬ S'.RF.F.Connected u w) ∧
    ((S'.RF.F.Connected v v ∧ S'.RF.F.Connected v' v') ∨
      (S'.RF.F.Connected v v' ∧ S'.RF.F.Connected v' v)) ∧
    (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v).card + 1 =
      (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v).card +
      (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v').card := by
  intro vOrig S₁ S' F_res
  have hvOrig_T : vOrig ∈ S.T₀.V := hInv.origVert_mem_TV hu.1
  have hInv₁ : LSFStructInv S₁ := (hInv.addOrigRoot_inv hvOrig_T).1
  have hInv' : LSFStructInv S' := applyLSFUpdate_structInv hInv hu
  have hR0' : S'.R₀_base = S₁.R₀_base := by
    dsimp only [S', S₁, applyLSFUpdate]; rw [ite_eq_left hvOrig_T]
  have hRorig' : S'.R_orig = S₁.R_orig := by simp only [LSFState.R_orig, LSFState.TH, hR0']; rfl
  have hvOrig_R1 : vOrig ∈ S₁.R_orig := subset_upClosure (Finset.mem_insert_self vOrig S.R₀_base)
  have hv_R1 : v ∈ S₁.R :=
    (origVert_mem_R_iff hInv₁.hGV_eq hInv₁.hdisj_iso hInv₁.R_orig_sub hInv₁.horig_id
      hInv₁.horig_split hu.1).mpr hvOrig_R1
  have hv'_not_R1 : v' ∉ S₁.R := fun h => hu.2.1 (hInv₁.to_RF_spanning.2.2.1 h)
  have hR' : S'.R = insert v' S₁.R := by
    dsimp only [LSFState.R]
    rw [hRorig']
    change S₁.R_orig ∪ insert v' S.isolatedVerts = insert v' (S₁.R_orig ∪ S.isolatedVerts)
    rw [Finset.union_insert]
  have hE_eq : S'.RF.F.E = S₁.RF.F.E := by
    show (forestGivenRoots S'.T₀ S'.r₀ S'.R_orig S'.π).E = (forestGivenRoots S₁.T₀ S₁.r₀ S₁.R_orig S₁.π).E
    rw [hRorig']; rfl
  have hF'_eq : S'.RF.F = S₁.RF.F.applyUpdate (.split v v' St Sh) := by
    cases h1 : S'.RF.F with
    | mk V1 E1 t1 h1_ =>
      have hV1 : V1 = insert v' S₁.RF.F.V := by
        have : S'.RF.F.V = insert v' S₁.RF.F.V := rfl; rwa [h1] at this
      have hE1 : E1 = S₁.RF.F.E := by rwa [h1] at hE_eq
      have ht1 : t1 = (S₁.RF.F.applyUpdate (.split v v' St Sh)).tail := by
        have : S'.RF.F.tail = (S₁.RF.F.applyUpdate (.split v v' St Sh)).tail := rfl; rwa [h1] at this
      have hh1 : h1_ = (S₁.RF.F.applyUpdate (.split v v' St Sh)).head := by
        have : S'.RF.F.head = (S₁.RF.F.applyUpdate (.split v v' St Sh)).head := rfl; rwa [h1] at this
      subst hV1 hE1 ht1 hh1; rfl
  have hFres_congr : F_res.V = S'.RF.F.V ∧ F_res.E = S'.RF.F.E ∧
      ∀ e ∈ F_res.E, F_res.tail e = S'.RF.F.tail e ∧ F_res.head e = S'.RF.F.head e := by
    rw [hF'_eq]
    refine ⟨rfl, rfl, fun e he => ?_⟩
    have he1 : e ∈ S₁.RF.F.E := he
    simp [F_res, MGraph.applyUpdate, he1]
  have hF1_for : S₁.RF.F.IsForest := hInv₁.to_RF_spanning.1
  have hv_F1 : v ∈ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu.1
  have hv'_not_F1 : v' ∉ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu.2.1
  have hv_F' : v ∈ S'.RF.F.V := hF'_eq ▸ Finset.mem_insert_of_mem hv_F1
  have hv'_F' : v' ∈ S'.RF.F.V := hF'_eq ▸ Finset.mem_insert_self v' S₁.RF.F.V
  have hnot_vv' : ¬ S'.RF.F.Connected v v' := by
    rw [hF'_eq]; exact forest_split_not_connected_vv' hF1_for hv_F1 hv'_not_F1 St Sh
  have hpart_V : ∀ u ∈ S'.RF.F.V, (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') ↔
      (u = v' ∨ (u ∈ S₁.RF.F.V ∧ S₁.RF.F.Connected u v)) := by
    intro u hu'
    rw [hF'_eq] at hu' ⊢
    constructor
    · rintro (⟨P, hP⟩ | ⟨P, hP⟩)
      · by_cases huv' : u = v'
        · exact Or.inl huv'
        · right
          have hu1 : u ∈ S₁.RF.F.V := (Finset.mem_insert.mp hu').resolve_left huv'
          refine ⟨hu1, ⟨P, ?_⟩⟩
          have hpr := forest_split_walk_proj hF1_for.1 hv'_not_F1 hP
          have hv_ne : v ≠ v' := fun h => hv'_not_F1 (h ▸ hv_F1)
          simpa [huv', hv_ne] using hpr
      · by_cases huv' : u = v'
        · exact Or.inl huv'
        · right
          have hu1 : u ∈ S₁.RF.F.V := (Finset.mem_insert.mp hu').resolve_left huv'
          refine ⟨hu1, ⟨P, ?_⟩⟩
          have hpr := forest_split_walk_proj hF1_for.1 hv'_not_F1 hP
          simpa [huv'] using hpr
    · rintro (huv' | ⟨_, ⟨P, hP⟩⟩)
      · rw [huv']; exact Or.inr (connected_refl _ v')
      · exact forest_split_connected_to_v_or_v' St Sh hP
  have hV'_eq : S'.RF.F.V = insert v' S₁.RF.F.V := by rw [hF'_eq]; rfl
  have hother_conn : ∀ u ∈ S'.RF.F.V, ¬ S'.RF.F.Connected u v → ¬ S'.RF.F.Connected u v' →
      u ∈ S₁.RF.F.V ∧ ∀ w ∈ S₁.RF.F.V, S'.RF.F.Connected u w ↔ S₁.RF.F.Connected u w := by
    intro u hu' hnuv hnuv'
    have hnot_rhs : ¬ (u = v' ∨ (u ∈ S₁.RF.F.V ∧ S₁.RF.F.Connected u v)) := by
      intro h; rcases (hpart_V u hu').mpr h with hc | hc <;> [exact hnuv hc; exact hnuv' hc]
    have hu_ne : u ≠ v' := fun h => hnot_rhs (Or.inl h)
    have hu1 : u ∈ S₁.RF.F.V := (Finset.mem_insert.mp (hV'_eq ▸ hu')).resolve_left hu_ne
    have hnot_uv1 : ¬ S₁.RF.F.Connected u v := fun hc => hnot_rhs (Or.inr ⟨hu1, hc⟩)
    refine ⟨hu1, fun w hw1 => ?_⟩
    have hw_ne : w ≠ v' := fun h => hv'_not_F1 (h ▸ hw1)
    constructor
    · rintro ⟨P, hP⟩
      rw [hF'_eq] at hP
      have hpr := forest_split_walk_proj hF1_for.1 hv'_not_F1 hP
      dsimp only at hpr
      rw [ite_eq_right hu_ne, ite_eq_right hw_ne] at hpr
      exact ⟨P, hpr⟩
    · rintro ⟨P, hP⟩
      have hno_v : ∀ x ∈ S₁.RF.F.walkVertices u P, x ≠ v := by
        intro x hx hxv; subst hxv
        exact hnot_uv1 (isWalk_mem_walkVertices_connected' hP hx)
      rw [hF'_eq]
      exact ⟨P, forest_split_lift_walk hF1_for.1 hv'_not_F1 hP hno_v⟩
  have hother_disj : ∀ u ∈ S'.RF.F.V, ∀ w ∈ S'.RF.F.V,
      (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') →
      ¬ S'.RF.F.Connected w v → ¬ S'.RF.F.Connected w v' →
      ¬ S'.RF.F.Connected u w := by
    intro u _ w _ hu_or hnwv hnwv' huw
    rcases hu_or with hc | hc
    · exact hnwv (connected_trans (connected_symm huw) hc)
    · exact hnwv' (connected_trans (connected_symm huw) hc)
  have hsum_eq : (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v).card + 1 =
      (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v).card +
      (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v').card := by
    set CA := S'.RF.F.V.filter fun u => S'.RF.F.Connected u v
    set CB := S'.RF.F.V.filter fun u => S'.RF.F.Connected u v'
    have hdisj : Disjoint CA CB := by
      rw [Finset.disjoint_left]; intro x hxA hxB
      exact hnot_vv' (connected_trans (connected_symm (Finset.mem_filter.mp hxA).2)
        (Finset.mem_filter.mp hxB).2)
    have hunion : CA ∪ CB = insert v' (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v) := by
      ext u
      simp only [CA, CB, Finset.mem_union, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro (⟨hu', hc⟩ | ⟨hu', hc⟩)
        · exact (hpart_V u hu').mp (Or.inl hc)
        · exact (hpart_V u hu').mp (Or.inr hc)
      · rintro (huv' | ⟨hu1, hc⟩)
        · rw [huv']; exact Or.inr ⟨hv'_F', connected_refl _ v'⟩
        · have hu' : u ∈ S'.RF.F.V := hV'_eq ▸ Finset.mem_insert_of_mem hu1
          rcases (hpart_V u hu').mpr (Or.inr ⟨hu1, hc⟩) with h1 | h2
          · exact Or.inl ⟨hu', h1⟩
          · exact Or.inr ⟨hu', h2⟩
    have hv'_not_f : v' ∉ S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v :=
      fun h => hv'_not_F1 (Finset.mem_filter.mp h).1
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_insert_of_notMem hv'_not_f]
  exact ⟨hvOrig_T, hInv₁, hInv', hRorig', hv_R1, hv'_not_R1, hR', hFres_congr,
    hv_F', hv'_F', hnot_vv', hpart_V, hother_conn, hother_disj,
    Or.inl ⟨connected_refl _ v, connected_refl _ v'⟩, hsum_eq⟩

end

end MinCostFlow.LSF.Program
