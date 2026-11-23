module

public import MinCostFlow.SparseCore.Program.TourSurgerySplit
public import MinCostFlow.SparseCore.Program.TourEditMath
import MinCostFlow.Bundle.TourSplit
import Mathlib.Tactic

/-!
# Vertex-split (`moveEnds`) graph validity and block-partition math

Proves `tourValid_applyEdit_moveEnds`, `fullTour_moveEnds_other`, and the `fullBlock`
index-monotonicity and iterative block-splitting lemmas for `moveEnds`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

/-! ## Edge-distinct walks and split-forest connectivity -/

theorem isWalk_append {F : MGraph} {a b c : ℕ} {P Q : List End}
    (hP : F.IsWalk a b P) (hQ : F.IsWalk b c Q) : F.IsWalk a c (P ++ Q) := by
  induction hP with
  | nil _ => exact hQ
  | cons he hsrc _ ih => exact .cons he hsrc (ih hQ)

theorem isWalk_split_append {F : MGraph} {a c : ℕ} {P Q : List End}
    (h : F.IsWalk a c (P ++ Q)) : ∃ b, F.IsWalk a b P ∧ F.IsWalk b c Q := by
  induction P generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons x xs ih =>
    cases h with
    | cons he hsrc htl =>
      obtain ⟨b, h1, h2⟩ := ih htl
      exact ⟨b, .cons he hsrc h1, h2⟩

theorem connected_exists_nodup_walk {F : MGraph} {a b : ℕ} (h : F.Connected a b) :
    ∃ P, F.IsWalk a b P ∧ (P.map Prod.fst).Nodup := by
  obtain ⟨P, hP⟩ := h
  suffices ∀ n, ∀ Q : List End, Q.length ≤ n → F.IsWalk a b Q → ∃ R, F.IsWalk a b R ∧ (R.map Prod.fst).Nodup from
    this P.length P (le_refl _) hP
  intro n
  induction n with
  | zero =>
    intro Q hlen hQ
    cases Q with
    | nil => exact ⟨[], hQ, List.nodup_nil⟩
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro Q hlen hQ
    by_cases hnd : (Q.map Prod.fst).Nodup
    · exact ⟨Q, hQ, hnd⟩
    · have hdup : ∃ A x B y C, Q = A ++ x :: (B ++ y :: C) ∧ x.1 = y.1 := by
        clear * - hnd
        induction Q with
        | nil => exact absurd List.nodup_nil hnd
        | cons x xs ihq =>
          simp only [List.map_cons, List.nodup_cons] at hnd
          by_cases hm : x.1 ∈ xs.map Prod.fst
          · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
            obtain ⟨B, C, rfl⟩ := List.mem_iff_append.mp hy
            exact ⟨[], x, B, y, C, rfl, hxy.symm⟩
          · push Not at hnd
            obtain ⟨A, u, B, v, C, rfl, huv⟩ := ihq (hnd hm)
            exact ⟨x :: A, u, B, v, C, rfl, huv⟩
      obtain ⟨A, x, B, y, C, rfl, hxy⟩ := hdup
      obtain ⟨u₁, hA, hrest1⟩ := isWalk_split_append hQ
      cases hrest1 with
      | cons hxE hxS hrest2 =>
        obtain ⟨u₂, _, hrest3⟩ := isWalk_split_append hrest2
        cases hrest3 with
        | cons hyE hyS hC =>
          by_cases hside : x.2 = y.2
          · have hxeqy : x = y := Prod.ext hxy hside
            subst hxeqy
            have hshort : F.IsWalk a b (A ++ x :: C) :=
              isWalk_append hA (.cons hxE hxS hC)
            exact ih (A ++ x :: C) (by simp at hlen ⊢; omega) hshort
          · have hdst_y : F.dst y = F.src x := by
              obtain ⟨e1, b1⟩ := x; obtain ⟨e2, b2⟩ := y
              change e1 = e2 at hxy; subst e2
              cases b1 <;> cases b2 <;> simp_all [MGraph.src, MGraph.dst]
            have hAC : F.IsWalk a b (A ++ C) :=
              isWalk_append hA (by rw [← hxS, ← hdst_y]; exact hC)
            exact ih (A ++ C) (by simp at hlen ⊢; omega) hAC

theorem connected_applySplit_lift_avoiding {F : MGraph} {v v' : ℕ}
    (St Sh : Finset ℕ) {a b : ℕ}
    (P : List End) (hwalk : F.IsWalk a b P) (hnoV : ∀ x ∈ P, F.src x ≠ v ∧ F.dst x ≠ v) :
    (F.applyUpdate (.split v v' St Sh)).IsWalk a b P := by
  induction hwalk with
  | nil u => exact .nil u
  | @cons a b x xs he hsrc _ ih =>
    have hxv : F.src x ≠ v := (hnoV x (by simp)).1
    have hdv : F.dst x ≠ v := (hnoV x (by simp)).2
    have hsrc' : (F.applyUpdate (.split v v' St Sh)).src x = F.src x := by
      obtain ⟨e, side⟩ := x; cases side <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, MGraph.applyUpdate] at hxv ⊢ <;> simp [hxv]
    have hdst' : (F.applyUpdate (.split v v' St Sh)).dst x = F.dst x := by
      obtain ⟨e, side⟩ := x; cases side <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte, MGraph.applyUpdate] at hdv ⊢ <;> simp [hdv]
    exact .cons he (by rw [hsrc', hsrc]) (hdst' ▸ ih fun y hy => hnoV y (by simp [hy]))

theorem connected_applySplit_v_or_v' {F : MGraph} (hF : F.IsForest) {v v' : ℕ}
    (St Sh : Finset ℕ) {u : ℕ} (hconn : F.Connected v u) :
    let F' := F.applyUpdate (.split v v' St Sh)
    F'.Connected v u ∨ F'.Connected v' u := by
  intro F'
  by_cases huv : u = v
  · exact Or.inl (huv ▸ connected_refl F' v)
  · obtain ⟨P, hwalk, hnd⟩ := connected_exists_nodup_walk hconn
    cases P with
    | nil => cases hwalk; exact absurd rfl huv
    | cons x xs =>
      cases hwalk with
      | cons he hsrc hrest =>
        have hnoV : ∀ y ∈ xs, F.src y ≠ v ∧ F.dst y ≠ v := by
          intro y hy
          have hsub_walk : (eraseForestEdge F x.1).IsWalk (F.dst x) u xs := by
            have hnotx : x.1 ∉ xs.map Prod.fst := (List.nodup_cons.mp hnd).1
            clear * - hrest hnotx
            generalize F.dst x = w0 at hrest ⊢
            induction hrest with
            | nil w => exact .nil w
            | @cons a b z zs hze hzs _ ih =>
              have hne : z.1 ≠ x.1 := fun h => hnotx (by simp [h])
              exact .cons (Finset.mem_erase.mpr ⟨hne, hze⟩) hzs (ih (fun hm => hnotx (by simp [hm])))
          have hreach_y : ∀ a b Q, (eraseForestEdge F x.1).IsWalk a b Q → y ∈ Q →
              (eraseForestEdge F x.1).Connected a (F.src y) ∧ (eraseForestEdge F x.1).Connected a (F.dst y) := by
            intro a b Q hQ hyQ
            induction hQ with
            | nil _ => simp at hyQ
            | @cons a b z zs hze hzs _ ih =>
              rcases List.mem_cons.mp hyQ with rfl | hyzs
              · exact ⟨hzs ▸ connected_refl _ _, ⟨[y], .cons hze hzs (.nil _)⟩⟩
              · have hstep : (eraseForestEdge F x.1).Connected a (F.dst z) := ⟨[z], .cons hze hzs (.nil _)⟩
                have ⟨h1, h2⟩ := ih hyzs
                exact ⟨connected_trans hstep h1, connected_trans hstep h2⟩
          have ⟨hcs, hcd⟩ := hreach_y _ _ _ hsub_walk hy
          have hnc_v := not_connected_eraseForestEdge hF he
          have hv_src : F.src x = v := hsrc
          refine ⟨fun h => hnc_v (by rw [hv_src]; exact connected_symm (h ▸ hcs)),
                  fun h => hnc_v (by rw [hv_src]; exact connected_symm (h ▸ hcd))⟩
        have hrest' : F'.IsWalk (F.dst x) u xs := connected_applySplit_lift_avoiding St Sh xs hrest hnoV
        have hdst_ne : F.dst x ≠ v := fun h =>
          isForest_no_selfLoop hF he (by
            obtain ⟨e, b⟩ := x; cases b <;> simp [MGraph.src, MGraph.dst] at hsrc h ⊢ <;> omega)
        have hdst' : F'.dst x = F.dst x := by
          obtain ⟨e, b⟩ := x
          cases b <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte, F', MGraph.applyUpdate] at hdst_ne ⊢ <;> simp [hdst_ne]
        have hsrc'_cases : F'.src x = v ∨ F'.src x = v' := by
          obtain ⟨e, b⟩ := x
          cases b <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, F', MGraph.applyUpdate] at hsrc ⊢
          · split_ifs; exact Or.inr rfl; exact Or.inl hsrc
          · split_ifs; exact Or.inr rfl; exact Or.inl hsrc
        rcases hsrc'_cases with hs | hs
        · exact Or.inl ⟨x :: xs, .cons he hs (hdst'.symm ▸ hrest')⟩
        · exact Or.inr ⟨x :: xs, .cons he hs (hdst'.symm ▸ hrest')⟩

theorem not_connected_v_v'_applySplit {F : MGraph} (hF : F.IsForest) {v v' : ℕ}
    (hne : v ≠ v') (hv' : v' ∉ F.V) (St Sh : Finset ℕ) :
    ¬ (F.applyUpdate (.split v v' St Sh)).Connected v v' := by
  intro hconn
  obtain ⟨Q, hQ, hnd⟩ := connected_exists_nodup_walk hconn
  cases Q with
  | nil => cases hQ; exact hne rfl
  | cons x xs =>
    let proj (u : ℕ) : ℕ := if u = v' then v else u
    have hproj_walk : ∀ a b P, (F.applyUpdate (.split v v' St Sh)).IsWalk a b P →
        F.IsWalk (proj a) (proj b) P := by
      intro a b P hP
      induction hP with
      | nil u => exact .nil (proj u)
      | @cons a b y ys he' hs' _ ih =>
        have heF : y.1 ∈ F.E := he'
        have hte : F.tail y.1 ≠ v' := fun h => hv' (h ▸ (hF.1 y.1 heF).1)
        have hhe : F.head y.1 ≠ v' := fun h => hv' (h ▸ (hF.1 y.1 heF).2)
        have hps : proj ((F.applyUpdate (.split v v' St Sh)).src y) = F.src y := by
          obtain ⟨e, side⟩ := y
          cases side <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, MGraph.applyUpdate, proj]
          · by_cases h1 : e ∈ Sh ∧ F.head e = v <;> simp [h1, hhe]
          · by_cases h1 : e ∈ St ∧ F.tail e = v <;> simp [h1, hte]
        have hpd : proj ((F.applyUpdate (.split v v' St Sh)).dst y) = F.dst y := by
          obtain ⟨e, side⟩ := y
          cases side <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte, MGraph.applyUpdate, proj]
          · by_cases h1 : e ∈ St ∧ F.tail e = v <;> simp [h1, hte]
          · by_cases h1 : e ∈ Sh ∧ F.head e = v <;> simp [h1, hhe]
        exact .cons heF (by rw [← hs', hps]) (hpd ▸ ih)
    have hwalk_F := hproj_walk v v' (x :: xs) hQ
    simp only [proj, hne, ↓reduceIte] at hwalk_F
    exact hF.2 (x :: xs) ⟨List.cons_ne_nil _ _, hnd, v, hwalk_F⟩

/-! ## `TourValid` and other-component preservation under `moveEnds` -/

theorem tourValid_applyEdit_moveEnds {vCap eCap v v' : ℕ} {sel : Finset End} {c : Bool} {s : TourAbs}
    (hv : TourValid vCap eCap s)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c)) :
    TourValid vCap eCap (tourApplyEdit s (.moveEnds v v' sel c)) := by
  classical
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', _⟩
  set p := movedBy sel c
  set moved := ((s.ord v).filter p).toFinset
  set St := (moved.filter fun x => x.2).image Prod.fst
  set Sh := (moved.filter fun x => !x.2).image Prod.fst
  set F' := s.rf.F.applyUpdate (.split v v' St Sh)
  set r := s.rf.root v
  set newRoot := if F'.Connected v r then v' else v
  have hF' : F'.IsForest := isForest_applySplit hv.compat.forest hv'NotF St Sh
  have hr_spec := hv.root_spec hvF
  have hnc_vv' : ¬F'.Connected v v' := not_connected_v_v'_applySplit hv.compat.forest hne hv'NotF St Sh
  have hconn_v_or_v'_r : F'.Connected v r ∨ F'.Connected v' r :=
    connected_applySplit_v_or_v' hv.compat.forest St Sh hr_spec.2
  have hcompat' : OrdForestCompat (applyOrdEdit s.ord (.moveEnds v v' sel c)) F' := by
    refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hF', fun u hu => ?_, fun e heF => ?_⟩
    · simp only [applyOrdEdit]
      split_ifs
      · exact (hv.compat.nodup v).filter _
      · rw [hord_v', List.nil_append]; exact (hv.compat.nodup v).filter _
      · exact hv.compat.nodup u
    · have hmem : ∀ w z, z ∈ applyOrdEdit s.ord (.moveEnds v v' sel c) w →
          (w = v ∧ z ∈ s.ord v ∧ p z = false) ∨
          (w = v' ∧ z ∈ s.ord v ∧ p z = true) ∨
          (w ≠ v ∧ w ≠ v' ∧ z ∈ s.ord w) := by
        intro w z hz
        simp only [applyOrdEdit] at hz
        split_ifs at hz with h1 h2
        · subst h1; simp only [List.mem_filter, Bool.not_eq_true'] at hz; exact Or.inl ⟨rfl, hz.1, hz.2⟩
        · subst h2; rw [hord_v', List.nil_append, List.mem_filter] at hz; exact Or.inr (Or.inl ⟨rfl, hz.1, hz.2⟩)
        · exact Or.inr (Or.inr ⟨h1, h2, hz⟩)
      rcases hmem u₁ z h1 with ⟨hu1, hz1, hp1⟩ | ⟨hu1, hz1, hp1⟩ | ⟨hn1, _, hz1⟩
      · rcases hmem u₂ z h2 with ⟨hu2, _, _⟩ | ⟨_, _, hp2⟩ | ⟨hn2, _, hz2⟩
        · exact hu1.trans hu2.symm
        · rw [hp1] at hp2; exact absurd hp2 Bool.false_ne_true
        · exact absurd (hv.compat.unique u₂ v z hz2 hz1) hn2
      · rcases hmem u₂ z h2 with ⟨_, _, hp2⟩ | ⟨hu2, _, _⟩ | ⟨hn2, _, hz2⟩
        · rw [hp1] at hp2; exact absurd hp2.symm Bool.false_ne_true
        · exact hu1.trans hu2.symm
        · exact absurd (hv.compat.unique u₂ v z hz2 hz1) hn2
      · rcases hmem u₂ z h2 with ⟨_, hz2, _⟩ | ⟨_, hz2, _⟩ | ⟨_, _, hz2⟩
        · exact absurd (hv.compat.unique u₁ v z hz1 hz2) hn1
        · exact absurd (hv.compat.unique u₁ v z hz1 hz2) hn1
        · exact hv.compat.unique u₁ u₂ z hz1 hz2
    · simp only [applyOrdEdit] at hu
      split_ifs at hu with h1 h2
      · exact h1 ▸ Finset.mem_insert_of_mem hvF
      · exact h2 ▸ Finset.mem_insert_self v' s.rf.F.V
      · exact Finset.mem_insert_of_mem (hv.compat.vert u hu)
    · have heF0 : e ∈ s.rf.F.E := heF
      obtain ⟨ht, hh⟩ := hv.compat.forestEnd e heF0
      refine ⟨?_, ?_⟩
      · simp only [F', MGraph.applyUpdate, applyOrdEdit]
        by_cases htv : s.rf.F.tail e = v
        · rw [htv] at ht ⊢
          by_cases hp : p (e, true) = true
          · have heSt : e ∈ St := Finset.mem_image.mpr
              ⟨(e, true), Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_filter.mpr ⟨ht, hp⟩), rfl⟩, rfl⟩
            simp [heSt, hne.symm, hord_v', ht, hp, p]
          · have heSt : e ∉ St := fun hm => by
              obtain ⟨⟨f, b⟩, hfb, hfe⟩ := Finset.mem_image.mp hm
              have ⟨hfm, hbt⟩ := Finset.mem_filter.mp hfb
              have hfe' : f = e := hfe
              have hbt' : b = true := hbt
              subst hfe'; subst hbt'
              exact hp (List.mem_filter.mp (List.mem_toFinset.mp hfm)).2
            have hpf : p (e, true) = false := by cases h : p (e, true) <;> simp_all
            simp [heSt, ht, hpf, p]
        · have htv' : s.rf.F.tail e ≠ v' := fun h => hv'NotF (h ▸ (hv.compat.forest.1 e heF0).1)
          simp [htv, htv', ht]
      · simp only [F', MGraph.applyUpdate, applyOrdEdit]
        by_cases hhv : s.rf.F.head e = v
        · rw [hhv] at hh ⊢
          by_cases hp : p (e, false) = true
          · have heSh : e ∈ Sh := Finset.mem_image.mpr
              ⟨(e, false), Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hh, hp⟩), rfl⟩, rfl⟩
            simp [heSh, hne.symm, hord_v', hh, hp, p]
          · have heSh : e ∉ Sh := fun hm => by
              obtain ⟨⟨f, b⟩, hfb, hfe⟩ := Finset.mem_image.mp hm
              have ⟨hfm, hbf⟩ := Finset.mem_filter.mp hfb
              have hfe' : f = e := hfe
              have hbf' : b = false := by simpa using hbf
              subst hfe'; subst hbf'
              exact hp (List.mem_filter.mp (List.mem_toFinset.mp hfm)).2
            have hpf : p (e, false) = false := by cases h : p (e, false) <;> simp_all
            simp [heSh, hh, hpf, p]
        · have hhv' : s.rf.F.head e ≠ v' := fun h => hv'NotF (h ▸ (hv.compat.forest.1 e heF0).2)
          simp [hhv, hhv', hh]
  have hR_proj : ∀ r₁ r₂, r₁ ∈ s.rf.R → r₂ ∈ s.rf.R → F'.Connected r₁ r₂ → r₁ = r₂ := by
    intro r₁ r₂ hr₁ hr₂ hc'
    have h1n : r₁ ≠ v' := fun h => hv'NotF (h ▸ hv.roots_sub hr₁)
    have h2n : r₂ ≠ v' := fun h => hv'NotF (h ▸ hv.roots_sub hr₂)
    have hc := connected_applySplit_proj hv.compat.forest.1 hv'NotF St Sh hc'
    simp only [h1n, h2n, ↓reduceIte] at hc
    exact (hv.root_eq_of_mem (hv.roots_sub hr₁) hr₁ (connected_refl _ _)).symm.trans
      (hv.root_eq_of_mem (hv.roots_sub hr₁) hr₂ hc)
  have hnewRoot_nc : ∀ r' ∈ s.rf.R, ¬F'.Connected newRoot r' := by
    intro r' hr' hc'
    have hr'n : r' ≠ v' := fun h => hv'NotF (h ▸ hv.roots_sub hr')
    have hc_vr' : s.rf.F.Connected v r' := by
      have hp := connected_applySplit_proj hv.compat.forest.1 hv'NotF St Sh hc'
      have hnr_p : (if newRoot = v' then v else newRoot) = v := by
        by_cases hvr : F'.Connected v r <;> simp [newRoot, hvr]
      simpa [hnr_p, hr'n] using hp
    have hr'_eq : r' = r := (hv.root_eq_of_mem hvF hr' hc_vr').symm
    subst hr'_eq
    dsimp only [newRoot] at hc'
    split_ifs at hc' with hvr
    · exact hnc_vv' (connected_trans hvr (connected_symm hc'))
    · exact hvr hc'
  refine
    { ordWithin :=
        ⟨hcompat'.nodup,
         fun u hge => by
           have h1 : u ≠ v := by omega
           have h2 : u ≠ v' := by omega
           simpa [tourApplyEdit, applyOrdEdit, h1, h2] using hv.ordWithin.2.1 u hge,
         fun u z hz => by
           simp only [tourApplyEdit, applyOrdEdit] at hz
           split_ifs at hz
           · exact hv.ordWithin.2.2 v z (List.mem_filter.mp hz).1
           · rw [hord_v', List.nil_append] at hz; exact hv.ordWithin.2.2 v z (List.mem_filter.mp hz).1
           · exact hv.ordWithin.2.2 u z hz⟩
      compat := hcompat'
      roots_sub := by
        intro u hu
        simp only [tourApplyEdit] at hu
        rcases Finset.mem_insert.mp hu with rfl | huR
        · change (if F'.Connected v r then v' else v) ∈ insert v' s.rf.F.V
          split_ifs
          · exact Finset.mem_insert_self v' s.rf.F.V
          · exact Finset.mem_insert_of_mem hvF
        · exact Finset.mem_insert_of_mem (hv.roots_sub huR)
      verts_lt := fun u hu => by
        rcases Finset.mem_insert.mp hu with rfl | huF
        · exact hv'Lt
        · exact hv.verts_lt u huF
      unique_root := fun w hw => by
        have hex : ∃ r₀, r₀ ∈ insert newRoot s.rf.R ∧ F'.Connected w r₀ := by
          rcases Finset.mem_insert.mp hw with rfl | hwF
          · by_cases hvr : F'.Connected v r
            · exact ⟨newRoot, Finset.mem_insert_self _ _, by simp [newRoot, hvr, connected_refl]⟩
            · exact ⟨r, Finset.mem_insert_of_mem hr_spec.1, hconn_v_or_v'_r.resolve_left hvr⟩
          · by_cases hcvw : s.rf.F.Connected v w
            · rcases connected_applySplit_v_or_v' hv.compat.forest St Sh hcvw with hvw | hv'w
              · by_cases hvr : F'.Connected v r
                · exact ⟨r, Finset.mem_insert_of_mem hr_spec.1, connected_trans (connected_symm hvw) hvr⟩
                · exact ⟨newRoot, Finset.mem_insert_self _ _, by simp [newRoot, hvr]; exact connected_symm hvw⟩
              · by_cases hvr : F'.Connected v r
                · exact ⟨newRoot, Finset.mem_insert_self _ _, by simp [newRoot, hvr]; exact connected_symm hv'w⟩
                · exact ⟨r, Finset.mem_insert_of_mem hr_spec.1,
                    connected_trans (connected_symm hv'w) (hconn_v_or_v'_r.resolve_left hvr)⟩
            · have hrw := hv.root_spec hwF
              obtain ⟨P, hwalk, _⟩ := connected_exists_nodup_walk hrw.2
              have hnoV : ∀ x ∈ P, s.rf.F.src x ≠ v ∧ s.rf.F.dst x ≠ v := by
                intro x hx
                have hreach : ∀ a b Q, s.rf.F.IsWalk a b Q → x ∈ Q →
                    s.rf.F.Connected a (s.rf.F.src x) ∧ s.rf.F.Connected a (s.rf.F.dst x) := by
                  intro a b Q hQ hxQ
                  induction hQ with
                  | nil _ => simp at hxQ
                  | @cons a b z zs hze hzs _ ih =>
                    rcases List.mem_cons.mp hxQ with rfl | hxzs
                    · exact ⟨hzs ▸ connected_refl _ _, ⟨[x], .cons hze hzs (.nil _)⟩⟩
                    · have hst : s.rf.F.Connected a (s.rf.F.dst z) := ⟨[z], .cons hze hzs (.nil _)⟩
                      have ⟨h1, h2⟩ := ih hxzs
                      exact ⟨connected_trans hst h1, connected_trans hst h2⟩
                have ⟨h1, h2⟩ := hreach _ _ _ hwalk hx
                exact ⟨fun h => hcvw (connected_symm (h ▸ h1)), fun h => hcvw (connected_symm (h ▸ h2))⟩
              exact ⟨s.rf.root w, Finset.mem_insert_of_mem hrw.1,
                ⟨P, connected_applySplit_lift_avoiding St Sh P hwalk hnoV⟩⟩
        obtain ⟨r₀, hr₀R, hr₀c⟩ := hex
        refine ⟨r₀, ⟨hr₀R, hr₀c⟩, fun r₁ ⟨hr₁R, hr₁c⟩ => ?_⟩
        have hc01 : F'.Connected r₀ r₁ := connected_trans (connected_symm hr₀c) hr₁c
        rcases Finset.mem_insert.mp hr₀R with rfl | h0R <;>
          rcases Finset.mem_insert.mp hr₁R with rfl | h1R
        · rfl
        · exact absurd hc01 (hnewRoot_nc r₁ h1R)
        · exact absurd (connected_symm hc01) (hnewRoot_nc r₀ h0R)
        · exact (hR_proj r₀ r₁ h0R h1R hc01).symm
      marked_open := fun z hz => by
        obtain ⟨⟨u, hzu⟩, hzo⟩ := hv.marked_open z hz
        refine ⟨?_, hzo⟩
        by_cases huv : u = v
        · subst huv
          by_cases hp : p z = true
          · exact ⟨v', by simp [tourApplyEdit, applyOrdEdit, hne.symm, hord_v', hzu, hp, p]⟩
          · have hpf : p z = false := by cases h : p z <;> simp_all
            exact ⟨u, by simp [tourApplyEdit, applyOrdEdit, hzu, hpf, p]⟩
        · have huv' : u ≠ v' := fun h => by rw [h, hord_v'] at hzu; simp at hzu
          exact ⟨u, by simp [tourApplyEdit, applyOrdEdit, huv, huv', hzu]⟩ }

theorem fullTour_moveEnds_other {vCap eCap v v' r' : ℕ} {sel : Finset End} {c : Bool} {s : TourAbs}
    (hv : TourValid vCap eCap s)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hr' : r' ∈ s.rf.R) (hne_root : r' ≠ s.rf.root v) :
    let s' := tourApplyEdit s (.moveEnds v v' sel c)
    fullTour s'.ord s'.rf.F (tourValid_applyEdit_moveEnds hv he).compat.forest r' =
      fullTour s.ord s.rf.F hv.compat.forest r' := by
  classical
  intro s'
  have hvalid' := tourValid_applyEdit_moveEnds hv he
  rcases he with ⟨_, _, hne, hvF, hv'NotF, _, _⟩
  have hnc_rv : ¬s.rf.F.Connected r' v := fun hc =>
    hne_root (hv.root_eq_of_mem hvF hr' (connected_symm hc)).symm
  have hr'_ne_v : r' ≠ v := fun h => hnc_rv (h ▸ connected_refl _ _)
  have hr'_ne_v' : r' ≠ v' := fun h => hv'NotF (h ▸ hv.roots_sub hr')
  have hord'_r' : s'.ord r' = s.ord r' := by simp [s', tourApplyEdit, applyOrdEdit, hr'_ne_v, hr'_ne_v']
  by_cases hnil : s.ord r' = []
  · rw [(fullTour_eq_nil_iff hvalid'.compat r').mpr (by rw [hord'_r', hnil]),
        (fullTour_eq_nil_iff hv.compat r').mpr hnil]
  · obtain ⟨a, ha⟩ : ∃ a, (s.ord r').head? = some a :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord r' <;> simp_all)
    have ha' : (s'.ord r').head? = some a := by rw [hord'_r']; exact ha
    have ha1 : a ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest r' :=
      ((fullTour_spec hvalid'.compat r').2 a).mpr ⟨r', List.mem_of_head? ha', connected_refl _ r'⟩
    have ha2 : a ∈ fullTour s.ord s.rf.F hv.compat.forest r' :=
      ((fullTour_spec hv.compat r').2 a).mpr ⟨r', List.mem_of_head? ha, connected_refl _ r'⟩
    have hrot : (fullTour s'.ord s'.rf.F hvalid'.compat.forest r').IsRotated
        (fullTour s.ord s.rf.F hv.compat.forest r') :=
      isRotated_of_cycNext_eq (fullTour_spec hvalid'.compat r').1 (fullTour_spec hv.compat r').1 ha1 ha2
        (fun z hz => by
          obtain ⟨u, hzu', hcru'⟩ := ((fullTour_spec hvalid'.compat r').2 z).mp hz
          have hproj_c := connected_applySplit_proj hv.compat.forest.1 hv'NotF _ _ hcru'
          simp only [hr'_ne_v', ↓reduceIte] at hproj_c
          have huv : u ≠ v := fun h => hnc_rv (by simpa [h, hne] using hproj_c)
          have huv' : u ≠ v' := fun h => hnc_rv (by simpa [h] using hproj_c)
          have hzu : z ∈ s.ord u := by simpa [s', tourApplyEdit, applyOrdEdit, huv, huv'] using hzu'
          refine (fullTour_cycNext hvalid'.compat r' z hz).trans ?_
          by_cases hzF : z.1 ∈ s.rf.F.E
          · have hFE : s'.rf.F.E = s.rf.F.E := rfl
            have hstep : s'.rf.F.Connected r' (s'.rf.F.dst z) :=
              connected_trans hcru' ⟨[z], .cons (hFE ▸ hzF) ((hvalid'.compat.ordSrc_of_forest (hFE ▸ hzF)).symm.trans (hvalid'.compat.ordSrc_eq hzu')) (.nil _)⟩
            have hpd := connected_applySplit_proj hv.compat.forest.1 hv'NotF _ _ hstep
            simp only [hr'_ne_v', ↓reduceIte] at hpd
            have hdv : s'.rf.F.dst z ≠ v := fun h => hnc_rv (by simpa [h, hne] using hpd)
            have hdv' : s'.rf.F.dst z ≠ v' := fun h => hnc_rv (by simpa [h] using hpd)
            have hdst_eq : s'.rf.F.dst z = s.rf.F.dst z := by
              obtain ⟨f, side⟩ := z
              cases side
              · simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte, s', tourApplyEdit, MGraph.applyUpdate] at hdv' ⊢
                split_ifs at hdv' ⊢
                · exact absurd rfl hdv'
                · rfl
              · simp only [MGraph.dst, ↓reduceIte, s', tourApplyEdit, MGraph.applyUpdate] at hdv' ⊢
                split_ifs at hdv' ⊢
                · exact absurd rfl hdv'
                · rfl
            have h1 : eulerSucc s'.ord s'.rf.F z = cycNext (s'.ord (s'.rf.F.dst z)) z.flip := by
              unfold eulerSucc; exact ite_eq_left_iff.mpr fun h => absurd hzF h
            have h2 : eulerSucc s.ord s.rf.F z = cycNext (s.ord (s.rf.F.dst z)) z.flip := by
              unfold eulerSucc; exact ite_eq_left_iff.mpr fun h => absurd hzF h
            rw [h1, h2, hdst_eq]
            have hdv1 : s.rf.F.dst z ≠ v := hdst_eq ▸ hdv
            have hdv2 : s.rf.F.dst z ≠ v' := hdst_eq ▸ hdv'
            have hord_d : s'.ord (s.rf.F.dst z) = s.ord (s.rf.F.dst z) := by
              simp [s', tourApplyEdit, applyOrdEdit, hdv1, hdv2]
            rw [hord_d]
          · have h1 : eulerSucc s'.ord s'.rf.F z = cycNext (s'.ord (ordSrc s'.ord z)) z := by
              unfold eulerSucc; exact ite_eq_right_iff.mpr fun h => absurd h hzF
            have h2 : eulerSucc s.ord s.rf.F z = cycNext (s.ord (ordSrc s.ord z)) z := by
              unfold eulerSucc; exact ite_eq_right_iff.mpr fun h => absurd h hzF
            rw [h1, h2, hvalid'.compat.ordSrc_eq hzu', hv.compat.ordSrc_eq hzu]
            simp [s', tourApplyEdit, applyOrdEdit, huv, huv'])
        (fullTour_cycNext hv.compat r')
    exact (tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r').1 (List.IsRotated.refl _)
        (fullTour_head? hvalid'.compat r' ha')).symm.trans
      (tour_rotateToList_eq_of_isRotated (fullTour_spec hv.compat r').1 hrot (fullTour_head? hv.compat r' ha))

/-! ## `fullBlock` monotonicity and iterative block splitting -/

theorem fullBlock_head? {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v : ℕ} {x : End} (hx : x ∈ ord v) :
    let fullBlock (z : End) : List End :=
      if z.1 ∉ F.E then [z]
      else if _h : z.1 ∈ F.E ∧ F.src z = v then
        z :: fullTourBlocks ord F (eraseForestEdge F z.1) (isForest_eraseEdge hc.forest z.1)
          (F.dst z) (afterEnd z.flip (ord (F.dst z))) ++ [z.flip]
      else []
    (fullBlock x).head? = some x := by
  intro fullBlock
  dsimp only [fullBlock]
  by_cases hopen : x.1 ∉ F.E
  · simp [hopen]
  · have hxe : x.1 ∈ F.E := by push Not at hopen; exact hopen
    have hxv : F.src x = v := (hc.ordSrc_of_forest hxe).symm.trans (hc.ordSrc_eq hx)
    simp [hxe, hxv]

theorem idxOf_flatMap_head_lt {α : Type*} [DecidableEq α] {f : α → List α} {xs : List α}
    (hnd : (xs.flatMap f).Nodup) (hhd : ∀ a ∈ xs, (f a).head? = some a)
    {x y : α} (hx : x ∈ xs) (hy : y ∈ xs) (hlt : xs.idxOf x < xs.idxOf y) :
    (xs.flatMap f).idxOf x < (xs.flatMap f).idxOf y := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    have hsp := List.nodup_append.mp hnd
    have ha_hd : (f a).head? = some a := hhd a (by simp)
    have ha_mem : a ∈ f a := List.mem_of_head? ha_hd
    by_cases hxa : a = x
    · subst hxa
      have hya : a ≠ y := fun h => by subst h; simp at hlt
      have hy_as : y ∈ as := (List.mem_cons.mp hy).resolve_left hya.symm
      have hy_mem_as : y ∈ as.flatMap f :=
        List.mem_flatMap.mpr ⟨y, hy_as, List.mem_of_head? (hhd y (by simp [hy_as]))⟩
      have hy_nfa : y ∉ f a := fun hm => hsp.2.2 y hm y hy_mem_as rfl
      have hidx_x : (f a ++ as.flatMap f).idxOf a = (f a).idxOf a := List.idxOf_append_of_mem ha_mem
      have hidx_y : (f a ++ as.flatMap f).idxOf y = (f a).length + (as.flatMap f).idxOf y :=
        List.idxOf_append_of_notMem hy_nfa
      have hlt_a : (f a).idxOf a < (f a).length := List.idxOf_lt_length_iff.mpr ha_mem
      omega
    · have hya : a ≠ y := by
        intro h; subst h; simp [List.idxOf_cons_self] at hlt
      have hx_as : x ∈ as := (List.mem_cons.mp hx).resolve_left (Ne.symm hxa)
      have hy_as : y ∈ as := (List.mem_cons.mp hy).resolve_left (Ne.symm hya)
      have hx_mem_as : x ∈ as.flatMap f :=
        List.mem_flatMap.mpr ⟨x, hx_as, List.mem_of_head? (hhd x (by simp [hx_as]))⟩
      have hy_mem_as : y ∈ as.flatMap f :=
        List.mem_flatMap.mpr ⟨y, hy_as, List.mem_of_head? (hhd y (by simp [hy_as]))⟩
      have hx_nfa : x ∉ f a := fun hm => hsp.2.2 x hm x hx_mem_as rfl
      have hy_nfa : y ∉ f a := fun hm => hsp.2.2 y hm y hy_mem_as rfl
      rw [List.idxOf_append_of_notMem hx_nfa, List.idxOf_append_of_notMem hy_nfa]
      have hlt' : as.idxOf x < as.idxOf y := by
        simpa [List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hya] using hlt
      have := ih hsp.2.1 (fun z hz => hhd z (by simp [hz])) hx_as hy_as hlt'
      omega

/-- A `Nodup` list `A` of elements from `xs` whose `idxOf` in `xs.flatMap f` is pairwise nondecreasing
equals `xs.filter (· ∈ A)`. -/
theorem filter_eq_of_perm_sorted_idxOf {α : Type*} [DecidableEq α] {f : α → List α} {xs A : List α}
    (hnd_xs : xs.Nodup) (hnd_flat : (xs.flatMap f).Nodup)
    (hhd : ∀ a ∈ xs, (f a).head? = some a)
    (hnd_A : A.Nodup) (hsub : ∀ a ∈ A, a ∈ xs)
    (hsorted : A.Pairwise fun a b => (xs.flatMap f).idxOf a ≤ (xs.flatMap f).idxOf b) :
    A = xs.filter fun z => decide (z ∈ A) := by
  have hperm : A.Perm (xs.filter fun z => decide (z ∈ A)) := by
    refine (List.perm_ext_iff_of_nodup hnd_A (hnd_xs.filter _)).mpr fun z => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hz => ⟨hsub z hz, hz⟩, fun h => h.2⟩
  have hsorted_xs : (xs.filter fun z => decide (z ∈ A)).Pairwise fun a b => xs.idxOf a < xs.idxOf b := by
    have hpw : xs.Pairwise fun a b => xs.idxOf a < xs.idxOf b := by
      refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
      rw [hnd_xs.idxOf_getElem i hi, hnd_xs.idxOf_getElem j hj]; exact hij
    exact hpw.filter _
  have hsorted_A : A.Pairwise fun a b => xs.idxOf a < xs.idxOf b := by
    refine List.Pairwise.imp_of_mem ?_ (hnd_A.and hsorted)
    intro a b ha hb ⟨hne, hle⟩
    by_contra hge
    have hne_idx : xs.idxOf a ≠ xs.idxOf b := fun heq => by
      have ha_lt := List.idxOf_lt_length_iff.mpr (hsub a ha)
      have hb_lt := List.idxOf_lt_length_iff.mpr (hsub b hb)
      exact hne (by rw [← List.getElem_idxOf ha_lt, ← List.getElem_idxOf hb_lt]; simp [heq])
    have hlt_ba : xs.idxOf b < xs.idxOf a := by omega
    have := idxOf_flatMap_head_lt hnd_flat hhd (hsub b hb) (hsub a ha) hlt_ba
    omega
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd h1 (Nat.not_lt.mpr (Nat.le_of_lt h2)))
    hsorted_A hsorted_xs hperm

end MinCostFlow.SparseCore.Program
