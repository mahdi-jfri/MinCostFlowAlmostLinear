module

public import MinCostFlow.SparseCore.Program.TourMath
import MinCostFlow.Bundle.TourSplit

/-!
# Vertex-split (`moveEnds`) surgery for Euler tours

Proves `fullTour_moveEnds_blocks`: splitting `v` into `v` and fresh `v'` partitions `fullTour` at
`v` into the kept-end blocks and moved-end blocks.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

/-- Splitting a vertex `v` of a forest into `v` and a fresh vertex `v' ∉ F.V` preserves `IsForest`. -/
theorem isForest_applySplit {F : MGraph} (hF : F.IsForest) {v v' : ℕ}
    (hv' : v' ∉ F.V) (St Sh : Finset ℕ) :
    (F.applyUpdate (.split v v' St Sh)).IsForest := by
  set F' := F.applyUpdate (.split v v' St Sh)
  have hval : F'.IsValid := by
    intro e he
    have heF : e ∈ F.E := he
    have ⟨ht, hh⟩ := hF.1 e heF
    refine ⟨?_, ?_⟩
    · simp only [F', MGraph.applyUpdate]
      split_ifs
      · exact Finset.mem_insert_self v' F.V
      · exact Finset.mem_insert_of_mem ht
    · simp only [F', MGraph.applyUpdate]
      split_ifs
      · exact Finset.mem_insert_self v' F.V
      · exact Finset.mem_insert_of_mem hh
  refine ⟨hval, fun P ⟨hne, hnd, start, hwalk⟩ => ?_⟩
  let proj (u : ℕ) : ℕ := if u = v' then v else u
  have hproj_walk : ∀ a b Q, F'.IsWalk a b Q → F.IsWalk (proj a) (proj b) Q := by
    intro a b Q hQ
    induction hQ with
    | nil u => exact .nil (proj u)
    | @cons a b x xs he' hs' _ ih =>
      have heF : x.1 ∈ F.E := he'
      have hte : F.tail x.1 ≠ v' := fun h => hv' (h ▸ (hF.1 x.1 heF).1)
      have hhe : F.head x.1 ≠ v' := fun h => hv' (h ▸ (hF.1 x.1 heF).2)
      have hps : proj (F'.src x) = F.src x := by
        obtain ⟨e, side⟩ := x
        cases side <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, F', MGraph.applyUpdate, proj]
        · by_cases h1 : e ∈ Sh ∧ F.head e = v
          · simp [h1]
          · simp [h1, hhe]
        · by_cases h1 : e ∈ St ∧ F.tail e = v
          · simp [h1]
          · simp [h1, hte]
      have hpd : proj (F'.dst x) = F.dst x := by
        obtain ⟨e, side⟩ := x
        cases side <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte, F', MGraph.applyUpdate, proj]
        · by_cases h1 : e ∈ St ∧ F.tail e = v
          · simp [h1]
          · simp [h1, hte]
        · by_cases h1 : e ∈ Sh ∧ F.head e = v
          · simp [h1]
          · simp [h1, hhe]
      exact .cons heF (by rw [← hs', hps]) (hpd ▸ ih)
  exact hF.2 P ⟨hne, hnd, proj start, hproj_walk start start P hwalk⟩

private theorem fullTourBlocks_congr_split {ord ord' : ℕ → List End} {F F' : MGraph}
    {v v' : ℕ} (hFE : F'.E = F.E) (hord_other : ∀ u, u ≠ v → u ≠ v' → ord' u = ord u)
    (H₁ H₂ : MGraph) (hH₁ : H₁.IsForest) (hH₂ : H₂.IsForest) (w : ℕ) (xs : List End)
    (hEE : H₁.E = H₂.E)
    (hE1 : ∀ e ∈ H₁.E, (H₁.Connected w (H₁.tail e) ∨ H₁.Connected w (H₁.head e)) →
      H₁.tail e = H₂.tail e ∧ H₁.head e = H₂.head e)
    (hE2 : ∀ e ∈ H₂.E, (H₂.Connected w (H₂.tail e) ∨ H₂.Connected w (H₂.head e)) →
      H₁.tail e = H₂.tail e ∧ H₁.head e = H₂.head e)
    (hconn : ∀ u, H₁.Connected w u → u ≠ v ∧ u ≠ v')
    (hsrc_iff : ∀ x ∈ xs, x.1 ∈ H₁.E → (H₁.src x = w ↔ H₂.src x = w)) :
    fullTourBlocks ord F H₁ hH₁ w xs = fullTourBlocks ord' F' H₂ hH₂ w xs := by
  rw [fullTourBlocks.eq_def, fullTourBlocks.eq_def]
  apply List.flatMap_congr
  intro x hx
  by_cases hopen : x.1 ∉ F.E
  · simp [hopen, hFE]
  · simp only [hopen, hFE, ↓reduceIte]
    by_cases h1 : x.1 ∈ H₁.E ∧ H₁.src x = w
    · have hx2 : x.1 ∈ H₂.E := hEE ▸ h1.1
      have hsrc2 : H₂.src x = w := (hsrc_iff x hx h1.1).mp h1.2
      have hEnds_x : H₁.tail x.1 = H₂.tail x.1 ∧ H₁.head x.1 = H₂.head x.1 := by
        apply hE1 x.1 h1.1
        obtain ⟨e, b⟩ := x
        cases b
        · exact Or.inr (h1.2 ▸ connected_refl H₁ w)
        · exact Or.inl (h1.2 ▸ connected_refl H₁ w)
      have hdst_eq : H₂.dst x = H₁.dst x := by
        obtain ⟨e, b⟩ := x; cases b <;> simp [MGraph.dst, hEnds_x.1, hEnds_x.2]
      have hstep1 : H₁.Connected w (H₁.dst x) := ⟨[x], .cons h1.1 h1.2 (.nil _)⟩
      have hstep2 : H₂.Connected w (H₂.dst x) := ⟨[x], .cons hx2 hsrc2 (.nil _)⟩
      have hne_dst := hconn (H₁.dst x) hstep1
      have hord_dst : ord' (H₁.dst x) = ord (H₁.dst x) := hord_other _ hne_dst.1 hne_dst.2
      simp only [h1, hx2, hsrc2, hdst_eq, hord_dst, and_self, ↓reduceDIte]
      congr 2
      exact fullTourBlocks_congr_split hFE hord_other
        (eraseForestEdge H₁ x.1) (eraseForestEdge H₂ x.1)
        (isForest_eraseEdge hH₁ x.1) (isForest_eraseEdge hH₂ x.1)
        (H₁.dst x) (afterEnd x.flip (ord (H₁.dst x)))
        (by simp [hEE])
        (fun e he hc' => hE1 e (Finset.mem_erase.mp he).2
          (hc'.imp (fun h => connected_trans hstep1 (connected_of_subgraph (eraseForestEdge_subgraph H₁ x.1) h))
            (fun h => connected_trans hstep1 (connected_of_subgraph (eraseForestEdge_subgraph H₁ x.1) h))))
        (fun e he hc' => hE2 e (Finset.mem_erase.mp he).2
          (hc'.imp (fun h => connected_trans (show H₂.Connected w (H₁.dst x) from hdst_eq ▸ hstep2)
              (connected_of_subgraph (eraseForestEdge_subgraph H₂ x.1) h))
            (fun h => connected_trans (show H₂.Connected w (H₁.dst x) from hdst_eq ▸ hstep2)
              (connected_of_subgraph (eraseForestEdge_subgraph H₂ x.1) h))))
        (fun u hu => hconn u (connected_trans hstep1 (connected_of_subgraph (eraseForestEdge_subgraph H₁ x.1) hu)))
        (fun y _ hy1 => by
          have hyF := (Finset.mem_erase.mp hy1).2
          constructor
          · intro hsy
            have hh := hE1 y.1 hyF (by
              obtain ⟨e, b⟩ := y; cases b
              · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsy
                exact Or.inr (hsy ▸ hstep1)
              · simp only [MGraph.src, ↓reduceIte] at hsy
                exact Or.inl (hsy ▸ hstep1))
            obtain ⟨e, b⟩ := y; cases b <;> simpa [MGraph.src, hh.1, hh.2] using hsy
          · intro hsy
            have hh := hE2 y.1 (hEE ▸ hyF) (by
              have hstep2' : H₂.Connected w (H₁.dst x) := hdst_eq ▸ hstep2
              obtain ⟨e, b⟩ := y; cases b
              · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsy
                exact Or.inr (hsy ▸ hstep2')
              · simp only [MGraph.src, ↓reduceIte] at hsy
                exact Or.inl (hsy ▸ hstep2'))
            obtain ⟨e, b⟩ := y; cases b <;> simpa [MGraph.src, hh.1, hh.2] using hsy)
    · have h2 : ¬ (x.1 ∈ H₂.E ∧ H₂.src x = w) := by
        rintro ⟨hx2, hsrc2⟩
        have hx1 : x.1 ∈ H₁.E := hEE.symm ▸ hx2
        exact h1 ⟨hx1, (hsrc_iff x hx hx1).mpr hsrc2⟩
      simp [h1, h2]
termination_by (compOf H₁ w).card
decreasing_by
  rw [← h1.2]
  exact branch_card_lt hH₁ h1.1

/-- Vertex-split (`moveEnds`) surgery: splitting `v` into `v` and fresh `v'` partitions
`fullTour ord F v` into the kept-end blocks (`fullTour ord' F' v`) and moved-end blocks
(`fullTour ord' F' v'`). -/
theorem fullTour_moveEnds_blocks {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v v' : ℕ} {sel : Finset End} {c : Bool}
    (hne : v ≠ v') (hv : v ∈ F.V) (hv' : v' ∉ F.V) (hord_v' : ord v' = []) :
    let p := movedBy sel c
    let moved := ((ord v).filter p).toFinset
    let St := (moved.filter fun x => x.2).image Prod.fst
    let Sh := (moved.filter fun x => !x.2).image Prod.fst
    let F' := F.applyUpdate (.split v v' St Sh)
    let ord' := applyOrdEdit ord (.moveEnds v v' sel c)
    have hF' : F'.IsForest := isForest_applySplit hc.forest hv' St Sh
    have hc' : OrdForestCompat ord' F' := by
      refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hF', fun u hu => ?_, fun e he => ?_⟩
      · simp only [ord', applyOrdEdit]
        split_ifs with h1 h2
        · exact (hc.nodup v).filter _
        · rw [hord_v', List.nil_append]; exact (hc.nodup v).filter _
        · exact hc.nodup u
      · have hmem : ∀ w z, z ∈ ord' w →
            (w = v ∧ z ∈ ord v ∧ p z = false) ∨
            (w = v' ∧ z ∈ ord v ∧ p z = true) ∨
            (w ≠ v ∧ w ≠ v' ∧ z ∈ ord w) := by
          intro w z hz
          simp only [ord', applyOrdEdit] at hz
          split_ifs at hz with h1 h2
          · subst h1; simp only [List.mem_filter, Bool.not_eq_true'] at hz
            exact Or.inl ⟨rfl, hz.1, hz.2⟩
          · subst h2; rw [hord_v', List.nil_append, List.mem_filter] at hz
            exact Or.inr (Or.inl ⟨rfl, hz.1, hz.2⟩)
          · exact Or.inr (Or.inr ⟨h1, h2, hz⟩)
        rcases hmem u₁ z h1 with ⟨hu1, hz1, hp1⟩ | ⟨hu1, hz1, hp1⟩ | ⟨hn1, _, hz1⟩
        · rw [hu1]
          rcases hmem u₂ z h2 with ⟨hu2, _, _⟩ | ⟨_, _, hp2⟩ | ⟨hn2, _, hz2⟩
          · exact hu2.symm
          · rw [hp1] at hp2; exact absurd hp2 Bool.false_ne_true
          · exact absurd (hc.unique u₂ v z hz2 hz1) hn2
        · rw [hu1]
          rcases hmem u₂ z h2 with ⟨_, _, hp2⟩ | ⟨hu2, _, _⟩ | ⟨hn2, _, hz2⟩
          · rw [hp1] at hp2; exact absurd hp2.symm Bool.false_ne_true
          · exact hu2.symm
          · exact absurd (hc.unique u₂ v z hz2 hz1) hn2
        · rcases hmem u₂ z h2 with ⟨_, hz2, _⟩ | ⟨_, hz2, _⟩ | ⟨_, _, hz2⟩
          · exact absurd (hc.unique u₁ v z hz1 hz2) hn1
          · exact absurd (hc.unique u₁ v z hz1 hz2) hn1
          · exact hc.unique u₁ u₂ z hz1 hz2
      · simp only [ord', applyOrdEdit] at hu
        split_ifs at hu with h1 h2
        · exact h1 ▸ Finset.mem_insert_of_mem hv
        · exact h2 ▸ Finset.mem_insert_self v' F.V
        · exact Finset.mem_insert_of_mem (hc.vert u hu)
      · have heF : e ∈ F.E := he
        obtain ⟨ht, hh⟩ := hc.forestEnd e heF
        refine ⟨?_, ?_⟩
        · simp only [F', MGraph.applyUpdate, ord', applyOrdEdit]
          by_cases htv : F.tail e = v
          · rw [htv] at ht ⊢
            by_cases hp : p (e, true) = true
            · have heSt : e ∈ St := Finset.mem_image.mpr
                ⟨(e, true), Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
                  (List.mem_filter.mpr ⟨ht, hp⟩), rfl⟩, rfl⟩
              simp [heSt, hne.symm, hord_v', ht, hp, p]
            · have heSt : e ∉ St := by
                intro hm
                obtain ⟨⟨f, b⟩, hfb, hfe⟩ := Finset.mem_image.mp hm
                have ⟨hfm, hbt⟩ := Finset.mem_filter.mp hfb
                have hf_eq : f = e := hfe
                have hb_eq : b = true := hbt
                subst hf_eq; subst hb_eq
                exact hp (List.mem_filter.mp (List.mem_toFinset.mp hfm)).2
              have hpf : p (e, true) = false := by cases h : p (e, true) <;> simp_all
              simp [heSt, ht, hpf, p]
          · have htv' : F.tail e ≠ v' := fun h => hv' (h ▸ (hc.forest.1 e heF).1)
            simp [htv, htv', ht]
        · simp only [F', MGraph.applyUpdate, ord', applyOrdEdit]
          by_cases hhv : F.head e = v
          · rw [hhv] at hh ⊢
            by_cases hp : p (e, false) = true
            · have heSh : e ∈ Sh := Finset.mem_image.mpr
                ⟨(e, false), Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
                  (List.mem_filter.mpr ⟨hh, hp⟩), rfl⟩, rfl⟩
              simp [heSh, hne.symm, hord_v', hh, hp, p]
            · have heSh : e ∉ Sh := by
                intro hm
                obtain ⟨⟨f, b⟩, hfb, hfe⟩ := Finset.mem_image.mp hm
                have ⟨hfm, hbf⟩ := Finset.mem_filter.mp hfb
                have hf_eq : f = e := hfe
                have hb_eq : b = false := by simpa using hbf
                subst hf_eq; subst hb_eq
                exact hp (List.mem_filter.mp (List.mem_toFinset.mp hfm)).2
              have hpf : p (e, false) = false := by cases h : p (e, false) <;> simp_all
              simp [heSh, hh, hpf, p]
          · have hhv' : F.head e ≠ v' := fun h => hv' (h ▸ (hc.forest.1 e heF).2)
            simp [hhv, hhv', hh]
    let fullBlock (x : End) : List End :=
      if x.1 ∉ F.E then [x]
      else if _h : x.1 ∈ F.E ∧ F.src x = v then
        x :: fullTourBlocks ord F (eraseForestEdge F x.1) (isForest_eraseEdge hc.forest x.1)
          (F.dst x) (afterEnd x.flip (ord (F.dst x))) ++ [x.flip]
      else []
    fullTour ord F hc.forest v = (ord v).flatMap fullBlock ∧
    fullTour ord' F' hc'.forest v = ((ord v).filter fun x => !p x).flatMap fullBlock ∧
    fullTour ord' F' hc'.forest v' = ((ord v).filter p).flatMap fullBlock := by
  intro p moved St Sh F' ord' hF' hc' fullBlock
  have h0 : fullTour ord F hc.forest v = (ord v).flatMap fullBlock := by
    unfold fullTour; rw [fullTourBlocks.eq_def]
  have hord_other : ∀ u, u ≠ v → u ≠ v' → ord' u = ord u := fun u h1 h2 => by
    simp [ord', applyOrdEdit, h1, h2]
  have hbranch_at_v : ∀ (x : End), x ∈ ord v → x.1 ∈ F.E →
      fullTourBlocks ord' F' (eraseForestEdge F' x.1) (isForest_eraseEdge hF' x.1)
        (F.dst x) (afterEnd x.flip (ord (F.dst x))) =
      fullTourBlocks ord F (eraseForestEdge F x.1) (isForest_eraseEdge hc.forest x.1)
        (F.dst x) (afterEnd x.flip (ord (F.dst x))) := by
    intro x hx_ord hxe
    have hxv : F.src x = v := (hc.ordSrc_of_forest hxe).symm.trans (hc.ordSrc_eq hx_ord)
    have hdv_ne' : F.dst x ≠ v' := fun h => hv' (h ▸ (by
      obtain ⟨e, b⟩ := x; have hh := hc.forest.1 e hxe; cases b <;> simp [MGraph.dst, hh.1, hh.2]))
    have hno_v : ∀ u, (eraseForestEdge F x.1).Connected (F.dst x) u → u ≠ v ∧ u ≠ v' := by
      intro u hu
      refine ⟨fun heq => not_connected_eraseForestEdge hc.forest hxe (hxv ▸ connected_symm (heq ▸ hu)),
        fun heq => hv' (heq ▸ ?_)⟩
      have hF_u : F.Connected (F.dst x) u :=
        connected_of_subgraph (eraseForestEdge_subgraph F x.1) hu
      have hwalkV : ∀ a b Q, F.IsWalk a b Q → a ∈ F.V → b ∈ F.V := by
        intro a b Q hQ ha
        induction hQ with
        | nil _ => exact ha
        | @cons _ _ y _ he' _ _ ih =>
          apply ih
          obtain ⟨f, side⟩ := y; have hf := hc.forest.1 f he'
          cases side <;> simp [MGraph.dst, hf.1, hf.2]
      obtain ⟨Q, hQ⟩ := hF_u
      exact hwalkV _ _ Q hQ (by
        obtain ⟨e, b⟩ := x; have hh := hc.forest.1 e hxe; cases b <;> simp [MGraph.dst, hh.1, hh.2])
    have hproj_eq : ∀ e ∈ (eraseForestEdge F x.1).E,
        ((eraseForestEdge F x.1).Connected (F.dst x) (F.tail e) ∨
         (eraseForestEdge F x.1).Connected (F.dst x) (F.head e)) →
        F.tail e = F'.tail e ∧ F.head e = F'.head e := by
      intro e he hce
      have hstep_e : (eraseForestEdge F x.1).Connected (F.tail e) (F.head e) :=
        ⟨[(e, true)], .cons he rfl (.nil _)⟩
      have ht_ne : F.tail e ≠ v := (hno_v (F.tail e) (hce.elim id (fun h => connected_trans h (connected_symm hstep_e)))).1
      have hh_ne : F.head e ≠ v := (hno_v (F.head e) (hce.elim (fun h => connected_trans h hstep_e) id)).1
      simp [F', MGraph.applyUpdate, ht_ne, hh_ne]
    refine (fullTourBlocks_congr_split (F := F) (F' := F') rfl hord_other
      (eraseForestEdge F x.1) (eraseForestEdge F' x.1)
      (isForest_eraseEdge hc.forest x.1) (isForest_eraseEdge hF' x.1)
      (F.dst x) (afterEnd x.flip (ord (F.dst x))) rfl hproj_eq ?_ hno_v ?_).symm
    · intro e he hce
      have heF : e ∈ F.E := (Finset.mem_erase.mp he).2
      have hproj_c : ∀ a b, (eraseForestEdge F' x.1).Connected a b →
          (eraseForestEdge F x.1).Connected (if a = v' then v else a) (if b = v' then v else b) :=
        fun _ _ hab => connected_applySplit_proj (isForest_eraseEdge hc.forest x.1).1 hv' St Sh hab
      have hpc := hce.imp (hproj_c _ _) (hproj_c _ _)
      simp only [hdv_ne', ↓reduceIte] at hpc
      have hte_p : (if F'.tail e = v' then v else F'.tail e) = F.tail e := by
        have htne : F.tail e ≠ v' := fun h => hv' (h ▸ (hc.forest.1 e heF).1)
        by_cases h : e ∈ St ∧ F.tail e = v <;> simp [F', MGraph.applyUpdate, h, htne]
      have hhe_p : (if F'.head e = v' then v else F'.head e) = F.head e := by
        have hhne : F.head e ≠ v' := fun h => hv' (h ▸ (hc.forest.1 e heF).2)
        by_cases h : e ∈ Sh ∧ F.head e = v <;> simp [F', MGraph.applyUpdate, h, hhne]
      rw [hte_p, hhe_p] at hpc
      exact hproj_eq e he hpc
    · intro y _ hy
      constructor
      · intro hsy
        have hh := hproj_eq y.1 hy (by
          obtain ⟨e, b⟩ := y; cases b
          · exact Or.inr (hsy ▸ connected_refl _ _)
          · exact Or.inl (hsy ▸ connected_refl _ _))
        obtain ⟨e, b⟩ := y; cases b <;> simpa [MGraph.src, hh.1, hh.2] using hsy
      · intro hsy
        have hsy_ne : F'.src y ≠ v' := hsy ▸ hdv_ne'
        obtain ⟨e, b⟩ := y
        cases b
        · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, F', MGraph.applyUpdate] at hsy hsy_ne ⊢
          split_ifs at hsy hsy_ne with h
          · exact absurd rfl hsy_ne
          · exact hsy
        · simp only [MGraph.src, ↓reduceIte, F', MGraph.applyUpdate] at hsy hsy_ne ⊢
          split_ifs at hsy hsy_ne with h
          · exact absurd rfl hsy_ne
          · exact hsy
  have hdst_and_ord : ∀ (x : End), x ∈ ord v → x.1 ∈ F.E →
      F'.dst x = F.dst x ∧ ord' (F.dst x) = ord (F.dst x) := by
    intro x hx_ord hxe
    have hxv : F.src x = v := (hc.ordSrc_of_forest hxe).symm.trans (hc.ordSrc_eq hx_ord)
    have hdv_ne : F.dst x ≠ v := fun h => isForest_no_selfLoop hc.forest hxe (by
      obtain ⟨e, b⟩ := x; cases b <;> simp [MGraph.src, MGraph.dst] at hxv h ⊢ <;> omega)
    have hdv_ne' : F.dst x ≠ v' := fun h => hv' (h ▸ (by
      obtain ⟨e, b⟩ := x; have hh := hc.forest.1 e hxe; cases b <;> simp [MGraph.dst, hh.1, hh.2]))
    refine ⟨?_, hord_other _ hdv_ne hdv_ne'⟩
    obtain ⟨e, b⟩ := x
    cases b <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hdv_ne ⊢ <;>
      simp [F', MGraph.applyUpdate, hdv_ne]
  have hord'_v : ord' v = (ord v).filter fun x => !p x := by
    simp [ord', applyOrdEdit, p]
  have hord'_v' : ord' v' = (ord v).filter p := by
    simp [ord', applyOrdEdit, hne.symm, hord_v', p]
  refine ⟨h0, ?_, ?_⟩
  · unfold fullTour; rw [fullTourBlocks.eq_def, hord'_v]
    apply List.flatMap_congr; intro x hx
    have ⟨hx_ord, hxp⟩ := List.mem_filter.mp hx
    have hFE : F'.E = F.E := rfl
    by_cases hopen : x.1 ∉ F.E
    · simp [fullBlock, hopen, hFE]
    · have hxe : x.1 ∈ F.E := by push Not at hopen; exact hopen
      have hxv : F.src x = v := (hc.ordSrc_of_forest hxe).symm.trans (hc.ordSrc_eq hx_ord)
      have hxv' : F'.src x = v :=
        (hc'.ordSrc_of_forest hxe).symm.trans (hc'.ordSrc_eq (by rw [hord'_v]; exact hx))
      obtain ⟨hdst, hordd⟩ := hdst_and_ord x hx_ord hxe
      have hopen' : ¬ x.1 ∉ F'.E := hFE ▸ hopen
      dsimp only [fullBlock]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hopen'),
        ite_eq_right_iff.mpr (fun h => absurd h hopen),
        dite_eq_left_iff.mpr (fun h => absurd ⟨hFE ▸ hxe, hxv'⟩ h),
        dite_eq_left_iff.mpr (fun h => absurd ⟨hxe, hxv⟩ h)]
      rw [hdst, hordd, hbranch_at_v x hx_ord hxe]
  · unfold fullTour; rw [fullTourBlocks.eq_def, hord'_v']
    apply List.flatMap_congr; intro x hx
    have ⟨hx_ord, hxp⟩ := List.mem_filter.mp hx
    have hFE : F'.E = F.E := rfl
    by_cases hopen : x.1 ∉ F.E
    · simp [fullBlock, hopen, hFE]
    · have hxe : x.1 ∈ F.E := by push Not at hopen; exact hopen
      have hxv : F.src x = v := (hc.ordSrc_of_forest hxe).symm.trans (hc.ordSrc_eq hx_ord)
      have hxv' : F'.src x = v' :=
        (hc'.ordSrc_of_forest hxe).symm.trans (hc'.ordSrc_eq (by rw [hord'_v']; exact hx))
      obtain ⟨hdst, hordd⟩ := hdst_and_ord x hx_ord hxe
      have hopen' : ¬ x.1 ∉ F'.E := hFE ▸ hopen
      dsimp only [fullBlock]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hopen'),
        ite_eq_right_iff.mpr (fun h => absurd h hopen),
        dite_eq_left_iff.mpr (fun h => absurd ⟨hFE ▸ hxe, hxv'⟩ h),
        dite_eq_left_iff.mpr (fun h => absurd ⟨hxe, hxv⟩ h)]
      rw [hdst, hordd, hbranch_at_v x hx_ord hxe]

end MinCostFlow.SparseCore.Program
