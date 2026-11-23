module

public import MinCostFlow.SparseCore.Program.TourMath

/-!
# Forest cut and link surgery for Euler tours

Proves `isForest_addForestEdge`, `fullTour_cut` (cutting a forest edge splits one Euler tour cycle
at its two ends), and `fullTour_link` (linking an open edge between distinct components splices
two Euler tour cycles together).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

theorem isForest_addForestEdge {F : MGraph} (hF : F.IsForest) {e u v : ℕ}
    (he : e ∉ F.E) (hu : u ∈ F.V) (hv : v ∈ F.V) (hnc : ¬ F.Connected u v) :
    (addForestEdge F e u v).IsForest := by
  refine ⟨?_, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hfF
    · simp [addForestEdge, hu, hv]
    · have hne : f ≠ e := fun h => he (h ▸ hfF)
      simpa [addForestEdge, Function.update_of_ne hne] using hF.1 f hfF
  · intro P ⟨hne, hnd, start, hwalk⟩
    have hsub_back : ∀ (a b : ℕ) (Q : List End),
        (addForestEdge F e u v).IsWalk a b Q → e ∉ Q.map Prod.fst → F.IsWalk a b Q := by
      intro a b Q hQ hneQ
      induction hQ with
      | nil w => exact .nil w
      | @cons a b z rest hzE hzS _ ih =>
        have hze : z.1 ≠ e := fun h => hneQ (List.mem_map.mpr ⟨z, List.mem_cons_self, h⟩)
        have hzF : z.1 ∈ F.E := (Finset.mem_insert.mp hzE).resolve_left hze
        have hsr : F.src z = a := by
          obtain ⟨f, side⟩ := z
          cases side <;> simpa [MGraph.src, addForestEdge, Function.update_of_ne hze] using hzS
        have hds : F.dst z = (addForestEdge F e u v).dst z := by
          obtain ⟨f, side⟩ := z
          cases side <;> simp [MGraph.dst, addForestEdge, Function.update_of_ne hze]
        exact .cons hzF hsr (hds ▸ ih fun hm => hneQ (List.mem_cons_of_mem _ hm))
    by_cases heP : e ∈ P.map Prod.fst
    · obtain ⟨x, hxP, hxe⟩ := List.mem_map.mp heP
      obtain ⟨P₁, P₂, rfl⟩ := List.mem_iff_append.mp hxP
      have hnd_e : e ∉ (P₁ ++ P₂).map Prod.fst := by
        rw [List.map_append, List.map_cons, hxe] at hnd
        have := List.nodup_append.mp hnd
        intro hm
        rw [List.map_append, List.mem_append] at hm
        rcases hm with h1 | h2
        · exact this.2.2 e h1 e List.mem_cons_self rfl
        · exact (List.nodup_cons.mp this.2.1).1 h2
      have hne1 : e ∉ P₁.map Prod.fst := fun h => hnd_e (by simp [h])
      have hne2 : e ∉ P₂.map Prod.fst := fun h => hnd_e (by simp [h])
      have hsplit : ∀ (a c : ℕ) (Q₁ Q₂ : List End),
          (addForestEdge F e u v).IsWalk a c (Q₁ ++ x :: Q₂) →
          (addForestEdge F e u v).IsWalk a ((addForestEdge F e u v).src x) Q₁ ∧
          (addForestEdge F e u v).IsWalk ((addForestEdge F e u v).dst x) c Q₂ := by
        intro a c Q₁ Q₂ hQ
        induction Q₁ generalizing a with
        | nil =>
          cases hQ with
          | cons _ hs hr => exact ⟨hs ▸ .nil _, hr⟩
        | cons y ys ih =>
          cases hQ with
          | cons he' hs' hr' =>
            obtain ⟨h1, h2⟩ := ih _ hr'
            exact ⟨.cons he' hs' h1, h2⟩
      obtain ⟨hw1, hw2⟩ := hsplit start start P₁ P₂ hwalk
      have hF1 : F.Connected start ((addForestEdge F e u v).src x) := ⟨P₁, hsub_back _ _ P₁ hw1 hne1⟩
      have hF2 : F.Connected ((addForestEdge F e u v).dst x) start := ⟨P₂, hsub_back _ _ P₂ hw2 hne2⟩
      have hconn_ends : F.Connected ((addForestEdge F e u v).dst x) ((addForestEdge F e u v).src x) :=
        connected_trans hF2 hF1
      obtain ⟨f, side⟩ := x
      change f = e at hxe; subst f
      cases side
      · simp only [MGraph.dst, MGraph.src, Bool.false_eq_true, ↓reduceIte, addForestEdge,
          Function.update_self] at hconn_ends
        exact hnc hconn_ends
      · simp only [MGraph.dst, MGraph.src, ↓reduceIte, addForestEdge,
          Function.update_self] at hconn_ends
        exact hnc (connected_symm hconn_ends)
    · exact hF.2 P ⟨hne, hnd, start, hsub_back _ _ P hwalk heP⟩

private theorem getLast?_append_singleton (xs : List End) (y : End) :
    (xs ++ [y]).getLast? = some y := by
  rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; rfl

private theorem cycNext_append_eq {xs ys : List End} (hnd : (xs ++ ys).Nodup) {a b : End}
    (ha : xs.getLast? = some a) (hb : ys.head? = some b) :
    cycNext (xs ++ ys) a = b := by
  have hc : IsCycleOf (cycNext (xs ++ ys)) (xs ++ ys) :=
    (isCycleOf_iff_cycNext hnd).mpr fun _ _ => rfl
  exact isSuccChain_link_of_append hc.1 ha hb

private theorem isCycleOf_of_split_cut {f : End → End} {P A Q : List End} {x y : End}
    (hnd : (P ++ x :: A ++ y :: Q).Nodup)
    (hcyc : IsCycleOf f (P ++ x :: A ++ y :: Q)) :
    let f' := Function.update (Function.update f x (f y)) y (f x)
    (P ++ x :: Q).Nodup ∧ IsCycleOf f' (P ++ x :: Q) ∧
    (A ++ [y]).Nodup ∧ IsCycleOf f' (A ++ [y]) := by
  have hnd' : (P ++ x :: (A ++ y :: Q)).Nodup := by simpa [List.append_assoc] using hnd
  have h1 := List.nodup_append.mp hnd'
  have h2 := List.nodup_cons.mp h1.2.1
  have h3 := List.nodup_append.mp h2.2
  have h4 := List.nodup_cons.mp h3.2.1
  have hxy : x ≠ y := fun h => h2.1 (by simp [h])
  have hxA : x ∉ A := fun h => h2.1 (by simp [h])
  have hxQ : x ∉ Q := fun h => h2.1 (by simp [h])
  have hyA : y ∉ A := fun h => h3.2.2 y h y List.mem_cons_self rfl
  have hyP : y ∉ P := fun h => h1.2.2 y h y (by simp) rfl
  have hxP : x ∉ P := fun h => h1.2.2 x h x List.mem_cons_self rfl
  have hnd1 : (P ++ x :: Q).Nodup := by
    refine List.nodup_append.mpr ⟨h1.1, List.nodup_cons.mpr ⟨hxQ, h4.2⟩, fun a ha b hb h => ?_⟩
    subst h
    rcases List.mem_cons.mp hb with rfl | hbQ
    · exact hxP ha
    · exact h1.2.2 a ha a (by simp [hbQ]) rfl
  have hnd2 : (A ++ [y]).Nodup := by
    refine List.nodup_append.mpr ⟨h3.1, List.nodup_singleton y, fun a ha b hb h => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; subst h; exact hyA ha
  have hch_full : IsSuccChain f ((P ++ [x]) ++ (A ++ [y]) ++ Q) := by
    simpa [List.append_assoc] using hcyc.1
  have hch_PA := isSuccChain_of_append_left hch_full
  have hch_Q := isSuccChain_of_append_right hch_full
  have hch_Px := isSuccChain_of_append_left hch_PA
  have hch_Ay := isSuccChain_of_append_right hch_PA
  have hch_P : IsSuccChain f P := isSuccChain_of_append_left (by simpa using hch_Px)
  have hch_A : IsSuccChain f A := isSuccChain_of_append_left (by simpa using hch_Ay)
  have hcongr : ∀ (L : List End), x ∉ L → y ∉ L → IsSuccChain f L →
      IsSuccChain (Function.update (Function.update f x (f y)) y (f x)) L := by
    intro L hxL hyL hL
    induction L with
    | nil => trivial
    | cons u rest ih =>
      cases rest with
      | nil => trivial
      | cons w ws =>
        have hux : u ≠ x := fun h => hxL (h ▸ List.mem_cons_self)
        have huy : u ≠ y := fun h => hyL (h ▸ List.mem_cons_self)
        refine ⟨by simp [Function.update_of_ne huy, Function.update_of_ne hux, hL.1],
          ih (fun h => hxL (List.mem_cons_of_mem _ h)) (fun h => hyL (List.mem_cons_of_mem _ h)) hL.2⟩
  have hch1 : IsSuccChain (Function.update (Function.update f x (f y)) y (f x)) (P ++ x :: Q) := by
    have h1P := hcongr P hxP hyP hch_P
    have h1Q := hcongr Q hxQ h4.1 hch_Q
    have h1xQ : IsSuccChain (Function.update (Function.update f x (f y)) y (f x)) (x :: Q) := by
      cases Q with
      | nil => trivial
      | cons q qs =>
        refine ⟨?_, h1Q⟩
        simp only [Function.update_of_ne hxy, Function.update_self]
        exact isSuccChain_link_of_append hch_full
          (by rw [List.getLast?_append_of_ne_nil _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
            List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; rfl) rfl
    refine isSuccChain_append h1P h1xQ fun a b ha hb => ?_
    have hbx : b = x := (Option.some.inj hb).symm; rw [hbx]
    have haP : a ∈ P := List.mem_of_getLast? ha
    have hax : a ≠ x := fun h => hxP (h ▸ haP)
    have hay : a ≠ y := fun h => hyP (h ▸ haP)
    simp only [Function.update_of_ne hay, Function.update_of_ne hax]
    exact isSuccChain_link_of_append hch_Px ha rfl
  have hcyc1 : IsCycleOf (Function.update (Function.update f x (f y)) y (f x)) (P ++ x :: Q) := by
    refine ⟨hch1, fun a b ha hb => ?_⟩
    cases Q with
    | nil =>
      have hbx : b = x := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hb
        exact (Option.some.inj hb).symm
      rw [hbx]
      simp only [Function.update_of_ne hxy, Function.update_self]
      cases P with
      | nil =>
        have hax : a = x := (Option.some.inj ha).symm; rw [hax]
        exact hcyc.2 x y rfl (by simpa [List.append_assoc] using getLast?_append_singleton (x :: A) y)
      | cons p ps =>
        have hap : a = p := (Option.some.inj ha).symm; rw [hap]
        exact hcyc.2 p y rfl (by simpa [List.append_assoc] using getLast?_append_singleton (p :: ps ++ x :: A) y)
    | cons q qs =>
      have hb_eq : (q :: qs).getLast? = some b := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] at hb
        exact hb
      have hbQ : b ∈ q :: qs := List.mem_of_getLast? hb_eq
      have hbx : b ≠ x := fun h => hxQ (h ▸ hbQ)
      have hby : b ≠ y := fun h => h4.1 (h ▸ hbQ)
      simp only [Function.update_of_ne hby, Function.update_of_ne hbx]
      have hhead_full : (P ++ x :: A ++ y :: q :: qs).head? = some a := by
        cases P <;> simpa using ha
      have hlast_full : (P ++ x :: A ++ y :: q :: qs).getLast? = some b := by
        have hre : P ++ x :: A ++ y :: q :: qs = (P ++ x :: A) ++ (y :: q :: qs) := by
          simp [List.append_assoc]
        rw [hre, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)]
        exact hb_eq
      exact hcyc.2 a b hhead_full hlast_full
  have hch2 : IsSuccChain (Function.update (Function.update f x (f y)) y (f x)) (A ++ [y]) := by
    refine isSuccChain_append (hcongr A hxA hyA hch_A) trivial fun a b ha hb => ?_
    have hby : b = y := (Option.some.inj hb).symm; rw [hby]
    have haA : a ∈ A := List.mem_of_getLast? ha
    have hax : a ≠ x := fun h => hxA (h ▸ haA)
    have hay : a ≠ y := fun h => hyA (h ▸ haA)
    simp only [Function.update_of_ne hay, Function.update_of_ne hax]
    exact isSuccChain_link_of_append hch_Ay ha rfl
  have hcyc2 : IsCycleOf (Function.update (Function.update f x (f y)) y (f x)) (A ++ [y]) := by
    refine ⟨hch2, fun a b ha hb => ?_⟩
    have hby : b = y := by
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hb
      exact (Option.some.inj hb).symm
    rw [hby]
    simp only [Function.update_self]
    exact isSuccChain_link_of_append hch_PA
      (by rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; rfl) ha
  exact ⟨hnd1, hcyc1, hnd2, hcyc2⟩

/-- Forest cut surgery: cutting forest edge `e` splits the Euler tour cycle at its two ends
`x` and `y` into the two new component tours. -/
theorem fullTour_cut {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {e r : ℕ} (he : e ∈ F.E) {P A Q : List End} {x y : End}
    (hxy : (x = (e, true) ∧ y = (e, false)) ∨ (x = (e, false) ∧ y = (e, true)))
    (hrot : (P ++ x :: A ++ y :: Q).IsRotated (fullTour ord F hc.forest r)) :
    let F' := eraseForestEdge F e
    have hc' : OrdForestCompat ord F' :=
      ⟨hc.nodup, hc.unique, isForest_eraseEdge hc.forest e, hc.vert,
        fun f hf => hc.forestEnd f (Finset.mem_erase.mp hf).2⟩
    (P ++ x :: Q).IsRotated (fullTour ord F' hc'.forest (F.src x)) ∧
    (A ++ [y]).IsRotated (fullTour ord F' hc'.forest (F.src y)) := by
  intro F' hc'
  have hnd : (P ++ x :: A ++ y :: Q).Nodup := hrot.perm.nodup_iff.mpr (fullTour_spec hc r).1
  have hcyc : IsCycleOf (eulerSucc ord F) (P ++ x :: A ++ y :: Q) :=
    (isCycleOf_iff_cycNext hnd).mpr fun z hz => by
      have hzr := hrot.perm.mem_iff.mp hz
      rw [cycNext_isRotated (fullTour_spec hc r).1 hrot.symm hzr, fullTour_cycNext hc r z hzr]
  obtain ⟨hnd1, hcyc1, hnd2, hcyc2⟩ := isCycleOf_of_split_cut hnd hcyc
  have hy_eq_xflip : y = x.flip := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hx_eq_yflip : x = y.flip := by rw [hy_eq_xflip, flip_flip]
  have hxe : x.1 = e := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have hye : y.1 = e := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have hf'_eq : ∀ z, Function.update (Function.update (eulerSucc ord F) x (eulerSucc ord F y))
      y (eulerSucc ord F x) z = eulerSucc ord F' z := by
    intro z
    by_cases hzy : z = y
    · subst z
      simp only [Function.update_self, eulerSucc, hxe, hye, he, ↓reduceIte,
        show ¬ e ∈ F'.E from fun h => (Finset.mem_erase.mp h).1 rfl]
      rw [hy_eq_xflip, hc.ordSrc_of_forest (show x.flip.1 ∈ F.E from hxe ▸ he), src_flip_eq]
    · by_cases hzx : z = x
      · subst z
        simp only [Function.update_of_ne hzy, Function.update_self, eulerSucc, hxe, hye, he,
          ↓reduceIte, show ¬ e ∈ F'.E from fun h => (Finset.mem_erase.mp h).1 rfl]
        rw [hx_eq_yflip, hc.ordSrc_of_forest (show y.flip.1 ∈ F.E from hye ▸ he), src_flip_eq]
      · simp only [Function.update_of_ne hzy, Function.update_of_ne hzx]
        have hze : z.1 ≠ e := by
          intro h
          have hcase : z = (e, true) ∨ z = (e, false) := by
            obtain ⟨f, b⟩ := z; change f = e at h; subst f; cases b <;> simp
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hcase with rfl | rfl <;>
            first | exact hzx rfl | exact hzy rfl
        simp only [eulerSucc, F', eraseForestEdge, Finset.mem_erase, hze, ne_eq, not_false_eq_true,
          true_and]
        rfl
  have hx_in : x ∈ fullTour ord F' hc'.forest (F.src x) :=
    ((fullTour_spec hc' (F.src x)).2 x).mpr
      ⟨F.src x, hc.mem_ord_of_forest (hxe ▸ he), connected_refl F' _⟩
  have hy_in : y ∈ fullTour ord F' hc'.forest (F.src y) :=
    ((fullTour_spec hc' (F.src y)).2 y).mpr
      ⟨F.src y, hc.mem_ord_of_forest (hye ▸ he), connected_refl F' _⟩
  refine ⟨isRotated_of_cycNext_eq hnd1 (fullTour_spec hc' _).1 (by simp) hx_in
      (fun z hz => ((isCycleOf_iff_cycNext hnd1).mp hcyc1 z hz).trans (hf'_eq z))
      (fullTour_cycNext hc' _),
    isRotated_of_cycNext_eq hnd2 (fullTour_spec hc' _).1 (by simp) hy_in
      (fun z hz => ((isCycleOf_iff_cycNext hnd2).mp hcyc2 z hz).trans (hf'_eq z))
      (fullTour_cycNext hc' _)⟩

/-- Forest link surgery: linking open edge `e` (whose endpoints `u, v` lie in distinct forest
components) splices the two Euler tour cycles at `(e, true)` and `(e, false)`. -/
theorem fullTour_link {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {e u v : ℕ} (he : e ∉ F.E) (hxu : (e, true) ∈ ord u) (hyv : (e, false) ∈ ord v)
    (hnc : ¬ F.Connected u v)
    {Px Qx Py Qy : List End}
    (hrx : (Px ++ (e, true) :: Qx).IsRotated (fullTour ord F hc.forest u))
    (hry : (Py ++ (e, false) :: Qy).IsRotated (fullTour ord F hc.forest v)) :
    let F' := addForestEdge F e u v
    have hc' : OrdForestCompat ord F' :=
      ⟨hc.nodup, hc.unique,
        isForest_addForestEdge hc.forest he (hc.vert u (List.ne_nil_of_mem hxu))
          (hc.vert v (List.ne_nil_of_mem hyv)) hnc,
        hc.vert, fun f hf => by
          rcases Finset.mem_insert.mp hf with rfl | hfF
          · simpa [F', addForestEdge] using ⟨hxu, hyv⟩
          · have hne : f ≠ e := fun h => he (h ▸ hfF)
            simpa [F', addForestEdge, Function.update_of_ne hne] using hc.forestEnd f hfF⟩
    (Px ++ (e, true) :: Qy ++ Py ++ (e, false) :: Qx).IsRotated
      (fullTour ord F' hc'.forest u) := by
  intro F' hc'
  set x : End := (e, true)
  set y : End := (e, false)
  have hndx : (Px ++ x :: Qx).Nodup := hrx.perm.nodup_iff.mpr (fullTour_spec hc u).1
  have hndy : (Py ++ y :: Qy).Nodup := hry.perm.nodup_iff.mpr (fullTour_spec hc v).1
  have hdisj : List.Disjoint (Px ++ x :: Qx) (Py ++ y :: Qy) := by
    intro z hzx hzy
    obtain ⟨w₁, hzw₁, huw₁⟩ := ((fullTour_spec hc u).2 z).mp (hrx.perm.mem_iff.mp hzx)
    obtain ⟨w₂, hzw₂, hvw₂⟩ := ((fullTour_spec hc v).2 z).mp (hry.perm.mem_iff.mp hzy)
    have hww : w₁ = w₂ := hc.unique w₁ w₂ z hzw₁ hzw₂
    subst hww
    exact hnc (connected_trans huw₁ (connected_symm hvw₂))
  have hnd_all : (Px ++ x :: Qy ++ Py ++ y :: Qx).Nodup := by
    have hperm : (Px ++ x :: Qy ++ Py ++ y :: Qx).Perm ((Px ++ x :: Qx) ++ (Py ++ y :: Qy)) := by
      simp only [List.append_assoc, List.cons_append]
      refine List.Perm.append_left Px (List.Perm.cons x ?_)
      have h1 : (Qy ++ (Py ++ y :: Qx)).Perm (Qx ++ (Qy ++ Py ++ [y])) := by
        have : Qy ++ (Py ++ y :: Qx) = (Qy ++ Py ++ [y]) ++ Qx := by simp [List.append_assoc]
        rw [this]; exact List.perm_append_comm
      refine h1.trans (List.Perm.append_left Qx ?_)
      have : Qy ++ Py ++ [y] = Qy ++ (Py ++ [y]) := by simp [List.append_assoc]
      rw [this]
      exact List.perm_append_comm.trans (by simp [List.append_assoc])
    exact hperm.nodup_iff.mpr (List.nodup_append.mpr ⟨hndx, hndy, fun a ha b hb h => hdisj ha (h ▸ hb)⟩)
  have hcx : IsCycleOf (eulerSucc ord F) (Px ++ x :: Qx) :=
    (isCycleOf_iff_cycNext hndx).mpr fun z hz => by
      have hzr := hrx.perm.mem_iff.mp hz
      rw [cycNext_isRotated (fullTour_spec hc u).1 hrx.symm hzr, fullTour_cycNext hc u z hzr]
  have hcy : IsCycleOf (eulerSucc ord F) (Py ++ y :: Qy) :=
    (isCycleOf_iff_cycNext hndy).mpr fun z hz => by
      have hzr := hry.perm.mem_iff.mp hz
      rw [cycNext_isRotated (fullTour_spec hc v).1 hry.symm hzr, fullTour_cycNext hc v z hzr]
  have hfx_eq : eulerSucc ord F' x = eulerSucc ord F y := by
    simp only [eulerSucc, x, y, F', addForestEdge, Finset.mem_insert_self, ↓reduceIte,
      he, MGraph.dst, Function.update_self, End.flip, Bool.not_true]
    rw [hc.ordSrc_eq hyv]
  have hfy_eq : eulerSucc ord F' y = eulerSucc ord F x := by
    simp only [eulerSucc, x, y, F', addForestEdge, Finset.mem_insert_self, ↓reduceIte,
      he, MGraph.dst, Bool.false_eq_true, Function.update_self, End.flip, Bool.not_false]
    rw [hc.ordSrc_eq hxu]
  have hf_other : ∀ z, z ≠ x → z ≠ y → eulerSucc ord F' z = eulerSucc ord F z := by
    intro z hzx hzy
    have hze : z.1 ≠ e := by
      intro h; obtain ⟨f, b⟩ := z; change f = e at h; subst f
      cases b
      · exact hzy rfl
      · exact hzx rfl
    simp only [eulerSucc, F', addForestEdge, Finset.mem_insert, hze, false_or]
    split_ifs with hzF
    · obtain ⟨f, b⟩ := z
      cases b <;> simp [MGraph.dst, Function.update_of_ne hze]
    · rfl
  have h1 := List.nodup_append.mp hndx
  have h2 := List.nodup_cons.mp h1.2.1
  have h3 := List.nodup_append.mp hndy
  have h4 := List.nodup_cons.mp h3.2.1
  have hcongr : ∀ (L : List End), x ∉ L → y ∉ L → IsSuccChain (eulerSucc ord F) L →
      IsSuccChain (eulerSucc ord F') L := by
    intro L hxL hyL hL
    induction L with
    | nil => trivial
    | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b bs =>
        have hax : a ≠ x := fun h => hxL (h ▸ List.mem_cons_self)
        have hay : a ≠ y := fun h => hyL (h ▸ List.mem_cons_self)
        exact ⟨(hf_other a hax hay).trans hL.1,
          ih (fun h => hxL (List.mem_cons_of_mem _ h)) (fun h => hyL (List.mem_cons_of_mem _ h)) hL.2⟩
  have hxPx : x ∉ Px := fun h => h1.2.2 x h x List.mem_cons_self rfl
  have hyPx : y ∉ Px := fun h => hdisj (a := y) (by simp [h]) (by simp)
  have hxQx : x ∉ Qx := h2.1
  have hyQx : y ∉ Qx := fun h => hdisj (a := y) (by simp [h]) (by simp)
  have hxPy : x ∉ Py := fun h => hdisj (a := x) (by simp) (by simp [h])
  have hyPy : y ∉ Py := fun h => h3.2.2 y h y List.mem_cons_self rfl
  have hxQy : x ∉ Qy := fun h => hdisj (a := x) (by simp) (by simp [h])
  have hyQy : y ∉ Qy := h4.1
  have hchPx : IsSuccChain (eulerSucc ord F') Px :=
    hcongr Px hxPx hyPx (isSuccChain_of_append_left hcx.1)
  have hchQx : IsSuccChain (eulerSucc ord F') Qx :=
    hcongr Qx hxQx hyQx (isSuccChain_of_append_right (xs := Px ++ [x]) (by simpa [List.append_assoc] using hcx.1))
  have hchPy : IsSuccChain (eulerSucc ord F') Py :=
    hcongr Py hxPy hyPy (isSuccChain_of_append_left hcy.1)
  have hchQy : IsSuccChain (eulerSucc ord F') Qy :=
    hcongr Qy hxQy hyQy (isSuccChain_of_append_right (xs := Py ++ [y]) (by simpa [List.append_assoc] using hcy.1))
  have hchQyPy : IsSuccChain (eulerSucc ord F') (Qy ++ Py) := by
    refine isSuccChain_append hchQy hchPy fun a b ha hb => ?_
    have haQy : a ∈ Qy := List.mem_of_getLast? ha
    rw [hf_other a (fun h => hxQy (h ▸ haQy)) (fun h => hyQy (h ▸ haQy))]
    have hhead_y : (Py ++ y :: Qy).head? = some b := by
      cases Py with
      | nil => simp at hb
      | cons p ps => simpa using hb
    have hlast_y : (Py ++ y :: Qy).getLast? = some a := by
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_cons_of_ne_nil (by intro h0; rw [h0] at ha; simp at ha)]
      exact ha
    exact hcy.2 b a hhead_y hlast_y
  have hchMid : IsSuccChain (eulerSucc ord F') (x :: (Qy ++ Py) ++ [y]) := by
    have hstep1 : IsSuccChain (eulerSucc ord F') (x :: (Qy ++ Py)) := by
      cases hqp : Qy ++ Py with
      | nil => trivial
      | cons b bs =>
        refine ⟨?_, hqp ▸ hchQyPy⟩
        rw [hfx_eq]
        cases Qy with
        | nil =>
          cases Py with
          | nil => simp at hqp
          | cons p ps =>
            have hbp : b = p := by simpa using congrArg List.head? hqp.symm
            rw [hbp]
            exact hcy.2 p y rfl (by simpa [List.append_assoc] using getLast?_append_singleton (p :: ps) y)
        | cons q qs =>
          have hbq : b = q := by simpa using congrArg List.head? hqp.symm
          rw [hbq]
          exact isSuccChain_link_of_append (xs := Py ++ [y]) (ys := q :: qs)
            (by simpa [List.append_assoc] using hcy.1) (getLast?_append_singleton Py y) rfl
    refine isSuccChain_append hstep1 trivial fun a b ha hb => ?_
    have hby : b = y := (Option.some.inj hb).symm; rw [hby]
    cases hqp : Qy ++ Py with
    | nil =>
      rw [hqp] at ha
      have hax : a = x := (Option.some.inj ha).symm; rw [hax]
      have hQy0 : Qy = [] := (List.append_eq_nil_iff.mp hqp).1
      have hPy0 : Py = [] := (List.append_eq_nil_iff.mp hqp).2
      rw [hfx_eq]
      exact hcy.2 y y (by simp [hPy0]) (by simp [hPy0, hQy0])
    | cons u' rest' =>
      rw [hqp, List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)] at ha
      have ha_qp : (Qy ++ Py).getLast? = some a := by rw [hqp]; exact ha
      cases Py with
      | nil =>
        rw [List.append_nil] at ha_qp
        have haQy : a ∈ Qy := List.mem_of_getLast? ha_qp
        rw [hf_other a (fun h => hxQy (h ▸ haQy)) (fun h => hyQy (h ▸ haQy))]
        exact hcy.2 y a rfl (by rw [List.nil_append, List.getLast?_cons_of_ne_nil
          (List.ne_nil_of_mem haQy)]; exact ha_qp)
      | cons p ps =>
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at ha_qp
        have haPy : a ∈ p :: ps := List.mem_of_getLast? ha_qp
        rw [hf_other a (fun h => hxPy (h ▸ haPy)) (fun h => hyPy (h ▸ haPy))]
        exact isSuccChain_link_of_append hcy.1 ha_qp rfl
  have hch_all : IsSuccChain (eulerSucc ord F') (Px ++ (x :: (Qy ++ Py) ++ [y]) ++ Qx) := by
    have hL : IsSuccChain (eulerSucc ord F') (Px ++ (x :: (Qy ++ Py) ++ [y])) := by
      refine isSuccChain_append hchPx hchMid fun a b ha hb => ?_
      have hbx : b = x := (Option.some.inj hb).symm; rw [hbx]
      have haPx : a ∈ Px := List.mem_of_getLast? ha
      rw [hf_other a (fun h => hxPx (h ▸ haPx)) (fun h => hyPx (h ▸ haPx))]
      exact isSuccChain_link_of_append hcx.1 ha rfl
    refine isSuccChain_append hL hchQx fun a b ha hb => ?_
    have hay : a = y := by
      have : (Px ++ (x :: (Qy ++ Py) ++ [y])).getLast? = some y := by
        simpa [List.append_assoc] using getLast?_append_singleton (Px ++ x :: (Qy ++ Py)) y
      exact (Option.some.inj (this.symm.trans ha)).symm
    rw [hay, hfy_eq]
    exact isSuccChain_link_of_append (xs := Px ++ [x]) (ys := Qx)
      (by simpa [List.append_assoc] using hcx.1) (getLast?_append_singleton Px x) hb
  have hcyc_all : IsCycleOf (eulerSucc ord F') (Px ++ x :: Qy ++ Py ++ y :: Qx) := by
    have heq_list : Px ++ (x :: (Qy ++ Py) ++ [y]) ++ Qx = Px ++ x :: Qy ++ Py ++ y :: Qx := by
      simp [List.append_assoc]
    rw [← heq_list]
    refine ⟨hch_all, fun a b ha hb => ?_⟩
    cases Qx with
    | nil =>
      have hby : b = y := by
        have : (Px ++ (x :: (Qy ++ Py) ++ [y]) ++ []).getLast? = some y := by
          simpa [List.append_assoc] using getLast?_append_singleton (Px ++ x :: (Qy ++ Py)) y
        exact (Option.some.inj (this.symm.trans hb)).symm
      rw [hby, hfy_eq]
      cases Px with
      | nil =>
        have hax : a = x := (Option.some.inj ha).symm; rw [hax]
        exact hcx.2 x x rfl rfl
      | cons p ps =>
        have hap : a = p := (Option.some.inj ha).symm; rw [hap]
        exact hcx.2 p x rfl (by simpa [List.append_assoc] using getLast?_append_singleton (p :: ps) x)
    | cons q qs =>
      have hb_eq : (q :: qs).getLast? = some b := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hb
        exact hb
      have hbQx : b ∈ q :: qs := List.mem_of_getLast? hb_eq
      rw [hf_other b (fun h => hxQx (h ▸ hbQx)) (fun h => hyQx (h ▸ hbQx))]
      have hhead_x : (Px ++ x :: q :: qs).head? = some a := by cases Px <;> simpa using ha
      have hlast_x : (Px ++ x :: q :: qs).getLast? = some b := by
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)]
        exact hb_eq
      exact hcx.2 a b hhead_x hlast_x
  have hx_in : x ∈ fullTour ord F' hc'.forest u :=
    ((fullTour_spec hc' u).2 x).mpr ⟨u, hxu, connected_refl F' u⟩
  exact isRotated_of_cycNext_eq hnd_all (fullTour_spec hc' u).1 (by simp) hx_in
    ((isCycleOf_iff_cycNext hnd_all).mp hcyc_all) (fullTour_cycNext hc' u)

end MinCostFlow.SparseCore.Program
