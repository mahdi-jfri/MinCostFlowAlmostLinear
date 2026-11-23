module

public import MinCostFlow.SparseCore.Program.TourSurgeryEdits
public import MinCostFlow.SparseCore.Program.TourCutLinkMath
import Mathlib.Tactic

/-!
# Graph and order math for simple `applyEdits` variants (`dropEdge`, `insertBefore`, `rotateTo`)

Proves `TourValid` preservation and Euler-tour preservation lemmas for `dropEdge`, `insertBefore`,
and `rotateTo`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

/-! ## `dropEdge` math -/

theorem tourValid_applyEdit_dropEdge {vCap eCap e : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (he_open : e ∉ s.rf.F.E) :
    TourValid vCap eCap (tourApplyEdit s (.dropEdge e)) where
  ordWithin :=
    ⟨fun v => (hv.ordWithin.1 v).filter _,
     fun v hge => by simp [tourApplyEdit, applyOrdEdit, hv.ordWithin.2.1 v hge],
     fun v x hx => hv.ordWithin.2.2 v x (List.mem_filter.mp hx).1⟩
  compat :=
    ⟨fun v => (hv.compat.nodup v).filter _,
     fun u₁ u₂ x h1 h2 => hv.compat.unique u₁ u₂ x (List.mem_filter.mp h1).1 (List.mem_filter.mp h2).1,
     hv.compat.forest,
     fun u hu => hv.compat.vert u fun h0 => hu (by simp [tourApplyEdit, applyOrdEdit, h0]),
     fun f hf => by
       have hne : f ≠ e := fun h => he_open (h ▸ hf)
       have ⟨ht, hh⟩ := hv.compat.forestEnd f hf
       exact ⟨by simp [tourApplyEdit, applyOrdEdit, ht, hne],
              by simp [tourApplyEdit, applyOrdEdit, hh, hne]⟩⟩
  roots_sub := hv.roots_sub
  verts_lt := hv.verts_lt
  unique_root := hv.unique_root
  marked_open := fun x hx => by
    simp only [tourApplyEdit, Finset.mem_filter] at hx
    obtain ⟨⟨v, hxv⟩, hxo⟩ := hv.marked_open x hx.1
    exact ⟨⟨v, by simp [tourApplyEdit, applyOrdEdit, hxv, bne_iff_ne.mp hx.2]⟩, hxo⟩

theorem applyOrdEdit_dropEdge_eq_updates {ord : ℕ → List End} {e : ℕ}
    (huniq : ∀ u₁ u₂ x, x ∈ ord u₁ → x ∈ ord u₂ → u₁ = u₂) :
    open Classical in
    let ord1 := if h : ∃ u, (e, true) ∈ ord u then
      Function.update ord h.choose ((ord h.choose).filter fun z => z != (e, true))
      else ord
    let ord2 := if h : ∃ v, (e, false) ∈ ord1 v then
      Function.update ord1 h.choose ((ord1 h.choose).filter fun z => z != (e, false))
      else ord1
    applyOrdEdit ord (.dropEdge e) = ord2 := by
  classical
  intro ord1 ord2
  funext w
  have hmem1 : ∀ w', ord1 w' = (ord w').filter fun z => z != (e, true) := by
    intro w'; dsimp only [ord1]
    split_ifs with hex
    · by_cases hwe : w' = hex.choose
      · subst hwe; simp
      · rw [Function.update_of_ne hwe, List.filter_eq_self.mpr]
        intro z hz; simp only [bne_iff_ne]; intro hze
        exact hwe (huniq w' hex.choose (e, true) (hze ▸ hz) hex.choose_spec)
    · rw [List.filter_eq_self.mpr]
      intro z hz; simp only [bne_iff_ne]; intro hze
      exact hex ⟨w', hze ▸ hz⟩
  have hmem2 : ∀ w', ord2 w' = (ord1 w').filter fun z => z != (e, false) := by
    intro w'; dsimp only [ord2]
    split_ifs with hex
    · by_cases hwe : w' = hex.choose
      · subst hwe; simp
      · rw [Function.update_of_ne hwe, List.filter_eq_self.mpr]
        intro z hz; simp only [bne_iff_ne]; intro hze
        have h1 : (e, false) ∈ ord w' := (List.mem_filter.mp (hmem1 w' ▸ (hze ▸ hz))).1
        have h2 : (e, false) ∈ ord hex.choose := (List.mem_filter.mp (hmem1 hex.choose ▸ hex.choose_spec)).1
        exact hwe (huniq w' hex.choose (e, false) h1 h2)
    · rw [List.filter_eq_self.mpr]
      intro z hz; simp only [bne_iff_ne]; intro hze
      exact hex ⟨w', hze ▸ hz⟩
  rw [hmem2 w, hmem1 w, List.filter_filter]
  simp only [applyOrdEdit]
  refine List.filter_congr fun z _ => ?_
  apply Bool.eq_iff_iff.mpr
  obtain ⟨f, b⟩ := z
  cases b <;> simp [bne_iff_ne]

theorem fullTour_dropOneOpen_other {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v r : ℕ} {x : End} (hx_mem : x ∈ ord v) (hx_open : x.1 ∉ F.E) (hnc : ¬F.Connected r v) :
    let ord' := Function.update ord v ((ord v).filter fun z => z != x)
    have hc' : OrdForestCompat ord' F := by
      refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hc.forest, fun u hu => ?_, fun e he => ?_⟩
      · by_cases huv : u = v
        · subst huv; simpa [ord'] using (hc.nodup u).filter _
        · simpa [ord', Function.update_of_ne huv] using hc.nodup u
      · have hsub : ∀ w z, z ∈ ord' w → z ∈ ord w := fun w z hz => by
          by_cases hwv : w = v
          · subst hwv; simp only [ord', Function.update_self, List.mem_filter] at hz; exact hz.1
          · simpa [ord', Function.update_of_ne hwv] using hz
        exact hc.unique u₁ u₂ z (hsub _ _ h1) (hsub _ _ h2)
      · by_cases huv : u = v
        · exact huv ▸ hc.vert v (List.ne_nil_of_mem hx_mem)
        · exact hc.vert u (by simpa [ord', Function.update_of_ne huv] using hu)
      · have hmem : ∀ w z, z ∈ ord w → z ≠ x → z ∈ ord' w := fun w z hz hzx => by
          by_cases hwv : w = v
          · subst hwv; simp [ord', hz, hzx]
          · simpa [ord', Function.update_of_ne hwv] using hz
        exact ⟨hmem _ _ (hc.forestEnd e he).1 (fun h => hx_open (h ▸ he)),
               hmem _ _ (hc.forestEnd e he).2 (fun h => hx_open (h ▸ he))⟩
    fullTour ord' F hc'.forest r = fullTour ord F hc.forest r := by
  intro ord' hc'
  have hr_ne_v : r ≠ v := fun h => hnc (h ▸ connected_refl F r)
  have hord'_r : ord' r = ord r := Function.update_of_ne hr_ne_v _ _
  by_cases hnil : ord r = []
  · rw [(fullTour_eq_nil_iff hc' r).mpr (by rw [hord'_r, hnil]),
        (fullTour_eq_nil_iff hc r).mpr hnil]
  · obtain ⟨a, ha⟩ : ∃ a, (ord r).head? = some a :=
      Option.isSome_iff_exists.mp (by cases ho : ord r <;> simp_all)
    have ha' : (ord' r).head? = some a := by rw [hord'_r]; exact ha
    have ha1 : a ∈ fullTour ord' F hc'.forest r :=
      ((fullTour_spec hc' r).2 a).mpr ⟨r, List.mem_of_head? ha', connected_refl F r⟩
    have ha2 : a ∈ fullTour ord F hc.forest r :=
      ((fullTour_spec hc r).2 a).mpr ⟨r, List.mem_of_head? ha, connected_refl F r⟩
    have hrot : (fullTour ord' F hc'.forest r).IsRotated (fullTour ord F hc.forest r) :=
      isRotated_of_cycNext_eq (fullTour_spec hc' r).1 (fullTour_spec hc r).1 ha1 ha2
        (fun z hz => by
          obtain ⟨u, hzu', hcru⟩ := ((fullTour_spec hc' r).2 z).mp hz
          have huv : u ≠ v := fun h => hnc (h ▸ hcru)
          have hzu : z ∈ ord u := by simpa [ord', Function.update_of_ne huv] using hzu'
          refine (fullTour_cycNext hc' r z hz).trans ?_
          by_cases hzF : z.1 ∈ F.E
          · have hdv : F.dst z ≠ v := fun h =>
              hnc (connected_trans hcru (h ▸ ⟨[z], .cons hzF ((hc.ordSrc_of_forest hzF).symm.trans (hc.ordSrc_eq hzu)) (.nil _)⟩))
            simp [eulerSucc, hzF, ord', Function.update_of_ne hdv]
          · simp [eulerSucc, hzF, hc'.ordSrc_eq hzu', hc.ordSrc_eq hzu, ord', Function.update_of_ne huv])
        (fullTour_cycNext hc r)
    exact (tour_rotateToList_eq_of_isRotated (fullTour_spec hc' r).1 (List.IsRotated.refl _) (fullTour_head? hc' r ha')).symm.trans
      (tour_rotateToList_eq_of_isRotated (fullTour_spec hc r).1 hrot (fullTour_head? hc r ha))

/-! ## `insertBefore` math -/

theorem tourValid_applyEdit_insertBefore {vCap eCap v : ℕ} {x : End} {yOpt : Option End}
    {s : TourAbs} (hv : TourValid vCap eCap s)
    (he : TourEditValid vCap eCap s (.insertBefore v x yOpt)) :
    TourValid vCap eCap (tourApplyEdit s (.insertBefore v x yOpt)) := by
  rcases he with ⟨hvLt, hvF, hxCap, _, hxFresh, _⟩
  have hmem_ib : ∀ z, z ∈ insertBeforeList x yOpt (s.ord v) ↔ z = x ∨ z ∈ s.ord v := by
    intro z; simp only [insertBeforeList]
    cases yOpt with
    | none => simp [or_comm]
    | some y' =>
      have htd := List.take_append_drop ((s.ord v).idxOf y') (s.ord v)
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro (h | rfl | h)
        · exact Or.inr (List.mem_of_mem_take h)
        · exact Or.inl rfl
        · exact Or.inr (List.mem_of_mem_drop h)
      · rintro (rfl | hz)
        · exact Or.inr (Or.inl rfl)
        · rw [← htd, List.mem_append] at hz
          rcases hz with h | h; exact Or.inl h; exact Or.inr (Or.inr h)
  have hnd_v : (insertBeforeList x yOpt (s.ord v)).Nodup := by
    simp only [insertBeforeList]
    cases yOpt with
    | none => exact List.nodup_append.mpr ⟨hv.compat.nodup v, List.nodup_singleton x,
        fun a ha b hb h => by simp at hb; subst hb; subst h; exact hxFresh v ha⟩
    | some y' =>
      have htd := List.take_append_drop ((s.ord v).idxOf y') (s.ord v)
      have hsp := List.nodup_append.mp (htd.symm ▸ hv.compat.nodup v)
      refine List.nodup_append.mpr ⟨hsp.1, List.nodup_cons.mpr ⟨fun hm => hxFresh v (List.mem_of_mem_drop hm), hsp.2.1⟩,
        fun a ha b hb h => ?_⟩
      subst h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hxFresh v (List.mem_of_mem_take ha)
      · exact hsp.2.2 a ha a hb' rfl
  refine
    { ordWithin :=
        ⟨fun u => by
           by_cases huv : u = v
           · subst huv; simpa [tourApplyEdit, applyOrdEdit] using hnd_v
           · simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.ordWithin.1 u,
         fun u hge => by
           have huv : u ≠ v := by omega
           simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.ordWithin.2.1 u hge,
         fun u z hz => by
           by_cases huv : u = v
           · subst huv; simp only [tourApplyEdit, applyOrdEdit, Function.update_self, hmem_ib] at hz
             rcases hz with rfl | hz; exact hxCap; exact hv.ordWithin.2.2 u z hz
           · simp only [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] at hz
             exact hv.ordWithin.2.2 u z hz⟩
      compat :=
        ⟨fun u => by
           by_cases huv : u = v
           · subst huv; simpa [tourApplyEdit, applyOrdEdit] using hnd_v
           · simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.compat.nodup u,
         fun u₁ u₂ z h1 h2 => by
           have hm : ∀ w, z ∈ (tourApplyEdit s (.insertBefore v x yOpt)).ord w ↔ (w = v ∧ z = x) ∨ z ∈ s.ord w := fun w => by
             by_cases hwv : w = v
             · subst hwv; simp [tourApplyEdit, applyOrdEdit, hmem_ib]
             · simp [tourApplyEdit, applyOrdEdit, hwv]
           rcases (hm u₁).mp h1 with ⟨rfl, rfl⟩ | h1'
           · rcases (hm u₂).mp h2 with ⟨rfl, _⟩ | h2'; rfl; exact absurd h2' (hxFresh u₂)
           · rcases (hm u₂).mp h2 with ⟨rfl, rfl⟩ | h2'; exact absurd h1' (hxFresh u₁); exact hv.compat.unique u₁ u₂ z h1' h2',
         hv.compat.forest,
         fun u hu => by
           by_cases huv : u = v
           · exact huv ▸ hvF
           · exact hv.compat.vert u (by simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hu),
         fun e he => by
           have hsub : ∀ w z, z ∈ s.ord w → z ∈ (tourApplyEdit s (.insertBefore v x yOpt)).ord w := fun w z hz => by
             by_cases hwv : w = v
             · subst hwv; simp [tourApplyEdit, applyOrdEdit, hmem_ib, hz]
             · simp [tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv, hz]
           exact ⟨hsub _ _ (hv.compat.forestEnd e he).1, hsub _ _ (hv.compat.forestEnd e he).2⟩⟩
      roots_sub := hv.roots_sub
      verts_lt := hv.verts_lt
      unique_root := hv.unique_root
      marked_open := fun z hz => by
        obtain ⟨⟨u, hzu⟩, hzo⟩ := hv.marked_open z hz
        refine ⟨⟨u, ?_⟩, hzo⟩
        by_cases huv : u = v
        · subst huv; simp [tourApplyEdit, applyOrdEdit, hmem_ib, hzu]
        · simp [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv, hzu] }

theorem insertBeforeList_head? (x : End) (yOpt : Option End) :
    ∀ xs : List End,
    (insertBeforeList x yOpt xs).head? =
      match xs.head? with
      | none => some x
      | some a => if yOpt = some a then some x else some a
  | [] => by cases yOpt <;> simp [insertBeforeList]
  | a :: as => by
    cases yOpt with
    | none => simp [insertBeforeList]
    | some y' =>
      by_cases hya : y' = a
      · subst hya; simp [insertBeforeList, List.idxOf_cons_self]
      · have hne : a ≠ y' := fun h => hya h.symm
        simp [insertBeforeList, List.idxOf_cons_ne _ hne, hya]

theorem empty_ord_mem_roots {vCap eCap v : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hvF : v ∈ s.rf.F.V) (hnil : s.ord v = []) :
    v ∈ s.rf.R ∧ ∀ u, s.rf.F.Connected v u → u = v := by
  have hiso : ∀ u, s.rf.F.Connected v u → u = v := by
    intro u hconn
    by_contra huv
    obtain ⟨x, hxF, hxsrc⟩ := exists_edge_of_connected_ne hconn (Ne.symm huv)
    have hx_in := hv.compat.mem_ord_of_forest hxF
    rw [hxsrc, hnil] at hx_in; simp at hx_in
  have hr := hv.root_spec hvF
  have heq : s.rf.root v = v := hiso _ hr.2
  exact ⟨heq ▸ hr.1, hiso⟩

theorem fullTour_insertOpen_singleton {vCap eCap v : ℕ} {x : End} {yOpt : Option End} {s : TourAbs}
    (hv : TourValid vCap eCap s) (he : TourEditValid vCap eCap s (.insertBefore v x yOpt))
    (hnil : s.ord v = []) :
    let s' := tourApplyEdit s (.insertBefore v x yOpt)
    fullTour s'.ord s'.rf.F (tourValid_applyEdit_insertBefore hv he).compat.forest v = [x] := by
  intro s'
  have hord' : s'.ord v = [x] := by
    simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, hnil]
    cases yOpt <;> simp [insertBeforeList]
  unfold fullTour
  rw [fullTourBlocks.eq_def, hord']
  simp [s', tourApplyEdit, he.2.2.2.1]

theorem fullTour_insertOpen_other {vCap eCap v r : ℕ} {x : End} {yOpt : Option End} {s : TourAbs}
    (hv : TourValid vCap eCap s) (he : TourEditValid vCap eCap s (.insertBefore v x yOpt))
    (hnc : ¬s.rf.F.Connected r v) :
    let s' := tourApplyEdit s (.insertBefore v x yOpt)
    fullTour s'.ord s'.rf.F (tourValid_applyEdit_insertBefore hv he).compat.forest r =
      fullTour s.ord s.rf.F hv.compat.forest r := by
  intro s'
  have hc' := (tourValid_applyEdit_insertBefore hv he).compat
  have hr_ne_v : r ≠ v := fun h => hnc (h ▸ connected_refl _ r)
  have hord'_r : s'.ord r = s.ord r := by simp [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr_ne_v]
  by_cases hnil : s.ord r = []
  · rw [(fullTour_eq_nil_iff hc' r).mpr (by rw [hord'_r, hnil]), (fullTour_eq_nil_iff hv.compat r).mpr hnil]
  · obtain ⟨a, ha⟩ : ∃ a, (s.ord r).head? = some a :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
    have ha' : (s'.ord r).head? = some a := by rw [hord'_r]; exact ha
    have ha1 : a ∈ fullTour s'.ord s'.rf.F hc'.forest r :=
      ((fullTour_spec hc' r).2 a).mpr ⟨r, List.mem_of_head? ha', connected_refl _ r⟩
    have ha2 : a ∈ fullTour s.ord s.rf.F hv.compat.forest r :=
      ((fullTour_spec hv.compat r).2 a).mpr ⟨r, List.mem_of_head? ha, connected_refl _ r⟩
    have hrot : (fullTour s'.ord s'.rf.F hc'.forest r).IsRotated (fullTour s.ord s.rf.F hv.compat.forest r) :=
      isRotated_of_cycNext_eq (fullTour_spec hc' r).1 (fullTour_spec hv.compat r).1 ha1 ha2
        (fun z hz => by
          obtain ⟨u, hzu', hcru⟩ := ((fullTour_spec hc' r).2 z).mp hz
          have huv : u ≠ v := fun h => hnc (h ▸ hcru)
          have hzu : z ∈ s.ord u := by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hzu'
          refine (fullTour_cycNext hc' r z hz).trans ?_
          by_cases hzF : z.1 ∈ s.rf.F.E
          · have hdv : s.rf.F.dst z ≠ v := fun h =>
              hnc (connected_trans hcru (h ▸ ⟨[z], .cons hzF ((hv.compat.ordSrc_of_forest hzF).symm.trans (hv.compat.ordSrc_eq hzu)) (.nil _)⟩))
            simp [eulerSucc, hzF, tourApplyEdit, applyOrdEdit, Function.update_of_ne hdv]
          · simp only [eulerSucc, tourApplyEdit, hzF, ↓reduceIte]
            have hsrc1 : ordSrc (applyOrdEdit s.ord (.insertBefore v x yOpt)) z = u := hc'.ordSrc_eq hzu'
            rw [hsrc1, hv.compat.ordSrc_eq hzu]
            simp [applyOrdEdit, Function.update_of_ne huv])
        (fullTour_cycNext hv.compat r)
    exact (tour_rotateToList_eq_of_isRotated (fullTour_spec hc' r).1 (List.IsRotated.refl _) (fullTour_head? hc' r ha')).symm.trans
      (tour_rotateToList_eq_of_isRotated (fullTour_spec hv.compat r).1 hrot (fullTour_head? hv.compat r ha))

/-! ## `rotateTo` math -/

theorem tourValid_applyEdit_rotateTo {vCap eCap v : ℕ} {y : End} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hvLt : v < vCap) :
    TourValid vCap eCap (tourApplyEdit s (.rotateTo v y)) := by
  have hmem : ∀ w z, z ∈ (tourApplyEdit s (.rotateTo v y)).ord w ↔ z ∈ s.ord w := fun w z => by
    by_cases hwv : w = v
    · subst hwv; simp only [tourApplyEdit, applyOrdEdit, Function.update_self]
      exact rotateToList_isRotated.perm.mem_iff.symm
    · simp [tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv]
  refine
    { ordWithin :=
        ⟨fun u => by
           by_cases huv : u = v
           · subst huv; simp only [tourApplyEdit, applyOrdEdit, Function.update_self]
             exact rotateToList_isRotated.perm.nodup_iff.mp (hv.ordWithin.1 u)
           · simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.ordWithin.1 u,
         fun u hge => by
           have huv : u ≠ v := by omega
           simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.ordWithin.2.1 u hge,
         fun u z hz => hv.ordWithin.2.2 u z ((hmem u z).mp hz)⟩
      compat :=
        ⟨fun u => by
           by_cases huv : u = v
           · subst huv; simp only [tourApplyEdit, applyOrdEdit, Function.update_self]
             exact rotateToList_isRotated.perm.nodup_iff.mp (hv.compat.nodup u)
           · simpa [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv] using hv.compat.nodup u,
         fun u₁ u₂ z h1 h2 => hv.compat.unique u₁ u₂ z ((hmem u₁ z).mp h1) ((hmem u₂ z).mp h2),
         hv.compat.forest,
         fun u hu => hv.compat.vert u fun h0 => hu (by
           by_cases huv : u = v
           · subst huv; simp [tourApplyEdit, applyOrdEdit, rotateToList, h0]
           · simp [tourApplyEdit, applyOrdEdit, Function.update_of_ne huv, h0]),
         fun e he => ⟨(hmem _ _).mpr (hv.compat.forestEnd e he).1, (hmem _ _).mpr (hv.compat.forestEnd e he).2⟩⟩
      roots_sub := hv.roots_sub
      verts_lt := hv.verts_lt
      unique_root := hv.unique_root
      marked_open := fun z hz => by
        obtain ⟨⟨u, hzu⟩, hzo⟩ := hv.marked_open z hz
        exact ⟨⟨u, (hmem u z).mpr hzu⟩, hzo⟩ }

theorem rotateToList_head?_of_mem {y : End} {xs : List End} (hy : y ∈ xs) :
    (rotateToList y xs).head? = some y := by
  unfold rotateToList
  simp only [hy, ↓reduceIte]
  have hlen : xs.idxOf y < xs.length := List.idxOf_lt_length_iff.mpr hy
  have hne : xs.drop (xs.idxOf y) ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  rw [List.head?_append_of_ne_nil _ hne, List.head?_drop, List.getElem?_eq_getElem hlen, List.getElem_idxOf hlen]

end MinCostFlow.SparseCore.Program
