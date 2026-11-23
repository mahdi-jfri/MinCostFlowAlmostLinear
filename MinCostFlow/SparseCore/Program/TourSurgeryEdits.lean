module

public import MinCostFlow.SparseCore.Program.TourMath

/-!
# Open-end insertion, deletion, and rotation surgery for Euler tours

Proves `fullTour_insertOpen`, `fullTour_dropOneOpen`, and `fullTour_rotateTo`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF

private theorem cycNext_append_eq' {xs ys : List End} (hnd : (xs ++ ys).Nodup) {a b : End}
    (ha : xs.getLast? = some a) (hb : ys.head? = some b) :
    cycNext (xs ++ ys) a = b := by
  have hc : IsCycleOf (cycNext (xs ++ ys)) (xs ++ ys) :=
    (isCycleOf_iff_cycNext hnd).mpr fun _ _ => rfl
  exact isSuccChain_link_of_append hc.1 ha hb

/-- Helper: cyclic-successor relation when inserting `x` immediately before `y` in `y :: tail`. -/
private theorem cycNext_cons_insert {x y : End} {tail : List End}
    (hnd : (x :: y :: tail).Nodup) {z : End} (hz : z ∈ y :: tail) :
    cycNext (x :: y :: tail) z = if cycNext (y :: tail) z = y then x else cycNext (y :: tail) z := by
  have hnd_o : (y :: tail).Nodup := (List.nodup_cons.mp hnd).2
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  rw [cycNext_eq_getElem hnd_o hi]
  have hi_n : i + 1 < (x :: y :: tail).length := by simpa using Nat.succ_lt_succ hi
  have hget_n : (x :: y :: tail)[i + 1]'hi_n = (y :: tail)[i]'hi := rfl
  conv_lhs => rw [← hget_n, cycNext_eq_getElem hnd hi_n]
  by_cases hlast : i + 1 < (y :: tail).length
  · have hne_y : (y :: tail)[(i + 1) % (y :: tail).length]'(Nat.mod_lt _ (by omega)) ≠ y := by
      simp only [Nat.mod_eq_of_lt hlast]
      intro heq
      have h0 : (y :: tail)[0]'(by simp) = y := rfl
      rw [← h0] at heq
      have := (hnd_o.getElem_inj_iff).mp heq
      omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne_y)]
    have hlt2 : i + 1 + 1 < (x :: y :: tail).length := by simpa using Nat.succ_lt_succ hlast
    simp only [Nat.mod_eq_of_lt hlast, Nat.mod_eq_of_lt hlt2]
    rfl
  · have heq_len : i + 1 = (y :: tail).length := by omega
    have hmod0 : (i + 1) % (y :: tail).length = 0 := by rw [heq_len, Nat.mod_self]
    have hmod1 : (i + 1 + 1) % (x :: y :: tail).length = 0 := by
      have : i + 1 + 1 = (x :: y :: tail).length := by
        simp only [List.length_cons] at heq_len ⊢; omega
      rw [this, Nat.mod_self]
    simp only [hmod0, hmod1]
    simp

/-- Helper: cyclic-successor relation when deleting `x` from `x :: tail` (with `tail ≠ []`). -/
private theorem cycNext_cons_delete {x : End} {tail : List End}
    (hnd : (x :: tail).Nodup) {z : End} (hz : z ∈ tail) :
    cycNext tail z = if cycNext (x :: tail) z = x then cycNext (x :: tail) x else cycNext (x :: tail) z := by
  have hnd_n : tail.Nodup := (List.nodup_cons.mp hnd).2
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  rw [cycNext_eq_getElem hnd_n hi]
  have hi_o : i + 1 < (x :: tail).length := by simpa using Nat.succ_lt_succ hi
  have hget_o : (x :: tail)[i + 1]'hi_o = tail[i]'hi := rfl
  have hcx_z : cycNext (x :: tail) (tail[i]'hi) =
      (x :: tail)[(i + 1 + 1) % (x :: tail).length]'(Nat.mod_lt _ (by simp)) := by
    rw [← hget_o, cycNext_eq_getElem hnd hi_o]
  rw [hcx_z]
  by_cases hlast : i + 1 < tail.length
  · have hlt2 : i + 1 + 1 < (x :: tail).length := by simpa using Nat.succ_lt_succ hlast
    have hne_x : (x :: tail)[(i + 1 + 1) % (x :: tail).length]'(Nat.mod_lt _ (by simp)) ≠ x := by
      simp only [Nat.mod_eq_of_lt hlt2]
      intro heq
      have h0 : (x :: tail)[0]'(by simp) = x := rfl
      rw [← h0] at heq
      have := (hnd.getElem_inj_iff).mp heq
      omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne_x)]
    simp only [Nat.mod_eq_of_lt hlast, Nat.mod_eq_of_lt hlt2]
    rfl
  · have heq_len : i + 1 = tail.length := by omega
    have hmod0 : (i + 1) % tail.length = 0 := by rw [heq_len, Nat.mod_self]
    have hmod1 : (i + 1 + 1) % (x :: tail).length = 0 := by
      have : i + 1 + 1 = (x :: tail).length := by simp only [List.length_cons]; omega
      rw [this, Nat.mod_self]
    have h0x : cycNext (x :: tail) x = tail[0]'(by omega) := by
      have := cycNext_eq_getElem hnd (i := 0) (by simp)
      have h1lt : 1 < (x :: tail).length := by simp only [List.length_cons]; omega
      simpa only [Nat.zero_add, Nat.mod_eq_of_lt h1lt, List.getElem_cons_zero,
        List.getElem_cons_succ] using this
    simp only [hmod0, hmod1, h0x]
    simp

private theorem idxOf_append_cons_of_notMem {y : End} {pre suf : List End} (h : y ∉ pre) :
    (pre ++ y :: suf).idxOf y = pre.length := by
  induction pre with
  | nil => simp [List.idxOf_cons_self]
  | cons a rest ih =>
    have hay : a ≠ y := fun heq => h (heq ▸ List.mem_cons_self)
    have hrest : y ∉ rest := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [List.idxOf_cons_ne _ hay, ih hrest]

private theorem idxOf_eq_length_of_notMem {y : End} {xs : List End} (h : y ∉ xs) :
    xs.idxOf y = xs.length := by
  induction xs with
  | nil => simp [List.idxOf]
  | cons a rest ih =>
    have hay : a ≠ y := fun heq => h (heq ▸ List.mem_cons_self)
    have hrest : y ∉ rest := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [List.idxOf_cons_ne _ hay, ih hrest]

/-- Single-end open insertion surgery: inserting a fresh open end `x` before `y` in `ord v`
inserts `x` immediately before `y` in `fullTour`. -/
theorem fullTour_insertOpen {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v : ℕ} {x y : End} {yOpt : Option End}
    (hv : v ∈ F.V) (hx_fresh : ∀ u, x ∉ ord u) (hx_open : x.1 ∉ F.E)
    (hy_mem : y ∈ ord v)
    (hy_target : yOpt = some y ∨ ((yOpt = none ∨ ∃ y', yOpt = some y' ∧ y' ∉ ord v) ∧
      (ord v).head? = some y))
    {P Q : List End}
    (hrot : (P ++ y :: Q).IsRotated (fullTour ord F hc.forest v)) :
    let ord' := applyOrdEdit ord (.insertBefore v x yOpt)
    have hc' : OrdForestCompat ord' F := by
      refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hc.forest, fun u hu => ?_, fun e he => ?_⟩
      · unfold ord' applyOrdEdit
        by_cases huv : u = v
        · subst huv
          simp only [Function.update_self, insertBeforeList]
          cases yOpt with
          | none => exact List.nodup_append.mpr ⟨hc.nodup u, List.nodup_singleton x,
              fun a ha b hb h => by simp at hb; subst hb; subst h; exact hx_fresh u ha⟩
          | some y' =>
            have htd := List.take_append_drop ((ord u).idxOf y') (ord u)
            have hnd_td : ((ord u).take ((ord u).idxOf y') ++ (ord u).drop ((ord u).idxOf y')).Nodup :=
              htd.symm ▸ hc.nodup u
            have hsp := List.nodup_append.mp hnd_td
            refine List.nodup_append.mpr ⟨hsp.1, List.nodup_cons.mpr
              ⟨fun hm => hx_fresh u (List.mem_of_mem_drop hm), hsp.2.1⟩, fun a ha b hb h => ?_⟩
            subst h
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hx_fresh u (List.mem_of_mem_take ha)
            · exact hsp.2.2 a ha a hb' rfl
        · simpa [Function.update_of_ne huv] using hc.nodup u
      · have hmem : ∀ w z, z ∈ ord' w ↔ (w = v ∧ z = x) ∨ z ∈ ord w := by
          intro w z
          unfold ord' applyOrdEdit
          by_cases hwv : w = v
          · subst hwv
            simp only [Function.update_self, insertBeforeList, true_and]
            cases yOpt with
            | none => simp [or_comm]
            | some y' =>
              have htd := List.take_append_drop ((ord w).idxOf y') (ord w)
              simp only [List.mem_append, List.mem_cons]
              constructor
              · rintro (h | rfl | h)
                · exact Or.inr (List.mem_of_mem_take h)
                · exact Or.inl rfl
                · exact Or.inr (List.mem_of_mem_drop h)
              · rintro (rfl | hz)
                · exact Or.inr (Or.inl rfl)
                · rw [← htd, List.mem_append] at hz
                  rcases hz with h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inr h)
          · simp [hwv]
        rcases (hmem u₁ z).mp h1 with ⟨rfl, hzx⟩ | h1'
        · subst hzx
          rcases (hmem u₂ z).mp h2 with ⟨rfl, _⟩ | h2'
          · rfl
          · exact absurd h2' (hx_fresh u₂)
        · rcases (hmem u₂ z).mp h2 with ⟨rfl, hzx⟩ | h2'
          · subst hzx; exact absurd h1' (hx_fresh u₁)
          · exact hc.unique u₁ u₂ z h1' h2'
      · by_cases huv : u = v
        · exact huv ▸ hv
        · exact hc.vert u (by simpa [ord', applyOrdEdit, Function.update_of_ne huv] using hu)
      · have hsub_ord : ∀ w z, z ∈ ord w → z ∈ ord' w := by
          intro w z hz
          unfold ord' applyOrdEdit
          by_cases hwv : w = v
          · subst hwv
            simp only [Function.update_self, insertBeforeList]
            cases yOpt with
            | none => simp [hz]
            | some y' =>
              have htd := List.take_append_drop ((ord w).idxOf y') (ord w)
              rw [← htd, List.mem_append] at hz
              rcases hz with h | h <;> simp [h]
          · simpa [Function.update_of_ne hwv] using hz
        exact ⟨hsub_ord _ _ (hc.forestEnd e he).1, hsub_ord _ _ (hc.forestEnd e he).2⟩
    (P ++ x :: y :: Q).IsRotated (fullTour ord' F hc'.forest v) := by
  intro ord' hc'
  have hnd : (P ++ y :: Q).Nodup := hrot.perm.nodup_iff.mpr (fullTour_spec hc v).1
  have hx_not_L : x ∉ P ++ y :: Q := by
    intro hm
    obtain ⟨u, hxu, _⟩ := ((fullTour_spec hc v).2 x).mp (hrot.perm.mem_iff.mp hm)
    exact hx_fresh u hxu
  have hnd_new : (P ++ x :: y :: Q).Nodup := by
    have h1 := List.nodup_append.mp hnd
    refine List.nodup_append.mpr ⟨h1.1, List.nodup_cons.mpr ⟨fun hm => hx_not_L (by simp [hm]),
      h1.2.1⟩, fun a ha b hb h => ?_⟩
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hx_not_L (by simp [ha])
    · exact h1.2.2 a ha a hb' rfl
  have hord'_cyc : cycNext (ord' v) x = y ∧
      ∀ z ∈ ord v, cycNext (ord' v) z = if cycNext (ord v) z = y then x else cycNext (ord v) z := by
    obtain ⟨pre, suf, hsplit⟩ := List.mem_iff_append.mp hy_mem
    have hnoty : y ∉ pre := fun hm =>
      (List.nodup_append.mp (hsplit ▸ hc.nodup v)).2.2 y hm y List.mem_cons_self rfl
    have hord'_rot : (ord' v).IsRotated (pre ++ x :: y :: suf) := by
      unfold ord' applyOrdEdit
      simp only [Function.update_self, insertBeforeList]
      rcases hy_target with rfl | ⟨hnone, hhead⟩
      · have hidx : (ord v).idxOf y = pre.length := by
          rw [hsplit]; exact idxOf_append_cons_of_notMem hnoty
        dsimp only
        rw [hidx, hsplit, List.take_left, List.drop_left]
      · have hpre_nil : pre = [] := by
          cases pre with
          | nil => rfl
          | cons p ps =>
            rw [hsplit] at hhead
            exact absurd (Option.some.inj hhead ▸ List.mem_cons_self) hnoty
        subst hpre_nil
        simp only [List.nil_append] at hsplit ⊢
        rcases hnone with rfl | ⟨y', rfl, hy'⟩
        · dsimp only; rw [hsplit]; exact List.isRotated_append (l := y :: suf) (l' := [x])
        · have hidx : (ord v).idxOf y' = (ord v).length := idxOf_eq_length_of_notMem hy'
          dsimp only
          rw [hidx, List.take_length, List.drop_length, hsplit]
          exact List.isRotated_append (l := y :: suf) (l' := [x])
    have hnd_rot : (pre ++ x :: y :: suf).Nodup := hord'_rot.perm.nodup_iff.mp (hc'.nodup v)
    have hx_mem' : x ∈ ord' v := hord'_rot.perm.mem_iff.mpr (by simp)
    have hcx : cycNext (ord' v) x = y := by
      rw [← cycNext_isRotated (hc'.nodup v) hord'_rot hx_mem']
      have h1 : cycNext ((pre ++ [x]) ++ (y :: suf)) x = y :=
        cycNext_append_eq' (xs := pre ++ [x]) (ys := y :: suf)
          (by simpa [List.append_assoc] using hnd_rot) (by simp) rfl
      simpa [List.append_assoc] using h1
    refine ⟨hcx, fun z hz => ?_⟩
    have hz' : z ∈ ord' v := hord'_rot.perm.mem_iff.mpr (by
      rw [hsplit] at hz; simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto)
    have hrot_old : (ord v).IsRotated (y :: (suf ++ pre)) := by
      rw [hsplit]
      have := List.isRotated_append (l := pre) (l' := y :: suf)
      simpa [List.cons_append, List.append_assoc] using this
    have hrot_new : (pre ++ x :: y :: suf).IsRotated (x :: y :: (suf ++ pre)) := by
      have := List.isRotated_append (l := pre) (l' := x :: y :: suf)
      simpa [List.cons_append, List.append_assoc] using this
    have hz_rot : z ∈ pre ++ x :: y :: suf := hord'_rot.perm.mem_iff.mp hz'
    rw [← cycNext_isRotated (hc'.nodup v) hord'_rot hz',
      ← cycNext_isRotated hnd_rot hrot_new hz_rot,
      ← cycNext_isRotated (hc.nodup v) hrot_old hz]
    exact cycNext_cons_insert (hrot_new.perm.nodup_iff.mp hnd_rot) (hrot_old.perm.mem_iff.mp hz)
  have hsucc_x : eulerSucc ord' F x = y := by
    simp only [eulerSucc, hx_open, ↓reduceIte]
    have hx_mem' : x ∈ ord' v := by
      unfold ord' applyOrdEdit; simp only [Function.update_self, insertBeforeList]
      cases yOpt <;> simp
    rw [hc'.ordSrc_eq hx_mem']
    exact hord'_cyc.1
  have hsucc_other : ∀ z, z ∈ P ++ y :: Q →
      eulerSucc ord' F z = if eulerSucc ord F z = y then x else eulerSucc ord F z := by
    intro z hz
    obtain ⟨u, hzu, _⟩ := ((fullTour_spec hc v).2 z).mp (hrot.perm.mem_iff.mp hz)
    by_cases hzF : z.1 ∈ F.E
    · simp only [eulerSucc, hzF, ↓reduceIte]
      by_cases hdv : F.dst z = v
      · rw [hdv]
        have hfl_v : z.flip ∈ ord v := by
          rw [← hdv, ← src_flip_eq]; exact hc.mem_ord_of_forest (x := z.flip) hzF
        exact hord'_cyc.2 z.flip hfl_v
      · have hne_y : cycNext (ord (F.dst z)) z.flip ≠ y := by
          intro heq
          have hfl_mem : z.flip ∈ ord (F.dst z) := by
            rw [← src_flip_eq]; exact hc.mem_ord_of_forest (x := z.flip) hzF
          have hmem_next : cycNext (ord (F.dst z)) z.flip ∈ ord (F.dst z) := by
            obtain ⟨i, hi, hz_eq⟩ := List.getElem_of_mem hfl_mem
            rw [← hz_eq, cycNext_eq_getElem (hc.nodup _) hi]; exact List.getElem_mem _
          rw [heq] at hmem_next
          exact hdv (hc.unique (F.dst z) v y hmem_next hy_mem)
        rw [ite_eq_right_iff.mpr (fun h => absurd h hne_y)]
        simp [ord', applyOrdEdit, Function.update_of_ne hdv]
    · simp only [eulerSucc, hzF, ↓reduceIte]
      have hzu' : z ∈ ord' u := by
        unfold ord' applyOrdEdit
        by_cases huv : u = v
        · subst huv; simp only [Function.update_self, insertBeforeList]
          cases yOpt with
          | none => simp [hzu]
          | some y' =>
            have htd := List.take_append_drop ((ord u).idxOf y') (ord u)
            rw [← htd, List.mem_append] at hzu
            rcases hzu with h | h <;> simp [h]
        · simpa [Function.update_of_ne huv] using hzu
      rw [hc.ordSrc_eq hzu, hc'.ordSrc_eq hzu']
      by_cases huv : u = v
      · subst huv; exact hord'_cyc.2 z hzu
      · have hne_y : cycNext (ord u) z ≠ y := by
          intro heq
          have hmem_next : cycNext (ord u) z ∈ ord u := by
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzu
            rw [cycNext_eq_getElem (hc.nodup _) hi]; exact List.getElem_mem _
          rw [heq] at hmem_next
          exact huv (hc.unique u v y hmem_next hy_mem)
        rw [ite_eq_right_iff.mpr (fun h => absurd h hne_y)]
        simp [ord', applyOrdEdit, Function.update_of_ne huv]
  have hcyc_old : ∀ z ∈ P ++ y :: Q, cycNext (P ++ y :: Q) z = eulerSucc ord F z := fun z hz => by
    have hzr := hrot.perm.mem_iff.mp hz
    rw [cycNext_isRotated (fullTour_spec hc v).1 hrot.symm hzr, fullTour_cycNext hc v z hzr]
  have hcyc_new : ∀ z ∈ P ++ x :: y :: Q, cycNext (P ++ x :: y :: Q) z = eulerSucc ord' F z := by
    have hrot_o : (P ++ y :: Q).IsRotated (y :: (Q ++ P)) := by
      have := List.isRotated_append (l := P) (l' := y :: Q)
      simpa [List.cons_append, List.append_assoc] using this
    have hrot_n : (P ++ x :: y :: Q).IsRotated (x :: y :: (Q ++ P)) := by
      have := List.isRotated_append (l := P) (l' := x :: y :: Q)
      simpa [List.cons_append, List.append_assoc] using this
    have hnd_n : (x :: y :: (Q ++ P)).Nodup := hrot_n.perm.nodup_iff.mp hnd_new
    intro z hz
    rw [← cycNext_isRotated hnd_new hrot_n hz]
    by_cases hzx : z = x
    · subst z
      rw [hsucc_x]
      have := cycNext_eq_getElem hnd_n (i := 0) (by simp)
      have h1lt : 1 < (x :: y :: (Q ++ P)).length := by simp
      simpa only [Nat.zero_add, Nat.mod_eq_of_lt h1lt, List.getElem_cons_zero,
        List.getElem_cons_succ] using this
    · have hz_old : z ∈ P ++ y :: Q := by
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with h | rfl | h | h
        · exact Or.inl h
        · exact absurd rfl hzx
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rw [hsucc_other z hz_old, ← hcyc_old z hz_old, ← cycNext_isRotated hnd hrot_o hz_old]
      exact cycNext_cons_insert hnd_n (hrot_o.perm.mem_iff.mp hz_old)
  have hx_in : x ∈ fullTour ord' F hc'.forest v := by
    have hx_mem' : x ∈ ord' v := by
      unfold ord' applyOrdEdit; simp only [Function.update_self, insertBeforeList]
      cases yOpt <;> simp
    exact ((fullTour_spec hc' v).2 x).mpr ⟨v, hx_mem', connected_refl F v⟩
  exact isRotated_of_cycNext_eq hnd_new (fullTour_spec hc' v).1 (by simp) hx_in hcyc_new
    (fullTour_cycNext hc' v)

/-- Single-end open deletion surgery: deleting an open end `x` from `ord v` removes `x` from
`fullTour`. -/
theorem fullTour_dropOneOpen {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    {v : ℕ} {x : End} (hx_mem : x ∈ ord v) (hx_open : x.1 ∉ F.E)
    {P Q : List End}
    (hrot : (P ++ x :: Q).IsRotated (fullTour ord F hc.forest v)) :
    let ord' := Function.update ord v ((ord v).filter fun z => z != x)
    have hc' : OrdForestCompat ord' F := by
      refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hc.forest, fun u hu => ?_, fun e he => ?_⟩
      · by_cases huv : u = v
        · subst huv; simpa [ord'] using (hc.nodup u).filter _
        · simpa [ord', Function.update_of_ne huv] using hc.nodup u
      · have hsub_o : ∀ w z, z ∈ ord' w → z ∈ ord w := by
          intro w z hz
          by_cases hwv : w = v
          · subst hwv; simp only [ord', Function.update_self, List.mem_filter] at hz; exact hz.1
          · simpa [ord', Function.update_of_ne hwv] using hz
        exact hc.unique u₁ u₂ z (hsub_o u₁ z h1) (hsub_o u₂ z h2)
      · by_cases huv : u = v
        · exact huv ▸ hc.vert v (List.ne_nil_of_mem hx_mem)
        · exact hc.vert u (by simpa [ord', Function.update_of_ne huv] using hu)
      · have hne_t : (e, true) ≠ x := fun h => hx_open (h ▸ he)
        have hne_h : (e, false) ≠ x := fun h => hx_open (h ▸ he)
        have hmem_o : ∀ w z, z ∈ ord w → z ≠ x → z ∈ ord' w := by
          intro w z hz hzx
          by_cases hwv : w = v
          · subst hwv; simp [ord', hz, hzx]
          · simpa [ord', Function.update_of_ne hwv] using hz
        exact ⟨hmem_o _ _ (hc.forestEnd e he).1 hne_t, hmem_o _ _ (hc.forestEnd e he).2 hne_h⟩
    (P ++ Q).IsRotated (fullTour ord' F hc'.forest v) := by
  intro ord' hc'
  have hnd : (P ++ x :: Q).Nodup := hrot.perm.nodup_iff.mpr (fullTour_spec hc v).1
  cases hPQ : P ++ Q with
  | nil =>
    have hP0 : P = [] := (List.append_eq_nil_iff.mp hPQ).1
    have hQ0 : Q = [] := (List.append_eq_nil_iff.mp hPQ).2
    subst hP0; subst hQ0
    have hfull_eq : fullTour ord' F hc'.forest v = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      obtain ⟨u, hzu, hvu⟩ := ((fullTour_spec hc' v).2 z).mp hz
      have hzu0 : z ∈ ord u ∧ z ≠ x := by
        by_cases huv : u = v
        · subst huv; simpa [ord', List.mem_filter] using hzu
        · have hz0 : z ∈ ord u := by simpa [ord', Function.update_of_ne huv] using hzu
          exact ⟨hz0, fun h => huv (hc.unique u v x (h ▸ hz0) hx_mem)⟩
      have hz_old : z ∈ fullTour ord F hc.forest v :=
        ((fullTour_spec hc v).2 z).mpr ⟨u, hzu0.1, hvu⟩
      have := hrot.perm.mem_iff.mpr hz_old
      simp only [List.nil_append, List.mem_singleton] at this
      exact hzu0.2 this
    rw [hfull_eq]
  | cons a rest =>
    have h1 := List.nodup_append.mp hnd
    have h2 := List.nodup_cons.mp h1.2.1
    have hnd_PQ : (P ++ Q).Nodup :=
      List.nodup_append.mpr ⟨h1.1, h2.2, fun u hu w hw h => h1.2.2 u hu w (List.mem_cons_of_mem _ hw) h⟩
    have hx_nPQ : x ∉ P ++ Q := by
      simp only [List.mem_append, not_or]
      exact ⟨fun hm => h1.2.2 x hm x List.mem_cons_self rfl, h2.1⟩
    have hord'_cyc : ∀ z ∈ ord' v,
        cycNext (ord' v) z = if cycNext (ord v) z = x then cycNext (ord v) x else cycNext (ord v) z := by
      obtain ⟨pre, suf, hsplit⟩ := List.mem_iff_append.mp hx_mem
      have hnotx : x ∉ pre := fun hm =>
        (List.nodup_append.mp (hsplit ▸ hc.nodup v)).2.2 x hm x List.mem_cons_self rfl
      have hnotx_suf : x ∉ suf := (List.nodup_cons.mp (List.nodup_append.mp (hsplit ▸ hc.nodup v)).2.1).1
      have hord'_eq : ord' v = pre ++ suf := by
        simp only [ord', Function.update_self, hsplit, List.filter_append, List.filter_cons,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self.mpr (by intro w hw; simp [bne_iff_ne]; intro h; subst h; exact hnotx hw),
          List.filter_eq_self.mpr (by intro w hw; simp [bne_iff_ne]; intro h; subst h; exact hnotx_suf hw)]
      have hrot_o : (ord v).IsRotated (x :: (suf ++ pre)) := by
        rw [hsplit]
        have := List.isRotated_append (l := pre) (l' := x :: suf)
        simpa [List.cons_append, List.append_assoc] using this
      have hrot_n : (ord' v).IsRotated (suf ++ pre) := by rw [hord'_eq]; exact List.isRotated_append
      intro z hz
      have hz0 : z ∈ ord v := (by simpa [ord'] using hz : z ∈ ord v ∧ z ≠ x).1
      rw [← cycNext_isRotated (hc'.nodup v) hrot_n hz,
        ← cycNext_isRotated (hc.nodup v) hrot_o hz0,
        ← cycNext_isRotated (hc.nodup v) hrot_o hx_mem]
      exact cycNext_cons_delete (hrot_o.perm.nodup_iff.mp (hc.nodup v)) (hrot_n.perm.mem_iff.mp hz)
    have hsucc_eq : ∀ z ∈ P ++ Q,
        eulerSucc ord' F z = if eulerSucc ord F z = x then eulerSucc ord F x else eulerSucc ord F z := by
      intro z hz
      have hz_ne_x : z ≠ x := fun h => hx_nPQ (h ▸ hz)
      have hz_old : z ∈ P ++ x :: Q := by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
      obtain ⟨u, hzu, _⟩ := ((fullTour_spec hc v).2 z).mp (hrot.perm.mem_iff.mp hz_old)
      have hsucc_x : eulerSucc ord F x = cycNext (ord v) x := by
        simp only [eulerSucc, hx_open, ↓reduceIte, hc.ordSrc_eq hx_mem]
      rw [hsucc_x]
      by_cases hzF : z.1 ∈ F.E
      · simp only [eulerSucc, hzF, ↓reduceIte]
        by_cases hdv : F.dst z = v
        · rw [hdv]
          have hfl_v : z.flip ∈ ord v := by
            rw [← hdv, ← src_flip_eq]; exact hc.mem_ord_of_forest (x := z.flip) hzF
          have hfl_ne : z.flip ≠ x := fun h => hx_open (h ▸ hzF)
          exact hord'_cyc z.flip (by simp [ord', hfl_v, hfl_ne])
        · have hne_x : cycNext (ord (F.dst z)) z.flip ≠ x := by
            intro heq
            have hfl_mem : z.flip ∈ ord (F.dst z) := by
              rw [← src_flip_eq]; exact hc.mem_ord_of_forest (x := z.flip) hzF
            have hmem_next : cycNext (ord (F.dst z)) z.flip ∈ ord (F.dst z) := by
              obtain ⟨i, hi, hz_eq⟩ := List.getElem_of_mem hfl_mem
              rw [← hz_eq, cycNext_eq_getElem (hc.nodup _) hi]; exact List.getElem_mem _
            rw [heq] at hmem_next
            exact hdv (hc.unique (F.dst z) v x hmem_next hx_mem)
          rw [ite_eq_right_iff.mpr (fun h => absurd h hne_x)]
          simp [ord', Function.update_of_ne hdv]
      · simp only [eulerSucc, hzF, ↓reduceIte]
        have hzu' : z ∈ ord' u := by
          by_cases huv : u = v
          · subst huv; simp [ord', hzu, hz_ne_x]
          · simpa [ord', Function.update_of_ne huv] using hzu
        rw [hc.ordSrc_eq hzu, hc'.ordSrc_eq hzu']
        by_cases huv : u = v
        · subst huv; exact hord'_cyc z hzu'
        · have hne_x : cycNext (ord u) z ≠ x := by
            intro heq
            have hmem_next : cycNext (ord u) z ∈ ord u := by
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzu
              rw [cycNext_eq_getElem (hc.nodup _) hi]; exact List.getElem_mem _
            rw [heq] at hmem_next
            exact huv (hc.unique u v x hmem_next hx_mem)
          rw [ite_eq_right_iff.mpr (fun h => absurd h hne_x)]
          simp [ord', Function.update_of_ne huv]
    have hcyc_PQ : ∀ z ∈ P ++ Q, cycNext (P ++ Q) z = eulerSucc ord' F z := by
      have hrot_o : (P ++ x :: Q).IsRotated (x :: (Q ++ P)) := by
        have := List.isRotated_append (l := P) (l' := x :: Q)
        simpa [List.cons_append, List.append_assoc] using this
      have hrot_n : (P ++ Q).IsRotated (Q ++ P) := List.isRotated_append
      intro z hz
      have hz_old : z ∈ P ++ x :: Q := by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
      have hx_old : x ∈ P ++ x :: Q := by simp
      have hco_z : cycNext (P ++ x :: Q) z = eulerSucc ord F z := by
        have hzr := hrot.perm.mem_iff.mp hz_old
        rw [cycNext_isRotated (fullTour_spec hc v).1 hrot.symm hzr, fullTour_cycNext hc v z hzr]
      have hco_x : cycNext (P ++ x :: Q) x = eulerSucc ord F x := by
        have hxr := hrot.perm.mem_iff.mp hx_old
        rw [cycNext_isRotated (fullTour_spec hc v).1 hrot.symm hxr, fullTour_cycNext hc v x hxr]
      rw [hsucc_eq z hz, ← hco_z, ← hco_x,
        ← cycNext_isRotated hnd_PQ hrot_n hz,
        ← cycNext_isRotated hnd hrot_o hz_old,
        ← cycNext_isRotated hnd hrot_o hx_old]
      exact cycNext_cons_delete (hrot_o.perm.nodup_iff.mp hnd) (hrot_n.perm.mem_iff.mp hz)
    have ha_PQ : a ∈ P ++ Q := by rw [hPQ]; exact List.mem_cons_self
    have ha_ne_x : a ≠ x := fun h => hx_nPQ (h ▸ ha_PQ)
    have ha_old : a ∈ P ++ x :: Q := by simp only [List.mem_append, List.mem_cons] at ha_PQ ⊢; tauto
    obtain ⟨u, hau, hvu⟩ := ((fullTour_spec hc v).2 a).mp (hrot.perm.mem_iff.mp ha_old)
    have hau' : a ∈ ord' u := by
      by_cases huv : u = v
      · subst huv; simp [ord', hau, ha_ne_x]
      · simpa [ord', Function.update_of_ne huv] using hau
    have ha_in : a ∈ fullTour ord' F hc'.forest v :=
      ((fullTour_spec hc' v).2 a).mpr ⟨u, hau', hvu⟩
    rw [← hPQ]
    exact isRotated_of_cycNext_eq hnd_PQ (fullTour_spec hc' v).1 ha_PQ ha_in hcyc_PQ
      (fullTour_cycNext hc' v)

/-- Rotating `ord v` leaves every component's `fullTour` unchanged up to cyclic rotation. -/
theorem fullTour_rotateTo {ord : ℕ → List End} {F : MGraph} (hc : OrdForestCompat ord F)
    (v : ℕ) (y : End) (r : ℕ) :
    let ord' := applyOrdEdit ord (.rotateTo v y)
    have hc' : OrdForestCompat ord' F := by
      refine ⟨fun u => ?_, fun u₁ u₂ z h1 h2 => ?_, hc.forest, fun u hu => ?_, fun e he => ?_⟩
      · by_cases huv : u = v
        · subst huv
          simp only [ord', applyOrdEdit, Function.update_self]
          exact rotateToList_isRotated.perm.nodup_iff.mp (hc.nodup u)
        · simpa [ord', applyOrdEdit, Function.update_of_ne huv] using hc.nodup u
      · have hmem : ∀ w z, z ∈ ord' w ↔ z ∈ ord w := fun w z => by
          by_cases hwv : w = v
          · subst hwv
            simp only [ord', applyOrdEdit, Function.update_self]
            exact rotateToList_isRotated.perm.mem_iff.symm
          · simp [ord', applyOrdEdit, Function.update_of_ne hwv]
        exact hc.unique u₁ u₂ z ((hmem u₁ z).mp h1) ((hmem u₂ z).mp h2)
      · by_cases huv : u = v
        · subst huv
          apply hc.vert u
          intro h0; apply hu
          simp [ord', applyOrdEdit, rotateToList, h0]
        · exact hc.vert u (by simpa [ord', applyOrdEdit, Function.update_of_ne huv] using hu)
      · have hmem : ∀ w z, z ∈ ord w → z ∈ ord' w := fun w z hz => by
          by_cases hwv : w = v
          · subst hwv
            simp only [ord', applyOrdEdit, Function.update_self]
            exact rotateToList_isRotated.perm.mem_iff.mp hz
          · simpa [ord', applyOrdEdit, Function.update_of_ne hwv] using hz
        exact ⟨hmem _ _ (hc.forestEnd e he).1, hmem _ _ (hc.forestEnd e he).2⟩
    (fullTour ord F hc.forest r).IsRotated (fullTour ord' F hc'.forest r) := by
  intro ord' hc'
  have hmem : ∀ w z, z ∈ ord' w ↔ z ∈ ord w := fun w z => by
    by_cases hwv : w = v
    · subst hwv
      simp only [ord', applyOrdEdit, Function.update_self]
      exact rotateToList_isRotated.perm.mem_iff.symm
    · simp [ord', applyOrdEdit, Function.update_of_ne hwv]
  have hsucc : ∀ z, z ∈ fullTour ord F hc.forest r → eulerSucc ord' F z = eulerSucc ord F z := by
    intro z hz
    obtain ⟨u, hzu, _⟩ := ((fullTour_spec hc r).2 z).mp hz
    by_cases hzF : z.1 ∈ F.E
    · simp only [eulerSucc, hzF, ↓reduceIte]
      by_cases hdv : F.dst z = v
      · rw [hdv]
        have hfl : z.flip ∈ ord v := by
          rw [← hdv, ← src_flip_eq]; exact hc.mem_ord_of_forest (x := z.flip) hzF
        simp only [ord', applyOrdEdit, Function.update_self]
        exact cycNext_isRotated (hc.nodup v) rotateToList_isRotated hfl
      · simp [ord', applyOrdEdit, Function.update_of_ne hdv]
    · simp only [eulerSucc, hzF, ↓reduceIte, hc.ordSrc_eq hzu, hc'.ordSrc_eq ((hmem u z).mpr hzu)]
      by_cases huv : u = v
      · subst huv
        simp only [ord', applyOrdEdit, Function.update_self]
        exact cycNext_isRotated (hc.nodup u) rotateToList_isRotated hzu
      · simp [ord', applyOrdEdit, Function.update_of_ne huv]
  cases ho : fullTour ord F hc.forest r with
  | nil =>
    have hnil' : fullTour ord' F hc'.forest r = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro z hz
      obtain ⟨u, hzu, hru⟩ := ((fullTour_spec hc' r).2 z).mp hz
      have := ((fullTour_spec hc r).2 z).mpr ⟨u, (hmem u z).mp hzu, hru⟩
      rw [ho] at this; simp at this
    rw [hnil']
  | cons a rest =>
    have ha : a ∈ fullTour ord F hc.forest r := by rw [ho]; exact List.mem_cons_self
    obtain ⟨u, hau, hru⟩ := ((fullTour_spec hc r).2 a).mp ha
    have ha' : a ∈ fullTour ord' F hc'.forest r :=
      ((fullTour_spec hc' r).2 a).mpr ⟨u, (hmem u a).mpr hau, hru⟩
    rw [← ho]
    exact isRotated_of_cycNext_eq (fullTour_spec hc r).1 (fullTour_spec hc' r).1 ha ha'
      (fun z hz => (fullTour_cycNext hc r z hz).trans (hsucc z hz).symm)
      (fullTour_cycNext hc' r)

end MinCostFlow.SparseCore.Program
