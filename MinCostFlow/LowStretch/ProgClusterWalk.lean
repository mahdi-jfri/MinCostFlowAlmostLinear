module

public import MinCostFlow.LowStretch.ProgClusterHw2
public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The stored form of a split highway

The child step reads the highway of each raw child in its stored form `hwE`: the pairs that are
not light, each with its flag and its two ends. When a highway is split into light walks and
steps (`HwDec`), its stored form is the list of the steps (`Cl.HwDec.hwE_eq`), and the stored
form of the part before a step `m` is the list of the first `m` steps (`Cl.HwDec.hwE_take`).

For the second fact we must know that position `i` of the highway is the position of step `m`.
The distance to the center does not grow along a highway and drops at each step, since a step
has positive length. So two different positions cannot both start a step at the same vertex.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

theorem hwE_nil (t θ : ℕ) (half : Finset ℕ) : hwE G t [] θ half = [] := by
  simp [hwE]

theorem hwE_cons (t p : ℕ) (hw : List ℕ) (θ : ℕ) (half : Finset ℕ) :
    hwE G t (p :: hw) θ half =
      (if θ ≤ G.pω p then [(p, if p ∈ half then 1 else 0, t, G.other p t)] else []) ++
        hwE G (G.other p t) hw θ half := by
  unfold hwE
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have e : ∀ m, hv G t (p :: hw) (m + 1) = hv G (G.other p t) hw m := fun m => by
    simp [hv, PG.vtx]
  have e0 : hv G t (p :: hw) 0 = t := by simp [hv, PG.vtx]
  have e1 : hv G t (p :: hw) 1 = G.other p t := by
    rw [e]; exact PG.vtx_getD_zero _ _
  have hf : (List.filter ((fun m => decide (θ ≤ G.pω ((p :: hw).getD m 0))) ∘ Nat.succ)
      (List.range hw.length)) = List.filter (fun m => decide (θ ≤ G.pω (hw.getD m 0)))
        (List.range hw.length) := by
    congr 1
  have hm : List.map ((fun m => ((p :: hw).getD m 0,
      if (p :: hw).getD m 0 ∈ half then 1 else 0, hv G t (p :: hw) m,
        hv G t (p :: hw) (m + 1))) ∘ Nat.succ) =
      List.map (fun m => (hw.getD m 0, if hw.getD m 0 ∈ half then 1 else 0,
        hv G (G.other p t) hw m, hv G (G.other p t) hw (m + 1))) := by
    congr 1
  by_cases h1 : θ ≤ G.pω p
  · rw [if_pos (by simpa using h1), if_pos h1, List.map_cons, List.map_map, hf, hm]
    simp only [List.getD_cons_zero, e0, zero_add, e1, List.singleton_append]
  · rw [if_neg (by simpa using h1), if_neg h1, List.map_map, hf, hm]; rfl

theorem hwE_append (t : ℕ) (l hw : List ℕ) (θ : ℕ) (half : Finset ℕ) :
    hwE G t (l ++ hw) θ half = hwE G t l θ half ++ hwE G (G.wend t l) hw θ half := by
  induction l generalizing t with
  | nil => simp [hwE_nil, PG.wend]
  | cons p l ih => rw [List.cons_append, hwE_cons, hwE_cons, ih]; simp [PG.wend]

theorem pairs_light {V : Set ℕ} {a b : ℕ} {l : List ℕ} (hl : G.IsWalk V (c.light G) a b l) :
    ∀ p ∈ l, G.pω p < c.θ := fun _ hp => hl.pair_mem hp

/-- A light walk has an empty stored form. -/
theorem hwE_light {V : Set ℕ} {a b : ℕ} {l : List ℕ} (hl : G.IsWalk V (c.light G) a b l)
    (half : Finset ℕ) : hwE G a l c.θ half = [] := by
  induction hl with
  | nil _ => exact hwE_nil _ _ _
  | cons _ hp hj _ ih =>
    rw [hwE_cons, if_neg (by have : G.pω _ < c.θ := hp; omega), hj.other_eq, ih]; rfl

/-- The stored form of a step. -/
def stE (half : Finset ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (s.1, if s.1 ∈ half then 1 else 0, s.2.1, s.2.2)

theorem nonlight_of_len {p : ℕ} (h : 0 < c.len G p) : c.θ ≤ G.pω p := by
  unfold len at h; split_ifs at h with h1 <;> omega

/-- **The stored form of a split highway** is the list of its steps. -/
theorem HwDec.hwE_eq {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} (h : c.HwDec G e st hw)
    (hpos : ∀ s ∈ st, 0 < c.len G s.1) (half : Finset ℕ) :
    hwE G e hw c.θ half = st.map (stE half) := by
  induction h with
  | nil hl => rw [hwE_light hl]; rfl
  | @cons e s st l hw hl hj hb hd hst ih =>
    rw [hwE_append, hwE_light hl, hl.wend_eq, hwE_cons,
      if_pos (nonlight_of_len (hpos s List.mem_cons_self)), hj.other_eq,
      ih fun s' hs' => hpos s' (List.mem_cons_of_mem _ hs')]
    rfl

/-- Along a highway the distance to the center does not grow. -/
theorem IsHighway.d_le {t : ℕ} {hw : List ℕ} (h : c.IsHighway G t hw) :
    ∀ j ≤ hw.length, c.d G c.x0 (hv G t hw j) ≤ c.d G c.x0 t := by
  intro j hj
  induction j with
  | zero => show c.d G c.x0 ((G.vtx t hw).getD 0 0) ≤ _; rw [PG.vtx_getD_zero]
  | succ j ih =>
    have := h.2 j (by omega)
    have := ih (by omega)
    omega

/-- **The stored form of the part before step `m`** is the list of the first `m` steps. -/
theorem HwDec.hwE_take (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
    (h : c.HwDec G e st hw) (hpos : ∀ s ∈ st, 0 < c.len G s.1) (half : Finset ℕ) {i m : ℕ}
    (hi : i < hw.length) (hm : m < st.length) (h1 : hw.getD i 0 = st[m].1)
    (h2 : hv G e hw i = st[m].2.1) :
    hwE G e (hw.take i) c.θ half = (st.take m).map (stE half) := by
  induction h generalizing i m with
  | nil _ => simp at hm
  | @cons e s st l hw hl hj hb hd hst ih =>
    have hend : G.wend e l = s.2.1 := hl.wend_eq
    have hps : 0 < c.len G s.1 := hpos s List.mem_cons_self
    have hpos' : ∀ s' ∈ st, 0 < c.len G s'.1 := fun s' hs' => hpos s' (List.mem_cons_of_mem _ hs')
    have hH := hst.highway hc
    have hm0 : c.θ ≤ G.pω (s :: st)[m].1 := nonlight_of_len (hpos _ (List.getElem_mem hm))
    simp only [List.length_append, List.length_cons] at hi
    rcases Nat.lt_trichotomy i l.length with hlt | heq | hgt
    · -- a position of the first light walk
      exfalso
      rw [List.getD_append _ _ _ _ hlt] at h1
      have := pairs_light hl (l.getD i 0)
        (by rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt)
      rw [h1] at this
      omega
    · subst heq
      cases m with
      | zero =>
        rw [List.take_left', hwE_light hl]
        · rfl
        · rfl
      | succ m =>
        exfalso
        have hv0 : hv G e (l ++ s.1 :: hw) l.length = s.2.1 := by
          unfold hv
          rw [show l.length = l.length + 0 by rfl, PG.vtx_append_getD, hend, PG.vtx_getD_zero]
        rw [hv0] at h2
        simp only [List.getElem_cons_succ] at h2 hm
        obtain ⟨j, hj', -, e2, -⟩ := hst.index (List.getElem_mem (by simpa using hm))
        have := hH.d_le j hj'.le
        unfold hv at this
        rw [e2, ← h2] at this
        omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = l.length + (i' + 1) := ⟨i - l.length - 1, by omega⟩
      have hvi : hv G e (l ++ s.1 :: hw) (l.length + (i' + 1)) = hv G s.2.2 hw i' := by
        unfold hv
        rw [PG.vtx_append_getD, hend]
        simp [PG.vtx, hj.other_eq]
      have hgi : (l ++ s.1 :: hw).getD (l.length + (i' + 1)) 0 = hw.getD i' 0 := by
        rw [List.getD_append_right _ _ _ _ (by omega), show l.length + (i' + 1) - l.length = i' + 1
          by omega]
        rfl
      rw [hvi] at h2
      rw [hgi] at h1
      cases m with
      | zero =>
        exfalso
        simp only [List.getElem_cons_zero] at h2
        have := hH.d_le i' (by omega)
        rw [h2] at this
        omega
      | succ m =>
        simp only [List.getElem_cons_succ] at h1 h2
        simp only [List.length_cons] at hm
        have := ih hpos' (i := i') (m := m) (by omega) (by omega) h1 h2
        rw [show l.length + (i' + 1) = l.length + (i' + 1) by rfl, List.take_append,
          List.take_of_length_le (by omega), show l.length + (i' + 1) - l.length = i' + 1 by omega,
          List.take_succ_cons, hwE_append, hwE_light hl, hend, hwE_cons,
          if_pos (nonlight_of_len hps), hj.other_eq, this]
        rfl

theorem wend_take (a : ℕ) (hw : List ℕ) :
    ∀ i ≤ hw.length, G.wend a (hw.take i) = hv G a hw i := by
  induction hw generalizing a with
  | nil => intro i hi; simp at hi; subst hi; simp [PG.wend, hv, PG.vtx]
  | cons p hw ih =>
    intro i hi
    cases i with
    | zero => simp [PG.wend, hv, PG.vtx]
    | succ i =>
      rw [List.take_succ_cons, PG.wend, ih _ i (by simpa using hi)]
      simp [hv, PG.vtx]

/-- **The stored form of the part after step `m`** is the list of the steps after `m`. -/
theorem HwDec.hwE_drop (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
    (h : c.HwDec G e st hw) (hpos : ∀ s ∈ st, 0 < c.len G s.1) (half : Finset ℕ) {i m : ℕ}
    (hi : i < hw.length) (hm : m < st.length) (h1 : hw.getD i 0 = st[m].1)
    (h2 : hv G e hw i = st[m].2.1) :
    hwE G (hv G e hw (i + 1)) (hw.drop (i + 1)) c.θ half = (st.drop (m + 1)).map (stE half) := by
  have hall := h.hwE_eq hpos half
  have htake := h.hwE_take hc hpos half hi hm h1 h2
  have hj := h.walk.joins_getD hi
  rw [← List.take_append_drop i hw, hwE_append, wend_take _ _ _ hi.le, htake,
    List.drop_eq_getElem_cons hi, hwE_cons,
    if_pos (by rw [← List.getD_eq_getElem _ _ hi, h1]
               exact nonlight_of_len (hpos _ (List.getElem_mem hm))),
    show G.other hw[i] (hv G e hw i) = hv G e hw (i + 1) by
      rw [← List.getD_eq_getElem _ _ hi]; exact hj.other_eq] at hall
  have hsplit : st.map (stE half) = (st.take m).map (stE half) ++
      (stE half st[m] :: (st.drop (m + 1)).map (stE half)) := by
    rw [← List.map_cons, ← List.drop_eq_getElem_cons hm, ← List.map_append, List.take_append_drop]
  rw [hsplit] at hall
  have := List.append_cancel_left hall
  simp only [List.singleton_append] at this
  exact (List.cons.inj this).2

end Cl

end MinCostFlow.LowStretch
