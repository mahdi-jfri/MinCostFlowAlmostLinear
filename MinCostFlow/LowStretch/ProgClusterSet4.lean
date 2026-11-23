module

public import MinCostFlow.LowStretch.ProgClusterSet3

/-!
# The steps of a split highway

Facts about the steps of a split highway (`StOk`) that the setup needs to write the stored
highway over the tree of the first run: each step joins its two ends with the distance dropping
by its length (`StOk.step`), the last entry is light-joined to the center (`StOk.lconn_last`),
and when the steps have positive lengths the start of step `k` is `d(e)` minus the length of the
first `k` steps away from the center (`StOk.d_start`), so the starts have distinct distances.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- **Step `k`** joins its two ends, which lie in `X`, and the distance drops by its length. -/
theorem StOk.step {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {k : ℕ}
    (hk : k < st.length) :
    G.Joins (st.getD k (0, 0, 0)).1 (st.getD k (0, 0, 0)).2.1 (st.getD k (0, 0, 0)).2.2 ∧
      (st.getD k (0, 0, 0)).2.1 ∈ c.X ∧ (st.getD k (0, 0, 0)).2.2 ∈ c.X ∧
      c.d G c.x0 (st.getD k (0, 0, 0)).2.1 =
        c.d G c.x0 (st.getD k (0, 0, 0)).2.2 + c.len G (st.getD k (0, 0, 0)).1 := by
  induction h generalizing k with
  | nil _ => simp at hk
  | @cons e s st hl hj hb hd hst ih =>
    cases k with
    | zero =>
      simp only [List.getD_cons_zero]
      obtain ⟨ps, hps⟩ := hl
      exact ⟨hj, hps.end_mem, hb, hd⟩
    | succ k =>
      simp only [List.getD_cons_succ]
      exact ih (by simp at hk; omega)

/-- The last entry is light-joined to the center. -/
theorem StOk.lconn_last {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) :
    c.LConn G (stEnt e st st.length) c.x0 := by
  induction h with
  | nil hl => simpa [stEnt] using hl
  | @cons e s st hl hj hb hd hst ih =>
    simp only [stEnt, List.map_cons, List.length_cons, List.getD_cons_succ] at ih ⊢
    cases st with
    | nil => simpa using ih
    | cons s' st' => simpa using ih

/-- The distance of the start of step `k`. -/
theorem StOk.d_start (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {k : ℕ}
    (hk : k < st.length) :
    c.d G c.x0 e = c.d G c.x0 (st.getD k (0, 0, 0)).2.1 + hcL G c st k := by
  rw [h.d_ent hc hk.le, d_lconn hc (h.lconn_ent hk)]

/-- The length of the first `k + 1` steps. -/
theorem hcL_succ (st : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < st.length) :
    hcL G c st (k + 1) = hcL G c st k + c.len G (st.getD k (0, 0, 0)).1 := by
  unfold hcL
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem _ _ hk]
  simp

/-- With positive lengths, the length of the first `k` steps grows strictly with `k`. -/
theorem hcL_lt (st : List (ℕ × ℕ × ℕ)) (hpos : ∀ s ∈ st, 0 < c.len G s.1) {i j : ℕ} (hij : i < j)
    (hj : j ≤ st.length) : hcL G c st i < hcL G c st j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hjl : j < st.length := by omega
    rw [hcL_succ st hjl]
    have hp := hpos (st.getD j (0, 0, 0))
      (by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl)
    rcases Nat.lt_or_ge i j with h1 | h1
    · have := ih h1 (by omega); omega
    · have : i = j := by omega
      subst this; omega

/-- **The starts of the steps have distinct distances**, when the steps have positive length. -/
theorem StOk.d_start_inj (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st)
    (hpos : ∀ s ∈ st, 0 < c.len G s.1) {i j : ℕ} (hi : i < st.length) (hj : j < st.length)
    (he : c.d G c.x0 (st.getD i (0, 0, 0)).2.1 = c.d G c.x0 (st.getD j (0, 0, 0)).2.1) :
    i = j := by
  have h1 := h.d_start hc hi
  have h2 := h.d_start hc hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hcL_lt st hpos hlt hj.le; omega
  · have := hcL_lt st hpos hlt hi.le; omega

/-- The start of every step is farther from the center than the center. -/
theorem StOk.d_start_pos {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st)
    (hpos : ∀ s ∈ st, 0 < c.len G s.1) {k : ℕ} (hk : k < st.length) :
    0 < c.d G c.x0 (st.getD k (0, 0, 0)).2.1 := by
  have := (h.step hk).2.2.2
  have hp := hpos (st.getD k (0, 0, 0))
    (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  omega

end Cl

end MinCostFlow.LowStretch
