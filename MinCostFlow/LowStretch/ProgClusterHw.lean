module

public import MinCostFlow.LowStretch.Segments

/-!
# The highway of a petal, from a path of super-vertices

The program knows the highway of a petal only as a path of super-vertices: the nodes `H[0], H[1],
…` of the tree of the first run of Dijkstra, from the super-vertex of the target to that of the
center. Between `H[k]` and `H[k+1]` it knows one pair `q_k`, with an end `a_k` in `H[k]` and an end
`b_k` in `H[k+1]`, along which the distance to the center drops by the length of `q_k`.

The highway of the petal metric is a walk of vertices. We build it (`hwB`) by putting a light walk
inside each super-vertex: from the target to `a_0`, from `b_0` to `a_1`, and so on, and from the
last `b` to the center. Light pairs have length `0` and keep the distance to the center, so this
walk is a highway (`hwB_highway`). Each of its steps either stays in one super-vertex or is one
of the pairs `q_k` (`hwB_steps`), and each `q_k` is one of its steps (`hwB_index`).

The portal of a petal is the first step that leaves it (`first_exit`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PG

variable (G : PG)

/-- The last vertex of the walk from `a` along `ps`. -/
def wend : ℕ → List ℕ → ℕ
  | a, [] => a
  | a, p :: ps => wend (G.other p a) ps

variable {G}

theorem vtx_getD_zero (a : ℕ) (ps : List ℕ) : (G.vtx a ps).getD 0 0 = a := by
  cases ps <;> rfl

theorem IsWalk.wend_eq {V P : Set ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) :
    G.wend a ps = b := by
  induction h with
  | nil _ => rfl
  | cons _ _ hj _ ih => simp only [wend, hj.other_eq, ih]

/-- The vertices of a walk along `ps ++ qs` after the first `ps.length` are those of the walk
along `qs` from the end of `ps`. -/
theorem vtx_append_getD (a : ℕ) (ps qs : List ℕ) (i : ℕ) :
    (G.vtx a (ps ++ qs)).getD (ps.length + i) 0 = (G.vtx (G.wend a ps) qs).getD i 0 := by
  induction ps generalizing a with
  | nil => simp [wend]
  | cons p ps ih =>
    rw [List.cons_append, vtx, List.length_cons, show ps.length + 1 + i = (ps.length + i) + 1 by omega,
      List.getD_cons_succ, ih]
    rfl

/-- The vertices of a walk along `ps ++ qs` up to `ps.length` are those of the walk along `ps`. -/
theorem vtx_append_getD_le (a : ℕ) (ps qs : List ℕ) {i : ℕ} (hi : i ≤ ps.length) :
    (G.vtx a (ps ++ qs)).getD i 0 = (G.vtx a ps).getD i 0 := by
  induction ps generalizing a i with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hi
    subst hi
    rw [List.nil_append, vtx_getD_zero, vtx_getD_zero]
  | cons p ps ih =>
    rw [List.cons_append, vtx, vtx]
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact ih _ (by simp at hi; omega)

end PG

namespace Cl

variable (G : PG) (c : Cl)

open Classical in
/-- A light walk from `u` to `v` inside `X`, when there is one. -/
noncomputable def lw (u v : ℕ) : List ℕ := if h : c.LConn G u v then Classical.choose h else []

variable {G c}

theorem lw_walk {u v : ℕ} (h : c.LConn G u v) : G.IsWalk ↑c.X (c.light G) u v (c.lw G u v) := by
  unfold lw
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (G c)

/-- The highway through the super-vertices: a light walk from `e` to `a_0`, the pair `q_0`, a light
walk from `b_0` to `a_1`, and so on, and a light walk from the last `b` to the center. Each step is
`(q, a, b)`. -/
noncomputable def hwB : ℕ → List (ℕ × ℕ × ℕ) → List ℕ
  | e, [] => c.lw G e c.x0
  | e, s :: st => c.lw G e s.2.1 ++ s.1 :: hwB s.2.2 st

/-- The steps fit: light walks between them and to the center, pairs that join their ends, and
the distance to the center drops by the length of each pair. -/
inductive StOk : ℕ → List (ℕ × ℕ × ℕ) → Prop
  | nil {e : ℕ} : c.LConn G e c.x0 → StOk e []
  | cons {e : ℕ} {s : ℕ × ℕ × ℕ} {st : List (ℕ × ℕ × ℕ)} : c.LConn G e s.2.1 →
      G.Joins s.1 s.2.1 s.2.2 → s.2.2 ∈ c.X →
      c.d G c.x0 s.2.1 = c.d G c.x0 s.2.2 + c.len G s.1 → StOk s.2.2 st → StOk e (s :: st)

variable {G c}

/-- The highway is a walk in `X` from `e` to the center. -/
theorem hwB_walk {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) :
    G.IsWalk ↑c.X Set.univ e c.x0 (c.hwB G e st) := by
  induction h with
  | nil hl => exact (lw_walk hl).mono le_rfl (Set.subset_univ _)
  | @cons e s st hl hj hb _ _ ih =>
    exact ((lw_walk hl).mono le_rfl (Set.subset_univ _)).append
      (.cons (lw_walk hl).end_mem (Set.mem_univ _) hj ih)

/-- A light pair inside `X` keeps the distance to the center and has length `0`. -/
theorem d_light (hc : c.Conn G) {p a b : ℕ} (hp : p ∈ c.light G) (hj : G.Joins p a b)
    (ha : a ∈ c.X) (hb : b ∈ c.X) : c.d G c.x0 a = c.d G c.x0 b + c.len G p := by
  have h0 : c.len G p = 0 := c.len_eq_zero_of_light hp
  have h1 := d_le_add_len hc hj ha hb
  have h2 := d_le_add_len hc hj.symm hb ha
  omega

/-- Along a light walk, every step keeps the distance, and its two ends are light-joined. -/
theorem light_steps (hc : c.Conn G) {u v : ℕ} {ps : List ℕ}
    (h : G.IsWalk ↑c.X (c.light G) u v ps) {i : ℕ} (hi : i < ps.length) :
    c.d G c.x0 ((G.vtx u ps).getD i 0) =
        c.d G c.x0 ((G.vtx u ps).getD (i + 1) 0) + c.len G (ps.getD i 0) ∧
      c.LConn G ((G.vtx u ps).getD i 0) ((G.vtx u ps).getD (i + 1) 0) := by
  have hj := h.joins_getD hi
  have ha := h.getD_mem (i := i) (by omega)
  have hb := h.getD_mem (i := i + 1) (by omega)
  have hp : ps.getD i 0 ∈ c.light G := h.pair_mem (by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
  exact ⟨d_light hc hp hj ha hb, ⟨[ps.getD i 0], .cons ha hp hj (.nil hb)⟩⟩

/-- **Each step of the highway** keeps the distance minus the length, and either joins two
light-joined vertices or is one of the given pairs, with its given ends. -/
theorem hwB_steps (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {i : ℕ}
    (hi : i < (c.hwB G e st).length) :
    c.d G c.x0 ((G.vtx e (c.hwB G e st)).getD i 0) =
        c.d G c.x0 ((G.vtx e (c.hwB G e st)).getD (i + 1) 0) +
          c.len G ((c.hwB G e st).getD i 0) ∧
      (c.LConn G ((G.vtx e (c.hwB G e st)).getD i 0) ((G.vtx e (c.hwB G e st)).getD (i + 1) 0) ∨
        ((c.hwB G e st).getD i 0, (G.vtx e (c.hwB G e st)).getD i 0,
          (G.vtx e (c.hwB G e st)).getD (i + 1) 0) ∈ st) := by
  induction h generalizing i with
  | nil hl =>
    have := light_steps hc (lw_walk hl) (i := i) hi
    exact ⟨this.1, Or.inl this.2⟩
  | @cons e s st hl hj hb hd hst ih =>
    have hw := lw_walk hl
    set l := c.lw G e s.2.1 with hlw
    have hend : G.wend e l = s.2.1 := hw.wend_eq
    simp only [hwB] at hi ⊢
    rw [← hlw] at hi ⊢
    rcases Nat.lt_or_ge i l.length with h1 | h1
    · rw [PG.vtx_append_getD_le _ _ _ (by omega), PG.vtx_append_getD_le _ _ _ (by omega),
        List.getD_append _ _ _ _ h1]
      have := light_steps hc hw h1
      exact ⟨this.1, Or.inl this.2⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = l.length + k := ⟨i - l.length, by omega⟩
      rw [PG.vtx_append_getD, show l.length + k + 1 = l.length + (k + 1) by omega,
        PG.vtx_append_getD, hend, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      cases k with
      | zero =>
        simp only [PG.vtx, List.getD_cons_zero, List.getD_cons_succ, hj.other_eq,
          PG.vtx_getD_zero]
        exact ⟨hd, Or.inr List.mem_cons_self⟩
      | succ k =>
        simp only [PG.vtx, List.getD_cons_succ, hj.other_eq]
        simp only [List.length_append, List.length_cons] at hi
        obtain ⟨h2, h3⟩ := ih (i := k) (by omega)
        refine ⟨h2, ?_⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (List.mem_cons_of_mem _ h3)

/-- **Each given pair is a step of the highway**, with its given ends. -/
theorem hwB_index {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {s : ℕ × ℕ × ℕ}
    (hs : s ∈ st) : ∃ i < (c.hwB G e st).length, (c.hwB G e st).getD i 0 = s.1 ∧
      (G.vtx e (c.hwB G e st)).getD i 0 = s.2.1 ∧
      (G.vtx e (c.hwB G e st)).getD (i + 1) 0 = s.2.2 := by
  induction h with
  | nil _ => simp at hs
  | @cons e s' st hl hj hb hd hst ih =>
    have hw := lw_walk hl
    set l := c.lw G e s'.2.1 with hlw
    have hend : G.wend e l = s'.2.1 := hw.wend_eq
    simp only [hwB]
    rw [← hlw]
    have key : ∀ k, k < (s'.1 :: c.hwB G s'.2.2 st).length →
        (l ++ s'.1 :: c.hwB G s'.2.2 st).getD (l.length + k) 0 =
            (s'.1 :: c.hwB G s'.2.2 st).getD k 0 ∧
          (G.vtx e (l ++ s'.1 :: c.hwB G s'.2.2 st)).getD (l.length + k) 0 =
            (G.vtx s'.2.1 (s'.1 :: c.hwB G s'.2.2 st)).getD k 0 ∧
          (G.vtx e (l ++ s'.1 :: c.hwB G s'.2.2 st)).getD (l.length + k + 1) 0 =
            (G.vtx s'.2.1 (s'.1 :: c.hwB G s'.2.2 st)).getD (k + 1) 0 := by
      intro k _
      refine ⟨List.getD_append_right _ _ _ _ (by omega) |>.trans (by rw [Nat.add_sub_cancel_left]),
        by rw [PG.vtx_append_getD, hend], ?_⟩
      rw [show l.length + k + 1 = l.length + (k + 1) by omega, PG.vtx_append_getD, hend]
    rcases List.mem_cons.mp hs with rfl | hs'
    · refine ⟨l.length, by simp, ?_⟩
      obtain ⟨k1, k2, k3⟩ := key 0 (by simp)
      rw [Nat.add_zero] at k1 k2 k3
      rw [k1, k2, k3]
      simp only [PG.vtx, List.getD_cons_zero, List.getD_cons_succ, hj.other_eq,
        PG.vtx_getD_zero]
      simp
    · obtain ⟨i, hi, e1, e2, e3⟩ := ih hs'
      refine ⟨l.length + (i + 1), by simp; omega, ?_⟩
      obtain ⟨k1, k2, k3⟩ := key (i + 1) (by simp; omega)
      rw [k1, k2, k3]
      simp only [PG.vtx, List.getD_cons_succ, hj.other_eq]
      exact ⟨e1, e2, e3⟩

/-- The highway built from the target is a highway of the petal metric. -/
theorem hwB_highway (hc : c.Conn G) {t : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G t st) :
    c.IsHighway G t (c.hwB G t st) :=
  ⟨hwB_walk h, fun i hi => (hwB_steps hc h hi).1⟩

end Cl

namespace PG

variable {G : PG}

/-- **The first exit.** A walk that starts in a set `W` and has a vertex outside `W` has a first
step that leaves `W`: all vertices up to number `i` lie in `W`, and vertex `i + 1` does not. -/
theorem first_exit (a : ℕ) (ps : List ℕ) (W : ℕ → Prop) (ha : W a)
    (hout : ∃ j ≤ ps.length, ¬ W ((G.vtx a ps).getD j 0)) :
    ∃ i < ps.length, (∀ k ≤ i, W ((G.vtx a ps).getD k 0)) ∧ ¬ W ((G.vtx a ps).getD (i + 1) 0) := by
  classical
  obtain ⟨j, hj, hnj⟩ := hout
  let n := Nat.find (p := fun j => j ≤ ps.length ∧ ¬ W ((G.vtx a ps).getD j 0)) ⟨j, hj, hnj⟩
  have hn : n ≤ ps.length ∧ ¬ W ((G.vtx a ps).getD n 0) := Nat.find_spec (p := fun j =>
    j ≤ ps.length ∧ ¬ W ((G.vtx a ps).getD j 0)) ⟨j, hj, hnj⟩
  have hmin : ∀ k < n, ¬ (k ≤ ps.length ∧ ¬ W ((G.vtx a ps).getD k 0)) := fun k hk =>
    Nat.find_min (p := fun j => j ≤ ps.length ∧ ¬ W ((G.vtx a ps).getD j 0)) ⟨j, hj, hnj⟩ hk
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, vtx_getD_zero] at hn
    exact hn.2 ha
  refine ⟨n - 1, by omega, fun k hk => ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hn.2⟩
  by_contra hw
  exact hmin k (by omega) ⟨by omega, hw⟩

end PG

end MinCostFlow.LowStretch
