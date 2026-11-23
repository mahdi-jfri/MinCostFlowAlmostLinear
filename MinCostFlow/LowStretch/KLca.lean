module

public import MinCostFlow.LowStretch.KOrder

/-!
# The lowest common node by heavy paths

The program groups the pairs by the lowest node of the merge tree above both ends, since a pair
becomes visible exactly when this node is split. It finds the node by climbing heavy paths. Start
with the two ends `a` and `b`. While their heads differ, move the one with the smaller head to the
parent of its head. When the heads agree, the two nodes lie on one path, and the higher one is
the answer.

* `climb`: a step keeps every common node above both. The head with the smaller number cannot be
  above the other node, so the common nodes lie above its parent.
* `climb_sz`: a step at least doubles the leaves below the moved node, so there are few steps.
* `meet`: when the heads agree, the larger node is above both and below every common node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace KT

variable {T : KT} {G : PG}

/-- A node below `l` has a head of number at most the head of `l`. -/
theorem hd_le_of_under (h : T.Ok G) {b l : ℕ} (hb : b < T.N) (hu : T.Under b l) :
    T.hd G b ≤ T.hd G l := by
  have hlN := hu.lt_N h hb
  rcases Under.total (hd_under h b hb) hu with h1 | h1
  · exact (h1.le h ((hd_under h b hb).lt_N h hb)).trans
      ((hd_under h l hlN).le h hlN)
  · obtain ⟨i, rfl⟩ := hu
    rw [hd_path h hb i h1]

/-- **A step of the climb.** If the head of `a` has a smaller number than the head of `b`, it is
not the root, and every node `l` above both `a` and `b` is above the parent of that head. -/
theorem climb (h : T.Ok G) {a b l : ℕ} (ha : a < T.N) (hb : b < T.N) (hla : T.Under a l)
    (hlb : T.Under b l) (hlt : T.hd G a < T.hd G b) :
    T.hd G a + 1 < T.N ∧ T.Under (T.par (T.hd G a)) l := by
  have hbN : T.hd G b < T.N := (hd_under h b hb).lt_N h hb
  refine ⟨by omega, ?_⟩
  have hua := hd_under h a ha
  -- the head of `a` is not above `l`: otherwise `l` lies on the heavy path of `a`
  have hnot : ¬ T.Under l (T.hd G a) := by
    intro hl
    obtain ⟨i, rfl⟩ := hla
    have e := hd_path h ha i hl
    have := hd_le_of_under h hb hlb
    omega
  rcases Under.total hua hla with h1 | h1
  · refine h1.par_of_ne h fun e => hnot ?_
    rw [← e]; exact Under.refl _
  · exact absurd h1 hnot

/-- A step of the climb at least doubles the number of leaves. -/
theorem climb_sz (h : T.Ok G) {a : ℕ} (ha : a < T.N) (hr : T.hd G a + 1 < T.N) :
    2 * T.sz G a ≤ T.sz G (T.par (T.hd G a)) :=
  two_sz_le h ha hr

/-- After a step the moved node is still a node of the tree. -/
theorem climb_lt (h : T.Ok G) {a : ℕ} (ha : a < T.N) : T.par (T.hd G a) < T.N :=
  par_lt_N h ((hd_under h a ha).lt_N h ha)

/-- **The end of the climb.** When the heads agree, the larger of the two nodes is above both,
and below every node above both. -/
theorem meet (h : T.Ok G) {a b : ℕ} (ha : a < T.N) (hb : b < T.N)
    (he : T.hd G a = T.hd G b) :
    T.Under a (max a b) ∧ T.Under b (max a b) ∧
      ∀ l, T.Under a l → T.Under b l → T.Under (max a b) l := by
  rcases hd_eq h ha hb he with h1 | h1
  · have hle := h1.le h ha
    rw [max_eq_right hle]
    exact ⟨h1, Under.refl _, fun _ _ hl => hl⟩
  · have hle := h1.le h hb
    rw [max_eq_left hle]
    exact ⟨Under.refl _, h1, fun _ hl _ => hl⟩

/-- The logarithm of the number of leaves below a node is at most that of `n`. -/
theorem log_sz_le (k : ℕ) : Nat.log 2 (T.sz G k) ≤ Nat.log 2 G.n :=
  Nat.log_mono_right (sz_le_n k)

/-- Doubling the leaves raises the logarithm. -/
theorem log_sz_lt (h : T.Ok G) {a b : ℕ} (ha : a < T.N) (hd : 2 * T.sz G a ≤ T.sz G b) :
    Nat.log 2 (T.sz G a) < Nat.log 2 (T.sz G b) := by
  have h1 := sz_pos h ha
  have h2 : Nat.log 2 (2 * T.sz G a) ≤ Nat.log 2 (T.sz G b) := Nat.log_mono_right hd
  rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)] at h2
  omega

end KT

end MinCostFlow.LowStretch
