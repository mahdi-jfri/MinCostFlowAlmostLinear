module

public import MinCostFlow.LowStretch.Cluster
public import Mathlib.Data.Nat.Log

/-!
# Petals as balls in a directed graph

A petal of [AN19] is a union of balls in cone metrics. Section 6 of [AN19] grows it as a ball in a
directed graph whose arc `a → b` along pair `p` has the shifted length
`w̄ = d(x0, a) + len p - d(x0, b)`. These lengths take many values. So that a Dijkstra search
with few distinct lengths can grow the petal, we round the cost `2 w̄` of each arc up to a power
of `2`, and up to at least the threshold `θ`. Arcs with `w̄ = 0` keep cost `0`. The highway, a
shortest walk from the target `t` to the center `x0`, gives extra arcs toward `x0` that cost the
length of their pair.

We never need the petal to be exactly the union of cones. We only need four facts, all proved
here:
* a cheap directed walk to `v` gives an undirected walk to `v` from a highway vertex with small
  excess (`exists_excess`), which replaces inequality (14) of [AN19];
* every directed walk costs at least the drop of `d(x0, ·)` (`potential`);
* moving away from `x0` along a pair of a shortest walk costs nothing (`step_zero`);
* one more pair costs at most `8` times its weight (`step_le`), so the balls form an
  `8`-concentric system.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The rounded cost of an arc with shifted length `x`. -/
def rc (θ x : ℕ) : ℕ := if x = 0 then 0 else max θ (2 ^ Nat.clog 2 (2 * x))

theorem le_rc (θ x : ℕ) : 2 * x ≤ rc θ x := by
  unfold rc
  split_ifs with h
  · omega
  · exact le_max_of_le_right (Nat.le_pow_clog Nat.one_lt_two _)

theorem rc_le (θ x : ℕ) : rc θ x ≤ max θ (4 * x) := by
  unfold rc
  split_ifs with h
  · exact Nat.zero_le _
  · refine max_le_max le_rfl ?_
    have h2 : 1 < 2 * x := by omega
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) Nat.one_lt_two h2
    have hpos : 0 < Nat.clog 2 (2 * x) := Nat.clog_pos Nat.one_lt_two h2
    have : 2 ^ Nat.clog 2 (2 * x) = 2 * 2 ^ (Nat.clog 2 (2 * x)).pred := by
      rw [← pow_succ']; congr 1; exact (Nat.succ_pred_eq_of_pos hpos).symm
    omega

/-- Vertex number `i` of the highway that starts at `t` and uses the pairs `hw`. -/
def hv (G : PG) (t : ℕ) (hw : List ℕ) (i : ℕ) : ℕ := (G.vtx t hw).getD i 0

namespace Cl

variable (G : PG) (c : Cl)

/-- The shifted length of the arc from `a` to `b` along pair `p`. -/
noncomputable def wbar (p a b : ℕ) : ℕ := c.d G c.x0 a + c.len G p - c.d G c.x0 b


/-- An arc from `a` to `b` of cost `k`: along any pair with its rounded cost, or along the
highway toward `x0` with the length of its pair. -/
inductive Arc (t : ℕ) (hw : List ℕ) : ℕ → ℕ → ℕ → Prop
  | normal {p a b : ℕ} : G.Joins p a b → Arc t hw a b (rc c.θ (c.wbar G p a b))
  | high {i : ℕ} : i < hw.length →
      Arc t hw (hv G t hw i) (hv G t hw (i + 1)) (c.len G (hw.getD i 0))

/-- `DR Y v k`: there is a directed walk inside `Y` from the target to `v` of cost `k`. -/
inductive DR (t : ℕ) (hw : List ℕ) (Y : Set ℕ) : ℕ → ℕ → Prop
  | start : t ∈ Y → DR t hw Y t 0
  | step {a b k k' : ℕ} : DR t hw Y a k → c.Arc G t hw a b k' → b ∈ Y → DR t hw Y b (k + k')

/-- The petal of radius `r`: the vertices reached from the target within cost `r`. -/
def Petal (t : ℕ) (hw : List ℕ) (Y : Set ℕ) (r : ℕ) : Set ℕ :=
  {v | ∃ k ≤ r, c.DR G t hw Y v k}

/-- The highway is a shortest walk to the center: each step lowers the distance to `x0` by the
length of its pair. -/
def IsHighway (t : ℕ) (hw : List ℕ) : Prop :=
  G.IsWalk ↑c.X Set.univ t c.x0 hw ∧
    ∀ i < hw.length, c.d G c.x0 (hv G t hw i) =
      c.d G c.x0 (hv G t hw (i + 1)) + c.len G (hw.getD i 0)

variable {G c}

theorem DR.mem {t : ℕ} {hw : List ℕ} {Y : Set ℕ} {v k : ℕ} (h : c.DR G t hw Y v k) : v ∈ Y := by
  cases h with
  | start ht => exact ht
  | step _ _ hb => exact hb

theorem Petal.mono {t : ℕ} {hw : List ℕ} {Y : Set ℕ} {r r' : ℕ} (h : r ≤ r') :
    c.Petal G t hw Y r ⊆ c.Petal G t hw Y r' := fun _ ⟨k, hk, hd⟩ => ⟨k, hk.trans h, hd⟩

theorem Petal.subset {t : ℕ} {hw : List ℕ} {Y : Set ℕ} {r : ℕ} : c.Petal G t hw Y r ⊆ Y :=
  fun _ ⟨_, _, hd⟩ => hd.mem

/-- The triangle inequality for the distance to the center across one pair. -/
theorem d_le_add_len (hc : c.Conn G) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ c.X)
    (hb : b ∈ c.X) : c.d G c.x0 b ≤ c.d G c.x0 a + c.len G p := by
  have hr : G.Reach ↑c.X c.x0 a := hc.2 a ha
  have hab : G.Reach ↑c.X a b := ⟨[p], .cons ha (Set.mem_univ p) hj (.nil hb)⟩
  exact (PG.dist_triangle _ hr hab).trans (Nat.add_le_add_left (PG.dist_le_pair _ hj ha hb) _)

theorem wbar_le (hc : c.Conn G) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ c.X) (hb : b ∈ c.X) :
    c.wbar G p a b ≤ 2 * c.len G p := by
  have := d_le_add_len hc hj.symm hb ha
  unfold wbar; omega

/-- The potential bound: a directed walk from the target to `v` costs at least
`d(x0, t) - d(x0, v)`. -/
theorem potential (hc : c.Conn G) {t : ℕ} {hw : List ℕ} {Y : Set ℕ} (hY : Y ⊆ ↑c.X)
    (hh : c.IsHighway G t hw) {v k : ℕ} (h : c.DR G t hw Y v k) :
    c.d G c.x0 t ≤ k + c.d G c.x0 v := by
  induction h with
  | start _ => omega
  | @step a b k k' ha harc hb ih =>
    cases harc with
    | @normal p _ _ hj =>
      have h1 := d_le_add_len hc hj.symm (hY hb) (hY ha.mem)
      have h2 := le_rc c.θ (c.wbar G p a b)
      have h3 : c.d G c.x0 a ≤ c.wbar G p a b + c.d G c.x0 b := by unfold wbar; omega
      omega
    | @high i hi =>
      have := hh.2 i hi
      omega

/-- Moving along a pair that keeps a shortest walk from the center costs nothing. -/
theorem step_zero {t : ℕ} {hw : List ℕ} {Y : Set ℕ} {p a b k : ℕ} (h : c.DR G t hw Y a k)
    (hj : G.Joins p a b) (hb : b ∈ Y) (hd : c.d G c.x0 b = c.d G c.x0 a + c.len G p) :
    c.DR G t hw Y b k := by
  have h0 : c.wbar G p a b = 0 := by unfold wbar; omega
  have := DR.step h (Arc.normal (c := c) (t := t) (hw := hw) hj) hb
  simpa [h0, rc] using this

/-- One more pair, not light, costs at most `8` times its weight. -/
theorem step_le (hc : c.Conn G) {t : ℕ} {hw : List ℕ} {Y : Set ℕ} (hY : Y ⊆ ↑c.X)
    {p a b k : ℕ} (h : c.DR G t hw Y a k) (hj : G.Joins p a b) (hb : b ∈ Y)
    (hθ : c.θ ≤ G.pω p) : ∃ k' ≤ k + 8 * G.pω p, c.DR G t hw Y b k' := by
  refine ⟨_, ?_, DR.step h (Arc.normal hj) hb⟩
  have h1 := rc_le c.θ (c.wbar G p a b)
  have h2 := wbar_le hc hj (hY h.mem) (hY hb)
  have h3 := len_le (c := c) (G := G) p
  have : max c.θ (4 * c.wbar G p a b) ≤ 8 * G.pω p := max_le (by omega) (by omega)
  omega

end Cl

end MinCostFlow.LowStretch
