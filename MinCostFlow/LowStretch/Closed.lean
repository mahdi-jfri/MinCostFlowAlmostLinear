module

public import MinCostFlow.LowStretch.Step

/-!
# What is left is closed toward the center

This is Claim 1 of [AN19]. Call `Y ⊆ X` *closed* if, whenever `b ∈ Y` and a pair `p = {a, b}`
is tight (`d(x0, b) = d(x0, a) + len p`), also `a ∈ Y`. Then a shortest walk from the center to
any vertex of `Y` stays in `Y`. The whole cluster is closed, and carving a petal from a closed set
leaves a closed set: if `a` were in the petal, the petal would also take `b`, since moving along a
tight pair costs nothing (`Cl.step_zero`). So every set `Y_j` of a step is closed, and so is the
stem.

We also show the facts about the sets of a step that the later files use: they shrink, the petals
and the stem split `X`, and distances to the center inside a closed set that holds the center are
the same as in `X`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- A lower bound on distances from a potential: if no pair in `V` changes `φ` by more than its
length, then `φ` grows by at most the distance. -/
theorem PG.le_dist_of_pot {G : PG} {V : Set ℕ} {len : ℕ → ℕ} (φ : ℕ → ℕ)
    (hφ : ∀ p a b, G.Joins p a b → a ∈ V → b ∈ V → φ b ≤ φ a + len p) {a b : ℕ}
    (h : G.Reach V a b) : φ b ≤ φ a + G.dist V len a b := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist len h
  rw [← hl]
  clear hl h
  induction hps with
  | nil _ => simp
  | @cons x y z p ps hx _ hj rest ih =>
    have := hφ p x y hj hx rest.start_mem
    simp only [PG.wlen_cons]
    omega

namespace Cl

variable {G : PG} {P : Par} {c : Cl}

theorem mem_carve {Y : Finset ℕ} {pd : PD} {v : ℕ} :
    v ∈ c.carve G Y pd ↔ v ∈ Y ∧ v ∈ c.Petal G pd.tj pd.hw ↑Y pd.r := by
  simp [carve]

theorem carve_subset (Y : Finset ℕ) (pd : PD) : c.carve G Y pd ⊆ Y :=
  fun _ h => (mem_carve.mp h).1

variable (G c) in
/-- `Y` is closed toward the center along tight pairs. -/
def Closed (Y : Finset ℕ) : Prop :=
  Y ⊆ c.X ∧ ∀ p a b, G.Joins p a b → a ∈ c.X → b ∈ Y →
    c.d G c.x0 b = c.d G c.x0 a + c.len G p → a ∈ Y

theorem closed_X : c.Closed G c.X := ⟨subset_rfl, fun _ _ _ _ ha _ _ => ha⟩

/-- Carving a petal from a closed set leaves a closed set. -/
theorem Closed.sdiff {Y : Finset ℕ} (hY : c.Closed G Y) (pd : PD) :
    c.Closed G (Y \ c.carve G Y pd) := by
  refine ⟨fun x hx => hY.1 (Finset.mem_sdiff.mp hx).1, fun p a b hj ha hb hd => ?_⟩
  obtain ⟨hbY, hbW⟩ := Finset.mem_sdiff.mp hb
  have haY := hY.2 p a b hj ha hbY hd
  refine Finset.mem_sdiff.mpr ⟨haY, fun haW => hbW ?_⟩
  obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp haW
  exact mem_carve.mpr ⟨hbY, k, hk, step_zero hdr hj (by simpa using hbY) hd⟩

theorem closed_Z (D : Dec) (k : ℕ) : c.Closed G (c.Z G D k) := by
  induction k with
  | zero => exact closed_X
  | succ k ih => exact ih.sdiff _

theorem Z_succ (D : Dec) (k : ℕ) : c.Z G D (k + 1) = c.Z G D k \ c.W G D k := rfl

theorem Z_antitone (D : Dec) {j k : ℕ} (h : j ≤ k) : c.Z G D k ⊆ c.Z G D j := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (Finset.sdiff_subset).trans ih

theorem Z_subset_X (D : Dec) (k : ℕ) : c.Z G D k ⊆ c.X := (closed_Z D k).1

theorem W_subset (D : Dec) (k : ℕ) : c.W G D k ⊆ c.Z G D k := carve_subset _ _

/-- A shortest walk from a vertex of a closed set to the center stays in the set. -/
theorem Closed.walk {Y : Finset ℕ} (hY : c.Closed G Y) (hc : c.Conn G) {z : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c.X Set.univ z c.x0 ps) (hl : PG.wlen (c.len G) ps = c.d G c.x0 z)
    (hz : z ∈ Y) : G.IsWalk ↑Y Set.univ z c.x0 ps := by
  suffices key : ∀ w, G.IsWalk ↑c.X Set.univ z w ps → w = c.x0 →
      PG.wlen (c.len G) ps = c.d G c.x0 z → z ∈ Y → G.IsWalk ↑Y Set.univ z w ps from
    key _ hw rfl hl hz
  intro w hw
  induction hw with
  | nil _ => intro _ _ hz; exact .nil hz
  | @cons x y w p ps hx hp hj rest ih =>
    intro hwx hl hz
    subst hwx
    have hyX : y ∈ c.X := rest.start_mem
    have h1 : c.d G c.x0 y ≤ PG.wlen (c.len G) ps := by
      have := PG.dist_le (len := c.len G) rest.reverse
      rw [PG.wlen_reverse] at this; exact this
    have h2 := d_le_add_len hc hj.symm hyX hx
    simp only [PG.wlen_cons] at hl
    have hy : y ∈ Y := hY.2 p y x hj.symm hyX hz (by omega)
    refine .cons hz hp hj ?_
    apply ih
    all_goals first | exact rest | rfl | exact hy | omega

/-- Every vertex of a closed set is joined to the center by a shortest walk inside the set. -/
theorem Closed.exists_walk {Y : Finset ℕ} (hY : c.Closed G Y) (hc : c.Conn G) {z : ℕ}
    (hz : z ∈ Y) : ∃ ps, G.IsWalk ↑Y Set.univ c.x0 z ps ∧ PG.wlen (c.len G) ps = c.d G c.x0 z := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (c.len G) (hc.2 z (hY.1 hz))
  have hw : G.IsWalk ↑c.X Set.univ z c.x0 ps.reverse := hps.reverse
  have hl' : PG.wlen (c.len G) ps.reverse = c.d G c.x0 z := by rw [PG.wlen_reverse]; exact hl
  refine ⟨ps, ?_, hl⟩
  simpa using (hY.walk hc hw hl' hz).reverse

/-- Inside a closed set that holds the center, distances from the center are those of `X`. -/
theorem Closed.dist_eq {Y : Finset ℕ} (hY : c.Closed G Y) (hc : c.Conn G) {z : ℕ}
    (hz : z ∈ Y) : G.dist ↑Y (c.len G) c.x0 z = c.d G c.x0 z := by
  obtain ⟨ps, hps, hl⟩ := hY.exists_walk hc hz
  refine le_antisymm ((PG.dist_le hps).trans_eq hl) ?_
  exact PG.dist_mono (Finset.coe_subset.mpr hY.1) _ ⟨ps, hps⟩

/-- The highway of a closed set's vertex stays in the set: each step of a highway is tight. -/
theorem Closed.hv_mem {Y : Finset ℕ} (hY : c.Closed G Y) {t : ℕ} {hw : List ℕ}
    (hh : c.IsHighway G t hw) {i : ℕ} (hiY : hv G t hw i ∈ Y) :
    ∀ k, i ≤ k → k ≤ hw.length → hv G t hw k ∈ Y := by
  intro k hik hk
  induction k, hik using Nat.le_induction with
  | base => exact hiY
  | succ k hik ih =>
    have hjk : G.Joins (hw.getD k 0) (hv G t hw k) (hv G t hw (k + 1)) := hh.joins (by omega)
    exact hY.2 _ _ _ hjk.symm (hh.hv_mem (by omega)) (ih (by omega)) (hh.2 k (by omega))

end Cl

end MinCostFlow.LowStretch
