module

public import MinCostFlow.LowStretch.Radius2
public import MinCostFlow.LowStretch.Volume3

/-!
# Tree distances and cut pairs

The stretch of a pair is its distance in the tree divided by its weight. At a cluster, every pair
with both ends in `X` either has both ends in one child, and is handled there, or is *cut*. A
cut pair has a walk in the tree through the center, of length at most a constant times the
radius `Δ` (`tdist_cut_le`). An active cut pair leaves one of the petals, so its weight `cw/ω` is
part of the cost of that petal (`cut_act_le`). The pairs inside the children and the cut pairs
are all the pairs inside `X`, each once (`sum_ins`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

theorem TW.symm {T : List ℕ} {a b l : ℕ} (h : TW G T a b l) : TW G T b a l :=
  let ⟨ps, hps, hle⟩ := h
  ⟨ps.reverse, hps.reverse, by rw [PG.wlen_reverse]; exact hle⟩

/-- The distance from `a` to `b` in the tree `T`, with lengths `ω / 2`. -/
noncomputable def PG.tdist (G : PG) (T : List ℕ) (a b : ℕ) : ℕ := sInf {l | TW G T a b l}

theorem tdist_le {T : List ℕ} {a b l : ℕ} (h : TW G T a b l) : G.tdist T a b ≤ l :=
  Nat.sInf_le h

theorem tw_tdist {T : List ℕ} {a b l : ℕ} (h : TW G T a b l) : TW G T a b (G.tdist T a b) :=
  Nat.sInf_mem (s := {l | TW G T a b l}) ⟨l, h⟩

theorem tdist_mono {T T' : List ℕ} {a b l : ℕ} (h : TW G T a b l) (hT : ∀ p ∈ T, p ∈ T') :
    G.tdist T' a b ≤ G.tdist T a b :=
  tdist_le ((tw_tdist h).mono hT le_rfl)

open Classical in
/-- The pairs with both ends in `X`. -/
noncomputable def PG.ins (G : PG) (X : Finset ℕ) : Finset ℕ :=
  (Finset.range G.m).filter fun p => G.pu p ∈ X ∧ G.pv p ∈ X

theorem PG.mem_ins {X : Finset ℕ} {p : ℕ} : p ∈ G.ins X ↔ p < G.m ∧ G.pu p ∈ X ∧ G.pv p ∈ X := by
  unfold PG.ins; simp

/-- A pair with both ends in `X` of a cluster of a run has a walk in the tree. -/
theorem RadOk.tw {c : Cl} {T : List ℕ} (h : RadOk G P c T) {p : ℕ} (hp : p ∈ G.ins c.X) :
    TW G T (G.pu p) (G.pv p) (2 * c.d G c.x0 (G.pu p) + P.A * c.X.card * c.θ +
      (2 * c.d G c.x0 (G.pv p) + P.A * c.X.card * c.θ)) := by
  obtain ⟨-, hu, hv⟩ := PG.mem_ins.mp hp
  exact (h.1 _ hu).symm.trans (h.1 _ hv)

namespace Cl

variable {c : Cl} {D : Dec}

/-- Every vertex of `X` lies in one of the pieces. -/
theorem exists_piece {z : ℕ} (hz : z ∈ c.X) : ∃ k < D.nch, z ∈ (c.raw G D k).X := by
  have h0 : z ∈ c.Z G D 0 := hz
  rcases (mem_Z_iff (Nat.zero_le _)).mp h0 with h | ⟨j, -, hj, h⟩
  · exact ⟨0, by unfold Dec.nch; omega, by rw [raw0_X]; exact h⟩
  · exact ⟨j + 1, by unfold Dec.nch; omega, by rw [rawP_X]; exact h⟩

open Classical in
variable (G c D) in
/-- The cut pairs: both ends in `X`, but not both in one piece. -/
noncomputable def cut : Finset ℕ :=
  (G.ins c.X).filter fun p => ¬ ∃ k < D.nch, Inside G (c.raw G D k).X p

theorem mem_Z_of {z : ℕ} (hz : z ∈ c.X) {k : ℕ} (h : ∀ j < k, z ∉ c.W G D j) : z ∈ c.Z G D k := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    rw [Z_succ]
    exact Finset.mem_sdiff.mpr ⟨ih fun j hj => h j (by omega), h k (by omega)⟩

/-- A cut pair leaves one of the petals. -/
theorem cut_leaves {p : ℕ} (hp : p ∈ c.cut G D) :
    ∃ k < D.ps.length, Leaves G (c.Z G D k) (c.W G D k) p := by
  classical
  unfold cut at hp
  obtain ⟨hpi, hno⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hu, hv⟩ := PG.mem_ins.mp hpi
  have hex : ∃ j, j < D.ps.length ∧ (G.pu p ∈ c.W G D j ∨ G.pv p ∈ c.W G D j) := by
    by_contra hne
    push Not at hne
    refine hno ⟨0, by unfold Dec.nch; omega, ?_⟩
    rw [raw0_X]
    exact ⟨mem_stem_of (k := 0) hu fun j _ hj => (hne j hj).1,
      mem_stem_of (k := 0) hv fun j _ hj => (hne j hj).2⟩
  have hk := Nat.find_spec hex
  set k := Nat.find hex
  have hmin : ∀ j < k, G.pu p ∉ c.W G D j ∧ G.pv p ∉ c.W G D j := by
    intro j hj
    have := Nat.find_min hex hj
    push Not at this
    exact this (by omega)
  have huZ := mem_Z_of hu fun j hj => (hmin j hj).1
  have hvZ := mem_Z_of hv fun j hj => (hmin j hj).2
  have hnot : ¬ (G.pu p ∈ c.W G D k ∧ G.pv p ∈ c.W G D k) := fun h =>
    hno ⟨k + 1, by unfold Dec.nch; omega, by rw [rawP_X]; exact h⟩
  refine ⟨k, hk.1, ?_⟩
  rcases hk.2 with h | h
  · exact Or.inl ⟨h, Finset.mem_sdiff.mpr ⟨hvZ, fun h' => hnot ⟨h, h'⟩⟩⟩
  · exact Or.inr ⟨h, Finset.mem_sdiff.mpr ⟨huZ, fun h' => hnot ⟨h', h⟩⟩⟩

/-- The active cut pairs have weight `cw / ω` at most the costs of the petals. -/
theorem cut_act_le :
    ∑ p ∈ c.cut G D ∩ c.act G P, (P.cw p : ℝ) / G.pω p ≤
      ∑ k ∈ Finset.range D.ps.length, c.cost G P (c.Z G D k) (D.pd k) := by
  classical
  unfold cost
  simp only
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have h1 : ∑ p ∈ c.cut G D ∩ c.act G P, (P.cw p : ℝ) / G.pω p ≤
      ∑ p ∈ c.act G P, if p ∈ c.cut G D then (P.cw p : ℝ) / G.pω p else 0 := by
    rw [← Finset.sum_filter]
    refine le_of_eq (Finset.sum_congr ?_ fun _ _ => rfl)
    ext p; simp [and_comm]
  refine h1.trans (Finset.sum_le_sum fun p _ => ?_)
  split_ifs with hp
  · obtain ⟨k, hk, hl⟩ := cut_leaves hp
    have : ∀ j ∈ Finset.range D.ps.length, 0 ≤
        (if Leaves G (c.Z G D j) (c.carve G (c.Z G D j) (D.pd j)) p then
          (P.cw p : ℝ) / G.pω p else 0) := fun j _ => by
      split_ifs <;> positivity
    have hle := Finset.single_le_sum this (Finset.mem_range.mpr hk)
    have hl' : Leaves G (c.Z G D k) (c.carve G (c.Z G D k) (D.pd k)) p := hl
    simp only [hl', ↓reduceIte] at hle
    exact hle
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- The pairs inside `X` are the pairs inside the pieces and the cut pairs, each once. -/
theorem sum_ins (f : ℕ → ℝ) :
    ∑ p ∈ G.ins c.X, f p =
      ∑ k ∈ Finset.range D.nch, ∑ p ∈ G.ins (c.raw G D k).X, f p + ∑ p ∈ c.cut G D, f p := by
  classical
  have hdisj : (Set.PairwiseDisjoint (↑(Finset.range D.nch)) fun k => G.ins (c.raw G D k).X) := by
    intro j hj k hk hjk
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpj hpk
    exact hjk (raw_eq_of_mem (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
      (PG.mem_ins.mp hpj).2.1 (PG.mem_ins.mp hpk).2.1)
  rw [← Finset.sum_biUnion hdisj]
  have hsplit : G.ins c.X = (Finset.range D.nch).biUnion (fun k => G.ins (c.raw G D k).X) ∪
      c.cut G D := by
    ext p
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, cut, Finset.mem_filter]
    constructor
    · intro hp
      by_cases h : ∃ k < D.nch, Inside G (c.raw G D k).X p
      · obtain ⟨k, hk, hi⟩ := h
        exact Or.inl ⟨k, hk, PG.mem_ins.mpr ⟨(PG.mem_ins.mp hp).1, hi⟩⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨k, -, hp⟩ | ⟨hp, -⟩)
      · obtain ⟨hm, hu, hv⟩ := PG.mem_ins.mp hp
        exact PG.mem_ins.mpr ⟨hm, raw_X_subset k hu, raw_X_subset k hv⟩
      · exact hp
  rw [hsplit, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro p hp hpc
  obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hp
  exact (Finset.mem_filter.mp hpc).2 ⟨k, Finset.mem_range.mp hk, (PG.mem_ins.mp hpk).2⟩

end Cl

end MinCostFlow.LowStretch
