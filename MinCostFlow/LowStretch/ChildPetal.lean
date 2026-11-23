module

public import MinCostFlow.LowStretch.Children

/-!
# The petal children

Child `k + 1` of a step is petal `k`, with center `x' = h_i` (the last highway vertex before the
portal), target `t_k` and highway `h_0, …, h_i`. For a regular petal these highway pairs are
halved. By Claim 9 they were not halved before, so their length becomes exactly half, and the
highway is a shortest walk in the petal: its distances to `x'` are `(d(x0, h_m) - d(x0, x'))/2`
(for the special petal, without the factor `1/2`). Here `d` is the metric of the cluster.

From this and inequality (14) we get the two inequalities used for the radius of the tree, and
the bound `3Δ/4` on the radius of each petal (Claim 6 of [AN19]).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {P : Par} {c : Cl} {D : Dec}

section

variable (k : ℕ)

@[simp] theorem rawP_X : (c.raw G D (k + 1)).X = c.W G D k := rfl
@[simp] theorem rawP_x0 : (c.raw G D (k + 1)).x0 = D.xc G k := rfl
@[simp] theorem rawP_t : (c.raw G D (k + 1)).t = (D.pd k).tj := rfl
@[simp] theorem rawP_θ : (c.raw G D (k + 1)).θ = c.θ := rfl
@[simp] theorem rawP_hw : (c.raw G D (k + 1)).hw = (D.pd k).hw.take (D.pd k).i := rfl

theorem rawP_half :
    (c.raw G D (k + 1)).half = if D.sp = true ∧ k = 0 then c.half
      else c.half ∪ ((D.pd k).hw.take (D.pd k).i).toFinset := rfl

theorem half_subset_rawP : c.half ⊆ (c.raw G D (k + 1)).half := by
  rw [rawP_half]; split_ifs
  · exact subset_rfl
  · exact Finset.subset_union_left

theorem rawP_len_le (p : ℕ) : (c.raw G D (k + 1)).len G p ≤ c.len G p :=
  len_child_le (rawP_θ k) (half_subset_rawP k) p

theorem len_le_two_rawP (hGo : G.Ok) (p : ℕ) : c.len G p ≤ 2 * (c.raw G D (k + 1)).len G p :=
  len_le_two_child (rawP_θ k) hGo p

theorem rawP_len_sp (hs : D.sp = true ∧ k = 0) : (c.raw G D (k + 1)).len G = c.len G := by
  funext p
  unfold len
  rw [rawP_half, rawP_θ]
  simp only [hs, and_self, ↓reduceIte]

end

theorem seg_pair {hw : List ℕ} {j k p : ℕ} (hp : p ∈ (hw.drop j).take (k - j)) (hk : k ≤ hw.length) :
    ∃ m, j ≤ m ∧ m < k ∧ hw.getD m 0 = p := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
  simp only [List.length_take, List.length_drop] at hm
  refine ⟨j + m, by omega, by omega, ?_⟩
  rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem]

theorem wlen_congr {f g : ℕ → ℕ} {ps : List ℕ} (h : ∀ p ∈ ps, f p = g p) :
    PG.wlen f ps = PG.wlen g ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [PG.wlen_cons]
    rw [h p (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem wlen_two_eq {f g : ℕ → ℕ} {ps : List ℕ} (h : ∀ p ∈ ps, 2 * f p = g p) :
    2 * PG.wlen f ps = PG.wlen g ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [PG.wlen_cons, Nat.mul_add]
    rw [h p (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

section petal

variable (hG : c.Good G) (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length)
include hG hD hk

/-- Claim 9: a highway pair of a regular petal, if not light, was not halved before. -/
theorem not_half_reg (hs : ¬ (D.sp = true ∧ k = 0)) {m : ℕ} (hm : m < (D.pd k).i)
    (hθ : c.θ ≤ G.pω ((D.pd k).hw.getD m 0)) : (D.pd k).hw.getD m 0 ∉ c.half := by
  intro hp
  have hpk := petalOk hD hk
  have hj := hpk.2.1.joins (show m < (D.pd k).hw.length by have := hpk.2.2.1; omega)
  have hu : hv G (D.pd k).tj (D.pd k).hw m ∈ c.W G D k := hpk.2.2.2.1 m (by omega)
  have hv' : hv G (D.pd k).tj (D.pd k).hw (m + 1) ∈ c.W G D k := hpk.2.2.2.1 (m + 1) (by omega)
  have hpu : G.pu ((D.pd k).hw.getD m 0) ∈ c.X := by
    rcases hj.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact W_subset_X k (h1 ▸ hu)
    · exact W_subset_X k (h1 ▸ hv')
  have hpv : G.pv ((D.pd k).hw.getD m 0) ∈ c.X := by
    rcases hj.2 with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact W_subset_X k (h1 ▸ hv')
    · exact W_subset_X k (h1 ▸ hu)
  have hc := hG.half _ hp hj.1 hpu hpv hθ
  obtain ⟨m', hm', -, hj'⟩ := PG.ends_of_mem hG.high.1 hc
  rcases hj'.end_eq hj with h | h
  · exact hw_not_mem_reg hG.conn hG.high hD (m := m') (by omega) hk hs
      (by show (G.vtx c.t c.hw).getD m' 0 ∈ _; rw [h]; exact hu)
  · exact hw_not_mem_reg hG.conn hG.high hD (m := m') (by omega) hk hs
      (by show (G.vtx c.t c.hw).getD m' 0 ∈ _; rw [h]; exact hv')

/-- The highway pairs of a regular petal have exactly half their length in the petal. -/
theorem two_len_rawP (hGo : G.Ok) (hs : ¬ (D.sp = true ∧ k = 0)) {m : ℕ} (hm : m < (D.pd k).i) :
    2 * (c.raw G D (k + 1)).len G ((D.pd k).hw.getD m 0) = c.len G ((D.pd k).hw.getD m 0) := by
  by_cases hl : G.pω ((D.pd k).hw.getD m 0) < c.θ
  · rw [len_eq_zero_of_light hl, len_eq_zero_of_light (c := c.raw G D (k + 1)) (by simpa using hl)]
  · refine len_child_halved (rawP_θ k) hGo ?_ (not_half_reg hG hD hk hs hm (by omega))
    rw [rawP_half]
    simp only [hs, ↓reduceIte]
    refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have hil := (petalOk hD hk).2.2.1
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨m, by rw [List.length_take]; omega, by simp⟩

/-- The factor between the metric of the cluster and that of petal `k` along its highway:
`2` for a regular petal and `1` for the special one. -/
def fac (D : Dec) (k : ℕ) : ℕ := if D.sp = true ∧ k = 0 then 1 else 2

omit hG hD hk in
theorem fac_pos : 0 < fac D k := by unfold fac; split_ifs <;> omega

omit hG hD hk in
theorem fac_len (hGo : G.Ok) (p : ℕ) : c.len G p ≤ fac D k * (c.raw G D (k + 1)).len G p := by
  unfold fac
  split_ifs with hs
  · rw [rawP_len_sp k hs]; omega
  · exact len_le_two_rawP k hGo p

theorem fac_seg (hGo : G.Ok) {m : ℕ} (hm : m < (D.pd k).i) :
    fac D k * (c.raw G D (k + 1)).len G ((D.pd k).hw.getD m 0) =
      c.len G ((D.pd k).hw.getD m 0) := by
  unfold fac
  split_ifs with hs
  · rw [rawP_len_sp k hs]; omega
  · exact two_len_rawP hG hD hk hGo hs hm

omit hG in
/-- The highway of petal `k` up to `h_m`, reversed, is a walk in the petal from its center. -/
theorem seg_walk_rawP {m : ℕ} (hm : m ≤ (D.pd k).i) :
    G.IsWalk ↑(c.W G D k) Set.univ (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw m)
      ((((D.pd k).hw.drop m).take ((D.pd k).i - m)).reverse) := by
  have hpk := petalOk hD hk
  have hw := (hpk.2.1.seg_walk hm hpk.2.2.1.le).restrict (S := ↑(c.W G D k)) fun x hx => by
    obtain ⟨m', h1, h2, rfl⟩ := seg_vtx hm hpk.2.2.1.le hx
    exact hpk.2.2.2.1 m' h2
  exact hw.reverse

/-- Distances along the highway of a petal, in the metric of the petal. -/
theorem fac_d_hv (hGo : G.Ok) {m : ℕ} (hm : m ≤ (D.pd k).i) :
    fac D k * (c.raw G D (k + 1)).d G (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw m) +
      c.d G c.x0 (D.xc G k) = c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw m) := by
  have hpk := petalOk hD hk
  have hwk := seg_walk_rawP hD hk hm
  have hsl := hpk.2.1.seg_len hm hpk.2.2.1.le
  -- upper bound from the walk
  have hup : fac D k * (c.raw G D (k + 1)).d G (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw m) ≤
      PG.wlen (c.len G) (((D.pd k).hw.drop m).take ((D.pd k).i - m)) := by
    have h1 : (c.raw G D (k + 1)).d G (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw m) ≤
        PG.wlen ((c.raw G D (k + 1)).len G)
          ((((D.pd k).hw.drop m).take ((D.pd k).i - m)).reverse) := by
      unfold d; rw [rawP_X]; exact PG.dist_le hwk
    rw [PG.wlen_reverse] at h1
    have h2 : fac D k * PG.wlen ((c.raw G D (k + 1)).len G)
        (((D.pd k).hw.drop m).take ((D.pd k).i - m)) =
        PG.wlen (c.len G) (((D.pd k).hw.drop m).take ((D.pd k).i - m)) := by
      rw [← PG.wlen_mul]
      refine wlen_congr fun p hp => ?_
      obtain ⟨m', h1, h2, rfl⟩ := seg_pair hp hpk.2.2.1.le
      exact fac_seg hG hD hk hGo h2
    calc _ ≤ fac D k * PG.wlen ((c.raw G D (k + 1)).len G)
          (((D.pd k).hw.drop m).take ((D.pd k).i - m)) := Nat.mul_le_mul_left _ h1
      _ = _ := h2
  -- lower bound from the potential
  have hlow := pot_child (c' := c.raw G D (k + 1)) hG.conn (by rw [rawP_X]; exact W_subset_X k)
    (fac_len hGo) (a := D.xc G k) (b := hv G (D.pd k).tj (D.pd k).hw m)
    (by rw [rawP_X]; exact ⟨_, hwk⟩)
  unfold Dec.xc at hup hlow ⊢
  omega

end petal

end Cl

end MinCostFlow.LowStretch
