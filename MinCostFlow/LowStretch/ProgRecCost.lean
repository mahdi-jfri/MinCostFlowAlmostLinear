module

public import MinCostFlow.LowStretch.ProgRecSpec

/-!
# The cost of one level of the recursion

The cluster procedure on `c` runs the body, the calls on the children and a few steps for each
child and for itself. This file shows that `recCost` of `c` pays for all of it, when `A` exceeds
the cost `K0` of these few steps.

* For a single vertex (`rec_leaf_cost`): the body costs at most `a (|S| + 1)`, and
  `recCost c ≥ ⌊2 a⌋ + a |S|` since the work is at least `1` (`Cl.Wk_one_le`).
* For a cluster with children (`rec_node_cost`): with `a = A · L`,
  `Σ_k recMain_k ≤ a (4 Σ_k Wk_k - 2 nch + 2 Σ_k hidW_k + Σ_k |S_k|)`. The work of the children
  is at most `Wk c - |act| - 1` (`Cl.Wk_step`), the splits of the children and their hidden
  parts are at most `hidW c` (`Cl.sum_vis_le`), and the body gives
  `Σ_k |S_k| ≤ |act| + Σ_k visW_k`. What is left of `recMain c` is at least `a (1 + nch) - 1`,
  which pays for the steps of the recursion. For the term with `kidCost`, the sizes of the
  children add up to `|X|` and there are at least two children, so
  `nch · kidCost + Σ_k 2 kidCost (2 |X_k| - 1) ≤ 2 kidCost (2 |X| - 1)`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par}

/-- The work of a cluster is at least `1`. -/
theorem Cl.Wk_one_le (hGo : G.Ok) {c : Cl} (hc : c.Inv G P) : 1 ≤ c.Wk G P := by
  have h1 : 1 ≤ c.X.card := Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
  have h2 : (1 : ℝ) ≤ c.X.card := by exact_mod_cast h1
  have h3 := gsum_nonneg (P := P) hGo c
  have h4 := inact_nonneg (G := G) (P := P) c
  have h5 := G0_ge (G := G) (P := P)
  have h6 : 0 ≤ G0 G P * inact G P c := mul_nonneg (by linarith) h4
  unfold Cl.Wk
  linarith

/-- `⌊a (4 Wk - 2)⌋ ≥ a (4 Wk - 2) - 1`, and the floor is at most its argument. -/
theorem floor_main (A L : ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ((A * L : ℕ) : ℝ) * (4 * W - 2) - 1 < (⌊((A * L : ℕ) : ℝ) * (4 * W - 2)⌋₊ : ℝ) ∧
      (⌊((A * L : ℕ) : ℝ) * (4 * W - 2)⌋₊ : ℝ) ≤ ((A * L : ℕ) : ℝ) * (4 * W - 2) := by
  have h0 : 0 ≤ ((A * L : ℕ) : ℝ) * (4 * W - 2) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  exact ⟨by linarith [Nat.lt_floor_add_one (((A * L : ℕ) : ℝ) * (4 * W - 2))], Nat.floor_le h0⟩

/-- **The cost of a single vertex.** -/
theorem rec_leaf_cost {w A K0 : ℕ} (hK : K0 ≤ A) (hL : 1 ≤ P.L) (hGo : G.Ok) {c : Cl} {R : Rec}
    (hc : c.Inv G P) :
    A * P.L * (R.S.length + 1) + K0 ≤ recCost w A T G P c R ∧
      K0 ≤ A * P.L := by
  have hW := Cl.Wk_one_le hGo hc
  have hAL : K0 ≤ A * P.L := hK.trans (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨?_, hAL⟩
  unfold recCost recMain
  obtain ⟨h1, -⟩ := floor_main A P.L _ hW
  have h2 : ((A * P.L : ℕ) : ℝ) * 2 ≤ ((A * P.L : ℕ) : ℝ) * (4 * c.Wk G P - 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have h3 : 2 * (A * P.L) ≤ ⌊((A * P.L : ℕ) : ℝ) * (4 * c.Wk G P - 2)⌋₊ := by
    have : ((2 * (A * P.L) : ℕ) : ℝ) < (⌊((A * P.L : ℕ) : ℝ) * (4 * c.Wk G P - 2)⌋₊ : ℝ) + 1 := by
      push_cast at h1 h2 ⊢; linarith
    exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
  have e : A * P.L * (R.S.length + 1) = A * P.L * R.S.length + A * P.L := by ring
  have e2 : A * P.L * (2 * T.hidW G c + R.S.length) =
      2 * (A * P.L * T.hidW G c) + A * P.L * R.S.length := by ring
  omega

/-- **The cost of a cluster with children.** -/
theorem rec_node_cost {w A K0 : ℕ} (hK : K0 + 1 ≤ A) {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl} {Rs : ℕ → Rec} (hok : R.Ok T G P c) (hcw : ∀ p, 1 ≤ P.cw p) (hL : 1 ≤ P.L)
    (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k))
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X)
    (hS : ∑ k ∈ Finset.range D.nch, (Rs k).S.length ≤
      (c.act G P).card + ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ) :
    bodyShare A T G P c R D cs + D.nch * kidCost w G.n +
      ∑ k ∈ Finset.range D.nch, recCost w A T G P (cs k) (Rs k) + K0 * (D.nch + 1) ≤
        recCost w A T G P c R := by
  classical
  have hGo := hok.hGo
  have hB := hok.hB
  have hc := hok.inv
  have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk => Cl.child_inv hGo hB hc hX hD hk (hn k hk)
  have hnch : 2 ≤ D.nch := by
    have := Cl.len_pos hB hc hX hD
    unfold Cl.Dec.nch; omega
  -- the sizes of the children
  have hcard : ∑ k ∈ Finset.range D.nch, (cs k).X.card = c.X.card := by
    rw [← Cl.sum_card_raw (G := G) (c := c) (D := D)]
    exact Finset.sum_congr rfl fun k hk => by rw [(hn k (Finset.mem_range.mp hk)).X_eq]
  have hpos : ∀ k < D.nch, 1 ≤ (cs k).X.card := fun k hk =>
    Finset.card_pos.mpr ⟨_, (hinv k hk).good.conn.1⟩
  have hsum1 : ∑ k ∈ Finset.range D.nch, (2 * (cs k).X.card - 1) + D.nch = 2 * c.X.card := by
    rw [← hcard, Finset.mul_sum]
    have : ∑ k ∈ Finset.range D.nch, (2 * (cs k).X.card - 1) + ∑ k ∈ Finset.range D.nch, 1 =
        ∑ k ∈ Finset.range D.nch, 2 * (cs k).X.card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k hk => by have := hpos k (Finset.mem_range.mp hk); omega
    simpa using this
  have hkid : D.nch * kidCost w G.n +
      ∑ k ∈ Finset.range D.nch, 2 * kidCost w G.n * (2 * (cs k).X.card - 1) ≤
      2 * kidCost w G.n * (2 * c.X.card - 1) := by
    rw [← Finset.mul_sum]
    have e : 2 * kidCost w G.n * (2 * c.X.card - 1) =
        2 * kidCost w G.n * (∑ k ∈ Finset.range D.nch, (2 * (cs k).X.card - 1)) +
          2 * kidCost w G.n * (D.nch - 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [e]
    have : D.nch * kidCost w G.n ≤ 2 * kidCost w G.n * (D.nch - 1) := by
      have : D.nch ≤ 2 * (D.nch - 1) := by omega
      calc D.nch * kidCost w G.n ≤ 2 * (D.nch - 1) * kidCost w G.n := Nat.mul_le_mul_right _ this
        _ = 2 * kidCost w G.n * (D.nch - 1) := by ring
    omega
  have hWk := Cl.Wk_step hGo hB hcw hc hX hD hn
  have hvis := Cl.sum_vis_le hok.tree hok.sub hc.one_le hn hsat
  have hmain : bodyShare A T G P c R D cs +
      ∑ k ∈ Finset.range D.nch, recMain A T G P (cs k) (Rs k) + K0 * (D.nch + 1) ≤
        recMain A T G P c R := by
    have hK0 : (K0 : ℝ) + 1 ≤ (A : ℝ) * P.L := by
      have : K0 + 1 ≤ A * P.L := hK.trans (Nat.le_mul_of_pos_right _ (by omega))
      exact_mod_cast this
    have ha0 : (0 : ℝ) ≤ (A : ℝ) * P.L := by positivity
    have hfl := fun k (hk : k < D.nch) => (floor_main A P.L _ (Cl.Wk_one_le hGo (hinv k hk))).2
    have hfc := (floor_main A P.L _ (Cl.Wk_one_le hGo hc)).1
    push_cast at hfl hfc
    have hR : (∑ k ∈ Finset.range D.nch, recMain A T G P (cs k) (Rs k) : ℝ) ≤
        ∑ k ∈ Finset.range D.nch, ((A : ℝ) * P.L * 4 * (cs k).Wk G P +
          (A : ℝ) * P.L * 2 * (T.hidW G (cs k) : ℝ) + (A : ℝ) * P.L * (Rs k).S.length -
          (A : ℝ) * P.L * 2) := by
      refine Finset.sum_le_sum fun k hk => ?_
      unfold recMain
      push_cast
      have := hfl k (Finset.mem_range.mp hk)
      linarith
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hR
    have hS' : (∑ k ∈ Finset.range D.nch, ((Rs k).S.length : ℝ)) ≤
        (c.act G P).card + ∑ k ∈ Finset.range D.nch, (T.visW G (c.raw G D k) (cs k).θ : ℝ) := by
      exact_mod_cast hS
    have hvis' : ∑ k ∈ Finset.range D.nch,
        ((T.visW G (c.raw G D k) (cs k).θ : ℝ) + T.hidW G (cs k)) ≤ T.hidW G c := by
      exact_mod_cast hvis
    rw [Finset.sum_add_distrib] at hvis'
    suffices h : (bodyShare A T G P c R D cs : ℝ) +
        ∑ k ∈ Finset.range D.nch, (recMain A T G P (cs k) (Rs k) : ℝ) + K0 * (D.nch + 1) <
          recMain A T G P c R + 1 by
      have : ((bodyShare A T G P c R D cs +
          ∑ k ∈ Finset.range D.nch, recMain A T G P (cs k) (Rs k) + K0 * (D.nch + 1) : ℕ) : ℝ) <
          ((recMain A T G P c R + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact Nat.lt_add_one_iff.mp (by exact_mod_cast this)
    have h1 : (A : ℝ) * P.L * 4 * ∑ k ∈ Finset.range D.nch, (cs k).Wk G P ≤
        (A : ℝ) * P.L * 4 * (c.Wk G P - (c.act G P).card - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (A : ℝ) * P.L * ∑ k ∈ Finset.range D.nch, ((Rs k).S.length : ℝ) ≤
        (A : ℝ) * P.L * ((c.act G P).card +
          ∑ k ∈ Finset.range D.nch, (T.visW G (c.raw G D k) (cs k).θ : ℝ)) :=
      mul_le_mul_of_nonneg_left hS' ha0
    have h3 : (A : ℝ) * P.L * (∑ k ∈ Finset.range D.nch, (T.visW G (c.raw G D k) (cs k).θ : ℝ) +
        ∑ k ∈ Finset.range D.nch, (T.hidW G (cs k) : ℝ)) ≤ (A : ℝ) * P.L * T.hidW G c :=
      mul_le_mul_of_nonneg_left hvis' ha0
    have h4 : (K0 : ℝ) * (D.nch + 1) + 1 ≤ (A : ℝ) * P.L * (D.nch + 1) := by
      have : (0 : ℝ) ≤ D.nch := Nat.cast_nonneg _
      nlinarith
    have h5 : (0 : ℝ) ≤ (A : ℝ) * P.L * (c.act G P).card := by positivity
    generalize (∑ k ∈ Finset.range D.nch, (recMain A T G P (cs k) (Rs k) : ℝ)) = RS at hR ⊢
    unfold bodyShare recMain
    push_cast
    linarith
  unfold recCost
  have e : ∑ k ∈ Finset.range D.nch,
      (recMain A T G P (cs k) (Rs k) + 2 * kidCost w G.n * (2 * (cs k).X.card - 1)) =
      ∑ k ∈ Finset.range D.nch, recMain A T G P (cs k) (Rs k) +
        ∑ k ∈ Finset.range D.nch, 2 * kidCost w G.n * (2 * (cs k).X.card - 1) :=
    Finset.sum_add_distrib
  rw [e]
  omega

end MinCostFlow.LowStretch
