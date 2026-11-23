module

public import MinCostFlow.LowStretch.Asymp

/-!
# The mathematics of item 1

Every run from the first cluster of the pair graph gives a spanning tree with total stretch at most
`K · m · log(n + 2) · log(log(n + 2))` for `K = 4 · 1146265800` (`run_spec`), and such a run exists
(`exists_tree`). So every graph that the statement allows has such a tree (`lsst_math`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

variable {G : WGraph}

/-- The constant of the stretch bound. -/
def Kst : ℝ := 4 * 1146265800

/-- A spanning tree has at most `m` edges, so a connected graph has `n ≤ m + 1`. -/
theorem n_le_of_spanning {T : List ℕ} (h : G.IsSpanningTree T) : G.n ≤ G.m + 1 := by
  obtain ⟨hnd, hlt, hlen, -⟩ := h
  have : T.toFinset ⊆ Finset.range G.m := fun j hj =>
    Finset.mem_range.mpr (hlt j (List.mem_toFinset.mp hj))
  have h1 := Finset.card_le_card this
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at h1
  omega

/-- **Item 1.** Every run from the first cluster gives a spanning tree with small total
stretch. -/
theorem run_spec (h : Allowed G) {θ : ℕ} {T : List ℕ}
    (hc : (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m))
    (hr : Run (pgOf G) (par G.n G.m) (root (pgOf G) θ) T) :
    G.IsSpanningTree T ∧ G.totalStretch T ≤ Kst * G.m * logLogFactor G.n := by
  have hsp := spanning h hc hr
  refine ⟨hsp, ?_⟩
  have hLLF : 0 ≤ logLogFactor G.n := by
    have hℓ := ell_ge h.conn.1
    have := log_ell_ge h.conn.1
    unfold logLogFactor
    exact mul_nonneg (by unfold ell at hℓ; linarith) (by unfold ell at this; linarith)
  by_cases hm : G.m = 0
  · have : G.totalStretch T = 0 := by
      unfold WGraph.totalStretch
      have : IsEmpty (Fin G.m) := by rw [hm]; exact Fin.isEmpty'
      simp
    rw [this, hm]; simp
  have hm1 : 1 ≤ G.m := Nat.one_le_iff_ne_zero.mpr hm
  have hP := h.fit
  have h1 := stretch_le h hc hr
  have h2 := Run.stretch hP.ok hP.B hP.κ hP.Q hP.BL hr hc
  have h3 := pot_le h hc hm1 (n_le_of_spanning hsp)
  have h4 := Afac_le h
  have hmr : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
  have h5 : (G.m : ℝ) * Afac G ≤ G.m * (1146265800 * logLogFactor G.n) :=
    mul_le_mul_of_nonneg_left h4 hmr
  unfold Kst
  nlinarith

/-- A run from the first cluster exists. -/
theorem exists_tree (h : Allowed G) : ∃ θ T, (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m) ∧
    Run (pgOf G) (par G.n G.m) (root (pgOf G) θ) T := by
  have hP := h.fit
  obtain ⟨θ, hθ⟩ := exists_root hP.ok hP.B hP.ω (root_conn h.valid h.conn)
  obtain ⟨T, hT⟩ := exists_run hP (root (pgOf G) θ) hθ
  exact ⟨θ, T, hθ, hT⟩

/-- **The mathematics of [AN19] Theorem 1**: every graph that the statement allows has a
spanning tree with total stretch at most `K · m · log(n + 2) · log(log(n + 2))`. -/
theorem lsst_math : ∃ K : ℝ, ∀ G : WGraph, G.graph.IsValid → G.graph.IsLoopless →
    G.IsConnected → (∀ e ∈ G.edges, 1 ≤ e.2.2) →
      ∃ T, G.IsSpanningTree T ∧ G.totalStretch T ≤ K * G.m * logLogFactor G.n := by
  refine ⟨Kst, fun G hV hL hc hw => ?_⟩
  have h : Allowed G := ⟨hV, hL, hc, hw⟩
  obtain ⟨θ, T, hθ, hT⟩ := exists_tree h
  exact ⟨T, run_spec h hθ hT⟩

end MinCostFlow.LowStretch
