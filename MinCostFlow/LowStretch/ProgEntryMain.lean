module

public import MinCostFlow.LowStretch.ProgEntry

/-!
# The statement from the contract of the cluster procedure

Let `p` be a program with the entry `entryB bCl` at index `0` and the procedures `preProcs 1`
after it. If the procedure at `bCl` meets the contract `clC` of the first cluster for every word
size, graph and merge tree, then `p` meets the statement of `Cited.LowStretchSpanningTree`, with
word size constant `340 + A` (`lowStretch_of_cl`). With the cluster procedure,
`lowStretchSpanningTree_of_cl` gives the statement.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The explicit stretch and running-time constant of `lowStretch_of_cl_explicit` for body
constant `A`. -/
def lowStretchConst (A : ℕ) : ℝ := Kst + (800000000 + 250000 * A)

/-- **The statement for the entry with explicit constant**, with the contract of the cluster
procedure as a hypothesis. -/
theorem lowStretch_of_cl_explicit {p : Program} {A bCl : ℕ}
    (hp : p.HasAt 0 (entryB bCl :: preProcs 1))
    (hCl : ∀ w G T, MeetsContract w p bCl (clC w A G T)) :
    ∀ G : WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
      (∀ e ∈ G.edges, 1 ≤ e.2.2) → ∀ ω, ∃ out cost,
        RunsTo (wordSize (340 + A) G.encode) p G.encode ω out cost ∧ G.IsSpanningTree out ∧
        G.totalStretch out ≤ lowStretchConst A * G.m * logLogFactor G.n ∧
        (cost : ℝ) ≤ lowStretchConst A * (G.m + 1) *
          (logLogFactor G.n + weightFactor G.n G.maxWeight) := by
  intro G hv hl hc hw ω
  unfold lowStretchConst
  have h : Allowed G := ⟨hv, hl, hc, hw⟩
  obtain ⟨o, st, c, hrun, ⟨Tr, rfl, hList, hsp, hst⟩, hcost⟩ := entry_run hp hCl h ω
  have hn := h.conn.1
  have hℓ := ell_ge hn
  have hlℓ := log_ell_ge hn
  have hLLF : 0 ≤ logLogFactor G.n := by
    have : logLogFactor G.n = ell G.n * Real.log (ell G.n) := rfl
    rw [this]; exact mul_nonneg (by linarith) (by linarith)
  have hKst : (0 : ℝ) ≤ 800000000 + 250000 * A := by positivity
  refine ⟨Tr, c + 2, runsTo_of_entry hp.head (length_lt_two_pow_wordSize (by omega) _) hrun
    rfl hList, hsp, ?_, ?_⟩
  · have hm : (0 : ℝ) ≤ G.m * logLogFactor G.n := mul_nonneg (Nat.cast_nonneg _) hLLF
    calc G.totalStretch Tr ≤ Kst * G.m * logLogFactor G.n := hst
      _ ≤ (Kst + (800000000 + 250000 * A)) * G.m * logLogFactor G.n := by nlinarith
  · have hc := entry_cost_le A h
    have hc' : ((c + 2 : ℕ) : ℝ) ≤ preCost G + clB A G +
        4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n + 30 * G.m + 17 * G.n + 1500 := by
      exact_mod_cast (by omega : c + 2 ≤ preCost G + clB A G +
        4 * G.n * kidCost (wordSize (340 + A) G.encode) G.n + 30 * G.m + 17 * G.n + 1500)
    have hWF : 0 ≤ weightFactor G.n G.maxWeight := by
      have : weightFactor G.n G.maxWeight =
          ell G.n * Real.log (Real.log ((G.maxWeight : ℝ) + 2) + 2) := rfl
      rw [this]
      have : (0 : ℝ) ≤ Real.log ((G.maxWeight : ℝ) + 2) :=
        Real.log_nonneg (by linarith [(Nat.cast_nonneg G.maxWeight : (0 : ℝ) ≤ G.maxWeight)])
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    have hpos : (0 : ℝ) ≤ (G.m + 1) * (logLogFactor G.n + weightFactor G.n G.maxWeight) := by
      positivity
    have hKs : (0 : ℝ) ≤ Kst := by unfold Kst; norm_num
    calc ((c + 2 : ℕ) : ℝ) ≤ (800000000 + 250000 * A) * (G.m + 1) *
          (logLogFactor G.n + weightFactor G.n G.maxWeight) := hc'.trans hc
      _ ≤ _ := by nlinarith

/-- **The statement for the entry**, with the contract of the cluster procedure as a
hypothesis. -/
theorem lowStretch_of_cl {p : Program} {A bCl : ℕ} (hp : p.HasAt 0 (entryB bCl :: preProcs 1))
    (hCl : ∀ w G T, MeetsContract w p bCl (clC w A G T)) :
    ∃ K : ℝ, ∀ G : WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
      (∀ e ∈ G.edges, 1 ≤ e.2.2) → ∀ ω, ∃ out cost,
        RunsTo (wordSize (340 + A) G.encode) p G.encode ω out cost ∧ G.IsSpanningTree out ∧
        G.totalStretch out ≤ K * G.m * logLogFactor G.n ∧
        (cost : ℝ) ≤ K * (G.m + 1) * (logLogFactor G.n + weightFactor G.n G.maxWeight) :=
  ⟨lowStretchConst A, lowStretch_of_cl_explicit hp hCl⟩

/-- **[AN19] Theorem 1** from a cluster procedure that meets the contract of the first
cluster. -/
theorem lowStretchSpanningTree_of_cl
    (h : ∃ (p : Program) (A bCl : ℕ), p.HasAt 0 (entryB bCl :: preProcs 1) ∧
      ∀ w G T, MeetsContract w p bCl (clC w A G T)) :
    LowStretchSpanningTree := by
  obtain ⟨p, A, bCl, hp, hCl⟩ := h
  obtain ⟨K, hK⟩ := lowStretch_of_cl hp hCl
  exact ⟨p, 340 + A, K, hK⟩

end MinCostFlow.LowStretch
