module

public import MinCostFlow.LowStretch.ProgPreIn
public import MinCostFlow.LowStretch.ProgParams
public import MinCostFlow.LowStretch.ProgRound

/-!
# The preprocessing, part 1: the constants and the rounded weights

`wP` finds the largest weight `W` (`maxwP`), writes the six constants `parVal n m` at `PAR`
(`parP`), and then the exponent `⌊log₂ w⌋ + σ` of each rounded weight at `EXP` and the rounded
weight at `PW` (`rndP`), where `σ = pσ n` is read back from `PAR + 3`. So `PW` holds the weights
of the pair graph `pgOf G` (`wP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- `wP` with `args = [n, m]`; `maxwP`, `parP` and `rndP` sit at `bM`, `bP` and `bR`. -/
def wP (bM bP bR : ℕ) : Stmt :=
  .seq (.call 2 bM [.reg 1, .const 2])
  (.seq (.call 3 bP [.reg 0, .reg 1, lin 2 3 0])
  (.seq (.assign 3 (.load (lin 5 3 0)))
  (.seq (.call 4 bR [.reg 1, .reg 3, .const 2, lin 8 3 0, lin 8 4 0, .reg 2])
  (.ret (.const 0)))))

theorem wP_noRand (bM bP bR : ℕ) : (wP bM bP bR).NoRand := by
  simp [wP, lin, Stmt.NoRand]

/-- The cost of `wP`. -/
def wCost (G : WGraph) : ℕ := 1000 * (G.n + 9) + G.m * (log2Cost G.maxWeight + 110) + 100

/-- The contract of `wP` for the graph `G`. -/
def wC (w : ℕ) (G : WGraph) : Contract where
  pre args mem := args = [G.n, G.m] ∧ InG w G mem
  post _ mem _ mem' := (∀ i < 6, mem' (aPAR G.n G.m + i) = parVal G.n G.m i) ∧
    (∀ p < G.m, mem' (aEXP G.n G.m + p) = Nat.log 2 (wtOf G p) + pσ G.n ∧
      mem' (aPW G.n G.m + p) = (pgOf G).pω p) ∧
    ∀ a, (a < aPAR G.n G.m ∨ aTLK G.n G.m ≤ a) → mem' a = mem a
  cost _ _ := wCost G

theorem pσ_le (n : ℕ) (hn : 1 ≤ n) : pσ n ≤ 2 ^ 16 * (n + 4) ^ 4 := by
  have h1 : 1 ≤ 8 * pB n * n := by
    have : 0 < pB n := by unfold pB pL; positivity
    nlinarith
  have h2 := Nat.log_lt_self 2 (show 8 * pB n * n ≠ 0 by omega)
  have h3 := pB_le_poly n
  have h4 : 8 * pB n * n ≤ 8 * (64 * (n + 4) ^ 2) * (n + 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 8 h3) (by omega)
  have h5 : 8 * (64 * (n + 4) ^ 2) * (n + 4) ≤ 2 ^ 16 * (n + 4) ^ 4 := by
    have : 1 ≤ (n + 4) := by omega
    have : (n + 4) ^ 3 ≤ (n + 4) ^ 4 := Nat.pow_le_pow_right this (by norm_num)
    nlinarith
  unfold pσ; omega

theorem wP_spec {w : ℕ} {p : Program} {b bM bP bR : ℕ} (hp : p.HasAt b [wP bM bP bR])
    (hM : MeetsContract w p bM (maxwC w)) (hP : MeetsContract w p bP (parC w))
    (hR : MeetsContract w p bR (rndC w)) (G : WGraph) : MeetsContract w p b (wC w G) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hG⟩ := hpre
  have hproc : p.procs[b]? = some (wP bM bP bR) := hp 0 (by simp)
  refine ⟨wP bM bP bR, hproc, ?_⟩
  have hw := hG.add_lt
  have hn1 := hG.one_le
  have hw2 := hG.two_le_w
  have hpar := hG.par_lt
  simp only [aH] at hw
  dsimp only [wP, lin]
  refine runs_start_le ?_
  wram_step
  · refine ⟨G.m, 2, rfl, by omega, fun j hj => ?_⟩
    show mem (2 + 3 * j + 2) < 2 ^ w
    rw [hG.wt j hj]
    have := hG.wt_mul_lt hj
    have : wtOf G j ≤ wtOf G j * 2 ^ pσ G.n := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  intro W mem1 pos1 h1
  obtain ⟨rfl, hW1, hW2⟩ := h1
  wram_step
  · exact ⟨G.n, G.m, aPAR G.n G.m, by simp [aPAR], hn1, hpar, by omega, by unfold aPAR; omega⟩
  intro v2 mem2 pos2 h2
  obtain ⟨h2a, h2b⟩ := h2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h2a h2b hW1 hW2
  have hσ : mem2 (2 + 3 * G.m + 0 * G.n + 3) = pσ G.n := h2a 3 (by norm_num)
  have hin : ∀ a < 2 + 3 * G.m, mem2 a = mem1 a := fun a ha => h2b a (Or.inl (by omega))
  have hG2 := hG.frame hin
  have hσ' : mem2 (5 + 3 * G.m + 0 * G.n) = pσ G.n := by rw [← hσ]; congr 1; omega
  have hWle : W ≤ G.maxWeight := by
    rcases hW2 with h | ⟨j, hj, h⟩
    · omega
    · rw [h]; show mem1 (2 + 3 * j + 2) ≤ _; rw [hG.wt j hj]; exact wtOf_le_maxWeight hj
  have hlog := Nat.mul_le_mul_left G.m (log2Cost_mono hWle)
  have hWw : W < 2 ^ w := by
    rcases hW2 with h | ⟨j, hj, h⟩
    · omega
    · rw [h]; show mem1 (2 + 3 * j + 2) < _; rw [hG.wt j hj]
      have := hG.wt_mul_lt hj
      have : wtOf G j ≤ wtOf G j * 2 ^ pσ G.n := Nat.le_mul_of_pos_right _ (by positivity)
      omega
  have hσw : pσ G.n < 2 ^ w := by have := pσ_le G.n hn1; omega
  wram_step
  wram_step
  · refine ⟨G.m, pσ G.n, 2, 8 + 3 * G.m + 0 * G.n, 8 + 4 * G.m + 0 * G.n, W,
      rfl, hw2, fun j hj => ?_, ?_, by omega, by omega, by omega⟩
    · show 1 ≤ mem2 (2 + 3 * j + 2) ∧ mem2 (2 + 3 * j + 2) ≤ W
      have := hW1 j hj
      change mem1 (2 + 3 * j + 2) ≤ W at this
      rw [hG2.wt j hj]; rw [hG.wt j hj] at this
      exact ⟨wtOf_pos hG.allowed hj, this⟩
    · rcases hW2 with h | ⟨j, hj, h⟩
      · rw [h]; omega
      · rw [h]; show mem1 (2 + 3 * j + 2) * _ < _; rw [hG.wt j hj]; exact hG.wt_mul_lt hj
  intro v3 mem3 pos3 h3
  obtain ⟨h3a, h3b⟩ := h3
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h3a h3b
  wram_step
  · refine ⟨fun i hi => ?_, fun q hq => ?_, fun a ha => ?_⟩
    · show mem3 _ = _
      rw [h3b _ (Or.inl (by unfold aPAR; omega))]
      have := h2a i hi; unfold aPAR; simpa using this
    · obtain ⟨e1, e2⟩ := h3a q hq
      unfold rexp at e1 e2
      rw [hG2.wt q hq] at e1 e2
      refine ⟨?_, ?_⟩
      · show mem3 _ = _; unfold aEXP; simpa using e1
      · show mem3 _ = _; unfold aPW; rw [pω_wtOf hq]; simpa using e2
    · show mem3 a = mem1 a
      unfold aPAR aTLK at ha
      rw [h3b a (by omega), h2b a (by omega)]
  · simp only [wC, maxwC, parC, rndC, wCost, List.getD_cons_zero, List.getD_cons_succ, Nat.mul_add]
    wram_cost

end MinCostFlow.LowStretch
