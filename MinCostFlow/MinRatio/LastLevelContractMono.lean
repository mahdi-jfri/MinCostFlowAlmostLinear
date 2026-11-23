module

public import MinCostFlow.MinRatio.LastLevelContract

/-!
# Monotonicity of the runtime last-level contract

A program that meets `lastLevelRuntimeMachineContract` with some multiplier, stretch precision and
allocation also meets it with larger ones:
* a larger multiplier gives a larger initialization budget;
* a larger stretch precision gives a stronger initialization precondition, since the stretch
  bound of a live edge is positive (`lastLevelStretchBound_pos`);
* a larger allocation gives a stronger room hypothesis and a weaker bound on the returned heap
  pointer.

The operations of the contract do not depend on these three numbers. The caller uses this
(`lastLevelRuntime_implements_mono`) to replace a multiplier, precision and allocation that depend
on the graph by bounds that hold for every graph of a given size.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- The stretch bound of a live edge is positive when every live length is positive: it is `2`
plus a quotient of nonnegative numbers. -/
theorem lastLevelStretchBound_pos {G : MGraph} {length : ℕ → ℝ}
    (hpos : ∀ e ∈ G.E, 0 < length e) {e : ℕ} (he : e ∈ G.E) :
    0 < lastLevelStretchBound G length e := by
  unfold lastLevelStretchBound
  have hsum : 0 ≤ ∑ f ∈ G.E, length f := Finset.sum_nonneg (fun f hf => (hpos f hf).le)
  have hdiv : 0 ≤ (∑ f ∈ G.E, length f) / length e := div_nonneg hsum (hpos e he).le
  linarith

/-- **Monotonicity of `lastLevelRuntimeMachineContract`** in the multiplier, the stretch
precision and the initialization allocation. -/
theorem lastLevelRuntime_implements_mono {w L vCap eCap mult mult' sP sP' : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool} {G : MGraph}
    {alloc alloc' : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {init : ℕ} {op : ℕ → ℕ}
    (h : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap mult sP alloc))
    (hmult : mult ≤ mult') (hsP : sP ≤ sP') (halloc : ∀ args, alloc 1 args ≤ alloc' 1 args) :
    R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap mult' sP' alloc') := by
  obtain ⟨hloc, hinit, hop⟩ := h
  refine ⟨hloc, ?_, hop⟩
  intro args mem pos ω hargs hpre hz hroom
  obtain ⟨graph, lengths, heap, hargsEq, h4, hPL, hbase, hstr⟩ := hpre
  have hposLen : ∀ e ∈ G.E,
      0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E e := by
    obtain ⟨graph', lengths', heap', hl, _, _, _, _, hpos⟩ := hbase
    simp only [List.cons.injEq] at hl
    obtain ⟨_, rfl, _⟩ := hl
    exact hpos
  have hpre0 : (lastLevelRuntimeMachineContract fmt L tool G vCap eCap mult sP alloc).initPre
      args mem := by
    refine ⟨graph, lengths, heap, hargsEq, h4, hPL, hbase, ?_⟩
    dsimp only at hstr ⊢
    intro e he
    have hB := lastLevelStretchBound_pos hposLen he
    have hpow : (2 : ℝ) ^ sP ≤ (2 : ℝ) ^ sP' := pow_le_pow_right₀ (by norm_num) hsP
    have hmono : 2 * (2 : ℝ) ^ sP *
        lastLevelStretchBound G (readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E) e ≤
        2 * (2 : ℝ) ^ sP' *
        lastLevelStretchBound G (readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E) e := by
      gcongr
    exact lt_of_le_of_lt hmono (hstr e he)
  have hroom0 : heapArg args + alloc 1 args < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (halloc args) _) hroom
  obtain ⟨body, hbody, o, st', c, hrun, s', x', hrep, hpost, hresp, hcost⟩ :=
    hinit args mem pos ω hargs hpre0 hz hroom0
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hresp
  refine ⟨body, hbody, o, st', c, hrun, s', x', hrep, hpost,
    ⟨hr1, hr2.trans (Nat.add_le_add_left (halloc args) _), hr3, hr4, hr5⟩, ?_⟩
  exact hcost.trans (Nat.mul_le_mul_right _ hmult)

end MinCostFlow.MinRatio

end
