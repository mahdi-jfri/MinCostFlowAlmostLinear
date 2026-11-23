module

public import MinCostFlow.LowStretch.ProgBodyNodeCongr

/-!
# The active pairs of the petal block

The setup leaves the active pairs at `ACT`: entry `i < nA` holds the pair `W.pr i` and its half
flag (`SetupOut`). Since `W.pr` maps `[0, nA)` one to one onto the active pairs of the cluster
(`PW.Ok.img`, `PW.Ok.inj`), the facts `act_nodup`, `act`, `act_fl` of `PetL.Ok` hold. The same
two facts give `nA = nact`, so register `22` holds the number of active pairs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ}

/-- The number of entries is the number of active pairs. -/
theorem Ok.nA_eq (h : W.Ok w mem) : W.nA = W.nact := by
  rw [h.hnact, ← h.img, Finset.card_image_of_injOn h.inj, Finset.card_range]

/-- **The active pairs of the petal block**, for a memory `M` that holds the entries at `ACT`. -/
theorem Ok.act_facts (h : W.Ok w mem) {M : ℕ → ℕ} {ACT : ℕ}
    (hA : ∀ i < W.nA, M (ACT + 2 * i) = W.pr i ∧
      M (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0)
    (X : PetL) (hX : X.ACT = ACT) (hn : X.nA = W.nA) :
    (X.actL M).Nodup ∧ (∀ p, p ∈ X.actL M ↔ p ∈ W.c.act W.G W.P) ∧
      ∀ i < X.nA, M (X.ACT + 2 * i + 1) = if M (X.ACT + 2 * i) ∈ W.c.half then 1 else 0 := by
  have hL : X.actL M = (List.range W.nA).map W.pr := by
    unfold PetL.actL
    rw [hn, hX]
    exact List.map_congr_left fun i hi => (hA i (List.mem_range.mp hi)).1
  refine ⟨?_, fun p => ?_, fun i hi => ?_⟩
  · rw [hL]
    exact List.Nodup.map_on (fun x hx y hy hxy => h.inj (by simpa using hx) (by simpa using hy) hxy)
      List.nodup_range
  · rw [hL, ← h.img]
    simp
  · rw [hn] at hi
    rw [hX, (hA i hi).1, (hA i hi).2]

end PW

end MinCostFlow.LowStretch
