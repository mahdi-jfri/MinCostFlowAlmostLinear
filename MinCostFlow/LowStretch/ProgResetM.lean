module

public import MinCostFlow.LowStretch.ProgResetL

/-!
# The reset of child `k`: what the calls after the split walk keep

Below the work array at `A`, the split walk changes only the labels of the vertices of child `k`,
`iotaP` writes above `A + 3 n`, and `ncP` writes above `A + 4 n` and the local indices of the new
nodes. So a cell below `A` that is neither a label of child `k` nor a local index holds after `ncP`
what it held at the split call (`CS.rsKeep10`). The precondition of `grpCopyP` (`CS.rsGcOk`) uses
this for the offsets `GOFF` of the pairs grouped by their lowest common node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **The cells that the reset keeps until `ncP`.** -/
theorem rsKeep10 {M7 M8 M9 M10 : ℕ → ℕ} {v : ℕ}
    (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a)
    (hsp : SplitPost S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 v M8 0)
    (hio : RsIota (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) M8 M9)
    (hok : (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).Ok w S.T.N)
    (hnc : (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).Done
      (S.sNK M1 k + v) M10)
    {a : ℕ} (ha : a < S.OUTK M1 H k + 2) (hlab : ∀ b ∈ (S.raw k).X, a ≠ S.E.LAB + b)
    (hloc : a < S.E.LOC ∨ S.E.LOC + S.T.N ≤ a) : M10 a = M6 a := by
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  obtain ⟨-, -, -, -, -, -, hlow, -, -⟩ := hsp
  rw [hnc.2.2 a (fun hout => by
      rcases hout with ⟨h1, -⟩ | ⟨i, hi, he⟩
      · simp only [rsNcE] at h1; omega
      · have := (hok.rd i hi).2.2.2
        simp only [rsNcE] at he this
        omega)]
  show M9 a = M6 a
  rw [hio.2 a (Or.inl (by omega)), hlow a (by show a < drawEnd (S.dwE M1 k H); omega) hlab,
    h7 a ha]

end CS

end MinCostFlow.LowStretch
