module

public import MinCostFlow.LowStretch.ProgResetA
public import MinCostFlow.LowStretch.ProgChildOneTest

/-!
# The reset of child `k`: the words and the loads

The words of `rsP` for raw child `k` (`CS.rsV`), and the memory facts of its loads
(`CS.rsFacts`). The loads read only the global block and the petal block, which are safe cells:
`MidOk` and `drawPost` keep them.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The words of `rsP` for raw child `k`, with heap pointer `H` at the start of child `k`. -/
noncomputable def rsV (M1 : ℕ → ℕ) (k H : ℕ) : RsV where
  GB := S.GB
  BK := S.h + 9 * k
  A := drawEnd (S.dwE M1 k H)
  Δ := (S.raw k).Δ S.G
  sz := (S.raw k).X.card
  μ := (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a))
  SRCK := S.ORDK + offOf (S.keyF M1) S.nA k
  cnt := S.cntK M1 k
  NA := S.NAK M1 H k
  sN := S.sNK M1 k
  cc := S.mem (S.X.CC + k)
  HM := S.HM
  XB := S.XB
  B := S.E.B
  CH1 := S.E.KCH1
  CH2 := S.E.KCH2
  MW := S.E.KMW
  SZ := S.E.KSZ
  LO := S.E.KLO
  ORDL := S.E.ORDL
  LAB := S.E.LAB
  n := S.E.n
  HEAD := S.E.HEAD
  LOC := S.E.LOC
  GOFF := S.E.GOFF
  GPR := S.E.GPR
  IN := S.E.IN
  ACT := S.X.ACT
  PP := S.X.PP

variable {S} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **The loads of `rsP` read what they should**, on any memory `M7` that agrees with `M6` below
`OUTK + 2`. -/
theorem rsFacts (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) {M7 : ℕ → ℕ}
    (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a) : RsFacts w (S.rsV M1 k H) M7 := by
  have hGB : (S.GB, 21) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have hXB : (S.XB, 16) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have bG := hpre.below _ hGB
  have bX := hpre.below _ hXB
  dsimp only at bG bX
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend := drawEnd_le (H := H) hpre hT hk
  have kG : ∀ i < 21, M7 (S.GB + i) = S.mem (S.GB + i) := fun i hi => by
    rw [h7 _ (by omega)]
    exact keep_safe hpre hT hI hk hmid (safe_reg hpre hGB (i := i) hi)
  have kX : ∀ i < 16, M7 (S.XB + i) = S.mem (S.XB + i) := fun i hi => by
    rw [h7 _ (by omega)]
    exact keep_safe hpre hT hI hk hmid (safe_reg hpre hXB (i := i) hi)
  exact ⟨kG 9 (by norm_num), kG 10 (by norm_num), kG 11 (by norm_num), kG 12 (by norm_num),
    kG 13 (by norm_num), kG 15 (by norm_num), kG 6 (by norm_num), kG 0 (by norm_num),
    kG 14 (by norm_num), kG 7 (by norm_num), kG 16 (by norm_num), kG 17 (by norm_num),
    kG 3 (by norm_num), kX 14 (by norm_num), kX 9 (by norm_num), by show S.GB + 17 < 2 ^ w; omega,
    by show S.XB + 14 < 2 ^ w; omega, by show drawEnd (S.dwE M1 k H) + 2 < 2 ^ w; omega,
    by omega⟩

end CS

end MinCostFlow.LowStretch
