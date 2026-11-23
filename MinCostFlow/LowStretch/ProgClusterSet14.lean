module

public import MinCostFlow.LowStretch.ProgClusterSet13
public import MinCostFlow.LowStretch.ProgClusterSet7

/-!
# The setup of a cluster: the path of the target in the petal searches

The special petal is carved along the path of parents of the node of `c.t` (`LInv.spPet_runs`
asks `W.Path mem vt n` and a split of the highway along `W.stp A mem vt n`). After the setup the
parents are the copy `NXT` of the array `PAR` of `hwFix`, so this path is the path of
`HF.V.path`: it follows the split highway `hwSt` and ends at the node of the center
(`PW.path_t`). The highway `c.hw` splits along it (`IsHighway.hwDec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {A : TA} {P : Par} {F : HF} {mem M M' : ℕ → ℕ} {H NL : ℕ}

/-- **The path of the target follows the split highway.** -/
theorem path_t (hV : F.V W.T W.G P W.c W.R mem M H NL) (hX : F.Done M M' F.nH) {mem' : ℕ → ℕ}
    (hcp : ∀ v < W.s, mem' (W.NXT + v) = M' (F.PAR + v))
    (hpp : ∀ v < W.s, mem' (A.PP + v) = M' (F.PP + v) ∧ mem' (A.PA + v) = M' (F.PA + v) ∧
      mem' (A.PB + v) = M' (F.PB + v)) :
    W.Path mem' (W.sv W.c.t) F.nH ∧
      W.stp A mem' (W.sv W.c.t) F.nH = Cl.hwSt W.G W.c.θ W.c.t W.c.hw := by
  have hpe : ∀ i ≤ F.nH, W.pe mem' (W.sv W.c.t) i = parEnd M' F.PAR (W.sv W.c.t) i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pe_succ', ih (by omega)]
      unfold parEnd
      rw [Function.iterate_succ_apply']
      exact hcp _ (hV.path_lt hX (by omega))
  refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
  · rw [hpe _ le_rfl]; exact hV.path_end hX
  · rw [hpe _ hi.le]; exact ⟨hV.path_ne hX hi, hV.path_lt hX hi.le⟩
  · apply List.ext_getElem
    · rw [stp_length, hV.nH]
    · intro i h1 h2
      have hi : i < F.nH := by rw [stp_length] at h1; exact h1
      rw [stp_getElem, hpe _ hi.le]
      have hl : parEnd M' F.PAR (W.sv W.c.t) i < W.s := hV.path_lt hX hi.le
      obtain ⟨q1, q2, q3⟩ := hpp _ hl
      obtain ⟨a1, a2, a3⟩ := hV.path_arc hX hi
      rw [q1, q2, q3]
      erw [a1, a2, a3]
      simp only [HF.sj]
      rw [List.getD_eq_getElem _ _ h2]

/-- **The highway splits along the path of the target.** -/
theorem path_t_dec (hV : F.V W.T W.G P W.c W.R mem M H NL) (hX : F.Done M M' F.nH)
    {mem' : ℕ → ℕ} (hcp : ∀ v < W.s, mem' (W.NXT + v) = M' (F.PAR + v))
    (hpp : ∀ v < W.s, mem' (A.PP + v) = M' (F.PP + v) ∧ mem' (A.PA + v) = M' (F.PA + v) ∧
      mem' (A.PB + v) = M' (F.PB + v)) :
    W.c.HwDec W.G W.c.t (W.stp A mem' (W.sv W.c.t) F.nH) W.c.hw := by
  rw [(path_t hV hX hcp hpp).2]
  exact hV.ok.inv.good.high.hwDec

end PW

end MinCostFlow.LowStretch
