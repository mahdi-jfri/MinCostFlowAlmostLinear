module

public import MinCostFlow.LowStretch.ProgBodyNodeOwed
public import MinCostFlow.LowStretch.ProgClusterLoop5
public import MinCostFlow.LowStretch.ProgramPetals

/-!
# The two facts of `ProgBodyNodeOwed` from the lemmas of the setup and the petal loop

The node part takes `setupCJ` and `RegPrefix` as hypotheses. Both follow from the lemmas of the
setup and of the petal loop:
- `setupCJ_of`: a procedure that meets `setupC` meets `setupCJ`, since `SetupOut` states
  `W.L.J = rootJ n + 5`, and `SetupOutJ` asks only `W.L.J ≤ rootJ n + 5`.
- `regPrefix_of`: `RegPrefix` is the statement of `LInv.regP_runs`, given the contracts of the
  procedures of the petals (`petalProcs_meets`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem SetupOut.toJ {w : ℕ} {g : SetG} {h : ℕ} {mem mem' : ℕ → ℕ}
    (H : SetupOut w g h mem mem') : SetupOutJ w g h mem mem' := by
  obtain ⟨W, A, Q, hS, n, ACT, hJ, rest⟩ := H.ex
  exact ⟨⟨W, A, Q, hS, n, ACT, hJ.le, rest⟩⟩

/-- **The setup meets `setupCJ`** when it meets `setupC`: the contracts have the same
precondition and cost, and `SetupOut` gives `SetupOutJ` (`SetupOut.toJ`). -/
theorem setupCJ_of {w : ℕ} {p : Program} {f : ℕ} (h : MeetsContract w p f (setupC w)) :
    MeetsContract w p f (setupCJ w) := by
  intro args mem pos ω hw hp
  obtain ⟨body, hb, o, st', c, hr, hpo, hc⟩ := h args mem pos ω hw hp
  exact ⟨body, hb, o, st', c, hr, fun g hg GB RB h' ha => (hpo g hg GB RB h' ha).toJ, hc⟩

/-- **The loop of the regular petals keeps its first petals**, from `LInv.regP_runs` and the
contracts of the procedures of the petals at `b` to `b + 13`. The copy at `b + 13` needs
`1 < 2^w`, which the invariant gives (`os_lt`). -/
theorem regPrefix_of {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (petalProcs b)) :
    RegPrefix w p (b + 12) (b + 13) := by
  obtain ⟨hS, hPush, hPS, hClr, hF, hT, hbP, hCp⟩ := petalProcs_meets (w := w) hp
  intro W A Q sp k0 M0 a0 st ω hI hL hW
  have hw1 : 1 < 2 ^ w := by have := hI.btw.ok.os_lt; omega
  exact hI.regP_runs hS hPush hPS hClr hF hT hbP (hCp hw1) hL hW ω

end MinCostFlow.LowStretch
