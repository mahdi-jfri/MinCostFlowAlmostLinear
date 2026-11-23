module

public import MinCostFlow.LowStretch.Program
public import MinCostFlow.LowStretch.ProgBodyNodeMeets
public import MinCostFlow.LowStretch.ProgramPetals
public import MinCostFlow.LowStretch.ProgBodyReset
public import MinCostFlow.LowStretch.ProgBodySS

/-!
# The program with its body

The body of the cluster procedure is the list `lsstBody rest iU iK`: the body `bodyP 31` at
`30`, the node part `nodeP iU 45 46 32 iK` at `31`, the loop of the regular petals `regP 45 46`
at `32`, the procedures of the petals `petalProcs 33` at `33` to `46` (one petal `petalP` at `45`,
the copy at `46`), and the other procedures `rest` (the setup and the child step) from `47` on,
at the indices `iU` (setup) and `iK` (child step).

`lowStretchSpanningTree_of_parts` gives `LowStretchSpanningTree` for this program from the
contracts of the setup, of the loop of the regular petals and of the child step
(`bodyP_meets`, `nodeP_meets`, `petalProcs_meets`, `lowStretchSpanningTree_of_prog`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The procedures of the body, from index `30` on. -/
def lsstBody (rest : List Stmt) (iU iK : ℕ) : ℕ → List Stmt := fun _ =>
  [bodyP 31, nodeP iU 45 46 32 iK, regP 45 46] ++ petalProcs 33 ++ rest

theorem lsstBody_procs (rest : List Stmt) (iU iK : ℕ) :
    (lsstProg (lsstBody rest iU iK)).procs[30]? = some (bodyP 31) ∧
      (lsstProg (lsstBody rest iU iK)).procs[31]? = some (nodeP iU 45 46 32 iK) ∧
      (lsstProg (lsstBody rest iU iK)).procs[32]? = some (regP 45 46) ∧
      (lsstProg (lsstBody rest iU iK)).HasAt 33 (petalProcs 33) := by
  have h := lsstProg_body (lsstBody rest iU iK)
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · simpa [lsstBody] using h 0 (by simp [lsstBody])
  · simpa [lsstBody] using h 1 (by simp [lsstBody])
  · simpa [lsstBody] using h 2 (by simp [lsstBody])
  · have hi' : i < 14 := by simpa [petalProcs_length] using hi
    have := h (3 + i) (by simp [lsstBody, petalProcs_length]; omega)
    rw [show 30 + (3 + i) = 33 + i by omega] at this
    rw [this]
    simp only [lsstBody, List.append_assoc]
    rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)]
    simp

/-- **[AN19] Theorem 1 for the program with its body**, from the contracts of the other
procedures of the body: the setup (`setupCJ`), the loop of the regular petals (`RegPrefix`) and
the child step (`MeetsChild`). The two facts on clusters that the cost of the body uses are
`Rec.Ok.nodes_le` (`s ≤ |S| + 1`) and `ClPre.reset_lt` (the numbers of the reset rule are
words). -/
theorem lowStretchSpanningTree_of_parts (rest : List Stmt) {iU iK : ℕ}
    (hSetup : ∀ w, MeetsContract w (lsstProg (lsstBody rest iU iK)) iU (setupCJ w))
    (hReg : ∀ w, RegPrefix w (lsstProg (lsstBody rest iU iK)) 45 46)
    (hK : ∀ w, MeetsChild w (lsstProg (lsstBody rest iU iK)) iK) :
    LowStretchSpanningTree := by
  obtain ⟨h30, h31, h32, h33⟩ := lsstBody_procs rest iU iK
  refine lowStretchSpanningTree_of_prog _ fun w => bodyP_meets h30 ?_ (by unfold bodyA; omega)
  obtain ⟨hS, hPush, hPS, hClr, hF, hT, hbP, hCp⟩ := petalProcs_meets (w := w) h33
  exact nodeP_meets h31 (hSetup w) hS hPush hPS hClr hF hT hbP hCp h32 (hReg w) (hK w)
    (fun _ _ _ _ _ h => h.nodes_le) fun _ _ _ _ _ _ _ _ _ _ hpre hD _ hk => hpre.reset_lt hD hk

end MinCostFlow.LowStretch
