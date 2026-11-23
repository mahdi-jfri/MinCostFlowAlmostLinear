module

public import MinCostFlow.LowStretch.ProgPre
public import MinCostFlow.LowStretch.ProgOut

/-!
# The procedures of the entry

`preProcs b` lists the preprocessing and every procedure it calls, from index `b` on, and ends
with `copyWords` at `b + 25`. A program that has this list at index `1` runs the preprocessing at
index `1` (`preP_meets`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited MinCostFlow.Expander

/-- The preprocessing, its parts and their procedures, from index `b` on, then `copyWords`. -/
def preProcs (b : ℕ) : List Stmt :=
  [preP (b + 1) (b + 2) (b + 3) (b + 4),
    wP (b + 5) (b + 6) (b + 7),
    kP (b + 9) (b + 10) (b + 11) (b + 12) (b + 14) (b + 15),
    gP (b + 18) (b + 19) (b + 10),
    rP (b + 8) (b + 21) (b + 22) (b + 23) (b + 24),
    maxwP, parP (b + 8), rndP (b + 8), log2P, tabP eMin, csrB, ddP, tabP eKey,
    siftDownProc, heapSortProc (b + 13), krP (b + 16), kstP (b + 17), findP, koP,
    lcaAll (b + 20), lcaOne, labP, filtP (nodeE (.reg 15)) (.reg 15) 1, locP,
    filtP eDiff (.reg 15) 2, copyWords]

theorem preProcs_length (b : ℕ) : (preProcs b).length = 26 := rfl

theorem hasAt_sub {p : Program} {b : ℕ} {l : List Stmt} (h : p.HasAt b l) (i : ℕ)
    (hi : i < l.length) : p.HasAt (b + i) [l[i]] := by
  intro j hj
  have : j = 0 := by simpa using hj
  subst this
  simpa using h i hi

/-- **The preprocessing** at index `b` meets its contract when `preProcs b` is at index `b`. -/
theorem preP_meets {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (preProcs b)) (G : WGraph) :
    MeetsContract w p b (preC w G) := by
  have h := fun i (hi : i < 26) => hasAt_sub hp i (by rw [preProcs_length]; exact hi)
  have hLog : MeetsContract w p (b + 8) (log2C w) := log2P_spec (h 8 (by norm_num))
  have hCsr : MeetsContract w p (b + 10) (csrC w) := csrB_spec (h 10 (by norm_num))
  have hW : MeetsContract w p (b + 1) (wC w G) :=
    wP_spec (h 1 (by norm_num)) (maxwP_spec (h 5 (by norm_num)))
      (parP_spec (h 6 (by norm_num)) (h 8 (by norm_num)))
      (rndP_spec (h 7 (by norm_num)) (h 8 (by norm_num))) G
  have hHs : MeetsContract w p (b + 13 + 1) (heapSortContract w) :=
    heapSort_spec (h 13 (by norm_num)) (h 14 (by norm_num))
  have hK : MeetsContract w p (b + 2) (kC w G) :=
    kP_spec (h 2 (by norm_num)) (minSpec (h 9 (by norm_num))) hCsr
      (DDE.ddP_spec (h 11 (by norm_num))) (keySpec (h 12 (by norm_num))) hHs
      (krP_spec (h 15 (by norm_num)) (h 16 (by norm_num)) (h 17 (by norm_num)) (pgOf G))
  have hG : ∀ T, MeetsContract w p (b + 3) (gC w G T) := fun T =>
    gP_spec (h 3 (by norm_num)) (koP_spec (h 18 (by norm_num)) T (pgOf G))
      (lcaAll_spec (h 19 (by norm_num)) (h 20 (by norm_num)) T (pgOf G)) hCsr
  have hR : ∀ T, MeetsContract w p (b + 4) (rC w G T) := fun T =>
    rP_spec (h 4 (by norm_num)) hLog (labP_spec (h 21 (by norm_num)) T (pgOf G))
      (nodesSpec (h 22 (by norm_num))) (locP_spec (h 23 (by norm_num)))
      (saSpec (h 24 (by norm_num)))
  simpa using preP_spec (h 0 (by norm_num)) hW hK hG hR

theorem copy_at {p : Program} {b : ℕ} (hp : p.HasAt b (preProcs b)) :
    p.HasAt (b + 25) [copyWords] :=
  hasAt_sub hp 25 (by rw [preProcs_length]; norm_num)

end MinCostFlow.LowStretch
