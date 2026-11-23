module

public import MinCostFlow.LSF.Program.TTrack
public import MinCostFlow.LSF.Program.TBlockFill

/-!
# The `T` block at the start

At the start of the data structure, `G = G₀` and the current tree `T_cur` is `T₀`. The `T`
block is then written in four parts: the header, frozen arrays and `idxOfEdge` table by
`tBlockFillProc`, the tracker graph by `tTrackProc`, the edge IDs by `t0EdgesProc`, and the
order `π` by `congOrderProc` (which writes its ranks straight into the `π` array).

`tBlockAt_init` collects these facts into `TBlockAt`. Its tracker part needs two facts about the
edge list of `T₀`: the first `nOrig` edges are the edges of `T₀` that are edges of `G₀`, and on
those edges the ends in `T₀` and in `G₀` agree. Both hold for the output of `t0EdgesProc`
(`ValidLSFParams` gives the second).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.DynSpanner.Program

@[expose] public section

theorem tBlockAt_init {mem : ℕ → ℕ} {tPtr vCap eCap tM nOrig : ℕ} {G₀ T₀ : MGraph}
    {π f : ℕ → ℕ} {tOrigList : List ℕ}
    (hH : TBlockHeader mem tPtr vCap eCap tM)
    (hlen : tOrigList.length = tM) (hnd : tOrigList.Nodup)
    (hmemT : ∀ e, e ∈ tOrigList ↔ e ∈ T₀.E)
    (hO : ListAt mem (tOrigIdBase tPtr vCap tM) tOrigList)
    (hP : ListAt mem (tPiBase tPtr vCap tM) (tOrigList.map π))
    (hI1 : ∀ i < tM, mem (tOrigIdBase tPtr vCap tM + i) < eCap →
      mem (tIdxOfEdgeBase tPtr vCap tM + mem (tOrigIdBase tPtr vCap tM + i)) = i + 1)
    (hI0 : ∀ e < eCap, (∀ i < tM, mem (tOrigIdBase tPtr vCap tM + i) ≠ e) →
      mem (tIdxOfEdgeBase tPtr vCap tM + e) = 0)
    (hdg : DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) (tTrackGraph G₀.V f (2 * nOrig)))
    (hf : ∀ i (hi : i < nOrig) (hi' : i < tOrigList.length),
      f (2 * i) = T₀.tail tOrigList[i] ∧ f (2 * i + 1) = T₀.head tOrigList[i])
    (hFr : ∀ i (hi : i < tOrigList.length),
      mem (tFrozenTailBase tPtr vCap tM + i) = T₀.tail tOrigList[i] ∧
      mem (tFrozenHeadBase tPtr vCap tM + i) = T₀.head tOrigList[i])
    (hnO : nOrig ≤ tM)
    (hG : ∀ i (hi : i < tOrigList.length), tOrigList[i] ∈ G₀.E ↔ i < nOrig)
    (hTG : ∀ e ∈ T₀.E, e ∈ G₀.E → T₀.tail e = G₀.tail e ∧ T₀.head e = G₀.head e) :
    TBlockAt mem tPtr vCap eCap tM G₀ T₀ T₀ π tOrigList := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hH
  have hOi : ∀ i (hi : i < tOrigList.length), mem (tOrigIdBase tPtr vCap tM + i) = tOrigList[i] :=
    fun i hi => hO i hi
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemT, hO, hP, fun i hi hlt => ?_,
    fun e he hne => ?_, tTrackGraph G₀.V f (2 * nOrig), hdg, rfl, fun e he => ?_,
    fun i hi => ?_⟩
  · rw [← hOi i hi]
    exact hI1 i (by omega) (by rw [hOi i hi]; exact hlt)
  · by_contra hno
    push_neg at hno
    have hall : ∀ i < tM, mem (tOrigIdBase tPtr vCap tM + i) ≠ e := by
      intro i hi heq
      exact hno i (by omega) (by rw [← hOi i (by omega)]; exact heq)
        (by rw [← heq, hI1 i hi (by rw [heq]; exact he)])
    exact hne (hI0 e he hall)
  · simp only [tTrackGraph, Finset.mem_range] at he; omega
  · have hfT : tOrigList[i] ∈ T₀.E := (hmemT _).mp (List.getElem_mem hi)
    have hGi := hG i hi
    obtain ⟨hFt, hFh⟩ := hFr i hi
    simp only [tTrackGraph, Finset.mem_range]
    refine ⟨?_, fun h2 => ?_, fun h2 => ?_, ?_, fun h2 => ?_, fun h2 => ?_⟩
    · constructor
      · intro h2
        have hin : tOrigList[i] ∈ G₀.E := hGi.mpr (by omega)
        exact ⟨hin, (hTG _ hfT hin).1.symm⟩
      · rintro ⟨hin, -⟩; have := hGi.mp hin; omega
    · rw [if_pos h2]; exact ⟨(hf i (by omega) hi).1, (hf i (by omega) hi).1⟩
    · exact hFt
    · constructor
      · intro h2
        have hin : tOrigList[i] ∈ G₀.E := hGi.mpr (by omega)
        exact ⟨hin, (hTG _ hfT hin).2.symm⟩
      · rintro ⟨hin, -⟩; have := hGi.mp hin; omega
    · rw [if_pos h2]; exact ⟨(hf i (by omega) hi).2, (hf i (by omega) hi).2⟩
    · exact hFh

end

end MinCostFlow.LSF.Program
