module

public import MinCostFlow.IPM.Machine.RoundEdgeModel
import MinCostFlow.IPM.Machine.RoundCleanupModel
import Mathlib.Tactic

/-!
# Conditions for relinking the new fractional edge

If the corrected edge is still fractional, the path supplied the
limiting availability. Cleanup cuts a limiting edge, separating the
endpoints and making the final Link legal.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The corrected coordinate, still between the original floor and
ceiling, lies within the same integral magnitude bound as its input. -/
theorem round_between_abs_le {q x : ℚ} {U : ℕ}
    (hQ : |(q:ℝ)|≤U) (hLo : (⌊q⌋:ℚ)≤x) (hHi : x≤(⌈q⌉:ℚ)) :
    |(x:ℝ)|≤U := by
  have hq : |q|≤(U:ℚ) := by exact_mod_cast hQ
  obtain ⟨hq₁,hq₂⟩ := abs_le.mp hq
  have hLo' : -(U:ℤ)≤⌊q⌋ := Int.le_floor.mpr (by push_cast; exact hq₁)
  have hHi' : ⌈q⌉≤(U:ℤ) := Int.ceil_le.mpr (by exact_mod_cast hq₂)
  have hh₁ : -(U:ℚ)≤(⌊q⌋:ℚ) := by exact_mod_cast hLo'
  have hh₂ : (⌈q⌉:ℚ)≤(U:ℚ) := by exact_mod_cast hHi'
  exact_mod_cast (abs_le.mpr ⟨hh₁.trans hLo,hHi.trans hh₂⟩ : |x|≤(U:ℚ))

set_option maxHeartbeats 550000 in
/-- All conditions for machine cleanup and the optional relink
follow from the model loop invariant. The cleanup keeps the new
edge's adjusted table coordinate and accounts exactly for its cuts. -/
theorem roundCycleClean_properties {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {P : ℕ} {M : ℚ}
    (st : RoundState D I) (j : Fin I.m) (backward : Bool)
    (hInv : LoopInv D I f P M j.val st) (hf : ∀ i,IsFixedPoint P (f i))
    (hFrac : isIntRat (f j)=false)
    (hComp : (D.toForest st.df).SameComp (I.edge j).tail (I.edge j).head) :
    let u := roundFrom (I.edge j) backward
    let v := roundTo (I.edge j) backward
    let aval := roundAvail (f j) backward
    let δ := roundCycleDelta D st.df j (f j) backward
    let q := roundCycleValue D st.df j (f j) backward
    let pushed := D.pathAdd st.df u v δ
    let clean := roundCycleClean D I (f j) st j backward
    0≤aval ∧ IsFixedPoint P q ∧ (⌊f j⌋:ℚ)≤q ∧ q≤(⌈f j⌉:ℚ) ∧
      (∀ e∈(D.toForest pushed).edges,ForestEdgeWeakInv I f e ∧
        IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd) ∧
      (∀ e∈(D.toForest clean.1).edges,ForestEdgeWeakInv I f e ∧
        IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd ∧ e.eid<j.val) ∧
      D.Inv clean.1 ∧ (D.toForest clean.1).n=I.n ∧ clean.2.1 j=q ∧
      (isIntRat q=false → ¬(D.toForest clean.1).SameComp (I.edge j).tail (I.edge j).head) ∧
      clean.2.2.1.cutOps+(D.toForest clean.1).edges.length =
        st.counts.cutOps+(D.toForest st.df).edges.length ∧
      (D.toForest clean.1).edges.length≤(D.toForest st.df).edges.length := by
  dsimp only
  let u := roundFrom (I.edge j) backward
  let v := roundTo (I.edge j) backward
  let aval := roundAvail (f j) backward
  let δ := roundCycleDelta D st.df j (f j) backward
  let q := roundCycleValue D st.df j (f j) backward
  let pushed := D.pathAdd st.df u v δ
  let clean := roundCycleClean D I (f j) st j backward
  obtain ⟨hDf,hN,hEdges,_,_,_,_,_,_,hLink,hCut,_,_,_,_,hFP,_,_⟩ := hInv
  have hu : (D.toForest st.df).SameComp u v := by
    cases backward
    · exact hComp.symm
    · exact hComp
  have hV := hD.2.1 _ hDf
  obtain ⟨steps,hPath,hw,_⟩ := MathForest.findSteps_some_of_sameComp hV hu
  obtain ⟨hB,hF,hB₀,_,hF₀,_,_⟩ := round_availability_bounds P (f j) (hf j) hFrac
  have hAval : 0≤aval := by cases backward; exact hF₀.le; exact hB₀.le
  have hAvalP : IsFixedPoint P aval := by cases backward; exact hF; exact hB
  have hStep : ∀ t∈steps,0≤t.dirAvail := by
    intro t ht
    have hh := (hEdges t.edge (hw.mem_edges t ht)).1
    cases hDir : t.fwd
    · simpa [PathStep.dirAvail,hDir] using hh.2.2.le
    · simpa [PathStep.dirAvail,hDir] using hh.2.1.le
  have hStepP : ∀ t∈steps,IsFixedPoint P t.dirAvail := by
    intro t ht
    have hh := (hFP hf).1 t.edge (hw.mem_edges t ht)
    cases hDir : t.fwd
    · simpa [PathStep.dirAvail,hDir] using hh.2.2
    · simpa [PathStep.dirAvail,hDir] using hh.2.1
  have hδ : 0≤δ := roundDelta_nonnegative hD hDf hPath aval hAval hStep
  have hδP : IsFixedPoint P δ := roundDelta_fixed hD hDf hPath aval hAvalP hStepP
  have hQP : IsFixedPoint P q := by
    cases backward
    · exact isFixedPoint_add (hf j) hδP
    · exact isFixedPoint_sub (hf j) hδP
  obtain ⟨hMax,hStepBound,hLimit⟩ := roundDelta_path hD hDf hPath aval
  have hMax' : δ≤aval := hMax
  obtain ⟨hq₁,hq₂,_,hq₃⟩ := roundCycleEdge_bounds (f j) δ backward hδ hMax'
  obtain ⟨hInvP,hNP,hLenP,hPathP,hWP,hBP⟩ := roundPathAdd_invariants hD hDf hPath
    (fun e he => (hEdges e he).1) (hFP hf).1 hδ hδP hStepBound
  have hFuel : (D.toForest pushed).edges.length < I.m+1 := by
    change (D.toForest pushed).edges.length=(D.toForest st.df).edges.length at hLenP
    have hj := j.isLt
    omega
  let arr := fun k => if k=j then q else st.flowArr k
  let counts := roundCycleCounts st.counts
  let rats := roundCycleRats D st.df j (f j) backward st.computedRats
  let steps' := steps.map fun t => { t with edge := t.edge.addFlow t.fwd δ }
  obtain ⟨hInvC,_,hSub,_,_,_,hOutside,_,hDisconnect,_,_,_,_,hLenC,hCount,_,_,_,_,_⟩ :=
    removeZeroEdges_spec hD (f:=f) (I.m+1) pushed arr counts rats u v steps' hInvP hPathP hFuel
      (fun e he => (hWP e he).1) hBP
  have hNC : (D.toForest clean.1).n=I.n :=
    (roundCleanup_n hD f (I.m+1) pushed arr counts rats u v steps' hInvP hPathP hFuel
      (fun e he => (hWP e he).1) hBP).trans (hNP.trans hN)
  have hFresh : ∀ e∈(D.toForest pushed).edges,e.eid<j.val := by
    intro e he
    obtain ⟨g,hg,hEq⟩ := roundPathAdd_edgeId hD hDf hPath e he
    exact hEq ▸ (hEdges g hg).2
  have hOut : j.val∉(D.toForest pushed).edges.map ForestEdge.eid := by
    intro hm
    obtain ⟨e,he,hj⟩ := List.mem_map.mp hm
    exact (Nat.ne_of_lt (hFresh e he)) hj
  have hC : clean.2.1 j=q := (hOutside j hOut).trans (by simp [arr])
  refine ⟨hAval,hQP,hq₁,hq₂,hWP,?_,hInvC,hNC,hC,?_,?_,?_⟩
  · intro e he
    have he' := hSub e he
    exact ⟨(hWP e he').1,(hWP e he').2.1,(hWP e he').2.2.1,(hWP e he').2.2.2,hFresh e he'⟩
  · intro hq hcomp
    obtain ⟨t,ht,hδeq⟩ := hLimit (hq₃ hq)
    let t' := { t with edge := t.edge.addFlow t.fwd δ }
    have ht' : t'∈steps' := List.mem_map_of_mem ht
    change t.dirAvail=δ at hδeq
    have hz' : t'.dirAvail=0 := by
      cases hF : t.fwd
      · have heq : t.edge.availBwd=δ := by simpa [PathStep.dirAvail,hF] using hδeq
        have hEq : t'.dirAvail=t.edge.availBwd-δ := by
          simp [t',PathStep.dirAvail,ForestEdge.addFlow,hF]
        exact hEq.trans (sub_eq_zero.mpr heq)
      · have heq : t.edge.availFwd=δ := by simpa [PathStep.dirAvail,hF] using hδeq
        have hEq : t'.dirAvail=t.edge.availFwd-δ := by
          simp [t',PathStep.dirAvail,ForestEdge.addFlow,hF]
        exact hEq.trans (sub_eq_zero.mpr heq)
    have hcomp' : (D.toForest clean.1).SameComp u v := by
      cases backward
      · exact hcomp.symm
      · exact hcomp
    exact hDisconnect ⟨t',ht',hz'⟩ hcomp'
  · exact hCount.trans (congrArg (fun n => st.counts.cutOps+n) hLenP)
  · exact hLenC.trans_eq hLenP

end MinCostFlow.IPM.Machine
