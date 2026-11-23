module

public import MinCostFlow.IPM.Machine.RoundDelta
public import MinCostFlow.Rounding.Cycles
import Mathlib.Tactic

/-!
# Exact path increments keep the rounding payloads in range

A cycle increment is the smaller of the new edge's availability
and the path minimum. Along the forest path it can only consume
the current directional availability. The reverse availability
stays positive and all payloads stay on the fixed-point grid.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The path minimum bounds the chosen increment on every path edge.
If the path supplies no hit, it is empty. -/
theorem roundDelta_path {D : DynForest} (hD : D.IsSpec) {s : D.State} {a b : ℕ}
    {steps : List PathStep} (hInv : D.Inv s)
    (hPath : findSteps (D.toForest s).edges a b=some steps) (q : ℚ) :
    let hit := D.pathMin s a b
    let δ := hit.elim q (fun e => min q e.avail)
    δ≤q ∧ (∀ t∈steps,δ≤t.dirAvail) ∧
      (δ<q → ∃ t∈steps,t.dirAvail=δ) := by
  dsimp only
  have hValid := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hValid.2.1 hPath
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  rw [hD.2.2.2.2.2.2.1 s a b hInv hConn,MathForest.pathMin,hPath,Option.bind_some]
  cases hmin : stepsMinHit steps with
  | none =>
    have hnil := stepsMinHit_eq_none_iff.mp hmin
    simp [hnil]
  | some hit =>
    dsimp only [Option.elim_some]
    obtain ⟨pre,t,post,hsplit,htHit,hPre,hPost⟩ := stepsMinHit_spec hmin
    have hav : t.dirAvail=hit.avail := by rw [← htHit]; rfl
    refine ⟨min_le_left _ _,?_,?_⟩
    · intro v hv
      rw [hsplit,List.mem_append,List.mem_cons] at hv
      rcases hv with hv | rfl | hv
      · exact (min_le_right _ _).trans (hPre v hv).le
      · exact hav ▸ min_le_right _ _
      · exact (min_le_right _ _).trans (hPost v hv)
    · intro hl
      have ht : t∈steps := by rw [hsplit]; simp
      have hLT : hit.avail<q := by
        by_contra hn
        rw [min_eq_left (le_of_not_gt hn)] at hl
        exact (lt_irrefl _ hl)
      exact ⟨t,ht,hav.trans (min_eq_right hLT.le).symm⟩

/-- A nonnegative edge availability and nonnegative path
availabilities give a nonnegative minimum. -/
theorem roundDelta_nonnegative {D : DynForest} (hD : D.IsSpec) {s : D.State}
    {a b : ℕ} {steps : List PathStep} (hInv : D.Inv s)
    (hPath : findSteps (D.toForest s).edges a b=some steps) (q : ℚ)
    (hq : 0≤q) (hStep : ∀ t∈steps,0≤t.dirAvail) :
    0≤(D.pathMin s a b).elim q (fun e => min q e.avail) := by
  have hV := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hV.2.1 hPath
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  rw [hD.2.2.2.2.2.2.1 s a b hInv hConn,MathForest.pathMin,hPath,Option.bind_some]
  cases hm : stepsMinHit steps with
  | none => exact hq
  | some hit =>
    obtain ⟨pre,t,post,hsplit,htHit,_,_⟩ := stepsMinHit_spec hm
    have ht : t∈steps := by rw [hsplit]; simp
    exact le_min hq (by rw [← htHit]; exact hStep t ht)

/-- Selecting an availability preserves the fixed-point grid. -/
theorem roundDelta_fixed {D : DynForest} (hD : D.IsSpec) {s : D.State}
    {a b P : ℕ} {steps : List PathStep} (hInv : D.Inv s)
    (hPath : findSteps (D.toForest s).edges a b=some steps) (q : ℚ)
    (hq : IsFixedPoint P q)
    (hStep : ∀ t∈steps,IsFixedPoint P t.dirAvail) :
    IsFixedPoint P ((D.pathMin s a b).elim q (fun e => min q e.avail)) := by
  have hV := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hV.2.1 hPath
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  rw [hD.2.2.2.2.2.2.1 s a b hInv hConn,MathForest.pathMin,hPath,Option.bind_some]
  cases hm : stepsMinHit steps with
  | none => exact hq
  | some hit =>
    obtain ⟨pre,t,post,hsplit,htHit,_,_⟩ := stepsMinHit_spec hm
    have ht : t∈steps := by rw [hsplit]; simp
    exact isFixedPoint_min hq (by rw [← htHit]; exact hStep t ht)

/-- Each edge after PathAdd has an unchanged identifier from the
old forest. This keeps the edge being inserted outside the path. -/
theorem roundPathAdd_edgeId {D : DynForest} (hD : D.IsSpec) {s : D.State}
    {a b : ℕ} {steps : List PathStep} {δ : ℚ} (hInv : D.Inv s)
    (hPath : findSteps (D.toForest s).edges a b=some steps) :
    ∀ e∈(D.toForest (D.pathAdd s a b δ)).edges,
      ∃ e'∈(D.toForest s).edges,e.eid=e'.eid := by
  have hV := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hV.2.1 hPath
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  have hSame := (hD.2.2.2.2.2.1 s a b δ hInv hConn).2
  intro e he
  have he' := hSame.2.subset he
  simp only [MathForest.pathAdd,hPath,List.mem_map] at he'
  obtain ⟨g,hg,rfl⟩ := he'
  refine ⟨g,hg,?_⟩
  unfold MathForest.applyStepsDelta
  split
  · rfl
  · rename_i t ht
    cases t.fwd <;> rfl

/-- The path increment leaves exactly the path required by cleanup,
with nonnegative forward and positive reverse availabilities. The
payloads remain dyadic and the edge set retains its size. -/
theorem roundPathAdd_invariants {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {s : D.State} {a b P : ℕ} {steps : List PathStep} {δ : ℚ}
    (hInv : D.Inv s) (hPath : findSteps (D.toForest s).edges a b=some steps)
    (hStrict : ∀ e∈(D.toForest s).edges,ForestEdgeStrictInv I f e)
    (hFP : ∀ e∈(D.toForest s).edges,
      IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd)
    (hδ : 0≤δ) (hδP : IsFixedPoint P δ) (hAvail : ∀ t∈steps,δ≤t.dirAvail) :
    let s' := D.pathAdd s a b δ
    let steps' := steps.map fun t => { t with edge := t.edge.addFlow t.fwd δ }
    D.Inv s' ∧ (D.toForest s').n=(D.toForest s).n ∧
      (D.toForest s').edges.length=(D.toForest s).edges.length ∧
      findSteps (D.toForest s').edges a b=some steps' ∧
      (∀ e∈(D.toForest s').edges,ForestEdgeWeakInv I f e ∧
        IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd) ∧
      (∀ t∈steps',0≤t.dirAvail ∧ 0<t.flip.dirAvail) := by
  dsimp only
  let s' := D.pathAdd s a b δ
  have hV := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hV.2.1 hPath
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  obtain ⟨hInv',hSame⟩ := hD.2.2.2.2.2.1 s a b δ hInv hConn
  have hPath' := pathAdd_findSteps hV hPath δ
  have hn : ((D.toForest s).pathAdd a b δ).n=(D.toForest s).n := by simp [MathForest.pathAdd,hPath]
  refine ⟨hInv',hSame.1.trans hn,hSame.2.length_eq.trans (MathForest.pathAdd_edges_length _ _ _ _),
    (hSame.findSteps_eq (hD.2.1 _ hInv') a b).trans hPath',?_,?_⟩
  · intro g hg
    have hg' := hSame.2.subset hg
    simp only [MathForest.pathAdd,hPath,List.mem_map] at hg'
    obtain ⟨e,he,rfl⟩ := hg'
    obtain ⟨hf,hFor,hBack⟩ := hFP e he
    by_cases hOn : ∃ t∈steps,t.edge=e
    · obtain ⟨t,ht,rfl⟩ := hOn
      rw [MathForest.applyStepsDelta_of_mem hV hPath δ ht]
      obtain ⟨⟨j,hid,hu,hv,hc,hfrac,hlo,hhi,hfwd,hbwd⟩,hp,hq⟩ := hStrict t.edge he
      have hBound := hAvail t ht
      refine ⟨⟨j,by simp [hid],by simp [hu],by simp [hv],by simp [hc],hfrac,?_⟩,?_⟩
      · cases tf : t.fwd <;> simp [PathStep.dirAvail,tf] at hBound
        all_goals simp [ForestEdge.addFlow]
        all_goals exact ⟨by linarith only [hδ,hBound,hlo,hhi,hfwd,hbwd],
          by linarith only [hδ,hBound,hlo,hhi,hfwd,hbwd],
          by linarith only [hfwd,hbwd],
          by linarith only [hfwd,hbwd]⟩
      · cases tf : t.fwd
        · exact ⟨isFixedPoint_sub hf hδP,isFixedPoint_add hFor hδP,isFixedPoint_sub hBack hδP⟩
        · exact ⟨isFixedPoint_add hf hδP,isFixedPoint_sub hFor hδP,isFixedPoint_add hBack hδP⟩
    · push Not at hOn
      rw [MathForest.applyStepsDelta_of_not_mem hV hPath δ he hOn]
      exact ⟨(hStrict e he).1,hf,hFor,hBack⟩
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    obtain ⟨_,hp,hq⟩ := hStrict u.edge (hw.mem_edges u hu)
    have hb := hAvail u hu
    cases hf : u.fwd
    · simp [PathStep.dirAvail,PathStep.flip,ForestEdge.addFlow,hf] at hb ⊢
      exact ⟨by linarith only [hb],by linarith only [hδ,hp]⟩
    · simp [PathStep.dirAvail,PathStep.flip,ForestEdge.addFlow,hf] at hb ⊢
      exact ⟨by linarith only [hb],by linarith only [hδ,hq]⟩

end MinCostFlow.IPM.Machine
