module

public import MinCostFlow.Rounding.Algorithm
import Mathlib.Tactic

/-!
# The zero-availability branch of path cleanup

A path minimum comes from a live edge. Its directional availability
is nonnegative, so the machine's exact zero test selects the same
branch as the model's positive-availability test.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The minimum report belongs to the path and has nonnegative
availability. Its identifier indexes the working flow table. -/
theorem roundCleanup_hit {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {s : D.State} {a b : ℕ} {steps : List PathStep}
    (hInv : D.Inv s) (hfs : findSteps (D.toForest s).edges a b = some steps)
    (hWeak : ∀ e ∈ (D.toForest s).edges, ForestEdgeWeakInv I f e)
    (hAvail : ∀ t ∈ steps, 0 ≤ t.dirAvail)
    {hit : PathHit} (hHit : D.pathMin s a b=some hit) :
    0 ≤ hit.avail ∧ hit.eid<I.m ∧ hit.x<(D.toForest s).n ∧ hit.y<(D.toForest s).n ∧
      (hit.avail≠0 ↔ 0<hit.avail) := by
  have hValid := hD.2.1 s hInv
  obtain ⟨hw,_⟩ := findSteps_sound hValid.2.1 hfs
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  have hEq := hD.2.2.2.2.2.2.1 s a b hInv hConn
  rw [hEq,MathForest.pathMin,hfs,Option.bind_some] at hHit
  obtain ⟨pre,t,post,hsplit,htHit,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    MathForest.cut_of_pathMin hValid hfs hHit
  have ht : t∈steps := by rw [hsplit]; simp
  have he := hWeak t.edge (hw.mem_edges t ht)
  have hav : 0≤hit.avail := by rw [← htHit]; exact hAvail t ht
  have hid : hit.eid<I.m := by rw [← htHit]; exact he.eid_lt
  have hends := hValid.1 t.edge (hw.mem_edges t ht)
  have hxy : hit.x<(D.toForest s).n ∧ hit.y<(D.toForest s).n := by
    rw [← htHit]
    cases ht' : t.fwd
    · exact ⟨by simpa [PathStep.toHit,PathStep.src,ht'] using hends.2.1,
        by simpa [PathStep.toHit,PathStep.dst,ht'] using hends.1⟩
    · exact ⟨by simpa [PathStep.toHit,PathStep.src,ht'] using hends.1,
        by simpa [PathStep.toHit,PathStep.dst,ht'] using hends.2.1⟩
  exact ⟨hav,hid,hxy.1,hxy.2,⟨fun hn => lt_of_le_of_ne hav (Ne.symm hn),ne_of_gt⟩⟩

/-- The cut splits the path into two legal recursive calls. The
second path survives any first call that preserves off-path edges. -/
theorem roundCleanup_split {D : DynForest} (hD : D.IsSpec)
    {s : D.State} {a b fuel : ℕ} {steps : List PathStep} {hit : PathHit}
    (hInv : D.Inv s) (hfs : findSteps (D.toForest s).edges a b=some steps)
    (hFuel : (D.toForest s).edges.length<fuel+1)
    (hHit : D.pathMin s a b=some hit) :
    let cut := D.cut s hit.x hit.y
    ∃ pre post,
      D.Inv cut ∧ (D.toForest cut).n=(D.toForest s).n ∧
      (D.toForest cut).edges.length+1=(D.toForest s).edges.length ∧
      (D.toForest cut).edges.length<fuel ∧
      (∀ e∈(D.toForest cut).edges,e∈(D.toForest s).edges) ∧
      findSteps (D.toForest cut).edges a hit.x=some pre ∧
      (∀ t∈pre,t∈steps) ∧ (∀ t∈post,t∈steps) ∧
      (∀ s' : D.State, D.Inv s' →
        (∀ e∈(D.toForest cut).edges,(∀ t∈pre,t.edge≠e) → e∈(D.toForest s').edges) →
        findSteps (D.toForest s').edges hit.y b=some post) := by
  have hValid := hD.2.1 s hInv
  obtain ⟨hw,hnd⟩ := findSteps_sound hValid.2.1 hfs
  have hConn : (D.toForest s).SameComp a b := ⟨_,hw.to_isWalk⟩
  rw [hD.2.2.2.2.2.2.1 s a b hInv hConn,MathForest.pathMin,hfs,Option.bind_some] at hHit
  obtain ⟨pre,t,post,hsplit,_,_,_,hValidCut,hmem,_,hlen,hpre,hpost,_,_,_⟩ :=
    MathForest.cut_of_pathMin hValid hfs hHit
  obtain ⟨hi,hsame⟩ := hD.2.2.2.2.1 s hit.x hit.y hInv
  have hV' := hD.2.1 _ hi
  have heq := hsame.2.length_eq
  refine ⟨pre,post,hi,hsame.1,by omega,by omega,?_,?_,?_,?_,?_⟩
  · intro e he
    exact (hmem e (hsame.2.subset he)).1
  · rw [hsame.findSteps_eq hV']
    exact hpre
  · intro u hu
    rw [hsplit]
    exact List.mem_append_left _ hu
  · intro u hu
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hu)
  · intro s' hi' hkeep
    obtain ⟨hwalk,hndPost⟩ := findSteps_sound hValidCut.2.1 hpost
    refine MathForest.findSteps_eq_of_isStepWalk (hD.2.1 s' hi')
      (hwalk.mono_of_mem ?_) hndPost
    intro v hv
    apply hkeep v.edge (hsame.2.symm.subset (hwalk.mem_edges v hv))
    intro u hu hEq
    rw [hsplit,List.map_append,List.map_cons] at hnd
    have hdisj := List.disjoint_of_nodup_append hnd
    have hu' : u.edge.toRaw∈pre.map PathStep.toRaw := List.mem_map_of_mem hu
    have hv' : u.edge.toRaw∈t.edge.toRaw::post.map PathStep.toRaw :=
      List.mem_cons_of_mem _ (hEq ▸ List.mem_map_of_mem hv)
    exact hdisj hu' hv'

/-- Cleanup keeps the vertex universe even when its recursion
removes every edge of a component. -/
theorem roundCleanup_n {D : DynForest} (hD : D.IsSpec) {I : Instance}
    (f : Fin I.m → ℚ) :
    ∀ fuel s arr counts rats a b steps,
      D.Inv s → findSteps (D.toForest s).edges a b=some steps →
      (D.toForest s).edges.length<fuel →
      (∀ e∈(D.toForest s).edges,ForestEdgeWeakInv I f e) →
      (∀ t∈steps,0≤t.dirAvail ∧ 0<t.flip.dirAvail) →
      (D.toForest (removeZeroEdges D I s arr counts rats a b fuel).1).n=(D.toForest s).n := by
  intro fuel
  induction fuel with
  | zero =>
    intro s arr cnt rats a b steps hInv hPath hFuel
    omega
  | succ fuel ih =>
    intro s arr cnt rats a b steps hInv hPath hFuel hWeak hBounds
    rw [removeZeroEdges]
    cases hh : D.pathMin s a b with
    | none => rfl
    | some hit =>
      dsimp only
      by_cases hp : 0<hit.avail
      · rw [ite_eq_left hp]
      · rw [ite_eq_right hp]
        obtain ⟨pre,post,hInv',hn',_,hFuel',hSub,hPre,hInPre,hInPost,hPost⟩ :=
          roundCleanup_split hD hInv hPath hFuel hh
        let cut := D.cut s hit.x hit.y
        let arr' := fun j : Fin I.m => if j.val=hit.eid then hit.flow else arr j
        let cnt' := { cnt with pathMinOps := cnt.pathMinOps+1,cutOps := cnt.cutOps+1, otherSteps := cnt.otherSteps+3 }
        let rats' := hit.flow::hit.avail::rats
        let first := removeZeroEdges D I cut arr' cnt' rats' a hit.x fuel
        have hWeak' : ∀ e∈(D.toForest cut).edges,ForestEdgeWeakInv I f e :=
          fun e he => hWeak e (hSub e he)
        have hb' : ∀ t∈pre,0≤t.dirAvail ∧ 0<t.flip.dirAvail :=
          fun t ht => hBounds t (hInPre t ht)
        obtain ⟨hFirst,_,hSub₁,hKeep,_,_,_,_,_,_,_,_,_,hLen,_,_,_,_,_,_⟩ :=
          removeZeroEdges_spec hD (f:=f) fuel cut arr' cnt' rats' a hit.x pre hInv' hPre hFuel' hWeak' hb'
        have hFirstN := ih cut arr' cnt' rats' a hit.x pre hInv' hPre hFuel' hWeak' hb'
        have hSecondN := ih first.1 first.2.1 first.2.2.1 first.2.2.2 hit.y b post
          hFirst (hPost first.1 hFirst hKeep) (hLen.trans_lt hFuel')
          (fun e he => hWeak' e (hSub₁ e he)) (fun t ht => hBounds t (hInPost t ht))
        exact hSecondN.trans (hFirstN.trans hn')

end MinCostFlow.IPM.Machine
