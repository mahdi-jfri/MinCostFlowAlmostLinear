module

public import MinCostFlow.HierPaths.BuildProgChoiceLoop

/-!
# The model history of a completed RAM loop

Every choice recorded by the scan is certified for its child's graph.
Decisions are reindexed by original child number, and a skipped iteration
leaves each saved child where it was.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- With no active child, all child certificates are already saved. -/
theorem ChoiceLoopData.saved_of_empty {D : ChoiceLoopData} {sts : ℕ → ChildState}
    (h : (D.round sts).jobs.count = 0) :
    ∀ c < D.count, ∃ T, (sts c).saved = some T := by
  intro c hc
  cases he : (sts c).saved with
  | some T => exact ⟨T,rfl⟩
  | none =>
    have hm : c ∈ activeChildren D.count sts := by simp [activeChildren,hc,he]
    have hLen : (activeChildren D.count sts).length = 0 := h
    exact False.elim (List.not_mem_nil ((List.length_eq_zero_iff.mp hLen) ▸ hm))

/-- The model game leaves its state unchanged once no child is active. -/
theorem ChoiceLoopData.next_of_empty {D : ChoiceLoopData} {sts : ℕ → ChildState}
    (h : (D.round sts).jobs.count = 0) (ans : ℕ → CoreResult) : D.next sts ans = sts := by
  funext c
  unfold ChoiceLoopData.next choiceGameRound
  by_cases hc : c < D.count
  · obtain ⟨T,hT⟩ := D.saved_of_empty h c hc
    simp [hc,childStepAnswer,hT]
  · simp [hc]

/-- Reindex the certified replies from the active table to the original children. -/
theorem ChoiceLoopData.certify_children {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult}
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i)) :
    ∀ c < D.count, (sts c).saved = none →
      CoreOutcomeSpec ParamConfig.default D.base.M (coreLevel D.base.M D.base.r D.base.childSize)
        (gameGraph D.base.childSize (sts c)) (answerByChild D.count sts answer c) := by
  intro c hc ha
  let l := activeChildren D.count sts
  have hMem : c ∈ l := by simp [l,activeChildren,hc,ha]
  let i := l.idxOf c
  have hi : i < l.length := List.idxOf_lt_length_of_mem hMem
  have hc' : l.getD i 0 = c := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_idxOf hi
  have hHere := hCert i hi
  change CoreOutcomeSpec ParamConfig.default D.base.M (coreLevel D.base.M D.base.r D.base.childSize)
    (gameGraph D.base.childSize (sts (l.getD i 0))) (answer i) at hHere
  rw [hc'] at hHere
  exact hHere

/-- A trace of the RAM loop is a run of the certified child-game model. -/
theorem ChoiceLoopTrace.certified {w : ℕ} {D : ChoiceLoopData} {initial mem : ℕ → ℕ}
    {t heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) :
    CertifiedGame D.base.route D.base.host D.base.verts D.base.M D.base.r D.base.Δ D.base.L
      D.base.childSize D.count D.offset t sts := by
  induction hTrace with
  | start => exact .start
  | @skip t heap sts mem tr hn ih =>
    let ans : ℕ → CoreResult := fun _ => .expander ∅
    have h : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
        (D.round sts).q ((D.round sts).jobs.graph i) (ans i) := by
      intro i hi
      rw [hn] at hi
      exact (Nat.not_lt_zero i hi).elim
    have hStep := CertifiedGame.step ih _ (D.certify_children h)
    have he := D.next_of_empty hn ans
    exact he ▸ hStep
  | run _ _ ans _ _ hc _ _ _ ih =>
    exact .step ih (answerByChild D.count _ ans) (D.certify_children hc)

/-- Termination of a RAM game follows from the certified round bound. -/
theorem ChoiceLoopTrace.done {w : ℕ} {D : ChoiceLoopData} {initial mem : ℕ → ℕ}
    {heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem)
    (hRouter : IsMatchingPlayer D.base.route D.base.routeCost)
    (hHost : HostPre D.base.host D.base.verts D.base.Δ D.base.L)
    {β : ℝ} (hβ : 0 < β) (hExp : D.base.host.IsExpansionExpanderOn D.base.verts β) {bh : ℕ}
    (hBh : max 2 (2/β) ≤ (bh:ℝ))
    (hChildren : IsChildren D.base.verts (fun c => shiftSet (D.offset c) (Finset.range D.base.childSize))
      D.count D.base.childSize)
    (heven : D.base.childSize%2=0) (hq : coreLevel D.base.M D.base.r D.base.childSize ≤ D.base.r)
    (hLog : D.base.childSize < 2^D.L') :
    (D.round sts).jobs.count = 0 := by
  obtain ⟨hInv,_⟩ := hTrace.certified.invariant hRouter hHost hβ hExp hBh hChildren heven hq
  have hDone := CertifiedGame.all_saved hChildren.1 hLog hInv
  change (activeChildren D.count sts).length = 0
  rw [List.length_eq_zero_iff,activeChildren,List.filter_eq_nil_iff]
  intro c hc ha
  obtain ⟨T,he⟩ := hDone c (List.mem_range.mp hc)
  simp [he] at ha

end MinCostFlow.HierPaths
