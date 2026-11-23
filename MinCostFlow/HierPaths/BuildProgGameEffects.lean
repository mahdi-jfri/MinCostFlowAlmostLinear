module

public import MinCostFlow.HierPaths.BuildProgGamePlayerBounds

/-!
# Memory effects of the game round

The common application scan changes only the selected child reservations
below the reply pointers. The record contains the new walks in the order
of their matching rows.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The walk directory and arena start for a matched round. -/
def BuildRoundData.walkBases (B : BuildRoundData) (A : BuildRoundAddrs)
    (Ms : List (List (ℕ × ℕ))) : ℕ × ℕ :=
  let dir := B.routedEnd A + 4
  (dir,dir + Ms.flatten.length + B.pathBound + 1 + B.host.n)

/-- A cell is outside the child graph writes of the round. -/
def BuildRoundData.unchangedBelow (B : BuildRoundData) (a : ℕ) : Prop :=
  B.indices.isEmpty = true ∨
    ∀ Ms emb, B.result.1 = .matched Ms emb →
      ∀ i < Ms.length, a < (B.applyData Ms emb).addr i ∨ (B.applyData Ms emb).cap i ≤ a

/-- The completed common round gives all rows with their graphs and walks, and
keeps the prefix outside the updated graphs. -/
theorem roundEffects_of_post {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem after : ℕ → ℕ} {v : ℕ} (hFit : BuildRoundFit w B A mem)
    (hPost : (buildOneRoundContract w B).post (B.args A) mem v after) :
    (∀ a < A.replies, B.unchangedBelow a → after a = mem a) ∧
    (∀ a, A.replies + B.jobs.count + 1 ≤ a → a < A.heap → after a = mem a) ∧
    (B.indices.isEmpty = false →
      ∃ Ms emb, B.result.1 = .matched Ms emb ∧
        ∀ i < Ms.length, (B.applyData Ms emb).RowAt after (B.walkBases A Ms).1 (B.walkBases A Ms).2 i) := by
  obtain ⟨A',m₁,m₂,mid,he,hS,hR,hF⟩ := hPost
  have ha : A = A' := by
    cases A
    cases A'
    simp only [BuildRoundData.args,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    rfl
  subst A'
  obtain ⟨_,_,_,_,hse,_,_,hSF,_,_⟩ := hS
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at hse
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hse
  obtain ⟨_,_,_,_,hre,hRoute,_,hRF,_⟩ := hR
  simp only [BuildRoundData.routeArgs,List.cons.injEq,and_true,true_and] at hre
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hre
  have hHeap : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hRP : A.replies ≤ B.prepared A := by
    obtain ⟨_,_,_,_,hEq,_,_,hRE,_,_,_,_,_,_,_⟩ := hFit.scan
    simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at hEq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := hEq
    omega
  have hMem (a : ℕ) (ha : a < A.replies) : m₂ a = mem a :=
    (hRF a (ha.trans_le hRP)).trans (hSF.1 a ha)
  by_cases hempty : B.indices.isEmpty
  · simp [roundFinishPost,hempty] at hF
    refine ⟨fun a ha _ => ?_,fun a hlo hhi => ?_,by simp [hempty]⟩
    · rw [hF.2]
      exact hMem a ha
    · rw [hF.2]
      exact (hRF a (hhi.trans_le hHeap)).trans (hSF.2 a hlo hhi)
  · obtain ⟨hmid,Ms,emb,hRes,hApply⟩ := by
      simpa [roundFinishPost,hempty] using hF
    subst mid
    obtain ⟨rep,idx,graphs,offs,ends,cap,heap,eq,hPost⟩ := hApply
    simp only [BuildRoundData.finishArgs,List.cons.injEq,and_true] at eq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_,rfl,rfl,_⟩ := eq
    obtain ⟨mt,tb,idx,graphs,offs,tmp,ends,vs,P,dir,out,he,_,_,_,hKeep,hRows⟩ := hPost
    simp only [finishBatchApplyArgs,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    have hBelow : B.prepared A ≤ B.routedEnd A := by
      simp only [BuildRoundData.routedEnd,BuildRoundData.routeReply,buildBatchEnd]
      omega
    refine ⟨?_,?_,fun _ => ⟨Ms,emb,hRes,hRows⟩⟩
    · intro a ha hSafe
      obtain hFalse | hApart := hSafe
      · exact False.elim (hempty hFalse)
      · exact (hKeep a ⟨ha.trans_le (hRP.trans hBelow),hApart Ms emb hRes⟩).trans (hMem a ha)
    · intro a hlo hhi
      have hCell := hKeep a ⟨hhi.trans_le (hHeap.trans hBelow),fun i hi => Or.inr
        (((hFit.reserved Ms emb (Bool.eq_false_iff.mpr hempty) hRes).1.spend i hi).trans (by omega))⟩
      exact hCell.trans ((hRF a (hhi.trans_le hHeap)).trans (hSF.2 a hlo hhi))

end MinCostFlow.HierPaths
