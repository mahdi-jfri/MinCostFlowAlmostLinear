module

public import MinCostFlow.HierPaths.BuildProgOneRoundSpec

/-!
# Retaining the information from a completed game round

Applying the matchings changes the child graph intervals, but keeps the
core replies, the cut list, and both active input arrays. This is the
information needed to save certificates and compact the active list.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The active arrays and reply blocks available to the next game step. -/
structure OneRoundMemory (B : BuildRoundData) (A : BuildRoundAddrs)
    (mem' : ℕ → ℕ) (v : ℕ) : Prop where
  graphs : ListAt mem' A.graphs (tabList B.jobs.count B.jobs.addr)
  offsets : ListAt mem' A.offsets (tabList B.jobs.count B.jobs.offset)
  replies : GameRepliesAt B.jobs B.core B.q A.heap A.replies mem'
  count : mem' (B.prepared A) = B.indices.length
  indices : ListAt mem' (B.prepared A + 1) B.indices
  preparedEnd : B.prepared A + 1 + B.indices.length ≤ v
  zero : ZeroFrom mem' v

private theorem row_frame_lower {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem₂ mem' : ℕ → ℕ} {mid v : ℕ} (hFit : BuildRoundFit w B A mem)
    (hRowsCount : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
      Ms.length = B.indices.length)
    (hTail : roundFinishPost w B A mid mem₂ mem' v)
    (hRound : RoundRouteAt B.jobs B.core B.q B.childSize (B.prepared A) mid B.result.1 mem₂) :
    mid ≤ v ∧ (∀ a, A.replies ≤ a → a < mid → mem' a = mem₂ a) ∧
    (∀ a < A.replies, (∀ i < B.jobs.count, a < B.jobs.addr i) → mem' a = mem₂ a) ∧
    (ZeroFrom mem₂ mid → ZeroFrom mem' v) := by
  by_cases hne : B.indices.isEmpty
  · simp only [roundFinishPost,hne,ite_true] at hTail
    obtain ⟨rfl,rfl⟩ := hTail
    exact ⟨le_rfl,fun _ _ _ => rfl,fun _ _ _ => rfl,id⟩
  · simp only [roundFinishPost,hne] at hTail
    obtain ⟨hEq,Ms,emb,hRes,hApply⟩ := hTail
    subst mid
    let D := B.applyData Ms emb
    obtain ⟨rep,idx,graphs,offs,ends,cap,heap,he,hPost⟩ := hApply
    simp only [BuildRoundData.finishArgs,List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_,rfl,rfl,_⟩ := he
    obtain ⟨mt,tb,idx,graphs,offs,tmp,ends,vs,P,dir,out,he,hEnd,hZero,hPos,hKeep,hRows⟩ := hPost
    simp only [finishBatchApplyArgs,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    have hStart : B.routedEnd A ≤ v := by
      have hh := D.cursor_mono (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n)
        (Nat.zero_le Ms.length)
      change B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n ≤ _ at hh
      change v = D.cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n) Ms.length at hEnd
      omega
    refine ⟨hStart,?_,?_,fun _ => hZero⟩
    · intro a hlo hhi
      apply hKeep a
      refine ⟨hhi,fun i hi => Or.inr ?_⟩
      exact ((hFit.reserved Ms emb (Bool.eq_false_iff.mpr hne) hRes).1.spend i hi).trans hlo
    · intro a ha hb
      apply hKeep a
      have hr : A.replies ≤ B.routedEnd A := by
        have hs := hFit.scan
        obtain ⟨g,o,h,r,eq,_,_,hAlloc,_,_,_⟩ := hs
        simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at eq
        obtain ⟨rfl,rfl,rfl,rfl⟩ := eq
        have hPrep : A.heap ≤ B.prepared A :=
          B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
        unfold BuildRoundData.routedEnd BuildRoundData.routeReply buildBatchEnd
        omega
      refine ⟨ha.trans_le hr,fun i hi => Or.inl (hb (D.child i) ?_)⟩
      have hInd : D.indices.length = D.matchings.length := (hRowsCount Ms emb (Bool.eq_false_iff.mpr hne) hRes).symm
      have hi' : i < D.indices.length := by
        change i < D.matchings.length at hi
        omega
      have hx : D.child i ∈ B.indices := by
        change D.indices.getD i 0 ∈ D.indices
        rw [List.getD_eq_getElem _ _ hi']
        exact List.getElem_mem _
      exact (mem_batchJobIndices.mp hx).1

/-- A complete round leaves the core certificates and cut indices readable. -/
theorem oneRoundMemory_of_post {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem' : ℕ → ℕ} {v : ℕ} (hFit : BuildRoundFit w B A mem)
    (hRowsCount : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb → Ms.length = B.indices.length)
    (hPost : (buildOneRoundContract w B).post (B.args A) mem v mem') :
    OneRoundMemory B A mem' v := by
  obtain ⟨A',mem₁,mem₂,mid,he,hSP,hRP,hTail⟩ := hPost
  have hEq : A = A' := by
    cases A
    cases A'
    simp only [BuildRoundData.args,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    rfl
  subst A'
  obtain ⟨_,_,_,_,hse,_,_,hSPF,hRepEnd,hReplies⟩ := hSP
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at hse
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hse
  obtain ⟨_,_,_,_,hre,hRoute,_,hRPF,hZero⟩ := hRP
  simp only [BuildRoundData.routeArgs,List.cons.injEq,and_true,true_and] at hre
  obtain ⟨rfl,rfl,rfl,rfl⟩ := hre
  obtain ⟨hm,hUpper,hLower,hZero'⟩ := row_frame_lower hFit hRowsCount hTail hRoute
  have hPrep : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hk := List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
    (List.range B.jobs.count)
  rw [List.length_range] at hk
  change B.indices.length ≤ B.jobs.count at hk
  have hMid : B.prepared A + 1 + B.indices.length ≤ mid := by
    have hp := hRoute.2.2
    change (if B.indices.isEmpty then mid = B.prepared A + 1 + B.jobs.count
      else _ ∧ _ ∧ B.routeReply A + (routeResultWords B.result.1).length ≤ mid) at hp
    split at hp
    · omega
    · have hR := hp.2.2
      unfold BuildRoundData.routeReply buildBatchEnd at hR
      omega
  have hs := hFit.scan
  obtain ⟨_,_,_,_,he,hGraphsEnd,hOffsetsEnd,hRepliesEnd,_,_,_,_,hG,hO,_⟩ := hs
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hlo (a : ℕ) (ha : a < A.replies) (hb : ∀ i < B.jobs.count, a < B.jobs.addr i) :
      mem' a = mem a :=
    (hLower a ha hb).trans ((hRPF a (by omega)).trans (hSPF.1 a ha))
  have hr (a : ℕ) (ha : A.replies ≤ a) (hb : a < B.prepared A) :
      mem' a = mem₁ a := (hUpper a ha (by omega)).trans (hRPF a hb)
  have hGraphTab : ListAt mem' A.graphs (tabList B.jobs.count B.jobs.addr) :=
    WordRAM.ListAt.congr hG fun a _ ha => by
      rw [length_tabList] at ha
      exact hlo a (ha.trans_le hGraphsEnd) fun i hi => ha.trans_le (hFit.beforeGraph i hi).1
  have hOffsetTab : ListAt mem' A.offsets (tabList B.jobs.count B.jobs.offset) :=
    WordRAM.ListAt.congr hO fun a _ ha => by
      rw [length_tabList] at ha
      exact hlo a (ha.trans_le hOffsetsEnd) fun i hi => ha.trans_le (hFit.beforeGraph i hi).2
  have hCore : GameRepliesAt B.jobs B.core B.q A.heap A.replies mem' := by
    refine ⟨(hr _ (by omega) (by omega)).trans hRepEnd, ?_⟩
    intro i hi
    obtain ⟨hPtr,hBlock⟩ := hReplies i hi
    have hHead : A.heap ≤ B.jobs.prepPrefix B.core B.q A.heap i :=
      B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le i)
    have hEnd : B.jobs.prepPrefix B.core B.q A.heap (i + 1) ≤ B.prepared A :=
      B.jobs.prepPrefix_mono B.core B.q A.heap (by omega)
    refine ⟨(hr _ (by omega) (by omega)).trans hPtr,
      hBlock.frame (fun a ha hb => hr a (by omega) (hb.trans_le hEnd)) ?_⟩
    intro U hu
    rw [hFit.childSize i hi]
    exact hFit.sets i hi U hu
  have hCount : mem₂ (B.prepared A) = B.indices.length := hRoute.1
  have hIdx : ListAt mem₂ (B.prepared A + 1) B.indices := hRoute.2.1
  refine ⟨hGraphTab,hOffsetTab,hCore,(hUpper _ (by omega) (by omega)).trans hCount,
    WordRAM.ListAt.congr hIdx (fun a lo hi => hUpper a (by omega) (hi.trans_le hMid)),
    hMid.trans hm,hZero' hZero⟩

end MinCostFlow.HierPaths
