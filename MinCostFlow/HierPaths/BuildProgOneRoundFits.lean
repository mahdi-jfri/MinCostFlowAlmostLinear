module

public import MinCostFlow.HierPaths.BuildProgOneRound

/-!
# The memory passed between common-round phases

The scan preserves the parent and active tables. Its replies supply the
routing phase. A matched routing phase preserves the original input
regions, then adds the cut indices and the router's two result tables.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private theorem round_scan_pre_refs {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs} {mem : ℕ → ℕ}
    (hPre : BuildRoundFit w B A mem) :
    A.replies + B.jobs.count + 1 ≤ A.heap ∧
    ListAt mem A.graphs (tabList B.jobs.count B.jobs.addr) ∧
    ListAt mem A.offsets (tabList B.jobs.count B.jobs.offset) ∧
    ∀ i < B.jobs.count, GraphAt mem (B.jobs.addr i) (B.jobs.graph i) ∧
      B.jobs.addr i + (B.jobs.graph i).encode.length ≤ A.replies := by
  have hs := hPre.scan
  change (buildGameScanContract ..).pre _ _ at hs
  obtain ⟨graphs, offsets, h, rep, he, _, _, hHeap, _, _, _, _, hG, hO, hJobs⟩ := hs
  simp only [BuildRoundData.scanArgs, List.cons.injEq, and_true, true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  exact ⟨hHeap,hG,hO,fun i hi => ⟨(hJobs i hi).1.1, (hJobs i hi).1.2.1⟩⟩

/-- The scan's reply table and preserved input regions satisfy the routing precondition. -/
theorem roundRoute_pre_after_scan {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem₁ : ℕ → ℕ} (hPre : BuildRoundFit w B A mem)
    (hScan : (B.scanContract w).post (B.scanArgs A) mem (B.prepared A) mem₁) :
    (B.routeContract w).pre (B.routeArgs A) mem₁ := by
  obtain ⟨hHeap, _, _, _⟩ := round_scan_pre_refs hPre
  obtain ⟨graphs,offsets,h,rep,he,_,hZ,hFrame,hReplyEnd,hReply⟩ := hScan
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hPrep : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hHost := hPre.hostBelow
  have hVerts := hPre.vertsBelow
  have hRoom := hPre.routeWord
  have hk : B.pairs.length = B.indices.length := length_batchJobPairs ..
  unfold BuildRoundData.routeReply at hRoom
  rw [← hk] at hRoom
  exact ⟨A.replies,A.host,A.verts,A.heap,B.prepared A,rfl,⟨hReplyEnd,hReply⟩,hHeap,le_rfl,hZ,
    WordRAM.ListAt.congr hPre.host (fun a _ ha => hFrame.1 a (ha.trans_le hHost)), hPre.hostValid,
    WordRAM.ListAt.congr hPre.verts (fun a _ ha => hFrame.1 a (ha.trans_le hVerts)),
    by omega,by omega,hPre.router,hPre.bits,hRoom,hPre.even,hPre.childSize,hPre.sets⟩

private theorem round_host_edges {G : Graph} {mem : ℕ → ℕ} {h : ℕ} (hAt : GraphAt mem h G) :
    ListAt mem (h + 2) (G.edges.flatMap fun e => [e.1, e.2]) := by
  change ListAt mem h ([G.n,G.m] ++ G.edges.flatMap fun e => [e.1,e.2]) at hAt
  exact (listAt_append.mp hAt).2

/-- When the batch is nonempty, the router's result and the graph reservations
supply the input to the matching-application phase. -/
theorem roundFinish_pre_after_route {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem₁ mem₂ : ℕ → ℕ} {mid : ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hPre : BuildRoundFit w B A mem) (hk : B.indices.isEmpty = false)
    (hRes : B.result.1 = .matched Ms emb)
    (hMatched : RouteMatchedSpec B.host B.verts B.pairs B.Δ B.L B.result.2 0 Ms emb)
    (hScan : (B.scanContract w).post (B.scanArgs A) mem (B.prepared A) mem₁)
    (hRoute : (B.routeContract w).post (B.routeArgs A) mem₁ mid mem₂)
    (hEnd : mid = B.routedEnd A) :
    mem₂ (B.prepared A) = B.indices.length ∧ mem₂ A.host = B.host.n ∧
    (buildFinishBatchContract w (B.applyData Ms emb)).pre (B.finishArgs A) mem₂ := by
  let D := B.applyData Ms emb
  let p := B.prepared A
  let rep := B.routeReply A
  let e := B.routedEnd A
  obtain ⟨hHeap,hGraphTab,hOffTab,hOld⟩ := round_scan_pre_refs hPre
  obtain ⟨_,_,_,_,he,_,hZ,hFrame₁,_,_⟩ := hScan
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  obtain ⟨_,_,_,_,he',hRound,_,hFrame₂,hZero₂⟩ := hRoute
  simp only [BuildRoundData.routeArgs,List.cons.injEq,and_true,true_and] at he'
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he'
  have hPrep : A.heap ≤ p := B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hBelow : ∀ a < A.replies, mem₂ a = mem a := fun a ha =>
    (hFrame₂ a (by omega)).trans (hFrame₁.1 a ha)
  have hHost : GraphAt mem₂ A.host B.host :=
    WordRAM.ListAt.congr hPre.host (fun a _ ha => hBelow a (ha.trans_le hPre.hostBelow))
  have hHostN : mem₂ A.host = B.host.n := hHost 0 (by simp [Graph.encode])
  change RoundRouteAt B.jobs B.core B.q B.childSize p mid B.result.1 mem₂ at hRound
  obtain ⟨hN,hIdx,hReply⟩ := hRound
  have hN' : mem₂ p = B.indices.length := hN
  have hIdx' : ListAt mem₂ (p + 1) B.indices := hIdx
  change (if B.indices.isEmpty then _ else mem₂ _ = mid ∧
    ListAt mem₂ rep (routeResultWords B.result.1) ∧ rep + (routeResultWords B.result.1).length ≤ mid) at hReply
  simp only [hk, Bool.false_eq_true, ite_false] at hReply
  obtain ⟨_,hAt,_⟩ := hReply
  have hMat : ListAt mem₂ rep (routeResultWords (.matched Ms emb)) := hRes ▸ hAt
  have hm : Ms.length = B.indices.length :=
    hMatched.1.trans (length_batchJobPairs ..)
  have hChild (i : ℕ) (hi : i < Ms.length) : D.child i < B.jobs.count := by
    have hLt : i < B.indices.length := by omega
    have hm : B.indices.getD i 0 ∈ B.indices := by
      rw [List.getD_eq_getElem _ _ hLt]
      exact List.getElem_mem _
    exact (mem_batchJobIndices.mp hm).1
  have hAddr (i : ℕ) (hi : i < Ms.length) : D.addr i ≤ A.replies := by
    have he := (hOld (D.child i) (hChild i hi)).2
    change D.addr i + (D.graph i).encode.length ≤ A.replies at he
    omega
  have hChildAt (i : ℕ) (hi : i < Ms.length) : GraphAt mem₂ (D.addr i) (D.graph i) := by
    obtain ⟨hAt,hEnd⟩ := hOld (D.child i) (hChild i hi)
    exact WordRAM.ListAt.congr hAt (fun a _ ha => hBelow a (ha.trans_le hEnd))
  obtain ⟨hKeep,hLocal,hWord⟩ := hPre.reserved Ms emb hk hRes
  have hRep : p + 1 + B.indices.length ≤ rep := by
    have hk := List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
      (List.range B.jobs.count)
    rw [List.length_range] at hk
    change B.indices.length ≤ B.jobs.count at hk
    dsimp [rep,BuildRoundData.routeReply,buildBatchEnd,p]
    omega
  have hRepLo : A.replies ≤ rep := by omega
  have hGraphTab₂ : ListAt mem₂ A.graphs (tabList D.jobs.count D.jobs.addr) :=
    WordRAM.ListAt.congr hGraphTab fun a _ ha => hBelow a (by
      obtain ⟨g,o,h,rep,he,hGO,_,_⟩ := hPre.scan
      simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      rw [length_tabList] at ha; exact ha.trans_le hGO)
  have hOffTab₂ : ListAt mem₂ A.offsets (tabList D.jobs.count D.jobs.offset) :=
    WordRAM.ListAt.congr hOffTab fun a _ ha => hBelow a (by
      obtain ⟨g,o,h,rep,he,_,hOO,_⟩ := hPre.scan
      simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      rw [length_tabList] at ha; exact ha.trans_le hOO)
  have hTables : ApplyBatchTables D mem₂ (p + 1) A.graphs A.offsets := by
    refine ⟨hIdx',hGraphTab₂,hOffTab₂,hm.symm,hChild,fun i hi => Or.inr ?_,
      fun i hi => hPre.beforeGraph (D.child i) (hChild i hi)⟩
    have hc := hKeep.spend i hi
    change D.cap i ≤ A.replies at hc
    omega
  have hRegions : FinishChildRegions w D (A.host + 2) rep :=
    ⟨hKeep.parent,fun i hi => (hKeep.spend i hi).trans hRepLo,hKeep.apart,hKeep.offsets⟩
  have hMatEnd : rep + (routeResultWords (.matched Ms emb)).length ≤ e := by
    dsimp [e,BuildRoundData.routedEnd,rep]
    rw [hRes]
    omega
  have hFinish := buildFinishBatch_pre_of_matched (D := D) (cap := B.pathBound) hMat hMatEnd
    ((show mid = e from hEnd) ▸ hZero₂) hPre.hostValid hMatched hPre.router.1 hPre.router.2.2.2.2.2.2
    (hPre.lastBound hk) hTables hRep hRegions (round_host_edges hHost) hChildAt hLocal hWord
  change (buildFinishBatchContract w D).pre
    [rep,p + 1,A.graphs,A.offsets,A.host + 2,B.host.n,B.pathBound,e,Ms.length] mem₂ at hFinish
  rw [hm] at hFinish
  exact ⟨hN',hHostN,hFinish⟩

end MinCostFlow.HierPaths
