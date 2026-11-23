module

public import MinCostFlow.HierPaths.BuildProgOneRoundFits

/-!
# Verification of a common child-game round

The round connects the three calls through their memory contracts. The
router is called once for the batch (with its own retries). The matching
application reads the router reply when there is a cut, and is skipped
when all replies are certificates.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private theorem routeArgs_word {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    (hWords : ∀ a ∈ B.args A, a < 2 ^ w) (hp : B.prepared A < 2 ^ w) :
    ∀ a ∈ B.routeArgs A, a < 2 ^ w := by
  intro a ha
  simp only [BuildRoundData.routeArgs,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hp | exact hWords _ (by simp [BuildRoundData.args])

private theorem round_addresses {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem : ℕ → ℕ} (hFit : BuildRoundFit w B A mem) :
    let p := B.prepared A
    let k := B.indices.length
    let s := B.childSize
    let batch := p + 1 + B.jobs.count
    p < 2 ^ w ∧ p + 1 < 2 ^ w ∧ batch < 2 ^ w ∧
    k + k < 2 ^ w ∧ batch + (k + k) < 2 ^ w ∧ batch + (k + k) + 1 < 2 ^ w ∧
    k * s < 2 ^ w ∧ batch + (k + k) + 1 + k * s < 2 ^ w := by
  have h := hFit.routeWord
  unfold BuildRoundData.routeReply buildBatchEnd at h
  dsimp only
  omega

/-- The cost of the round after the core scan, including unpacking the result. -/
@[expose] def buildOneRoundTailCost (w : ℕ) (B : BuildRoundData) : ℕ :=
  (B.routeContract w).cost [] (fun _ => 0) +
    (match B.result.1 with
     | .matched Ms emb => (buildFinishBatchContract w (B.applyData Ms emb)).cost [] (fun _ => 0)
     | .cut _ => 0) + 110

set_option maxHeartbeats 600000 in
/-- The tail proof uses the memory left by the scan. Its replies may be the
actual certified choices instead of answers fixed before the scan, and the
router call may leave any valid bump gap `rBump`. -/
theorem buildOneRoundTail_runs {w fRoute fFinish prefixCost total : ℕ} {p : Program}
    {B : BuildRoundData} {A : BuildRoundAddrs} {mem mem₁ : ℕ → ℕ}
    {pos pos₁ : ℕ} {ω : ℕ → Bool}
    (hWords : ∀ a ∈ B.args A, a < 2 ^ w)
    (hFitAll : ∀ rBump, B.ValidRouteBump rBump → BuildRoundFit w (B.withRouteBump rBump) A mem)
    (hSP : (B.scanContract w).post (B.scanArgs A) mem (B.prepared A) mem₁)
    (hRoute : MeetsContract w p fRoute (B.routeContract w))
    (hFinish : ∀ Ms emb, B.result.1 = .matched Ms emb →
      MeetsContract w p fFinish (buildFinishBatchContract w (B.applyData Ms emb)))
    (hPlayer : IsMatchingPlayer B.route B.routeCost) {β : ℝ}
    (hβ : 0 < β) (hExp : B.host.IsExpansionExpanderOn B.verts β)
    (hBudget : prefixCost + buildOneRoundTailCost w B ≤ total) :
    ∃ o st' c rBump, Runs w p ω (buildOneRoundTail fRoute fFinish)
      { startState (B.args A) mem pos with
        mem := mem₁
        regs := Function.update (startState (B.args A) mem pos).regs 15 (B.prepared A)
        pos := pos₁ }
      o st' c ∧ B.ValidRouteBump rBump ∧
      (buildOneRoundContract w (B.withRouteBump rBump)).post (B.args A) mem o.value st'.mem ∧
      prefixCost + c ≤ total := by
  suffices h : ∃ o st' c, Runs w p ω (buildOneRoundTail fRoute fFinish)
      { startState (B.args A) mem pos with
        mem := mem₁
        regs := Function.update (startState (B.args A) mem pos).regs 15 (B.prepared A)
        pos := pos₁ }
      o st' c ∧
      (∃ rBump, B.ValidRouteBump rBump ∧
        (buildOneRoundContract w (B.withRouteBump rBump)).post (B.args A) mem o.value st'.mem) ∧
      prefixCost + c ≤ total by
    obtain ⟨o, st', c, hRun, ⟨rBump, hRBump, hDone⟩, hCost⟩ := h
    exact ⟨o, st', c, rBump, hRun, hRBump, hDone, hCost⟩
  have hFit0 : BuildRoundFit w (B.withRouteBump 0) A mem := hFitAll 0 (Nat.zero_le _)
  unfold buildOneRoundTail
  let prep := B.prepared A
  let k := B.indices.length
  let batch := prep + 1 + B.jobs.count
  let rep := B.routeReply A
  have hRp : rep = batch + (k + k) + 1 + k * B.childSize := by
    dsimp [rep,batch,k,BuildRoundData.routeReply,buildBatchEnd]
    omega
  obtain ⟨hp,hp1,hB,hK2,hBK,hBK1,hMul,hAll⟩ := round_addresses hFit0
  change prep < 2 ^ w at hp
  change prep + 1 < 2 ^ w at hp1
  change batch < 2 ^ w at hB
  change k + k < 2 ^ w at hK2
  change batch + (k + k) < 2 ^ w at hBK
  change batch + (k + k) + 1 < 2 ^ w at hBK1
  change k * B.childSize < 2 ^ w at hMul
  change batch + (k + k) + 1 + k * B.childSize < 2 ^ w at hAll
  have hw := hFit0.bits
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hRoutePre : (B.routeContract w).pre (B.routeArgs A) mem₁ :=
    roundRoute_pre_after_scan (B := B.withRouteBump 0) hFit0 hSP
  refine runs_seq_call_le hRoute (vs := B.routeArgs A) ?_ (routeArgs_word hWords hp)
    hRoutePre ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,BuildRoundData.args,BuildRoundData.routeArgs]
  intro mid mem₂ pos₂ hRP
  have hrP := hRP
  obtain ⟨replyAddr,hostAddr,vertsAddr,heapAddr,he,hRound,hMidHi,hFrame,hZero⟩ := hrP
  simp only [BuildRoundData.routeArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hCount : mem₂ prep = k := hRound.1
  refine runs_seq_assign_le (v := k) ?_ ?_
  · change mem₂ (B.prepared A) = k at hCount
    simp [Expr.eval,Function.update,hCount]
  refine runs_seq_cond_le (v := k) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · intro hk
    have hLength : 1 ≤ B.pairs.length := by
      have eq : B.pairs.length = B.indices.length := length_batchJobPairs ..
      change B.pairs.length = k at eq
      omega
    obtain ⟨_,hExists⟩ := exists_lemma_1 hPlayer
    obtain ⟨⟨Ms,emb,hRes,hMatch,_⟩,_⟩ :=
      hExists B.host B.verts B.pairs B.Δ B.L hFit0.router hLength β hβ hExp
    change B.result.1 = .matched Ms emb at hRes
    change RouteMatchedSpec B.host B.verts B.pairs B.Δ B.L B.result.2 0 Ms emb at hMatch
    have hNotEmpty : B.indices.isEmpty = false :=
      Bool.eq_false_iff.mpr (fun he => hk (List.isEmpty_iff_length_eq_zero.mp he))
    have hLo : rep + (routeResultWords B.result.1).length ≤ mid := by
      have hh := hRound.2.2
      change (if B.indices.isEmpty then _ else _ ∧ _ ∧ rep + (routeResultWords B.result.1).length ≤ mid) at hh
      simp only [hNotEmpty, Bool.false_eq_true, ite_false] at hh
      exact hh.2.2
    have hHi : mid ≤ rep + (B.verts.card + 1) *
        routerSpaceUpTo B.routeSpace B.host.n B.host.encode.length
          (pairsWords B.pairs).length (B.Δ + B.L + max 2 B.verts.card) := by
      have hpk : B.pairs.length = B.indices.length := length_batchJobPairs ..
      change mid ≤ buildBatchEnd (prep + 1 + B.jobs.count) B.pairs.length B.childSize + _ at hMidHi
      rw [hpk] at hMidHi
      exact hMidHi
    let rBump := mid - (rep + (routeResultWords B.result.1).length)
    have hRBump : B.ValidRouteBump rBump := by
      dsimp only [BuildRoundData.ValidRouteBump, rBump]
      omega
    let Br := B.withRouteBump rBump
    have hFitR : BuildRoundFit w Br A mem := hFitAll rBump hRBump
    have hMidEq : mid = Br.routedEnd A := by
      change mid = rep + (routeResultWords B.result.1).length + rBump
      dsimp only [rBump]
      omega
    obtain ⟨_,hHostN,hFP⟩ := roundFinish_pre_after_route (B := Br) hFitR hNotEmpty hRes hMatch hSP hRP hMidEq
    let e := Br.routedEnd A
    let D := Br.applyData Ms emb
    have hEndW : e + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n < 2 ^ w := by
      obtain ⟨_,_,hWord⟩ := hFitR.reserved Ms emb hNotEmpty hRes
      have he := D.cursor_mono (e + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n)
        (Nat.zero_le Ms.length)
      change e + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n ≤ _ at he
      change D.cursor (e + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n) Ms.length < _ at hWord
      exact he.trans_lt hWord
    have hE : e < 2 ^ w := by omega
    have hHostAddr : A.host + 2 < 2 ^ w := by
      have hh := hFit0.hostBelow
      have hScanPre := hFit0.scan
      obtain ⟨_,_,_,_,eq,_,_,hAddr,_,_,_⟩ := hScanPre
      simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at eq
      obtain ⟨rfl,rfl,rfl,rfl⟩ := eq
      have hH : A.heap ≤ prep := B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
      have hLen : 2 ≤ B.host.encode.length := by simp [Graph.encode]
      omega
    have hNW : B.host.n < 2 ^ w := by omega
    have hrW : rep < 2 ^ w := hRp ▸ hAll
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := prep + 1) ?_ ?_
    · have hh : B.prepared A + 1 < 2^w := hp1
      simp [Expr.eval,Function.update,hOne,hh,prep]
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := batch) ?_ ?_
    · have hb : prep + 1 + B.jobs.count < 2 ^ w := hB
      simp [Expr.eval,startState,Function.update,BuildRoundData.args,batch,hb]
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := rep) ?_ ?_
    · simp [Expr.eval,startState,Function.update,BuildRoundData.args,hOne,hK2,hBK,hBK1,hMul,hAll,hRp]
    refine runs_seq_call_le (hFinish Ms emb hRes) (vs := Br.finishArgs A) ?_ ?_ hFP ?_
    · change evalArgs w _ _ =
        some [rep, prep + 1, A.graphs, A.offsets, A.host + 2, B.host.n, B.pathBound, Br.routedEnd A, k]
      rw [← hMidEq]
      simp [evalArgs, Expr.eval, startState, Function.update, BuildRoundData.args,
        hHostAddr, hTwo, hHostN, rep, prep, k, Br, BuildRoundData.withRouteBump]
    · have hg := hWords A.graphs (by simp [BuildRoundData.args])
      have ho := hWords A.offsets (by simp [BuildRoundData.args])
      have hcap := hWords B.pathBound (by simp [BuildRoundData.args])
      have hkW : B.indices.length < 2 ^ w := by change k < _; omega
      change ∀ a ∈ [rep, prep + 1, A.graphs, A.offsets, A.host + 2, B.host.n, B.pathBound, e, k],
        a < 2 ^ w
      wram_words
    intro v mem₃ pos₃ hPost
    refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
    · refine ⟨rBump, hRBump, A, mem₁, mem₂, mid, rfl, hSP, hRP, ?_⟩
      unfold roundFinishPost
      rw [show Br.indices.isEmpty = false from hNotEmpty]
      simp only [Bool.false_eq_true, ite_false, Outcome.value]
      exact ⟨hMidEq, Ms, emb, hRes, hPost⟩
    · simp [BuildRoundData.routeContract, buildRoundRouteContract, buildFinishBatchContract,
        Expr.size, argsSize, Nat.add_assoc]
      simp [buildOneRoundTailCost, BuildRoundData.routeContract, buildRoundRouteContract,
        buildFinishBatchContract, hRes, Nat.add_assoc] at hBudget
      omega
  · intro hk
    refine runs_seq_nop_le ?_
    refine runs_ret_le (v := mid) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
    · refine ⟨0, Nat.zero_le _, A, mem₁, mem₂, mid, rfl, hSP, hRP, ?_⟩
      have he : B.indices.isEmpty = true := List.isEmpty_iff_length_eq_zero.mpr hk
      unfold roundFinishPost
      rw [show (B.withRouteBump 0).indices.isEmpty = true from he]
      simp [Outcome.value]
    · simp [BuildRoundData.routeContract, buildRoundRouteContract, Expr.size, argsSize]
      simp [buildOneRoundTailCost, BuildRoundData.routeContract, buildRoundRouteContract] at hBudget
      omega

end MinCostFlow.HierPaths
