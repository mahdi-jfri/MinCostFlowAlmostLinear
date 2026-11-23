module

public import MinCostFlow.HierPaths.BuildProgPrepareChild

/-!
# Calling the core on all active children

Scan the active child table in order. Each child receives one core call, followed
by request preparation when the reply is a cut. Store a pointer to each reply so
the round can gather just the cuts into a single router request.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Parallel tables of graph addresses and terminal offsets refer to these child graphs.
Optional `choice` records certified replies and optional `bump` records the core's extra
bump-heap gap beyond `(coreResultWords answer).length` for each child. -/
structure BuildGameJobs where
  count : ℕ
  graph : ℕ → Graph
  addr : ℕ → ℕ
  offset : ℕ → ℕ
  choice : Option (ℕ → CoreResult) := none
  bump : Option (ℕ → ℕ) := none

/-- Use the replies of the current scan when they have been recorded. -/
def BuildGameJobs.answer (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q i : ℕ) : CoreResult :=
  (J.choice.getD (fun j => core q (J.graph j))) i

/-- Extra bump-heap gap left by the core on child `i` (`0` for the exact-model specialization). -/
def BuildGameJobs.bumpSize (J : BuildGameJobs) (i : ℕ) : ℕ :=
  (J.bump.getD (fun _ => 0)) i

/-- Heap cursor after preparing the first `i` active children. -/
def BuildGameJobs.prepPrefix (J : BuildGameJobs) (answer : ℕ → Graph → CoreResult) (q h : ℕ) :
    ℕ → ℕ
  | 0 => h
  | i + 1 => preparedChildEnd (J.prepPrefix answer q h i) (J.graph i).n (J.answer answer q i) +
      J.bumpSize i

/-- One iteration takes the next child graph and its offset from the active table. -/
def buildGameScanStep (f : ℕ) : Stmt :=
  .seq (.call 9 f [.reg 0, .load (.bin .add (.reg 4) (.reg 8)), .reg 1, .reg 2, .reg 6,
      .load (.bin .add (.reg 5) (.reg 8))])
    (.seq (.store (.bin .add (.reg 7) (.reg 8)) (.reg 6)) (.assign 6 (.reg 9)))

/-- Args are `[q, M, r, count, graphs, offsets, heap, replies]`. Writes `replies[0..count]`
(ending with `replies[count] = top`) and returns `top`. -/
def buildGameScanProc (f : ℕ) : Stmt :=
  .seq (forRange 8 (.const 0) (.reg 3) (buildGameScanStep f))
    (.seq (.store (.bin .add (.reg 7) (.reg 3)) (.reg 6)) (.ret (.reg 6)))

theorem buildGameScanProc_noRand (f : ℕ) : (buildGameScanProc f).NoRand := by
  simp [buildGameScanProc, buildGameScanStep, forRange, forUp, Stmt.NoRand]

/-- Conditions on one child graph, in memory below the reply pointer table. -/
def BuildGameJobs.ChildFits (J : BuildGameJobs) (w M r q table : ℕ) (mem : ℕ → ℕ) (i : ℕ) : Prop :=
  let G := J.graph i
  GraphAt mem (J.addr i) G ∧ J.addr i + G.encode.length ≤ table ∧
    G.IsValid ∧ G.IsLoopless ∧ G.n ≤ (NOf M r) ^ q ∧
    (∀ v < G.n, G.deg v ≤ deltaParam M) ∧ 2 ≤ G.n ∧ J.offset i + G.n < 2 ^ w

/-- The cost of one scan step includes its core reply, the mask and the request. -/
def prepGameStepCost (J : BuildGameJobs) (K q : ℕ) (coreCost : ℕ → Graph → ℕ) (i : ℕ) : ℕ :=
  let G := J.graph i
  K * (coreCost q G + G.encode.length + 1) + 160 * G.n + 290

/-- Prepare every active child, retaining earlier replies while the heap grows. -/
def buildGameScanContract (w K M r q : ℕ) (core : ℕ → Graph → CoreResult)
    (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ) (J : BuildGameJobs) : Contract where
  pre args mem := ∃ graphs offsets h replies, args = [q, M, r, J.count, graphs, offsets, h, replies] ∧
    graphs + J.count ≤ replies ∧ offsets + J.count ≤ replies ∧ replies + J.count + 1 ≤ h ∧
    1 < 2 ^ w ∧ h < 2 ^ w ∧ q ≤ r ∧ ZeroFrom mem h ∧
    ListAt mem graphs (tabList J.count J.addr) ∧ ListAt mem offsets (tabList J.count J.offset) ∧
    ∀ i < J.count, J.ChildFits w M r q replies mem i ∧
      J.prepPrefix core q h i + sC (J.graph i).encode.length + 3 * (J.graph i).n < 2 ^ w
  post args mem v mem' := ∃ graphs offsets h replies,
    args = [q, M, r, J.count, graphs, offsets, h, replies] ∧ v = J.prepPrefix core q h J.count ∧
    ZeroFrom mem' v ∧
    ((∀ a < replies, mem' a = mem a) ∧ (∀ a, replies + J.count + 1 ≤ a → a < h → mem' a = mem a)) ∧
    mem' (replies + J.count) = J.prepPrefix core q h J.count ∧
    ∀ i < J.count, mem' (replies + i) = J.prepPrefix core q h i ∧
      PreparedChildAt mem' (J.prepPrefix core q h i) (J.prepPrefix core q h (i + 1))
        (J.graph i).n (J.offset i) (J.answer core q i)
  cost _ _ := rangeCost (prepGameStepCost J K q coreCost) 0 J.count + 9 * J.count + 28

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Each prepared reply extends the heap. -/
theorem BuildGameJobs.prepPrefix_mono (J : BuildGameJobs) (core : ℕ → Graph → CoreResult)
    (q h : ℕ) : Monotone (J.prepPrefix core q h) := by
  apply monotone_nat_of_le_succ
  intro i
  change J.prepPrefix core q h i ≤
    preparedChildEnd (J.prepPrefix core q h i) (J.graph i).n (J.answer core q i) + J.bumpSize i
  cases J.answer core q i <;> simp [preparedChildEnd] <;> omega

private def gameScanInv (J : BuildGameJobs) (core : ℕ → Graph → CoreResult)
    (q M r graphs offsets h replies : ℕ) (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = q ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = J.count ∧
    st.regs 4 = graphs ∧ st.regs 5 = offsets ∧ st.regs 6 = J.prepPrefix core q h i ∧
    st.regs 7 = replies ∧ st.regs 8 = i ∧ ZeroFrom st.mem (J.prepPrefix core q h i) ∧
    ((∀ a < replies, st.mem a = mem a) ∧ (∀ a, replies + i ≤ a → a < h → st.mem a = mem a)) ∧
    ∀ j < i, st.mem (replies + j) = J.prepPrefix core q h j ∧
      PreparedChildAt st.mem (J.prepPrefix core q h j) (J.prepPrefix core q h (j + 1))
        (J.graph j).n (J.offset j) (J.answer core q j)

private theorem buildGameScan_step {w K M r q f graphs offsets h replies i : ℕ}
    {p : Program} {J : BuildGameJobs} {mem : ℕ → ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ} {cfg : ParamConfig}
    (hPlayer : IsCorePlayer cfg M r core coreCost)
    (hExact : ∀ i < J.count, J.answer core q i = core q (J.graph i))
    (hZeroBump : ∀ i < J.count, J.bumpSize i = 0)
    (hProc : ∀ G, MeetsContract w p f (buildPrepareChildContract w K M r q core coreCost sC G))
    (hArgs : ∀ a ∈ [q, M, r, J.count, graphs, offsets, h, replies], a < 2 ^ w)
    (hq : q ≤ r) (hi : i < J.count) (hGO : graphs + J.count ≤ replies)
    (hOO : offsets + J.count ≤ replies) (hRO : replies + J.count + 1 ≤ h)
    (hGraphs : ListAt mem graphs (tabList J.count J.addr))
    (hOffsets : ListAt mem offsets (tabList J.count J.offset))
    (hJob : ∀ j < J.count, J.ChildFits w M r q replies mem j ∧
      J.prepPrefix core q h j + sC (J.graph j).encode.length + 3 * (J.graph j).n < 2 ^ w) :
    Triple w p (gameScanInv J core q M r graphs offsets h replies mem i) (buildGameScanStep f)
      (normalPost fun st =>
        gameScanInv J core q M r graphs offsets h replies mem (i + 1)
          {st with regs := Function.update st.regs 8 (i + 1)} ∧ st.regs 8 = i)
      (fun _ => prepGameStepCost J K q coreCost i) := by
  intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hZero, hFrame, hPrev⟩
  let top := J.prepPrefix core q h i
  let G := J.graph i
  have hMono := J.prepPrefix_mono core q h
  have hh : h ≤ top := hMono (Nat.zero_le i)
  have hrTop : replies + i < top := by omega
  obtain ⟨⟨hGraph, hGE, hValid, hLoop, hn, hDeg, hs, ho⟩, hRoom⟩ := hJob i hi
  change top + sC G.encode.length + 3 * G.n < 2 ^ w at hRoom
  change J.addr i + G.encode.length ≤ replies at hGE
  have hG' : GraphAt st.mem (J.addr i) G := WordRAM.ListAt.congr hGraph
    (fun j _ hj => hFrame.1 j (hj.trans_le hGE))
  have ht : top < 2 ^ w := by omega
  have hga : graphs + i < 2 ^ w := by omega
  have hoa : offsets + i < 2 ^ w := by omega
  have hgRead : st.mem (graphs + i) = J.addr i :=
    (hFrame.1 _ (by omega)).trans (listAt_tabList hGraphs hi)
  have hoRead : st.mem (offsets + i) = J.offset i :=
    (hFrame.1 _ (by omega)).trans (listAt_tabList hOffsets hi)
  refine runs_start_le ?_
  unfold buildGameScanStep
  refine runs_seq_call_le (hProc G) (vs := [q, J.addr i, M, r, top, J.offset i]) ?_ ?_
    ⟨J.addr i, top, J.offset i, rfl,
      ⟨⟨J.addr i, top, rfl, hG', hGE.trans (by omega), hq, hValid, hLoop, hn, hDeg⟩, hZero, by
        change top + sC G.encode.length < 2 ^ w
        omega⟩, hs, ho, hRoom⟩ ?_
  · simp [evalArgs, Expr.eval, h0, h1, h2, h4, h5, h6, h8, hgRead, hoRead, hga, hoa, top]
  · have hwq := hArgs q (by simp)
    have hwM := hArgs M (by simp)
    have hwr := hArgs r (by simp)
    change J.offset i + G.n < 2 ^ w at ho
    wram_words
  intro v mem' pos' hPost
  obtain ⟨_, _, _, hEq, hLo, hHi, hBelow, hZ', hEndEq, hReply⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl, rfl⟩ := hEq
  have hI := hExact i hi
  have hv : v = J.prepPrefix core q h (i + 1) := by
    change v = preparedChildEnd top G.n (J.answer core q i) + J.bumpSize i
    rw [hI, hZeroBump i hi, Nat.add_zero]
    exact hEndEq
  have hDest : replies + i < 2 ^ w := hrTop.trans ht
  refine runs_seq_store_le (x := replies + i) (v := top) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h7, h8, hDest]
  · simp [Expr.eval, Function.update, h6, top]
  refine runs_assign_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
      by simpa using h3, by simpa using h4, by simpa using h5, by simp [hv],
      by simpa using h7, by simp, ?_, ?_, ?_⟩, by simpa using h8⟩
    · intro j hj
      change Function.update mem' (replies + i) top j = 0
      rw [Function.update_of_ne (by omega)]
      exact hZ' j (by omega)
    · constructor
      · intro j hj
        change Function.update mem' (replies + i) top j = mem j
        rw [Function.update_of_ne (by omega)]
        exact (hBelow j (by omega)).trans (hFrame.1 j hj)
      · intro j hj hlo
        change Function.update mem' (replies + i) top j = mem j
        rw [Function.update_of_ne (by omega)]
        exact (hBelow j (hlo.trans_le hh)).trans (hFrame.2 j (by omega) hlo)
    · intro j hj
      change Function.update mem' (replies + i) top (replies + j) = _ ∧ _
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hPrevPtr, hPrevBlock⟩ := hPrev j hj
        have hjEnd : J.prepPrefix core q h (j + 1) ≤ top := hMono (by omega)
        have hjStart : h ≤ J.prepPrefix core q h j := hMono (Nat.zero_le j)
        have hjCut : ∀ U, J.answer core q j = .cut U → U ⊆ Finset.range (J.graph j).n := by
          obtain ⟨⟨_, _, hvj, hlj, hnj, hdj, _, _⟩, _⟩ := hJob j (hj.trans hi)
          intro U hU
          have hs := hPlayer.spec q (J.graph j) hq hvj hlj hnj hdj
          rw [hExact j (hj.trans hi)] at hU
          rw [hU] at hs
          exact hs.1
        constructor
        · rw [Function.update_of_ne (by omega), hBelow _ (by omega)]
          exact hPrevPtr
        · -- Cells in the reply start above the entire pointer table.
          have hMem : ∀ a, J.prepPrefix core q h j ≤ a →
              a < J.prepPrefix core q h (j + 1) →
              Function.update mem' (replies + i) top a = st.mem a := by
            intro a ha hb
            rw [Function.update_of_ne (by omega)]
            exact hBelow a (hb.trans_le hjEnd)
          exact hPrevBlock.frame hMem hjCut
      · refine ⟨by simp [top], ?_⟩
        rw [← hv,hI]
        have hCut : ∀ U, core q G = .cut U → U ⊆ Finset.range G.n := by
          intro U hU
          have hs := hPlayer.spec q G hq hValid hLoop hn hDeg
          rw [hU] at hs
          exact hs.1
        exact hReply.frame (fun a ha _ => Function.update_of_ne (by omega) _ _) hCut
  · simp [prepGameStepCost, buildPrepareChildContract, Expr.size, argsSize, G]; omega

/-- The active-child scan prepares all replies in order and preserves the input tables. -/
theorem buildGameScanProc_meetsContract {w K M r q f fChild : ℕ} {p : Program}
    {J : BuildGameJobs} {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {sC : ℕ → ℕ} {cfg : ParamConfig}
    (hf : p.procs[f]? = some (buildGameScanProc fChild))
    (hPlayer : IsCorePlayer cfg M r core coreCost)
    (hExact : ∀ i < J.count, J.answer core q i = core q (J.graph i))
    (hZeroBump : ∀ i < J.count, J.bumpSize i = 0)
    (hChild : ∀ G, MeetsContract w p fChild
      (buildPrepareChildContract w K M r q core coreCost sC G)) :
    MeetsContract w p f (buildGameScanContract w K M r q core coreCost sC J) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨graphs, offsets, h, replies, rfl, hGO, hOO, hRO, hw, hh, hq, hZero, hGraphs, hOffsets,
    hJob⟩ := hPre
  let st0 := startState [q, M, r, J.count, graphs, offsets, h, replies] mem pos
  have hLoop := Triple.forRange_le (p := p) (r := 8) (lo := .const 0) (hi := .reg 3)
    (body := buildGameScanStep fChild) (P := fun st => st = st0)
    (Inv := gameScanInv J core q M r graphs offsets h replies mem)
    (prepGameStepCost J K q coreCost) 0 J.count (Nat.zero_le _) hw
    (fun _ => hArgs J.count (by simp))
    (fun st hEq => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _), ?_⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hZero, ⟨fun _ _ => rfl,fun _ _ _ => rfl⟩,
        fun j hj => False.elim (Nat.not_lt_zero j hj)⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
    (fun _ _ hi => buildGameScan_step hPlayer hExact hZeroBump hChild hArgs hq hi hGO hOO hRO hGraphs hOffsets hJob)
  refine runs_start_le ?_
  unfold buildGameScanProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_, _, _, hCnt, _, _, hTop, hRep, _, hZ, hFrame, hBlocks⟩
  have hRepCntW : replies + J.count < 2 ^ w := by omega
  have hMono := J.prepPrefix_mono core q h
  have hTopGe : h ≤ J.prepPrefix core q h J.count := hMono (Nat.zero_le _)
  refine runs_seq_store_le (x := replies + J.count) (v := J.prepPrefix core q h J.count)
    (by simp [Expr.eval, hRep, hCnt, hRepCntW])
    (Expr.eval_reg_of_eq hTop) ?_
  refine runs_ret_le (Expr.eval_reg_of_eq hTop) ?_ ?_
  · refine ⟨graphs, offsets, h, replies, rfl, rfl, ?_, ⟨?_, ?_⟩, by simp, ?_⟩
    · intro a ha
      simp only [Outcome.value] at ha
      change Function.update st.mem (replies + J.count) (J.prepPrefix core q h J.count) a = 0
      rw [Function.update_of_ne (by omega)]
      exact hZ a ha
    · intro a ha
      change Function.update st.mem (replies + J.count) (J.prepPrefix core q h J.count) a = mem a
      rw [Function.update_of_ne (by omega)]
      exact hFrame.1 a ha
    · intro a ha1 ha2
      change Function.update st.mem (replies + J.count) (J.prepPrefix core q h J.count) a = mem a
      rw [Function.update_of_ne (by omega)]
      exact hFrame.2 a (by omega) ha2
    · intro i hi
      obtain ⟨hPtr, hBlk⟩ := hBlocks i hi
      have hiStart : h ≤ J.prepPrefix core q h i := hMono (Nat.zero_le _)
      refine ⟨by change Function.update _ _ _ _ = _; rw [Function.update_of_ne (by omega)]; exact hPtr, ?_⟩
      refine hBlk.frame (fun a ha _ => Function.update_of_ne (by omega) _ _) ?_
      intro U hU
      obtain ⟨⟨_, _, hvi, hli, hni, hdi, _, _⟩, _⟩ := hJob i hi
      have hs := hPlayer.spec q (J.graph i) hq hvi hli hni hdi
      rw [hExact i hi] at hU
      rw [hU] at hs
      exact hs.1
  · simp [buildGameScanContract, Expr.size]
    omega

end MinCostFlow.HierPaths
