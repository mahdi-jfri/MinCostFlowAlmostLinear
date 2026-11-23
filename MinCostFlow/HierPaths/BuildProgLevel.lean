module

public import MinCostFlow.HierPaths.BuildProgLevelDefs
import MinCostFlow.HierPaths.BuildProgLevelBack
import MinCostFlow.HierPaths.BuildProgLevelSetup
import MinCostFlow.HierPaths.InitLayout

/-!
# Verification of the complete one-parent static level builder

Combines the singleton path (`buildSingletonProc`) with the non-singleton pipeline
(`nonSingleton_setup_runs`, `buildGameChoiceProcs`, `buildInjectEndProc`, `nonSingleton_back_runs`)
to prove `buildLevelProcs_providesBuildLevel : ProvidesBuildLevel`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Complete non-singleton run (Setup + Game + Back) -/

set_option maxHeartbeats 800000 in
private theorem buildLevelNonSingleton_runs {w K C router core : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    {p : Program} {prior later : List Stmt} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w K route routeCost sR p router)
    (hCore : ProvidesCore w K M r (coreCost M r) (sC M r) p core)
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : RouteCostLe routeCost C)
    (hCoreCost : CoreCostBound coreCost)
    (hArgW : ∀ a ∈ buildLevelArgs g x start s k M r Δ L L' bh h, a < 2 ^ w)
    (hG : GraphAt mem g G) (hX : ListAt mem x (finsetWords (buildLevelVerts start s k)))
    (hGE : g + G.encode.length ≤ h)
    (hXE : x + (finsetWords (buildLevelVerts start s k)).length ≤ h)
    (hZero : ZeroFrom mem h)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L')
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w) :
    ∃ (D_level : BuildLevelData) (v : ℕ) (st' : State) (c : ℕ),
      Runs w p ω
        (buildLevelNonSingletonProc (prior.length + 34) (prior.length + 35)
          (prior.length + 1) (prior.length + 41) (prior.length + 44)
          (prior.length + 45) (prior.length + 46) (prior.length + 57)
          (prior.length + 14))
        (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos)
        (.returned v) st' c ∧
      h + (D_level.encode k).length ≤ v ∧
      v ≤ h + buildLevelSpace sR sC G s k M r Δ L L' bh ∧
      ListAt st'.mem h (D_level.encode k) ∧
      (∀ a < h, st'.mem a = mem a) ∧
      ZeroFrom st'.mem v ∧
      D_level.Good G start s k M r Δ L L' bh ∧
      c + 40 ≤ buildLevelCost (buildLevelConst K C) G s k M r Δ L L' bh := by
  let b := prior.length
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  set T := buildLevelDegree L'
  set limit := 49 * L' + 1
  set d := routePathLen Δ bh L
  set slotWords := 2 + T * s
  set maxM := T * (s / 2)
  set saved := h + limit
  set graphs := saved + k
  set offsets := graphs + k
  set slots := offsets + k
  set replies := slots + k * slotWords
  set heap0 := replies + k + 1
  set q := coreLevel M r s
  set coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
  set routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
    (Δ + L + max 2 (s * k))
  have hCoreCapEq : roundCoreCap D = coreCap := rfl
  have hRouteCapEq : roundRouteCap D = routeCap := by
    unfold roundRouteCap
    have hCard : (buildLevelVerts start s k).card = s * k := by
      simp [buildLevelVerts, Nat.mul_comm]
    change ((buildLevelVerts start s k).card + 1) *
        (Finset.range (2 * k + 1 + k * s + 1)).sup
          (fun pLen => routerSpaceUpTo sR G.n G.encode.length pLen
            (Δ + L + max 2 (buildLevelVerts start s k).card)) = routeCap
    rw [hCard]; rfl
  have hHyp : ChoiceGameHyp D β bh :=
    levelChoiceData_hyp hPlayer hValid hHost hPos hExp hBh hs hEven hsN hRank hDeg hsL
  have hLay : GameFixedLayout w D.geometry :=
    levelChoiceData_fixedLayout hGE hXE hHost hs hk hSpace
  have hNonSing : h + ((T + 4 * k + 1 + k * slotWords) +
      T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
      (k + k * (T * s)) + (k + 1 + k * slotWords) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
      (maxCoreSpace (sC M r) slotWords + routeCap +
        6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
      connAllSpace sR G s k Δ L d +
      NOf M r + d + G.n + 100) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
  have hStartLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
  have hCardW : (buildLevelVerts start s k).card < 2 ^ w := by
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; omega
  have hSKW : s * k < 2 ^ w := by
    have : s * k = k * s := Nat.mul_comm s k
    omega
  -- Word bounds
  have hGW : g < 2 ^ w := hArgW g (by simp [buildLevelArgs])
  have hXW : x < 2 ^ w := hArgW x (by simp [buildLevelArgs])
  have hStartW : start < 2 ^ w := hArgW start (by simp [buildLevelArgs])
  have hSW : s < 2 ^ w := hArgW s (by simp [buildLevelArgs])
  have hKW : k < 2 ^ w := hArgW k (by simp [buildLevelArgs])
  have hMW : M < 2 ^ w := hArgW M (by simp [buildLevelArgs])
  have hRW : r < 2 ^ w := hArgW r (by simp [buildLevelArgs])
  have hΔW : Δ < 2 ^ w := hArgW Δ (by simp [buildLevelArgs])
  have hLW : L < 2 ^ w := hArgW L (by simp [buildLevelArgs])
  have hHW : h < 2 ^ w := hArgW h (by simp [buildLevelArgs])
  have hDW : d < 2 ^ w := by omega
  have hTW : T < 2 ^ w := by omega
  have hLimW : limit < 2 ^ w := by dsimp [limit, T, buildLevelDegree] at hTW ⊢; omega
  have hHeap0W : heap0 < 2 ^ w := by
    dsimp [heap0, replies, slots, offsets, graphs, saved, limit, T, buildLevelDegree] at hNonSing ⊢
    omega
  have hRepW : replies < 2 ^ w := by dsimp [heap0] at hHeap0W; omega
  have hSlotsW : slots < 2 ^ w := by dsimp [replies] at hRepW; omega
  have hOffsW : offsets < 2 ^ w := by dsimp [slots] at hSlotsW; omega
  have hGraphsW : graphs < 2 ^ w := by dsimp [offsets] at hOffsW; omega
  have hSavedW : saved < 2 ^ w := by dsimp [graphs] at hGraphsW; omega
  have hKSlotW : k * slotWords < 2 ^ w := by dsimp [replies] at hRepW; omega
  have hSlotW : slotWords < 2 ^ w := by
    have : 1 * slotWords ≤ k * slotWords := Nat.mul_le_mul_right slotWords (by omega); omega
  have hQW : q < 2 ^ w := (coreLevel_le hsN).trans_lt hRW
  -- Step 1: run setup
  obtain ⟨st1, cSetup, hRunSetup, h1r0, h1r1, h1r2, h1r3, h1r4, h1r5, h1r6, h1r7, h1r8, h1r11,
    h1r12, h1r13, h1r15, h1r16, h1r17, h1r18, h1r19, h1r20, h1r21, h1r22, h1r23,
    hInitMem, hM1BelowGraphs, hDirZero, hCostSetup⟩ :=
    nonSingleton_setup_runs (w := w) (K := K) (router := router) (core := core)
      (route := route) (routeCost := routeCost) (sR := sR) (coreCost := coreCost) (sC := sC)
      (β := β) (pos := pos) (ω := ω) hp hArgW hG hX hGE hXE hZero hHost hBh hs hk hsN hSpace
  -- Step 2: run fGameLoop
  have hSpecLoop := buildGameChoiceProcs_meetsContract
    (w := w) (core := core) (router := router)
    (tailBudget := levelTailBudget K C G s k Δ L bh)
    (stepBudget := levelStepBudget K C G s k M r Δ L L' bh)
    (D := D) (hp := buildLevelProcs_gameSplit hp)
    hRouter hCore hPlayer hPos hExp hCardW
  have hLoopIdx : (prior ++ [buildLevelEntryProc (b + 58) (b + 59)]).length = b + 1 := by simp [b]
  rw [hLoopIdx] at hSpecLoop
  have hLoopFit := levelChoiceData_loopFit hPlayer hC hCoreCost hGE hXE hValid hHost
    hPos hExp hBh hs hk hEven hsN hRank hDeg hsL hSpace hArgW hInitMem
  have hLoopArgsEq : [q, M, r, k, graphs, offsets, heap0, replies, s, g, x, Δ, L, d, s * k, start,
      saved, h, limit] = D.args D.addrs.heap (fun _ => ChildState.init) := by
    have hAct : (D.round (fun _ => ChildState.init)).jobs.count = k := by
      change (activeChildren k (fun _ => ChildState.init)).length = k
      simp [activeChildren, ChildState.init]
    have hCard : (buildLevelVerts start s k).card = s * k := by
      simp [buildLevelVerts, Nat.mul_comm]
    simp only [ChoiceLoopData.args, BuildRoundData.stepArgs, BuildRoundData.args, hAct]
    change [q, M, r, k, graphs, offsets, heap0, replies, s, g, x, Δ, L, d, s * k, start,
        saved, h, limit] =
      [q, M, r, k, graphs, offsets, heap0, replies, s, g, x, Δ, L, d,
        (buildLevelVerts start s k).card, start, saved, h, limit]
    rw [hCard]
  obtain ⟨st2, cLoop, heap₁, hRunLoop, hPost2, h2r25, h2other, hCostLoop⟩ :=
    runs_call_of_meetsContract (r := 25)
      (args := [.reg 23, .reg 5, .reg 6, .reg 4, .reg 18, .reg 19, .reg 22, .reg 21,
        .reg 3, .reg 0, .reg 1, .reg 7, .reg 8, .reg 12, .bin .mul (.reg 3) (.reg 4),
        .reg 2, .reg 17, .reg 11, .reg 13])
      hSpecLoop
      (vs := [q, M, r, k, graphs, offsets, heap0, replies, s, g, x, Δ, L, d, s * k, start, saved, h, limit])
      (by simp [evalArgs, Expr.eval, BinOp.eval, h1r0, h1r1, h1r2, h1r3, h1r4, h1r5, h1r6, h1r7, h1r8, h1r11,
            h1r12, h1r13, h1r17, h1r18, h1r19, h1r21, h1r22, h1r23, hSKW,
            q, graphs, offsets, heap0, replies, d, saved, limit, slots, slotWords, T])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      ⟨hLoopArgsEq, hLoopFit⟩ ω
  obtain ⟨sts, hTrace, _⟩ := hPost2
  have hRoomAll : ∀ t' heap' sts' mem', t' < D.limit → ChoiceLoopTrace w D st1.mem t' heap' sts' mem' →
      (D.round sts').jobs.count ≠ 0 →
      ChoiceRoundBudget w (levelTailBudget K C G s k Δ L bh) D heap' sts' :=
    fun t' heap' sts' mem' ht' hTr' _ =>
      levelChoiceData_roundBudget hPlayer hC hValid hHost hPos hExp hBh hs hk hEven hsN hRank hDeg hsL
        hSpace ht' hTr'
  have hMem2 : ChoiceGameMemory D heap₁ sts st2.mem :=
    hTrace.memory le_rfl hHyp hLay hInitMem hRoomAll
  obtain ⟨hInjInput, hInjSizes⟩ := hTrace.injectInput hHyp hLay hInitMem hRoomAll
  obtain ⟨Ms, emb, hInjRes1, hInjMatch, hInjFull, hInjRunLe⟩ :=
    hTrace.injectMatched hHyp (by change 1 ≤ k; omega)
  let runEnd := (lemma1Route route G (buildLevelVerts start s k)
    (injPairs s k D.offset sts) Δ L).2
  have hInjRes : lemma1Route route G (buildLevelVerts start s k)
      (injPairs s k D.offset sts) Δ L = (.matched Ms emb, runEnd) :=
    Prod.ext hInjRes1 rfl
  have hInjFit := levelChoiceData_injectEndFit hPlayer hValid hHost hPos hExp
    hBh hs hk hEven hsN hRank hDeg hsL hSpace hTrace hInjRunLe hInjMatch hInjFull
  obtain ⟨hInjRouteCost, hInjFinishCost⟩ := levelChoiceData_injectCost_le hPlayer hC hValid hHost
    hPos hExp hBh hs hk hEven hsN hRank hDeg hsL hTrace hInjRes hInjRunLe hInjMatch hInjFull
  have hSpecInj := buildLevelProcs_injectEnd_meetsContract (heap := heap₁) (slot := slots)
    (runEnd := runEnd) hp hRouter hTrace hHyp hLay hCardW hInjRes hInjRunLe hInjMatch hInjFull
  have hHeap1Le : heap₁ ≤ D.addrs.heap + D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by
    rw [← hCoreCapEq, ← hRouteCapEq]
    exact choiceLoopTrace_heap_le hTrace hHyp le_rfl
  have hH0Le : D.addrs.heap ≤ h + (T + 4 * k + 1 + k * slotWords) := by
    change h + limit + k + k + k + k * (2 + (limit + 1) * s) + k + 1 ≤ h + (T + 4 * k + 1 + k * (2 + T * s))
    have : limit + 1 = T := rfl
    rw [this]; omega
  have hHeap1W : heap₁ < 2 ^ w := by
    have hLimT : D.limit ≤ T := by change 49 * L' + 1 ≤ 49 * L' + 2; omega
    have h2 : D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) ≤
        T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
      Nat.mul_le_mul_right _ hLimT
    omega
  -- Step 3: run fInjectEnd
  have hInjArgsEq : [g, x, saved, start, s, k, Δ, L, heap₁, graphs, offsets, slots, slotWords, replies, d] =
      injectEndArgs D heap₁ slots := rfl
  have hInjPre : (buildInjectEndContract w D heap₁ slots sts Ms emb).pre
      (injectEndArgs D heap₁ slots) st2.mem :=
    ⟨rfl, hMem2, hInjInput, hInjSizes, hInjFit⟩
  have h2r (r' : ℕ) (hne : r' ≠ 25) : st2.regs r' = st1.regs r' := h2other r' hne
  have h2r0 : st2.regs 0 = g := (h2r 0 (by omega)).trans h1r0
  have h2r1 : st2.regs 1 = x := (h2r 1 (by omega)).trans h1r1
  have h2r2 : st2.regs 2 = start := (h2r 2 (by omega)).trans h1r2
  have h2r3 : st2.regs 3 = s := (h2r 3 (by omega)).trans h1r3
  have h2r4 : st2.regs 4 = k := (h2r 4 (by omega)).trans h1r4
  have h2r7 : st2.regs 7 = Δ := (h2r 7 (by omega)).trans h1r7
  have h2r8 : st2.regs 8 = L := (h2r 8 (by omega)).trans h1r8
  have h2r12 : st2.regs 12 = d := (h2r 12 (by omega)).trans h1r12
  have h2r15 : st2.regs 15 = slotWords := (h2r 15 (by omega)).trans h1r15
  have h2r17 : st2.regs 17 = saved := (h2r 17 (by omega)).trans h1r17
  have h2r18 : st2.regs 18 = graphs := (h2r 18 (by omega)).trans h1r18
  have h2r19 : st2.regs 19 = offsets := (h2r 19 (by omega)).trans h1r19
  have h2r20 : st2.regs 20 = slots := (h2r 20 (by omega)).trans h1r20
  have h2r21 : st2.regs 21 = replies := (h2r 21 (by omega)).trans h1r21
  obtain ⟨st3, cInj, injEnd, hRunInj, hPost3, h3r26, h3other, hCostInj⟩ :=
    runs_call_of_meetsContract (r := 26)
      (args := [.reg 0, .reg 1, .reg 17, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8,
        .reg 25, .reg 18, .reg 19, .reg 20, .reg 15, .reg 21, .reg 12])
      hSpecInj
      (vs := injectEndArgs D heap₁ slots)
      (by rw [← hInjArgsEq]; simp [evalArgs, Expr.eval, h2r0, h2r1, h2r2, h2r3, h2r4, h2r7, h2r8,
            h2r12, h2r15, h2r17, h2r18, h2r19, h2r20, h2r21, h2r25,
            saved, graphs, offsets, slots, slotWords, replies, d, limit, T])
      (by rw [← hInjArgsEq]; intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> assumption)
      hInjPre ω
  have h3r (r' : ℕ) (hne26 : r' ≠ 26) (hne25 : r' ≠ 25) : st3.regs r' = st1.regs r' :=
    (h3other r' hne26).trans (h2other r' hne25)
  -- Extract TraceRoundsMem, InjArchive, GraphAt, ListAt, and prefix frame after fInjectEnd!
  obtain ⟨hRounds3, hInjArch3⟩ := finishedLevelMem_of_inject hTrace hHyp hLay
    hInitMem hDirZero hRoomAll (fun _ => rfl) hInjRes hInjRunLe hInjMatch hInjFull hPost3
  have hInjEndBound' : injEnd ≤ h + (T + 4 * k + 1 + k * slotWords) +
      T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hInjDiff, _⟩ := hInjArch3
    rw [hRouteCapEq] at hInjDiff
    change injEnd - heap₁ - G.n ≤ roundNonHoleCap s k d + routeCap at hInjDiff
    have hFin : injEnd ≤ heap₁ + (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by omega
    have hMulT : D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
        (roundNonHoleCap s k d + coreCap + routeCap + G.n) =
        T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
      (Nat.succ_mul D.limit (roundNonHoleCap s k d + coreCap + routeCap + G.n)).symm
    calc injEnd ≤ heap₁ + (roundNonHoleCap s k d + coreCap + routeCap + G.n) := hFin
      _ ≤ (D.addrs.heap + D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n)) +
          (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
        Nat.add_le_add_right hHeap1Le _
      _ = D.addrs.heap + (D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
          (roundNonHoleCap s k d + coreCap + routeCap + G.n)) :=
        Nat.add_assoc _ _ _
      _ = D.addrs.heap + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by rw [hMulT]
      _ ≤ h + (T + 4 * k + 1 + k * slotWords) + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
        Nat.add_le_add_right hH0Le _
  -- Prefix below h is preserved across loop and injection
  have hM2BelowH : ∀ a < h, st2.mem a = mem a := fun a ha =>
    (choiceLoopTrace_prefix_frame le_rfl hTrace hHyp hLay hInitMem hRoomAll a ha).trans
      (hM1BelowGraphs a (by omega))
  have hM3BelowH : ∀ a < h, st3.mem a = mem a := fun a ha =>
    (injectEnd_prefix_frame hTrace hHyp hLay hMem2 hInjMatch hInjFull hPost3 a ha).trans
      (hM2BelowH a ha)
  have hGraphAt3 : GraphAt st3.mem g G :=
    WordRAM.ListAt.congr hG fun a _ hb => hM3BelowH a (hb.trans_le hGE)
  have hVertsAt3 : ListAt st3.mem x (finsetWords (buildLevelVerts start s k)) :=
    WordRAM.ListAt.congr hX fun a _ hb => hM3BelowH a (hb.trans_le hXE)
  -- Level guarantees and child family bounds
  let F := finishedChildFamily route G (buildLevelVerts start s k) Δ L s k (fun c => start + c * s) sts
  have hGood : (levelDataOfFamily route G start s k Δ L F).Good G start s k M r Δ L L' bh :=
    hTrace.levelGood hHyp (by change 1 ≤ k; omega) hs rfl
  have hFlen : ∀ c < k, (F c).length ≤ maxM := by
    intro c hc
    have hSlotLe := injectEnd_child_le_slot hTrace hHyp (fun _ => rfl) hInjMatch hInjFull
      hInjArch3 hPost3 c hc
    change 2 + 2 * (F c).length ≤ 2 + T * s at hSlotLe
    have h2MaxM : 2 * maxM = T * s := by
      have h2Half : 2 * (s / 2) = s := by omega
      dsimp [maxM]; calc 2 * (T * (s / 2)) = T * (2 * (s / 2)) := by ring
        _ = T * s := by rw [h2Half]
    omega
  have hFends : ∀ c < k, ∀ e ∈ (F c).map Prod.fst, e.1 < s ∧ e.2 < s := by
    intro c hc e he
    have hSh : (start + c * s + e.1, start + c * s + e.2) ∈
        ((levelDataOfFamily route G start s k Δ L F).host c).edges := by
      simp only [levelDataOfFamily, shiftEdges]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hMem := (hGood.graph c hc).2.2.2.1 _ hSh
    simp only [buildLevelChild, mem_shiftSet, Finset.mem_range] at hMem
    exact hMem
  have hFwalk : ∀ c < k, ∀ e < (F c).length, ((F c).getD e ((0, 0), [])).2.length ≤ d := by
    intro c hc e he
    have hEm : e < ((levelDataOfFamily route G start s k Δ L F).host c).m := by
      simpa [levelDataOfFamily, Graph.m, shiftEdges] using he
    have hL := hGood.embedLength c hc e hEm
    simpa [levelDataOfFamily, List.getD_eq_getElem _ _ he] using hL
  -- Step 4: run Back!
  obtain ⟨vFinal, stFinal, cBack, hRunBack, hEncLeV, hVLeSpace, hListAtF, hPresF, hZeroF,
    hCostBack⟩ :=
    nonSingleton_back_runs (w := w) (K := K) (C := C) (router := router) (core := core)
      (route := route) (routeCost := routeCost) (sR := sR) (coreCost := coreCost) (sC := sC)
      (G := G) (g := g) (x := x) (start := start) (s := s) (k := k) (M := M) (r := r)
      (Δ := Δ) (L := L) (L' := L') (bh := bh) (h := h) (heap₁ := heap₁) (injEnd := injEnd)
      (β := β) (p := p) (prior := prior) (later := later) (initMem := mem) (sts := sts)
      (st := st3) (ω := ω)
      hp hRouter hPlayer hC hGE hXE hValid hHost hPos hExp hBh hs hk hEven hSpace hArgW
      hGraphAt3 hVertsAt3 hM3BelowH hRounds3 hInjArch3 hInjEndBound' hFlen hFends hFwalk
      ((h3r 0 (by omega) (by omega)).trans h1r0)
      ((h3r 1 (by omega) (by omega)).trans h1r1)
      ((h3r 2 (by omega) (by omega)).trans h1r2)
      ((h3r 3 (by omega) (by omega)).trans h1r3)
      ((h3r 4 (by omega) (by omega)).trans h1r4)
      ((h3r 7 (by omega) (by omega)).trans h1r7)
      ((h3r 8 (by omega) (by omega)).trans h1r8)
      ((h3r 11 (by omega) (by omega)).trans h1r11)
      ((h3r 12 (by omega) (by omega)).trans h1r12)
      ((h3r 13 (by omega) (by omega)).trans h1r13)
      ((h3r 15 (by omega) (by omega)).trans h1r15)
      ((h3r 16 (by omega) (by omega)).trans h1r16)
      ((h3r 20 (by omega) (by omega)).trans h1r20)
      ((h3other 25 (by omega)).trans h2r25)
      h3r26
  -- Aggregate cost bound
  obtain ⟨hTotCost, _⟩ := nonSingleton_cost_and_len_le
    (K := K) (C := C) (sR := sR) (sC := sC) (G := G) (start := start) (s := s) (k := k)
    (M := M) (r := r) (Δ := Δ) (L := L) (L' := L') (bh := bh)
    (injRouteCost := (buildFullRouteContract w K route routeCost sR G
      (buildLevelVerts start s k) (injPairs s k D.offset sts) Δ L
      (buildLevelVerts start s k).card 2).cost [] (fun _ => 0))
    (injFinishCost := (buildFinishBatchContract w (D.injectionData sts Ms emb)).cost [] (fun _ => 0))
    (F := F) hPlayer hHost hPos hExp hBh hs hk hEven hFlen hFwalk
    hInjRouteCost hInjFinishCost
  -- Combine Setup, Game (Loop ;; Inj), and Back into buildLevelNonSingletonProc!
  have hRunGame : Runs w p ω (buildLevelNonSingletonGame (b + 1) (b + 41))
      st1 .normal st3 (cLoop + cInj + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st2, cLoop, cInj, hRunLoop, hRunInj, rfl⟩)
  have hRunFront : Runs w p ω (buildLevelNonSingletonFront (b + 34) (b + 35) (b + 1) (b + 41))
      (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos)
      .normal st3 (cSetup + (cLoop + cInj + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, cSetup, cLoop + cInj + 1, hRunSetup, hRunGame, rfl⟩)
  have hRunProc : Runs w p ω
      (buildLevelNonSingletonProc (b + 34) (b + 35) (b + 1) (b + 41) (b + 44)
        (b + 45) (b + 46) (b + 57) (b + 14))
      (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos)
      (.returned vFinal)
      stFinal ((cSetup + (cLoop + cInj + 1) + 1) + cBack + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st3, cSetup + (cLoop + cInj + 1) + 1, cBack, hRunFront, hRunBack, rfl⟩)
  refine ⟨levelDataOfFamily route G start s k Δ L F, vFinal, stFinal,
    (cSetup + (cLoop + cInj + 1) + 1) + cBack + 1,
    hRunProc, hEncLeV, hVLeSpace, hListAtF, hPresF, hZeroF, hGood, ?_⟩
  rw [buildInjectEnd_cost_eq] at hCostInj
  simp only [buildChoiceLoopContract, Expr.size, argsSize] at hCostLoop hCostInj
  have hDlim : D.limit = limit := rfl
  have hDcnt : D.count = k := rfl
  have hDcs : D.base.childSize = s := rfl
  rw [hDlim] at hCostLoop
  rw [hDcnt, hDcs] at hCostInj
  set injRC := (buildFullRouteContract w K route routeCost sR G
    (buildLevelVerts start s k) (injPairs s k D.offset sts) Δ L
    (buildLevelVerts start s k).card 2).cost [] (fun _ => 0)
  set injFC := (buildFinishBatchContract w (D.injectionData sts Ms emb)).cost [] (fun _ => 0)
  change cInj ≤ 15 + ((k * (120 * s + 260) + 64) + injRC + 70 +
    (60 * k + 16 + injFC + 90) + 120) + 1 at hCostInj
  dsimp only [F, limit, T, maxM, d] at hCostLoop hCostInj hCostBack hTotCost ⊢
  linarith only [hCostSetup, hCostLoop, hCostInj, hCostBack, hTotCost]

/-! ### Main theorem: `buildLevelProcs` meets `ProvidesBuildLevel` -/

/-- The assembled one-parent procedure block `buildLevelProcs` meets the published
`ProvidesBuildLevel` contract for every parent group and valid player parameters,
with explicit scratch space `buildLevelSpace` and multiplicative constant `buildLevelConst K C`. -/
theorem buildLevelProcs_providesBuildLevel {w K C router core : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {p : Program} {prior later : List Stmt}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w K route routeCost sR p router)
    (hCore : ∀ M r, ProvidesCore w K M r (coreCost M r) (sC M r) p core)
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : RouteCostLe routeCost C)
    (hCoreCost : CoreCostBound coreCost) :
    ProvidesBuildLevel w (buildLevelConst K C) (buildLevelSpace sR sC) p prior.length := by
  intro G start s k M r Δ L L' bh
  let b := prior.length
  have hEntry := buildLevelProcs_lookup_entry hp
  refine meetsContract_of_runs hEntry fun args mem pos ω hArgW hPre => ?_
  obtain ⟨⟨g, x, h, rfl, hG, hX, hGE, hXE, hValid, hHost, hk2, hs1, hsPar, hsN, hRank, hDeg, hsL,
    β, hPos, hExp, hBh⟩, hZero, hSpace⟩ := hPre
  change ZeroFrom mem h at hZero
  change h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w at hSpace
  have h1W : 1 < 2 ^ w := by
    have h1 : h + (singletonSpace sR G k Δ L bh + G.n + 100) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left (le_max_left _ _) h) hSpace
    omega
  have hArgs12 : argsSize (List.range 12 |>.map Expr.reg) = 12 := by decide
  refine runs_start_le ?_
  unfold buildLevelEntryProc
  refine runs_cond_le (v := if s = 1 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs]))
      (Expr.eval_const h1W) h1W) ?_ ?_
  · -- Singleton branch: s = 1
    intro hsEq1
    have hsEq : s = 1 := by by_contra hne; simp [hne] at hsEq1
    subst hsEq
    have hSingSpace : h + singletonSpace sR G k Δ L bh + G.n + 100 < 2 ^ w := by
      have h1 : h + (singletonSpace sR G k Δ L bh + G.n + 100) < 2 ^ w :=
        lt_of_le_of_lt (Nat.add_le_add_left (le_max_left _ _) h) hSpace
      omega
    have hStartLe : start + k * 1 ≤ G.n := levelVerts_end_le_n hHost le_rfl (by omega)
    have hCardW : (buildLevelVerts start 1 k).card < 2 ^ w := by
      rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; omega
    have ht24 := buildLevelProcs_lookup_tail hp 24 (by decide)
    simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht24
    have hSpecConn := buildLevelProcs_connAll_meetsContract (w := w) (K := K) (C := C)
      (sR := sR) (G := G) (start := start) (s := 1) (k := k) (Δ := Δ) (L := L) (bh := bh)
      hp hRouter hPlayer hC hValid hPos hExp hBh hCardW
    have hSpecSing := buildSingletonProc_meetsContract (w := w) (K := K) (C := C)
      (route := route) (sR := sR) (G := G) (start := start) (k := k) (M := M) (r := r)
      (Δ := Δ) (L := L) (L' := L') (bh := bh) (by simpa [b] using ht24) hPlayer hSpecConn
    have hSingPre : (buildSingletonContract w K C route sR G start k M r Δ L L' bh).pre
        (buildLevelArgs g x start 1 k M r Δ L L' bh h) mem :=
      ⟨g, x, h, rfl, hG, hX, hGE, hXE, hZero, hValid, hHost, hk2, by omega, by omega, by omega,
       by omega, β, hPos, hExp, hBh⟩
    refine runs_seq_call_le hSpecSing
      (vs := buildLevelArgs g x start 1 k M r Δ L L' bh h)
      (by simp [List.range_succ, evalArgs, Expr.eval, startState, buildLevelArgs])
      hArgW hSingPre ?_
    intro v mem' _ hPostS
    obtain ⟨_, _, _, heqS, hLoS, hHiS, hAtS, hFrS, hZS, hGoodS⟩ := hPostS
    simp only [buildLevelArgs, List.cons.injEq, and_true, true_and] at heqS
    obtain ⟨rfl, rfl, rfl⟩ := heqS
    obtain ⟨hCostS, _, _⟩ := singleton_cost_and_len_le
      (K := K) (C := C) (sR := sR) (sC := sC) (M := M) (r := r) (L' := L')
      hPlayer hHost hPos hExp hBh hk2
    let D_sing := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
    have hSingLeSpace : singletonSpace sR G k Δ L bh ≤ buildLevelSpace sR sC G 1 k M r Δ L L' bh :=
      le_trans (by omega) (le_max_left _ _)
    refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
    · refine ⟨⟨by change h ≤ v; omega, by change v ≤ h + buildLevelSpace sR sC G 1 k M r Δ L L' bh; omega,
        hFrS, hZS, trivial⟩,
        g, x, h, D_sing, rfl, hAtS, hLoS, hGoodS⟩
    · simp only [buildLevelContract, heapContract, buildSingletonContract, Expr.size]
      rw [hArgs12]
      omega
  · -- Non-singleton branch: 1 < s
    intro hsNe1
    have hsNe : s ≠ 1 := by intro heq; simp [heq] at hsNe1
    have hsGt1 : 1 < s := by omega
    have hEven : s % 2 = 0 := hsPar.resolve_left hsNe
    have ht25 := buildLevelProcs_lookup_tail hp 25 (by decide)
    simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht25
    -- Wrap buildLevelNonSingleton_runs as a call to procedure b + 59
    have hCallNonSing : ∃ o st' c,
        Runs w p ω (.call 12 (b + 59) (List.range 12 |>.map Expr.reg))
          (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos) o st' c ∧
        (∃ (D_level : BuildLevelData) (v : ℕ),
          o = .normal ∧
          st'.regs 12 = v ∧
          h + (D_level.encode k).length ≤ v ∧
          v ≤ h + buildLevelSpace sR sC G s k M r Δ L L' bh ∧
          ListAt st'.mem h (D_level.encode k) ∧
          (∀ a < h, st'.mem a = mem a) ∧
          ZeroFrom st'.mem v ∧
          D_level.Good G start s k M r Δ L L' bh) ∧
        c + 20 ≤ buildLevelCost (buildLevelConst K C) G s k M r Δ L L' bh := by
      obtain ⟨D_level, v, stBody, cBody, hRunBody, hEncLeV, hVLeSp, hAtB, hPrB, hZB, hGoodB, hCostB⟩ :=
        buildLevelNonSingleton_runs (w := w) (K := K) (C := C) (router := router) (core := core)
          (G := G) (g := g) (x := x) (start := start) (s := s) (k := k) (M := M) (r := r)
          (Δ := Δ) (L := L) (L' := L') (bh := bh) (h := h) (pos := pos) (ω := ω)
          hp hRouter (hCore M r) hPlayer hC hCoreCost hArgW hG hX hGE hXE hZero hValid hHost
          hPos hExp hBh hsGt1 hk2 hEven hsN hRank hDeg hsL hSpace
      have hEvalArgs : evalArgs w (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos)
          (List.range 12 |>.map Expr.reg) = some (buildLevelArgs g x start s k M r Δ L L' bh h) := by
        simp [List.range_succ, evalArgs, Expr.eval, startState, buildLevelArgs]
      have hCallRun : Runs w p ω (.call 12 (b + 59) (List.range 12 |>.map Expr.reg))
          (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos) .normal
          { (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos) with
            regs := Function.update (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos).regs
              12 v
            mem := stBody.mem
            pos := stBody.pos }
          (argsSize (List.range 12 |>.map Expr.reg) + cBody + 1) :=
        runs_call_iff.mpr ⟨buildLevelArgs g x start s k M r Δ L L' bh h,
          buildLevelNonSingletonProc (b + 34) (b + 35) (b + 1) (b + 41) (b + 44)
            (b + 45) (b + 46) (b + 57) (b + 14),
          .returned v, stBody, cBody, hEvalArgs, by simpa [b] using ht25,
          hRunBody, rfl, rfl, rfl⟩
      refine ⟨.normal, _, _, hCallRun,
        ⟨D_level, v, rfl, by simp, hEncLeV, hVLeSp, hAtB, hPrB, hZB, hGoodB⟩, ?_⟩
      rw [hArgs12]
      omega
    obtain ⟨o1, st1, c1, hRun1, ⟨D_level, v, rfl, hr12, hEncLeV, hVLeSp, hAt1, hPr1, hZ1, hGood1⟩, hCost1⟩ :=
      hCallNonSing
    have hRetRun : Runs w p ω (.ret (.reg 12)) st1 (.returned v) st1 2 :=
      runs_ret_iff.mpr ⟨v, Expr.eval_reg_of_eq hr12, rfl, rfl, rfl⟩
    refine ⟨.returned v, st1, c1 + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨st1, c1, 2, hRun1, hRetRun, rfl⟩), ?_, ?_⟩
    · refine ⟨⟨by change h ≤ v; omega,
        by change v ≤ h + buildLevelSpace sR sC G s k M r Δ L L' bh; omega,
        hPr1, hZ1, trivial⟩,
        g, x, h, D_level, rfl, hAt1, hEncLeV, hGood1⟩
    · simp only [buildLevelContract, heapContract, Expr.size]
      omega

end MinCostFlow.HierPaths

