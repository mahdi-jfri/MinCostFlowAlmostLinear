module

public import MinCostFlow.HierPaths.BuildProgGameBudgetBase
public import MinCostFlow.HierPaths.BuildProgGameBudgetRound
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Final injection fit and aggregate level cost and size budgets

Proves `levelChoiceData_injectEndFit`, `singleton_cost_and_len_le`,
`levelChoiceData_injectCost_le`, and `nonSingleton_cost_and_len_le`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Final injection fit and end-cursor bound -/

/-- The finished certified game trace satisfies `InjectEndFit` and ends within `h + injEndOff`. -/
theorem levelChoiceData_injectEndFit {w K heap₁ runEnd : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L')
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w)
    (hTrace : ChoiceLoopTrace w
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h)
      initial
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).limit
      heap₁ sts mem)
    (hRunLe : runEnd ≤ bh)
    (hMatch : RouteMatchedSpec G (buildLevelVerts start s k)
      (injPairs s k (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts)
      Δ L runEnd 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs s k
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts).length),
      (Ms.getD i []).length = ((injPairs s k
        (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts)[i]'hi).1.card) :
    let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
    let slots := h + D.limit + k + k + k
    let pairs := injPairs s k D.offset sts
    InjectEndFit w D heap₁ slots pairs Ms emb sts := by
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  set T := buildLevelDegree L'
  set d := routePathLen Δ bh L
  set slotWords := 2 + T * s
  set maxPLen := 2 * k + 1 + k * s
  set heap0Off := T + 4 * k + 1 + k * slotWords
  set coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
  set routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length maxPLen (Δ + L + max 2 (s * k))
  set injEndOff := heap0Off + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n)
  set scratchMid := maxCoreSpace (sC M r) slotWords + routeCap +
    6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60
  let slots := h + D.limit + k + k + k
  let pairs := injPairs s k D.offset sts
  let rep := injectReplyBase heap₁ k s
  have hHyp : ChoiceGameHyp D β bh :=
    levelChoiceData_hyp hPlayer hValid hHost hPos hExp hBh hs hEven hsN hRank hDeg hsL
  have hCoreCapEq : roundCoreCap D = coreCap := rfl
  have hXcard : D.base.verts.card = s * k := by
    change (buildLevelVerts start s k).card = s * k
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; ring
  have hRouteCapEq : roundRouteCap D = routeCap := by
    unfold roundRouteCap
    dsimp only [routeCap, maxRouteSpace, maxPLen]
    rw [hXcard]; rfl
  have hHeap1 : heap₁ ≤ D.addrs.heap + D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by
    have h1 := choiceLoopTrace_heap_le hTrace hHyp le_rfl
    rwa [hCoreCapEq, hRouteCapEq] at h1
  have hNonSing : h + injEndOff + scratchMid + G.n + 100 < 2 ^ w := by
    have h1 : h + (injEndOff + (k + k * (T * s)) + (k + 1 + k * slotWords) +
        (k + 1 + k * (T * s + 1 + T * s * d)) + T + scratchMid +
        connAllSpace sR G s k Δ L d + NOf M r + d + G.n + 100) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
    omega
  have hHeap0Le : D.addrs.heap ≤ h + heap0Off := by
    rw [lcd_heap]
    dsimp [heap0Off, slotWords, T, buildLevelDegree]; omega
  have hLimSucc : D.limit + 1 = T := rfl
  have hPairsLen : pairs.length = k := by simp [pairs, injPairs]
  have hMLen : Ms.length = k := hMatch.1.trans hPairsLen
  have hPairsCard : ∀ p ∈ pairs, p.1.card + p.2.card ≤ s := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hSub : savedSet s (sts c) ⊆ Finset.range s := by
      unfold savedSet
      cases hS : (sts c).saved with
      | none => exact Finset.Subset.rfl
      | some S =>
        obtain ⟨hInv, _⟩ := hTrace.certified.invariant hHyp.router hHyp.host hHyp.positive
          hHyp.expansion hHyp.denominator hHyp.children hHyp.even (coreLevel_le hHyp.coreSize)
        exact ((hInv c (List.mem_range.mp hc)).2.2.2.1 S hS).1
    rw [card_shiftSet, card_shiftSet, Finset.card_sdiff_of_subset hSub, Finset.card_range]
    have hCard : (savedSet s (sts c)).card ≤ s := by simpa using Finset.card_le_card hSub
    omega
  have hPW : (pairsWords pairs).length ≤ maxPLen := by
    have h1 := pairsWords_length_of_card_le hPairsCard
    rw [hPairsLen] at h1
    exact h1
  have hSR := le_maxRouteSpace sR G.n G.encode.length (Δ + L + max 2 (s * k)) hPW
  have hMulSR : (D.base.verts.card + 1) *
      routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 D.base.verts.card) ≤ routeCap := by
    rw [hXcard]
    exact Nat.mul_le_mul_left (s * k + 1) hSR
  have hFlatLe : Ms.flatten.length ≤ s * k := by
    have hgen : ∀ n ≤ Ms.length, (Ms.take n).flatten.length ≤ n * s := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        rw [List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
          List.flatten_singleton, Nat.succ_mul]
        have h1 := ih (Nat.le_of_succ_le hn)
        have hnP : n < pairs.length := by omega
        have h2 : (Ms.getD n []).length = (pairs[n]'hnP).1.card := hFull n hnP
        have h3 := hPairsCard _ (List.getElem_mem hnP)
        rw [List.getD_eq_getElem _ _ hn] at h2
        omega
    have h1 := hgen Ms.length le_rfl
    rw [List.take_length, hMLen, Nat.mul_comm] at h1
    exact h1
  have hWalkLe : ∀ j < Ms.flatten.length, (emb j).length ≤ d := by
    intro j hj
    have hLen : (emb j).length ≤ routePathLen Δ runEnd L := hMatch.2.2.2.2.1 j hj
    have hMono : routePathLen Δ runEnd L ≤ d := by dsimp [d]; unfold routePathLen; gcongr
    exact hLen.trans hMono
  have hHeap1Bound : heap₁ ≤ h + injEndOff := by
    have h1 : D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) ≤
        T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp [injEndOff]; omega
  have hRepEq : rep = heap₁ + s + 2 * k + 1 + k * s := by
    unfold rep injectReplyBase buildBatchEnd; omega
  have hksEq : k * s = s * k := Nat.mul_comm k s
  have hStartLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
  have hScr1 : 2 * s + 2 * k + 1 + s * k + routeCap ≤ scratchMid := by
    dsimp [scratchMid]; omega
  refine ⟨fun _ => rfl, ?_, ?_, by change 1 ≤ s; omega, hXcard, by omega, ?_, ?_, ?_⟩
  · change h + D.limit + k + k + k + k * D.geometry.slotWords ≤ D.addrs.heap
    rw [lcd_limit, lcd_slotWords, lcd_heap]; omega
  · change start + k * s < 2 ^ w; omega
  · change rep + s < 2 ^ w; omega
  · change rep + (D.base.verts.card + 1) *
      routerSpaceUpTo sR G.n G.encode.length (pairsWords pairs).length
        (Δ + L + max 2 D.base.verts.card) < 2 ^ w
    omega
  · intro top _ hTopHi
    have hCur : (D.injectionData sts Ms emb).cursor
        (top + 4 + Ms.flatten.length + d + 1 + G.n) Ms.length ≤
        top + 4 + Ms.flatten.length + d + 1 + G.n + Ms.flatten.length * (d + 1) :=
      applyBatch_cursor_le (D.injectionData sts Ms emb)
        (top + 4 + Ms.flatten.length + d + 1 + G.n) d hWalkLe
    have hFlatD : Ms.flatten.length * d ≤ s * k * d := Nat.mul_le_mul_right d hFlatLe
    have hFlatD1 : Ms.flatten.length * (d + 1) ≤ s * k * d + s * k := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have hTopLe : top ≤ rep + routeCap := hTopHi.trans (Nat.add_le_add_left hMulSR rep)
    have hStep : (D.injectionData sts Ms emb).cursor
        (top + 4 + Ms.flatten.length + d + 1 + G.n) Ms.length ≤
        heap₁ + (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by
      dsimp only [roundNonHoleCap] at *
      omega
    have hMul : T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) =
        D.limit * (roundNonHoleCap s k d + coreCap + routeCap + G.n) +
          (roundNonHoleCap s k d + coreCap + routeCap + G.n) := by
      rw [← hLimSucc, Nat.succ_mul]
    have hEndLe : (D.injectionData sts Ms emb).cursor
        (top + 4 + Ms.flatten.length + d + 1 + G.n) Ms.length ≤ h + injEndOff := by
      dsimp [injEndOff]; omega
    change (D.injectionData sts Ms emb).cursor
      (top + 4 + Ms.flatten.length + d + 1 + G.n) Ms.length < 2 ^ w
    omega

/-! ### Aggregate cost and output-length bounds -/

private theorem base_pos_helpers {G : Graph} {s k M r Δ L L' bh : ℕ}
    (_hs : 1 ≤ s) (hk : 2 ≤ k) (hΔ : 1 ≤ Δ) (hL : 1 ≤ L) (hbh : 2 ≤ bh) :
    let X := s * k
    let T := buildLevelDegree L'
    let d := routePathLen Δ bh L
    let R := routeCong Δ bh L
    let coreTerm := (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)
    let base := T * X * (coreTerm + T + 1) +
      (T * k + k * k + 1) * (X + G.m + 1) * (d + 1) * (R + 1) + k * k + 1
    1 ≤ d ∧ 1 ≤ R ∧
    ell M ≤ coreTerm ∧
    T * X * (d + 1) ≤ (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) ∧
    (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base ∧
    (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base ∧
    k * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base ∧
    T * X * (coreTerm + T + 1) ≤ base ∧
    k * k ≤ base ∧ 1 ≤ base := by
  intro X T d R coreTerm base
  have hd1 : 1 ≤ d := by
    dsimp [d]; unfold routePathLen
    have h1 := Nat.mul_pos (Nat.mul_pos hΔ (by omega : 0 < bh)) hL
    have : 32 * Δ * bh * L = 32 * (Δ * bh * L) := by ring
    omega
  have hR1 : 1 ≤ R := by
    dsimp [R]; unfold routeCong routeBatchH
    have h1 := Nat.mul_pos (Nat.mul_pos (by omega : 0 < bh) hΔ) hL
    have h2 : 1 ≤ 16 * bh * Δ * (d + 1) * L := by
      have := Nat.mul_pos h1 (by omega : 0 < d + 1)
      have : 16 * bh * Δ * (d + 1) * L = 16 * (bh * Δ * L * (d + 1)) := by ring
      omega
    exact h2
  have hEll : ell M ≤ coreTerm := by
    have hN : 1 ≤ (NOf M r) ^ 2 := by
      have h4 := four_le_NOf M r
      rw [Nat.pow_two]
      exact Nat.mul_pos (by omega) (by omega)
    exact (ell_le_WParam_pow M r).trans (Nat.le_mul_of_pos_left _ hN)
  have hTXd : T * X * (d + 1) ≤ (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) := by
    have h1 : X ≤ k * (X + G.m + 1) :=
      (by omega : X ≤ X + G.m + 1).trans (Nat.le_mul_of_pos_left _ (by omega))
    have h2 : T * X ≤ T * (k * (X + G.m + 1)) := Nat.mul_le_mul_left T h1
    have h3 : T * X * (d + 1) ≤ (T * k) * (X + G.m + 1) * (d + 1) := by
      have hEq : T * (k * (X + G.m + 1)) = (T * k) * (X + G.m + 1) := by ring
      rw [hEq] at h2
      exact Nat.mul_le_mul_right (d + 1) h2
    exact h3.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hDist : (T * k + k * k + 1) * (X + G.m + 1) * (d + 1) * (R + 1) =
      (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) +
      (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) +
      (X + G.m + 1) * (d + 1) * (R + 1) := by ring
  have hKKB : (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base := by
    dsimp [base]; rw [hDist]; omega
  have hTKB : (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base := by
    dsimp [base]; rw [hDist]; omega
  have hKB : k * (X + G.m + 1) * (d + 1) * (R + 1) ≤ base := by
    have hT1 : 1 ≤ T := by dsimp [T, buildLevelDegree]; omega
    have h1 : k ≤ T * k := Nat.le_mul_of_pos_left k hT1
    have h2 : k * (X + G.m + 1) * (d + 1) * (R + 1) ≤
        (T * k) * (X + G.m + 1) * (d + 1) * (R + 1) := by gcongr
    exact h2.trans hTKB
  refine ⟨hd1, hR1, hEll, hTXd, hKKB, hTKB, hKB, by dsimp [base]; omega, by dsimp [base]; omega,
    by dsimp [base]; omega⟩

/-- Singleton-branch (`s = 1`) cost and output-length bounds against `buildLevelCost` and
`buildLevelSpace`. -/
theorem singleton_cost_and_len_le {K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {sC : ℕ → ℕ → ℕ → ℕ} {G : Graph} {start k M r Δ L L' bh : ℕ} {β : ℝ}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hHost : HostPre G (buildLevelVerts start 1 k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start 1 k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ)) (hk : 2 ≤ k) :
    let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
    connAllCostBound K C G 1 k Δ L bh + 80 * k + 300 ≤
      buildLevelCost (buildLevelConst K C) G 1 k M r Δ L L' bh ∧
    (D.encode k).length ≤ buildLevelSpace sR sC G 1 k M r Δ L L' bh ∧
    (D.encode k).length ≤ buildLevelCost (buildLevelConst K C) G 1 k M r Δ L L' bh := by
  let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
  have hbh2 : 2 ≤ bh := bh_ge_two hBh
  set X := 1 * k
  set T := buildLevelDegree L'
  set d := routePathLen Δ bh L
  set R := routeCong Δ bh L
  set base := T * X * ((NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + T + 1) +
    (T * k + k * k + 1) * (X + G.m + 1) * (d + 1) * (R + 1) + k * k + 1
  obtain ⟨hd1, hR1, _, _, hKKB, _, _, _, hKK, h1B⟩ :=
    base_pos_helpers (G := G) (s := 1) (k := k) (M := M) (r := r) (L' := L')
      le_rfl hk hHost.2.2.1 hHost.2.2.2.2.1 hbh2
  have hKLeKK : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  have hCost : connAllCostBound K C G 1 k Δ L bh + 80 * k + 300 ≤
      buildLevelCost (buildLevelConst K C) G 1 k M r Δ L L' bh := by
    unfold connAllCostBound buildLevelCost buildLevelConst
    change (2 * (K * (C + 10) + 280) + 3000) * (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) +
      250 * (k * k) + 200 + 80 * k + 300 ≤ (12 * (K * (C + 10) + 280) + 18000) * base
    have h1 : (2 * (K * (C + 10) + 280) + 3000) * (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) =
        (2 * (K * (C + 10) + 280) + 3000) * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) := by ring
    rw [h1]
    have h2 : (2 * (K * (C + 10) + 280) + 3000) * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) ≤
        (2 * (K * (C + 10) + 280) + 3000) * base := Nat.mul_le_mul_left _ hKKB
    have h3 : (12 * (K * (C + 10) + 280) + 18000) * base =
        (2 * (K * (C + 10) + 280) + 3000) * base + 10 * (K * (C + 10) + 280) * base +
        15000 * base := by ring
    omega
  have hSec2 := levelConnSec_length_le hPlayer hPos hExp hHost le_rfl (by omega) hBh
  have hEncLen : (D.encode k).length ≤ 5 * k + 6 + (k * k + 1 + k * k * (11 + d)) := by
    unfold BuildLevelData.encode
    rw [length_layoutList]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have hS0 : (csrList k fun c => (D.host c).encode).length = 3 * k + 1 := by
      have heq : (fun c => (D.host c).encode) = fun _ => [G.n, 0] := by
        funext c; simp [D, levelDataOfFamily, shiftEdges, Graph.encode, Graph.m]
      rw [heq, csrList, List.length_append, length_csrOffsets, length_csrData_eq]
      simp [List.sum_replicate]; omega
    have hS1 : (csrList k fun c => csrList (D.host c).m (D.emb c)).length = 2 * k + 1 := by
      have heq : (fun c => csrList (D.host c).m (D.emb c)) = fun _ => [0] := by
        funext c; simp [D, levelDataOfFamily, shiftEdges, Graph.m, csrList, csrOffsets, csrData]
      rw [heq, csrList, List.length_append, length_csrOffsets, length_csrData_eq]
      simp [List.sum_replicate]; omega
    have hS2 : (csrList (k * k) fun i =>
        csrList (D.conn (i / k) (i % k)).length fun j =>
          connWords ((D.conn (i / k) (i % k)).getD j (0, 0, []))).length ≤
        k * k + 1 + k * k * (11 + d) := by
      change (csrList (k * k) (levelConnRow route G start 1 k Δ L)).length ≤ _
      have h1 : 8 + 3 * 1 + 1 * d = 11 + d := by omega
      simpa [d, h1] using hSec2
    rw [hS0, hS1]
    linarith only [hS2]
  have hSpaceLe : (D.encode k).length ≤ buildLevelSpace sR sC G 1 k M r Δ L L' bh := by
    have hSing : (D.encode k).length ≤ singletonSpace sR G k Δ L bh + G.n + 100 := by
      dsimp only [singletonSpace, connAllSpace]
      have h11 : k * k * (11 + d) = k * k * (8 + 3 * 1 + 1 * d) := by ring
      change (D.encode k).length ≤ 5 * k + 6 + (2 * (k * k) + k * k * connPairSpace sR G 1 k Δ L d +
        (k * k + 1 + k * k * (8 + 3 * 1 + 1 * d)) + 10) + 1 + G.n + 100
      omega
    exact hSing.trans (le_max_left _ _)
  have hLenCost : (D.encode k).length ≤ buildLevelCost (buildLevelConst K C) G 1 k M r Δ L L' bh := by
    unfold buildLevelCost buildLevelConst
    change (D.encode k).length ≤ (12 * (K * (C + 10) + 280) + 18000) * base
    have hKKd : k * k * (11 + d) ≤ 11 * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) := by
      have h1 : 11 + d ≤ 11 * (d + 1) := by omega
      have h2 : k * k * (11 + d) ≤ k * k * (11 * (d + 1)) := Nat.mul_le_mul_left _ h1
      have h3 : k * k * (d + 1) ≤ (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) := by
        have ha : 1 ≤ X + G.m + 1 := by omega
        have hb : 1 ≤ R + 1 := by omega
        calc k * k * (d + 1) = (k * k) * 1 * (d + 1) * 1 := by ring
          _ ≤ (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) := by gcongr
      have h4 : k * k * (11 * (d + 1)) = 11 * (k * k * (d + 1)) := by ring
      omega
    have h5 : 5 * k + 6 + (k * k + 1 + k * k * (11 + d)) ≤ 25 * base := by
      have hKKdB : k * k * (11 + d) ≤ 11 * base := hKKd.trans (Nat.mul_le_mul_left 11 hKKB)
      omega
    have h6 : 25 * base ≤ (12 * (K * (C + 10) + 280) + 18000) * base :=
      Nat.mul_le_mul_right base (by omega)
    exact hEncLen.trans (h5.trans h6)
  exact ⟨hCost, hSpaceLe, hLenCost⟩

/-- Bounds on the final injection's routing and matching-application costs. -/
theorem levelChoiceData_injectCost_le {w K C heap₁ runEnd : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hPlayer : IsMatchingPlayer route routeCost) (hC : RouteCostLe routeCost C)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L')
    (hTrace : ChoiceLoopTrace w
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h)
      initial
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).limit
      heap₁ sts mem)
    (hRes : lemma1Route route G (buildLevelVerts start s k)
      (injPairs s k (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts)
      Δ L = (.matched Ms emb, runEnd))
    (hRunLe : runEnd ≤ bh)
    (hMatch : RouteMatchedSpec G (buildLevelVerts start s k)
      (injPairs s k (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts)
      Δ L runEnd 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs s k
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts).length),
      (Ms.getD i []).length = ((injPairs s k
        (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).offset sts)[i]'hi).1.card) :
    let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
    (buildFullRouteContract w K route routeCost sR G (buildLevelVerts start s k)
      (injPairs s k D.offset sts) Δ L (buildLevelVerts start s k).card 2).cost [] (fun _ => 0) ≤
      4 * (K * (C + 10) + 280) *
        (k * (s * k + G.m + 1) * (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1)) ∧
    (buildFinishBatchContract w (D.injectionData sts Ms emb)).cost [] (fun _ => 0) ≤
      380 * (s * k) * (routePathLen Δ bh L + 1) + 330 * k + 112 := by
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  let pairs := injPairs s k D.offset sts
  set d := routePathLen Δ bh L
  set R := routeCong Δ bh L
  set unit := k * (s * k + G.m + 1) * (d + 1) * (R + 1)
  have hHyp : ChoiceGameHyp D β bh :=
    levelChoiceData_hyp hPlayer hValid hHost hPos hExp hBh hs hEven hsN hRank hDeg hsL
  have hPre : RouterPre G (buildLevelVerts start s k) pairs Δ L := hTrace.injectRouterPre hHyp
  have hPairsLen : pairs.length = k := by simp [pairs, injPairs]
  have hMLen : Ms.length = k := hMatch.1.trans hPairsLen
  have hXcard : (buildLevelVerts start s k).card = s * k := by
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; ring
  have hUnitPos : 1 ≤ unit := by
    have h1 : 1 ≤ k * (s * k + G.m + 1) := Nat.mul_pos (by omega) (by omega)
    have h2 : 1 ≤ (d + 1) * (R + 1) := Nat.mul_pos (by omega) (by omega)
    calc 1 = 1 * 1 := rfl
      _ ≤ (k * (s * k + G.m + 1)) * ((d + 1) * (R + 1)) := Nat.mul_le_mul h1 h2
      _ = unit := by dsimp [unit]; ring
  refine ⟨?_, ?_⟩
  · have hFR := buildFullRouteCost_graph_le (w := w) (K := K) (C := C) (sR := sR)
      (args := []) (mem := fun _ => 0) hPlayer hPre (by rw [hPairsLen]; omega)
      (fun b' hb' => hC G (buildLevelVerts start s k) pairs Δ L b' 0
        hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1 hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 hb' hPre.2.2.2.2.2.2)
      (buildLevelVerts start s k).card 2 le_rfl
    have hRunEq : (fullRoute route G (buildLevelVerts start s k) pairs Δ L
        (buildLevelVerts start s k).card 2).2 = runEnd := congrArg Prod.snd hRes
    rw [hRunEq] at hFR
    have hMono := routeBoundG_mono_b (C := K * (C + 10) + 280) (G := G)
      (X := buildLevelVerts start s k) (pairs := pairs) (Δ := Δ) (L := L) hRunLe
    have hRB : routeBoundG (K * (C + 10) + 280) G (buildLevelVerts start s k) pairs Δ L bh ≤
        (K * (C + 10) + 280) * (unit + 1) := by
      unfold routeBoundG
      rw [hXcard, hPairsLen]
      have hR1 : R ≤ R + 1 := Nat.le_succ R
      have hProd : k * (s * k + G.m + 1) * (d + 1) * R ≤ unit := by dsimp [unit]; gcongr
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hProd 1)
    have h2 : 2 * ((K * (C + 10) + 280) * (unit + 1)) ≤ 4 * (K * (C + 10) + 280) * unit := by
      have hL : 2 * ((K * (C + 10) + 280) * (unit + 1)) =
          2 * (K * (C + 10) + 280) * unit + 2 * (K * (C + 10) + 280) := by ring
      have hR2 : 4 * (K * (C + 10) + 280) * unit =
          2 * (K * (C + 10) + 280) * unit + 2 * (K * (C + 10) + 280) * unit := by ring
      have h3 : 2 * (K * (C + 10) + 280) ≤ 2 * (K * (C + 10) + 280) * unit :=
        Nat.le_mul_of_pos_right _ hUnitPos
      rw [hL, hR2]
      exact Nat.add_le_add_left h3 _
    exact hFR.trans ((Nat.mul_le_mul_left 2 (hMono.trans hRB)).trans h2)
  · apply applyBatch_finishCost_le (w := w) (s := s) (k := k) (d := d)
    · change Ms.length ≤ k; omega
    · intro i hi
      change i < Ms.length at hi
      have hiP : i < pairs.length := by omega
      have h1 : (Ms.getD i []).length = (pairs[i]'hiP).1.card := hFull i hiP
      have hpEq : pairs[i]'hiP = (shiftSet (D.offset i) (Finset.range s \ savedSet s (sts i)),
          shiftSet (D.offset i) (savedSet s (sts i))) := by
        simp [pairs, injPairs]
      rw [hpEq, card_shiftSet] at h1
      have h2 : (Finset.range s \ savedSet s (sts i)).card ≤ s := by
        calc (Finset.range s \ savedSet s (sts i)).card ≤ (Finset.range s).card :=
              Finset.card_le_card Finset.sdiff_subset
          _ = s := Finset.card_range s
      change (Ms.getD i []).length ≤ s
      omega
    · intro i hi j hj
      change i < Ms.length at hi
      have hfl : flatIndex Ms i j < Ms.flatten.length :=
        (getD_flatten_flatIndex Ms (0, 0) hi hj).1
      have hLen : (emb (flatIndex Ms i j)).length ≤ routePathLen Δ runEnd L :=
        hMatch.2.2.2.2.1 (flatIndex Ms i j) hfl
      have hMono : routePathLen Δ runEnd L ≤ d := by dsimp [d]; unfold routePathLen; gcongr
      exact hLen.trans hMono

/-- Non-singleton (`1 < s`) aggregate cost and output-length bounds against `buildLevelCost`
and `buildLevelSpace`. -/
theorem nonSingleton_cost_and_len_le {K C : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {start s k M r Δ L L' bh injRouteCost injFinishCost : ℕ} {β : ℝ}
    {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0)
    (hFlen : ∀ c < k, (F c).length ≤ buildLevelDegree L' * (s / 2))
    (hFwalk : ∀ c < k, ∀ e < (F c).length, ((F c).getD e ((0, 0), [])).2.length ≤ routePathLen Δ bh L)
    (hInjRoute : injRouteCost ≤
      4 * (K * (C + 10) + 280) *
        (k * (s * k + G.m + 1) * (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1)))
    (hInjFinish : injFinishCost ≤
      380 * (s * k) * (routePathLen Δ bh L + 1) + 330 * k + 112) :
    let T := buildLevelDegree L'
    let limit := 49 * L' + 1
    let d := routePathLen Δ bh L
    let maxM := T * (s / 2)
    let s0 := (sec0Words G.n start s k F).length
    let s1 := (sec1Words k F).length
    let s2 := (csrList (k * k) (levelConnRow route G start s k Δ L)).length
    let totalCost :=
      (32 * ell M + 24 * s + 120) +
      (52 * k + 16) +
      (limit * (levelStepBudget K C G s k M r Δ L L' bh + 9) + 12) +
      ((k * (120 * s + 260) + 64) + injRouteCost + 70 +
        (60 * k + 16 + injFinishCost + 90) + 120) +
      ((limit + 1) * (32 * (s * k) + 170 * k + 260) + 120) +
      (k * (50 * maxM + 105) + 60) +
      (k * (maxM * (17 * d + 85) + 115) + 60) +
      connAllCostBound K C G s k Δ L bh +
      (17 * (s0 + s1 + s2) + 12) +
      500
    totalCost ≤ buildLevelCost (buildLevelConst K C) G s k M r Δ L L' bh ∧
    4 + s0 + s1 + s2 ≤ buildLevelSpace sR sC G s k M r Δ L L' bh := by
  set T := buildLevelDegree L'
  set limit := 49 * L' + 1
  set X := s * k
  set d := routePathLen Δ bh L
  set R := routeCong Δ bh L
  set maxM := T * (s / 2)
  set s0 := (sec0Words G.n start s k F).length
  set s1 := (sec1Words k F).length
  set s2 := (csrList (k * k) (levelConnRow route G start s k Δ L)).length
  set coreTerm := (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)
  set CK := K * (C + 10) + 280
  set base := T * X * (coreTerm + T + 1) +
    (T * k + k * k + 1) * (X + G.m + 1) * (d + 1) * (R + 1) + k * k + 1
  have hbh2 : 2 ≤ bh := bh_ge_two hBh
  obtain ⟨hd1, hR1, hEll, hTXd, hKKB, hTKB, hKB, hCoreB, hKK, h1B⟩ :=
    base_pos_helpers (G := G) (s := s) (k := k) (M := M) (r := r) (L' := L')
      (by omega) hk hHost.2.2.1 hHost.2.2.2.2.1 hbh2
  have h2Half : 2 * (s / 2) = s := by omega
  have h2MaxM : 2 * maxM = T * s := by
    dsimp [maxM]; calc 2 * (T * (s / 2)) = T * (2 * (s / 2)) := by ring
      _ = T * s := by rw [h2Half]
  have hMaxMLe : maxM ≤ T * s := by omega
  have hKMaxM : k * maxM ≤ T * X := by
    calc k * maxM ≤ k * (T * s) := Nat.mul_le_mul_left k hMaxMLe
      _ = T * X := by dsimp [X]; ring
  have hTXdLeB : T * X * (d + 1) ≤ base := hTXd.trans hTKB
  have hTXLeB : T * X ≤ base := (Nat.le_mul_of_pos_right _ (by omega)).trans hTXdLeB
  have hX4 : 4 ≤ X := by
    calc 4 = 2 * 2 := rfl
      _ ≤ s * k := Nat.mul_le_mul (by omega) hk
  have hT2 : 2 ≤ T := by dsimp [T, buildLevelDegree]; omega
  have hXLeTX : X ≤ T * X := Nat.le_mul_of_pos_left X (by omega)
  have hSLeX : s ≤ X := Nat.le_mul_of_pos_right s (by omega)
  have hKLeX : k ≤ X := Nat.le_mul_of_pos_left k (by omega)
  have hTLeTX : T ≤ T * X := Nat.le_mul_of_pos_right T (by omega)
  have hLimLeT : limit ≤ T := by dsimp [limit, T, buildLevelDegree]; omega
  have hLim1 : limit + 1 = T := rfl
  -- Section length bounds
  have hS0Le : s0 ≤ k + 1 + k * (2 + T * s) := by
    have h1 := sec0Words_length_le (gn := G.n) (start := start) (s := s) (k := k) (maxM := maxM) hFlen
    have h2 : 3 * k + 1 + 2 * (k * maxM) = k + 1 + k * (2 + 2 * maxM) := by ring
    rw [h2, h2MaxM] at h1
    exact h1
  have hKSlot : k * (2 + T * s) = 2 * k + T * X := by dsimp [X]; ring
  have hS0B : s0 ≤ 5 * (T * X) := by omega
  have hS1Le : s1 ≤ 2 * k + 1 + k * (maxM * (d + 1)) :=
    sec1Words_length_le (k := k) (d := d) (maxM := maxM) hFlen hFwalk
  have hS1LeSpace : s1 ≤ k + 1 + k * (T * s + 1 + T * s * d) := by
    have h1 : maxM * (d + 1) ≤ T * s * (d + 1) := Nat.mul_le_mul_right (d + 1) hMaxMLe
    have h2 : k * (maxM * (d + 1)) ≤ k * (T * s * (d + 1)) := Nat.mul_le_mul_left k h1
    have h3 : 2 * k + 1 + k * (T * s * (d + 1)) = k + 1 + k * (T * s + 1 + T * s * d) := by ring
    omega
  have hS1B : s1 ≤ 4 * (T * X * (d + 1)) := by
    have h1 : k * (maxM * (d + 1)) = (k * maxM) * (d + 1) := by ring
    have h2 : (k * maxM) * (d + 1) ≤ T * X * (d + 1) := Nat.mul_le_mul_right (d + 1) hKMaxM
    have h3 : T * X ≤ T * X * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hS2Le : s2 ≤ k * k + 1 + k * k * (8 + 3 * s + s * d) :=
    levelConnSec_length_le hPlayer hPos hExp hHost (by omega) (by omega) hBh
  have hS2B : s2 ≤ 13 * base := by
    have h1 : 8 + 3 * s + s * d ≤ 11 * s * (d + 1) := by
      have hR : 11 * s * (d + 1) = 11 * (s * d) + 11 * s := by ring
      omega
    have h2 : k * k * (8 + 3 * s + s * d) ≤ 11 * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) := by
      calc k * k * (8 + 3 * s + s * d)
          ≤ k * k * (11 * s * (d + 1)) := Nat.mul_le_mul_left _ h1
        _ = 11 * ((k * k) * s * (d + 1) * 1) := by ring
        _ ≤ 11 * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) := by
            have hsX : s ≤ X + G.m + 1 := by omega
            have h1R : 1 ≤ R + 1 := by omega
            gcongr
    have h3 : k * k * (8 + 3 * s + s * d) ≤ 11 * base := h2.trans (Nat.mul_le_mul_left 11 hKKB)
    omega
  -- Bound each cost component against base
  have hC1 : 32 * ell M + 24 * s + 120 ≤ 180 * base := by
    have hCT : coreTerm ≤ T * X * (coreTerm + T + 1) :=
      (by omega : coreTerm ≤ coreTerm + T + 1).trans
        (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
    have hEllB : ell M ≤ base := hEll.trans (hCT.trans hCoreB)
    omega
  have hC2 : 52 * k + 16 ≤ 70 * base := by omega
  have hC3 : limit * (levelStepBudget K C G s k M r Δ L L' bh + 9) + 12 ≤
      (4 * CK + 2 * K + 2250) * base := by
    have hStepEq : levelStepBudget K C G s k M r Δ L L' bh + 9 =
        (2 * K + 700) * (X * (coreTerm + T + 1)) +
        (4 * CK + 1500) * (k * (X + G.m + 1) * (d + 1) * (R + 1)) + 19 := by
      unfold levelStepBudget levelTailBudget; dsimp only
    rw [hStepEq]
    have h1 := Nat.mul_le_mul_right ((2 * K + 700) * (X * (coreTerm + T + 1)) +
        (4 * CK + 1500) * (k * (X + G.m + 1) * (d + 1) * (R + 1)) + 19) hLimLeT
    have hDist : T * ((2 * K + 700) * (X * (coreTerm + T + 1)) +
        (4 * CK + 1500) * (k * (X + G.m + 1) * (d + 1) * (R + 1)) + 19) =
        (2 * K + 700) * (T * X * (coreTerm + T + 1)) +
        (4 * CK + 1500) * ((T * k) * (X + G.m + 1) * (d + 1) * (R + 1)) + 19 * T := by ring
    have hA : (2 * K + 700) * (T * X * (coreTerm + T + 1)) ≤ (2 * K + 700) * base :=
      Nat.mul_le_mul_left _ hCoreB
    have hB : (4 * CK + 1500) * ((T * k) * (X + G.m + 1) * (d + 1) * (R + 1)) ≤
        (4 * CK + 1500) * base := Nat.mul_le_mul_left _ hTKB
    have hTot : (4 * CK + 2 * K + 2250) * base =
        (2 * K + 700) * base + (4 * CK + 1500) * base + 50 * base := by ring
    have hTLeB : T ≤ base := hTLeTX.trans hTXLeB
    have h1B' : 1 ≤ base := h1B
    linarith only [h1, hDist, hA, hB, hTot, hTLeB, h1B']
  have hC4 : (k * (120 * s + 260) + 64) + injRouteCost + 70 +
      (60 * k + 16 + injFinishCost + 90) + 120 ≤ (4 * CK + 1700) * base := by
    have h1 : k * (120 * s + 260) = 120 * X + 260 * k := by dsimp [X]; ring
    have h2 : injRouteCost ≤ 4 * CK * base :=
      hInjRoute.trans (Nat.mul_le_mul_left (4 * CK) hKB)
    have hXd : X * (d + 1) ≤ base := by
      have h1' : X * (d + 1) ≤ T * X * (d + 1) :=
        Nat.mul_le_mul_right (d + 1) hXLeTX
      exact h1'.trans hTXdLeB
    have hXB : X ≤ base := hXLeTX.trans hTXLeB
    have hKB' : k ≤ base := hKLeX.trans hXB
    have h1B' : 1 ≤ base := h1B
    have hFin : injFinishCost ≤ 822 * base := by
      have h380 : 380 * X * (d + 1) = 380 * (X * (d + 1)) := by ring
      linarith only [hInjFinish, h380, hXd, hKB', h1B']
    have hTot : (4 * CK + 1700) * base = 4 * CK * base + 1700 * base := by ring
    linarith only [h1, h2, hFin, hTot, hXB, hKB', h1B']
  have hC5 : (limit + 1) * (32 * X + 170 * k + 260) + 120 ≤ 600 * base := by
    rw [hLim1]
    have h1 : 32 * X + 170 * k + 260 ≤ 462 * X := by linarith only [hKLeX, hX4]
    have h2 : T * (32 * X + 170 * k + 260) ≤ T * (462 * X) := Nat.mul_le_mul_left T h1
    have h3 : T * (462 * X) = 462 * (T * X) := by ring
    have h1B' : 1 ≤ base := h1B
    linarith only [h2, h3, hTXLeB, h1B']
  have hC6 : k * (50 * maxM + 105) + 60 ≤ 250 * base := by
    have h1 : k * (50 * maxM + 105) = 50 * (k * maxM) + 105 * k := by ring
    have hKMB : k * maxM ≤ base := hKMaxM.trans hTXLeB
    have hKB' : k ≤ base := hKLeX.trans (hXLeTX.trans hTXLeB)
    have h1B' : 1 ≤ base := h1B
    linarith only [h1, hKMB, hKB', h1B']
  have hC7 : k * (maxM * (17 * d + 85) + 115) + 60 ≤ 260 * base := by
    have h1 : maxM * (17 * d + 85) ≤ maxM * (85 * (d + 1)) := Nat.mul_le_mul_left maxM (by omega)
    have h2 : k * (maxM * (17 * d + 85) + 115) ≤ k * (maxM * (85 * (d + 1)) + 115) :=
      Nat.mul_le_mul_left k (by omega)
    have h3 : k * (maxM * (85 * (d + 1)) + 115) = 85 * ((k * maxM) * (d + 1)) + 115 * k := by ring
    have h4 : (k * maxM) * (d + 1) ≤ base := (Nat.mul_le_mul_right (d + 1) hKMaxM).trans hTXdLeB
    have hKB' : k ≤ base := hKLeX.trans (hXLeTX.trans hTXLeB)
    have h1B' : 1 ≤ base := h1B
    linarith only [h2, h3, h4, hKB', h1B']
  have hC8 : connAllCostBound K C G s k Δ L bh ≤ (2 * CK + 3500) * base := by
    unfold connAllCostBound
    change (2 * CK + 3000) * (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) + 250 * (k * k) + 200 ≤
      (2 * CK + 3500) * base
    have h1 : (2 * CK + 3000) * (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) =
        (2 * CK + 3000) * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) := by ring
    rw [h1]
    have h2 : (2 * CK + 3000) * ((k * k) * (X + G.m + 1) * (d + 1) * (R + 1)) ≤
        (2 * CK + 3000) * base := Nat.mul_le_mul_left _ hKKB
    have h3 : (2 * CK + 3500) * base = (2 * CK + 3000) * base + 500 * base := by ring
    have hKK' : k * k ≤ base := hKK
    have h1B' : 1 ≤ base := h1B
    linarith only [h2, h3, hKK', h1B']
  have hC9 : 17 * (s0 + s1 + s2) + 12 ≤ 400 * base := by
    have hS0B' : s0 ≤ 5 * base := hS0B.trans (Nat.mul_le_mul_left 5 hTXLeB)
    have hS1B' : s1 ≤ 4 * base := hS1B.trans (Nat.mul_le_mul_left 4 hTXdLeB)
    have h1B' : 1 ≤ base := h1B
    linarith only [hS0B', hS1B', hS2B, h1B']
  have hKLeCK : K ≤ CK := by
    have : K ≤ K * (C + 10) := Nat.le_mul_of_pos_right K (by omega)
    dsimp [CK]; omega
  refine ⟨?_, ?_⟩
  · unfold buildLevelCost buildLevelConst
    change (32 * ell M + 24 * s + 120) + (52 * k + 16) +
      (limit * (levelStepBudget K C G s k M r Δ L L' bh + 9) + 12) +
      ((k * (120 * s + 260) + 64) + injRouteCost + 70 +
        (60 * k + 16 + injFinishCost + 90) + 120) +
      ((limit + 1) * (32 * X + 170 * k + 260) + 120) +
      (k * (50 * maxM + 105) + 60) +
      (k * (maxM * (17 * d + 85) + 115) + 60) +
      connAllCostBound K C G s k Δ L bh +
      (17 * (s0 + s1 + s2) + 12) + 500 ≤ (12 * CK + 18000) * base
    have hSum : (32 * ell M + 24 * s + 120) + (52 * k + 16) +
        (limit * (levelStepBudget K C G s k M r Δ L L' bh + 9) + 12) +
        ((k * (120 * s + 260) + 64) + injRouteCost + 70 +
          (60 * k + 16 + injFinishCost + 90) + 120) +
        ((limit + 1) * (32 * X + 170 * k + 260) + 120) +
        (k * (50 * maxM + 105) + 60) +
        (k * (maxM * (17 * d + 85) + 115) + 60) +
        connAllCostBound K C G s k Δ L bh +
        (17 * (s0 + s1 + s2) + 12) + 500 ≤
        180 * base + 70 * base + (4 * CK + 2 * K + 2250) * base + (4 * CK + 1700) * base +
        600 * base + 250 * base + 260 * base + (2 * CK + 3500) * base + 400 * base +
        500 * base := by
      have h500 : 500 ≤ 500 * base := Nat.le_mul_of_pos_right 500 h1B
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        hC1 hC2) hC3) hC4) hC5) hC6) hC7) hC8) hC9) h500
    have hColl : 180 * base + 70 * base + (4 * CK + 2 * K + 2250) * base + (4 * CK + 1700) * base +
        600 * base + 250 * base + 260 * base + (2 * CK + 3500) * base + 400 * base +
        500 * base =
        (10 * CK + 2 * K + 9710) * base := by ring
    rw [hColl] at hSum
    have hCoef : 10 * CK + 2 * K + 9710 ≤ 12 * CK + 18000 := by linarith only [hKLeCK]
    exact hSum.trans (Nat.mul_le_mul_right base hCoef)
  · unfold buildLevelSpace
    refine le_trans ?_ (le_max_right _ _)
    have hS2Conn : s2 ≤ connAllSpace sR G s k Δ L d := by
      unfold connAllSpace; omega
    have hS012 : 4 + s0 + s1 + s2 ≤ (k + 1 + k * (2 + T * s)) +
        (k + 1 + k * (T * s + 1 + T * s * d)) + connAllSpace sR G s k Δ L d + 100 := by
      linarith only [hS0Le, hS1LeSpace, hS2Conn]
    refine hS012.trans ?_
    have hadd : ∀ (a u v b1 b2 w c1 c2 c3 z : ℕ),
        u + v + w + z ≤ a + u + v + b1 + b2 + w + c1 + c2 + c3 + z := by intros; omega
    exact hadd _ _ _ _ _ _ _ _ _ _

end MinCostFlow.HierPaths
