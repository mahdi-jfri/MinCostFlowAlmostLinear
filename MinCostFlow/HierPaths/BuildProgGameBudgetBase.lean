module

public import MinCostFlow.HierPaths.BuildProgChildTrace
public import MinCostFlow.HierPaths.BuildProgSec01
public import MinCostFlow.HierPaths.BuildProgReclaim
public import MinCostFlow.HierPaths.BuildProgSingleton
public import MinCostFlow.HierPaths.BuildProgCoreLevel
public import MinCostFlow.HierPaths.BuildProgWalkCollect
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Space, word, and cost budgets for the one-parent level builder

This file instantiates `ChoiceLoopData` for a non-singleton parent group (`1 < s`), defines the
explicit scratch-space function `buildLevelSpace` and constant `buildLevelConst`, proves the fixed
memory layout, unconditional per-trace heap bound, uniform round and loop budgets
(`ChoiceRoundBudget`, `ChoiceLoopFit`), final injection fit (`InjectEndFit`), and aggregate cost
and output-size bounds matching `buildLevelCost`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Size-sensitive operation-count bound of the core cut player (matching `IsCorePlayer.cost_le`).
-/
def CoreCostBound (coreCost : ℕ → ℕ → ℕ → Graph → ℕ) : Prop :=
  ∀ M r q (G : Graph), 1 ≤ q → q ≤ r → G.IsValid → G.IsLoopless →
    (NOf M r) ^ (q - 1) < G.n → G.n ≤ (NOf M r) ^ q →
    (∀ v < G.n, G.deg v ≤ deltaParam M) →
    coreCost M r q G ≤ G.n * (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)

/-- Maximum core scratch space over child graph encodings of length up to `slotWords`. -/
def maxCoreSpace (sC : ℕ → ℕ) (slotWords : ℕ) : ℕ :=
  (Finset.range (slotWords + 1)).sup sC

/-- Maximum router scratch space over pair encodings of length up to `maxPLen` and parameter
budgets up to `parCap`. -/
def maxRouteSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (gn gLen maxPLen parCap : ℕ) : ℕ :=
  (Finset.range (maxPLen + 1)).sup (fun pLen => routerSpaceUpTo sR gn gLen pLen parCap)

/-- Total scratch and output space above `h` needed by the one-parent level builder
for both singleton (`s = 1`) and non-singleton (`1 < s`) parents. -/
def buildLevelSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (sC : ℕ → ℕ → ℕ → ℕ)
    (G : Graph) (s k M r Δ L L' bh : ℕ) : ℕ :=
  let T := buildLevelDegree L'
  let d := routePathLen Δ bh L
  let slotWords := 2 + T * s
  let maxPLen := 2 * k + 1 + k * s
  let heap0Off := T + 4 * k + 1 + k * slotWords
  let coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
  let routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length maxPLen (Δ + L + max 2 (s * k))
  let injEndOff := heap0Off + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n)
  let sec0Max := k + 1 + k * slotWords
  let sec1Max := k + 1 + k * (T * s + 1 + T * s * d)
  let walkMax := k + k * (T * s)
  let scratchMid := maxCoreSpace (sC M r) slotWords + routeCap +
    6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60
  let nonSing :=
    injEndOff + walkMax + sec0Max + sec1Max + T + scratchMid +
    connAllSpace sR G s k Δ L d + NOf M r + d + G.n + 100
  max (singletonSpace sR G k Δ L bh + G.n + 100) nonSing

/-- Uniform per-round tail cost budget after the core scan. -/
def levelTailBudget (K C : ℕ) (G : Graph) (s k Δ L bh : ℕ) : ℕ :=
  let X := s * k
  let d := routePathLen Δ bh L
  let R := routeCong Δ bh L
  (4 * (K * (C + 10) + 280) + 1500) * (k * (X + G.m + 1) * (d + 1) * (R + 1))

/-- Uniform per-iteration step cost budget for the certified game loop. -/
def levelStepBudget (K C : ℕ) (G : Graph) (s k M r Δ L L' bh : ℕ) : ℕ :=
  let X := s * k
  let T := buildLevelDegree L'
  let coreTerm := (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)
  (2 * K + 700) * (X * (coreTerm + T + 1)) + levelTailBudget K C G s k Δ L bh + 10

/-- Multiplicative constant in `buildLevelCost` derived from the player constant `K`
and router operation-count constant `C`. -/
def buildLevelConst (K C : ℕ) : ℕ :=
  12 * (K * (C + 10) + 280) + 18000

/-- Concrete `ChoiceLoopData` laid out starting at heap address `h` for a non-singleton parent. -/
def levelChoiceData (K : ℕ) (route : RouterFn) (routeCost : RouterCostFn)
    (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (coreCost : ℕ → ℕ → ℕ → Graph → ℕ) (sC : ℕ → ℕ)
    (G : Graph) (g x start s k M r Δ L L' bh h : ℕ) : ChoiceLoopData :=
  let limit := 49 * L' + 1
  let slotWords := 2 + (limit + 1) * s
  let directory := h
  let saved := directory + limit
  let graphs := saved + k
  let offsets := graphs + k
  let slots := offsets + k
  let replies := slots + k * slotWords
  let heap0 := replies + k + 1
  let childAddr := fun c => slots + c * slotWords
  let base : BuildRoundData :=
    { K := K
      M := M
      r := r
      q := coreLevel M r s
      childSize := s
      Δ := Δ
      L := L
      pathBound := routePathLen Δ bh L
      host := G
      verts := buildLevelVerts start s k
      jobs := modelGameJobs s k (fun c => start + c * s) childAddr (fun _ => ChildState.init)
      core := fun _ _ => .cut ∅
      coreCost := coreCost M r
      coreSpace := sC
      route := route
      routeCost := routeCost
      routeSpace := sR }
  let addrs : BuildRoundAddrs :=
    { graphs := graphs, offsets := offsets, heap := heap0, replies := replies, host := g, verts := x }
  ⟨base, addrs, k, start, childAddr, saved, directory, L'⟩

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Projection lemmas for `levelChoiceData` -/

theorem lcd_limit (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).limit =
      49 * L' + 1 := rfl

theorem lcd_slotWords (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).geometry.slotWords =
      2 + buildLevelDegree L' * s := rfl

theorem lcd_dir (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).directory = h := rfl

theorem lcd_saved (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).saved =
      h + (49 * L' + 1) := rfl

theorem lcd_graphs (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).addrs.graphs =
      h + (49 * L' + 1) + k := rfl

theorem lcd_offsets (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).addrs.offsets =
      h + (49 * L' + 1) + k + k := rfl

theorem lcd_replies (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).addrs.replies =
      h + (49 * L' + 1) + k + k + k + k * (2 + buildLevelDegree L' * s) := rfl

theorem lcd_heap (K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) :
    (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h).addrs.heap =
      h + (49 * L' + 1) + k + k + k + k * (2 + buildLevelDegree L' * s) + k + 1 := rfl

/-! ### Basic parameter and space helpers -/

theorem rangeCost_zero_le_mul {f : ℕ → ℕ} {n B : ℕ} (h : ∀ i < n, f i ≤ B) :
    rangeCost f 0 n ≤ n * B := by
  suffices ∀ m lo, (∀ i, lo ≤ i → i < lo + m → f i ≤ B) → rangeCost f lo (lo + m) ≤ m * B by
    simpa using this n 0 (fun i _ hi => h i (by omega))
  intro m
  induction m with
  | zero => intro lo _; simp [rangeCost]
  | succ m ih =>
    intro lo hlo
    rw [rangeCost_step (by omega)]
    have h1 := hlo lo le_rfl (by omega)
    have h2 : rangeCost f (lo + 1) (lo + (m + 1)) ≤ m * B := by
      have heq : lo + (m + 1) = (lo + 1) + m := by omega
      rw [heq]
      exact ih (lo + 1) (fun i hi1 hi2 => hlo i (by omega) (by omega))
    rw [Nat.succ_mul]
    omega

theorem le_maxCoreSpace (sC : ℕ → ℕ) {m cap : ℕ} (hm : m ≤ cap) :
    sC m ≤ maxCoreSpace sC cap := by
  unfold maxCoreSpace
  exact Finset.le_sup (f := sC) (Finset.mem_range.mpr (by omega))

theorem le_maxRouteSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (gn gLen parCap : ℕ) {m cap : ℕ} (hm : m ≤ cap) :
    routerSpaceUpTo sR gn gLen m parCap ≤ maxRouteSpace sR gn gLen cap parCap := by
  unfold maxRouteSpace
  exact Finset.le_sup (f := fun pLen => routerSpaceUpTo sR gn gLen pLen parCap)
    (Finset.mem_range.mpr (by omega))

theorem levelVerts_end_le_n {G : Graph} {start s k Δ L : ℕ}
    (hHost : HostPre G (buildLevelVerts start s k) Δ L) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    start + k * s ≤ G.n := by
  have hks : 1 ≤ k * s := Nat.mul_pos hk hs
  have hmem : start + k * s - 1 ∈ buildLevelVerts start s k := by
    simp only [buildLevelVerts, Finset.mem_Ico]; omega
  have hlt := Finset.mem_range.mp (hHost.1 hmem)
  omega

theorem one_le_r_of_one_lt_s {M r s : ℕ} (hs : 1 < s) (hsN : s ≤ (NOf M r) ^ r) : 1 ≤ r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst hr0
  simp at hsN
  omega

theorem bh_ge_two {β : ℝ} {bh : ℕ} (hbh : max 2 (2 / β) ≤ (bh : ℝ)) : 2 ≤ bh := by
  have h2 : (2 : ℝ) ≤ (bh : ℝ) := (le_max_left 2 (2 / β)).trans hbh
  exact_mod_cast h2

theorem ell_le_WParam_pow (M r : ℕ) :
    ell M ≤ (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) := by
  have hW : ell M ≤ WParam ParamConfig.default M := by
    unfold WParam LParam; omega
  have hW1 : 1 ≤ WParam ParamConfig.default M := by
    unfold WParam; omega
  calc ell M ≤ WParam ParamConfig.default M := hW
    _ = (WParam ParamConfig.default M) ^ 1 := (Nat.pow_one _).symm
    _ ≤ (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
        Nat.pow_le_pow_right hW1 (by omega)

theorem pairsWords_length_of_card_le {pairs : List (Finset ℕ × Finset ℕ)} {s : ℕ}
    (h : ∀ p ∈ pairs, p.1.card + p.2.card ≤ s) :
    (pairsWords pairs).length ≤ 2 * pairs.length + 1 + pairs.length * s := by
  induction pairs with
  | nil => simp [pairsWords, length_layoutList]
  | cons p rest ih =>
    have h1 := h p (by simp)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [pairsWords, length_layoutList, List.flatMap_cons, List.cons_append,
      List.nil_append, List.length_cons, List.map_cons, List.sum_cons, finsetWords,
      Finset.length_sort, Nat.succ_mul] at h2 ⊢
    omega

/-! ### Fixed layout and game hypotheses -/

/-- `levelChoiceData` satisfies `GameFixedLayout` whenever `h + buildLevelSpace < 2 ^ w`. -/
theorem levelChoiceData_fixedLayout {w K : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ}
    (hGE : g + G.encode.length ≤ h)
    (hXE : x + (finsetWords (buildLevelVerts start s k)).length ≤ h)
    (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hs : 1 < s) (hk : 2 ≤ k)
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w) :
    GameFixedLayout w (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).geometry := by
  have hNonSing : h + (let T := buildLevelDegree L'
      let d := routePathLen Δ bh L
      let slotWords := 2 + T * s
      let maxPLen := 2 * k + 1 + k * s
      let heap0Off := T + 4 * k + 1 + k * slotWords
      let coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
      let routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length maxPLen (Δ + L + max 2 (s * k))
      let injEndOff := heap0Off + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n)
      let sec0Max := k + 1 + k * slotWords
      let sec1Max := k + 1 + k * (T * s + 1 + T * s * d)
      let walkMax := k + k * (T * s)
      let scratchMid := maxCoreSpace (sC M r) slotWords + routeCap +
        6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60
      injEndOff + walkMax + sec0Max + sec1Max + T + scratchMid +
        connAllSpace sR G s k Δ L d + NOf M r + d + G.n + 100) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
  have hGnW : G.n < 2 ^ w := by dsimp only at hNonSing; omega
  have hEndLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
  have hBits : 3 < 2 ^ w := by dsimp only at hNonSing; omega
  let limit := 49 * L' + 1
  let slotWords := 2 + (limit + 1) * s
  refine ⟨hBits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ s; omega
  · exact hGE
  · exact hXE
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · intro c hc
    have hMul : (c + 1) * slotWords ≤ k * slotWords := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at hMul
    change h + limit + k + k + k ≤ h + limit + k + k + k + c * slotWords ∧
      h + limit + k + k + k + c * slotWords + slotWords ≤ h + limit + k + k + k + k * slotWords
    omega
  · intro c hc c' hc' hne
    change h + limit + k + k + k + c * slotWords + slotWords ≤ h + limit + k + k + k + c' * slotWords ∨
      h + limit + k + k + k + c' * slotWords + slotWords ≤ h + limit + k + k + k + c * slotWords
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · left
      have hMul : (c + 1) * slotWords ≤ c' * slotWords := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at hMul; omega
    · right
      have hMul : (c' + 1) * slotWords ≤ c * slotWords := Nat.mul_le_mul_right _ hgt
      rw [Nat.succ_mul] at hMul; omega
  · change h + limit + k + k + k ≤ h + limit + k + k + k + k * slotWords
    exact Nat.le_add_right _ _
  · exact le_rfl
  · intro c hc
    change start + c * s + s < 2 ^ w
    have hMul : (c + 1) * s ≤ k * s := Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at hMul
    omega

/-- `levelChoiceData` satisfies `ChoiceGameHyp`. -/
theorem levelChoiceData_hyp {K : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L') :
    ChoiceGameHyp (levelChoiceData K route routeCost sR coreCost sC G g x start s k M r Δ L L' bh h) β bh :=
  ⟨hPlayer, hValid, hHost, hPos, hExp, hBh,
   buildLevel_isChildren (start := start) (k := k) (by omega),
   hEven, hsN, hRank, hDeg, hsL, le_rfl⟩

/-! ### Unconditional per-trace heap bound -/

theorem choicePairs_card_le {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {sts : ℕ → ChildState} {ans : ℕ → CoreResult} {bump : ℕ → ℕ}
    (h : ChoiceGameHyp D β bh)
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (ans i)) :
    ∀ p ∈ ((D.round sts).withReplies ans bump).pairs, p.1.card + p.2.card ≤ D.base.childSize := by
  intro p hp
  rw [show ((D.round sts).withReplies ans bump).pairs = ((D.round sts).withReplies ans).pairs from rfl,
    D.pairs_eq] at hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hck, ha, U, hU⟩ := mem_choiceRequesting.mp hc
  have hReq : choiceRequest D.base.childSize (D.offset c) (sts c)
      (answerByChild D.count sts ans c) =
      some (shiftSet (D.offset c) (bisectOf D.base.childSize U),
        shiftSet (D.offset c) (Finset.range D.base.childSize \ bisectOf D.base.childSize U)) := by
    simp [choiceRequest, ha, hU]
  have hProps := choiceRequest_props h.even (D.certify_children hCert c hck ha) hReq
  rw [hReq, Option.getD_some]
  dsimp only at hProps ⊢
  have hCard := Finset.card_le_card (Finset.union_subset hProps.1 hProps.2.1)
  rw [Finset.card_union_of_disjoint hProps.2.2.1] at hCard
  have hRHS : (shiftSet (D.offset c) (Finset.range D.base.childSize)).card = D.base.childSize := by
    rw [card_shiftSet, Finset.card_range]
  omega

/-- Purely algebraic bound on the route reply address, pair words length, and round record end
for any certified round replies `ans`, valid core bump `bump`, and valid router bump `rBump`. -/
theorem round_step_bounds {D : ChoiceLoopData} {β : ℝ} {bh heap : ℕ}
    {sts : ℕ → ChildState} {ans : ℕ → CoreResult} {bump : ℕ → ℕ} {rBump : ℕ}
    (h : ChoiceGameHyp D β bh)
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (ans i))
    (hBump : (D.round sts).ValidBump ans bump)
    (hRBump : ((D.round sts).withReplies ans bump).ValidRouteBump rBump)
    (hSlot : ∀ i < (D.round sts).jobs.count,
      ((D.round sts).jobs.graph i).encode.length ≤ D.geometry.slotWords) :
    let B := (D.round sts).withReplies ans bump rBump
    let A := D.atHeap heap
    (pairsWords B.pairs).length ≤ 2 * D.count + 1 + D.count * D.base.childSize ∧
    B.routeReply A ≤ heap + roundCoreCap D + 5 * (D.base.childSize * D.count) + 7 * D.count + 2 ∧
    B.record A + 2 + B.jobs.count ≤
      heap + roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        roundCoreCap D + roundRouteCap D + D.base.host.n := by
  let B := (D.round sts).withReplies ans bump rBump
  let A := D.atHeap heap
  have hPrep : B.prepared A ≤ heap + roundCoreCap D := prepPrefix_le_validBump hBump hSlot heap
  have hCnt : B.jobs.count ≤ D.count := D.active_le sts
  have hIdxLe : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices, batchJobIndices, cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  have hPairsLen : B.pairs.length = B.indices.length := length_batchJobPairs ..
  have hPairsCard : ∀ p ∈ B.pairs, p.1.card + p.2.card ≤ D.base.childSize :=
    choicePairs_card_le h hCert
  have hPW : (pairsWords B.pairs).length ≤ 2 * D.count + 1 + D.count * D.base.childSize := by
    have h1 := pairsWords_length_of_card_le hPairsCard
    have h2 : B.pairs.length ≤ D.count := by omega
    have h3 : B.pairs.length * D.base.childSize ≤ D.count * D.base.childSize :=
      Nat.mul_le_mul_right _ h2
    omega
  have hRBumpLe : rBump ≤ roundRouteCap D := by
    have hSup : routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
          (pairsWords B.pairs).length (D.base.Δ + D.base.L + max 2 D.base.verts.card) ≤
        (Finset.range (2 * D.count + 1 + D.count * D.base.childSize + 1)).sup
          (fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
            pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card)) :=
      Finset.le_sup
        (f := fun pLen => routerSpaceUpTo D.base.routeSpace D.base.host.n D.base.host.encode.length
          pLen (D.base.Δ + D.base.L + max 2 D.base.verts.card))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hPW))
    exact hRBump.trans (Nat.mul_le_mul_left (D.base.verts.card + 1) hSup)
  have hRR : B.routeReply A ≤ heap + roundCoreCap D + 5 * (D.base.childSize * D.count) + 7 * D.count + 2 := by
    change buildBatchEnd (B.prepared A + 1 + B.jobs.count) B.indices.length D.base.childSize ≤ _
    unfold buildBatchEnd
    have hMul : B.indices.length * D.base.childSize ≤ D.count * D.base.childSize :=
      Nat.mul_le_mul_right _ (by omega)
    have hksEq : D.count * D.base.childSize = D.base.childSize * D.count := Nat.mul_comm _ _
    omega
  refine ⟨hPW, hRR, ?_⟩
  by_cases hem : B.indices.isEmpty = true
  · have hRec : B.record A = B.prepared A + 1 + B.jobs.count := by
      unfold BuildRoundData.record; simp [hem]
    change B.record A + 2 + B.jobs.count ≤ _
    rw [hRec]
    unfold roundNonHoleCap
    omega
  · have hne : B.indices.isEmpty = false := Bool.eq_false_iff.mpr hem
    obtain ⟨Ms, emb, hRes, hMatch, hFull, hLast⟩ := h.matched hCert hne
    have hResB : B.result.1 = .matched Ms emb := hRes
    have hMlen : Ms.length = B.indices.length :=
      (D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne hRes).1
    have hRowLe : ∀ j < Ms.length, (Ms.getD j []).length ≤ D.base.childSize := by
      intro j hj
      have hjP : j < B.pairs.length := by omega
      have h1 : (Ms.getD j []).length = (B.pairs[j]'hjP).1.card := hFull j hjP
      have h2 := hPairsCard _ (List.getElem_mem hjP)
      omega
    have hFlatLe : Ms.flatten.length ≤ D.base.childSize * D.count := by
      have hgen : ∀ n ≤ Ms.length, (Ms.take n).flatten.length ≤ n * D.base.childSize := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hn
          rw [List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
            List.flatten_singleton, Nat.succ_mul]
          have h1 := ih (Nat.le_of_succ_le hn)
          have h2 : (Ms[n]'hn).length ≤ D.base.childSize := by
            have := hRowLe n hn; rwa [List.getD_eq_getElem _ _ hn] at this
          omega
      have h1 := hgen Ms.length le_rfl
      rw [List.take_length] at h1
      have h2 : Ms.length * D.base.childSize ≤ D.count * D.base.childSize :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.mul_comm D.count D.base.childSize] at h2
      exact h1.trans h2
    have hWalkLe : ∀ j < Ms.flatten.length, (emb j).length ≤ D.base.pathBound := by
      intro j hj
      have hLen : (emb j).length ≤ routePathLen D.base.Δ B.result.2 D.base.L :=
        hMatch.2.2.2.2.1 j hj
      have hMono : routePathLen D.base.Δ B.result.2 D.base.L ≤ routePathLen D.base.Δ bh D.base.L := by
        unfold routePathLen; gcongr; exact hLast
      exact hLen.trans (hMono.trans h.path)
    have hRec : B.record A = (B.applyData Ms emb).cursor
        (B.routedEnd A + 4 + Ms.flatten.length + D.base.pathBound + 1 + D.base.host.n) Ms.length := by
      unfold BuildRoundData.record
      simp [hne, hResB]
      rfl
    have hRoutedEq : B.routedEnd A = B.routeReply A + (routeResultWords (.matched Ms emb)).length + rBump := by
      unfold BuildRoundData.routedEnd; rw [hResB]; rfl
    have hResLen := routeMatched_length_le hWalkLe
    have hCur := applyBatch_cursor_le (B.applyData Ms emb)
      (B.routedEnd A + 4 + Ms.flatten.length + D.base.pathBound + 1 + D.base.host.n)
      D.base.pathBound hWalkLe
    have hFlatD : Ms.flatten.length * D.base.pathBound ≤
        D.base.childSize * D.count * D.base.pathBound :=
      Nat.mul_le_mul_right _ hFlatLe
    have hFlatD1 : Ms.flatten.length * (D.base.pathBound + 1) ≤
        D.base.childSize * D.count * D.base.pathBound + D.base.childSize * D.count := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    change B.record A + 2 + B.jobs.count ≤
      heap + roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        roundCoreCap D + roundRouteCap D + D.base.host.n
    rw [hRec]
    change (B.applyData Ms emb).cursor
      (B.routedEnd A + 4 + Ms.flatten.length + D.base.pathBound + 1 + D.base.host.n) Ms.length ≤
      B.routedEnd A + 4 + Ms.flatten.length + D.base.pathBound + 1 + D.base.host.n +
      Ms.flatten.length * (D.base.pathBound + 1) at hCur
    unfold roundNonHoleCap
    omega

/-- Unconditional upper bound on the heap cursor after `t ≤ D.limit` iterations of `ChoiceLoopTrace`. -/
theorem choiceLoopTrace_heap_le {w t heap : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) (h : ChoiceGameHyp D β bh)
    (ht : t ≤ D.limit) :
    heap ≤ D.addrs.heap +
      t * (roundNonHoleCap D.base.childSize D.count D.base.pathBound +
        roundCoreCap D + roundRouteCap D + D.base.host.n) := by
  induction hTrace with
  | start => simp
  | skip _ _ ih =>
    have := ih (Nat.le_of_succ_le ht)
    rw [Nat.succ_mul]; omega
  | @run t heap sts mem v after tr _ ans bump rBump hCert hBump hRBump hPost ih =>
    have hPrev := ih (Nat.le_of_succ_le ht)
    have hSlot : ∀ i < (D.round sts).jobs.count,
        ((D.round sts).jobs.graph i).encode.length ≤ D.geometry.slotWords := by
      intro i hi
      obtain ⟨hInv, _⟩ := tr.certified.invariant h.router h.host h.positive h.expansion
        h.denominator h.children h.even (coreLevel_le h.coreSize)
      have hEnc := (gameGraph_bounds_of_inv (hInv (D.active sts i) (D.active_mem hi).1)).2.2.1
      exact hEnc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : t ≤ D.limit + 1)) _)
    have hv : v = ((D.round sts).withReplies ans bump rBump).record (D.atHeap heap) := hPost.1
    have hStep : ((D.round sts).withReplies ans bump rBump).record (D.atHeap heap) + 2 +
        (D.round sts).jobs.count ≤
        heap + roundNonHoleCap D.base.childSize D.count D.base.pathBound +
          roundCoreCap D + roundRouteCap D + D.base.host.n :=
      (round_step_bounds (heap := heap) h hCert hBump hRBump hSlot).2.2
    rw [hv, Nat.succ_mul]
    omega


end MinCostFlow.HierPaths
