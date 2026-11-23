module

public import MinCostFlow.HierPaths.BuildProgGameBudgetBase
import MinCostFlow.HierPaths.BuildProgRouteCost
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Round routing, tail cost, and loop-fit budgets for the one-parent level builder

Proves `buildFullRouteCost_empty_le`, `applyBatch_finishCost_le`, `oneRoundTailCost_le`,
`levelChoiceData_roundBudget`, and `levelChoiceData_loopFit`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Routing and tail cost bounds -/

/-- When `pairs = []`, full routing retries terminate before `b ≥ bh` on a `β`-expander,
charging at most `(K * (C + 4) + 200) * (X.card + G.m + 1) * (d + 1)`. -/
theorem buildFullRouteCost_empty_le {w K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {G : Graph} {X : Finset ℕ} {Δ L bh : ℕ} {β : ℝ}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : RouteCostLe routeCost C)
    (hHost : HostPre G X Δ L) (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn X β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (n : ℕ) :
    (buildFullRouteContract w K route routeCost sR G X [] Δ L n 2).cost [] (fun _ => 0) ≤
      (K * (C + 4) + 200) * (X.card + G.m + 1) * (routePathLen Δ bh L + 1) := by
  let callCost := fun b' => K * (routeCost G X [] Δ L b' 0 + G.encode.length +
    (finsetWords X).length * (L + 1) + (pairsWords []).length + 1)
  let outcome := fun b' => route G X [] Δ L b' 0
  let M := (K * (C + 4) + 200) * (X.card + G.m + 1) * (L + 1)
  have hG : G.encode.length = 2 + 2 * G.m := buildGraph_encode_length G
  have hX : (finsetWords X).length = X.card := Finset.length_sort _
  have hPW : (pairsWords []).length = 1 := by simp [pairsWords, length_layoutList]
  have hVP : ValidTerminalPairs X [] := ⟨fun _ h => by simp at h, by simp⟩
  have hResLen : ∀ b', 2 ≤ b' → (routeResultWords (outcome b')).length ≤ X.card + 7 := by
    intro b' hb'
    have hSpec := hPlayer.spec G X [] Δ L b' 0 hHost.1 hHost.2.1 hHost.2.2.1 hHost.2.2.2.1
      hHost.2.2.2.2.1 hHost.2.2.2.2.2 hb' hVP
    change RouteSpec G X [] Δ L b' 0 (outcome b') at hSpec
    cases hOut : outcome b' with
    | matched Ms emb =>
      rw [hOut] at hSpec
      have := routeResultWords_empty_matched_length hSpec
      omega
    | cut U =>
      rw [hOut] at hSpec
      have hSub := Finset.card_le_card hSpec.1
      simp only [routeResultWords, length_layoutList, List.length_cons, List.length_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, finsetWords, Finset.length_sort]
      omega
  have hStep : ∀ b', 2 ≤ b' →
      callCost b' + 17 * (routeResultWords (outcome b')).length + 70 ≤ M := by
    intro b' hb'
    have hrc := hC G X [] Δ L b' 0 hHost.1 hHost.2.1 hHost.2.2.1 hHost.2.2.2.1
      hHost.2.2.2.2.1 hHost.2.2.2.2.2 hb' hVP
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.mul_one] at hrc
    have hA : 1 ≤ X.card + G.m + 1 := by omega
    have hL1 : 1 ≤ L + 1 := by omega
    have h1 : routeCost G X [] Δ L b' 0 + G.encode.length + (finsetWords X).length * (L + 1) +
        (pairsWords []).length + 1 ≤ (C + 4) * ((X.card + G.m + 1) * (L + 1)) := by
      rw [hG, hX, hPW]
      have hL2 : 2 ≤ L + 1 := by have := hHost.2.2.2.2.1; omega
      have hAL2 : 2 * (X.card + G.m + 1) ≤ (X.card + G.m + 1) * (L + 1) := by
        rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ hL2
      have hXL : X.card * (L + 1) ≤ (X.card + G.m + 1) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      have hC1 : C ≤ C * ((X.card + G.m + 1) * (L + 1)) :=
        Nat.le_mul_of_pos_right C (Nat.mul_pos hA hL1)
      have hExp4 : (C + 4) * ((X.card + G.m + 1) * (L + 1)) =
          C * ((X.card + G.m + 1) * (L + 1)) + 4 * ((X.card + G.m + 1) * (L + 1)) := by ring
      omega
    have h2 : callCost b' ≤ K * (C + 4) * (X.card + G.m + 1) * (L + 1) := by
      calc callCost b' ≤ K * ((C + 4) * ((X.card + G.m + 1) * (L + 1))) := Nat.mul_le_mul_left K h1
        _ = K * (C + 4) * (X.card + G.m + 1) * (L + 1) := by ring
    have hRL := hResLen b' hb'
    have h3 : 17 * (routeResultWords (outcome b')).length + 70 ≤
        200 * (X.card + G.m + 1) * (L + 1) := by
      have h30 : 17 * (routeResultWords (outcome b')).length + 70 ≤ 200 * (X.card + G.m + 1) := by omega
      exact h30.trans (Nat.le_mul_of_pos_right _ hL1)
    have hM : M = K * (C + 4) * (X.card + G.m + 1) * (L + 1) +
        200 * (X.card + G.m + 1) * (L + 1) := by dsimp [M]; ring
    omega
  have hCutLt : ∀ b' U, 2 ≤ b' → outcome b' = .cut U → b' < bh ∧ U.card ≤ X.card := by
    intro b' U hb' hCut
    have hSpec := hPlayer.spec G X [] Δ L b' 0 hHost.1 hHost.2.1 hHost.2.2.1 hHost.2.2.2.1
      hHost.2.2.2.2.1 hHost.2.2.2.2.2 hb' hVP
    change RouteSpec G X [] Δ L b' 0 (outcome b') at hSpec
    rw [hCut] at hSpec
    obtain ⟨hSub, hCutLe, hU1, hC1⟩ := hSpec
    have hUNE : U.Nonempty := Finset.card_pos.mp (by omega)
    have hCNE : (X \ U).Nonempty := Finset.card_pos.mp (by omega)
    have hUNeX : U ≠ X := by
      intro heq; rw [heq, Finset.sdiff_self] at hCNE; exact Finset.not_nonempty_empty hCNE
    have hExpU := hExp U hSub hUNE hUNeX
    have hMinPos : (0 : ℝ) < min (U.card : ℝ) ((X \ U).card : ℝ) := by
      apply lt_min <;> exact_mod_cast (by omega : 0 < _)
    have hCutR : (b' : ℝ) * (G.cutIn X U : ℝ) ≤ min (U.card : ℝ) ((X \ U).card : ℝ) := by
      have hNat : ((b' * G.cutIn X U : ℕ) : ℝ) ≤ ((min U.card (X \ U).card : ℕ) : ℝ) := by
        exact_mod_cast hCutLe
      simpa [Nat.cast_mul, Nat.cast_min] using hNat
    have hProd : (b' : ℝ) * β * min (U.card : ℝ) ((X \ U).card : ℝ) ≤
        min (U.card : ℝ) ((X \ U).card : ℝ) := by
      calc (b' : ℝ) * β * min (U.card : ℝ) ((X \ U).card : ℝ)
          = (b' : ℝ) * (β * min (U.card : ℝ) ((X \ U).card : ℝ)) := by ring
        _ ≤ (b' : ℝ) * (G.cutIn X U : ℝ) :=
            mul_le_mul_of_nonneg_left hExpU (by positivity)
        _ ≤ min (U.card : ℝ) ((X \ U).card : ℝ) := hCutR
    have h1 : (b' : ℝ) * β ≤ 1 := by nlinarith
    have h2 : (b' : ℝ) ≤ 1 / β := by rw [le_div_iff₀ hPos]; linarith
    have h3 : (1 / β : ℝ) < 2 / β := div_lt_div_of_pos_right (by norm_num) hPos
    have h4 : (b' : ℝ) < (bh : ℝ) := (h2.trans_lt h3).trans_le ((le_max_right 2 (2 / β)).trans hBh)
    exact ⟨by exact_mod_cast h4, Finset.card_le_card hSub⟩
  have hRec : ∀ m b', 2 ≤ b' → buildFullRouteCost callCost outcome m b' ≤ (1 + (bh - b')) * M := by
    intro m
    induction m with
    | zero =>
      intro b' hb'
      simp only [buildFullRouteCost]
      have h1 := hStep b' hb'
      exact h1.trans (Nat.le_mul_of_pos_left M (by omega))
    | succ m ih =>
      intro b' hb'
      simp only [buildFullRouteCost]
      cases hOut : outcome b' with
      | matched Ms emb =>
        have h1 := hStep b' hb'
        rw [hOut] at h1
        exact h1.trans (Nat.le_mul_of_pos_left M (by omega))
      | cut U =>
        obtain ⟨hlt, _⟩ := hCutLt b' U hb' hOut
        have h1 : callCost b' + 40 ≤ M := by
          have := hStep b' hb'; omega
        have h2 := ih (2 * b') (by omega)
        have h3 : 1 + (1 + (bh - 2 * b')) ≤ 1 + (bh - b') := by omega
        calc callCost b' + 40 + buildFullRouteCost callCost outcome m (2 * b')
            ≤ M + (1 + (bh - 2 * b')) * M := Nat.add_le_add h1 h2
          _ = (1 + (1 + (bh - 2 * b'))) * M := by ring
          _ ≤ (1 + (bh - b')) * M := Nat.mul_le_mul_right M h3
  have hBase := hRec n 2 le_rfl
  have hbh2 : 2 ≤ bh := bh_ge_two hBh
  have hbhD : (1 + (bh - 2)) * (L + 1) ≤ routePathLen Δ bh L + 1 := by
    have hΔ := hHost.2.2.1
    have hL := hHost.2.2.2.2.1
    have h1 : (1 + (bh - 2)) * (L + 1) ≤ bh * (2 * L) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : bh * (2 * L) ≤ 32 * Δ * bh * L := by
      have h32 : 2 ≤ 32 * Δ := by omega
      calc bh * (2 * L) = 2 * (bh * L) := by ring
        _ ≤ (32 * Δ) * (bh * L) := Nat.mul_le_mul_right _ h32
        _ = 32 * Δ * bh * L := by ring
    unfold routePathLen; omega
  exact hBase.trans (by
    calc (1 + (bh - 2)) * M
        = (K * (C + 4) + 200) * (X.card + G.m + 1) * ((1 + (bh - 2)) * (L + 1)) := by dsimp [M]; ring
      _ ≤ (K * (C + 4) + 200) * (X.card + G.m + 1) * (routePathLen Δ bh L + 1) :=
          Nat.mul_le_mul_left _ hbhD)

/-- Upper bound on `buildFinishBatchContract.cost` from row count, row length, and walk length bounds. -/
theorem applyBatch_finishCost_le {w s k d : ℕ} {A : ApplyBatchData}
    (hLen : A.matchings.length ≤ k)
    (hRow : ∀ i < A.matchings.length, (A.matchings.getD i []).length ≤ s)
    (hWalk : ∀ i < A.matchings.length, ∀ j < (A.row i).count, ((A.row i).raw j).length ≤ d) :
    (buildFinishBatchContract w A).cost [] (fun _ => 0) ≤
      380 * (s * k) * (d + 1) + 330 * k + 112 := by
  change rangeCost (applyBatchStepCost A) 0 A.matchings.length + 9 * A.matchings.length + 112 ≤ _
  have hStep : ∀ i < A.matchings.length,
      applyBatchStepCost A i ≤ 380 * s * (d + 1) + 320 := by
    intro i hi
    unfold applyBatchStepCost
    dsimp only
    have hcnt : (A.row i).count ≤ s := hRow i hi
    have hInner : rangeCost (fun j => 136 * ((A.row i).raw j).length + 330) 0 (A.row i).count ≤
        (A.row i).count * (136 * d + 330) :=
      rangeCost_zero_le_mul fun j hj => by have := hWalk i hi j hj; omega
    have hMul : (A.row i).count * (136 * d + 330) ≤ s * (136 * d + 330) :=
      Nat.mul_le_mul_right _ hcnt
    have h380 : s * (136 * d + 330) + 47 * s ≤ 380 * s * (d + 1) := by
      have hL : s * (136 * d + 330) + 47 * s = 136 * (s * d) + 377 * s := by ring
      have hR : 380 * s * (d + 1) = 380 * (s * d) + 380 * s := by ring
      rw [hL, hR]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by decide)) (Nat.mul_le_mul_right _ (by decide))
    have h47 : 47 * (A.row i).count ≤ 47 * s := Nat.mul_le_mul_left 47 hcnt
    exact Nat.add_le_add_right (Nat.add_le_add (hInner.trans hMul) h47 |>.trans h380) 320
  have hSum : rangeCost (applyBatchStepCost A) 0 A.matchings.length ≤
      A.matchings.length * (380 * s * (d + 1) + 320) :=
    rangeCost_zero_le_mul hStep
  have hMulK : A.matchings.length * (380 * s * (d + 1) + 320) ≤
      k * (380 * s * (d + 1) + 320) := Nat.mul_le_mul_right _ hLen
  have hEq : k * (380 * s * (d + 1) + 320) = 380 * (s * k) * (d + 1) + 320 * k := by ring
  omega

/-- Every certified round's tail cost fits inside `levelTailBudget`. -/
theorem oneRoundTailCost_le {w K C : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {sts : ℕ → ChildState} {ans : ℕ → CoreResult} {bump : ℕ → ℕ}
    (hK : D.base.K = K)
    (hVerts : D.base.verts = buildLevelVerts D.first D.base.childSize D.count)
    (h : ChoiceGameHyp D β bh)
    (hC : RouteCostLe D.base.routeCost C)
    (hk : 2 ≤ D.count) (hs : 1 < D.base.childSize)
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (ans i)) :
    buildOneRoundTailCost w ((D.round sts).withReplies ans bump) ≤
      levelTailBudget K C D.base.host D.base.childSize D.count D.base.Δ D.base.L bh := by
  let B := (D.round sts).withReplies ans bump
  set G := D.base.host
  set s := D.base.childSize
  set k := D.count
  set d := routePathLen D.base.Δ bh D.base.L
  set R := routeCong D.base.Δ bh D.base.L
  set unit := k * (s * k + G.m + 1) * (d + 1) * (R + 1)
  have hXcard : D.base.verts.card = s * k := by
    rw [hVerts, buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; ring
  have hUnitPos : 1 ≤ unit := by
    have h1 : 1 ≤ k * (s * k + G.m + 1) := Nat.mul_pos (by omega) (by omega)
    have h2 : 1 ≤ (d + 1) * (R + 1) := Nat.mul_pos (by omega) (by omega)
    calc 1 = 1 * 1 := rfl
      _ ≤ (k * (s * k + G.m + 1)) * ((d + 1) * (R + 1)) := Nat.mul_le_mul h1 h2
      _ = unit := by dsimp [unit]; ring
  have hCnt : B.jobs.count ≤ k := D.active_le sts
  have hIdxLe : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices, batchJobIndices, cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  have hPairsLen : B.pairs.length = B.indices.length := length_batchJobPairs ..
  have hSK : s * k ≤ unit := by
    have h1 : s * k ≤ s * k + G.m + 1 := by omega
    have h2 : s * k + G.m + 1 ≤ k * (s * k + G.m + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : k * (s * k + G.m + 1) ≤ k * (s * k + G.m + 1) * (d + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h4 : k * (s * k + G.m + 1) * (d + 1) ≤ unit := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hSKD : (s * k) * (d + 1) ≤ unit := by
    have h1 : s * k ≤ k * (s * k + G.m + 1) :=
      (by omega : s * k ≤ s * k + G.m + 1).trans (Nat.le_mul_of_pos_left _ (by omega))
    have h2 : (s * k) * (d + 1) ≤ k * (s * k + G.m + 1) * (d + 1) := Nat.mul_le_mul_right _ h1
    exact h2.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hKLe : k ≤ unit := (Nat.le_mul_of_pos_left k (by omega : 0 < s)).trans hSK
  have hPre : RouterPre G D.base.verts B.pairs D.base.Δ D.base.L := h.routerPre hCert
  have hFullCost : (buildFullRouteContract w D.base.K D.base.route D.base.routeCost D.base.routeSpace
      G D.base.verts B.pairs D.base.Δ D.base.L D.base.verts.card 2).cost [] (fun _ => 0) ≤
      4 * (K * (C + 10) + 280) * unit := by
    rw [hK]
    by_cases hEmpty : B.pairs = []
    · rw [hEmpty]
      have hE := buildFullRouteCost_empty_le (w := w) (K := K) (sR := D.base.routeSpace)
        h.router hC h.host h.positive h.expansion h.denominator D.base.verts.card
      have hU : (D.base.verts.card + G.m + 1) * (d + 1) ≤ unit := by
        rw [hXcard]
        have h1 : s * k + G.m + 1 ≤ k * (s * k + G.m + 1) := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : (s * k + G.m + 1) * (d + 1) ≤ k * (s * k + G.m + 1) * (d + 1) :=
          Nat.mul_le_mul_right _ h1
        exact h2.trans (Nat.le_mul_of_pos_right _ (by omega))
      have hCoef : K * (C + 4) + 200 ≤ 4 * (K * (C + 10) + 280) := by
        have : K * (C + 4) ≤ K * (C + 10) := Nat.mul_le_mul_left K (by omega)
        omega
      have hAssoc : (K * (C + 4) + 200) * (D.base.verts.card + G.m + 1) * (d + 1) =
          (K * (C + 4) + 200) * ((D.base.verts.card + G.m + 1) * (d + 1)) := by ring
      have hMul := Nat.mul_le_mul hCoef hU
      rw [← hAssoc] at hMul
      exact hE.trans hMul
    · have hPos : 1 ≤ B.pairs.length := List.length_pos_iff.mpr hEmpty
      have hR := buildFullRouteCost_graph_le (w := w) (K := K) (C := C) (sR := D.base.routeSpace)
        (args := []) (mem := fun _ => 0) h.router hPre hPos
        (fun b' hb' => hC G D.base.verts B.pairs D.base.Δ D.base.L b' 0
          hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1 hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 hb' hPre.2.2.2.2.2.2)
        D.base.verts.card 2 le_rfl
      have hne : B.indices.isEmpty = false := by
        apply Bool.eq_false_iff.mpr
        intro h0
        have := List.isEmpty_iff_length_eq_zero.mp h0
        omega
      obtain ⟨_, _, _, _, _, hLast⟩ := h.matched hCert hne
      have hBLe : (fullRoute D.base.route G D.base.verts B.pairs D.base.Δ D.base.L
          D.base.verts.card 2).2 ≤ bh := hLast
      have hMono := routeBoundG_mono_b (C := K * (C + 10) + 280) (G := G) (X := D.base.verts)
        (pairs := B.pairs) (Δ := D.base.Δ) (L := D.base.L) hBLe
      have hRB : routeBoundG (K * (C + 10) + 280) G D.base.verts B.pairs D.base.Δ D.base.L bh ≤
          (K * (C + 10) + 280) * (unit + 1) := by
        unfold routeBoundG
        rw [hXcard]
        have hP : B.pairs.length ≤ k := by omega
        have hR1 : R ≤ R + 1 := Nat.le_succ R
        have hProd : B.pairs.length * (s * k + G.m + 1) * (d + 1) * R ≤ unit := by
          dsimp [unit]; gcongr
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
      exact le_trans hR (le_trans (Nat.mul_le_mul_left 2 (le_trans hMono hRB)) h2)
  have hFinishCost : (match B.result.1 with
      | .matched Ms emb => (buildFinishBatchContract w (B.applyData Ms emb)).cost [] (fun _ => 0)
      | .cut _ => 0) ≤ 850 * unit := by
    cases hRes : B.result.1 with
    | cut _ => exact Nat.zero_le _
    | matched Ms emb =>
      by_cases hEmpty : B.indices.isEmpty = true
      · have hP0 : B.pairs = [] := by
          have : B.pairs.length = 0 := by rw [hPairsLen]; exact List.isEmpty_iff_length_eq_zero.mp hEmpty
          exact List.eq_nil_of_length_eq_zero this
        have hBge2 : 2 ≤ B.result.2 := by
          have hge2 : ∀ n b, 2 ≤ b →
              2 ≤ (fullRoute D.base.route G D.base.verts B.pairs D.base.Δ D.base.L n b).2 := by
            intro n; induction n with
            | zero => intro b hb; exact hb
            | succ n ih =>
              intro b hb; simp only [fullRoute]
              cases D.base.route G D.base.verts B.pairs D.base.Δ D.base.L b 0 with
              | matched _ _ => exact hb
              | cut _ => exact ih (2 * b) (by omega)
          exact hge2 D.base.verts.card 2 le_rfl
        have hSpec := h.router.spec G D.base.verts B.pairs D.base.Δ D.base.L B.result.2 0
          hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1 hPre.2.2.2.2.1 hPre.2.2.2.2.2.1
          hBge2 hPre.2.2.2.2.2.2
        have hResEq : B.result.1 = D.base.route G D.base.verts B.pairs D.base.Δ D.base.L B.result.2 0 := by
          have hgen : ∀ n b, (fullRoute D.base.route G D.base.verts B.pairs D.base.Δ D.base.L n b).1 =
              D.base.route G D.base.verts B.pairs D.base.Δ D.base.L
                (fullRoute D.base.route G D.base.verts B.pairs D.base.Δ D.base.L n b).2 0 := by
            intro n; induction n with
            | zero => intro b; rfl
            | succ n ih =>
              intro b; simp only [fullRoute]
              cases h1 : D.base.route G D.base.verts B.pairs D.base.Δ D.base.L b 0 with
              | matched _ _ => simp [h1]
              | cut _ => exact ih (2 * b)
          exact hgen D.base.verts.card 2
        rw [← hResEq, hRes] at hSpec
        have hM0 : Ms.length = 0 := by simpa [hP0] using hSpec.1
        have hFC := applyBatch_finishCost_le (w := w) (s := s) (k := k) (d := d)
          (A := B.applyData Ms emb) (by change Ms.length ≤ k; omega)
          (fun i hi => by change i < Ms.length at hi; omega)
          (fun i hi => by change i < Ms.length at hi; omega)
        have h380 : 380 * (s * k) * (d + 1) = 380 * ((s * k) * (d + 1)) := by ring
        dsimp only
        omega
      · have hne : B.indices.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
        obtain ⟨Ms', emb', hRes', hMatch, hFull, hLast⟩ := h.matched hCert hne
        rw [hRes] at hRes'
        cases hRes'
        have hMlen : Ms.length = B.indices.length :=
          (D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne hRes).1
        have hPairsCard : ∀ p ∈ B.pairs, p.1.card + p.2.card ≤ s := choicePairs_card_le h hCert
        have hFC := applyBatch_finishCost_le (w := w) (s := s) (k := k) (d := d)
          (A := B.applyData Ms emb) (by change Ms.length ≤ k; omega)
          (fun i hi => by
            change i < Ms.length at hi
            have hiP : i < B.pairs.length := by omega
            have h1 : (Ms.getD i []).length = (B.pairs[i]'hiP).1.card := hFull i hiP
            have h2 := hPairsCard _ (List.getElem_mem hiP)
            change (Ms.getD i []).length ≤ s
            omega)
          (fun i hi j hj => by
            change i < Ms.length at hi
            have hfl : flatIndex Ms i j < Ms.flatten.length :=
              (getD_flatten_flatIndex Ms (0, 0) hi hj).1
            have hLen : (emb (flatIndex Ms i j)).length ≤ routePathLen D.base.Δ B.result.2 D.base.L :=
              hMatch.2.2.2.2.1 (flatIndex Ms i j) hfl
            have hMono : routePathLen D.base.Δ B.result.2 D.base.L ≤ d := by
              dsimp [d]; unfold routePathLen; gcongr
            exact hLen.trans hMono)
        have h380 : 380 * (s * k) * (d + 1) = 380 * ((s * k) * (d + 1)) := by ring
        dsimp only
        omega
  unfold buildOneRoundTailCost BuildRoundData.routeContract buildRoundRouteContract levelTailBudget
  dsimp only
  have h1 : B.pairs.length * (17 * s + 128) ≤ 17 * (s * k) + 128 * k := by
    have hP : B.pairs.length ≤ k := by omega
    have hMul := Nat.mul_le_mul_right (17 * s + 128) hP
    have hEq : k * (17 * s + 128) = 17 * (s * k) + 128 * k := by ring
    omega
  have hL : (4 * (K * (C + 10) + 280) + 1500) * unit =
      4 * (K * (C + 10) + 280) * unit + 1500 * unit := by ring
  change 36 * B.jobs.count + B.pairs.length * (17 * s + 128) +
    (buildFullRouteContract w D.base.K D.base.route D.base.routeCost D.base.routeSpace
      G D.base.verts B.pairs D.base.Δ D.base.L D.base.verts.card 2).cost [] (fun _ => 0) + 160 +
    (match B.result.1 with
     | .matched Ms emb => (buildFinishBatchContract w (B.applyData Ms emb)).cost [] (fun _ => 0)
     | .cut _ => 0) + 110 ≤ (4 * (K * (C + 10) + 280) + 1500) * unit
  omega

/-! ### Uniform round budget and loop fit -/

/-- Every reachable round `t < D.limit` of `levelChoiceData` meets `ChoiceRoundBudget`. -/
theorem levelChoiceData_roundBudget {w K C t heap : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    (hPlayer : IsMatchingPlayer route routeCost) (hC : RouteCostLe routeCost C)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L')
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w)
    (ht : t < (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).limit)
    (hTrace : ChoiceLoopTrace w
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h)
      initial t heap sts mem) :
    ChoiceRoundBudget w (levelTailBudget K C G s k Δ L bh)
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h) heap sts := by
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  have hHyp : ChoiceGameHyp D β bh :=
    levelChoiceData_hyp hPlayer hValid hHost hPos hExp hBh hs hEven hsN hRank hDeg hsL
  have hHeapLe := choiceLoopTrace_heap_le hTrace hHyp ht.le
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
  have hCoreCapEq : roundCoreCap D = coreCap := rfl
  have hXcard : D.base.verts.card = s * k := by
    change (buildLevelVerts start s k).card = s * k
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; ring
  have hRouteCapEq : roundRouteCap D = routeCap := by
    unfold roundRouteCap
    dsimp only [routeCap, maxRouteSpace, maxPLen]
    rw [hXcard]; rfl
  have hNonSing : h + injEndOff + scratchMid < 2 ^ w := by
    have h1 : h + (injEndOff + (k + k * (T * s)) + (k + 1 + k * slotWords) +
        (k + 1 + k * (T * s + 1 + T * s * d)) + T + scratchMid +
        connAllSpace sR G s k Δ L d + NOf M r + d + G.n + 100) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
    omega
  have hHeap0 : D.addrs.heap ≤ h + heap0Off := by
    rw [lcd_heap]
    dsimp [heap0Off, slotWords, T, buildLevelDegree]; omega
  have htLe : t + 1 ≤ T := by
    rw [lcd_limit] at ht; dsimp [T, buildLevelDegree]; omega
  have hHeapStep : heap + (roundNonHoleCap s k d + coreCap + routeCap + G.n) ≤ h + injEndOff := by
    have h1 : (t + 1) * (roundNonHoleCap s k d + coreCap + routeCap + G.n) ≤
        T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
      Nat.mul_le_mul_right _ htLe
    rw [Nat.succ_mul] at h1
    change heap ≤ D.addrs.heap + t * (roundNonHoleCap s k d + roundCoreCap D + roundRouteCap D + G.n) at hHeapLe
    rw [hCoreCapEq, hRouteCapEq] at hHeapLe
    dsimp [injEndOff]; omega
  have hHeapBound : heap ≤ h + injEndOff := by omega
  have hSlotAll : ∀ j < (D.round sts).jobs.count,
      ((D.round sts).jobs.graph j).encode.length ≤ D.geometry.slotWords := by
    intro j hj
    have hInv := (hTrace.certified.invariant hHyp.router hHyp.host hHyp.positive hHyp.expansion
      hHyp.denominator hHyp.children hHyp.even (coreLevel_le hHyp.coreSize)).1
    have hGLen := (gameGraph_bounds_of_inv (hInv (D.active sts j) (D.active_mem hj).1)).2.2.1
    change (gameGraph s (sts (D.active sts j))).encode.length ≤ 2 + t * s at hGLen
    have h1 : t * s ≤ T * s := Nat.mul_le_mul_right s (by omega)
    change (gameGraph s (sts (D.active sts j))).encode.length ≤ 2 + T * s
    omega
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    have hiK : i < k := lt_of_lt_of_le hi (D.active_le sts)
    have hSlotEq : D.geometry.slotWords = slotWords := rfl
    have hStepLe : ∀ j < i, scanStepSpace (sC M r) (D.round sts).jobs s j ≤
        maxCoreSpace (sC M r) slotWords + 3 * s := by
      intro j hj
      have hSCj := le_maxCoreSpace (sC M r) (hSlotEq ▸ hSlotAll j (lt_trans hj hi))
      unfold scanStepSpace; omega
    have hRC : rangeCost (scanStepSpace (sC M r) (D.round sts).jobs s) 0 i ≤
        i * (maxCoreSpace (sC M r) slotWords + 3 * s) :=
      rangeCost_zero_le_mul hStepLe
    have hSC := le_maxCoreSpace (sC M r) (hSlotEq ▸ hSlotAll i hi)
    have hMul : (i + 1) * (maxCoreSpace (sC M r) slotWords + 3 * s) ≤ coreCap :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hiK)
    rw [Nat.succ_mul] at hMul
    change heap + rangeCost (scanStepSpace (sC M r) (D.round sts).jobs s) 0 i +
      sC M r ((D.round sts).jobs.graph i).encode.length + 3 * s < 2 ^ w
    omega
  · intro ans bump hCert hBump
    obtain ⟨hPW, hRR, _⟩ := round_step_bounds (heap := heap) (rBump := 0) hHyp hCert hBump (Nat.zero_le _) hSlotAll
    have hPW' : (pairsWords ((D.round sts).withReplies ans bump).pairs).length ≤ maxPLen := hPW
    have hRR' : ((D.round sts).withReplies ans bump).routeReply (D.atHeap heap) ≤
        heap + coreCap + 5 * (s * k) + 7 * k + 2 := hCoreCapEq ▸ hRR
    have hSR := le_maxRouteSpace sR G.n G.encode.length (Δ + L + max 2 (s * k)) hPW'
    refine ⟨?_, ?_, ?_⟩
    · have hMulSR : (D.base.verts.card + 1) *
          routerSpaceUpTo sR G.n G.encode.length
            (pairsWords ((D.round sts).withReplies ans bump).pairs).length
            (Δ + L + max 2 D.base.verts.card) ≤
          routeCap := by
        rw [hXcard]
        exact Nat.mul_le_mul_left (s * k + 1) hSR
      have hScr : 5 * (s * k) + 7 * k + 2 + routeCap ≤ scratchMid := by
        dsimp [scratchMid]; omega
      change ((D.round sts).withReplies ans bump).routeReply (D.atHeap heap) +
        (D.base.verts.card + 1) *
          routerSpaceUpTo sR G.n G.encode.length
            (pairsWords ((D.round sts).withReplies ans bump).pairs).length
            (Δ + L + max 2 D.base.verts.card) < 2 ^ w
      omega
    · intro rBump hRBump
      have hRec := (round_step_bounds (heap := heap) hHyp hCert hBump hRBump hSlotAll).2.2
      rw [hCoreCapEq, hRouteCapEq] at hRec
      change (((D.round sts).withReplies ans bump).withRouteBump rBump).record (D.atHeap heap) + 2 +
        (D.round sts).jobs.count ≤ heap + roundNonHoleCap s k d + coreCap + routeCap + G.n at hRec
      change (((D.round sts).withReplies ans bump).withRouteBump rBump).record (D.atHeap heap) + 2 +
        (D.round sts).jobs.count < 2 ^ w
      omega
    · exact oneRoundTailCost_le rfl rfl hHyp hC hk hs hCert

/-- `levelChoiceData` meets `ChoiceLoopFit` from its initial post-setup memory. -/
theorem levelChoiceData_loopFit {w K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ} {initial : ℕ → ℕ}
    (hPlayer : IsMatchingPlayer route routeCost) (hC : RouteCostLe routeCost C)
    (hCoreCost : CoreCostBound coreCost)
    (hGE : g + G.encode.length ≤ h)
    (hXE : x + (finsetWords (buildLevelVerts start s k)).length ≤ h)
    (hValid : G.IsValid) (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hPos : 0 < β) (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hEven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hRank : r ≤ ell M) (hDeg : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L')
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w)
    (hArgW : ∀ a ∈ buildLevelArgs g x start s k M r Δ L L' bh h, a < 2 ^ w)
    (hInit : ChoiceGameMemory
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h)
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h).addrs.heap
      (fun _ => ChildState.init) initial) :
    ChoiceLoopFit w (levelTailBudget K C G s k Δ L bh)
      (levelStepBudget K C G s k M r Δ L L' bh)
      (levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h) initial := by
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  have hHyp : ChoiceGameHyp D β bh :=
    levelChoiceData_hyp hPlayer hValid hHost hPos hExp hBh hs hEven hsN hRank hDeg hsL
  have hLay : GameFixedLayout w D.geometry :=
    levelChoiceData_fixedLayout hGE hXE hHost hs hk hSpace
  have hRoom : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
      (D.round sts).jobs.count ≠ 0 →
      ChoiceRoundBudget w (levelTailBudget K C G s k Δ L bh) D heap sts :=
    fun t heap sts mem ht hTr _ =>
      levelChoiceData_roundBudget hPlayer hC hValid hHost hPos hExp hBh hs hk hEven hsN hRank hDeg hsL hSpace ht hTr
  set T := buildLevelDegree L'
  set d := routePathLen Δ bh L
  set slotWords := 2 + T * s
  set heap0Off := T + 4 * k + 1 + k * slotWords
  set coreCap := k * (maxCoreSpace (sC M r) slotWords + 3 * s)
  set routeCap := (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s) (Δ + L + max 2 (s * k))
  set injEndOff := heap0Off + T * (roundNonHoleCap s k d + coreCap + routeCap + G.n)
  have hCoreCapEq : roundCoreCap D = coreCap := rfl
  have hXcard : D.base.verts.card = s * k := by
    change (buildLevelVerts start s k).card = s * k
    rw [buildLevelVerts, Nat.card_Ico, Nat.add_sub_cancel_left]; ring
  have hRouteCapEq : roundRouteCap D = routeCap := by
    unfold roundRouteCap
    dsimp only [routeCap, maxRouteSpace]
    rw [hXcard]; rfl
  have hNonSing : h + injEndOff + d + G.n < 2 ^ w := by
    have h1 : h + (injEndOff + (k + k * (T * s)) + (k + 1 + k * slotWords) +
        (k + 1 + k * (T * s + 1 + T * s * d)) + T +
        (maxCoreSpace (sC M r) slotWords + routeCap +
          6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
        connAllSpace sR G s k Δ L d + NOf M r + d + G.n + 100) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
    omega
  have hHeap0 : D.addrs.heap ≤ h + heap0Off := by
    rw [lcd_heap]
    dsimp [heap0Off, slotWords, T, buildLevelDegree]; omega
  have hDirW : D.directory + D.limit < 2 ^ w := by
    rw [lcd_dir, lcd_limit]
    have hT2 : 49 * L' + 1 ≤ T := by dsimp [T, buildLevelDegree]; omega
    dsimp [injEndOff, heap0Off] at hNonSing; omega
  have hBudget3 : 3 ≤ levelStepBudget K C G s k M r Δ L L' bh := by
    unfold levelStepBudget; dsimp only; omega
  have hMW : M < 2 ^ w := hArgW M (by simp [buildLevelArgs])
  have hRW : r < 2 ^ w := hArgW r (by simp [buildLevelArgs])
  have hGW : g < 2 ^ w := hArgW g (by simp [buildLevelArgs])
  have hXW : x < 2 ^ w := hArgW x (by simp [buildLevelArgs])
  have hStartW : start < 2 ^ w := hArgW start (by simp [buildLevelArgs])
  have hSW : s < 2 ^ w := hArgW s (by simp [buildLevelArgs])
  have hKW : k < 2 ^ w := hArgW k (by simp [buildLevelArgs])
  have hΔW : Δ < 2 ^ w := hArgW Δ (by simp [buildLevelArgs])
  have hLW : L < 2 ^ w := hArgW L (by simp [buildLevelArgs])
  have hH0W : D.addrs.heap < 2 ^ w := by dsimp [injEndOff] at hNonSing; omega
  have hXcardW : D.base.verts.card < 2 ^ w := by
    have hEndLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
    rw [hXcard, Nat.mul_comm s k]; omega
  have hWords : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
      ∀ a ∈ D.args heap sts, a < 2 ^ w := by
    intro t heap sts mem ht hTr a ha
    have hHeapLe := choiceLoopTrace_heap_le hTr hHyp ht.le
    have hHeapW : heap < 2 ^ w := by
      have htLe : t ≤ T := by rw [lcd_limit] at ht; dsimp [T, buildLevelDegree]; omega
      have h1 : t * (roundNonHoleCap s k d + coreCap + routeCap + G.n) ≤
          T * (roundNonHoleCap s k d + coreCap + routeCap + G.n) :=
        Nat.mul_le_mul_right _ htLe
      change heap ≤ D.addrs.heap + t * (roundNonHoleCap s k d + roundCoreCap D + roundRouteCap D + G.n) at hHeapLe
      rw [hCoreCapEq, hRouteCapEq] at hHeapLe
      dsimp [injEndOff] at hNonSing; omega
    have hQLe : coreLevel M r s ≤ r := coreLevel_le hsN
    have hCntLe : (D.round sts).jobs.count ≤ k := D.active_le sts
    have hSavedLe : D.saved ≤ D.addrs.heap := by rw [lcd_saved, lcd_heap]; omega
    have hGraphsLe : D.addrs.graphs ≤ D.addrs.heap := by rw [lcd_graphs, lcd_heap]; omega
    have hOffsLe : D.addrs.offsets ≤ D.addrs.heap := by rw [lcd_offsets, lcd_heap]; omega
    have hRepLe : D.addrs.replies ≤ D.addrs.heap := by rw [lcd_replies, lcd_heap]; omega
    have hDirLe : D.directory ≤ D.addrs.heap := by rw [lcd_dir, lcd_heap]; omega
    have hLimW : D.limit < 2 ^ w := by omega
    simp only [ChoiceLoopData.args, BuildRoundData.stepArgs, BuildRoundData.args,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hHeapW | exact hMW | exact hRW | exact hGW | exact hXW
      | exact hStartW | exact hSW | exact hΔW | exact hLW | exact hLimW | exact hXcardW
      | (change coreLevel M r s < 2 ^ w; omega)
      | (change (D.round sts).jobs.count < 2 ^ w; omega)
      | (change d < 2 ^ w; omega)
      | (change D.addrs.graphs < 2 ^ w; omega)
      | (change D.addrs.offsets < 2 ^ w; omega)
      | (change D.addrs.replies < 2 ^ w; omega)
      | (change D.saved < 2 ^ w; omega)
      | (change D.directory < 2 ^ w; omega)
  refine choiceLoopFit_of_initial hHyp hLay hInit hDirW hBudget3 hWords hRoom ?_
  intro t heap sts mem ht hTr _
  let B := D.round sts
  set coreTerm := (NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)
  have hInv := (hTr.certified.invariant hHyp.router hHyp.host hHyp.positive hHyp.expansion
    hHyp.denominator hHyp.children hHyp.even (coreLevel_le hHyp.coreSize)).1
  have hQ1 : 1 ≤ coreLevel M r s := one_le_coreLevel (by omega)
  have hQr : coreLevel M r s ≤ r := coreLevel_le hsN
  have hQPrev : (NOf M r) ^ (coreLevel M r s - 1) < s := pow_pred_coreLevel_lt (by omega)
  have hQPow : s ≤ (NOf M r) ^ (coreLevel M r s) := le_pow_coreLevel M r s
  have htLe : t ≤ 49 * L' := by rw [lcd_limit] at ht; omega
  have hStepBound : ∀ i < B.jobs.count,
      prepGameStepCost B.jobs K (coreLevel M r s) (coreCost M r) i ≤
        (2 * K + 310) * (s * (coreTerm + T + 1)) := by
    intro i hi
    unfold prepGameStepCost
    dsimp only
    have hAc : D.active sts i < k := (D.active_mem hi).1
    obtain ⟨hGv, hGl, hGLen, hGDeg⟩ := gameGraph_bounds_of_inv (hInv (D.active sts i) hAc)
    have hGLenS : (gameGraph s (sts (D.active sts i))).encode.length ≤ 2 + t * s := hGLen
    have hGn : (B.jobs.graph i).n = s := rfl
    have hCC : coreCost M r (coreLevel M r s) (B.jobs.graph i) ≤ s * coreTerm := by
      have h1 := hCoreCost M r (coreLevel M r s) (B.jobs.graph i) hQ1 hQr hGv hGl
        (hGn.symm ▸ hQPrev) (hGn.symm ▸ hQPow)
        (fun v hv => (hGDeg v hv).trans (htLe.trans hDeg))
      simpa [hGn, coreTerm, Nat.mul_assoc] using h1
    have hELen : (B.jobs.graph i).encode.length ≤ 2 + T * s := by
      have h1 : t * s ≤ T * s := Nat.mul_le_mul_right s (by dsimp [T, buildLevelDegree]; omega)
      change (gameGraph s (sts (D.active sts i))).encode.length ≤ 2 + T * s
      omega
    have hKTerm : K * (coreCost M r (coreLevel M r s) (B.jobs.graph i) +
        (B.jobs.graph i).encode.length + 1) ≤ 2 * K * (s * (coreTerm + T + 1)) := by
      have h1 : coreCost M r (coreLevel M r s) (B.jobs.graph i) +
          (B.jobs.graph i).encode.length + 1 ≤ 2 * (s * (coreTerm + T + 1)) := by
        have hExp : 2 * (s * (coreTerm + T + 1)) = 2 * (s * coreTerm) + 2 * (T * s) + 2 * s := by ring
        omega
      calc K * (coreCost M r (coreLevel M r s) (B.jobs.graph i) + (B.jobs.graph i).encode.length + 1)
          ≤ K * (2 * (s * (coreTerm + T + 1))) := Nat.mul_le_mul_left K h1
        _ = 2 * K * (s * (coreTerm + T + 1)) := by ring
    have hLinTerm : 160 * (B.jobs.graph i).n + 290 ≤ 310 * (s * (coreTerm + T + 1)) := by
      rw [hGn]
      have h1 : 160 * s + 290 ≤ 310 * s := by omega
      have h2 : s ≤ s * (coreTerm + T + 1) := Nat.le_mul_of_pos_right s (by omega)
      omega
    have hSplit : (2 * K + 310) * (s * (coreTerm + T + 1)) =
        2 * K * (s * (coreTerm + T + 1)) + 310 * (s * (coreTerm + T + 1)) := by ring
    omega
  have hRange : rangeCost (prepGameStepCost B.jobs K (coreLevel M r s) (coreCost M r)) 0 B.jobs.count ≤
      (2 * K + 310) * ((s * k) * (coreTerm + T + 1)) := by
    have h1 := rangeCost_zero_le_mul hStepBound
    have hCnt : B.jobs.count ≤ k := D.active_le sts
    have h2 : B.jobs.count * ((2 * K + 310) * (s * (coreTerm + T + 1))) ≤
        k * ((2 * K + 310) * (s * (coreTerm + T + 1))) := Nat.mul_le_mul_right _ hCnt
    have hEq : k * ((2 * K + 310) * (s * (coreTerm + T + 1))) =
        (2 * K + 310) * ((s * k) * (coreTerm + T + 1)) := by ring
    omega
  change rangeCost (prepGameStepCost B.jobs K (coreLevel M r s) (coreCost M r)) 0 B.jobs.count +
    9 * B.jobs.count + 38 + levelTailBudget K C G s k Δ L bh + 128 * B.jobs.count + 226 + 60 ≤
    (2 * K + 700) * ((s * k) * (coreTerm + T + 1)) + levelTailBudget K C G s k Δ L bh + 10
  have hCnt : B.jobs.count ≤ k := D.active_le sts
  have hSK1 : 4 ≤ s * k := by
    calc 4 = 2 * 2 := rfl
      _ ≤ s * k := Nat.mul_le_mul (by omega) hk
  have hKLe : k ≤ s * k := Nat.le_mul_of_pos_left k (by omega)
  have hSKLe : s * k ≤ (s * k) * (coreTerm + T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hRem : 9 * B.jobs.count + 38 + 128 * B.jobs.count + 226 + 60 ≤
      390 * ((s * k) * (coreTerm + T + 1)) := by omega
  have hSplit : (2 * K + 700) * ((s * k) * (coreTerm + T + 1)) =
      (2 * K + 310) * ((s * k) * (coreTerm + T + 1)) + 390 * ((s * k) * (coreTerm + T + 1)) := by ring
  omega


end MinCostFlow.HierPaths
