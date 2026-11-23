module

public import MinCostFlow.HierPaths.BuildProgContracts
public import MinCostFlow.ExpanderDecomp.RouteProgWrap
public import MinCostFlow.ExpanderDecomp.RouteMeets
public import MinCostFlow.HierPaths.BuildProgLevelSpec
import MinCostFlow.ExpanderDecomp.RouteProgEntry
import MinCostFlow.HierPaths.InitBlockLen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Cost, space, and layout lemmas for the static router bridge (`BuildRouterBridgeMath`)

Pure mathematical bounds and memory-layout facts used by `BuildRouterBridge*.lean` to bridge
`routeOrCutPairsWithWalksContract` (`ExpanderDecomp/RouteProgWrap.lean`) to `ProvidesRouter`
(`HierPaths/BuildProgContracts.lean`):
* `routeOrCut_matched_walks_sum_le`: total length + count of all emitted walks in `routeOrCut`
  is bounded by `routeOrCutCost` (each accepted path in `dfsStep` charges `es.length + 2`).
* `routeOrCut_routeCostLe`: `RouteCostLe routeOrCutCost 20`.
* `routerBridgeSpace` and `routerBridgeK`: polynomial space envelope (`10^7 · B^11`) and
  constant time factor (`4000`) covering setup, `routeOrCutPairsProc`, and output packing.
* Layout lemmas connecting `pairsWords`, `EdgesAt`, `csrList`, and `routeResultWords`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Multiplicative time constant in `ProvidesRouter` for `routerBridgeProcs`. -/
def routerBridgeK : ℕ := 4000

/-- Polynomial scratch-space envelope for `routerBridgeProcs` as a function of
`(G.n, G.encode.length, (pairsWords pairs).length, Δ + L + b + z)`. -/
def routerBridgeSpace (n gLen pLen par : ℕ) : ℕ :=
  10000000 * (n + gLen + pLen + par + 2) ^ 11

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-! ## 1. Walk-Length Sum Bounded by `routeOrCutCost` -/

private def pathWeight (ps : List ((ℕ × ℕ) × List ℕ)) : ℕ :=
  (ps.map fun p => p.2.length + 1).sum

private lemma pathWeight_append (ps qs : List ((ℕ × ℕ) × List ℕ)) :
    pathWeight (ps ++ qs) = pathWeight ps + pathWeight qs := by
  simp [pathWeight, List.map_append, List.sum_append]

private lemma pathWeight_zipWith_flatten
    (acc batch : List (List ((ℕ × ℕ) × List ℕ))) :
    pathWeight (List.zipWith (· ++ ·) acc batch).flatten ≤
      pathWeight acc.flatten + pathWeight batch.flatten := by
  induction acc generalizing batch with
  | nil => simp [pathWeight]
  | cons a rest ih =>
    cases batch with
    | nil => simp [pathWeight]
    | cons b brest =>
      simp only [List.zipWith_cons_cons, List.flatten_cons, pathWeight_append]
      have h := ih brest
      omega

private lemma dfsStep_pathWeight_le (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s : ℕ) :
    ∀ fuel u r trail st,
      pathWeight st.paths ≤ st.cost →
      pathWeight (dfsStep V T dist j s fuel u r trail st).paths ≤
        (dfsStep V T dist j s fuel u r trail st).cost := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; exact h
  | succ fuel ih =>
    intro u r trail st hst
    unfold dfsStep
    split_ifs with hu hr
    · simp only [pathWeight, List.map_cons, List.sum_cons, List.length_reverse, List.length_map,
        stackVerts, List.length_cons] at hst ⊢
      omega
    · cases trail with
      | nil => simp only at hst ⊢; omega
      | cons hd rest => exact ih hd.1 (r - 1) rest _ (by dsimp only; omega)
    · cases hcur : st.cursor u with
      | nil =>
        cases trail with
        | nil => simp only at hst ⊢; omega
        | cons hd rest => exact ih hd.1 (r - 1) rest _ (by dsimp only; omega)
      | cons hd rest =>
        dsimp only
        split_ifs
        · exact ih hd.1 (r + 1) ((u, hd.2) :: trail) _ (by dsimp only; omega)
        · exact ih u r trail _ (by dsimp only; omega)

private lemma dfsSources_pathWeight_le (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ) :
    ∀ srcs st,
      pathWeight st.paths ≤ st.cost →
      pathWeight (dfsSources V T dist j fuel srcs st).paths ≤
        (dfsSources V T dist j fuel srcs st).cost := by
  intro srcs
  induction srcs with
  | nil => intro _ h; exact h
  | cons s rest ih =>
    intro st hst
    unfold dfsSources
    split_ifs
    · exact ih _ (by dsimp only; omega)
    · exact ih _ (dfsStep_pathWeight_le V T dist j s fuel s 0 [] _ (by dsimp only; omega))

private lemma dfsBlock_pathWeight_le (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ)
    (dist : ℕ → Option ℕ) (j : ℕ) :
    pathWeight (dfsBlock adj V S T dist j).paths ≤ (dfsBlock adj V S T dist j).cost :=
  dfsSources_pathWeight_le V T dist j _ _ _ (by simp [pathWeight])

private lemma shortPathBlockLoop_pathWeight_le (adj : ℕ → List (ℕ × ℕ)) (S T : Finset ℕ) (d : ℕ) :
    ∀ rem V acc cost,
      pathWeight acc ≤ cost →
      pathWeight (shortPathBlockLoop adj S T d rem V acc cost).paths ≤
        (shortPathBlockLoop adj S T d rem V acc cost).cost := by
  intro rem
  induction rem with
  | zero => intro _ _ _ h; exact h
  | succ rem ih =>
    intro V acc cost hacc
    unfold shortPathBlockLoop
    dsimp only
    split_ifs
    · refine ih _ _ _ ?_
      rw [pathWeight_append]
      have hdfs := dfsBlock_pathWeight_le adj V S T
        (bfsLayers adj V S d T).dist (bfsLayers adj V S d T).maxReached
      omega
    · dsimp only; omega

private lemma batchRoutePairs_pathWeight_le (adj : ℕ → List (ℕ × ℕ)) (d : ℕ) :
    ∀ pairs V,
      pathWeight (batchRoutePairs adj d pairs V).perPairPaths.flatten ≤
        (batchRoutePairs adj d pairs V).cost := by
  intro pairs
  induction pairs with
  | nil => intro _; simp [batchRoutePairs, pathWeight]
  | cons p rest ih =>
    intro V
    unfold batchRoutePairs
    simp only [List.flatten_cons, pathWeight_append]
    have hsp := shortPathBlockLoop_pathWeight_le adj p.1 p.2 d (d + 1) V [] 0 (by simp [pathWeight])
    have htl := ih (shortPathBlock adj V p.1 p.2 d).remVerts
    change pathWeight (shortPathBlock adj V p.1 p.2 d).paths +
      pathWeight (batchRoutePairs adj d rest (shortPathBlock adj V p.1 p.2 d).remVerts).perPairPaths.flatten ≤
      (shortPathBlock adj V p.1 p.2 d).cost +
      (batchRoutePairs adj d rest (shortPathBlock adj V p.1 p.2 d).remVerts).cost + 1
    unfold shortPathBlock at *
    omega

private lemma runBatch_matched_pathWeight_le (G : Graph) (X : Finset ℕ) (Δ b L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (bp : List (List ((ℕ × ℕ) × List ℕ)))
    (remPairs : List (Finset ℕ × Finset ℕ))
    (hout : (runBatch G X Δ b L pairs).outcome = .matched bp remPairs) :
    pathWeight bp.flatten ≤ (runBatch G X Δ b L pairs).cost := by
  unfold runBatch at hout ⊢
  dsimp only at hout ⊢
  split_ifs at hout ⊢ with h
  · cases hout
    have hbr := batchRoutePairs_pathWeight_le (adjOf G X) (routeD Δ b L) pairs X
    dsimp only; omega

private lemma routeBatches_matched_pathWeight_le (G : Graph) (X : Finset ℕ) (Δ b L z : ℕ) :
    ∀ rem curPairs acc cost Ms emb,
      pathWeight acc.flatten ≤ cost →
      (routeBatches G X Δ b L z rem curPairs acc cost).1 = .matched Ms emb →
      ((List.range Ms.flatten.length).map fun j => (emb j).length + 1).sum ≤
        (routeBatches G X Δ b L z rem curPairs acc cost).2 := by
  intro rem
  have hmk : ∀ (acc : List (List ((ℕ × ℕ) × List ℕ))) (Ms : List (List (ℕ × ℕ)))
      (emb : ℕ → List ℕ),
      mkMatchedResult acc = .matched Ms emb →
      ((List.range Ms.flatten.length).map fun j => (emb j).length + 1).sum =
        pathWeight acc.flatten := by
    intro acc Ms emb hEq
    unfold mkMatchedResult at hEq
    cases hEq
    have hflat : (acc.map fun ps => ps.map Prod.fst).flatten = acc.flatten.map Prod.fst := by
      induction acc with
      | nil => simp
      | cons a r ih => simp only [List.map_cons, List.flatten_cons, List.map_append, ih]
    rw [hflat, List.length_map]
    unfold pathWeight
    set xs := acc.flatten
    have hmap : ((List.range xs.length).map fun j => (xs.getD j ((0, 0), [])).2.length + 1) =
        xs.map fun p => p.2.length + 1 := by
      apply List.ext_getElem (by simp)
      intro i hi _
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    rw [hmap]
  induction rem with
  | zero =>
    intro curPairs acc cost Ms emb hacc hEq
    simp only [routeBatches] at hEq ⊢
    rw [hmk acc Ms emb hEq]
    exact hacc
  | succ rem ih =>
    intro curPairs acc cost Ms emb hacc hEq
    simp only [routeBatches] at hEq ⊢
    split_ifs at hEq ⊢ with hdone
    · rw [hmk acc Ms emb hEq]; exact hacc
    · cases hout : (runBatch G X Δ b L curPairs).outcome with
      | cut U => rw [hout] at hEq; simp at hEq
      | matched bp remPairs =>
        rw [hout] at hEq
        dsimp only at hEq ⊢
        refine ih remPairs (List.zipWith (· ++ ·) acc bp)
          (cost + (runBatch G X Δ b L curPairs).cost) Ms emb ?_ hEq
        have h1 := pathWeight_zipWith_flatten acc bp
        have h2 := runBatch_matched_pathWeight_le G X Δ b L curPairs bp remPairs hout
        omega

/-- Total length plus count of all walks emitted by `routeOrCut` is bounded by `routeOrCutCost`. -/
theorem routeOrCut_matched_walks_sum_le {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : routeOrCut G X pairs Δ L b z = .matched Ms emb) :
    ((List.range Ms.flatten.length).map fun j => (emb j).length + 1).sum ≤
      routeOrCutCost G X pairs Δ L b z := by
  unfold routeOrCut routeOrCutRaw at h
  unfold routeOrCutCost routeOrCutRaw
  split_ifs at h ⊢ with hdone
  · cases h
    have hnil : (List.replicate pairs.length ([] : List (ℕ × ℕ))).flatten = [] := by
      induction pairs.length with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih]
    simp [hnil]
  · have hnil : (List.replicate pairs.length ([] : List ((ℕ × ℕ) × List ℕ))).flatten = [] := by
      induction pairs.length with
      | zero => simp
      | succ n ih => simp [List.replicate_succ, ih]
    exact routeBatches_matched_pathWeight_le G X Δ b L z (routeR Δ b L) pairs
      (List.replicate pairs.length []) 0 Ms emb (by simp [pathWeight, hnil]) h

theorem routeOrCut_matched_total_le_cost {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : routeOrCut G X pairs Δ L b z = .matched Ms emb) :
    Ms.flatten.length ≤ routeOrCutCost G X pairs Δ L b z := by
  have hsum := routeOrCut_matched_walks_sum_le h
  have hge : Ms.flatten.length ≤
      ((List.range Ms.flatten.length).map fun j => (emb j).length + 1).sum := by
    generalize Ms.flatten.length = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      omega
  exact hge.trans hsum

theorem routeOrCut_matched_walks_len_le_cost {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : routeOrCut G X pairs Δ L b z = .matched Ms emb) :
    ((List.range Ms.flatten.length).map fun j => (emb j).length).sum ≤
      routeOrCutCost G X pairs Δ L b z := by
  have hsum := routeOrCut_matched_walks_sum_le h
  have hle : ((List.range Ms.flatten.length).map fun j => (emb j).length).sum ≤
      ((List.range Ms.flatten.length).map fun j => (emb j).length + 1).sum := by
    generalize Ms.flatten.length = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      omega
  exact hle.trans hsum

/-! ## 2. Model Cost, Setup Cost, and Polynomial Space Bounds -/

/-- `routeOrCutCost` satisfies `RouteCostLe` with constant `20`. -/
theorem routeOrCut_routeCostLe : RouteCostLe routeOrCutCost 20 := by
  intro G X pairs Δ L b z _ _ hΔ hdeg hL hXL hb hvtp
  have hle := routeOrCutCost_le G pairs (routeTerminalPairs_of_validTerminalPairs hvtp)
    (z := z) hΔ hb hL hdeg hXL
  unfold routeCostConst routeD routeR at hle
  have heq : 20 * pairs.length * (X.card + (G.inside X).length + 1) *
      (routePathLen Δ b L + 1) * routeCong Δ b L =
      20 * (pairs.length * (X.card + (G.inside X).length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L) := by ring
  rw [heq] at hle
  exact hle.trans (Nat.mul_le_mul_left 20 (Nat.le_succ _))

/-- Setup cost of `routeOrCutPairsProc` fits inside the `RouterProcContract` linear-times-`L` budget. -/
theorem routeOrCutPairsTotalCost_le_bridge {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {L rcost : ℕ}
    (hL : 1 ≤ L) (hXL : X.card < 2 ^ L) :
    routeOrCutPairsTotalCost G.m X.card pairs.length rcost ≤
      2500 * rcost + 1700 * (finsetWords X).length * (L + 1) +
        500 * G.encode.length + 200 * (pairsWords pairs).length + 4000 := by
  have hlog := log_two_add_two_le hL hXL
  have hG : G.encode.length = 2 + 2 * G.m := by
    simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
  have hX : (finsetWords X).length = X.card := Finset.length_sort _
  have hP : 2 * pairs.length + 1 ≤ (pairsWords pairs).length := by
    unfold pairsWords
    rw [length_layoutList]
    have hlen : (pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]).length =
        2 * pairs.length := by
      induction pairs with
      | nil => simp
      | cons _ r ih => simp; omega
    omega
  have hmul : X.card * (2 * Nat.log 2 (X.card + 2) + 1) ≤ 2 * (X.card * (L + 1)) := by
    calc X.card * (2 * Nat.log 2 (X.card + 2) + 1)
        ≤ X.card * (2 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (X.card * (L + 1)) := by ring
  have hXL_ge : X.card ≤ X.card * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold routeOrCutPairsTotalCost routeCsrProgCost routeOrCutPairsSetupCost
    buildLocalCsrCost buildLocalPairsCost
  rw [hG, hX, Nat.mul_assoc 1700]
  omega

private lemma routerBridgeSpace_arith {n m nX k gLen pLen par Δ L b z rcost : ℕ}
    (hnX_n : nX ≤ n) (hG : gLen = 2 + 2 * m) (hk_p : 2 * k + 1 ≤ pLen)
    (hpar : par = Δ + L + b + z)
    (hrc_raw : rcost ≤ 20 * k * (nX + m + 1) * (routeD Δ b L + 1) * routeR Δ b L) :
    routeOrCutParamBound m nX k Δ L b z ≤ routerBridgeSpace n gLen pLen par ∧
    (1 + nX) + (1 + 2 * k) + pLen + 5 + (2 + 2 * n) +
      routeOrCutPairsHeapSpace n m nX k rcost + 16 + n + k + (7 + k + 4 * rcost) + 100 ≤
      routerBridgeSpace n gLen pLen par := by
  generalize hB : n + gLen + pLen + par + 2 = B
  have hB1 : 1 ≤ B := by omega
  have hBpow (a : ℕ) (ha : a ≤ 11) : B ^ a ≤ B ^ 11 := Nat.pow_le_pow_right hB1 ha
  have hΔB : Δ ≤ B := by omega
  have hLB : L ≤ B := by omega
  have hbB : b ≤ B := by omega
  have hzB : z ≤ B := by omega
  have hkB : k ≤ B := by omega
  have hnX1B : nX + 1 ≤ B := by omega
  have hXmB : nX + m + 1 ≤ B := by omega
  have hd_le : routeD Δ b L ≤ 32 * B ^ 3 := by
    unfold routeD routePathLen
    have h1 : Δ * b * L ≤ B * B * B := Nat.mul_le_mul (Nat.mul_le_mul hΔB hbB) hLB
    calc 32 * Δ * b * L = 32 * (Δ * b * L) := by ring
      _ ≤ 32 * (B * B * B) := Nat.mul_le_mul_left 32 h1
      _ = 32 * B ^ 3 := by ring
  have hd1_le : routeD Δ b L + 1 ≤ 33 * B ^ 3 := by
    have : 1 ≤ B ^ 3 := Nat.one_le_pow 3 B hB1; omega
  have hd3_le : routeD Δ b L + 3 ≤ 35 * B ^ 3 := by
    have : 1 ≤ B ^ 3 := Nat.one_le_pow 3 B hB1; omega
  have hHb_le : routeHBatch Δ b L ≤ 528 * B ^ 5 := by
    unfold routeHBatch routeBatchH
    have hbΔ : b * Δ ≤ B * B := Nat.mul_le_mul hbB hΔB
    calc 16 * b * Δ * (routeD Δ b L + 1)
        = 16 * (b * Δ) * (routeD Δ b L + 1) := by ring
      _ ≤ 16 * (B * B) * (33 * B ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 16 hbΔ) hd1_le
      _ = 528 * B ^ 5 := by ring
  have hR_le : routeR Δ b L ≤ 528 * B ^ 6 := by
    unfold routeR routeCong
    calc routeHBatch Δ b L * L ≤ (528 * B ^ 5) * B := Nat.mul_le_mul hHb_le hLB
      _ = 528 * B ^ 6 := by ring
  have hrc_le : rcost ≤ 400000 * B ^ 11 := by
    have hprod : k * (nX + m + 1) * (routeD Δ b L + 1) * routeR Δ b L ≤
        B * B * (33 * B ^ 3) * (528 * B ^ 6) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hkB hXmB) hd1_le) hR_le
    calc rcost ≤ 20 * k * (nX + m + 1) * (routeD Δ b L + 1) * routeR Δ b L := hrc_raw
      _ = 20 * (k * (nX + m + 1) * (routeD Δ b L + 1) * routeR Δ b L) := by ring
      _ ≤ 20 * (B * B * (33 * B ^ 3) * (528 * B ^ 6)) := Nat.mul_le_mul_left 20 hprod
      _ = 348480 * B ^ 11 := by ring
      _ ≤ 400000 * B ^ 11 := Nat.mul_le_mul_right _ (by omega)
  have hpar_le : routeOrCutParamBound m nX k Δ L b z ≤ 400000 * B ^ 11 := by
    unfold routeOrCutParamBound
    dsimp only
    have h1 : k * (routeD Δ b L + 3) + 1 ≤ 36 * B ^ 4 := by
      have h1a : k * (routeD Δ b L + 3) ≤ B * (35 * B ^ 3) := Nat.mul_le_mul hkB hd3_le
      have h1b : B * (35 * B ^ 3) = 35 * B ^ 4 := by ring
      have h1c : 1 ≤ B ^ 4 := Nat.one_le_pow 4 B hB1
      omega
    have hRmul : routeR Δ b L * (k * (routeD Δ b L + 3) + 1) ≤ 19008 * B ^ 10 := by
      calc routeR Δ b L * (k * (routeD Δ b L + 3) + 1)
          ≤ (528 * B ^ 6) * (36 * B ^ 4) := Nat.mul_le_mul hR_le h1
        _ = 19008 * B ^ 10 := by ring
    have hHbMul : (nX + 1) * routeHBatch Δ b L ≤ 528 * B ^ 6 := by
      calc (nX + 1) * routeHBatch Δ b L ≤ B * (528 * B ^ 5) := Nat.mul_le_mul hnX1B hHb_le
        _ = 528 * B ^ 6 := by ring
    have h16b : 16 * b * (2 * m + Δ + 1) ≤ 32 * B ^ 2 := by
      have h2m : 2 * m + Δ + 1 ≤ 2 * B := by omega
      calc 16 * b * (2 * m + Δ + 1) ≤ (16 * B) * (2 * B) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 16 hbB) h2m
        _ = 32 * B ^ 2 := by ring
    have h10 := hBpow 10 (by omega)
    have h6 := hBpow 6 (by omega)
    have h3 := hBpow 3 (by omega)
    have h2 := hBpow 2 (by omega)
    have h1p : B ≤ B ^ 11 := by simpa using hBpow 1 (by omega)
    have h0 := Nat.one_le_pow 11 B hB1
    omega
  unfold routerBridgeSpace
  rw [hB]
  refine ⟨by omega, ?_⟩
  unfold routeOrCutPairsHeapSpace localCsrSpace localPairsSpace batchScratchSize
  have h1p : B ≤ B ^ 11 := by simpa using hBpow 1 (by omega)
  have h0 : 1 ≤ B ^ 11 := Nat.one_le_pow 11 B hB1
  have hlin : n + m + nX + k + pLen ≤ 4 * B := by omega
  omega

/-- All bridge scratch, `routeOrCutPairsHeapSpace`, and `routeOrCutParamBound` fit inside
`routerBridgeSpace G.n G.encode.length (pairsWords pairs).length (Δ + L + b + z)`. -/
theorem routerBridgeSpace_bounds {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    (hPre : RouterPre G X pairs Δ L) (hb : 2 ≤ b) :
    routeOrCutParamBound G.m X.card pairs.length Δ L b z ≤
      routerBridgeSpace G.n G.encode.length (pairsWords pairs).length (Δ + L + b + z) ∧
    (1 + X.card) + (1 + 2 * pairs.length) + (pairsWords pairs).length + 5 + (2 + 2 * G.n) +
      routeOrCutPairsHeapSpace G.n G.m X.card pairs.length (routeOrCutCost G X pairs Δ L b z) +
      16 + G.n + pairs.length +
      (7 + pairs.length + 4 * routeOrCutCost G X pairs Δ L b z) + 100 ≤
      routerBridgeSpace G.n G.encode.length (pairsWords pairs).length (Δ + L + b + z) := by
  have hnX_n : X.card ≤ G.n := by simpa using Finset.card_le_card hPre.1
  have hG : G.encode.length = 2 + 2 * G.m := by
    simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
  have hk_p : 2 * pairs.length + 1 ≤ (pairsWords pairs).length := by
    unfold pairsWords; rw [length_layoutList]
    have hlen : (pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]).length =
        2 * pairs.length := by
      induction pairs with
      | nil => simp
      | cons _ r ih => simp; omega
    omega
  have hrc_raw : routeOrCutCost G X pairs Δ L b z ≤
      20 * pairs.length * (X.card + G.m + 1) * (routeD Δ b L + 1) * routeR Δ b L := by
    have hle := routeOrCutCost_le G pairs
      (routeTerminalPairs_of_validTerminalPairs hPre.2.2.2.2.2.2) (z := z)
      hPre.2.2.1 hb hPre.2.2.2.2.1 hPre.2.2.2.1 hPre.2.2.2.2.2.1
    have hin : (G.inside X).length ≤ G.m := List.length_filter_le _ _
    unfold routeCostConst at hle
    exact hle.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (by omega))))
  exact routerBridgeSpace_arith hnX_n hG hk_p rfl hrc_raw

/-! ## 3. Layout Lemmas for `pairsWords`, `EdgesAt`, and `routeResultWords` -/

/-- The `2 * pairs.length` sorted lists packed inside `pairsWords pairs`. -/
def pairsSections (pairs : List (Finset ℕ × Finset ℕ)) : List (List ℕ) :=
  pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]

theorem pairsSections_length (pairs : List (Finset ℕ × Finset ℕ)) :
    (pairsSections pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => simp [pairsSections]
  | cons _ r ih => simp [pairsSections]; omega

theorem pairsSections_getElem_even {pairs : List (Finset ℕ × Finset ℕ)} {i : ℕ}
    (hi : i < pairs.length) :
    (pairsSections pairs)[2 * i]'(by rw [pairsSections_length]; omega) =
      finsetWords (pairs[i]'hi).1 := by
  induction pairs generalizing i with
  | nil => cases hi
  | cons p r ih =>
    cases i with
    | zero => simp [pairsSections]
    | succ i =>
      have hi' : i < r.length := by simpa using hi
      have hidx : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
      have hps : pairsSections (p :: r) = finsetWords p.1 :: finsetWords p.2 :: pairsSections r := rfl
      simp only [hps, hidx, List.getElem_cons_succ]
      exact ih hi'

theorem pairsSections_getElem_odd {pairs : List (Finset ℕ × Finset ℕ)} {i : ℕ}
    (hi : i < pairs.length) :
    (pairsSections pairs)[2 * i + 1]'(by rw [pairsSections_length]; omega) =
      finsetWords (pairs[i]'hi).2 := by
  induction pairs generalizing i with
  | nil => cases hi
  | cons p r ih =>
    cases i with
    | zero => simp [pairsSections]
    | succ i =>
      have hi' : i < r.length := by simpa using hi
      have hidx : 2 * (i + 1) + 1 = ((2 * i + 1) + 1) + 1 := by omega
      have hps : pairsSections (p :: r) = finsetWords p.1 :: finsetWords p.2 :: pairsSections r := rfl
      simp only [hps, hidx, List.getElem_cons_succ]
      exact ih hi'

/-- Prefix sum of section lengths in `pairsSections pairs`. -/
def pairsSecOff (pairs : List (Finset ℕ × Finset ℕ)) (j : ℕ) : ℕ :=
  (((pairsSections pairs).take j).map List.length).sum

theorem pairsSecOff_zero (pairs : List (Finset ℕ × Finset ℕ)) :
    pairsSecOff pairs 0 = 0 := by simp [pairsSecOff]

theorem pairsSecOff_succ {pairs : List (Finset ℕ × Finset ℕ)} {j : ℕ}
    (hj : j < 2 * pairs.length) :
    pairsSecOff pairs (j + 1) =
      pairsSecOff pairs j + ((pairsSections pairs)[j]'(by rw [pairsSections_length]; exact hj)).length := by
  unfold pairsSecOff
  have hj' : j < (pairsSections pairs).length := by rw [pairsSections_length]; exact hj
  rw [List.take_succ_eq_append_getElem hj', List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

theorem pairsSecOff_le_total (pairs : List (Finset ℕ × Finset ℕ)) (j : ℕ) :
    pairsSecOff pairs j ≤ ((pairsSections pairs).map List.length).sum := by
  unfold pairsSecOff
  have h := List.take_append_drop j (pairsSections pairs)
  conv_rhs => rw [← h, List.map_append, List.sum_append]
  omega

theorem pairsWords_length_eq (pairs : List (Finset ℕ × Finset ℕ)) :
    (pairsWords pairs).length = 2 * pairs.length + 1 + ((pairsSections pairs).map List.length).sum := by
  unfold pairsWords pairsSections
  rw [length_layoutList, ← pairsSections, pairsSections_length]

theorem pairsWords_offset_eq {mem : ℕ → ℕ} {pAddr : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hP : ListAt mem pAddr (pairsWords pairs)) {j : ℕ} (hj : j ≤ 2 * pairs.length) :
    mem (pAddr + j) = pairsSecOff pairs j := by
  have hAt : ListAt mem pAddr (layoutList (pairsSections pairs)) := hP
  have hj' : j ≤ (pairsSections pairs).length := by rw [pairsSections_length]; exact hj
  have hOff := csrList_offset hAt hj'
  rw [hOff]
  unfold pairsSecOff
  have hgen : ∀ n ≤ (pairsSections pairs).length,
      ((List.range n).map fun i => ((pairsSections pairs).getD i []).length).sum =
      (((pairsSections pairs).take n).map List.length).sum := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ih (Nat.le_of_succ_le hn), List.take_succ_eq_append_getElem hn, List.map_append,
        List.sum_append, List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ hn]
  exact hgen j hj'

theorem pairsWords_section_listAt {mem : ℕ → ℕ} {pAddr : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hP : ListAt mem pAddr (pairsWords pairs)) {j : ℕ} (hj : j < 2 * pairs.length) :
    ListAt mem (pAddr + 2 * pairs.length + 1 + pairsSecOff pairs j)
      ((pairsSections pairs)[j]'(by rw [pairsSections_length]; exact hj)) := by
  have hAt : ListAt mem pAddr (layoutList (pairsSections pairs)) := hP
  have hj' : j < (pairsSections pairs).length := by rw [pairsSections_length]; exact hj
  have hData : ListAt mem (pAddr + (pairsSections pairs).length + 1)
      (csrData (pairsSections pairs).length (fun i => (pairsSections pairs).getD i [])) := by
    unfold layoutList csrList at hAt
    have h2 := (listAt_append.mp hAt).2
    rw [length_csrOffsets] at h2
    simpa only [Nat.add_assoc] using h2
  have hflat : csrData (pairsSections pairs).length (fun i => (pairsSections pairs).getD i []) =
      (pairsSections pairs).flatten := by
    unfold csrData
    have hgen : ∀ n ≤ (pairsSections pairs).length,
        ((List.range n).flatMap fun i => (pairsSections pairs).getD i []) =
        ((pairsSections pairs).take n).flatten := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih (Nat.le_of_succ_le hn),
          List.take_succ_eq_append_getElem hn, List.flatten_append, List.flatten_singleton,
          List.getD_eq_getElem _ _ hn]
    simpa using hgen (pairsSections pairs).length le_rfl
  rw [hflat, pairsSections_length] at hData
  have hsplit : pairsSections pairs =
      (pairsSections pairs).take j ++ [(pairsSections pairs)[j]'hj'] ++
        (pairsSections pairs).drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj', List.take_append_drop]
  rw [hsplit, List.flatten_append, List.flatten_append, List.flatten_singleton] at hData
  have hlen : ((pairsSections pairs).take j).flatten.length = pairsSecOff pairs j := by
    rw [List.length_flatten]; rfl
  have h1 := (listAt_append.mp hData).1
  have h2 := (listAt_append.mp h1).2
  rwa [hlen] at h2

/-- `EdgesAt` is equivalent to `ListAt` of the flattened `[u, v]` edge pairs. -/
theorem edgesAt_iff_listAt_flatMap {mem : ℕ → ℕ} {addr : ℕ} {es : List (ℕ × ℕ)} :
    EdgesAt mem addr es ↔ ListAt mem addr (es.flatMap fun e => [e.1, e.2]) := by
  induction es generalizing addr with
  | nil => simp [EdgesAt, ListAt]
  | cons e rest ih =>
    constructor
    · intro h
      have h0 := h 0 (Nat.zero_lt_succ _)
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at h0
      have hrest : EdgesAt mem (addr + 2) rest := fun j hj => by
        have h' := h (j + 1) (Nat.succ_lt_succ hj)
        simp only [List.getElem_cons_succ] at h'
        have ha1 : addr + 2 * (j + 1) = addr + 2 + 2 * j := by omega
        rw [ha1] at h'; exact h'
      have hl := ih.mp hrest
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      exact listAt_cons.mpr ⟨h0.1, listAt_cons.mpr ⟨h0.2, by simpa [Nat.add_assoc] using hl⟩⟩
    · intro h
      simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
      obtain ⟨h0, h1⟩ := listAt_cons.mp h
      obtain ⟨h1', hrest⟩ := listAt_cons.mp h1
      have hrest' : EdgesAt mem (addr + 2) rest := ih.mpr (by simpa [Nat.add_assoc] using hrest)
      intro j hj
      cases j with
      | zero => simpa using And.intro h0 h1'
      | succ j =>
        have h' := hrest' j (Nat.lt_of_succ_lt_succ hj)
        have ha1 : addr + 2 * (j + 1) = addr + 2 + 2 * j := by omega
        rw [ha1]; exact h'

/-- `csrData` of the per-pair matchings equals the flat edge words of `Ms.flatten`. -/
theorem csrData_matchings_eq_flatten (Ms : List (List (ℕ × ℕ))) :
    csrData Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]) =
      Ms.flatten.flatMap fun e => [e.1, e.2] := by
  unfold csrData
  have hgen : ∀ n ≤ Ms.length,
      ((List.range n).flatMap fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]) =
      (Ms.take n).flatten.flatMap fun e => [e.1, e.2] := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih (Nat.le_of_succ_le hn),
        List.take_succ_eq_append_getElem hn, List.flatten_append, List.flatten_singleton,
        List.flatMap_append, List.getD_eq_getElem _ _ hn]
  simpa using hgen Ms.length le_rfl

/-- `csrOffsets` of the per-pair matchings equals `2 *` the prefix sums of row lengths. -/
theorem csrOffsets_matchings_getElem (Ms : List (List (ℕ × ℕ))) {i : ℕ} (hi : i ≤ Ms.length) :
    (csrOffsets Ms.length (fun j => (Ms.getD j []).flatMap fun e => [e.1, e.2]))[i]'(by
        rw [length_csrOffsets]; omega) =
      2 * ((Ms.take i).map List.length).sum := by
  simp only [csrOffsets, List.getElem_map, List.getElem_range]
  have hgen : ∀ n ≤ Ms.length,
      ((List.range n).map fun j => ((Ms.getD j []).flatMap fun e => [e.1, e.2]).length).sum =
      2 * ((Ms.take n).map List.length).sum := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ih (Nat.le_of_succ_le hn), List.take_succ_eq_append_getElem hn, List.map_append,
        List.sum_append, List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ hn]
      have hlen : ((Ms[n]'hn).flatMap fun e => [e.1, e.2]).length = 2 * (Ms[n]'hn).length := by
        simp [List.length_flatMap, Nat.mul_comm]
      omega
  exact hgen i hi

/-- Length of `routeResultWords (.matched Ms emb)` in terms of `Ms.length` and `routeOrCutCost`. -/
theorem routeResultWords_matched_len_le {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : routeOrCut G X pairs Δ L b z = .matched Ms emb) :
    (routeResultWords (.matched Ms emb)).length ≤
      7 + Ms.length + 4 * routeOrCutCost G X pairs Δ L b z := by
  have htot := routeOrCut_matched_total_le_cost h
  have hlen := routeOrCut_matched_walks_len_le_cost h
  unfold routeResultWords
  rw [length_layoutList]
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  have h1 : (csrList Ms.length fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]).length =
      Ms.length + 1 + 2 * Ms.flatten.length := by
    rw [csrList, List.length_append, length_csrOffsets, csrData_matchings_eq_flatten]
    have hflat : (Ms.flatten.flatMap fun e => [e.1, e.2]).length = 2 * Ms.flatten.length := by
      generalize Ms.flatten = es
      induction es with
      | nil => simp
      | cons _ _ ih => simp [ih]; omega
    omega
  have h2 : (csrList Ms.flatten.length emb).length =
      Ms.flatten.length + 1 + ((List.range Ms.flatten.length).map fun j => (emb j).length).sum := by
    rw [csrList, List.length_append, length_csrOffsets, csrData, List.length_flatMap]
  omega

/-- Explicit expansion of `routeResultWords (.cut U)`. -/
theorem routeResultWords_cut_eq (U : Finset ℕ) :
    routeResultWords (.cut U) = [0, 1, 1 + U.card, 1 + U.card, 1] ++ finsetWords U := by
  unfold routeResultWords layoutList csrList csrOffsets csrData finsetWords
  simp [List.range_succ, Finset.length_sort]

/-- Explicit expansion of `routeResultWords (.matched Ms emb)`. -/
theorem routeResultWords_matched_eq (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) :
    let sec1 := csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])
    let sec2 := csrList Ms.flatten.length emb
    routeResultWords (.matched Ms emb) =
      [0, 1, 1 + sec1.length, 1 + sec1.length + sec2.length, 0] ++ sec1 ++ sec2 := by
  intro sec1 sec2
  unfold routeResultWords layoutList csrList csrOffsets csrData
  simp [sec1, sec2, csrList, csrOffsets, csrData, List.range_succ, List.append_assoc, Nat.add_assoc]

end MinCostFlow.HierPaths
