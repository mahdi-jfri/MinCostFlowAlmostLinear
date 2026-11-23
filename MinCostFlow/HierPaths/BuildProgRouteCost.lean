module

public import MinCostFlow.HierPaths.BuildProgFullRoute
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Paying for the full-routing retries

Under the bump router contract, cut retries bump without zeroing and the final matched reply is
copied down once. The router bound grows with the denominator and pays for both the router and
its wrapper across all attempts, including the single final copy.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

private theorem route_spec_of_pre
    {route : RouterFn} {routeCost : RouterCostFn} (hPlayer : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b : ℕ}
    (hPre : RouterPre G X pairs Δ L) (hb : 2 ≤ b) :
    RouteSpec G X pairs Δ L b 0 (route G X pairs Δ L b 0) := by
  obtain ⟨hX, hLoop, hΔ, hDeg, hL, hXL, hPairs⟩ := hPre
  exact hPlayer.spec G X pairs Δ L b 0 hX hLoop hΔ hDeg hL hXL hb hPairs

private theorem sum_map_le_mul_rc {n B : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j ≤ B) :
    ((List.range n).map f).sum ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Nat.succ_mul]
    have h1 := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    have h2 := h n (Nat.lt_succ_self n)
    omega

private theorem sum_flat_pairs_len (Ms : List (List (ℕ × ℕ))) :
    ((List.range Ms.length).map fun i =>
      ((Ms.getD i []).flatMap fun e => [e.1, e.2]).length).sum = 2 * Ms.flatten.length := by
  have hgen : ∀ n ≤ Ms.length,
      ((List.range n).map fun i =>
        ((Ms.getD i []).flatMap fun e => [e.1, e.2]).length).sum =
        2 * (Ms.take n).flatten.length := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ih (Nat.le_of_succ_le hn), List.take_succ_eq_append_getElem hn, List.flatten_append,
        List.length_append, List.flatten_singleton, List.getD_eq_getElem _ _ hn]
      have hlen : ((Ms[n]'hn).flatMap fun e => [e.1, e.2]).length = 2 * (Ms[n]'hn).length := by
        simp [List.length_flatMap, Nat.mul_comm]
      omega
  simpa using hgen Ms.length le_rfl

/-- Length bound on `routeResultWords res` for any `RouteSpec`-valid outcome. -/
theorem routeResultWords_length_le_of_spec
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {res : RouteResult}
    (hPre : RouterPre G X pairs Δ L)
    (hSpec : RouteSpec G X pairs Δ L b z res) :
    (routeResultWords res).length ≤
      7 + pairs.length + 3 * (pairs.length * X.card) +
        pairs.length * X.card * routePathLen Δ b L + X.card := by
  cases res with
  | cut U =>
    rw [routeCutWords_length]
    have hU : U.card ≤ X.card := Finset.card_le_card hSpec.1
    omega
  | matched Ms emb =>
    obtain ⟨hLen, hMatch, _, _, hWalkLen, _⟩ := hSpec
    have hRowLe : ∀ i < Ms.length, (Ms.getD i []).length ≤ X.card := by
      intro i hi
      have hiP : i < pairs.length := hLen ▸ hi
      obtain ⟨hMem, hNd, _⟩ := hMatch i hiP
      have hSub : ((Ms.getD i []).map Prod.fst).toFinset ⊆ X := by
        intro v hv
        rw [List.mem_toFinset, List.mem_map] at hv
        obtain ⟨e, he, rfl⟩ := hv
        exact (hPre.2.2.2.2.2.2.1 _ (List.getElem_mem hiP)).1 (hMem e he).1
      have hCard : ((Ms.getD i []).map Prod.fst).toFinset.card ≤ X.card :=
        Finset.card_le_card hSub
      rw [List.toFinset_card_of_nodup hNd, List.length_map] at hCard
      exact hCard
    have hFlatLe : Ms.flatten.length ≤ pairs.length * X.card := by
      have hgen : ∀ n ≤ Ms.length, (Ms.take n).flatten.length ≤ n * X.card := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hn
          rw [List.take_succ_eq_append_getElem hn, List.flatten_append, List.length_append,
            List.flatten_singleton, Nat.succ_mul]
          have h1 := ih (Nat.le_of_succ_le hn)
          have h2 : (Ms[n]'hn).length ≤ X.card := by
            have := hRowLe n hn; rwa [List.getD_eq_getElem _ _ hn] at this
          omega
      have h1 := hgen Ms.length le_rfl
      rw [List.take_length, hLen] at h1
      exact h1
    change (layoutList [[0], csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2]),
      csrList Ms.flatten.length emb]).length ≤ _
    rw [length_layoutList]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have h1 : (csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])).length =
        Ms.length + 1 + 2 * Ms.flatten.length := by
      rw [csrList, List.length_append, length_csrOffsets, csrData, List.length_flatMap,
        sum_flat_pairs_len]
    have h2 : (csrList Ms.flatten.length emb).length ≤
        Ms.flatten.length + 1 + Ms.flatten.length * routePathLen Δ b L := by
      rw [csrList, List.length_append, length_csrOffsets, csrData, List.length_flatMap]
      have hsum := sum_map_le_mul_rc (B := routePathLen Δ b L) hWalkLen
      omega
    have hMul : Ms.flatten.length * routePathLen Δ b L ≤
        pairs.length * X.card * routePathLen Δ b L :=
      Nat.mul_le_mul_right _ hFlatLe
    omega

/-- When `pairs = []`, any `RouteSpec`-valid matched result has length `7`. -/
theorem routeResultWords_empty_matched_length
    {G : Graph} {X : Finset ℕ} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hSpec : RouteSpec G X [] Δ L b z (.matched Ms emb)) :
    (routeResultWords (.matched Ms emb)).length = 7 := by
  have hLen : Ms.length = 0 := hSpec.1
  rcases List.length_eq_zero_iff.mp hLen with rfl
  simp [routeResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ]

/-- The RAM cost is at most twice the last router bound. The per-call premise charges
the player, reading its inputs, and the single final copy to that bound. -/
theorem buildFullRouteCost_le
    {route : RouterFn} {routeCost : RouterCostFn} (_hPlayer : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L C : ℕ}
    (hPre : RouterPre G X pairs Δ L) (hPairs : 1 ≤ pairs.length)
    {callCost : ℕ → ℕ}
    (hPay : ∀ b, 2 ≤ b →
      callCost b + 17 * (routeResultWords (route G X pairs Δ L b 0)).length + 70 ≤
        routeBound C G X pairs Δ L b) :
    ∀ n b, 2 ≤ b →
      buildFullRouteCost callCost (fun b' => route G X pairs Δ L b' 0) n b +
        routeBound C G X pairs Δ L b ≤
      2 * routeBound C G X pairs Δ L (fullRoute route G X pairs Δ L n b).2 := by
  intro n
  induction n with
  | zero =>
    intro b hb
    have hCost := hPay b hb
    simp only [buildFullRouteCost, fullRoute]
    omega
  | succ n ih =>
    intro b hb
    have hCost := hPay b hb
    cases hR : route G X pairs Δ L b 0 with
    | matched M emb =>
      simp only [buildFullRouteCost, fullRoute, hR] at hCost ⊢
      omega
    | cut U =>
      have hNext := ih (2 * b) (by omega)
      have hDouble := two_mul_routeBound_le (C := C) (G := G) (X := X) (b := b)
        hPairs hPre.2.2.1 hPre.2.2.2.2.1 (by omega)
      simp only [buildFullRouteCost, fullRoute, hR]
      omega

private theorem pairsWords_length_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (h : ∀ p ∈ pairs, p.1 ⊆ X ∧ p.2 ⊆ X) :
    (pairsWords pairs).length ≤ pairs.length * (2 * X.card + 2) + 1 := by
  induction pairs with
  | nil => simp [pairsWords, length_layoutList]
  | cons p pairs ih =>
    have hTail := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p (by simp)
    have ha := Finset.card_le_card hp.1
    have hb := Finset.card_le_card hp.2
    simp only [pairsWords, length_layoutList, List.flatMap_cons, List.cons_append,
      List.nil_append, List.length_cons, List.map_cons, List.sum_cons, finsetWords,
      Finset.length_sort, Nat.succ_mul] at hTail ⊢
    omega

/-- On a host encoded without edges outside the routing set, the concrete call cost,
wrapper, and final copy fit the router bound after increasing its constant. -/
theorem buildFullRouteCost_compact_le
    {w K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    {args : List ℕ} {mem : ℕ → ℕ}
    (hPlayer : IsMatchingPlayer route routeCost) (hPre : RouterPre G X pairs Δ L)
    (hk : 1 ≤ pairs.length) (hEdges : G.m = (G.inside X).length)
    (hC : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b)
    (n b : ℕ) (hb : 2 ≤ b) :
    (buildFullRouteContract w K route routeCost sR G X pairs Δ L n b).cost args mem ≤
      2 * routeBound (K * (C + 10) + 280) G X pairs Δ L
        (fullRoute route G X pairs Δ L n b).2 := by
  have hp := pairsWords_length_le fun p hp => ⟨(hPre.2.2.2.2.2.2.1 p hp).1,
    (hPre.2.2.2.2.2.2.1 p hp).2.1⟩
  have hG : G.encode.length = 2 + 2 * G.m := by
    simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
  have hX : (finsetWords X).length = X.card := Finset.length_sort _
  let overhead := G.encode.length + (finsetWords X).length * (L + 1) + (pairsWords pairs).length + 1
  let callCost := fun b' => K * (routeCost G X pairs Δ L b' 0 + G.encode.length +
    (finsetWords X).length * (L + 1) + (pairsWords pairs).length + 1)
  have hPay : ∀ b', 2 ≤ b' →
      callCost b' + 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70 ≤
        routeBound (K * (C + 10) + 280) G X pairs Δ L b' := by
    intro b' hb'
    let A := pairs.length * (X.card + G.m + 1)
    let d := routePathLen Δ b' L
    let Q := A * (d + 1) * routeCong Δ b' L + 1
    have hA : X.card + G.m + 1 ≤ A := Nat.le_mul_of_pos_left _ (by omega)
    have hA1 : 1 ≤ A := by omega
    have hPairs : (pairsWords pairs).length ≤ 2 * A + 1 := by
      apply hp.trans
      have he : 2 * X.card + 2 ≤ 2 * (X.card + G.m + 1) := by omega
      calc pairs.length * (2 * X.card + 2) + 1
          ≤ pairs.length * (2 * (X.card + G.m + 1)) + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ he) _
        _ = 2 * A + 1 := by dsimp [A]; ring
    have hCong : 0 < routeCong Δ b' L := by
      have hΔ := hPre.2.2.1
      have hL := hPre.2.2.2.2.1
      unfold routeCong routeBatchH
      positivity
    have hAdQ : A * (d + 1) ≤ Q := by
      have hb := Nat.le_mul_of_pos_right (A * (d + 1)) hCong
      dsimp [Q]; omega
    have hAQ : A ≤ Q := (Nat.le_mul_of_pos_right A (by omega : 0 < d + 1)).trans hAdQ
    have hLd : L ≤ d := by
      have hΔ := hPre.2.2.1
      have h32 : 1 ≤ 32 * Δ * b' := by nlinarith
      simpa [d, routePathLen] using Nat.le_mul_of_pos_left L h32
    have hXLQ : (finsetWords X).length * (L + 1) ≤ Q := by
      rw [hX]
      exact (Nat.mul_le_mul (by omega : X.card ≤ A) (by omega : L + 1 ≤ d + 1)).trans hAdQ
    have hOverQ : overhead ≤ 10 * Q := by
      have hRest : G.encode.length + (pairsWords pairs).length + 1 ≤ 9 * A := by omega
      dsimp [overhead]; omega
    have hSpec := route_spec_of_pre hPlayer hPre hb'
    have hResLen := routeResultWords_length_le_of_spec hPre hSpec
    have hPX : pairs.length * X.card ≤ A := Nat.mul_le_mul_left _ (by omega)
    have hPL : pairs.length ≤ A := Nat.le_mul_of_pos_right _ (by omega)
    have hPXD : pairs.length * X.card * routePathLen Δ b' L ≤ A * (d + 1) :=
      Nat.mul_le_mul hPX (Nat.le_succ d)
    have hLenQ : (routeResultWords (route G X pairs Δ L b' 0)).length ≤ 13 * Q := by
      have hXle : X.card ≤ A := by omega
      omega
    have hExtra : 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70 ≤ 280 * Q := by
      omega
    have hBound (c : ℕ) : routeBound c G X pairs Δ L b' = c * Q := by
      simp only [routeBound, Q, A, d, hEdges]
    have hRoute := hC b' hb'
    rw [hBound] at hRoute ⊢
    calc callCost b' + 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70
        ≤ K * (C * Q + 10 * Q) + 280 * Q := by
          have hr := Nat.mul_le_mul_left K (Nat.add_le_add hRoute hOverQ)
          have hBill : callCost b' = K * (routeCost G X pairs Δ L b' 0 + overhead) := by
            simp only [callCost, overhead, Nat.add_assoc]
          rw [hBill]
          omega
      _ = (K * (C + 10) + 280) * Q := by ring
  have h := buildFullRouteCost_le hPlayer hPre hk hPay n b hb
  exact (Nat.le_add_right ..).trans h

end MinCostFlow.HierPaths
