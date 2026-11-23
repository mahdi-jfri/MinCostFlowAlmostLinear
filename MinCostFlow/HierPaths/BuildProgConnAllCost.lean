module

public import MinCostFlow.HierPaths.BuildProgConnOne
public import MinCostFlow.HierPaths.BuildProgConnSize
public import MinCostFlow.HierPaths.BuildProgLevelModel
import MinCostFlow.HierPaths.BuildProgRouteCost
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Cost, space, and length bounds for sibling connector packing

Separates the model definitions (`levelConnRow`, `connPairSpace`, `connAllSpace`, `routeBoundG`,
`connAllCostBound`) and arithmetic/cost proofs from the 2-pass Word-RAM procedure in
`BuildProgConnAll.lean`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The `i`-th row of the connector CSR section (`c = i / k`, `c' = i % k`). -/
def levelConnRow (route : RouterFn) (G : Graph) (start s k Δ L i : ℕ) : List ℕ :=
  let D := levelDataOfFamily route G start s k Δ L (fun _ => [])
  let pair := D.conn (i / k) (i % k)
  csrList pair.length (fun j => connWords (pair.getD j (0, 0, [])))

/-- Bump space used by one sibling pair routing + erasure + gather call above its heap base. -/
def connPairSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (s k Δ L d : ℕ) : ℕ :=
  3 + 2 * s + (s * k + 1) * routerSpaceUpTo sR G.n G.encode.length (3 + 2 * s)
    (Δ + L + max 2 (s * k)) +
    22 + 10 * s + 3 * (s * d) + d + G.n

/-- Total bump space above `dst` used by `buildConnAllProc` across all `k * k` pairs and the
contiguous CSR section `sec2`. -/
def connAllSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (s k Δ L d : ℕ) : ℕ :=
  2 * (k * k) + (k * k) * connPairSpace sR G s k Δ L d +
    (k * k + 1 + k * k * (8 + 3 * s + s * d)) + 10

/-- `routeBound` using total edge count `G.m` instead of `(G.inside X).length`. -/
def routeBoundG (C : ℕ) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b : ℕ) : ℕ :=
  C * (pairs.length * (X.card + G.m + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L + 1)

/-- Upper bound on the cost of writing the entire connector CSR section. -/
def connAllCostBound (K C : ℕ) (G : Graph) (s k Δ L bh : ℕ) : ℕ :=
  let X := s * k
  let d := routePathLen Δ bh L
  let R := routeCong Δ bh L
  (2 * (K * (C + 10) + 280) + 3000) * (k * k) * (X + G.m + 1) * (d + 1) * (R + 1) +
    250 * (k * k) + 200

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

theorem routeBound_le_routeBoundG (C : ℕ) (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b : ℕ) :
    routeBound C G X pairs Δ L b ≤ routeBoundG C G X pairs Δ L b := by
  unfold routeBound routeBoundG
  have hin : (G.inside X).length ≤ G.m := List.length_filter_le _ _
  gcongr

theorem routeBoundG_mono_b {C : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b₁ b₂ : ℕ} (hb : b₁ ≤ b₂) :
    routeBoundG C G X pairs Δ L b₁ ≤ routeBoundG C G X pairs Δ L b₂ := by
  unfold routeBoundG routeCong routeBatchH routePathLen
  gcongr

private theorem two_mul_routeBoundG_le {C : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b : ℕ}
    (hk : 1 ≤ pairs.length) (hΔ : 1 ≤ Δ) (hL : 1 ≤ L) (hb : 1 ≤ b) :
    2 * routeBoundG C G X pairs Δ L b ≤ routeBoundG C G X pairs Δ L (2 * b) := by
  unfold routeBoundG
  have hd : routePathLen Δ (2 * b) L = 2 * routePathLen Δ b L := by
    unfold routePathLen; ring
  have hd1 : 1 ≤ routePathLen Δ b L := by unfold routePathLen; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hR1 : 1 ≤ routeCong Δ b L := by unfold routeCong routeBatchH; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hR2 : 2 * routeCong Δ b L ≤ routeCong Δ (2 * b) L := by
    unfold routeCong routeBatchH
    calc 2 * (16 * b * Δ * (routePathLen Δ b L + 1) * L)
        = 16 * (2 * b) * Δ * (routePathLen Δ b L + 1) * L := by ring
      _ ≤ 16 * (2 * b) * Δ * (routePathLen Δ (2 * b) L + 1) * L := by
          have : routePathLen Δ b L + 1 ≤ routePathLen Δ (2 * b) L + 1 := by omega
          gcongr
  have hA1 : 1 ≤ pairs.length * (X.card + G.m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmul : 2 * ((routePathLen Δ b L + 1) * routeCong Δ b L) + 1 ≤
      (routePathLen Δ (2 * b) L + 1) * routeCong Δ (2 * b) L := by
    have h1 : 2 * (routePathLen Δ b L + 1) + 1 ≤ 2 * (routePathLen Δ (2 * b) L + 1) := by omega
    have h2 : (2 * (routePathLen Δ b L + 1) + 1) * routeCong Δ b L ≤
        (routePathLen Δ (2 * b) L + 1) * routeCong Δ (2 * b) L := by
      calc (2 * (routePathLen Δ b L + 1) + 1) * routeCong Δ b L
          ≤ (2 * (routePathLen Δ (2 * b) L + 1)) * routeCong Δ b L := Nat.mul_le_mul_right _ h1
        _ = (routePathLen Δ (2 * b) L + 1) * (2 * routeCong Δ b L) := by ring
        _ ≤ (routePathLen Δ (2 * b) L + 1) * routeCong Δ (2 * b) L := Nat.mul_le_mul_left _ hR2
    nlinarith
  have hbig : 2 * (pairs.length * (X.card + G.m + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L + 1) ≤
      pairs.length * (X.card + G.m + 1) * (routePathLen Δ (2 * b) L + 1) * routeCong Δ (2 * b) L + 1 := by
    have hstep := Nat.mul_le_mul_left (pairs.length * (X.card + G.m + 1)) hmul
    nlinarith
  calc 2 * (C * (pairs.length * (X.card + G.m + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
      = C * (2 * (pairs.length * (X.card + G.m + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L + 1)) := by ring
    _ ≤ C * (pairs.length * (X.card + G.m + 1) * (routePathLen Δ (2 * b) L + 1) * routeCong Δ (2 * b) L + 1) :=
        Nat.mul_le_mul_left C hbig

private theorem pairsWords_len_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
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

/-- Full-routing cost bound using `G.m` (without requiring `G.m = (G.inside X).length`). -/
theorem buildFullRouteCost_graph_le
    {w K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    {args : List ℕ} {mem : ℕ → ℕ}
    (hPlayer : IsMatchingPlayer route routeCost) (hPre : RouterPre G X pairs Δ L)
    (hk : 1 ≤ pairs.length)
    (hC : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b)
    (n b : ℕ) (hb : 2 ≤ b) :
    (buildFullRouteContract w K route routeCost sR G X pairs Δ L n b).cost args mem ≤
      2 * routeBoundG (K * (C + 10) + 280) G X pairs Δ L
        (fullRoute route G X pairs Δ L n b).2 := by
  have hp := pairsWords_len_le fun p hp => ⟨(hPre.2.2.2.2.2.2.1 p hp).1,
    (hPre.2.2.2.2.2.2.1 p hp).2.1⟩
  have hG : G.encode.length = 2 + 2 * G.m := by
    simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
  have hX : (finsetWords X).length = X.card := Finset.length_sort _
  let overhead := G.encode.length + (finsetWords X).length * (L + 1) + (pairsWords pairs).length + 1
  let callCost := fun b' => K * (routeCost G X pairs Δ L b' 0 + G.encode.length +
    (finsetWords X).length * (L + 1) + (pairsWords pairs).length + 1)
  have hPay : ∀ b', 2 ≤ b' →
      callCost b' + 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70 ≤
        routeBoundG (K * (C + 10) + 280) G X pairs Δ L b' := by
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
      unfold routeCong routeBatchH; positivity
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
    have hSpec := hPlayer.spec G X pairs Δ L b' 0 hPre.1 hPre.2.1 hPre.2.2.1 hPre.2.2.2.1
      hPre.2.2.2.2.1 hPre.2.2.2.2.2.1 hb' hPre.2.2.2.2.2.2
    have hResLen := routeResultWords_length_le_of_spec hPre hSpec
    have hPX : pairs.length * X.card ≤ A := Nat.mul_le_mul_left _ (by omega)
    have hPL : pairs.length ≤ A := Nat.le_mul_of_pos_right _ (by omega)
    have hPXD : pairs.length * X.card * d ≤ A * (d + 1) := Nat.mul_le_mul hPX (Nat.le_succ d)
    have hLenQ : (routeResultWords (route G X pairs Δ L b' 0)).length ≤ 12 * Q := by
      have hQ1 : 1 ≤ Q := by dsimp [Q]; omega
      have hQ2 : 2 ≤ Q := by
        have h1 : 1 ≤ A * (d + 1) := Nat.mul_pos hA1 (by omega)
        have h2 : 1 ≤ A * (d + 1) * routeCong Δ b' L := Nat.mul_pos h1 hCong
        dsimp [Q]; omega
      change (routeResultWords (route G X pairs Δ L b' 0)).length ≤
        7 + pairs.length + 3 * (pairs.length * X.card) + pairs.length * X.card * d + X.card at hResLen
      omega
    have hExtra : 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70 ≤ 280 * Q := by
      have hQ2 : 2 ≤ Q := by
        have h1 : 1 ≤ A * (d + 1) := Nat.mul_pos hA1 (by omega)
        have h2 : 1 ≤ A * (d + 1) * routeCong Δ b' L := Nat.mul_pos h1 hCong
        dsimp [Q]; omega
      omega
    have hRoute : routeCost G X pairs Δ L b' 0 ≤ C * Q :=
      (hC b' hb').trans (routeBound_le_routeBoundG C G X pairs Δ L b')
    change _ ≤ (K * (C + 10) + 280) * Q
    calc callCost b' + 17 * (routeResultWords (route G X pairs Δ L b' 0)).length + 70
        ≤ K * (C * Q + 10 * Q) + 280 * Q := by
          have hr := Nat.mul_le_mul_left K (Nat.add_le_add hRoute hOverQ)
          have hBill : callCost b' = K * (routeCost G X pairs Δ L b' 0 + overhead) := by
            simp only [callCost, overhead, Nat.add_assoc]
          rw [hBill]; omega
      _ = (K * (C + 10) + 280) * Q := by ring
  have hRec : ∀ m b', 2 ≤ b' →
      buildFullRouteCost callCost (fun b'' => route G X pairs Δ L b'' 0) m b' +
        routeBoundG (K * (C + 10) + 280) G X pairs Δ L b' ≤
      2 * routeBoundG (K * (C + 10) + 280) G X pairs Δ L (fullRoute route G X pairs Δ L m b').2 := by
    intro m
    induction m with
    | zero =>
      intro b' hb'
      have hCost := hPay b' hb'
      simp only [buildFullRouteCost, fullRoute]; omega
    | succ m ih =>
      intro b' hb'
      have hCost := hPay b' hb'
      cases hR : route G X pairs Δ L b' 0 with
      | matched M emb =>
        simp only [buildFullRouteCost, fullRoute, hR] at hCost ⊢; omega
      | cut U =>
        have hNext := ih (2 * b') (by omega)
        have hDouble := two_mul_routeBoundG_le (C := K * (C + 10) + 280) (G := G) (X := X)
          (b := b') hk hPre.2.2.1 hPre.2.2.2.2.1 (by omega)
        simp only [buildFullRouteCost, fullRoute, hR]; omega
  exact (Nat.le_add_right ..).trans (hRec n b hb)

/-- For `c' ≤ c`, the connector row is the empty CSR block `[0]`. -/
theorem levelConnRow_of_ge {route : RouterFn} {G : Graph} {start s k Δ L i : ℕ}
    (hle : i % k ≤ i / k) : levelConnRow route G start s k Δ L i = [0] := by
  have hnot : ¬ i / k < i % k := by omega
  simp [levelConnRow, levelDataOfFamily, hnot, csrList, csrOffsets, csrData]

private theorem csrList_congr {n : ℕ} {f g : ℕ → List ℕ} (h : ∀ j < n, f j = g j) :
    csrList n f = csrList n g := by
  have hlen : ∀ j < n, (f j).length = (g j).length := fun j hj => congrArg List.length (h j hj)
  unfold csrList csrOffsets csrData
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hik : i ≤ n := by simp at hi; omega
    congr 1
    apply List.map_congr_left
    intro j hj
    exact hlen j (by simp at hj; omega)
  · apply List.flatMap_congr
    intro j hj
    exact h j (by simp at hj; omega)

/-- Exact equality of the connector row for `c < c'` using `csrList_congr`. -/
theorem levelConnRow_eq_connectorRows {route : RouterFn} {G : Graph} {start s k Δ L i : ℕ}
    {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ}
    (hlt : i / k < i % k)
    (hRes : (lemma1Route route G (buildLevelVerts start s k)
      (connRequestPairs (start + (i / k) * s) (start + (i % k) * s) s) Δ L).1 = .matched [M] emb) :
    levelConnRow route G start s k Δ L i = csrList M.length (connectorRows G M emb) := by
  have hSib : siblingConns route G (buildLevelVerts start s k) Δ L (buildLevelChild start s)
      (i / k) (i % k) =
      (List.range M.length).map fun j => (edgeAt M j, erase G.edges (edgeAt M j).1 (emb j)) := by
    unfold siblingConns buildLevelChild
    change connOf G.edges (lemma1Route route G (buildLevelVerts start s k)
      (connRequestPairs (start + (i / k) * s) (start + (i % k) * s) s) Δ L).1 = _
    rw [hRes]
    simp [connOf]
  unfold levelConnRow levelDataOfFamily
  simp only [hlt, ↓reduceIte, hSib, List.map_map, List.length_map, List.length_range]
  apply csrList_congr
  intro j hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [connWords, connectorRows, buildConnectorRowWords]

theorem sum_map_le_mul_conn {n B : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j ≤ B) :
    ((List.range n).map f).sum ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have h1 := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    have h2 := h n (Nat.lt_succ_self n)
    rw [Nat.succ_mul]
    omega

theorem rangeCost_le_mul_conn {n B : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j ≤ B) :
    rangeCost f 0 n ≤ n * B := by
  unfold rangeCost
  rw [Nat.sub_zero, ← List.range_eq_range']
  exact sum_map_le_mul_conn h

/-- Length bound on the entire connector CSR section `sec2`. -/
theorem levelConnSec_length_le {route : RouterFn} {routeCost : RouterCostFn}
    {G : Graph} {start s k Δ L bh : ℕ} {β : ℝ}
    (hPlayer : IsMatchingPlayer route routeCost) (hPos : 0 < β)
    (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hHost : HostPre G (buildLevelVerts start s k) Δ L) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ)) :
    (csrList (k * k) (levelConnRow route G start s k Δ L)).length ≤
      k * k + 1 + k * k * (8 + 3 * s + s * routePathLen Δ bh L) := by
  rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
  refine Nat.add_le_add_left (sum_map_le_mul_conn fun i hi => ?_) _
  have hc : i / k < k := Nat.div_lt_of_lt_mul hi
  have hc' : i % k < k := Nat.mod_lt i (by omega)
  by_cases hlt : i / k < i % k
  · have hch := buildLevel_isChildren (start := start) (k := k) hs
    have hPre := routerPre_pair hHost hch hc hc' (by omega)
    obtain ⟨_, hex⟩ := exists_lemma_1 hPlayer
    obtain ⟨⟨Ms, emb, hRes, hMatch, hFull⟩, _, hLast, _, _⟩ :=
      hex G (buildLevelVerts start s k) [(buildLevelChild start s (i / k),
        buildLevelChild start s (i % k))] Δ L hPre (by simp) β hPos hExp
    have hLen1 : Ms.length = 1 := by simpa using hMatch.1
    rcases List.length_eq_one_iff.mp hLen1 with ⟨M, rfl⟩
    have hMlen : M.length = s := by
      have hf := hFull 0 (by simp)
      simpa [buildLevelChild, card_shiftSet] using hf
    have hLastNat : (lemma1Route route G (buildLevelVerts start s k)
        [(buildLevelChild start s (i / k), buildLevelChild start s (i % k))] Δ L).2 ≤ bh := by
      exact_mod_cast hLast.trans hBh
    have hWalk : ∀ j < M.length, IsEdgeWalk G.edges (edgeAt M j).1 (edgeAt M j).2 (emb j) := by
      intro j hj
      have hj' : j < ([M] : List (List (ℕ × ℕ))).flatten.length := by simpa using hj
      have hmem : edgeAt M j ∈ M := by
        unfold edgeAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      have hends := (hMatch.2.1 0 (by simp)).1 (edgeAt M j) (by simpa using hmem)
      have hins : insideB (buildLevelVerts start s k) (edgeAt ([M] : List (List (ℕ × ℕ))).flatten j) = true := by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, insideB,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨(hch.2.1 _ hc).1 hends.1, (hch.2.1 _ hc').1 hends.2⟩
      simpa [Graph.m, edgeAt] using (hMatch.2.2.2.1 j hj' hins).1
    have hEmbLen : ∀ j < M.length, (emb j).length ≤ routePathLen Δ bh L := by
      intro j hj
      have hj' : j < ([M] : List (List (ℕ × ℕ))).flatten.length := by simpa using hj
      have h1 := hMatch.2.2.2.2.1 j hj'
      have h2 : routePathLen Δ (lemma1Route route G (buildLevelVerts start s k)
          [(buildLevelChild start s (i / k), buildLevelChild start s (i % k))] Δ L).2 L ≤
          routePathLen Δ bh L := by
        unfold routePathLen; gcongr
      exact h1.trans h2
    have hEq := levelConnRow_eq_connectorRows hlt hRes
    rw [hEq]
    have hsz : (csrList M.length (connectorRows G M emb)).length ≤
        8 + 3 * M.length + ((List.range M.length).map fun j => (emb j).length).sum :=
      (connectorRows_length_le hWalk).trans (by rw [connectorReplyLength])
    have hraw : ((List.range M.length).map fun j => (emb j).length).sum ≤ M.length * routePathLen Δ bh L :=
      sum_map_le_mul_conn hEmbLen
    rw [hMlen] at hsz hraw ⊢
    omega
  · rw [levelConnRow_of_ge (by omega)]
    simp; omega

/-- Cost bound for one `buildConnOneContract` call on a sibling pair. -/
theorem pair_one_cost_le {w K C : ℕ} {route : RouterFn} {routeCost : RouterCostFn}
    {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {G : Graph} {start s k Δ L bh a b : ℕ}
    {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {args : List ℕ} {mem : ℕ → ℕ}
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : ∀ pairs b', RouterPre G (buildLevelVerts start s k) pairs Δ L → 2 ≤ b' →
      routeCost G (buildLevelVerts start s k) pairs Δ L b' 0 ≤
        routeBound C G (buildLevelVerts start s k) pairs Δ L b')
    (hPre : RouterPre G (buildLevelVerts start s k) (connRequestPairs a b s) Δ L)
    (_hRes : (lemma1Route route G (buildLevelVerts start s k) (connRequestPairs a b s) Δ L).1 =
      .matched [M] emb)
    (hLast : (lemma1Route route G (buildLevelVerts start s k) (connRequestPairs a b s) Δ L).2 ≤ bh)
    (hMlen : M.length = s)
    (hWalk : ∀ j < M.length, IsEdgeWalk G.edges (edgeAt M j).1 (edgeAt M j).2 (emb j))
    (hEmbLen : ∀ j < M.length, (emb j).length ≤ routePathLen Δ bh L)
    (hs : 1 ≤ s) (hk : 1 ≤ k) :
    (buildConnOneContract w K route routeCost sR G (buildLevelVerts start s k) a b Δ L
      (routePathLen Δ bh L) M emb).cost args mem ≤
      (2 * (K * (C + 10) + 280) + 1500) * (s * k + G.m + 1) *
        (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1) := by
  let X := buildLevelVerts start s k
  let d := routePathLen Δ bh L
  let R := routeCong Δ bh L
  let pairs := connRequestPairs a b s
  have hXcard : X.card = s * k := by simp [X, buildLevelVerts, Nat.mul_comm]
  have hFull := buildFullRouteCost_graph_le (w := w) (K := K) (C := C) (sR := sR)
    (args := args) (mem := mem) hPlayer hPre (by simp [connRequestPairs])
    (fun b' hb' => hC pairs b' hPre hb') X.card 2 (by decide)
  have hRB : routeBoundG (K * (C + 10) + 280) G X pairs Δ L
      (fullRoute route G X pairs Δ L X.card 2).2 ≤
      (K * (C + 10) + 280) * ((s * k + G.m + 1) * (d + 1) * (R + 1)) := by
    have h1 := routeBoundG_mono_b (C := K * (C + 10) + 280) (G := G) (X := X) (pairs := pairs)
      (Δ := Δ) (L := L) hLast
    apply h1.trans
    unfold routeBoundG
    simp only [pairs, connRequestPairs, List.length_singleton, one_mul, hXcard]
    have hmul : (s * k + G.m + 1) * (d + 1) * R + 1 ≤ (s * k + G.m + 1) * (d + 1) * (R + 1) := by
      have hpos : 1 ≤ (s * k + G.m + 1) * (d + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    exact Nat.mul_le_mul_left _ hmul
  have hErase1 : rangeCost (fun i => 136 * ((connectorWalkRow M emb).raw i).length + 330) 0
      (connectorWalkRow M emb).count ≤ s * (136 * d + 330) := by
    change rangeCost _ 0 M.length ≤ _
    rw [hMlen]
    exact rangeCost_le_mul_conn fun j hj => by
      have hlen := hEmbLen j (hMlen.symm ▸ hj)
      simp only [BuildWalkRow.raw, connectorWalkRow, Nat.zero_add]
      omega
  have hErase2 : rangeCost (fun i => 17 * (erase G.edges (edgeAt M i).1 (emb i)).length + 100) 0
      M.length ≤ s * (17 * d + 100) := by
    rw [hMlen]
    exact rangeCost_le_mul_conn fun j hj => by
      have hjM : j < M.length := hMlen.symm ▸ hj
      have hsub := ((erase_spec (emb j).length _ _ _ le_rfl (hWalk j hjM)).2.1).length_le
      have hlen := hEmbLen j hjM
      omega
  have hS : s ≤ s * k := Nat.le_mul_of_pos_right s (by omega)
  let P := (s * k + G.m + 1) * (d + 1) * (R + 1)
  have hsd : s * d ≤ P :=
    (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hs1 : s ≤ P :=
    ((show s ≤ s * k + G.m + 1 by omega).trans (Nat.le_mul_of_pos_right _ (by omega))).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  have h1b : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by dsimp [P]; positivity)
  have hFR : (buildFullRouteContract w K route routeCost sR G X pairs Δ L X.card 2).cost args mem ≤
      2 * (K * (C + 10) + 280) * P := by
    calc _ ≤ 2 * routeBoundG (K * (C + 10) + 280) G X pairs Δ L
            (fullRoute route G X pairs Δ L X.card 2).2 := hFull
      _ ≤ 2 * ((K * (C + 10) + 280) * P) := Nat.mul_le_mul_left 2 hRB
      _ = _ := by ring
  have hExtra : 48 * s + 64 + 40 + (s * (136 * d + 330) + 9 * s + 16 + 130) +
      (s * (17 * d + 100) + 30 * s + 40) + 140 ≤ 1500 * P := by
    have hsimp : 48 * s + 64 + 40 + (s * (136 * d + 330) + 9 * s + 16 + 130) +
        (s * (17 * d + 100) + 30 * s + 40) + 140 = 153 * (s * d) + 517 * s + 430 := by ring
    rw [hsimp]; omega
  simp only [buildConnOneContract, buildConnRouteContract, buildConnEraseContract,
    buildWalkRowContract]
  have hcnt : (connectorWalkRow M emb).count = s := hMlen
  rw [hcnt] at hErase1 ⊢
  rw [hMlen] at hErase2 ⊢
  have hRHS : (2 * (K * (C + 10) + 280) + 1500) * (s * k + G.m + 1) * (d + 1) * (R + 1) =
      2 * (K * (C + 10) + 280) * P + 1500 * P := by dsimp [P]; ring
  change 48 * s + 64 +
      (buildFullRouteContract w K route routeCost sR G X pairs Δ L X.card 2).cost args mem + 40 +
      (rangeCost (fun i => 136 * ((connectorWalkRow M emb).raw i).length + 330) 0 s + 9 * s + 16 + 130) +
      (rangeCost (fun i => 17 * (erase G.edges (edgeAt M i).1 (emb i)).length + 100) 0 s + 30 * s + 40) +
      140 ≤ _
  rw [hRHS]
  linarith

end MinCostFlow.HierPaths
