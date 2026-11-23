module

public import MinCostFlow.ExpanderDecomp.OneShotStepB
public import MinCostFlow.ExpanderDecomp.ProgStepBSpec
public import MinCostFlow.ExpanderDecomp.ProgStepCMath
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure Mathematical Helpers for Step B (`ProgStepBMath`)

Provides the pure list-reconstruction, per-block scatter, fake-edge budget, and cost/space
envelope lemmas used by the Step B Word-RAM procedures (`ProgStepB*.lean`):

* `smallerSide_padToHalf_lists`: reconstructs `(padToHalf B (smallerSide B U)).sort (· ≤ ·)` and
  `(B \ padToHalf B (smallerSide B U)).sort (· ≤ ·)` by partitioning `blockList vs b i` against
  a nodup list for `U`, taking the smaller half, padding from the complement prefix, and
  partitioning `blockList vs b i` once more.
* `savedS_partition_lists`: partitioning `blockList vs b i` by `u ∈ S` yields `(B \ S).sort (· ≤ ·)`
  and `S.sort (· ≤ ·)` in strictly increasing order.
* `scatter_filter_eq_getD`: when terminal pairs `(C'_idx, comp_idx)` are pairwise disjoint and
  `matchings` satisfies `RouteMatchedSpec`, filtering `matchings.flatten` by `e.1 ∈ C'_idx`
  recovers `matchings.getD idx []` as a sublist with exact multiset/cut equivalence (in fact
  identical as a list!).
* `stepB_fake_len_le_k`: `(49 * cp.L + 2) * (k / cp.D q) ≤ k`, justifying the `2 * k` buffer
  `fAddr` in `stepBContract`.
* `stepB_round_router_cost_le`, `stepB_total_cost_le`, `stepB_total_space_le`: pure arithmetic
  envelopes connecting the Word-RAM step and heap bounds to `stepBCostBound` and `stepBSpace`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Sorted Partition Lemmas for `smallerSide`, `padToHalf`, and `savedS` -/

/-- Filtering a strictly increasing list `B_list` (`B_list.toFinset = B`) by `u ∈ S` and `u ∉ S`
yields `(B ∩ S).sort (· ≤ ·)` and `(B \ S).sort (· ≤ ·)`. When `S ⊆ B`, the first is
`S.sort (· ≤ ·)`. -/
lemma filter_blockList_inter_sdiff {B_list : List ℕ} {S : Finset ℕ}
    (hB_lt : B_list.Pairwise (· < ·)) (hSB : S ⊆ B_list.toFinset) :
    B_list.filter (fun u => decide (u ∈ S)) = S.sort (· ≤ ·) ∧
    B_list.filter (fun u => decide (u ∉ S)) = (B_list.toFinset \ S).sort (· ≤ ·) := by
  have hB_eq : B_list = B_list.toFinset.sort (· ≤ ·) := eq_sort_of_pairwise_lt hB_lt
  have h1 := filter_sort_eq_sort_inter B_list.toFinset S
  have h2 := filter_sort_eq_sort_sdiff B_list.toFinset S
  rw [← hB_eq] at h1 h2
  rw [Finset.inter_eq_right.mpr hSB] at h1
  exact ⟨h1, h2⟩

/-- Exact list reconstruction of `padToHalf B (smallerSide B U)` and its complement in `B` from
the sorted block list `B_list` (`B_list.toFinset = B`, even length `b`) and any subset `U ⊆ B`. -/
lemma smallerSide_padToHalf_lists {B_list : List ℕ} {U : Finset ℕ}
    (hB_lt : B_list.Pairwise (· < ·)) (hUB : U ⊆ B_list.toFinset) (heven : Even B_list.length) :
    let B := B_list.toFinset
    let inU := B_list.filter (fun u => decide (u ∈ U))
    let notU := B_list.filter (fun u => decide (u ∉ U))
    let C_list := if inU.length ≤ notU.length then inU else notU
    let rem_list := if inU.length ≤ notU.length then notU else inU
    let pad := rem_list.take (B_list.length / 2 - C_list.length)
    let C' := (C_list ++ pad).toFinset
    C' = padToHalf B (smallerSide B U) ∧
    B_list.filter (fun u => decide (u ∈ C')) = (padToHalf B (smallerSide B U)).sort (· ≤ ·) ∧
    B_list.filter (fun u => decide (u ∉ C')) = (B \ padToHalf B (smallerSide B U)).sort (· ≤ ·) ∧
    (B_list.filter (fun u => decide (u ∈ C'))).length = B_list.length / 2 ∧
    (B_list.filter (fun u => decide (u ∉ C'))).length = B_list.length / 2 := by
  intro B inU notU C_list rem_list pad C'
  have hB_nd : B_list.Nodup := hB_lt.imp fun h => Nat.ne_of_lt h
  have hB_card : B.card = B_list.length := List.toFinset_card_of_nodup hB_nd
  have hpart := filter_blockList_inter_sdiff hB_lt hUB
  have hinU_len : inU.length = U.card := by
    change (B_list.filter (fun u => decide (u ∈ U))).length = U.card
    rw [hpart.1, Finset.length_sort]
  have hnotU_len : notU.length = (B \ U).card := by
    change (B_list.filter (fun u => decide (u ∉ U))).length = (B \ U).card
    rw [hpart.2, Finset.length_sort]
  have hC_eq : C_list.toFinset = smallerSide B U := by
    dsimp only [C_list, smallerSide]
    rw [hinU_len, hnotU_len]
    split_ifs with hle
    · rw [show inU = U.sort (· ≤ ·) from hpart.1]; ext v; simp
    · rw [show notU = (B \ U).sort (· ≤ ·) from hpart.2]; ext v; simp
  have hrem_eq : rem_list = (B \ smallerSide B U).sort (· ≤ ·) := by
    dsimp only [rem_list, smallerSide]
    rw [hinU_len, hnotU_len]
    split_ifs with hle
    · exact hpart.2
    · rw [Finset.sdiff_sdiff_eq_self hUB]; exact hpart.1
  have hC_len : C_list.length = (smallerSide B U).card := by
    dsimp only [C_list, smallerSide]
    rw [hinU_len, hnotU_len]
    split_ifs <;> [exact hinU_len; exact hnotU_len]
  have hC'_eq : C' = padToHalf B (smallerSide B U) := by
    dsimp only [C', pad, padToHalf]
    rw [List.toFinset_append, hC_eq, hrem_eq, hB_card, hC_len]
  have hadd : (B \ U).card + U.card = B.card := Finset.card_sdiff_add_card_eq_card hUB
  have hC_sub : smallerSide B U ⊆ B := by
    unfold smallerSide; split_ifs; exact hUB; exact Finset.sdiff_subset
  have h2C : 2 * (smallerSide B U).card ≤ B.card := by
    unfold smallerSide; split_ifs <;> omega
  have hpad := padToHalf_spec hC_sub h2C (hB_card ▸ heven)
  have hpart2 := filter_blockList_inter_sdiff hB_lt (hC'_eq.symm ▸ hpad.2.1)
  refine ⟨hC'_eq, ?_, ?_, ?_, ?_⟩
  · rw [hpart2.1, hC'_eq]
  · rw [hpart2.2, hC'_eq]
  · rw [hpart2.1, Finset.length_sort, hC'_eq, hpad.2.2.1, hB_card]
  · rw [hpart2.2, Finset.length_sort, hC'_eq, hpad.2.2.2, hpad.2.2.1, hB_card]

/-! ## 2. Exact Per-Block Scatter Lemma for `matchings.flatten` -/

/-- When terminal pairs `pairs` have pairwise disjoint first-endpoint sets and `matchings`
satisfies `RouteMatchedSpec`, filtering `matchings.flatten` by `e.1 ∈ (pairs[idx]).1` recovers
`matchings.getD idx []` identically as a list. -/
lemma filter_flatten_by_fst_eq_getD {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {matchings : List (List (ℕ × ℕ))}
    (hvtp : ValidTerminalPairs X pairs) (hlen : matchings.length = pairs.length)
    (hpm : ∀ j (hj : j < pairs.length),
      IsPartialMatching (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings.getD j []))
    {idx : ℕ} (hidx : idx < pairs.length) :
    matchings.flatten.filter (fun e => decide (e.1 ∈ (pairs[idx]'hidx).1)) =
      matchings.getD idx [] := by
  induction pairs generalizing matchings idx with
  | nil => simp at hidx
  | cons p ps ih =>
    cases matchings with
    | nil => simp at hlen
    | cons m ms =>
      have hlen' : ms.length = ps.length := by simpa using hlen
      have hvtp_tail : ValidTerminalPairs X ps := by
        refine ⟨fun q hq => hvtp.1 q (List.mem_cons_of_mem p hq), ?_⟩
        have hpw := hvtp.2
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
        exact hpw.2.2
      have hpm_tail : ∀ j (hj : j < ps.length),
          IsPartialMatching (ps[j]'hj).1 (ps[j]'hj).2 (ms.getD j []) := fun j hj => by
        simpa using hpm (j + 1) (Nat.succ_lt_succ hj)
      have hdisj_head : ∀ q ∈ ps, Disjoint p.1 q.1 := by
        intro q hq
        have hpw := hvtp.2
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
        exact hpw.1 q.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩))
      simp only [List.flatten_cons, List.filter_append]
      cases idx with
      | zero =>
        have hm_all : m.filter (fun e => decide (e.1 ∈ p.1)) = m := by
          rw [List.filter_eq_self]
          intro e he
          exact decide_eq_true ((hpm 0 (Nat.zero_lt_succ _)).1 e (by simpa using he)).1
        have hms_none : ms.flatten.filter (fun e => decide (e.1 ∈ p.1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          obtain ⟨m', hm', hem'⟩ := List.mem_flatten.mp he
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hm'
          have hj_ps : j < ps.length := by omega
          have he_in : e.1 ∈ (ps[j]'hj_ps).1 := by
            have := (hpm_tail j hj_ps).1 e
            rw [List.getD_eq_getElem _ _ hj] at this
            exact (this hem').1
          have hdj := hdisj_head (ps[j]'hj_ps) (List.getElem_mem hj_ps)
          simp [Finset.disjoint_left.mp hdj |>.mt (not_not.mpr he_in)]
        simp only [List.getElem_cons_zero]
        rw [hm_all, hms_none, List.append_nil]; rfl
      | succ idx' =>
        have hidx' : idx' < ps.length := Nat.lt_of_succ_lt_succ hidx
        have hm_none : m.filter (fun e => decide (e.1 ∈ (ps[idx']'hidx').1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          have he_in : e.1 ∈ p.1 := ((hpm 0 (Nat.zero_lt_succ _)).1 e (by simpa using he)).1
          have hdj := hdisj_head (ps[idx']'hidx') (List.getElem_mem hidx')
          simp [Finset.disjoint_left.mp hdj he_in]
        simp only [List.getElem_cons_succ]
        rw [hm_none, List.nil_append]
        exact ih hvtp_tail hlen' hpm_tail hidx'

/-! ## 3. Step B Fake-Edge, Cost, and Space Envelopes -/

/-- Under `CoreParamsValid cp r`, total fake edges across at most `49 * cp.L + 2` calls with
deficit budget `z = k / cp.D q` never exceed `k`. -/
lemma stepB_fake_len_le_k {cp : CoreParams} {r q k : ℕ} (hcfg : CoreParamsValid cp r)
    (hq1 : 1 ≤ q) (hqr : q ≤ r) :
    (49 * cp.L + 2) * (k / cp.D q) ≤ k := by
  have hΔ := hcfg.hΔ
  have hP := hcfg.hP12 q hq1 hqr
  have hD := hcfg.hD q hq1 hqr
  have hle : 49 * cp.L + 2 ≤ cp.D q := by nlinarith
  calc (49 * cp.L + 2) * (k / cp.D q)
      ≤ cp.D q * (k / cp.D q) := Nat.mul_le_mul_right _ hle
    _ ≤ k := Nat.mul_div_le k (cp.D q)

/-- Every witness graph `W_i` during Step B has at most `cp.Δ * b` edges (since at most
`49 * cp.L + 1` rounds of `b / 2` edges are added and `49 * cp.L + 20 ≤ cp.Δ`). -/
lemma stepB_witness_edges_le {cp : CoreParams} {r b t : ℕ} (hcfg : CoreParamsValid cp r)
    (ht : t ≤ 49 * cp.L + 1) :
    t * (b / 2) ≤ cp.Δ * b := by
  have hΔ := hcfg.hΔ
  have hb : b / 2 ≤ b := Nat.div_le_self b 2
  exact Nat.mul_le_mul (by omega) hb

/-- Bound on `100 * N * L` covering `(49 * L + 1) * nBlocks` when `nBlocks ≤ 2 * N` and `4 ≤ L`. -/
lemma stepB_subCore_calls_le {N L nBlocks : ℕ} (hL : 4 ≤ L) (hnb : nBlocks ≤ 2 * N) :
    (49 * L + 1) * nBlocks ≤ 100 * N * L := by
  have h1 : 49 * L + 1 ≤ 50 * L := by omega
  have h2 : (49 * L + 1) * nBlocks ≤ (50 * L) * (2 * N) := Nat.mul_le_mul h1 hnb
  have h3 : (50 * L) * (2 * N) = 100 * N * L := by ring
  omega

/-- Single-round router cost bound `R1` for `routerCallCost` (`C_route = 80`) under `stepBContract`
preconditions. -/
def stepBRouterR1 (N L q : ℕ) : ℕ :=
  3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0 * N ^ (q + 1) * L ^ 7

lemma stepB_single_routerCallCost_le {cfg : ParamConfig} {M r q z : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hqr : q ≤ r)
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hX2 : 2 ≤ X.card) (hXle : X.card ≤ (coreParamsOf cfg M r).N ^ q)
    (hpairs : ValidTerminalPairs X pairs) (hplen : pairs.length ≤ 2 * (coreParamsOf cfg M r).N) :
    routerCallCost G X pairs (coreParamsOf cfg M r).Δ (coreParamsOf cfg M r).L 100 z ≤
      stepBRouterR1 (NOf M r) (LParam M) q := by
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hN1 : 1 ≤ NOf M r := by omega
  have hΔ : 1 ≤ deltaParam M := one_le_tParam M
  have hXL : X.card < 2 ^ LParam M := by
    have h1 : X.card ≤ (NOf M r) ^ r := le_trans hXle (Nat.pow_le_pow_right hN1 hqr)
    exact lt_of_le_of_lt h1 hcfg.hNrL
  have hbase := routerCallCost_bounded G X pairs (deltaParam M) (LParam M) 100 z hX hGloop hΔ hdegG
    (by omega) hXL (by decide) hpairs
  rw [routePathLen_core_eq, routeCong_core_eq] at hbase
  have hins : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * X.card := by
    have h2 : 2 * (G.inside X).length ≤ (coreParamsOf cfg M r).Δ * X.card := by
      rw [← volIn_self]; exact volIn_le_mul_card (Finset.Subset.refl X) hdegG
    unfold coreParamsOf deltaParam tParam at h2
    dsimp only at h2
    have hsplit : 1024 * LParam M * X.card = 2 * (512 * LParam M * X.card) := by ring
    have h1 : (G.inside X).length ≤ 512 * LParam M * X.card := by omega
    have h3 : X.card + 1 ≤ 512 * LParam M * X.card := by nlinarith
    omega
  have hinsN : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * (NOf M r) ^ q :=
    le_trans hins (Nat.mul_le_mul_left _ hXle)
  have hd : dCore M + 1 ≤ ParamConfig.d0 * (LParam M) ^ 2 := by
    unfold dCore deltaParam tParam ParamConfig.d0
    have hL : 1 ≤ (LParam M) ^ 2 := by nlinarith
    have heq : 3200 * (1024 * LParam M) * LParam M = 3276800 * (LParam M) ^ 2 := by ring
    omega
  have hR : RCore M ≤ ParamConfig.R0 * (LParam M) ^ 4 := by
    unfold RCore deltaParam tParam ParamConfig.R0
    calc 1600 * (1024 * LParam M) * (dCore M + 1) * LParam M
        ≤ 1600 * (1024 * LParam M) * (ParamConfig.d0 * (LParam M) ^ 2) * LParam M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
      _ = 1600 * 1024 * ParamConfig.d0 * (LParam M) ^ 4 := by ring
  set B := 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7
  have hBpos : 1 ≤ B := by
    have h1 : 1 ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 := by
      unfold ParamConfig.R0 ParamConfig.d0; decide
    have h2 : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ hN1
    have h3 : 1 ≤ (LParam M) ^ 7 := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 * 1 := by decide
      _ ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hprod : pairs.length * (X.card + (G.inside X).length + 1) * (dCore M + 1) * RCore M ≤ 2 * B := by
    calc pairs.length * (X.card + (G.inside X).length + 1) * (dCore M + 1) * RCore M
        ≤ (2 * NOf M r) * (1024 * LParam M * (NOf M r) ^ q) *
            (ParamConfig.d0 * (LParam M) ^ 2) * (ParamConfig.R0 * (LParam M) ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hplen hinsN) hd) hR
      _ = 2 * B := by dsimp only [B]; ring
  calc routerCallCost G X pairs (deltaParam M) (LParam M) 100 z
      ≤ 80 * (pairs.length * (X.card + (G.inside X).length + 1) * (dCore M + 1) * RCore M + 1) := hbase
    _ ≤ 80 * (2 * B + B) := Nat.mul_le_mul_left _ (Nat.add_le_add hprod hBpos)
    _ = stepBRouterR1 (NOf M r) (LParam M) q := by unfold stepBRouterR1; dsimp only [B]; ring

/-- Constant multiplier `K_B` covering all non-`subCore` work in Step B (`≤ 49 * L + 2` router
calls + local per-round loops). -/
def stepBTimeConst (C_rt : ℕ) : ℕ :=
  (C_rt + 1) * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0 + 1000000)

/-- Constant multiplier `S_B` covering all non-`subCore` heap allocations in Step B (`≤ 49 * L + 2`
calls to `outerRouterSpace` + persistent witness graphs and per-round buffers). -/
def stepBSpaceConst (C_sp : ℕ) : ℕ :=
  (C_sp + 1) * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0 + 500000)

lemma stepB_nonSubCore_cost_le {C_rt N L q : ℕ} (hN : 4 ≤ N) (hL : 4 ≤ L) :
    (49 * L + 2) * (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) +
      2000 * N ^ q * L + 2000 ≤
      stepBTimeConst C_rt * N ^ (q + 1) * L ^ 8 := by
  have hN1 : 1 ≤ N := by omega
  have hL1 : 1 ≤ L := by omega
  have hNq : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (Nat.le_succ q)
  have hNq_pos : 1 ≤ N ^ (q + 1) := Nat.one_le_pow _ _ hN1
  have hL8_pos : 1 ≤ L ^ 8 := Nat.one_le_pow _ _ hL1
  have h49 : 49 * L + 2 ≤ 50 * L := by omega
  have hR1 : stepBRouterR1 N L q =
      (3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7) := by
    unfold stepBRouterR1; ring
  have h50L_R1 : (49 * L + 2) * stepBRouterR1 N L q ≤
      (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 8) := by
    rw [hR1]
    have hmul : (49 * L + 2) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) ≤
        (50 * L) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) :=
      Nat.mul_le_mul_right _ h49
    have heq : (50 * L) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) =
        (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 8) := by ring
    omega
  have hN_le : N ≤ N ^ (q + 1) := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (Nat.succ_pos q)
  have hL_le : L ≤ L ^ 8 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 8 := Nat.pow_le_pow_right hL1 (by decide)
  have hM : 1 ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul hNq_pos hL8_pos
  have hNL_le : N ^ (q + 1) * L ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul_left _ hL_le
  have hNqL_le : N ^ q * L ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul hNq hL_le
  have hL_M : L ≤ N ^ (q + 1) * L ^ 8 := le_trans hL_le (Nat.le_mul_of_pos_left _ hNq_pos)
  set P := N ^ (q + 1) * L ^ 8
  have h1 : (49 * L + 2) * (C_rt * stepBRouterR1 N L q) ≤
      C_rt * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by
    have heq : (49 * L + 2) * (C_rt * stepBRouterR1 N L q) = C_rt * ((49 * L + 2) * stepBRouterR1 N L q) := by ring
    have heq2 : C_rt * ((50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P) =
        C_rt * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by ring
    rw [heq, ← heq2]
    exact Nat.mul_le_mul_left C_rt h50L_R1
  have h2 : (49 * L + 2) * C_rt ≤ 50 * C_rt * P := by
    have ha : (49 * L + 2) * C_rt ≤ (50 * L) * C_rt := Nat.mul_le_mul_right _ h49
    have hb : (50 * L) * C_rt ≤ (50 * P) * C_rt := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 50 hL_M)
    have hc : (50 * P) * C_rt = 50 * C_rt * P := by ring
    omega
  have hL2_le : L ^ 2 ≤ L ^ 8 := Nat.pow_le_pow_right hL1 (by decide)
  have hNL2_le : N ^ (q + 1) * L ^ 2 ≤ N ^ (q + 1) * L ^ 8 := Nat.mul_le_mul_left _ hL2_le
  have h3 : (49 * L + 2) * (5000 * N ^ q * L + 2000 * N + 2000) ≤ 450000 * P := by
    have hNqL : N ^ q * L ≤ N ^ (q + 1) * L := Nat.mul_le_mul_right L hNq
    have hNL : N ≤ N ^ (q + 1) * L := le_trans hN_le (Nat.le_mul_of_pos_right _ hL1)
    have h1L : 1 ≤ N ^ (q + 1) * L := Nat.mul_le_mul hNq_pos hL1
    have ha : 5000 * N ^ q * L + 2000 * N + 2000 ≤ 9000 * (N ^ (q + 1) * L) := by
      have : 5000 * N ^ q * L = 5000 * (N ^ q * L) := by ring
      omega
    have hb : (49 * L + 2) * (5000 * N ^ q * L + 2000 * N + 2000) ≤ (50 * L) * (9000 * (N ^ (q + 1) * L)) :=
      Nat.mul_le_mul h49 ha
    have hc : (50 * L) * (9000 * (N ^ (q + 1) * L)) = 450000 * (N ^ (q + 1) * L ^ 2) := by ring
    have hd : 450000 * (N ^ (q + 1) * L ^ 2) ≤ 450000 * P := Nat.mul_le_mul_left 450000 hNL2_le
    omega
  have h4 : (49 * L + 2) * (C_rt * stepBRouterR1 N L q + C_rt + 5000 * N ^ q * L + 2000 * N + 2000) =
      (49 * L + 2) * (C_rt * stepBRouterR1 N L q) + (49 * L + 2) * C_rt +
      (49 * L + 2) * (5000 * N ^ q * L + 2000 * N + 2000) := by ring
  have h5 : stepBTimeConst C_rt * N ^ (q + 1) * L ^ 8 =
      C_rt * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P +
      (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P +
      C_rt * 1000000 * P + 1000000 * P := by
    unfold stepBTimeConst; dsimp only [P]; ring
  have h6 : 50 * C_rt * P ≤ C_rt * 1000000 * P := by
    have ha : 50 * C_rt ≤ C_rt * 1000000 := by omega
    exact Nat.mul_le_mul_right P ha
  have h7 : 2000 * N ^ q * L ≤ 2000 * P := by
    have heq : 2000 * N ^ q * L = 2000 * (N ^ q * L) := by ring
    have := Nat.mul_le_mul_left 2000 hNqL_le
    omega
  omega

lemma stepB_nonSubCore_space_le {C_sp n N L q : ℕ} (hN : 4 ≤ N) (hL : 4 ≤ L) :
    (49 * L + 2) * (outerRouterSpace C_sp n (stepBRouterR1 N L q) + 20 * N ^ q + 20 * N + 2 * n + 20) +
      200 * N ^ q * L + 200 * N + 200 ≤
      stepBSpaceConst C_sp * ((n + 3) ^ 4 * L + N ^ (q + 1) * L ^ 8) := by
  have hN1 : 1 ≤ N := by omega
  have hL1 : 1 ≤ L := by omega
  have hNq : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (Nat.le_succ q)
  have hNq_pos : 1 ≤ N ^ (q + 1) := Nat.one_le_pow _ _ hN1
  have hL8_pos : 1 ≤ L ^ 8 := Nat.one_le_pow _ _ hL1
  have h49 : 49 * L + 2 ≤ 50 * L := by omega
  have hpow : (n + 3) ^ 4 = n ^ 4 + 12 * n ^ 3 + 54 * n ^ 2 + 108 * n + 81 := by ring
  have hn4 : 2 * n + 1 ≤ (n + 3) ^ 4 := by omega
  have hR1 : stepBRouterR1 N L q =
      (3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7) := by
    unfold stepBRouterR1; ring
  set P := N ^ (q + 1) * L ^ 8
  set Q := (n + 3) ^ 4 * L
  have h50L_R1 : (49 * L + 2) * stepBRouterR1 N L q ≤
      (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by
    rw [hR1]
    have hmul : (49 * L + 2) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) ≤
        (50 * L) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) :=
      Nat.mul_le_mul_right _ h49
    have heq : (50 * L) * ((3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * (N ^ (q + 1) * L ^ 7)) =
        (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by dsimp only [P]; ring
    omega
  have hN_le : N ≤ N ^ (q + 1) := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (Nat.succ_pos q)
  have hL_le : L ≤ L ^ 8 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 8 := Nat.pow_le_pow_right hL1 (by decide)
  have hM : 1 ≤ P := Nat.mul_le_mul hNq_pos hL8_pos
  have hNL_le : N ^ (q + 1) * L ≤ P := Nat.mul_le_mul_left _ hL_le
  have hNqL_le : N ^ q * L ≤ P := Nat.mul_le_mul hNq hL_le
  have hrt_exp : outerRouterSpace C_sp n (stepBRouterR1 N L q) =
      C_sp * stepBRouterR1 N L q + C_sp * ((n + 3) ^ 4 + 1) := by
    unfold outerRouterSpace; ring
  rw [hrt_exp]
  have h1 : (49 * L + 2) * (C_sp * stepBRouterR1 N L q) ≤
      C_sp * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by
    have heq : (49 * L + 2) * (C_sp * stepBRouterR1 N L q) = C_sp * ((49 * L + 2) * stepBRouterR1 N L q) := by ring
    have heq2 : C_sp * ((50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P) =
        C_sp * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P := by ring
    rw [heq, ← heq2]; exact Nat.mul_le_mul_left C_sp h50L_R1
  have h2 : (49 * L + 2) * (C_sp * ((n + 3) ^ 4 + 1)) ≤ C_sp * 100 * Q := by
    have ha : (n + 3) ^ 4 + 1 ≤ 2 * (n + 3) ^ 4 := by omega
    have hb : (49 * L + 2) * (C_sp * ((n + 3) ^ 4 + 1)) ≤ (50 * L) * (C_sp * (2 * (n + 3) ^ 4)) :=
      Nat.mul_le_mul h49 (Nat.mul_le_mul_left C_sp ha)
    have hc : (50 * L) * (C_sp * (2 * (n + 3) ^ 4)) = C_sp * 100 * Q := by dsimp only [Q]; ring
    omega
  have h3 : (49 * L + 2) * (20 * N ^ q + 20 * N + 2 * n + 20) ≤ 3000 * P + 50 * Q := by
    have ha : 20 * N ^ q + 20 * N + 20 ≤ 60 * N ^ (q + 1) := by omega
    have hb : (49 * L + 2) * (20 * N ^ q + 20 * N + 20) ≤ (50 * L) * (60 * N ^ (q + 1)) :=
      Nat.mul_le_mul h49 ha
    have hc : (50 * L) * (60 * N ^ (q + 1)) = 3000 * (N ^ (q + 1) * L) := by ring
    have hd : (49 * L + 2) * (2 * n) ≤ (50 * L) * (n + 3) ^ 4 := Nat.mul_le_mul h49 (by omega)
    have he : (50 * L) * (n + 3) ^ 4 = 50 * Q := by dsimp only [Q]; ring
    have hf : (49 * L + 2) * (20 * N ^ q + 20 * N + 2 * n + 20) =
        (49 * L + 2) * (20 * N ^ q + 20 * N + 20) + (49 * L + 2) * (2 * n) := by ring
    have hg : 3000 * (N ^ (q + 1) * L) ≤ 3000 * P := Nat.mul_le_mul_left 3000 hNL_le
    omega
  have h4 : (49 * L + 2) * (C_sp * stepBRouterR1 N L q + C_sp * ((n + 3) ^ 4 + 1) +
      20 * N ^ q + 20 * N + 2 * n + 20) =
      (49 * L + 2) * (C_sp * stepBRouterR1 N L q) + (49 * L + 2) * (C_sp * ((n + 3) ^ 4 + 1)) +
      (49 * L + 2) * (20 * N ^ q + 20 * N + 2 * n + 20) := by ring
  have h5 : stepBSpaceConst C_sp * (Q + P) =
      C_sp * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P +
      (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * P +
      C_sp * (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * Q +
      (50 * 3 * 80 * 1024 * ParamConfig.d0 * ParamConfig.R0) * Q +
      C_sp * 500000 * Q + 500000 * Q + C_sp * 500000 * P + 500000 * P := by
    unfold stepBSpaceConst; ring
  have h6 : C_sp * 100 * Q ≤ C_sp * 500000 * Q :=
    Nat.mul_le_mul_right Q (by omega)
  have h7 : N ≤ P := le_trans hN_le (Nat.le_mul_of_pos_right _ hL8_pos)
  have h8 : 200 * N ^ q * L ≤ 200 * P := by
    have heq : 200 * N ^ q * L = 200 * (N ^ q * L) := by ring
    have := Nat.mul_le_mul_left 200 hNqL_le
    omega
  omega

end MinCostFlow.ExpanderDecomp
