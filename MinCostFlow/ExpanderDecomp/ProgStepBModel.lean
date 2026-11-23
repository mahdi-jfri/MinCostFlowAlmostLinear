module

public import MinCostFlow.ExpanderDecomp.ProgStepBMath
public import MinCostFlow.ExpanderDecomp.OneShotStepB

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step B Per-Round Model Invariant (`ProgStepBModel`)

Pure mathematical invariant `SbModelInv` and transition theorems for Step B (`OneShotStepB.lean`)
when the recursive sub-core oracle returns an arbitrary `CoreResult` satisfying `CoreSpec` on each
active block call (matching the existential postcondition of `stepBSubCoreContract`).

Main results:
- `SbModelInv`, `sbModelInv_init`
- `sbModelInv_block_pre`
- `sbModelInv_round_step`
- `sbModelInv_final_inj`
- `stepB_block_arith`
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ## 1. Parameter Arithmetic for Step B -/

/-- Basic arithmetic consequences of `stepBContract`'s parameter hypotheses (`q ≥ 2`,
`b = N^(q-1) / 2`, `nBlocks = k / b`, `k ≤ N^q`, `4 ≤ N`, `4 ≤ L`). -/
lemma stepB_block_arith {cfg : ParamConfig} {M r q k b nBlocks : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq2 : 2 ≤ q) (hqr : q ≤ r)
    (hk_lo : (coreParamsOf cfg M r).N ^ (q - 1) / 2 ≤ k)
    (hk_hi : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_eq : b = (coreParamsOf cfg M r).N ^ (q - 1) / 2)
    (hnb_eq : nBlocks = k / b) :
    let cp := coreParamsOf cfg M r
    4 ≤ cp.N ∧ 4 ≤ cp.L ∧ 2 ≤ b ∧ Even b ∧ b ≤ cp.N ^ (q - 1) ∧
    1 ≤ nBlocks ∧ nBlocks ≤ 2 * cp.N ∧ nBlocks * b ≤ k ∧ k < 2 ^ cp.L := by
  intro cp
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hN4 : 4 ≤ cp.N := four_le_NOf M r
  have hL4 : 4 ≤ cp.L := four_le_LParam M
  have h4_dvd_N : 4 ∣ cp.N := by
    change 4 ∣ NOf M r
    unfold NOf
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left 2 (ceilDiv (ell M) r))
    rw [hd, Nat.pow_add]
    exact ⟨2 ^ d, by ring⟩
  have h4_dvd_pow : 4 ∣ cp.N ^ (q - 1) := by
    have hq1 : 1 ≤ q - 1 := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hq1
    rw [hm, Nat.pow_add, pow_one]
    exact dvd_mul_of_dvd_left h4_dvd_N _
  obtain ⟨c, hc⟩ := h4_dvd_pow
  have hc_pos : 1 ≤ c := by
    have hpow_pos : 4 ≤ cp.N ^ (q - 1) := by
      calc 4 ≤ cp.N := hN4
        _ = cp.N ^ 1 := (pow_one cp.N).symm
        _ ≤ cp.N ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hb_2c : b = 2 * c := by rw [hb_eq, hc]; omega
  have hb2 : 2 ≤ b := by omega
  have hb_even : Even b := ⟨c, by omega⟩
  have hb_le : b ≤ cp.N ^ (q - 1) := hb_eq ▸ Nat.div_le_self _ 2
  have hnb1 : 1 ≤ nBlocks := by
    rw [hnb_eq]
    exact Nat.div_pos (by omega) (by omega)
  have hnb_le : nBlocks ≤ 2 * cp.N := by
    rw [hnb_eq]
    have hpow_eq : cp.N ^ q = 2 * cp.N * b := by
      have hq_eq : q = (q - 1) + 1 := by omega
      rw [hq_eq, Nat.pow_succ, hc, hb_2c]; ring
    rw [hpow_eq] at hk_hi
    calc k / b ≤ (2 * cp.N * b) / b := Nat.div_le_div_right hk_hi
      _ = 2 * cp.N := Nat.mul_div_cancel (2 * cp.N) (by omega)
  have hnb_b : nBlocks * b ≤ k := hnb_eq ▸ Nat.div_mul_le_self k b
  have hkL : k < 2 ^ cp.L := by
    have h1 : cp.N ^ q ≤ cp.N ^ r := Nat.pow_le_pow_right (by omega) hqr
    exact lt_of_le_of_lt (le_trans hk_hi h1) hcfg.hNrL
  exact ⟨hN4, hL4, hb2, hb_even, hb_le, hnb1, hnb_le, hnb_b, hkL⟩

/-! ## 2. Per-Round Model Invariant -/

/-- Pure mathematical invariant after `t` rounds of Step B (`0 ≤ t ≤ 49 * cfg.L + 1`), tracking
a `BlockGameState` whose rounds were produced by arbitrary `CoreSpec`-valid sub-core outputs. -/
structure SbModelInv (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b nBlocks z t : ℕ) (st : BlockGameState) : Prop where
  calls_len : st.calls.length ≤ t
  calls_valid : ∀ c ∈ st.calls, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z
  numRounds_le : ∀ i < nBlocks, st.numRounds i ≤ t
  active_numRounds : ∀ i < nBlocks, st.active i = true → st.numRounds i = t
  rounds_pm : ∀ i < nBlocks, ∀ j < st.numRounds i, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j)
  rounds_len : ∀ i < nBlocks, ∀ j < st.numRounds i, (st.rounds i j).length = b / 2
  rounds_cut : ∀ i < nBlocks, ∀ j < st.numRounds i,
    ∃ C ⊆ blockSet vs b i,
      (blockSet vs b i).card ≤ 4 * C.card ∧
      (∀ e ∈ st.rounds i j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
      100 * (Graph.mk G.n (witnessEdges (st.rounds i) j)).cutIn (blockSet vs b i) C ≤
        (blockSet vs b i).card
  inactive_exp : ∀ i < nBlocks, st.active i = false →
    st.savedS i ⊆ blockSet vs b i ∧
    (blockSet vs b i).card ≤ 2 * (st.savedS i).card ∧
    (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).IsExpansionExpanderOn
      (st.savedS i) (1 / (cfg.P (q - 1) : ℝ))
  sub_cut : ∀ i < nBlocks, ∀ Y S : Finset ℕ,
    (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).cutIn Y S ≤
      (Graph.mk G.n (callsWitnessEdges st.calls)).cutIn Y S

lemma sbModelInv_init (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b nBlocks z : ℕ) : SbModelInv cfg q G X vs b nBlocks z 0 BlockGameState.init where
  calls_len := by simp [BlockGameState.init]
  calls_valid := by simp [BlockGameState.init]
  numRounds_le := by simp [BlockGameState.init]
  active_numRounds := by simp [BlockGameState.init]
  rounds_pm := by simp [BlockGameState.init]
  rounds_len := by simp [BlockGameState.init]
  rounds_cut := by simp [BlockGameState.init]
  inactive_exp := by simp [BlockGameState.init]
  sub_cut := by simp [BlockGameState.init, witnessEdges, Graph.cutIn, Graph.inside]

/-- Length of `witnessEdges M m` when each round has length `halfB`. -/
lemma witnessEdges_length {M : ℕ → List (ℕ × ℕ)} {m halfB : ℕ}
    (hlen : ∀ j < m, (M j).length = halfB) :
    (witnessEdges M m).length = m * halfB := by
  induction m with
  | zero => simp [witnessEdges]
  | succ m ih =>
    rw [witnessEdges, List.length_append, ih (fun j hj => hlen j (Nat.lt_succ_of_lt hj)),
      hlen m (Nat.lt_succ_self m), Nat.succ_mul]

/-- Modifying `M` at index `t` does not change `witnessEdges M j` for `j ≤ t`. -/
lemma witnessEdges_congr_lt {M₁ M₂ : ℕ → List (ℕ × ℕ)} {m : ℕ}
    (h : ∀ j < m, M₁ j = M₂ j) : witnessEdges M₁ m = witnessEdges M₂ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [witnessEdges, witnessEdges, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h m (Nat.lt_succ_self m)]

/-- A witness built from `m` perfect matchings on `B` is loopless and has degree `≤ m` on `B`. -/
private lemma sb_witnessEdges_loopless_deg_le {n m : ℕ} {B : Finset ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < m, IsPerfectMatchingOn B (M j)) :
    (∀ e ∈ (Graph.mk n (witnessEdges M m)).inside B, e.1 ≠ e.2) ∧
    (∀ v ∈ B, (Graph.mk n (witnessEdges M m)).degIn B v ≤ m) := by
  induction m with
  | zero =>
    refine ⟨fun e he => by simp [witnessEdges, Graph.inside] at he,
      fun v _ => by simp [witnessEdges, Graph.degIn, Graph.inside]⟩
  | succ m ih =>
    have hprev := ih fun j hj => hM j (Nat.lt_succ_of_lt hj)
    have hm := hM m (Nat.lt_succ_self m)
    have hnd := hm.2.1
    have hloop : ∀ e ∈ M m, e.1 ≠ e.2 := by
      have hgen : ∀ (L : List (ℕ × ℕ)), (L.flatMap fun e => [e.1, e.2]).Nodup →
          ∀ e ∈ L, e.1 ≠ e.2 := by
        intro L
        induction L with
        | nil => intro _ e he; simp at he
        | cons p rest ihr =>
          rcases p with ⟨a, b⟩
          intro hnd' e he
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd'
          rcases List.mem_cons.mp he with rfl | hrest
          · intro heq; dsimp only at heq; apply hnd'.1; rw [heq]; exact List.mem_cons_self
          · exact ihr hnd'.2.2 e hrest
      exact hgen (M m) hnd
    have hdeg_m : ∀ v ∈ B, (Graph.mk n (M m)).degIn B v ≤ 1 := by
      intro v _
      have h1 : ((Graph.mk n (M m)).inside B |>.filter fun e => e.1 = v).length ≤
          ((M m).filter fun e => e.1 = v).length := by
        unfold Graph.inside; rw [List.filter_filter]
        exact length_filter_le_of_imp (M m) fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have h2 : ((Graph.mk n (M m)).inside B |>.filter fun e => e.2 = v).length ≤
          ((M m).filter fun e => e.2 = v).length := by
        unfold Graph.inside; rw [List.filter_filter]
        exact length_filter_le_of_imp (M m) fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have hsum : ((M m).filter fun e => e.1 = v).length + ((M m).filter fun e => e.2 = v).length =
          ((M m).flatMap fun e => [e.1, e.2]).count v := by
        clear h1 h2 hnd hloop hm hprev ih hM
        induction M m with
        | nil => simp
        | cons p rest ihr =>
          rcases p with ⟨a, b⟩
          simp only [List.filter_cons, List.flatMap_cons, List.cons_append, List.nil_append,
            List.count_cons, beq_iff_eq]
          by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb] <;> omega
      have hcnt : ((M m).flatMap fun e => [e.1, e.2]).count v ≤ 1 :=
        List.nodup_iff_count_le_one.mp hnd v
      unfold Graph.degIn; omega
    refine ⟨fun e he => ?_, fun v hv => ?_⟩
    · rw [mem_inside_iff, witnessEdges] at he
      rcases List.mem_append.mp he.1 with h1 | h2
      · exact hprev.1 e (mem_inside_iff.mpr ⟨h1, he.2.1, he.2.2⟩)
      · exact hloop e h2
    · rw [witnessEdges, degIn_append]
      have := hprev.2 v hv; have := hdeg_m v hv; omega

/-- Every block `i < nBlocks` under `SbModelInv t st` (`t ≤ 49 * cfg.L + 1`) meets all
preconditions of `stepBSubCoreContract` at level `q - 1`. -/
lemma sbModelInv_block_pre {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z t : ℕ} {st : BlockGameState}
    (hX : X ⊆ Finset.range G.n) (hnd : vs.Nodup) (hvs : vs.toFinset = X)
    (hb_le : b ≤ cfg.N ^ (q - 1)) (ht : t ≤ 49 * cfg.L + 1)
    (hinv : SbModelInv cfg q G X vs b (numFullBlocks vs b) z t st)
    {i : ℕ} (hi : i < numFullBlocks vs b) :
    let W := Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))
    let B := blockSet vs b i
    B ⊆ Finset.range W.n ∧ W.IsValid ∧ (∀ e ∈ W.inside B, e.1 ≠ e.2) ∧
      B.card = b ∧ B.card ≤ cfg.N ^ (q - 1) ∧
      (∀ v ∈ B, W.degIn B v ≤ cfg.Δ) ∧ W.m = st.numRounds i * (b / 2) ∧ W.m ≤ cfg.Δ * b := by
  dsimp only
  have hBsub : blockSet vs b i ⊆ Finset.range G.n :=
    (blockSet_subset_toFinset vs b i).trans (hvs.symm ▸ hX)
  have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
  have hwd := sb_witnessEdges_loopless_deg_le (n := G.n) (hinv.rounds_pm i hi)
  have hWvalid : (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).IsValid := by
    have hgen : ∀ m, (∀ j < m, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j)) →
        ∀ e ∈ witnessEdges (st.rounds i) m, e.1 < G.n ∧ e.2 < G.n := by
      intro m hm e he
      induction m with
      | zero => simp [witnessEdges] at he
      | succ m ihm =>
        rw [witnessEdges] at he
        rcases List.mem_append.mp he with h1 | h2
        · exact ihm (fun j hj => hm j (Nat.lt_succ_of_lt hj)) h1
        · have hmem := (hm m (Nat.lt_succ_self m)).1 e h2
          exact ⟨Finset.mem_range.mp (hBsub hmem.1), Finset.mem_range.mp (hBsub hmem.2)⟩
    exact hgen (st.numRounds i) (hinv.rounds_pm i hi)
  have hnr := hinv.numRounds_le i hi
  have hΔ := hcfg.hΔ
  have hWm : (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).m = st.numRounds i * (b / 2) :=
    witnessEdges_length (hinv.rounds_len i hi)
  have hWm_le : st.numRounds i * (b / 2) ≤ cfg.Δ * b :=
    stepB_witness_edges_le hcfg (by omega)
  exact ⟨hBsub, hWvalid, hwd.1, hBcard, by rw [hBcard]; exact hb_le,
    fun v hv => le_trans (hwd.2 v hv) (by omega), hWm, hWm ▸ hWm_le⟩

/-! ## 3. Single-Round Transition Lemma -/

/-- One round of Step B given per-block `CoreSpec`-valid outcomes `res i` for all active blocks.
Produces either a router cut satisfying `RouteCutSpec`, or the updated `BlockGameState` satisfying
`SbModelInv (t + 1)` with exact per-block witness-graph and fake-edge updates. -/
theorem sbModelInv_round_step {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z t : ℕ} {st : BlockGameState}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X)
    (hb_pos : 0 < b) (hb_even : Even b)
    (hinv : SbModelInv cfg q G X vs b (numFullBlocks vs b) z t st)
    (res : ℕ → CoreResult)
    (hres : ∀ i < numFullBlocks vs b, st.active i = true →
      CoreSpec cfg (q - 1) (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
        (blockSet vs b i) (res i)) :
    let k := numFullBlocks vs b
    let rpairs : List (ℕ × (Finset ℕ × Finset ℕ)) := (List.range k).filterMap fun i =>
      if st.active i then
        match res i with
        | .expander _ => none
        | .cut U =>
            let B := blockSet vs b i
            let C' := padToHalf B (smallerSide B U)
            some (i, (C', B \ C'))
      else none
    let pairs := rpairs.map Prod.snd
    ValidTerminalPairs X pairs ∧ pairs.length ≤ k ∧
    match routeOrCut G X pairs cfg.Δ cfg.L 100 z with
    | .cut U => RouteCutSpec G X 100 z U
    | .matched matchings emb =>
        let rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩
        let newM : ℕ → List (ℕ × ℕ) := fun i =>
          match rpairs.findIdx? (fun ip => decide (ip.1 = i)) with
          | none => []
          | some idx =>
              let p := pairs.getD idx (∅, ∅)
              let m := matchings.getD idx []
              m ++ completeMatchingFake p.1 p.2 m
        let st' : BlockGameState :=
          { active := fun i =>
              if i < k ∧ st.active i then
                match res i with | .expander _ => false | .cut _ => true
              else st.active i
            savedS := fun i =>
              if i < k ∧ st.active i then
                match res i with | .expander S => S | .cut _ => st.savedS i
              else st.savedS i
            numRounds := fun i =>
              if i < k ∧ st.active i then
                match res i with | .expander _ => st.numRounds i | .cut _ => st.numRounds i + 1
              else st.numRounds i
            rounds := fun i j =>
              if i < k ∧ st.active i then
                match res i with
                | .expander _ => st.rounds i j
                | .cut _ => if j = st.numRounds i then newM i else st.rounds i j
              else st.rounds i j
            calls := if pairs.isEmpty then st.calls else st.calls ++ [rc] }
        SbModelInv cfg q G X vs b k z (t + 1) st' ∧
        (∀ idx (hidx : idx < rpairs.length),
          newM (rpairs[idx]'hidx).1 =
            matchings.getD idx [] ++
              completeMatchingFake (pairs[idx]'(by simp [pairs, hidx])).1
                (pairs[idx]'(by simp [pairs, hidx])).2 (matchings.getD idx [])) := by
  intro k rpairs pairs
  have hmem_rp : ∀ i p, (i, p) ∈ rpairs ↔
      i < k ∧ st.active i = true ∧
      ∃ U, res i = .cut U ∧
        p = (padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U),
             blockSet vs b i \ padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U)) := by
    intro i p
    dsimp only [rpairs]
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨j, hj, hsome⟩
      have hjk : j < k := List.mem_range.mp hj
      by_cases hact : st.active j = true
      · simp only [hact, ↓reduceIte] at hsome
        cases hsc : res j with
        | expander S => simp [hsc] at hsome
        | cut U =>
          simp only [hsc, Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨rfl, rfl⟩ := hsome
          exact ⟨hjk, hact, U, hsc, rfl⟩
      · simp [hact] at hsome
    · rintro ⟨hik, hact, U, hsc, rfl⟩
      exact ⟨i, List.mem_range.mpr hik, by simp [hact, hsc]⟩
  have hids_sub : List.Sublist (rpairs.map Prod.fst) (List.range k) := by
    have hgen : ∀ (l : List ℕ) (f : ℕ → Option (ℕ × (Finset ℕ × Finset ℕ))),
        (∀ a p, f a = some p → p.1 = a) → List.Sublist ((l.filterMap f).map Prod.fst) l := by
      intro l f hf
      induction l with
      | nil => simp
      | cons a rest ih =>
        rw [List.filterMap_cons]
        cases hfa : f a with
        | none => exact List.Sublist.cons a ih
        | some p => rw [List.map_cons, hf a p hfa]; exact List.Sublist.cons_cons a ih
    refine hgen (List.range k) _ fun a p hp => ?_
    by_cases hact : st.active a = true
    · simp only [hact, ↓reduceIte] at hp
      cases hsc : res a with
      | expander _ => simp [hsc] at hp
      | cut _ => simp only [hsc, Option.some.injEq] at hp; rw [← hp]
    · simp [hact] at hp
  have hids_nd : (rpairs.map Prod.fst).Nodup := hids_sub.nodup List.nodup_range
  have hplen_le : pairs.length ≤ k := by
    have := hids_sub.length_le
    simp only [pairs, List.length_map, List.length_range] at this ⊢; exact this
  have hvp : ValidTerminalPairs X pairs := by
    rw [← hvs]
    refine validTerminalPairs_of_distinct_blocks hnd hb_pos hids_nd fun ip hip => ?_
    rcases ip with ⟨i, p⟩
    obtain ⟨hik, hact, U, hsc, rfl⟩ := (hmem_rp i p).mp hip
    have hcs := hres i hik hact; rw [hsc] at hcs
    have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hik
    have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
    have hpad := padToHalf_spec hsm.1 hsm.2.1 (by rw [hBcard]; exact hb_even)
    exact ⟨hik, hpad.2.1, Finset.sdiff_subset, disjoint_sdiff_self_right, le_of_eq hpad.2.2.2.symm⟩
  refine ⟨hvp, hplen_le, ?_⟩
  have hrspec := routeOrCut_isMatchingPlayer.spec G X pairs cfg.Δ cfg.L 100 z
    hX hGloop hcfg.hΔ_pos hdegG hcfg.hL hXL (by decide) hvp
  cases hrt : routeOrCut G X pairs cfg.Δ cfg.L 100 z with
  | cut U => rw [hrt] at hrspec; exact hrspec
  | matched matchings emb =>
    rw [hrt] at hrspec
    dsimp only
    set rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩
    set newM : ℕ → List (ℕ × ℕ) := fun i =>
      match rpairs.findIdx? (fun ip => decide (ip.1 = i)) with
      | none => []
      | some idx =>
          let p := pairs.getD idx (∅, ∅)
          let m := matchings.getD idx []
          m ++ completeMatchingFake p.1 p.2 m
    set st' : BlockGameState :=
      { active := fun i =>
          if i < k ∧ st.active i then
            match res i with | .expander _ => false | .cut _ => true
          else st.active i
        savedS := fun i =>
          if i < k ∧ st.active i then
            match res i with | .expander S => S | .cut _ => st.savedS i
          else st.savedS i
        numRounds := fun i =>
          if i < k ∧ st.active i then
            match res i with | .expander _ => st.numRounds i | .cut _ => st.numRounds i + 1
          else st.numRounds i
        rounds := fun i j =>
          if i < k ∧ st.active i then
            match res i with
            | .expander _ => st.rounds i j
            | .cut _ => if j = st.numRounds i then newM i else st.rounds i j
          else st.rounds i j
        calls := if pairs.isEmpty then st.calls else st.calls ++ [rc] }
    have hfindIdx_eq : ∀ idx (hidx : idx < rpairs.length),
        rpairs.findIdx? (fun ip => decide (ip.1 = (rpairs[idx]'hidx).1)) = some idx := by
      intro idx hidx
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨hidx, by simp, fun j hj => ?_⟩
      simp only [decide_eq_true_eq]
      intro heq
      have hne : j ≠ idx := Nat.ne_of_lt hj
      have h1 : (rpairs.map Prod.fst)[j]'(by simp; omega) = (rpairs[j]'(by omega)).1 := List.getElem_map _
      have h2 : (rpairs.map Prod.fst)[idx]'(by simp; omega) = (rpairs[idx]'hidx).1 := List.getElem_map _
      exact hne ((List.Nodup.getElem_inj_iff hids_nd).mp (by rw [h1, h2, heq]))
    have hnewM_at : ∀ idx (hidx : idx < rpairs.length),
        newM (rpairs[idx]'hidx).1 =
          matchings.getD idx [] ++
            completeMatchingFake (pairs[idx]'(by simp [pairs, hidx])).1
              (pairs[idx]'(by simp [pairs, hidx])).2 (matchings.getD idx []) := by
      intro idx hidx
      dsimp only [newM]
      rw [hfindIdx_eq idx hidx]
      simp only [List.getD_eq_getElem _ _ (show idx < pairs.length by simp [pairs, hidx])]
    have hnewM_spec : ∀ i < k, st.active i = true → ∀ U, res i = .cut U →
        let B := blockSet vs b i
        let C := smallerSide B U
        IsPerfectMatchingOn B (newM i) ∧
        (newM i).length = b / 2 ∧
        (∀ e ∈ newM i, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
        (∀ Y S : Finset ℕ, (Graph.mk G.n (newM i)).cutIn Y S ≤
          (Graph.mk G.n (rc.routed ++ rc.fake)).cutIn Y S) := by
      intro i hi hact U hsc
      dsimp only
      set B := blockSet vs b i
      set C := smallerSide B U
      set C' := padToHalf B C
      have hcs := hres i hi hact; rw [hsc] at hcs
      have hBcard : B.card = b := card_blockSet hnd hi
      have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
      have hpad := padToHalf_spec hsm.1 hsm.2.1 (by rw [hBcard]; exact hb_even)
      have hip_mem : (i, (C', B \ C')) ∈ rpairs := (hmem_rp i _).mpr ⟨hi, hact, U, hsc, rfl⟩
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hip_mem
      have hidx_p : idx < pairs.length := by simp [pairs, hidx]
      have hpair_eq : pairs[idx]'hidx_p = (C', B \ C') := by simp [pairs, hget]
      have hfst_eq : (rpairs[idx]'hidx).1 = i := by rw [hget]
      have hnew_eq : newM i = matchings.getD idx [] ++ completeMatchingFake C' (B \ C') (matchings.getD idx []) := by
        rw [← hfst_eq, hnewM_at idx hidx, hpair_eq]
      have hmspec := hrspec.2.1 idx hidx_p
      rw [hpair_eq] at hmspec
      set m := matchings.getD idx []
      set f := completeMatchingFake C' (B \ C') m
      have hcf := completeMatchingFake_spec (le_of_eq hpad.2.2.2.symm) hmspec.1 hmspec.2.1 hmspec.2.2
      have hlen_mf : (m ++ f).length = b / 2 := by
        rw [hcf.2.2.2.2.2.2.1, hpad.2.2.1, hBcard]
      have hpm_B : IsPerfectMatchingOn B (m ++ f) :=
        isPerfectMatchingOn_complete disjoint_sdiff_self_right (Finset.union_sdiff_of_subset hpad.2.1)
          hpad.2.2.2.symm hmspec.1 hmspec.2.1 hmspec.2.2
      have hcross : ∀ e ∈ m ++ f, ¬ (e.1 ∈ C ∧ e.2 ∈ C) := by
        intro e he ⟨_, h2⟩
        have h12 : e.1 ∈ C' ∧ e.2 ∈ B \ C' := by
          rcases List.mem_append.mp he with h | h
          · exact hmspec.1 e h
          · exact hcf.2.1 e h
        exact (Finset.mem_sdiff.mp h12.2).2 (hpad.1 h2)
      have hcut_rc : ∀ Y S : Finset ℕ, (Graph.mk G.n (m ++ f)).cutIn Y S ≤
          (Graph.mk G.n (rc.routed ++ rc.fake)).cutIn Y S := by
        intro Y S
        rw [cutIn_append, cutIn_append]
        have hidx_m : idx < matchings.length := by rw [hrspec.1]; exact hidx_p
        have hm_in : m ∈ matchings := by
          dsimp only [m]; rw [List.getD_eq_getElem _ _ hidx_m]; exact List.getElem_mem hidx_m
        have hf_in : f ∈ List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings := by
          have hidx_z : idx < (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings).length := by
            simp [hidx_p, hidx_m]
          have hget_z : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings)[idx]'hidx_z = f := by
            rw [List.getElem_zipWith, hpair_eq]
            dsimp only [f, m]; rw [List.getD_eq_getElem _ _ hidx_m]
          rw [← hget_z]; exact List.getElem_mem hidx_z
        exact Nat.add_le_add (cutIn_le_flatten G.n hm_in Y S) (cutIn_le_flatten G.n hf_in Y S)
      rw [hnew_eq]
      exact ⟨hpm_B, hlen_mf, hcross, hcut_rc⟩
    have hrounds_lt : ∀ i j, j < st.numRounds i → st'.rounds i j = st.rounds i j := by
      intro i j hj
      dsimp only [st']
      by_cases hcond : i < k ∧ st.active i = true
      · simp only [hcond, and_self, ↓reduceIte]
        cases res i with
        | expander _ => rfl
        | cut _ => simp [Nat.ne_of_lt hj]
      · simp [hcond]
    have hw_eq : ∀ i m, m ≤ st.numRounds i →
        witnessEdges (st'.rounds i) m = witnessEdges (st.rounds i) m := fun i m hm =>
      witnessEdges_congr_lt fun j hj => hrounds_lt i j (lt_of_lt_of_le hj hm)
    have hrc_valid : rc.Valid G X (routeCong cfg.Δ 100 cfg.L) z :=
      routedCall_valid_of_matched hvp hrspec
    refine ⟨?_, hnewM_at⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [st']; split_ifs
      · exact Nat.le_succ_of_le hinv.calls_len
      · rw [List.length_append, List.length_singleton]; have := hinv.calls_len; omega
    · intro c hc; dsimp only [st'] at hc; split_ifs at hc
      · exact hinv.calls_valid c hc
      · rcases List.mem_append.mp hc with h1 | h2
        · exact hinv.calls_valid c h1
        · rw [List.mem_singleton.mp h2]; exact hrc_valid
    · intro i hi; dsimp only [st']
      by_cases hact : st.active i = true
      · simp only [hi, hact, and_self, ↓reduceIte]
        cases res i with
        | expander _ => exact Nat.le_succ_of_le (hinv.numRounds_le i hi)
        | cut _ => exact Nat.add_le_add_right (hinv.numRounds_le i hi) 1
      · simp [hi, hact]; exact Nat.le_succ_of_le (hinv.numRounds_le i hi)
    · intro i hi hact'; dsimp only [st'] at hact' ⊢
      by_cases hact : st.active i = true
      · simp only [hi, hact, and_self, ↓reduceIte] at hact' ⊢
        cases hsc : res i with
        | expander _ => simp [hsc] at hact'
        | cut _ => rw [hinv.active_numRounds i hi hact]
      · simp [hi, hact] at hact'
    · intro i hi j hj; dsimp only [st'] at hj
      by_cases hact : st.active i = true
      · simp only [hi, hact, and_self, ↓reduceIte] at hj
        cases hsc : res i with
        | expander _ =>
          simp only [hsc] at hj; rw [hrounds_lt i j hj]; exact hinv.rounds_pm i hi j hj
        | cut U =>
          simp only [hsc] at hj
          by_cases hjeq : j = st.numRounds i
          · subst hjeq
            have hr : st'.rounds i (st.numRounds i) = newM i := by dsimp only [st']; simp [hi, hact, hsc]
            rw [hr]; exact (hnewM_spec i hi hact U hsc).1
          · rw [hrounds_lt i j (by omega)]; exact hinv.rounds_pm i hi j (by omega)
      · simp only [hi, hact] at hj
        rw [hrounds_lt i j hj]; exact hinv.rounds_pm i hi j hj
    · intro i hi j hj; dsimp only [st'] at hj
      by_cases hact : st.active i = true
      · simp only [hi, hact, and_self, ↓reduceIte] at hj
        cases hsc : res i with
        | expander _ =>
          simp only [hsc] at hj; rw [hrounds_lt i j hj]; exact hinv.rounds_len i hi j hj
        | cut U =>
          simp only [hsc] at hj
          by_cases hjeq : j = st.numRounds i
          · subst hjeq
            have hr : st'.rounds i (st.numRounds i) = newM i := by dsimp only [st']; simp [hi, hact, hsc]
            rw [hr]; exact (hnewM_spec i hi hact U hsc).2.1
          · rw [hrounds_lt i j (by omega)]; exact hinv.rounds_len i hi j (by omega)
      · simp only [hi, hact] at hj
        rw [hrounds_lt i j hj]; exact hinv.rounds_len i hi j hj
    · intro i hi j hj; dsimp only [st'] at hj
      by_cases hact : st.active i = true
      · simp only [hi, hact, and_self, ↓reduceIte] at hj
        cases hsc : res i with
        | expander _ =>
          simp only [hsc] at hj
          rw [hw_eq i j (le_of_lt hj), hrounds_lt i j hj]
          exact hinv.rounds_cut i hi j hj
        | cut U =>
          simp only [hsc] at hj
          rw [hw_eq i j (by omega)]
          by_cases hjeq : j = st.numRounds i
          · subst hjeq
            have hr : st'.rounds i (st.numRounds i) = newM i := by dsimp only [st']; simp [hi, hact, hsc]
            rw [hr]
            have hcs := hres i hi hact; rw [hsc] at hcs
            have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
            exact ⟨smallerSide (blockSet vs b i) U, hsm.1, hsm.2.2.1,
              (hnewM_spec i hi hact U hsc).2.2.1, hsm.2.2.2⟩
          · rw [hrounds_lt i j (by omega)]; exact hinv.rounds_cut i hi j (by omega)
      · simp only [hi, hact] at hj
        rw [hw_eq i j (le_of_lt hj), hrounds_lt i j hj]
        exact hinv.rounds_cut i hi j hj
    · intro i hi hact'
      by_cases hact : st.active i = true
      · dsimp only [st'] at hact' ⊢
        simp only [hi, hact, and_self, ↓reduceIte] at hact' ⊢
        cases hsc : res i with
        | cut _ => simp [hsc] at hact'
        | expander S =>
          dsimp only
          have hcs := hres i hi hact; rw [hsc] at hcs; exact hcs
      · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
        dsimp only [st']
        simp only [hi, hactf, Bool.false_eq_true, and_false, ↓reduceIte]
        exact hinv.inactive_exp i hi hactf
    · intro i hi Y S
      by_cases hemp : pairs.isEmpty = true
      · have hno_cut : ∀ j < k, st.active j = true → ∀ U, res j ≠ .cut U := by
          intro j hj hact U hsc
          have hip : (j, (padToHalf (blockSet vs b j) (smallerSide (blockSet vs b j) U),
              blockSet vs b j \ padToHalf (blockSet vs b j) (smallerSide (blockSet vs b j) U))) ∈ rpairs :=
            (hmem_rp j _).mpr ⟨hj, hact, U, hsc, rfl⟩
          have hne : pairs ≠ [] := by
            intro hnil; have hlen0 : rpairs.length = 0 := by simpa [pairs] using congrArg List.length hnil
            exact List.not_mem_nil (List.eq_nil_of_length_eq_zero hlen0 ▸ hip)
          simp [List.isEmpty_iff.mp hemp] at hne
        have hcalls_eq : st'.calls = st.calls := by dsimp only [st']; simp [hemp]
        have hnr_eq : st'.numRounds i = st.numRounds i := by
          dsimp only [st']
          by_cases hact : st.active i = true
          · simp only [hi, hact, and_self, ↓reduceIte]
            cases hsc : res i with
            | expander _ => rfl
            | cut U => exact absurd hsc (hno_cut i hi hact U)
          · simp [hi, hact]
        rw [hcalls_eq, hnr_eq, hw_eq i _ le_rfl]
        exact hinv.sub_cut i hi Y S
      · have hcalls_eq : st'.calls = st.calls ++ [rc] := by dsimp only [st']; simp [hemp]
        rw [hcalls_eq]
        have hcw : callsWitnessEdges (st.calls ++ [rc]) =
            callsWitnessEdges st.calls ++ (rc.routed ++ rc.fake) := by simp [callsWitnessEdges]
        rw [hcw, cutIn_append]
        by_cases hact : st.active i = true
        · cases hsc : res i with
          | expander _ =>
            have hnr_eq : st'.numRounds i = st.numRounds i := by dsimp only [st']; simp [hi, hact, hsc]
            rw [hnr_eq, hw_eq i _ le_rfl]
            exact le_trans (hinv.sub_cut i hi Y S) (Nat.le_add_right _ _)
          | cut U =>
            have hnr_eq : st'.numRounds i = st.numRounds i + 1 := by dsimp only [st']; simp [hi, hact, hsc]
            have hr_eq : st'.rounds i (st.numRounds i) = newM i := by dsimp only [st']; simp [hi, hact, hsc]
            rw [hnr_eq, witnessEdges, hw_eq i _ le_rfl, hr_eq, cutIn_append]
            exact Nat.add_le_add (hinv.sub_cut i hi Y S) ((hnewM_spec i hi hact U hsc).2.2.2 Y S)
        · have hnr_eq : st'.numRounds i = st.numRounds i := by dsimp only [st']; simp [hi, hact]
          rw [hnr_eq, hw_eq i _ le_rfl]
          exact le_trans (hinv.sub_cut i hi Y S) (Nat.le_add_right _ _)

/-! ## 4. Final Complement-Injection Lemma -/

/-- After `49 * cfg.L + 1` rounds, every block is inactive (by the round bound `round_bound_nat`) and the final combined
complement-injection call satisfies the Step B postcondition. -/
theorem sbModelInv_final_inj {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq2 : 2 ≤ q) (hqr : q ≤ r)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ} {st : BlockGameState}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X) (hb_pos : 0 < b)
    (hinv : SbModelInv cfg q G X vs b (numFullBlocks vs b) z (49 * cfg.L + 1) st) :
    let k := numFullBlocks vs b
    let injPairs := (List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)
    (∀ i < k, st.active i = false) ∧
    ValidTerminalPairs X injPairs ∧
    match routeOrCut G X injPairs cfg.Δ cfg.L 100 z with
    | .cut U => RouteCutSpec G X 100 z U
    | .matched matchings emb =>
        let callsB := st.calls ++ [⟨matchings.flatten, emb, completeBatchFake injPairs matchings⟩]
        callsB.length ≤ 49 * cfg.L + 2 ∧
        (∀ c ∈ callsB, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
        (∀ i < k, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
          (blockSet vs b i) (1 / (2 * (cfg.P (q - 1) : ℝ)))) := by
  intro k injPairs
  have hall_inactive : ∀ i < k, st.active i = false := by
    intro i hi
    by_contra hact
    have hactt : st.active i = true := Bool.eq_true_of_not_eq_false hact
    have hnr : st.numRounds i = 49 * cfg.L + 1 := hinv.active_numRounds i hi hactt
    have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
    have hBne : (blockSet vs b i).Nonempty := Finset.card_pos.mp (by rw [hBcard]; exact hb_pos)
    have hBL : (blockSet vs b i).card < 2 ^ cfg.L := by
      have hsub : blockSet vs b i ⊆ X := hvs ▸ blockSet_subset_toFinset vs b i
      exact lt_of_le_of_lt (Finset.card_le_card hsub) hXL
    have hlt := round_bound_nat hBne hBL
      (fun j hj => hinv.rounds_pm i hi j (hnr.symm ▸ hj))
      (fun j hj => hinv.rounds_cut i hi j (hnr.symm ▸ hj))
    omega
  have hinj_valid : ValidTerminalPairs X injPairs := by
    rw [← hvs]
    let rpairs := (List.range k).map fun i => (i, (blockSet vs b i \ st.savedS i, st.savedS i))
    have hmap : injPairs = rpairs.map Prod.snd := by simp [injPairs, rpairs]
    rw [hmap]
    refine validTerminalPairs_of_distinct_blocks hnd hb_pos ?_ ?_
    · have hfst : rpairs.map Prod.fst = List.range k := by simp [rpairs, Function.comp_def]
      rw [hfst]; exact List.nodup_range
    · intro ip hip
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hip
      have hik : i < k := List.mem_range.mp hi
      obtain ⟨hSsub, hS2, _⟩ := hinv.inactive_exp i hik (hall_inactive i hik)
      have hsd : (blockSet vs b i \ st.savedS i).card + (st.savedS i).card =
          (blockSet vs b i).card := Finset.card_sdiff_add_card_eq_card hSsub
      exact ⟨hik, Finset.sdiff_subset, hSsub, disjoint_sdiff_self_left, by dsimp only; omega⟩
  refine ⟨hall_inactive, hinj_valid, ?_⟩
  have hrspec := routeOrCut_isMatchingPlayer.spec G X injPairs cfg.Δ cfg.L 100 z
    hX hGloop hcfg.hΔ_pos hdegG hcfg.hL hXL (by decide) hinj_valid
  cases hrt : routeOrCut G X injPairs cfg.Δ cfg.L 100 z with
  | cut U => rw [hrt] at hrspec; exact hrspec
  | matched matchings emb =>
    rw [hrt] at hrspec
    dsimp only
    set rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake injPairs matchings⟩
    have hrc_valid : rc.Valid G X (routeCong cfg.Δ 100 cfg.L) z :=
      routedCall_valid_of_matched hinj_valid hrspec
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton]; have := hinv.calls_len; omega
    · intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · exact hinv.calls_valid c h1
      · rw [List.mem_singleton.mp h2]; exact hrc_valid
    · intro i hi
      obtain ⟨hSsub, hS2, hSexp⟩ := hinv.inactive_exp i hi (hall_inactive i hi)
      have hSexp_st : (Graph.mk G.n (callsWitnessEdges st.calls)).IsExpansionExpanderOn
          (st.savedS i) (1 / (cfg.P (q - 1) : ℝ)) := by
        intro T hTS hne hneS
        have h1 := hSexp T hTS hne hneS
        have hcut1 : ((Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).cutIn
            (st.savedS i) T : ℝ) ≤
            ((Graph.mk G.n (callsWitnessEdges st.calls)).cutIn (st.savedS i) T : ℝ) := by
          exact_mod_cast hinv.sub_cut i hi (st.savedS i) T
        linarith
      have hi_inj : i < injPairs.length := by simp [injPairs, hi]
      have hmspec := hrspec.2.1 i hi_inj
      have hp_eq : injPairs[i]'hi_inj = (blockSet vs b i \ st.savedS i, st.savedS i) := by
        simp [injPairs]
      rw [hp_eq] at hmspec
      dsimp only at hmspec
      set m := matchings.getD i []
      set f := completeMatchingFake (blockSet vs b i \ st.savedS i) (st.savedS i) m
      have hsd : (blockSet vs b i \ st.savedS i).card + (st.savedS i).card =
          (blockSet vs b i).card := Finset.card_sdiff_add_card_eq_card hSsub
      have hcf := completeMatchingFake_spec (by omega) hmspec.1 hmspec.2.1 hmspec.2.2
      have hPpos : (0 : ℝ) < cfg.P (q - 1) := Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
      have hβ0 : 0 ≤ 1 / (cfg.P (q - 1) : ℝ) := by positivity
      have hβ1 : 1 / (cfg.P (q - 1) : ℝ) ≤ 1 := by
        rw [div_le_one hPpos]; exact_mod_cast hcfg.hP_pos (by omega)
      have hinj_exp := isExpansionExpanderOn_of_injection (E := callsWitnessEdges st.calls)
        (M := m ++ f) hβ0 hβ1 hSsub hSexp_st
        (fun e he => by
          have h12 : e.1 ∈ blockSet vs b i \ st.savedS i ∧ e.2 ∈ st.savedS i := by
            rcases List.mem_append.mp he with h | h
            · exact hmspec.1 e h
            · exact hcf.2.1 e h
          exact ⟨(Finset.mem_sdiff.mp h12.1).1, (Finset.mem_sdiff.mp h12.1).2, h12.2⟩)
        hcf.2.2.2.2.2.1
        (fun v hvB hvS => hcf.2.2.2.2.2.2.2 v (Finset.mem_sdiff.mpr ⟨hvB, hvS⟩))
      have hdiv : 1 / (cfg.P (q - 1) : ℝ) / 2 = 1 / (2 * (cfg.P (q - 1) : ℝ)) := by ring
      rw [hdiv] at hinj_exp
      intro T hTB hne hneB
      have h1 := hinj_exp T hTB hne hneB
      have hcw : callsWitnessEdges (st.calls ++ [rc]) =
          callsWitnessEdges st.calls ++ (rc.routed ++ rc.fake) := by simp [callsWitnessEdges]
      have hcut_le : (Graph.mk G.n (callsWitnessEdges st.calls ++ (m ++ f))).cutIn
          (blockSet vs b i) T ≤
          (Graph.mk G.n (callsWitnessEdges (st.calls ++ [rc]))).cutIn (blockSet vs b i) T := by
        rw [hcw, cutIn_append, cutIn_append, cutIn_append, cutIn_append]
        have hi_m : i < matchings.length := by rw [hrspec.1]; exact hi_inj
        have hm_in : m ∈ matchings := by
          dsimp only [m]; rw [List.getD_eq_getElem _ _ hi_m]; exact List.getElem_mem hi_m
        have hf_in : f ∈ List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) injPairs matchings := by
          have hi_z : i < (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) injPairs matchings).length := by
            simp [hi_inj, hi_m]
          have hget_z : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) injPairs matchings)[i]'hi_z = f := by
            rw [List.getElem_zipWith, hp_eq]
            dsimp only [f, m]; rw [List.getD_eq_getElem _ _ hi_m]
          rw [← hget_z]; exact List.getElem_mem hi_z
        have h1' : (Graph.mk G.n m).cutIn (blockSet vs b i) T ≤
            (Graph.mk G.n rc.routed).cutIn (blockSet vs b i) T :=
          cutIn_le_flatten G.n hm_in (blockSet vs b i) T
        have h2' : (Graph.mk G.n f).cutIn (blockSet vs b i) T ≤
            (Graph.mk G.n rc.fake).cutIn (blockSet vs b i) T :=
          cutIn_le_flatten G.n hf_in (blockSet vs b i) T
        omega
      have hcut_ler : ((Graph.mk G.n (callsWitnessEdges st.calls ++ (m ++ f))).cutIn
          (blockSet vs b i) T : ℝ) ≤
          ((Graph.mk G.n (callsWitnessEdges (st.calls ++ [rc]))).cutIn (blockSet vs b i) T : ℝ) := by
        exact_mod_cast hcut_le
      linarith

end MinCostFlow.ExpanderDecomp
