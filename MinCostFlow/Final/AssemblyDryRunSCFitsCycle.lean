module

public import MinCostFlow.Final.AssemblyDryRunSC
import MinCostFlow.Final.AssemblyDryRunSCFitsBounds
import MinCostFlow.Chain.LevelConnected
import MinCostFlow.LSF.Lemma54InitWith
import MinCostFlow.LSF.PathRoot
import MinCostFlow.LSF.Walks
import MinCostFlow.Final.RuntimeQualityBounds
import Mathlib.Tactic

/-!
# Cycle-graph and irrationality helpers for `AssemblyDryRunSCFitsCounterexample`

Provides the graph-theoretic and rationality lemmas used to disprove the unguarded
`DrySCInitBridgeHyps.hCoreLenFits`:

* `bigWordSource`, `bigWordSource_wordSize_ge`: zero-edge circulation whose word size covers any `K`.
* `cycleCirculation`, `cycleCirculation_hyps`, `cycleCirculation_augmented_edges`: directed
  `N`-cycle circulation whose augmented graph contains the `N` cycle edges `(e, (e + 1) % N)` at
  indices `0 .. N - 1`.
* `exists_large_cycle_N`, `dryWitnessUsed_sigma_lt_two_pow_k`: existence of `N ≥ 3` with
  `cfg.TP.σ cfg.P.k cfg.N₀ < 2 ^ k < N`.
* `cycle_tree_has_high_stretch_edge`: every spanning tree of the augmented `N`-cycle has a cycle
  edge of tree stretch at least `1 + M_star` when cycle edges have length `√2` and all other edges
  have length `M_star * √2`.
* `levelStretchBound_sqrt2_rat`: on positive-integer multiples of `√2`, every `levelStretchBound`
  is a positive rational number.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.IPM
  MinCostFlow.IPM.Machine MinCostFlow.SparseCore MinCostFlow.SparseCore.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Scaling MinCostFlow.MinRatio

/-! ## 1. Auxiliary source and cycle circulations -/

/-- A zero-edge circulation whose `n = 2 ^ K` forces `dryWordSize ≥ K`. -/
@[expose] def bigWordSource (K : ℕ) : Circulation where
  n := 2 ^ K
  m := 0
  tail := Fin.elim0
  head := Fin.elim0
  capacity := Fin.elim0
  cost := Fin.elim0

theorem bigWordSource_wordSize_ge (allocationCoefficient allocationDegree K : ℕ) :
    K ≤ dryWordSize dryWitnessUsed allocationCoefficient allocationDegree (bigWordSource K) := by
  dsimp only [dryWordSize, wordSize]
  have hmul : 1 ≤ scratchWordMultiplier 1
      (forestProgramsScratchDegree allocationCoefficient allocationDegree
        (concreteQualityLinearCoeff (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed))) := by
    unfold scratchWordMultiplier; omega
  have hsw : (bigWordSource K).solverWords = [2 ^ K, 0] := by
    simp [Circulation.solverWords, bigWordSource]
  rw [hsw]
  have hlog : K ≤ Nat.log 2 ([2 ^ K, 0].length + [2 ^ K, 0].foldr max 0 + 2) := by
    apply Nat.le_log_of_pow_le (by decide)
    simp only [List.length_cons, List.length_nil, List.foldr_cons, List.foldr_nil]
    omega
  calc K ≤ K + 1 := Nat.le_succ K
    _ ≤ Nat.log 2 ([2 ^ K, 0].length + [2 ^ K, 0].foldr max 0 + 2) + 1 := Nat.succ_le_succ hlog
    _ = 1 * (Nat.log 2 ([2 ^ K, 0].length + [2 ^ K, 0].foldr max 0 + 2) + 1) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hmul

/-- Directed `N`-cycle circulation with unit capacities and zero costs. -/
@[expose] def cycleCirculation (N : ℕ) (hN : 3 ≤ N) : Circulation where
  n := N
  m := N
  tail := fun e => e
  head := fun e => ⟨(e.val + 1) % N, Nat.mod_lt _ (by omega)⟩
  capacity := fun _ => 1
  cost := fun _ => 0

theorem cycleCirculation_hyps {N : ℕ} (hN : 3 ≤ N) :
    let J := cycleCirculation N hN
    J.n ≤ 2 * J.m + 1 ∧ 0 < J.m ∧ J.CostsBounded (J.m ^ 10) ∧
      ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  refine ⟨by dsimp [cycleCirculation]; omega, by dsimp [cycleCirculation]; omega, ?_, ?_⟩
  · intro e; simp [cycleCirculation]
  · intro e; exact ⟨le_rfl, Nat.one_le_pow 40 N (by omega)⟩

/-- Strict monotonicity of an order isomorphism `Fin n ≃o Fin n` forces it to be the identity. -/
private theorem orderIso_fin_self_val {n : ℕ} (f : Fin n ≃o Fin n) (i : Fin n) :
    (f i).val = i.val := by
  have hle : ∀ (g : Fin n ≃o Fin n) (k : ℕ) (hk : k < n), k ≤ (g ⟨k, hk⟩).val := by
    intro g k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have h1 : k ≤ (g ⟨k, hk'⟩).val := ih hk'
      have h2 : (g ⟨k, hk'⟩).val < (g ⟨k + 1, hk⟩).val :=
        g.strictMono (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
      omega
  have h1 : i.val ≤ (f i).val := hle f i.val i.isLt
  have h2 : (f i).val ≤ (f.symm (f i)).val := hle f.symm (f i).val (f i).isLt
  rw [f.symm_apply_apply] at h2
  exact le_antisymm h2 h1

/-- The first `N` edges of `namedInstance (solverConnectedAugmented (cycleCirculation N hN))`
are the `N` cycle edges `(e, (e + 1) % N)`. -/
theorem cycleCirculation_augmented_edges {N : ℕ} (hN : 3 ≤ N) :
    let J := cycleCirculation N hN
    let I := solverConnectedAugmented J
    let G := namedInstance I
    N ≤ I.m ∧ I.m ≤ 7 * N ∧ Finset.range N ⊆ G.E ∧
      ∀ e < N, G.tail e = e ∧ G.head e = (e + 1) % N := by
  intro J I G
  have hJ := cycleCirculation_hyps hN
  have hsz := solverConnectedAugmented_size J hJ.1 hJ.2.1 (fun e => (hJ.2.2.2 e).1)
  have hfree_eq : freeEdges J.toInstance = Finset.univ := by
    ext e
    simp only [freeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Circulation.toInstance_edge]
    simp [Circulation.inputEdge, J, cycleCirculation]
  have hfree_card_m : (freeEdges J.toInstance).card = J.toInstance.m := by
    rw [hfree_eq, Finset.card_univ, Fintype.card_fin]
  have hfree_card : (freeEdges J.toInstance).card = N := by
    rw [hfree_card_m, Circulation.toInstance_m]; rfl
  refine ⟨hsz.1, hsz.2, fun e he => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp he) hsz.1),
    fun e he => ?_⟩
  have heI : e < I.m := lt_of_lt_of_le he hsz.1
  have hEdge : I.edge ⟨e, heI⟩ =
      connectedInitialEdgeArray J.toInstance (solverPenalty J.m : ℤ)
        (arrayIndex (connectedInitialEdgeArray J.toInstance (solverPenalty J.m : ℤ))
          (initialDemands J.toInstance) ⟨e, heI⟩) :=
    instanceOfArrays_edge _ _ ⟨e, heI⟩
  have hIdxVal : (arrayIndex (connectedInitialEdgeArray J.toInstance (solverPenalty J.m : ℤ))
      (initialDemands J.toInstance) ⟨e, heI⟩).val = e := rfl
  have heFree : e < (freeEdges J.toInstance).card := hfree_card.symm ▸ he
  have hLeft1 : arrayIndex (connectedInitialEdgeArray J.toInstance (solverPenalty J.m : ℤ))
      (initialDemands J.toInstance) ⟨e, heI⟩ =
      Fin.castAdd ((zeroDeficitVertices J.toInstance).card + (zeroDeficitVertices J.toInstance).card)
        (Fin.castAdd (deficitVertices J.toInstance).card ⟨e, heFree⟩) := by
    apply Fin.ext; simp [hIdxVal]
  rw [hLeft1] at hEdge
  simp only [connectedInitialEdgeArray, initialEdgeArray, Fin.addCases_left, freeEdgeArray] at hEdge
  have hFreeVal : (freeIndex J.toInstance ⟨e, heFree⟩).1.val = e := by
    let e1 : Fin J.toInstance.m ≃o Fin (freeEdges J.toInstance).card :=
      Fin.castOrderIso hfree_card_m.symm
    let e2 : Fin (freeEdges J.toInstance).card ≃o (freeEdges J.toInstance : Set (Fin J.toInstance.m)) :=
      (freeEdges J.toInstance).orderIsoOfFin rfl
    let e3 : (freeEdges J.toInstance : Set (Fin J.toInstance.m)) ≃o Fin J.toInstance.m :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hfree_eq.symm ▸ Finset.mem_univ x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    let iso : Fin J.toInstance.m ≃o Fin J.toInstance.m := (e1.trans e2).trans e3
    have heM : e < J.toInstance.m := hfree_card_m ▸ heFree
    have hval := orderIso_fin_self_val iso ⟨e, heM⟩
    simpa [iso, e1, e2, e3, freeIndex] using hval
  have hEdgeVal : I.edge ⟨e, heI⟩ = J.inputEdge ⟨e, he⟩ := by
    rw [hEdge, Circulation.toInstance_edge]
    congr 1
    apply Fin.ext
    simpa [Circulation.inputIndex] using hFreeVal
  simp only [G, namedInstance, heI, ↓reduceDIte, hEdgeVal, Circulation.inputEdge, J, cycleCirculation]
  exact ⟨trivial, trivial⟩

/-! ## 2. Choosing `N` with `cfg.TP.σ cfg.P.k cfg.N₀ < 2 ^ k < N` -/

theorem exists_large_cycle_N :
    ∃ N : ℕ, ∃ hN : 3 ≤ N,
      let J := cycleCirculation N hN
      let I := solverConnectedAugmented J
      let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
      let A := concreteQualityBudgetWithLast dryWitnessUsed
      let k := cappedQualityExponent threshold A I.m
      (2 : ℝ) ^ k < (N : ℝ) := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  obtain ⟨B, hB1, hB⟩ := alg2TimeFactor_le_rpow (C := 65536 * ((A : ℝ) + 1)) (a := 47 / 48)
    (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  let N := max 3 (max threshold (Nat.ceil (7 * B ^ 2) + 1))
  have hN3 : 3 ≤ N := le_max_left _ _
  have hNth : threshold ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNB : Nat.ceil (7 * B ^ 2) + 1 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨N, hN3, ?_⟩
  dsimp only
  let J := cycleCirculation N hN3
  let I := solverConnectedAugmented J
  have hIm_ge : N ≤ I.m := (cycleCirculation_augmented_edges hN3).1
  have hIm_le : I.m ≤ 7 * N := (cycleCirculation_augmented_edges hN3).2.1
  have hCap_le : chainEdgeCap threshold I.m ≤ 7 * N := max_le hIm_le (by omega)
  have hCap1 : 1 ≤ chainEdgeCap threshold I.m :=
    le_trans (by omega : 1 ≤ 3) (hN3.trans (hIm_ge.trans (le_max_left _ _)))
  have hq := (integerQualityExponent_bounds A (chainEdgeCap threshold I.m)).2
  have htf := hB (chainEdgeCap threshold I.m) hCap1
  have h7B : 7 * B ^ 2 < (N : ℝ) := by
    have h1 : 7 * B ^ 2 ≤ (Nat.ceil (7 * B ^ 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (7 * B ^ 2) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNB
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h7N : (B * ((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 < (N : ℝ) ^ 2 := by
    have h1 : ((chainEdgeCap threshold I.m : ℕ) : ℝ) ≤ (7 * N : ℝ) := by exact_mod_cast hCap_le
    have h2 : (((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 =
        ((chainEdgeCap threshold I.m : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    calc (B * ((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2
        = B ^ 2 * (((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = B ^ 2 * ((chainEdgeCap threshold I.m : ℕ) : ℝ) := by rw [h2]
      _ ≤ B ^ 2 * (7 * (N : ℝ)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
      _ = (7 * B ^ 2) * (N : ℝ) := by ring
      _ < (N : ℝ) * (N : ℝ) := mul_lt_mul_of_pos_right h7B hNpos
      _ = (N : ℝ) ^ 2 := (sq _).symm
  have hlt : B * ((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ) < (N : ℝ) := by
    nlinarith [sq_nonneg (B * ((chainEdgeCap threshold I.m : ℕ) : ℝ) ^ (1 / 2 : ℝ) - (N : ℝ)),
      mul_nonneg (le_trans zero_le_one hB1) (Real.rpow_nonneg (Nat.cast_nonneg (chainEdgeCap threshold I.m)) (1 / 2 : ℝ))]
  change (2 : ℝ) ^ integerQualityExponent A (chainEdgeCap threshold I.m) < (N : ℝ)
  exact lt_of_le_of_lt (hq.trans htf) hlt

theorem dryWitnessUsed_sigma_lt_two_pow_k
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.TP.σ cfg.P.k cfg.N₀ < (2 : ℝ) ^ k := by
  intro I threshold A k cfg
  let V := solverPenalty J.m
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
      (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  obtain ⟨⟨hκ_pos, hKappa⟩, _⟩ :=
    dryWitnessUsed.specWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ N₀ α Ψ ε
      hM₀1 hThresh hN₀ hPsi hα
  have hAge : 15 + 5 * dryWitnessUsed.C_γ ≤ (A : ℝ) := Nat.le_ceil _
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A hAge M₀ hKappa
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  set σ_tot := alg2SigmaTotOwn cfg.TP cfg.LP cfg.P cfg.N₀
  set σ_mwu_max := alg2SigmaGame cfg.σ_mwu cfg.N₀
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hVcfg.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hσ_mwu_nn : 0 ≤ σ_mwu_max := le_max_left 0 _
  have hpow_ge1 : 1 ≤ (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d :=
    one_le_pow₀ (by nlinarith)
  have hd_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) := by
    have : (0 : ℝ) ≤ cfg.P.d := Nat.cast_nonneg _
    nlinarith
  have hσ_tot_nn : 0 ≤ σ_tot := by
    unfold σ_tot alg2SigmaTotOwn alg2SigmaTotAt
    exact le_trans zero_le_one ((hVcfg.hLP.1 _).trans (le_max_right _ _))
  have hdenom_ge : σ_tot + 1 ≤ (σ_tot + 1) *
      (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) := by
    have hprod_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by nlinarith
    nlinarith
  have hκ_pos' : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := hκ_pos
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hinv : 1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ (2 : ℝ) ^ k := by
    rw [div_le_iff₀ hκ_pos']
    have h1 := (div_le_iff₀ h2k_pos).mp hk_le_κ
    linarith
  have hκ_eq : alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ =
      1 / ((σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d)) := rfl
  rw [hκ_eq, one_div_one_div] at hinv
  have hσ_le : cfg.TP.σ cfg.P.k cfg.N₀ ≤ σ_tot := le_max_left _ _
  linarith

/-! ## 3. Forward cycle walks and high-stretch edge in any spanning tree -/

private def cycleFwdWalk (N start : ℕ) : ℕ → List (ℕ × Bool)
  | 0 => []
  | len + 1 => (start % N, true) :: cycleFwdWalk N (start + 1) len

private theorem cycleFwdWalk_length (N start len : ℕ) :
    (cycleFwdWalk N start len).length = len := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih => simp [cycleFwdWalk, ih]

private theorem cycleFwdWalk_isWalk {T : MGraph} {N : ℕ} (hN : 0 < N)
    (hEdge : ∀ e < N, e ∈ T.E → T.tail e = e ∧ T.head e = (e + 1) % N) :
    ∀ (len start : ℕ),
      (∀ j < len, (start + j) % N ∈ T.E) →
      T.IsWalk (start % N) ((start + len) % N) (cycleFwdWalk N start len) := by
  intro len
  induction len with
  | zero =>
    intro start _
    simp only [cycleFwdWalk, Nat.add_zero]
    exact .nil (start % N)
  | succ len ih =>
    intro start hmem
    have h0_lt : start % N < N := Nat.mod_lt _ hN
    have h0_mem : start % N ∈ T.E := by simpa using hmem 0 (Nat.succ_pos len)
    have h0_end := hEdge (start % N) h0_lt h0_mem
    have hsrc : T.src (start % N, true) = start % N := by
      simp [MGraph.src, h0_end.1]
    have hdst : T.dst (start % N, true) = (start + 1) % N := by
      simp [MGraph.dst, h0_end.2, Nat.add_mod]
    have htail : T.IsWalk ((start + 1) % N) ((start + (len + 1)) % N)
        (cycleFwdWalk N (start + 1) len) := by
      have h1 := ih (start + 1) (fun j hj => by
        rw [show start + 1 + j = start + (j + 1) by omega]
        exact hmem (j + 1) (Nat.succ_lt_succ hj))
      rwa [show start + 1 + len = start + (len + 1) by omega] at h1
    exact .cons h0_mem hsrc (hdst ▸ htail)

private theorem cycleFwdWalk_walkVertices {T : MGraph} {N : ℕ} (hN : 0 < N)
    (hEdge : ∀ e < N, e ∈ T.E → T.tail e = e ∧ T.head e = (e + 1) % N) :
    ∀ (len start : ℕ),
      (∀ j < len, (start + j) % N ∈ T.E) →
      T.walkVertices (start % N) (cycleFwdWalk N start len) =
        (List.range (len + 1)).map (fun j => (start + j) % N) := by
  intro len
  induction len with
  | zero => intro start _; simp [MGraph.walkVertices, cycleFwdWalk]
  | succ len ih =>
    intro start hmem
    have h0_lt : start % N < N := Nat.mod_lt _ hN
    have h0_mem : start % N ∈ T.E := by simpa using hmem 0 (Nat.succ_pos len)
    have h0_end := hEdge (start % N) h0_lt h0_mem
    have hdst : T.dst (start % N, true) = (start + 1) % N := by
      simp [MGraph.dst, h0_end.2, Nat.add_mod]
    have hih := ih (start + 1) (fun j hj => by
      rw [show start + 1 + j = start + (j + 1) by omega]
      exact hmem (j + 1) (Nat.succ_lt_succ hj))
    change start % N :: (T.dst (start % N, true) ::
        (cycleFwdWalk N (start + 1) len).map T.dst) = _
    rw [hdst]
    have hih' : (start + 1) % N :: (cycleFwdWalk N (start + 1) len).map T.dst =
        (List.range (len + 1)).map (fun j => (start + 1 + j) % N) := hih
    rw [hih']
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_def]
    congr 1; omega

private theorem cycleFwdWalk_isPath {T : MGraph} {N : ℕ} (hN : 0 < N)
    (hEdge : ∀ e < N, e ∈ T.E → T.tail e = e ∧ T.head e = (e + 1) % N)
    {len start : ℕ} (hlen : len < N)
    (hmem : ∀ j < len, (start + j) % N ∈ T.E) :
    T.IsPath (start % N) ((start + len) % N) (cycleFwdWalk N start len) := by
  refine ⟨cycleFwdWalk_isWalk hN hEdge len start hmem, ?_⟩
  rw [cycleFwdWalk_walkVertices hN hEdge len start hmem]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb hEq
  have ha' : a < N := lt_of_lt_of_le (List.mem_range.mp ha) hlen
  have hb' : b < N := lt_of_lt_of_le (List.mem_range.mp hb) hlen
  have hmeq : a ≡ b [MOD N] := Nat.ModEq.add_left_cancel' start hEq
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hmeq

theorem cycle_tree_has_high_stretch_edge
    {G T₀ : MGraph} {r₀ N M_star : ℕ} (hN : 3 ≤ N) (hM1 : 1 ≤ M_star) (hMN : M_star < N)
    (hG : G.IsValid) (hRan : Finset.range N ⊆ G.E)
    (hCyc : ∀ e < N, G.tail e = e ∧ G.head e = (e + 1) % N)
    (hT₀ : IsRootedTree T₀ r₀) (hTV : T₀.V = G.V)
    (hTG₀ : ∀ f ∈ T₀.E, f ∈ G.E → T₀.tail f = G.tail f ∧ T₀.head f = G.head f)
    (hTp₀ : ∀ e ∈ G.E, walkEdges (T₀.forestPath (G.tail e) (G.head e)) ⊆ G.E) :
    let ℓ₀ : ℕ → ℝ := fun e => if e < N then Real.sqrt 2 else (M_star : ℝ) * Real.sqrt 2
    ∃ e₀ < N, 1 + (M_star : ℝ) ≤ treeStretch G T₀ (safeLen G ℓ₀) e₀ := by
  classical
  intro ℓ₀
  have hTEdge : ∀ e < N, e ∈ T₀.E → T₀.tail e = e ∧ T₀.head e = (e + 1) % N := fun e he heT => by
    have h1 := hTG₀ e heT (hRan (Finset.mem_range.mpr he))
    rw [h1.1, h1.2]
    exact hCyc e he
  have hsq2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set S : Finset ℕ := T₀.E ∩ Finset.range N
  have hSsub : S ⊆ Finset.range N := Finset.inter_subset_right
  have hScard_le : S.card ≤ N := (Finset.card_le_card hSsub).trans (by simp)
  have hSneN : S.card ≠ N := by
    intro hcard
    have hSeq : S = Finset.range N := Finset.eq_of_subset_of_card_le hSsub (by simp [hcard])
    have hall : ∀ i < N, i ∈ T₀.E := fun i hi =>
      (Finset.mem_inter.mp (hSeq.symm ▸ Finset.mem_range.mpr hi)).1
    have hp1 : T₀.IsPath 0 (N - 1) (cycleFwdWalk N 0 (N - 1)) := by
      have h1 := cycleFwdWalk_isPath (T := T₀) (by omega : 0 < N) hTEdge (start := 0)
        (len := N - 1) (by omega) (fun j _ => hall _ (Nat.mod_lt _ (by omega)))
      simpa [Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)] using h1
    have hNm1_end := hTEdge (N - 1) (by omega) (hall (N - 1) (by omega))
    have hNm1_mod : (N - 1 + 1) % N = 0 := by rw [Nat.sub_add_cancel (by omega)]; exact Nat.mod_self N
    have hp2 : T₀.IsPath 0 (N - 1) [(N - 1, false)] := by
      refine ⟨.cons (hall (N - 1) (by omega))
          (by simp [MGraph.src, hNm1_end.2, hNm1_mod])
          (by simp [MGraph.dst, hNm1_end.1]; exact .nil _), ?_⟩
      simp [MGraph.walkVertices, MGraph.dst, hNm1_end.1]
      omega
    have hEq := (forestPath_eq_of_isPath hT₀.isForest hp1).symm.trans
      (forestPath_eq_of_isPath hT₀.isForest hp2)
    have hlen := congrArg List.length hEq
    rw [cycleFwdWalk_length] at hlen
    simp at hlen
    omega
  by_cases hcard : S.card = N - 1
  · have hSlt : S.card < (Finset.range N).card := by simp; omega
    obtain ⟨e₀, he₀R, he₀S⟩ := Finset.exists_mem_notMem_of_card_lt_card hSlt
    have he₀_lt : e₀ < N := Finset.mem_range.mp he₀R
    have hall : ∀ i < N, i ≠ e₀ → i ∈ T₀.E := by
      intro i hi hne
      have hsub : S ⊆ (Finset.range N).erase e₀ := fun x hx =>
        Finset.mem_erase.mpr ⟨fun h => he₀S (h ▸ hx), hSsub hx⟩
      have hEq : S = (Finset.range N).erase e₀ :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem he₀R, Finset.card_range, hcard])
      have hiS : i ∈ S := hEq.symm ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr hi⟩
      exact (Finset.mem_inter.mp hiS).1
    have hwalk_mem : ∀ j < N - 1, (e₀ + 1 + j) % N ∈ T₀.E := by
      intro j hj
      have hlt : (e₀ + 1 + j) % N < N := Nat.mod_lt _ (by omega)
      have hne : (e₀ + 1 + j) % N ≠ e₀ := by
        intro hEq
        have hmeq : e₀ + (1 + j) ≡ e₀ + 0 [MOD N] := by
          rw [Nat.ModEq, Nat.add_zero, Nat.mod_eq_of_lt he₀_lt]
          simpa [Nat.add_assoc] using hEq
        have h1 := Nat.ModEq.add_left_cancel' e₀ hmeq
        rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 + j < N), Nat.zero_mod] at h1
        omega
      exact hall _ hlt hne
    have hp_fwd : T₀.IsPath ((e₀ + 1) % N) e₀ (cycleFwdWalk N (e₀ + 1) (N - 1)) := by
      have h1 := cycleFwdWalk_isPath (T := T₀) (by omega : 0 < N) hTEdge (start := e₀ + 1)
        (len := N - 1) (by omega) hwalk_mem
      have hend : (e₀ + 1 + (N - 1)) % N = e₀ := by
        rw [show e₀ + 1 + (N - 1) = e₀ + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he₀_lt]
      rwa [hend] at h1
    have hp_rev : T₀.IsPath e₀ ((e₀ + 1) % N) (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1))) :=
      IsPath_walkRev hp_fwd
    have hfp : T₀.forestPath (G.tail e₀) (G.head e₀) = walkRev (cycleFwdWalk N (e₀ + 1) (N - 1)) := by
      rw [(hCyc e₀ he₀_lt).1, (hCyc e₀ he₀_lt).2]
      exact forestPath_eq_of_isPath hT₀.isForest hp_rev
    have hnd := isPath_nodup_edges hp_rev
    have hcard_we : (walkEdges (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1)))).card = N - 1 := by
      rw [walkEdges, List.toFinset_card_of_nodup hnd, List.length_map, walkRev,
        List.length_reverse, List.length_map, cycleFwdWalk_length]
    have hwe_lt : ∀ f ∈ walkEdges (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1))), f < N := by
      intro f hf
      rw [walkEdges_walkRev] at hf
      have hmem_l : f ∈ (cycleFwdWalk N (e₀ + 1) (N - 1)).map Prod.fst := List.mem_toFinset.mp hf
      suffices ∀ (len start : ℕ), f ∈ (cycleFwdWalk N start len).map Prod.fst → f < N from
        this (N - 1) (e₀ + 1) hmem_l
      intro len
      induction len with
      | zero => intro _ h; simp [cycleFwdWalk] at h
      | succ len ih =>
        intro start h
        simp only [cycleFwdWalk, List.map_cons, List.mem_cons] at h
        rcases h with rfl | hrest
        · exact Nat.mod_lt _ (by omega)
        · exact ih (start + 1) hrest
    refine ⟨e₀, he₀_lt, ?_⟩
    unfold treeStretch
    rw [hfp, walkLength_eq_sum_of_isPath (safeLen G ℓ₀) hp_rev]
    have hsum : ∑ f ∈ walkEdges (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1))), safeLen G ℓ₀ f =
        ((N - 1 : ℕ) : ℝ) * Real.sqrt 2 := by
      calc ∑ f ∈ walkEdges (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1))), safeLen G ℓ₀ f
          = ∑ _f ∈ walkEdges (walkRev (cycleFwdWalk N (e₀ + 1) (N - 1))), Real.sqrt 2 := by
            refine Finset.sum_congr rfl fun f hf => ?_
            have hflt := hwe_lt f hf
            rw [safeLen_eq_of_mem ℓ₀ (hRan (Finset.mem_range.mpr hflt))]
            simp [ℓ₀, hflt]
        _ = ((N - 1 : ℕ) : ℝ) * Real.sqrt 2 := by simp [hcard_we]
    have hℓe₀ : safeLen G ℓ₀ e₀ = Real.sqrt 2 := by
      rw [safeLen_eq_of_mem ℓ₀ (hRan he₀R)]; simp [ℓ₀, he₀_lt]
    rw [hsum, hℓe₀, mul_div_cancel_right₀ _ hsq2_pos.ne']
    have hMN' : (M_star : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : M_star ≤ N - 1)
    linarith
  · have hSlt : S.card < N - 1 := by omega
    let H_cyc : MGraph := { V := Finset.range N, E := S, tail := G.tail, head := G.head }
    have hHval : H_cyc.IsValid := by
      intro f hf
      have hfN : f < N := Finset.mem_range.mp (hSsub hf)
      have hc := hCyc f hfN
      exact ⟨Finset.mem_range.mpr (by rw [hc.1]; exact hfN),
        Finset.mem_range.mpr (by rw [hc.2]; exact Nat.mod_lt _ (by omega))⟩
    have hHnotConn : ¬ (∀ u ∈ H_cyc.V, ∀ v ∈ H_cyc.V, H_cyc.Connected u v) := by
      intro hconn
      have hle := Chain.connected_n_le_m_add_one hHval hconn
      have hHn : H_cyc.n = N := Finset.card_range N
      have hHm : H_cyc.m = S.card := rfl
      omega
    have hExistsDis : ∃ e₀ < N, ¬ H_cyc.Connected e₀ ((e₀ + 1) % N) := by
      by_contra hall
      push Not at hall
      have h0 : ∀ w < N, H_cyc.Connected 0 w := by
        intro w
        induction w with
        | zero => intro _; exact MGraph.connected_refl H_cyc 0
        | succ w ih =>
          intro hw
          have h1 := ih (by omega)
          have h2 := hall w (by omega)
          rw [Nat.mod_eq_of_lt hw] at h2
          exact MGraph.connected_trans h1 h2
      apply hHnotConn
      intro u hu v hv
      exact MGraph.connected_trans (MGraph.connected_symm (h0 u (Finset.mem_range.mp hu)))
        (h0 v (Finset.mem_range.mp hv))
    obtain ⟨e₀, he₀_lt, he₀_dis⟩ := hExistsDis
    have he₀G : e₀ ∈ G.E := hRan (Finset.mem_range.mpr he₀_lt)
    set p := T₀.forestPath (G.tail e₀) (G.head e₀)
    have hp_path : T₀.IsPath (G.tail e₀) (G.head e₀) p :=
      forestPath_isPath hT₀.isForest (hT₀.connected (hTV ▸ (hG e₀ he₀G).1) (hTV ▸ (hG e₀ he₀G).2))
    have hp_subG : walkEdges p ⊆ G.E := hTp₀ e₀ he₀G
    have hExistsStar : ∃ f ∈ walkEdges p, ¬ f < N := by
      by_contra hAllLt
      push Not at hAllLt
      have hWalkH : ∀ (u v : ℕ) (P : List (ℕ × Bool)),
          T₀.IsWalk u v P → (∀ f ∈ walkEdges P, f ∈ G.E ∧ f < N) → H_cyc.IsWalk u v P := by
        intro u v P hW hP
        induction hW with
        | nil w => exact .nil w
        | @cons u' v' x rest hxE hsrc _ ih =>
          have hxWE : x.1 ∈ walkEdges (x :: rest) := by simp [walkEdges]
          have hxG : x.1 ∈ G.E := (hP x.1 hxWE).1
          have hxN : x.1 < N := (hP x.1 hxWE).2
          have hxS : x.1 ∈ H_cyc.E := Finset.mem_inter.mpr ⟨hxE, Finset.mem_range.mpr hxN⟩
          have hxEnd := hTG₀ x.1 hxE hxG
          have hsrc' : H_cyc.src x = u' := by
            unfold MGraph.src at hsrc ⊢
            change (if x.2 then G.tail x.1 else G.head x.1) = u'
            rw [← hxEnd.1, ← hxEnd.2]; exact hsrc
          have hdst' : H_cyc.dst x = T₀.dst x := by
            unfold MGraph.dst
            change (if x.2 then G.head x.1 else G.tail x.1) = _
            rw [← hxEnd.1, ← hxEnd.2]
          refine .cons hxS hsrc' (hdst'.symm ▸ ih fun f hf => hP f ?_)
          simp only [walkEdges, List.mem_toFinset, List.mem_map, List.mem_cons] at hf ⊢
          rcases hf with ⟨a, ha, rfl⟩
          exact ⟨a, Or.inr ha, rfl⟩
      have hconn : H_cyc.Connected (G.tail e₀) (G.head e₀) :=
        ⟨p, hWalkH _ _ p hp_path.1 fun f hf => ⟨hp_subG hf, hAllLt f hf⟩⟩
      rw [(hCyc e₀ he₀_lt).1, (hCyc e₀ he₀_lt).2] at hconn
      exact he₀_dis hconn
    obtain ⟨f, hfWE, hfNotLt⟩ := hExistsStar
    have hfG : f ∈ G.E := hp_subG hfWE
    have hsafe_nn : ∀ g, 0 ≤ safeLen G ℓ₀ g := fun g => by
      unfold safeLen; split_ifs
      · dsimp only [ℓ₀]; split_ifs <;> positivity
      · exact le_rfl
    have hsum_ge : (M_star : ℝ) * Real.sqrt 2 ≤ ∑ g ∈ walkEdges p, safeLen G ℓ₀ g := by
      have hf_eq : safeLen G ℓ₀ f = (M_star : ℝ) * Real.sqrt 2 := by
        rw [safeLen_eq_of_mem ℓ₀ hfG]; simp [ℓ₀, hfNotLt]
      rw [← hf_eq]
      exact Finset.single_le_sum (fun g _ => hsafe_nn g) hfWE
    have hℓe₀ : safeLen G ℓ₀ e₀ = Real.sqrt 2 := by
      rw [safeLen_eq_of_mem ℓ₀ he₀G]; simp [ℓ₀, he₀_lt]
    refine ⟨e₀, he₀_lt, ?_⟩
    unfold treeStretch
    rw [walkLength_eq_sum_of_isPath (safeLen G ℓ₀) hp_path, hℓe₀]
    have hdiv : (M_star : ℝ) ≤ (∑ g ∈ walkEdges p, safeLen G ℓ₀ g) / Real.sqrt 2 := by
      rw [le_div_iff₀ hsq2_pos]; exact hsum_ge
    linarith

/-! ## 4. Rationality of `levelStretchBound` on `√2`-scaled lengths -/

private theorem walkLength_safeLen_sqrt2_rat {G F : MGraph} {c : ℕ → ℕ} (u v : ℕ) :
    let ℓ : ℕ → ℝ := fun e => (c e : ℝ) * Real.sqrt 2
    ∃ r : ℚ, 0 ≤ r ∧ walkLength (safeLen G ℓ) (F.forestPath u v) = (r : ℝ) * Real.sqrt 2 := by
  classical
  intro ℓ
  unfold MGraph.forestPath
  split_ifs with h
  · set p := Classical.choose h
    have hp : F.IsPath u v p := Classical.choose_spec h
    rw [walkLength_eq_sum_of_isPath (safeLen G ℓ) hp]
    refine ⟨∑ f ∈ walkEdges p, if f ∈ G.E then (c f : ℚ) else 0,
      Finset.sum_nonneg fun f _ => by split_ifs <;> positivity, ?_⟩
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold safeLen ℓ
    split_ifs <;> simp
  · exact ⟨0, le_rfl, by simp [walkLength, walkEdges]⟩

private theorem rootedForest_stretch_sqrt2_rat {G : MGraph} {c : ℕ → ℕ}
    (hc : ∀ f ∈ G.E, 0 < c f) (RF : RootedForest) {e : ℕ} (he : e ∈ G.E) :
    let ℓ : ℕ → ℝ := fun f => (c f : ℝ) * Real.sqrt 2
    ∃ r : ℚ, 0 < r ∧ RF.stretch G (safeLen G ℓ) e = (r : ℝ) := by
  intro ℓ
  have hsq2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hce : (0 : ℚ) < (c e : ℚ) := Nat.cast_pos.mpr (hc e he)
  have hsafe_e : safeLen G ℓ e = (c e : ℝ) * Real.sqrt 2 := safeLen_eq_of_mem ℓ he
  unfold RootedForest.stretch
  dsimp only
  rw [hsafe_e]
  split_ifs
  · obtain ⟨r, hr0, hr⟩ := walkLength_safeLen_sqrt2_rat (G := G) (F := RF.F) (c := c)
      (G.tail e) (G.head e)
    refine ⟨1 + r / (c e : ℚ), by positivity, ?_⟩
    rw [hr, mul_div_mul_right _ _ hsq2.ne']
    push_cast; rfl
  · obtain ⟨r1, hr10, hr1⟩ := walkLength_safeLen_sqrt2_rat (G := G) (F := RF.F) (c := c)
      (G.tail e) (RF.root (G.tail e))
    obtain ⟨r2, hr20, hr2⟩ := walkLength_safeLen_sqrt2_rat (G := G) (F := RF.F) (c := c)
      (G.head e) (RF.root (G.head e))
    refine ⟨1 + (r1 + r2) / (c e : ℚ), by positivity, ?_⟩
    rw [hr1, hr2, ← add_mul, mul_div_mul_right _ _ hsq2.ne']
    push_cast; rfl

theorem levelStretchBound_sqrt2_rat {G T₀ : MGraph} {r₀ : ℕ} {π : ℕ → ℕ}
    {c : ℕ → ℕ} (hc : ∀ f ∈ G.E, 0 < c f) {e : ℕ} (he : e ∈ G.E) :
    let ℓ : ℕ → ℝ := fun f => (c f : ℝ) * Real.sqrt 2
    ∃ r : ℚ, 0 < r ∧ levelStretchBound T₀ r₀ π G (safeLen G ℓ) e = (r : ℝ) := by
  intro ℓ
  unfold levelStretchBound
  dsimp only
  set D := (Nat.log 2 T₀.V.card + 1) * (Nat.log 2 T₀.V.card + 2)
  have hex : ∀ i ∈ Finset.range (D + 1), ∃ r : ℚ, 0 < r ∧
      (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e = (r : ℝ) :=
    fun i _ => rootedForest_stretch_sqrt2_rat hc _ he
  classical
  choose rf hrf using hex
  refine ⟨2 * ∑ i ∈ Finset.range (D + 1), if hi : i ∈ Finset.range (D + 1) then rf i hi else 0, ?_, ?_⟩
  · have hsum_pos : (0 : ℚ) < ∑ i ∈ Finset.range (D + 1),
        if hi : i ∈ Finset.range (D + 1) then rf i hi else 0 := by
      refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos D)⟩
      simp only [hi, ↓reduceDIte]
      exact (hrf i hi).1
    linarith
  · push_cast
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hi, ↓reduceDIte]
    exact (hrf i hi).2

end MinCostFlow.Final.DryRun
