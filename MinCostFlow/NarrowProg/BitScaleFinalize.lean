module

public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Narrow.BitScalingModel
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.PositiveCapacities
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.NarrowProg.AccNormalize
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 2 accumulator finalization and Stage 2 helpers (`bitScaleFinalize`, `max2`)

Normalizes the lazy base-`2 ^ k` positive and negative accumulators for all `m` edges using
`accNormalize` and subtracts them with `limbsSub` into the output flow limb array `pFlow`,
and provides the pure helper lemmas and `max2` used by `BitScale.lean`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Stage 2 space bound and pure mathematical helpers -/

/-- Total heap words consumed by `bitScale` on instance `I` with limb width `k` and solver
space function `S`. -/
def bitScaleSpace (I : Circulation) (k : ℕ) (S : ℕ → ℕ → ℕ) : ℕ :=
  let T := bitScalingPhases I
  5 + 2 * I.m + 3 * I.m * (T / k + 2) + T * (2 + 12 * I.m + S (I.n + 1) (2 * I.m))

private theorem foldr_max_le_iff (l : List ℕ) (M : ℕ) :
    l.foldr max 0 ≤ M ↔ ∀ x ∈ l, x ≤ M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

/-- The maximum limb value of `capLimbs` equals `circMaxCapacity I`. -/
theorem maxLimbsVal_eq_circMaxCapacity {I : Circulation} {k : ℕ} {capLimbs : List (List ℕ)}
    (hlen : capLimbs.length = I.m)
    (hcaps : ∀ j (hj : j < I.m), Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) :
    maxLimbsVal k capLimbs = circMaxCapacity I := by
  unfold maxLimbsVal circMaxCapacity
  apply le_antisymm
  · rw [foldr_max_le_iff]
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hj' : j < I.m := by omega
    have hval := hcaps j hj'
    rw [List.getD_eq_getElem _ _ hj] at hval
    rw [hval]
    exact Finset.le_sup (f := I.capacity) (Finset.mem_univ (⟨j, hj'⟩ : Fin I.m))
  · refine Finset.sup_le fun e _ => ?_
    have hj : e.val < capLimbs.length := by omega
    have hmem : Nat.ofDigits (2 ^ k) (capLimbs[e.val]'hj) ∈
        capLimbs.map (Nat.ofDigits (2 ^ k)) :=
      List.mem_map.mpr ⟨capLimbs[e.val]'hj, List.getElem_mem hj, rfl⟩
    have hval := hcaps e.val e.isLt
    rw [List.getD_eq_getElem _ _ hj] at hval
    rw [← hval]
    exact (foldr_max_le_iff _ _).mp le_rfl _ hmem

/-- `Nat.size (maxTopLimb capLimbs) ≤ bitScalingPhases I`, avoiding any `k` overhead when `k > T`. -/
theorem size_maxTopLimb_le_bitScalingPhases {I : Circulation} {k w : ℕ}
    {capLimbs : List (List ℕ)}
    (hk : 1 ≤ k) (hlen : capLimbs.length = I.m)
    (hC : ∀ l ∈ capLimbs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w)
    (hcaps : ∀ j (hj : j < I.m), Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) :
    Nat.size (maxTopLimb capLimbs) ≤ bitScalingPhases I := by
  obtain ⟨hsize, hz, _⟩ := bestPairPrefix_spec hk hC capLimbs.length le_rfl
  rw [List.take_length, maxLimbsVal_eq_circMaxCapacity hlen hcaps] at hsize
  unfold maxTopLimb bitScalingPhases
  rw [← hsize]
  unfold pairBitLength
  split_ifs with h0
  · simp [hz h0]
  · omega

/-- Splitting `m * L` free zero words into `m` contiguous `L`-word zero arrays. -/
theorem free_mul_eq_prod (base m L : ℕ) :
    Assn.free base (m * L) =
      ∏ j ∈ Finset.range m, Assn.list (base + j * L) (List.replicate L 0) := by
  induction m with
  | zero => simp [Assn.free]
  | succ m ih =>
    rw [Nat.succ_mul, Assn.free_add', Finset.prod_range_succ, ih, Assn.free]

/-- Positive final capped residual/flow entries agree with positive residual capacities of `I`. -/
theorem residual_pos_iff_of_capped (I : Circulation) (T : ℕ) (g : Fin I.m → ℤ) (e : Fin I.m) :
    (0 < cappedResidual I T T g (I.m + 1) e ↔
      0 < (I.residual g).capacity (Fin.castAdd I.m e)) ∧
    (0 < cappedFlow g (I.m + 1) e ↔
      0 < (I.residual g).capacity (Fin.natAdd I.m e)) := by
  simp only [cappedResidual, cappedFlow, phaseResidual, Nat.sub_self, pow_zero,
    Nat.div_one, Fin.addCases_left, Fin.addCases_right]
  omega

/-- Every accumulator value at the end of `T` phases fits strictly below `(2 ^ k) ^ (T / k + 2)`. -/
theorem bitScale_acc_lt_pow_L {k T m : ℕ} (hk : 1 ≤ k) (hm : m + 1 < 2 ^ k) :
    (m + 1) * (2 ^ T - 1) < (2 ^ k) ^ (T / k + 2) := by
  have h1 : (m + 1) * (2 ^ T - 1) ≤ (m + 1) * 2 ^ T :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : (m + 1) * 2 ^ T < 2 ^ k * 2 ^ T :=
    Nat.mul_lt_mul_of_pos_right hm (by positivity)
  have hdiv : k * (T / k) + T % k = T := Nat.div_add_mod T k
  have hmod : T % k < k := Nat.mod_lt T (by omega)
  have hexp : k + T ≤ k * (T / k + 2) := by nlinarith
  have h3 : 2 ^ k * 2 ^ T ≤ (2 ^ k) ^ (T / k + 2) := by
    rw [← pow_add, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hexp
  omega

/-- All solver-contract preconditions for `J = (bitScalePhaseInstance I T t g).positiveInstance`. -/
theorem positivePhase_solver_pre {I : Circulation} {w T t : ℕ} {g : Fin I.m → ℤ}
    (hn : I.n + 1 < 2 ^ w) (hm : 5 * I.m + 9 < 2 ^ w)
    (hcostB : I.CostsBounded ((2 * I.m) ^ 10))
    (hcostW : ∀ e, (I.cost e).natAbs < 2 ^ w) :
    let J := (bitScalePhaseInstance I T t g).positiveInstance
    J.n = I.n + 1 ∧ J.m = 2 * I.m ∧ J.solverWords.length = 2 + 10 * I.m ∧
      (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ J.CostsBounded (J.m ^ 10) ∧
      (∀ a, 1 ≤ J.capacity a ∧ J.capacity a ≤ J.m ^ 40) := by
  intro J
  have hJn : J.n = I.n + 1 := rfl
  have hJm : J.m = 2 * I.m := by
    change I.m + I.m = 2 * I.m; omega
  have hJlen : J.solverWords.length = 2 + 10 * I.m := by
    rw [J.solverWords_length, hJm]; omega
  have hJcost : J.CostsBounded (J.m ^ 10) := by
    intro a
    rw [hJm]
    dsimp only [J, Circulation.positiveInstance]
    split_ifs
    · simp
    · refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
      · simpa only [bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
          Fin.addCases_left] using hcostB e
      · simpa only [bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
          Fin.addCases_right, Int.natAbs_neg] using hcostB e
  have hJcap : ∀ a, 1 ≤ J.capacity a ∧ J.capacity a ≤ J.m ^ 40 := by
    intro a
    refine ⟨Circulation.positiveInstance_capacity_pos (bitScalePhaseInstance I T t g) a, ?_⟩
    have hm_pos : 1 ≤ I.m := by
      have ha := a.isLt
      change a.val < I.m + I.m at ha
      omega
    have hcap_le : J.capacity a ≤ I.m + 1 := by
      dsimp only [J, Circulation.positiveInstance]
      split_ifs
      · omega
      · exact Nat.min_le_right _ _
    have hle_Jm : I.m + 1 ≤ J.m := by omega
    have hJm_pow : J.m ≤ J.m ^ 40 := Nat.le_self_pow (by norm_num) J.m
    omega
  have hJwords : ∀ x ∈ J.solverWords, x < 2 ^ w := by
    intro x hx
    simp only [Circulation.solverWords, List.mem_cons, List.mem_flatMap,
      Circulation.solverEdgeWords, List.mem_finRange, true_and] at hx
    rcases hx with rfl | rfl | ⟨a, hx⟩
    · rw [hJn]; exact hn
    · rw [hJm]; omega
    · simp only [List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact lt_of_lt_of_le (J.tail a).isLt (by rw [hJn]; omega)
      · exact lt_of_lt_of_le (J.head a).isLt (by rw [hJn]; omega)
      · have hcap_le : J.capacity a ≤ I.m + 1 := by
          dsimp only [J, Circulation.positiveInstance]
          split_ifs
          · omega
          · exact Nat.min_le_right _ _
        omega
      · split_ifs <;> omega
      · dsimp only [J, Circulation.positiveInstance]
        split_ifs
        · simp
        · refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
          · simpa only [bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
              Fin.addCases_left] using hcostW e
          · simpa only [bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
              Fin.addCases_right, Int.natAbs_neg] using hcostW e
  exact ⟨hJn, hJm, hJlen, hJwords, hJcost, hJcap⟩

/-- Return `max a b`. -/
wram_def max2 (a, b) {
  if a < b {
    a := b
  }
  return a
}

/-- Specification of `max2`: returns `max a b`. -/
def max2Spec (w : ℕ) : Spec (ℕ × ℕ) where
  pre := fun (a, b) args => ⌜args = [a, b] ∧ 1 < 2 ^ w⌝
  post := fun (a, b) args v => ⌜args = [a, b] ∧ v = max a b⌝

theorem max2_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some max2) :
    Meets w p f ((max2Spec w).withCost fun _ _ => 20) := by
  sep_enter ⟨a, b⟩ with hw
  sep_run

/-! ### Accumulator finalization (`bitScaleFinalize`) -/

/-- Final normalized flow limbs for edge `e` produced by normalizing `posAcc e` and `negAcc e`
and subtracting with `limbsSub`. -/
def finalizedFlowLimbs {m : ℕ} (k : ℕ) (posAcc negAcc : Fin m → List ℕ) (e : Fin m) : List ℕ :=
  subLimbs k (normLimbs k (posAcc e)) (normLimbs k (negAcc e))

private theorem prod_list_le_gc (n : ℕ) (p : ℕ → ℕ) (xs : ℕ → List ℕ) :
    (∏ j ∈ Finset.range n, Assn.list (p j) (xs j)) ≤ Assn.gc := by
  induction n with
  | zero => simpa using Assn.one_le_gc
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have h1 : Assn.list (p n) (xs n) ≤ Assn.gc := Assn.noDebt_list _ _
    exact le_trans (Assn.mul_le_mul_of_le ih h1) (by rw [Assn.gc_mul_gc])

private def finPartial (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) (i j : ℕ) : List ℕ :=
  if h : j < m then (if j < i then newAcc ⟨j, h⟩ else oldAcc ⟨j, h⟩) else []

private theorem finPartial_zero (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) (j : ℕ) :
    finPartial m oldAcc newAcc 0 j = if h : j < m then oldAcc ⟨j, h⟩ else [] := by
  unfold finPartial; simp

private theorem finPartial_all (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) {j : ℕ} (hj : j < m) :
    finPartial m oldAcc newAcc m j = newAcc ⟨j, hj⟩ := by
  unfold finPartial; simp [hj]

private theorem list_finPartial_self {pBase L m i : ℕ} (oldAcc newAcc : Fin m → List ℕ)
    (hi : i < m) :
    Assn.list (pBase + i * L) (finPartial m oldAcc newAcc i i) =
    Assn.list (pBase + i * L) (oldAcc ⟨i, hi⟩) := by
  congr 1; unfold finPartial; simp [hi]

private theorem list_finPartial_succ {pBase L m i : ℕ} (oldAcc newAcc : Fin m → List ℕ)
    {xs : List ℕ} (hi : i < m) (hxs : xs = newAcc ⟨i, hi⟩) :
    Assn.list (pBase + i * L) xs =
    Assn.list (pBase + i * L) (finPartial m oldAcc newAcc (i + 1) i) := by
  congr 1; rw [hxs]; unfold finPartial; simp [hi]

private theorem finPartial_prod_erase_eq {pBase L m i : ℕ}
    (oldAcc newAcc : Fin m → List ℕ) :
    (∏ j ∈ (Finset.range m).erase i,
      Assn.list (pBase + j * L) (finPartial m oldAcc newAcc i j)) =
    (∏ j ∈ (Finset.range m).erase i,
      Assn.list (pBase + j * L) (finPartial m oldAcc newAcc (i + 1) j)) := by
  refine Finset.prod_congr rfl fun j hj => ?_
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  congr 1; unfold finPartial
  split_ifs <;> first | rfl | omega

/-- Named value for `bitScaleFinalizeSpec`. -/
structure BitScaleFinalizeData where
  m : ℕ
  k : ℕ
  L : ℕ
  g : Fin m → ℤ
  posAcc : Fin m → List ℕ
  negAcc : Fin m → List ℕ
  flowInit : Fin m → List ℕ

/-- Normalize `posAcc` and `negAcc` in place and write `posAcc - negAcc` into `pFlow` for all
`m` edges, each of length `L` limbs in base `2 ^ k`. -/
wram_def bitScaleFinalize (norm sub : ℕ) (pPosAcc, pNegAcc, pFlow, m, L, k) {
  off := 0
  for i in 0 .. m {
    r := norm(pPosAcc + off, L, k)
    r := norm(pNegAcc + off, L, k)
    r := sub(pPosAcc + off, pNegAcc + off, pFlow + off, L, k)
    off := off + L
  }
  return 0
}

/-- Specification of `bitScaleFinalize`: produces normalized `L`-limb base-`2 ^ k` representations
of the nonnegative integral flow `g` in `pFlow`. -/
def bitScaleFinalizeSpec (w : ℕ) : Spec BitScaleFinalizeData where
  pre d args := ⨆ (pPosAcc : ℕ) (pNegAcc : ℕ) (pFlow : ℕ),
    ⌜args = [pPosAcc, pNegAcc, pFlow, d.m, d.L, d.k] ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ 0 < d.L ∧ d.m * d.L < 2 ^ w ∧
      pPosAcc + d.m * d.L ≤ 2 ^ w ∧ pNegAcc + d.m * d.L ≤ 2 ^ w ∧ pFlow + d.m * d.L ≤ 2 ^ w ∧
      (∀ e : Fin d.m, (d.posAcc e).length = d.L ∧ (d.negAcc e).length = d.L ∧
        (d.flowInit e).length = d.L) ∧
      (∀ e : Fin d.m, (∀ x ∈ d.posAcc e, x < 2 ^ (w - 1)) ∧
        (∀ x ∈ d.negAcc e, x < 2 ^ (w - 1))) ∧
      (∀ e : Fin d.m, Nat.ofDigits (2 ^ d.k) (d.posAcc e) < (2 ^ d.k) ^ d.L ∧
        Nat.ofDigits (2 ^ d.k) (d.negAcc e) < (2 ^ d.k) ^ d.L) ∧
      (∀ e : Fin d.m, 0 ≤ d.g e ∧
        ((Nat.ofDigits (2 ^ d.k) (d.posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ d.k) (d.negAcc e) : ℕ) : ℤ) = d.g e)⌝ *
    (∏ j ∈ Finset.range d.m,
      Assn.list (pPosAcc + j * d.L) (if h : j < d.m then d.posAcc ⟨j, h⟩ else [])) *
    (∏ j ∈ Finset.range d.m,
      Assn.list (pNegAcc + j * d.L) (if h : j < d.m then d.negAcc ⟨j, h⟩ else [])) *
    (∏ j ∈ Finset.range d.m,
      Assn.list (pFlow + j * d.L) (if h : j < d.m then d.flowInit ⟨j, h⟩ else []))
  post d args v := ⨆ (pPosAcc : ℕ) (pNegAcc : ℕ) (pFlow : ℕ),
    let flowLimbs := finalizedFlowLimbs d.k d.posAcc d.negAcc
    ⌜args = [pPosAcc, pNegAcc, pFlow, d.m, d.L, d.k] ∧ v = 0 ∧
      (∀ e : Fin d.m, Limbs d.k (flowLimbs e) ∧ (flowLimbs e).length = d.L ∧
        ((Nat.ofDigits (2 ^ d.k) (flowLimbs e) : ℕ) : ℤ) = d.g e)⌝ *
    (∏ j ∈ Finset.range d.m,
      Assn.list (pFlow + j * d.L) (if h : j < d.m then flowLimbs ⟨j, h⟩ else []))

/-- `bitScaleFinalize` runs in `(2 * Tnorm L + Tsub L + 60) * m + 40` steps. -/
theorem bitScaleFinalize_meets {w : ℕ} {p : Program} {f norm sub : ℕ} {Tnorm Tsub : ℕ → ℕ}
    (hp : p.procs[f]? = some (bitScaleFinalize norm sub))
    (hnorm : Meets w p norm ((accNormalizeSpec w).withCost fun x _ => Tnorm x.2.length))
    (hsub : Meets w p sub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length)) :
    Meets w p f ((bitScaleFinalizeSpec w).withCost fun d _ =>
      (2 * Tnorm d.L + Tsub d.L + 60) * d.m + 40) := by
  sep_enter ⟨m, k, L, g, posAcc, negAcc, flowInit⟩ with
    hk h2kw hL_pos hmL hpPos_fit hpNeg_fit hpFlow_fit hlen hlt_half hval_lt hg_diff
  have hkw : k < w := by omega
  generalize hposN_def : (fun e : Fin m => normLimbs k (posAcc e)) = posN
  generalize hnegN_def : (fun e : Fin m => normLimbs k (negAcc e)) = negN
  generalize hflowF_def : finalizedFlowLimbs k posAcc negAcc = flowF
  sep_step
  have hpos0 : (∏ j ∈ Finset.range m,
        Assn.list (pPosAcc + j * L) (if h : j < m then posAcc ⟨j, h⟩ else [])) =
      (∏ j ∈ Finset.range m, Assn.list (pPosAcc + j * L) (finPartial m posAcc posN 0 j)) := by
    refine Finset.prod_congr rfl fun j _ => by rw [finPartial_zero]
  have hneg0 : (∏ j ∈ Finset.range m,
        Assn.list (pNegAcc + j * L) (if h : j < m then negAcc ⟨j, h⟩ else [])) =
      (∏ j ∈ Finset.range m, Assn.list (pNegAcc + j * L) (finPartial m negAcc negN 0 j)) := by
    refine Finset.prod_congr rfl fun j _ => by rw [finPartial_zero]
  have hflow0 : (∏ j ∈ Finset.range m,
        Assn.list (pFlow + j * L) (if h : j < m then flowInit ⟨j, h⟩ else [])) =
      (∏ j ∈ Finset.range m, Assn.list (pFlow + j * L) (finPartial m flowInit flowF 0 j)) := by
    refine Finset.prod_congr rfl fun j _ => by rw [finPartial_zero]
  sep_apply hpos0
  sep_apply hneg0
  sep_apply hflow0
  sep_for (fun i (r0 : ℕ) =>
    ⟨[pPosAcc, pNegAcc, pFlow, m, L, k, i * L, i, r0],
      i ≤ m, (2 * Tnorm L + Tsub L + 45) * (m - i) + 10,
      [∏ j ∈ Finset.range m, Assn.list (pPosAcc + j * L) (finPartial m posAcc posN i j),
       ∏ j ∈ Finset.range m, Assn.list (pNegAcc + j * L) (finPartial m negAcc negN i j),
       ∏ j ∈ Finset.range m, Assn.list (pFlow + j * L) (finPartial m flowInit flowF i j)]⟩)
    with r0
  · set e : Fin m := ⟨i, hhi⟩
    have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hhi
    have hiL_lt : i * L < m * L := Nat.mul_lt_mul_of_pos_right hhi hL_pos
    have hpPos_lt : pPosAcc + i * L < 2 ^ w := by omega
    have hpNeg_lt : pNegAcc + i * L < 2 ^ w := by omega
    have hpFlow_lt : pFlow + i * L < 2 ^ w := by omega
    have hplen : (posAcc e).length = L := (hlen e).1
    have hnlen : (negAcc e).length = L := (hlen e).2.1
    have hflen : (flowInit e).length = L := (hlen e).2.2
    have hplt : ∀ x ∈ posAcc e, x < 2 ^ (w - 1) := (hlt_half e).1
    have hnlt : ∀ x ∈ negAcc e, x < 2 ^ (w - 1) := (hlt_half e).2
    -- Split out edge `i`
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pPosAcc + j * L) (finPartial m posAcc posN i j))
    sep_apply list_finPartial_self (pBase := pPosAcc) (L := L) posAcc posN hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pNegAcc + j * L) (finPartial m negAcc negN i j))
    sep_apply list_finPartial_self (pBase := pNegAcc) (L := L) negAcc negN hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pFlow + j * L) (finPartial m flowInit flowF i j))
    sep_apply list_finPartial_self (pBase := pFlow) (L := L) flowInit flowF hhi
    -- Normalize `posAcc e` and `negAcc e`
    sep_step from (k, posAcc e)
    sep_step from (k, negAcc e)
    have hpn_len : (normLimbs k (posAcc e)).length = L := by rw [length_normLimbs, hplen]
    have hnn_len : (normLimbs k (negAcc e)).length = L := by rw [length_normLimbs, hnlen]
    -- Subtract `posN e - negN e` into `flowF e`
    sep_step from (k, normLimbs k (posAcc e), normLimbs k (negAcc e), flowInit e)
    -- Re-join all three products
    have hpos_eq : normLimbs k (posAcc e) = posN e := by rw [← hposN_def]
    have hneg_eq : normLimbs k (negAcc e) = negN e := by rw [← hnegN_def]
    have hflow_eq : subLimbs k (normLimbs k (posAcc e)) (normLimbs k (negAcc e)) = flowF e := by
      rw [← hflowF_def]; rfl
    sep_apply list_finPartial_succ (pBase := pPosAcc) (L := L) posAcc posN hhi hpos_eq
    sep_apply finPartial_prod_erase_eq (pBase := pPosAcc) (L := L) (i := i) posAcc posN
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pPosAcc + j * L) (finPartial m posAcc posN (i + 1) j))).symm
    sep_apply list_finPartial_succ (pBase := pNegAcc) (L := L) negAcc negN hhi hneg_eq
    sep_apply finPartial_prod_erase_eq (pBase := pNegAcc) (L := L) (i := i) negAcc negN
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pNegAcc + j * L) (finPartial m negAcc negN (i + 1) j))).symm
    sep_apply list_finPartial_succ (pBase := pFlow) (L := L) flowInit flowF hhi hflow_eq
    sep_apply finPartial_prod_erase_eq (pBase := pFlow) (L := L) (i := i) flowInit flowF
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pFlow + j * L) (finPartial m flowInit flowF (i + 1) j))).symm
    have hoff_next : i * L + L = (i + 1) * L := by ring
    have hoff_lt : i * L + L < 2 ^ w := by
      rw [hoff_next]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right L (by omega : i + 1 ≤ m)) hmL
    sep_run
    rw [hplen, hnlen, hpn_len]; push_cast; linarith
  · have hflow_all : (∏ j ∈ Finset.range m,
          Assn.list (pFlow + j * L) (finPartial m flowInit flowF m j)) =
        (∏ j ∈ Finset.range m,
          Assn.list (pFlow + j * L) (if h : j < m then flowF ⟨j, h⟩ else [])) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < m := Finset.mem_range.mp hj
      simp only [finPartial_all m flowInit flowF hj', hj', ↓reduceDIte]
    sep_apply hflow_all
    subst hflowF_def
    have hpost : ∀ e : Fin m,
        Limbs k (finalizedFlowLimbs k posAcc negAcc e) ∧
        (finalizedFlowLimbs k posAcc negAcc e).length = L ∧
        ((Nat.ofDigits (2 ^ k) (finalizedFlowLimbs k posAcc negAcc e) : ℕ) : ℤ) = g e := by
      intro e
      have hplen : (posAcc e).length = L := (hlen e).1
      have hnlen : (negAcc e).length = L := (hlen e).2.1
      have hsub_eq := normLimbs_sub_eq hk
        (by rw [hplen, hnlen]) (hlt_half e).1 (hlt_half e).2
        (by rw [hplen]; exact (hval_lt e).1) (by rw [hnlen]; exact (hval_lt e).2)
        (by have := (hg_diff e).1; have := (hg_diff e).2; omega)
      have hpr := normRun_spec hk (hlt_half e).1 (posAcc e).length le_rfl
      have hnr := normRun_spec hk (hlt_half e).2 (negAcc e).length le_rfl
      have hsubr := subRun_spec hk hpr.2.2 hnr.2.2
        (by rw [length_carryRun, length_carryRun, hplen, hnlen])
        (normLimbs k (posAcc e)).length le_rfl
      have hL_flow : Limbs k (finalizedFlowLimbs k posAcc negAcc e) := hsubr.2.2
      have hlen_flow : (finalizedFlowLimbs k posAcc negAcc e).length = L := by
        unfold finalizedFlowLimbs subLimbs
        rw [length_carryRun, length_normLimbs, hplen]
      have hval_flow : ((Nat.ofDigits (2 ^ k) (finalizedFlowLimbs k posAcc negAcc e) : ℕ) : ℤ) =
          g e := by
        unfold finalizedFlowLimbs
        rw [hsub_eq.2]
        have := (hg_diff e).1; have := (hg_diff e).2; omega
      exact ⟨hL_flow, hlen_flow, hval_flow⟩
    sep_run
    calc $ ((2 * (Tnorm L : ℤ) + (Tsub L : ℤ) + 45) * ((m : ℤ) - (m : ℤ)) + 10 - 2) *
          ((∏ j ∈ Finset.range m, Assn.list (pPosAcc + j * L) (finPartial m posAcc posN m j)) *
            ∏ j ∈ Finset.range m, Assn.list (pNegAcc + j * L) (finPartial m negAcc negN m j))
        ≤ Assn.gc * (Assn.gc * Assn.gc) :=
          Assn.mul_le_mul_of_le (Assn.credits_le_gc (by omega))
            (Assn.mul_le_mul_of_le (prod_list_le_gc _ _ _) (prod_list_le_gc _ _ _))
      _ = Assn.gc := by rw [Assn.gc_mul_gc, Assn.gc_mul_gc]

/-- Concrete-cost corollary with `accNormalize` and `limbsSub`. -/
theorem bitScaleFinalize_meets_direct {w : ℕ} {p : Program} {f norm sub : ℕ}
    (hp : p.procs[f]? = some (bitScaleFinalize norm sub))
    (hnorm : p.procs[norm]? = some accNormalize)
    (hsub : p.procs[sub]? = some limbsSub) :
    Meets w p f ((bitScaleFinalizeSpec w).withCost fun d _ => (150 * d.L + 140) * d.m + 40) := by
  have h := bitScaleFinalize_meets (w := w)
    (Tnorm := fun n => 45 * n + 25) (Tsub := fun n => 60 * n + 30)
    hp (accNormalize_meets hnorm) (limbsSub_meets hsub)
  exact h.withCost_mono fun d _ => by nlinarith

end MinCostFlow.NarrowProg
