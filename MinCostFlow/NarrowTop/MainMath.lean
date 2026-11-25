module

public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0Read
public import MinCostFlow.NarrowProg.Stage0Check
public import MinCostFlow.NarrowProg.Stage0Shift
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage3Answer
public import MinCostFlow.Scaling.ReductionAlgorithm
public import MinCostFlow.Scaling.PositiveScatter
import MinCostFlow.Scaling.IsolatedDemands
import MinCostFlow.Scaling.ReductionCapacityBounds
import MinCostFlow.Narrow.OuterCirculation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Mathematical lemmas for `narrowMain`

Supplies the pure mathematical facts needed by `MinCostFlow/NarrowTop/Main.lean`:
- Compressed vertex bounds for the two pruned circulation calls:
  `feasibility_compress_n_le` (`≤ 2 * I.m + 1`) and `residual_compress_n_le` (`≤ 2 * I.m`).
- Dimension, capacity, and cost bounds for both pruned calls (`feasibility_pruned_bounds`,
  `residual_pruned_bounds`).
- Joint Stage 1 space bound `stage1CircSpace_sum_le` and total heap space bound
  `narrowMain_totalSpace_le` inside `narrowMainSpace I S`.
- Stage 1 width bounds from `NarrowMainFits` (`narrowMain_stage1_widths`).
- Reduction correctness for both the infeasible branch (`narrowMain_feas_infeasible`) and
  the optimal-flow branch (`narrowMain_stage3_correct`), proved via
  `Circulation.solvePruned_correct` and `FlowReduction.reduceToCirculation_correct_of_calls`.
-/

@[expose] public section

open MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowTop

/-! ### Compressed vertex counts of the two pruned calls -/

private theorem scan_count_eq_card {n : ℕ} (s : VertexLabels n) (vs : List (Fin n))
    (hs : s.count = (Finset.univ.filter fun v : Fin n => s.table v ≠ 0).card) :
    (s.scan vs).count = (Finset.univ.filter fun v : Fin n => (s.scan vs).table v ≠ 0).card := by
  induction vs generalizing s with
  | nil => exact hs
  | cons v vs ih =>
    apply ih (s.encounter v)
    unfold VertexLabels.encounter
    split_ifs with h0
    · have hfilt : (Finset.univ.filter fun u : Fin n =>
          Function.update s.table v (s.count + 1) u ≠ 0) =
          insert v (Finset.univ.filter fun u : Fin n => s.table u ≠ 0) := by
        ext u
        by_cases huv : u = v
        · subst huv; simp
        · simp [huv]
      have hnotmem : v ∉ Finset.univ.filter (fun u : Fin n => s.table u ≠ 0) := by
        simp [h0]
      rw [hfilt, Finset.card_insert_of_notMem hnotmem, hs]
    · exact hs

private theorem scan_table_ne_zero_mem {n : ℕ} (s : VertexLabels n) (vs : List (Fin n))
    (v : Fin n) (hv : (s.scan vs).table v ≠ 0) : s.table v ≠ 0 ∨ v ∈ vs := by
  induction vs generalizing s with
  | nil => exact Or.inl hv
  | cons u us ih =>
    rcases ih (s.encounter u) hv with h | h
    · by_cases hvu : v = u
      · exact Or.inr (hvu ▸ List.mem_cons_self)
      · left
        unfold VertexLabels.encounter at h
        split_ifs at h
        · simpa [Function.update_of_ne hvu] using h
        · exact h
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem endpointLabels_count_eq_card (K : Circulation) :
    K.endpointLabels.count =
      (Finset.univ.filter fun v : Fin K.n => 0 < K.endpointLabels.table v).card := by
  have h0 : (VertexLabels.empty K.n).count =
      (Finset.univ.filter fun v : Fin K.n => (VertexLabels.empty K.n).table v ≠ 0).card := by
    simp [VertexLabels.empty]
  have h := scan_count_eq_card (VertexLabels.empty K.n) K.endpoints h0
  simpa [Circulation.endpointLabels, Nat.pos_iff_ne_zero] using h

private theorem endpointLabels_count_le_card (K : Circulation) (T : Finset (Fin K.n))
    (hT : ∀ v ∈ K.endpoints, v ∈ T) : K.endpointLabels.count ≤ T.card := by
  rw [endpointLabels_count_eq_card]
  apply Finset.card_le_card
  intro v hv
  have hne : K.endpointLabels.table v ≠ 0 := Nat.ne_of_gt (Finset.mem_filter.mp hv).2
  rcases scan_table_ne_zero_mem (VertexLabels.empty K.n) K.endpoints v hne with h | h
  · simp [VertexLabels.empty] at h
  · exact hT v h

/-- Every active vertex of the pruned feasibility circulation is either an active vertex of
`shiftedGraph I hv` or the single auxiliary vertex `Fin.last I.n`. -/
theorem feasibility_compress_n_le (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) :
    (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.compress.n ≤ 2 * I.m + 1 := by
  set J := FlowReduction.shiftedGraph I hv
  set P := FlowReduction.buildFeasibilityInstance I hv
  set P' := P.withoutZeroEdges
  set S : Finset (Fin I.n) := Finset.univ.filter fun v : Fin I.n => 0 < J.endpointLabels.table v
  set T : Finset (Fin (I.n + 1)) := insert (Fin.last I.n) (S.image Fin.castSucc)
  have hsupp : ∀ v : Fin I.n, FlowReduction.shiftedDemand I v ≠ 0 →
      0 < J.endpointLabels.table v :=
    FlowReduction.shiftedDemand_support I hv hiso
  have hmem : ∀ v ∈ P'.endpoints, v ∈ T := by
    intro v hv_ep
    have hcases : (∃ e : Fin P'.m, P'.tail e = v) ∨ (∃ e : Fin P'.m, P'.head e = v) := by
      unfold Circulation.endpoints at hv_ep
      rcases List.mem_append.mp hv_ep with h | h <;>
        obtain ⟨e, rfl⟩ := List.mem_ofFn.mp h
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    have hpos_ep : ∀ (a : Fin P.m), 0 < P.capacity a → P.tail a ∈ T ∧ P.head a ∈ T := by
      intro a hcap
      refine Fin.addCases (fun e => ?_) (fun b => ?_) a hcap
      · intro _
        simp only [P, FlowReduction.buildFeasibilityInstance, Circulation.demandInstance,
          Fin.addCases_left]
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨J.tail e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.tail_label_pos e⟩, rfl⟩),
          Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨J.head e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.head_label_pos e⟩, rfl⟩)⟩
      · refine Fin.addCases (fun u => ?_) (fun u => ?_) b
        · intro hcap'
          simp only [P, FlowReduction.buildFeasibilityInstance, Circulation.demandInstance,
            Fin.addCases_right, Fin.addCases_left, FlowReduction.buildShiftedDemands_eq] at hcap' ⊢
          have hne : FlowReduction.shiftedDemand I u ≠ 0 := by omega
          exact ⟨Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp u hne⟩, rfl⟩)⟩
        · intro hcap'
          simp only [P, FlowReduction.buildFeasibilityInstance, Circulation.demandInstance,
            Fin.addCases_right, FlowReduction.buildShiftedDemands_eq] at hcap' ⊢
          have hne : FlowReduction.shiftedDemand I u ≠ 0 := by omega
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp u hne⟩, rfl⟩),
            Finset.mem_insert_self _ _⟩
    rcases hcases with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · have hcap : 0 < P.capacity (P.positiveIndex e) :=
        (P.mem_positiveEdges_iff _).mp (List.getElem_mem e.isLt)
      exact (hpos_ep (P.positiveIndex e) hcap).1
    · have hcap : 0 < P.capacity (P.positiveIndex e) :=
        (P.mem_positiveEdges_iff _).mp (List.getElem_mem e.isLt)
      exact (hpos_ep (P.positiveIndex e) hcap).2
  have hle := endpointLabels_count_le_card P' T hmem
  have hTcard : T.card ≤ S.card + 1 := by
    calc T.card ≤ (S.image Fin.castSucc).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
  have hScard : S.card ≤ 2 * I.m := by
    rw [← endpointLabels_count_eq_card J]
    exact J.endpointLabels_count_le
  exact le_trans hle (le_trans hTcard (Nat.add_le_add_right hScard 1))

/-- Every active vertex of the pruned residual circulation is an active vertex of
`shiftedGraph I hv`, so its compressed vertex count is at most `2 * I.m`. -/
theorem residual_compress_n_le (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.compress.n ≤ 2 * I.m := by
  set J := FlowReduction.shiftedGraph I hv
  set R := J.residual f
  set R' := R.withoutZeroEdges
  set S : Finset (Fin I.n) := Finset.univ.filter fun v : Fin I.n => 0 < J.endpointLabels.table v
  have hmem : ∀ v ∈ R'.endpoints, v ∈ S := by
    intro v hv_ep
    have hcases : (∃ e : Fin R'.m, R'.tail e = v) ∨ (∃ e : Fin R'.m, R'.head e = v) := by
      unfold Circulation.endpoints at hv_ep
      rcases List.mem_append.mp hv_ep with h | h <;>
        obtain ⟨e, rfl⟩ := List.mem_ofFn.mp h
      · exact Or.inl ⟨e, rfl⟩
      · exact Or.inr ⟨e, rfl⟩
    have hR_ep : ∀ a : Fin R.m, R.tail a ∈ S ∧ R.head a ∈ S := by
      intro a
      refine Fin.addCases (fun e => ?_) (fun e => ?_) a
      · simp only [R, Circulation.residual, Fin.addCases_left]
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.tail_label_pos e⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.head_label_pos e⟩⟩
      · simp only [R, Circulation.residual, Fin.addCases_right]
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.head_label_pos e⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, J.tail_label_pos e⟩⟩
    rcases hcases with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact (hR_ep (R.positiveIndex e)).1
    · exact (hR_ep (R.positiveIndex e)).2
  have hle := endpointLabels_count_le_card R' S hmem
  have hScard : S.card ≤ 2 * I.m := by
    rw [← endpointLabels_count_eq_card J]
    exact J.endpointLabels_count_le
  exact le_trans hle hScard

/-! ### Dimension, capacity, and cost bounds for both pruned calls -/

theorem feasibility_pruned_bounds (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    P'.n = I.n + 1 ∧
    P'.m ≤ 3 * I.m ∧
    circMaxCapacity P' ≤ FlowReduction.scalingCapacityBudget I I.maxCapacity ∧
    circMaxCost P' ≤ 1 := by
  set P := FlowReduction.buildFeasibilityInstance I hv
  set P' := P.withoutZeroEdges
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have h := FlowReduction.feasibilityInstance_positiveEdges_le_three I hv hiso
    rw [← FlowReduction.buildFeasibilityInstance_eq] at h
    exact h
  · unfold circMaxCapacity
    apply Finset.sup_le
    intro e _
    exact FlowReduction.buildFeasibilityInstance_capacity_le I hv I.maxCapacity
      (demand_natAbs_le_maxCapacity' I hv) (lower_natAbs_le_maxCapacity' I)
      (upper_natAbs_le_maxCapacity' I) (P.positiveIndex e)
  · unfold circMaxCost
    apply Finset.sup_le
    intro e _
    have h : ∀ a : Fin P.m, (P.cost a).natAbs ≤ 1 := by
      intro a
      refine Fin.addCases (fun _ => by simp [P])
        (fun _ => by simp [P]) a
    exact h (P.positiveIndex e)

theorem residual_pruned_bounds (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    R'.n = I.n ∧
    R'.m ≤ 2 * I.m ∧
    circMaxCapacity R' ≤ 2 * I.maxCapacity ∧
    circMaxCost R' ≤ I.maxCost := by
  let J := FlowReduction.shiftedGraph I hv
  let R := J.residual f
  let R' := R.withoutZeroEdges
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have h := R.positiveEdges_length_le
    change ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m ≤ I.m + I.m at h
    omega
  · unfold circMaxCapacity
    apply Finset.sup_le
    intro e _
    have hcap : ∀ a : Fin R.m, R.capacity a ≤ 2 * I.maxCapacity := by
      intro a
      refine Fin.addCases (fun j => ?_) (fun j => ?_) a
      · simp only [R, Fin.addCases_left]
        have hJ := FlowReduction.shiftedGraph_capacity_le I hv I.maxCapacity
          (lower_natAbs_le_maxCapacity' I) (upper_natAbs_le_maxCapacity' I) j
        have hfj := hf j
        change J.capacity j ≤ 2 * I.maxCapacity at hJ
        change 0 ≤ f j ∧ f j ≤ (J.capacity j : ℤ) at hfj
        omega
      · simp only [R, Fin.addCases_right]
        have hJ := FlowReduction.shiftedGraph_capacity_le I hv I.maxCapacity
          (lower_natAbs_le_maxCapacity' I) (upper_natAbs_le_maxCapacity' I) j
        have hfj := hf j
        omega
    exact hcap (R.positiveIndex e)
  · unfold circMaxCost
    apply Finset.sup_le
    intro e _
    have hcost : ∀ a : Fin R.m, (R.cost a).natAbs ≤ I.maxCost := by
      intro a
      refine Fin.addCases (fun j => ?_) (fun j => ?_) a
      · simp only [R, Fin.addCases_left]
        exact cost_natAbs_le_maxCost' I j
      · simp only [R, Fin.addCases_right, Int.natAbs_neg]
        exact cost_natAbs_le_maxCost' I j
    exact hcost (R.positiveIndex e)

/-! ### Joint Stage 1 space bound and total `narrowMain` space bound -/

private theorem two_mul_maxCap_le_budget (I : Instance) :
    2 * I.maxCapacity ≤ FlowReduction.scalingCapacityBudget I I.maxCapacity := by
  unfold FlowReduction.scalingCapacityBudget
  have h := Nat.mul_le_mul_right I.maxCapacity (show 2 ≤ 2 * (I.m + 1) by omega)
  omega

/-- Joint Stage 1 space bound for the feasibility call `P'` and residual call `R'`.
While `stage1CircSpace P' k S` can slightly exceed `narrowStage1SpaceBound I S` on its own,
the sum of both calls is always at most `2 * narrowStage1SpaceBound I S + 1`. -/
theorem stage1CircSpace_sum_le (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (S : ℕ → ℕ → ℕ) (hS : ∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m') :
    let k := narrowLimbWidth I
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    stage1CircSpace P' k S + stage1CircSpace R' k S ≤ 2 * narrowStage1SpaceBound I S + 1 := by
  intro k P' R'
  obtain ⟨hPn, hPm, hPcap, hPcost⟩ := feasibility_pruned_bounds I hv hiso
  obtain ⟨hRn, hRm, hRcap, hRcost⟩ := residual_pruned_bounds I hv f hf
  change P'.n = I.n + 1 at hPn
  change P'.m ≤ 3 * I.m at hPm
  change circMaxCapacity P' ≤ FlowReduction.scalingCapacityBudget I I.maxCapacity at hPcap
  change circMaxCost P' ≤ 1 at hPcost
  change R'.n = I.n at hRn
  change R'.m ≤ 2 * I.m at hRm
  change circMaxCapacity R' ≤ 2 * I.maxCapacity at hRcap
  change circMaxCost R' ≤ I.maxCost at hRcost
  by_cases hm0 : I.m = 0
  · have hP0 : P'.m = 0 := by omega
    have hR0 : R'.m = 0 := by omega
    simp [stage1CircSpace, hP0, hR0]
  have hm1 : 1 ≤ I.m := by omega
  have hPcn : P'.compress.n ≤ 2 * I.m + 1 := feasibility_compress_n_le I hv hiso
  have hRcn : R'.compress.n ≤ 2 * I.m := residual_compress_n_le I hv f
  set U := I.maxCapacity
  set C := I.maxCost
  set B_U := FlowReduction.scalingCapacityBudget I U
  set T_U := Nat.size B_U
  set L_c := Nat.size (max C 1)
  set K_cap := T_U / k + 2
  set L_limbs := L_c / k + 2
  set R_bnd := 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (I.m + 1) + 1)
  set startSp := (I.n + 1) + 30 + 48 * I.m + 15 * I.m * K_cap + 3 * I.m * L_limbs
  set bsSp := 5 + 12 * I.m + 18 * I.m * K_cap +
    T_U * (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m))
  set dualSp := 50 + 180 * I.m + 150 * I.m + S (6 * I.m + 2) (36 * I.m)
  have hTP : bitScalingPhases P' ≤ T_U := Nat.size_le_size hPcap
  have hTR : bitScalingPhases R' ≤ T_U := Nat.size_le_size (le_trans hRcap (two_mul_maxCap_le_budget I))
  have hLP : costScaleBits P' ≤ L_c := Nat.size_le_size (le_trans hPcost (le_max_right C 1))
  have hLR : costScaleBits R' ≤ L_c := Nat.size_le_size (le_trans hRcost (le_max_left C 1))
  have hRP : narrowCostRounds P'.compress ≤ R_bnd := by
    apply narrowCircModel_rounds_le P' I.m C hPm
    intro e
    have hle : (P'.cost e).natAbs ≤ circMaxCost P' :=
      Finset.le_sup (f := fun j => (P'.cost j).natAbs) (Finset.mem_univ e)
    exact le_trans hle (le_trans hPcost (le_max_right C 1))
  have hRR : narrowCostRounds R'.compress ≤ R_bnd := by
    apply narrowCircModel_rounds_le R' I.m C (by omega)
    intro e
    have hle : (R'.cost e).natAbs ≤ circMaxCost R' :=
      Finset.le_sup (f := fun j => (R'.cost j).natAbs) (Finset.mem_univ e)
    exact le_trans hle (le_trans hRcost (le_max_left C 1))
  have hstart_sum : stage1StartSpace P' k + stage1StartSpace R' k ≤ 2 * startSp + 1 := by
    unfold stage1StartSpace
    dsimp only
    have hKP : bitScalingPhases P' / k + 2 ≤ K_cap := Nat.add_le_add_right (Nat.div_le_div_right hTP) 2
    have hKR : bitScalingPhases R' / k + 2 ≤ K_cap := Nat.add_le_add_right (Nat.div_le_div_right hTR) 2
    have hLP' : costScaleBits P' / k + 2 ≤ L_limbs := Nat.add_le_add_right (Nat.div_le_div_right hLP) 2
    have hLR' : costScaleBits R' / k + 2 ≤ L_limbs := Nat.add_le_add_right (Nat.div_le_div_right hLR) 2
    have h1 : 5 * P'.m * (bitScalingPhases P' / k + 2) ≤ 15 * (I.m * K_cap) := by
      have := Nat.mul_le_mul (by omega : 5 * P'.m ≤ 15 * I.m) hKP; linarith
    have h2 : 5 * R'.m * (bitScalingPhases R' / k + 2) ≤ 10 * (I.m * K_cap) := by
      have := Nat.mul_le_mul (by omega : 5 * R'.m ≤ 10 * I.m) hKR; linarith
    have h3 : P'.m * (costScaleBits P' / k + 2) ≤ 3 * (I.m * L_limbs) := by
      have := Nat.mul_le_mul hPm hLP'; linarith
    have h4 : R'.m * (costScaleBits R' / k + 2) ≤ 2 * (I.m * L_limbs) := by
      have := Nat.mul_le_mul hRm hLR'; linarith
    have hK2 : 2 ≤ K_cap := Nat.le_add_left 2 _
    have hL2 : 2 ≤ L_limbs := Nat.le_add_left 2 _
    have h5 : 10 ≤ 5 * (I.m * K_cap) := by nlinarith
    have h6 : 2 ≤ I.m * L_limbs := by nlinarith
    have h7 : 6 ≤ 6 * I.m := by omega
    have hsp : 2 * startSp + 1 =
        2 * I.n + 63 + 96 * I.m + 30 * (I.m * K_cap) + 6 * (I.m * L_limbs) := by
      dsimp only [startSp]; ring
    rw [hsp, hPn, hRn]
    omega
  have hbsP : stage1RoundBitScaleSpace P'.compress k S ≤ bsSp := by
    unfold stage1RoundBitScaleSpace
    have hTP' : bitScalingPhases P'.compress ≤ T_U := hTP
    have hKP : bitScalingPhases P'.compress / k + 2 ≤ K_cap :=
      Nat.add_le_add_right (Nat.div_le_div_right hTP') 2
    have h1 : 6 * P'.compress.m * (bitScalingPhases P'.compress / k + 2) ≤ 18 * I.m * K_cap :=
      Nat.mul_le_mul (by change 6 * P'.m ≤ 18 * I.m; omega) hKP
    have hS1 : S (P'.compress.n + 1) (4 * P'.compress.m) ≤ S (6 * I.m + 1) (12 * I.m) :=
      hS _ _ _ _ (by omega) (by change 4 * P'.m ≤ 12 * I.m; omega)
    have h2 : bitScalingPhases P'.compress * (2 + 24 * P'.compress.m + S (P'.compress.n + 1) (4 * P'.compress.m)) ≤
        T_U * (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m)) :=
      Nat.mul_le_mul hTP' (by change 2 + 24 * P'.m + _ ≤ _; omega)
    have h0 : 5 + 4 * P'.compress.m ≤ 5 + 12 * I.m := by change 5 + 4 * P'.m ≤ _; omega
    exact Nat.add_le_add (Nat.add_le_add h0 h1) h2
  have hbsR : stage1RoundBitScaleSpace R'.compress k S ≤ bsSp := by
    unfold stage1RoundBitScaleSpace
    have hTR' : bitScalingPhases R'.compress ≤ T_U := hTR
    have hKR : bitScalingPhases R'.compress / k + 2 ≤ K_cap :=
      Nat.add_le_add_right (Nat.div_le_div_right hTR') 2
    have h1 : 6 * R'.compress.m * (bitScalingPhases R'.compress / k + 2) ≤ 18 * I.m * K_cap :=
      Nat.mul_le_mul (by change 6 * R'.m ≤ 18 * I.m; omega) hKR
    have hS1 : S (R'.compress.n + 1) (4 * R'.compress.m) ≤ S (6 * I.m + 1) (12 * I.m) :=
      hS _ _ _ _ (by omega) (by change 4 * R'.m ≤ 12 * I.m; omega)
    have h2 : bitScalingPhases R'.compress * (2 + 24 * R'.compress.m + S (R'.compress.n + 1) (4 * R'.compress.m)) ≤
        T_U * (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m)) :=
      Nat.mul_le_mul hTR' (by change 2 + 24 * R'.m + _ ≤ _; omega)
    have h0 : 5 + 4 * R'.compress.m ≤ 5 + 12 * I.m := by change 5 + 4 * R'.m ≤ _; omega
    exact Nat.add_le_add (Nat.add_le_add h0 h1) h2
  have hdual_sum : stage1DualSpace P'.compress S + stage1DualSpace R'.compress S ≤ 2 * dualSp := by
    have hSP : S (P'.compress.n + 2) (2 * (4 * P'.compress.m + P'.compress.n)) ≤
        S (6 * I.m + 2) (36 * I.m) :=
      hS _ _ _ _ (by omega) (by change 2 * (4 * P'.m + P'.compress.n) ≤ 36 * I.m; omega)
    have hSR : S (R'.compress.n + 2) (2 * (4 * R'.compress.m + R'.compress.n)) ≤
        S (6 * I.m + 2) (36 * I.m) :=
      hS _ _ _ _ (by omega) (by change 2 * (4 * R'.m + R'.compress.n) ≤ 36 * I.m; omega)
    have hdual_eq : ∀ (K : Circulation), stage1DualSpace K S =
        (14 + 5 * K.n + 24 * (4 * K.m + K.n)) + S (K.n + 2) (2 * (4 * K.m + K.n)) := by
      intro K; unfold stage1DualSpace; dsimp only; ring
    rw [hdual_eq P'.compress, hdual_eq R'.compress]
    have h1 : 14 + 5 * P'.compress.n + 24 * (4 * P'.compress.m + P'.compress.n) ≤ 43 + 346 * I.m := by
      change 14 + 5 * P'.compress.n + 24 * (4 * P'.m + P'.compress.n) ≤ _; omega
    have h2 : 14 + 5 * R'.compress.n + 24 * (4 * R'.compress.m + R'.compress.n) ≤ 14 + 250 * I.m := by
      change 14 + 5 * R'.compress.n + 24 * (4 * R'.m + R'.compress.n) ≤ _; omega
    have h3 : (43 + 346 * I.m) + (14 + 250 * I.m) ≤ 100 + 660 * I.m := by omega
    have hsp : 2 * dualSp = (100 + 660 * I.m) + (S (6 * I.m + 2) (36 * I.m) + S (6 * I.m + 2) (36 * I.m)) := by
      dsimp only [dualSp]; ring
    rw [hsp]
    have hrearr : ∀ a b c d : ℕ, (a + b) + (c + d) = (a + c) + (b + d) := fun _ _ _ _ => by omega
    rw [hrearr]
    exact Nat.add_le_add (le_trans (Nat.add_le_add h1 h2) h3) (Nat.add_le_add hSP hSR)
  have hround_sum :
      narrowCostRounds P'.compress *
          (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) +
      narrowCostRounds R'.compress *
          (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S) ≤
      2 * (R_bnd * (bsSp + dualSp)) := by
    calc
      narrowCostRounds P'.compress *
            (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) +
          narrowCostRounds R'.compress *
            (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S)
        ≤ R_bnd * (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) +
          R_bnd * (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hRP) (Nat.mul_le_mul_right _ hRR)
      _ = R_bnd * ((stage1RoundBitScaleSpace P'.compress k S + stage1RoundBitScaleSpace R'.compress k S) +
            (stage1DualSpace P'.compress S + stage1DualSpace R'.compress S)) := by ring
      _ ≤ R_bnd * ((bsSp + bsSp) + 2 * dualSp) :=
          Nat.mul_le_mul_left R_bnd (Nat.add_le_add (Nat.add_le_add hbsP hbsR) hdual_sum)
      _ = 2 * (R_bnd * (bsSp + dualSp)) := by ring
  have hP_le : stage1CircSpace P' k S ≤ stage1StartSpace P' k +
      narrowCostRounds P'.compress *
        (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) := by
    unfold stage1CircSpace; dsimp only; split_ifs
    · exact Nat.zero_le _
    · exact le_rfl
  have hR_le : stage1CircSpace R' k S ≤ stage1StartSpace R' k +
      narrowCostRounds R'.compress *
        (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S) := by
    unfold stage1CircSpace; dsimp only; split_ifs
    · exact Nat.zero_le _
    · exact le_rfl
  have hBnd : narrowStage1SpaceBound I S = startSp + R_bnd * (bsSp + dualSp) := rfl
  rw [hBnd]
  have hrearr : ∀ a b c d : ℕ, (a + b) + (c + d) = (a + c) + (b + d) := fun _ _ _ _ => by omega
  have hcomb : (stage1StartSpace P' k + stage1StartSpace R' k) +
      (narrowCostRounds P'.compress *
          (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) +
       narrowCostRounds R'.compress *
          (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S)) ≤
      (2 * startSp + 1) + 2 * (R_bnd * (bsSp + dualSp)) :=
    Nat.add_le_add hstart_sum hround_sum
  have hrhs : (2 * startSp + 1) + 2 * (R_bnd * (bsSp + dualSp)) =
      2 * (startSp + R_bnd * (bsSp + dualSp)) + 1 := by ring
  calc stage1CircSpace P' k S + stage1CircSpace R' k S
      ≤ (stage1StartSpace P' k +
          narrowCostRounds P'.compress *
            (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S)) +
        (stage1StartSpace R' k +
          narrowCostRounds R'.compress *
            (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S)) :=
        Nat.add_le_add hP_le hR_le
    _ = (stage1StartSpace P' k + stage1StartSpace R' k) +
        (narrowCostRounds P'.compress *
            (stage1RoundBitScaleSpace P'.compress k S + stage1DualSpace P'.compress S) +
         narrowCostRounds R'.compress *
            (stage1RoundBitScaleSpace R'.compress k S + stage1DualSpace R'.compress S)) := hrearr _ _ _ _
    _ ≤ (2 * startSp + 1) + 2 * (R_bnd * (bsSp + dualSp)) := hcomb
    _ = 2 * (startSp + R_bnd * (bsSp + dualSp)) + 1 := hrhs

/-- Total heap space across all 6 stages of `narrowMain` fits inside `narrowMainSpace I S`. -/
theorem narrowMain_totalSpace_le (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (S : ℕ → ℕ → ℕ) (hS : ∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m')
    {cnt L : ℕ} (hcnt : cnt ≤ 2 * I.m) (hL : L ≤ narrowMaxCapLimbs I + 1) :
    let k := narrowLimbWidth I
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    5 + stage0ReadSpace I + stage0CheckSpace I + stage0ShiftSpace I.m cnt L +
      (26 * I.m + I.m * L + 12) + stage1CircSpace P' k S +
      (16 * I.m + 4 * I.m * L + 2 * I.m * narrowMaxCostLimbs I + 12) + stage1CircSpace R' k S +
      stage3AnswerSpace I.m L ≤ narrowMainSpace I S := by
  intro k P' R'
  have hsum : stage1CircSpace P' k S + stage1CircSpace R' k S ≤ 2 * narrowStage1SpaceBound I S + 1 :=
    stage1CircSpace_sum_le I hv hiso f hf S hS
  unfold stage0ReadSpace stage0CheckSpace stage0ShiftSpace stage3AnswerSpace narrowMainSpace
  dsimp only
  set L_dem := narrowMaxCapLimbs I + 1
  have h1 : I.m * L ≤ I.m * L_dem := Nat.mul_le_mul_left I.m hL
  have h2 : cnt * L ≤ 2 * I.m * L_dem := Nat.mul_le_mul hcnt hL
  have h3 : 3 * cnt * L ≤ 6 * (I.m * L_dem) := by nlinarith
  have h4 : I.m * (2 + L) = 2 * I.m + I.m * L := by ring
  have h5 : 4 * I.m * L = 4 * (I.m * L) := by ring
  have h6 : 13 * I.m * L_dem = 13 * (I.m * L_dem) := by ring
  omega

/-! ### Stage 1 width bounds from `NarrowMainFits` -/

private theorem upperClip_mono {a b : ℕ} (h : a ≤ b) : upperClip a ≤ upperClip b := by
  unfold upperClip costPrecisionExp costClipExp
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.add_le_add
  · exact Nat.clog_mono_right 2 (Nat.pow_le_pow_left (by omega) 8)
  · exact Nat.clog_mono_right 2 (by omega)

/-- `NarrowMainFits w S I hv` implies all word-width side conditions needed by `narrowMain`
and by `stage1CircSpec` on any circulation `K` with `K.n ≤ I.n + 1` and `K.m ≤ 3 * I.m`. -/
theorem narrowMain_stage1_widths {w : ℕ} {S : ℕ → ℕ → ℕ} {I : Instance} {hv : I.IsValid}
    (hfits : NarrowMainFits w S I hv) {K : Circulation} (hKn : K.n ≤ I.n + 1) (hKm : K.m ≤ 3 * I.m) :
    let k := narrowLimbWidth I
    1 ≤ k ∧ 2 * k ≤ w ∧ k + Nat.log 2 (2 * k) + 2 ≤ w ∧
    2 * K.m + 1 < 2 ^ k ∧ 6 * K.m + 4 < 2 ^ w ∧ K.n + 1 < 2 ^ w ∧
    (6 * K.m + 21) * upperClip K.m < 2 ^ w ∧ 10 < 2 ^ w ∧ 2 < 2 ^ w := by
  obtain ⟨h2k1, hclip, hmem⟩ := hfits
  set k := narrowLimbWidth I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have h6m : 6 * I.m + 1 < 2 ^ k := six_mul_m_add_one_lt_pow_limbWidth I hv
  have hlog := limbWidth_log_bound hk3 h2k1
  have h2pow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
  have hclip_le : (6 * K.m + 21) * upperClip K.m ≤ (18 * I.m + 21) * upperClip (3 * I.m) :=
    Nat.mul_le_mul (by omega) (upperClip_mono hKm)
  have hup_pos : 1 ≤ upperClip (3 * I.m) := Nat.pow_pos (by decide)
  have h18m : 18 * I.m + 21 ≤ (18 * I.m + 21) * upperClip (3 * I.m) :=
    Nat.le_mul_of_pos_right _ hup_pos
  have h4n : 4 * I.n + 60 ≤ narrowMainSpace I S := by
    unfold narrowMainSpace; dsimp only; omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ### Reduction correctness via `solvePruned_correct` and `reduceToCirculation_correct_of_calls` -/

private theorem shiftedCap_lt_pow_L {I : Instance} {hv : I.IsValid} {L : ℕ}
    (hcaps : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hltL : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length < L)
    (e : Fin I.m) :
    (FlowReduction.shiftedGraph I hv).capacity e < (2 ^ narrowLimbWidth I) ^ L := by
  set k := narrowLimbWidth I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hb : 2 ≤ 2 ^ k := le_trans (by decide : 2 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) hk3)
  have hL1 : 1 ≤ L := by have := (hltL e).1; omega
  have hlo : (I.edge e).lower.natAbs < (2 ^ k) ^ (L - 1) := by
    have h1 := ofDigits_lt_pow_length (k := k) (by omega)
      (digits_canonical (by omega) (I.edge e).lower.natAbs).1
    rw [Nat.ofDigits_digits] at h1
    have h2 : (2 ^ k) ^ (Nat.digits (2 ^ k) (I.edge e).lower.natAbs).length ≤ (2 ^ k) ^ (L - 1) :=
      Nat.pow_le_pow_right (by omega) (by have := (hltL e).1; omega)
    exact lt_of_lt_of_le h1 h2
  have hhi : (I.edge e).upper.natAbs < (2 ^ k) ^ (L - 1) := by
    have h1 := ofDigits_lt_pow_length (k := k) (by omega)
      (digits_canonical (by omega) (I.edge e).upper.natAbs).1
    rw [Nat.ofDigits_digits] at h1
    have h2 : (2 ^ k) ^ (Nat.digits (2 ^ k) (I.edge e).upper.natAbs).length ≤ (2 ^ k) ^ (L - 1) :=
      Nat.pow_le_pow_right (by omega) (by have := (hltL e).2; omega)
    exact lt_of_lt_of_le h1 h2
  have hcap : (FlowReduction.shiftedGraph I hv).capacity e ≤
      (I.edge e).lower.natAbs + (I.edge e).upper.natAbs := by
    change ((I.edge e).upper - (I.edge e).lower).toNat ≤ _
    have := hcaps e
    omega
  have hpow : (2 ^ k) ^ L = (2 ^ k) * (2 ^ k) ^ (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ']
  have h2pow : 2 * (2 ^ k) ^ (L - 1) ≤ (2 ^ k) * (2 ^ k) ^ (L - 1) :=
    Nat.mul_le_mul_right _ hb
  omega

/-- Total number of `k`-bit cost limbs across all edges of `I`. -/
def totCostLimbs (I : Instance) : ℕ :=
  ∑ e : Fin I.m, (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length

theorem totCostLimbs_le (I : Instance) :
    totCostLimbs I ≤ I.m * narrowMaxCostLimbs I := by
  have hk1 : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hb : 1 < 2 ^ narrowLimbWidth I := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk1
    have h2 : 2 ≤ 2 ^ narrowLimbWidth I := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hk1)
    omega
  have hterm : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length ≤ narrowMaxCostLimbs I := by
    intro e
    have hle : (I.edge e).cost.natAbs ≤ I.maxCost := by
      unfold Instance.maxCost
      have hfold_le : ∀ (x : ℕ) (l : List ℕ), x ∈ l → x ≤ l.foldr max 0 := by
        intro x l hmem
        induction l with
        | nil => cases hmem
        | cons a l ih =>
          simp only [List.foldr_cons]
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact le_max_left _ _
          · exact le_trans (ih hmem') (le_max_right _ _)
      exact hfold_le _ _ (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
    unfold narrowMaxCostLimbs
    by_cases h0 : (I.edge e).cost.natAbs = 0
    · rw [h0]; simp
    · have hc0 : I.maxCost ≠ 0 := by omega
      rw [Nat.length_digits _ _ hb h0, Nat.length_digits _ _ hb hc0]
      exact Nat.add_le_add_right (Nat.log_mono_right hle) 1
  unfold totCostLimbs
  calc ∑ e : Fin I.m, (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length
      ≤ ∑ _e : Fin I.m, narrowMaxCostLimbs I := Finset.sum_le_sum fun e _ => hterm e
    _ = I.m * narrowMaxCostLimbs I := by simp

private theorem maxCapacity_mem_cases (I : Instance) (hv : I.IsValid) :
    I.maxCapacity = 0 ∨
      (∃ e : Fin I.m, I.maxCapacity = (I.edge e).lower.natAbs ∨
        I.maxCapacity = (I.edge e).upper.natAbs) ∨
      (∃ v : Fin I.n, I.maxCapacity = (I.d v).natAbs) := by
  have hfold : ∀ (l : List ℕ), l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
    intro l; induction l with
    | nil => left; rfl
    | cons a l ih =>
      simp only [List.foldr_cons]
      rcases le_total a (l.foldr max 0) with h | h
      · rw [max_eq_right h]
        rcases ih with h0 | hm
        · left; exact h0
        · right; exact List.mem_cons_of_mem a hm
      · rw [max_eq_left h]; right; exact List.mem_cons_self
  unfold Instance.maxCapacity
  rcases hfold _ with h0 | hm
  · left; exact h0
  · rcases List.mem_append.mp hm with hm1 | hm2
    · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm1
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      right; left; refine ⟨⟨i, hi⟩, ?_⟩
      rcases le_total (I.edges[i]'hi).lower.natAbs (I.edges[i]'hi).upper.natAbs with h | h
      · right; rw [← heq, max_eq_right h]; rfl
      · left; rw [← heq, max_eq_left h]; rfl
    · obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm2
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hin : i < I.n := by rw [← hv.2]; exact hi
      right; right; refine ⟨⟨i, hin⟩, ?_⟩
      rw [← heq]; unfold Instance.d; rw [List.getD_eq_getElem _ _ hi]

/-- When `stage0Check` succeeds (`isolatedCheck = true`), the computed limb width `L` equals
`narrowMaxCapLimbs I + 1`. -/
theorem stage0Check_L_eq (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) {act : List ℕ} {L : ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    (hL1 : 1 ≤ L) (hLle : L ≤ narrowMaxCapLimbs I + 1)
    (hedge : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length < L)
    (hdem : ∀ (c : ℕ) (hc : c < act.length),
      (Nat.digits (2 ^ narrowLimbWidth I) (I.d (act[c]'hc)).natAbs).length < L) :
    L = narrowMaxCapLimbs I + 1 := by
  have hmem := maxCapacity_mem_cases I hv
  unfold narrowMaxCapLimbs at hLle ⊢
  rcases hmem with h0 | ⟨e, hlo | hhi⟩ | ⟨v, hdv⟩
  · rw [h0] at hLle ⊢; simp at hLle ⊢; omega
  · rw [hlo] at hLle ⊢; have := (hedge e).1; omega
  · rw [hhi] at hLle ⊢; have := (hedge e).2; omega
  · set el := (FlowReduction.shiftedGraph I hv).endpointLabels
    by_cases hlab : el.table v = 0
    · have hdv0 : I.d v = 0 :=
        ((FlowReduction.isolatedCheck_iff I hv).mp hiso v).resolve_left
          (by change ¬ 0 < el.table v; omega)
      rw [hdv, hdv0] at hLle ⊢; simp at hLle ⊢; omega
    · have hval := Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)
      have hle : el.table v ≤ el.count := hval.1 v
      have hc_lt : el.table v - 1 < el.count := by omega
      have hc_act : el.table v - 1 < act.length := by rw [hact.1]; exact hc_lt
      have htab : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ = el.table v := by
        have := (hact.2 (el.table v - 1) hc_act).2; omega
      have hne : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ ≠ 0 := by omega
      have hv_eq : (⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ : Fin I.n) = v :=
        hval.2 _ _ hne htab
      have hact_eq : act[el.table v - 1]'hc_act = v.val := congrArg Fin.val hv_eq
      have hd := hdem (el.table v - 1) hc_act
      rw [hact_eq] at hd
      rw [hdv] at hLle ⊢
      omega

/-- `narrowMaxCapLimbs I + 1 < 2 ^ narrowLimbWidth I` for every valid instance `I`. -/
theorem narrowMaxCapLimbs_lt_pow_k (I : Instance) (hv : I.IsValid) :
    narrowMaxCapLimbs I + 1 < 2 ^ narrowLimbWidth I := by
  have hk1 : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hlog : Nat.log 2 I.maxCapacity + 2 ≤ narrowBitLength I := by
    rcases maxCapacity_mem_cases I hv with h0 | ⟨e, hlo | hhi⟩ | ⟨v, hdv⟩
    · rw [h0]; have := four_le_narrowBitLength I; simp; omega
    · have hle : narrowEdgeBits (I.edge e) ≤ (I.edges.map narrowEdgeBits).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
      unfold narrowBitLength narrowEdgeBits narrowIntBits at hle ⊢
      rw [hlo]; omega
    · have hle : narrowEdgeBits (I.edge e) ≤ (I.edges.map narrowEdgeBits).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨I.edge e, List.getElem_mem e.isLt, rfl⟩)
      unfold narrowBitLength narrowEdgeBits narrowIntBits at hle ⊢
      rw [hhi]; omega
    · have hv' : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
      have hdv' : I.d v = I.demand[v.val]'hv' := List.getD_eq_getElem _ _ hv'
      have hle : narrowIntBits (I.d v) ≤ (I.demand.map narrowIntBits).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨I.d v, hdv' ▸ List.getElem_mem hv', rfl⟩)
      unfold narrowBitLength narrowIntBits at hle ⊢
      rw [hdv]; omega
  have hlt := narrowBitLength_lt_pow_limbWidth I
  have hdig : narrowMaxCapLimbs I ≤ Nat.log 2 I.maxCapacity + 1 := by
    unfold narrowMaxCapLimbs
    by_cases h0 : I.maxCapacity = 0
    · rw [h0]; simp
    · have h2le : 2 ≤ 2 ^ narrowLimbWidth I :=
        le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hk1)
      have hb : 1 < 2 ^ narrowLimbWidth I := by omega
      rw [Nat.length_digits _ _ hb h0]
      have h1 : (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤ I.maxCapacity :=
        Nat.pow_log_le_self _ h0
      have h2 : 2 ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤
          (2 ^ narrowLimbWidth I) ^ Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity :=
        Nat.pow_le_pow_left h2le _
      have h3 : Nat.log (2 ^ narrowLimbWidth I) I.maxCapacity ≤ Nat.log 2 I.maxCapacity :=
        (Nat.le_log_iff_pow_le (by decide) h0).mpr (le_trans h2 h1)
      omega
  omega

/-- Given a feasible shifted flow `f` from `stage0Feas` and an optimal residual circulation `g`
from `stage0Res`, proves the limb-length preconditions of `stage3AnswerSpec` and
`narrowIsCorrectAnswer I (stage3AnsList d)`. -/
theorem narrowMain_stage3_correct (I : Instance) (hv : I.IsValid) (L : ℕ)
    (hcaps : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hltL : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length < L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length < L)
    (f : Fin I.m → ℤ)
    (hf_bnds : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hf_feas : I.IsFeasible (FlowReduction.restore I (fun e => (f e : ℝ))))
    (g : Fin (I.m + I.m) → ℤ)
    (hg_opt : ((FlowReduction.shiftedGraph I hv).residual f).Optimal (fun a => (g a : ℝ)))
    (hg_nonneg : ∀ e : Fin I.m, 0 ≤ g (Fin.castAdd I.m e) ∧ 0 ≤ g (Fin.natAdd I.m e))
    (hrev_le : ∀ e : Fin I.m, (g (Fin.natAdd I.m e)).toNat ≤ (f e).toNat)
    (hsum_le : ∀ e : Fin I.m, (f e).toNat + (g (Fin.castAdd I.m e)).toNat ≤
      (FlowReduction.shiftedGraph I hv).capacity e) :
    let d : Stage3Data := ⟨I, hv, L, fun e => (f e).toNat,
      fun e => (g (Fin.castAdd I.m e)).toNat, fun e => (g (Fin.natAdd I.m e)).toNat⟩
    (∀ e, (Nat.digits (2 ^ narrowLimbWidth I) (d.fVal e)).length ≤ L ∧
          (Nat.digits (2 ^ narrowLimbWidth I) (d.hFwdVal e)).length ≤ L ∧
          (Nat.digits (2 ^ narrowLimbWidth I) (d.hRevVal e)).length ≤ L) ∧
    narrowIsCorrectAnswer I (stage3AnsList d) := by
  let J := FlowReduction.shiftedGraph I hv
  have hdig_of_lt : ∀ {x : ℕ}, x < (2 ^ narrowLimbWidth I) ^ L →
      (Nat.digits (2 ^ narrowLimbWidth I) x).length ≤ L := by
    intro x hx
    have hk1 : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
    by_contra hgt
    have hlt : L < (Nat.digits (2 ^ narrowLimbWidth I) x).length := by omega
    have hne : Nat.digits (2 ^ narrowLimbWidth I) x ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hge := ofDigits_ge_pow_pred (k := narrowLimbWidth I) hk1
      (digits_canonical hk1 x) hne
    rw [Nat.ofDigits_digits] at hge
    have hpow : (2 ^ narrowLimbWidth I) ^ L ≤
        (2 ^ narrowLimbWidth I) ^ ((Nat.digits (2 ^ narrowLimbWidth I) x).length - 1) :=
      Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)
    omega
  have hdigs : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (f e).toNat).length ≤ L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (g (Fin.castAdd I.m e)).toNat).length ≤ L ∧
      (Nat.digits (2 ^ narrowLimbWidth I) (g (Fin.natAdd I.m e)).toNat).length ≤ L := by
    intro e
    have hcap_lt : (FlowReduction.shiftedGraph I hv).capacity e < (2 ^ narrowLimbWidth I) ^ L :=
      shiftedCap_lt_pow_L (hv := hv) hcaps hltL e
    have hf_le : (f e).toNat ≤ (FlowReduction.shiftedGraph I hv).capacity e := by
      have := hf_bnds e; omega
    have h1 : (f e).toNat < (2 ^ narrowLimbWidth I) ^ L := lt_of_le_of_lt hf_le hcap_lt
    have h2 : (g (Fin.castAdd I.m e)).toNat < (2 ^ narrowLimbWidth I) ^ L :=
      lt_of_le_of_lt (by have := hsum_le e; omega) hcap_lt
    have h3 : (g (Fin.natAdd I.m e)).toNat < (2 ^ narrowLimbWidth I) ^ L :=
      lt_of_le_of_lt (le_trans (hrev_le e) hf_le) hcap_lt
    exact ⟨hdig_of_lt h1, hdig_of_lt h2, hdig_of_lt h3⟩
  have hmin := FlowReduction.minCostFlow_of_residual_optimal I hv hcaps f hf_feas
    (fun a => (g a : ℝ)) hg_opt
  let d : Stage3Data := ⟨I, hv, L, fun e => (f e).toNat,
    fun e => (g (Fin.castAdd I.m e)).toNat, fun e => (g (Fin.natAdd I.m e)).toNat⟩
  have hflow_eq : (fun e => ((stage3Flow d e : ℤ) : ℝ)) =
      FlowReduction.restore I (J.augment f (fun a => (g a : ℝ))) := by
    funext e
    unfold stage3Flow FlowReduction.restore Circulation.augment Circulation.project
    dsimp only [d]
    have hf0 : ((f e).toNat : ℤ) = f e := Int.toNat_of_nonneg (hf_bnds e).1
    have hfwd0 : ((g (Fin.castAdd I.m e)).toNat : ℤ) = g (Fin.castAdd I.m e) :=
      Int.toNat_of_nonneg (hg_nonneg e).1
    have hrev0 : ((g (Fin.natAdd I.m e)).toNat : ℤ) = g (Fin.natAdd I.m e) :=
      Int.toNat_of_nonneg (hg_nonneg e).2
    rw [hf0, hfwd0, hrev0]
    push_cast
    ring
  rw [← hflow_eq] at hmin
  exact ⟨hdigs, Or.inr ⟨stage3Flow d, hmin, rfl⟩⟩

end MinCostFlow.NarrowTop
