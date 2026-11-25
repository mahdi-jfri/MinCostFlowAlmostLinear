module

public import MinCostFlow.NarrowProg.Stage0FeasLayout
import WordRAM.Sep.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 5 (layout): pruned residual circulation `R'`

Characterizes `R' = ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges` as the
concatenation of two scans (`resFwdPos`, `resRevPos`), proves the reversible heap-splitting
lemmas connecting `pCapBuf2`, `pFeasFlow`, and `pCostBuf2` to `stage1Input R'`, and proves the
capacity/cost limb invariants and scatter identities for Item 5.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Two-pass decomposition of `((shiftedGraph I hv).residual f).positiveEdges` -/

/-- Original edges with positive forward residual capacity among the first `i` edges. -/
def resFwdPos (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (i : ℕ) : List (Fin I.m) :=
  ((List.finRange I.m).take i).filter (fun e =>
    decide (0 < (((FlowReduction.shiftedGraph I hv).capacity e : ℤ) - f e).toNat))

/-- Original edges with positive reverse residual capacity (`f e > 0`) among the first `i` edges. -/
def resRevPos (I : Instance) (f : Fin I.m → ℤ) (i : ℕ) : List (Fin I.m) :=
  ((List.finRange I.m).take i).filter (fun e => decide (0 < (f e).toNat))

theorem resFwdPos_zero (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    resFwdPos I hv f 0 = [] := by
  simp [resFwdPos]

theorem resRevPos_zero (I : Instance) (f : Fin I.m → ℤ) :
    resRevPos I f 0 = [] := by
  simp [resRevPos]

private theorem finRange_take_succ' {n i : ℕ} (hi : i < n) :
    (List.finRange n).take (i + 1) = (List.finRange n).take i ++ [⟨i, hi⟩] := by
  rw [List.take_succ_eq_append_getElem (by simp; exact hi)]
  simp

theorem resFwdPos_succ (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) {i : ℕ} (hi : i < I.m) :
    resFwdPos I hv f (i + 1) =
      resFwdPos I hv f i ++
        (if 0 < (((FlowReduction.shiftedGraph I hv).capacity ⟨i, hi⟩ : ℤ) - f ⟨i, hi⟩).toNat
         then [⟨i, hi⟩] else []) := by
  unfold resFwdPos
  rw [finRange_take_succ' hi, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem resRevPos_succ (I : Instance) (f : Fin I.m → ℤ) {i : ℕ} (hi : i < I.m) :
    resRevPos I f (i + 1) =
      resRevPos I f i ++ (if 0 < (f ⟨i, hi⟩).toNat then [⟨i, hi⟩] else []) := by
  unfold resRevPos
  rw [finRange_take_succ' hi, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem resFwdPos_nodup (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (i : ℕ) :
    (resFwdPos I hv f i).Nodup :=
  ((List.nodup_finRange I.m).take).filter _

theorem resRevPos_nodup (I : Instance) (f : Fin I.m → ℤ) (i : ℕ) :
    (resRevPos I f i).Nodup :=
  ((List.nodup_finRange I.m).take).filter _

theorem resFwdPos_length_le (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (i : ℕ) :
    (resFwdPos I hv f i).length ≤ i := by
  unfold resFwdPos
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem resRevPos_length_le (I : Instance) (f : Fin I.m → ℤ) (i : ℕ) :
    (resRevPos I f i).length ≤ i := by
  unfold resRevPos
  exact le_trans (List.length_filter_le _ _) (by simp)

private theorem finRange_add_eq' (a b : ℕ) :
    List.finRange (a + b) =
      (List.finRange a).map (Fin.castAdd b) ++ (List.finRange b).map (Fin.natAdd a) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_finRange]
    by_cases ha : i < a
    · rw [List.getElem_append_left (by simp; exact ha)]
      simp [Fin.castAdd]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange]
      apply Fin.ext; simp [Fin.natAdd]; omega

/-- Exact 2-pass decomposition of `((shiftedGraph I hv).residual f).positiveEdges`. -/
theorem res_positiveEdges_eq (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    ((FlowReduction.shiftedGraph I hv).residual f).positiveEdges =
      (resFwdPos I hv f I.m).map (Fin.castAdd I.m) ++
      (resRevPos I f I.m).map (Fin.natAdd I.m) := by
  set R := (FlowReduction.shiftedGraph I hv).residual f
  unfold Circulation.positiveEdges
  change (List.finRange (I.m + I.m)).filter (fun e => decide (0 < R.capacity e)) = _
  rw [finRange_add_eq' I.m I.m, List.filter_append, List.filter_map, List.filter_map]
  have h1 : (List.finRange I.m).filter
      ((fun e => decide (0 < R.capacity e)) ∘ Fin.castAdd I.m) = resFwdPos I hv f I.m := by
    unfold resFwdPos
    rw [List.take_of_length_le (by simp)]
    apply List.filter_congr; intro e _
    simp [R, Fin.addCases_left]
  have h2 : (List.finRange I.m).filter
      ((fun e => decide (0 < R.capacity e)) ∘ Fin.natAdd I.m) = resRevPos I f I.m := by
    unfold resRevPos
    rw [List.take_of_length_le (by simp)]
    apply List.filter_congr; intro e _
    simp only [Function.comp_def, R, Fin.addCases_right]
  rw [h1, h2]

theorem res_m_eq (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m =
      (resFwdPos I hv f I.m).length + (resRevPos I f I.m).length := by
  change ((FlowReduction.shiftedGraph I hv).residual f).positiveEdges.length = _
  rw [res_positiveEdges_eq I hv f]
  simp only [List.length_append, List.length_map]

theorem res_m_le_two_m (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m ≤ 2 * I.m := by
  rw [res_m_eq]
  have h1 := resFwdPos_length_le I hv f I.m
  have h2 := resRevPos_length_le I f I.m
  omega

/-! ### Total cost-limb budget and Stage 1 arrays for `R'` -/

/-- Sum of canonical cost-limb lengths over all `I.m` input edges. -/
def totCostLimbs (I : Instance) : ℕ :=
  ∑ e : Fin I.m, (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length

/-- Prefix sum of canonical cost-limb lengths over the first `i` edges. -/
def prefixCostLimbs (I : Instance) (i : ℕ) : ℕ :=
  ∑ e ∈ Finset.range i,
    if h : e < I.m then (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨e, h⟩).cost.natAbs).length
    else 0

theorem prefixCostLimbs_zero (I : Instance) : prefixCostLimbs I 0 = 0 := by
  simp [prefixCostLimbs]

theorem prefixCostLimbs_succ (I : Instance) {i : ℕ} (hi : i < I.m) :
    prefixCostLimbs I (i + 1) =
      prefixCostLimbs I i + (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨i, hi⟩).cost.natAbs).length := by
  unfold prefixCostLimbs
  rw [Finset.sum_range_succ, dite_eq_left hi]

theorem prefixCostLimbs_full (I : Instance) : prefixCostLimbs I I.m = totCostLimbs I := by
  unfold prefixCostLimbs totCostLimbs
  rw [← Fin.sum_univ_eq_sum_range (fun i =>
    if h : i < I.m then (Nat.digits (2 ^ narrowLimbWidth I) (I.edge ⟨i, h⟩).cost.natAbs).length else 0) I.m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [dite_eq_left e.isLt]

theorem totCostLimbs_le (I : Instance) : totCostLimbs I ≤ I.m * narrowMaxCostLimbs I := by
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth I
  have hb : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  unfold totCostLimbs narrowMaxCostLimbs
  calc ∑ e : Fin I.m, (Nat.digits (2 ^ k) (I.edge e).cost.natAbs).length
      ≤ ∑ _e : Fin I.m, (Nat.digits (2 ^ k) I.maxCost).length :=
        Finset.sum_le_sum fun e _ => digits_length_mono hb (cost_natAbs_le_maxCost' I e)
    _ = I.m * (Nat.digits (2 ^ k) I.maxCost).length := by simp

/-- Canonical capacity limb lists of `R'`. -/
def resCapLimbs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) : List (List ℕ) :=
  let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  List.ofFn fun j : Fin R'.m => Nat.digits (2 ^ narrowLimbWidth I) (R'.capacity j)

/-- Capacity limb pointers of `R'` (forward arcs in `pCapBuf2`, reverse arcs in `pFeasFlow`). -/
def resCapPtrs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCapBuf2 pFeasFlow L : ℕ) : List ℕ :=
  (resFwdPos I hv f I.m).map (fun e => pCapBuf2 + e.val * L) ++
  (resRevPos I f I.m).map (fun e => pFeasFlow + e.val * L)

/-- Canonical cost limb lists of `R'`. -/
def resCostLimbs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) : List (List ℕ) :=
  let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  List.ofFn fun j : Fin R'.m => Nat.digits (2 ^ narrowLimbWidth I) (R'.cost j).natAbs

/-- Sequential cost-limb pointers of `R'` inside `pCostBuf2`. -/
def resCostPtrs (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (pCostBuf2 : ℕ) : List ℕ :=
  let cl := resCostLimbs I hv f
  List.ofFn fun j : Fin cl.length => pCostBuf2 + ((cl.take j.val).map List.length).sum

theorem resCapPtrs_length (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCapBuf2 pFeasFlow L : ℕ) :
    (resCapPtrs I hv f pCapBuf2 pFeasFlow L).length =
      ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m := by
  simp only [resCapPtrs, List.length_append, List.length_map]
  exact (res_m_eq I hv f).symm

theorem resCapLimbs_length (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    (resCapLimbs I hv f).length =
      ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m := by
  simp [resCapLimbs]

theorem resCostLimbs_length (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    (resCostLimbs I hv f).length =
      ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m := by
  simp [resCostLimbs]

theorem resCostPtrs_length (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (pCostBuf2 : ℕ) :
    (resCostPtrs I hv f pCostBuf2).length =
      ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m := by
  simp [resCostPtrs, resCostLimbs]

/-- Cost-limb list built from any list of edge indices `es` (for Pass Fwd / Pass Rev). -/
def edgeCostLimbList (I : Instance) (es : List (Fin I.m)) : List (List ℕ) :=
  es.map fun e => Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs

theorem edgeCostLimbList_flatten_len_le (I : Instance) (es : List (Fin I.m)) (hn : es.Nodup) :
    (edgeCostLimbList I es).flatten.length ≤ totCostLimbs I := by
  rw [List.length_flatten]
  unfold edgeCostLimbList totCostLimbs
  rw [List.map_map]
  simp only [Function.comp_def]
  have hsum : (es.map (fun e => (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length)).sum =
      ∑ e ∈ es.toFinset, (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length := by
    exact (List.sum_toFinset _ hn).symm
  rw [hsum]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private theorem ofFn_posIdx_map {α : Type} (J : Circulation) (g : Fin J.m → α) :
    (List.ofFn fun j : Fin J.withoutZeroEdges.m => g (J.positiveIndex j)) =
      J.positiveEdges.map g := by
  apply List.ext_getElem (by simp)
  intro j _ _; simp [Circulation.positiveIndex]

theorem resCostLimbs_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    edgeCostLimbList I (resFwdPos I hv f I.m) ++ edgeCostLimbList I (resRevPos I f I.m) =
      resCostLimbs I hv f := by
  unfold resCostLimbs edgeCostLimbList
  rw [ofFn_posIdx_map ((FlowReduction.shiftedGraph I hv).residual f)
        (fun e => Nat.digits (2 ^ narrowLimbWidth I)
          (((FlowReduction.shiftedGraph I hv).residual f).cost e).natAbs),
      res_positiveEdges_eq I hv f, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right, Int.natAbs_neg]

theorem resTails_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    (resFwdPos I hv f I.m).map (fun e => (I.edge e).tail) ++
      (resRevPos I f I.m).map (fun e => (I.edge e).head) =
      List.ofFn fun j : Fin R'.m => (R'.tail j).val := by
  dsimp only
  rw [ofFn_posIdx_map ((FlowReduction.shiftedGraph I hv).residual f)
        (fun e => (((FlowReduction.shiftedGraph I hv).residual f).tail e).val),
      res_positiveEdges_eq I hv f, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right, FlowReduction.shiftedGraph]

theorem resHeads_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    (resFwdPos I hv f I.m).map (fun e => (I.edge e).head) ++
      (resRevPos I f I.m).map (fun e => (I.edge e).tail) =
      List.ofFn fun j : Fin R'.m => (R'.head j).val := by
  dsimp only
  rw [ofFn_posIdx_map ((FlowReduction.shiftedGraph I hv).residual f)
        (fun e => (((FlowReduction.shiftedGraph I hv).residual f).head e).val),
      res_positiveEdges_eq I hv f, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right, FlowReduction.shiftedGraph]

theorem resCapLens_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let k := narrowLimbWidth I
    (resFwdPos I hv f I.m).map (fun e => (Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity e : ℤ) - f e).toNat).length) ++
      (resRevPos I f I.m).map (fun e => (Nat.digits (2 ^ k) (f e).toNat).length) =
      (resCapLimbs I hv f).map List.length := by
  dsimp only
  unfold resCapLimbs
  rw [ofFn_posIdx_map ((FlowReduction.shiftedGraph I hv).residual f)
        (fun e => Nat.digits (2 ^ narrowLimbWidth I)
          (((FlowReduction.shiftedGraph I hv).residual f).capacity e)),
      res_positiveEdges_eq I hv f, List.map_append, List.map_append,
      List.map_map, List.map_map, List.map_map, List.map_map]
  simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right]

theorem resCostSigns_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    (resFwdPos I hv f I.m).map (fun e => if (I.edge e).cost < 0 then 1 else 0) ++
      (resRevPos I f I.m).map (fun e => if -(I.edge e).cost < 0 then 1 else 0) =
      List.ofFn fun j : Fin R'.m => if R'.cost j < 0 then 1 else 0 := by
  dsimp only
  rw [ofFn_posIdx_map ((FlowReduction.shiftedGraph I hv).residual f)
        (fun e => if ((FlowReduction.shiftedGraph I hv).residual f).cost e < 0 then 1 else 0),
      res_positiveEdges_eq I hv f, List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right, FlowReduction.shiftedGraph]

theorem resCostLens_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let k := narrowLimbWidth I
    (resFwdPos I hv f I.m).map (fun e => (Nat.digits (2 ^ k) (I.edge e).cost.natAbs).length) ++
      (resRevPos I f I.m).map (fun e => (Nat.digits (2 ^ k) (I.edge e).cost.natAbs).length) =
      (resCostLimbs I hv f).map List.length := by
  rw [← resCostLimbs_eq_two_pass I hv f, List.map_append]
  simp [edgeCostLimbList, Function.comp_def]

theorem resCostPtrs_eq_two_pass (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (pCostBuf2 : ℕ) :
    let fwd := resFwdPos I hv f I.m
    let rev := resRevPos I f I.m
    let fwdCL := edgeCostLimbList I fwd
    let revCL := edgeCostLimbList I rev
    List.ofFn (fun t : Fin fwd.length =>
        pCostBuf2 + ((fwdCL.take t.val).map List.length).sum) ++
      List.ofFn (fun t : Fin rev.length =>
        pCostBuf2 + (fwdCL.map List.length).sum + ((revCL.take t.val).map List.length).sum) =
      resCostPtrs I hv f pCostBuf2 := by
  dsimp only
  set fwd := resFwdPos I hv f I.m
  set rev := resRevPos I f I.m
  set fwdCL := edgeCostLimbList I fwd
  set revCL := edgeCostLimbList I rev
  have hcl : fwdCL ++ revCL = resCostLimbs I hv f := resCostLimbs_eq_two_pass I hv f
  have hf_len : fwdCL.length = fwd.length := by simp [fwdCL, edgeCostLimbList]
  have hr_len : revCL.length = rev.length := by simp [revCL, edgeCostLimbList]
  apply List.ext_getElem
  · simp only [resCostPtrs, List.length_append, List.length_ofFn, ← hcl, hf_len, hr_len]
  · intro j h1 h2
    simp only [resCostPtrs, List.getElem_ofFn]
    by_cases hlt : j < fwd.length
    · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]
      simp only [← hcl]
      rw [List.take_append_of_le_length (by omega)]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      simp only [← hcl, List.length_ofFn]
      rw [List.take_append, List.take_of_length_le (l := fwdCL) (by omega),
          List.map_append, List.sum_append, hf_len, Nat.add_assoc]

/-! ### Reversible heap splits for `pCapBuf2 * pFeasFlow` and `pCostBuf2` -/

/-- Splitting a flattened list of limb arrays into a product of `Assn.list` atoms. -/
theorem list_flatten_eq_prod (base : ℕ) (xss : List (List ℕ)) :
    Assn.list base xss.flatten =
      ∏ j ∈ Finset.range xss.length,
        Assn.list (base + ((xss.take j).map List.length).sum) (xss.getD j []) := by
  induction xss using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
    rw [List.flatten_append, List.flatten_singleton, Assn.list_append, ih,
        List.length_append, List.length_singleton, Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      have hlt : j < xs.length := Finset.mem_range.mp hj
      rw [List.take_append_of_le_length (le_of_lt hlt),
          List.getD_eq_getElem (xs ++ [a]) _ (by simp; omega),
          List.getElem_append_left hlt,
          ← List.getD_eq_getElem xs _ hlt]
    · rw [List.length_flatten, List.take_append_of_le_length (le_refl _), List.take_length,
          List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]

/-- Exact split of `pCostBuf2` into the cost-limb product of `stage1Input R'` plus the unused tail. -/
theorem res_split_costBuf (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (pCostBuf2 : ℕ) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    let flat := (resCostLimbs I hv f).flatten
    Assn.list pCostBuf2 (flat ++ List.replicate (2 * totCostLimbs I - flat.length) 0) =
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCostPtrs I hv f pCostBuf2).getD j 0)
          ((resCostLimbs I hv f).getD j [])) *
      Assn.list (pCostBuf2 + flat.length) (List.replicate (2 * totCostLimbs I - flat.length) 0) := by
  dsimp only
  set R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  set cl := resCostLimbs I hv f
  have hlen : cl.length = R'.m := resCostLimbs_length I hv f
  rw [Assn.list_append, list_flatten_eq_prod]
  congr 1
  rw [hlen]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hlt : j < R'.m := Finset.mem_range.mp hj
  have hptr : (resCostPtrs I hv f pCostBuf2).getD j 0 =
      pCostBuf2 + ((cl.take j).map List.length).sum := by
    rw [List.getD_eq_getElem _ _ (by rw [resCostPtrs_length]; exact hlt)]
    simp [resCostPtrs, cl]
  rw [hptr]

/-- Reversible split of `pCapBuf2 * pFeasFlow` into the capacity-limb product of `stage1Input R'`
plus a framed remainder `R`. -/
theorem res_split_capBuf_feasFlow (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (pCapBuf2 pFeasFlow L : ℕ)
    (hfwdLen : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I)
        (((FlowReduction.shiftedGraph I hv).capacity e : ℤ) - f e).toNat).length ≤ L)
    (hrevLen : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) (f e).toNat).length ≤ L) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    let k := narrowLimbWidth I
    ∃ R : Assn,
      (∏ e ∈ Finset.range I.m,
        Assn.list (pCapBuf2 + e * L)
          (if h : e < I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph I hv).capacity ⟨e, h⟩ : ℤ) - f ⟨e, h⟩).toNat) L
          else [])) *
      (∏ e ∈ Finset.range I.m,
        Assn.list (pFeasFlow + e * L)
          (if h : e < I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, h⟩).toNat) L else [])) =
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j [])) * R := by
  dsimp only
  set R := (FlowReduction.shiftedGraph I hv).residual f
  set R' := R.withoutZeroEdges
  set fwd := resFwdPos I hv f I.m
  set rev := resRevPos I f I.m
  set k := narrowLimbWidth I
  have hpe := res_positiveEdges_eq I hv f
  have hm := res_m_eq I hv f
  have hnodup_fwd : (fwd.map Fin.val).Nodup :=
    (resFwdPos_nodup I hv f I.m).map Fin.val_injective
  have hnodup_rev : (rev.map Fin.val).Nodup :=
    (resRevPos_nodup I f I.m).map Fin.val_injective
  let rowFwd : ℕ → ℕ := fun e =>
    if h : e < I.m then
      (((FlowReduction.shiftedGraph I hv).capacity ⟨e, h⟩ : ℤ) - f ⟨e, h⟩).toNat
    else 0
  let rowRev : ℕ → ℕ := fun e => if h : e < I.m then (f ⟨e, h⟩).toNat else 0
  obtain ⟨R1, hR1⟩ := prod_padLimbs_split_finset (base := pCapBuf2) (L := L) (k := k)
    Fin.val rowFwd fwd (Finset.range I.m) hnodup_fwd
    (fun e _ => Finset.mem_range.mpr e.isLt)
    (fun e he => by
      have hlt := Finset.mem_range.mp he
      simp only [rowFwd, dite_eq_left hlt]; exact hfwdLen ⟨e, hlt⟩)
  obtain ⟨R2, hR2⟩ := prod_padLimbs_split_finset (base := pFeasFlow) (L := L) (k := k)
    Fin.val rowRev rev (Finset.range I.m) hnodup_rev
    (fun e _ => Finset.mem_range.mpr e.isLt)
    (fun e he => by
      have hlt := Finset.mem_range.mp he
      simp only [rowRev, dite_eq_left hlt]; exact hrevLen ⟨e, hlt⟩)
  have hprod_fwd :
      (∏ j ∈ Finset.range fwd.length,
        Assn.list ((fwd.map fun e => pCapBuf2 + e.val * L).getD j 0)
          ((fwd.map fun e => Nat.digits (2 ^ k) (rowFwd e.val)).getD j [])) =
      ∏ j ∈ Finset.range fwd.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j []) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hlt : j < fwd.length := Finset.mem_range.mp hj
    have hlt_R : j < R'.m := by
      change j < ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m
      rw [hm]; exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    have hptr1 : (fwd.map fun e => pCapBuf2 + e.val * L).getD j 0 = pCapBuf2 + (fwd[j]'hlt).val * L := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map]
    have hptr2 : (resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0 = pCapBuf2 + (fwd[j]'hlt).val * L := by
      rw [List.getD_eq_getElem _ _ (by rw [resCapPtrs_length]; exact hlt_R)]
      simp only [resCapPtrs]
      rw [List.getElem_append_left (by simp [fwd, hlt]), List.getElem_map]
    have hlim1 : (fwd.map fun e => Nat.digits (2 ^ k) (rowFwd e.val)).getD j [] =
        Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity (fwd[j]'hlt) : ℤ) - f (fwd[j]'hlt)).toNat := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map]
      simp only [rowFwd, dite_eq_left (fwd[j]'hlt).isLt, Fin.eta]
    have hlim2 : (resCapLimbs I hv f).getD j [] =
        Nat.digits (2 ^ k) (((FlowReduction.shiftedGraph I hv).capacity (fwd[j]'hlt) : ℤ) - f (fwd[j]'hlt)).toNat := by
      rw [List.getD_eq_getElem _ _ (by rw [resCapLimbs_length]; exact hlt_R)]
      simp only [resCapLimbs, List.getElem_ofFn]
      have hidx : R.positiveIndex ⟨j, hlt_R⟩ = Fin.castAdd I.m (fwd[j]'hlt) := by
        unfold Circulation.positiveIndex
        rw [List.getElem_of_eq hpe hlt_R, List.getElem_append_left (by simp [fwd, hlt])]; simp [fwd]
      change Nat.digits (2 ^ k) (R.capacity (R.positiveIndex ⟨j, hlt_R⟩)) = _
      rw [hidx]; simp only [R, Fin.addCases_left]
    rw [hptr1, hptr2, hlim1, hlim2]
  have hprod_rev :
      (∏ t ∈ Finset.range rev.length,
        Assn.list ((rev.map fun e => pFeasFlow + e.val * L).getD t 0)
          ((rev.map fun e => Nat.digits (2 ^ k) (rowRev e.val)).getD t [])) =
      ∏ t ∈ Finset.range rev.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD (fwd.length + t) 0)
          ((resCapLimbs I hv f).getD (fwd.length + t) []) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    have hlt : t < rev.length := Finset.mem_range.mp ht
    have hlt_R : fwd.length + t < R'.m := by
      change fwd.length + t < ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m
      rw [hm]; exact Nat.add_lt_add_left hlt _
    have hptr1 : (rev.map fun e => pFeasFlow + e.val * L).getD t 0 = pFeasFlow + (rev[t]'hlt).val * L := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map]
    have hptr2 : (resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD (fwd.length + t) 0 =
        pFeasFlow + (rev[t]'hlt).val * L := by
      rw [List.getD_eq_getElem _ _ (by rw [resCapPtrs_length]; exact hlt_R)]
      simp only [resCapPtrs]
      rw [List.getElem_append_right (by simp [fwd]), List.getElem_map]
      simp [fwd, rev]
    have hlim1 : (rev.map fun e => Nat.digits (2 ^ k) (rowRev e.val)).getD t [] =
        Nat.digits (2 ^ k) (f (rev[t]'hlt)).toNat := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map]
      simp only [rowRev, dite_eq_left (rev[t]'hlt).isLt, Fin.eta]
    have hlim2 : (resCapLimbs I hv f).getD (fwd.length + t) [] =
        Nat.digits (2 ^ k) (f (rev[t]'hlt)).toNat := by
      rw [List.getD_eq_getElem _ _ (by rw [resCapLimbs_length]; exact hlt_R)]
      simp only [resCapLimbs, List.getElem_ofFn]
      have hidx : R.positiveIndex ⟨fwd.length + t, hlt_R⟩ = Fin.natAdd I.m (rev[t]'hlt) := by
        unfold Circulation.positiveIndex
        rw [List.getElem_of_eq hpe hlt_R, List.getElem_append_right (by simp [fwd])]
        simp [fwd, rev]
      change Nat.digits (2 ^ k) (R.capacity (R.positiveIndex ⟨fwd.length + t, hlt_R⟩)) = _
      rw [hidx]; simp only [R, Fin.addCases_right]
    rw [hptr1, hptr2, hlim1, hlim2]
  have hjoin :
      (∏ j ∈ Finset.range R'.m,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j [])) =
      (∏ j ∈ Finset.range fwd.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j [])) *
      (∏ t ∈ Finset.range rev.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD (fwd.length + t) 0)
          ((resCapLimbs I hv f).getD (fwd.length + t) [])) := by
    rw [hm, Finset.prod_range_add]
  have h1_congr :
      (∏ e ∈ Finset.range I.m,
        Assn.list (pCapBuf2 + e * L)
          (if h : e < I.m then
            padLimbs (Nat.digits (2 ^ k)
              (((FlowReduction.shiftedGraph I hv).capacity ⟨e, h⟩ : ℤ) - f ⟨e, h⟩).toNat) L
          else [])) =
      (∏ e ∈ Finset.range I.m,
        Assn.list (pCapBuf2 + e * L) (padLimbs (Nat.digits (2 ^ k) (rowFwd e)) L)) := by
    refine Finset.prod_congr rfl fun e he => ?_
    simp only [rowFwd, dite_eq_left (Finset.mem_range.mp he)]
  have h2_congr :
      (∏ e ∈ Finset.range I.m,
        Assn.list (pFeasFlow + e * L)
          (if h : e < I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨e, h⟩).toNat) L else [])) =
      (∏ e ∈ Finset.range I.m,
        Assn.list (pFeasFlow + e * L) (padLimbs (Nat.digits (2 ^ k) (rowRev e)) L)) := by
    refine Finset.prod_congr rfl fun e he => ?_
    simp only [rowRev, dite_eq_left (Finset.mem_range.mp he)]
  refine ⟨R1 * R2, ?_⟩
  rw [h1_congr, h2_congr, hR1, hR2, hprod_fwd, hprod_rev]
  have hjoin' : (∏ j ∈ Finset.range ((FlowReduction.shiftedGraph I hv).residual f).positiveEdges.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j [])) =
      (∏ j ∈ Finset.range fwd.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD j 0)
          ((resCapLimbs I hv f).getD j [])) *
      (∏ t ∈ Finset.range rev.length,
        Assn.list ((resCapPtrs I hv f pCapBuf2 pFeasFlow L).getD (fwd.length + t) 0)
          ((resCapLimbs I hv f).getD (fwd.length + t) [])) := hjoin
  rw [hjoin']
  ac_rfl

/-! ### Stage 1 limb specifications and scatter identities for `R'` -/

theorem resCapLimbs_spec (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) {w L : ℕ}
    (hk3 : 3 ≤ narrowLimbWidth I) (h2k1 : 2 * narrowLimbWidth I + 1 ≤ w)
    (hL_lt : L < 2 ^ narrowLimbWidth I)
    (hcapLen : ∀ j (_hj : j < ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m),
      ((resCapLimbs I hv f).getD j []).length ≤ L) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    let k := narrowLimbWidth I
    ∀ j (hj : j < R'.m),
      CanonicalLimbs k ((resCapLimbs I hv f).getD j []) ∧
      ((resCapLimbs I hv f).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((resCapLimbs I hv f).getD j []) = R'.capacity ⟨j, hj⟩ := by
  dsimp only
  set R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := by omega
  intro j hj
  have hget : (resCapLimbs I hv f).getD j [] = Nat.digits (2 ^ k) (R'.capacity ⟨j, hj⟩) := by
    rw [List.getD_eq_getElem _ _ (by rw [resCapLimbs_length]; exact hj)]
    simp [resCapLimbs, R', k]
  have hlen_lt : ((resCapLimbs I hv f).getD j []).length < 2 ^ k := by
    have := hcapLen j hj; omega
  refine ⟨?_, limbLen_mul_k_lt_pow_w hk3 h2k1 hlen_lt, ?_⟩
  · rw [hget]; exact digits_canonical hk1 _
  · rw [hget, Nat.ofDigits_digits]

theorem resCostLimbs_spec (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) {w : ℕ}
    (hk3 : 3 ≤ narrowLimbWidth I) (h2k1 : 2 * narrowLimbWidth I + 1 ≤ w) :
    let R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    let k := narrowLimbWidth I
    ∀ j (hj : j < R'.m),
      CanonicalLimbs k ((resCostLimbs I hv f).getD j []) ∧
      ((resCostLimbs I hv f).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((resCostLimbs I hv f).getD j []) = (R'.cost ⟨j, hj⟩).natAbs := by
  dsimp only
  set R' := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := by omega
  have hb : 1 < 2 ^ k := by have := two_le_pow hk1; omega
  intro j hj
  have hget : (resCostLimbs I hv f).getD j [] = Nat.digits (2 ^ k) (R'.cost ⟨j, hj⟩).natAbs := by
    rw [List.getD_eq_getElem _ _ (by rw [resCostLimbs_length]; exact hj)]
    simp [resCostLimbs, R', k]
  have hcost_le : (R'.cost ⟨j, hj⟩).natAbs ≤ I.maxCost :=
    le_trans (Finset.le_sup (f := fun e => (R'.cost e).natAbs) (Finset.mem_univ (⟨j, hj⟩ : Fin R'.m)))
      (residual_withoutZeroEdges_maxCost_le I hv f)
  have hlen_lt : ((resCostLimbs I hv f).getD j []).length < 2 ^ k := by
    rw [hget]
    have h1 := digits_length_mono hb hcost_le
    have h2 : (Nat.digits (2 ^ k) I.maxCost).length + 1 < 2 ^ k := narrowMaxCostLimbs_lt_pow_k I
    omega
  refine ⟨?_, limbLen_mul_k_lt_pow_w hk3 h2k1 hlen_lt, ?_⟩
  · rw [hget]; exact digits_canonical hk1 _
  · rw [hget, Nat.ofDigits_digits]

theorem res_scatterPositive_fwd (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (g' : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → ℤ)
    (j : ℕ) (hj : j < (resFwdPos I hv f I.m).length) :
    let R := (FlowReduction.shiftedGraph I hv).residual f
    let hj' : j < R.withoutZeroEdges.m := by
      have hm := res_m_eq I hv f; change R.withoutZeroEdges.m = _ at hm; omega
    R.scatterPositive g' (Fin.castAdd I.m ((resFwdPos I hv f I.m)[j]'hj)) = g' ⟨j, hj'⟩ := by
  intro R hj'
  have hpe := res_positiveEdges_eq I hv f
  have hreal : ((R.scatterPositive g'
      (Fin.castAdd I.m ((resFwdPos I hv f I.m)[j]'hj)) : ℤ) : ℝ) = (g' ⟨j, hj'⟩ : ℝ) := by
    have h1 := congrFun (R.scatterPositive_cast g')
      (Fin.castAdd I.m ((resFwdPos I hv f I.m)[j]'hj))
    have h2 := congrFun (R.scatterPositive_eq_extendPositive (fun r => (g' r : ℝ)))
      (Fin.castAdd I.m ((resFwdPos I hv f I.m)[j]'hj))
    rw [h1, h2]
    have hidx : R.positiveIndex ⟨j, hj'⟩ = Fin.castAdd I.m ((resFwdPos I hv f I.m)[j]'hj) := by
      unfold Circulation.positiveIndex
      rw [List.getElem_of_eq hpe (by simp; omega), List.getElem_append_left (by simp [hj])]
      simp
    rw [← hidx]
    have hpos : 0 < R.capacity (R.positiveIndex ⟨j, hj'⟩) :=
      (R.mem_positiveEdges_iff _).mp (List.getElem_mem hj')
    rw [Circulation.extendPositive, dite_eq_left hpos, R.positiveSlot_positiveIndex ⟨j, hj'⟩ hpos]
  exact_mod_cast hreal

theorem res_scatterPositive_rev (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (g' : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → ℤ)
    (t : ℕ) (ht : t < (resRevPos I f I.m).length) :
    let R := (FlowReduction.shiftedGraph I hv).residual f
    let fwdLen := (resFwdPos I hv f I.m).length
    let hj' : fwdLen + t < R.withoutZeroEdges.m := by
      have hm := res_m_eq I hv f; change R.withoutZeroEdges.m = _ at hm; omega
    R.scatterPositive g' (Fin.natAdd I.m ((resRevPos I f I.m)[t]'ht)) = g' ⟨fwdLen + t, hj'⟩ := by
  intro R fwdLen hj'
  have hpe := res_positiveEdges_eq I hv f
  have hreal : ((R.scatterPositive g'
      (Fin.natAdd I.m ((resRevPos I f I.m)[t]'ht)) : ℤ) : ℝ) = (g' ⟨fwdLen + t, hj'⟩ : ℝ) := by
    have h1 := congrFun (R.scatterPositive_cast g')
      (Fin.natAdd I.m ((resRevPos I f I.m)[t]'ht))
    have h2 := congrFun (R.scatterPositive_eq_extendPositive (fun r => (g' r : ℝ)))
      (Fin.natAdd I.m ((resRevPos I f I.m)[t]'ht))
    rw [h1, h2]
    have hidx : R.positiveIndex ⟨fwdLen + t, hj'⟩ = Fin.natAdd I.m ((resRevPos I f I.m)[t]'ht) := by
      unfold Circulation.positiveIndex
      rw [List.getElem_of_eq hpe (by simp [fwdLen]; omega), List.getElem_append_right (by simp [fwdLen])]
      simp [fwdLen]
    rw [← hidx]
    have hpos : 0 < R.capacity (R.positiveIndex ⟨fwdLen + t, hj'⟩) :=
      (R.mem_positiveEdges_iff _).mp (List.getElem_mem hj')
    rw [Circulation.extendPositive, dite_eq_left hpos, R.positiveSlot_positiveIndex ⟨fwdLen + t, hj'⟩ hpos]
  exact_mod_cast hreal

theorem res_scatterPositive_not_fwd (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (g' : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → ℤ)
    (e : Fin I.m) (hne : e ∉ resFwdPos I hv f I.m) :
    ((FlowReduction.shiftedGraph I hv).residual f).scatterPositive g' (Fin.castAdd I.m e) = 0 := by
  let R := (FlowReduction.shiftedGraph I hv).residual f
  have hcap0 : R.capacity (Fin.castAdd I.m e) = 0 := by
    by_contra hne0
    apply hne
    unfold resFwdPos
    rw [List.take_of_length_le (by simp)]
    refine List.mem_filter.mpr ⟨List.mem_finRange e, decide_eq_true_eq.mpr ?_⟩
    simp only [R, Fin.addCases_left, FlowReduction.shiftedGraph] at hne0 ⊢
    omega
  have hreal : ((R.scatterPositive g' (Fin.castAdd I.m e) : ℤ) : ℝ) = 0 := by
    have h1 := congrFun (R.scatterPositive_cast g') (Fin.castAdd I.m e)
    have h2 := congrFun (R.scatterPositive_eq_extendPositive (fun r => (g' r : ℝ)))
      (Fin.castAdd I.m e)
    rw [h1, h2, R.extendPositive_zero _ _ hcap0]
  exact_mod_cast hreal

theorem res_scatterPositive_not_rev (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ)
    (g' : Fin ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges.m → ℤ)
    (e : Fin I.m) (hne : e ∉ resRevPos I f I.m) :
    ((FlowReduction.shiftedGraph I hv).residual f).scatterPositive g' (Fin.natAdd I.m e) = 0 := by
  let R := (FlowReduction.shiftedGraph I hv).residual f
  have hcap0 : R.capacity (Fin.natAdd I.m e) = 0 := by
    by_contra hne0
    apply hne
    unfold resRevPos
    rw [List.take_of_length_le (by simp)]
    refine List.mem_filter.mpr ⟨List.mem_finRange e, decide_eq_true_eq.mpr ?_⟩
    simp only [R, Fin.addCases_right] at hne0
    omega
  have hreal : ((R.scatterPositive g' (Fin.natAdd I.m e) : ℤ) : ℝ) = 0 := by
    have h1 := congrFun (R.scatterPositive_cast g') (Fin.natAdd I.m e)
    have h2 := congrFun (R.scatterPositive_eq_extendPositive (fun r => (g' r : ℝ)))
      (Fin.natAdd I.m e)
    rw [h1, h2, R.extendPositive_zero _ _ hcap0]
  exact_mod_cast hreal

end MinCostFlow.NarrowProg
