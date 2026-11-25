module

public import MinCostFlow.NarrowProg.Stage0Stage1
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4 (layout & Pass 1): pruned feasibility circulation `P'`

Characterizes `P' = (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges` as the
concatenation of three scans (`feasOrigPos`, `feasArtPos`, `feasArtNeg`), proves the reversible
heap-splitting lemmas connecting `pShCapBuf`, `pShDemBuf`, and `pOneCells` to `stage1Input P'`,
and verifies `stage0FeasPass1` (emitting the positive-capacity original edges).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Three-pass decomposition of `(buildFeasibilityInstance I hv).positiveEdges` -/

/-- Original edges with positive shifted capacity among the first `i` edges. -/
def feasOrigPos (I : Instance) (hv : I.IsValid) (i : ℕ) : List (Fin I.m) :=
  ((List.finRange I.m).take i).filter (fun e => decide (0 < (FlowReduction.shiftedGraph I hv).capacity e))

/-- Vertices with positive shifted demand among the first `i` vertices. -/
def feasArtPos (I : Instance) (i : ℕ) : List (Fin I.n) :=
  ((List.finRange I.n).take i).filter (fun v => decide (0 < FlowReduction.shiftedDemand I v))

/-- Vertices with negative shifted demand among the first `i` vertices. -/
def feasArtNeg (I : Instance) (i : ℕ) : List (Fin I.n) :=
  ((List.finRange I.n).take i).filter (fun v => decide (FlowReduction.shiftedDemand I v < 0))

theorem feasOrigPos_zero (I : Instance) (hv : I.IsValid) : feasOrigPos I hv 0 = [] := by
  simp [feasOrigPos]

theorem feasArtPos_zero (I : Instance) : feasArtPos I 0 = [] := by
  simp [feasArtPos]

theorem feasArtNeg_zero (I : Instance) : feasArtNeg I 0 = [] := by
  simp [feasArtNeg]

private theorem finRange_take_succ {n i : ℕ} (hi : i < n) :
    (List.finRange n).take (i + 1) = (List.finRange n).take i ++ [⟨i, hi⟩] := by
  rw [List.take_succ_eq_append_getElem (by simp; exact hi)]
  simp

theorem feasOrigPos_succ (I : Instance) (hv : I.IsValid) {i : ℕ} (hi : i < I.m) :
    feasOrigPos I hv (i + 1) =
      feasOrigPos I hv i ++
        (if 0 < (FlowReduction.shiftedGraph I hv).capacity ⟨i, hi⟩ then [⟨i, hi⟩] else []) := by
  unfold feasOrigPos
  rw [finRange_take_succ hi, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem feasArtPos_succ (I : Instance) {i : ℕ} (hi : i < I.n) :
    feasArtPos I (i + 1) =
      feasArtPos I i ++
        (if 0 < FlowReduction.shiftedDemand I ⟨i, hi⟩ then [⟨i, hi⟩] else []) := by
  unfold feasArtPos
  rw [finRange_take_succ hi, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

theorem feasArtNeg_succ (I : Instance) {i : ℕ} (hi : i < I.n) :
    feasArtNeg I (i + 1) =
      feasArtNeg I i ++
        (if FlowReduction.shiftedDemand I ⟨i, hi⟩ < 0 then [⟨i, hi⟩] else []) := by
  unfold feasArtNeg
  rw [finRange_take_succ hi, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]

private theorem finRange_add_eq (a b : ℕ) :
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

/-- Exact 3-pass decomposition of `(buildFeasibilityInstance I hv).positiveEdges`. -/
theorem feas_positiveEdges_eq (I : Instance) (hv : I.IsValid) :
    (FlowReduction.buildFeasibilityInstance I hv).positiveEdges =
      (feasOrigPos I hv I.m).map (Fin.castAdd (I.n + I.n)) ++
      (feasArtPos I I.n).map (fun v => Fin.natAdd I.m (Fin.castAdd I.n v)) ++
      (feasArtNeg I I.n).map (fun v => Fin.natAdd I.m (Fin.natAdd I.n v)) := by
  set P := FlowReduction.buildFeasibilityInstance I hv
  unfold Circulation.positiveEdges
  change (List.finRange (I.m + (I.n + I.n))).filter (fun e => decide (0 < P.capacity e)) = _
  rw [finRange_add_eq I.m (I.n + I.n), finRange_add_eq I.n I.n,
      List.map_append, List.map_map, List.map_map,
      List.filter_append, List.filter_append,
      List.filter_map, List.filter_map, List.filter_map]
  simp only [List.append_assoc]
  have h1 : (List.finRange I.m).filter
      ((fun e => decide (0 < P.capacity e)) ∘ Fin.castAdd (I.n + I.n)) = feasOrigPos I hv I.m := by
    unfold feasOrigPos
    rw [List.take_of_length_le (by simp)]
    apply List.filter_congr; intro e _
    simp [P, Fin.addCases_left]
  have h2 : (List.finRange I.n).filter
      ((fun e => decide (0 < P.capacity e)) ∘ (Fin.natAdd I.m ∘ Fin.castAdd I.n)) =
      feasArtPos I I.n := by
    unfold feasArtPos
    rw [List.take_of_length_le (by simp)]
    apply List.filter_congr; intro v _
    simp only [Function.comp_def, P, Fin.addCases_right, Fin.addCases_left,
      FlowReduction.buildShiftedDemands_eq, decide_eq_decide]
    omega
  have h3 : (List.finRange I.n).filter
      ((fun e => decide (0 < P.capacity e)) ∘ (Fin.natAdd I.m ∘ Fin.natAdd I.n)) =
      feasArtNeg I I.n := by
    unfold feasArtNeg
    rw [List.take_of_length_le (by simp)]
    apply List.filter_congr; intro v _
    simp only [Function.comp_def, P, Fin.addCases_right,
      FlowReduction.buildShiftedDemands_eq, decide_eq_decide]
    omega
  rw [h1, h2, h3]
  simp only [Function.comp_def]

theorem feas_m_eq (I : Instance) (hv : I.IsValid) :
    (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m =
      (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length + (feasArtNeg I I.n).length := by
  change (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.length = _
  rw [feas_positiveEdges_eq I hv]
  simp only [List.length_append, List.length_map]

theorem feas_m_le_three_m (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true) :
    (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m ≤ 3 * I.m := by
  rw [FlowReduction.buildFeasibilityInstance_eq]
  exact FlowReduction.feasibilityInstance_positiveEdges_le_three I hv hiso

theorem feasOrigPos_nodup (I : Instance) (hv : I.IsValid) (i : ℕ) :
    (feasOrigPos I hv i).Nodup :=
  ((List.nodup_finRange I.m).take).filter _

theorem feasArtPos_nodup (I : Instance) (i : ℕ) : (feasArtPos I i).Nodup :=
  ((List.nodup_finRange I.n).take).filter _

theorem feasArtNeg_nodup (I : Instance) (i : ℕ) : (feasArtNeg I i).Nodup :=
  ((List.nodup_finRange I.n).take).filter _

theorem feasOrigPos_pos {I : Instance} {hv : I.IsValid} {i : ℕ} {e : Fin I.m}
    (he : e ∈ feasOrigPos I hv i) : 0 < (FlowReduction.shiftedGraph I hv).capacity e := by
  unfold feasOrigPos at he
  exact decide_eq_true_eq.mp (List.mem_filter.mp he).2

theorem feasArtPos_pos {I : Instance} {i : ℕ} {v : Fin I.n}
    (hv' : v ∈ feasArtPos I i) : 0 < FlowReduction.shiftedDemand I v := by
  unfold feasArtPos at hv'
  exact decide_eq_true_eq.mp (List.mem_filter.mp hv').2

theorem feasArtNeg_neg {I : Instance} {i : ℕ} {v : Fin I.n}
    (hv' : v ∈ feasArtNeg I i) : FlowReduction.shiftedDemand I v < 0 := by
  unfold feasArtNeg at hv'
  exact decide_eq_true_eq.mp (List.mem_filter.mp hv').2

/-! ### Exact `stage1Input` pointer and limb lists for `P'` -/

/-- Capacity pointer for edge `a : Fin P.m` of the feasibility instance. -/
def feasCapPtr (I : Instance) (hv : I.IsValid) (pShCapBuf pShDemBuf L : ℕ)
    (a : Fin (FlowReduction.buildFeasibilityInstance I hv).m) : ℕ :=
  let el := (FlowReduction.shiftedGraph I hv).endpointLabels
  Fin.addCases (m := I.m) (n := I.n + I.n)
    (fun e => pShCapBuf + e.val * L)
    (Fin.addCases (m := I.n) (n := I.n)
      (fun v => pShDemBuf + (el.table v - 1) * L)
      (fun v => pShDemBuf + (el.table v - 1) * L))
    a

/-- Capacity pointers list for `P'`. -/
def feasCapPtrs (I : Instance) (hv : I.IsValid) (pShCapBuf pShDemBuf L : ℕ) : List ℕ :=
  (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.map
    (feasCapPtr I hv pShCapBuf pShDemBuf L)

/-- Canonical capacity limb lists for `P'`. -/
def feasCapLimbs (I : Instance) (hv : I.IsValid) : List (List ℕ) :=
  let P := FlowReduction.buildFeasibilityInstance I hv
  P.positiveEdges.map fun a => Nat.digits (2 ^ narrowLimbWidth I) (P.capacity a)

/-- Cost pointer list for `P'`: `0` on original edges, `pOneCells + j` on artificial arcs. -/
def feasCostPtrs (I : Instance) (hv : I.IsValid) (pOneCells : ℕ) : List ℕ :=
  let P := FlowReduction.buildFeasibilityInstance I hv
  let m1Orig := (feasOrigPos I hv I.m).length
  List.ofFn fun j : Fin P.withoutZeroEdges.m =>
    if j.val < m1Orig then 0 else pOneCells + j.val

/-- Canonical cost limb lists for `P'`: `[]` on original edges (cost `0`), `[1]` on artificial
arcs (cost `-1`, `natAbs = 1`). -/
def feasCostLimbs (I : Instance) (hv : I.IsValid) : List (List ℕ) :=
  let P := FlowReduction.buildFeasibilityInstance I hv
  let m1Orig := (feasOrigPos I hv I.m).length
  List.ofFn fun j : Fin P.withoutZeroEdges.m =>
    if j.val < m1Orig then [] else [1]

/-- Exact 3-part formula for `feasCapPtrs`. -/
theorem feasCapPtrs_eq (I : Instance) (hv : I.IsValid) (pShCapBuf pShDemBuf L : ℕ) :
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    feasCapPtrs I hv pShCapBuf pShDemBuf L =
      (feasOrigPos I hv I.m).map (fun e => pShCapBuf + e.val * L) ++
      (feasArtPos I I.n).map (fun v => pShDemBuf + (el.table v - 1) * L) ++
      (feasArtNeg I I.n).map (fun v => pShDemBuf + (el.table v - 1) * L) := by
  unfold feasCapPtrs
  rw [feas_positiveEdges_eq I hv]
  simp only [List.map_append, List.map_map, Function.comp_def, feasCapPtr,
    Fin.addCases_left, Fin.addCases_right]

/-- Exact 3-part formula for `feasCapLimbs.map List.length`. -/
theorem feasCapLens_eq (I : Instance) (hv : I.IsValid) :
    let k := narrowLimbWidth I
    (feasCapLimbs I hv).map List.length =
      (feasOrigPos I hv I.m).map (fun e => (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity e)).length) ++
      (feasArtPos I I.n).map (fun v => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand I v).natAbs).length) ++
      (feasArtNeg I I.n).map (fun v => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand I v).natAbs).length) := by
  dsimp only
  unfold feasCapLimbs; dsimp only
  rw [feas_positiveEdges_eq I hv]
  simp only [List.map_append, List.map_map, Function.comp_def]
  congr 1
  · congr 1
    · apply List.map_congr_left; intro e _
      simp [Fin.addCases_left]
    · apply List.map_congr_left; intro v hv'
      have hp := feasArtPos_pos hv'
      simp only [Fin.addCases_right, Fin.addCases_left, FlowReduction.buildShiftedDemands_eq]
      congr 2; omega
  · apply List.map_congr_left; intro v hv'
    have hn := feasArtNeg_neg hv'
    simp only [Fin.addCases_right, FlowReduction.buildShiftedDemands_eq]
    congr 2; omega

/-- Exact 3-part formula for `P'.tail`. -/
theorem feasTails_eq (I : Instance) (hv : I.IsValid) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    (List.ofFn fun e : Fin P'.m => (P'.tail e).val) =
      (feasOrigPos I hv I.m).map (fun e => (I.edge e).tail) ++
      (feasArtPos I I.n).map (fun _ => I.n) ++
      (feasArtNeg I I.n).map (fun v => v.val) := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  have hof : (List.ofFn fun e : Fin P.withoutZeroEdges.m => (P.withoutZeroEdges.tail e).val) =
      P.positiveEdges.map (fun a => (P.tail a).val) := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp [Circulation.withoutZeroEdges, Circulation.positiveIndex]
  rw [hof, feas_positiveEdges_eq I hv]
  simp only [List.map_append, List.map_map, Function.comp_def, P,
    Fin.addCases_left, Fin.addCases_right]
  rfl

/-- Exact 3-part formula for `P'.head`. -/
theorem feasHeads_eq (I : Instance) (hv : I.IsValid) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    (List.ofFn fun e : Fin P'.m => (P'.head e).val) =
      (feasOrigPos I hv I.m).map (fun e => (I.edge e).head) ++
      (feasArtPos I I.n).map (fun v => v.val) ++
      (feasArtNeg I I.n).map (fun _ => I.n) := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  have hof : (List.ofFn fun e : Fin P.withoutZeroEdges.m => (P.withoutZeroEdges.head e).val) =
      P.positiveEdges.map (fun a => (P.head a).val) := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp [Circulation.withoutZeroEdges, Circulation.positiveIndex]
  rw [hof, feas_positiveEdges_eq I hv]
  simp only [List.map_append, List.map_map, Function.comp_def, P,
    Fin.addCases_left, Fin.addCases_right]
  rfl

/-- Exact 2-part formula for `P'` cost signs (`0` on original edges, `1` on artificial arcs). -/
theorem feasCostSigns_eq (I : Instance) (hv : I.IsValid) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let m1Orig := (feasOrigPos I hv I.m).length
    (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) =
      List.replicate m1Orig 0 ++ List.replicate (P'.m - m1Orig) 1 := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  have hof : (List.ofFn fun e : Fin P.withoutZeroEdges.m => if P.withoutZeroEdges.cost e < 0 then 1 else 0) =
      P.positiveEdges.map (fun a => if P.cost a < 0 then 1 else 0) := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.getElem_ofFn, List.getElem_map, Circulation.withoutZeroEdges, Circulation.positiveIndex]
    rfl
  rw [hof]
  change P.positiveEdges.map (fun a => if P.cost a < 0 then 1 else 0) =
    List.replicate (feasOrigPos I hv I.m).length 0 ++
      List.replicate (P.positiveEdges.length - (feasOrigPos I hv I.m).length) 1
  rw [feas_positiveEdges_eq I hv]
  simp only [List.map_append, List.map_map, Function.comp_def, P,
    Fin.addCases_left, Fin.addCases_right, List.length_append, List.length_map]
  have h0 : (feasOrigPos I hv I.m).map (fun _ => (if (0 : ℤ) < 0 then 1 else 0)) =
      List.replicate (feasOrigPos I hv I.m).length 0 := by simp
  have h1 : (feasArtPos I I.n).map (fun _ => (if (-1 : ℤ) < 0 then 1 else 0)) =
      List.replicate (feasArtPos I I.n).length 1 := by simp
  have h2 : (feasArtNeg I I.n).map (fun _ => (if (-1 : ℤ) < 0 then 1 else 0)) =
      List.replicate (feasArtNeg I I.n).length 1 := by simp
  rw [h0, h1, h2, List.append_assoc, ← List.replicate_add]
  congr 2; omega

theorem feasCostLens_eq (I : Instance) (hv : I.IsValid) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let m1Orig := (feasOrigPos I hv I.m).length
    (feasCostLimbs I hv).map List.length =
      List.replicate m1Orig 0 ++ List.replicate (P'.m - m1Orig) 1 := by
  dsimp only
  have hm : (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.length =
      (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length + (feasArtNeg I I.n).length :=
    feas_m_eq I hv
  apply List.ext_getElem
  · simp [feasCostLimbs]; change (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.length = _; omega
  · intro j hj1 hj2
    simp only [feasCostLimbs, List.getElem_map, List.getElem_ofFn]
    by_cases hlt : j < (feasOrigPos I hv I.m).length
    · rw [ite_eq_left hlt, List.getElem_append_left (by simp; exact hlt), List.getElem_replicate]; rfl
    · rw [ite_eq_right hlt, List.getElem_append_right (by simp; omega), List.getElem_replicate]; rfl

theorem feasCostPtrs_eq (I : Instance) (hv : I.IsValid) (pOneCells : ℕ) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let m1Orig := (feasOrigPos I hv I.m).length
    feasCostPtrs I hv pOneCells =
      List.replicate m1Orig 0 ++
        List.ofFn (fun t : Fin (P'.m - m1Orig) => pOneCells + (m1Orig + t.val)) := by
  dsimp only
  have hm : (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.length =
      (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length + (feasArtNeg I I.n).length :=
    feas_m_eq I hv
  apply List.ext_getElem
  · simp [feasCostPtrs]; change (FlowReduction.buildFeasibilityInstance I hv).positiveEdges.length = _; omega
  · intro j hj1 hj2
    simp only [feasCostPtrs, List.getElem_ofFn]
    by_cases hlt : j < (feasOrigPos I hv I.m).length
    · rw [ite_eq_left hlt, List.getElem_append_left (by simp; exact hlt), List.getElem_replicate]
    · rw [ite_eq_right hlt, List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_replicate]
      omega

theorem feasCostLimbs_spec (I : Instance) (hv : I.IsValid) {w : ℕ}
    (hk1 : 1 ≤ narrowLimbWidth I) (hkw : narrowLimbWidth I < 2 ^ w) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let k := narrowLimbWidth I
    ∀ j (hj : j < P'.m),
      CanonicalLimbs k ((feasCostLimbs I hv).getD j []) ∧
      ((feasCostLimbs I hv).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((feasCostLimbs I hv).getD j []) = (P'.cost ⟨j, hj⟩).natAbs := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  have h2k : 2 ≤ 2 ^ narrowLimbWidth I := two_le_pow hk1
  intro j hj
  have hget : (feasCostLimbs I hv).getD j [] =
      if j < (feasOrigPos I hv I.m).length then [] else [1] := by
    rw [List.getD_eq_getElem _ _ (by simp [feasCostLimbs]; exact hj)]
    simp [feasCostLimbs]
  rw [hget]
  have hidx_pos : (P.positiveIndex ⟨j, hj⟩).val < I.m ↔ j < (feasOrigPos I hv I.m).length := by
    unfold Circulation.positiveIndex
    have hpe : P.positiveEdges =
        (feasOrigPos I hv I.m).map (Fin.castAdd (I.n + I.n)) ++
        (feasArtPos I I.n).map (fun v => Fin.natAdd I.m (Fin.castAdd I.n v)) ++
        (feasArtNeg I I.n).map (fun v => Fin.natAdd I.m (Fin.natAdd I.n v)) :=
      feas_positiveEdges_eq I hv
    have hlen1 : ((feasOrigPos I hv I.m).map (Fin.castAdd (I.n + I.n))).length =
        (feasOrigPos I hv I.m).length := List.length_map _
    constructor
    · intro hlt
      dsimp only at hlt
      by_contra hge
      have hj' : (feasOrigPos I hv I.m).length ≤ j := by omega
      have hpe_len : P.positiveEdges.length =
          (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length + (feasArtNeg I I.n).length :=
        feas_m_eq I hv
      have hj_lt_pe : j < P.positiveEdges.length := hj
      have hge_val : I.m ≤ (P.positiveEdges[j]'hj_lt_pe).val := by
        have hmem : P.positiveEdges[j]'hj_lt_pe ∈
            (feasArtPos I I.n).map (fun v => Fin.natAdd I.m (Fin.castAdd I.n v)) ++
            (feasArtNeg I I.n).map (fun v => Fin.natAdd I.m (Fin.natAdd I.n v)) := by
          have hget_r : P.positiveEdges[j]'hj_lt_pe =
              ((feasArtPos I I.n).map (fun v => Fin.natAdd I.m (Fin.castAdd I.n v)) ++
               (feasArtNeg I I.n).map (fun v => Fin.natAdd I.m (Fin.natAdd I.n v)))[
                j - (feasOrigPos I hv I.m).length]'(by simp; omega) := by
            conv_lhs => simp only [hpe, List.append_assoc]
            rw [List.getElem_append_right (by rw [hlen1]; exact hj')]
            simp [hlen1]
          rw [hget_r]; exact List.getElem_mem _
        rcases List.mem_append.mp hmem with h1 | h2
        · obtain ⟨v, _, hv_eq⟩ := List.mem_map.mp h1
          rw [← hv_eq]; simp [Fin.natAdd]
        · obtain ⟨v, _, hv_eq⟩ := List.mem_map.mp h2
          rw [← hv_eq]; simp [Fin.natAdd]
      omega
    · intro hlt
      dsimp only
      have hget_l : P.positiveEdges[j]'hj =
          ((feasOrigPos I hv I.m).map (Fin.castAdd (I.n + I.n)))[j]'(by rw [hlen1]; exact hlt) := by
        conv_lhs => simp only [hpe, List.append_assoc]
        rw [List.getElem_append_left (by rw [hlen1]; exact hlt)]
      rw [hget_l, List.getElem_map]
      exact ((feasOrigPos I hv I.m)[j]'hlt).isLt
  by_cases hlt : j < (feasOrigPos I hv I.m).length
  · rw [ite_eq_left hlt]
    have hval_lt : (P.positiveIndex ⟨j, hj⟩).val < I.m := hidx_pos.mpr hlt
    have hcast : (FlowReduction.buildFeasibilityInstance I hv).positiveIndex ⟨j, hj⟩ =
        Fin.castAdd (I.n + I.n) ⟨(P.positiveIndex ⟨j, hj⟩).val, hval_lt⟩ := by
      apply Fin.ext; rfl
    rw [hcast, Fin.addCases_left]
    exact ⟨by simpa using digits_canonical hk1 0, by simp, rfl⟩
  · rw [ite_eq_right hlt]
    have hval_ge : I.m ≤ (P.positiveIndex ⟨j, hj⟩).val := by
      have := mt hidx_pos.mp hlt; omega
    have hlt_tot : (P.positiveIndex ⟨j, hj⟩).val < I.m + (I.n + I.n) := (P.positiveIndex ⟨j, hj⟩).isLt
    have hnat : (FlowReduction.buildFeasibilityInstance I hv).positiveIndex ⟨j, hj⟩ =
        Fin.natAdd I.m ⟨(P.positiveIndex ⟨j, hj⟩).val - I.m, by
          change (P.positiveIndex ⟨j, hj⟩).val - I.m < I.n + I.n; omega⟩ := by
      apply Fin.ext
      change ((FlowReduction.buildFeasibilityInstance I hv).positiveIndex ⟨j, hj⟩).val =
        I.m + ((P.positiveIndex ⟨j, hj⟩).val - I.m)
      dsimp only [P] at hval_ge ⊢; omega
    rw [hnat, Fin.addCases_right]
    exact ⟨⟨fun x hx => by simp at hx; omega, fun _ => by simp⟩, by simpa using hkw, by simp⟩

/-! ### Reversible heap splitting for `pShCapBuf`, `pShDemBuf`, and `pOneCells` -/

theorem activeShiftedDemand_of_label_pos {I : Instance} {hv : I.IsValid} {act : List ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    {v : Fin I.n} (hpos : 0 < (FlowReduction.shiftedGraph I hv).endpointLabels.table v) :
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    el.table v - 1 < el.count ∧
      activeShiftedDemand I act (el.table v - 1) = FlowReduction.shiftedDemand I v := by
  set el := (FlowReduction.shiftedGraph I hv).endpointLabels
  have hval := Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)
  have hle : el.table v ≤ el.count := hval.1 v
  have hc_lt : el.table v - 1 < el.count := by omega
  have hc_act : el.table v - 1 < act.length := by rw [hact.1]; exact hc_lt
  refine ⟨hc_lt, ?_⟩
  rw [activeShiftedDemand_eq hact hc_act]
  have htab : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ = el.table v := by
    have := (hact.2 (el.table v - 1) hc_act).2
    omega
  have hne : el.table ⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ ≠ 0 := by omega
  have hv_eq : (⟨act[el.table v - 1]'hc_act, (hact.2 _ hc_act).1⟩ : Fin I.n) = v :=
    hval.2 _ _ hne htab
  rw [hv_eq]

/-- Split a `Finset.prod` of `padLimbs` rows along an injective index list `xs` into
canonical prefixes for `xs` and a framed remainder `R`. -/
theorem prod_padLimbs_split_finset {α : Type} {base L k : ℕ}
    (idx : α → ℕ) (rowVal : ℕ → ℕ)
    (xs : List α) (S : Finset ℕ)
    (hnodup : (xs.map idx).Nodup)
    (hmem : ∀ a ∈ xs, idx a ∈ S)
    (hrowLen : ∀ i ∈ S, (Nat.digits (2 ^ k) (rowVal i)).length ≤ L) :
    ∃ R : Assn,
      (∏ i ∈ S, Assn.list (base + i * L) (padLimbs (Nat.digits (2 ^ k) (rowVal i)) L)) =
      (∏ t ∈ Finset.range xs.length,
        Assn.list ((xs.map fun a => base + idx a * L).getD t 0)
          ((xs.map fun a => Nat.digits (2 ^ k) (rowVal (idx a))).getD t [])) * R := by
  induction xs generalizing S with
  | nil =>
    refine ⟨∏ i ∈ S, Assn.list (base + i * L) (padLimbs (Nat.digits (2 ^ k) (rowVal i)) L), ?_⟩
    simp
  | cons a tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, hnodup_tl⟩ := hnodup
    have ha_mem : idx a ∈ S := hmem a List.mem_cons_self
    have htl_mem : ∀ b ∈ tl, idx b ∈ S.erase (idx a) := fun b hb =>
      Finset.mem_erase.mpr ⟨fun heq => hnotmem (List.mem_map.mpr ⟨b, hb, heq⟩),
        hmem b (List.mem_cons_of_mem a hb)⟩
    have htl_len : ∀ i ∈ S.erase (idx a), (Nat.digits (2 ^ k) (rowVal i)).length ≤ L :=
      fun i hi => hrowLen i (Finset.mem_of_mem_erase hi)
    obtain ⟨R', hR'⟩ := ih (S.erase (idx a)) hnodup_tl htl_mem htl_len
    have hhead_split :
        Assn.list (base + idx a * L) (padLimbs (Nat.digits (2 ^ k) (rowVal (idx a))) L) =
        Assn.list (base + idx a * L) (Nat.digits (2 ^ k) (rowVal (idx a))) *
        Assn.list (base + idx a * L + (Nat.digits (2 ^ k) (rowVal (idx a))).length)
          (List.replicate (L - (Nat.digits (2 ^ k) (rowVal (idx a))).length) 0) := by
      rw [padLimbs, Assn.list_append]
    refine ⟨Assn.list (base + idx a * L + (Nat.digits (2 ^ k) (rowVal (idx a))).length)
      (List.replicate (L - (Nat.digits (2 ^ k) (rowVal (idx a))).length) 0) * R', ?_⟩
    rw [← Finset.mul_prod_erase S _ ha_mem, hhead_split, hR']
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ]
    ac_rfl

/-- Reversible split of `pShCapBuf` and `pShDemBuf` into the exact capacity-limb product of
`stage1Input P'` plus a framed remainder `R`. -/
theorem feas_split_shCap_shDem (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv = true)
    {act : List ℕ} (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    (pShCapBuf pShDemBuf L : ℕ)
    (hcapLen : ∀ e : Fin I.m,
      (Nat.digits (2 ^ narrowLimbWidth I) ((FlowReduction.shiftedGraph I hv).capacity e)).length ≤ L)
    (hdemLen : ∀ c < (FlowReduction.shiftedGraph I hv).endpointLabels.count,
      (Nat.digits (2 ^ narrowLimbWidth I) (activeShiftedDemand I act c).natAbs).length ≤ L) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    let k := narrowLimbWidth I
    ∃ R : Assn,
      (∏ i ∈ Finset.range I.m,
        Assn.list (pShCapBuf + i * L)
          (if hlt : i < I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity ⟨i, hlt⟩)) L
          else [])) *
      (∏ c ∈ Finset.range el.count,
        Assn.list (pShDemBuf + c * L)
          (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand I act c).natAbs) L)) =
      (∏ j ∈ Finset.range P'.m,
        Assn.list ((feasCapPtrs I hv pShCapBuf pShDemBuf L).getD j 0)
          ((feasCapLimbs I hv).getD j [])) * R := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  set el := (FlowReduction.shiftedGraph I hv).endpointLabels
  set k := narrowLimbWidth I
  have hPeq := FlowReduction.buildFeasibilityInstance_eq I hv
  have hval : el.Valid := Circulation.endpointLabels_valid (FlowReduction.shiftedGraph I hv)
  -- Split `pShCapBuf` along `feasOrigPos I hv I.m`
  let capRow : ℕ → ℕ := fun i =>
    if hlt : i < I.m then (FlowReduction.shiftedGraph I hv).capacity ⟨i, hlt⟩ else 0
  have hcap_rew :
      (∏ i ∈ Finset.range I.m,
        Assn.list (pShCapBuf + i * L)
          (if hlt : i < I.m then
            padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity ⟨i, hlt⟩)) L
          else [])) =
      (∏ i ∈ Finset.range I.m,
        Assn.list (pShCapBuf + i * L) (padLimbs (Nat.digits (2 ^ k) (capRow i)) L)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hlt : i < I.m := Finset.mem_range.mp hi
    simp only [capRow, dite_eq_left hlt]
  have horig_nodup : ((feasOrigPos I hv I.m).map Fin.val).Nodup :=
    (feasOrigPos_nodup I hv I.m).map Fin.val_injective
  obtain ⟨R1, hR1⟩ := prod_padLimbs_split_finset (base := pShCapBuf) (L := L) (k := k)
    Fin.val capRow (feasOrigPos I hv I.m) (Finset.range I.m) horig_nodup
    (fun e _ => Finset.mem_range.mpr e.isLt)
    (fun i hi => by
      have hlt : i < I.m := Finset.mem_range.mp hi
      simp only [capRow, dite_eq_left hlt]; exact hcapLen ⟨i, hlt⟩)
  -- Split `pShDemBuf` along `feasArtPos I I.n ++ feasArtNeg I I.n`
  let artList : List (Fin I.n) := feasArtPos I I.n ++ feasArtNeg I I.n
  let demRow : ℕ → ℕ := fun c => (activeShiftedDemand I act c).natAbs
  have hart_pos : ∀ v ∈ artList, 0 < el.table v := by
    intro v hv'
    rcases List.mem_append.mp hv' with hp | hn
    · exact FlowReduction.shiftedDemand_support I hv hiso v (ne_of_gt (feasArtPos_pos hp))
    · exact FlowReduction.shiftedDemand_support I hv hiso v (ne_of_lt (feasArtNeg_neg hn))
  have hart_nodup : (artList.map fun v => el.table v - 1).Nodup := by
    have hdisj : ∀ a ∈ feasArtPos I I.n, ∀ b ∈ feasArtNeg I I.n, a ≠ b := by
      intro a ha b hb heq
      subst heq
      have h1 := feasArtPos_pos ha
      have h2 := feasArtNeg_neg hb
      omega
    have hl_nodup : artList.Nodup :=
      List.nodup_append.mpr ⟨feasArtPos_nodup I I.n, feasArtNeg_nodup I I.n, hdisj⟩
    refine List.nodup_map_iff_inj_on hl_nodup |>.mpr ?_
    intro u hu v hv' heq
    have hpu := hart_pos u hu
    have hpv := hart_pos v hv'
    have htab : el.table u = el.table v := by omega
    exact hval.2 u v (by omega) htab
  obtain ⟨R2, hR2⟩ := prod_padLimbs_split_finset (base := pShDemBuf) (L := L) (k := k)
    (fun v => el.table v - 1) demRow artList (Finset.range el.count) hart_nodup
    (fun v hv' => Finset.mem_range.mpr (activeShiftedDemand_of_label_pos hact (hart_pos v hv')).1)
    (fun c hc => hdemLen c (Finset.mem_range.mp hc))
  -- Identify the two mapped lists with `feasCapPtrs` and `feasCapLimbs`
  have hptrs :
      feasCapPtrs I hv pShCapBuf pShDemBuf L =
      (feasOrigPos I hv I.m).map (fun e => pShCapBuf + e.val * L) ++
      artList.map (fun v => pShDemBuf + (el.table v - 1) * L) := by
    rw [feasCapPtrs_eq]; simp [artList, el, List.map_append, List.append_assoc]
  have hlimbs :
      feasCapLimbs I hv =
      (feasOrigPos I hv I.m).map (fun e => Nat.digits (2 ^ k) (capRow e.val)) ++
      artList.map (fun v => Nat.digits (2 ^ k) (demRow (el.table v - 1))) := by
    unfold feasCapLimbs; dsimp only
    rw [feas_positiveEdges_eq I hv]
    simp only [artList, List.map_append, List.map_map, Function.comp_def, List.append_assoc]
    congr 1
    · apply List.map_congr_left; intro e _
      simp only [capRow, dite_eq_left e.isLt, Fin.addCases_left, k]
    · congr 1
      · apply List.map_congr_left; intro v hv'
        have hp := feasArtPos_pos hv'
        have hpos := FlowReduction.shiftedDemand_support I hv hiso v (ne_of_gt hp)
        have hdem : activeShiftedDemand I act (el.table v - 1) = FlowReduction.shiftedDemand I v :=
          (activeShiftedDemand_of_label_pos hact hpos).2
        simp only [demRow, hdem, Fin.addCases_right, Fin.addCases_left,
          FlowReduction.buildShiftedDemands_eq, k]
        congr 1; omega
      · apply List.map_congr_left; intro v hv'
        have hn := feasArtNeg_neg hv'
        have hpos := FlowReduction.shiftedDemand_support I hv hiso v (ne_of_lt hn)
        have hdem : activeShiftedDemand I act (el.table v - 1) = FlowReduction.shiftedDemand I v :=
          (activeShiftedDemand_of_label_pos hact hpos).2
        simp only [demRow, hdem, Fin.addCases_right, FlowReduction.buildShiftedDemands_eq, k]
        congr 1; omega
  have hm_eq : P.withoutZeroEdges.m = (feasOrigPos I hv I.m).length + artList.length := by
    rw [feas_m_eq]; simp [artList, Nat.add_assoc]
  have hjoin :
      (∏ j ∈ Finset.range P.withoutZeroEdges.m,
        Assn.list ((feasCapPtrs I hv pShCapBuf pShDemBuf L).getD j 0)
          ((feasCapLimbs I hv).getD j [])) =
      (∏ t ∈ Finset.range (feasOrigPos I hv I.m).length,
        Assn.list (((feasOrigPos I hv I.m).map fun e => pShCapBuf + e.val * L).getD t 0)
          (((feasOrigPos I hv I.m).map fun e => Nat.digits (2 ^ k) (capRow e.val)).getD t [])) *
      (∏ t ∈ Finset.range artList.length,
        Assn.list ((artList.map fun v => pShDemBuf + (el.table v - 1) * L).getD t 0)
          ((artList.map fun v => Nat.digits (2 ^ k) (demRow (el.table v - 1))).getD t [])) := by
    rw [hm_eq, Finset.prod_range_add, hptrs, hlimbs]
    congr 1
    · refine Finset.prod_congr rfl fun t ht => ?_
      have hlt : t < (feasOrigPos I hv I.m).length := Finset.mem_range.mp ht
      congr 1
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; exact hlt),
            List.getElem_append_left (by simp; exact hlt)]
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; exact hlt),
            List.getElem_append_left (by simp; exact hlt)]
    · refine Finset.prod_congr rfl fun t ht => ?_
      have hlt : t < artList.length := Finset.mem_range.mp ht
      congr 1
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; exact hlt),
            List.getElem_append_right (by simp)]
        simp
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; exact hlt),
            List.getElem_append_right (by simp)]
        simp
  refine ⟨R1 * R2, ?_⟩
  rw [hcap_rew, hR1, hR2, hjoin]
  ac_rfl

private theorem prod_range_replicate_one (base len : ℕ) :
    (∏ t ∈ Finset.range len, (base + t ↦ 1)) = Assn.list base (List.replicate len 1) := by
  induction len generalizing base with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ', List.replicate_succ, Assn.list_cons, add_zero, mul_comm]
    congr 1
    have := ih (base + 1)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Reversible split of `pOneCells` into the cost-limb product of `stage1Input P'` plus the two
unused zero slices. -/
theorem feas_split_oneCells (I : Instance) (hv : I.IsValid)
    (_hiso : FlowReduction.isolatedCheck I hv = true) (pOneCells : ℕ) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let m1Orig := (feasOrigPos I hv I.m).length
    Assn.list pOneCells
        (List.replicate m1Orig 0 ++ List.replicate (P'.m - m1Orig) 1 ++
          List.replicate (3 * I.m - P'.m) 0) =
      (∏ j ∈ Finset.range P'.m,
        Assn.list ((feasCostPtrs I hv pOneCells).getD j 0)
          ((feasCostLimbs I hv).getD j [])) *
      Assn.list pOneCells (List.replicate m1Orig 0) *
      Assn.list (pOneCells + m1Orig + (P'.m - m1Orig))
        (List.replicate (3 * I.m - P'.m) 0) := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  have hm_eq : P.withoutZeroEdges.m =
      (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length + (feasArtNeg I I.n).length :=
    feas_m_eq I hv
  have hm_ge : (feasOrigPos I hv I.m).length ≤ P.withoutZeroEdges.m := by omega
  have hprod :
      (∏ j ∈ Finset.range P.withoutZeroEdges.m,
        Assn.list ((feasCostPtrs I hv pOneCells).getD j 0)
          ((feasCostLimbs I hv).getD j [])) =
      Assn.list (pOneCells + (feasOrigPos I hv I.m).length)
        (List.replicate (P.withoutZeroEdges.m - (feasOrigPos I hv I.m).length) 1) := by
    have hsplit : P.withoutZeroEdges.m =
        (feasOrigPos I hv I.m).length + (P.withoutZeroEdges.m - (feasOrigPos I hv I.m).length) := by omega
    conv_lhs => rw [hsplit, Finset.prod_range_add]
    have h1 : (∏ j ∈ Finset.range (feasOrigPos I hv I.m).length,
        Assn.list ((feasCostPtrs I hv pOneCells).getD j 0) ((feasCostLimbs I hv).getD j [])) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hlt : j < (feasOrigPos I hv I.m).length := Finset.mem_range.mp hj
      have hget : (feasCostLimbs I hv).getD j [] = [] := by
        rw [List.getD_eq_getElem _ _ (by
          simp only [feasCostLimbs, List.length_ofFn]
          change j < P.withoutZeroEdges.m; omega)]
        simp [feasCostLimbs, hlt]
      rw [hget, Assn.list_nil]
    have h2 : (∏ t ∈ Finset.range (P.withoutZeroEdges.m - (feasOrigPos I hv I.m).length),
        Assn.list ((feasCostPtrs I hv pOneCells).getD ((feasOrigPos I hv I.m).length + t) 0)
          ((feasCostLimbs I hv).getD ((feasOrigPos I hv I.m).length + t) [])) =
        ∏ t ∈ Finset.range (P.withoutZeroEdges.m - (feasOrigPos I hv I.m).length),
          (pOneCells + (feasOrigPos I hv I.m).length + t ↦ 1) := by
      refine Finset.prod_congr rfl fun t ht => ?_
      have hlt : (feasOrigPos I hv I.m).length + t < P.withoutZeroEdges.m := by
        have := Finset.mem_range.mp ht; omega
      have hptr : (feasCostPtrs I hv pOneCells).getD ((feasOrigPos I hv I.m).length + t) 0 =
          pOneCells + ((feasOrigPos I hv I.m).length + t) := by
        rw [List.getD_eq_getElem _ _ (by
          simp only [feasCostPtrs, List.length_ofFn]
          exact hlt)]
        simp [feasCostPtrs]
      have hlim : (feasCostLimbs I hv).getD ((feasOrigPos I hv I.m).length + t) [] = [1] := by
        rw [List.getD_eq_getElem _ _ (by
          simp only [feasCostLimbs, List.length_ofFn]
          exact hlt)]
        simp [feasCostLimbs]
      rw [hptr, hlim, Assn.list_cons, Assn.list_nil, mul_one, Nat.add_assoc]
    rw [h1, one_mul, h2, prod_range_replicate_one]
  rw [Assn.list_append, Assn.list_append, List.length_append, List.length_replicate,
      List.length_replicate, hprod]
  simp only [Nat.add_assoc]
  ac_rfl

/-- Canonicality, bit-width, and value correctness of `feasCapLimbs`. -/
theorem feasCapLimbs_spec (I : Instance) (hv : I.IsValid) {w L : ℕ}
    (hk3 : 3 ≤ narrowLimbWidth I) (h2k1 : 2 * narrowLimbWidth I + 1 ≤ w)
    (hL_lt : L < 2 ^ narrowLimbWidth I)
    (hcapLen : ∀ j (_hj : j < (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m),
      ((feasCapLimbs I hv).getD j []).length ≤ L) :
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let k := narrowLimbWidth I
    ∀ j (hj : j < P'.m),
      CanonicalLimbs k ((feasCapLimbs I hv).getD j []) ∧
      ((feasCapLimbs I hv).getD j []).length * k < 2 ^ w ∧
      Nat.ofDigits (2 ^ k) ((feasCapLimbs I hv).getD j []) = P'.capacity ⟨j, hj⟩ := by
  dsimp only
  set P := FlowReduction.buildFeasibilityInstance I hv
  set k := narrowLimbWidth I
  have hk1 : 1 ≤ k := by omega
  intro j hj
  have hget : (feasCapLimbs I hv).getD j [] =
      Nat.digits (2 ^ k) (P.withoutZeroEdges.capacity ⟨j, hj⟩) := by
    rw [List.getD_eq_getElem _ _ (by simp [feasCapLimbs]; exact hj)]
    simp [feasCapLimbs, Circulation.positiveIndex, P, k]
  have hlen_lt : ((feasCapLimbs I hv).getD j []).length < 2 ^ k := by
    have := hcapLen j hj; omega
  refine ⟨?_, limbLen_mul_k_lt_pow_w hk3 h2k1 hlen_lt, ?_⟩
  · rw [hget]; exact digits_canonical hk1 _
  · rw [hget, Nat.ofDigits_digits]

theorem list_set_append_replicate {xs : List ℕ} {cap v : ℕ} (h : xs.length < cap) :
    (xs ++ List.replicate (cap - xs.length) 0).set xs.length v =
      (xs ++ [v]) ++ List.replicate (cap - (xs.length + 1)) 0 := by
  have hsub : cap - xs.length = (cap - (xs.length + 1)) + 1 := by omega
  rw [hsub, List.replicate_succ]
  apply List.ext_getElem
  · simp only [List.length_set, List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    omega
  · intro i h1 h2
    simp only [List.getElem_set]
    by_cases heq : xs.length = i
    · subst heq
      rw [ite_eq_left rfl, List.getElem_append_left (by simp), List.getElem_append_right (le_refl _)]
      simp
    · rw [ite_eq_right heq]
      by_cases hlt : i < xs.length
      · rw [List.getElem_append_left hlt, List.getElem_append_left (by simp; omega),
            List.getElem_append_left hlt]
      · have hgt : xs.length < i := by omega
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp; omega)]
        have hi' : i - xs.length = (i - (xs.length + 1)) + 1 := by omega
        simp [hi']

end MinCostFlow.NarrowProg
