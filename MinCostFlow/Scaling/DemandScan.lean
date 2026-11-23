module

public import MinCostFlow.Scaling.FlowReduction
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring

/-!
# Building shifted demands with an edge scan

The lower-capacity reduction in the proof of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, needs the vector `d - Bᵀ lower`. Rather than evaluate one
sum per vertex, initialize the demand table and scan edges once. For each edge,
subtract its lower capacity at the tail and add it at the head. The two writes
are sequential, so this also handles loops correctly.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- Apply one edge's lower-capacity contribution to the demand table. -/
def demandStep (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (e : Fin I.m) : Fin I.n → ℤ :=
  let tail := (shiftedGraph I hv).tail e
  let head := (shiftedGraph I hv).head e
  let s' := Function.update s tail (s tail - (I.edge e).lower)
  Function.update s' head (s' head + (I.edge e).lower)

/-- The two table updates are exactly minus the edge's incidence contribution.
When the edge is a loop, these two updates cancel. -/
theorem demandStep_apply (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (e : Fin I.m) (v : Fin I.n) :
    demandStep I hv s e v = s v - coefficient I e v * (I.edge e).lower := by
  classical
  have ht : v = (shiftedGraph I hv).tail e ↔ v.val = (I.edge e).tail := Fin.ext_iff
  have hh : v = (shiftedGraph I hv).head e ↔ v.val = (I.edge e).head := Fin.ext_iff
  simp only [demandStep, Function.update_apply, coefficient, ← ht, ← hh]
  split_ifs <;> simp_all

/-- Scan any edge list, retaining repeated contributions if an index repeats. -/
def scanDemands (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (es : List (Fin I.m)) : Fin I.n → ℤ :=
  es.foldl (demandStep I hv) s

/-- The edge scan agrees with the sum of incidence contributions. -/
theorem scanDemands_apply (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (es : List (Fin I.m)) (v : Fin I.n) :
    scanDemands I hv s es v = s v -
      (es.map (fun e => coefficient I e v * (I.edge e).lower)).sum := by
  induction es generalizing s with
  | nil => simp [scanDemands]
  | cons e es ih =>
    change scanDemands I hv (demandStep I hv s e) es v = _
    rw [ih, demandStep_apply]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Compute the shifted demand vector with one explicit edge loop. -/
def buildShiftedDemands (I : Instance) (hv : I.IsValid) : Fin I.n → ℤ :=
  scanDemands I hv (fun v => I.d v) (List.finRange I.m)

/-- The efficient table computation agrees with the reduction's demand vector. -/
theorem buildShiftedDemands_eq (I : Instance) (hv : I.IsValid) :
    buildShiftedDemands I hv = shiftedDemand I := by
  funext v
  rw [buildShiftedDemands, scanDemands_apply]
  rw [← Fin.sum_univ_def]
  rfl

/-- Count the table operations of the scan. Each edge reads its three input
fields, reads and writes two demand cells, performs two integer operations,
and pays two loop-control operations. -/
def scanDemandsWithWork (I : Instance) (hv : I.IsValid) :
    (Fin I.n → ℤ) → List (Fin I.m) → (Fin I.n → ℤ) × ℕ
  | s, [] => (s, 0)
  | s, e :: es =>
      let r := scanDemandsWithWork I hv (demandStep I hv s e) es
      (r.1, 11 + r.2)

/-- Adding the work counter does not alter the computed demand table. -/
theorem scanDemandsWithWork_value (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (es : List (Fin I.m)) :
    (scanDemandsWithWork I hv s es).1 = scanDemands I hv s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (demandStep I hv s e)

/-- The scan uses exactly eleven counted operations per edge. Initialization
of the demand table is separate and reads and writes each of the `n` entries. -/
theorem scanDemandsWithWork_work (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (es : List (Fin I.m)) :
    (scanDemandsWithWork I hv s es).2 = 11 * es.length := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    change 11 + (scanDemandsWithWork I hv (demandStep I hv s e) es).2 = _
    rw [ih, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

end MinCostFlow.Scaling.FlowReduction
