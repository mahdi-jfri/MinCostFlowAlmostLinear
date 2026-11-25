module

public import WordRAM.Module
public import WordRAM.Sep.CostSpec
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0Read
public import MinCostFlow.NarrowProg.Stage0Check
public import MinCostFlow.NarrowProg.Stage0Shift
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowTop.Program
public import MinCostFlow.NarrowTop.MainMath

/-!
# Interface specifications for the two pruned Stage 1 calls (`stage0Feas`, `stage0Res`)

Defines the specifications and module packages for the pruned feasibility call (`stage0Feas`)
and the pruned residual call (`stage0Res`) consumed by `narrowMain` (`NarrowTop/Main.lean`),
matching the published `Stage0Feas` / `Stage0Res` contracts with explicit `w`-independent
overhead constants and per-call `stage1CircSpace` bounds.
-/

@[expose] public section

open WordRAM WordRAM.Sep MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg
  MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowTop

/-! ### Stage 0 feasibility call specification (`stage0Feas`) -/

/-- Overhead heap space of `stage0Feas` excluding `stage1CircSpace P' k S`. -/
def stage0FeasSpace (m L : ℕ) : ℕ :=
  10 + 2 + 8 * (3 * m) + m + m * L

/-- Named data for the pruned feasibility call `stage0Feas`. -/
structure Stage0FeasData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  outBuf : List ℕ

/-- Specification of `stage0Feas(pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf,
pShDemSign, pShDemLen, L, k, pFeasOut, h)`. Builds `P' = (buildFeasibilityInstance I hv).withoutZeroEdges`,
invokes `stage1Circ`, checks saturation of the demand arcs, and scatters the feasible shifted flow
into `pFeasFlow` when `ok = 1`. -/
def stage0FeasSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0FeasData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pFeasOut : ℕ) (h : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pFeasOut, h] ∧
      ActiveInv el d.act ∧ d.L < 2 ^ k ∧
      2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pShCapLen + d.I.m ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      d.I.n + 2 < 2 ^ w ∧ d.outBuf.length = 2 ∧
      h + stage0FeasSpace d.I.m d.L + stage1CircSpace P' k S < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pFeasOut d.outBuf * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pFeasOut : ℕ) (h : ℕ)
      (ok : ℕ) (pFeasFlow : ℕ) (f : Fin d.I.m → ℤ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pFeasOut, h] ∧
      h + stage0FeasSpace d.I.m d.L ≤ h' ∧
      h' ≤ h + stage0FeasSpace d.I.m d.L + stage1CircSpace P' k S ∧
      pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ ok ≤ 1 ∧
      (ok = 1 →
        (∀ e : Fin d.I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph d.I d.hv).capacity e : ℤ)) ∧
        d.I.IsFeasible (FlowReduction.restore d.I (fun e => (f e : ℝ)))) ∧
      (ok = 0 → ∀ x, ¬ d.I.IsFeasible x)⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    (if ok = 1 then
      (∏ i ∈ Finset.range d.I.m,
        Assn.list (pFeasFlow + i * d.L)
          (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (f ⟨i, hlt⟩).toNat) d.L else []))
    else Assn.gc) *
    Assn.list pFeasOut [ok, pFeasFlow] * Assn.free h' (2 ^ w - h') * Assn.gc

/-! ### Stage 0 residual call specification (`stage0Res`) -/

/-- Overhead heap space of `stage0Res` excluding `stage1CircSpace R' k S`. -/
def stage0ResSpace (m L totCost : ℕ) : ℕ :=
  10 + 2 + 8 * (2 * m) + m * L + 2 * totCost + 2 * m * L

/-- Named data for the pruned residual call `stage0Res`. -/
structure Stage0ResData where
  I : Instance
  hv : I.IsValid
  f : Fin I.m → ℤ
  hf : ∀ e : Fin I.m, 0 ≤ f e ∧ f e ≤ ((FlowReduction.shiftedGraph I hv).capacity e : ℤ)
  L : ℕ
  hLge : narrowMaxCapLimbs I + 1 ≤ L
  outBuf : List ℕ

/-- Specification of `stage0Res(pEdges, pShCapBuf, pFeasFlow, n, m, L, k, pResOut, h)`.
Builds `R' = ((shiftedGraph I hv).residual f).withoutZeroEdges`, invokes `stage1Circ`, and
scatters the forward and reverse flow tables into `pHFwd` and `pHRev`. -/
def stage0ResSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage0ResData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pResOut : ℕ) (h : ℕ),
    let k := narrowLimbWidth d.I
    let R' := ((FlowReduction.shiftedGraph d.I d.hv).residual d.f).withoutZeroEdges
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k, pResOut, h] ∧
      d.L < 2 ^ k ∧ 2 * k + 1 ≤ w ∧ (18 * d.I.m + 21) * upperClip (3 * d.I.m) < 2 ^ w ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ pFeasFlow + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      d.I.n + 1 < 2 ^ w ∧ d.outBuf.length = 2 ∧
      h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) + stage1CircSpace R' k S < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    Assn.list pResOut d.outBuf * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pFeasFlow : ℕ) (pResOut : ℕ) (h : ℕ)
      (pHFwd : ℕ) (pHRev : ℕ) (g : Fin (d.I.m + d.I.m) → ℤ),
    let k := narrowLimbWidth d.I
    let R := (FlowReduction.shiftedGraph d.I d.hv).residual d.f
    let R' := R.withoutZeroEdges
    ⌜args = [pEdges, pShCapBuf, pFeasFlow, d.I.n, d.I.m, d.L, k, pResOut, h] ∧
      h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) ≤ h' ∧
      h' ≤ h + stage0ResSpace d.I.m d.L (totCostLimbs d.I) + stage1CircSpace R' k S ∧
      pHFwd + d.I.m * d.L ≤ 2 ^ w ∧ pHRev + d.I.m * d.L ≤ 2 ^ w ∧
      R.Optimal (fun a => (g a : ℝ)) ∧
      (∀ e : Fin d.I.m, 0 ≤ g (Fin.castAdd d.I.m e) ∧ 0 ≤ g (Fin.natAdd d.I.m e)) ∧
      (∀ e : Fin d.I.m, (g (Fin.natAdd d.I.m e)).toNat ≤ (d.f e).toNat) ∧
      (∀ e : Fin d.I.m, (d.f e).toNat + (g (Fin.castAdd d.I.m e)).toNat ≤
        (FlowReduction.shiftedGraph d.I d.hv).capacity e)⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pShCapBuf + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pFeasFlow + i * d.L)
        (if hlt : i < d.I.m then padLimbs (Nat.digits (2 ^ k) (d.f ⟨i, hlt⟩).toNat) d.L else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHFwd + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) (g (Fin.castAdd d.I.m ⟨i, hlt⟩)).toNat) d.L
        else [])) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pHRev + i * d.L)
        (if hlt : i < d.I.m then
          padLimbs (Nat.digits (2 ^ k) (g (Fin.natAdd d.I.m ⟨i, hlt⟩)).toNat) d.L
        else [])) *
    Assn.list pResOut [pHFwd, pHRev] * Assn.free h' (2 ^ w - h') * Assn.gc

/-! ### Module packages for `stage0Feas` and `stage0Res` -/

/-- Module package for the pruned feasibility call (`stage0Feas`) and pruned residual call
(`stage0Res`), using disjoint `.mainAux` procedure indices `≥ 100`. -/
structure Stage0CallsPkg where
  feasMod : Module NarrowTopName
  resMod : Module NarrowTopName
  feasEntry : ℕ
  resEntry : ℕ
  feas_names : ∀ n ∈ feasMod.names, ∃ i, n = .mainAux i ∧ 100 ≤ i ∧ i < 200
  res_names : ∀ n ∈ resMod.names, ∃ i, n = .mainAux i ∧ 200 ≤ i
  feas_nodup : feasMod.names.Nodup
  res_nodup : resMod.names.Nodup
  feas_noRand : feasMod.NoRand
  res_noRand : resMod.NoRand
  aFeas : ℕ
  aRes : ℕ
  feas_meets :
    ∀ (w : ℕ) (p : Program) (idx : NarrowTopName → ℕ)
      (S : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℕ),
      (∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m') →
      (∀ n n' m m' u u' c c', n ≤ n' → m ≤ m' → u ≤ u' → c ≤ c' →
        B n m u c ≤ B n' m' u' c') →
      feasMod.Placed p idx →
      Meets w p (idx (.stage1 0)) ((stage1CircSpec w S).withCost fun x _ =>
        B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) →
      Meets w p (idx (.mainAux feasEntry))
        ((stage0FeasSpec w S).withCost fun d _ =>
          aFeas * (d.I.n + d.I.m * (d.L + 1) + 1) +
          B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1)
  res_meets :
    ∀ (w : ℕ) (p : Program) (idx : NarrowTopName → ℕ)
      (S : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ → ℕ → ℕ),
      (∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m') →
      (∀ n n' m m' u u' c c', n ≤ n' → m ≤ m' → u ≤ u' → c ≤ c' →
        B n m u c ≤ B n' m' u' c') →
      resMod.Placed p idx →
      Meets w p (idx (.stage1 0)) ((stage1CircSpec w S).withCost fun x _ =>
        B x.1.n x.1.m (circMaxCapacity x.1) (circMaxCost x.1)) →
      Meets w p (idx (.mainAux resEntry))
        ((stage0ResSpec w S).withCost fun d _ =>
          aRes * (d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) + 1) +
          B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost)

end MinCostFlow.NarrowTop
