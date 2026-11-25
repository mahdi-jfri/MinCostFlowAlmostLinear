module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Sep.BridgeHeap
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.Scaling.VertexCompression
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.PropagateLabelsProgram
import MinCostFlow.Scaling.LabelOutputLayout
import MinCostFlow.Narrow.CostUnitsClip

/-!
# Shared layouts, specifications, and first-layer bridges for Stage 1

This file defines:
- `stage1Input`, `stage1CircSpace`, `stage1CircSpec`: the fixed input/output
  memory layout and top-level specification of `stage1Circ` (Stage 1 + vertex
  compression + `m = 0` handling).
- `stage1BitScaleInput`, `stage1BitScaleSpace`, `stage1BitScaleSpec`: Stage 2's
  `bitScale` specification (definitionally identical to `narrowprog`'s
  `bitScaleInput` / `bitScaleSpec`).
- `stage1SolverSpec` and `solverContract_meets_stage1SolverSpec`: local bridge
  from first-layer `solverContract w T S` keeping both `Assn.list h flow` and
  `Assn.cells (Set.Ico (h + J.m) (max v (h + J.m))) m₁` (no gap before `max v (h + J.m)`).
- `stage1PropLabelsSpec`, `propagateLabels_meets_stage1PropSpec`, and
  `stage1PropLabelsMod`: bridge from first-layer `propagateLabels_meetsContract`
  (`MinCostFlow/Scaling/PropagateLabelsProgram.lean`) via `MeetsContract.meets_heap`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

/-! ### Encoding of `FreezeState` -/

/-- Machine word encoding of `FreezeState`: `0 = none`, `1 = pos`, `2 = neg`. -/
def freezeCode : FreezeState → ℕ
  | .none => 0
  | .pos => 1
  | .neg => 2

/-! ### Stage 1 top-level input, space, and specification -/

/-- Memory layout of the Stage 1 input circulation `I` with base-`2 ^ k` capacity
and cost limb lists: a 10-word descriptor at `pIn` pointing to the edge tables
and canonical limb arrays. -/
def stage1Input (I : Circulation) (k : ℕ)
    (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (costPtrs : List ℕ) (costLimbs : List (List ℕ))
    (pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens : ℕ) : Assn :=
  Assn.list pIn [I.n, I.m, k, pTail, pHead, pCapPtrs, pCapLens, pCostSign, pCostPtrs, pCostLens] *
  Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])) *
  Assn.list pCostSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list pCostPtrs costPtrs *
  Assn.list pCostLens (costLimbs.map List.length) *
  (∏ j ∈ Finset.range I.m, Assn.list (costPtrs.getD j 0) (costLimbs.getD j []))

/-- Space budget of Stage 2 (`bitScale`), matching `narrowprog`. -/
def stage1BitScaleSpace (J : Circulation) (k : ℕ) (S : ℕ → ℕ → ℕ) : ℕ :=
  5 + 2 * J.m + 3 * J.m * (bitScalingPhases J / k + 2) +
    bitScalingPhases J * (2 + 12 * J.m + S (J.n + 1) (2 * J.m))

/-- Per-round dual-extraction space budget for a compressed circulation `C`. -/
def stage1DualSpace (C : Circulation) (S : ℕ → ℕ → ℕ) : ℕ :=
  let Sm := 4 * C.m + C.n
  let Qm := 2 * Sm
  (2 + 5 * Sm) + Sm + (2 + 5 * Qm) + Qm + S (C.n + 2) Qm + (5 + 5 * (C.n + 1) + 6 * Sm)

/-- Per-round `bitScale` space upper bound for any feasible residual of `C`. -/
def stage1RoundBitScaleSpace (C : Circulation) (k : ℕ) (S : ℕ → ℕ → ℕ) : ℕ :=
  5 + 4 * C.m + 6 * C.m * (bitScalingPhases C / k + 2) +
    bitScalingPhases C * (2 + 24 * C.m + S (C.n + 1) (4 * C.m))

/-- Start-phase space budget for `stage1Start` on `I`. -/
def stage1StartSpace (I : Circulation) (k : ℕ) : ℕ :=
  let K_cap := bitScalingPhases I / k + 2
  let L_limbs := costScaleBits I / k + 2
  I.n + 40 + 18 * I.m + 5 * I.m * K_cap + I.m * L_limbs

/-- Total heap space budget of `stage1Circ`. -/
def stage1CircSpace (I : Circulation) (k : ℕ) (S : ℕ → ℕ → ℕ) : ℕ :=
  if I.m = 0 then 0
  else
    let C := I.compress
    stage1StartSpace I k +
      narrowCostRounds C * (stage1RoundBitScaleSpace C k S + stage1DualSpace C S)

/-- Top-level specification of `stage1Circ (pIn, pOut, h)`. -/
def stage1CircSpec (w : ℕ) (S : ℕ → ℕ → ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ × List (List ℕ) × List ℕ) where
  pre := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs, outBuf) args =>
    ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ),
      ⌜args = [pIn, pOut, h] ∧ outBuf.length = 2 ∧
        capPtrs.length = I.m ∧ capLimbs.length = I.m ∧
        costPtrs.length = I.m ∧ costLimbs.length = I.m ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (capLimbs.getD j []) ∧
          (capLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = I.capacity ⟨j, hj⟩) ∧
        (∀ j (hj : j < I.m), CanonicalLimbs k (costLimbs.getD j []) ∧
          (costLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (costLimbs.getD j []) = (I.cost ⟨j, hj⟩).natAbs) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧ k + Nat.log 2 (2 * k) + 2 ≤ w ∧
        2 * I.m + 1 < 2 ^ k ∧ 6 * I.m + 4 < 2 ^ w ∧ I.n + 1 < 2 ^ w ∧
        (6 * I.m + 21) * upperClip I.m < 2 ^ w ∧
        h + stage1CircSpace I k S < 2 ^ w⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.list pOut outBuf * Assn.free h (2 ^ w - h)
  post := fun (I, k, capPtrs, capLimbs, costPtrs, costLimbs, _) args h' =>
    ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCapPtrs : ℕ) (pCapLens : ℕ)
      (pCostSign : ℕ) (pCostPtrs : ℕ) (pCostLens : ℕ) (pFlow : ℕ)
      (f : Fin I.m → ℤ) (flowLimbs : Fin I.m → List ℕ),
      let K_cap := bitScalingPhases I / k + 2
      ⌜args = [pIn, pOut, h] ∧ h ≤ h' ∧ h' ≤ h + stage1CircSpace I k S ∧
        I.Optimal (fun e => (f e : ℝ)) ∧
        (∀ e, 0 ≤ f e ∧ Limbs k (flowLimbs e) ∧ (flowLimbs e).length = K_cap ∧
          ((Nat.ofDigits (2 ^ k) (flowLimbs e) : ℕ) : ℤ) = f e)⌝ *
      stage1Input I k capPtrs capLimbs costPtrs costLimbs
        pIn pTail pHead pCapPtrs pCapLens pCostSign pCostPtrs pCostLens *
      Assn.list pOut [pFlow, K_cap] *
      (∏ e ∈ Finset.range I.m, Assn.list (pFlow + e * K_cap)
        (if h : e < I.m then flowLimbs ⟨e, h⟩ else [])) *
      Assn.free h' (2 ^ w - h')

/-! ### Stage 2 (`bitScale`) layout and specification (matching `narrowprog`) -/

/-- Memory layout of the Stage 2 (`bitScale`) input circulation `J`, matching
`MinCostFlow.NarrowProg.bitScaleInput` verbatim. -/
def stage1BitScaleInput (J : Circulation) (k : ℕ) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (pIn pTail pHead pCSign pCMag pCapPtrs pCapLens : ℕ) : Assn :=
  Assn.list pIn [J.n, J.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens] *
  Assn.list pTail (List.ofFn fun e : Fin J.m => (J.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin J.m => (J.head e).val) *
  Assn.list pCSign (List.ofFn fun e : Fin J.m => if J.cost e < 0 then 1 else 0) *
  Assn.list pCMag (List.ofFn fun e : Fin J.m => (J.cost e).natAbs) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  ∏ j ∈ Finset.range J.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])

/-- Specification of Stage 2 (`bitScale`), matching `MinCostFlow.NarrowProg.bitScaleSpec`
verbatim. -/
def stage1BitScaleSpec (w : ℕ) (S : ℕ → ℕ → ℕ) :
    Spec (Circulation × ℕ × List ℕ × List (List ℕ) × List ℕ) where
  pre := fun (J, k, capPtrs, capLimbs, outBuf) args =>
    ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCSign : ℕ) (pCMag : ℕ)
      (pCapPtrs : ℕ) (pCapLens : ℕ),
      ⌜args = [pIn, pOut, h] ∧ outBuf.length = 4 ∧
        capPtrs.length = J.m ∧ capLimbs.length = J.m ∧
        (∀ j (hj : j < J.m), CanonicalLimbs k (capLimbs.getD j []) ∧
          (capLimbs.getD j []).length * k < 2 ^ w ∧
          Nat.ofDigits (2 ^ k) (capLimbs.getD j []) = J.capacity ⟨j, hj⟩) ∧
        1 ≤ k ∧ 2 * k ≤ w ∧ k + Nat.log 2 (2 * k) + 2 ≤ w ∧
        J.m + 1 < 2 ^ k ∧ 3 * J.m + 4 < 2 ^ w ∧ J.n + 1 < 2 ^ w ∧
        J.CostsBounded ((2 * J.m) ^ 10) ∧ (∀ e, (J.cost e).natAbs < 2 ^ w) ∧
        h + stage1BitScaleSpace J k S < 2 ^ w⌝ *
      stage1BitScaleInput J k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens *
      Assn.list pOut outBuf * Assn.free h (2 ^ w - h)
  post := fun (J, k, capPtrs, capLimbs, _) args h' =>
    ⨆ (pIn : ℕ) (pOut : ℕ) (h : ℕ) (pTail : ℕ) (pHead : ℕ) (pCSign : ℕ) (pCMag : ℕ)
      (pCapPtrs : ℕ) (pCapLens : ℕ)
      (g : Fin J.m → ℤ) (flowLimbs : Fin J.m → List ℕ),
      let T := bitScalingPhases J
      let L := T / k + 2
      let pRho := h
      let pGCap := h + J.m
      let pFlow := h + 2 * J.m
      ⌜args = [pIn, pOut, h] ∧ h ≤ h' ∧ h' ≤ h + stage1BitScaleSpace J k S ∧
        J.Optimal (fun e => (g e : ℝ)) ∧
        (∀ e, 0 ≤ g e ∧ Limbs k (flowLimbs e) ∧ (flowLimbs e).length = L ∧
          ((Nat.ofDigits (2 ^ k) (flowLimbs e) : ℕ) : ℤ) = g e) ∧
        (∀ e, (0 < cappedResidual J T T g (J.m + 1) e ↔
            0 < (J.residual g).capacity (Fin.castAdd J.m e)) ∧
          (0 < cappedFlow g (J.m + 1) e ↔
            0 < (J.residual g).capacity (Fin.natAdd J.m e)))⌝ *
      stage1BitScaleInput J k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens *
      Assn.list pOut [pFlow, L, pRho, pGCap] *
      Assn.list pRho (List.ofFn fun e => cappedResidual J T T g (J.m + 1) e) *
      Assn.list pGCap (List.ofFn fun e => cappedFlow g (J.m + 1) e) *
      (∏ e ∈ Finset.range J.m, Assn.list (pFlow + e * L)
        (if h : e < J.m then flowLimbs ⟨e, h⟩ else [])) *
      Assn.free h' (2 ^ w - h')

/-! ### Local `meets_heap_zero` and bridge for `solverContract` -/

/-- `heapSpec` strengthened with `ZeroFrom m₁ v` in its postcondition. -/
def heapSpecZeroS1 (w : ℕ) (pre : List ℕ → (ℕ → ℕ) → Prop)
    (post : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop) (cost space : List ℕ → (ℕ → ℕ) → ℕ)
    (D : List ℕ → Set ℕ) : Spec (ℕ → ℕ) where
  pre m₀ args := ⌜pre args m₀ ∧ heapArg args + space args m₀ < 2 ^ w⌝ * $ (cost args m₀ : ℤ) *
    (Assn.cells (D args) m₀ * Assn.free (heapArg args) (2 ^ w - heapArg args))
  post m₀ args v := ⨆ m₁ : ℕ → ℕ,
    ⌜heapArg args ≤ v ∧ v ≤ heapArg args + space args m₀ ∧ ZeroFrom m₁ v ∧
      ∃ m : ℕ → ℕ, (∀ a ∈ D args, m a = m₀ a) ∧ pre args m ∧ post args m m₁⌝ *
    (Assn.cells (D args) m₀ * Assn.cells (Set.Ico (heapArg args) v) m₁ *
      Assn.free v (2 ^ w - v))

/-- Strengthened `MeetsContract.meets_heap` retaining `ZeroFrom m₁ v`. -/
theorem meets_heap_zero_s1 {w : ℕ} {p : Program} {f : ℕ}
    {pre : List ℕ → (ℕ → ℕ) → Prop} {post : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    {cost space : List ℕ → (ℕ → ℕ) → ℕ} {D : List ℕ → Set ℕ} {body : Stmt}
    (hC : MeetsContract w p f (heapContract w pre post cost space))
    (hL : HeapLocalTo pre cost space D) (hproc : p.procs[f]? = some body) :
    Meets w p f (heapSpecZeroS1 w pre post cost space D) := by
  refine ⟨body, hproc, fun m₀ args => ?_⟩
  intro st ω h hf c hpre hd hin hok hw
  obtain ⟨hρ, hpre⟩ := Assn.pure_mul_apply.mp hpre
  obtain ⟨⟨hP, hfit⟩, hcells⟩ := Assn.pure_credits_apply.mp hpre
  set H := heapArg args with hHdef
  have hH : H ≤ 2 ^ w := by omega
  obtain ⟨hc, hbelow, rfl⟩ := Assn.cells_mul_free_top hH hcells hok
  have hin₁ := Heap.in_restrict.mp hin.of_union_left
  have hfD := Heap.disjoint_restrict_left.mp hd
  set st₀ := st.withHigh w fun _ => 0 with hst₀
  have hagree : ∀ a ∈ D args, st₀.mem a = m₀ a := fun a ha => by
    have hlt : a < 2 ^ w := by have := hbelow a ha; omega
    show memMix w st.mem (fun _ => 0) a = _
    rw [memMix_of_lt hlt]
    simpa [hbelow a ha] using hin₁ a (Or.inl ha)
  have hzero : ZeroFrom st₀.mem H := fun a ha => by
    by_cases hlt : a < 2 ^ w
    · show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_lt hlt]
      simpa [Nat.not_lt.mpr ha] using hin₁ a (Or.inr ⟨ha, hlt⟩)
    · show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_ge (Nat.not_lt.mp hlt)]
  have hP₀ := hL.pre args m₀ st₀.mem hagree hP
  have hcost := hL.cost args m₀ st₀.mem hagree hP
  have hspace := hL.space args m₀ st₀.mem hagree hP
  obtain ⟨body', hproc', o, st₁, k, hrun, ⟨hHv, hvle, hlow, hz, hpost⟩, hk⟩ :=
    hC args st₀.mem st.pos ω (args_lt_of_argRegs (hρ ▸ hw.1)) ⟨hP₀, hzero, by omega⟩
  rw [hproc] at hproc'
  cases hproc'
  rw [show startState args st₀.mem st.pos = st₀ from
    (eq_startState_of_regs (st := st₀) hρ).symm] at hrun
  have hrun' := Runs.of_withHigh_zero hrun hw
  have hv : o.value ≤ 2 ^ w := by
    change o.value ≤ H + space args st₀.mem at hvle; omega
  set st' := st₁.withHigh w st.mem with hst'
  have hlow' : ∀ a < 2 ^ w, st'.mem a = st₁.mem a := fun a ha => memMix_of_lt ha
  refine ⟨o, st', k, Heap.restrict (D args ∪ Set.Ico H (2 ^ w)) st'.mem, c - k, hrun', ?_,
    Heap.disjoint_restrict_left.mpr hfD, ?_,
    Heap.addrOk_restrict.mpr (Heap.addrOk_restrict.mp hok),
    by change k ≤ cost args st₀.mem at hk; omega⟩
  · refine Assn.mul_gc_of_nonneg ((Assn.iSup_apply _ _ _).mpr ⟨st₁.mem, ?_⟩)
      (by change k ≤ cost args st₀.mem at hk; omega)
    refine Assn.pure_mul_apply.mpr ⟨⟨hHv, by change o.value ≤ H + space args st₀.mem at hvle; omega,
      hz, st₀.mem, hagree, hP₀, hpost⟩, ?_⟩
    rw [Assn.cells_congr (D := Set.Ico H o.value) (m' := st'.mem) fun a ha => by
      simp only [Set.mem_Ico] at ha; exact (hlow' a (by omega)).symm]
    refine Assn.cells_mul_cells_mul_free_top hbelow hHv hv (fun a ha => ?_) (fun a ha hlt => ?_)
    · have hlt : a < H := hbelow a ha
      rw [hlow' a (by omega), hlow a hlt, hagree a ha]
    · rw [hlow' a hlt]; exact hz a ha
  · refine (Heap.in_union (Heap.disjoint_restrict_left.mpr hfD)).mpr
      ⟨Heap.in_restrict.mpr fun _ _ => rfl, fun a x hx => ?_⟩
    have hnot : a ∉ D args ∪ Set.Ico H (2 ^ w) := fun ha => by rw [hfD a ha] at hx; cases hx
    have hold := ((Heap.in_union hd).mp hin).2 a x hx
    by_cases haH : a < H
    · rw [hlow' a (by omega), hlow a haH]
      show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_lt (by omega), hold]
    · have hge : 2 ^ w ≤ a := by
        by_contra hlt
        exact hnot (Or.inr ⟨Nat.not_lt.mp haH, Nat.not_le.mp hlt⟩)
      show memMix w st₁.mem st.mem a = _
      rw [memMix_of_ge hge, hold]

/-- Second-layer specification of the bounded solver, keeping both the output flow
`Assn.list h flow` and the remaining allocated cells `[h + J.m, max v (h + J.m))`
so callers can merge `[a, max v (h + J.m))` without gaps. -/
def stage1SolverSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Circulation where
  pre J args := ⨆ a : ℕ,
    let h := a + J.solverWords.length
    ⌜args = [a, h] ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      J.CostsBounded (J.m ^ 10) ∧ h + J.m + S J.n J.m < 2 ^ w ∧
      ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40⌝ *
    Assn.list a J.solverWords * Assn.free h (2 ^ w - h)
  post J args v := ⨆ (a : ℕ) (flow : List ℕ) (m₁ : ℕ → ℕ),
    let h := a + J.solverWords.length
    ⌜args = [a, h] ∧ h ≤ v ∧ v ≤ h + J.m + S J.n J.m ∧ flow.length = J.m ∧
      J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ))⌝ *
    Assn.list a J.solverWords * Assn.list h flow *
    Assn.cells (Set.Ico (h + J.m) (max v (h + J.m))) m₁ *
    Assn.free (max v (h + J.m)) (2 ^ w - max v (h + J.m))

private def stage1SolverCells : List ℕ → Set ℕ
  | [a, h] => Set.Ico a h
  | _ => ∅

private lemma stage1SolverDim_of_at (J : Circulation) (mem : ℕ → ℕ) (a h : ℕ)
    (hat : ListAt mem a J.solverWords) :
    solverDimensions [a, h] mem = (J.n, J.m) := by
  have h0 : mem (a + 0) = J.n := hat 0 (by rw [J.solverWords_length]; omega)
  have h1 : mem (a + 1) = J.m := hat 1 (by rw [J.solverWords_length]; omega)
  simp only [solverDimensions, List.getD, List.getElem?_cons_zero, Option.getD_some,
    Nat.add_zero] at h0 ⊢
  exact Prod.ext h0 h1

private lemma stage1SolverContract_heapLocalTo (w : ℕ) (T S : ℕ → ℕ → ℕ) :
    HeapLocalTo
      (fun args mem => ∃ a h : ℕ, args = [a, h] ∧ ∃ J : Circulation,
        ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h ∧
        (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ J.CostsBounded (J.m ^ 10) ∧
        h + J.m + S J.n J.m < 2 ^ w ∧ ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
      (fun args mem => T (solverDimensions args mem).1 (solverDimensions args mem).2)
      (fun args mem => (solverDimensions args mem).2 +
        S (solverDimensions args mem).1 (solverDimensions args mem).2)
      stage1SolverCells where
  pre args m m' hagree hpre := by
    obtain ⟨a, h, rfl, J, hat, hle, hw, hc, hsp, hcap⟩ := hpre
    refine ⟨a, h, rfl, J, ?_, hle, hw, hc, hsp, hcap⟩
    intro i hi
    rw [hagree (a + i) (by simp only [stage1SolverCells, Set.mem_Ico]; omega)]
    exact hat i hi
  cost args m m' hagree hpre := by
    obtain ⟨a, h, rfl, J, hat, hle, -, -, -, -⟩ := hpre
    have hlen := J.solverWords_length
    have h0 : m' a = m a := hagree a (by simp only [stage1SolverCells, Set.mem_Ico]; omega)
    have h1 : m' (a + 1) = m (a + 1) :=
      hagree (a + 1) (by simp only [stage1SolverCells, Set.mem_Ico]; omega)
    simp only [solverDimensions, List.getD, List.getElem?_cons_zero, Option.getD_some, h0, h1, le_rfl]
  space args m m' hagree hpre := by
    obtain ⟨a, h, rfl, J, hat, hle, -, -, -, -⟩ := hpre
    have hlen := J.solverWords_length
    have h0 : m' a = m a := hagree a (by simp only [stage1SolverCells, Set.mem_Ico]; omega)
    have h1 : m' (a + 1) = m (a + 1) :=
      hagree (a + 1) (by simp only [stage1SolverCells, Set.mem_Ico]; omega)
    simp only [solverDimensions, List.getD, List.getElem?_cons_zero, Option.getD_some, h0, h1, le_rfl]

private lemma cells_free_split_exact {w h v m : ℕ} {m₁ : ℕ → ℕ}
    (hhv : h ≤ v) (hv : v ≤ 2 ^ w) (hhm : h + m ≤ 2 ^ w) (hz : ZeroFrom m₁ v) :
    Assn.cells (Set.Ico h v) m₁ * Assn.free v (2 ^ w - v) =
      Assn.list h ((List.range m).map fun i => m₁ (h + i)) *
      Assn.cells (Set.Ico (h + m) (max v (h + m))) m₁ *
      Assn.free (max v (h + m)) (2 ^ w - max v (h + m)) := by
  have hlist : Assn.list h ((List.range m).map fun i => m₁ (h + i)) =
      Assn.cells (Set.Ico h (h + m)) m₁ := by
    rw [Assn.list_eq_cells]
    simp only [List.length_map, List.length_range]
    refine Assn.cells_congr fun x hx => ?_
    simp only [Set.mem_Ico] at hx
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    congr 1; omega
  rw [hlist]
  rcases le_or_gt (h + m) v with hle | hlt
  · rw [max_eq_left hle]
    have hdisj : Disjoint (Set.Ico h (h + m)) (Set.Ico (h + m) v) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; simp only [Set.mem_Ico] at hx1 hx2; omega
    rw [← Assn.cells_union hdisj, Set.Ico_union_Ico_eq_Ico (by omega) hle]
  · rw [max_eq_right (le_of_lt hlt)]
    have hempty : Set.Ico (h + m) (h + m) = ∅ := Set.Ico_self (h + m)
    rw [hempty, Assn.cells_empty, mul_one]
    have hsplit : 2 ^ w - v = (h + m - v) + (2 ^ w - (h + m)) := by omega
    rw [hsplit, Assn.free_add', show v + (h + m - v) = h + m by omega]
    have hfree_eq : Assn.free v (h + m - v) = Assn.cells (Set.Ico v (h + m)) m₁ := by
      rw [Assn.free_eq_cells, show v + (h + m - v) = h + m by omega]
      exact Assn.cells_congr fun x hx => by
        simp only [Set.mem_Ico] at hx; exact (hz x hx.1).symm
    rw [hfree_eq, ← mul_assoc]
    have hdisj : Disjoint (Set.Ico h v) (Set.Ico v (h + m)) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; simp only [Set.mem_Ico] at hx1 hx2; omega
    rw [← Assn.cells_union hdisj, Set.Ico_union_Ico_eq_Ico hhv (le_of_lt hlt)]

/-- Bridge from first-layer `solverContract w T S` to `stage1SolverSpec w S`. -/
theorem solverContract_meets_stage1SolverSpec {w : ℕ} {p : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ}
    {body : Stmt} (hC : MeetsContract w p f (solverContract w T S))
    (hproc : p.procs[f]? = some body) :
    Meets w p f ((stage1SolverSpec w S).withCost fun J _ => T J.n J.m) := by
  have hheap := meets_heap_zero_s1 hC (stage1SolverContract_heapLocalTo w T S) hproc
  refine hheap.weaken fun J args _ h c _ hpre => ?_
  simp only [Spec.withCost, stage1SolverSpec] at hpre
  obtain ⟨h1, h2, c1, c2, hd, rfl, rfl, hpre1, hc2⟩ := hpre
  obtain ⟨a, ha⟩ := (Assn.iSup_apply _ _ _).mp hpre1
  rw [mul_assoc] at ha
  obtain ⟨⟨rfl, hwords, hcostB, hfit, hcap⟩, hlists⟩ := Assn.pure_mul_apply.mp ha
  set h₀ := a + J.solverWords.length with hh₀
  let m₀ : ℕ → ℕ := fun x => J.solverWords.getD (x - a) 0
  have hat₀ : ListAt m₀ a J.solverWords := fun i hi => by
    simp only [m₀, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]
  have hdim₀ : solverDimensions [a, h₀] m₀ = (J.n, J.m) :=
    stage1SolverDim_of_at J m₀ a h₀ hat₀
  have hlist_eq : Assn.list a J.solverWords = Assn.cells (stage1SolverCells [a, h₀]) m₀ := by
    rw [stage1SolverCells, Assn.list_eq_cells]
  have hheap_eq : (Assn.cells (stage1SolverCells [a, h₀]) m₀ * Assn.free h₀ (2 ^ w - h₀)) h1 c1 := by
    rwa [← hlist_eq]
  have hcredit_eq : ($ (T (solverDimensions [a, h₀] m₀).1 (solverDimensions [a, h₀] m₀).2 : ℤ)) h2 c2 := by
    rwa [hdim₀]
  refine ⟨m₀, ?_, fun v => ?_⟩
  · simp only [heapSpecZeroS1, heapArg, List.getLastD_cons, List.getLastD_nil]
    rw [mul_assoc]
    refine Assn.pure_mul_apply.mpr ⟨⟨⟨a, h₀, rfl, J, hat₀, le_rfl, hwords, hcostB, hfit, hcap⟩,
      by rw [hdim₀]; dsimp only; omega⟩, ?_⟩
    exact ⟨h2, h1, c2, c1, hd.symm, Heap.union_comm hd, add_comm c1 c2, hcredit_eq, hheap_eq⟩
  · simp only [heapSpecZeroS1, heapArg, List.getLastD_cons, List.getLastD_nil]
    refine Assn.iSup_le_iff'.mpr fun m₁ => Assn.pure_mul_le.mpr ?_
    rintro ⟨hhv, hvle, hz, m, hagree, -, hpost⟩
    rw [hdim₀] at hvle; dsimp only at hvle
    have hat_m : ListAt m a J.solverWords := fun i hi => by
      rw [hagree (a + i) (by simp only [stage1SolverCells, Set.mem_Ico]; omega)]
      exact hat₀ i hi
    have hopt_m₁ : J.Optimal (fun e => (J.readSolverFlow m₁ h₀ e : ℝ)) := hpost J hat_m
    let flow : List ℕ := (List.range J.m).map fun i => m₁ (h₀ + i)
    have hflow_len : flow.length = J.m := by simp [flow]
    have hflow_opt : J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ)) := by
      convert hopt_m₁ using 1
      funext e
      simp only [Circulation.readSolverFlow, Int.cast_natCast, flow,
        List.getD_eq_getElem _ _ (by simp [e.isLt] : e.val < ((List.range J.m).map _).length),
        List.getElem_map, List.getElem_range]
    refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun a' : ℕ => ⨆ flow' : List ℕ, ⨆ m' : ℕ → ℕ, _) a) le_rfl)
    refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun flow' : List ℕ => ⨆ m' : ℕ → ℕ, _) flow) le_rfl)
    refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun m' : ℕ → ℕ => _) m₁) le_rfl)
    dsimp only
    rw [← hlist_eq]
    have hpure_ok : [a, h₀] = [a, h₀] ∧ h₀ ≤ v ∧ v ≤ h₀ + J.m + S J.n J.m ∧
        flow.length = J.m ∧ J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ)) :=
      ⟨rfl, hhv, by omega, hflow_len, hflow_opt⟩
    rw [eq_true hpure_ok, Assn.pure_true, one_mul]
    have hcf := cells_free_split_exact (w := w) (m := J.m) hhv (by omega) (by omega) hz
    rw [mul_assoc, hcf]
    simp only [← mul_assoc, hh₀, flow]
    exact Assn.le_mul_gc _

/-! ### Bridge for `propagateLabels_meetsContract` -/

/-- Named ghost arguments for `stage1PropLabelsSpec`. -/
structure PropLabelsArgs where
  J : Circulation
  flow : Fin J.m → ℤ
  root : Fin J.n
  C : ℕ
  mPad : ℕ → ℕ

/-- Second-layer specification for `propagateLabels` (`Scaling/PropagateLabelsProgram.lean`).
Owns `J.solverWords` at `a`, `flow` at `fp = a + J.solverWords.length`, contiguous scratch cells
`[fp + J.m, base)`, and `Assn.free base (2 ^ w - base)`. Returns `ret` with the signed label table
`Assn.list (base + 2) ((List.ofFn (J.propagateLabels flow root).1.labels).flatMap encodeSignedPair)`
and `Assn.free ret (2 ^ w - ret)`. -/
def stage1PropLabelsSpec (w : ℕ) : Spec PropLabelsArgs where
  pre x args := ⨆ (a : ℕ) (base : ℕ),
    let fp := a + x.J.solverWords.length
    ⌜args = [a, fp, x.root.val, base] ∧ fp + x.J.m ≤ base ∧
      (∀ e, 0 ≤ x.flow e ∧ (x.flow e).toNat < 2 ^ w) ∧
      (∀ e, (x.J.cost e).natAbs ≤ x.C) ∧ (x.J.m + 1) * x.C < 2 ^ w ∧
      base + 5 + 5 * x.J.n + 6 * x.J.m < 2 ^ w ∧ 8 < 2 ^ w⌝ *
    Assn.list a x.J.solverWords *
    Assn.list fp (List.ofFn fun e => (x.flow e).toNat) *
    Assn.cells (Set.Ico (fp + x.J.m) base) x.mPad *
    Assn.free base (2 ^ w - base)
  post x args ret := ⨆ (a : ℕ) (base : ℕ),
    let fp := a + x.J.solverWords.length
    ⌜args = [a, fp, x.root.val, base] ∧
      base + 3 + 5 * x.J.n ≤ ret ∧ ret ≤ base + 3 + 5 * x.J.n + 6 * x.J.m⌝ *
    Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) *
    Assn.free ret (2 ^ w - ret)

private def stage1PropCells : List ℕ → Set ℕ
  | [a, _, _, base] => Set.Ico a base
  | _ => ∅

private lemma signedTable_extract_from_cells {base ret n : ℕ} {m₁ : ℕ → ℕ}
    {labs : Fin n → ℤ} (hret : base + 2 + 2 * n ≤ ret)
    (htab : SignedTableAt m₁ (base + 2) labs) :
    Assn.cells (Set.Ico base ret) m₁ ≤
      Assn.list (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) * Assn.gc := by
  have hlistAt : ListAt m₁ (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) := htab.listAt
  have hlen : ((List.ofFn labs).flatMap encodeSignedPair).length = 2 * n := by
    rw [flatMap_encodeSignedPair_length, List.length_ofFn]
  have hlist_eq : Assn.list (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) =
      Assn.cells (Set.Ico (base + 2) (base + 2 + 2 * n)) m₁ := by
    rw [Assn.list_eq_cells, hlen]
    refine Assn.cells_congr fun x hx => ?_
    simp only [Set.mem_Ico] at hx
    have hi : x - (base + 2) < ((List.ofFn labs).flatMap encodeSignedPair).length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    have := hlistAt (x - (base + 2)) hi
    rw [show base + 2 + (x - (base + 2)) = x by omega] at this
    exact this.symm
  have hsub1 : Set.Ico base ret =
      Set.Ico base (base + 2) ∪ Set.Ico (base + 2) (base + 2 + 2 * n) ∪
      Set.Ico (base + 2 + 2 * n) ret := by
    rw [Set.Ico_union_Ico_eq_Ico (by omega) (by omega),
      Set.Ico_union_Ico_eq_Ico (by omega) hret]
  have hd1 : Disjoint (Set.Ico base (base + 2)) (Set.Ico (base + 2) (base + 2 + 2 * n)) := by
    rw [Set.disjoint_left]; intro x h1 h2; simp only [Set.mem_Ico] at h1 h2; omega
  have hd2 : Disjoint (Set.Ico base (base + 2) ∪ Set.Ico (base + 2) (base + 2 + 2 * n))
      (Set.Ico (base + 2 + 2 * n) ret) := by
    rw [Set.disjoint_left]; intro x h1 h2
    simp only [Set.mem_union, Set.mem_Ico] at h1 h2; omega
  rw [hsub1, Assn.cells_union hd2, Assn.cells_union hd1, ← hlist_eq]
  calc Assn.cells (Set.Ico base (base + 2)) m₁ *
        Assn.list (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) *
        Assn.cells (Set.Ico (base + 2 + 2 * n) ret) m₁
      = Assn.list (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) *
          (Assn.cells (Set.Ico base (base + 2)) m₁ *
            Assn.cells (Set.Ico (base + 2 + 2 * n) ret) m₁) := by
        rw [mul_comm (Assn.cells (Set.Ico base (base + 2)) m₁), mul_assoc]
    _ ≤ Assn.list (base + 2) ((List.ofFn labs).flatMap encodeSignedPair) * Assn.gc :=
        Assn.mul_le_mul_of_le le_rfl ((Assn.noDebt_cells _ _).mul (Assn.noDebt_cells _ _))

/-- Bridge from first-layer `propagateLabels_meetsContract` to `stage1PropLabelsSpec`. -/
theorem propagateLabels_meets_stage1PropSpec {w b : ℕ} {p : Program}
    (hp : p.HasAt b (propagateLabelsModule b)) :
    Meets w p b ((stage1PropLabelsSpec w).withCost fun x _ => 3000 * x.J.m + 800) := by
  have hproc : p.procs[b]? = some (propagateLabelsBody (b + 1) (b + 9)) := hp.head
  refine ⟨propagateLabelsBody (b + 1) (b + 9), hproc, fun x args => ?_⟩
  have hC0 := propagateLabels_meetsContract (w := w) hp x.C x.J x.flow x.root
  intro st ω h hf c hpre hd hin hok hw
  obtain ⟨hρ, hpre'⟩ := Assn.pure_mul_apply.mp hpre
  obtain ⟨h1, h2, c1, c2, hd12, rfl, rfl, hpre1, hc2⟩ := hpre'
  dsimp only [stage1PropLabelsSpec] at hpre1
  obtain ⟨a, ha⟩ := (Assn.iSup_apply _ _ _).mp hpre1
  obtain ⟨base, hbase⟩ := (Assn.iSup_apply _ _ _).mp ha
  rw [mul_assoc, mul_assoc, mul_assoc] at hbase
  obtain ⟨⟨rfl, hfp_le, hvals, hcosts, hbud, hsp, hw8⟩, hmem⟩ := Assn.pure_mul_apply.mp hbase
  set fp := a + x.J.solverWords.length with hfp_def
  set flist := List.ofFn fun e => (x.flow e).toNat with hflist_def
  have hflist_len : flist.length = x.J.m := List.length_ofFn
  let m₀ : ℕ → ℕ := fun addr =>
    if addr < fp then x.J.solverWords.getD (addr - a) 0
    else if addr < fp + x.J.m then flist.getD (addr - fp) 0
    else x.mPad addr
  have hat_J : ListAt m₀ a x.J.solverWords := fun i hi => by
    have hlt : a + i < fp := by omega
    simp only [m₀, hlt, ↓reduceIte, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]
  have hat_f : ListAt m₀ fp flist := fun i hi => by
    have hge : ¬ (fp + i < fp) := by omega
    have hlt : fp + i < fp + x.J.m := by omega
    simp only [m₀, hge, hlt, ↓reduceIte, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]
  have hcells_eq :
      Assn.list a x.J.solverWords * Assn.list fp flist *
        Assn.cells (Set.Ico (fp + x.J.m) base) x.mPad =
      Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ := by
    rw [stage1PropCells, Assn.list_eq_cells, Assn.list_eq_cells, hflist_len]
    have hc1 : Assn.cells (Set.Ico a fp) (fun addr => x.J.solverWords.getD (addr - a) 0) =
        Assn.cells (Set.Ico a fp) m₀ := Assn.cells_congr fun addr haddr => by
      simp only [Set.mem_Ico] at haddr; simp [m₀, haddr.2]
    have hc2' : Assn.cells (Set.Ico fp (fp + x.J.m)) (fun addr => flist.getD (addr - fp) 0) =
        Assn.cells (Set.Ico fp (fp + x.J.m)) m₀ := Assn.cells_congr fun addr haddr => by
      simp only [Set.mem_Ico] at haddr
      simp [m₀, show ¬ addr < fp by omega, haddr.2]
    have hc3 : Assn.cells (Set.Ico (fp + x.J.m) base) x.mPad =
        Assn.cells (Set.Ico (fp + x.J.m) base) m₀ := Assn.cells_congr fun addr haddr => by
      simp only [Set.mem_Ico] at haddr
      simp [m₀, show ¬ addr < fp by omega, show ¬ addr < fp + x.J.m by omega]
    rw [hc1, hc2', hc3]
    have hd_a : Disjoint (Set.Ico a fp) (Set.Ico fp (fp + x.J.m)) := by
      rw [Set.disjoint_left]; intro z hz1 hz2; simp only [Set.mem_Ico] at hz1 hz2; omega
    have hd_b : Disjoint (Set.Ico a (fp + x.J.m)) (Set.Ico (fp + x.J.m) base) := by
      rw [Set.disjoint_left]; intro z hz1 hz2; simp only [Set.mem_Ico] at hz1 hz2; omega
    rw [← Assn.cells_union hd_a, Set.Ico_union_Ico_eq_Ico (by omega) (by omega),
      ← Assn.cells_union hd_b, Set.Ico_union_Ico_eq_Ico (by omega) hfp_le]
  have hmem' : (Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ *
      Assn.free base (2 ^ w - base)) h1 c1 := by
    rw [← hcells_eq, mul_assoc, mul_assoc]
    simpa only [mul_assoc] using hmem
  have hbase_le : base ≤ 2 ^ w := by omega
  obtain ⟨hc1, hbelow, h1_eq⟩ := Assn.cells_mul_free_top hbase_le hmem' (Heap.addrOk_union.mp hok).1
  have hin_all := hin.of_union_left
  have hin1 := Heap.in_restrict.mp (h1_eq ▸ hin_all.of_union_left)
  have hfD := Heap.disjoint_restrict_left.mp (h1_eq ▸ (Heap.disjoint_union_left.mp hd).1)
  have hc2_eq : h2 = Heap.empty ∧ c2 = (3000 * x.J.m + 800 : ℤ) := hc2
  obtain ⟨rfl, rfl⟩ := hc2_eq
  rw [Heap.union_empty] at hok hd hin
  set st₀ := st.withHigh w fun _ => 0 with hst₀
  have hagree : ∀ addr ∈ stage1PropCells [a, fp, x.root.val, base], st₀.mem addr = m₀ addr :=
    fun addr haddr => by
      have hlt : addr < 2 ^ w := by have := hbelow addr haddr; omega
      show memMix w st.mem (fun _ => 0) addr = _
      rw [memMix_of_lt hlt]
      simpa [hbelow addr haddr] using hin1 addr (Or.inl haddr)
  have hzero : ZeroFrom st₀.mem base := fun addr haddr => by
    by_cases hlt : addr < 2 ^ w
    · show memMix w st.mem (fun _ => 0) addr = _
      rw [memMix_of_lt hlt]
      simpa [Nat.not_lt.mpr haddr] using hin1 addr (Or.inr ⟨haddr, hlt⟩)
    · show memMix w st.mem (fun _ => 0) addr = _
      rw [memMix_of_ge (Nat.not_lt.mp hlt)]
  have hat_J₀ : ListAt st₀.mem a x.J.solverWords := fun i hi => by
    rw [hagree (a + i) (by simp only [stage1PropCells, Set.mem_Ico]; omega)]
    exact hat_J i hi
  have hat_f₀ : ListAt st₀.mem fp flist := fun i hi => by
    rw [hagree (fp + i) (by simp only [stage1PropCells, Set.mem_Ico]; omega)]
    exact hat_f i hi
  obtain ⟨body', hproc', o, st₁, k, hrun, ⟨hlo, hhi, hstate, hz1, hframe1⟩, hk⟩ :=
    hC0 [a, fp, x.root.val, base] st₀.mem st.pos ω (args_lt_of_argRegs (hρ ▸ hw.1))
      ⟨a, fp, base, rfl, hat_J₀, hat_f₀, by omega, hfp_le, hvals, hcosts, hbud, hzero, hsp, hw8⟩
  rw [hproc] at hproc'; cases hproc'
  rw [show startState [a, fp, x.root.val, base] st₀.mem st.pos = st₀ from
    (eq_startState_of_regs (st := st₀) hρ).symm] at hrun
  have hrun' := Runs.of_withHigh_zero hrun hw
  have hbase_arg : heapArg [a, fp, x.root.val, base] = base := rfl
  rw [hbase_arg] at hlo hhi hstate hframe1
  dsimp only [labelNodes] at hlo hhi
  have hv_le : o.value ≤ 2 ^ w := by omega
  set st' := st₁.withHigh w st.mem with hst'
  have hlow' : ∀ addr < 2 ^ w, st'.mem addr = st₁.mem addr := fun addr hlt => memMix_of_lt hlt
  have hcost_le : k ≤ 3000 * x.J.m + 800 := hk
  refine ⟨o, st', k, Heap.restrict (stage1PropCells [a, fp, x.root.val, base] ∪ Set.Ico base (2 ^ w)) st'.mem,
    c1 + (3000 * x.J.m + 800 : ℤ) - k, hrun', ?_,
    Heap.disjoint_restrict_left.mpr hfD, ?_,
    Heap.addrOk_restrict.mpr (Heap.addrOk_restrict.mp (h1_eq ▸ hok)),
    by omega⟩
  · have hown_full :
        (Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ *
          Assn.cells (Set.Ico base o.value) st₁.mem *
          Assn.free o.value (2 ^ w - o.value))
        (Heap.restrict (stage1PropCells [a, fp, x.root.val, base] ∪ Set.Ico base (2 ^ w)) st'.mem) 0 := by
      rw [Assn.cells_congr (D := Set.Ico base o.value) (m' := st'.mem) fun addr haddr => by
        simp only [Set.mem_Ico] at haddr; exact (hlow' addr (by omega)).symm]
      refine Assn.cells_mul_cells_mul_free_top hbelow (by omega) hv_le (fun addr haddr => ?_)
        (fun addr haddr hlt => ?_)
      · have hlt : addr < base := hbelow addr haddr
        rw [hlow' addr (by omega), hframe1 addr hlt, hagree addr haddr]
      · rw [hlow' addr hlt]; exact hz1 addr haddr
    have htab_le : Assn.cells (Set.Ico base o.value) st₁.mem ≤
        Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) * Assn.gc :=
      signedTable_extract_from_cells (by omega) hstate.labels
    have hcomb :
        Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ *
          Assn.cells (Set.Ico base o.value) st₁.mem *
          Assn.free o.value (2 ^ w - o.value) ≤
        Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) *
          Assn.free o.value (2 ^ w - o.value) * Assn.gc := by
      calc _ ≤ Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ *
              (Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) *
                Assn.gc) * Assn.free o.value (2 ^ w - o.value) :=
            Assn.mul_le_mul_of_le (Assn.mul_le_mul_of_le le_rfl htab_le) le_rfl
        _ = (Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) *
              Assn.free o.value (2 ^ w - o.value)) *
              (Assn.cells (stage1PropCells [a, fp, x.root.val, base]) m₀ * Assn.gc) := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
        _ ≤ _ := Assn.mul_le_mul_of_le le_rfl
            ((Assn.noDebt_cells _ _).mul (le_rfl : Assn.gc ≤ Assn.gc))
    have hstep := hcomb _ _ hown_full
    have hpost_le :
        Assn.list (base + 2) ((List.ofFn (x.J.propagateLabels x.flow x.root).1.labels).flatMap encodeSignedPair) *
          Assn.free o.value (2 ^ w - o.value) * Assn.gc ≤
        (stage1PropLabelsSpec w).post x [a, fp, x.root.val, base] o.value * Assn.gc := by
      refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun a' : ℕ => ⨆ base' : ℕ, _) a) le_rfl)
      refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun base' : ℕ => _) base) le_rfl)
      dsimp only
      have hpure_ok : [a, fp, x.root.val, base] = [a, fp, x.root.val, base] ∧
          base + 3 + 5 * x.J.n ≤ o.value ∧ o.value ≤ base + 3 + 5 * x.J.n + 6 * x.J.m :=
        ⟨rfl, hlo, hhi⟩
      rw [eq_true hpure_ok, Assn.pure_true, one_mul, mul_assoc]
    have hfinal := hpost_le _ _ hstep
    obtain ⟨hA, hB, cA, cB, hdAB, heqH, heqC, hA_sat, hB_sat⟩ := hfinal
    refine ⟨hA, hB, cA, cB + (c1 + (3000 * x.J.m + 800 : ℤ) - k), hdAB, heqH, by omega, hA_sat, ?_⟩
    change 0 ≤ cB at hB_sat
    change 0 ≤ cB + (c1 + (3000 * x.J.m + 800 : ℤ) - k)
    omega
  · refine (Heap.in_union (Heap.disjoint_restrict_left.mpr hfD)).mpr
      ⟨Heap.in_restrict.mpr fun _ _ => rfl, fun addr v hx => ?_⟩
    have hnot : addr ∉ stage1PropCells [a, fp, x.root.val, base] ∪ Set.Ico base (2 ^ w) :=
      fun ha' => by rw [hfD addr ha'] at hx; cases hx
    have hold := ((Heap.in_union hd).mp hin).2 addr v hx
    by_cases haH : addr < base
    · rw [hlow' addr (by omega), hframe1 addr haH]
      show memMix w st.mem (fun _ => 0) addr = _
      rw [memMix_of_lt (by omega), hold]
    · have hge : 2 ^ w ≤ addr := by
        by_contra hlt
        exact hnot (Or.inr ⟨Nat.not_lt.mp haH, Nat.not_le.mp hlt⟩)
      show memMix w st₁.mem st.mem addr = _
      rw [memMix_of_ge hge, hold]

/-- Helper lemma merging a `List` and a `cells` range into one contiguous `cells` range. -/
theorem list_mul_cells_eq_cells {a b : ℕ} {l : List ℕ} {m : ℕ → ℕ} (hle : a + l.length ≤ b) :
    Assn.list a l * Assn.cells (Set.Ico (a + l.length) b) m =
      Assn.cells (Set.Ico a b) (fun x => if x < a + l.length then l.getD (x - a) 0 else m x) := by
  rw [Assn.list_eq_cells]
  have h1 : Assn.cells (Set.Ico a (a + l.length)) (fun x => l.getD (x - a) 0) =
      Assn.cells (Set.Ico a (a + l.length))
        (fun x => if x < a + l.length then l.getD (x - a) 0 else m x) :=
    Assn.cells_congr fun x hx => by simp only [Set.mem_Ico] at hx; simp [hx.2]
  have h2 : Assn.cells (Set.Ico (a + l.length) b) m =
      Assn.cells (Set.Ico (a + l.length) b)
        (fun x => if x < a + l.length then l.getD (x - a) 0 else m x) :=
    Assn.cells_congr fun x hx => by simp only [Set.mem_Ico] at hx; simp [show ¬ x < a + l.length by omega]
  have hd : Disjoint (Set.Ico a (a + l.length)) (Set.Ico (a + l.length) b) := by
    rw [Set.disjoint_left]; intro x hx1 hx2; simp only [Set.mem_Ico] at hx1 hx2; omega
  rw [h1, h2, ← Assn.cells_union hd, Set.Ico_union_Ico_eq_Ico (by omega) hle]

end MinCostFlow.NarrowProg.Stage1
