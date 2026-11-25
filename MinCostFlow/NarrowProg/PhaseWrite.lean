module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.Defs
public import MinCostFlow.NarrowProg.LimbBit
public import MinCostFlow.NarrowProg.TopBitLength
public import MinCostFlow.Scaling.PositiveCapacities
public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.Narrow.CappedRecurrence
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Writing one bit-scaling phase instance in solver format

Given a circulation `I` whose capacities are stored as base-`2 ^ k` limb lists, the current capped
residuals `ρ̃`, the current capped flows `g̃`, and the current bit index `shift`, `phaseWrite`
writes `J.solverWords` for the positive-capacity phase instance
`J = (bitScalePhaseInstance I T t g).positiveInstance` into a `2 + 10 * I.m` buffer, in
`O(I.m + 1)` steps (calling `limbBit` once per edge).

The writer is split into three small procedures:
- `phaseWriteFwd`: writes the `5 * I.m` forward slot words (calling `limbBit` once per edge).
- `phaseWriteRev`: writes the `5 * I.m` reverse slot words.
- `phaseWrite`: writes the 2-word header `[I.n + 1, 2 * I.m]` and calls `phaseWriteFwd` and
  `phaseWriteRev`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

attribute [local sep_len] List.length_ofFn

/-! ### Shared input layout for Stage 2 -/

/-- Pointers stored inside the 9-word Stage 2 input descriptor at `pIn`. -/
structure BitScalePtrs where
  pTail : ℕ
  pHead : ℕ
  pCSign : ℕ
  pCMag : ℕ
  pCapPtrs : ℕ
  pCapLens : ℕ

/-- Memory layout of the Stage 2 input circulation `I` with base-`2 ^ k` capacity limb lists:
a 9-word descriptor at `pIn` pointing to the edge tables and capacity limb arrays. -/
def bitScaleInput (I : Circulation) (k : ℕ) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (pIn pTail pHead pCSign pCMag pCapPtrs pCapLens : ℕ) : Assn :=
  Assn.list pIn [I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens] *
  Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
  Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
  Assn.list pCSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
  Assn.list pCMag (List.ofFn fun e : Fin I.m => (I.cost e).natAbs) *
  Assn.list pCapPtrs capPtrs *
  Assn.list pCapLens (capLimbs.map List.length) *
  ∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j [])

theorem bitScaleInput_eq (I : Circulation) (k : ℕ) (capPtrs : List ℕ) (capLimbs : List (List ℕ))
    (pIn pTail pHead pCSign pCMag pCapPtrs pCapLens : ℕ) :
    bitScaleInput I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens =
      Assn.list pIn [I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens] *
      Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
      Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
      Assn.list pCSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
      Assn.list pCMag (List.ofFn fun e : Fin I.m => (I.cost e).natAbs) *
      Assn.list pCapPtrs capPtrs *
      Assn.list pCapLens (capLimbs.map List.length) *
      ∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []) :=
  rfl

/-! ### Exact solver-word decomposition of `positiveInstance` -/

/-- The 5 solver words for forward slot `e` in a bit-scaling phase instance after positive-capacity
encoding. -/
def phaseFwdWords (I : Circulation) (rho : Fin I.m → ℕ) (shift : ℕ) (e : Fin I.m) : List ℕ :=
  let cap := min (2 * rho e + capBit I shift e) (I.m + 1)
  if cap = 0 then [I.n, I.n, 1, 0, 0]
  else [(I.tail e).val, (I.head e).val, cap, if I.cost e < 0 then 1 else 0, (I.cost e).natAbs]

/-- The 5 solver words for reverse slot `e` in a bit-scaling phase instance after positive-capacity
encoding. -/
def phaseRevWords (I : Circulation) (gcap : Fin I.m → ℕ) (e : Fin I.m) : List ℕ :=
  let cap := min (2 * gcap e) (I.m + 1)
  if cap = 0 then [I.n, I.n, 1, 0, 0]
  else [(I.head e).val, (I.tail e).val, cap, if -I.cost e < 0 then 1 else 0, (I.cost e).natAbs]

/-- Concatenation of the first `i` 5-word edge records. -/
def prefixEdgeWords (m : ℕ) (f : Fin m → List ℕ) (i : ℕ) : List ℕ :=
  ((List.finRange m).take i).flatMap f

theorem length_phaseFwdWords (I : Circulation) (rho : Fin I.m → ℕ) (shift : ℕ) (e : Fin I.m) :
    (phaseFwdWords I rho shift e).length = 5 := by
  unfold phaseFwdWords; dsimp only; split_ifs <;> rfl

theorem length_phaseRevWords (I : Circulation) (gcap : Fin I.m → ℕ) (e : Fin I.m) :
    (phaseRevWords I gcap e).length = 5 := by
  unfold phaseRevWords; dsimp only; split_ifs <;> rfl

theorem prefixEdgeWords_zero (m : ℕ) (f : Fin m → List ℕ) :
    prefixEdgeWords m f 0 = [] := rfl

theorem prefixEdgeWords_succ {m : ℕ} (f : Fin m → List ℕ) {i : ℕ} (hi : i < m) :
    prefixEdgeWords m f (i + 1) = prefixEdgeWords m f i ++ f ⟨i, hi⟩ := by
  unfold prefixEdgeWords
  have hlen : i < (List.finRange m).length := by simp [hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton, List.getElem_finRange]
  rfl

theorem prefixEdgeWords_all (m : ℕ) (f : Fin m → List ℕ) :
    prefixEdgeWords m f m = (List.finRange m).flatMap f := by
  unfold prefixEdgeWords
  rw [List.take_of_length_le (by simp)]

theorem length_prefixEdgeWords {m : ℕ} {f : Fin m → List ℕ} (hf : ∀ e, (f e).length = 5)
    {i : ℕ} (hi : i ≤ m) :
    (prefixEdgeWords m f i).length = 5 * i := by
  induction i with
  | zero => simp [prefixEdgeWords_zero]
  | succ i ih =>
    rw [prefixEdgeWords_succ f (by omega), List.length_append, ih (by omega), hf]
    omega

private theorem finRange_add (m : ℕ) :
    List.finRange (m + m) =
      (List.finRange m).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd m) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.length_finRange] at h1
  rw [List.getElem_finRange]
  by_cases hi : i < m
  · rw [List.getElem_append_left (by simp [hi]), List.getElem_map, List.getElem_finRange]
    rfl
  · rw [List.getElem_append_right (by simp; omega), List.getElem_map, List.getElem_finRange]
    ext
    simp only [Fin.val_cast, List.length_map, List.length_finRange, Fin.val_natAdd]
    omega

/-- The solver words of `(bitScalePhaseInstance I T t g).positiveInstance` split into the 2-word
header `[I.n + 1, 2 * I.m]`, the `5 * I.m` forward slot words, and the `5 * I.m` reverse slot words. -/
theorem positiveInstance_solverWords_eq (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ)
    (hg : ∀ e, 0 ≤ g e ∧ g e ≤ (truncInstance I (T - t)).capacity e) :
    (bitScalePhaseInstance I T t g).positiveInstance.solverWords =
      [I.n + 1, 2 * I.m] ++
      (List.finRange I.m).flatMap
        (phaseFwdWords I (cappedResidual I T t g (I.m + 1)) (T - (t + 1))) ++
      (List.finRange I.m).flatMap (phaseRevWords I (cappedFlow g (I.m + 1))) := by
  set P := bitScalePhaseInstance I T t g
  set J := P.positiveInstance
  have hm : J.m = 2 * I.m := by change I.m + I.m = 2 * I.m; omega
  have h1 : J.solverWords = [I.n + 1, 2 * I.m] ++
      (List.finRange (I.m + I.m)).flatMap J.solverEdgeWords := by
    simp only [Circulation.solverWords, List.cons_append, List.nil_append]
    congr 1
    exact congrArg (· :: _) hm
  rw [h1, finRange_add, List.flatMap_append, List.flatMap_map, List.flatMap_map, List.append_assoc]
  congr 1
  congr 1
  · refine List.flatMap_congr fun e _ => ?_
    have hcap : P.capacity (Fin.castAdd I.m e) =
        min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - (t + 1)) e) (I.m + 1) :=
      phaseInstance_capacity_forward (truncInstance I (T - t))
        (capBit I (T - (t + 1))) g hg (I.m + 1) e
    unfold Circulation.solverEdgeWords phaseFwdWords
    dsimp only [J, Circulation.positiveInstance]
    by_cases hz : P.capacity (Fin.castAdd I.m e) = 0
    · have hz' : min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - (t + 1)) e) (I.m + 1) = 0 :=
        hcap ▸ hz
      simp only [hz, hz', ↓reduceIte, Fin.val_last, lt_self_iff_false, Int.natAbs_zero]
      rfl
    · have hz' : min (2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - (t + 1)) e) (I.m + 1) ≠ 0 :=
        hcap ▸ hz
      simp only [hz', ↓reduceIte, Fin.val_castSucc, hcap]
      simp only [P, bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
        doubled, truncInstance, Fin.addCases_left]
  · refine List.flatMap_congr fun e _ => ?_
    have hcap : P.capacity (Fin.natAdd I.m e) = min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) :=
      phaseInstance_capacity_reverse (truncInstance I (T - t))
        (capBit I (T - (t + 1))) g (fun k => (hg k).1) (I.m + 1) e
    unfold Circulation.solverEdgeWords phaseRevWords
    dsimp only [J, Circulation.positiveInstance]
    by_cases hz : P.capacity (Fin.natAdd I.m e) = 0
    · have hz' : min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) = 0 := hcap ▸ hz
      simp only [hz, hz', ↓reduceIte, Fin.val_last, lt_self_iff_false, Int.natAbs_zero]
      rfl
    · have hz' : min (2 * cappedFlow g (I.m + 1) e) (I.m + 1) ≠ 0 := hcap ▸ hz
      simp only [hz', ↓reduceIte, Fin.val_castSucc, hcap]
      simp only [P, bitScalePhaseInstance, phaseInstance, capCapacities, Circulation.residual,
        doubled, truncInstance, Fin.addCases_right, Int.natAbs_neg]

private theorem list_split_five {pDst : ℕ} {L buf : List ℕ} {i : ℕ}
    (hL : L.length = 5 * i) (hi : 5 * i + 5 ≤ buf.length) :
    Assn.list pDst (L ++ buf.drop (5 * i)) =
      Assn.list pDst L *
      (pDst + 5 * i ↦ buf[5 * i]'(by omega)) *
      (pDst + 5 * i + 1 ↦ buf[5 * i + 1]'(by omega)) *
      (pDst + 5 * i + 2 ↦ buf[5 * i + 2]'(by omega)) *
      (pDst + 5 * i + 3 ↦ buf[5 * i + 3]'(by omega)) *
      (pDst + 5 * i + 4 ↦ buf[5 * i + 4]'(by omega)) *
      Assn.list (pDst + 5 * (i + 1)) (buf.drop (5 * (i + 1))) := by
  have hd : buf.drop (5 * i) =
      buf[5 * i]'(by omega) :: buf[5 * i + 1]'(by omega) :: buf[5 * i + 2]'(by omega) ::
      buf[5 * i + 3]'(by omega) :: buf[5 * i + 4]'(by omega) :: buf.drop (5 * (i + 1)) := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega)]
    simp only [show 5 * i + 1 + 1 = 5 * i + 2 by omega,
      show 5 * i + 2 + 1 = 5 * i + 3 by omega,
      show 5 * i + 3 + 1 = 5 * i + 4 by omega,
      show 5 * i + 4 + 1 = 5 * (i + 1) by omega]
  rw [Assn.list_append, hL, hd]
  simp only [Assn.list_cons, mul_assoc,
    show pDst + 5 * i + 1 + 1 = pDst + 5 * i + 2 by omega,
    show pDst + 5 * i + 2 + 1 = pDst + 5 * i + 3 by omega,
    show pDst + 5 * i + 3 + 1 = pDst + 5 * i + 4 by omega,
    show pDst + 5 * i + 4 + 1 = pDst + 5 * (i + 1) by omega]

private theorem list_join_five {pDst : ℕ} {L buf : List ℕ} {i : ℕ}
    (hL : L.length = 5 * i) (a0 a1 a2 a3 a4 : ℕ) :
    Assn.list pDst L *
      (pDst + 5 * i ↦ a0) *
      (pDst + 5 * i + 1 ↦ a1) *
      (pDst + 5 * i + 2 ↦ a2) *
      (pDst + 5 * i + 3 ↦ a3) *
      (pDst + 5 * i + 4 ↦ a4) *
      Assn.list (pDst + 5 * (i + 1)) (buf.drop (5 * (i + 1))) =
    Assn.list pDst ((L ++ [a0, a1, a2, a3, a4]) ++ buf.drop (5 * (i + 1))) := by
  rw [Assn.list_append, Assn.list_append, List.length_append, hL]
  simp only [Assn.list_cons, Assn.list_nil, mul_one, List.length_cons, List.length_nil, mul_assoc,
    show pDst + 5 * i + 1 + 1 = pDst + 5 * i + 2 by omega,
    show pDst + 5 * i + 2 + 1 = pDst + 5 * i + 3 by omega,
    show pDst + 5 * i + 3 + 1 = pDst + 5 * i + 4 by omega,
    show pDst + 5 * i + 4 + 1 = pDst + 5 * (i + 1) by omega,
    show pDst + (5 * i + 5) = pDst + 5 * (i + 1) by omega]

private theorem rev_cost_sign (c : ℤ) :
    (if 0 < c.natAbs then 1 - (if c < 0 then 1 else 0) else 0) =
      if -c < 0 then 1 else 0 := by
  by_cases h0 : c = 0
  · subst h0; simp
  · by_cases hlt : c < 0
    · have hpos : 0 < c.natAbs := Int.natAbs_pos.mpr h0
      have hneg : ¬ (-c < 0) := by omega
      simp only [hpos, hlt, hneg, ↓reduceIte]
    · have hpos : 0 < c.natAbs := Int.natAbs_pos.mpr h0
      have hneg : -c < 0 := by omega
      simp only [hpos, hlt, hneg, ↓reduceIte]

private theorem set_two {buf : List ℕ} (hlen : buf.length = 2) (a b : ℕ) :
    (buf.set 0 a).set 1 b = [a, b] := by
  rcases buf with _ | ⟨x0, _ | ⟨x1, _ | xs⟩⟩
  · simp at hlen
  · simp at hlen
  · rfl
  · simp at hlen

local macro "sep_five_stores" : tactic =>
  `(tactic| (sep_step; sep_step; sep_step; sep_step; sep_step;
             sep_step; sep_step; sep_step; sep_step))

/-! ### Forward slot writer -/

/-- Named value for `phaseWriteFwdSpec`. -/
structure PhaseWriteFwdData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  rho : Fin I.m → ℕ
  shift : ℕ
  buf : List ℕ

/-- Write the `5 * m` forward slot words into `pDst`, calling `limbBit` (`lb`) once per edge. -/
wram_def phaseWriteFwd (lb : ℕ) (pIn, pRho, shift, pDst) {
  n := mem[pIn]
  m := mem[pIn + 1]
  k := mem[pIn + 2]
  pTail := mem[pIn + 3]
  pHead := mem[pIn + 4]
  pCSign := mem[pIn + 5]
  pCMag := mem[pIn + 6]
  pCapPtrs := mem[pIn + 7]
  pCapLens := mem[pIn + 8]
  M := m + 1
  off := 0
  for i in 0 .. m {
    b := lb(mem[pCapPtrs + i], mem[pCapLens + i], shift, k)
    cap := 2 * mem[pRho + i] + b
    if M < cap {
      cap := M
    }
    if cap == 0 {
      mem[pDst + off] := n
      mem[pDst + off + 1] := n
      mem[pDst + off + 2] := 1
      mem[pDst + off + 3] := 0
      mem[pDst + off + 4] := 0
    } else {
      mem[pDst + off] := mem[pTail + i]
      mem[pDst + off + 1] := mem[pHead + i]
      mem[pDst + off + 2] := cap
      mem[pDst + off + 3] := mem[pCSign + i]
      mem[pDst + off + 4] := mem[pCMag + i]
    }
    off := off + 5
  }
  return 0
}

/-- Specification of `phaseWriteFwd`: overwrites `5 * I.m` cells at `pDst` with the forward slot
words `(List.finRange I.m).flatMap (phaseFwdWords I rho shift)`. -/
def phaseWriteFwdSpec (w : ℕ) : Spec PhaseWriteFwdData where
  pre d args := ⨆ (pIn : ℕ) (pRho : ℕ) (pDst : ℕ),
    ⌜args = [pIn, pRho, d.shift, pDst] ∧
      d.capPtrs.length = d.I.m ∧ d.capLimbs.length = d.I.m ∧ d.buf.length = 5 * d.I.m ∧
      1 ≤ d.k ∧ 5 * d.I.m + 9 < 2 ^ w ∧
      (∀ e, d.rho e ≤ d.I.m + 1) ∧
      (∀ j (hj : j < d.I.m), Limbs d.k (d.capLimbs.getD j []) ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩)⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pRho (List.ofFn d.rho) * Assn.list pDst d.buf
  post d args v := ⨆ (pIn : ℕ) (pRho : ℕ) (pDst : ℕ),
    ⌜args = [pIn, pRho, d.shift, pDst] ∧ v = 0⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pRho (List.ofFn d.rho) *
    Assn.list pDst ((List.finRange d.I.m).flatMap (phaseFwdWords d.I d.rho d.shift))

theorem phaseWriteFwd_meets {w : ℕ} {p : Program} {f lb : ℕ} {Tlb : ℕ}
    (hp : p.procs[f]? = some (phaseWriteFwd lb))
    (hlb : Meets w p lb ((limbBitSpec w).withCost fun _ _ => Tlb)) :
    Meets w p f ((phaseWriteFwdSpec w).withCost fun d _ => (Tlb + 120) * d.I.m + 120) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩, rho, shift, buf⟩ with
    hptrs hlimbs hbuf hk hw hrho hcaps
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hn hm hk_1 hpTail_1 hpHead_1 hpCSign_1 hpCMag_1 hpCapPtrs_1 hpCapLens_1
  subst n m k_1 pTail_1 pHead_1 pCSign_1 pCMag_1 pCapPtrs_1 pCapLens_1
  sep_step; sep_step
  subst M
  sep_for (fun i (t : ℕ × ℕ) =>
    ⟨[pIn, pRho, shift, pDst, I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens,
      I.m + 1, 5 * i, i, t.1, t.2],
      i ≤ I.m, (Tlb + 110) * (I.m - i) + 10,
      [Assn.list pIn [I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens],
       Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val),
       Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val),
       Assn.list pCSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0),
       Assn.list pCMag (List.ofFn fun e : Fin I.m => (I.cost e).natAbs),
       Assn.list pCapPtrs capPtrs,
       Assn.list pCapLens (capLimbs.map List.length),
       ∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []),
       Assn.list pRho (List.ofFn rho),
       Assn.list pDst (prefixEdgeWords I.m (phaseFwdWords I rho shift) i ++ buf.drop (5 * i))]⟩)
    with ⟨t1, t2⟩
  · have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    have hxi : capLimbs.getD i [] = capLimbs[i]'(by omega) :=
      List.getD_eq_getElem capLimbs [] (by omega)
    have hpi : capPtrs.getD i 0 = capPtrs[i]'(by omega) :=
      List.getD_eq_getElem capPtrs 0 (by omega)
    have hLi : Limbs k (capLimbs.getD i []) := (hcaps i hhi).1
    have hVi : Nat.ofDigits (2 ^ k) (capLimbs.getD i []) = I.capacity ⟨i, hhi⟩ := (hcaps i hhi).2
    have hbit_eq : (Nat.ofDigits (2 ^ k) (capLimbs.getD i []) / 2 ^ shift) % 2 =
        capBit I shift ⟨i, hhi⟩ := by rw [hVi]; rfl
    have hpre_len := length_prefixEdgeWords (length_phaseFwdWords I rho shift) (by omega : i ≤ I.m)
    sep_apply list_split_five (pDst := pDst) (buf := buf) hpre_len (by omega)
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))
    sep_step from (k, capLimbs.getD i [], shift)
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))).symm
    have hbi : b = capBit I shift ⟨i, hhi⟩ := by rw [hb, hbit_eq]
    have hb_le : b ≤ 1 := by rw [hbi]; unfold capBit; omega
    have hrho_i : (List.ofFn rho)[i]'(by simp [hhi]) = rho ⟨i, hhi⟩ := by simp
    have hrho_le : rho ⟨i, hhi⟩ ≤ I.m + 1 := hrho ⟨i, hhi⟩
    have hcap_lt : 2 * (List.ofFn rho)[i]'(by simp [hhi]) + b < 2 ^ w := by rw [hrho_i]; omega
    sep_step
    have hcap_eq : cap = 2 * rho ⟨i, hhi⟩ + capBit I shift ⟨i, hhi⟩ := by
      rw [hcap, hrho_i, hbi]
    sep_step
    · -- M < cap
      sep_step
      have hmin : min (2 * rho ⟨i, hhi⟩ + capBit I shift ⟨i, hhi⟩) (I.m + 1) = I.m + 1 := by omega
      have hfw : [(I.tail ⟨i, hhi⟩).val, (I.head ⟨i, hhi⟩).val, I.m + 1,
          if I.cost ⟨i, hhi⟩ < 0 then 1 else 0, (I.cost ⟨i, hhi⟩).natAbs] =
          phaseFwdWords I rho shift ⟨i, hhi⟩ := by
        unfold phaseFwdWords; dsimp only; rw [hmin]; simp
      sep_step
      sep_five_stores
      sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
      simp only [hcap_1, List.getElem_ofFn, hfw, ← prefixEdgeWords_succ _ hhi]
      sep_run
    · -- cap ≤ M
      sep_step
      have hmin : min (2 * rho ⟨i, hhi⟩ + capBit I shift ⟨i, hhi⟩) (I.m + 1) = cap := by omega
      sep_step
      · -- cap = 0
        have hfw : [I.n, I.n, 1, 0, 0] = phaseFwdWords I rho shift ⟨i, hhi⟩ := by
          unfold phaseFwdWords; dsimp only; rw [hmin, hcond_1]; simp
        sep_five_stores
        sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
        rw [hfw, ← prefixEdgeWords_succ _ hhi]
        sep_run
      · -- cap ≠ 0
        have hfw : [(I.tail ⟨i, hhi⟩).val, (I.head ⟨i, hhi⟩).val, cap,
            if I.cost ⟨i, hhi⟩ < 0 then 1 else 0, (I.cost ⟨i, hhi⟩).natAbs] =
            phaseFwdWords I rho shift ⟨i, hhi⟩ := by
          unfold phaseFwdWords; dsimp only; rw [hmin]; simp [hcond_1]
        sep_five_stores
        sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
        simp only [List.getElem_ofFn, hfw, ← prefixEdgeWords_succ _ hhi]
        sep_run
  · rw [prefixEdgeWords_all, List.drop_of_length_le (by omega), List.append_nil]
    sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
    sep_run

/-! ### Reverse slot writer -/

/-- Named value for `phaseWriteRevSpec`. -/
structure PhaseWriteRevData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  gcap : Fin I.m → ℕ
  buf : List ℕ

/-- Write the `5 * m` reverse slot words into `pDst`. -/
wram_def phaseWriteRev (pIn, pGCap, pDst) {
  n := mem[pIn]
  m := mem[pIn + 1]
  pTail := mem[pIn + 3]
  pHead := mem[pIn + 4]
  pCSign := mem[pIn + 5]
  pCMag := mem[pIn + 6]
  M := m + 1
  off := 0
  for i in 0 .. m {
    cap := 2 * mem[pGCap + i]
    if M < cap {
      cap := M
    }
    if cap == 0 {
      mem[pDst + off] := n
      mem[pDst + off + 1] := n
      mem[pDst + off + 2] := 1
      mem[pDst + off + 3] := 0
      mem[pDst + off + 4] := 0
    } else {
      rsign := 0
      if 0 < mem[pCMag + i] {
        rsign := 1 - mem[pCSign + i]
      }
      mem[pDst + off] := mem[pHead + i]
      mem[pDst + off + 1] := mem[pTail + i]
      mem[pDst + off + 2] := cap
      mem[pDst + off + 3] := rsign
      mem[pDst + off + 4] := mem[pCMag + i]
    }
    off := off + 5
  }
  return 0
}

/-- Specification of `phaseWriteRev`: overwrites `5 * I.m` cells at `pDst` with the reverse slot
words `(List.finRange I.m).flatMap (phaseRevWords I gcap)`. -/
def phaseWriteRevSpec (w : ℕ) : Spec PhaseWriteRevData where
  pre d args := ⨆ (pIn : ℕ) (pGCap : ℕ) (pDst : ℕ),
    ⌜args = [pIn, pGCap, pDst] ∧
      d.buf.length = 5 * d.I.m ∧ 5 * d.I.m + 9 < 2 ^ w ∧
      (∀ e, d.gcap e ≤ d.I.m + 1)⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pGCap (List.ofFn d.gcap) * Assn.list pDst d.buf
  post d args v := ⨆ (pIn : ℕ) (pGCap : ℕ) (pDst : ℕ),
    ⌜args = [pIn, pGCap, pDst] ∧ v = 0⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pGCap (List.ofFn d.gcap) *
    Assn.list pDst ((List.finRange d.I.m).flatMap (phaseRevWords d.I d.gcap))

theorem phaseWriteRev_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some phaseWriteRev) :
    Meets w p f ((phaseWriteRevSpec w).withCost fun d _ => 130 * d.I.m + 100) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩, gcap, buf⟩ with
    hbuf hw hgcap
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hn hm hpTail_1 hpHead_1 hpCSign_1 hpCMag_1
  subst n m pTail_1 pHead_1 pCSign_1 pCMag_1
  sep_step; sep_step
  subst M
  sep_for (fun i (t : ℕ × ℕ) =>
    ⟨[pIn, pGCap, pDst, I.n, I.m, pTail, pHead, pCSign, pCMag, I.m + 1, 5 * i, i, t.1, t.2],
      i ≤ I.m, 120 * (I.m - i) + 10,
      [Assn.list pIn [I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens],
       Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val),
       Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val),
       Assn.list pCSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0),
       Assn.list pCMag (List.ofFn fun e : Fin I.m => (I.cost e).natAbs),
       Assn.list pCapPtrs capPtrs,
       Assn.list pCapLens (capLimbs.map List.length),
       ∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []),
       Assn.list pGCap (List.ofFn gcap),
       Assn.list pDst (prefixEdgeWords I.m (phaseRevWords I gcap) i ++ buf.drop (5 * i))]⟩)
    with ⟨t1, t2⟩
  · have hpre_len := length_prefixEdgeWords (length_phaseRevWords I gcap) (by omega : i ≤ I.m)
    sep_apply list_split_five (pDst := pDst) (buf := buf) hpre_len (by omega)
    have hg_i : (List.ofFn gcap)[i]'(by simp [hhi]) = gcap ⟨i, hhi⟩ := by simp
    have hg_le : gcap ⟨i, hhi⟩ ≤ I.m + 1 := hgcap ⟨i, hhi⟩
    have hcap_lt : 2 * (List.ofFn gcap)[i]'(by simp [hhi]) < 2 ^ w := by rw [hg_i]; omega
    have hrc := rev_cost_sign (I.cost ⟨i, hhi⟩)
    sep_step
    have hcap_eq : cap = 2 * gcap ⟨i, hhi⟩ := by rw [hcap, hg_i]
    sep_step
    · -- M < cap
      sep_step
      have hmin : min (2 * gcap ⟨i, hhi⟩) (I.m + 1) = I.m + 1 := by omega
      sep_step; sep_step; sep_step; sep_step; sep_step
      · -- 0 < cmag
        sep_step
        have hrw : [(I.head ⟨i, hhi⟩).val, (I.tail ⟨i, hhi⟩).val, I.m + 1,
            1 - (if I.cost ⟨i, hhi⟩ < 0 then 1 else 0), (I.cost ⟨i, hhi⟩).natAbs] =
            phaseRevWords I gcap ⟨i, hhi⟩ := by
          unfold phaseRevWords; dsimp only; rw [hmin, ← hrc]
          simp only [List.getElem_ofFn] at hcond_2
          simp [hcond_2]
        sep_five_stores
        sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
        simp only [hcap_1, hrsign, List.getElem_ofFn, hrw, ← prefixEdgeWords_succ _ hhi]
        sep_run
      · -- cmag = 0
        sep_step
        have hrw : [(I.head ⟨i, hhi⟩).val, (I.tail ⟨i, hhi⟩).val, I.m + 1,
            0, (I.cost ⟨i, hhi⟩).natAbs] = phaseRevWords I gcap ⟨i, hhi⟩ := by
          unfold phaseRevWords; dsimp only; rw [hmin, ← hrc]
          simp only [List.getElem_ofFn] at hcond_2
          simp [show ¬ 0 < (I.cost ⟨i, hhi⟩).natAbs by omega]
        sep_five_stores
        sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
        simp only [hcap_1, List.getElem_ofFn, hrw, ← prefixEdgeWords_succ _ hhi]
        sep_run
    · -- cap ≤ M
      sep_step
      have hmin : min (2 * gcap ⟨i, hhi⟩) (I.m + 1) = cap := by omega
      sep_step
      · -- cap = 0
        have hrw : [I.n, I.n, 1, 0, 0] = phaseRevWords I gcap ⟨i, hhi⟩ := by
          unfold phaseRevWords; dsimp only; rw [hmin, hcond_1]; simp
        sep_five_stores
        sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
        rw [hrw, ← prefixEdgeWords_succ _ hhi]
        sep_run
      · -- cap ≠ 0
        sep_step; sep_step; sep_step; sep_step
        · -- 0 < cmag
          sep_step
          have hrw : [(I.head ⟨i, hhi⟩).val, (I.tail ⟨i, hhi⟩).val, cap,
              1 - (if I.cost ⟨i, hhi⟩ < 0 then 1 else 0), (I.cost ⟨i, hhi⟩).natAbs] =
              phaseRevWords I gcap ⟨i, hhi⟩ := by
            unfold phaseRevWords; dsimp only; rw [hmin, ← hrc]
            simp only [List.getElem_ofFn] at hcond_2
            simp [hcond_1, hcond_2]
          sep_five_stores
          sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
          simp only [hrsign, List.getElem_ofFn, hrw, ← prefixEdgeWords_succ _ hhi]
          sep_run
        · -- cmag = 0
          sep_step
          have hrw : [(I.head ⟨i, hhi⟩).val, (I.tail ⟨i, hhi⟩).val, cap,
              0, (I.cost ⟨i, hhi⟩).natAbs] = phaseRevWords I gcap ⟨i, hhi⟩ := by
            unfold phaseRevWords; dsimp only; rw [hmin, ← hrc]
            simp only [List.getElem_ofFn] at hcond_2
            simp [hcond_1, show ¬ 0 < (I.cost ⟨i, hhi⟩).natAbs by omega]
          sep_five_stores
          sep_apply list_join_five (pDst := pDst) (buf := buf) hpre_len _ _ _ _ _
          simp only [List.getElem_ofFn, hrw, ← prefixEdgeWords_succ _ hhi]
          sep_run
  · rw [prefixEdgeWords_all, List.drop_of_length_le (by omega), List.append_nil]
    sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
    sep_run

/-! ### Top-level phase instance writer -/

/-- Named value for `phaseWriteSpec`. -/
structure PhaseWriteData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  T : ℕ
  t : ℕ
  g : Fin I.m → ℤ
  buf : List ℕ

/-- Write `J.solverWords` for `J = (bitScalePhaseInstance I T t g).positiveInstance` into the
`2 + 10 * m` buffer at `pBuf`, calling `phaseWriteFwd` (`fwd`) and `phaseWriteRev` (`rev`). -/
wram_def phaseWrite (fwd rev : ℕ) (pIn, pRho, pGCap, shift, pBuf) {
  n := mem[pIn]
  m := mem[pIn + 1]
  mem[pBuf] := n + 1
  mem[pBuf + 1] := 2 * m
  r := fwd(pIn, pRho, shift, pBuf + 2)
  r := rev(pIn, pGCap, pBuf + 2 + 5 * m)
  return 0
}

/-- Specification of `phaseWrite`: fills the `2 + 10 * I.m` cells at `pBuf` with
`(bitScalePhaseInstance I T t g).positiveInstance.solverWords`. -/
def phaseWriteSpec (w : ℕ) : Spec PhaseWriteData where
  pre d args := ⨆ (pIn : ℕ) (pRho : ℕ) (pGCap : ℕ) (pBuf : ℕ),
    ⌜args = [pIn, pRho, pGCap, d.T - (d.t + 1), pBuf] ∧
      d.capPtrs.length = d.I.m ∧ d.capLimbs.length = d.I.m ∧ d.buf.length = 2 + 10 * d.I.m ∧
      1 ≤ d.k ∧ d.I.n + 1 < 2 ^ w ∧ 5 * d.I.m + 9 < 2 ^ w ∧ pBuf + (2 + 10 * d.I.m) < 2 ^ w ∧
      (∀ e, 0 ≤ d.g e ∧ d.g e ≤ (truncInstance d.I (d.T - d.t)).capacity e) ∧
      (∀ j (hj : j < d.I.m), Limbs d.k (d.capLimbs.getD j []) ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩)⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pRho (List.ofFn fun e => cappedResidual d.I d.T d.t d.g (d.I.m + 1) e) *
    Assn.list pGCap (List.ofFn fun e => cappedFlow d.g (d.I.m + 1) e) *
    Assn.list pBuf d.buf
  post d args v := ⨆ (pIn : ℕ) (pRho : ℕ) (pGCap : ℕ) (pBuf : ℕ),
    ⌜args = [pIn, pRho, pGCap, d.T - (d.t + 1), pBuf] ∧ v = 0⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pRho (List.ofFn fun e => cappedResidual d.I d.T d.t d.g (d.I.m + 1) e) *
    Assn.list pGCap (List.ofFn fun e => cappedFlow d.g (d.I.m + 1) e) *
    Assn.list pBuf (bitScalePhaseInstance d.I d.T d.t d.g).positiveInstance.solverWords

private theorem list_split_three (pBuf m : ℕ) {buf : List ℕ} (hbuf : buf.length = 2 + 10 * m) :
    Assn.list pBuf buf =
      Assn.list pBuf (buf.take 2) *
      Assn.list (pBuf + 2) ((buf.drop 2).take (5 * m)) *
      Assn.list (pBuf + 2 + 5 * m) ((buf.drop 2).drop (5 * m)) := by
  have h1 : buf = buf.take 2 ++ ((buf.drop 2).take (5 * m) ++ (buf.drop 2).drop (5 * m)) := by
    rw [List.take_append_drop, List.take_append_drop]
  conv_lhs => rw [h1]
  rw [Assn.list_append, Assn.list_append, List.length_take, Nat.min_eq_left (by omega),
    List.length_take, List.length_drop, Nat.min_eq_left (by omega), mul_assoc]

private theorem list_join_three (pBuf m : ℕ) (a b c : List ℕ) (ha : a.length = 2)
    (hb : b.length = 5 * m) :
    Assn.list pBuf a * Assn.list (pBuf + 2) b * Assn.list (pBuf + 2 + 5 * m) c =
      Assn.list pBuf (a ++ b ++ c) := by
  rw [Assn.list_append, Assn.list_append, List.length_append, ha, hb, Nat.add_assoc]

theorem phaseWrite_meets {w : ℕ} {p : Program} {f fwd rev : ℕ} {Tf Tr : ℕ → ℕ}
    (hp : p.procs[f]? = some (phaseWrite fwd rev))
    (hfwd : Meets w p fwd ((phaseWriteFwdSpec w).withCost fun d _ => Tf d.I.m))
    (hrev : Meets w p rev ((phaseWriteRevSpec w).withCost fun d _ => Tr d.I.m)) :
    Meets w p f ((phaseWriteSpec w).withCost fun d _ => Tf d.I.m + Tr d.I.m + 70) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩, T, t, g, buf⟩ with
    hptrs hlimbs hbuf hk hn hw hbufw hg hcaps
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step
  sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hn_1 hm
  subst hn_1 hm
  sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
  sep_apply list_split_three pBuf I.m hbuf
  have hlen0 : (buf.take 2).length = 2 := by rw [List.length_take]; omega
  have hlen1 : ((buf.drop 2).take (5 * I.m)).length = 5 * I.m := by
    rw [List.length_take, List.length_drop]; omega
  have hlen2 : ((buf.drop 2).drop (5 * I.m)).length = 5 * I.m := by
    rw [List.length_drop, List.length_drop]; omega
  sep_step
  sep_step
  have hhdr : ((buf.take 2).set 0 (I.n + 1)).set 1 (2 * I.m) = [I.n + 1, 2 * I.m] :=
    set_two hlen0 _ _
  have hrho_le : ∀ e, cappedResidual I T t g (I.m + 1) e ≤ I.m + 1 := fun e => Nat.min_le_right _ _
  have hgcap_le : ∀ e, cappedFlow g (I.m + 1) e ≤ I.m + 1 := fun e => Nat.min_le_right _ _
  sep_step from ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
    cappedResidual I T t g (I.m + 1), T - (t + 1), (buf.drop 2).take (5 * I.m)⟩
  sep_step from ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
    cappedFlow g (I.m + 1), (buf.drop 2).drop (5 * I.m)⟩
  rw [hhdr]
  have hfwd_len : ((List.finRange I.m).flatMap
      (phaseFwdWords I (cappedResidual I T t g (I.m + 1)) (T - (t + 1)))).length = 5 * I.m := by
    rw [← prefixEdgeWords_all]
    exact length_prefixEdgeWords (length_phaseFwdWords I _ _) le_rfl
  sep_apply list_join_three pBuf I.m [I.n + 1, 2 * I.m]
    ((List.finRange I.m).flatMap
      (phaseFwdWords I (cappedResidual I T t g (I.m + 1)) (T - (t + 1))))
    ((List.finRange I.m).flatMap (phaseRevWords I (cappedFlow g (I.m + 1))))
    rfl hfwd_len
  rw [← positiveInstance_solverWords_eq I T t g hg]
  sep_run

theorem phaseWrite_meets_direct {w : ℕ} {p : Program} {f fwd rev lb : ℕ}
    (hp : p.procs[f]? = some (phaseWrite fwd rev))
    (hfwd : p.procs[fwd]? = some (phaseWriteFwd lb))
    (hrev : p.procs[rev]? = some phaseWriteRev)
    (hlb : p.procs[lb]? = some limbBit) :
    Meets w p f ((phaseWriteSpec w).withCost fun d _ => 285 * d.I.m + 290) := by
  have h1 := phaseWrite_meets (w := w) (Tf := fun m => (35 + 120) * m + 120)
    (Tr := fun m => 130 * m + 100) hp (phaseWriteFwd_meets hfwd (limbBit_meets hlb))
    (phaseWriteRev_meets hrev)
  exact h1.withCost_mono fun d _ => by omega

theorem phaseWrite_meetsO {w : ℕ} {p : Program} {f fwd rev lb : ℕ}
    (hp : p.procs[f]? = some (phaseWrite fwd rev))
    (hfwd : p.procs[fwd]? = some (phaseWriteFwd lb))
    (hrev : p.procs[rev]? = some phaseWriteRev)
    (hlb : p.procs[lb]? = some limbBit) :
    MeetsO w p f (phaseWriteSpec w) fun d _ => d.I.m + 1 :=
  MeetsO.of_meets (phaseWrite_meets_direct hp hfwd hrev hlb) ⟨290, fun _ => by dsimp only; omega⟩

/-! ### Module -/

/-- Three-procedure module for `phaseWrite`, parameterized by procedure names. -/
def phaseWriteMod {ι : Type} (writeName fwdName revName lbName : ι) : Module ι :=
  ⟨[(fwdName, fun idx => phaseWriteFwd (idx lbName)),
    (revName, fun _ => phaseWriteRev),
    (writeName, fun idx => phaseWrite (idx fwdName) (idx revName))]⟩

theorem phaseWriteMod_noRand {ι : Type} (writeName fwdName revName lbName : ι) :
    (phaseWriteMod writeName fwdName revName lbName).NoRand := by
  wram_no_rand

/-- In any program placing `phaseWriteMod` alongside `limbBit`, `phaseWrite` runs in `O(m + 1)`
steps. -/
theorem phaseWriteMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {writeName fwdName revName lbName : ι}
    (hp : (phaseWriteMod writeName fwdName revName lbName).Placed p idx)
    (hlb : p.procs[idx lbName]? = some limbBit) :
    MeetsO w p (idx writeName) (phaseWriteSpec w) (fun d _ => d.I.m + 1) :=
  phaseWrite_meetsO
    (hp.get (n := writeName) (b := fun idx => phaseWrite (idx fwdName) (idx revName))
      (by simp [phaseWriteMod]))
    (hp.get (n := fwdName) (b := fun idx => phaseWriteFwd (idx lbName))
      (by simp [phaseWriteMod]))
    (hp.get (n := revName) (b := fun _ => phaseWriteRev)
      (by simp [phaseWriteMod]))
    hlb

end MinCostFlow.NarrowProg
