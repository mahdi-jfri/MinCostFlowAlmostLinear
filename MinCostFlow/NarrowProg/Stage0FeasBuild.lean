module

public import MinCostFlow.NarrowProg.Stage0FeasPasses
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4 (builder): `writeStage1Hdr`, `stage0FeasArtBoth`, and `stage0FeasBuild`

- `writeStage1Hdr`: writes the 10-word Stage 1 input header at `pIn` (reused by Item 5).
- `stage0FeasArtBoth`: runs `stage0FeasArtPass` for `wantSign = 0` and `wantSign = 1`, then splits
  the `3 * m` arrays into exact `P'.m` prefixes and `pOneCells` via `feas_split_oneCells`.
- `stage0FeasBuild`: runs `stage0FeasPass1`, `stage0FeasArtBoth`, and `writeStage1Hdr`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Reusable 10-word Stage 1 header writer (`writeStage1Hdr`) -/

private theorem list_split_ten {p : ℕ} {xs : List ℕ} (h : xs.length = 10) :
    Assn.list p xs =
      (p ↦ xs[0]'(by omega)) * (p + 1 ↦ xs[1]'(by omega)) * (p + 2 ↦ xs[2]'(by omega)) *
      (p + 3 ↦ xs[3]'(by omega)) * (p + 4 ↦ xs[4]'(by omega)) * (p + 5 ↦ xs[5]'(by omega)) *
      (p + 6 ↦ xs[6]'(by omega)) * (p + 7 ↦ xs[7]'(by omega)) * (p + 8 ↦ xs[8]'(by omega)) *
      (p + 9 ↦ xs[9]'(by omega)) := by
  rcases xs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4,
    _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  simp only [Assn.list_cons, Assn.list_nil, mul_one, ← mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 1 + 1 + 1 = p + 3 by omega,
    show p + 1 + 1 + 1 + 1 = p + 4 by omega, show p + 1 + 1 + 1 + 1 + 1 = p + 5 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 = p + 6 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 7 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 8 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 9 by omega,
    List.getElem_cons_zero, List.getElem_cons_succ]

private theorem list_join_ten (p a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * (p + 3 ↦ a3) * (p + 4 ↦ a4) *
    (p + 5 ↦ a5) * (p + 6 ↦ a6) * (p + 7 ↦ a7) * (p + 8 ↦ a8) * (p + 9 ↦ a9) =
      Assn.list p [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, ← mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 1 + 1 + 1 = p + 3 by omega,
    show p + 1 + 1 + 1 + 1 = p + 4 by omega, show p + 1 + 1 + 1 + 1 + 1 = p + 5 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 = p + 6 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 7 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 8 by omega,
    show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 9 by omega]

wram_def writeStage1Hdr
    (pIn, n, m, k, pTail, pHead, pCapPtr, pCapLen, pCostSign, pCostPtr, pCostLen) {
  mem[pIn] := n
  mem[pIn + 1] := m
  mem[pIn + 2] := k
  mem[pIn + 3] := pTail
  mem[pIn + 4] := pHead
  mem[pIn + 5] := pCapPtr
  mem[pIn + 6] := pCapLen
  mem[pIn + 7] := pCostSign
  mem[pIn + 8] := pCostPtr
  mem[pIn + 9] := pCostLen
  return 0
}

structure WriteStage1HdrData where
  n : ℕ
  m : ℕ
  k : ℕ
  pTail : ℕ
  pHead : ℕ
  pCapPtr : ℕ
  pCapLen : ℕ
  pCostSign : ℕ
  pCostPtr : ℕ
  pCostLen : ℕ
  buf : List ℕ

def writeStage1HdrSpec (w : ℕ) : Spec WriteStage1HdrData where
  pre := fun d args => ⨆ (pIn : ℕ),
    ⌜args = [pIn, d.n, d.m, d.k, d.pTail, d.pHead, d.pCapPtr, d.pCapLen,
        d.pCostSign, d.pCostPtr, d.pCostLen] ∧
      d.buf.length = 10 ∧ pIn + 10 ≤ 2 ^ w⌝ *
    Assn.list pIn d.buf
  post := fun d args res => ⨆ (pIn : ℕ),
    ⌜args = [pIn, d.n, d.m, d.k, d.pTail, d.pHead, d.pCapPtr, d.pCapLen,
        d.pCostSign, d.pCostPtr, d.pCostLen] ∧ res = 0⌝ *
    Assn.list pIn [d.n, d.m, d.k, d.pTail, d.pHead, d.pCapPtr, d.pCapLen,
      d.pCostSign, d.pCostPtr, d.pCostLen]

theorem writeStage1Hdr_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some writeStage1Hdr) :
    Meets w p f ((writeStage1HdrSpec w).withCost fun _ _ => 70) := by
  sep_enter d with hlen hpIn
  sep_apply list_split_ten hlen
  sep_step; sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step; sep_step
  sep_apply list_join_ten pIn d.n d.m d.k d.pTail d.pHead d.pCapPtr d.pCapLen
    d.pCostSign d.pCostPtr d.pCostLen
  sep_step

/-! ### Two-pass artificial-arc builder (`stage0FeasArtBoth`) -/

private theorem split_zero_prefix (p a cap : ℕ) (h : a ≤ cap) :
    Assn.list p (List.replicate cap 0) =
      Assn.list p (List.replicate a 0 ++ List.replicate (cap - a) 0) := by
  rw [← List.replicate_add, show a + (cap - a) = cap by omega]

private theorem ofFn_append_ptr (pOneCells a b c : ℕ) :
    List.ofFn (fun t : Fin b => pOneCells + (a + t.val)) ++
      List.ofFn (fun t : Fin c => pOneCells + ((a + b) + t.val)) =
      List.ofFn (fun t : Fin (b + c) => pOneCells + (a + t.val)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    by_cases hlt : i < b
    · rw [List.getElem_append_left (by simp; exact hlt)]; simp
    · rw [List.getElem_append_right (by simp; omega)]; simp; omega

private theorem feasBuild_arrays_eq (I : Instance) (hv : I.IsValid)
    (pShCapBuf pShDemBuf L pOneCells : ℕ) :
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    let k := narrowLimbWidth I
    let P' := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    let orig := feasOrigPos I hv I.m
    let preT := orig.map (fun e => (I.edge e).tail) ++
      (feasArtList I 0 I.n).map (fun u => if 0 = 0 then I.n else u.val)
    preT.length + (feasArtList I 1 I.n).length = P'.m ∧
    (preT ++ (feasArtList I 1 I.n).map (fun u => if 1 = 0 then I.n else u.val)) =
      (List.ofFn fun e : Fin P'.m => (P'.tail e).val) ∧
    ((orig.map (fun e => (I.edge e).head) ++
        (feasArtList I 0 I.n).map (fun u => if 0 = 0 then u.val else I.n)) ++
      (feasArtList I 1 I.n).map (fun u => if 1 = 0 then u.val else I.n)) =
      (List.ofFn fun e : Fin P'.m => (P'.head e).val) ∧
    ((orig.map (fun e => pShCapBuf + e.val * L) ++
        (feasArtList I 0 I.n).map (fun u => pShDemBuf + (el.table u - 1) * L)) ++
      (feasArtList I 1 I.n).map (fun u => pShDemBuf + (el.table u - 1) * L)) =
      feasCapPtrs I hv pShCapBuf pShDemBuf L ∧
    ((orig.map (fun e => (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity e)).length) ++
        (feasArtList I 0 I.n).map (fun u => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand I u).natAbs).length)) ++
      (feasArtList I 1 I.n).map (fun u => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand I u).natAbs).length)) =
      (feasCapLimbs I hv).map List.length ∧
    ((List.replicate orig.length 0 ++ List.replicate (feasArtList I 0 I.n).length 1) ++
      List.replicate (feasArtList I 1 I.n).length 1) =
      List.replicate orig.length 0 ++ List.replicate (P'.m - orig.length) 1 ∧
    ((List.replicate orig.length 0 ++ List.replicate (feasArtList I 0 I.n).length 1) ++
      List.replicate (feasArtList I 1 I.n).length 1) =
      (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) ∧
    ((List.replicate orig.length 0 ++ List.replicate (feasArtList I 0 I.n).length 1) ++
      List.replicate (feasArtList I 1 I.n).length 1) =
      (feasCostLimbs I hv).map List.length ∧
    ((List.replicate orig.length 0 ++
        List.ofFn (fun t : Fin (feasArtList I 0 I.n).length => pOneCells + (orig.length + t.val))) ++
      List.ofFn (fun t : Fin (feasArtList I 1 I.n).length => pOneCells + (preT.length + t.val))) =
      feasCostPtrs I hv pOneCells := by
  dsimp only
  have hm_eq := feas_m_eq I hv
  have hfl0 : feasArtList I 0 I.n = feasArtPos I I.n := rfl
  have hfl1 : feasArtList I 1 I.n = feasArtNeg I I.n := rfl
  have hpre : (List.map (fun e => (I.edge e).tail) (feasOrigPos I hv I.m) ++
      List.map (fun u : Fin I.n => if 0 = 0 then I.n else u.val) (feasArtList I 0 I.n)).length =
      (feasOrigPos I hv I.m).length + (feasArtPos I I.n).length := by simp [hfl0]
  have hrep : (List.replicate (feasOrigPos I hv I.m).length 0 ++
        List.replicate (feasArtList I 0 I.n).length 1) ++
      List.replicate (feasArtList I 1 I.n).length 1 =
      List.replicate (feasOrigPos I hv I.m).length 0 ++
        List.replicate ((FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m -
          (feasOrigPos I hv I.m).length) 1 := by
    rw [List.append_assoc, ← List.replicate_add]
    congr 2; rw [hfl0, hfl1, hm_eq]; omega
  refine ⟨by rw [hpre, hfl1]; exact hm_eq.symm, ?_, ?_, ?_, ?_, hrep, ?_, ?_, ?_⟩
  · rw [feasTails_eq]; simp [hfl0, hfl1]
  · rw [feasHeads_eq]; simp [hfl0, hfl1]
  · rw [feasCapPtrs_eq]; simp [hfl0, hfl1]
  · rw [feasCapLens_eq]; simp [hfl0, hfl1]
  · rw [hrep, feasCostSigns_eq]
  · rw [hrep, feasCostLens_eq]
  · rw [feasCostPtrs_eq, List.append_assoc]
    congr 1
    rw [hpre, hfl0, ofFn_append_ptr]
    have hsum : (feasArtPos I I.n).length + (feasArtList I 1 I.n).length =
        (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m -
          (feasOrigPos I hv I.m).length := by rw [hfl1, hm_eq]; omega
    apply List.ext_getElem
    · simp [hsum]
    · intro i _ _; simp

wram_def stage0FeasArtBoth (artPass : ℕ)
    (pLabels, n, pShDemBuf, pShDemSign, pShDemLen, L,
     pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells, m1Orig) {
  m1Pos := artPass(pLabels, n, pShDemBuf, pShDemSign, pShDemLen, L,
    pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells, m1Orig, 0)
  m1 := artPass(pLabels, n, pShDemBuf, pShDemSign, pShDemLen, L,
    pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells, m1Pos, 1)
  return m1
}

structure Stage0FeasArtBothData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ
  pShCapBuf : ℕ

def stage0FeasArtBothSpec (w : ℕ) : Spec Stage0FeasArtBothData where
  pre := fun d args => ⨆ (pLabels : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let orig := feasOrigPos d.I d.hv d.I.m
    let cap := 3 * d.I.m
    ⌜args = [pLabels, d.I.n, pShDemBuf, pShDemSign, pShDemLen, d.L,
        pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
        orig.length] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      pTail1 + cap ≤ 2 ^ w ∧ pHead1 + cap ≤ 2 ^ w ∧
      pCapPtr1 + cap ≤ 2 ^ w ∧ pCapLen1 + cap ≤ 2 ^ w ∧
      pCostSign1 + cap ≤ 2 ^ w ∧ pCostPtr1 + cap ≤ 2 ^ w ∧
      pCostLen1 + cap ≤ 2 ^ w ∧ pOneCells + cap ≤ 2 ^ w ∧
      cap < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pTail1 (orig.map (fun e => (d.I.edge e).tail) ++ List.replicate (cap - orig.length) 0) *
    Assn.list pHead1 (orig.map (fun e => (d.I.edge e).head) ++ List.replicate (cap - orig.length) 0) *
    Assn.list pCapPtr1 (orig.map (fun e => d.pShCapBuf + e.val * d.L) ++ List.replicate (cap - orig.length) 0) *
    Assn.list pCapLen1 (orig.map (fun e =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
      List.replicate (cap - orig.length) 0) *
    Assn.list pCostSign1 (List.replicate cap 0) *
    Assn.list pCostPtr1 (List.replicate cap 0) *
    Assn.list pCostLen1 (List.replicate cap 0) *
    Assn.list pOneCells (List.replicate cap 0)
  post := fun d args res => ⨆ (pLabels : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [pLabels, d.I.n, pShDemBuf, pShDemSign, pShDemLen, d.L,
        pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
        orig.length] ∧
      res = P'.m⌝ *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pTail1 (List.ofFn fun e : Fin P'.m => (P'.tail e).val) *
    Assn.list pHead1 (List.ofFn fun e : Fin P'.m => (P'.head e).val) *
    Assn.list pCapPtr1 (feasCapPtrs d.I d.hv d.pShCapBuf pShDemBuf d.L) *
    Assn.list pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) *
    Assn.list pCostSign1 (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) *
    Assn.list pCostPtr1 (feasCostPtrs d.I d.hv pOneCells) *
    Assn.list pCostLen1 ((feasCostLimbs d.I d.hv).map List.length) *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCostPtrs d.I d.hv pOneCells).getD j 0)
        ((feasCostLimbs d.I d.hv).getD j [])) *
    Assn.gc

theorem stage0FeasArtBoth_meets {w : ℕ} {p : Program} {f artPass : ℕ} {Tart : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0FeasArtBoth artPass))
    (hart : Meets w p artPass ((stage0FeasArtPassSpec w).withCost fun d _ => Tart d.I.n)) :
    Meets w p f ((stage0FeasArtBothSpec w).withCost fun d _ => 2 * Tart d.I.n + 60) := by
  sep_enter d with hact hL1 hpLab hpDem hcntL hpS hpL
    hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOne hcapW hnW
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
  set orig := feasOrigPos d.I d.hv d.I.m
  have hm_eq : P'.m = orig.length + (feasArtPos d.I d.I.n).length + (feasArtNeg d.I d.I.n).length :=
    feas_m_eq d.I d.hv
  have hm_le : P'.m ≤ 3 * d.I.m := feas_m_le_three_m d.I d.hv d.hiso
  have horig_le : orig.length ≤ 3 * d.I.m := by omega
  have hfl0 : feasArtList d.I 0 d.I.n = feasArtPos d.I d.I.n := rfl
  have hfl1 : feasArtList d.I 1 d.I.n = feasArtNeg d.I d.I.n := rfl
  sep_apply split_zero_prefix pCostSign1 orig.length (3 * d.I.m) horig_le
  sep_apply split_zero_prefix pCostPtr1 orig.length (3 * d.I.m) horig_le
  sep_apply split_zero_prefix pCostLen1 orig.length (3 * d.I.m) horig_le
  sep_apply split_zero_prefix pOneCells orig.length (3 * d.I.m) horig_le
  have hpre0_len : (orig.map fun e => (d.I.edge e).tail).length = orig.length := List.length_map _
  have hcap0_le : (orig.map fun e => (d.I.edge e).tail).length + (feasArtList d.I 0 d.I.n).length ≤ 3 * d.I.m := by
    rw [hpre0_len, hfl0]; omega
  sep_step from (⟨d.I, d.hv, d.hiso, d.act, d.L, 3 * d.I.m, 0,
    orig.map (fun e => (d.I.edge e).tail),
    orig.map (fun e => (d.I.edge e).head),
    orig.map (fun e => d.pShCapBuf + e.val * d.L),
    orig.map (fun e => (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length),
    List.replicate orig.length 0,
    List.replicate orig.length 0,
    List.replicate orig.length 0,
    List.replicate orig.length 0⟩ : Stage0FeasArtPassData)
  have hpre1_len : (orig.map (fun e => (d.I.edge e).tail) ++
      (feasArtList d.I 0 d.I.n).map (fun u => if 0 = 0 then d.I.n else u.val)).length =
      orig.length + (feasArtPos d.I d.I.n).length := by
    simp [hfl0]
  have hlen_p2 : (orig.map (fun e => (d.I.edge e).tail)).length + (feasArtList d.I 0 d.I.n).length =
      (orig.map (fun e => (d.I.edge e).tail) ++
        (feasArtList d.I 0 d.I.n).map (fun u => if 0 = 0 then d.I.n else u.val)).length := by simp
  rw [hlen_p2, hpre0_len]
  have hcap1_le : (orig.map (fun e => (d.I.edge e).tail) ++
      (feasArtList d.I 0 d.I.n).map (fun u => if 0 = 0 then d.I.n else u.val)).length +
      (feasArtList d.I 1 d.I.n).length ≤ 3 * d.I.m := by
    rw [hpre1_len, hfl1]; omega
  sep_step from (⟨d.I, d.hv, d.hiso, d.act, d.L, 3 * d.I.m, 1,
    orig.map (fun e => (d.I.edge e).tail) ++
      (feasArtList d.I 0 d.I.n).map (fun u => if 0 = 0 then d.I.n else u.val),
    orig.map (fun e => (d.I.edge e).head) ++
      (feasArtList d.I 0 d.I.n).map (fun u => if 0 = 0 then u.val else d.I.n),
    orig.map (fun e => d.pShCapBuf + e.val * d.L) ++
      (feasArtList d.I 0 d.I.n).map (fun u => pShDemBuf + (el.table u - 1) * d.L),
    orig.map (fun e => (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
      (feasArtList d.I 0 d.I.n).map (fun u => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I u).natAbs).length),
    List.replicate orig.length 0 ++ List.replicate (feasArtList d.I 0 d.I.n).length 1,
    List.replicate orig.length 0 ++
      List.ofFn (fun t : Fin (feasArtList d.I 0 d.I.n).length => pOneCells + (orig.length + t.val)),
    List.replicate orig.length 0 ++ List.replicate (feasArtList d.I 0 d.I.n).length 1,
    List.replicate orig.length 0 ++ List.replicate (feasArtList d.I 0 d.I.n).length 1⟩ : Stage0FeasArtPassData)
  obtain ⟨hPm, hT_eq, hH_eq, hCP_eq, hCL_eq, hrep_art, _, _, hCoP_eq⟩ :=
    feasBuild_arrays_eq d.I d.hv d.pShCapBuf pShDemBuf d.L pOneCells
  rw [hPm, hT_eq, hH_eq, hCP_eq, hCL_eq, hCoP_eq, hrep_art]
  have hCS_atom : Assn.list pCostSign1
      ((List.replicate orig.length 0 ++ List.replicate (P'.m - orig.length) 1) ++
        List.replicate (3 * d.I.m - P'.m) 0) =
      Assn.list pCostSign1
        ((List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) ++
          List.replicate (3 * d.I.m - P'.m) 0) := by
    rw [feasCostSigns_eq]
  have hCoL_atom : Assn.list pCostLen1
      ((List.replicate orig.length 0 ++ List.replicate (P'.m - orig.length) 1) ++
        List.replicate (3 * d.I.m - P'.m) 0) =
      Assn.list pCostLen1
        ((feasCostLimbs d.I d.hv).map List.length ++
          List.replicate (3 * d.I.m - P'.m) 0) := by
    rw [feasCostLens_eq]
  sep_apply hCS_atom
  sep_apply hCoL_atom
  sep_apply Assn.list_append pTail1 (List.ofFn fun e : Fin P'.m => (P'.tail e).val) _
  sep_apply Assn.list_append pHead1 (List.ofFn fun e : Fin P'.m => (P'.head e).val) _
  sep_apply Assn.list_append pCapPtr1 (feasCapPtrs d.I d.hv d.pShCapBuf pShDemBuf d.L) _
  sep_apply Assn.list_append pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) _
  sep_apply Assn.list_append pCostSign1 (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) _
  sep_apply Assn.list_append pCostPtr1 (feasCostPtrs d.I d.hv pOneCells) _
  sep_apply Assn.list_append pCostLen1 ((feasCostLimbs d.I d.hv).map List.length) _
  sep_apply feas_split_oneCells d.I d.hv d.hiso pOneCells
  sep_step

/-! ### Top-level feasibility builder (`stage0FeasBuild`) -/

wram_def stage0FeasBuild (pass1 artBoth writeHdr : ℕ)
    (pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen, L, k,
     pIn1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1,
     pOrigIdx1, pOneCells) {
  m1Orig := pass1(pEdges, m, pShCapBuf, pShCapLen, L, pTail1, pHead1, pCapPtr1, pCapLen1, pOrigIdx1)
  m1 := artBoth(pLabels, n, pShDemBuf, pShDemSign, pShDemLen, L,
    pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells, m1Orig)
  d := writeHdr(pIn1, n + 1, m1, k, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1)
  return m1Orig
}

structure Stage0FeasBuildData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ

def stage0FeasBuildSpec (w : ℕ) : Spec Stage0FeasBuildData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pIn1 : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOrigIdx1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let cap := 3 * d.I.m
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pIn1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1,
        pCostLen1, pOrigIdx1, pOneCells] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pShCapLen + d.I.m ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      pIn1 + 10 ≤ 2 ^ w ∧
      pTail1 + cap ≤ 2 ^ w ∧ pHead1 + cap ≤ 2 ^ w ∧
      pCapPtr1 + cap ≤ 2 ^ w ∧ pCapLen1 + cap ≤ 2 ^ w ∧
      pCostSign1 + cap ≤ 2 ^ w ∧ pCostPtr1 + cap ≤ 2 ^ w ∧
      pCostLen1 + cap ≤ 2 ^ w ∧ pOrigIdx1 + d.I.m ≤ 2 ^ w ∧ pOneCells + cap ≤ 2 ^ w ∧
      cap < 2 ^ w ∧ d.I.n + 1 < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pIn1 (List.replicate 10 0) *
    Assn.list pTail1 (List.replicate cap 0) *
    Assn.list pHead1 (List.replicate cap 0) *
    Assn.list pCapPtr1 (List.replicate cap 0) *
    Assn.list pCapLen1 (List.replicate cap 0) *
    Assn.list pCostSign1 (List.replicate cap 0) *
    Assn.list pCostPtr1 (List.replicate cap 0) *
    Assn.list pCostLen1 (List.replicate cap 0) *
    Assn.list pOrigIdx1 (List.replicate d.I.m 0) *
    Assn.list pOneCells (List.replicate cap 0)
  post := fun d args res => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pIn1 : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOrigIdx1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [pEdges, pLabels, d.I.n, d.I.m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign,
        pShDemLen, d.L, k, pIn1, pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1,
        pCostLen1, pOrigIdx1, pOneCells] ∧
      res = orig.length⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pIn1 [P'.n, P'.m, k, pTail1, pHead1, pCapPtr1, pCapLen1,
      pCostSign1, pCostPtr1, pCostLen1] *
    Assn.list pTail1 (List.ofFn fun e : Fin P'.m => (P'.tail e).val) *
    Assn.list pHead1 (List.ofFn fun e : Fin P'.m => (P'.head e).val) *
    Assn.list pCapPtr1 (feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L) *
    Assn.list pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) *
    Assn.list pCostSign1 (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) *
    Assn.list pCostPtr1 (feasCostPtrs d.I d.hv pOneCells) *
    Assn.list pCostLen1 ((feasCostLimbs d.I d.hv).map List.length) *
    (∏ j ∈ Finset.range P'.m,
      Assn.list ((feasCostPtrs d.I d.hv pOneCells).getD j 0)
        ((feasCostLimbs d.I d.hv).getD j [])) *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0) *
    Assn.gc

theorem stage0FeasBuild_meets {w : ℕ} {p : Program} {f pass1 artBoth writeHdr : ℕ}
    {Tp1 Tboth : ℕ → ℕ} {Thdr : ℕ}
    (hp : p.procs[f]? = some (stage0FeasBuild pass1 artBoth writeHdr))
    (hp1 : Meets w p pass1 ((stage0FeasPass1Spec w).withCost fun d _ => Tp1 d.I.m))
    (hboth : Meets w p artBoth ((stage0FeasArtBothSpec w).withCost fun d _ => Tboth d.I.n))
    (hhdr : Meets w p writeHdr ((writeStage1HdrSpec w).withCost fun _ _ => Thdr)) :
    Meets w p f ((stage0FeasBuildSpec w).withCost fun d _ =>
      Tp1 d.I.m + Tboth d.I.n + Thdr + 100) := by
  sep_enter d with hact hL1 hpE h11m hpLab hpCap hmL hpLen hpDem hcntL hpS hpL
    hpIn hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOI hpOne hcapW hn1W
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set P' := (FlowReduction.buildFeasibilityInstance d.I d.hv).withoutZeroEdges
  set orig := feasOrigPos d.I d.hv d.I.m
  generalize hF1 :
    (Assn.list pLabels (List.ofFn el.table) *
     Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
       if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
     Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
       (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
     Assn.list pIn1 (List.replicate 10 0) *
     Assn.list pCostSign1 (List.replicate (3 * d.I.m) 0) *
     Assn.list pCostPtr1 (List.replicate (3 * d.I.m) 0) *
     Assn.list pCostLen1 (List.replicate (3 * d.I.m) 0) *
     Assn.list pOneCells (List.replicate (3 * d.I.m) 0)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.L, 3 * d.I.m⟩ : Stage0FeasPass1Data)
  generalize hF2 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
       (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
     Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0)) = F2
  sep_apply hF2
  subst F1; sep_norm
  sep_step from (⟨d.I, d.hv, d.hiso, d.act, d.L, pShCapBuf⟩ : Stage0FeasArtBothData)
  generalize hF3 :
    (Assn.list pLabels (List.ofFn el.table) *
     Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
       if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
     Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
       (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
     Assn.list pTail1 (List.ofFn fun e : Fin P'.m => (P'.tail e).val) *
     Assn.list pHead1 (List.ofFn fun e : Fin P'.m => (P'.head e).val) *
     Assn.list pCapPtr1 (feasCapPtrs d.I d.hv pShCapBuf pShDemBuf d.L) *
     Assn.list pCapLen1 ((feasCapLimbs d.I d.hv).map List.length) *
     Assn.list pCostSign1 (List.ofFn fun e : Fin P'.m => if P'.cost e < 0 then 1 else 0) *
     Assn.list pCostPtr1 (feasCostPtrs d.I d.hv pOneCells) *
     Assn.list pCostLen1 ((feasCostLimbs d.I d.hv).map List.length) *
     (∏ j ∈ Finset.range P'.m,
       Assn.list ((feasCostPtrs d.I d.hv pOneCells).getD j 0)
         ((feasCostLimbs d.I d.hv).getD j []))) = F3
  sep_apply hF3
  sep_step from (⟨d.I.n + 1, P'.m, k, pTail1, pHead1, pCapPtr1, pCapLen1,
    pCostSign1, pCostPtr1, pCostLen1, List.replicate 10 0⟩ : WriteStage1HdrData)
  subst F3 F2; sep_norm
  sep_step

end MinCostFlow.NarrowProg
