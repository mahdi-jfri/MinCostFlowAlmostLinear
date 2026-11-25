module

public import MinCostFlow.NarrowProg.Stage0ShiftCaps
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 3: lazy demand accumulation over active vertices and edges

Implements `stage0ShiftDemInit` and `stage0ShiftDemEdges` using two lazy base-`2 ^ k`
accumulators per active vertex (`0` space and `0` work per isolated vertex).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

wram_def stage0ShiftDemInit (accAdd : ℕ) (pDems, pActive, cnt, pDemPos, pDemNeg, L) {
  rowOff := 0
  for i in 0 .. cnt {
    v := mem[pActive + i]
    dOff := v * 3
    dSign := mem[pDems + dOff]
    dLen := mem[pDems + dOff + 1]
    dPtr := mem[pDems + dOff + 2]
    if dSign == 0 {
      d := accAdd(pDemPos + rowOff, dPtr, dLen)
    } else {
      d := accAdd(pDemNeg + rowOff, dPtr, dLen)
    }
    rowOff := rowOff + L
  }
  return 0
}

structure Stage0ShiftDemInitData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  actTail : List ℕ
  L : ℕ

def stage0ShiftDemInitSpec (w : ℕ) : Spec Stage0ShiftDemInitData where
  pre := fun d args => ⨆ (pDems : ℕ) (pActive : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pDems, pActive, el.count, pDemPos, pDemNeg, d.L] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k ≤ w ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pDems + 3 * d.I.n ≤ 2 ^ w ∧ 3 * d.I.n < 2 ^ w ∧
      pDemPos + el.count * d.L ≤ 2 ^ w ∧ pDemNeg + el.count * d.L ≤ 2 ^ w ∧
      el.count * d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if h : v < d.I.n then demRec d.I ⟨v, h⟩ else [])) *
    Assn.list pActive (d.act ++ d.actTail) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (List.replicate d.L 0)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (List.replicate d.L 0))
  post := fun d args v => ⨆ (pDems : ℕ) (pActive : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    ⌜args = [pDems, pActive, el.count, pDemPos, pDemNeg, d.L] ∧ v = 0⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if h : v < d.I.n then demRec d.I ⟨v, h⟩ else [])) *
    Assn.list pActive (d.act ++ d.actTail) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L 0 c)) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L 0 c))

theorem stage0ShiftDemInit_meets {w : ℕ} {p : Program} {f accAdd : ℕ} {Tacc : ℕ → ℕ}
    (hmono : ∀ a b, a ≤ b → Tacc a ≤ Tacc b)
    (hp : p.procs[f]? = some (stage0ShiftDemInit accAdd))
    (hacc : Meets w p accAdd ((accAddLimbsSpec w).withCost fun x _ => Tacc x.2.length)) :
    Meets w p f ((stage0ShiftDemInitSpec w).withCost fun d _ =>
      (Tacc d.L + 115) * (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count + 40) := by
  sep_enter d with hact hL1 h2k hdemLt hpD h3n hpPos hpNeg hcntL
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have hk1 : 1 ≤ narrowLimbWidth d.I := one_le_narrowLimbWidth d.I
  have h2kw : 2 ^ narrowLimbWidth d.I < 2 ^ w :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  sep_step
  have hinitP : (∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (List.replicate d.L 0)) =
      ∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L 0 c) := by
    apply Finset.prod_congr rfl; intro c _; simp [initPosRow]
  have hinitN : (∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (List.replicate d.L 0)) =
      ∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L 0 c) := by
    apply Finset.prod_congr rfl; intro c _; simp [initNegRow]
  sep_apply hinitP; sep_apply hinitN
  sep_for (fun i (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
      ⟨[pDems, pActive, el.count, pDemPos, pDemNeg, d.L, i * d.L, i,
        t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2],
      i ≤ el.count, (Tacc d.L + 95) * (el.count - i) + 15,
      [Assn.list 0 (narrowEncode d.I),
       ∏ v ∈ Finset.range d.I.n,
         Assn.list (pDems + v * 3) (if h : v < d.I.n then demRec d.I ⟨v, h⟩ else []),
       Assn.list pActive (d.act ++ d.actTail),
       ∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c),
       ∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c)]⟩)
    with ⟨v0, dOff0, dSign0, dLen0, dPtr0, d0⟩
  · have hi_act : i < d.act.length := by rw [hact.1]; exact hhi
    have hv_lt : d.act[i]'hi_act < d.I.n := (hact.2 i hi_act).1
    have hact_get : (d.act ++ d.actTail)[i]'(by simp; omega) = d.act[i]'hi_act :=
      List.getElem_append_left hi_act
    sep_step; sep_step
    rw [hact_get] at hv
    subst v
    let vf : Fin d.I.n := ⟨d.act[i]'hi_act, hv_lt⟩
    have hmemV : vf.val ∈ Finset.range d.I.n := Finset.mem_range.mpr vf.isLt
    sep_apply Assn.prod_eq_mul_erase hmemV
      (fun u => Assn.list (pDems + u * 3) (if h : u < d.I.n then demRec d.I ⟨u, h⟩ else []))
    have hcurD : Assn.list (pDems + vf.val * 3) (if h : vf.val < d.I.n then demRec d.I ⟨vf.val, h⟩ else []) =
        Assn.list (pDems + vf.val * 3) (demRec d.I vf) := by simp [vf, hv_lt]
    sep_apply hcurD
    have hdemRec_len : (demRec d.I vf).length = 3 := rfl
    sep_step; sep_step; sep_step
    simp only [demRec, List.getElem_cons_zero, List.getElem_cons_succ] at hdSign hdLen hdPtr
    subst dSign dLen dPtr
    sep_apply hcurD.symm
    sep_apply (Assn.prod_eq_mul_erase hmemV
      (fun u => Assn.list (pDems + u * 3) (if h : u < d.I.n then demRec d.I ⟨u, h⟩ else []))).symm
    have hmemC : i ∈ Finset.range el.count := Finset.mem_range.mpr hhi
    have hdigLt : (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length < d.L := hdemLt i hi_act
    have hdigLimbs : Limbs (narrowLimbWidth d.I) (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs) :=
      digits_limbs hk1 _
    have hcost_le : Tacc (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length ≤ Tacc d.L :=
      hmono _ _ (by omega)
    have hnext_mul : i * d.L + d.L = (i + 1) * d.L := by ring
    have hnext_lt : (i + 1) * d.L ≤ el.count * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step
    · -- dSign = 0 => I.d vf ≥ 0
      have hnn : ¬ (d.I.d vf < 0) := by split_ifs at hcond with h; omega
      sep_apply Assn.prod_eq_mul_erase hmemC
        (fun c => Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c))
      have hcurP : Assn.list (pDemPos + i * d.L) (initPosRow d.I d.act d.L i i) =
          Assn.list (pDemPos + i * d.L) (List.replicate d.L 0) := by simp [initPosRow]
      sep_apply hcurP
      sep_apply list_narrowEncode_split d.I d.hv
      sep_apply Assn.prod_eq_mul_erase hmemV
        (fun u => Assn.list (demStartPos d.I u)
          (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else []))
      have hcurW : Assn.list (demStartPos d.I vf.val)
          (if h : vf.val < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d vf.val) else []) =
          Assn.list (demStartPos d.I vf.val) (intWords (narrowLimbWidth d.I) (d.I.d vf)) := by
        simp [vf, hv_lt]
      sep_apply hcurW
      sep_apply list_intWords (demStartPos d.I vf.val) (narrowLimbWidth d.I) (d.I.d vf)
      have hdemAtom :
          Assn.list (demStartPos d.I vf.val + 2)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs) =
          Assn.list (demPtr d.I vf)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs) := rfl
      sep_apply hdemAtom
      generalize hF :
        ((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
         (∏ j ∈ Finset.range d.I.m,
           Assn.list (edgeStartPos d.I j)
             (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
         (demStartPos d.I vf.val ↦ if d.I.d vf < 0 then 1 else 0) *
         (demStartPos d.I vf.val + 1 ↦
           (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length) *
         (∏ u ∈ (Finset.range d.I.n).erase vf.val,
           Assn.list (demStartPos d.I u)
             (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else [])) *
         (∏ u ∈ Finset.range d.I.n,
           Assn.list (pDems + u * 3) (if h : u < d.I.n then demRec d.I ⟨u, h⟩ else [])) *
         Assn.list pActive (d.act ++ d.actTail) *
         (∏ c ∈ (Finset.range el.count).erase i,
           Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c)) *
         (∏ c ∈ Finset.range el.count,
           Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c))) = F
      have hdigLt' : (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length < d.L := hdigLt
      have hside : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length,
          (List.replicate d.L 0).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega),
          List.getD_eq_getElem _ _ hj, List.getElem_replicate]
        have hlj := hdigLimbs _ (List.getElem_mem hj); omega
      sep_apply hF
      sep_step from (List.replicate d.L 0, Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs)
      subst F; sep_norm
      sep_apply hdemAtom.symm
      sep_apply (list_intWords (demStartPos d.I vf.val) (narrowLimbWidth d.I) (d.I.d vf)).symm
      sep_apply hcurW.symm
      sep_apply (Assn.prod_eq_mul_erase hmemV
        (fun u => Assn.list (demStartPos d.I u)
          (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else []))).symm
      sep_apply (list_narrowEncode_split d.I d.hv).symm
      have hPnext :
          Assn.list (pDemPos + i * d.L) (accAddList (List.replicate d.L 0)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs)) *
          (∏ c ∈ (Finset.range el.count).erase i,
            Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L (i + 1) c) := by
        rw [accAddList_replicate_zero (by omega), Assn.prod_eq_mul_erase hmemC]
        congr 1
        · simp [initPosRow, hi_act, vf, hnn]
        · apply Finset.prod_congr rfl; intro c hc
          have hne : c ≠ i := Finset.ne_of_mem_erase hc
          have hiff : (c < i + 1) ↔ (c < i) := by omega
          simp [initPosRow, hiff]
      have hNnext :
          (∏ c ∈ Finset.range el.count,
            Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _
        by_cases hci : c = i
        · subst hci; simp [initNegRow, hi_act, vf, hnn]
        · have hiff : (c < i + 1) ↔ (c < i) := by omega
          simp [initNegRow, hiff]
      sep_apply hPnext; sep_apply hNnext
      sep_step
    · -- dSign = 1 => I.d vf < 0
      have hneg : d.I.d vf < 0 := by split_ifs at hcond with h <;> omega
      sep_apply Assn.prod_eq_mul_erase hmemC
        (fun c => Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c))
      have hcurN : Assn.list (pDemNeg + i * d.L) (initNegRow d.I d.act d.L i i) =
          Assn.list (pDemNeg + i * d.L) (List.replicate d.L 0) := by simp [initNegRow]
      sep_apply hcurN
      sep_apply list_narrowEncode_split d.I d.hv
      sep_apply Assn.prod_eq_mul_erase hmemV
        (fun u => Assn.list (demStartPos d.I u)
          (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else []))
      have hcurW : Assn.list (demStartPos d.I vf.val)
          (if h : vf.val < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d vf.val) else []) =
          Assn.list (demStartPos d.I vf.val) (intWords (narrowLimbWidth d.I) (d.I.d vf)) := by
        simp [vf, hv_lt]
      sep_apply hcurW
      sep_apply list_intWords (demStartPos d.I vf.val) (narrowLimbWidth d.I) (d.I.d vf)
      have hdemAtom :
          Assn.list (demStartPos d.I vf.val + 2)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs) =
          Assn.list (demPtr d.I vf)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs) := rfl
      sep_apply hdemAtom
      generalize hF :
        ((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
         (∏ j ∈ Finset.range d.I.m,
           Assn.list (edgeStartPos d.I j)
             (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
         (demStartPos d.I vf.val ↦ if d.I.d vf < 0 then 1 else 0) *
         (demStartPos d.I vf.val + 1 ↦
           (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length) *
         (∏ u ∈ (Finset.range d.I.n).erase vf.val,
           Assn.list (demStartPos d.I u)
             (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else [])) *
         (∏ u ∈ Finset.range d.I.n,
           Assn.list (pDems + u * 3) (if h : u < d.I.n then demRec d.I ⟨u, h⟩ else [])) *
         Assn.list pActive (d.act ++ d.actTail) *
         (∏ c ∈ Finset.range el.count,
           Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c)) *
         (∏ c ∈ (Finset.range el.count).erase i,
           Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c))) = F
      have hdigLt' : (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length < d.L := hdigLt
      have hside : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).length,
          (List.replicate d.L 0).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega),
          List.getD_eq_getElem _ _ hj, List.getElem_replicate]
        have hlj := hdigLimbs _ (List.getElem_mem hj); omega
      sep_apply hF
      sep_step from (List.replicate d.L 0, Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs)
      subst F; sep_norm
      sep_apply hdemAtom.symm
      sep_apply (list_intWords (demStartPos d.I vf.val) (narrowLimbWidth d.I) (d.I.d vf)).symm
      sep_apply hcurW.symm
      sep_apply (Assn.prod_eq_mul_erase hmemV
        (fun u => Assn.list (demStartPos d.I u)
          (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else []))).symm
      sep_apply (list_narrowEncode_split d.I d.hv).symm
      have hNnext :
          Assn.list (pDemNeg + i * d.L) (accAddList (List.replicate d.L 0)
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.d vf).natAbs)) *
          (∏ c ∈ (Finset.range el.count).erase i,
            Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L i c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L (i + 1) c) := by
        rw [accAddList_replicate_zero (by omega), Assn.prod_eq_mul_erase hmemC]
        congr 1
        · simp [initNegRow, hi_act, vf, hneg]
        · apply Finset.prod_congr rfl; intro c hc
          have hne : c ≠ i := Finset.ne_of_mem_erase hc
          have hiff : (c < i + 1) ↔ (c < i) := by omega
          simp [initNegRow, hiff]
      have hPnext :
          (∏ c ∈ Finset.range el.count,
            Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L i c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _
        by_cases hci : c = i
        · subst hci; simp [initPosRow, hi_act, vf, hneg]
        · have hiff : (c < i + 1) ↔ (c < i) := by omega
          simp [initPosRow, hiff]
      sep_apply hPnext; sep_apply hNnext
      sep_step
  · have hP0 : (∏ c ∈ Finset.range el.count,
        Assn.list (pDemPos + c * d.L) (initPosRow d.I d.act d.L el.count c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L 0 c) := by
      simp [edgePosRow, hact.1]
    have hN0 : (∏ c ∈ Finset.range el.count,
        Assn.list (pDemNeg + c * d.L) (initNegRow d.I d.act d.L el.count c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L 0 c) := by
      simp [edgeNegRow, hact.1]
    sep_apply hP0; sep_apply hN0
    sep_step

/-! ### `stage0ShiftDemEdges`: accumulate `± |lower e|` into lazy demand accumulators -/

wram_def stage0ShiftDemEdges (accAdd : ℕ) (pEdges, m, pLabels, pDemPos, pDemNeg, L) {
  off := 0
  for i in 0 .. m {
    u := mem[pEdges + off]
    v := mem[pEdges + off + 1]
    loSign := mem[pEdges + off + 2]
    loLen := mem[pEdges + off + 3]
    loPtr := mem[pEdges + off + 4]
    lu := mem[pLabels + u] - 1
    lv := mem[pLabels + v] - 1
    if loSign == 0 {
      d := accAdd(pDemPos + lv * L, loPtr, loLen)
      d := accAdd(pDemNeg + lu * L, loPtr, loLen)
    } else {
      d := accAdd(pDemPos + lu * L, loPtr, loLen)
      d := accAdd(pDemNeg + lv * L, loPtr, loLen)
    }
    off := off + 11
  }
  return 0
}

structure Stage0ShiftDemEdgesData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  L : ℕ

def stage0ShiftDemEdgesSpec (w : ℕ) : Spec Stage0ShiftDemEdgesData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, d.I.m, pLabels, pDemPos, pDemNeg, d.L] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pDemPos + el.count * d.L ≤ 2 ^ w ∧ pDemNeg + el.count * d.L ≤ 2 ^ w ∧
      el.count * d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L 0 c)) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L 0 c))
  post := fun d args v => ⨆ (pEdges : ℕ) (pLabels : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    ⌜args = [pEdges, d.I.m, pLabels, pDemPos, pDemNeg, d.L] ∧ v = 0⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L d.I.m c)) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L d.I.m c))

theorem stage0ShiftDemEdges_meets {w : ℕ} {p : Program} {f accAdd : ℕ} {Tacc : ℕ → ℕ}
    (hmono : ∀ a b, a ≤ b → Tacc a ≤ Tacc b)
    (hp : p.procs[f]? = some (stage0ShiftDemEdges accAdd))
    (hacc : Meets w p accAdd ((accAddLimbsSpec w).withCost fun x _ => Tacc x.2.length)) :
    Meets w p f ((stage0ShiftDemEdgesSpec w).withCost fun d _ =>
      (2 * Tacc d.L + 145) * d.I.m + 40) := by
  sep_enter d with hact hL1 h2k1 hedgeLt hdemLt hpE h11m hpPos hpNeg hcntL
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have hk1 : 1 ≤ narrowLimbWidth d.I := one_le_narrowLimbWidth d.I
  have hm1_lt : d.I.m + 1 < 2 ^ narrowLimbWidth d.I := m_add_one_lt_pow_limbWidth d.I d.hv
  have h2k_le : (2 ^ narrowLimbWidth d.I) * (2 ^ narrowLimbWidth d.I) ≤ 2 ^ (w - 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hhalf_lt : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hprops := edgeRow_props d.I d.hv hact hL1 hedgeLt hdemLt
  sep_step
  sep_for (fun i (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
      ⟨[pEdges, d.I.m, pLabels, pDemPos, pDemNeg, d.L, i * 11, i,
        t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2],
      i ≤ d.I.m, (2 * Tacc d.L + 125) * (d.I.m - i) + 15,
      [Assn.list 0 (narrowEncode d.I),
       ∏ j ∈ Finset.range d.I.m,
         Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []),
       Assn.list pLabels (List.ofFn el.table),
       ∏ c ∈ Finset.range el.count,
         Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L i c),
       ∏ c ∈ Finset.range el.count,
         Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L i c)]⟩)
    with ⟨u0, v0, loS0, loL0, loP0, lu0, lv0, d0⟩
  · let e : Fin d.I.m := ⟨i, hhi⟩
    have hmem : i ∈ Finset.range d.I.m := Finset.mem_range.mpr hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))
    have hcurE : Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec d.I e) := by simp [e, hhi]
    sep_apply hcurE
    have hedgeRec_len : (edgeRec d.I e).length = 11 := rfl
    sep_step; sep_step; sep_step; sep_step; sep_step
    simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ] at hu hv hloSign hloLen hloPtr
    subst u v loSign loLen loPtr
    sep_apply hcurE.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else []))).symm
    have htu : (d.I.edge e).tail < d.I.n := (d.hv.1 _ (List.getElem_mem e.isLt)).1
    have hhv : (d.I.edge e).head < d.I.n := (d.hv.1 _ (List.getElem_mem e.isLt)).2
    have hlu_pos : 0 < el.table ((FlowReduction.shiftedGraph d.I d.hv).tail e) :=
      Circulation.tail_label_pos (FlowReduction.shiftedGraph d.I d.hv) e
    have hlv_pos : 0 < el.table ((FlowReduction.shiftedGraph d.I d.hv).head e) :=
      Circulation.head_label_pos (FlowReduction.shiftedGraph d.I d.hv) e
    have hlu_le : el.table ((FlowReduction.shiftedGraph d.I d.hv).tail e) ≤ el.count :=
      (Circulation.endpointLabels_valid (FlowReduction.shiftedGraph d.I d.hv)).1 _
    have hlv_le : el.table ((FlowReduction.shiftedGraph d.I d.hv).head e) ≤ el.count :=
      (Circulation.endpointLabels_valid (FlowReduction.shiftedGraph d.I d.hv)).1 _
    have htab_len : (List.ofFn el.table).length = d.I.n := List.length_ofFn
    sep_step; sep_step
    simp only [List.getElem_ofFn] at hlu hlv
    subst lu lv
    set lt := el.table ((FlowReduction.shiftedGraph d.I d.hv).tail e) - 1
    set lh := el.table ((FlowReduction.shiftedGraph d.I d.hv).head e) - 1
    have hlt_cnt : lt < el.count := by omega
    have hlh_cnt : lh < el.count := by omega
    have hlt_mul : lt * d.L < el.count * d.L := Nat.mul_lt_mul_of_pos_right hlt_cnt (by omega)
    have hlh_mul : lh * d.L < el.count * d.L := Nat.mul_lt_mul_of_pos_right hlh_cnt (by omega)
    have hloLen := hedgeLt e
    have hloLimbs : Limbs (narrowLimbWidth d.I) (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs) :=
      digits_limbs hk1 _
    have hcost_le : Tacc (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length ≤ Tacc d.L :=
      hmono _ _ (by omega)
    have hsum_fit : ∀ (xs : List ℕ) (x : ℕ),
        (∀ y ∈ xs, y ≤ (i + 1) * (2 ^ narrowLimbWidth d.I - 1)) →
        x < 2 ^ narrowLimbWidth d.I →
        ∀ y ∈ xs, y + x < 2 ^ w := by
      intro xs x hxs hx y hy
      have hyb := hxs y hy
      have hle1 : (i + 1) * (2 ^ narrowLimbWidth d.I - 1) ≤ (i + 1) * 2 ^ narrowLimbWidth d.I :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hmul : (i + 2) * 2 ^ narrowLimbWidth d.I =
          (i + 1) * 2 ^ narrowLimbWidth d.I + 2 ^ narrowLimbWidth d.I := by ring
      have h1 : y + x < (i + 2) * 2 ^ narrowLimbWidth d.I := by omega
      have h2 : (i + 2) * 2 ^ narrowLimbWidth d.I ≤ (d.I.m + 1) * 2 ^ narrowLimbWidth d.I :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (d.I.m + 1) * 2 ^ narrowLimbWidth d.I < 2 ^ narrowLimbWidth d.I * 2 ^ narrowLimbWidth d.I :=
        Nat.mul_lt_mul_of_pos_right hm1_lt (Nat.two_pow_pos _)
      omega
    -- Split narrowEncode I once to expose edgeLoPtr d.I e
    sep_apply list_narrowEncode_split d.I d.hv
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos d.I j)
        (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else []))
    have hcurW : Assn.list (edgeStartPos d.I i)
        (if h : i < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨i, h⟩) else []) =
        Assn.list (edgeStartPos d.I i) (narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge e)) := by
      simp [e, hhi]
    sep_apply hcurW
    sep_apply list_narrowEdgeWords d.I e
    sep_apply list_intWords (edgeStartPos d.I e.val + 2) (narrowLimbWidth d.I) (d.I.edge e).lower
    have hloAtom :
        Assn.list (edgeStartPos d.I e.val + 2 + 2)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs) =
        Assn.list (edgeLoPtr d.I e)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs) := rfl
    sep_apply hloAtom
    sep_step
    · -- loSign = 0 => lower ≥ 0: pos[lh] += lo, neg[lt] += lo
      have hnn : ¬ ((d.I.edge e).lower < 0) := by split_ifs at hcond with h; omega
      obtain ⟨hplhL, _, hplhB, _, _, _, _⟩ := hprops i (by omega) lh
      obtain ⟨_, hnltL, _, hnltB, _, _, _⟩ := hprops i (by omega) lt
      sep_apply Assn.prod_eq_mul_erase (Finset.mem_range.mpr hlh_cnt)
        (fun c => Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L i c))
      sep_apply Assn.prod_eq_mul_erase (Finset.mem_range.mpr hlt_cnt)
        (fun c => Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L i c))
      generalize hF1 :
        ((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
         (edgeStartPos d.I e.val ↦ (d.I.edge e).tail) *
         (edgeStartPos d.I e.val + 1 ↦ (d.I.edge e).head) *
         (edgeStartPos d.I e.val + 2 ↦ if (d.I.edge e).lower < 0 then 1 else 0) *
         (edgeStartPos d.I e.val + 2 + 1 ↦
           (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length) *
         Assn.list (edgeHiPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).upper) *
         Assn.list (edgeCostPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).cost) *
         (∏ j ∈ (Finset.range d.I.m).erase i,
           Assn.list (edgeStartPos d.I j)
             (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
         (∏ u ∈ Finset.range d.I.n,
           Assn.list (demStartPos d.I u)
             (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else [])) *
         (∏ j ∈ Finset.range d.I.m,
           Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else [])) *
         Assn.list pLabels (List.ofFn el.table) *
         (∏ c ∈ (Finset.range el.count).erase lh,
           Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L i c)) *
         (∏ c ∈ (Finset.range el.count).erase lt,
           Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L i c))) = F1
      have hside1 : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length,
          (edgePosRow d.I d.hv d.act d.L i lh).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
        exact hsum_fit _ _ hplhB (hloLimbs _ (List.getElem_mem hj)) _ (List.getElem_mem (by omega))
      have hside2 : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length,
          (edgeNegRow d.I d.hv d.act d.L i lt).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
        exact hsum_fit _ _ hnltB (hloLimbs _ (List.getElem_mem hj)) _ (List.getElem_mem (by omega))
      sep_apply hF1
      sep_step
      sep_step from (edgePosRow d.I d.hv d.act d.L i lh,
          Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)
      sep_step from (edgeNegRow d.I d.hv d.act d.L i lt,
          Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)
      subst F1; sep_norm
      sep_apply hloAtom.symm
      sep_apply (list_intWords (edgeStartPos d.I e.val + 2) (narrowLimbWidth d.I) (d.I.edge e).lower).symm
      sep_apply (list_narrowEdgeWords d.I e).symm
      sep_apply hcurW.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (edgeStartPos d.I j)
          (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else []))).symm
      sep_apply (list_narrowEncode_split d.I d.hv).symm
      sep_apply (prod_func_update hlh_cnt pDemPos d.L (edgePosRow d.I d.hv d.act d.L i)
        (accAddList (edgePosRow d.I d.hv d.act d.L i lh)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs))).symm
      sep_apply (prod_func_update hlt_cnt pDemNeg d.L (edgeNegRow d.I d.hv d.act d.L i)
        (accAddList (edgeNegRow d.I d.hv d.act d.L i lt)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs))).symm
      have hPn : (∏ c ∈ Finset.range el.count,
          Assn.list (pDemPos + c * d.L) (Function.update (edgePosRow d.I d.hv d.act d.L i) lh
            (accAddList (edgePosRow d.I d.hv d.act d.L i lh)
              (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)) c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _; simp [edgePosRow, hhi, hnn, lh, e, el]
      have hNn : (∏ c ∈ Finset.range el.count,
          Assn.list (pDemNeg + c * d.L) (Function.update (edgeNegRow d.I d.hv d.act d.L i) lt
            (accAddList (edgeNegRow d.I d.hv d.act d.L i lt)
              (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)) c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _; simp [edgeNegRow, hhi, hnn, lt, e, el]
      sep_apply hPn; sep_apply hNn
      sep_step
    · -- loSign = 1 => lower < 0: pos[lt] += lo, neg[lh] += lo
      have hneg : (d.I.edge e).lower < 0 := by split_ifs at hcond with h <;> omega
      obtain ⟨hpltL, _, hpltB, _, _, _, _⟩ := hprops i (by omega) lt
      obtain ⟨_, hnlhL, _, hnlhB, _, _, _⟩ := hprops i (by omega) lh
      sep_apply Assn.prod_eq_mul_erase (Finset.mem_range.mpr hlt_cnt)
        (fun c => Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L i c))
      sep_apply Assn.prod_eq_mul_erase (Finset.mem_range.mpr hlh_cnt)
        (fun c => Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L i c))
      generalize hF1 :
        ((0 ↦ narrowLimbWidth d.I) * (1 ↦ d.I.n) * (2 ↦ d.I.m) *
         (edgeStartPos d.I e.val ↦ (d.I.edge e).tail) *
         (edgeStartPos d.I e.val + 1 ↦ (d.I.edge e).head) *
         (edgeStartPos d.I e.val + 2 ↦ if (d.I.edge e).lower < 0 then 1 else 0) *
         (edgeStartPos d.I e.val + 2 + 1 ↦
           (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length) *
         Assn.list (edgeHiPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).upper) *
         Assn.list (edgeCostPos d.I e) (intWords (narrowLimbWidth d.I) (d.I.edge e).cost) *
         (∏ j ∈ (Finset.range d.I.m).erase i,
           Assn.list (edgeStartPos d.I j)
             (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else [])) *
         (∏ u ∈ Finset.range d.I.n,
           Assn.list (demStartPos d.I u)
             (if h : u < d.I.n then intWords (narrowLimbWidth d.I) (d.I.d u) else [])) *
         (∏ j ∈ Finset.range d.I.m,
           Assn.list (pEdges + j * 11) (if h : j < d.I.m then edgeRec d.I ⟨j, h⟩ else [])) *
         Assn.list pLabels (List.ofFn el.table) *
         (∏ c ∈ (Finset.range el.count).erase lt,
           Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L i c)) *
         (∏ c ∈ (Finset.range el.count).erase lh,
           Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L i c))) = F1
      have hside1 : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length,
          (edgePosRow d.I d.hv d.act d.L i lt).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
        exact hsum_fit _ _ hpltB (hloLimbs _ (List.getElem_mem hj)) _ (List.getElem_mem (by omega))
      have hside2 : ∀ j < (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length,
          (edgeNegRow d.I d.hv d.act d.L i lh).getD j 0 +
            (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).getD j 0 < 2 ^ w := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
        exact hsum_fit _ _ hnlhB (hloLimbs _ (List.getElem_mem hj)) _ (List.getElem_mem (by omega))
      sep_apply hF1
      sep_step
      sep_step from (edgePosRow d.I d.hv d.act d.L i lt,
          Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)
      sep_step from (edgeNegRow d.I d.hv d.act d.L i lh,
          Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)
      subst F1; sep_norm
      sep_apply hloAtom.symm
      sep_apply (list_intWords (edgeStartPos d.I e.val + 2) (narrowLimbWidth d.I) (d.I.edge e).lower).symm
      sep_apply (list_narrowEdgeWords d.I e).symm
      sep_apply hcurW.symm
      sep_apply (Assn.prod_eq_mul_erase hmem
        (fun j => Assn.list (edgeStartPos d.I j)
          (if h : j < d.I.m then narrowEdgeWords (narrowLimbWidth d.I) (d.I.edge ⟨j, h⟩) else []))).symm
      sep_apply (list_narrowEncode_split d.I d.hv).symm
      sep_apply (prod_func_update hlt_cnt pDemPos d.L (edgePosRow d.I d.hv d.act d.L i)
        (accAddList (edgePosRow d.I d.hv d.act d.L i lt)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs))).symm
      sep_apply (prod_func_update hlh_cnt pDemNeg d.L (edgeNegRow d.I d.hv d.act d.L i)
        (accAddList (edgeNegRow d.I d.hv d.act d.L i lh)
          (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs))).symm
      have hPn : (∏ c ∈ Finset.range el.count,
          Assn.list (pDemPos + c * d.L) (Function.update (edgePosRow d.I d.hv d.act d.L i) lt
            (accAddList (edgePosRow d.I d.hv d.act d.L i lt)
              (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)) c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _; simp [edgePosRow, hhi, hneg, lt, e, el]
      have hNn : (∏ c ∈ Finset.range el.count,
          Assn.list (pDemNeg + c * d.L) (Function.update (edgeNegRow d.I d.hv d.act d.L i) lh
            (accAddList (edgeNegRow d.I d.hv d.act d.L i lh)
              (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs)) c)) =
          ∏ c ∈ Finset.range el.count,
            Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L (i + 1) c) := by
        apply Finset.prod_congr rfl; intro c _; simp [edgeNegRow, hhi, hneg, lh, e, el]
      sep_apply hPn; sep_apply hNn
      sep_step
  · sep_step

/-! ### `stage0ShiftDemFin`: normalize active accumulators and emit canonical shifted demands -/

end MinCostFlow.NarrowProg
