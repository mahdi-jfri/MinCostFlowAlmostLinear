module

public import MinCostFlow.NarrowProg.Stage0ShiftDemAcc
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 3: shifted capacities and shifted demands on active vertices

Combines `stage0ShiftCaps`, `stage0ShiftDemInit`, `stage0ShiftDemEdges`, and `stage0ShiftDemFin`
into `stage0Shift` (and polymorphic module `stage0ShiftMod`), computing:
- `pShCapBuf` (`m * L_dem` limbs) and `pShCapLen` (`m` canonical limb lengths) for
  `(shiftedGraph I hv).capacity e = ((I.edge e).upper - (I.edge e).lower).toNat`;
- `pShDemBuf` (`cnt * L_dem` limbs), `pShDemSign` (`cnt`), `pShDemLen` (`cnt`) for
  `shiftedDemand I (act[c])` ONLY on the `cnt ≤ 2 * m` active vertices (`0` space and `0` work per
  isolated vertex).

Total space: `stage0ShiftSpace m cnt L_dem = m * L_dem + m + 3 * cnt * L_dem + 2 * cnt + 2 * L_dem`
(`≤ 7 * m * L_dem + 5 * m + 2 * L_dem`). Total time: `O(m * (narrowMaxCapLimbs I + 1) + 1)`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### Shifted demand indexed by active slot -/

/-- Shifted demand of the `c`-th active vertex (`0` if out of bounds). -/
def activeShiftedDemand (I : Instance) (act : List ℕ) (c : ℕ) : ℤ :=
  if h : c < act.length then
    if hv : act[c]'h < I.n then FlowReduction.shiftedDemand I ⟨act[c]'h, hv⟩ else 0
  else 0

theorem activeShiftedDemand_eq {I : Instance} {hv : I.IsValid} {act : List ℕ}
    (hact : ActiveInv (FlowReduction.shiftedGraph I hv).endpointLabels act)
    {c : ℕ} (hc : c < act.length) :
    activeShiftedDemand I act c = FlowReduction.shiftedDemand I ⟨act[c]'hc, (hact.2 c hc).1⟩ := by
  unfold activeShiftedDemand
  simp [hc, (hact.2 c hc).1]

/-! ### `stage0ShiftDemFin`: normalize active accumulators and emit canonical shifted demands -/

wram_def stage0ShiftDemFin (shiftOneDem : ℕ)
    (cnt, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, L, k) {
  rowOff := 0
  for i in 0 .. cnt {
    len := shiftOneDem(pDemPos + rowOff, pDemNeg + rowOff, pShDemBuf + rowOff,
      pShDemSign + i, L, k)
    mem[pShDemLen + i] := len
    rowOff := rowOff + L
  }
  return 0
}

structure Stage0ShiftDemFinData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  L : ℕ
  signBuf : List ℕ
  lenBuf : List ℕ

def stage0ShiftDemFinSpec (w : ℕ) : Spec Stage0ShiftDemFinData where
  pre := fun d args => ⨆ (pDemPos : ℕ) (pDemNeg : ℕ) (pShDemBuf : ℕ)
      (pShDemSign : ℕ) (pShDemLen : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [el.count, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, d.L, k] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pDemPos + el.count * d.L ≤ 2 ^ w ∧ pDemNeg + el.count * d.L ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      d.signBuf.length = el.count ∧ d.lenBuf.length = el.count⌝ *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemPos + c * d.L) (edgePosRow d.I d.hv d.act d.L d.I.m c)) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemNeg + c * d.L) (edgeNegRow d.I d.hv d.act d.L d.I.m c)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pShDemBuf + c * d.L) (List.replicate d.L 0)) *
    Assn.list pShDemSign d.signBuf * Assn.list pShDemLen d.lenBuf
  post := fun d args v => ⨆ (pDemPos : ℕ) (pDemNeg : ℕ) (pShDemBuf : ℕ)
      (pShDemSign : ℕ) (pShDemLen : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [el.count, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, d.L, k] ∧ v = 0⌝ *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemPos + c * d.L) (normLimbs k (edgePosRow d.I d.hv d.act d.L d.I.m c))) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pDemNeg + c * d.L) (normLimbs k (edgeNegRow d.I d.hv d.act d.L d.I.m c))) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length)

theorem stage0ShiftDemFin_meets {w : ℕ} {p : Program} {f shiftOneDem : ℕ} {T1 : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftDemFin shiftOneDem))
    (h1 : Meets w p shiftOneDem ((stage0ShiftOneDemSpec w).withCost fun d _ => T1 d.pos.length)) :
    Meets w p f ((stage0ShiftDemFinSpec w).withCost fun d _ =>
      (T1 d.L + 90) * (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count + 35) := by
  sep_enter d with hact hL1 h2k1 hedgeLt hdemLt hpPos hpNeg hpBuf hcntL hsignB hlenB
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have hk1 : 1 ≤ narrowLimbWidth d.I := one_le_narrowLimbWidth d.I
  have hm1_lt : d.I.m + 1 < 2 ^ narrowLimbWidth d.I := m_add_one_lt_pow_limbWidth d.I d.hv
  have h2k_le : (2 ^ narrowLimbWidth d.I) * (2 ^ narrowLimbWidth d.I) ≤ 2 ^ (w - 1) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprops := edgeRow_props d.I d.hv hact hL1 hedgeLt hdemLt d.I.m le_rfl
  sep_step
  sep_for (fun i (len0 : ℕ) =>
      ⟨[el.count, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, d.L, narrowLimbWidth d.I,
        i * d.L, i, len0],
      i ≤ el.count, (T1 d.L + 70) * (el.count - i) + 15,
      [∏ c ∈ Finset.range el.count,
         Assn.list (pDemPos + c * d.L)
           (if c < i then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
            else edgePosRow d.I d.hv d.act d.L d.I.m c),
       ∏ c ∈ Finset.range el.count,
         Assn.list (pDemNeg + c * d.L)
           (if c < i then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
            else edgeNegRow d.I d.hv d.act d.L d.I.m c),
       ∏ c ∈ Finset.range el.count,
         Assn.list (pShDemBuf + c * d.L)
           (if c < i then
              padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
                (activeShiftedDemand d.I d.act c).natAbs) d.L
            else List.replicate d.L 0),
       Assn.list pShDemSign
         ((List.ofFn fun j : Fin i =>
           if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) ++ d.signBuf.drop i),
       Assn.list pShDemLen
         ((List.ofFn fun j : Fin i =>
           (Nat.digits (2 ^ narrowLimbWidth d.I)
             (activeShiftedDemand d.I d.act j.val).natAbs).length) ++ d.lenBuf.drop i)]⟩)
    with len0
  · have hi_act : i < d.act.length := by rw [hact.1]; exact hhi
    have hmem : i ∈ Finset.range el.count := Finset.mem_range.mpr hhi
    obtain ⟨hpL, hnL, hpB, hnB, hpV, hnV, hdiff⟩ := hprops i
    have hposW : ∀ x ∈ edgePosRow d.I d.hv d.act d.L d.I.m i, x < 2 ^ (w - 1) := by
      intro x hx
      have hxb := hpB x hx
      have hle1 : (d.I.m + 1) * (2 ^ narrowLimbWidth d.I - 1) ≤
          (d.I.m + 1) * 2 ^ narrowLimbWidth d.I :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hlt2 := Nat.mul_lt_mul_of_pos_right hm1_lt (Nat.two_pow_pos (narrowLimbWidth d.I))
      omega
    have hnegW : ∀ x ∈ edgeNegRow d.I d.hv d.act d.L d.I.m i, x < 2 ^ (w - 1) := by
      intro x hx
      have hxb := hnB x hx
      have hle1 : (d.I.m + 1) * (2 ^ narrowLimbWidth d.I - 1) ≤
          (d.I.m + 1) * 2 ^ narrowLimbWidth d.I :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hlt2 := Nat.mul_lt_mul_of_pos_right hm1_lt (Nat.two_pow_pos (narrowLimbWidth d.I))
      omega
    have hpow_step : (2 ^ narrowLimbWidth d.I) ^ d.L =
        2 ^ narrowLimbWidth d.I * (2 ^ narrowLimbWidth d.I) ^ (d.L - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hL1]
    have hposFit : Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i) <
        (2 ^ narrowLimbWidth d.I) ^ (edgePosRow d.I d.hv d.act d.L d.I.m i).length := by
      rw [hpL, hpow_step]
      exact lt_trans hpV (Nat.mul_lt_mul_of_pos_right hm1_lt (Nat.pow_pos (Nat.two_pow_pos _)))
    have hnegFit : Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i) <
        (2 ^ narrowLimbWidth d.I) ^ (edgeNegRow d.I d.hv d.act d.L d.I.m i).length := by
      rw [hnL, hpow_step]
      exact lt_trans hnV (Nat.mul_lt_mul_of_pos_right hm1_lt (Nat.pow_pos (Nat.two_pow_pos _)))
    have hdiff_eq :
        ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ) =
        activeShiftedDemand d.I d.act i := by
      rw [activeShiftedDemand_eq hact hi_act, hdiff hi_act, FlowReduction.shiftedDemand]
      congr 1
      apply Finset.sum_congr rfl; intro e _; simp [e.isLt]
    -- Pull block i from pDemPos, pDemNeg, pShDemBuf, and cell i from pShDemSign
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun c => Assn.list (pDemPos + c * d.L)
        (if c < i then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
         else edgePosRow d.I d.hv d.act d.L d.I.m c))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun c => Assn.list (pDemNeg + c * d.L)
        (if c < i then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
         else edgeNegRow d.I d.hv d.act d.L d.I.m c))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun c => Assn.list (pShDemBuf + c * d.L)
        (if c < i then
           padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L
         else List.replicate d.L 0))
    have hcurP : Assn.list (pDemPos + i * d.L)
        (if i < i then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i)
         else edgePosRow d.I d.hv d.act d.L d.I.m i) =
        Assn.list (pDemPos + i * d.L) (edgePosRow d.I d.hv d.act d.L d.I.m i) := by simp
    have hcurN : Assn.list (pDemNeg + i * d.L)
        (if i < i then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i)
         else edgeNegRow d.I d.hv d.act d.L d.I.m i) =
        Assn.list (pDemNeg + i * d.L) (edgeNegRow d.I d.hv d.act d.L d.I.m i) := by simp
    have hcurB : Assn.list (pShDemBuf + i * d.L)
        (if i < i then
           padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act i).natAbs) d.L
         else List.replicate d.L 0) =
        Assn.list (pShDemBuf + i * d.L) (List.replicate d.L 0) := by simp
    sep_apply hcurP; sep_apply hcurN; sep_apply hcurB
    have hsign_split :
        Assn.list pShDemSign
          ((List.ofFn fun j : Fin i =>
            if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) ++ d.signBuf.drop i) =
        Assn.list pShDemSign
          (List.ofFn fun j : Fin i =>
            if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) *
        (pShDemSign + i ↦ d.signBuf[i]'(by omega)) *
        Assn.list (pShDemSign + (i + 1)) (d.signBuf.drop (i + 1)) := by
      rw [Assn.list_append, List.length_ofFn,
        List.drop_eq_getElem_cons (by omega : i < d.signBuf.length), Assn.list_cons]
      simp only [mul_assoc, show pShDemSign + i + 1 = pShDemSign + (i + 1) by omega]
    sep_apply hsign_split
    generalize hF :
      ((∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pDemPos + c * d.L)
            (if c < i then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
             else edgePosRow d.I d.hv d.act d.L d.I.m c)) *
       (∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pDemNeg + c * d.L)
            (if c < i then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
             else edgeNegRow d.I d.hv d.act d.L d.I.m c)) *
       (∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pShDemBuf + c * d.L)
            (if c < i then
               padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L
             else List.replicate d.L 0)) *
       Assn.list pShDemSign
         (List.ofFn fun j : Fin i => if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) *
       Assn.list (pShDemSign + (i + 1)) (d.signBuf.drop (i + 1)) *
       Assn.list pShDemLen
         ((List.ofFn fun j : Fin i =>
           (Nat.digits (2 ^ narrowLimbWidth d.I)
             (activeShiftedDemand d.I d.act j.val).natAbs).length) ++ d.lenBuf.drop i)) = F
    sep_apply hF
    sep_step from (⟨narrowLimbWidth d.I, edgePosRow d.I d.hv d.act d.L d.I.m i,
      edgeNegRow d.I d.hv d.act d.L d.I.m i, List.replicate d.L 0,
      d.signBuf[i]'(by omega)⟩ : ShiftOneDemData)
    subst F; sep_norm
    rw [hdiff_eq] at hlen
    -- Reassemble all 4 arrays for i + 1
    have hPn :
        Assn.list (pDemPos + i * d.L) (normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i)) *
        (∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pDemPos + c * d.L)
            (if c < i then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
             else edgePosRow d.I d.hv d.act d.L d.I.m c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemPos + c * d.L)
            (if c < i + 1 then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
             else edgePosRow d.I d.hv d.act d.L d.I.m c) := by
      rw [Assn.prod_eq_mul_erase hmem]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro c hc
        have hne : c ≠ i := Finset.ne_of_mem_erase hc
        have hiff : (c < i + 1) ↔ (c < i) := by omega
        simp [hiff]
    have hNn :
        Assn.list (pDemNeg + i * d.L) (normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i)) *
        (∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pDemNeg + c * d.L)
            (if c < i then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
             else edgeNegRow d.I d.hv d.act d.L d.I.m c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemNeg + c * d.L)
            (if c < i + 1 then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
             else edgeNegRow d.I d.hv d.act d.L d.I.m c) := by
      rw [Assn.prod_eq_mul_erase hmem]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro c hc
        have hne : c ≠ i := Finset.ne_of_mem_erase hc
        have hiff : (c < i + 1) ↔ (c < i) := by omega
        simp [hiff]
    have hBn :
        Assn.list (pShDemBuf + i * d.L)
          (padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
            (((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ) -
             ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ)).natAbs)
            (edgePosRow d.I d.hv d.act d.L d.I.m i).length) *
        (∏ c ∈ (Finset.range el.count).erase i,
          Assn.list (pShDemBuf + c * d.L)
            (if c < i then
               padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L
             else List.replicate d.L 0)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pShDemBuf + c * d.L)
            (if c < i + 1 then
               padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L
             else List.replicate d.L 0) := by
      rw [hdiff_eq, hpL, Assn.prod_eq_mul_erase hmem]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro c hc
        have hne : c ≠ i := Finset.ne_of_mem_erase hc
        have hiff : (c < i + 1) ↔ (c < i) := by omega
        simp [hiff]
    have hSn :
        Assn.list pShDemSign
          (List.ofFn fun j : Fin i => if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) *
        (pShDemSign + i ↦
          if ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ) -
             ((Nat.ofDigits (2 ^ narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m i) : ℕ) : ℤ) < 0
          then 1 else 0) *
        Assn.list (pShDemSign + (i + 1)) (d.signBuf.drop (i + 1)) =
        Assn.list pShDemSign
          ((List.ofFn fun j : Fin (i + 1) =>
            if activeShiftedDemand d.I d.act j.val < 0 then 1 else 0) ++ d.signBuf.drop (i + 1)) := by
      rw [hdiff_eq, List.ofFn_succ', List.concat_eq_append, List.append_assoc, Assn.list_append,
        List.length_ofFn, List.singleton_append, Assn.list_cons]
      simp only [Fin.val_castSucc, Fin.val_last, mul_assoc,
        show pShDemSign + i + 1 = pShDemSign + (i + 1) by omega]
    sep_apply hPn; sep_apply hNn; sep_apply hBn; sep_apply hSn
    have hlen_l : ((List.ofFn fun j : Fin i =>
        (Nat.digits (2 ^ narrowLimbWidth d.I)
          (activeShiftedDemand d.I d.act j.val).natAbs).length) ++ d.lenBuf.drop i).length =
        el.count := by simp; omega
    have hnext_mul : i * d.L + d.L = (i + 1) * d.L := by ring
    have hnext_lt : (i + 1) * d.L ≤ el.count * d.L := Nat.mul_le_mul_right d.L (by omega)
    sep_step
    have hset_len :
        ((List.ofFn fun j : Fin i =>
            (Nat.digits (2 ^ narrowLimbWidth d.I)
              (activeShiftedDemand d.I d.act j.val).natAbs).length) ++ d.lenBuf.drop i).set i len =
        (List.ofFn fun j : Fin (i + 1) =>
            (Nat.digits (2 ^ narrowLimbWidth d.I)
              (activeShiftedDemand d.I d.act j.val).natAbs).length) ++ d.lenBuf.drop (i + 1) := by
      rw [set_append_drop (by simp) (by omega), List.ofFn_succ', List.concat_eq_append]
      simp [hlen]
    sep_apply (show Assn.list pShDemLen _ = Assn.list pShDemLen _ from congrArg (Assn.list pShDemLen) hset_len)
    sep_step
    · rw [hpL, Nat.cast_add, Nat.cast_one]; linarith
  · have hPfin : (∏ c ∈ Finset.range el.count,
        Assn.list (pDemPos + c * d.L)
          (if c < el.count then normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)
           else edgePosRow d.I d.hv d.act d.L d.I.m c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemPos + c * d.L)
            (normLimbs (narrowLimbWidth d.I) (edgePosRow d.I d.hv d.act d.L d.I.m c)) := by
      apply Finset.prod_congr rfl; intro c hc; simp [Finset.mem_range.mp hc]
    have hNfin : (∏ c ∈ Finset.range el.count,
        Assn.list (pDemNeg + c * d.L)
          (if c < el.count then normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)
           else edgeNegRow d.I d.hv d.act d.L d.I.m c)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pDemNeg + c * d.L)
            (normLimbs (narrowLimbWidth d.I) (edgeNegRow d.I d.hv d.act d.L d.I.m c)) := by
      apply Finset.prod_congr rfl; intro c hc; simp [Finset.mem_range.mp hc]
    have hBfin : (∏ c ∈ Finset.range el.count,
        Assn.list (pShDemBuf + c * d.L)
          (if c < el.count then
             padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L
           else List.replicate d.L 0)) =
        ∏ c ∈ Finset.range el.count,
          Assn.list (pShDemBuf + c * d.L)
            (padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L) := by
      apply Finset.prod_congr rfl; intro c hc; simp [Finset.mem_range.mp hc]
    sep_apply hPfin; sep_apply hNfin; sep_apply hBfin
    have hd1 : d.signBuf.drop el.count = [] := List.drop_of_length_le (by omega)
    have hd2 : d.lenBuf.drop el.count = [] := List.drop_of_length_le (by omega)
    rw [hd1, hd2, List.append_nil, List.append_nil]
    sep_step

/-! ### `stage0ShiftDem`: combine `demInit`, `demEdges`, and `demFin` -/

wram_def stage0ShiftDem (demInit demEdges demFin : ℕ)
    (pEdges, pDems, pLabels, pActive, m, cnt, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, L, k) {
  d := demInit(pDems, pActive, cnt, pDemPos, pDemNeg, L)
  d := demEdges(pEdges, m, pLabels, pDemPos, pDemNeg, L)
  d := demFin(cnt, pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, L, k)
  return 0
}

structure Stage0ShiftDemData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  actTail : List ℕ
  L : ℕ

def stage0ShiftDemSpec (w : ℕ) : Spec Stage0ShiftDemData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pDemPos : ℕ) (pDemNeg : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, pDemPos, pDemNeg,
        pShDemBuf, pShDemSign, pShDemLen, d.L, k] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m, (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pDems + 3 * d.I.n ≤ 2 ^ w ∧ 3 * d.I.n < 2 ^ w ∧
      pDemPos + el.count * d.L ≤ 2 ^ w ∧ pDemNeg + el.count * d.L ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (List.replicate d.L 0)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (List.replicate d.L 0)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pShDemBuf + c * d.L) (List.replicate d.L 0)) *
    Assn.list pShDemSign (List.replicate el.count 0) *
    Assn.list pShDemLen (List.replicate el.count 0)
  post := fun d args v => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pDemPos : ℕ) (pDemNeg : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, pDemPos, pDemNeg,
        pShDemBuf, pShDemSign, pShDemLen, d.L, k] ∧ v = 0⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
    (∏ c ∈ Finset.range el.count,
      Assn.list (pShDemBuf + c * d.L)
        (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.gc

theorem stage0ShiftDem_meets {w : ℕ} {p : Program} {f demInit demEdges demFin : ℕ}
    {Tdi Tde Tdf : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftDem demInit demEdges demFin))
    (hdi : Meets w p demInit ((stage0ShiftDemInitSpec w).withCost fun d _ =>
      Tdi (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count d.L))
    (hde : Meets w p demEdges ((stage0ShiftDemEdgesSpec w).withCost fun d _ => Tde d.I.m d.L))
    (hdf : Meets w p demFin ((stage0ShiftDemFinSpec w).withCost fun d _ =>
      Tdf (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count d.L)) :
    Meets w p f ((stage0ShiftDemSpec w).withCost fun d _ =>
      let cnt := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count
      Tdi cnt d.L + Tde d.I.m d.L + Tdf cnt d.L + 60) := by
  sep_enter d with hact hL1 h2k1 hloLt hdemLt hpE h11m hpD h3n hpPos hpNeg hpBuf hcntL
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have h2k : 2 * narrowLimbWidth d.I ≤ w := by omega
  generalize hGout :
    ((∏ c ∈ Finset.range el.count, Assn.list (pShDemBuf + c * d.L) (List.replicate d.L 0)) *
     Assn.list pShDemSign (List.replicate el.count 0) *
     Assn.list pShDemLen (List.replicate el.count 0)) = Gout
  sep_apply hGout
  generalize hF1 :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.act, d.actTail, d.L⟩ : Stage0ShiftDemInitData)
  subst F1; sep_norm
  generalize hF2 :
    ((∏ v ∈ Finset.range d.I.n,
        Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
     Assn.list pActive (d.act ++ d.actTail)) = F2
  sep_apply hF2
  sep_step from (⟨d.I, d.hv, d.act, d.L⟩ : Stage0ShiftDemEdgesData)
  generalize hF3 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table)) = F3
  sep_apply hF3
  subst Gout; sep_norm
  have hrep_cnt : (List.replicate el.count 0).length =
      (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count := List.length_replicate
  sep_step from (⟨d.I, d.hv, d.act, d.L, List.replicate el.count 0,
    List.replicate el.count 0⟩ : Stage0ShiftDemFinData)
  subst F2 F3; sep_norm
  sep_step
  · refine (Assn.noDebt_credits (by dsimp only [el]; omega)).mul ?_
    exact (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _).mul
      (Assn.noDebt_prod _ fun _ _ => Assn.noDebt_list _ _)

end MinCostFlow.NarrowProg
