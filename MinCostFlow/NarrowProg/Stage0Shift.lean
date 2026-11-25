module

public import MinCostFlow.NarrowProg.Stage0ShiftDemFin
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 3: top-level `stage0Shift` and polymorphic `stage0ShiftMod`

Allocates shifted capacity and active-demand arrays from `Assn.free h (2 ^ w - h)` (`0` space and
`0` work per isolated vertex) and runs `stage0ShiftCaps`, `stage0ShiftDemInit`,
`stage0ShiftDemEdges`, and `stage0ShiftDemFin` in `O(m * (L + 1) + 1)` time.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg


/-- Exact space allocated by `stage0Shift` (0 space per isolated vertex). -/
def stage0ShiftSpace (m cnt L : ℕ) : ℕ :=
  m * L + m + 3 * cnt * L + 2 * cnt + 2 * L

theorem stage0ShiftSpace_le (m cnt L : ℕ) (hcnt : cnt ≤ 2 * m) :
    stage0ShiftSpace m cnt L ≤ 7 * m * L + 5 * m + 2 * L := by
  unfold stage0ShiftSpace
  have : 3 * cnt * L ≤ 6 * m * L := by
    calc 3 * cnt * L ≤ 3 * (2 * m) * L := Nat.mul_le_mul_right L (by omega)
      _ = 6 * m * L := by ring
  nlinarith

private theorem split_free_shift {h m cnt L w : ℕ}
    (hfit : h + stage0ShiftSpace m cnt L < 2 ^ w) :
    Assn.free h (2 ^ w - h) ≤
      (∏ i ∈ Finset.range m, Assn.list (h + i * L) (List.replicate L 0)) *
      Assn.list (h + m * L) (List.replicate m 0) *
      (∏ c ∈ Finset.range cnt, Assn.list (h + m * L + m + c * L) (List.replicate L 0)) *
      (∏ c ∈ Finset.range cnt, Assn.list (h + m * L + m + cnt * L + c * L) (List.replicate L 0)) *
      (∏ c ∈ Finset.range cnt, Assn.list (h + m * L + m + cnt * L + cnt * L + c * L) (List.replicate L 0)) *
      Assn.list (h + m * L + m + cnt * L + cnt * L + cnt * L) (List.replicate cnt 0) *
      Assn.list (h + m * L + m + cnt * L + cnt * L + cnt * L + cnt) (List.replicate cnt 0) *
      Assn.list (h + m * L + m + cnt * L + cnt * L + cnt * L + cnt + cnt) (List.replicate L 0) *
      Assn.list (h + m * L + m + cnt * L + cnt * L + cnt * L + cnt + cnt + L) (List.replicate L 0) *
      Assn.free (h + stage0ShiftSpace m cnt L) (2 ^ w - (h + stage0ShiftSpace m cnt L)) := by
  unfold stage0ShiftSpace at hfit ⊢
  set mL := m * L
  set cL := cnt * L
  have hsp : h + (mL + m + 3 * cnt * L + 2 * cnt + 2 * L) =
      h + mL + m + cL + cL + cL + cnt + cnt + L + L := by
    change h + (m * L + m + 3 * cnt * L + 2 * cnt + 2 * L) =
      h + m * L + m + cnt * L + cnt * L + cnt * L + cnt + cnt + L + L
    ring
  rw [hsp]
  have hfit' : h + mL + m + cL + cL + cL + cnt + cnt + L + L < 2 ^ w := hsp ▸ hfit
  have h1 : 2 ^ w - h = mL + (2 ^ w - (h + mL)) := by omega
  have h2 : 2 ^ w - (h + mL) = m + (2 ^ w - (h + mL + m)) := by omega
  have h3 : 2 ^ w - (h + mL + m) = cL + (2 ^ w - (h + mL + m + cL)) := by omega
  have h4 : 2 ^ w - (h + mL + m + cL) = cL + (2 ^ w - (h + mL + m + cL + cL)) := by omega
  have h5 : 2 ^ w - (h + mL + m + cL + cL) = cL + (2 ^ w - (h + mL + m + cL + cL + cL)) := by omega
  have h6 : 2 ^ w - (h + mL + m + cL + cL + cL) = cnt + (2 ^ w - (h + mL + m + cL + cL + cL + cnt)) := by omega
  have h7 : 2 ^ w - (h + mL + m + cL + cL + cL + cnt) = cnt + (2 ^ w - (h + mL + m + cL + cL + cL + cnt + cnt)) := by omega
  have h8 : 2 ^ w - (h + mL + m + cL + cL + cL + cnt + cnt) = L + (2 ^ w - (h + mL + m + cL + cL + cL + cnt + cnt + L)) := by omega
  have h9 : 2 ^ w - (h + mL + m + cL + cL + cL + cnt + cnt + L) = L + (2 ^ w - (h + mL + m + cL + cL + cL + cnt + cnt + L + L)) := by omega
  rw [h1, Assn.free_add', h2, Assn.free_add, h3, Assn.free_add', h4, Assn.free_add',
      h5, Assn.free_add', h6, Assn.free_add, h7, Assn.free_add, h8, Assn.free_add,
      h9, Assn.free_add, free_to_prod_replicate, free_to_prod_replicate,
      free_to_prod_replicate, free_to_prod_replicate]
  simp only [← mul_assoc]
  exact le_refl _

private theorem list_split_five {p : ℕ} {xs : List ℕ} (h : xs.length = 5) :
    Assn.list p xs =
      (p ↦ xs[0]'(by omega)) * (p + 1 ↦ xs[1]'(by omega)) * (p + 2 ↦ xs[2]'(by omega)) *
      (p + 3 ↦ xs[3]'(by omega)) * (p + 4 ↦ xs[4]'(by omega)) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | _⟩⟩⟩⟩⟩ <;> simp at h
  simp only [Assn.list_cons, Assn.list_nil, mul_one, ← mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 1 + 1 + 1 = p + 3 by omega,
    show p + 1 + 1 + 1 + 1 = p + 4 by omega, List.getElem_cons_zero, List.getElem_cons_succ]

private theorem list_join_five (p a b c d e : ℕ) :
    (p ↦ a) * (p + 1 ↦ b) * (p + 2 ↦ c) * (p + 3 ↦ d) * (p + 4 ↦ e) =
      Assn.list p [a, b, c, d, e] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, ← mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 1 + 1 + 1 = p + 3 by omega,
    show p + 1 + 1 + 1 + 1 = p + 4 by omega]

wram_def stage0ShiftWork (shiftCaps shiftDem : ℕ)
    (pEdges, pDems, pLabels, pActive, m, cnt, pShCapBuf, pShCapLen,
     pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, pTmpA, pTmpB, L, k) {
  d := shiftCaps(pEdges, m, pShCapBuf, pShCapLen, pTmpA, pTmpB, L, k)
  d := shiftDem(pEdges, pDems, pLabels, pActive, m, cnt, pDemPos, pDemNeg,
    pShDemBuf, pShDemSign, pShDemLen, L, k)
  return 0
}

structure Stage0ShiftWorkData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  actTail : List ℕ
  L : ℕ

def stage0ShiftWorkSpec (w : ℕ) : Spec Stage0ShiftWorkData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pShCapBuf : ℕ) (pShCapLen : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pTmpA : ℕ) (pTmpB : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, pShCapBuf, pShCapLen,
        pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, pTmpA, pTmpB, d.L, k] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < d.L) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pDems + 3 * d.I.n ≤ 2 ^ w ∧ 3 * d.I.n < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pDemPos + el.count * d.L ≤ 2 ^ w ∧ pDemNeg + el.count * d.L ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
    (∏ i ∈ Finset.range d.I.m, Assn.list (pShCapBuf + i * d.L) (List.replicate d.L 0)) *
    Assn.list pShCapLen (List.replicate d.I.m 0) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (List.replicate d.L 0)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (List.replicate d.L 0)) *
    (∏ c ∈ Finset.range el.count, Assn.list (pShDemBuf + c * d.L) (List.replicate d.L 0)) *
    Assn.list pShDemSign (List.replicate el.count 0) *
    Assn.list pShDemLen (List.replicate el.count 0) *
    Assn.list pTmpA (List.replicate d.L 0) *
    Assn.list pTmpB (List.replicate d.L 0)
  post := fun d args v => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pShCapBuf : ℕ) (pShCapLen : ℕ) (pDemPos : ℕ) (pDemNeg : ℕ)
      (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ) (pTmpA : ℕ) (pTmpB : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, pShCapBuf, pShCapLen,
        pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, pTmpA, pTmpB, d.L, k] ∧ v = 0⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
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
    Assn.gc

theorem stage0ShiftWork_meets {w : ℕ} {p : Program} {f shiftCaps shiftDem : ℕ}
    {Tc : ℕ → ℕ → ℕ} {Td : ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftWork shiftCaps shiftDem))
    (hc : Meets w p shiftCaps ((stage0ShiftCapsSpec w).withCost fun d _ => Tc d.I.m d.L))
    (hd : Meets w p shiftDem ((stage0ShiftDemSpec w).withCost fun d _ =>
      Td d.I.m (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count d.L)) :
    Meets w p f ((stage0ShiftWorkSpec w).withCost fun d _ =>
      let cnt := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count
      Tc d.I.m d.L + Td d.I.m cnt d.L + 80) := by
  sep_enter d with hact hL1 h2k1 hcaps hedgeLt hdemLt hpE h11m hpD h3n hpCap hmL hpPos hpNeg hpBuf hcntL
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have hloLt : ∀ e : Fin d.I.m,
      (Nat.digits (2 ^ narrowLimbWidth d.I) (d.I.edge e).lower.natAbs).length < d.L :=
    fun e => (hedgeLt e).1
  have h2k : 2 * narrowLimbWidth d.I ≤ w := by omega
  generalize hF1 :
    ((∏ v ∈ Finset.range d.I.n,
        Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table) * Assn.list pActive (d.act ++ d.actTail) *
     (∏ c ∈ Finset.range el.count, Assn.list (pDemPos + c * d.L) (List.replicate d.L 0)) *
     (∏ c ∈ Finset.range el.count, Assn.list (pDemNeg + c * d.L) (List.replicate d.L 0)) *
     (∏ c ∈ Finset.range el.count, Assn.list (pShDemBuf + c * d.L) (List.replicate d.L 0)) *
     Assn.list pShDemSign (List.replicate el.count 0) *
     Assn.list pShDemLen (List.replicate el.count 0)) = F1
  sep_apply hF1
  sep_step from (⟨d.I, d.hv, d.L, List.replicate d.I.m 0, List.replicate d.L 0,
    List.replicate d.L 0⟩ : Stage0ShiftCapsData) with htmpA1 htmpB1
  generalize hGcaps :
    ((∏ i ∈ Finset.range d.I.m,
        Assn.list (pShCapBuf + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
              ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
     Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
        (Nat.digits (2 ^ narrowLimbWidth d.I) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
     Assn.list pTmpA tmpA1 * Assn.list pTmpB tmpB1) = Gcaps
  sep_apply hGcaps
  subst F1; sep_norm
  sep_step from (⟨d.I, d.hv, d.act, d.actTail, d.L⟩ : Stage0ShiftDemData)
  subst Gcaps; sep_norm
  sep_step
  · dsimp only [el]; omega

wram_def stage0Shift (shiftWork : ℕ)
    (pEdges, pDems, pLabels, pActive, m, cnt, L, k, pShiftOut, h) {
  mL := m * L
  cL := cnt * L
  pShCapBuf := h
  pShCapLen := pShCapBuf + mL
  pDemPos := pShCapLen + m
  pDemNeg := pDemPos + cL
  pShDemBuf := pDemNeg + cL
  pShDemSign := pShDemBuf + cL
  pShDemLen := pShDemSign + cnt
  pTmpA := pShDemLen + cnt
  pTmpB := pTmpA + L
  hNext := pTmpB + L
  d := shiftWork(pEdges, pDems, pLabels, pActive, m, cnt, pShCapBuf, pShCapLen,
    pDemPos, pDemNeg, pShDemBuf, pShDemSign, pShDemLen, pTmpA, pTmpB, L, k)
  mem[pShiftOut] := pShCapBuf
  mem[pShiftOut + 1] := pShCapLen
  mem[pShiftOut + 2] := pShDemBuf
  mem[pShiftOut + 3] := pShDemSign
  mem[pShiftOut + 4] := pShDemLen
  return hNext
}

structure Stage0ShiftData where
  I : Instance
  hv : I.IsValid
  act : List ℕ
  actTail : List ℕ
  L : ℕ
  outBuf : List ℕ

def stage0ShiftSpec (w : ℕ) : Spec Stage0ShiftData where
  pre := fun d args => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pShiftOut : ℕ) (h : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, d.L, k, pShiftOut, h] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ 2 * k + 1 ≤ w ∧
      (∀ e : Fin d.I.m, (d.I.edge e).lower ≤ (d.I.edge e).upper) ∧
      (∀ e : Fin d.I.m,
        (Nat.digits (2 ^ k) (d.I.edge e).lower.natAbs).length < d.L ∧
        (Nat.digits (2 ^ k) (d.I.edge e).upper.natAbs).length < d.L) ∧
      (∀ (c : ℕ) (hc : c < d.act.length),
        (Nat.digits (2 ^ k) (d.I.d (d.act[c]'hc)).natAbs).length < d.L) ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pDems + 3 * d.I.n ≤ 2 ^ w ∧ 3 * d.I.n < 2 ^ w ∧
      d.outBuf.length = 5 ∧ h + stage0ShiftSpace d.I.m el.count d.L < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
    Assn.list pShiftOut d.outBuf * Assn.free h (2 ^ w - h)
  post := fun d args h' => ⨆ (pEdges : ℕ) (pDems : ℕ) (pLabels : ℕ) (pActive : ℕ)
      (pShiftOut : ℕ) (h : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let mL := d.I.m * d.L
    let cL := el.count * d.L
    let pShCapBuf := h
    let pShCapLen := h + mL
    let pShDemBuf := h + mL + d.I.m + cL + cL
    let pShDemSign := pShDemBuf + cL
    let pShDemLen := pShDemSign + el.count
    ⌜args = [pEdges, pDems, pLabels, pActive, d.I.m, el.count, d.L, k, pShiftOut, h] ∧
      h' = h + stage0ShiftSpace d.I.m el.count d.L⌝ *
    Assn.list 0 (narrowEncode d.I) *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range d.I.n,
      Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pActive (d.act ++ d.actTail) *
    Assn.list pShiftOut [pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen] *
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
    Assn.free (h + stage0ShiftSpace d.I.m el.count d.L)
      (2 ^ w - (h + stage0ShiftSpace d.I.m el.count d.L)) * Assn.gc

theorem stage0Shift_meets {w : ℕ} {p : Program} {f shiftWork : ℕ}
    {Tw : ℕ → ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0Shift shiftWork))
    (hw : Meets w p shiftWork ((stage0ShiftWorkSpec w).withCost fun d _ =>
      Tw d.I.m (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count d.L)) :
    Meets w p f ((stage0ShiftSpec w).withCost fun d _ =>
      let cnt := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count
      Tw d.I.m cnt d.L + 120) := by
  sep_enter d with hact hL1 h2k1 hcaps hedgeLt hdemLt hpE h11m hpD h3n hout hfit
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  have hsp_def : stage0ShiftSpace d.I.m el.count d.L =
      d.I.m * d.L + d.I.m + 3 * el.count * d.L + 2 * el.count + 2 * d.L := rfl
  have h3cL : 3 * el.count * d.L = el.count * d.L + el.count * d.L + el.count * d.L := by ring
  generalize hPre0 :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     (∏ v ∈ Finset.range d.I.n,
        Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table) * Assn.list pActive (d.act ++ d.actTail) *
     Assn.list pShiftOut d.outBuf * Assn.free h (2 ^ w - h)) = Pre0
  sep_apply hPre0
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  subst mL cL pDemPos pShDemBuf pShDemLen pTmpA pTmpB hNext
  subst Pre0; sep_norm
  sep_apply split_free_shift (h := h) (m := d.I.m) (cnt := el.count) (L := d.L) (w := w) hfit
  sep_apply list_split_five (p := pShiftOut) hout
  generalize hG0 :
    ((pShiftOut ↦ d.outBuf[0]'(by omega)) * (pShiftOut + 1 ↦ d.outBuf[1]'(by omega)) *
     (pShiftOut + 2 ↦ d.outBuf[2]'(by omega)) * (pShiftOut + 3 ↦ d.outBuf[3]'(by omega)) *
     (pShiftOut + 4 ↦ d.outBuf[4]'(by omega)) *
     Assn.free (h + stage0ShiftSpace d.I.m el.count d.L)
       (2 ^ w - (h + stage0ShiftSpace d.I.m el.count d.L))) = G0
  sep_apply hG0
  have hfit_cL : (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count * d.L < 2 ^ w := by
    change el.count * d.L < 2 ^ w; omega
  have hfit_pos : h + d.I.m * d.L + d.I.m +
      (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count * d.L ≤ 2 ^ w := by
    change h + d.I.m * d.L + d.I.m + el.count * d.L ≤ 2 ^ w; omega
  have hfit_neg : h + d.I.m * d.L + d.I.m + el.count * d.L +
      (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count * d.L ≤ 2 ^ w := by
    change h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L ≤ 2 ^ w; omega
  have hfit_buf : h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L +
      (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count * d.L ≤ 2 ^ w := by
    change h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L ≤ 2 ^ w; omega
  sep_step from (⟨d.I, d.hv, d.act, d.actTail, d.L⟩ : Stage0ShiftWorkData)
  generalize hGwork :
    (Assn.list 0 (narrowEncode d.I) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
     (∏ v ∈ Finset.range d.I.n,
        Assn.list (pDems + v * 3) (if hlt : v < d.I.n then demRec d.I ⟨v, hlt⟩ else [])) *
     Assn.list pLabels (List.ofFn el.table) * Assn.list pActive (d.act ++ d.actTail) *
     (∏ i ∈ Finset.range d.I.m,
        Assn.list (h + i * d.L)
          (if hlt : i < d.I.m then
            padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I)
              ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hlt⟩)) d.L
          else [])) *
     Assn.list (h + d.I.m * d.L) (List.ofFn fun e : Fin d.I.m =>
        (Nat.digits (2 ^ narrowLimbWidth d.I) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
     (∏ c ∈ Finset.range el.count,
        Assn.list (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + c * d.L)
          (padLimbs (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c).natAbs) d.L)) *
     Assn.list (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L)
       (List.ofFn fun c : Fin el.count =>
         if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
     Assn.list (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L + el.count)
       (List.ofFn fun c : Fin el.count =>
         (Nat.digits (2 ^ narrowLimbWidth d.I) (activeShiftedDemand d.I d.act c.val).natAbs).length)) = Gwork
  sep_apply hGwork
  subst G0; sep_norm
  sep_step; sep_step; sep_step; sep_step; sep_step
  sep_apply list_join_five pShiftOut h (h + d.I.m * d.L)
    (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L)
    (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L)
    (h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L + el.count)
  subst Gwork; sep_norm
  have hnext_eq :
      h + d.I.m * d.L + d.I.m + el.count * d.L + el.count * d.L + el.count * d.L +
        el.count + el.count + d.L + d.L =
      h + stage0ShiftSpace d.I.m el.count d.L := by
    unfold stage0ShiftSpace; ring
  sep_step
  · dsimp only [el]; omega

theorem stage0Shift_meets_direct {w : ℕ} {p : Program}
    {f pCopy lAdd lSub lCmp cLen accAdd accNorm sOneCap sOneDem sCaps dInit dEdges dFin sDem sWork : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0Shift sWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlAdd : p.procs[lAdd]? = some limbsAdd)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (haccAdd : p.procs[accAdd]? = some accAddLimbs)
    (haccNorm : p.procs[accNorm]? = some accNormalize)
    (hsOneCap : p.procs[sOneCap]? = some (stage0ShiftOneCap pCopy lAdd lSub cLen))
    (hsOneDem : p.procs[sOneDem]? = some (stage0ShiftOneDem accNorm lCmp lSub cLen))
    (hsCaps : p.procs[sCaps]? = some (stage0ShiftCaps sOneCap))
    (hdInit : p.procs[dInit]? = some (stage0ShiftDemInit accAdd))
    (hdEdges : p.procs[dEdges]? = some (stage0ShiftDemEdges accAdd))
    (hdFin : p.procs[dFin]? = some (stage0ShiftDemFin sOneDem))
    (hsDem : p.procs[sDem]? = some (stage0ShiftDem dInit dEdges dFin))
    (hsWork : p.procs[sWork]? = some (stage0ShiftWork sCaps sDem)) :
    Meets w p f ((stage0ShiftSpec w).withCost fun d _ =>
      980 * d.I.m * d.L + 1500 * d.I.m + 450) := by
  have h1 := padCopy_meets (w := w) (by omega) hpCopy
  have h2 := limbsAdd_meets (w := w) hlAdd
  have h3 := limbsSub_meets (w := w) hlSub
  have h4 := limbsCmp_meets (w := w) hw hlCmp
  have h5 := canonLen_meets (w := w) hcLen
  have h6 := accAddLimbs_meets (w := w) (by omega) haccAdd
  have h7 := accNormalize_meets (w := w) haccNorm
  have h8 := stage0ShiftOneCap_meets (w := w)
    (Tpad := fun L => 55 * L + 35) (Tadd := fun L => 50 * L + 30)
    (Tsub := fun L => 60 * L + 30) (Tcan := fun L => 45 * L + 25)
    hsOneCap h1 h2 h3 h5
  have h9 := stage0ShiftOneDem_meets (w := w)
    (Tnorm := fun L => 45 * L + 25) (Tcmp := fun L => 40 * L + 20)
    (Tsub := fun L => 60 * L + 30) (Tcan := fun L => 45 * L + 25)
    hsOneDem h7 h4 h3 h5
  have h10 := stage0ShiftCaps_meets (w := w)
    (T1 := fun L => 2 * (55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (45 * L + 25) + 80)
    hsCaps h8
  have h11 := stage0ShiftDemInit_meets (w := w) (Tacc := fun L => 55 * L + 30)
    (fun _ _ h => by omega) hdInit h6
  have h12 := stage0ShiftDemEdges_meets (w := w) (Tacc := fun L => 55 * L + 30)
    (fun _ _ h => by omega) hdEdges h6
  have h13 := stage0ShiftDemFin_meets (w := w)
    (T1 := fun L => 2 * (45 * L + 25) + (40 * L + 20) + (60 * L + 30) + (45 * L + 25) + 80)
    hdFin h9
  have h14 := stage0ShiftDem_meets (w := w)
    (Tdi := fun cnt L => (55 * L + 30 + 115) * cnt + 40)
    (Tde := fun m L => (2 * (55 * L + 30) + 145) * m + 40)
    (Tdf := fun cnt L => (2 * (45 * L + 25) + (40 * L + 20) + (60 * L + 30) + (45 * L + 25) + 80 + 90) * cnt + 35)
    hsDem h11 h12 h13
  have h15 := stage0ShiftWork_meets (w := w)
    (Tc := fun m L => (2 * (55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (45 * L + 25) + 80 + 110) * m + 40)
    (Td := fun m cnt L =>
      ((55 * L + 30 + 115) * cnt + 40) +
      ((2 * (55 * L + 30) + 145) * m + 40) +
      ((2 * (45 * L + 25) + (40 * L + 20) + (60 * L + 30) + (45 * L + 25) + 80 + 90) * cnt + 35) + 60)
    hsWork h10 h14
  exact (stage0Shift_meets
    (Tw := fun m cnt L =>
      ((2 * (55 * L + 35) + (50 * L + 30) + (60 * L + 30) + (45 * L + 25) + 80 + 110) * m + 40) +
      (((55 * L + 30 + 115) * cnt + 40) +
       ((2 * (55 * L + 30) + 145) * m + 40) +
       ((2 * (45 * L + 25) + (40 * L + 20) + (60 * L + 30) + (45 * L + 25) + 80 + 90) * cnt + 35) + 60) + 80)
    hp h15).withCost_mono fun d _ => by
      have hcnt : (FlowReduction.shiftedGraph d.I d.hv).endpointLabels.count ≤ 2 * d.I.m :=
        Circulation.endpointLabels_count_le (FlowReduction.shiftedGraph d.I d.hv)
      dsimp only
      nlinarith

theorem stage0Shift_meetsO {w : ℕ} {p : Program}
    {f pCopy lAdd lSub lCmp cLen accAdd accNorm sOneCap sOneDem sCaps dInit dEdges dFin sDem sWork : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0Shift sWork))
    (hpCopy : p.procs[pCopy]? = some padCopy)
    (hlAdd : p.procs[lAdd]? = some limbsAdd)
    (hlSub : p.procs[lSub]? = some limbsSub)
    (hlCmp : p.procs[lCmp]? = some limbsCmp)
    (hcLen : p.procs[cLen]? = some canonLen)
    (haccAdd : p.procs[accAdd]? = some accAddLimbs)
    (haccNorm : p.procs[accNorm]? = some accNormalize)
    (hsOneCap : p.procs[sOneCap]? = some (stage0ShiftOneCap pCopy lAdd lSub cLen))
    (hsOneDem : p.procs[sOneDem]? = some (stage0ShiftOneDem accNorm lCmp lSub cLen))
    (hsCaps : p.procs[sCaps]? = some (stage0ShiftCaps sOneCap))
    (hdInit : p.procs[dInit]? = some (stage0ShiftDemInit accAdd))
    (hdEdges : p.procs[dEdges]? = some (stage0ShiftDemEdges accAdd))
    (hdFin : p.procs[dFin]? = some (stage0ShiftDemFin sOneDem))
    (hsDem : p.procs[sDem]? = some (stage0ShiftDem dInit dEdges dFin))
    (hsWork : p.procs[sWork]? = some (stage0ShiftWork sCaps sDem)) :
    MeetsO w p f (stage0ShiftSpec w) fun d _ => d.I.m * (d.L + 1) + 1 :=
  MeetsO.of_meets
    (stage0Shift_meets_direct hw hp hpCopy hlAdd hlSub hlCmp hcLen haccAdd haccNorm
      hsOneCap hsOneDem hsCaps hdInit hdEdges hdFin hsDem hsWork)
    ⟨1500, fun ⟨d, _⟩ => by dsimp only; nlinarith⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage0ShiftMod`, polymorphic over any name type `ι`. -/
structure Stage0ShiftNames (ι : Type) where
  padCopy : ι
  limbsAdd : ι
  limbsSub : ι
  limbsCmp : ι
  canonLen : ι
  accAddLimbs : ι
  accNormalize : ι
  shiftOneCap : ι
  shiftOneDem : ι
  shiftCaps : ι
  shiftDemInit : ι
  shiftDemEdges : ι
  shiftDemFin : ι
  shiftDem : ι
  shiftWork : ι
  stage0Shift : ι

/-- Self-contained polymorphic module for Stage 0 item 3 (`stage0Shift`). -/
def stage0ShiftMod {ι : Type} (names : Stage0ShiftNames ι) : Module ι :=
  ⟨[(names.padCopy, fun _ => padCopy),
    (names.limbsAdd, fun _ => limbsAdd),
    (names.limbsSub, fun _ => limbsSub),
    (names.limbsCmp, fun _ => limbsCmp),
    (names.canonLen, fun _ => canonLen),
    (names.accAddLimbs, fun _ => accAddLimbs),
    (names.accNormalize, fun _ => accNormalize),
    (names.shiftOneCap, fun idx =>
      stage0ShiftOneCap (idx names.padCopy) (idx names.limbsAdd)
        (idx names.limbsSub) (idx names.canonLen)),
    (names.shiftOneDem, fun idx =>
      stage0ShiftOneDem (idx names.accNormalize) (idx names.limbsCmp)
        (idx names.limbsSub) (idx names.canonLen)),
    (names.shiftCaps, fun idx => stage0ShiftCaps (idx names.shiftOneCap)),
    (names.shiftDemInit, fun idx => stage0ShiftDemInit (idx names.accAddLimbs)),
    (names.shiftDemEdges, fun idx => stage0ShiftDemEdges (idx names.accAddLimbs)),
    (names.shiftDemFin, fun idx => stage0ShiftDemFin (idx names.shiftOneDem)),
    (names.shiftDem, fun idx =>
      stage0ShiftDem (idx names.shiftDemInit) (idx names.shiftDemEdges)
        (idx names.shiftDemFin)),
    (names.shiftWork, fun idx =>
      stage0ShiftWork (idx names.shiftCaps) (idx names.shiftDem)),
    (names.stage0Shift, fun idx => stage0Shift (idx names.shiftWork))]⟩

theorem stage0ShiftMod_noRand {ι : Type} (names : Stage0ShiftNames ι) :
    (stage0ShiftMod names).NoRand := by
  wram_no_rand

theorem stage0ShiftMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : Stage0ShiftNames ι} (hw : 2 < 2 ^ w)
    (hp : (stage0ShiftMod names).Placed p idx) :
    MeetsO w p (idx names.stage0Shift) (stage0ShiftSpec w) fun d _ => d.I.m * (d.L + 1) + 1 :=
  stage0Shift_meetsO hw
    (hp.get (n := names.stage0Shift) (b := fun idx =>
      stage0Shift (idx names.shiftWork)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.padCopy) (b := fun _ => padCopy) (by simp [stage0ShiftMod]))
    (hp.get (n := names.limbsAdd) (b := fun _ => limbsAdd) (by simp [stage0ShiftMod]))
    (hp.get (n := names.limbsSub) (b := fun _ => limbsSub) (by simp [stage0ShiftMod]))
    (hp.get (n := names.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage0ShiftMod]))
    (hp.get (n := names.canonLen) (b := fun _ => canonLen) (by simp [stage0ShiftMod]))
    (hp.get (n := names.accAddLimbs) (b := fun _ => accAddLimbs) (by simp [stage0ShiftMod]))
    (hp.get (n := names.accNormalize) (b := fun _ => accNormalize) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftOneCap) (b := fun idx =>
      stage0ShiftOneCap (idx names.padCopy) (idx names.limbsAdd)
        (idx names.limbsSub) (idx names.canonLen)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftOneDem) (b := fun idx =>
      stage0ShiftOneDem (idx names.accNormalize) (idx names.limbsCmp)
        (idx names.limbsSub) (idx names.canonLen)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftCaps) (b := fun idx =>
      stage0ShiftCaps (idx names.shiftOneCap)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftDemInit) (b := fun idx =>
      stage0ShiftDemInit (idx names.accAddLimbs)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftDemEdges) (b := fun idx =>
      stage0ShiftDemEdges (idx names.accAddLimbs)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftDemFin) (b := fun idx =>
      stage0ShiftDemFin (idx names.shiftOneDem)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftDem) (b := fun idx =>
      stage0ShiftDem (idx names.shiftDemInit) (idx names.shiftDemEdges)
        (idx names.shiftDemFin)) (by simp [stage0ShiftMod]))
    (hp.get (n := names.shiftWork) (b := fun idx =>
      stage0ShiftWork (idx names.shiftCaps) (idx names.shiftDem)) (by simp [stage0ShiftMod]))

end MinCostFlow.NarrowProg
