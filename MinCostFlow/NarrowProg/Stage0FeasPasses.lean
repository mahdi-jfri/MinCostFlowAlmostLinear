module

public import MinCostFlow.NarrowProg.Stage0FeasLayout
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 0, item 4 (Passes 1–3): `stage0FeasPass1` and `stage0FeasArtPass`

- `stage0FeasPass1`: scans original edges `i ∈ [0, m)` with positive shifted capacity in `O(m + 1)`.
- `stage0FeasArtPass`: scans vertices `v ∈ [0, n)` once, emitting artificial arcs for `wantSign = 0`
  (positive shifted demand, `(n, v)`) or `wantSign = 1` (negative shifted demand, `(v, n)`), in
  `O(n + 1)` time.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Pass 1 (`stage0FeasPass1`): scan original edges with positive shifted capacity -/

wram_def stage0FeasPass1
    (pEdges, m, pShCapBuf, pShCapLen, L, pTail1, pHead1, pCapPtr1, pCapLen1, pOrigIdx1) {
  j := 0
  for i in 0 .. m {
    if 0 < mem[pShCapLen + i] {
      mem[pTail1 + j] := mem[pEdges + i * 11]
      mem[pHead1 + j] := mem[pEdges + i * 11 + 1]
      mem[pCapPtr1 + j] := pShCapBuf + i * L
      mem[pCapLen1 + j] := mem[pShCapLen + i]
      mem[pOrigIdx1 + j] := i
      j := j + 1
    }
  }
  return j
}

structure Stage0FeasPass1Data where
  I : Instance
  hv : I.IsValid
  L : ℕ
  cap : ℕ

def stage0FeasPass1Spec (w : ℕ) : Spec Stage0FeasPass1Data where
  pre := fun d args => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pOrigIdx1 : ℕ),
    let k := narrowLimbWidth d.I
    ⌜args = [pEdges, d.I.m, pShCapBuf, pShCapLen, d.L, pTail1, pHead1, pCapPtr1, pCapLen1, pOrigIdx1] ∧
      1 ≤ d.L ∧ d.I.m ≤ d.cap ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧
      pShCapBuf + d.I.m * d.L ≤ 2 ^ w ∧ d.I.m * d.L < 2 ^ w ∧
      pShCapLen + d.I.m ≤ 2 ^ w ∧
      pTail1 + d.cap ≤ 2 ^ w ∧ pHead1 + d.cap ≤ 2 ^ w ∧
      pCapPtr1 + d.cap ≤ 2 ^ w ∧ pCapLen1 + d.cap ≤ 2 ^ w ∧ pOrigIdx1 + d.I.m ≤ 2 ^ w ∧
      d.cap < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    Assn.list pTail1 (List.replicate d.cap 0) *
    Assn.list pHead1 (List.replicate d.cap 0) *
    Assn.list pCapPtr1 (List.replicate d.cap 0) *
    Assn.list pCapLen1 (List.replicate d.cap 0) *
    Assn.list pOrigIdx1 (List.replicate d.I.m 0)
  post := fun d args v => ⨆ (pEdges : ℕ) (pShCapBuf : ℕ) (pShCapLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ) (pOrigIdx1 : ℕ),
    let k := narrowLimbWidth d.I
    let orig := feasOrigPos d.I d.hv d.I.m
    ⌜args = [pEdges, d.I.m, pShCapBuf, pShCapLen, d.L, pTail1, pHead1, pCapPtr1, pCapLen1, pOrigIdx1] ∧
      v = orig.length⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else [])) *
    Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) *
    Assn.list pTail1 (orig.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - orig.length) 0) *
    Assn.list pHead1 (orig.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - orig.length) 0) *
    Assn.list pCapPtr1 (orig.map (fun e => pShCapBuf + e.val * d.L) ++ List.replicate (d.cap - orig.length) 0) *
    Assn.list pCapLen1 (orig.map (fun e =>
      (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
      List.replicate (d.cap - orig.length) 0) *
    Assn.list pOrigIdx1 (orig.map Fin.val ++ List.replicate (d.I.m - orig.length) 0)

private theorem feasOrigPos_length_le (I : Instance) (hv : I.IsValid) (i : ℕ) :
    (feasOrigPos I hv i).length ≤ i := by
  unfold feasOrigPos
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem stage0FeasPass1_meets {w : ℕ} {p : Program} {f : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some stage0FeasPass1) :
    Meets w p f ((stage0FeasPass1Spec w).withCost fun d _ => 95 * d.I.m + 40) := by
  sep_enter d with hL1 hmcap hpE h11m hpCap hmL hpLen hpT hpH hpCP hpCL hpOI hcapW
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; omega
  set k := narrowLimbWidth d.I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have h2k : 2 ≤ 2 ^ k := two_le_pow hk1
  sep_step
  sep_for (fun i =>
      let xs := feasOrigPos d.I d.hv i
      ⟨[pEdges, d.I.m, pShCapBuf, pShCapLen, d.L, pTail1, pHead1, pCapPtr1, pCapLen1, pOrigIdx1,
        xs.length, i],
       i ≤ d.I.m,
       80 * (d.I.m - i) + 15,
       [(∏ e ∈ Finset.range d.I.m,
           Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else [])),
        Assn.list pShCapLen (List.ofFn fun e : Fin d.I.m =>
          (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length),
        Assn.list pTail1 (xs.map (fun e => (d.I.edge e).tail) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pHead1 (xs.map (fun e => (d.I.edge e).head) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pCapPtr1 (xs.map (fun e => pShCapBuf + e.val * d.L) ++ List.replicate (d.cap - xs.length) 0),
        Assn.list pCapLen1 (xs.map (fun e =>
          (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
          List.replicate (d.cap - xs.length) 0),
        Assn.list pOrigIdx1 (xs.map Fin.val ++ List.replicate (d.I.m - xs.length) 0)]⟩)
  · have hi : i < d.I.m := hhi
    have hle_j : (feasOrigPos d.I d.hv i).length ≤ i := feasOrigPos_length_le d.I d.hv i
    have hj_lt : (feasOrigPos d.I d.hv i).length < d.cap := by omega
    have hsucc := feasOrigPos_succ d.I d.hv hi
    have hcapLen_lt : i < (List.ofFn fun e : Fin d.I.m =>
        (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length).length := by
      simp; exact hi
    sep_step
    · have hcap_pos : 0 < (FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩ := by
        simp only [List.getElem_ofFn] at hcond
        change 0 < (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩)).length at hcond
        by_contra h0
        have heq : (FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩ = 0 := by omega
        rw [heq] at hcond; simp at hcond
      have hi11 : i * 11 < 11 * d.I.m := by omega
      have hpEi : pEdges + i * 11 + 1 < 2 ^ w := by omega
      have hiL : i * d.L < d.I.m * d.L := Nat.mul_lt_mul_of_pos_right hi (by omega)
      have hpull := (Finset.mul_prod_erase (Finset.range d.I.m)
        (fun e => Assn.list (pEdges + e * 11) (if hlt : e < d.I.m then edgeRec d.I ⟨e, hlt⟩ else []))
        (Finset.mem_range.mpr hi)).symm
      sep_apply hpull
      have hcurE : Assn.list (pEdges + i * 11) (if hlt : i < d.I.m then edgeRec d.I ⟨i, hlt⟩ else []) =
          Assn.list (pEdges + i * 11) (edgeRec d.I ⟨i, hi⟩) := by simp [hi]
      sep_apply hcurE
      have hlen_er : (edgeRec d.I ⟨i, hi⟩).length = 11 := rfl
      have hlen_T : ((feasOrigPos d.I d.hv i).map (fun e => (d.I.edge e).tail) ++
          List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).length = d.cap := by simp; omega
      have hlen_H : ((feasOrigPos d.I d.hv i).map (fun e => (d.I.edge e).head) ++
          List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).length = d.cap := by simp; omega
      have hlen_CP : ((feasOrigPos d.I d.hv i).map (fun e : Fin d.I.m => pShCapBuf + e.val * d.L) ++
          List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).length = d.cap := by simp; omega
      have hlen_CL : ((feasOrigPos d.I d.hv i).map (fun e =>
          (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
          List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).length = d.cap := by simp; omega
      have hlen_OI : ((feasOrigPos d.I d.hv i).map Fin.val ++
          List.replicate (d.I.m - (feasOrigPos d.I d.hv i).length) 0).length = d.I.m := by simp; omega
      have hsucc' : feasOrigPos d.I d.hv (i + 1) = feasOrigPos d.I d.hv i ++ [⟨i, hi⟩] := by
        rw [hsucc, ite_eq_left hcap_pos]
      have hlen_next : (feasOrigPos d.I d.hv (i + 1)).length = (feasOrigPos d.I d.hv i).length + 1 := by
        rw [hsucc']; simp
      have hT : (((feasOrigPos d.I d.hv i).map fun e => (d.I.edge e).tail) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).set
            (feasOrigPos d.I d.hv i).length (d.I.edge ⟨i, hi⟩).tail =
          ((feasOrigPos d.I d.hv (i + 1)).map fun e => (d.I.edge e).tail) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv (i + 1)).length) 0 := by
        have h1 := list_set_append_replicate (xs := (feasOrigPos d.I d.hv i).map fun e => (d.I.edge e).tail)
          (cap := d.cap) (v := (d.I.edge ⟨i, hi⟩).tail) (by simp; exact hj_lt)
        simp only [List.length_map] at h1
        rw [h1, hsucc', List.map_append]; simp
      have hH : (((feasOrigPos d.I d.hv i).map fun e => (d.I.edge e).head) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).set
            (feasOrigPos d.I d.hv i).length (d.I.edge ⟨i, hi⟩).head =
          ((feasOrigPos d.I d.hv (i + 1)).map fun e => (d.I.edge e).head) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv (i + 1)).length) 0 := by
        have h1 := list_set_append_replicate (xs := (feasOrigPos d.I d.hv i).map fun e => (d.I.edge e).head)
          (cap := d.cap) (v := (d.I.edge ⟨i, hi⟩).head) (by simp; exact hj_lt)
        simp only [List.length_map] at h1
        rw [h1, hsucc', List.map_append]; simp
      have hCP : (((feasOrigPos d.I d.hv i).map fun e : Fin d.I.m => pShCapBuf + e.val * d.L) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).set
            (feasOrigPos d.I d.hv i).length (pShCapBuf + i * d.L) =
          ((feasOrigPos d.I d.hv (i + 1)).map fun e : Fin d.I.m => pShCapBuf + e.val * d.L) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv (i + 1)).length) 0 := by
        have h1 := list_set_append_replicate (xs := (feasOrigPos d.I d.hv i).map fun e : Fin d.I.m => pShCapBuf + e.val * d.L)
          (cap := d.cap) (v := pShCapBuf + i * d.L) (by simp; exact hj_lt)
        simp only [List.length_map] at h1
        rw [h1, hsucc', List.map_append]; simp
      have hCL : (((feasOrigPos d.I d.hv i).map fun e =>
              (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv i).length) 0).set
            (feasOrigPos d.I d.hv i).length
            ((Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩)).length) =
          ((feasOrigPos d.I d.hv (i + 1)).map fun e =>
              (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length) ++
            List.replicate (d.cap - (feasOrigPos d.I d.hv (i + 1)).length) 0 := by
        have h1 := list_set_append_replicate
          (xs := (feasOrigPos d.I d.hv i).map fun e =>
            (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity e)).length)
          (cap := d.cap)
          (v := (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩)).length)
          (by simp; exact hj_lt)
        simp only [List.length_map] at h1
        rw [h1, hsucc', List.map_append]; simp
      have hOI : (((feasOrigPos d.I d.hv i).map Fin.val) ++
            List.replicate (d.I.m - (feasOrigPos d.I d.hv i).length) 0).set
            (feasOrigPos d.I d.hv i).length i =
          ((feasOrigPos d.I d.hv (i + 1)).map Fin.val) ++
            List.replicate (d.I.m - (feasOrigPos d.I d.hv (i + 1)).length) 0 := by
        have h1 := list_set_append_replicate (xs := (feasOrigPos d.I d.hv i).map Fin.val)
          (cap := d.I.m) (v := i) (by simp; omega)
        simp only [List.length_map] at h1
        rw [h1, hsucc', List.map_append]; simp
      sep_step; sep_step
      sep_apply hcurE.symm
      sep_apply hpull.symm
      sep_step; sep_step; sep_step
      simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_ofFn,
        hT, hH, hCP, hCL, hOI, hlen_next]
      sep_step
    · have hcap0 : ¬ (0 < (FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩) := by
        simp only [List.getElem_ofFn] at hcond
        change (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩)).length ≤ 0 at hcond
        intro hpos
        have hne : Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩) ≠ [] :=
          (Nat.digits_ne_nil_iff_ne_zero).mpr (by omega)
        have hlen : 0 < (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph d.I d.hv).capacity ⟨i, hi⟩)).length :=
          List.length_pos_iff.mpr hne
        omega
      have hsucc' : feasOrigPos d.I d.hv (i + 1) = feasOrigPos d.I d.hv i := by
        rw [hsucc, ite_eq_right hcap0, List.append_nil]
      simp only [hsucc']
      sep_step
  · sep_step

/-! ### Parameterized artificial-arc scan (`stage0FeasArtPass`) -/

/-- Artificial-arc vertex list selected by `wantSign` (`0` = positive demand, `1` = negative). -/
def feasArtList (I : Instance) (wantSign i : ℕ) : List (Fin I.n) :=
  if wantSign = 0 then feasArtPos I i else feasArtNeg I i

theorem feasArtList_zero (I : Instance) (wantSign : ℕ) : feasArtList I wantSign 0 = [] := by
  unfold feasArtList; split_ifs <;> simp [feasArtPos_zero, feasArtNeg_zero]

theorem feasArtList_succ (I : Instance) {wantSign i : ℕ} (hi : i < I.n) :
    feasArtList I wantSign (i + 1) =
      feasArtList I wantSign i ++
        (if (if wantSign = 0 then 0 < FlowReduction.shiftedDemand I ⟨i, hi⟩
             else FlowReduction.shiftedDemand I ⟨i, hi⟩ < 0)
         then [⟨i, hi⟩] else []) := by
  unfold feasArtList
  by_cases h0 : wantSign = 0
  · simp only [ite_eq_left h0]; exact feasArtPos_succ I hi
  · simp only [ite_eq_right h0]; exact feasArtNeg_succ I hi

theorem feasArtList_length_le (I : Instance) (wantSign i : ℕ) (_hi : i ≤ I.n) :
    (feasArtList I wantSign i).length ≤ (feasArtList I wantSign I.n).length := by
  unfold feasArtList
  have htake : ∀ (P : Fin I.n → Bool),
      (((List.finRange I.n).take i).filter P).length ≤
        (((List.finRange I.n).take I.n).filter P).length := by
    intro P
    have hsplit : (List.finRange I.n).take I.n =
        (List.finRange I.n).take i ++ ((List.finRange I.n).take I.n).drop i := by
      rw [List.take_of_length_le (by simp)]
      exact (List.take_append_drop i (List.finRange I.n)).symm
    rw [hsplit, List.filter_append, List.length_append]
    omega
  split_ifs
  · exact htake _
  · exact htake _

wram_def stage0FeasArtEmit
    (n, v, wantSign, capPtr, capLen, pTail1, pHead1, pCapPtr1, pCapLen1,
     pCostSign1, pCostPtr1, pCostLen1, pOneCells, j) {
  if wantSign == 0 {
    mem[pTail1 + j] := n
    mem[pHead1 + j] := v
  } else {
    mem[pTail1 + j] := v
    mem[pHead1 + j] := n
  }
  mem[pCapPtr1 + j] := capPtr
  mem[pCapLen1 + j] := capLen
  mem[pCostSign1 + j] := 1
  mem[pCostPtr1 + j] := pOneCells + j
  mem[pCostLen1 + j] := 1
  mem[pOneCells + j] := 1
  return 0
}

structure Stage0FeasArtEmitData where
  n : ℕ
  v : ℕ
  wantSign : ℕ
  capPtr : ℕ
  capLen : ℕ
  j : ℕ
  lT : List ℕ
  lH : List ℕ
  lCP : List ℕ
  lCL : List ℕ
  lCS : List ℕ
  lCoP : List ℕ
  lCoL : List ℕ
  lOne : List ℕ

def ArtEmitOk (d : Stage0FeasArtEmitData) (pOneCells w : ℕ) : Prop :=
  d.j < d.lT.length ∧ d.j < d.lH.length ∧ d.j < d.lCP.length ∧ d.j < d.lCL.length ∧
  d.j < d.lCS.length ∧ d.j < d.lCoP.length ∧ d.j < d.lCoL.length ∧ d.j < d.lOne.length ∧
  pOneCells + d.j < 2 ^ w

def stage0FeasArtEmitSpec (w : ℕ) : Spec Stage0FeasArtEmitData where
  pre := fun d args => ⨆ (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    ⌜args = [d.n, d.v, d.wantSign, d.capPtr, d.capLen, pTail1, pHead1, pCapPtr1, pCapLen1,
        pCostSign1, pCostPtr1, pCostLen1, pOneCells, d.j] ∧
      ArtEmitOk d pOneCells w⌝ *
    Assn.list pTail1 d.lT * Assn.list pHead1 d.lH *
    Assn.list pCapPtr1 d.lCP * Assn.list pCapLen1 d.lCL *
    Assn.list pCostSign1 d.lCS * Assn.list pCostPtr1 d.lCoP *
    Assn.list pCostLen1 d.lCoL * Assn.list pOneCells d.lOne
  post := fun d args res => ⨆ (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    ⌜args = [d.n, d.v, d.wantSign, d.capPtr, d.capLen, pTail1, pHead1, pCapPtr1, pCapLen1,
        pCostSign1, pCostPtr1, pCostLen1, pOneCells, d.j] ∧ res = 0⌝ *
    Assn.list pTail1 (d.lT.set d.j (if d.wantSign = 0 then d.n else d.v)) *
    Assn.list pHead1 (d.lH.set d.j (if d.wantSign = 0 then d.v else d.n)) *
    Assn.list pCapPtr1 (d.lCP.set d.j d.capPtr) * Assn.list pCapLen1 (d.lCL.set d.j d.capLen) *
    Assn.list pCostSign1 (d.lCS.set d.j 1) * Assn.list pCostPtr1 (d.lCoP.set d.j (pOneCells + d.j)) *
    Assn.list pCostLen1 (d.lCoL.set d.j 1) * Assn.list pOneCells (d.lOne.set d.j 1)

theorem stage0FeasArtEmit_meets {w : ℕ} {p : Program} {f : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some stage0FeasArtEmit) :
    Meets w p f ((stage0FeasArtEmitSpec w).withCost fun _ _ => 70) := by
  sep_enter d with hok
  obtain ⟨hT, hH, hCP, hCL, hCS, hCoP, hCoL, hOne, hpOne⟩ := hok
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; omega
  sep_step
  · sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
    simp only [stage0FeasArtEmitSpec, Spec.withCost, ite_eq_left hcond]
    sep_step
  · sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
    simp only [stage0FeasArtEmitSpec, Spec.withCost, ite_eq_right hcond]
    sep_step

wram_def stage0FeasArtPass (artEmit : ℕ)
    (pLabels, n, pShDemBuf, pShDemSign, pShDemLen, L,
     pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
     j0, wantSign) {
  j := j0
  for v in 0 .. n {
    if 0 < mem[pLabels + v] {
      if mem[pShDemSign + (mem[pLabels + v] - 1)] == wantSign {
        if 0 < mem[pShDemLen + (mem[pLabels + v] - 1)] {
          dummy := artEmit(n, v, wantSign, pShDemBuf + (mem[pLabels + v] - 1) * L,
            mem[pShDemLen + (mem[pLabels + v] - 1)],
            pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells, j)
          j := j + 1
        }
      }
    }
  }
  return j
}

structure Stage0FeasArtPassData where
  I : Instance
  hv : I.IsValid
  hiso : FlowReduction.isolatedCheck I hv = true
  act : List ℕ
  L : ℕ
  cap : ℕ
  wantSign : ℕ
  tailPre : List ℕ
  headPre : List ℕ
  capPtrPre : List ℕ
  capLenPre : List ℕ
  costSignPre : List ℕ
  costPtrPre : List ℕ
  costLenPre : List ℕ
  onePre : List ℕ

def stage0FeasArtPassSpec (w : ℕ) : Spec Stage0FeasArtPassData where
  pre := fun d args => ⨆ (pLabels : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let j0 := d.tailPre.length
    ⌜args = [pLabels, d.I.n, pShDemBuf, pShDemSign, pShDemLen, d.L,
        pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
        j0, d.wantSign] ∧
      ActiveInv el d.act ∧ 1 ≤ d.L ∧ (d.wantSign = 0 ∨ d.wantSign = 1) ∧
      d.headPre.length = j0 ∧ d.capPtrPre.length = j0 ∧ d.capLenPre.length = j0 ∧
      d.costSignPre.length = j0 ∧ d.costPtrPre.length = j0 ∧ d.costLenPre.length = j0 ∧
      d.onePre.length = j0 ∧
      j0 + (feasArtList d.I d.wantSign d.I.n).length ≤ d.cap ∧
      pLabels + d.I.n ≤ 2 ^ w ∧
      pShDemBuf + el.count * d.L ≤ 2 ^ w ∧ el.count * d.L < 2 ^ w ∧
      pShDemSign + el.count ≤ 2 ^ w ∧ pShDemLen + el.count ≤ 2 ^ w ∧
      pTail1 + d.cap ≤ 2 ^ w ∧ pHead1 + d.cap ≤ 2 ^ w ∧
      pCapPtr1 + d.cap ≤ 2 ^ w ∧ pCapLen1 + d.cap ≤ 2 ^ w ∧
      pCostSign1 + d.cap ≤ 2 ^ w ∧ pCostPtr1 + d.cap ≤ 2 ^ w ∧
      pCostLen1 + d.cap ≤ 2 ^ w ∧ pOneCells + d.cap ≤ 2 ^ w ∧
      d.cap < 2 ^ w ∧ d.I.n < 2 ^ w⌝ *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pTail1 (d.tailPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pHead1 (d.headPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pCapPtr1 (d.capPtrPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pCapLen1 (d.capLenPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pCostSign1 (d.costSignPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pCostPtr1 (d.costPtrPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pCostLen1 (d.costLenPre ++ List.replicate (d.cap - j0) 0) *
    Assn.list pOneCells (d.onePre ++ List.replicate (d.cap - j0) 0)
  post := fun d args res => ⨆ (pLabels : ℕ) (pShDemBuf : ℕ) (pShDemSign : ℕ) (pShDemLen : ℕ)
      (pTail1 : ℕ) (pHead1 : ℕ) (pCapPtr1 : ℕ) (pCapLen1 : ℕ)
      (pCostSign1 : ℕ) (pCostPtr1 : ℕ) (pCostLen1 : ℕ) (pOneCells : ℕ),
    let el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
    let k := narrowLimbWidth d.I
    let j0 := d.tailPre.length
    let xs := feasArtList d.I d.wantSign d.I.n
    ⌜args = [pLabels, d.I.n, pShDemBuf, pShDemSign, pShDemLen, d.L,
        pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
        j0, d.wantSign] ∧
      res = j0 + xs.length⌝ *
    Assn.list pLabels (List.ofFn el.table) *
    Assn.list pShDemSign (List.ofFn fun c : Fin el.count =>
      if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) *
    Assn.list pShDemLen (List.ofFn fun c : Fin el.count =>
      (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) *
    Assn.list pTail1 ((d.tailPre ++ xs.map (fun u => if d.wantSign = 0 then d.I.n else u.val)) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pHead1 ((d.headPre ++ xs.map (fun u => if d.wantSign = 0 then u.val else d.I.n)) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pCapPtr1 ((d.capPtrPre ++ xs.map (fun u => pShDemBuf + (el.table u - 1) * d.L)) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pCapLen1 ((d.capLenPre ++ xs.map (fun u =>
      (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I u).natAbs).length)) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pCostSign1 ((d.costSignPre ++ List.replicate xs.length 1) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pCostPtr1 ((d.costPtrPre ++
      List.ofFn (fun t : Fin xs.length => pOneCells + (j0 + t.val))) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pCostLen1 ((d.costLenPre ++ List.replicate xs.length 1) ++
      List.replicate (d.cap - (j0 + xs.length)) 0) *
    Assn.list pOneCells ((d.onePre ++ List.replicate xs.length 1) ++
      List.replicate (d.cap - (j0 + xs.length)) 0)

private theorem ofFn_succ_ptr (pOneCells j0 n : ℕ) :
    (List.ofFn fun t : Fin n => pOneCells + (j0 + t.val)) ++ [pOneCells + (j0 + n)] =
      List.ofFn fun t : Fin (n + 1) => pOneCells + (j0 + t.val) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.val_castSucc, Fin.val_last]

private theorem artPass_len_map {α : Type} {pre : List ℕ} {xs : List α}
    {f : α → ℕ} {cap j0 : ℕ} (hpre : pre.length = j0) (hj : j0 + xs.length ≤ cap) :
    ((pre ++ xs.map f) ++ List.replicate (cap - (j0 + xs.length)) 0).length = cap := by
  simp only [List.length_append, List.length_map, List.length_replicate, hpre]; omega

private theorem artPass_len_rep {pre : List ℕ} {n cap j0 : ℕ}
    (hpre : pre.length = j0) (hj : j0 + n ≤ cap) :
    ((pre ++ List.replicate n 1) ++ List.replicate (cap - (j0 + n)) 0).length = cap := by
  simp only [List.length_append, List.length_replicate, hpre]; omega

private theorem artPass_len_ptr {pre : List ℕ} {pOneCells n cap j0 : ℕ}
    (hpre : pre.length = j0) (hj : j0 + n ≤ cap) :
    ((pre ++ List.ofFn fun t : Fin n => pOneCells + (j0 + t.val)) ++
      List.replicate (cap - (j0 + n)) 0).length = cap := by
  simp only [List.length_append, List.length_ofFn, List.length_replicate, hpre]; omega

private theorem artPass_set_map {α : Type} {pre : List ℕ} {xs : List α} {a : α}
    {f : α → ℕ} {cap j0 : ℕ} (hpre : pre.length = j0) (hj : j0 + xs.length < cap) :
    ((pre ++ xs.map f) ++ List.replicate (cap - (j0 + xs.length)) 0).set (j0 + xs.length) (f a) =
      (pre ++ (xs ++ [a]).map f) ++ List.replicate (cap - (j0 + (xs ++ [a]).length)) 0 := by
  have h1 := list_set_append_replicate (xs := pre ++ xs.map f) (cap := cap) (v := f a)
    (by simp [hpre]; exact hj)
  simp only [List.length_append, List.length_map, hpre] at h1
  rw [h1, List.map_append]; simp [List.append_assoc, Nat.add_assoc]

private theorem artPass_set_rep {pre : List ℕ} {n cap j0 : ℕ}
    (hpre : pre.length = j0) (hj : j0 + n < cap) :
    ((pre ++ List.replicate n 1) ++ List.replicate (cap - (j0 + n)) 0).set (j0 + n) 1 =
      (pre ++ List.replicate (n + 1) 1) ++ List.replicate (cap - (j0 + (n + 1))) 0 := by
  have h1 := list_set_append_replicate (xs := pre ++ List.replicate n 1) (cap := cap) (v := 1)
    (by simp [hpre]; exact hj)
  simp only [List.length_append, List.length_replicate, hpre] at h1
  rw [h1, List.replicate_succ']; simp [List.append_assoc, Nat.add_assoc]

private theorem artPass_set_ptr {pre : List ℕ} {pOneCells n cap j0 : ℕ}
    (hpre : pre.length = j0) (hj : j0 + n < cap) :
    ((pre ++ List.ofFn fun t : Fin n => pOneCells + (j0 + t.val)) ++
      List.replicate (cap - (j0 + n)) 0).set (j0 + n) (pOneCells + (j0 + n)) =
      (pre ++ List.ofFn fun t : Fin (n + 1) => pOneCells + (j0 + t.val)) ++
        List.replicate (cap - (j0 + (n + 1))) 0 := by
  have h1 := list_set_append_replicate
    (xs := pre ++ List.ofFn fun t : Fin n => pOneCells + (j0 + t.val))
    (cap := cap) (v := pOneCells + (j0 + n)) (by simp [hpre]; exact hj)
  simp only [List.length_append, List.length_ofFn, hpre] at h1
  rw [h1, List.append_assoc pre, ofFn_succ_ptr, Nat.add_assoc]

theorem stage0FeasArtPass_meets {w : ℕ} {p : Program} {f artEmit : ℕ} {Temit : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (stage0FeasArtPass artEmit))
    (hemit : Meets w p artEmit ((stage0FeasArtEmitSpec w).withCost fun _ _ => Temit)) :
    Meets w p f ((stage0FeasArtPassSpec w).withCost fun d _ => (Temit + 115) * d.I.n + 40) := by
  sep_enter d with hact hL1 hws hhL hcpL hclL hcsL hcoL hcolL hoL htot
    hpLab hpDem hcntL hpS hpL hpT hpH hpCP hpCL hpCS hpCoP hpCoL hpOne hcapW hnW
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; omega
  set el := (FlowReduction.shiftedGraph d.I d.hv).endpointLabels
  set k := narrowLimbWidth d.I
  set j0 := d.tailPre.length
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth d.I
  have h2k : 2 ≤ 2 ^ k := two_le_pow hk1
  generalize hLabL : List.ofFn el.table = labL
  generalize hSignL : (List.ofFn fun c : Fin el.count =>
    if activeShiftedDemand d.I d.act c.val < 0 then 1 else 0) = signL
  generalize hLenL : (List.ofFn fun c : Fin el.count =>
    (Nat.digits (2 ^ k) (activeShiftedDemand d.I d.act c.val).natAbs).length) = lenL
  have hlabL_len : labL.length = d.I.n := by rw [← hLabL]; simp
  have hsignL_len : signL.length = el.count := by rw [← hSignL]; simp
  have hlenL_len : lenL.length = el.count := by rw [← hLenL]; simp
  sep_step
  sep_for (fun v (dum : ℕ) =>
      let xs := feasArtList d.I d.wantSign v
      ⟨[pLabels, d.I.n, pShDemBuf, pShDemSign, pShDemLen, d.L,
        pTail1, pHead1, pCapPtr1, pCapLen1, pCostSign1, pCostPtr1, pCostLen1, pOneCells,
        j0, d.wantSign, j0 + xs.length, v, dum],
       v ≤ d.I.n,
       (Temit + 100) * (d.I.n - v) + 15,
       [Assn.list pLabels labL,
        Assn.list pShDemSign signL,
        Assn.list pShDemLen lenL,
        Assn.list pTail1 ((d.tailPre ++ xs.map (fun u => if d.wantSign = 0 then d.I.n else u.val)) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pHead1 ((d.headPre ++ xs.map (fun u => if d.wantSign = 0 then u.val else d.I.n)) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pCapPtr1 ((d.capPtrPre ++ xs.map (fun u => pShDemBuf + (el.table u - 1) * d.L)) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pCapLen1 ((d.capLenPre ++ xs.map (fun u =>
          (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I u).natAbs).length)) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pCostSign1 ((d.costSignPre ++ List.replicate xs.length 1) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pCostPtr1 ((d.costPtrPre ++
          List.ofFn (fun t : Fin xs.length => pOneCells + (j0 + t.val))) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pCostLen1 ((d.costLenPre ++ List.replicate xs.length 1) ++
          List.replicate (d.cap - (j0 + xs.length)) 0),
        Assn.list pOneCells ((d.onePre ++ List.replicate xs.length 1) ++
          List.replicate (d.cap - (j0 + xs.length)) 0)]⟩)
    with dum0
  · have hv_lt : v < d.I.n := hhi
    have hsucc := feasArtList_succ d.I hv_lt (wantSign := d.wantSign)
    have hlab_len : v < labL.length := by omega
    have hlab_get : labL[v]'hlab_len = el.table ⟨v, hv_lt⟩ := by
      subst labL; simp
    sep_step
    · rw [hlab_get] at hcond
      obtain ⟨hc_lt, hdem_eq0⟩ := activeShiftedDemand_of_label_pos hact (v := ⟨v, hv_lt⟩) hcond
      have hdem_eq : activeShiftedDemand d.I d.act (el.table ⟨v, hv_lt⟩ - 1) =
          FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ := hdem_eq0
      have hcL : (el.table ⟨v, hv_lt⟩ - 1) * d.L < el.count * d.L :=
        Nat.mul_lt_mul_of_pos_right hc_lt (by omega)
      have hsign_len : labL[v]'hlab_len - 1 < signL.length := by rw [hlab_get, hsignL_len]; exact hc_lt
      have hdemlen_len : labL[v]'hlab_len - 1 < lenL.length := by rw [hlab_get, hlenL_len]; exact hc_lt
      have hsign_get : signL[labL[v]'hlab_len - 1]'hsign_len =
          if FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ < 0 then 1 else 0 := by
        subst signL; simp only [List.getElem_ofFn, hlab_get, hdem_eq]
      have hdemlen_get : lenL[labL[v]'hlab_len - 1]'hdemlen_len =
          (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩).natAbs).length := by
        subst lenL; simp only [List.getElem_ofFn, hlab_get, hdem_eq]
      sep_step
      · rw [hsign_get] at hcond_1
        sep_step
        · rw [hdemlen_get] at hcond_2
          have hdem_ne : FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ ≠ 0 := by
            intro h0; rw [h0] at hcond_2; simp at hcond_2
          have hcond_art : if d.wantSign = 0 then 0 < FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩
              else FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ < 0 := by
            rcases hws with h0 | h1
            · rw [ite_eq_left h0]; rw [h0] at hcond_1; split_ifs at hcond_1; omega
            · rw [ite_eq_right (by omega)]; rw [h1] at hcond_1; split_ifs at hcond_1; omega
          have hsucc' : feasArtList d.I d.wantSign (v + 1) =
              feasArtList d.I d.wantSign v ++ [⟨v, hv_lt⟩] := by
            rw [hsucc, ite_eq_left hcond_art]
          have hlen_next : (feasArtList d.I d.wantSign (v + 1)).length =
              (feasArtList d.I d.wantSign v).length + 1 := by
            rw [hsucc']; simp
          have hj_lt : j0 + (feasArtList d.I d.wantSign v).length < d.cap := by
            have := feasArtList_length_le d.I d.wantSign (v + 1) (by omega)
            omega
          have hj_le : j0 + (feasArtList d.I d.wantSign v).length ≤ d.cap := Nat.le_of_lt hj_lt
          have hcL' : (labL[v]'hlab_len - 1) * d.L < el.count * d.L := by
            rw [hlab_get]; exact hcL
          have hlab_pos' : 1 ≤ labL[v]'hlab_len := by rw [hlab_get]; omega
          have hpOne_j : pOneCells + (j0 + (feasArtList d.I d.wantSign v).length) < 2 ^ w := by omega
          have hj1_w : j0 + (feasArtList d.I d.wantSign v).length + 1 < 2 ^ w := by omega
          let ed : Stage0FeasArtEmitData :=
            ⟨d.I.n, v, d.wantSign, pShDemBuf + (labL[v]'hlab_len - 1) * d.L,
              lenL[labL[v]'hlab_len - 1]'hdemlen_len, j0 + (feasArtList d.I d.wantSign v).length,
              (d.tailPre ++ (feasArtList d.I d.wantSign v).map (fun u : Fin d.I.n => if d.wantSign = 0 then d.I.n else u.val)) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.headPre ++ (feasArtList d.I d.wantSign v).map (fun u : Fin d.I.n => if d.wantSign = 0 then u.val else d.I.n)) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.capPtrPre ++ (feasArtList d.I d.wantSign v).map (fun u : Fin d.I.n => pShDemBuf + (el.table u - 1) * d.L)) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.capLenPre ++ (feasArtList d.I d.wantSign v).map (fun u : Fin d.I.n =>
                (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I u).natAbs).length)) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.costSignPre ++ List.replicate (feasArtList d.I d.wantSign v).length 1) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.costPtrPre ++ List.ofFn (fun t : Fin (feasArtList d.I d.wantSign v).length => pOneCells + (j0 + t.val))) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.costLenPre ++ List.replicate (feasArtList d.I d.wantSign v).length 1) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0,
              (d.onePre ++ List.replicate (feasArtList d.I d.wantSign v).length 1) ++
                List.replicate (d.cap - (j0 + (feasArtList d.I d.wantSign v).length)) 0⟩
          have hok : ArtEmitOk ed pOneCells w :=
            ⟨(artPass_len_map rfl hj_le).symm ▸ hj_lt,
             (artPass_len_map hhL hj_le).symm ▸ hj_lt,
             (artPass_len_map hcpL hj_le).symm ▸ hj_lt,
             (artPass_len_map hclL hj_le).symm ▸ hj_lt,
             (artPass_len_rep hcsL hj_le).symm ▸ hj_lt,
             (artPass_len_ptr hcoL hj_le).symm ▸ hj_lt,
             (artPass_len_rep hcolL hj_le).symm ▸ hj_lt,
             (artPass_len_rep hoL hj_le).symm ▸ hj_lt,
             hpOne_j⟩
          clear hdem_eq0 hdem_eq hc_lt hcL hdem_ne hcond_art hsucc hcond hcond_1 hcond_2
          sep_step from ed
          dsimp only [ed]
          rw [hdemlen_get, hlab_get,
            artPass_set_map (f := fun u : Fin d.I.n => if d.wantSign = 0 then d.I.n else u.val) (a := ⟨v, hv_lt⟩) rfl hj_lt,
            artPass_set_map (f := fun u : Fin d.I.n => if d.wantSign = 0 then u.val else d.I.n) (a := ⟨v, hv_lt⟩) hhL hj_lt,
            artPass_set_map (f := fun u : Fin d.I.n => pShDemBuf + (el.table u - 1) * d.L) (a := ⟨v, hv_lt⟩) hcpL hj_lt,
            artPass_set_map (f := fun u : Fin d.I.n => (Nat.digits (2 ^ k) (FlowReduction.shiftedDemand d.I u).natAbs).length)
              (a := ⟨v, hv_lt⟩) hclL hj_lt,
            artPass_set_rep hcsL hj_lt, artPass_set_ptr hcoL hj_lt,
            artPass_set_rep hcolL hj_lt, artPass_set_rep hoL hj_lt,
            ← hsucc', ← hlen_next]
          sep_step
        · rw [hdemlen_get] at hcond_2
          have hdem0 : FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ = 0 := by
            by_contra hne
            have hne' : (FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩).natAbs ≠ 0 := by omega
            have hdne := (Nat.digits_ne_nil_iff_ne_zero (b := 2 ^ k)).mpr hne'
            have hpos := List.length_pos_iff.mpr hdne
            omega
          have hcond_f : ¬ (if d.wantSign = 0 then 0 < FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩
              else FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ < 0) := by
            rw [hdem0]; split_ifs <;> omega
          have hsucc' : feasArtList d.I d.wantSign (v + 1) = feasArtList d.I d.wantSign v := by
            rw [hsucc, ite_eq_right hcond_f, List.append_nil]
          rw [hsucc']
          sep_step
      · rw [hsign_get] at hcond_1
        have hcond_f : ¬ (if d.wantSign = 0 then 0 < FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩
            else FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ < 0) := by
          rcases hws with h0 | h1
          · rw [ite_eq_left h0]; rw [h0] at hcond_1; split_ifs at hcond_1 <;> omega
          · rw [ite_eq_right (by omega)]; rw [h1] at hcond_1; split_ifs at hcond_1 <;> omega
        have hsucc' : feasArtList d.I d.wantSign (v + 1) = feasArtList d.I d.wantSign v := by
          rw [hsucc, ite_eq_right hcond_f, List.append_nil]
        rw [hsucc']
        sep_step
    · rw [hlab_get] at hcond
      have hdem0 : FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ = 0 := by
        by_contra hne
        have hp : 0 < el.table ⟨v, hv_lt⟩ := FlowReduction.shiftedDemand_support d.I d.hv d.hiso ⟨v, hv_lt⟩ hne
        omega
      have hcond_f : ¬ (if d.wantSign = 0 then 0 < FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩
          else FlowReduction.shiftedDemand d.I ⟨v, hv_lt⟩ < 0) := by
        rw [hdem0]; split_ifs <;> omega
      have hsucc' : feasArtList d.I d.wantSign (v + 1) = feasArtList d.I d.wantSign v := by
        rw [hsucc, ite_eq_right hcond_f, List.append_nil]
      rw [hsucc']
      sep_step
  · subst labL signL lenL
    sep_step
  all_goals simp [feasArtList_zero]

end MinCostFlow.NarrowProg
