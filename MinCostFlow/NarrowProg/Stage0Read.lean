module

public import WordRAM.Module
public import MinCostFlow.NarrowProg.ReadInt
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.BitScaleFinalize
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring

/-!
# Stage 0, item 1: single-pass input reader (`stage0Read`)

Splits `Assn.list 0 (narrowEncode I)` into its 3-word header `[k, n, m]`, per-edge encoded blocks
`narrowEdgeWords k (I.edge e)` at `edgeStartPos I e.val`, and per-vertex encoded demands
`intWords k (I.d v)` at `demStartPos I v.val` (`list_narrowEncode_split`).

`stage0Read` makes one `O(m + n + 1)` pass with `readInt`, keeping all limb arrays in place inside
`[0, (narrowEncode I).length)` and writing:
- an 11-word record `edgeRec I e` at `pEdges + 11 * e` for each edge `e : Fin I.m`:
  `[tail, head, loSign, loLen, loPtr, hiSign, hiLen, hiPtr, cSign, cLen, cPtr]`;
- a 3-word record `demRec I v` at `pDems + 3 * v` for each vertex `v : Fin I.n`:
  `[dSign, dLen, dPtr]`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Input positions and parsed records -/

/-- Starting address of edge `i` inside `narrowEncode I`. -/
def edgeStartPos (I : Instance) (i : ℕ) : ℕ :=
  3 + ((I.edges.take i).flatMap (narrowEdgeWords (narrowLimbWidth I))).length

/-- Starting address of the `lower` limbs of edge `e`. -/
def edgeLoPtr (I : Instance) (e : Fin I.m) : ℕ :=
  edgeStartPos I e.val + 4

/-- Starting address of `intWords k (I.edge e).upper` inside `narrowEncode I`. -/
def edgeHiPos (I : Instance) (e : Fin I.m) : ℕ :=
  edgeStartPos I e.val + 2 + (intWords (narrowLimbWidth I) (I.edge e).lower).length

/-- Starting address of the `upper` limbs of edge `e`. -/
def edgeHiPtr (I : Instance) (e : Fin I.m) : ℕ :=
  edgeHiPos I e + 2

/-- Starting address of `intWords k (I.edge e).cost` inside `narrowEncode I`. -/
def edgeCostPos (I : Instance) (e : Fin I.m) : ℕ :=
  edgeHiPos I e + (intWords (narrowLimbWidth I) (I.edge e).upper).length

/-- Starting address of the `cost` limbs of edge `e`. -/
def edgeCostPtr (I : Instance) (e : Fin I.m) : ℕ :=
  edgeCostPos I e + 2

/-- Starting address of the demands section inside `narrowEncode I`. -/
def demBasePos (I : Instance) : ℕ :=
  edgeStartPos I I.m

/-- Starting address of demand `v` inside `narrowEncode I`. -/
def demStartPos (I : Instance) (v : ℕ) : ℕ :=
  demBasePos I + ((I.demand.take v).flatMap (intWords (narrowLimbWidth I))).length

/-- Starting address of the demand limbs of vertex `v`. -/
def demPtr (I : Instance) (v : Fin I.n) : ℕ :=
  demStartPos I v.val + 2

/-- The 11-word parsed record for edge `e`:
`[tail, head, loSign, loLen, loPtr, hiSign, hiLen, hiPtr, cSign, cLen, cPtr]`. -/
def edgeRec (I : Instance) (e : Fin I.m) : List ℕ :=
  let k := narrowLimbWidth I
  let ed := I.edge e
  [ed.tail, ed.head,
   if ed.lower < 0 then 1 else 0, (Nat.digits (2 ^ k) ed.lower.natAbs).length, edgeLoPtr I e,
   if ed.upper < 0 then 1 else 0, (Nat.digits (2 ^ k) ed.upper.natAbs).length, edgeHiPtr I e,
   if ed.cost < 0 then 1 else 0, (Nat.digits (2 ^ k) ed.cost.natAbs).length, edgeCostPtr I e]

/-- The 3-word parsed record for vertex `v`: `[dSign, dLen, dPtr]`. -/
def demRec (I : Instance) (v : Fin I.n) : List ℕ :=
  let k := narrowLimbWidth I
  let dv := I.d v
  [if dv < 0 then 1 else 0, (Nat.digits (2 ^ k) dv.natAbs).length, demPtr I v]

/-! ### Position and splitting lemmas -/

theorem edgeStartPos_zero (I : Instance) : edgeStartPos I 0 = 3 := by
  simp [edgeStartPos]

theorem edgeStartPos_succ (I : Instance) (e : Fin I.m) :
    edgeStartPos I (e.val + 1) =
      edgeCostPos I e + (intWords (narrowLimbWidth I) (I.edge e).cost).length := by
  unfold edgeCostPos edgeHiPos edgeStartPos
  have htake : I.edges.take (e.val + 1) = I.edges.take e.val ++ [I.edge e] := by
    rw [List.take_add_one, List.getElem?_eq_getElem e.isLt]; rfl
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.length_append]
  simp only [narrowEdgeWords, List.length_cons, List.length_append]
  omega

theorem edgeStartPos_mono (I : Instance) {i j : ℕ} (hij : i ≤ j) :
    edgeStartPos I i ≤ edgeStartPos I j := by
  unfold edgeStartPos
  have htake : I.edges.take i = (I.edges.take j).take i := by
    rw [List.take_take, Nat.min_eq_left hij]
  have hsplit : I.edges.take j = I.edges.take i ++ (I.edges.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (I.edges.take j), ← htake]
  rw [hsplit, List.flatMap_append, List.length_append]
  omega

theorem demBasePos_le_encode (I : Instance) : demBasePos I ≤ (narrowEncode I).length := by
  unfold demBasePos edgeStartPos narrowEncode Instance.m
  rw [List.take_length]
  simp only [List.length_cons, List.length_append]
  omega

theorem demStartPos_zero (I : Instance) : demStartPos I 0 = demBasePos I := by
  simp [demStartPos]

theorem demStartPos_succ (I : Instance) (hv : I.IsValid) (v : Fin I.n) :
    demStartPos I (v.val + 1) =
      demStartPos I v.val + (intWords (narrowLimbWidth I) (I.d v)).length := by
  unfold demStartPos
  have hv' : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
  have hdv : I.demand[v.val]'hv' = I.d v := (List.getD_eq_getElem _ _ hv').symm
  have htake : I.demand.take (v.val + 1) = I.demand.take v.val ++ [I.d v] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hv', Option.toList_some, hdv]
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.length_append]
  omega

theorem demStartPos_n (I : Instance) (hv : I.IsValid) :
    demStartPos I I.n = (narrowEncode I).length := by
  unfold demStartPos demBasePos edgeStartPos narrowEncode Instance.m
  rw [List.take_length, ← hv.2, List.take_length]
  simp only [List.length_cons, List.length_append]
  omega

theorem demStartPos_mono (I : Instance) {i j : ℕ} (hij : i ≤ j) :
    demStartPos I i ≤ demStartPos I j := by
  unfold demStartPos
  have htake : I.demand.take i = (I.demand.take j).take i := by
    rw [List.take_take, Nat.min_eq_left hij]
  have hsplit : I.demand.take j = I.demand.take i ++ (I.demand.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (I.demand.take j), ← htake]
  rw [hsplit, List.flatMap_append, List.length_append]
  omega

/-- Split `Assn.list base (xs.flatMap f)` into a separating product over `Finset.range xs.length`. -/
theorem list_flatMap_split {α : Type} (base : ℕ) (xs : List α) (f : α → List ℕ) :
    Assn.list base (xs.flatMap f) =
      ∏ i ∈ Finset.range xs.length,
        Assn.list (base + ((xs.take i).flatMap f).length)
          (if h : i < xs.length then f (xs[i]'h) else []) := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
    rw [List.flatMap_append, List.flatMap_singleton, Assn.list_append, ih]
    have hrange : Finset.range (xs ++ [a]).length = Finset.range (xs.length + 1) := by simp
    rw [hrange, Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' : i < xs.length := Finset.mem_range.mp hi
      have htake : (xs ++ [a]).take i = xs.take i := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hi')]
      have hget : (xs ++ [a])[i]'(by simp; omega) = xs[i]'hi' :=
        List.getElem_append_left hi'
      simp [hi', htake, hget, Nat.le_of_lt hi']
    · have htake : (xs ++ [a]).take xs.length = xs := by simp
      have hget : (xs ++ [a])[xs.length]'(by simp) = a := by simp
      simp [htake, hget]

/-- Splitting `Assn.list 0 (narrowEncode I)` into header, per-edge blocks, and per-demand blocks. -/
theorem list_narrowEncode_split (I : Instance) (hv : I.IsValid) :
    Assn.list 0 (narrowEncode I) =
      (0 ↦ narrowLimbWidth I) * (1 ↦ I.n) * (2 ↦ I.m) *
      (∏ i ∈ Finset.range I.m,
        Assn.list (edgeStartPos I i)
          (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else [])) *
      (∏ v ∈ Finset.range I.n,
        Assn.list (demStartPos I v)
          (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else [])) := by
  unfold narrowEncode
  simp only [Assn.list_cons, Assn.list_append, zero_add,
    show (1 : ℕ) + 1 = 2 by omega, show (2 : ℕ) + 1 = 3 by omega, mul_assoc]
  rw [list_flatMap_split 3 I.edges (narrowEdgeWords (narrowLimbWidth I)),
    list_flatMap_split (3 + (I.edges.flatMap (narrowEdgeWords (narrowLimbWidth I))).length)
      I.demand (intWords (narrowLimbWidth I))]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl
    (congrArg₂ (· * ·) ?_ ?_)))
  · refine Finset.prod_congr rfl fun i _ => ?_
    rfl
  · have hbase : 3 + (I.edges.flatMap (narrowEdgeWords (narrowLimbWidth I))).length =
        demBasePos I := by
      unfold demBasePos edgeStartPos Instance.m
      rw [List.take_length]
    rw [hbase]
    refine Finset.prod_congr (by rw [hv.2]) fun v hvlt => ?_
    have hv1 : v < I.n := Finset.mem_range.mp hvlt
    have hv2 : v < I.demand.length := by rw [hv.2]; exact hv1
    have hdv : I.demand[v]'hv2 = I.d v := (List.getD_eq_getElem _ _ hv2).symm
    simp [demStartPos, hv1, hv2, hdv]

/-- Splitting a single encoded edge into its tail, head, lower, upper, and cost blocks. -/
theorem list_narrowEdgeWords (I : Instance) (e : Fin I.m) :
    Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) =
      (edgeStartPos I e.val ↦ (I.edge e).tail) *
      (edgeStartPos I e.val + 1 ↦ (I.edge e).head) *
      Assn.list (edgeStartPos I e.val + 2) (intWords (narrowLimbWidth I) (I.edge e).lower) *
      Assn.list (edgeHiPos I e) (intWords (narrowLimbWidth I) (I.edge e).upper) *
      Assn.list (edgeCostPos I e) (intWords (narrowLimbWidth I) (I.edge e).cost) := by
  unfold narrowEdgeWords edgeCostPos edgeHiPos
  simp only [Assn.list_cons, Assn.list_append, List.length_append, add_assoc, mul_assoc,
    show edgeStartPos I e.val + 1 + 1 = edgeStartPos I e.val + 2 by omega]

/-! ### Heap-splitting helpers -/

private theorem list_split_three_zero (p : ℕ) :
    Assn.list p (List.replicate 3 0) = (p ↦ 0) * (p + 1 ↦ 0) * (p + 2 ↦ 0) := by
  simp only [List.replicate_succ, List.replicate_zero, Assn.list_cons, Assn.list_nil, mul_one,
    mul_assoc, show p + 1 + 1 = p + 2 by omega]

private theorem list_join_three (p a0 a1 a2 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) = Assn.list p [a0, a1, a2] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc, show p + 1 + 1 = p + 2 by omega]

private theorem list_split_eleven_zero (p : ℕ) :
    Assn.list p (List.replicate 11 0) =
      (p ↦ 0) * (p + 1 ↦ 0) * (p + 2 ↦ 0) * (p + 3 ↦ 0) * (p + 4 ↦ 0) *
      (p + 5 ↦ 0) * (p + 6 ↦ 0) * (p + 7 ↦ 0) * (p + 8 ↦ 0) * (p + 9 ↦ 0) * (p + 10 ↦ 0) := by
  simp only [List.replicate_succ, List.replicate_zero, Assn.list_cons, Assn.list_nil, mul_one,
    mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega, show p + 4 + 1 = p + 5 by omega,
    show p + 5 + 1 = p + 6 by omega, show p + 6 + 1 = p + 7 by omega,
    show p + 7 + 1 = p + 8 by omega, show p + 8 + 1 = p + 9 by omega,
    show p + 9 + 1 = p + 10 by omega]

private theorem list_join_eleven (p a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * (p + 3 ↦ a3) * (p + 4 ↦ a4) *
    (p + 5 ↦ a5) * (p + 6 ↦ a6) * (p + 7 ↦ a7) * (p + 8 ↦ a8) * (p + 9 ↦ a9) * (p + 10 ↦ a10) =
      Assn.list p [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega, show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega, show p + 4 + 1 = p + 5 by omega,
    show p + 5 + 1 = p + 6 by omega, show p + 6 + 1 = p + 7 by omega,
    show p + 7 + 1 = p + 8 by omega, show p + 8 + 1 = p + 9 by omega,
    show p + 9 + 1 = p + 10 by omega]

/-! ### Helper 1: `stage0ReadOneEdge` -/

/-- Parse one encoded edge starting at `pos`, writing its 11-word record at `pE` using the
4-word `readInt` buffer `pBuf`, and return the start position of the next edge. -/
wram_def stage0ReadOneEdge (ri : ℕ) (pos, pE, pBuf) {
  mem[pE] := mem[pos]
  mem[pE + 1] := mem[pos + 1]
  nxt := ri(pos + 2, pBuf)
  mem[pE + 2] := mem[pBuf]
  mem[pE + 3] := mem[pBuf + 1]
  mem[pE + 4] := mem[pBuf + 2]
  nxt := ri(nxt, pBuf)
  mem[pE + 5] := mem[pBuf]
  mem[pE + 6] := mem[pBuf + 1]
  mem[pE + 7] := mem[pBuf + 2]
  nxt := ri(nxt, pBuf)
  mem[pE + 8] := mem[pBuf]
  mem[pE + 9] := mem[pBuf + 1]
  mem[pE + 10] := mem[pBuf + 2]
  return nxt
}

/-- Specification of `stage0ReadOneEdge`. -/
def stage0ReadOneEdgeSpec (w : ℕ) : Spec ((I : Instance) × Fin I.m × List ℕ) where
  pre := fun ⟨I, e, buf⟩ args => ⨆ (pE : ℕ) (pBuf : ℕ),
    ⌜args = [edgeStartPos I e.val, pE, pBuf] ∧ buf.length = 4 ∧
      edgeStartPos I (e.val + 1) < 2 ^ w ∧ pE + 11 ≤ 2 ^ w ∧ 10 < 2 ^ w⌝ *
    Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) *
    Assn.list pE (List.replicate 11 0) *
    Assn.list pBuf buf
  post := fun ⟨I, e, _⟩ args v => ⨆ (pE : ℕ) (pBuf : ℕ) (buf' : List ℕ),
    ⌜args = [edgeStartPos I e.val, pE, pBuf] ∧ v = edgeStartPos I (e.val + 1) ∧
      buf'.length = 4⌝ *
    Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) *
    Assn.list pE (edgeRec I e) *
    Assn.list pBuf buf'

theorem stage0ReadOneEdge_meets {w : ℕ} {p : Program} {f ri : ℕ} {Tri : ℕ}
    (hp : p.procs[f]? = some (stage0ReadOneEdge ri))
    (hri : Meets w p ri ((readIntSpec w).withCost fun _ _ => Tri)) :
    Meets w p f ((stage0ReadOneEdgeSpec w).withCost fun _ _ => 3 * Tri + 160) := by
  sep_enter ⟨I, e, buf⟩ with hbuf hpos_lt hpE_lt hw10
  have hk : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hnext := edgeStartPos_succ I e
  have hlo_fit : edgeStartPos I e.val + 2 +
      (intWords (narrowLimbWidth I) (I.edge e).lower).length < 2 ^ w := by
    unfold edgeCostPos edgeHiPos at hnext; omega
  have hhi_fit : edgeHiPos I e +
      (intWords (narrowLimbWidth I) (I.edge e).upper).length < 2 ^ w := by
    unfold edgeCostPos at hnext; omega
  have hcost_fit : edgeCostPos I e +
      (intWords (narrowLimbWidth I) (I.edge e).cost).length < 2 ^ w := by omega
  sep_apply list_narrowEdgeWords I e
  sep_apply list_split_eleven_zero pE
  sep_step; sep_step
  have hlo_pos_lt : edgeStartPos I e.val + 2 < 2 ^ w := by omega
  sep_step from (narrowLimbWidth I, (I.edge e).lower, buf) with _ _ _ _ _
  have hlo_eq : edgeStartPos I e.val + 2 + 2 +
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length = edgeHiPos I e := by
    unfold edgeHiPos; rw [intWords_length]; omega
  rw [hlo_eq] at hnxt; subst nxt
  sep_step; sep_step; sep_step
  sep_step from (narrowLimbWidth I, (I.edge e).upper,
    [if (I.edge e).lower < 0 then 1 else 0,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length,
      edgeStartPos I e.val + 2 + 2, edgeHiPos I e]) with _ _ _ _ _
  have hhi_eq : edgeHiPos I e + 2 +
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length = edgeCostPos I e := by
    unfold edgeCostPos; rw [intWords_length]; omega
  rw [hhi_eq] at hnxt; subst nxt
  sep_step; sep_step; sep_step
  sep_step from (narrowLimbWidth I, (I.edge e).cost,
    [if (I.edge e).upper < 0 then 1 else 0,
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length,
      edgeHiPos I e + 2, edgeCostPos I e]) with _ _ _ _ _
  have hcost_eq : edgeCostPos I e + 2 +
      (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).cost.natAbs).length =
      edgeStartPos I (e.val + 1) := by
    rw [hnext, intWords_length]; omega
  rw [hcost_eq] at hnxt; subst nxt
  sep_step; sep_step; sep_step
  have hloPtr_eq : edgeStartPos I e.val + 2 + 2 = edgeLoPtr I e := by unfold edgeLoPtr; omega
  rw [hloPtr_eq]
  sep_apply list_join_eleven pE
  sep_apply (list_narrowEdgeWords I e).symm
  sep_step

/-! ### Helper 2: `stage0ReadEdges` -/

private def edgeRecPartial (I : Instance) (i j : ℕ) : List ℕ :=
  if h : j < I.m then
    if j < i then edgeRec I ⟨j, h⟩ else List.replicate 11 0
  else []

/-- Parse all `m` edges starting at address `3`, filling `pEdges + 11 * i` for `i < m`,
and return `demBasePos I`. -/
wram_def stage0ReadEdges (oneEdge : ℕ) (pEdges, pBuf, m) {
  pos := 3
  off := 0
  for i in 0 .. m {
    pos := oneEdge(pos, pEdges + off, pBuf)
    off := off + 11
  }
  return pos
}

/-- Specification of `stage0ReadEdges`. -/
def stage0ReadEdgesSpec (w : ℕ) : Spec (Instance × List ℕ) where
  pre := fun (I, buf) args => ⨆ (pEdges : ℕ) (pBuf : ℕ),
    ⌜args = [pEdges, pBuf, I.m] ∧ buf.length = 4 ∧
      demBasePos I < 2 ^ w ∧ pEdges + 11 * I.m ≤ 2 ^ w ∧ 11 * I.m < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (edgeStartPos I i)
        (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else [])) *
    (∏ i ∈ Finset.range I.m, Assn.list (pEdges + i * 11) (List.replicate 11 0)) *
    Assn.list pBuf buf
  post := fun (I, _) args v => ⨆ (pEdges : ℕ) (pBuf : ℕ) (buf' : List ℕ),
    ⌜args = [pEdges, pBuf, I.m] ∧ v = demBasePos I ∧ buf'.length = 4⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (edgeStartPos I i)
        (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else [])) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else [])) *
    Assn.list pBuf buf'

theorem stage0ReadEdges_meets {w : ℕ} {p : Program} {f oneEdge : ℕ} {T1 : ℕ}
    (hp : p.procs[f]? = some (stage0ReadEdges oneEdge))
    (h1 : Meets w p oneEdge ((stage0ReadOneEdgeSpec w).withCost fun _ _ => T1)) :
    Meets w p f ((stage0ReadEdgesSpec w).withCost fun x _ => (T1 + 45) * x.1.m + 40) := by
  sep_enter ⟨I, buf⟩ with hbuf hbase_lt hpE_fit h11m hw10
  have hinit : (∏ i ∈ Finset.range I.m, Assn.list (pEdges + i * 11) (List.replicate 11 0)) =
      (∏ i ∈ Finset.range I.m, Assn.list (pEdges + i * 11) (edgeRecPartial I 0 i)) := by
    refine Finset.prod_congr rfl fun j hj => by simp [edgeRecPartial, Finset.mem_range.mp hj]
  sep_apply hinit
  sep_step; sep_step
  have hpos0 : (3 : ℕ) = edgeStartPos I 0 := (edgeStartPos_zero I).symm
  rw [hpos0]
  sep_for (fun i (b : List ℕ) =>
    ⟨[pEdges, pBuf, I.m, edgeStartPos I i, i * 11, i], i ≤ I.m ∧ b.length = 4,
      (T1 + 30) * (I.m - i) + 10,
      [∏ j ∈ Finset.range I.m,
          Assn.list (edgeStartPos I j)
            (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []),
       ∏ j ∈ Finset.range I.m, Assn.list (pEdges + j * 11) (edgeRecPartial I i j),
       Assn.list pBuf b]⟩) with b
  · have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    let e : Fin I.m := ⟨i, hhi⟩
    have hnext_lt : edgeStartPos I (e.val + 1) < 2 ^ w :=
      lt_of_le_of_lt (edgeStartPos_mono I (by omega : e.val + 1 ≤ I.m)) hbase_lt
    have hpEi_lt : pEdges + i * 11 + 11 ≤ 2 ^ w := by
      have : (i + 1) * 11 ≤ I.m * 11 := Nat.mul_le_mul_right 11 (by omega)
      omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos I j)
        (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (edgeRecPartial I i j))
    have hcur_in : Assn.list (edgeStartPos I i)
          (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else []) =
        Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) := by
      simp [e, hhi]
    have hcur_rec : Assn.list (pEdges + i * 11) (edgeRecPartial I i i) =
        Assn.list (pEdges + i * 11) (List.replicate 11 0) := by
      simp [edgeRecPartial, hhi]
    sep_apply hcur_in
    sep_apply hcur_rec
    generalize hF :
      ((∏ j ∈ (Finset.range I.m).erase i,
          Assn.list (edgeStartPos I j)
            (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else [])) *
       ∏ j ∈ (Finset.range I.m).erase i,
          Assn.list (pEdges + j * 11) (edgeRecPartial I i j)) = F
    sep_apply hF
    sep_step from (⟨I, e, b⟩ : (J : Instance) × Fin J.m × List ℕ) with hpos' hb'
    subst F
    sep_norm
    sep_apply hcur_in.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos I j)
        (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []))).symm
    have hnext_rec : Assn.list (pEdges + i * 11) (edgeRec I e) =
        Assn.list (pEdges + i * 11) (edgeRecPartial I (i + 1) i) := by
      simp [edgeRecPartial, e, hhi]
    have herase_eq : (∏ j ∈ (Finset.range I.m).erase i,
          Assn.list (pEdges + j * 11) (edgeRecPartial I i j)) =
        (∏ j ∈ (Finset.range I.m).erase i,
          Assn.list (pEdges + j * 11) (edgeRecPartial I (i + 1) j)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      congr 1; unfold edgeRecPartial
      split_ifs <;> first | rfl | omega
    sep_apply hnext_rec
    sep_apply herase_eq
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (edgeRecPartial I (i + 1) j))).symm
    have hoff_eq : i * 11 + 11 = (i + 1) * 11 := by ring
    have hoff_lt : i * 11 + 11 < 2 ^ w := by omega
    sep_step
  · have hdone : (∏ j ∈ Finset.range I.m, Assn.list (pEdges + j * 11) (edgeRecPartial I I.m j)) =
        (∏ j ∈ Finset.range I.m,
          Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else [])) := by
      refine Finset.prod_congr rfl fun j hj => by
        have hj' : j < I.m := Finset.mem_range.mp hj
        simp [edgeRecPartial, hj']
    sep_apply hdone
    sep_step

/-! ### Helper 3: `stage0ReadDems` -/

private def demRecPartial (I : Instance) (i j : ℕ) : List ℕ :=
  if h : j < I.n then
    if j < i then demRec I ⟨j, h⟩ else List.replicate 3 0
  else []

/-- Parse all `n` demands starting at `pos = demBasePos I`, filling `pDems + 3 * v` for `v < n`. -/
wram_def stage0ReadDems (ri : ℕ) (pos, pDems, pBuf, n) {
  off := 0
  for v in 0 .. n {
    pos := ri(pos, pBuf)
    mem[pDems + off] := mem[pBuf]
    mem[pDems + off + 1] := mem[pBuf + 1]
    mem[pDems + off + 2] := mem[pBuf + 2]
    off := off + 3
  }
  return pos
}

/-- Specification of `stage0ReadDems`. -/
def stage0ReadDemsSpec (w : ℕ) : Spec ({ I : Instance // I.IsValid } × List ℕ) where
  pre := fun (⟨I, _⟩, buf) args => ⨆ (pDems : ℕ) (pBuf : ℕ),
    ⌜args = [demBasePos I, pDems, pBuf, I.n] ∧ buf.length = 4 ∧
      (narrowEncode I).length < 2 ^ w ∧ pDems + 3 * I.n ≤ 2 ^ w ∧ 3 * I.n < 2 ^ w ∧ 3 < 2 ^ w⌝ *
    (∏ v ∈ Finset.range I.n,
      Assn.list (demStartPos I v)
        (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else [])) *
    (∏ v ∈ Finset.range I.n, Assn.list (pDems + v * 3) (List.replicate 3 0)) *
    Assn.list pBuf buf
  post := fun (⟨I, _⟩, _) args r => ⨆ (pDems : ℕ) (pBuf : ℕ) (buf' : List ℕ),
    ⌜args = [demBasePos I, pDems, pBuf, I.n] ∧ r = (narrowEncode I).length ∧ buf'.length = 4⌝ *
    (∏ v ∈ Finset.range I.n,
      Assn.list (demStartPos I v)
        (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else [])) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if h : v < I.n then demRec I ⟨v, h⟩ else [])) *
    Assn.list pBuf buf'

theorem stage0ReadDems_meets {w : ℕ} {p : Program} {f ri : ℕ} {Tri : ℕ}
    (hp : p.procs[f]? = some (stage0ReadDems ri))
    (hri : Meets w p ri ((readIntSpec w).withCost fun _ _ => Tri)) :
    Meets w p f ((stage0ReadDemsSpec w).withCost fun x _ => (Tri + 85) * x.1.1.n + 35) := by
  sep_enter ⟨⟨I, hv⟩, buf⟩ with hbuf henc_lt hpD_fit h3n hw3
  have hk : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hinit : (∏ v ∈ Finset.range I.n, Assn.list (pDems + v * 3) (List.replicate 3 0)) =
      (∏ v ∈ Finset.range I.n, Assn.list (pDems + v * 3) (demRecPartial I 0 v)) := by
    refine Finset.prod_congr rfl fun j hj => by simp [demRecPartial, Finset.mem_range.mp hj]
  sep_apply hinit
  sep_step
  have hpos0 : demBasePos I = demStartPos I 0 := (demStartPos_zero I).symm
  rw [hpos0]
  sep_for (fun v (b : List ℕ) =>
    ⟨[demStartPos I v, pDems, pBuf, I.n, v * 3, v], v ≤ I.n ∧ b.length = 4,
      (Tri + 70) * (I.n - v) + 10,
      [∏ j ∈ Finset.range I.n,
          Assn.list (demStartPos I j)
            (if _ : j < I.n then intWords (narrowLimbWidth I) (I.d j) else []),
       ∏ j ∈ Finset.range I.n, Assn.list (pDems + j * 3) (demRecPartial I v j),
       Assn.list pBuf b]⟩) with b
  · have hmem : v ∈ Finset.range I.n := Finset.mem_range.mpr hhi
    have hnext : demStartPos I (v + 1) =
        demStartPos I v + (intWords (narrowLimbWidth I) (I.d v)).length :=
      demStartPos_succ I hv ⟨v, hhi⟩
    have hfit : demStartPos I v + (intWords (narrowLimbWidth I) (I.d v)).length < 2 ^ w := by
      have hle : demStartPos I (v + 1) ≤ (narrowEncode I).length := by
        rw [← demStartPos_n I hv]; exact demStartPos_mono I (by omega)
      omega
    have hpDv_fit : pDems + v * 3 + 3 ≤ 2 ^ w := by
      have : (v + 1) * 3 ≤ I.n * 3 := Nat.mul_le_mul_right 3 (by omega)
      omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (demStartPos I j)
        (if _ : j < I.n then intWords (narrowLimbWidth I) (I.d j) else []))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pDems + j * 3) (demRecPartial I v j))
    have hcur_in : Assn.list (demStartPos I v)
          (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else []) =
        Assn.list (demStartPos I v) (intWords (narrowLimbWidth I) (I.d v)) := by simp [hhi]
    have hcur_rec : Assn.list (pDems + v * 3) (demRecPartial I v v) =
        Assn.list (pDems + v * 3) (List.replicate 3 0) := by simp [demRecPartial, hhi]
    sep_apply hcur_in
    sep_apply hcur_rec
    generalize hF :
      ((∏ j ∈ (Finset.range I.n).erase v,
          Assn.list (demStartPos I j)
            (if _ : j < I.n then intWords (narrowLimbWidth I) (I.d j) else [])) *
       ∏ j ∈ (Finset.range I.n).erase v,
          Assn.list (pDems + j * 3) (demRecPartial I v j)) = F
    sep_apply hF
    sep_step from (narrowLimbWidth I, I.d v, b) with _ _ _ _ _
    have hpos_eq : demStartPos I v + 2 +
        (Nat.digits (2 ^ narrowLimbWidth I) (I.d v).natAbs).length = demStartPos I (v + 1) := by
      rw [hnext, intWords_length]; omega
    rw [hpos_eq] at hpos; subst pos
    sep_apply list_split_three_zero (pDems + v * 3)
    sep_step; sep_step; sep_step
    sep_apply list_join_three (pDems + v * 3)
    subst F
    sep_norm
    sep_apply hcur_in.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (demStartPos I j)
        (if _ : j < I.n then intWords (narrowLimbWidth I) (I.d j) else []))).symm
    have hnext_rec : Assn.list (pDems + v * 3)
          [if I.d v < 0 then 1 else 0, (Nat.digits (2 ^ narrowLimbWidth I) (I.d v).natAbs).length,
            demStartPos I v + 2] =
        Assn.list (pDems + v * 3) (demRecPartial I (v + 1) v) := by
      simp [demRecPartial, demRec, demPtr, hhi]
    have herase_eq : (∏ j ∈ (Finset.range I.n).erase v,
          Assn.list (pDems + j * 3) (demRecPartial I v j)) =
        (∏ j ∈ (Finset.range I.n).erase v,
          Assn.list (pDems + j * 3) (demRecPartial I (v + 1) j)) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : j ≠ v := (Finset.mem_erase.mp hj).1
      congr 1; unfold demRecPartial
      split_ifs <;> first | rfl | omega
    sep_apply hnext_rec
    sep_apply herase_eq
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pDems + j * 3) (demRecPartial I (v + 1) j))).symm
    have hoff_eq : v * 3 + 3 = (v + 1) * 3 := by ring
    have hoff_lt : v * 3 + 3 < 2 ^ w := by omega
    sep_step
  · have hdone : (∏ j ∈ Finset.range I.n, Assn.list (pDems + j * 3) (demRecPartial I I.n j)) =
        (∏ j ∈ Finset.range I.n,
          Assn.list (pDems + j * 3) (if h : j < I.n then demRec I ⟨j, h⟩ else [])) := by
      refine Finset.prod_congr rfl fun j hj => by
        have hj' : j < I.n := Finset.mem_range.mp hj
        simp [demRecPartial, hj']
    sep_apply hdone
    rw [demStartPos_n I hv]
    sep_step

/-! ### Top-level `stage0Read` -/

/-- Heap space consumed by `stage0Read`: 4-word `readInt` buffer + `11 * m` edge records +
`3 * n` demand records. -/
def stage0ReadSpace (I : Instance) : ℕ :=
  4 + 11 * I.m + 3 * I.n

private theorem split_free_read {h m n w : ℕ} (hfit : h + (4 + 11 * m + 3 * n) ≤ 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate 4 0) *
      (∏ i ∈ Finset.range m, Assn.list (h + 4 + i * 11) (List.replicate 11 0)) *
      (∏ v ∈ Finset.range n, Assn.list (h + 4 + 11 * m + v * 3) (List.replicate 3 0)) *
      Assn.free (h + 4 + 11 * m + 3 * n) (2 ^ w - (h + 4 + 11 * m + 3 * n)) := by
  have hsplit : 2 ^ w - h =
      4 + (m * 11 + (n * 3 + (2 ^ w - (h + 4 + 11 * m + 3 * n)))) := by omega
  rw [hsplit, Assn.free_add', Assn.free_add', Assn.free_add',
    ← free_mul_eq_prod, ← free_mul_eq_prod]
  simp only [Assn.free, mul_assoc,
    show h + 4 + m * 11 = h + 4 + 11 * m by omega,
    show h + 4 + 11 * m + n * 3 = h + 4 + 11 * m + 3 * n by omega]

/-- Single-pass Stage 0 input reader. Reads `n` and `m` from addresses `1` and `2`, allocates
`pBuf = h`, `pEdges = h + 4`, `pDems = h + 4 + 11 * m`, parses all edges and demands in place,
and returns the new heap pointer `h + 4 + 11 * m + 3 * n`. -/
wram_def stage0Read (rEdges rDems : ℕ) (h) {
  n := mem[1]
  m := mem[2]
  pEdges := h + 4
  pDems := pEdges + 11 * m
  pos := rEdges(pEdges, h, m)
  pos := rDems(pos, pDems, h, n)
  return pDems + 3 * n
}

/-- Specification of `stage0Read`. Preserves `narrowEncode I` unmutated at address `0` and
produces the parsed edge and demand records at `h + 4` and `h + 4 + 11 * I.m`. -/
def stage0ReadSpec (w : ℕ) : Spec { I : Instance // I.IsValid } where
  pre := fun ⟨I, _⟩ args => ⨆ (h : ℕ),
    ⌜args = [h] ∧ (narrowEncode I).length ≤ h ∧
      h + stage0ReadSpace I < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode I) * Assn.free h (2 ^ w - h)
  post := fun ⟨I, _⟩ args h' => ⨆ (h : ℕ),
    let pEdges := h + 4
    let pDems := h + 4 + 11 * I.m
    ⌜args = [h] ∧ h' = h + stage0ReadSpace I⌝ *
    Assn.list 0 (narrowEncode I) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if hlt : i < I.m then edgeRec I ⟨i, hlt⟩ else [])) *
    (∏ v ∈ Finset.range I.n,
      Assn.list (pDems + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
    Assn.free h' (2 ^ w - h')

theorem stage0Read_meets {w : ℕ} {p : Program} {f rEdges rDems : ℕ}
    {Te Td : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0Read rEdges rDems))
    (he : Meets w p rEdges ((stage0ReadEdgesSpec w).withCost fun x _ => Te x.1.m))
    (hd : Meets w p rDems ((stage0ReadDemsSpec w).withCost fun x _ => Td x.1.1.n)) :
    Meets w p f ((stage0ReadSpec w).withCost fun d _ => Te d.1.m + Td d.1.n + 80) := by
  sep_enter ⟨I, hv⟩ with hge hfit hw10
  have hfit' : h + (4 + 11 * I.m + 3 * I.n) < 2 ^ w := hfit
  have henc_lt : (narrowEncode I).length < 2 ^ w := by omega
  have hbase_lt : demBasePos I < 2 ^ w := lt_of_le_of_lt (demBasePos_le_encode I) henc_lt
  have hw11 : 11 < 2 ^ w := by
    have : 4 ≤ w := by
      by_contra hlt
      have : w ≤ 3 := by omega
      interval_cases w <;> omega
    exact lt_of_lt_of_le (by decide : 11 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) this)
  sep_apply list_narrowEncode_split I hv
  sep_apply split_free_read (h := h) (m := I.m) (n := I.n) (w := w) (by omega)
  sep_step; sep_step
  sep_step; sep_step
  subst pDems
  have h11m : 11 * I.m < 2 ^ w := by omega
  have hpE_fit : h + 4 + 11 * I.m ≤ 2 ^ w := by omega
  have h3n : 3 * I.n < 2 ^ w := by omega
  have hpD_fit : h + 4 + 11 * I.m + 3 * I.n ≤ 2 ^ w := by omega
  generalize hF1 :
    ((0 ↦ narrowLimbWidth I) * (1 ↦ I.n) * (2 ↦ I.m) *
     (∏ v ∈ Finset.range I.n,
        Assn.list (demStartPos I v)
          (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else [])) *
     (∏ v ∈ Finset.range I.n, Assn.list (h + 4 + 11 * I.m + v * 3) (List.replicate 3 0)) *
     Assn.free (h + 4 + 11 * I.m + 3 * I.n) (2 ^ w - (h + 4 + 11 * I.m + 3 * I.n))) = F1
  sep_apply hF1
  sep_step from (I, List.replicate 4 0) with hbuf1
  subst F1
  sep_norm
  generalize hF2 :
    ((0 ↦ narrowLimbWidth I) * (1 ↦ I.n) * (2 ↦ I.m) *
     (∏ i ∈ Finset.range I.m,
        Assn.list (edgeStartPos I i)
          (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else [])) *
     (∏ i ∈ Finset.range I.m,
        Assn.list (h + 4 + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else [])) *
     Assn.free (h + 4 + 11 * I.m + 3 * I.n) (2 ^ w - (h + 4 + 11 * I.m + 3 * I.n))) = F2
  sep_apply hF2
  sep_step from (⟨I, hv⟩, buf') with hbuf2
  subst F2
  sep_norm
  sep_apply (list_narrowEncode_split I hv).symm
  have hret_eq : h + 4 + 11 * I.m + 3 * I.n = h + stage0ReadSpace I := by
    dsimp only [stage0ReadSpace]; omega
  sep_step

theorem stage0Read_meets_direct {w : ℕ} {p : Program} {f ri oneEdge rEdges rDems : ℕ}
    (hp : p.procs[f]? = some (stage0Read rEdges rDems))
    (hri : p.procs[ri]? = some readInt)
    (h1 : p.procs[oneEdge]? = some (stage0ReadOneEdge ri))
    (he : p.procs[rEdges]? = some (stage0ReadEdges oneEdge))
    (hd : p.procs[rDems]? = some (stage0ReadDems ri)) :
    Meets w p f ((stage0ReadSpec w).withCost fun d _ => 400 * d.1.m + 150 * d.1.n + 155) := by
  have hriM := readInt_meets (w := w) hri
  have h1M := stage0ReadOneEdge_meets (w := w) h1 hriM
  have heM := stage0ReadEdges_meets (w := w) he h1M
  have hdM := stage0ReadDems_meets (w := w) hd hriM
  exact (stage0Read_meets (Te := fun m => (3 * 65 + 160 + 45) * m + 40)
    (Td := fun n => (65 + 85) * n + 35) hp heM hdM).withCost_mono fun d _ => by omega

theorem stage0Read_meetsO {w : ℕ} {p : Program} {f ri oneEdge rEdges rDems : ℕ}
    (hp : p.procs[f]? = some (stage0Read rEdges rDems))
    (hri : p.procs[ri]? = some readInt)
    (h1 : p.procs[oneEdge]? = some (stage0ReadOneEdge ri))
    (he : p.procs[rEdges]? = some (stage0ReadEdges oneEdge))
    (hd : p.procs[rDems]? = some (stage0ReadDems ri)) :
    MeetsO w p f (stage0ReadSpec w) fun d _ => d.1.m + d.1.n + 1 :=
  MeetsO.of_meets (stage0Read_meets_direct hp hri h1 he hd)
    ⟨400, fun ⟨d, _⟩ => by dsimp only; omega⟩

/-! ### Polymorphic module -/

/-- Procedure names for `stage0ReadMod`, polymorphic over any name type `ι`. -/
structure Stage0ReadNames (ι : Type) where
  readInt : ι
  readOneEdge : ι
  readEdges : ι
  readDems : ι
  stage0Read : ι

/-- Self-contained polymorphic module for Stage 0 item 1 (`stage0Read`). -/
def stage0ReadMod {ι : Type} (names : Stage0ReadNames ι) : Module ι :=
  ⟨[(names.readInt, fun _ => readInt),
    (names.readOneEdge, fun idx => stage0ReadOneEdge (idx names.readInt)),
    (names.readEdges, fun idx => stage0ReadEdges (idx names.readOneEdge)),
    (names.readDems, fun idx => stage0ReadDems (idx names.readInt)),
    (names.stage0Read, fun idx => stage0Read (idx names.readEdges) (idx names.readDems))]⟩

theorem stage0ReadMod_noRand {ι : Type} (names : Stage0ReadNames ι) :
    (stage0ReadMod names).NoRand := by
  wram_no_rand

theorem stage0ReadMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {names : Stage0ReadNames ι} (hp : (stage0ReadMod names).Placed p idx) :
    MeetsO w p (idx names.stage0Read) (stage0ReadSpec w) fun d _ => d.1.m + d.1.n + 1 :=
  stage0Read_meetsO
    (hp.get (n := names.stage0Read) (b := fun idx =>
      stage0Read (idx names.readEdges) (idx names.readDems)) (by simp [stage0ReadMod]))
    (hp.get (n := names.readInt) (b := fun _ => readInt) (by simp [stage0ReadMod]))
    (hp.get (n := names.readOneEdge) (b := fun idx =>
      stage0ReadOneEdge (idx names.readInt)) (by simp [stage0ReadMod]))
    (hp.get (n := names.readEdges) (b := fun idx =>
      stage0ReadEdges (idx names.readOneEdge)) (by simp [stage0ReadMod]))
    (hp.get (n := names.readDems) (b := fun idx =>
      stage0ReadDems (idx names.readInt)) (by simp [stage0ReadMod]))

end MinCostFlow.NarrowProg
