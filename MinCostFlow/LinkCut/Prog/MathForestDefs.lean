module

public import MinCostFlow.LinkCut.Prog.SplayAccess
public import MinCostFlow.Rounding.DynForest
public import WordRAM.DataStructure
import Mathlib.Data.List.Perm.Basic

/-!
# Memory layout, representation invariant, and Word-RAM `DSRep` for `MathForest`

This file defines the concrete memory representation (`LctMemRep`), footprint, and
potential (`lctPhi`) packaged into `lctDSRep : WordRAM.DSRep MathForest` for deterministic
`L`-limb Link-Cut trees on `MathForest` (van den Brand et al., `arXiv:2309.16629v1`,
Lemma 4.1 on p. 13, from [KangP15] Section 4).

## Header and arena layout from handle `b`
With handle `b` and vertex count `n`, `lctNodesBase b := b + 6` and `lctCap n := 2 * n`:
- `b + 0 = nb - 6`: `n` (number of vertices `0 .. n - 1`, stored at node IDs `1 .. n`)
- `b + 1 = nb - 5`: `cap = 2 * n` (free/active edge slots occupy `n + 1 .. 2 * n`)
- `b + 2 = nb - 4`: `freeHead` (head of singly linked free slot stack via `OFF_EU`, `0` = empty)
- `b + 3 = nb - 3`: `L` (limb count of fixed-point / integer `Num` values; read by `SplayProcs`)
- `b + 4 = nb - 2`: `P` (fixed-point binary precision bits: rationals stored as `N / 2 ^ P`)
- `b + 5 = nb - 1`: `hp` (bump heap pointer above `lctArenaHi b (2 * n)`)
- `[nb, lctArenaHi b (2 * n))`: `2 * n + 1` splay-node records of stride `NODE_STRIDE = 30`.

## Amortized potential and footprint locality
The potential is `lctPhi L mem b n := splayMemPhi (K_SPLAY_STEP L) mem nb cap (lctVSize ...) +
C_HEAVY L * lctHeavyCount mem nb cap`, directly matching `splayForest_runs`.
To keep `lctDSRep.Local` exact even when callers allocate in gaps between operations, `LctConc`
records allocated half-open intervals `regions` covering `[b, lctArenaHi b cap)` and every
live `L`-limb `Num` block without requiring `ZeroFrom mem (mem (nb - 1))` between calls.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ConstantsAndLayout

/-- Header offset storing vertex count `n`. -/
def LCT_HDR_N : ℕ := 0
/-- Header offset storing total node capacity `cap = 2 * n`. -/
def LCT_HDR_CAP : ℕ := 1
/-- Header offset storing head of the free edge-slot stack (linked via `OFF_EU`). -/
def LCT_HDR_FREE : ℕ := 2
/-- Header offset storing limb count `L` (`nb - 3`). -/
def LCT_HDR_L : ℕ := 3
/-- Header offset storing fixed-point precision `P` (`nb - 2`). -/
def LCT_HDR_P : ℕ := 4
/-- Header offset storing bump heap pointer `hp` (`nb - 1`). -/
def LCT_HDR_HP : ℕ := 5
/-- Number of header words before `nodesBase`. -/
def LCT_HDR_SIZE : ℕ := 6

/-- Base address of the node array `nodes[0 .. cap]` from handle `b`. -/
def lctNodesBase (b : ℕ) : ℕ := b + LCT_HDR_SIZE

/-- Node capacity `2 * n`: vertex IDs `1 .. n`, edge subdivision IDs `n + 1 .. 2 * n`. -/
def lctCap (n : ℕ) : ℕ := 2 * n

/-- Exclusive upper bound of the header + node array `[b, lctArenaHi b cap)`. -/
def lctArenaHi (b cap : ℕ) : ℕ := lctNodesBase b + NODE_STRIDE * (cap + 1)

/-- Total static arena size in words starting at handle `b`. -/
def lctArenaWords (n : ℕ) : ℕ := LCT_HDR_SIZE + NODE_STRIDE * (lctCap n + 1)

/-- Node fields storing pointer addresses into heap `Num` blocks (or `0`). -/
def ptrOffs : List ℕ :=
  [OFF_FLOW_PTR, OFF_AF_PTR, OFF_AB_PTR, OFF_COST_FWD, OFF_COST_BWD,
   OFF_CSUM_FWD, OFF_CSUM_BWD, OFF_TAG_PTR, OFF_MIN1_VAL, OFF_MIN2_VAL]

/-- Potential credit per heavy dashed edge (absorbs one heavy splice iteration + `pull`). -/
def C_HEAVY (L : ℕ) : ℕ := C_SPLAY_CONST L + K_PULL L + 4 * L + 500

/-- Constant factor for deterministic `O(n)` initialization (`initCost ≤ C_LCT_INIT * (n + 1)`). -/
def C_LCT_INIT : ℕ := 2000

/-- Constant factor for `O((L + 1) * (Nat.log 2 (n + 2) + 1))` amortized operation cost. -/
def C_LCT_OP : ℕ := 200000

/-- Worst-case heap + arena constant factor (`space ≤ C_LCT_SPACE * (L + 1) * ...`). -/
def C_LCT_SPACE : ℕ := 500

theorem lctNodesBase_ge3 (b : ℕ) : 3 ≤ lctNodesBase b := by
  unfold lctNodesBase LCT_HDR_SIZE; omega

theorem lctArenaHi_eq (b cap : ℕ) : b + (LCT_HDR_SIZE + NODE_STRIDE * (cap + 1)) = lctArenaHi b cap := by
  unfold lctArenaHi lctNodesBase; omega

theorem b_lt_lctArenaHi (b cap : ℕ) : b < lctArenaHi b cap := by
  unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega

theorem lctArenaWords_eq (b n : ℕ) : b + lctArenaWords n = lctArenaHi b (lctCap n) := by
  unfold lctArenaWords lctArenaHi lctNodesBase LCT_HDR_SIZE; omega

theorem c_heavy_le (L : ℕ) : C_HEAVY L ≤ 8200 * (L + 1) := by
  unfold C_HEAVY C_SPLAY_CONST K_PULL
  omega

end ConstantsAndLayout

section FixedPointAndSteps

/-- Decode an `L`-limb fixed-point rational `intVal mem a h L / 2 ^ P`. -/
def fixRat (mem : ℕ → ℕ) (a h L P : ℕ) : ℚ :=
  (intVal mem a h L : ℚ) / ((2 : ℚ) ^ P)

theorem fixRat_eq_fixVal (mem : ℕ → ℕ) (a h L P : ℕ) :
    ((fixRat mem a h L P : ℚ) : ℝ) = fixVal mem a h L P := by
  simp [fixRat, fixVal]

/-- A rational `q` fits in `L`-limb two's-complement fixed-point with precision `P`. -/
def IsFixedFit (h L P : ℕ) (q : ℚ) : Prop :=
  ∃ k : ℤ, Fits h L k ∧ q = (k : ℚ) / ((2 : ℚ) ^ P)

/-- Extract the numerator `q * 2 ^ P` as an integer. -/
def fixedNum (P : ℕ) (q : ℚ) : ℤ :=
  (q * ((2 : ℚ) ^ P)).num

theorem fixedNum_eq {h L P : ℕ} {q : ℚ} (hq : IsFixedFit h L P q) :
    Fits h L (fixedNum P q) ∧ q = (fixedNum P q : ℚ) / ((2 : ℚ) ^ P) := by
  rcases hq with ⟨k, hk_fit, rfl⟩
  have h2p : ((2 : ℚ) ^ P) ≠ 0 := by positivity
  have hmul : ((k : ℚ) / ((2 : ℚ) ^ P)) * ((2 : ℚ) ^ P) = (k : ℚ) := by
    field_simp
  have hnum : fixedNum P ((k : ℚ) / ((2 : ℚ) ^ P)) = k := by
    unfold fixedNum
    rw [hmul]
    exact Rat.num_intCast k
  rw [hnum]
  exact ⟨hk_fit, rfl⟩

/-- An edge of `MathForest` fits when its cost fits as an `L`-limb integer and its
flow, forward availability, and backward availability fit as `L`-limb fixed-point values. -/
def EdgeFits (h L P : ℕ) (e : ForestEdge) : Prop :=
  Fits h L e.cost ∧
  IsFixedFit h L P e.flow ∧
  IsFixedFit h L P e.availFwd ∧
  IsFixedFit h L P e.availBwd

/-- Convert a decoded `RawStep` into a `PathStep` over edge `e`. -/
def RawStep.toPathStep (e : ForestEdge) (s : RawStep) : PathStep :=
  { edge := e, fwd := s.fwd }

/-- Exact match between a decoded `RawStep` `s` at node `ed` and edge `e : ForestEdge`. -/
def stepMatchesEdge (P : ℕ) (ed : ℕ) (e : ForestEdge) (s : RawStep) : Prop :=
  s.nodeId = ed ∧
  s.eid = e.eid ∧
  s.eu = e.u ∧
  s.ev = e.v ∧
  s.cost = e.cost ∧
  (s.flow : ℚ) / ((2 : ℚ) ^ P) = e.flow ∧
  (s.availFwd : ℚ) / ((2 : ℚ) ^ P) = e.availFwd ∧
  (s.availBwd : ℚ) / ((2 : ℚ) ^ P) = e.availBwd

theorem stepMatchesEdge_signedCost {P ed : ℕ} {e : ForestEdge} {s : RawStep}
    (hm : stepMatchesEdge P ed e s) :
    s.signedCost = (s.toPathStep e).signedCost := by
  rcases hm with ⟨_, _, _, _, hcost, _, _, _⟩
  cases hdir : s.fwd <;> simp [RawStep.signedCost, PathStep.signedCost, RawStep.toPathStep, hcost, hdir]

theorem stepMatchesEdge_dirAvail {P ed : ℕ} {e : ForestEdge} {s : RawStep}
    (hm : stepMatchesEdge P ed e s) :
    (s.dirAvail : ℚ) / ((2 : ℚ) ^ P) = (s.toPathStep e).dirAvail := by
  rcases hm with ⟨_, _, _, _, _, _, haf, hab⟩
  cases hf : s.fwd <;> simp [RawStep.dirAvail, PathStep.dirAvail, RawStep.toPathStep, hf, haf, hab]

theorem stepMatchesEdge_flip {P ed : ℕ} {e : ForestEdge} {s : RawStep}
    (hm : stepMatchesEdge P ed e s) :
    stepMatchesEdge P ed e s.flip := by
  simpa [stepMatchesEdge, RawStep.flip] using hm

theorem stepMatchesEdge_addFlow {P ed : ℕ} {e : ForestEdge} {s : RawStep} {d : ℤ} {δ : ℚ}
    (hm : stepMatchesEdge P ed e s) (hδ : δ = (d : ℚ) / ((2 : ℚ) ^ P)) :
    stepMatchesEdge P ed (e.addFlow s.fwd δ) (s.addDelta d) := by
  rcases hm with ⟨hn, heid, heu, hev, hcost, hf, haf, hab⟩
  cases hdir : s.fwd
  · simp only [stepMatchesEdge, RawStep.addDelta, ForestEdge.addFlow, hdir, Bool.false_eq_true,
      ↓reduceIte, hn, heid, heu, hev, hcost, hδ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hf, Int.cast_sub, sub_div]
    · rw [← haf, Int.cast_add, add_div]
    · rw [← hab, Int.cast_sub, sub_div]
  · simp only [stepMatchesEdge, RawStep.addDelta, ForestEdge.addFlow, hdir,
      ↓reduceIte, hn, heid, heu, hev, hcost, hδ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hf, Int.cast_add, add_div]
    · rw [← haf, Int.cast_sub, sub_div]
    · rw [← hab, Int.cast_add, add_div]

theorem intVal_agree_block {mem₁ mem₂ : ℕ → ℕ} {a h L : ℕ}
    (hag : ∀ i < L, mem₂ (a + i) = mem₁ (a + i)) :
    intVal mem₂ a h L = intVal mem₁ a h L := by
  have hu : ∀ L a, (∀ i < L, mem₂ (a + i) = mem₁ (a + i)) →
      unsignedVal mem₂ a h L = unsignedVal mem₁ a h L := by
    intro L
    induction L with
    | zero => intro _ _; rfl
    | succ k ih =>
        intro a hk
        have h0 : mem₂ a = mem₁ a := by simpa using hk 0 (Nat.zero_lt_succ k)
        simp only [unsignedVal]
        rw [h0, ih (a + 1) (fun i hi => by
          simpa [Nat.add_assoc, Nat.add_comm 1 i] using hk (i + 1) (by omega))]
  simp [intVal, hu L a hag]

theorem valid_agree_block {mem₁ mem₂ : ℕ → ℕ} {a h L : ℕ}
    (hag : ∀ i < L, mem₂ (a + i) = mem₁ (a + i))
    (hv : MinCostFlow.Num.Valid mem₁ a h L) :
    MinCostFlow.Num.Valid mem₂ a h L :=
  fun i hi => by rw [hag i hi]; exact hv i hi

theorem fixRat_agree_block {mem₁ mem₂ : ℕ → ℕ} {a h L P : ℕ}
    (hag : ∀ i < L, mem₂ (a + i) = mem₁ (a + i)) :
    fixRat mem₂ a h L P = fixRat mem₁ a h L P := by
  simp [fixRat, intVal_agree_block hag]

theorem RawStep.nodeId_flip (s : RawStep) : s.flip.nodeId = s.nodeId := rfl

theorem RawStep.nodeId_addDeltaMod (h L : ℕ) (s : RawStep) (δ : ℤ) :
    (s.addDeltaMod h L δ).nodeId = s.nodeId := by
  unfold RawStep.addDeltaMod
  split_ifs <;> rfl

theorem evalMemSteps_map_nodeId (mem : ℕ → ℕ) (nb h L : ℕ) (t : AuxTree) (b : Bool) (δ : ℤ) :
    (evalMemSteps mem nb h L t b δ).map RawStep.nodeId =
      (t.evalInorder (revFlag mem nb) b).filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) := by
  induction t generalizing b δ with
  | leaf => simp [evalMemSteps, AuxTree.evalInorder]
  | node x l r ihl ihr =>
      by_cases h0 : nodeField mem nb x OFF_HASE = 0
      · have hown0 : nodeOwnRawStep mem nb h L x = none := by simp [nodeOwnRawStep, h0]
        cases b
        · simp only [evalMemSteps, AuxTree.evalInorder, Bool.false_eq_true, ↓reduceIte,
            hown0, Option.map_none, Option.toList_none, List.append_nil,
            List.map_append, List.filter_append, List.filter_cons, List.filter_nil,
            Bool.false_xor, h0, ne_eq, not_true_eq_false, decide_false]
          rw [ihl, ihr]
        · simp only [evalMemSteps, AuxTree.evalInorder, ↓reduceIte,
            hown0, Option.map_none, Option.toList_none, List.append_nil,
            List.map_append, List.filter_append, List.filter_cons, List.filter_nil,
            Bool.true_xor, h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [ihr, ihl]
      · have hownId : ∀ (s : RawStep), nodeOwnRawStep mem nb h L x = some s → s.nodeId = x := by
          intro s hs; unfold nodeOwnRawStep at hs; simp [h0] at hs; subst hs; rfl
        cases hopt : nodeOwnRawStep mem nb h L x with
        | none => simp [nodeOwnRawStep, h0] at hopt
        | some s =>
            have hsx : s.nodeId = x := hownId s hopt
            cases b
            · simp only [evalMemSteps, AuxTree.evalInorder, Bool.false_eq_true, ↓reduceIte,
                hopt, Option.map_some, Option.toList_some, List.map_append, List.map_cons,
                List.map_nil, RawStep.nodeId_addDeltaMod, hsx, List.filter_append,
                List.filter_cons, List.filter_nil, Bool.false_xor, h0, ne_eq,
                not_false_eq_true, decide_true]
              rw [ihl, ihr]
            · simp only [evalMemSteps, AuxTree.evalInorder, ↓reduceIte,
                hopt, Option.map_some, Option.toList_some, List.map_append, List.map_cons,
                List.map_nil, RawStep.nodeId_addDeltaMod, RawStep.nodeId_flip, hsx,
                List.filter_append, List.filter_cons, List.filter_nil, Bool.true_xor,
                h0, ne_eq, not_false_eq_true, decide_true]
              rw [ihr, ihl]

end FixedPointAndSteps

section AuxForestModel

/-- Ancestor parent induced by a logical auxiliary path list `xs` whose top path-parent is `prev`. -/
def listParentFrom (prev : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | y :: ys, u => if u = y then prev else listParentFrom y ys u

/-- Logical in-order traversal of the auxiliary splay tree rooted at `r`. -/
def lctTreeSeq (mem : ℕ → ℕ) (nb cap r : ℕ) : List ℕ :=
  (readAuxTree mem nb cap cap r).evalInorder (revFlag mem nb) false

/-- If `u` lies in auxiliary tree `r`, compute its parent in the represented subdivided forest. -/
def treeParentEntry (mem : ℕ → ℕ) (nb cap r u : ℕ) : Option ℕ :=
  let seq := lctTreeSeq mem nb cap r
  if u ∈ seq then
    let pp := nodeField mem nb r OFF_PPAR
    some (listParentFrom (if pp ≤ cap then pp else 0) seq u)
  else none

/-- Represented parent map on node IDs `1 .. cap` induced purely from memory `[nb, arenaHi)`. -/
def lctAuxParent (mem : ℕ → ℕ) (nb cap u : ℕ) : ℕ :=
  match (auxRootIds mem nb cap).findSome? (fun r => treeParentEntry mem nb cap r u) with
  | some p => p
  | none => 0

/-- Iterate a parent map `k` steps from `u`. -/
def iterParent (par : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, u => u
  | k + 1, u => iterParent par k (par u)

/-- Bounded reachability in the represented parent map (`u` reaches `y` in `< cap` steps). -/
def reachesIn (par : ℕ → ℕ) (cap u y : ℕ) : Bool :=
  decide (1 ≤ u ∧ u ≤ cap) &&
    (List.range cap).any (fun k => decide (iterParent par k u = y))

/-- Represented subtree size at node `y` in `[1 .. cap]`. -/
def lctRepSize (mem : ℕ → ℕ) (nb cap y : ℕ) : ℕ :=
  (((List.range cap).map (· + 1)).filter
    (fun u => reachesIn (lctAuxParent mem nb cap) cap u y)).length

/-- Represented subtree size of auxiliary root `r` (at its logical top node). -/
def dashedChildSize (mem : ℕ → ℕ) (nb cap r : ℕ) : ℕ :=
  match lctTreeSeq mem nb cap r with
  | [] => 0
  | hd :: _ => lctRepSize mem nb cap hd

/-- Virtual (dashed-child) weight `vSize y` = sum of represented sizes of auxiliary trees
whose root `OFF_PPAR` equals `y`. -/
def lctVSize (mem : ℕ → ℕ) (nb cap y : ℕ) : ℕ :=
  (((auxRootIds mem nb cap).filter (fun r => decide (nodeField mem nb r OFF_PPAR = y))).map
    (fun r => dashedChildSize mem nb cap r)).sum

/-- Whether auxiliary root `r` represents a heavy dashed edge (`2 * size(hd) > size(ppar)`
with `1 ≤ ppar ≤ cap`). -/
def isHeavyRoot (mem : ℕ → ℕ) (nb cap r : ℕ) : Bool :=
  let pp := nodeField mem nb r OFF_PPAR
  decide (1 ≤ pp ∧ pp ≤ cap) &&
    match lctTreeSeq mem nb cap r with
    | [] => false
    | hd :: _ => decide (lctRepSize mem nb cap pp < 2 * lctRepSize mem nb cap hd)

/-- Number of heavy dashed edges across all auxiliary roots in `1 .. cap`. -/
def lctHeavyCount (mem : ℕ → ℕ) (nb cap : ℕ) : ℕ :=
  ((auxRootIds mem nb cap).filter (fun r => isHeavyRoot mem nb cap r)).length

/-- Global potential `splayMemPhi (K_SPLAY_STEP L) + C_HEAVY L * lctHeavyCount`. -/
def lctPhi (L : ℕ) (mem : ℕ → ℕ) (b n : ℕ) : ℕ :=
  splayMemPhi (K_SPLAY_STEP L) mem (lctNodesBase b) (lctCap n)
      (lctVSize mem (lctNodesBase b) (lctCap n)) +
    C_HEAVY L * lctHeavyCount mem (lctNodesBase b) (lctCap n)

end AuxForestModel

section RepresentationAndDSRep

/-- Concrete Word-RAM representation witness for a `MathForest`. -/
structure LctConc where
  n : ℕ
  trees : List AuxTree
  freeEdges : List ℕ
  edgeMap : List (ℕ × ForestEdge)
  regions : List (ℕ × ℕ)
  hpHi : ℕ

/-- Singly linked free edge-slot stack starting at `hd` and linked through `OFF_EU`. -/
def FreeSlotChain (mem : ℕ → ℕ) (nb : ℕ) : ℕ → List ℕ → Prop
  | hd, [] => hd = 0
  | hd, ed :: rest => hd = ed ∧ FreeSlotChain mem nb (nodeField mem nb ed OFF_EU) rest

/-- Vertex slots `1 .. n` hold `ISV = 1` and `HASE = 0`. -/
def VertexNodeOk (mem : ℕ → ℕ) (nb n : ℕ) : Prop :=
  ∀ v < n,
    let u := v + 1
    nodeField mem nb u OFF_ISV = 1 ∧ nodeField mem nb u OFF_HASE = 0

/-- Active edge slots `(ed, e) ∈ edgeMap` store static edge identity (`ISV=0, HASE=1, EID, EU, EV`)
and decode inside `evalMemSteps` to an oriented `RawStep` matching `e` and consistent with
`lctAuxParent`. -/
def ActiveEdgeNodeOk (mem : ℕ → ℕ) (nb h L P n : ℕ) (trees : List AuxTree)
    (edgeMap : List (ℕ × ForestEdge)) : Prop :=
  let cap := lctCap n
  let par := lctAuxParent mem nb cap
  ∀ p ∈ edgeMap,
    let ed := p.1
    let e := p.2
    n + 1 ≤ ed ∧ ed ≤ cap ∧
    nodeField mem nb ed OFF_ISV = 0 ∧
    nodeField mem nb ed OFF_HASE = 1 ∧
    nodeField mem nb ed OFF_EID = e.eid ∧
    nodeField mem nb ed OFF_EU = e.u ∧
    nodeField mem nb ed OFF_EV = e.v ∧
    ∃ t ∈ trees, ed ∈ t.toList ∧
      ∃ s ∈ evalMemSteps mem nb h L t false 0,
        stepMatchesEdge P ed e s ∧
        ((s.fwd = true ∧ par ed = e.u + 1 ∧ par (e.v + 1) = ed) ∨
         (s.fwd = false ∧ par ed = e.v + 1 ∧ par (e.u + 1) = ed))

/-- Every auxiliary tree `t ∈ trees` is either a free singleton edge slot with `PPAR = 0`,
or an active non-empty path ending at a vertex node with `PPAR` pointing to `0` or an active node. -/
def LctAuxPathOk (mem : ℕ → ℕ) (nb n : ℕ) (freeEdges : List ℕ) (trees : List AuxTree) : Prop :=
  let cap := lctCap n
  ∀ t ∈ trees,
    let seq := t.evalInorder (revFlag mem nb) false
    let pp := nodeField mem nb t.rootId OFF_PPAR
    seq ≠ [] ∧
    (pp = 0 ∨ (1 ≤ pp ∧ pp ≤ cap ∧ pp ∉ freeEdges)) ∧
    ((t.rootId ∈ freeEdges ∧ t = AuxTree.node t.rootId .leaf .leaf ∧ pp = 0) ∨
      (∃ v, v < n ∧ seq.getLast? = some (v + 1)))

/-- Represented parent map `par` on `1 .. 2 * n` forms an acyclic subdivided forest matching
active `edgeMap` and free `freeEdges`. -/
def LctSubdivOk (mem : ℕ → ℕ) (nb n : ℕ) (freeEdges : List ℕ)
    (edgeMap : List (ℕ × ForestEdge)) : Prop :=
  let cap := lctCap n
  let par := lctAuxParent mem nb cap
  (∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0) ∧
  (∀ ed ∈ freeEdges, par ed = 0) ∧
  (∀ v < n, par (v + 1) = 0 ∨
    ∃ p ∈ edgeMap, (p.2.u = v ∨ p.2.v = v) ∧ par (v + 1) = p.1) ∧
  (∀ p ∈ edgeMap,
    (par p.1 = p.2.u + 1 ∧ par (p.2.v + 1) = p.1) ∨
    (par p.1 = p.2.v + 1 ∧ par (p.2.u + 1) = p.1))

/-- Footprint predicate of a concrete `LctConc` state: the header and node array
`[b, lctArenaHi b (lctCap x.n))` plus all allocated heap intervals in `x.regions`. -/
def lctFoot (b : ℕ) (x : LctConc) (a : ℕ) : Prop :=
  (b ≤ a ∧ a < lctArenaHi b (lctCap x.n)) ∨ ∃ iv ∈ x.regions, iv.1 ≤ a ∧ a < iv.2

/-- Every active `Num` pointer field in nodes `0 .. cap` is either `0` or lies in `lctFoot b x`
(of width `max 1 L`, below `mem (nb - 1)`). -/
def PtrFootOk (b : ℕ) (mem : ℕ → ℕ) (x : LctConc) (L : ℕ) : Prop :=
  let nb := lctNodesBase b
  let cap := lctCap x.n
  let arenaHi := lctArenaHi b cap
  ∀ u ≤ cap, ∀ off ∈ ptrOffs,
    let ptr := nodeField mem nb u off
    ptr = 0 ∨
      (arenaHi ≤ ptr ∧ ptr + L ≤ mem (nb - 1) ∧
        ∀ a, ptr ≤ a → a < ptr + max 1 L → lctFoot b x a)

/-- Full Word-RAM representation invariant tying `MathForest` `F` and `LctConc` `x` to `mem`. -/
def LctMemRep (w h L P b : ℕ) (F : MathForest) (x : LctConc) (mem : ℕ → ℕ) : Prop :=
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let arenaHi := lctArenaHi b cap
  0 < h ∧
  2 * h + 2 ≤ w ∧
  F.Valid ∧
  (∀ e ∈ F.edges, EdgeFits h L P e) ∧
  x.n = F.n ∧
  arenaHi ≤ x.hpHi ∧
  0 < x.hpHi ∧
  lctFoot b x (x.hpHi - 1) ∧
  (∀ iv ∈ x.regions, b ≤ iv.1 ∧ iv.1 < iv.2 ∧ iv.2 ≤ x.hpHi) ∧
  mem (b + LCT_HDR_N) = F.n ∧
  mem (b + LCT_HDR_CAP) = cap ∧
  mem (b + LCT_HDR_L) = L ∧
  mem (b + LCT_HDR_P) = P ∧
  arenaHi ≤ mem (b + LCT_HDR_HP) ∧
  mem (b + LCT_HDR_HP) ≤ x.hpHi ∧
  mem (b + LCT_HDR_HP) < 2 ^ w ∧
  (x.edgeMap.map Prod.snd).Perm F.edges ∧
  ((x.edgeMap.map Prod.fst) ++ x.freeEdges).Perm ((List.range F.n).map (F.n + 1 + ·)) ∧
  FreeSlotChain mem nb (mem (b + LCT_HDR_FREE)) x.freeEdges ∧
  (∀ ed ∈ x.freeEdges,
    F.n + 1 ≤ ed ∧ ed ≤ cap ∧
    AuxTree.node ed .leaf .leaf ∈ x.trees ∧
    nodeField mem nb ed OFF_PPAR = 0 ∧
    nodeField mem nb ed OFF_ISV = 0 ∧
    nodeField mem nb ed OFF_HASE = 0) ∧
  SlotZeroOk mem nb ∧
  (x.trees.flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) ∧
  (∀ t ∈ x.trees, t ≠ .leaf ∧
    nodeField mem nb t.rootId OFF_PPAR < 2 ^ w ∧
    TreeMemMatch w h L mem nb cap t 0 (nodeField mem nb t.rootId OFF_PPAR)) ∧
  VertexNodeOk mem nb F.n ∧
  ActiveEdgeNodeOk mem nb h L P F.n x.trees x.edgeMap ∧
  LctAuxPathOk mem nb F.n x.freeEdges x.trees ∧
  LctSubdivOk mem nb F.n x.freeEdges x.edgeMap ∧
  PtrFootOk b mem x L

/-- Word-RAM `DSRep MathForest` for `LctMemRep`. -/
def lctDSRep (w h L P : ℕ) : DSRep MathForest where
  τ := LctConc
  rep b F x mem := LctMemRep w h L P b F x mem
  phi b x mem := lctPhi L mem b x.n
  foot b x a := lctFoot b x a

end RepresentationAndDSRep

end MinCostFlow.LinkCut.Prog
