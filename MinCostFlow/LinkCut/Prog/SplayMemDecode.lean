module

public import MinCostFlow.LinkCut.Prog.SplayDefs
public import MinCostFlow.LinkCut.Prog.Amortized
public import MinCostFlow.Num.Encoding

namespace MinCostFlow.LinkCut.Prog

/-!
# Node fields, limb aggregates, and memory invariants of the splay arena

Multi-limb integer aggregates, logical edge steps, decoding of node fields, the memory
invariant `TreeMemMatch`, and the first framing facts about it.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-- Root node identifier of an `AuxTree`, or `0` for `leaf`. -/
def AuxTree.rootId : AuxTree → ℕ
  | .leaf => 0
  | .node id _ _ => id

/-- Flip the immediate children of the root of `t` (corresponding to `reverseNode`). -/
def AuxTree.flipRoot : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r => .node id r l

/-- Sentinel slot `0` at `nodesBase` stores zeros in all `NODE_STRIDE` fields. -/
def SlotZeroOk (mem : ℕ → ℕ) (nodesBase : ℕ) : Prop :=
  ∀ off < NODE_STRIDE, mem (nodesBase + off) = 0

/-- Boolean reversal flag stored at node `x`. -/
def revFlag (mem : ℕ → ℕ) (nodesBase x : ℕ) : Bool :=
  decide (nodeField mem nodesBase x OFF_REV ≠ 0)

/-- Sum of `OFF_ISV` over node list `L`. -/
def listVcnt (mem : ℕ → ℕ) (nodesBase : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => nodeField mem nodesBase x OFF_ISV + listVcnt mem nodesBase xs

theorem listVcnt_append (mem : ℕ → ℕ) (nodesBase : ℕ) (L₁ L₂ : List ℕ) :
    listVcnt mem nodesBase (L₁ ++ L₂) = listVcnt mem nodesBase L₁ + listVcnt mem nodesBase L₂ := by
  induction L₁ with
  | nil => simp [listVcnt]
  | cons x xs ih => simp [listVcnt, ih]; omega

theorem listVcnt_reverse (mem : ℕ → ℕ) (nodesBase : ℕ) (L : List ℕ) :
    listVcnt mem nodesBase L.reverse = listVcnt mem nodesBase L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [listVcnt_append, ih, listVcnt]; omega

/-! ### Multi-limb integer aggregates and logical edge steps -/

/-- Directional integer minimum aggregate over node IDs, storing earliest and latest tying IDs. -/
structure IntMinAgg where
  has : Bool
  val : ℤ
  first : ℕ
  last : ℕ
  deriving DecidableEq

/-- Combine two directional `IntMinAgg` summaries (`a` ordered before `b`). -/
def combineIntMinAgg (a b : IntMinAgg) : IntMinAgg :=
  if !b.has then (if !a.has then ⟨false, 0, 0, 0⟩ else a)
  else if !a.has then b
  else if b.val < a.val then b
  else if a.val = b.val then { a with last := b.last }
  else a

/-- Reverse a directional `IntMinAgg` summary (swapping earliest and latest tying nodes). -/
def IntMinAgg.rev (a : IntMinAgg) : IntMinAgg :=
  if !a.has then ⟨false, 0, 0, 0⟩ else { a with first := a.last, last := a.first }

theorem combineIntMinAgg_assoc (a b c : IntMinAgg) :
    combineIntMinAgg (combineIntMinAgg a b) c = combineIntMinAgg a (combineIntMinAgg b c) := by
  rcases a with ⟨ha, va, fa, la⟩
  rcases b with ⟨hb, vb, fb, lb⟩
  rcases c with ⟨hc, vc, fc, lc⟩
  cases ha <;> cases hb <;> cases hc
  all_goals simp only [combineIntMinAgg, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · by_cases hbc : vc < vb <;> by_cases hebc : vb = vc <;> simp [hbc, hebc]
  · by_cases hab : vb < va <;> by_cases heab : va = vb <;> simp [hab, heab]
  · by_cases hab : vb < va <;> by_cases hbc : vc < vb <;> by_cases hac : vc < va <;>
      by_cases heab : va = vb <;> by_cases hebc : vb = vc <;> by_cases heac : va = vc <;>
      · simp only [hab, hbc, hac, heab, hebc, heac, ↓reduceIte]
        all_goals (split_ifs <;> simp_all <;> omega)

theorem combineIntMinAgg_rev (a b : IntMinAgg) :
    combineIntMinAgg b.rev a.rev = (combineIntMinAgg a b).rev := by
  rcases a with ⟨ha, va, fa, la⟩
  rcases b with ⟨hb, vb, fb, lb⟩
  cases ha <;> cases hb <;> simp [combineIntMinAgg, IntMinAgg.rev]
  by_cases hab : vb < va <;> by_cases hba : va < vb <;> by_cases he : va = vb <;>
    simp [hab, hba, he] <;> omega

/-- List fold computing the `IntMinAgg` over `(nodeId, keyVal)` pairs. -/
def listIntMinAgg : List (ℕ × ℤ) → IntMinAgg
  | [] => ⟨false, 0, 0, 0⟩
  | (id, v) :: xs => combineIntMinAgg ⟨true, v, id, id⟩ (listIntMinAgg xs)

theorem listIntMinAgg_false_eq {xs : List (ℕ × ℤ)} (h : (listIntMinAgg xs).has = false) :
    listIntMinAgg xs = ⟨false, 0, 0, 0⟩ := by
  cases xs with
  | nil => rfl
  | cons p xs =>
      rcases p with ⟨id, v⟩
      rcases hxs : listIntMinAgg xs with ⟨hb, vb, fb, lb⟩
      cases hb
      · simp only [listIntMinAgg, combineIntMinAgg, hxs, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] at h
        cases h
      · simp only [listIntMinAgg, combineIntMinAgg, hxs, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte] at h
        split_ifs at h

theorem listIntMinAgg_append (xs ys : List (ℕ × ℤ)) :
    listIntMinAgg (xs ++ ys) = combineIntMinAgg (listIntMinAgg xs) (listIntMinAgg ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, listIntMinAgg]
      cases h : (listIntMinAgg ys).has
      · rw [listIntMinAgg_false_eq h]; simp [combineIntMinAgg]
      · simp [combineIntMinAgg, h]
  | cons p xs ih =>
      rcases p with ⟨id, v⟩
      simp only [List.cons_append, listIntMinAgg, ih, combineIntMinAgg_assoc]

theorem listIntMinAgg_reverse (xs : List (ℕ × ℤ)) :
    listIntMinAgg xs.reverse = (listIntMinAgg xs).rev := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      rcases p with ⟨id, v⟩
      simp only [List.reverse_cons, listIntMinAgg_append, listIntMinAgg, ih]
      have hsing : combineIntMinAgg ⟨true, v, id, id⟩ ⟨false, 0, 0, 0⟩ = ⟨true, v, id, id⟩ := by
        simp [combineIntMinAgg]
      rw [hsing]
      simpa [IntMinAgg.rev] using combineIntMinAgg_rev ⟨true, v, id, id⟩ (listIntMinAgg xs)

/-- Edge step record decoded from an active edge splay node in integer (`ℤ`) units. -/
structure RawStep where
  nodeId : ℕ
  eid : ℕ
  eu : ℕ
  ev : ℕ
  fwd : Bool
  cost : ℤ
  flow : ℤ
  availFwd : ℤ
  availBwd : ℤ
  deriving DecidableEq

namespace RawStep

/-- Reverse traversal orientation of a `RawStep`. -/
def flip (s : RawStep) : RawStep :=
  { s with fwd := !s.fwd }

/-- Signed traversal cost of a `RawStep`. -/
def signedCost (s : RawStep) : ℤ :=
  if s.fwd then s.cost else -s.cost

/-- Availability in the traversal direction of `s`. -/
def dirAvail (s : RawStep) : ℤ :=
  if s.fwd then s.availFwd else s.availBwd

/-- Shift `s` by `δ` modulo `capacity h L` (using two's-complement wrap `wrap h L`). -/
def addDeltaMod (h L : ℕ) (s : RawStep) (δ : ℤ) : RawStep :=
  if s.fwd then
    { s with
      flow := wrap h L (s.flow + δ)
      availFwd := wrap h L (s.availFwd - δ)
      availBwd := wrap h L (s.availBwd + δ) }
  else
    { s with
      flow := wrap h L (s.flow - δ)
      availFwd := wrap h L (s.availFwd + δ)
      availBwd := wrap h L (s.availBwd - δ) }

/-- Exact un-wrapped shift of `s` by `δ` in traversal direction `s.fwd`. -/
def addDelta (s : RawStep) (δ : ℤ) : RawStep :=
  if s.fwd then
    { s with
      flow := s.flow + δ
      availFwd := s.availFwd - δ
      availBwd := s.availBwd + δ }
  else
    { s with
      flow := s.flow - δ
      availFwd := s.availFwd + δ
      availBwd := s.availBwd - δ }

@[simp]
theorem signedCost_flip (s : RawStep) : s.flip.signedCost = -s.signedCost := by
  cases hf : s.fwd <;> simp [flip, signedCost, hf]

@[simp]
theorem signedCost_addDeltaMod (h L : ℕ) (s : RawStep) (δ : ℤ) :
    (s.addDeltaMod h L δ).signedCost = s.signedCost := by
  cases hf : s.fwd <;> simp [addDeltaMod, signedCost, hf]

@[simp]
theorem signedCost_addDelta (s : RawStep) (δ : ℤ) :
    (s.addDelta δ).signedCost = s.signedCost := by
  cases hf : s.fwd <;> simp [addDelta, signedCost, hf]

@[simp]
theorem dirAvail_addDeltaMod (h L : ℕ) (s : RawStep) (δ : ℤ) :
    (s.addDeltaMod h L δ).dirAvail = wrap h L (s.dirAvail - δ) := by
  cases hf : s.fwd <;> simp [addDeltaMod, dirAvail, hf]

@[simp]
theorem dirAvail_flip_addDeltaMod (h L : ℕ) (s : RawStep) (δ : ℤ) :
    (s.addDeltaMod h L δ).flip.dirAvail = wrap h L (s.flip.dirAvail + δ) := by
  cases hf : s.fwd <;> simp [addDeltaMod, flip, dirAvail, hf]

@[simp]
theorem dirAvail_addDelta (s : RawStep) (δ : ℤ) :
    (s.addDelta δ).dirAvail = s.dirAvail - δ := by
  cases hf : s.fwd <;> simp [addDelta, dirAvail, hf]

@[simp]
theorem dirAvail_flip_addDelta (s : RawStep) (δ : ℤ) :
    (s.addDelta δ).flip.dirAvail = s.flip.dirAvail + δ := by
  cases hf : s.fwd <;> simp [addDelta, flip, dirAvail, hf]

theorem addDeltaMod_flip (h L : ℕ) (s : RawStep) (δ : ℤ) :
    s.flip.addDeltaMod h L (-δ) = (s.addDeltaMod h L δ).flip := by
  cases hf : s.fwd <;> simp [addDeltaMod, flip, hf, sub_eq_add_neg, add_comm]

theorem wrap_add_wrap_right (h L : ℕ) (a b : ℤ) :
    wrap h L (a + wrap h L b) = wrap h L (a + b) :=
  wrap_add_wrap h L a b

theorem wrap_sub_wrap_right (h L : ℕ) (a b : ℤ) :
    wrap h L (a - wrap h L b) = wrap h L (a - b) := by
  apply wrap_congr
  rw [Int.sub_emod, wrap_emod, ← Int.sub_emod]

theorem addDeltaMod_addDeltaMod (h L : ℕ) (s : RawStep) (δ₁ δ₂ : ℤ) :
    (s.addDeltaMod h L δ₁).addDeltaMod h L δ₂ = s.addDeltaMod h L (δ₁ + δ₂) := by
  cases hdir : s.fwd
  · simp only [addDeltaMod, hdir, Bool.false_eq_true, ↓reduceIte]
    have h1 : wrap h L (wrap h L (s.flow - δ₁) - δ₂) = wrap h L (s.flow - (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.sub_emod, wrap_emod, ← Int.sub_emod]; ring_nf
    have h2 : wrap h L (wrap h L (s.availFwd + δ₁) + δ₂) = wrap h L (s.availFwd + (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.add_emod, wrap_emod, ← Int.add_emod]; ring_nf
    have h3 : wrap h L (wrap h L (s.availBwd - δ₁) - δ₂) = wrap h L (s.availBwd - (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.sub_emod, wrap_emod, ← Int.sub_emod]; ring_nf
    simp [h1, h2, h3]
  · simp only [addDeltaMod, hdir, ↓reduceIte]
    have h1 : wrap h L (wrap h L (s.flow + δ₁) + δ₂) = wrap h L (s.flow + (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.add_emod, wrap_emod, ← Int.add_emod]; ring_nf
    have h2 : wrap h L (wrap h L (s.availFwd - δ₁) - δ₂) = wrap h L (s.availFwd - (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.sub_emod, wrap_emod, ← Int.sub_emod]; ring_nf
    have h3 : wrap h L (wrap h L (s.availBwd + δ₁) + δ₂) = wrap h L (s.availBwd + (δ₁ + δ₂)) := by
      apply wrap_congr
      rw [Int.add_emod, wrap_emod, ← Int.add_emod]; ring_nf
    simp [h1, h2, h3]

theorem addDeltaMod_zero {h L : ℕ} {s : RawStep}
    (hf : Fits h L s.flow) (haf : Fits h L s.availFwd) (hab : Fits h L s.availBwd) :
    s.addDeltaMod h L 0 = s := by
  rcases s with ⟨nid, eid, eu, ev, fwd, cost, flow, af, ab⟩
  cases fwd <;> simp [addDeltaMod, wrap_of_fits hf, wrap_of_fits haf, wrap_of_fits hab]

end RawStep

/-- Total signed cost of a list of `RawStep`s. -/
def listRawCost (steps : List RawStep) : ℤ :=
  (steps.map RawStep.signedCost).sum

theorem listRawCost_append (xs ys : List RawStep) :
    listRawCost (xs ++ ys) = listRawCost xs + listRawCost ys := by
  simp [listRawCost, List.map_append, List.sum_append]

theorem listRawCost_reverse_flip (xs : List RawStep) :
    listRawCost (xs.reverse.map RawStep.flip) = -listRawCost xs := by
  induction xs with
  | nil => simp [listRawCost]
  | cons s xs ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [listRawCost_append, ih]
      simp only [listRawCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        RawStep.signedCost_flip]
      omega

/-! ### Decoding multi-limb node fields and memory invariants -/

/-- Check that a mandatory `Num` block pointer lies in `[arenaHi, hp)` and holds `L` valid limbs. -/
def NumPtrOk (mem : ℕ → ℕ) (arenaHi hp h L ptr : ℕ) : Prop :=
  ptr ≠ 0 ∧ arenaHi ≤ ptr ∧ ptr + L ≤ hp ∧ Valid mem ptr h L

/-- Check that an optional `Num` pointer is either `0` (canonical zero) or a valid block in `[arenaHi, hp)`. -/
def OptNumPtrOk (mem : ℕ → ℕ) (arenaHi hp h L ptr : ℕ) : Prop :=
  ptr = 0 ∨ (arenaHi ≤ ptr ∧ ptr + L ≤ hp ∧ Valid mem ptr h L)

/-- Signed integer decoded from an optional `Num` block pointer (`0` decodes as `0`). -/
def optIntVal (mem : ℕ → ℕ) (h L ptr : ℕ) : ℤ :=
  if ptr = 0 then 0 else intVal mem ptr h L

/-- Signed lazy delta stored on node `x`. -/
def nodeTagInt (mem : ℕ → ℕ) (nb h L x : ℕ) : ℤ :=
  if nodeField mem nb x OFF_HAS_TAG = 0 then 0
  else if nodeField mem nb x OFF_TAG_NEG = 0 then
    optIntVal mem h L (nodeField mem nb x OFF_TAG_PTR)
  else
    -optIntVal mem h L (nodeField mem nb x OFF_TAG_PTR)

/-- Decode the directional forward `IntMinAgg` stored on node `x`. -/
def nodeIntMinAgg1 (mem : ℕ → ℕ) (nb h L x : ℕ) : IntMinAgg :=
  ⟨decide (nodeField mem nb x OFF_MIN1_HAS ≠ 0),
   optIntVal mem h L (nodeField mem nb x OFF_MIN1_VAL),
   nodeField mem nb x OFF_MIN1_FIRST,
   nodeField mem nb x OFF_MIN1_LAST⟩

/-- Decode the directional backward `IntMinAgg` stored on node `x`. -/
def nodeIntMinAgg2 (mem : ℕ → ℕ) (nb h L x : ℕ) : IntMinAgg :=
  ⟨decide (nodeField mem nb x OFF_MIN2_HAS ≠ 0),
   optIntVal mem h L (nodeField mem nb x OFF_MIN2_VAL),
   nodeField mem nb x OFF_MIN2_FIRST,
   nodeField mem nb x OFF_MIN2_LAST⟩

/-- Decode the local `RawStep` stored at node `x` (none when `OFF_HASE = 0`). -/
def nodeOwnRawStep (mem : ℕ → ℕ) (nb h L x : ℕ) : Option RawStep :=
  if nodeField mem nb x OFF_HASE = 0 then none
  else
    let dir := decide (nodeField mem nb x OFF_DIR ≠ 0)
    let cf := intVal mem (nodeField mem nb x OFF_COST_FWD) h L
    let cb := intVal mem (nodeField mem nb x OFF_COST_BWD) h L
    let af := intVal mem (nodeField mem nb x OFF_AF_PTR) h L
    let ab := intVal mem (nodeField mem nb x OFF_AB_PTR) h L
    let flow := intVal mem (nodeField mem nb x OFF_FLOW_PTR) h L
    some
      { nodeId := x
        eid := nodeField mem nb x OFF_EID
        eu := nodeField mem nb x OFF_EU
        ev := nodeField mem nb x OFF_EV
        fwd := dir
        cost := if dir then cf else cb
        flow := flow
        availFwd := if dir then af else ab
        availBwd := if dir then ab else af }

/-- Decode the logical in-order sequence of active edge steps represented by `t`,
evaluating pending `REV` flags and pending `TAG` deltas from the root downwards. -/
def evalMemSteps (mem : ℕ → ℕ) (nb h L : ℕ) : AuxTree → Bool → ℤ → List RawStep
  | .leaf, _, _ => []
  | .node x l r, flipAcc, δAcc =>
      let own := (nodeOwnRawStep mem nb h L x).map
        (fun s => (if flipAcc then s.flip else s).addDeltaMod h L δAcc) |>.toList
      let flip' := flipAcc ^^ revFlag mem nb x
      let δLocal := if flipAcc then -nodeTagInt mem nb h L x else nodeTagInt mem nb h L x
      let δ' := δAcc + δLocal
      if flipAcc then
        evalMemSteps mem nb h L r flip' δ' ++ own ++ evalMemSteps mem nb h L l flip' δ'
      else
        evalMemSteps mem nb h L l flip' δ' ++ own ++ evalMemSteps mem nb h L r flip' δ'

/-- Compatibility condition ensuring shifting `steps` by `δ` keeps all edge fields in `Fits h L`. -/
def StepsShiftFit (h L : ℕ) (steps : List RawStep) (δ : ℤ) : Prop :=
  ∀ s ∈ steps,
    Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd ∧
    Fits h L (if s.fwd then s.flow + δ else s.flow - δ) ∧
    Fits h L (if s.fwd then s.availFwd - δ else s.availFwd + δ) ∧
    Fits h L (if s.fwd then s.availBwd + δ else s.availBwd - δ)

/-- Recursive memory-vs-`AuxTree` representation invariant for a single auxiliary tree `t`
with parent `parentId`, path-parent `pparVal`, limb width `h`, and limb count `L`. -/
def TreeMemMatch (w h L : ℕ) (mem : ℕ → ℕ) (nodesBase cap : ℕ) :
    AuxTree → ℕ → ℕ → Prop
  | .leaf, _, _ => True
  | .node x l r, parentId, pparVal =>
      let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
      let hp := mem (nodesBase - 1)
      1 ≤ x ∧ x ≤ cap ∧
      nodeField mem nodesBase x OFF_LEFT = l.rootId ∧
      nodeField mem nodesBase x OFF_RIGHT = r.rootId ∧
      nodeField mem nodesBase x OFF_PARENT = parentId ∧
      nodeField mem nodesBase x OFF_PPAR = pparVal ∧
      nodeField mem nodesBase x OFF_REV ≤ 1 ∧
      nodeField mem nodesBase x OFF_ISV ≤ 1 ∧
      nodeField mem nodesBase x OFF_HASE ≤ 1 ∧
      nodeField mem nodesBase x OFF_ISV + nodeField mem nodesBase x OFF_HASE ≤ 1 ∧
      nodeField mem nodesBase x OFF_DIR ≤ 1 ∧
      nodeField mem nodesBase x OFF_HAS_TAG ≤ 1 ∧
      nodeField mem nodesBase x OFF_TAG_NEG ≤ 1 ∧
      nodeField mem nodesBase x OFF_EU < 2 ^ w ∧
      nodeField mem nodesBase x OFF_EV < 2 ^ w ∧
      nodeField mem nodesBase x OFF_EID < 2 ^ w ∧
      (nodeField mem nodesBase x OFF_HASE = 1 →
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_FLOW_PTR) ∧
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_AF_PTR) ∧
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_AB_PTR) ∧
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_COST_FWD) ∧
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_COST_BWD) ∧
        intVal mem (nodeField mem nodesBase x OFF_COST_BWD) h L =
          wrap h L (-intVal mem (nodeField mem nodesBase x OFF_COST_FWD) h L)) ∧
      (nodeField mem nodesBase x OFF_HASE = 0 →
        nodeField mem nodesBase x OFF_DIR = 0 ∧
        nodeField mem nodesBase x OFF_FLOW_PTR = 0 ∧
        nodeField mem nodesBase x OFF_AF_PTR = 0 ∧
        nodeField mem nodesBase x OFF_AB_PTR = 0 ∧
        nodeField mem nodesBase x OFF_COST_FWD = 0 ∧
        nodeField mem nodesBase x OFF_COST_BWD = 0) ∧
      OptNumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_CSUM_FWD) ∧
      OptNumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_CSUM_BWD) ∧
      (nodeField mem nodesBase x OFF_HAS_TAG = 1 →
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_TAG_PTR) ∧
        ((l ≠ .leaf ∧ nodeField mem nodesBase l.rootId OFF_MIN1_HAS = 1) ∨
         (r ≠ .leaf ∧ nodeField mem nodesBase r.rootId OFF_MIN1_HAS = 1)) ∧
        ∃ d : ℤ, d % (capacity h L : ℤ) = nodeTagInt mem nodesBase h L x % (capacity h L : ℤ) ∧
          StepsShiftFit h L
            (evalMemSteps mem nodesBase h L l (revFlag mem nodesBase x) 0 ++
             evalMemSteps mem nodesBase h L r (revFlag mem nodesBase x) 0) d) ∧
      (nodeField mem nodesBase x OFF_HAS_TAG = 0 →
        nodeField mem nodesBase x OFF_TAG_PTR = 0 ∧
        nodeField mem nodesBase x OFF_TAG_NEG = 0) ∧
      nodeField mem nodesBase x OFF_MIN1_HAS ≤ 1 ∧
      nodeField mem nodesBase x OFF_MIN2_HAS = nodeField mem nodesBase x OFF_MIN1_HAS ∧
      (nodeField mem nodesBase x OFF_MIN1_HAS = 1 →
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_MIN1_VAL) ∧
        NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase x OFF_MIN2_VAL) ∧
        nodeField mem nodesBase x OFF_MIN1_FIRST < 2 ^ w ∧
        nodeField mem nodesBase x OFF_MIN1_LAST < 2 ^ w ∧
        nodeField mem nodesBase x OFF_MIN2_FIRST < 2 ^ w ∧
        nodeField mem nodesBase x OFF_MIN2_LAST < 2 ^ w) ∧
      (nodeField mem nodesBase x OFF_MIN1_HAS = 0 →
        nodeField mem nodesBase x OFF_MIN1_VAL = 0 ∧
        nodeField mem nodesBase x OFF_MIN1_FIRST = 0 ∧
        nodeField mem nodesBase x OFF_MIN1_LAST = 0 ∧
        nodeField mem nodesBase x OFF_MIN2_VAL = 0 ∧
        nodeField mem nodesBase x OFF_MIN2_FIRST = 0 ∧
        nodeField mem nodesBase x OFF_MIN2_LAST = 0) ∧
      (let seq := (AuxTree.node x l r).evalInorder (revFlag mem nodesBase) false
       let steps := evalMemSteps mem nodesBase h L (.node x l r) false 0
       nodeField mem nodesBase x OFF_VCNT = listVcnt mem nodesBase seq ∧
       optIntVal mem h L (nodeField mem nodesBase x OFF_CSUM_FWD) = wrap h L (listRawCost steps) ∧
       optIntVal mem h L (nodeField mem nodesBase x OFF_CSUM_BWD) = wrap h L (-listRawCost steps) ∧
       (nodeField mem nodesBase x OFF_MIN1_HAS = 1 ↔ steps ≠ []) ∧
       nodeIntMinAgg1 mem nodesBase h L x =
         listIntMinAgg (steps.map fun s => (s.nodeId, s.dirAvail)) ∧
       nodeIntMinAgg2 mem nodesBase h L x =
         listIntMinAgg (steps.map fun s => (s.nodeId, s.flip.dirAvail))) ∧
      TreeMemMatch w h L mem nodesBase cap l x 0 ∧
      TreeMemMatch w h L mem nodesBase cap r x 0

/-- Full invariant for a collection of disjoint auxiliary splay trees partitioning `1 .. cap`. -/
def SplayForestOk (w h L : ℕ) (mem : ℕ → ℕ) (nodesBase cap : ℕ) (trees : List AuxTree) : Prop :=
  0 < h ∧
  2 * h + 2 ≤ w ∧
  3 ≤ nodesBase ∧
  nodesBase + NODE_STRIDE * (cap + 1) ≤ mem (nodesBase - 1) ∧
  mem (nodesBase - 3) = L ∧
  mem (nodesBase - 1) < 2 ^ w ∧
  ZeroFrom mem (mem (nodesBase - 1)) ∧
  SlotZeroOk mem nodesBase ∧
  (trees.flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) ∧
  ∀ t ∈ trees, t ≠ .leaf ∧
    nodeField mem nodesBase t.rootId OFF_PPAR < 2 ^ w ∧
    TreeMemMatch w h L mem nodesBase cap t 0 (nodeField mem nodesBase t.rootId OFF_PPAR)

/-! ### Basic `TreeMemMatch` and framing properties -/

theorem TreeMemMatch.nodup_perm_mem {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp)
    {y : ℕ} (hy : y ∈ t.toList) : 1 ≤ y ∧ y ≤ cap := by
  induction t generalizing p pp with
  | leaf => simp [AuxTree.toList] at hy
  | node x l r ihl ihr =>
      rcases ht with ⟨hx1, hx2, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hy
      rcases hy with (hlm | rfl) | hrm
      · exact ihl hl hlm
      · exact ⟨hx1, hx2⟩
      · exact ihr hr hrm

theorem TreeMemMatch.readAuxTree_eq {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp fuel : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp)
    (hfuel : t.countNodes ≤ fuel) :
    readAuxTree mem nodesBase cap fuel t.rootId = t := by
  induction t generalizing p pp fuel with
  | leaf => cases fuel <;> rfl
  | node x l r ihl ihr =>
      rcases ht with ⟨hx1, hx2, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have hc : 1 + l.countNodes + r.countNodes ≤ fuel := by simpa [AuxTree.countNodes] using hfuel
      cases fuel with
      | zero => omega
      | succ f =>
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0) with ⟨x', rfl⟩
          have hlhs : readAuxTree mem nodesBase cap (f + 1) (AuxTree.node x'.succ l r).rootId =
              AuxTree.node x'.succ
                (readAuxTree mem nodesBase cap f (nodeField mem nodesBase x'.succ OFF_LEFT))
                (readAuxTree mem nodesBase cap f (nodeField mem nodesBase x'.succ OFF_RIGHT)) := by
            simp only [AuxTree.rootId, readAuxTree, hx2, ↓reduceIte]
          rw [hlhs, hL, hR, ihl hl (fuel := f) (by omega), ihr hr (fuel := f) (by omega)]

theorem TreeMemMatch.node_lt_pow {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nodesBase cap t p pp)
    {y : ℕ} (hy : y ∈ t.toList) : y < 2 ^ w := by
  have hyb := ht.nodup_perm_mem hy
  unfold NODE_STRIDE at hbase
  omega

theorem numPtrOk_congr {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp₁ hp₂ h L ptr : ℕ}
    (hge : hp₁ ≤ hp₂) (hag : ∀ a, arenaHi ≤ a → a < hp₁ → mem₂ a = mem₁ a)
    (hk : NumPtrOk mem₁ arenaHi hp₁ h L ptr) : NumPtrOk mem₂ arenaHi hp₂ h L ptr := by
  rcases hk with ⟨hnz, hlo, hhi, hval⟩
  refine ⟨hnz, hlo, le_trans hhi hge, ?_⟩
  intro i hi
  rw [hag (ptr + i) (by omega) (by omega)]
  exact hval i hi

theorem optNumPtrOk_congr {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp₁ hp₂ h L ptr : ℕ}
    (hge : hp₁ ≤ hp₂) (hag : ∀ a, arenaHi ≤ a → a < hp₁ → mem₂ a = mem₁ a)
    (hk : OptNumPtrOk mem₁ arenaHi hp₁ h L ptr) : OptNumPtrOk mem₂ arenaHi hp₂ h L ptr := by
  rcases hk with rfl | ⟨hlo, hhi, hval⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hlo, le_trans hhi hge, ?_⟩
    intro i hi
    rw [hag (ptr + i) (by omega) (by omega)]
    exact hval i hi

end
end MinCostFlow.LinkCut.Prog
