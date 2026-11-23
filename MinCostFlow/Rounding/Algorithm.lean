module

public import MinCostFlow.Statement.Problem
public import MinCostFlow.Rounding.DynForest

/-!
# Cycle-cancelling rounding algorithm model (Kang–Payor Section 4)

This file defines the mathematical model of Kang–Payor's `O(m log n)` flow-rounding algorithm
(`arXiv:1507.08139v1`, Section 4), parameterized over an abstract `DynForest` (`Link`, `Cut`,
`FindRoot`, `PathAdd`, `PathMin`, `PathSum`).

Edges `j = 0, …, m - 1` of the instance are processed one by one:
* Integral-flow edges are skipped.
* Fractional edges whose endpoints lie in different trees (`FindRoot u ≠ FindRoot v`) are linked.
* Fractional edges whose endpoints lie in the same tree (`FindRoot u = FindRoot v`, including
  self-loops `u = v` and parallel edges) form a cycle; `PathSum` computes the path cost, we pick
  the direction of non-positive cycle cost (non-negative cost saving), push the minimum
  availability `δ` along the cycle via `PathAdd` and on `flowArr[j]`, recursively cut all
  zero-availability edges along the tree path (`removeZeroEdges` along `a`–`x` and `y`–`v`), and
  link edge `j` only if its updated flow remains fractional.

The file also proves the specification of `removeZeroEdges`: fuel non-exhaustion (hence
termination), exact `Cut` and `PathMin` counts, full removal of zero-availability edges on the
path, preservation of the global actual flow, and fixed-point / magnitude invariants.
-/

@[expose] public section

namespace MinCostFlow.Rounding

/-- Fixed-point precision predicate: `q` is an integer multiple of `2^{-P}`. -/
def IsFixedPoint (P : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / (2 : ℚ) ^ P

theorem isFixedPoint_int (P : ℕ) (z : ℤ) : IsFixedPoint P (z : ℚ) :=
  ⟨z * (2 : ℤ) ^ P, by
    have h2 : ((2 : ℚ) ^ P) ≠ 0 := pow_ne_zero P (by norm_num)
    push_cast
    field_simp [h2]⟩

theorem isFixedPoint_add {P : ℕ} {a b : ℚ} (ha : IsFixedPoint P a) (hb : IsFixedPoint P b) :
    IsFixedPoint P (a + b) := by
  obtain ⟨za, rfl⟩ := ha
  obtain ⟨zb, rfl⟩ := hb
  refine ⟨za + zb, ?_⟩
  push_cast
  ring

theorem isFixedPoint_sub {P : ℕ} {a b : ℚ} (ha : IsFixedPoint P a) (hb : IsFixedPoint P b) :
    IsFixedPoint P (a - b) := by
  obtain ⟨za, rfl⟩ := ha
  obtain ⟨zb, rfl⟩ := hb
  refine ⟨za - zb, ?_⟩
  push_cast
  ring

theorem isFixedPoint_min {P : ℕ} {a b : ℚ} (ha : IsFixedPoint P a) (hb : IsFixedPoint P b) :
    IsFixedPoint P (min a b) := by
  by_cases h : a ≤ b
  · simpa [min_eq_left h] using ha
  · simpa [min_eq_right (le_of_not_ge h)] using hb

/-- Computable test whether a rational number is an integer. -/
def isIntRat (q : ℚ) : Bool :=
  q.den == 1

theorem isIntRat_iff {q : ℚ} : isIntRat q = true ↔ ∃ z : ℤ, q = z := by
  unfold isIntRat
  rw [beq_iff_eq]
  constructor
  · intro h
    exact ⟨q.num, by rw [← Rat.num_div_den q, h]; simp⟩
  · rintro ⟨z, rfl⟩
    simp

/-- Operation and step counts for the Section 4 rounding model. -/
structure RoundCounts where
  findRootOps : ℕ := 0
  linkOps : ℕ := 0
  cutOps : ℕ := 0
  pathAddOps : ℕ := 0
  pathMinOps : ℕ := 0
  pathSumOps : ℕ := 0
  otherSteps : ℕ := 0
  deriving DecidableEq

namespace RoundCounts

/-- Total number of dynamic-tree operations (`FindRoot`, `Link`, `Cut`, `PathAdd`, `PathMin`,
`PathSum`). -/
def treeOps (c : RoundCounts) : ℕ :=
  c.findRootOps + c.linkOps + c.cutOps + c.pathAddOps + c.pathMinOps + c.pathSumOps

end RoundCounts

/-- State threaded through the Section 4 rounding loop. -/
structure RoundState (D : DynForest) (I : Instance) where
  df : D.State
  flowArr : Fin I.m → ℚ
  counts : RoundCounts
  computedRats : List ℚ
  computedCosts : List ℤ

/-- Recursively remove all zero-availability edges along the `a`–`b` path in `df` (Kang–Payor
Section 4, paragraph 3): query `PathMin(a, b)`, if an edge `(x, y)` has zero availability, flush
its stored flow to `flowArr`, `Cut(x, y)`, and recurse on `a`–`x` and `y`–`b`. -/
def removeZeroEdges (D : DynForest) (I : Instance)
    (df : D.State) (flowArr : Fin I.m → ℚ) (counts : RoundCounts)
    (rats : List ℚ) (a b : ℕ) :
    ℕ → D.State × (Fin I.m → ℚ) × RoundCounts × List ℚ
  | 0 => (df, flowArr, counts, rats)
  | fuel + 1 =>
    match D.pathMin df a b with
    | none =>
      (df, flowArr,
        { counts with
          pathMinOps := counts.pathMinOps + 1
          otherSteps := counts.otherSteps + 1 },
        rats)
    | some hit =>
      if hit.avail > 0 then
        (df, flowArr,
          { counts with
            pathMinOps := counts.pathMinOps + 1
            otherSteps := counts.otherSteps + 2 },
          hit.avail :: rats)
      else
        let flowArr₁ := fun k : Fin I.m => if k.1 = hit.eid then hit.flow else flowArr k
        let df₁ := D.cut df hit.x hit.y
        let counts₁ :=
          { counts with
            pathMinOps := counts.pathMinOps + 1
            cutOps := counts.cutOps + 1
            otherSteps := counts.otherSteps + 3 }
        let rats₁ := hit.flow :: hit.avail :: rats
        let r₂ := removeZeroEdges D I df₁ flowArr₁ counts₁ rats₁ a hit.x fuel
        removeZeroEdges D I r₂.1 r₂.2.1 r₂.2.2.1 r₂.2.2.2 hit.y b fuel

/-- Process a single edge `j : Fin I.m` in Kang–Payor Section 4. -/
def roundEdgeStep (D : DynForest) (I : Instance) (f : Fin I.m → ℚ)
    (st : RoundState D I) (j : Fin I.m) : RoundState D I :=
  let fj := f j
  if isIntRat fj then
    { st with
      counts := { st.counts with otherSteps := st.counts.otherSteps + 1 } }
  else
    let e := I.edge j
    let u := e.tail
    let v := e.head
    let aFwd : ℚ := (⌈fj⌉ : ℚ) - fj
    let aBwd : ℚ := fj - (⌊fj⌋ : ℚ)
    let rU := D.findRoot st.df u
    let rV := D.findRoot st.df v
    let counts₁ :=
      { st.counts with
        findRootOps := st.counts.findRootOps + 2
        otherSteps := st.counts.otherSteps + 4 }
    let rats₁ := aBwd :: aFwd :: st.computedRats
    if rU ≠ rV then
      let fe : ForestEdge :=
        { eid := j.1, u := u, v := v, cost := e.cost, flow := fj, availFwd := aFwd, availBwd := aBwd }
      { df := D.link st.df fe
        flowArr := st.flowArr
        counts :=
          { counts₁ with
            linkOps := counts₁.linkOps + 1
            otherSteps := counts₁.otherSteps + 1 }
        computedRats := rats₁
        computedCosts := st.computedCosts }
    else
      let pathCost := D.pathSum st.df u v
      let cycCostFwd := e.cost - pathCost
      let counts₂ :=
        { counts₁ with
          pathSumOps := counts₁.pathSumOps + 1
          otherSteps := counts₁.otherSteps + 2 }
      let costs₂ := cycCostFwd :: pathCost :: st.computedCosts
      if cycCostFwd ≤ 0 then
        let hitOpt := D.pathMin st.df v u
        let δ := match hitOpt with
          | none => aFwd
          | some hit => min aFwd hit.avail
        let newFlow := fj + δ
        let flowArr₁ := fun k : Fin I.m => if k = j then newFlow else st.flowArr k
        let df₁ := D.pathAdd st.df v u δ
        let counts₃ :=
          { counts₂ with
            pathMinOps := counts₂.pathMinOps + 1
            pathAddOps := counts₂.pathAddOps + 1
            otherSteps := counts₂.otherSteps + 3 }
        let rats₃ :=
          match hitOpt with
          | none => newFlow :: δ :: rats₁
          | some hit => newFlow :: δ :: hit.avail :: rats₁
        let (df₂, flowArr₂, counts₄, rats₄) :=
          removeZeroEdges D I df₁ flowArr₁ counts₃ rats₃ v u (I.m + 1)
        if isIntRat newFlow then
          { df := df₂
            flowArr := flowArr₂
            counts := { counts₄ with otherSteps := counts₄.otherSteps + 1 }
            computedRats := rats₄
            computedCosts := costs₂ }
        else
          let newAFwd : ℚ := (⌈fj⌉ : ℚ) - newFlow
          let newABwd : ℚ := newFlow - (⌊fj⌋ : ℚ)
          let fe : ForestEdge :=
            { eid := j.1, u := u, v := v, cost := e.cost, flow := newFlow,
              availFwd := newAFwd, availBwd := newABwd }
          { df := D.link df₂ fe
            flowArr := flowArr₂
            counts :=
              { counts₄ with
                linkOps := counts₄.linkOps + 1
                otherSteps := counts₄.otherSteps + 3 }
            computedRats := newABwd :: newAFwd :: rats₄
            computedCosts := costs₂ }
      else
        let hitOpt := D.pathMin st.df u v
        let δ := match hitOpt with
          | none => aBwd
          | some hit => min aBwd hit.avail
        let newFlow := fj - δ
        let flowArr₁ := fun k : Fin I.m => if k = j then newFlow else st.flowArr k
        let df₁ := D.pathAdd st.df u v δ
        let counts₃ :=
          { counts₂ with
            pathMinOps := counts₂.pathMinOps + 1
            pathAddOps := counts₂.pathAddOps + 1
            otherSteps := counts₂.otherSteps + 3 }
        let rats₃ :=
          match hitOpt with
          | none => newFlow :: δ :: rats₁
          | some hit => newFlow :: δ :: hit.avail :: rats₁
        let (df₂, flowArr₂, counts₄, rats₄) :=
          removeZeroEdges D I df₁ flowArr₁ counts₃ rats₃ u v (I.m + 1)
        if isIntRat newFlow then
          { df := df₂
            flowArr := flowArr₂
            counts := { counts₄ with otherSteps := counts₄.otherSteps + 1 }
            computedRats := rats₄
            computedCosts := costs₂ }
        else
          let newAFwd : ℚ := (⌈fj⌉ : ℚ) - newFlow
          let newABwd : ℚ := newFlow - (⌊fj⌋ : ℚ)
          let fe : ForestEdge :=
            { eid := j.1, u := u, v := v, cost := e.cost, flow := newFlow,
              availFwd := newAFwd, availBwd := newABwd }
          { df := D.link df₂ fe
            flowArr := flowArr₂
            counts :=
              { counts₄ with
                linkOps := counts₄.linkOps + 1
                otherSteps := counts₄.otherSteps + 3 }
            computedRats := newABwd :: newAFwd :: rats₄
            computedCosts := costs₂ }

/-- Process edges `0, 1, …, k - 1` of `I`. -/
def roundFlowLoop (D : DynForest) (I : Instance) (f : Fin I.m → ℚ) :
    (k : ℕ) → k ≤ I.m → RoundState D I
  | 0, _ =>
    { df := D.init I.n
      flowArr := f
      counts := {}
      computedRats := (List.finRange I.m).map f
      computedCosts := [] }
  | k + 1, hk =>
    let st := roundFlowLoop D I f k (Nat.le_of_succ_le hk)
    roundEdgeStep D I f st ⟨k, hk⟩

/-- The Section 4 rounding algorithm returning the final state (output flow `flowArr`, operation
counts, and computed number traces). -/
def roundFlow (D : DynForest) (I : Instance) (f : Fin I.m → ℚ) : RoundState D I :=
  roundFlowLoop D I f I.m (Nat.le_refl _)

/-! ## Edge and flow invariants -/

/-- Weak edge invariant: `e` corresponds to a fractional edge `j` of `I`, with `e.flow` in
`[⌊f j⌋, ⌈f j⌉]` and exact availabilities summing to `1`. -/
def ForestEdgeWeakInv (I : Instance) (f : Fin I.m → ℚ) (e : ForestEdge) : Prop :=
  ∃ j : Fin I.m,
    e.eid = j.1 ∧
    e.u = (I.edge j).tail ∧
    e.v = (I.edge j).head ∧
    e.cost = (I.edge j).cost ∧
    (¬ ∃ z : ℤ, f j = z) ∧
    (⌊f j⌋ : ℚ) ≤ e.flow ∧ e.flow ≤ (⌈f j⌉ : ℚ) ∧
    e.availFwd = (⌈f j⌉ : ℚ) - e.flow ∧
    e.availBwd = e.flow - (⌊f j⌋ : ℚ)

/-- Strict edge invariant: `e` satisfies `ForestEdgeWeakInv` and both availabilities are
strictly positive (so `e.flow` is fractional). -/
def ForestEdgeStrictInv (I : Instance) (f : Fin I.m → ℚ) (e : ForestEdge) : Prop :=
  ForestEdgeWeakInv I f e ∧ 0 < e.availFwd ∧ 0 < e.availBwd

theorem ForestEdgeWeakInv.avail_bounds {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) :
    0 ≤ e.availFwd ∧ e.availFwd ≤ 1 ∧ 0 ≤ e.availBwd ∧ e.availBwd ≤ 1 ∧
    e.availFwd + e.availBwd = 1 := by
  obtain ⟨j, _, _, _, _, hfrac, hlo, hhi, hfwd, hbwd⟩ := h
  have hlt : (⌊f j⌋ : ℚ) < f j :=
    lt_of_le_of_ne (Int.floor_le (f j)) (fun h => hfrac ⟨⌊f j⌋, h.symm⟩)
  have hceil : (⌈f j⌉ : ℤ) = ⌊f j⌋ + 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith,
    by exact_mod_cast (Int.lt_floor_add_one (f j)).le⟩
  have hdiff : (⌈f j⌉ : ℚ) - (⌊f j⌋ : ℚ) = 1 := by
    rw [hceil]
    push_cast
    ring
  have hsum : e.availFwd + e.availBwd = 1 := by linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, hsum⟩

theorem ForestEdgeWeakInv.eid_lt {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) : e.eid < I.m := by
  obtain ⟨j, heid, _⟩ := h
  exact heid ▸ j.2

theorem ForestEdgeWeakInv.flow_bounds {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) :
    ∃ j : Fin I.m, e.eid = j.1 ∧ |e.flow| ≤ |f j| + 1 := by
  obtain ⟨j, heid, _, _, _, _, hlo, hhi, _, _⟩ := h
  refine ⟨j, heid, ?_⟩
  have h3 : (⌈f j⌉ : ℚ) < f j + 1 := Int.ceil_lt_add_one (f j)
  have h4 : f j - 1 < (⌊f j⌋ : ℚ) := Int.sub_one_lt_floor (f j)
  rw [abs_le]
  constructor
  · have := neg_abs_le (f j)
    linarith
  · have := le_abs_self (f j)
    linarith

theorem ForestEdgeWeakInv.isInt_of_availFwd_zero {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) (hz : e.availFwd = 0) : ∃ z : ℤ, e.flow = z := by
  obtain ⟨j, _, _, _, _, _, _, _, hfwd, _⟩ := h
  exact ⟨⌈f j⌉, by linarith⟩

theorem ForestEdgeWeakInv.isInt_of_availBwd_zero {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) (hz : e.availBwd = 0) : ∃ z : ℤ, e.flow = z := by
  obtain ⟨j, _, _, _, _, _, _, _, _, hbwd⟩ := h
  exact ⟨⌊f j⌋, by linarith⟩

theorem ForestEdgeStrictInv.of_weak_pos {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeWeakInv I f e) (hfwd : 0 < e.availFwd) (hbwd : 0 < e.availBwd) :
    ForestEdgeStrictInv I f e :=
  ⟨h, hfwd, hbwd⟩

theorem ForestEdgeStrictInv.isFrac {I : Instance} {f : Fin I.m → ℚ} {e : ForestEdge}
    (h : ForestEdgeStrictInv I f e) : ¬ ∃ z : ℤ, e.flow = z := by
  obtain ⟨⟨j, _, _, _, _, hfrac, _, _, hfwd, hbwd⟩, hpf, hpb⟩ := h
  rintro ⟨z, hz⟩
  have h1 : (⌊f j⌋ : ℚ) < (z : ℚ) := by linarith
  have h2 : (z : ℚ) < (⌈f j⌉ : ℚ) := by linarith
  have hz1 : ⌊f j⌋ + 1 ≤ z := Int.lt_iff_add_one_le.mp (by exact_mod_cast h1)
  have hz2 : z + 1 ≤ ⌈f j⌉ := Int.lt_iff_add_one_le.mp (by exact_mod_cast h2)
  have hlt : (⌊f j⌋ : ℚ) < f j :=
    lt_of_le_of_ne (Int.floor_le (f j)) (fun h => hfrac ⟨⌊f j⌋, h.symm⟩)
  have hceil : (⌈f j⌉ : ℤ) = ⌊f j⌋ + 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith,
    by exact_mod_cast (Int.lt_floor_add_one (f j)).le⟩
  omega

/-- The actual flow of edge `k` across the array `flowArr` and dynamic forest `F`: if `k` is
currently active in `F`, its value is `e.flow` stored in `F`; otherwise it is `flowArr k`. -/
def actualFlow {I : Instance} (F : MathForest) (flowArr : Fin I.m → ℚ) (k : Fin I.m) : ℚ :=
  match F.edges.find? fun e => e.eid == k.1 with
  | none => flowArr k
  | some e => e.flow

theorem actualFlow_of_mem {I : Instance} {F : MathForest} (hnd : (F.edges.map ForestEdge.eid).Nodup)
    (flowArr : Fin I.m → ℚ) {e : ForestEdge} (he : e ∈ F.edges) {k : Fin I.m} (hk : e.eid = k.1) :
    actualFlow F flowArr k = e.flow := by
  unfold actualFlow
  have hfind : F.edges.find? (fun x => x.eid == k.1) = some e := by
    have aux : ∀ es : List ForestEdge, (es.map ForestEdge.eid).Nodup → e ∈ es →
        es.find? (fun x => x.eid == k.1) = some e := by
      intro es hnd' he'
      induction es with
      | nil => simp at he'
      | cons z zs ih =>
        rw [List.map_cons, List.nodup_cons] at hnd'
        simp only [List.find?]
        rcases List.mem_cons.mp he' with rfl | he_zs
        · simp [hk]
        · have hne : z.eid ≠ k.1 := fun h => hnd'.1 (h ▸ hk ▸ List.mem_map_of_mem he_zs)
          have hbeq : (z.eid == k.1) = false := beq_eq_false_iff_ne.mpr hne
          rw [hbeq]
          exact ih hnd'.2 he_zs
    exact aux F.edges hnd he
  rw [hfind]

theorem actualFlow_of_not_mem {I : Instance} {F : MathForest}
    (flowArr : Fin I.m → ℚ) {k : Fin I.m} (hnot : k.1 ∉ F.edges.map ForestEdge.eid) :
    actualFlow F flowArr k = flowArr k := by
  unfold actualFlow
  have hnone : F.edges.find? (fun x => x.eid == k.1) = none := by
    rw [List.find?_eq_none]
    intro e he
    simp only [beq_iff_eq]
    intro h
    exact hnot (h ▸ List.mem_map_of_mem he)
  rw [hnone]

theorem actualFlow_sameState {I : Instance} {F₁ F₂ : MathForest} (h : F₁.SameState F₂)
    (hV₁ : F₁.Valid) (flowArr : Fin I.m → ℚ) (k : Fin I.m) :
    actualFlow F₁ flowArr k = actualFlow F₂ flowArr k := by
  have hV₂ := h.valid_iff.mp hV₁
  by_cases hm : k.1 ∈ F₁.edges.map ForestEdge.eid
  · rw [List.mem_map] at hm
    obtain ⟨e, he, hk⟩ := hm
    have he₂ : e ∈ F₂.edges := h.2.subset he
    rw [actualFlow_of_mem hV₁.2.1 flowArr he hk, actualFlow_of_mem hV₂.2.1 flowArr he₂ hk]
  · have hm₂ : k.1 ∉ F₂.edges.map ForestEdge.eid := fun hm' => by
      rw [List.mem_map] at hm'
      obtain ⟨e, he, hk⟩ := hm'
      exact hm (List.mem_map.mpr ⟨e, h.2.symm.subset he, hk⟩)
    rw [actualFlow_of_not_mem flowArr hm, actualFlow_of_not_mem flowArr hm₂]

/-- Specification of `removeZeroEdges`: proves fuel non-exhaustion, exact `Cut` and `PathMin`
counts, removal of all zero-availability edges on `steps`, preservation of off-path edges and
`actualFlow`, disconnection if a zero-availability edge existed, and fixed-point/magnitude
closure. -/
theorem removeZeroEdges_spec {D : DynForest} (hSpec : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} :
    ∀ fuel df flowArr counts rats a b steps,
      D.Inv df →
      findSteps (D.toForest df).edges a b = some steps →
      (D.toForest df).edges.length < fuel →
      (∀ e ∈ (D.toForest df).edges, ForestEdgeWeakInv I f e) →
      (∀ s ∈ steps, 0 ≤ s.dirAvail ∧ 0 < s.flip.dirAvail) →
      let (df', flowArr', counts', rats') :=
        removeZeroEdges D I df flowArr counts rats a b fuel
      D.Inv df' ∧
      (∀ k : Fin I.m, actualFlow (D.toForest df') flowArr' k =
        actualFlow (D.toForest df) flowArr k) ∧
      (∀ e ∈ (D.toForest df').edges, e ∈ (D.toForest df).edges) ∧
      (∀ e ∈ (D.toForest df).edges, (∀ s ∈ steps, s.edge ≠ e) → e ∈ (D.toForest df').edges) ∧
      (∀ s ∈ steps, s.dirAvail = 0 →
        s.edge.eid ∉ (D.toForest df').edges.map ForestEdge.eid) ∧
      (∀ s ∈ steps, s.edge ∈ (D.toForest df').edges → ForestEdgeStrictInv I f s.edge) ∧
      (∀ k : Fin I.m, k.1 ∉ (D.toForest df).edges.map ForestEdge.eid → flowArr' k = flowArr k) ∧
      (∀ k : Fin I.m, k.1 ∈ (D.toForest df).edges.map ForestEdge.eid →
        k.1 ∉ (D.toForest df').edges.map ForestEdge.eid → ∃ z : ℤ, flowArr' k = z) ∧
      ((∃ s ∈ steps, s.dirAvail = 0) → ¬ (D.toForest df').SameComp a b) ∧
      counts'.findRootOps = counts.findRootOps ∧
      counts'.linkOps = counts.linkOps ∧
      counts'.pathAddOps = counts.pathAddOps ∧
      counts'.pathSumOps = counts.pathSumOps ∧
      (D.toForest df').edges.length ≤ (D.toForest df).edges.length ∧
      counts'.cutOps + (D.toForest df').edges.length =
        counts.cutOps + (D.toForest df).edges.length ∧
      counts'.pathMinOps + 2 * counts.cutOps = counts.pathMinOps + 2 * counts'.cutOps + 1 ∧
      counts'.otherSteps + 5 * counts.cutOps ≤ counts.otherSteps + 5 * counts'.cutOps + 2 ∧
      (∀ P : ℕ,
        (∀ e ∈ (D.toForest df).edges, IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧
          IsFixedPoint P e.availBwd) →
        (∀ q ∈ rats, IsFixedPoint P q) →
        ∀ q ∈ rats', IsFixedPoint P q) ∧
      (∀ M : ℚ,
        (∀ j, |f j| + 1 ≤ M) →
        (∀ q ∈ rats, |q| ≤ M) →
        ∀ q ∈ rats', |q| ≤ M) ∧
      (∀ k : Fin I.m, flowArr' k = flowArr k ∨
        ∃ e ∈ (D.toForest df).edges, e.eid = k.1 ∧ flowArr' k = e.flow) := by
  intro fuel
  induction fuel with
  | zero =>
    intro df flowArr counts rats a b steps _ _ hfuel
    omega
  | succ fuel ih =>
    intro df flowArr counts rats a b steps hInv hfs hfuel hWeak hPath
    have hV : (D.toForest df).Valid := hSpec.2.1 df hInv
    obtain ⟨hw, _⟩ := findSteps_sound hV.2.1 hfs
    have hconn : (D.toForest df).SameComp a b := ⟨_, hw.to_isWalk⟩
    have hPM_eq : D.pathMin df a b = (D.toForest df).pathMin a b :=
      hSpec.2.2.2.2.2.2.1 df a b hInv hconn
    dsimp only
    rw [removeZeroEdges]
    rw [hPM_eq]
    unfold MathForest.pathMin
    rw [hfs, Option.bind_some]
    cases hmin : stepsMinHit steps with
    | none =>
      have hnil : steps = [] := stepsMinHit_eq_none_iff.mp hmin
      subst hnil
      dsimp only
      refine ⟨hInv, fun _ => rfl, fun _ h => h, fun _ he _ => he, ?_, ?_, fun _ _ => rfl,
        fun k hk1 hk2 => absurd hk1 hk2, ?_, rfl, rfl, rfl, rfl, Nat.le_refl _, rfl,
        by omega, by omega, fun _ _ hR => hR, fun _ _ hR => hR, fun _ => Or.inl rfl⟩
      · intro s hs; simp at hs
      · intro s hs; simp at hs
      · rintro ⟨s, hs, _⟩; simp at hs
    | some hit =>
      dsimp only
      obtain ⟨pre, s, post, hsplit, hs_hit, hpre_avail, hpost_avail, hV_cut, hmem_cut,
        hkeep_cut, hlen_cut, hfs_pre, hfs_post, hconn_pre, hconn_post, hdisc_cut⟩ :=
        MathForest.cut_of_pathMin hV hfs hmin
      have hs_in_steps : s ∈ steps := by rw [hsplit]; simp
      have hdir_nn : 0 ≤ hit.avail := by
        have := (hPath s hs_in_steps).1
        rw [← hs_hit]
        exact this
      by_cases hpos : hit.avail > 0
      · rw [ite_eq_left hpos]
        dsimp only
        have hstep_pos : ∀ t ∈ steps, 0 < t.dirAvail := by
          intro t ht
          rw [hsplit, List.mem_append, List.mem_cons] at ht
          rcases ht with ht | rfl | ht
          · exact lt_trans hpos (hpre_avail t ht)
          · exact lt_of_lt_of_le hpos (by rw [← hs_hit]; rfl)
          · exact lt_of_lt_of_le hpos (hpost_avail t ht)
        refine ⟨hInv, fun _ => rfl, fun _ h => h, fun _ he _ => he, ?_, ?_, fun _ _ => rfl,
          fun k hk1 hk2 => absurd hk1 hk2, ?_, rfl, rfl, rfl, rfl, Nat.le_refl _, rfl,
          by omega, by omega, ?_, ?_, fun _ => Or.inl rfl⟩
        · intro t ht ht0
          exact absurd ht0 (ne_of_gt (hstep_pos t ht))
        · intro t ht _
          have h1 := hstep_pos t ht
          have h2 := (hPath t ht).2
          have hw_t := hWeak t.edge (hw.mem_edges t ht)
          rcases tf : t.fwd with _ | _
          · simp [PathStep.dirAvail, PathStep.flip, tf] at h1 h2
            exact ⟨hw_t, h2, h1⟩
          · simp [PathStep.dirAvail, PathStep.flip, tf] at h1 h2
            exact ⟨hw_t, h1, h2⟩
        · rintro ⟨t, ht, ht0⟩
          exact absurd ht0 (ne_of_gt (hstep_pos t ht))
        · intro P hFP_df hFP_rats q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · have hfp := hFP_df s.edge (hw.mem_edges s hs_in_steps)
            have hav : hit.avail = s.dirAvail := by rw [← hs_hit]; rfl
            rw [hav]
            cases hf : s.fwd <;> simp [PathStep.dirAvail, hf, hfp.2.1, hfp.2.2]
          · exact hFP_rats q hq
        · intro M hM hM_rats q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · have hs_weak := hWeak s.edge (hw.mem_edges s hs_in_steps)
            have hb := hs_weak.avail_bounds
            have hav : hit.avail = s.dirAvail := by rw [← hs_hit]; rfl
            have h01 : 0 ≤ hit.avail ∧ hit.avail ≤ 1 := by
              rw [hav]
              cases hf : s.fwd <;> simp [PathStep.dirAvail, hf, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1]
            have h1M : (1 : ℚ) ≤ M := by
              have := hM ⟨s.edge.eid, hs_weak.eid_lt⟩
              have hnn : (0 : ℚ) ≤ |f ⟨s.edge.eid, hs_weak.eid_lt⟩| := abs_nonneg _
              linarith
            rw [abs_of_nonneg h01.1]
            linarith
          · exact hM_rats q hq
      · rw [ite_eq_right hpos]
        have hzero : hit.avail = 0 := le_antisymm (le_of_not_gt hpos) hdir_nn
        have hcut_spec := hSpec.2.2.2.2.1 df hit.x hit.y hInv
        obtain ⟨hInv₁, hSame₁⟩ := hcut_spec
        have hV₁ : (D.toForest (D.cut df hit.x hit.y)).Valid := hSpec.2.1 _ hInv₁
        have hs_mem : s.edge ∈ (D.toForest df).edges := hw.mem_edges s hs_in_steps
        have hs_eid : s.edge.eid = hit.eid := by rw [← hs_hit]; rfl
        have hs_flow : s.edge.flow = hit.flow := by rw [← hs_hit]; rfl
        have hs_weak := hWeak s.edge hs_mem
        have hs_int : ∃ z : ℤ, hit.flow = z := by
          rw [← hs_flow]
          have hav : s.dirAvail = 0 := by rw [← hs_hit] at hzero; exact hzero
          cases hf : s.fwd
          · simp [PathStep.dirAvail, hf] at hav
            exact hs_weak.isInt_of_availBwd_zero hav
          · simp [PathStep.dirAvail, hf] at hav
            exact hs_weak.isInt_of_availFwd_zero hav
        let flowArr₁ := fun k : Fin I.m => if k.1 = hit.eid then hit.flow else flowArr k
        let df₁ := D.cut df hit.x hit.y
        let counts₁ : RoundCounts :=
          { counts with
            pathMinOps := counts.pathMinOps + 1
            cutOps := counts.cutOps + 1
            otherSteps := counts.otherSteps + 3 }
        let rats₁ := hit.flow :: hit.avail :: rats
        have hact₁ : ∀ k : Fin I.m,
            actualFlow (D.toForest df₁) flowArr₁ k = actualFlow (D.toForest df) flowArr k := by
          intro k
          rw [actualFlow_sameState hSame₁ hV₁ flowArr₁ k]
          by_cases hke : k.1 = hit.eid
          · have hnot_mem : k.1 ∉ ((D.toForest df).cut hit.x hit.y).edges.map ForestEdge.eid := by
              intro hm
              rw [List.mem_map] at hm
              obtain ⟨e, he, heq⟩ := hm
              exact (hmem_cut e he).2 (heq.trans hke)
            rw [actualFlow_of_not_mem flowArr₁ hnot_mem]
            dsimp [flowArr₁]
            rw [ite_eq_left hke, ← hs_flow]
            exact (actualFlow_of_mem hV.2.1 flowArr hs_mem (hs_eid.trans hke.symm)).symm
          · have hflow_k : flowArr₁ k = flowArr k := by
              dsimp [flowArr₁]; rw [ite_eq_right hke]
            by_cases hm : k.1 ∈ (D.toForest df).edges.map ForestEdge.eid
            · rw [List.mem_map] at hm
              obtain ⟨e, he, heq⟩ := hm
              have he_cut : e ∈ ((D.toForest df).cut hit.x hit.y).edges :=
                hkeep_cut e he (heq.symm ▸ hke)
              rw [actualFlow_of_mem hV_cut.2.1 flowArr₁ he_cut heq,
                actualFlow_of_mem hV.2.1 flowArr he heq]
            · have hnot_cut : k.1 ∉ ((D.toForest df).cut hit.x hit.y).edges.map ForestEdge.eid := by
                intro hm'
                rw [List.mem_map] at hm'
                obtain ⟨e, he, heq⟩ := hm'
                exact hm (List.mem_map.mpr ⟨e, (hmem_cut e he).1, heq⟩)
              rw [actualFlow_of_not_mem flowArr₁ hnot_cut, actualFlow_of_not_mem flowArr hm, hflow_k]
        have hlen_df₁ : (D.toForest df₁).edges.length < fuel := by
          have hlen_eq : (D.toForest df₁).edges.length =
              ((D.toForest df).cut hit.x hit.y).edges.length := hSame₁.2.length_eq
          omega
        have hfs_pre₁ : findSteps (D.toForest df₁).edges a hit.x = some pre := by
          rw [hSame₁.findSteps_eq hV₁]
          exact hfs_pre
        have hmem_df₁ : ∀ e, e ∈ (D.toForest df₁).edges ↔
            e ∈ (D.toForest df).edges ∧ e.eid ≠ hit.eid := by
          intro e
          constructor
          · intro he
            exact hmem_cut e (hSame₁.2.subset he)
          · rintro ⟨he, hne⟩
            exact hSame₁.2.symm.subset (hkeep_cut e he hne)
        have hWeak₁ : ∀ e ∈ (D.toForest df₁).edges, ForestEdgeWeakInv I f e :=
          fun e he => hWeak e (hmem_df₁ e |>.mp he).1
        have hPath_pre : ∀ t ∈ pre, 0 ≤ t.dirAvail ∧ 0 < t.flip.dirAvail :=
          fun t ht => hPath t (by rw [hsplit]; simp [ht])
        let res₂ := removeZeroEdges D I df₁ flowArr₁ counts₁ rats₁ a hit.x fuel
        obtain ⟨hInv₂, hact₂, hsub₂, hkeep₂, hrem₂, hstrict₂, hflow_out₂, hflow_int₂, _,
          hc₂_fr, hc₂_lk, hc₂_pa, hc₂_ps, hlen₂, hcut₂, hpm₂, hos₂, hFP_rats₂, hM_rats₂, hcases₂⟩ :=
          ih df₁ flowArr₁ counts₁ rats₁ a hit.x pre
            hInv₁ hfs_pre₁ hlen_df₁ hWeak₁ hPath_pre
        -- Now verify `post` survives completely into `res₂.1`!
        have hV₂ : (D.toForest res₂.1).Valid := hSpec.2.1 _ hInv₂
        have hpost_in_df₁ : ∀ t ∈ post, t.edge ∈ (D.toForest df₁).edges := by
          intro t ht
          obtain ⟨hw_post, _⟩ := findSteps_sound hV_cut.2.1 hfs_post
          exact hSame₁.2.symm.subset (hw_post.mem_edges t ht)
        have hpost_not_pre : ∀ t ∈ post, ∀ u ∈ pre, u.edge ≠ t.edge := by
          intro t ht u hu heq
          have hnd_steps : (steps.map PathStep.toRaw).Nodup := (findSteps_sound hV.2.1 hfs).2
          rw [hsplit, List.map_append, List.map_cons] at hnd_steps
          have hdisj := List.disjoint_of_nodup_append hnd_steps
          have hm1 : u.edge.toRaw ∈ pre.map PathStep.toRaw := List.mem_map_of_mem hu
          have hm2 : u.edge.toRaw ∈ s.edge.toRaw :: post.map PathStep.toRaw :=
            List.mem_cons_of_mem _ (heq ▸ List.mem_map_of_mem ht)
          exact hdisj hm1 hm2
        have hpost_in_df₂ : ∀ t ∈ post, t.edge ∈ (D.toForest res₂.1).edges := fun t ht =>
          hkeep₂ t.edge (hpost_in_df₁ t ht) (fun u hu => hpost_not_pre t ht u hu)
        have hfs_post₂ : findSteps (D.toForest res₂.1).edges hit.y b = some post := by
          obtain ⟨hw_post, hnd_post⟩ := findSteps_sound hV_cut.2.1 hfs_post
          exact MathForest.findSteps_eq_of_isStepWalk hV₂ (hw_post.mono_of_mem hpost_in_df₂) hnd_post
        have hlen_df₂ : (D.toForest res₂.1).edges.length < fuel := lt_of_le_of_lt hlen₂ hlen_df₁
        have hWeak₂ : ∀ e ∈ (D.toForest res₂.1).edges, ForestEdgeWeakInv I f e :=
          fun e he => hWeak₁ e (hsub₂ e he)
        have hPath_post : ∀ t ∈ post, 0 ≤ t.dirAvail ∧ 0 < t.flip.dirAvail :=
          fun t ht => hPath t (by rw [hsplit]; simp [ht])
        obtain ⟨hInv₃, hact₃, hsub₃, hkeep₃, hrem₃, hstrict₃, hflow_out₃, hflow_int₃, _,
          hc₃_fr, hc₃_lk, hc₃_pa, hc₃_ps, hlen₃, hcut₃, hpm₃, hos₃, hFP_rats₃, hM_rats₃, hcases₃⟩ :=
          ih res₂.1 res₂.2.1 res₂.2.2.1 res₂.2.2.2 hit.y b post
            hInv₂ hfs_post₂ hlen_df₂ hWeak₂ hPath_post
        refine ⟨hInv₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro k; exact (hact₃ k).trans ((hact₂ k).trans (hact₁ k))
        · intro e he; exact (hmem_df₁ e |>.mp (hsub₂ e (hsub₃ e he))).1
        · intro e he hnot
          have he_ne_s : e ≠ s.edge := fun heq => hnot s hs_in_steps heq.symm
          have heid_ne : e.eid ≠ hit.eid := fun heid => by
            apply he_ne_s
            have aux : ∀ es : List ForestEdge, (es.map ForestEdge.eid).Nodup →
                e ∈ es → s.edge ∈ es → e = s.edge := by
              intro es hnd' h1' h2'
              induction es with
              | nil => simp at h1'
              | cons z zs ihz =>
                rw [List.map_cons, List.nodup_cons] at hnd'
                rcases List.mem_cons.mp h1' with h1 | h1 <;>
                  rcases List.mem_cons.mp h2' with h2 | h2
                · exact h1.trans h2.symm
                · exact absurd (h1 ▸ (heid.trans hs_eid.symm) ▸ List.mem_map_of_mem h2) hnd'.1
                · exact absurd (h2 ▸ (heid.trans hs_eid.symm).symm ▸ List.mem_map_of_mem h1) hnd'.1
                · exact ihz hnd'.2 h1 h2
            exact aux (D.toForest df).edges hV.2.1 he hs_mem
          have he₁ : e ∈ (D.toForest df₁).edges := (hmem_df₁ e).mpr ⟨he, heid_ne⟩
          have he₂ : e ∈ (D.toForest res₂.1).edges :=
            hkeep₂ e he₁ (fun u hu => hnot u (by rw [hsplit]; simp [hu]))
          exact hkeep₃ e he₂ (fun u hu => hnot u (by rw [hsplit]; simp [hu]))
        · intro t ht ht0 hm
          rw [hsplit, List.mem_append, List.mem_cons] at ht
          rcases ht with ht_pre | rfl | ht_post
          · apply hrem₂ t ht_pre ht0
            rw [List.mem_map] at hm ⊢
            obtain ⟨e, he, heq⟩ := hm
            exact ⟨e, hsub₃ e he, heq⟩
          · rw [List.mem_map] at hm
            obtain ⟨e, he, heq⟩ := hm
            exact (hmem_df₁ e |>.mp (hsub₂ e (hsub₃ e he))).2 (heq.trans hs_eid)
          · exact hrem₃ t ht_post ht0 hm
        · intro t ht ht_in
          rw [hsplit, List.mem_append, List.mem_cons] at ht
          rcases ht with ht_pre | rfl | ht_post
          · exact hstrict₂ t ht_pre (hsub₃ t.edge ht_in)
          · exfalso
            exact (hmem_df₁ t.edge |>.mp (hsub₂ t.edge (hsub₃ t.edge ht_in))).2 hs_eid
          · exact hstrict₃ t ht_post ht_in
        · intro k hnot
          have hke : k.1 ≠ hit.eid := fun h =>
            hnot (List.mem_map.mpr ⟨s.edge, hs_mem, hs_eid.trans h.symm⟩)
          have hnot₁ : k.1 ∉ (D.toForest df₁).edges.map ForestEdge.eid := fun hm => by
            rw [List.mem_map] at hm
            obtain ⟨e, he, heq⟩ := hm
            exact hnot (List.mem_map.mpr ⟨e, (hmem_df₁ e |>.mp he).1, heq⟩)
          have hnot₂ : k.1 ∉ (D.toForest res₂.1).edges.map ForestEdge.eid := fun hm => by
            rw [List.mem_map] at hm
            obtain ⟨e, he, heq⟩ := hm
            exact hnot₁ (List.mem_map.mpr ⟨e, hsub₂ e he, heq⟩)
          rw [hflow_out₃ k hnot₂, hflow_out₂ k hnot₁]
          dsimp [flowArr₁]
          rw [ite_eq_right hke]
        · intro k hk_in hk_out
          by_cases hke : k.1 = hit.eid
          · have hnot₁ : k.1 ∉ (D.toForest df₁).edges.map ForestEdge.eid := fun hm => by
              rw [List.mem_map] at hm
              obtain ⟨e, he, heq⟩ := hm
              exact (hmem_df₁ e |>.mp he).2 (heq.trans hke)
            have hnot₂ : k.1 ∉ (D.toForest res₂.1).edges.map ForestEdge.eid := fun hm => by
              rw [List.mem_map] at hm
              obtain ⟨e, he, heq⟩ := hm
              exact hnot₁ (List.mem_map.mpr ⟨e, hsub₂ e he, heq⟩)
            rw [hflow_out₃ k hnot₂, hflow_out₂ k hnot₁]
            dsimp [flowArr₁]
            rw [ite_eq_left hke]
            exact hs_int
          · have hk₁ : k.1 ∈ (D.toForest df₁).edges.map ForestEdge.eid := by
              rw [List.mem_map] at hk_in ⊢
              obtain ⟨e, he, heq⟩ := hk_in
              exact ⟨e, (hmem_df₁ e).mpr ⟨he, heq.symm ▸ hke⟩, heq⟩
            by_cases hk₂ : k.1 ∈ (D.toForest res₂.1).edges.map ForestEdge.eid
            · exact hflow_int₃ k hk₂ hk_out
            · rw [hflow_out₃ k hk₂]
              exact hflow_int₂ k hk₁ hk₂
        · intro _ ⟨q, hq⟩
          obtain ⟨q', hq', hq'_nd, _⟩ := exists_nodup_walk_of_walk hq
          have hsub_q' : ∀ z ∈ q', z ∈ (D.toForest df₁).rawEdges := by
            intro z hz
            have hz_mem := hq'.subset z hz
            unfold MathForest.rawEdges at hz_mem ⊢
            rw [List.mem_map] at hz_mem ⊢
            obtain ⟨e, he, rfl⟩ := hz_mem
            exact ⟨e, hsub₂ e (hsub₃ e he), rfl⟩
          have hq₁ : IsWalk (D.toForest df₁).rawEdges a b q' := hq'.mono_of_mem hsub_q'
          have hsc₁ : (D.toForest df₁).SameComp a b := ⟨q', hq₁⟩
          rw [hSame₁.sameComp_iff] at hsc₁
          exact hdisc_cut hsc₁
        · rw [hc₃_fr, hc₂_fr]
        · rw [hc₃_lk, hc₂_lk]
        · rw [hc₃_pa, hc₂_pa]
        · rw [hc₃_ps, hc₂_ps]
        · have h1 : (D.toForest df₁).edges.length = ((D.toForest df).cut hit.x hit.y).edges.length :=
            hSame₁.2.length_eq
          exact le_trans hlen₃ (le_trans hlen₂ (by omega))
        · have h1 : (D.toForest df₁).edges.length = ((D.toForest df).cut hit.x hit.y).edges.length :=
            hSame₁.2.length_eq
          let res₃ := removeZeroEdges D I res₂.1 res₂.2.1 res₂.2.2.1 res₂.2.2.2 hit.y b fuel
          change res₃.2.2.1.cutOps + (D.toForest res₃.1).edges.length =
            counts.cutOps + (D.toForest df).edges.length
          change res₂.2.2.1.cutOps + (D.toForest res₂.1).edges.length =
            counts₁.cutOps + (D.toForest df₁).edges.length at hcut₂
          change res₃.2.2.1.cutOps + (D.toForest res₃.1).edges.length =
            res₂.2.2.1.cutOps + (D.toForest res₂.1).edges.length at hcut₃
          have hc1 : counts₁.cutOps = counts.cutOps + 1 := rfl
          omega
        · let res₃ := removeZeroEdges D I res₂.1 res₂.2.1 res₂.2.2.1 res₂.2.2.2 hit.y b fuel
          change res₃.2.2.1.pathMinOps + 2 * counts.cutOps =
            counts.pathMinOps + 2 * res₃.2.2.1.cutOps + 1
          change res₂.2.2.1.pathMinOps + 2 * counts₁.cutOps =
            counts₁.pathMinOps + 2 * res₂.2.2.1.cutOps + 1 at hpm₂
          change res₃.2.2.1.pathMinOps + 2 * res₂.2.2.1.cutOps =
            res₂.2.2.1.pathMinOps + 2 * res₃.2.2.1.cutOps + 1 at hpm₃
          have hc1 : counts₁.cutOps = counts.cutOps + 1 := rfl
          have hp1 : counts₁.pathMinOps = counts.pathMinOps + 1 := rfl
          omega
        · let res₃ := removeZeroEdges D I res₂.1 res₂.2.1 res₂.2.2.1 res₂.2.2.2 hit.y b fuel
          change res₃.2.2.1.otherSteps + 5 * counts.cutOps ≤
            counts.otherSteps + 5 * res₃.2.2.1.cutOps + 2
          change res₂.2.2.1.otherSteps + 5 * counts₁.cutOps ≤
            counts₁.otherSteps + 5 * res₂.2.2.1.cutOps + 2 at hos₂
          change res₃.2.2.1.otherSteps + 5 * res₂.2.2.1.cutOps ≤
            res₂.2.2.1.otherSteps + 5 * res₃.2.2.1.cutOps + 2 at hos₃
          have hc1 : counts₁.cutOps = counts.cutOps + 1 := rfl
          have ho1 : counts₁.otherSteps = counts.otherSteps + 3 := rfl
          omega
        · intro P hFP_df hFP_rats
          have hFP_df₁ : ∀ e ∈ (D.toForest df₁).edges,
              IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd :=
            fun e he => hFP_df e (hmem_df₁ e |>.mp he).1
          have hFP_hit_flow : IsFixedPoint P hit.flow := by
            rw [← hs_flow]
            exact (hFP_df s.edge hs_mem).1
          have hFP_hit_avail : IsFixedPoint P hit.avail := by
            rw [hzero]
            exact isFixedPoint_int P 0
          have hFP_rats₁ : ∀ q ∈ rats₁, IsFixedPoint P q := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hFP_hit_flow
            · rcases List.mem_cons.mp hq with rfl | hq
              · exact hFP_hit_avail
              · exact hFP_rats q hq
          have hFP_df₂ : ∀ e ∈ (D.toForest res₂.1).edges,
              IsFixedPoint P e.flow ∧ IsFixedPoint P e.availFwd ∧ IsFixedPoint P e.availBwd :=
            fun e he => hFP_df₁ e (hsub₂ e he)
          exact hFP_rats₃ P hFP_df₂ (hFP_rats₂ P hFP_df₁ hFP_rats₁)
        · intro M hM hM_rats
          have hM_hit_flow : |hit.flow| ≤ M := by
            rw [← hs_flow]
            obtain ⟨j, _, hfb⟩ := hs_weak.flow_bounds
            exact le_trans hfb (hM j)
          have hM_hit_avail : |hit.avail| ≤ M := by
            rw [hzero, abs_zero]
            have := hM ⟨s.edge.eid, hs_weak.eid_lt⟩
            have : (0 : ℚ) ≤ |f ⟨s.edge.eid, hs_weak.eid_lt⟩| := abs_nonneg _
            linarith
          have hM_rats₁ : ∀ q ∈ rats₁, |q| ≤ M := by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hM_hit_flow
            · rcases List.mem_cons.mp hq with rfl | hq
              · exact hM_hit_avail
              · exact hM_rats q hq
          exact hM_rats₃ M hM (hM_rats₂ M hM hM_rats₁)
        · intro k
          rcases hcases₃ k with hk3 | ⟨e, he, heid, hflow⟩
          · rcases hcases₂ k with hk2 | ⟨e, he, heid, hflow⟩
            · have hk2' : (removeZeroEdges D I res₂.1 res₂.2.1 res₂.2.2.1 res₂.2.2.2 hit.y b fuel).2.1 k =
                  flowArr₁ k := hk3.trans hk2
              rw [hk2']
              dsimp [flowArr₁]
              by_cases hke : k.1 = hit.eid
              · rw [ite_eq_left hke]
                exact Or.inr ⟨s.edge, hs_mem, hs_eid.trans hke.symm, hs_flow.symm⟩
              · rw [ite_eq_right hke]
                exact Or.inl rfl
            · exact Or.inr ⟨e, (hmem_df₁ e |>.mp he).1, heid, hk3.trans hflow⟩
          · exact Or.inr ⟨e, (hmem_df₁ e |>.mp (hsub₂ e he)).1, heid, hflow⟩

end MinCostFlow.Rounding

