module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Rounding.DynForest

/-!
# Machine interface for the rounding dynamic forest

Lemma 4.1 (page 13) uses the dynamic forest operations specified by
`Rounding.DynForest.IsSpec`. This file gives their machine layouts
and a `WordRAM.DataStructure` contract, including signed fit conditions.
The abstract state is exactly `D.State`; no forest correctness result is
made a field of a state. The separate premise `D.IsSpec` supplies those
results. A link-cut implementation can use its own local representation
and amortization potential through `WordRAM.DSRep`.

All calls end in the heap pointer; operations begin with a handle.
Init is `[n,L,P,heap]`. It carries the block width and scale for subsequent calls. Operation codes 0--5 are FindRoot, Link, Cut,
PathAdd, PathMin and PathSum. Their other arguments are respectively
`[v]`, `[edgeRecord]`, `[u,v]`, `[u,v,deltaBlock]`, `[u,v]`, `[u,v]`.
Only Init, FindRoot, PathMin and PathSum write public answers. A scalar
uses `L` limbs of `h` bits at precision `P`; costs and PathSum use
signed integer blocks at precision zero. A forest edge is `[eid,u,v]`
followed by four blocks: integer cost, flow, forward and backward
availability. PathMin returns `[0]` for none, or `[1,eid,x,y]` followed
by availability and flow blocks for a hit. Fits checks are numerical
range checks on the exact mathematical operation, not correctness
assumptions about an implementation.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Exact rational decoding of a fixed-point block. -/
def readRat (mem : ℕ → ℕ) (a h L P : ℕ) : ℚ :=
  (Num.intVal mem a h L : ℚ)/(2 : ℚ)^P

/-- Valid limbs with the specified rational decoding. -/
def RatAt (mem : ℕ → ℕ) (a h L P : ℕ) (x : ℚ) : Prop :=
  Num.Valid mem a h L ∧ readRat mem a h L P = x

/-- A rational fits when its scaled value is an integer in the signed range. -/
def RatFits (h L P : ℕ) (x : ℚ) : Prop :=
  ∃ z : ℤ, Num.Fits h L z ∧ x = (z : ℚ)/(2 : ℚ)^P

/-- The input layout for Link. -/
def ForestEdgeAt (mem : ℕ → ℕ) (a h L P : ℕ) (e : ForestEdge) : Prop :=
  ListAt mem a [e.eid,e.u,e.v] ∧
    Num.Valid mem (a+3) h L ∧ Num.intVal mem (a+3) h L = e.cost ∧
    RatAt mem (a+3+L) h L P e.flow ∧
    RatAt mem (a+3+2*L) h L P e.availFwd ∧
    RatAt mem (a+3+3*L) h L P e.availBwd

/-- The tagged PathMin output, with the source's exact tie choice. -/
def PathHitAt (mem : ℕ → ℕ) (a h L P : ℕ) : Option PathHit → Prop
  | none => mem a = 0
  | some hit => ListAt mem a [1,hit.eid,hit.x,hit.y] ∧
      RatAt mem (a+4) h L P hit.avail ∧ RatAt mem (a+4+L) h L P hit.flow

/-- Every payload in a forest fits the selected representation. -/
def ForestFits (D : DynForest) (h L P : ℕ) (s : D.State) : Prop :=
  ∀ e ∈ (D.toForest s).edges,
    Num.Fits h L e.cost ∧ RatFits h L P e.flow ∧
      RatFits h L P e.availFwd ∧ RatFits h L P e.availBwd

/-- The dynamic-forest contract. Its semantics are exactly the operations
of `DynForest`, with the preconditions from `DynForest.IsSpec`.
`rate n` is an amortized operation bound (including multiword arithmetic),
and allocation is an implementation space bound. WordRAM's `DSRep`
handles locality, heap framing and amortization for every operation. -/
def forestMachineContract (D : DynForest) (w h L P : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) : DataStructure D.State where
  initPre args _ := ∃ n heap, args = [n,L,P,heap]
  initPost args _ s _ := s = D.init (args.getD 0 0)
  initCost args _ := rate (args.getD 0 0)*(args.getD 0 0+1)
  initSpace args _ := allocation 6 args
  pre i s args mem := D.Inv s ∧ ForestFits D h L P s ∧
    match i with
    | 0 => ∃ b v heap, args = [b,v,heap] ∧ v < (D.toForest s).n
    | 1 => ∃ b a heap e, args = [b,a,heap] ∧ a+3+4*L ≤ heap ∧
        ForestEdgeAt mem a h L P e ∧ e.eid < 2^w ∧ e.u < (D.toForest s).n ∧ e.v < (D.toForest s).n ∧
        ¬ (D.toForest s).SameComp e.u e.v ∧
        (∀ e' ∈ (D.toForest s).edges, e'.eid ≠ e.eid) ∧
        ForestFits D h L P (D.link s e)
    | 2 => ∃ b u v heap, args = [b,u,v,heap] ∧ ForestFits D h L P (D.cut s u v)
    | 3 => ∃ b u v a heap, args = [b,u,v,a,heap] ∧ a+L ≤ heap ∧
        Num.Valid mem a h L ∧ (D.toForest s).SameComp u v ∧
        ForestFits D h L P (D.pathAdd s u v (readRat mem a h L P))
    | 4 => ∃ b u v heap, args = [b,u,v,heap] ∧ (D.toForest s).SameComp u v
    | 5 => ∃ b u v heap, args = [b,u,v,heap] ∧ (D.toForest s).SameComp u v ∧
        Num.Fits h L (D.pathSum s u v)
    | _ => False
  post i s args mem s' mem' :=
    match i with
    | 0 => s' = s ∧ mem' (heapArg args) = D.findRoot s (args.getD 1 0)
    | 1 => ∃ e, ForestEdgeAt mem (args.getD 1 0) h L P e ∧ s' = D.link s e
    | 2 => s' = D.cut s (args.getD 1 0) (args.getD 2 0)
    | 3 => s' = D.pathAdd s (args.getD 1 0) (args.getD 2 0)
        (readRat mem (args.getD 3 0) h L P)
    | 4 => s' = s ∧ PathHitAt mem' (heapArg args) h L P
        (D.pathMin s (args.getD 1 0) (args.getD 2 0))
    | 5 => s' = s ∧ Num.Valid mem' (heapArg args) h L ∧
        Num.intVal mem' (heapArg args) h L = D.pathSum s (args.getD 1 0) (args.getD 2 0)
    | _ => False
  cost _ s _ _ := rate (D.toForest s).n
  space i _ args _ := allocation i args

/-- PathAdd preserves the abstract forest invariant by the existing
specification; the machine contract does not ask the caller to prove
this correctness fact as an extra input condition. -/
theorem forestMachine_pathAdd_inv (D : DynForest) (hD : D.IsSpec)
    (w h L P : ℕ) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (s s' : D.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hp : (forestMachineContract D w h L P rate allocation).pre 3 s args mem)
    (hq : (forestMachineContract D w h L P rate allocation).post 3 s args mem s' mem') :
    D.Inv s' := by
  obtain ⟨hinv, _, b, u, v, a, heap, rfl, _, _, hcomp, _⟩ := hp
  change s' = D.pathAdd s u v (readRat mem a h L P) at hq
  rw [hq]
  exact (hD.2.2.2.2.2.1 s u v _ hinv hcomp).1

/-- Every PathMin answer returns a rational with a fitting dyadic
representation. This follows from its output block, not from assuming
that every real number can be represented. -/
theorem PathHitAt.avail_dyadic {mem : ℕ → ℕ} {a h L P : ℕ} {hit : PathHit}
    (hp : PathHitAt mem a h L P (some hit)) :
    RatFits h L P hit.avail := by
  exact ⟨Num.intVal mem (a+4) h L, Num.intVal_fits hp.2.1.1, hp.2.1.2.symm⟩

end MinCostFlow.IPM.Machine
