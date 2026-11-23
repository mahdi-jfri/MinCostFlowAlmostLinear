module

public import MinCostFlow.Scaling.CycleExtractionModel
public import MinCostFlow.Scaling.BoolTableLayout
public import MinCostFlow.Scaling.AdjacencyLayout
import WordRAM.Memory

/-!
# Stored state of the unit-flow cycle traversal

The header stores the traversal mode and its vertex, three immutable-list
pointers, the signed running cycle cost, and an optional result pointer.
Per-vertex path flags and outgoing heads follow it. Immutable list nodes
lie after these arrays and a one-cell gap, so zero denotes an empty list.
All fields represent exactly the data of `Circulation.CycleState`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Tags for choosing a start, walking, peeling a closed part, and completion. -/
def cycleModeTag {J : Circulation} : Circulation.CycleMode J → ℕ
  | .choose => 0
  | .walk _ => 1
  | .peel _ => 2
  | .done => 3

/-- Walking and peeling store their vertex index. The other modes use zero. -/
def cycleModeVertex {J : Circulation} : Circulation.CycleMode J → ℕ
  | .walk v | .peel v => v.val
  | .choose | .done => 0

/-- The stored tag and vertex determine exactly the traversal mode. -/
theorem cycleMode_eq_iff {J : Circulation} (a b : Circulation.CycleMode J) :
    a=b ↔ cycleModeTag a=cycleModeTag b ∧ cycleModeVertex a=cycleModeVertex b := by
  cases a <;> cases b <;> simp [cycleModeTag,cycleModeVertex,Fin.ext_iff]

/-- Path flags begin after the nine-word header. -/
def cycleSeen (base : ℕ) : ℕ := base+9

/-- Outgoing pointer/length pairs follow the path flags. -/
def cycleHeads (n base : ℕ) : ℕ := base+9+n

/-- Immutable nodes follow the vertex arrays and one null-gap cell. -/
def cycleNodes (n base : ℕ) : ℕ := base+10+3*n

/-- An absent result has zero flag. A present result has flag one and
an immutable list at the stored result pointer. -/
def CycleResultAt {m : ℕ} (mem : ℕ → ℕ) (lo bound flag ptr : ℕ)
    (result : Option (List (Fin m))) : Prop :=
  match result with
  | none => flag=0
  | some es => flag=1 ∧ IndexListAt mem lo bound ptr es

/-- The header, vertex arrays, and immutable lists encode the complete
cycle-traversal state without imposing any algorithmic invariant. -/
def CycleStateAt {J : Circulation} (mem : ℕ → ℕ) (base bound : ℕ)
    (s : Circulation.CycleState J) : Prop :=
  ∃ candidates stack edges flag result,
    ListAt mem base [cycleModeTag s.mode,cycleModeVertex s.mode,candidates,stack,edges,
      if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result] ∧
    IndexListAt mem (cycleNodes J.n base) bound candidates s.candidates ∧
    IndexListAt mem (cycleNodes J.n base) bound stack s.stack ∧
    IndexListAt mem (cycleNodes J.n base) bound edges s.cycleEdges ∧
    CycleResultAt mem (cycleNodes J.n base) bound flag result s.result ∧
    BoolTableAt mem (cycleSeen base) s.onPath ∧
    AdjacencyAt mem (cycleHeads J.n base) (cycleNodes J.n base) bound s.outgoing

/-- Preserving the old state cells preserves its exact values while fresh
node allocation may enlarge the allowed immutable-node range. -/
theorem CycleStateAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : Circulation.CycleState J}
    (hat : CycleStateAt mem base bound s) (hnodes : cycleNodes J.n base≤bound)
    (hbound : bound≤bound') (hframe : ∀ x<bound,mem' x=mem x) :
    CycleStateAt mem' base bound' s := by
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hat
  refine ⟨candidates,stack,edges,flag,result,hheader.of_agree_below (h₀ := bound) ?_ hframe,
    (hcandidates.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound,
    (hstack.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound,
    (hedges.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound,?_,
    hseen.of_agree_below ?_ hframe,hout.of_agree_below ?_ hbound hframe⟩
  · change base+9≤bound
    dsimp only [cycleNodes] at hnodes
    omega
  · cases hr : s.result with
    | none => simpa only [CycleResultAt,hr] using hresult
    | some es =>
      simp only [CycleResultAt,hr] at hresult
      obtain ⟨hflag,hlist⟩ := hresult
      exact ⟨hflag,(hlist.of_agree (fun x _ hx => hframe x hx)).mono le_rfl hbound⟩
  · dsimp only [cycleSeen,cycleNodes] at *
    omega
  · dsimp only [cycleHeads,cycleNodes] at *
    omega

/-- A fresh zero region represents the empty choosing state, before its
candidate and outgoing lists are initialized. -/
theorem cycleStateAt_empty (J : Circulation) {mem : ℕ → ℕ} {base bound : ℕ}
    (hz : ZeroFrom mem base) : CycleStateAt mem base bound
      { mode:=.choose,outgoing:=fun _ => [],candidates:=[],stack:=[],onPath:=fun _ => false,
        cycleEdges:=[],cycleCost:=0,result:=none : Circulation.CycleState J } := by
  refine ⟨0,0,0,0,0,?_,.nil,.nil,.nil,rfl,?_,?_⟩
  · intro i hi
    have hi' : i<9 := hi
    rw [hz (base+i) (by omega)]
    change 0=(List.replicate 9 (0 : ℕ))[i]
    exact (List.getElem_replicate hi').symm
  · exact boolTableAt_false (fun x hx => hz x (by dsimp only [cycleSeen] at hx; omega))
  · exact adjacencyAt_empty (fun x hx => hz x (by dsimp only [cycleHeads] at hx; omega))

/-- All empty-state layout conditions and a nonzero node base hold together
in zero memory for every graph. -/
theorem exists_emptyCycleStateAt (J : Circulation) :
    ∃ mem bound,CycleStateAt mem 0 bound
      { mode:=.choose,outgoing:=fun _ => [],candidates:=[],stack:=[],onPath:=fun _ => false,
        cycleEdges:=[],cycleCost:=0,result:=none : Circulation.CycleState J } ∧
      cycleNodes J.n 0≤bound ∧ ZeroFrom mem bound := by
  exact ⟨fun _ => 0,cycleNodes J.n 0,cycleStateAt_empty J (fun _ _ => rfl),le_rfl,fun _ _ => rfl⟩

end MinCostFlow.Scaling.Machine
