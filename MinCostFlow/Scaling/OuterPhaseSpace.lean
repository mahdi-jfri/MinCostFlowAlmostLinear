module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
public import MinCostFlow.Scaling.ResidualOptimizationContract
import MinCostFlow.Scaling.FeasibilityPhaseWordSize
import MinCostFlow.Scaling.ResidualOptimizationWordSize

/-!
# Entering either outer phase in a shared larger memory

The fixed-source width theorems prove all numeric premises jointly in
canonical memory. Those numeric bounds are independent of placement.
A fresh region large enough for that entire source width therefore lets
either phase run after an earlier phase, provided its real source arrays
are stored below the current heap. No result of an algorithm is assumed.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The first phase's complete reserve is bounded by its fixed source
width's address space, independently of its source placement. -/
theorem feasibilityPhaseSpace_le_source_capacity (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U) :
    feasibilityPhaseSpace I hv C U≤2^wordSize 16384 (I.encode++[C,U]) := by
  obtain ⟨_,hpre⟩ := feasibilityPhase_pre_wordSize solver entry T hproc I hv C U hC horder hd hl hu
  obtain ⟨a,heap,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs⟩ := hpre
  change heap+feasibilityPhaseSpace I hv C U<2^wordSize 16384 (I.encode++[C,U]) at hs
  omega

/-- Every bounded starting flow has the same fixed source-width upper
bound on the complete residual optimization reserve. -/
theorem residualOptimizationSpace_le_source_capacity (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U) :
    residualOptimizationSpace I hv f C U≤2^wordSize 16384 (I.encode++[C,U]) := by
  obtain ⟨_,_,_,hpre⟩ := residualOptimization_pre_wordSize solver entry T hproc I hv f C U hf hC hl hu
  obtain ⟨a,graph,flow,heap,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs⟩ := hpre
  change heap+residualOptimizationSpace I hv f C U<2^wordSize 16384 (I.encode++[C,U]) at hs
  omega

/-- A fresh region covering one complete source-width address space
supplies all first-phase numeric conditions at any valid source placement. -/
theorem feasibilityPhase_pre_of_source_space {w : ℕ} (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (C U a heap : ℕ) (mem : ℕ → ℕ) (hC : 1≤C)
    (horder : ∀ e∈I.edges,e.lower≤e.upper)
    (hd : ∀ v : Fin I.n,(I.d v).natAbs≤U)
    (hl : ∀ e∈I.edges,e.lower.natAbs≤U) (hu : ∀ e∈I.edges,e.upper.natAbs≤U)
    (hat : ListAt mem a I.encode) (hend : a+I.encode.length≤heap) (hz : ZeroFrom mem heap)
    (hs : heap+2^wordSize 16384 (I.encode++[C,U])<2^w) :
    (∀ x∈[a,C,U,heap],x<2^w) ∧
      (feasibilityPhaseContract w solver entry T hproc I hv C U).pre [a,C,U,heap] mem := by
  let guest := wordSize 16384 (I.encode++[C,U])
  change heap+2^guest<2^w at hs
  obtain ⟨hargs,hpre⟩ := feasibilityPhase_pre_wordSize solver entry T hproc I hv C U hC horder hd hl hu
  obtain ⟨a0,heap0,_,_,_,_,_,_,_,hIwords,hPwords,_,h8,hbudget,hB,hMass,hObj,_,hspace⟩ := hpre
  have hguest : 2^guest<2^w := by omega
  have hS : feasibilityPhaseSpace I hv C U≤2^guest := by
    change heap0+feasibilityPhaseSpace I hv C U<2^guest at hspace
    omega
  refine ⟨?_,a,heap,rfl,hat,hend,horder,hd,hl,hu,
    (fun x hx => (hIwords x hx).trans hguest),(fun x hx => (hPwords x hx).trans hguest),hC,
    h8.trans hguest,hbudget.trans hguest,hB.trans hguest,hMass.trans hguest,hObj.trans hguest,hz,?_⟩
  · have hcw := (hargs C (by simp)).trans hguest
    have huw := (hargs U (by simp)).trans hguest
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · exact (Nat.add_le_add_left hS heap).trans_lt hs

/-- The same source-width region supplies every second-phase numeric
condition for any edgewise bounded starting flow and stored source arrays. -/
theorem residualOptimization_pre_of_source_space {w : ℕ} (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U a graph flow heap : ℕ) (mem : ℕ → ℕ)
    (hf : ∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ))
    (hC : ∀ e,(I.edge e).cost.natAbs≤C)
    (hl : ∀ e,(I.edge e).lower.natAbs≤U) (hu : ∀ e,(I.edge e).upper.natAbs≤U)
    (hat : ListAt mem a I.encode) (hgraph : ListAt mem graph (FlowReduction.shiftedGraph I hv).solverWords)
    (hflow : ListAt mem flow (List.ofFn (fun e => (f e).toNat)))
    (hend : a+I.encode.length≤heap) (hgraphEnd : graph+(FlowReduction.shiftedGraph I hv).solverWords.length≤heap)
    (hflowEnd : flow+I.m≤heap) (hz : ZeroFrom mem heap)
    (hs : heap+2^wordSize 16384 (I.encode++[C,U])<2^w) :
    (∀ x∈[a,graph,flow,C,U,heap],x<2^w) ∧
      (residualOptimizationContract w solver entry T hproc I hv f C U).pre
        [a,graph,flow,C,U,heap] mem := by
  let guest := wordSize 16384 (I.encode++[C,U])
  change heap+2^guest<2^w at hs
  obtain ⟨mem0,heap0,hargs,hpre⟩ := residualOptimization_pre_wordSize solver entry T hproc I hv f C U hf hC hl hu
  obtain ⟨a0,graph0,flow0,h0,_,_,_,_,_,_,_,_,_,_,_,hIwords,hJwords,hRwords,h8,hB,h4U,_,hspace⟩ := hpre
  have hguest : 2^guest<2^w := by omega
  have hS : residualOptimizationSpace I hv f C U≤2^guest := by
    change h0+residualOptimizationSpace I hv f C U<2^guest at hspace
    omega
  refine ⟨?_,a,graph,flow,heap,rfl,hat,hgraph,hflow,hend,hgraphEnd,hflowEnd,hf,hC,hl,hu,
    (fun x hx => (hIwords x hx).trans hguest),(fun x hx => (hJwords x hx).trans hguest),
    (fun x hx => (hRwords x hx).trans hguest),h8.trans hguest,hB.trans hguest,h4U.trans hguest,hz,?_⟩
  · have hcw := (hargs C (by simp)).trans hguest
    have huw := (hargs U (by simp)).trans hguest
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact (Nat.add_le_add_left hS heap).trans_lt hs

end MinCostFlow.Scaling.Machine
