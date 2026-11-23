module

public import MinCostFlow.Scaling.OuterEntryContract
public import MinCostFlow.Scaling.OuterEntryPaperCost
import MinCostFlow.Scaling.OuterEntryProgram
import MinCostFlow.Scaling.ArbitraryDemandMachineCorrectness
import MinCostFlow.Scaling.InputMagnitudeBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# The whole Appendix C scaling program

The supplied deterministic bounded-circulation solver determines one
input-independent whole program. On every valid original encoding and
every random tape, its run writes a correct integral minimum-cost flow
or the infeasibility tag. Its cost has the three logarithmic scaling
factors multiplying solver time plus edge work, with additive vertex
work. The circulation solver is the only algorithmic parameter.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The complete Appendix C outer program runs on exactly `I.encode`,
with word multiplier 131072, and writes a correct answer. The explicit
constant is `K=2*10^18*(solver.regBound+1)` and the padded binary logs
express the paper's `log(m)*log(mU)*log(C)` bound. This statement includes
the cost of the whole-program entry call and holds for every random tape. -/
theorem outerScaling_runsTo (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,RunsTo (wordSize 131072 I.encode) (outerScalingProgram solver entry) I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost≤wholeScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (wholeScalingConstant solver*I.n) (wholeScalingConstant solver*I.m)+I.m)+
        wholeScalingConstant solver*I.n := by
  let w := wordSize 131072 I.encode
  let p := outerScalingProgram solver entry
  let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
    (canonicalSolver solver entry T hproc) I hv I.maxCost I.maxCapacity).value
  have hp : p.HasAt 0 (outerEntryModule solver entry 0) := hasAt_self _
  have hk := outerEntry_meetsContract (w := w) hproc hdet hmono hp I hv
  have hin : I.encode.length<2^w := length_lt_two_pow_wordSize (by decide) _
  obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hk [I.encode.length] (initMem I.encode) 0 ω
    (by intro x hx; have he : x=I.encode.length := List.mem_singleton.mp hx; exact he ▸ hin) ⟨rfl,rfl,rfl⟩
  change o.value=answer.length ∧ ListAt st.mem 0 answer at hpost
  have hlen : 1≤answer.length := by
    dsimp only [answer]
    cases (FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv I.maxCost I.maxCapacity).value with
    | none => exact le_rfl
    | some f => rw [scalingAnswerWords_some_length]; omega
  have hc : ∀ e,(I.edge e).cost.natAbs≤I.maxCost := fun e =>
    Link.elem_le_foldr_max (List.mem_map.mpr ⟨I.edge e,List.getElem_mem e.isLt,rfl⟩)
  have hl : ∀ e,(I.edge e).lower.natAbs≤I.maxCapacity := fun e =>
    lower_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  have hu : ∀ e,(I.edge e).upper.natAbs≤I.maxCapacity := fun e =>
    upper_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  have hcorrect : I.IsCorrectAnswer answer := arbitraryDemand_answer_correct solver entry T hproc
    I hv I.maxCost I.maxCapacity hc hl hu
  have hpaper := outerEntry_cost_paper w solver entry T hproc hmono I hv [I.encode.length] (initMem I.encode)
  cases o with
  | normal =>
    have hz : 0=answer.length := hpost.1
    omega
  | returned len =>
    have he : answer.length=len := hpost.1.symm
    refine ⟨answer,c+2,runsTo_of_entry hbody hin hr he hpost.2,hcorrect,?_⟩
    exact (Nat.add_le_add_right hcost 2).trans hpaper

end MinCostFlow.Scaling.Machine
