module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Exec
import WordRAM.Entry

/-!
# Positive time for the empty bounded circulation

The solver contract applies to the empty circulation as well. Its
preconditions have a concrete canonical witness and every machine run
has positive cost. Therefore the supplied bound satisfies `T(0,0)>=1`.
This pays for the constant empty-input branch in the outer time bound
without adding an assumption about the solver's time function.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A solver meeting the actual circulation contract necessarily has a
positive time bound at `(0,0)`. -/
theorem solverTime_zero_pos (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch)) : 1≤T 0 0 := by
  let J : Circulation := ⟨0,0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0⟩
  have hc : J.CostsBounded (J.m^10) := fun e => Fin.elim0 e
  have hu : ∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40 := fun e => Fin.elim0 e
  obtain ⟨w,hwords,hpre⟩ := exists_solver_pre T solverScratch J hc hu
  obtain ⟨body,_,o,st,c,hr,_,hcost⟩ := hproc w [0,J.solverWords.length]
    (initMem J.solverWords) 0 (fun _ => false) hwords hpre
  have hd := solverDimensions_of_at J (initMem J.solverWords) 0 J.solverWords.length (listAt_initMem _)
  change c≤T (solverDimensions [0,J.solverWords.length] (initMem J.solverWords)).1
    (solverDimensions [0,J.solverWords.length] (initMem J.solverWords)).2 at hcost
  rw [hd] at hcost
  exact hr.cost_pos.trans hcost

end MinCostFlow.Scaling.Machine
