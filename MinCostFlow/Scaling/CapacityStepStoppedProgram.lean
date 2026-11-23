module

public import MinCostFlow.Scaling.CapacityStepContract
import WordRAM.Tactic

/-!
# Returning a stopped capacity-scaling state

The early-stop flag makes subsequent iterations return immediately. The
stored header already ends at the current heap, so returning that heap
preserves the exact model state and all memory without allocation.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A stopped capacity state takes constant cost and leaves every memory
cell unchanged, exactly as the model's early-stop branch. -/
theorem capacityStep_stopped_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hp : p.HasAt b (capacityStepModule solver entry b)) (J : Circulation) (s : CapacityState J)
    (C U : ℕ) (hstop : s.stopped=true) :
    MeetsContract w p b (capacityStepContract w solver entry T hproc J s C U) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hinput,hRinput,hf,hC,hu,hm,hzero,
    hspace,hsmall,hmass,hguest,hbudget,hproduct,hround,hroundGuest,haddition,hw⟩ := hpre
  obtain ⟨ptr,hheader,hptrEnd,hread⟩ := hstate
  have hs1 : state+1<2^w := by omega
  have hflag : mem (state+1)=1 := by
    have h : mem (state+1)=s.stopped.toNat := hheader 1 (by change 1<2; decide)
    simpa only [hstop,Bool.toNat_true] using h
  have hbase : heap-2=state := by omega
  have hmodel : (s.step (canonicalSolver solver entry T hproc)).value=s := by
    simp only [CapacityState.step,hstop,↓reduceIte]
  apply runs_start_le
  unfold capacityStepBody
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  wram_step
  refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤heap ∧ heap≤heap+capacityStepSpace solver entry T hproc J s ∧
      CapacityStateAt mem (heap-2) heap (s.step (canonicalSolver solver entry T hproc)).value ∧
      ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
    rw [hbase,hmodel]
    exact ⟨le_rfl,Nat.le_add_right _ _,⟨ptr,hheader,hptrEnd,hread⟩,hzero,fun _ _ => rfl⟩
  · simp only [capacityStepContract,hstop,↓reduceIte,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

end MinCostFlow.Scaling.Machine
