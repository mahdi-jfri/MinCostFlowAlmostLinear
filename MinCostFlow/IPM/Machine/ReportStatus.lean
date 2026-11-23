module

public import WordRAM.DataStructure
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Returning a reported-list pointer and checked status

The target-test driver needs both the stable Detect report and the
refresh result. Append two fresh words, the report pointer followed by
the status bit. The uniform last-word status lets a failed guard stop
the target test before preparing or applying the next Update batch.
The write preserves every earlier word and any DS footprint below it.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[reportPointer,status,heap]`; return the endpoint of the
two-word record `[reportPointer,status]`. -/
def reportStatusBody : Stmt :=
  .store (.reg 2) (.reg 0) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 1) ;;
  .ret (.bin .add (.reg 2) (.const 2))

/-- Exact two-word output with old-prefix frame and fresh zero suffix. -/
def boundedStatusRecordContract (w limit : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ pointer bit heap,args=[pointer,bit,heap] ∧ bit≤limit)
    (fun args _ mem' => mem' (heapArg args)=args.getD 0 0 ∧
      mem' (heapArg args+1)=args.getD 1 0)
    (fun _ _ => 30) (fun _ _ => 2)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+2}

/-- Detect and flow refresh records carry a binary status. -/
abbrev reportStatusContract (w : ℕ) : Contract := boundedStatusRecordContract w 1

/-- Appending the pointer/status pair is deterministic. -/
theorem reportStatusBody_noRand : reportStatusBody.NoRand := by
  simp [reportStatusBody,Stmt.NoRand]

/-- The actual two-word record procedure costs at most thirty operations. -/
theorem boundedStatusRecord_meetsContract {w limit entry : ℕ} {p : Program}
    (hp : p.procs[entry]?=some reportStatusBody) :
    MeetsContract w p entry (boundedStatusRecordContract w limit) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨⟨pointer,bit,heap,rfl,hbit⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+2<2^w at hspace
  have hpw : pointer<2^w := hwords _ (by simp)
  have hbw : bit<2^w := hwords _ (by simp)
  have hhw : heap<2^w := hwords _ (by simp)
  have h1 : heap+1<2^w := by omega
  have h2 : heap+2<2^w := hspace
  have hw : 2<2^w := by omega
  apply runs_start_le
  unfold reportStatusBody
  wram_step
  wram_step
  refine runs_ret_le (v:=heap+2) (by eval_expr) ?_ ?_
  · change (heap≤heap+2 ∧ heap+2≤heap+2 ∧
      (∀ z<heap,Function.update (Function.update mem heap pointer) (heap+1) bit z=mem z) ∧
      ZeroFrom (Function.update (Function.update mem heap pointer) (heap+1) bit) (heap+2) ∧
      (Function.update (Function.update mem heap pointer) (heap+1) bit heap=pointer ∧
        Function.update (Function.update mem heap pointer) (heap+1) bit (heap+1)=bit)) ∧ heap+2=heap+2
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro z hz0
      rw [Function.update_of_ne (by omega : z≠heap+1),Function.update_of_ne (by omega : z≠heap)]
    · intro z hz0
      rw [Function.update_of_ne (by omega : z≠heap+1),Function.update_of_ne (by omega : z≠heap)]
      exact hz z (by omega)
    · simp
  · simp only [boundedStatusRecordContract,heapContract,Expr.size_reg,Expr.size_bin,Expr.size_const]
    omega

/-- The binary status record uses the same two-word writer. -/
theorem reportStatus_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]?=some reportStatusBody) :
    MeetsContract w p entry (reportStatusContract w) :=
  boundedStatusRecord_meetsContract hp

/-- The last two returned words decode to the report pointer and bit. -/
theorem reportStatus_output {w pointer bit heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (reportStatusContract w).post [pointer,bit,heap] mem v mem') :
    mem' (v-2)=pointer ∧ mem' (v-1)=bit := by
  have hv := hout.2
  change v=heap+2 at hv
  have hd := hout.1.2.2.2.2
  change mem' heap=pointer ∧ mem' (heap+1)=bit at hd
  have h0 : v-2=heap := by omega
  have h1 : v-1=heap+1 := by omega
  simpa only [h0,h1] using hd

/-- A DS below the input heap retains its exact concrete state and credit. -/
theorem reportStatus_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w pointer bit heap v b : ℕ} {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (reportStatusContract w).post [pointer,bit,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  have hh := hlocal b s x mem mem' (fun z hz => (hframe z (hfoot z hz)).symm)
  exact ⟨hh.1 hrep,hh.2⟩

/-- Both status values have actual terminating runs with all word and
workspace conditions jointly satisfied. Address zero holds an empty
report header, and the new record is written above that prefix. -/
theorem reportStatus_example (bit : ℕ) (hbit : bit≤1) (ω : ℕ → Bool) :
    EndsAsContract 16 ⟨[reportStatusBody]⟩ 0 (reportStatusContract 16)
      [0,bit,4] (fun _ => 0) 0 ω := by
  have hwords : ∀ z∈[0,bit,4],z<2^16 := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl <;> omega
  exact reportStatus_meetsContract rfl [0,bit,4] (fun _ => 0) 0 ω hwords
    ⟨⟨0,bit,4,rfl,hbit⟩,(fun _ _ => rfl),by change 4+2<2^16; decide⟩

end MinCostFlow.IPM.Machine
