module

public import WordRAM.DataStructure
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Appending the status of a guarded target-test step

A reported-edge step appends a single status bit after its scratch work.
The returned heap minus one then has a uniform meaning on all guard
branches. The write preserves a data structure whose footprint is below
that incoming heap, including its amortized potential.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[bit,heap]`. -/
def flagRecordBody : Stmt :=
  .store (.reg 1) (.reg 0) ;;
  .ret (.bin .add (.reg 1) (.const 1))

/-- One status-bit entry. -/
def flagRecordModule : List Stmt := [flagRecordBody]

/-- One fresh output word, exact heap, unchanged old prefix and zero suffix. -/
def flagRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ bit heap,args=[bit,heap] ∧ bit≤1)
    (fun args _ mem' => mem' (heapArg args)=args.getD 0 0)
    (fun _ _ => 20) (fun _ _ => 1)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+1}

/-- A status-bit write is deterministic. -/
theorem flagRecord_noRand : flagRecordBody.NoRand := by
  simp [flagRecordBody,Stmt.NoRand]

/-- The actual status-bit write costs at most twenty operations. -/
theorem flagRecord_meetsContract {w b : ℕ} {p : Program} (hp : p.HasAt b flagRecordModule) :
    MeetsContract w p b (flagRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨bit,heap,rfl,hbit⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+1<2^w at hspace
  have hb : bit<2^w := hwords _ (by simp)
  have hh : heap<2^w := hwords _ (by simp)
  apply runs_start_le
  unfold flagRecordBody
  wram_step
  refine runs_ret_le (v:=heap+1) (by eval_expr) ?_ ?_
  · change (heap≤heap+1 ∧ heap+1≤heap+1 ∧
      (∀ z<heap,Function.update mem heap bit z=mem z) ∧
      ZeroFrom (Function.update mem heap bit) (heap+1) ∧ Function.update mem heap bit heap=bit) ∧
      heap+1=heap+1
    refine ⟨⟨by omega,le_rfl,?_,?_,by simp⟩,rfl⟩
    · intro z hz
      exact Function.update_of_ne (by omega : z≠heap) _ _
    · intro z hz0
      rw [Function.update_of_ne (by omega : z≠heap)]
      exact hz z (by omega)
  · simp only [flagRecordContract,heapContract,Expr.size_reg,Expr.size_bin,Expr.size_const]
    omega

/-- The last word of the returned heap is exactly the supplied status. -/
theorem flagRecord_output {w bit heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (flagRecordContract w).post [bit,heap] mem v mem') : mem' (v-1)=bit := by
  have hv := hout.2
  change v=heap+1 at hv
  have hb := hout.1.2.2.2.2
  change mem' heap=bit at hb
  simpa only [hv,Nat.add_sub_cancel] using hb

/-- Both status values have actual terminating machine runs, with all
word and workspace premises satisfied together on every tape. -/
theorem flagRecord_example (bit : ℕ) (hbit : bit≤1) (ω : ℕ → Bool) :
    EndsAsContract 16 ⟨flagRecordModule⟩ 0 (flagRecordContract 16)
      [bit,0] (fun _ => 0) 0 ω := by
  have hp : (⟨flagRecordModule⟩ : Program).HasAt 0 flagRecordModule := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hwords : ∀ z∈[bit,0],z<2^16 := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl <;> omega
  exact flagRecord_meetsContract hp [bit,0] (fun _ => 0) 0 ω hwords
    ⟨⟨bit,0,rfl,hbit⟩,(fun _ _ => rfl),by change 1<2^16; decide⟩

/-- Appending a bit above the DS footprint preserves its represented
state and potential, so completing a step does not spend its credit. -/
theorem flagRecord_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w bit heap v b : ℕ} {mem mem' : ℕ → ℕ} {s : σ} {x : R.τ}
    (hout : (flagRecordContract w).post [bit,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' := by
  have hf := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hf
  have hh := hlocal b s x mem mem' (fun z hz => (hf z (hfoot z hz)).symm)
  exact ⟨hh.1 hrep,hh.2⟩

end MinCostFlow.IPM.Machine
