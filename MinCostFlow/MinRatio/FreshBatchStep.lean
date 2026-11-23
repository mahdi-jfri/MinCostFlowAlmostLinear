module

public import MinCostFlow.MinRatio.FreshRecordModel
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# One iteration of the fresh-name batch translator

The translator follows `translateBatch` in input order. An iteration
passes one record to the dispatcher, advances the input cursor by the
number of output words, and decreases the number of remaining records.
Insertion and deletion preserve their respective record widths. The step
proof keeps the record contract intact so it can be used for the map
and graph invariants of the complete loop.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Registers 0 and 4 are the input and output cursors. Registers 1–3
hold the map bases and counter address, and register 5 counts records. -/
def freshBatchStep (dispatch : ℕ) : Stmt :=
  .call 6 dispatch [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .assign 0 (.bin .add (.reg 0) (.bin .sub (.reg 6) (.reg 4))) ;;
  .assign 4 (.reg 6) ;;
  .assign 5 (.bin .sub (.reg 5) (.const 1))

/-- The translation loop visits each remaining record once. -/
def freshBatchLoop (dispatch : ℕ) : Stmt :=
  .loop (.reg 5) (freshBatchStep dispatch)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- The step body has no random instruction. -/
theorem freshBatchStep_noRand (dispatch : ℕ) : (freshBatchStep dispatch).NoRand := by
  simp [freshBatchStep, Stmt.NoRand]

/-- A dispatcher returns the old output cursor plus the width of the
original record. -/
theorem freshRecord_return {w src fwd inv counter heap ret internal : ℕ}
    {record : Update} {mem mem' : ℕ → ℕ}
    (hout : (freshRecordContract w record internal).post [src, fwd, inv, counter, heap] mem ret mem') :
    ret = heap + (updateWords record).length := by
  cases record with
  | split _ _ _ => cases hout
  | delete e => exact hout.1
  | insert e u v =>
    obtain ⟨_, _, _, heap', hargs, hret, _⟩ := hout
    have hh : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
    subst heap'
    exact hret

/-- One iteration costs at most 160 steps. It preserves the table and
counter addresses and leaves the dispatcher's exact memory postcondition. -/
theorem freshBatchStep_triple {w dispatch internal : ℕ} {p : Program} (record : Update)
    (hcall : MeetsContract w p dispatch (freshRecordContract w record internal))
    {st : State}
    (hpre : (freshRecordContract w record internal).pre
      [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4] st.mem)
    (hwords : ∀ x ∈ [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4], x < 2 ^ w)
    (hsrc : st.regs 0 + (updateWords record).length < 2 ^ w)
    (hhp : st.regs 4 + (updateWords record).length < 2 ^ w)
    (hrem : 0 < st.regs 5) (hremWord : st.regs 5 < 2 ^ w) :
    Triple w p (fun s => s = st) (freshBatchStep dispatch)
      (normalPost fun s =>
        s.regs 0 = st.regs 0 + (updateWords record).length ∧
        s.regs 1 = st.regs 1 ∧ s.regs 2 = st.regs 2 ∧ s.regs 3 = st.regs 3 ∧
        s.regs 4 = st.regs 4 + (updateWords record).length ∧ s.regs 5 = st.regs 5 - 1 ∧
        (freshRecordContract w record internal).post
          [st.regs 0, st.regs 1, st.regs 2, st.regs 3, st.regs 4] st.mem (s.regs 4) s.mem)
      (fun _ => 160) := by
  intro s tape hs
  subst s
  have h1w : 1 < 2 ^ w := by omega
  have hdw : (updateWords record).length < 2 ^ w := by omega
  apply runs_start_le
  unfold freshBatchStep
  refine runs_seq_call_le hcall (by rfl) hwords hpre ?_
  intro ret mem' pos' hpost
  have hr := freshRecord_return hpost
  have hdelta : ret - st.regs 4 = (updateWords record).length := by omega
  have hret : ret < 2 ^ w := by omega
  have hrem' : st.regs 5 - 1 < 2 ^ w := by omega
  have hsum : st.regs 0 + (ret - st.regs 4) < 2 ^ w := by rwa [hdelta]
  wram_run
  · simp only [normalPost]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp_all
  · simp only [freshRecordContract]
    wram_cost

end MinCostFlow.MinRatio
