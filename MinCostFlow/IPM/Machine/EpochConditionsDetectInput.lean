module

public import MinCostFlow.IPM.Machine.EpochConditions
public import MinCostFlow.IPM.Machine.HistoryAppend

/-!
# The valid history supplied to the next actual Detect

Append the unchanged input of the upcoming Detect to the shared history.
Earlier states, report times and cache values are unchanged. This gives
the original specification a valid prefix ending at that operation,
while preserving the current caller condition and concrete machine data.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Extend only the shared input history for the upcoming Detect.
The actual memory, registers and credit witness are unchanged. -/
def EpochPoint.detectInput {τ : Type} (P : EpochPoint τ) (i : ℕ) : EpochPoint τ :=
  {P with
    history := appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i))
    eta := Function.update P.eta (2*i+1) 0
    op := Function.update P.op (2*i+1) false}

/-- The upcoming Detect has a valid unchanged input with the same
current DS state, cache, registers, memory and concrete credit. -/
theorem EpochConditions.detect_input {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : WordRAM.DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ} {initialHeap space finish i : ℕ}
    {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) :
    let Q := P.detectInput i
    EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i Q ∧
    MinRatioHistoryValid Q.history Q.op (2*i+1) ∧
    (∀ j≤2*i+1,Q.history.G j=namedInstance I) ∧ Q.op (2*i+1)=false ∧
    Q.history.ℓ (2*i+1)=readVector P.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
    minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)=
      minRatioState A.eraseFailure P.history P.eta P.op (2*i) := by
  let Q := P.detectInput i
  obtain ⟨hi,hcount,hcounter,hregs,hheap,hbudget,hprefix,hvalid,hG,hpre,hgOld,hlOld,hcache,hranges,hhist⟩ := h
  have hhistQ : HistoryLengthsWithin Q.history (2*i+1) F.rangeExponent :=
    appendHistoryStage_lengthsWithin [] _ _ hhist (hhist (2*i) le_rfl)
  have hnewValid : MinRatioHistoryValid Q.history Q.op (2*i+1) :=
    appendHistoryStage_valid_detect P.history P.op (2*i) hvalid
  have hnewG : ∀ j≤2*i+1,Q.history.G j=namedInstance I := by
    intro j hj
    by_cases he : j=2*i+1
    · subst j
      simpa only [Q,EpochPoint.detectInput,appendHistoryStage,Function.update_self] using hG (2*i) le_rfl
    · have hj' : j≤2*i := by omega
      simpa only [Q,EpochPoint.detectInput,appendHistoryStage,Function.update_of_ne he] using hG j hj'
  have hstate : ∀ t≤2*i,minRatioState A.eraseFailure Q.history Q.eta Q.op t=
      minRatioState A.eraseFailure P.history P.eta P.op t :=
    appendHistoryStage_past_state A.eraseFailure P.history P.eta P.op (2*i) []
      (P.history.g (2*i)) (P.history.ℓ (2*i)) 0 false
  have hlast (e : ℕ) : minRatioLast A.eraseFailure Q.history Q.eta Q.op (2*i) e=
      minRatioLast A.eraseFailure P.history P.eta P.op (2*i) e :=
    appendHistoryStage_past_last A.eraseFailure P.history P.eta P.op (2*i) []
      (P.history.g (2*i)) (P.history.ℓ (2*i)) 0 false (2*i) e le_rfl
  have hheld (e : ℕ) : minRatioState A.eraseFailure Q.history Q.eta Q.op
      (minRatioLast A.eraseFailure Q.history Q.eta Q.op (2*i) e)=
      minRatioState A.eraseFailure P.history P.eta P.op
        (minRatioLast A.eraseFailure P.history P.eta P.op (2*i) e) := by
    rw [hlast e]
    exact hstate _ (minRatioLast_le A.eraseFailure P.history P.eta P.op (2*i) e)
  have hcurrentG : Q.history.g (2*i)=P.history.g (2*i) := by
    simp only [Q,EpochPoint.detectInput,appendHistoryStage,Function.update_of_ne (by omega : 2*i≠2*i+1)]
  have hcurrentL : Q.history.ℓ (2*i)=P.history.ℓ (2*i) := by
    simp only [Q,EpochPoint.detectInput,appendHistoryStage,Function.update_of_ne (by omega : 2*i≠2*i+1)]
  refine ⟨?_,hnewValid,hnewG,?_,?_,hstate (2*i) le_rfl⟩
  · refine ⟨hi,hcount,hcounter,hregs,hheap,hbudget,hprefix,?_,?_,?_,?_,?_,?_,hranges,
      fun j hj => hhistQ j (Nat.le_succ_of_le hj)⟩

    · exact hnewValid.mono Q.history Q.op (2*i+1) (2*i) (Nat.le_succ _)
    · intro j hj
      exact hnewG j (Nat.le_trans hj (Nat.le_succ _))
    · change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
        (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) P.credit q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I (P.machine.regs 8)).take 20) P.machine.mem
      rw [hstate (2*i) le_rfl]
      exact hpre
    · exact hgOld.trans hcurrentG.symm
    · exact hlOld.trans hcurrentL.symm
    · intro e he
      change reportedCachePost F A
        (minRatioState A.eraseFailure Q.history Q.eta Q.op (minRatioLast A.eraseFailure Q.history Q.eta Q.op (2*i) e))
        I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e P.machine.mem
      rw [hheld e]
      exact hcache e he
  · simp only [EpochPoint.detectInput,Function.update_self]
  · simpa only [Q,EpochPoint.detectInput,appendHistoryStage,Function.update_self] using hlOld.symm

end MinCostFlow.IPM.Machine
