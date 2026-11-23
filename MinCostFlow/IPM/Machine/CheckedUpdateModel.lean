module

public import MinCostFlow.IPM.Machine.CheckedUpdateTransition
import MinCostFlow.IPM.Machine.VectorFrame
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Decoding the state returned by the checked driver

The scan and batch preparation write fresh memory. Thus the exact
Update transition uses the coefficient tables and requested
normalization supplied to the driver. The resulting state is the state
in the run theorem, rather than a separate representation witness.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Every checked transition either leaves its state unchanged or uses
one exact refresh batch and the common decoded effective normalization.
The old coefficient tables determine the latter model transition. -/
theorem checkedUpdateTransition_model {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (S : Finset ℕ)
    {b source report g l eta heap neg mx mn : ℕ} {s s' : A.State}
    {mem final : ℕ → ℕ} {v : ℕ}
    (hgEnd : g+I.m*F.limbs≤heap) (hlEnd : l+I.m*F.limbs≤heap)
    (heEnd : eta+F.limbs≤heap)
    (htrace : checkedUpdateTransition F A I κ α rate allocation S
      b source report g l eta heap neg mx mn s s' mem final v) :
    s'=s ∨ ∃ (es : List ℕ) (actual : ℝ) (answer : ℕ),
      es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s' ∧
      s'=(A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual).1 ∧
      AnswerAt final answer (A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual).2 := by
  obtain ⟨checkedEnd,checkedMem,hcheck,hbranch⟩ := htrace
  by_cases haccept : checkedMem (checkedEnd-1)=1
  · rw [ite_eq_left haccept] at hbranch
    obtain ⟨batchEnd,batchMem,hbatch,hupdate,_⟩ := hbranch
    obtain ⟨bit,_,hrecord⟩ := hcheck
    have hscanFrame : ∀ z<heap,checkedMem z=mem z := hrecord.1.2.2.1
    have hchecked : checkedEnd=heap+2 := hrecord.2
    have hbatchFrame : ∀ z<checkedEnd,batchMem z=checkedMem z := hbatch.1.2.2.1
    have hframe : ∀ z<heap,batchMem z=mem z := by
      intro z hz
      exact (hbatchFrame z (by omega)).trans (hscanFrame z hz)
    have hg := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
    have hl := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
    have he := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd
    have hb := hbatch.1.2.2.2.2
    change ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧
      BatchAt batchMem checkedEnd (refreshEdges (namedInstance I) es) ∧ _ at hb
    obtain ⟨es,hnd,hset,hBatch,_⟩ := hb
    obtain ⟨actual,hscalar,hnorm,hfit,hstep⟩ := hupdate
    have hresult := hstep _ hBatch
    simp only [List.getD_cons_zero,List.getD_cons_succ] at hresult hnorm
    rw [hg,hl] at hresult
    rw [he] at hnorm
    exact Or.inr ⟨es,actual,batchEnd,hnd,hset,
      by rw [← hset,List.toFinset_card_of_nodup hnd],hscalar,hnorm,hfit,hresult⟩
  · rw [ite_eq_right haccept] at hbranch
    exact Or.inl hbranch.1

end MinCostFlow.IPM.Machine
