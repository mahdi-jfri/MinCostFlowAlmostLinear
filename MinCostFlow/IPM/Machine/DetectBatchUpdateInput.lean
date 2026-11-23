module

public import MinCostFlow.IPM.Machine.DetectBatchOutput
public import MinCostFlow.IPM.Machine.DetectBatchState
public import MinCostFlow.IPM.Machine.MinRatioUpdateProgram
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Complete Update input after preparing the reported batch

Batch preparation writes above the old heap. Hence it preserves the
checked coefficient tables, requested normalization, concrete DS state
and its credit. Decode its exact fixed-graph batch and word bounds to
supply every premise of the reserved machine Update. Its charge depends
on twice the actual reported-set size, not the graph size.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual prepared batch, checked tables and normalization supply
the full reserved Update input. All range premises are data invariants
already supplied by the coefficient and flow-range checks. -/
theorem minRatioUpdate_pre_after_detectBatch {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {source report heap v b g l eta : ℕ} {S : Finset ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hout : (detectBatchContract w I S).post [source,report,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap)
    (hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s)
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hq : ∀ e∈(namedInstance I).E,|A.query s e|≤(2:ℝ)^F.rangeExponent)
    (hgEnd : g+I.m*F.limbs≤heap) (hlEnd : l+I.m*F.limbs≤heap)
    (heEnd : eta+F.limbs≤heap) (heValid : Num.Valid mem eta F.fmt.limbBits F.limbs)
    (heLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision)
    (heHi : Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^F.rangeExponent)
    (hvalid : ∀ e<I.m,Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hdetected : MinRatioDetectedWith A (namedInstance I) s (· ∈ S)
      (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space
      0 s [b,heap,g,l,eta,v] mem'+(1+2*F.limbs)<2^w) :
    (minRatioUpdateContract w R (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation)
      b s x).pre [b,heap,g,l,eta,1+2*F.limbs,v] mem' := by
  have hvWord : v<2^w := by omega
  obtain ⟨es,hnd,hset,hlen,hbatch,hrefresh,hwords,hsize,hcount,hv⟩ := detectBatch_output hpre hout hvWord
  have hstate := detectBatch_preserves_state R hlocal hout hrep hfoot
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  have hlo := hout.1.1
  change heap≤v at hlo
  have heta := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd
  refine ⟨heap,g,l,eta,1+2*F.limbs,v,rfl,hstate.1,?_,hstate.2.2.1,?_,hspace⟩
  · refine ⟨hfit,b,heap,g,l,eta,v,refreshEdges (namedInstance I) es,rfl,hk,hprec,hq,
      hbatch,hwords,hrefresh,?_,hgEnd.trans hlo,hlEnd.trans hlo,heEnd.trans hlo,
      Num.IPM.valid_frozen hframe heEnd heValid,?_,?_,?_,?_,?_,?_⟩
    · rw [hsize]
      omega
    · rw [heta]
      exact heLo
    · rw [heta]
      exact heHi
    · intro e he
      have hgE := (reported_entry_end g F.limbs e I.m he).trans hgEnd
      have hlE := (reported_entry_end l F.limbs e I.m he).trans hlEnd
      exact ⟨Num.IPM.valid_frozen hframe hgE (hvalid e he).1,
        Num.IPM.valid_frozen hframe hlE (hvalid e he).2⟩
    · intro e he
      have heM : e<I.m := Finset.mem_range.mp he
      have hgE := (reported_entry_end g F.limbs e I.m heM).trans hgEnd
      have hlE := (reported_entry_end l F.limbs e I.m heM).trans hlEnd
      have hgValue := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgE
      have hlValue := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlE
      simpa only [readVector,heM,↓reduceIte,hgValue,hlValue] using hrange e he
    · rw [hcount]
      have hsub : S⊆(namedInstance I).E := by
        obtain ⟨⟨_,_,_,heq,_,_,_,hsubset,_,_,_⟩,_,_⟩ := hpre
        simp only [List.cons.injEq,and_true] at heq
        obtain ⟨rfl,rfl,rfl⟩ := heq
        exact hsubset
      have hcard : S.card≤I.m := by
        simpa only [namedInstance,Finset.card_range] using Finset.card_le_card hsub
      omega
    · have hdet := hdetected.mono (changed':=fun e => ∃ u∈refreshEdges (namedInstance I) es,u.Inserts e)
        (fun e _ he => (refreshEdges_inserts (namedInstance I) es e).mpr
          (List.mem_toFinset.mp (hset ▸ he)))
      refine hdet.congr ?_ ?_
      · intro e he
        have heM : e<I.m := Finset.mem_range.mp he
        have hgE := (reported_entry_end g F.limbs e I.m heM).trans hgEnd
        simp only [readVector,heM,↓reduceIte]
        exact Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgE
      · intro e he
        have heM : e<I.m := Finset.mem_range.mp he
        have hlE := (reported_entry_end l F.limbs e I.m heM).trans hlEnd
        simp only [readVector,heM,↓reduceIte]
        exact Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlE
  · exact hout.1.2.2.2.1

/-- The prepared batch makes the next actual Update charge exactly its
per-operation rate times one plus twice the reported-set size. -/
theorem minRatioUpdate_cost_after_detectBatch {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {source report heap v b g l eta : ℕ} {S : Finset ℕ} {s : A.State} {mem mem' : ℕ → ℕ}
    (hpre : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hout : (detectBatchContract w I S).post [source,report,heap] mem v mem')
    (hvWord : v<2^w) :
    (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).cost
      0 s [b,heap,g,l,eta,v] mem'=rate I.m*(1+2*S.card) := by
  obtain ⟨es,_,_,_,hbatch,_,_,_,hcount,_⟩ := detectBatch_output hpre hout hvWord
  rw [minRatioMachine_update_cost F A (namedInstance I) I.m κ α rate allocation s
    [b,heap,g,l,eta,v] mem' _ hbatch,hcount]

end MinCostFlow.IPM.Machine
