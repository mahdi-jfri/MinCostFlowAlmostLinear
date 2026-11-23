module

public import MinCostFlow.IPM.Machine.RoundProcedures
import WordRAM.Tactic

/-!
# Choosing the improving direction of a rounding cycle

The forward cycle cost is the new edge cost minus the existing
path cost. A signed comparison suffices to choose the backward
direction exactly when this difference is positive.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Read the signed path cost and compare it to the new edge cost.
The heap is returned in register 14 and the backward bit in 15. -/
def roundDirectionBody (B : RoundProcedures) : Stmt :=
  .call 14 B.pathSum [.reg 0,.reg 2,.reg 3,.reg 6,.reg 13] ;;
  .call 15 B.less [.reg 13,.reg 4,.reg 6]

/-- Both calls are deterministic statements. -/
theorem roundDirection_noRand (B : RoundProcedures) : (roundDirectionBody B).NoRand := by
  simp [roundDirectionBody,Stmt.NoRand]

/-- The connected branch obtains the exact direction without
altering the abstract forest, flow table, or saved availabilities. -/
theorem roundDirection_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (I : Instance) (j : Fin I.m) (b ac fp one base af ab heap : ℕ) (s : D.State) (x : R.τ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hw : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,fp,L,P,one,base,I.m+1,af,ab,heap],z<2^w)
    (hL : 0<L) (hb : b≤heap) (hc : ac+L≤b) (hCost : RatAt mem ac h L 0 (I.edge j).cost)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hComp : (D.toForest s).SameComp (I.edge j).tail (I.edge j).head)
    (hSum : Num.Fits h L (D.pathSum s (I.edge j).tail (I.edge j).head))
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hZero : ZeroFrom mem heap)
    (hSpace : heap+allocation 5 [b,(I.edge j).tail,(I.edge j).head,heap]+L<2^w) :
    let args := [b,j.val,(I.edge j).tail,(I.edge j).head,ac,fp,L,P,one,base,I.m+1,af,ab,heap]
    ∃ out final cost y,
      Runs w p ω (roundDirectionBody B) (startState args mem pos) .normal final cost ∧
      final.regs 14=out ∧ final.regs 15=(roundBackward D s j).toNat ∧
      (∀ z<14,final.regs z=(startState args mem pos).regs z) ∧
      R.rep b s y final.mem ∧ heap+L≤out ∧ out≤heap+allocation 5 [b,(I.edge j).tail,(I.edge j).head,heap]+L ∧
      ZeroFrom final.mem out ∧ (∀ z<b,final.mem z=mem z) ∧
      (∀ z<heap,¬R.foot b x z → final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      (∀ z,R.foot b y z → R.foot b x z ∨ heap≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤rate (D.toForest s).n+41*L+80+R.phi b x mem := by
  dsimp only
  let u := (I.edge j).tail
  let v := (I.edge j).head
  let parent := startState [b,j.val,u,v,ac,fp,L,P,one,base,I.m+1,af,ab,heap] mem pos
  have hw₀ : ∀ z∈[b,u,v,L,heap],z<2^w := by
    intro z hz
    apply hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  obtain ⟨out,raw,c₁,y,hRun,hPath,hRep₁,hLo,hHi,hZero₁,hMem,hFoot₁,hFrame,hFoot₂,hC₁⟩ :=
    roundPathSum_runs D rate allocation R himpl b u v heap s x mem pos ω hw₀ hb hL
      hInv hFit hComp hSum hRep hFoot hZero hSpace
  have hArgs₁ : evalArgs w parent [.reg 0,.reg 2,.reg 3,.reg 6,.reg 13]=some [b,u,v,L,heap] := rfl
  have hCall₁ := round_returning_call (dst:=14) hB.pathSum_at hArgs₁ hRun
  let mid : State := ⟨raw.mem,Function.update parent.regs 14 out,raw.pos⟩
  have hArgs₂ : evalArgs w mid [.reg 13,.reg 4,.reg 6]=some [heap,ac,L] := rfl
  have hW₂ : ∀ z∈[heap,ac,L],z<2^w := by
    intro z hz
    apply hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  have hC' := hCost.frozen hMem hc
  have hPre : (Num.lessContract w h).pre [heap,ac,L] mid.mem :=
    ⟨heap,ac,L,rfl,by omega,by omega,hPath.1,hC'.1⟩
  obtain ⟨final,c₂,bit,hCall₂,hOut₂,hBit,hRegs,hC₂⟩ :=
    runs_call_of_meetsContract (r:=15) hB.less_spec hArgs₂ hW₂ hPre ω
  obtain ⟨hMem₂,hDec⟩ := hOut₂
  have he : final.mem=raw.mem := hMem₂
  change bit=(if Num.intVal raw.mem heap h L<Num.intVal raw.mem ac h L then 1 else 0) at hDec
  have hBt : bit=(roundBackward D s j).toNat := by
    simp only [hPath.lt_iff hC'] at hDec
    unfold roundBackward
    by_cases hl : D.pathSum s u v<(I.edge j).cost
    · simpa [u,v,hl] using hDec
    · simpa [u,v,hl] using hDec
  refine ⟨out,final,5+c₁+1+c₂+1,y,?_,?_,hBit.trans hBt,?_,
    he ▸ hRep₁,hLo,hHi,he ▸ hZero₁,?_,?_,hFoot₁,hFoot₂,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid,_,_,hCall₁,hCall₂,rfl⟩)
  · exact (hRegs 14 (by decide)).trans (by simp [mid])
  · intro i hi
    rw [hRegs i (by omega)]
    exact Function.update_of_ne (show i≠14 by omega) _ _
  · intro i hi
    rw [he]
    exact hMem i hi
  · intro i hi hf
    rw [he]
    exact hFrame i hi hf
  · rw [he]
    change c₂≤3+(41*L+51)+1 at hC₂
    omega

end MinCostFlow.IPM.Machine
