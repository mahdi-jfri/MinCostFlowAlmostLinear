module

public import MinCostFlow.IPM.Machine.RoundPackLink
public import MinCostFlow.IPM.Machine.RoundRelinkModel
public import MinCostFlow.IPM.Machine.RoundAvailabilityProgram
import WordRAM.Tactic

/-!
# Relinking only when the corrected edge stays fractional

The exact integer test skips the forest update if the new
coordinate is integral. Otherwise we recompute its availability
within the original unit interval and call Link.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [b,eid,u,v,cost,flow,L,P,one,heap], link only a fractional edge. -/
def roundRelinkBody (integer availability packLink : ℕ) : Stmt :=
  .call 10 integer [.reg 5,.reg 6,.reg 7] ;;
  .cond (.reg 10) (.ret (.reg 9))
    (.call 11 availability [.reg 5,.reg 8,.reg 6,.reg 7,.reg 9] ;;
     .call 11 packLink [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,
       .bin .sub (.reg 11) (.reg 6),
       .bin .sub (.reg 11) (.bin .mul (.const 3) (.reg 6)),.reg 6,.reg 11] ;;
     .ret (.reg 11))

/-- The relink test and both branches are deterministic. -/
theorem roundRelink_noRand (integer availability packLink : ℕ) :
    (roundRelinkBody integer availability packLink).NoRand := by
  simp [roundRelinkBody,Stmt.NoRand]

set_option maxHeartbeats 700000 in
/-- Relink preserves the flow table, adds the exact fractional edge
when needed, and allocates at most the availability scratch, record
and the forest's allocation bound. -/
theorem roundRelink_runs {w h L P integer availability packLink pack link A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep D.State) {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hInt : MeetsContract w p integer (Num.isIntegerContract w h))
    (hAvail : MeetsContract w p availability (roundAvailabilityContract w h))
    (hPackLink : p.procs[packLink]?=some (roundPackLinkBody pack link))
    (hPack : ∀ e, MeetsContract w p pack (roundLinkRecordContract w h P e))
    (hLink : p.procs[link]?=some (roundLinkBody (op 1)))
    (hAlloc : ∀ b a heap,allocation 1 [b,a,heap]≤A)
    (I : Instance) (j : Fin I.m) (q original : ℚ)
    (b ac af one heap : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ)
    (ω : ℕ → Bool) (hWords : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,af,L,P,one,heap],z<2^w)
    (hP : h∣P) (hb : b≤heap) (hC : ac+L≤b) (hF : af+L≤b) (hOne : one+L≤b)
    (hCost : RatAt mem ac h L 0 (I.edge j).cost) (hFlow : RatAt mem af h L P q)
    (hUnit : RatAt mem one h L P 1) (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hReady : isIntRat q=false →
      let e := roundingEdge I j original q
      e.u<(D.toForest s).n ∧ e.v<(D.toForest s).n ∧ ¬(D.toForest s).SameComp e.u e.v ∧
      (∀ g∈(D.toForest s).edges,g.eid≠j.val) ∧
      Num.Fits h L e.cost ∧ RatFits h L P q ∧ RatFits h L P (⌊q⌋:ℚ) ∧
      RatFits h L P e.availFwd ∧ RatFits h L P e.availBwd ∧
      (⌊q⌋=⌊original⌋ ∧ ⌈q⌉=⌈original⌉))
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hZero : ZeroFrom mem heap) (hSpace : heap+11*L+4+A<2^w) :
    ∃ out final cost y,
      Runs w p ω (roundRelinkBody integer availability packLink)
        (startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,af,L,P,one,heap] mem pos)
        (.returned out) final cost ∧
      R.rep b (if isIntRat q then s else D.link s (roundingEdge I j original q)) y final.mem ∧
      heap≤out ∧ out≤heap+11*L+4+A ∧ ZeroFrom final.mem out ∧ (∀ z<b,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      cost+R.phi b y final.mem≤rate (D.toForest s).n+336*L+570+R.phi b x mem := by
  let e := roundingEdge I j original q
  let s₀ := startState [b,j.val,(I.edge j).tail,(I.edge j).head,ac,af,L,P,one,heap] mem pos
  have hArg₀ : evalArgs w s₀ [.reg 5,.reg 6,.reg 7]=some [af,L,P] := rfl
  have hw₀ : ∀ z∈[af,L,P],z<2^w := by
    intro z hz
    apply hWords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  have hPre₀ : (Num.isIntegerContract w h).pre [af,L,P] mem :=
    ⟨af,L,P,rfl,hP,by omega,hFlow.1⟩
  obtain ⟨s₁,c₁,bit,hCall₁,hOut₁,hBit,hRegs₁,hC₁⟩ :=
    runs_call_of_meetsContract (r:=10) hInt hArg₀ hw₀ hPre₀ ω
  obtain ⟨hm₁,hDec⟩ := hOut₁
  have hMem₁ : s₁.mem=mem := hm₁
  change bit=(if (2:ℤ)^P∣Num.intVal mem af h L then 1 else 0) at hDec
  simp only [hFlow.isInt_iff] at hDec
  change c₁≤3+(19*L+40)+1 at hC₁
  have hReg₁ (i : ℕ) (hi : i<10) : s₁.regs i=s₀.regs i := hRegs₁ i (by omega)
  have hH₁ : s₁.regs 9=heap := hReg₁ 9 (by decide)
  by_cases hQ : isIntRat q=true
  · have hB : s₁.regs 10=1 := hBit.trans (by simpa [hQ] using hDec)
    have hRet : Runs w p ω (.ret (.reg 9)) s₁ (.returned heap) s₁ 2 :=
      runs_ret_iff.mpr ⟨heap,congrArg some hH₁,rfl,rfl,rfl⟩
    have hCond (other : Stmt) : Runs w p ω (.cond (.reg 10) (.ret (.reg 9)) other)
        s₁ (.returned heap) s₁ 4 :=
      runs_cond_iff.mpr ⟨1,2,congrArg some hB,hRet,rfl⟩
    refine ⟨heap,s₁,c₁+5,x,?_,?_,le_rfl,by omega,?_,fun z _ => congrFun hMem₁ z,hFoot,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨s₁,c₁,4,hCall₁,hCond _,rfl⟩)
    · simpa only [hMem₁,hQ,ite_true] using hRep
    · rwa [hMem₁]
    · rw [hMem₁]
      omega
  · have hQ' : isIntRat q=false := Bool.eq_false_iff.mpr hQ
    have hB : s₁.regs 10=0 := hBit.trans (by simpa [hQ] using hDec)
    obtain ⟨hu,hv,hDis,hFresh,hFC,hFQ,hFloor,hFA,hFB,hFlo,hCe⟩ := hReady hQ'
    have hA₀ : RatFits h L P ((⌈q⌉:ℚ)-q) := by rw [hCe]; exact hFA
    have hB₀ : RatFits h L P (q-(⌊q⌋:ℚ)) := by rw [hFlo]; exact hFB
    have hArgs₂ : evalArgs w s₁ [.reg 5,.reg 8,.reg 6,.reg 7,.reg 9]=some [af,one,L,P,heap] := by
      have h₅ : s₁.regs 5=af := hReg₁ 5 (by decide)
      have h₆ : s₁.regs 6=L := hReg₁ 6 (by decide)
      have h₇ : s₁.regs 7=P := hReg₁ 7 (by decide)
      have h₈ : s₁.regs 8=one := hReg₁ 8 (by decide)
      simp [evalArgs,Expr.eval,h₅,h₆,h₇,h₈,hH₁]
    have hw₂ : ∀ z∈[af,one,L,P,heap],z<2^w := by
      intro z hz
      apply hWords
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
      tauto
    have hPre₂ : (roundAvailabilityContract w h).pre [af,one,L,P,heap] s₁.mem :=
      ⟨af,one,L,P,heap,q,rfl,by rwa [hMem₁],by rwa [hMem₁],hQ',hF.trans hb,hOne.trans hb,
        hFloor,hB₀,hA₀,by rwa [hMem₁],by omega⟩
    obtain ⟨s₂,c₂,h₂,hCall₂,hOut₂,hHeap₂,hRegs₂,hC₂⟩ :=
      runs_call_of_meetsContract (r:=11) hAvail hArgs₂ hw₂ hPre₂ ω
    obtain ⟨hEq₂,hFrame₂,hZero₂,hAb,hAf⟩ := hOut₂
    change h₂=heap+7*L+1 at hEq₂
    change ∀ z<heap,s₂.mem z=s₁.mem z at hFrame₂
    change RatAt s₂.mem (heap+4*L+1) h L P (readRat s₁.mem af h L P-(⌊readRat s₁.mem af h L P⌋:ℚ)) at hAb
    change RatAt s₂.mem (heap+6*L+1) h L P ((⌈readRat s₁.mem af h L P⌉:ℚ)-readRat s₁.mem af h L P) at hAf
    rw [hMem₁,hFlow.2,hFlo] at hAb
    rw [hMem₁,hFlow.2,hCe] at hAf
    have hFrame : ∀ z<heap,s₂.mem z=mem z :=
      fun z hz => (hFrame₂ z hz).trans (congrFun hMem₁ z)
    obtain ⟨hRep₂,hPhi₂⟩ := himpl.1 b s x mem s₂.mem (fun z hz => (hFrame z (hFoot z hz).2).symm)
    let fwd := heap+6*L+1
    let bwd := heap+4*L+1
    have hH₂ : h₂<2^w := by omega
    have hFw : fwd<2^w := by dsimp [fwd]; omega
    have hBw : bwd<2^w := by dsimp [bwd]; omega
    have hFwd : fwd+L≤h₂ := by dsimp [fwd]; omega
    have hBwd : bwd+L≤h₂ := by dsimp [bwd]; omega
    have hw₃ : ∀ z∈[b,e.eid,e.u,e.v,ac,af,fwd,bwd,L,h₂],z<2^w := by
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | exact hWords _ (by simp [e,roundingEdge])
    have hRoom : h₂+3+4*L+allocation 1 [b,h₂,h₂+3+4*L]<2^w := by
      have := hAlloc b h₂ (h₂+3+4*L)
      omega
    obtain ⟨out,raw,c₃,y,hRun₃,hRep₃,hLo,hHi,hZero₃,hMem₃,hFoot₃,hC₃⟩ :=
      roundPackLink_runs D hD rate allocation R himpl hPack hLink e b ac af fwd bwd h₂ s x
        s₂.mem s₂.pos ω hw₃ ⟨by omega,by omega,hFwd,hBwd⟩
        (hCost.frozen hFrame (hC.trans hb)) (hFlow.frozen hFrame (hF.trans hb)) hAf hAb hInv hFit
        ⟨hFC,hFQ,hFA,hFB⟩ hu hv hDis hFresh (hRep₂ hRep)
        (fun z hz => ⟨(hFoot z hz).1,(hFoot z hz).2.trans_le (by omega)⟩) hZero₂ (by omega) hRoom
    have hReg₂ (i : ℕ) (hi : i<10) : s₂.regs i=s₀.regs i :=
      (hRegs₂ i (by omega)).trans (hReg₁ i hi)
    let args₃ : List Expr := [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,
       .bin .sub (.reg 11) (.reg 6),.bin .sub (.reg 11) (.bin .mul (.const 3) (.reg 6)),.reg 6,.reg 11]
    have hArgs₃ : evalArgs w s₂ args₃=some [b,e.eid,e.u,e.v,ac,af,fwd,bwd,L,h₂] := by
      have h₀ : s₂.regs 0=b := hReg₂ 0 (by decide)
      have h₁ : s₂.regs 1=e.eid := hReg₂ 1 (by decide)
      have h₂' : s₂.regs 2=e.u := hReg₂ 2 (by decide)
      have h₃ : s₂.regs 3=e.v := hReg₂ 3 (by decide)
      have h₄ : s₂.regs 4=ac := hReg₂ 4 (by decide)
      have h₅ : s₂.regs 5=af := hReg₂ 5 (by decide)
      have h₆ : s₂.regs 6=L := hReg₂ 6 (by decide)
      have hThree : 3<2^w := by omega
      have hTriple : 3*L<2^w := by omega
      have hF : h₂-L=fwd := by dsimp [fwd]; omega
      have hB' : h₂-3*L=bwd := by dsimp [bwd]; omega
      rw [← hF,← hB']
      dsimp only [args₃]
      eval_expr
    have hCall₃ := round_returning_call (dst:=11) hPackLink hArgs₃ hRun₃
    let final : State := ⟨raw.mem,Function.update s₂.regs 11 out,raw.pos⟩
    have hRet : Runs w p ω (.ret (.reg 11)) final (.returned out) final 2 :=
      runs_ret_iff.mpr ⟨out,by simp [final,Expr.eval],rfl,rfl,rfl⟩
    have hFract : Runs w p ω (.call 11 availability [.reg 5,.reg 8,.reg 6,.reg 7,.reg 9] ;;
        .call 11 packLink args₃ ;; .ret (.reg 11)) s₁ (.returned out) final (c₂+(16+c₃+1+2+1)+1) :=
      runs_seq_iff.mpr (Or.inr ⟨s₂,_,_,hCall₂,runs_seq_iff.mpr (Or.inr
        ⟨final,_,_,hCall₃,hRet,rfl⟩),rfl⟩)
    have hCond : Runs w p ω (.cond (.reg 10) (.ret (.reg 9))
        (.call 11 availability [.reg 5,.reg 8,.reg 6,.reg 7,.reg 9] ;;
        .call 11 packLink args₃ ;; .ret (.reg 11))) s₁ (.returned out) final
        (1+(c₂+(16+c₃+1+2+1)+1)+1) :=
      runs_cond_iff.mpr ⟨0,_,congrArg some hB,hFract,rfl⟩
    refine ⟨out,final,c₁+(1+(c₂+(16+c₃+1+2+1)+1)+1)+1,y,?_,
      by simpa only [hQ,Bool.false_eq_true,ite_false] using hRep₃,by omega,?_,hZero₃,?_,hFoot₃,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨s₁,_,_,hCall₁,hCond,rfl⟩)
    · have := hAlloc b h₂ (h₂+3+4*L)
      omega
    · intro z hz
      exact (hMem₃ z hz).trans (hFrame z (hz.trans_le hb))
    · change c₂≤5+(249*L+300)+1 at hC₂
      change _+R.phi b y raw.mem≤_
      omega

end MinCostFlow.IPM.Machine
