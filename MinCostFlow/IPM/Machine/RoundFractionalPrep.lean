module

public import MinCostFlow.IPM.Machine.RoundConnected
import WordRAM.Tactic

/-!
# Preparing a fractional edge for the rounding step

Compute both availabilities and query the two endpoint roots.
Save the first root before the second query. The availability
blocks stay outside both forest footprints.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [b,eid,u,v,cost,flow,L,P,one,base,fuel,heap], prepare the edge.
Registers 12 and 15 give availability and forest heap ends. Registers
14 and 16 give the roots. -/
def roundFractionalPrepBody (B : RoundProcedures) : Stmt :=
  .call 12 B.availability [.reg 5,.reg 8,.reg 6,.reg 7,.reg 11] ;;
  .call 13 B.findRoot [.reg 0,.reg 2,.reg 12] ;;
  .assign 14 (.load (.reg 12)) ;;
  .call 15 B.findRoot [.reg 0,.reg 3,.reg 13] ;;
  .assign 16 (.load (.reg 13))

/-- The preparation uses deterministic numeric and tree calls. -/
theorem roundFractionalPrep_noRand (B : RoundProcedures) : (roundFractionalPrepBody B).NoRand := by
  simp [roundFractionalPrepBody,Stmt.NoRand]

set_option maxHeartbeats 550000 in
/-- Preparing a fractional edge reads its exact endpoints' roots,
preserves the flow table, and delivers both fixed-point availabilities
outside the forest's private memory. -/
theorem roundFractionalPrep_runs {w h L P A : ℕ} (D : DynForest) (hD : D.IsSpec)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (B : RoundProcedures) (hB : B.Linked w h P p op)
    (hAlloc : ∀ b v heap,allocation 0 [b,v,heap]≤A)
    (I : Instance) (j : Fin I.m) (q : ℚ) (b ac fp one base heap : ℕ) (s : D.State) (x : R.τ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hw : ∀ z∈[b,j.val,(I.edge j).tail,(I.edge j).head,ac,fp,L,P,one,base,I.m+1,heap],z<2^w)
    (hb : b≤heap) (hFp : fp+L≤heap) (hOne : one+L≤heap)
    (hQ : RatAt mem fp h L P q) (hUnit : RatAt mem one h L P 1)
    (hFrac : isIntRat q=false) (hFloor : RatFits h L P (⌊q⌋:ℚ))
    (hBwd : RatFits h L P (q-(⌊q⌋:ℚ))) (hFwd : RatFits h L P ((⌈q⌉:ℚ)-q))
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hu : (I.edge j).tail<(D.toForest s).n) (hv : (I.edge j).head<(D.toForest s).n)
    (hn : (D.toForest s).n≤2^w)
    (hRep : R.rep b s x mem) (hFoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hZero : ZeroFrom mem heap) (hSpace : heap+2*A+7*L+3<2^w) :
    let args := [b,j.val,(I.edge j).tail,(I.edge j).head,ac,fp,L,P,one,base,I.m+1,heap]
    let av := heap+7*L+1
    let af := heap+6*L+1
    let ab := heap+4*L+1
    ∃ out final cost y,
      Runs w p ω (roundFractionalPrepBody B) (startState args mem pos) .normal final cost ∧
      (∀ z<12,final.regs z=(startState args mem pos).regs z) ∧
      final.regs 12=av ∧ final.regs 15=out ∧
      final.regs 14=D.findRoot s (I.edge j).tail ∧ final.regs 16=D.findRoot s (I.edge j).head ∧
      R.rep b s y final.mem ∧ av≤out ∧ out≤heap+2*A+7*L+3 ∧ ZeroFrom final.mem out ∧
      (∀ z<b,final.mem z=mem z) ∧ (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      (∀ z,R.foot b y z → z<heap ∨ av≤z) ∧
      RatAt final.mem af h L P ((⌈q⌉:ℚ)-q) ∧ RatAt final.mem ab h L P (q-(⌊q⌋:ℚ)) ∧
      cost+R.phi b y final.mem≤2*rate (D.toForest s).n+249*L+400+R.phi b x mem := by
  dsimp only
  let u := (I.edge j).tail
  let v := (I.edge j).head
  let args := [b,j.val,u,v,ac,fp,L,P,one,base,I.m+1,heap]
  let parent := startState args mem pos
  let av := heap+7*L+1
  let af := heap+6*L+1
  let ab := heap+4*L+1
  have wAt (i : Fin 12) : args[i.val]'i.isLt<2^w := hw _ (List.getElem_mem (l:=args) i.isLt)
  have hw₀ : ∀ z∈[fp,one,L,P,heap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact wAt 5
    · exact wAt 8
    · exact wAt 6
    · exact wAt 7
    · exact wAt 11
  have hArgs₁ : evalArgs w parent [.reg 5,.reg 8,.reg 6,.reg 7,.reg 11]=some [fp,one,L,P,heap] := rfl
  obtain ⟨st₁,c₁,d₁,hCall₁,hOut₁,hReg₁,hRegs₁,hC₁⟩ :=
    runs_call_of_meetsContract (r:=12) hB.availability_spec hArgs₁ hw₀
      ⟨fp,one,L,P,heap,q,rfl,hQ,hUnit,hFrac,hFp,hOne,hFloor,hBwd,hFwd,hZero,by omega⟩ ω
  obtain ⟨he₁,hFrame₁,hZero₁,hBack₁,hFor₁⟩ := hOut₁
  have hd₁ : d₁=av := he₁
  rw [hd₁] at hReg₁ hZero₁
  change ∀ z<heap,st₁.mem z=mem z at hFrame₁
  change RatAt st₁.mem af h L P ((⌈readRat mem fp h L P⌉:ℚ)-readRat mem fp h L P) at hFor₁
  change RatAt st₁.mem ab h L P (readRat mem fp h L P-(⌊readRat mem fp h L P⌋:ℚ)) at hBack₁
  rw [hQ.2] at hFor₁ hBack₁
  have hAvEq : av=heap+7*L+1 := rfl
  have hFitAv : av<2^w := by dsimp [av]; omega
  have hav : heap≤av := by dsimp [av]; omega
  have havB : b≤av := hb.trans hav
  obtain ⟨hRep₁,hPhi₁⟩ := himpl.1 b s x mem st₁.mem (fun z hz => (hFrame₁ z (hFoot z hz).2).symm)
  have hAlloc₂ := hAlloc b u av
  have hSp₂ : av+allocation 0 [b,u,av]+1<2^w := by omega
  have hw₂ : ∀ z∈[b,u,av],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact wAt 0
    · exact wAt 2
    · exact hFitAv
  obtain ⟨d₂,raw₂,c₂,x₂,hRun₂,hRoot₂,hRep₂,hLo₂,hHi₂,hZero₂,hBelow₂,hFoot₂,hMem₂,hPriv₂,hC₂⟩ :=
    roundFindRoot_runs D rate allocation R himpl b u av s x st₁.mem st₁.pos ω hw₂ havB
      hInv hFit hu (hRep₁ hRep) (fun z hz => ⟨(hFoot z hz).1,(hFoot z hz).2.trans_le hav⟩)
      hZero₁ hSp₂
  have hArgs₂ : evalArgs w st₁ [.reg 0,.reg 2,.reg 12]=some [b,u,av] := by
    have h₀ : st₁.regs 0=b := hRegs₁ 0 (by decide)
    have h₂ : st₁.regs 2=u := hRegs₁ 2 (by decide)
    simp [evalArgs,Expr.eval,h₀,h₂,hReg₁]
  have hCall₂ := round_returning_call (dst:=13) hB.root_at hArgs₂ hRun₂
  let st₂ : State := ⟨raw₂.mem,Function.update st₁.regs 13 d₂,raw₂.pos⟩
  let rootU := D.findRoot s u
  let st₃ := {st₂ with regs := Function.update st₂.regs 14 rootU}
  have hUA : rootU<2^w := (hD.2.2.1 s u hInv hu).1.trans_le hn
  have hLa : st₂.regs 12=av := hReg₁
  have hRa : st₂.mem av=rootU := hRoot₂
  have hRead₂ : Runs w p ω (.assign 14 (.load (.reg 12))) st₂ .normal st₃ 3 :=
    runs_assign_iff.mpr ⟨_,by eval_expr,rfl,rfl,rfl⟩
  have hA₃ := hAlloc b v d₂
  have hSp₃ : d₂+allocation 0 [b,v,d₂]+1<2^w := by omega
  have hd₂ : d₂<2^w := by omega
  have hw₃ : ∀ z∈[b,v,d₂],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact wAt 0
    · exact wAt 3
    · exact hd₂
  obtain ⟨out,raw₃,c₃,y,hRun₃,hRoot₃,hRep₃,hLo₃,hHi₃,hZero₃,hBelow₃,hFoot₃,hMem₃,hPriv₃,hC₃⟩ :=
    roundFindRoot_runs D rate allocation R himpl b v d₂ s x₂ st₃.mem st₃.pos ω hw₃
      (havB.trans (by omega)) hInv hFit hv hRep₂ hFoot₂ hZero₂ hSp₃
  have hArg₃ : evalArgs w st₃ [.reg 0,.reg 3,.reg 13]=some [b,v,d₂] := by
    have h₀ : st₁.regs 0=b := hRegs₁ 0 (by decide)
    have h₃ : st₁.regs 3=v := hRegs₁ 3 (by decide)
    simp [evalArgs,Expr.eval,st₃,st₂,h₀,h₃]
  have hCall₃ := round_returning_call (dst:=15) hB.root_at hArg₃ hRun₃
  let st₄ : State := ⟨raw₃.mem,Function.update st₃.regs 15 out,raw₃.pos⟩
  let rootV := D.findRoot s v
  let final := {st₄ with regs := Function.update st₄.regs 16 rootV}
  have hVA : rootV<2^w := (hD.2.2.1 s v hInv hv).1.trans_le hn
  have hLastArg : st₄.regs 13=d₂ := by simp [st₄,st₃,st₂]
  have hLastMem : st₄.mem d₂=rootV := hRoot₃
  have hRead₃ : Runs w p ω (.assign 16 (.load (.reg 13))) st₄ .normal final 3 :=
    runs_assign_iff.mpr ⟨_,by eval_expr,rfl,rfl,rfl⟩
  have hAvFrame : ∀ z,heap≤z → z<av → final.mem z=st₁.mem z := by
    intro z hl hh
    have h₂ := hMem₂ z hh (fun hz => (Nat.not_lt_of_ge hl) (hFoot z hz).2)
    have h₃ := hMem₃ z (by omega) (fun hz => by
      rcases hPriv₂ z hz with hz | ⟨hz,_⟩
      · exact (Nat.not_lt_of_ge hl) (hFoot z hz).2
      · exact (Nat.not_lt_of_ge hz) hh)
    exact h₃.trans h₂
  have hFor : RatAt final.mem af h L P ((⌈q⌉:ℚ)-q) :=
    hFor₁.agree (fun i hi => hAvFrame _ (by dsimp [af]; omega) (by dsimp [af,av]; omega))
  have hBack : RatAt final.mem ab h L P (q-(⌊q⌋:ℚ)) :=
    hBack₁.agree (fun i hi => hAvFrame _ (by dsimp [ab]; omega) (by dsimp [ab,av]; omega))
  have hFresh : ∀ z,R.foot b y z → z<heap ∨ av≤z := by
    intro z hz
    rcases hPriv₃ z hz with hz | ⟨hz,_⟩
    · rcases hPriv₂ z hz with hz | ⟨hz,_⟩
      · exact Or.inl (hFoot z hz).2
      · exact Or.inr hz
    · exact Or.inr ((show av≤d₂ from by omega).trans hz)
  refine ⟨out,final,c₁+(3+c₂+1+(3+(3+c₃+1+3+1)+1)+1)+1,y,?_,?_,
    by simpa [final,st₄,st₃,st₂] using hReg₁,by simp [final,st₄],by simp [final,st₄,st₃,rootU,u],
    by simp [final,rootV,v],hRep₃,by omega,?_,hZero₃,?_,hFoot₃,hFresh,hFor,hBack,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st₁,_,_,hCall₁,runs_seq_iff.mpr (Or.inr
      ⟨st₂,_,_,hCall₂,runs_seq_iff.mpr (Or.inr ⟨st₃,_,_,hRead₂,
        runs_seq_iff.mpr (Or.inr ⟨st₄,_,_,hCall₃,hRead₃,rfl⟩),rfl⟩),rfl⟩),rfl⟩)
  · intro z hz
    have h13 : z≠13 := by omega
    have h14 : z≠14 := by omega
    have h15 : z≠15 := by omega
    have h16 : z≠16 := by omega
    simpa [final,st₄,st₃,st₂,h13,h14,h15,h16] using hRegs₁ z (by omega)
  · omega
  · intro z hz
    exact (hBelow₃ z hz).trans ((hBelow₂ z hz).trans (hFrame₁ z (hz.trans_le hb)))
  · change c₁≤5+(249*L+300)+1 at hC₁
    change c₂+R.phi b x₂ raw₂.mem≤rate (D.toForest s).n+16+R.phi b x st₁.mem at hC₂
    change c₃+R.phi b y raw₃.mem≤rate (D.toForest s).n+16+R.phi b x₂ raw₂.mem at hC₃
    change c₁+(3+c₂+1+(3+(3+c₃+1+3+1)+1)+1)+1+R.phi b y raw₃.mem≤
      2*rate (D.toForest s).n+249*L+400+R.phi b x mem
    omega

end MinCostFlow.IPM.Machine
