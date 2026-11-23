module

public import MinCostFlow.IPM.Machine.RoundCleanupQuery
import WordRAM.Tactic

/-!
# Executing the cut prefix of recursive path cleanup

The prefix saves the split endpoints and the smaller fuel. It then
flushes the exact hit flow and cuts its edge before either recursive
call runs.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Execute the register updates that prepare the two recursive calls. -/
theorem roundCleanupSave_runs {w a fuel : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {hit : PathHit} {h L P : ℕ}
    (ha : st.regs 5=a) (hf : st.regs 6=fuel+1)
    (hHit : PathHitAt st.mem a h L P (some hit))
    (hFuel : fuel+1<2^w) (ha' : a+3<2^w) :
    let final := {st with regs := Function.update (Function.update (Function.update st.regs 9 hit.x) 10 hit.y) 11 fuel}
    Runs w p ω roundCleanupSave st .normal final 16 := by
  dsimp only
  let s₁ := {st with regs := Function.update st.regs 9 hit.x}
  let s₂ := {s₁ with regs := Function.update s₁.regs 10 hit.y}
  have hThree : 3<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hOne : 1<2^w := by omega
  have ha₂ : a+2<2^w := by omega
  have hmem := pathHit_words hHit
  have hEvalX : (Expr.load (.bin .add (.reg 5) (.const 2))).eval w st=some hit.x := by
    eval_expr
  have hEvalY : (Expr.load (.bin .add (.reg 5) (.const 3))).eval w s₁=some hit.y := by
    have hm : s₁.mem (a+3)=hit.y := hmem.2.2.2
    eval_expr
  have hEvalFuel : (Expr.bin .sub (.reg 6) (.const 1)).eval w s₂=some fuel := by
    have hVal : (Expr.reg 6).eval w s₂=some (fuel+1) := by simpa [s₂,s₁,Expr.eval] using hf
    rw [Expr.eval_sub hVal (by eval_expr) (by omega)]
    simp
  have h₁ : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 2)))) st .normal s₁ 5 :=
    runs_assign_iff.mpr ⟨_,hEvalX,rfl,rfl,rfl⟩
  have h₂ : Runs w p ω (.assign 10 (.load (.bin .add (.reg 5) (.const 3)))) s₁ .normal s₂ 5 :=
    runs_assign_iff.mpr ⟨_,hEvalY,rfl,rfl,rfl⟩
  have h₃ : Runs w p ω (.assign 11 (.bin .sub (.reg 6) (.const 1))) s₂ .normal
      {s₂ with regs := Function.update s₂.regs 11 fuel} 4 :=
    runs_assign_iff.mpr ⟨_,hEvalFuel,rfl,rfl,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s₁,5,10,h₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂,5,4,h₂,h₃,rfl⟩),rfl⟩)

/-- The actual cut prefix preserves the inputs for the recursive
calls. The saved endpoint registers never depend on the post-cut
contents of the PathMin record. -/
theorem roundCleanupCut_runs {w h L P copy entry : ℕ} (D : DynForest) (hD : D.IsSpec)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hBody : p.procs[entry]?=some (roundFlushCutBody copy (op 2)))
    (I : Instance) (e : Fin I.m) (hit : PathHit) (heid : hit.eid=e.val)
    (b a base heap fuel : ℕ) (s : D.State) (x : R.τ) (st : State) (ω : ℕ → Bool)
    (regs : st.regs 0=b ∧ st.regs 3=base ∧ st.regs 4=L ∧ st.regs 5=a ∧
      st.regs 6=fuel+1 ∧ st.regs 7=heap)
    (hFuel : fuel+1<2^w)
    (flow : Fin I.m → ℚ) (hflow : RoundFlowAt I st.mem base h L P flow)
    (hhit : PathHitAt st.mem a h L P (some hit)) (hL : 0<L)
    (hTable : base+I.m*L≤b) (hb : b≤a) (hBlock : a+4+2*L≤heap)
    (hX : hit.x<2^w) (hY : hit.y<2^w)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s)
    (hrep : R.rep b s x st.mem) (hfoot : ∀ z,R.foot b x z → b≤z ∧ z<heap)
    (hz : ZeroFrom st.mem heap) (hSpace : heap+allocation 2 [b,hit.x,hit.y,heap]<2^w) :
    ∃ out final cost y,
      Runs w p ω (roundCleanupSave ;; .call 7 entry roundCleanupCutArgs)
        st .normal final cost ∧
      R.rep b (D.cut s hit.x hit.y) y final.mem ∧
      RoundFlowAt I final.mem base h L P (fun j => if j.val=hit.eid then hit.flow else flow j) ∧
      heap≤out ∧ out≤heap+allocation 2 [b,hit.x,hit.y,heap] ∧ ZeroFrom final.mem out ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧ (∀ z<base,final.mem z=st.mem z) ∧
      (∀ j<7,final.regs j=st.regs j) ∧
      final.regs 7=out ∧ final.regs 9=hit.x ∧ final.regs 10=hit.y ∧ final.regs 11=fuel ∧
      cost+R.phi b y final.mem≤rate (D.toForest s).n+(copyWordsContract w).cost [a+4+L,base+e.val*L,L] st.mem
        +80+R.phi b x st.mem := by
  obtain ⟨h₀,h₃,h₄,h₅,h₆,h₇⟩ := regs
  let saved := {st with regs := Function.update (Function.update (Function.update st.regs 9 hit.x) 10 hit.y) 11 fuel}
  have hSave : Runs w p ω roundCleanupSave st .normal saved 16 :=
    roundCleanupSave_runs h₅ h₆ hhit hFuel (by omega)
  obtain ⟨out,raw,c,y,hRun,hRep,hFrame,hFoot,hFlow,hCost⟩ :=
    roundFlushCut_runs D hD rate allocation R himpl hCopy I e hit heid b a base heap s x
      st.mem st.pos ω flow hflow hhit hL hTable hb hBlock hX hY hInv hFit hrep hfoot hz hSpace
  have hArgs : evalArgs w saved roundCleanupCutArgs=some [b,a,base,L,heap] := by
    simp [roundCleanupCutArgs,evalArgs,saved,Expr.eval,h₀,h₃,h₄,h₅,h₇]
  have hCall := round_returning_call (dst:=7) hBody hArgs hRun
  let final : State := ⟨raw.mem,Function.update saved.regs 7 out,raw.pos⟩
  refine ⟨out,final,16+(5+c+1)+1,y,?_,hRep,?_,hFrame.1,hFrame.2.1,hFrame.2.2.1,
    ?_,?_,?_,by simp [final],by simp [final,saved],by simp [final,saved],by simp [final,saved],?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨saved,_,_,hSave,hCall,rfl⟩)
  · intro j
    by_cases hje : j=e
    · subst j
      simpa [← heid] using hFlow e
    · have hjval : j.val≠hit.eid := by
        rw [heid]
        exact fun hv => hje (Fin.ext hv)
      simpa [hje,hjval] using hFlow j
  · intro z hz'
    rcases hFoot z hz' with hz' | ⟨hlo,hhi⟩
    · exact ⟨(hfoot z hz').1,(hfoot z hz').2.trans_le hFrame.1⟩
    · exact ⟨by omega,hhi⟩
  · intro z hz'
    exact hFrame.2.2.2.1 z (by omega) (by
      rintro (hz'' | ⟨hh,_⟩)
      · have := (hfoot z hz'').1
        omega
      · omega)
  · intro j hj
    have h7' : j≠7 := by omega
    have h9 : j≠9 := by omega
    have h10 : j≠10 := by omega
    have h11 : j≠11 := by omega
    simp [final,saved,h7',h9,h10,h11]
  · change 16+(5+c+1)+1+R.phi b y raw.mem≤_
    omega

end MinCostFlow.IPM.Machine
