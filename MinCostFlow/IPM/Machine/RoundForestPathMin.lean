module

public import MinCostFlow.IPM.Machine.ForestContract
import WordRAM.Tactic

/-!
# Allocated path-minimum records

The dynamic forest reports its selected edge using a tagged block.
Reserve the whole block, including a zero suffix of its encoded
numbers, before passing any of its addresses to the next operation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Rounding WordRAM

/-- Call PathMin on [handle,u,v,heap], then keep its entire tagged
record below the returned heap, including any implicit zero words. -/
def roundForestPathMinBody (pathMin : ℕ) : Stmt :=
  .call 5 pathMin [.reg 0,.reg 1,.reg 2,.reg 4] ;;
  .assign 6 (.bin .add (.bin .add (.reg 4) (.const 4)) (.bin .mul (.const 2) (.reg 3))) ;;
  .cond (.bin .lt (.reg 5) (.reg 6)) (.ret (.reg 6)) (.ret (.reg 5))

/-- The padding and return contain no random instruction. -/
theorem roundForestPathMin_noRand (pathMin : ℕ) : (roundForestPathMinBody pathMin).NoRand := by
  simp [roundForestPathMinBody,Stmt.NoRand]

set_option maxHeartbeats 380000 in
/-- The padded path-minimum call keeps the same credited forest and
the exact tie choice specified by the dynamic forest's PathMin. -/
theorem roundForestPathMin_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (b u v heap : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,u,v,L,heap],z<2^w) (hw : 4<2^w)
    (hInv : D.Inv s) (hfits : ForestFits D h L P s) (hcomp : (D.toForest s).SameComp u v)
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) (hz : ZeroFrom mem heap)
    (hspace : heap+allocation 4 [b,u,v,heap]+4+2*L<2^w) :
    ∃ out final cost credit,
      Runs w p ω (roundForestPathMinBody (op 4)) (startState [b,u,v,L,heap] mem pos)
        (.returned out) final cost ∧
      PathHitAt final.mem heap h L P (D.pathMin s u v) ∧ R.rep b s credit final.mem ∧
      heap+4+2*L≤out ∧ out≤heap+allocation 4 [b,u,v,heap]+4+2*L ∧
      out<2^w ∧ ZeroFrom final.mem out ∧
      (∀ z<heap,¬R.foot b x z → final.mem z=mem z) ∧
      (∀ z,R.foot b credit z → R.foot b x z ∨ heap≤z ∧ z<out) ∧
      cost+R.phi b credit final.mem≤rate (D.toForest s).n+25+R.phi b x mem := by
  let args := [b,u,v,heap]
  have hArgs : ∀ z∈args,z<2^w := by
    intro z hz
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    all_goals exact hwords _ (by simp)
  have hPre : (forestMachineContract D w h L P rate allocation).pre 4 s args mem :=
    ⟨hInv,hfits,⟨b,u,v,heap,rfl,hcomp⟩⟩
  obtain ⟨body,hbody,o,st,c,hRun,s',y,hrep',hout,hmem,hcost⟩ :=
    himpl.2.2 4 b s x args mem pos ω hArgs rfl hrep hPre hfoot hz (by
      change heap+allocation 4 [b,u,v,heap]<2^w
      omega)
  obtain ⟨hState,hHit⟩ := hout
  have hs' : s'=s := hState
  subst s'
  have hEnd : o.value≤heap+allocation 4 [b,u,v,heap] := hmem.2.1
  have hEndFit : o.value<2^w := by omega
  have hPadded : heap+4+2*L<2^w := by omega
  have hSmall : 2*L<2^w := by omega
  have hH4 : heap+4<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hOne : 1<2^w := by omega
  let parent : State := ⟨st.mem,Function.update (startState [b,u,v,L,heap] mem pos).regs 5 o.value,st.pos⟩
  let sized : State := {parent with regs := Function.update parent.regs 6 (heap+4+2*L)}
  have hCall : Runs w p ω (.call 5 (op 4) [.reg 0,.reg 1,.reg 2,.reg 4])
      (startState [b,u,v,L,heap] mem pos) .normal parent (c+5) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,o,st,c,rfl,hbody,hRun,rfl,?_,by change c+5=4+c+1; omega⟩
    cases st
    rfl
  have hSet : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 4) (.const 4)) (.bin .mul (.const 2) (.reg 3))))
      parent .normal sized 8 := by
    apply runs_assign_iff.mpr
    refine ⟨_,by dsimp only [parent]; eval_expr,rfl,rfl,rfl⟩
  let out := max o.value (heap+4+2*L)
  have hCond : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 6)) (.ret (.reg 6)) (.ret (.reg 5)))
      sized (.returned out) sized 6 := by
    have he' : (Expr.reg 5).eval w sized=some o.value := by simp [sized,parent,Expr.eval]
    have he : (Expr.reg 6).eval w sized=some (heap+4+2*L) := by simp [sized,Expr.eval]
    by_cases hlt : o.value<heap+4+2*L
    · have hret : Runs w p ω (.ret (.reg 6)) sized (.returned out) sized 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=heap+4+2*L from max_eq_right hlt.le]; exact he,rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨1,2,Expr.eval_lt_true he' he hlt hOne,by simpa using hret,rfl⟩
    · have hle := Nat.le_of_not_gt hlt
      have hret : Runs w p ω (.ret (.reg 5)) sized (.returned out) sized 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=o.value from max_eq_left hle]; exact he',rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨0,2,Expr.eval_lt_false he' he hle hOne,by simpa using hret,rfl⟩
  have hBound : out≤heap+allocation 4 [b,u,v,heap]+4+2*L := max_le (by omega) (by omega)
  have hHere := le_max_left o.value (heap+4+2*L)
  refine ⟨out,sized,c+21,y,?_,hHit,hrep',le_max_right _ _,hBound,hBound.trans_lt hspace,
    fun q hq => hmem.2.2.1 q (hHere.trans hq),hmem.2.2.2.1,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨parent,c+5,15,hCall,
      runs_seq_iff.mpr (Or.inr ⟨sized,8,6,hSet,hCond,rfl⟩),rfl⟩)
  · intro q hq
    rcases hmem.2.2.2.2 q hq with hOld | ⟨hlo,hhi⟩
    · exact Or.inl hOld
    · exact Or.inr ⟨hlo,hhi.trans_le hHere⟩
  · change c+R.phi b y st.mem≤rate (D.toForest s).n+R.phi b x mem at hcost
    change c+21+R.phi b y st.mem≤_
    omega

end MinCostFlow.IPM.Machine
