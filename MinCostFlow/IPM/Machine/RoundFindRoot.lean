module

public import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic

/-!
# Reading a dynamic forest root

The rounder reads the root into a register before issuing the next
forest call. This handles an answer of zero even if it was represented
by the zero part of memory past the returned heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,vertex,heap], return the heap and save the root
in the answer cell at the input heap. -/
def roundFindRootBody (findRoot : ℕ) : Stmt :=
  .call 3 findRoot [.reg 0,.reg 1,.reg 2] ;;
  .assign 4 (.bin .add (.reg 2) (.const 1)) ;;
  .cond (.bin .lt (.reg 3) (.reg 4)) (.ret (.reg 4)) (.ret (.reg 3))

/-- The path to a root answer uses a deterministic call and padding. -/
theorem roundFindRoot_noRand (findRoot : ℕ) : (roundFindRootBody findRoot).NoRand := by
  simp [roundFindRootBody,Stmt.NoRand]

/-- A root call returns the exact vertex name, with no change to the
abstract state and the answer cell below the next heap pointer. -/
theorem roundFindRoot_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (b v heap : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,v,heap],z<2^w) (hb : b≤heap)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s) (hV : v<(D.toForest s).n)
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → b≤z ∧ z<heap) (hz : ZeroFrom mem heap)
    (hSpace : heap+allocation 0 [b,v,heap]+1<2^w) :
    ∃ out final c y,
      Runs w p ω (roundFindRootBody (op 0)) (startState [b,v,heap] mem pos) (.returned out) final c ∧
      final.mem heap=D.findRoot s v ∧ R.rep b s y final.mem ∧
      heap+1≤out ∧ out≤heap+allocation 0 [b,v,heap]+1 ∧
      ZeroFrom final.mem out ∧ (∀ z<b,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      (∀ z<heap,¬R.foot b x z → final.mem z=mem z) ∧
      (∀ z,R.foot b y z → R.foot b x z ∨ heap≤z ∧ z<out) ∧
      c+R.phi b y final.mem≤rate (D.toForest s).n+16+R.phi b x mem := by
  let parent := startState [b,v,heap] mem pos
  let exprs : List Expr := [.reg 0,.reg 1,.reg 2]
  have hArgs : evalArgs w parent exprs=some [b,v,heap] := rfl
  have hPre : (forestMachineContract D w h L P rate allocation).pre 0 s [b,v,heap] mem :=
    ⟨hInv,hFit,⟨b,v,heap,rfl,hV⟩⟩
  obtain ⟨raw,st,c,s',y,hRun,hReg,hRegs,hout,hRep,hMem,hC⟩ :=
    roundForest_call_runs (i:=0) (dst:=3) D rate allocation R himpl
      parent ω s x exprs [b,v,heap] hArgs hwords rfl hrep hPre
      (fun z hz' => (hfoot z hz').2) hz (by change heap+allocation 0 [b,v,heap]<2^w; omega)
  change s'=s ∧ st.mem heap=D.findRoot s v at hout
  obtain ⟨hs',hRoot⟩ := hout
  subst s'
  let final := {st with regs := Function.update st.regs 4 (heap+1)}
  let out := max raw (heap+1)
  have hOne : 1<2^w := by omega
  have hOpt : heap+1<2^w := by omega
  have hRegH : st.regs 2=heap := hRegs 2 (by decide)
  have hSet : Runs w p ω (.assign 4 (.bin .add (.reg 2) (.const 1))) st .normal final 4 :=
    runs_assign_iff.mpr ⟨_,by eval_expr,rfl,rfl,rfl⟩
  have hCond : Runs w p ω (.cond (.bin .lt (.reg 3) (.reg 4)) (.ret (.reg 4)) (.ret (.reg 3)))
      final (.returned out) final 6 := by
    have h3 : (Expr.reg 3).eval w final=some raw := by simp [final,Expr.eval,hReg]
    have h4 : (Expr.reg 4).eval w final=some (heap+1) := by simp [final,Expr.eval]
    by_cases ho : raw<heap+1
    · have hret : Runs w p ω (.ret (.reg 4)) final (.returned out) final 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=heap+1 from max_eq_right ho.le]; exact h4,rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨1,2,Expr.eval_lt_true h3 h4 ho hOne,hret,rfl⟩
    · have hle := Nat.le_of_not_gt ho
      have hret : Runs w p ω (.ret (.reg 3)) final (.returned out) final 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=raw from max_eq_left hle]; exact h3,rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨0,2,Expr.eval_lt_false h3 h4 hle hOne,hret,rfl⟩
  have hRaw : raw≤heap+allocation 0 [b,v,heap] := hMem.2.1
  have ho : raw≤out := le_max_left _ _
  refine ⟨out,final,c+12,y,?_,hRoot,hRep,le_max_right _ _,max_le (by omega) (by omega),
    fun z hz' => hMem.2.2.1 z (ho.trans hz'),?_,?_,hMem.2.2.2.1,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st,c,11,hRun,runs_seq_iff.mpr (Or.inr ⟨final,4,6,hSet,hCond,rfl⟩),rfl⟩)
  · intro z hz'
    exact hMem.2.2.2.1 z (show z<heap from hz'.trans_le hb)
      (fun hf => (Nat.not_le_of_lt hz') (hfoot z hf).1)
  · intro z hz'
    rcases hMem.2.2.2.2 z hz' with hz' | ⟨hlo,hhi⟩
    · exact ⟨(hfoot z hz').1,(hfoot z hz').2.trans_le (by unfold out; omega)⟩
    · exact ⟨hb.trans hlo,hhi.trans_le ho⟩
  · intro z hz'
    exact (hMem.2.2.2.2 z hz').imp id (fun ⟨hlo,hhi⟩ => ⟨hlo,hhi.trans_le ho⟩)
  · change c+R.phi b y st.mem≤rate (D.toForest s).n+3+1+R.phi b x mem at hC
    change c+12+R.phi b y st.mem≤_
    omega

end MinCostFlow.IPM.Machine
