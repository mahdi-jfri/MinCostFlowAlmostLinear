module

public import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic

/-!
# Reading the signed forest path cost

Reserve all limbs of the PathSum answer before using it in the
cost comparison that chooses a cycle direction.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [forest,from,to,L,heap], return the padded heap after the
path-cost call. The answer stays at the input heap. -/
def roundPathSumBody (pathSum : ℕ) : Stmt :=
  .call 5 pathSum [.reg 0,.reg 1,.reg 2,.reg 4] ;;
  .assign 6 (.bin .add (.reg 4) (.reg 3)) ;;
  .cond (.bin .lt (.reg 5) (.reg 6)) (.ret (.reg 6)) (.ret (.reg 5))

/-- The path-cost call and padding are deterministic. -/
theorem roundPathSum_noRand (pathSum : ℕ) : (roundPathSumBody pathSum).NoRand := by
  simp [roundPathSumBody,Stmt.NoRand]

/-- The PathSum answer is the full signed cost block at precision zero.
The query leaves the same abstract forest and transfers its credit. -/
theorem roundPathSum_runs {w h L P : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (b u v heap : ℕ) (s : D.State) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,u,v,L,heap],z<2^w) (hb : b≤heap) (hL : 0<L)
    (hInv : D.Inv s) (hFit : ForestFits D h L P s) (hComp : (D.toForest s).SameComp u v) (hSum : Num.Fits h L (D.pathSum s u v))
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → b≤z ∧ z<heap) (hz : ZeroFrom mem heap)
    (hSpace : heap+allocation 5 [b,u,v,heap]+L<2^w) :
    ∃ out final c y,
      Runs w p ω (roundPathSumBody (op 5)) (startState [b,u,v,L,heap] mem pos) (.returned out) final c ∧
      RatAt final.mem heap h L 0 (D.pathSum s u v) ∧ R.rep b s y final.mem ∧
      heap+L≤out ∧ out≤heap+allocation 5 [b,u,v,heap]+L ∧
      ZeroFrom final.mem out ∧ (∀ z<b,final.mem z=mem z) ∧
      (∀ z,R.foot b y z → b≤z ∧ z<out) ∧
      (∀ z<heap,¬R.foot b x z → final.mem z=mem z) ∧
      (∀ z,R.foot b y z → R.foot b x z ∨ heap≤z ∧ z<out) ∧
      c+R.phi b y final.mem≤rate (D.toForest s).n+17+R.phi b x mem := by
  let parent := startState [b,u,v,L,heap] mem pos
  let exprs : List Expr := [.reg 0,.reg 1,.reg 2,.reg 4]
  have hArgs : evalArgs w parent exprs=some [b,u,v,heap] := rfl
  have hPre : (forestMachineContract D w h L P rate allocation).pre 5 s [b,u,v,heap] mem :=
    ⟨hInv,hFit,⟨b,u,v,heap,rfl,hComp,hSum⟩⟩
  have hw : ∀ z∈[b,u,v,heap],z<2^w := by
    intro z hz'
    apply hwords
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz' ⊢
    tauto
  obtain ⟨raw,st,c,s',y,hRun,hReg,hRegs,hout,hRep,hMem,hC⟩ :=
    roundForest_call_runs (i:=5) (dst:=5) D rate allocation R himpl
      parent ω s x exprs [b,u,v,heap] hArgs hw rfl hrep hPre
      (fun z hz' => (hfoot z hz').2) hz (by change heap+allocation 5 [b,u,v,heap]<2^w; omega)
  change s'=s ∧ Num.Valid st.mem heap h L ∧ Num.intVal st.mem heap h L=D.pathSum s u v at hout
  obtain ⟨hs',hValue,hSumEq⟩ := hout
  subst s'
  let final := {st with regs := Function.update st.regs 6 (heap+L)}
  let out := max raw (heap+L)
  have hOne : 1<2^w := by omega
  have hOpt : heap+L<2^w := by omega
  have hRegH : st.regs 4=heap := hRegs 4 (by decide)
  have hRegL : st.regs 3=L := hRegs 3 (by decide)
  have hSet : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.reg 3))) st .normal final 4 :=
    runs_assign_iff.mpr ⟨_,by eval_expr,rfl,rfl,rfl⟩
  have hCond : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 6)) (.ret (.reg 6)) (.ret (.reg 5)))
      final (.returned out) final 6 := by
    have h3 : (Expr.reg 5).eval w final=some raw := by simp [final,Expr.eval,hReg]
    have h4 : (Expr.reg 6).eval w final=some (heap+L) := by simp [final,Expr.eval]
    by_cases ho : raw<heap+L
    · have hret : Runs w p ω (.ret (.reg 6)) final (.returned out) final 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=heap+L from max_eq_right ho.le]; exact h4,rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨1,2,Expr.eval_lt_true h3 h4 ho hOne,hret,rfl⟩
    · have hle := Nat.le_of_not_gt ho
      have hret : Runs w p ω (.ret (.reg 5)) final (.returned out) final 2 :=
        runs_ret_iff.mpr ⟨out,by rw [show out=raw from max_eq_left hle]; exact h3,rfl,rfl,rfl⟩
      exact runs_cond_iff.mpr ⟨0,2,Expr.eval_lt_false h3 h4 hle hOne,hret,rfl⟩
  have hRaw : raw≤heap+allocation 5 [b,u,v,heap] := hMem.2.1
  have ho : raw≤out := le_max_left _ _
  refine ⟨out,final,c+12,y,?_,⟨hValue,by simp [final,readRat,hSumEq]⟩,hRep,le_max_right _ _,max_le (by omega) (by omega),
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
  · change c+R.phi b y st.mem≤rate (D.toForest s).n+4+1+R.phi b x mem at hC
    change c+12+R.phi b y st.mem≤_
    omega

end MinCostFlow.IPM.Machine
