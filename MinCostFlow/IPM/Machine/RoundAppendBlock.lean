module

public import MinCostFlow.IPM.Machine.RoundFlowTable
import WordRAM.Tactic

/-!
# Appending one exact block to a forest record

The working record is allocated in fresh memory. Copy a signed
block verbatim and return the first cell after it.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On [source,L,heap], append the L-word block. -/
def roundAppendBlockBody (copy : ℕ) : Stmt :=
  .call 3 copy [.reg 0,.reg 2,.reg 1] ;;
  .ret (.bin .add (.reg 2) (.reg 1))

/-- The fixed-point encoding, regardless of precision, is copied exactly. -/
def roundAppendBlockContract (w : ℕ) : Contract :=
  let c := heapContract w
    (fun args _ => ∃ src L heap,args=[src,L,heap] ∧ src+L≤heap ∧ 1<2^w)
    (fun args mem final => ∀ i<args.getD 1 0,
      final (heapArg args+i)=mem (args.getD 0 0+i))
    (fun args _ => 17*args.getD 1 0+20) (fun args _ => args.getD 1 0)
  {c with post := fun args mem v final => c.post args mem v final ∧ v=heapArg args+args.getD 1 0}

/-- The block copy and address calculation are deterministic. -/
theorem roundAppendBlock_noRand (copy : ℕ) : (roundAppendBlockBody copy).NoRand := by
  simp [roundAppendBlockBody,Stmt.NoRand]

/-- The append preserves the allocated prefix and returns the exact end. -/
theorem roundAppendBlock_meetsContract {w entry copy : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (roundAppendBlockBody copy))
    (hCopy : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (roundAppendBlockContract w) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hWords hPre
  obtain ⟨⟨src,L,heap,rfl,hsrc,hOne⟩,hz,hspace⟩ := hPre
  change ZeroFrom mem heap at hz
  change heap+L<2^w at hspace
  have hSrc : src<2^w := hWords _ (by simp)
  have hHeap : heap<2^w := hWords _ (by simp)
  have hL : L<2^w := hWords _ (by simp)
  apply runs_start_le
  unfold roundAppendBlockBody
  refine runs_seq_call_le hCopy (vs:=[src,heap,L]) rfl (by wram_words)
    ⟨src,heap,L,rfl,hOne,by omega,by omega,Or.inr hsrc⟩ ?_
  intro r final pos' hout
  obtain ⟨src',dst',len',heq,_,hBlock,hFrame⟩ := hout
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  refine runs_ret_le (v:=heap+L) (by eval_expr) ?_ ?_
  · change (heap≤heap+L ∧ heap+L≤heap+L ∧ (∀ z<heap,final z=mem z) ∧
      ZeroFrom final (heap+L) ∧ (∀ i<L,final (heap+i)=mem (src+i))) ∧ heap+L=heap+L
    exact ⟨⟨by omega,le_rfl,fun z hz' => hFrame z (Or.inl hz'),
      fun z hz' => (hFrame z (Or.inr hz')).trans (hz z (by omega)),hBlock⟩,rfl⟩
  · simp only [roundAppendBlockContract,heapContract,copyWordsContract,List.getD_cons_zero,List.getD_cons_succ,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin]
    omega

/-- The append output carries the same rational as its source. -/
theorem roundAppendBlock_rat {w src L heap h P v : ℕ} {mem final : ℕ → ℕ} {q : ℚ}
    (hq : RatAt mem src h L P q)
    (hout : (roundAppendBlockContract w).post [src,L,heap] mem v final) :
    RatAt final heap h L P q := by
  have hCopy : ∀ i<L,final (heap+i)=mem (src+i) := hout.1.2.2.2.2
  constructor
  · intro j hj
    rw [hCopy j hj]
    exact hq.1 j hj
  · unfold readRat at *
    rw [Num.intVal_congr hCopy]
    exact hq.2

end MinCostFlow.IPM.Machine
