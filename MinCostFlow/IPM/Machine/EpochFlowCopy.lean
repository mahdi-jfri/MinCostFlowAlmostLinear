module

public import MinCostFlow.IPM.Machine.Layout
public import WordRAM.CopyWords
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# A separate mutable copy of the epoch base flow

Keep the epoch's base flow in its old block and copy all fixed-point
coordinates into a fresh mutable cache. Later reported-coordinate writes
then leave the base unchanged. The program uses the library's verified
word-copy procedure and counts its full cost.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[source,m,L,heap]`; copy `m*L` words and return their end. -/
def epochFlowCopyBody (copy : ℕ) : Stmt :=
  .call 4 copy [.reg 0,.reg 3,.bin .mul (.reg 1) (.reg 2)] ;;
  .ret (.bin .add (.reg 3) (.bin .mul (.reg 1) (.reg 2)))

/-- Fresh exact word copy, with the complete old-prefix frame. No
rounding occurs, so every decoded fixed-point coordinate is unchanged. -/
def epochFlowCopyContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ source m L heap,args=[source,m,L,heap] ∧
      source+m*L≤heap ∧ 1<2^w)
    (fun args mem final => ∀ i<args.getD 1 0*args.getD 2 0,
      final (heapArg args+i)=mem (args.getD 0 0+i))
    (fun args _ => 17*(args.getD 1 0*args.getD 2 0)+40)
    (fun args _ => args.getD 1 0*args.getD 2 0)
  {C with post := fun args mem v final => C.post args mem v final ∧
    v=heapArg args+args.getD 1 0*args.getD 2 0}

/-- The caller's copy and return contain no random instruction. -/
theorem epochFlowCopy_noRand (copy : ℕ) : (epochFlowCopyBody copy).NoRand := by
  simp [epochFlowCopyBody,Stmt.NoRand]

/-- The actual library copy and caller meet the fresh-flow contract in
at most seventeen operations per word plus forty caller operations. -/
theorem epochFlowCopy_meetsContract {w entry copy : ℕ} {p : Program}
    (hp : p.procs[entry]?=some (epochFlowCopyBody copy))
    (hcopy : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (epochFlowCopyContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨⟨source,m,L,heap,rfl,hsource,hOne⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+m*L<2^w at hspace
  have hs := hwords source (by simp)
  have hm := hwords m (by simp)
  have hL := hwords L (by simp)
  have hh := hwords heap (by simp)
  have hcount : m*L<2^w := by omega
  apply runs_start_le
  unfold epochFlowCopyBody
  refine runs_seq_call_le hcopy (vs:=[source,heap,m*L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨source,heap,m*L,rfl,hOne,by omega,by omega,Or.inr hsource⟩
  intro v final pos' hout
  obtain ⟨source',heap',len',heq,_,hcopied,hframe⟩ := hout
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  refine runs_ret_le (v:=heap+m*L) (by eval_expr) ?_ ?_
  · change (heap≤heap+m*L ∧ heap+m*L≤heap+m*L ∧
      (∀ z<heap,final z=mem z) ∧ ZeroFrom final (heap+m*L) ∧
      (∀ i<m*L,final (heap+i)=mem (source+i))) ∧ heap+m*L=heap+m*L
    refine ⟨⟨by omega,le_rfl,?_,?_,hcopied⟩,rfl⟩
    · intro z hz'
      exact hframe z (Or.inl hz')
    · intro z hz'
      exact (hframe z (Or.inr hz')).trans (hz z (by omega))
  · simp only [epochFlowCopyContract,heapContract,copyWordsContract,Expr.size_reg,Expr.size_bin,
      argsSize_cons,argsSize_nil,List.getD_cons_zero,List.getD_cons_succ]
    omega

/-- Every copied coordinate has the original valid fixed-point words
and equals the preserved epoch base in the actual final memory. -/
theorem epochFlowCopy_coordinate {w source m L heap v h P e : ℕ} {mem final : ℕ → ℕ}
    (hout : (epochFlowCopyContract w).post [source,m,L,heap] mem v final)
    (hsource : source+m*L≤heap) (he : e<m)
    (hvalid : Num.Valid mem (source+e*L) h L) :
    Num.Valid final (heap+e*L) h L ∧
      Num.fixVal final (heap+e*L) h L P=Num.fixVal final (source+e*L) h L P := by
  have hcopied := hout.1.2.2.2.2
  change ∀ i<m*L,final (heap+i)=mem (source+i) at hcopied
  have hframe := hout.1.2.2.1
  change ∀ z<heap,final z=mem z at hframe
  have hend := reported_entry_end 0 L e m he
  simp only [Nat.zero_add] at hend
  have hblock : ∀ i<L,final (heap+e*L+i)=mem (source+e*L+i) := by
    intro i hi
    simpa only [Nat.add_assoc] using hcopied (e*L+i) (by omega)
  refine ⟨?_,?_⟩
  · intro i hi
    rw [hblock i hi]
    exact hvalid i hi
  · have hvalue : Num.fixVal final (heap+e*L) h L P=Num.fixVal mem (source+e*L) h L P := by
      unfold Num.fixVal
      rw [Num.intVal_congr hblock]
    exact hvalue.trans (Num.IPM.fixVal_frozen hframe (by omega : source+e*L+L≤heap)).symm

/-- Copying the base preserves strict capacity slacks in the new mutable
cache when both capacity blocks precede the fresh allocation. -/
theorem epochFlowCopy_inside {w source m L heap v h P e lo up : ℕ} {mem final : ℕ → ℕ}
    (hout : (epochFlowCopyContract w).post [source,m,L,heap] mem v final)
    (hsource : source+m*L≤heap) (he : e<m)
    (hvalid : Num.Valid mem (source+e*L) h L)
    (hlo : lo+e*L+L≤heap) (hup : up+e*L+L≤heap)
    (hinside : Num.fixVal mem (lo+e*L) h L P<Num.fixVal mem (source+e*L) h L P ∧
      Num.fixVal mem (source+e*L) h L P<Num.fixVal mem (up+e*L) h L P) :
    Num.fixVal final (lo+e*L) h L P<Num.fixVal final (heap+e*L) h L P ∧
      Num.fixVal final (heap+e*L) h L P<Num.fixVal final (up+e*L) h L P := by
  have hcopy := (epochFlowCopy_coordinate (P:=P) hout hsource he hvalid).2
  have hframe := hout.1.2.2.1
  change ∀ z<heap,final z=mem z at hframe
  have hsourceEnd := (reported_entry_end source L e m he).trans hsource
  rw [hcopy,Num.IPM.fixVal_frozen hframe hlo,Num.IPM.fixVal_frozen hframe hup,
    Num.IPM.fixVal_frozen hframe hsourceEnd]
  exact hinside

end MinCostFlow.IPM.Machine
