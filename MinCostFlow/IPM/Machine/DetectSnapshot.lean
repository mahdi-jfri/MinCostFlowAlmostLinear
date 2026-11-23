module

public import MinCostFlow.IPM.Machine.Layout
public import WordRAM.CopyWords
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Keeping Detect's reported order outside the DS footprint

Definition 4.5 (page 14) returns a set of reported edges. Its concrete
answer may share allocated storage with the DS representation. Before
Query calls, copy the header and names to fresh caller memory, retaining
the returned order. Later DS calls can then preserve this list by their
memory frame. Copying adds linear work in the Detect output size.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[detectAnswer,heap]`. Copy the count and all reported names
with the library word-copy procedure, and return the fresh endpoint. -/
def detectSnapshotBody (copy : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .call 3 copy [.reg 0,.reg 1,.bin .add (.reg 2) (.const 1)] ;;
  .ret (.bin .add (.reg 1) (.bin .add (.const 1) (.reg 2)))

/-- Snapshot exactly the actual Detect answer, including its order. The
source answer ends before the incoming heap. -/
def detectSnapshotContract (w : ℕ) (S : Finset ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ report heap,args=[report,heap] ∧
      DetectAt mem report S ∧ report+1+S.card≤heap ∧ 1<2^w)
    (fun args mem mem' => DetectAt mem' (heapArg args) S ∧
      ∀ i<1+S.card,mem' (heapArg args+i)=mem (args.getD 0 0+i))
    (fun _ _ => 17*S.card+100) (fun _ _ => 1+S.card)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+(1+S.card)}

/-- The snapshot entry contains no randomness. -/
theorem detectSnapshotBody_noRand (copy : ℕ) : (detectSnapshotBody copy).NoRand := by
  simp [detectSnapshotBody,Stmt.NoRand]

/-- The actual library copy gives the snapshot with a linear operation
bound, preserving all old memory and the fresh zero suffix. -/
theorem detectSnapshot_meetsContract {w copy entry : ℕ} {p : Program}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hp : p.procs[entry]?=some (detectSnapshotBody copy)) (S : Finset ℕ) :
    MeetsContract w p entry (detectSnapshotContract w S) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨⟨report,heap,rfl,hdetect,hend,hw⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(1+S.card)<2^w at hspace
  have hcount := hdetect.count
  have hr : report<2^w := hwords _ (by simp)
  have hh : heap<2^w := hwords _ (by simp)
  have hc : S.card<2^w := by omega
  have hcw : S.card+1<2^w := by omega
  apply runs_start_le
  unfold detectSnapshotBody
  wram_step
  refine runs_seq_call_le hcopy (vs:=[report,heap,S.card+1]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨report,heap,S.card+1,rfl,hw,by omega,by omega,Or.inr (by omega)⟩
  · intro v mem' pos' hout
    obtain ⟨src,dst,len,heq,_,hcopied,hframe⟩ := hout
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    change ∀ i<S.card+1,mem' (heap+i)=mem (report+i) at hcopied
    change ∀ z,z<heap ∨ heap+(S.card+1)≤z → mem' z=mem z at hframe
    obtain ⟨es,hnd,hset,hheader,hnames⟩ := hdetect
    have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
    refine runs_ret_le (v:=heap+(1+S.card)) (by eval_expr) ?_ ?_
    · change (heap≤heap+(1+S.card) ∧ heap+(1+S.card)≤heap+(1+S.card) ∧
        (∀ z<heap,mem' z=mem z) ∧ ZeroFrom mem' (heap+(1+S.card)) ∧
        (DetectAt mem' heap S ∧ ∀ i<1+S.card,mem' (heap+i)=mem (report+i))) ∧ _
      refine ⟨⟨by omega,le_rfl,?_,?_,?_,?_⟩,rfl⟩
      · intro z hz0
        exact hframe z (Or.inl hz0)
      · intro z hz0
        rw [hframe z (Or.inr (by omega))]
        exact hz z (by omega)
      · refine ⟨es,hnd,hset,?_,?_⟩
        · simpa only [Nat.add_zero] using (hcopied 0 (by omega)).trans hheader
        · intro i hi
          have he := hcopied (1+i) (by omega)
          simp only [← Nat.add_assoc] at he
          exact he.trans (hnames i hi)
      · intro i hi
        exact hcopied i (by omega)
    · simp only [detectSnapshotContract,heapContract,copyWordsContract,
        Expr.size_reg,Expr.size_bin,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
      omega

end MinCostFlow.IPM.Machine
