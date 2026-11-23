module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryRecord
import MinCostFlow.Num.ModulePlacement
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Writing a hub edge for a zero deficit

The connected version of Lemma 4.12 (page 31 of Chen et al.,
arXiv:2203.00671v2) adds both directions at zero-deficit vertices.
One pass writes the outgoing direction and a second pass writes the
incoming direction. The record format is the same in both passes.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A pass supplies the endpoints in its chosen order. -/
def connectedPairRecordWords (tail head incoming outgoing penalty : ℕ) : List ℕ :=
  if incoming = outgoing then [tail, head, 2, 0, penalty] else []

/-- Arguments `[tail,head,incoming,outgoing,penalty,heap]`. -/
def connectedPairRecordBody (write : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.reg 3))
    (.call 6 write [.reg 0,.reg 1,.const 2,.reg 4,.reg 5] ;; .ret (.reg 6))
    (.ret (.reg 5))

/-- The selector and the shared five-word record writer. -/
def connectedPairRecordModule (b : ℕ) : List Stmt :=
  [connectedPairRecordBody (b+1)] ++ initialAuxiliaryRecordModule

/-- Emit one record exactly when the deficit is zero. -/
def connectedPairRecordContract (w : ℕ) : Contract :=
  let rows := fun (args : List ℕ) => connectedPairRecordWords
    (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0)
  let C := heapContract w
    (fun args _ => ∃ u v inc out penalty heap, args = [u,v,inc,out,penalty,heap])
    (fun args _ mem' => ListAt mem' (heapArg args) (rows args))
    (fun _ _ => 100) (fun _ _ => 5)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      v = heapArg args+(rows args).length }

/-- The pair selector and writer are deterministic. -/
theorem connectedPairRecordModule_noRand (b : ℕ) :
    ∀ body ∈ connectedPairRecordModule b, body.NoRand := by
  intro body hb
  simp only [connectedPairRecordModule, initialAuxiliaryRecordModule, List.singleton_append,
    List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp [connectedPairRecordBody, Stmt.NoRand]
  · exact initialAuxiliaryRecordBody_noRand

/-- The zero-deficit selector meets the exact record contract. -/
theorem connectedPairRecord_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (connectedPairRecordModule b)) :
    MeetsContract w p b (connectedPairRecordContract w) := by
  have hwriter : p.HasAt (b+1) initialAuxiliaryRecordModule := Num.hasAt_append_right hp
  have hk := initialAuxiliaryRecord_meetsContract hw hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨u,v,inc,out,penalty,heap,rfl⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+5 < 2^w at hspace
  have hu : u < 2^w := hwords _ (by simp)
  have hv : v < 2^w := hwords _ (by simp)
  have hi : inc < 2^w := hwords _ (by simp)
  have ho : out < 2^w := hwords _ (by simp)
  have hkword : penalty < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  have htwo : 2 < 2^w := by omega
  apply runs_start_le
  unfold connectedPairRecordBody
  wram_step
  · have heq : inc = out := by simpa [startState] using hcond
    refine runs_seq_call_le hk (vs := [u,v,2,penalty,heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,_,rfl⟩,hzero,hspace⟩
    · intro value mem' pos' hpost
      have hval : value = heap+5 := hpost.2
      have hfit : value < 2^w := by omega
      refine runs_ret_le (v := value) (by eval_expr) ?_ ?_
      · simpa [connectedPairRecordContract, initialAuxiliaryRecordContract, heapContract,
          connectedPairRecordWords, heq, heapArg, Outcome.value, startState] using hpost
      · simp only [connectedPairRecordContract,initialAuxiliaryRecordContract,heapContract,
          Expr.size_bin,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hne : inc ≠ out := by simpa [startState] using hcond
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · change (heap ≤ heap ∧ heap ≤ heap+5 ∧ (∀ x < heap, mem x = mem x) ∧
        ZeroFrom mem heap ∧ ListAt mem heap (connectedPairRecordWords u v inc out penalty)) ∧
        heap = heap+(connectedPairRecordWords u v inc out penalty).length
      simp [connectedPairRecordWords,hne,hzero,ListAt]
    · simp only [connectedPairRecordContract,heapContract,Expr.size_bin,Expr.size_reg]
      omega

end MinCostFlow.IPM.Machine
