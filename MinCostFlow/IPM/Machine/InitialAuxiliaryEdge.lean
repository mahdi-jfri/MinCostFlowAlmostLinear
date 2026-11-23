module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryRecord
public import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Selecting one auxiliary edge from the midpoint deficit

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) adds an edge precisely at nonzero deficit.
For zero-demand circulation input the doubled deficit is incoming
capacity minus outgoing capacity. This procedure compares those two
unsigned words. Equal totals produce no edge. Otherwise subtraction
is performed in the nonnegative order, giving the exact integral
capacity, and the edge is oriented as in `starEdge`.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The exact solver record, or no record for a zero deficit. -/
def initialAuxiliaryWords (v n incoming outgoing penalty : ℕ) : List ℕ :=
  if incoming = outgoing then [] else
    if outgoing < incoming then [v,n,incoming-outgoing,0,penalty]
    else [n,v,outgoing-incoming,0,penalty]

/-- Arguments `[vertex,newVertex,incoming,outgoing,penalty,heap]`. -/
def initialAuxiliaryEdgeBody (write : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.reg 3)) (.ret (.reg 5))
    (.cond (.bin .lt (.reg 3) (.reg 2))
      (.call 6 write [.reg 0,.reg 1,.bin .sub (.reg 2) (.reg 3),.reg 4,.reg 5] ;;
        .ret (.reg 6))
      (.call 6 write [.reg 1,.reg 0,.bin .sub (.reg 3) (.reg 2),.reg 4,.reg 5] ;;
        .ret (.reg 6)))

/-- Selector and its verified record writer. -/
def initialAuxiliaryEdgeModule (b : ℕ) : List Stmt :=
  [initialAuxiliaryEdgeBody (b+1)] ++ initialAuxiliaryRecordModule

/-- Emit the selected edge with five words of worst-case space. A zero
input deficit returns the same heap and leaves the memory unchanged. -/
def initialAuxiliaryEdgeContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ v n inc out penalty heap, args = [v,n,inc,out,penalty,heap] ∧ v < n)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (initialAuxiliaryWords (args.getD 0 0) (args.getD 1 0)
        (args.getD 2 0) (args.getD 3 0) (args.getD 4 0)))
    (fun _ _ => 100) (fun _ _ => 5)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+
      (initialAuxiliaryWords (args.getD 0 0) (args.getD 1 0)
        (args.getD 2 0) (args.getD 3 0) (args.getD 4 0)).length }

/-- The selector and writer use no randomness. -/
theorem initialAuxiliaryEdgeModule_noRand (b : ℕ) :
    ∀ body ∈ initialAuxiliaryEdgeModule b, body.NoRand := by
  intro body hb
  simp only [initialAuxiliaryEdgeModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [initialAuxiliaryEdgeBody,Stmt.NoRand]
  · simp only [initialAuxiliaryRecordModule,List.mem_singleton] at hb
    subst body
    exact initialAuxiliaryRecordBody_noRand

/-- The machine comparison, orientation and capacity subtraction are
exact, including the zero-deficit branch. Cost is at most one hundred
operations and old memory is preserved on every branch. -/
theorem initialAuxiliaryEdge_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialAuxiliaryEdgeModule b)) :
    MeetsContract w p b (initialAuxiliaryEdgeContract w) := by
  have hwriter : p.HasAt (b+1) initialAuxiliaryRecordModule := Num.hasAt_append_right hp
  have hk := initialAuxiliaryRecord_meetsContract hw hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨vertex,n,inc,out,penalty,heap,rfl,hvertex⟩,hzero,hspace⟩ := hpre
  change heap+5 < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hv : vertex < 2^w := hwords _ (by simp)
  have hn : n < 2^w := hwords _ (by simp)
  have hi : inc < 2^w := hwords _ (by simp)
  have ho : out < 2^w := hwords _ (by simp)
  have hkword : penalty < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold initialAuxiliaryEdgeBody
  wram_step
  · have heq : inc = out := by simpa [startState] using hcond
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · change (heap ≤ heap ∧ heap ≤ heap+5 ∧ (∀ x < heap, mem x = mem x) ∧
        ZeroFrom mem heap ∧ ListAt mem heap (initialAuxiliaryWords vertex n inc out penalty)) ∧
        heap = heap+(initialAuxiliaryWords vertex n inc out penalty).length
      simp [initialAuxiliaryWords,heq,hzero,ListAt]
    · simp only [initialAuxiliaryEdgeContract,heapContract,Expr.size_bin,Expr.size_reg]
      omega
  · have hne : inc ≠ out := by simpa [startState] using hcond
    wram_step
    · have hpos : out < inc := by simpa [startState] using hcond
      have hdiff : inc-out < 2^w := (Nat.sub_le _ _).trans_lt hi
      refine runs_seq_call_le hk (vs := [vertex,n,inc-out,penalty,heap]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,rfl⟩,hzero,hspace⟩
      · intro value mem' pos' hpost
        have hvalue : value = heap+5 := hpost.2
        have hvaluew : value < 2^w := by omega
        refine runs_ret_le (v := value) (by eval_expr) ?_ ?_
        · simpa [initialAuxiliaryEdgeContract,initialAuxiliaryRecordContract,heapContract,
            initialAuxiliaryWords,hne,hpos,heapArg,Outcome.value,startState] using hpost
        · simp only [initialAuxiliaryEdgeContract,initialAuxiliaryRecordContract,heapContract,
            Expr.size_bin,Expr.size_reg,argsSize_cons,argsSize_nil]
          omega
    · have hnonpos : ¬out < inc := by simpa [startState] using hcond
      have hdiff : out-inc < 2^w := (Nat.sub_le _ _).trans_lt ho
      refine runs_seq_call_le hk (vs := [n,vertex,out-inc,penalty,heap]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_,_,_,_,_,rfl⟩,hzero,hspace⟩
      · intro value mem' pos' hpost
        have hvalue : value = heap+5 := hpost.2
        have hvaluew : value < 2^w := by omega
        refine runs_ret_le (v := value) (by eval_expr) ?_ ?_
        · simpa [initialAuxiliaryEdgeContract,initialAuxiliaryRecordContract,heapContract,
            initialAuxiliaryWords,hne,hnonpos,heapArg,Outcome.value,startState] using hpost
        · simp only [initialAuxiliaryEdgeContract,initialAuxiliaryRecordContract,heapContract,
            Expr.size_bin,Expr.size_reg,argsSize_cons,argsSize_nil]
          omega

/-- At every nonzero deficit the emitted record is exactly the existing
`starEdge` construction, including its orientation and integral capacity.
The comparison is done on unsigned input words; no sign convention is
changed when the resulting signed deficit is negative. -/
theorem initialAuxiliaryWords_starEdge (n vertex inc out penalty : ℕ)
    (hv : vertex < n) (hne : inc ≠ out) :
    let e := starEdge n ⟨vertex,hv⟩ ((inc : ℤ)-(out : ℤ)) penalty
    initialAuxiliaryWords vertex n inc out penalty = [e.tail,e.head,e.upper.toNat,0,penalty] := by
  dsimp only
  by_cases hpos : out < inc
  · have hz : 0 ≤ (inc : ℤ)-(out : ℤ) := sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hpos)
    have hcast : (inc : ℤ)-(out : ℤ) = ((inc-out : ℕ) : ℤ) :=
      (Nat.cast_sub (Nat.le_of_lt hpos)).symm
    simp [initialAuxiliaryWords,hne,hpos,starEdge,hcast]
  · have hlt : inc < out := by omega
    have hz : (inc : ℤ)-(out : ℤ) < 0 := sub_neg.mpr (by exact_mod_cast hlt)
    have hcast : -((inc : ℤ)-(out : ℤ)) = ((out-inc : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      ring
    simp only [initialAuxiliaryWords,hne,hpos,↓reduceIte,starEdge,not_le.mpr hz,
      abs_of_neg hz,hcast,Int.toNat_natCast]

end MinCostFlow.IPM.Machine
