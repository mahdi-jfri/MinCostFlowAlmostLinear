module

public import MinCostFlow.HierPaths.InitProgAppend
public import MinCostFlow.HierPaths.InitStore
public import MinCostFlow.HierPaths.PortsHost

/-!
# Appending the padding edges of the root host

Each new terminal is joined to the old port with the same offset.
The loop appends the two endpoint words for each edge.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The endpoint words for a single padding edge. -/
def buildTopPadWords (ports i : ℕ) : List ℕ := [ports + i, i]

/-- Arguments are the old port count, padding count and output address. -/
def buildTopPadProc : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.assign 4 (.bin .add (.reg 0) (.reg 3)) ;;
     .assign 6 (.reg 2) ;;
     storeSeq [4, 3] 0 (.assign 2 (.bin .add (.reg 6) (.const 2)))) ;;
  .ret (.reg 2)

theorem buildTopPadProc_noRand : buildTopPadProc.NoRand := by
  simp [buildTopPadProc, storeSeq, forRange, forUp, Stmt.NoRand]

theorem buildTopPadWords_eq (ports count : ℕ) :
    initAppendPrefix (buildTopPadWords ports) count =
      (attEdges ports count id).flatMap (fun e => [e.1, e.2]) := by
  simp [initAppendPrefix, attEdges, List.flatMap_map]
  rfl

private theorem padPrefix_length (ports count : ℕ) :
    (initAppendPrefix (buildTopPadWords ports) count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [initAppendPrefix_succ, List.length_append, ih]
    rfl

/-- The procedure writes only the appended edges and takes linear time in their number. -/
def buildTopPadContract (w : ℕ) : Contract where
  pre args _ := ∃ ports count dst, args = [ports, count, dst] ∧
    ports + count < 2 ^ w ∧ dst + 2 * count < 2 ^ w ∧ 2 < 2 ^ w
  post args mem r mem' := ∃ ports count dst, args = [ports, count, dst] ∧
    r = dst + 2 * count ∧ ListAt mem' dst (initAppendPrefix (buildTopPadWords ports) count) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost args _ := 40 * args.getD 1 0 + 10

theorem buildTopPadProc_meetsContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some buildTopPadProc) :
    MeetsContract w p f (buildTopPadContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω words pre => ?_
  obtain ⟨ports, count, dst, rfl, hports, hdst, h2⟩ := pre
  let R := fun (s : State) => s.regs 0 = ports ∧ s.regs 1 = count
  have h1 : 1 < 2 ^ w := by omega
  have hloop := initAppendLoop_triple (w := w) (p := p) (dstReg := 2) (idxReg := 3)
    (hi := .reg 1) (body :=
      .assign 4 (.bin .add (.reg 0) (.reg 3)) ;; .assign 6 (.reg 2) ;;
      storeSeq [4, 3] 0 (.assign 2 (.bin .add (.reg 6) (.const 2))))
    R (buildTopPadWords ports) (fun _ => 26) count dst mem (by decide)
    h1 (words _ (by simp)) (fun _ _ hs => by simpa [R] using hs)
    (fun _ hs => Expr.eval_reg_of_eq hs.2) ?_
  · refine runs_start_le ?_
    unfold buildTopPadProc
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl⟩, rfl, rfl⟩ ?_
    intro s ⟨_, hptr, hs, hf⟩
    rw [padPrefix_length] at hptr
    refine runs_ret_le (v := s.regs 2) (Expr.eval_reg_of_eq rfl)
      ⟨ports, count, dst, rfl, hptr, hs, fun y hy => hf y (by
        rw [padPrefix_length, ← hptr]; exact hy)⟩ ?_
    simp [buildTopPadContract, rangeCost_const, Expr.size]
    omega
  intro i hi s ⟨r0, r1⟩ hidx hout _ st ω' hst
  subst st
  let out := dst + 2 * i
  have hout' : s.regs 2 = out := by simpa [out, padPrefix_length] using hout
  have hb : out + 2 < 2 ^ w := by dsimp [out]; omega
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := ports + i)
    (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq hidx) (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := out) (by simpa using hout')) ?_
  refine runs_storeSeq [4, 3] 0 _ _ _ rfl (by simpa using hb) ?_
  intro mem' hmem hfr
  refine runs_assign_le (v := out + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (r := 6) (v := out)
      (st := {s with regs := Function.update (Function.update s.regs 4 (ports + i)) 6 out, mem := mem'})
      (by exact Function.update_self 6 out (Function.update s.regs 4 (ports + i)))) (Expr.eval_const h2) hb) ?_ ?_
  · refine ⟨⟨by simpa using r0, by simpa using r1⟩, by simpa using hidx, ?_, ?_, ?_⟩
    · simp [out, padPrefix_length]; omega
    · rw [padPrefix_length]
      change ListAt mem' out [ports + i, i]
      intro j hj
      have h := hmem j (by simpa using hj)
      rcases j with _ | _ | j
      · simpa using h
      · simpa [hidx] using h
      · simp at hj
    · intro y hy
      apply hfr
      simpa [padPrefix_length, out, Nat.mul_add, Nat.add_assoc] using hy
  · simp [Expr.size]

end MinCostFlow.HierPaths

end
