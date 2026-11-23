module

public import MinCostFlow.HierPaths.BuildTopModel

/-!
# Calling the level procedure on a parent

The sorted terminals of each parent are a slice of the global terminal
table. The call computes the start of that slice in constant time and
passes it to the level procedure.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

theorem buildTopLevelWords_eq (start s k : ℕ) :
    finsetWords (buildLevelVerts start s k) = List.range' start (s * k) := by
  have hSet : (List.range' start (s * k)).toFinset = buildLevelVerts start s k := by
    ext i
    simp [Nat.mul_comm s k, buildLevelVerts, List.mem_range']
    constructor
    · rintro ⟨t, ht, rfl⟩
      omega
    · intro hi
      exact ⟨i - start, by omega, by omega⟩
  rw [← hSet, finsetWords]
  exact (List.toFinset_sort (· ≤ ·) (List.nodup_range' 1)).mpr (List.pairwise_le_range' 1)

/-- Invoke the level program with a slice of the shared terminal table. -/
def buildTopParentCall (level : ℕ) : Stmt :=
  .call 12 level [.reg 0, .bin .add (.reg 1) (.reg 2), .reg 2, .reg 3, .reg 4,
    .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11] ;;
  .ret (.reg 12)

theorem buildTopParentCall_noRand (level : ℕ) : (buildTopParentCall level).NoRand := by
  simp [buildTopParentCall, Stmt.NoRand]

/-- The parent call uses the same level contract with a derived terminal-list address. -/
def buildTopParentCallContract (w K : ℕ)
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (G : Graph) (start s k M r Δ L L' bh : ℕ) : Contract where
  pre args mem := ∃ ga base h,
    args = buildLevelArgs ga base start s k M r Δ L L' bh h ∧
    base + start < 2 ^ w ∧
    (buildLevelContract w K space G start s k M r Δ L L' bh).pre
      (buildLevelArgs ga (base + start) start s k M r Δ L L' bh h) mem
  post args mem v mem' := ∃ ga base h,
    args = buildLevelArgs ga base start s k M r Δ L L' bh h ∧
    (buildLevelContract w K space G start s k M r Δ L L' bh).post
      (buildLevelArgs ga (base + start) start s k M r Δ L L' bh h) mem v mem'
  cost _ _ := buildLevelCost K G s k M r Δ L L' bh + 24

theorem buildTopParentCall_meetsContract {w K f level : ℕ} {p : Program}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {start s k M r Δ L L' bh : ℕ}
    (hp : p.procs[f]? = some (buildTopParentCall level))
    (hl : ProvidesBuildLevel w K space p level) :
    MeetsContract w p f (buildTopParentCallContract w K space G start s k M r Δ L L' bh) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, base, h, rfl, ha, hpre⟩ := hpre
  refine runs_start_le ?_
  unfold buildTopParentCall
  refine runs_seq_call_le (hl G start s k M r Δ L L' bh)
    (vs := buildLevelArgs ga (base + start) start s k M r Δ L L' bh h) ?_ ?_ hpre ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, buildLevelArgs, ha]
  · intro v hv
    simp only [buildLevelArgs, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | rfl | hv
    · exact hw v (by simp [buildLevelArgs, hv])
    · exact ha
    · apply hw v
      simp only [buildLevelArgs, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr hv)
  intro n mem' pos' hpost
  refine runs_ret_le (v := n) (Expr.eval_reg_of_eq rfl) ⟨ga, base, h, rfl, hpost⟩ ?_
  simp [buildTopParentCallContract, buildLevelContract, heapContract, Expr.size, argsSize]
  omega

end MinCostFlow.HierPaths

end
