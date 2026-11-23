module

public import MinCostFlow.HierPaths.InitProgFillWord
public import MinCostFlow.LowStretch.ProgChildIota

/-!
# Labels of the root host edges

The original port edges receive their one-based input edge numbers.
Cloud and padding edges receive zero.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.LowStretch

def buildTopLabelWords (original total : ℕ) : List ℕ :=
  (List.range original).map (· + 1) ++ List.replicate (total - original) 0

def buildTopLabels (iota fill : ℕ) : Stmt :=
  .call 3 iota [.reg 0, .reg 2, .const 1, .const 1] ;;
  .call 4 fill [.bin .add (.reg 2) (.reg 0), .bin .sub (.reg 1) (.reg 0), .const 0] ;;
  .ret (.reg 4)

theorem buildTopLabels_noRand (iota fill : ℕ) : (buildTopLabels iota fill).NoRand := by
  simp [buildTopLabels, Stmt.NoRand]

/-- Arguments are the number of original edges, the total number of edges, and the destination. -/
def buildTopLabelsContract (w : ℕ) : Contract where
  pre args _ := ∃ m n dst, args = [m, n, dst] ∧ m ≤ n ∧ dst + n + 1 < 2 ^ w
  post args mem r mem' := ∃ m n dst, args = [m, n, dst] ∧ r = dst + n ∧
    ListAt mem' dst (buildTopLabelWords m n) ∧ ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost args _ := 40 * args.getD 1 0 + 75

theorem buildTopLabels_meetsContract {w f iota fill : ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopLabels iota fill))
    (hi : p.HasAt iota [iotaP]) (hf : p.procs[fill]? = some initFillWord) :
    MeetsContract w p f (buildTopLabelsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨m, n, dst, rfl, hmn, hroom⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have hm : m < 2 ^ w := by omega
  have hd : dst < 2 ^ w := by omega
  have hdm : dst + m < 2 ^ w := by omega
  have hnm : n - m < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopLabels
  refine runs_seq_call_le (iotaP_spec hi) (vs := [m, dst, 1, 1]) ?_ ?_
    ⟨m, dst, 1, 1, rfl, by omega, by omega⟩ ?_
  · simp [evalArgs, Expr.eval, startState, h1]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  intro _ mem₁ pos₁ hpost
  obtain ⟨hdata, hframe⟩ := hpost m dst 1 1 rfl
  refine runs_seq_call_le (initFillWord_meetsContract hf) (vs := [dst + m, n - m, 0])
    ?_ ?_ ⟨dst + m, n - m, 0, rfl, by omega, h1⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, hdm, hnm]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  intro r mem₂ pos₂ hpost
  obtain ⟨a', n', w', ha, hr, hz, hf₂⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨ha, hb, hc⟩ := ha
  subst a' n' w'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨m, n, dst, rfl, by change r = dst + n; omega, ?_, ?_⟩ ?_
  · unfold buildTopLabelWords
    refine listAt_append.mpr ⟨?_, by simpa using hz⟩
    intro i hi
    have hm' : i < m := by simpa using hi
    rw [List.getElem_map, List.getElem_range]
    exact (hf₂ _ (.inl (by omega))).trans (by simpa using hdata i hm')
  · intro y hy
    change y < dst ∨ r ≤ y at hy
    rcases hy with hy | hy
    · exact (hf₂ _ (.inl (by omega))).trans (hframe _ (.inl hy))
    · exact (hf₂ _ (.inr (by omega))).trans (hframe _ (.inr (by omega)))
  · simp [buildTopLabelsContract, initFillWordContract, iotaC, Expr.size, argsSize]
    omega

end MinCostFlow.HierPaths

end
