module

public import MinCostFlow.LowStretch.ProgResetG
public import MinCostFlow.LowStretch.ProgChildIota

/-!
# The reset of child `k`: the index list of the new nodes

After the split walk returns the number `v` of split nodes, `rsB` has `cnt = sN + v` new nodes in
column `1` of the work array at `A`. It puts `cnt` in register `39`, the address `IDX = A + 3 cnt`
in register `40`, writes the index list `3 i + 1` for `i < cnt` there (`iotaP`), so that `ncP`
reads column `1`, and puts `IDX + cnt` in register `42` (`rsIota_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- **The index list of the new nodes.** -/
theorem rsIota_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {V : RsV} {st : State}
    (fio : MeetsContract w p I.io (iotaC w)) (hR : V.Regs st) {v : ℕ} (h38 : st.regs 38 = v)
    (hroom : V.A + 4 * (V.sN + v) + 1 < 2 ^ w) (hw3 : 3 < 2 ^ w) {s : Stmt}
    {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ st' : State, (∀ r < 39, st'.regs r = st.regs r) → st'.regs 38 = v →
      st'.regs 39 = V.sN + v → st'.regs 40 = V.A + 3 * (V.sN + v) →
      st'.regs 42 = V.A + 3 * (V.sN + v) + (V.sN + v) →
      (∀ i < V.sN + v, st'.mem (V.A + 3 * (V.sN + v) + i) = 3 * i + 1) →
      (∀ a, (a < V.A + 3 * (V.sN + v) ∨ V.A + 3 * (V.sN + v) + (V.sN + v) ≤ a) →
        st'.mem a = st.mem a) →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ k + 60 + 30 * (V.sN + v + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.seq (.assign 39 (addR 9 38))
      (.seq (.assign 40 (.bin .add (.reg 2) (mulC 3 39)))
      (.seq (.call 41 I.io (rgs [39, 40, 30, 31]))
      (.seq (.assign 42 (addR 40 39)) s))))
      st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have h2 : st.regs 2 = V.A := hR 2 (by norm_num)
  have h9 : st.regs 9 = V.sN := hR 9 (by norm_num)
  have h30 : st.regs 30 = 3 := hR 30 (by norm_num)
  have h31 : st.regs 31 = 1 := hR 31 (by norm_num)
  set cnt := V.sN + v with hcnt
  set IDX := V.A + 3 * cnt with hIDX
  refine runs_seq_assign_le (v := cnt) (by unfold addR; eval_expr) ?_
  refine runs_seq_assign_le (v := IDX) (by unfold mulC; eval_expr) ?_
  refine runs_seq_callR_le (vs := [cnt, IDX, 3, 1]) fio (by simp [h30, h31]) (by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega) ⟨cnt, IDX, 3, 1, rfl, by omega, by omega⟩ ?_
  intro u M' pos' hpost
  obtain ⟨hio, hfr⟩ := hpost cnt IDX 3 1 rfl
  refine runs_seq_assign_le (v := IDX + cnt) (by unfold addR; eval_expr) ?_
  refine runs_exists_mono (hrest _ (fun r hr => by
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
    (by simp [h38]) (by simp) (by simp) (by simp) (fun i hi => by simpa using hio i hi)
    (fun a ha => hfr a ha)) ?_
  simp only [Expr.size, addR, mulC, List.length_cons, List.length_nil, iotaC,
    List.getD_cons_zero]
  omega

end MinCostFlow.LowStretch
