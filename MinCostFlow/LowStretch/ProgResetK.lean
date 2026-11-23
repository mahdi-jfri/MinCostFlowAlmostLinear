module

public import MinCostFlow.LowStretch.ProgResetJ
public import MinCostFlow.LowStretch.ProgSplitGrp

/-!
# The reset of child `k`: the stored pairs and the record block

After `ncP`, the reset has `n = sN + v` nodes, at `NA = A + 4 n`. It stores the pairs at
`SA = A + 5 n` (register `43`): first the `cnt` pairs of key group `k` with flag `0` (`pcP` with
`keep = 0`, layout `rsPcE`), then the pairs grouped at the `v` split nodes, which lie in column `2`
of the work array (`grpCopyP` on `[A + 2, v, GOFF, GPR, SA, cnt]`, layout `rsGcE`). The call of
`grpCopyP` returns the number `cnt + g` of stored pairs (register `44`). Then the reset writes
seven words of the record block at `BK` (`rsBlk`) and returns `SA + 2 (cnt + g)` (`rsTail_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace RsV

variable (V : RsV)

/-- The layout of the call of `pcP` in the reset, for `n` nodes, on memory `M`. -/
def rsPcE (n : ℕ) (M : ℕ → ℕ) : PCE :=
  ⟨V.cnt, V.SRCK, V.ACT, V.IN, V.LAB, V.LOC, V.HM, V.PP, 0, V.A + 5 * n, M⟩

/-- The layout of the call of `grpCopyP` in the reset, for `v` split nodes and `n` nodes. -/
def rsGcE (v n : ℕ) (M : ℕ → ℕ) : GCE := ⟨V.A + 2, v, V.GOFF, V.GPR, V.A + 5 * n, V.cnt, M⟩

/-- The memory after the seven stores into the record block: `n` nodes, `m` stored pairs, the
logarithm `lx` of the new threshold. -/
def rsBlk (n m lx : ℕ) (M : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update M V.BK n) (V.BK + 1) m) (V.BK + 2) (V.A + 5 * n))
    (V.BK + 3) lx) (V.BK + 4) (V.A + 4 * n)) (V.BK + 6) V.cc) (V.BK + 7) 0

end RsV

/-- The number of items of `grpCopyP` is the sum of the sizes of the ranges. -/
theorem GCE.seq_length (E : GCE) :
    E.seq.length = ((List.range E.nsp).map fun i => E.hi i - E.lo i).sum := by
  simp [GCE.seq, GCE.blk, List.length_flatMap]

set_option maxHeartbeats 1000000 in
/-- **The stored pairs, the record block and the return.** -/
theorem rsTail_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {V : RsV} {st : State}
    (fpc : MeetsContract w p I.pc (pcC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    (hR : V.Regs st) {v n lx : ℕ} (h36 : st.regs 36 = lx) (h38 : st.regs 38 = v)
    (h39 : st.regs 39 = n) (hvn : v ≤ n) (h42 : st.regs 42 = V.A + 4 * n)
    (hpc : (V.rsPcE n st.mem).Ok w)
    (hgc : ∀ M, (V.rsPcE n st.mem).Done V.cnt M → (V.rsGcE v n M).Ok w)
    (hw : ∀ x ∈ V.args ++ [V.SRCK, V.ACT, V.IN, V.LAB, V.LOC, V.HM, V.PP, V.GOFF, V.GPR], x < 2 ^ w)
    (hBK : V.BK + 7 < 2 ^ w) {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ M2 M3 pos', (V.rsPcE n st.mem).Done V.cnt M2 →
      (V.rsGcE v n M2).Done M3 (V.rsGcE v n M2).seq →
      ∀ regs, Q (.returned (V.A + 5 * n + 2 * (V.cnt + (V.rsGcE v n M2).seq.length)))
        { mem := V.rsBlk n (V.cnt + (V.rsGcE v n M2).seq.length) lx M3, regs := regs,
          pos := pos' } ∧
      k + 300 + 200 * V.cnt + 60 * ((V.rsGcE v n M2).seq.length + v) ≤ T) :
    ∃ o st' c, Runs w p ω
      (.seq (.assign 43 (addR 42 39))
      (.seq (.call 41 I.pc (rgs [7, 6, 27, 26, 20, 23, 11, 28, 29, 43]))
      (.seq (.call 44 I.gc (rgs [32, 38, 24, 25, 43, 7]))
      (.seq (.store (.reg 1) (.reg 39))
      (.seq (.store (.bin .add (.reg 1) (.const 1)) (.reg 44))
      (.seq (.store (.bin .add (.reg 1) (.const 2)) (.reg 43))
      (.seq (.store (.bin .add (.reg 1) (.const 3)) (.reg 36))
      (.seq (.store (.bin .add (.reg 1) (.const 4)) (.reg 42))
      (.seq (.store (.bin .add (.reg 1) (.const 6)) (.reg 10))
      (.seq (.store (.bin .add (.reg 1) (.const 7)) (.reg 29))
        (.ret (.bin .add (.reg 43) (mulC 2 44))))))))))))) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hroom := hpc.room
  simp only [RsV.rsPcE] at hroom
  have h1 : st.regs 1 = V.BK := hR 1 (by norm_num)
  have h2 : st.regs 2 = V.A := hR 2 (by norm_num)
  have h7 : st.regs 7 = V.cnt := hR 7 (by norm_num)
  have h10 : st.regs 10 = V.cc := hR 10 (by norm_num)
  have h29 : st.regs 29 = 0 := hR 29 (by norm_num)
  have h32 : st.regs 32 = V.A + 2 := hR 32 (by norm_num)
  have h6 : st.regs 6 = V.SRCK := hR 6 (by norm_num)
  have h27 : st.regs 27 = V.ACT := hR 27 (by norm_num)
  have h26 : st.regs 26 = V.IN := hR 26 (by norm_num)
  have h20 : st.regs 20 = V.LAB := hR 20 (by norm_num)
  have h23 : st.regs 23 = V.LOC := hR 23 (by norm_num)
  have h11 : st.regs 11 = V.HM := hR 11 (by norm_num)
  have h28 : st.regs 28 = V.PP := hR 28 (by norm_num)
  have h24 : st.regs 24 = V.GOFF := hR 24 (by norm_num)
  have h25 : st.regs 25 = V.GPR := hR 25 (by norm_num)
  simp only [RsV.args, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hw
  obtain ⟨-, -, -, -, -, -, -, wcnt, -, -, -, -, -, -, wSRCK, wACT, wIN, wLAB, wLOC, wHM, wPP,
    wGOFF, wGPR⟩ := hw
  set SA := V.A + 5 * n with hSA
  refine runs_seq_assign_le (v := V.A + 4 * n + n)
    (Expr.eval_add (Expr.eval_reg_of_eq h42) (Expr.eval_reg_of_eq h39) (by omega)) ?_
  rw [show V.A + 4 * n + n = SA by omega]
  -- the stored pairs with flag `0`
  refine runs_seq_callR_le (vs := (V.rsPcE n st.mem).args) fpc (by
    simp only [List.map_cons, List.map_nil, RsV.rsPcE, PCE.args, Function.update_apply]
    simp [h7, h6, h27, h26, h20, h23, h11, h28, h29, hSA]) (by
    simp only [RsV.rsPcE, PCE.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    ⟨_, rfl, rfl, hpc⟩ ?_
  intro u2 M2 q2 hp2
  have hd2 := hp2 (V.rsPcE n st.mem) rfl rfl
  have hg := hgc M2 hd2
  have groom : V.A + 5 * n + 2 * (V.cnt + (V.rsGcE v n M2).seq.length) + 2 < 2 ^ w := hg.room
  -- the pairs grouped at the split nodes
  refine runs_seq_callR_le (vs := [V.A + 2, v, V.GOFF, V.GPR, SA, V.cnt]) fgc (by
    simp [h32, h38, h24, h25, h7]) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    ⟨V.rsGcE v n M2, rfl, rfl, hg⟩ ?_
  intro g M3 q3 hp3
  obtain ⟨hgv, hd3⟩ := hp3 (V.rsGcE v n M2) rfl rfl
  simp only [RsV.rsGcE] at hgv
  set m := V.cnt + (V.rsGcE v n M2).seq.length with hm
  -- the record block
  refine runs_seq_store_le (x := V.BK) (v := n) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 1) (v := m) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 2) (v := SA) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 3) (v := lx) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 4) (v := V.A + 4 * n) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 6) (v := V.cc) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := V.BK + 7) (v := 0) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := SA + 2 * m) (by unfold mulC; eval_expr) ?_ ?_
  · exact (hrest M2 M3 q3 hd2 hd3 _).1
  · have hc := (hrest M2 M3 q3 hd2 hd3 st.regs).2
    have hcost : (grpCopyC w).cost [V.A + 2, v, V.GOFF, V.GPR, SA, V.cnt] M2 =
        60 * ((V.rsGcE v n M2).seq.length + v) + 20 := by
      simp only [grpCopyC, List.getD_cons_zero, List.getD_cons_succ]
      rw [GCE.seq_length]
      rfl
    simp only [hcost, pcC, RsV.rsPcE, PCE.args, List.getD_cons_zero, Expr.size, addR, mulC,
      List.length_cons, List.length_nil]
    omega

end MinCostFlow.LowStretch
