module

public import MinCostFlow.HierPaths.Layout
public import MinCostFlow.HierPaths.ModelPick
public import MinCostFlow.HierPaths.QueryProgRoute
public import MinCostFlow.HierPaths.QueryProgGroupSize

/-!
# The connector choice read from the block

`GetPath` asks, for two groups `Y` and `Z` at depth `j + 1`, which connector joins them
(`pickContract`, `HierPaths/QueryProgRoute.lean`). The model answers with `StaticArrays.pick`:
the entry under the cursor of the pair array `pairIdx j Y Z`. The block does not store
`pairIdx j Y Z` for all `Y` and `Z`, only for siblings: section 12 holds, at depth `j`, the
entry `Y * br + z` for the child at position `z` of the parent of `Y` (`pairIdxTable`).

So a program reading the block computes a slightly different function, `tablePick`, defined for
all `j`, `Y` and `Z`: it looks up the entry `Y * br + Z % br`, and returns `0` when a read falls
outside a table. It checks `Y < numGroups x b (j + 1)` before it forms `Y * br`, as a program
must, since the product may not fit in a word otherwise. This file shows that `tablePick` agrees with the model's choice on the pairs
that `GetPath` asks about: siblings `Y ≠ Z` among the groups at depth `j + 1`, with `j` below the
leaf depth (`tablePick_eq_pick`).

The program `pickProc` computes `tablePick` from the block. It reads the leaf depth and the
number of pairs from the header, the group sizes computed from the header, the pair index from
section 12, the cursor from section 21 and the connector from section 8. It writes nothing. Its
contract is `pickBlockContract`, the form of `pickContract` that `routeProc` uses.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

namespace HierConcrete

variable (x : HierConcrete)

/-- The connector that the tables of the block give for the groups `Y` and `Z` at depth
`j + 1`: the pair index at entry `Y * br + Z % br` of the table at depth `j`, then the entry
under the cursor of that pair array. -/
def tablePick (j Y Z : ℕ) : ℕ :=
  if j < x.depth ∧ Y < numGroups x.H.A.x x.H.A.b (j + 1) ∧
      (x.pairIdxTable j).getD (Y * branching x.H.A.x x.H.A.b j +
        Z % branching x.H.A.x x.H.A.b j) 0 < x.H.A.numPairs then
    (x.H.A.pairConns ((x.pairIdxTable j).getD (Y * branching x.H.A.x x.H.A.b j +
        Z % branching x.H.A.x x.H.A.b j) 0)).getD
      (x.ms.st.pairCur ((x.pairIdxTable j).getD (Y * branching x.H.A.x x.H.A.b j +
        Z % branching x.H.A.x x.H.A.b j) 0)) 0
  else 0

end HierConcrete

open WordRAM

/-- The start of section `i` of the block at register `0`. -/
def secExpr (i : ℕ) : Expr :=
  .bin .add (.bin .add (.reg 0) (.const 25)) (.load (.bin .add (.reg 0) (.const i)))

/-- The connector choice read from the block. Registers: `0` the block `b`, `1` the depth `j`,
`2` and `3` the vertices `u` and `v`. Every check that fails returns `0`, as `tablePick` does. -/
def pickProc : Stmt :=
  -- `4`: the leaf depth (header word 7); check `j < depth`.
  .assign 4 (.load (.bin .add (secExpr 0) (.const 7))) ;;
  .cond (.bin .lt (.reg 1) (.reg 4)) .nop (.ret (.const 0)) ;;
  -- `6`: the group size at depth `j + 1`; `7`: the branching `br`; `8`, `9`: the groups `Y`, `Z`.
  .assign 5 (secExpr 0) ;;
  .assign 19 (.load (.bin .add (.reg 5) (.const 5))) ;;
  .assign 20 (.load (.bin .add (.reg 5) (.const 6))) ;;
  .assign 20 (queryBranchExpr (.reg 19) (.reg 20)) ;;
  .assign 6 (queryGroupSizeExpr (.reg 19) (.reg 20) (.bin .add (.reg 1) (.const 1))) ;;
  .assign 22 (queryGroupSizeExpr (.reg 19) (.reg 20) (.reg 1)) ;;
  .assign 7 (.bin .div (.reg 22) (.reg 6)) ;;
  .assign 8 (.bin .div (.reg 2) (.reg 6)) ;;
  .assign 9 (.bin .div (.reg 3) (.reg 6)) ;;
  -- `11`, `12`: the start and end of the table at depth `j` in section 12; check
  -- `Y < numGroups x b (j + 1)`, which is the table length divided by `br`.
  .assign 10 (secExpr 12) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.reg 1))) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.bin .add (.reg 1) (.const 1)))) ;;
  .cond (.bin .lt (.reg 8) (.bin .div (.bin .sub (.reg 12) (.reg 11)) (.reg 7))) .nop
    (.ret (.const 0)) ;;
  -- `13`: the pair index at entry `Y * br + Z % br`; check it against the number of pairs.
  .assign 13 (.load (.bin .add
    (.bin .add (.bin .add (.reg 10) (.bin .add (.reg 4) (.const 1))) (.reg 11))
    (.bin .add (.bin .mul (.reg 8) (.reg 7)) (.bin .mod (.reg 9) (.reg 7))))) ;;
  .assign 14 (.load (.bin .add (secExpr 0) (.const 4))) ;;
  .cond (.bin .lt (.reg 13) (.reg 14)) .nop (.ret (.const 0)) ;;
  -- `15`: the cursor; `17`, `18`: the start and end of the pair array in section 8.
  .assign 15 (.load (.bin .add (secExpr 21) (.reg 13))) ;;
  .assign 16 (secExpr 8) ;;
  .assign 17 (.load (.bin .add (.reg 16) (.reg 13))) ;;
  .assign 18 (.load (.bin .add (.reg 16) (.bin .add (.reg 13) (.const 1)))) ;;
  .cond (.bin .lt (.reg 15) (.bin .sub (.reg 18) (.reg 17))) .nop (.ret (.const 0)) ;;
  .ret (.load (.bin .add
    (.bin .add (.bin .add (.reg 16) (.bin .add (.reg 14) (.const 1))) (.reg 17)) (.reg 15)))

/-- The contract of `pickProc` for the block `x` at `b`: the form of `pickContract` that
`routeProc` uses, with `tablePick` as the choice. The context is the block in memory. -/
def pickBlockContract (x : HierConcrete) (b : ℕ) : Contract :=
  pickContract x.H.A.x x.H.A.b x.tablePick b (fun mem => ListAt mem b x.encode) 400

namespace HierConcrete

end HierConcrete

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

public section

namespace HierConcrete

variable {x : HierConcrete}

/-- The pair index table gives `pairIdx j Y Z` at entry `Y * br + Z % br` when `Y` and `Z` have
the same parent and `Y` is among the groups at depth `j + 1`. -/
theorem pairIdxTable_getD {j Y Z : ℕ}
    (hpar : parentGroup x.H.A.x x.H.A.b j Y = parentGroup x.H.A.x x.H.A.b j Z)
    (hY : Y < numGroups x.H.A.x x.H.A.b (j + 1)) :
    (x.pairIdxTable j).getD (Y * branching x.H.A.x x.H.A.b j +
      Z % branching x.H.A.x x.H.A.b j) 0 = x.H.pairIdx j Y Z := by
  have hbr : 0 < branching x.H.A.x x.H.A.b j := branching_pos
  have hmod : Z % branching x.H.A.x x.H.A.b j < branching x.H.A.x x.H.A.b j := Nat.mod_lt _ hbr
  have hi : Y * branching x.H.A.x x.H.A.b j + Z % branching x.H.A.x x.H.A.b j <
      numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j := by
    have : (Y + 1) * branching x.H.A.x x.H.A.b j ≤
        numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j :=
      Nat.mul_le_mul_right _ hY
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  -- Dividing the entry by `br` gives `Y`, and its remainder is `Z % br`.
  have hdiv : (Y * branching x.H.A.x x.H.A.b j + Z % branching x.H.A.x x.H.A.b j) /
      branching x.H.A.x x.H.A.b j = Y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbr, Nat.div_eq_of_lt hmod, Nat.zero_add]
  have hrem : (Y * branching x.H.A.x x.H.A.b j + Z % branching x.H.A.x x.H.A.b j) %
      branching x.H.A.x x.H.A.b j = Z % branching x.H.A.x x.H.A.b j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
  -- The parent of `Y` is that of `Z`, so the child at position `Z % br` is `Z`.
  have hZ : Y / branching x.H.A.x x.H.A.b j * branching x.H.A.x x.H.A.b j +
      Z % branching x.H.A.x x.H.A.b j = Z := by
    have : Y / branching x.H.A.x x.H.A.b j = Z / branching x.H.A.x x.H.A.b j := hpar
    rw [this, Nat.mul_comm]
    exact Nat.div_add_mod Z _
  simp only [pairIdxTable, tabList]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  rw [hdiv, hrem, hZ]

/-- The choice read from the block is the model's choice, for siblings `Y ≠ Z` among the groups
at depth `j + 1` with `j` below the leaf depth. -/
theorem tablePick_eq_pick {j Y Z : ℕ} (hj : j < x.depth)
    (hpar : parentGroup x.H.A.x x.H.A.b j Y = parentGroup x.H.A.x x.H.A.b j Z) (hne : Y ≠ Z)
    (hY : Y < numGroups x.H.A.x x.H.A.b (j + 1)) (hZ : Z < numGroups x.H.A.x x.H.A.b (j + 1))
    (hP : x.H.A.PairSpec x.H.pairIdx) :
    x.tablePick j Y Z = x.H.A.pick x.H.pairIdx x.ms.st j Y Z := by
  have hlt := hP.lt j Y Z hpar hne hY hZ
  unfold tablePick
  rw [pairIdxTable_getD hpar hY, ite_eq_left ⟨hj, hY, hlt⟩]
  rfl

end HierConcrete

end

end MinCostFlow.HierPaths

namespace MinCostFlow.HierPaths

open WordRAM

public section

/-- The words a program reads from a compressed list of lists: the start and end of list `i`,
its entries, and that it lies inside the compressed form. -/
theorem csr_reads {mem : ℕ → ℕ} {a k : ℕ} {f : ℕ → List ℕ} (h : ListAt mem a (csrList k f))
    {i : ℕ} (hi : i < k) :
    mem (a + i) = ((List.range i).map fun j => (f j).length).sum ∧
    mem (a + (i + 1)) = ((List.range i).map fun j => (f j).length).sum + (f i).length ∧
    ListAt mem (a + (k + 1) + ((List.range i).map fun j => (f j).length).sum) (f i) ∧
    a + (k + 1) + ((List.range i).map fun j => (f j).length).sum + (f i).length ≤
      a + (csrList k f).length := by
  refine ⟨csrList_offset h hi.le, ?_, listAt_csrList_get h hi, ?_⟩
  · rw [csrList_offset h (by omega : i + 1 ≤ k), sum_range_map_succ (fun j => (f j).length)]
  · have := csr_end_le k f hi
    omega

/-- Section `i` of the block, at the address a program computes from word `i`, and its end. -/
theorem block_sec {x : HierConcrete} {mem : ℕ → ℕ} {b i : ℕ} (h : ListAt mem b x.encode)
    (hi : i < 24) :
    ListAt mem (b + 25 + mem (b + i)) (x.sections.getD i []) ∧
      b + 25 + mem (b + i) + (x.sections.getD i []).length ≤ b + x.encode.length := by
  have hb : ListAt mem b (csrList 24 fun i => x.sections.getD i []) := h
  obtain ⟨h1, -, h3, h4⟩ := csr_reads hb hi
  rw [h1]
  exact ⟨h3, h4⟩



set_option maxHeartbeats 4000000 in
/-- `pickProc` meets its contract. -/
theorem pickProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some pickProc) {x : HierConcrete} {b : ℕ}
    (hw : b + x.encode.length < 2 ^ w) (hxw : 2 ^ x.H.A.x < 2 ^ w)
    (hbpos : 0 < x.H.A.b) :
    MeetsContract w p f (pickBlockContract x b) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨j, u, v, rfl, h⟩ := hpre
  have hu : u < 2 ^ w := hwords u (by simp)
  have hv : v < 2 ^ w := hwords v (by simp)
  obtain ⟨hL0, hE0⟩ := block_sec h (i := 0) (by norm_num)
  obtain ⟨hL8, hE8⟩ := block_sec h (i := 8) (by norm_num)
  obtain ⟨hL12, hE12⟩ := block_sec h (i := 12) (by norm_num)
  obtain ⟨hL21, hE21⟩ := block_sec h (i := 21) (by norm_num)
  change ListAt mem _ x.header at hL0
  change ListAt mem _ (csrList x.H.A.numPairs x.H.A.pairConns) at hL8
  change ListAt mem _ (csrList x.depth x.pairIdxTable) at hL12
  change ListAt mem _ (tabList x.H.A.numPairs x.ms.st.pairCur) at hL21
  change _ + x.header.length ≤ _ at hE0
  change _ + (csrList x.H.A.numPairs x.H.A.pairConns).length ≤ _ at hE8
  change _ + (csrList x.depth x.pairIdxTable).length ≤ _ at hE12
  change _ + (tabList x.H.A.numPairs x.ms.st.pairCur).length ≤ _ at hE21
  generalize hB0 : b + 25 + mem (b + 0) = B0 at hL0 hE0
  generalize hB8 : b + 25 + mem (b + 8) = B8 at hL8 hE8
  generalize hB12 : b + 25 + mem (b + 12) = B12 at hL12 hE12
  generalize hB21 : b + 25 + mem (b + 21) = B21 at hL21 hE21
  have hlen0 : x.header.length = 15 := rfl
  have hdep : mem (B0 + 7) = x.depth := hL0 7 (by simp [hlen0])
  have hnp : mem (B0 + 4) = x.H.A.numPairs := hL0 4 (by simp [hlen0])
  have hx : mem (B0 + 5) = x.H.A.x := hL0 5 (by simp [hlen0])
  have hb : mem (B0 + 6) = x.H.A.b := hL0 6 (by simp [hlen0])
  have hx' : mem (b + 25 + mem (b + 0) + 5) = x.H.A.x := by rw [hB0, hx]
  have hb' : mem (b + 25 + mem (b + 0) + 6) = x.H.A.b := by rw [hB0, hb]
  rw [length_tabList] at hE21
  have hdepthW : x.depth < 2 ^ w := by
    rw [length_csrList_q] at hE12
    omega
  refine runs_start_le ?_
  have hbr : 0 < branching x.H.A.x x.H.A.b j := branching_pos
  have hgpos : 0 < groupSize x.H.A.x x.H.A.b (j + 1) := groupSize_pos
  have hcur : ∀ q, q < x.H.A.numPairs → mem (B21 + q) = x.ms.st.pairCur q :=
    fun q hq => listAt_tabList hL21 hq
  unfold pickProc secExpr startState
  -- The check `j < depth`.
  wram_step
  wram_step
  on_goal 2 =>
    have hj : ¬ j < x.depth := by rw [hB0, hdep] at hcond; exact hcond
    refine runs_seq_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
    · intro j' u' v' he
      simp only [List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [pickFor, HierConcrete.tablePick]
      split_ifs with hc
      · exact absurd hc.1 hj
      · rfl
    · simp only [pickBlockContract, pickContract]; (try simp only [queryGroupSizeExpr, queryBranchExpr]); wram_cost
  have hj : j < x.depth := by rw [hB0, hdep] at hcond; exact hcond
  obtain ⟨hS0, hS1, hT12, hT12e⟩ := csr_reads hL12 hj
  have hlen12 : (x.pairIdxTable j).length =
      numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j := by
    simp [HierConcrete.pairIdxTable, tabList]
  simp only [hB0, hdep]
  wram_step
  wram_step
  wram_step
  wram_step
  have hjw : j + 1 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt hj) hdepthW
  have hmul₁ := queryDepth_mul_min_lt hbpos (Nat.succ_le_of_lt hj) hxw
  have hmul₀ := queryDepth_mul_min_lt hbpos hj.le hxw
  refine runs_seq_assign_le
    (eval_queryBranchExpr (xe := .reg 19) (be := .reg 20)
      (Expr.eval_reg_of_eq (by simpa using hx')) (Expr.eval_reg_of_eq (by simpa using hb'))
      (x.H.A.x.lt_two_pow_self.trans hxw)) ?_
  refine runs_seq_assign_le
    (eval_queryGroupSizeExpr (xe := .reg 19) (be := .reg 20)
      (je := .bin .add (.reg 1) (.const 1))
      (Expr.eval_reg_of_eq (by simpa using hx')) (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_add (a := .reg 1) (by eval_expr) (Expr.eval_const (by omega)) hjw) hxw hmul₁) ?_
  refine runs_seq_assign_le
    (eval_queryGroupSizeExpr (xe := .reg 19) (be := .reg 20) (je := .reg 1)
      (Expr.eval_reg_of_eq (by simpa using hx')) (Expr.eval_reg_of_eq (by simp))
      (by eval_expr) hxw hmul₀) ?_
  simp only [groupSize_query_min_branch]
  have hG₀ : groupSize x.H.A.x x.H.A.b j < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le ..)).trans_lt hxw
  wram_step
  have hbrdef : groupSize x.H.A.x x.H.A.b j / groupSize x.H.A.x x.H.A.b (j + 1) =
      branching x.H.A.x x.H.A.b j := rfl
  simp only [hbrdef]
  wram_step
  wram_step
  wram_step
  simp only [hB12]
  wram_step
  simp only [hS0]
  wram_step
  simp only [hS1, hlen12]
  -- The check `Y < numGroups x b (j + 1)`.
  wram_step
  on_goal 2 =>
    simp only [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hbr] at hcond
    refine runs_seq_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
    · intro j' u' v' he
      simp only [List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [pickFor, HierConcrete.tablePick, groupOf]
      exact (if_neg (fun hc => hcond hc.2.1)).symm
    · simp only [pickBlockContract, pickContract]; (try simp only [queryGroupSizeExpr, queryBranchExpr]); wram_cost
  simp only [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hbr] at hcond
  have hY := hcond
  -- The entry `Y * br + Z % br` of the table.
  have hkey : u / groupSize x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j +
      v / groupSize x.H.A.x x.H.A.b (j + 1) % branching x.H.A.x x.H.A.b j <
      numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j := by
    have h1 := Nat.mod_lt (v / groupSize x.H.A.x x.H.A.b (j + 1)) hbr
    have h2 : (u / groupSize x.H.A.x x.H.A.b (j + 1) + 1) * branching x.H.A.x x.H.A.b j ≤
        numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j :=
      Nat.mul_le_mul_right _ hY
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have hidx := hT12 _ (by rw [hlen12]; exact hkey)
  rw [hlen12] at hT12e
  have hYw : u / groupSize x.H.A.x x.H.A.b (j + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hu
  have hZw : v / groupSize x.H.A.x x.H.A.b (j + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hv
  wram_step
  wram_step
  simp only [hidx]
  rw [← List.getD_eq_getElem _ 0]
  generalize hPdef : (x.pairIdxTable j).getD
    (u / groupSize x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j +
      v / groupSize x.H.A.x x.H.A.b (j + 1) % branching x.H.A.x x.H.A.b j) 0 = P
  wram_step
  simp only [hB0, hnp]
  -- The check `P < numPairs`.
  wram_step
  on_goal 2 =>
    refine runs_seq_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
    · intro j' u' v' he
      simp only [List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [pickFor, HierConcrete.tablePick, groupOf, hPdef]
      exact (if_neg (fun hc => hcond hc.2.2)).symm
    · simp only [pickBlockContract, pickContract]; (try simp only [queryGroupSizeExpr, queryBranchExpr]); wram_cost
  have hP := hcond
  obtain ⟨hR0, hR1, hT8, hT8e⟩ := csr_reads hL8 hP
  wram_step
  wram_step
  simp only [hB21, hcur P hP]
  wram_step
  simp only [hB8]
  wram_step
  simp only [hR0]
  wram_step
  simp only [hR1]
  -- The check that the cursor is before the end of the pair array.
  wram_step
  on_goal 2 =>
    refine runs_seq_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
    · intro j' u' v' he
      simp only [List.cons.injEq, true_and, and_true] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [pickFor, HierConcrete.tablePick, groupOf, hPdef]
      rw [if_pos ⟨hj, hY, hP⟩]
      exact (List.getD_eq_default _ _ (by omega)).symm
    · simp only [pickBlockContract, pickContract]; (try simp only [queryGroupSizeExpr, queryBranchExpr]); wram_cost
  have hc : x.ms.st.pairCur P < (x.H.A.pairConns P).length := by omega
  wram_step
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_⟩ ?_
  · intro j' u' v' he
    simp only [List.cons.injEq, true_and, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [pickFor, HierConcrete.tablePick, groupOf, hPdef]
    rw [if_pos ⟨hj, hY, hP⟩, List.getD_eq_getElem _ 0 hc]
    exact hT8 _ hc
  · simp only [pickBlockContract, pickContract]; (try simp only [queryGroupSizeExpr, queryBranchExpr]); wram_cost

end

end MinCostFlow.HierPaths
