module

public import MinCostFlow.LinkCut.Prog.MathForestCutPhi
public import MinCostFlow.LinkCut.Prog.MathForestCutInvs

/-!
# The `cut` program and its small pieces

`cut x y` runs in four steps. It first checks that both vertices exist. It then calls
`reroot (x + 1)` and `expose (y + 1)`, so the path from `x` to `y` is one auxiliary tree with
`y + 1` at its root. The edge `{x, y}` exists exactly when this path has two vertices and the
edge node between them has endpoints `x` and `y`. In that case `cut` splays the edge node,
detaches the two vertex nodes from it, and pushes it back on the free slot stack.

This file defines the program (`lctCutBody`), shows that it uses no random bits, and proves the
run lemmas of its straight-line pieces (`cut_mainSetup_runs`, `cut_read_runs`,
`cut_splice_runs`). It also proves `cut_edges_perm`, which says how the edge map changes.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutProgramDefs

/-- Amortized constant factor of `cut`: the bound is `C_CUT_OP L * (log (n + 2) + 1)`. -/
def C_CUT_OP (L : ℕ) : ℕ := 400000 * (L + 1)

/-- Values stored into the freed edge slot: the old free stack head (register `r`) in
`OFF_EU`, and `0` everywhere else. -/
def lctCutClearPairsExpr (r : ℕ) : List (ℕ × Expr) :=
  (List.range NODE_STRIDE).map
    (fun off => (off, if off = OFF_EU then Expr.reg r else Expr.const 0))

/-- Registers set before the calls, on `args = [b, x, y, hp]` with `n` in register `4`:
`5 = nb`, `6 = x + 1`, `7 = y + 1`, `8` the address of node `y + 1`, `15` that of `x + 1`. -/
def lctCutMainSetupBody : Stmt :=
  .assign 5 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
  .assign 6 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 7 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 8 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 7))) ;;
  .assign 15 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 6)))

/-- Reads the edge node `ed` below `y + 1` (register `9`), its address (`10`) and its two
endpoints (`11`, `12`). -/
def lctCutReadBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 8) (.const OFF_MIN1_FIRST))) ;;
  .assign 10 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 9))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.const OFF_EU))) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.const OFF_EV)))

/-- The write of `cut`: push `ed` on the free stack, detach `x + 1` and `y + 1`, and clear
`ed`. -/
def lctCutSpliceBody : Stmt :=
  .assign 14 (.load (.bin .add (.reg 0) (.const LCT_HDR_FREE))) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_FREE)) (.reg 9) ;;
  .store (.bin .add (.reg 15) (.const OFF_PARENT)) (.const 0) ;;
  .store (.bin .add (.reg 8) (.const OFF_PARENT)) (.const 0) ;;
  storeNodeOffsExprStmt (.reg 10) (lctCutClearPairsExpr 14)

/-- Nonzero exactly when the endpoints in registers `11, 12` are `{x, y}`. -/
def lctCutMatchExpr : Expr :=
  .bin .add (.bin .mul (.bin .eq (.reg 11) (.reg 1)) (.bin .eq (.reg 12) (.reg 2)))
    (.bin .mul (.bin .eq (.reg 11) (.reg 2)) (.bin .eq (.reg 12) (.reg 1)))

/-- After `expose (y + 1)` found a path of two vertices: read the edge node, and cut it if its
endpoints are `x` and `y`. -/
def lctCutEdgeBody (lp : LctProcs) : Stmt :=
  lctCutReadBody ;;
  .cond lctCutMatchExpr (.call 25 lp.splay.splay [.reg 5, .reg 9] ;; lctCutSpliceBody) .nop

/-- The part of `cut` that runs when `x < n` and `y < n`. -/
def lctCutMainBody (lp : LctProcs) : Stmt :=
  lctCutMainSetupBody ;;
  .call 25 lp.reroot [.reg 5, .reg 6] ;;
  .call 25 lp.expose [.reg 5, .reg 7] ;;
  .cond (.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT))) (.const 2))
    (lctCutEdgeBody lp) .nop

/-- Nonzero exactly when `x < n` and `y < n` (registers `1, 2, 4`). -/
def lctCutGoodExpr : Expr :=
  .bin .mul (.bin .lt (.reg 1) (.reg 4)) (.bin .lt (.reg 2) (.reg 4))

/-- Deterministic Word-RAM `cut` taking `args = [b, x, y, hp_caller]`. -/
def lctCutBody (lp : LctProcs) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const LCT_HDR_N))) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 3) ;;
  .cond lctCutGoodExpr (lctCutMainBody lp) .nop ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 13) (.const 1))

theorem lctCutSpliceBody_noRand : lctCutSpliceBody.NoRand := by
  simp [lctCutSpliceBody, storeNodeOffsExprStmt_noRand, Stmt.NoRand]

theorem lctCutEdgeBody_noRand (lp : LctProcs) : (lctCutEdgeBody lp).NoRand := by
  simp [lctCutEdgeBody, lctCutReadBody, lctCutSpliceBody_noRand, Stmt.NoRand]

theorem lctCutMainBody_noRand (lp : LctProcs) : (lctCutMainBody lp).NoRand := by
  simp [lctCutMainBody, lctCutMainSetupBody, lctCutEdgeBody_noRand, Stmt.NoRand]

theorem lctCutBody_noRand (lp : LctProcs) : (lctCutBody lp).NoRand := by
  simp [lctCutBody, lctCutMainBody_noRand, Stmt.NoRand]

end CutProgramDefs

section CutEdges

/-- After removing the edge node `ed` of the edge `e = {x, y}` from the edge map, the edges
left are those of `F.cut x y`. The forest has no second edge between `x` and `y`
(`eq_edge_of_endpoints`), and its edges are distinct because their ids are. -/
theorem cut_edges_perm {F : MathForest} (hV : F.Valid) {edgeMap : List (ℕ × ForestEdge)}
    {ed x y : ℕ} {e : ForestEdge}
    (hperme : (edgeMap.map Prod.snd).Perm F.edges) (hnd : (edgeMap.map Prod.fst).Nodup)
    (hm : (ed, e) ∈ edgeMap) (he_end : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)) :
    ((edgeMap.filter (fun p => decide (p.1 ≠ ed))).map Prod.snd).Perm (F.cut x y).edges := by
  set filt := edgeMap.filter (fun p => decide (p.1 ≠ ed))
  have hp1 : (e :: filt.map Prod.snd).Perm F.edges :=
    ((cut_edgeMap_perm_filter hnd hm).map Prod.snd).symm.trans hperme
  have hnd_F : F.edges.Nodup := List.Nodup.of_map ForestEdge.eid hV.2.1
  have hnd1 : (e :: filt.map Prod.snd).Nodup := hp1.nodup_iff.2 hnd_F
  have he_F : e ∈ F.edges := hp1.subset List.mem_cons_self
  let q : ForestEdge → Bool := fun e' => !((e'.u == x && e'.v == y) || (e'.u == y && e'.v == x))
  have hqe : q e = false := by
    rcases he_end with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [q, h1, h2]
  have hq_rest : ∀ e' ∈ filt.map Prod.snd, q e' = true := by
    intro e' he'
    by_contra hq
    have hend : (e'.u = x ∧ e'.v = y) ∨ (e'.u = y ∧ e'.v = x) := by
      simp [q] at hq
      by_cases h1 : e'.u = x ∧ e'.v = y
      · exact Or.inl h1
      · exact Or.inr (hq (not_and_or.1 h1))
    have he'_F : e' ∈ F.edges := hp1.subset (List.mem_cons_of_mem _ he')
    have heq := eq_edge_of_endpoints hV he_F he'_F he_end hend
    exact (List.nodup_cons.1 hnd1).1 (heq ▸ he')
  have hfilt : (e :: filt.map Prod.snd).filter q = filt.map Prod.snd := by
    rw [List.filter_cons_of_neg (by simp [hqe]), List.filter_eq_self]
    exact hq_rest
  have hp2 := hp1.filter q
  rw [hfilt] at hp2
  exact hp2

end CutEdges

section CutRunPieces

theorem cut_mainSetup_runs {w b x y n pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ}
    (hr0 : regs 0 = b) (hr1 : regs 1 = x) (hr2 : regs 2 = y)
    (hx : x < n) (hy : y < n)
    (hroom : lctNodesBase b + NODE_STRIDE * (lctCap n + 1) < 2 ^ w) :
    ∃ c,
      Runs w p ω lctCutMainSetupBody { mem := mem, regs := regs, pos := pos } .normal
        { mem := mem,
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update regs 5 (lctNodesBase b)) 6 (x + 1)) 7 (y + 1)) 8
            (lctNodesBase b + NODE_STRIDE * (y + 1))) 15
            (lctNodesBase b + NODE_STRIDE * (x + 1)),
          pos := pos } c ∧ c ≤ 30 := by
  set nb := lctNodesBase b
  have hcap : lctCap n = 2 * n := rfl
  have hx_cap : x + 1 + 1 ≤ lctCap n + 1 := by omega
  have hy_cap : y + 1 + 1 ≤ lctCap n + 1 := by omega
  have hmx := Nat.mul_le_mul_left NODE_STRIDE hx_cap
  have hmy := Nat.mul_le_mul_left NODE_STRIDE hy_cap
  rw [Nat.mul_add, Nat.mul_one] at hmx hmy
  have hstride : 1 ≤ NODE_STRIDE := by unfold NODE_STRIDE; omega
  have hxs : x + 1 ≤ NODE_STRIDE * (x + 1) := Nat.le_mul_of_pos_left _ hstride
  have hys : y + 1 ≤ NODE_STRIDE * (y + 1) := Nat.le_mul_of_pos_left _ hstride
  have hnb : nb = b + LCT_HDR_SIZE := rfl
  have h1w : 1 < 2 ^ w := by unfold NODE_STRIDE at hmx; omega
  have hS : NODE_STRIDE < 2 ^ w := by omega
  have hsz : LCT_HDR_SIZE < 2 ^ w := by unfold LCT_HDR_SIZE at hnb ⊢; omega
  set r5 := Function.update regs 5 nb
  set r6 := Function.update r5 6 (x + 1)
  set r7 := Function.update r6 7 (y + 1)
  set r8 := Function.update r7 8 (nb + NODE_STRIDE * (y + 1))
  have s5 : Runs w p ω (.assign 5 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)))
      { mem := mem, regs := regs, pos := pos } .normal { mem := mem, regs := r5, pos := pos } 4 :=
    runs_assign_iff.2 ⟨nb, Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const hsz)
      (by omega), rfl, rfl, rfl⟩
  have s6 : Runs w p ω (.assign 6 (.bin .add (.reg 1) (.const 1)))
      { mem := mem, regs := r5, pos := pos } .normal { mem := mem, regs := r6, pos := pos } 4 :=
    runs_assign_iff.2 ⟨x + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, hr1]))
      (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
  have s7 : Runs w p ω (.assign 7 (.bin .add (.reg 2) (.const 1)))
      { mem := mem, regs := r6, pos := pos } .normal { mem := mem, regs := r7, pos := pos } 4 :=
    runs_assign_iff.2 ⟨y + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r6, r5, hr2]))
      (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
  have s8 : Runs w p ω (.assign 8 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 7))))
      { mem := mem, regs := r7, pos := pos } .normal { mem := mem, regs := r8, pos := pos } 6 :=
    runs_assign_iff.2 ⟨nb + NODE_STRIDE * (y + 1),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7, r6, r5]))
        (Expr.eval_mul (Expr.eval_const hS) (Expr.eval_reg_of_eq (by simp [r7])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  have s15 : Runs w p ω (.assign 15 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 6))))
      { mem := mem, regs := r8, pos := pos } .normal
      { mem := mem, regs := Function.update r8 15 (nb + NODE_STRIDE * (x + 1)), pos := pos } 6 :=
    runs_assign_iff.2 ⟨nb + NODE_STRIDE * (x + 1),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8, r7, r6, r5]))
        (Expr.eval_mul (Expr.eval_const hS) (Expr.eval_reg_of_eq (by simp [r8, r7, r6]))
          (by omega)) (by omega), rfl, rfl, rfl⟩
  exact ⟨_, link_runs_seq_normal s5 (link_runs_seq_normal s6 (link_runs_seq_normal s7
    (link_runs_seq_normal s8 s15))), by omega⟩

theorem cut_read_runs {w nb y ed eu ev pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ}
    (hr5 : regs 5 = nb) (hr8 : regs 8 = nb + NODE_STRIDE * (y + 1))
    (hed : nodeField mem nb (y + 1) OFF_MIN1_FIRST = ed)
    (heu : nodeField mem nb ed OFF_EU = eu) (hev : nodeField mem nb ed OFF_EV = ev)
    (hy_room : nb + NODE_STRIDE * (y + 1) + NODE_STRIDE < 2 ^ w)
    (hed_room : nb + NODE_STRIDE * ed + NODE_STRIDE < 2 ^ w) :
    ∃ c,
      Runs w p ω lctCutReadBody { mem := mem, regs := regs, pos := pos } .normal
        { mem := mem,
          regs := Function.update (Function.update (Function.update
            (Function.update regs 9 ed) 10 (nb + NODE_STRIDE * ed)) 11 eu) 12 ev,
          pos := pos } c ∧ c ≤ 30 := by
  have hS : NODE_STRIDE < 2 ^ w := by omega
  have hoff_lt : ∀ k, k < NODE_STRIDE → k < 2 ^ w := fun k hk => by omega
  have hed_w : ed ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_left _ (by unfold NODE_STRIDE; omega)
  set r9 := Function.update regs 9 ed
  set r10 := Function.update r9 10 (nb + NODE_STRIDE * ed)
  set r11 := Function.update r10 11 eu
  have s9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 8) (.const OFF_MIN1_FIRST))))
      { mem := mem, regs := regs, pos := pos } .normal { mem := mem, regs := r9, pos := pos } 5 :=
    runs_assign_iff.2 ⟨ed, Expr.eval_load_mem (Expr.eval_add (Expr.eval_reg_of_eq hr8)
      (Expr.eval_const (hoff_lt _ (by unfold OFF_MIN1_FIRST NODE_STRIDE; omega)))
      (by unfold OFF_MIN1_FIRST NODE_STRIDE at *; omega)) hed, rfl, rfl, rfl⟩
  have s10 : Runs w p ω (.assign 10 (.bin .add (.reg 5) (.bin .mul (.const NODE_STRIDE) (.reg 9))))
      { mem := mem, regs := r9, pos := pos } .normal { mem := mem, regs := r10, pos := pos } 6 :=
    runs_assign_iff.2 ⟨nb + NODE_STRIDE * ed,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r9, hr5]))
        (Expr.eval_mul (Expr.eval_const hS) (Expr.eval_reg_of_eq (by simp [r9])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  have s11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.const OFF_EU))))
      { mem := mem, regs := r10, pos := pos } .normal { mem := mem, regs := r11, pos := pos } 5 :=
    runs_assign_iff.2 ⟨eu, Expr.eval_load_mem (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r10]))
      (Expr.eval_const (hoff_lt _ (by unfold OFF_EU NODE_STRIDE; omega)))
      (by unfold OFF_EU NODE_STRIDE at *; omega)) heu, rfl, rfl, rfl⟩
  have s12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 10) (.const OFF_EV))))
      { mem := mem, regs := r11, pos := pos } .normal
      { mem := mem, regs := Function.update r11 12 ev, pos := pos } 5 :=
    runs_assign_iff.2 ⟨ev, Expr.eval_load_mem (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r11, r10]))
      (Expr.eval_const (hoff_lt _ (by unfold OFF_EV NODE_STRIDE; omega)))
      (by unfold OFF_EV NODE_STRIDE at *; omega)) hev, rfl, rfl, rfl⟩
  exact ⟨_, link_runs_seq_normal s9 (link_runs_seq_normal s10 (link_runs_seq_normal s11 s12)),
    by omega⟩

theorem cut_splice_runs {w b x y ed oldFree pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ}
    (hr0 : regs 0 = b) (hr8 : regs 8 = lctNodesBase b + NODE_STRIDE * (y + 1))
    (hr9 : regs 9 = ed) (hr10 : regs 10 = lctNodesBase b + NODE_STRIDE * ed)
    (hr15 : regs 15 = lctNodesBase b + NODE_STRIDE * (x + 1))
    (hfree : mem (b + LCT_HDR_FREE) = oldFree)
    (hx_room : lctNodesBase b + NODE_STRIDE * (x + 1) + NODE_STRIDE < 2 ^ w)
    (hy_room : lctNodesBase b + NODE_STRIDE * (y + 1) + NODE_STRIDE < 2 ^ w)
    (hed_room : lctNodesBase b + NODE_STRIDE * ed + NODE_STRIDE < 2 ^ w) :
    ∃ c,
      Runs w p ω lctCutSpliceBody { mem := mem, regs := regs, pos := pos } .normal
        { mem := lctCutWriteMem mem (lctNodesBase b) b x y oldFree ed,
          regs := Function.update regs 14 oldFree, pos := pos } c ∧ c ≤ 250 := by
  set nb := lctNodesBase b
  have hnb : nb = b + LCT_HDR_SIZE := rfl
  have hS : NODE_STRIDE < 2 ^ w := by omega
  have hfree_w : b + LCT_HDR_FREE < 2 ^ w := by
    unfold LCT_HDR_FREE; unfold LCT_HDR_SIZE at hnb; omega
  have hF : LCT_HDR_FREE < 2 ^ w := by unfold LCT_HDR_FREE at *; omega
  have hP : OFF_PARENT < 2 ^ w := by unfold OFF_PARENT NODE_STRIDE at *; omega
  have h0w : 0 < 2 ^ w := Nat.two_pow_pos w
  set r14 := Function.update regs 14 oldFree
  set m1 := Function.update mem (b + LCT_HDR_FREE) ed
  set m2 := Function.update m1 (nb + NODE_STRIDE * (x + 1) + OFF_PARENT) 0
  set m3 := Function.update m2 (nb + NODE_STRIDE * (y + 1) + OFF_PARENT) 0
  have s14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 0) (.const LCT_HDR_FREE))))
      { mem := mem, regs := regs, pos := pos } .normal { mem := mem, regs := r14, pos := pos } 5 :=
    runs_assign_iff.2 ⟨oldFree, Expr.eval_load_mem (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const hF) hfree_w) hfree, rfl, rfl, rfl⟩
  have sfree : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_FREE)) (.reg 9))
      { mem := mem, regs := r14, pos := pos } .normal { mem := m1, regs := r14, pos := pos } 5 :=
    runs_store_iff.2 ⟨b + LCT_HDR_FREE, ed,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r14, hr0])) (Expr.eval_const hF) hfree_w,
      Expr.eval_reg_of_eq (by simp [r14, hr9]), rfl, rfl, rfl⟩
  have sx : Runs w p ω (.store (.bin .add (.reg 15) (.const OFF_PARENT)) (.const 0))
      { mem := m1, regs := r14, pos := pos } .normal { mem := m2, regs := r14, pos := pos } 5 :=
    runs_store_iff.2 ⟨nb + NODE_STRIDE * (x + 1) + OFF_PARENT, 0,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r14, hr15])) (Expr.eval_const hP)
        (by unfold OFF_PARENT NODE_STRIDE at *; omega),
      Expr.eval_const h0w, rfl, rfl, rfl⟩
  have sy : Runs w p ω (.store (.bin .add (.reg 8) (.const OFF_PARENT)) (.const 0))
      { mem := m2, regs := r14, pos := pos } .normal { mem := m3, regs := r14, pos := pos } 5 :=
    runs_store_iff.2 ⟨nb + NODE_STRIDE * (y + 1) + OFF_PARENT, 0,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r14, hr8])) (Expr.eval_const hP)
        (by unfold OFF_PARENT NODE_STRIDE at *; omega),
      Expr.eval_const h0w, rfl, rfl, rfl⟩
  let pairs : List (ℕ × (Expr × ℕ)) := (List.range NODE_STRIDE).map (fun off =>
    (off, (if off = OFF_EU then Expr.reg 14 else Expr.const 0,
      if off = OFF_EU then oldFree else 0)))
  have hpairs : ∀ q ∈ pairs, q.1 < 2 ^ w ∧ nb + NODE_STRIDE * ed + q.1 < 2 ^ w ∧
      ∀ mem', Expr.eval w { mem := mem', regs := r14, pos := pos } q.2.1 = some q.2.2 := by
    intro q hq
    obtain ⟨off, hoff, rfl⟩ := List.mem_map.1 hq
    have hoff' := List.mem_range.1 hoff
    refine ⟨by omega, by omega, fun mem' => ?_⟩
    by_cases he : off = OFF_EU
    · simp only [he, ↓reduceIte]; exact Expr.eval_reg_of_eq (by simp [r14])
    · simp only [he, ↓reduceIte]; exact Expr.eval_const h0w
  obtain ⟨c_cl, hrun_cl, hc_cl⟩ := storeNodeOffsExprStmt_runs (p := p) (ω := ω)
    (addrExpr := .reg 10) (nb := nb) (x := ed)
    (fun _ => Expr.eval_reg_of_eq (by simp [r14, hr10])) pairs hpairs m3
  have hmap1 : pairs.map (fun q => (q.1, q.2.1)) = lctCutClearPairsExpr 14 := by
    simp [pairs, lctCutClearPairsExpr, List.map_map, Function.comp_def]
  have hmap2 : pairs.map (fun q => (q.1, q.2.2)) = lctCutClearPairs oldFree := by
    simp [pairs, lctCutClearPairs, List.map_map, Function.comp_def]
  have hsum : (pairs.map fun q => (Expr.reg 10).size + q.2.1.size).sum = 2 * NODE_STRIDE := by
    have : (pairs.map fun q => (Expr.reg 10).size + q.2.1.size) =
        (List.range NODE_STRIDE).map (fun _ => 2) := by
      simp only [pairs, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro off _
      split_ifs <;> rfl
    rw [this, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm]
  have hlen : pairs.length = NODE_STRIDE := by simp [pairs]
  rw [hmap1, hmap2] at hrun_cl
  rw [hsum, hlen] at hc_cl
  have hw : lctCutWriteMem mem nb b x y oldFree ed = writeNodeOffs m3 nb ed
      (lctCutClearPairs oldFree) := rfl
  rw [hw]
  refine ⟨_, link_runs_seq_normal s14 (link_runs_seq_normal sfree (link_runs_seq_normal sx
    (link_runs_seq_normal sy hrun_cl))), ?_⟩
  unfold NODE_STRIDE at hc_cl
  omega

end CutRunPieces

end MinCostFlow.LinkCut.Prog
