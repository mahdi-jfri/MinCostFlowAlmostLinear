module

public import MinCostFlow.LowStretch.ProgPreKLoop
public import MinCostFlow.LowStretch.ProgPreLoop2

/-!
# Two filter loops of the preprocessing

* `filtP (nodeE (.reg 15)) (.reg 15) 1` with `args = [N, NODES, KMW, KPAR, θ]` lists the
  `θ`-nodes of the merge tree (`nodesSpec`).
* `filtP eDiff (.reg 15) 2` with `args = [m, SA, IN, LAB]` lists the pairs whose ends have
  different labels, two cells apart (`saSpec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- What the node filter needs. -/
def nodesPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ N NODES KMW KPAR TH, args = [N, NODES, KMW, KPAR, TH] ∧ KMW + N ≤ NODES ∧
    KPAR + N ≤ NODES ∧ NODES < 2 ^ w ∧ ∀ k < N, mem (KPAR + k) < N

/-- The test of the node filter. -/
def nodesC (args : List ℕ) (mem : ℕ → ℕ) (k : ℕ) : ℕ :=
  if mem (args.getD 2 0 + k) < args.getD 4 0 ∧
    (k + 1 < args.getD 0 0 → args.getD 4 0 ≤ mem (args.getD 2 0 + mem (args.getD 3 0 + k)))
  then 1 else 0

theorem nodesSpec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [filtP (nodeE (.reg 15)) (.reg 15) 1]) :
    MeetsContract w p b (filtC w (nodeE (.reg 15)) (.reg 15) 1 (nodesPre w) nodesC fun _ _ k => k) := by
  refine filtP_spec hp (fun args mem hpre st hR hi hfr => ?_)
  obtain ⟨N, NODES, KMW, KPAR, TH, rfl, l1, l2, hD, hlt⟩ := hpre
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hi hfr ⊢
  obtain ⟨k, h15⟩ : ∃ k, st.regs 15 = k := ⟨_, rfl⟩
  rw [h15] at hi ⊢
  have hb := hlt k hi
  have ha : st.mem (KPAR + k) = mem (KPAR + k) := hfr _ (Or.inl (by omega))
  refine ⟨?_, fun _ => Expr.eval_reg_of_eq h15⟩
  have r0 : st.regs 0 = N := hR 0 (by norm_num)
  have r2 : st.regs 2 = KMW := hR 2 (by norm_num)
  have r3 : st.regs 3 = KPAR := hR 3 (by norm_num)
  have r4 : st.regs 4 = TH := hR 4 (by norm_num)
  refine nodeE_eval (Expr.eval_reg_of_eq h15) r0 r2 r3 r4 (hfr (KMW + k) (Or.inl (by omega))) ha
    (hfr (KMW + mem (KPAR + k)) (Or.inl (by omega))) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-- `1` if the ends of pair `i` have different labels, with `IN` and `LAB` in registers `2` and
`3`. -/
def eDiff : Expr :=
  .bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 3) eEnd0)) (.load (.bin .add (.reg 3) eEnd1)))

/-- What the pair filter needs. -/
def saPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ M DST IN LAB K, args = [M, DST, IN, LAB] ∧ IN + 3 * M ≤ LAB ∧ LAB + K ≤ DST ∧ DST < 2 ^ w ∧
    ∀ i < M, mem (IN + 3 * i) < K ∧ mem (IN + 3 * i + 1) < K

/-- The test of the pair filter. -/
def saC (args : List ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ :=
  if mem (args.getD 3 0 + mem (args.getD 2 0 + 3 * i)) =
    mem (args.getD 3 0 + mem (args.getD 2 0 + 3 * i + 1)) then 0 else 1

theorem saSpec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [filtP eDiff (.reg 15) 2]) :
    MeetsContract w p b (filtC w eDiff (.reg 15) 2 (saPre w) saC fun _ _ i => i) := by
  refine filtP_spec hp (fun args mem hpre st hR hi hfr => ?_)
  obtain ⟨M, DST, IN, LAB, K, rfl, l1, l2, hD, hlt⟩ := hpre
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hi hfr ⊢
  obtain ⟨i, h15⟩ : ∃ i, st.regs 15 = i := ⟨_, rfl⟩
  rw [h15] at hi ⊢
  obtain ⟨hu, hv⟩ := hlt i hi
  have h2 : st.regs 2 = IN := hR 2 (by norm_num)
  have h3 : st.regs 3 = LAB := hR 3 (by norm_num)
  have e0 : eEnd0.eval w st = some (mem (IN + 3 * i)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h15) (by omega))
      (by omega)) (hfr _ (Or.inl (by omega)))
  have e1 : eEnd1.eval w st = some (mem (IN + 3 * i + 1)) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h2)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h15) (by omega))
      (by omega)) (Expr.eval_const (by omega)) (by omega)) (hfr _ (Or.inl (by omega)))
  have f0 := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3) e0 (by omega))
    (hfr _ (Or.inl (by omega)))
  have f1 := Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h3) e1 (by omega))
    (hfr _ (Or.inl (by omega)))
  have g := Expr.eval_bin (op := .eq) f0 f1 (by simp; split_ifs <;> omega)
  have g2 := Expr.eval_bin (op := .sub) (Expr.eval_const (k := 1) (by omega)) g
    (by simp; split_ifs <;> omega)
  refine ⟨?_, fun _ => Expr.eval_reg_of_eq h15⟩
  unfold eDiff; rw [g2]; unfold saC
  simp only [List.getD_cons_zero, List.getD_cons_succ, BinOp.eval_sub, BinOp.eval]
  split_ifs <;> rfl

end MinCostFlow.LowStretch
