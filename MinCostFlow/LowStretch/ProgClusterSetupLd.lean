module

public import MinCostFlow.LowStretch.ProgClusterSetupW
public import MinCostFlow.LowStretch.ProgChildOneA

/-!
# The setup of a cluster: the loads

The first part of `setupP` loads the words that it needs into the registers `3` to `22`
(`suPro`). This file names these words (`SuV`) and proves that the loads put them in the
registers (`suPro_runs`), from the memory facts in `SuFacts`, by `runs_assigns_le`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The words in the registers `0` to `22` of `setupP` after the loads. -/
structure SuV where
  GB : ℕ
  RB : ℕ
  h : ℕ
  n : ℕ
  m : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  B : ℕ
  J : ℕ
  INF : ℕ
  s : ℕ
  nS : ℕ
  SA : ℕ
  lθ : ℕ
  x0 : ℕ
  t : ℕ
  nH : ℕ
  HW : ℕ
  ts : ℕ

namespace SuV

variable (V : SuV)

/-- The words in the registers `0` to `22`. -/
def vals : List ℕ :=
  [V.GB, V.RB, V.h, V.n, V.m, V.IN, V.PW, V.EXP, V.LAB, V.LOC, V.B, V.J, V.INF, V.s, V.nS, V.SA,
    V.lθ, V.x0, V.t, V.nH, V.HW, V.h + 51, V.ts]

/-- The arguments of `setupP`. -/
def args : List ℕ := [V.GB, V.RB, V.h]

/-- All registers after the loads. -/
def f (r : ℕ) : ℕ := if r < 23 then V.vals.getD r 0 else 0

/-- The registers after the loads, as later steps use them. -/
def Regs (st : State) : Prop := ∀ r < 23, st.regs r = V.vals.getD r 0

theorem Regs.upd {V : SuV} {st : State} (h : V.Regs st) {r : ℕ} (hr : 23 ≤ r) (v : ℕ)
    (M : ℕ → ℕ) (q : ℕ) : V.Regs { mem := M, regs := Function.update st.regs r v, pos := q } :=
  fun r' hr' => by
    dsimp only
    rw [Function.update_of_ne (by omega)]; exact h r' hr'

theorem regs_of_f {V : SuV} {st : State} (h : st.regs = V.f) : V.Regs st := fun r hr => by
  rw [h]; simp [f, hr]

end SuV

/-- The memory facts that the loads of `setupP` use. -/
structure SuFacts (w : ℕ) (V : SuV) (M : ℕ → ℕ) : Prop where
  g0 : M V.GB = V.n
  g1 : M (V.GB + 1) = V.m
  g3 : M (V.GB + 3) = V.IN
  g4 : M (V.GB + 4) = V.PW
  g5 : M (V.GB + 5) = V.EXP
  g6 : M (V.GB + 6) = V.LAB
  g7 : M (V.GB + 7) = V.LOC
  g18 : M (V.GB + 18) = V.B
  g19 : M (V.GB + 19) = V.J
  g20 : M (V.GB + 20) = V.INF
  r0 : M V.RB = V.s
  r1 : M (V.RB + 1) = V.nS
  r2 : M (V.RB + 2) = V.SA
  r3 : M (V.RB + 3) = V.lθ
  r6 : M (V.RB + 6) = V.t
  r7 : M (V.RB + 7) = V.nH
  r8 : M (V.RB + 8) = V.HW
  x0 : M (V.LOC + M (V.LAB + M (V.RB + 5))) = V.x0
  ts : M (V.LOC + M (V.LAB + V.t)) = V.ts
  bGB : V.GB + 21 < 2 ^ w
  bRB : V.RB + 9 < 2 ^ w
  bh : V.h + 51 < 2 ^ w
  blab : V.LAB + M (V.RB + 5) < 2 ^ w ∧ V.LAB + V.t < 2 ^ w
  bloc : V.LOC + M (V.LAB + M (V.RB + 5)) < 2 ^ w ∧ V.LOC + M (V.LAB + V.t) < 2 ^ w

theorem suPro_pairwise : suPro.Pairwise (fun a b => a.1 < b.1) := by decide

theorem suPro_cost : (suPro.map fun q => q.2.size + 2).sum ≤ 300 := by decide

/-- **The loads.** Started on the arguments of `V`, the loads of `setupP` put the words of `V`
in the registers. -/
theorem suPro_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {V : SuV} {M : ℕ → ℕ} {pos : ℕ}
    (hF : SuFacts w V M) {s : Stmt} {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ st : State, V.Regs st → st.mem = M →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 300 + c ≤ T) :
    ∃ o st' c, Runs w p ω (assigns suPro s) (startState V.args M pos) o st' c ∧ Q o st' ∧
      c ≤ T := by
  refine runs_start_le (runs_assigns_le V.f (fun i => V.args.getD i 0) suPro _ 0
    suPro_pairwise rfl (fun r => ?_) ?_ (fun st' h1 h2 => ?_))
  · split_ifs with h
    · rfl
    · simp only [suPro, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases Nat.lt_or_ge r 3 with h3 | h3
      · interval_cases r <;> rfl
      · have : V.args.getD r 0 = 0 := List.getD_eq_default _ _ (by simp [SuV.args]; omega)
        show V.args.getD r 0 = V.f r
        rw [this]
        unfold SuV.f
        split_ifs with h23
        · exfalso; omega
        · rfl
  · intro q hq st' hM hr
    have hM' : st'.mem = M := hM
    have ld : ∀ {r i x v : ℕ}, st'.regs r = x → x + i < 2 ^ w → st'.mem (x + i) = v →
        (ldO r i).eval w st' = some v := fun hr hb hm =>
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const
        (by omega)) hb) hm
    have hG := hF.bGB; have hR := hF.bRB; have hH := hF.bh
    simp only [suPro, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    have R := fun i (hi : i < _) => hr i hi <;> dsimp only at R
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g0)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g1)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g3)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g4)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g5)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g6)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g7)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g18)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g19)
    · exact ld (show st'.regs 0 = V.GB from R 0 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.g20)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r0)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r1)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r2)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r3)
    · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
            (show st'.regs 9 = V.LOC from R 9 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 8 = V.LAB from R 8 (by norm_num)))
          (ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega) (congrFun hM' _))
          hF.blab.1) (congrFun hM' _)) hF.bloc.1) ((congrFun hM' _).trans hF.x0)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r6)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r7)
    · exact ld (show st'.regs 1 = V.RB from R 1 (by norm_num)) (by omega)
        ((congrFun hM' _).trans hF.r8)
    · exact Expr.eval_add (Expr.eval_reg_of_eq (show st'.regs 2 = V.h from R 2 (by norm_num)))
        (Expr.eval_const (by omega)) hF.bh
    · exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
            (show st'.regs 9 = V.LOC from R 9 (by norm_num)))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
                (show st'.regs 8 = V.LAB from R 8 (by norm_num)))
          (Expr.eval_reg_of_eq (show st'.regs 18 = V.t from R 18 (by norm_num))) hF.blab.2)
          (congrFun hM' _)) hF.bloc.2) ((congrFun hM' _).trans hF.ts)
  · obtain ⟨o, st'', c, a1, a2, a3⟩ := hrest st' (SuV.regs_of_f h2) h1
    refine ⟨o, st'', c, a1, a2, ?_⟩
    have := suPro_cost
    omega

end MinCostFlow.LowStretch
