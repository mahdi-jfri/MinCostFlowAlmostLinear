module

public import MinCostFlow.LowStretch.ProgChildOneAll

/-!
# The top level: the loads

The child step starts by loading the sizes of the three blocks and laying out its scratch arrays
from `h + 9 nch` on (`topPro`). This file names the values of the registers `0` to `26` after
these loads (`CS.topF`) and proves that the loads put them there (`CS.topPro_runs`), when the
scratch arrays end at a word.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The words in the registers `0` to `26` after the loads of `childP`. -/
def topVals : List ℕ :=
  [S.GB, S.RB, S.XB, S.h, S.nch, S.s, S.nA, S.CHX, S.OFFN, S.CNTN, S.ORDN, S.KEY, S.OFFK,
    S.CNTK, S.ORDK, S.HM, S.H0, S.X.nP, S.X.PL, S.X.PO, S.X.ACT, S.E.IN, S.E.LAB, S.E.LOC,
    S.nch + 1, 0, S.H0]

/-- All registers after the loads. -/
def topF (r : ℕ) : ℕ := S.topVals.getD r 0

/-- The arguments of the child step. -/
def topArgs : List ℕ := [S.GB, S.RB, S.XB, S.h]

theorem topPro_pairwise : topPro.Pairwise (fun a b => a.1 < b.1) := by decide

theorem topPro_cost : (topPro.map fun q => q.2.size + 2).sum ≤ 300 := by decide

variable {S}

/-- The number of children is one more than the number of petals. -/
theorem nch_eq {w : ℕ} (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.X.nP + 1 = S.nch := by
  have h : S.X.nP = S.D.ps.length := hpre.pet.nP
  rw [h]; rfl

/-- **The loads.** Started on the arguments `[GB, RB, XB, h]`, the loads of `childP` put the
words of `topF` in the registers and do not touch the memory. -/
theorem topPro_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {pos : ℕ}
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hb : S.H0 + S.nch + 4 < 2 ^ w) {s : Stmt} {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ st : State, st.regs = S.topF → st.mem = S.mem →
      ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 300 + c ≤ T) :
    ∃ o st' c, Runs w p ω (assigns topPro s) (startState S.topArgs S.mem pos) o st' c ∧
      Q o st' ∧ c ≤ T := by
  have hnP := nch_eq hpre
  have hX : S.XB + 16 ≤ S.h := hpre.below (S.XB, 16) (by simp [readRegs])
  have hG : S.GB + 21 ≤ S.h := hpre.below (S.GB, 21) (by simp [readRegs])
  have hR : S.RB + 9 ≤ S.h := hpre.below (S.RB, 9) (by simp [readRegs])
  have e7 : S.CHX = S.h + 9 * S.nch := rfl
  have e8 : S.OFFN = S.CHX + S.s := rfl
  have e9 : S.CNTN = S.OFFN + S.nch + 1 := rfl
  have e10 : S.ORDN = S.CNTN + S.nch := rfl
  have e11 : S.KEY = S.ORDN + S.s := rfl
  have e12 : S.OFFK = S.KEY + S.nA := rfl
  have e13 : S.CNTK = S.OFFK + S.nch + 2 := rfl
  have e14 : S.ORDK = S.CNTK + S.nch + 1 := rfl
  have e15 : S.HM = S.ORDK + S.nA := rfl
  have e16 : S.H0 = S.HM + S.s := rfl
  refine runs_start_le (runs_assigns_le S.topF (fun i => S.topArgs.getD i 0) topPro _ 0
    topPro_pairwise rfl (fun r => ?_) ?_ (fun st' h1 h2 => ?_))
  · split_ifs with h
    · rfl
    · simp only [topPro, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases Nat.lt_or_ge r 4 with h4 | h4
      · interval_cases r <;> rfl
      · have : S.topArgs.getD r 0 = 0 := List.getD_eq_default _ _ (by simp [topArgs]; omega)
        show S.topArgs.getD r 0 = S.topF r
        rw [this]
        exact (List.getD_eq_default _ _ (by simp [topVals]; omega)).symm
  · intro q hq st' hM hr
    have hM' : st'.mem = S.mem := hM
    have hw : 2 < 2 ^ w := by omega
    have ld : ∀ {r i x v : ℕ}, st'.regs r = x → x + i < 2 ^ w → S.mem (x + i) = v →
        (ldO r i).eval w st' = some v := fun hr hb hm =>
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const
        (by omega)) hb) ((congrFun hM' _).trans hm)
    have rg : ∀ {r v : ℕ}, st'.regs r = v → (Expr.reg r).eval w st' = some v :=
      fun h => Expr.eval_reg_of_eq h
    simp only [topPro, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    have R := fun i (hi : i < _) => hr i hi <;> dsimp only at R
    · show _ = some S.nch
      rw [← hnP]
      exact Expr.eval_add (ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl)
        (Expr.eval_const (by omega)) (by omega)
    · exact ld (show st'.regs 1 = S.RB from R 1 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl
    · exact Expr.eval_add (rg (show st'.regs 3 = S.h from R 3 (by norm_num)))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (rg (show st'.regs 4 = S.nch from R 4 (by norm_num))) (by omega)) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 7 = S.CHX from R 7 (by norm_num)))
        (rg (show st'.regs 5 = S.s from R 5 (by norm_num))) (by omega)
    · exact Expr.eval_add (Expr.eval_add (rg (show st'.regs 8 = S.OFFN from R 8 (by norm_num)))
        (rg (show st'.regs 4 = S.nch from R 4 (by norm_num))) (by omega))
        (Expr.eval_const (by omega)) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 9 = S.CNTN from R 9 (by norm_num)))
        (rg (show st'.regs 4 = S.nch from R 4 (by norm_num))) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 10 = S.ORDN from R 10 (by norm_num)))
        (rg (show st'.regs 5 = S.s from R 5 (by norm_num))) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 11 = S.KEY from R 11 (by norm_num)))
        (rg (show st'.regs 6 = S.nA from R 6 (by norm_num))) (by omega)
    · exact Expr.eval_add (Expr.eval_add (rg (show st'.regs 12 = S.OFFK from R 12 (by norm_num)))
        (rg (show st'.regs 4 = S.nch from R 4 (by norm_num))) (by omega))
        (Expr.eval_const (by omega)) (by omega)
    · exact Expr.eval_add (Expr.eval_add (rg (show st'.regs 13 = S.CNTK from R 13 (by norm_num)))
        (rg (show st'.regs 4 = S.nch from R 4 (by norm_num))) (by omega))
        (Expr.eval_const (by omega)) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 14 = S.ORDK from R 14 (by norm_num)))
        (rg (show st'.regs 6 = S.nA from R 6 (by norm_num))) (by omega)
    · exact Expr.eval_add (rg (show st'.regs 15 = S.HM from R 15 (by norm_num)))
        (rg (show st'.regs 5 = S.s from R 5 (by norm_num))) (by omega)
    · exact ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 2 = S.XB from R 2 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 0 = S.GB from R 0 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 0 = S.GB from R 0 (by norm_num)) (by omega) rfl
    · exact ld (show st'.regs 0 = S.GB from R 0 (by norm_num)) (by omega) rfl
    · exact Expr.eval_add (rg (show st'.regs 4 = S.nch from R 4 (by norm_num)))
        (Expr.eval_const (by omega)) (by omega)
    · exact Expr.eval_const (by omega)
    · exact rg (show st'.regs 16 = S.H0 from R 16 (by norm_num))
  · obtain ⟨o, st'', c, a1, a2, a3⟩ := hrest st' h2 h1
    exact ⟨o, st'', c, a1, a2, by have := topPro_cost; omega⟩

end CS

end MinCostFlow.LowStretch
