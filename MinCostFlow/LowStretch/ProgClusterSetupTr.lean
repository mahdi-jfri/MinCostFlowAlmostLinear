module

public import MinCostFlow.LowStretch.ProgClusterSetupDr

/-!
# The setup of a cluster: the precondition of `treeP`

After the first run of Dijkstra, the setup calls `treeP` with its arrays from the end `Z` of the
cells of `drawP` on (`DWE.tf Z`). Its precondition `TF.Pre` asks that the arrays follow each
other and that every cell that `treeP` reads for a node lies below `Z`. The cells it reads are
the parent arc of the node in the run, the stored entry of that arc, its pair and the label and
local index of an end of the pair (`First.edge` bounds all of them), so they lie in the arrays
of `drawP` or below `h` (`First.tfPre`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace Rec

variable {w : ℕ} {T : KT} {G : PG} {c : Cl} {R : Rec} {E : DWE} {mem M : ℕ → ℕ}

/-- **The precondition of `treeP`** after the first run, with its arrays from `Z` on. -/
theorem First.tfPre (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (hIN : E.IN + 3 * m ≤ E.H) (hLAB : E.LAB + n ≤ E.H)
    (hLOC : E.LOC + NL ≤ E.H) {Z : ℕ} (hZ : drawEnd E ≤ Z) (hw : Z + 8 * E.s + 8 < 2 ^ w) :
    (E.tf Z).Pre M w := by
  have eE : drawEnd E = E.H + 16 * E.nS + 8 * E.s + 9 + (3 + 4 * E.J + 2 * E.J * E.Aq) + 2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, fun u hu hux => ?_⟩
  all_goals try (simp only [DWE.tf]; omega)
  have hu' : u < E.s := hu
  have hux' : u ≠ E.x0 := hux
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpk, hord, -, hpp, he0, hlab⟩ :=
    h.edge hAP hSA Z hu' hux'
  have e1 : (E.tf Z).TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  have e2 : (E.tf Z).NN = E.s + 1 := rfl
  have e3 : (E.tf Z).PAR = Z := rfl
  have e4 : (E.tf Z).ORD = E.H + 8 * E.nS + 2 * E.s + 3 := rfl
  have e5 : (E.tf Z).CS = E.H + 12 * E.nS + 2 * E.s + 3 := rfl
  have e6 : (E.tf Z).CL = E.H + 14 * E.nS + 2 * E.s + 3 := rfl
  have e7 : (E.tf Z).SA = E.SA := rfl
  have e8 : (E.tf Z).IN = E.IN := rfl
  have e9 : (E.tf Z).LAB = E.LAB := rfl
  have e10 : (E.tf Z).LOC = E.LOC := rfl
  have e11 : E.ap.ORD = E.H + 8 * E.nS + 2 * E.s + 3 := rfl
  rw [e11] at hord
  have hpp' : (E.tf Z).pp M u < m := hpp
  have he0' : (E.tf Z).e0 M u < n := he0
  have hlab' : M ((E.tf Z).LAB + (E.tf Z).e0 M u) < NL := hlab
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  rw [e9] at hlab'
  refine ⟨by omega, by omega, by omega, ?_, by omega, by omega, by omega, by omega, by omega⟩
  show E.SA + M (E.H + 8 * E.nS + 2 * E.s + 3 + (E.tf Z).pk M u) + 1 < Z
  omega

end Rec

/-! ### The addresses of the layout -/

section Eval

variable {w : ℕ} {st : State}

theorem mulC_eval {a r v : ℕ} (h : st.regs r = v) (ha : a < 2 ^ w) (hb : a * v < 2 ^ w) :
    (mulC a r).eval w st = some (a * v) :=
  Expr.eval_mul (Expr.eval_const ha) (Expr.eval_reg_of_eq h) hb

/-- The value of `suH a b k`, with `H`, `nS`, `s` in registers `21`, `14`, `13`. -/
theorem suH_eval {H nS s a b k x : ℕ} (h21 : st.regs 21 = H) (h14 : st.regs 14 = nS)
    (h13 : st.regs 13 = s) (hw : 2 ^ 20 < 2 ^ w) (ha : a < 2 ^ 20) (hb : b < 2 ^ 20)
    (hk : k < 2 ^ 20) (hx : x = H + a * nS + b * s + k) (hlt : x < 2 ^ w) :
    (suH a b k).eval w st = some x := by
  subst hx
  exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h21)
    (mulC_eval h14 (by omega) (by omega)) (by omega)) (mulC_eval h13 (by omega) (by omega))
    (by omega)) (Expr.eval_const (by omega)) hlt

/-- The value of `suZ a b c k`, with `Z`, `nS`, `s`, `L` in registers `24`, `14`, `13`, `28`. -/
theorem suZ_eval {Z nS s L a b c k x : ℕ} (h24 : st.regs 24 = Z) (h14 : st.regs 14 = nS)
    (h13 : st.regs 13 = s) (h28 : st.regs 28 = L) (hw : 2 ^ 20 < 2 ^ w) (ha : a < 2 ^ 20)
    (hb : b < 2 ^ 20) (hc : c < 2 ^ 20) (hk : k < 2 ^ 20) (hx : x = Z + a * nS + b * s + c * L + k)
    (hlt : x < 2 ^ w) : (suZ a b c k).eval w st = some x := by
  subst hx
  exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h24)
    (mulC_eval h14 (by omega) (by omega)) (by omega)) (mulC_eval h13 (by omega) (by omega))
    (by omega)) (mulC_eval h28 (by omega) (by omega)) (by omega)) (Expr.eval_const (by omega))
    hlt

/-- The value of `suR b k`, with `RR`, `s` in registers `33`, `13`. -/
theorem suR_eval {RR s b k x : ℕ} (h33 : st.regs 33 = RR) (h13 : st.regs 13 = s)
    (hw : 2 ^ 20 < 2 ^ w) (hb : b < 2 ^ 20) (hk : k < 2 ^ 20) (hx : x = RR + b * s + k)
    (hlt : x < 2 ^ w) : (suR b k).eval w st = some x := by
  subst hx
  exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h33)
    (mulC_eval h13 (by omega) (by omega)) (by omega)) (Expr.eval_const (by omega)) hlt

end Eval

end MinCostFlow.LowStretch
