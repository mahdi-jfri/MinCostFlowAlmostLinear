module

public import MinCostFlow.LowStretch.ProgPreLoop2

/-!
# Where the preprocessing puts its arrays

The input is at address `0`: `n`, `m`, then three words per edge, so the ends of edge `p` are at
`2 + 3p` and `3 + 3p`. Every array of the preprocessing starts at an address `c + u m + v n` for
fixed numbers `c`, `u`, `v`. The program computes such an address with the expression
`lin c u v`, from `n` in register `0` and `m` in register `1` (`lin_eval`). The node arrays have
room for `2n` nodes.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `c + u m + v n`, with `n` in register `0` and `m` in register `1`. -/
def lin (c u v : ℕ) : Expr :=
  .bin .add (.bin .add (.const c) (.bin .mul (.const u) (.reg 1))) (.bin .mul (.const v) (.reg 0))

theorem lin_size (c u v : ℕ) : (lin c u v).size = 9 := rfl

theorem lin_eval {w : ℕ} {st : State} {n m c u v : ℕ} (h0 : st.regs 0 = n) (h1 : st.regs 1 = m)
    (hb : c + u * m + v * n + u + v < 2 ^ w) :
    (lin c u v).eval w st = some (c + u * m + v * n) :=
  Expr.eval_add (Expr.eval_add (Expr.eval_const (by omega))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h1) (by omega)) (by omega))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h0) (by omega)) (by omega)

/-! ### The addresses -/

/-- The six numbers of `parVal`. -/
def aPAR (_n m : ℕ) : ℕ := 2 + 3 * m
/-- The exponents of the rounded weights. -/
def aEXP (_n m : ℕ) : ℕ := 8 + 3 * m
/-- The rounded weights. -/
def aPW (_n m : ℕ) : ℕ := 8 + 4 * m
/-- The smaller end of each pair. -/
def aTLK (_n m : ℕ) : ℕ := 8 + 5 * m
def aDOFF (_n m : ℕ) : ℕ := 8 + 6 * m
def aDCNT (n m : ℕ) : ℕ := 9 + 6 * m + n
def aDORD (n m : ℕ) : ℕ := 9 + 6 * m + 2 * n
def aMARK (n m : ℕ) : ℕ := 9 + 7 * m + 2 * n
def aBEST (n m : ℕ) : ℕ := 9 + 7 * m + 3 * n
/-- The kept pairs. -/
def aDOUT (n m : ℕ) : ℕ := 9 + 7 * m + 4 * n
/-- Their sort keys. -/
def aKEYS (n m : ℕ) : ℕ := 9 + 8 * m + 4 * n
def aUF (n m : ℕ) : ℕ := 9 + 9 * m + 4 * n
def aSZ (n m : ℕ) : ℕ := 9 + 9 * m + 5 * n
def aTN (n m : ℕ) : ℕ := 9 + 9 * m + 6 * n
def aKPAR (n m : ℕ) : ℕ := 9 + 9 * m + 7 * n
def aKCH1 (n m : ℕ) : ℕ := 9 + 9 * m + 9 * n
def aKCH2 (n m : ℕ) : ℕ := 9 + 9 * m + 11 * n
def aKMW (n m : ℕ) : ℕ := 9 + 9 * m + 13 * n
def aKMP (n m : ℕ) : ℕ := 9 + 9 * m + 15 * n
def aKSZ (n m : ℕ) : ℕ := 9 + 9 * m + 17 * n
def aKLO (n m : ℕ) : ℕ := 9 + 9 * m + 19 * n
def aHEAD (n m : ℕ) : ℕ := 9 + 9 * m + 21 * n
def aORDL (n m : ℕ) : ℕ := 9 + 9 * m + 23 * n
def aLCA (n m : ℕ) : ℕ := 9 + 9 * m + 24 * n
def aGOFF (n m : ℕ) : ℕ := 9 + 10 * m + 24 * n
def aGCNT (n m : ℕ) : ℕ := 10 + 10 * m + 26 * n
def aGORD (n m : ℕ) : ℕ := 10 + 10 * m + 28 * n
/-- Five cells: `N`, `θ`, `lθ`, `s`, `nS`. -/
def aCTL (n m : ℕ) : ℕ := 10 + 11 * m + 28 * n
def aNODES (n m : ℕ) : ℕ := 15 + 11 * m + 28 * n
def aLAB (n m : ℕ) : ℕ := 15 + 11 * m + 30 * n
def aLOC (n m : ℕ) : ℕ := 15 + 11 * m + 32 * n
def aSA (n m : ℕ) : ℕ := 15 + 11 * m + 34 * n
def aOUT (n m : ℕ) : ℕ := 15 + 13 * m + 34 * n
/-- The heap pointer. -/
def aH (n m : ℕ) : ℕ := 15 + 13 * m + 35 * n

end MinCostFlow.LowStretch
