module

public import MinCostFlow.LowStretch.ProgClusterSetup
public import MinCostFlow.LowStretch.Params
public import MinCostFlow.LowStretch.Exist4

/-!
# The setup of a cluster: facts of the ghost and of the layout

The petal searches need `8 L (λ₀ + 3) ≤ Δ` and `V ≤ 2^λ₀ κ` (`PW.Ok.hΔ`, `PW.Ok.hV`). They hold
for the constants `par n m` of every pair graph with a vertex, as in `Params.fit`, and for every
cluster with at least two vertices whose record meets `Rec.Ok` (`setup_hΔ`, `setup_hV`).

The second part gives the addresses of the layout of `setupP` as numbers (`SuN`) and the bound
on its end `hS` that `SetupOut` asks (`SuN.hS_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The constants `par n m` meet the bound `8 L (λ₀ + 3) ≤ 2 B` of `Par.Fit`. -/
theorem par_BL (n m : ℕ) : 8 * (par n m).L * (Cl.lam (par n m) 0 + 3) ≤ 2 * (par n m).B := by
  rw [lam0_eq]; simp only [par, pB]; ring_nf; exact le_rfl

/-- The constants `par n m` meet the volume bound of `Par.Fit` on every pair graph with a
vertex. The proof is the one of `Params.fit`. -/
theorem par_lam (G : PG) (hn : 1 ≤ G.n) :
    Vmax G (par G.n G.m) ≤ 2 ^ Cl.lam (par G.n G.m) 0 * ((par G.n G.m).κ : ℝ) := by
  rw [Vmax_eq, lam0_eq]
  simp only [par]
  have hn2 : 0 < G.n ^ 2 := by positivity
  have hm : G.m < G.n ^ 2 * pκ G.n G.m := by
    unfold pκ; exact Nat.lt_mul_div_succ _ hn2
  have key : (G.n + 1) * pκ G.n G.m + G.m ≤ 2 ^ 2 ^ pL G.n * pκ G.n G.m := by
    have h1 := sq_le_pow G.n
    have h2 : (G.n + 1) * pκ G.n G.m + G.n ^ 2 * pκ G.n G.m ≤ (G.n + 2) ^ 2 * pκ G.n G.m := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by nlinarith)
    have h3 := Nat.mul_le_mul_right (pκ G.n G.m) h1
    omega
  exact_mod_cast key

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- A cluster with two vertices lies in a graph with a vertex. -/
theorem Rec.Ok.n_pos (h : R.Ok T G P c) (hX : 2 ≤ c.X.card) : 1 ≤ G.n := by
  have := Finset.card_le_card h.inv.sub
  simp only [Finset.card_range] at this
  omega

/-- **The radius is large**: `8 L (λ₀ + 3) ≤ Δ` (`PW.Ok.hΔ`). -/
theorem setup_hΔ (h : R.Ok T G P c) (hP : P = par G.n G.m) (hX : 2 ≤ c.X.card) :
    8 * P.L * (Cl.lam P 0 + 3) ≤ c.Δ G := by
  subst hP; exact Cl.Δ_ge_L h.inv hX (par_BL _ _)

/-- **The volume is small**: `V ≤ 2^λ₀ κ` (`PW.Ok.hV`). -/
theorem setup_hV (h : R.Ok T G P c) (hP : P = par G.n G.m) (hX : 2 ≤ c.X.card) :
    c.V G P ≤ 2 ^ Cl.lam P 0 * (P.κ : ℝ) := by
  have hn := h.n_pos hX
  subst hP; exact Cl.V_le_Vmax.trans (par_lam G hn)

/-! ### The layout as numbers -/

/-- The words that fix the layout of `setupP`: the heap pointer `h`, the numbers `nS` of stored
pairs and `s` of nodes, the number `J` of classes and the number `L` of buckets. -/
structure SuN where
  h : ℕ
  nS : ℕ
  s : ℕ
  J : ℕ
  L : ℕ

namespace SuN

variable (N : SuN)

/-- The start of the arrays of `drawP`. -/
def H : ℕ := N.h + 51

/-- The end of the cells of `drawP` (`drawEnd`). -/
def Z : ℕ := N.H + 16 * N.nS + 8 * N.s + 14 + 4 * N.J + 2 * N.J * (2 * N.nS + N.s + 1)

/-- The address `Z + a nS + b s + c L + k`. -/
def z (a b c k : ℕ) : ℕ := N.Z + a * N.nS + b * N.s + c * N.L + k

/-- The capacity of the queues of the petal searches. -/
def A2 : ℕ := 2 * N.nS + 2 * N.s

/-- The queues of the petal searches. -/
def D : ℕ := N.z 23 26 2 16

/-- The number `J + 5` of classes of the queues of the petal searches. The arcs of the active
pairs have classes up to `J + 4`, since their reduced lengths are below `4 · 128 B n² θ`. -/
def Jq : ℕ := N.J + 5

/-- The two cells after the queues. -/
def RR : ℕ := N.D + 3 + 4 * N.Jq + 2 * N.Jq * N.A2

/-- The address `RR + b s + k`. -/
def r (b k : ℕ) : ℕ := N.RR + b * N.s + k

/-- The end of the heap of the setup. -/
def hS : ℕ := N.r 6 16

theorem RR_eq : N.RR = N.D + pqSize N.Jq N.A2 := by
  unfold RR pqSize; ring

/-- **The end of the heap is in bound**: `hS ≤ h + 1000 (J + 1) (nS + s + L + 10)`. -/
theorem hS_le : N.hS ≤ N.h + 1000 * (N.J + 1) * (N.nS + N.s + N.L + 10) := by
  unfold hS r RR D z Z H A2 Jq
  nlinarith [Nat.zero_le (N.J * N.nS), Nat.zero_le (N.J * N.s), Nat.zero_le (N.J * N.L)]

end SuN

end MinCostFlow.LowStretch
