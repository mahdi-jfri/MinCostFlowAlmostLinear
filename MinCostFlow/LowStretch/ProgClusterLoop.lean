module

public import MinCostFlow.LowStretch.ProgClusterOne
public import MinCostFlow.LowStretch.ProgCopy

/-!
# The loop of the regular petals: program and invariant

The loop `regP` scans the nodes `u = 0, 1, …, s - 1` once. When `u` is allowed and far
(`3Δ < 4 FD[u]`), it carves a regular petal with target `PA[u]` and range `[0, Δ/8]`
(`regPet`): it calls `petalP`, copies the settled list to `PL + PO[k]`, and writes `PO[k + 1]`,
the target `CT[k + 1]`, the center `CC[k + 1]` and the portal `PT[k]` of petal `k`.

A node that was passed and is still allowed is near, since marks only change from `os` to
`os + 1`. So at the end every allowed node is near, which is the rule for the stem.

This file has the program, the facts that each petal leaves (`PW.PetOut`) and the invariant of the
loop (`PW.LInv`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### Petals added at the end -/

namespace Cl

variable {G : PG} {c : Cl}

theorem Dec.pd_append_lt {sp : Bool} {ps : List PD} {pd : PD} {j : ℕ} (hj : j < ps.length) :
    (⟨sp, ps ++ [pd]⟩ : Dec).pd j = (⟨sp, ps⟩ : Dec).pd j := by
  simp only [Dec.pd, List.getD_append _ _ _ _ hj]

theorem Dec.pd_append_eq {sp : Bool} {ps : List PD} {pd : PD} :
    (⟨sp, ps ++ [pd]⟩ : Dec).pd ps.length = pd := by
  simp [Dec.pd]

theorem W_append {sp : Bool} {ps : List PD} {pd : PD} {j : ℕ} (hj : j < ps.length) :
    c.W G ⟨sp, ps ++ [pd]⟩ j = c.W G ⟨sp, ps⟩ j := by
  unfold W; rw [Z_append sp ps [pd] hj.le, Dec.pd_append_lt hj]

theorem Z_append_last {sp : Bool} {ps : List PD} {pd : PD} :
    c.Z G ⟨sp, ps ++ [pd]⟩ (ps.length + 1) =
      c.Z G ⟨sp, ps⟩ ps.length \ c.carve G (c.Z G ⟨sp, ps⟩ ps.length) pd := by
  simp only [Z]
  rw [Z_append sp ps [pd] le_rfl, Dec.pd_append_eq]

theorem W_append_last {sp : Bool} {ps : List PD} {pd : PD} :
    c.W G ⟨sp, ps ++ [pd]⟩ ps.length = c.carve G (c.Z G ⟨sp, ps⟩ ps.length) pd := by
  unfold W; rw [Z_append sp ps [pd] le_rfl, Dec.pd_append_eq]

end Cl

/-! ### The program -/

/-- One regular petal at node `u` (register `32`). Registers `0 … 31` hold the arguments of
`petalP` (with the stamp in `13` and the start `0` of the range in `23`), `33 … 37` the output
arrays `PL, PO, CT, CC, PT`, `38, 39` the tree arrays `PP, PA`, and `41` the number `k` of petals. -/
def regPet (bP bC : ℕ) : Stmt :=
  .seq (.call 43 bP [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
    .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18,
    .reg 19, .reg 20, .reg 21, .reg 22, .reg 23, .reg 24, .reg 25, .reg 26, .reg 27, .reg 28,
    .reg 29, .reg 30, .reg 31, .reg 32])
  (.seq (.assign 44 (.load (.bin .add (.reg 34) (.reg 41))))
  (.seq (.assign 45 (.load (.bin .add (.reg 31) (.const 1))))
  (.seq (.call 46 bC [.reg 29, .reg 45, .bin .add (.reg 33) (.reg 44)])
  (.seq (.store (.bin .add (.reg 34) (.bin .add (.reg 41) (.const 1)))
    (.bin .add (.reg 44) (.reg 45)))
  (.seq (.store (.bin .add (.reg 35) (.bin .add (.reg 41) (.const 1)))
    (.load (.bin .add (.reg 39) (.reg 32))))
  (.seq (.assign 47 (.load (.bin .add (.reg 31) (.const 3))))
  (.seq (.store (.bin .add (.reg 36) (.bin .add (.reg 41) (.const 1)))
    (.load (.bin .add (.reg 39) (.reg 47))))
  (.seq (.store (.bin .add (.reg 37) (.reg 41)) (.load (.bin .add (.reg 38) (.reg 47))))
  (.seq (.assign 41 (.bin .add (.reg 41) (.const 1)))
    (.assign 13 (.bin .add (.reg 13) (.const 1))))))))))))

/-- The test of node `u`: allowed (`OK[u] = os`) and far (`3Δ < 4 FD[u]`, with `Δ` in register
`42` and `FD` in register `40`). -/
def regCond : Expr :=
  .bin .mul (.bin .eq (.load (.bin .add (.reg 9) (.reg 32))) (.reg 10))
    (.bin .lt (.bin .mul (.const 3) (.reg 42))
      (.bin .mul (.const 4) (.load (.bin .add (.reg 40) (.reg 32)))))

/-- The body of the loop. -/
def regBody (bP bC : ℕ) : Stmt :=
  .seq (.cond regCond (regPet bP bC) .nop) (.assign 32 (.bin .add (.reg 32) (.const 1)))

/-- **The loop of the regular petals.** It returns the number of petals. -/
def regP (bP bC : ℕ) : Stmt :=
  .seq (.loop (.bin .lt (.reg 32) (.reg 30)) (regBody bP bC)) (.ret (.reg 41))

theorem regP_noRand (bP bC : ℕ) : (regP bP bC).NoRand := by
  simp [regP, regBody, regPet, Stmt.NoRand]

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {A : TA}

/-- The addresses of the outputs of the petal loop. -/
structure LA where
  PL : ℕ
  PO : ℕ
  CT : ℕ
  CC : ℕ
  PT : ℕ

/-- The output cells. -/
def Out (W : PW) (Q : LA) (x : ℕ) : Prop :=
  (Q.PL ≤ x ∧ x < Q.PL + W.s) ∨ (Q.PO ≤ x ∧ x < Q.PO + W.s + 1) ∨
    (Q.CT ≤ x ∧ x < Q.CT + W.s + 1) ∨ (Q.CC ≤ x ∧ x < Q.CC + W.s + 1) ∨
    (Q.PT ≤ x ∧ x < Q.PT + W.s)

/-- The settled list of petal `j`. -/
def nl (Q : LA) (mem : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range (mem (Q.PO + (j + 1)) - mem (Q.PO + j))).map (fun i => mem (Q.PL + mem (Q.PO + j) + i))

/-- **What petal `j` of `D` leaves**: its settled list holds the nodes of the petal once each,
its target, center and portal are written, and its highway splits along the path of parents of
its target in the memory `M0` at the start of the loop. -/
def PetOut (W : PW) (A : TA) (Q : LA) (M0 mem : ℕ → ℕ) (D : Cl.Dec) (j : ℕ) : Prop :=
  (nl Q mem j).Nodup ∧ (∀ v, v ∈ nl Q mem j ↔ ∃ x ∈ W.c.W W.G D j, W.sv x = v) ∧
  mem (Q.CT + (j + 1)) = (D.pd j).tj ∧ mem (Q.CC + (j + 1)) = D.xc W.G j ∧
  mem (Q.PT + j) = D.portal j ∧
  ∃ n m, W.Path M0 (W.sv (D.pd j).tj) n ∧ (D.pd j).tj ∈ W.c.X ∧
    W.c.HwDec W.G (D.pd j).tj (W.stp A M0 (W.sv (D.pd j).tj) n) (D.pd j).hw ∧ m < n ∧
    (D.pd j).hw.getD (D.pd j).i 0 = M0 (A.PP + W.pe M0 (W.sv (D.pd j).tj) m) ∧
    hv W.G (D.pd j).tj (D.pd j).hw (D.pd j).i = M0 (A.PA + W.pe M0 (W.sv (D.pd j).tj) m) ∧
    hv W.G (D.pd j).tj (D.pd j).hw ((D.pd j).i + 1) = M0 (A.PB + W.pe M0 (W.sv (D.pd j).tj) m)

/-- The values of the fixed registers of the loop. -/
def LReg (W : PW) (A : TA) (Q : LA) (Δ : ℕ) : List ℕ :=
  [W.L.D, W.L.J, W.L.A, W.L.INF, W.L.LO, W.L.HI, W.L.HD, W.L.CS, W.L.CL, W.L.OK, W.L.os, W.L.TS,
    W.L.NN, 0, W.RR, W.ORD, W.AS, W.EXP, W.Es, W.SUM, W.M, W.κ, W.nact, 0, W.bw, W.Lb, W.SQ,
    W.P2, W.NXT, W.SL, W.s, W.CTL, 0, Q.PL, Q.PO, Q.CT, Q.CC, Q.PT, A.PP, A.PA, A.FD, 0, Δ]

/-- The ghost state of the loop: the node `u`, the stamp `rs`, the petals so far, and the
potential `φ`. -/
structure LG where
  u : ℕ
  rs : ℕ
  ps : List PD
  φ : ℕ

/-- **The invariant of the loop**, for a cluster whose decomposition step has the flag `sp`, with
`k0` petals before the loop and the memory `M0` at its start. -/
structure LInv (W : PW) (A : TA) (Q : LA) (sp : Bool) (k0 : ℕ) (M0 : ℕ → ℕ) (w : ℕ) (a : LG)
    (st : State) : Prop where
  regs : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 → st.regs i = (W.LReg A Q (W.c.Δ W.G)).getD i 0
  r13 : st.regs 13 = a.rs
  r32 : st.regs 32 = a.u
  r41 : st.regs 41 = a.ps.length
  k0le : k0 ≤ a.ps.length
  btw : W.Btw w st.mem a.rs
  tree : W.Tree A st.mem
  cone : W.Cone st.mem
  φ : W.Φ st.mem = a.φ
  Y : W.Y st.mem = W.c.Z W.G ⟨sp, a.ps⟩ a.ps.length
  safe : ∀ x, W.Safe x → ¬ W.Out Q x → st.mem x = M0 x
  low : ∀ x, x < W.L.TS → (x < W.L.HD ∨ W.L.HD + W.L.MM ≤ x) →
    ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.s) → st.mem x = M0 x
  scan : ∀ v < a.u, v < W.s → st.mem (W.L.OK + v) = W.L.os →
    4 * st.mem (A.FD + v) ≤ 3 * W.c.Δ W.G
  reg : ∀ j, k0 ≤ j → j < a.ps.length →
    3 * W.c.Δ W.G < 4 * W.c.d W.G W.c.x0 ((⟨sp, a.ps⟩ : Cl.Dec).pd j).tj ∧
    W.c.PetalOk W.G W.P (W.c.Z W.G ⟨sp, a.ps⟩ j) 0 ((⟨sp, a.ps⟩ : Cl.Dec).pd j)
  po : ∀ j < a.ps.length, st.mem (Q.PO + j) ≤ st.mem (Q.PO + (j + 1))
  out : ∀ j < a.ps.length, W.PetOut A Q M0 st.mem ⟨sp, a.ps⟩ j
  room : st.mem (Q.PO + a.ps.length) + (W.Nodes st.mem).card ≤ W.s
  kle : a.ps.length + (W.Nodes st.mem).card ≤ W.s
  ule : a.u ≤ W.s
  rsw : a.rs + (W.s - a.u) < 2 ^ w

end PW

end MinCostFlow.LowStretch
