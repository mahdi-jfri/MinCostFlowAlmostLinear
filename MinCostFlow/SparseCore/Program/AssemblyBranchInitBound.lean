module

public import MinCostFlow.SparseCore.Program.AssemblyBranchInitModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepCost
public import MinCostFlow.SparseCore.Program.ReadMain

/-!
# Bounds for the init of a branch (`AssemblyBranchInitBound`)

The init of a branch (`asmBrInitStmt`, `AssemblyBranchInitIface.lean`) makes two calls: the first
phase (`AsmBrCoreInitAt`) and the init of the readout data of P10 (`ReadBranchAt.init`). This file
holds what the proof of the init (`AssemblyBranchInit.lean`) needs besides the two calls:
* `AsmBrReadAt`: P10 at every caps that meet its word condition. `asmBrReadAt_of_hasReadProcs`
  proves it from P10's procedures (`readBranchAt_readRep`).
* `exportAt_mono`: an export that ends by `h` also ends by every `h' ≥ h`. P4's export of the
  branch ends below the heap pointer of the first phase, and P10's init reads it there.
* `asmBrInitPoly` and `asmBrInit_space_le`: the space of the first phase and of P10's init is at
  most a polynomial of degree `JP.deg + 3`, for the polynomial `JP` of the first phase. P10's init
  allocates `readMul (vCap + tCap + size + 1) (L_w + 1)` cells. Here `tCap ≤ 2 (vCap + eCap + 2) ²`
  and `size ≤ 4 vCap + 4 eCap`, so the first factor is at most `5 B ²` with `B` the argument of the
  polynomial plus `2`, and the limb bound gives `L_w + 1 ≤ (capExp + 129) B`.
* `asmBrInitMul`, `initMachCost_ge` and `asmBrInit_cost_le`: the cost of the init is at most
  `asmBrInitMul` times the machine cost of the model. The machine cost of the init of the model is
  at least `(3 m + 2) lg ²`, where `lg = log₂ (M + N + 2) + 1`. P10's init costs
  `readMul (size + 1) (L_w + 1)`, with `size + 1 ≤ 8 m + 5` and `L_w + 1 ≤ K lg ²`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## P10 at every caps -/

/-- **P10 at the caps of a branch.** The readout data of P10 (`readRep`) meet `ReadBranchAt` at
every caps `vCap`, `eCap`, `tCap` and limb count `L_w` that meet P10's word condition, for all
spanner parameters `SP` below the caps and every root query `Q k` of P4. P10's procedures give it
(`asmBrReadAt_of_hasReadProcs`). -/
def AsmBrReadAt (w P : ℕ) (p : Program) (bRead : ℕ) (readIdx : ℕ → ℕ) (fRoot : ℕ)
    (Q : ℕ → RootQueryAt w p fRoot) (readMul : ℕ) : Prop :=
  ∀ (k vCap eCap tCap L_w : ℕ) (SP : DSParams) (cap : ℕ),
    SP.w = w → SP.eCap ≤ eCap → eCap ≤ tCap → 1 ≤ L_w →
    (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w →
    ReadBranchAt (readRep vCap eCap tCap L_w P) w vCap eCap tCap L_w P SP cap p bRead readIdx
      fRoot (Q k) readMul

/-- P10's procedures give `AsmBrReadAt` (`readBranchAt_readRep`). -/
theorem asmBrReadAt_of_hasReadProcs {w P : ℕ} {p : Program} {bRead fRoot : ℕ}
    {Q : ℕ → RootQueryAt w p fRoot} (hp : HasReadProcs p bRead fRoot) :
    AsmBrReadAt w P p bRead readBranchIdx13 fRoot Q readBranchMul :=
  fun _ _ _ _ _ _ _ hw he het hL hword => readBranchAt_readRep hp hw he het hL hword

/-! ## Exports -/

/-- An export that ends by `h` also ends by every `h' ≥ h`. -/
theorem exportAt_mono {mem : ℕ → ℕ} {d h h' : ℕ} {G : MGraph} (hE : ExportAt mem d h G)
    (hh : h ≤ h') : ExportAt mem d h' G := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hE
  exact ⟨h0, h1, h2, h3, h4, h5, h6, by omega, h8, h9, by omega, by omega⟩

/-! ## Space -/

/-- **The space of the init of a branch**: a polynomial of degree `JP.deg + 3`, from the
polynomial `JP` of the first phase, P10's factor `readMul` and `capExp`. -/
def asmBrInitPoly (JP : PolyBound) (readMul capExp : ℕ) : PolyBound where
  coeff := JP.coeff + 5 * readMul * (capExp + sparseCoreReadout2LimbConst + 1)
  deg := JP.deg + 3

/-- `log₂ n + 1 ≤ n` for `n ≥ 1`. -/
private theorem log_succ_le {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n + 1 ≤ n := by
  have := Nat.log_lt_self 2 (show n ≠ 0 by omega)
  omega

/-- The limb count of a branch is at most `(capExp + 129) B` for `B` above `L` and `M + N + 2`. -/
theorem limbs_succ_le_B {L_w L M N capExp B : ℕ} (hLB : L + 1 ≤ B) (hMB : M + N + 2 ≤ B)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    L_w + 1 ≤ (capExp + sparseCoreReadout2LimbConst + 1) * B := by
  have hlog : Nat.log 2 (M + N + 2) + 1 ≤ B := (log_succ_le (by omega)).trans hMB
  have h1 : (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ≤
      (capExp + sparseCoreReadout2LimbConst) * B := Nat.mul_le_mul_left _ hlog
  have e : (capExp + sparseCoreReadout2LimbConst + 1) * B =
      (capExp + sparseCoreReadout2LimbConst) * B + B := by ring
  omega

/-- **The space of the init is at most `asmBrInitPoly`.** The first phase allocates at most
`JP.eval X` cells and P10's init at most `readSpace readMul vCap tCap L_w size` cells, where
`X = M + N + k + vCap + eCap + L + depth`. -/
theorem asmBrInit_space_le (JP : PolyBound) (readMul : ℕ)
    {M N k vCap eCap L depth capExp tCap L_w size : ℕ}
    (htc : tCap ≤ 2 * (vCap + eCap + 2) ^ 2)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    (hsz : size ≤ 4 * vCap + 4 * eCap) :
    JP.eval (M + N + k + vCap + eCap + L + depth) + readSpace readMul vCap tCap L_w size ≤
      (asmBrInitPoly JP readMul capExp).eval (M + N + k + vCap + eCap + L + depth) := by
  set B := M + N + k + vCap + eCap + L + depth + 2 with hBdef
  set d := JP.deg
  set K := capExp + sparseCoreReadout2LimbConst + 1
  have hB : 2 ≤ B := by omega
  have hBpos : 0 < B := by omega
  have hpw : ∀ {a b : ℕ}, a ≤ b → B ^ a ≤ B ^ b := fun h => Nat.pow_le_pow_right hBpos h
  have hval : (asmBrInitPoly JP readMul capExp).eval (M + N + k + vCap + eCap + L + depth) =
      (JP.coeff + 5 * readMul * K) * B ^ (d + 3) := rfl
  have hJ : JP.eval (M + N + k + vCap + eCap + L + depth) = JP.coeff * B ^ d := rfl
  rw [hval, hJ]
  have hT1 : JP.coeff * B ^ d ≤ JP.coeff * B ^ (d + 3) := Nat.mul_le_mul_left _ (hpw (by omega))
  have hVB : vCap + eCap + 2 ≤ B := by omega
  have htB : tCap ≤ 2 * B ^ 2 :=
    htc.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hVB 2))
  have hB2 : 2 * B ≤ B ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right B hB
  have hX : vCap + tCap + size + 1 ≤ 5 * B ^ 2 := by omega
  have hLw1 : L_w + 1 ≤ K * B := limbs_succ_le_B (by omega) (by omega) hLw
  have hT2 : readSpace readMul vCap tCap L_w size ≤ 5 * readMul * K * B ^ (d + 3) := by
    unfold readSpace
    calc readMul * (vCap + tCap + size + 1) * (L_w + 1)
        ≤ readMul * (5 * B ^ 2) * (K * B) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) hLw1
      _ = 5 * readMul * K * B ^ 3 := by ring
      _ ≤ 5 * readMul * K * B ^ (d + 3) := Nat.mul_le_mul_left _ (hpw (by omega))
  have e : (JP.coeff + 5 * readMul * K) * B ^ (d + 3) =
      JP.coeff * B ^ (d + 3) + 5 * readMul * K * B ^ (d + 3) := by ring
  omega

/-- The polynomial of the first phase is below `asmBrInitPoly` at every argument. -/
theorem polyBound_le_asmBrInitPoly (JP : PolyBound) (readMul capExp x : ℕ) :
    JP.eval x ≤ (asmBrInitPoly JP readMul capExp).eval x := by
  show JP.coeff * (x + 2) ^ JP.deg ≤
    (JP.coeff + 5 * readMul * (capExp + sparseCoreReadout2LimbConst + 1)) * (x + 2) ^ (JP.deg + 3)
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-! ## Cost -/

/-- **The cost factor of the init of a branch**: the factor `jMul` of the first phase, three times
P10's factor `readMul` times the limb factor, and `120` for the steps of the program. -/
def asmBrInitMul (jMul readMul capExp limbMul : ℕ) : ℕ :=
  jMul + 3 * readMul * (limbMul + capExp + sparseCoreReadout2LimbConst + 1) + 120

/-- The machine cost of the init of a branch in the model is at least `(3 m + 2) lg ²`. -/
theorem initMachCost_ge {depth : ℕ} (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    (3 * G.m + 2) * bundleLogFactor M N ≤
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord
        j).machCost :=
  Nat.mul_le_mul_right _ (by omega)

/-- **The cost of the init is at most `asmBrInitMul` times the machine cost.** The first phase
costs at most `jMul · machCost`, P10's init at most `readMul (size + 1) (L_w + 1)`, and the program
`120` steps. -/
theorem asmBrInit_cost_le {jMul readMul capExp limbMul L M N L_w size n m machCost : ℕ}
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    (hsz : size ≤ 4 * n + 4 * m) (hnm : n ≤ m + 1)
    (hmc : (3 * m + 2) * bundleLogFactor M N ≤ machCost) :
    jMul * machCost + readMul * (size + 1) * (L_w + 1) + 120 ≤
      asmBrInitMul jMul readMul capExp limbMul * machCost := by
  set K := limbMul + capExp + sparseCoreReadout2LimbConst + 1
  set lg := bundleLogFactor M N
  have hLw1 : L_w + 1 ≤ K * lg := limbs_succ_le hL hLw
  have hlg : 1 ≤ lg := Nat.one_le_pow _ _ (by omega)
  have hsz1 : size + 1 ≤ 3 * (3 * m + 2) := by omega
  have hR : readMul * (size + 1) * (L_w + 1) ≤ 3 * readMul * K * machCost :=
    calc readMul * (size + 1) * (L_w + 1)
        ≤ readMul * (3 * (3 * m + 2)) * (K * lg) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hsz1) hLw1
      _ = 3 * readMul * K * ((3 * m + 2) * lg) := by ring
      _ ≤ 3 * readMul * K * machCost := Nat.mul_le_mul_left _ hmc
  have hmc1 : 1 ≤ machCost := le_trans (Nat.mul_pos (by omega) hlg) hmc
  have e : asmBrInitMul jMul readMul capExp limbMul * machCost =
      jMul * machCost + 3 * readMul * K * machCost + 120 * machCost := by
    unfold asmBrInitMul; ring
  omega

end MinCostFlow.SparseCore.Program
