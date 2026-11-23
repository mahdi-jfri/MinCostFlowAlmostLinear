module

public import MinCostFlow.MinRatio.WireSelectUpdate
public import MinCostFlow.Num.ShiftLeft

/-!
# Select-heap key evaluator: definitions, relocatable module, and repaired metadata contract

Implements the key evaluator `evalKeyProc` for the min-ratio select-heap (`jtree.tex`, pages 21
and 24):
1. `evalKeyWalkLoopBody` and `evalKeyProcBody`: walks the spanner embedding `MEmbAt` of a
   candidate edge `e` at level `lvl`, evaluates `potGrad C g φ (lvl + 1) f` on `e` and every
   embedding edge `f` via `evalEdgePotGradBody`, accumulates the signed cycle gradient numerator
   `walkInner (potGrad C g φ (lvl + 1)) (sparsifierCycle lvl e)` and the core-length denominator
   `wlenAt ℓ lvl e`, and copies the two `Lk`-limb results into `nDst` and `dDst`.
2. `evalKeyModule b h`: relocatable, deterministic 12-procedure block containing `evalKeyProcBody`
   (at `b + 0`), `evalEdgePotGradBody`, `evalEdgePotGradLoopBody`, `evalKeyWalkLoopBody`,
   `copyLimbsToBody`, `Num.addModule`, and `Num.subtractModule`.
3. `SelectCoreLenInvNext`, `SelectLevelMetaAtRepaired`, `SelectLevelMetaBounded`, and
   `evalCandKeyContractRepaired`: minimal repair of `SelectCoreLenInv` (`WireSelectKeyEval.lean`)
   and `evalCandKeyContract` (`WireSelectUpdate.lean`) fixing two obstructions documented in
   `WireSelectEvalKeyProofs.lean`:
   - `SelectCoreLenInv` had `coreLen j e = C.chainLen ℓ j e` instead of `C.chainLen ℓ (j + 1) e`,
     omitting `(C.activeLSF lvl).wstr e * C.chainLen ℓ lvl e` from memory;
   - `evalCandKeyContract.pre` did not bound the metadata tables and `MEmbAt` walk buffers below
     `scratch` (and `< 2 ^ w`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Key-evaluator procedures and relocatable deterministic module -/

/-- Recursive loop walking the spanner embedding `P = C.activeEmb lvl e` stored as `MWalkAt` at
`walkPtr` (`[P.length, f_0, d_0, f_1, d_1, ...]`).
Arguments: `[meta, lvl, walkPtr, len, idx, accN, accD, tmpG, Lk, scratch]`.
In `C.sparsifierCycle lvl e = (e, true) :: walkRev P`, each embedding step `(f, dir)` is reversed:
forward (`dir = 1`) subtracts `potGrad (lvl + 1) f` from `accN`, backward (`dir = 0`) adds it.
Every step adds `coreLen[lvl][f]` to `accD`. Returns the final scratch pointer. -/
def evalKeyWalkLoopBody (self evalEdgePotGrad copyTo addProc subProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 4) (.reg 3))
    (.assign 10 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 4)))) ;;
     .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 2) (.reg 4)))) ;;
     .call 12 evalEdgePotGrad [.reg 0, .reg 1, .reg 10, .reg 7, .reg 8, .reg 9] ;;
     .cond (.reg 11)
       (.call 13 subProc [.reg 5, .reg 7, .reg 8, .reg 12] ;;
        .call 14 copyTo [.bin .add (.reg 12) (.reg 8), .reg 5, .reg 8])
       (.call 13 addProc [.reg 5, .reg 7, .reg 8, .reg 12] ;;
        .call 14 copyTo [.reg 12, .reg 5, .reg 8]) ;;
     .assign 15 (.load (.bin .add (.reg 0) (.const smDOff))) ;;
     .assign 16 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 15) (.const 1))) (.reg 1)))) ;;
     .call 17 addProc [.reg 6, .bin .add (.reg 16) (.bin .mul (.reg 10) (.reg 8)), .reg 8, .reg 13] ;;
     .call 18 copyTo [.reg 13, .reg 6, .reg 8] ;;
     .call 19 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1),
       .reg 5, .reg 6, .reg 7, .reg 8, .reg 17] ;;
     .ret (.reg 19))
    (.ret (.reg 9))

theorem evalKeyWalkLoopBody_noRand (self evalEdgePotGrad copyTo addProc subProc : ℕ) :
    (evalKeyWalkLoopBody self evalEdgePotGrad copyTo addProc subProc).NoRand := by
  simp [evalKeyWalkLoopBody, Stmt.NoRand]

/-- Entry procedure `evalKeyProcBody` (`args = [meta, lvl, e, nDst, dDst, Lk, scratch]`):
1. Allocates three `Lk`-limb scratch accumulators `accN`, `accD`, `tmpG` at `[scratch, scratch + 3 * Lk)`.
2. Initializes `accN := potGrad C g φ (lvl + 1) e` via `evalEdgePotGrad` and
   `accD := coreLen[lvl][e]` via `copyTo`.
3. If `lvl < d`, walks `C.activeEmb lvl e` via `walkLoop`, accumulating both `accN` and `accD`.
   If `lvl = d`, loads `pLast` from `smEntryAddr meta d 7 d` and shifts `accN` left by `pLast`
   bits via `shiftLeft` so both `accN` and `accD` share precision `P + pLast`.
4. Copies `accN` to `nDst` and `accD` to `dDst`, returning the final scratch pointer. -/
def evalKeyProcBody (evalEdgePotGrad walkLoop copyTo shiftLeft : ℕ) : Stmt :=
  .assign 7 (.reg 6) ;;
  .assign 8 (.bin .add (.reg 6) (.reg 5)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 5)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 5)) ;;
  .call 11 evalEdgePotGrad [.reg 0, .reg 1, .reg 2, .reg 7, .reg 5, .reg 10] ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const smDOff))) ;;
  .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
    (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 12) (.const 1))) (.reg 1)))) ;;
  .call 14 copyTo [.bin .add (.reg 13) (.bin .mul (.reg 2) (.reg 5)), .reg 8, .reg 5] ;;
  .cond (.bin .lt (.reg 1) (.reg 12))
    (.assign 15 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.bin .mul (.const 5) (.bin .add (.reg 12) (.const 1))) (.reg 1)))) ;;
     .assign 16 (.load (.bin .add (.reg 15) (.reg 2))) ;;
     .assign 17 (.load (.reg 16)) ;;
     .call 11 walkLoop [.reg 0, .reg 1, .reg 16, .reg 17, .const 0,
       .reg 7, .reg 8, .reg 9, .reg 5, .reg 11])
    (.assign 15 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.bin .mul (.const 7) (.bin .add (.reg 12) (.const 1))) (.reg 12)))) ;;
     .assign 16 (.reg 11) ;;
     .call 11 shiftLeft [.reg 7, .reg 5, .reg 15, .reg 16] ;;
     .call 17 copyTo [.reg 16, .reg 7, .reg 5]) ;;
  .call 18 copyTo [.reg 7, .reg 3, .reg 5] ;;
  .call 19 copyTo [.reg 8, .reg 4, .reg 5] ;;
  .ret (.reg 11)

theorem evalKeyProcBody_noRand (evalEdgePotGrad walkLoop copyTo shiftLeft : ℕ) :
    (evalKeyProcBody evalEdgePotGrad walkLoop copyTo shiftLeft).NoRand := by
  simp [evalKeyProcBody, Stmt.NoRand]

/-- Alias for `evalKeyProcBody`, the entry-point procedure of `evalKeyModule`. -/
abbrev evalKeyProc : ℕ → ℕ → ℕ → ℕ → Stmt := evalKeyProcBody

/-- Self-contained relocatable deterministic 14-procedure block implementing `evalKeyProc`
starting at procedure index `b` with `h`-bit limbs:
- `b + 0`: `evalKeyProcBody` (entry point)
- `b + 1`: `evalEdgePotGradBody`
- `b + 2`: `evalEdgePotGradLoopBody`
- `b + 3`: `evalKeyWalkLoopBody`
- `b + 4`: `copyLimbsToBody`
- `b + 5 .. b + 6`: `Num.addModule (b + 5) h` (length `2`)
- `b + 7 .. b + 11`: `Num.subtractModule (b + 7) h` (length `5`)
- `b + 12 .. b + 13`: `Num.shiftLeftModule (b + 12) h` (length `2`). -/
def evalKeyModule (b h : ℕ) : List Stmt :=
  [ evalKeyProcBody (b + 1) (b + 3) (b + 4) (b + 12),
    evalEdgePotGradBody (b + 2) (b + 4),
    evalEdgePotGradLoopBody (b + 2) (b + 4) (b + 5) (b + 7),
    evalKeyWalkLoopBody (b + 3) (b + 1) (b + 4) (b + 5) (b + 7),
    copyLimbsToBody ] ++
  Num.addModule (b + 5) h ++
  Num.subtractModule (b + 7) h ++
  Num.shiftLeftModule (b + 12) h

theorem evalKeyModule_length (b h : ℕ) : (evalKeyModule b h).length = 14 := by
  simp [evalKeyModule, Num.addModule, Num.subtractModule, Num.negateModule, Num.shiftLeftModule]

theorem evalKeyModule_noRand (b h : ℕ) : ∀ s ∈ evalKeyModule b h, s.NoRand := by
  intro s hs
  simp only [evalKeyModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl | rfl | rfl) | ha) | hs) | hsh
  · exact evalKeyProcBody_noRand ..
  · exact evalEdgePotGradBody_noRand ..
  · exact evalEdgePotGradLoopBody_noRand ..
  · exact evalKeyWalkLoopBody_noRand ..
  · exact copyLimbsToBody_noRand
  · exact Num.addModule_noRand _ _ _ ha
  · exact Num.subtractModule_noRand _ _ _ hs
  · exact Num.shiftLeftModule_noRand _ _ _ hsh

/-! ## 2. Exact space and step-cost bounds -/

/-- Step cost of `evalEdgePotGradLoopBody` for `rem` remaining levels (`O(rem · Lk)`). -/
def evalEdgePotGradLoopCost (rem Lk : ℕ) : ℕ :=
  rem * (130 * Lk + 240) + 20

/-- Step cost of `evalEdgePotGradBody` at level `lvl` (`O((lvl + 1) · Lk)`). -/
def evalEdgePotGradCostExact (lvl Lk : ℕ) : ℕ :=
  (lvl + 1) * (130 * Lk + 240) + 18 * Lk + 80

/-- Scratch space per embedding edge in `evalKeyWalkLoopBody`. -/
def evalKeyStepSpace (lvl Lk : ℕ) : ℕ :=
  evalEdgePotGradSpace lvl Lk + 3 * Lk

/-- Scratch space for `evalKeyWalkLoopBody` with `rem` remaining embedding edges. -/
def evalKeyWalkLoopSpace (rem lvl Lk : ℕ) : ℕ :=
  rem * evalKeyStepSpace lvl Lk

/-- Step cost per embedding edge in `evalKeyWalkLoopBody`. -/
def evalKeyStepCost (lvl Lk : ℕ) : ℕ :=
  evalEdgePotGradCostExact lvl Lk + 148 * Lk + 240

/-- Step cost for `evalKeyWalkLoopBody` with `rem` remaining embedding edges. -/
def evalKeyWalkLoopCost (rem lvl Lk : ℕ) : ℕ :=
  rem * (evalKeyStepCost lvl Lk + 40) + 20

/-- Total scratch space for `evalKeyProcBody` at level `lvl` with embedding length `embLen`. -/
def evalKeySpace (lvl embLen Lk : ℕ) : ℕ :=
  4 * Lk + evalEdgePotGradSpace lvl Lk + evalKeyWalkLoopSpace embLen lvl Lk

/-- Total step cost for `evalKeyProcBody` at level `lvl` with embedding length `embLen`. -/
def evalKeyCost (lvl embLen Lk : ℕ) : ℕ :=
  evalEdgePotGradCostExact lvl Lk + evalKeyWalkLoopCost embLen lvl Lk + 120 * Lk + 380

/-- Monotonicity of `evalKeySpace` in `lvl` and `embLen`. -/
theorem evalKeySpace_mono {lvl₁ lvl₂ emb₁ emb₂ Lk : ℕ}
    (hl : lvl₁ ≤ lvl₂) (he : emb₁ ≤ emb₂) :
    evalKeySpace lvl₁ emb₁ Lk ≤ evalKeySpace lvl₂ emb₂ Lk := by
  unfold evalKeySpace evalKeyWalkLoopSpace evalKeyStepSpace evalEdgePotGradSpace
  have h1 : (lvl₁ + 1) * (3 * Lk) ≤ (lvl₂ + 1) * (3 * Lk) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hl 1)
  have h2 : emb₁ * ((lvl₁ + 1) * (3 * Lk) + 3 * Lk) ≤
      emb₂ * ((lvl₂ + 1) * (3 * Lk) + 3 * Lk) :=
    Nat.mul_le_mul he (Nat.add_le_add_right h1 _)
  omega

/-- Monotonicity of `evalKeyCost` in `lvl` and `embLen`. -/
theorem evalKeyCost_mono {lvl₁ lvl₂ emb₁ emb₂ Lk : ℕ}
    (hl : lvl₁ ≤ lvl₂) (he : emb₁ ≤ emb₂) :
    evalKeyCost lvl₁ emb₁ Lk ≤ evalKeyCost lvl₂ emb₂ Lk := by
  unfold evalKeyCost evalKeyWalkLoopCost evalKeyStepCost evalEdgePotGradCostExact
  have h1 : (lvl₁ + 1) * (130 * Lk + 240) ≤ (lvl₂ + 1) * (130 * Lk + 240) :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hl 1)
  have hstep : (lvl₁ + 1) * (130 * Lk + 240) + 18 * Lk + 80 + 148 * Lk + 240 + 40 ≤
      (lvl₂ + 1) * (130 * Lk + 240) + 18 * Lk + 80 + 148 * Lk + 240 + 40 := by
    omega
  have h2 := Nat.mul_le_mul he hstep
  linarith

/-- Paper-form cost bound: `evalKeyCost lvl embLen Lk` is multilinear in `embLen + 1`, `lvl + 1`,
and `Lk + 1`, i.e., `O((lvl + 1) · Lk · |emb e|)` plus `O((lvl + 1) · Lk)`, hence `m^{o(1)}` per
key when `d`, `Lk`, and `|emb e|` are `m^{o(1)}`. -/
theorem evalKeyCost_paper_form (lvl embLen Lk : ℕ) :
    evalKeyCost lvl embLen Lk ≤ 600 * (embLen + 1) * (lvl + 1) * (Lk + 1) + 400 := by
  unfold evalKeyCost evalKeyWalkLoopCost evalKeyStepCost evalEdgePotGradCostExact
  have h1 : 1 ≤ lvl + 1 := Nat.succ_pos lvl
  have h2 : 166 * Lk + 360 ≤ 360 * (lvl + 1) * (Lk + 1) := by
    have hmul : 360 * (Lk + 1) ≤ 360 * (lvl + 1) * (Lk + 1) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left 360 (Nat.le_mul_of_pos_left _ h1)
    omega
  have h3 : (lvl + 1) * (130 * Lk + 240) ≤ 240 * (lvl + 1) * (Lk + 1) := by
    have : 130 * Lk + 240 ≤ 240 * (Lk + 1) := by omega
    calc (lvl + 1) * (130 * Lk + 240)
        ≤ (lvl + 1) * (240 * (Lk + 1)) := Nat.mul_le_mul_left _ this
      _ = 240 * (lvl + 1) * (Lk + 1) := by ring
  have hstep : (lvl + 1) * (130 * Lk + 240) + 18 * Lk + 80 + 148 * Lk + 240 + 40 ≤
      600 * (lvl + 1) * (Lk + 1) := by
    linarith
  have hfirst : (lvl + 1) * (130 * Lk + 240) + 18 * Lk + 80 + 120 * Lk ≤
      600 * (lvl + 1) * (Lk + 1) := by
    linarith
  have hloop : embLen * ((lvl + 1) * (130 * Lk + 240) + 18 * Lk + 80 + 148 * Lk + 240 + 40) ≤
      embLen * (600 * (lvl + 1) * (Lk + 1)) :=
    Nat.mul_le_mul_left embLen hstep
  have hcomb : 600 * (lvl + 1) * (Lk + 1) + embLen * (600 * (lvl + 1) * (Lk + 1)) =
      600 * (embLen + 1) * (lvl + 1) * (Lk + 1) := by ring
  linarith

/-- Paper-form space bound: `evalKeySpace lvl embLen Lk ≤ 4 * (embLen + 1) * (lvl + 2) * Lk`. -/
theorem evalKeySpace_paper_form (lvl embLen Lk : ℕ) :
    evalKeySpace lvl embLen Lk ≤ 4 * (embLen + 1) * (lvl + 2) * Lk := by
  unfold evalKeySpace evalKeyWalkLoopSpace evalKeyStepSpace evalEdgePotGradSpace
  have h1 : 4 * Lk + (lvl + 1) * (3 * Lk) + embLen * ((lvl + 1) * (3 * Lk) + 3 * Lk) +
      (lvl + 1) * Lk + embLen * (lvl + 2) * Lk =
      4 * (embLen + 1) * (lvl + 2) * Lk := by ring
  omega

/-! ## 3. Repaired metadata invariant and repaired key-evaluation contract -/

/-- Repaired core-length invariant: at every level `j ≤ C.d`, `coreLen j` stores the core-graph
edge lengths `ℓ^{𝒞(G_j, F_j)} = C.chainLen ℓ (j + 1)` on `(C.G j).E`.
(In `WireSelectKeyEval.lean`, `SelectCoreLenInv` stored `C.chainLen ℓ j`, which omitted the stretch
factor `(C.activeLSF lvl).wstr e` needed for `C.wlenAt ℓ lvl e`.) -/
def SelectCoreLenInvNext (C : TreeChain) (ℓ : ℕ → ℝ) (coreLen : ℕ → ℕ → ℝ) : Prop :=
  ∀ j ≤ C.d, ∀ e ∈ (C.G j).E, coreLen j e = C.chainLen ℓ (j + 1) e

/-- Repaired `SelectLevelMetaAt` using `SelectCoreLenInvNext` so `coreLenPtr lvl` stores
`C.chainLen ℓ (lvl + 1)` on `(C.G lvl).E` (covering every edge of `C.sparsifierCycle lvl e`). -/
def SelectLevelMetaAtRepaired (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h P : ℕ)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ) : Prop :=
  mloc.d = C.d ∧
  mem (mloc.metaBase + smG0Off) = mloc.g0Ptr ∧
  mem (mloc.metaBase + smDOff) = mloc.d ∧
  (∀ j ≤ C.d,
    mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 4 j) = mloc.coreLenPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 5 j) = mloc.embPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 7 j) = mloc.sPtr j) ∧
  EdgeValuesAt mem mloc.g0Ptr h mloc.Lk P (C.G 0).E g ∧
  (∀ j ≤ C.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V (φ j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.coreLenPtr j) h mloc.Lk
    (coreLenPrec C.d P mloc.pLast j) (C.G j).E (coreLen j)) ∧
  (∀ j < C.d, MEmbAt mem (mloc.embPtr j) (C.activeCore j).E (mloc.eCap j) (C.activeEmb j)) ∧
  (∀ j ≤ C.d, DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F) ∧
  (∀ j < C.d, DynGraphAt mem (mloc.sPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeS j)) ∧
  SelectPotInv C g φ ∧
  SelectCoreLenInvNext C ℓ coreLen ∧
  mloc.sPtr mloc.d = mloc.pLast

/-- Read-only slice of `SelectLevelMetaAtRepaired` actually accessed by `evalKeyProc` and
`evalEdgePotGradBody` (omitting `fPtr` and interior `sPtr`, which are only tested by
`selectProcessEdgeBody`, while keeping the terminal `pLast` word at `smEntryAddr meta d 7 d`). -/
def SelectLevelMetaReadAt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h P : ℕ)
    (C : TreeChain) (g : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ) : Prop :=
  mloc.d = C.d ∧
  mem (mloc.metaBase + smG0Off) = mloc.g0Ptr ∧
  mem (mloc.metaBase + smDOff) = mloc.d ∧
  (∀ j ≤ C.d,
    mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 4 j) = mloc.coreLenPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 5 j) = mloc.embPtr j) ∧
  EdgeValuesAt mem mloc.g0Ptr h mloc.Lk P (C.G 0).E g ∧
  (∀ j ≤ C.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V (φ j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.coreLenPtr j) h mloc.Lk
    (coreLenPrec C.d P mloc.pLast j) (C.G j).E (coreLen j)) ∧
  (∀ j < C.d, MEmbAt mem (mloc.embPtr j) (C.activeCore j).E (mloc.eCap j) (C.activeEmb j)) ∧
  mem (smEntryAddr mloc.metaBase mloc.d 7 mloc.d) = mloc.pLast

theorem SelectLevelMetaAtRepaired.toRead {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc} {h P : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hm : SelectLevelMetaAtRepaired mem mloc h P C g ℓ φ coreLen) :
    SelectLevelMetaReadAt mem mloc h P C g φ coreLen := by
  obtain ⟨h1, h2, h3, htab, h4, h5, h6, h7, h8, _, _, _, _, hpLast⟩ := hm
  refine ⟨h1, h2, h3, fun j hj =>
    let t := htab j hj
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1⟩, h4, h5, h6, h7, h8, ?_⟩
  have ht := (htab C.d le_rfl).2.2.2.2.2.2.2
  rw [← h1] at ht
  exact ht.trans hpLast

-- `SelectLevelMetaBounded` lives in `WireSelectUpdate.lean`, where `evalCandKeyContract`
-- uses it.

/-- Repaired contract for `evalKeyProc [meta, lvl, e, nDst, dDst, Lk, scratch]`: identical to
`evalCandKeyContract` (`WireSelectUpdate.lean`) except using `SelectLevelMetaAtRepaired` and
requiring `SelectLevelMetaBounded mem mloc C scratch` in `pre`. -/
def evalCandKeyContractRepaired (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl e nDst dDst scratch,
      args = [mloc.metaBase, lvl, e, nDst, dDst, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧
      lvl ≤ C.d ∧ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E ∧
      nDst + mloc.Lk ≤ dDst ∧ dDst + mloc.Lk ≤ scratch ∧
      SelectLevelMetaAtRepaired mem mloc h P C g ℓ φ coreLen ∧
      SelectLevelMetaBounded mem mloc C scratch ∧
      ZeroFrom mem scratch ∧ scratch + evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let e := args.getD 2 0
    let nDst := args.getD 3 0
    let dDst := args.getD 4 0
    let scratch := args.getD 6 0
    let Q := coreLenPrec C.d P mloc.pLast lvl
    scratch ≤ ret ∧ ret ≤ scratch + evalSpace ∧
    Num.Valid mem' nDst h mloc.Lk ∧ Num.Valid mem' dDst h mloc.Lk ∧
    (∀ j < mloc.Lk, mem' (nDst + j) < 2 ^ w) ∧ (∀ j < mloc.Lk, mem' (dDst + j) < 2 ^ w) ∧
    Num.fixVal mem' nDst h mloc.Lk Q = walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e) ∧
    Num.fixVal mem' dDst h mloc.Lk Q = C.wlenAt ℓ lvl e ∧
    0 < Num.intVal mem' dDst h mloc.Lk ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < nDst ∨ nDst + mloc.Lk ≤ a) → (a < dDst ∨ dDst + mloc.Lk ≤ a) →
      mem' a = mem a)
  cost _ _ := evalCost

end MinCostFlow.MinRatio
