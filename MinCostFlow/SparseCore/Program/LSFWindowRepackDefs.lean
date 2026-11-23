module

public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.LSF.Program.Utils
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sparse Host-Repack Procedures for Guest `LSFRep` Handles (`LSFWindowRepackDefs`)

Defines the deterministic Word-RAM procedures that sparsely repack a guest `(LSFRep h).rep` handle
living at host address `guestBase + h_g` (with guest capacities `vCap_g, eCap_g, L_w_g`) into fresh
zeroed host memory starting at `dst` with host capacities `(vCap_h, eCap_h, L_w_h)` satisfying
`vCap_g ≤ vCap_h`, `eCap_g ≤ eCap_h`, `L_w_g ≤ L_w_h`:

* `repackDynGraphProc`: sparse `O(H.n + H.m + 1)` copy of any `DynGraphAt` into larger capacities.
* `repackTBlockProc`: sparse `O(n₀ + 1)` copy of `TBlockAt` (rebuilding `tIdxOfEdgeBase` for
  `eCap_h`).
* `repackFAncProc`: sparse `O(n₀ + 1)` copy of `FAncAt`.
* `repackWBlockProc`: `O(n₀ + 1)` copy of `WBlockAt` (recomputing its 4 header pointers).
* `repackWstrProc`: sparse `O(m₀ * L_w_g + 1)` copy of `WstrAt` (zero-extending `L_w_g → L_w_h`).
* `repackAuxProc`: sparse `O(n₀ * auxLogCap n₀ + 1)` copy of `AuxAt`.
* `repackOneLSFProc`: writes the 24-word host header, calls all six sub-block repackers, and
  returns `dstEnd = lsfEndAddr dst vCap_h eCap_h n₀ tM L_w_h`.

Total cost per handle is `O(n₀ * auxLogCap n₀ + m₀ * L_w_g + 1)`, completely independent of
`vCap_h`, `eCap_h`, and `L_w_h`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## Zero-extension lemma for positive signed fixed-point limbs -/

lemma unsignedVal_zero_extend {mem : ℕ → ℕ} {a h L₁ L₂ : ℕ} (hL : L₁ ≤ L₂)
    (hz : ∀ i, L₁ ≤ i → i < L₂ → mem (a + i) = 0) :
    unsignedVal mem a h L₂ = unsignedVal mem a h L₁ := by
  induction L₁ generalizing a L₂ with
  | zero =>
    simp only [unsignedVal]
    exact unsignedVal_zero fun i hi => hz i (Nat.zero_le _) hi
  | succ L₁ ih =>
    cases L₂ with
    | zero => omega
    | succ L₂ =>
      simp only [unsignedVal]
      congr 2
      exact ih (by omega) fun i h1 h2 => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hz (i + 1) (by omega) (by omega)

lemma intVal_zero_extend_pos {mem : ℕ → ℕ} {a h L₁ L₂ : ℕ}
    (_hh : 1 ≤ h) (hL : L₁ ≤ L₂)
    (hv : Valid mem a h L₁) (hpos : 1 ≤ intVal mem a h L₁)
    (hz : ∀ i, L₁ ≤ i → i < L₂ → mem (a + i) = 0) :
    Valid mem a h L₂ ∧ intVal mem a h L₂ = intVal mem a h L₁ := by
  have hv₂ : Valid mem a h L₂ := fun i hi => by
    by_cases hlt : i < L₁
    · exact hv i hlt
    · rw [hz i (Nat.le_of_not_lt hlt) hi]; exact base_pos h
  have hu_eq : unsignedVal mem a h L₂ = unsignedVal mem a h L₁ :=
    unsignedVal_zero_extend hL hz
  have hu_lt := unsignedVal_lt hv
  have hnot_neg₁ : ¬ capacity h L₁ ≤ 2 * unsignedVal mem a h L₁ := by
    intro hge
    unfold intVal signedVal at hpos
    rw [ite_eq_left hge] at hpos
    omega
  have hcap_le : capacity h L₁ ≤ capacity h L₂ := by
    rw [Num.capacity_eq_two_pow, Num.capacity_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left h hL)
  have hnot_neg₂ : ¬ capacity h L₂ ≤ 2 * unsignedVal mem a h L₂ := by
    rw [hu_eq]; omega
  refine ⟨hv₂, ?_⟩
  unfold intVal signedVal
  rw [ite_eq_right hnot_neg₂, ite_eq_right hnot_neg₁, hu_eq]

/-- Direct-body sequential call helper (for internal procedures verified via `Runs`). -/
lemma runs_seq_call_body_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body s : Stmt} {st : State} {vs : List ℕ} {k T c1_max : ℕ}
    {P_call : ℕ → State → Prop} {Q : Outcome → State → Prop}
    (hp : p.procs[f]? = some body)
    (hargs : evalArgs w st args = some vs)
    (hbody : ∃ ret st1 c1, Runs w p ω body (startState vs st.mem st.pos) (.returned ret) st1 c1 ∧
      P_call ret st1 ∧ c1 ≤ c1_max)
    (hrest : ∀ ret st1, P_call ret st1 →
      ∃ o st' c2, Runs w p ω s { st1 with regs := Function.update st.regs r ret } o st' c2 ∧
        Q o st' ∧ (k + argsSize args + c1_max + 2) + c2 ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hbody with ⟨ret, st1, c1, hr1, hP1, hc1⟩
  rcases hrest ret st1 hP1 with ⟨o, st', c2, hr2, hq, hc2⟩
  refine ⟨o, st', (argsSize args + c1 + 1) + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨{ st1 with regs := Function.update st.regs r ret },
      argsSize args + c1 + 1, c2,
      runs_call_iff.mpr ⟨vs, body, .returned ret, st1, c1, hargs, hp, hr1, rfl, rfl, rfl⟩,
      hr2, rfl⟩),
    hq, by omega⟩

/-- Flat sequential assignment helper keeping `State.mk` explicit (avoids exponential term blowup
when chaining many `assign`/`store` statements). -/
lemma runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {s₂ : Stmt}
    {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {Q : Outcome → State → Prop} {acc B v : ℕ}
    (he : e.eval w ⟨m, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨m, Function.update regs r v, pos⟩ o st' c ∧
      Q o st' ∧ acc + e.size + 2 + c ≤ B) :
    ∃ o st' c, Runs w p ω (.assign r e ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_assign_le he h₂

/-- Flat sequential store helper keeping `State.mk` explicit. -/
lemma runs_seq_store_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {s₂ : Stmt}
    {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {Q : Outcome → State → Prop} {acc B x v : ℕ}
    (ha : a.eval w ⟨m, regs, pos⟩ = some x) (he : e.eval w ⟨m, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨Function.update m x v, regs, pos⟩ o st' c ∧
      Q o st' ∧ acc + a.size + e.size + 2 + c ≤ B) :
    ∃ o st' c, Runs w p ω (.store a e ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_store_le ha he h₂

/-- Flat sequential contract-call helper keeping `State.mk` explicit. -/
lemma runs_seq_call_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s₂ : Stmt} {C : Contract} {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ}
    {Q : Outcome → State → Prop} {acc B : ℕ}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w ⟨m, regs, pos⟩ args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w) (hpre : C.pre vs m)
    (h₂ : ∀ ret m' pos', C.post vs m ret m' →
      ∃ o st' c, Runs w p ω s₂ ⟨m', Function.update regs r ret, pos'⟩ o st' c ∧
        Q o st' ∧ acc + argsSize args + C.cost vs m + 2 + c ≤ B) :
    ∃ o st' c, Runs w p ω (.call r f args ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_call_le hf hargs hwords hpre h₂

/-- Flat sequential direct-body call helper keeping `State.mk` explicit. -/
lemma runs_seq_call_body_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body s₂ : Stmt} {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ} {acc B c1_max : ℕ}
    {P_call : ℕ → State → Prop} {Q : Outcome → State → Prop}
    (hp : p.procs[f]? = some body)
    (hargs : evalArgs w ⟨m, regs, pos⟩ args = some vs)
    (hbody : ∃ ret st1 c1, Runs w p ω body (startState vs m pos) (.returned ret) st1 c1 ∧
      P_call ret st1 ∧ c1 ≤ c1_max)
    (hrest : ∀ ret st1, P_call ret st1 →
      ∃ o st' c2, Runs w p ω s₂ ⟨st1.mem, Function.update regs r ret, st1.pos⟩ o st' c2 ∧
        Q o st' ∧ (acc + argsSize args + c1_max + 2) + c2 ≤ B) :
    ∃ o st' c, Runs w p ω (.call r f args ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_call_body_le hp hargs hbody hrest

/-! ## Sub-block sparse-repack procedures -/

/-- Sparse copy of `DynGraphAt mem src vCap_s eCap_s H` into fresh zeroed memory at `dst` with
capacities `(vCap_d, eCap_d)`. Args: `[src, dst, vCap_d, eCap_d]`. Returns `0`. -/
def repackDynGraphProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .store (.bin .add (.reg 1) (.const dgVCapOff)) (.reg 2) ;;
  .store (.bin .add (.reg 1) (.const dgECapOff)) (.reg 3) ;;
  .store (.bin .add (.reg 1) (.const dgNOff)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const dgMOff)) (.reg 7) ;;
  -- Vertex pass: i = 0 .. n_H - 1
  .assign 8 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 4)) ;;
  .assign 9 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 4))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 4))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 4))) ;;
  forRange 12 (.const 0) (.reg 6)
    (.assign 13 (.load (.bin .add (.reg 8) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
     .store (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 13)) (.const 1) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 2)) (.reg 12)) (.reg 13) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 2) (.reg 2))) (.reg 13)) (.reg 12) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 3) (.reg 2))) (.reg 13)) (.reg 14) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 4) (.reg 2))) (.reg 14)) (.reg 13) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 5) (.reg 2))) (.reg 14))
       (.load (.bin .add (.reg 10) (.reg 14))) ;;
     .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 6) (.reg 2))) (.reg 14))
       (.load (.bin .add (.reg 11) (.reg 14)))) ;;
  -- Edge pass: i = 0 .. m_H - 1
  .assign 8 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 4))) ;;
  .assign 9 (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 7) (.reg 2))) ;;
  forRange 12 (.const 0) (.reg 7)
    (.assign 13 (.load (.bin .add (.bin .add (.reg 8) (.reg 5)) (.reg 12))) ;;
     .store (.bin .add (.reg 9) (.reg 13)) (.const 1) ;;
     .store (.bin .add (.bin .add (.reg 9) (.reg 3)) (.reg 12)) (.reg 13) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 3))) (.reg 13)) (.reg 12) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 3) (.reg 3))) (.reg 13))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 5))) (.reg 13))) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 3))) (.reg 13))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 5))) (.reg 13))) ;;
     .assign 14 (.bin .mul (.const 2) (.reg 13)) ;;
     .assign 15 (.bin .add (.reg 14) (.const 1)) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 3))) (.reg 14))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 5) (.reg 5))) (.reg 14))) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 3))) (.reg 15))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 5) (.reg 5))) (.reg 15))) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 7) (.reg 3))) (.reg 14))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 7) (.reg 5))) (.reg 14))) ;;
     .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 7) (.reg 3))) (.reg 15))
       (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 7) (.reg 5))) (.reg 15)))) ;;
  .ret (.const 0)

/-- Sparse copy of `TBlockAt` from guest block at host address `srcT` (with internal pointers
relative to `guestBase`) to fresh zeroed `dstT` with host capacities `(vCap_h, eCap_h)`.
Args: `[srcT, dstT, vCap_h, eCap_h, guestBase]`. Returns `0`. -/
def repackTBlockProc (bCopy bRepDg : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const tOffM))) ;;
  .assign 6 (.bin .add (.reg 1) (.const tHdrSize)) ;;
  .assign 7 (.bin .add (.bin .mul (.const 2) (.reg 5)) (.const 1)) ;;
  .assign 8 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 4)) (.bin .mul (.const 7) (.reg 2)))
    (.bin .mul (.const 9) (.reg 7))) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 5)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 5)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 3)) ;;
  .store (.bin .add (.reg 1) (.const tOffM)) (.reg 5) ;;
  .store (.bin .add (.reg 1) (.const tOffDgTPtr)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const tOffOrigIdPtr)) (.reg 8) ;;
  .store (.bin .add (.reg 1) (.const tOffPiPtr)) (.reg 9) ;;
  .store (.bin .add (.reg 1) (.const tOffFrozenTailPtr)) (.reg 10) ;;
  .store (.bin .add (.reg 1) (.const tOffFrozenHeadPtr)) (.reg 11) ;;
  .store (.bin .add (.reg 1) (.const tOffIdxOfEdgePtr)) (.reg 12) ;;
  .store (.bin .add (.reg 1) (.const tOffSplitScratchPtr)) (.reg 13) ;;
  .call 14 bRepDg
    [.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const tOffDgTPtr))), .reg 6, .reg 2, .reg 7] ;;
  .assign 15 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const tOffOrigIdPtr)))) ;;
  .call 14 bCopy [.reg 8, .reg 15, .reg 5] ;;
  .call 14 bCopy [.reg 9, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const tOffPiPtr))), .reg 5] ;;
  .call 14 bCopy [.reg 10, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const tOffFrozenTailPtr))), .reg 5] ;;
  .call 14 bCopy [.reg 11, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const tOffFrozenHeadPtr))), .reg 5] ;;
  forRange 16 (.const 0) (.reg 5)
    (.assign 17 (.load (.bin .add (.reg 15) (.reg 16))) ;;
     .cond (.bin .lt (.reg 17) (.reg 3))
       (.store (.bin .add (.reg 12) (.reg 17)) (.bin .add (.reg 16) (.const 1)))
       .nop) ;;
  .ret (.const 0)

/-- Sparse copy of `FAncAt` from guest block at host address `srcFAnc` (internal pointers relative
to `guestBase`, using `srcDgF`'s vertex list of size `n0`) to fresh zeroed `dstFAnc` with host
`vCap_h`. Args: `[srcFAnc, srcDgF, dstFAnc, vCap_h, guestBase]`. Returns `0`. -/
def repackFAncProc (bCopy : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const fOffRCount))) ;;
  .assign 6 (.bin .add (.reg 2) (.const fAncHdrSize)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 3)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 3)) ;;
  .store (.bin .add (.reg 2) (.const fOffRCount)) (.reg 5) ;;
  .store (.bin .add (.reg 2) (.const fOffIsRootPtr)) (.reg 6) ;;
  .store (.bin .add (.reg 2) (.const fOffRListPtr)) (.reg 7) ;;
  .store (.bin .add (.reg 2) (.const fOffCompIdPtr)) (.reg 8) ;;
  .store (.bin .add (.reg 2) (.const fOffCompRootPtr)) (.reg 9) ;;
  .store (.bin .add (.reg 2) (.const fOffCompSizePtr)) (.reg 10) ;;
  .assign 11 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const fOffRListPtr)))) ;;
  .assign 12 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const fOffCompIdPtr)))) ;;
  .assign 13 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const fOffCompRootPtr)))) ;;
  .assign 14 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const fOffCompSizePtr)))) ;;
  .call 15 bCopy [.reg 7, .reg 11, .reg 5] ;;
  forRange 16 (.const 0) (.reg 5)
    (.assign 17 (.load (.bin .add (.reg 11) (.reg 16))) ;;
     .store (.bin .add (.reg 6) (.reg 17)) (.const 1) ;;
     .store (.bin .add (.reg 9) (.reg 17)) (.load (.bin .add (.reg 13) (.reg 17))) ;;
     .store (.bin .add (.reg 10) (.reg 17)) (.load (.bin .add (.reg 14) (.reg 17)))) ;;
  .assign 15 (.load (.bin .add (.reg 1) (.const dgVCapOff))) ;;
  .assign 16 (.load (.bin .add (.reg 1) (.const dgNOff))) ;;
  .assign 17 (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 15)) ;;
  forRange 18 (.const 0) (.reg 16)
    (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
     .store (.bin .add (.reg 8) (.reg 19)) (.load (.bin .add (.reg 12) (.reg 19)))) ;;
  .ret (.const 0)

/-- Copy of `WBlockAt` from `srcW` to fresh zeroed `dstW` (size `wBlockSize n0`).
Args: `[srcW, dstW, n0]`. Returns `0`. -/
def repackWBlockProc (bCopy : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 1) (.const wHdrSize)) ;;
  .assign 4 (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 2))) ;;
  .assign 6 (.bin .add (.reg 5) (.bin .add (.reg 2) (.const 1))) ;;
  .store (.bin .add (.reg 1) (.const wOffNumPieces)) (.load (.bin .add (.reg 0) (.const wOffNumPieces))) ;;
  .store (.bin .add (.reg 1) (.const wOffVertOffPtr)) (.reg 3) ;;
  .store (.bin .add (.reg 1) (.const wOffVertsPtr)) (.reg 4) ;;
  .store (.bin .add (.reg 1) (.const wOffEdgeOffPtr)) (.reg 5) ;;
  .store (.bin .add (.reg 1) (.const wOffEdgesPtr)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const wOffTotalVerts)) (.load (.bin .add (.reg 0) (.const wOffTotalVerts))) ;;
  .store (.bin .add (.reg 1) (.const wOffTotalEdges)) (.load (.bin .add (.reg 0) (.const wOffTotalEdges))) ;;
  .call 7 bCopy
    [.reg 3, .bin .add (.reg 0) (.const wHdrSize),
     .bin .add (.bin .mul (.const 5) (.reg 2)) (.const 2)] ;;
  .ret (.const 0)

/-- Sparse copy of `WstrAt` over active edges of `srcDgG`, zero-extending `L_w_g → L_w_h`.
Args: `[srcDgG, srcNum, srcDen, L_w_g, dstNum, dstDen, L_w_h]`. Returns `0`. -/
def repackWstrProc (bCopy : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const dgVCapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 7))) (.reg 8)) ;;
  forRange 11 (.const 0) (.reg 9)
    (.assign 12 (.load (.bin .add (.reg 10) (.reg 11))) ;;
     .call 13 bCopy
       [.bin .add (.reg 4) (.bin .mul (.reg 12) (.reg 6)),
        .bin .add (.reg 1) (.bin .mul (.reg 12) (.reg 3)),
        .reg 3] ;;
     .call 13 bCopy
       [.bin .add (.reg 5) (.bin .mul (.reg 12) (.reg 6)),
        .bin .add (.reg 2) (.bin .mul (.reg 12) (.reg 3)),
        .reg 3]) ;;
  .ret (.const 0)

/-- Sparse copy of `AuxAt` from guest block at host address `srcAux` (internal pointers relative
to `guestBase`) to fresh zeroed `dstAux` with host `vCap_h` (using `hldDepthBound n0` computed via
`bLog` for the stack offset). Args: `[srcAux, dstAux, vCap_h, n0, guestBase]`. Returns `0`. -/
def repackAuxProc (bCopy bLog : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const auxOffLogCap))) ;;
  .assign 6 (.bin .add (.reg 1) (.const auxHdrSize)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 2)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 3)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 3)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 3)) ;;
  .assign 12 (.bin .mul (.reg 3) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 11) (.reg 12)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 12)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 3)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 2)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 2)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 2)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 2)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 2)) ;;
  .assign 21 (.bin .add (.reg 20) (.reg 2)) ;;
  -- Compute hldDepthBound n0 + 2 = (Nat.log 2 n0 + 1) * (Nat.log 2 n0 + 2) + 2 for auxFSplitScratchBase
  .call 22 bLog [.reg 3] ;;
  .assign 23 (.bin .add (.reg 22) (.const 1)) ;;
  .assign 24 (.bin .add (.bin .mul (.reg 23) (.bin .add (.reg 23) (.const 1))) (.const 2)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 24)) ;;
  -- Store 20-word header
  .store (.bin .add (.reg 1) (.const auxOffVIdxPtr)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const auxOffVListPtr)) (.reg 7) ;;
  .store (.bin .add (.reg 1) (.const auxOffT0ParentPtr)) (.reg 8) ;;
  .store (.bin .add (.reg 1) (.const auxOffT0ParentTreeIdxPtr)) (.reg 9) ;;
  .store (.bin .add (.reg 1) (.const auxOffT0DepthPtr)) (.reg 10) ;;
  .store (.bin .add (.reg 1) (.const auxOffLogCap)) (.reg 5) ;;
  .store (.bin .add (.reg 1) (.const auxOffUpVPtr)) (.reg 11) ;;
  .store (.bin .add (.reg 1) (.const auxOffUpMinIdxPtr)) (.reg 13) ;;
  .store (.bin .add (.reg 1) (.const auxOffThParentPtr)) (.reg 14) ;;
  .store (.bin .add (.reg 1) (.const auxOffOrigVertPtr)) (.reg 15) ;;
  .store (.bin .add (.reg 1) (.const auxOffIsOrigVertPtr)) (.reg 16) ;;
  .store (.bin .add (.reg 1) (.const auxOffQBufAPtr)) (.reg 17) ;;
  .store (.bin .add (.reg 1) (.const auxOffQBufBPtr)) (.reg 18) ;;
  .store (.bin .add (.reg 1) (.const auxOffVisAPtr)) (.reg 19) ;;
  .store (.bin .add (.reg 1) (.const auxOffVisBPtr)) (.reg 20) ;;
  .store (.bin .add (.reg 1) (.const auxOffThStackPtr)) (.reg 21) ;;
  .store (.bin .add (.reg 1) (.const auxOffFSplitScratchPtr)) (.reg 22) ;;
  .store (.bin .add (.reg 1) (.const auxOffR0Idx)) (.load (.bin .add (.reg 0) (.const auxOffR0Idx))) ;;
  -- Copy dense n0- and (n0 * logCap)-sized arrays
  .assign 23 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffVListPtr)))) ;;
  .call 25 bCopy [.reg 7, .reg 23, .reg 3] ;;
  .call 25 bCopy [.reg 8, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0ParentPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 9, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0ParentTreeIdxPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 10, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffT0DepthPtr))), .reg 3] ;;
  .call 25 bCopy [.reg 11, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffUpVPtr))), .reg 12] ;;
  .call 25 bCopy [.reg 13, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffUpMinIdxPtr))), .reg 12] ;;
  .call 25 bCopy [.reg 14, .bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffThParentPtr))), .reg 3] ;;
  -- Sparse vertex-indexed arrays: vIdx, isOrigVert, origVert
  .assign 24 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.const auxOffOrigVertPtr)))) ;;
  forRange 25 (.const 0) (.reg 3)
    (.assign 26 (.load (.bin .add (.reg 23) (.reg 25))) ;;
     .store (.bin .add (.reg 6) (.reg 26)) (.bin .add (.reg 25) (.const 1)) ;;
     .store (.bin .add (.reg 16) (.reg 26)) (.const 1) ;;
     .store (.bin .add (.reg 15) (.reg 26)) (.load (.bin .add (.reg 24) (.reg 26)))) ;;
  .ret (.const 0)

/-- Top-level sparse repacker of one guest LSF handle `src` (in host address space, i.e.,
`guestBase + h_g`) into fresh zeroed host memory starting at `dst` with host capacities
`(vCap_h, eCap_h, L_w_h)`. Args: `[guestBase, h_g, dst, vCap_h, eCap_h, L_w_h]`.
Returns `lsfEndAddr dst vCap_h eCap_h n0 tM L_w_h`. -/
def repackOneLSFProc (bLog bRepDg bRepT bRepFAnc bRepW bRepWstr bRepAux : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 0) (.reg 1)) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.const lsfOffN0))) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const lsfOffM0))) ;;
  .assign 9 (.load (.bin .add (.reg 6) (.const lsfOffTM))) ;;
  .assign 10 (.load (.bin .add (.reg 6) (.const lsfOffLW))) ;;
  -- Compute destination sub-block base addresses matching Layout.lean
  .assign 11 (.bin .add (.reg 2) (.const lsfHdrSize)) ;;
  -- dgGSize = 4 + 7 * vCap_h + 9 * eCap_h
  .assign 12 (.bin .add (.reg 11)
    (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 3))) (.bin .mul (.const 9) (.reg 4)))) ;;
  -- tBlockSize = 8 + (4 + 7 * vCap_h + 9 * (2 * tM + 1)) + 4 * tM + eCap_h + (4 + 2 * tM)
  .assign 13 (.bin .add (.reg 12)
    (.bin .add (.bin .add (.bin .add (.bin .add (.const tHdrSize)
      (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 3)))
        (.bin .mul (.const 9) (.bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1)))))
      (.bin .mul (.const 4) (.reg 9))) (.reg 4)) (.bin .add (.const 4) (.bin .mul (.const 2) (.reg 9))))) ;;
  -- fECap = 3 * eCap_h + n0
  .assign 14 (.bin .add (.bin .mul (.const 3) (.reg 4)) (.reg 7)) ;;
  .assign 15 (.bin .add (.reg 13)
    (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 3))) (.bin .mul (.const 9) (.reg 14)))) ;;
  .assign 16 (.bin .add (.reg 15) (.bin .add (.const fAncHdrSize) (.bin .mul (.const 5) (.reg 3)))) ;;
  .assign 17 (.bin .add (.reg 16) (.bin .add (.const 9) (.bin .mul (.const 5) (.reg 7)))) ;;
  -- auxSize = 20 + 7 * vCap_h + 5 * n0 + 2 * (n0 * logCap) + (hldDepthBound n0 + 2) + (4 + n0)
  .call 18 bLog [.bin .add (.reg 7) (.const 1)] ;;
  .assign 18 (.bin .add (.reg 18) (.const 1)) ;;
  .call 19 bLog [.reg 7] ;;
  .assign 19 (.bin .add (.reg 19) (.const 1)) ;;
  .assign 20 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.const auxHdrSize)
    (.bin .mul (.const 7) (.reg 3))) (.bin .mul (.const 5) (.reg 7)))
    (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 18))))
    (.bin .add (.bin .mul (.reg 19) (.bin .add (.reg 19) (.const 1))) (.const 2)))
    (.bin .add (.const 4) (.reg 7))) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 20)) ;;
  .assign 19 (.bin .add (.reg 18) (.bin .mul (.reg 4) (.reg 5))) ;;
  .assign 20 (.bin .add (.reg 19) (.bin .mul (.reg 4) (.reg 5))) ;;
  -- Store 24-word header at dst
  .store (.bin .add (.reg 2) (.const lsfOffVCap)) (.reg 3) ;;
  .store (.bin .add (.reg 2) (.const lsfOffECap)) (.reg 4) ;;
  .store (.bin .add (.reg 2) (.const lsfOffN0)) (.reg 7) ;;
  .store (.bin .add (.reg 2) (.const lsfOffM0)) (.reg 8) ;;
  .store (.bin .add (.reg 2) (.const lsfOffDgGPtr)) (.reg 11) ;;
  .store (.bin .add (.reg 2) (.const lsfOffTPtr)) (.reg 12) ;;
  .store (.bin .add (.reg 2) (.const lsfOffDgFPtr)) (.reg 13) ;;
  .store (.bin .add (.reg 2) (.const lsfOffFAncPtr)) (.reg 15) ;;
  .store (.bin .add (.reg 2) (.const lsfOffWPtr)) (.reg 16) ;;
  .store (.bin .add (.reg 2) (.const lsfOffWstrNumPtr)) (.reg 18) ;;
  .store (.bin .add (.reg 2) (.const lsfOffWstrDenPtr)) (.reg 19) ;;
  .store (.bin .add (.reg 2) (.const lsfOffLW)) (.reg 5) ;;
  .store (.bin .add (.reg 2) (.const lsfOffHLimb)) (.load (.bin .add (.reg 6) (.const lsfOffHLimb))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffPFp)) (.load (.bin .add (.reg 6) (.const lsfOffPFp))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffLIn)) (.load (.bin .add (.reg 6) (.const lsfOffLIn))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffRCount)) (.load (.bin .add (.reg 6) (.const lsfOffRCount))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffAuxPtr)) (.reg 17) ;;
  .store (.bin .add (.reg 2) (.const lsfOffEnd)) (.reg 20) ;;
  .store (.bin .add (.reg 2) (.const lsfOffR0)) (.load (.bin .add (.reg 6) (.const lsfOffR0))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffKNat)) (.load (.bin .add (.reg 6) (.const lsfOffKNat))) ;;
  .store (.bin .add (.reg 2) (.const lsfOffTM)) (.reg 9) ;;
  -- Repack all 7 sub-blocks (translating guest internal pointers by + guestBase)
  .assign 21 (.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffDgGPtr)))) ;;
  .call 22 bRepDg [.reg 21, .reg 11, .reg 3, .reg 4] ;;
  .call 22 bRepT [.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffTPtr))), .reg 12, .reg 3, .reg 4, .reg 0] ;;
  .assign 23 (.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffDgFPtr)))) ;;
  .call 22 bRepDg [.reg 23, .reg 13, .reg 3, .reg 14] ;;
  .call 22 bRepFAnc [.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffFAncPtr))), .reg 23, .reg 15, .reg 3, .reg 0] ;;
  .call 22 bRepW [.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffWPtr))), .reg 16, .reg 7] ;;
  .call 22 bRepWstr
    [.reg 21,
     .bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffWstrNumPtr))),
     .bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffWstrDenPtr))),
     .reg 10, .reg 18, .reg 19, .reg 5] ;;
  .call 22 bRepAux [.bin .add (.reg 0) (.load (.bin .add (.reg 6) (.const lsfOffAuxPtr))), .reg 17, .reg 3, .reg 7, .reg 0] ;;
  .ret (.reg 20)

def repackProcs (bRep bCopy bLog : ℕ) : List Stmt :=
  [repackDynGraphProc,
   repackTBlockProc bCopy (bRep + 0),
   repackFAncProc bCopy,
   repackWBlockProc bCopy,
   repackWstrProc bCopy,
   repackAuxProc bCopy bLog,
   repackOneLSFProc bLog (bRep + 0) (bRep + 1) (bRep + 2) (bRep + 3) (bRep + 4) (bRep + 5)]

lemma repackProcs_length (bRep bCopy bLog : ℕ) : (repackProcs bRep bCopy bLog).length = 7 := rfl

lemma repackProcs_noRand (bRep bCopy bLog : ℕ) : ∀ s ∈ repackProcs bRep bCopy bLog, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackDynGraphProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackTBlockProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackFAncProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackWBlockProc, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackWstrProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackAuxProc, forRange, forUp, Stmt.NoRand]
  rcases List.mem_cons.mp hs with rfl | hs; · simp [repackOneLSFProc, Stmt.NoRand]
  cases hs

/-- Step bound for repacking one guest LSF handle into host memory (independent of `vCap_h`,
`eCap_h`, and `L_w_h`). -/
def repackOneLSFCost (n0 m0 L_w_g : ℕ) : ℕ :=
  120 * n0 * auxLogCap n0 + 50 * m0 * L_w_g + 1600 * n0 + 300 * m0 + 2000

end MinCostFlow.SparseCore.Program
