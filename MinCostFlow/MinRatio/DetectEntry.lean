module

public import MinCostFlow.MinRatio.DetectStart

/-!
# Detect entry from the IPM call

Definition 4.5 (page 14) supplies the report output address. The
call obtains the tree and its lookup tables from the data-structure
handle before running the reporting loop of Theorem 5.1 (pages 29–30).
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The Detect fields in the handle are the tree handle, slot names,
inverse names, threshold pointers, live edge count, and workspace sizes. -/
@[expose] def DetectHeaderAt (mem : ℕ → ℕ) (handle tree names inverse thresholds count limbs searchSpace readSpace : ℕ) : Prop :=
  ListAt mem handle [tree, names, inverse, thresholds, count, limbs, searchSpace, readSpace]

/-- Decode the shared handle and preserve the incoming heap as the report base. -/
@[expose] def detectEntryArgs : Stmt :=
  .assign 17 (.reg 1) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const 7))) ;;
  .assign 0 (.load (.bin .add (.reg 0) (.const 0)))

/-- Decode the Detect header and load its workspace sizes in 50 steps. -/
theorem detectEntryArgs_runs {w handle base tree names inverse thresholds count limbs searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (ht : DetectHeaderAt mem handle tree names inverse thresholds count limbs searchSpace readSpace)
    (hheader : handle + 7 < 2 ^ w) :
    ∃ out, Runs w p ω detectEntryArgs
      (startState [handle, base] mem pos) .normal out 50 ∧ out.mem = mem ∧ out.pos = pos ∧
      out.regs 0 = tree ∧ out.regs 17 = base ∧ out.regs 6 = names ∧ out.regs 7 = inverse ∧
      out.regs 14 = thresholds ∧ out.regs 18 = count ∧ out.regs 10 = limbs ∧
      out.regs 15 = searchSpace ∧ out.regs 16 = readSpace := by
  let s0 := startState [handle, base] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 17 base }
  let s2 := { s1 with regs := Function.update s1.regs 6 names }
  let s3 := { s2 with regs := Function.update s2.regs 7 inverse }
  let s4 := { s3 with regs := Function.update s3.regs 14 thresholds }
  let s5 := { s4 with regs := Function.update s4.regs 18 count }
  let s6 := { s5 with regs := Function.update s5.regs 10 limbs }
  let s7 := { s6 with regs := Function.update s6.regs 15 searchSpace }
  let s8 := { s7 with regs := Function.update s7.regs 16 readSpace }
  let s9 := { s8 with regs := Function.update s8.regs 0 tree }
  have hload (st : State) (r offset value : ℕ) (hreg : st.regs 0 = handle)
      (hmem : st.mem = mem) (ha : offset ≤ 7) (hv : mem (handle + offset) = value) :
      Runs w p ω (.assign r (.load (.bin .add (.reg 0) (.const offset)))) st .normal
        { st with regs := Function.update st.regs r value } 5 := by
    refine runs_assign_iff.mpr ⟨value, ?_, rfl, rfl, rfl⟩
    have hoff : offset < 2 ^ w := by omega
    have haddr : handle + offset < 2 ^ w := by omega
    simp only [Expr.eval, BinOp.eval, hreg, hmem, ite_eq_left hoff]
    change Option.map mem (if handle + offset < 2 ^ w then some (handle + offset) else none) = _
    rw [ite_eq_left haddr]
    exact congrArg some hv
  have hr1 : Runs w p ω (.assign 17 (.reg 1)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨base, rfl, rfl, rfl, rfl⟩
  have hr2 := hload s1 6 1 names rfl rfl (by decide) (ht 1 (by simp))
  have hr3 := hload s2 7 2 inverse rfl rfl (by decide) (ht 2 (by simp))
  have hr4 := hload s3 14 3 thresholds rfl rfl (by decide) (ht 3 (by simp))
  have hr5 := hload s4 18 4 count rfl rfl (by decide) (ht 4 (by simp))
  have hr6 := hload s5 10 5 limbs rfl rfl (by decide) (ht 5 (by simp))
  have hr7 := hload s6 15 6 searchSpace rfl rfl (by decide) (ht 6 (by simp))
  have hr8 := hload s7 16 7 readSpace rfl rfl (by decide) (ht 7 (by simp))
  have hr9 := hload s8 0 0 tree rfl rfl (by decide) (ht 0 (by simp))
  refine ⟨s9, ?_, rfl, rfl, ?_⟩
  · unfold detectEntryArgs
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 2, 47, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 5, 41, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 5, 35, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 5, 29, hr4, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s5, 5, 23, hr5, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s6, 5, 17, hr6, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s7, 5, 11, hr7, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s8, 5, 5, hr8, hr9, rfl⟩)
  · simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne]

/-- The IPM Detect entry receives just the handle and report base. -/
@[expose] def detectIPMBody (find read report finish : ℕ) : Stmt :=
  detectEntryArgs ;; detectProgram find read report finish

/-- Entry setup and its sequence instruction add 51 steps. -/
theorem detectIPMBody_runs_of_program
    {w find read report finish heap cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st setup out : State}
    (hs : Runs w p ω (detectEntryArgs) st .normal setup 50)
    (hr : Runs w p ω (detectProgram find read report finish) setup (.returned heap) out cost) :
    Runs w p ω (detectIPMBody find read report finish)
      st (.returned heap) out (50 + cost + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨setup, 50, cost, hs, hr, rfl⟩)

/-- The stored numeric parameters include the limb width and binary
precision from Init, and the two workspace sizes used by Detect. -/
@[expose] def MinRatioNumericHeaderAt (mem : ℕ → ℕ) (handle limbs precision searchSpace readSpace : ℕ) :
    Prop :=
  ListAt mem (handle + 5) [limbs, searchSpace, readSpace, precision]

/-- Store the width and precision from registers 2 and 3 and the workspace
sizes from registers 78 and 79 at the handle in register 74. -/
@[expose] def storeMinRatioNumericHeader : Stmt :=
  .store (.bin .add (.reg 74) (.const 5)) (.reg 2) ;;
  .store (.bin .add (.reg 74) (.const 6)) (.reg 78) ;;
  .store (.bin .add (.reg 74) (.const 7)) (.reg 79) ;;
  .store (.bin .add (.reg 74) (.const 8)) (.reg 3)

/-- The Init store writes the four numeric fields and preserves all
other memory, registers, and the random tape position. -/
theorem storeMinRatioNumericHeader_runs {w handle limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 74 = handle) (hL : st.regs 2 = limbs) (hP : st.regs 3 = precision)
    (hs : st.regs 78 = searchSpace) (hr : st.regs 79 = readSpace)
    (hroom : handle + 8 < 2 ^ w) :
    ∃ out, Runs w p ω storeMinRatioNumericHeader st .normal out 23 ∧
      MinRatioNumericHeaderAt out.mem handle limbs precision searchSpace readSpace ∧
      (∀ a, a < handle + 5 ∨ handle + 8 < a → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  let s1 := { st with mem := Function.update st.mem (handle + 5) limbs }
  let s2 := { s1 with mem := Function.update s1.mem (handle + 6) searchSpace }
  let s3 := { s2 with mem := Function.update s2.mem (handle + 7) readSpace }
  let out := { s3 with mem := Function.update s3.mem (handle + 8) precision }
  have hstore (s : State) (off r value : ℕ) (ho : off ≤ 8) (hbase : s.regs 74 = handle)
      (hv : s.regs r = value) :
      Runs w p ω (.store (.bin .add (.reg 74) (.const off)) (.reg r)) s .normal
        { s with mem := Function.update s.mem (handle + off) value } 5 := by
    refine runs_store_iff.mpr ⟨handle + off, value, ?_, ?_, rfl, rfl, rfl⟩
    · simp [Expr.eval, BinOp.eval, hbase, show off < 2 ^ w by omega,
        show handle + off < 2 ^ w by omega]
    · simp [Expr.eval, hv]
  have h1 := hstore st 5 2 limbs (by decide) hh hL
  have h2 := hstore s1 6 78 searchSpace (by decide) hh hs
  have h3 := hstore s2 7 79 readSpace (by decide) hh hr
  have h4 := hstore s3 8 3 precision (by decide) hh hP
  refine ⟨out, ?_, ?_, ?_, rfl, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 17, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 11, h2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, 5, h3, h4, rfl⟩), rfl⟩), rfl⟩)
  · intro j hj
    have hj' : j < 4 := hj
    interval_cases j <;> simp [out, s3, s2, s1]
  · intro a ha
    simp [out, s3, s2, s1, Function.update_of_ne (show a ≠ handle + 5 by omega),
      Function.update_of_ne (show a ≠ handle + 6 by omega),
      Function.update_of_ne (show a ≠ handle + 7 by omega),
      Function.update_of_ne (show a ≠ handle + 8 by omega)]

/-- Load the numeric format at the chain entry before registers 0
through 4 are reused. The traversal reads the saved width in register 67. -/
@[expose] def loadMinRatioNumericFormat : Stmt :=
  .assign 67 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 68 (.load (.bin .add (.reg 0) (.const 8)))

/-- Reading the saved width and precision takes eleven steps. -/
theorem loadMinRatioNumericFormat_runs {w handle limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} (hh : st.regs 0 = handle)
    (hn : MinRatioNumericHeaderAt st.mem handle limbs precision searchSpace readSpace)
    (hroom : handle + 8 < 2 ^ w) :
    ∃ out, Runs w p ω loadMinRatioNumericFormat st .normal out 11 ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧
      (∀ r, r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 67 limbs }
  let out := { mid with regs := Function.update mid.regs 68 precision }
  have hL : st.mem (handle + 5) = limbs := by simpa using hn 0 (by simp)
  have hP : st.mem (handle + 8) = precision := by simpa [Nat.add_assoc] using hn 3 (by simp)
  have h1 : Runs w p ω (.assign 67 (.load (.bin .add (.reg 0) (.const 5)))) st .normal mid 5 :=
    runs_assign_iff.mpr ⟨limbs, by
      simp [Expr.eval, BinOp.eval, hh, show 5 < 2 ^ w by omega,
        show handle + 5 < 2 ^ w by omega, hL], rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 68 (.load (.bin .add (.reg 0) (.const 8)))) mid .normal out 5 :=
    runs_assign_iff.mpr ⟨precision, by
      simp [Expr.eval, BinOp.eval, mid, hh, Function.update_of_ne, show 8 < 2 ^ w by omega,
        hroom, hP], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 5, h1, h2, rfl⟩),
    by simp [out, mid], by simp [out],
    fun r h67 h68 => by simp [out, mid, Function.update_of_ne, h67, h68], rfl, rfl⟩

end MinCostFlow.MinRatio
