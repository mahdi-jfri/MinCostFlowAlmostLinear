module

public import MinCostFlow.MinRatio.DetectEntry

/-!
# Chain parameters stored at Init

The chain routines of Algorithm 1 (page 20) share parameters chosen
at initialization. The fixed header places them after the Detect
and numeric format fields.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The eight chain fields follow the numeric header in the handle.
The barrier pointer addresses its exponent header and fixed-point block. -/
@[expose] def ChainInitParametersAt (mem : ℕ → ℕ)
    (handle m V depth branch psi alphaPtr quality epsilon : ℕ) : Prop :=
  ListAt mem (handle + 9) [m, V, depth, branch, psi, alphaPtr, quality, epsilon]

/-- Store the chain parameters at the handle in register 74. Depth and
branching have been saved in registers 75 and 76. -/
@[expose] def storeChainInitParameters : Stmt :=
  .store (.bin .add (.reg 74) (.const 9)) (.reg 0) ;;
  .store (.bin .add (.reg 74) (.const 10)) (.reg 1) ;;
  .store (.bin .add (.reg 74) (.const 11)) (.reg 75) ;;
  .store (.bin .add (.reg 74) (.const 12)) (.reg 76) ;;
  .store (.bin .add (.reg 74) (.const 13)) (.reg 6) ;;
  .store (.bin .add (.reg 74) (.const 14)) (.reg 4) ;;
  .store (.bin .add (.reg 74) (.const 15)) (.reg 72) ;;
  .store (.bin .add (.reg 74) (.const 16)) (.reg 73)

/-- The Init header stores take 47 steps and affect only the eight
chain parameter cells. -/
theorem storeChainInitParameters_runs {w handle m V depth branch psi alphaPtr quality epsilon : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 74 = handle)
    (hm : st.regs 0 = m)
    (hV : st.regs 1 = V)
    (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch)
    (hpsi : st.regs 6 = psi)
    (ha : st.regs 4 = alphaPtr)
    (hq : st.regs 72 = quality)
    (he : st.regs 73 = epsilon)
    (hroom : handle + 16 < 2 ^ w) :
    ∃ out, Runs w p ω storeChainInitParameters st .normal out 47 ∧
      ChainInitParametersAt out.mem handle m V depth branch psi alphaPtr quality epsilon ∧
      (∀ a, a < handle + 9 ∨ handle + 16 < a → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  let s0 := st
  let s1 := { s0 with mem := Function.update s0.mem (handle + 9) m }
  let s2 := { s1 with mem := Function.update s1.mem (handle + 10) V }
  let s3 := { s2 with mem := Function.update s2.mem (handle + 11) depth }
  let s4 := { s3 with mem := Function.update s3.mem (handle + 12) branch }
  let s5 := { s4 with mem := Function.update s4.mem (handle + 13) psi }
  let s6 := { s5 with mem := Function.update s5.mem (handle + 14) alphaPtr }
  let s7 := { s6 with mem := Function.update s6.mem (handle + 15) quality }
  let s8 := { s7 with mem := Function.update s7.mem (handle + 16) epsilon }
  have hstore (s : State) (off r value : ℕ) (ho : off ≤ 16) (hbase : s.regs 74 = handle)
      (hv : s.regs r = value) :
      Runs w p ω (.store (.bin .add (.reg 74) (.const off)) (.reg r)) s .normal
        { s with mem := Function.update s.mem (handle + off) value } 5 := by
    refine runs_store_iff.mpr ⟨handle + off, value, ?_, by simp [Expr.eval, hv], rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, hbase, show off < 2 ^ w by omega,
      show handle + off < 2 ^ w by omega]
  have hr1 := hstore s0 9 0 m (by decide) hh hm
  have hr2 := hstore s1 10 1 V (by decide) hh hV
  have hr3 := hstore s2 11 75 depth (by decide) hh hd
  have hr4 := hstore s3 12 76 branch (by decide) hh hb
  have hr5 := hstore s4 13 6 psi (by decide) hh hpsi
  have hr6 := hstore s5 14 4 alphaPtr (by decide) hh ha
  have hr7 := hstore s6 15 72 quality (by decide) hh hq
  have hr8 := hstore s7 16 73 epsilon (by decide) hh he
  refine ⟨s8, ?_, ?_, ?_, rfl, rfl⟩
  · unfold storeChainInitParameters
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 5, 41, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 5, 35, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 5, 29, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 5, 23, hr4, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s5, 5, 17, hr5, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s6, 5, 11, hr6, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s7, 5, 5, hr7, hr8, rfl⟩)
  · intro j hj
    have hj' : j < 8 := hj
    interval_cases j <;> simp [s8, s7, s6, s5, s4, s3, s2, s1, s0]
  · intro a ha'
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, s0]
    rw [Function.update_of_ne (show a ≠ handle + 16 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 15 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 14 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 13 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 12 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 11 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 10 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 9 by omega)]

/-- Load the saved chain parameters using the handle in register 74.
The loads leave the operation argument registers available to the caller. -/
@[expose] def loadChainInitParameters : Stmt :=
  .assign 88 (.load (.bin .add (.reg 74) (.const 9))) ;;
  .assign 89 (.load (.bin .add (.reg 74) (.const 10))) ;;
  .assign 75 (.load (.bin .add (.reg 74) (.const 11))) ;;
  .assign 76 (.load (.bin .add (.reg 74) (.const 12))) ;;
  .assign 90 (.load (.bin .add (.reg 74) (.const 13))) ;;
  .assign 91 (.load (.bin .add (.reg 74) (.const 14))) ;;
  .assign 72 (.load (.bin .add (.reg 74) (.const 15))) ;;
  .assign 73 (.load (.bin .add (.reg 74) (.const 16)))

/-- Chain operations recover the exact Init parameters in 47 steps,
while retaining every other register and the machine memory. -/
theorem loadChainInitParameters_runs {w handle m V depth branch psi alphaPtr quality epsilon : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 74 = handle)
    (hat : ChainInitParametersAt st.mem handle m V depth branch psi alphaPtr quality epsilon)
    (hroom : handle + 16 < 2 ^ w) :
    ∃ out, Runs w p ω loadChainInitParameters st .normal out 47 ∧
      out.regs 88 = m ∧ out.regs 89 = V ∧ out.regs 75 = depth ∧ out.regs 76 = branch ∧
      out.regs 90 = psi ∧ out.regs 91 = alphaPtr ∧ out.regs 72 = quality ∧ out.regs 73 = epsilon ∧
      (∀ r, r ≠ 88 → r ≠ 89 → r ≠ 75 → r ≠ 76 → r ≠ 90 → r ≠ 91 → r ≠ 72 → r ≠ 73 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let s0 := st
  let s1 := { s0 with regs := Function.update s0.regs 88 m }
  let s2 := { s1 with regs := Function.update s1.regs 89 V }
  let s3 := { s2 with regs := Function.update s2.regs 75 depth }
  let s4 := { s3 with regs := Function.update s3.regs 76 branch }
  let s5 := { s4 with regs := Function.update s4.regs 90 psi }
  let s6 := { s5 with regs := Function.update s5.regs 91 alphaPtr }
  let s7 := { s6 with regs := Function.update s6.regs 72 quality }
  let s8 := { s7 with regs := Function.update s7.regs 73 epsilon }
  have hload (s : State) (off r value : ℕ) (ho : off ≤ 16) (hbase : s.regs 74 = handle)
      (hm : s.mem (handle + off) = value) :
      Runs w p ω (.assign r (.load (.bin .add (.reg 74) (.const off)))) s .normal
        { s with regs := Function.update s.regs r value } 5 := by
    refine runs_assign_iff.mpr ⟨value, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, hbase, hm, show off < 2 ^ w by omega,
      show handle + off < 2 ^ w by omega]
  have hm1 : st.mem (handle + 9) = m := by
    simpa [Nat.add_assoc] using hat 0 (by simp)
  have hr1 := hload s0 9 88 m (by decide) hh hm1
  have hm2 : st.mem (handle + 10) = V := by
    simpa [Nat.add_assoc] using hat 1 (by simp)
  have hr2 := hload s1 10 89 V (by decide) hh hm2
  have hm3 : st.mem (handle + 11) = depth := by
    simpa [Nat.add_assoc] using hat 2 (by simp)
  have hr3 := hload s2 11 75 depth (by decide) hh hm3
  have hm4 : st.mem (handle + 12) = branch := by
    simpa [Nat.add_assoc] using hat 3 (by simp)
  have hr4 := hload s3 12 76 branch (by decide) hh hm4
  have hm5 : st.mem (handle + 13) = psi := by
    simpa [Nat.add_assoc] using hat 4 (by simp)
  have hr5 := hload s4 13 90 psi (by decide) hh hm5
  have hm6 : st.mem (handle + 14) = alphaPtr := by
    simpa [Nat.add_assoc] using hat 5 (by simp)
  have hr6 := hload s5 14 91 alphaPtr (by decide) hh hm6
  have hm7 : st.mem (handle + 15) = quality := by
    simpa [Nat.add_assoc] using hat 6 (by simp)
  have hr7 := hload s6 15 72 quality (by decide) hh hm7
  have hm8 : st.mem (handle + 16) = epsilon := by
    simpa [Nat.add_assoc] using hat 7 (by simp)
  have hr8 := hload s7 16 73 epsilon (by decide) hh hm8
  refine ⟨s8, ?_, ?_⟩
  · unfold loadChainInitParameters
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 5, 41, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 5, 35, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 5, 29, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 5, 23, hr4, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s5, 5, 17, hr5, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s6, 5, 11, hr6, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s7, 5, 5, hr7, hr8, rfl⟩)
  · simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, Function.update_of_ne]
    intro r h0 h1 h75 h76 h6 h4 h72 h73
    simp [Function.update_of_ne, h0, h1, h75, h76, h6, h4, h72, h73]

/-- Allocate the chain header from the free pointer in register 7.
The handle and next free pointer are saved in registers 74 and 77. -/
@[expose] def allocateChainInitHeader : Stmt :=
  .assign 74 (.reg 7) ;; storeChainInitParameters ;;
  .assign 77 (.bin .add (.reg 74) (.const 17))

/-- The allocation installs the chain fields, preserves the earlier
blocks, and leaves the first nine header cells available for the
Detect fields and numeric format. -/
theorem allocateChainInitHeader_runs {w heap m V depth branch psi alphaPtr quality epsilon : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 7 = heap)
    (hm : st.regs 0 = m) (hV : st.regs 1 = V) (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch) (hpsi : st.regs 6 = psi) (ha : st.regs 4 = alphaPtr)
    (hq : st.regs 72 = quality) (he : st.regs 73 = epsilon)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 17 < 2 ^ w) :
    ∃ out, Runs w p ω allocateChainInitHeader st .normal out 55 ∧
      out.regs 74 = heap ∧ out.regs 77 = heap + 17 ∧
      ChainInitParametersAt out.mem heap m V depth branch psi alphaPtr quality epsilon ∧
      (∀ a < heap + 9, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + 17) ∧
      (∀ r, r ≠ 74 → r ≠ 77 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let ready := { st with regs := Function.update st.regs 74 heap }
  have hstart : Runs w p ω (.assign 74 (.reg 7)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  obtain ⟨mid, hr, hheader, hframe, hregs, hpos⟩ :=
    storeChainInitParameters_runs (w := w) (p := p) (ω := ω) (st := ready) (handle := heap) (by simp [ready])
      (by simpa [ready] using hm) (by simpa [ready] using hV) (by simpa [ready] using hd)
      (by simpa [ready] using hb) (by simpa [ready] using hpsi) (by simpa [ready] using ha)
      (by simpa [ready] using hq) (by simpa [ready] using he) (by omega)
  have h74 : mid.regs 74 = heap := by rw [hregs]; simp [ready]
  let out := { mid with regs := Function.update mid.regs 77 (heap + 17) }
  have hnext : Runs w p ω (.assign 77 (.bin .add (.reg 74) (.const 17))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, h74, hroom, show 17 < 2 ^ w by omega], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, h74], by simp [out], hheader,
    fun a ha => hframe a (Or.inl ha), ?_, ?_, hpos⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 2, 52, hstart,
      runs_seq_iff.mpr (Or.inr ⟨mid, 47, 4, hr, hnext, rfl⟩), rfl⟩)
  · intro a ha
    exact (hframe a (Or.inr (by omega))).trans (hz a (by omega))
  · intro r h74' h77
    simp [out, hregs, ready, Function.update_of_ne, h74', h77]

/-- The nine chain words of the solver header: the eight chain parameters of
`ChainInitParametersAt` and, right after them at `handle + 17`, the depth `coreDepth` that the
sparse-core program takes at its initialization. -/
@[expose] def SolverChainHeaderAt (mem : ℕ → ℕ)
    (handle m V depth branch psi alphaPtr quality epsilon coreDepth : ℕ) : Prop :=
  ListAt mem (handle + 9) [m, V, depth, branch, psi, alphaPtr, quality, epsilon, coreDepth]

theorem SolverChainHeaderAt.chain {mem : ℕ → ℕ}
    {handle m V depth branch psi alphaPtr quality epsilon coreDepth : ℕ}
    (h : SolverChainHeaderAt mem handle m V depth branch psi alphaPtr quality epsilon coreDepth) :
    ChainInitParametersAt mem handle m V depth branch psi alphaPtr quality epsilon :=
  fun j hj => by
    have hj' : j < 8 := hj
    have := h j (by simp; omega)
    interval_cases j <;> simpa using this

theorem SolverChainHeaderAt.coreDepth_eq {mem : ℕ → ℕ}
    {handle m V depth branch psi alphaPtr quality epsilon coreDepth : ℕ}
    (h : SolverChainHeaderAt mem handle m V depth branch psi alphaPtr quality epsilon coreDepth) :
    mem (handle + 17) = coreDepth := by
  simpa [Nat.add_assoc] using h 8 (by simp)

theorem SolverChainHeaderAt.of_chain {mem : ℕ → ℕ}
    {handle m V depth branch psi alphaPtr quality epsilon coreDepth : ℕ}
    (h : ChainInitParametersAt mem handle m V depth branch psi alphaPtr quality epsilon)
    (hD : mem (handle + 17) = coreDepth) :
    SolverChainHeaderAt mem handle m V depth branch psi alphaPtr quality epsilon coreDepth := by
  change ListAt mem (handle + 9)
    ([m, V, depth, branch, psi, alphaPtr, quality, epsilon] ++ [coreDepth])
  refine listAt_append.mpr ⟨h, ?_⟩
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  simpa [Nat.add_assoc] using hD

/-- Store the sparse-core depth at `handle + 17` and move the free pointer in register `77` past
it. The depth is read from the cell at `reg 57 + reg 75`, which is `pBase + 6 + d` in the
initializer, and kept in register `98`. -/
@[expose] def storeCoreDepthHeader : Stmt :=
  .assign 98 (.load (.bin .add (.reg 57) (.reg 75))) ;;
  .store (.bin .add (.reg 74) (.const 17)) (.reg 98) ;;
  .assign 77 (.bin .add (.reg 74) (.const 18))

/-- The depth store writes only the cell `handle + 17`, and sets registers `98` (the depth) and
`77` (`handle + 18`). -/
theorem storeCoreDepthHeader_runs {w handle src d coreDepth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h74 : st.regs 74 = handle) (h57 : st.regs 57 = src) (h75 : st.regs 75 = d)
    (hsrc : st.mem (src + d) = coreDepth) (hsrcW : src + d < 2 ^ w)
    (hroom : handle + 18 < 2 ^ w) :
    ∃ out, Runs w p ω storeCoreDepthHeader st .normal out 16 ∧
      out.mem = Function.update st.mem (handle + 17) coreDepth ∧
      out.regs 98 = coreDepth ∧ out.regs 77 = handle + 18 ∧
      (∀ r, r ≠ 98 → r ≠ 77 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let s1 := { st with regs := Function.update st.regs 98 coreDepth }
  let s2 := { s1 with mem := Function.update s1.mem (handle + 17) coreDepth }
  let s3 := { s2 with regs := Function.update s2.regs 77 (handle + 18) }
  have r1 : Runs w p ω (.assign 98 (.load (.bin .add (.reg 57) (.reg 75)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨coreDepth, by simp [Expr.eval, BinOp.eval, h57, h75, hsrcW, hsrc],
      rfl, rfl, rfl⟩
  have h74' : s1.regs 74 = handle := by simp [s1, h74]
  have r2 : Runs w p ω (.store (.bin .add (.reg 74) (.const 17)) (.reg 98)) s1 .normal s2 5 :=
    runs_store_iff.mpr ⟨handle + 17, coreDepth, by
      simp [Expr.eval, BinOp.eval, h74', show 17 < 2 ^ w by omega,
        show handle + 17 < 2 ^ w by omega], by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 77 (.bin .add (.reg 74) (.const 18))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨handle + 18, by
      simp [Expr.eval, BinOp.eval, s2, h74', show 18 < 2 ^ w by omega, hroom], rfl, rfl, rfl⟩
  refine ⟨s3, ?_, rfl, by simp [s3, s2, s1], by simp [s3], ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 10, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, r2, r3, rfl⟩), rfl⟩)
  · intro r h98 h77
    simp [s3, s2, s1, Function.update_of_ne h98, Function.update_of_ne h77]

/-- Allocate the shared handle and store its chain and numeric fields. -/
@[expose] def allocateMinRatioInitHeader : Stmt :=
  allocateChainInitHeader ;; storeMinRatioNumericHeader

/-- The allocated handle holds both parameter records and leaves its
five Detect descriptor cells untouched for installation of the tree. -/
theorem allocateMinRatioInitHeader_runs
    {w heap m V depth branch psi alphaPtr quality epsilon limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 7 = heap)
    (hm : st.regs 0 = m) (hV : st.regs 1 = V) (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch) (hpsi : st.regs 6 = psi) (ha : st.regs 4 = alphaPtr)
    (hq : st.regs 72 = quality) (he : st.regs 73 = epsilon)
    (hL : st.regs 2 = limbs) (hP : st.regs 3 = precision)
    (hs : st.regs 78 = searchSpace) (hr : st.regs 79 = readSpace)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 17 < 2 ^ w) :
    ∃ out, Runs w p ω allocateMinRatioInitHeader st .normal out 79 ∧
      out.regs 74 = heap ∧ out.regs 77 = heap + 17 ∧
      ChainInitParametersAt out.mem heap m V depth branch psi alphaPtr quality epsilon ∧
      MinRatioNumericHeaderAt out.mem heap limbs precision searchSpace readSpace ∧
      (∀ a < heap + 5, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + 17) ∧
      (∀ r, r ≠ 74 → r ≠ 77 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  obtain ⟨mid, hrun, hhandle, hheap, hchain, hframe, hfree, hregs, hpos⟩ :=
    allocateChainInitHeader_runs (ω := ω) hh hm hV hd hb hpsi ha hq he hz hroom
  obtain ⟨out, hrun', hnumeric, hframe', hregs', hpos'⟩ :=
    storeMinRatioNumericHeader_runs (w := w) (p := p) (ω := ω) hhandle
      ((hregs 2 (by decide) (by decide)).trans hL) ((hregs 3 (by decide) (by decide)).trans hP)
      ((hregs 78 (by decide) (by decide)).trans hs) ((hregs 79 (by decide) (by decide)).trans hr)
      (by omega)
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 55, 23, hrun, hrun', rfl⟩),
    hregs' ▸ hhandle, hregs' ▸ hheap, ?_, hnumeric, ?_, ?_,
    fun r h74 h77 => hregs' ▸ hregs r h74 h77, hpos'.trans hpos⟩
  · intro j hj
    exact (hframe' (heap + 9 + j) (Or.inr (by omega))).trans (hchain j hj)
  · intro a ha'
    exact (hframe' a (Or.inl ha')).trans (hframe a (by omega))
  · intro a ha'
    exact (hframe' a (Or.inr (by omega))).trans (hfree a ha')

/-- Install the tree and lookup descriptors at the start of the
allocated handle. The descriptors are in registers 80 through 84. -/
@[expose] def storeMinRatioDetectDescriptors : Stmt :=
  .store (.bin .add (.reg 74) (.const 0)) (.reg 80) ;;
  .store (.bin .add (.reg 74) (.const 1)) (.reg 81) ;;
  .store (.bin .add (.reg 74) (.const 2)) (.reg 82) ;;
  .store (.bin .add (.reg 74) (.const 3)) (.reg 83) ;;
  .store (.bin .add (.reg 74) (.const 4)) (.reg 84)

/-- Installing the Detect descriptors completes its handle view and
preserves the numeric format and chain parameters. -/
theorem storeMinRatioDetectDescriptors_runs
    {w handle tree names inverse thresholds count limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 74 = handle)
    (ht : st.regs 80 = tree) (hn : st.regs 81 = names) (hi : st.regs 82 = inverse)
    (hd : st.regs 83 = thresholds) (hc : st.regs 84 = count)
    (hnum : MinRatioNumericHeaderAt st.mem handle limbs precision searchSpace readSpace)
    (hword : handle + 4 < 2 ^ w) :
    ∃ out, Runs w p ω storeMinRatioDetectDescriptors st .normal out 29 ∧
      DetectHeaderAt out.mem handle tree names inverse thresholds count limbs searchSpace readSpace ∧
      MinRatioNumericHeaderAt out.mem handle limbs precision searchSpace readSpace ∧
      (∀ a, a < handle ∨ handle + 4 < a → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  let s0 := st
  let s1 := { s0 with mem := Function.update s0.mem (handle + 0) tree }
  let s2 := { s1 with mem := Function.update s1.mem (handle + 1) names }
  let s3 := { s2 with mem := Function.update s2.mem (handle + 2) inverse }
  let s4 := { s3 with mem := Function.update s3.mem (handle + 3) thresholds }
  let s5 := { s4 with mem := Function.update s4.mem (handle + 4) count }
  have hstore (s : State) (off r value : ℕ) (ho : off ≤ 4) (hbase : s.regs 74 = handle)
      (hv : s.regs r = value) :
      Runs w p ω (.store (.bin .add (.reg 74) (.const off)) (.reg r)) s .normal
        { s with mem := Function.update s.mem (handle + off) value } 5 := by
    refine runs_store_iff.mpr ⟨handle + off, value, ?_, by simp [Expr.eval, hv], rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, hbase, show off < 2 ^ w by omega,
      show handle + off < 2 ^ w by omega]
  have hr1 := hstore s0 0 80 tree (by decide) hh ht
  have hr2 := hstore s1 1 81 names (by decide) hh hn
  have hr3 := hstore s2 2 82 inverse (by decide) hh hi
  have hr4 := hstore s3 3 83 thresholds (by decide) hh hd
  have hr5 := hstore s4 4 84 count (by decide) hh hc
  have hframe (a : ℕ) (ha : a < handle ∨ handle + 4 < a) : s5.mem a = st.mem a := by
    simp only [s5, s4, s3, s2, s1, s0]
    rw [Function.update_of_ne (show a ≠ handle + 4 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 3 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 2 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 1 by omega)]
    rw [Function.update_of_ne (show a ≠ handle + 0 by omega)]
  have hnum' : MinRatioNumericHeaderAt s5.mem handle limbs precision searchSpace readSpace := by
    intro j hj
    exact (hframe (handle + 5 + j) (Or.inr (by omega))).trans (hnum j hj)
  refine ⟨s5, ?_, ?_, hnum', hframe, rfl, rfl⟩
  · unfold storeMinRatioDetectDescriptors
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 5, 23, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 5, 17, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 5, 11, hr3, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s4, 5, 5, hr4, hr5, rfl⟩)
  · change ListAt s5.mem handle ([tree, names, inverse, thresholds, count] ++
      [limbs, searchSpace, readSpace])
    apply listAt_append.mpr
    constructor
    · intro j hj
      have hj' : j < 5 := hj
      interval_cases j <;> simp [s5, s4, s3, s2, s1, s0]
    · exact ListAt.take hnum' 3

/-- Reserve enough Detect read scratch for both the tree procedure's
allocation bound in register 79 and its fixed-point edge record. -/
@[expose] def setMinRatioReadSpace : Stmt :=
  .assign 85 (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2))) ;;
  .cond (.bin .lt (.reg 79) (.reg 85)) (.assign 79 (.reg 85)) .nop

/-- The stored read budget covers the machine allocation and the
two endpoints and four fixed-point fields of the edge record. -/
theorem setMinRatioReadSpace_runs {w limbs space : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hL : st.regs 2 = limbs) (hs : st.regs 79 = space)
    (hw : 4 < 2 ^ w) (hroom : 2 + 4 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω setMinRatioReadSpace st .normal out cost ∧
      out.regs 79 = max space (2 + 4 * limbs) ∧
      (∀ r, r ≠ 79 → r ≠ 85 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ cost ≤ 13 := by
  let size := 2 + 4 * limbs
  let mid := { st with regs := Function.update st.regs 85 size }
  have hr : Runs w p ω (.assign 85 (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2))))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨size, by
      simp [Expr.eval, BinOp.eval, hL, hw, size, hroom, show 2 < 2 ^ w by omega,
        show 4 * limbs < 2 ^ w by omega], rfl, rfl, rfl⟩
  have h79 : mid.regs 79 = space := by simpa [mid] using hs
  have h85 : mid.regs 85 = size := by simp [mid]
  by_cases hlt : space < size
  · let out := { mid with regs := Function.update mid.regs 79 size }
    have ha : Runs w p ω (.assign 79 (.reg 85)) mid .normal out 2 :=
      runs_assign_iff.mpr ⟨size, by simp [Expr.eval, h85], rfl, rfl, rfl⟩
    have hc : Runs w p ω (.cond (.bin .lt (.reg 79) (.reg 85)) (.assign 79 (.reg 85)) .nop)
        mid .normal out 6 :=
      runs_cond_iff.mpr ⟨1, 2, by
        simp [Expr.eval, BinOp.eval, h79, h85, hlt, show w ≠ 0 by (intro he; simp [he] at hw)],
        ha, rfl⟩
    exact ⟨out, 13, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr, hc, rfl⟩),
      by simp [out, max_eq_right hlt.le, size],
      fun r hr79 hr85 => by simp [out, mid, Function.update_of_ne, hr79, hr85], rfl, rfl, le_rfl⟩
  · have hc : Runs w p ω (.cond (.bin .lt (.reg 79) (.reg 85)) (.assign 79 (.reg 85)) .nop)
        mid .normal mid 5 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, h79, h85, hlt],
        runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨mid, 12, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 5, hr, hc, rfl⟩),
      h79.trans (max_eq_left (Nat.le_of_not_gt hlt)).symm,
      fun r _ hr85 => by simp [mid, Function.update_of_ne, hr85], rfl, rfl, by decide⟩

/-- Set the runtime read reserve before storing the two parameter records. -/
@[expose] def installMinRatioRuntimeHeader : Stmt :=
  setMinRatioReadSpace ;; allocateMinRatioInitHeader

/-- The resulting header supplies the exact numeric format and a read
reserve that covers both the tool and the fixed-point edge record. -/
theorem installMinRatioRuntimeHeader_runs
    {w heap m V depth branch psi alphaPtr quality epsilon limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 7 = heap)
    (hm : st.regs 0 = m) (hV : st.regs 1 = V) (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch) (hpsi : st.regs 6 = psi) (ha : st.regs 4 = alphaPtr)
    (hq : st.regs 72 = quality) (he : st.regs 73 = epsilon)
    (hL : st.regs 2 = limbs) (hP : st.regs 3 = precision)
    (hs : st.regs 78 = searchSpace) (hr : st.regs 79 = readSpace)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 17 < 2 ^ w)
    (hreadRoom : 2 + 4 * limbs < 2 ^ w) :
    ∃ out c, Runs w p ω installMinRatioRuntimeHeader st .normal out c ∧
      out.regs 74 = heap ∧ out.regs 77 = heap + 17 ∧
      ChainInitParametersAt out.mem heap m V depth branch psi alphaPtr quality epsilon ∧
      MinRatioNumericHeaderAt out.mem heap limbs precision searchSpace
        (max readSpace (2 + 4 * limbs)) ∧
      (∀ a < heap + 5, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + 17) ∧
      (∀ r, r ≠ 74 → r ≠ 77 → r ≠ 79 → r ≠ 85 → out.regs r = st.regs r) ∧
      out.pos = st.pos ∧ c ≤ 93 := by
  obtain ⟨mid, c, hstep, hread, hkeep, hmem, hpos, hc⟩ :=
    setMinRatioReadSpace_runs (w := w) (p := p) (ω := ω) hL hr (by omega) hreadRoom
  obtain ⟨out, hrun, hhandle, hheap, hchain, hnum, hframe, hfree, hregs, hpos'⟩ :=
    allocateMinRatioInitHeader_runs (ω := ω) ((hkeep 7 (by decide) (by decide)).trans hh)
      ((hkeep 0 (by decide) (by decide)).trans hm) ((hkeep 1 (by decide) (by decide)).trans hV)
      ((hkeep 75 (by decide) (by decide)).trans hd) ((hkeep 76 (by decide) (by decide)).trans hb)
      ((hkeep 6 (by decide) (by decide)).trans hpsi) ((hkeep 4 (by decide) (by decide)).trans ha)
      ((hkeep 72 (by decide) (by decide)).trans hq) ((hkeep 73 (by decide) (by decide)).trans he)
      ((hkeep 2 (by decide) (by decide)).trans hL) ((hkeep 3 (by decide) (by decide)).trans hP)
      ((hkeep 78 (by decide) (by decide)).trans hs) hread (hmem.symm ▸ hz) hroom
  exact ⟨out, c + 80, runs_seq_iff.mpr (Or.inr ⟨mid, c, 79, hstep, hrun, by omega⟩),
    hhandle, hheap, hchain, hnum, fun a ha => (hframe a ha).trans (congrFun hmem a),
    hfree, fun r h74 h77 h79 h85 => (hregs r h74 h77).trans (hkeep r h79 h85),
    hpos'.trans hpos, by omega⟩

/-- Load the two Init records while keeping the operation arguments in
their original registers. The handle is the first argument. -/
@[expose] def loadMinRatioOperationParameters : Stmt :=
  .assign 74 (.reg 0) ;; loadMinRatioNumericFormat ;; loadChainInitParameters

/-- A single fixed entry prefix reloads the configured chain and its
fixed-point format from the handle in 62 steps. -/
theorem loadMinRatioOperationParameters_runs
    {w handle m V depth branch psi alphaPtr quality epsilon limbs precision searchSpace readSpace : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 0 = handle)
    (hn : MinRatioNumericHeaderAt st.mem handle limbs precision searchSpace readSpace)
    (hc : ChainInitParametersAt st.mem handle m V depth branch psi alphaPtr quality epsilon)
    (hroom : handle + 16 < 2 ^ w) :
    ∃ out, Runs w p ω loadMinRatioOperationParameters st .normal out 62 ∧
      out.regs 74 = handle ∧ out.regs 67 = limbs ∧ out.regs 68 = precision ∧
      out.regs 88 = m ∧ out.regs 89 = V ∧ out.regs 75 = depth ∧ out.regs 76 = branch ∧
      out.regs 90 = psi ∧ out.regs 91 = alphaPtr ∧ out.regs 72 = quality ∧ out.regs 73 = epsilon ∧
      (∀ r < 67, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let ready := { st with regs := Function.update st.regs 74 handle }
  have hsave : Runs w p ω (.assign 74 (.reg 0)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  obtain ⟨mid, hr, hL, hP, hregs, hmem, hpos⟩ :=
    loadMinRatioNumericFormat_runs (w := w) (p := p) (ω := ω) (st := ready)
      (by simpa [ready] using hh) hn (by omega)
  have h74 : mid.regs 74 = handle := (hregs 74 (by decide) (by decide)).trans (by simp [ready])
  obtain ⟨out, hrun, hm, hV, hd, hb, hpsi, ha, hq, he, hkeep, hmem', hpos'⟩ :=
    loadChainInitParameters_runs (ω := ω) h74 (hmem.symm ▸ hc) hroom
  have h74' := hkeep 74 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hL' := hkeep 67 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hP' := hkeep 68 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  refine ⟨out, ?_, h74'.trans h74, hL'.trans hL, hP'.trans hP,
    hm, hV, hd, hb, hpsi, ha, hq, he, ?_, hmem'.trans hmem, hpos'.trans hpos⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 2, 59, hsave,
      runs_seq_iff.mpr (Or.inr ⟨mid, 11, 47, hr, hrun, rfl⟩), rfl⟩)
  · intro r hl
    exact (hkeep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)).trans ((hregs r (by omega) (by omega)).trans
      (by simp [ready, Function.update_of_ne (show r ≠ 74 by omega)]))

end MinCostFlow.MinRatio
