module

public import MinCostFlow.MinRatio.InitThresholdDimensions
public import MinCostFlow.MinRatio.InitLevels

/-!
# Path evaluation for the rebuild thresholds

The path pair uses scratch registers that also hold chain inputs.
Save those inputs across the path pair and advance to its returned heap cursor.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Run the paired path enclosures with the chain inputs saved. -/
@[expose] def initRebuildPathPair
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg : ℕ) : Stmt :=
  saveRebuildPathInputs ;;
  computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c
    decK thr coeffLo coeffHi coeffBits cDeg ;;
  restoreRebuildPathInputs

/-- The path-pair handoff restores the threshold inputs, keeps the four
path endpoints, and passes the fresh cursor to the integer table writer. -/
theorem initRebuildPathPair_runs
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg
      budget heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {post : State → Prop}
    (hpath : ∀ ready, ready.mem = st.mem →
      (∀ r < 130, ready.regs r = st.regs r) →
      ∃ mid cost, Runs w p ω
        (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c
          decK thr coeffLo coeffHi coeffBits cDeg) ready .normal mid cost ∧
        post mid ∧ heap ≤ mid.regs 99 ∧ ZeroFrom mid.mem (mid.regs 99) ∧
        (∀ x < heap, mid.mem x = ready.mem x) ∧ cost ≤ budget) :
    ∃ out mid cost, Runs w p ω
      (initRebuildPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
        coeffLo coeffHi coeffBits cDeg) st .normal out cost ∧ post mid ∧
      out.regs 14 = st.regs 14 ∧ out.regs 44 = st.regs 44 ∧
      out.regs 47 = st.regs 47 ∧ out.regs 48 = st.regs 48 ∧ out.regs 92 = st.regs 92 ∧
      out.regs 98 = mid.regs 99 ∧ heap ≤ out.regs 98 ∧ ZeroFrom out.mem (out.regs 98) ∧
      out.mem = mid.mem ∧ (∀ x < heap, out.mem x = st.mem x) ∧
      (∀ r, r ≠ 14 → r ≠ 44 → r ≠ 47 → r ≠ 48 → r ≠ 92 → r ≠ 98 →
        out.regs r = mid.regs r) ∧ cost ≤ budget + 33 := by
  obtain ⟨ready, hr₁, h130, h131, h132, h133, h134, hm, hf⟩ :=
    saveRebuildPathInputs_runs (w := w) (p := p) (ω := ω) (st := st)
  obtain ⟨mid, c₀, hr₂, hp, hheap, hz, hframe, hc⟩ :=
    hpath ready hm (fun r hr => hf r (by omega) (by omega) (by omega) (by omega) (by omega))
  obtain ⟨out, hr₃, h14, h44, h47, h48, h92, h98, hm', hf'⟩ :=
    restoreRebuildPathInputs_runs (w := w) (p := p) (ω := ω) (st := mid)
  have hsave {r : ℕ} (hr : 130 ≤ r) :=
    computeInitSparsifierPathPair_preserves_saved hr hr₂
  refine ⟨out, mid, c₀ + 33, ?_, hp,
    h14.trans ((hsave (by decide)).trans h130), h44.trans ((hsave (by decide)).trans h131),
    h47.trans ((hsave (by decide)).trans h132), h48.trans ((hsave (by decide)).trans h133),
    h92.trans ((hsave (by decide)).trans h134), h98, h98.symm ▸ hheap, ?_, hm',
    fun x hx => (congrFun hm' x).trans ((hframe x hx).trans (congrFun hm x)), hf', by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 14, c₀ + 18, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨mid, c₀, 17, hr₂, hr₃, by omega⟩), by omega⟩)
  · rw [hm', h98]
    exact hz

/-- Generate the path enclosures and then write the integer rebuild
table at the returned heap cursor. -/
@[expose] def initIntegerThresholdsAfterPathPair
    (qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient : ℕ) : Stmt :=
  initRebuildPathPair qEntry bits load log pack exp shiftEntry Kγ c
    decK thr coeffLo coeffHi coeffBits cDeg ;;
  initIntegerThresholdsFromPathBounds power clog bits load log pack coefficient

/-- The integer table writer preserves memory below the path pair's
returned cursor. The composed initializer therefore preserves memory
below the original cursor and charges one sequencing step. -/
theorem initIntegerThresholdsAfterPathPair_runs
    {w qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient pathCost tableBudget heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready : State} {post : State → Prop}
    (hpath : Runs w p ω
      (initRebuildPathPair qEntry bits load log pack exp shiftEntry Kγ c
        decK thr coeffLo coeffHi coeffBits cDeg) st .normal ready pathCost)
    (hheap : heap ≤ ready.regs 98)
    (hpathFrame : ∀ x < heap, ready.mem x = st.mem x)
    (htable : ∃ out cost, Runs w p ω
        (initIntegerThresholdsFromPathBounds power clog bits load log pack coefficient)
        ready .normal out cost ∧
      post out ∧ (∀ x < ready.regs 98, out.mem x = ready.mem x) ∧ cost ≤ tableBudget) :
    ∃ out cost, Runs w p ω
      (initIntegerThresholdsAfterPathPair qEntry power clog bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st .normal out cost ∧
      post out ∧ (∀ x < heap, out.mem x = st.mem x) ∧ cost ≤ pathCost + tableBudget + 1 := by
  obtain ⟨out, cost, hr, hpost, hf, hc⟩ := htable
  exact ⟨out, pathCost + cost + 1, runs_seq_iff.mpr (Or.inr ⟨ready, pathCost, cost, hpath, hr, rfl⟩),
    hpost, fun x hx => (hf x (hx.trans_le hheap)).trans (hpathFrame x hx),
    Nat.add_le_add_right (Nat.add_le_add_left hc pathCost) 1⟩

/-- Combine the path and coefficient enclosure budgets before choosing
the working precision. Register 37 supplies the sparse-core logarithm input. -/
@[expose] def stageRebuildWorkspaceBudgets (coefficient : ℕ) : Stmt :=
  .assign 35 (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 36) (.reg 35)))
    (.const (65536 * coefficient + 4))) ;;
  .assign 36 (.bin .add (.bin .mul (.reg 36) (.reg 36))
    (.bin .add (.reg 37) (.const (2 * coefficient + 5))))

/-- The two resulting words dominate the coefficient, path and logarithm
bounds used by the integer threshold writer. -/
theorem stageRebuildWorkspaceBudgets_runs
    {w coefficient pathBound pathErr input : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : st.regs 36 = pathBound) (he : st.regs 35 = pathErr)
    (hi : st.regs 37 = input) :
    let err := 2 * (pathBound * pathErr) + (65536 * coefficient + 4)
    let bound := pathBound * pathBound + (input + (2 * coefficient + 5))
    err < 2 ^ w → bound < 2 ^ w →
    ∃ out, Runs w p ω (stageRebuildWorkspaceBudgets coefficient) st .normal out 17 ∧
      out.regs 35 = err ∧ out.regs 36 = bound ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 35 → r ≠ 36 → out.regs r = st.regs r) ∧
      65536 * coefficient + 2 ≤ err ∧ 2 * pathBound * pathErr + 2 ≤ err ∧
      2 * coefficient + 2 ≤ bound ∧ pathBound ^ 2 ≤ bound ∧ input + 3 ≤ bound := by
  dsimp only
  intro herr hbound
  let err := 2 * (pathBound * pathErr) + (65536 * coefficient + 4)
  let bound := pathBound * pathBound + (input + (2 * coefficient + 5))
  have htwo : 2 < 2 ^ w := by omega
  have hec : 65536 * coefficient + 4 < 2 ^ w := by omega
  have hbc : 2 * coefficient + 5 < 2 ^ w := by omega
  let mid := {st with regs := Function.update st.regs 35 err}
  let out := {mid with regs := Function.update mid.regs 36 bound}
  have hr₁ : Runs w p ω (.assign 35 (.bin .add
      (.bin .mul (.const 2) (.bin .mul (.reg 36) (.reg 35)))
      (.const (65536 * coefficient + 4)))) st .normal mid 8 := by
    apply runs_assign_iff.mpr
    refine ⟨err, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, hb, he, htwo, hec, err, herr,
      show pathBound * pathErr < 2 ^ w by omega,
      show 2 * (pathBound * pathErr) < 2 ^ w by omega]
  have hr₂ : Runs w p ω (.assign 36 (.bin .add (.bin .mul (.reg 36) (.reg 36))
      (.bin .add (.reg 37) (.const (2 * coefficient + 5))))) mid .normal out 8 := by
    apply runs_assign_iff.mpr
    refine ⟨bound, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, mid, hb, hi, hbc, bound, hbound,
      show pathBound * pathBound < 2 ^ w by omega,
      show input + (2 * coefficient + 5) < 2 ^ w by omega]
  refine ⟨out, ?_, by simp [out, mid, err], by simp [out, bound], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 8, 8, hr₁, hr₂, by decide⟩)
  · intro r h35 h36
    simp [out, mid, h35, h36]
  all_goals (try simp only [pow_two, Nat.mul_assoc]); omega

/-- Select the aligned working precision, evaluate both path bounds, and write the
integer rebuild thresholds in the chain header. -/
@[expose] def initRebuildThresholdsFromBudgets
    (h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient : ℕ) : Stmt :=
  initRebuildLogWorkspace clog bits h ;;
  initIntegerThresholdsAfterPathPair qEntry power clog bits load log pack exp shiftEntry
    Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient

/-- Composing workspace selection with the path and table stages preserves the
memory below the initializer's original heap cursor. -/
theorem initRebuildThresholdsFromBudgets_runs
    {w h qEntry power clog bitsEntry load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient M N depth L buckets degree err bound budget : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {post : State → Prop}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hbit : MeetsContract w p bitsEntry Num.IPM.bitLengthContract)
    (hh : 0 < h)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (h75 : st.regs 75 = depth) (h44 : st.regs 44 = L)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (hbuckets : 0 < buckets) (hb : 0 < bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let coarse := Chain.concreteThresholdScale depth
    let bits := growthWorkingBits L cap coarse (max err (4096 * (input + 2))) bound
    let precision := (bits + (h - 1)) / h * h
    let limbs := precision + range + 4
    precision < w →
    (∀ ready : State, ready.regs 68 = precision → ready.regs 67 = limbs →
      ready.regs 4 = 2 ^ precision → bits ≤ precision →
      max 16 (range + 11) ≤ precision → precision < bits + h → h ∣ precision →
      ready.mem = st.mem →
      (∀ r, r ≠ 4 → r ≠ 24 → r ≠ 57 → r ≠ 67 → r ≠ 68 →
        r ≠ 124 → r ≠ 126 → r ≠ 127 → r < 27 ∨ 38 < r → ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω
        (initIntegerThresholdsAfterPathPair qEntry power clog bitsEntry load log pack exp shiftEntry
          Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) ready .normal out cost ∧
        post out ∧ (∀ x < ready.regs 98, out.mem x = ready.mem x) ∧ cost ≤ budget) →
    ∃ out cost, Runs w p ω
      (initRebuildThresholdsFromBudgets h qEntry power clog bitsEntry load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st .normal out cost ∧
      post out ∧ (∀ x < st.regs 98, out.mem x = st.mem x) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L +
        40 * bits + 14 * range + 224 + budget + 1 := by
  dsimp only
  intro hwidth hcontinue
  obtain ⟨ready, workspaceCost, hrun, hprecision, hlimbs, hscale, hbits, haccuracy,
    halign, hdvd, hmem, hregs, hcost⟩ :=
    initRebuildLogWorkspace_runs (ω := ω) hp hbit hh hM hN hMpos h75 h44 h47 h48
      h35 h36 hbuckets hb hwidth
  obtain ⟨out, cost, hout, hpost, hframe, hbudget⟩ :=
    hcontinue ready hprecision hlimbs hscale hbits haccuracy halign hdvd hmem hregs
  have hheap := hregs 98 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Or.inr (by decide))
  exact ⟨out, workspaceCost + cost + 1,
    runs_seq_iff.mpr (Or.inr ⟨ready, workspaceCost, cost, hrun, hout, rfl⟩),
    hpost, fun x hx => (hframe x (hheap.symm ▸ hx)).trans (congrFun hmem x),
    Nat.add_le_add_right (Nat.add_le_add hcost hbudget) 1⟩

/-- The sparsifier depth stage leaves the padded edge count in register
23. Use it to form the sparse-core logarithm input. -/
@[expose] def stageRebuildBudgetLogInput : Stmt :=
  .assign 37 (.bin .mul (.reg 23)
    (.bin .add (.bin .mul (.const 2) (.reg 23)) (.const 60)))

/-- The logarithm input is the sum of the core vertex and edge bounds. -/
theorem stageRebuildBudgetLogInput_runs
    {w m : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hm : st.regs 23 = m) (hpos : 0 < m)
    (hfit : SparseCore.coreNMax m + m < 2 ^ w) :
    ∃ out, Runs w p ω stageRebuildBudgetLogInput st .normal out 8 ∧
      out.regs 37 = SparseCore.coreNMax m + m ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 37 → out.regs r = st.regs r) := by
  have he : m * (2 * m + 60) = SparseCore.coreNMax m + m := by
    unfold SparseCore.coreNMax SparseCore.coreSplitMax
    ring
  have hmul : m * (2 * m + 60) < 2 ^ w := he.symm ▸ hfit
  have hlinear := (Nat.le_mul_of_pos_left (2 * m + 60) hpos).trans_lt hmul
  let out := {st with regs := Function.update st.regs 37 (SparseCore.coreNMax m + m)}
  refine ⟨out, ?_, by simp [out], rfl, fun r hr => by simp [out, hr]⟩
  apply runs_assign_iff.mpr
  refine ⟨_, ?_, rfl, rfl, rfl⟩
  simp [Expr.eval, hm, show 2 < 2 ^ w by omega, show 60 < 2 ^ w by omega,
    show 2 * m < 2 ^ w by omega, hlinear, he, hfit]

/-- Derive the enclosure budgets from the path bounds before
selecting the precision and constructing the rebuild table. -/
@[expose] def initRebuildThresholds
    (h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient : ℕ) : Stmt :=
  stageRebuildBudgetLogInput ;;
  stageRebuildWorkspaceBudgets coefficient ;;
  initRebuildThresholdsFromBudgets h qEntry power clog bits load log pack exp shiftEntry
    Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient

/-- Budget staging preserves the heap and changes only registers 35 through 37.
It adds twenty-seven steps to threshold initialization. -/
theorem initRebuildThresholds_runs
    {w h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient pathBound pathErr m budget : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {post : State → Prop}
    (hb : st.regs 36 = pathBound) (he : st.regs 35 = pathErr)
    (hm : st.regs 23 = m) (hpos : 0 < m)
    (hfit : SparseCore.coreNMax m + m < 2 ^ w) :
    let input := SparseCore.coreNMax m + m
    let err := 2 * (pathBound * pathErr) + (65536 * coefficient + 4)
    let bound := pathBound * pathBound + (input + (2 * coefficient + 5))
    err < 2 ^ w → bound < 2 ^ w →
    (∀ ready : State, ready.regs 35 = err → ready.regs 36 = bound →
      ready.mem = st.mem → (∀ r, r ≠ 35 → r ≠ 36 → r ≠ 37 → ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω
        (initRebuildThresholdsFromBudgets h qEntry power clog bits load log pack exp shiftEntry
          Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) ready .normal out cost ∧
        post out ∧ (∀ x < ready.regs 98, out.mem x = ready.mem x) ∧ cost ≤ budget) →
    ∃ out cost, Runs w p ω
      (initRebuildThresholds h qEntry power clog bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st .normal out cost ∧
      post out ∧ (∀ x < st.regs 98, out.mem x = st.mem x) ∧ cost ≤ budget + 27 := by
  dsimp only
  intro herr hbound hcontinue
  obtain ⟨logInput, hlog, h37, hm₁, hf₁⟩ :=
    stageRebuildBudgetLogInput_runs (p := p) (ω := ω) hm hpos hfit
  obtain ⟨ready, hr, h35, h36, hm₂, hf₂, _⟩ :=
    stageRebuildWorkspaceBudgets_runs (p := p) (ω := ω)
      ((hf₁ 36 (by decide)).trans hb) ((hf₁ 35 (by decide)).trans he) h37 herr hbound
  have hf r h35' h36' h37' := (hf₂ r h35' h36').trans (hf₁ r h37')
  have hmem := hm₂.trans hm₁
  obtain ⟨out, cost, hout, hp, hframe, hc⟩ := hcontinue ready h35 h36 hmem hf
  have hheap := hf 98 (by decide) (by decide) (by decide)
  exact ⟨out, 8 + (17 + cost + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨logInput, 8, _, hlog,
    runs_seq_iff.mpr (Or.inr ⟨ready, 17, cost, hr, hout, rfl⟩), rfl⟩),
    hp, fun x hx => (hframe x (hheap.symm ▸ hx)).trans (congrFun hmem x), by omega⟩

/-- Check whether the statement leaves a register untouched. -/
@[expose] def avoidsRegister (r : ℕ) : Stmt → Bool
  | .assign dest _ | .rand dest | .call dest _ _ => decide (r ≠ dest)
  | .seq first rest | .cond _ first rest => avoidsRegister r first && avoidsRegister r rest
  | .loop _ body => avoidsRegister r body
  | _ => true

/-- A statement that avoids a register preserves its value. -/
theorem runs_preserves_register {w r : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st out : State} {o : Outcome} {c : ℕ}
    (hb : avoidsRegister r s = true)
    (h : Runs w p ω s st o out c) : out.regs r = st.regs r := by
  induction c using Nat.strong_induction_on generalizing s st out o with
  | h c ih =>
    cases s with
    | nop => exact congrArg (fun s : State => s.regs r) (runs_nop_iff.mp h).2.1
    | ret e =>
      obtain ⟨_, _, _, rfl, _⟩ := runs_ret_iff.mp h
      rfl
    | store a e =>
      obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h
      rfl
    | assign dest e =>
      obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp h
      have hd : r ≠ dest := of_decide_eq_true hb
      exact Function.update_of_ne hd _ _
    | rand dest =>
      obtain ⟨_, rfl, _⟩ := runs_rand_iff.mp h
      have hd : r ≠ dest := of_decide_eq_true hb
      exact Function.update_of_ne hd _ _
    | call dest f args =>
      obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp h
      have hd : r ≠ dest := of_decide_eq_true hb
      exact Function.update_of_ne hd _ _
    | seq s t =>
      have hboth : avoidsRegister r s = true ∧ avoidsRegister r t = true :=
        Bool.and_eq_true_iff.mp hb
      rcases runs_seq_iff.mp h with ⟨_, _, hs, _, hc⟩ | ⟨mid, _, _, hs, ht, hc⟩
      · exact ih _ (by omega) hboth.1 hs
      · exact (ih _ (by omega) hboth.2 ht).trans (ih _ (by omega) hboth.1 hs)
    | cond e s t =>
      have hboth : avoidsRegister r s = true ∧ avoidsRegister r t = true :=
        Bool.and_eq_true_iff.mp hb
      obtain ⟨v, d, _, ht, hc⟩ := runs_cond_iff.mp h
      apply ih d (by omega) _ ht
      split <;> tauto
    | loop e body =>
      have hbody : avoidsRegister r body = true := hb
      rcases runs_loop_iff.mp h with ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, ht, _, hc⟩ |
        ⟨mid, _, _, _, _, _, hs, ht, hc⟩
      · rfl
      · exact ih _ (by omega) hbody ht
      · exact (ih _ (by omega) hb ht).trans (ih _ (by omega) hbody hs)

/-- Rebuild threshold initialization preserves the saved solver limb
count and precision, as well as the saved alpha and penalty words. -/
theorem initRebuildThresholds_preserves_solver_arguments
    {w h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient cost r : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {o : Outcome}
    (hlo : 101 ≤ r) (hhi : r ≤ 104)
    (hr : Runs w p ω
      (initRebuildThresholds h qEntry power clog bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st o out cost) :
    out.regs r = st.regs r := by
  have hregs : r = 101 ∨ r = 102 ∨ r = 103 ∨ r = 104 := by omega
  rcases hregs with rfl | rfl | rfl | rfl <;>
    exact runs_preserves_register (by rfl) hr

/-- The threshold stages preserve the packed graph and both vector
pointers used by the initial level rebuild. -/
theorem initRebuildThresholds_preserves_root_pointers
    {w h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient cost r : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {o : Outcome}
    (hlo : 69 ≤ r) (hhi : r ≤ 71)
    (hr : Runs w p ω
      (initRebuildThresholds h qEntry power clog bits load log pack exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st o out cost) :
    out.regs r = st.regs r := by
  have hregs : r = 69 ∨ r = 70 ∨ r = 71 := by omega
  rcases hregs with rfl | rfl | rfl <;>
    exact runs_preserves_register (by rfl) hr

/-- Compute the integer bucket cap before choosing the rebuild workspace,
whose size depends on that cap. -/
@[expose] def initIntegerBucketAndRebuildThresholds
    (lsstConstant h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient : ℕ) : Stmt :=
  initConcreteIntegerBucketStage clog lsstConstant ;;
  initRebuildThresholds h qEntry power clog bits load log pack exp shiftEntry
    Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient

/-- The bucket stage supplies the exact cap and preserves the heap cursor
for the rebuild threshold stage. -/
theorem initIntegerBucketAndRebuildThresholds_runs
    {w lsstConstant h qEntry power clog bits load log pack exp shiftEntry Kγ c decK thr
      coeffLo coeffHi coeffBits cDeg coefficient width M N budget : ℕ}
    (hM : 1 ≤ M) {p : Program} {ω : ℕ → Bool} {st : State} {post : State → Prop}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h22 : st.regs 22 = M) (h92 : st.regs 92 = N)
    (h6 : st.regs 6 = width)
    (h75 : st.regs 75 = (Chain.concreteChainParams M hM).d)
    (h76 : st.regs 76 = (Chain.concreteChainParams M hM).k)
    (hvertices : 4 * M + 3 < 2 ^ w) :
    let P := Chain.concreteChainParams M hM
    let stretch := max 2 (Chain.concreteBucketStretch lsstConstant P.k (4 * M))
    let cap := Chain.concreteBucketCap lsstConstant width P.k P.d (4 * M)
    stretch + 1 < 2 ^ w → cap < 2 ^ w →
    (∀ ready : State, ready.regs 47 = cap →
      ready.regs 14 = Nat.clog 2 (4 * M + 2) →
      ready.mem = st.mem →
      (∀ r, r ∉ [14, 15, 16, 17, 18, 46, 47, 57, 99] → ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω
        (initRebuildThresholds h qEntry power clog bits load log pack exp shiftEntry
          Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) ready .normal out cost ∧
        post out ∧ (∀ x < ready.regs 98, out.mem x = ready.mem x) ∧ cost ≤ budget) →
    ∃ out cost, Runs w p ω
      (initIntegerBucketAndRebuildThresholds lsstConstant h qEntry power clog bits load log pack
        exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) st .normal out cost ∧
      post out ∧ (∀ x < st.regs 98, out.mem x = st.mem x) ∧
      cost ≤ 40 * (Nat.clog 2 (4 * M + 2) + Nat.clog 2 stretch) + 120 + budget + 1 := by
  dsimp only
  intro hstretch hcap hcontinue
  obtain ⟨ready, bucketCost, hr, hcap', hlog, _, _, _, hmem, hregs, hcost⟩ :=
    initConcreteIntegerBucketStage_runs (ω := ω) hM hp h22 h92 rfl h6 h75 h76 hvertices
      hstretch hcap
  obtain ⟨out, cost, hout, hpost, hframe, hbudget⟩ :=
    hcontinue ready hcap' hlog hmem hregs
  have hheap := hregs 98 (by decide)
  exact ⟨out, bucketCost + cost + 1, runs_seq_iff.mpr (Or.inr ⟨ready, bucketCost, cost, hr, hout, rfl⟩),
    hpost, fun x hx => (hframe x (hheap.symm ▸ hx)).trans (congrFun hmem x),
    Nat.add_le_add_right (Nat.add_le_add hcost hbudget) 1⟩

/-- After the integer bucket stage, select the sparsifier depth before
choosing the threshold workspace. The final continuation builds the levels. -/
@[expose] def solverInitWithIntegerThresholds
    (alpha select quality graphPack threshold b h clog lsstConstant qEntry power exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient : ℕ)
    (retry levels : Stmt) : Stmt :=
  solverInitWithIntegerBucket alpha select quality graphPack threshold b h clog lsstConstant retry
    (initThresholdsAfterBucketCap
      (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry) ;;
    initRebuildThresholds h qEntry power clog b (b + 1) (b + 6) (b + 3) exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient ;;
    levels)

/-- Successful runs of the numeric stages feed their resulting states to
level construction, with one step charged for each sequence. -/
theorem solverInitWithIntegerThresholds_runs
    {w alpha select quality graphPack threshold b h clog lsstConstant qEntry power exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient : ℕ}
    {inputCost bucketCost depthCost thresholdCost levelCost : ℕ}
    {p : Program} {ω : ℕ → Bool}
    {st ready bucket depth tables out : State} {retry levels : Stmt} {outcome : Outcome}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hb : Runs w p ω (prepareLinkedIntegerBucket threshold b h clog lsstConstant retry)
      ready .normal bucket bucketCost)
    (hd : Runs w p ω (initThresholdsAfterBucketCap
      (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry))
      bucket .normal depth depthCost)
    (ht : Runs w p ω
      (initRebuildThresholds h qEntry power clog b (b + 1) (b + 6) (b + 3) exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) depth .normal tables thresholdCost)
    (hl : Runs w p ω levels tables outcome out levelCost) :
    Runs w p ω
      (solverInitWithIntegerThresholds alpha select quality graphPack threshold b h clog lsstConstant
        qEntry power exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient retry levels)
      st outcome out (inputCost + bucketCost + depthCost + thresholdCost + levelCost + 4) := by
  have hlevels := runs_seq_iff.mpr (Or.inr ⟨tables, thresholdCost, levelCost, ht, hl, rfl⟩)
  have hrest := runs_seq_iff.mpr (Or.inr ⟨depth, depthCost, thresholdCost + levelCost + 1,
    hd, hlevels, rfl⟩)
  have hr := solverInitWithIntegerBucket_runs hi hb hrest
  simpa only [solverInitWithIntegerThresholds, Nat.add_assoc, show 1 + (1 + 2) = 4 by decide] using hr

/-- Start Algorithm 1 level construction at the first address after
the integer threshold table and restore the solver numeric format. -/
@[expose] def buildSolverInitLevelsAfterThresholds
    (init read forestOp copy sort cell terminalInit : ℕ) : Stmt :=
  .assign 77 (.reg 98) ;;
  .assign 67 (.reg 103) ;;
  .assign 68 (.reg 104) ;;
  buildSolverInitLevels init read forestOp copy sort cell terminalInit

/-- Moving the fresh cursor into the level initializer's heap register
and restoring the solver format preserves the threshold table. -/
theorem buildSolverInitLevelsAfterThresholds_runs
    {w init read forestOp copy sort cell terminalInit budget : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {post : State → Prop}
    (hlevels : ∀ ready : State, ready.regs 77 = st.regs 98 →
      ready.regs 67 = st.regs 103 → ready.regs 68 = st.regs 104 →
      ready.mem = st.mem →
      (∀ r, r ≠ 77 → r ≠ 67 → r ≠ 68 → ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω
        (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
        ready .normal out cost ∧ post out ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω
      (buildSolverInitLevelsAfterThresholds init read forestOp copy sort cell terminalInit)
      st .normal out cost ∧ post out ∧ cost ≤ budget + 9 := by
  let heapReady := {st with regs := Function.update st.regs 77 (st.regs 98)}
  let widthReady := {heapReady with regs := Function.update heapReady.regs 67 (st.regs 103)}
  let ready := {widthReady with regs := Function.update widthReady.regs 68 (st.regs 104)}
  have hstage : Runs w p ω (.assign 77 (.reg 98)) st .normal heapReady 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval], rfl, rfl, rfl⟩
  have hwidth : Runs w p ω (.assign 67 (.reg 103)) heapReady .normal widthReady 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, heapReady], rfl, rfl, rfl⟩
  have hprecision : Runs w p ω (.assign 68 (.reg 104)) widthReady .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, widthReady, heapReady], rfl, rfl, rfl⟩
  obtain ⟨out, cost, hr, hpost, hc⟩ := hlevels ready
    (by simp [ready, widthReady, heapReady]) (by simp [ready, widthReady])
    (by simp [ready]) rfl (fun r h77 h67 h68 => by simp [ready, widthReady, heapReady, h77, h67, h68])
  have hright := runs_seq_iff.mpr (Or.inr ⟨ready, 2, cost, hprecision, hr, rfl⟩)
  have hmid := runs_seq_iff.mpr (Or.inr ⟨widthReady, 2, 2 + cost + 1, hwidth, hright, rfl⟩)
  exact ⟨out, 2 + (2 + (2 + cost + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨heapReady, 2, _, hstage, hmid, rfl⟩), hpost, by omega⟩

/-- Reserving the descriptor tables and building the suffix leave the
solver's limb count and precision in the caller registers. -/
theorem buildSolverInitLevels_preserves_format
    {w init read forestOp copy sort cell terminalInit cost r : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {outcome : Outcome}
    (hr : 67 ≤ r) (hrhi : r ≤ 68)
    (hrun : Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st outcome out cost) :
    out.regs r = st.regs r := by
  have hrCases : r = 67 ∨ r = 68 := by omega
  rcases hrCases with rfl | rfl <;>
    exact runs_preserves_register (by rfl) hrun

/-- The initial rebuild keeps the threshold table address in the caller
register used to install the Detect descriptor. -/
theorem buildSolverInitLevelsAfterThresholds_preserves_table_address
    {w init read forestOp copy sort cell terminalInit cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {o : Outcome}
    (hr : Runs w p ω
      (buildSolverInitLevelsAfterThresholds init read forestOp copy sort cell terminalInit)
      st o out cost) :
    out.regs 83 = st.regs 83 :=
  runs_preserves_register (by rfl) hr

/-- A level run that preserves the memory below its fresh cursor also
preserves each threshold written before that cursor. -/
theorem buildSolverInitLevelsAfterThresholds_preserves_table
    {w init read forestOp copy sort cell terminalInit cost table depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {o : Outcome}
    (hr : Runs w p ω
      (buildSolverInitLevelsAfterThresholds init read forestOp copy sort cell terminalInit)
      st o out cost)
    (htable : st.regs 83 = table) (hheap : table + depth < st.regs 98)
    (hframe : ∀ a < st.regs 98, out.mem a = st.mem a) :
    out.regs 83 = table ∧ ∀ j ≤ depth, out.mem (table + j) = st.mem (table + j) :=
  ⟨(buildSolverInitLevelsAfterThresholds_preserves_table_address hr).trans htable,
    fun j hj => hframe (table + j) ((Nat.add_le_add_left hj table).trans_lt hheap)⟩

/-- Run the solver's numeric Init followed by the Algorithm 1 level builder. -/
@[expose] def solverInitWithIntegerThresholdLevels
    (alpha select quality graphPack threshold b h clog lsstConstant qEntry power exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient : ℕ)
    (retry : Stmt) (init read forestOp copy sort cell terminalInit : ℕ) : Stmt :=
  solverInitWithIntegerThresholds alpha select quality graphPack threshold b h clog lsstConstant
    qEntry power exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient retry
    (buildSolverInitLevelsAfterThresholds init read forestOp copy sort cell terminalInit)

/-- The solver entry passes the table state to the level builder that
restores the solver format and uses the table's returned heap. -/
theorem solverInitWithIntegerThresholdLevels_runs
    {w alpha select quality graphPack threshold b h clog lsstConstant qEntry power exp shiftEntry
      Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient : ℕ}
    {inputCost bucketCost depthCost thresholdCost levelCost init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {ω : ℕ → Bool}
    {st ready bucket depth tables out : State} {retry : Stmt}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hb : Runs w p ω (prepareLinkedIntegerBucket threshold b h clog lsstConstant retry)
      ready .normal bucket bucketCost)
    (hd : Runs w p ω (initThresholdsAfterBucketCap
      (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry))
      bucket .normal depth depthCost)
    (ht : Runs w p ω
      (initRebuildThresholds h qEntry power clog b (b + 1) (b + 6) (b + 3) exp shiftEntry
        Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient) depth .normal tables thresholdCost)
    (hl : Runs w p ω (buildSolverInitLevelsAfterThresholds init read forestOp copy sort cell terminalInit)
      tables .normal out levelCost) :
    Runs w p ω
      (solverInitWithIntegerThresholdLevels alpha select quality graphPack threshold b h clog lsstConstant
        qEntry power exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg coefficient retry init read forestOp copy sort cell terminalInit)
      st .normal out (inputCost + bucketCost + depthCost + thresholdCost + levelCost + 4) :=
  solverInitWithIntegerThresholds_runs hi hb hd ht hl

end MinCostFlow.MinRatio
