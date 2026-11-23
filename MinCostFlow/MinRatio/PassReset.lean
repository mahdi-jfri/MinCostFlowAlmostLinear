module

public import WordRAM.Logic
public import MinCostFlow.Chain.Algorithm2
import MinCostFlow.Chain.Algorithm2Uncond

/-!
# Resetting pass counters

Algorithm 2 (page 29) clears the counters strictly above a shifted level
and clears the counters from the rebuilt level onward. Both operations
clear a suffix of the same table.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Register 0 is the table base, register 1 the first index to clear,
and register 2 the exclusive end. -/
@[expose] def resetPassSuffix : Stmt :=
  forRange 19 (.reg 1) (.reg 2)
    (.store (.bin .add (.reg 0) (.reg 19)) (.const 0))

theorem resetPassSuffix_noRand : resetPassSuffix.NoRand := by
  simp [resetPassSuffix, forRange, forUp, Stmt.NoRand]

/-- The pass-table suffix is zeroed in fourteen steps per counter plus
seven fixed steps. Every address outside the suffix is preserved. -/
theorem resetPassSuffix_runs {w base first stop : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (hbase : st.regs 0 = base) (hfirst : st.regs 1 = first) (hstop : st.regs 2 = stop)
    (horder : first ≤ stop) (hbound : base + stop < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (stop - first) + 7 ∧
      (∀ a, out.mem a = if base + first ≤ a ∧ a < base + stop then 0 else st.mem a) ∧
      (∀ r ≠ 19, out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let Inv := fun i (s : State) =>
    s.regs 19 = i ∧ (∀ r ≠ 19, s.regs r = st.regs r) ∧ s.pos = st.pos ∧
      (∀ a, s.mem a = if base + first ≤ a ∧ a < base + i then 0 else st.mem a)
  have hstep : ∀ i, first ≤ i → i < stop →
      Triple w p (Inv i) (.store (.bin .add (.reg 0) (.reg 19)) (.const 0))
        (normalPost fun s' => Inv (i + 1) { s' with regs := Function.update s'.regs 19 (i + 1) } ∧
          s'.regs 19 = i) (fun _ => 5) := by
    intro i hil hir s bits hs
    obtain ⟨hi, hregs, hpos, hm⟩ := hs
    let out := { s with mem := Function.update s.mem (base + i) 0 }
    have haddr : base + i < 2 ^ w := by omega
    have hrun : Runs w p bits (.store (.bin .add (.reg 0) (.reg 19)) (.const 0))
        s .normal out 5 :=
      runs_store_iff.mpr ⟨base + i, 0, by
        simp [Expr.eval, BinOp.eval, hi, (hregs 0 (by decide)).trans hbase, haddr],
        by simp [Expr.eval], rfl, rfl, rfl⟩
    refine ⟨.normal, out, 5, hrun, ⟨⟨by simp [out], ?_, hpos, ?_⟩, hi⟩, le_rfl⟩
    · intro r hr
      simpa [out, Function.update_of_ne hr] using hregs r hr
    · intro a
      change Function.update s.mem (base + i) 0 a = _
      by_cases ha : a = base + i
      · subst a
        simp [show base + first ≤ base + i by omega, show base + i < base + (i + 1) by omega]
      · rw [Function.update_of_ne ha, hm]
        have he : (base + first ≤ a ∧ a < base + i) ↔
            (base + first ≤ a ∧ a < base + (i + 1)) := by omega
        simp only [he]
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 19) (lo := .reg 1) (hi := .reg 2) 5 first stop horder hw (fun _ => by omega)
    (by
      intro s hs
      subst s
      refine ⟨by simp [Expr.eval, hfirst], by simp, ?_, rfl, ?_⟩
      · intro r hr
        simp [Function.update_of_ne hr]
      · intro a
        simp [show ¬ (base + first ≤ a ∧ a < base + first) by omega])
    (fun _ _ _ _ hs => hs.1)
    (fun _ s _ _ hs => by simp [Expr.eval, (hs.2.1 2 (by decide)).trans hstop])
    hstep
  obtain ⟨o, out, cost, hr, hn, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hn
  | normal =>
    exact ⟨out, cost, hr, by simpa [Expr.size, Nat.mul_comm] using hc,
      hn.2.2.2, hn.2.1, hn.2.2.1⟩

/-- Register 3 is the branch-wrap bit. Increment the selected pass count
before clearing the strictly deeper levels. -/
@[expose] def incrementWrappedPass : Stmt :=
  .cond (.reg 3)
    (.store (.bin .add (.reg 0) (.reg 1))
      (.bin .add (.load (.bin .add (.reg 0) (.reg 1))) (.const 1))) .nop

/-- The shifts of Algorithm 2 (page 29) update the pass table with the
same wrap decision as the branch advance. -/
@[expose] def advanceShiftPasses : Stmt :=
  incrementWrappedPass ;;
  .assign 1 (.bin .add (.reg 1) (.const 1)) ;;
  resetPassSuffix

theorem advanceShiftPasses_noRand : advanceShiftPasses.NoRand := by
  simp [advanceShiftPasses, incrementWrappedPass, resetPassSuffix_noRand, Stmt.NoRand]

private theorem incrementWrappedPass_runs {w base i count : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (wrapped : Bool)
    (hb : st.regs 0 = base) (hi : st.regs 1 = i)
    (hwrap : st.regs 3 = if wrapped then 1 else 0)
    (hcount : st.mem (base + i) = count) (haddr : base + i < 2 ^ w)
    (hword : wrapped = true → count + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω incrementWrappedPass st .normal out cost ∧ cost ≤ 12 ∧
      out.regs = st.regs ∧ out.pos = st.pos ∧
      out.mem = (if wrapped then Function.update st.mem (base + i) (count + 1) else st.mem) := by
  cases wrapped with
  | false =>
    have he : (Expr.reg 3).eval w st = some 0 := by simp [Expr.eval, hwrap]
    exact ⟨st, 3, runs_cond_iff.mpr ⟨0, 1, he, by
      simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
      by decide, rfl, rfl, rfl⟩
  | true =>
    let out := { st with mem := Function.update st.mem (base + i) (count + 1) }
    have he : (Expr.reg 3).eval w st = some 1 := by simp [Expr.eval, hwrap]
    have ha : (Expr.bin .add (.reg 0) (.reg 1)).eval w st = some (base + i) := by
      simp [Expr.eval, BinOp.eval, hb, hi, haddr]
    have hv : (Expr.bin .add (.load (.bin .add (.reg 0) (.reg 1))) (.const 1)).eval w st =
        some (count + 1) := by
      simp [Expr.eval, BinOp.eval, hb, hi, haddr, hcount, hw, hword rfl]
    have hr : Runs w p ω
        (.store (.bin .add (.reg 0) (.reg 1))
          (.bin .add (.load (.bin .add (.reg 0) (.reg 1))) (.const 1))) st .normal out 10 :=
      runs_store_iff.mpr ⟨base + i, count + 1, ha, hv, rfl, rfl, rfl⟩
    exact ⟨out, 12, runs_cond_iff.mpr ⟨1, 10, he, by simpa using hr, rfl⟩,
      le_rfl, rfl, rfl, rfl⟩

/-- The selected pass count is incremented only on wrap. Every deeper
counter is cleared, with fourteen steps charged to each reset. -/
theorem advanceShiftPasses_runs {w base i stop count : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (wrapped : Bool)
    (hb : st.regs 0 = base) (hi : st.regs 1 = i) (hend : st.regs 2 = stop)
    (hwrap : st.regs 3 = if wrapped then 1 else 0)
    (hcount : st.mem (base + i) = count)
    (hil : i < stop) (hbound : base + stop < 2 ^ w) (hw : 1 < 2 ^ w)
    (hword : wrapped = true → count + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω advanceShiftPasses st .normal out cost ∧
      cost ≤ 14 * (stop - (i + 1)) + 25 ∧
      (∀ a, out.mem a = if base + (i + 1) ≤ a ∧ a < base + stop then 0
        else if a = base + i ∧ wrapped then count + 1 else st.mem a) ∧ out.pos = st.pos := by
  obtain ⟨mid, c₁, hinc, hc₁, hregs, hpos, hmem⟩ :=
    incrementWrappedPass_runs (ω := ω) wrapped hb hi hwrap hcount (by omega) hword hw
  let start := { mid with regs := Function.update mid.regs 1 (i + 1) }
  have hstart : Runs w p ω (.assign 1 (.bin .add (.reg 1) (.const 1))) mid .normal start 4 :=
    runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, hregs, hi, hw,
      show i + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨out, c₂, hr, hc₂, hreset, _, hpos'⟩ := resetPassSuffix_runs (ω := ω) (st := start)
    (base := base) (first := i + 1) (stop := stop)
    (by simp [start, Function.update_of_ne, hregs, hb]) (by simp [start])
    (by simp [start, Function.update_of_ne, hregs, hend]) (by omega) hbound hw
  refine ⟨out, c₁ + (4 + c₂ + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨mid, c₁, _, hinc,
      runs_seq_iff.mpr (Or.inr ⟨start, 4, c₂, hstart, hr, rfl⟩), rfl⟩),
    by omega, ?_, hpos'.trans hpos⟩
  intro a
  rw [hreset a]
  change (if _ then 0 else mid.mem a) = _
  rw [hmem]
  cases wrapped <;> by_cases hn : a = base + i <;>
    simp [hn, Function.update_of_ne]

/-- Algorithm 2 (page 29) preserves the passes before the selected level, advances the
selected pass on branch wrap, and clears the passes at deeper levels. -/
theorem advanceShiftPasses_table_runs {w base levels : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (i : Fin levels) (passes : Fin levels → ℕ) (wrapped : Bool)
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = levels)
    (hwrap : st.regs 3 = if wrapped then 1 else 0)
    (htable : ∀ j, st.mem (base + j.val) = passes j)
    (hbound : base + levels < 2 ^ w) (hw : 1 < 2 ^ w)
    (hword : wrapped = true → passes i + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω advanceShiftPasses st .normal out cost ∧
      cost ≤ 14 * (levels - (i.val + 1)) + 25 ∧ out.pos = st.pos ∧
      (∀ a, (a < base + i.val ∨ base + levels ≤ a) → out.mem a = st.mem a) ∧
      ∀ j : Fin levels, out.mem (base + j.val) =
        if i < j then 0
        else if j = i then (if wrapped then passes i + 1 else passes i)
        else passes j := by
  obtain ⟨out, cost, hr, hc, hm, hp⟩ :=
    advanceShiftPasses_runs (ω := ω) wrapped hb hi hend hwrap (htable i)
      i.isLt hbound hw hword
  refine ⟨out, cost, hr, hc, hp, ?_, fun j => ?_⟩
  · intro a ha
    have hnone : ¬ (base + (i.val + 1) ≤ a ∧ a < base + levels) := by omega
    have hne : a ≠ base + i.val := by
      have := i.isLt
      omega
    simp [hm, hnone, hne]
  · rw [hm, htable j]
    have hdeep : (base + (i.val + 1) ≤ base + j.val ∧
        base + j.val < base + levels) ↔ i < j := by
      change (_ ∧ _) ↔ i.val < j.val
      have := j.isLt
      omega
    simp only [hdeep, Nat.add_right_inj]
    by_cases hj : j = i
    · subst j
      simp
    · have hval : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp [hj, hval]

/-- Algorithm 2 (page 29) resets every pass from the first rebuilt level onward. -/
theorem resetRebuiltPasses_table_runs {w base levels : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (first : Fin levels) (passes : Fin levels → ℕ)
    (hb : st.regs 0 = base) (hfirst : st.regs 1 = first.val) (hend : st.regs 2 = levels)
    (htable : ∀ j, st.mem (base + j.val) = passes j)
    (hbound : base + levels < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (levels - first.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin levels, out.mem (base + j.val) = if first ≤ j then 0 else passes j := by
  obtain ⟨out, cost, hr, hc, hm, _, hp⟩ :=
    resetPassSuffix_runs (ω := ω) hb hfirst hend first.isLt.le hbound hw
  refine ⟨out, cost, hr, hc, hp, fun j => ?_⟩
  have hreset : (base + first.val ≤ base + j.val ∧ base + j.val < base + levels)
      ↔ first ≤ j := by
    change (_ ∧ _) ↔ first.val ≤ j.val
    have := j.isLt
    omega
  simp only [hm, htable, hreset]

private theorem firstRebuiltLevel_increment (d i : ℕ) (counts : ℕ → ℕ) :
    Chain.firstRebuiltLevel d counts
      (fun j => if j = i then counts i + 1 else counts j) =
        if i < d then some i else none := by
  by_cases hi : i < d
  · simpa only [ite_eq_left hi] using Chain.firstRebuiltLevel_eq_of_inc hi counts
  · rw [ite_eq_right hi]
    unfold Chain.firstRebuiltLevel
    apply List.find?_eq_none.mpr
    intro j hj
    have hlt := List.mem_range.mp hj
    have hne : j ≠ i := by omega
    simp [hne]

/-- The Algorithm 2 scan returns the level passed to Algorithm 1's rebuild when
that level is below the terminal one (Algorithms 1 and 2, pages 20 and 29). -/
theorem firstRebuiltLevel_algorithm1_rebuild {T : Chain.SparseCoreRestartTool}
    {L : Chain.LastLevelTool} {P : Chain.ChainParams} (st : Chain.ChainState T P)
    (i : ℕ) (G : MGraph) (extraEnc : ℕ) :
    Chain.firstRebuiltLevel P.d st.rebuildCount
      (Chain.algorithm1_rebuild T L P st i G extraEnc).1.rebuildCount =
        if i < P.d then some i else none := by
  unfold Chain.algorithm1_rebuild
  split
  · rename_i hi
    simpa only [ite_eq_left hi] using firstRebuiltLevel_increment P.d i st.rebuildCount
  · rename_i hi
    simpa only [ite_eq_right hi, ite_eq_right (Nat.lt_irrefl P.d)] using
      firstRebuiltLevel_increment P.d P.d st.rebuildCount

/-- For a nonterminal rebuild, the pass table after the machine reset agrees
with the pass synchronization in Algorithm 2 (page 29). -/
theorem resetAlgorithm1RebuildPasses_runs {T : Chain.SparseCoreRestartTool}
    {L : Chain.LastLevelTool} {P : Chain.ChainParams} (chain : Chain.ChainState T P)
    (i : Fin P.d) (G : MGraph) (extraEnc : ℕ) (passes : Fin (P.d + 1) → ℕ)
    {w base : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hi : st.regs 1 = i.val) (hend : st.regs 2 = P.d + 1)
    (htable : ∀ j, st.mem (base + j.val) = passes j)
    (hbound : base + (P.d + 1) < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω resetPassSuffix st .normal out cost ∧
      cost ≤ 14 * (P.d + 1 - i.val) + 7 ∧ out.pos = st.pos ∧
      ∀ j : Fin (P.d + 1), out.mem (base + j.val) =
        match Chain.firstRebuiltLevel P.d chain.rebuildCount
            (Chain.algorithm1_rebuild T L P chain i.val G extraEnc).1.rebuildCount with
        | none => passes j
        | some first => if first ≤ j.val then 0 else passes j := by
  have hfirst := firstRebuiltLevel_algorithm1_rebuild (L := L) chain i.val G extraEnc
  rw [ite_eq_left i.isLt] at hfirst
  simp only [hfirst]
  let start : Fin (P.d + 1) := ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self P.d)⟩
  exact resetRebuiltPasses_table_runs start passes hb hi hend htable hbound hw

/-- Algorithm 2 (page 29) sees either no periodic rebuild in Algorithm 1's
update or one rebuild at a level below the terminal level. -/
theorem firstRebuiltLevel_algorithm1_update_cases {T : Chain.SparseCoreRestartTool}
    {L : Chain.LastLevelTool} {TP : Chain.SparseCoreParams} {P : Chain.ChainParams} {N₀ : ℕ}
    (st : Chain.ChainState T P) (U : List Update) (g ℓ : ℕ → ℝ) :
    let updated := (Chain.algorithm1_update T L TP P N₀ st U g ℓ).1
    (updated.rebuildCount = st.rebuildCount ∧
      Chain.firstRebuiltLevel P.d st.rebuildCount updated.rebuildCount = none) ∨
    ∃ i : Fin P.d,
      updated.rebuildCount = (fun j => if j = i.val then st.rebuildCount i.val + 1
        else st.rebuildCount j) ∧
      Chain.firstRebuiltLevel P.d st.rebuildCount updated.rebuildCount = some i.val := by
  dsimp only [Chain.algorithm1_update]
  rcases Chain.updateLoop_rebuildCount_cases T L TP P N₀ ℓ g P.d 0 _ _ U _
      (Nat.zero_add _) with hsame | ⟨i, _, hi, hincr⟩
  · exact Or.inl ⟨hsame, by rw [hsame]; exact Chain.firstRebuiltLevel_eq_of_eq _⟩
  · exact Or.inr ⟨⟨i, hi⟩, hincr, by rw [hincr]; exact Chain.firstRebuiltLevel_eq_of_inc hi _⟩

/-- After Algorithm 1 Update, register 3 carries the rebuild flag.
On a rebuild, clear the terminal branch at the address in register 4
and reset the passes beginning at the index in register 1 (page 29). -/
@[expose] def syncRebuildPasses : Stmt :=
  .cond (.reg 3) (.store (.reg 4) (.const 0) ;; resetPassSuffix) .nop

theorem syncRebuildPasses_noRand : syncRebuildPasses.NoRand := by
  simp [syncRebuildPasses, resetPassSuffix_noRand, Stmt.NoRand]

/-- The rebuild flag gates both the terminal branch reset and the pass-table reset. -/
theorem syncRebuildPasses_runs {w base levels branchAddr : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (rebuilt : Option (Fin levels))
    (hb : st.regs 0 = base)
    (hi : ∀ i ∈ rebuilt, st.regs 1 = (i : Fin levels).val)
    (hend : st.regs 2 = levels)
    (hflag : st.regs 3 = if rebuilt.isSome then 1 else 0)
    (haddr : st.regs 4 = branchAddr)
    (hbound : base + levels < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω syncRebuildPasses st .normal out cost ∧ out.pos = st.pos ∧
      cost ≤ (rebuilt.elim 3 fun i => 14 * (levels - i.val) + 13) ∧
      ∀ a, out.mem a = match rebuilt with
        | none => st.mem a
        | some i =>
          if (base + i.val ≤ a ∧ a < base + levels) ∨ a = branchAddr then 0 else st.mem a := by
  cases rebuilt with
  | none =>
    refine ⟨st, 3, ?_, rfl, le_rfl, fun _ => rfl⟩
    exact runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hflag], by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
  | some i =>
    let mid := { st with mem := Function.update st.mem branchAddr 0 }
    have hstore : Runs w p ω (.store (.reg 4) (.const 0)) st .normal mid 3 :=
      runs_store_iff.mpr ⟨branchAddr, 0, by simp [Expr.eval, haddr],
        by simp [Expr.eval], rfl, rfl, rfl⟩
    obtain ⟨out, cost, hr, hc, hm, _, hp⟩ :=
      resetPassSuffix_runs (ω := ω) (st := mid) hb (hi i (by simp)) hend i.isLt.le hbound hw
    refine ⟨out, 3 + cost + 1 + 2, ?_, hp, by simp; omega, fun a => ?_⟩
    · exact runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, hflag],
        by simpa using runs_seq_iff.mpr (Or.inr ⟨mid, 3, cost, hstore, hr, rfl⟩), by simp [Expr.size]; omega⟩
    · rw [hm]
      change (if _ then 0 else Function.update st.mem branchAddr 0 a) = _
      by_cases heq : a = branchAddr <;> simp [heq, Function.update_of_ne]

/-- The branch and pass cells implement Algorithm 2's synchronization after
Algorithm 1 Update (page 29). The caller supplies the rebuild decision made
while forwarding the updates. -/
theorem syncRebuildPasses_algorithm1_update_runs {T : Chain.SparseCoreRestartTool}
    {L : Chain.LastLevelTool} {TP : Chain.SparseCoreParams} {P : Chain.ChainParams} {N₀ : ℕ}
    (chain : Chain.ChainState T P) (U : List Update) (g ℓ : ℕ → ℝ)
    (passes : Fin (P.d + 1) → ℕ) (branD : ℕ)
    {w base branchAddr : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 0 = base) (hend : st.regs 2 = P.d + 1)
    (haddr : st.regs 4 = branchAddr) (hbranch : st.mem branchAddr = branD)
    (htable : ∀ j, st.mem (base + j.val) = passes j)
    (hdisjoint : ∀ j : Fin (P.d + 1), base + j.val ≠ branchAddr)
    (hbound : base + (P.d + 1) < 2 ^ w) (hw : 1 < 2 ^ w) :
    let next := (Chain.algorithm1_update T L TP P N₀ chain U g ℓ).1
    let first := Chain.firstRebuiltLevel P.d chain.rebuildCount next.rebuildCount
    (∀ i ∈ first, st.regs 1 = i) →
    st.regs 3 = (if first.isSome then 1 else 0) →
    ∃ out cost, Runs w p ω syncRebuildPasses st .normal out cost ∧ out.pos = st.pos ∧
      cost ≤ first.elim 3 (fun i => 14 * (P.d + 1 - i) + 13) ∧
      out.mem branchAddr = first.elim branD (fun _ => 0) ∧
      ∀ j : Fin (P.d + 1), out.mem (base + j.val) =
        first.elim (passes j) (fun i => if i ≤ j.val then 0 else passes j) := by
  dsimp only
  intro hindex hflag
  rcases firstRebuiltLevel_algorithm1_update_cases (L := L) (TP := TP) (N₀ := N₀)
      chain U g ℓ with ⟨_, hnone⟩ | ⟨i, _, hsome⟩
  · rw [hnone] at hflag ⊢
    obtain ⟨out, cost, hr, hp, hc, hm⟩ :=
      syncRebuildPasses_runs (ω := ω) (none : Option (Fin (P.d + 1))) hb
        (by simp) hend hflag haddr hbound hw
    exact ⟨out, cost, hr, hp, hc, (hm branchAddr).trans hbranch,
      fun j => (hm (base + j.val)).trans (htable j)⟩
  · rw [hsome] at hindex hflag ⊢
    let start : Fin (P.d + 1) := ⟨i.val, i.isLt.trans (Nat.lt_succ_self _)⟩
    obtain ⟨out, cost, hr, hp, hc, hm⟩ :=
      syncRebuildPasses_runs (ω := ω) (some start) hb
        (by
          intro j hj
          have heq : start = j := by simpa using hj
          subst j
          exact hindex i.val (by simp))
        hend hflag haddr hbound hw
    refine ⟨out, cost, hr, hp, hc, by simp [hm], fun j => ?_⟩
    have hlevel : base + i.val ≤ base + j.val ∧ base + j.val < base + (P.d + 1)
        ↔ i.val ≤ j.val := by
      have := j.isLt
      omega
    simp only [hm, start, hdisjoint j, or_false, hlevel, htable, Option.elim_some]

end MinCostFlow.MinRatio
