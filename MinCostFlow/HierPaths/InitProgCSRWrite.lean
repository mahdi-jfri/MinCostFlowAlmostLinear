module

public import MinCostFlow.HierPaths.InitProgAppend

/-!
# Writing compressed rows in one pass

The writer reserves one offset per row and one end offset. It writes the
next offset, appends that row to the data area, and advances the pointer.
The row procedure may use scratch above the row provided it restores it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are a caller context, the number of rows, and the output address.
The row call receives that context, its row number and its data address. -/
def initCSRWrite (row : ℕ) : Stmt :=
  .assign 3 (.bin .add (.bin .add (.reg 2) (.reg 1)) (.const 1)) ;;
  .assign 4 (.reg 3) ;;
  forRange 5 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 2) (.reg 5)) (.bin .sub (.reg 4) (.reg 3)) ;;
      .call 4 row [.reg 0, .reg 5, .reg 4]) ;;
  .store (.bin .add (.reg 2) (.reg 1)) (.bin .sub (.reg 4) (.reg 3)) ;;
  .ret (.reg 4)

theorem initCSRWrite_noRand (row : ℕ) : (initCSRWrite row).NoRand := by
  simp [initCSRWrite, forRange, forUp, Stmt.NoRand]

/-- A row call appends one row to a cleared suffix and clears its work space. -/
def initCSRWriteRowContract (ctx i : ℕ) (xs : List ℕ) (W : ℕ → (ℕ → ℕ) → Prop)
    (cost : ℕ) : Contract where
  pre args mem := ∃ dst, args = [ctx, i, dst] ∧ W dst mem ∧ ZeroFrom mem dst
  post args mem v mem' := ∃ dst, args = [ctx, i, dst] ∧ v = dst + xs.length ∧
    ListAt mem' dst xs ∧ ZeroFrom mem' v ∧ ∀ y < dst, mem' y = mem y
  cost _ _ := cost

private theorem initCSRData_prefix (rows : ℕ → List ℕ) (i : ℕ) :
    (csrData i rows).length = initCSRPrefix rows i := by
  rw [csrData, List.length_flatMap, initCSRPrefix]

private theorem initCSRData_next (rows : ℕ → List ℕ) (i : ℕ) :
    csrData (i + 1) rows = csrData i rows ++ rows i := by
  simp [csrData, List.range_succ, List.flatMap_append]

/-- Contract for the combined pass. The fixed context points to memory before
the section, so its invariant survives both offset and data writes. -/
def initCSRWriteContract (w ctx k : ℕ) (rows : ℕ → List ℕ) (cost : ℕ → ℕ)
    (W : ℕ → (ℕ → ℕ) → Prop) (scratch : ℕ) : Contract where
  pre args mem := ∃ dst, args = [ctx, k, dst] ∧ W dst mem ∧ ZeroFrom mem dst ∧
    dst + (csrList k rows).length + scratch < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ dst, args = [ctx, k, dst] ∧ v = dst + (csrList k rows).length ∧
    ListAt mem' dst (csrList k rows) ∧ ZeroFrom mem' v ∧ ∀ y < dst, mem' y = mem y
  cost _ _ := rangeCost cost 0 k + 30 * k + 40

theorem initCSRWrite_meetsContract {w f row ctx k scratch : ℕ} {rows : ℕ → List ℕ} {p : Program}
    {cost : ℕ → ℕ} {W : ℕ → (ℕ → ℕ) → Prop}
    (hp : p.procs[f]? = some (initCSRWrite row))
    (hRow : ∀ i < k, MeetsContract w p row (initCSRWriteRowContract ctx i (rows i)
      (fun addr mem => ∃ dst, W dst mem ∧ dst + k + 1 ≤ addr ∧
        addr + (rows i).length + scratch < 2 ^ w) (cost i)))
    (hStable : ∀ dst mem mem', W dst mem → (∀ y < dst, mem' y = mem y) → W dst mem') :
    MeetsContract w p f (initCSRWriteContract w ctx k rows cost W scratch) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨dst, rfl, hW, hz, hroom, h1⟩ := hpre
  let data := dst + k + 1
  let pref := initCSRPrefix rows
  have hlen : (csrList k rows).length = k + 1 + pref k := by
    rw [csrList, List.length_append, length_csrOffsets, initCSRData_prefix]
  have hEnd : data + pref k + scratch < 2 ^ w := by rw [hlen] at hroom; dsimp [data]; omega
  have hPref (i : ℕ) (hi : i ≤ k) : pref i ≤ pref k := by
    simpa only [pref, initAppendPrefix, List.length_flatMap, initCSRPrefix] using
      initAppendPrefix_length_mono rows hi
  let R := fun (s : State) => s.regs 0 = ctx ∧ s.regs 1 = k ∧ s.regs 2 = dst ∧ s.regs 3 = data
  let Inv := fun (i : ℕ) (s : State) => R s ∧ s.regs 5 = i ∧
    s.regs 4 = data + pref i ∧ (∀ j < i, s.mem (dst + j) = pref j) ∧
    ListAt s.mem data (csrData i rows) ∧ ZeroFrom s.mem (data + pref i) ∧
    ∀ y < dst, s.mem y = mem y
  have hdw : data < 2 ^ w := by omega
  have hbw : dst + k < 2 ^ w := by dsimp [data] at hdw; omega
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0)
    (hi := .reg 1) (P := fun s => R s ∧ s.regs 4 = data ∧ s.mem = mem) (Inv := Inv)
    (body := .store (.bin .add (.reg 2) (.reg 5)) (.bin .sub (.reg 4) (.reg 3)) ;;
      .call 4 row [.reg 0, .reg 5, .reg 4])
    (fun i => cost i + 15) 0 k (Nat.zero_le _) h1 (fun _ => hw _ (by simp))
    (fun s ⟨hr, hd, hm⟩ => by
      have he : pref 0 = 0 := rfl
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [R] using hr
      · simpa [he] using hd
      · exact fun _ h => (Nat.not_lt_zero _ h).elim
      · simp [csrData, ListAt]
      · rw [he, Nat.add_zero, hm]
        exact fun _ hy => hz _ (by dsimp [data] at hy; omega)
      · exact fun y _ => congrFun hm y)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.1.2.1)
    (fun i _ hi => by
      intro s ω' ⟨⟨r0, r1, r2, r3⟩, r5, r4, hoff, hdata, hZero, hf⟩
      let out := data + pref i
      have hs : pref (i + 1) = pref i + (rows i).length := initCSRPrefix_succ rows i
      have hp : out + (rows i).length + scratch < 2 ^ w := by
        have h := hPref (i + 1) hi
        rw [hs] at h
        dsimp [out]
        omega
      have how : out < 2 ^ w := by omega
      have hiw : dst + i < 2 ^ w := by omega
      have hdo : dst + i < data := by dsimp [data]; omega
      let m₁ := Function.update s.mem (dst + i) (pref i)
      have hW₁ : W dst m₁ := hStable dst mem m₁ hW fun y hy =>
        (Function.update_of_ne (by omega) _ _).trans (hf y hy)
      have hZero₁ : ZeroFrom m₁ out := fun y hy =>
        (Function.update_of_ne (by dsimp [out] at hy; omega) _ _).trans (hZero y hy)
      refine runs_start_le ?_
      refine runs_seq_store_le (x := dst + i) (v := pref i)
        (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r5) hiw)
        (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r3) how)
          (Nat.add_sub_cancel_left _ _)) ?_
      refine runs_call_le (hRow i hi) (vs := [ctx, i, out])
        (by simp [evalArgs, Expr.eval, r0, r5, r4, out]) ?_
        ⟨out, rfl, ⟨dst, hW₁, Nat.le_add_right _ _, hp⟩, hZero₁⟩ ?_
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact hw _ (by simp)
        · omega
        · exact how
      · intro r mem₂ pos₂ hp₂
        obtain ⟨out', ha, hr, hwds, hz₂, hf₂⟩ := hp₂
        simp only [List.cons.injEq, and_true] at ha
        obtain ⟨_, _, hou⟩ := ha
        subst out' r
        have he : data + pref (i + 1) = out + (rows i).length := by rw [hs]; exact (Nat.add_assoc ..).symm
        refine ⟨⟨⟨?_, by simp, ?_, ?_, ?_, he.symm ▸ hz₂, ?_⟩, by simpa using r5⟩, ?_⟩
        · exact ⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3⟩
        · simpa using he.symm
        · intro j hj
          have hbefore : dst + j < out := by dsimp [data, out]; omega
          change mem₂ (dst + j) = _
          rw [hf₂ _ hbefore]
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
          · exact (Function.update_of_ne (by omega) _ _).trans (hoff j hj')
          · exact Function.update_self ..
        · rw [initCSRData_next, listAt_append, initCSRData_prefix]
          refine ⟨listAt_congr (fun j hj => ?_) hdata, hwds⟩
          rw [initCSRData_prefix] at hj
          change j < pref i at hj
          exact ((hf₂ _ (by dsimp [out]; omega)).trans
            (Function.update_of_ne (by omega) _ _)).symm
        · intro y hy
          exact (hf₂ _ (by dsimp [out, data]; omega)).trans
            ((Function.update_of_ne (by omega) _ _).trans (hf y hy))
        · simp [initCSRWriteRowContract, argsSize, Expr.size]; omega)
  refine runs_start_le ?_
  unfold initCSRWrite
  refine runs_seq_assign_le (v := data) (Expr.eval_add
    (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_reg_of_eq (v := k) rfl) hbw)
    (Expr.eval_const h1) hdw) ?_
  refine runs_seq_assign_le (v := data) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
  intro s ⟨⟨r0, r1, r2, r3⟩, _, r4, hoff, hdata, hz', hf⟩
  have hptr : data + pref k < 2 ^ w := by omega
  refine runs_seq_store_le (x := dst + k) (v := pref k)
    (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r1) hbw)
    (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r3) hptr)
      (Nat.add_sub_cancel_left _ _)) ?_
  refine runs_ret_le (v := data + pref k) (Expr.eval_reg_of_eq r4)
    ⟨dst, rfl, ?_, ?_, ?_, ?_⟩ ?_
  · simp [Outcome.value, hlen, data, Nat.add_assoc]
  · rw [csrList, listAt_append, length_csrOffsets]
    refine ⟨listAt_csrOffsets_of fun i hi => ?_, listAt_congr (fun i hi => ?_) hdata⟩
    · rcases Nat.lt_or_eq_of_le hi with h | rfl
      · exact (Function.update_of_ne (by omega) _ _).trans (hoff i h)
      · exact Function.update_self ..
    · exact (Function.update_of_ne (by dsimp [data]; omega) _ _).symm
  · intro y hy
    change data + pref k ≤ y at hy
    exact (Function.update_of_ne (by dsimp [data] at hy; omega) _ _).trans (hz' y hy)
  · intro y hy
    exact (Function.update_of_ne (by omega) _ _).trans (hf y hy)
  · simp [initCSRWriteContract, Expr.size, rangeCost_add]
    omega

end MinCostFlow.HierPaths

end
