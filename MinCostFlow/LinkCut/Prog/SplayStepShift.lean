module

public import MinCostFlow.LinkCut.Prog.SplayStepBase

namespace MinCostFlow.LinkCut.Prog

/-!
Word-RAM specification for `shiftPtrStmt` and `applyTagBody`:
- `listIntMinAgg_mem` for bounding shifted path-minima via `StepsShiftFit`,
- `shiftPtrStmt_triple` and `shiftFieldStmt_triple` wrapping `Num.add` / `Num.subtract`,
- `applyTagBody_zero_triple` and `applyTagBody_runs_subtree`.
-/

open WordRAM MinCostFlow.Num


@[expose] public section

/-! ### `IntMinAgg` and `RawStep.addDeltaMod` helpers -/

theorem listIntMinAgg_mem {xs : List (ℕ × ℤ)}
    (hhas : (listIntMinAgg xs).has = true) :
    ∃ p ∈ xs, (listIntMinAgg xs).val = p.2 := by
  induction xs with
  | nil => simp [listIntMinAgg] at hhas
  | cons p xs ih =>
      rcases p with ⟨id, v⟩
      rcases hxs : listIntMinAgg xs with ⟨hb, vb, fb, lb⟩
      cases hb
      · refine ⟨(id, v), List.mem_cons_self, ?_⟩
        simp [listIntMinAgg, hxs, combineIntMinAgg]
      · simp only [listIntMinAgg, hxs, combineIntMinAgg, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : vb < v
        · rcases ih (by simp [hxs]) with ⟨q, hqm, hqv⟩
          refine ⟨q, List.mem_cons_of_mem _ hqm, ?_⟩
          simp only [hxs] at hqv
          simpa [hlt] using hqv
        · by_cases heq : v = vb
          · subst heq; exact ⟨(id, v), List.mem_cons_self, by simp⟩
          · exact ⟨(id, v), List.mem_cons_self, by simp [hlt, heq]⟩

theorem rawStep_addDeltaMod_congr {h L : ℕ} {s : RawStep} {a b : ℤ}
    (hmod : a % (capacity h L : ℤ) = b % (capacity h L : ℤ)) :
    s.addDeltaMod h L a = s.addDeltaMod h L b := by
  have hplus : ∀ x : ℤ, wrap h L (x + a) = wrap h L (x + b) := fun x => by
    apply wrap_congr
    rw [Int.add_emod, hmod, ← Int.add_emod]
  have hminus : ∀ x : ℤ, wrap h L (x - a) = wrap h L (x - b) := fun x => by
    apply wrap_congr
    rw [Int.sub_emod, hmod, ← Int.sub_emod]
  cases hf : s.fwd <;> simp [RawStep.addDeltaMod, hf, hplus, hminus]

theorem stepsShiftFit_compose {h L : ℕ} {steps : List RawStep} {d₀ d : ℤ}
    (hfit₀ : StepsShiftFit h L steps d₀)
    (hfit₁ : StepsShiftFit h L (steps.map (fun s => s.addDelta d₀)) d) :
    StepsShiftFit h L steps (d₀ + d) := by
  intro s hs
  rcases hfit₀ s hs with ⟨hf0, haf0, hab0, hfs0, hafs0, habs0⟩
  have hm := hfit₁ (s.addDelta d₀) (List.mem_map.mpr ⟨s, hs, rfl⟩)
  rcases hm with ⟨_, _, _, hfs1, hafs1, habs1⟩
  cases hdir : s.fwd <;>
    simp only [RawStep.addDelta, hdir, Bool.false_eq_true, ↓reduceIte] at hfs0 hafs0 habs0 hfs1 hafs1 habs1 ⊢
  · refine ⟨hf0, haf0, hab0, ?_, ?_, ?_⟩
    · simpa [sub_sub] using hfs1
    · simpa [add_assoc] using hafs1
    · simpa [sub_sub] using habs1
  · refine ⟨hf0, haf0, hab0, ?_, ?_, ?_⟩
    · simpa [add_assoc] using hfs1
    · simpa [sub_sub] using hafs1
    · simpa [add_assoc] using habs1

theorem zeroFrom_update_lt_hp {mem : ℕ → ℕ} {hp addr val : ℕ}
    (hz : ZeroFrom mem hp) (hlt : addr < hp) :
    ZeroFrom (Function.update mem addr val) hp := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact hz i hi

def NodeHeapStepMem (arenaHi ptr hp₀ hp₁ : ℕ) (m₀ m₁ : ℕ → ℕ) : Prop :=
  hp₀ ≤ hp₁ ∧ ZeroFrom m₁ hp₁ ∧
  (∀ a, a < arenaHi → (∀ off < NODE_STRIDE, a ≠ ptr + off) → m₁ a = m₀ a) ∧
  (∀ a, arenaHi ≤ a → a < hp₀ → m₁ a = m₀ a)

theorem nodeHeapStepMem_refl (arenaHi ptr hp : ℕ) (m : ℕ → ℕ)
    (hz : ZeroFrom m hp) : NodeHeapStepMem arenaHi ptr hp hp m m :=
  ⟨le_rfl, hz, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem nodeHeapStepMem_trans {arenaHi ptr hp₀ hp₁ hp₂ : ℕ} {m₀ m₁ m₂ : ℕ → ℕ}
    (h₁₂ : NodeHeapStepMem arenaHi ptr hp₀ hp₁ m₀ m₁)
    (h₂₃ : NodeHeapStepMem arenaHi ptr hp₁ hp₂ m₁ m₂) :
    NodeHeapStepMem arenaHi ptr hp₀ hp₂ m₀ m₂ :=
  ⟨le_trans h₁₂.1 h₂₃.1, h₂₃.2.1,
    fun a ha hne => (h₂₃.2.2.1 a ha hne).trans (h₁₂.2.2.1 a ha hne),
    fun a ha1 ha2 => (h₂₃.2.2.2 a ha1 (lt_of_lt_of_le ha2 h₁₂.1)).trans (h₁₂.2.2.2 a ha1 ha2)⟩

theorem nodeHeapStepMem_numPtrOk {arenaHi hp₀ hp₁ h L ptr q : ℕ} {m₀ m₁ : ℕ → ℕ}
    (hst : NodeHeapStepMem arenaHi ptr hp₀ hp₁ m₀ m₁)
    (hq : NumPtrOk m₀ arenaHi hp₀ h L q) :
    NumPtrOk m₁ arenaHi hp₁ h L q := by
  rcases hq with ⟨hne, hlo, hhi, hval⟩
  refine ⟨hne, hlo, le_trans hhi hst.1, ?_⟩
  intro i hi
  rw [hst.2.2.2 (q + i) (by omega) (by omega)]
  exact hval i hi

/-! ### `shiftPtrStmt` and `shiftFieldStmt` triples -/

theorem shiftPtrStmt_triple {w h L arenaHi hp vPtr tPtr isAddVal : ℕ}
    {sp : SplayProcs} {p : Program} {isAddExpr : Expr}
    {valPtrReg tPtrReg LReg hpReg outPtrReg : ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hnd_regs : [valPtrReg, tPtrReg, LReg, hpReg, outPtrReg].Nodup)
    (st₀ : State)
    (heval_cond : isAddExpr.eval w st₀ = some isAddVal)
    (hr_val : st₀.regs valPtrReg = vPtr)
    (hr_t : st₀.regs tPtrReg = tPtr)
    (hr_L : st₀.regs LReg = L)
    (hr_hp : st₀.regs hpReg = hp)
    (harena_pos : 1 ≤ arenaHi)
    (hv_ok : NumPtrOk st₀.mem arenaHi hp h L vPtr)
    (ht_ok : NumPtrOk st₀.mem arenaHi hp h L tPtr)
    (hz : ZeroFrom st₀.mem hp)
    (hhp_lt : hp + 2 * L < 2 ^ w) :
    ∀ ω, ∃ st' c hp' outPtr,
      Runs w p ω (shiftPtrStmt sp isAddExpr valPtrReg tPtrReg LReg hpReg outPtrReg)
        st₀ .normal st' c ∧
      st'.regs hpReg = hp' ∧
      st'.regs outPtrReg = outPtr ∧
      (∀ r, r ≠ hpReg → r ≠ outPtrReg → st'.regs r = st₀.regs r) ∧
      hp ≤ hp' ∧ hp' ≤ hp + 2 * L ∧
      c + (hp' - hp) ≤ isAddExpr.size + 76 * L + 60 ∧
      (∀ a < hp, st'.mem a = st₀.mem a) ∧
      ZeroFrom st'.mem hp' ∧
      NumPtrOk st'.mem arenaHi hp' h L outPtr ∧
      intVal st'.mem outPtr h L = wrap h L
        (if isAddVal = 0 then intVal st₀.mem vPtr h L - intVal st₀.mem tPtr h L
         else intVal st₀.mem vPtr h L + intVal st₀.mem tPtr h L) := by
  intro ω
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd_regs
  rcases hnd_regs with ⟨⟨_, _, _, _⟩, ⟨_, _, _⟩, ⟨hLh, _⟩, hho, _⟩
  have hargs : evalArgs w st₀ [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] =
      some [vPtr, tPtr, L, hp] := by
    simp [evalArgs, Expr.eval, hr_val, hr_t, hr_L, hr_hp]
  have hwords : ∀ a ∈ ([vPtr, tPtr, L, hp] : List ℕ), a < 2 ^ w := by
    intro a ha
    have hv_hi := hv_ok.2.2.1
    have ht_hi := ht_ok.2.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have harena_hp : arenaHi ≤ hp := by have := hv_ok.2.1; have := hv_ok.2.2.1; omega
  dsimp only [shiftPtrStmt]
  by_cases hadd : isAddVal = 0
  · have hpre_sub : (subtractContract w h).pre [vPtr, tPtr, L, hp] st₀.mem := by
      refine ⟨⟨vPtr, tPtr, L, hp, rfl, hv_ok.2.2.1, ht_ok.2.2.1, hv_ok.2.2.2, ht_ok.2.2.2⟩,
        hz, ?_⟩
      change hp + 2 * L < 2 ^ w
      exact hhp_lt
    rcases hp_ok.sub_ok [vPtr, tPtr, L, hp] st₀.mem st₀.pos ω hwords hpre_sub with
      ⟨body, hproc, o, st1, c_sub, hr_sub, hpost_sub, hc_sub⟩
    rcases hpost_sub with ⟨ho_eq, _, _, hpres1, hz1, hv1, hint1⟩
    change o.value = hp + 2 * L at ho_eq
    change ∀ a < hp, st1.mem a = st₀.mem a at hpres1
    change ZeroFrom st1.mem o.value at hz1
    change Valid st1.mem (hp + L) h L at hv1
    change intVal st1.mem (hp + L) h L = wrap h L (intVal st₀.mem vPtr h L - intVal st₀.mem tPtr h L) at hint1
    change c_sub ≤ 74 * L + 42 at hc_sub
    let st_call : State := { st1 with regs := Function.update st₀.regs hpReg (hp + 2 * L) }
    have hcall : Runs w p ω
        (Stmt.call hpReg sp.numSub [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg])
        st₀ .normal st_call (argsSize [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] + c_sub + 1) := by
      dsimp only [st_call]
      rw [← ho_eq]
      exact runs_call_iff.mpr ⟨[vPtr, tPtr, L, hp], body, o, st1, c_sub, hargs, hproc, hr_sub, rfl, rfl, rfl⟩
    have hr_hp1 : st_call.regs hpReg = hp + 2 * L := Function.update_self _ _ _
    have hr_L1 : st_call.regs LReg = L := by
      dsimp [st_call]; rw [Function.update_of_ne hLh, hr_L]
    have hsub_ev : (Expr.bin .sub (.reg hpReg) (.reg LReg)).eval w st_call = some (hp + L) := by
      have h1 := Expr.eval_sub (Expr.eval_reg_of_eq hr_hp1) (Expr.eval_reg_of_eq hr_L1) (by omega)
      simpa [show hp + 2 * L - L = hp + L by omega] using h1
    let st' : State := { mem := st_call.mem, regs := Function.update st_call.regs outPtrReg (hp + L), pos := st_call.pos }
    have hass : Runs w p ω (Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))
        st_call .normal st' ((Expr.bin .sub (.reg hpReg) (.reg LReg)).size + 1) :=
      runs_assign_iff.mpr ⟨hp + L, hsub_ev, rfl, rfl, rfl⟩
    have hbranch : Runs w p ω
        (Stmt.call hpReg sp.numSub [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] ;;
         Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))
        st₀ .normal st' _ :=
      runs_seq_iff.mpr (Or.inr ⟨st_call, _, _, hcall, hass, rfl⟩)
    refine ⟨st', _, hp + 2 * L, hp + L, runs_cond_iff.mpr ⟨0, _, by simpa [hadd] using heval_cond,
        by simpa using hbranch, rfl⟩, ?_, ?_, ?_, by omega, le_rfl, ?_, hpres1, ?_, ?_, ?_⟩
    · dsimp [st', st_call]; rw [Function.update_of_ne hho]; exact hr_hp1
    · dsimp [st']; exact Function.update_self _ _ _
    · intro r hr1 hr2
      dsimp [st', st_call]; rw [Function.update_of_ne hr2, Function.update_of_ne hr1]
    · simp only [Expr.size, argsSize] at *; omega
    · simpa [st', st_call, ho_eq] using hz1
    · exact ⟨by omega, by omega, by omega, hv1⟩
    · simp only [hadd, ↓reduceIte]; exact hint1
  · have hpre_add : (addContract w h).pre [vPtr, tPtr, L, hp] st₀.mem := by
      refine ⟨vPtr, tPtr, L, hp, rfl, ?_⟩
      exact ⟨⟨vPtr, tPtr, L, 0, hp, rfl, hv_ok.2.2.1, ht_ok.2.2.1, Nat.zero_le 1,
        hv_ok.2.2.2, ht_ok.2.2.2⟩, hz, by change hp + L < 2 ^ w; omega⟩
    rcases hp_ok.add_ok [vPtr, tPtr, L, hp] st₀.mem st₀.pos ω hwords hpre_add with
      ⟨body, hproc, o, st1, c_add, hr_add, hpost_add, hc_add⟩
    rcases hpost_add with ⟨ho_eq, _, _, hpres1, hz1, hl1⟩
    change o.value = hp + L at ho_eq
    change ∀ a < hp, st1.mem a = st₀.mem a at hpres1
    change ZeroFrom st1.mem o.value at hz1
    change ListAt st1.mem hp (digits h L (unsignedVal st₀.mem vPtr h L + unsignedVal st₀.mem tPtr h L + 0)) at hl1
    change c_add ≤ 38 * L + 15 at hc_add
    have hval1 := addCarry_value hl1
    let st_call : State := { st1 with regs := Function.update st₀.regs hpReg (hp + L) }
    have hcall : Runs w p ω
        (Stmt.call hpReg sp.numAdd [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg])
        st₀ .normal st_call (argsSize [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] + c_add + 1) := by
      dsimp only [st_call]
      rw [← ho_eq]
      exact runs_call_iff.mpr ⟨[vPtr, tPtr, L, hp], body, o, st1, c_add, hargs, hproc, hr_add, rfl, rfl, rfl⟩
    have hr_hp1 : st_call.regs hpReg = hp + L := Function.update_self _ _ _
    have hr_L1 : st_call.regs LReg = L := by
      dsimp [st_call]; rw [Function.update_of_ne hLh, hr_L]
    have hsub_ev : (Expr.bin .sub (.reg hpReg) (.reg LReg)).eval w st_call = some hp := by
      have hlt : hp + L < 2 ^ w := by omega
      have h1 := Expr.eval_sub (Expr.eval_reg_of_eq hr_hp1) (Expr.eval_reg_of_eq hr_L1) hlt
      simpa [show hp + L - L = hp by omega] using h1
    let st' : State := { mem := st_call.mem, regs := Function.update st_call.regs outPtrReg hp, pos := st_call.pos }
    have hass : Runs w p ω (Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))
        st_call .normal st' ((Expr.bin .sub (.reg hpReg) (.reg LReg)).size + 1) :=
      runs_assign_iff.mpr ⟨hp, hsub_ev, rfl, rfl, rfl⟩
    have hbranch : Runs w p ω
        (Stmt.call hpReg sp.numAdd [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] ;;
         Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))
        st₀ .normal st' _ :=
      runs_seq_iff.mpr (Or.inr ⟨st_call, _, _, hcall, hass, rfl⟩)
    refine ⟨st', _, hp + L, hp, runs_cond_iff.mpr ⟨isAddVal, _, heval_cond,
        by simpa [hadd] using hbranch, rfl⟩, ?_, ?_, ?_, by omega, by omega, ?_, hpres1, ?_, ?_, ?_⟩
    · dsimp [st', st_call]; rw [Function.update_of_ne hho]; exact hr_hp1
    · dsimp [st']; exact Function.update_self _ _ _
    · intro r hr1 hr2
      dsimp [st', st_call]; rw [Function.update_of_ne hr2, Function.update_of_ne hr1]
    · simp only [Expr.size, argsSize] at *; omega
    · simpa [st', st_call, ho_eq] using hz1
    · exact ⟨by omega, harena_hp, le_rfl, hval1.1⟩
    · simp only [hadd, ↓reduceIte]; simpa [Int.natCast_zero, add_zero] using hval1.2

theorem shiftFieldStmt_triple {w h L nodesBase cap x ptr tPtr fOff isAddVal : ℕ}
    {sp : SplayProcs} {p : Program} {isAddExpr : Expr}
    (hp_ok : SplayProgramOk w h p sp)
    (st₀ : State)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (_hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hf_lt : fOff < NODE_STRIDE)
    (hptr_eq : ptr = nodesBase + NODE_STRIDE * x)
    (hr_cond_indep : ∀ v8, isAddExpr.eval w { mem := st₀.mem, regs := Function.update st₀.regs 8 v8, pos := st₀.pos } = some isAddVal)
    (hr4 : st₀.regs 4 = ptr)
    (ht_ptr : st₀.regs 2 = tPtr) (hr6 : st₀.regs 6 = L)
    (hp₀ : ℕ) (hr7 : st₀.regs 7 = hp₀)
    (harena_pos : 1 ≤ nodesBase + NODE_STRIDE * (cap + 1))
    (harena_le : nodesBase + NODE_STRIDE * (cap + 1) ≤ hp₀)
    (hf_ok : NumPtrOk st₀.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L (st₀.mem (ptr + fOff)))
    (ht_ok : NumPtrOk st₀.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp₀ h L tPtr)
    (hz : ZeroFrom st₀.mem hp₀)
    (hhp_lt : hp₀ + 2 * L < 2 ^ w) :
    ∀ ω, ∃ st' c hp' outPtr,
      Runs w p ω
        (Stmt.assign 8 (fieldLoadExpr 4 fOff) ;;
         shiftPtrStmt sp isAddExpr 8 2 6 7 9 ;;
         Stmt.store (fieldAddrExpr 4 fOff) (.reg 9))
        st₀ .normal st' c ∧
      st'.regs 7 = hp' ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → st'.regs r = st₀.regs r) ∧
      hp₀ ≤ hp' ∧ hp' ≤ hp₀ + 2 * L ∧
      c + (hp' - hp₀) ≤ isAddExpr.size + 76 * L + 72 ∧
      NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1)) ptr hp₀ hp' st₀.mem st'.mem ∧
      st'.mem (ptr + fOff) = outPtr ∧
      (∀ off < NODE_STRIDE, off ≠ fOff → st'.mem (ptr + off) = st₀.mem (ptr + off)) ∧
      NumPtrOk st'.mem (nodesBase + NODE_STRIDE * (cap + 1)) hp' h L outPtr ∧
      intVal st'.mem outPtr h L = wrap h L
        (if isAddVal = 0 then intVal st₀.mem (st₀.mem (ptr + fOff)) h L - intVal st₀.mem tPtr h L
         else intVal st₀.mem (st₀.mem (ptr + fOff)) h L + intVal st₀.mem tPtr h L) := by
  intro ω
  subst hptr_eq
  have hal := nodeAddr_lt_pow hbase hx2 hf_lt
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 8 (st₀.mem (nodesBase + NODE_STRIDE * x + fOff)), pos := st₀.pos }
  have ha1 : Runs w p ω (Stmt.assign 8 (fieldLoadExpr 4 fOff)) st₀ .normal st1 ((fieldLoadExpr 4 fOff).size + 1) :=
    runs_assign_iff.mpr ⟨st₀.mem (nodesBase + NODE_STRIDE * x + fOff),
      eval_fieldLoadExpr hr4 hal, rfl, rfl, rfl⟩
  rcases shiftPtrStmt_triple (vPtr := st₀.mem (nodesBase + NODE_STRIDE * x + fOff)) (tPtr := tPtr)
      hp_ok (by decide : ([8, 2, 6, 7, 9] : List ℕ).Nodup) st1 (hr_cond_indep _)
      (by dsimp [st1]; exact Function.update_self _ _ _)
      (by dsimp [st1]; rw [Function.update_of_ne (by decide), ht_ptr])
      (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr6])
      (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr7])
      harena_pos hf_ok ht_ok hz hhp_lt ω with
    ⟨st2, c2, hp', outPtr, hr2_step, hr2_7, hr2_9, hr2_other, hle1, hle2, hc2, hpres2, hz2, hout_ok, hint2⟩
  have hr2_4 : st2.regs 4 = nodesBase + NODE_STRIDE * x := by
    rw [hr2_other 4 (by decide) (by decide)]; dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr4
  let st' : State :=
    ⟨Function.update st2.mem (nodesBase + NODE_STRIDE * x + fOff) outPtr, st2.regs, st2.pos⟩
  have hstore : Runs w p ω (Stmt.store (fieldAddrExpr 4 fOff) (.reg 9)) st2 .normal st' _ :=
    runs_store_iff.mpr ⟨nodesBase + NODE_STRIDE * x + fOff, outPtr,
      eval_fieldAddrExpr hr2_4 hal, Expr.eval_reg_of_eq hr2_9, rfl, rfl, rfl⟩
  have hslot_hi : nodesBase + NODE_STRIDE * x + fOff < nodesBase + NODE_STRIDE * (cap + 1) := by
    have hmul : NODE_STRIDE * x + fOff < NODE_STRIDE * (cap + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have := Nat.mul_le_mul_left NODE_STRIDE hx2
      omega
    omega
  have nhs : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1)) (nodesBase + NODE_STRIDE * x) hp₀ hp' st₀.mem st'.mem := by
    refine ⟨hle1, ?_, ?_, ?_⟩
    · dsimp [st']; exact zeroFrom_update_lt_hp hz2 (lt_of_lt_of_le hslot_hi (le_trans harena_le hle1))
    · intro a ha hne
      dsimp [st']
      rw [Function.update_of_ne (hne fOff hf_lt), hpres2 a (lt_of_lt_of_le ha harena_le)]
    · intro a ha1 _
      dsimp [st']
      rw [Function.update_of_ne (by omega : a ≠ nodesBase + NODE_STRIDE * x + fOff), hpres2 a (by omega)]
  refine ⟨st', _, hp', outPtr,
    runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha1, runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hr2_step, hstore, rfl⟩), rfl⟩),
    hr2_7, ?_, hle1, hle2, ?_, nhs, ?_, ?_, ?_, ?_⟩
  · intro r h7 h8 h9
    rw [hr2_other r h7 h9]
    dsimp [st1]; rw [Function.update_of_ne h8]
  · simp only [fieldLoadExpr, fieldAddrExpr, Expr.size] at hc2 ⊢; omega
  · dsimp [st']; exact Function.update_self _ _ _
  · intro off hoff hne
    dsimp [st']
    have hne' : nodesBase + NODE_STRIDE * x + off ≠ nodesBase + NODE_STRIDE * x + fOff := by omega
    have hoff_lt : nodesBase + NODE_STRIDE * x + off < hp₀ := by
      have := Nat.mul_le_mul_left NODE_STRIDE hx2
      rw [Nat.mul_add, Nat.mul_one] at *; omega
    rw [Function.update_of_ne hne', hpres2 _ hoff_lt]
  · rcases hout_ok with ⟨hone, hlo, hhi, hval⟩
    refine ⟨hone, hlo, hhi, ?_⟩
    intro i hi
    dsimp [st']
    rw [Function.update_of_ne (by omega : outPtr + i ≠ nodesBase + NODE_STRIDE * x + fOff)]
    exact hval i hi
  · have hcongr : ∀ i < L, st'.mem (outPtr + i) = st2.mem (outPtr + i) := fun i hi => by
      dsimp [st']
      rw [Function.update_of_ne (by
        have hlo := hout_ok.2.1
        have hmx := Nat.mul_le_mul_left NODE_STRIDE hx2
        have hf' : fOff < NODE_STRIDE := hf_lt
        rw [Nat.mul_add, Nat.mul_one] at hlo
        omega)]
    dsimp [st']
    rw [intVal_congr hcongr]
    exact hint2

theorem runs_seq3_prepend {w p ω s1 s2 s3 rest st0 st1 st2 o c1 c2}
    (h1 : Runs w p ω (s1 ;; s2 ;; s3) st0 .normal st1 c1)
    (h2 : Runs w p ω rest st1 o st2 c2) :
    Runs w p ω (s1 ;; s2 ;; s3 ;; rest) st0 o st2 (c1 + c2 + 1) := by
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, heq, _⟩ | ⟨sma, c1a, c1bc, ha, hbc, rfl⟩
  · cases heq
  rcases runs_seq_iff.mp hbc with ⟨_, _, _, heq, _⟩ | ⟨smb, c1b, c1c, hb, hc, rfl⟩
  · cases heq
  exact runs_seq_iff.mpr (Or.inr ⟨sma, c1a, c1b + (c1c + c2 + 1) + 1, ha,
    runs_seq_iff.mpr (Or.inr ⟨smb, c1b, c1c + c2 + 1, hb,
      runs_seq_iff.mpr (Or.inr ⟨st1, c1c, c2, hc, h2, rfl⟩), rfl⟩), by omega⟩)


theorem runs_seq_prepend {w p ω a b rest st0 st1 st2 o c1 c2}
    (h1 : Runs w p ω (a ;; b) st0 .normal st1 c1)
    (h2 : Runs w p ω rest st1 o st2 c2) :
    Runs w p ω (a ;; b ;; rest) st0 o st2 (c1 + c2 + 1) := by
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, heq, _⟩ | ⟨sm, ca, cb, ha, hb, rfl⟩
  · cases heq
  exact runs_seq_iff.mpr (Or.inr ⟨sm, ca, cb + c2 + 1, ha,
    runs_seq_iff.mpr (Or.inr ⟨st1, cb, c2, hb, h2, rfl⟩), by omega⟩)

theorem runs_seq6_prepend {w p ω s1 s2 s3 s4 s5 s6 rest st0 st1 st2 o c1 c2}
    (h1 : Runs w p ω (s1 ;; s2 ;; s3 ;; s4 ;; s5 ;; s6) st0 .normal st1 c1)
    (h2 : Runs w p ω rest st1 o st2 c2) :
    Runs w p ω (s1 ;; s2 ;; s3 ;; s4 ;; s5 ;; s6 ;; rest) st0 o st2 (c1 + c2 + 1) := by
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, heq, _⟩ | ⟨sm1, c1a, c1b, h1a, h1b, rfl⟩
  · cases heq
  rcases runs_seq_iff.mp h1b with ⟨_, _, _, heq, _⟩ | ⟨sm2, c2a, c2b, h2a, h2b, rfl⟩
  · cases heq
  rcases runs_seq_iff.mp h2b with ⟨_, _, _, heq, _⟩ | ⟨sm3, c3a, c3b, h3a, h3b, rfl⟩
  · cases heq
  rcases runs_seq_iff.mp h3b with ⟨_, _, _, heq, _⟩ | ⟨sm4, c4a, c4b, h4a, h4b, rfl⟩
  · cases heq
  rcases runs_seq_iff.mp h4b with ⟨_, _, _, heq, _⟩ | ⟨sm5, c5a, c5b, h5a, h5b, rfl⟩
  · cases heq
  exact runs_seq_iff.mpr (Or.inr ⟨sm1, c1a, _, h1a,
    runs_seq_iff.mpr (Or.inr ⟨sm2, c2a, _, h2a,
      runs_seq_iff.mpr (Or.inr ⟨sm3, c3a, _, h3a,
        runs_seq_iff.mpr (Or.inr ⟨sm4, c4a, _, h4a,
          runs_seq_iff.mpr (Or.inr ⟨sm5, c5a, _, h5a,
            runs_seq_iff.mpr (Or.inr ⟨st1, c5b, c2, h5b, h2, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)

end

end MinCostFlow.LinkCut.Prog
