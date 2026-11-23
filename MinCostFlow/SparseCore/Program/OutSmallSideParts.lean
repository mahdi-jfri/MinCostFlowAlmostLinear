module

public import MinCostFlow.SparseCore.Program.OutSmallSideLoop

/-!
# The straight parts of the helper `outSmallSide`

The helper has three straight parts around its walk: the head writes `v` and `v'` in the record
and links it (`ssHead_runs`), the start of the walk sets the side and the flag from the first
marked ends (`ssInit_runs`), and the copy moves the list of the chosen part to the end of the
heap (`ssCopy_runs`). Each is a few register and memory steps of constant cost (the copy costs
the length of the list).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

theorem runs_cond_true {e : Expr} {s t : Stmt} {st st' : State} {o : Outcome} {v c : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (h : Runs w p ω s st o st' c) :
    Runs w p ω (.cond e s t) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨v, c, he, by rw [ite_eq_right hv]; exact h, rfl⟩

theorem runs_cond_false {e : Expr} {s t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (he : e.eval w st = some 0) (h : Runs w p ω t st o st' c) :
    Runs w p ω (.cond e s t) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨0, c, he, by rw [ite_eq_left rfl]; exact h, rfl⟩

/-- **The head.** It writes `v` at `h` and `v'` at `h + 1`, links the record after `last`, and
sets the heap pointer to `h + 5`. -/
theorem ssHead_runs {tourH r₁ r₂ v v' last h : ℕ} (mem : ℕ → ℕ) (pos : ℕ)
    (hh : h + 5 < 2 ^ w) (hlast : last ≠ 0 → last + 4 < h) :
    ∃ st' c, Runs w p ω ssHead (startState [tourH, r₁, r₂, v, v', last, h] mem pos) .normal
      st' c ∧ c ≤ 25 ∧ st'.pos = pos ∧
      (∀ r, r ≠ 7 → st'.regs r = [tourH, r₁, r₂, v, v', last, h].getD r 0) ∧
      st'.regs 7 = h + 5 ∧
      ∀ a, st'.mem a = if a = h then v else if a = h + 1 then v' else
        if last ≠ 0 ∧ a = last + 4 then h else mem a := by
  set st0 := startState [tourH, r₁, r₂, v, v', last, h] mem pos with hst0
  have h1w : 1 < 2 ^ w := by omega
  have hs1 := runs_store_of (w := w) (p := p) (ω := ω) (a := .reg 6) (e := .reg 3) (st := st0)
    (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_reg_of_eq (v := v) rfl)
  set st1 : State := { st0 with mem := Function.update st0.mem h v } with hst1
  have hs2 := runs_store_of (w := w) (p := p) (ω := ω) (a := .bin .add (.reg 6) (.const 1)) (e := .reg 4)
    (st := st1) (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_const h1w)
      (by omega)) (Expr.eval_reg_of_eq (v := v') rfl)
  set st2 : State := { st1 with mem := Function.update st1.mem (h + 1) v' } with hst2
  -- the link
  obtain ⟨st3, c3, hs3, hc3, hpos3, hregs3, hmem3⟩ : ∃ st3 c3,
      Runs w p ω (.cond (.reg 5) (.store (.bin .add (.reg 5) (.const 4)) (.reg 6)) .nop) st2
        .normal st3 c3 ∧ c3 ≤ 7 ∧ st3.pos = pos ∧ st3.regs = st0.regs ∧
      ∀ a, st3.mem a = if last ≠ 0 ∧ a = last + 4 then h else st2.mem a := by
    have h5 : st2.regs 5 = last := rfl
    by_cases hl : last = 0
    · have hnop : Runs w p ω (if last = 0 then Stmt.nop
          else .store (.bin .add (.reg 5) (.const 4)) (.reg 6)) st2 .normal st2 1 := by
        rw [ite_eq_left hl]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      exact ⟨st2, _, runs_cond_iff.mpr ⟨last, 1, Expr.eval_reg_of_eq h5, hnop, rfl⟩,
        by simp, rfl, rfl, fun a => by simp [hl]⟩
    · have hl4 := hlast hl
      have hst := runs_store_of (w := w) (p := p) (ω := ω) (a := .bin .add (.reg 5) (.const 4))
        (e := .reg 6) (st := st2) (Expr.eval_add (Expr.eval_reg_of_eq h5)
          (Expr.eval_const (k := 4) (by omega)) (by omega)) (Expr.eval_reg_of_eq (v := h) rfl)
      have hst' : Runs w p ω (if last = 0 then Stmt.nop
          else .store (.bin .add (.reg 5) (.const 4)) (.reg 6)) st2 .normal
          { st2 with mem := Function.update st2.mem (last + 4) h } 5 := by
        rw [ite_eq_right hl]; exact hst
      refine ⟨_, _, runs_cond_iff.mpr ⟨last, 5, Expr.eval_reg_of_eq h5, hst', rfl⟩,
        by simp, rfl, rfl, fun a => ?_⟩
      by_cases ha : a = last + 4
      · simp [ha, hl]
      · simp [ha]
  have hs4 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 7) (st := st3)
    (e := .bin .add (.reg 6) (.const 5))
    (Expr.eval_add (Expr.eval_reg_of_eq (r := 6) (v := h) (by rw [hregs3]; rfl))
      (Expr.eval_const (k := 5) (by omega)) (by omega))
  refine ⟨_, _, runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 hs4)), ?_, hpos3,
    ?_, by simp, ?_⟩
  · simp only [Expr.size_reg, Expr.size_bin, Expr.size_const]; omega
  · intro r hr
    simp [Function.update_of_ne hr, hregs3, hst0, startState]
  · intro a
    simp only [hmem3, hst2, hst1, hst0, startState]
    by_cases h1 : a = h
    · subst h1; simp [show ¬ (last ≠ 0 ∧ a = last + 4) from fun ⟨hl, he⟩ => by
        have := hlast hl; omega]
    · by_cases h2 : a = h + 1
      · subst h2
        have hne : ¬ (last ≠ 0 ∧ h + 1 = last + 4) := fun ⟨hl, he⟩ => by
          have := hlast hl; omega
        rw [ite_eq_right hne, ite_eq_right (by omega : ¬ h + 1 = h), ite_eq_left rfl]
        simp
      · simp [h1, h2]

/-- **The start of the walk.** The side and the flag come from the codes of the first marked
ends in registers `9` and `10`, and the current ends are these first ends. -/
theorem ssInit_runs (st : State) (h1w : 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω ssInit st .normal st' c ∧ c ≤ 25 ∧ st'.mem = st.mem ∧
      st'.pos = st.pos ∧
      (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → st'.regs r = st.regs r) ∧
      st'.regs 12 = st.regs 9 ∧ st'.regs 13 = st.regs 10 ∧
      st'.regs 11 = (if st.regs 9 = 0 then 0 else if st.regs 10 = 0 then 1 else 0) ∧
      st'.regs 14 = (if st.regs 9 = 0 then 0 else if st.regs 10 = 0 then 0 else 1) := by
  have ha1 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 11) (st := st)
    (Expr.eval_const (k := 0) (by omega))
  set stA : State := { st with regs := Function.update st.regs 11 0 } with hstA
  have ha2 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 14) (st := stA)
    (Expr.eval_const (k := 0) (by omega))
  set stB : State := { stA with regs := Function.update stA.regs 14 0 } with hstB
  have hB9 : stB.regs 9 = st.regs 9 := by simp [hstB, hstA]
  have hB10 : stB.regs 10 = st.regs 10 := by simp [hstB, hstA]
  -- the test
  obtain ⟨stC, cC, hC, hcC, hmemC, hposC, hregsC, h11C, h14C⟩ : ∃ stC cC,
      Runs w p ω (.cond (.bin .eq (.reg 9) (.const 0)) .nop
        (.cond (.bin .eq (.reg 10) (.const 0)) (.assign 11 (.const 1)) (.assign 14 (.const 1))))
        stB .normal stC cC ∧ cC ≤ 12 ∧ stC.mem = st.mem ∧ stC.pos = st.pos ∧
      (∀ r, r ≠ 11 → r ≠ 14 → stC.regs r = st.regs r) ∧
      stC.regs 11 = (if st.regs 9 = 0 then 0 else if st.regs 10 = 0 then 1 else 0) ∧
      stC.regs 14 = (if st.regs 9 = 0 then 0 else if st.regs 10 = 0 then 0 else 1) := by
    have he9 := Expr.eval_eq_op (w := w) (st := stB) (Expr.eval_reg_of_eq hB9)
      (Expr.eval_const (k := 0) (by omega)) h1w
    by_cases h9 : st.regs 9 = 0
    · refine ⟨stB, _, runs_cond_true (by simpa [h9] using he9) one_ne_zero
        (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), by simp, rfl, rfl, ?_, ?_, ?_⟩
      · intro r h11 h14; simp [hstB, hstA, Function.update_of_ne h11, Function.update_of_ne h14]
      · simp [hstB, hstA, h9]
      · simp [hstB, hstA, h9]
    · have he10 := Expr.eval_eq_op (w := w) (st := stB) (Expr.eval_reg_of_eq hB10)
        (Expr.eval_const (k := 0) (by omega)) h1w
      by_cases h10 : st.regs 10 = 0
      · have ha := runs_assign_of (w := w) (p := p) (ω := ω) (r := 11) (st := stB)
          (Expr.eval_const (k := 1) h1w)
        refine ⟨_, _, runs_cond_false (by simpa [h9] using he9)
          (runs_cond_true (by simpa [h10] using he10) one_ne_zero ha), by simp, rfl, rfl,
          ?_, ?_, ?_⟩
        · intro r h11 h14; simp [hstB, hstA, Function.update_of_ne h11, Function.update_of_ne h14]
        · simp [h9, h10]
        · simp [hstB, hstA, h9, h10]
      · have ha := runs_assign_of (w := w) (p := p) (ω := ω) (r := 14) (st := stB)
          (Expr.eval_const (k := 1) h1w)
        refine ⟨_, _, runs_cond_false (by simpa [h9] using he9)
          (runs_cond_false (by simpa [h10] using he10) ha), by simp, rfl, rfl, ?_, ?_, ?_⟩
        · intro r h11 h14; simp [hstB, hstA, Function.update_of_ne h11, Function.update_of_ne h14]
        · simp [hstB, hstA, h9, h10]
        · simp [h9, h10]
  have ha3 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 12) (st := stC)
    (Expr.eval_reg_of_eq (r := 9) (v := st.regs 9) (hregsC 9 (by norm_num) (by norm_num)))
  have ha4 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 13)
    (st := { stC with regs := Function.update stC.regs 12 (st.regs 9) })
    (Expr.eval_reg_of_eq (r := 10) (v := st.regs 10) (by
      simp [hregsC 10]))
  refine ⟨_, _, runs_seq_normal ha1 (runs_seq_normal ha2 (runs_seq_normal hC
    (runs_seq_normal ha3 ha4))), ?_, hmemC, hposC, ?_, by simp, by simp, ?_, ?_⟩
  · simp only [Expr.size_reg, Expr.size_const]; omega
  · intro r h11 h12 h13 h14
    simp [Function.update_of_ne h12, Function.update_of_ne h13, hregsC r h11 h14]
  · simp [h11C]
  · simp [h14C]

/-- **The copy.** The list of length `len` at `src` (its length word and its entries) is copied
to `dst`, after it. -/
theorem ssCopy_runs (st : State) {src dst len : ℕ} (h7 : st.regs 7 = src) (h8 : st.regs 8 = dst)
    (h18 : st.regs 18 = len) (hsd : src + len + 1 ≤ dst) (hw : dst + len + 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω ssCopy st .normal st' c ∧ c ≤ 19 * (len + 1) + 9 ∧
      st'.pos = st.pos ∧ (∀ r, r ≠ 19 → st'.regs r = st.regs r) ∧
      ∀ a, st'.mem a =
        if dst ≤ a ∧ a < dst + (len + 1) then st.mem (src + (a - dst)) else st.mem a := by
  have h1w : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i s => s.pos = st.pos ∧ (∀ r, r ≠ 19 → s.regs r = st.regs r) ∧
    s.regs 19 = i ∧ ∀ a, s.mem a =
      if dst ≤ a ∧ a < dst + i then st.mem (src + (a - dst)) else st.mem a
  have ht := Triple.forRange_le (w := w) (p := p) (P := fun s => s = st) (r := 19)
    (lo := .const 0) (hi := .bin .add (.reg 18) (.const 1))
    (body := .store (.bin .add (.reg 8) (.reg 19)) (.load (.bin .add (.reg 7) (.reg 19))))
    (Inv := Inv) (fun _ => 8) 0 (len + 1) (by omega) h1w (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), rfl, fun r hr => by simp [Function.update_of_ne hr],
        by simp, fun a => by simp⟩)
    (fun i s _ _ hI => hI.2.2.1)
    (fun i s _ _ hI => Expr.eval_add (Expr.eval_reg_of_eq ((hI.2.1 18 (by norm_num)).trans h18))
      (Expr.eval_const h1w) (by omega))
    (fun i _ hi => by
      intro s ω' hI
      obtain ⟨hpos, hregs, h19, hmem⟩ := hI
      have h8s : s.regs 8 = dst := (hregs 8 (by norm_num)).trans h8
      have h7s : s.regs 7 = src := (hregs 7 (by norm_num)).trans h7
      have hsrc : s.mem (src + i) = st.mem (src + i) := by
        rw [hmem]; rw [ite_eq_right (by omega)]
      have hrun := runs_store_of (w := w) (p := p) (ω := ω') (st := s)
        (a := .bin .add (.reg 8) (.reg 19)) (e := .load (.bin .add (.reg 7) (.reg 19)))
        (Expr.eval_add (Expr.eval_reg_of_eq h8s) (Expr.eval_reg_of_eq h19) (by omega))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h7s) (Expr.eval_reg_of_eq h19)
          (by omega)) hsrc)
      refine ⟨_, _, _, hrun, ⟨⟨hpos, fun r hr => by simp [Function.update_of_ne hr, hregs r hr],
        by simp, fun a => ?_⟩, by simpa using h19⟩, by simp⟩
      simp only
      by_cases ha : a = dst + i
      · subst ha; simp
      · rw [Function.update_of_ne ha, hmem a]
        by_cases hlo : dst ≤ a ∧ a < dst + i
        · rw [ite_eq_left hlo, ite_eq_left ⟨hlo.1, by omega⟩]
        · rw [ite_eq_right hlo, ite_eq_right (by omega)])
  obtain ⟨o, st', c, hrun, hpost, hc⟩ := ht st ω rfl
  cases o with
  | returned u => exact absurd hpost (by simp)
  | normal =>
    obtain ⟨hpos, hregs, -, hmem⟩ := hpost
    refine ⟨st', c, hrun, ?_, hpos, hregs, hmem⟩
    have hrc := rangeCost_le_mul (f := fun _ => 8) (lo := 0) (hi := len + 1) (c := 8)
      (fun _ _ _ => le_rfl)
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at hc
    omega

end MinCostFlow.SparseCore.Program
