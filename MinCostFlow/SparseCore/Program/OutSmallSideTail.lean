module

public import MinCostFlow.SparseCore.Program.OutSmallSideParts

/-!
# The end of the helper `outSmallSide`

After the walk, register `11` holds the side. The end of the helper lists the marked ends of the
chosen part with `listMarked`, copies the list after the cells of that call, writes the side and
the place of the list in the record, and returns the new heap pointer (`ssTail_runs`). The copy
is what keeps the list away from every cell that the tour may take.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

section Tail

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- **The end of the helper.** -/
theorem ssTail_runs (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH r₁ r₂ v v' last h : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} (ω : ℕ → Bool)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx₀ (last + 4)))
    (stD : State) (tx : T.rep.τ) (cur : ℕ)
    (hF : SSFrame T tourH last h v v' s tx₀ mem₀ cur tx stD.mem)
    (hA : SSArgs stD tourH r₁ r₂ v v' last h) (h7 : stD.regs 7 = cur)
    (h11 : stD.regs 11 = ssSide s r₁ r₂)
    (htour : tourH < 2 ^ w) (hr₁ : r₁ < vCap) (hr₂ : r₂ < vCap)
    (hspace : cur + S.listSpace (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length +
      (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length + 1 < 2 ^ w) :
    ∃ st' c tx' cur', Runs w p ω (ssTail lm) stD
      (.returned (cur' + 1 + (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length))
      st' c ∧
      T.rep.rep tourH s tx' st'.mem ∧
      st'.mem h = v ∧ st'.mem (h + 1) = v' ∧ st'.mem (h + 2) = ssSide s r₁ r₂ ∧
      st'.mem (h + 3) = cur' ∧ st'.mem (h + 4) = 0 ∧
      EndListAt st'.mem cur' (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)) ∧
      cur + 1 + (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length ≤ cur' ∧
      cur' ≤ cur + S.listSpace (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length ∧
      ZeroFrom st'.mem (cur' + 1 + (s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length) ∧
      (last ≠ 0 → st'.mem (last + 4) = h) ∧
      (∀ a < h, ¬ T.rep.foot tourH tx₀ a → (last = 0 ∨ a ≠ last + 4) → st'.mem a = mem₀ a) ∧
      (∀ a, T.rep.foot tourH tx' a → T.rep.foot tourH tx₀ a ∨ (h + 5 ≤ a ∧ a < cur')) ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        S.mul * ((s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length + 1) *
          ordStoreLog eCap +
        19 * ((s.markedList (if ssSide s r₁ r₂ = 0 then r₁ else r₂)).length + 1) + 60 +
        T.rep.phi tourH tx stD.mem := by
  set root := if ssSide s r₁ r₂ = 0 then r₁ else r₂ with hroot
  have h1w : 1 < 2 ^ w := by omega
  have hrootV : root < vCap := by rw [hroot]; split <;> assumption
  -- the root
  have ha1 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 16) (st := stD)
    (Expr.eval_reg_of_eq (r := 1) hA.2.1)
  set stE1 : State := { stD with regs := Function.update stD.regs 16 r₁ } with hstE1
  have h11' : stE1.regs 11 = ssSide s r₁ r₂ := by simp [hstE1, h11]
  obtain ⟨stE2, cE2, hcE2, hE2c, hE2mem, hE2regs, hE2_16⟩ : ∃ stE2 cE2,
      Runs w p ω (.cond (.reg 11) (.assign 16 (.reg 2)) .nop) stE1 .normal stE2 cE2 ∧
      cE2 ≤ 4 ∧ stE2.mem = stD.mem ∧ (∀ r, r ≠ 16 → stE2.regs r = stD.regs r) ∧
      stE2.regs 16 = root := by
    by_cases hs0 : ssSide s r₁ r₂ = 0
    · refine ⟨stE1, _, runs_cond_false (by rw [← hs0]; exact Expr.eval_reg_of_eq h11')
        (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), by simp, rfl, fun r hr => by
          simp [hstE1, Function.update_of_ne hr], by simp [hstE1, hroot, hs0]⟩
    · have ha := runs_assign_of (w := w) (p := p) (ω := ω) (r := 16) (st := stE1)
        (Expr.eval_reg_of_eq (r := 2) (v := r₂) (by simp [hstE1, hA.2.2.1]))
      refine ⟨_, _, runs_cond_true (Expr.eval_reg_of_eq h11') hs0 ha, by simp, rfl,
        fun r hr => by simp [hstE1, Function.update_of_ne hr], by simp [hroot, hs0]⟩
  have hE2_0 : stE2.regs 0 = tourH := (hE2regs 0 (by norm_num)).trans hA.1
  have hE2_7 : stE2.regs 7 = cur := (hE2regs 7 (by norm_num)).trans h7
  -- the list
  have hfoot : ∀ a, T.rep.foot tourH tx a → a < cur := SSFrame.foot_lt hfoot₀ hF
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hlist, hle, hresp, hcost⟩ :=
    T.listMarked_runs tourH root cur s tx stE2.mem stE2.pos ω htour hrootV (by omega)
      (hE2mem ▸ hF.1) hfoot (hE2mem ▸ hF.2.1) (by omega)
  have hargs : evalArgs w stE2 [.reg 0, .reg 16, .reg 7] = some [tourH, root, cur] :=
    evalArgs_cons (Expr.eval_reg_of_eq hE2_0) (evalArgs_cons (Expr.eval_reg_of_eq hE2_16)
      (evalArgs_cons (Expr.eval_reg_of_eq hE2_7) (evalArgs_nil w stE2)))
  have hcall := runs_call_of (r := 8) (ω := ω) hargs hproc hrun
  set cur' := o.value with hcur'
  set stE3 : State := { st₁ with regs := Function.update stE2.regs 8 cur' } with hstE3
  have hF' : SSFrame T tourH last h v v' s tx₀ mem₀ cur' tx' st₁.mem :=
    SSFrame.respects hfoot₀ hlast (hE2mem ▸ hF) hrep' hresp
  have hlen : st₁.mem cur = (s.markedList root).length := hlist.1
  have ha18 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 18) (st := stE3)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (r := 7) (v := cur) (by simp [hstE3, hE2_7]))
      hlen)
  set stE4 : State := { stE3 with regs := Function.update stE3.regs 18 (s.markedList root).length } with hstE4
  have hcur'le : cur' ≤ cur + S.listSpace (s.markedList root).length := hresp.2.1
  have hcopyw : cur' + (s.markedList root).length + 1 < 2 ^ w := by omega
  have hcp := ssCopy_runs (p := p) (ω := ω) stE4 (src := cur) (dst := cur') (len := (s.markedList root).length)
    (by simp [hstE4, hstE3, hE2_7]) (by simp [hstE4, hstE3]) (by simp [hstE4]) (by omega)
    hcopyw
  obtain ⟨stE5, cE5, hrE5, hcE5, hposE5, hregsE5, hmemE5⟩ := hcp
  have h6 : stE5.regs 6 = h := by
    rw [hregsE5 6 (by norm_num)]; simp [hstE4, hstE3, hE2regs 6 (by norm_num), hA.2.2.2.2.2.2]
  have h11E : stE5.regs 11 = ssSide s r₁ r₂ := by
    rw [hregsE5 11 (by norm_num)]; simp [hstE4, hstE3, hE2regs 11 (by norm_num), h11]
  have h8E : stE5.regs 8 = cur' := by rw [hregsE5 8 (by norm_num)]; simp [hstE4, hstE3]
  have h18E : stE5.regs 18 = (s.markedList root).length := by rw [hregsE5 18 (by norm_num)]; simp [hstE4]
  have hhw : h + 3 < 2 ^ w := by have := hF.2.2.1; omega
  have hs1 := runs_store_of (w := w) (p := p) (ω := ω) (st := stE5)
    (a := .bin .add (.reg 6) (.const 2)) (e := .reg 11)
    (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_const (k := 2) (by omega)) (by omega))
    (Expr.eval_reg_of_eq h11E)
  set stE6 : State := { stE5 with mem := Function.update stE5.mem (h + 2) (ssSide s r₁ r₂) }
    with hstE6
  have hs2 := runs_store_of (w := w) (p := p) (ω := ω) (st := stE6)
    (a := .bin .add (.reg 6) (.const 3)) (e := .reg 8)
    (Expr.eval_add (Expr.eval_reg_of_eq (r := 6) (v := h) (by simp [hstE6, h6]))
      (Expr.eval_const (k := 3) (by omega)) (by omega))
    (Expr.eval_reg_of_eq (r := 8) (v := cur') (by simp [hstE6, h8E]))
  set stE7 : State := { stE6 with mem := Function.update stE6.mem (h + 3) cur' } with hstE7
  have hret : Runs w p ω (.ret (.bin .add (.bin .add (.reg 8) (.reg 18)) (.const 1))) stE7
      (.returned (cur' + 1 + (s.markedList root).length)) stE7 6 := by
    refine runs_ret_iff.mpr ⟨cur' + 1 + (s.markedList root).length, ?_, rfl, rfl, rfl⟩
    have := Expr.eval_add (w := w) (st := stE7)
      (Expr.eval_add (Expr.eval_reg_of_eq (r := 8) (v := cur') (by simp [hstE7, hstE6, h8E]))
        (Expr.eval_reg_of_eq (r := 18) (v := (s.markedList root).length)
          (by simp [hstE7, hstE6, h18E])) (by omega))
      (Expr.eval_const (k := 1) h1w) (by omega)
    rw [this]; congr 1; omega
  have hrun_all := runs_seq_normal ha1 (runs_seq_normal hcE2 (runs_seq_normal hcall
    (runs_seq_normal ha18 (runs_seq_normal hrE5 (runs_seq_normal hs1
      (runs_seq_normal hs2 hret))))))
  -- the final memory
  have hmemF : ∀ a, stE7.mem a = if a = h + 3 then cur' else if a = h + 2 then ssSide s r₁ r₂
      else if cur' ≤ a ∧ a < cur' + ((s.markedList root).length + 1) then st₁.mem (cur + (a - cur'))
      else st₁.mem a := by
    intro a
    by_cases h3 : a = h + 3
    · simp [hstE7, h3]
    · by_cases h2 : a = h + 2
      · simp [hstE7, hstE6, h2]
      · rw [ite_eq_right h3, ite_eq_right h2]
        show Function.update (Function.update stE5.mem (h + 2) _) (h + 3) cur' a = _
        rw [Function.update_of_ne h3, Function.update_of_ne h2, hmemE5]
  have hcur5 : h + 5 ≤ cur := hF.2.2.1
  have hcurle : cur + 1 + (s.markedList root).length ≤ cur' := hle
  have hlow : ∀ a, a < cur' → a ≠ h + 2 → a ≠ h + 3 → stE7.mem a = st₁.mem a := by
    intro a ha h2 h3
    rw [hmemF, ite_eq_right h3, ite_eq_right h2, ite_eq_right (by omega)]
  obtain ⟨-, hz', -, hft', hfr', hv1, hv2, hv4, hl'⟩ := hF'
  -- the tour state is unchanged by the writes after the list call
  have hagree : ∀ a, T.rep.foot tourH tx' a → st₁.mem a = stE7.mem a := by
    intro a ha
    have hlt : a < cur' := by
      rcases hft' a ha with ha | ⟨-, ha⟩
      · have := hfoot₀ a ha; omega
      · exact ha
    have h2 : a ≠ h + 2 := by
      rintro rfl; rcases hft' _ ha with ha | ⟨ha, -⟩
      · have := hfoot₀ _ ha; omega
      · omega
    have h3 : a ≠ h + 3 := by
      rintro rfl; rcases hft' _ ha with ha | ⟨ha, -⟩
      · have := hfoot₀ _ ha; omega
      · omega
    exact (hlow a hlt h2 h3).symm
  obtain ⟨hrepF, hphiF⟩ := T.rep_local tourH s tx' st₁.mem stE7.mem hagree
  refine ⟨stE7, _, tx', cur', hrun_all, hrepF hrep', ?_, ?_, ?_, ?_, ?_, ⟨?_, fun i hi => ?_⟩,
    hcurle, hresp.2.1, ?_, ?_, ?_, hft', ?_⟩
  · rw [hlow h (by omega) (by omega) (by omega)]; exact hv1
  · rw [hlow (h + 1) (by omega) (by omega) (by omega)]; exact hv2
  · rw [hmemF, ite_eq_right (by omega), ite_eq_left rfl]
  · rw [hmemF, ite_eq_left rfl]
  · rw [hlow (h + 4) (by omega) (by omega) (by omega)]; exact hv4
  · rw [hmemF, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨le_rfl, by omega⟩, Nat.sub_self,
      Nat.add_zero]
    exact hlen
  · rw [hmemF, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
      show cur + (cur' + 1 + i - cur') = cur + 1 + i by omega]
    exact hlist.2 i hi
  · intro a ha
    rw [hmemF, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hz' a (by omega)
  · intro hl0
    rcases hlast with hl1 | ⟨hl1, -⟩
    · exact absurd hl1 hl0
    · rw [hlow (last + 4) (by omega) (by omega) (by omega)]; exact hl' hl0
  · intro a ha hn hl0
    rw [hlow a (by omega) (by omega) (by omega)]; exact hfr' a ha hn hl0
  · rw [← hphiF]
    have hphiD : T.rep.phi tourH tx stE2.mem = T.rep.phi tourH tx stD.mem := by rw [hE2mem]
    simp only [Expr.size_reg, Expr.size_bin, Expr.size_const, Expr.size_load, argsSize_cons,
      argsSize_nil]
    omega

end Tail

end MinCostFlow.SparseCore.Program
