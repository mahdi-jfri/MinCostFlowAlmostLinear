module

public import MinCostFlow.SparseCore.Program.OutStepSplitA

/-!
# One split of the output step, second part

The second part of a split round (`osSplitB`) runs after the first record of the split has been
applied to the stored graph. It reads the degrees of `v'` and `v`, picks the vertex `x` of the
smaller side (`osChoose`), copies the incidence list `L` of `x` to the edit region, and writes the
head `[tag, v, v', |L|]` of the edit in front of it. This file proves that the edit written is
`outSplitEdit` and that it has `updateEnc + 3` words (`osSplitB_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- **The choice of the smaller side.** -/
theorem osChoose_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {v v' d d' : ℕ}
    (h21 : st.regs 21 = v) (h22 : st.regs 22 = v') (h31 : st.regs 31 = d') (h32 : st.regs 32 = d)
    (hw : 3 < 2 ^ w) :
    ∃ st' c, Runs w p ω osChoose st .normal st' c ∧ st'.mem = st.mem ∧
      st'.regs 33 = (if d < d' then v else v') ∧ st'.regs 34 = (if d < d' then 3 else 2) ∧
      st'.regs 35 = (if d < d' then 2 else 1) ∧
      (∀ r, r ≠ 33 → r ≠ 34 → r ≠ 35 → st'.regs r = st.regs r) ∧ c ≤ 40 := by
  obtain ⟨st₁, hr₁, hm₁, h33₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 33)
    (e := .reg 22) (v := v') (Expr.eval_reg_of_eq h22)
  obtain ⟨st₂, hr₂, hm₂, h34₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 34)
    (e := .const 2) (st := st₁) (v := 2) (Expr.eval_const (by omega))
  obtain ⟨st₃, hr₃, hm₃, h35₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 35)
    (e := .const 1) (st := st₂) (v := 1) (Expr.eval_const (by omega))
  have g : ∀ r, r ≠ 33 → r ≠ 34 → r ≠ 35 → st₃.regs r = st.regs r :=
    fun r a b c => by rw [ho₃ r c, ho₂ r b, ho₁ r a]
  have hcond := Expr.eval_lt_op (w := w) (st := st₃) (Expr.eval_reg_of_eq
    (by rw [g 32 (by omega) (by omega) (by omega), h32]))
    (Expr.eval_reg_of_eq (by rw [g 31 (by omega) (by omega) (by omega), h31])) (by omega)
  by_cases hlt : d < d'
  · rw [ite_eq_left hlt] at hcond
    obtain ⟨st₄, hr₄, hm₄, h33₄, ho₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 33)
      (e := .reg 21) (st := st₃) (v := v)
      (Expr.eval_reg_of_eq (by rw [g 21 (by omega) (by omega) (by omega), h21]))
    obtain ⟨st₅, hr₅, hm₅, h34₅, ho₅⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 34)
      (e := .const 3) (st := st₄) (v := 3) (Expr.eval_const (by omega))
    obtain ⟨st₆, hr₆, hm₆, h35₆, ho₆⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 35)
      (e := .const 2) (st := st₅) (v := 2) (Expr.eval_const (by omega))
    refine ⟨st₆, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
      (step_cond_true hcond one_ne_zero (runs_seq_normal hr₄ (runs_seq_normal hr₅ hr₆))))),
      by rw [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁], ?_, ?_, ?_, fun r a b c => ?_, ?_⟩
    · rw [ho₆ 33 (by omega), ho₅ 33 (by omega), h33₄, ite_eq_left hlt]
    · rw [ho₆ 34 (by omega), h34₅, ite_eq_left hlt]
    · rw [h35₆, ite_eq_left hlt]
    · rw [ho₆ r c, ho₅ r b, ho₄ r a, g r a b c]
    · simp only [Expr.size]; omega
  · rw [ite_eq_right hlt] at hcond
    refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
      (step_cond_false hcond step_nop))), by rw [hm₃, hm₂, hm₁], ?_, ?_, ?_, g, ?_⟩
    · rw [ho₃ 33 (by omega), ho₂ 33 (by omega), h33₁, ite_eq_right hlt]
    · rw [ho₃ 34 (by omega), h34₂, ite_eq_right hlt]
    · rw [h35₃, ite_eq_right hlt]
    · simp only [Expr.size]; omega

/-- The vertices of the graph after a split. -/
theorem mem_applySplit_V {G : MGraph} {v v' x : ℕ} {St Sh : Finset ℕ} :
    x ∈ (G.applyUpdate (.split v v' St Sh)).V ↔ x = v' ∨ x ∈ G.V :=
  Finset.mem_insert

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- **The second part of a split round**: the edit of the split, with its incidence list. -/
theorem osSplitB_runs (hC : SCtx T A tx₀) {gd wk : ℕ}
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hwk : p.procs[wk]? = some outWalkBody)
    {st : State} {v v' : ℕ} {St Sh : Finset ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) U E bp ep cur s tx st.mem)
    (hR : SRegs st A vCap eCap) (h16 : st.regs 16 = ep) (h21 : st.regs 21 = v)
    (h22 : st.regs 22 = v')
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w)
    (hGv : G.IsValid) (hval : G.UpdateIsValid (.split v v' St Sh))
    (hroom : ep + 4 + 2 * eCap ≤ A.t0) :
    ∃ stB cB L, (∀ rest o st'' c', Runs w p ω rest stB o st'' c' →
        Runs w p ω (osSplitB gd wk rest) st o st'' (cB + c')) ∧
      SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) U E bp ep cur s tx stB.mem ∧
      T.rep.phi A.tourH tx stB.mem = T.rep.phi A.tourH tx st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 34 → r ≠ 35 → r ≠ 36 → stB.regs r = st.regs r) ∧
      stB.regs 34 = (if (G.applyUpdate (.split v v' St Sh)).deg v <
        (G.applyUpdate (.split v v' St Sh)).deg v' then 3 else 2) ∧
      stB.regs 36 = L.length ∧ L.Nodup ∧
      (∀ k, k ∈ L ↔ k < 2 * eCap ∧ (endOfKey k).1 ∈ (G.applyUpdate (.split v v' St Sh)).E ∧
        (G.applyUpdate (.split v v' St Sh)).src (endOfKey k) =
          if (G.applyUpdate (.split v v' St Sh)).deg v <
            (G.applyUpdate (.split v v' St Sh)).deg v' then v else v') ∧
      ListAt stB.mem (ep + 4) L ∧
      decodeOrdEdit stB.mem ep = (outSplitEdit G v v' St Sh, 4 + L.length) ∧
      L.length + 1 = G.updateEnc (.split v v' St Sh) ∧
      cB ≤ 30 * L.length + 400 := by
  set G' := G.applyUpdate (.split v v' St Sh) with hG'
  have hR' := hR
  obtain ⟨-, -, -, -, -, -, -, r10, -, -, -, -, -, r23, r24, r25⟩ := hR'
  have hgh := hC.2.2.1
  have hvw : vCap + eCap + 2 < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow two_ne_zero _) hw
  have h9 : 9 ≤ (vCap + eCap + 2) ^ 2 := by
    have hv1 : 1 ≤ vCap := by
      have := (hB.2.2.2.2.2.2.1).2.1 v' (mem_applySplit_V.mpr (Or.inl rfl)); omega
    exact Nat.pow_le_pow_left (by omega : 3 ≤ vCap + eCap + 2) 2
  have hw16 : 16 ≤ 2 ^ w := rs_sixteen_le (by omega)
  have hbp2 := hB.2.2.2.2.2.2.2.2.1
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hG := hB.2.2.2.2.2.2.1
  have hgw : A.g + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hvV : v ∈ G'.V := mem_applySplit_V.mpr (Or.inr hval.1)
  have hv'V : v' ∈ G'.V := mem_applySplit_V.mpr (Or.inl rfl)
  -- the two degrees
  obtain ⟨st₁, c₁, hr₁, hm₁, h31₁, ho₁, hc₁⟩ := os_deg (ω := ω) (dst := 31) hgd hG r10 h22 hv'V
    hw16 hgw
  obtain ⟨st₂, c₂, hr₂, hm₂, h32₂, ho₂, hc₂⟩ := os_deg (ω := ω) (dst := 32) (st := st₁) hgd
    (by rw [hm₁]; exact hG) (by rw [ho₁ 10 (by omega), r10]) (by rw [ho₁ 21 (by omega), h21]) hvV
    hw16 hgw
  have g₂ : ∀ r, r ≠ 31 → r ≠ 32 → st₂.regs r = st.regs r :=
    fun r a b => by rw [ho₂ r b, ho₁ r a]
  -- the choice
  obtain ⟨st₃, c₃, hr₃, hm₃, h33₃, h34₃, h35₃, ho₃, hc₃⟩ := osChoose_runs (w := w) (p := p) (ω := ω)
    (st := st₂) (by rw [g₂ 21 (by omega) (by omega), h21])
    (by rw [g₂ 22 (by omega) (by omega), h22]) (by rw [ho₂ 31 (by omega), h31₁]) h32₂ (by omega)
  set x := if G'.deg v < G'.deg v' then v else v' with hx
  have hxV : x ∈ G'.V := by rw [hx]; split_ifs <;> assumption
  have g₃ : ∀ r, r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 34 → r ≠ 35 → st₃.regs r = st.regs r :=
    fun r a b c d e => by rw [ho₃ r c d e, g₂ r a b]
  have hm₃' : st₃.mem = st.mem := by rw [hm₃, hm₂, hm₁]
  -- the incidence list of `x`
  obtain ⟨hslot, L, hL, hLmem⟩ := DynGraphAt.incList hG hxV
  have hLnd : L.Nodup := hL.1
  have hLlt : ∀ k ∈ L, k < 2 * eCap := hL.2.1
  have hLlen : L.length ≤ 2 * eCap := nodup_length_le_of_lt hLnd hLlt
  have hlay : dgIncHeadBase A.g vCap + vCap ≤ A.g + dynGraphSize vCap eCap ∧
      dgExtToIntBase A.g vCap + vCap ≤ A.g + dynGraphSize vCap eCap ∧
      dgHeNextBase A.g vCap eCap + 2 * eCap ≤ A.g + dynGraphSize vCap eCap := by
    unfold dgIncHeadBase dgExtToIntBase dgHeNextBase dynGraphSize; omega
  have hxc : x < vCap := hG.2.1 x hxV
  have hB₃ : SBase T A tx₀ mem₀ S₀ G' U E bp ep cur s tx st₃.mem := by rw [hm₃']; exact hB
  obtain ⟨st₄, c₄, hr₄, hB₄, hp₄, hL₄, hag₄, h36₄, ho₄, hc₄⟩ := os_walk (ω := ω) (r := 36)
    (args := [.reg 25, .bin .add (.reg 24) (.load (.bin .add (.reg 23) (.reg 33))),
      .bin .add (.reg 16) (.const 4)]) hC hwk hB₃
    (evalArgs_three
      (Expr.eval_reg_of_eq (by rw [g₃ 25 (by omega) (by omega) (by omega) (by omega) (by omega),
        r25]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by rw [g₃ 24 (by omega) (by omega) (by omega)
        (by omega) (by omega), r24]))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [g₃ 23 (by omega)
          (by omega) (by omega) (by omega) (by omega), r23])) (Expr.eval_reg_of_eq h33₃)
          (by omega)) rfl) (by rw [hm₃']; omega))
      (Expr.eval_add (Expr.eval_reg_of_eq (by rw [g₃ 16 (by omega) (by omega) (by omega)
        (by omega) (by omega), h16])) (Expr.eval_const (by omega)) (by omega)))
    (by rw [hm₃']; exact hL)
    (fun k hk => by have := hLlt k hk; omega) (by omega) (by omega)
    (fun j hj => by rw [hm₃']; omega) (fun k hk j hj => by have := hLlt k hk; omega)
    (fun j hj => ⟨by omega, by omega, by omega, by omega⟩)
  have g₄ : ∀ r, r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 34 → r ≠ 35 → r ≠ 36 →
      st₄.regs r = st.regs r := fun r a b c d e f => by rw [ho₄ r f, g₃ r a b c d e]
  -- the head of the edit
  obtain ⟨st₅, hr₅, hB₅, hp₅, hm₅, hg₅⟩ := os_store (p := p) (ω := ω) (a := .reg 16)
    (e := .reg 35) hC hB₄ (Expr.eval_reg_of_eq (by rw [g₄ 16 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), h16]))
    (Expr.eval_reg_of_eq (by rw [ho₄ 35 (by omega), h35₃])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₆, hr₆, hB₆, hp₆, hm₆, hg₆⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 1)) (e := .reg 21) hC hB₅
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, g₄ 16 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), h16])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₅, g₄ 21 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h21])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₇, hr₇, hB₇, hp₇, hm₇, hg₇⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 2)) (e := .reg 22) hC hB₆
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, g₄ 16 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), h16])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, g₄ 22 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), h22])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₈, hr₈, hB₈, hp₈, hm₈, hg₈⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 3)) (e := .reg 36) hC hB₇
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₇, hg₆, hg₅, g₄ 16 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), h16])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₇, hg₆, hg₅, h36₄])) ⟨by omega, by omega, by omega, by omega⟩
  have hag : ∀ y, ¬ (ep ≤ y ∧ y < ep + 4) → st₈.mem y = st₄.mem y := by
    intro y hy
    rw [hm₈, hm₇, hm₆, hm₅]
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | omega
  have hL₈ : ListAt st₈.mem (ep + 4) L := fun i hi => by rw [hag _ (by omega)]; exact hL₄ i hi
  have htag : (if G'.deg v < G'.deg v' then 2 else 1) = 1 ∨
      (if G'.deg v < G'.deg v' then 2 else 1) = 2 := by split_ifs <;> simp
  have hdec := decodeOrdEdit_move (mem := st₈.mem) (a := ep) (v := v) (v' := v') (keys := L)
    htag (by simp [hm₈, hm₇, hm₆, hm₅, Function.update_apply])
    (by simp [hm₈, hm₇, hm₆, hm₅, Function.update_apply])
    (by simp [hm₈, hm₇, hm₆, hm₅, Function.update_apply])
    (by simp [hm₈, Function.update_apply]) hL₈
  have hGE : ∀ e ∈ G.E, e < eCap := fun e he => hG.2.2.1 e he
  obtain ⟨hedit, henc⟩ := outSplitEdit_eq_incList hGv hval hGE hLnd hx hLmem
  rw [← hedit] at hdec
  have hrun := fun rest o st'' c' (hrest : Runs w p ω rest st₈ o st'' c') =>
    runs_seq_cont hr₁ (runs_seq_cont hr₂ (runs_seq_cont hr₃ (runs_seq_cont hr₄
      (runs_seq_last (runs_seq_normal hr₅ (runs_seq_normal hr₆ (runs_seq_normal hr₇ hr₈)))
        hrest))))
  refine ⟨st₈, _, L, hrun, hB₈, ?_, ?_, ?_, ?_, hLnd, hLmem, hL₈, hdec, henc, ?_⟩
  · rw [hp₈, hp₇, hp₆, hp₅, hp₄, hm₃']
  · intro r a b c d e f
    rw [hg₈, hg₇, hg₆, hg₅, g₄ r a b c d e f]
  · rw [hg₈, hg₇, hg₆, hg₅, ho₄ 34 (by omega), h34₃]
  · rw [hg₈, hg₇, hg₆, hg₅, h36₄]
  · simp only [argsSize, Expr.size, List.map, List.sum_cons, List.sum_nil] at hc₄ ⊢
    omega

end MinCostFlow.SparseCore.Program
