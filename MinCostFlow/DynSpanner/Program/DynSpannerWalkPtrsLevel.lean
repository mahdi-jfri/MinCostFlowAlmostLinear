module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkPtrsDefs

/-!
# Walk pointers of the affected edges: invariant and level lookup

`WPInv c i st` is the invariant of the loop of `dsWalkPtrsStmt` after `i` edges: the fixed
registers hold the bases of the state, the counter is `i`, the first `i` table entries hold the
walk pointers, and memory outside the table is unchanged.

`dsWalkPtrs_findLevel_triple` is the level lookup `findEmbLevel inDom_mid j e`. Its code and proof
are those of `dsFilterAffected_findLevel_triple`, with `WPInv` in place of the invariant of the
filter. The lookup only reads the fixed area, so any invariant that fixes this area works.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Invariant of the loop of `dsWalkPtrsStmt` after `i` edges. -/
def WPInv (c : FilterCtx) (i : ℕ) (st : State) : Prop :=
  FilterFixedRegs c st ∧
  st.regs 14 = i ∧
  (∀ k (hk : k < c.cand.length), k < i → st.mem (c.outArrPtr + k) = c.walkPtr c.cand[k]) ∧
  ∀ addr, (addr < c.outArrPtr ∨ c.outArrPtr + c.candLen ≤ addr) → st.mem addr = c.mem0 addr

lemma WPInv.read_fix {c : FilterCtx} {idx : ℕ} {st : State} (h : WPInv c idx st)
    {addr : ℕ} (ha : addr < c.b + dsFixedSize c.L c.vCap c.eCap) : st.mem addr = c.mem0 addr :=
  h.2.2.2 addr (Or.inl (lt_of_lt_of_le ha c.hfix_out))

lemma WPInv.read_cand {c : FilterCtx} {idx : ℕ} {st : State} (h : WPInv c idx st)
    {k : ℕ} (hk : k < c.candLen) :
    st.mem (c.candPtr + k) = c.cand[k]'(by have := c.hcand_len; omega) := by
  rw [h.2.2.2 _ (c.hcand_out k hk)]
  simpa using c.hm_cand k (by have := c.hcand_len; omega)

lemma WPInv.of_regs_agree {c : FilterCtx} {idx : ℕ} {st st' : State}
    (h : WPInv c idx st) (hmem : st'.mem = st.mem)
    (hr : ∀ r ≤ 14, r ≠ 12 → st'.regs r = st.regs r) (_hr12 : st'.regs 12 = st.regs 12) :
    WPInv c idx st' := by
  rcases h with ⟨hf, h14, htab, hfr⟩
  exact ⟨hf.agree (fun r hr' hn12 => hr r (by omega) hn12),
    (hr 14 (by omega) (by omega)).trans h14,
    fun k hk hki => (congrFun hmem _).trans (htab k hk hki),
    fun addr ha => (congrFun hmem addr).trans (hfr addr ha)⟩

/-- The level lookup of `dsWalkPtrsBodyStmt`, cost `35 · j + 7`. -/
lemma dsWalkPtrs_findLevel_triple (c : FilterCtx) {p : Program}
    {idx e : ℕ} (he_G : e ∈ c.G'.E) (he_cap : e < c.eCap)
    (rInit : ℕ → ℕ) :
    Triple c.w p
      (fun st => WPInv c idx st ∧ st.regs 15 = e ∧ st.regs 16 = 0 ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (forRange 17 (.const 0) (.reg 1)
        (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
         .cond (.reg 18)
           (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
             (.assign 16 (.reg 17))
             .nop)
           .nop))
      (normalPost fun st => WPInv c idx st ∧ st.regs 15 = e ∧
        st.regs 16 = findEmbLevel c.inDom_mid c.j e ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (fun _ => 35 * c.j + 7) := by
  have hlay := c.lay
  have hw16 := c.hw16
  let stepFn : ℕ → ℕ → ℕ := fun acc i =>
    if hi : i < c.L + 1 then if e ∈ c.inDom_mid ⟨i, hi⟩ then i else acc else acc
  let InvL : ℕ → State → Prop := fun i st =>
    WPInv c idx st ∧
    st.regs 15 = e ∧
    st.regs 16 = (List.range i).foldl stepFn 0 ∧
    st.regs 17 = i ∧
    ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r
  have ht := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st => WPInv c idx st ∧ st.regs 15 = e ∧ st.regs 16 = 0 ∧
      ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
    (r := 17) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
      .cond (.reg 18)
        (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
          (.assign 16 (.reg 17))
          .nop)
        .nop)
    (Inv := InvL) 26 0 c.j
    (Nat.zero_le _) (by omega)
    (fun _ => lt_of_le_of_lt c.hjL (Nat.lt_trans (Nat.lt_succ_self _) hlay.L1_w))
    (fun st ⟨hfm, r15, r16, hfr⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      exact ⟨WPInv.of_regs_agree hfm rfl
        (fun r hr _ => by simp [show r ≠ 17 by omega]) (by simp),
        by simp [r15], by simp [r16], by simp,
        fun r hr h12 => by simp [show r ≠ 17 by omega, hfr r hr h12]⟩)
    (fun i st _ _ hL => hL.2.2.2.1)
    (fun i st _ _ hL => by simp [Expr.eval, hL.1.1.r1])
    (fun i _ hi => by
      intro st ω ⟨hfm, r15, r16, r17, hfr⟩
      have hiL1 : i < c.L + 1 := by have := c.hjL; omega
      have hdg_lt_fix : dsDomGenBase c.b c.L c.vCap c.eCap + i <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have := hlay.ed_eq; have := hlay.pi_eq; have := hlay.sb_eq; have := hlay.sb_le_fix; omega
      have hdg_w : dsDomGenBase c.b c.L c.vCap c.eCap + i < 2 ^ c.w := by
        have := hlay.dom_lt_w; omega
      have hdg_mem : st.mem (dsDomGenBase c.b c.L c.vCap c.eCap + i) =
          c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) := hfm.read_fix hdg_lt_fix
      have hie_lt : i * c.eCap + e < (c.L + 1) * c.eCap := by
        have h1 : i * c.eCap + e < i * c.eCap + c.eCap := by omega
        have h2 : (i + 1) * c.eCap ≤ (c.L + 1) * c.eCap := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at h2; omega
      have hie_w : i * c.eCap + e < 2 ^ c.w := lt_trans hie_lt hlay.Le_w
      have hie_mul_w : i * c.eCap < 2 ^ c.w := by omega
      have hed_lt_fix : dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e) <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have := hlay.pi_eq; have := hlay.sb_eq; have := hlay.sb_le_fix; omega
      have hed_w : dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e) < 2 ^ c.w := by
        have := hlay.ed_lt_w; omega
      have hed_mem : st.mem (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e)) =
          c.mem0 (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + i * c.eCap + e) := by
        rw [hfm.read_fix hed_lt_fix, ← Nat.add_assoc]
      set dg := c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i)
      set eg := c.mem0 (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + i * c.eCap + e)
      suffices hres : ∃ o st' c_1,
          Runs c.w p ω
            (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
             .cond (.reg 18)
               (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
                 (.assign 16 (.reg 17))
                 .nop)
               .nop) st o st' c_1 ∧
            normalPost (fun st' => InvL (i + 1) { st' with regs := Function.update st'.regs 17 (i + 1) } ∧ st'.regs 17 = i) o st' ∧
            0 + c_1 ≤ 26 by
        rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
        dsimp only; exact ⟨o, st', c_1, hr, hq, by omega⟩
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hfm.1.r8)
          (Expr.eval_reg_of_eq r17) hdg_w) hdg_mem) ?_
      have hdom_iff : (0 < dg ∧ eg = dg) ↔ e ∈ c.inDom_mid ⟨i, hiL1⟩ := by
        have hdom0 := c.hdom ⟨i, hiL1⟩ hi e he_cap
        rw [c.hinDom_eq ⟨i, hiL1⟩ hi, Finset.mem_inter]
        exact ⟨fun h => ⟨hdom0.mp h, he_G⟩, fun h => hdom0.mpr h.1⟩
      refine runs_cond_le (v := dg) (Expr.eval_reg_of_eq (r := 18) (v := dg) (by simp)) ?_ ?_
      · intro hdg_nz
        have hdg_pos : 0 < dg := Nat.pos_of_ne_zero hdg_nz
        refine runs_cond_le (v := if eg = dg then 1 else 0)
          (Expr.eval_eq_op
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [hfm.1.r9]))
                (Expr.eval_add
                  (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [r17]))
                    (Expr.eval_reg_of_eq (by simp [hfm.1.r6])) hie_mul_w)
                  (Expr.eval_reg_of_eq (by simp [r15])) hie_w)
                hed_w)
              (by simpa using hed_mem))
            (Expr.eval_reg_of_eq (r := 18) (v := dg) (by simp))
            (by omega)) ?_ ?_
        · intro heg_nz
          have he_in : e ∈ c.inDom_mid ⟨i, hiL1⟩ :=
            hdom_iff.mp ⟨hdg_pos, by by_contra hne; simp [hne] at heg_nz⟩
          refine runs_assign_le (Expr.eval_reg_of_eq (r := 17) (v := i) (by simp [r17])) ?_
            (by dsimp only [Expr.size]; omega)
          refine ⟨⟨WPInv.of_regs_agree hfm rfl
            (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 18 by omega])
            (by simp),
            by simp [r15], ?_, by simp,
            fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
            by simp [r17]⟩
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          dsimp only [stepFn]
          simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17), Function.update_self]
          rw [dite_eq_left_of_eq_true (eq_true hiL1)]
          simp only [eq_true he_in, ↓reduceIte]
        · intro heg_z
          have he_nin : e ∉ c.inDom_mid ⟨i, hiL1⟩ :=
            fun hmem => by simp [(hdom_iff.mpr hmem).2] at heg_z
          refine runs_nop_le ?_ (by dsimp only [Expr.size]; omega)
          refine ⟨⟨WPInv.of_regs_agree hfm rfl
            (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega]) (by simp),
            by simp [r15], ?_, by simp,
            fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
            by simp [r17]⟩
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          dsimp only [stepFn]
          simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17),
            Function.update_of_ne (by decide : (16 : ℕ) ≠ 18), r16]
          rw [dite_eq_left_of_eq_true (eq_true hiL1)]
          simp only [eq_false he_nin, ↓reduceIte]
          rfl
      · intro hdg_z
        have he_nin : e ∉ c.inDom_mid ⟨i, hiL1⟩ := fun hmem => by
          have := (hdom_iff.mpr hmem).1; omega
        refine runs_nop_le ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨WPInv.of_regs_agree hfm rfl
          (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega]) (by simp),
          by simp [r15], ?_, by simp,
          fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
          by simp [r17]⟩
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [stepFn]
        simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17),
          Function.update_of_ne (by decide : (16 : ℕ) ≠ 18), r16]
        rw [dite_eq_left_of_eq_true (eq_true hiL1)]
        simp only [eq_false he_nin, ↓reduceIte]
        rfl)
  refine ht.conseq (fun st h => h) (fun o st' h => by
      cases o with
      | returned _ => exact h
      | normal =>
        refine ⟨h.1, h.2.1, ?_, h.2.2.2.2⟩
        rw [h.2.2.1, findEmbLevel_eq_foldl c.inDom_mid c.hjL e])
    fun st _ => by dsimp only [Expr.size]; omega

end

end MinCostFlow.DynSpanner.Program
