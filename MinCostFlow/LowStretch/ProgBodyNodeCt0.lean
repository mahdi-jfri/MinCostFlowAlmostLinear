module

public import MinCostFlow.LowStretch.ProgBodyNode
import MinCostFlow.LowStretch.ProgBodyNodeCongr

/-!
# The target of child `0` in the node part

`ct0` stores the target of child `0` at `CT[0]` (register `35`). Without a special petal it is
the target of the cluster (register `52`). With one, it is the outer end of the special portal:
register `59` gets the address `IN + 3 PT[0]` of the two ends of the portal pair, and the end
that is not the center `CC[1]` of the special petal is the target. `runs_seq_ct0` gives the run
at the level of registers and memory: the memory gains one cell and only register `59` changes.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- **The store of `CT[0]`**, followed by a statement `s`. The value `e` is the target `t` in
register `52` without a special petal (flag `0` in register `53`). With one (flag `1`), it is the
end of the pair `pr = PT[0]` at `IN + 3 pr` that is not `CC[1]`, where `IN` is read at `GB + 3`. -/
theorem runs_seq_ct0 {w : ℕ} {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → Prop}
    {s : Stmt} {st : State} {k T : ℕ} {sp : Bool} {CT t e : ℕ}
    (r53 : st.regs 53 = if sp then 1 else 0) (r35 : st.regs 35 = CT) (r52 : st.regs 52 = t)
    (hw : 3 < 2 ^ w)
    (hsp : sp = true → ∃ GB PT CC IN pr, st.regs 60 = GB ∧ st.regs 37 = PT ∧
      st.regs 36 = CC ∧ st.mem (GB + 3) = IN ∧ st.mem PT = pr ∧ GB + 3 < 2 ^ w ∧
      CC + 1 < 2 ^ w ∧ IN + 3 * pr + 1 < 2 ^ w ∧
      e = if st.mem (IN + 3 * pr) = st.mem (CC + 1) then st.mem (IN + 3 * pr + 1)
        else st.mem (IN + 3 * pr))
    (hnsp : sp = false → e = t)
    (hrest : ∀ regs' : ℕ → ℕ, (∀ r, r ≠ 59 → regs' r = st.regs r) →
      ∃ o st' c, Runs w p ω s { st with regs := regs', mem := Function.update st.mem CT e }
        o st' c ∧ Q o st' ∧ (k + 60) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq ct0 s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hw1 : 1 < 2 ^ w := by omega
  unfold ct0
  refine runs_seq_cond_le (v := if sp then 1 else 0) (Expr.eval_reg_of_eq r53) (fun hv => ?_)
    (fun hv => ?_)
  · have hs : sp = true := by cases sp <;> simp_all
    obtain ⟨GB, PT, CC, IN, pr, r60, r37, r36, hIN, hpr, hGB, hCC, hIN3, he⟩ := hsp hs
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := IN + 3 * pr)
      (Expr.eval_add (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r60)
          (Expr.eval_const (by omega)) hGB) hIN)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_load_of_eq
          (Expr.eval_reg_of_eq r37) hpr) (by omega)) (by omega)) ?_
    set st1 : State := { st with regs := Function.update st.regs 59 (IN + 3 * pr) } with hst1
    have q59 : st1.regs 59 = IN + 3 * pr := by simp [hst1]
    have q35 : st1.regs 35 = CT := by simp [hst1, r35]
    have q36 : st1.regs 36 = CC := by simp [hst1, r36]
    have hm : st1.mem = st.mem := rfl
    have hrest' := hrest st1.regs (fun r hr => by simp [hst1, hr])
    by_cases hx : st.mem (IN + 3 * pr) = st.mem (CC + 1)
    · simp only [hx, ↓reduceIte] at he
      refine runs_seq_cond_le (v := 1) (Expr.eval_eq_true (Expr.eval_load (Expr.eval_reg_of_eq q59))
          (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq q36) (Expr.eval_const (by omega))
            hCC)) hx hw1) (fun _ => ?_) (fun h0 => absurd h0 (by omega))
      refine runs_seq_store_le (x := CT) (v := e) (Expr.eval_reg_of_eq q35)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq q59) (Expr.eval_const
          (by omega)) (by omega)) he.symm) ?_
      obtain ⟨o, st', c, hr, hq, hc⟩ := hrest'
      refine ⟨o, st', c, hr, hq, ?_⟩
      simp only [Expr.size] at hc ⊢
      omega
    · simp only [hx, ↓reduceIte] at he
      refine runs_seq_cond_le (v := 0) (Expr.eval_eq_false
          (Expr.eval_load (Expr.eval_reg_of_eq q59))
          (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq q36) (Expr.eval_const (by omega))
            hCC)) hx hw1) (fun h0 => absurd rfl h0) (fun _ => ?_)
      refine runs_seq_store_le (x := CT) (v := e) (Expr.eval_reg_of_eq q35)
        (Expr.eval_load_of_eq (Expr.eval_reg_of_eq q59) he.symm) ?_
      obtain ⟨o, st', c, hr, hq, hc⟩ := hrest'
      refine ⟨o, st', c, hr, hq, ?_⟩
      simp only [Expr.size] at hc ⊢
      omega
  · have hs : sp = false := by cases sp <;> simp_all
    have he := hnsp hs
    refine runs_seq_store_le (x := CT) (v := e) (Expr.eval_reg_of_eq r35)
      (Expr.eval_reg_of_eq (r52.trans he.symm)) ?_
    obtain ⟨o, st', c, hr, hq, hc⟩ := hrest st.regs (fun _ _ => rfl)
    refine ⟨o, st', c, hr, hq, ?_⟩
    simp only [Expr.size] at hc ⊢
    omega

/-- **The target of child `0` with a special petal** is the end of the special portal that is
not the center of the special petal (`hv_succ`). -/
theorem Cl.raw_zero_t_sp {G : PG} {c : Cl} {D : Cl.Dec} (hsp : D.sp = true)
    (hi : (D.pd 0).i < (D.pd 0).hw.length) :
    (c.raw G D 0).t = G.other (D.portal 0) (D.xc G 0) := by
  simp only [Cl.raw, hsp, ↓reduceIte, Cl.Dec.yc, Cl.Dec.portal, Cl.Dec.xc]
  exact hv_succ G _ _ _ hi

/-- **The target of child `0` without a special petal** is the target of the cluster. -/
theorem Cl.raw_zero_t {G : PG} {c : Cl} {D : Cl.Dec} (hsp : D.sp = false) :
    (c.raw G D 0).t = c.t := by
  simp [Cl.raw, hsp]

end MinCostFlow.LowStretch
