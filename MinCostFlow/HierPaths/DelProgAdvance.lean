module

public import MinCostFlow.HierPaths.DelProgBase
public import MinCostFlow.HierPaths.Cursor

/-!
# The cursor loop of the `Delete` program

`Delete` moves the support cursor of each touched vertex and the cursor of each touched pair
forward to the next valid entry (`advance`, `HierPaths/Cursor.lean`). The program does this with
one loop for both kinds of cursor. `advanceStmt test rc rN rgo rv` keeps the cursor in register
`rc` and the length in register `rN`. In each round, if the cursor is below the length, it runs
`test`, which leaves the validity bit of the entry under the cursor in register `rv`, and then it
stops at a valid entry or moves the cursor one step. Register `rgo` is `1` while the loop runs.

`advanceStmt_triple`: if `test` meets its specification, the loop ends with the cursor at
`advance valid N c`, at cost at most `(advance valid N c - c + 1) · (T + 30) + 2`, where `T`
bounds the cost of `test`. The frame `F` holds everything else the caller needs; it must hold
again after `test` and after writes to `rc` and `rgo`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The cursor loop. -/
def advanceStmt (test : Stmt) (rc rN rgo rv : ℕ) : Stmt :=
  .seq (.assign rgo (.const 1))
    (.loop (.reg rgo)
      (.cond (.bin .lt (.reg rc) (.reg rN))
        (.seq test
          (.cond (.reg rv) (.assign rgo (.const 0))
            (.assign rc (.bin .add (.reg rc) (.const 1)))))
        (.assign rgo (.const 0))))

theorem advanceStmt_noRand {test : Stmt} (ht : test.NoRand) (rc rN rgo rv : ℕ) :
    (advanceStmt test rc rN rgo rv).NoRand := by
  simp [advanceStmt, Stmt.NoRand, ht]

private theorem advance_eq (valid : ℕ → Bool) (N c : ℕ) :
    advance valid N c = if c < N then (if valid c then c else advance valid N (c + 1)) else c := by
  rw [advance]

/-- **The cursor loop.** -/
theorem advanceStmt_triple {w : ℕ} {p : Program} {test : Stmt} {rc rN rgo rv : ℕ}
    (hrc : rc ≠ rgo) (hrN : rN ≠ rgo) (hrNc : rN ≠ rc) (hrvg : rv ≠ rgo)
    {F : State → Prop} {valid : ℕ → Bool} {N T : ℕ} (hw : N + 1 < 2 ^ w)
    (hFN : ∀ s, F s → s.regs rN = N)
    (hFc : ∀ s v, F s → F { s with regs := Function.update s.regs rc v })
    (hFg : ∀ s v, F s → F { s with regs := Function.update s.regs rgo v })
    (htest : ∀ c < N, Triple w p (fun s => F s ∧ s.regs rc = c ∧ s.regs rgo = 1) test
      (normalPost fun s' => F s' ∧ s'.regs rc = c ∧ s'.regs rgo = 1 ∧
        s'.regs rv = if valid c then 1 else 0) (fun _ => T))
    {c₀ : ℕ} (hc₀ : c₀ ≤ N) :
    Triple w p (fun s => F s ∧ s.regs rc = c₀) (advanceStmt test rc rN rgo rv)
      (normalPost fun s' => F s' ∧ s'.regs rc = advance valid N c₀)
      (fun _ => (advance valid N c₀ - c₀ + 1) * (T + 30) + 6) := by
  set A := advance valid N c₀ with hA
  have hcA : c₀ ≤ A := le_advance valid N c₀
  have hAN : A ≤ N := advance_le valid hc₀
  -- The loop invariant.
  let Inv : State → Prop := fun s => F s ∧ (s.regs rgo = 1 ∨ s.regs rgo = 0) ∧
    (s.regs rgo = 1 → s.regs rc ≤ N ∧ s.regs rc ≤ A ∧ advance valid N (s.regs rc) = A) ∧
    (s.regs rgo = 0 → s.regs rc = A)
  let rem : State → ℕ := fun s => if s.regs rgo = 1 then (A + 1 - s.regs rc) * (T + 30) + 2 else 2
  let ms : State → ℕ := fun s => if s.regs rgo = 1 then A + 1 - s.regs rc else 0
  have hw1 : 1 < 2 ^ w := by omega
  have hloop : Triple w p Inv (.loop (.reg rgo)
      (.cond (.bin .lt (.reg rc) (.reg rN))
        (.seq test
          (.cond (.reg rv) (.assign rgo (.const 0))
            (.assign rc (.bin .add (.reg rc) (.const 1)))))
        (.assign rgo (.const 0)))) (normalPost fun s' => F s' ∧ s'.regs rc = A) rem := by
    refine Triple.loop_measure (m := ms) (condVal := fun s => s.regs rgo)
      (fun s _ => Expr.eval_reg_of_eq rfl) ?_ ?_
    · intro s hs h0
      refine ⟨⟨hs.1, hs.2.2.2 h0⟩, ?_⟩
      simp only [rem, h0]; simp [Expr.size]
    · intro s hs hne
      have h1 : s.regs rgo = 1 := hs.2.1.resolve_right hne
      obtain ⟨hcN, hcA', hadv⟩ := hs.2.2.1 h1
      have hN := hFN s hs.1
      by_cases hlt : s.regs rc < N
      · -- the cursor is inside the array: run the test
        set c := s.regs rc with hc
        refine ⟨T + 20, ?_⟩
        have hcond := Triple.cond (p := p) (P := fun s' => s' = s) (e := .bin .lt (.reg rc) (.reg rN))
          (val := fun s' => if s'.regs rc < s'.regs rN then 1 else 0)
          (fun s' _ => Expr.eval_lt_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hw1)
          (s := .seq test (.cond (.reg rv) (.assign rgo (.const 0))
            (.assign rc (.bin .add (.reg rc) (.const 1)))))
          (t := .assign rgo (.const 0))
          (Q := fun o s' => match o with
            | .returned _ => False
            | .normal => Inv s' ∧ ms s' < ms s ∧ 1 + (T + 20) + rem s' + 1 ≤ rem s)
          (T_t := fun _ => T + 15) (T_f := fun _ => 4) ?_ ?_
        · refine hcond.conseq (fun s' h => h) (fun o s' h => ?_) (fun s' hs' => ?_)
          · cases o with
            | returned u => exact h.elim
            | normal => exact h
          · subst hs'; split_ifs <;> simp [Expr.size] <;> omega
        · -- the test runs
          refine Triple.seq_normal (R := fun s1 => F s1 ∧ s1.regs rc = c ∧ s1.regs rgo = 1 ∧
              s1.regs rv = if valid c then 1 else 0)
            ((htest c hlt).weaken_pre fun s' h => by
              obtain ⟨rfl, _⟩ := h; exact ⟨hs.1, rfl, h1⟩) ?_
            (fun _ _ _ _ => le_refl _)
          refine (Triple.cond (val := fun s1 => s1.regs rv)
            (fun s1 _ => Expr.eval_reg_of_eq rfl) ?_ ?_ (T_t := fun _ => 2) (T_f := fun _ => 4)
            (Q := fun o s' => match o with
              | .returned _ => False
              | .normal => Inv s' ∧ ms s' < ms s ∧ 1 + (T + 20) + rem s' + 1 ≤ rem s)).mono_cost
            (fun _ _ => by split_ifs <;> simp [Expr.size] <;> omega)
          · -- valid: stop here
            refine (Triple.assign (val := fun _ => 0) (fun _ _ => Expr.eval_const (by omega))
              (Q := fun s' => Inv s' ∧ ms s' < ms s ∧ 1 + (T + 20) + rem s' + 1 ≤ rem s)
              (fun s1 hs1 => ?_)).conseq (fun _ h => h) (fun o s' h => ?_) (fun _ _ => by
                simp [Expr.size])
            · obtain ⟨⟨hF1, hc1, hg1, hv1⟩, hne1⟩ := hs1
              have hvc : valid c = true := by
                by_contra hh; simp [hh] at hv1; exact hne1 hv1
              have hAc : A = c := by rw [← hadv, advance_of_valid valid hlt hvc]
              refine ⟨⟨hFg _ _ hF1, Or.inr (by simp), fun h => by simp at h, fun _ => ?_⟩, ?_, ?_⟩
              · simp [Function.update_of_ne hrc, hc1, hAc]
              · simp only [ms, h1, ite_true, Function.update_self]; simp; omega
              · simp only [rem, h1, Function.update_self]; simp
                have : A + 1 - c = 1 := by omega
                rw [this]; omega
            · cases o with
              | returned u => exact h
              | normal => exact h
          · -- invalid: move on
            refine (Triple.assign (val := fun s1 => s1.regs rc + 1)
              (fun s1 hs1 => Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega))
                (by rw [hs1.1.2.1]; omega))
              (Q := fun s' => Inv s' ∧ ms s' < ms s ∧ 1 + (T + 20) + rem s' + 1 ≤ rem s)
              (fun s1 hs1 => ?_)).conseq (fun _ h => h) (fun o s' h => ?_) (fun _ _ => by
                simp [Expr.size])
            · obtain ⟨⟨hF1, hc1, hg1, hv1⟩, hz1⟩ := hs1
              have hvc : valid c = false := by
                by_contra hh; simp at hh; simp [hh] at hv1; exact absurd hz1 (by rw [hv1]; omega)
              have hnext : advance valid N (c + 1) = A := by
                rw [← hadv, advance_eq valid N c]; simp [hlt, hvc]
              have hc1A : c + 1 ≤ A := by rw [← hnext]; exact le_advance valid N (c + 1)
              have hg' : (Function.update s1.regs rc (s1.regs rc + 1)) rgo = 1 := by
                rw [Function.update_of_ne (Ne.symm hrc)]; exact hg1
              have hc' : (Function.update s1.regs rc (s1.regs rc + 1)) rc = c + 1 := by
                simp [hc1]
              refine ⟨⟨hFc _ _ hF1, Or.inl hg', fun _ => ?_, fun h => by simp_all⟩, ?_, ?_⟩
              · refine ⟨?_, ?_, ?_⟩ <;> simp only [hc'] <;> omega
              · simp only [ms, hg', h1, ite_true, hc']; omega
              · simp only [rem, hg', h1, ite_true, hc']
                have e1 : A + 1 - c = (A + 1 - (c + 1)) + 1 := by omega
                rw [e1, Nat.add_mul]; omega
            · cases o with
              | returned u => exact h
              | normal => exact h
        · -- not possible: the cursor is below the length
          intro s' ω hs'
          obtain ⟨rfl, hz⟩ := hs'
          simp [hN, ← hc, hlt] at hz
      · -- the cursor is at the end: stop
        have hcN' : s.regs rc = N := by omega
        have hAc : A = s.regs rc := by
          rw [← hadv, advance_eq]; simp [hlt]
        refine ⟨8, ?_⟩
        refine (Triple.cond (p := p) (P := fun s' => s' = s) (e := .bin .lt (.reg rc) (.reg rN))
          (val := fun s' => if s'.regs rc < s'.regs rN then 1 else 0)
          (fun s' _ => Expr.eval_lt_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hw1)
          (T_t := fun _ => 0) (T_f := fun _ => 4)
          (Q := fun o s' => match o with
            | .returned _ => False
            | .normal => Inv s' ∧ ms s' < ms s ∧ 1 + 8 + rem s' + 1 ≤ rem s) ?_ ?_).conseq
          (fun _ h => h) (fun o s' h => ?_) (fun s' hs' => ?_)
        · intro s' ω hs'
          obtain ⟨rfl, hz⟩ := hs'
          simp [hN, hlt] at hz
        · refine (Triple.assign (val := fun _ => 0) (fun _ _ => Expr.eval_const (by omega))
            (Q := fun s' => Inv s' ∧ ms s' < ms s ∧ 1 + 8 + rem s' + 1 ≤ rem s)
            (fun s1 hs1 => ?_)).conseq (fun _ h => h) (fun o s' h => ?_) (fun _ _ => by
              simp [Expr.size])
          · obtain ⟨hs1e, _⟩ := hs1
            rw [hs1e]
            refine ⟨⟨hFg _ _ hs.1, Or.inr (by simp), fun h => by simp at h, fun _ => ?_⟩, ?_, ?_⟩
            · simp [Function.update_of_ne hrc, hAc]
            · simp only [ms, h1, ite_true, Function.update_self]; simp; omega
            · simp only [rem, h1, Function.update_self]; simp
              have : A + 1 - s.regs rc = 1 := by omega
              rw [this]; omega
          · cases o with
            | returned u => exact h
            | normal => exact h
        · cases o with
          | returned u => exact h.elim
          | normal => exact h
        · subst hs'; simp [Expr.size, hN, hlt]
  refine Triple.seq_normal (R := fun s1 => Inv s1 ∧ s1.regs rc = c₀ ∧ s1.regs rgo = 1)
    (Triple.assign (val := fun _ => 1) (fun _ _ => Expr.eval_const hw1) fun s hs => ?_)
    (hloop.weaken_pre fun _ h => h.1) ?_
  · have hg : (Function.update s.regs rgo 1) rgo = 1 := by simp
    have hc : (Function.update s.regs rgo 1) rc = c₀ := by
      rw [Function.update_of_ne hrc]; exact hs.2
    refine ⟨⟨hFg _ _ hs.1, Or.inl hg, fun _ => ?_, fun h => by simp at h⟩, hc, hg⟩
    simp only [hc]
    exact ⟨hc₀, hcA, rfl⟩
  · intro s s1 _ hs1
    simp only [rem, hs1.2.2, ite_true, hs1.2.1]
    have e1 : A + 1 - c₀ = A - c₀ + 1 := by omega
    rw [e1]
    simp [Expr.size]
    omega
