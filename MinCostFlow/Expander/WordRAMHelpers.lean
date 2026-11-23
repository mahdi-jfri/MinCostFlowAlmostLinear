module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import WordRAM.Entry
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.Expander.GraphHelpers

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared Word-RAM Helpers for Section 8 Expander Implementations

Provides:
1. `Program.HasAt` slicing and `NoRand` preservation (`forUp_noRand`, `forRange_noRand`,
   `relocStmt_noRand`, `runner_noRand`).
2. `RunsTo` word-size output-length (`runsTo_length_lt`) and `2 ^ wordSize c x` bounds.
3. Deterministic `.rand` elimination (`stripRandStmt`, `stripRandProg`) preserving `fun _ => false`
   executions within a `2×` cost factor (`runsTo_stripRand`), plus a black-box block-level
   variant (`runs_stripRand_block`) via infinite-loop prefix trapping.
4. Direct `.call` helper around `WordRAM.runner_spec` (`runs_call_runner_stripRand`), plus
   unit-fraction rational rounding and handshaking (`sum_deg_eq_two_mul_m`).
-/

public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ### 1. Program.HasAt and NoRand helpers -/

lemma hasAt_append_left {p : Program} {b : ℕ} {A B : List Stmt}
    (h : p.HasAt b (A ++ B)) : p.HasAt b A := by
  intro i hi
  have hi' : i < (A ++ B).length := by simp; omega
  simpa [List.getElem_append_left hi] using h i hi'

lemma hasAt_append_right {p : Program} {b : ℕ} {A B : List Stmt}
    (h : p.HasAt b (A ++ B)) : p.HasAt (b + A.length) B := by
  intro i hi
  have hi' : A.length + i < (A ++ B).length := by simp; omega
  have hget := h (A.length + i) hi'
  rw [show b + (A.length + i) = b + A.length + i by omega,
    List.getElem_append_right (by omega)] at hget
  simpa using hget

lemma hasAt_cons_tail {p : Program} {b : ℕ} {hd : Stmt} {tl : List Stmt}
    (h : p.HasAt b (hd :: tl)) : p.HasAt (b + 1) tl :=
  hasAt_append_right (A := [hd]) (B := tl) h

lemma forUp_noRand (r : ℕ) (hi : Expr) (body : Stmt) (hb : body.NoRand) :
    (forUp r hi body).NoRand := by
  simp [forUp, Stmt.NoRand, hb]

lemma forRange_noRand (r : ℕ) (lo hi : Expr) (body : Stmt) (hb : body.NoRand) :
    (forRange r lo hi body).NoRand := by
  simp [forRange, forUp, Stmt.NoRand, hb]

lemma relocStmt_noRand (R b : ℕ) : ∀ s : Stmt, s.NoRand → (relocStmt R b s).NoRand
  | .nop, _ => by simp [relocStmt, Stmt.NoRand]
  | .assign r e, _ => by simp [relocStmt, Stmt.NoRand]
  | .store a e, _ => by simp [relocStmt, Stmt.NoRand]
  | .rand _, h => h.elim
  | .seq s t, h => by
    simp only [relocStmt.eq_5, Stmt.NoRand]
    exact ⟨relocStmt_noRand R b s h.1, relocStmt_noRand R b t h.2⟩
  | .cond e s t, h => by
    simp only [relocStmt.eq_6, Stmt.NoRand]
    exact ⟨relocStmt_noRand R b s h.1, relocStmt_noRand R b t h.2⟩
  | .loop e body, h => by
    simp only [relocStmt.eq_7, Stmt.NoRand]
    exact relocStmt_noRand R b body h
  | .call r f args, _ => by simp [relocStmt.eq_8, Stmt.NoRand]
  | .ret e, _ => by simp [relocStmt.eq_9, Stmt.NoRand]

lemma runnerEntry_noRand (Q : Program) (c b : ℕ) : (runnerEntry Q c b).NoRand := by
  have h1 : (computeWordSizeStmt c 0 1 3 4 5 6 7).NoRand := by
    cases c <;> simp [computeWordSizeStmt, Stmt.NoRand]
  have h2 : (copyWordsStmt 0 6 1 5).NoRand := by
    simp [copyWordsStmt, Stmt.NoRand]
  simp [runnerEntry, Stmt.NoRand, h1, h2]

lemma runner_noRand {Q : Program} (hQ : Q.IsDeterministic) (c b : ℕ) :
    ∀ s ∈ runner Q c b, s.NoRand := by
  intro s hs
  simp only [runner, List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨q, hq, rfl⟩
  · exact runnerEntry_noRand Q c b
  · exact relocStmt_noRand Q.regBound b q (hQ q hq)

/-! ### 2. Word-size, register-bound, and RunsTo output bounds -/

lemma expr_eval_lt_pow {w : ℕ} {st : State}
    (hregs : ∀ r, st.regs r < 2 ^ w) (hmem : ∀ a, st.mem a < 2 ^ w) :
    ∀ {e : Expr} {v : ℕ}, e.eval w st = some v → v < 2 ^ w
  | .const _, _, he => by
    simp only [Expr.eval] at he
    split_ifs at he with hk
    cases he; exact hk
  | .reg r, _, he => by
    simp only [Expr.eval] at he
    cases he
    exact hregs r
  | .load a, _, he => by
    simp only [Expr.eval] at he
    cases ha : a.eval w st with
    | none => simp [ha] at he
    | some x =>
      simp only [ha, Option.map_some, Option.some.injEq] at he
      subst he
      exact hmem x
  | .bin _ a b, _, he => by
    simp only [Expr.eval] at he
    cases ha : a.eval w st with
    | none => simp [ha] at he
    | some va =>
      cases hb : b.eval w st with
      | none => simp [ha, hb] at he
      | some vb =>
        simp only [ha, hb] at he
        split_ifs at he with hv
        cases he; exact hv

lemma evalArgs_lt_pow {w : ℕ} {st : State}
    (hregs : ∀ r, st.regs r < 2 ^ w) (hmem : ∀ a, st.mem a < 2 ^ w) :
    ∀ {args : List Expr} {vs : List ℕ},
      evalArgs w st args = some vs → ∀ v ∈ vs, v < 2 ^ w
  | [], _, h, v, hv => by
    simp [evalArgs] at h
    cases h
    simp at hv
  | a :: as, vs, h, v, hv => by
    simp only [evalArgs] at h
    cases ha : a.eval w st with
    | none => simp [ha] at h
    | some va =>
      cases has : evalArgs w st as with
      | none => simp [ha, has] at h
      | some vas =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact expr_eval_lt_pow hregs hmem ha
        · exact evalArgs_lt_pow hregs hmem has v hv'

private lemma readWord_lt_two_pow (ω : ℕ → Bool) (pos w : ℕ) :
    readWord ω pos w < 2 ^ w := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih =>
    have h := ih (pos + 1)
    simp only [readWord, pow_succ']
    split_ifs <;> omega

lemma exec_outcome_lt_pow {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ fuel s st o st' c,
      exec w p ω fuel s st = some (o, st', c) →
      (∀ r, st.regs r < 2 ^ w) →
      (∀ a, st.mem a < 2 ^ w) →
      (∀ r, st'.regs r < 2 ^ w) ∧ (∀ a, st'.mem a < 2 ^ w) ∧ o.value < 2 ^ w := by
  intro fuel
  induction fuel with
  | zero => intro s st o st' c h; simp [exec] at h
  | succ fuel ih =>
    intro s st o st' c h hregs hmem
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨hregs, hmem, by simp [Outcome.value, hpos]⟩
    | assign r e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have hv := expr_eval_lt_pow hregs hmem he
        refine ⟨fun r' => ?_, hmem, by simp [Outcome.value, hpos]⟩
        by_cases hrr : r' = r
        · subst hrr; simpa using hv
        · simpa [hrr] using hregs r'
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st with
      | none => simp [ha] at h
      | some va =>
        cases he : e.eval w st with
        | none => simp [ha, he] at h
        | some ve =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          have hv := expr_eval_lt_pow hregs hmem he
          refine ⟨hregs, fun x => ?_, by simp [Outcome.value, hpos]⟩
          by_cases hxa : x = va
          · subst hxa; simpa using hv
          · simpa [hxa] using hmem x
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      refine ⟨fun r' => ?_, hmem, by simp [Outcome.value, hpos]⟩
      by_cases hrr : r' = r
      · subst hrr; simpa using readWord_lt_two_pow ω st.pos w
      · simpa [hrr] using hregs r'
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases h1 : exec w p ω fuel s₁ st with
      | none => simp [h1] at h
      | some res1 =>
        rcases res1 with ⟨o1, st1, c1⟩
        cases o1 with
        | returned u =>
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          have res := ih s₁ st (.returned u) st1 c1 h1 hregs hmem
          rcases h with ⟨rfl, rfl, rfl⟩
          exact res
        | normal =>
          simp only [h1] at h
          cases h2 : exec w p ω fuel s₂ st1 with
          | none => simp [h2] at h
          | some res2 =>
            rcases res2 with ⟨o2, st2, c2⟩
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            have ⟨hr1, hm1, _⟩ := ih s₁ st .normal st1 c1 h1 hregs hmem
            have res := ih s₂ st1 o2 st2 c2 h2 hr1 hm1
            rcases h with ⟨rfl, rfl, rfl⟩
            exact res
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        cases h1 : exec w p ω fuel (if v = 0 then s₂ else s₁) st with
        | none => simp [h1] at h
        | some res =>
          rcases res with ⟨o1, st1, c1⟩
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          have res := ih _ st o1 st1 c1 h1 hregs hmem
          rcases h with ⟨rfl, rfl, rfl⟩
          exact res
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        split_ifs at h with hv
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨hregs, hmem, by simp [Outcome.value, hpos]⟩
        · cases h1 : exec w p ω fuel body st with
          | none => simp [h1] at h
          | some res1 =>
            rcases res1 with ⟨o1, st1, c1⟩
            cases o1 with
            | returned u =>
              simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
              have res := ih body st (.returned u) st1 c1 h1 hregs hmem
              rcases h with ⟨rfl, rfl, rfl⟩
              exact res
            | normal =>
              simp only [h1] at h
              cases h2 : exec w p ω fuel (.loop e body) st1 with
              | none => simp [h2] at h
              | some res2 =>
                rcases res2 with ⟨o2, st2, c2⟩
                simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
                have ⟨hr1, hm1, _⟩ := ih body st .normal st1 c1 h1 hregs hmem
                have res := ih (.loop e body) st1 o2 st2 c2 h2 hr1 hm1
                rcases h with ⟨rfl, rfl, rfl⟩
                exact res
    | call r f args =>
      simp only [exec] at h
      cases hargs : evalArgs w st args with
      | none => simp [hargs] at h
      | some vs =>
        cases hproc : p.procs[f]? with
        | none => simp [hargs, hproc] at h
        | some body =>
          simp only [hargs, hproc] at h
          cases h1 : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
          | none =>
            simp only [List.getD_eq_getElem?_getD] at h1 h
            simp [h1] at h
          | some res1 =>
            rcases res1 with ⟨o1, st1, c1⟩
            simp only [List.getD_eq_getElem?_getD] at h1 h
            rw [h1] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            have hvs : ∀ i, vs.getD i 0 < 2 ^ w := by
              intro i
              by_cases hi : i < vs.length
              · rw [List.getD_eq_getElem _ _ hi]
                exact evalArgs_lt_pow hregs hmem hargs vs[i] (List.getElem_mem hi)
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
                exact hpos
            have ⟨_, hm1, ho1⟩ :=
              ih body { st with regs := fun i => vs.getD i 0 } o1 st1 c1
                (by simpa only [List.getD_eq_getElem?_getD] using h1) hvs hmem
            rcases h with ⟨rfl, rfl, rfl⟩
            refine ⟨fun r' => ?_, hm1, by simp [Outcome.value, hpos]⟩
            by_cases hrr : r' = r
            · subst hrr
              simp only [Function.update_self]
              cases o1 <;> exact ho1
            · simpa [hrr] using hregs r'
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact ⟨hregs, hmem, by simp [Outcome.value, expr_eval_lt_pow hregs hmem he]⟩

lemma runsTo_length_lt {c : ℕ} (hc : 1 ≤ c) {Q : Program} {x : List ℕ} {ω : ℕ → Bool}
    {out : List ℕ} {cost : ℕ} (hrun : RunsTo (wordSize c x) Q x ω out cost) :
    out.length < 2 ^ wordSize c x := by
  obtain ⟨o, st, ⟨fuel, hfuel⟩, hout⟩ := runsTo_iff_exists_runs.mp hrun
  have hinitMem : ∀ a, initMem x a < 2 ^ wordSize c x := by
    intro a
    by_cases ha : a < x.length
    · simp only [initMem, List.getD_eq_getElem _ _ ha]
      exact lt_two_pow_wordSize_of_mem hc (List.getElem_mem ha)
    · simp only [initMem, List.getD_eq_default _ _ (Nat.le_of_not_lt ha)]
      exact Nat.two_pow_pos _
  have ⟨hregs, _, _⟩ := exec_outcome_lt_pow fuel _ _ o st cost hfuel
    (fun _ => Nat.two_pow_pos _) hinitMem
  have hlen : out.length = st.regs 0 := by
    rw [← hout]
    simp
  rw [hlen]
  exact hregs 0

lemma two_pow_log_succ_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (Nat.log 2 n + 1) ≤ 2 * n := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  rw [pow_succ']
  omega

lemma two_pow_wordSize_le (c : ℕ) (x : List ℕ) :
    2 ^ wordSize c x ≤ (2 * (x.length + x.foldr max 0 + 2)) ^ c := by
  unfold wordSize
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (two_pow_log_succ_le (by omega)) c

lemma exists_unit_frac_le {α : ℝ} (hα : 0 < α) :
    ∃ D : ℕ, 1 ≤ D ∧ (1 : ℝ) / D ≤ α := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hα
  exact ⟨k + 1, by omega, by simpa [Nat.cast_add, Nat.cast_one] using hk.le⟩

lemma sum_deg_eq_two_mul_m {G : Graph} (hGv : G.IsValid) :
    ∑ v ∈ G.verts, G.deg v = 2 * G.m := by
  have hvol : G.vol G.verts = 2 * G.m := vol_verts_of_isValid hGv
  rw [← hvol]
  unfold Graph.vol Graph.volIn Graph.deg
  rfl

/-! ### 3. Deterministic `.rand` elimination (`stripRandStmt`, `stripRandProg`) -/

@[expose] def stripRandStmt : Stmt → Stmt
  | .nop => .nop
  | .assign r e => .assign r e
  | .store a e => .store a e
  | .rand r => .assign r (.const 0)
  | .seq s t => .seq (stripRandStmt s) (stripRandStmt t)
  | .cond e s t => .cond e (stripRandStmt s) (stripRandStmt t)
  | .loop e body => .loop e (stripRandStmt body)
  | .call r f args => .call r f args
  | .ret e => .ret e

@[expose] def stripRandProg (Q : Program) : Program :=
  ⟨Q.procs.map stripRandStmt⟩

lemma stripRandStmt_noRand : ∀ s : Stmt, (stripRandStmt s).NoRand
  | .nop => trivial
  | .assign _ _ => trivial
  | .store _ _ => trivial
  | .rand _ => trivial
  | .seq s t => ⟨stripRandStmt_noRand s, stripRandStmt_noRand t⟩
  | .cond _ s t => ⟨stripRandStmt_noRand s, stripRandStmt_noRand t⟩
  | .loop _ body => stripRandStmt_noRand body
  | .call _ _ _ => trivial
  | .ret _ => trivial

lemma stripRandProg_isDeterministic (Q : Program) : (stripRandProg Q).IsDeterministic := by
  intro s hs
  simp only [stripRandProg, List.mem_map] at hs
  rcases hs with ⟨q, _, rfl⟩
  exact stripRandStmt_noRand q

lemma stripRandStmt_regBound : ∀ s : Stmt, (stripRandStmt s).regBound = s.regBound
  | .nop => rfl
  | .assign _ _ => rfl
  | .store _ _ => rfl
  | .rand r => by
    change max (r + 1) (Expr.const 0).regBound = r + 1
    simp [Expr.regBound]
  | .seq s t => by
    show max (stripRandStmt s).regBound (stripRandStmt t).regBound = max s.regBound t.regBound
    rw [stripRandStmt_regBound s, stripRandStmt_regBound t]
  | .cond e s t => by
    show max e.regBound (max (stripRandStmt s).regBound (stripRandStmt t).regBound) =
      max e.regBound (max s.regBound t.regBound)
    rw [stripRandStmt_regBound s, stripRandStmt_regBound t]
  | .loop e body => by
    show max e.regBound (stripRandStmt body).regBound = max e.regBound body.regBound
    rw [stripRandStmt_regBound body]
  | .call _ _ _ => rfl
  | .ret _ => rfl

private lemma foldr_regBound_stripRand (l : List Stmt) :
    (l.map stripRandStmt).foldr (fun s acc => max s.regBound acc) 0 =
      l.foldr (fun s acc => max s.regBound acc) 0 := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, List.foldr_cons, stripRandStmt_regBound, ih]

lemma stripRandProg_regBound (Q : Program) : (stripRandProg Q).regBound = Q.regBound := by
  unfold Program.regBound stripRandProg
  exact congrArg (max 1) (foldr_regBound_stripRand Q.procs)

lemma runnerScale_stripRandProg (Q : Program) :
    runnerScale (stripRandProg Q) = runnerScale Q := by
  simp [runnerScale, stripRandProg_regBound]

lemma readWord_false (pos w : ℕ) : readWord (fun _ => false) pos w = 0 := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih => simp [readWord, ih (pos + 1)]

lemma eval_congr_mem_regs {w : ℕ} {st₁ st₂ : State}
    (hregs : st₁.regs = st₂.regs) (hmem : st₁.mem = st₂.mem) :
    ∀ e : Expr, e.eval w st₁ = e.eval w st₂ := by
  intro e
  induction e with
  | const k => rfl
  | reg r => simp [Expr.eval, hregs]
  | load a ih => simp [Expr.eval, ih, hmem]
  | bin op a b iha ihb => simp [Expr.eval, iha, ihb]

lemma evalArgs_congr_mem_regs {w : ℕ} {st₁ st₂ : State}
    (hregs : st₁.regs = st₂.regs) (hmem : st₁.mem = st₂.mem) :
    ∀ args : List Expr, evalArgs w st₁ args = evalArgs w st₂ args
  | [] => rfl
  | a :: as => by
    simp only [evalArgs, eval_congr_mem_regs hregs hmem a, evalArgs_congr_mem_regs hregs hmem as]

private lemma exec_loop_true_none {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ fuel st, exec w p ω fuel (.loop (.const 1) .nop) st = none := by
  intro fuel
  induction fuel with
  | zero => intro st; rfl
  | succ fuel ih =>
    intro st
    rw [exec]
    simp only [Expr.eval]
    split_ifs with h1
    · cases fuel with
      | zero => rfl
      | succ k =>
        have hnop : exec w p ω (k + 1) .nop st = some (.normal, st, 1) := rfl
        have hloop : exec w p ω (k + 1) (.loop (.const 1) .nop) st = none := ih st
        dsimp only
        rw [hnop]
        dsimp only
        rw [hloop]
        simp only [ite_eq_right_iff]
        intro hfalse; simp at hfalse
    · rfl

lemma exec_stripRand_gen {w : ℕ} {Q Q' : Program} {ω : ℕ → Bool}
    (hcall : ∀ (f : ℕ) (body : Stmt), Q.procs[f]? = some body →
      body = .loop (.const 1) .nop ∨ Q'.procs[f]? = some (stripRandStmt body)) :
    ∀ fuel s st₁ st₂ o st₁' c,
      st₁.regs = st₂.regs →
      st₁.mem = st₂.mem →
      exec w Q (fun _ => false) fuel s st₁ = some (o, st₁', c) →
      ∃ st₂' c',
        exec w Q' ω fuel (stripRandStmt s) st₂ = some (o, st₂', c') ∧
        st₂'.regs = st₁'.regs ∧ st₂'.mem = st₁'.mem ∧ c' ≤ 2 * c := by
  intro fuel
  induction fuel with
  | zero => intro s st₁ st₂ o st₁' c _ _ h; simp [exec] at h
  | succ fuel ih =>
    intro s st₁ st₂ o st₁' c hregs hmem h
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨st₂, 1, by simp [stripRandStmt, exec], hregs.symm, hmem.symm, by omega⟩
    | assign r e =>
      simp only [exec] at h
      cases he : e.eval w st₁ with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have he2 : e.eval w st₂ = some v := (eval_congr_mem_regs hregs hmem e).symm.trans he
        exact ⟨{ mem := st₂.mem, regs := Function.update st₂.regs r v, pos := st₂.pos },
          e.size + 1, by simp [stripRandStmt, exec, he2], by simp [hregs], hmem.symm, by omega⟩
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st₁ with
      | none => simp [ha] at h
      | some va =>
        cases he : e.eval w st₁ with
        | none => simp [ha, he] at h
        | some ve =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          have ha2 : a.eval w st₂ = some va := (eval_congr_mem_regs hregs hmem a).symm.trans ha
          have he2 : e.eval w st₂ = some ve := (eval_congr_mem_regs hregs hmem e).symm.trans he
          exact ⟨{ mem := Function.update st₂.mem va ve, regs := st₂.regs, pos := st₂.pos },
            a.size + e.size + 1,
            by simp [stripRandStmt, exec, ha2, he2], hregs.symm, by simp [hmem], by omega⟩
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
      refine ⟨{ st₂ with regs := Function.update st₂.regs r 0 }, (Expr.const 0).size + 1,
        ?_, ?_, hmem.symm, ?_⟩
      · simp [stripRandStmt, exec, Expr.eval, hpos]
      · simp [hregs, readWord_false]
      · simp [Expr.size]
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases h1 : exec w Q (fun _ => false) fuel s₁ st₁ with
      | none => simp [h1] at h
      | some res1 =>
        rcases res1 with ⟨o1, st1, c1⟩
        cases o1 with
        | returned u =>
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          rcases ih s₁ st₁ st₂ (.returned u) st1 c1 hregs hmem h1 with
            ⟨st₂', c1', h1', hr1, hm1, hc1⟩
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨st₂', c1' + 1, by simp [stripRandStmt, exec, h1'], hr1, hm1, by omega⟩
        | normal =>
          simp only [h1] at h
          cases h2 : exec w Q (fun _ => false) fuel s₂ st1 with
          | none => simp [h2] at h
          | some res2 =>
            rcases res2 with ⟨o2, st2, c2⟩
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            rcases ih s₁ st₁ st₂ .normal st1 c1 hregs hmem h1 with
              ⟨st1', c1', h1', hr1, hm1, hc1⟩
            rcases ih s₂ st1 st1' o2 st2 c2 hr1.symm hm1.symm h2 with
              ⟨st₂', c2', h2', hr2, hm2, hc2⟩
            rcases h with ⟨rfl, rfl, rfl⟩
            exact ⟨st₂', c1' + c2' + 1, by simp [stripRandStmt, exec, h1', h2'], hr2, hm2,
              by omega⟩
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w st₁ with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        cases h1 : exec w Q (fun _ => false) fuel (if v = 0 then s₂ else s₁) st₁ with
        | none => simp [h1] at h
        | some res =>
          rcases res with ⟨o1, st1, c1⟩
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          have he2 : e.eval w st₂ = some v := (eval_congr_mem_regs hregs hmem e).symm.trans he
          have hite : stripRandStmt (if v = 0 then s₂ else s₁) =
              if v = 0 then stripRandStmt s₂ else stripRandStmt s₁ := by
            split_ifs <;> rfl
          rcases ih _ st₁ st₂ o1 st1 c1 hregs hmem h1 with ⟨st₂', c1', h1', hr1, hm1, hc1⟩
          rw [hite] at h1'
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨st₂', e.size + c1' + 1, by simp [stripRandStmt, exec, he2, h1'], hr1, hm1,
            by omega⟩
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st₁ with
      | none => simp [he] at h
      | some v =>
        have he2 : e.eval w st₂ = some v := (eval_congr_mem_regs hregs hmem e).symm.trans he
        simp only [he] at h
        split_ifs at h with hv
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨st₂, e.size + 1, by simp [stripRandStmt, exec, he2, hv], hregs.symm, hmem.symm,
            by omega⟩
        · cases h1 : exec w Q (fun _ => false) fuel body st₁ with
          | none => simp [h1] at h
          | some res1 =>
            rcases res1 with ⟨o1, st1, c1⟩
            cases o1 with
            | returned u =>
              simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
              rcases ih body st₁ st₂ (.returned u) st1 c1 hregs hmem h1 with
                ⟨st₂', c1', h1', hr1, hm1, hc1⟩
              rcases h with ⟨rfl, rfl, rfl⟩
              exact ⟨st₂', e.size + c1' + 1, by simp [stripRandStmt, exec, he2, hv, h1'],
                hr1, hm1, by omega⟩
            | normal =>
              simp only [h1] at h
              cases h2 : exec w Q (fun _ => false) fuel (.loop e body) st1 with
              | none => simp [h2] at h
              | some res2 =>
                rcases res2 with ⟨o2, st2, c2⟩
                simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
                rcases ih body st₁ st₂ .normal st1 c1 hregs hmem h1 with
                  ⟨st1', c1', h1', hr1, hm1, hc1⟩
                rcases ih (.loop e body) st1 st1' o2 st2 c2 hr1.symm hm1.symm h2 with
                  ⟨st₂', c2', h2', hr2, hm2, hc2⟩
                simp only [stripRandStmt] at h2'
                rcases h with ⟨rfl, rfl, rfl⟩
                exact ⟨st₂', e.size + c1' + c2' + 1,
                  by simp [stripRandStmt, exec, he2, hv, h1', h2'], hr2, hm2, by omega⟩
    | call r f args =>
      simp only [exec] at h
      cases hargs : evalArgs w st₁ args with
      | none => simp [hargs] at h
      | some vs =>
        cases hproc : Q.procs[f]? with
        | none => simp [hargs, hproc] at h
        | some body =>
          rcases hcall f body hproc with rfl | hproc2
          · simp [hargs, hproc, exec_loop_true_none] at h
          · simp only [hargs, hproc] at h
            cases h1 : exec w Q (fun _ => false) fuel body
                { st₁ with regs := fun i => vs.getD i 0 } with
            | none =>
              simp only [List.getD_eq_getElem?_getD] at h1 h
              simp [h1] at h
            | some res1 =>
              rcases res1 with ⟨o1, st1, c1⟩
              simp only [List.getD_eq_getElem?_getD] at h1 h
              have hargs2 : evalArgs w st₂ args = some vs :=
                (evalArgs_congr_mem_regs hregs hmem args).symm.trans hargs
              rcases ih body { st₁ with regs := fun i => vs.getD i 0 }
                  { st₂ with regs := fun i => vs.getD i 0 } o1 st1 c1 rfl hmem
                  (by simpa only [List.getD_eq_getElem?_getD] using h1) with
                ⟨st2, c1', h1', _, hm1, hc1⟩
              rw [h1] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              refine ⟨{ mem := st2.mem, regs := Function.update st₂.regs r o1.value, pos := st2.pos },
                argsSize args + c1' + 1, ?_, by cases o1 <;> simp [hregs, Outcome.value], hm1,
                by omega⟩
              simp only [stripRandStmt, exec, hargs2, hproc2, List.getD_eq_getElem?_getD]
              simp only [List.getD_eq_getElem?_getD] at h1'
              rw [h1']
              cases o1 <;> rfl
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st₁ with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have he2 : e.eval w st₂ = some v := (eval_congr_mem_regs hregs hmem e).symm.trans he
        exact ⟨st₂, e.size + 1, by simp [stripRandStmt, exec, he2], hregs.symm, hmem.symm,
          by omega⟩

lemma exec_stripRand {w : ℕ} {Q : Program} {ω : ℕ → Bool} :
    ∀ fuel s st₁ st₂ o st₁' c,
      st₁.regs = st₂.regs →
      st₁.mem = st₂.mem →
      exec w Q (fun _ => false) fuel s st₁ = some (o, st₁', c) →
      ∃ st₂' c',
        exec w (stripRandProg Q) ω fuel (stripRandStmt s) st₂ = some (o, st₂', c') ∧
        st₂'.regs = st₁'.regs ∧ st₂'.mem = st₁'.mem ∧ c' ≤ 2 * c :=
  exec_stripRand_gen fun f body hproc => Or.inr (by simp [stripRandProg, hproc])

lemma runsTo_stripRand {w : ℕ} {Q : Program} {x : List ℕ} {out : List ℕ} {cost : ℕ}
    (h : RunsTo w Q x (fun _ => false) out cost) :
    ∀ ω, ∃ cost', RunsTo w (stripRandProg Q) x ω out cost' ∧ cost' ≤ 2 * cost := by
  intro ω
  obtain ⟨o, st, ⟨fuel, hfuel⟩, hout⟩ := runsTo_iff_exists_runs.mp h
  rcases exec_stripRand (ω := ω) fuel (.call 0 0 [.const x.length]) _ _ o st cost rfl rfl hfuel with
    ⟨st', c', h', hr, hm, hc⟩
  refine ⟨c', runsTo_iff_exists_runs.mpr ⟨o, st', ⟨fuel, h'⟩, ?_⟩, hc⟩
  rw [← hout]
  have hr0 : st'.regs 0 = st.regs 0 := congrFun hr 0
  rw [hr0]
  refine List.map_congr_left fun i _ => ?_
  exact congrFun hm i

lemma trapProg_hasAt (b : ℕ) (orig : List Stmt) :
    (⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ : Program).HasAt b orig := by
  intro i hi
  rw [List.getElem?_append_right (by simp), List.length_replicate,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi]

lemma exec_stripRand_block {b : ℕ} {orig : List Stmt} {p' : Program}
    (hp' : p'.HasAt b (orig.map stripRandStmt)) {w : ℕ} {ω : ℕ → Bool} :
    ∀ fuel s st₁ st₂ o st₁' c,
      st₁.regs = st₂.regs →
      st₁.mem = st₂.mem →
      exec w ⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ (fun _ => false) fuel s st₁ =
        some (o, st₁', c) →
      ∃ st₂' c',
        exec w p' ω fuel (stripRandStmt s) st₂ = some (o, st₂', c') ∧
        st₂'.regs = st₁'.regs ∧ st₂'.mem = st₁'.mem ∧ c' ≤ 2 * c := by
  refine exec_stripRand_gen fun f body hproc => ?_
  by_cases hfb : f < b
  · left
    have hget : (List.replicate b (.loop (.const 1) .nop) ++ orig)[f]? =
        some (.loop (.const 1) .nop) := by
      rw [List.getElem?_append_left (by simp [hfb]), List.getElem?_replicate]
      simp [hfb]
    exact Option.some.inj (hproc.symm.trans hget)
  · right
    have hfb_ge : b ≤ f := Nat.le_of_not_lt hfb
    have hlt : f - b < orig.length := by
      by_contra hge
      have hnone : (List.replicate b (.loop (.const 1) .nop) ++ orig)[f]? = none := by
        rw [List.getElem?_append_right (by simp [hfb_ge]), List.length_replicate]
        exact List.getElem?_eq_none (by omega)
      rw [hnone] at hproc
      cases hproc
    have hget : (List.replicate b (.loop (.const 1) .nop) ++ orig)[f]? = some orig[f - b] := by
      rw [List.getElem?_append_right (by simp [hfb_ge]), List.length_replicate,
        List.getElem?_eq_getElem hlt]
    have hbody := Option.some.inj (hproc.symm.trans hget)
    subst hbody
    have hpget := hp' (f - b) (by simpa using hlt)
    rw [show b + (f - b) = f by omega] at hpget
    simpa [List.getElem_map] using hpget

/-! ### 5. Running `runner (stripRandProg Q)` via `.call` -/

lemma runs_call_runner_stripRand {w : ℕ} {p Q : Program} {ω : ℕ → Bool}
    {r b_run c : ℕ} {aExpr lenExpr hExpr : Expr} {st : State}
    {a len h cost_Q : ℕ} {x out : List ℕ}
    (hp : p.HasAt b_run (runner (stripRandProg Q) c b_run))
    (hargs : evalArgs w st [aExpr, lenExpr, hExpr] = some [a, len, h])
    (ha_le : a + len ≤ h) (hlen : len = x.length) (hlist : ListAt st.mem a x)
    (hzero : ZeroFrom st.mem h)
    (hw_bound : h + 2 ^ (wordSize c x + 1) + 2 ≤ 2 ^ w)
    (hrun : RunsTo (wordSize c x) Q x (fun _ => false) out cost_Q) :
    ∃ st' c_call,
      Runs w p ω (.call r b_run [aExpr, lenExpr, hExpr]) st .normal st' c_call ∧
      st'.regs = Function.update st.regs r (h + 1 + 2 ^ wordSize c x) ∧
      st'.mem h = out.length ∧
      ListAt st'.mem (h + 1) out ∧
      (∀ j < h, st'.mem j = st.mem j) ∧
      ZeroFrom st'.mem (h + 1 + 2 ^ wordSize c x) ∧
      c_call ≤ aExpr.size + lenExpr.size + hExpr.size +
        runnerScale Q * (2 * cost_Q + len + wordSize c x + 1) + 1 := by
  obtain ⟨cost', hrun', hcost'⟩ := runsTo_stripRand hrun (subBits w (wordSize c x) st.pos ω)
  obtain ⟨body, o, st1, c_H, hproc, hruns, hval, hlen_mem, hout, hframe, hzero', hcH⟩ :=
    runner_spec hp ha_le hlen hlist hzero hw_bound hrun'
  have hstart : startState [a, len, h] st.mem st.pos =
      { st with regs := fun i => ([a, len, h] : List ℕ).getD i 0 } := by
    cases st; rfl
  rw [hstart] at hruns
  refine ⟨{ st1 with regs := Function.update st.regs r o.value },
    argsSize [aExpr, lenExpr, hExpr] + c_H + 1,
    runs_call_iff.mpr ⟨[a, len, h], body, o, st1, c_H, hargs, hproc, hruns, rfl, rfl, rfl⟩,
    ?_, hlen_mem, hout, hframe, hzero', ?_⟩
  · simp [hval]
  · rw [runnerScale_stripRandProg] at hcH
    have hmul : runnerScale Q * (cost' + len + wordSize c x + 1) ≤
        runnerScale Q * (2 * cost_Q + len + wordSize c x + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [argsSize]
    omega

end MinCostFlow.Expander
