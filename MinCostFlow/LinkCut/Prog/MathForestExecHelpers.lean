module

public import MinCostFlow.LinkCut.Prog.MathForestWalk

/-!
# Word-RAM `exec` Unpacking and Splay Numeric Frame Helpers

Provides inversion lemmas for `WordRAM.exec` and `Expr.eval`, a generic `Stmt.noRet`
checker (`exec_noRet_normal`), read-only procedure framing (`ReadOnlyStmt`, covering `Zero`,
`Less`, `IsNegative`, `UnsignedLess`, and `Equal`), and exact heap-interval bounds for
`Add`, `AddCarry`, `Negate`, `NegateCarry`, and `Subtract` inside `splayBodies`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

section ExecHelpers

theorem eval_bin_some {w : ℕ} {st : State} {op : BinOp} {a b : Expr} {v : ℕ}
    (h : (Expr.bin op a b).eval w st = some v) :
    ∃ x y, a.eval w st = some x ∧ b.eval w st = some y ∧
      op.eval x y < 2 ^ w ∧ v = op.eval x y := by
  simp only [Expr.eval] at h
  cases ha : a.eval w st with
  | none => simp [ha] at h
  | some x =>
      cases hb : b.eval w st with
      | none => simp [ha, hb] at h
      | some y =>
          simp only [ha, hb] at h
          split_ifs at h with hlt
          cases h
          exact ⟨x, y, rfl, rfl, hlt, rfl⟩

theorem eval_const_some {w : ℕ} {st : State} {k v : ℕ}
    (h : (Expr.const k).eval w st = some v) : v = k ∧ k < 2 ^ w := by
  simp only [Expr.eval] at h
  split_ifs at h with hk
  cases h; exact ⟨rfl, hk⟩

theorem evalArgs_cons {w : ℕ} {st : State} {e : Expr} {es : List Expr} {vs : List ℕ} :
    evalArgs w st (e :: es) = some vs ↔
      ∃ v vs', e.eval w st = some v ∧ evalArgs w st es = some vs' ∧ vs = v :: vs' := by
  constructor
  · intro h
    simp only [evalArgs] at h
    cases hv : e.eval w st with
    | none => simp [hv] at h
    | some v =>
        cases hvs : evalArgs w st es with
        | none => simp [hv, hvs] at h
        | some vs' => simp [hv, hvs] at h; exact ⟨v, vs', rfl, rfl, h.symm⟩
  · rintro ⟨v, vs', hv, hvs, rfl⟩
    simp [evalArgs, hv, hvs]

theorem evalArgs_nil {w : ℕ} {st : State} {vs : List ℕ} :
    evalArgs w st [] = some vs ↔ vs = [] := by
  simp [evalArgs]

theorem eval_nodePtr_some {w : ℕ} {st : State} {r0 r1 v : ℕ}
    (h : (nodePtrExpr r0 r1).eval w st = some v) :
    v = st.regs r0 + NODE_STRIDE * st.regs r1 ∧ v < 2 ^ w := by
  rcases eval_bin_some h with ⟨x, y, hx, hy, hlt, rfl⟩
  simp only [Expr.eval] at hx; cases hx
  rcases eval_bin_some hy with ⟨a, b, ha, hb, _, rfl⟩
  rcases eval_const_some ha with ⟨rfl, _⟩
  simp only [Expr.eval] at hb; cases hb
  exact ⟨rfl, hlt⟩

theorem eval_fieldAddr_some {w : ℕ} {st : State} {ptrReg off v : ℕ}
    (h : (fieldAddrExpr ptrReg off).eval w st = some v) :
    v = st.regs ptrReg + off ∧ v < 2 ^ w := by
  rcases eval_bin_some h with ⟨x, y, hx, hy, hlt, rfl⟩
  simp only [Expr.eval] at hx; cases hx
  rcases eval_const_some hy with ⟨rfl, _⟩
  exact ⟨rfl, hlt⟩

theorem eval_fieldLoad_some {w : ℕ} {st : State} {ptrReg off v : ℕ}
    (h : (fieldLoadExpr ptrReg off).eval w st = some v) :
    v = st.mem (st.regs ptrReg + off) := by
  simp only [fieldLoadExpr, Expr.eval, Option.map_eq_some_iff] at h
  rcases h with ⟨addr, ha, rfl⟩
  rcases eval_fieldAddr_some ha with ⟨rfl, _⟩
  rfl

theorem eval_sub_reg_const {w : ℕ} {st : State} {r k v : ℕ}
    (h : (Expr.bin .sub (.reg r) (.const k)).eval w st = some v) :
    v = st.regs r - k := by
  rcases eval_bin_some h with ⟨x, y, hx, hy, _, rfl⟩
  simp only [Expr.eval] at hx; cases hx
  rcases eval_const_some hy with ⟨rfl, _⟩
  rfl

theorem exec_nop_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {st st' : State} {o : Outcome} {c : ℕ} :
    exec w p ω fuel .nop st = some (o, st', c) ↔
      0 < fuel ∧ o = .normal ∧ st' = st ∧ c = 1 := by
  cases fuel with
  | zero => simp [exec]
  | succ f => simp [exec]; aesop

theorem exec_assign_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {r : ℕ} {e : Expr} {st st' : State} {o : Outcome} {c : ℕ} :
    exec w p ω fuel (.assign r e) st = some (o, st', c) ↔
      ∃ f v, fuel = f + 1 ∧ e.eval w st = some v ∧ o = .normal ∧
        st' = { st with regs := Function.update st.regs r v } ∧ c = e.size + 1 := by
  cases fuel with
  | zero => simp [exec]
  | succ f =>
      simp only [exec]
      cases e.eval w st with
      | none => simp
      | some v => simp; aesop

theorem exec_store_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {a e : Expr} {st st' : State} {o : Outcome} {c : ℕ} :
    exec w p ω fuel (.store a e) st = some (o, st', c) ↔
      ∃ f addr val, fuel = f + 1 ∧ a.eval w st = some addr ∧ e.eval w st = some val ∧
        o = .normal ∧ st' = { st with mem := Function.update st.mem addr val } ∧
        c = a.size + e.size + 1 := by
  cases fuel with
  | zero => simp [exec]
  | succ f =>
      simp only [exec]
      cases a.eval w st with
      | none => simp
      | some addr =>
          cases e.eval w st with
          | none => simp
          | some val => simp; aesop

theorem exec_ret_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {e : Expr} {st st' : State} {o : Outcome} {c : ℕ} :
    exec w p ω fuel (.ret e) st = some (o, st', c) ↔
      ∃ f v, fuel = f + 1 ∧ e.eval w st = some v ∧ o = .returned v ∧
        st' = st ∧ c = e.size + 1 := by
  cases fuel with
  | zero => simp [exec]
  | succ f =>
      simp only [exec]
      cases e.eval w st with
      | none => simp
      | some v => simp; aesop

theorem exec_seq_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {s t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.seq s t) st = some (o, st', c)) :
    ∃ f, fuel = f + 1 ∧
      ((∃ v c1, exec w p ω f s st = some (.returned v, st', c1) ∧ o = .returned v ∧ c = c1 + 1) ∨
       (∃ st1 c1 c2, exec w p ω f s st = some (.normal, st1, c1) ∧
         exec w p ω f t st1 = some (o, st', c2) ∧ c = c1 + c2 + 1)) := by
  cases fuel with
  | zero => simp [exec] at h
  | succ f =>
      simp only [exec] at h
      cases h1 : exec w p ω f s st with
      | none => simp [h1] at h
      | some res =>
          rcases res with ⟨o1, st1, c1⟩
          cases o1 with
          | returned v =>
              simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨ho, hst, hc⟩; subst ho hst hc
              exact ⟨f, rfl, Or.inl ⟨v, c1, h1, rfl, rfl⟩⟩
          | normal =>
              simp only [h1] at h
              cases h2 : exec w p ω f t st1 with
              | none => simp [h2] at h
              | some res2 =>
                  rcases res2 with ⟨o2, st2, c2⟩
                  simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨ho, hst, hc⟩; subst ho hst hc
                  exact ⟨f, rfl, Or.inr ⟨st1, c1, c2, h1, h2, rfl⟩⟩

/-- Returns `true` when a statement contains no `.ret` instructions (cannot return early). -/
def stmtNoRet : Stmt → Bool
  | .nop | .assign _ _ | .store _ _ | .rand _ | .call _ _ _ => true
  | .ret _ => false
  | .seq s t | .cond _ s t => stmtNoRet s && stmtNoRet t
  | .loop _ b => stmtNoRet b

theorem exec_noRet_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ fuel s st o st' c, stmtNoRet s = true → exec w p ω fuel s st = some (o, st', c) →
      o = .normal := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s st o st' c hnr hex
      cases fuel with
      | zero => simp [exec] at hex
      | succ f =>
          cases s with
          | nop => exact (exec_nop_iff.1 hex).2.1
          | assign _ _ => exact (exec_assign_iff.1 hex).choose_spec.choose_spec.2.2.1
          | store _ _ => exact (exec_store_iff.1 hex).choose_spec.choose_spec.choose_spec.2.2.2.1
          | rand _ => simp [exec] at hex; exact hex.1.symm
          | call r g args =>
              simp only [exec] at hex
              cases h1 : evalArgs w st args with
              | none => simp [h1] at hex
              | some vs =>
                  simp only [h1] at hex
                  cases h2 : p.procs[g]? with
                  | none => simp [h2] at hex
                  | some body =>
                      simp only [h2] at hex
                      cases h3 : exec w p ω f body { st with regs := fun i => vs[i]?.getD 0 } with
                      | none => simp [h3] at hex
                      | some res => rcases res with ⟨o1, st1, c1⟩; simp [h3] at hex; exact hex.1.symm
          | ret _ => simp [stmtNoRet] at hnr
          | seq s1 s2 =>
              simp only [stmtNoRet, Bool.and_eq_true] at hnr
              rcases exec_seq_elim hex with ⟨f', hf', hbr⟩
              cases hf'
              rcases hbr with ⟨v, c1, h1, _, _⟩ | ⟨st1, _, c2, h1, h2, _⟩
              · exact Outcome.noConfusion (ih f (by omega) s1 st _ st' c1 hnr.1 h1)
              · exact ih f (by omega) s2 st1 o st' c2 hnr.2 h2
          | cond e s1 s2 =>
              simp only [stmtNoRet, Bool.and_eq_true] at hnr
              simp only [exec] at hex
              cases he : e.eval w st with
              | none => simp [he] at hex
              | some v =>
                  simp only [he] at hex
                  cases h1 : exec w p ω f (if v = 0 then s2 else s1) st with
                  | none => simp [h1] at hex
                  | some res =>
                      rcases res with ⟨o1, st1, c1⟩
                      simp only [h1, Option.some.injEq, Prod.mk.injEq] at hex
                      rcases hex with ⟨rfl, _, _⟩
                      by_cases hv0 : v = 0
                      · simp only [hv0, ↓reduceIte] at h1
                        exact ih f (by omega) s2 st o1 st1 c1 hnr.2 h1
                      · simp only [hv0, ↓reduceIte] at h1
                        exact ih f (by omega) s1 st o1 st1 c1 hnr.1 h1
          | loop e b =>
              simp only [stmtNoRet] at hnr
              simp only [exec] at hex
              cases he : e.eval w st with
              | none => simp [he] at hex
              | some v =>
                  simp only [he] at hex
                  by_cases hv : v = 0
                  · simp [hv] at hex; exact hex.1.symm
                  · simp only [hv, ↓reduceIte] at hex
                    cases hb : exec w p ω f b st with
                    | none => simp [hb] at hex
                    | some res =>
                        rcases res with ⟨o1, st1, c1⟩
                        cases o1 with
                        | returned u =>
                            exact Outcome.noConfusion (ih f (by omega) b st _ st1 c1 hnr hb)
                        | normal =>
                            simp only [hb] at hex
                            cases hl : exec w p ω f (.loop e b) st1 with
                            | none => simp [hl] at hex
                            | some res2 =>
                                rcases res2 with ⟨o2, st2, c2⟩
                                simp only [hl, Option.some.injEq, Prod.mk.injEq] at hex
                                rcases hex with ⟨rfl, _, _⟩
                                exact ih f (by omega) (.loop e b) st1 o2 st2 c2 hnr hl

theorem exec_seq_of_noRet {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {s t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (hnr : stmtNoRet s = true)
    (h : exec w p ω fuel (.seq s t) st = some (o, st', c)) :
    ∃ f st1 c1 c2, fuel = f + 1 ∧ exec w p ω f s st = some (.normal, st1, c1) ∧
      exec w p ω f t st1 = some (o, st', c2) ∧ c = c1 + c2 + 1 := by
  rcases exec_seq_elim h with ⟨f, hf, hbr⟩
  rcases hbr with ⟨v, c1, h1, _, _⟩ | ⟨st1, c1, c2, h1, h2, hc⟩
  · exact Outcome.noConfusion (exec_noRet_normal f s st (.returned v) st' c1 hnr h1)
  · exact ⟨f, st1, c1, c2, hf, h1, h2, hc⟩

theorem exec_cond_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {e : Expr} {s t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.cond e s t) st = some (o, st', c)) :
    ∃ f v c1, fuel = f + 1 ∧ e.eval w st = some v ∧
      exec w p ω f (if v = 0 then t else s) st = some (o, st', c1) ∧ c = e.size + c1 + 1 := by
  cases fuel with
  | zero => simp [exec] at h
  | succ f =>
      simp only [exec] at h
      obtain ⟨v, hv⟩ : ∃ v, e.eval w st = some v := by
        cases h_ev : e.eval w st
        · simp [h_ev] at h
        · exact ⟨_, rfl⟩
      simp only [hv] at h
      cases h1 : exec w p ω f (if v = 0 then t else s) st with
      | none => simp [h1] at h
      | some res =>
          rcases res with ⟨o1, st1, c1⟩
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨ho, hst, hc⟩; subst ho hst
          exact ⟨f, v, c1, rfl, hv, h1, hc.symm⟩

theorem exec_call_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {r fIdx : ℕ} {args : List Expr} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.call r fIdx args) st = some (o, st', c)) :
    ∃ f vs body o1 st1 c1, fuel = f + 1 ∧ evalArgs w st args = some vs ∧
      p.procs[fIdx]? = some body ∧
      exec w p ω f body { st with regs := fun i => vs.getD i 0 } = some (o1, st1, c1) ∧
      o = .normal ∧
      st' = { st1 with regs := Function.update st.regs r (Outcome.rec 0 (fun u => u) o1) } ∧
      c = argsSize args + c1 + 1 := by
  cases fuel with
  | zero => simp [exec] at h
  | succ f =>
      simp only [exec] at h
      obtain ⟨vs, ha⟩ : ∃ vs, evalArgs w st args = some vs := by
        cases h_ea : evalArgs w st args
        · simp [h_ea] at h
        · exact ⟨_, rfl⟩
      obtain ⟨body, hp⟩ : ∃ body, p.procs[fIdx]? = some body := by
        cases h_pr : p.procs[fIdx]?
        · simp [ha, h_pr] at h
        · exact ⟨_, rfl⟩
      simp only [ha, hp, List.getD] at h
      cases hb : exec w p ω f body { st with regs := fun i => vs[i]?.getD 0 } with
      | none => simp [hb] at h
      | some res =>
          rcases res with ⟨o1, st1, c1⟩
          simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨ho, hst, hc⟩; subst ho hst
          exact ⟨f, vs, body, o1, st1, c1, rfl, ha, hp, hb, rfl, by cases o1 <;> rfl, hc.symm⟩

theorem exec_loop_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {e : Expr} {body : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.loop e body) st = some (o, st', c)) :
    ∃ f v, fuel = f + 1 ∧ e.eval w st = some v ∧
      ((v = 0 ∧ o = .normal ∧ st' = st ∧ c = e.size + 1) ∨
       (v ≠ 0 ∧ ∃ u c1, exec w p ω f body st = some (.returned u, st', c1) ∧
         o = .returned u ∧ c = e.size + c1 + 1) ∨
       (v ≠ 0 ∧ ∃ st1 c1 c2, exec w p ω f body st = some (.normal, st1, c1) ∧
         exec w p ω f (.loop e body) st1 = some (o, st', c2) ∧ c = e.size + c1 + c2 + 1)) := by
  cases fuel with
  | zero => simp [exec] at h
  | succ f =>
      simp only [exec] at h
      obtain ⟨v, hv⟩ : ∃ v, e.eval w st = some v := by
        cases h_ev : e.eval w st
        · simp [h_ev] at h
        · exact ⟨_, rfl⟩
      simp only [hv] at h
      by_cases hv0 : v = 0
      · simp only [hv0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨ho, hst, hc⟩; subst ho hst
        exact ⟨f, 0, rfl, by simpa [hv0] using hv, Or.inl ⟨rfl, rfl, rfl, hc.symm⟩⟩
      · simp only [hv0, ↓reduceIte] at h
        cases hb : exec w p ω f body st with
        | none => simp [hb] at h
        | some res =>
            rcases res with ⟨o1, st1, c1⟩
            cases o1 with
            | returned u =>
                simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨ho, hst, hc⟩; subst ho hst
                exact ⟨f, v, rfl, hv, Or.inr (Or.inl ⟨hv0, u, c1, hb, rfl, hc.symm⟩)⟩
            | normal =>
                simp only [hb] at h
                cases hl : exec w p ω f (.loop e body) st1 with
                | none => simp [hl] at h
                | some res2 =>
                    rcases res2 with ⟨o2, st2, c2⟩
                    simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨ho, hst, hc⟩; subst ho hst
                    exact ⟨f, v, rfl, hv, Or.inr (Or.inr ⟨hv0, st1, c1, c2, hb, hl, hc.symm⟩)⟩

theorem exec_seq_assign_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {r : ℕ} {e : Expr} {t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.seq (.assign r e) t) st = some (o, st', c)) :
    ∃ f v c2, fuel = f + 1 ∧ e.eval w st = some v ∧
      exec w p ω f t { st with regs := Function.update st.regs r v } = some (o, st', c2) ∧
      c = (e.size + 1) + c2 + 1 := by
  rcases exec_seq_of_noRet rfl h with ⟨f, st1, c1, c2, hf, h1, h2, hc⟩
  rcases exec_assign_iff.1 h1 with ⟨_, v, _, he, _, rfl, rfl⟩
  exact ⟨f, v, c2, hf, he, h2, hc⟩

theorem exec_seq_store_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {a e : Expr} {t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.seq (.store a e) t) st = some (o, st', c)) :
    ∃ f addr val c2, fuel = f + 1 ∧ a.eval w st = some addr ∧ e.eval w st = some val ∧
      exec w p ω f t { st with mem := Function.update st.mem addr val } = some (o, st', c2) ∧
      c = (a.size + e.size + 1) + c2 + 1 := by
  rcases exec_seq_of_noRet rfl h with ⟨f, st1, c1, c2, hf, h1, h2, hc⟩
  rcases exec_store_iff.1 h1 with ⟨_, addr, val, _, ha, he, _, rfl, rfl⟩
  exact ⟨f, addr, val, c2, hf, ha, he, h2, hc⟩

theorem exec_seq_call_elim {w : ℕ} {p : Program} {ω : ℕ → Bool} {fuel : ℕ}
    {r fIdx : ℕ} {args : List Expr} {t : Stmt} {st st' : State} {o : Outcome} {c : ℕ}
    (h : exec w p ω fuel (.seq (.call r fIdx args) t) st = some (o, st', c)) :
    ∃ f f' vs body o1 st1 c1 c2, fuel = f + 1 ∧ f = f' + 1 ∧
      evalArgs w st args = some vs ∧ p.procs[fIdx]? = some body ∧
      exec w p ω f' body { st with regs := fun i => vs.getD i 0 } = some (o1, st1, c1) ∧
      exec w p ω f t { st1 with regs := Function.update st.regs r (Outcome.rec 0 (fun v => v) o1) } =
        some (o, st', c2) ∧
      c = (argsSize args + c1 + 1) + c2 + 1 := by
  rcases exec_seq_of_noRet rfl h with ⟨f, stMid, c0, c2, hf, h1, h2, hc⟩
  rcases exec_call_elim h1 with ⟨f', vs, body, o1, st1, c1, hf', ha, hpb, hb, _, rfl, rfl⟩
  exact ⟨f, f', vs, body, o1, st1, c1, c2, hf, hf', ha, hpb, hb, h2, hc⟩

/-- Syntactic read-only check on statements whose callees satisfy `fs`. -/
def ReadOnlyStmt (fs : ℕ → Prop) : Stmt → Prop
  | .nop => True
  | .assign _ _ => True
  | .rand _ => True
  | .ret _ => True
  | .store _ _ => False
  | .seq s t => ReadOnlyStmt fs s ∧ ReadOnlyStmt fs t
  | .cond _ s t => ReadOnlyStmt fs s ∧ ReadOnlyStmt fs t
  | .loop _ b => ReadOnlyStmt fs b
  | .call _ f _ => fs f

theorem exec_readOnly_mem_eq {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fs : ℕ → Prop} (hfs : ∀ f, fs f → ∃ b, p.procs[f]? = some b ∧ ReadOnlyStmt fs b) :
    ∀ fuel s st o st' c, ReadOnlyStmt fs s → exec w p ω fuel s st = some (o, st', c) →
      st'.mem = st.mem := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro s st o st' c hs hex
      cases fuel with
      | zero => simp [exec] at hex
      | succ f =>
          cases s with
          | nop => rcases exec_nop_iff.1 hex with ⟨_, _, rfl, _⟩; rfl
          | assign r e => rcases exec_assign_iff.1 hex with ⟨_, _, _, _, _, rfl, _⟩; rfl
          | rand r => simp [exec] at hex; rcases hex with ⟨_, rfl, _⟩; rfl
          | ret e => rcases exec_ret_iff.1 hex with ⟨_, _, _, _, _, rfl, _⟩; rfl
          | store _ _ => exact False.elim hs
          | seq s1 s2 =>
              rcases exec_seq_elim hex with ⟨f', hf', hbr⟩
              cases hf'
              rcases hbr with ⟨v, c1, h1, _, _⟩ | ⟨st1, c1, c2, h1, h2, _⟩
              · exact ih f (by omega) s1 st _ st' c1 hs.1 h1
              · have hm1 := ih f (by omega) s1 st _ st1 c1 hs.1 h1
                have hm2 := ih f (by omega) s2 st1 o st' c2 hs.2 h2
                exact hm2.trans hm1
          | cond e s1 s2 =>
              rcases exec_cond_elim hex with ⟨f', v, c1, hf', _, h1, _⟩
              cases hf'
              by_cases hv : v = 0
              · simp only [hv, ↓reduceIte] at h1
                exact ih f (by omega) s2 st o st' c1 hs.2 h1
              · simp only [hv, ↓reduceIte] at h1
                exact ih f (by omega) s1 st o st' c1 hs.1 h1
          | loop e b =>
              rcases exec_loop_elim hex with ⟨f', v, hf', _, hbr⟩
              cases hf'
              rcases hbr with ⟨_, _, rfl, _⟩ | ⟨_, u, c1, hb, _, _⟩ | ⟨_, st1, c1, c2, hb, hl, _⟩
              · rfl
              · exact ih f (by omega) b st _ st' c1 hs hb
              · have hm1 := ih f (by omega) b st _ st1 c1 hs hb
                have hm2 := ih f (by omega) (.loop e b) st1 o st' c2 hs hl
                exact hm2.trans hm1
          | call r g args =>
              rcases exec_call_elim hex with ⟨f', vs, body, o1, st1, c1, hf', _, hpg, hb, _, rfl, _⟩
              cases hf'
              rcases hfs g hs with ⟨b', hpb, hrb⟩
              have heqb : body = b' := Option.some.inj (hpg.symm.trans hpb)
              subst heqb
              exact ih f (by omega) body { st with regs := fun i => vs.getD i 0 } o1 st1 c1 hrb hb

end ExecHelpers

section SplayProgramLookup

/-- Exact `procs` entries for `p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h)`. -/
theorem splayBodies_procs_eq {p : Program} {spBase h : ℕ}
    (hp : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h)) :
    let sp := SplayProcs.atBase spBase
    p.procs[sp.numZero]? = some zeroBody ∧
    p.procs[sp.numCopy]? = some copyBody ∧
    p.procs[sp.numAdd]? = some (addBody (sp.numAdd + 1)) ∧
    p.procs[sp.numAdd + 1]? = some (addCarryBody (sp.numAdd + 1) h) ∧
    p.procs[sp.numSub]? = some (subtractBody (sp.numSub + 1) (sp.numSub + 3)) ∧
    p.procs[sp.numSub + 1]? = some (negateBody (sp.numSub + 2)) ∧
    p.procs[sp.numSub + 2]? = some (negateCarryBody (sp.numSub + 2) h) ∧
    p.procs[sp.numSub + 3]? = some (addBody (sp.numSub + 4)) ∧
    p.procs[sp.numSub + 4]? = some (addCarryBody (sp.numSub + 4) h) ∧
    p.procs[sp.numLess]? = some (lessBody (sp.numLess + 1) (sp.numLess + 2)) ∧
    p.procs[sp.numLess + 1]? = some (isNegativeBody h) ∧
    p.procs[sp.numLess + 2]? = some (unsignedLessBody (sp.numLess + 2)) ∧
    p.procs[sp.numEqual]? = some (equalBody sp.numEqual) ∧
    p.procs[sp.revNode]? = some revNodeBody ∧
    p.procs[sp.applyTag]? = some (applyTagBody sp) ∧
    p.procs[sp.pushDown]? = some (pushDownBody sp) ∧
    p.procs[sp.pull]? = some (pullBody sp) ∧
    p.procs[sp.pushPath]? = some (pushPathBody sp) ∧
    p.procs[sp.rotate]? = some (rotateBody sp) ∧
    p.procs[sp.splay]? = some (splayBody sp) := by
  dsimp only [splayBodies] at hp
  have hr6 := hasAt_append_right hp
  have hl5 := hasAt_append_left hp
  have hp5 := hasAt_append_right hl5
  have hl4 := hasAt_append_left hl5
  have hp4 := hasAt_append_right hl4
  have hl3 := hasAt_append_left hl4
  have hp3 := hasAt_append_right hl3
  have hl2 := hasAt_append_left hl3
  have hp2 := hasAt_append_right hl2
  have hl1 := hasAt_append_left hl2
  have hp1 := hasAt_append_right hl1
  have hp0 := hasAt_append_left hl1
  have hzero_len : (zeroModule (SplayProcs.atBase spBase).numZero).length = 1 := by simp [zeroModule]
  have hcopy_len : (copyModule (SplayProcs.atBase spBase).numCopy).length = 1 := by simp [copyModule]
  have hadd_len : (addModule (SplayProcs.atBase spBase).numAdd h).length = 2 := by simp [addModule]
  have hsub_len : (subtractModule (SplayProcs.atBase spBase).numSub h).length = 5 := by
    simp [subtractModule, negateModule, addModule]
  have hless_len : (lessModule (SplayProcs.atBase spBase).numLess h).length = 3 := by simp [lessModule]
  have hequal_len : (equalModule (SplayProcs.atBase spBase).numEqual).length = 1 := by
    simp [equalModule]
  simp only [List.length_append, hzero_len, hcopy_len, hadd_len, hsub_len,
    hless_len, hequal_len] at hp1 hp2 hp3 hp4 hp5 hr6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [SplayProcs.atBase, zeroModule] using hp0 0 (by simp [zeroModule])
  · simpa [SplayProcs.atBase, copyModule] using hp1 0 (by simp [copyModule])
  · simpa [SplayProcs.atBase, addModule] using hp2 0 (by simp [addModule])
  · simpa [SplayProcs.atBase, addModule, Nat.add_assoc] using hp2 1 (by simp [addModule])
  · simpa [SplayProcs.atBase, subtractModule] using
      hp3 0 (by simp [subtractModule, negateModule, addModule])
  · simpa [SplayProcs.atBase, subtractModule, negateModule, Nat.add_assoc] using
      hp3 1 (by simp [subtractModule, negateModule, addModule])
  · simpa [SplayProcs.atBase, subtractModule, negateModule, Nat.add_assoc] using
      hp3 2 (by simp [subtractModule, negateModule, addModule])
  · simpa [SplayProcs.atBase, subtractModule, negateModule, addModule, Nat.add_assoc] using
      hp3 3 (by simp [subtractModule, negateModule, addModule])
  · simpa [SplayProcs.atBase, subtractModule, negateModule, addModule, Nat.add_assoc] using
      hp3 4 (by simp [subtractModule, negateModule, addModule])
  · simpa [SplayProcs.atBase, lessModule] using hp4 0 (by simp [lessModule])
  · simpa [SplayProcs.atBase, lessModule, Nat.add_assoc] using hp4 1 (by simp [lessModule])
  · simpa [SplayProcs.atBase, lessModule, Nat.add_assoc] using hp4 2 (by simp [lessModule])
  · simpa [SplayProcs.atBase, equalModule] using hp5 0 (by simp [equalModule])
  · simpa [SplayProcs.atBase] using hr6 0 (by simp)
  · simpa [SplayProcs.atBase] using hr6 1 (by simp)
  · simpa [SplayProcs.atBase] using hr6 2 (by simp)
  · simpa [SplayProcs.atBase] using hr6 3 (by simp)
  · simpa [SplayProcs.atBase] using hr6 4 (by simp)
  · simpa [SplayProcs.atBase] using hr6 5 (by simp)
  · simpa [SplayProcs.atBase] using hr6 6 (by simp)

theorem numReadOnly_mem_eq {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h)) :
    let sp := SplayProcs.atBase spBase
    (∀ fuel st o st' c, exec w p ω fuel (lessBody (sp.numLess + 1) (sp.numLess + 2)) st =
      some (o, st', c) → st'.mem = st.mem) ∧
    (∀ fuel st o st' c, exec w p ω fuel (equalBody sp.numEqual) st =
      some (o, st', c) → st'.mem = st.mem) ∧
    (∀ fuel st o st' c, exec w p ω fuel zeroBody st =
      some (o, st', c) → st'.mem = st.mem) := by
  rcases splayBodies_procs_eq hp with ⟨hz, _, _, _, _, _, _, _, _, hless, hneg, huless, heq, _⟩
  let sp := SplayProcs.atBase spBase
  let fs : ℕ → Prop := fun f =>
    f = sp.numZero ∨ f = sp.numLess ∨ f = sp.numLess + 1 ∨
    f = sp.numLess + 2 ∨ f = sp.numEqual
  have hfs : ∀ f, fs f → ∃ b, p.procs[f]? = some b ∧ ReadOnlyStmt fs b := by
    intro f hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact ⟨zeroBody, hz, trivial⟩
    · refine ⟨lessBody (sp.numLess + 1) (sp.numLess + 2), hless, ?_⟩
      simp [lessBody, ReadOnlyStmt, fs]
    · refine ⟨isNegativeBody h, hneg, ?_⟩
      simp [isNegativeBody, ReadOnlyStmt]
    · refine ⟨unsignedLessBody (sp.numLess + 2), huless, ?_⟩
      simp [unsignedLessBody, ReadOnlyStmt, fs]
    · refine ⟨equalBody sp.numEqual, heq, ?_⟩
      simp [equalBody, ReadOnlyStmt, fs]
  refine ⟨?_, ?_, ?_⟩
  · intro fuel st o st' c hex
    exact exec_readOnly_mem_eq hfs fuel _ st o st' c
      (by simp only [lessBody, ReadOnlyStmt, fs, sp, SplayProcs.atBase]; simp) hex
  · intro fuel st o st' c hex
    exact exec_readOnly_mem_eq hfs fuel _ st o st' c
      (by simp only [equalBody, ReadOnlyStmt, fs, sp, SplayProcs.atBase]; simp) hex
  · intro fuel st o st' c hex
    exact exec_readOnly_mem_eq hfs fuel zeroBody st o st' c trivial hex

end SplayProgramLookup

section NumAllocSafe

theorem addCarry_exec_safe {w h b : ℕ} {p : Program} {ω : ℕ → Bool}
    (hb : p.procs[b]? = some (addCarryBody b h)) :
    ∀ fuel st o st' c,
      exec w p ω fuel (addCarryBody b h) st = some (o, st', c) →
      let len := st.regs 2
      let hp := st.regs 4
      o = .returned (hp + len) ∧
      (∀ a, a < hp ∨ hp + len ≤ a → st'.mem a = st.mem a) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro st o st' c hex
      dsimp only
      rcases exec_cond_elim hex with ⟨f, v, c1, rfl, he_cond, hcond_ex, _⟩
      rcases eval_bin_some he_cond with ⟨x2, x0, hx2, hx0, _, rfl⟩
      simp only [Expr.eval] at hx2; cases hx2
      rcases eval_const_some hx0 with ⟨rfl, _⟩
      by_cases hL0 : st.regs 2 = 0
      · have hv1 : BinOp.eq.eval (st.regs 2) 0 ≠ 0 := by simp [BinOp.eval, hL0]
        simp only [hv1, ↓reduceIte] at hcond_ex
        rcases exec_ret_iff.1 hcond_ex with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
        simp only [Expr.eval] at he_ret; cases he_ret
        exact ⟨by simp [hL0], fun _ _ => rfl⟩
      · have hv0 : BinOp.eq.eval (st.regs 2) 0 = 0 := by simp [BinOp.eval, hL0]
        simp only [hv0, ↓reduceIte] at hcond_ex
        rcases exec_seq_assign_elim hcond_ex with ⟨f1, v5, c2, hf1, _, h2, _⟩
        rcases exec_seq_store_elim h2 with ⟨f2, addr, val, c3, hf2, ha_ev, _, h3, _⟩
        simp only [Expr.eval, Function.update_of_ne (by decide : (4 : ℕ) ≠ 5)] at ha_ev
        cases ha_ev
        rcases exec_seq_call_elim h3 with ⟨f3, f3', vs, body, o_rec, st_rec, c_rec, c4, hf3, hf3', hvs, hpb, hrec, h4, _⟩
        have hbody : body = addCarryBody b h := Option.some.inj (hpb.symm.trans hb)
        subst hbody
        rcases exec_ret_iff.1 h4 with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
        simp only [Expr.eval, Function.update_self] at he_ret; cases he_ret
        rcases evalArgs_cons.1 hvs with ⟨_, vs1, _, hvs1, rfl⟩
        rcases evalArgs_cons.1 hvs1 with ⟨_, vs2, _, hvs2, rfl⟩
        rcases evalArgs_cons.1 hvs2 with ⟨v2, vs3, hv2, hvs3, rfl⟩
        rcases evalArgs_cons.1 hvs3 with ⟨_, vs4, _, hvs4, rfl⟩
        rcases evalArgs_cons.1 hvs4 with ⟨v4, vs5, hv4, hvs5, rfl⟩
        rw [evalArgs_nil.1 hvs5] at *
        have hv2_eq : v2 = st.regs 2 - 1 := by
          simpa [Function.update_of_ne (by decide : (2 : ℕ) ≠ 5)] using eval_sub_reg_const hv2
        rcases eval_bin_some hv4 with ⟨x4, x1, hx4, hx1, _, rfl⟩
        simp only [Expr.eval, Function.update_of_ne (by decide : (4 : ℕ) ≠ 5)] at hx4
        cases hx4
        rcases eval_const_some hx1 with ⟨rfl, _⟩
        have hrec_ih := ih f3' (by omega) _ _ _ _ hrec
        simp [List.getD, hv2_eq] at hrec_ih
        rcases hrec_ih with ⟨ho_eq, hmem_rec⟩
        cases o_rec with
        | normal => cases ho_eq
        | returned u_rec =>
            cases ho_eq
            have hadd_eq : st.regs 4 + 1 + (st.regs 2 - 1) = st.regs 4 + st.regs 2 := by omega
            refine ⟨by simp [hadd_eq], fun a ha => ?_⟩
            have ha_rec : a ≤ st.regs 4 ∨ st.regs 4 + 1 + (st.regs 2 - 1) ≤ a := by omega
            rw [hmem_rec a ha_rec]
            simp [Function.update_of_ne (show a ≠ st.regs 4 by omega)]

theorem add_exec_safe {w h b : ℕ} {p : Program} {ω : ℕ → Bool}
    (hk : p.procs[b + 1]? = some (addCarryBody (b + 1) h)) :
    ∀ fuel st o st' c,
      exec w p ω fuel (addBody (b + 1)) st = some (o, st', c) →
      let len := st.regs 2
      let hp := st.regs 3
      o = .returned (hp + len) ∧
      (∀ a, a < hp ∨ hp + len ≤ a → st'.mem a = st.mem a) := by
  intro fuel st o st' c hex
  dsimp only [addBody] at hex
  rcases exec_seq_call_elim hex with ⟨f, f', vs, body, o1, st1, c1, c2, _, _, hvs, hpb, hrec, hret, _⟩
  have hbody : body = addCarryBody (b + 1) h := Option.some.inj (hpb.symm.trans hk)
  subst hbody
  rcases evalArgs_cons.1 hvs with ⟨_, vs1, _, hvs1, rfl⟩
  rcases evalArgs_cons.1 hvs1 with ⟨_, vs2, _, hvs2, rfl⟩
  rcases evalArgs_cons.1 hvs2 with ⟨v2, vs3, hv2, hvs3, rfl⟩
  rcases evalArgs_cons.1 hvs3 with ⟨_, vs4, _, hvs4, rfl⟩
  rcases evalArgs_cons.1 hvs4 with ⟨v3, vs5, hv3, hvs5, rfl⟩
  rw [evalArgs_nil.1 hvs5] at *
  simp only [Expr.eval] at hv2 hv3; cases hv2; cases hv3
  rcases addCarry_exec_safe hk f' _ _ _ _ hrec with ⟨ho_eq, hmem⟩
  simp [List.getD] at ho_eq hmem
  cases o1 with
  | normal => cases ho_eq
  | returned u =>
      cases ho_eq
      rcases exec_ret_iff.1 hret with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
      simp only [Expr.eval, Function.update_self] at he_ret; cases he_ret
      exact ⟨rfl, hmem⟩

theorem negateCarry_exec_safe {w h b : ℕ} {p : Program} {ω : ℕ → Bool}
    (hb : p.procs[b]? = some (negateCarryBody b h)) :
    ∀ fuel st o st' c,
      exec w p ω fuel (negateCarryBody b h) st = some (o, st', c) →
      let len := st.regs 1
      let hp := st.regs 3
      o = .returned (hp + len) ∧
      (∀ a, a < hp ∨ hp + len ≤ a → st'.mem a = st.mem a) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro st o st' c hex
      dsimp only
      rcases exec_cond_elim hex with ⟨f, v, c1, rfl, he_cond, hcond_ex, _⟩
      rcases eval_bin_some he_cond with ⟨x1, x0, hx1, hx0, _, rfl⟩
      simp only [Expr.eval] at hx1; cases hx1
      rcases eval_const_some hx0 with ⟨rfl, _⟩
      by_cases hL0 : st.regs 1 = 0
      · have hv1 : BinOp.eq.eval (st.regs 1) 0 ≠ 0 := by simp [BinOp.eval, hL0]
        simp only [hv1, ↓reduceIte] at hcond_ex
        rcases exec_ret_iff.1 hcond_ex with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
        simp only [Expr.eval] at he_ret; cases he_ret
        exact ⟨by simp [hL0], fun _ _ => rfl⟩
      · have hv0 : BinOp.eq.eval (st.regs 1) 0 = 0 := by simp [BinOp.eval, hL0]
        simp only [hv0, ↓reduceIte] at hcond_ex
        rcases exec_seq_assign_elim hcond_ex with ⟨f1, v4, c2, hf1, _, h2, _⟩
        rcases exec_seq_store_elim h2 with ⟨f2, addr, val, c3, hf2, ha_ev, _, h3, _⟩
        simp only [Expr.eval, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)] at ha_ev
        cases ha_ev
        rcases exec_seq_call_elim h3 with ⟨f3, f3', vs, body, o_rec, st_rec, c_rec, c4, hf3, hf3', hvs, hpb, hrec, h4, _⟩
        have hbody : body = negateCarryBody b h := Option.some.inj (hpb.symm.trans hb)
        subst hbody
        rcases exec_ret_iff.1 h4 with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
        simp only [Expr.eval, Function.update_self] at he_ret; cases he_ret
        rcases evalArgs_cons.1 hvs with ⟨_, vs1, _, hvs1, rfl⟩
        rcases evalArgs_cons.1 hvs1 with ⟨v1, vs2, hv1, hvs2, rfl⟩
        rcases evalArgs_cons.1 hvs2 with ⟨_, vs3, _, hvs3, rfl⟩
        rcases evalArgs_cons.1 hvs3 with ⟨v3, vs4, hv3, hvs4, rfl⟩
        rw [evalArgs_nil.1 hvs4] at *
        have hv1_eq : v1 = st.regs 1 - 1 := by
          simpa [Function.update_of_ne (by decide : (1 : ℕ) ≠ 4)] using eval_sub_reg_const hv1
        rcases eval_bin_some hv3 with ⟨x3, xone, hx3, hxone, _, rfl⟩
        simp only [Expr.eval, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)] at hx3
        cases hx3
        rcases eval_const_some hxone with ⟨rfl, _⟩
        have hrec_ih := ih f3' (by omega) _ _ _ _ hrec
        simp [List.getD, hv1_eq] at hrec_ih
        rcases hrec_ih with ⟨ho_eq, hmem_rec⟩
        cases o_rec with
        | normal => cases ho_eq
        | returned u_rec =>
            cases ho_eq
            have hadd_eq : st.regs 3 + 1 + (st.regs 1 - 1) = st.regs 3 + st.regs 1 := by omega
            refine ⟨by simp [hadd_eq], fun a ha => ?_⟩
            have ha_rec : a ≤ st.regs 3 ∨ st.regs 3 + 1 + (st.regs 1 - 1) ≤ a := by omega
            rw [hmem_rec a ha_rec]
            simp [Function.update_of_ne (show a ≠ st.regs 3 by omega)]

theorem negate_exec_safe {w h b : ℕ} {p : Program} {ω : ℕ → Bool}
    (hk : p.procs[b + 1]? = some (negateCarryBody (b + 1) h)) :
    ∀ fuel st o st' c,
      exec w p ω fuel (negateBody (b + 1)) st = some (o, st', c) →
      let len := st.regs 1
      let hp := st.regs 2
      o = .returned (hp + len) ∧
      (∀ a, a < hp ∨ hp + len ≤ a → st'.mem a = st.mem a) := by
  intro fuel st o st' c hex
  dsimp only [negateBody] at hex
  rcases exec_seq_call_elim hex with ⟨f, f', vs, body, o1, st1, c1, c2, _, _, hvs, hpb, hrec, hret, _⟩
  have hbody : body = negateCarryBody (b + 1) h := Option.some.inj (hpb.symm.trans hk)
  subst hbody
  rcases evalArgs_cons.1 hvs with ⟨_, vs1, _, hvs1, rfl⟩
  rcases evalArgs_cons.1 hvs1 with ⟨v1, vs2, hv1, hvs2, rfl⟩
  rcases evalArgs_cons.1 hvs2 with ⟨_, vs3, _, hvs3, rfl⟩
  rcases evalArgs_cons.1 hvs3 with ⟨v2, vs4, hv2, hvs4, rfl⟩
  rw [evalArgs_nil.1 hvs4] at *
  simp only [Expr.eval] at hv1 hv2; cases hv1; cases hv2
  rcases negateCarry_exec_safe hk f' _ _ _ _ hrec with ⟨ho_eq, hmem⟩
  simp [List.getD] at ho_eq hmem
  cases o1 with
  | normal => cases ho_eq
  | returned u =>
      cases ho_eq
      rcases exec_ret_iff.1 hret with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
      simp only [Expr.eval, Function.update_self] at he_ret; cases he_ret
      exact ⟨rfl, hmem⟩

theorem subtract_exec_safe {w h spBase : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : p.HasAt spBase (splayBodies (SplayProcs.atBase spBase) h)) :
    let sp := SplayProcs.atBase spBase
    ∀ fuel st o st' c,
      exec w p ω fuel (subtractBody (sp.numSub + 1) (sp.numSub + 3)) st = some (o, st', c) →
      let len := st.regs 2
      let hp0 := st.regs 3
      o = .returned (hp0 + 2 * len) ∧
      (∀ a, a < hp0 ∨ hp0 + 2 * len ≤ a → st'.mem a = st.mem a) := by
  rcases splayBodies_procs_eq hp with ⟨_, _, _, _, _, hneg, hnegc, hadd, haddc, _⟩
  intro sp fuel st o st' c hex
  dsimp only [subtractBody] at hex
  rcases exec_seq_call_elim hex with ⟨f1, f1', vs1, body1, o1, st1, c1, c2, _, _, hvs1, hpb1, hrec1, h2, _⟩
  have hb1 : body1 = negateBody (sp.numSub + 2) := Option.some.inj (hpb1.symm.trans hneg)
  subst hb1
  rcases evalArgs_cons.1 hvs1 with ⟨_, a1, _, ha1, rfl⟩
  rcases evalArgs_cons.1 ha1 with ⟨v2, a2, hv2, ha2, rfl⟩
  rcases evalArgs_cons.1 ha2 with ⟨v3, a3, hv3, ha3, rfl⟩
  rw [evalArgs_nil.1 ha3] at *
  simp only [Expr.eval] at hv2 hv3; cases hv2; cases hv3
  rcases negate_exec_safe hnegc f1' _ _ _ _ hrec1 with ⟨ho1, hmem1⟩
  simp [List.getD] at ho1 hmem1
  cases o1 with
  | normal => cases ho1
  | returned u1 =>
      cases ho1
      rcases exec_seq_call_elim h2 with ⟨f2, f2', vs2, body2, o2, st2, c3, c4, _, _, hvs2, hpb2, hrec2, hret, _⟩
      have hb2 : body2 = addBody (sp.numSub + 4) := Option.some.inj (hpb2.symm.trans hadd)
      subst hb2
      rcases evalArgs_cons.1 hvs2 with ⟨_, b1, _, hb1, rfl⟩
      rcases evalArgs_cons.1 hb1 with ⟨_, b2, _, hb2, rfl⟩
      rcases evalArgs_cons.1 hb2 with ⟨w2, b3, hw2, hb3, rfl⟩
      rcases evalArgs_cons.1 hb3 with ⟨w4, b4, hw4, hb4, rfl⟩
      rw [evalArgs_nil.1 hb4] at *
      simp only [Expr.eval, Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
        Function.update_self] at hw2 hw4
      cases hw2; cases hw4
      rcases add_exec_safe haddc f2' _ _ _ _ hrec2 with ⟨ho2, hmem2⟩
      simp [List.getD] at ho2 hmem2
      cases o2 with
      | normal => cases ho2
      | returned u2 =>
          cases ho2
          rcases exec_ret_iff.1 hret with ⟨_, vret, _, he_ret, rfl, rfl, _⟩
          simp only [Expr.eval, Function.update_self] at he_ret; cases he_ret
          have h2eq : st.regs 3 + st.regs 2 + st.regs 2 = st.regs 3 + 2 * st.regs 2 := by omega
          refine ⟨by simp [h2eq], fun a ha => ?_⟩
          rw [hmem2 a (by omega), hmem1 a (by omega)]

end NumAllocSafe

end MinCostFlow.LinkCut.Prog
