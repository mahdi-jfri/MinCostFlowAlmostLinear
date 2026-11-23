module

public import WordRAM.Contract

/-!
# Widening a deterministic guest execution

Word size only bounds successful arithmetic in a deterministic run.
A larger guest word therefore preserves the decoded tree and cost of
the canonical Theorem 2.2 execution (page 7).
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

private theorem eval_widen {w W : ℕ} (hw : w ≤ W) (st : State) (e : Expr) (v : ℕ)
    (he : e.eval w st = some v) : e.eval W st = some v := by
  have hpow : 2^w ≤ (2:ℕ)^W := Nat.pow_le_pow_right (by decide) hw
  induction e generalizing v with
  | reg r => exact he
  | const x =>
    have hx : x < 2^w := by
      by_contra! h
      simp [Expr.eval,not_lt.mpr h] at he
    simpa [Expr.eval,hx,hx.trans_le hpow] using he
  | load a ih =>
    cases h : a.eval w st with
    | none => simp [Expr.eval,h] at he
    | some x => simpa [Expr.eval,h,ih _ h] using he
  | bin op a b ia ib =>
    cases ha : a.eval w st <;> cases hb : b.eval w st <;>
      simp [Expr.eval,ha,hb] at he
    rename_i x y
    have hh : op.eval x y < 2^w := by
      by_contra! h
      simp [not_lt.mpr h] at he
    simpa [Expr.eval,ia _ ha,ib _ hb,hh,hh.trans_le hpow] using he

private theorem evalArgs_widen {w W : ℕ} (hw : w ≤ W) (st : State)
    (args : List Expr) (vs : List ℕ) (he : evalArgs w st args = some vs) :
    evalArgs W st args = some vs := by
  induction args generalizing vs with
  | nil => exact he
  | cons e es ih =>
    cases h : e.eval w st <;> cases hs : evalArgs w st es <;>
      simp [evalArgs,h,hs] at he
    rename_i v values
    simpa [evalArgs,eval_widen hw st e v h,ih values hs] using he

private theorem exec_widen {w W : ℕ} (hw : w ≤ W) {p : Program}
    (hp : p.IsDeterministic) (ω : ℕ → Bool) :
    ∀ fuel s st o out cost, s.NoRand →
      exec w p ω fuel s st = some (o,out,cost) →
      exec W p ω fuel s st = some (o,out,cost) := by
  intro fuel
  induction fuel with
  | zero => intro s st o out cost _ h; cases h
  | succ f ih =>
    intro s st o out cost hs hr
    cases s with
    | nop => exact hr
    | rand r => exact hs.elim
    | assign r e =>
      cases h : e.eval w st with
      | none => simp [exec,h] at hr
      | some v => simpa [exec,eval_widen hw st e v h] using (by simpa [exec,h] using hr)
    | ret e =>
      cases h : e.eval w st with
      | none => simp [exec,h] at hr
      | some v => simpa [exec,eval_widen hw st e v h] using (by simpa [exec,h] using hr)
    | store a e =>
      cases ha : a.eval w st <;> cases he : e.eval w st <;>
        simp [exec,ha,he] at hr
      rename_i x v
      simpa [exec,eval_widen hw st a x ha,eval_widen hw st e v he] using hr
    | seq s t =>
      cases h : exec w p ω f s st with
      | none => simp [exec,h] at hr
      | some result =>
        obtain ⟨outcome,mid,c⟩ := result
        have h' := ih s st outcome mid c hs.1 h
        cases outcome with
        | returned v => simpa [exec,h'] using (by simpa [exec,h] using hr)
        | normal =>
          cases ht : exec w p ω f t mid with
          | none => simp [exec,h,ht] at hr
          | some result =>
            obtain ⟨o',out',c'⟩ := result
            simpa [exec,h',ih t mid o' out' c' hs.2 ht] using (by simpa [exec,h,ht] using hr)
    | cond e s t =>
      cases he : e.eval w st with
      | none => simp [exec,he] at hr
      | some v =>
        have hsw : (if v = 0 then t else s).NoRand := by split <;> first | exact hs.2 | exact hs.1
        cases h : exec w p ω f (if v = 0 then t else s) st with
        | none => simp [exec,he,h] at hr
        | some result =>
          obtain ⟨o',out',c'⟩ := result
          simpa [exec,eval_widen hw st e v he,ih _ _ _ _ _ hsw h] using
            (by simpa [exec,he,h] using hr)
    | loop e body =>
      cases he : e.eval w st with
      | none => simp [exec,he] at hr
      | some v =>
        have he' := eval_widen hw st e v he
        by_cases hv : v = 0
        · simpa [exec,he',hv] using (by simpa [exec,he,hv] using hr)
        cases h : exec w p ω f body st with
        | none => simp [exec,he,hv,h] at hr
        | some result =>
          obtain ⟨outcome,mid,c⟩ := result
          have h' := ih body st outcome mid c hs h
          cases outcome with
          | returned u => simpa [exec,he',hv,h'] using (by simpa [exec,he,hv,h] using hr)
          | normal =>
            cases ht : exec w p ω f (.loop e body) mid with
            | none => simp [exec,he,hv,h,ht] at hr
            | some result =>
              obtain ⟨o',out',c'⟩ := result
              simpa [exec,he',hv,h',ih _ _ o' out' c' hs ht] using
                (by simpa [exec,he,hv,h,ht] using hr)
    | call r g args =>
      cases ha : evalArgs w st args <;> cases hg : p.procs[g]? <;>
        simp only [exec,ha,hg] at hr <;> try contradiction
      rename_i vs body
      let start := startState vs st.mem st.pos
      have hbody := hp body (List.mem_of_getElem? hg)
      cases h : exec w p ω f body start with
      | none =>
        dsimp [start,startState] at h
        simp only [h] at hr
        contradiction
      | some result =>
        obtain ⟨o',out',c'⟩ := result
        have h' := ih body start o' out' c' hbody h
        dsimp [start,startState] at h h'
        simp only [h] at hr
        simpa only [exec,evalArgs_widen hw st args vs ha,hg,h'] using hr

/-- A successful deterministic run is preserved when the word size is widened. -/
theorem deterministicRuns_widen {w W : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st out : State} {o : Outcome} {cost : ℕ}
    (hw : w ≤ W) (hp : p.IsDeterministic) (hs : s.NoRand)
    (h : Runs w p ω s st o out cost) : Runs W p ω s st o out cost := by
  obtain ⟨f,hf⟩ := h
  exact ⟨f,exec_widen hw hp ω f s st o out cost hs hf⟩

end MinCostFlow.LastLevelProgram
