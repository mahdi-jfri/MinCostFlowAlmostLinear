module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExplicitExpander.Graph

/-!
# The program that writes the explicit expander: the edge loops

The program of `Program.lean` writes `(explicitGraph n).encode`, which is `n`, the number of
edges, and then the two ends of each edge. It works with these registers:
`1` holds `n`, `2` holds `m = ⌊√n⌋`, `3` holds `N = m²`, `4` holds the address of the next free
cell, `5` is the loop counter, `6` and `7` hold the point `(z / m, z % m)`, and `8` holds a
neighbour.

This file defines the statements and proves the two loops that write the edges, from address `2`
on. The invariant `EdgeState n m L` says that the edges `L` are written there and that register
`4` points just after them.

* `coreLoop_triple`: for `z < N`, the loop computes the four neighbours `tgt m z i` and writes
  each edge `(z, tgt m z i)` that is not a loop (`emit_triple`). This writes `coreEdges m`.
* `pendLoop_triple`: for `N ≤ j' < n`, the loop writes the edge `(j', (j' - N) % N)`. This
  writes `pendEdges N (n - N)`.

Every number the loops compute is below `16n + 48`, which fits in a word.
-/

public section

namespace MinCostFlow.ExplicitExpander

open WordRAM

/-- The ends of the edges `L`, in order. -/
@[expose] def flatE (L : List (ℕ × ℕ)) : List ℕ := L.flatMap fun e => [e.1, e.2]

lemma flatE_length (L : List (ℕ × ℕ)) : (flatE L).length = 2 * L.length := by
  induction L with
  | nil => simp [flatE]
  | cons e L ih =>
    simp only [flatE, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

lemma flatE_append (L L' : List (ℕ × ℕ)) : flatE (L ++ L') = flatE L ++ flatE L' := by
  simp [flatE]

/-- Write `e` to register `8`, and the edge `(reg 5, reg 8)` at register `4` unless it is a
loop. -/
@[expose] def emitStmt (e : Expr) : Stmt :=
  .seq (.assign 8 e)
    (.cond (.bin .eq (.reg 8) (.reg 5)) .nop
      (.seq (.store (.reg 4) (.reg 5))
        (.seq (.store (.bin .add (.reg 4) (.const 1)) (.reg 8))
          (.assign 4 (.bin .add (.reg 4) (.const 2))))))

/-- `((x + 2y) % m) * m + y`, with `x, y, m` in registers `6, 7, 2`. -/
@[expose] def tExpr0 : Expr :=
  .bin .add (.bin .mul (.bin .mod (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.reg 2))
    (.reg 2)) (.reg 7)

/-- `((x + 2y + 1) % m) * m + y`. -/
@[expose] def tExpr1 : Expr :=
  .bin .add (.bin .mul (.bin .mod (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7)))
    (.const 1)) (.reg 2)) (.reg 2)) (.reg 7)

/-- `x * m + (y + 2x) % m`. -/
@[expose] def tExpr2 : Expr :=
  .bin .add (.bin .mul (.reg 6) (.reg 2)) (.bin .mod (.bin .add (.reg 7) (.bin .mul (.const 2)
    (.reg 6))) (.reg 2))

/-- `x * m + (y + 2x + 1) % m`. -/
@[expose] def tExpr3 : Expr :=
  .bin .add (.bin .mul (.reg 6) (.reg 2)) (.bin .mod (.bin .add (.bin .add (.reg 7)
    (.bin .mul (.const 2) (.reg 6))) (.const 1)) (.reg 2))

/-- The body of the loop over the vertices `z < N` of the Margulis part. -/
@[expose] def coreBody : Stmt :=
  .seq (.assign 6 (.bin .div (.reg 5) (.reg 2)))
    (.seq (.assign 7 (.bin .mod (.reg 5) (.reg 2)))
      (.seq (emitStmt tExpr0) (.seq (emitStmt tExpr1) (.seq (emitStmt tExpr2)
        (emitStmt tExpr3)))))

/-- The body of the loop over the other vertices `N ≤ j' < n`: write `(j', (j' - N) % N)`. -/
@[expose] def pendBody : Stmt :=
  .seq (.store (.reg 4) (.reg 5))
    (.seq (.store (.bin .add (.reg 4) (.const 1))
        (.bin .mod (.bin .sub (.reg 5) (.reg 3)) (.reg 3)))
      (.assign 4 (.bin .add (.reg 4) (.const 2))))

/-- The edges of the first `z` vertices of the Margulis part. -/
@[expose] def coreUpTo (m z : ℕ) : List (ℕ × ℕ) := (List.range z).flatMap (vertexEdges m)

/-- Registers `1` to `4` hold `n`, `m`, `m²` and `2 + 2|L|`, and the ends of the edges `L` are
written from address `2` on. -/
@[expose] def EdgeState (n m : ℕ) (L : List (ℕ × ℕ)) (st : State) : Prop :=
  st.regs 1 = n ∧ st.regs 2 = m ∧ st.regs 3 = m * m ∧ st.regs 4 = 2 + 2 * L.length ∧
    ListAt st.mem 2 (flatE L)

lemma EdgeState.update {n m : ℕ} {L : List (ℕ × ℕ)} {st : State} (h : EdgeState n m L st)
    {r : ℕ} (hr : 5 ≤ r) (v : ℕ) :
    EdgeState n m L { st with regs := Function.update st.regs r v } := by
  obtain ⟨h1, h2, h3, h4, hm⟩ := h
  refine ⟨?_, ?_, ?_, ?_, hm⟩ <;> dsimp only <;>
    rw [Function.update_of_ne (by omega)] <;> assumption

lemma length_vertexEdges (m z : ℕ) : (vertexEdges m z).length ≤ 4 := by
  have h : ∀ t, (emitE z t).length ≤ 1 := fun t => by unfold emitE; split_ifs <;> simp
  simp only [vertexEdges, List.length_append]
  have := h (tgt m z 0); have := h (tgt m z 1); have := h (tgt m z 2); have := h (tgt m z 3)
  omega

lemma length_coreUpTo (m z : ℕ) : (coreUpTo m z).length ≤ 4 * z := by
  induction z with
  | zero => simp [coreUpTo]
  | succ z ih =>
    simp only [coreUpTo, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.length_append] at ih ⊢
    have := length_vertexEdges m z
    omega

lemma coreUpTo_succ (m z : ℕ) : coreUpTo m (z + 1) = coreUpTo m z ++ vertexEdges m z := by
  simp [coreUpTo, List.range_succ, List.flatMap_append]

variable {w : ℕ}

/-- One call of `emitStmt`: the edge `(z, t)` is appended unless `t = z`. -/
theorem emit_triple (p : Program) (e : Expr) {n m z x y t : ℕ} {L : List (ℕ × ℕ)}
    (hw : 1 < 2 ^ w) (hptr : 2 + 2 * L.length + 2 < 2 ^ w)
    (he : ∀ st : State, EdgeState n m L st → st.regs 5 = z → st.regs 6 = x → st.regs 7 = y →
      e.eval w st = some t) :
    Triple w p (fun st => EdgeState n m L st ∧ st.regs 5 = z ∧ st.regs 6 = x ∧ st.regs 7 = y)
      (emitStmt e)
      (normalPost fun st => EdgeState n m (L ++ emitE z t) st ∧ st.regs 5 = z ∧
        st.regs 6 = x ∧ st.regs 7 = y)
      (fun _ => e.size + 25) := by
  intro st ω ⟨hE, h5, h6, h7⟩
  have hev := he st hE h5 h6 h7
  obtain ⟨h1, h2, h3, h4, hm⟩ := hE
  refine runs_start_le (runs_seq_assign_le hev ?_)
  have h8 : (Function.update st.regs 8 t) 8 = t := Function.update_self ..
  have h5' : (Function.update st.regs 8 t) 5 = z := by
    rw [Function.update_of_ne (by decide)]; exact h5
  have h4' : (Function.update st.regs 8 t) 4 = 2 + 2 * L.length := by
    rw [Function.update_of_ne (by decide)]; exact h4
  by_cases htz : t = z
  · refine runs_cond_le (v := 1)
      (Expr.eval_eq_true (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h5') htz hw)
      (fun _ => ?_) (fun h => absurd h one_ne_zero)
    refine runs_nop_le ?_ ?_
    · have hE : EdgeState n m L st := ⟨h1, h2, h3, h4, hm⟩
      simp only [normalPost, emitE, htz, ↓reduceIte, List.append_nil]
      refine ⟨hE.update (r := 8) (by decide) t, h5', ?_, ?_⟩
      · rw [Function.update_of_ne (by decide)]; exact h6
      · rw [Function.update_of_ne (by decide)]; exact h7
    · simp only [Expr.size]; omega
  · refine runs_cond_le (v := 0)
      (Expr.eval_eq_false (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h5') htz hw)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlen := flatE_length L
    refine runs_seq_store_le (x := 2 + 2 * L.length) (v := z) (Expr.eval_reg_of_eq h4')
      (Expr.eval_reg_of_eq h5') ?_
    refine runs_seq_store_le (x := 2 + 2 * L.length + 1) (v := t)
      (Expr.eval_add (Expr.eval_reg_of_eq h4') (Expr.eval_const hw) (by omega))
      (Expr.eval_reg_of_eq h8) ?_
    refine runs_assign_le (v := 2 + 2 * L.length + 2)
      (Expr.eval_add (Expr.eval_reg_of_eq h4') (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · simp only [normalPost, emitE, htz, ↓reduceIte]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (1 : ℕ) ≠ 8 by decide)]; exact h1
      · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (2 : ℕ) ≠ 8 by decide)]; exact h2
      · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (3 : ℕ) ≠ 8 by decide)]; exact h3
      · simp only [Function.update_self, List.length_append, List.length_singleton]; ring
      · rw [flatE_append]
        have hs1 := hm.snoc z
        rw [hlen] at hs1
        have hs2 := hs1.snoc t
        simp only [List.length_append, hlen, List.length_singleton] at hs2
        have hflat : flatE [(z, t)] = [z, t] := rfl
        rw [hflat, show flatE L ++ [z, t] = flatE L ++ [z] ++ [t] by simp]
        exact hs2
      · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 4 by decide)]; exact h5'
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (6 : ℕ) ≠ 8 by decide)]; exact h6
      · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (7 : ℕ) ≠ 8 by decide)]; exact h7
    · simp only [Expr.size]; omega


/-- The facts the core loop needs about one vertex `z < m²`, as hypotheses for `omega`. -/
private structure VertexFacts (n m z : ℕ) : Prop where
  hm : 1 ≤ m
  hN : m * m ≤ n
  hmn : m ≤ n
  hz : z < m * m
  hx : z / m < m
  hy : z % m < m
  t0 : (z / m + 2 * (z % m)) % m * m + z % m < m * m
  t1 : (z / m + 2 * (z % m) + 1) % m * m + z % m < m * m
  t2 : z / m * m + (z % m + 2 * (z / m)) % m < m * m
  t3 : z / m * m + (z % m + 2 * (z / m) + 1) % m < m * m

private lemma vertexFacts {n m z : ℕ} (hm : 1 ≤ m) (hN : m * m ≤ n) (hz : z < m * m) :
    VertexFacts n m z where
  hm := hm
  hN := hN
  hmn := le_trans (Nat.le_mul_self m) hN
  hz := hz
  hx := Nat.div_lt_of_lt_mul hz
  hy := Nat.mod_lt _ (by omega)
  t0 := tgt_lt 0 hz
  t1 := tgt_lt 1 hz
  t2 := tgt_lt 2 hz
  t3 := tgt_lt 3 hz

/-- Evaluate a neighbour expression: every intermediate value is at most the result, or below
`3m`. -/
local macro "t_eval" h:ident : tactic =>
  `(tactic| (obtain ⟨hm, hN, hmn, hz, hx, hy, t0, t1, t2, t3⟩ := $h
             simp only [tExpr0, tExpr1, tExpr2, tExpr3, tgt]
             eval_expr
             all_goals omega))

private lemma tExpr0_eval {n m z : ℕ} {st : State} (hf : VertexFacts n m z)
    (hW : 16 * n + 48 < 2 ^ w) (h2 : st.regs 2 = m) (h6 : st.regs 6 = z / m)
    (h7 : st.regs 7 = z % m) : tExpr0.eval w st = some (tgt m z 0) := by t_eval hf

private lemma tExpr1_eval {n m z : ℕ} {st : State} (hf : VertexFacts n m z)
    (hW : 16 * n + 48 < 2 ^ w) (h2 : st.regs 2 = m) (h6 : st.regs 6 = z / m)
    (h7 : st.regs 7 = z % m) : tExpr1.eval w st = some (tgt m z 1) := by t_eval hf

private lemma tExpr2_eval {n m z : ℕ} {st : State} (hf : VertexFacts n m z)
    (hW : 16 * n + 48 < 2 ^ w) (h2 : st.regs 2 = m) (h6 : st.regs 6 = z / m)
    (h7 : st.regs 7 = z % m) : tExpr2.eval w st = some (tgt m z 2) := by t_eval hf

private lemma tExpr3_eval {n m z : ℕ} {st : State} (hf : VertexFacts n m z)
    (hW : 16 * n + 48 < 2 ^ w) (h2 : st.regs 2 = m) (h6 : st.regs 6 = z / m)
    (h7 : st.regs 7 = z % m) : tExpr3.eval w st = some (tgt m z 3) := by t_eval hf


private lemma length_emitE (z t : ℕ) : (emitE z t).length ≤ 1 := by
  unfold emitE; split_ifs <;> simp

/-- The four `emitStmt` calls of the core body. -/
private lemma emits_triple (p : Program) {n m z : ℕ} (hf : VertexFacts n m z)
    (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (fun st => EdgeState n m (coreUpTo m z) st ∧ st.regs 5 = z ∧
        st.regs 6 = z / m ∧ st.regs 7 = z % m)
      (.seq (emitStmt tExpr0) (.seq (emitStmt tExpr1) (.seq (emitStmt tExpr2)
        (emitStmt tExpr3))))
      (normalPost fun st => EdgeState n m (coreUpTo m (z + 1)) st ∧ st.regs 5 = z)
      (fun _ => 160) := by
  have hw : 1 < 2 ^ w := by omega
  have hL := length_coreUpTo m z
  have hzN := hf.hz
  have hNn := hf.hN
  have l0 := length_emitE z (tgt m z 0)
  have l1 := length_emitE z (tgt m z 1)
  have l2 := length_emitE z (tgt m z 2)
  have E0 := emit_triple p tExpr0 (L := coreUpTo m z) (n := n) (m := m) (z := z) (x := z / m)
    (y := z % m) (t := tgt m z 0) hw (by omega)
    (fun st hE _ h6 h7 => tExpr0_eval hf hW hE.2.1 h6 h7)
  have E1 := emit_triple p tExpr1 (L := coreUpTo m z ++ emitE z (tgt m z 0)) (n := n) (m := m)
    (z := z) (x := z / m) (y := z % m) (t := tgt m z 1) hw
    (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => tExpr1_eval hf hW hE.2.1 h6 h7)
  have E2 := emit_triple p tExpr2
    (L := coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1)) (n := n) (m := m)
    (z := z) (x := z / m) (y := z % m) (t := tgt m z 2) hw
    (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => tExpr2_eval hf hW hE.2.1 h6 h7)
  have E3 := emit_triple p tExpr3
    (L := coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1) ++ emitE z (tgt m z 2))
    (n := n) (m := m) (z := z) (x := z / m) (y := z % m) (t := tgt m z 3) hw
    (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => tExpr3_eval hf hW hE.2.1 h6 h7)
  have E := Triple.seq_normal_const E0 (Triple.seq_normal_const E1
    (Triple.seq_normal_const E2 E3))
  refine E.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal =>
      refine ⟨?_, h.2.1⟩
      have hl : coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1) ++
          emitE z (tgt m z 2) ++ emitE z (tgt m z 3) = coreUpTo m (z + 1) := by
        rw [coreUpTo_succ]; simp [vertexEdges]
      rw [← hl]
      exact h.1
  · intro _ _
    simp only [tExpr0, tExpr1, tExpr2, tExpr3, Expr.size]
    omega

/-- The body of the core loop, for one vertex `z < m²`. -/
theorem coreBody_triple (p : Program) {n m z : ℕ} (hm : 1 ≤ m) (hN : m * m ≤ n)
    (hz : z < m * m) (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (fun st => EdgeState n m (coreUpTo m z) st ∧ st.regs 5 = z) coreBody
      (normalPost fun st => EdgeState n m (coreUpTo m (z + 1)) st ∧ st.regs 5 = z)
      (fun _ => 200) := by
  have hf := vertexFacts (n := n) hm hN hz
  intro st ω ⟨hE, h5⟩
  have h2 := hE.2.1
  refine runs_start_le (runs_seq_assign_le (v := z / m)
    (Expr.eval_div (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h2) (by omega)) ?_)
  have h5a : (Function.update st.regs 6 (z / m)) 5 = z := by
    rw [Function.update_of_ne (by decide)]; exact h5
  have h2a : (Function.update st.regs 6 (z / m)) 2 = m := by
    rw [Function.update_of_ne (by decide)]; exact h2
  refine runs_seq_assign_le (v := z % m)
    (Expr.eval_mod (Expr.eval_reg_of_eq h5a) (Expr.eval_reg_of_eq h2a) (by omega)) ?_
  refine runs_triple_le (emits_triple p hf hW) ?_ (fun _ _ h => h) ?_
  · refine ⟨(hE.update (r := 6) (by decide) _).update (r := 7) (by decide) _, ?_, ?_, ?_⟩
    · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 7 by decide)]; exact h5a
    · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 7 by decide), Function.update_self]
    · simp only [Function.update_self]
  · simp only [Expr.size]; omega

/-- **The core loop** writes the edges of the Margulis part, `coreEdges m`. -/
theorem coreLoop_triple (p : Program) {n m : ℕ} (hm : 1 ≤ m) (hN : m * m ≤ n)
    (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (EdgeState n m [])
      (forRange 5 (.const 0) (.reg 3) coreBody)
      (normalPost fun st => EdgeState n m (coreEdges m) st)
      (fun _ => 220 * n + 10) := by
  have hw : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := coreBody) (P := EdgeState n m [])
    (Inv := fun z st => EdgeState n m (coreUpTo m z) st ∧ st.regs 5 = z)
    200 0 (m * m) (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hE => ⟨Expr.eval_const (by omega),
      ⟨hE.update (r := 5) (by decide) 0, by simp⟩⟩)
    (fun _ _ _ _ h => h.2)
    (fun _ st _ _ h => Expr.eval_reg_of_eq h.1.2.2.1)
    (fun z _ hz => (coreBody_triple p hm hN hz hW).strengthen_post fun o st h => by
      cases o with
      | returned _ => exact h
      | normal => exact ⟨⟨h.1.update (r := 5) (by decide) _, by simp⟩, h.2⟩)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal => exact h.1
  · intro _ _
    simp only [Expr.size, Nat.sub_zero]
    nlinarith


lemma pendEdges_succ (N k : ℕ) : pendEdges N (k + 1) = pendEdges N k ++ [(N + k, k % N)] := by
  simp [pendEdges, List.range_succ]

/-- The body of the second loop, for one vertex `j'` with `N ≤ j' < n`. -/
theorem pendBody_triple (p : Program) {n m j : ℕ} (hN : m * m ≤ j)
    (hj : j < n) (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (fun st => EdgeState n m (coreEdges m ++ pendEdges (m * m) (j - m * m)) st ∧
        st.regs 5 = j) pendBody
      (normalPost fun st => EdgeState n m (coreEdges m ++ pendEdges (m * m) (j + 1 - m * m)) st ∧
        st.regs 5 = j)
      (fun _ => 30) := by
  have hw : 1 < 2 ^ w := by omega
  intro st ω ⟨hE, h5⟩
  obtain ⟨h1, h2, h3, h4, hmem⟩ := hE
  set L := coreEdges m ++ pendEdges (m * m) (j - m * m) with hL
  have hlenL : L.length ≤ 4 * (m * m) + (j - m * m) := by
    have := length_coreUpTo m (m * m)
    simp only [hL, List.length_append, pendEdges, List.length_map, List.length_range]
    exact Nat.add_le_add_right this _
  have hmm : m ≤ m * m := Nat.le_mul_self m
  have hlen := flatE_length L
  refine runs_start_le (runs_seq_store_le (x := 2 + 2 * L.length) (v := j)
    (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h5) ?_)
  refine runs_seq_store_le (x := 2 + 2 * L.length + 1) (v := (j - m * m) % (m * m))
    (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const hw) (by omega))
    (Expr.eval_mod (Expr.eval_sub (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h3) (by omega))
      (Expr.eval_reg_of_eq h3) (by omega)) ?_
  refine runs_assign_le (v := 2 + 2 * L.length + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
  · have hk : j + 1 - m * m = (j - m * m) + 1 := by omega
    have hjN : m * m + (j - m * m) = j := by omega
    have hL' : coreEdges m ++ pendEdges (m * m) (j + 1 - m * m) =
        L ++ [(j, (j - m * m) % (m * m))] := by
      rw [hk, pendEdges_succ, hjN, hL, List.append_assoc]
    simp only [normalPost]
    rw [hL']
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide)]; exact h1
    · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide)]; exact h2
    · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide)]; exact h3
    · simp only [Function.update_self, List.length_append, List.length_singleton]; ring
    · rw [flatE_append]
      have hs1 := hmem.snoc j
      rw [hlen] at hs1
      have hs2 := hs1.snoc ((j - m * m) % (m * m))
      simp only [List.length_append, hlen, List.length_singleton] at hs2
      have hflat : flatE [(j, (j - m * m) % (m * m))] = [j, (j - m * m) % (m * m)] := rfl
      rw [hflat, show flatE L ++ [j, (j - m * m) % (m * m)] =
        flatE L ++ [j] ++ [(j - m * m) % (m * m)] by simp]
      exact hs2
    · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 4 by decide)]; exact h5
  · simp only [Expr.size]; omega

/-- **The second loop** writes the edges `(N + j, j % N)` for `j < n - N`. -/
theorem pendLoop_triple (p : Program) {n m : ℕ} (hN : m * m ≤ n)
    (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (EdgeState n m (coreEdges m))
      (forRange 5 (.reg 3) (.reg 1) pendBody)
      (normalPost fun st => EdgeState n m (coreEdges m ++ pendEdges (m * m) (n - m * m)) st)
      (fun _ => 40 * n + 10) := by
  have hw : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .reg 3) (hi := .reg 1)
    (body := pendBody) (P := EdgeState n m (coreEdges m))
    (Inv := fun j st => EdgeState n m (coreEdges m ++ pendEdges (m * m) (j - m * m)) st ∧
      st.regs 5 = j)
    30 (m * m) n hN hw (fun _ => by omega)
    (fun st hE => ⟨Expr.eval_reg_of_eq hE.2.2.1,
      ⟨by simpa [pendEdges] using hE.update (r := 5) (by decide) (m * m), by simp⟩⟩)
    (fun _ _ _ _ h => h.2)
    (fun _ st _ _ h => Expr.eval_reg_of_eq h.1.1)
    (fun j hj hjn => (pendBody_triple p hj hjn hW).strengthen_post fun o st h => by
      cases o with
      | returned _ => exact h
      | normal => exact ⟨⟨h.1.update (r := 5) (by decide) _, by simp⟩, h.2⟩)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal => exact h.1
  · intro _ _
    simp only [Expr.size]
    omega

end MinCostFlow.ExplicitExpander
