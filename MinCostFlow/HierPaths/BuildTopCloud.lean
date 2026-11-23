module

public import MinCostFlow.ExpanderDecomp.ProgCloud
public import MinCostFlow.ExplicitExpander.Program

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Zero-heap explicit cloud expander procedure

The standard `cloudExpanderProcs` wraps `explicitProgram` in `WordRAM.runner`,
which advances the heap pointer by `O(s^4)`. Since `coreBody` and `pendBody`
from `ExplicitExpander` already write edges at the address held in register `4`,
running them directly with register `4` initialized to `outAddr + 2` writes
`(cloud s).encode` in place at `outAddr`, preserves all other memory, uses zero
heap space, and returns the incoming heap pointer unchanged in `O(s)` steps.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp
  MinCostFlow.ExplicitExpander

/-- Direct in-place cloud expander procedure.
Arguments `[sAddr, outAddr, h]`: reads `s = mem[sAddr]`, writes `(cloud s).encode`
at `outAddr`, preserves all memory outside `[outAddr, outAddr + 2 + 9 * s)`,
and returns `h` unchanged. -/
def buildTopCloud : Stmt :=
  .assign 9 (.reg 1) ;;
  .assign 10 (.reg 2) ;;
  .assign 1 (.load (.reg 0)) ;;
  .assign 2 (.const 1) ;;
  sqrtLoop ;;
  .assign 3 (.bin .mul (.reg 2) (.reg 2)) ;;
  .assign 4 (.bin .add (.reg 9) (.const 2)) ;;
  forRange 5 (.const 0) (.reg 3) coreBody ;;
  forRange 5 (.reg 3) (.reg 1) pendBody ;;
  .store (.reg 9) (.reg 1) ;;
  .store (.bin .add (.reg 9) (.const 1))
    (.bin .div (.bin .sub (.reg 4) (.bin .add (.reg 9) (.const 2))) (.const 2)) ;;
  .ret (.reg 10)

theorem buildTopCloud_noRand : buildTopCloud.NoRand := by
  simp [buildTopCloud, sqrtLoop, forRange, forUp, coreBody, pendBody, emitStmt, Stmt.NoRand]

/-- Contract for `buildTopCloud`: linear time `≤ 400 * s`, zero heap advance (`v = h`),
writes `GraphAt mem' outAddr (cloud s)`, and preserves memory outside `[outAddr, outAddr + 2 + 9 * s)`. -/
def buildTopCloudContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ sAddr outAddr h s, args = [sAddr, outAddr, h] ∧
      mem sAddr = s ∧ 2 ≤ s ∧
      outAddr + 2 + 9 * s < 2 ^ w ∧ 16 * s + 48 < 2 ^ w
  post args mem v mem' :=
    let sAddr := args.getD 0 0
    let outAddr := args.getD 1 0
    let h := args.getD 2 0
    let s := mem sAddr
    v = h ∧
    GraphAt mem' outAddr (cloud s) ∧
    (∀ a, a < outAddr ∨ outAddr + 2 + 9 * s ≤ a → mem' a = mem a)
  cost args mem := 400 * mem (args.getD 0 0)

private def EdgeStateAt (base n m : ℕ) (mem0 : ℕ → ℕ) (r9 r10 : ℕ) (L : List (ℕ × ℕ))
    (st : State) : Prop :=
  st.regs 1 = n ∧ st.regs 2 = m ∧ st.regs 3 = m * m ∧
    st.regs 4 = base + 2 * L.length ∧ st.regs 9 = r9 ∧ st.regs 10 = r10 ∧
    ListAt st.mem base (flatE L) ∧
    (∀ a, a < base ∨ base + 2 * L.length ≤ a → st.mem a = mem0 a)

private lemma EdgeStateAt.update {base n m r9 r10 : ℕ} {mem0 : ℕ → ℕ} {L : List (ℕ × ℕ)}
    {st : State} (h : EdgeStateAt base n m mem0 r9 r10 L st)
    {r : ℕ} (hr1 : 5 ≤ r) (hr2 : r ≤ 8) (v : ℕ) :
    EdgeStateAt base n m mem0 r9 r10 L { st with regs := Function.update st.regs r v } := by
  obtain ⟨h1, h2, h3, h4, h9, h10, hm, hf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm, hf⟩ <;> dsimp only <;>
    rw [Function.update_of_ne (by omega)] <;> assumption

private lemma sqrtLoop_frame_triple {w : ℕ} (p : Program) {n r9 r10 : ℕ} {mem0 : ℕ → ℕ}
    (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 1 = n ∧ 1 ≤ st.regs 2 ∧ st.regs 2 * st.regs 2 ≤ n ∧
        st.regs 9 = r9 ∧ st.regs 10 = r10 ∧ st.mem = mem0)
      sqrtLoop
      (normalPost fun st => st.regs 1 = n ∧ st.regs 2 = Nat.sqrt n ∧
        st.regs 9 = r9 ∧ st.regs 10 = r10 ∧ st.mem = mem0)
      (fun _ => 16 * n + 12) := by
  have hw : 1 < 2 ^ w := by omega
  have h := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .lt (.bin .mul (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 2) (.const 1)))
      (.bin .add (.reg 1) (.const 1)))
    (body := .assign 2 (.bin .add (.reg 2) (.const 1)))
    (Inv := fun st => st.regs 1 = n ∧ 1 ≤ st.regs 2 ∧ st.regs 2 * st.regs 2 ≤ n ∧
      st.regs 9 = r9 ∧ st.regs 10 = r10 ∧ st.mem = mem0)
    (Q := fun st => st.regs 1 = n ∧ st.regs 2 = Nat.sqrt n ∧
      st.regs 9 = r9 ∧ st.regs 10 = r10 ∧ st.mem = mem0)
    (fun st => n - st.regs 2)
    (fun st => if (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 then 1 else 0) 4
    (fun st ⟨h1, hk, hkn, _, _, _⟩ => by
      have hsq : (st.regs 2 + 1) * (st.regs 2 + 1) ≤ 4 * n := by nlinarith
      have hk1 : st.regs 2 + 1 < 2 ^ w := by nlinarith
      exact Expr.eval_lt_op
        (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) hk1)
          (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) hk1) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_const hw) (by omega)) hw)
    (fun st ⟨h1, _, hkn, h9, h10, hmem⟩ hc => by
      refine ⟨h1, Nat.eq_sqrt.mpr ⟨hkn, ?_⟩, h9, h10, hmem⟩
      by_contra hlt
      simp only [show (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 by omega, ↓reduceIte] at hc
      exact one_ne_zero hc)
    (fun st ⟨h1, hk, hkn, h9, h10, hmem⟩ hc => by
      have hlt : (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 := by
        by_contra hlt
        simp only [hlt, ↓reduceIte, ne_eq, not_true_eq_false] at hc
      have hk1 : st.regs 2 + 1 ≤ n := by nlinarith
      intro s ω hs
      subst hs
      refine ⟨.normal, { s with regs := Function.update s.regs 2 (s.regs 2 + 1) }, 4,
        runs_assign_iff.mpr ⟨s.regs 2 + 1,
          Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) (by omega), rfl, rfl,
          rfl⟩, ?_, le_rfl⟩
      simp only [normalPost, Function.update_self]
      refine ⟨⟨?_, by omega, by omega, ?_, ?_, hmem⟩, by omega⟩
      · rw [Function.update_of_ne (by decide)]; exact h1
      · rw [Function.update_of_ne (by decide)]; exact h9
      · rw [Function.update_of_ne (by decide)]; exact h10)
  refine h.mono_cost fun st _ => ?_
  simp only [Expr.size]
  have : (11 + 4 + 1) * (n - st.regs 2) ≤ 16 * n := by
    rw [show 11 + 4 + 1 = 16 by rfl]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

private lemma emitAt_triple {w : ℕ} (p : Program) (e : Expr)
    {base n m r9 r10 z x y t : ℕ} {mem0 : ℕ → ℕ} {L : List (ℕ × ℕ)}
    (hw : 1 < 2 ^ w) (hptr : base + 2 * L.length + 2 < 2 ^ w)
    (he : ∀ st : State, EdgeStateAt base n m mem0 r9 r10 L st →
      st.regs 5 = z → st.regs 6 = x → st.regs 7 = y → e.eval w st = some t) :
    Triple w p
      (fun st => EdgeStateAt base n m mem0 r9 r10 L st ∧
        st.regs 5 = z ∧ st.regs 6 = x ∧ st.regs 7 = y)
      (emitStmt e)
      (normalPost fun st => EdgeStateAt base n m mem0 r9 r10 (L ++ emitE z t) st ∧
        st.regs 5 = z ∧ st.regs 6 = x ∧ st.regs 7 = y)
      (fun _ => e.size + 25) := by
  intro st ω ⟨hE, h5, h6, h7⟩
  have hev := he st hE h5 h6 h7
  obtain ⟨h1, h2, h3, h4, h9, h10, hm, hf⟩ := hE
  refine runs_start_le (runs_seq_assign_le hev ?_)
  have h8 : (Function.update st.regs 8 t) 8 = t := Function.update_self ..
  have h5' : (Function.update st.regs 8 t) 5 = z := by
    rw [Function.update_of_ne (by decide)]; exact h5
  have h4' : (Function.update st.regs 8 t) 4 = base + 2 * L.length := by
    rw [Function.update_of_ne (by decide)]; exact h4
  by_cases htz : t = z
  · refine runs_cond_le (v := 1)
      (Expr.eval_eq_true (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h5') htz hw)
      (fun _ => ?_) (fun h => absurd h one_ne_zero)
    refine runs_nop_le ?_ ?_
    · have hE : EdgeStateAt base n m mem0 r9 r10 L st := ⟨h1, h2, h3, h4, h9, h10, hm, hf⟩
      simp only [normalPost, emitE, htz, ↓reduceIte, List.append_nil]
      refine ⟨hE.update (r := 8) (by decide) (by decide) t, h5', ?_, ?_⟩
      · rw [Function.update_of_ne (by decide)]; exact h6
      · rw [Function.update_of_ne (by decide)]; exact h7
    · simp only [Expr.size]; omega
  · refine runs_cond_le (v := 0)
      (Expr.eval_eq_false (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h5') htz hw)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlen := flatE_length L
    refine runs_seq_store_le (x := base + 2 * L.length) (v := z) (Expr.eval_reg_of_eq h4')
      (Expr.eval_reg_of_eq h5') ?_
    refine runs_seq_store_le (x := base + 2 * L.length + 1) (v := t)
      (Expr.eval_add (Expr.eval_reg_of_eq h4') (Expr.eval_const hw) (by omega))
      (Expr.eval_reg_of_eq h8) ?_
    refine runs_assign_le (v := base + 2 * L.length + 2)
      (Expr.eval_add (Expr.eval_reg_of_eq h4') (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · simp only [normalPost, emitE, htz, ↓reduceIte]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (1 : ℕ) ≠ 8 by decide)]; exact h1
      · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (2 : ℕ) ≠ 8 by decide)]; exact h2
      · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (3 : ℕ) ≠ 8 by decide)]; exact h3
      · simp only [Function.update_self, List.length_append, List.length_singleton]; ring
      · simp only [Function.update_of_ne (show (9 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (9 : ℕ) ≠ 8 by decide)]; exact h9
      · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (10 : ℕ) ≠ 8 by decide)]; exact h10
      · rw [flatE_append]
        have hs1 := hm.snoc z
        rw [hlen] at hs1
        have hs2 := hs1.snoc t
        simp only [List.length_append, hlen, List.length_singleton] at hs2
        have hflat : flatE [(z, t)] = [z, t] := rfl
        rw [hflat, show flatE L ++ [z, t] = flatE L ++ [z] ++ [t] by simp]
        exact hs2
      · intro a ha
        dsimp only
        simp only [List.length_append, List.length_singleton] at ha
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hf a (by omega)
      · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 4 by decide)]; exact h5'
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (6 : ℕ) ≠ 8 by decide)]; exact h6
      · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 4 by decide),
          Function.update_of_ne (show (7 : ℕ) ≠ 8 by decide)]; exact h7
    · simp only [Expr.size]; omega

private lemma length_emitE' (z t : ℕ) : (emitE z t).length ≤ 1 := by
  unfold emitE; split_ifs <;> simp

private lemma tExpr_evals {w n m z : ℕ} {st : State}
    (hm : 1 ≤ m) (hN : m * m ≤ n) (hz : z < m * m) (hW : 16 * n + 48 < 2 ^ w)
    (h2 : st.regs 2 = m) (h6 : st.regs 6 = z / m) (h7 : st.regs 7 = z % m) :
    tExpr0.eval w st = some (tgt m z 0) ∧
    tExpr1.eval w st = some (tgt m z 1) ∧
    tExpr2.eval w st = some (tgt m z 2) ∧
    tExpr3.eval w st = some (tgt m z 3) := by
  have hmn : m ≤ n := le_trans (Nat.le_mul_self m) hN
  have hx : z / m < m := Nat.div_lt_of_lt_mul hz
  have hy : z % m < m := Nat.mod_lt _ (by omega)
  have t0 := tgt_lt 0 hz
  have t1 := tgt_lt 1 hz
  have t2 := tgt_lt 2 hz
  have t3 := tgt_lt 3 hz
  simp only [tgt] at t0 t1 t2 t3
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [tExpr0, tExpr1, tExpr2, tExpr3, tgt]; eval_expr)

private lemma coreBodyAt_triple {w : ℕ} (p : Program)
    {base n m r9 r10 z : ℕ} {mem0 : ℕ → ℕ}
    (hm : 1 ≤ m) (hN : m * m ≤ n) (hz : z < m * m)
    (hW : 16 * n + 48 < 2 ^ w) (hBase : base + 9 * n < 2 ^ w) :
    Triple w p
      (fun st => EdgeStateAt base n m mem0 r9 r10 (coreUpTo m z) st ∧ st.regs 5 = z)
      coreBody
      (normalPost fun st =>
        EdgeStateAt base n m mem0 r9 r10 (coreUpTo m (z + 1)) st ∧ st.regs 5 = z)
      (fun _ => 200) := by
  have hw : 1 < 2 ^ w := by omega
  have hL := length_coreUpTo m z
  have l0 := length_emitE' z (tgt m z 0)
  have l1 := length_emitE' z (tgt m z 1)
  have l2 := length_emitE' z (tgt m z 2)
  have E0 := emitAt_triple p tExpr0 (base := base) (mem0 := mem0) (r9 := r9) (r10 := r10)
    (L := coreUpTo m z) (n := n) (m := m) (z := z) (x := z / m) (y := z % m) (t := tgt m z 0)
    hw (by omega) (fun st hE _ h6 h7 => (tExpr_evals hm hN hz hW hE.2.1 h6 h7).1)
  have E1 := emitAt_triple p tExpr1 (base := base) (mem0 := mem0) (r9 := r9) (r10 := r10)
    (L := coreUpTo m z ++ emitE z (tgt m z 0)) (n := n) (m := m) (z := z) (x := z / m)
    (y := z % m) (t := tgt m z 1) hw (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => (tExpr_evals hm hN hz hW hE.2.1 h6 h7).2.1)
  have E2 := emitAt_triple p tExpr2 (base := base) (mem0 := mem0) (r9 := r9) (r10 := r10)
    (L := coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1)) (n := n) (m := m) (z := z)
    (x := z / m) (y := z % m) (t := tgt m z 2) hw (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => (tExpr_evals hm hN hz hW hE.2.1 h6 h7).2.2.1)
  have E3 := emitAt_triple p tExpr3 (base := base) (mem0 := mem0) (r9 := r9) (r10 := r10)
    (L := coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1) ++ emitE z (tgt m z 2))
    (n := n) (m := m) (z := z) (x := z / m) (y := z % m) (t := tgt m z 3)
    hw (by simp only [List.length_append]; omega)
    (fun st hE _ h6 h7 => (tExpr_evals hm hN hz hW hE.2.1 h6 h7).2.2.2)
  have E : Triple w p
      (fun st => EdgeStateAt base n m mem0 r9 r10 (coreUpTo m z) st ∧ st.regs 5 = z ∧
        st.regs 6 = z / m ∧ st.regs 7 = z % m)
      (.seq (emitStmt tExpr0) (.seq (emitStmt tExpr1) (.seq (emitStmt tExpr2) (emitStmt tExpr3))))
      (normalPost fun st => EdgeStateAt base n m mem0 r9 r10 (coreUpTo m (z + 1)) st ∧ st.regs 5 = z)
      (fun _ => 160) :=
    (Triple.seq_normal_const E0 (Triple.seq_normal_const E1
      (Triple.seq_normal_const E2 E3))).conseq (fun _ h => h)
      (fun o st h => by
        cases o with
        | returned _ => exact h
        | normal =>
          refine ⟨?_, h.2.1⟩
          have hl : coreUpTo m z ++ emitE z (tgt m z 0) ++ emitE z (tgt m z 1) ++
              emitE z (tgt m z 2) ++ emitE z (tgt m z 3) = coreUpTo m (z + 1) := by
            rw [coreUpTo_succ]; simp [vertexEdges]
          rw [← hl]; exact h.1)
      (fun _ _ => by simp only [tExpr0, tExpr1, tExpr2, tExpr3, Expr.size]; omega)
  intro st ω ⟨hE, h5⟩
  have h2 := hE.2.1
  have hmn : m ≤ n := le_trans (Nat.le_mul_self m) hN
  refine runs_start_le (runs_seq_assign_le (v := z / m)
    (Expr.eval_div (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h2) (by omega)) ?_)
  have h5a : (Function.update st.regs 6 (z / m)) 5 = z := by
    rw [Function.update_of_ne (by decide)]; exact h5
  have h2a : (Function.update st.regs 6 (z / m)) 2 = m := by
    rw [Function.update_of_ne (by decide)]; exact h2
  refine runs_seq_assign_le (v := z % m)
    (Expr.eval_mod (Expr.eval_reg_of_eq h5a) (Expr.eval_reg_of_eq h2a) (by omega)) ?_
  refine runs_triple_le E ?_ (fun _ _ h => h) ?_
  · refine ⟨(hE.update (r := 6) (by decide) (by decide) _).update (r := 7) (by decide) (by decide) _,
      ?_, ?_, ?_⟩
    · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 7 by decide)]; exact h5a
    · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 7 by decide), Function.update_self]
    · simp only [Function.update_self]
  · simp only [Expr.size]; omega

private lemma coreLoopAt_triple {w : ℕ} (p : Program) {base n m r9 r10 : ℕ} {mem0 : ℕ → ℕ}
    (hm : 1 ≤ m) (hN : m * m ≤ n) (hW : 16 * n + 48 < 2 ^ w) (hBase : base + 9 * n < 2 ^ w) :
    Triple w p (EdgeStateAt base n m mem0 r9 r10 [])
      (forRange 5 (.const 0) (.reg 3) coreBody)
      (normalPost fun st => EdgeStateAt base n m mem0 r9 r10 (coreEdges m) st)
      (fun _ => 220 * n + 10) := by
  have hw : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := coreBody) (P := EdgeStateAt base n m mem0 r9 r10 [])
    (Inv := fun z st => EdgeStateAt base n m mem0 r9 r10 (coreUpTo m z) st ∧ st.regs 5 = z)
    200 0 (m * m) (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hE => ⟨Expr.eval_const (by omega),
      ⟨hE.update (r := 5) (by decide) (by decide) 0, by simp⟩⟩)
    (fun _ _ _ _ h => h.2)
    (fun _ st _ _ h => Expr.eval_reg_of_eq h.1.2.2.1)
    (fun z _ hz => (coreBodyAt_triple p hm hN hz hW hBase).strengthen_post fun o st h => by
      cases o with
      | returned _ => exact h
      | normal => exact ⟨⟨h.1.update (r := 5) (by decide) (by decide) _, by simp⟩, h.2⟩)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h; cases o <;> [exact h.1; exact h]
  · intro _ _; simp only [Expr.size, Nat.sub_zero]; nlinarith

private lemma pendBodyAt_triple {w : ℕ} (p : Program)
    {base n m r9 r10 j : ℕ} {mem0 : ℕ → ℕ}
    (hN : m * m ≤ j) (hj : j < n) (hW : 16 * n + 48 < 2 ^ w) (hBase : base + 9 * n < 2 ^ w) :
    Triple w p
      (fun st => EdgeStateAt base n m mem0 r9 r10
        (coreEdges m ++ pendEdges (m * m) (j - m * m)) st ∧ st.regs 5 = j)
      pendBody
      (normalPost fun st => EdgeStateAt base n m mem0 r9 r10
        (coreEdges m ++ pendEdges (m * m) (j + 1 - m * m)) st ∧ st.regs 5 = j)
      (fun _ => 30) := by
  have hw : 1 < 2 ^ w := by omega
  intro st ω ⟨hE, h5⟩
  obtain ⟨h1, h2, h3, h4, h9, h10, hmem, hf⟩ := hE
  set L := coreEdges m ++ pendEdges (m * m) (j - m * m) with hL
  have hlenL : L.length ≤ 4 * (m * m) + (j - m * m) := by
    have := length_coreUpTo m (m * m)
    simp only [hL, List.length_append, pendEdges, List.length_map, List.length_range]
    exact Nat.add_le_add_right this _
  have hlen := flatE_length L
  refine runs_start_le (runs_seq_store_le (x := base + 2 * L.length) (v := j)
    (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h5) ?_)
  refine runs_seq_store_le (x := base + 2 * L.length + 1) (v := (j - m * m) % (m * m))
    (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const hw) (by omega))
    (Expr.eval_mod (Expr.eval_sub (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq h3) (by omega))
      (Expr.eval_reg_of_eq h3) (by omega)) ?_
  refine runs_assign_le (v := base + 2 * L.length + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
  · have hk : j + 1 - m * m = (j - m * m) + 1 := by omega
    have hjN : m * m + (j - m * m) = j := by omega
    have hL' : coreEdges m ++ pendEdges (m * m) (j + 1 - m * m) =
        L ++ [(j, (j - m * m) % (m * m))] := by
      rw [hk, pendEdges_succ, hjN, hL, List.append_assoc]
    simp only [normalPost]
    rw [hL']
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide)]; exact h1
    · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide)]; exact h2
    · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide)]; exact h3
    · simp only [Function.update_self, List.length_append, List.length_singleton]; ring
    · simp only [Function.update_of_ne (show (9 : ℕ) ≠ 4 by decide)]; exact h9
    · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 4 by decide)]; exact h10
    · rw [flatE_append]
      have hs1 := hmem.snoc j
      rw [hlen] at hs1
      have hs2 := hs1.snoc ((j - m * m) % (m * m))
      simp only [List.length_append, hlen, List.length_singleton] at hs2
      have hflat : flatE [(j, (j - m * m) % (m * m))] = [j, (j - m * m) % (m * m)] := rfl
      rw [hflat, show flatE L ++ [j, (j - m * m) % (m * m)] =
        flatE L ++ [j] ++ [(j - m * m) % (m * m)] by simp]
      exact hs2
    · intro a ha
      dsimp only
      simp only [List.length_append, List.length_singleton] at ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hf a (by omega)
    · simp only [Function.update_of_ne (show (5 : ℕ) ≠ 4 by decide)]; exact h5
  · simp only [Expr.size]; omega

private lemma pendLoopAt_triple {w : ℕ} (p : Program) {base n m r9 r10 : ℕ} {mem0 : ℕ → ℕ}
    (hN : m * m ≤ n) (hW : 16 * n + 48 < 2 ^ w) (hBase : base + 9 * n < 2 ^ w) :
    Triple w p (EdgeStateAt base n m mem0 r9 r10 (coreEdges m))
      (forRange 5 (.reg 3) (.reg 1) pendBody)
      (normalPost fun st =>
        EdgeStateAt base n m mem0 r9 r10 (coreEdges m ++ pendEdges (m * m) (n - m * m)) st)
      (fun _ => 40 * n + 10) := by
  have hw : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .reg 3) (hi := .reg 1)
    (body := pendBody) (P := EdgeStateAt base n m mem0 r9 r10 (coreEdges m))
    (Inv := fun j st => EdgeStateAt base n m mem0 r9 r10
      (coreEdges m ++ pendEdges (m * m) (j - m * m)) st ∧ st.regs 5 = j)
    30 (m * m) n hN hw (fun _ => by omega)
    (fun st hE => ⟨Expr.eval_reg_of_eq hE.2.2.1,
      ⟨by simpa [pendEdges] using hE.update (r := 5) (by decide) (by decide) (m * m), by simp⟩⟩)
    (fun _ _ _ _ h => h.2)
    (fun _ st _ _ h => Expr.eval_reg_of_eq h.1.1)
    (fun j hj hjn => (pendBodyAt_triple p hj hjn hW hBase).strengthen_post fun o st h => by
      cases o with
      | returned _ => exact h
      | normal => exact ⟨⟨h.1.update (r := 5) (by decide) (by decide) _, by simp⟩, h.2⟩)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st h; cases o <;> [exact h.1; exact h]
  · intro _ _; simp only [Expr.size]; omega

/-- `buildTopCloud` writes `cloud s` in place at `outAddr` in `≤ 400 * s` steps with zero heap. -/
theorem buildTopCloud_meetsContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some buildTopCloud) :
    MeetsContract w p f (buildTopCloudContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨sAddr, outAddr, h, s, rfl, hs_mem, hs2, hOutW, hW⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hBaseW : (outAddr + 2) + 9 * s < 2 ^ w := by omega
  set m := Nat.sqrt s with hm_def
  have hm1 : 1 ≤ m := Nat.sqrt_pos.mpr (by omega)
  have hN : m * m ≤ s := Nat.sqrt_le s
  refine runs_start_le ?_
  unfold buildTopCloud
  refine runs_seq_assign_le (v := outAddr) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_assign_le (v := h) (Expr.eval_reg_of_eq (by simp [startState])) ?_
  refine runs_seq_assign_le (v := s)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hs_mem) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const hw1) ?_
  refine runs_seq_triple_le (sqrtLoop_frame_triple p (n := s) (r9 := outAddr) (r10 := h)
    (mem0 := mem) hW) ?_ ?_
  · refine ⟨by simp, by simp, by simp; omega, by simp, by simp, rfl⟩
  intro st₁ ⟨h1, h2, h9, h10, hmem1⟩
  refine runs_seq_assign_le (v := m * m)
    (Expr.eval_mul (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq h2) (by omega)) ?_
  refine runs_seq_assign_le (v := outAddr + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h9])) (Expr.eval_const hw2) (by omega)) ?_
  have hE0 : EdgeStateAt (outAddr + 2) s m mem outAddr h []
      ⟨st₁.mem, Function.update (Function.update st₁.regs 3 (m * m)) 4 (outAddr + 2), st₁.pos⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, listAt_nil _ _, fun a _ => hmem1 ▸ rfl⟩
    · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (1 : ℕ) ≠ 3 by decide)]; exact h1
    · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (2 : ℕ) ≠ 3 by decide)]; exact h2
    · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide), Function.update_self]
    · simp
    · simp only [Function.update_of_ne (show (9 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (9 : ℕ) ≠ 3 by decide)]; exact h9
    · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (10 : ℕ) ≠ 3 by decide)]; exact h10
  refine runs_seq_triple_le (coreLoopAt_triple p hm1 hN hW hBaseW) hE0 ?_
  intro st₂ hE2
  refine runs_seq_triple_le (pendLoopAt_triple p hN hW hBaseW) hE2 ?_
  intro st₃ ⟨h31, _, _, h34, h39, h310, hmem3, hf3⟩
  set E := coreEdges m ++ pendEdges (m * m) (s - m * m) with hE_def
  have hcloud_eq : cloud s = explicitGraph s := cloud_eq_explicitGraph hs2
  have hlenE : 2 * E.length ≤ 9 * s := by
    have hcm := cloud_m_le hs2
    rw [hcloud_eq] at hcm
    simpa [explicitGraph, Graph.m, hE_def, hm_def] using hcm
  refine runs_seq_store_le (x := outAddr) (v := s)
    (Expr.eval_reg_of_eq h39) (Expr.eval_reg_of_eq h31) ?_
  refine runs_seq_store_le (x := outAddr + 1) (v := E.length)
    (Expr.eval_add (Expr.eval_reg_of_eq h39) (Expr.eval_const hw1) (by omega))
    (Expr.eval_eq_of_eq
      (Expr.eval_div
        (Expr.eval_sub (Expr.eval_reg_of_eq h34)
          (Expr.eval_add (Expr.eval_reg_of_eq h39) (Expr.eval_const hw2) (by omega))
          (by omega))
        (Expr.eval_const hw2) (by omega))
      (by omega)) ?_
  refine runs_ret_le (v := h) (Expr.eval_reg_of_eq h310) ?_ ?_
  · dsimp only [buildTopCloudContract]
    simp only [List.getD_cons_zero, List.getD_cons_succ, hs_mem]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hcloud_eq]
      change ListAt _ outAddr (explicitGraph s).encode
      have henc : (explicitGraph s).encode = s :: E.length :: flatE E := rfl
      rw [henc, listAt_cons, listAt_cons]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Function.update_of_ne (by omega : outAddr ≠ outAddr + 1), Function.update_self]
      · simp only [Function.update_self]
      · exact (hmem3.update_lt (by omega)).update_lt (by omega)
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hf3 a (by omega)
  · simp only [buildTopCloudContract, List.getD_cons_zero, hs_mem, Expr.size]
    omega

end MinCostFlow.HierPaths

end
