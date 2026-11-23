module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompDefs
import WordRAM.Tactic

/-!
# Composing a walk with an embedding: loop invariant and one step

`CompCtx` collects the data and the precondition of `dsCompEdgeContract`. `CompInv c i st` is
the invariant of the loop of `dsCompEdgeStmt` after `i` edges of `Q`: the counter `reg 4` is the
length of `acc i = (Q.take i).flatMap (compPiece T)`, the words after `out` encode `acc i`, and
memory outside the output area is unchanged.

`dsComp_step_triple` proves one loop step. The copy of the next piece starts at
`out + 2 · |acc i|`, so its length word overwrites the last word of `acc i` (or the length word
of the output when `i = 0`). The step saves this word before the call and writes it back after.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The words of a walk after its length word. -/
def walkWords (P : List (ℕ × Bool)) : List ℕ :=
  P.flatMap fun p => [p.1, if p.2 then 1 else 0]

lemma walkWords_append (P P' : List (ℕ × Bool)) :
    walkWords (P ++ P') = walkWords P ++ walkWords P' := by
  simp [walkWords, List.flatMap_append]

lemma walkWords_length (P : List (ℕ × Bool)) : (walkWords P).length = 2 * P.length :=
  flatMap_pair_length P

lemma mWalkAt_iff (mem : ℕ → ℕ) (a : ℕ) (P : List (ℕ × Bool)) :
    MWalkAt mem a P ↔ mem a = P.length ∧ ListAt mem (a + 1) (walkWords P) := by
  unfold MWalkAt mWalkEncode walkWords
  exact listAt_cons

/-- The output after the first `i` edges of `Q`. -/
def compAcc (T : Embedding) (Q : List (ℕ × Bool)) (i : ℕ) : List (ℕ × Bool) :=
  (Q.take i).flatMap (compPiece T)

lemma compAcc_succ (T : Embedding) (Q : List (ℕ × Bool)) {i : ℕ} (hi : i < Q.length) :
    compAcc T Q (i + 1) = compAcc T Q i ++ compPiece T Q[i] := by
  simp only [compAcc]
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma compAcc_length_le (T : Embedding) (Q : List (ℕ × Bool)) (i : ℕ) :
    (compAcc T Q i).length ≤ (Q.flatMap (compPiece T)).length := by
  conv_rhs => rw [← List.take_append_drop i Q]
  simp only [compAcc, List.flatMap_append, List.length_append]
  omega

lemma compAcc_all (T : Embedding) (Q : List (ℕ × Bool)) :
    compAcc T Q Q.length = Q.flatMap (compPiece T) := by
  simp [compAcc]

/-- The data and the precondition of `dsCompEdgeContract`, unpacked. -/
structure CompCtx where
  w : ℕ
  eCap : ℕ
  T : Embedding
  Q : List (ℕ × Bool)
  qPtr : ℕ
  tab : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hqB : qPtr + (2 * Q.length + 1) < 2 ^ w
  htB : tab + eCap < 2 ^ w
  hoB : out + (2 * (Q.flatMap (compPiece T)).length + 1) < 2 ^ w
  dOQ : IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) qPtr (2 * Q.length + 1)
  dOT : IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) tab eCap
  hQ : MWalkAt mem0 qPtr Q
  hx : ∀ x ∈ Q, x.1 < eCap ∧ MWalkAt mem0 (mem0 (tab + x.1)) (T x.1) ∧
    mem0 (tab + x.1) + (2 * (T x.1).length + 1) < 2 ^ w ∧
    IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) (mem0 (tab + x.1))
      (2 * (T x.1).length + 1) ∧
    ∀ y ∈ T x.1, y.1 < eCap

/-- Invariant of the loop of `dsCompEdgeStmt` after `i` edges of `Q`. -/
def CompInv (c : CompCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.qPtr ∧ st.regs 1 = c.tab ∧ st.regs 2 = c.out ∧ st.regs 3 = c.Q.length ∧
  st.regs 4 = (compAcc c.T c.Q i).length ∧ st.regs 5 = i ∧
  ListAt st.mem (c.out + 1) (walkWords (compAcc c.T c.Q i)) ∧
  ∀ addr, (addr < c.out ∨ c.out + (2 * (c.Q.flatMap (compPiece c.T)).length + 1) ≤ addr) →
    st.mem addr = c.mem0 addr

/-- One loop step of `dsCompEdgeStmt`, cost `70 · |T x| + 100` for the edge `x = Q[i]`. -/
theorem dsComp_step_triple (c : CompCtx) {p : Program} {bOps bEmb : ℕ}
    (hpEmb : p.HasAt bEmb (embOpsProcs bOps)) {i : ℕ} (hi : i < c.Q.length) :
    Triple c.w p (CompInv c i) (dsCompBodyStmt bEmb)
      (normalPost fun st₁ =>
        CompInv c (i + 1) { st₁ with regs := Function.update st₁.regs 5 (i + 1) } ∧
          st₁.regs 5 = i)
      (fun _ => 70 * (c.T c.Q[i].1).length + 100) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, hL, hfr⟩ := hI
  have hw16 := c.hw16
  have hqB := c.hqB
  have htB := c.htB
  have hoB := c.hoB
  have hxQ : c.Q[i] ∈ c.Q := List.getElem_mem hi
  obtain ⟨hxE, hTat0, hTb, dOW, hTe⟩ := c.hx _ hxQ
  have hsucc := compAcc_succ c.T c.Q hi
  have hle1 := compAcc_length_le c.T c.Q (i + 1)
  have hlen1 : (compAcc c.T c.Q (i + 1)).length =
      (compAcc c.T c.Q i).length + (c.T c.Q[i].1).length := by
    rw [hsucc, List.length_append, compPiece_length]
  -- Reads of the inputs.
  have hQst : MWalkAt st.mem c.qPtr c.Q := c.hQ.of_agree fun addr h1 h2 =>
    hfr addr (c.dOQ.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 (by omega))
  have h6 : st.mem (c.qPtr + (2 * i + 1)) = c.Q[i].1 := by
    have := MWalkAt_step_edge hQst hi
    rwa [show c.qPtr + 1 + 2 * i = c.qPtr + (2 * i + 1) by omega] at this
  have h7 : st.mem (c.qPtr + (2 * i + 2)) = if c.Q[i].2 then 1 else 0 := by
    have := MWalkAt_step_dir hQst hi
    rwa [show c.qPtr + 1 + 2 * i + 1 = c.qPtr + (2 * i + 2) by omega] at this
  have htab : st.mem (c.tab + c.Q[i].1) = c.mem0 (c.tab + c.Q[i].1) :=
    hfr _ (c.dOT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hTst : MWalkAt st.mem (c.mem0 (c.tab + c.Q[i].1)) (c.T c.Q[i].1) :=
    hTat0.of_agree fun addr h1 h2 =>
      hfr addr (dOW.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 (by omega))
  have hn : st.mem (c.mem0 (c.tab + c.Q[i].1)) = (c.T c.Q[i].1).length := MWalkAt_head hTst
  have hdw : (if c.Q[i].2 then 1 else 0) < 2 ^ c.w := by split_ifs <;> omega
  have hTe_w : ∀ y ∈ compPiece c.T c.Q[i], y.1 < 2 ^ c.w := by
    intro y hy
    unfold compPiece at hy
    split_ifs at hy
    · have := hTe y hy; omega
    · obtain ⟨z, hz, hzy⟩ := mem_walkRev_fst hy
      have := hTe z hz; omega
  dsimp only [dsCompBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.Q[i].1)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0)
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r5)
        (by omega)) (Expr.eval_const (by omega)) (by omega)) (by omega)) h6) ?_
  refine runs_seq_assign_le (v := if c.Q[i].2 then 1 else 0)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp [r5])) (by omega)) (Expr.eval_const (by omega))
        (by omega)) (by omega)) h7) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.tab + c.Q[i].1))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) htab) ?_
  refine runs_seq_assign_le (v := (c.T c.Q[i].1).length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hn) ?_
  refine runs_seq_assign_le (v := c.out + 2 * (compAcc c.T c.Q i).length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r4]))
        (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := st.mem (c.out + 2 * (compAcc c.T c.Q i).length))
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) rfl) ?_
  -- The piece is written at `dst = out + 2 · |acc i|`; then the saved word is put back.
  have hdisj : c.mem0 (c.tab + c.Q[i].1) + (2 * (c.T c.Q[i].1).length + 1) ≤
        c.out + 2 * (compAcc c.T c.Q i).length ∨
      c.out + 2 * (compAcc c.T c.Q i).length + (2 * (c.T c.Q[i].1).length + 1) ≤
        c.mem0 (c.tab + c.Q[i].1) := by
    unfold IvlDisj at dOW; omega
  have hfinish : ∀ (K T : ℕ) (mem₁ : ℕ → ℕ) (regs₁ : ℕ → ℕ) (pos₁ : ℕ),
      MWalkAt mem₁ (c.out + 2 * (compAcc c.T c.Q i).length) (compPiece c.T c.Q[i]) →
      (∀ addr, addr < c.out + 2 * (compAcc c.T c.Q i).length ∨
        c.out + 2 * (compAcc c.T c.Q i).length + (2 * (compPiece c.T c.Q[i]).length + 1) ≤
          addr → mem₁ addr = st.mem addr) →
      regs₁ 0 = c.qPtr → regs₁ 1 = c.tab → regs₁ 2 = c.out → regs₁ 3 = c.Q.length →
      regs₁ 4 = (compAcc c.T c.Q i).length → regs₁ 5 = i →
      regs₁ 9 = c.out + 2 * (compAcc c.T c.Q i).length →
      regs₁ 10 = st.mem (c.out + 2 * (compAcc c.T c.Q i).length) →
      regs₁ 12 = (c.T c.Q[i].1).length → K + 10 ≤ T →
      ∃ o st' c₁, Runs c.w p ω
        (.store (.reg 9) (.reg 10) ;; .assign 4 (.bin .add (.reg 4) (.reg 12)))
        { mem := mem₁, regs := regs₁, pos := pos₁ } o st' c₁ ∧
        normalPost (fun st₁ =>
          CompInv c (i + 1) { st₁ with regs := Function.update st₁.regs 5 (i + 1) } ∧
            st₁.regs 5 = i) o st' ∧ K + c₁ ≤ T := by
    intro K T mem₁ regs₁ pos₁ hW₁ hfr₁ q0 q1 q2 q3 q4 q5 q9 q10 q12 hKT
    have hplen := compPiece_length c.T c.Q[i]
    refine runs_seq_store_le (x := c.out + 2 * (compAcc c.T c.Q i).length)
      (v := st.mem (c.out + 2 * (compAcc c.T c.Q i).length))
      (Expr.eval_reg_of_eq q9) (Expr.eval_reg_of_eq q10) ?_
    refine runs_assign_le (v := (compAcc c.T c.Q i).length + (c.T c.Q[i].1).length)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using q4))
        (Expr.eval_reg_of_eq (by simpa using q12)) (by omega)) ?_
      (by simp only [Expr.size_reg, Expr.size_bin]; omega)
    refine ⟨⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [hlen1], by simp,
      ?_, ?_⟩, by simp [q5]⟩
    · show ListAt (Function.update mem₁ (c.out + 2 * (compAcc c.T c.Q i).length)
        (st.mem (c.out + 2 * (compAcc c.T c.Q i).length))) (c.out + 1)
        (walkWords (compAcc c.T c.Q (i + 1)))
      rw [hsucc, walkWords_append, listAt_append]
      refine ⟨hL.congr fun k hk1 hk2 => ?_, ?_⟩
      · rw [walkWords_length] at hk2
        by_cases hk : k = c.out + 2 * (compAcc c.T c.Q i).length
        · subst hk; simp
        · rw [Function.update_of_ne hk, hfr₁ k (Or.inl (by omega))]
      · have h2 := ((mWalkAt_iff _ _ _).mp hW₁).2
        rw [walkWords_length, show c.out + 1 + 2 * (compAcc c.T c.Q i).length =
          c.out + 2 * (compAcc c.T c.Q i).length + 1 by omega]
        exact h2.congr fun k hk1 _ => Function.update_of_ne (by omega) _ _
    · intro addr ha
      have hne : addr ≠ c.out + 2 * (compAcc c.T c.Q i).length := by omega
      show Function.update mem₁ _ _ addr = _
      rw [Function.update_of_ne hne, hfr₁ addr (by omega), hfr addr ha]
  have hcopy := mWalkCopy_meetsContract (w := c.w) (P := c.T c.Q[i].1) hpEmb
  have hrev := mWalkRev_meetsContract (w := c.w) (P := c.T c.Q[i].1) hpEmb
  have hplen := compPiece_length c.T c.Q[i]
  have hptr_w : c.mem0 (c.tab + c.Q[i].1) < 2 ^ c.w := by omega
  have hdst_w : c.out + 2 * (compAcc c.T c.Q i).length < 2 ^ c.w := by omega
  have hTw : ∀ y ∈ c.T c.Q[i].1, y.1 < 2 ^ c.w := fun y hy => by have := hTe y hy; omega
  refine runs_seq_cond_le (v := if c.Q[i].2 then 1 else 0)
    (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · intro hnz
    have hx2 : c.Q[i].2 = true := by
      by_contra h; simp [h] at hnz
    have hpc : compPiece c.T c.Q[i] = c.T c.Q[i].1 := by simp [compPiece, hx2]
    refine runs_seq_call_le hcopy (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> assumption)
      ⟨_, _, rfl, hw16, by omega, by omega, hdisj, hTw, hTst⟩ ?_
    rintro v mem₁ pos₁ ⟨_, _, hargs', _, hW₁, hfr₁⟩
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl⟩ := hargs'
    refine hfinish _ _ mem₁ _ pos₁ (hpc ▸ hW₁)
      (fun addr h => hfr₁ addr (by rw [hplen] at h; exact h))
      (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4]) (by simp [r5])
      (by simp) (by simp) (by simp) ?_
    simp only [mWalkCopyContract, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    omega
  · intro hz
    have hx2 : c.Q[i].2 = false := by
      by_contra h; simp [h] at hz
    have hpc : compPiece c.T c.Q[i] = walkRev (c.T c.Q[i].1) := by simp [compPiece, hx2]
    refine runs_seq_call_le hrev (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> assumption)
      ⟨_, _, rfl, hw16, by omega, by omega, hdisj, hTw, hTst⟩ ?_
    rintro v mem₁ pos₁ ⟨_, _, hargs', _, hW₁, hfr₁⟩
    simp only [List.cons.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl⟩ := hargs'
    refine hfinish _ _ mem₁ _ pos₁ (hpc ▸ hW₁)
      (fun addr h => hfr₁ addr (by rw [hplen] at h; exact h))
      (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4]) (by simp [r5])
      (by simp) (by simp) (by simp) ?_
    simp only [mWalkRevContract, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
