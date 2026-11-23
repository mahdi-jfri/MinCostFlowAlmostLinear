module

public import MinCostFlow.LowStretch.PQRep

/-!
# Emptying the class queues

After a petal search the queue may still hold entries. `pqClear` empties it without running
Dijkstra on: it sets the first and last-plus-one positions of every list to `0`, sets every leaf
of the tournament tree to its empty value `INF · J + c`, and rebuilds the inner cells of the tree
from the bottom up (`pqClear_spec`). Its cost is `O(J)`, not the size of the queue.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The cells of the queue that `pqClear` writes: the tree and the positions of the lists. -/
def pqOut (D J a : ℕ) : Prop := D + 4 ≤ a ∧ a < D + 3 + 4 * J

/-- After the first loop, the leaves of `c < i` are empty and their lists are at `0`. -/
def ClrDone (M : ℕ → ℕ) (D J INF i : ℕ) : Prop :=
  ∀ c < i, M (pqH D J c) = 0 ∧ M (pqT D J c) = 0 ∧ M (D + 3 + J + c) = INF * J + c

/-- After `k` steps of the second loop, the inner cells `J - k, …, J - 1` are the least of their
two children. -/
def ClrTree (M : ℕ → ℕ) (D J k : ℕ) : Prop :=
  ∀ i, J - k ≤ i → 1 ≤ i → i < J → M (D + 3 + i) = min (M (D + 3 + 2 * i)) (M (D + 3 + 2 * i + 1))

/-- The body of the first loop, for `c` in register `3`. Registers `0`, `1`, `2` hold `D`, `J`,
`INF`. -/
def clrB1 : Stmt :=
  .seq (.store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 2) (.reg 1)))
      (.reg 3)) (.const 0))
  (.seq (.store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 3) (.reg 1)))
      (.reg 3)) (.const 0))
    (.store (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3)) (.reg 1)) (.reg 3))
      (.bin .add (.bin .mul (.reg 2) (.reg 1)) (.reg 3))))

/-- The body of the second loop, for step `k` in register `3`: cell `i = J - 1 - k`. -/
def clrB2 : Stmt :=
  .seq (.assign 4 (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 3)))
  (.seq (.assign 5 (.load (.bin .add (.bin .add (.reg 0) (.const 3))
      (.bin .mul (.const 2) (.reg 4)))))
  (.seq (.assign 6 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 3))
      (.bin .mul (.const 2) (.reg 4))) (.const 1))))
    (.cond (.bin .lt (.reg 6) (.reg 5))
      (.store (.bin .add (.bin .add (.reg 0) (.const 3)) (.reg 4)) (.reg 6))
      (.store (.bin .add (.bin .add (.reg 0) (.const 3)) (.reg 4)) (.reg 5)))))

/-- `pqClear` with arguments `[D, J, INF]`. -/
def pqClear : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1) clrB1)
  (.seq (forRange 3 (.const 0) (.bin .sub (.reg 1) (.const 1)) clrB2) (.ret (.const 0)))

theorem pqClear_noRand : pqClear.NoRand := by
  simp [pqClear, clrB1, clrB2, forRange, forUp, Stmt.NoRand]

/-- The contract of `pqClear`. The cells `D`, `D + 1`, `D + 2` already hold `J`, `A`, `INF`. -/
def pqClearC (w : ℕ) : Contract where
  pre args mem := ∃ D J A INF, args = [D, J, INF] ∧ mem D = J ∧ mem (D + 1) = A ∧
    mem (D + 2) = INF ∧ 1 ≤ J ∧ D + pqSize J A < 2 ^ w ∧ INF * J + J < 2 ^ w
  post args mem _ mem' := ∀ D J A INF, args = [D, J, INF] → mem (D + 1) = A →
    PQRep mem' D J A INF (fun _ => []) ∧ (∀ c < J, mem' (pqT D J c) = 0) ∧
    ∀ a, ¬ pqOut D J a → mem' a = mem a
  cost args _ := 150 * args.getD 1 0 + 50

end MinCostFlow.LowStretch

namespace MinCostFlow.LowStretch

open WordRAM

set_option maxHeartbeats 2000000 in
theorem pqClear_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [pqClear]) :
    MeetsContract w p b (pqClearC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨D, J, A, INF, rfl, hD, hA, hIc, hJ, hfit, hINF⟩ := hpre
  have hproc : p.procs[b]? = some pqClear := hp 0 (by simp)
  clear hp
  have hsz : D + 3 + 4 * J ≤ D + pqSize J A := by unfold pqSize; omega
  have hw1 : 1 < 2 ^ w := by omega
  have wJ : J < 2 ^ w := by omega
  let R : State → Prop := fun st => st.regs 0 = D ∧ st.regs 1 = J ∧ st.regs 2 = INF
  have hRu : ∀ st r v, R st → 3 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2⟩ hr
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  -- the first loop
  let I1 : ℕ → State → Prop := fun c st => R st ∧ st.regs 3 = c ∧ ClrDone st.mem D J INF c ∧
    ∀ a, ¬ pqOut D J a → st.mem a = mem a
  have hloop1 := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := clrB1) (P := fun st => R st ∧ st.mem = mem) (Inv := I1) 40 0 J
    (Nat.zero_le _) hw1 (fun _ => wJ)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 3 0 hr (by omega), by simp,
      fun c hc => absurd hc (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun c _ hc st ω hI => by
      obtain ⟨⟨a0, a1, a2⟩, h3, hdone, hfr⟩ := hI
      have hb : INF * J + c < 2 ^ w := by omega
      refine runs_start_le ?_
      dsimp only [clrB1]
      wram_run
      all_goals first
        | wram_cost
        | omega
        | (refine ⟨⟨⟨?_, ?_, ?_⟩, by simp, fun c' hc' => ?_, fun a ha => ?_⟩, by simp [h3]⟩
           · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a0
           · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a1
           · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a2
           · by_cases e : c' = c
             · subst e
               refine ⟨?_, ?_, ?_⟩ <;>
                 simp (disch := omega) only [pqH, pqT, Function.update_of_ne, Function.update_self,
                   a0, a1, a2, h3] <;> omega
             · obtain ⟨d1, d2, d3⟩ := hdone c' (by omega)
               refine ⟨?_, ?_, ?_⟩ <;>
                 simp (disch := omega) only [pqH, pqT, Function.update_of_ne, a0, a1, a2, h3] <;>
                 simp only [pqH, pqT] at d1 d2 <;> assumption
           · unfold pqOut at ha
             simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3]
             exact hfr a ha))
  -- the second loop
  let I2 : ℕ → State → Prop := fun k st => R st ∧ st.regs 3 = k ∧ ClrDone st.mem D J INF J ∧
    ClrTree st.mem D J k ∧ ∀ a, ¬ pqOut D J a → st.mem a = mem a
  have hloop2 := Triple.forRange_const (p := p) (r := 3) (lo := .const 0)
    (hi := .bin .sub (.reg 1) (.const 1))
    (body := clrB2) (P := I1 J) (Inv := I2) 60 0 (J - 1)
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hI => ⟨by eval_expr, hRu st 3 0 hI.1 (by omega), by simp, hI.2.2.1,
      fun i h1 h2 h3 => by omega, hI.2.2.2⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun k _ hk st ω hI => by
      obtain ⟨⟨a0, a1, a2⟩, h3, hdone, htree, hfr⟩ := hI
      have hb1 : D + 3 + 2 * (J - 1 - k) + 1 < 2 ^ w := by omega
      have e0 : st.mem (st.regs 0 + 3 + 2 * (J - 1 - k) + 1) = st.mem (D + 3 + 2 * (J - 1 - k) + 1) := by
        rw [a0]
      have e0' : st.mem (st.regs 0 + 3 + 2 * (J - 1 - k)) = st.mem (D + 3 + 2 * (J - 1 - k)) := by
        rw [a0]
      by_cases hlt : st.mem (D + 3 + 2 * (J - 1 - k) + 1) < st.mem (D + 3 + 2 * (J - 1 - k))
      · refine runs_start_le ?_
        dsimp only [clrB2]
        wram_run
        all_goals first
          | wram_cost
          | omega
          | (refine ⟨⟨⟨?_, ?_, ?_⟩, by simp, fun c hc => ?_, fun i i1 i2 i3 => ?_, fun a ha => ?_⟩,
              by simp [h3]⟩
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a0
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a1
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a2
             · obtain ⟨d1, d2, d3⟩ := hdone c hc
               simp only [pqH, pqT] at d1 d2 ⊢
               refine ⟨?_, ?_, ?_⟩ <;>
                 simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3] <;> assumption
             · by_cases e : i = J - 1 - k
               · subst e
                 simp (disch := omega) only [Function.update_of_ne, Function.update_self, a0, a1,
                   a2, h3]
                 omega
               · have := htree i (by omega) i2 i3
                 simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3]
                 exact this
             · unfold pqOut at ha
               simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3]
               exact hfr a ha)
      · refine runs_start_le ?_
        dsimp only [clrB2]
        wram_run
        all_goals first
          | wram_cost
          | omega
          | (refine ⟨⟨⟨?_, ?_, ?_⟩, by simp, fun c hc => ?_, fun i i1 i2 i3 => ?_, fun a ha => ?_⟩,
              by simp [h3]⟩
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a0
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a1
             · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact a2
             · obtain ⟨d1, d2, d3⟩ := hdone c hc
               simp only [pqH, pqT] at d1 d2 ⊢
               refine ⟨?_, ?_, ?_⟩ <;>
                 simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3] <;> assumption
             · by_cases e : i = J - 1 - k
               · subst e
                 simp (disch := omega) only [Function.update_of_ne, Function.update_self, a0, a1,
                   a2, h3]
                 omega
               · have := htree i (by omega) i2 i3
                 simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3]
                 exact this
             · unfold pqOut at ha
               simp (disch := omega) only [Function.update_of_ne, a0, a1, a2, h3]
               exact hfr a ha))
  refine ⟨pqClear, hproc, ?_⟩
  dsimp only [pqClear]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop1 ⟨⟨rfl, rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  refine runs_seq_triple_le hloop2 hI (fun st2 hI2 => ?_)
  obtain ⟨-, -, hdone, htree, hfr⟩ := hI2
  refine runs_ret_le (by eval_expr) (fun D' J' A' INF' he hA' => ?_) ?_
  · simp only [List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hfrD : ∀ a, a < D + 4 → st2.mem a = mem a := fun a ha => hfr a (by unfold pqOut; omega)
    refine ⟨⟨by rw [hfrD _ (by omega)]; exact hD, by rw [hfrD _ (by omega)]; exact hA'.symm ▸ rfl,
      by rw [hfrD _ (by omega)]; exact hIc, hJ, fun c hc => ?_, fun c hc => ?_, fun _ _ => rfl,
      fun _ => List.Pairwise.nil, fun _ e he => absurd he (List.not_mem_nil), fun i i1 i2 => ?_,
      fun c hc => ?_⟩, fun c hc => (hdone c hc).2.1, fun a ha => hfr a ha⟩
    · rw [(hdone c hc).1, (hdone c hc).2.1]; omega
    · simp [pqList, (hdone c hc).1, (hdone c hc).2.1]
    · exact htree i (by omega) i1 i2
    · rw [(hdone c hc).2.2]; rfl
  · simp only [pqClearC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

end MinCostFlow.LowStretch
