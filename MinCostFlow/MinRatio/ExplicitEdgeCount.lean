module

public import MinCostFlow.MinRatio.ExplicitEdgeLayout
public import WordRAM.Logic
public import MinCostFlow.Num.SignedPair
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic

/-!
# Counting explicit cycle traversals

Algorithm 2 (page 29) applies the net normalized increment to each
explicit edge. This loop counts occurrences of a designated name and
direction in the packed route. It reads the route in place and uses
one counter and one accumulator register.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

@[expose] def explicitEdgeDirectionWord (dir : Bool) : ℕ := if dir then 1 else 0

/-- Registers 0 through 3 hold the base, length, name, and direction.
Register 4 indexes the route and register 5 holds the count. -/
@[expose] def explicitEdgeCountStep : Stmt :=
  .assign 5 (.bin .add (.reg 5) (.bin .and
    (.bin .eq (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))) (.reg 2))
    (.bin .eq (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))
      (.const 1))) (.reg 3))))

@[expose] def explicitEdgeCountInv (mem : ℕ → ℕ) (base e : ℕ) (dir : Bool)
    (edges : List (ℕ × Bool)) (i : ℕ) (st : State) : Prop :=
  st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = edges.length ∧ st.regs 2 = e ∧
    st.regs 3 = explicitEdgeDirectionWord dir ∧ st.regs 4 = i ∧ st.regs 5 = (edges.take i).count (e, dir)

/-- Scanning the route counts exactly the specified directional
traversals, preserves memory, and uses at most `34 * length + 4` steps. -/
theorem explicitEdgeCount_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ}
    {base e : ℕ} {dir : Bool} {edges : List (ℕ × Bool)}
    (hr : ExplicitEdgesAt mem base edges) (hbound : base + 2 * edges.length + 2 < 2 ^ w)
    :
    Triple w p (explicitEdgeCountInv mem base e dir edges 0)
      (forUp 4 (.reg 1) explicitEdgeCountStep)
      (normalPost (explicitEdgeCountInv mem base e dir edges edges.length))
      (fun _ => 34 * edges.length + 4) := by
  refine
    (Triple.forUp_const (Inv := explicitEdgeCountInv mem base e dir edges) 25 0 edges.length
      (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun _ _ _ _ h => h.2.2.2.2.2.1)
      (fun _ st _ _ h => by simp [Expr.eval, h.2.2.1]) ?_).mono_cost ?_
  · intro i _ hi st ω hin
    obtain ⟨hm, hb, hl, hname, hd, hiReg, hcount⟩ := hin
    have hbase : base < 2 ^ w := by omega
    have htwo : 2 < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    have hmul : 2 * i < 2 ^ w := by omega
    have haddr : base + 2 * i < 2 ^ w := by omega
    have hdiraddr : base + 2 * i + 1 < 2 ^ w := by omega
    let next := (edges.take (i + 1)).count (e, dir)
    have hnext : next < 2 ^ w := by
      have := List.count_le_length (l := edges.take (i + 1)) (a := (e, dir))
      rw [List.length_take] at this
      have := Nat.min_le_right (i + 1) edges.length
      omega
    have hstep := hr.count_step hi e dir
    have hev : (match explicitEdgeCountStep with
        | .assign _ ex => ex.eval w st
        | _ => none) = some next := by
      change (match explicitEdgeCountStep with | .assign _ ex => ex.eval w st | _ => none) = _
      have hbStep : next = _ := hstep
      have hwadd : (edges.take i).count (e, dir) +
          (if mem (base + 2 * i) = e ∧
              mem (base + 2 * i + 1) = explicitEdgeDirectionWord dir then 1 else 0) < 2 ^ w := by
        unfold explicitEdgeDirectionWord
        rw [← hstep]
        exact hnext
      rw [hbStep]
      by_cases hn : mem (base + 2 * i) = e <;>
        by_cases hdir : mem (base + 2 * i + 1) = explicitEdgeDirectionWord dir <;>
          simp only [hn, hdir, true_and, false_and, and_false, ite_true, ite_false] at hwadd ⊢ <;>
          unfold explicitEdgeDirectionWord at hdir <;>
          simp [explicitEdgeCountStep, Expr.eval, hb, hm, hiReg, hname, hd, hcount,
            htwo, hone, hmul, haddr, hdiraddr, hn, hdir, hwadd, explicitEdgeDirectionWord] at ⊢ <;> omega
    apply runs_start_le
    unfold explicitEdgeCountStep at hev ⊢
    refine runs_assign_le hev ?_ (by simp [Expr.size])
    simp [normalPost, explicitEdgeCountInv, hm, hb, hl, hname, hd, hiReg, next,
      Function.update_of_ne]
  · intro st _
    simp [Expr.size]
    omega

/-- Return the count of one direction of an explicit edge. -/
@[expose] def explicitEdgeCountBody : Stmt :=
  .assign 4 (.const 0) ;;
  .assign 5 (.const 0) ;;
  forUp 4 (.reg 1) explicitEdgeCountStep ;;
  .ret (.reg 5)

/-- The four arguments give the packed route address, length, name, and direction. -/
@[expose] def explicitEdgeCountContract (w : ℕ) (edges : List (ℕ × Bool))
    (e : ℕ) (dir : Bool) : Contract where
  pre args mem := ∃ base, args = [base, edges.length, e, explicitEdgeDirectionWord dir] ∧
    ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length + 2 < 2 ^ w
  post _ mem ret mem' := ret = edges.count (e, dir) ∧ mem' = mem
  cost _ _ := 34 * edges.length + 13

/-- The scan has no randomized statements. -/
theorem explicitEdgeCountBody_noRand : explicitEdgeCountBody.NoRand := by
  simp [explicitEdgeCountBody, forUp, explicitEdgeCountStep, Stmt.NoRand]

/-- The counting procedure returns the directional multiplicity with no memory writes. -/
theorem explicitEdgeCount_meetsContract {w entry : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (e : ℕ) (dir : Bool)
    (hp : p.HasAt entry [explicitEdgeCountBody]) :
    MeetsContract w p entry (explicitEdgeCountContract w edges e dir) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, rfl, hr, hb⟩ := hpre
  have hz : 0 < 2 ^ w := Nat.two_pow_pos w
  apply runs_start_le
  unfold explicitEdgeCountBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le (explicitEdgeCount_loop (e := e) (dir := dir) hr hb) ?_ ?_
  · simp [explicitEdgeCountInv, startState, Function.update_of_ne]
  · intro st hs
    obtain ⟨hm, _, _, _, _, _, hc⟩ := hs
    rw [List.take_length] at hc
    refine runs_ret_le (v := edges.count (e, dir)) (by simp [Expr.eval, hc]) ?_ ?_
    · exact ⟨rfl, hm⟩
    · simp [explicitEdgeCountContract, Expr.size]
      omega

/-- Comparing the two directional counts gives the sign and lets
word subtraction compute the magnitude without underflow. -/
theorem encodeInt_of_directional_counts (forward backward : ℕ) :
    encodeSignedPair ((forward : ℤ) - (backward : ℤ)) =
      if forward < backward then [1, backward - forward] else [0, forward - backward] := by
  by_cases hf : forward < backward
  · have hs : (forward : ℤ) - (backward : ℤ) < 0 := by omega
    have hm : ((forward : ℤ) - (backward : ℤ)).natAbs = backward - forward := by omega
    simp [encodeSignedPair, hf, hs, hm]
  · have hs : ¬ (forward : ℤ) - (backward : ℤ) < 0 := by omega
    have hm : ((forward : ℤ) - (backward : ℤ)).natAbs = forward - backward := by omega
    simp [encodeSignedPair, hf, hs, hm]

end MinCostFlow.MinRatio
