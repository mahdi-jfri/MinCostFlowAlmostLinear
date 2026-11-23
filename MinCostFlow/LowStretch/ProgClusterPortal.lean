module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The portal of a petal

After a petal search, the pointer cell holds the first highway node `H[j]` that is not settled.
The portal pair leaves the petal from `H[j - 1]`. `portP` finds `H[j - 1]` by walking the array
`NXT` from the target until the next node is the pointer. In general (`portC`): from `src`, it
returns the first node `x` of the walk along `NXT` with `NXT[x] = ptr`. The cost is linear in the
number of steps.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- Node number `k` of the walk along `NXT` from `src`. -/
def pIt (mem : ℕ → ℕ) (NXT src k : ℕ) : ℕ := (fun y => mem (NXT + y))^[k] src

/-- Node number `k` is the first node of the walk whose next node is `ptr`. -/
def PortOk (mem : ℕ → ℕ) (NXT src ptr k : ℕ) : Prop :=
  mem (NXT + pIt mem NXT src k) = ptr ∧ ∀ k' < k, mem (NXT + pIt mem NXT src k') ≠ ptr

theorem PortOk.unique {mem : ℕ → ℕ} {NXT src ptr k k' : ℕ} (h : PortOk mem NXT src ptr k)
    (h' : PortOk mem NXT src ptr k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with e | e | e
  · exact absurd h.1 (h'.2 k e)
  · exact e
  · exact absurd h'.1 (h.2 k' e)

theorem pIt_succ (mem : ℕ → ℕ) (NXT src k : ℕ) :
    pIt mem NXT src (k + 1) = mem (NXT + pIt mem NXT src k) := by
  unfold pIt; rw [Function.iterate_succ_apply']

/-- The number of steps, when the walk meets the pointer. -/
noncomputable def portK (mem : ℕ → ℕ) (NXT src ptr : ℕ) : ℕ :=
  sInf {k | PortOk mem NXT src ptr k}

theorem PortOk.portK_eq {mem : ℕ → ℕ} {NXT src ptr k : ℕ} (h : PortOk mem NXT src ptr k) :
    portK mem NXT src ptr = k :=
  (Nat.sInf_mem (s := {k | PortOk mem NXT src ptr k}) ⟨k, h⟩).unique h

/-- The fewest steps left from the node in register `1`. -/
noncomputable def portRem (mem : ℕ → ℕ) (NXT src k : ℕ) (st : State) : ℕ :=
  sInf {r | ∃ i, i + r = k ∧ st.regs 1 = pIt mem NXT src i}

/-- `portP` with `args = [NXT, src, ptr]`. -/
def portP : Stmt :=
  .seq (.loop (.bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 0) (.reg 1))) (.reg 2)))
    (.assign 1 (.load (.bin .add (.reg 0) (.reg 1)))))
  (.ret (.reg 1))

theorem portP_noRand : portP.NoRand := by simp [portP, Stmt.NoRand]

/-- The contract of `portP`. -/
noncomputable def portC (w : ℕ) : Contract where
  pre args mem := ∃ NXT src ptr k, args = [NXT, src, ptr] ∧ PortOk mem NXT src ptr k ∧ 1 < 2 ^ w ∧
    ∀ k' ≤ k, NXT + pIt mem NXT src k' < 2 ^ w ∧ pIt mem NXT src (k' + 1) < 2 ^ w
  post args mem v mem' := mem' = mem ∧ ∀ NXT src ptr k, args = [NXT, src, ptr] →
    PortOk mem NXT src ptr k → v = pIt mem NXT src k
  cost args mem := 20 * (portK mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) + 1)

theorem portP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [portP]) :
    MeetsContract w p b (portC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨NXT, src, ptr, k, rfl, hk, hw1, hw⟩ := hpre
  have hproc : p.procs[b]? = some portP := hp 0 (by simp)
  clear hp
  have hw0 : NXT < 2 ^ w := hwords _ (by simp)
  have hw2 : ptr < 2 ^ w := hwords _ (by simp)
  let rem : State → ℕ := portRem mem NXT src k
  let I : State → Prop := fun st => st.regs 0 = NXT ∧ st.regs 2 = ptr ∧ st.mem = mem ∧
    ∃ i ≤ k, st.regs 1 = pIt mem NXT src i
  have hrem : ∀ st, I st → rem st ≤ k ∧ ∃ i, i + rem st = k ∧ st.regs 1 = pIt mem NXT src i := by
    intro st ⟨_, _, _, i, hi, h1⟩
    show portRem mem NXT src k st ≤ k ∧ ∃ i, i + portRem mem NXT src k st = k ∧ _
    unfold portRem
    have hne : {r | ∃ i, i + r = k ∧ st.regs 1 = pIt mem NXT src i}.Nonempty :=
      ⟨k - i, i, by omega, h1⟩
    have := Nat.sInf_mem hne
    obtain ⟨i0, e0, e1⟩ := this
    exact ⟨by omega, i0, e0, e1⟩
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 0) (.reg 1))) (.reg 2)))
    (body := .assign 1 (.load (.bin .add (.reg 0) (.reg 1)))) (Inv := I)
    (Q := fun st => st.mem = mem ∧ st.regs 1 = pIt mem NXT src k)
    rem (fun st => 1 - (if st.mem (NXT + st.regs 1) = ptr then 1 else 0)) 10
    (fun st hI => by
      obtain ⟨h0, h2, hm, i, hi, h1⟩ := hI
      have a1 : st.regs 0 + st.regs 1 < 2 ^ w := by rw [h0, h1]; exact (hw i hi).1
      have a2 : st.mem (st.regs 0 + st.regs 1) < 2 ^ w := by
        rw [h0, h1, hm, ← pIt_succ mem NXT src i]; exact (hw i hi).2
      have a3 : st.regs 2 < 2 ^ w := by rw [h2]; exact hw2
      eval_expr
      all_goals simp [Expr.MemAt, h1])
    (fun st hI hv => by
      obtain ⟨-, i0, e0, e1⟩ := hrem st hI
      obtain ⟨-, -, hm, -⟩ := hI
      have hp : st.mem (NXT + st.regs 1) = ptr := by
        by_contra hne; simp [hne] at hv
      rw [hm, e1] at hp
      refine ⟨hm, ?_⟩
      rw [e1]
      rcases Nat.lt_or_ge i0 k with hlt | hge
      · exact absurd hp (hk.2 i0 hlt)
      · rw [show i0 = k by omega])
    (fun st hI hv => by
      obtain ⟨-, i0, e0, e1⟩ := hrem st hI
      obtain ⟨h0, h2, hm, -⟩ := hI
      have hne : st.mem (NXT + st.regs 1) ≠ ptr := by
        intro e; simp [e] at hv
      rw [hm, e1] at hne
      have hi0 : i0 < k := by
        rcases Nat.lt_or_ge i0 k with h | h
        · exact h
        · exfalso; rw [show i0 = k by omega] at hne; exact hne hk.1
      intro st' ω' hst
      rw [hst]
      have a1 : st.regs 0 + st.regs 1 < 2 ^ w := by rw [h0, e1]; exact (hw i0 hi0.le).1
      refine runs_start_le ?_
      wram_run
      · have hnew : st.mem (NXT + pIt mem NXT src i0) = pIt mem NXT src (i0 + 1) := by
          rw [hm, pIt_succ]
        refine ⟨⟨by simp [h0], by simp [h2], by simp [hm], i0 + 1, by omega, by simp [hnew]⟩, ?_⟩
        have hle : rem { st with regs := Function.update st.regs 1 (st.mem (NXT + pIt mem NXT src i0)) }
            ≤ k - (i0 + 1) := Nat.sInf_le ⟨i0 + 1, by omega, by simp [hnew]⟩
        show _ < portRem mem NXT src k st
        have : rem st = portRem mem NXT src k st := rfl
        omega
      · wram_cost)
  refine ⟨portP, hproc, ?_⟩
  dsimp only [portP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl⟩ (fun st hQ => ?_)
  obtain ⟨hm, h1⟩ := hQ
  refine runs_ret_le (by eval_expr) ⟨hm, fun NXT' src' ptr' k' he hk' => ?_⟩ ?_
  · simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    rw [← hk.unique hk']; rfl
  · have hr0 : rem (startState [NXT, src, ptr] mem pos) ≤ k :=
      (hrem _ ⟨rfl, rfl, rfl, 0, Nat.zero_le _, rfl⟩).1
    simp only [portC, List.getD_cons_zero, List.getD_cons_succ, Expr.size, hk.portK_eq]
    nlinarith

end MinCostFlow.LowStretch
