module

public import MinCostFlow.LowStretch.ProgBodyNodeTail
public import MinCostFlow.LowStretch.ProgBodyNodeOwed
public import MinCostFlow.LowStretch.ProgBodyNodeFit

/-!
# Tools for the run of the node part

The run of the node part is built forward: each piece gives its final state before the next piece
runs. This file has the forward forms of a sequence, of the loads `ldR` (`ldR_fwd`), the places
of the block registers (`blkRegs_lt`, `blkRegs_hi`), the bound `Φ ≤ A` of the potential of the
petal searches (`PW.Ok.Φ_le_A`), and the room for the heap of the setup (`node_room`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- A sequence, forward. -/
theorem run_seq {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ st' : State}
    {o : Outcome} {c₁ c₂ : ℕ} (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st' c₂) : Runs w p ω (.seq s₁ s₂) st o st' (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

/-- An assignment, forward. -/
theorem run_assign {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {st : State} {v : ℕ}
    (he : e.eval w st = some v) :
    Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v }
      (e.size + 1) :=
  runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

/-- **The loads, forward.** There are registers `regs'` with the loaded values such that every
run of `s` from them gives a run of `ldR b rs i s`, at most `6` steps per load more. -/
theorem ldR_fwd {w : ℕ} {p : Program} {ω : ℕ → Bool} {b c : ℕ} :
    ∀ (rs : List ℕ) (i : ℕ) (st : State), st.regs b = c → b ∉ rs → rs.Nodup →
      c + i + rs.length < 2 ^ w →
      ∃ regs' : ℕ → ℕ, (∀ j (hj : j < rs.length), regs' rs[j] = st.mem (c + i + j)) ∧
        (∀ r, r ∉ rs → regs' r = st.regs r) ∧
        ∀ (s : Stmt) (o : Outcome) (st' : State) (c' : ℕ),
          Runs w p ω s { st with regs := regs' } o st' c' →
          ∃ c'', Runs w p ω (ldR b rs i s) st o st' c'' ∧ c'' ≤ c' + 6 * rs.length := by
  intro rs
  induction rs with
  | nil =>
    intro i st _ _ _ _
    exact ⟨st.regs, fun j hj => by simp at hj, fun _ _ => rfl, fun s o st' c' h =>
      ⟨c', h, by simp⟩⟩
  | cons r rs ih =>
    intro i st hb hbr hnd hlt
    have hci : c + i < 2 ^ w := by simp at hlt; omega
    have hi : i < 2 ^ w := by omega
    have hbr' : b ≠ r := fun e => hbr (e ▸ List.mem_cons_self)
    have hbrs : b ∉ rs := fun h => hbr (List.mem_cons_of_mem _ h)
    have hrn : r ∉ rs := (List.nodup_cons.mp hnd).1
    set st1 : State := { st with regs := Function.update st.regs r (st.mem (c + i)) } with hst1
    obtain ⟨regs', hm, hf, hrun⟩ := ih (i + 1) st1
      (by simp only [hst1]; rw [Function.update_of_ne hbr']; exact hb) hbrs
      (List.nodup_cons.mp hnd).2 (by simp at hlt; omega)
    have he : (Expr.load (.bin .add (.reg b) (.const i))).eval w st = some (st.mem (c + i)) :=
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hb) (Expr.eval_const hi) hci)
    refine ⟨regs', fun j hj => ?_, fun y hy => ?_, fun s o st' c' h => ?_⟩
    · rcases j with _ | j
      · simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf r hrn]
        simp [hst1]
      · have := hm j (by simpa using hj)
        simp only [List.getElem_cons_succ]
        rw [show c + i + (j + 1) = c + (i + 1) + j by omega, this]
    · have hyr : y ≠ r := fun e => hy (e ▸ List.mem_cons_self)
      rw [hf y (fun h => hy (List.mem_cons_of_mem _ h))]
      simp only [hst1]
      rw [Function.update_of_ne hyr]
    · obtain ⟨c'', hr, hc⟩ := hrun s o st' c' h
      refine ⟨_, run_seq (run_assign he) hr, ?_⟩
      simp only [Expr.size, List.length_cons] at hc ⊢
      omega

theorem blkRegs_nodup : blkRegs.Nodup := by decide

theorem blkRegs_length : blkRegs.length = 51 := by decide

theorem blkRegs_lt {i : ℕ} (hi : i < 43) : blkRegs[i]'(by rw [blkRegs_length]; omega) = i := by
  interval_cases i <;> rfl

theorem blkRegs_hi {j : ℕ} (hj : j < 8) :
    blkRegs[43 + j]'(by rw [blkRegs_length]; omega) = 50 + j := by
  interval_cases j <;> rfl

theorem not_mem_blkRegs {r : ℕ} (h1 : 43 ≤ r) (h2 : r < 50 ∨ 58 ≤ r) : r ∉ blkRegs := by
  simp only [blkRegs, List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem PW.LReg_length (W : PW) (A : PW.TA) (Q : PW.LA) (Δ : ℕ) : (W.LReg A Q Δ).length = 43 := by
  simp [PW.LReg]

theorem setupBlock_lt {W : PW} {A : PW.TA} {Q : PW.LA} {i : ℕ} (hi : i < 43) :
    (setupBlock W A Q).getD i 0 = (W.LReg A Q (W.c.Δ W.G)).getD i 0 := by
  unfold setupBlock
  rw [List.getD_eq_getElem _ _ (by simp [PW.LReg_length]; omega),
    List.getD_eq_getElem _ _ (by simp [PW.LReg_length]; omega),
    List.getElem_append_left (by simp [PW.LReg_length]; omega)]

theorem setupBlock_hi {W : PW} {A : PW.TA} {Q : PW.LA} (j : ℕ) :
    (setupBlock W A Q).getD (43 + j) 0 = [W.c.loS W.G, W.sv W.c.t, W.c.t,
      if 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t then 1 else 0].getD j 0 := by
  unfold setupBlock
  rw [List.getD_append_right _ _ _ _ (by simp [PW.LReg_length])]
  simp [PW.LReg_length]

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ}

/-- **The potential is at most the capacity of the queues**: each allowed node is below `s` and
its degree plus one is counted in the budget of the arcs. -/
theorem Ok.Φ_le_A (h : W.Ok w mem) : W.Φ mem ≤ W.L.A := by
  have hNN := h.hNN
  have hsub : W.Nodes mem ⊆ Finset.range W.s := fun u hu => by
    simp only [Nodes, Finset.mem_filter, Finset.mem_range] at hu ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp (hNN ▸ hu.1) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hu.2) h.sS
  refine le_trans ?_ h.budget
  unfold Φ
  refine le_trans (Finset.sum_le_sum_of_subset hsub) (Finset.sum_le_sum fun u hu => ?_)
  have hu := Finset.mem_range.mp hu
  simp [DL.deg, DL.g, show u < W.L.NN by omega]

end PW

/-- **The heap of the setup and the petal block fit in the room of the cluster.** -/
theorem node_room {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {h hS J : ℕ}
    (hA : 20000 ≤ A) (hL1 : 1 ≤ P.L) (hS1 : 1 ≤ R.S.length)
    (hs : R.nodes.length ≤ R.S.length + 1)
    (hhS : hS ≤ h + 1000 * (J + 1) * (R.S.length + R.nodes.length + P.L + 10)) :
    hS + 16 ≤ h + (J + 2) * recCost w A T G P c R := by
  have h1 : A * P.L * R.S.length ≤ recCost w A T G P c R := by
    unfold recCost recMain
    have := Nat.mul_le_mul_left (A * P.L) (show R.S.length ≤ 2 * T.hidW G c + R.S.length by omega)
    omega
  have e1 : A * P.L * R.S.length = A * (P.L * R.S.length) := by ring
  have h4 : 20000 * (P.L * R.S.length) ≤ A * (P.L * R.S.length) := Nat.mul_le_mul_right _ hA
  have f1 : R.S.length ≤ P.L * R.S.length := Nat.le_mul_of_pos_left _ (by omega)
  have f2 : P.L ≤ P.L * R.S.length := Nat.le_mul_of_pos_right _ (by omega)
  have f3 : 1 ≤ P.L * R.S.length := Nat.mul_pos (by omega) (by omega)
  have h5 : 1000 * (R.S.length + R.nodes.length + P.L + 10) + 16 ≤ recCost w A T G P c R := by
    omega
  have h6 := Nat.mul_le_mul_left (J + 2) h5
  have e : (J + 2) * (1000 * (R.S.length + R.nodes.length + P.L + 10) + 16) =
      1000 * (J + 1) * (R.S.length + R.nodes.length + P.L + 10) +
        (1000 * (R.S.length + R.nodes.length + P.L + 10) + 16 * (J + 2)) := by ring
  omega

end MinCostFlow.LowStretch
