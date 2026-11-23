module

public import MinCostFlow.LowStretch.ProgBodyKids
public import MinCostFlow.LowStretch.ProgClusterSetupSpec
public import MinCostFlow.LowStretch.ProgChildOneB
public import MinCostFlow.HierPaths.DelProgRegFrame

/-!
# The node part of the body: the procedure

The node part runs on a cluster with at least two super-vertices. It keeps its arguments
`GB, RB, h` in registers `60, 61, 62` and then
1. calls the setup, which leaves a block of `51` words at `h` (`SetupOut`);
2. loads the block into registers (`ldR`): the registers `0 … 42` of the petal loop, then
   `50, 51, 52` for the special petal, the flag of the special petal in `53`, the addresses `PF`,
   `PB`, `ACT` in `54, 55, 56`, and the end `hS` of the heap of the setup in `57`;
3. sets the stamp (register `13`) to `1`, runs the special petal when the flag is `1`, and calls
   the loop of the regular petals, which returns the number of petals into register `58`;
4. writes the center `CC[0] = x0` and the target `CT[0]` of child `0`: the target of the
   cluster, or, with a special petal, the other end of the special portal `PT[0]` seen from the
   center `CC[1]` of the special petal;
5. writes the petal block of `16` words at `hS` (`stR`) and calls the child step at `hS + 16`;
6. writes the four words of `wr4` at `h` and returns.

The setup and the loop write only the registers below `48`, so the registers from `50` on keep
their values across them (`runs_regs_frame`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### Loading registers -/

/-- Load `r_b + i + j` into register `rs[j]`, then run `s`. -/
def ldR (b : ℕ) : List ℕ → ℕ → Stmt → Stmt
  | [], _, s => s
  | r :: rs, i, s => .seq (.assign r (.load (.bin .add (.reg b) (.const i)))) (ldR b rs (i + 1) s)

theorem ldR_noRand (b : ℕ) (s : Stmt) (hs : s.NoRand) :
    ∀ (rs : List ℕ) (i : ℕ), (ldR b rs i s).NoRand
  | [], _ => hs
  | _ :: rs, i => by
    simp only [ldR, Stmt.NoRand, true_and]
    exact ldR_noRand b s hs rs (i + 1)

/-- **What `ldR` leaves.** With `r_b = c`, `b` not among the distinct registers `rs` and
`c + i + |rs| < 2^w`, the continuation `s` runs with register `rs[j]` holding `mem (c + i + j)`
and the other registers unchanged. Each load costs at most `6` steps. -/
theorem runs_ldR {w : ℕ} {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → Prop}
    {s : Stmt} {b c : ℕ} :
    ∀ (rs : List ℕ) (i : ℕ) (st : State) (k T : ℕ), st.regs b = c → b ∉ rs → rs.Nodup →
      c + i + rs.length < 2 ^ w →
      (∀ regs' : ℕ → ℕ, (∀ j (hj : j < rs.length), regs' rs[j] = st.mem (c + i + j)) →
        (∀ r, r ∉ rs → regs' r = st.regs r) →
        ∃ o st' c', Runs w p ω s { st with regs := regs' } o st' c' ∧ Q o st' ∧
          k + 6 * rs.length + c' ≤ T) →
      ∃ o st' c', Runs w p ω (ldR b rs i s) st o st' c' ∧ Q o st' ∧ k + c' ≤ T := by
  intro rs
  induction rs with
  | nil =>
    intro i st k T _ _ _ _ hs
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs st.regs (fun j hj => by simp at hj) (fun _ _ => rfl)
    exact ⟨o, st', c', hr, hq, by simpa using hc⟩
  | cons r rs ih =>
    intro i st k T hb hbr hnd hlt hs
    have hci : c + i < 2 ^ w := by simp at hlt; omega
    have hi : i < 2 ^ w := by omega
    have hbr' : b ≠ r := fun e => hbr (e ▸ List.mem_cons_self)
    have hbrs : b ∉ rs := fun h => hbr (List.mem_cons_of_mem _ h)
    have hrn : r ∉ rs := (List.nodup_cons.mp hnd).1
    unfold ldR
    refine runs_seq_assign_le (v := st.mem (c + i))
      (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hb) (Expr.eval_const hi) hci)) ?_
    refine ih (i + 1) { st with regs := Function.update st.regs r (st.mem (c + i)) } _ T
      (by simp only; rw [Function.update_of_ne hbr']; exact hb) hbrs (List.nodup_cons.mp hnd).2
      (by simp at hlt; omega) ?_
    intro regs' hm hf
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs regs' (fun j hj => by
        rcases j with _ | j
        · simp only [List.getElem_cons_zero, Nat.add_zero]
          rw [hf r hrn]
          simp
        · have := hm j (by simpa using hj)
          simp only [List.getElem_cons_succ]
          rw [show c + i + (j + 1) = c + (i + 1) + j by omega, this])
      (fun y hy => by
        have hyr : y ≠ r := fun e => hy (e ▸ List.mem_cons_self)
        rw [hf y (fun h => hy (List.mem_cons_of_mem _ h))]
        simp only
        rw [Function.update_of_ne hyr])
    refine ⟨o, st', c', hr, hq, ?_⟩
    simp only [Expr.size, List.length_cons] at hc ⊢
    omega

/-! ### The register frame -/

/-- A run of a statement that writes only registers below `n` keeps the registers from `n` on. -/
theorem runs_regs_frame {w : ℕ} {p : Program} {ω : ℕ → Bool} {n : ℕ} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ} (hs : HierPaths.Stmt.WritesBelow n s)
    (hr : Runs w p ω s st o st' c) : ∀ r, n ≤ r → st'.regs r = st.regs r := by
  obtain ⟨fuel, h⟩ := hr
  exact HierPaths.exec_regs_of_writesBelow fuel s st hs h

theorem spPet_writesBelow (bP bC : ℕ) : HierPaths.Stmt.WritesBelow 48 (spPet bP bC) := by
  simp [spPet, regPet, HierPaths.Stmt.WritesBelow]

/-! ### The procedure -/

/-- The registers that receive the block of the setup, in order. -/
def blkRegs : List ℕ := List.range 43 ++ [50, 51, 52, 53, 54, 55, 56, 57]

/-- The registers that hold the petal block, in order (`PetL`). -/
def petRegs : List ℕ := [58, 53, 33, 34, 9, 10, 35, 36, 28, 38, 54, 39, 55, 22, 56, 42]

/-- The target of child `0`: the target `c.t` of the cluster (register `52`), or, with a special
petal (flag in register `53`), the other end of the special portal. Register `59` gets the
address `IN + 3 PT[0]` of the ends of the portal; the end that is not the center `CC[1]` of the
special petal is the target. -/
def ct0 : Stmt :=
  .cond (.reg 53)
    (.seq (.assign 59 (.bin .add (.load (.bin .add (.reg 60) (.const 3)))
        (.bin .mul (.const 3) (.load (.reg 37)))))
      (.cond (.bin .eq (.load (.reg 59)) (.load (.bin .add (.reg 36) (.const 1))))
        (.store (.reg 35) (.load (.bin .add (.reg 59) (.const 1))))
        (.store (.reg 35) (.load (.reg 59)))))
    (.store (.reg 35) (.reg 52))

/-- The end of the node part: the call of the child step at `hS + 16` (register `63`) with the
petal block at `hS`, the four words of `wr4` at `h`, and the return. -/
def nodeEnd (bK : ℕ) : Stmt :=
  .seq (.assign 63 (.bin .add (.reg 57) (.const 16)))
  (.seq (.call 59 bK [.reg 60, .reg 61, .reg 57, .reg 63])
  (.seq (.store (.reg 62) (.bin .add (.reg 58) (.const 1)))
  (.seq (.store (.bin .add (.reg 62) (.const 1)) (.reg 63))
  (.seq (.store (.bin .add (.reg 62) (.const 2)) (.reg 59))
  (.seq (.store (.bin .add (.reg 62) (.const 3)) (.reg 37))
    (.ret (.const 0)))))))

/-- The middle of the node part, after the block is loaded: the stamp, the special petal, the
loop of the regular petals (procedure `bR`), `CC[0]`, `CT[0]`, the petal block, and the end. -/
def nodeMid (bP bC bR bK : ℕ) : Stmt :=
  .seq (.assign 13 (.const 1))
  (.seq (.cond (.reg 53) (spPet bP bC) .nop)
  (.seq (.call 58 bR (rgs (List.range 43)))
  (.seq (.store (.reg 36) (.load (.bin .add (.reg 61) (.const 5))))
  (.seq ct0
    (stR 57 petRegs 0 (nodeEnd bK))))))

/-- **The node part**, called with `[GB, RB, h]`: the setup (procedure `bS`), the petals
(`bP`, `bC` for `spPet`, `bR` for the loop) and the child step (`bK`). -/
def nodeP (bS bP bC bR bK : ℕ) : Stmt :=
  .seq (.assign 60 (.reg 0))
  (.seq (.assign 61 (.reg 1))
  (.seq (.assign 62 (.reg 2))
  (.seq (.call 59 bS [.reg 60, .reg 61, .reg 62])
    (ldR 62 blkRegs 0 (nodeMid bP bC bR bK)))))

theorem nodeP_noRand (bS bP bC bR bK : ℕ) : (nodeP bS bP bC bR bK).NoRand := by
  simp only [nodeP, Stmt.NoRand, true_and]
  refine ldR_noRand _ _ ?_ _ _
  simp only [nodeMid, Stmt.NoRand, true_and]
  refine ⟨⟨spPet_noRand bP bC, trivial⟩, ?_, ?_⟩
  · simp [ct0, Stmt.NoRand]
  · exact stR_noRand _ _ (by simp [nodeEnd, Stmt.NoRand]) _ _

end MinCostFlow.LowStretch
