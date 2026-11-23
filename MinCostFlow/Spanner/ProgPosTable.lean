module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.ProgSubgraph

@[expose] public section

/-!
# The Position Table of the Kept Edges

The embedding of `W` into `J̃` renames each edge `j` of `J` to its position `kept.idxOf j` in the
list of kept edges. The program reads these positions from a table: `posTableBody` stores `i` at
`T + kept[i]` for every `i`. Since `kept` has no repeats, cell `T + j` then holds `kept.idxOf j`
for every kept edge `j`. The result is `posTable_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Procedure body, at `args = [kAddr, k, T, bound]`. The last argument is used only by the contract. -/
def posTableBody : Stmt :=
  forRange 3 (.const 0) (.reg 1) (
    .assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
    .store (.bin .add (.reg 2) (.reg 4)) (.reg 3)) ;;
  .ret (.const 0)

/-- The kept edges are at `kAddr`, without repeats and below `bound`, and the table
`[T, T + bound)` lies after the list and fits in a word. -/
def PosTablePre (mem : ℕ → ℕ) (kAddr k T bound : ℕ) (kept : List ℕ) (w : ℕ) : Prop :=
  ListAt mem kAddr kept ∧ kept.length = k ∧ kept.Nodup ∧ (∀ j ∈ kept, j < bound) ∧
    kAddr + k ≤ T ∧ T + bound < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `posTableBody`. -/
def posTableContract (w : ℕ) : Contract where
  pre args mem := ∃ kAddr k T bound kept, args = [kAddr, k, T, bound] ∧
    PosTablePre mem kAddr k T bound kept w
  post args mem _ mem' := ∀ kAddr k T bound kept, args = [kAddr, k, T, bound] →
    PosTablePre mem kAddr k T bound kept w →
    (∀ j ∈ kept, mem' (T + j) = kept.idxOf j) ∧ ∀ x, x < T ∨ T + bound ≤ x → mem' x = mem x
  cost args _ := args.getD 1 0 * 30 + 20

/-- Loop invariant after `i` kept edges. -/
def PosInv (mem : ℕ → ℕ) (kAddr k T bound : ℕ) (kept : List ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = kAddr ∧ st.regs 1 = k ∧ st.regs 2 = T ∧ st.regs 3 = i ∧ i ≤ k ∧
    (∀ t (ht : t < i) (htk : t < kept.length), st.mem (T + kept[t]) = t) ∧
    ∀ x, x < T ∨ T + bound ≤ x → st.mem x = mem x

lemma posTable_step {w : ℕ} {p : Program} {mem : ℕ → ℕ} {kAddr k T bound : ℕ} {kept : List ℕ}
    (hpre : PosTablePre mem kAddr k T bound kept w) (i : ℕ) (hi : i < k) :
    Triple w p (PosInv mem kAddr k T bound kept i)
      (.assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
        .store (.bin .add (.reg 2) (.reg 4)) (.reg 3))
      (normalPost fun st₁ =>
        PosInv mem kAddr k T bound kept (i + 1)
          { st₁ with regs := Function.update st₁.regs 3 (i + 1) } ∧ st₁.regs 3 = i)
      (fun _ => 20) := by
  obtain ⟨hK, hlen, hnd, hlt, hKT, hTw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, hik, hdone, hout⟩ := hI
  have hil : i < kept.length := by omega
  set j := kept[i]'hil with hjdef
  have hjb : j < bound := hlt j (List.getElem_mem hil)
  have hkj : st.mem (kAddr + i) = j := by
    rw [hout _ (Or.inl (by omega))]; exact hK.getElem hil
  have e4 : (Expr.load (.bin .add (.reg 0) (.reg 3))).eval w st = some j :=
    ev_load' (ev_add (ev_reg r0 (by omega)) (ev_reg r3 (by omega)) (by omega)) hkj
  let s1 : State := { st with regs := Function.update st.regs 4 j }
  have ea : (Expr.bin .add (.reg 2) (.reg 4)).eval w s1 = some (T + j) :=
    ev_add (ev_reg (v := T) (by simp [s1, r2]) (by omega)) (ev_reg (v := j) (by simp [s1])
      (by omega)) (by omega)
  have ev : (Expr.reg 3).eval w s1 = some i := ev_reg (v := i) (by simp [s1, r3]) (by omega)
  refine runs_start_le ?_
  refine runs_seq_assign_le e4 ?_
  refine runs_store_le ea ev ⟨⟨by simp [s1, r0], by simp [s1, r1], by simp [s1, r2], by simp,
    by omega, ?_, ?_⟩, by simp [s1, r3]⟩ (by simp only [Expr.size]; omega)
  · intro t ht htk
    simp only [s1]
    by_cases hti : t = i
    · subst hti; rw [← hjdef, Function.update_self]
    · have hne : kept[t] ≠ j := fun h => hti ((hnd.getElem_inj_iff).mp h)
      rw [Function.update_of_ne (by omega)]
      exact hdone t (by omega) htk
  · intro x hx
    simp only [s1]
    rw [Function.update_of_ne (by omega)]
    exact hout x hx

/-- `posTableBody` at `f` meets `posTableContract`. The cost is `30 k + 20`. -/
theorem posTable_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hproc : p.procs[f]? = some posTableBody) :
    MeetsContract w p f (posTableContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨kAddr, k, T, bound, kept, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hK, hlen, hnd, hlt, hKT, hTw, hw1⟩ := hP'
  have hkw : k < 2 ^ w := hwords k (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 3) (lo := .const 0) (hi := .reg 1)
    (P := fun st => st.regs 0 = kAddr ∧ st.regs 1 = k ∧ st.regs 2 = T ∧ st.mem = mem)
    (Inv := PosInv mem kAddr k T bound kept) 20 0 k (Nat.zero_le _) hw1 (fun _ => hkw)
    (fun st ⟨q0, q1, q2, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp, Nat.zero_le _,
        fun t ht => absurd ht (Nat.not_lt_zero _), fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.1 hkw)
    (fun i _ hi => posTable_step hP i hi)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, hdone, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega)) (fun kA' k' T' b' kept' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    have hkk : kept = kept' := List.ext_getElem (hlen.trans h2.2.1.symm) fun t h1 h2' =>
      (hK.getElem h1).symm.trans (h2.1.getElem h2')
    subst hkk
    refine ⟨fun j hj => ?_, hout⟩
    obtain ⟨t, htk, rfl⟩ := List.getElem_of_mem hj
    rw [hdone t (by omega) htk, hnd.idxOf_getElem]
  · simp only [Expr.size, posTableContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    omega

end MinCostFlow.Spanner
