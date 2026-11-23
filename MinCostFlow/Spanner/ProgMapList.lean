module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.ProgSubgraph

@[expose] public section

/-!
# Renaming a List Through a Table

To embed `W` into `J̃`, each walk of the embedding of `W` into `J` keeps its vertices, and each of
its edges `j` becomes the position of `j` among the kept edges. The positions are in a table built
by `posTableBody`. This file gives the loop that renames a list through such a table: it writes
`mem (T + xs[i])` at `dst + i` for every `i`. The result is `mapList_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Procedure body, at `args = [src, n, T, dst, bound]`. The last argument is used only by the
contract. -/
def mapListBody : Stmt :=
  forRange 5 (.const 0) (.reg 1) (
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .store (.bin .add (.reg 3) (.reg 5)) (.load (.bin .add (.reg 2) (.reg 6)))) ;;
  .ret (.const 0)

/-- The list is at `src`, its entries are below `bound`, and the list and the table
`[T, T + bound)` lie below the output `dst`, which fits in a word with room for `n` cells. -/
def MapListPre (mem : ℕ → ℕ) (src n T dst bound : ℕ) (xs : List ℕ) (w : ℕ) : Prop :=
  ListAt mem src xs ∧ xs.length = n ∧ (∀ x ∈ xs, x < bound) ∧ src + n ≤ dst ∧
    T + bound ≤ dst ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `mapListBody`. -/
def mapListContract (w : ℕ) : Contract where
  pre args mem := ∃ src n T dst bound xs, args = [src, n, T, dst, bound] ∧
    MapListPre mem src n T dst bound xs w
  post args mem _ mem' := ∀ src n T dst bound xs, args = [src, n, T, dst, bound] →
    MapListPre mem src n T dst bound xs w →
    ListAt mem' dst (xs.map fun x => mem (T + x)) ∧ ∀ x, x < dst ∨ dst + n ≤ x → mem' x = mem x
  cost args _ := args.getD 1 0 * 30 + 20

/-- Loop invariant after `i` entries. -/
def MapListInv (mem : ℕ → ℕ) (src n T dst : ℕ) (xs : List ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = T ∧ st.regs 3 = dst ∧ st.regs 5 = i ∧ i ≤ n ∧
    (∀ t (ht : t < i) (htx : t < xs.length), st.mem (dst + t) = mem (T + xs[t])) ∧
    ∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x

lemma mapList_step {w : ℕ} {p : Program} {mem : ℕ → ℕ} {src n T dst bound : ℕ} {xs : List ℕ}
    (hpre : MapListPre mem src n T dst bound xs w) (i : ℕ) (hi : i < n) :
    Triple w p (MapListInv mem src n T dst xs i)
      (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
        .store (.bin .add (.reg 3) (.reg 5)) (.load (.bin .add (.reg 2) (.reg 6))))
      (normalPost fun st₁ =>
        MapListInv mem src n T dst xs (i + 1)
          { st₁ with regs := Function.update st₁.regs 5 (i + 1) } ∧ st₁.regs 5 = i)
      (fun _ => 20) := by
  obtain ⟨hX, hlen, hlt, hsd, hTd, hdw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r5, hin, hdone, hout⟩ := hI
  have hil : i < xs.length := by omega
  set j := xs[i]'hil with hjdef
  have hjb : j < bound := hlt j (List.getElem_mem hil)
  have hxj : st.mem (src + i) = j := by
    rw [hout _ (Or.inl (by omega))]; exact hX.getElem hil
  have e6 : (Expr.load (.bin .add (.reg 0) (.reg 5))).eval w st = some j :=
    ev_load' (ev_add (ev_reg r0 (by omega)) (ev_reg r5 (by omega)) (by omega)) hxj
  let s1 : State := { st with regs := Function.update st.regs 6 j }
  have ea : (Expr.bin .add (.reg 3) (.reg 5)).eval w s1 = some (dst + i) :=
    ev_add (ev_reg (v := dst) (by simp [s1, r3]) (by omega)) (ev_reg (v := i) (by simp [s1, r5])
      (by omega)) (by omega)
  have ev : (Expr.load (.bin .add (.reg 2) (.reg 6))).eval w s1 = some (mem (T + j)) :=
    ev_load' (ev_add (ev_reg (v := T) (by simp [s1, r2]) (by omega))
      (ev_reg (v := j) (by simp [s1]) (by omega)) (by omega))
      (by simp only [s1]; exact hout _ (Or.inl (by omega)))
  refine runs_start_le ?_
  refine runs_seq_assign_le e6 ?_
  refine runs_store_le ea ev ⟨⟨by simp [s1, r0], by simp [s1, r1], by simp [s1, r2],
    by simp [s1, r3], by simp, by omega, ?_, ?_⟩, by simp [s1, r5]⟩
    (by simp only [Expr.size]; omega)
  · intro t ht htx
    simp only [s1]
    by_cases hti : t = i
    · subst hti; rw [← hjdef, Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact hdone t (by omega) htx
  · intro x hx
    simp only [s1]
    rw [Function.update_of_ne (by omega)]
    exact hout x (by omega)

/-- `mapListBody` at `f` meets `mapListContract`. The cost is `30 n + 20`. -/
theorem mapList_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hproc : p.procs[f]? = some mapListBody) :
    MeetsContract w p f (mapListContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨src, n, T, dst, bound, xs, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hX, hlen, hlt, hsd, hTd, hdw, hw1⟩ := hP'
  have hnw : n < 2 ^ w := hwords n (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 5) (lo := .const 0) (hi := .reg 1)
    (P := fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = T ∧ st.regs 3 = dst ∧
      st.mem = mem)
    (Inv := MapListInv mem src n T dst xs) 20 0 n (Nat.zero_le _) hw1 (fun _ => hnw)
    (fun st ⟨q0, q1, q2, q3, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp, Nat.zero_le _,
        fun t ht => absurd ht (Nat.not_lt_zero _), fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.1 hnw)
    (fun i _ hi => mapList_step hP i hi)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, -, hdone, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega)) (fun s' n' T' d' b' xs' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
    have hxx : xs = xs' := List.ext_getElem (hlen.trans h2.2.1.symm) fun t h1 h2' =>
      (hX.getElem h1).symm.trans (h2.1.getElem h2')
    subst hxx
    refine ⟨fun t ht => ?_, hout⟩
    rw [List.length_map] at ht
    rw [List.getElem_map]
    exact hdone t (by omega) ht
  · simp only [Expr.size, mapListContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    omega

end MinCostFlow.Spanner
