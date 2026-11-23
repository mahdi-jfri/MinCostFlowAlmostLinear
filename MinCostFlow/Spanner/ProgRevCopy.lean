module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.ProgSubgraph

@[expose] public section

/-!
# Copying a List in Reverse Order

A step of the composed embedding uses the walk of an edge either as it is or turned around
(`Walk.reverse`), and turning a walk around reverses its vertex list and its edge list. This file
gives the loop that copies a list in reverse order: it writes `mem (src + len - 1 - i)` at
`dst + i`. The result is `revCopy_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Procedure body, at `args = [dst, src, len]`. -/
def revCopyBody : Stmt :=
  forRange 3 (.const 0) (.reg 2) (
    .assign 4 (.load (.bin .sub (.bin .add (.reg 1) (.reg 2)) (.bin .add (.reg 3) (.const 1)))) ;;
    .store (.bin .add (.reg 0) (.reg 3)) (.reg 4)) ;;
  .ret (.const 0)

/-- The list is at `src`, below the output `dst`, which fits in a word with room for `len`
cells. -/
def RevCopyPre (mem : ℕ → ℕ) (dst src len : ℕ) (xs : List ℕ) (w : ℕ) : Prop :=
  ListAt mem src xs ∧ xs.length = len ∧ src + len ≤ dst ∧ dst + len < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `revCopyBody`. -/
def revCopyContract (w : ℕ) : Contract where
  pre args mem := ∃ dst src len xs, args = [dst, src, len] ∧ RevCopyPre mem dst src len xs w
  post args mem _ mem' := ∀ dst src len xs, args = [dst, src, len] →
    RevCopyPre mem dst src len xs w →
    ListAt mem' dst xs.reverse ∧ ∀ x, x < dst ∨ dst + len ≤ x → mem' x = mem x
  cost args _ := args.getD 2 0 * 30 + 20

/-- Loop invariant after `i` entries. -/
def RevCopyInv (mem : ℕ → ℕ) (dst src len : ℕ) (xs : List ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = len ∧ st.regs 3 = i ∧ i ≤ len ∧
    (∀ t (ht : t < i) (htx : t < xs.reverse.length), st.mem (dst + t) = xs.reverse[t]) ∧
    ∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x

lemma revCopy_step {w : ℕ} {p : Program} {mem : ℕ → ℕ} {dst src len : ℕ} {xs : List ℕ}
    (hpre : RevCopyPre mem dst src len xs w) (i : ℕ) (hi : i < len) :
    Triple w p (RevCopyInv mem dst src len xs i)
      (.assign 4 (.load (.bin .sub (.bin .add (.reg 1) (.reg 2))
          (.bin .add (.reg 3) (.const 1)))) ;;
        .store (.bin .add (.reg 0) (.reg 3)) (.reg 4))
      (normalPost fun st₁ =>
        RevCopyInv mem dst src len xs (i + 1)
          { st₁ with regs := Function.update st₁.regs 3 (i + 1) } ∧ st₁.regs 3 = i)
      (fun _ => 20) := by
  obtain ⟨hX, hlen, hsd, hdw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, hin, hdone, hout⟩ := hI
  have hil : len - 1 - i < xs.length := by omega
  have hir : i < xs.reverse.length := by rw [List.length_reverse]; omega
  have hval : xs.reverse[i] = xs[len - 1 - i] := by
    rw [List.getElem_reverse]; congr 1; omega
  have hxj : st.mem (src + len - (i + 1)) = xs.reverse[i] := by
    rw [hout _ (Or.inl (by omega)), hval, show src + len - (i + 1) = src + (len - 1 - i) by omega]
    exact hX.getElem hil
  have e4 : (Expr.load (.bin .sub (.bin .add (.reg 1) (.reg 2))
      (.bin .add (.reg 3) (.const 1)))).eval w st = some xs.reverse[i] :=
    ev_load' (ev_sub (ev_add (ev_reg r1 (by omega)) (ev_reg r2 (by omega)) (by omega))
      (ev_add (ev_reg r3 (by omega)) (ev_const hw1) (by omega)) (by omega) (by omega)) hxj
  let s1 : State := { st with regs := Function.update st.regs 4 xs.reverse[i] }
  have ea : (Expr.bin .add (.reg 0) (.reg 3)).eval w s1 = some (dst + i) :=
    ev_add (ev_reg (v := dst) (by simp [s1, r0]) (by omega)) (ev_reg (v := i) (by simp [s1, r3])
      (by omega)) (by omega)
  have ev : (Expr.reg 4).eval w s1 = some xs.reverse[i] := by
    simp [s1, Expr.eval]
  refine runs_start_le ?_
  refine runs_seq_assign_le e4 ?_
  refine runs_store_le ea ev ⟨⟨by simp [s1, r0], by simp [s1, r1], by simp [s1, r2],
    by simp, by omega, ?_, ?_⟩, by simp [s1, r3]⟩
    (by simp only [Expr.size]; omega)
  · intro t ht htx
    simp only [s1]
    by_cases hti : t = i
    · subst hti; rw [Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact hdone t (by omega) htx
  · intro x hx
    simp only [s1]
    rw [Function.update_of_ne (by omega)]
    exact hout x (by omega)

/-- `revCopyBody` at `f` meets `revCopyContract`. The cost is `30 len + 20`. -/
theorem revCopy_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hproc : p.procs[f]? = some revCopyBody) :
    MeetsContract w p f (revCopyContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨dst, src, len, xs, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hX, hlen, hsd, hdw, hw1⟩ := hP'
  have hnw : len < 2 ^ w := hwords len (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 3) (lo := .const 0) (hi := .reg 2)
    (P := fun st => st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = len ∧ st.mem = mem)
    (Inv := RevCopyInv mem dst src len xs) 20 0 len (Nat.zero_le _) hw1 (fun _ => hnw)
    (fun st ⟨q0, q1, q2, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp, Nat.zero_le _,
        fun t ht => absurd ht (Nat.not_lt_zero _), fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.1 hnw)
    (fun i _ hi => revCopy_step hP i hi)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, hdone, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega)) (fun d' s' l' xs' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    have hxx : xs = xs' := List.ext_getElem (hlen.trans h2.2.1.symm) fun t h1 h2' =>
      (hX.getElem h1).symm.trans (h2.1.getElem h2')
    subst hxx
    refine ⟨fun t ht => hdone t (by rw [List.length_reverse] at ht; omega) ht, hout⟩
  · simp only [Expr.size, revCopyContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    omega

end MinCostFlow.Spanner
