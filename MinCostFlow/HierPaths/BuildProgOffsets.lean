module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.HierPaths.LayoutEncode

/-!
# Writing the offsets of a compressed list

Each section of the static output but the first is a table or a list of lists in compressed
form (`csrList`), whose first part is the `k + 1` start offsets of the lists: the prefix sums of
their lengths. `offsetsProc`, called with `[lens, k, dst]`, where the lengths are the words
`lens, …, lens + k − 1`, writes the prefix sums `psum g 0, …, psum g k` to `dst, …, dst + k` and
changes no other cell (`offsetsProc_meetsContract`). The cost is `22 k + 30`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The prefix sums `g 0 + ⋯ + g (i − 1)`. -/
def psum (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => psum g i + g i

/-- `for r3 in [0, k): (mem[dst + r3] := r4; r4 := r4 + mem[lens + r3])`;
`mem[dst + k] := r4`; return `r4`. Register `4` starts at `0`. -/
def offsetsProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1)
      (.seq (.store (.bin .add (.reg 2) (.reg 3)) (.reg 4))
        (.assign 4 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.reg 3)))))))
    (.seq (.store (.bin .add (.reg 2) (.reg 1)) (.reg 4)) (.ret (.reg 4)))

/-- The contract of `offsetsProc`. The total length must fit in a word. -/
def offsetsContract (w : ℕ) : Contract where
  pre args mem := ∃ lens k dst, args = [lens, k, dst] ∧ lens + k ≤ dst ∧ dst + k < 2 ^ w ∧
    psum (fun j => mem (lens + j)) k < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ lens k dst, args = [lens, k, dst] ∧
    v = psum (fun j => mem (lens + j)) k ∧
    (∀ i ≤ k, mem' (dst + i) = psum (fun j => mem (lens + j)) i) ∧
    ∀ x, (x < dst ∨ dst + k < x) → mem' x = mem x
  cost args _ := 22 * args.getD 1 0 + 30

/-- The prefix sums as list sums. -/
theorem psum_eq_sum (g : ℕ → ℕ) : ∀ i, psum g i = ((List.range i).map g).sum
  | 0 => rfl
  | i + 1 => by rw [psum, psum_eq_sum g i, List.range_succ]; simp

/-- **The offsets written by `offsetsProc` are those of `csrList`.** If the lengths in memory
are those of the lists `f 0, …, f (k − 1)`, the words the procedure writes at `dst` are the
offsets part `csrOffsets k f` of `csrList k f`. -/
theorem listAt_csrOffsets {mem mem' : ℕ → ℕ} {lens k dst : ℕ} {f : ℕ → List ℕ}
    (hlen : ∀ j < k, mem (lens + j) = (f j).length)
    (hout : ∀ i ≤ k, mem' (dst + i) = psum (fun j => mem (lens + j)) i) :
    ListAt mem' dst (csrOffsets k f) := by
  intro i hi
  have hik : i ≤ k := by simp [csrOffsets] at hi; omega
  simp only [csrOffsets, List.getElem_map, List.getElem_range]
  rw [hout i hik, psum_eq_sum]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact hlen j (by simp at hj; omega)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

theorem psum_mono (g : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : psum g i ≤ psum g j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · have := ih (by omega); simp only [psum]; omega
    · rw [h']

/-- The loop of `offsetsProc`. -/
theorem offsets_triple {w lens k dst : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hld : lens + k ≤ dst) (hdk : dst + k < 2 ^ w)
    (hsum : psum (fun j => mem₀ (lens + j)) k < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = lens ∧ st.regs 1 = k ∧ st.regs 2 = dst ∧ st.regs 4 = 0 ∧
        st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1)
        (.seq (.store (.bin .add (.reg 2) (.reg 3)) (.reg 4))
          (.assign 4 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.reg 3)))))))
      (normalPost fun st' => st'.regs 0 = lens ∧ st'.regs 1 = k ∧ st'.regs 2 = dst ∧
        st'.regs 4 = psum (fun j => mem₀ (lens + j)) k ∧
        (∀ i < k, st'.mem (dst + i) = psum (fun j => mem₀ (lens + j)) i) ∧
        ∀ x, (x < dst ∨ dst + k ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 22 * k + 7) := by
  set g := fun j => mem₀ (lens + j)
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .seq (.store (.bin .add (.reg 2) (.reg 3)) (.reg 4))
          (.assign 4 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.reg 3))))))
    (P := fun st => st.regs 0 = lens ∧ st.regs 1 = k ∧ st.regs 2 = dst ∧ st.regs 4 = 0 ∧
        st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = lens ∧ st.regs 1 = k ∧ st.regs 2 = dst ∧ st.regs 3 = i ∧
      st.regs 4 = psum g i ∧
      (∀ j < i, st.mem (dst + j) = psum g j) ∧
      (∀ x, (x < dst ∨ dst + i ≤ x) → st.mem x = mem₀ x))
    13 0 k (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h4, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp, by simp [h4, psum],
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = k := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, h4, hz, hf⟩
      have hli : st.mem (lens + i) = mem₀ (lens + i) := hf _ (Or.inl (by omega))
      have hdw : dst + i < 2 ^ w := by omega
      have hlw : lens + i < 2 ^ w := by omega
      have hpi : psum g (i + 1) < 2 ^ w := lt_of_le_of_lt (psum_mono g (by omega)) hsum
      have hgi : g i = mem₀ (lens + i) := rfl
      have hpw : psum g i + mem₀ (lens + i) < 2 ^ w := by
        simp only [psum] at hpi; omega
      have hmw : mem₀ (lens + i) < 2 ^ w := by omega
      refine ⟨.normal, State.mk (Function.update st.mem (dst + i) (psum g i))
        (Function.update st.regs 4 (psum g (i + 1))) st.pos, 13, ?_, ?_, le_refl _⟩
      · refine runs_seq_iff.mpr (Or.inr ⟨State.mk (Function.update st.mem (dst + i) (psum g i))
          st.regs st.pos, 5, 7, ?_, ?_, rfl⟩)
        · refine runs_store_iff.mpr ⟨dst + i, psum g i, ?_, ?_, rfl, rfl, rfl⟩
          · simp [Expr.eval, h2, h3, hdw]
          · simp [Expr.eval, h4]
        · refine runs_assign_iff.mpr ⟨psum g (i + 1), ?_, rfl, rfl, rfl⟩
          have hli' : Function.update st.mem (dst + i) (psum g i) (lens + i) =
              mem₀ (lens + i) := by
            rw [Function.update_of_ne (by omega), hli]
          have hpi' : psum g (i + 1) = psum g i + mem₀ (lens + i) := rfl
          simp [Expr.eval, h0, h3, h4, hlw, hli', hpi', hpw]
      · refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp, by simp, ?_, ?_⟩,
          by simp [h3]⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hz j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨h0, h1, h2, _, h4, hz, hf⟩ := hpost
      exact ⟨h0, h1, h2, h4, hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`offsetsProc` meets its contract.** -/
theorem offsetsProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some offsetsProc) :
    MeetsContract w p f (offsetsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨lens, k, dst, rfl, hld, hdk, hsum, hw⟩
  refine runs_start_le ?_
  dsimp only [offsetsProc]
  refine runs_seq_triple_le (offsets_triple p mem hw hld hdk hsum)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      rfl⟩ ?_
  intro st₁ ⟨h0, h1, h2, h4, hz, hf⟩
  have hdw : dst + k < 2 ^ w := hdk
  refine runs_seq_store_le (x := dst + k) (v := psum (fun j => mem (lens + j)) k)
    (by simp [Expr.eval, h1, h2, hdw]) (by simp [Expr.eval, h4]) ?_
  refine runs_ret_le (v := psum (fun j => mem (lens + j)) k) (by simp [Expr.eval, h4])
    ⟨lens, k, dst, rfl, rfl, ?_, ?_⟩ ?_
  · intro i hi
    dsimp only
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [Function.update_of_ne (by omega)]; exact hz i hik
    · rw [show i = k by omega, Function.update_self]
  · intro x hx
    dsimp only
    rw [Function.update_of_ne (by omega)]
    exact hf x (by omega)
  · simp only [offsetsContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_reg,
      Expr.size_bin]
    omega

end MinCostFlow.HierPaths
