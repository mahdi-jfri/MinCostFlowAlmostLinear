module

public import WordRAM.Logic
import Mathlib.Logic.Function.Iterate
import WordRAM.Tactic

/-!
# One row of the ancestor table

The stretch pass in Definition 5.8 (pages 19–20) uses a table of
ancestor jumps. To double the jump length, look up each vertex's
current ancestor and then look up that ancestor in the same row.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Arguments are `[previous row, next row, vertex count]`. -/
def ancestorRowLoop : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3))
      (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 0) (.reg 3))))))

/-- Fill the next row in linear time while preserving the previous row. -/
theorem ancestorRowLoop_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ)
    (pos src dst n : ℕ) (jump : ℕ → ℕ)
    (hw : 1 < 2^w) (hs : src + n < 2^w) (hd : dst + n < 2^w)
    (hsep : src + n ≤ dst ∨ dst + n ≤ src)
    (hjump : ∀ i < n, jump i < n ∧ mem (src+i) = jump i) :
    Triple w p (fun st => st = startState [src,dst,n] mem pos) ancestorRowLoop
      (normalPost fun st =>
        (∀ i < n, st.mem (dst+i) = jump (jump i)) ∧
        (∀ a, a < dst ∨ dst+n ≤ a → st.mem a = mem a))
      (fun _ => 20*n+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = n ∧ st.regs 3 = i ∧
    (∀ j < i, st.mem (dst+j) = jump (jump j)) ∧
    (∀ a, a < dst ∨ dst+i ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 3))
      (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 0) (.reg 3))))))
    (Inv := Inv) (P := fun st => st = startState [src,dst,n] mem pos)
    11 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 2 = n := h.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,hdone,hframe⟩
      obtain ⟨hj₁, hread₁⟩ := hjump i hi
      obtain ⟨hj₂, hread₂⟩ := hjump (jump i) hj₁
      have hval₁ : st.mem (src+i) = jump i := (hframe _ (by omega)).trans hread₁
      have hval₂ : st.mem (src+jump i) = jump (jump i) := (hframe _ (by omega)).trans hread₂
      have hsrc : src < 2^w := by omega
      have hdst : dst < 2^w := by omega
      have hi' : i < 2^w := by omega
      have hs₁ : src+i < 2^w := by omega
      have hs₂ : src+jump i < 2^w := by omega
      have hd₁ : dst+i < 2^w := by omega
      have hw₁ : jump i < 2^w := by omega
      have hw₂ : jump (jump i) < 2^w := by omega
      refine ⟨.normal, { st with mem := Function.update st.mem (dst+i) (jump (jump i)) },
        11, runs_store_iff.mpr ⟨_,_,by eval_expr,?_,rfl,rfl,rfl⟩,?_,by simp⟩
      · eval_expr
        change st.mem (src + st.mem (src+i)) = _
        rwa [hval₁]
      ·
        refine ⟨⟨h0,h1,h2,by simp,?_,?_⟩,h3⟩
        · intro j hj
          dsimp only
          by_cases heq : j = i
          · subst j
            simp
          · rw [Function.update_of_ne (by omega)]
            exact hdone j (by omega)
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe a (ha.imp_right (by omega)))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | normal => exact h.2.2.2.2
    | returned _ => exact h
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.mul_comm]

/-- A row at level `k` follows the parent pointer `2^k` times. -/
def ancestorJump (parent : ℕ → ℕ) (k v : ℕ) : ℕ :=
  (parent^[2^k]) v

/-- Doubling a row gives precisely the next power-of-two jump. -/
theorem ancestorJump_succ (parent : ℕ → ℕ) (k v : ℕ) :
    ancestorJump parent (k+1) v = ancestorJump parent k (ancestorJump parent k v) := by
  unfold ancestorJump
  rw [pow_succ, Nat.mul_two, Function.iterate_add_apply]

/-- A parent function closed on the compact range has all its jump rows
closed on that range as well. -/
theorem ancestorJump_lt {parent : ℕ → ℕ} {n : ℕ}
    (hparent : ∀ v < n, parent v < n) (k : ℕ) {v : ℕ} (hv : v < n) :
    ancestorJump parent k v < n := by
  induction k generalizing v with
  | zero => simpa [ancestorJump] using hparent v hv
  | succ k ih =>
    rw [ancestorJump_succ]
    exact ih (ih hv)

/-- The machine pass constructs row `k + 1` of the binary lifting
table from row `k`. -/
theorem ancestorJumpRow_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ)
    (pos src dst n k : ℕ) (parent : ℕ → ℕ)
    (hw : 1 < 2^w) (hs : src+n < 2^w) (hd : dst+n < 2^w)
    (hsep : src+n ≤ dst ∨ dst+n ≤ src)
    (hparent : ∀ v < n, parent v < n)
    (hrow : ∀ v < n, mem (src+v) = ancestorJump parent k v) :
    Triple w p (fun st => st = startState [src,dst,n] mem pos) ancestorRowLoop
      (normalPost fun st =>
        (∀ v < n, st.mem (dst+v) = ancestorJump parent (k+1) v) ∧
        (∀ a, a < dst ∨ dst+n ≤ a → st.mem a = mem a))
      (fun _ => 20*n+7) := by
  refine (ancestorRowLoop_triple p mem pos src dst n (ancestorJump parent k) hw hs hd hsep
    (fun i hi => ⟨ancestorJump_lt hparent k hi, hrow i hi⟩)).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st h
  cases o with
  | returned _ => exact h
  | normal =>
    exact ⟨fun v hv => (h.1 v hv).trans (ancestorJump_succ parent k v).symm, h.2⟩

/-- Callable ancestor-row procedure. -/
def ancestorRowBody : Stmt := ancestorRowLoop ;; .ret (.const 0)

/-- Inputs and outputs for one row of the jump table. -/
def ancestorRowContract (w : ℕ) (jump : ℕ → ℕ) : Contract where
  pre args mem := ∃ src dst n, args = [src,dst,n] ∧ 1 < 2^w ∧
    src+n < 2^w ∧ dst+n < 2^w ∧ (src+n ≤ dst ∨ dst+n ≤ src) ∧
    ∀ i < n, jump i < n ∧ mem (src+i) = jump i
  post args mem ret out :=
    let dst := args.getD 1 0
    let n := args.getD 2 0
    ret = 0 ∧ (∀ i < n, out (dst+i) = jump (jump i)) ∧
      (∀ a, a < dst ∨ dst+n ≤ a → out a = mem a)
  cost args _ := 20 * args.getD 2 0 + 10

/-- The row pass meets its callable contract. -/
theorem ancestorRow_meetsContract {w row : ℕ} {p : Program}
    (hp : p.procs[row]? = some ancestorRowBody) (jump : ℕ → ℕ) :
    MeetsContract w p row (ancestorRowContract w jump) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,n,rfl,hw,hs,hd,hsep,hjump⟩ := hpre
  have hzero : 0 < 2^w := Nat.two_pow_pos _
  apply runs_start_le
  unfold ancestorRowBody
  refine runs_seq_triple_le (ancestorRowLoop_triple p mem pos src dst n jump hw hs hd hsep hjump)
    rfl ?_
  intro st ⟨hrow,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,hrow,hframe⟩ ?_
  simp [ancestorRowContract, Expr.size]

end MinCostFlow.LastLevelProgram
