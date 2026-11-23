module

public import MinCostFlow.HierPaths.DelProgLayout
public import WordRAM.Logic

/-!
# Reading and writing one word of a section

A program that holds the handle `b` of a block (`HierPaths/Layout.lean`) in register `r` finds
word `k` of section `i` at `b + (S + 1) + mem (b + i) + k`, with `S` the number of sections
(`listAt_section`). `secAddr S r i k` is this address as an expression, with `k` an
expression too. This file proves:

* `addr_lt_length`: the address is inside the block;
* `eval_secAddr` and `eval_readSec`: the address and the word there evaluate, when the block
  ends below `2 ^ w`;
* `triple_writeSec`: storing a value there gives the block with that word of section `i`
  replaced (`listAt_layout_write`), with the registers unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The address of word `k` of section `i` of a block with `S` sections whose handle is in
register `r`. -/
def secAddr (S r i : ℕ) (k : Expr) : Expr :=
  .bin .add (.bin .add (.bin .add (.reg r) (.const (S + 1)))
    (.load (.bin .add (.reg r) (.const i)))) k

/-- Word `k` of section `i` of the block. -/
def readSec (S r i : ℕ) (k : Expr) : Expr := .load (secAddr S r i k)

private theorem csrData_length_ge (n : ℕ) (f : ℕ → List ℕ) {i : ℕ} (hi : i < n) :
    ((List.range i).map fun j => (f j).length).sum + (f i).length ≤ (csrData n f).length := by
  have h1 : ((List.range (i + 1)).map fun j => (f j).length).sum =
      ((List.range i).map fun j => (f j).length).sum + (f i).length := by
    simp [List.range_succ]
  have h2 : (csrData n f).length = ((List.range n).map fun j => (f j).length).sum := by
    simp [csrData, List.length_flatMap]
  rw [← h1, h2]
  have hk : n = (i + 1) + (n - (i + 1)) := by omega
  conv_rhs => rw [hk, List.range_add, List.map_append, List.sum_append]
  omega

/-- The word `k` of section `i` lies inside the block. -/
theorem addr_lt_length {bs : List (List ℕ)} {i : ℕ} (hi : i < bs.length) {k : ℕ}
    (hk : k < (bs.getD i []).length) :
    bs.length + 1 + ((List.range i).map fun j => (bs.getD j []).length).sum + k <
      (layoutList bs).length := by
  have := csrData_length_ge bs.length (fun j => bs.getD j []) hi
  simp only [layoutList, csrList, List.length_append, length_csrOffsets]
  omega

/-- Reading word `k` of section `i`. -/
theorem mem_secWord {mem : ℕ → ℕ} {b : ℕ} {bs : List (List ℕ)} (h : ListAt mem b (layoutList bs))
    {i : ℕ} (hi : i < bs.length) {k : ℕ} (hk : k < (bs.getD i []).length) :
    mem (b + (bs.length + 1) + mem (b + i) + k) = (bs.getD i [])[k] :=
  listAt_section h hi k hk

/-- The offset word of section `i` is the sum of the lengths before it. -/
theorem mem_secOffset {mem : ℕ → ℕ} {b : ℕ} {bs : List (List ℕ)} (h : ListAt mem b (layoutList bs))
    {i : ℕ} (hi : i ≤ bs.length) :
    mem (b + i) = ((List.range i).map fun j => (bs.getD j []).length).sum :=
  csrList_offset h hi

/-- The address expression evaluates to word `k` of section `i`, inside the block. -/
theorem eval_secAddr {w : ℕ} {st : State} {b : ℕ} {bs : List (List ℕ)}
    (h : ListAt st.mem b (layoutList bs)) (hb : b + (layoutList bs).length < 2 ^ w) {r : ℕ}
    (hr : st.regs r = b) {i : ℕ} (hi : i < bs.length) {ke : Expr} {k : ℕ}
    (hke : ke.eval w st = some k) (hk : k < (bs.getD i []).length) :
    (secAddr bs.length r i ke).eval w st =
      some (b + (bs.length + 1) + st.mem (b + i) + k) := by
  have hoff := mem_secOffset h hi.le
  have hlt := addr_lt_length hi hk
  unfold secAddr
  refine Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr)
    (Expr.eval_const (by omega)) (by omega)) (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const (by omega)) (by omega)) rfl)
    (by omega)) hke (by omega)

/-- The read expression evaluates to word `k` of section `i`. -/
theorem eval_readSec {w : ℕ} {st : State} {b : ℕ} {bs : List (List ℕ)}
    (h : ListAt st.mem b (layoutList bs)) (hb : b + (layoutList bs).length < 2 ^ w) {r : ℕ}
    (hr : st.regs r = b) {i : ℕ} (hi : i < bs.length) {ke : Expr} {k : ℕ}
    (hke : ke.eval w st = some k) (hk : k < (bs.getD i []).length) :
    (readSec bs.length r i ke).eval w st = some ((bs.getD i [])[k]) :=
  Expr.eval_load_of_eq (eval_secAddr h hb hr hi hke hk) (mem_secWord h hi hk)

/-- **Writing word `k` of section `i`.** From a state with the block in memory, the store
leaves the block with entry `k` of section `i` replaced by the value `v`, and the registers
unchanged. -/
theorem triple_writeSec {w : ℕ} {p : Program} {P : State → Prop} {b : ℕ} {bs : List (List ℕ)}
    {r i : ℕ} (hi : i < bs.length) {ke ve : Expr} {k : State → ℕ} {v : State → ℕ}
    (hP : ∀ st, P st → ListAt st.mem b (layoutList bs) ∧ st.regs r = b ∧
      ke.eval w st = some (k st) ∧ k st < (bs.getD i []).length ∧ ve.eval w st = some (v st))
    (hb : b + (layoutList bs).length < 2 ^ w) :
    Triple w p P (.store (secAddr bs.length r i ke) ve)
      (normalPost fun st' => ∃ st, P st ∧ st'.regs = st.regs ∧ st'.pos = st.pos ∧
        ListAt st'.mem b (layoutList (bs.set i ((bs.getD i []).set (k st) (v st)))))
      (fun _ => (secAddr bs.length r i ke).size + ve.size + 1) := by
  refine Triple.store (addr := fun st => b + (bs.length + 1) + st.mem (b + i) + k st) (val := v)
    (fun st hst => ?_) (fun st hst => (hP st hst).2.2.2.2) (fun st hst => ?_)
  · obtain ⟨h, hr, hke, hk, _⟩ := hP st hst
    exact eval_secAddr h hb hr hi hke hk
  · obtain ⟨h, _, _, hk, _⟩ := hP st hst
    exact ⟨st, hst, rfl, rfl, listAt_layout_write h hi hk (v st)⟩

/-- `triple_writeSec` with the frame: cells outside the block keep their values. -/
theorem triple_writeSec' {w : ℕ} {p : Program} {P : State → Prop} {b : ℕ} {bs : List (List ℕ)}
    {r i : ℕ} (hi : i < bs.length) {ke ve : Expr} {k : State → ℕ} {v : State → ℕ}
    (hP : ∀ st, P st → ListAt st.mem b (layoutList bs) ∧ st.regs r = b ∧
      ke.eval w st = some (k st) ∧ k st < (bs.getD i []).length ∧ ve.eval w st = some (v st))
    (hb : b + (layoutList bs).length < 2 ^ w) :
    Triple w p P (.store (secAddr bs.length r i ke) ve)
      (normalPost fun st' => ∃ st, P st ∧ st'.regs = st.regs ∧ st'.pos = st.pos ∧
        ListAt st'.mem b (layoutList (bs.set i ((bs.getD i []).set (k st) (v st)))) ∧
        ∀ a, (a < b ∨ b + (layoutList bs).length ≤ a) → st'.mem a = st.mem a)
      (fun _ => (secAddr bs.length r i ke).size + ve.size + 1) := by
  refine Triple.store (addr := fun st => b + (bs.length + 1) + st.mem (b + i) + k st) (val := v)
    (fun st hst => ?_) (fun st hst => (hP st hst).2.2.2.2) (fun st hst => ?_)
  · obtain ⟨h, hr, hke, hk, _⟩ := hP st hst
    exact eval_secAddr h hb hr hi hke hk
  · obtain ⟨h, _, _, hk, _⟩ := hP st hst
    have hoff := mem_secOffset h hi.le
    have hlt := addr_lt_length hi hk
    refine ⟨st, hst, rfl, rfl, listAt_layout_write h hi hk (v st), fun a ha => ?_⟩
    show Function.update _ _ _ a = _
    exact Function.update_of_ne (by rw [hoff]; omega) _ _

end MinCostFlow.HierPaths

end
