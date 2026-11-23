module

public import MinCostFlow.HierPaths.DelProgBase

/-!
# The first step of the `Delete` program: mark the edge deleted

`Delete(e)` first records that `e` is deleted: it sets bit `e` of section 16 (the deleted edges)
and adds one to the count of deleted edges, word 14 of the header (section 0). `markDelStmt` is
this step, for the handle in register `0` and the edge in register `1`, as in the argument list
`[b, e, h]` of operation `0`. `markDel_triple` shows that it leaves in memory the block of
`HierConcrete.markDeleted`, the concrete state with `e` added to the deleted edges of both the
dynamic and the abstract state.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- The concrete state with the edge `e` marked deleted. -/
def HierConcrete.markDeleted (x : HierConcrete) (e : ℕ) : HierConcrete :=
  ⟨x.H, ⟨{ x.ms.st with deleted := insert e x.ms.st.deleted },
    { x.ms.abs with deleted := insert e x.ms.abs.deleted }⟩⟩

/-- The number of sections of the block. -/
abbrev numSec : ℕ := 24

/-- Set bit `e` of the deleted edges, then add one to the count of deleted edges. -/
def markDelStmt : Stmt :=
  .seq (.store (secAddr numSec 0 16 (.reg 1)) (.const 1))
    (.store (secAddr numSec 0 0 (.const 14))
      (.bin .add (readSec numSec 0 0 (.const 14)) (.const 1)))

theorem markDelStmt_noRand : markDelStmt.NoRand := by
  simp [markDelStmt, Stmt.NoRand]

theorem HierConcrete.sections_markDeleted (x : HierConcrete) {e : ℕ}
    (he : e ∉ x.ms.st.deleted) :
    (x.markDeleted e).sections =
      (x.sections.set 16 ((x.sections.getD 16 []).set e 1)).set 0
        (((x.sections.set 16 ((x.sections.getD 16 []).set e 1)).getD 0 []).set 14
          (x.ms.st.deleted.card + 1)) := by
  have hbit : (bitsList x.m fun e' => decide (e' ∈ x.ms.st.deleted)).set e 1 =
      bitsList x.m fun e' => decide (e' ∈ insert e x.ms.st.deleted) := by
    have := bitsList_set x.m (fun e' => decide (e' ∈ x.ms.st.deleted)) e true
    simp only [if_true] at this
    rw [this]
    congr 1
    funext e'
    by_cases h : e' = e
    · subst h; simp
    · simp [Finset.mem_insert, h]
  have hcard : (insert e x.ms.st.deleted).card = x.ms.st.deleted.card + 1 :=
    Finset.card_insert_of_notMem he
  simp only [HierConcrete.sections, HierConcrete.header, HierConcrete.markDeleted,
    HierConcrete.n, HierConcrete.m, HierConcrete.depth, HierConcrete.pairIdxTable] at hbit ⊢
  simp [List.set, hbit, hcard]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The block keeps its length when a word is replaced. -/
theorem length_layoutList_set_set (bs : List (List ℕ)) (i k v : ℕ) :
    (layoutList (bs.set i ((bs.getD i []).set k v))).length = (layoutList bs).length := by
  by_cases hi : i < bs.length
  · by_cases hk : k < (bs.getD i []).length
    · have hset : layoutList (bs.set i ((bs.getD i []).set k v)) =
          (layoutList bs).set (bs.length + 1 + ((List.range i).map fun j =>
            (bs.getD j []).length).sum + k) v := by
        unfold layoutList
        rw [← csrList_set (fun j => bs.getD j []) hi hk v, List.length_set]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [List.getD_eq_getElem?_getD, hi]
        · rw [Function.update_of_ne hj]
          simp [List.getD_eq_getElem?_getD, Ne.symm hj]
      rw [hset, List.length_set]
    · rw [List.set_eq_of_length_le (l := bs.getD i []) (by omega)]
      have : bs.set i (bs.getD i []) = bs := by
        apply List.ext_getElem (by simp)
        intro j h1 h2
        rw [List.getElem_set]
        split_ifs with h
        · subst h; simp [List.getD_eq_getElem?_getD, hi]
        · rfl
      rw [this]
  · rw [List.set_eq_of_length_le (by omega)]

/-- **The marking step.** From the block of `x` in memory, with the handle in register `0` and
an edge `e < m` not yet deleted in register `1`, `markDelStmt` leaves the block of
`x.markDeleted e` and the registers unchanged. -/
theorem markDel_triple {w : ℕ} {p : Program} (x : HierConcrete) {b e : ℕ} {R mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hR1 : R 1 = e) (hem : e < x.m) (he : e ∉ x.ms.st.deleted)
    (hb : b + x.encode.length < 2 ^ w) (hcw : x.ms.st.deleted.card + 1 < 2 ^ w) :
    Triple w p (fun st => st.regs = R ∧ ListAt st.mem b x.encode ∧ st.mem = mem0) markDelStmt
      (normalPost fun st' => st'.regs = R ∧ ListAt st'.mem b (x.markDeleted e).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → st'.mem j = mem0 j)
      (fun _ => 40) := by
  have hlen : x.sections.length = numSec := rfl
  have henc : 25 ≤ x.encode.length := by
    simp [HierConcrete.encode, layoutList, csrList]
  have h16 : 16 < x.sections.length := by rw [hlen]; norm_num
  have h0 : 0 < (x.sections.set 16 ((x.sections.getD 16 []).set e 1)).length := by
    rw [List.length_set, hlen]; norm_num
  have hlen1 : (x.sections.set 16 ((x.sections.getD 16 []).set e 1)).length = numSec := by
    rw [List.length_set, hlen]
  have hbits : (x.sections.getD 16 []).length = x.m := by
    simp [HierConcrete.sections]
  have hhdr : (x.sections.set 16 ((x.sections.getD 16 []).set e 1)).getD 0 [] = x.header := by
    simp [HierConcrete.sections]
  have hb1 : b + (layoutList (x.sections.set 16 ((x.sections.getD 16 []).set e 1))).length <
      2 ^ w := by
    rw [length_layoutList_set_set]; exact hb
  have t1 := triple_writeSec' (w := w) (p := p)
    (P := fun st => st.regs = R ∧ ListAt st.mem b x.encode ∧ st.mem = mem0) (b := b) (bs := x.sections) (r := 0)
    h16 (ke := .reg 1) (ve := .const 1) (k := fun _ => e) (v := fun _ => 1)
    (fun st hst => ⟨hst.2.1, by rw [hst.1, hR0], Expr.eval_reg_of_eq (by rw [hst.1, hR1]),
      by rw [hbits]; exact hem, Expr.eval_const (by omega)⟩) hb
  have t2 := triple_writeSec' (w := w) (p := p)
    (P := fun st => st.regs = R ∧
      ListAt st.mem b (layoutList (x.sections.set 16 ((x.sections.getD 16 []).set e 1))) ∧
      ∀ j, (j < b ∨ b + x.encode.length ≤ j) → st.mem j = mem0 j)
    (b := b) (bs := x.sections.set 16 ((x.sections.getD 16 []).set e 1)) (r := 0) h0
    (ke := .const 14) (ve := .bin .add (readSec numSec 0 0 (.const 14)) (.const 1))
    (k := fun _ => 14) (v := fun _ => x.ms.st.deleted.card + 1)
    (fun st hst => by
      refine ⟨hst.2.1, by rw [hst.1, hR0], Expr.eval_const (by omega), ?_, ?_⟩
      · rw [hhdr]; simp [HierConcrete.header]
      · have hr := eval_readSec (w := w) (st := st) hst.2.1 hb1 (r := 0) (by rw [hst.1, hR0]) h0
          (ke := .const 14) (k := 14) (Expr.eval_const (by omega)) (by rw [hhdr]; simp [HierConcrete.header])
        rw [hlen1] at hr
        simp [HierConcrete.sections, HierConcrete.header] at hr
        exact Expr.eval_add hr (Expr.eval_const (by omega)) hcw) hb1
  rw [hlen] at t1
  rw [hlen1] at t2
  refine (Triple.seq_normal t1 (t2.weaken_pre ?_) (fun _ _ _ _ => ?_)).strengthen_post ?_
  · rintro st ⟨st0, hst0, hregs, _, hl, hf⟩
    exact ⟨hregs.trans hst0.1, hl, fun j hj => (hf j hj).trans (congrFun hst0.2.2 j)⟩
  · simp [secAddr, readSec, Expr.size]
  · rintro (_ | _) st' h
    · obtain ⟨st1, hst1, hregs, _, hl, hf⟩ := h
      refine ⟨hregs.trans hst1.1, ?_, ?_⟩
      · unfold HierConcrete.encode
        rw [HierConcrete.sections_markDeleted x he]
        exact hl
      · intro j hj
        have hj' : j < b ∨ b + (layoutList (x.sections.set 16
            ((x.sections.getD 16 []).set e 1))).length ≤ j := by
          rw [length_layoutList_set_set]
          exact hj
        exact (hf j hj').trans (hst1.2.2 j hj)
    · exact h

end MinCostFlow.HierPaths

end
