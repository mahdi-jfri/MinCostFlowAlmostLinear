module

public import MinCostFlow.HierPaths.DelProgFields
public import MinCostFlow.HierPaths.DelProgAdvance

/-!
# The validity test of the pair cursors

Entry `i` of the connector array of pair `q` is valid when its connector `c` is eligible
(`StaticArrays.pairValid`). The invariant `DelInv` says that the ineligibility bits (section 15)
are set exactly for the connectors that are not eligible (`inelig_eq`). So the program reads `c`
from the list `pairConns q` (section 8) and returns `1` minus the bit of `c`.

`pairTestStmt` does this, with the handle in register `0`, the pair in register `rq`, the cursor in
register `rc`, and the result in register `rv`. `pairTest_triple` is the specification that
`advanceStmt_triple` asks of its test. With it, `pairAdvance_triple` moves a pair cursor.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

theorem csrList_data_lt {n : ℕ} (f : ℕ → List ℕ) {j : ℕ} (hj : j < n) {k : ℕ}
    (hk : k < (f j).length) :
    n + 1 + ((List.range j).map fun i => (f i).length).sum + k < (csrList n f).length := by
  have h1 : ((List.range (j + 1)).map fun i => (f i).length).sum =
      ((List.range j).map fun i => (f i).length).sum + (f j).length := by
    simp [List.range_succ]
  have h2 : (csrList n f).length = n + 1 + ((List.range n).map fun i => (f i).length).sum := by
    simp [csrList, csrData, List.length_flatMap]
  have hk' : n = (j + 1) + (n - (j + 1)) := by omega
  have h3 : ((List.range (j + 1)).map fun i => (f i).length).sum ≤
      ((List.range n).map fun i => (f i).length).sum := by
    conv_rhs => rw [hk', List.range_add, List.map_append, List.sum_append]
    omega
  omega

/-- `eval_readSec` with the value as `getD`, which rewrites without dependent indices. -/
theorem eval_readSec' {w : ℕ} {st : State} {b : ℕ} {bs : List (List ℕ)}
    (h : ListAt st.mem b (layoutList bs)) (hb : b + (layoutList bs).length < 2 ^ w) {r : ℕ}
    (hr : st.regs r = b) {i : ℕ} (hi : i < bs.length) {ke : Expr} {k : ℕ}
    (hke : ke.eval w st = some k) (hk : k < (bs.getD i []).length) :
    (readSec bs.length r i ke).eval w st = some ((bs.getD i []).getD k 0) := by
  rw [eval_readSec h hb hr hi hke hk, List.getD_eq_getElem _ _ hk]

/-- A word index of a section is below the length of the block. -/
theorem lt_length_of_sec {bs : List (List ℕ)} {i : ℕ} (hi : i < bs.length) {k : ℕ}
    (hk : k < (bs.getD i []).length) : k < (layoutList bs).length := by
  have := addr_lt_length hi hk
  omega

theorem csrList_getD_offset {n : ℕ} (f : ℕ → List ℕ) {j : ℕ} (hj : j ≤ n) :
    (csrList n f).getD j 0 = ((List.range j).map fun i => (f i).length).sum := by
  have h : j < (csrList n f).length := by simp [csrList]; omega
  rw [List.getD_eq_getElem _ _ h, csrList_getElem_offset f hj h]

theorem csrList_getD_data {n : ℕ} (f : ℕ → List ℕ) {j : ℕ} (hj : j < n) {k : ℕ}
    (hk : k < (f j).length) :
    (csrList n f).getD (n + 1 + ((List.range j).map fun i => (f i).length).sum + k) 0 =
      (f j).getD k 0 := by
  have h := csrList_data_lt f hj hk
  rw [List.getD_eq_getElem _ _ h, csrList_getElem_data f hj hk h, List.getD_eq_getElem _ _ hk]

/-- Read connector `cur` of pair `q` into `rcon`, then set `rv` to `1` minus its bit. -/
def pairTestStmt (rq rc rcon rv : ℕ) : Stmt :=
  .seq (.assign rcon (readSec numSec 0 8
      (.bin .add (.bin .add (readSec numSec 0 0 (.const 4)) (.const 1))
        (.bin .add (readSec numSec 0 8 (.reg rq)) (.reg rc)))))
    (.assign rv (.bin .sub (.const 1) (readSec numSec 0 15 (.reg rcon))))

theorem pairTestStmt_noRand (rq rc rcon rv : ℕ) : (pairTestStmt rq rc rcon rv).NoRand := by
  simp [pairTestStmt, Stmt.NoRand]

/-- **The pair test.** -/
theorem pairTest_triple {w : ℕ} {p : Program} (x : HierConcrete) {b q : ℕ}
    {rq rc rgo rcon rv : ℕ} (h0con : rcon ≠ 0) (h0v : rv ≠ 0) (hqcon : rcon ≠ rq)
    (hccon : rcon ≠ rc) (hgcon : rcon ≠ rgo) (hcv : rv ≠ rc) (hgv : rv ≠ rgo)
    (hconv : rcon ≠ rv)
    (hq : q < x.H.A.numPairs) (hb : b + x.encode.length < 2 ^ w)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    (hmem : ∀ c ∈ x.H.A.pairConns q, c < x.H.A.C.numConn)
    {F : State → Prop}
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs rq = q ∧ ListAt s.mem b x.encode)
    (hFcon : ∀ s v, F s → F { s with regs := Function.update s.regs rcon v })
    (hFv : ∀ s v, F s → F { s with regs := Function.update s.regs rv v })
    (c : ℕ) (hc : c < (x.H.A.pairConns q).length) :
    Triple w p (fun s => F s ∧ s.regs rc = c ∧ s.regs rgo = 1) (pairTestStmt rq rc rcon rv)
      (normalPost fun s' => F s' ∧ s'.regs rc = c ∧ s'.regs rgo = 1 ∧
        s'.regs rv = if x.H.A.pairValid (x.H.A.surv x.ms.st) q c then 1 else 0)
      (fun _ => 60) := by
  have hlen : x.sections.length = numSec := rfl
  have henc : 25 ≤ x.encode.length := by
    simp [HierConcrete.encode, layoutList, csrList]
  have hs8 : x.sections.getD 8 [] = csrList x.H.A.numPairs x.H.A.pairConns := by
    simp [HierConcrete.sections]
  have hs15 : x.sections.getD 15 [] =
      bitsList x.H.A.C.numConn fun c => decide (c ∈ x.ms.st.inelig) := by
    simp [HierConcrete.sections]
  have hs0 : x.sections.getD 0 [] = x.header := by simp [HierConcrete.sections]
  set off := ((List.range q).map fun i => (x.H.A.pairConns i).length).sum with hoff
  set con := (x.H.A.pairConns q)[c] with hcon
  have hconlt : con < x.H.A.C.numConn := hmem con (List.getElem_mem hc)
  have hidx := csrList_data_lt x.H.A.pairConns hq hc
  have hw : x.encode.length < 2 ^ w := by omega
  have hl0 : 0 < x.sections.length := by rw [hlen]; norm_num
  have hl8 : 8 < x.sections.length := by rw [hlen]; norm_num
  have hl15 : 15 < x.sections.length := by rw [hlen]; norm_num
  have hql : q < (x.sections.getD 8 []).length := by rw [hs8]; simp [csrList]; omega
  have hdl : x.H.A.numPairs + 1 + (off + c) < (x.sections.getD 8 []).length := by
    rw [hs8]; omega
  have hdw : x.H.A.numPairs + 1 + (off + c) < 2 ^ w := by
    have := lt_length_of_sec hl8 hdl
    have h' : (layoutList x.sections).length = x.encode.length := rfl
    omega
  have hbit : (x.sections.getD 15 []).getD con 0 = if con ∈ x.ms.st.inelig then 1 else 0 := by
    rw [hs15, List.getD_eq_getElem _ _ (by simpa using hconlt)]
    simp [bitsList]
  -- the value read into `rcon`
  have hread1 : ∀ s, F s → s.regs rc = c → (readSec numSec 0 8
      (.bin .add (.bin .add (readSec numSec 0 0 (.const 4)) (.const 1))
        (.bin .add (readSec numSec 0 8 (.reg rq)) (.reg rc)))).eval w s = some con := by
    intro s hs hrc
    obtain ⟨hr0, hrq, hl⟩ := hF s hs
    have hl' : ListAt s.mem b (layoutList x.sections) := hl
    have hnp : (readSec numSec 0 0 (.const 4)).eval w s = some x.H.A.numPairs := by
      have := eval_readSec' (w := w) hl' hb hr0 hl0 (ke := .const 4) (k := 4)
        (Expr.eval_const (by omega)) (by rw [hs0]; simp [HierConcrete.header])
      rw [hlen, hs0] at this
      simpa [HierConcrete.header] using this
    have hq8 : (readSec numSec 0 8 (.reg rq)).eval w s = some off := by
      have := eval_readSec' (w := w) hl' hb hr0 hl8 (ke := .reg rq) (k := q)
        (Expr.eval_reg_of_eq hrq) hql
      rw [hlen, hs8, csrList_getD_offset _ hq.le] at this
      exact this
    have := eval_readSec' (w := w) hl' hb hr0 hl8
      (ke := .bin .add (.bin .add (readSec numSec 0 0 (.const 4)) (.const 1))
        (.bin .add (readSec numSec 0 8 (.reg rq)) (.reg rc)))
      (k := x.H.A.numPairs + 1 + (off + c))
      (Expr.eval_add (Expr.eval_add hnp (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_add hq8 (Expr.eval_reg_of_eq hrc) (by omega)) (by omega)) hdl
    rw [hlen, hs8, ← Nat.add_assoc, csrList_getD_data _ hq hc,
      List.getD_eq_getElem _ _ hc] at this
    exact this
  have hvalid : x.H.A.pairValid (x.H.A.surv x.ms.st) q c = decide (con ∉ x.ms.st.inelig) := by
    unfold StaticArrays.pairValid
    rw [List.getD_eq_getElem _ _ hc, ← hcon, hinel]
    simp [hconlt]
  refine Triple.seq_normal
    (R := fun s1 => F s1 ∧ s1.regs rc = c ∧ s1.regs rgo = 1 ∧ s1.regs rcon = con)
    (Triple.assign (val := fun _ => con) (fun s hs => hread1 s hs.1 hs.2.1) fun s hs => ?_)
    (Triple.assign (val := fun _ => if x.H.A.pairValid (x.H.A.surv x.ms.st) q c then 1 else 0)
      (fun s hs => ?_) fun s hs => ?_) ?_
  · refine ⟨hFcon _ _ hs.1, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hccon)]; exact hs.2.1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgcon)]; exact hs.2.2
  · obtain ⟨hF1, _, _, hcon1⟩ := hs
    obtain ⟨hr0, _, hl⟩ := hF s hF1
    have hl' : ListAt s.mem b (layoutList x.sections) := hl
    have := eval_readSec' (w := w) hl' hb hr0 hl15 (ke := .reg rcon) (k := con)
      (Expr.eval_reg_of_eq hcon1) (by rw [hs15]; simpa using hconlt)
    rw [hlen, hbit] at this
    have e := Expr.eval_bin (op := .sub) (Expr.eval_const (w := w) (st := s) (k := 1) (by omega))
      this (by simp only [BinOp.eval]; split_ifs <;> omega)
    rw [e, hvalid]
    by_cases hh : con ∈ x.ms.st.inelig <;> simp [BinOp.eval, hh]
  · obtain ⟨hF1, hc1, hg1, _⟩ := hs
    refine ⟨hFv _ _ hF1, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hcv)]; exact hc1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgv)]; exact hg1
  · intro _ _ _ _
    simp [readSec, secAddr, Expr.size]

/-- **Moving a pair cursor.** With the length of the connector array of pair `q` in register
`rN`, the loop moves the cursor in register `rc` from `c₀` to the next eligible entry. -/
theorem pairAdvance_triple {w : ℕ} {p : Program} (x : HierConcrete) {b q : ℕ}
    {rq rc rN rgo rcon rv : ℕ} (h0con : rcon ≠ 0) (h0v : rv ≠ 0) (hqcon : rcon ≠ rq)
    (hccon : rcon ≠ rc) (hgcon : rcon ≠ rgo) (hcv : rv ≠ rc) (hgv : rv ≠ rgo)
    (hconv : rcon ≠ rv) (hrc : rc ≠ rgo) (hrN : rN ≠ rgo) (hrNc : rN ≠ rc)
    (hq : q < x.H.A.numPairs) (hb : b + x.encode.length < 2 ^ w)
    (hw : (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    (hmem : ∀ c ∈ x.H.A.pairConns q, c < x.H.A.C.numConn)
    {F : State → Prop}
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs rq = q ∧ ListAt s.mem b x.encode)
    (hFN : ∀ s, F s → s.regs rN = (x.H.A.pairConns q).length)
    (hFcon : ∀ s v, F s → F { s with regs := Function.update s.regs rcon v })
    (hFv : ∀ s v, F s → F { s with regs := Function.update s.regs rv v })
    (hFc : ∀ s v, F s → F { s with regs := Function.update s.regs rc v })
    (hFg : ∀ s v, F s → F { s with regs := Function.update s.regs rgo v })
    {c₀ : ℕ} (hc₀ : c₀ ≤ (x.H.A.pairConns q).length) :
    Triple w p (fun s => F s ∧ s.regs rc = c₀)
      (advanceStmt (pairTestStmt rq rc rcon rv) rc rN rgo rv)
      (normalPost fun s' => F s' ∧ s'.regs rc =
        advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q) (x.H.A.pairConns q).length c₀)
      (fun _ => (advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q) (x.H.A.pairConns q).length c₀ -
        c₀ + 1) * (60 + 30) + 6) :=
  advanceStmt_triple hrc hrN hrNc hgv hw hFN hFc hFg
    (fun c hc => pairTest_triple x h0con h0v hqcon hccon hgcon hcv hgv hconv hq hb hinel hmem
      hF hFcon hFv c hc) hc₀

end MinCostFlow.HierPaths

end
