module

public import MinCostFlow.HierPaths.InitProgFlatRead

/-!
# Addressing a hierarchy row

Both the host and the embedding tables use a rectangular array of row
offsets. The row number is computed from the depth and group in constant time.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the static block address, the number of terminals and depths,
and the requested depth and group. The section number is fixed by the caller. -/
def initFlatSeek (sectionId seek : ℕ) : Stmt :=
  .call 5 seek
    [.bin .add (.bin .add (.reg 0) (.const 7)) (.load (.bin .add (.reg 0) (.const sectionId))),
      .bin .mul (.reg 1) (.reg 2),
      .bin .add (.bin .mul (.reg 3) (.reg 1)) (.reg 4)] ;;
  .ret (.reg 5)

theorem initFlatSeek_noRand (i seek : ℕ) : (initFlatSeek i seek).NoRand := by
  simp [initFlatSeek, Stmt.NoRand]

/-- A rectangular table in the static output permits lookup without changing memory. -/
def initFlatSeekContract (w i : ℕ) (S : StaticData) (D : ℕ) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ h j g, args = [h, S.numTerm, D, j, g] ∧ StaticOut mem h S ∧
    h + S.encode.length < 2 ^ w ∧ i < 6 ∧ j < D ∧ g < S.numTerm ∧
    S.sections.getD i [] = csrList (D * S.numTerm) f
  post args mem v mem' := ∃ h j g, args = [h, S.numTerm, D, j, g] ∧
    v = initCSRAddr (h + 7 + mem (h + i)) (D * S.numTerm) f (j * S.numTerm + g) ∧ mem' = mem
  cost _ _ := 40

theorem initFlatSeek_meetsContract {w k i seek D : ℕ} {S : StaticData} {f : ℕ → List ℕ}
    {p : Program} (hp : p.procs[k]? = some (initFlatSeek i seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p k (initFlatSeekContract w i S D f) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨h, j, g, rfl, hS, hw, hi, hj, hg, hsection⟩ := hpre
  let a := h + 7 + mem (h + i)
  let n := D * S.numTerm
  let z := j * S.numTerm + g
  have hrow : ListAt mem a (csrList n f) := hsection ▸ hS.section hi
  have ha : a + (csrList n f).length < 2 ^ w := by
    have hb := hS.section_end_le hi
    rw [hsection] at hb
    exact hb.trans_lt hw
  have hn : n + 1 ≤ (csrList n f).length := by rw [length_csrList]; omega
  have hz : z < n := calc
    j * S.numTerm + g < j * S.numTerm + S.numTerm := Nat.add_lt_add_left hg _
    _ = (j + 1) * S.numTerm := (Nat.succ_mul _ _).symm
    _ ≤ n := Nat.mul_le_mul_right _ hj
  have hz' : j * S.numTerm ≤ z := Nat.le_add_right _ _
  have haw : a < 2 ^ w := by omega
  have hn' : n < 2 ^ w := by omega
  have hzw : z < 2 ^ w := hz.trans hn'
  have haEval : (Expr.bin .add (.bin .add (.reg 0) (.const 7))
      (.load (.bin .add (.reg 0) (.const i)))).eval w
      (startState [h, S.numTerm, D, j, g] mem pos) = some a := by
    have hb : h + 7 ≤ a := Nat.le_add_right _ _
    exact Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_const (by omega)) (by omega)) rfl)
      haw
  refine runs_start_le ?_
  unfold initFlatSeek
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := n) (f := f) hseek)
    (vs := [a, n, z]) ?_ ?_ ⟨a, z, rfl, hz.le, hrow, ha⟩ ?_
  · have hnEval : (Expr.bin .mul (.reg 1) (.reg 2)).eval w
        (startState [h, S.numTerm, D, j, g] mem pos) = some n := by
      rw [show n = S.numTerm * D from Nat.mul_comm _ _]
      refine Expr.eval_mul (Expr.eval_reg_of_eq (v := S.numTerm) rfl)
        (Expr.eval_reg_of_eq (v := D) rfl) ?_
      simpa only [Nat.mul_comm] using hn'
    have hzEval : (Expr.bin .add (.bin .mul (.reg 3) (.reg 1)) (.reg 4)).eval w
        (startState [h, S.numTerm, D, j, g] mem pos) = some z :=
      Expr.eval_add (Expr.eval_mul (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
        (hz'.trans_lt hzw)) (Expr.eval_reg_of_eq rfl) hzw
    simp only [evalArgs, haEval, hnEval, hzEval]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact haw
    · exact hn'
    · exact hzw
  intro v mem' pos' hp'
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq rfl) ⟨h, j, g, rfl, hp'⟩ ?_
  simp [initCSRSeekContract, initFlatSeekContract, argsSize, Expr.size]

end MinCostFlow.HierPaths

end
