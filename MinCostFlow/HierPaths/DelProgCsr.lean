module

public import MinCostFlow.HierPaths.DelProgScan

/-!
# Reading a list interval in the Delete block

The connector and walk passes traverse CSR lists. Two offset reads give the half-open
interval of words to scan, including an empty interval when the list has no entries.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The start of a list in a CSR section with `n` lists. -/
def delCsrStart (n : ℕ) (f : ℕ → List ℕ) (j : ℕ) : ℕ :=
  n + 1 + ((List.range j).map fun i => (f i).length).sum

theorem delCsrStart_succ (n : ℕ) (f : ℕ → List ℕ) (j : ℕ) :
    delCsrStart n f (j + 1) = delCsrStart n f j + (f j).length := by
  simp [delCsrStart, List.range_succ, Nat.add_assoc]

theorem delCsrStart_le (n : ℕ) (f : ℕ → List ℕ) {j : ℕ} (hj : j ≤ n) :
    delCsrStart n f j ≤ (csrList n f).length := by
  have hlen : (csrList n f).length = delCsrStart n f n := by
    simp [csrList, csrData, List.length_flatMap, delCsrStart]
  rw [hlen]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
  conv_rhs => rw [hk, delCsrStart, List.range_add, List.map_append, List.sum_append]
  unfold delCsrStart
  omega

/-- Two offset reads give the start and end words of the list indexed by register `r`. -/
def delCsrSetup (i r lo hi : ℕ) (count : Expr) : Stmt :=
  .seq (.assign lo (.bin .add (.bin .add count (.const 1)) (readSec numSec 0 i (.reg r))))
    (.assign hi (.bin .add (.bin .add count (.const 1))
      (readSec numSec 0 i (.bin .add (.reg r) (.const 1)))))

theorem delCsrSetup_noRand (i r lo hi : ℕ) (count : Expr) :
    (delCsrSetup i r lo hi count).NoRand := by
  simp [delCsrSetup, Stmt.NoRand]

/-- Read a CSR interval while preserving memory and all registers other than the two outputs. -/
theorem delCsrSetup_triple {w : ℕ} {p : Program} {x : HierConcrete}
    {b i n j r lo hi : ℕ} {f : ℕ → List ℕ} {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop}
    {count : Expr}
    (hiSec : i < numSec) (hsec : x.sections.getD i [] = csrList n f)
    (hj : j < n) (hR0 : R 0 = b) (hRr : R r = j) (hlo0 : lo ≠ 0) (hlor : lo ≠ r)
    (hM : ∀ mem, M mem → ListAt mem b x.encode) (hb : b + x.encode.length < 2 ^ w)
    (hc : ∀ s : State, M s.mem → s.regs 0 = b → count.eval w s = some n) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) (delCsrSetup i r lo hi count)
      (normalPost fun s =>
        s.regs = Function.update (Function.update R lo (delCsrStart n f j)) hi
          (delCsrStart n f (j + 1)) ∧ M s.mem)
      (fun _ => 2 * count.size + 50) := by
  have hpos : 0 < (x.sections.getD i []).length := by rw [hsec]; simp [csrList]
  have hle : (x.sections.getD i []).length ≤ x.encode.length := by
    have h := lt_length_of_sec (bs := x.sections) (i := i)
      (by rw [x.length_sections']; exact hiSec)
      (k := (x.sections.getD i []).length - 1) (by omega)
    change _ < x.encode.length at h
    omega
  have hread : ∀ (s : State), M s.mem → s.regs 0 = b → ∀ {k : ℕ} {ke : Expr},
      k ≤ n → ke.eval w s = some k →
      (Expr.bin .add (.bin .add count (.const 1)) (readSec numSec 0 i ke)).eval w s =
        some (delCsrStart n f k) := by
    intro s hm h0 k ke hk hke
    have hkl : k < (x.sections.getD i []).length := by
      rw [hsec]; simp [csrList]; omega
    have hoff := eval_readSec' (w := w)
      (show ListAt s.mem b (layoutList x.sections) from hM _ hm)
      hb h0 (i := i) (by rw [x.length_sections']; exact hiSec) hke hkl
    rw [x.length_sections', hsec, csrList_getD_offset _ hk] at hoff
    have hbound := (delCsrStart_le n f hk).trans (hsec ▸ hle)
    have hn : n + 1 ≤ delCsrStart n f k := by unfold delCsrStart; omega
    exact Expr.eval_add (Expr.eval_add (hc s hm h0) (Expr.eval_const (by omega)) (by omega))
      hoff (by simpa only [delCsrStart] using hbound.trans_lt (by omega : x.encode.length < 2 ^ w))
  have hjw : j + 1 < 2 ^ w := by
    have h := (delCsrStart_le n f (Nat.le_of_lt hj)).trans (hsec ▸ hle)
    have hn : n + 1 ≤ delCsrStart n f j := by unfold delCsrStart; omega
    omega
  unfold delCsrSetup
  refine (Triple.seq_normal_const
    (triple_assign_exact (R := R) (M := M) (r := lo) (v := delCsrStart n f j) ?_)
    (triple_assign_exact (r := hi) (v := delCsrStart n f (j + 1)) ?_)).mono_cost ?_
  · intro s hs hm
    exact hread s hm (by rw [hs, hR0]) hj.le (Expr.eval_reg_of_eq (by rw [hs, hRr]))
  · intro s hs hm
    exact hread s hm (by rw [hs]; simpa [Ne.symm hlo0] using hR0) hj
      (Expr.eval_add (Expr.eval_reg_of_eq (v := j) (by rw [hs]; simpa [Ne.symm hlor] using hRr))
        (Expr.eval_const (by omega)) hjw)
  · intro s hs
    simp only [readSec, secAddr, Expr.size]
    omega

end MinCostFlow.HierPaths

end
