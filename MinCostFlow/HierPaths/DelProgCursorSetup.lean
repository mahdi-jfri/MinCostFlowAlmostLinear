module

public import MinCostFlow.HierPaths.DelProgConnPass
public import MinCostFlow.HierPaths.DelProgSupTest

/-!
# Loading a cursor and the length of its list

Pair lists have one word per entry. Support lists have three words per entry. The same
setup reads the two offsets and divides their difference by the entry width.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Load a list length and cursor for the index in register 39. -/
def delCursorSetup (lists curs width : ℕ) (count : Expr) : Stmt :=
  .seq (delCsrSetup lists 39 40 41 count)
    (.seq (.assign 42 (.bin .div (.bin .sub (.reg 41) (.reg 40)) (.const width)))
      (.assign 43 (readSec numSec 0 curs (.reg 39))))

theorem delCursorSetup_noRand (lists curs width : ℕ) (count : Expr) :
    (delCursorSetup lists curs width count).NoRand := by
  simp [delCursorSetup, delCsrSetup_noRand, Stmt.NoRand]

/-- The register loads for a cursor refresh preserve memory. -/
theorem delCursorSetup_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b n j lists curs width old : ℕ} {f : ℕ → List ℕ} {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop}
    {count : Expr}
    (hl : lists < numSec) (hc : curs < numSec)
    (hsec : x.sections.getD lists [] = csrList n f)
    (hj : j < n) (hR0 : R 0 = b) (hR39 : R 39 = j)
    (hjcur : j < (x.sections.getD curs []).length) (hold : (x.sections.getD curs [])[j] = old)
    (hwidthW : width < 2 ^ w)
    (hM : ∀ mem, M mem → ListAt mem b x.encode) (hb : b + x.encode.length < 2 ^ w)
    (hcount : ∀ s : State, M s.mem → s.regs 0 = b → count.eval w s = some n) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) (delCursorSetup lists curs width count)
      (normalPost fun s =>
        s.regs = Function.update (Function.update
          (Function.update (Function.update R 40 (delCsrStart n f j)) 41
            (delCsrStart n f (j + 1))) 42 ((f j).length / width)) 43 old ∧ M s.mem)
      (fun _ => 2 * count.size + 80) := by
  let lo := delCsrStart n f j
  let hi := delCsrStart n f (j + 1)
  let R' := Function.update (Function.update R 40 lo) 41 hi
  let R'' := Function.update R' 42 ((f j).length / width)
  have hhi : hi = lo + (f j).length := delCsrStart_succ _ _ _
  have hdiff : hi - lo = (f j).length := by omega
  have hhiW : hi < 2 ^ w := by
    have h1 := delCsrStart_le n f hj
    have hpos : 0 < (x.sections.getD lists []).length := by rw [hsec]; simp [csrList]
    have h2 := lt_length_of_sec (bs := x.sections) (i := lists)
      (by rw [x.length_sections']; exact hl)
      (k := (x.sections.getD lists []).length - 1) (by omega)
    rw [hsec] at h2
    change _ < x.encode.length at h2
    change hi ≤ _ at h1
    omega
  have hlen : (f j).length < 2 ^ w := by omega
  have hset := delCsrSetup_triple (p := p) (r := 39) (lo := 40) (hi := 41)
    hl hsec hj hR0 hR39 (by decide) (by decide) hM hb hcount
  have hdiv : Triple w p (fun s => s.regs = R' ∧ M s.mem)
      (.assign 42 (.bin .div (.bin .sub (.reg 41) (.reg 40)) (.const width)))
      (normalPost fun s => s.regs = R'' ∧ M s.mem)
      (fun _ => 6) := by
    refine (triple_assign_exact (v := (f j).length / width) ?_).mono_cost (fun _ _ => by simp [Expr.size])
    intro s hr _
    rw [← hdiff]
    exact Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq (v := hi) (by rw [hr]; simp [R']))
      (Expr.eval_reg_of_eq (v := lo) (by rw [hr]; simp [R'])) hhiW)
      (Expr.eval_const hwidthW) (by rw [hdiff]; exact hlen)
  have hload : Triple w p (fun s => s.regs = R'' ∧ M s.mem)
      (.assign 43 (readSec numSec 0 curs (.reg 39)))
      (normalPost fun s => s.regs = Function.update R'' 43 old ∧ M s.mem)
      (fun _ => 14) := by
    refine (triple_assign_exact ?_).mono_cost (fun _ _ => by simp [readSec, secAddr, Expr.size])
    intro s hr hm
    have h := eval_readSec (w := w)
      (show ListAt s.mem b (layoutList x.sections) from hM _ hm) hb (r := 0)
      (by rw [hr]; simpa [R', R''] using hR0) (i := curs)
      (by rw [x.length_sections']; exact hc)
      (Expr.eval_reg_of_eq (r := 39) (v := j) (by rw [hr]; simpa [R', R''] using hR39)) hjcur
    rwa [x.length_sections', hold] at h
  exact (Triple.seq_normal_const hset (Triple.seq_normal_const hdiv hload)).mono_cost
    (fun _ _ => by omega)

/-- Write the advanced cursor in register 43 to the index in register 39. -/
def delCursorStore (sec : ℕ) : Stmt :=
  .store (secAddr numSec 0 sec (.reg 39)) (.reg 43)

theorem delCursorStore_noRand (sec : ℕ) : (delCursorStore sec).NoRand := by
  simp [delCursorStore, Stmt.NoRand]

/-- Writing the cursor preserves the registers and cells outside the block. -/
theorem delCursorStore_triple {w : ℕ} {p : Program} (x y : HierConcrete)
    {b sec j next : ℕ} (hsec : sec < numSec)
    (hj : j < (x.sections.getD sec []).length)
    (hy : y.sections = x.sections.set sec ((x.sections.getD sec []).set j next))
    (hb : b + x.encode.length < 2 ^ w) {F : State → Prop}
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs 39 = j ∧ s.regs 43 = next ∧
      ListAt s.mem b x.encode) :
    Triple w p F (delCursorStore sec) (normalPost fun s =>
      ∃ s₀, F s₀ ∧ s.regs = s₀.regs ∧ ListAt s.mem b y.encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = s₀.mem i)
      (fun _ => 14) := by
  have H := triple_writeSec' (w := w) (p := p) (P := F) (bs := x.sections) (r := 0)
    (i := sec) (by rw [x.length_sections']; exact hsec) (ke := .reg 39) (ve := .reg 43)
    (k := fun _ => j) (v := fun _ => next) (fun s hs => by
      obtain ⟨h0, h39, h43, hmem⟩ := hF s hs
      exact ⟨hmem, h0, Expr.eval_reg_of_eq h39, hj, Expr.eval_reg_of_eq h43⟩) hb
  rw [x.length_sections'] at H
  unfold delCursorStore
  refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [secAddr, Expr.size])
  cases o <;> try contradiction
  obtain ⟨s₀, hs₀, hregs, _, hmem, hframe⟩ := h
  refine ⟨s₀, hs₀, hregs, ?_, hframe⟩
  change ListAt s.mem b (layoutList y.sections)
  rwa [hy]

end MinCostFlow.HierPaths

end
